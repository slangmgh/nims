##
## simple nim repl
##
## compile with libffi, must use gcc
## >>> nimble install libffi
## >>> nim c --cc:gcc -d:release -d:nimcore -d:nimHasLibFFI nims.nim
##
## compile without libffi
## >>> nim c -d:release -d:nimcore nims.nim
##

import os, terminal, strutils, sequtils, times, macros, strformat
import "../../compiler" / [ast, astalgo, modules, passes, condsyms,
       options, sem, semdata, llstream, vm, vmdef, nimeval, lineinfos, msgs,
       modulegraphs, idents, pathutils, passaux, scriptconfig, parser]

import segfaults

const my_special_vmops = defined(myvmops)

when my_special_vmops:
   import httputils, guessencoding

const
   indent_oprs = {'=', ':', '+', '-', '*', '/', '\\', '<', '>', '!', '?', '^',
                                       '|', '%', '&', '$', '@', '~', ','}
   indent_keys = ["var", "let", "const", "import", "type", "object", "enum", "and", "or", "not"]
   indent_spaces = "   "

let
   nims_cache_file = getTempDir() / "nims_cache_file.nim"

type
   RunOption = enum
      opt_verbose
      opt_save_nims_code
      opt_no_preload_module
      opt_paste_mode
      opt_exception_to_reset_module
      opt_error_to_reload_code
      opt_check_failed_module_time
      opt_using_ic_cache

   ErrorHook = proc(config: ConfigRef; info: TLineInfo; msg: string; severity: Severity) {.closure, gcsafe.}
   RunContext = ref object
      conf: ConfigRef

      input_stream: PLLStream

      libpath: string
      libs: seq[string]
      imports: seq[string]

      options: set[RunOption]
      max_compiler_errors: int

      failed_imports: seq[tuple[name: string, fullname: string, time: Time]]

      last_input_line: string
      last_line_is_import: bool
      last_line_has_error: bool
      last_line_need_reset: bool

      pre_load_code: string
      input_lines_good: seq[string]

proc init(ctx: RunContext) =
   ctx.last_line_need_reset = false
   ctx.last_line_has_error = false
   ctx.last_line_is_import = false
   ctx.last_input_line = ""

template on(o: RunOption): bool = o in ctx.options

proc toggle_option(ctx: RunContext, o: RunOption) =
   if o in ctx.options:
      ctx.options.excl o
   else:
      ctx.options.incl o

proc add_failed_module(ctx: RunContext, name, fullname: string) =
   let time = getLastModificationTime(fullname)
   ctx.failed_imports.add (name, fullname, time)

proc is_failed_module(ctx: RunContext, name: string): bool =
   ctx.failed_imports.anyIt(it.name == name)

proc refresh_failed_module_with_last_mod_time(ctx: RunContext) =
   ctx.failed_imports = ctx.failed_imports.filterIt(it.time == getLastModificationTime(it.fullname))

var native_import_procs {.compileTime.} : string

macro vmops(vm: PCtx, op: untyped, argtypes: varargs[untyped]): untyped =
   let op_wrapper = ident($op & "_wrapper")
   let a = ident("a")
   var call_op = newCall(op)
   for i, arg in argtypes:
      let get_arg_name = ident("get" & ($arg).capitalizeAscii)
      call_op.add newCall(get_arg_name).add(a, newLit(i))

   quote do:
      proc `op_wrapper`(`a`: VmArgs) {.nimcall.} =
         setResult(`a`, `call_op`)
      `vm`.registerCallback(`op`.ast_to_str, `op_wrapper`)

macro vm_native_proc(vm: PCtx, list: untyped): untyped =
   var vmops_calls = newStmtList()
   for p in list:
      if p.kind in [nnkProcDef, nnkFuncDef]:
         var op = p.name
         var pcall = newCall("vmops", `vm`, `op`)

         native_import_procs.add "proc " & $p.name & "*("
         let params = p.params
         for i in 1 ..< params.len:
            let ptype = params[i][^2]
            for j in 0 .. len(params[i])-3:
               if i > 1 or j > 0:
                  native_import_procs.add ", "
               native_import_procs.add $params[i][j] & ": " & $ptype
               pcall.add ptype

         native_import_procs.add "): " & $p.params[0] & " = discard\p"
         vmops_calls.add pcall

   vmops_calls

template with_color(fg: ForegroundColor, bright = false, body: untyped) =
   setForegroundColor(fg, bright)
   block:
      body
   resetAttributes()

func count_triples(s: string): int =
  var i = 0
  while i+2 < s.len:
    if s[i] == '"' and s[i+1] == '"' and s[i+2] == '"':
      inc result
      inc i, 2
    inc i

func continue_line*(line: string): bool =
   line.len > 0 and
      ((line[^1] in indent_oprs) or indent_keys.anyIt(line.endsWith(it)))

func is_all_space(line: string): bool =
   line == "" or line.allIt(it == ' ')

func is_import_line(s: string): bool =
   let s = s.strip
   s.startsWith("import ") or s.startsWith("from ") or s.startsWith("include ")

proc disable_stdout() =
   const device = when defined(windows): "NUL" else: "/dev/null"
   discard reopen(stdout, device, fmWrite)

proc enable_stdout() =
   const device = when defined(windows): "CON" else: "/dev/tty"
   discard reopen(stdout, device, fmWrite)

proc get_prompt(indent_level, line_no: int): string =
   let prompt_str = if indent_level == 0: ">>> " else: ">++ "
   &"{line_no}{prompt_str}{indent_spaces.repeat(indent_level)}"

proc show_raw_buffer(buffer: string, header: string) =
   with_color(fgCyan, false):
      echo header.center(70, '-')

   with_color(fgYellow, false):
      echo buffer.strip(leading = false)

   with_color(fgCyan, false):
      echo '-'.repeat(70)

proc save_nims_cache_file(lines: seq[string]) =
   let file = open(nims_cache_file, fmWrite)
   defer: file.close
   file.write(lines.join(""))

proc load_nims_cache_file(): seq[string] =
   if file_exists(nims_cache_file):
      let file = open(nims_cache_file, fmRead)
      defer: file.close
      result = readAll(file).split_lines.filterIt(it.strip() != "").mapIt(it & "\p")

proc readLineFromStdin(prompt: string): (string, bool) =
   let time_start = cpuTime()
   stdout.write(prompt)
   let s = readLine(stdin)
   let time_end = cpuTime()
   let is_paste = time_end - time_start < 0.08
   (s, is_paste)

type ResetError* = object of CatchableError
type ReloadError* = object of CatchableError

template Reset(): untyped = newException(ResetError, "Reset the vm")
template Reload(): untyped = newException(ReloadError, "Reload the code")

## paste mode
## 不做任何缩进和命令处理，直接把内容加上去
## 切换成paste mode的方式：
## 1. 用paste命令
## 2. 当发现readLine调用时间特别短的时候
## 3. 发现输入的行中有注释行，第一个字符为'#'的时候
##
## 正常模式
## 做缩进和命令处理
## 切换成正常模式的方式
## 1. 用paste命令

proc my_read_line(ctx: RunContext): string =
   template args(n: int, s: string): string = (if cmds.len > n: cmds[n] else: s)
   template argn[T: float|int](n: int, v: T): T =
      if cmds.len > n:
         when T is int: parseInt(cmds[n])
         else: parseFloat(cmds[n])
      else: v

   template add_line() =
      buffer &= myline & "\p"
      inc(line_no)

   template onoff(v: RunOption): string = (if v in ctx.options: "on" else: "off")

   template doCmd(cmd: string) =
      case cmd
      of "help", "h":
         with_color(fgCyan, false):
            echo ":help   [\\h]: Show help."
            echo ":clear  [\\c]: Clear the input code."
            echo ":show   [\\s]: Show the current code."
            echo ":paste  [\\p]: Enable/Disable the paste mode."
            echo ":except [\\e]: Enable/Disable the except to reset mode."
            echo ":option [\\o]: Show current options."
            echo ":reset  [\\r]: Reset the vm to init state."
            echo ":exit   [\\q]: Exit the program."
      of "exit", "quit", "q", "x":
         quit()
      of "verbose", "debug", "v", "d":
         ctx.toggle_option(opt_verbose)
         setForegroundColor(fgCyan)
         with_color(fgCyan, false):
            echo "Debug mode is " & opt_verbose.onoff
      of "paste", "p":
         ctx.toggle_option(opt_paste_mode)
         with_color(fgCyan, false):
            echo "Paste mode is " & opt_paste_mode.onoff
      of "exceptmode", "xm", "except":
         ctx.toggle_option(opt_exception_to_reset_module)
         with_color(fgCyan, false):
            echo "Exception reset mode is " & opt_exception_to_reset_module.onoff
      of "ic", "iccache":
         when false:
            ctx.toggle_option(opt_using_ic_cache)
            with_color(fgCyan, false):
               echo "Using incremental cache is " & opt_using_ic_cache.onoff
      of "errormode", "em", "error":
         ctx.toggle_option(opt_error_to_reload_code)
         with_color(fgCyan, false):
            echo "Error reload mode is " & opt_error_to_reload_code.onoff
      of "savecode", "sc", "cache":
         ctx.toggle_option(opt_save_nims_code)
         with_color(fgCyan, false):
            echo "Save nims code is " & opt_save_nims_code.onoff
      of "show", "s":
         show_raw_buffer(ctx.input_lines_good.join(""), "Current buffer")
      of "maxerrors", "me":
         if cmds.len > 1:
            ctx.max_compiler_errors = argn(1, 10)
         with_color(fgCyan, false):
            echo "Max compiler errors is " & $ctx.max_compiler_errors
      of "clean", "clear", "c":
         if ctx.input_lines_good.len > 0:
            let clear_line_count = argn(1, -1)
            if clear_line_count < 0 or clear_line_count >= ctx.input_lines_good.len:
               ctx.input_lines_good = @[]
               with_color(fgCyan, false):
                  echo "Input buffer is empty"

               if opt_save_nims_code.on:
                  save_nims_cache_file(ctx.input_lines_good)
            else:
               ctx.input_lines_good = ctx.input_lines_good[0..^(clear_line_count+1)]
               show_raw_buffer(ctx.input_lines_good.join(""), "Current buffer")

               if opt_save_nims_code.on:
                  save_nims_cache_file(ctx.input_lines_good)
      of "keep", "k":
         if ctx.input_lines_good.len > 0:
            var keep_line_count = argn(1, -1)
            if keep_line_count == 0:
               ctx.input_lines_good = @[]
               with_color(fgCyan, false):
                  echo "Input buffer is empty"

               if opt_save_nims_code.on:
                  save_nims_cache_file(ctx.input_lines_good)
            elif keep_line_count > 0 and keep_line_count < ctx.input_lines_good.len:
                  ctx.input_lines_good = ctx.input_lines_good[0..(keep_line_count-1)]
                  show_raw_buffer(ctx.input_lines_good.join(""), "Current buffer")

                  if opt_save_nims_code.on:
                     save_nims_cache_file(ctx.input_lines_good)
      of "load", "ll":
         ctx.input_lines_good = load_nims_cache_file()
         raise Reload()
      of "options", "option", "o":
         with_color(fgCyan, false):
            echo "Exception reset mode is " & opt_exception_to_reset_module.onoff
            echo "Error reload mode is " & opt_error_to_reload_code.onoff
            echo "Save nims code is " & opt_save_nims_code.onoff
            echo "Paste mode is " & opt_paste_mode.onoff
            when false:
               echo "Using incremental cache is " & opt_using_ic_cache.onoff
            # echo "Verbose mode is " & opt_verbose.onoff
            echo "Max compiler errors is " & $ctx.max_compiler_errors
      of "reload", "rr":
         raise Reload()
      of "reset", "r", "rs", "rb":
         if cmd == "rs":
            ctx.input_lines_good = @[]
            if opt_save_nims_code.on:
               save_nims_cache_file(ctx.input_lines_good)

         if cmd == "rb":
            ctx.failed_imports = @[]
         else:
            # 手工reset，需要检查编译失败的模块时候需要重新加载
            ctx.options.incl opt_check_failed_module_time

         raise Reset()
      else:
         with_color(fgRed, false):
            echo &"Unknown command {cmds[0]}."

   var
      buffer = ""
      indent_level = 0
      triples = 0
      line_no = 1

   while true:
      var (myline, is_paste) = readLineFromStdin(get_prompt(indent_level, line_no))

      if opt_paste_mode.on:
         ctx.options.excl opt_paste_mode
         add_line()
         continue

      if myline.len > 0 and myline[0] == '#':
         ctx.options.incl opt_paste_mode
         continue

      if is_paste:
         add_line()
         continue

      let cmds = myline.replace(',', ' ').splitWhitespace
      if cmds.len > 0 and cmds[0].len > 0:
         case cmds[0][0]
         of ':', '\\':
            doCmd(cmds[0][1..^1])
            continue
         of '!':
            discard execShellCmd(myline.strip[1..^1])
            continue
         else:
            discard

      inc triples, count_triples(myline)
      let in_triple_string = (triples and 1) == 1
      let need_continue = myline.continue_line
      if myline.is_all_space:
         if indent_level > 0:
            dec(indent_level)
      else:
         if myline[0] != ' ':
            buffer &= indent_spaces.repeat(indent_level)

         add_line()
         if in_triple_string:
            continue
         elif need_continue:
            inc(indent_level)
            continue

      if indent_level == 0 and buffer != "" and (not need_continue) and (not in_triple_string):
         break

   if opt_verbose.on:
      show_raw_buffer(buffer, "Line buffer")

   return buffer

# 在重新初始化的时候，会执行原来成功的代码，这时我们不需要输出
proc my_msg_writeln_hook(msg: string) =
   discard

proc disable_output(conf: ConfigRef) =
   conf.writelnHook = my_msg_writeln_hook
   disable_stdout()

proc enable_output(conf: ConfigRef) =
   if not conf.writelnHook.isNil:
      conf.writelnHook = nil
      enable_stdout()

proc get_line(ctx: RunContext): string =
   if ctx.last_line_need_reset:
      # 出现代码错误，抛出异常后重置环境
      ctx.last_line_need_reset = false
      raise Reset()

   if ctx.last_line_has_error:
      ctx.last_line_has_error = false
      ctx.last_input_line = ""

      if opt_error_to_reload_code.on:
         raise Reload()
      else:
         # 由于出现语法错误的时候，有时会导致下一次输出出现问题，所以
         # 就发送一条无关紧要的语句，修正输出
         # 比如输入 &"{\"xx"}" 就会导致下一条语句没有输出（如果没有下面的语句的话）
         # 不过好像现在又正常了，先不用吧
         # 有时还是不正常了，还是加上吧

         when true:
            ctx.last_input_line = ""
            disable_output(ctx.conf)
            return "echo \" \""

   if ctx.last_input_line != "":
      if ctx.input_lines_good.len == 0 or ctx.input_lines_good[^1] != ctx.last_input_line:
         ctx.input_lines_good.add ctx.last_input_line
         if opt_save_nims_code.on:
            save_nims_cache_file(ctx.input_lines_good)

   ctx.last_input_line = my_read_line(ctx)
   ctx.last_line_is_import = ctx.last_input_line.is_import_line

   return ctx.last_input_line

proc setup_input_stream(ctx: RunContext) =
   proc llReadFromStdin(s: PLLStream, buf: pointer, bufLen: int): int =
      # Ensure the output is fine
      enable_output(ctx.conf)

      s.rd = 0
      if s.lineOffset < 0:
         ctx.last_input_line = ""

         # 初始化import代码，不做任何输出
         disable_output(ctx.conf)
         s.s = ctx.pre_load_code & ctx.input_lines_good.join("")
      else:
         s.s = get_line(ctx)

      # 执行前总是reset错误数
      ctx.conf.errorCounter = 0

      # 设置lineOffset为0, 以确保报错信息和显示行号一致
      s.lineOffset = 0

      result = min(bufLen, s.s.len - s.rd)
      if result > 0:
         copyMem(buf, addr(s.s[s.rd]), result)
         inc(s.rd, result)

   ctx.input_stream = llStreamOpenStdIn(llReadFromStdin)

proc safe_compile_module(graph: ModuleGraph, ctx: RunContext, mf: AbsoluteFile): bool =
   var
      conf = ctx.conf
      success = true

   proc on_compile_error(conf: ConfigRef; info: TLineInfo; msg: string; severity: Severity) {.gcsafe.} =
      if severity == Error and conf.m.errorOutputs.len != 0:
         success = false
         if conf.errorCounter >= ctx.max_compiler_errors:
            raise Reset()

   let old_hook = conf.structuredErrorHook
   conf.errorCounter = 0
   conf.structuredErrorHook = on_compile_error
   try:
      discard graph.compileModule(fileInfoIdx(conf, mf), {})
   except:
      success = false
   finally:
      conf.structuredErrorHook = old_hook

   success

proc setup_config_error_hook(ctx: RunContext) =
   proc on_compile_error(conf: ConfigRef; info: TLineInfo; msg: string; severity: Severity) {.gcsafe.} =
      if severity == Error and conf.m.errorOutputs.len != 0:
         if ctx.last_line_is_import:
            # 出现import错误，一般需要reset虚拟机环境，否则会出各自异常
            # 这里先不能直接抛出Reset异常，因为我们还需要输出异常信息
            ctx.last_line_need_reset = true

            if conf.errorCounter >= ctx.max_compiler_errors:
               with_color(fgRed, false):
                  echo "Too many error occured, skip..."

               # 这里可以直接抛出异常了, 不需要屏蔽输出了
               raise Reset()
         else:
            ctx.last_line_has_error = true

   ctx.conf.structuredErrorHook = on_compile_error

proc register_custom_vmops(vm: PEvalContext, ctx: RunContext, graph: ModuleGraph) =
   var
      conf = ctx.conf

   proc now(): string = times.now().format("HH:mm:ss")
   proc today(): string = times.now().format("yyyy-MM-dd")

   vm.vm_native_proc:
      func cpu_time(): float
      func epoch_time(): float
      proc now(): string
      proc today(): string

   when my_special_vmops:
      vm.vm_native_proc:
         proc httpget(url: string): string
         proc httppost(url, body: string): string
         func make_console_codepage(s: string): string
         func make_gb(s: string): string
         func make_tchar(s: string): string
         func make_utf8(s: string): string

   graph.compileSystemModule()

   # 将注册的API作为一个模块自动import
   const native_import_procs_def = native_import_procs
   let sf = getTempDir() / "scriptapi.nim"
   block:
      let file = open(sf, fmWrite)
      file.write(native_import_procs_def)
      file.close

   conf.implicitImports.add sf
   discard graph.safe_compile_module(ctx, AbsoluteFile sf)

proc setup_interactive_passes(graph: ModuleGraph) =
   registerPass(graph, semPass)
   registerPass(graph, evalPass)

proc setup_vm_config_define(conf: ConfigRef) =
   initDefines(conf.symbols)
   defineSymbol(conf.symbols, "nimconfig")
   defineSymbol(conf.symbols, "nimscript")

   when hasFFI:
      defineSymbol(conf.symbols, "nimffi")
      defineSymbol(conf.symbols, "nimHasLibFFI")

   when my_special_vmops:
      defineSymbol(conf.symbols, "nimVmops")

   undefSymbol(conf.symbols, "nimv2")

proc setup_vm_config(ctx: RunContext, conf: ConfigRef) =
   conf.searchPaths.add ctx.libpath.AbsoluteDir
   for p in ctx.libs:
      let p = p.AbsoluteDir
      conf.searchPaths.add(p)

   conf.libpath = ctx.libpath.AbsoluteDir
   conf.cmd = cmdInteractive
   conf.errorMax = high(int)
   conf.spellSuggestMax = 0
   conf.options.excl optHints
   conf.globalOptions.excl {optTinyRtti, optOwnedRefs, optSeqDestructors}
   conf.features.incl vmopsDanger

   conf.symbolFiles = disabledSf
   conf.selectedGC = gcUnselected

   # 使用incremental compile cache, 目前看起来好像对模块加载速度没有多大提高
   when false:
      if opt_using_ic_cache.on:
         conf.symbolFiles = v2Sf
         conf.cCompiler = ccNone
         conf.selectedGC = gcUnselected
         conf.options = {}
         conf.globalOptions = {}

   when hasFFI:
      conf.features.incl compiletimeFFI

   setup_vm_config_define(conf)

proc create_script_vm(graph: ModuleGraph): PCtx =
   var m = graph.makeModule(AbsoluteFile"script")
   incl(m.flags, sfMainModule)

   var vm = setupVM(m, graph.cache, "stdin", graph, idGeneratorFromModule(m))
   graph.vm = vm
   return vm

proc load_preload_module(ctx: RunContext, graph: ModuleGraph) =
   var conf = graph.config

   if opt_check_failed_module_time.on:
      ctx.options.excl opt_check_failed_module_time
      ctx.refresh_failed_module_with_last_mod_time()

   var pre_compile_module: seq[string]

   # 预编译这些模块，这样在出现异常重新加载的时候，就不需要重新解析了
   var pre_load_module: seq[string]
   if not opt_no_preload_module.on:
      pre_load_module =  @["strutils", "strformat", "os", "tables", "sets", "math", "json", "macros"]
      when not my_special_vmops:
         pre_load_module.add "sequtils"

   for f in pre_load_module & ctx.imports:
      if not is_failed_module(ctx, f):
         let mf = findFile(conf, f & ".nim")
         if not mf.isEmpty:
            if not graph.safe_compile_module(ctx, mf):
               ctx.add_failed_module(f, mf.string)
               raise Reset()
            else:
               pre_compile_module.add f

   # 缺省import的模块
   if pre_compile_module.len > 0:
      ctx.pre_load_code = "import " & pre_compile_module.join(",") & "\p"
   else:
      ctx.pre_load_code = ""

proc setup_vm_environment(ctx: RunContext, graph: ModuleGraph) =
   setup_input_stream(ctx)
   setup_vm_config(ctx, graph.config)
   setup_config_error_hook(ctx)
   setup_interactive_passes(graph)

   var vm = create_script_vm(graph)
   vm.register_custom_vmops(ctx, graph)
   load_preload_module(ctx, graph)

proc run_repl(ctx: RunContext) =
   var graph = newModuleGraph(newIdentCache(), ctx.conf)
   setup_vm_environment(ctx, graph)

   # 存在3种类型的出错：
   # 1. 输入代码语法错，一般不需要额外操作，只是把错误的代码忽略就可以
   # 2. 输入代码抛出异常，这个时候原来的代码建立的环境会失效，需要重新执行一遍代码，就是reload
   # 3. 如果输入import times这种，可能会破坏整个vm，这个时候需要重建整个环境，就是reset
   while true:
      try:
         ctx.init()
         let vm = cast[PCtx](graph.vm)
         graph.processModule(vm.module, vm.idgen, ctx.input_stream)
      except ResetError:
         break
      except ReloadError:
         discard
      except NilAccessDefect:
         # 出现 nil 异常，我们还是Reset吧
         break
      except:
         with_color(fgRed, false):
            stdout.write("Error: ")
         echo getCurrentExceptionMsg()

         if opt_exception_to_reset_module.on:
            break

proc ctrl_c_proc() {.noconv.} =
   quit "CTRL-C pressed, quit."

proc main() =
   var nimlib = ""

   let args = commandLineParams()
   let libs_arg = args.filterIt(it.startsWith("--lib:") or it.startsWith("-lib:"))
   if libs_arg.len > 0:
      for arg in libs_arg:
         var s = arg.split(':')[1]
         if file_exists(s / "system.nim"):
            nimlib = s
            break

   if nimlib == "":
      nimlib = findNimStdLib()

   if nimlib == "":
      quit("Cannot find nim.exe in the PATH")

   var libs = @[nimlib / "core",
                nimlib / "pure",
                nimlib / "pure/collections",
                nimlib / "system",
                nimlib / "windows"]

   when my_special_vmops:
      libs.add(nimlib /../ "mylib")

   let pkg_dir = (if getEnv("NIMBLE_DIR") != "": getEnv("NIMBLE_DIR") else: nimlib /../ "nimble") / "pkgs"
   for p in walkDir(pkg_dir):
      libs.add p.path

   var ctx = RunContext(max_compiler_errors: 10, libpath: nimlib, libs: libs)
   if args.anyIt(it.startsWith("-cache") or it.startsWith("--cache")):
      ctx.options.incl opt_save_nims_code
      ctx.input_lines_good = load_nims_cache_file()

   if args.anyIt(it.startsWith("-no-preload-module") or it.startsWith("--no-preload-module")):
      ctx.options.incl opt_no_preload_module

   ctx.imports = args.filterIt(not it.startsWith("-"))
   set_control_chook(ctrl_c_proc)
   while true:
      try:
         ctx.conf = newConfigRef()
         run_repl(ctx)
      except:
         discard

when isMainModule:
   main()
