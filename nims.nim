## nims.nim

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

var
   using_ic_cache = false
   restart_eval = true
   pre_load_code = ""

   failed_imports: seq[tuple[name: string, fullname: string, time: Time]]
   check_failed_module_time = false

   save_nims_code = false
   verbose = false
   paste_mode = false
   exception_to_reset_module = false
   error_to_reload_code = false

   last_input_line = ""
   last_line_is_import = false
   input_lines_good: seq[string]
   cur_error_count = 0

   last_line_has_error = false
   last_line_need_reset = false

   max_compiler_errors = 10

   cur_conf: ConfigRef
   cur_graph: ModuleGraph
   cur_module: PSym


proc add_failed_module(name, fullname: string) =
   let time = getLastModificationTime(fullname)
   failed_imports.add (name, fullname, time)

proc is_failed_module(name: string): bool =
   failed_imports.anyIt(it.name == name)

proc refresh_failed_module_with_last_mod_time() =
   failed_imports = failed_imports.filterIt(it.time == getLastModificationTime(it.fullname))

var native_import_procs {.compileTime.} : string

macro vmops(ctx: PCtx, op: untyped, argtypes: varargs[untyped]): untyped =
   let op_wrapper = ident($op & "_wrapper")
   let a = ident("a")
   var call_op = newCall(op)
   for i, arg in argtypes:
      let get_arg_name = ident("get" & ($arg).capitalizeAscii)
      call_op.add newCall(get_arg_name).add(a, newLit(i))

   quote do:
      proc `op_wrapper`(`a`: VmArgs) {.nimcall.} =
         setResult(`a`, `call_op`)
      `ctx`.registerCallback(`op`.ast_to_str, `op_wrapper`)

macro vm_native(ctx: PCtx, list: untyped): untyped =
   var vmops_calls = newStmtList()
   for p in list:
      if p.kind in [nnkProcDef, nnkFuncDef]:
         var op = p.name
         var pcall = newCall("vmops", `ctx`, `op`)

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

proc count_triples(s: string): int =
  var i = 0
  while i+2 < s.len:
    if s[i] == '"' and s[i+1] == '"' and s[i+2] == '"':
      inc result
      inc i, 2
    inc i

proc continue_line*(line: string): bool =
   line.len > 0 and
      ((line[^1] in indent_oprs) or indent_keys.anyIt(line.endsWith(it)))

proc is_all_space(line: string): bool =
   line == "" or line.allIt(it == ' ')

proc is_import_line(s: string): bool =
   let s = s.strip
   s.startsWith("import ") or s.startsWith("from ") or s.startsWith("include ")

proc disable_stdout() =
   discard reopen(stdout, "NUL", fmWrite)

proc enable_stdout() =
   discard reopen(stdout, "CON", fmWrite)

proc get_prompt(indent_level, line_no: int): string =
   if restart_eval:
      restart_eval = false
      "01>>> "
   else:
      let prompt_str = if indent_level == 0: ">>> " else: ">++ "
      &"{line_no:<02}{prompt_str}{indent_spaces.repeat(indent_level)}"

proc show_raw_buffer(buffer: string, header: string) =
   with_color(fgCyan, false):
      echo header.center(70, '-')

   with_color(fgYellow, false):
      echo buffer.strip(leading = false)

   with_color(fgCyan, false):
      echo '-'.repeat(70)

proc save_nims_cache_file(lines: seq[string]) =
   if save_nims_code:
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

when false:
   # fix when time avalaible
   proc selectUniqueSymbol(graph: ModuleGraph, module: PSym, name: string;
                            symKinds: set[TSymKind] = {skLet, skVar}): PSym =
      let n = getIdent(graph.cache, name)
      var it: ModuleIter
      var s = initModuleIter(it, graph, module, n)
      result = nil
      while s != nil:
         if s.kind in symKinds:
            if result == nil: result = s
            else: return nil # ambiguous
         s = nextModuleIter(it, graph)

   proc get_global_value(name: string): PNode =
      let v = selectUniqueSymbol(cur_graph, cur_module, name)
      if v.isNil:
         nil
      else:
         vm.getGlobalValue(PCtx cur_graph.vm, v)

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

proc my_read_line(line_no: int): string =
   template args(n: int, s: string): string = (if cmds.len > n: cmds[n] else: s)
   template argn[T: float|int](n: int, v: T): T =
      if cmds.len > n:
         when T is int: parseInt(cmds[n])
         else: parseFloat(cmds[n])
      else: v

   template add_line() =
      buffer &= myline & "\p"
      inc(line_no)

   template onoff(v: bool): string = (if v: "on" else: "off")

   template doCmd(cmd: string) =
      case cmd
      of "help", "h":
         with_color(fgCyan, false):
            echo ":help   [\\h]: Show help."
            echo ":clear  [\\c]: Clear the input code."
            echo ":show   [\\s]: Show the current code."
            echo ":paste  [\\p]: Enable/Disable the paste mode."
            echo ":except [\\e]: Enable/Disable the except to reset mode."
            echo ":ic     [\\ic]:Enable/Disable the incremental cache."
            echo ":option [\\o]: Show current options."
            echo ":reset  [\\r]: Reset the vm to init state."
            echo ":exit   [\\q]: Exit the program."
      of "exit", "quit", "q", "x":
         quit()
      of "verbose", "debug", "v", "d":
         verbose = not verbose
         setForegroundColor(fgCyan)
         with_color(fgCyan, false):
            echo "Debug mode is " & verbose.onoff
      of "paste", "p":
         paste_mode = not paste_mode
         with_color(fgCyan, false):
            echo "Paste mode is " & paste_mode.onoff
      of "exceptmode", "xm", "except":
         exception_to_reset_module = not exception_to_reset_module
         with_color(fgCyan, false):
            echo "Exception reset mode is " & exception_to_reset_module.onoff
      of "ic", "iccache":
         using_ic_cache = not using_ic_cache
         with_color(fgCyan, false):
            echo "Using incremental cache is " & using_ic_cache.onoff
      of "errormode", "em", "error":
         error_to_reload_code = not error_to_reload_code
         with_color(fgCyan, false):
            echo "Error reload mode is " & error_to_reload_code.onoff
      of "savecode", "sc", "cache":
         save_nims_code = not save_nims_code
         with_color(fgCyan, false):
            echo "Save nims code is " & save_nims_code.onoff
      of "show", "s":
         show_raw_buffer(input_lines_good.join(""), "Current buffer")
      of "maxerrors", "me":
         if cmds.len > 1:
            max_compiler_errors = argn(1, 10)
         with_color(fgCyan, false):
            echo "Max compiler errors is " & $max_compiler_errors
      of "clean", "clear", "c":
         if input_lines_good.len > 0:
            let clear_line_count = argn(1, -1)
            if clear_line_count < 0 or clear_line_count >= input_lines_good.len:
               input_lines_good = @[]
               with_color(fgCyan, false):
                  echo "Input buffer is empty"
               save_nims_cache_file(input_lines_good)
            else:
               input_lines_good = input_lines_good[0..^(clear_line_count+1)]
               show_raw_buffer(input_lines_good.join(""), "Current buffer")
               save_nims_cache_file(input_lines_good)
      of "keep", "k":
         if input_lines_good.len > 0:
            var keep_line_count = argn(1, -1)
            if keep_line_count == 0:
               input_lines_good = @[]
               with_color(fgCyan, false):
                  echo "Input buffer is empty"
               save_nims_cache_file(input_lines_good)
            elif keep_line_count > 0 and keep_line_count < input_lines_good.len:
                  input_lines_good = input_lines_good[0..(keep_line_count-1)]
                  show_raw_buffer(input_lines_good.join(""), "Current buffer")
                  save_nims_cache_file(input_lines_good)
      of "load", "ll":
         input_lines_good = load_nims_cache_file()
         raise Reload()
      of "check":
         when false:
            let s = args(1, "")
            if s != "":
               if get_global_value(s).isNil:
                  echo "no sym:", s
               else:
                  echo "has sym:", s
      of "options", "option", "o":
         with_color(fgCyan, false):
            echo "Exception reset mode is " & exception_to_reset_module.onoff
            echo "Error reload mode is " & error_to_reload_code.onoff
            echo "Save nims code is " & save_nims_code.onoff
            echo "Paste mode is " & paste_mode.onoff
            echo "Using incremental cache is " & using_ic_cache.onoff
            # echo "Debug mode is " & verbose.onoff
            echo "Max compiler errors is " & $max_compiler_errors
      of "config":
         with_color(fgCyan, false):
            echo "SymbolFiles: ", cur_conf.symbolFiles
            echo "GC: ", cur_conf.selectedGC
            echo "Options: ", cur_conf.options
            echo "GlobalOptions: ", cur_conf.globalOptions
      of "reload", "rr":
         raise Reload()
      of "reset", "r", "rs", "rb":
         if cmd == "rs":
            input_lines_good = @[]
            save_nims_cache_file(input_lines_good)

         if cmd == "rb":
            failed_imports = @[]
         else:
            # 手工reset，需要检查编译失败的模块时候需要重新加载
            check_failed_module_time = true

         raise Reset()
      else:
         with_color(fgRed, false):
            echo "Unknown command [$#]." % cmds[0]

   var
      buffer = ""
      indent_level = 0
      line_no = line_no
      triples = 0

   while true:
      var (myline, is_paste) = readLineFromStdin(get_prompt(indent_level, line_no+2))

      if paste_mode:
         paste_mode = false
         add_line()
         continue

      if myline.len > 0 and myline[0] == '#':
         paste_mode = true
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

   if verbose:
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

proc get_line(lineno: int): string =
   if last_line_need_reset:
      # 出现代码错误，抛出异常后重置环境
      last_line_need_reset = false
      raise Reset()

   if last_line_has_error:
      last_line_has_error = false

      if error_to_reload_code:
         raise Reload()
      else:
         # 由于出现语法错误的时候，有时会导致下一次输出出现问题，所以
         # 就发送一条无关紧要的语句，修正输出
         # 比如输入 &"{\"xx"}" 就会导致下一条语句没有输出（如果没有下面的语句的话）
         # 不过好像现在又正常了，先不用吧

         when false:
            disable_output(cur_conf)
            last_input_line = ""
            return "echo \" \""

   if lineno == 0:
      if input_lines_good.len > 0:
         # 当有初始化代码的时候，不做任何输出
         disable_output(cur_conf)

      last_input_line = ""
      return pre_load_code & input_lines_good.join("")
   else:
      if last_input_line != "":
         input_lines_good.add last_input_line
         save_nims_cache_file(input_lines_good)

      last_input_line = my_read_line(lineno)
      last_line_is_import = last_input_line.is_import_line
      if last_line_is_import:
         cur_error_count = cur_conf.errorCounter

      return last_input_line

proc llReadFromStdin(s: PLLStream, buf: pointer, bufLen: int): int =
   # 读取代码前确保输出正常
   enable_output(cur_conf)

   if s.lineOffset < 0:
      s.lineOffset = 0

   s.rd = 0
   s.s = get_line(s.lineOffset)

   inc(s.lineOffset)
   result = min(bufLen, s.s.len - s.rd)
   if result > 0:
      copyMem(buf, addr(s.s[s.rd]), result)
      inc(s.rd, result)

proc on_compile_error(conf: ConfigRef; info: TLineInfo; msg: string; severity: Severity) {.gcsafe.} =
   {.gcsafe.}:
      if severity == Error and conf.m.errorOutputs.len != 0:
         if last_line_is_import:
            # 出现import错误，一般需要reset虚拟机环境，否则会出各自异常
            # 这里不能直接抛出Reset异常，因为我们还需要输出异常信息
            last_line_need_reset = true

            if conf.errorCounter - cur_error_count >= max_compiler_errors:
               with_color(fgRed, false):
                  echo "Too many error occured, skip..."

               # 这里可以直接抛出异常了, 不需要屏蔽输出了
               raise Reset()
         else:
            last_line_has_error = true

proc interactivePasses(graph: ModuleGraph) =
   initDefines(graph.config.symbols)
   defineSymbol(graph.config.symbols, "nimconfig")
   defineSymbol(graph.config.symbols, "nimscript")
   when hasFFI:
      defineSymbol(graph.config.symbols, "nimffi")
      defineSymbol(graph.config.symbols, "nimHasLibFFI")
   when my_special_vmops:
      defineSymbol(graph.config.symbols, "nimVmops")
   undefSymbol(graph.config.symbols, "nimv2")
   registerPass(graph, semPass)
   registerPass(graph, evalPass)

proc now(): string = times.now().format("HH:mm:ss")
proc today(): string = times.now().format("yyyy-MM-dd")

proc run_repl*(r: TLLRepl, libpath: string, libs: openArray[string], imports: seq[string]) =
   var conf = newConfigRef()
   var cache = newIdentCache()
   var graph = newModuleGraph(cache, conf)
   cur_graph = graph

   conf.searchPaths.add libpath.AbsoluteDir
   for p in libs:
      let p = p.AbsoluteDir
      conf.searchPaths.add(p)

   conf.libpath = libpath.AbsoluteDir
   conf.cmd = cmdInteractive
   conf.errorMax = high(int)
   conf.spellSuggestMax = 0
   conf.options.excl optHints
   conf.globalOptions.excl {optTinyRtti, optOwnedRefs, optSeqDestructors}
   conf.features.incl vmopsDanger

   # 使用incremental compile cache, 目前看起来好像对模块加载速度没有多大提高
   if using_ic_cache:
      conf.symbolFiles = v2Sf
      conf.cCompiler = ccNone
      conf.selectedGC = gcUnselected
      conf.options = {}
      conf.globalOptions = {}

   when hasFFI:
      conf.features.incl compiletimeFFI

   conf.structuredErrorHook = on_compile_error
   cur_conf = conf

   interactivePasses(graph)
   var m = graph.makeStdinModule()
   incl(m.flags, sfMainModule)
   cur_module = m

   var idgen = idGeneratorFromModule(m)
   var ctx = setupVM(m, cache, "stdin", graph, idgen)

   when my_special_vmops:
      ctx.vm_native:
         proc httpget(url: string): string
         proc httppost(url, body: string): string
         func make_console_codepage(s: string): string
         func make_gb(s: string): string
         func make_tchar(s: string): string
         func make_utf8(s: string): string
         func cpu_time(): float
         func epoch_time(): float
         proc now(): string
         proc today(): string

   graph.vm = ctx
   graph.compileSystemModule()

   # 将注册的API作为一个模块自动import
   when my_special_vmops:
      const native_import_procs_def = native_import_procs
      let sf = getTempDir() / "scriptapi.nim"
      block:
         let file = open(sf, fmWrite)
         file.write(native_import_procs_def)
         file.close

      conf.implicitImports.add sf
      discard graph.compileModule(fileInfoIdx(conf, AbsoluteFile sf), {})

   template tryCompile(f: string): bool =
      var ok: bool
      let mf = findFile(conf, f & ".nim")
      if not mf.isEmpty:
         last_line_is_import = true
         last_line_need_reset = false
         try:
            discard graph.compileModule(fileInfoIdx(conf, mf), {})
         except:
            last_line_need_reset = true
         finally:
            if last_line_need_reset:
               last_line_need_reset = false
               add_failed_module(f, mf.string)
               raise Reset()

            ok = not last_line_need_reset
            last_line_is_import = false
      else:
         ok = false
      ok

   if check_failed_module_time:
      check_failed_module_time = false
      refresh_failed_module_with_last_mod_time()

   var pre_compile_module: seq[string]

   # 预编译这些模块，这样在出现异常重新加载的时候，就不需要重新解析了
   const pre_load_module = @["strutils", "strformat", "os", "tables", "sets", "math", "json", "macros"]
   for f in pre_load_module & imports:
      if not is_failed_module(f) and tryCompile(f):
         pre_compile_module.add f

   # 缺省import的模块
   pre_load_code = "import " & pre_compile_module.join(",") & "\p"

   # 存在3种类型的出错：
   # 1. 输入代码语法错，一般不需要额外操作，只是把错误的代码忽略就可以
   # 2. 输入代码抛出异常，这个时候原来的代码建立的环境会失效，需要重新执行一遍代码，就是reload
   # 3. 如果输入import times这种，可能会破坏整个vm，这个时候需要重建整个环境，就是reset
   while true:
      try:
         last_line_need_reset = false
         last_line_has_error = false
         processModule(graph, m, idgen, llStreamOpenStdIn(r))
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

         if exception_to_reset_module:
            break

proc ctrl_c_proc*() {.noconv.} =
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

   let imports = args.filterIt(not it.startsWith("-"))
   if args.anyIt(it.startsWith("-cache") or it.startsWith("--cache")):
      save_nims_code = true
      input_lines_good = load_nims_cache_file()

   set_control_chook(ctrl_c_proc)
   while true:
      try:
         restart_eval = true
         run_repl(llReadFromStdin, nimlib, libs, imports)
      except:
         discard

when isMainModule:
   main()
