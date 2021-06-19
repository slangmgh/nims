##
## Simple nim repl
##
## Compile with libffi, must use gcc, libffi doesn't support msvc
## >>> nimble install libffi
## >>> nim c --cc:gcc -d:release -d:nimcore -d:nimHasLibFFI nims.nim
##
## Compile without libffi
## >>> nim c -d:release -d:nimcore nims.nim
##

import os, terminal, strutils, sequtils, times, macros, strformat, parseopt
import "../../compiler" / [ast, astalgo, modules, passes, condsyms,
       options, sem, semdata, llstream, vm, vmdef, nimeval, lineinfos, msgs,
       modulegraphs, idents, pathutils, passaux, scriptconfig, parser]

# Import segfaults so we can catch NilAccessDefect
# rather than crash the program and quit
import segfaults

const my_special_vmops = defined(myvmops)

when my_special_vmops:
   import httputils, guessencoding
   import winutils

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
      opt_exception_to_reset_module
      opt_import_error_to_reset_module
      opt_error_to_reload_code
      opt_auto_create_var
      opt_paste_by_input_time_elapse
      opt_paste_mode

   RunContext = ref object
      conf: ConfigRef
      graph: ModuleGraph
      main_module: PSym
      idgen: IdGenerator

      input_stream: PLLStream

      libpath: string
      libs: seq[string]
      imports: seq[string]
      scriptapi_import: string

      options: set[RunOption]
      max_compiler_errors: int

      failed_imports: seq[tuple[name: string, fullname: string, time: Time]]

      last_input_line: string
      last_line_is_import: bool
      last_line_has_error: bool
      last_line_need_reset: bool
      check_failed_module_time: bool

      pre_load_code: string
      input_lines_good: seq[string]

      saved_stdout: FileHandle
      saved_stderr: FileHandle

proc init(ctx: RunContext) =
   ctx.last_line_need_reset = false
   ctx.last_line_has_error = false
   ctx.last_line_is_import = false
   ctx.last_input_line = ""
   if not ctx.input_stream.isNil:
      ctx.input_stream.lineOffset = -1
      ctx.input_stream.s = ""

proc vm(ctx: RunContext): PCtx = PCtx ctx.graph.vm

proc copy(ctx: RunContext): RunContext =
   RunContext(
      conf: newConfigRef(),
      libpath: ctx.libpath,
      libs: ctx.libs,
      max_compiler_errors: ctx.max_compiler_errors,
      failed_imports: ctx.failed_imports,
      scriptapi_import: ctx.scriptapi_import
   )

template process_switch_on_off(o: RunOption, val: string) =
   block:
      let s = if val == "": "on" else: val
      if s in ["on", "1"]:
         ctx.options.incl o
      elif s in ["off", "0"]:
         ctx.options.excl o
      else:
         echo "Option value must be 'on' or 'off'."

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

const
   sImport = "import "
   sInclue = "include "
   sFrom = "from "

func is_import_line(s: string): bool =
   s.startsWith(sImport) or s.startsWith(sFrom) or s.startsWith(sInclue)

proc get_prompt(indent_level, line_no: int): string =
   let prompt_str = if indent_level == 0: ">>> " else: ">++ "
   &"{line_no}{prompt_str}{indent_spaces.repeat(indent_level)}"

proc show_raw_buffer(buffer: string, header: string) =
   with_color(fgCyan, false):
      echo header.center(70, '-')

   var lineno = 1
   for s in buffer.strip.splitLines:
      with_color(fgCyan, false):
         stdout.write(&"{($lineno & \".\"):<4}")
      with_color(fgYellow, false):
         echo s
      inc(lineno)

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

type ResetError* = object of CatchableError
type ReloadError* = object of CatchableError

template Reset(): untyped = newException(ResetError, "Reset the vm")
template Reload(): untyped = newException(ReloadError, "Reload the code")

proc print_loaded_module(graph: ModuleGraph) =
   echo &"Total loaded module: {graph.ifaces.len}"

   let xlen = graph.ifaces.len
   if xlen >= 0:
      var conf = graph.config
      for i in 0..xlen-1:
         let f = toFullPath(conf, FileIndex i)
         echo &"idx: {i}, name: {f}"

proc print_module_export_syms(graph: ModuleGraph, m: PSym) =
   for s in allSyms(graph, m):
      echo s

proc print_module_syms(graph: ModuleGraph, m: PSym) =
   let interf = semtabAll(graph, m)
   echo "Symbol counts:", interf.counter
   for s in interf:
      echo &"{s.kind} {s.name.s}: {s.typ.kind}"

proc print_global_values(graph: ModuleGraph) =
   let c = PCtx graph.vm
   echo "Total globals:", c.globals.len
   let xlen = c.globals.len
   for i in 0..<xlen:
      let n = c.globals[i][]
      echo n.info.line, n


proc is_var_exists(graph: ModuleGraph, m: PSym, name: string): bool =
   let interf = semtabAll(graph, m)
   for s in interf:
      if s.kind in {skLet, skVar} and s.name.s == name:
         return true

   return false

proc readLineFromStdin(ctx: RunContext, prompt: string): (string, bool) =
   let time_start = cpuTime()
   stdout.write(prompt)

   # We must use flush to ensure the output is visible, becasue after
   # redirect, without newline, the text may not be flush to the console
   # Because we already use non buffered stdout, so it is no need to call
   # flush, but anyway, call it do no harm.
   flushFile(stdout)

   let s = readLine(stdin)
   let time_end = cpuTime()
   let is_paste =
      if opt_paste_by_input_time_elapse.on:
         when my_special_vmops:
            let hwnd = find_window("TPHotkeyMain", visible = false)
            if not hwnd.isNil and send_message(hwnd, WM_USER + 11, 0, 0) == 2:
               true
            else:
               time_end - time_start < 0.08
         else:
            time_end - time_start < 0.08
      else:
         false
   (s, is_paste)

## paste mode
## don't do any indent, add the code directly
## it is used to paste code to terminal
##
## paste mode is triggered at following situation:
## 1. use :paste command, must using :go to execute code
## 2. The code starts with '#', must using :go to execute code
## 3. When the readLine call take very small time, less than 0.08 seconds
##    Using paste-by-time-elapse to enable it
##

proc my_read_line(ctx: RunContext): string =
   template args(n: int, s: string): string = (if cmds.len > n: cmds[n] else: s)
   template argn[T: float|int](n: int, v: T): T =
      if cmds.len > n:
         when T is int: parseInt(cmds[n])
         else: parseFloat(cmds[n])
      else: v

   template add_line() =
      if buffer == "":
         buffer &= myline.strip(trailing = false) & "\p"
      else:
         buffer &= myline & "\p"
      inc(line_no)

   template onoff(v: RunOption): string = (if v in ctx.options: "on" else: "off")

   template doCmd(cmd: string) =
      case cmd
      of "help", "h":
         with_color(fgCyan, false):
            echo ":help, :h                  : Show help."
            echo ":clear, :c NUM             : Clear the last NUM line or all codes."
            echo ":keep, :k NUM              : Keep the first NUM like codes."
            echo ":show, :s                  : Show the current code in buffer."
            echo ":paste, :p [on|off]        : Show/toggle the paste mode."
            echo ":cache [on|off]            : Show/toggle the auto save/load the script codes."
            echo ":auto-create-var [on|off]  : Show/toggle auto create var when not exist."
            echo ":error-to-reload [on|off]  : Show/toggle syntax error to reload mode."
            echo ":max-errors [NUM]          : Show/set max compiler errors to NUM."
            echo ":option, :o                : Show current options."
            echo ":reload, :r                : Reload the code manually."
            echo ":reset, :rr                : Reset the vm to manually."
            echo ":go                        : Execute code in paste mode."
            echo ":exit, :q, :x              : Exit the program."
      of "exit", "quit", "q", "x":
         quit()
      of "go":
         return buffer
      of "verbose", "v", "d":
         if cmds.len > 1:
            process_switch_on_off(opt_verbose, cmds[1])
         with_color(fgCyan, false):
            echo "Verbose mode is " & opt_verbose.onoff
      of "paste-by-time-elapse", "pte", "tep":
         if cmds.len > 1:
            process_switch_on_off(opt_paste_by_input_time_elapse, cmds[1])
         with_color(fgCyan, false):
            echo "Paste according to input time elapse(pte): " & opt_paste_by_input_time_elapse.onoff
      of "paste", "p":
         if cmds.len > 1:
            process_switch_on_off(opt_paste_mode, cmds[1])
         with_color(fgCyan, false):
            echo "Paste mode(p): " & opt_paste_mode.onoff
            if opt_paste_mode.on:
               echo "Please input command ':go' to execute code."
      of "auto-save-code", "asc", "cache":
         if cmds.len > 1:
            process_switch_on_off(opt_save_nims_code, cmds[1])
         with_color(fgCyan, false):
            echo "Auto save/load script code(asc): " & opt_save_nims_code.onoff
      of "show", "s":
         show_raw_buffer(ctx.input_lines_good.join(""), "Current buffer")
      of "max-errors", "me":
         if cmds.len > 1:
            ctx.max_compiler_errors = argn(1, ctx.max_compiler_errors)
         with_color(fgCyan, false):
            echo "Max compiler errors(me): " & $ctx.max_compiler_errors
      of "clean", "clear", "c":
         if ctx.input_lines_good.len > 0:
            ctx.input_lines_good = ctx.input_lines_good.join("").strip.split_lines.mapIt(it & "\p")
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
            ctx.input_lines_good = ctx.input_lines_good.join("").strip.split_lines.mapIt(it & "\p")
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
      of "auto-create-var", "acv":
         if cmds.len > 1:
            process_switch_on_off(opt_auto_create_var, cmds[1])
         with_color(fgCyan, false):
            echo "Auto create variable(acv) " & opt_auto_create_var.onoff
      of "error-to-reload", "setr", "sem":
         if cmds.len > 1:
            process_switch_on_off(opt_error_to_reload_code, cmds[1])
         with_color(fgCyan, false):
            echo "Syntax error to reload mode(setr) " & opt_error_to_reload_code.onoff
      of "except-to-reset", "eetr", "eem":
         if cmds.len > 1:
            process_switch_on_off(opt_exception_to_reset_module, cmds[1])
         with_color(fgCyan, false):
            echo "Exception error to reset mode(eetr): " & opt_exception_to_reset_module.onoff
      of "import-error-to-reset", "ietr", "iem":
         if cmds.len > 1:
            process_switch_on_off(opt_import_error_to_reset_module, cmds[1])
         with_color(fgCyan, false):
            echo "Import error to reset mode(ietr): " & opt_import_error_to_reset_module.onoff
      of "options", "option", "o":
         with_color(fgCyan, false):
            echo "Syntax error to reload mode(setr): " & opt_error_to_reload_code.onoff
            echo "Exception error to reset mode(eetr): " & opt_exception_to_reset_module.onoff
            echo "Import error to reset mode(ietr): " & opt_import_error_to_reset_module.onoff
            echo "Auto create variable(acv): " & opt_auto_create_var.onoff
            echo "Auto save/load script code(asc): " & opt_save_nims_code.onoff
            echo "Paste according to input time elapse(pte): " & opt_paste_by_input_time_elapse.onoff
            echo "Paste mode(p): " & opt_paste_mode.onoff
            echo "Max compiler errors(me): " & $ctx.max_compiler_errors
      of "load", "ll":
         ctx.input_lines_good = load_nims_cache_file()
         if opt_verbose.on:
            with_color(fgRed, false):
               echo "Load code from cache file."
         raise Reload()
      of "reload", "r", "rs":
         if cmd == "rs": # Clear the input buffer before reset
            ctx.input_lines_good = @[]
            if opt_verbose.on:
               with_color(fgRed, false):
                  echo "Clear the code buffer."
            if opt_save_nims_code.on:
               save_nims_cache_file(ctx.input_lines_good)

         if opt_verbose.on:
            with_color(fgRed, false):
               echo "Reload the code."
         raise Reload()
      of "reset", "rr", "rrs", "rrb":
         if cmd == "rrs": # Clear the input buffer before reset
            ctx.input_lines_good = @[]
            if opt_verbose.on:
               with_color(fgRed, false):
                  echo "Clear the code buffer."
            if opt_save_nims_code.on:
               save_nims_cache_file(ctx.input_lines_good)

         if cmd == "rrb": # Clear the failed import module before reset
            ctx.failed_imports = @[]
         else:
            # Reset vm manually，we need to check the modified time of failed module
            # to see if it need reload
            ctx.check_failed_module_time = true

         if opt_verbose.on:
            with_color(fgRed, false):
               echo "Reset the vm environment."
         raise Reset()
      of "print-loaded-module", "plm":
         with_color(fgCyan, false):
            print_loaded_module(ctx.graph)
      of "print-module-syms", "pms":
         let idx = argn(1, 0)
         if idx >= ctx.graph.ifaces.len:
            with_color(fgCyan, false):
               echo "Max module number is: ", ctx.graph.ifaces.len - 1
         else:
            with_color(fgCyan, false):
               print_module_syms(ctx.graph, getModule(ctx.graph, FileIndex idx))
      of "print-global-values", "pgv":
         with_color(fgCyan, false):
            print_global_values(ctx.graph)
      else:
         with_color(fgRed, false):
            echo &"Unknown command {cmds[0]}."

   var
      buffer = ""
      indent_level = 0
      triples = 0
      line_no = 1
      manual_paste_mode = false

   const cmds_no_colon = ["help", "go", "exit", "quit", "reload", "reset", "option"]

   while true:
      var (myline, is_time_elapse_paste) = readLineFromStdin(ctx, get_prompt(indent_level, line_no))

      if myline in cmds_no_colon:
         myline = ":" & myline

      let cmds = myline.replace(',', ' ').splitWhitespace
      if cmds.len > 0 and cmds[0].len > 0:
         case cmds[0][0]
         of ':', '\\':
            doCmd(cmds[0][1..^1].replace('_', '-'))
            continue
         of '!':
            discard execShellCmd(myline.strip[1..^1])
            continue
         else:
            discard

      if manual_paste_mode or opt_paste_mode.on:
         add_line()
         continue

      if buffer == "" and myline.len > 0 and myline[0] == '#':
         with_color(fgCyan, false):
            echo "In one-time paste mode."
            echo "Please input command ':go' to execute code."
         manual_paste_mode = true
         continue

      if is_time_elapse_paste:
         add_line()
         continue

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

when defined(windows):
   proc c_dup(oldfd: FileHandle): FileHandle {.importc: "_dup", header: "<io.h>".}
   proc c_dup2(oldfd: FileHandle, newfd: FileHandle): cint {.importc: "_dup2", header: "<io.h>".}
   proc c_close(fd: FileHandle): cint {.importc: "_close", header: "<io.h>".}
else:
   proc c_dup(oldfd: FileHandle): FileHandle {.importc: "dup", header: "<unistd.h>".}
   proc c_dup2(oldfd: FileHandle, newfd: FileHandle): cint {.importc: "dup2", header: "<unistd.h>".}
   proc c_close(fd: FileHandle): cint {.importc: "close", header: "<unistd.h>".}

var IOLBF {.importc: "_IOLBF", nodecl, header: "<stdio.h>".}: cint
var IONBF {.importc: "_IONBF", nodecl, header: "<stdio.h>".}: cint
proc c_setvbuf(f: File, buf: pointer, mode: cint, size: csize_t): cint {.
  importc: "setvbuf", header: "<stdio.h>", tags: [].}

proc disable_stdout(ctx: RunContext) =
   const device = when defined(windows): "NUL:" else: "/dev/null"
   template do_with(con: untyped) =
      ctx.`saved con` = c_dup(con.getFileHandle)
      discard reopen(con, device, fmWrite)

      # Set the stdout/stderr to no buffer, so stdout.write need not flush to display
      discard c_setvbuf(con, nil, IONBF, 0)
      flushFile(con)

   # We cannot call setStdIoUnbuffered, because set stdin to unbuffered
   # will make the program close console and run in dead cycle after using doskey F7/F8
   # function with cmd.exe.

   do_with(stdout)
   do_with(stderr)

proc enable_stdout(ctx: RunContext) =
   const device = when defined(windows): "CON:" else: "/dev/tty"

   template do_with(con: untyped) =
      if ctx.`saved con` != FileHandle(-1):
         discard c_dup2(ctx.`saved con`, con.getFileHandle)
         flushFile(con)
         discard c_close(ctx.`saved con`)
         ctx.`saved con` = FileHandle(-1)
      else:
         discard reopen(con, device, fmWrite)

   do_with(stdout)
   do_with(stderr)

proc my_msg_writeln_hook(msg: string) =
   discard

proc disable_output(ctx: RunContext) =
   ctx.conf.writelnHook = my_msg_writeln_hook
   disable_stdout(ctx)

proc enable_output(ctx: RunContext) =
   if not ctx.conf.writelnHook.isNil:
      ctx.conf.writelnHook = nil
      enable_stdout(ctx)

proc get_line(ctx: RunContext): string =
   if ctx.last_line_need_reset:
      # When error on import, we need to reset the VM or reload the code
      # according the config option.
      #
      # If we compile module before import, this code will never be
      # triggered, because import always successful.

      ctx.last_line_need_reset = false

      if opt_import_error_to_reset_module.on:
         raise Reset()
      else:
         raise Reload()

   if ctx.last_line_has_error:
      ctx.last_line_has_error = false

      if opt_error_to_reload_code.on or
         ctx.last_input_line.startsWith("var ") or ctx.last_input_line.startsWith("let "):
         # Sometime syntax error will make scope context error, so maybe we need reload
         ctx.last_input_line = ""
         raise Reload()
      else:
         # Sometime syntax error will make the next line code doesn't output result,
         # so we add an empty echo to fix this.
         # For example, input &"{\"xx"}" will make the display disappear sometime, it
         # not always true of cause.

         ctx.last_input_line = ""
         disable_output(ctx)
         return "echo \" \""

   if ctx.last_input_line != "":
      if ctx.input_lines_good.len == 0 or ctx.input_lines_good[^1] != ctx.last_input_line:
         ctx.input_lines_good.add ctx.last_input_line
         if opt_save_nims_code.on:
            save_nims_cache_file(ctx.input_lines_good)

   ctx.last_input_line = my_read_line(ctx)

   return ctx.last_input_line

proc reinit_vm_state(ctx: RunContext) =
   # Reset some variable before code execute
   ctx.conf.errorCounter = 0
   var vm = ctx.vm
   vm.oldErrorCount = 0
   vm.mode = emRepl
   refresh(vm, ctx.main_module, ctx.idgen)

proc safe_compile_module(ctx: RunContext, mf: AbsoluteFile): bool =
   var
      conf = ctx.conf
      success = true

   proc on_compile_error(conf: ConfigRef; info: TLineInfo; msg: string; severity: Severity) {.gcsafe.} =
      if severity == Error and conf.m.errorOutputs.len != 0:
         success = false

   let old_hook = conf.structuredErrorHook
   conf.structuredErrorHook = on_compile_error
   reinit_vm_state(ctx)
   try:
      discard ctx.graph.compileModule(fileInfoIdx(conf, mf), {})
   except:
      success = false
   finally:
      conf.structuredErrorHook = old_hook

   success

proc get_imports_from_line(line: string): seq[string] =
   if line.find('[') >= 0:
      with_color(fgRed, false):
         echo "Complex import with '[', ']' is not supportted."
   else:
      let line = line.replace("\p", "").strip
      if line.startsWith(sImport):
         var endpos = line.find(" except ")
         if endpos < 0:
            endpos = line.len - 1
         result = line[sImport.len..endpos].replace(" ", "").split(',').mapIt(it.strip)
      elif line.startsWith(sInclue):
         result = line[sInclue.len..^1].replace(" ", "").split(',').mapIt(it.strip)
      elif line.startsWith(sFrom):
         let endpos = line.find(" import ")
         if endpos < 0:
            echo "Import from without import."
         else:
            result = @[line[sFrom.len..endpos].strip]

proc compile_import_module(ctx: RunContext) =
   var ok_imports: seq[string]
   var imports = get_imports_from_line(ctx.last_input_line)
   for f in imports:
      if not is_failed_module(ctx, f):
         let mf = findFile(ctx.conf, f & ".nim")
         if not mf.isEmpty:
            if safe_compile_module(ctx, mf):
               ok_imports.add(f)
            else:
               ctx.add_failed_module(f, mf.string)

   if ok_imports.len > 0:
      if ctx.last_input_line.startsWith(sImport) and
         ctx.last_input_line.find(" except ") < 0 and
         ctx.last_input_line.find(" as ") < 0:
         ctx.last_input_line = sImport & ok_imports.join(", ") & "\p"
      elif ctx.last_input_line.startsWith(sImport):
         ctx.last_input_line = sInclue & ok_imports.join(", ") & "\p"
      else: # from ... import ... / import ... except ... / import ... as ...
         discard
   else:
      ctx.last_input_line = ""

proc check_var_set_value(ctx: RunContext): bool =
   # var a = 1; var a = 2; echo a; will output 1
   # so we need remove "var " from the second statement
   if ctx.last_input_line.startsWith("var ") or ctx.last_input_line.startsWith("let "):
      if ctx.last_input_line.find('=') >= 0:
         let vars = ctx.last_input_line[4..^1].split('=')[0].split(',').mapIt(it.strip.split(':')[0])
         for v in vars:
            if is_var_exists(ctx.graph, ctx.main_module, v):
               ctx.last_input_line = ctx.last_input_line[4..^1].strip(trailing = false)
               return true
   elif opt_auto_create_var.on and ctx.last_input_line.find('=') >= 0:
      let v = ctx.last_input_line.split('=')[0].strip
      if v.validIdentifier and not is_var_exists(ctx.graph, ctx.main_module, v):
         ctx.last_input_line = "var " & ctx.last_input_line
         return true
   return false

proc setup_input_stream(ctx: RunContext) =
   proc llReadFromStdin(s: PLLStream, buf: pointer, bufLen: int): int =
      # Ensure the output is fine
      enable_output(ctx)

      s.rd = 0
      if s.lineOffset < 0:
         # This line indicate that the code will not be added to input_lines_good
         ctx.last_input_line = ""

         s.s = ctx.pre_load_code & ctx.input_lines_good.join("")
         if opt_verbose.on:
            with_color(fgRed, false):
               echo "Run startup code:"
            with_color(fgCyan, false):
               echo s.s

         # When the code reloaded or vm reset, we need to re-execute the saved code,
         # at this time, we should disable output, or else the output will confuse
         # the user.
         disable_output(ctx)
      else:
         s.s = get_line(ctx)
         ctx.last_line_is_import = ctx.last_input_line.is_import_line
         if ctx.last_line_is_import:
            compile_import_module(ctx)
            s.s = ctx.last_input_line
         elif check_var_set_value(ctx):
            s.s = ctx.last_input_line

      # Set the lineOffset to 0, so the syntax error's line number will be same
      # with the line number in input prompt
      s.lineOffset = 0

      reinit_vm_state(ctx)

      result = min(bufLen, s.s.len - s.rd)
      if result > 0:
         copyMem(buf, addr(s.s[s.rd]), result)
         inc(s.rd, result)

   ctx.input_stream = llStreamOpenStdIn(llReadFromStdin)

proc setup_config_error_hook(ctx: RunContext) =
   proc on_compile_error(conf: ConfigRef; info: TLineInfo; msg: string; severity: Severity) {.gcsafe.} =
      if severity == Error and conf.m.errorOutputs.len != 0:
         if ctx.last_line_is_import:
            # When import error occured, the VM environment will be ruined,
            # so we need reset the VM environment, we set flag here untill
            # some errors displayed
            ctx.last_line_need_reset = true

            # If we compile module before import, this code will never be
            # triggered, because import always successful
            if conf.errorCounter >= ctx.max_compiler_errors:
               with_color(fgRed, false):
                  echo "Too many error occured, skip..."
         else:
            ctx.last_line_has_error = true

   ctx.conf.structuredErrorHook = on_compile_error

proc register_custom_vmops(vm: PEvalContext, ctx: RunContext) =
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

   # Registered api as implit import module
   const native_import_procs_def = native_import_procs
   let sf = getTempDir() / "scriptapi.nim"
   block:
      let file = open(sf, fmWrite)
      file.write(native_import_procs_def)
      file.close
      ctx.scriptapi_import = sf.changeFileExt("")

   conf.implicitImports.add sf
   discard safe_compile_module(ctx, AbsoluteFile sf)

proc setup_interactive_passes(ctx: RunContext) =
   registerPass(ctx.graph, semPass)
   registerPass(ctx.graph, evalPass)

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

proc setup_vm_config(ctx: RunContext) =
   var conf = ctx.conf
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

   when hasFFI:
      conf.features.incl compiletimeFFI

   setup_vm_config_define(conf)

proc create_script_vm(ctx: RunContext): PCtx =
   const name = "script"
   var graph = ctx.graph
   var m = graph.makeModule(AbsoluteFile name)
   ctx.main_module = m
   ctx.idgen = idGeneratorFromModule(m)

   var vm = setupVM(m, graph.cache, name, graph, ctx.idgen)
   graph.vm = vm
   graph.compileSystemModule()
   return vm

proc set_stop_compile_handler(ctx: RunContext) =
   proc stop(): bool =
      ctx.conf.errorCounter >= ctx.max_compiler_errors

   ctx.graph.doStopCompile = stop

proc load_preload_module(ctx: RunContext) =
   var conf = ctx.conf

   if ctx.check_failed_module_time:
      ctx.check_failed_module_time = false
      ctx.refresh_failed_module_with_last_mod_time()

   var pre_compile_module: seq[string]

   # Pre-load this module
   var pre_load_module: seq[string]
   if not opt_no_preload_module.on:
      pre_load_module =  @["strutils", "strformat", "os", "tables", "sets", "math", "json", "macros"]
      when not my_special_vmops:
         pre_load_module.add "sequtils"

   for f in pre_load_module & ctx.imports:
      if not is_failed_module(ctx, f):
         let mf = findFile(conf, f & ".nim")
         if not mf.isEmpty:
            if not safe_compile_module(ctx, mf):
               ctx.add_failed_module(f, mf.string)
               raise Reset()
            else:
               pre_compile_module.add f

   if ctx.scriptapi_import != "":
      pre_compile_module.add ctx.scriptapi_import

   if pre_compile_module.len > 0:
      ctx.pre_load_code = "import " & pre_compile_module.join(", ") & "\p"
   else:
      ctx.pre_load_code = ""

proc setup_compile_environment(ctx: RunContext) =
   set_stop_compile_handler(ctx)
   setup_vm_config(ctx)
   setup_config_error_hook(ctx)
   setup_interactive_passes(ctx)

   var vm = create_script_vm(ctx)
   vm.register_custom_vmops(ctx)

proc setup_vm_environment(ctx: RunContext) =
   setup_input_stream(ctx)
   setup_compile_environment(ctx)
   load_preload_module(ctx)

proc reset_vm_state(ctx: RunContext) =
   initStrTables(ctx.graph, ctx.main_module)
   refresh(ctx.vm, ctx.main_module, ctx.idgen)

proc run_repl(ctx: RunContext) =
   # There is three type of errors:
   # 1. General syntax error, sometime it will make the sempass scope
   #    context error, so maybe we need reload the code, there is option
   #    to control this.
   # 2. The code or compiler raise exception, it's happen rarely, but
   #    maybe we need reload the code to prevent some error result,
   #    there is option to control this.
   # 3. Error when import module, the sem context is ruined almost,
   #    we need reset the vm, there is config to control reload code
   #    or reset vm. But now, we will compile module first, if there is
   #    error, we will no import the module, so there is no need to
   #    reload code or reset vm, anyway, you can still reset the vm using
   #    command :r or :rs

   while true:
      try:
         ctx.init()
         reinit_vm_state(ctx)
         ctx.graph.processModule(ctx.main_module, ctx.idgen, ctx.input_stream)
      except ResetError:
         break
      except ReloadError:
         discard
      except NilAccessDefect:
         # now we treat NilAccessDefect same as general exception
         with_color(fgRed, false):
            stdout.write("Error: ")
         echo getCurrentExceptionMsg()

         if opt_exception_to_reset_module.on:
            break
      except:
         with_color(fgRed, false):
            stdout.write("Error: ")
         echo getCurrentExceptionMsg()

         if opt_exception_to_reset_module.on:
            break

      # Reset the vm/module state when reload
      reset_vm_state(ctx)

proc rebuild_vm_environment(ctx: RunContext) =
   ctx.conf = newConfigRef()
   ctx.graph = newModuleGraph(newIdentCache(), ctx.conf)
   setup_vm_environment(ctx)

const HelpText = """
+----------------------------------------------------------------------------+
|                            Simple nim repl                                 |
|                             Version 0.2                                    |
+----------------------------------------------------------------------------+
Build time: $1 $2

Usage:
  nims [options] [modules ...]

Options:
  --help, -h                     show help
  --nimpath:PATH                 set nim directory, contains lib/system.nim
  -p, --path:PATH                add path to search module
  -c, --cache:on|off             turn auto load/save script code on|off (off)
  --no-preload-module:on|off     turn load preload module off|on (off)
  --auto-create-var:on|off       turn auto create var when not exist on|off (on)
  --error-to-reload:on|off       turn reload on syntax error on|off (on)
  --max-compiler-errors:NUM      set max compiler errors (5)

Modules:
   Module name list will be loaded at start.
"""

proc show_help() =
   echo HelpText % [CompileDate, CompileTime]

proc set_options_from_command_line(ctx: RunContext) =
   var
      nimlib = ""
      modules: seq[string]
      paths: seq[string]

   let argv = commandLineParams().mapIt((if it[0] == '-' and it.len >= 3 and it[1] != '-': "-" & it else: it))
   for kind, key, val in getopt(cmdline = argv):
      case kind
      of cmdArgument:
         modules.add key
      of cmdLongOption, cmdShortOption:
         case key
         of "help", "h":
            show_help()
            quit()
         of "nimpath":
            if file_exists(val / "lib" / "system.nim"):
               nimlib = val / "lib"
         of "p", "path":
            paths.add val
         of "c", "cache":
            process_switch_on_off(opt_save_nims_code, val)
            if opt_save_nims_code.on:
               ctx.input_lines_good = load_nims_cache_file()
         of "no-preload-module":
            process_switch_on_off(opt_no_preload_module, val)
         of "import-error-to-reset":
            process_switch_on_off(opt_import_error_to_reset_module, val)
         of "exception-to-reset":
            process_switch_on_off(opt_exception_to_reset_module, val)
         of "error-to-reload":
            process_switch_on_off(opt_error_to_reload_code, val)
         of "auto-create-var":
            process_switch_on_off(opt_auto_create_var, val)
         of "verbose":
            process_switch_on_off(opt_verbose, val)
         of "max-compiler-errors":
            ctx.max_compiler_errors = parseInt(val)
         else:
            echo &"Unknown option [{key} {val}]\p"
            quit()
      of cmdEnd: discard

   if nimlib == "":
      nimlib = findNimStdLib()
      if nimlib == "":
         const exe_ext = when defined(windows): ".exe" else: ""
         quit(&"Cannot find nim{exe_ext} in the PATH")

   var libs = @[nimlib / "core",
                nimlib / "pure",
                nimlib / "pure/collections",
                nimlib / "system",
                nimlib / "windows"]

   when my_special_vmops:
      libs.add(nimlib /../ "mylib")

   libs.add paths

   let pkg_dir = (if getEnv("NIMBLE_DIR") != "": getEnv("NIMBLE_DIR") else: nimlib /../ "nimble") / "pkgs"
   for p in walkDir(pkg_dir):
      libs.add p.path

   ctx.libpath = nimlib
   ctx.libs = libs
   ctx.imports = modules

proc ctrl_c_proc() {.noconv.} =
   sleep(100)
   quit "CTRL-C pressed, quit."

proc main() =
   var ctx = RunContext(max_compiler_errors: 5, saved_stdout: FileHandle(-1))
   ctx.options.incl {opt_error_to_reload_code, opt_auto_create_var}
   when my_special_vmops:
      ctx.options.incl {opt_paste_by_input_time_elapse}

   set_options_from_command_line(ctx)
   set_control_chook(ctrl_c_proc)
   while true:
      try:
         # When reset, code goes here, we will rebuild the vm environment
         rebuild_vm_environment(ctx)
         run_repl(ctx)
      except:
         discard

when isMainModule:
   main()
