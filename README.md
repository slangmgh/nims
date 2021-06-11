# nims
simple nim repl

This is enhanced version of "nim secret".

Build:
1. Without libffi: nim c -d:release -d:nimcore nims.nim
2. With libffi: nim c -cc:gcc -d:release -d:nimcore -d:nimHasLibFFI nims.nim

Feature list:
1.  It is fast, just like real repl.
2.  Much robust than "nim secret", nim secret is very easy to crash.
3.  Support all the function of nimscript.
4.  Support libffi, so some importc proc works.
5.  Input script auto indent.
6.  Multi-line code paste should work.
7.  With "-cache" option, input script can be auto save/load.
8.  You can add native callback function with vm_native_proc macro easily.
