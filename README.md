# nims
simple nim nrpl

This is enhanced version of "nim secret".

Build:
1. Without libffi: nim c -d:release -d:nimcore nims.nim
2. With libffi: nim c -cc:gcc -d:release -d:nimcore -d:nimHasLibFFI nims.nim

Feature list:
1.  It is fast, just like real nrpl.
2.  Robust than "nim secret", nim secret is very easy to crash.
3.  Support all the function of nimscript.
4.  Input script auto indent.
5.  Multi-line code paste should work.
6.  With "-cache" option, input script can be auto save/load.
7.  You can add native callback function with vm_native macro easily.
