# libcad
![rust workflow](https://github.com/hiro4bbh-ntt/libcad/actions/workflows/rust.yml/badge.svg)
[(cargo doc on GitHub Pages)](https://hiro4bbh-ntt.github.io/libcad/libcad/index.html)


## Abstract
libcad is a Casting Analysis Device, which is a static analysis framework for LLVM Intermediate Representation (LLIR).

Currently, libcad supports type confusion detection related to tagged union and inheritance.

See `./LICENSE` if you use libcad.


## Preparation
Install Rust [https://www.rust-lang.org/ja], and clone this repository.

To build and test libcad:
```
cargo test
```
Notice that the test build uses Clang to generate test input files.
You can use system default Clang, it will not require other LLVM tools.

To create Rust documentation of libcad:
```
cargo doc
```


## Example - Type Checker `typechk`
This example shows how to check C/C++ tagged union.

libcad can verify per module.
Compile source files in `./tests/cpp` as follows:
```
% mkdir -p ./target/tmp
% clang -S -emit-llvm -g -O0 -arch x86_64 -o ./target/tmp/tagged_union.ll ./tests/cpp/tagged_union.cpp
% clang -S -emit-llvm -g -O0 -arch x86_64 -o ./target/tmp/tagged_union_vuln.ll ./tests/cpp/tagged_union_vuln.cpp
```
Notice that:
- `-S -emit-llvm`: Create one LLIR source text file per one C/C++ source file.
  - because, if you link LLIR files, duplicated typedefs may be generated.
  - for example, due to the way to handle `external` types in each source file, a structure `%struct.A = struct{%struct.B*}` may be split into `%struct.A.2 = struct{%struct.B*}}`, `%struct.A.3 = struct{i8*}`, and so on.
  - and currently, libcad does not support binary representation of LLIR.
- `-g`: Attach the debug information.
  - in order to get the corresponding line numbers from reported warnings.
- `-O0`: Let the optimization level least.
  - for avoiding complex optimized instructions.
- `-arch x86_64`: Let the target architecture `x86_64`.
  - because generated code in some architectures (e.g. `aarch64`) may lose type information (e.g. in passing struct by value).
  - see [https://lists.llvm.org/pipermail/cfe-dev/2013-January/027302.html].

Verify the LLIR modules:
```
% cargo run -- typechk --annot ./tests/annot/tagged_union.lisp ./target/tmp/tagged_union.ll
loading annotation ./tests/annot/tagged_union.lisp ...
loading module ./target/tmp/tagged_union.ll ...
typechk(cast):
  0 possibly unsafe cast(s) found (25 analyzed)
% cargo run -- typechk --annot ./tests/annot/tagged_union.lisp ./target/tmp/tagged_union_vuln.ll
loading annotation ./tests/annot/tagged_union.lisp ...
loading module ./target/tmp/tagged_union_vuln.ll ...
typechk(cast):
  ./tests/cpp/tagged_union_vuln.cpp:7:3(@_Z19object_alloc_byte_tv): store i64 to *<?_>!object-tag.cast-tag0@0+0: failed to verify cast as void under context and(eq(0x3, deref($0)))
  ./tests/cpp/tagged_union_vuln.cpp:14:12(@_Z19object_alloc_byte_vh): store i8 to *<?_>!object-tag.cast-target@0+8: failed to verify cast as i8 under context and(eq(0x2a, deref($1)))
  ./tests/cpp/tagged_union_vuln.cpp:21:3(@_Z20object_alloc_byte_tvh): store i64 to *<?_>!object-tag.cast-tag0@0+0: failed to verify cast as void under context and(eq(0x8, deref($0)))
...
  25 possibly unsafe cast(s) found (35 analyzed)
```
Notice that you can use `cargo run --release` for release build.
The tool accepts the following flags:
- `--all`: show the all unresolved warnings by structural type checking.
- `--annot path`: specify the annotation file path.
- `--debug`: show the internal states in analyzing warnings.
- `--verbose`: show the all internal states of the type checker.


## Example - Interpreter `interp`
A LLIR interpreter is experimentally implemented for testing operational semantics.
```
% cargo run -- interp --verbose 'ret i64 add nsw (i64 1, i64 2)'
at(@__cad_entry__%0#0): ret(<i32 3>)
finished(<i32 3>)
% cargo run -- interp --verbose "$(echo -ne "%1 = alloca i64\n store i64 1, i64* %1\n %2 = load i64, i64* %1\n ret i64 add nsw (i64 %2, i64 1)")"
at(@__cad_entry__%0#0): alloca(%1, <i64 undef@0xffffffffffffffff(0)>)
at(@__cad_entry__%0#1): store-to(<i64 1>, alloca#0)
at(@__cad_entry__%0#2): define-local(%2, <i64 1>)
at(@__cad_entry__%0#3): ret(<i32 2>)
finished(<i32 2>)
% cargo run -- interp 'call void @_Z17use_object_allocav()' ./target/tmp/at(@__cad_entry__%0#0): call(none, @_Z17use_object_allocav, [])
at(@_Z17use_object_allocav%0#0): alloca(%1, <i64 undef@0xffffffffffffffff(0), double undef>)
at(@_Z17use_object_allocav%0#1): dbgintr(@llvm.dbg.declare)
at(@_Z17use_object_allocav%0#2): define-local(%2, <alloca#0+8>)
at(@_Z17use_object_allocav%0#3): collapse-poison(%3, alloca#0+8, i8)
error: at(@_Z17use_object_allocav%0#4): cannot write i8 value at <i64 undef@0xffffffffffffffff(0), double undef>[8..]
```
Currently, annotated tagged union is unsupported, because it requites to extend LLIR semantics (especially memory structure).

An annotation file can be specified (`--annot path` option), and `--verbose` option is for debugging purpose.


## Example - Annotation
To define the specification of a C/C++ tagged union as abstract refinement type:
```lisp
(define-refiner object-tag (cast-match
    ((== (bitand (deref $0) 0xff) 0x00) void)
    ((== (bitand (deref $0) 0xff) 0x01) void)
    ((== (bitand (deref $0) 0xff) 0x02) void)
    ((== (bitand (deref $0) 0xff) 0x03) i8)
    ((== (bitand (deref $0) 0xff) 0x04) i32)
    ((== (bitand (deref $0) 0xff) 0x08) (ptr "struct.Closure"))))
```
Assign the defined refinement type to a LLIR typedef (e.g. in `%struct.Object`, the `0`-th field is tag and `1`-th field is value):
```lisp
(apply-refiner "struct.Object" (fieldptr 1) (cast object-tag (fieldptr 0)))
```
You can reuse the same refinement type in multiple physical structures.

To define the specification of a C/C++ inheritance, and assign it to a LLIR typedef (e.g. in `%struct.SingleInheritClass` and its children, the `0`-th field is tag):
```lisp
(define-refiner single-inherit-class-tag (cast-match
    ((== (bitand (deref $0) 0xff) 0x01) "struct.SingleInheritClass1")
    ((== (bitand (deref $0) 0xff) 0x01) "struct.SingleInheritClass2")))
  
(apply-refiner "struct.SingleInheritClass" baseptr (downcast single-inherit-class-tag (fieldptr 0)))
```

To restrict the cast target types in the specification defined by `cast-match`, and assign it to LLIR typedef (e.g. the `0`-th field of `%struct.ContextInline` is restricted):
```lisp
(define-refiner object-closure-tag (restrict-cast-match object-tag (ptr "struct.Closure")))
(apply-refiner "struct.ContextInline" (fieldptr 0) (restrict object-closure-tag))
```


## Experiments - Lua 5.4.0
An annotation example is the following code:
```lisp
(define-refiner tvalue-tag (cast-match
  ((== (bitand (deref $0) 0x7f) 0x00) void)  ; nil
  ((== (bitand (deref $0) 0x7f) 0x01) void)  ; false
  ((== (bitand (deref $0) 0x7f) 0x02) (ptr i8))
  ((== (bitand (deref $0) 0x7f) 0x03) i64)
  ((== (bitand (deref $0) 0x7f) 0x10) void)  ; empty slot
  ((== (bitand (deref $0) 0x7f) 0x11) void)  ; true
  ((== (bitand (deref $0) 0x7f) 0x13) double)
  ((== (bitand (deref $0) 0x7f) 0x16) (ptr (func i32 (ptr "struct.lua_State"))))
  ((== (bitand (deref $0) 0x40) 0x40) (ptr "struct.GCObject"))
  ((== (bitand (deref $0) 0x0f) 0x04) (ptr "struct.TString"))
  ((== (bitand (deref $0) 0x3f) 0x05) (ptr "struct.Table"))
  ((== (bitand (deref $0) 0x3f) 0x06) (ptr "struct.LClosure"))
  ((== (bitand (deref $0) 0x3f) 0x26) (ptr "struct.CClosure"))
  ((== (bitand (deref $0) 0x3f) 0x07) (ptr "struct.Udata"))
  ((== (bitand (deref $0) 0x3f) 0x08) (ptr "struct.lua_State"))))

(apply-refiner "struct.TValue" (fieldptr 0) (cast tvalue-tag (fieldptr 1)))

(apply-refiner "struct.NodeKey" (fieldptr 0) (cast tvalue-tag (fieldptr 1)))
(apply-refiner "struct.NodeKey" (fieldptr 4) (cast tvalue-tag (fieldptr 2)))

(define-refiner gcobject-tag (cast-match
  ((== (bitand (deref $0) 0x0f) 0x04) "struct.TString")
  ((== (bitand (deref $0) 0x3f) 0x05) "struct.Table")
  ((== (bitand (deref $0) 0x3f) 0x06) "struct.LClosure")
  ((== (bitand (deref $0) 0x3f) 0x26) "struct.CClosure")
  ((== (bitand (deref $0) 0x3f) 0x07) "struct.Udata")
  ((== (bitand (deref $0) 0x3f) 0x08) "struct.lua_State")
  ((== (bitand (deref $0) 0x3f) 0x09) "struct.UpVal")
  ((== (bitand (deref $0) 0x3f) 0x0a) "struct.Proto")))

(apply-refiner "struct.GCObject" baseptr (downcast gcobject-tag (fieldptr 1)))

(define-refiner callinfo-func-tag (restrict-cast-match tvalue-tag (ptr "struct.LClosure")))

(apply-refiner "struct.CallInfo" (fieldptr 0) (restrict callinfo-func-tag))
```

You can compile Lua 5.4.0 (downloadable from [https://github.com/lua/lua/releases/tag/v5.4.0]) as follows:
```
make CFLAGS='-S -emit-llvm -g -O0 -arch x86_64' AR='echo'
```

You can detect the following (maybe critical) type confusions:
- Already fixed bugs in later version than 5.4.0:
  - "Fixed bug of keys removed from tables vs 'next'." [https://github.com/lua/lua/commit/52c86797608f1bf927be5bab1e9b97b7d35bdf2c]
- Two bugs we reported but not fixed:
  - "PATCH: Add Type Checking in op_bitwiseK." [http://lua-users.org/lists/lua-l/2021-04/msg00066.html]
  - "PATCH: How to handle CallInfo func field safely?" [http://lua-users.org/lists/lua-l/2021-04/msg00067.html]
