# Benchmark report

The corpus holds 300 programs, drawn by `gen.py` from the seeds 1 to 300. The build discarded 0 seeds.

## Agreement with g++

The agreement covers the corpus and two directories of programs written by hand, `ub/` with undefined behaviour and `notcore/` with valid C++17 programs outside Core C++. A program fails because it is not Core C++ when `corecpp check` rejects it with a syntax or type error. A program fails due to undefined behaviour when `corecpp` gives an error result of undefined behaviour, exit code 134. The errors `outOfFuel`, `noTarget`, `negativeSize` and a failed `assert` do not count, since C++17 defines the behaviour of the last three and the first one is a limit of the evaluator (`Error` in `CoreCpp/Semantics.lean`). No exit code of g++ is compared for these two outcomes. Otherwise a program agrees when `g++ -std=c++17` and `corecpp` give the same exit code. The build keeps only corpus programs free of sanitizer reports, and `gen.py` draws only Core C++ programs, so no corpus program fails by construction.

| Outcome | Corpus | `ub/` | `notcore/` |
| --- | --- | --- | --- |
| Agree | 300 | 0 | 0 |
| Fails due to undefined behaviour | 0 | 9 | 0 |
| Fails because the program is not Core C++ | 0 | 0 | 12 |

| Program | Outcome | g++ | corecpp | Message of corecpp |
| --- | --- | --- | --- | --- |
| `ub/delete_without_virtual_destructor.cpp` | Fails due to undefined behaviour | 3 | 134 | delete through Base* of an object of class Derived without a virtual destructor |
| `ub/division_by_zero.cpp` | Fails due to undefined behaviour | 22 | 134 | division by zero |
| `ub/double_delete.cpp` | Fails due to undefined behaviour | 133 | 134 | delete of a location already freed, ℓ1 |
| `ub/missing_return.cpp` | Fails due to undefined behaviour | 1 | 134 | function sign ended without return |
| `ub/null_dereference.cpp` | Fails due to undefined behaviour | 139 | 134 | dereference of nullptr |
| `ub/remainder_by_zero.cpp` | Fails due to undefined behaviour | 7 | 134 | division by zero |
| `ub/signed_overflow.cpp` | Fails due to undefined behaviour | 0 | 134 | int overflow |
| `ub/use_after_delete.cpp` | Fails due to undefined behaviour | 6 | 134 | access to a location outside the store, ℓ1 |
| `ub/vector_out_of_bounds.cpp` | Fails due to undefined behaviour | 3 | 134 | index 4 outside a vector of size 4 |
| `notcore/array.cpp` | Fails because the program is not Core C++ | 4 | 1 | not a Core C++ program, but a valid C++17 program |
| `notcore/automatic_object.cpp` | Fails because the program is not Core C++ | 4 | 1 | not a Core C++ program, but a valid C++17 program |
| `notcore/bool_to_int.cpp` | Fails because the program is not Core C++ | 2 | 1 | operator + applied to bool |
| `notcore/char.cpp` | Fails because the program is not Core C++ | 3 | 1 | not a Core C++ program, but a valid C++17 program |
| `notcore/compound_assignment.cpp` | Fails because the program is not Core C++ | 10 | 1 | not a Core C++ program, but a valid C++17 program |
| `notcore/do_while.cpp` | Fails because the program is not Core C++ | 12 | 1 | not a Core C++ program, but a valid C++17 program |
| `notcore/increment.cpp` | Fails because the program is not Core C++ | 6 | 1 | not a Core C++ program, but a valid C++17 program |
| `notcore/member_initializer.cpp` | Fails because the program is not Core C++ | 7 | 1 | not a Core C++ program, but a valid C++17 program |
| `notcore/overload_ranking.cpp` | Fails because the program is not Core C++ | 2 | 1 | the call of f is ambiguous, more than one overload accepts these arguments |
| `notcore/range_for.cpp` | Fails because the program is not Core C++ | 6 | 1 | not a Core C++ program, but a valid C++17 program |
| `notcore/switch.cpp` | Fails because the program is not Core C++ | 20 | 1 | not a Core C++ program, but a valid C++17 program |
| `notcore/unsigned.cpp` | Fails because the program is not Core C++ | 3 | 1 | not a Core C++ program, but a valid C++17 program |

## Fuel and time

The fuel of a program is the least fuel under which the evaluator gives a result, the depth of its derivation. The time is the wall clock time of the evaluator at the default fuel of 10⁶, parsing and type checking excluded, measured by `benchfuel` on one machine. `benchfuel` runs one program at a time, each with a limit of 30 s. 31 programs exceed the limit, b002, b016, b027, b042, b046, b054, b060, b064, b075, b096, b102, b123, b125, b136, b145, b147, b158, b174, b178, b189, b197, b209, b217, b226, b230, b243, b252, b256, b268, b269, b285, and the table excludes them. A later section reports their agreement.

| Measure | Minimum | Median | 90th percentile | Maximum |
| --- | --- | --- | --- | --- |
| Fuel | 13 | 64 | 113 | 174 |
| Time (ms) | 0.1 | 22.1 | 864.3 | 7816.1 |

The total time of the evaluator on the corpus is 80.6 s.

## Programs over 30 s

Each program over the limit of `benchfuel` runs once under `corecpp run` at the default fuel, with no time limit and no search for the least fuel. The time is the wall clock time of the process, parsing and type checking included, with up to 6 programs at a time.

| Program | g++ | corecpp | Time (s) |
| --- | --- | --- | --- |
| b002 | 2 | 2 | 227.9 |
| b016 | 3 | 3 | 99.8 |
| b027 | 0 | 0 | 10.8 |
| b042 | 18 | 18 | 398.7 |
| b046 | 241 | 241 | 22.2 |
| b054 | 90 | 90 | 6.6 |
| b060 | 0 | 0 | 7.8 |
| b064 | 61 | 61 | 9.5 |
| b075 | 120 | 120 | 7.4 |
| b096 | 27 | 27 | 5.6 |
| b102 | 33 | 33 | 4.6 |
| b123 | 110 | 110 | 271.0 |
| b125 | 254 | 254 | 5.5 |
| b136 | 254 | 254 | 8.7 |
| b145 | 8 | 8 | 30.0 |
| b147 | 138 | 138 | 50.1 |
| b158 | 12 | 12 | 30.0 |
| b174 | 0 | 0 | 26.7 |
| b178 | 7 | 7 | 15.8 |
| b189 | 24 | 24 | 416.3 |
| b197 | 2 | 2 | 23.3 |
| b209 | 0 | 0 | 75.8 |
| b217 | 12 | 12 | 56.4 |
| b226 | 212 | 212 | 375.0 |
| b230 | 0 | 0 | 5.9 |
| b243 | 2 | 2 | 7.7 |
| b252 | 216 | 216 | 181.0 |
| b256 | 244 | 244 | 28.5 |
| b268 | 160 | 160 | 30.1 |
| b269 | 0 | 0 | 7.4 |
| b285 | 5 | 5 | 992.0 |

## Coverage by class of construction

Each table counts the programs that use a construction, with the median fuel and the median time of those programs. `coverage.py` defines how each construction is found.

### Types

| Construction | Programs | Median fuel | Median time (ms) |
| --- | --- | --- | --- |
| `Ty.int` | 300 | 64 | 22.1 |
| `Ty.bool` | 299 | 64 | 22.1 |
| `Ty.void` | 294 | 64 | 21.7 |
| `Ty.cls` | 289 | 64 | 22.3 |
| `Ty.ptr` | 300 | 64 | 22.1 |
| `Ty.lib` | 295 | 64 | 22.1 |
| `Ty.fn` | 275 | 65 | 23.5 |

### Unary operators

| Construction | Programs | Median fuel | Median time (ms) |
| --- | --- | --- | --- |
| `UnOp.not` | 234 | 72 | 34.5 |
| `UnOp.neg` | 300 | 64 | 22.1 |

### Binary operators

| Construction | Programs | Median fuel | Median time (ms) |
| --- | --- | --- | --- |
| `BinOp.add` | 300 | 64 | 22.1 |
| `BinOp.sub` | 297 | 64 | 22.2 |
| `BinOp.mul` | 300 | 64 | 22.1 |
| `BinOp.div` | 300 | 64 | 22.1 |
| `BinOp.mod` | 300 | 64 | 22.1 |
| `BinOp.eq` | 275 | 68 | 24.1 |
| `BinOp.ne` | 286 | 65 | 23.3 |
| `BinOp.lt` | 297 | 64 | 22.2 |
| `BinOp.le` | 285 | 65.5 | 24.0 |
| `BinOp.gt` | 279 | 66.5 | 23.4 |
| `BinOp.ge` | 271 | 69 | 26.7 |
| `BinOp.and` | 246 | 70 | 29.5 |
| `BinOp.or` | 219 | 72 | 38.7 |

### Expressions

| Construction | Programs | Median fuel | Median time (ms) |
| --- | --- | --- | --- |
| `Expr.intLit` | 300 | 64 | 22.1 |
| `Expr.boolLit` | 281 | 65.5 | 23.7 |
| `Expr.nullptr` | 62 | 60.5 | 23.1 |
| `Expr.var` | 300 | 64 | 22.1 |
| `Expr.unop` | 300 | 64 | 22.1 |
| `Expr.binop` | 300 | 64 | 22.1 |
| `Expr.cond` | 299 | 64 | 22.1 |
| `Expr.call` | 298 | 64 | 22.1 |
| `Expr.newObj` | 261 | 64 | 23.3 |
| `Expr.newLib` | 286 | 63 | 22.1 |
| `Expr.this` | 281 | 64 | 22.8 |
| `Expr.methodCall` | 240 | 63 | 15.6 |
| `Expr.field` | 113 | 66.5 | 23.4 |
| `Expr.arrow` | 285 | 64 | 22.1 |
| `Expr.deref` | 271 | 64 | 22.8 |
| `Expr.index` | 175 | 65 | 31.6 |
| `Expr.lambda` | 263 | 65 | 24.0 |
| `Expr.callFn` | 199 | 65.5 | 24.9 |
| `method call with .` | 215 | 64 | 21.2 |
| `method call with ->` | 221 | 62 | 14.6 |

### Commands

| Construction | Programs | Median fuel | Median time (ms) |
| --- | --- | --- | --- |
| `Cmd.block` | 239 | 72 | 34.8 |
| `Cmd.ite` | 269 | 70.5 | 30.6 |
| `Cmd.while` | 223 | 72 | 36.8 |
| `Cmd.for` | 277 | 68 | 27.2 |
| `Cmd.ret` | 300 | 64 | 22.1 |
| `Cmd.decl` | 300 | 64 | 22.1 |
| `Cmd.declRef` | 139 | 63.5 | 23.8 |
| `Cmd.declAuto` | 271 | 70 | 28.6 |
| `Cmd.assign` | 300 | 64 | 22.1 |
| `Cmd.exprStmt` | 255 | 64 | 19.1 |
| `Cmd.delete` | 294 | 63.5 | 21.9 |
| `if without else` | 255 | 72.5 | 34.8 |
| `return without a value` | 83 | 58 | 14.2 |

### Declarations

| Construction | Programs | Median fuel | Median time (ms) |
| --- | --- | --- | --- |
| `Decl.cls` | 286 | 64 | 22.1 |
| `Decl.fn` | 300 | 64 | 22.1 |
| `Decl.tmpl` | 122 | 68 | 22.8 |
| `Decl.libTmpl` | 297 | 64 | 22.1 |
| `Decl.libFn` | 91 | 71.5 | 25.1 |
| `namespace` | 73 | 65 | 22.1 |
| `nested namespace` | 59 | 73 | 31.2 |
| `parameter by reference` | 254 | 64 | 22.6 |

### Classes

| Construction | Programs | Median fuel | Median time (ms) |
| --- | --- | --- | --- |
| `Vis.pub` | 292 | 64 | 22.2 |
| `Vis.priv` | 281 | 64 | 22.8 |
| `base class` | 193 | 59 | 14.0 |
| `constructor` | 281 | 64 | 22.8 |
| `destructor` | 224 | 62 | 17.0 |
| `virtual destructor` | 193 | 59 | 14.0 |
| `destructor not virtual` | 83 | 78 | 34.5 |
| `virtual method` | 193 | 59 | 14.0 |
| `override` | 193 | 59 | 14.0 |
| `method returning a reference` | 186 | 69 | 27.6 |

### Operator overloading

| Construction | Programs | Median fuel | Median time (ms) |
| --- | --- | --- | --- |
| `operator+` | 108 | 68 | 19.4 |
| `operator-` | 108 | 68 | 19.4 |
| `operator*` | 108 | 68 | 19.4 |
| `operator/` | 108 | 68 | 19.4 |
| `operator%` | 108 | 68 | 19.4 |
| `operator==` | 108 | 68 | 19.4 |
| `operator!=` | 108 | 68 | 19.4 |
| `operator<` | 108 | 68 | 19.4 |
| `operator<=` | 108 | 68 | 19.4 |
| `operator>` | 108 | 68 | 19.4 |
| `operator>=` | 108 | 68 | 19.4 |
| `operator[]` | 108 | 68 | 19.4 |

### Library

| Construction | Programs | Median fuel | Median time (ms) |
| --- | --- | --- | --- |
| `std::vector` | 205 | 63 | 26.8 |
| `std::function` | 273 | 65.5 | 23.4 |
| `assert` | 91 | 71.5 | 25.1 |

The corpus covers 88 of 88 constructions.
