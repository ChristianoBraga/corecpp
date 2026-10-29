# Benchmark

A corpus of 300 random Core C++ programs, `corpus/`, for differential testing with `g++`.

```
python3 -I benchmark/gen.py SEED       # one program
benchmark/build.sh [COUNT]             # the corpus, 300 programs by default
bin/compare benchmark/corpus/*.cpp     # exit codes of g++ and corecpp
python3 -I benchmark/coverage.py       # constructions the corpus uses
```

The generator `gen.py` draws a program from a seed. Its docstring states the invariants that keep a program well typed, terminating and free of undefined behaviour. The script `build.sh` keeps a program only when the build with `-fsanitize=undefined,address` runs without a report. The sanitizers serve as a check of the absence of undefined behaviour that does not depend on corecpp. Every program records its seed and the exit code of `g++`.

The script `coverage.py` counts the programs per construction of the abstract syntax, `CoreCpp/Syntax.lean`, and per construction recorded as a flag or a name, such as `virtual`, `override` or an operator.

The directories `ub/` and `notcore/` hold programs written by hand. Each program of `ub/` has undefined behaviour in C++17, and its first line cites the clause of N4659 that makes it undefined. Each program of `notcore/` is a valid C++17 program that `corecpp check` rejects. The script `report.py` writes `REPORT.md`, with the agreement of all three sets and the fuel, the time and the coverage of the corpus by class of construction.

Two choices follow the blueprint. A reference argument has exactly the type of its parameter (node `param_ref`), so only a pointer of the base type reaches a parameter `Base&`. No class redefines a method that is not virtual (rule T-Class, node `cls_decl`).
