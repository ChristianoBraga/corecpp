# Preproc, the preprocessor of Core C++

## Principle

C++ is a monotonic extension of Core C++. Every Core C++ file is a C++ file, and never the other way around. C++ keeps the meaning of every Core C++ program. Where C++ leaves the behaviour undefined, its allowed results include the one Core C++ gives, `error` among them. Core C++ therefore refines C++.

Preproc is the preprocessor of Core C++, a language of its own that runs before the Core C++ compiler. Every Preproc program is a valid input of the preprocessor of `g++`. The two compilers use different headers. The Core C++ compiler uses the headers of Core C++, written in Core C++. `g++` uses its own headers.

## Purpose

Preproc supports four things.

1. Conditional compilation on flags.
2. The inclusion of a subset of the standard library.
3. The inclusion of a subset of the STL.
4. The macro `assert` of `<cassert>`.

A flag has no value and never reaches the code. Preproc selects lines and replaces each `#include` by the contents of a header. It substitutes nothing else.

## Pipeline

```
bin/ccpp-pre -D CCPP_DEBUG= prog.cpp -o prog.i.cpp  Preproc
bin/corecpp run prog.i.cpp                          Core C++
g++ -std=c++17 -D CCPP_DEBUG= prog.cpp              C++, with the headers of g++
```

The library `Preproc` (`preproc/Preproc.lean`) implements the language, and the executable `ccpp-pre` (`preproc/PreprocMain.lean`, run through `bin/ccpp-pre`) reads the command line. `tests/Preproc.lean` tests it on the programs of `tests/preproc/`. Preproc reads files as sequences of lines, and it never lexes or parses Core C++. Its output T(p) is a Core C++ program without directives, and the Core C++ compiler reads it without knowing Preproc. The surface between the two is empty.

## Grammar

The terminals are whole lines. `Text` stands for any text line, and `NL` ends a directive line.

```
File  = Group ;
Group = { Line | Cond } ;
Line  = "#include" "<" Header ">" NL
      | "#define" FlagId NL
      | Text
      ;
Cond  = Test FlagId NL Group [ "#else" NL Group ] "#endif" NL ;
Test  = "#ifdef" | "#ifndef" ;
```

The construction of `core-cpp/CoreCpp/LL1.lean` finds this grammar LL(1), with 14 productions. `Header` ranges over the headers that Core C++ provides.

## Lexical rules

The rules apply to every line, including the lines of a branch that is not selected and the lines of every header. The C++ preprocessor splices lines and removes comments before it recognises directives (N4659 §5.2 [lex.phases], phases 2 to 4). The rules keep the line structure the same for both.

1. A directive line is exactly one of the forms of the grammar.
2. A text line does not start with `#` or with the digraph `%:`, possibly after white space. The C++ preprocessor would read either as a directive, since `%:` is the alternative token for `#` (N4659 §5.5 [lex.digraph], Table 1).
3. No line contains a backslash, `/*`, `'` or `"`. These could splice lines, hide lines in a comment, or open a literal.
4. A `FlagId` has the prefix `CCPP_` and no `__`. Identifiers with `__` are reserved (N4659 §5.10 [lex.name], item 3.1).
5. A word of a text line is a maximal run of letters, digits and `_`. No word starts with `CCPP_`, so a flag never occurs in a text line.

The rules make every Preproc program a valid input of `g++ -E`. The directives are standard directives, and rule 3 excludes the unterminated literals and comments that could fail. Any other character passes through `g++ -E` as a preprocessing token, as `@` and `$` do.

The prefix keeps flags away from keywords, from library names (N4659 §20.5.4.3.2 [macro.names]), from `defined` (N4659 §19.8 [cpp.predefined], paragraph 4), and from the names that the compiler predefines. It also keeps `NDEBUG` out of reach, so every `assert` stays active.

## Meaning

The flag environment φ is a finite set of flags. It starts as φ₀, the flags given as `-D CCPP_X=` on the command line, each a `FlagId` by rule 4. The option `-D F=` gives F an empty replacement list, as `#define F` does (GCC manual, Preprocessor Options). A flag defined both ways therefore has identical replacement lists, which N4659 §19.3 [cpp.replace], paragraph 2, requires of a redefinition.

Preproc processes the lines in order. The judgement φ ⊢ G ⇒ t, φ′ gives the text t of a group and the flag environment after it.

```
─────────────────────────────────── (P-Define)
φ ⊢ #define F ⇒ ε, φ ∪ {F}

φ ⊢ H(h) ⇒ t, φ′
─────────────────────────────────── (P-Include)
φ ⊢ #include <h> ⇒ t, φ′

F ∈ φ    φ ⊢ G₁ ⇒ t, φ′
─────────────────────────────────────────── (P-IfdefT)
φ ⊢ #ifdef F G₁ #else G₂ #endif ⇒ t, φ′

F ∉ φ    φ ⊢ G₂ ⇒ t, φ′
─────────────────────────────────────────── (P-IfdefF)
φ ⊢ #ifdef F G₁ #else G₂ #endif ⇒ t, φ′
```

H(h) is the contents of the Core C++ header h. In C++ too, `#include <h>` is replaced by the entire contents of the header (N4659 §19.2 [cpp.include], paragraph 2). The directive `#ifndef` swaps the premises F ∈ φ and F ∉ φ, and a missing `#else` stands for an empty G₂. A text line gives itself and leaves φ unchanged. A sequence of lines concatenates the texts and threads φ.

## Headers of Core C++

The headers of Core C++ are Core C++ code for the Core C++ compiler, in the directory `preproc/include`. Each is a Preproc file. It may contain conditionals and other `#include` lines, and a guard makes it idempotent.

```
#ifndef CCPP_H_VECTOR
#define CCPP_H_VECTOR
… Core C++ declarations …
#endif
```

A C++ header too may be included more than once "with no effect different from being included exactly once" (N4659 §20.5.2.2 [using.headers], paragraph 2).

| Library | Header | Contents in Core C++ |
| --- | --- | --- |
| standard library | `<cassert>` | a guard, since `assert` is a statement of Core C++ |
| standard library | `<cstdlib>` | a possible addition |
| STL | `<vector>` | a guard, since `std::vector` is built into Core C++ |
| STL | `<functional>` | a guard, since `std::function` is built into Core C++ |
| STL | `<optional>`, `<array>`, `<map>` | possible additions |

C++ allows a header only outside any declaration or definition, and before the first reference to its entities (N4659 §20.5.2.2 [using.headers], paragraph 3). Preproc does not check this. An `#include` inside a function body puts declarations inside a block, and the Core C++ compiler rejects them by its own grammar.

## Assert

The C++ header `<cassert>` has the contents of the C header `<assert.h>` (N4659 §22.3.1 [cassert.syn]). With `NDEBUG` undefined, a failed `assert` writes a diagnostic and calls `abort` (N1570 §7.2.1.1). Core C++ is to read `assert(e)` as a statement, which it does not do yet.

```
Γ ⊢ e : bool
──────────────────── (T-Assert)
Γ ⊢ assert(e) ⊣ Γ

ρ, σ ⊢ e ⇒ true, σ′
─────────────────────────────────── (E-AssertTrue)
ρ, σ ⊢ assert(e) ⇒ normal, ρ, σ′

ρ, σ ⊢ e ⇒ false, σ′
─────────────────────────── (E-AssertFalse)
ρ, σ ⊢ assert(e) ⇒ error
```

An `error` of e propagates. Core C++ ends an `error` with exit code 134 (`core-cpp/Main.lean`, line 59), and the shell reports 134 for a process that `abort` ends.

## Correctness

Take a Preproc program p whose output T(p) Core C++ accepts. The property is that compiling p with `g++` and running T(p) in Core C++ give the same exit status under the same `-D` options. It rests on two facts.

1. The C++ preprocessor selects the same lines as Preproc (N4659 §19.1 [cpp.cond], paragraphs 11 and 12), and rule 5 keeps the flags out of the code.
2. For the names the subset admits, each Core C++ header agrees with the `g++` header of the same name. This is one obligation per header. `bin/compare` tests it by running `g++` on p and `bin/corecpp` on T(p).

A built-in name such as `std::vector` stays in scope without its header in Core C++. Such a program falls outside the property, since `g++` rejects it.

## Open points

1. The line numbers of T(p) differ from those of p after an inclusion, and Core C++ has no `#line`.
2. Every Core C++ file is a C++ file, headers included. Adding declarations to namespace `std` makes a C++ program undefined (N4659 §20.5.4.2.1 [namespace.std], paragraph 1). A Core C++ header that declares a library name in `std` would therefore break the principle. The headers of the table hold only guards until Core C++ settles how it declares library names.

## Left out

Preproc leaves out macros with values, `#if` with expressions, `defined(…)`, `#undef`, `#include "file"`, `#pragma`, `#line`, `#error`, and `#` and `##`.

## References

* GCC manual, Preprocessor Options, https://gcc.gnu.org/onlinedocs/gcc/Preprocessor-Options.html
* ISO/IEC 9899:2011, Programming Languages, C, in the committee draft N1570 of WG14, https://www.open-std.org/jtc1/sc22/wg14/www/docs/n1570.pdf
* ISO/IEC 14882:2017, Programming Languages, C++, in the final working draft N4659 of WG21, https://www.open-std.org/jtc1/sc22/wg21/docs/papers/2017/n4659.pdf
