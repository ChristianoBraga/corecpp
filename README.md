# Core C++

<img src="docs/logo.svg" alt="Core C++ logo, a C inside a C followed by ++" width="176">

Core C++ is a well behaved subset of C++17 used as the core language of the
course 09022, Linguagens de Programação, at IME (Instituto Militar de
Engenharia, 5th year of Engenharia de Computação). Every concept of the course
is introduced as a construction of Core C++, added to the implemented core in
the order of the syllabus, with its typing and evaluation rules in natural
semantics on the board. This repository holds the Lean 4 implementation of
those rules.

Every Core C++ program compiles with `g++ -std=c++17`. The subset has an LL(1)
grammar, a deterministic semantics and no undefined behaviour. Everything
C++17 leaves undefined is rejected statically or is the runtime result
`error`, which is not a value of the language.

## Contents

| Module | Role |
|---|---|
| `CoreCpp/Token.lean`, `CoreCpp/Lexer.lean` | Tokens and the hand written lexer |
| `CoreCpp/Syntax.lean`, `CoreCpp/Parser.lean` | Abstract syntax and the recursive descent parser, one function per nonterminal |
| `CoreCpp/Semantics.lean` | Locations, values, environment ρ, store σ, `error` and control results |
| `CoreCpp/Typing.lean` | Static semantics, Γ ⊢ e : τ and Γ ⊢ c ⊣ Γ' |
| `CoreCpp/Eval.lean` | Evaluator in natural semantics, one function per judgment, each rule in the comment of the case that implements it |
| `CoreCpp/Pretty.lean` | Printing of syntax and semantic domains |
| `CoreCpp/Templates.lean` | Expansion of class templates by substitution, before checking |
| `CoreCpp/Fragment.lean` | The fragment of each paradigm, a predicate over the abstract syntax |
| `CoreCpp/Logic.lean` | A small logic language, terms, unification and SLD resolution |
| `Main.lean`, `bin/corecpp` | Command line interpreter |
| `Test.lean` | Tests, run with `lake env lean Test.lean` |
| `examples/` | One program per concept, all accepted by `g++`, expected result in the header comment |
| `examples/logic/` | Programs of the logic language, run with `bin/corecpp prolog` |
| `docs/` | The blueprint of the semantics, see below |

The judgments follow the sequent style of Kahn (1987). The hypotheses ρ and σ
stand left of ⊢, the subject right of it and the result after ⇒.

```
ρ, σ ⊢ e ⇒ v, σ'          expression evaluation
ρ, σ ⊢ e ⇒ₗ ℓ, σ'         location denotation
ρ, σ ⊢ c ⇒ r, ρ', σ'      command execution
```

## Usage

The toolchain is `leanprover/lean4:v4.32.2`, installed through `elan`. The
interpreter has no dependencies.

```
lake build
lake env lean Test.lean
bin/corecpp [ast|check|run|trace] <file.cpp | ->
bin/corecpp fragment [imperative|oo|functional] <file.cpp | ->
bin/corecpp prolog <file.pl | ->
```

The mode `run` is the default. The exit code of `run` and `trace` is the value
of `main` modulo 256, so the following behaves like compiling with `g++` and
running the result.

```
echo 'int main() { return 42; }' | bin/corecpp -; echo $?
```

The mode `ast` prints the abstract syntax tree, `check` type checks, and
`trace` prints the derivation as it is written on the board, the premises over
a line of inference, the conclusion under it and the rule name at the right. A
legend names the environments ρᵢ, the stores σⱼ and the subjects too long for
a judgment, so every judgment fits one line, and a subtree too wide for the
page is written apart under a name 𝒟ₖ. The mode `fragment` says whether a
program lies in the fragment of a paradigm, and names the offending
construction when it does not. The mode `prolog` reads a logic program and
answers its queries.

```
$ echo 'int main() { int x = 1; return x; }' | bin/corecpp trace -
ρ₀ = []            σ₀ = {}
ρ₁ = [x ↦ ℓ0]      σ₁ = {ℓ0 ↦ 1}

                   𝒟₁                       𝒟₂
  ρ₀, σ₀ ⊢ int x = 1; ⇒ normal, ρ₁, σ₁    ρ₁, σ₁ ⊢ return x; ⇒ ret 1, ρ₁, σ₁
  ────────────────────────────────────────────────────────────────────────── (Call)
  ρ₀, σ₀ ⊢ main() ⇒ 1, σ₀

𝒟₁
  ────────────────── (Lit)
  ρ₀, σ₀ ⊢ 1 ⇒ 1, σ₀
  ──────────────────────────────────── (Decl)
  ρ₀, σ₀ ⊢ int x = 1; ⇒ normal, ρ₁, σ₁
...
```

## Blueprint

The blueprint is published at
[christianobraga.github.io/corecpp](https://christianobraga.github.io/corecpp/).
The directory [`docs/`](docs/) holds its source, a
[Verso Blueprint](https://github.com/leanprover/verso-blueprint) of the
semantics. It states every typing and evaluation rule, one node per
construction and one chapter per unit of the syllabus, links each node to the
Lean declarations that implement it, and renders a dependency graph and a
progress summary. The planned constructions without rules yet appear as
pending nodes.

```
cd docs
lake exe vbp build          # writes _out/site/html-multi/
lake exe vbp build --serve  # serves the site locally
```

The entry page is `docs/_out/site/html-multi/index.html`. The published copy
lives on the branch `gh-pages`, the contents of that directory plus an empty
`.nojekyll`, served by GitHub Pages.

## Language decisions

- `int` is 32 bit two's complement and overflow is `error`. The basic types are
  `int`, `bool` and `void`.
- Where C++17 leaves the evaluation order unspecified, Core C++ evaluates left
  to right. Orders C++17 fixes are kept, the right operand before the left in
  assignment.
- No global variables, every local declaration has an initialiser, braces are
  mandatory.
- Every object is created with `new`, reached by pointer or reference and never
  copied. Destructors run only on `delete`.
- Lambdas capture only by copy, `[=]`, and occur only where C++ converts them
  to a known `std::function`.
- Divergence has no derivation. The inductive big step semantics does not
  describe non terminating executions, a limitation stated in the course
  (Leroy and Grall, Coinductive big-step operational semantics).

## Status

The seven units of the course are implemented and tested. Basic types,
expressions and commands, first order functions with call by value and by
reference, classes with fields and with methods, constructors, destructors,
`new`, `delete`, `this`, `virtual`, single inheritance, namespaces, pointers,
`nullptr`, `std::vector`, local references, lambdas `[=]` and
`std::function`, overloading, operator members, class templates and `auto`.
Unit VII adds no construction, and gives instead the fragment of each
paradigm and a small logic language.

Outside the design, and therefore not implemented. Function templates,
partial specialisation, objects by value, copy constructors, RAII,
exceptions, multiple inheritance, the preprocessor and separate compilation.
In the logic language, negation, the cut, assert and retract.

## References

- Gilles Kahn, Natural Semantics, STACS 1987, LNCS 247, Springer.
- David A. Watt, Programming Language Concepts and Paradigms, Prentice Hall, 1990.
- Xavier Leroy and Hervé Grall, Coinductive big-step operational semantics, Information and Computation 207 (2009).
- J. A. Robinson, A Machine-Oriented Logic Based on the Resolution Principle, Journal of the ACM 12 (1965).
- Robert Kowalski, Predicate Logic as Programming Language, IFIP Congress (1974).
- ISO/IEC 14882:2017, Programming Languages, C++.
