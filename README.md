# Core C++

<img src="docs/logo.svg" alt="Core C++ logo, a C inside a C followed by ++" width="176">

Core C++ is a well behaved subset of C++17 with a complete formal semantics.
Every construction has a typing rule and an evaluation rule, written in
natural semantics, and this repository holds the Lean 4 implementation of
those rules, a lexer, a parser, a type checker, an evaluator that prints the
derivation of each execution, and a command line interpreter.

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
| `Main.lean`, `bin/corecpp` | Command line interpreter |
| `CoreCpp/Grammar.lean` | The grammar of Core C++ with the theorem that it is LL(1), by the package [ll1-lean](https://github.com/ChristianoBraga/ll1-lean) |
| `grammar/core-cpp.ebnf`, `CoreCpp/GrammarRules.lean` | The grammar of Core C++ in EBNF, and the Lean module that `lake exe ebnf2lean` generates from it |
| `CoreCpp/GrammarTerm.lean`, `tools/Ebnf2Lean.lean` | The terminals of the grammar and the generator |
| `preproc/` | Preproc, the preprocessor of Core C++, a language of its own run before the compiler, with the headers of Core C++ in `preproc/include` and the design in `ccpp-preproc.md` |
| `bin/ccpp-pre` | The preprocessor, `bin/ccpp-pre [-D CCPP_X=]... <file> [-o out]` |
| `tests/Test.lean` | Tests of Core C++, run with `lake env lean tests/Test.lean` |
| `tests/Grammar.lean` | Round trip between `grammar/core-cpp.ebnf` and `CoreCpp/GrammarRules.lean` |
| `examples/` | One program per concept, all accepted by `g++`, expected result in the header comment |
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
interpreter depends only on the package [ll1-lean](https://github.com/ChristianoBraga/ll1-lean).

```
lake build
lake exe ebnf2lean        # after an edit of grammar/core-cpp.ebnf
lake env lean tests/Test.lean
lake env lean tests/Grammar.lean
lake env lean tests/Preproc.lean
bin/corecpp [ast|check|run|trace] <file.cpp | ->
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
page is written apart under a name 𝒟ₖ.

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
construction or nonterminal and one chapter per group of constructions, links
each node to the Lean declarations that implement it, and renders a dependency
graph and a progress summary.

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
  describe non terminating executions, a limitation of the style (Leroy and
  Grall, Coinductive big-step operational semantics).

## Status

The whole design is implemented and tested. Basic types, expressions and
commands, first order functions with call by value and by reference, classes
with fields and with methods, constructors, destructors, `new`, `delete`,
`this`, `virtual`, single inheritance, namespaces, pointers, `nullptr`,
`std::vector`, local references, lambdas `[=]` and `std::function`,
overloading, operator members, class templates and `auto`.

Outside the design, and therefore not implemented. Function templates,
partial specialisation, objects by value, copy constructors, RAII,
exceptions, multiple inheritance and separate compilation.

## References

- Gilles Kahn, Natural Semantics, STACS 1987, LNCS 247, Springer.
- David A. Watt, Programming Language Concepts and Paradigms, Prentice Hall, 1990.
- Xavier Leroy and Hervé Grall, Coinductive big-step operational semantics, Information and Computation 207 (2009).
- ISO/IEC 14882:2017, Programming Languages, C++.
