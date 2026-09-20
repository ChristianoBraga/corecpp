# corecpp

Core C++ is a well behaved subset of C++17 used as the core language of the
course 09022 Linguagens de Programação at IME (5th year, Engenharia de
Computação). The course follows Watt's structure, introduces every concept as
a construction of Core C++, added to the implemented core in the order of the
syllabus with its natural semantics rules on the board, and uses Lean 4 as the
programming language in which the semantics is coded. The course proposal
is `../.claude/proposta-curso.md` and the language design, with the grammar and
the discrepancy table, is `../.claude/core-cpp-design.md`. Both are in
Portuguese. Repository `git@github.com:ChristianoBraga/corecpp.git`, public since 2026-09-18.

## Conventions

- Code, comments, docstrings, identifiers, error messages and grammar
  nonterminals are always in English. Prose replies to Christiano are in
  Portuguese.
- RULE ZERO of `~/.claude/CLAUDE.md` applies. Short replies, active voice, no
  first person, no `:`, `-` or `;` in prose, exact domain terminology. Token,
  not "ficha". Closure, not "fechamento". Command (`Cmd`) for assignment,
  block, if, while, for, return, declaration. A statement is a command or an
  expression followed by `;`.
- Every semantic rule is written in natural semantics notation in the comment
  of the case that implements it, with the rule name. Judgments are
  ρ, σ ⊢ e ⇒ v, σ', ρ, σ ⊢ e ⇒ₗ ℓ, σ', ρ, σ ⊢ c ⇒ r, ρ', σ' and, for typing,
  Γ ⊢ e : τ and Γ ⊢ c ⊣ Γ'. Sequent style as in Kahn (1987), hypotheses left
  of ⊢, subject right of it, result after ⇒.
- One parser function per grammar nonterminal, one evaluator function per
  judgment. The grammar is LL(1) by construction, verified by inspection so far.

## Layout

- `CoreCpp/Token.lean`, `Lexer.lean` (hand written finite automaton, longest
  match, `std::function` and `std::vector` as single tokens, uppercase initial
  for type identifiers), `Syntax.lean` (AST), `Parser.lean` (recursive
  descent), `Semantics.lean` (Loc, Val, Error, Env, Store, Ctrl),
  `Pretty.lean`, `Typing.lean` (static semantics), `Eval.lean` (evaluator in the
  monad `M := ExceptT Error (StateM TState)` carrying the derivation trace).
- `Main.lean`, the executable. `bin/corecpp [ast|check|run|trace] <file | ->`.
  The wrapper rebuilds when sources change. It lives in `bin/` because the
  macOS filesystem does not distinguish `corecpp` from `CoreCpp`.
- `Test.lean`, `#eval` tests. Run with `lake env lean Test.lean`.
- `docs/`, the Verso Blueprint package with the semantic rules and pointers to
  the code, written in English because the rendered interface of Verso is
  English only. It requires `leanprover/verso-blueprint` at `v4.32.0` and `corecpp`
  from `..`. The package is named `CoreCppBlueprint`, equal to the library,
  because `vbp` builds `+<package>:olean`. One chapter per UD under
  `docs/CoreCppBlueprint/Chapters/`, one `:::definition` node per construction
  with the typing and evaluation rules in KaTeX and `(lean := ...)` naming the
  implementing functions. Only definitions, theorems and types are accepted as
  `lean` targets, never constructors. Build with `lake exe vbp build` inside
  `docs/`, preview with `--serve`, output in `docs/_out/site/html-multi/`. The
  site is published at https://christianobraga.github.io/corecpp/ from the
  orphan branch `gh-pages`, which holds a copy of that directory and an empty
  `.nojekyll`. After regenerating, copy the directory into a `gh-pages`
  worktree, commit and push.
- `examples/*.cpp`, one per concept, all compile with `g++ -std=c++17`, with the
  expected result in the header comment.
- Toolchain `leanprover/lean4:v4.32.2`, no dependencies. `lake build` works. The
  BAIF hook that blocks bare `lake build` exempts projects without Mathlib.

## Language decisions in force

- No undefined behaviour. Everything C++17 leaves undefined is either rejected
  statically or the runtime result `error`, which is not a value of the
  language. Null dereference, out of bounds, division by zero, `int`
  overflow, access to a location outside σ, double `delete`, `delete` through a
  base pointer without virtual destructor.
- Deterministic. Where C++17 leaves the order unspecified, Core C++ evaluates
  left to right. Orders C++17 fixes are kept, right before left in assignment.
- `int` is 32 bit two's complement, overflow is `error`. Only `int`, `bool`,
  `void` as basic types.
- ρ maps identifiers to locations, σ maps locations to values, from the first
  rule. Scope exit removes the block's locations from σ. Locations are never
  reused.
- No global variables. Every local declaration has an initialiser, by the
  grammar.
- Every object, vectors included, is created with `new`, lives until `delete`
  or program end, is reached by pointer or reference, and is never copied.
  Destructors run only on `delete`. No objects by value, no copy constructors,
  no RAII, no initialiser lists.
- Lambdas only `[=]`, with copies of basic values and pointers, read only.
  A lambda expression occurs only as initialiser of a `std::function`
  declaration, as argument of a `std::function` parameter, or as a `return`
  expression. No `[&]`.
- Templates only on classes, instantiated in type position. Overloading by
  argument type, not distinguishing `std::function` parameters. `auto` local.
- Single translation unit, no preprocessor, methods defined inside the class.
- Inductive big step semantics. Divergence has no derivation and the course
  states this limitation (Leroy and Grall).

## Status on 2026-09-20

Implemented and tested: basic types, expressions, commands, first order
functions with call by value, type checker, evaluator with trace, CLI, and the
UD II fragment, classes with public fields only, `new C()`, pointers to classes
as the recursive type, `nullptr`, `->`, `.`, `*` and `[]` as location denoting
expressions, `std::vector<τ>` created with `new`, objects as records of
locations with a class tag, `error` on null dereference, out of bounds and
negative size, eighteen examples. The specification of the fragment is
`../.claude/spec-ud2.md`. Not yet implemented: `T&` parameters and local
references, lambdas and `std::function`, methods, constructors, destructors,
`delete`, `this`, `virtual`, namespaces, templates, operator overloading,
`auto` beyond local declarations. Next step by the course order is UD III
references, then UD IV lambdas.

Worklog and memory of the course live under `../.claude/`.
