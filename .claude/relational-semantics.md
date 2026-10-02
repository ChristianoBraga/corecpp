# The semantics as relations, the evaluator as their interpreter

Design note, 2026-10-01, branch `relational-semantics`. It records the
decisions taken in conversation and the order of the work.

## Principle

The semantics of Core C++ is a set of inductive propositions, one per
judgement, one constructor per rule. The evaluator of `CoreCpp.Eval` is the
interpreter of those relations, to be proved sound and complete with respect
to them. The structure follows Radix, the DSL of Leonardo de Moura's tutorial
"The Lean Programming Language and Theorem Prover", ETAPS 2026, Turin,
13 April, whose code is at github.com/leodemoura/RadixExperiment and
github.com/leodemoura/ETAPSTutorial2026. There the relation `BigStep` is the
specification, the function `interp` the implementation, and the theorems
`interp_sound`, `interp_complete`, `interp_fuel_mono` and `BigStep.det` tie
them. The slide states the principle, "the relational semantics is the
ground truth".

## The judgements

| Judgement | Lean relation | Interpreter |
| --- | --- | --- |
| ρ, σ ⊢ e ⇒ v, σ′ | `Semantics.Eval p ρ σ e v σ′` | `Eval.expr` |
| ρ, σ ⊢ e ⇒ₗ ℓ, σ′ | `Semantics.LEval p ρ σ e ℓ σ′` | `Eval.lval` |
| ρ, σ ⊢ c ⇒ r, ρ′, σ′ | `Semantics.Exec p ρ σ c r ρ′ σ′` | `Eval.cmd` |
| ρ, σ ⊢ c̄ ⇒ r, ρ′, σ′ | `Semantics.Execs p ρ σ c̄ r ρ′ σ′` | `Eval.cmds` |
| Γ ⊢ e : τ | `Semantics.HasType p Γ e τ` | `Typing.expr` |
| Γ ⊢ₗ e : τ | `Semantics.LHasType p Γ e τ` | `Typing.lval` |
| Γ ⊢ e ◁ τ | `Semantics.Accept p Γ e τ` | `Typing.accept` |
| Γ ⊢ c ⊣ Γ′ | `Semantics.Check p τᵣ Γ c Γ′` | `Typing.cmd` |
| Γ ⊢ c̄ ⊣ Γ′ | `Semantics.Checks p τᵣ Γ c̄ Γ′` | `Typing.cmds` |
| Γ ⊢ τ ok | `Semantics.WF p τ` | `Typing.wellFormed` |
| ⊢ f, ⊢ C, ⊢ p | `Semantics.FunOk`, `ClassOk`, `ProgramOk` | `Typing.fn`, `Typing.cls`, `check` |
| τ′ ≈ τ | `Typing.compat p τ′ τ`, a function | `Typing.compat` |

The program p is a parameter of every relation, the function table and the
class table of the rules. The subject of a rule is the pointer to the
statement under execution, and a rule applies to a subject when its
conclusion matches the constructor of the subject. The relations of one
judgement family form one `mutual` block, since Call needs the command
judgement and Block the expression judgement. The auxiliary relations
`Args`, `Bind`, `Member`, `CallMethod`, `Ctors`, `Dtors`, `Apply`,
`ApplyArgs` and `Returns` name the premises that several rules share, the
arguments left to right, the binding of parameters, the call of a member
body, the dispatch of a method, the constructors and destructors of a chain,
the application of a closure and the value a control gives.

## How a rule is written

A constructor is laid out as the rule is written on the board, the premises
one per line, the inference line as a comment with the name the blueprint
uses, and the conclusion under it. The docstring, when there is one, holds
the side remark only.

```lean
  /-- A zero divisor has no derivation. -/
  | div
      (h₁ : ⟨ρ, σ⟩ ⊢ e₁ ⇒ .int n₁, σ₁)
      (h₂ : ⟨ρ, σ₁⟩ ⊢ e₂ ⇒ .int n₂, σ₂)
      (hz : n₂ ≠ 0)
      (hd : op.divide n₁ n₂ = some n)
      (hr : Int32.inRange n) :
    -- ──────────────────────────────────── (Div)
      ⟨ρ, σ⟩ ⊢ .binop op e₁ e₂ ⇒ .int n, σ₂
```

The notation is the one of the judgements.

| Judgement | Notation | Expands to |
| --- | --- | --- |
| ρ, σ ⊢ e ⇒ v, σ′ | `⟨ρ, σ⟩ ⊢ e ⇒ v, σ'` | `Eval p ρ σ e v σ'` |
| ρ, σ ⊢ e ⇒ₗ ℓ, σ′ | `⟨ρ, σ⟩ ⊢ e ⇒ₗ ℓ, σ'` | `LEval p ρ σ e ℓ σ'` |
| ρ, σ ⊢ c ⇒ r, ρ′, σ′ | `⟨ρ, σ⟩ ⊢ c ⇒ r, ρ', σ'` | `Exec p ρ σ c r ρ' σ'` |
| ρ, σ ⊢ c̄ ⇒ r, ρ′, σ′ | `⟨ρ, σ⟩ ⊢ cs ⇒* r, ρ', σ'` | `Execs p ρ σ cs r ρ' σ'` |
| Γ ⊢ e : τ | `Γ ⊢ e : τ` | `HasType p Γ e τ` |
| Γ ⊢ₗ e : τ | `Γ ⊢ₗ e : τ` | `LHasType p Γ e τ` |
| Γ ⊢ e ◁ τ | `Γ ⊢ e ◁ τ` | `Accept p Γ e τ` |
| Γ ⊢ c ⊣ Γ′ under τᵣ | `⟨Γ, τᵣ⟩ ⊢ c ⊣ Γ'` | `Check p τᵣ Γ c Γ'` |
| Γ ⊢ c̄ ⊣ Γ′ under τᵣ | `⟨Γ, τᵣ⟩ ⊢ cs ⊣* Γ'` | `Checks p τᵣ Γ cs Γ'` |

It makes two concessions to the parser. The configuration ⟨ρ, σ⟩, and ⟨Γ, τᵣ⟩ for a command with the result type of
its body, are in angle brackets, since a notation that starts with a bare
term and a comma would register a parser on every comma and break the tuples
of Lean. A sequence of commands takes `⇒*` and `⊣*`, since the parser cannot
tell a command from a list of commands. The program is the `p`
in scope, the parameter of the relations, so that no rule names it, as in the
blueprint. The notation is declared before the relations and with
`hygiene false`, so that `p` and the names `Eval`, `LEval`, `Exec` and
`Execs` resolve at the use site, the latter to the relations under definition
inside the `mutual` block. The name of a constructor must lead in the syntax
of `inductive`, so the rule name appears twice, as the constructor and on the
inference line. A command of our own that reads a rule premises first is
possible, some fifty lines of `syntax` and `macro_rules`, and was not judged
worth it.

## `error` is the absence of a derivation

The relations have no `error`. A dereference of `nullptr`, a division by
zero, an overflow, an index out of bounds, a missing return, a double
`delete`, a `delete` through a base pointer without a virtual destructor and
every other case C++17 leaves undefined have no derivation, because a premise
of every rule that could reach them fails, `σ(ℓ) = v`, `n₂ ≠ 0`,
`n ∈ [−2³¹, 2³¹ − 1]`, `0 ≤ i < n`. The evaluator keeps its `Error` with the
messages and the exit code 134.

This is the choice of Radix, and it helps the proofs in two ways. No rule
propagates an error, since a premise without derivation gives a conclusion
without derivation, so there is no constructor Seq with `error` in its first
command, no While with `error` in its body, no Call with `error` in an
argument. Every induction on a relation has one case per construction and
none for propagation. The price is what the relation cannot say. "This
program gives `error`" is a statement about the evaluator, and the claim of
the design, that everything C++17 leaves undefined gives `error`, becomes
"a well typed program is stuck only at the undefined cases". The rules of the
blueprint that conclude `error`, Div-Zero and Deref-Null, become the cases
where no rule applies, stated as side conditions of the rules that do.

## The library

A module is a relation plus a function. The relation, in
`CoreCpp/Semantics/Library.lean`, is the specification of the names the
header of the module declares, in the forms of the judgements of the
language. The structure `Module` has the four relations a module may give,
`new`, `index`, `delete` and `call`, each an instance of a judgement of the
language, left at `False` when the entity does not have it. The rules of the
language for a subject of the library, NewLib, LocIndex, DeleteLib and
CallLib, take the relation of the module as a premise. In the relation nothing
is called. The premise holds or it does not. Only the interpreter, when it
checks that premise, calls the module's function, and soundness proves that
the function agrees with the relation.

The static side is the structure `StaticModule`, the signatures of the uses as
relations, `wf`, `new`, `index`, `delete` and `call`, which the rules
T-NewLib, T-IndexLib, T-LocIndexLib, T-DeleteLib and T-CallLib take as
premises, and WF-Lib for the well formed instances. The module is found by
the name the header declares, `moduleOf` and `staticOf`, and nothing else
links the two.

The function side, `CoreCpp/Std/Module.lean`, mirrors the two structures.
`StaticFns` has `wf`, `new`, `index`, `delete` and `call` as functions, the
signatures of `new` as a list, one per arity, and `Fns` has the dynamic
functions, each returning the name of the rule it concludes for the trace.
`Std.staticFnsOf` and `Std.fnsOf` find them by the declared name, and
`Std.isObject` is true of a class and of a library type whose module gives
`new` a signature. The type checker calls them where the rules have a module
premise, `staticsOf` in `Typing.lean`, and the evaluator through `libStep`,
which records the premise in the trace under the rule of the module. No flag describes a type of the library. Whether a type is
an object type is read from the keyword `class` of its declaration in the
header. Whether a type converts to it is an instance of τ′ ↪ τ that the module
adds. No field has a library type, since every library type is an object,
so the default `new` gives a field is `Ty.default` of a basic or pointer
type, and no module needs a default. The structures `Statics`, `Intrinsic`,
`Sig`, `Use` and `Result` of the former `CoreCpp/Std/Intrinsic.lean`, the
node `Expr.intrinsic`, the rewriting of the uses in `Typing.annotate` and the
flags `convertible` and `hasDefault` are gone since step 4.

An object type is a class or an entity of the library whose module gives
`new` a signature, `Semantics.IsObject`, so no flag says which library types
are objects. The implementation of the test, `Std.isObject`, asks the
functions of the module for the signatures of `new` and is true when there is
one.

`std::function` is an object, by the decision of 2026-10-01, and the
relations state it. `new std::function<F>(λ)` creates it, rules F-New and
TF-New of its module, with the closure as its target at a location of its
own, and `new std::function<F>()` creates the function with no target, rules
F-Empty and TF-Empty, `null` at that location, as default construction does
in N4659 §23.14.13.2.1 ¶1. It is reached by pointer and called as `(*f)(ē)`,
rule CallFn of the language, which reads the target and applies it, and a
call of the function with no target has no derivation. A lambda is
acceptable at its function type F, rule T-Lambda, so it occurs as the
argument of `new`. No variable, field or parameter has the type by value,
since it is an object type, and a reference to it binds as any object does.
The interpreter, the tests, the examples and the blueprint follow, since
step 4.

## Overload resolution

The rule T-Overload of the blueprint selects, among the candidates of a name,
the one that accepts the arguments, the exact one when several accept, and
rejects the ambiguous call. A relation cannot state it. "No other candidate
accepts the arguments" places the typing relation under a negation, which
Lean's positivity condition forbids in an inductive proposition. The relation
therefore reads the signature `Typing.annotate` fills into the call, rules
T-Call and T-Method with `Program.pickFun` and `Program.pickMethod`, and a
call without a signature has a derivation only when its name has one
candidate. The uniqueness and the rejection of ambiguity are properties of
the type checker, to be stated as theorems about it, not rules of the
relation. The same holds of the rule Distinguishable, which is a condition of
`ClassOk` and `ProgramOk` on the declared signatures alone.

## Preproc

Unchanged. `#include <h>` is replaced by the header, a Core C++ file that
declares the names. The header makes the program well formed, the Lean module
of the same name gives the rules, and the link between them is the name.

## Layout

| Directory or file | Role |
| --- | --- |
| `CoreCpp/Semantics.lean` | the domains, ℓ, v, ρ, σ, r |
| `CoreCpp/Semantics/Library.lean` | the relations of the modules and `moduleOf` |
| `CoreCpp/Semantics/Dynamic.lean` | the dynamic judgements, `Eval`, `LEval`, `Exec`, `Execs` and the auxiliaries |
| `CoreCpp/Semantics/Static.lean` | the static judgements, `HasType`, `LHasType`, `Accept`, `Check`, `Checks`, `WF`, `FunOk`, `ClassOk`, `ProgramOk` |
| `CoreCpp/Eval.lean`, `CoreCpp/Typing.lean` | the interpreters, on fuel |
| `CoreCpp/Std/` | the functions of the modules |
| `CoreCpp/Proofs/` | determinism, soundness, completeness, to come |

## The interpreter

`Eval.lean` keeps its monad and its trace. The trace it prints is a derivation
of the relation. Since step 4 every function of its `mutual` block, and every
function of the two blocks of `Typing.lean`, with `wellFormed`, `refReturns`
and `refRets`, takes a first argument `fuel : Nat` and recurses on it
structurally, as in Radix, so that theorems about them are possible. No
`partial def` remains in the two files. Fuel exhaustion is `Error.outOfFuel`
and `TypeError.outOfFuel`, and `runWith`, `run` and `typingFuel` give a bound
of 10⁶ that no program reaches, since fuel bounds the depth of a derivation
and not its size. The library sites are calls of the module functions where
the relation has a module premise. Its results on every test and example
stayed the same, and the examples of `std::function` were rewritten with
`new` and `(*f)(ē)`.

## The theorems

For each dynamic judgement, with `n` the fuel.

- Determinism. `Eval p ρ σ e v₁ σ₁ → Eval p ρ σ e v₂ σ₂ → v₁ = v₂ ∧ σ₁ = σ₂`.
  The claim "deterministic" of `CLAUDE.md` becomes this theorem.
- Soundness. `expr n p ρ σ e = .ok (v, σ′) → Eval p ρ σ e v σ′`.
- Completeness. `Eval p ρ σ e v σ′ → ∃ n, expr n p ρ σ e = .ok (v, σ′)`.
- Fuel monotonicity, so that the existential of completeness composes.

## The blueprint

Since step 6 each node points at the inductive of its judgement, a type and
so an admissible target, beside the function that implements it, and the
node `judg_relations` of the domains chapter presents the relations, the
notation table, the interpreters on fuel and the two theorems to come. The
Library chapter presents the rules of each module under the same judgement
as the language's rules. The domains chapter states `error` as the absence
of a derivation, and every rule that concluded `error`, DivZero and the
second rule of `int32`, became a remark that the case has no derivation and
that the evaluator gives `error`.

## Order of the work

Each step leaves every check green, `lake build`, the three test files,
`bin/compare` with 35 agreements and 8 expected differences, and
`lake exe vbp build`, and each is a commit on the branch.

1. This note.
2. `Semantics/Library.lean` and `Semantics/Dynamic.lean`, the dynamic
   judgements transcribed from the comments of `Eval.lean`, no proof. Done
   with this note.
3. `Semantics/Static.lean`, the static judgements transcribed from
   `Typing.lean`. Done. The judgements on declarations, `FunOk`, `ClassOk`
   and `ProgramOk`, are structures of named conditions rather than
   inductives with one constructor, since their conditions are side
   conditions on the declarations and not premises on subterms.
4. The interpreter. `Eval.lean` and `Typing.lean` on fuel, the library as
   relation plus function, the intrinsics gone, `Typing.annotate` without the
   rewriting of uses, `std::function` as an object, with the tests, the
   examples, the Library chapter and the lambda nodes of the blueprint, and
   the design lines of `CLAUDE.md`. Done. The grammar needed no production,
   since `new ClassType Args` and `( Expr ) Args` already derive
   `new std::function<F>(λ)` and `(*f)(ē)`.
5. Determinism, then soundness, then completeness. Postponed by decision
   of 2026-10-02, the convergence of each chapter comes first.
6. The blueprint and the design lines of `CLAUDE.md`. Done.

## Open

- Whether `locOf` and the fields `static` and `sig` stay in the AST as the
  annotations of the type checker, or the relation is stated over the source
  program with the annotations as premises.
- The merge order with `converge-chapter-2` and `converge-chapter-3`, both
  unmerged, and the redo of their open defects on this design.
- The grammar, if `new std::function<F>(λ)` needs a production.
- The condition `inherited` of `ClassOk` transcribes the type checker as it
  is, a redefined method must be marked `virtual` in the base, which rejects
  the third level of a chain. The decision that `override` implies `virtual`,
  as in C++17 §13.3 ¶2, changes both the relation and the type checker, on a
  branch of chapter 6.
