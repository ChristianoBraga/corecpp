# Plan. The theorem `progress`

## The node of the blueprint

The node `progress` of `docs/CoreCppBlueprint/Chapters/Abstraction.lean`
states that a well typed program has a derivation, does not terminate, or is
stuck at a case the evaluator reports as `error`. The stuck cases are those
C++17 leaves undefined, the end of a `main` without `return`, the call of a
`std::function` with no target and a failed `assert`. The node says "There
is no Lean proof yet".

`CoreCpp/Semantics/Progress.lean` states it with fuel.

```
def Progress (p : Program) : Prop :=
  ProgramOk p → ∀ fuel e, runMain p fuel = .error e → e ≠ .outOfFuel → e.isGuard = false
```

The guards are `undeclaredVariable`, `undeclaredFunction`, `arity`,
`typeError` and `notCallable`, the causes that only a program the type
checker rejects can reach.

## The statement is false as written

`runMain p` evaluates the program as parsed. An unannotated call takes the
first function of its name, `FunEnv.lookupSig` with `none`. The program

```cpp
int f(bool b) { if (b) { return 1; } return 0; }
int f(int n) { return n; }
int main() { return f(3); }
```

passes `check`, and `runMain p 1000` gives
`typeError "condition of if is not boolean, got 3"`, a guard, while `run p`
gives 3. Checked on 2026-11-16 with a scratch script. No theorem yet links
`check` to `ProgramOk`, so the counterexample to `Progress` assumes that
`ProgramOk p` holds when `check p` succeeds.

The evaluator never runs the program as parsed. `run` evaluates the program
`prepare` gives, `run_eq`. The statement must quantify over that program.

```
def Progress (p : Program) : Prop :=
  ProgramOk p → ∀ q, prepare p = .ok q →
    ∀ fuel e, runMain q fuel = .error e → e ≠ .outOfFuel → e.isGuard = false
```

## What the proof needs

### 1. The typing of the annotated program

The proof inducts on the evaluation of `q`, and the typing facts concern
`p`. Two routes connect them.

1. Preservation of typing by `annotate`, `ProgramOk p → annotate p = .ok q →
   ProgramOk q`, plus the facts the annotations carry. Each `sig` names an
   overload of the callee with that signature, and each `static` is the
   class of the receiver in Γ.
2. The elaboration judgment Γ ⊢ e : τ ⇝ e′ of
   `.claude/relational-semantics.md`, with `annotate` as its interpreter.
   The typing derivation then yields the annotated term, and the proof
   follows the elaboration.

Route 2 also closes the gap of `run_sound`, which covers `q` and not `p`.
Route 1 is smaller. Either way the type checker needs soundness for the
relations, `Typing.expr`, `Typing.cmd` and `check` with respect to
`HasType`, `Check` and `ProgramOk`, unless the proof starts from the
relations alone.

### 2. Typed configurations

The judgments of the evaluator carry no types, so the proof needs a typing of
the dynamic domains.

- A store typing Σ, a finite map from locations to types, and the value
  judgment Σ ⊢ v : τ. Integers, booleans, `void`, `null` at every pointer
  type, `loc ℓ` at `C*` when σ(ℓ) is an object whose tag is a subclass of
  C, and `lib L ℓ̄` at its template instance.
- Well formed objects. The tag names a class of the program, and the fields
  of `obj T […]` are those of the chain of T, each at a location of its
  declared type.
- The library. A vector holds locations of its element type. A
  `std::function` holds `null` or a closure of its function type.
- Closures. The body checks under the captured context, and each captured
  value has the type of its variable.
- The consistency of Γ with ρ and σ. Every variable of Γ is bound in ρ at
  a location of its type, and `this` at a receiver of the current class.
- A location outside dom σ needs no invariant. A read of it is
  `danglingLocation`, which is not a guard. The store typing never shrinks,
  so scope exit and `delete` leave it as it is.

### 3. The main lemma

The proof follows `InterpSound.lean`, one induction on the fuel for every
function of the evaluator at once. A predicate `Safe c P` states that every
result of c is a value satisfying P or an error that is not a guard. Its
lemmas mirror those of `Ok`, for sequencing, `traced`, `tracedLib`,
`tracedCases` and the loops of `for`.

For `expr`, with Γ ⊢ e : τ and the configuration consistent, every value
`(r, σ′)` has r of type τ under some Σ′ ⊇ Σ, an lvalue of type τ when
Γ ⊢ₗ e : τ, and σ′ consistent. The commands, the calls, `runMember`,
`applyVals` and the library follow the same pattern.

Each case discharges the guards of its body.

| Guard | Discharged by |
| --- | --- |
| `undeclaredVariable` | Γ consistent with ρ, T-Var and T-VarField |
| `undeclaredFunction` | T-Call and the `sig` that `annotate` wrote |
| `arity` | T-Call, T-Method, T-CallLib and the length of the parameters |
| `typeError` | the value judgment, case by case, including `resolve`, which finds the method by `ClassOk` and the subclass order |
| `notCallable` | the typing of `std::function` and of its target |

### 4. Steps

1. Restate `Progress` over `prepare`, in `Progress.lean` and in the node of
   the blueprint.
2. Prove the soundness of the type checker for the static relations, or
   choose to start from the relations and prove that `annotate` preserves
   them.
3. Define the typed configurations of section 2 in a new file
   `CoreCpp/Semantics/Safety.lean`.
4. Prove the lemmas of `Safe` and the main lemma, one function of the
   evaluator at a time, in the order of `InterpSound.lean`.
5. Derive `Progress` for `run`, and link the node with `lean :=`.

## Open choices

1. Route 1 or route 2 of section 1. Route 2 changes the design of
   `annotate` and of the static relations.
2. Whether the main lemma also states preservation, the type of the
   result, which Radix proves as a theorem of its own. It is needed as an
   invariant anyway.
3. Whether `danglingLocation`, `missingReturn` and the other errors that
   are not guards need a finer statement, for instance that `danglingLocation`
   arises only after a `delete` or a scope exit.
