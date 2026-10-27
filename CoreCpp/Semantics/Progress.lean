import CoreCpp.Semantics.Dynamic
import CoreCpp.Semantics.Static
import CoreCpp.Eval

/-!
# The statement of progress

The theorem `progress` of the blueprint, with fuel. A well typed program has a
derivation, does not terminate, or is stuck at a case that the evaluator
reports as `error`. The inductive relations have no derivation for a program
that does not terminate, so the statement bounds the evaluation by fuel. For
every fuel the evaluator of `main` gives a value with a derivation, runs out of
fuel, or reports a cause of `error` that is not a guard against a program the
type checker rejects.
-/

namespace CoreCpp

/-- The causes of `error` that only a program the type checker rejects can
reach. -/
def Error.isGuard : Error → Bool
  | .undeclaredVariable _ | .undeclaredFunction _ | .arity _ | .typeError _ | .notCallable _ => true
  | _ => false

/-- The result of `main()` in the annotated program p with the given fuel. -/
def runMain (p : Program) (fuel : Nat) : Except Error Val :=
  (((Eval.expr fuel p [] {} (.call "main" [] none)).run.run {}).1).map (·.1)

namespace Semantics

/-- The statement of `progress`. For a well typed program p and every fuel, the
evaluation of `main()` gives a value v with a derivation of p ⇒ v, runs out of
fuel, or stops at a cause of `error` that is not a guard. -/
def Progress (p : Program) : Prop :=
  ProgramOk p → ∀ fuel,
    match runMain p fuel with
    | .ok v => Runs p v
    | .error .outOfFuel => True
    | .error e => e.isGuard = false

end Semantics

end CoreCpp
