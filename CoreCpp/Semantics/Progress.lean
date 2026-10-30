import CoreCpp.Semantics.Dynamic
import CoreCpp.Semantics.Static
import CoreCpp.Semantics.InterpSound

/-!
# The statement of progress

The theorem `progress` of the blueprint, with fuel. A well typed program has a
derivation, does not terminate, or is stuck at a case that the evaluator
reports as `error`. The inductive relations have no derivation for a program
that does not terminate, so the statement bounds the evaluation by fuel. A
value of the evaluator has a derivation for every program, by `interp_sound`.
The statement below covers the errors. For every fuel the evaluator of `main`
runs out of fuel or reports a cause of `error` that is not a guard against a
program the type checker rejects.
-/

namespace CoreCpp

/-- The causes of `error` that only a program the type checker rejects can
reach. -/
def Error.isGuard : Error → Bool
  | .undeclaredVariable _ | .undeclaredFunction _ | .arity _ | .typeError _ | .notCallable _ => true
  | _ => false

namespace Semantics

/-- The statement of `progress`. For a well typed program p and every fuel,
an error of the evaluation of `main()` is the exhaustion of the fuel or a
cause of `error` that is not a guard. -/
def Progress (p : Program) : Prop :=
  ProgramOk p → ∀ fuel e, runMain p fuel = .error e → e ≠ .outOfFuel → e.isGuard = false

end Semantics

end CoreCpp
