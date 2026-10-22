import CoreCpp.Syntax
import CoreCpp.Semantics

/-!
# The functions of a module

A module of the library is a relation plus a function. The relations, in
`CoreCpp.Semantics.Library`, are the specification of the names its header
declares. The functions here are the implementation, one per relation, which
the type checker and the evaluator call where the rules of the language have
the relation as a premise. A use the relation does not derive is an error of
the function. Each dynamic function names the rule it concludes, for the
trace.

The language finds a module by the name its header declares, `Std.fnsOf` and
`Std.staticFnsOf`, and knows no module otherwise.
-/

namespace CoreCpp.Std

/-- The static functions of a module, the signatures of its uses at the
template arguments τ̄ of the instance. A use the module does not have gives
`none`. -/
structure StaticFns where
  /-- Γ ⊢_L L⟨τ̄⟩ ok, or why the instance is ill formed. -/
  wf : List Ty → Except String Unit := fun _ => .error "no instance"
  /-- Γ ⊢_L new : τ̄ₐ → τ, the signatures of `new`, each its parameter types
  and its result, one per arity. An entity with none is not an object. -/
  new : List Ty → List (List Ty × Ty) := fun _ => []
  /-- Γ ⊢_L operator[] : τ₁ → τ, a location, the index type and the element type. -/
  index : List Ty → Option (Ty × Ty) := fun _ => none
  /-- Γ ⊢_L delete ok. -/
  delete : List Ty → Bool := fun _ => false
  /-- Γ ⊢_L f : τ̄ₐ → τ, for a function declared without a body. -/
  call : Option (List Ty × Ty) := none

/-- The dynamic functions of a module, with the name of the rule each
concludes. A use the module does not have is a type error, which a well typed
program never reaches. -/
structure Fns where
  /-- σ ⊢_L new⟨τ̄⟩(v̄) ⇒ v, σ′. -/
  new : List Ty → List Val → Store → Except Error (String × Val × Store) :=
    fun _ _ _ => throw (.typeError "no new in this module")
  /-- σ ⊢_L v[i] ⇒ₗ ℓ, σ′. -/
  index : Val → Val → Store → Except Error (String × Loc × Store) :=
    fun _ _ _ => throw (.typeError "no indexing in this module")
  /-- σ ⊢_L delete v ⇒ σ′. -/
  delete : Val → Store → Except Error (String × Store) :=
    fun _ _ => throw (.typeError "no delete in this module")
  /-- σ ⊢_L f(v̄) ⇒ v, σ′. -/
  call : List Val → Store → Except Error (String × Val × Store) :=
    fun _ _ => throw (.typeError "no call in this module")

end CoreCpp.Std
