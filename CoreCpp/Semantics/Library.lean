import CoreCpp.Semantics

/-!
# The judgements of the library, as relations

A module of the library gives the semantics of the names its header declares,
as relations in the forms of the judgements of the language. The rules of the
language for a subject of the library, `new L⟨τ̄⟩(ē)`, `e[i]`, `delete e` and
the call of a function declared without a body, take the relation of the
module as a premise. The module is found by the name the header declares, and
nothing else links the two.

These relations are the specification. The functions of `CoreCpp.Std` that
execute them are the implementation, to be proved sound with respect to them.
A use with no derivation here is `error` there.
-/

namespace CoreCpp.Semantics

/-- The relations a module may give. Each one is an instance of a judgement of
the language, and a module leaves at `False` the ones its entity does not
have. -/
structure Module where
  /-- σ ⊢_L new⟨τ̄⟩(v̄) ⇒ v, σ′, the creation of an instance. -/
  new : List Ty → List Val → Store → Val → Store → Prop := fun _ _ _ _ _ => False
  /-- σ ⊢_L v[i] ⇒ₗ ℓ, σ′, the location of an element. -/
  index : Val → Val → Store → Loc → Store → Prop := fun _ _ _ _ _ => False
  /-- σ ⊢_L delete v ⇒ σ′, the store after the instance leaves it. -/
  delete : Val → Store → Store → Prop := fun _ _ _ => False
  /-- σ ⊢_L f(v̄) ⇒ v, σ′, the call of a function declared without a body. -/
  call : List Val → Store → Val → Store → Prop := fun _ _ _ _ => False

/-! ## `std::vector`, the module of `<vector>` -/

namespace Vector

/-- σ ⊢_vector new⟨τ⟩(k) ⇒ loc ℓ, σ′. -/
inductive New : List Ty → List Val → Store → Val → Store → Prop where
  /-- A negative size has no derivation. -/
  | new
      (hk : 0 ≤ k)
      (ha : σ.allocMany (List.replicate k.toNat t.default) = (ls, σ₁))
      (ho : σ₁.alloc (.lib "std::vector" ls) = (ℓ, σ₂)) :
    -- ──────────────────────────────────────────────────────────── (V-New)
      New [t] [.int k] σ (.loc ℓ) σ₂

/-- σ ⊢_vector v[i] ⇒ₗ ℓ, σ. -/
inductive Index : Val → Val → Store → Loc → Store → Prop where
  /-- An index out of bounds has no derivation. -/
  | index
      (hi : 0 ≤ i)
      (hl : ls[i.toNat]? = some ℓ) :
    -- ──────────────────────────────── (V-Index)
      Index (.lib L ls) (.int i) σ ℓ σ

/-- σ ⊢_vector delete v ⇒ σ′. -/
inductive Delete : Val → Store → Store → Prop where
  /-- The language frees the location of the vector itself. -/
  | delete :
    -- ──────────────────────────────── (V-Delete)
      Delete (.lib L ls) σ (σ.free ls)

def module : Module := { new := New, index := Index, delete := Delete }

end Vector

/-! ## `std::function`, the module of `<functional>`

A value of `std::function<τ(τ̄)>` is a closure, a value of the language, and
its call is the application of a closure, the rule Apply. The module adds no
relation. -/

namespace Function

def module : Module := {}

end Function

/-! ## `assert`, the module of `<cassert>` -/

namespace Assert

/-- σ ⊢_assert assert(v) ⇒ void, σ. -/
inductive Call : List Val → Store → Val → Store → Prop where
  /-- A failed assertion has no derivation. -/
  | holds :
    -- ───────────────────────── (A-True)
      Call [.bool true] σ .void σ

def module : Module := { call := Call }

end Assert

/-- The module of a name a header declares. -/
def moduleOf : String → Option Module
  | "std::vector" => some Vector.module
  | "std::function" => some Function.module
  | "assert" => some Assert.module
  | _ => none

end CoreCpp.Semantics
