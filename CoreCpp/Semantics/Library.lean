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

/-- The static relations a module may give, the signatures of its uses, each
an instance of a judgement of the type checker, at the template arguments τ̄
of the instance. A module leaves at `False` the ones its entity does not
have. -/
structure StaticModule where
  /-- Γ ⊢_L L⟨τ̄⟩ ok, the instance is well formed. -/
  wf : List Ty → Prop := fun _ => False
  /-- Γ ⊢_L new : τ̄ₐ → τ, the signature of the creation of an instance. -/
  new : List Ty → List Ty → Ty → Prop := fun _ _ _ => False
  /-- Γ ⊢_L operator[] : τ₁ → τ, a location, the signature of indexing. -/
  index : List Ty → Ty → Ty → Prop := fun _ _ _ => False
  /-- Γ ⊢_L delete ok, an instance is deleted. -/
  delete : List Ty → Prop := fun _ => False
  /-- Γ ⊢_L f : τ̄ₐ → τ, the signature of a function declared without a body. -/
  call : List Ty → Ty → Prop := fun _ _ => False

/-- The dynamic relations a module may give. Each one is an instance of a judgement of
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

/-- The element type of a vector has values and a default, so it is neither
an object type, nor a type of the library, nor `void`, `nullptr_t` or a
function type. -/
def isElement : Ty → Bool
  | .cls _ | .lib .. | .fn .. | .void | .nullT => false
  | _ => true

/-- Γ ⊢_vector new : int → std::vector<τ>*. -/
inductive TNew : List Ty → List Ty → Ty → Prop where
  | new :
    -- ──────────────────────────────────────── (TV-New)
      TNew [t] [.int] (.ptr (.lib "std::vector" [t]))

/-- Γ ⊢_vector operator[] : int → τ, a location. -/
inductive TIndex : List Ty → Ty → Ty → Prop where
  | index :
    -- ──────────────── (TV-Index)
      TIndex [t] .int t

/-- Γ ⊢_vector delete ok. -/
inductive TDelete : List Ty → Prop where
  | delete :
    -- ─────────── (TV-Delete)
      TDelete [t]

def statics : StaticModule :=
  { wf := fun ts => match ts with | [t] => isElement t = true | _ => False,
    new := TNew, index := TIndex, delete := TDelete }

end Vector

/-! ## `std::function`, the module of `<functional>`

A value of `std::function<τ(τ̄)>` is a closure, a value of the language, and
its call is the application of a closure, the rule Apply. The type is the
written form of the function type τ(τ̄), and the type checker treats it as
such. The module states only which instances are well formed, those whose
argument is a function type. -/

namespace Function

def module : Module := {}

def statics : StaticModule :=
  { wf := fun ts => match ts with | [.fn ..] => True | _ => False }

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

/-- Γ ⊢_assert assert : bool → void. -/
inductive TCall : List Ty → Ty → Prop where
  | call :
    -- ─────────────────── (TA-Call)
      TCall [.bool] .void

def statics : StaticModule := { call := TCall }

end Assert

/-- The dynamic relations of the module of a name a header declares. -/
def moduleOf : String → Option Module
  | "std::vector" => some Vector.module
  | "std::function" => some Function.module
  | "assert" => some Assert.module
  | _ => none

/-- The static relations of the module of a name a header declares. -/
def staticOf : String → Option StaticModule
  | "std::vector" => some Vector.statics
  | "std::function" => some Function.statics
  | "assert" => some Assert.statics
  | _ => none

end CoreCpp.Semantics
