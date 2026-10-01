import CoreCpp.Syntax
import CoreCpp.Semantics

/-!
# The interface of an intrinsic

An intrinsic is an entity of the library, a class template of `namespace std`
or a function, that a header of Core C++ declares without a body. Its meaning
is a set of judgements in natural semantics, which the rules of the language
use as premises. The language knows no intrinsic by name. At a use it asks
the library for the signature of the use, the static judgement, and for its
result, the dynamic judgement. With L the intrinsic and τ̄ its template
arguments, the judgements are the following.

    Γ ⊢_L L⟨τ̄⟩ ok              instOk      the instance is well formed
    Γ ⊢_L u : τ̄ₐ → τ           sig         the signature of the use u
    Γ ⊢_L τ ↪ L⟨τ̄⟩             convFrom    τ converts to L⟨τ̄⟩
    default L⟨τ̄⟩ = v           default     the value new gives a field of the type
    σ ⊢_L u(v̄) ⇒ r, σ′         eval        the result of the use u

The dynamic judgement may use one judgement of the language, the application
of a closure, which the language passes as `apply`.
-/

namespace CoreCpp.Std

/-- The uses of an entity of the library that the language delegates. -/
inductive Use where
  | new
  | member (m : String)
  | call
  | delete
  deriving Repr, BEq, Inhabited

/-- The name of a use in an `Expr.intrinsic` node. -/
def Use.toString : Use → String
  | .new => "new"
  | .member m => m
  | .call => "call"
  | .delete => "delete"

def Use.ofString : String → Use
  | "new" => .new
  | "call" => .call
  | "delete" => .delete
  | m => .member m

/-- The signature of a use. The parameters take their arguments by value, and
the mark `retLoc` says that the result is a location, as `v[i]` is. -/
structure Sig where
  params : List Ty
  ret : Ty
  retLoc : Bool := false
  deriving Inhabited

/-- The result of a use, a value or a location. -/
inductive Result where
  | val (v : Val)
  | loc (l : Loc)

/-- The static part of an intrinsic, the judgements the type checker uses. -/
structure Statics where
  /-- The qualified name of the declaration, `std::vector` or `assert`. -/
  name : String
  /-- The number of template parameters, or of parameters for a function. -/
  arity : Nat
  /-- The values of its instances live in the store and are never copied. -/
  isObject : Bool := false
  /-- Another type converts to it, so a parameter of its type tells no two
  overloads apart. -/
  convertible : Bool := false
  /-- Γ ⊢_L L⟨τ̄⟩ ok. -/
  instOk : List Ty → Except String Unit := fun _ => .ok ()
  /-- Γ ⊢_L u : τ̄ₐ → τ, at the template arguments τ̄. -/
  sig : Use → List Ty → Except String Sig
  /-- Γ ⊢_L τ ↪ L⟨τ̄⟩. -/
  convFrom : List Ty → Ty → Bool := fun _ _ => false
  /-- default L⟨τ̄⟩, the value `new` gives a field of the type before the
  constructor runs, `none` when the type has no default, an object type for
  instance. -/
  default : List Ty → Option Val := fun _ => none

/-- An intrinsic, its static judgements and its dynamic one. The dynamic
judgement is polymorphic in the monad of the evaluator, which passes the
application of a closure as its first argument. -/
structure Intrinsic extends Statics where
  /-- σ ⊢_L u(v̄) ⇒ r, σ′, with the name of the rule that gives it. -/
  eval : {m : Type → Type} → [Monad m] → [MonadExcept Error m] →
    (Val → List Val → Store → m (Val × Store)) →
    Use → List Ty → List Val → Store → m (String × Result × Store)

end CoreCpp.Std
