import CoreCpp.Syntax

/-!
# Core C++ semantic domains

Locations ℓ, values v, environment ρ, store σ, control results r and the
`error` result. Section 6 of the language design.

* ρ : Id → ℓ, the environment, maps identifiers to locations.
* σ : ℓ → v, the store, maps locations to values. The domain of σ is the set of
  live locations. Locations are never reused.
* An object is a record of locations with a class tag, stored at its own
  location. A pointer value is the location of an object. A vector is an
  object whose record is the list of the locations of its elements.
-/

namespace CoreCpp

/-- Memory location. -/
abbrev Loc := Nat

/-- Values. `int` is a 32-bit two's complement integer, stored as an `Int` with
the range invariant checked at every operation. `loc` is a pointer to the
object stored at ℓ, `null` the value of `nullptr`, `obj` an object with its
class tag and one location per field, and `vec` a vector with one location
per element. -/
inductive Val where
  | int  (n : Int)
  | bool (b : Bool)
  | void
  | loc  (l : Loc)
  | null
  | obj  (tag : String) (fields : List (String × Loc))
  | vec  (elems : List Loc)
  deriving Repr, BEq, Inhabited

/-- Bounds of `int`. -/
def Int32.min : Int := -(2 ^ 31)
def Int32.max : Int := 2 ^ 31 - 1
def Int32.inRange (n : Int) : Bool := Int32.min ≤ n && n ≤ Int32.max

/-- The default value of a type, the one `new` gives to every field and
element. Object types have no value, their default is never asked. -/
def Ty.default : Ty → Val
  | .int => .int 0
  | .bool => .bool false
  | .ptr _ => .null
  | _ => .void

/-- The `error` result. It is not a value of the language. No syntax produces,
tests or catches it. It corresponds in C++ to abnormal program termination. -/
inductive Error where
  | divisionByZero
  | overflow
  | nullDereference
  | outOfBounds (i n : Int)
  | negativeSize (n : Int)
  | danglingLocation (l : Loc)
  | undeclaredVariable (x : String)
  | undeclaredFunction (f : String)
  | arity (f : String)
  | typeError (msg : String)     -- for programs that skipped the type checker
  | missingReturn (f : String)
  deriving Repr, BEq, Inhabited

/-- A binding of ρ. `owned` records whether the declaration that created the
binding allocated the location, as `τ x = e` does, or aliased an existing one,
as the reference `τ& y = e` does. Block exit frees only owned locations, so an
alias never removes the location of the variable it names. -/
structure Binding where
  loc   : Loc
  owned : Bool := true
  deriving Repr, BEq, Inhabited

/-- Environment ρ, a finite map from identifiers to locations. The most recent
entry wins, which realises shadowing by inner blocks. -/
abbrev Env := List (String × Binding)

def Env.lookup (ρ : Env) (x : String) : Option Loc :=
  (ρ.find? (·.1 == x)).map (·.2.loc)

/-- ρ[x ↦ ℓ], a binding to a location the declaration allocated. -/
def Env.extend (ρ : Env) (x : String) (l : Loc) : Env := (x, ⟨l, true⟩) :: ρ

/-- ρ[x ↦ ℓ] for a reference, a binding to a location that already exists. -/
def Env.alias (ρ : Env) (x : String) (l : Loc) : Env := (x, ⟨l, false⟩) :: ρ

/-- Store σ with the location counter. `next` is the next free location. -/
structure Store where
  mem  : List (Loc × Val) := []
  next : Loc := 0
  deriving Repr, Inhabited

namespace Store

/-- σ(ℓ), or nothing if ℓ ∉ dom σ. -/
def read (σ : Store) (l : Loc) : Option Val :=
  (σ.mem.find? (·.1 == l)).map (·.2)

/-- σ[ℓ ↦ v] for ℓ ∈ dom σ. -/
def write (σ : Store) (l : Loc) (v : Val) : Store :=
  { σ with mem := σ.mem.map fun (l', v') => if l' == l then (l', v) else (l', v') }

/-- Allocates a fresh location ℓ ∉ dom σ holding v. Returns ℓ and σ[ℓ ↦ v]. -/
def alloc (σ : Store) (v : Val) : Loc × Store :=
  (σ.next, { mem := (σ.next, v) :: σ.mem, next := σ.next + 1 })

/-- Allocates one fresh location per value, in order. -/
def allocMany (σ : Store) (vs : List Val) : List Loc × Store :=
  vs.foldl (fun (ls, σ) v => let (l, σ') := σ.alloc v; (ls ++ [l], σ')) ([], σ)

/-- σ ∖ L, removes the locations in L from the domain. Realises scope exit. -/
def free (σ : Store) (ls : List Loc) : Store :=
  { σ with mem := σ.mem.filter fun (l, _) => !ls.contains l }

def dom (σ : Store) : List Loc := σ.mem.map (·.1)

end Store

/-- Control result of a statement. -/
inductive Ctrl where
  | normal
  | ret (v : Val)
  deriving Repr, BEq, Inhabited

/-- Function environment, the program seen as a finite map from names. The
whole program is threaded, because `new` also needs the class table. -/
abbrev FunEnv := Program

def FunEnv.lookup (fs : FunEnv) (f : String) : Option Fun :=
  fs.funs.find? (·.name == f)

end CoreCpp
