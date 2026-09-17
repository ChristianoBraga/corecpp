import CoreCpp.Syntax

/-!
# Core C++ semantic domains

Locations ℓ, values v, environment ρ, store σ, control results r and the
`error` result. Section 6 of the language design.

* ρ : Id → ℓ, the environment, maps identifiers to locations.
* σ : ℓ → v, the store, maps locations to values. The domain of σ is the set of
  live locations. Locations are never reused.
-/

namespace CoreCpp

/-- Memory location. -/
abbrev Loc := Nat

/-- Values. `int` is a 32-bit two's complement integer, stored as an `Int` with
the range invariant checked at every operation. -/
inductive Val where
  | int  (n : Int)
  | bool (b : Bool)
  | void
  deriving Repr, BEq, Inhabited

/-- Bounds of `int`. -/
def Int32.min : Int := -(2 ^ 31)
def Int32.max : Int := 2 ^ 31 - 1
def Int32.inRange (n : Int) : Bool := Int32.min ≤ n && n ≤ Int32.max

/-- The `error` result. It is not a value of the language. No syntax produces,
tests or catches it. It corresponds in C++ to abnormal program termination. -/
inductive Error where
  | divisionByZero
  | overflow
  | danglingLocation (l : Loc)
  | undeclaredVariable (x : String)
  | undeclaredFunction (f : String)
  | arity (f : String)
  | typeError (msg : String)     -- provisional, until the type checker exists
  | missingReturn (f : String)
  deriving Repr, BEq, Inhabited

/-- Environment ρ, a finite map from identifiers to locations. The most recent
entry wins, which realises shadowing by inner blocks. -/
abbrev Env := List (String × Loc)

def Env.lookup (ρ : Env) (x : String) : Option Loc :=
  (ρ.find? (·.1 == x)).map (·.2)

/-- ρ[x ↦ ℓ] -/
def Env.extend (ρ : Env) (x : String) (l : Loc) : Env := (x, l) :: ρ

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

/-- Function environment, the program seen as a finite map from names. -/
abbrev FunEnv := List Fun

def FunEnv.lookup (fs : FunEnv) (f : String) : Option Fun :=
  fs.find? (·.name == f)

end CoreCpp
