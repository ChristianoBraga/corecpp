import CoreCpp.Syntax

/-!
# Core C++ semantic domains

Locations ℓ, values v, environment ρ, store σ, control results r and the
`error` result. Section 6 of the language design.

* ρ : Id → ℓ, the environment, maps identifiers to locations.
* σ : ℓ → v, the store, maps locations to values. The domain of σ is the set of
  live locations. A counter gives fresh locations, and removing a location
  never decreases it, so locations are never reused.
* An object is a record of locations with a class tag, stored at its own
  location. A pointer value is the location of an object. A value of the
  library, such as a vector, carries the name of its template and a list of
  locations, whose meaning its module of `CoreCpp.Std` gives.
* A closure is the value of a lambda expression, its parameters, its body
  and the read only copies of the variables it captured.
* Inside a method, `this` is bound in ρ to the location of the receiver, an
  alias binding, and `delete` removes the locations of an object from σ.
-/

namespace CoreCpp

/-- A location ℓ, a natural number. The store hands them out in increasing
order, so a location is never reused. -/
abbrev Loc := Nat

/-- Values.

`int` is a 32-bit two's complement integer, stored as an `Int` with the range
invariant checked at every operation. `loc` is a pointer to the object stored
at ℓ, and `null` is the value of `nullptr`.

`obj` is an object with its class tag and one location per field, and
`lib L ℓ̄` a value of the library entity `L` with its locations.

`closure ps τ c cap` is the value of `[=](ps) -> τ { c }`, carrying the values
the lambda captured by copy, one per free variable of the body. -/
inductive Val where
  /-- An integer of `int`, within the range of `Int32`. -/
  | int  (n : Int)
  /-- A truth value of `bool`. -/
  | bool (b : Bool)
  /-- The result of a function without return value, and the initial content
  of a field of type `std::function`. -/
  | void
  /-- A pointer, the location of an object or of an instance of the library. -/
  | loc  (l : Loc)
  /-- The value of `nullptr`. -/
  | null
  /-- An object of class `tag`, one location per field of its chain. -/
  | obj  (tag : String) (fields : List (String × Loc))
  /-- An instance of the library entity `tag`, with its locations. -/
  | lib  (tag : String) (locs : List Loc)
  /-- The value of a lambda, its parameters, result type, body and copies. -/
  | closure (params : List Param) (ret : Ty) (body : List Cmd) (captured : List (String × Val))
  deriving Repr, BEq, Inhabited

/-- The least value of `int`, −2³¹. -/
def Int32.min : Int := -(2 ^ 31)
/-- The greatest value of `int`, 2³¹ − 1. -/
def Int32.max : Int := 2 ^ 31 - 1
/-- Whether n lies in the range of `int`, the test of the partial operation
`int32`. -/
def Int32.inRange (n : Int) : Bool := Int32.min ≤ n && n ≤ Int32.max

/-- The default value of a type, the one `new` gives to every field and
element before the constructor runs, `int 0`, `bool false` and `null`. Object
types have no value, their default is never asked. A field of type
`std::function` starts empty, `void`, and a call through it before the
constructor assigns a lambda is `error`, as the `bad_function_call` of C++. -/
def Ty.default : Ty → Val
  | .int => .int 0
  | .bool => .bool false
  | .ptr _ => .null
  | _ => .void

/-- The `error` result. It is not a value of the language. No syntax produces,
tests or catches it. It corresponds in C++ to abnormal program termination. -/
inductive Error where
  /-- A division or a remainder by zero. -/
  | divisionByZero
  /-- An `int` result outside the range of `Int32`. -/
  | overflow
  /-- The dereference of `nullptr`. -/
  | nullDereference
  /-- The index `i` outside a vector of `n` elements. -/
  | outOfBounds (i n : Int)
  /-- A vector created with the negative size `n`. -/
  | negativeSize (n : Int)
  /-- A read or a write of a location outside dom σ. -/
  | danglingLocation (l : Loc)
  /-- A variable that neither ρ nor the fields of the receiver bind. -/
  | undeclaredVariable (x : String)
  /-- A function the program does not declare, a guard for a program that
  skipped the type checker. -/
  | undeclaredFunction (f : String)
  /-- A call with the wrong number of arguments, a guard for a program that
  skipped the type checker. -/
  | arity (f : String)
  /-- A value of the wrong form, a guard for a program that skipped the type
  checker. -/
  | typeError (msg : String)
  /-- A non `void` function whose body ends without `return`. -/
  | missingReturn (f : String)
  /-- The call of a value that is not a closure, an unassigned `std::function`
  field. -/
  | notCallable (v : Val)
  /-- A `delete` through a pointer to the base `static` of an object of class
  `tag`, with no virtual destructor in the chain of `static`. -/
  | deleteWithoutVirtualDtor (static tag : String)
  /-- A second `delete` of the object at ℓ. -/
  | doubleDelete (l : Loc)
  /-- An error that a rule of `CoreCpp.Std` gives, a failed `assert`. -/
  | library (msg : String)
  deriving Repr, BEq, Inhabited

/-- A binding of ρ. `owned` records whether the declaration that created the
binding allocated the location, as `τ x = e` does, or aliased an existing one,
as the reference `τ& y = e` does. Block exit frees only owned locations, so an
alias never removes the location of the variable it names. -/
structure Binding where
  /-- The location the identifier denotes. -/
  loc   : Loc
  /-- Whether the declaration allocated the location, so scope exit frees it. -/
  owned : Bool := true
  deriving Repr, BEq, Inhabited

/-- Environment ρ, a finite map from identifiers to locations. The most recent
entry wins, which realises shadowing by inner blocks. -/
abbrev Env := List (String × Binding)

/-- ρ(x), the location of the most recent binding of x. -/
def Env.lookup (ρ : Env) (x : String) : Option Loc :=
  (ρ.find? (·.1 == x)).map (·.2.loc)

/-- ρ[x ↦ ℓ], a binding to a location the declaration allocated. -/
def Env.extend (ρ : Env) (x : String) (l : Loc) : Env := (x, ⟨l, true⟩) :: ρ

/-- ρ[x ↦ ℓ] for a reference, a binding to a location that already exists. -/
def Env.alias (ρ : Env) (x : String) (l : Loc) : Env := (x, ⟨l, false⟩) :: ρ

/-- Store σ with the location counter. `next` is the next free location.
Every location of `mem` lies below `next`, and only `alloc` increases it. -/
structure Store where
  /-- The bindings of σ, the most recent first. -/
  mem  : List (Loc × Val) := []
  /-- The next free location, the counter that `alloc` increments. -/
  next : Loc := 0
  deriving Repr, Inhabited

namespace Store

/-- σ(ℓ), or nothing if ℓ ∉ dom σ. -/
def read (σ : Store) (l : Loc) : Option Val :=
  (σ.mem.find? (·.1 == l)).map (·.2)

/-- σ[ℓ ↦ v] for ℓ ∈ dom σ. Outside the domain σ stays unchanged, and the
evaluator checks the domain first. -/
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

/-- dom σ, the live locations. -/
def dom (σ : Store) : List Loc := σ.mem.map (·.1)

end Store

/-- The control result r of a command. -/
inductive Ctrl where
  /-- The command completed, and the next command runs. -/
  | normal
  /-- A `return` with the value v, which interrupts sequence, block and loop
  up to the call. -/
  | ret (v : Val)
  deriving Repr, BEq, Inhabited

/-- Function environment, the program seen as a finite map from names to
overload sets. The whole program is threaded, because `new` also needs the
class table. -/
abbrev FunEnv := Program

/-- The first function named f, the lookup by name alone. -/
def FunEnv.lookup (fs : FunEnv) (f : String) : Option Fun :=
  fs.funs.find? (·.name == f)

/-- The function named f with the signature the type checker chose, or the
first one of the name when the program was not annotated. -/
def FunEnv.lookupSig (fs : FunEnv) (f : String) (sig : Option (List Ty)) : Option Fun :=
  match sig with
  | some s => (fs.funsNamed f).find? fun g => sigOf g.params == s
  | none => fs.lookup f

end CoreCpp
