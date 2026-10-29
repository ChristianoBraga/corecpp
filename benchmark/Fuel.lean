import CoreCpp
import Preproc

/-!
# benchfuel, fuel and time of the evaluator on the benchmark corpus

    lake exe benchfuel <file.cpp>...

Prints one line per file, tab separated, with the name, the least fuel under
which the evaluator gives a result other than `outOfFuel`, the result at the
default fuel of `run`, and the time in milliseconds of that run. The fuel
bounds the depth of the derivation, so the least fuel is the depth of the
derivation of the program. A doubling search finds the least power of two
that suffices, and a binary search below it finds the least fuel, assuming
that a result reached under some fuel is reached under any larger fuel. Run it from the root
of the repository, which holds `preproc/include`.
-/

open CoreCpp

def load (path : String) : IO (Option Program) := do
  let src ← IO.FS.readFile path
  match ← Preproc.translateLines "preproc/include" [] path src with
  | .error e => IO.eprintln e; return none
  | .ok lines =>
    match parseUnit lines with
    | .error e => IO.eprintln s!"{path}: {e}"; return none
    | .ok p =>
      match check p with
      | .error e => IO.eprintln s!"{path}: type error: {e}"; return none
      | .ok () => return some p

def exhausted : Except Error Val → Bool
  | .error .outOfFuel => true
  | _ => false

/-- The least fuel in `(lo, hi]` under which the program does not exhaust it,
given that it exhausts `lo` and not `hi`. -/
partial def least (p : Program) (lo hi : Nat) : Nat :=
  if hi ≤ lo + 1 then hi
  else
    let mid := (lo + hi) / 2
    if exhausted (run p mid) then least p mid hi else least p lo mid

/-- The least power of two `k ≥ n` under which the program does not exhaust
the fuel, given that it exhausts `n / 2`. -/
partial def doubling (p : Program) (n : Nat) : Nat :=
  if exhausted (run p n) then doubling p (2 * n) else n

def main (args : List String) : IO UInt32 := do
  for path in args do
    let some p ← load path | continue
    let t0 ← IO.monoNanosNow
    let r ← IO.lazyPure fun _ => run p
    let t1 ← IO.monoNanosNow
    let name := (System.FilePath.mk path).fileStem.getD path
    let res := match r with | .ok v => s!"{v}" | .error e => s!"error ({e})"
    let fuel := if exhausted r then "over" else
      let k := doubling p 1
      s!"{least p (k / 2) k}"
    IO.println s!"{name}\t{fuel}\t{res}\t{(t1 - t0).toFloat / 1000000}"
  return 0
