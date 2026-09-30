import CoreCpp
import Preproc

/-!
# corecpp, the Core C++ command line interpreter

    corecpp ast   <file>   parse and print the abstract syntax tree
    corecpp check <file>   parse and type check
    corecpp run   <file>   parse, type check and evaluate, printing the result of main
    corecpp trace <file>   as run, printing the derivation before the result
    corecpp <file>         same as run

Every mode first runs Preproc on the file, with the headers of Core C++ from
`preproc/include` and the flags of the options `-D CCPP_X=`, which go before
the file.

`<file>` may be `-` for standard input, so that

    echo 'int main() { return 42; }' | corecpp - ; echo $?

behaves like compiling with g++ and running the program. The exit code of `run`
and `trace` is the value returned by main, reduced modulo 256 as the operating
system does. An `error` result exits with 134, the code of an aborted process,
and a syntax or type error exits with 1.

The mode `trace` lays the derivation out as one writes it on the board, the
premises over a line of inference and the conclusion under it, with a legend
naming the environments, the stores and the long subjects, and the subtrees
too wide for the page written apart as named derivations.
-/

open CoreCpp

def usage : String :=
  "usage: corecpp [ast|check|run|trace] [-D CCPP_X=]... <file.cpp | ->"

def readSource (path : String) : IO String :=
  if path == "-" then do
    let stdin ← IO.getStdin
    stdin.readToEnd
  else IO.FS.readFile path

/-- The headers of Core C++. The executable is `.lake/build/bin/corecpp` in the repository. -/
def includeDir : IO System.FilePath := do
  let app ← IO.appPath
  let root := app.parent.bind (·.parent) |>.bind (·.parent) |>.bind (·.parent)
  return (root.getD ".") / "preproc" / "include"

def load (flags : List String) (path : String) : IO (Option Program) := do
  let lines ← match ← Preproc.translateLines (← includeDir) flags path (← readSource path) with
    | .ok t => pure t
    | .error e => IO.eprintln e; return none
  match parseUnit lines with
  | .ok p => return some p
  | .error e => IO.eprintln s!"{path}: {e}"; return none

def typed (p : Program) : IO Bool := do
  match check p with
  | .ok () => return true
  | .error e => IO.eprintln s!"type error: {e}"; return false

/-- Exit code of a program result, as the operating system would compute it. -/
def exitCode : Except Error Val → UInt32
  | .ok (.int n) => (n % 256).toNat.toUInt32
  | .ok _        => 0
  | .error _     => 134

def report (r : Except Error Val) : IO UInt32 := do
  match r with
  | .ok v    => IO.println s!"main() ⇒ {v}"
  | .error e => IO.eprintln s!"main() ⇒ error ({e})"
  return exitCode r

def dispatch (cmd : String) (flags : List String) (path : String) : IO UInt32 := do
  match cmd with
  | "ast" =>
    let some p ← load flags path | return 1
    IO.println (toString (repr p))
    return 0
  | "check" =>
    let some p ← load flags path | return 1
    if ← typed p then IO.println "well typed"; return 0 else return 1
  | "run" =>
    let some p ← load flags path | return 1
    if !(← typed p) then return 1
    report (run p)
  | "trace" =>
    let some p ← load flags path | return 1
    if !(← typed p) then return 1
    let (r, log) := runWith true p
    IO.println (renderTrace log)
    IO.println ""
    report r
  | _ => IO.eprintln usage; return 64

/-- The flags of the options `-D CCPP_X=` or `-DCCPP_X=`, and the other arguments. -/
def flagsOf : List String → Option (List String × List String)
  | [] => some ([], [])
  | "-D" :: d :: rest => cons d rest
  | a :: rest => if a.startsWith "-D" && a.length > 2 then cons (a.drop 2).toString rest
    else (flagsOf rest).map fun (fs, as) => (fs, a :: as)
where
  cons (d : String) (rest : List String) : Option (List String × List String) :=
    match d.splitOn "=" with
    | [f, ""] => if Preproc.isFlag f then (flagsOf rest).map fun (fs, as) => (f :: fs, as) else none
    | _ => none

def main (args : List String) : IO UInt32 := do
  match flagsOf args with
  | some (flags, [cmd, path]) => dispatch cmd flags path
  | some (flags, [path])      => dispatch "run" flags path
  | _                         => IO.eprintln usage; return 64
