import CoreCpp

/-!
# corecpp, the Core C++ command line interpreter

    corecpp ast   <file>   parse and print the abstract syntax tree
    corecpp check <file>   parse and type check
    corecpp run   <file>   parse, type check and evaluate, printing the result of main
    corecpp trace <file>   as run, printing the derivation before the result
    corecpp <file>         same as run

    corecpp fragment imperative|oo|functional <file>
                           whether the program lies in the fragment of the paradigm
    corecpp prolog <file>  run the queries of a logic program

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
  "usage: corecpp [ast|check|run|trace] <file.cpp | ->\n" ++
  "       corecpp fragment [imperative|oo|functional] <file.cpp | ->\n" ++
  "       corecpp prolog <file.pl | ->"

def readSource (path : String) : IO String :=
  if path == "-" then do
    let stdin ← IO.getStdin
    stdin.readToEnd
  else IO.FS.readFile path

def load (path : String) : IO (Option Program) := do
  let src ← readSource path
  match parseProgram src with
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

def dispatch (cmd path : String) : IO UInt32 := do
  match cmd with
  | "ast" =>
    let some p ← load path | return 1
    IO.println (toString (repr p))
    return 0
  | "check" =>
    let some p ← load path | return 1
    if ← typed p then IO.println "well typed"; return 0 else return 1
  | "run" =>
    let some p ← load path | return 1
    if !(← typed p) then return 1
    report (run p)
  | "trace" =>
    let some p ← load path | return 1
    if !(← typed p) then return 1
    let (r, log) := runWith true p
    IO.println (renderTrace log)
    IO.println ""
    report r
  | "prolog" =>
    let src ← readSource path
    match Logic.parse src with
    | .error e => IO.eprintln s!"{path}: {e}"; return 1
    | .ok (cs, qs) =>
      if qs.isEmpty then
        IO.eprintln s!"{path}: the file has no query"
        return 1
      for q in qs do
        IO.println (Logic.answersToString q (Logic.query cs q))
      return 0
  | _ => IO.eprintln usage; return 64

/-- The fragment modes, `corecpp fragment <name> <file>`. -/
def dispatchFragment (name path : String) : IO UInt32 := do
  let some f := Frag.ofString? name
    | IO.eprintln usage; return 64
  let some p ← load path | return 1
  match fragment f p with
  | .ok () => IO.println s!"in the {f} fragment"; return 0
  | .error r => IO.eprintln (toString r); return 1

def main (args : List String) : IO UInt32 := do
  match args with
  | ["fragment", name, path] => dispatchFragment name path
  | [cmd, path] => dispatch cmd path
  | [path]      => dispatch "run" path
  | _           => IO.eprintln usage; return 64
