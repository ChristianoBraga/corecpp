import Preproc

/-!
# Tests of Preproc

The programs of `tests/preproc/accepted/` run under several sets of flags.
Without `#include`, the lines that Preproc keeps are the lines that
`g++ -E -P -undef -x c++ -std=c++17` keeps, blank lines aside. With `#include`,
compiling the program with `g++` and running the output of Preproc with
`bin/corecpp` give the same exit status. Every program of
`tests/preproc/rejected/` violates a rule of Preproc and fails. Run from the
root of the repository with `lake env lean tests/Preproc.lean`.
-/

open Preproc

def includeDir : System.FilePath := "preproc/include"

def check (b : Bool) (what : String) : IO Unit :=
  unless b do throw (IO.userError s!"failed: {what}")

/-- The lines that carry tokens, without their `//` comments. The comparison
drops comments, which `g++ -E` removes and Preproc keeps. Rule 3 excludes
quotes, so `//` never stands inside a literal. -/
def nonblank (s : String) : List String :=
  let code (l : String) : String := (l.splitOn "//").head!
  ((s.splitOn "\n").map code).filter fun l => l.any (!·.isWhitespace)

def defines (flags : List String) : Array String := (flags.map (s!"-D{·}=")).toArray

def sh (cmd : String) (args : Array String) : IO IO.Process.Output :=
  IO.Process.output { cmd, args }

def preprocess (path : String) (flags : List String) : IO String := do
  match ← translate includeDir flags path (← IO.FS.readFile path) with
  | .ok t => return t
  | .error e => throw (IO.userError e)

/-- Selection agrees with the preprocessor of `g++`, on a program without `#include`. -/
def sameSelection (path : String) (flags : List String) : IO Unit := do
  let t ← preprocess path flags
  let out ← sh "g++" (#["-E", "-P", "-undef", "-x", "c++", "-std=c++17"] ++ defines flags ++ #[path])
  check (out.exitCode == 0) s!"g++ -E on {path}"
  check (nonblank t == nonblank out.stdout) s!"selection of {path} under {flags}"

/-- The exit status of `g++` on the program equals that of `bin/corecpp` on its output. -/
def sameStatus (path : String) (flags : List String) : IO Unit := do
  let t ← preprocess path flags
  IO.FS.writeFile "/tmp/preproc-test.i.cpp" t
  let c ← sh "g++" (#["-std=c++17", "-o", "/tmp/preproc-test"] ++ defines flags ++ #[path])
  check (c.exitCode == 0) s!"g++ on {path}"
  let g ← sh "/tmp/preproc-test" #[]
  let r ← sh "bin/corecpp" #["run", "/tmp/preproc-test.i.cpp"]
  check (g.exitCode == r.exitCode) s!"status of {path} under {flags}, g++ {g.exitCode}, corecpp {r.exitCode}"

#eval show IO Unit from do
  let dir := "tests/preproc/accepted"
  for flags in [[], ["CCPP_SMALL"], ["CCPP_DOUBLE"], ["CCPP_SMALL", "CCPP_DOUBLE"]] do
    sameSelection s!"{dir}/select.cpp" flags
    sameStatus s!"{dir}/select.cpp" flags
  for flags in [[], ["CCPP_FUN"]] do
    sameStatus s!"{dir}/headers.cpp" flags
  IO.println "accepted programs ok"

#eval show IO Unit from do
  let fs := (← System.FilePath.readDir "tests/preproc/rejected").map (·.path)
  for f in fs.qsort (·.toString < ·.toString) do
    match ← translate includeDir [] f.toString (← IO.FS.readFile f) with
    | .ok _ => throw (IO.userError s!"failed: {f} was accepted")
    | .error e => IO.println e
  IO.println s!"{fs.size} rejected programs ok"
