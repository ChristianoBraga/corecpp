import Preproc

/-!
# ccpp-pre, the preprocessor of Core C++

    ccpp-pre [-D CCPP_X=]... [-I dir] <file | -> [-o out]

A flag is given as `-D CCPP_X=` or `-DCCPP_X=`, with an empty replacement list
as `#define CCPP_X` gives. The headers of Core C++ come from `dir`, by default
`preproc/include` of the repository. The output goes to `out`, or to standard
output. A violation of the rules of Preproc exits with 1.
-/

open Preproc

def usage : String := "usage: ccpp-pre [-D CCPP_X=]... [-I dir] <file.cpp | -> [-o out]"

structure Opts where
  flags : List String := []
  includeDir : Option String := none
  input : Option String := none
  output : Option String := none

def parseFlag (s : String) : Except String String :=
  match s.splitOn "=" with
  | [f, ""] => if isFlag f then .ok f else .error s!"-D {s} needs a flag CCPP_X without __"
  | _ => .error s!"-D {s} needs the form CCPP_X=, with an empty definition"

def parseArgs : List String → Opts → Except String Opts
  | [], o => .ok o
  | "-D" :: f :: rest, o => do parseArgs rest { o with flags := o.flags ++ [← parseFlag f] }
  | "-I" :: d :: rest, o => parseArgs rest { o with includeDir := some d }
  | "-o" :: out :: rest, o => parseArgs rest { o with output := some out }
  | a :: rest, o =>
    if a.startsWith "-D" && a.length > 2 then do
      parseArgs rest { o with flags := o.flags ++ [← parseFlag (a.drop 2).toString] }
    else if o.input.isNone then parseArgs rest { o with input := some a }
    else .error usage

def main (args : List String) : IO UInt32 := do
  match parseArgs args {} with
  | .error e => IO.eprintln e; return 1
  | .ok o =>
    let some input := o.input | IO.eprintln usage; return 1
    let src ← if input == "-" then (← IO.getStdin).readToEnd else IO.FS.readFile input
    let dir ← match o.includeDir with
      | some d => pure (System.FilePath.mk d)
      | none => do
        -- The executable is .lake/build/bin/ccpp-pre in the repository.
        let app ← IO.appPath
        let root := app.parent.bind (·.parent) |>.bind (·.parent) |>.bind (·.parent)
        pure ((root.getD ".") / "preproc" / "include")
    match ← translate dir o.flags input src with
    | .error e => IO.eprintln e; return 1
    | .ok t =>
      match o.output with
      | some out => IO.FS.writeFile out t
      | none => IO.print t
      return 0
