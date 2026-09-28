import CoreCpp.Ebnf

/-!
# The LL(1) construction on the grammar of Python 3.8

The grammar is `tests/ll1/grammars/python38.ebnf`, generated from the file
`Grammar/Grammar` of CPython at the branch 3.8, the input of the parser
generator `pgen`. `pgen` reads each rule as a regular expression, turns it
into a DFA, and checks the FIRST sets of the arcs of its initial state only
(`Parser/pgen/pgen.py`, `calcfirst`,
https://raw.githubusercontent.com/python/cpython/3.8/Parser/pgen/pgen.py).

The programs are fourteen modules of the standard library of CPython 3.8 in
`tests/ll1/programs/python38/stdlib/`, from
https://github.com/python/cpython/tree/3.8/Lib, under the license of the
`LICENSE` file there, and five snippets in
`tests/ll1/programs/python38/snippets/`. `tests/ll1/python38tok.py` gives
their token classes with the tokenizer of the installed `python3`. Run from
the root of the repository with `lake env lean tests/ll1/Python.lean`.
-/

open CoreCpp.LL1 CoreCpp.EbnfFile

def grammarPath : String := "tests/ll1/grammars/python38.ebnf"

def check (b : Bool) (what : String) : IO Unit :=
  unless b do throw (IO.userError s!"failed: {what}")

/-- The rules with a conflict, each with the number of conflicting lookaheads. -/
def conflictRules (g : Grammar String) : List (String × Nat) :=
  let names := g.conflicts.map fun ((A, _), _) => ((A.splitOn ".").head!.splitOn "#").head!
  names.eraseDups.map fun A => (A, names.count A)

#eval show IO Unit from do
  check ((← load grammarPath).length == 92) "92 rules"
  -- Through BNF, 80 conflicts in 16 rules, among them typedargslist and
  -- varargslist, whose alternatives share long prefixes.
  let g ← loadGrammar grammarPath (some "file_input")
  check (g.conflicts.length == 80) "80 conflicts"
  check ((conflictRules g).length == 16) "16 rules"
  -- Through one DFA per rule, as pgen reads the file, no conflict, with FOLLOW
  -- taken into account, a condition stronger than the one pgen checks.
  let d ← loadGrammar grammarPath (some "file_input") (dfa := true)
  check d.isLL1 "LL(1) through DFAs"
  IO.println "python38 grammar ok"

def tokenClasses (path : System.FilePath) : IO (List String) := do
  let out ← IO.Process.output
    { cmd := "python3", args := #["tests/ll1/python38tok.py", grammarPath, path.toString] }
  unless out.exitCode == 0 do throw (IO.userError s!"{path}: {out.stderr}")
  return (out.stdout.splitOn "\n").filter (· != "")

def pyFiles (dir : System.FilePath) : IO (List System.FilePath) := do
  let fs := (← dir.readDir).map (·.path) |>.filter (·.extension == some "py")
  return (fs.qsort (·.toString < ·.toString)).toList

#eval show IO Unit from do
  let d ← loadGrammar grammarPath (some "file_input") (dfa := true)
  let tb := d.table
  let parses (f : System.FilePath) : IO Bool := do
    return (d.parse tb id (← tokenClasses f)).toOption.isSome
  -- Every module of the standard library parses.
  let fs ← pyFiles "tests/ll1/programs/python38/stdlib"
  let bad ← fs.filterM fun f => return !(← parses f)
  check (fs.length == 14 && bad.isEmpty) s!"modules rejected {bad}"
  -- The walrus operator and positional only parameters, new in 3.8, parse.
  -- Parenthesised context managers (3.9), except* (3.11) and type parameters
  -- (3.12) do not.
  let expect := [("except_star_311", false), ("paren_with_39", false),
    ("posonly_38", true), ("type_params_312", false), ("walrus_38", true)]
  for (name, ok) in expect do
    let r ← parses s!"tests/ll1/programs/python38/snippets/{name}.py"
    check (r == ok) s!"{name} gave {r}"
  IO.println s!"{fs.length} modules and {expect.length} snippets ok"
