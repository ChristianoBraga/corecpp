import CoreCpp.LL1

/-!
# The grammar of Python 3.8

The file `Grammar/Grammar` of CPython at the branch 3.8,
https://raw.githubusercontent.com/python/cpython/3.8/Grammar/Grammar, the input
of the parser generator `pgen`, which reads each rule as a regular expression,
turns it into a DFA, and checks the FIRST sets of the arcs of its initial state
only (`Parser/pgen/pgen.py`, `calcfirst`). The rules below are generated from
that file, one per rule, with the quoted strings as terminals and the token
classes `NAME`, `NUMBER`, `STRING`, `NEWLINE`, `INDENT`, `DEDENT`,
`ENDMARKER`, `ASYNC`, `AWAIT` and `TYPE_COMMENT` as terminals too. Run with
`lake env lean LL1PythonTest.lean`.
-/

open CoreCpp.LL1

private def t (a : String) : Ebnf String := .t a
private def n (A : String) : Ebnf String := .n A
private def seq (es : List (Ebnf String)) : Ebnf String := .seq es
private def alt (es : List (Ebnf String)) : Ebnf String := .alt es
private def star (e : Ebnf String) : Ebnf String := .star e
private def opt (e : Ebnf String) : Ebnf String := .opt e

def py38Rules : List (Rule String) := [
  ⟨"single_input", alt [t "NEWLINE", n "simple_stmt", seq [n "compound_stmt", t "NEWLINE"]]⟩,
  ⟨"file_input", seq [star (alt [t "NEWLINE", n "stmt"]), t "ENDMARKER"]⟩,
  ⟨"eval_input", seq [n "testlist", star (t "NEWLINE"), t "ENDMARKER"]⟩,
  ⟨"decorator", seq [t "@", n "dotted_name", opt (seq [t "(", opt (n "arglist"), t ")"]), t "NEWLINE"]⟩,
  ⟨"decorators", seq [n "decorator", star (n "decorator")]⟩,
  ⟨"decorated", seq [n "decorators", alt [n "classdef", n "funcdef", n "async_funcdef"]]⟩,
  ⟨"async_funcdef", seq [t "ASYNC", n "funcdef"]⟩,
  ⟨"funcdef", seq [t "def", t "NAME", n "parameters", opt (seq [t "->", n "test"]), t ":", opt (t "TYPE_COMMENT"), n "func_body_suite"]⟩,
  ⟨"parameters", seq [t "(", opt (n "typedargslist"), t ")"]⟩,
  ⟨"typedargslist", alt [seq [n "tfpdef", opt (seq [t "=", n "test"]), star (seq [t ",", opt (t "TYPE_COMMENT"), n "tfpdef", opt (seq [t "=", n "test"])]), t ",", opt (t "TYPE_COMMENT"), t "/", opt (seq [t ",", opt (alt [seq [opt (t "TYPE_COMMENT"), n "tfpdef", opt (seq [t "=", n "test"]), star (seq [t ",", opt (t "TYPE_COMMENT"), n "tfpdef", opt (seq [t "=", n "test"])]), alt [t "TYPE_COMMENT", opt (seq [t ",", opt (t "TYPE_COMMENT"), opt (alt [seq [t "*", opt (n "tfpdef"), star (seq [t ",", opt (t "TYPE_COMMENT"), n "tfpdef", opt (seq [t "=", n "test"])]), alt [t "TYPE_COMMENT", opt (seq [t ",", opt (t "TYPE_COMMENT"), opt (seq [t "**", n "tfpdef", opt (t ","), opt (t "TYPE_COMMENT")])])]], seq [t "**", n "tfpdef", opt (t ","), opt (t "TYPE_COMMENT")]])])]], seq [t "*", opt (n "tfpdef"), star (seq [t ",", opt (t "TYPE_COMMENT"), n "tfpdef", opt (seq [t "=", n "test"])]), alt [t "TYPE_COMMENT", opt (seq [t ",", opt (t "TYPE_COMMENT"), opt (seq [t "**", n "tfpdef", opt (t ","), opt (t "TYPE_COMMENT")])])]], seq [t "**", n "tfpdef", opt (t ","), opt (t "TYPE_COMMENT")]])])], alt [seq [n "tfpdef", opt (seq [t "=", n "test"]), star (seq [t ",", opt (t "TYPE_COMMENT"), n "tfpdef", opt (seq [t "=", n "test"])]), alt [t "TYPE_COMMENT", opt (seq [t ",", opt (t "TYPE_COMMENT"), opt (alt [seq [t "*", opt (n "tfpdef"), star (seq [t ",", opt (t "TYPE_COMMENT"), n "tfpdef", opt (seq [t "=", n "test"])]), alt [t "TYPE_COMMENT", opt (seq [t ",", opt (t "TYPE_COMMENT"), opt (seq [t "**", n "tfpdef", opt (t ","), opt (t "TYPE_COMMENT")])])]], seq [t "**", n "tfpdef", opt (t ","), opt (t "TYPE_COMMENT")]])])]], seq [t "*", opt (n "tfpdef"), star (seq [t ",", opt (t "TYPE_COMMENT"), n "tfpdef", opt (seq [t "=", n "test"])]), alt [t "TYPE_COMMENT", opt (seq [t ",", opt (t "TYPE_COMMENT"), opt (seq [t "**", n "tfpdef", opt (t ","), opt (t "TYPE_COMMENT")])])]], seq [t "**", n "tfpdef", opt (t ","), opt (t "TYPE_COMMENT")]]]⟩,
  ⟨"tfpdef", seq [t "NAME", opt (seq [t ":", n "test"])]⟩,
  ⟨"varargslist", alt [seq [n "vfpdef", opt (seq [t "=", n "test"]), star (seq [t ",", n "vfpdef", opt (seq [t "=", n "test"])]), t ",", t "/", opt (seq [t ",", opt (alt [seq [n "vfpdef", opt (seq [t "=", n "test"]), star (seq [t ",", n "vfpdef", opt (seq [t "=", n "test"])]), opt (seq [t ",", opt (alt [seq [t "*", opt (n "vfpdef"), star (seq [t ",", n "vfpdef", opt (seq [t "=", n "test"])]), opt (seq [t ",", opt (seq [t "**", n "vfpdef", opt (t ",")])])], seq [t "**", n "vfpdef", opt (t ",")]])])], seq [t "*", opt (n "vfpdef"), star (seq [t ",", n "vfpdef", opt (seq [t "=", n "test"])]), opt (seq [t ",", opt (seq [t "**", n "vfpdef", opt (t ",")])])], seq [t "**", n "vfpdef", opt (t ",")]])])], alt [seq [n "vfpdef", opt (seq [t "=", n "test"]), star (seq [t ",", n "vfpdef", opt (seq [t "=", n "test"])]), opt (seq [t ",", opt (alt [seq [t "*", opt (n "vfpdef"), star (seq [t ",", n "vfpdef", opt (seq [t "=", n "test"])]), opt (seq [t ",", opt (seq [t "**", n "vfpdef", opt (t ",")])])], seq [t "**", n "vfpdef", opt (t ",")]])])], seq [t "*", opt (n "vfpdef"), star (seq [t ",", n "vfpdef", opt (seq [t "=", n "test"])]), opt (seq [t ",", opt (seq [t "**", n "vfpdef", opt (t ",")])])], seq [t "**", n "vfpdef", opt (t ",")]]]⟩,
  ⟨"vfpdef", t "NAME"⟩,
  ⟨"stmt", alt [n "simple_stmt", n "compound_stmt"]⟩,
  ⟨"simple_stmt", seq [n "small_stmt", star (seq [t ";", n "small_stmt"]), opt (t ";"), t "NEWLINE"]⟩,
  ⟨"small_stmt", alt [n "expr_stmt", n "del_stmt", n "pass_stmt", n "flow_stmt", n "import_stmt", n "global_stmt", n "nonlocal_stmt", n "assert_stmt"]⟩,
  ⟨"expr_stmt", seq [n "testlist_star_expr", alt [n "annassign", seq [n "augassign", alt [n "yield_expr", n "testlist"]], opt (seq [seq [seq [t "=", alt [n "yield_expr", n "testlist_star_expr"]], star (seq [t "=", alt [n "yield_expr", n "testlist_star_expr"]])], opt (t "TYPE_COMMENT")])]]⟩,
  ⟨"annassign", seq [t ":", n "test", opt (seq [t "=", alt [n "yield_expr", n "testlist_star_expr"]])]⟩,
  ⟨"testlist_star_expr", seq [alt [n "test", n "star_expr"], star (seq [t ",", alt [n "test", n "star_expr"]]), opt (t ",")]⟩,
  ⟨"augassign", alt [t "+=", t "-=", t "*=", t "@=", t "/=", t "%=", t "&=", t "|=", t "^=", t "<<=", t ">>=", t "**=", t "//="]⟩,
  ⟨"del_stmt", seq [t "del", n "exprlist"]⟩,
  ⟨"pass_stmt", t "pass"⟩,
  ⟨"flow_stmt", alt [n "break_stmt", n "continue_stmt", n "return_stmt", n "raise_stmt", n "yield_stmt"]⟩,
  ⟨"break_stmt", t "break"⟩,
  ⟨"continue_stmt", t "continue"⟩,
  ⟨"return_stmt", seq [t "return", opt (n "testlist_star_expr")]⟩,
  ⟨"yield_stmt", n "yield_expr"⟩,
  ⟨"raise_stmt", seq [t "raise", opt (seq [n "test", opt (seq [t "from", n "test"])])]⟩,
  ⟨"import_stmt", alt [n "import_name", n "import_from"]⟩,
  ⟨"import_name", seq [t "import", n "dotted_as_names"]⟩,
  ⟨"import_from", seq [t "from", alt [seq [star (alt [t ".", t "..."]), n "dotted_name"], seq [alt [t ".", t "..."], star (alt [t ".", t "..."])]], t "import", alt [t "*", seq [t "(", n "import_as_names", t ")"], n "import_as_names"]]⟩,
  ⟨"import_as_name", seq [t "NAME", opt (seq [t "as", t "NAME"])]⟩,
  ⟨"dotted_as_name", seq [n "dotted_name", opt (seq [t "as", t "NAME"])]⟩,
  ⟨"import_as_names", seq [n "import_as_name", star (seq [t ",", n "import_as_name"]), opt (t ",")]⟩,
  ⟨"dotted_as_names", seq [n "dotted_as_name", star (seq [t ",", n "dotted_as_name"])]⟩,
  ⟨"dotted_name", seq [t "NAME", star (seq [t ".", t "NAME"])]⟩,
  ⟨"global_stmt", seq [t "global", t "NAME", star (seq [t ",", t "NAME"])]⟩,
  ⟨"nonlocal_stmt", seq [t "nonlocal", t "NAME", star (seq [t ",", t "NAME"])]⟩,
  ⟨"assert_stmt", seq [t "assert", n "test", opt (seq [t ",", n "test"])]⟩,
  ⟨"compound_stmt", alt [n "if_stmt", n "while_stmt", n "for_stmt", n "try_stmt", n "with_stmt", n "funcdef", n "classdef", n "decorated", n "async_stmt"]⟩,
  ⟨"async_stmt", seq [t "ASYNC", alt [n "funcdef", n "with_stmt", n "for_stmt"]]⟩,
  ⟨"if_stmt", seq [t "if", n "namedexpr_test", t ":", n "suite", star (seq [t "elif", n "namedexpr_test", t ":", n "suite"]), opt (seq [t "else", t ":", n "suite"])]⟩,
  ⟨"while_stmt", seq [t "while", n "namedexpr_test", t ":", n "suite", opt (seq [t "else", t ":", n "suite"])]⟩,
  ⟨"for_stmt", seq [t "for", n "exprlist", t "in", n "testlist", t ":", opt (t "TYPE_COMMENT"), n "suite", opt (seq [t "else", t ":", n "suite"])]⟩,
  ⟨"try_stmt", seq [t "try", t ":", n "suite", alt [seq [seq [seq [n "except_clause", t ":", n "suite"], star (seq [n "except_clause", t ":", n "suite"])], opt (seq [t "else", t ":", n "suite"]), opt (seq [t "finally", t ":", n "suite"])], seq [t "finally", t ":", n "suite"]]]⟩,
  ⟨"with_stmt", seq [t "with", n "with_item", star (seq [t ",", n "with_item"]), t ":", opt (t "TYPE_COMMENT"), n "suite"]⟩,
  ⟨"with_item", seq [n "test", opt (seq [t "as", n "expr"])]⟩,
  ⟨"except_clause", seq [t "except", opt (seq [n "test", opt (seq [t "as", t "NAME"])])]⟩,
  ⟨"suite", alt [n "simple_stmt", seq [t "NEWLINE", t "INDENT", seq [n "stmt", star (n "stmt")], t "DEDENT"]]⟩,
  ⟨"namedexpr_test", seq [n "test", opt (seq [t ":=", n "test"])]⟩,
  ⟨"test", alt [seq [n "or_test", opt (seq [t "if", n "or_test", t "else", n "test"])], n "lambdef"]⟩,
  ⟨"test_nocond", alt [n "or_test", n "lambdef_nocond"]⟩,
  ⟨"lambdef", seq [t "lambda", opt (n "varargslist"), t ":", n "test"]⟩,
  ⟨"lambdef_nocond", seq [t "lambda", opt (n "varargslist"), t ":", n "test_nocond"]⟩,
  ⟨"or_test", seq [n "and_test", star (seq [t "or", n "and_test"])]⟩,
  ⟨"and_test", seq [n "not_test", star (seq [t "and", n "not_test"])]⟩,
  ⟨"not_test", alt [seq [t "not", n "not_test"], n "comparison"]⟩,
  ⟨"comparison", seq [n "expr", star (seq [n "comp_op", n "expr"])]⟩,
  ⟨"comp_op", alt [t "<", t ">", t "==", t ">=", t "<=", t "<>", t "!=", t "in", seq [t "not", t "in"], t "is", seq [t "is", t "not"]]⟩,
  ⟨"star_expr", seq [t "*", n "expr"]⟩,
  ⟨"expr", seq [n "xor_expr", star (seq [t "|", n "xor_expr"])]⟩,
  ⟨"xor_expr", seq [n "and_expr", star (seq [t "^", n "and_expr"])]⟩,
  ⟨"and_expr", seq [n "shift_expr", star (seq [t "&", n "shift_expr"])]⟩,
  ⟨"shift_expr", seq [n "arith_expr", star (seq [alt [t "<<", t ">>"], n "arith_expr"])]⟩,
  ⟨"arith_expr", seq [n "term", star (seq [alt [t "+", t "-"], n "term"])]⟩,
  ⟨"term", seq [n "factor", star (seq [alt [t "*", t "@", t "/", t "%", t "//"], n "factor"])]⟩,
  ⟨"factor", alt [seq [alt [t "+", t "-", t "~"], n "factor"], n "power"]⟩,
  ⟨"power", seq [n "atom_expr", opt (seq [t "**", n "factor"])]⟩,
  ⟨"atom_expr", seq [opt (t "AWAIT"), n "atom", star (n "trailer")]⟩,
  ⟨"atom", alt [seq [t "(", opt (alt [n "yield_expr", n "testlist_comp"]), t ")"], seq [t "[", opt (n "testlist_comp"), t "]"], seq [t "{", opt (n "dictorsetmaker"), t "}"], t "NAME", t "NUMBER", seq [t "STRING", star (t "STRING")], t "...", t "None", t "True", t "False"]⟩,
  ⟨"testlist_comp", seq [alt [n "namedexpr_test", n "star_expr"], alt [n "comp_for", seq [star (seq [t ",", alt [n "namedexpr_test", n "star_expr"]]), opt (t ",")]]]⟩,
  ⟨"trailer", alt [seq [t "(", opt (n "arglist"), t ")"], seq [t "[", n "subscriptlist", t "]"], seq [t ".", t "NAME"]]⟩,
  ⟨"subscriptlist", seq [n "subscript", star (seq [t ",", n "subscript"]), opt (t ",")]⟩,
  ⟨"subscript", alt [n "test", seq [opt (n "test"), t ":", opt (n "test"), opt (n "sliceop")]]⟩,
  ⟨"sliceop", seq [t ":", opt (n "test")]⟩,
  ⟨"exprlist", seq [alt [n "expr", n "star_expr"], star (seq [t ",", alt [n "expr", n "star_expr"]]), opt (t ",")]⟩,
  ⟨"testlist", seq [n "test", star (seq [t ",", n "test"]), opt (t ",")]⟩,
  ⟨"dictorsetmaker", alt [seq [alt [seq [n "test", t ":", n "test"], seq [t "**", n "expr"]], alt [n "comp_for", seq [star (seq [t ",", alt [seq [n "test", t ":", n "test"], seq [t "**", n "expr"]]]), opt (t ",")]]], seq [alt [n "test", n "star_expr"], alt [n "comp_for", seq [star (seq [t ",", alt [n "test", n "star_expr"]]), opt (t ",")]]]]⟩,
  ⟨"classdef", seq [t "class", t "NAME", opt (seq [t "(", opt (n "arglist"), t ")"]), t ":", n "suite"]⟩,
  ⟨"arglist", seq [n "argument", star (seq [t ",", n "argument"]), opt (t ",")]⟩,
  ⟨"argument", alt [seq [n "test", opt (n "comp_for")], seq [n "test", t ":=", n "test"], seq [n "test", t "=", n "test"], seq [t "**", n "test"], seq [t "*", n "test"]]⟩,
  ⟨"comp_iter", alt [n "comp_for", n "comp_if"]⟩,
  ⟨"sync_comp_for", seq [t "for", n "exprlist", t "in", n "or_test", opt (n "comp_iter")]⟩,
  ⟨"comp_for", seq [opt (t "ASYNC"), n "sync_comp_for"]⟩,
  ⟨"comp_if", seq [t "if", n "test_nocond", opt (n "comp_iter")]⟩,
  ⟨"encoding_decl", t "NAME"⟩,
  ⟨"yield_expr", seq [t "yield", opt (n "yield_arg")]⟩,
  ⟨"yield_arg", alt [seq [t "from", n "test"], n "testlist_star_expr"]⟩,
  ⟨"func_body_suite", alt [n "simple_stmt", seq [t "NEWLINE", opt (seq [t "TYPE_COMMENT", t "NEWLINE"]), t "INDENT", seq [n "stmt", star (n "stmt")], t "DEDENT"]]⟩,
  ⟨"func_type_input", seq [n "func_type", star (t "NEWLINE"), t "ENDMARKER"]⟩,
  ⟨"func_type", seq [t "(", opt (n "typelist"), t ")", t "->", n "test"]⟩,
  ⟨"typelist", alt [seq [n "test", star (seq [t ",", n "test"]), opt (seq [t ",", opt (alt [seq [t "*", opt (n "test"), star (seq [t ",", n "test"]), opt (seq [t ",", t "**", n "test"])], seq [t "**", n "test"]])])], seq [t "*", opt (n "test"), star (seq [t ",", n "test"]), opt (seq [t ",", t "**", n "test"])], seq [t "**", n "test"]]⟩
]

def py38 : Grammar String := translate "file_input" py38Rules
def py38Dfa : Grammar String := translateDfa "file_input" py38Rules

def conflictRules (g : Grammar String) : List (String × Nat) :=
  let names := g.conflicts.map fun ((A, _), _) => ((A.splitOn ".").head!.splitOn "#").head!
  names.eraseDups.map fun A => (A, names.count A)

#guard py38Rules.length == 92

-- Through BNF, 80 conflicts in 16 rules, among them `typedargslist` and
-- `varargslist`, whose alternatives share long prefixes.
#guard py38.conflicts.length == 80
#guard (conflictRules py38).length == 16

-- Through one DFA per rule, as `pgen` reads the file, no conflict, with FOLLOW
-- taken into account, a condition stronger than the one `pgen` checks.
#guard py38Dfa.isLL1

/-! ## Programs

`tests/python38/tokens/` holds the token classes of fourteen modules of the
standard library of CPython 3.8, 7950 lines, from
https://raw.githubusercontent.com/python/cpython/3.8/Lib/, written by
`tests/python38/tokclass.py`. `tests/python38/snippets/` holds five short
programs, two with syntax new in 3.8 and three with syntax of later versions,
with their token classes. -/

def py38Table : Table String := py38Dfa.table

def parseTokens (path : System.FilePath) : IO Bool := do
  let toks := ((← IO.FS.readFile path).splitOn "\n").filter (· != "")
  return (py38Dfa.parse py38Table id toks).toOption.isSome

def tokenFiles (dir : System.FilePath) : IO (List System.FilePath) := do
  let fs := (← dir.readDir).map (·.path) |>.filter (·.extension == some "tok")
  return (fs.qsort (·.toString < ·.toString)).toList

-- Every module of the standard library is accepted.
#eval show IO Unit from do
  let fs ← tokenFiles "tests/python38/tokens"
  let bad ← fs.filterM fun f => return !(← parseTokens f)
  if fs.length != 14 || !bad.isEmpty then throw (IO.userError s!"rejected {bad}")
  IO.println s!"{fs.length} modules accepted"

-- The walrus operator and positional only parameters, new in 3.8, are
-- accepted. Parenthesised context managers (3.9), `except*` (3.11) and type
-- parameters (3.12) are rejected.
#eval show IO Unit from do
  let expect := [("except_star_311", false), ("paren_with_39", false),
    ("posonly_38", true), ("type_params_312", false), ("walrus_38", true)]
  for (name, ok) in expect do
    let r ← parseTokens s!"tests/python38/snippets/{name}.tok"
    if r != ok then throw (IO.userError s!"{name} gave {r}")
  IO.println "snippets as expected"
