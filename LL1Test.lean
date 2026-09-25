import CoreCpp.LL1

/-!
# Tests of the LL(1) construction on published grammars

Each grammar comes from a public source, with the sets, table, derivation or
conflict the source gives. Production numbers of the sources start at 1, and
indices here start at 0. `ε` is not a member of the sets computed here, whose
nullable nonterminals are listed apart. Run with `lake env lean LL1Test.lean`.

* Wikipedia, LL parser, https://en.wikipedia.org/wiki/LL_parser
* Hovemeyer, Lecture 9, LL(1) parsing, Johns Hopkins 601.428/628, 2022,
  https://jhucompilers.github.io/fall2022/lectures/lecture09-public.pdf
-/

open CoreCpp.LL1

/-- A grammar in BNF over string terminals. A name is a nonterminal when it is
the left side of some production. -/
def bnf (start : String) (ps : List (String × List String)) : Grammar String :=
  let nts := ps.map (·.1)
  ⟨start, ps.map fun (A, rhs) => ⟨A, rhs.map fun x => if nts.contains x then .n x else .t x⟩⟩

def setEq [BEq α] (xs ys : List α) : Bool := xs.all ys.contains && ys.all xs.contains

def tokens (s : String) : List String := (s.splitOn " ").filter (· != "")

def run (g : Grammar String) (s : String) : Except String (List Nat) :=
  g.parse g.table id (tokens s)

/-! ## Wikipedia, the grammar of the section "Concrete example" -/

def wiki : Grammar String := bnf "S" [("S", ["F"]), ("S", ["(", "S", "+", "F", ")"]), ("F", ["a"])]

-- The table of the article, `S` with `(` gives 2, `S` with `a` gives 1, `F` with `a` gives 3.
#guard setEq wiki.table [(("S", some "("), [1]), (("S", some "a"), [0]), (("F", some "a"), [2])]
#guard wiki.isLL1
-- The input `( a + a )` has the rule sequence [2, 1, 3, 3] of the article.
#guard (run wiki "( a + a )").toOption == some [1, 0, 2, 2]
#guard (run wiki "( a + )").toOption.isNone
#guard (run wiki "a a").toOption.isNone

/-! ## Wikipedia, the two grammars the article gives as not LL(1) -/

def wikiConflict1 : Grammar String := bnf "S" [("S", ["A", "a", "b"]), ("A", ["a"]), ("A", [])]

-- FIRST(A) is {a, ε} and FOLLOW(A) is {a}, so `A` with `a` selects both productions.
#guard setEq (wikiConflict1.first.get "A") ["a"]
#guard wikiConflict1.nullable.contains "A"
#guard setEq (wikiConflict1.follow.get "A") [some "a"]
#guard !wikiConflict1.isLL1
#guard wikiConflict1.conflicts.map (·.1) == [("A", some "a")]

def wikiConflict2 : Grammar String := bnf "S" [
  ("S", ["A"]), ("S", ["B"]),
  ("A", ["a", "A", "b"]), ("A", []),
  ("B", ["a", "B", "b", "b"]), ("B", [])]

#guard !wikiConflict2.isLL1
#guard setEq (wikiConflict2.conflicts.map (·.1)) [("S", some "a"), ("S", none)]

/-! ## Hovemeyer, the FIRST example -/

def jhuFirst : Grammar String := bnf "A" [
  ("A", ["a"]), ("A", ["B"]), ("A", ["C"]),
  ("B", ["b"]), ("B", []),
  ("C", ["c", "e"]), ("C", ["d", "e"])]

-- FIRST(A) = {a, b, c, d, ε}.
#guard setEq (jhuFirst.first.get "A") ["a", "b", "c", "d"]
#guard jhuFirst.nullable.contains "A"

/-! ## Hovemeyer, the FOLLOW example -/

def jhuFollow : Grammar String := bnf "A" [
  ("A", ["a", "B", "c"]), ("A", ["C"]),
  ("C", ["d", "B", "G", "f"]),
  ("B", ["g"]),
  ("G", ["h"]), ("G", [])]

-- FOLLOW(A) = {eof} and FOLLOW(B) = {c, f, h}.
#guard setEq (jhuFollow.follow.get "A") [none]
#guard setEq (jhuFollow.follow.get "B") [some "c", some "f", some "h"]

/-! ## Hovemeyer, the expression grammar, its sets and its table -/

def jhuExpr : Grammar String := bnf "E" [
  ("E", ["T", "E'"]),
  ("E'", ["+", "T", "E'"]), ("E'", ["-", "T", "E'"]), ("E'", []),
  ("T", ["F", "T'"]),
  ("T'", ["*", "F", "T'"]), ("T'", ["/", "F", "T'"]), ("T'", []),
  ("F", ["i"]), ("F", ["n"])]

#guard setEq (jhuExpr.first.get "E") ["i", "n"]
#guard setEq (jhuExpr.first.get "E'") ["+", "-"]
#guard setEq (jhuExpr.first.get "T") ["i", "n"]
#guard setEq (jhuExpr.first.get "T'") ["*", "/"]
#guard setEq (jhuExpr.first.get "F") ["i", "n"]
#guard setEq jhuExpr.nullable ["E'", "T'"]
#guard setEq (jhuExpr.follow.get "E") [none]
#guard setEq (jhuExpr.follow.get "E'") [none]
#guard setEq (jhuExpr.follow.get "T") [some "+", some "-", none]
#guard setEq (jhuExpr.follow.get "T'") [some "+", some "-", none]
#guard setEq (jhuExpr.follow.get "F") [some "*", some "/", some "+", some "-", none]

-- The table of the lecture, row by row.
#guard setEq jhuExpr.table [
  (("E", some "i"), [0]), (("E", some "n"), [0]),
  (("E'", some "+"), [1]), (("E'", some "-"), [2]), (("E'", none), [3]),
  (("T", some "i"), [4]), (("T", some "n"), [4]),
  (("T'", some "+"), [7]), (("T'", some "-"), [7]), (("T'", some "*"), [5]),
  (("T'", some "/"), [6]), (("T'", none), [7]),
  (("F", some "i"), [8]), (("F", some "n"), [9])]
#guard jhuExpr.isLL1

-- The leftmost derivation of `i + n * i`.
#guard (run jhuExpr "i + n * i").toOption == some [0, 4, 8, 7, 1, 4, 9, 5, 8, 7, 3]
#guard (run jhuExpr "i + * n").toOption.isNone
#guard (run jhuExpr "").toOption.isNone
#guard (jhuExpr.tree (tokens "i - n") [0, 4, 8, 7, 2, 4, 9, 7, 3]).isSome

/-! # Grammars of real programming languages

The published EBNF of three languages of Wirth, transcribed with the
translation of `LL1.lean`, over the token classes `ident` and `number`.

* PL/0, Wikipedia, https://en.wikipedia.org/wiki/PL/0, section Grammar, and
  the three programs of section Examples.
* Oberon-0, Wirth, Compiler Construction, revised edition of May 2017,
  chapter 6, p. 30, and the module `Samples` of the same page,
  https://people.inf.ethz.ch/wirth/CompilerConstruction/CompilerConstruction1.pdf
* Oberon-07, Wirth, The Programming Language Oberon, revision 3.5.2016,
  Appendix, https://people.inf.ethz.ch/wirth/Oberon/Oberon07.Report.pdf
-/

section Real

private def t (a : String) : Ebnf String := .t a
private def n (A : String) : Ebnf String := .n A
private def seq (es : List (Ebnf String)) : Ebnf String := .seq es
private def alt (es : List (Ebnf String)) : Ebnf String := .alt es
private def star (e : Ebnf String) : Ebnf String := .star e
private def opt (e : Ebnf String) : Ebnf String := .opt e
private def ts (as : List String) : Ebnf String := alt (as.map t)

/-- A scanner for the tests. Letters start an identifier, digits a number,
symbols are tried in the order given, longest first, and a word among the
keywords is the keyword. With `fold` the keywords are case insensitive. -/
def scan (keywords : List String) (fold : Bool) (syms : List String) (src : String) :
    Except String (List String) :=
  let norm (w : String) := if fold then w.toLower else w
  let rec go : Nat → List Char → List String → Except String (List String)
    | 0, _, acc => .ok acc.reverse
    | _ + 1, [], acc => .ok acc.reverse
    | f + 1, c :: cs, acc =>
      if c.isWhitespace then go f cs acc
      else if c.isAlpha then
        let w := String.ofList (c :: cs.takeWhile Char.isAlphanum)
        let rest := cs.dropWhile Char.isAlphanum
        match keywords.find? (norm · == norm w) with
        | some k => go f rest (k :: acc)
        | none => go f rest ("ident" :: acc)
      else if c.isDigit then go f (cs.dropWhile Char.isDigit) ("number" :: acc)
      else
        match syms.find? (fun s => (c :: cs).take s.length == s.toList) with
        | some s => go f ((c :: cs).drop s.length) (s :: acc)
        | none => .error s!"unexpected character {c}"
  go (src.length + 1) src.toList []

def accepts (g : Grammar String) (toks : Except String (List String)) : Bool :=
  match toks with
  | .ok ts => (g.parse g.table id ts).toOption.isSome
  | .error _ => false

/-! ## PL/0 -/

def pl0Rules : List (Rule String) := [
  ⟨"program", seq [n "block", t "."]⟩,
  ⟨"block", seq [
    opt (seq [t "const", t "ident", t "=", t "number",
      star (seq [t ",", t "ident", t "=", t "number"]), t ";"]),
    opt (seq [t "var", t "ident", star (seq [t ",", t "ident"]), t ";"]),
    star (seq [t "procedure", t "ident", t ";", n "block", t ";"]),
    n "statement"]⟩,
  ⟨"statement", opt (alt [
    seq [t "ident", t ":=", n "expression"],
    seq [t "call", t "ident"],
    seq [t "?", t "ident"],
    seq [t "!", n "expression"],
    seq [t "begin", n "statement", star (seq [t ";", n "statement"]), t "end"],
    seq [t "if", n "condition", t "then", n "statement"],
    seq [t "while", n "condition", t "do", n "statement"]])⟩,
  ⟨"condition", alt [
    seq [t "odd", n "expression"],
    seq [n "expression", ts ["=", "#", "<", "<=", ">", ">="], n "expression"]]⟩,
  ⟨"expression", seq [opt (ts ["+", "-"]), n "term", star (seq [ts ["+", "-"], n "term"])]⟩,
  ⟨"term", seq [n "factor", star (seq [ts ["*", "/"], n "factor"])]⟩,
  ⟨"factor", alt [t "ident", t "number", seq [t "(", n "expression", t ")"]]⟩]

def pl0 : Grammar String := translate "program" pl0Rules

def pl0Scan := scan ["const", "var", "procedure", "call", "begin", "end", "if", "then",
  "while", "do", "odd"] true [":=", "<=", ">=", ".", ",", ";", "=", "#", "<", ">", "+", "-",
  "*", "/", "(", ")", "?", "!"]

def pl0Squares := "VAR x, squ;

PROCEDURE square;
BEGIN
   squ:= x * x
END;

BEGIN
   x := 1;
   WHILE x <= 10 DO
   BEGIN
      CALL square;
      ! squ;
      x := x + 1
   END
END."

def pl0Primes := "const max = 100;
var arg, ret;

procedure isprime;
var i;
begin
	ret := 1;
	i := 2;
	while i < arg do
	begin
		if arg / i * i = arg then
		begin
			ret := 0;
			i := arg
		end;
		i := i + 1
	end
end;

procedure primes;
begin
	arg := 2;
	while arg < max do
	begin
		call isprime;
		if ret = 1 then write arg;
		arg := arg + 1
	end
end;

call primes
."

def pl0Compilerbau := "VAR x, y, z, q, r, n, f;

PROCEDURE multiply;
VAR a, b;
BEGIN
  a := x;
  b := y;
  z := 0;
  WHILE b > 0 DO
  BEGIN
    IF ODD b THEN z := z + a;
    a := 2 * a;
    b := b / 2
  END
END;

PROCEDURE divide;
VAR w;
BEGIN
  r := x;
  q := 0;
  w := y;
  WHILE w <= r DO w := 2 * w;
  WHILE w > y DO
  BEGIN
    q := 2 * q;
    w := w / 2;
    IF w <= r THEN
    BEGIN
      r := r - w;
      q := q + 1
    END
  END
END;

PROCEDURE gcd;
VAR f, g;
BEGIN
  f := x;
  g := y;
  WHILE f # g DO
  BEGIN
    IF f < g THEN g := g - f;
    IF g < f THEN f := f - g
  END;
  z := f
END;

PROCEDURE fact;
BEGIN
  IF n > 1 THEN
  BEGIN
    f := n * f;
    n := n - 1;
    CALL fact
  END
END;

BEGIN
  ?x; ?y; CALL multiply; !z;
  ?x; ?y; CALL divide; !q; !r;
  ?x; ?y; CALL gcd; !z;
  ?n; f := 1; CALL fact; !f
END."

#guard pl0.isLL1
#guard accepts pl0 (pl0Scan pl0Squares)
#guard accepts pl0 (pl0Scan pl0Compilerbau)
-- The primes program writes `write arg`, which the grammar lacks. The article
-- says that `write` corresponds to `!`.
#guard !accepts pl0 (pl0Scan pl0Primes)
#guard accepts pl0 (pl0Scan (pl0Primes.replace "write arg" "! arg"))
#guard !accepts pl0 (pl0Scan "begin x := end.")

/-! ## Oberon-0 -/

def oberon0Rules (factored : Bool) : List (Rule String) := [
  ⟨"selector", star (alt [seq [t ".", t "ident"], seq [t "[", n "expression", t "]"]])⟩,
  ⟨"factor", alt [seq [t "ident", n "selector"], t "number",
    seq [t "(", n "expression", t ")"], seq [t "~", n "factor"]]⟩,
  ⟨"term", seq [n "factor", star (seq [ts ["*", "DIV", "MOD", "&"], n "factor"])]⟩,
  ⟨"SimpleExpression", seq [opt (ts ["+", "-"]), n "term",
    star (seq [ts ["+", "-", "OR"], n "term"])]⟩,
  ⟨"expression", seq [n "SimpleExpression",
    opt (seq [ts ["=", "#", "<", "<=", ">", ">="], n "SimpleExpression"])]⟩,
  ⟨"assignment", seq [t "ident", n "selector", t ":=", n "expression"]⟩,
  ⟨"ActualParameters", seq [t "(", opt (seq [n "expression",
    star (seq [t ",", n "expression"])]), t ")"]⟩,
  ⟨"ProcedureCall", seq [t "ident", n "selector", opt (n "ActualParameters")]⟩,
  ⟨"IfStatement", seq [t "IF", n "expression", t "THEN", n "StatementSequence",
    star (seq [t "ELSIF", n "expression", t "THEN", n "StatementSequence"]),
    opt (seq [t "ELSE", n "StatementSequence"]), t "END"]⟩,
  ⟨"WhileStatement", seq [t "WHILE", n "expression", t "DO", n "StatementSequence", t "END"]⟩,
  ⟨"RepeatStatement", seq [t "REPEAT", n "StatementSequence", t "UNTIL", n "expression"]⟩,
  ⟨"statement", opt (alt (
    (if factored then
      [seq [t "ident", n "selector",
        alt [seq [t ":=", n "expression"], opt (n "ActualParameters")]]]
    else [n "assignment", n "ProcedureCall"]) ++
    [n "IfStatement", n "WhileStatement"]))⟩,
  ⟨"StatementSequence", seq [n "statement", star (seq [t ";", n "statement"])]⟩,
  ⟨"IdentList", seq [t "ident", star (seq [t ",", t "ident"])]⟩,
  ⟨"ArrayType", seq [t "ARRAY", n "expression", t "OF", n "type"]⟩,
  ⟨"FieldList", opt (seq [n "IdentList", t ":", n "type"])⟩,
  ⟨"RecordType", seq [t "RECORD", n "FieldList", star (seq [t ";", n "FieldList"]), t "END"]⟩,
  ⟨"type", alt [t "ident", n "ArrayType", n "RecordType"]⟩,
  ⟨"FPSection", seq [opt (t "VAR"), n "IdentList", t ":", n "type"]⟩,
  ⟨"FormalParameters", seq [t "(", opt (seq [n "FPSection",
    star (seq [t ";", n "FPSection"])]), t ")"]⟩,
  ⟨"ProcedureHeading", seq [t "PROCEDURE", t "ident", opt (n "FormalParameters")]⟩,
  ⟨"ProcedureBody", seq [n "declarations",
    opt (seq [t "BEGIN", n "StatementSequence"]), t "END", t "ident"]⟩,
  ⟨"ProcedureDeclaration", seq [n "ProcedureHeading", t ";", n "ProcedureBody"]⟩,
  ⟨"declarations", seq [
    opt (seq [t "CONST", star (seq [t "ident", t "=", n "expression", t ";"])]),
    opt (seq [t "TYPE", star (seq [t "ident", t "=", n "type", t ";"])]),
    opt (seq [t "VAR", star (seq [n "IdentList", t ":", n "type", t ";"])]),
    star (seq [n "ProcedureDeclaration", t ";"])]⟩,
  ⟨"module", seq [t "MODULE", t "ident", t ";", n "declarations",
    opt (seq [t "BEGIN", n "StatementSequence"]), t "END", t "ident", t "."]⟩]

def oberon0 : Grammar String := translate "module" (oberon0Rules false)
def oberon0Factored : Grammar String := translate "module" (oberon0Rules true)

def oberonScan := scan ["DIV", "MOD", "OR", "OF", "THEN", "DO", "UNTIL", "END", "ELSE",
  "ELSIF", "IF", "WHILE", "REPEAT", "ARRAY", "RECORD", "CONST", "TYPE", "VAR", "PROCEDURE",
  "BEGIN", "MODULE"] false [":=", "<=", ">=", "*", "&", "+", "-", "=", "#", "<", ">", ".",
  ",", ":", ")", "]", "(", "[", "~", ";"]

def oberon0Samples := "MODULE Samples;
      PROCEDURE Multiply*;
         VAR x, y, z: INTEGER;
      BEGIN OpenInput; ReadInt(x); ReadInt(y); z := 0;
         WHILE x > 0 DO
             IF x MOD 2 = 1 THEN z := z + y END ;
             y := 2*y; x := x DIV 2
         END ;
         WriteInt(x, 4); WriteInt(y, 4); WriteInt(z, 6); WriteLn
      END Multiply;
      PROCEDURE Divide*;
         VAR x, y, r, q, w: INTEGER;
      BEGIN OpenInput; ReadInt(x); ReadInt(y); r := x; q := 0; w := y;
         WHILE w <= r DO w := 2*w END ;
         WHILE w > y DO
              q := 2*q; w := w DIV 2;
              IF w <= r THEN r := r - w; q := q + 1 END
         END ;
         WriteInt(x.4); WriteInt(y, 4); WriteInt(q, 4); WriteInt(r, 4); WriteLn
      END Divide;
      PROCEDURE Sum*;
         VAR n, s: INTEGER;
      BEGIN OpenInput; s:= 0;
         WHILE ~eot() DO ReadInt(n); WriteInt(n, 4); s := s + n END ;
         WriteInt(s, 6); WriteLn
      END Sum;

   END Samples."

-- As published, `assignment` and `ProcedureCall` both start with `ident`, the
-- only conflict of the grammar.
#guard !oberon0.isLL1
/-- The conflicts, each named by its rule and lookahead, without the index of
the auxiliary nonterminal. -/
def conflictsAt (g : Grammar String) : List (String × Look String) :=
  g.conflicts.map fun ((A, a), _) => ((A.splitOn ".").head!, a)

#guard conflictsAt oberon0 == [("statement", some "ident")]
-- Factored as `ident selector ( ":=" expression | [ActualParameters] )`, the
-- grammar is LL(1).
#guard oberon0Factored.isLL1
-- The module of the book uses three forms outside the syntax of the same
-- page, the export mark `*`, the function call `eot()` in a factor and the
-- typing slip `x.4`. Without them the module is accepted.
#guard !accepts oberon0Factored (oberonScan oberon0Samples)
#guard accepts oberon0Factored (oberonScan (((oberon0Samples.replace "*;" ";").replace
  "eot()" "eot").replace "x.4" "x, 4"))

/-! ## Oberon-07 -/

def oberon07Rules : List (Rule String) := [
  ⟨"qualident", seq [opt (seq [t "ident", t "."]), t "ident"]⟩,
  ⟨"identdef", seq [t "ident", opt (t "*")]⟩,
  ⟨"ConstDeclaration", seq [n "identdef", t "=", n "ConstExpression"]⟩,
  ⟨"ConstExpression", n "expression"⟩,
  ⟨"TypeDeclaration", seq [n "identdef", t "=", n "type"]⟩,
  ⟨"type", alt [n "qualident", n "ArrayType", n "RecordType", n "PointerType",
    n "ProcedureType"]⟩,
  ⟨"ArrayType", seq [t "ARRAY", n "length", star (seq [t ",", n "length"]), t "OF", n "type"]⟩,
  ⟨"length", n "ConstExpression"⟩,
  ⟨"RecordType", seq [t "RECORD", opt (seq [t "(", n "BaseType", t ")"]),
    opt (n "FieldListSequence"), t "END"]⟩,
  ⟨"BaseType", n "qualident"⟩,
  ⟨"FieldListSequence", seq [n "FieldList", star (seq [t ";", n "FieldList"])]⟩,
  ⟨"FieldList", seq [n "IdentList", t ":", n "type"]⟩,
  ⟨"IdentList", seq [n "identdef", star (seq [t ",", n "identdef"])]⟩,
  ⟨"PointerType", seq [t "POINTER", t "TO", n "type"]⟩,
  ⟨"ProcedureType", seq [t "PROCEDURE", opt (n "FormalParameters")]⟩,
  ⟨"VariableDeclaration", seq [n "IdentList", t ":", n "type"]⟩,
  ⟨"expression", seq [n "SimpleExpression", opt (seq [n "relation", n "SimpleExpression"])]⟩,
  ⟨"relation", ts ["=", "#", "<", "<=", ">", ">=", "IN", "IS"]⟩,
  ⟨"SimpleExpression", seq [opt (ts ["+", "-"]), n "term",
    star (seq [n "AddOperator", n "term"])]⟩,
  ⟨"AddOperator", ts ["+", "-", "OR"]⟩,
  ⟨"term", seq [n "factor", star (seq [n "MulOperator", n "factor"])]⟩,
  ⟨"MulOperator", ts ["*", "/", "DIV", "MOD", "&"]⟩,
  ⟨"factor", alt [t "number", t "string", t "NIL", t "TRUE", t "FALSE", n "set",
    seq [n "designator", opt (n "ActualParameters")],
    seq [t "(", n "expression", t ")"], seq [t "~", n "factor"]]⟩,
  ⟨"designator", seq [n "qualident", star (n "selector")]⟩,
  ⟨"selector", alt [seq [t ".", t "ident"], seq [t "[", n "ExpList", t "]"], t "^",
    seq [t "(", n "qualident", t ")"]]⟩,
  ⟨"set", seq [t "{", opt (seq [n "element", star (seq [t ",", n "element"])]), t "}"]⟩,
  ⟨"element", seq [n "expression", opt (seq [t "..", n "expression"])]⟩,
  ⟨"ExpList", seq [n "expression", star (seq [t ",", n "expression"])]⟩,
  ⟨"ActualParameters", seq [t "(", opt (n "ExpList"), t ")"]⟩,
  ⟨"statement", opt (alt [n "assignment", n "ProcedureCall", n "IfStatement",
    n "CaseStatement", n "WhileStatement", n "RepeatStatement", n "ForStatement"])⟩,
  ⟨"assignment", seq [n "designator", t ":=", n "expression"]⟩,
  ⟨"ProcedureCall", seq [n "designator", opt (n "ActualParameters")]⟩,
  ⟨"StatementSequence", seq [n "statement", star (seq [t ";", n "statement"])]⟩,
  ⟨"IfStatement", seq [t "IF", n "expression", t "THEN", n "StatementSequence",
    star (seq [t "ELSIF", n "expression", t "THEN", n "StatementSequence"]),
    opt (seq [t "ELSE", n "StatementSequence"]), t "END"]⟩,
  ⟨"CaseStatement", seq [t "CASE", n "expression", t "OF", n "case",
    star (seq [t "|", n "case"]), t "END"]⟩,
  ⟨"case", opt (seq [n "CaseLabelList", t ":", n "StatementSequence"])⟩,
  ⟨"CaseLabelList", seq [n "LabelRange", star (seq [t ",", n "LabelRange"])]⟩,
  ⟨"LabelRange", seq [n "label", opt (seq [t "..", n "label"])]⟩,
  ⟨"label", alt [t "number", t "string", n "qualident"]⟩,
  ⟨"WhileStatement", seq [t "WHILE", n "expression", t "DO", n "StatementSequence",
    star (seq [t "ELSIF", n "expression", t "DO", n "StatementSequence"]), t "END"]⟩,
  ⟨"RepeatStatement", seq [t "REPEAT", n "StatementSequence", t "UNTIL", n "expression"]⟩,
  ⟨"ForStatement", seq [t "FOR", t "ident", t ":=", n "expression", t "TO", n "expression",
    opt (seq [t "BY", n "ConstExpression"]), t "DO", n "StatementSequence", t "END"]⟩,
  ⟨"ProcedureDeclaration", seq [n "ProcedureHeading", t ";", n "ProcedureBody", t "ident"]⟩,
  ⟨"ProcedureHeading", seq [t "PROCEDURE", n "identdef", opt (n "FormalParameters")]⟩,
  ⟨"ProcedureBody", seq [n "DeclarationSequence",
    opt (seq [t "BEGIN", n "StatementSequence"]),
    opt (seq [t "RETURN", n "expression"]), t "END"]⟩,
  ⟨"DeclarationSequence", seq [
    opt (seq [t "CONST", star (seq [n "ConstDeclaration", t ";"])]),
    opt (seq [t "TYPE", star (seq [n "TypeDeclaration", t ";"])]),
    opt (seq [t "VAR", star (seq [n "VariableDeclaration", t ";"])]),
    star (seq [n "ProcedureDeclaration", t ";"])]⟩,
  ⟨"FormalParameters", seq [t "(", opt (seq [n "FPSection",
    star (seq [t ";", n "FPSection"])]), t ")", opt (seq [t ":", n "qualident"])]⟩,
  ⟨"FPSection", seq [opt (t "VAR"), t "ident", star (seq [t ",", t "ident"]), t ":",
    n "FormalType"]⟩,
  ⟨"FormalType", seq [star (seq [t "ARRAY", t "OF"]), n "qualident"]⟩,
  ⟨"module", seq [t "MODULE", t "ident", t ";", opt (n "ImportList"),
    n "DeclarationSequence", opt (seq [t "BEGIN", n "StatementSequence"]),
    t "END", t "ident", t "."]⟩,
  ⟨"ImportList", seq [t "IMPORT", n "import", star (seq [t ",", n "import"]), t ";"]⟩,
  ⟨"import", seq [t "ident", opt (seq [t ":=", t "ident"])]⟩]

def oberon07 : Grammar String := translate "module" oberon07Rules

-- Three conflicts. In `statement`, `assignment` and `ProcedureCall` both start
-- with a designator. In `qualident`, `[ident "."] ident` cannot tell a module
-- prefix from the identifier itself on `ident`. In `designator`, the selector
-- `"(" qualident ")"` of a type guard and `ActualParameters` both start with `(`.
#guard !oberon07.isLL1
#guard setEq (conflictsAt oberon07)
  [("statement", some "ident"), ("designator", some "("), ("qualident", some "ident")]

end Real
