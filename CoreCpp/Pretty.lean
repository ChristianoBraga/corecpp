import CoreCpp.Syntax
import CoreCpp.Semantics

/-!
# Pretty printing of Core C++ syntax and semantic domains

Concrete syntax for expressions and commands, with the minimum of parentheses
that the grammar's precedence levels require, and the notation of the design
document for locations, values, environments, stores and control results.
-/

namespace CoreCpp

def UnOp.toString : UnOp → String
  | .not => "!" | .neg => "-"

def BinOp.toString : BinOp → String
  | .add => "+" | .sub => "-" | .mul => "*" | .div => "/" | .mod => "%"
  | .eq => "==" | .ne => "!=" | .lt => "<" | .le => "<=" | .gt => ">" | .ge => ">="
  | .and => "&&" | .or => "||"

/-- Precedence level of a binary operator, higher binds tighter. -/
def BinOp.prec : BinOp → Nat
  | .or => 1 | .and => 2 | .eq | .ne => 3 | .lt | .le | .gt | .ge => 4
  | .add | .sub => 5 | .mul | .div | .mod => 6

def Param.toString (p : Param) : String :=
  s!"{p.ty}{if p.byRef then "&" else ""} {p.name}"

instance : ToString Param := ⟨Param.toString⟩

/-- The binary operator an operator member overloads, `operator+` giving
`+`, so the call prints in the infix form the source wrote. -/
def opOfName (m : String) : Option BinOp :=
  [BinOp.add, .sub, .mul, .div, .mod, .eq, .ne, .lt, .le, .gt, .ge].find?
    fun op => m == s!"operator{op.toString}"

/-- Precedence of an expression, 0 for the conditional, 7 for unary, 8 for
postfix and atoms. A lambda is an atom, it never occurs as an operand. The
call of an operator member has the precedence of its operator, and indexing
that of a postfix form. -/
def Expr.prec : Expr → Nat
  | .cond .. => 0
  | .binop op .. => op.prec
  | .methodCall _ _ m _ _ _ => match opOfName m with | some op => op.prec | none => 8
  | .unop .. | .deref .. | .locOf .. => 7
  | _ => 8

/-- Removes the trailing `;` of a command rendered inside a `for` header. -/
def Cmd.stripSemi (s : String) : String := if s.endsWith ";" then String.ofList s.toList.dropLast else s

mutual

partial def Expr.toString (e : Expr) : String :=
  let paren (p : Nat) (e : Expr) : String :=
    if e.prec < p then s!"({Expr.toString e})" else Expr.toString e
  match e with
  | .intLit n  => s!"{n}"
  | .boolLit b => if b then "true" else "false"
  | .nullptr   => "nullptr"
  | .var x     => x
  | .unop op e => s!"{op.toString}{paren 7 e}"
  | .binop op l r => s!"{paren op.prec l} {op.toString} {paren (op.prec + 1) r}"
  | .cond c t e => s!"{paren 1 c} ? {paren 1 t} : {paren 0 e}"
  | .call f as _ => s!"{f}({", ".intercalate (as.map Expr.toString)})"
  | .callFn f as => s!"{paren 8 f}({", ".intercalate (as.map Expr.toString)})"
  | .methodCall r arrow m as _ _ =>
    match opOfName m, as with
    | some op, [a] => s!"{paren op.prec r} {op.toString} {paren (op.prec + 1) a}"
    | none, [a] =>
      if m == "operator[]" then s!"{paren 8 r}[{Expr.toString a}]"
      else s!"{paren 8 r}{if arrow then "->" else "."}{m}({", ".intercalate (as.map Expr.toString)})"
    | _, _ => s!"{paren 8 r}{if arrow then "->" else "."}{m}({", ".intercalate (as.map Expr.toString)})"
  | .this => "this"
  | .newObj c as => s!"new {c}({", ".intercalate (as.map Expr.toString)})"
  | .newVec t n => s!"new std::vector<{t}>({Expr.toString n})"
  | .field e f => s!"{paren 8 e}.{f}"
  | .arrow e f => s!"{paren 8 e}->{f}"
  | .deref e   => s!"*{paren 7 e}"
  | .index e i => s!"{paren 8 e}[{Expr.toString i}]"
  | .lambda ps r b => s!"[=]({", ".intercalate (ps.map Param.toString)}) -> {r} {Cmd.toString (.block b)}"
  | .locOf e   => s!"&{paren 7 e}"

partial def Cmd.toString : Cmd → String
  | .block cs => s!"\{ {" ".intercalate (cs.map Cmd.toString)} }"
  | .ite c t [] => s!"if ({Expr.toString c}) {Cmd.toString (.block t)}"
  | .ite c t e => s!"if ({Expr.toString c}) {Cmd.toString (.block t)} else {Cmd.toString (.block e)}"
  | .while c b => s!"while ({Expr.toString c}) {Cmd.toString (.block b)}"
  | .for i c s b => s!"for ({Cmd.stripSemi (Cmd.toString i)}; {Expr.toString c}; {Cmd.stripSemi (Cmd.toString s)}) {Cmd.toString (.block b)}"
  | .ret none => "return;"
  | .ret (some e) => s!"return {Expr.toString e};"
  | .decl t x e => s!"{t} {x} = {Expr.toString e};"
  | .declRef t x e => s!"{t}& {x} = {Expr.toString e};"
  | .declAuto x e => s!"auto {x} = {Expr.toString e};"
  | .assign l r => s!"{Expr.toString l} = {Expr.toString r};"
  | .exprStmt e => s!"{Expr.toString e};"
  | .delete e _ => s!"delete {Expr.toString e};"

end

instance : ToString Expr := ⟨Expr.toString⟩
instance : ToString Cmd := ⟨Cmd.toString⟩

def Loc.toString (l : Loc) : String := s!"ℓ{l}"

partial def Val.toString : Val → String
  | .int n  => s!"{n}"
  | .bool b => if b then "true" else "false"
  | .void   => "void"
  | .loc l  => Loc.toString l
  | .null   => "nullptr"
  | .obj c fs => s!"{c}\{{", ".intercalate (fs.map fun (f, l) => s!"{f} ↦ {Loc.toString l}")}}"
  | .vec ls => s!"vector[{", ".intercalate (ls.map Loc.toString)}]"
  | .closure ps _ _ cap =>
    s!"closure({", ".intercalate (ps.map Param.toString)})[{", ".intercalate (cap.map fun (x, v) => s!"{x} ↦ {Val.toString v}")}]"

instance : ToString Val := ⟨Val.toString⟩

def Env.toString (ρ : Env) : String :=
  "[" ++ ", ".intercalate (ρ.reverse.map fun (x, b) => s!"{x} ↦ {Loc.toString b.loc}") ++ "]"

def Store.toString (σ : Store) : String :=
  "{" ++ ", ".intercalate (σ.mem.reverse.map fun (l, v) => s!"{Loc.toString l} ↦ {v}") ++ "}"

def Ctrl.toString : Ctrl → String
  | .normal => "normal"
  | .ret v  => s!"ret {v}"

instance : ToString Ctrl := ⟨Ctrl.toString⟩

def Error.toString : Error → String
  | .divisionByZero        => "division by zero"
  | .overflow              => "int overflow"
  | .nullDereference       => "dereference of nullptr"
  | .outOfBounds i n       => s!"index {i} outside a vector of size {n}"
  | .negativeSize n        => s!"vector of negative size {n}"
  | .danglingLocation l    => s!"access to a location outside the store, {Loc.toString l}"
  | .undeclaredVariable x  => s!"undeclared variable {x}"
  | .undeclaredFunction f  => s!"undeclared function {f}"
  | .arity f               => s!"wrong number of arguments in call to {f}"
  | .typeError msg         => s!"type error at run time, {msg}"
  | .missingReturn f       => s!"function {f} ended without return"
  | .notCallable v         => s!"call of a value that is not a function, {v}"
  | .deleteWithoutVirtualDtor s t => s!"delete through {s}* of an object of class {t} without a virtual destructor"
  | .doubleDelete l        => s!"delete of a location already freed, {Loc.toString l}"

instance : ToString Error := ⟨Error.toString⟩

end CoreCpp
