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

def Ty.toString : Ty → String
  | .int => "int" | .bool => "bool" | .void => "void"
  | .cls c => c
  | .ptr t => s!"{t.toString}*"
  | .vec t => s!"std::vector<{t.toString}>"
  | .nullT => "nullptr_t"

instance : ToString Ty := ⟨Ty.toString⟩

namespace Expr

/-- Precedence of an expression, 0 for the conditional, 7 for unary, 8 for
postfix and atoms. -/
def prec : Expr → Nat
  | .cond .. => 0
  | .binop op .. => op.prec
  | .unop .. | .deref .. => 7
  | _ => 8

partial def toString (e : Expr) : String :=
  let paren (p : Nat) (e : Expr) : String :=
    if e.prec < p then s!"({toString e})" else toString e
  match e with
  | .intLit n  => s!"{n}"
  | .boolLit b => if b then "true" else "false"
  | .nullptr   => "nullptr"
  | .var x     => x
  | .unop op e => s!"{op.toString}{paren 7 e}"
  | .binop op l r => s!"{paren op.prec l} {op.toString} {paren (op.prec + 1) r}"
  | .cond c t e => s!"{paren 1 c} ? {paren 1 t} : {paren 0 e}"
  | .call f as => s!"{f}({", ".intercalate (as.map toString)})"
  | .newObj c  => s!"new {c}()"
  | .newVec t n => s!"new std::vector<{t}>({toString n})"
  | .field e f => s!"{paren 8 e}.{f}"
  | .arrow e f => s!"{paren 8 e}->{f}"
  | .deref e   => s!"*{paren 7 e}"
  | .index e i => s!"{paren 8 e}[{toString i}]"

end Expr

instance : ToString Expr := ⟨Expr.toString⟩

namespace Cmd

/-- Removes the trailing `;` of a command rendered inside a `for` header. -/
def stripSemi (s : String) : String := if s.endsWith ";" then String.ofList s.toList.dropLast else s

partial def toString : Cmd → String
  | .block cs => s!"\{ {" ".intercalate (cs.map toString)} }"
  | .ite c t [] => s!"if ({c}) {toString (.block t)}"
  | .ite c t e => s!"if ({c}) {toString (.block t)} else {toString (.block e)}"
  | .while c b => s!"while ({c}) {toString (.block b)}"
  | .for i c s b => s!"for ({stripSemi (toString i)}; {c}; {stripSemi (toString s)}) {toString (.block b)}"
  | .ret none => "return;"
  | .ret (some e) => s!"return {e};"
  | .decl t x e => s!"{t} {x} = {e};"
  | .declRef t x e => s!"{t}& {x} = {e};"
  | .declAuto x e => s!"auto {x} = {e};"
  | .assign l r => s!"{l} = {r};"
  | .exprStmt e => s!"{e};"

end Cmd

instance : ToString Cmd := ⟨Cmd.toString⟩

def Loc.toString (l : Loc) : String := s!"ℓ{l}"

def Val.toString : Val → String
  | .int n  => s!"{n}"
  | .bool b => if b then "true" else "false"
  | .void   => "void"
  | .loc l  => Loc.toString l
  | .null   => "nullptr"
  | .obj c fs => s!"{c}\{{", ".intercalate (fs.map fun (f, l) => s!"{f} ↦ {Loc.toString l}")}}"
  | .vec ls => s!"vector[{", ".intercalate (ls.map Loc.toString)}]"

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

instance : ToString Error := ⟨Error.toString⟩

end CoreCpp
