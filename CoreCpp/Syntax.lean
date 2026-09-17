/-!
# Core C++ abstract syntax, subset

Basic types, expressions, commands and functions. A statement is a command or an expression followed by `;`. Assignment is a command. One tree per nonterminal
of the grammar in section 4 of the language design.
-/

namespace CoreCpp

/-- Basic types. -/
inductive Ty where
  | int | bool | void
  deriving Repr, BEq, DecidableEq, Inhabited

inductive UnOp where
  | not | neg
  deriving Repr, BEq, DecidableEq

inductive BinOp where
  | add | sub | mul | div | mod
  | eq | ne | lt | le | gt | ge
  | and | or
  deriving Repr, BEq, DecidableEq

/-- Expressions. Function call is included because `Args` is part of `PostfixExpr`. -/
inductive Expr where
  | intLit  (n : Int)
  | boolLit (b : Bool)
  | var     (x : String)
  | unop    (op : UnOp) (e : Expr)
  | binop   (op : BinOp) (l r : Expr)
  | cond    (c t e : Expr)
  | call    (f : String) (args : List Expr)
  deriving Repr, BEq, Inhabited

/-- Commands. A block is a list of commands. `exprStmt` is the statement that
evaluates an expression and discards its value. -/
inductive Cmd where
  | block    (cs : List Cmd)
  | ite      (c : Expr) (t : List Cmd) (e : List Cmd)
  | while    (c : Expr) (body : List Cmd)
  | for      (init : Cmd) (c : Expr) (step : Cmd) (body : List Cmd)
  | ret      (e : Option Expr)
  | decl     (ty : Ty) (x : String) (init : Expr)
  | declAuto (x : String) (init : Expr)
  | assign   (lhs rhs : Expr)
  | exprStmt (e : Expr)
  deriving Repr, BEq, Inhabited

structure Param where
  ty   : Ty
  name : String
  deriving Repr, BEq, Inhabited

structure Fun where
  ret    : Ty
  name   : String
  params : List Param
  body   : List Cmd
  deriving Repr, BEq, Inhabited

/-- A program is a list of functions. There are no global variables. -/
abbrev Program := List Fun

end CoreCpp
