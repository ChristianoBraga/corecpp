import CoreCpp.Syntax
import CoreCpp.Pretty

/-!
# Fragments of Core C++, one per paradigm

Three of the four paradigms are restrictions of the core, and a restriction
is a predicate over the abstract syntax, not a grammar of its own.
A program lies in a fragment when no construction it mentions is forbidden
there, so the three checks are one walk over `Program` with three sets of
forbidden constructions.

* The **imperative** fragment keeps the basic types, variables, assignment,
  the commands and first order functions. It forbids classes, `new`, `delete`,
  pointers, vectors, lambdas and function values. Its store therefore holds
  only basic values, grows by declaration and shrinks at scope exit, and the
  program never reaches a location it did not declare.
* The **object oriented** fragment adds classes, methods, constructors,
  destructors, inheritance, dispatch, `new`, `delete`, pointers and vectors,
  and forbids lambdas and function values. State outlives a block there, and
  is reached only through `this` and through pointers.
* The **functional** fragment keeps the expressions, the lambdas, the function
  values and the calls, and forbids assignment, the loops, `new`, `delete`,
  references and everything that reaches an object. Its store is written once,
  at allocation, and never again, so an expression has the same value every
  time it is evaluated in the same ρ and σ.

The logic paradigm has no counterpart in the core, and `CoreCpp.Logic` gives
it a language of its own.
-/

namespace CoreCpp

/-- The three fragments of Core C++, one per paradigm that restricts it. -/
inductive Frag where
  /-- Basic types, variables, assignment, commands, first order functions. -/
  | imperative
  /-- The imperative fragment with classes, objects, dispatch and the heap. -/
  | oo
  /-- Expressions, lambdas, function values and calls, with no update. -/
  | functional
  deriving Repr, BEq, DecidableEq, Inhabited

/-- The name of a fragment, as the command line writes it. -/
def Frag.toString : Frag → String
  | .imperative => "imperative"
  | .oo => "oo"
  | .functional => "functional"

instance : ToString Frag := ⟨Frag.toString⟩

/-- The fragment of that name, for the command line. -/
def Frag.ofString? : String → Option Frag
  | "imperative" => some .imperative
  | "oo" => some .oo
  | "functional" => some .functional
  | _ => none

/-- Why a program lies outside a fragment. `what` names the construction the
fragment forbids and `site` the declaration in which it occurs. -/
structure Reject where
  /-- The fragment the program was checked against. -/
  frag : Frag
  /-- The forbidden construction, named as the language design names it. -/
  what : String
  /-- The declaration in which the construction occurs. -/
  site : String
  deriving Repr, BEq, Inhabited

def Reject.toString (r : Reject) : String :=
  s!"{r.site}: {r.what} is outside the {r.frag} fragment"

instance : ToString Reject := ⟨Reject.toString⟩

namespace Fragment

/-- The constructions each fragment forbids, named as the language design
names them. The walk below asks this predicate once per construction it
meets. -/
def forbids (f : Frag) (what : String) : Bool :=
  match f with
  | .imperative =>
    ["class", "class template", "method call", "this", "new", "delete",
     "field access", "pointer dereference", "indexing", "pointer type",
     "vector type", "class type", "lambda", "function type",
     "call through a function value"].contains what
  | .oo =>
    ["lambda", "function type", "call through a function value"].contains what
  | .functional =>
    ["assignment", "while", "for", "expression statement", "local reference",
     "reference parameter", "class", "class template", "method call", "this",
     "new", "delete", "field access", "pointer dereference", "indexing",
     "pointer type", "vector type", "class type"].contains what

/-- The first construction of the type τ that the fragment forbids. -/
partial def tyBad (f : Frag) : Ty → Option String
  | .int | .bool | .void | .nullT => none
  | .cls _ => if forbids f "class type" then some "class type" else none
  | .ptr t => if forbids f "pointer type" then some "pointer type" else tyBad f t
  | .vec t => if forbids f "vector type" then some "vector type" else tyBad f t
  | .fn r ps =>
    if forbids f "function type" then some "function type"
    else (tyBad f r).orElse fun _ => ps.findSome? (tyBad f)

mutual

/-- The first construction of the expression that the fragment forbids. -/
partial def exprBad (f : Frag) : Expr → Option String
  | .intLit _ | .boolLit _ | .nullptr | .var _ => none
  | .unop _ e | .locOf e => exprBad f e
  | .binop _ a b => (exprBad f a).orElse fun _ => exprBad f b
  | .cond a b c => (exprBad f a).orElse fun _ => (exprBad f b).orElse fun _ => exprBad f c
  | .call _ es _ => es.findSome? (exprBad f)
  | .newObj _ es =>
    if forbids f "new" then some "new" else es.findSome? (exprBad f)
  | .newVec t n =>
    if forbids f "new" then some "new"
    else (tyBad f t).orElse fun _ => exprBad f n
  | .this => if forbids f "this" then some "this" else none
  | .methodCall recv _ _ es _ _ =>
    if forbids f "method call" then some "method call"
    else (exprBad f recv).orElse fun _ => es.findSome? (exprBad f)
  | .field e _ | .arrow e _ =>
    if forbids f "field access" then some "field access" else exprBad f e
  | .deref e =>
    if forbids f "pointer dereference" then some "pointer dereference" else exprBad f e
  | .index e i =>
    if forbids f "indexing" then some "indexing"
    else (exprBad f e).orElse fun _ => exprBad f i
  | .lambda ps τ b =>
    if forbids f "lambda" then some "lambda"
    else (ps.findSome? fun q => paramBad f q).orElse fun _ =>
      (tyBad f τ).orElse fun _ => b.findSome? (cmdBad f)
  | .callFn g es =>
    if forbids f "call through a function value" then some "call through a function value"
    else (exprBad f g).orElse fun _ => es.findSome? (exprBad f)

/-- The first construction of the command that the fragment forbids. -/
partial def cmdBad (f : Frag) : Cmd → Option String
  | .block cs => cs.findSome? (cmdBad f)
  | .ite c t e =>
    (exprBad f c).orElse fun _ =>
      (t.findSome? (cmdBad f)).orElse fun _ => e.findSome? (cmdBad f)
  | .while c b =>
    if forbids f "while" then some "while"
    else (exprBad f c).orElse fun _ => b.findSome? (cmdBad f)
  | .for i c s b =>
    if forbids f "for" then some "for"
    else (cmdBad f i).orElse fun _ => (exprBad f c).orElse fun _ =>
      (cmdBad f s).orElse fun _ => b.findSome? (cmdBad f)
  | .ret none => none
  | .ret (some e) => exprBad f e
  | .decl τ _ e => (tyBad f τ).orElse fun _ => exprBad f e
  | .declRef τ _ e =>
    if forbids f "local reference" then some "local reference"
    else (tyBad f τ).orElse fun _ => exprBad f e
  | .declAuto _ e => exprBad f e
  | .assign l r =>
    if forbids f "assignment" then some "assignment"
    else (exprBad f l).orElse fun _ => exprBad f r
  | .exprStmt e =>
    if forbids f "expression statement" then some "expression statement" else exprBad f e
  | .delete e _ =>
    if forbids f "delete" then some "delete" else exprBad f e

/-- The first construction of the parameter that the fragment forbids. -/
partial def paramBad (f : Frag) (q : Param) : Option String :=
  if q.byRef && forbids f "reference parameter" then some "reference parameter"
  else tyBad f q.ty

end

/-- The first construction of the function that the fragment forbids. -/
def funBad (f : Frag) (fn : Fun) : Option String :=
  (tyBad f fn.ret).orElse fun _ =>
    (fn.params.findSome? (paramBad f)).orElse fun _ => fn.body.findSome? (cmdBad f)

/-- The first construction of the class that the fragment forbids, with the
site at which it occurs. -/
def classBad (f : Frag) (c : ClassDecl) : Option (String × String) :=
  if forbids f "class" then some ("class", s!"class {c.name}")
  else
    let inFields := c.fields.findSome? fun fd =>
      (tyBad f fd.ty).map (·, s!"class {c.name}, field {fd.name}")
    let inMethods := c.methods.findSome? fun m =>
      ((tyBad f m.ret).orElse fun _ =>
        (m.params.findSome? (paramBad f)).orElse fun _ =>
          m.body.findSome? (cmdBad f)).map (·, s!"class {c.name}, method {m.name}")
    let inCtor := c.ctor.bind fun k =>
      ((k.params.findSome? (paramBad f)).orElse fun _ =>
        k.body.findSome? (cmdBad f)).map (·, s!"class {c.name}, constructor")
    let inDtor := c.dtor.bind fun d =>
      (d.body.findSome? (cmdBad f)).map (·, s!"class {c.name}, destructor")
    inFields.orElse fun _ => inMethods.orElse fun _ => inCtor.orElse fun _ => inDtor

/-- The first construction of the declaration that the fragment forbids,
with the site at which it occurs. -/
def declBad (f : Frag) : Decl → Option (String × String)
  | .fn fn => (funBad f fn).map (·, s!"function {fn.name}")
  | .cls c => classBad f c
  | .tmpl _ c =>
    if forbids f "class template" then some ("class template", s!"template {c.name}")
    else classBad f c

end Fragment

/-- Whether the program lies in the fragment, and why it does not.

    p has no construction f forbids
    ─────────────────────────────── (Frag)
    p ∈ f                                                                     -/
def fragment (f : Frag) (p : Program) : Except Reject Unit :=
  match p.findSome? (Fragment.declBad f) with
  | none => .ok ()
  | some (what, site) => .error ⟨f, what, site⟩

end CoreCpp
