import CoreCpp.Syntax

/-!
# Class template instantiation

A class template is expanded by substitution before the program is checked
and before it runs, the rule `Inst` of the UD VI specification.

    p has template<typename T> class C { … }    C<τ> mentioned in p    C<τ> not in the class table
    ────────────────────────────────────────────────────────────────────────────────── (Inst)
    p ⟶ p, class C<τ> { … [T := τ] … }

The rule applies to a fixed point, because the class it adds may mention
another instantiation. Instantiation costs nothing at run time, since it
happens before, and two instantiations of one template are two independent
classes, with no subtype relation between them.

A template is never checked, only its instantiations are, as in C++. The name
of an instantiation is the chain the design prints for the type, `Pilha<int>`,
so the name in the source and the name of the expanded class agree, and the
parser builds it when it reads a type.
-/

namespace CoreCpp
namespace Templates

/-! ## Substitution in a mangled class name

A class name carries its type arguments as text, `No<T>`, so substituting the
parameter of the template rewrites the name as well as the types around it.
-/

/-- Splits the arguments of a mangled name at the commas of depth zero. -/
partial def splitArgs (s : String) : List String :=
  let rec go (cs : List Char) (depth : Nat) (cur : List Char) (acc : List String) : List String :=
    match cs with
    | [] => acc ++ [String.ofList cur.reverse]
    | c :: rest =>
      if c == '<' then go rest (depth + 1) (c :: cur) acc
      else if c == '>' then go rest (depth - 1) (c :: cur) acc
      else if c == ',' && depth == 0 then go rest depth [] (acc ++ [String.ofList cur.reverse])
      else go rest depth (c :: cur) acc
  go s.toList 0 [] []

/-- The base name and the arguments of a mangled name, `Pilha<int>` into
`Pilha` and `["int"]`, and a name without arguments into itself and `[]`. -/
def splitName (n : String) : String × List String :=
  match n.splitOn "<" with
  | [] | [_] => (n, [])
  | base :: rest =>
    let inner := "<".intercalate rest
    let inner := if inner.endsWith ">" then inner.dropRight 1 else inner
    (base, splitArgs inner)

/-- Substitutes the type parameter in a mangled class name, `[T := int]` on
`No<T>` giving `No<int>`. The parameter may also be the whole name. -/
partial def substName (param repl : String) (n : String) : String :=
  if n == param then repl
  else
    let (base, args) := splitName n
    if args.isEmpty then n
    else
      let subArg (a : String) : String :=
        let core := (a.dropEndWhile (· == '*')).toString
        let stars := a.length - core.length
        substName param repl core ++ String.ofList (List.replicate stars '*')
      s!"{base}<{", ".intercalate (args.map subArg)}>"

/-- `[T := τ]` on a type. -/
partial def substTy (param : String) (τ : Ty) : Ty → Ty
  | .cls n => if n == param then τ else .cls (substName param τ.toString n)
  | .ptr t => .ptr (substTy param τ t)
  | .vec t => .vec (substTy param τ t)
  | .fn r ps => .fn (substTy param τ r) (ps.map (substTy param τ))
  | t => t

def substParam (param : String) (τ : Ty) (q : Param) : Param :=
  { q with ty := substTy param τ q.ty }

mutual

/-- `[T := τ]` on an expression, on the types it mentions and on the class
names of `new` and of the instantiations inside them. -/
partial def substExpr (param : String) (τ : Ty) : Expr → Expr
  | .unop op e => .unop op (substExpr param τ e)
  | .binop op a b => .binop op (substExpr param τ a) (substExpr param τ b)
  | .cond a b c => .cond (substExpr param τ a) (substExpr param τ b) (substExpr param τ c)
  | .call f es s => .call f (es.map (substExpr param τ)) s
  | .callFn f es => .callFn (substExpr param τ f) (es.map (substExpr param τ))
  | .newObj c es => .newObj (substName param τ.toString c) (es.map (substExpr param τ))
  | .newVec t n => .newVec (substTy param τ t) (substExpr param τ n)
  | .methodCall r a m es st sg =>
    .methodCall (substExpr param τ r) a m (es.map (substExpr param τ)) st sg
  | .field e f => .field (substExpr param τ e) f
  | .arrow e f => .arrow (substExpr param τ e) f
  | .deref e => .deref (substExpr param τ e)
  | .locOf e => .locOf (substExpr param τ e)
  | .index e i => .index (substExpr param τ e) (substExpr param τ i)
  | .lambda ps r b => .lambda (ps.map (substParam param τ)) (substTy param τ r) (b.map (substCmd param τ))
  | e => e

/-- `[T := τ]` on a command. -/
partial def substCmd (param : String) (τ : Ty) : Cmd → Cmd
  | .block cs => .block (cs.map (substCmd param τ))
  | .ite c t e => .ite (substExpr param τ c) (t.map (substCmd param τ)) (e.map (substCmd param τ))
  | .while c b => .while (substExpr param τ c) (b.map (substCmd param τ))
  | .for i c s b =>
    .for (substCmd param τ i) (substExpr param τ c) (substCmd param τ s) (b.map (substCmd param τ))
  | .ret none => .ret none
  | .ret (some e) => .ret (some (substExpr param τ e))
  | .decl t x e => .decl (substTy param τ t) x (substExpr param τ e)
  | .declRef t x e => .declRef (substTy param τ t) x (substExpr param τ e)
  | .declAuto x e => .declAuto x (substExpr param τ e)
  | .assign l r => .assign (substExpr param τ l) (substExpr param τ r)
  | .exprStmt e => .exprStmt (substExpr param τ e)
  | .delete e s => .delete (substExpr param τ e) s

end

/-- The class of the template instantiated at τ, with the name the source
writes for it. -/
def substClass (param : String) (τ : Ty) (c : ClassDecl) : ClassDecl :=
  { name := s!"{c.name}<{τ}>"
    base := c.base.map (substName param τ.toString)
    fields := c.fields.map fun f => { f with ty := substTy param τ f.ty }
    methods := c.methods.map fun m =>
      { m with ret := substTy param τ m.ret,
               params := m.params.map (substParam param τ),
               body := m.body.map (substCmd param τ) }
    ctor := c.ctor.map fun k =>
      { k with params := k.params.map (substParam param τ), body := k.body.map (substCmd param τ) }
    dtor := c.dtor.map fun d => { d with body := d.body.map (substCmd param τ) } }

/-! ## The instantiations a program mentions -/

/-- The class names a type mentions. -/
partial def tyNames : Ty → List String
  | .cls n => [n]
  | .ptr t | .vec t => tyNames t
  | .fn r ps => tyNames r ++ ps.flatMap tyNames
  | _ => []

mutual

partial def exprNames : Expr → List String
  | .unop _ e | .field e _ | .arrow e _ | .deref e | .locOf e => exprNames e
  | .binop _ a b | .index a b => exprNames a ++ exprNames b
  | .cond a b c => exprNames a ++ exprNames b ++ exprNames c
  | .call _ es _ => es.flatMap exprNames
  | .callFn f es => exprNames f ++ es.flatMap exprNames
  | .methodCall r _ _ es _ _ => exprNames r ++ es.flatMap exprNames
  | .newObj c es => c :: es.flatMap exprNames
  | .newVec t n => tyNames t ++ exprNames n
  | .lambda ps r b => ps.flatMap (fun q => tyNames q.ty) ++ tyNames r ++ b.flatMap cmdNames
  | _ => []

partial def cmdNames : Cmd → List String
  | .block cs => cs.flatMap cmdNames
  | .ite c t e => exprNames c ++ t.flatMap cmdNames ++ e.flatMap cmdNames
  | .while c b => exprNames c ++ b.flatMap cmdNames
  | .for i c s b => cmdNames i ++ exprNames c ++ cmdNames s ++ b.flatMap cmdNames
  | .ret none => []
  | .ret (some e) | .exprStmt e | .declAuto _ e | .delete e _ => exprNames e
  | .decl t _ e | .declRef t _ e => tyNames t ++ exprNames e
  | .assign l r => exprNames l ++ exprNames r

end

def classNames (c : ClassDecl) : List String :=
  c.base.toList
    ++ c.fields.flatMap (fun f => tyNames f.ty)
    ++ c.methods.flatMap (fun m => tyNames m.ret ++ m.params.flatMap (fun q => tyNames q.ty) ++ m.body.flatMap cmdNames)
    ++ (c.ctor.map fun k => k.params.flatMap (fun q => tyNames q.ty) ++ k.body.flatMap cmdNames).getD []
    ++ (c.dtor.map fun d => d.body.flatMap cmdNames).getD []

def declNames : Decl → List String
  | .cls c => classNames c
  | .tmpl _ _ => []
  | .fn f => tyNames f.ret ++ f.params.flatMap (fun q => tyNames q.ty) ++ f.body.flatMap cmdNames

/-- The type a mangled name denotes, the inverse of `Ty.toString` on the
types a template is instantiated at. A function type is not one of them. -/
partial def readTy (s : String) : Option Ty :=
  let core := (s.dropEndWhile (· == '*')).toString
  let stars := s.length - core.length
  let base : Option Ty :=
    if core == "int" then some .int
    else if core == "bool" then some .bool
    else if core == "void" then some .void
    else if core == "" || core.contains '(' then none
    else if core.startsWith "std::vector<" && core.endsWith ">" then
      (readTy ((core.drop "std::vector<".length).toString.dropRight 1)).map Ty.vec
    else some (.cls core)
  base.map fun t => (List.replicate stars ()).foldl (fun t _ => Ty.ptr t) t

/-- The class the program should hold for the mentioned name, or the reason
it cannot be built. -/
def expand (p : Program) (n : String) : Except String ClassDecl := do
  let (base, args) := splitName n
  let [a] := args | throw s!"the instantiation {n} does not have one type argument"
  let some (param, cd) := p.lookupTemplate base
    | throw s!"{base} is not a class template, in the instantiation {n}"
  let some τ := readTy a | throw s!"the type argument {a} of {n} is not one this subset instantiates"
  return substClass param τ cd

/-- Adds one class per instantiation the program mentions, to a fixed point.
Idempotent, so `check` and `runWith` may both apply it. -/
partial def instantiate (p : Program) (fuel : Nat := 32) : Except String Program := do
  match fuel with
  | 0 => throw "class template instantiation does not terminate"
  | fuel + 1 =>
    let known := p.classes.map (·.name)
    let wanted := (p.flatMap declNames).eraseDups.filter fun n =>
      n.contains '<' && !known.contains n
    if wanted.isEmpty then return p
    let added ← wanted.mapM (expand p)
    instantiate (p ++ added.map Decl.cls) fuel

end Templates
end CoreCpp
