import Verso
import VersoManual
import VersoBlueprint
import CoreCpp.Syntax
import CoreCpp.Typing
import CoreCpp.Eval
import CoreCpp.Semantics.Static
import CoreCpp.Semantics.Dynamic

open Verso.Genre
open Verso.Genre.Manual
open Informal

set_option verso.blueprint.foldCodeBlocks true

#doc (Manual) "Types and expressions" =>

The typing and evaluation rules of the basic constructions of `Expr`. The typing rules are constructors of `Semantics.HasType` and `Semantics.LHasType`, which `Typing.expr` and `Typing.lval` implement. The evaluation rules are constructors of `Semantics.Eval` and `Semantics.LEval`, which `Eval.expr` and `Eval.lval` implement, each rule in the comment of the case that implements it. Calls, lambdas, `this`, members and the uses of the library have their rules in the later chapters.

Where C++17 leaves the evaluation order unspecified, Core C++ evaluates left to right. The last section holds the composite and recursive types, objects and pointers, whose expressions denote locations.

:::group "ud2"
Values, types and expressions.
:::

# Literals

:::definition "expr_lit" (parent := "ud2") (lean := "CoreCpp.Typing.expr, CoreCpp.Eval.expr, CoreCpp.Eval.int32, CoreCpp.Int32.inRange, CoreCpp.Semantics.HasType, CoreCpp.Semantics.Eval") (uses := "judg_ty_expr, judg_ev_expr, dom_int32")
An integer literal has type `int` and a boolean literal has type `bool`. Evaluation leaves the store unchanged. The rule Lit has the range premise of {bpref "dom_int32"}[], which never fails, because the lexer of {bpref "lex_automaton"}[] rejects a literal above $`2^{31}-1`.

$$`\dfrac{}{\Gamma \vdash n : \mathsf{int}}\;\textsf{(T-Lit)}`

$$`\dfrac{}{\Gamma \vdash b : \mathsf{bool}}\;\textsf{(T-BoolLit)}`

$$`\dfrac{n \in [-2^{31},\, 2^{31}-1]}{\rho, \sigma \vdash n \Rightarrow \mathsf{int}\,n, \sigma}\;\textsf{(Lit)}`

$$`\dfrac{}{\rho, \sigma \vdash b \Rightarrow \mathsf{bool}\,b, \sigma}\;\textsf{(BoolLit)}`
:::

# Variable

:::definition "expr_lvar" (parent := "ud2") (lean := "CoreCpp.Typing.lval, CoreCpp.Eval.lval, CoreCpp.TEnv.isConst, CoreCpp.Semantics.LHasType, CoreCpp.Semantics.LEval") (uses := "judg_ty_lval, judg_ev_lval")
The variable denotes the location the environment assigns to it, and the store does not change. A variable that a lambda captures by copy is read only in $`\Gamma`, so it denotes no location for the type checker and is never assigned. Inside a member body an unqualified field of `this` also denotes a location, rule LocVarField of {bpref "cls_this"}[], with the typing rule T-LocVarField. The other expressions that denote a location, `*e`, `e.f` and `e->f`, are the nodes of the last section, and an element `v[i]` of a vector is a use of the library, {bpref "std_uses"}[].

$$`\dfrac{\Gamma(x) = \tau \qquad x \text{ not captured}}{\Gamma \vdash_{\ell} x : \tau}\;\textsf{(T-LocVar)}`

$$`\dfrac{\rho(x) = \ell}{\rho, \sigma \vdash x \Rightarrow_{\ell} \ell, \sigma}\;\textsf{(LocVar)}`
:::

:::definition "expr_var" (parent := "ud2") (lean := "CoreCpp.Typing.expr, CoreCpp.Eval.expr, CoreCpp.Eval.lval, CoreCpp.Eval.readLoc, CoreCpp.Semantics.HasType, CoreCpp.Semantics.Eval") (uses := "judg_ty_expr, judg_ev_expr, expr_lvar")
Reading $`x` is reading $`\sigma(\rho(x))`. The premise $`\ell \in \mathrm{dom}\,\sigma` fails for a location that left the store, so that read has no derivation and the evaluator gives `error`. Inside a member body $`x` may be a field of `this`, rule T-VarField of {bpref "cls_this"}[], and the first premise of Var then holds by LocVarField.

$$`\dfrac{\Gamma(x) = \tau}{\Gamma \vdash x : \tau}\;\textsf{(T-Var)}`

$$`\dfrac{\rho, \sigma \vdash x \Rightarrow_{\ell} \ell, \sigma \qquad \ell \in \mathrm{dom}\,\sigma}{\rho, \sigma \vdash x \Rightarrow \sigma(\ell), \sigma}\;\textsf{(Var)}`
:::

# Unary operators

:::definition "expr_unary" (parent := "ud2") (lean := "CoreCpp.Typing.expr, CoreCpp.Eval.expr, CoreCpp.UnOp, CoreCpp.Eval.unop, CoreCpp.Eval.int32, CoreCpp.Semantics.HasType, CoreCpp.Semantics.Eval") (uses := "judg_ty_expr, judg_ev_expr, dom_int32")
Logical negation requires `bool` and arithmetic negation requires `int`. Negation has the range premise, because the negation of $`-2^{31}` overflows, and that negation has no derivation.

$$`\dfrac{\Gamma \vdash e : \mathsf{bool}}{\Gamma \vdash\, !e : \mathsf{bool}}\;\textsf{(T-Not)}`

$$`\dfrac{\Gamma \vdash e : \mathsf{int}}{\Gamma \vdash -e : \mathsf{int}}\;\textsf{(T-Neg)}`

$$`\dfrac{\rho, \sigma \vdash e \Rightarrow \mathsf{bool}\,b, \sigma'}{\rho, \sigma \vdash\, !e \Rightarrow \mathsf{bool}\,\neg b, \sigma'}\;\textsf{(Not)}`

$$`\dfrac{\rho, \sigma \vdash e \Rightarrow \mathsf{int}\,n, \sigma' \qquad -n \in [-2^{31},\, 2^{31}-1]}{\rho, \sigma \vdash -e \Rightarrow \mathsf{int}(-n), \sigma'}\;\textsf{(Neg)}`

In the code, the case `unop` of `Eval.expr` evaluates the operand and calls `Eval.unop`, which applies `Eval.int32` to $`-n`.
:::

# Binary operators

:::definition "expr_arith" (parent := "ud2") (lean := "CoreCpp.Typing.expr, CoreCpp.Eval.expr, CoreCpp.BinOp, CoreCpp.BinOp.isArithmetic, CoreCpp.BinOp.isArith, CoreCpp.BinOp.arith, CoreCpp.BinOp.divide, CoreCpp.Eval.binop, CoreCpp.Semantics.HasType, CoreCpp.Semantics.Eval") (uses := "judg_ty_expr, judg_ev_expr, dom_int32")
The arithmetic operators require `int` on both operands. The left operand is evaluated before the right one, the order Core C++ chooses where C++17 fixes none. Division and remainder truncate toward zero, as in C++. A zero divisor and a result outside the range of `int` fail a premise, so the expression has no derivation and the evaluator gives `error`.

The quotient of $`-2^{31}` by $`-1` is $`2^{31}`, outside the range, so it has no derivation. C++17 leaves the remainder undefined whenever it leaves the quotient undefined (N4659 §8.6 paragraph 4), so the remainder exists only when the quotient is in the range, and the remainder of $`-2^{31}` by $`-1` has no derivation either.

A left operand of class type calls a member `operator⊕` instead, rule T-OpBin of {bpref "op_member"}[].

$$`\dfrac{\Gamma \vdash e_1 : \mathsf{int} \qquad \Gamma \vdash e_2 : \mathsf{int}}{\Gamma \vdash e_1 \oplus e_2 : \mathsf{int}}\;\textsf{(T-Arith)}, \quad \oplus \in \{+, -, *, /, \%\}`

$$`\dfrac{\begin{array}{c} \rho, \sigma \vdash e_1 \Rightarrow \mathsf{int}\,n_1, \sigma_1 \qquad \rho, \sigma_1 \vdash e_2 \Rightarrow \mathsf{int}\,n_2, \sigma_2 \\ n_1 \oplus n_2 \in [-2^{31},\, 2^{31}-1] \end{array}}{\rho, \sigma \vdash e_1 \oplus e_2 \Rightarrow \mathsf{int}(n_1 \oplus n_2), \sigma_2}\;\textsf{(Arith)}, \quad \oplus \in \{+, -, *\}`

$$`\dfrac{\begin{array}{c} \rho, \sigma \vdash e_1 \Rightarrow \mathsf{int}\,n_1, \sigma_1 \qquad \rho, \sigma_1 \vdash e_2 \Rightarrow \mathsf{int}\,n_2, \sigma_2 \\ n_2 \neq 0 \qquad n = n_1 \oslash n_2 \qquad n \in [-2^{31},\, 2^{31}-1] \end{array}}{\rho, \sigma \vdash e_1 \oslash e_2 \Rightarrow \mathsf{int}\,n, \sigma_2}\;\textsf{(Div)}, \quad \oslash \in \{/, \%\}`

In the code, the case `binop` of `Eval.expr` evaluates both operands and calls `Eval.binop`.
:::

:::definition "expr_rel" (parent := "ud2") (lean := "CoreCpp.Typing.expr, CoreCpp.Eval.expr, CoreCpp.Eval.binop, CoreCpp.BinOp.compare, CoreCpp.Typing.compat, CoreCpp.Typing.related, CoreCpp.Ty.comparable, CoreCpp.Semantics.HasType, CoreCpp.Semantics.Eval") (uses := "judg_ty_expr, judg_ev_expr")
Equality compares two `int`, two `bool`, two pointers, or `nullptr` with a pointer or with `nullptr`, when $`\tau_1 \approx \tau_2` or $`\tau_2 \approx \tau_1`, the test `Ty.comparable`. A pointer to a derived class thus compares with a pointer to its base, {bpref "cls_subsumption"}[]. Two pointers are equal when they are the same location, and `nullptr` equals only `nullptr`. Order compares two `int`, and there is no order on pointers. The result is `bool`, and the left operand is evaluated before the right one. A left operand of class type calls a member operator, as in {bpref "expr_arith"}[].

$$`\dfrac{\begin{array}{c} \Gamma \vdash e_1 : \tau_1 \qquad \Gamma \vdash e_2 : \tau_2 \qquad \tau_1 \approx \tau_2 \lor \tau_2 \approx \tau_1 \\ \tau_1, \tau_2 \in \{\mathsf{int}, \mathsf{bool}, \tau*, \mathsf{nullptr\_t}\} \end{array}}{\Gamma \vdash e_1 \bowtie e_2 : \mathsf{bool}}\;\textsf{(T-Eq)}, \quad \bowtie \in \{==, \mathrel{!=}\}`

$$`\dfrac{\Gamma \vdash e_1 : \mathsf{int} \qquad \Gamma \vdash e_2 : \mathsf{int}}{\Gamma \vdash e_1 \bowtie e_2 : \mathsf{bool}}\;\textsf{(T-Rel)}, \quad \bowtie \in \{<, <=, >, >=\}`

$$`\dfrac{\rho, \sigma \vdash e_1 \Rightarrow v_1, \sigma_1 \qquad \rho, \sigma_1 \vdash e_2 \Rightarrow v_2, \sigma_2 \qquad v_1 \bowtie v_2 = b}{\rho, \sigma \vdash e_1 \bowtie e_2 \Rightarrow \mathsf{bool}\,b, \sigma_2}\;\textsf{(Rel)}, \quad \bowtie \in \{==, \mathrel{!=}, <, <=, >, >=\}`
:::

:::definition "expr_logic" (parent := "ud2") (lean := "CoreCpp.Typing.expr, CoreCpp.Eval.expr, CoreCpp.Eval.expectBool, CoreCpp.BinOp.isLogical, CoreCpp.Semantics.HasType, CoreCpp.Semantics.Eval") (uses := "judg_ty_expr, judg_ev_expr")
Conjunction and disjunction require `bool` and short circuit. The second operand is evaluated only when the first one does not decide the result. A class never overloads them.

$$`\dfrac{\Gamma \vdash e_1 : \mathsf{bool} \qquad \Gamma \vdash e_2 : \mathsf{bool}}{\Gamma \vdash e_1 \odot e_2 : \mathsf{bool}}\;\textsf{(T-Logic)}, \quad \odot \in \{\&\&, ||\}`

$$`\dfrac{\rho, \sigma \vdash e_1 \Rightarrow \mathsf{bool}\,\mathtt{false}, \sigma_1}{\rho, \sigma \vdash e_1 \mathbin{\&\&} e_2 \Rightarrow \mathsf{bool}\,\mathtt{false}, \sigma_1}\;\textsf{(And-False)}`

$$`\dfrac{\rho, \sigma \vdash e_1 \Rightarrow \mathsf{bool}\,\mathtt{true}, \sigma_1 \qquad \rho, \sigma_1 \vdash e_2 \Rightarrow v, \sigma_2}{\rho, \sigma \vdash e_1 \mathbin{\&\&} e_2 \Rightarrow v, \sigma_2}\;\textsf{(And-True)}`

$$`\dfrac{\rho, \sigma \vdash e_1 \Rightarrow \mathsf{bool}\,\mathtt{true}, \sigma_1}{\rho, \sigma \vdash e_1 \mathbin{||} e_2 \Rightarrow \mathsf{bool}\,\mathtt{true}, \sigma_1}\;\textsf{(Or-True)}`

$$`\dfrac{\rho, \sigma \vdash e_1 \Rightarrow \mathsf{bool}\,\mathtt{false}, \sigma_1 \qquad \rho, \sigma_1 \vdash e_2 \Rightarrow v, \sigma_2}{\rho, \sigma \vdash e_1 \mathbin{||} e_2 \Rightarrow v, \sigma_2}\;\textsf{(Or-False)}`

In the code, the cases `binop .and` and `binop .or` of `Eval.expr` implement the two pairs of rules.
:::

# Conditional

:::definition "expr_cond" (parent := "ud2") (lean := "CoreCpp.Typing.expr, CoreCpp.Typing.value, CoreCpp.Typing.compat, CoreCpp.Ty.join, CoreCpp.Semantics.HasValues, CoreCpp.Eval.expr, CoreCpp.Eval.expectBool, CoreCpp.Semantics.HasType, CoreCpp.Semantics.Eval, CoreCpp.Typing.lval, CoreCpp.Typing.locJoin, CoreCpp.Eval.lval, CoreCpp.Semantics.LHasType, CoreCpp.Semantics.LEval") (uses := "judg_ty_expr, judg_ev_expr, judg_ty_lval, judg_ev_lval")
The condition is `bool`. For a value, both branches have types with values, neither `void` nor an object type, and the type of the conditional is their join, `Ty.join`. The join is $`\tau_2` when the two types are equal or when $`\tau_2` is a pointer type and $`\tau_3` is $`\mathsf{nullptr\_t}`, $`\tau_3` when $`\tau_2 \approx \tau_3`, and $`\tau_2` when $`\tau_3 \approx \tau_2`. A pointer to a derived class and a pointer to its base thus join at the base, and a pointer and `nullptr` join at the pointer type in either order, so `c ? p : nullptr` and `c ? nullptr : p` both have the type of `p`, the composite pointer type of C++ (N4659 §8.16 paragraph 7). Only the chosen branch is evaluated, after the condition.

$$`\dfrac{\begin{array}{c} \Gamma \vdash e_1 : \mathsf{bool} \qquad \Gamma \vdash e_2 : \tau_2 \qquad \Gamma \vdash e_3 : \tau_3 \\ \tau_2, \tau_3 \text{ have values} \qquad \tau = \mathrm{join}(\tau_2, \tau_3) \end{array}}{\Gamma \vdash e_1\ ?\ e_2 : e_3 \;:\; \tau}\;\textsf{(T-Cond)}`

$$`\mathrm{join}(\tau_2, \tau_3) = \begin{cases} \tau_2 & \text{if } \tau_2 = \tau_3 \text{ or } \tau_2 = \tau'* \text{ and } \tau_3 = \mathsf{nullptr\_t} \\ \tau_3 & \text{else if } \tau_2 \approx \tau_3 \\ \tau_2 & \text{else if } \tau_3 \approx \tau_2 \end{cases}`

$$`\dfrac{\rho, \sigma \vdash e_1 \Rightarrow \mathsf{bool}\,\mathtt{true}, \sigma_1 \qquad \rho, \sigma_1 \vdash e_2 \Rightarrow v, \sigma_2}{\rho, \sigma \vdash e_1\ ?\ e_2 : e_3 \Rightarrow v, \sigma_2}\;\textsf{(Cond-T)}`

$$`\dfrac{\rho, \sigma \vdash e_1 \Rightarrow \mathsf{bool}\,\mathtt{false}, \sigma_1 \qquad \rho, \sigma_1 \vdash e_3 \Rightarrow v, \sigma_2}{\rho, \sigma \vdash e_1\ ?\ e_2 : e_3 \Rightarrow v, \sigma_2}\;\textsf{(Cond-F)}`

When the two branches denote locations of one type, the conditional denotes the location of the chosen branch, as C++ makes it an lvalue (N4659 §8.16 paragraph 4). So `(c ? x : y) = 7` assigns to `x` or to `y`, `int& r = c ? x : y;` binds a reference, and `(c ? *p : *q).value` reaches a field without copying an object. Branches of object type must denote locations, rule T-CondObj, so `c ? *p : *q` never copies. The two types must be equal, or a class and one of its bases, which join at the base, `Typing.locJoin`. The derived object is then reached as an object of its base, as C++ binds it (N4659 §8.16 paragraph 4), so a call of a virtual method dispatches on the class of the chosen object, and a member of the derived class alone is a type error.

$$`\dfrac{\Gamma \vdash e_1 : \mathsf{bool} \qquad \Gamma \vdash_{\ell} e_2 : \tau_2 \qquad \Gamma \vdash_{\ell} e_3 : \tau_3 \qquad \tau = \mathrm{locJoin}(\tau_2, \tau_3)}{\Gamma \vdash_{\ell} e_1\ ?\ e_2 : e_3 \;:\; \tau}\;\textsf{(T-LocCond)}`

$$`\dfrac{\Gamma \vdash_{\ell} e_1\ ?\ e_2 : e_3 \;:\; \tau \qquad \tau \text{ object type}}{\Gamma \vdash e_1\ ?\ e_2 : e_3 \;:\; \tau}\;\textsf{(T-CondObj)}`

$$`\dfrac{\rho, \sigma \vdash e_1 \Rightarrow \mathsf{bool}\,\mathtt{true}, \sigma_1 \qquad \rho, \sigma_1 \vdash e_2 \Rightarrow_{\ell} \ell, \sigma_2}{\rho, \sigma \vdash e_1\ ?\ e_2 : e_3 \Rightarrow_{\ell} \ell, \sigma_2}\;\textsf{(LocCond-T)}`

$$`\dfrac{\rho, \sigma \vdash e_1 \Rightarrow \mathsf{bool}\,\mathtt{false}, \sigma_1 \qquad \rho, \sigma_1 \vdash e_3 \Rightarrow_{\ell} \ell, \sigma_2}{\rho, \sigma \vdash e_1\ ?\ e_2 : e_3 \Rightarrow_{\ell} \ell, \sigma_2}\;\textsf{(LocCond-F)}`
:::

# Objects and pointers

:::definition "expr_null" (parent := "ud2") (lean := "CoreCpp.Typing.expr, CoreCpp.Typing.compat, CoreCpp.Eval.expr, CoreCpp.Semantics.HasType, CoreCpp.Semantics.Eval") (uses := "judg_ty_expr, judg_ev_expr, dom_val")
The literal `nullptr` has the internal type $`\mathsf{nullptr\_t}`, compatible with itself and with every pointer type, and with no other. Its value is $`\mathsf{null}`.

$$`\dfrac{}{\Gamma \vdash \mathtt{nullptr} : \mathsf{nullptr\_t}}\;\textsf{(T-Null)}`

$$`\dfrac{}{\rho, \sigma \vdash \mathtt{nullptr} \Rightarrow \mathsf{null}, \sigma}\;\textsf{(Null)}`
:::

:::definition "expr_new" (parent := "ud2") (lean := "CoreCpp.Typing.expr, CoreCpp.Eval.expr, CoreCpp.Program.lookupClass, CoreCpp.Program.allFields, CoreCpp.Store.alloc, CoreCpp.Store.allocMany, CoreCpp.Ty.default, CoreCpp.Semantics.Ctors, CoreCpp.Semantics.HasType, CoreCpp.Semantics.Eval") (uses := "judg_ty_expr, judg_ev_expr, dom_classes, dom_store")
The expression `new C()` allocates one location per field of $`C`, each with the default value of its type, `Ty.default`, then the record itself, tagged with the class, and evaluates to a pointer to the record. Its type is $`C*`. A class without a constructor takes no arguments, so the empty parentheses are its whole argument list. The typing rule below is the one of a class without constructor, and the evaluation rule is the case of a class without base and without constructor. A class with a constructor takes its arguments in the parentheses, and a class with a base also gets the fields of its bases, {bpref "cls_new"}[].

$$`\dfrac{C \mapsto \mathtt{class}\ C\ \{\ldots\} \qquad C \text{ has no constructor}}{\Gamma \vdash \mathtt{new}\ C() : C*}\;\textsf{(T-New)}`

$$`\dfrac{\begin{array}{c} C \mapsto \mathtt{class}\ C\ \{\, \tau_1\, f_1; \ldots; \tau_n\, f_n; \,\} \\ (\ell_i, \sigma_i) = \mathrm{alloc}(\sigma_{i-1}, \mathrm{default}\,\tau_i),\ \sigma_0 = \sigma \\ (\ell, \sigma') = \mathrm{alloc}(\sigma_n, \mathsf{obj}\,C\,[f_1 \mapsto \ell_1, \ldots, f_n \mapsto \ell_n]) \end{array}}{\rho, \sigma \vdash \mathtt{new}\ C() \Rightarrow \mathsf{loc}\,\ell, \sigma'}\;\textsf{(New)}`
:::

:::definition "expr_deref" (parent := "ud2") (lean := "CoreCpp.Typing.lval, CoreCpp.Eval.lval, CoreCpp.Eval.pointee, CoreCpp.Semantics.LHasType, CoreCpp.Semantics.LEval") (uses := "judg_ty_lval, judg_ev_lval, expr_null")
The dereference `*e` denotes the location the pointer holds, with the store the evaluation of $`e` leaves. When the pointer is $`\mathsf{null}` the premise of LocDeref fails, so there is no derivation and the evaluator gives `error`, where C++17 leaves the dereference undefined. A pointer after `delete` denotes a location outside the store, and the read of {bpref "expr_read"}[] has no derivation there.

$$`\dfrac{\Gamma \vdash e : \tau*}{\Gamma \vdash_{\ell} {*e} : \tau}\;\textsf{(T-LocDeref)}`

$$`\dfrac{\rho, \sigma \vdash e \Rightarrow \mathsf{loc}\,\ell, \sigma'}{\rho, \sigma \vdash {*e} \Rightarrow_{\ell} \ell, \sigma'}\;\textsf{(LocDeref)}`
:::

:::definition "expr_field" (parent := "ud2") (lean := "CoreCpp.Typing.lval, CoreCpp.Typing.fieldType, CoreCpp.Program.visibleField, CoreCpp.Eval.lval, CoreCpp.Eval.fieldLoc, CoreCpp.Eval.pointee, CoreCpp.Semantics.LHasType, CoreCpp.Semantics.LEval") (uses := "judg_ty_lval, judg_ev_lval, expr_deref, dom_classes")
The field access `e.f` denotes the location of the field $`f` in the record that $`e` denotes. The access `e->f` denotes the field of the record its pointer holds, as `(*e).f` does, so a null pointer has no derivation and the evaluator gives `error`. The record must be in the store, so an access through a pointer after `delete` has no derivation either. The premise $`C \text{ has } \tau\, f` holds of a field of $`C` or of one of its bases, and a private field must be visible from $`\Gamma`, `Program.visibleField` and {bpref "cls_visible"}[].

$$`\dfrac{\Gamma \vdash e : C \qquad C \text{ has } \tau\, f}{\Gamma \vdash_{\ell} e.f : \tau}\;\textsf{(T-LocField)}`

$$`\dfrac{\Gamma \vdash e : C* \qquad C \text{ has } \tau\, f}{\Gamma \vdash_{\ell} e\mathtt{->}f : \tau}\;\textsf{(T-LocArrow)}`

$$`\dfrac{\rho, \sigma \vdash e \Rightarrow_{\ell} \ell, \sigma' \qquad \sigma'(\ell) = \mathsf{obj}\,C\,[\ldots f \mapsto \ell_f \ldots]}{\rho, \sigma \vdash e.f \Rightarrow_{\ell} \ell_f, \sigma'}\;\textsf{(LocField)}`

$$`\dfrac{\rho, \sigma \vdash e \Rightarrow \mathsf{loc}\,\ell, \sigma' \qquad \sigma'(\ell) = \mathsf{obj}\,C\,[\ldots f \mapsto \ell_f \ldots]}{\rho, \sigma \vdash e\mathtt{->}f \Rightarrow_{\ell} \ell_f, \sigma'}\;\textsf{(LocArrow)}`
:::

:::definition "expr_read" (parent := "ud2") (lean := "CoreCpp.Typing.expr, CoreCpp.Program.visibleField, CoreCpp.Eval.expr, CoreCpp.Eval.readLoc, CoreCpp.Expr.isPlace, CoreCpp.Semantics.HasType, CoreCpp.Semantics.Eval") (uses := "expr_deref, expr_field, std_uses")
Reading `*e`, `e.f`, `e->f` or `e[i]` as a value is reading the content of the location it denotes, one rule for the four forms. A location outside the store has no derivation, and the evaluator gives `error`. Three typing rules give the value the type of the location. The element `v[i]` of a vector takes its location from the library, rule LocIndex of {bpref "std_uses"}[].

$$`\dfrac{\Gamma \vdash e : \tau*}{\Gamma \vdash {*e} : \tau}\;\textsf{(T-Deref)}`

$$`\dfrac{\Gamma \vdash e : C \qquad C \text{ has } \tau\, f}{\Gamma \vdash e.f : \tau}\;\textsf{(T-Field)}`

$$`\dfrac{\Gamma \vdash e : C* \qquad C \text{ has } \tau\, f}{\Gamma \vdash e\mathtt{->}f : \tau}\;\textsf{(T-Arrow)}`

$$`\dfrac{\rho, \sigma \vdash e \Rightarrow_{\ell} \ell, \sigma' \qquad \ell \in \mathrm{dom}\,\sigma'}{\rho, \sigma \vdash e \Rightarrow \sigma'(\ell), \sigma'}\;\textsf{(Read)}, \quad e \in \{{*e'},\ e'.f,\ e'\mathtt{->}f,\ e'[i]\}`
:::
