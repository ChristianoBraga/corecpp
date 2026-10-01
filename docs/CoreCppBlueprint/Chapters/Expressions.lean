import Verso
import VersoManual
import VersoBlueprint
import CoreCpp.Syntax
import CoreCpp.Typing
import CoreCpp.Eval

open Verso.Genre
open Verso.Genre.Manual
open Informal

set_option verso.blueprint.foldCodeBlocks true

#doc (Manual) "Types and expressions" =>

The typing and evaluation rules of the constructions of `Expr`. The typing rules live in `Typing.expr` and `Typing.lval`, the evaluation rules in `Eval.expr` and `Eval.lval`, each in the comment of the case that implements it. The trace of `bin/corecpp trace` cites them by these names.

Where C++17 leaves the evaluation order unspecified, Core C++ evaluates left to right. The last section holds the composite and recursive types, objects and pointers, whose expressions denote locations.

:::group "ud2"
Values, types and expressions.
:::

# Literals

:::definition "expr_lit" (parent := "ud2") (lean := "CoreCpp.Typing.expr, CoreCpp.Eval.expr, CoreCpp.Eval.int32") (uses := "judg_ty_expr, judg_ev_expr, dom_int32")
An integer literal has type `int` and a boolean literal has type `bool`. Evaluation leaves the store unchanged, and the integer literal goes through the range check. The lexer, `Lexer.run`, already rejects a literal above $`2^{31} - 1`, so that check never fails.

$$`\dfrac{}{\Gamma \vdash n : \mathsf{int}}\;\textsf{(T-Lit)}`

$$`\dfrac{}{\Gamma \vdash b : \mathsf{bool}}\;\textsf{(T-BoolLit)}`

$$`\dfrac{}{\rho, \sigma \vdash n \Rightarrow \mathsf{int32}\,n, \sigma}\;\textsf{(Lit)}`

$$`\dfrac{}{\rho, \sigma \vdash b \Rightarrow \mathsf{bool}\,b, \sigma}\;\textsf{(BoolLit)}`

Some of the implementations are `partial`, so Lean records opaque constants that carry the type and not the body, and no property of them is proved here.
:::

# Variable

:::definition "expr_lvar" (parent := "ud2") (lean := "CoreCpp.Typing.lval, CoreCpp.Eval.lval") (uses := "judg_ty_lval, judg_ev_lval")
The variable denotes the location the environment assigns to it. The store does not change. A variable a lambda captures by copy denotes no location, $`\Gamma` marks it read only. Inside a member body an unqualified field of `this` also denotes a location, the rules T-VarField and LocVarField of {bpref "cls_this"}[]. The other location denoting expressions, `*e`, `e.f` and `e->f`, are the nodes of the last section, and an element `v[i]` of a vector is a use of the library, {bpref "std_uses"}[].

$$`\dfrac{\Gamma(x) = \tau \qquad x \text{ not captured}}{\Gamma \vdash_{\ell} x : \tau}\;\textsf{(T-LocVar)}`

$$`\dfrac{\rho(x) = \ell}{\rho, \sigma \vdash x \Rightarrow_{\ell} \ell, \sigma}\;\textsf{(LocVar)}`

The implementations are `partial`, so Lean records opaque constants that carry the type and not the body, and no property of them is proved here.
:::

:::definition "expr_var" (parent := "ud2") (lean := "CoreCpp.Typing.expr, CoreCpp.Eval.expr, CoreCpp.Eval.lval, CoreCpp.Eval.readLoc") (uses := "judg_ty_expr, judg_ev_expr, expr_lvar")
Reading $`x` is reading $`\sigma(\rho(x))`. The location must be live, and `Eval.readLoc` makes a location outside $`\mathrm{dom}\,\sigma` the result `error`.

$$`\dfrac{\Gamma(x) = \tau}{\Gamma \vdash x : \tau}\;\textsf{(T-Var)}`

$$`\dfrac{\rho, \sigma \vdash x \Rightarrow_{\ell} \ell, \sigma \qquad \ell \in \mathrm{dom}\,\sigma}{\rho, \sigma \vdash x \Rightarrow \sigma(\ell), \sigma}\;\textsf{(Var)}`

The implementations are `partial`, so Lean records opaque constants that carry the type and not the body, and no property of them is proved here.
:::

# Unary operators

:::definition "expr_unary" (parent := "ud2") (lean := "CoreCpp.Typing.expr, CoreCpp.Eval.expr, CoreCpp.UnOp, CoreCpp.Eval.unop") (uses := "judg_ty_expr, judg_ev_expr, dom_int32")
Logical negation requires `bool` and arithmetic negation requires `int`. Negation goes through $`\mathsf{int32}`, because the negation of $`-2^{31}` overflows.

$$`\dfrac{\Gamma \vdash e : \mathsf{bool}}{\Gamma \vdash\, !e : \mathsf{bool}}\;\textsf{(T-Not)}`

$$`\dfrac{\Gamma \vdash e : \mathsf{int}}{\Gamma \vdash -e : \mathsf{int}}\;\textsf{(T-Neg)}`

$$`\dfrac{\rho, \sigma \vdash e \Rightarrow \mathsf{bool}\,b, \sigma'}{\rho, \sigma \vdash\, !e \Rightarrow \mathsf{bool}\,\neg b, \sigma'}\;\textsf{(Not)}`

$$`\dfrac{\rho, \sigma \vdash e \Rightarrow \mathsf{int}\,n, \sigma'}{\rho, \sigma \vdash -e \Rightarrow \mathsf{int32}(-n), \sigma'}\;\textsf{(Neg)}`

In the code, the case `unop` of `Eval.expr` evaluates the operand and calls `Eval.unop`.

Some of the implementations are `partial`, so Lean records opaque constants that carry the type and not the body, and no property of them is proved here.
:::

# Binary operators

:::definition "expr_arith" (parent := "ud2") (lean := "CoreCpp.Typing.expr, CoreCpp.Eval.expr, CoreCpp.BinOp, CoreCpp.Eval.binop") (uses := "judg_ty_expr, judg_ev_expr, dom_int32")
The arithmetic operators require `int` on both operands. The left operand is evaluated before the right one. Division and remainder truncate toward zero, as in C++, and a zero divisor is `error`. The quotient of $`-2^{31}` by $`-1` is $`2^{31}`, so $`\mathsf{int32}` makes it `error`. The remainder of $`-2^{31}` by $`-1` is $`0`, where C++17 leaves both results undefined (N4659 §8.6 paragraph 4). A left operand of class type calls a member `operator⊕` instead, the rule T-OpBin of {bpref "op_member"}[].

$$`\dfrac{\Gamma \vdash e_1 : \mathsf{int} \qquad \Gamma \vdash e_2 : \mathsf{int}}{\Gamma \vdash e_1 \oplus e_2 : \mathsf{int}}\;\textsf{(T-Arith)}, \quad \oplus \in \{+, -, *, /, \%\}`

$$`\dfrac{\rho, \sigma \vdash e_1 \Rightarrow \mathsf{int}\,n_1, \sigma_1 \qquad \rho, \sigma_1 \vdash e_2 \Rightarrow \mathsf{int}\,n_2, \sigma_2}{\rho, \sigma \vdash e_1 \oplus e_2 \Rightarrow \mathsf{int32}(n_1 \oplus n_2), \sigma_2}\;\textsf{(Arith)}, \quad \oplus \in \{+, -, *\}`

$$`\dfrac{\begin{array}{c} \rho, \sigma \vdash e_1 \Rightarrow \mathsf{int}\,n_1, \sigma_1 \qquad \rho, \sigma_1 \vdash e_2 \Rightarrow \mathsf{int}\,n_2, \sigma_2 \\ n_2 \neq 0 \end{array}}{\rho, \sigma \vdash e_1 \oslash e_2 \Rightarrow \mathsf{int32}(n_1 \oslash n_2), \sigma_2}\;\textsf{(Div)}, \quad \oslash \in \{/, \%\}`

$$`\dfrac{\rho, \sigma \vdash e_1 \Rightarrow \mathsf{int}\,n_1, \sigma_1 \qquad \rho, \sigma_1 \vdash e_2 \Rightarrow \mathsf{int}\,0, \sigma_2}{\rho, \sigma \vdash e_1 \oslash e_2 \Rightarrow \mathsf{error}}\;\textsf{(DivZero)}`

In the code, the case `binop` of `Eval.expr` evaluates both operands and calls `Eval.binop`.

Some of the implementations are `partial`, so Lean records opaque constants that carry the type and not the body, and no property of them is proved here.
:::

:::definition "expr_rel" (parent := "ud2") (lean := "CoreCpp.Typing.expr, CoreCpp.Eval.expr, CoreCpp.Eval.binop, CoreCpp.Typing.compat, CoreCpp.Typing.related") (uses := "judg_ty_expr, judg_ev_expr")
Equality compares two `int`, two `bool`, two pointers or `nullptr` with a pointer, when $`\tau_1 \approx \tau_2` or $`\tau_2 \approx \tau_1`. A pointer to a derived class thus compares with a pointer to its base, {bpref "cls_subsumption"}[]. Two pointers are equal when they are the same location, and `nullptr` equals only `nullptr`. Order compares two `int`, and there is no order on pointers. The result is `bool`. A left operand of class type calls a member operator, as in {bpref "expr_arith"}[].

$$`\dfrac{\begin{array}{c} \Gamma \vdash e_1 : \tau_1 \qquad \Gamma \vdash e_2 : \tau_2 \qquad \tau_1 \approx \tau_2 \lor \tau_2 \approx \tau_1 \\ \tau_1, \tau_2 \in \{\mathsf{int}, \mathsf{bool}, \tau*, \mathsf{nullptr\_t}\} \end{array}}{\Gamma \vdash e_1 \bowtie e_2 : \mathsf{bool}}\;\textsf{(T-Eq)}, \quad \bowtie \in \{==, \mathrel{!=}\}`

$$`\dfrac{\Gamma \vdash e_1 : \mathsf{int} \qquad \Gamma \vdash e_2 : \mathsf{int}}{\Gamma \vdash e_1 \bowtie e_2 : \mathsf{bool}}\;\textsf{(T-Rel)}, \quad \bowtie \in \{<, <=, >, >=\}`

$$`\dfrac{\rho, \sigma \vdash e_1 \Rightarrow v_1, \sigma_1 \qquad \rho, \sigma_1 \vdash e_2 \Rightarrow v_2, \sigma_2}{\rho, \sigma \vdash e_1 \bowtie e_2 \Rightarrow \mathsf{bool}(v_1 \bowtie v_2), \sigma_2}\;\textsf{(Rel)}`

Some of the implementations are `partial`, so Lean records opaque constants that carry the type and not the body, and no property of them is proved here.
:::

:::definition "expr_logic" (parent := "ud2") (lean := "CoreCpp.Typing.expr, CoreCpp.Eval.expr, CoreCpp.Eval.expectBool") (uses := "judg_ty_expr, judg_ev_expr")
Conjunction and disjunction require `bool` and short circuit. The second operand is evaluated only when the first one does not decide the result.

$$`\dfrac{\Gamma \vdash e_1 : \mathsf{bool} \qquad \Gamma \vdash e_2 : \mathsf{bool}}{\Gamma \vdash e_1 \odot e_2 : \mathsf{bool}}\;\textsf{(T-Logic)}, \quad \odot \in \{\&\&, ||\}`

$$`\dfrac{\rho, \sigma \vdash e_1 \Rightarrow \mathsf{bool}\,\mathtt{false}, \sigma_1}{\rho, \sigma \vdash e_1 \mathbin{\&\&} e_2 \Rightarrow \mathsf{bool}\,\mathtt{false}, \sigma_1}\;\textsf{(And-False)}`

$$`\dfrac{\rho, \sigma \vdash e_1 \Rightarrow \mathsf{bool}\,\mathtt{true}, \sigma_1 \qquad \rho, \sigma_1 \vdash e_2 \Rightarrow v, \sigma_2}{\rho, \sigma \vdash e_1 \mathbin{\&\&} e_2 \Rightarrow v, \sigma_2}\;\textsf{(And-True)}`

$$`\dfrac{\rho, \sigma \vdash e_1 \Rightarrow \mathsf{bool}\,\mathtt{true}, \sigma_1}{\rho, \sigma \vdash e_1 \mathbin{||} e_2 \Rightarrow \mathsf{bool}\,\mathtt{true}, \sigma_1}\;\textsf{(Or-True)}`

$$`\dfrac{\rho, \sigma \vdash e_1 \Rightarrow \mathsf{bool}\,\mathtt{false}, \sigma_1 \qquad \rho, \sigma_1 \vdash e_2 \Rightarrow v, \sigma_2}{\rho, \sigma \vdash e_1 \mathbin{||} e_2 \Rightarrow v, \sigma_2}\;\textsf{(Or-False)}`

In the code, the cases `binop .and` and `binop .or` of `Eval.expr` implement the two pairs of rules.

The implementations are `partial`, so Lean records opaque constants that carry the type and not the body, and no property of them is proved here.
:::

# Conditional

:::definition "expr_cond" (parent := "ud2") (lean := "CoreCpp.Typing.expr, CoreCpp.Typing.value, CoreCpp.Typing.compat, CoreCpp.Eval.expr, CoreCpp.Eval.expectBool") (uses := "judg_ty_expr, judg_ev_expr")
The condition is `bool`. Both branches have types with values, neither `void` nor an object type, and one of them converts to the other by $`\approx`. The type of the conditional is the type of $`e_3` when $`\tau_2 \approx \tau_3`, and the type of $`e_2` otherwise. Only the chosen branch is evaluated.

$$`\dfrac{\begin{array}{c} \Gamma \vdash e_1 : \mathsf{bool} \qquad \Gamma \vdash e_2 : \tau_2 \qquad \Gamma \vdash e_3 : \tau_3 \\ \tau_2, \tau_3 \text{ have values} \qquad \tau = \begin{cases} \tau_3 & \text{if } \tau_2 \approx \tau_3 \\ \tau_2 & \text{else if } \tau_3 \approx \tau_2 \end{cases} \end{array}}{\Gamma \vdash e_1\ ?\ e_2 : e_3 \;:\; \tau}\;\textsf{(T-Cond)}`

$$`\dfrac{\rho, \sigma \vdash e_1 \Rightarrow \mathsf{bool}\,\mathtt{true}, \sigma_1 \qquad \rho, \sigma_1 \vdash e_2 \Rightarrow v, \sigma_2}{\rho, \sigma \vdash e_1\ ?\ e_2 : e_3 \Rightarrow v, \sigma_2}\;\textsf{(Cond-T)}`

$$`\dfrac{\rho, \sigma \vdash e_1 \Rightarrow \mathsf{bool}\,\mathtt{false}, \sigma_1 \qquad \rho, \sigma_1 \vdash e_3 \Rightarrow v, \sigma_2}{\rho, \sigma \vdash e_1\ ?\ e_2 : e_3 \Rightarrow v, \sigma_2}\;\textsf{(Cond-F)}`

The implementations are `partial`, so Lean records opaque constants that carry the type and not the body, and no property of them is proved here.
:::

# Objects and pointers

:::definition "expr_null" (parent := "ud2") (lean := "CoreCpp.Typing.expr, CoreCpp.Eval.expr") (uses := "judg_ty_expr, judg_ev_expr, dom_val")
The literal `nullptr` has the internal type $`\mathsf{nullptr\_t}`, compatible with itself and with every pointer type, and with no other. Its value is $`\mathsf{null}`.

$$`\dfrac{}{\Gamma \vdash \mathtt{nullptr} : \mathsf{nullptr\_t}}\;\textsf{(T-Null)}`

$$`\dfrac{}{\rho, \sigma \vdash \mathtt{nullptr} \Rightarrow \mathsf{null}, \sigma}\;\textsf{(Null)}`

The implementations are `partial`, so Lean records opaque constants that carry the type and not the body, and no property of them is proved here.
:::

:::definition "expr_new" (parent := "ud2") (lean := "CoreCpp.Typing.expr, CoreCpp.Eval.expr, CoreCpp.Store.allocMany, CoreCpp.Ty.default") (uses := "judg_ty_expr, judg_ev_expr, dom_classes, dom_store")
The expression `new C()` allocates one location per field of $`C`, each with the default value of its type, then the record itself, tagged with the class, and evaluates to a pointer to the record. Its type is $`C*`. The default value is $`0` for `int`, `false` for `bool` and $`\mathsf{null}` for a pointer, `Ty.default`. The empty parentheses are the whole argument list for a class without a constructor. The rules below are the case of a class without base and without constructor. A class with a constructor takes its arguments in those parentheses, and a class with a base also gets the fields of its bases, {bpref "cls_new"}[].

$$`\dfrac{C \mapsto \mathtt{class}\ C\ \{\, \tau_1\, f_1; \ldots; \tau_n\, f_n; \,\}}{\Gamma \vdash \mathtt{new}\ C() : C*}\;\textsf{(T-New)}`

$$`\dfrac{\begin{array}{c} C \mapsto \mathtt{class}\ C\ \{\, \tau_1\, f_1; \ldots; \tau_n\, f_n; \,\} \\ (\ell_i, \sigma_i) = \mathrm{alloc}(\sigma_{i-1}, \mathrm{default}\,\tau_i),\ \sigma_0 = \sigma \\ (\ell, \sigma') = \mathrm{alloc}(\sigma_n, \mathsf{obj}\,C\,[f_1 \mapsto \ell_1, \ldots, f_n \mapsto \ell_n]) \end{array}}{\rho, \sigma \vdash \mathtt{new}\ C() \Rightarrow \mathsf{loc}\,\ell, \sigma'}\;\textsf{(New)}`

Some of the implementations are `partial`, so Lean records opaque constants that carry the type and not the body, and no property of them is proved here.
:::

:::definition "expr_deref" (parent := "ud2") (lean := "CoreCpp.Typing.lval, CoreCpp.Eval.lval, CoreCpp.Eval.pointee") (uses := "judg_ty_lval, judg_ev_lval, expr_null")
The dereference `*e` denotes the location the pointer holds. When the pointer is $`\mathsf{null}` the result is `error`, where C++17 leaves the dereference undefined.

$$`\dfrac{\Gamma \vdash e : \tau*}{\Gamma \vdash_{\ell} {*e} : \tau}\;\textsf{(T-LocDeref)}`

$$`\dfrac{\rho, \sigma \vdash e \Rightarrow \mathsf{loc}\,\ell, \sigma'}{\rho, \sigma \vdash {*e} \Rightarrow_{\ell} \ell, \sigma'}\;\textsf{(LocDeref)}`

Some of the implementations are `partial`, so Lean records opaque constants that carry the type and not the body, and no property of them is proved here.
:::

:::definition "expr_field" (parent := "ud2") (lean := "CoreCpp.Typing.lval, CoreCpp.Typing.fieldType, CoreCpp.Eval.lval, CoreCpp.Eval.fieldLoc, CoreCpp.Eval.pointee") (uses := "judg_ty_lval, judg_ev_lval, expr_deref, dom_classes")
The field access `e.f` denotes the location of the field $`f` in the record that $`e` denotes, and `e->f` abbreviates `(*e).f`, so a null pointer is `error`. The type of the field comes from the class table. The premise $`C \text{ has } \tau\, f` holds of a field of $`C` or of one of its bases, and a private field must be visible from $`\Gamma`, {bpref "cls_visible"}[]. A location outside $`\mathrm{dom}\,\sigma'` is `error`, the access through a pointer after `delete`.

$$`\dfrac{\Gamma \vdash e : C \qquad C \text{ has } \tau\, f}{\Gamma \vdash_{\ell} e.f : \tau}\;\textsf{(T-LocField)}`

$$`\dfrac{\Gamma \vdash e : C* \qquad C \text{ has } \tau\, f}{\Gamma \vdash_{\ell} e\mathtt{->}f : \tau}\;\textsf{(T-LocArrow)}`

$$`\dfrac{\rho, \sigma \vdash e \Rightarrow_{\ell} \ell, \sigma' \qquad \sigma'(\ell) = \mathsf{obj}\,C\,[\ldots f \mapsto \ell_f \ldots]}{\rho, \sigma \vdash e.f \Rightarrow_{\ell} \ell_f, \sigma'}\;\textsf{(LocField)}`

$$`\dfrac{\rho, \sigma \vdash e \Rightarrow \mathsf{loc}\,\ell, \sigma' \qquad \sigma'(\ell) = \mathsf{obj}\,C\,[\ldots f \mapsto \ell_f \ldots]}{\rho, \sigma \vdash e\mathtt{->}f \Rightarrow_{\ell} \ell_f, \sigma'}\;\textsf{(LocArrow)}`

The implementations are `partial`, so Lean records opaque constants that carry the type and not the body, and no property of them is proved here.
:::

:::definition "expr_read" (parent := "ud2") (lean := "CoreCpp.Typing.expr, CoreCpp.Eval.expr, CoreCpp.Eval.readLoc") (uses := "expr_deref, expr_field, std_uses")
Reading `*e`, `e.f` or `e->f` as a value is reading the content of the location it denotes, one rule for the three forms. A location outside $`\mathrm{dom}\,\sigma'` is `error`. Three typing rules give the value the type of the location. An element `v[i]` of a vector is a use of the library, {bpref "std_uses"}[].

$$`\dfrac{\Gamma \vdash e : \tau*}{\Gamma \vdash {*e} : \tau}\;\textsf{(T-Deref)}`

$$`\dfrac{\Gamma \vdash e : C \qquad C \text{ has } \tau\, f}{\Gamma \vdash e.f : \tau}\;\textsf{(T-Field)}`

$$`\dfrac{\Gamma \vdash e : C* \qquad C \text{ has } \tau\, f}{\Gamma \vdash e\mathtt{->}f : \tau}\;\textsf{(T-Arrow)}`

$$`\dfrac{\rho, \sigma \vdash e \Rightarrow_{\ell} \ell, \sigma' \qquad \ell \in \mathrm{dom}\,\sigma'}{\rho, \sigma \vdash e \Rightarrow \sigma'(\ell), \sigma'}\;\textsf{(Read)}, \quad e \in \{{*e'},\ e'.f,\ e'\mathtt{->}f\}`

Some of the implementations are `partial`, so Lean records opaque constants that carry the type and not the body, and no property of them is proved here.
:::
