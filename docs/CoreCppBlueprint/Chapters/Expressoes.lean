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

#doc (Manual) "UD II, expressions" =>

One typing rule and one evaluation rule per construction of `Expr`. The typing rules live in `Typing.expr` and the evaluation rules in `Eval.expr`, each in the comment of the case that implements it. Where C++17 leaves the evaluation order unspecified, Core C++ evaluates left to right. The second half of the chapter holds the composite and recursive types of UD II, objects, pointers and vectors, whose expressions denote locations.

:::group "ud2"
UD II, values, types and expressions.
:::

# Literals

:::definition "expr_lit" (parent := "ud2") (lean := "CoreCpp.Typing.expr, CoreCpp.Eval.expr, CoreCpp.Eval.int32") (uses := "judg_ty_expr, judg_ev_expr, dom_int32")
An integer literal has type `int` and a boolean literal has type `bool`. Evaluation leaves the store unchanged, and the integer literal goes through the range check.

$$`\dfrac{}{\Gamma \vdash n : \mathsf{int}}\;\textsf{(T-Lit)}`

$$`\dfrac{}{\Gamma \vdash b : \mathsf{bool}}\;\textsf{(T-BoolLit)}`

$$`\dfrac{}{\rho, \sigma \vdash n \Rightarrow \mathsf{int32}\,n, \sigma}\;\textsf{(Lit)}`

$$`\dfrac{}{\rho, \sigma \vdash b \Rightarrow \mathsf{bool}\,b, \sigma}\;\textsf{(BoolLit)}`
:::

# Variable

:::definition "expr_lvar" (parent := "ud2") (lean := "CoreCpp.Typing.lval, CoreCpp.Eval.lval") (uses := "judg_ty_lval, judg_ev_lval")
The variable denotes the location the environment assigns to it. The store does not change. The other location denoting expressions, `*e`, `e.f`, `e->f` and `e[i]`, are the nodes of the second half of this chapter.

$$`\dfrac{\Gamma(x) = \tau}{\Gamma \vdash_{\ell} x : \tau}\;\textsf{(T-LocVar)}`

$$`\dfrac{\rho(x) = \ell}{\rho, \sigma \vdash x \Rightarrow_{\ell} \ell, \sigma}\;\textsf{(LocVar)}`
:::

:::definition "expr_var" (parent := "ud2") (lean := "CoreCpp.Typing.expr, CoreCpp.Eval.expr") (uses := "judg_ty_expr, judg_ev_expr, expr_lvar")
Reading $`x` is reading $`\sigma(\rho(x))`. The location must be live.

$$`\dfrac{\Gamma(x) = \tau}{\Gamma \vdash x : \tau}\;\textsf{(T-Var)}`

$$`\dfrac{\rho, \sigma \vdash x \Rightarrow_{\ell} \ell, \sigma \qquad \ell \in \mathrm{dom}\,\sigma}{\rho, \sigma \vdash x \Rightarrow \sigma(\ell), \sigma}\;\textsf{(Var)}`
:::

# Unary operators

:::definition "expr_unary" (parent := "ud2") (lean := "CoreCpp.Typing.expr, CoreCpp.Eval.expr, CoreCpp.UnOp, CoreCpp.Eval.unop") (uses := "judg_ty_expr, judg_ev_expr, dom_int32")
Logical negation requires `bool` and arithmetic negation requires `int`. Negation goes through $`\mathsf{int32}`, because the negation of $`-2^{31}` overflows.

$$`\dfrac{\Gamma \vdash e : \mathsf{bool}}{\Gamma \vdash\, !e : \mathsf{bool}}\;\textsf{(T-Not)}`

$$`\dfrac{\Gamma \vdash e : \mathsf{int}}{\Gamma \vdash -e : \mathsf{int}}\;\textsf{(T-Neg)}`

$$`\dfrac{\rho, \sigma \vdash e \Rightarrow \mathsf{bool}\,b, \sigma'}{\rho, \sigma \vdash\, !e \Rightarrow \mathsf{bool}\,\neg b, \sigma'}\;\textsf{(Not)}`

$$`\dfrac{\rho, \sigma \vdash e \Rightarrow \mathsf{int}\,n, \sigma'}{\rho, \sigma \vdash -e \Rightarrow \mathsf{int32}(-n), \sigma'}\;\textsf{(Neg)}`

In the code, the case `Unary` of `Eval.expr` evaluates the operand and calls `Eval.unop`.
:::

# Binary operators

:::definition "expr_arith" (parent := "ud2") (lean := "CoreCpp.Typing.expr, CoreCpp.Eval.expr, CoreCpp.BinOp, CoreCpp.Eval.binop") (uses := "judg_ty_expr, judg_ev_expr, dom_int32")
The arithmetic operators require `int` on both operands. The left operand is evaluated before the right one. Division and remainder truncate toward zero, as in C++, and a zero divisor is `error`.

$$`\dfrac{\Gamma \vdash e_1 : \mathsf{int} \qquad \Gamma \vdash e_2 : \mathsf{int}}{\Gamma \vdash e_1 \oplus e_2 : \mathsf{int}}\;\textsf{(T-Arith)}, \quad \oplus \in \{+, -, *, /, \%\}`

$$`\dfrac{\rho, \sigma \vdash e_1 \Rightarrow \mathsf{int}\,n_1, \sigma_1 \qquad \rho, \sigma_1 \vdash e_2 \Rightarrow \mathsf{int}\,n_2, \sigma_2}{\rho, \sigma \vdash e_1 \oplus e_2 \Rightarrow \mathsf{int32}(n_1 \oplus n_2), \sigma_2}\;\textsf{(Arith)}, \quad \oplus \in \{+, -, *\}`

$$`\dfrac{\begin{array}{c} \rho, \sigma \vdash e_1 \Rightarrow \mathsf{int}\,n_1, \sigma_1 \qquad \rho, \sigma_1 \vdash e_2 \Rightarrow \mathsf{int}\,n_2, \sigma_2 \\ n_2 \neq 0 \end{array}}{\rho, \sigma \vdash e_1 \oslash e_2 \Rightarrow \mathsf{int32}(n_1 \oslash n_2), \sigma_2}\;\textsf{(Div)}, \quad \oslash \in \{/, \%\}`

$$`\dfrac{\rho, \sigma \vdash e_1 \Rightarrow \mathsf{int}\,n_1, \sigma_1 \qquad \rho, \sigma_1 \vdash e_2 \Rightarrow \mathsf{int}\,0, \sigma_2}{\rho, \sigma \vdash e_1 \oslash e_2 \Rightarrow \mathsf{error}}\;\textsf{(DivZero)}`

In the code, the case `Binary` of `Eval.expr` evaluates both operands and calls `Eval.binop`.
:::

:::definition "expr_rel" (parent := "ud2") (lean := "CoreCpp.Typing.expr, CoreCpp.Eval.expr, CoreCpp.Eval.binop, CoreCpp.Typing.compat") (uses := "judg_ty_expr, judg_ev_expr")
Equality compares two `int`, two `bool` or two pointers, and `nullptr` against a pointer, the relation $`\tau_1 \approx \tau_2`. Two pointers are equal when they are the same location, and `nullptr` equals only `nullptr`. Order compares two `int`, there is no order on pointers. The result is `bool`.

$$`\dfrac{\begin{array}{c} \Gamma \vdash e_1 : \tau_1 \qquad \Gamma \vdash e_2 : \tau_2 \qquad \tau_1 \approx \tau_2 \\ \tau_1, \tau_2 \in \{\mathsf{int}, \mathsf{bool}, \tau*, \mathsf{nullptr\_t}\} \end{array}}{\Gamma \vdash e_1 \bowtie e_2 : \mathsf{bool}}\;\textsf{(T-Eq)}, \quad \bowtie \in \{==, \mathrel{!=}\}`

$$`\dfrac{\Gamma \vdash e_1 : \mathsf{int} \qquad \Gamma \vdash e_2 : \mathsf{int}}{\Gamma \vdash e_1 \bowtie e_2 : \mathsf{bool}}\;\textsf{(T-Rel)}, \quad \bowtie \in \{<, <=, >, >=\}`

$$`\dfrac{\rho, \sigma \vdash e_1 \Rightarrow v_1, \sigma_1 \qquad \rho, \sigma_1 \vdash e_2 \Rightarrow v_2, \sigma_2}{\rho, \sigma \vdash e_1 \bowtie e_2 \Rightarrow \mathsf{bool}(v_1 \bowtie v_2), \sigma_2}\;\textsf{(Rel)}`
:::

:::definition "expr_logic" (parent := "ud2") (lean := "CoreCpp.Typing.expr, CoreCpp.Eval.expr") (uses := "judg_ty_expr, judg_ev_expr")
Conjunction and disjunction require `bool` and short circuit. The second operand is evaluated only when the first one does not decide the result.

$$`\dfrac{\Gamma \vdash e_1 : \mathsf{bool} \qquad \Gamma \vdash e_2 : \mathsf{bool}}{\Gamma \vdash e_1 \odot e_2 : \mathsf{bool}}\;\textsf{(T-Logic)}, \quad \odot \in \{\&\&, ||\}`

$$`\dfrac{\rho, \sigma \vdash e_1 \Rightarrow \mathsf{bool}\,\mathtt{false}, \sigma_1}{\rho, \sigma \vdash e_1 \mathbin{\&\&} e_2 \Rightarrow \mathsf{bool}\,\mathtt{false}, \sigma_1}\;\textsf{(And-False)}`

$$`\dfrac{\rho, \sigma \vdash e_1 \Rightarrow \mathsf{bool}\,\mathtt{true}, \sigma_1 \qquad \rho, \sigma_1 \vdash e_2 \Rightarrow v, \sigma_2}{\rho, \sigma \vdash e_1 \mathbin{\&\&} e_2 \Rightarrow v, \sigma_2}\;\textsf{(And-True)}`

$$`\dfrac{\rho, \sigma \vdash e_1 \Rightarrow \mathsf{bool}\,\mathtt{true}, \sigma_1}{\rho, \sigma \vdash e_1 \mathbin{||} e_2 \Rightarrow \mathsf{bool}\,\mathtt{true}, \sigma_1}\;\textsf{(Or-True)}`

$$`\dfrac{\rho, \sigma \vdash e_1 \Rightarrow \mathsf{bool}\,\mathtt{false}, \sigma_1 \qquad \rho, \sigma_1 \vdash e_2 \Rightarrow v, \sigma_2}{\rho, \sigma \vdash e_1 \mathbin{||} e_2 \Rightarrow v, \sigma_2}\;\textsf{(Or-False)}`

In the code, the cases `And` and `Or` of `Eval.expr` implement the two pairs of rules.
:::

# Conditional

:::definition "expr_cond" (parent := "ud2") (lean := "CoreCpp.Typing.expr, CoreCpp.Eval.expr") (uses := "judg_ty_expr, judg_ev_expr")
The condition is `bool` and both branches have the same type, other than `void`. Only the chosen branch is evaluated.

$$`\dfrac{\begin{array}{c} \Gamma \vdash e_1 : \mathsf{bool} \qquad \Gamma \vdash e_2 : \tau \\ \Gamma \vdash e_3 : \tau \qquad \tau \neq \mathsf{void} \end{array}}{\Gamma \vdash e_1\ ?\ e_2 : e_3 \;:\; \tau}\;\textsf{(T-Cond)}`

$$`\dfrac{\rho, \sigma \vdash e_1 \Rightarrow \mathsf{bool}\,\mathtt{true}, \sigma_1 \qquad \rho, \sigma_1 \vdash e_2 \Rightarrow v, \sigma_2}{\rho, \sigma \vdash e_1\ ?\ e_2 : e_3 \Rightarrow v, \sigma_2}\;\textsf{(Cond-T)}`

$$`\dfrac{\rho, \sigma \vdash e_1 \Rightarrow \mathsf{bool}\,\mathtt{false}, \sigma_1 \qquad \rho, \sigma_1 \vdash e_3 \Rightarrow v, \sigma_2}{\rho, \sigma \vdash e_1\ ?\ e_2 : e_3 \Rightarrow v, \sigma_2}\;\textsf{(Cond-F)}`
:::

# Objects, pointers and vectors

:::definition "expr_null" (parent := "ud2") (lean := "CoreCpp.Typing.expr, CoreCpp.Eval.expr") (uses := "judg_ty_expr, judg_ev_expr, dom_val")
The literal `nullptr` has the internal type $`\mathsf{nullptr\_t}`, compatible with every pointer type and with no other. Its value is $`\mathsf{null}`.

$$`\dfrac{}{\Gamma \vdash \mathtt{nullptr} : \mathsf{nullptr\_t}}\;\textsf{(T-Null)} \qquad \dfrac{}{\rho, \sigma \vdash \mathtt{nullptr} \Rightarrow \mathsf{null}, \sigma}\;\textsf{(Null)}`
:::

:::definition "expr_new" (parent := "ud2") (lean := "CoreCpp.Typing.expr, CoreCpp.Eval.expr, CoreCpp.Store.allocMany, CoreCpp.Ty.default") (uses := "judg_ty_expr, judg_ev_expr, dom_classes, dom_store")
The expression `new C()` allocates one location per field of $`C`, each with the default value of its type, then the record itself, tagged with the class, and evaluates to a pointer to the record. Its type is $`C*`. The empty parentheses are the whole argument list for a class without a constructor. UD V adds the constructor and its arguments, {bpref "cls_new"}[].

$$`\dfrac{C \mapsto \mathtt{class}\ C\ \{\, \tau_1\, f_1; \ldots; \tau_n\, f_n; \,\}}{\Gamma \vdash \mathtt{new}\ C() : C*}\;\textsf{(T-New)}`

$$`\dfrac{\begin{array}{c} C \mapsto \mathtt{class}\ C\ \{\, \tau_1\, f_1; \ldots; \tau_n\, f_n; \,\} \qquad (\ell_i, \sigma_i) = \mathrm{alloc}(\sigma_{i-1}, \mathrm{default}\,\tau_i),\ \sigma_0 = \sigma \\ (\ell, \sigma') = \mathrm{alloc}(\sigma_n, \mathsf{obj}\,C\,[f_1 \mapsto \ell_1, \ldots, f_n \mapsto \ell_n]) \end{array}}{\rho, \sigma \vdash \mathtt{new}\ C() \Rightarrow \mathsf{loc}\,\ell, \sigma'}\;\textsf{(New)}`
:::

:::definition "expr_newvec" (parent := "ud2") (lean := "CoreCpp.Typing.expr, CoreCpp.Eval.expr, CoreCpp.Typing.storable") (uses := "judg_ty_expr, judg_ev_expr, dom_val, dom_store")
The expression `new std::vector<τ>(n)` evaluates the size, allocates one location per element with the default value of $`\tau`, then the vector record, and evaluates to a pointer to it. A negative size is `error`. The element type has values, so there are no vectors of objects, only of pointers to them.

$$`\dfrac{\Gamma \vdash n : \mathsf{int} \qquad \tau \text{ has values}}{\Gamma \vdash \mathtt{new}\ \mathtt{std{:}{:}vector}\langle\tau\rangle(n) : \mathtt{std{:}{:}vector}\langle\tau\rangle *}\;\textsf{(T-NewVec)}`

$$`\dfrac{\begin{array}{c} \rho, \sigma \vdash n \Rightarrow \mathsf{int}\,k, \sigma_1 \qquad k \ge 0 \qquad (\ell_i, \sigma'_i) = \mathrm{alloc}(\sigma'_{i-1}, \mathrm{default}\,\tau),\ 1 \le i \le k,\ \sigma'_0 = \sigma_1 \\ (\ell, \sigma_2) = \mathrm{alloc}(\sigma'_k, \mathsf{vec}\,[\ell_1, \ldots, \ell_k]) \end{array}}{\rho, \sigma \vdash \mathtt{new}\ \mathtt{std{:}{:}vector}\langle\tau\rangle(n) \Rightarrow \mathsf{loc}\,\ell, \sigma_2}\;\textsf{(NewVec)}`
:::

:::definition "expr_deref" (parent := "ud2") (lean := "CoreCpp.Typing.lval, CoreCpp.Eval.lval, CoreCpp.Eval.pointee") (uses := "judg_ty_lval, judg_ev_lval, expr_null")
The dereference `*e` denotes the location the pointer holds. When the pointer is $`\mathsf{null}` the result is `error`, where C++17 leaves the dereference undefined.

$$`\dfrac{\Gamma \vdash e : \tau*}{\Gamma \vdash_{\ell} {*e} : \tau}\;\textsf{(T-LocDeref)} \qquad \dfrac{\rho, \sigma \vdash e \Rightarrow \mathsf{loc}\,\ell, \sigma'}{\rho, \sigma \vdash {*e} \Rightarrow_{\ell} \ell, \sigma'}\;\textsf{(LocDeref)}`
:::

:::definition "expr_field" (parent := "ud2") (lean := "CoreCpp.Typing.lval, CoreCpp.Typing.fieldType, CoreCpp.Eval.lval, CoreCpp.Eval.fieldLoc") (uses := "judg_ty_lval, judg_ev_lval, expr_deref, dom_classes")
The field access `e.f` denotes the location of the field $`f` in the record that $`e` denotes, and `e->f` abbreviates `(*e).f`, so a null pointer is `error`. The type of the field comes from the class table.

$$`\dfrac{\Gamma \vdash e : C \qquad C \text{ has } \tau\, f}{\Gamma \vdash_{\ell} e.f : \tau}\;\textsf{(T-LocField)} \qquad \dfrac{\Gamma \vdash e : C* \qquad C \text{ has } \tau\, f}{\Gamma \vdash_{\ell} e\mathtt{->}f : \tau}\;\textsf{(T-LocArrow)}`

$$`\dfrac{\rho, \sigma \vdash e \Rightarrow_{\ell} \ell, \sigma' \qquad \sigma'(\ell) = \mathsf{obj}\,C\,[\ldots f \mapsto \ell_f \ldots]}{\rho, \sigma \vdash e.f \Rightarrow_{\ell} \ell_f, \sigma'}\;\textsf{(LocField)}`

$$`\dfrac{\rho, \sigma \vdash e \Rightarrow \mathsf{loc}\,\ell, \sigma' \qquad \sigma'(\ell) = \mathsf{obj}\,C\,[\ldots f \mapsto \ell_f \ldots]}{\rho, \sigma \vdash e\mathtt{->}f \Rightarrow_{\ell} \ell_f, \sigma'}\;\textsf{(LocArrow)}`
:::

:::definition "expr_index" (parent := "ud2") (lean := "CoreCpp.Typing.lval, CoreCpp.Eval.lval") (uses := "judg_ty_lval, judg_ev_lval, expr_deref")
The indexing `e[i]` denotes the location of element $`i` of the vector $`e` denotes. The vector is evaluated before the index, the order C++17 fixes for `operator[]`. An index outside $`[0, n)` is `error`, where C++17 leaves it undefined. This is the completeness principle at work, a vector knows its size and every access is checked.

$$`\dfrac{\Gamma \vdash e : \mathtt{std{:}{:}vector}\langle\tau\rangle \qquad \Gamma \vdash i : \mathsf{int}}{\Gamma \vdash_{\ell} e[i] : \tau}\;\textsf{(T-LocIndex)}`

$$`\dfrac{\begin{array}{c} \rho, \sigma \vdash e \Rightarrow_{\ell} \ell, \sigma_1 \qquad \sigma_1(\ell) = \mathsf{vec}\,[\ell_0, \ldots, \ell_{n-1}] \\ \rho, \sigma_1 \vdash i \Rightarrow \mathsf{int}\,k, \sigma_2 \qquad 0 \le k < n \end{array}}{\rho, \sigma \vdash e[i] \Rightarrow_{\ell} \ell_k, \sigma_2}\;\textsf{(LocIndex)}`
:::

:::definition "expr_read" (parent := "ud2") (lean := "CoreCpp.Typing.expr, CoreCpp.Eval.expr, CoreCpp.Eval.readLoc") (uses := "expr_deref, expr_field, expr_index")
Reading `*e`, `e.f`, `e->f` or `e[i]` as a value is reading the content of the location it denotes, one rule for the four forms. The typing rules `T-Deref`, `T-Field`, `T-Arrow` and `T-Index` give the value the type of the location.

$$`\dfrac{\rho, \sigma \vdash e \Rightarrow_{\ell} \ell, \sigma' \qquad \ell \in \mathrm{dom}\,\sigma'}{\rho, \sigma \vdash e \Rightarrow \sigma'(\ell), \sigma'}\;\textsf{(Read)}, \quad e \in \{{*e'},\ e'.f,\ e'\mathtt{->}f,\ e'[i]\}`
:::
