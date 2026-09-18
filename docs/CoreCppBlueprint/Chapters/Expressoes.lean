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

One typing rule and one evaluation rule per construction of `Expr`. The typing rules live in `Typing.expr` and the evaluation rules in `Eval.expr`, each in the comment of the case that implements it. Where C++17 leaves the evaluation order unspecified, Core C++ evaluates left to right.

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
The variable denotes the location the environment assigns to it. The store does not change.

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

:::definition "expr_rel" (parent := "ud2") (lean := "CoreCpp.Typing.expr, CoreCpp.Eval.expr, CoreCpp.Eval.binop") (uses := "judg_ty_expr, judg_ev_expr")
Equality compares two `int` or two `bool`. Order compares two `int`. The result is `bool`.

$$`\dfrac{\begin{array}{c} \Gamma \vdash e_1 : \tau \qquad \Gamma \vdash e_2 : \tau \\ \tau \in \{\mathsf{int}, \mathsf{bool}\} \end{array}}{\Gamma \vdash e_1 \bowtie e_2 : \mathsf{bool}}\;\textsf{(T-Eq)}, \quad \bowtie \in \{==, \mathrel{!=}\}`

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
