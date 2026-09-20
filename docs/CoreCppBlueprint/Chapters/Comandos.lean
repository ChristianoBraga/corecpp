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

#doc (Manual) "UD III, storage and commands" =>

One typing rule and one evaluation rule per construction of `Cmd`. The typing rules live in `Typing.cmd` and the evaluation rules in `Eval.cmd`. Scope is the restoration of $`\rho` at block exit, and lifetime is the removal of the local locations from $`\sigma`. UD III adds the local reference, a second name for an existing location, and fixes the evaluation order of the expressions with effects.

:::group "ud3"
UD III, variables, update and commands.
:::

# Declaration

:::definition "cmd_decl" (parent := "ud3") (lean := "CoreCpp.Typing.cmd, CoreCpp.Eval.cmd") (uses := "judg_ty_cmd, judg_ev_cmd, dom_store")
Every local declaration has an initialiser, by the grammar. It allocates a fresh location and extends $`\rho` for the following commands. With `auto`, $`\tau` is the type of the initialiser.

$$`\dfrac{\Gamma \vdash e : \tau \qquad \tau \neq \mathsf{void}}{\Gamma \vdash \tau\ x = e \dashv \Gamma[x \mapsto \tau]}\;\textsf{(T-Decl)}`

$$`\dfrac{\Gamma \vdash e : \tau \qquad \tau \neq \mathsf{void}}{\Gamma \vdash \mathtt{auto}\ x = e \dashv \Gamma[x \mapsto \tau]}\;\textsf{(T-Auto)}`

$$`\dfrac{\rho, \sigma \vdash e \Rightarrow v, \sigma' \qquad (\ell, \sigma'') = \mathrm{alloc}(\sigma', v)}{\rho, \sigma \vdash \tau\ x = e \Rightarrow \mathsf{normal}, \rho[x \mapsto \ell], \sigma''}\;\textsf{(Decl)}`
:::

# Local reference

:::definition "cmd_declref" (parent := "ud3") (lean := "CoreCpp.Typing.cmd, CoreCpp.Eval.cmd, CoreCpp.Env.alias") (uses := "cmd_decl, judg_ty_lval, judg_ev_lval, dom_env")
The local reference `τ& y = e` binds a second name to the location `e` denotes, without allocating. The initialiser must denote a location and have the declared type, and the reference has in $`\Gamma` the type of its referent, because every read and write through it is a read or write at the referent. The binding is an alias, not owned, so the exit of the block that declared the reference leaves the location in $`\sigma`. A reference to a temporary, to `nullptr` or to an expression without a location does not exist, and a dangling reference is impossible by construction, because a reference names only locations of enclosing blocks or of objects in the store.

$$`\dfrac{\Gamma \vdash_{\ell} e : \tau \qquad \tau \text{ has values}}{\Gamma \vdash \tau\mathtt{\&}\ x = e \dashv \Gamma[x \mapsto \tau]}\;\textsf{(T-DeclRef)}`

$$`\dfrac{\rho, \sigma \vdash e \Rightarrow_{\ell} \ell, \sigma'}{\rho, \sigma \vdash \tau\mathtt{\&}\ x = e \Rightarrow \mathsf{normal}, \rho[x \mapsto \ell], \sigma'}\;\textsf{(DeclRef)}`
:::

# Assignment

:::definition "cmd_assign" (parent := "ud3") (lean := "CoreCpp.Typing.cmd, CoreCpp.Eval.cmd") (uses := "judg_ty_cmd, judg_ev_cmd, expr_lvar")
The left side denotes a location and has the type of the right side. The order is the one C++17 fixes for assignment, the right operand before the left one. The location must be live.

$$`\dfrac{\Gamma \vdash_{\ell} e_1 : \tau \qquad \Gamma \vdash e_2 : \tau}{\Gamma \vdash e_1 = e_2 \dashv \Gamma}\;\textsf{(T-Assign)}`

$$`\dfrac{\begin{array}{c} \rho, \sigma \vdash e_2 \Rightarrow v, \sigma_1 \qquad \rho, \sigma_1 \vdash e_1 \Rightarrow_{\ell} \ell, \sigma_2 \\ \ell \in \mathrm{dom}\,\sigma_2 \end{array}}{\rho, \sigma \vdash e_1 = e_2 \Rightarrow \mathsf{normal}, \rho, \sigma_2[\ell \mapsto v]}\;\textsf{(Assign)}`
:::

# Sequence and block

:::definition "cmd_seq" (parent := "ud3") (lean := "CoreCpp.Typing.cmds, CoreCpp.Eval.cmds") (uses := "judg_ty_cmd, judg_ev_cmd")
The sequence carries the environment from one command to the next. A $`\mathsf{ret}` interrupts the sequence.

$$`\dfrac{}{\Gamma \vdash \varepsilon \dashv \Gamma}\;\textsf{(T-Seq-Empty)}`

$$`\dfrac{\Gamma \vdash c \dashv \Gamma_1 \qquad \Gamma_1 \vdash cs \dashv \Gamma_2}{\Gamma \vdash c\ cs \dashv \Gamma_2}\;\textsf{(T-Seq)}`

$$`\dfrac{}{\rho, \sigma \vdash \varepsilon \Rightarrow \mathsf{normal}, \rho, \sigma}\;\textsf{(Seq-Empty)}`

$$`\dfrac{\rho, \sigma \vdash c \Rightarrow \mathsf{normal}, \rho_1, \sigma_1 \qquad \rho_1, \sigma_1 \vdash cs \Rightarrow r, \rho_2, \sigma_2}{\rho, \sigma \vdash c\ cs \Rightarrow r, \rho_2, \sigma_2}\;\textsf{(Seq)}`

$$`\dfrac{\rho, \sigma \vdash c \Rightarrow \mathsf{ret}\,v, \rho_1, \sigma_1}{\rho, \sigma \vdash c\ cs \Rightarrow \mathsf{ret}\,v, \rho_1, \sigma_1}\;\textsf{(Seq-Ret)}`
:::

:::definition "cmd_block" (parent := "ud3") (lean := "CoreCpp.Typing.cmd, CoreCpp.Eval.cmd, CoreCpp.Eval.fresh") (uses := "cmd_seq, dom_store")
The block discards the extension of $`\rho` and removes from $`\sigma` the locations it allocated. The function `Eval.fresh` computes $`\rho' \setminus \rho` restricted to the owned bindings, so the alias a reference declaration made never frees the location it names. Scope is the restoration of $`\rho`, lifetime is the removal from $`\sigma`.

$$`\dfrac{\Gamma \vdash c_1 \ldots c_n \dashv \Gamma'}{\Gamma \vdash \{\, c_1 \ldots c_n \,\} \dashv \Gamma}\;\textsf{(T-Block)}`

$$`\dfrac{\rho, \sigma \vdash c_1 \ldots c_n \Rightarrow r, \rho', \sigma'}{\rho, \sigma \vdash \{\, c_1 \ldots c_n \,\} \Rightarrow r, \rho, \sigma' \setminus (\rho' \setminus \rho)}\;\textsf{(Block)}`
:::

# Conditional

:::definition "cmd_if" (parent := "ud3") (lean := "CoreCpp.Typing.cmd, CoreCpp.Eval.cmd") (uses := "cmd_block, judg_ev_expr")
Braces are mandatory, and each branch is a block. An `if` without `else` has an empty block as second branch.

$$`\dfrac{\begin{array}{c} \Gamma \vdash e : \mathsf{bool} \qquad \Gamma \vdash \{c_1\} \dashv \Gamma \\ \Gamma \vdash \{c_2\} \dashv \Gamma \end{array}}{\Gamma \vdash \mathtt{if}\ (e)\ \{c_1\}\ \mathtt{else}\ \{c_2\} \dashv \Gamma}\;\textsf{(T-If)}`

$$`\dfrac{\rho, \sigma \vdash e \Rightarrow \mathsf{bool}\,\mathtt{true}, \sigma_1 \qquad \rho, \sigma_1 \vdash \{c_1\} \Rightarrow r, \rho, \sigma_2}{\rho, \sigma \vdash \mathtt{if}\ (e)\ \{c_1\}\ \mathtt{else}\ \{c_2\} \Rightarrow r, \rho, \sigma_2}\;\textsf{(If-T)}`

$$`\dfrac{\rho, \sigma \vdash e \Rightarrow \mathsf{bool}\,\mathtt{false}, \sigma_1 \qquad \rho, \sigma_1 \vdash \{c_2\} \Rightarrow r, \rho, \sigma_2}{\rho, \sigma \vdash \mathtt{if}\ (e)\ \{c_1\}\ \mathtt{else}\ \{c_2\} \Rightarrow r, \rho, \sigma_2}\;\textsf{(If-F)}`
:::

# Loops

:::definition "cmd_while" (parent := "ud3") (lean := "CoreCpp.Typing.cmd, CoreCpp.Eval.cmd") (uses := "cmd_block, judg_ev_expr")
The rule `While-T` recurs on its own conclusion. A `return` in the body interrupts the loop. The divergence of `while (true) {}` has no derivation, a limitation of inductive big step semantics (Leroy and Grall).

$$`\dfrac{\Gamma \vdash e : \mathsf{bool} \qquad \Gamma \vdash \{c\} \dashv \Gamma}{\Gamma \vdash \mathtt{while}\ (e)\ \{c\} \dashv \Gamma}\;\textsf{(T-While)}`

$$`\dfrac{\rho, \sigma \vdash e \Rightarrow \mathsf{bool}\,\mathtt{false}, \sigma_1}{\rho, \sigma \vdash \mathtt{while}\ (e)\ \{c\} \Rightarrow \mathsf{normal}, \rho, \sigma_1}\;\textsf{(While-F)}`

$$`\dfrac{\begin{array}{c} \rho, \sigma \vdash e \Rightarrow \mathsf{bool}\,\mathtt{true}, \sigma_1 \qquad \rho, \sigma_1 \vdash \{c\} \Rightarrow \mathsf{normal}, \rho, \sigma_2 \\ \rho, \sigma_2 \vdash \mathtt{while}\ (e)\ \{c\} \Rightarrow r, \rho, \sigma_3 \end{array}}{\rho, \sigma \vdash \mathtt{while}\ (e)\ \{c\} \Rightarrow r, \rho, \sigma_3}\;\textsf{(While-T)}`

$$`\dfrac{\rho, \sigma \vdash e \Rightarrow \mathsf{bool}\,\mathtt{true}, \sigma_1 \qquad \rho, \sigma_1 \vdash \{c\} \Rightarrow \mathsf{ret}\,v, \rho, \sigma_2}{\rho, \sigma \vdash \mathtt{while}\ (e)\ \{c\} \Rightarrow \mathsf{ret}\,v, \rho, \sigma_2}\;\textsf{(While-Ret)}`
:::

:::definition "cmd_for" (parent := "ud3") (lean := "CoreCpp.Typing.cmd, CoreCpp.Eval.cmd") (uses := "cmd_while, cmd_decl, cmd_block")
The `for` is defined through `while`. The variable of the initialiser has the loop as its scope, the body is a block of its own, and the step runs after the body, outside the body's scope.

$$`\dfrac{\begin{array}{c} \Gamma \vdash c_0 \dashv \Gamma_0 \qquad \Gamma_0 \vdash e : \mathsf{bool} \\ \Gamma_0 \vdash c_s \dashv \Gamma_0 \qquad \Gamma_0 \vdash \{c\} \dashv \Gamma_0 \end{array}}{\Gamma \vdash \mathtt{for}\ (c_0;\, e;\, c_s)\ \{c\} \dashv \Gamma}\;\textsf{(T-For)}`

$$`\dfrac{\begin{array}{c} \rho, \sigma \vdash c_0 \Rightarrow \mathsf{normal}, \rho_0, \sigma_0 \\ \rho_0, \sigma_0 \vdash \mathtt{while}\ (e)\ \{\, \{c\}\ c_s \,\} \Rightarrow r, \rho_0, \sigma_1 \end{array}}{\rho, \sigma \vdash \mathtt{for}\ (c_0;\, e;\, c_s)\ \{c\} \Rightarrow r, \rho, \sigma_1 \setminus (\rho_0 \setminus \rho)}\;\textsf{(For)}`
:::

# Evaluation order

:::definition "eval_order" (parent := "ud3") (lean := "CoreCpp.Eval.expr, CoreCpp.Eval.cmd, CoreCpp.Eval.lval") (uses := "expr_arith, cmd_assign, fun_call")
Once a call inside an expression may write the store, the order in which the operands are evaluated is part of the meaning. Core C++ fixes one order for every construction and the interpreter implements it. In the binary operators, the left operand before the right one, rule `Binary`. In a call, the arguments left to right, rule `Call`. In the assignment, the right side before the left one, rule `Assign`. In the indexing, the vector before the index, rule `LocIndex`. The first two are choices of Core C++ where C++17 fixes no order, the last two are the orders C++17 fixes. For `f() + g()` with effects, C++17 also admits the derivation that evaluates `g()` first, and Core C++ has no such derivation, because `Binary` has one order of premises. The example `call_order.cpp` returns 21 in Core C++, and 21 or 12 under a C++ compiler.
:::

# Expression statement

:::definition "cmd_exprstmt" (parent := "ud3") (lean := "CoreCpp.Typing.cmd, CoreCpp.Eval.cmd") (uses := "judg_ty_cmd, judg_ev_cmd")
An expression followed by `;` is a command that evaluates the expression and discards the value. Any type is accepted, `void` included, which allows a call to a `void` function as a statement.

$$`\dfrac{\Gamma \vdash e : \tau}{\Gamma \vdash e; \dashv \Gamma}\;\textsf{(T-ExprStmt)}`

$$`\dfrac{\rho, \sigma \vdash e \Rightarrow v, \sigma'}{\rho, \sigma \vdash e; \Rightarrow \mathsf{normal}, \rho, \sigma'}\;\textsf{(ExprStmt)}`
:::
