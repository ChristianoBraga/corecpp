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

One typing rule and one evaluation rule per construction of `Cmd`. The typing rules live in `Typing.cmd` and the evaluation rules in `Eval.cmd`. Scope is the restoration of $`\rho` at block exit, and lifetime is the removal of the local locations from $`\sigma`.

:::group "ud3"
UD III, variables, update and commands.
:::

# Declaration

:::definition "cmd_decl" (parent := "ud3") (lean := "CoreCpp.Typing.cmd, CoreCpp.Eval.cmd") (uses := "judg_ty_cmd, judg_ev_cmd, dom_store")
Every local declaration has an initialiser, by the grammar. It allocates a fresh location and extends $`\rho` for the following commands. With `auto`, $`\tau` is the type of the initialiser.

$$`\dfrac{\Gamma \vdash e : \tau \qquad \tau \neq \mathsf{void}}{\Gamma \vdash \tau\ x = e \dashv \Gamma[x \mapsto \tau]}\;\textsf{(T-Decl)} \qquad \dfrac{\Gamma \vdash e : \tau \qquad \tau \neq \mathsf{void}}{\Gamma \vdash \mathtt{auto}\ x = e \dashv \Gamma[x \mapsto \tau]}\;\textsf{(T-Auto)}`

$$`\dfrac{\rho, \sigma \vdash e \Rightarrow v, \sigma' \qquad (\ell, \sigma'') = \mathrm{alloc}(\sigma', v)}{\rho, \sigma \vdash \tau\ x = e \Rightarrow \mathsf{normal}, \rho[x \mapsto \ell], \sigma''}\;\textsf{(Decl)}`
:::

# Assignment

:::definition "cmd_assign" (parent := "ud3") (lean := "CoreCpp.Typing.cmd, CoreCpp.Eval.cmd") (uses := "judg_ty_cmd, judg_ev_cmd, expr_lvar")
The left side denotes a location and has the type of the right side. The order is the one C++17 fixes for assignment, the right operand before the left one. The location must be live.

$$`\dfrac{\Gamma \vdash_{\ell} e_1 : \tau \qquad \Gamma \vdash e_2 : \tau}{\Gamma \vdash e_1 = e_2 \dashv \Gamma}\;\textsf{(T-Assign)}`

$$`\dfrac{\rho, \sigma \vdash e_2 \Rightarrow v, \sigma_1 \qquad \rho, \sigma_1 \vdash e_1 \Rightarrow_{\ell} \ell, \sigma_2 \qquad \ell \in \mathrm{dom}\,\sigma_2}{\rho, \sigma \vdash e_1 = e_2 \Rightarrow \mathsf{normal}, \rho, \sigma_2[\ell \mapsto v]}\;\textsf{(Assign)}`
:::

# Sequence and block

:::definition "cmd_seq" (parent := "ud3") (lean := "CoreCpp.Typing.cmds, CoreCpp.Eval.cmds") (uses := "judg_ty_cmd, judg_ev_cmd")
The sequence carries the environment from one command to the next. A $`\mathsf{ret}` interrupts the sequence.

$$`\dfrac{}{\Gamma \vdash \varepsilon \dashv \Gamma}\;\textsf{(T-Seq-Empty)} \qquad \dfrac{\Gamma \vdash c \dashv \Gamma_1 \qquad \Gamma_1 \vdash cs \dashv \Gamma_2}{\Gamma \vdash c\ cs \dashv \Gamma_2}\;\textsf{(T-Seq)}`

$$`\dfrac{}{\rho, \sigma \vdash \varepsilon \Rightarrow \mathsf{normal}, \rho, \sigma}\;\textsf{(Seq-Empty)} \qquad \dfrac{\rho, \sigma \vdash c \Rightarrow \mathsf{normal}, \rho_1, \sigma_1 \qquad \rho_1, \sigma_1 \vdash cs \Rightarrow r, \rho_2, \sigma_2}{\rho, \sigma \vdash c\ cs \Rightarrow r, \rho_2, \sigma_2}\;\textsf{(Seq)}`

$$`\dfrac{\rho, \sigma \vdash c \Rightarrow \mathsf{ret}\,v, \rho_1, \sigma_1}{\rho, \sigma \vdash c\ cs \Rightarrow \mathsf{ret}\,v, \rho_1, \sigma_1}\;\textsf{(Seq-Ret)}`
:::

:::definition "cmd_block" (parent := "ud3") (lean := "CoreCpp.Typing.cmd, CoreCpp.Eval.cmd, CoreCpp.Eval.fresh") (uses := "cmd_seq, dom_store")
The block discards the extension of $`\rho` and removes from $`\sigma` the locations it declared. The function `Eval.fresh` computes $`\rho' \setminus \rho`.

$$`\dfrac{\Gamma \vdash c_1 \ldots c_n \dashv \Gamma'}{\Gamma \vdash \{\, c_1 \ldots c_n \,\} \dashv \Gamma}\;\textsf{(T-Block)} \qquad \dfrac{\rho, \sigma \vdash c_1 \ldots c_n \Rightarrow r, \rho', \sigma'}{\rho, \sigma \vdash \{\, c_1 \ldots c_n \,\} \Rightarrow r, \rho, \sigma' \setminus (\rho' \setminus \rho)}\;\textsf{(Block)}`
:::

# Conditional

:::definition "cmd_if" (parent := "ud3") (lean := "CoreCpp.Typing.cmd, CoreCpp.Eval.cmd") (uses := "cmd_block, judg_ev_expr")
Braces are mandatory, and each branch is a block. An `if` without `else` has an empty block as second branch.

$$`\dfrac{\Gamma \vdash e : \mathsf{bool} \qquad \Gamma \vdash \{c_1\} \dashv \Gamma \qquad \Gamma \vdash \{c_2\} \dashv \Gamma}{\Gamma \vdash \mathtt{if}\ (e)\ \{c_1\}\ \mathtt{else}\ \{c_2\} \dashv \Gamma}\;\textsf{(T-If)}`

$$`\dfrac{\rho, \sigma \vdash e \Rightarrow \mathsf{bool}\,\mathtt{true}, \sigma_1 \qquad \rho, \sigma_1 \vdash \{c_1\} \Rightarrow r, \rho, \sigma_2}{\rho, \sigma \vdash \mathtt{if}\ (e)\ \{c_1\}\ \mathtt{else}\ \{c_2\} \Rightarrow r, \rho, \sigma_2}\;\textsf{(If-T)} \qquad \dfrac{\rho, \sigma \vdash e \Rightarrow \mathsf{bool}\,\mathtt{false}, \sigma_1 \qquad \rho, \sigma_1 \vdash \{c_2\} \Rightarrow r, \rho, \sigma_2}{\rho, \sigma \vdash \mathtt{if}\ (e)\ \{c_1\}\ \mathtt{else}\ \{c_2\} \Rightarrow r, \rho, \sigma_2}\;\textsf{(If-F)}`
:::

# Loops

:::definition "cmd_while" (parent := "ud3") (lean := "CoreCpp.Typing.cmd, CoreCpp.Eval.cmd") (uses := "cmd_block, judg_ev_expr")
The rule `While-T` recurs on its own conclusion. A `return` in the body interrupts the loop. The divergence of `while (true) {}` has no derivation, a limitation of inductive big step semantics (Leroy and Grall).

$$`\dfrac{\Gamma \vdash e : \mathsf{bool} \qquad \Gamma \vdash \{c\} \dashv \Gamma}{\Gamma \vdash \mathtt{while}\ (e)\ \{c\} \dashv \Gamma}\;\textsf{(T-While)}`

$$`\dfrac{\rho, \sigma \vdash e \Rightarrow \mathsf{bool}\,\mathtt{false}, \sigma_1}{\rho, \sigma \vdash \mathtt{while}\ (e)\ \{c\} \Rightarrow \mathsf{normal}, \rho, \sigma_1}\;\textsf{(While-F)}`

$$`\dfrac{\rho, \sigma \vdash e \Rightarrow \mathsf{bool}\,\mathtt{true}, \sigma_1 \qquad \rho, \sigma_1 \vdash \{c\} \Rightarrow \mathsf{normal}, \rho, \sigma_2 \qquad \rho, \sigma_2 \vdash \mathtt{while}\ (e)\ \{c\} \Rightarrow r, \rho, \sigma_3}{\rho, \sigma \vdash \mathtt{while}\ (e)\ \{c\} \Rightarrow r, \rho, \sigma_3}\;\textsf{(While-T)}`

$$`\dfrac{\rho, \sigma \vdash e \Rightarrow \mathsf{bool}\,\mathtt{true}, \sigma_1 \qquad \rho, \sigma_1 \vdash \{c\} \Rightarrow \mathsf{ret}\,v, \rho, \sigma_2}{\rho, \sigma \vdash \mathtt{while}\ (e)\ \{c\} \Rightarrow \mathsf{ret}\,v, \rho, \sigma_2}\;\textsf{(While-Ret)}`
:::

:::definition "cmd_for" (parent := "ud3") (lean := "CoreCpp.Typing.cmd, CoreCpp.Eval.cmd") (uses := "cmd_while, cmd_decl, cmd_block")
The `for` is defined through `while`. The variable of the initialiser has the loop as its scope, the body is a block of its own, and the step runs after the body, outside the body's scope.

$$`\dfrac{\Gamma \vdash c_0 \dashv \Gamma_0 \qquad \Gamma_0 \vdash e : \mathsf{bool} \qquad \Gamma_0 \vdash c_s \dashv \Gamma_0 \qquad \Gamma_0 \vdash \{c\} \dashv \Gamma_0}{\Gamma \vdash \mathtt{for}\ (c_0;\, e;\, c_s)\ \{c\} \dashv \Gamma}\;\textsf{(T-For)}`

$$`\dfrac{\rho, \sigma \vdash c_0 \Rightarrow \mathsf{normal}, \rho_0, \sigma_0 \qquad \rho_0, \sigma_0 \vdash \mathtt{while}\ (e)\ \{\, \{c\}\ c_s \,\} \Rightarrow r, \rho_0, \sigma_1}{\rho, \sigma \vdash \mathtt{for}\ (c_0;\, e;\, c_s)\ \{c\} \Rightarrow r, \rho, \sigma_1 \setminus (\rho_0 \setminus \rho)}\;\textsf{(For)}`
:::

# Expression statement

:::definition "cmd_exprstmt" (parent := "ud3") (lean := "CoreCpp.Typing.cmd, CoreCpp.Eval.cmd") (uses := "judg_ty_cmd, judg_ev_cmd")
An expression followed by `;` is a command that evaluates the expression and discards the value. Any type is accepted, `void` included, which allows a call to a `void` function as a statement.

$$`\dfrac{\Gamma \vdash e : \tau}{\Gamma \vdash e; \dashv \Gamma}\;\textsf{(T-ExprStmt)} \qquad \dfrac{\rho, \sigma \vdash e \Rightarrow v, \sigma'}{\rho, \sigma \vdash e; \Rightarrow \mathsf{normal}, \rho, \sigma'}\;\textsf{(ExprStmt)}`
:::
