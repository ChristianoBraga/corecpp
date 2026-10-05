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

#doc (Manual) "Storage and commands" =>

The typing and evaluation rules of the commands, the constructors of `Cmd`. The typing rules are constructors of `Semantics.Check` and `Semantics.Checks`, which `Typing.cmd` and `Typing.cmds` implement. The evaluation rules are constructors of `Semantics.Exec` and `Semantics.Execs`, which `Eval.cmd` and `Eval.cmds` implement, each rule in the comment of the case that implements it. The command `return` has its rules in {bpref "fun_return"}[] and the command `delete` in {bpref "cls_delete"}[].

The typing relation has the result type $`\tau_r` of the enclosing body as a parameter, {bpref "judg_ty_cmd"}[]. The rules of this chapter pass it unchanged to their premises and never read it, so they leave it implicit.

Scope is the restoration of $`\rho` at block exit, and lifetime is the removal of the local locations from $`\sigma`. The chapter also holds the local reference, a second name for an existing location, and the evaluation order of the expressions with effects.

:::group "ud3"
Variables, update and commands.
:::

# Declaration

:::definition "cmd_decl" (parent := "ud3") (lean := "CoreCpp.Typing.cmd, CoreCpp.Typing.storable, CoreCpp.Typing.wellFormed, CoreCpp.Typing.accept, CoreCpp.Typing.value, CoreCpp.TEnv.bind, CoreCpp.Eval.cmd, CoreCpp.Store.alloc, CoreCpp.Env.extend, CoreCpp.Semantics.Storable, CoreCpp.Semantics.HasValues, CoreCpp.Semantics.WF, CoreCpp.Semantics.Accept, CoreCpp.Semantics.Check, CoreCpp.Semantics.Exec") (uses := "judg_ty_cmd, judg_ev_cmd, dom_store, dom_env, dom_tenv, dom_types, fun_accept")
Every local declaration has an initialiser, by the grammar. The declared type is storable and well formed, the predicate $`\mathsf{Storable}` of {bpref "dom_tenv"}[] and the judgment $`\Gamma \vdash \tau\ \mathsf{ok}` of {bpref "dom_types"}[], so no variable has an object type, the type $`\mathsf{nullptr\_t}` or a function type. The initialiser is acceptable at the declared type, the judgment $`\Gamma \vdash e \lhd \tau` of {bpref "fun_accept"}[], which requires of the initialiser a type $`\tau'` with values and $`\tau' \approx \tau`. A variable of type `void` therefore has no initialiser that type checks.

With `auto`, $`\tau` is the type of the initialiser, which has values and is storable.

The declaration evaluates the initialiser, allocates a fresh location with its value, $`(\ell, \sigma'') = \mathrm{alloc}(\sigma', v)` of {bpref "dom_store"}[], and extends $`\rho` with the owned binding $`\rho[x \mapsto \ell]`, `Env.extend`, for the following commands. Evaluation ignores the declared type. The relation states the rule Decl twice, the constructor `decl` for `τ x = e` and the constructor `declAuto` for `auto x = e`.

$$`\dfrac{\mathsf{Storable}(\tau) \qquad \Gamma \vdash \tau\ \mathsf{ok} \qquad \Gamma \vdash e \lhd \tau}{\Gamma \vdash \tau\ x = e \dashv \Gamma[x \mapsto \tau]}\;\textsf{(T-Decl)}`

$$`\dfrac{\Gamma \vdash e : \tau \qquad \mathsf{HasValues}(\tau) \qquad \mathsf{Storable}(\tau)}{\Gamma \vdash \mathtt{auto}\ x = e \dashv \Gamma[x \mapsto \tau]}\;\textsf{(T-Auto)}`

$$`\dfrac{\rho, \sigma \vdash e \Rightarrow v, \sigma' \qquad (\ell, \sigma'') = \mathrm{alloc}(\sigma', v)}{\rho, \sigma \vdash \tau\ x = e \Rightarrow \mathsf{normal}, \rho[x \mapsto \ell], \sigma''}\;\textsf{(Decl)}`

$$`\dfrac{\rho, \sigma \vdash e \Rightarrow v, \sigma' \qquad (\ell, \sigma'') = \mathrm{alloc}(\sigma', v)}{\rho, \sigma \vdash \mathtt{auto}\ x = e \Rightarrow \mathsf{normal}, \rho[x \mapsto \ell], \sigma''}\;\textsf{(Decl)}`
:::

# Local reference

:::definition "cmd_declref" (parent := "ud3") (lean := "CoreCpp.Typing.cmd, CoreCpp.Typing.bindable, CoreCpp.Typing.wellFormed, CoreCpp.Typing.lval, CoreCpp.Eval.cmd, CoreCpp.Eval.lval, CoreCpp.Env.alias, CoreCpp.Semantics.Bindable, CoreCpp.Semantics.WF, CoreCpp.Semantics.LHasType, CoreCpp.Semantics.LEval, CoreCpp.Semantics.Check, CoreCpp.Semantics.Exec") (uses := "cmd_decl, judg_ty_lval, judg_ev_lval, dom_env, dom_tenv, dom_types")
The local reference `τ& x = e` binds a second name to the location `e` denotes, without allocating.

The declared type is bindable by reference and well formed, $`\mathsf{Bindable}_{\mathtt{true}}(\tau)` of {bpref "dom_tenv"}[], so it may be an object type. The initialiser denotes a location of the type $`\tau` itself, with no conversion, so a reference to a base never binds an object of a derived class. The reference has in $`\Gamma` the type of its referent, because every read and write through it is a read or write at the referent.

The binding $`\rho[x \mapsto_{\mathsf{a}} \ell]`, `Env.alias`, is an alias and not owned, so the exit of the block that declared the reference leaves the location in $`\sigma`.

The referent may be an object, as in `C& r = *p;`, since the reference binds its location and copies nothing. A reference to a temporary, to `nullptr` or to an expression without a location does not exist. A reference may still dangle. When `delete` frees an object or a vector, a reference to the object, to one of its fields or to one of its elements names a location outside $`\sigma`. A later read or write through the reference fails a premise $`\ell \in \mathrm{dom}\,\sigma`, so it has no derivation, and the evaluator gives `error` with the exit code 134. C++17 leaves that access undefined.

$$`\dfrac{\mathsf{Bindable}_{\mathtt{true}}(\tau) \qquad \Gamma \vdash \tau\ \mathsf{ok} \qquad \Gamma \vdash_{\ell} e : \tau}{\Gamma \vdash \tau\mathtt{\&}\ x = e \dashv \Gamma[x \mapsto \tau]}\;\textsf{(T-DeclRef)}`

$$`\dfrac{\rho, \sigma \vdash e \Rightarrow_{\ell} \ell, \sigma'}{\rho, \sigma \vdash \tau\mathtt{\&}\ x = e \Rightarrow \mathsf{normal}, \rho[x \mapsto_{\mathsf{a}} \ell], \sigma'}\;\textsf{(DeclRef)}`
:::

# Assignment

:::definition "cmd_assign" (parent := "ud3") (lean := "CoreCpp.Typing.cmd, CoreCpp.Typing.lval, CoreCpp.Typing.value, CoreCpp.Typing.compat, CoreCpp.Eval.cmd, CoreCpp.Eval.lval, CoreCpp.Store.read, CoreCpp.Store.write, CoreCpp.Semantics.HasValues, CoreCpp.Semantics.LHasType, CoreCpp.Semantics.HasType, CoreCpp.Semantics.Check, CoreCpp.Semantics.Exec") (uses := "judg_ty_cmd, judg_ev_cmd, expr_lvar, dom_types, dom_store")
The left side denotes a location whose type has values, and the right side has a type with values that $`\approx` accepts at it, {bpref "dom_types"}[]. An object is never assigned, since an object type has no values. The order is the one C++17 fixes for assignment, the right operand before the left one (N4659 §8.18 paragraph 1). The location must be live, $`\ell \in \mathrm{dom}\,\sigma_2`, so an assignment through a reference that dangles has no derivation.

$$`\dfrac{\begin{array}{c} \Gamma \vdash_{\ell} e_1 : \tau \qquad \mathsf{HasValues}(\tau) \\ \Gamma \vdash e_2 : \tau' \qquad \mathsf{HasValues}(\tau') \qquad \tau' \approx \tau \end{array}}{\Gamma \vdash e_1 = e_2 \dashv \Gamma}\;\textsf{(T-Assign)}`

$$`\dfrac{\begin{array}{c} \rho, \sigma \vdash e_2 \Rightarrow v, \sigma_1 \qquad \rho, \sigma_1 \vdash e_1 \Rightarrow_{\ell} \ell, \sigma_2 \\ \ell \in \mathrm{dom}\,\sigma_2 \end{array}}{\rho, \sigma \vdash e_1 = e_2 \Rightarrow \mathsf{normal}, \rho, \sigma_2[\ell \mapsto v]}\;\textsf{(Assign)}`
:::

# Sequence and block

:::definition "cmd_seq" (parent := "ud3") (lean := "CoreCpp.Typing.cmds, CoreCpp.Eval.cmds, CoreCpp.Semantics.Checks, CoreCpp.Semantics.Execs") (uses := "judg_ty_cmd, judg_ev_cmd, dom_ctrl")
The sequence carries the environment from one command to the next. A $`\mathsf{ret}` interrupts the sequence, and the commands after it do not run.

$$`\dfrac{}{\Gamma \vdash \varepsilon \dashv \Gamma}\;\textsf{(T-Seq-Empty)}`

$$`\dfrac{\Gamma \vdash c \dashv \Gamma_1 \qquad \Gamma_1 \vdash cs \dashv \Gamma_2}{\Gamma \vdash c\ cs \dashv \Gamma_2}\;\textsf{(T-Seq)}`

$$`\dfrac{}{\rho, \sigma \vdash \varepsilon \Rightarrow \mathsf{normal}, \rho, \sigma}\;\textsf{(Seq-Empty)}`

$$`\dfrac{\rho, \sigma \vdash c \Rightarrow \mathsf{normal}, \rho_1, \sigma_1 \qquad \rho_1, \sigma_1 \vdash cs \Rightarrow r, \rho_2, \sigma_2}{\rho, \sigma \vdash c\ cs \Rightarrow r, \rho_2, \sigma_2}\;\textsf{(Seq)}`

$$`\dfrac{\rho, \sigma \vdash c \Rightarrow \mathsf{ret}\,v, \rho_1, \sigma_1}{\rho, \sigma \vdash c\ cs \Rightarrow \mathsf{ret}\,v, \rho_1, \sigma_1}\;\textsf{(Seq-Ret)}`
:::

:::definition "cmd_block" (parent := "ud3") (lean := "CoreCpp.Typing.cmd, CoreCpp.Eval.cmd, CoreCpp.Eval.fresh, CoreCpp.Env.fresh, CoreCpp.Store.free, CoreCpp.Semantics.Check, CoreCpp.Semantics.Exec") (uses := "cmd_seq, dom_store, dom_env")
The block discards the extension of $`\rho` and removes from $`\sigma` the locations it allocated. The set $`\mathrm{fresh}(\rho, \rho')`, `Env.fresh`, holds the locations of the owned bindings of $`\rho'` that $`\rho` does not have, so the alias a reference declaration made never frees the location it names. The evaluator computes the same set with `Eval.fresh`. Scope is the restoration of $`\rho`, lifetime is the removal from $`\sigma`.

$$`\dfrac{\Gamma \vdash c_1 \ldots c_n \dashv \Gamma'}{\Gamma \vdash \{\, c_1 \ldots c_n \,\} \dashv \Gamma}\;\textsf{(T-Block)}`

$$`\dfrac{\rho, \sigma \vdash c_1 \ldots c_n \Rightarrow r, \rho', \sigma'}{\rho, \sigma \vdash \{\, c_1 \ldots c_n \,\} \Rightarrow r, \rho, \sigma' \setminus \mathrm{fresh}(\rho, \rho')}\;\textsf{(Block)}`
:::

# Conditional

:::definition "cmd_if" (parent := "ud3") (lean := "CoreCpp.Typing.cmd, CoreCpp.Eval.cmd, CoreCpp.Eval.expectBool, CoreCpp.Semantics.Check, CoreCpp.Semantics.Exec") (uses := "cmd_block, judg_ev_expr")
Braces are mandatory, and each branch is a block. An `if` without `else` has an empty block as second branch. The condition is evaluated first, and only the chosen branch runs.

$$`\dfrac{\begin{array}{c} \Gamma \vdash e : \mathsf{bool} \qquad \Gamma \vdash \{c_1\} \dashv \Gamma \\ \Gamma \vdash \{c_2\} \dashv \Gamma \end{array}}{\Gamma \vdash \mathtt{if}\ (e)\ \{c_1\}\ \mathtt{else}\ \{c_2\} \dashv \Gamma}\;\textsf{(T-If)}`

$$`\dfrac{\rho, \sigma \vdash e \Rightarrow \mathsf{bool}\,\mathtt{true}, \sigma_1 \qquad \rho, \sigma_1 \vdash \{c_1\} \Rightarrow r, \rho, \sigma_2}{\rho, \sigma \vdash \mathtt{if}\ (e)\ \{c_1\}\ \mathtt{else}\ \{c_2\} \Rightarrow r, \rho, \sigma_2}\;\textsf{(If-T)}`

$$`\dfrac{\rho, \sigma \vdash e \Rightarrow \mathsf{bool}\,\mathtt{false}, \sigma_1 \qquad \rho, \sigma_1 \vdash \{c_2\} \Rightarrow r, \rho, \sigma_2}{\rho, \sigma \vdash \mathtt{if}\ (e)\ \{c_1\}\ \mathtt{else}\ \{c_2\} \Rightarrow r, \rho, \sigma_2}\;\textsf{(If-F)}`
:::

# Loops

:::definition "cmd_while" (parent := "ud3") (lean := "CoreCpp.Typing.cmd, CoreCpp.Eval.cmd, CoreCpp.Eval.expectBool, CoreCpp.Semantics.Check, CoreCpp.Semantics.Exec") (uses := "cmd_block, judg_ev_expr, dom_ctrl")
The rule While-T recurs on its own conclusion. A `return` in the body interrupts the loop, rule While-Ret. The divergence of `while (true) {}` has no derivation, a limitation of inductive big step semantics (Kahn, RR-0601, §4.4, p. 11).

$$`\dfrac{\Gamma \vdash e : \mathsf{bool} \qquad \Gamma \vdash \{c\} \dashv \Gamma}{\Gamma \vdash \mathtt{while}\ (e)\ \{c\} \dashv \Gamma}\;\textsf{(T-While)}`

$$`\dfrac{\rho, \sigma \vdash e \Rightarrow \mathsf{bool}\,\mathtt{false}, \sigma_1}{\rho, \sigma \vdash \mathtt{while}\ (e)\ \{c\} \Rightarrow \mathsf{normal}, \rho, \sigma_1}\;\textsf{(While-F)}`

$$`\dfrac{\begin{array}{c} \rho, \sigma \vdash e \Rightarrow \mathsf{bool}\,\mathtt{true}, \sigma_1 \qquad \rho, \sigma_1 \vdash \{c\} \Rightarrow \mathsf{normal}, \rho, \sigma_2 \\ \rho, \sigma_2 \vdash \mathtt{while}\ (e)\ \{c\} \Rightarrow r, \rho, \sigma_3 \end{array}}{\rho, \sigma \vdash \mathtt{while}\ (e)\ \{c\} \Rightarrow r, \rho, \sigma_3}\;\textsf{(While-T)}`

$$`\dfrac{\rho, \sigma \vdash e \Rightarrow \mathsf{bool}\,\mathtt{true}, \sigma_1 \qquad \rho, \sigma_1 \vdash \{c\} \Rightarrow \mathsf{ret}\,v, \rho, \sigma_2}{\rho, \sigma \vdash \mathtt{while}\ (e)\ \{c\} \Rightarrow \mathsf{ret}\,v, \rho, \sigma_2}\;\textsf{(While-Ret)}`
:::

:::definition "cmd_for" (parent := "ud3") (lean := "CoreCpp.Typing.cmd, CoreCpp.Eval.cmd, CoreCpp.Eval.fresh, CoreCpp.Env.fresh, CoreCpp.Semantics.Check, CoreCpp.Semantics.Exec") (uses := "cmd_while, cmd_decl, cmd_block")
The `for` is defined through `while`. The variable of the initialiser has the loop as its scope, and the loop frees its location at exit, $`\mathrm{fresh}(\rho, \rho_0)` of {bpref "cmd_block"}[]. The body is a block of its own, and the step runs after the body, outside the body's scope. The step is checked under $`\Gamma_0`, and its context $`\Gamma_s` is discarded. The initialiser ends with $`\mathsf{normal}`.

$$`\dfrac{\begin{array}{c} \Gamma \vdash c_0 \dashv \Gamma_0 \qquad \Gamma_0 \vdash e : \mathsf{bool} \\ \Gamma_0 \vdash c_s \dashv \Gamma_s \qquad \Gamma_0 \vdash \{c\} \dashv \Gamma_0 \end{array}}{\Gamma \vdash \mathtt{for}\ (c_0;\, e;\, c_s)\ \{c\} \dashv \Gamma}\;\textsf{(T-For)}`

$$`\dfrac{\begin{array}{c} \rho, \sigma \vdash c_0 \Rightarrow \mathsf{normal}, \rho_0, \sigma_0 \\ \rho_0, \sigma_0 \vdash \mathtt{while}\ (e)\ \{\, \{c\}\ c_s \,\} \Rightarrow r, \rho_0, \sigma_1 \end{array}}{\rho, \sigma \vdash \mathtt{for}\ (c_0;\, e;\, c_s)\ \{c\} \Rightarrow r, \rho, \sigma_1 \setminus \mathrm{fresh}(\rho, \rho_0)}\;\textsf{(For)}`
:::

# Evaluation order

:::definition "eval_order" (parent := "ud3") (lean := "CoreCpp.Eval.expr, CoreCpp.Eval.cmd, CoreCpp.Eval.lval, CoreCpp.Semantics.Eval, CoreCpp.Semantics.LEval, CoreCpp.Semantics.Exec, CoreCpp.Semantics.Bind") (uses := "expr_arith, expr_rel, cmd_assign, fun_call, std_uses")
Once a call inside an expression may write the store, the order in which the operands are evaluated is part of the meaning. Core C++ fixes one order for every construction, and each rule states it by the order of its premises, the store of one premise being the input of the next.

 * In the arithmetic and relational operators, the left operand before the right one, rules Arith, Div and Rel.
 * In a call, the arguments left to right, rule Call through the relation `Bind`.
 * In the assignment, the right side before the left one, rule Assign.
 * In the indexing of a vector, the receiver before the index, rule LocIndex.

The first two are choices of Core C++ where C++17 fixes no order, the last two are the orders C++17 fixes, for the assignment (N4659 §8.18 paragraph 1) and for the subscript (N4659 §8.2.1 paragraph 1), which an overloaded `operator[]` keeps (N4659 §16.3.1.2 paragraph 2). For `f() + g()` with effects, C++17 also admits the evaluation of `g()` first, and Core C++ has no such derivation, because Arith has one order of premises. The example `call_order.cpp` returns 21 in Core C++, and 21 or 12 under a C++ compiler.
:::

# Expression statement

:::definition "cmd_exprstmt" (parent := "ud3") (lean := "CoreCpp.Typing.cmd, CoreCpp.Eval.cmd, CoreCpp.Semantics.Check, CoreCpp.Semantics.Exec") (uses := "judg_ty_cmd, judg_ev_cmd")
An expression followed by `;` is a command that evaluates the expression and discards the value. Any type is accepted, `void` included, which allows a call to a `void` function as a statement.

$$`\dfrac{\Gamma \vdash e : \tau}{\Gamma \vdash e; \dashv \Gamma}\;\textsf{(T-ExprStmt)}`

$$`\dfrac{\rho, \sigma \vdash e \Rightarrow v, \sigma'}{\rho, \sigma \vdash e; \Rightarrow \mathsf{normal}, \rho, \sigma'}\;\textsf{(ExprStmt)}`
:::

# Rules of the chapter

Every typing rule and every evaluation rule of this chapter, in the order of its sections, the typing rules of each section before its evaluation rules. Each rule is stated with its explanation, and with the definition of its notation, in the section named above it.

*Declaration*

$$`\dfrac{\mathsf{Storable}(\tau) \qquad \Gamma \vdash \tau\ \mathsf{ok} \qquad \Gamma \vdash e \lhd \tau}{\Gamma \vdash \tau\ x = e \dashv \Gamma[x \mapsto \tau]}\;\textsf{(T-Decl)}`

$$`\dfrac{\Gamma \vdash e : \tau \qquad \mathsf{HasValues}(\tau) \qquad \mathsf{Storable}(\tau)}{\Gamma \vdash \mathtt{auto}\ x = e \dashv \Gamma[x \mapsto \tau]}\;\textsf{(T-Auto)}`

 

$$`\dfrac{\rho, \sigma \vdash e \Rightarrow v, \sigma' \qquad (\ell, \sigma'') = \mathrm{alloc}(\sigma', v)}{\rho, \sigma \vdash \tau\ x = e \Rightarrow \mathsf{normal}, \rho[x \mapsto \ell], \sigma''}\;\textsf{(Decl)}`

$$`\dfrac{\rho, \sigma \vdash e \Rightarrow v, \sigma' \qquad (\ell, \sigma'') = \mathrm{alloc}(\sigma', v)}{\rho, \sigma \vdash \mathtt{auto}\ x = e \Rightarrow \mathsf{normal}, \rho[x \mapsto \ell], \sigma''}\;\textsf{(Decl)}`

*Local reference*

$$`\dfrac{\mathsf{Bindable}_{\mathtt{true}}(\tau) \qquad \Gamma \vdash \tau\ \mathsf{ok} \qquad \Gamma \vdash_{\ell} e : \tau}{\Gamma \vdash \tau\mathtt{\&}\ x = e \dashv \Gamma[x \mapsto \tau]}\;\textsf{(T-DeclRef)}`

 

$$`\dfrac{\rho, \sigma \vdash e \Rightarrow_{\ell} \ell, \sigma'}{\rho, \sigma \vdash \tau\mathtt{\&}\ x = e \Rightarrow \mathsf{normal}, \rho[x \mapsto_{\mathsf{a}} \ell], \sigma'}\;\textsf{(DeclRef)}`

*Assignment*

$$`\dfrac{\begin{array}{c} \Gamma \vdash_{\ell} e_1 : \tau \qquad \mathsf{HasValues}(\tau) \\ \Gamma \vdash e_2 : \tau' \qquad \mathsf{HasValues}(\tau') \qquad \tau' \approx \tau \end{array}}{\Gamma \vdash e_1 = e_2 \dashv \Gamma}\;\textsf{(T-Assign)}`

 

$$`\dfrac{\begin{array}{c} \rho, \sigma \vdash e_2 \Rightarrow v, \sigma_1 \qquad \rho, \sigma_1 \vdash e_1 \Rightarrow_{\ell} \ell, \sigma_2 \\ \ell \in \mathrm{dom}\,\sigma_2 \end{array}}{\rho, \sigma \vdash e_1 = e_2 \Rightarrow \mathsf{normal}, \rho, \sigma_2[\ell \mapsto v]}\;\textsf{(Assign)}`

*Sequence and block*

$$`\dfrac{}{\Gamma \vdash \varepsilon \dashv \Gamma}\;\textsf{(T-Seq-Empty)}`

$$`\dfrac{\Gamma \vdash c \dashv \Gamma_1 \qquad \Gamma_1 \vdash cs \dashv \Gamma_2}{\Gamma \vdash c\ cs \dashv \Gamma_2}\;\textsf{(T-Seq)}`

$$`\dfrac{\Gamma \vdash c_1 \ldots c_n \dashv \Gamma'}{\Gamma \vdash \{\, c_1 \ldots c_n \,\} \dashv \Gamma}\;\textsf{(T-Block)}`

 

$$`\dfrac{}{\rho, \sigma \vdash \varepsilon \Rightarrow \mathsf{normal}, \rho, \sigma}\;\textsf{(Seq-Empty)}`

$$`\dfrac{\rho, \sigma \vdash c \Rightarrow \mathsf{normal}, \rho_1, \sigma_1 \qquad \rho_1, \sigma_1 \vdash cs \Rightarrow r, \rho_2, \sigma_2}{\rho, \sigma \vdash c\ cs \Rightarrow r, \rho_2, \sigma_2}\;\textsf{(Seq)}`

$$`\dfrac{\rho, \sigma \vdash c \Rightarrow \mathsf{ret}\,v, \rho_1, \sigma_1}{\rho, \sigma \vdash c\ cs \Rightarrow \mathsf{ret}\,v, \rho_1, \sigma_1}\;\textsf{(Seq-Ret)}`

$$`\dfrac{\rho, \sigma \vdash c_1 \ldots c_n \Rightarrow r, \rho', \sigma'}{\rho, \sigma \vdash \{\, c_1 \ldots c_n \,\} \Rightarrow r, \rho, \sigma' \setminus \mathrm{fresh}(\rho, \rho')}\;\textsf{(Block)}`

*Conditional*

$$`\dfrac{\begin{array}{c} \Gamma \vdash e : \mathsf{bool} \qquad \Gamma \vdash \{c_1\} \dashv \Gamma \\ \Gamma \vdash \{c_2\} \dashv \Gamma \end{array}}{\Gamma \vdash \mathtt{if}\ (e)\ \{c_1\}\ \mathtt{else}\ \{c_2\} \dashv \Gamma}\;\textsf{(T-If)}`

 

$$`\dfrac{\rho, \sigma \vdash e \Rightarrow \mathsf{bool}\,\mathtt{true}, \sigma_1 \qquad \rho, \sigma_1 \vdash \{c_1\} \Rightarrow r, \rho, \sigma_2}{\rho, \sigma \vdash \mathtt{if}\ (e)\ \{c_1\}\ \mathtt{else}\ \{c_2\} \Rightarrow r, \rho, \sigma_2}\;\textsf{(If-T)}`

$$`\dfrac{\rho, \sigma \vdash e \Rightarrow \mathsf{bool}\,\mathtt{false}, \sigma_1 \qquad \rho, \sigma_1 \vdash \{c_2\} \Rightarrow r, \rho, \sigma_2}{\rho, \sigma \vdash \mathtt{if}\ (e)\ \{c_1\}\ \mathtt{else}\ \{c_2\} \Rightarrow r, \rho, \sigma_2}\;\textsf{(If-F)}`

*Loops*

$$`\dfrac{\Gamma \vdash e : \mathsf{bool} \qquad \Gamma \vdash \{c\} \dashv \Gamma}{\Gamma \vdash \mathtt{while}\ (e)\ \{c\} \dashv \Gamma}\;\textsf{(T-While)}`

$$`\dfrac{\begin{array}{c} \Gamma \vdash c_0 \dashv \Gamma_0 \qquad \Gamma_0 \vdash e : \mathsf{bool} \\ \Gamma_0 \vdash c_s \dashv \Gamma_s \qquad \Gamma_0 \vdash \{c\} \dashv \Gamma_0 \end{array}}{\Gamma \vdash \mathtt{for}\ (c_0;\, e;\, c_s)\ \{c\} \dashv \Gamma}\;\textsf{(T-For)}`

 

$$`\dfrac{\rho, \sigma \vdash e \Rightarrow \mathsf{bool}\,\mathtt{false}, \sigma_1}{\rho, \sigma \vdash \mathtt{while}\ (e)\ \{c\} \Rightarrow \mathsf{normal}, \rho, \sigma_1}\;\textsf{(While-F)}`

$$`\dfrac{\begin{array}{c} \rho, \sigma \vdash e \Rightarrow \mathsf{bool}\,\mathtt{true}, \sigma_1 \qquad \rho, \sigma_1 \vdash \{c\} \Rightarrow \mathsf{normal}, \rho, \sigma_2 \\ \rho, \sigma_2 \vdash \mathtt{while}\ (e)\ \{c\} \Rightarrow r, \rho, \sigma_3 \end{array}}{\rho, \sigma \vdash \mathtt{while}\ (e)\ \{c\} \Rightarrow r, \rho, \sigma_3}\;\textsf{(While-T)}`

$$`\dfrac{\rho, \sigma \vdash e \Rightarrow \mathsf{bool}\,\mathtt{true}, \sigma_1 \qquad \rho, \sigma_1 \vdash \{c\} \Rightarrow \mathsf{ret}\,v, \rho, \sigma_2}{\rho, \sigma \vdash \mathtt{while}\ (e)\ \{c\} \Rightarrow \mathsf{ret}\,v, \rho, \sigma_2}\;\textsf{(While-Ret)}`

$$`\dfrac{\begin{array}{c} \rho, \sigma \vdash c_0 \Rightarrow \mathsf{normal}, \rho_0, \sigma_0 \\ \rho_0, \sigma_0 \vdash \mathtt{while}\ (e)\ \{\, \{c\}\ c_s \,\} \Rightarrow r, \rho_0, \sigma_1 \end{array}}{\rho, \sigma \vdash \mathtt{for}\ (c_0;\, e;\, c_s)\ \{c\} \Rightarrow r, \rho, \sigma_1 \setminus \mathrm{fresh}(\rho, \rho_0)}\;\textsf{(For)}`

*Expression statement*

$$`\dfrac{\Gamma \vdash e : \tau}{\Gamma \vdash e; \dashv \Gamma}\;\textsf{(T-ExprStmt)}`

 

$$`\dfrac{\rho, \sigma \vdash e \Rightarrow v, \sigma'}{\rho, \sigma \vdash e; \Rightarrow \mathsf{normal}, \rho, \sigma'}\;\textsf{(ExprStmt)}`
