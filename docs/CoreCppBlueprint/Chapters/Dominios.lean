import Verso
import VersoManual
import VersoBlueprint
import CoreCpp.Semantics
import CoreCpp.Typing
import CoreCpp.Eval

open Verso.Genre
open Verso.Genre.Manual
open Informal

set_option verso.blueprint.foldCodeBlocks true

#doc (Manual) "Judgments and domains" =>

Core C++ has three semantic components and four judgments. The typing context $`\Gamma` maps identifiers to types. The environment $`\rho` maps identifiers to locations $`\ell`. The store $`\sigma` maps locations to values, and its domain is the set of live locations. The notation is the sequent style of Kahn (1987). Hypotheses stand left of $`\vdash`, the subject right of it, and the result after $`\Rightarrow`.

:::author "christiano" (name := "Christiano Braga")
:::

:::group "dominios"
Semantic domains, in `CoreCpp/Semantics.lean` and `CoreCpp/Typing.lean`.
:::

:::group "juizos"
The judgments, one Lean function each, in `CoreCpp/Typing.lean` and `CoreCpp/Eval.lean`.
:::

# Domains

:::definition "dom_loc" (parent := "dominios") (lean := "CoreCpp.Loc")
A location $`\ell` is a natural number. Locations are never reused.
:::

:::definition "dom_val" (parent := "dominios") (lean := "CoreCpp.Val") (uses := "dom_int32")
The values are $`\mathsf{int}\,n`, $`\mathsf{bool}\,b` and $`\mathsf{void}`. The value $`\mathsf{void}` is the result of a call to a function without return value and is never stored.
:::

:::definition "dom_int32" (parent := "dominios") (lean := "CoreCpp.Int32.min, CoreCpp.Int32.max, CoreCpp.Int32.inRange")
The type `int` has 32 bits in two's complement. The partial operation $`\mathsf{int32}` returns the integer when it lies in the range and `error` otherwise.

$$`\dfrac{n \in [-2^{31},\, 2^{31}-1]}{\mathsf{int32}\,n = \mathsf{int}\,n} \qquad \dfrac{n \notin [-2^{31},\, 2^{31}-1]}{\mathsf{int32}\,n = \mathsf{error}}`
:::

:::definition "dom_env" (parent := "dominios") (lean := "CoreCpp.Env, CoreCpp.Env.lookup, CoreCpp.Env.extend") (uses := "dom_loc")
The environment $`\rho` is a finite map from identifiers to locations. The notation $`\rho[x \mapsto \ell]` extends $`\rho`, and the most recent binding prevails.
:::

:::definition "dom_store" (parent := "dominios") (lean := "CoreCpp.Store, CoreCpp.Store.read, CoreCpp.Store.write, CoreCpp.Store.alloc, CoreCpp.Store.free, CoreCpp.Store.dom") (uses := "dom_loc, dom_val")
The store $`\sigma` is a finite map from locations to values. The operation $`\mathrm{alloc}(\sigma, v)` returns a fresh location $`\ell \notin \mathrm{dom}\,\sigma` and the store $`\sigma[\ell \mapsto v]`. The operation $`\sigma \setminus L` removes the locations of $`L` from the domain. Reading or writing outside the domain is `error`.
:::

:::definition "dom_ctrl" (parent := "dominios") (lean := "CoreCpp.Ctrl") (uses := "dom_val")
The control result $`r` of a command is $`\mathsf{normal}` or $`\mathsf{ret}\,v`. A $`\mathsf{ret}` interrupts sequence, block and loop up to the call that consumes it.
:::

:::definition "dom_erro" (parent := "dominios") (lean := "CoreCpp.Error")
The result `error` is not a value of the language. It replaces the result of any dynamic judgment and propagates to the whole program. Its causes are division by zero, `int` overflow, a location outside $`\sigma`, an undeclared variable or function, wrong arity and a missing `return` in a non `void` function.
:::

:::definition "dom_tenv" (parent := "dominios") (lean := "CoreCpp.TEnv, CoreCpp.TEnv.lookup")
The typing context $`\Gamma` is a finite map from identifiers to types $`\tau \in \{\mathsf{int}, \mathsf{bool}, \mathsf{void}\}`.
:::

:::definition "dom_funenv" (parent := "dominios") (lean := "CoreCpp.FunEnv, CoreCpp.FunEnv.lookup")
The functions of the program form a finite map from names to declarations. It is fixed during the whole evaluation and stays implicit in the judgments.
:::

# Static judgments

:::definition "judg_ty_expr" (parent := "juizos") (lean := "CoreCpp.Expr, CoreCpp.Typing.expr") (uses := "dom_tenv, gram_ast")
The judgment $`\Gamma \vdash e : \tau` states that the expression $`e` has type $`\tau` in the context $`\Gamma`. One rule per constructor of `Expr`.
:::

:::definition "judg_ty_lval" (parent := "juizos") (lean := "CoreCpp.Typing.lval") (uses := "dom_tenv")
The judgment $`\Gamma \vdash_{\ell} e : \tau` holds for the expressions that denote a location. In the current subset, only the variable.
:::

:::definition "judg_ty_cmd" (parent := "juizos") (lean := "CoreCpp.Cmd, CoreCpp.Typing.cmd, CoreCpp.Typing.cmds") (uses := "judg_ty_expr, gram_ast")
The judgment $`\Gamma \vdash c \dashv \Gamma'` states that the command $`c` is well typed and extends $`\Gamma` to $`\Gamma'`, so that a declaration reaches the following commands of the sequence. The return type $`\tau_r` of the enclosing function is an implicit parameter.
:::

# Dynamic judgments

:::definition "judg_ev_expr" (parent := "juizos") (lean := "CoreCpp.Eval.expr") (uses := "dom_env, dom_store, dom_val, dom_erro")
The judgment $`\rho, \sigma \vdash e \Rightarrow v, \sigma'` states that the expression $`e`, under the environment $`\rho` and the store $`\sigma`, evaluates to $`v` and yields $`\sigma'`. The store enters expressions because a function call inside an expression may change it.
:::

:::definition "judg_ev_lval" (parent := "juizos") (lean := "CoreCpp.Eval.lval") (uses := "dom_env, dom_store, dom_loc")
The judgment $`\rho, \sigma \vdash e \Rightarrow_{\ell} \ell, \sigma'` states that the expression $`e` denotes the location $`\ell`.
:::

:::definition "judg_ev_cmd" (parent := "juizos") (lean := "CoreCpp.Eval.cmd, CoreCpp.Eval.cmds") (uses := "judg_ev_expr, dom_ctrl")
The judgment $`\rho, \sigma \vdash c \Rightarrow r, \rho', \sigma'` states that the command $`c` yields the control $`r`, the environment $`\rho'` and the store $`\sigma'`. The output environment exists so that a declaration extends $`\rho` for the following commands, and the block discards the extension when it ends.
:::

:::definition "judg_trace" (parent := "juizos") (lean := "CoreCpp.M, CoreCpp.TState, CoreCpp.TraceEntry, CoreCpp.Eval.traced, CoreCpp.renderTrace") (uses := "judg_ev_expr, judg_ev_cmd")
The evaluator runs in the monad $`M`, which carries the derivation tree. Each rule application records its conclusion, with the rule name, at the depth of the tree. Premises are recorded before the conclusion, and `bin/corecpp trace` prints the tree in post order, indented by depth.
:::
