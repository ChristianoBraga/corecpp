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

#doc (Manual) "Abstraction" =>

Functions with parameters by value and by reference, `return` as a control result, lambdas with capture by copy, function values of type `std::function`, and the program. The call evaluates the arguments left to right, allocates a fresh location with a copy for each parameter by value, binds each parameter by reference to the location of its argument, and removes the copies from $`\sigma` on return.

:::group "ud4"
Functions, parameters and calls.
:::

# Call

:::definition "fun_call" (parent := "ud4") (lean := "CoreCpp.Typing.expr, CoreCpp.Eval.expr, CoreCpp.Fun, CoreCpp.Param") (uses := "judg_ty_expr, judg_ev_expr, cmd_seq, dom_funenv, dom_store")
Let $`f \mapsto \tau\ f(\tau_1\,x_1, \ldots, \tau_k\,x_k)\ \{c\}` be in the program. The environment of the function holds only the parameters, because there are no global variables.

Each argument is checked at the type of its parameter by the judgment $`\Gamma \vdash e \lhd \tau` of {bpref "fun_accept"}[], so that a lambda may be an argument. A variable `f` of function type in $`\Gamma` hides the function named `f`, and the call is then {bpref "fun_callfn"}[].

$$`\dfrac{f \notin \Gamma \qquad \Gamma \vdash e_i \lhd \tau_i \quad (1 \le i \le k)}{\Gamma \vdash f(e_1, \ldots, e_k) : \tau}\;\textsf{(T-Call)}`

$$`\dfrac{\begin{array}{c} \rho, \sigma_{i-1} \vdash e_i \Rightarrow v_i, \sigma_i \quad (1 \le i \le k,\ \sigma_0 = \sigma) \\ (\ell_i, \sigma'_i) = \mathrm{alloc}(\sigma'_{i-1}, v_i) \quad (1 \le i \le k,\ \sigma'_0 = \sigma_k) \\ [x_1 \mapsto \ell_1, \ldots, x_k \mapsto \ell_k], \sigma'_k \vdash c \Rightarrow \mathsf{ret}\,v, \rho', \sigma'' \end{array}}{\rho, \sigma \vdash f(e_1, \ldots, e_k) \Rightarrow v, \sigma'' \setminus (\{\ell_1, \ldots, \ell_k\} \cup (\rho' \setminus \rho_f))}\;\textsf{(Call)}`

The return frees the copies of the arguments and the locals the body declared, $`\rho' \setminus \rho_f` read as the owned bindings the body added, so after a call the store holds only what existed before it and the objects created with `new`. When the body ends with $`\mathsf{normal}`, the result is $`\mathsf{void}` if $`\tau = \mathsf{void}` and `error` otherwise. A missing `return` in a non `void` function is an evaluation `error`, not a type error. The rule above is the case in which every parameter is by value, and {bpref "param_ref"}[] gives the case of a parameter by reference.
:::

# Parameters by reference

:::definition "param_ref" (parent := "ud4") (lean := "CoreCpp.Param, CoreCpp.Typing.expr, CoreCpp.Eval.expr, CoreCpp.Env.alias") (uses := "fun_call, judg_ty_lval, judg_ev_lval, dom_env")
A parameter $`\tau_j\&\ x_j` receives the location of its argument, which must denote a location of exactly the type $`\tau_j`. The binding of $`x_j` in the function environment is an alias, as in a local reference, and the return does not free it. In $`\Gamma` the parameter has the type of its referent.

$$`\dfrac{f \notin \Gamma \qquad \Gamma \vdash e_i \lhd \tau_i \ \text{for each } p_i = \tau_i \qquad \Gamma \vdash_{\ell} e_j : \tau_j \ \text{for each } p_j = \tau_j\&}{\Gamma \vdash f(e_1, \ldots, e_k) : \tau}\;\textsf{(T-Call)}`

$$`\dfrac{\begin{array}{c} \text{for each } i \text{ left to right, } \sigma'_0 = \sigma \\ p_i = \tau_i \colon \ \rho, \sigma'_{i-1} \vdash e_i \Rightarrow v_i, \sigma_i \quad (\ell_i, \sigma'_i) = \mathrm{alloc}(\sigma_i, v_i) \\ p_i = \tau_i\& \colon \ \rho, \sigma'_{i-1} \vdash e_i \Rightarrow_{\ell} \ell_i, \sigma'_i \\ [x_1 \mapsto \ell_1, \ldots, x_k \mapsto \ell_k], \sigma'_k \vdash c \Rightarrow \mathsf{ret}\,v, \rho', \sigma'' \end{array}}{\rho, \sigma \vdash f(e_1, \ldots, e_k) \Rightarrow v, \sigma'' \setminus (\{\ell_i \mid p_i \text{ by value}\} \cup (\rho' \setminus \rho_f))}\;\textsf{(Call)}`

Two reference parameters bound to the same argument alias each other, and a write through one is read through the other, as in C++.
:::

# Lambdas and function values

:::definition "fun_accept" (parent := "ud4") (lean := "CoreCpp.Typing.accept, CoreCpp.Typing.lambdaAt, CoreCpp.TBind, CoreCpp.TEnv.captured") (uses := "judg_ty_expr, judg_ty_cmd, dom_tenv")
A lambda has no type of its own. The judgment $`\Gamma \vdash e \lhd \tau`, $`e` is acceptable at $`\tau`, checks a lambda against the `std::function` type expected where it occurs, as argument, as initialiser of a declaration and as `return` expression, and for any other expression it is $`\Gamma \vdash e : \tau'` with $`\tau' \approx \tau`. The body is checked under $`\Gamma` with every variable of the enclosing scope marked read only, the copies of `[=]`, and with the parameters of the lambda as ordinary variables. The rule `T-LocVar` requires a variable that is not read only, so an assignment to a captured variable, or a reference to it, is a type error.

$$`\dfrac{\Gamma \vdash e : \tau' \qquad \tau' \approx \tau \qquad \tau' \text{ has values}}{\Gamma \vdash e \lhd \tau}\;\textsf{(Accept)}`

$$`\dfrac{\begin{array}{c} \Gamma' = \Gamma \text{ marked read only}, [x_1 \mapsto \tau_1, \ldots, x_k \mapsto \tau_k] \\ \Gamma' \vdash c \dashv \Gamma'' \qquad \tau, \tau_i \text{ storable and well formed} \end{array}}{\Gamma \vdash \mathtt{[=]}(\tau_1\,x_1, \ldots, \tau_k\,x_k)\ \mathtt{->}\ \tau\ \{c\} \lhd \mathtt{std{:}{:}function}\langle \tau(\tau_1, \ldots, \tau_k) \rangle}\;\textsf{(T-Lambda)}`

Outside its three positions a lambda is a type error, and `auto x = [=]…` is a syntax error, because the grammar admits a lambda only as an argument expression.
:::

:::definition "lambda" (parent := "ud4") (lean := "CoreCpp.Eval.expr, CoreCpp.Eval.captures, CoreCpp.Expr.vars, CoreCpp.Cmd.vars") (uses := "judg_ev_expr, dom_closure, fun_accept")
A lambda evaluates to a closure with copies of the free variables of its body that the environment binds, taken when the lambda is evaluated. The closure holds values, not locations. A captured `int` or `bool` is a copy the body reads and never writes, and a captured pointer still reaches its object in $`\sigma`, so an effect through it is visible outside the lambda.

$$`\dfrac{\begin{array}{c} \{y_1, \ldots, y_m\} = \text{free variables of } c \text{ bound in } \rho, \text{ minus the } x_i \\ \rho(y_j) = \ell_j \qquad \ell_j \in \mathrm{dom}\,\sigma \qquad w_j = \sigma(\ell_j) \end{array}}{\rho, \sigma \vdash \mathtt{[=]}(\tau_1\,x_1, \ldots, \tau_k\,x_k)\ \mathtt{->}\ \tau\ \{c\} \Rightarrow \mathsf{closure}(\vec{x}, \tau, c, [y_1 \mapsto w_1, \ldots, y_m \mapsto w_m]), \sigma}\;\textsf{(Lambda)}`
:::

:::definition "fun_callfn" (parent := "ud4") (lean := "CoreCpp.Typing.callValue, CoreCpp.Eval.applyClosure") (uses := "lambda, fun_call, judg_ev_expr, dom_store")
A call through a function value evaluates the function expression to a closure, the arguments by value and left to right, allocates fresh locations for the captured copies and for the parameters, runs the body in an environment with those bindings only, and frees them on return. When the callee is a variable `f` of function type, `f(…)` is this rule and not the call of the function named `f`.

$$`\dfrac{\Gamma \vdash e : \mathtt{std{:}{:}function}\langle \tau(\tau_1, \ldots, \tau_k) \rangle \qquad \Gamma \vdash e_i \lhd \tau_i \quad (1 \le i \le k)}{\Gamma \vdash e(e_1, \ldots, e_k) : \tau}\;\textsf{(T-CallFn)}`

$$`\dfrac{\begin{array}{c} \rho, \sigma \vdash e \Rightarrow \mathsf{closure}(x_1 \ldots x_k, \tau, c, [y_1 \mapsto w_1, \ldots, y_m \mapsto w_m]), \sigma_0 \\ \rho, \sigma_{i-1} \vdash e_i \Rightarrow v_i, \sigma_i \quad (1 \le i \le k) \qquad (\ell'_j, \cdot) = \mathrm{alloc}(w_j) \qquad (\ell_i, \cdot) = \mathrm{alloc}(v_i) \\ [y_1 \mapsto \ell'_1, \ldots, y_m \mapsto \ell'_m, x_1 \mapsto \ell_1, \ldots, x_k \mapsto \ell_k], \sigma' \vdash c \Rightarrow \mathsf{ret}\,v, \rho'', \sigma'' \end{array}}{\rho, \sigma \vdash e(e_1, \ldots, e_k) \Rightarrow v, \sigma'' \setminus (\{\ell'_j, \ell_i\} \cup (\rho'' \setminus \rho_c))}\;\textsf{(CallFn)}`

With $`\mathsf{normal}` in place of $`\mathsf{ret}\,v` the result is $`\mathsf{void}` if $`\tau = \mathsf{void}` and `error` otherwise. Nothing of the environment of the call is visible inside the body, only the copies and the parameters.
:::

# Return

:::definition "fun_return" (parent := "ud4") (lean := "CoreCpp.Typing.cmd, CoreCpp.Eval.cmd") (uses := "judg_ty_cmd, judg_ev_cmd, dom_ctrl")
The `return` yields the control $`\mathsf{ret}\,v`, which `Seq-Ret` and `While-Ret` propagate up to the call. The type of the expression is the return type $`\tau_r` of the enclosing function.

$$`\dfrac{\tau_r = \mathsf{void}}{\Gamma \vdash \mathtt{return} \dashv \Gamma}\;\textsf{(T-RetVoid)}`

$$`\dfrac{\Gamma \vdash e : \tau_r \qquad \tau_r \neq \mathsf{void}}{\Gamma \vdash \mathtt{return}\ e \dashv \Gamma}\;\textsf{(T-Ret)}`

$$`\dfrac{}{\rho, \sigma \vdash \mathtt{return} \Rightarrow \mathsf{ret}\,\mathsf{void}, \rho, \sigma}\;\textsf{(ReturnVoid)}`

$$`\dfrac{\rho, \sigma \vdash e \Rightarrow v, \sigma'}{\rho, \sigma \vdash \mathtt{return}\ e \Rightarrow \mathsf{ret}\,v, \rho, \sigma'}\;\textsf{(Return)}`
:::

# Function and program

:::definition "fun_decl" (parent := "ud4") (lean := "CoreCpp.Typing.fn") (uses := "judg_ty_cmd")
A function is well typed when its body is, under the context of its parameters and its return type.

$$`\dfrac{[x_1 \mapsto \tau_1, \ldots, x_k \mapsto \tau_k] \vdash c \dashv \Gamma'}{\vdash \tau\ f(\tau_1\,x_1, \ldots, \tau_k\,x_k)\ \{c\}}\;\textsf{(T-Fun)}`
:::

:::definition "program" (parent := "ud4") (lean := "CoreCpp.Program, CoreCpp.check, CoreCpp.runWith, CoreCpp.run") (uses := "fun_decl, fun_call")
A program is a list of functions with distinct names and a function `int main()`. The initial store is empty, because there are no global variables, and the result is the value of `main()`.

$$`\dfrac{\begin{array}{c} \text{distinct names} \qquad \vdash f_i \ \text{for each } i \\ \mathtt{main} \mapsto \mathtt{int\ main()}\ \{c\} \end{array}}{\vdash p}\;\textsf{(T-Program)}`

$$`\dfrac{[\,], \emptyset \vdash \mathtt{main}() \Rightarrow v, \sigma}{p \Rightarrow v}\;\textsf{(Program)}`
:::

# Properties

:::theorem "progresso" (parent := "ud4") (uses := "judg_ev_expr, judg_ev_cmd, judg_ty_expr, judg_ty_cmd")
Every derivation of a well typed program ends in a value or in `error`. Every well typed constructor has an evaluation rule, checked by inspection of the rule set. There is no Lean proof, and the property is stated without proving it.
:::

:::theorem "determinismo" (parent := "ud4") (uses := "judg_ev_expr, judg_ev_cmd")
Every construction has rules with mutually exclusive premises, and a Core C++ program has at most one result. The evaluation order fixed left to right removes the choice C++17 leaves to the compiler. There is no Lean proof.
:::
