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

#doc (Manual) "UD IV, abstraction" =>

First order functions with call by value, `return` as a control result, and the program. The call evaluates the arguments left to right, allocates a fresh location with a copy for each parameter and removes those locations from $`\sigma` on return.

:::group "ud4"
UD IV, functions, parameters and calls.
:::

# Call

:::definition "fun_call" (parent := "ud4") (lean := "CoreCpp.Typing.expr, CoreCpp.Eval.expr, CoreCpp.Fun, CoreCpp.Param") (uses := "judg_ty_expr, judg_ev_expr, cmd_seq, dom_funenv, dom_store")
Let $`f \mapsto \tau\ f(\tau_1\,x_1, \ldots, \tau_k\,x_k)\ \{c\}` be in the program. The environment of the function holds only the parameters, because there are no global variables.

$$`\dfrac{\Gamma \vdash e_i : \tau_i \quad (1 \le i \le k)}{\Gamma \vdash f(e_1, \ldots, e_k) : \tau}\;\textsf{(T-Call)}`

$$`\dfrac{\begin{array}{c} \rho, \sigma_{i-1} \vdash e_i \Rightarrow v_i, \sigma_i \quad (1 \le i \le k,\ \sigma_0 = \sigma) \\ (\ell_i, \sigma'_i) = \mathrm{alloc}(\sigma'_{i-1}, v_i) \quad (1 \le i \le k,\ \sigma'_0 = \sigma_k) \\ [x_1 \mapsto \ell_1, \ldots, x_k \mapsto \ell_k], \sigma'_k \vdash c \Rightarrow \mathsf{ret}\,v, \rho', \sigma'' \end{array}}{\rho, \sigma \vdash f(e_1, \ldots, e_k) \Rightarrow v, \sigma'' \setminus \{\ell_1, \ldots, \ell_k\}}\;\textsf{(Call)}`

When the body ends with $`\mathsf{normal}`, the result is $`\mathsf{void}` if $`\tau = \mathsf{void}` and `error` otherwise. A missing `return` in a non `void` function is an evaluation `error`, not a type error.
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
Every derivation of a well typed program ends in a value or in `error`. Every well typed constructor has an evaluation rule, checked by inspection of the rule set. There is no Lean proof, and the course states the property without proving it.
:::

:::theorem "determinismo" (parent := "ud4") (uses := "judg_ev_expr, judg_ev_cmd")
Every construction has rules with mutually exclusive premises, and a Core C++ program has at most one result. The evaluation order fixed left to right removes the choice C++17 leaves to the compiler. There is no Lean proof.
:::
