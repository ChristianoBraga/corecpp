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

Functions with parameters by value and by reference, `return` as a control result, lambdas with capture by copy, function values, and the program. The call evaluates the arguments left to right, allocates a fresh location with a copy for each parameter by value, and binds each parameter by reference to the location of its argument. The return removes the copies and the locals of the body from $`\sigma`.

:::group "abstraction"
Functions, parameters and calls.
:::

# Call

:::definition "fun_call" (parent := "abstraction") (lean := "CoreCpp.Typing.expr, CoreCpp.Eval.expr, CoreCpp.Fun, CoreCpp.Param, CoreCpp.Semantics.HasType, CoreCpp.Semantics.Eval, CoreCpp.Semantics.Bind, CoreCpp.Semantics.Returns") (uses := "judg_ty_expr, judg_ev_expr, cmd_seq, dom_funenv, dom_store, dom_env")
Let $`f \mapsto \tau\ f(\tau_1\,x_1, \ldots, \tau_k\,x_k)\ \{c\}` be in the program. The environment of the function holds only the parameters, because there are no global variables.

Each argument is checked at the type of its parameter by the judgment $`\Gamma \vdash e \lhd \tau` of {bpref "fun_accept"}[], so that a lambda may be an argument. A variable `f` of a `std::function` type in $`\Gamma` hides the function named `f`, and the call is then {bpref "fun_callfn"}[].

$$`\dfrac{f \notin \Gamma \qquad \Gamma \vdash e_i \lhd \tau_i \quad (1 \le i \le k)}{\Gamma \vdash f(e_1, \ldots, e_k) : \tau}\;\textsf{(T-Call)}`

$$`\dfrac{\begin{array}{c} f \notin \rho \qquad \rho, \sigma'_{i-1} \vdash e_i \Rightarrow v_i, \sigma_i \quad (\ell_i, \sigma'_i) = \mathrm{alloc}(\sigma_i, v_i) \quad (1 \le i \le k,\ \sigma'_0 = \sigma) \\ \rho_f = [x_1 \mapsto \ell_1, \ldots, x_k \mapsto \ell_k] \qquad \rho_f, \sigma'_k \vdash c \Rightarrow r, \rho', \sigma'' \qquad \mathsf{Returns}(r, \tau, v) \end{array}}{\rho, \sigma \vdash f(e_1, \ldots, e_k) \Rightarrow v, \sigma'' \setminus (\{\ell_1, \ldots, \ell_k\} \cup \mathrm{fresh}(\rho_f, \rho'))}\;\textsf{(Call)}`

The return frees the copies of the arguments and the locals the body declared, $`\mathrm{fresh}(\rho_f, \rho')` of {bpref "dom_env"}[]. After a call the store holds only what existed before it and the objects created with `new`.

The predicate $`\mathsf{Returns}(r, \tau, v)` gives the result $`v` of a body with result type $`\tau` that ends with the control $`r`. A `return e` gives the value of `e`. A body that ends with $`\mathsf{normal}` gives $`\mathsf{void}` if $`\tau = \mathsf{void}`, and otherwise there is no derivation. A missing `return` in a non `void` function is an `error` of the evaluator, not a type error. C++17 leaves it undefined in a function other than `main` (N4659 §9.6.3 paragraph 2). For `main` the rule departs from C++17, where the end of `main` is a `return 0` (N4659 §6.6.1 paragraph 5).

$$`\dfrac{}{\mathsf{Returns}(\mathsf{ret}\,v, \tau, v)}\;\textsf{(Returns-Ret)}`

$$`\dfrac{}{\mathsf{Returns}(\mathsf{normal}, \mathsf{void}, \mathsf{void})}\;\textsf{(Returns-Void)}`

The rule above is the case in which every parameter is by value, and {bpref "param_ref"}[] gives the case of a parameter by reference.
:::

# Parameters by reference

:::definition "param_ref" (parent := "abstraction") (lean := "CoreCpp.Param, CoreCpp.Typing.expr, CoreCpp.Eval.expr, CoreCpp.Env.alias, CoreCpp.Semantics.HasType, CoreCpp.Semantics.Eval, CoreCpp.Semantics.CheckArgs, CoreCpp.Semantics.Bind") (uses := "fun_call, judg_ty_lval, judg_ev_lval, dom_env")
A parameter $`\tau_j\&\ x_j` receives the location of its argument, which must denote a location of exactly the type $`\tau_j`. The binding of $`x_j` in the function environment is an alias, as in a local reference, and the return does not free it. In $`\Gamma` the parameter has the type of its referent.

$$`\dfrac{f \notin \Gamma \qquad \Gamma \vdash e_i \lhd \tau_i \ \text{for each } p_i = \tau_i \qquad \Gamma \vdash_{\ell} e_j : \tau_j \ \text{for each } p_j = \tau_j\&}{\Gamma \vdash f(e_1, \ldots, e_k) : \tau}\;\textsf{(T-Call)}`

$$`\dfrac{\begin{array}{c} f \notin \rho \qquad \text{for each } i \text{ left to right, } \sigma'_0 = \sigma \\ p_i = \tau_i \colon \ \rho, \sigma'_{i-1} \vdash e_i \Rightarrow v_i, \sigma_i \quad (\ell_i, \sigma'_i) = \mathrm{alloc}(\sigma_i, v_i) \\ p_i = \tau_i\& \colon \ \rho, \sigma'_{i-1} \vdash e_i \Rightarrow_{\ell} \ell_i, \sigma'_i \\ \rho_f = [x_1 \mapsto \ell_1, \ldots, x_k \mapsto \ell_k] \qquad \rho_f, \sigma'_k \vdash c \Rightarrow r, \rho', \sigma'' \qquad \mathsf{Returns}(r, \tau, v) \end{array}}{\rho, \sigma \vdash f(e_1, \ldots, e_k) \Rightarrow v, \sigma'' \setminus (\{\ell_i \mid p_i \text{ by value}\} \cup \mathrm{fresh}(\rho_f, \rho'))}\;\textsf{(Call)}`

Two reference parameters bound to the same argument alias each other, and a write through one is read through the other, as in C++.
:::

# Lambdas and function values

:::definition "fun_accept" (parent := "abstraction") (lean := "CoreCpp.Typing.accept, CoreCpp.Typing.lambdaAt, CoreCpp.TBind, CoreCpp.TEnv.captured, CoreCpp.Semantics.Accept") (uses := "judg_ty_expr, judg_ty_cmd, dom_tenv")
A lambda has no type of its own. The judgment $`\Gamma \vdash e \lhd \tau`, $`e` is acceptable at $`\tau`, checks a lambda against the function type expected where it occurs, the argument of `new std::function<F>(λ)` in {bpref "std_function"}[]. For any other expression it is $`\Gamma \vdash e : \tau'` with $`\mathsf{Compat}(\tau', \tau)`.

The type checker checks the body under $`\Gamma` with every variable of the enclosing scope marked read only, the copies of `[=]`. The parameters of the lambda are ordinary variables, and the result type of the body is the result type $`\tau` of the lambda.

The rule `T-LocVar` requires a variable that is not read only, so an assignment to a captured variable, or a reference to it, is a type error.

$$`\dfrac{\Gamma \vdash e : \tau' \qquad \mathsf{Compat}(\tau', \tau) \qquad \tau' \text{ has values}}{\Gamma \vdash e \lhd \tau}\;\textsf{(Accept)}`

$$`\dfrac{\begin{array}{c} \Gamma' = \Gamma \text{ marked read only}, [x_1 \mapsto \tau_1, \ldots, x_k \mapsto \tau_k]\qquad \Gamma' \vdash c \dashv \Gamma'' \text{ with result type } \tau \\ \tau = \mathsf{void} \lor \mathsf{Storable}(\tau) \qquad \mathsf{Storable}(\tau_i) \qquad \tau, \tau_i \text{ well formed} \end{array}}{\Gamma \vdash \mathtt{[=]}(\tau_1\,x_1, \ldots, \tau_k\,x_k)\ \mathtt{->}\ \tau\ \{c\} \lhd \tau(\tau_1, \ldots, \tau_k)}\;\textsf{(T-Lambda)}`

Anywhere else a lambda is a syntax error, since the grammar admits it only as an argument of `new`. As the argument of a `new` of a class of the program it is a type error, since no constructor parameter has a function type. The grammar chapter, {bpref "parse_statement"}[], explains the decision.
:::

:::definition "lambda" (parent := "abstraction") (lean := "CoreCpp.Eval.expr, CoreCpp.Eval.captures, CoreCpp.Expr.vars, CoreCpp.Cmd.vars, CoreCpp.Semantics.Eval, CoreCpp.captures?") (uses := "judg_ev_expr, dom_closure, fun_accept")
A lambda evaluates to a closure with copies of the variables of its body that the environment binds, its parameters excluded, at the evaluation of the lambda. The closure holds values, not locations. A captured `int` or `bool` is a copy the body reads and never writes. A captured pointer still reaches its object in $`\sigma`, so an effect through it is visible outside the lambda.

$$`\dfrac{\begin{array}{c} \{y_1, \ldots, y_m\} = \text{variables of } c \text{ bound in } \rho, \text{ minus the } x_i\qquad \rho(y_j) = \ell_j \\ \ell_j \in \mathrm{dom}\,\sigma\qquad w_j = \sigma(\ell_j) \end{array}}{\begin{array}{c} \rho, \sigma \vdash \mathtt{[=]}(\tau_1\,x_1, \ldots, \tau_k\,x_k)\ \mathtt{->}\ \tau\ \{c\} \\ \Rightarrow \mathsf{closure}(\vec{x}, \tau, c, [y_1 \mapsto w_1, \ldots, y_m \mapsto w_m]), \sigma \end{array}}\;\textsf{(Lambda)}`
:::

:::definition "fun_callfn" (parent := "abstraction") (lean := "CoreCpp.Typing.callValue, CoreCpp.Eval.target, CoreCpp.Eval.applyClosure, CoreCpp.Eval.applyVals, CoreCpp.Semantics.Apply, CoreCpp.Semantics.ApplyArgs") (uses := "lambda, fun_call, judg_ev_expr, dom_store")
A call through a function object, `(*f)(e₁, …, eₖ)` for a pointer `f`, evaluates the callee to the object and reads its target, a closure. It then evaluates the arguments by value and left to right, and allocates fresh locations for the captured copies and for the parameters. The body runs in an environment with those bindings only, and the return frees them with the locals of the body.

When the callee is a reference `g` to a function object, `g(…)` is this rule and not the call of the function named `g`.

$$`\dfrac{\Gamma \vdash e : \mathtt{std{:}{:}function}\langle\tau(\tau_1, \ldots, \tau_k)\rangle \qquad \Gamma \vdash e_i \lhd \tau_i \quad (1 \le i \le k)}{\Gamma \vdash e(e_1, \ldots, e_k) : \tau}\;\textsf{(T-CallFn)}`

$$`\dfrac{\begin{array}{c} \rho, \sigma \vdash e \Rightarrow \mathsf{lib}\ \mathtt{std{:}{:}function}\,[\ell_t], \sigma_0\qquad \sigma_0(\ell_t) = w \\ \rho, \sigma_{i-1} \vdash e_i \Rightarrow v_i, \sigma_i \quad (1 \le i \le k)\qquad \mathrm{apply}(\sigma_k, w, (v_1, \ldots, v_k)) \Rightarrow v, \sigma' \end{array}}{\rho, \sigma \vdash e(e_1, \ldots, e_k) \Rightarrow v, \sigma'}\;\textsf{(CallFn)}`

The target $`w` is a closure, and the function with no target, $`\mathsf{null}` at $`\ell_t`, has no derivation, so its call is `error` in the evaluator. The application of the closure to the values is a judgment of its own. It allocates the captured copies and then the arguments, `allocMany` of {bpref "dom_store"}[], and its body ends as the body of {bpref "fun_call"}[] does.

$$`\dfrac{\begin{array}{c} v = \mathsf{closure}(x_1 \ldots x_k, \tau, c, [y_1 \mapsto w_1, \ldots, y_m \mapsto w_m]) \\ (\ell'_1 \ldots \ell'_m\, \ell_1 \ldots \ell_k, \sigma_1) = \mathrm{allocMany}(\sigma, w_1 \ldots w_m\, v_1 \ldots v_k) \\ \rho_c = [y_1 \mapsto \ell'_1, \ldots, y_m \mapsto \ell'_m, x_1 \mapsto \ell_1, \ldots, x_k \mapsto \ell_k] \\ \rho_c, \sigma_1 \vdash c \Rightarrow r, \rho'', \sigma'' \qquad \mathsf{Returns}(r, \tau, v') \end{array}}{\mathrm{apply}(\sigma, v, (v_1, \ldots, v_k)) \Rightarrow v', \sigma'' \setminus (\{\ell'_1, \ldots, \ell'_m, \ell_1, \ldots, \ell_k\} \cup \mathrm{fresh}(\rho_c, \rho''))}\;\textsf{(Apply)}`
:::

# Return

:::definition "fun_return" (parent := "abstraction") (lean := "CoreCpp.Typing.cmd, CoreCpp.Eval.cmd, CoreCpp.Semantics.Check, CoreCpp.Semantics.Exec") (uses := "judg_ty_cmd, judg_ev_cmd, dom_ctrl")
The `return` yields the control $`\mathsf{ret}\,v`, which `Seq-Ret` and `While-Ret` propagate up to the call. The expression of `return e` is acceptable at the result type $`\tau_r` of the enclosing body.

$$`\dfrac{\tau_r = \mathsf{void}}{\Gamma \vdash \mathtt{return} \dashv \Gamma}\;\textsf{(T-RetVoid)}`

$$`\dfrac{\Gamma \vdash e \lhd \tau_r \qquad \tau_r \neq \mathsf{void}}{\Gamma \vdash \mathtt{return}\ e \dashv \Gamma}\;\textsf{(T-Ret)}`

$$`\dfrac{}{\rho, \sigma \vdash \mathtt{return} \Rightarrow \mathsf{ret}\,\mathsf{void}, \rho, \sigma}\;\textsf{(ReturnVoid)}`

$$`\dfrac{\rho, \sigma \vdash e \Rightarrow v, \sigma'}{\rho, \sigma \vdash \mathtt{return}\ e \Rightarrow \mathsf{ret}\,v, \rho, \sigma'}\;\textsf{(Return)}`
:::

# Function and program

:::definition "fun_decl" (parent := "abstraction") (lean := "CoreCpp.Typing.fn, CoreCpp.Semantics.FunOk") (uses := "judg_ty_cmd, dom_tenv")
A function is well typed when its body is well typed under the context of its parameters and its result type. Its result type is `void` or storable, each parameter type is bindable, and every type is well formed. A reference parameter may thus have an object type.

$$`\dfrac{\begin{array}{c} \tau = \mathsf{void} \lor \mathsf{Storable}(\tau) \qquad \mathsf{Bindable}_{r_i}(\tau_i) \qquad \tau, \tau_i \text{ well formed} \\ [x_1 \mapsto \tau_1, \ldots, x_k \mapsto \tau_k] \vdash c \dashv \Gamma' \text{ with result type } \tau \end{array}}{\vdash \tau\ f(\tau_1\,x_1, \ldots, \tau_k\,x_k)\ \{c\}}\;\textsf{(T-Fun)}`
:::

:::definition "program" (parent := "abstraction") (lean := "CoreCpp.Program, CoreCpp.check, CoreCpp.runWith, CoreCpp.run, CoreCpp.Semantics.ProgramOk, CoreCpp.Semantics.Runs") (uses := "fun_decl, fun_call, cls_decl, overload_set, std_library")
A program is a list of declarations of classes and functions with a function `int main()`. The initial store is empty, because there are no global variables, and the result is the value of `main()`.

Two functions of one name have distinct and distinguishable signatures, {bpref "overload_set"}[]. Each class $`C` is well formed, $`\vdash C` of {bpref "cls_decl"}[]. Each class template a header declares has a module of {bpref "std_library"}[], and each function it declares has one that agrees with the declaration.

$$`\dfrac{\begin{array}{c} \text{overloads distinct and distinguishable} \qquad \text{distinct names of classes and class templates} \qquad \text{a module for each declaration of a header} \\ \vdash C_j \ \text{for each } j \qquad \vdash f_i \ \text{for each } i \qquad \mathtt{main} \mapsto \mathtt{int\ main()}\ \{c\} \end{array}}{\vdash p}\;\textsf{(T-Program)}`

$$`\dfrac{[\,], \emptyset \vdash \mathtt{main}() \Rightarrow v, \sigma}{p \Rightarrow v}\;\textsf{(Program)}`
:::

# Properties

:::theorem "progress" (parent := "abstraction") (uses := "judg_ev_expr, judg_ev_cmd, judg_ty_expr, judg_ty_cmd, judg_relations")
A well typed program has a derivation, does not terminate, or is stuck. It is stuck at a case C++17 leaves undefined, or at the end of a `main` without `return`, and the evaluator reports it as `error`. Every well typed constructor has an evaluation rule, checked by inspection of the rule set. There is no Lean proof yet.
:::

:::theorem "determinism" (parent := "abstraction") (uses := "judg_ev_expr, judg_ev_cmd, judg_relations")
Every construct has rules with mutually exclusive premises, and a Core C++ program has at most one result. The evaluation order fixed left to right removes the choice C++17 leaves to the compiler. The relations of {bpref "judg_relations"}[] make the statement precise. Two derivations of $`\rho, \sigma \vdash e \Rightarrow v, \sigma'` for the same $`e` give the same $`v` and $`\sigma'`. There is no Lean proof yet.
:::

# Rules of the chapter

Every typing rule and every evaluation rule of this chapter, in the order of its sections, the typing rules of each section before its evaluation rules. The section named above each rule states it with its explanation and with the definition of its notation.

*Call*

$$`\dfrac{f \notin \Gamma \qquad \Gamma \vdash e_i \lhd \tau_i \quad (1 \le i \le k)}{\Gamma \vdash f(e_1, \ldots, e_k) : \tau}\;\textsf{(T-Call)}`

 

$$`\dfrac{\begin{array}{c} f \notin \rho \qquad \rho, \sigma'_{i-1} \vdash e_i \Rightarrow v_i, \sigma_i \quad (\ell_i, \sigma'_i) = \mathrm{alloc}(\sigma_i, v_i) \quad (1 \le i \le k,\ \sigma'_0 = \sigma) \\ \rho_f = [x_1 \mapsto \ell_1, \ldots, x_k \mapsto \ell_k] \qquad \rho_f, \sigma'_k \vdash c \Rightarrow r, \rho', \sigma'' \qquad \mathsf{Returns}(r, \tau, v) \end{array}}{\rho, \sigma \vdash f(e_1, \ldots, e_k) \Rightarrow v, \sigma'' \setminus (\{\ell_1, \ldots, \ell_k\} \cup \mathrm{fresh}(\rho_f, \rho'))}\;\textsf{(Call)}`

$$`\dfrac{}{\mathsf{Returns}(\mathsf{ret}\,v, \tau, v)}\;\textsf{(Returns-Ret)}`

$$`\dfrac{}{\mathsf{Returns}(\mathsf{normal}, \mathsf{void}, \mathsf{void})}\;\textsf{(Returns-Void)}`

*Parameters by reference*

$$`\dfrac{f \notin \Gamma \qquad \Gamma \vdash e_i \lhd \tau_i \ \text{for each } p_i = \tau_i \qquad \Gamma \vdash_{\ell} e_j : \tau_j \ \text{for each } p_j = \tau_j\&}{\Gamma \vdash f(e_1, \ldots, e_k) : \tau}\;\textsf{(T-Call)}`

 

$$`\dfrac{\begin{array}{c} f \notin \rho \qquad \text{for each } i \text{ left to right, } \sigma'_0 = \sigma \\ p_i = \tau_i \colon \ \rho, \sigma'_{i-1} \vdash e_i \Rightarrow v_i, \sigma_i \quad (\ell_i, \sigma'_i) = \mathrm{alloc}(\sigma_i, v_i) \\ p_i = \tau_i\& \colon \ \rho, \sigma'_{i-1} \vdash e_i \Rightarrow_{\ell} \ell_i, \sigma'_i \\ \rho_f = [x_1 \mapsto \ell_1, \ldots, x_k \mapsto \ell_k] \qquad \rho_f, \sigma'_k \vdash c \Rightarrow r, \rho', \sigma'' \qquad \mathsf{Returns}(r, \tau, v) \end{array}}{\rho, \sigma \vdash f(e_1, \ldots, e_k) \Rightarrow v, \sigma'' \setminus (\{\ell_i \mid p_i \text{ by value}\} \cup \mathrm{fresh}(\rho_f, \rho'))}\;\textsf{(Call)}`

*Lambdas and function values*

$$`\dfrac{\Gamma \vdash e : \tau' \qquad \mathsf{Compat}(\tau', \tau) \qquad \tau' \text{ has values}}{\Gamma \vdash e \lhd \tau}\;\textsf{(Accept)}`

$$`\dfrac{\begin{array}{c} \Gamma' = \Gamma \text{ marked read only}, [x_1 \mapsto \tau_1, \ldots, x_k \mapsto \tau_k]\qquad \Gamma' \vdash c \dashv \Gamma'' \text{ with result type } \tau \\ \tau = \mathsf{void} \lor \mathsf{Storable}(\tau) \qquad \mathsf{Storable}(\tau_i) \qquad \tau, \tau_i \text{ well formed} \end{array}}{\Gamma \vdash \mathtt{[=]}(\tau_1\,x_1, \ldots, \tau_k\,x_k)\ \mathtt{->}\ \tau\ \{c\} \lhd \tau(\tau_1, \ldots, \tau_k)}\;\textsf{(T-Lambda)}`

$$`\dfrac{\Gamma \vdash e : \mathtt{std{:}{:}function}\langle\tau(\tau_1, \ldots, \tau_k)\rangle \qquad \Gamma \vdash e_i \lhd \tau_i \quad (1 \le i \le k)}{\Gamma \vdash e(e_1, \ldots, e_k) : \tau}\;\textsf{(T-CallFn)}`

 

$$`\dfrac{\begin{array}{c} \{y_1, \ldots, y_m\} = \text{variables of } c \text{ bound in } \rho, \text{ minus the } x_i\qquad \rho(y_j) = \ell_j \\ \ell_j \in \mathrm{dom}\,\sigma\qquad w_j = \sigma(\ell_j) \end{array}}{\begin{array}{c} \rho, \sigma \vdash \mathtt{[=]}(\tau_1\,x_1, \ldots, \tau_k\,x_k)\ \mathtt{->}\ \tau\ \{c\} \\ \Rightarrow \mathsf{closure}(\vec{x}, \tau, c, [y_1 \mapsto w_1, \ldots, y_m \mapsto w_m]), \sigma \end{array}}\;\textsf{(Lambda)}`

$$`\dfrac{\begin{array}{c} \rho, \sigma \vdash e \Rightarrow \mathsf{lib}\ \mathtt{std{:}{:}function}\,[\ell_t], \sigma_0\qquad \sigma_0(\ell_t) = w \\ \rho, \sigma_{i-1} \vdash e_i \Rightarrow v_i, \sigma_i \quad (1 \le i \le k)\qquad \mathrm{apply}(\sigma_k, w, (v_1, \ldots, v_k)) \Rightarrow v, \sigma' \end{array}}{\rho, \sigma \vdash e(e_1, \ldots, e_k) \Rightarrow v, \sigma'}\;\textsf{(CallFn)}`

$$`\dfrac{\begin{array}{c} v = \mathsf{closure}(x_1 \ldots x_k, \tau, c, [y_1 \mapsto w_1, \ldots, y_m \mapsto w_m]) \\ (\ell'_1 \ldots \ell'_m\, \ell_1 \ldots \ell_k, \sigma_1) = \mathrm{allocMany}(\sigma, w_1 \ldots w_m\, v_1 \ldots v_k) \\ \rho_c = [y_1 \mapsto \ell'_1, \ldots, y_m \mapsto \ell'_m, x_1 \mapsto \ell_1, \ldots, x_k \mapsto \ell_k] \\ \rho_c, \sigma_1 \vdash c \Rightarrow r, \rho'', \sigma'' \qquad \mathsf{Returns}(r, \tau, v') \end{array}}{\mathrm{apply}(\sigma, v, (v_1, \ldots, v_k)) \Rightarrow v', \sigma'' \setminus (\{\ell'_1, \ldots, \ell'_m, \ell_1, \ldots, \ell_k\} \cup \mathrm{fresh}(\rho_c, \rho''))}\;\textsf{(Apply)}`

*Return*

$$`\dfrac{\tau_r = \mathsf{void}}{\Gamma \vdash \mathtt{return} \dashv \Gamma}\;\textsf{(T-RetVoid)}`

$$`\dfrac{\Gamma \vdash e \lhd \tau_r \qquad \tau_r \neq \mathsf{void}}{\Gamma \vdash \mathtt{return}\ e \dashv \Gamma}\;\textsf{(T-Ret)}`

 

$$`\dfrac{}{\rho, \sigma \vdash \mathtt{return} \Rightarrow \mathsf{ret}\,\mathsf{void}, \rho, \sigma}\;\textsf{(ReturnVoid)}`

$$`\dfrac{\rho, \sigma \vdash e \Rightarrow v, \sigma'}{\rho, \sigma \vdash \mathtt{return}\ e \Rightarrow \mathsf{ret}\,v, \rho, \sigma'}\;\textsf{(Return)}`

*Function and program*

$$`\dfrac{\begin{array}{c} \tau = \mathsf{void} \lor \mathsf{Storable}(\tau) \qquad \mathsf{Bindable}_{r_i}(\tau_i) \qquad \tau, \tau_i \text{ well formed} \\ [x_1 \mapsto \tau_1, \ldots, x_k \mapsto \tau_k] \vdash c \dashv \Gamma' \text{ with result type } \tau \end{array}}{\vdash \tau\ f(\tau_1\,x_1, \ldots, \tau_k\,x_k)\ \{c\}}\;\textsf{(T-Fun)}`

$$`\dfrac{\begin{array}{c} \text{overloads distinct and distinguishable} \qquad \text{distinct names of classes and class templates} \qquad \text{a module for each declaration of a header} \\ \vdash C_j \ \text{for each } j \qquad \vdash f_i \ \text{for each } i \qquad \mathtt{main} \mapsto \mathtt{int\ main()}\ \{c\} \end{array}}{\vdash p}\;\textsf{(T-Program)}`

 

$$`\dfrac{[\,], \emptyset \vdash \mathtt{main}() \Rightarrow v, \sigma}{p \Rightarrow v}\;\textsf{(Program)}`
