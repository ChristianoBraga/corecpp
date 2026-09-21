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

:::definition "dom_val" (parent := "dominios") (lean := "CoreCpp.Val, CoreCpp.Ty.default") (uses := "dom_int32, dom_loc")
The values are $`\mathsf{int}\,n`, $`\mathsf{bool}\,b`, $`\mathsf{void}`, the pointer $`\mathsf{loc}\,\ell`, the value $`\mathsf{null}` of `nullptr`, the object $`\mathsf{obj}\,C\,[f_1 \mapsto \ell_1, \ldots, f_n \mapsto \ell_n]`, a record of one location per field with its class tag, and the vector $`\mathsf{vec}\,[\ell_0, \ldots, \ell_{n-1}]`, one location per element. The value $`\mathsf{void}` is the result of a call to a function without return value, and the initial content of a field of function type before the constructor assigns it. UD IV adds the closure, {bpref "dom_closure"}[]. Since UD V the tag of an object is the class it was created with, its fields are those of the whole chain of classes, the root base first, and the tag decides the dispatch of virtual methods and the destructors that `delete` runs. Objects and vectors live in the store at their own location and are reached only through pointers. The default value of a type, which `new` gives to every field and element, is $`\mathsf{int}\,0`, $`\mathsf{bool}\,\mathtt{false}` or $`\mathsf{null}`.
:::

:::definition "dom_int32" (parent := "dominios") (lean := "CoreCpp.Int32.min, CoreCpp.Int32.max, CoreCpp.Int32.inRange")
The type `int` has 32 bits in two's complement. The partial operation $`\mathsf{int32}` returns the integer when it lies in the range and `error` otherwise.

$$`\dfrac{n \in [-2^{31},\, 2^{31}-1]}{\mathsf{int32}\,n = \mathsf{int}\,n} \qquad \dfrac{n \notin [-2^{31},\, 2^{31}-1]}{\mathsf{int32}\,n = \mathsf{error}}`
:::

:::definition "dom_env" (parent := "dominios") (lean := "CoreCpp.Env, CoreCpp.Binding, CoreCpp.Env.lookup, CoreCpp.Env.extend, CoreCpp.Env.alias") (uses := "dom_loc")
The environment $`\rho` is a finite map from identifiers to locations. The notation $`\rho[x \mapsto \ell]` extends $`\rho`, and the most recent binding prevails. Each binding records whether the declaration that made it allocated the location, as `τ x = e` does, or aliased an existing one, as the reference `τ& y = e` does. Block exit frees only the owned locations. Inside a member body, `this` is an alias binding to the location of the receiver, made by the call and never freed by the return.
:::

:::definition "dom_store" (parent := "dominios") (lean := "CoreCpp.Store, CoreCpp.Store.read, CoreCpp.Store.write, CoreCpp.Store.alloc, CoreCpp.Store.allocMany, CoreCpp.Store.free, CoreCpp.Store.dom") (uses := "dom_loc, dom_val")
The store $`\sigma` is a finite map from locations to values. The operation $`\mathrm{alloc}(\sigma, v)` returns a fresh location $`\ell \notin \mathrm{dom}\,\sigma` and the store $`\sigma[\ell \mapsto v]`. The operation $`\sigma \setminus L` removes the locations of $`L` from the domain. Reading or writing outside the domain is `error`.
:::

:::definition "dom_closure" (parent := "dominios") (lean := "CoreCpp.Val, CoreCpp.Ty.isFn") (uses := "dom_val")
The value of a lambda is the closure $`\mathsf{closure}(x_1 \ldots x_k, \tau, c, [y_1 \mapsto w_1, \ldots, y_m \mapsto w_m])`, with the parameters, the result type, the body and the captured copies, one value per free variable of the body. The types `std::function<τ(τ₁, …, τₖ)>` have closures as values. A variable or a parameter holds a closure, a field or a vector element does not, because `new` would have to give it a default value and there is no empty function in this subset.
:::

:::definition "dom_ctrl" (parent := "dominios") (lean := "CoreCpp.Ctrl") (uses := "dom_val")
The control result $`r` of a command is $`\mathsf{normal}` or $`\mathsf{ret}\,v`. A $`\mathsf{ret}` interrupts sequence, block and loop up to the call that consumes it.
:::

:::definition "dom_erro" (parent := "dominios") (lean := "CoreCpp.Error")
The result `error` is not a value of the language. It replaces the result of any dynamic judgment and propagates to the whole program. Its causes are division by zero, `int` overflow, the dereference of `nullptr`, an index outside a vector, a negative vector size, a location outside $`\sigma`, an undeclared variable or function, wrong arity, a missing `return` in a non `void` function, a second `delete` of the same object, and a `delete` through a pointer to a base class without a virtual destructor.
:::

:::definition "dom_tenv" (parent := "dominios") (lean := "CoreCpp.TEnv, CoreCpp.TBind, CoreCpp.TEnv.lookup, CoreCpp.TEnv.isConst, CoreCpp.TEnv.bind, CoreCpp.TEnv.captured, CoreCpp.TEnv.self")
The typing context $`\Gamma` is a finite map from identifiers to types. The types are $`\mathsf{int}`, $`\mathsf{bool}`, $`\mathsf{void}`, a class $`C`, a pointer $`\tau*`, a vector $`\mathsf{std{:}{:}vector}\langle\tau\rangle` and the internal type $`\mathsf{nullptr\_t}` of `nullptr`. Class and vector types are object types, they have no values, and no variable, parameter, result or field has one. An expression of object type occurs only as the operand of `.`, `[]` or `*`. Since UD IV each binding carries a mark, read only or not. The mark is set on every binding of the enclosing scope when the body of a lambda is checked, so that the copies of `[=]` are read and never written.
:::

:::definition "dom_funenv" (parent := "dominios") (lean := "CoreCpp.Decl, CoreCpp.Program, CoreCpp.Program.funs, CoreCpp.FunEnv, CoreCpp.FunEnv.lookup")
A program is a list of declarations, classes and functions. The functions form a finite map from names to declarations, fixed during the whole evaluation and implicit in the judgments.
:::

:::definition "dom_classes" (parent := "dominios") (lean := "CoreCpp.ClassDecl, CoreCpp.Field, CoreCpp.Method, CoreCpp.Ctor, CoreCpp.Dtor, CoreCpp.Vis, CoreCpp.Program.classes, CoreCpp.Program.lookupClass, CoreCpp.Program.chain, CoreCpp.Program.allFields, CoreCpp.Program.findField, CoreCpp.Program.findMethod, CoreCpp.Program.subclass, CoreCpp.Program.hasVirtualDtor")
The classes of the program form the class table, a finite map from class names to declarations. A declaration has an optional base, fields and methods with their visibility, at most one constructor and at most one destructor. The table gives, for a class, its chain up to the root base, every field of the chain with the class that declares it, the nearest method of a given name, the subclass relation and whether some class of the chain has a virtual destructor. The type checker consults it for types, visibility and dispatch, and `new` and `delete` for the fields to allocate and to free. Names are qualified by their namespace, `N::C`.
:::

# Static judgments

:::definition "judg_ty_expr" (parent := "juizos") (lean := "CoreCpp.Expr, CoreCpp.Typing.expr") (uses := "dom_tenv, gram_ast")
The judgment $`\Gamma \vdash e : \tau` states that the expression $`e` has type $`\tau` in the context $`\Gamma`. One rule per constructor of `Expr`.
:::

:::definition "judg_ty_lval" (parent := "juizos") (lean := "CoreCpp.Typing.lval") (uses := "dom_tenv")
The judgment $`\Gamma \vdash_{\ell} e : \tau` holds for the expressions that denote a location, a variable, `*e`, `e.f`, `e->f` and `e[i]`.
:::

:::definition "judg_ty_cmd" (parent := "juizos") (lean := "CoreCpp.Cmd, CoreCpp.Typing.cmd, CoreCpp.Typing.cmds") (uses := "judg_ty_expr, gram_ast")
The judgment $`\Gamma \vdash c \dashv \Gamma'` states that the command $`c` is well typed and extends $`\Gamma` to $`\Gamma'`, so that a declaration reaches the following commands of the sequence. The return type $`\tau_r` of the enclosing function is an implicit parameter.
:::

# Dynamic judgments

:::definition "judg_ev_expr" (parent := "juizos") (lean := "CoreCpp.Eval.expr") (uses := "dom_env, dom_store, dom_val, dom_erro")
The judgment $`\rho, \sigma \vdash e \Rightarrow v, \sigma'` states that the expression $`e`, under the environment $`\rho` and the store $`\sigma`, evaluates to $`v` and yields $`\sigma'`. The store enters expressions because a function call inside an expression may change it.
:::

:::definition "judg_ev_lval" (parent := "juizos") (lean := "CoreCpp.Eval.lval") (uses := "dom_env, dom_store, dom_loc")
The judgment $`\rho, \sigma \vdash e \Rightarrow_{\ell} \ell, \sigma'` states that the expression $`e` denotes the location $`\ell`. It holds for a variable, a dereferenced pointer, a field of an object, a field through a pointer and an element of a vector.
:::

:::definition "judg_ev_cmd" (parent := "juizos") (lean := "CoreCpp.Eval.cmd, CoreCpp.Eval.cmds") (uses := "judg_ev_expr, dom_ctrl")
The judgment $`\rho, \sigma \vdash c \Rightarrow r, \rho', \sigma'` states that the command $`c` yields the control $`r`, the environment $`\rho'` and the store $`\sigma'`. The output environment exists so that a declaration extends $`\rho` for the following commands, and the block discards the extension when it ends.
:::

:::definition "judg_trace" (parent := "juizos") (lean := "CoreCpp.M, CoreCpp.TState, CoreCpp.TraceAnte, CoreCpp.TraceCons, CoreCpp.TraceEntry, CoreCpp.Eval.traced, CoreCpp.renderTrace") (uses := "judg_ev_expr, judg_ev_cmd")
The evaluator runs in the monad $`M`, which carries the derivation tree. Each rule application records the instance of the rule it concludes, at its depth in the tree, with the antecedent and the consequent in parts. The function `renderTrace` then lays the tree out as a derivation is written on the board, the premises over a line of inference, the conclusion under it and the rule name at the right. A legend names the environments $`\rho_i`, the stores $`\sigma_j` and the subjects too long for a judgment, so every judgment fits one line, and a subtree wider than the page is written apart under a name $`\mathcal{D}_k`.
:::
