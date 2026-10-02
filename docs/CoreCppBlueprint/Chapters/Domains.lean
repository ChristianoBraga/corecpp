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

Core C++ has three semantic components and four judgments. The typing context $`\Gamma` maps identifiers to types. The environment $`\rho` maps identifiers to locations $`\ell`. The store $`\sigma` maps locations to values, and its domain is the set of live locations.

The notation is the sequent style of Kahn (1987). Hypotheses stand left of $`\vdash`, the subject right of it, and the result after $`\Rightarrow`.

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
The values are $`\mathsf{int}\,n`, $`\mathsf{bool}\,b`, $`\mathsf{void}`, the pointer $`\mathsf{loc}\,\ell`, the value $`\mathsf{null}` of `nullptr`, the object $`\mathsf{obj}\,C\,[f_1 \mapsto \ell_1, \ldots, f_n \mapsto \ell_n]`, a record of one location per field with its class tag, and the instance $`\mathsf{lib}\,L\,[\ell_0, \ldots, \ell_{n-1}]` of an object type $`L` of the library, such as a vector, with one location per element, {bpref "std_vector"}[].

The value $`\mathsf{void}` is the result of a call to a function without return value, and the initial content of a field of function type before the constructor assigns it. The closure is a value too, {bpref "dom_closure"}[].

The tag of an object is the class it was created with, its fields are those of the whole chain of classes, the root base first, and the tag decides the dispatch of virtual methods and the destructors that `delete` runs. Objects and instances of object types of the library live in the store at their own location and are reached only through pointers.

The default value of a type, which `new` gives to every field and element, is $`\mathsf{int}\,0`, $`\mathsf{bool}\,\mathtt{false}` or $`\mathsf{null}`.
:::

:::definition "dom_int32" (parent := "dominios") (lean := "CoreCpp.Int32.min, CoreCpp.Int32.max, CoreCpp.Int32.inRange")
The type `int` has 32 bits in two's complement. The partial operation $`\mathsf{int32}` returns the integer when it lies in the range and `error` otherwise.

C++17 fixes neither the width nor the representation of `int`. A plain `int` has the natural size suggested by the architecture of the execution environment, with a range of at least $`[-32767, 32767]` (N4659 §6.9.1 paragraph 2 and §21.3.5, N1570 §5.2.4.2.1). Its representation may be two's complement, ones' complement or signed magnitude (N4659 §6.9.1 paragraph 7). The range of `int` is therefore a property of the platform.

The ABI of the platform fixes it. The System V AMD64 psABI and AAPCS64 both give `int` 32 bits, and GCC supports only two's complement integer types.

An arithmetic result outside the range of `int` has undefined behaviour (N4659 §8 paragraph 4), and Core C++ makes it `error`. That boundary has to be the boundary of the implementation Core C++ is compared with, `g++` and clang on x86‑64 and ARM64. A wider range would give a value where C++ gives none, and a narrower one would give `error` where C++ gives a value.

The representation enters only through the lower bound $`-2^{31}`. Core C++ has no bitwise operators, no shifts and no unsigned types, so no program observes a bit pattern. The width lives only in `Int32.min` and `Int32.max`.

$$`\dfrac{n \in [-2^{31},\, 2^{31}-1]}{\mathsf{int32}\,n = \mathsf{int}\,n} \qquad \dfrac{n \notin [-2^{31},\, 2^{31}-1]}{\mathsf{int32}\,n = \mathsf{error}}`
:::

:::definition "dom_env" (parent := "dominios") (lean := "CoreCpp.Env, CoreCpp.Binding, CoreCpp.Env.lookup, CoreCpp.Env.extend, CoreCpp.Env.alias") (uses := "dom_loc")
The environment $`\rho` is a finite map from identifiers to locations. The notation $`\rho[x \mapsto \ell]` extends $`\rho`, and the most recent binding prevails.

Each binding records whether the declaration that made it allocated the location, as `τ x = e` does, or aliased an existing one, as the reference `τ& y = e` does. Block exit frees only the owned locations.

Inside a member body, `this` is an alias binding to the location of the receiver, made by the call and never freed by the return.
:::

:::definition "dom_store" (parent := "dominios") (lean := "CoreCpp.Store, CoreCpp.Store.read, CoreCpp.Store.write, CoreCpp.Store.alloc, CoreCpp.Store.allocMany, CoreCpp.Store.free, CoreCpp.Store.dom") (uses := "dom_loc, dom_val")
The store $`\sigma` is a finite map from locations to values. The operation $`\mathrm{alloc}(\sigma, v)` returns a fresh location $`\ell \notin \mathrm{dom}\,\sigma` and the store $`\sigma[\ell \mapsto v]`. The operation $`\sigma \setminus L` removes the locations of $`L` from the domain. Reading or writing outside the domain is `error`.
:::

:::definition "dom_closure" (parent := "dominios") (lean := "CoreCpp.Val, CoreCpp.Ty.isFn") (uses := "dom_val")
The value of a lambda is the closure $`\mathsf{closure}(x_1 \ldots x_k, \tau, c, [y_1 \mapsto w_1, \ldots, y_m \mapsto w_m])`, with the parameters, the result type, the body and the captured copies, one value per free variable of the body.

A closure is held by a `std::function` object of {bpref "std_function"}[], whose one location holds it as the target of the object, or $`\mathsf{null}` for the function with no target. No variable, field or element holds a closure directly, since a `std::function` is an object, reached by pointer or by reference.
:::

:::definition "dom_ctrl" (parent := "dominios") (lean := "CoreCpp.Ctrl") (uses := "dom_val")
The control result $`r` of a command is $`\mathsf{normal}` or $`\mathsf{ret}\,v`. A $`\mathsf{ret}` interrupts sequence, block and loop up to the call that consumes it.
:::

:::definition "dom_erro" (parent := "dominios") (lean := "CoreCpp.Error")
The result `error` is not a value of the language. It replaces the result of any dynamic judgment and propagates to the whole program.

Its causes are division by zero, `int` overflow, the dereference of `nullptr`, an index outside a vector, a negative vector size, a failed `assert`, a location outside $`\sigma`, an undeclared variable or function, wrong arity, a missing `return` in a non `void` function, a second `delete` of the same object, and a `delete` through a pointer to a base class without a virtual destructor.
:::

:::definition "dom_tenv" (parent := "dominios") (lean := "CoreCpp.TEnv, CoreCpp.TBind, CoreCpp.TEnv.lookup, CoreCpp.TEnv.isConst, CoreCpp.TEnv.bind, CoreCpp.TEnv.captured, CoreCpp.TEnv.self")
The typing context $`\Gamma` is a finite map from identifiers to types. The types are $`\mathsf{int}`, $`\mathsf{bool}`, $`\mathsf{void}`, a class $`C`, a pointer $`\tau*`, an instance $`L\langle\tau_1, \ldots, \tau_k\rangle` of a class template of the library, a function type $`\tau(\tau_1, \ldots, \tau_k)` as template argument, and the internal type $`\mathsf{nullptr\_t}` of `nullptr`.

Class types and the object types of the library are object types, they have no values, and no variable, parameter, result or field has one. An expression of object type occurs only as the operand of `.`, `[]` or `*`.

Each binding carries a mark, read only or not. The mark is set on every binding of the enclosing scope when the body of a lambda is checked, so that the copies of `[=]` are read and never written.
:::

:::definition "dom_funenv" (parent := "dominios") (lean := "CoreCpp.Decl, CoreCpp.Program, CoreCpp.Program.funs, CoreCpp.FunEnv, CoreCpp.FunEnv.lookup")
The function environment gathers the functions a program declares, a finite map from a name to its declaration, built once by the elaboration and implicit in every judgment, which reads it and never changes it. {bpref "gram_ast"}[] gives the syntax of the declarations it holds.
:::

:::definition "dom_classes" (parent := "dominios") (lean := "CoreCpp.ClassDecl, CoreCpp.Field, CoreCpp.Method, CoreCpp.Ctor, CoreCpp.Dtor, CoreCpp.Vis, CoreCpp.Program.classes, CoreCpp.Program.lookupClass, CoreCpp.Program.chain, CoreCpp.Program.allFields, CoreCpp.Program.findField, CoreCpp.Program.findMethod, CoreCpp.Program.subclass, CoreCpp.Program.hasVirtualDtor")
The classes of the program form the class table, a finite map from class names to declarations. A declaration has an optional base, fields and methods with their visibility, at most one constructor and at most one destructor.

The table gives, for a class, its chain up to the root base, every field of the chain with the class that declares it, the nearest method of a given name, the subclass relation and whether some class of the chain has a virtual destructor.

The type checker consults it for types, visibility and dispatch, and `new` and `delete` for the fields to allocate and to free. Names are qualified by their namespace, `N::C`.
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
The judgment $`\rho, \sigma \vdash e \Rightarrow_{\ell} \ell, \sigma'` states that the expression $`e` denotes the location $`\ell`. It holds for a variable, a dereferenced pointer, a field of an object, a field through a pointer, and a use of the library that gives a location, such as an element of a vector.
:::

:::definition "judg_ev_cmd" (parent := "juizos") (lean := "CoreCpp.Eval.cmd, CoreCpp.Eval.cmds") (uses := "judg_ev_expr, dom_ctrl")
The judgment $`\rho, \sigma \vdash c \Rightarrow r, \rho', \sigma'` states that the command $`c` yields the control $`r`, the environment $`\rho'` and the store $`\sigma'`. The output environment exists so that a declaration extends $`\rho` for the following commands, and the block discards the extension when it ends.
:::

:::definition "judg_trace" (parent := "juizos") (lean := "CoreCpp.M, CoreCpp.TState, CoreCpp.TraceAnte, CoreCpp.TraceCons, CoreCpp.TraceEntry, CoreCpp.Eval.traced, CoreCpp.renderTrace") (uses := "judg_ev_expr, judg_ev_cmd")
The evaluator runs in the monad $`M`, which carries the derivation tree. Each rule application records the instance of the rule it concludes, at its depth in the tree, with the antecedent and the consequent in parts.

The function `renderTrace` then lays the tree out as a derivation is written on the board, the premises over a line of inference, the conclusion under it and the rule name at the right.

A legend names the environments $`\rho_i`, the stores $`\sigma_j` and the subjects too long for a judgment, so every judgment fits one line, and a subtree wider than the page is written apart under a name $`\mathcal{D}_k`.
:::
