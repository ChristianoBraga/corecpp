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

Core C++ has three semantic components, three static judgments and three dynamic ones. The typing context $`\Gamma` maps identifiers to types. The environment $`\rho` maps identifiers to locations $`\ell`. The store $`\sigma` maps locations to values, and its domain is the set of live locations.

The notation is the sequent style of Kahn (1987). Hypotheses stand left of $`\vdash`, the subject right of it, and the result after $`\Rightarrow`.

:::author "christiano" (name := "Christiano Braga")
:::

:::group "dominios"
Semantic domains, in `CoreCpp/Semantics.lean` and `CoreCpp/Typing.lean`.
:::

:::group "juizos"
The judgments, in `CoreCpp/Typing.lean` and `CoreCpp/Eval.lean`, one Lean function each and one more for command sequences.
:::

# Domains

:::definition "dom_loc" (parent := "dominios") (lean := "CoreCpp.Loc")
A location $`\ell` is a natural number. The store keeps a counter of the next free location. Allocation takes the counter and increments it, and the removal of a location never decreases it, so locations are never reused.
:::

:::definition "dom_val" (parent := "dominios") (lean := "CoreCpp.Val, CoreCpp.Ty.default") (uses := "dom_int32, dom_loc")
The values are $`\mathsf{int}\,n`, $`\mathsf{bool}\,b`, $`\mathsf{void}`, the pointer $`\mathsf{loc}\,\ell`, the value $`\mathsf{null}` of `nullptr`, the object $`\mathsf{obj}\,C\,[f_1 \mapsto \ell_1, \ldots, f_n \mapsto \ell_n]`, a record of one location per field with its class tag, the instance $`\mathsf{lib}\,L\,[\ell_0, \ldots, \ell_{n-1}]` of an object type $`L` of the library, such as a vector, with one location per element, {bpref "std_vector"}[], and the closure of a lambda, {bpref "dom_closure"}[].

The value $`\mathsf{void}` is the result of a call to a function without return value, and the initial content of a field of type `std::function` before the constructor assigns it.

The tag of an object is the class it was created with, its fields are those of the whole chain of classes, the root base first, and the tag decides the dispatch of virtual methods and the destructors that `delete` runs. Objects and instances of object types of the library live in the store at their own location and are reached only by pointer or by reference.

The default value of a type, which `new` gives to every field and element, is $`\mathsf{int}\,0` for `int`, $`\mathsf{bool}\,\mathtt{false}` for `bool` and $`\mathsf{null}` for a pointer type. Object types have no default value, and every other type gets $`\mathsf{void}`.
:::

:::definition "dom_int32" (parent := "dominios") (lean := "CoreCpp.Int32.min, CoreCpp.Int32.max, CoreCpp.Int32.inRange, CoreCpp.Eval.int32")
The type `int` has 32 bits in two's complement. The partial operation $`\mathsf{int32}` returns the integer when it lies in the range and `error` otherwise.

C++17 fixes neither the width nor the representation of `int`. A plain `int` has the natural size suggested by the architecture of the execution environment, with a range of at least $`[-32767, 32767]` (N4659 §6.9.1 paragraph 2 and §21.3.5, N1570 §5.2.4.2.1). Its representation may be two's complement, ones' complement or signed magnitude (N4659 §6.9.1 paragraph 7). The range of `int` is therefore a property of the platform.

The ABI of the platform fixes it. The System V AMD64 psABI and AAPCS64 both give `int` 32 bits, and GCC supports only two's complement integer types.

An arithmetic result outside the range of `int` has undefined behaviour (N4659 §8 paragraph 4), and Core C++ makes it `error`. That boundary has to be the boundary of the implementation Core C++ is compared with, `g++` and clang on x86‑64 and ARM64. A wider range would give a value where C++ gives none, and a narrower one would give `error` where C++ gives a value.

The representation enters only through the lower bound $`-2^{31}`. Core C++ has no bitwise operators, no shifts and no unsigned types, so no program observes a bit pattern. The width lives only in `Int32.min` and `Int32.max`.

$$`\dfrac{n \in [-2^{31},\, 2^{31}-1]}{\mathsf{int32}\,n = \mathsf{int}\,n} \qquad \dfrac{n \notin [-2^{31},\, 2^{31}-1]}{\mathsf{int32}\,n = \mathsf{error}}`
:::

:::definition "dom_env" (parent := "dominios") (lean := "CoreCpp.Env, CoreCpp.Binding, CoreCpp.Env.lookup, CoreCpp.Env.extend, CoreCpp.Env.alias") (uses := "dom_loc")
The environment $`\rho` is a finite map from identifiers to locations. The notation $`\rho[x \mapsto \ell]` extends $`\rho`. The lookup $`\rho(x)` gives the location of the most recent binding of $`x`, so an inner declaration shadows an outer one.

Each binding records whether the declaration that made it allocated the location, as `τ x = e` does, or aliased an existing one, as the reference `τ& y = e` does. Scope exit, at the end of a block, of a `for` loop or of a call, frees only the owned locations.

Inside a member body, `this` is an alias binding to the location of the receiver, made by the call and never freed by the return.
:::

:::definition "dom_store" (parent := "dominios") (lean := "CoreCpp.Store, CoreCpp.Store.read, CoreCpp.Store.write, CoreCpp.Store.alloc, CoreCpp.Store.allocMany, CoreCpp.Store.free, CoreCpp.Store.dom, CoreCpp.Eval.readLoc") (uses := "dom_loc, dom_val")
The store $`\sigma` is a finite map from locations to values, with the counter of {bpref "dom_loc"}[]. Its domain $`\mathrm{dom}\,\sigma` is the set of live locations.

The read $`\sigma(\ell)` gives the content of $`\ell \in \mathrm{dom}\,\sigma`, and the write $`\sigma[\ell \mapsto v]` replaces it. The operation $`\mathrm{alloc}(\sigma, v)` returns a fresh location $`\ell \notin \mathrm{dom}\,\sigma` and the store $`\sigma[\ell \mapsto v]`, and its iteration allocates one location per value of a list, in order. The operation $`\sigma \setminus L` removes the locations of $`L` from the domain, at scope exit and at `delete`.

The evaluator turns a read or a write outside the domain into `error`.
:::

:::definition "dom_closure" (parent := "dominios") (lean := "CoreCpp.Val, CoreCpp.Ty.isFn") (uses := "dom_val")
The value of a lambda is the closure $`\mathsf{closure}(\tau_1\,x_1 \ldots \tau_k\,x_k,\ \tau,\ c,\ [y_1 \mapsto w_1, \ldots, y_m \mapsto w_m])`, with the parameters, the result type, the body and the captured copies. The copies are the values of the free variables of the body that $`\rho` binds when the lambda is evaluated.

The types `std::function<τ(τ₁, …, τₖ)>` of {bpref "std_function"}[] have closures as values. The function type `τ(τ₁, …, τₖ)` itself is only a template argument, and no variable has it.

A variable, a parameter or a field holds a closure. A field of type `std::function` holds $`\mathsf{void}` until the constructor assigns it, and a call through it before that is `error`. A vector element holds no closure, because `std::vector` rejects an element type of the library.
:::

:::definition "dom_ctrl" (parent := "dominios") (lean := "CoreCpp.Ctrl") (uses := "dom_val")
The control result $`r` of a command is $`\mathsf{normal}` or $`\mathsf{ret}\,v`. A $`\mathsf{ret}` interrupts sequence, block and loop up to the call that consumes it. A call whose body ends with $`\mathsf{normal}` gives $`\mathsf{void}` when the result type is `void`, and `error` otherwise.
:::

:::definition "dom_erro" (parent := "dominios") (lean := "CoreCpp.Error")
The result `error` is not a value of the language. No syntax produces, tests or catches it. It replaces the result of any dynamic judgment and propagates to the whole program, as abnormal termination does in C++.

Its causes are division by zero, `int` overflow, the dereference of `nullptr`, an index outside a vector, a negative vector size, a read or a write of a location outside $`\sigma`, an undeclared variable, a missing `return` in a non `void` function, the call of a value that is not a closure, a second `delete` of the same object, a `delete` through a pointer to a base class without a virtual destructor, and an error that a rule of the library gives, such as a failed `assert`.

Three further causes guard a program that skipped the type checker. They are an undeclared function, a call with the wrong number of arguments, and a value of the wrong form.
:::

:::definition "dom_tenv" (parent := "dominios") (lean := "CoreCpp.TEnv, CoreCpp.TBind, CoreCpp.TEnv.lookup, CoreCpp.TEnv.isConst, CoreCpp.TEnv.bind, CoreCpp.TEnv.captured, CoreCpp.TEnv.self")
The typing context $`\Gamma` is a finite map from identifiers to types. The types are $`\mathsf{int}`, $`\mathsf{bool}`, $`\mathsf{void}`, a class $`C`, a pointer $`\tau*`, an instance $`L\langle\tau_1, \ldots, \tau_k\rangle` of a class template of the library, a function type $`\tau(\tau_1, \ldots, \tau_k)` as template argument, and the internal type $`\mathsf{nullptr\_t}` of `nullptr`.

Class types and the object types of the library are object types. They have no values, and no variable, parameter by value, result or field has one. An expression of object type, such as `*p`, occurs only before `.` or `[]`, or as the argument of a reference parameter.

The lookup $`\Gamma(x)` gives the type of the most recent binding of $`x`. Inside a member body the binding $`\mathtt{this} \mapsto C*` gives the current class $`C`.

Each binding carries a mark, read only or not. The check of a lambda body sets the mark on every binding of the enclosing scope, so that the copies of `[=]` are read and never written.
:::

:::definition "dom_funenv" (parent := "dominios") (lean := "CoreCpp.Decl, CoreCpp.Program, CoreCpp.Program.funs, CoreCpp.FunEnv, CoreCpp.FunEnv.lookup, CoreCpp.FunEnv.lookupSig")
The function environment is the program itself, read as a finite map from a name to the overload set of its functions. The whole program serves, because `new` also needs the class table. It is fixed once the templates are instantiated and the calls annotated, and it is implicit in every judgment, which reads it and never changes it.

The lookup by name gives the first function of the name, and the lookup by signature gives the overload that the type checker chose. The syntax of the declarations is in {bpref "gram_ast"}[].
:::

:::definition "dom_classes" (parent := "dominios") (lean := "CoreCpp.ClassDecl, CoreCpp.Field, CoreCpp.Method, CoreCpp.Ctor, CoreCpp.Dtor, CoreCpp.Vis, CoreCpp.Program.classes, CoreCpp.Program.lookupClass, CoreCpp.Program.chain, CoreCpp.Program.allFields, CoreCpp.Program.findField, CoreCpp.Program.findMethod, CoreCpp.Program.subclass, CoreCpp.Program.hasVirtualDtor")
The classes of the program form the class table, a finite map from class names to declarations. A declaration has an optional base, fields and methods with their visibility, at most one constructor and at most one destructor.

The table gives, for a class, its chain up to the root base, every field of the chain with the class that declares it, the nearest method of a given name, the first of its overload set, the subclass relation and whether some class of the chain has a virtual destructor.

The type checker consults it for types, visibility and dispatch, and `new` and `delete` for the fields to allocate and to free. Names are qualified by their namespace, `N::C`.

The chain is `partial`, with a bound of 64 classes, so Lean records an opaque constant that carries the type and not the body, and no property of it is proved here.
:::

# Static judgments

:::definition "judg_ty_expr" (parent := "juizos") (lean := "CoreCpp.Expr, CoreCpp.Typing.expr, CoreCpp.TypeError, CoreCpp.T") (uses := "dom_tenv, gram_ast")
The judgment $`\Gamma \vdash e : \tau` states that the expression $`e` has type $`\tau` in the context $`\Gamma`. The class table is a parameter of every static judgment. Every constructor of `Expr` but the lambda has one rule or more.

A lambda has no type of its own. The judgment $`\Gamma \vdash e \triangleleft \tau` checks it at the `std::function` type its position expects.

A static judgment that fails gives a type error, and the type checker stops at the first one.

Some of the implementations are `partial`, so Lean records opaque constants that carry the type and not the body, and no property of them is proved here.
:::

:::definition "judg_ty_lval" (parent := "juizos") (lean := "CoreCpp.Typing.lval") (uses := "dom_tenv")
The judgment $`\Gamma \vdash_{\ell} e : \tau` holds for the expressions that denote a location. These are a variable not captured by a lambda, an unqualified field of `this`, `*e`, `e.f`, `e->f`, the indexing `e[i]` of a vector, and the call of a member that returns `τ&`, `operator[]` included.

The implementations are `partial`, so Lean records opaque constants that carry the type and not the body, and no property of them is proved here.
:::

:::definition "judg_ty_cmd" (parent := "juizos") (lean := "CoreCpp.Cmd, CoreCpp.Typing.cmd, CoreCpp.Typing.cmds") (uses := "judg_ty_expr, gram_ast")
The judgment $`\Gamma \vdash c \dashv \Gamma'` states that the command $`c` is well typed and extends $`\Gamma` to $`\Gamma'`, so that a declaration reaches the following commands of the sequence. A block, a conditional and a loop discard the extension. The return type $`\tau_r` of the enclosing function is an implicit parameter.

Some of the implementations are `partial`, so Lean records opaque constants that carry the type and not the body, and no property of them is proved here.
:::

# Dynamic judgments

:::definition "judg_ev_expr" (parent := "juizos") (lean := "CoreCpp.Eval.expr") (uses := "dom_env, dom_store, dom_val, dom_erro")
The judgment $`\rho, \sigma \vdash e \Rightarrow v, \sigma'` states that the expression $`e`, under the environment $`\rho` and the store $`\sigma`, evaluates to $`v` and yields $`\sigma'`. The store enters expressions because a call or a `new` inside an expression may change it.

The implementations are `partial`, so Lean records opaque constants that carry the type and not the body, and no property of them is proved here.
:::

:::definition "judg_ev_lval" (parent := "juizos") (lean := "CoreCpp.Eval.lval, CoreCpp.Eval.fieldLoc") (uses := "dom_env, dom_store, dom_loc")
The judgment $`\rho, \sigma \vdash e \Rightarrow_{\ell} \ell, \sigma'` states that the expression $`e` denotes the location $`\ell`. It holds for a variable, an unqualified field of `this`, a dereferenced pointer, a field of an object, a field through a pointer, the call of a member that returns a reference, and a use of the library that gives a location, such as an element of a vector.

The implementations are `partial`, so Lean records opaque constants that carry the type and not the body, and no property of them is proved here.
:::

:::definition "judg_ev_cmd" (parent := "juizos") (lean := "CoreCpp.Eval.cmd, CoreCpp.Eval.cmds, CoreCpp.Eval.fresh") (uses := "judg_ev_expr, dom_ctrl")
The judgment $`\rho, \sigma \vdash c \Rightarrow r, \rho', \sigma'` states that the command $`c` yields the control $`r`, the environment $`\rho'` and the store $`\sigma'`. The output environment exists so that a declaration extends $`\rho` for the following commands, and the block discards the extension when it ends. The block also removes from $`\sigma'` the locations of its owned bindings.

The implementations are `partial`, so Lean records opaque constants that carry the type and not the body, and no property of them is proved here.
:::

:::definition "judg_trace" (parent := "juizos") (lean := "CoreCpp.M, CoreCpp.TState, CoreCpp.TraceAnte, CoreCpp.TraceCons, CoreCpp.TraceEntry, CoreCpp.Eval.traced, CoreCpp.Eval.tracedLib, CoreCpp.renderTrace") (uses := "judg_ev_expr, judg_ev_cmd")
The evaluator runs in the monad $`M`, an exception monad over a state that carries the derivation trace. When tracing is enabled, each rule application records the instance of the rule it concludes, at its depth in the tree, with the antecedent and the consequent in parts. A rule whose premises fail records `error` as its consequent. The state survives the error, so the trace up to the failing rule is kept.

The log holds the instances in post order, each premise before its conclusion. The function `renderTrace` rebuilds the tree from the depths and lays it out as a derivation is written on the board, the premises over a line of inference, the conclusion under it and the rule name at the right.

A legend names the environments $`\rho_i`, the stores $`\sigma_j` and the subjects longer than 40 characters, so every judgment fits one line. A subtree wider than 100 columns is written apart under a name $`\mathcal{D}_k`.
:::
