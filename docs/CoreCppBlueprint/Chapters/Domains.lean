import Verso
import VersoManual
import VersoBlueprint
import CoreCpp.Semantics
import CoreCpp.Typing
import CoreCpp.Eval
import CoreCpp.Semantics.Static
import CoreCpp.Semantics.Dynamic

open Verso.Genre
open Verso.Genre.Manual
open Informal

set_option verso.blueprint.foldCodeBlocks true

#doc (Manual) "Judgments and domains" =>

Core C++ has three semantic components. The typing context $`\Gamma` maps identifiers to types. The environment $`\rho` maps identifiers to locations $`\ell`. The store $`\sigma` maps locations to values, and its domain is the set of live locations.

The notation is the sequent style of Kahn (1987). Hypotheses stand left of $`\vdash`, the subject right of it, and the result after $`\Rightarrow`.

Each judgment is an inductive proposition of `CoreCpp/Semantics/`, with one constructor per rule, and the type checker of `CoreCpp/Typing.lean` and the evaluator of `CoreCpp/Eval.lean` are the functions that interpret them, {bpref "judg_relations"}[]. Every node of this blueprint points at both, the relation and the function.

:::author "christiano" (name := "Christiano Braga")
:::

:::group "dominios"
Semantic domains, in `CoreCpp/Semantics.lean` and `CoreCpp/Typing.lean`.
:::

:::group "juizos"
The judgments, one inductive proposition each in `CoreCpp/Semantics/`, interpreted by one Lean function each in `CoreCpp/Typing.lean` and `CoreCpp/Eval.lean`.
:::

# Domains

:::definition "dom_loc" (parent := "dominios") (lean := "CoreCpp.Loc")
A location $`\ell` is a natural number. Locations are never reused.
:::

:::definition "dom_val" (parent := "dominios") (lean := "CoreCpp.Val, CoreCpp.Ty.default") (uses := "dom_int32, dom_loc")
The values are $`\mathsf{int}\,n`, $`\mathsf{bool}\,b`, $`\mathsf{void}`, the pointer $`\mathsf{loc}\,\ell`, the value $`\mathsf{null}` of `nullptr`, the object $`\mathsf{obj}\,C\,[f_1 \mapsto \ell_1, \ldots, f_n \mapsto \ell_n]`, a record of one location per field with its class tag, and the instance $`\mathsf{lib}\,L\,[\ell_0, \ldots, \ell_{n-1}]` of an object type $`L` of the library, such as a vector, with one location per element, {bpref "std_vector"}[].

The value $`\mathsf{void}` is the result of a call to a function without return value. The closure is a value too, {bpref "dom_closure"}[].

The tag of an object is the class it was created with, its fields are those of the whole chain of classes, the root base first, and the tag decides the dispatch of virtual methods and the destructors that `delete` runs. Objects and instances of object types of the library live in the store at their own location and are reached only through pointers and references.

The default value of a type, which `new` gives to every field and to every element of a vector, is $`\mathsf{int}\,0`, $`\mathsf{bool}\,\mathtt{false}` or $`\mathsf{null}`.
:::

:::definition "dom_int32" (parent := "dominios") (lean := "CoreCpp.Int32.min, CoreCpp.Int32.max, CoreCpp.Int32.inRange, CoreCpp.Eval.int32")
The type `int` has 32 bits in two's complement. Every rule that gives an integer has the premise $`n \in [-2^{31},\, 2^{31}-1]`, the test `Int32.inRange`, so a result outside the range has no derivation. The function $`\mathsf{int32}` of the evaluator returns the integer when it lies in the range and `error` otherwise.

C++17 fixes neither the width nor the representation of `int`. A plain `int` has the natural size suggested by the architecture of the execution environment, with a range of at least $`[-32767, 32767]` (N4659 §6.9.1 paragraph 2 and §21.3.5, N1570 §5.2.4.2.1). Its representation may be two's complement, ones' complement or signed magnitude (N4659 §6.9.1 paragraph 7). The range of `int` is therefore a property of the platform.

The ABI of the platform fixes it. The System V AMD64 psABI and AAPCS64 both give `int` 32 bits, and GCC supports only two's complement integer types.

An arithmetic result outside the range of `int` has undefined behaviour (N4659 §8 paragraph 4), and Core C++ makes it `error`. That boundary has to be the boundary of the implementation Core C++ is compared with, `g++` and clang on x86‑64 and ARM64. A wider range would give a value where C++ gives none, and a narrower one would give `error` where C++ gives a value.

The representation enters only through the lower bound $`-2^{31}`. Core C++ has no bitwise operators, no shifts and no unsigned types, so no program observes a bit pattern. The width lives in `Int32.min` and `Int32.max`, and in the largest integer literal the lexer of {bpref "lex_automaton"}[] accepts.

$$`\dfrac{n \in [-2^{31},\, 2^{31}-1]}{\mathsf{int32}\,n = \mathsf{int}\,n}`
:::

:::definition "dom_env" (parent := "dominios") (lean := "CoreCpp.Env, CoreCpp.Binding, CoreCpp.Env.lookup, CoreCpp.Env.extend, CoreCpp.Env.alias, CoreCpp.Env.fresh") (uses := "dom_loc")
The environment $`\rho` is a finite map from identifiers to locations. The notation $`\rho[x \mapsto \ell]` extends $`\rho`, and the most recent binding prevails.

Each binding records whether the declaration that made it allocated the location, as `τ x = e` does, or aliased an existing one, as the reference `τ& y = e` does. Block exit frees only the owned locations, the owned bindings of $`\rho' \setminus \rho` that `Env.fresh` gives.

Inside a member body, `this` is an alias binding to the location of the receiver, made by the call and never freed by the return.
:::

:::definition "dom_store" (parent := "dominios") (lean := "CoreCpp.Store, CoreCpp.Store.read, CoreCpp.Store.write, CoreCpp.Store.alloc, CoreCpp.Store.allocMany, CoreCpp.Store.free, CoreCpp.Store.dom") (uses := "dom_loc, dom_val")
The store $`\sigma` is a finite map from locations to values, with a counter of the next location. The operation $`\mathrm{alloc}(\sigma, v)` returns the location of the counter, $`\ell \notin \mathrm{dom}\,\sigma`, and the store $`\sigma[\ell \mapsto v]` with the counter advanced, and `allocMany` allocates one location per value, in order. The operation $`\sigma \setminus L` removes the locations of $`L` from the domain and leaves the counter, so a freed location is never allocated again. A rule that reads or writes a location has the premise $`\ell \in \mathrm{dom}\,\sigma`, so an access outside the domain has no derivation, and the evaluator gives `error`.
:::

:::definition "dom_closure" (parent := "dominios") (lean := "CoreCpp.Val, CoreCpp.Ty.isFn") (uses := "dom_val")
The value of a lambda is the closure $`\mathsf{closure}(x_1 \ldots x_k, \tau, c, [y_1 \mapsto w_1, \ldots, y_m \mapsto w_m])`, with the parameters, the result type, the body and the captured copies, one value per variable of the body, other than a parameter, that the environment binds.

A closure is held by a `std::function` object of {bpref "std_function"}[], whose one location holds it as the target of the object, or $`\mathsf{null}` for the function with no target. No variable, field or element holds a closure directly, since a `std::function` is an object, reached by pointer or by reference. The type of a lambda is the function type $`\tau(\tau_1, \ldots, \tau_k)`, which `Ty.isFn` recognises, and it occurs only as the template argument of `std::function`.
:::

:::definition "dom_ctrl" (parent := "dominios") (lean := "CoreCpp.Ctrl") (uses := "dom_val")
The control result $`r` of a command is $`\mathsf{normal}` or $`\mathsf{ret}\,v`. A $`\mathsf{ret}` interrupts sequence, block and loop up to the call that consumes it.
:::

:::definition "dom_erro" (parent := "dominios") (lean := "CoreCpp.Error")
The result `error` is not a value of the language. In the relations it is the absence of a derivation. Whatever C++17 leaves undefined fails a premise of every rule that could reach it, $`\sigma(\ell) = v`, $`n_2 \neq 0`, $`n \in [-2^{31}, 2^{31}-1]`, $`0 \le i < n`, and the subject has no derivation, with nothing to propagate. The evaluator, which runs the relations, reports the case as `error`, with a message and the exit code 134, and the error replaces the result of the whole program.

Its causes are division by zero, `int` overflow, the dereference of `nullptr`, an index outside a vector, a negative vector size, a failed `assert`, the call of a `std::function` with no target, a location outside $`\sigma`, a missing `return` in a non `void` function, a second `delete` of the same object, a `delete` through a pointer to a base class without a virtual destructor, and the exhaustion of the fuel of the evaluator, a bound on the depth of a derivation that no program reaches. The causes `undeclaredVariable`, `undeclaredFunction`, `arity`, `typeError` and `notCallable` guard the evaluator against a program that skipped the type checker.
:::

:::definition "dom_tenv" (parent := "dominios") (lean := "CoreCpp.TEnv, CoreCpp.TBind, CoreCpp.TEnv.lookup, CoreCpp.TEnv.isConst, CoreCpp.TEnv.bind, CoreCpp.TEnv.captured, CoreCpp.TEnv.self, CoreCpp.Semantics.IsObject, CoreCpp.Semantics.HasValues, CoreCpp.Semantics.Storable, CoreCpp.Semantics.Bindable")
The typing context $`\Gamma` is a finite map from identifiers to types. The types are $`\mathsf{int}`, $`\mathsf{bool}`, $`\mathsf{void}`, a class $`C`, a pointer $`\tau*`, an instance $`L\langle\tau_1, \ldots, \tau_k\rangle` of a class template of the library, a function type $`\tau(\tau_1, \ldots, \tau_k)` as template argument, and the internal type $`\mathsf{nullptr\_t}` of `nullptr`.

Class types and the types of the library whose module gives `new` a signature, `std::vector` and `std::function`, are object types, `IsObject`. They have no values, and no variable, by value parameter, result or field has one, `Storable`. A reference parameter and a local reference may have an object type, `Bindable`. An expression of object type, such as `*p`, never stands where a value is expected, `HasValues`. It occurs as the left operand of `.`, as the operand of `[]` or of an operator member, as the callee of `(*f)(ē)`, as the argument of a reference parameter and as the initialiser of a local reference.

Each binding carries a mark, read only or not. The mark is set on every binding of the enclosing scope when the body of a lambda is checked, so that the copies of `[=]` are read and never written. The binding of `this` gives the current class, `TEnv.self`, inside a member body.
:::

:::definition "dom_funenv" (parent := "dominios") (lean := "CoreCpp.Decl, CoreCpp.Program, CoreCpp.Program.funs, CoreCpp.Program.funsNamed, CoreCpp.Program.libDecls, CoreCpp.FunEnv, CoreCpp.FunEnv.lookup, CoreCpp.FunEnv.lookupSig, CoreCpp.Program.pickFun")
The function environment is the program $`p` seen as a finite map from a name to the overload set of the functions of that name, `funsNamed`, and to the declarations of the library, `libDecls`. The program is a parameter of every relation, which reads it and never changes it. The evaluator selects a function by the signature the type checker wrote into the call, `lookupSig`, and the static relation by `pickFun`. {bpref "gram_ast"}[] gives the syntax of the declarations it holds.
:::

:::definition "dom_classes" (parent := "dominios") (lean := "CoreCpp.ClassDecl, CoreCpp.Field, CoreCpp.Method, CoreCpp.Ctor, CoreCpp.Dtor, CoreCpp.Vis, CoreCpp.Program.classes, CoreCpp.Program.lookupClass, CoreCpp.Program.chain, CoreCpp.Program.allFields, CoreCpp.Program.findField, CoreCpp.Program.findMethod, CoreCpp.Program.findMethods, CoreCpp.Program.subclass, CoreCpp.Program.hasVirtualDtor")
The classes of the program form the class table, a finite map from class names to declarations. A declaration has an optional base, fields and methods with their visibility, at most one constructor and at most one destructor.

The table gives, for a class, its chain up to the root base, every field of the chain with the class that declares it, the nearest method of a given name, the overload set of a method name, one method per signature, the subclass relation and whether some class of the chain has a virtual destructor.

The type checker consults it for types, visibility and dispatch, and `new` and `delete` for the fields to allocate and to free. Names are qualified by their namespace, `N::C`.
:::

# Relations and interpreters

:::definition "judg_relations" (parent := "juizos") (lean := "CoreCpp.Semantics.HasType, CoreCpp.Semantics.LHasType, CoreCpp.Semantics.Accept, CoreCpp.Semantics.Check, CoreCpp.Semantics.Checks, CoreCpp.Semantics.WF, CoreCpp.Semantics.FunOk, CoreCpp.Semantics.ClassOk, CoreCpp.Semantics.ProgramOk, CoreCpp.Semantics.Eval, CoreCpp.Semantics.LEval, CoreCpp.Semantics.Exec, CoreCpp.Semantics.Execs, CoreCpp.Semantics.Runs, CoreCpp.Typing.wellFormed, CoreCpp.Typing.typingFuel, CoreCpp.runWith") (uses := "dom_tenv, dom_env, dom_store, dom_erro")
The semantics is a set of inductive propositions, one per judgment, one constructor per rule, named as the rule is named in this blueprint, in `CoreCpp/Semantics/Static.lean` and `Dynamic.lean`, and the relations of the modules of the library in `Library.lean`. A constructor is laid out as a rule is written on the board, the premises one per line, the inference line with the name, and the conclusion under it. The program $`p` is a parameter of every relation, the function table and the class table.

| Judgment | Relation | Notation in Lean | Interpreter |
| --- | --- | --- | --- |
| $`\Gamma \vdash e : \tau` | `HasType p Γ e τ` | `Γ ⊢ e : τ` | `Typing.expr` |
| $`\Gamma \vdash_{\ell} e : \tau` | `LHasType p Γ e τ` | `Γ ⊢ₗ e : τ` | `Typing.lval` |
| $`\Gamma \vdash e \lhd \tau` | `Accept p Γ e τ` | `Γ ⊢ e ◁ τ` | `Typing.accept` |
| $`\Gamma \vdash c \dashv \Gamma'` | `Check p τᵣ Γ c Γ'` | `⟨Γ, τᵣ⟩ ⊢ c ⊣ Γ'` | `Typing.cmd` |
| $`\Gamma \vdash \bar{c} \dashv \Gamma'` | `Checks p τᵣ Γ cs Γ'` | `⟨Γ, τᵣ⟩ ⊢ cs ⊣* Γ'` | `Typing.cmds` |
| $`\Gamma \vdash \tau\ \mathsf{ok}` | `WF p τ` | | `Typing.wellFormed` |
| $`\vdash f`, $`\vdash C`, $`\vdash p` | `FunOk`, `ClassOk`, `ProgramOk` | | `Typing.fn`, `Typing.cls`, `check` |
| $`\rho, \sigma \vdash e \Rightarrow v, \sigma'` | `Eval p ρ σ e v σ'` | `⟨ρ, σ⟩ ⊢ e ⇒ v, σ'` | `Eval.expr` |
| $`\rho, \sigma \vdash e \Rightarrow_{\ell} \ell, \sigma'` | `LEval p ρ σ e ℓ σ'` | `⟨ρ, σ⟩ ⊢ e ⇒ₗ ℓ, σ'` | `Eval.lval` |
| $`\rho, \sigma \vdash c \Rightarrow r, \rho', \sigma'` | `Exec p ρ σ c r ρ' σ'` | `⟨ρ, σ⟩ ⊢ c ⇒ r, ρ', σ'` | `Eval.cmd` |
| $`\rho, \sigma \vdash \bar{c} \Rightarrow r, \rho', \sigma'` | `Execs p ρ σ cs r ρ' σ'` | `⟨ρ, σ⟩ ⊢ cs ⇒* r, ρ', σ'` | `Eval.cmds` |
| $`p \Rightarrow v` | `Runs p v` | | `run` |

The configuration $`\langle\rho, \sigma\rangle`, and $`\langle\Gamma, \tau_r\rangle` for a command with the result type of its body, are in angle brackets in Lean, and a sequence takes a starred arrow, two concessions to the parser of Lean. The relation is the specification and the function its interpreter. Every recursive function of the type checker and of the evaluator takes as first argument the fuel, a bound on the depth of a derivation, and recurses on it. The constant `typingFuel` and the function `runWith` set it to $`10^6`, and its exhaustion is the error `outOfFuel`. With the fuel, the functions admit two theorems, soundness, that a result of the function is a derivation of the relation, and completeness, that a derivation is reached with enough fuel. The structure follows Radix, the DSL of Leonardo de Moura's tutorial at ETAPS 2026.

The judgments on declarations, $`\vdash f`, $`\vdash C` and $`\vdash p`, are structures of named conditions rather than relations with one constructor, since their conditions are side conditions on the declarations and not premises on subterms. The selection of an overload, {bpref "overload_pick"}[], is the work of the type checker, which writes its choice into the call, and the relation reads it.
:::

# Static judgments

:::definition "judg_ty_expr" (parent := "juizos") (lean := "CoreCpp.Expr, CoreCpp.Typing.expr, CoreCpp.Semantics.HasType") (uses := "dom_tenv, gram_ast, judg_relations")
The judgment $`\Gamma \vdash e : \tau` states that the expression $`e` has type $`\tau` in the context $`\Gamma`. Each rule concludes about one constructor of `Expr`, and a constructor may have several rules, as the call of a name has T-Call, T-CallLib, T-CallThis and T-CallFn. A lambda has no rule of this judgment. The judgment $`\Gamma \vdash e \lhd \tau` accepts it at its function type, and accepts any other expression by its type.
:::

:::definition "judg_ty_lval" (parent := "juizos") (lean := "CoreCpp.Typing.lval, CoreCpp.Semantics.LHasType") (uses := "dom_tenv, judg_relations")
The judgment $`\Gamma \vdash_{\ell} e : \tau` holds for the expressions that denote a location, a variable not captured by copy, an unqualified field of `this`, `*e`, `e.f`, `e->f`, the element `e[i]` of a vector, an `operator[]` or a method call whose member returns a reference, and a conditional whose two branches denote locations of one type.
:::

:::definition "judg_ty_cmd" (parent := "juizos") (lean := "CoreCpp.Cmd, CoreCpp.Typing.cmd, CoreCpp.Typing.cmds, CoreCpp.Semantics.Check, CoreCpp.Semantics.Checks") (uses := "judg_ty_expr, gram_ast, judg_relations")
The judgment $`\Gamma \vdash c \dashv \Gamma'` states that the command $`c` is well typed and extends $`\Gamma` to $`\Gamma'`, so that a declaration reaches the following commands of the sequence. The result type $`\tau_r` of the enclosing body, a function, a member or a lambda, is a parameter of the relation, written $`\langle\Gamma, \tau_r\rangle` in Lean.
:::

# Dynamic judgments

:::definition "judg_ev_expr" (parent := "juizos") (lean := "CoreCpp.Eval.expr, CoreCpp.Semantics.Eval") (uses := "dom_env, dom_store, dom_val, dom_erro, judg_relations")
The judgment $`\rho, \sigma \vdash e \Rightarrow v, \sigma'` states that the expression $`e`, under the environment $`\rho` and the store $`\sigma`, evaluates to $`v` and yields $`\sigma'`. The store enters expressions because a call or a `new` inside an expression may change it.
:::

:::definition "judg_ev_lval" (parent := "juizos") (lean := "CoreCpp.Eval.lval, CoreCpp.Semantics.LEval") (uses := "dom_env, dom_store, dom_loc, judg_relations")
The judgment $`\rho, \sigma \vdash e \Rightarrow_{\ell} \ell, \sigma'` states that the expression $`e` denotes the location $`\ell`. It holds for a variable, an unqualified field of `this`, a dereferenced pointer, a field of an object, a field through a pointer, a call of a member that returns a reference, a use of the library that gives a location, such as an element of a vector, and a conditional, which denotes the location of the chosen branch.
:::

:::definition "judg_ev_cmd" (parent := "juizos") (lean := "CoreCpp.Eval.cmd, CoreCpp.Eval.cmds, CoreCpp.Semantics.Exec, CoreCpp.Semantics.Execs") (uses := "judg_ev_expr, dom_ctrl, judg_relations")
The judgment $`\rho, \sigma \vdash c \Rightarrow r, \rho', \sigma'` states that the command $`c` yields the control $`r`, the environment $`\rho'` and the store $`\sigma'`. The output environment exists so that a declaration extends $`\rho` for the following commands, and the block discards the extension and frees its owned locations when it ends.
:::

:::definition "judg_trace" (parent := "juizos") (lean := "CoreCpp.M, CoreCpp.TState, CoreCpp.TraceAnte, CoreCpp.TraceCons, CoreCpp.TraceEntry, CoreCpp.Eval.traced, CoreCpp.Eval.tracedLib, CoreCpp.Eval.libStep, CoreCpp.renderTrace") (uses := "judg_ev_expr, judg_ev_cmd")
The evaluator runs in the monad $`M`, which carries the trace of the derivation. When tracing is enabled, each rule application records the instance of the rule it concludes, or the error, at its depth in the tree, with the antecedent and the consequent in parts. A premise of the library is recorded under the rule of its module, such as V-New or F-New. The log is in post order.

The function `renderTrace` rebuilds the tree from the log and lays it out as a derivation is written on the board, the premises over a line of inference, the conclusion under it and the rule name at the right.

A legend names the environments $`\rho_i`, the stores $`\sigma_j` and the subjects too long for a judgment, so every judgment fits one line, and a subtree wider than the page is written apart under a name $`\mathcal{D}_k`.
:::
