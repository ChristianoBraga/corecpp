import Verso
import VersoManual
import VersoBlueprint
import CoreCpp.Std
import CoreCpp.Typing
import CoreCpp.Eval
import CoreCpp.Semantics.Library

open Verso.Genre
open Verso.Genre.Manual
open Informal

set_option verso.blueprint.foldCodeBlocks true

#doc (Manual) "The standard library" =>

The headers of Core C++ declare the entities of the library without a body, the class templates `std::vector` and `std::function` and the function `assert`. Each declared name has a module, which holds relations and functions. The relations, in `CoreCpp/Semantics/Library.lean`, specify the entity in the forms of the judgments of the language. The rules of the language take them as premises. The functions, in `CoreCpp/Std/`, implement them, and the type checker and the evaluator call a function where a rule has its relation as a premise.

The type checker and the evaluator know no module by name. They find the module of a declared name. A use of an undeclared entity is a type error, so a program uses the library only through its `#include`.

Nothing of this is built into the syntax. The grammar has no production and the lexer no reserved word for the library. The declaration `namespace std` opens an ordinary namespace, and `std::vector` is an ordinary qualified name. The case of the name tells a class of the library, lowercase, from a class of the program, uppercase.

:::group "library"
The library, its interface and its modules.
:::

# Interface

:::definition "std_library" (parent := "library") (lean := "CoreCpp.Semantics.StaticModule, CoreCpp.Semantics.Module, CoreCpp.Semantics.staticOf, CoreCpp.Semantics.moduleOf, CoreCpp.Std.StaticFns, CoreCpp.Std.Fns, CoreCpp.Std.staticFnsOf, CoreCpp.Std.fnsOf, CoreCpp.Std.isObject") (uses := "pp_headers, judg_ty_expr, judg_ev_expr")
A module $`L` gives at most five static relations and four dynamic ones. Each relation other than the predicate $`\mathrm{wf}_L` is an instance of a judgment of the language. In each, $`\bar{\tau}` denotes the template arguments of the instance. A relation the entity does not have is left at $`\mathsf{False}`.

| Relation | Meaning | Lean |
| --- | --- | --- |
| $`\mathrm{wf}_L(\bar{\tau})` | the instance is well formed | `wf` |
| $`\Gamma \vdash_L \mathtt{new} : \tau_1 \times \cdots \times \tau_k \to \tau` | a signature of `new` | `new` |
| $`\Gamma \vdash_L \mathtt{operator[]} : \tau_1 \to \tau` | the signature of indexing, a location | `index` |
| $`\Gamma \vdash_L \mathtt{delete}\ \mathsf{ok}` | an instance is deleted | `delete` |
| $`\Gamma \vdash_L f : \tau_1 \times \cdots \times \tau_k \to \tau` | the signature of a function without a body | `call` |
| $`\sigma \vdash_L \mathtt{new}\langle\bar{\tau}\rangle(v_1, \ldots, v_k) \Rightarrow v, \sigma'` | the creation of an instance | `new` |
| $`\sigma \vdash_L v[i] \Rightarrow_{\ell} \ell, \sigma'` | the location of an element | `index` |
| $`\sigma \vdash_L \mathtt{delete}\ v \Rightarrow \sigma'` | the store after the instance leaves it | `delete` |
| $`\sigma \vdash_L f(v_1, \ldots, v_k) \Rightarrow v, \sigma'` | the call of a function without a body | `call` |

The static relations form `StaticModule` and the dynamic ones `Module`, found by the declared name through `staticOf` and `moduleOf`. The functions `StaticFns` and `Fns` implement them, found through `staticFnsOf` and `fnsOf`. Each dynamic function names the rule it concludes, for the trace. The predicate $`\mathrm{wf}_L` is a premise of the rule WF-Lib of {bpref "dom_types"}[]. The module of `assert` leaves it at $`\mathsf{False}`, since `assert` is no type.

An object type is a class or an entity of the library whose module gives `new` a signature, `Std.isObject`. Its values live in the store and are reached by pointer or by reference, so no variable, field, parameter or result has the type by value. A vector and a `std::function` are objects.
:::

:::definition "std_uses" (parent := "library") (lean := "CoreCpp.Typing.expr, CoreCpp.Typing.lval, CoreCpp.Typing.cmd, CoreCpp.Eval.expr, CoreCpp.Eval.lval, CoreCpp.Eval.cmd, CoreCpp.Eval.libStep, CoreCpp.Semantics.HasType, CoreCpp.Semantics.LHasType, CoreCpp.Semantics.Eval, CoreCpp.Semantics.LEval, CoreCpp.Semantics.Exec, CoreCpp.Semantics.Check") (uses := "std_library, judg_ty_lval, judg_ev_lval, dom_store")
The rules of the language for a subject of the library take the relation of its module as a premise. The arguments are values, evaluated left to right, and a module premise with no derivation makes the use `error` in the evaluator.

$$`\dfrac{\Gamma \vdash L\langle\bar{\tau}\rangle\ \mathsf{ok} \qquad \Gamma \vdash_L \mathtt{new} : \tau_1 \times \cdots \times \tau_k \to \tau \qquad \Gamma \vdash e_i \lhd \tau_i}{\Gamma \vdash \mathtt{new}\ L\langle\bar{\tau}\rangle(e_1, \ldots, e_k) : \tau}\;\textsf{(T-NewLib)}`

$$`\dfrac{f \notin \Gamma \qquad f \text{ no function of the program, declared by a header} \qquad \Gamma \vdash_f f : \tau_1 \times \cdots \times \tau_k \to \tau \qquad \Gamma \vdash e_i \lhd \tau_i}{\Gamma \vdash f(e_1, \ldots, e_k) : \tau}\;\textsf{(T-CallLib)}`

$$`\dfrac{\Gamma \vdash e : L\langle\bar{\tau}\rangle \qquad \Gamma \vdash_L \mathtt{operator[]} : \tau_1 \to \tau \qquad \Gamma \vdash i \lhd \tau_1}{\Gamma \vdash e[i] : \tau}\;\textsf{(T-IndexLib)}`

$$`\dfrac{\Gamma \vdash e : L\langle\bar{\tau}\rangle \qquad \Gamma \vdash_L \mathtt{operator[]} : \tau_1 \to \tau \qquad \Gamma \vdash i \lhd \tau_1}{\Gamma \vdash_{\ell} e[i] : \tau}\;\textsf{(T-LocIndexLib)}`

$$`\dfrac{\Gamma \vdash e : L\langle\bar{\tau}\rangle* \qquad L\langle\bar{\tau}\rangle \text{ an object type} \qquad \Gamma \vdash_L \mathtt{delete}\ \mathsf{ok}}{\Gamma \vdash \mathtt{delete}\ e \dashv \Gamma}\;\textsf{(T-DeleteLib)}`

$$`\dfrac{\rho, \sigma_{i-1} \vdash e_i \Rightarrow v_i, \sigma_i \quad (1 \le i \le k) \qquad \sigma_k \vdash_L \mathtt{new}\langle\bar{\tau}\rangle(v_1, \ldots, v_k) \Rightarrow v, \sigma'}{\rho, \sigma_0 \vdash \mathtt{new}\ L\langle\bar{\tau}\rangle(e_1, \ldots, e_k) \Rightarrow v, \sigma'}\;\textsf{(NewLib)}`

$$`\dfrac{\begin{array}{c} f \notin \rho \qquad f \text{ no function of the program, declared by a header} \\ \rho, \sigma_{i-1} \vdash e_i \Rightarrow v_i, \sigma_i \quad (1 \le i \le k) \qquad \sigma_k \vdash_f f(v_1, \ldots, v_k) \Rightarrow v, \sigma' \end{array}}{\rho, \sigma_0 \vdash f(e_1, \ldots, e_k) \Rightarrow v, \sigma'}\;\textsf{(CallLib)}`

$$`\dfrac{\rho, \sigma \vdash e \Rightarrow \mathsf{lib}\,L\,\bar{\ell}, \sigma_1 \qquad \rho, \sigma_1 \vdash i \Rightarrow v, \sigma_2 \qquad \sigma_2 \vdash_L (\mathsf{lib}\,L\,\bar{\ell})[v] \Rightarrow_{\ell} \ell, \sigma'}{\rho, \sigma \vdash e[i] \Rightarrow_{\ell} \ell, \sigma'}\;\textsf{(LocIndex)}`

The receiver is evaluated before the index, the order C++17 fixes for subscripting (N4659 §8.2.1 ¶1), also when `operator[]` is overloaded (N4659 §16.3.1.2 ¶2). In a value position `e[i]` is read by the rule `Read`.

$$`\dfrac{\begin{array}{c} \rho, \sigma \vdash e \Rightarrow \mathsf{loc}\,\ell, \sigma_0\qquad \sigma_0(\ell) = \mathsf{lib}\,L\,\bar{\ell} \\ \sigma_0 \vdash_L \mathtt{delete}\ (\mathsf{lib}\,L\,\bar{\ell}) \Rightarrow \sigma_1 \end{array}}{\rho, \sigma \vdash \mathtt{delete}\ e \Rightarrow \mathsf{normal}, \rho, \sigma_1 \setminus \{\ell\}}\;\textsf{(DeleteLib)}`

The command `delete e` on a pointer to an instance frees what the module owns and then the location of the instance.
:::

# Headers

:::definition "std_vector" (parent := "library") (lean := "CoreCpp.Semantics.Vector.TNew, CoreCpp.Semantics.Vector.TIndex, CoreCpp.Semantics.Vector.TDelete, CoreCpp.Semantics.Vector.New, CoreCpp.Semantics.Vector.Index, CoreCpp.Semantics.Vector.Delete, CoreCpp.Std.Vector.statics, CoreCpp.Std.Vector.fns, CoreCpp.Std.Vector.elementOk, CoreCpp.Semantics.Vector.isElement, CoreCpp.Semantics.Vector.statics") (uses := "std_library, std_uses")
The header `<vector>` declares `template <typename T> class vector;` in `namespace std`. A vector is an object, created with `new` and reached by pointer. Its value $`\mathsf{lib}\ \mathtt{std{:}{:}vector}\,[\ell_0, \ldots, \ell_{n-1}]` holds one location per element.

The element type has values and a default, so it is not a class, a type of the library, a function type, `void` or $`\mathsf{nullptr\_t}`. A vector therefore holds an object only through a pointer to it.

The predicate $`\mathrm{wf}_{\mathit{vector}}` states this condition with `Vector.isElement`.

$$`\begin{array}{lcl} \mathrm{wf}_{\mathit{vector}}(\bar{\tau}) & \iff & \bar{\tau} = \tau \ \land\ (\tau = \mathsf{int} \lor \tau = \mathsf{bool} \lor \tau = \tau'*) \end{array}`

$$`\dfrac{}{\Gamma \vdash_{\mathit{vector}} \mathtt{new} : \mathsf{int} \to \mathtt{std{:}{:}vector}\langle\tau\rangle*}\;\textsf{(TV-New)}`

$$`\dfrac{}{\Gamma \vdash_{\mathit{vector}} \mathtt{operator[]} : \mathsf{int} \to \tau}\;\textsf{(TV-Index)}`

$$`\dfrac{}{\Gamma \vdash_{\mathit{vector}} \mathtt{delete}\ \mathsf{ok}}\;\textsf{(TV-Delete)}`

Indexing gives a location, so `v[i]` may stand on the left of an assignment and bind a reference.

$$`\dfrac{\begin{array}{c} k \ge 0\qquad (\ell_i, \sigma_i) = \mathrm{alloc}(\sigma_{i-1}, \mathrm{default}\,\tau)\ (1 \le i \le k) \\ (\ell, \sigma') = \mathrm{alloc}(\sigma_k, \mathsf{lib}\ \mathtt{std{:}{:}vector}\,[\ell_1, \ldots, \ell_k]) \end{array}}{\sigma_0 \vdash_{\mathit{vector}} \mathtt{new}\langle\tau\rangle(k) \Rightarrow \mathsf{loc}\,\ell, \sigma'}\;\textsf{(V-New)}`

$$`\dfrac{0 \le i < n}{\sigma \vdash_{\mathit{vector}} (\mathsf{lib}\ \mathtt{std{:}{:}vector}\,[\ell_0, \ldots, \ell_{n-1}])[i] \Rightarrow_{\ell} \ell_i, \sigma}\;\textsf{(V-Index)}`

$$`\dfrac{}{\sigma \vdash_{\mathit{vector}} \mathtt{delete}\ (\mathsf{lib}\ \mathtt{std{:}{:}vector}\,[\ell_0, \ldots, \ell_{n-1}]) \Rightarrow \sigma \setminus \{\ell_0, \ldots, \ell_{n-1}\}}\;\textsf{(V-Delete)}`

A negative size and an index outside $`[0, n)` have no derivation, and the evaluator gives `error` for them. C++17 defines `a[n]` as `*(a.begin() + n)` with no bounds check, which only `at` performs (N4659 §26.2.3, Table 88).
:::

:::definition "std_function" (parent := "library") (lean := "CoreCpp.Semantics.Function.TNew, CoreCpp.Semantics.Function.TDelete, CoreCpp.Semantics.Function.New, CoreCpp.Semantics.Function.Delete, CoreCpp.Std.Function.statics, CoreCpp.Std.Function.fns, CoreCpp.Ty.function, CoreCpp.Semantics.Function.statics") (uses := "std_library, std_uses, fun_accept, fun_callfn")
The header `<functional>` declares `template <typename F> class function;` in `namespace std`. The template argument is a function type $`F = \tau(\tau_1, \ldots, \tau_k)`. A `std::function<F>` is an object, since its module gives `new` a signature. It is created with `new`, reached by pointer and destroyed with `delete`. Its value $`\mathsf{lib}\ \mathtt{std{:}{:}function}\,[\ell_t]` holds one location $`\ell_t`. That location holds the target, a closure, or $`\mathsf{null}` for the function with no target.

The predicate $`\mathrm{wf}_{\mathit{function}}` states that the template argument is a function type.

$$`\begin{array}{lcl} \mathrm{wf}_{\mathit{function}}(\bar{\tau}) & \iff & \bar{\tau} = \tau(\tau_1, \ldots, \tau_k) \end{array}`

The argument of `new std::function<F>(λ)` is a lambda, acceptable at its function type $`F` by the rule `T-Lambda` of {bpref "fun_accept"}[]. The form `new std::function<F>()` is the default construction of C++ (N4659 §23.14.13.2.1 ¶1), which gives the function with no target.

$$`\dfrac{}{\Gamma \vdash_{\mathit{function}} \mathtt{new} : F \to \mathtt{std{:}{:}function}\langle F\rangle*}\;\textsf{(TF-New)}`

$$`\dfrac{}{\Gamma \vdash_{\mathit{function}} \mathtt{new} : \to \mathtt{std{:}{:}function}\langle F\rangle*}\;\textsf{(TF-Empty)}`

$$`\dfrac{}{\Gamma \vdash_{\mathit{function}} \mathtt{delete}\ \mathsf{ok}}\;\textsf{(TF-Delete)}`

$$`\dfrac{w = \mathsf{closure}(\ldots) \qquad (\ell_t, \sigma_1) = \mathrm{alloc}(\sigma, w) \qquad (\ell, \sigma') = \mathrm{alloc}(\sigma_1, \mathsf{lib}\ \mathtt{std{:}{:}function}\,[\ell_t])}{\sigma \vdash_{\mathit{function}} \mathtt{new}\langle F\rangle(w) \Rightarrow \mathsf{loc}\,\ell, \sigma'}\;\textsf{(F-New)}`

$$`\dfrac{(\ell_t, \sigma_1) = \mathrm{alloc}(\sigma, \mathsf{null}) \qquad (\ell, \sigma') = \mathrm{alloc}(\sigma_1, \mathsf{lib}\ \mathtt{std{:}{:}function}\,[\ell_t])}{\sigma \vdash_{\mathit{function}} \mathtt{new}\langle F\rangle() \Rightarrow \mathsf{loc}\,\ell, \sigma'}\;\textsf{(F-Empty)}`

$$`\dfrac{}{\sigma \vdash_{\mathit{function}} \mathtt{delete}\ (\mathsf{lib}\ \mathtt{std{:}{:}function}\,[\ell_t]) \Rightarrow \sigma \setminus \{\ell_t\}}\;\textsf{(F-Delete)}`

The call of the object, `(*f)(e₁, …, eₖ)` for a pointer `f`, is the rule `CallFn` of {bpref "fun_callfn"}[], a rule of the language. That rule reads the target and applies it. The function with no target has no derivation there, and the evaluator gives `error`, as the `bad_function_call` of C++ ends a program that does not catch it.
:::

:::definition "std_assert" (parent := "library") (lean := "CoreCpp.Semantics.Assert.TCall, CoreCpp.Semantics.Assert.Call, CoreCpp.Std.Assert.statics, CoreCpp.Std.Assert.fns") (uses := "std_library, std_uses")
The header `<cassert>` declares `void assert(bool condition);`. In C++ `assert` is a macro, and with `NDEBUG` undefined a failed assertion calls `abort` (N1570 §7.2.1.1). Core C++ gives `error`, which ends with the same exit status.

$$`\dfrac{}{\Gamma \vdash_{\mathit{assert}} \mathtt{assert} : \mathsf{bool} \to \mathsf{void}}\;\textsf{(TA-Call)}`

$$`\dfrac{}{\sigma \vdash_{\mathit{assert}} \mathtt{assert}(\mathtt{true}) \Rightarrow \mathsf{void}, \sigma}\;\textsf{(A-True)}`

A failed assertion, `assert(false)`, has no derivation.
:::

# Rules of the chapter

Every definition, every typing rule and every evaluation rule of this chapter, in the order of its sections, the typing rules of each section before its evaluation rules. The section named above each rule states it with its explanation and with the definition of its notation.

*Interface*

$$`\dfrac{\Gamma \vdash L\langle\bar{\tau}\rangle\ \mathsf{ok} \qquad \Gamma \vdash_L \mathtt{new} : \tau_1 \times \cdots \times \tau_k \to \tau \qquad \Gamma \vdash e_i \lhd \tau_i}{\Gamma \vdash \mathtt{new}\ L\langle\bar{\tau}\rangle(e_1, \ldots, e_k) : \tau}\;\textsf{(T-NewLib)}`

$$`\dfrac{f \notin \Gamma \qquad f \text{ no function of the program, declared by a header} \qquad \Gamma \vdash_f f : \tau_1 \times \cdots \times \tau_k \to \tau \qquad \Gamma \vdash e_i \lhd \tau_i}{\Gamma \vdash f(e_1, \ldots, e_k) : \tau}\;\textsf{(T-CallLib)}`

$$`\dfrac{\Gamma \vdash e : L\langle\bar{\tau}\rangle \qquad \Gamma \vdash_L \mathtt{operator[]} : \tau_1 \to \tau \qquad \Gamma \vdash i \lhd \tau_1}{\Gamma \vdash e[i] : \tau}\;\textsf{(T-IndexLib)}`

$$`\dfrac{\Gamma \vdash e : L\langle\bar{\tau}\rangle \qquad \Gamma \vdash_L \mathtt{operator[]} : \tau_1 \to \tau \qquad \Gamma \vdash i \lhd \tau_1}{\Gamma \vdash_{\ell} e[i] : \tau}\;\textsf{(T-LocIndexLib)}`

$$`\dfrac{\Gamma \vdash e : L\langle\bar{\tau}\rangle* \qquad L\langle\bar{\tau}\rangle \text{ an object type} \qquad \Gamma \vdash_L \mathtt{delete}\ \mathsf{ok}}{\Gamma \vdash \mathtt{delete}\ e \dashv \Gamma}\;\textsf{(T-DeleteLib)}`

 

$$`\dfrac{\rho, \sigma_{i-1} \vdash e_i \Rightarrow v_i, \sigma_i \quad (1 \le i \le k) \qquad \sigma_k \vdash_L \mathtt{new}\langle\bar{\tau}\rangle(v_1, \ldots, v_k) \Rightarrow v, \sigma'}{\rho, \sigma_0 \vdash \mathtt{new}\ L\langle\bar{\tau}\rangle(e_1, \ldots, e_k) \Rightarrow v, \sigma'}\;\textsf{(NewLib)}`

$$`\dfrac{\begin{array}{c} f \notin \rho \qquad f \text{ no function of the program, declared by a header} \\ \rho, \sigma_{i-1} \vdash e_i \Rightarrow v_i, \sigma_i \quad (1 \le i \le k) \qquad \sigma_k \vdash_f f(v_1, \ldots, v_k) \Rightarrow v, \sigma' \end{array}}{\rho, \sigma_0 \vdash f(e_1, \ldots, e_k) \Rightarrow v, \sigma'}\;\textsf{(CallLib)}`

$$`\dfrac{\rho, \sigma \vdash e \Rightarrow \mathsf{lib}\,L\,\bar{\ell}, \sigma_1 \qquad \rho, \sigma_1 \vdash i \Rightarrow v, \sigma_2 \qquad \sigma_2 \vdash_L (\mathsf{lib}\,L\,\bar{\ell})[v] \Rightarrow_{\ell} \ell, \sigma'}{\rho, \sigma \vdash e[i] \Rightarrow_{\ell} \ell, \sigma'}\;\textsf{(LocIndex)}`

$$`\dfrac{\begin{array}{c} \rho, \sigma \vdash e \Rightarrow \mathsf{loc}\,\ell, \sigma_0\qquad \sigma_0(\ell) = \mathsf{lib}\,L\,\bar{\ell} \\ \sigma_0 \vdash_L \mathtt{delete}\ (\mathsf{lib}\,L\,\bar{\ell}) \Rightarrow \sigma_1 \end{array}}{\rho, \sigma \vdash \mathtt{delete}\ e \Rightarrow \mathsf{normal}, \rho, \sigma_1 \setminus \{\ell\}}\;\textsf{(DeleteLib)}`

*Headers*

$$`\begin{array}{lcl} \mathrm{wf}_{\mathit{vector}}(\bar{\tau}) & \iff & \bar{\tau} = \tau \ \land\ (\tau = \mathsf{int} \lor \tau = \mathsf{bool} \lor \tau = \tau'*) \end{array}`

$$`\begin{array}{lcl} \mathrm{wf}_{\mathit{function}}(\bar{\tau}) & \iff & \bar{\tau} = \tau(\tau_1, \ldots, \tau_k) \end{array}`

$$`\dfrac{}{\Gamma \vdash_{\mathit{vector}} \mathtt{new} : \mathsf{int} \to \mathtt{std{:}{:}vector}\langle\tau\rangle*}\;\textsf{(TV-New)}`

$$`\dfrac{}{\Gamma \vdash_{\mathit{vector}} \mathtt{operator[]} : \mathsf{int} \to \tau}\;\textsf{(TV-Index)}`

$$`\dfrac{}{\Gamma \vdash_{\mathit{vector}} \mathtt{delete}\ \mathsf{ok}}\;\textsf{(TV-Delete)}`

$$`\dfrac{}{\Gamma \vdash_{\mathit{function}} \mathtt{new} : F \to \mathtt{std{:}{:}function}\langle F\rangle*}\;\textsf{(TF-New)}`

$$`\dfrac{}{\Gamma \vdash_{\mathit{function}} \mathtt{new} : \to \mathtt{std{:}{:}function}\langle F\rangle*}\;\textsf{(TF-Empty)}`

$$`\dfrac{}{\Gamma \vdash_{\mathit{function}} \mathtt{delete}\ \mathsf{ok}}\;\textsf{(TF-Delete)}`

$$`\dfrac{}{\Gamma \vdash_{\mathit{assert}} \mathtt{assert} : \mathsf{bool} \to \mathsf{void}}\;\textsf{(TA-Call)}`

 

$$`\dfrac{\begin{array}{c} k \ge 0\qquad (\ell_i, \sigma_i) = \mathrm{alloc}(\sigma_{i-1}, \mathrm{default}\,\tau)\ (1 \le i \le k) \\ (\ell, \sigma') = \mathrm{alloc}(\sigma_k, \mathsf{lib}\ \mathtt{std{:}{:}vector}\,[\ell_1, \ldots, \ell_k]) \end{array}}{\sigma_0 \vdash_{\mathit{vector}} \mathtt{new}\langle\tau\rangle(k) \Rightarrow \mathsf{loc}\,\ell, \sigma'}\;\textsf{(V-New)}`

$$`\dfrac{0 \le i < n}{\sigma \vdash_{\mathit{vector}} (\mathsf{lib}\ \mathtt{std{:}{:}vector}\,[\ell_0, \ldots, \ell_{n-1}])[i] \Rightarrow_{\ell} \ell_i, \sigma}\;\textsf{(V-Index)}`

$$`\dfrac{}{\sigma \vdash_{\mathit{vector}} \mathtt{delete}\ (\mathsf{lib}\ \mathtt{std{:}{:}vector}\,[\ell_0, \ldots, \ell_{n-1}]) \Rightarrow \sigma \setminus \{\ell_0, \ldots, \ell_{n-1}\}}\;\textsf{(V-Delete)}`

$$`\dfrac{w = \mathsf{closure}(\ldots) \qquad (\ell_t, \sigma_1) = \mathrm{alloc}(\sigma, w) \qquad (\ell, \sigma') = \mathrm{alloc}(\sigma_1, \mathsf{lib}\ \mathtt{std{:}{:}function}\,[\ell_t])}{\sigma \vdash_{\mathit{function}} \mathtt{new}\langle F\rangle(w) \Rightarrow \mathsf{loc}\,\ell, \sigma'}\;\textsf{(F-New)}`

$$`\dfrac{(\ell_t, \sigma_1) = \mathrm{alloc}(\sigma, \mathsf{null}) \qquad (\ell, \sigma') = \mathrm{alloc}(\sigma_1, \mathsf{lib}\ \mathtt{std{:}{:}function}\,[\ell_t])}{\sigma \vdash_{\mathit{function}} \mathtt{new}\langle F\rangle() \Rightarrow \mathsf{loc}\,\ell, \sigma'}\;\textsf{(F-Empty)}`

$$`\dfrac{}{\sigma \vdash_{\mathit{function}} \mathtt{delete}\ (\mathsf{lib}\ \mathtt{std{:}{:}function}\,[\ell_t]) \Rightarrow \sigma \setminus \{\ell_t\}}\;\textsf{(F-Delete)}`

$$`\dfrac{}{\sigma \vdash_{\mathit{assert}} \mathtt{assert}(\mathtt{true}) \Rightarrow \mathsf{void}, \sigma}\;\textsf{(A-True)}`
