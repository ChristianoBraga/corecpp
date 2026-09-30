import Verso
import VersoManual
import VersoBlueprint
import CoreCpp.Std
import CoreCpp.Typing
import CoreCpp.Eval

open Verso.Genre
open Verso.Genre.Manual
open Informal

set_option verso.blueprint.foldCodeBlocks true

#doc (Manual) "The standard library" =>

The headers of Core C++ declare the entities of the library without a body, the class templates `std::vector` and `std::function` and the function `assert`. Each declaration names an intrinsic, a set of judgments in natural semantics that the rules of the language use as premises. The intrinsics live in `CoreCpp/Std/`, apart from the type checker and the evaluator, which know no intrinsic by name. A use of an undeclared entity is a type error, so a program uses the library only through its `#include`. Nothing of this is built into the syntax. The grammar has no production and the lexer no reserved word for the library, `namespace std` is an ordinary namespace and `std::vector` an ordinary qualified name, and what tells a class of the library from one of the program is the case of its name, lowercase for the first and uppercase for the second.

:::group "ud7"
The library, its interface and its intrinsics.
:::

# Interface

:::definition "std_library" (parent := "ud7") (lean := "CoreCpp.Std.Use, CoreCpp.Std.Sig, CoreCpp.Std.Result, CoreCpp.Std.Statics, CoreCpp.Std.Intrinsic, CoreCpp.Std.library") (uses := "pp_headers, judg_ty_expr, judg_ev_expr")
An intrinsic $`L` has a name, the number of its template parameters, and four judgments. The metavariable $`\bar{\tau}` stands for its template arguments, $`u` for a use, `new`, `delete`, a call, or a member such as `operator[]`, and $`r` for a value or a location.

| Judgment | Meaning | Lean |
| --- | --- | --- |
| $`\Gamma \vdash_L L\langle\bar{\tau}\rangle\ \mathsf{ok}` | the instance is well formed | `instOk` |
| $`\Gamma \vdash_L u : \tau_1 \times \cdots \times \tau_k \to \tau` | the signature of the use $`u` | `sig` |
| $`\Gamma \vdash_L \tau \hookrightarrow L\langle\bar{\tau}\rangle` | the type $`\tau` converts to the instance | `convFrom` |
| $`\sigma \vdash_L u(v_1, \ldots, v_k) \Rightarrow r, \sigma'` | the result of the use $`u` | `eval` |

The dynamic judgment may use one judgment of the language as a premise, the application of a closure of {bpref "fun_callfn"}[]. Three further marks say how the language treats the values of an instance. An object lives in the store and is reached by pointer, a type without a default is excluded from fields and elements, and a convertible type tells no two overloads apart.
:::

:::definition "std_uses" (parent := "ud7") (lean := "CoreCpp.Typing.expr, CoreCpp.Typing.lval, CoreCpp.Typing.annotate, CoreCpp.Eval.expr, CoreCpp.Eval.lval, CoreCpp.Eval.libUse") (uses := "std_library, judg_ty_lval, judg_ev_lval, dom_store")
The type checker rewrites every use of the library into the node $`L.u(e_1, \ldots, e_k)`, with the receiver as $`e_1` for a member. A call of a declared function is the use `call`, a call through a value of an instance is `operator()`, and indexing is `operator[]`. The evaluator has one rule for the node, whatever $`L`. The arguments are values, evaluated left to right.

$$`\dfrac{\Gamma \vdash_L L\langle\bar{\tau}\rangle\ \mathsf{ok} \qquad \Gamma \vdash_L \mathtt{new} : \tau_1 \times \cdots \times \tau_k \to \tau \qquad \Gamma \vdash e_i \lhd \tau_i}{\Gamma \vdash \mathtt{new}\ L\langle\bar{\tau}\rangle(e_1, \ldots, e_k) : \tau}\;\textsf{(T-NewLib)}`

$$`\dfrac{f \text{ declared by a header} \qquad \Gamma \vdash_f \mathtt{call} : \tau_1 \times \cdots \times \tau_k \to \tau \qquad \Gamma \vdash e_i \lhd \tau_i}{\Gamma \vdash f(e_1, \ldots, e_k) : \tau}\;\textsf{(T-CallLib)}`

$$`\dfrac{\Gamma \vdash e : L\langle\bar{\tau}\rangle \qquad \Gamma \vdash_L \mathtt{operator[]} : \tau_1 \to \tau \qquad \Gamma \vdash i \lhd \tau_1}{\Gamma \vdash e[i] : \tau}\;\textsf{(T-IndexLib)}`

$$`\dfrac{\Gamma \vdash e : L\langle\bar{\tau}\rangle \qquad \Gamma \vdash_L \mathtt{operator[]} : \tau_1 \to \tau, \text{ a location} \qquad \Gamma \vdash i \lhd \tau_1}{\Gamma \vdash_{\ell} e[i] : \tau}\;\textsf{(T-LocIndexLib)}`

$$`\dfrac{\rho, \sigma_{i-1} \vdash e_i \Rightarrow v_i, \sigma_i \quad (1 \le i \le k) \qquad \sigma_k \vdash_L \mathtt{new}\langle\bar{\tau}\rangle(v_1, \ldots, v_k) \Rightarrow v, \sigma'}{\rho, \sigma_0 \vdash \mathtt{new}\ L\langle\bar{\tau}\rangle(e_1, \ldots, e_k) \Rightarrow v, \sigma'}\;\textsf{(NewLib)}`

$$`\dfrac{\rho, \sigma_{i-1} \vdash e_i \Rightarrow v_i, \sigma_i \quad (1 \le i \le k) \qquad \sigma_k \vdash_L u(v_1, \ldots, v_k) \Rightarrow r, \sigma'}{\rho, \sigma_0 \vdash L.u(e_1, \ldots, e_k) \Rightarrow v, \sigma'}\;\textsf{(Lib)}`

In the rule `Lib` the result is $`v = r` for a value and $`v = \sigma'(r)` for a location. With the same premises, a use that gives a location denotes it.

$$`\dfrac{\rho, \sigma_{i-1} \vdash e_i \Rightarrow v_i, \sigma_i \quad (1 \le i \le k) \qquad \sigma_k \vdash_L u(v_1, \ldots, v_k) \Rightarrow \ell, \sigma'}{\rho, \sigma_0 \vdash L.u(e_1, \ldots, e_k) \Rightarrow_{\ell} \ell, \sigma'}\;\textsf{(LocLib)}`
 The command `delete e` on a pointer to an instance frees what the intrinsic owns and then the location of the instance.

$$`\dfrac{\rho, \sigma \vdash e \Rightarrow \mathsf{loc}\,\ell, \sigma_0 \qquad \sigma_0(\ell) = \mathsf{lib}\,L\,\bar{\ell} \qquad \sigma_0 \vdash_L \mathtt{delete}(\sigma_0(\ell)) \Rightarrow \mathsf{void}, \sigma_1}{\rho, \sigma \vdash \mathtt{delete}\ e \Rightarrow \mathsf{normal}, \rho, \sigma_1 \setminus \{\ell\}}\;\textsf{(DeleteLib)}`
:::

# Headers

:::definition "std_vector" (parent := "ud7") (lean := "CoreCpp.Std.vector, CoreCpp.Std.elementOk") (uses := "std_library, std_uses")
The header `<vector>` declares `template <typename T> class vector;` in `namespace std`. A vector is an object, created with `new` and reached by pointer. Its value $`\mathsf{lib}\ \mathtt{std{:}{:}vector}\,[\ell_0, \ldots, \ell_{n-1}]` holds one location per element. The element type has values and a default, so it is not a class, a type of the library, a function type, `void` or $`\mathsf{nullptr\_t}`. A vector therefore holds pointers to objects and never objects.

$$`\dfrac{}{\Gamma \vdash_{\mathit{vector}} \mathtt{new} : \mathsf{int} \to \mathtt{std{:}{:}vector}\langle\tau\rangle*}\;\textsf{(TV-New)} \qquad \dfrac{}{\Gamma \vdash_{\mathit{vector}} \mathtt{operator[]} : \mathsf{int} \to \tau}\;\textsf{(TV-Index)}`

The use `operator[]` gives a location, so `v[i]` may stand on the left of an assignment and bind a reference.

$$`\dfrac{k \ge 0 \qquad (\ell_i, \sigma_i) = \mathrm{alloc}(\sigma_{i-1}, \mathrm{default}\,\tau)\ (1 \le i \le k) \qquad (\ell, \sigma') = \mathrm{alloc}(\sigma_k, \mathsf{lib}\ \mathtt{std{:}{:}vector}\,[\ell_1, \ldots, \ell_k])}{\sigma_0 \vdash_{\mathit{vector}} \mathtt{new}\langle\tau\rangle(k) \Rightarrow \mathsf{loc}\,\ell, \sigma'}\;\textsf{(V-New)}`

$$`\dfrac{0 \le i < n}{\sigma \vdash_{\mathit{vector}} \mathtt{operator[]}(\mathsf{lib}\ \mathtt{std{:}{:}vector}\,[\ell_0, \ldots, \ell_{n-1}], i) \Rightarrow \ell_i, \sigma}\;\textsf{(V-Index)}`

$$`\dfrac{}{\sigma \vdash_{\mathit{vector}} \mathtt{delete}(\mathsf{lib}\ \mathtt{std{:}{:}vector}\,[\ell_0, \ldots, \ell_{n-1}]) \Rightarrow \mathsf{void}, \sigma \setminus \{\ell_0, \ldots, \ell_{n-1}\}}\;\textsf{(V-Delete)}`

A negative size and an index outside $`[0, n)` are `error`, where C++17 leaves the index undefined. The receiver is evaluated before the index, the order C++17 fixes for `operator[]`.
:::

:::definition "std_function" (parent := "ud7") (lean := "CoreCpp.Std.function") (uses := "std_library, std_uses, fun_accept, fun_callfn")
The header `<functional>` declares `template <typename F> class function;` in `namespace std`. The template argument is a function type $`\tau(\tau_1, \ldots, \tau_k)`. A value of the instance is the closure of a lambda. It is not an object and has no default, so no field and no element has the type.

$$`\dfrac{}{\Gamma \vdash_{\mathit{function}} \tau(\tau_1, \ldots, \tau_k) \hookrightarrow \mathtt{std{:}{:}function}\langle\tau(\tau_1, \ldots, \tau_k)\rangle}\;\textsf{(TF-Conv)}`

$$`\dfrac{}{\Gamma \vdash_{\mathit{function}} \mathtt{operator()} : \tau_1 \times \cdots \times \tau_k \to \tau}\;\textsf{(TF-Call)}, \quad \text{at } \mathtt{std{:}{:}function}\langle\tau(\tau_1, \ldots, \tau_k)\rangle`

$$`\dfrac{\sigma \vdash \mathrm{apply}(v, v_1, \ldots, v_k) \Rightarrow v', \sigma'}{\sigma \vdash_{\mathit{function}} \mathtt{operator()}(v, v_1, \ldots, v_k) \Rightarrow v', \sigma'}\;\textsf{(F-Call)}`

The premise of `F-Call` is the application of a closure, the one judgment of the language an intrinsic uses. The type is convertible, so two overloads that differ only in a parameter of this type are indistinguishable, {bpref "overload_set"}[].
:::

:::definition "std_assert" (parent := "ud7") (lean := "CoreCpp.Std.assert") (uses := "std_library, std_uses")
The header `<cassert>` declares `void assert(bool condition);`. In C++ `assert` is a macro, and with `NDEBUG` undefined a failed assertion calls `abort` (N1570 §7.2.1.1). Core C++ gives `error`, which ends with the same exit status.

$$`\dfrac{}{\Gamma \vdash_{\mathit{assert}} \mathtt{call} : \mathsf{bool} \to \mathsf{void}}\;\textsf{(TA-Call)}`

$$`\dfrac{}{\sigma \vdash_{\mathit{assert}} \mathtt{call}(\mathtt{true}) \Rightarrow \mathsf{void}, \sigma}\;\textsf{(A-True)} \qquad \dfrac{}{\sigma \vdash_{\mathit{assert}} \mathtt{call}(\mathtt{false}) \Rightarrow \mathsf{error}}\;\textsf{(A-False)}`
:::
