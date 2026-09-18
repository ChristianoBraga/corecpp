import Verso
import VersoManual
import VersoBlueprint

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Planned constructions" =>

Constructions of the Core C++ design without rules or implementation yet. They appear in the graph and in the summary as pending work, in the order of the UD.

:::group "pendentes"
Constructions planned in `core-cpp-design.md`, not implemented.
:::

# UD III

:::definition "ref_local" (parent := "pendentes") (uses := "cmd_decl, judg_ev_lval")
The local reference `int& y = x` binds a second name to the same location, without allocating.

$$`\dfrac{\rho, \sigma \vdash e \Rightarrow_{\ell} \ell, \sigma'}{\rho, \sigma \vdash \tau\&\ y = e \Rightarrow \mathsf{normal}, \rho[y \mapsto \ell], \sigma'}\;\textsf{(DeclRef)}`
:::

:::definition "lval_ext" (parent := "pendentes") (uses := "judg_ev_lval")
The judgment $`\Rightarrow_{\ell}` extends to `v[i]`, `o.field`, `p->field` and `*p`. An index out of bounds and the dereference of `nullptr` are `error`.
:::

# UD IV

:::definition "param_ref" (parent := "pendentes") (uses := "fun_call, judg_ev_lval")
A `T&` parameter receives the location of the argument instead of a fresh location with a copy.
:::

:::definition "lambda" (parent := "pendentes") (uses := "fun_call, dom_env")
The lambda expression `[=]` evaluates to a closure, a pair of body and environment with read only copies of the basic values and pointers the body uses. It occurs only as initialiser of a `std::function`, argument of a `std::function` parameter or `return` expression.
:::

# UD V

:::definition "class_new" (parent := "pendentes") (uses := "dom_store, dom_val")
An object is a record of locations with a class tag. The `new` allocates the locations of the fields and calls the constructor. Vectors are objects like any other.
:::

:::definition "method_dispatch" (parent := "pendentes") (uses := "class_new, fun_call")
A method call binds `this` to the location of the object. With `virtual`, the method is chosen by the class tag of the object, not by the static type of the pointer.
:::

:::definition "delete_cmd" (parent := "pendentes") (uses := "class_new")
The `delete p` runs the destructor with `this` at the location of the object and removes the locations of the object from $`\sigma`. Double `delete`, access after `delete` and `delete` through a base pointer without a `virtual` destructor are `error`.
:::

:::definition "subsumption" (parent := "pendentes") (uses := "class_new, judg_ty_expr")
A pointer to a derived class is accepted where a pointer to the base is expected. It is the only implicit conversion between classes.
:::

# UD VI

:::definition "overload" (parent := "pendentes") (uses := "fun_call, judg_ty_expr")
Overloading of functions and operators by argument type, resolved in $`\Gamma`, except over `std::function` parameters. The expression `v[i]` is the call of `operator[]`, which returns `int&`.
:::

:::definition "template_class" (parent := "pendentes") (uses := "class_new")
Class templates only, instantiated in type position, by substitution of the type parameter at instantiation.
:::
