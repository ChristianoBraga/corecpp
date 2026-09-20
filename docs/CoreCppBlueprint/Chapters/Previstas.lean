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

# UD IV

:::definition "param_ref" (parent := "pendentes") (uses := "fun_call, judg_ev_lval")
A `T&` parameter receives the location of the argument instead of a fresh location with a copy.
:::

:::definition "lambda" (parent := "pendentes") (uses := "fun_call, dom_env")
The lambda expression `[=]` evaluates to a closure, a pair of body and environment with read only copies of the basic values and pointers the body uses. It occurs only as initialiser of a `std::function`, argument of a `std::function` parameter or `return` expression.
:::

# UD V

:::definition "class_new" (parent := "pendentes") (uses := "expr_new")
Constructors, `private` sections and methods. The `new C(args)` of UD V allocates the fields as the `new C()` of UD II does and then runs the constructor body with `this` bound to the object.
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
