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

# UD VI

:::definition "overload" (parent := "pendentes") (uses := "fun_call, judg_ty_expr")
Overloading of functions and operators by argument type, resolved in $`\Gamma`, except over `std::function` parameters. The expression `v[i]` is the call of `operator[]`, which returns `int&`.
:::

:::definition "template_class" (parent := "pendentes") (uses := "cls_decl")
Class templates only, instantiated in type position, by substitution of the type parameter at instantiation.
:::
