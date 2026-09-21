import Verso
import VersoManual
import VersoBlueprint
import CoreCpp.Syntax
import CoreCpp.Parser
import CoreCpp.Typing
import CoreCpp.Eval

open Verso.Genre
open Verso.Genre.Manual
open Informal

set_option verso.blueprint.foldCodeBlocks true

#doc (Manual) "Encapsulation" =>

Classes with `public` and `private` sections, methods, constructors run by `new`, destructors run by `delete`, `this`, single inheritance, subsumption, dispatch by the class tag for `virtual` methods and namespaces. An abstract data type is a public signature over a private representation, and visibility is a typing rule. Objects are still records of locations with a tag, created by `new` and never copied, and the destructor runs only on `delete`. The static class of every receiver and of every `delete` is written into the tree by the type checker, since $`\rho` and $`\sigma` carry no types.

:::group "ud5"
Abstract data types, objects, classes and inheritance.
:::

# Classes and visibility

:::definition "cls_decl" (parent := "ud5") (lean := "CoreCpp.ClassDecl, CoreCpp.Field, CoreCpp.Method, CoreCpp.Ctor, CoreCpp.Dtor, CoreCpp.Vis, CoreCpp.Typing.cls, CoreCpp.Typing.memberEnv") (uses := "dom_classes, judg_ty_cmd")
A class has an optional base, fields and methods with a visibility, at most one constructor named after the class and at most one destructor. Members before the first section label are private, as in C++. The class is well formed when the base exists and the chain is acyclic, the fields have types with values and repeat no field of a base, the members have distinct names, a method that redefines a method of a base finds it `virtual` there, carries `override` and keeps the signature, the constructor of the base takes no parameters, and every member body is well typed under `this`.

$$`\dfrac{\begin{array}{c} B \text{ exists, chain acyclic} \qquad \text{fields storable, well formed, new in the chain} \\ \text{each redefined } m \text{ is virtual in the base, marked override, same signature} \qquad B \text{ has no constructor or one without parameters} \\ [\mathtt{this} \mapsto C*, p_1, \ldots, p_k] \vdash c \dashv \Gamma' \text{ for each member body} \end{array}}{\vdash \mathtt{class}\ C\ \mathtt{:}\ \mathtt{public}\ B\ \{ \ldots \}}\;\textsf{(T-Class)}`

The context of a member body binds `this` to $`C*` and the parameters as variables, so the current class is the class of `this` in $`\Gamma`.
:::

:::definition "cls_visible" (parent := "ud5") (lean := "CoreCpp.TEnv.self, CoreCpp.Typing.fieldType, CoreCpp.Typing.methodCall") (uses := "cls_decl, dom_tenv")
A private member declared in class $`K` is visible exactly when $`\Gamma(\mathtt{this}) = K*`. Visibility is thus a typing rule, and the public section of a class is the signature of an abstract data type while the private section is its representation, reachable only from the member bodies of the class.

$$`\dfrac{C \text{ has } \tau\ f \text{ declared in } K \qquad f \text{ public or } \Gamma(\mathtt{this}) = K*}{\Gamma \vdash e.f : \tau \text{ for } \Gamma \vdash e : C}\;\textsf{(Visible)}`

The same premise applies to methods, {bpref "cls_method"}[].
:::

:::definition "cls_this" (parent := "ud5") (lean := "CoreCpp.Typing.expr, CoreCpp.Eval.expr, CoreCpp.Eval.lval") (uses := "judg_ty_expr, judg_ev_expr, judg_ev_lval, dom_env")
Inside a member body `this` is the location of the receiver. It is bound in $`\rho` by the call as an alias, never a variable, and it evaluates to a pointer. An unqualified name that is not a variable denotes the member of `this`, both in the type checker and in the evaluator.

$$`\dfrac{\Gamma(\mathtt{this}) = C*}{\Gamma \vdash \mathtt{this} : C*}\;\textsf{(T-This)} \qquad \dfrac{x \notin \Gamma \qquad \Gamma(\mathtt{this}) = C* \qquad \Gamma \vdash \mathtt{this}\mathtt{->}x : \tau}{\Gamma \vdash x : \tau}\;\textsf{(T-VarField)}`

$$`\dfrac{\rho(\mathtt{this}) = \ell}{\rho, \sigma \vdash \mathtt{this} \Rightarrow \mathsf{loc}\,\ell, \sigma}\;\textsf{(This)} \qquad \dfrac{x \notin \rho \qquad \rho(\mathtt{this}) = \ell \qquad \sigma(\ell) = \mathsf{obj}\,C\,[\ldots x \mapsto \ell_x \ldots]}{\rho, \sigma \vdash x \Rightarrow_{\ell} \ell_x, \sigma}\;\textsf{(LocVarField)}`
:::

# Objects

:::definition "cls_new" (parent := "ud5") (lean := "CoreCpp.Typing.expr, CoreCpp.Eval.expr, CoreCpp.Program.allFields, CoreCpp.Program.chain") (uses := "expr_new, cls_decl, cls_member, dom_store")
The expression `new C(args)` allocates one location per field of the whole chain of $`C`, the root base first, then the tagged record, and runs the constructors from the root base down, each with `this` bound to the object, the one of $`C` with the arguments and the others with none, since there are no initialiser lists. A class without a constructor is created by `new C()` and keeps the default values.

$$`\dfrac{C \mapsto \mathtt{class}\ C\ \{\ldots C(p_1\,x_1, \ldots, p_k\,x_k)\ \{c\} \ldots\} \qquad \text{arguments as in T-Call}}{\Gamma \vdash \mathtt{new}\ C(e_1, \ldots, e_k) : C*}\;\textsf{(T-New)}`

$$`\dfrac{\begin{array}{c} f_1 \ldots f_n \text{ the fields of the chain of } C \qquad (\ell_i, \sigma_i) = \mathrm{alloc}(\sigma_{i-1}, \mathrm{default}\,\tau_i) \qquad (\ell, \sigma') = \mathrm{alloc}(\sigma_n, \mathsf{obj}\,C\,[f_1 \mapsto \ell_1, \ldots, f_n \mapsto \ell_n]) \\ \text{the constructors of the chain run from the root down with } \mathtt{this} \mapsto \ell \text{, giving } \sigma'' \end{array}}{\rho, \sigma \vdash \mathtt{new}\ C(e_1, \ldots, e_k) \Rightarrow \mathsf{loc}\,\ell, \sigma''}\;\textsf{(New)}`
:::

:::definition "cls_member" (parent := "ud5") (lean := "CoreCpp.Eval.runMember, CoreCpp.Typing.checkArgs") (uses := "fun_call, param_ref, judg_ev_cmd, dom_env")
The call of a member body, a method, a constructor or a destructor, binds `this` to the location $`\ell` of the receiver as an alias and the parameters as in the call of a function, by value with a fresh copy and by reference with an alias. The return frees the copies and the locals of the body, never the receiver.

$$`\dfrac{\begin{array}{c} p_i = \tau_i \Rightarrow \rho, \sigma'_{i-1} \vdash e_i \Rightarrow v_i, \sigma_i,\ (\ell_i, \sigma'_i) = \mathrm{alloc}(\sigma_i, v_i) \qquad p_i = \tau_i\& \Rightarrow \rho, \sigma'_{i-1} \vdash e_i \Rightarrow_{\ell} \ell_i, \sigma'_i \\ \rho_m = [\mathtt{this} \mapsto \ell, x_1 \mapsto \ell_1, \ldots, x_k \mapsto \ell_k] \qquad \rho_m, \sigma'_k \vdash c \Rightarrow r, \rho', \sigma'' \end{array}}{\mathrm{member}\ \ell\ (e_1, \ldots, e_k) \Rightarrow v, \sigma'' \setminus (\{\ell_i \mid p_i \text{ by value}\} \cup (\rho' \setminus \rho_m))}\;\textsf{(Member)}`

With $`\mathsf{normal}` in place of $`\mathsf{ret}\,v` the result is $`\mathsf{void}` for a `void` member and `error` otherwise.
:::

:::definition "cls_method" (parent := "ud5") (lean := "CoreCpp.Typing.methodCall, CoreCpp.Eval.expr, CoreCpp.Eval.resolve, CoreCpp.Program.findMethod") (uses := "cls_member, cls_visible, cls_dispatch, judg_ty_expr, judg_ev_expr")
A method call `e.m(args)` needs a receiver of class type and `e->m(args)` a receiver of pointer type. The method is the nearest $`m` in the chain of the static class of the receiver, it must be visible, and the arguments are checked as in a call. An unqualified call `m(args)` inside a member body is `this->m(args)`.

$$`\dfrac{\Gamma \vdash e : C \qquad C \text{ has } \tau\ m(p_1\,x_1, \ldots, p_k\,x_k) \text{ visible from } \Gamma \qquad \text{arguments as in T-Call}}{\Gamma \vdash e.m(e_1, \ldots, e_k) : \tau}\;\textsf{(T-Method)}`

$$`\dfrac{\Gamma \vdash e : C* \qquad C \text{ has } \tau\ m(\ldots) \text{ visible from } \Gamma \qquad \text{arguments as in T-Call}}{\Gamma \vdash e\mathtt{->}m(e_1, \ldots, e_k) : \tau}\;\textsf{(T-MethodArrow)}`

$$`\dfrac{\begin{array}{c} \rho, \sigma \vdash e \Rightarrow_{\ell} \ell, \sigma_0 \text{ or } \rho, \sigma \vdash e \Rightarrow \mathsf{loc}\,\ell, \sigma_0 \qquad \sigma_0(\ell) = \mathsf{obj}\,T\,[\ldots] \qquad S \text{ the static class of } e \\ m \mapsto \tau\ m(\ldots)\{c\} \text{ nearest } S \text{, or nearest } T \text{ when virtual} \qquad \mathrm{member}\ \ell\ (e_1, \ldots, e_k) \Rightarrow v, \sigma' \end{array}}{\rho, \sigma \vdash e.m(e_1, \ldots, e_k) \Rightarrow v, \sigma'}\;\textsf{(MethodCall)}`
:::

# Inheritance

:::definition "cls_subsumption" (parent := "ud5") (lean := "CoreCpp.Typing.compat, CoreCpp.Typing.related, CoreCpp.Program.subclass") (uses := "cls_decl, judg_ty_expr")
A pointer to a derived class is accepted where a pointer to its base is expected, in declarations, assignments, arguments, returns, comparisons and the branches of `?:`. It is the only conversion between class types, and the other direction is a type error.

$$`\dfrac{D \text{ derives from } B}{D* \approx B*}\;\textsf{(Subsumption)}`
:::

:::definition "cls_dispatch" (parent := "ud5") (lean := "CoreCpp.Eval.resolve, CoreCpp.Program.findMethod, CoreCpp.Typing.cls") (uses := "cls_decl, cls_subsumption, dom_classes")
A `virtual` method is chosen by the class tag $`T` of the receiver, the nearest declaration in the chain of $`T`, so a call through a base pointer reaches the override of the derived class. A non virtual method is chosen by the static class $`S`. A derived class redefines only a method the base declares `virtual`, and marks it `override`, so the method reached from $`S` and the one reached from $`T` coincide for every non virtual method. Redefining a non virtual method, marking `override` without a virtual method in a base, or changing the signature is a type error.
:::

:::theorem "cls_dispatch_agree" (parent := "ud5") (uses := "cls_dispatch, cls_method")
For every well typed program, the method a call resolves to by the static class of the receiver and the method it resolves to by the class tag coincide whenever the method is not virtual. The nearest declaration of a non virtual $`m` from $`S` is also the nearest from $`T`, because no class between $`T` and $`S` redeclares $`m`. There is no Lean proof, the property follows from the rule T-Class by inspection.
:::

:::definition "cls_delete" (parent := "ud5") (lean := "CoreCpp.Typing.cmd, CoreCpp.Eval.cmd, CoreCpp.Program.hasVirtualDtor") (uses := "cls_member, cls_dispatch, judg_ty_cmd, judg_ev_cmd, dom_store, dom_erro")
The command `delete e` applies to a pointer to a class or to a vector. On an object it runs the destructors of the chain from the tag up to the root, each with `this` bound to the object, and removes the record and the field locations from $`\sigma`. A second `delete`, a `delete` through a pointer to a base without a virtual destructor in its chain, and any later access are `error`, the three cases C++17 leaves undefined. `delete nullptr` does nothing, as in C++.

$$`\dfrac{\Gamma \vdash e : C*}{\Gamma \vdash \mathtt{delete}\ e \dashv \Gamma}\;\textsf{(T-Delete)} \qquad \dfrac{\Gamma \vdash e : \mathsf{std{:}{:}vector}\langle\tau\rangle*}{\Gamma \vdash \mathtt{delete}\ e \dashv \Gamma}\;\textsf{(T-DeleteVec)}`

$$`\dfrac{\begin{array}{c} \rho, \sigma \vdash e \Rightarrow \mathsf{loc}\,\ell, \sigma_0 \qquad \sigma_0(\ell) = \mathsf{obj}\,T\,[f_1 \mapsto \ell_1, \ldots, f_n \mapsto \ell_n] \qquad S \text{ the static class of } e \\ S = T \text{ or the chain of } S \text{ has a virtual destructor} \qquad \text{the destructors of the chain of } T \text{ run from } T \text{ up, giving } \sigma_1 \end{array}}{\rho, \sigma \vdash \mathtt{delete}\ e \Rightarrow \mathsf{normal}, \rho, \sigma_1 \setminus \{\ell, \ell_1, \ldots, \ell_n\}}\;\textsf{(Delete)}`

$$`\dfrac{\rho, \sigma \vdash e \Rightarrow \mathsf{loc}\,\ell, \sigma_0 \qquad \sigma_0(\ell) = \mathsf{vec}\,[\ell_1, \ldots, \ell_n]}{\rho, \sigma \vdash \mathtt{delete}\ e \Rightarrow \mathsf{normal}, \rho, \sigma_0 \setminus \{\ell, \ell_1, \ldots, \ell_n\}}\;\textsf{(DeleteVec)} \qquad \dfrac{\rho, \sigma \vdash e \Rightarrow \mathsf{null}, \sigma_0}{\rho, \sigma \vdash \mathtt{delete}\ e \Rightarrow \mathsf{normal}, \rho, \sigma_0}\;\textsf{(DeleteNull)}`
:::

# Static classes and namespaces

:::definition "cls_annotate" (parent := "ud5") (lean := "CoreCpp.Typing.annotate, CoreCpp.Typing.staticClass, CoreCpp.Typing.annExpr, CoreCpp.Typing.annCmd, CoreCpp.Typing.annCmds, CoreCpp.runWith") (uses := "cls_method, cls_delete, judg_ty_expr")
Neither $`\rho` nor $`\sigma` carries types, and the rules MethodCall and Delete need the static class of the receiver. After a program is checked, `annotate` walks it with the typing context and writes into every method call and every `delete` the class the receiver has in $`\Gamma`, and rewrites an unqualified `m(args)` inside a member body into `this->m(args)`. The program runs annotated, and an ill typed program, which `check` rejects, runs as parsed with every dispatch by the tag.
:::

:::definition "cls_namespace" (parent := "ud5") (lean := "CoreCpp.declaration, CoreCpp.classType, CoreCpp.P.qualify") (uses := "parse_program")
A `namespace N { … }` holds classes and namespaces, and the parser flattens it. Every class declared inside is named `N::C`, and every unqualified class name mentioned in a type or in `new` inside the namespace is read as `N::C`. From outside, the class is reached by its qualified name, `N::C`, in types and in `new`. Namespaces add no rule of typing or of evaluation.
:::
