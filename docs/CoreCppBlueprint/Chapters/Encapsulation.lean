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

Classes with `public` and `private` sections, methods, constructors run by `new`, destructors run by `delete`, `this`, single inheritance, subsumption, dispatch by the class tag for `virtual` methods and namespaces.

An abstract data type is a public signature over a private representation, and visibility is a typing rule. Objects are still records of locations with a tag, created by `new` and never copied, and the destructor runs only on `delete`.

The type checker writes the static class of every receiver and of every `delete` into the tree, since $`\rho` and $`\sigma` carry no types.

:::group "encapsulation"
Abstract data types, objects, classes and inheritance.
:::

# Classes and visibility

:::definition "cls_decl" (parent := "encapsulation") (lean := "CoreCpp.ClassDecl, CoreCpp.Field, CoreCpp.Method, CoreCpp.Ctor, CoreCpp.Dtor, CoreCpp.Vis, CoreCpp.Typing.cls, CoreCpp.Typing.memberEnv, CoreCpp.Semantics.ClassOk") (uses := "dom_classes, judg_ty_cmd")
A class has an optional base, fields and methods with a visibility, at most one constructor named after the class and at most one destructor. Members before the first section label are private, as in C++ (N4659 §14 paragraph 3).

The class is well formed, $`\vdash C`, when the conditions of `ClassOk` hold. The base exists and the chain of bases is acyclic. The fields have distinct names, repeat no field of a base, and have storable, non `void` and well formed types. No method has the name of a field. Two methods of one name are distinguishable, {bpref "overload_set"}[], and no signature occurs twice. An operator member takes one parameter, {bpref "op_member"}[].

A method that redefines a method of a base finds it virtual there, carries `override` and keeps the signature, and `override` marks only a redefinition. The result types are `void` or storable, the parameter types bindable, and all are well formed. The constructor of the base takes no parameters, since there are no initialiser lists. Every member body is well typed under `this`, and a member that returns a reference satisfies T-RetRef of {bpref "op_refret"}[].

$$`\dfrac{\begin{array}{c} B \text{ exists, chain acyclic}\qquad \text{fields distinct, new in the chain, storable, not void, well formed} \\ \text{no method named as a field}\qquad \text{methods of one name distinguishable, no signature twice}\qquad \text{operators with one parameter} \\ \text{each redefined } m \text{ is virtual in the base, marked override, same signature}\qquad \text{override only on a redefinition} \\ \text{results void or storable, parameters bindable, all well formed}\qquad B \text{ has no constructor or one without parameters} \\ [\mathtt{this} \mapsto C*, p_1, \ldots, p_k] \vdash c \dashv \Gamma' \text{ with its result type, for each member body}\qquad \text{T-RetRef for each member returning } \tau\& \end{array}}{\vdash \mathtt{class}\ C\ \mathtt{:}\ \mathtt{public}\ B\ \{ \ldots \}}\;\textsf{(T-Class)}`

The context of a member body binds `this` to $`C*` and the parameters as variables, so the current class is the class of `this` in $`\Gamma`.
:::

:::definition "cls_visible" (parent := "encapsulation") (lean := "CoreCpp.TEnv.self, CoreCpp.Typing.fieldType, CoreCpp.Typing.methodCall, CoreCpp.Semantics.MethodSel") (uses := "cls_decl, dom_tenv")
A private member declared in class $`K` is visible exactly when $`\Gamma(\mathtt{this}) = K*`. Visibility is thus a typing rule. The public section of a class is the signature of an abstract data type, and the private section is its representation, reachable only from the member bodies of the class.

$$`\dfrac{C \text{ has } \tau\ f \text{ declared in } K \qquad f \text{ public or } \Gamma(\mathtt{this}) = K*}{\Gamma \vdash e.f : \tau \text{ for } \Gamma \vdash e : C}\;\textsf{(Visible)}`

The same premise applies to methods, {bpref "cls_method"}[].
:::

:::definition "cls_this" (parent := "encapsulation") (lean := "CoreCpp.Typing.expr, CoreCpp.Eval.expr, CoreCpp.Eval.lval, CoreCpp.Semantics.HasType, CoreCpp.Semantics.Eval, CoreCpp.Semantics.LEval") (uses := "judg_ty_expr, judg_ev_expr, judg_ev_lval, dom_env")
Inside a member body `this` is the location of the receiver. The call binds it in $`\rho` as an alias, never as a variable, and it evaluates to a pointer. An unqualified name that is not a variable denotes the member of `this`, both in the type checker and in the evaluator.

$$`\dfrac{\Gamma(\mathtt{this}) = C*}{\Gamma \vdash \mathtt{this} : C*}\;\textsf{(T-This)}`

$$`\dfrac{x \notin \Gamma \qquad \Gamma(\mathtt{this}) = C* \qquad \Gamma \vdash \mathtt{this}\mathtt{->}x : \tau}{\Gamma \vdash x : \tau}\;\textsf{(T-VarField)}`

$$`\dfrac{x \notin \Gamma \qquad \Gamma(\mathtt{this}) = C* \qquad \Gamma \vdash_{\ell} \mathtt{this}\mathtt{->}x : \tau}{\Gamma \vdash_{\ell} x : \tau}\;\textsf{(T-LocVarField)}`

The same holds of a call. An unqualified name that is neither a variable nor a function of the program is a member of the receiver. The evaluator also requires that no header declares the name. The annotation of {bpref "cls_annotate"}[] rewrites such a call into `this->f(…)`, so CallThis applies only to a program that runs as parsed.

$$`\dfrac{\begin{array}{c} f \notin \Gamma\qquad f \text{ is no function of the program}\qquad \Gamma(\mathtt{this}) = C* \\ \Gamma \vdash \mathtt{this}\mathtt{->}f(e_1, \ldots, e_k) : \tau \end{array}}{\Gamma \vdash f(e_1, \ldots, e_k) : \tau}\;\textsf{(T-CallThis)}`

$$`\dfrac{\rho(\mathtt{this}) = \ell}{\rho, \sigma \vdash \mathtt{this} \Rightarrow \mathsf{loc}\,\ell, \sigma}\;\textsf{(This)}`

$$`\dfrac{x \notin \rho \qquad \rho(\mathtt{this}) = \ell \qquad \sigma(\ell) = \mathsf{obj}\,C\,[\ldots x \mapsto \ell_x \ldots]}{\rho, \sigma \vdash x \Rightarrow_{\ell} \ell_x, \sigma}\;\textsf{(LocVarField)}`

$$`\dfrac{\begin{array}{c} f \notin \rho\qquad f \text{ is no function of the program or of a header}\qquad \rho(\mathtt{this}) = \ell \\ \rho, \sigma \vdash \mathtt{this}\mathtt{->}f(e_1, \ldots, e_k) \Rightarrow v, \sigma' \end{array}}{\rho, \sigma \vdash f(e_1, \ldots, e_k) \Rightarrow v, \sigma'}\;\textsf{(CallThis)}`
:::

# Objects

:::definition "cls_new" (parent := "encapsulation") (lean := "CoreCpp.Typing.expr, CoreCpp.Eval.expr, CoreCpp.Program.allFields, CoreCpp.Program.chain, CoreCpp.Semantics.HasType, CoreCpp.Semantics.Eval, CoreCpp.Semantics.Ctors") (uses := "expr_new, cls_decl, cls_member, dom_store")
The expression `new C(args)` allocates one location per field of the whole chain of $`C`, the root base first, and then the tagged record. It runs the constructors from the root base down, each with `this` bound to the object. The constructor of $`C` receives the arguments and the others none, since there are no initialiser lists.

A class without a constructor is created by `new C()` and keeps the default values.

$$`\dfrac{C \mapsto \mathtt{class}\ C\ \{\ldots C(p_1\,x_1, \ldots, p_k\,x_k)\ \{c\} \ldots\} \qquad \text{arguments as in T-Call}}{\Gamma \vdash \mathtt{new}\ C(e_1, \ldots, e_k) : C*}\;\textsf{(T-New)}`

$$`\dfrac{\begin{array}{c} f_1 \ldots f_n \text{ the fields of the chain of } C\qquad (\ell_i, \sigma_i) = \mathrm{alloc}(\sigma_{i-1}, \mathrm{default}\,\tau_i) \\ (\ell, \sigma') = \mathrm{alloc}(\sigma_n, \mathsf{obj}\,C\,[f_1 \mapsto \ell_1, \ldots, f_n \mapsto \ell_n]) \\ \text{the constructors of the chain run from the root down} \\ \text{with } \mathtt{this} \mapsto \ell \text{, giving } \sigma'' \end{array}}{\rho, \sigma \vdash \mathtt{new}\ C(e_1, \ldots, e_k) \Rightarrow \mathsf{loc}\,\ell, \sigma''}\;\textsf{(New)}`
:::

:::definition "cls_member" (parent := "encapsulation") (lean := "CoreCpp.Eval.runMember, CoreCpp.Typing.checkArgs, CoreCpp.Semantics.CheckArgs, CoreCpp.Semantics.Member") (uses := "fun_call, param_ref, judg_ev_cmd, dom_env")
The call of a member body, a method, a constructor or a destructor, binds `this` to the location $`\ell` of the receiver as an alias. It binds the parameters as the call of a function does, by value with a fresh copy and by reference with an alias. The return frees the copies and the locals of the body, never the receiver.

$$`\dfrac{\begin{array}{c} \text{for each } i \text{ left to right, } \sigma'_0 = \sigma \\ p_i = \tau_i \colon \ \rho, \sigma'_{i-1} \vdash e_i \Rightarrow v_i, \sigma_i \quad (\ell_i, \sigma'_i) = \mathrm{alloc}(\sigma_i, v_i) \\ p_i = \tau_i\& \colon \ \rho, \sigma'_{i-1} \vdash e_i \Rightarrow_{\ell} \ell_i, \sigma'_i \\ \rho_m = [\mathtt{this} \mapsto \ell, x_1 \mapsto \ell_1, \ldots, x_k \mapsto \ell_k]\qquad \rho_m, \sigma'_k \vdash c \Rightarrow r, \rho', \sigma'' \qquad \mathsf{Returns}(r, \tau, v) \end{array}}{\rho, \sigma \vdash \mathrm{member}\ \ell\ (e_1, \ldots, e_k) \Rightarrow v, \sigma'' \setminus (\{\ell_i \mid p_i \text{ by value}\} \cup \mathrm{fresh}(\rho_m, \rho'))}\;\textsf{(Member)}`

The predicate $`\mathsf{Returns}` of {bpref "fun_call"}[] gives the result. A non `void` member that ends without `return` has no derivation, an `error` of the evaluator.
:::

:::definition "cls_method" (parent := "encapsulation") (lean := "CoreCpp.Typing.methodCall, CoreCpp.Eval.expr, CoreCpp.Eval.resolve, CoreCpp.Program.findMethod, CoreCpp.Semantics.MethodSel, CoreCpp.Semantics.Eval, CoreCpp.Program.resolve, CoreCpp.Semantics.CallMethod") (uses := "cls_member, cls_visible, cls_dispatch, judg_ty_expr, judg_ev_expr")
A method call `e.m(args)` needs a receiver of class type and `e->m(args)` a receiver of pointer type. The method is the nearest $`m` in the chain of the static class of the receiver, it must be visible, and the arguments are checked as in a call. An unqualified call `m(args)` inside a member body is `this->m(args)`. A method that returns a reference has the rules of {bpref "op_refret"}[], which read the location it returns.

$$`\dfrac{\begin{array}{c} \Gamma \vdash e : C\qquad C \text{ has } \tau\ m(p_1\,x_1, \ldots, p_k\,x_k) \text{ visible from } \Gamma \\ \text{arguments as in T-Call} \end{array}}{\Gamma \vdash e.m(e_1, \ldots, e_k) : \tau}\;\textsf{(T-Method)}`

$$`\dfrac{\begin{array}{c} \Gamma \vdash e : C*\qquad C \text{ has } \tau\ m(\ldots) \text{ visible from } \Gamma \\ \text{arguments as in T-Call} \end{array}}{\Gamma \vdash e\mathtt{->}m(e_1, \ldots, e_k) : \tau}\;\textsf{(T-MethodArrow)}`

$$`\dfrac{\begin{array}{c} \rho, \sigma \vdash e \Rightarrow_{\ell} \ell, \sigma_0 \text{ or } \rho, \sigma \vdash e \Rightarrow \mathsf{loc}\,\ell, \sigma_0\qquad \sigma_0(\ell) = \mathsf{obj}\,T\,[\ldots] \\ S \text{ the static class of } e \\ m \mapsto \tau\ m(\ldots)\{c\} \text{ nearest } S \text{, or nearest } T \text{ when virtual, returning no reference} \\ \rho, \sigma_0 \vdash \mathrm{member}\ \ell\ (e_1, \ldots, e_k) \Rightarrow v, \sigma' \end{array}}{\rho, \sigma \vdash e.m(e_1, \ldots, e_k) \Rightarrow v, \sigma'}\;\textsf{(MethodCall)}`
:::

# Inheritance

:::definition "cls_subsumption" (parent := "encapsulation") (lean := "CoreCpp.Typing.compat, CoreCpp.Typing.related, CoreCpp.Program.subclass") (uses := "cls_decl, judg_ty_expr")
A pointer to a derived class is accepted where a pointer to its base is expected, in declarations, assignments, arguments, returns, comparisons and the branches of `?:`. It is the only conversion between pointers to classes, and the other direction is a type error.

$$`\dfrac{D \text{ derives from } B}{\mathsf{Compat}(D*, B*)}\;\textsf{(Subsumption)}`
:::

:::definition "cls_dispatch" (parent := "encapsulation") (lean := "CoreCpp.Eval.resolve, CoreCpp.Program.findMethod, CoreCpp.Typing.cls, CoreCpp.Semantics.ClassOk, CoreCpp.Program.resolve, CoreCpp.Method.virtual") (uses := "cls_decl, cls_subsumption, dom_classes")
A method is virtual when it is declared `virtual` or marked `override`, `Method.virtual`. An override is virtual without the word `virtual`, as in C++ (N4659 §13.3 paragraph 2). A third class of a chain may therefore override it again, and a call through a pointer to the middle class dispatches.

The class tag $`T` of the receiver chooses a virtual method, the nearest declaration in the chain of $`T`, so a call through a base pointer reaches the override of the derived class. The static class $`S` chooses a non virtual method.

A derived class redefines only a method that is virtual in the base, and marks it `override`. So the method reached from $`S` and the one reached from $`T` coincide for every non virtual method.

Redefining a non virtual method, marking `override` without a virtual method in a base, or changing the signature is a type error.
:::

:::theorem "cls_dispatch_agree" (parent := "encapsulation") (uses := "cls_dispatch, cls_method")
For every well typed program, the method a call resolves to by the static class of the receiver and the method it resolves to by the class tag coincide whenever the method is not virtual.

The nearest declaration of a non virtual $`m` from $`S` is also the nearest from $`T`, because no class between $`T` and $`S` redeclares $`m` with its signature. The property follows from the rule T-Class by inspection, and there is no Lean proof.
:::

:::definition "cls_delete" (parent := "encapsulation") (lean := "CoreCpp.Typing.cmd, CoreCpp.Eval.cmd, CoreCpp.Program.hasVirtualDtor, CoreCpp.Semantics.Check, CoreCpp.Semantics.Exec, CoreCpp.Semantics.Dtors") (uses := "cls_member, cls_dispatch, judg_ty_cmd, judg_ev_cmd, dom_store, dom_error")
The command `delete e` applies to a pointer to a class or to an object type of the library, whose rule `DeleteLib` in {bpref "std_uses"}[] frees what the module owns and then the location of the instance.

On an object it runs the destructors of the chain from the tag up to the root, each with `this` bound to the object, and removes the record and the field locations from $`\sigma`.

A second `delete` and any later access through the pointer have no derivation. So does a `delete` through a pointer to a base without a virtual destructor in its chain. The evaluator gives `error` in the three cases, which C++17 leaves undefined (N4659 §8.3.5 paragraphs 2 and 3, §6.7 paragraph 4). The command `delete nullptr` runs no destructor, as in C++ (N4659 §8.3.5 paragraph 6).

$$`\dfrac{\Gamma \vdash e : C*}{\Gamma \vdash \mathtt{delete}\ e \dashv \Gamma}\;\textsf{(T-Delete)}`

$$`\dfrac{\Gamma \vdash e : L\langle\bar{\tau}\rangle* \qquad L\langle\bar{\tau}\rangle \text{ an object type} \qquad \Gamma \vdash_L \mathtt{delete}\ \mathsf{ok}}{\Gamma \vdash \mathtt{delete}\ e \dashv \Gamma}\;\textsf{(T-DeleteLib)}`

$$`\dfrac{\begin{array}{c} \rho, \sigma \vdash e \Rightarrow \mathsf{loc}\,\ell, \sigma_0\qquad \sigma_0(\ell) = \mathsf{obj}\,T\,[f_1 \mapsto \ell_1, \ldots, f_n \mapsto \ell_n] \\ S \text{ the static class of } e\qquad S = T \text{ or the chain of } S \text{ has a virtual destructor} \\ \text{the destructors of the chain of } T \text{ run from } T \text{ up, giving } \sigma_1 \end{array}}{\rho, \sigma \vdash \mathtt{delete}\ e \Rightarrow \mathsf{normal}, \rho, \sigma_1 \setminus \{\ell, \ell_1, \ldots, \ell_n\}}\;\textsf{(Delete)}`

$$`\dfrac{\rho, \sigma \vdash e \Rightarrow \mathsf{null}, \sigma_0}{\rho, \sigma \vdash \mathtt{delete}\ e \Rightarrow \mathsf{normal}, \rho, \sigma_0}\;\textsf{(DeleteNull)}`
:::

# Static classes and namespaces

:::definition "cls_annotate" (parent := "encapsulation") (lean := "CoreCpp.Typing.annotate, CoreCpp.Typing.staticClass, CoreCpp.Typing.annExpr, CoreCpp.Typing.annCmd, CoreCpp.Typing.annCmds, CoreCpp.runWith") (uses := "cls_method, cls_delete, judg_ty_expr")
Neither $`\rho` nor $`\sigma` carries types, and the rules MethodCall and Delete need the static class of the receiver.

After a program is checked, `annotate` walks it with the typing context. It writes into every method call and every `delete` the class the receiver has in $`\Gamma`. It also rewrites an unqualified `m(args)` inside a member body into `this->m(args)`.

The program runs annotated. An ill typed program, which `check` rejects, runs as parsed, with every dispatch by the tag.
:::

:::definition "cls_namespace" (parent := "encapsulation") (lean := "CoreCpp.declaration, CoreCpp.classType, CoreCpp.P.qualify") (uses := "parse_program")
A `namespace N { … }` holds classes and namespaces, and the parser flattens it. Every class declared inside is named `N::C`, and the parser reads every unqualified class name in a type or in `new` inside the namespace as `N::C`. Outside the namespace the class has its qualified name, `N::C`, in types and in `new`. Namespaces add no rule of typing or of evaluation.
:::

# Rules of the chapter

Every typing rule and every evaluation rule of this chapter, in the order of its sections, the typing rules of each section before its evaluation rules. The section named above each rule states it with its explanation and with the definition of its notation.

*Classes and visibility*

$$`\dfrac{\begin{array}{c} B \text{ exists, chain acyclic}\qquad \text{fields distinct, new in the chain, storable, not void, well formed} \\ \text{no method named as a field}\qquad \text{methods of one name distinguishable, no signature twice}\qquad \text{operators with one parameter} \\ \text{each redefined } m \text{ is virtual in the base, marked override, same signature}\qquad \text{override only on a redefinition} \\ \text{results void or storable, parameters bindable, all well formed}\qquad B \text{ has no constructor or one without parameters} \\ [\mathtt{this} \mapsto C*, p_1, \ldots, p_k] \vdash c \dashv \Gamma' \text{ with its result type, for each member body}\qquad \text{T-RetRef for each member returning } \tau\& \end{array}}{\vdash \mathtt{class}\ C\ \mathtt{:}\ \mathtt{public}\ B\ \{ \ldots \}}\;\textsf{(T-Class)}`

$$`\dfrac{C \text{ has } \tau\ f \text{ declared in } K \qquad f \text{ public or } \Gamma(\mathtt{this}) = K*}{\Gamma \vdash e.f : \tau \text{ for } \Gamma \vdash e : C}\;\textsf{(Visible)}`

$$`\dfrac{\Gamma(\mathtt{this}) = C*}{\Gamma \vdash \mathtt{this} : C*}\;\textsf{(T-This)}`

$$`\dfrac{x \notin \Gamma \qquad \Gamma(\mathtt{this}) = C* \qquad \Gamma \vdash \mathtt{this}\mathtt{->}x : \tau}{\Gamma \vdash x : \tau}\;\textsf{(T-VarField)}`

$$`\dfrac{x \notin \Gamma \qquad \Gamma(\mathtt{this}) = C* \qquad \Gamma \vdash_{\ell} \mathtt{this}\mathtt{->}x : \tau}{\Gamma \vdash_{\ell} x : \tau}\;\textsf{(T-LocVarField)}`

$$`\dfrac{\begin{array}{c} f \notin \Gamma\qquad f \text{ is no function of the program}\qquad \Gamma(\mathtt{this}) = C* \\ \Gamma \vdash \mathtt{this}\mathtt{->}f(e_1, \ldots, e_k) : \tau \end{array}}{\Gamma \vdash f(e_1, \ldots, e_k) : \tau}\;\textsf{(T-CallThis)}`

 

$$`\dfrac{\rho(\mathtt{this}) = \ell}{\rho, \sigma \vdash \mathtt{this} \Rightarrow \mathsf{loc}\,\ell, \sigma}\;\textsf{(This)}`

$$`\dfrac{x \notin \rho \qquad \rho(\mathtt{this}) = \ell \qquad \sigma(\ell) = \mathsf{obj}\,C\,[\ldots x \mapsto \ell_x \ldots]}{\rho, \sigma \vdash x \Rightarrow_{\ell} \ell_x, \sigma}\;\textsf{(LocVarField)}`

$$`\dfrac{\begin{array}{c} f \notin \rho\qquad f \text{ is no function of the program or of a header}\qquad \rho(\mathtt{this}) = \ell \\ \rho, \sigma \vdash \mathtt{this}\mathtt{->}f(e_1, \ldots, e_k) \Rightarrow v, \sigma' \end{array}}{\rho, \sigma \vdash f(e_1, \ldots, e_k) \Rightarrow v, \sigma'}\;\textsf{(CallThis)}`

*Objects*

$$`\dfrac{C \mapsto \mathtt{class}\ C\ \{\ldots C(p_1\,x_1, \ldots, p_k\,x_k)\ \{c\} \ldots\} \qquad \text{arguments as in T-Call}}{\Gamma \vdash \mathtt{new}\ C(e_1, \ldots, e_k) : C*}\;\textsf{(T-New)}`

$$`\dfrac{\begin{array}{c} \Gamma \vdash e : C\qquad C \text{ has } \tau\ m(p_1\,x_1, \ldots, p_k\,x_k) \text{ visible from } \Gamma \\ \text{arguments as in T-Call} \end{array}}{\Gamma \vdash e.m(e_1, \ldots, e_k) : \tau}\;\textsf{(T-Method)}`

$$`\dfrac{\begin{array}{c} \Gamma \vdash e : C*\qquad C \text{ has } \tau\ m(\ldots) \text{ visible from } \Gamma \\ \text{arguments as in T-Call} \end{array}}{\Gamma \vdash e\mathtt{->}m(e_1, \ldots, e_k) : \tau}\;\textsf{(T-MethodArrow)}`

 

$$`\dfrac{\begin{array}{c} f_1 \ldots f_n \text{ the fields of the chain of } C\qquad (\ell_i, \sigma_i) = \mathrm{alloc}(\sigma_{i-1}, \mathrm{default}\,\tau_i) \\ (\ell, \sigma') = \mathrm{alloc}(\sigma_n, \mathsf{obj}\,C\,[f_1 \mapsto \ell_1, \ldots, f_n \mapsto \ell_n]) \\ \text{the constructors of the chain run from the root down} \\ \text{with } \mathtt{this} \mapsto \ell \text{, giving } \sigma'' \end{array}}{\rho, \sigma \vdash \mathtt{new}\ C(e_1, \ldots, e_k) \Rightarrow \mathsf{loc}\,\ell, \sigma''}\;\textsf{(New)}`

$$`\dfrac{\begin{array}{c} \text{for each } i \text{ left to right, } \sigma'_0 = \sigma \\ p_i = \tau_i \colon \ \rho, \sigma'_{i-1} \vdash e_i \Rightarrow v_i, \sigma_i \quad (\ell_i, \sigma'_i) = \mathrm{alloc}(\sigma_i, v_i) \\ p_i = \tau_i\& \colon \ \rho, \sigma'_{i-1} \vdash e_i \Rightarrow_{\ell} \ell_i, \sigma'_i \\ \rho_m = [\mathtt{this} \mapsto \ell, x_1 \mapsto \ell_1, \ldots, x_k \mapsto \ell_k]\qquad \rho_m, \sigma'_k \vdash c \Rightarrow r, \rho', \sigma'' \qquad \mathsf{Returns}(r, \tau, v) \end{array}}{\rho, \sigma \vdash \mathrm{member}\ \ell\ (e_1, \ldots, e_k) \Rightarrow v, \sigma'' \setminus (\{\ell_i \mid p_i \text{ by value}\} \cup \mathrm{fresh}(\rho_m, \rho'))}\;\textsf{(Member)}`

$$`\dfrac{\begin{array}{c} \rho, \sigma \vdash e \Rightarrow_{\ell} \ell, \sigma_0 \text{ or } \rho, \sigma \vdash e \Rightarrow \mathsf{loc}\,\ell, \sigma_0\qquad \sigma_0(\ell) = \mathsf{obj}\,T\,[\ldots] \\ S \text{ the static class of } e \\ m \mapsto \tau\ m(\ldots)\{c\} \text{ nearest } S \text{, or nearest } T \text{ when virtual, returning no reference} \\ \rho, \sigma_0 \vdash \mathrm{member}\ \ell\ (e_1, \ldots, e_k) \Rightarrow v, \sigma' \end{array}}{\rho, \sigma \vdash e.m(e_1, \ldots, e_k) \Rightarrow v, \sigma'}\;\textsf{(MethodCall)}`

*Inheritance*

$$`\dfrac{D \text{ derives from } B}{\mathsf{Compat}(D*, B*)}\;\textsf{(Subsumption)}`

$$`\dfrac{\Gamma \vdash e : C*}{\Gamma \vdash \mathtt{delete}\ e \dashv \Gamma}\;\textsf{(T-Delete)}`

$$`\dfrac{\Gamma \vdash e : L\langle\bar{\tau}\rangle* \qquad L\langle\bar{\tau}\rangle \text{ an object type} \qquad \Gamma \vdash_L \mathtt{delete}\ \mathsf{ok}}{\Gamma \vdash \mathtt{delete}\ e \dashv \Gamma}\;\textsf{(T-DeleteLib)}`

 

$$`\dfrac{\begin{array}{c} \rho, \sigma \vdash e \Rightarrow \mathsf{loc}\,\ell, \sigma_0\qquad \sigma_0(\ell) = \mathsf{obj}\,T\,[f_1 \mapsto \ell_1, \ldots, f_n \mapsto \ell_n] \\ S \text{ the static class of } e\qquad S = T \text{ or the chain of } S \text{ has a virtual destructor} \\ \text{the destructors of the chain of } T \text{ run from } T \text{ up, giving } \sigma_1 \end{array}}{\rho, \sigma \vdash \mathtt{delete}\ e \Rightarrow \mathsf{normal}, \rho, \sigma_1 \setminus \{\ell, \ell_1, \ldots, \ell_n\}}\;\textsf{(Delete)}`

$$`\dfrac{\rho, \sigma \vdash e \Rightarrow \mathsf{null}, \sigma_0}{\rho, \sigma \vdash \mathtt{delete}\ e \Rightarrow \mathsf{normal}, \rho, \sigma_0}\;\textsf{(DeleteNull)}`
