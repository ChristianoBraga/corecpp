import Verso
import VersoManual
import VersoBlueprint
import CoreCpp.Syntax
import CoreCpp.Parser
import CoreCpp.Templates
import CoreCpp.Typing
import CoreCpp.Eval

open Verso.Genre
open Verso.Genre.Manual
open Informal

set_option verso.blueprint.foldCodeBlocks true

#doc (Manual) "Type systems" =>

Overloading of functions and methods by the type of the arguments, operator members, class templates instantiated by substitution, subtyping and type inference.

A name denotes an overload set, and a call selects one candidate. An infix operator on an object, and the indexing of an object, are the calls of the members `operator⊕` and `operator[]`. A member may return $`\tau\&`, so `v[i] = x` assigns to the location `operator[]` returns.

A template is expanded before the program is checked, so instantiation costs nothing at run time. Only the instantiations are checked.

:::group "type_systems"
Overloading, polymorphism, subtyping and inference.
:::

# Overloading

:::definition "overload_set" (parent := "type_systems") (lean := "CoreCpp.sigOf, CoreCpp.Program.funsNamed, CoreCpp.Program.findMethods, CoreCpp.Typing.distinguishable") (uses := "fun_decl, cls_decl")
A name denotes an overload set. It holds the functions of the program with that name, or the methods of that name along the chain of a class, one per signature. A method of a derived class replaces the one of a base with the same signature. A different signature is another overload, so the subset has no name hiding. Two declarations of one name coexist only when they are distinguishable.

$$`\dfrac{\text{arities differ, or } \exists i.\ p_i \neq q_i \text{ and neither } p_i \text{ nor } q_i \text{ is a } \mathtt{std{:}{:}function}}{\text{the two declarations are overloads}}\;\textsf{(Distinguishable)}`

The restriction keeps a lambda argument from deciding a call, which would ask for the type of the lambda before the candidate that gives it is known. A `std::function` is an object of {bpref "std_function"}[], so a parameter has it only by reference. The exclusion applies there, and two functions `g` whose parameters are `std::function<int(int)>&` and `std::function<bool(int)>&` are not distinguishable.
:::

:::definition "overload_pick" (parent := "type_systems") (lean := "CoreCpp.Typing.pickOverload, CoreCpp.Typing.resolveFun, CoreCpp.Typing.resolveMethod, CoreCpp.Semantics.MethodSel") (uses := "overload_set, fun_call, cls_method")
A call collects the candidates of its arity that accept the arguments, each argument by value acceptable at the type of its parameter and each argument of a reference parameter denoting a location of that type. The choice is the exact candidate when several accept.

$$`\dfrac{\begin{array}{c} A = \text{the candidates of } \mathrm{cand}(f, k) \text{ that accept } e_1, \ldots, e_k \\ A \text{ has one element whose parameters are} \\ \text{exactly the types of the arguments, or } A \text{ is a singleton} \end{array}}{\text{the call of } f \text{ selects that candidate}}\;\textsf{(T-Overload)}`

With no candidate of the arity the error is an arity error, measured on the first candidate. With $`A` empty the error is the one of the single candidate of that arity, when there is one, and no overload otherwise. With two or more in $`A` and no exact one the call is ambiguous. Core C++ does not rank implicit conversion sequences, as C++ does (N4659 §16.3.3.2).
:::

:::definition "overload_sig" (parent := "type_systems") (lean := "CoreCpp.FunEnv.lookupSig, CoreCpp.Eval.resolve, CoreCpp.Typing.annotate, CoreCpp.Program.resolve") (uses := "overload_pick, judg_ev_expr")
Overloading adds no evaluation rule. The type checker writes the signature of the chosen candidate into the field `sig` of the call. The evaluator looks a function or a method up by name and signature instead of by name alone. A program that was not annotated, which the checker rejects first, runs with the first candidate of the name.
:::

# Operator members

:::definition "op_member" (parent := "type_systems") (lean := "CoreCpp.operatorName, CoreCpp.Typing.methodCall, CoreCpp.Semantics.MethodSel") (uses := "overload_pick, cls_method")
An infix operator whose left operand is an object, and the indexing of an object, are the calls of members. The left operand decides, so no operator on `int` or `bool` changes meaning, and `&&` and `||` are not overloaded.

$$`\dfrac{\begin{array}{c} \star \text{ a binary operator other than } \mathtt{\&\&} \text{ and } \mathtt{||}\qquad \Gamma \vdash e_1 : C \\ C \text{ has } \mathtt{operator}\star \text{ visible from } \Gamma\qquad \Gamma \vdash e_1.\mathtt{operator}\star(e_2) : \tau \end{array}}{\Gamma \vdash e_1 \star e_2 : \tau}\;\textsf{(T-OpBin)}`

$$`\dfrac{\begin{array}{c} \Gamma \vdash e : C\qquad C \text{ has } \mathtt{operator[]} \text{ visible from } \Gamma \\ \Gamma \vdash e.\mathtt{operator[]}(i) : \tau \end{array}}{\Gamma \vdash e[i] : \tau}\;\textsf{(T-OpIndex)}`

The type checker rewrites both forms into the call of the member, and from there they are ordinary method calls, with the visibility, the overload resolution and the dispatch of a method. The trace shows the rule `MethodCall` under the infix form.
:::

:::definition "op_refret" (parent := "type_systems") (lean := "CoreCpp.Method, CoreCpp.Typing.refReturns, CoreCpp.Typing.refRets, CoreCpp.Eval.callMethod, CoreCpp.Semantics.RefReturns, CoreCpp.Semantics.CallMethod") (uses := "op_member, judg_ev_lval")
A member may return $`\tau\&`, with $`\tau` not `void`. Every `return e` of its body then has an operand that denotes a location under $`\Gamma_m`, the context of `this` and of the parameters, without the locals of the body. The walk does not enter the body of a lambda, because the `return` of a lambda is the lambda's. The rule T-Ret of the body then requires $`\Gamma \vdash e \lhd \tau`.

$$`\dfrac{\tau \neq \mathsf{void} \qquad \text{every } \mathtt{return}\ e \text{ of } c \text{ has } \Gamma_m \vdash_{\ell} e : \tau' \text{ for some } \tau'}{\vdash \tau\&\ m(\ldots)\ \{c\} \text{ in } C}\;\textsf{(T-RetRef)}`

$$`\dfrac{\Gamma \vdash e : C \qquad \mathtt{operator[]} \text{ selected as in T-Method, returning } \tau\&}{\Gamma \vdash_{\ell} e[i] : \tau}\;\textsf{(T-LocOpIndex)}`

$$`\dfrac{m \text{ selected as in T-Method, returning } \tau\&}{\Gamma \vdash_{\ell} e.m(e_1, \ldots, e_k) : \tau}\;\textsf{(T-LocMethod)}`

The rule T-LocMethod also covers `e->m(…)`, with the selection of T-MethodArrow.

The annotation rewrites the `return e` of such a member as `return &e`, the location as a value, an expression no program writes. Its type is the type of the location it denotes.

$$`\dfrac{\Gamma \vdash_{\ell} e : \tau}{\Gamma \vdash \&e : \tau}\;\textsf{(T-LocOf)}`

$$`\dfrac{\rho, \sigma \vdash e \Rightarrow_{\ell} \ell, \sigma'}{\rho, \sigma \vdash \&e \Rightarrow \mathsf{loc}\ \ell, \sigma'}\;\textsf{(LocOf)}`

$$`\dfrac{\text{the premises of MethodCall, except that } m \text{ returns } \tau\the premises of MethodCall, with } m \text{ returning } \tau\& \text{ and } \text{, with } v = \mathsf{loc}\,\ell'}{\rho, \sigma \vdash e.m(e_1, \ldots, e_k) \Rightarrow_{\ell} \ell', \sigma'}\;\textsf{(MethodLoc)}`

$$`\dfrac{\text{the premises of MethodCall, except that } m \text{ returns } \tau\the premises of MethodCall, with } m \text{ returning } \tau\& \text{ and } \text{, with } v = \mathsf{loc}\,\ell' \qquad \sigma'(\ell') = w}{\rho, \sigma \vdash e.m(e_1, \ldots, e_k) \Rightarrow w, \sigma'}\;\textsf{(MethodCallRef)}`

Since the locals of the body are outside $`\Gamma_m`, a member never returns the location of one of them. The return frees the location of a parameter by value, so a member that returns it returns a freed location. Reading that location has no derivation, an `error` of the evaluator by the general rule of locations outside $`\sigma`.
:::

# Parametric polymorphism

:::definition "tmpl_decl" (parent := "type_systems") (lean := "CoreCpp.Decl, CoreCpp.Program.templates, CoreCpp.classType") (uses := "cls_decl, gram_full")
A class template is a class with a type parameter, `template<typename T> class C`, and it is instantiated only in type position, `C<int>`. The name of an instantiation is the text of its type, `Stack<int>`, so the name in the source and the name of the expanded class agree. The parser builds it when it reads a type. The grammar admits one type parameter.
:::

:::definition "tmpl_inst" (parent := "type_systems") (lean := "CoreCpp.Templates.instantiate, CoreCpp.Templates.substClass, CoreCpp.Templates.substTy, CoreCpp.Templates.substName") (uses := "tmpl_decl")
Instantiation is substitution, and it precedes every other judgment.

$$`\dfrac{\begin{array}{c} p \text{ has } \mathtt{template{<}typename\ T{>}\ class}\ C\qquad C{<}\tau{>} \text{ mentioned in } p \\ C{<}\tau{>} \notin \text{class table of } p \end{array}}{p \longrightarrow p, \mathtt{class}\ C{<}\tau{>}\ \{ \ldots [T := \tau] \ldots \}}\;\textsf{(Inst)}`

The substitution replaces the type `T` in the base, the fields, the parameters, the results and the bodies, the types of local declarations, of `new` and of lambdas included. It also substitutes the type arguments in the name of every class it mentions, so `Node<T>*` inside `List<T>` becomes `Node<int>*` in `List<int>`.

The rule applies to a fixed point, because the class it adds may mention another instantiation. After 32 rounds the expansion fails, which rejects a template that mentions ever larger instantiations of itself. The expansion is idempotent, so `check` and `annotate`, which `runWith` calls, both apply it.

A template is never checked, only its instantiations are. Two instantiations of one template are two independent classes with no subtype relation between them.
:::

# Subtyping and inference

:::theorem "subtyping" (parent := "type_systems") (uses := "cls_subsumption, tmpl_inst")
Subtyping is the rule Subsumption of {bpref "cls_subsumption"}[], the relation $`\mathsf{Compat}(D*, B*)`. It is the only conversion between pointers to classes. No typing rule derives $`\Gamma \vdash e : B*` from $`\Gamma \vdash e : D*`. The rules that require $`\mathsf{Compat}` apply it instead, in declarations, assignments, arguments, results, comparisons and the branches of `?:`.

Subtype polymorphism and parametric polymorphism do not compose in the subset. Two instantiations of one template have no subtype relation, so a `Stack<D*>*` is not accepted where a `Stack<B*>*` is expected. Such a conversion would be unsound, because a `Stack<B*>` accepts a `push` of any `B*` and a `Stack<D*>` does not. Variance is left out of the subset.
:::

:::definition "inference" (parent := "type_systems") (lean := "CoreCpp.Cmd") (uses := "cmd_decl")
Type inference in Core C++ is local. The rule of `auto` is T-Auto of {bpref "cmd_decl"}[], and it covers pointers to instantiations, since a pointer has values.

$$`\dfrac{\Gamma \vdash e : \tau \qquad \mathsf{HasValues}(\tau) \qquad \mathsf{Storable}(\tau)}{\Gamma \vdash \mathtt{auto}\ x = e \dashv \Gamma[x \mapsto \tau]}\;\textsf{(T-Auto)}`

A lambda has no type of its own, so it never initialises an `auto`, which the grammar already guarantees. Core C++ has no inference over a whole program, such as the type inference of Hindley (Trans. AMS 146, 1969, pp. 29–60, doi:10.1090/S0002-9947-1969-0253905-6) and Milner (JCSS 17, 1978, pp. 348–375, doi:10.1016/0022-0000(78)90014-4).
:::

# Rules of the chapter

Every definition, every typing rule and every evaluation rule of this chapter, in the order of its sections, the typing rules of each section before its evaluation rules. The section named above each rule states it with its explanation and with the definition of its notation.

*Overloading*

$$`\dfrac{\text{arities differ, or } \exists i.\ p_i \neq q_i \text{ and neither } p_i \text{ nor } q_i \text{ is a } \mathtt{std{:}{:}function}}{\text{the two declarations are overloads}}\;\textsf{(Distinguishable)}`

$$`\dfrac{\begin{array}{c} A = \text{the candidates of } \mathrm{cand}(f, k) \text{ that accept } e_1, \ldots, e_k \\ A \text{ has one element whose parameters are} \\ \text{exactly the types of the arguments, or } A \text{ is a singleton} \end{array}}{\text{the call of } f \text{ selects that candidate}}\;\textsf{(T-Overload)}`

*Operator members*

$$`\dfrac{\begin{array}{c} \star \text{ a binary operator other than } \mathtt{\&\&} \text{ and } \mathtt{||}\qquad \Gamma \vdash e_1 : C \\ C \text{ has } \mathtt{operator}\star \text{ visible from } \Gamma\qquad \Gamma \vdash e_1.\mathtt{operator}\star(e_2) : \tau \end{array}}{\Gamma \vdash e_1 \star e_2 : \tau}\;\textsf{(T-OpBin)}`

$$`\dfrac{\begin{array}{c} \Gamma \vdash e : C\qquad C \text{ has } \mathtt{operator[]} \text{ visible from } \Gamma \\ \Gamma \vdash e.\mathtt{operator[]}(i) : \tau \end{array}}{\Gamma \vdash e[i] : \tau}\;\textsf{(T-OpIndex)}`

$$`\dfrac{\tau \neq \mathsf{void} \qquad \text{every } \mathtt{return}\ e \text{ of } c \text{ has } \Gamma_m \vdash_{\ell} e : \tau' \text{ for some } \tau'}{\vdash \tau\&\ m(\ldots)\ \{c\} \text{ in } C}\;\textsf{(T-RetRef)}`

$$`\dfrac{\Gamma \vdash e : C \qquad \mathtt{operator[]} \text{ selected as in T-Method, returning } \tau\&}{\Gamma \vdash_{\ell} e[i] : \tau}\;\textsf{(T-LocOpIndex)}`

$$`\dfrac{m \text{ selected as in T-Method, returning } \tau\&}{\Gamma \vdash_{\ell} e.m(e_1, \ldots, e_k) : \tau}\;\textsf{(T-LocMethod)}`

$$`\dfrac{\Gamma \vdash_{\ell} e : \tau}{\Gamma \vdash \&e : \tau}\;\textsf{(T-LocOf)}`

 

$$`\dfrac{\rho, \sigma \vdash e \Rightarrow_{\ell} \ell, \sigma'}{\rho, \sigma \vdash \&e \Rightarrow \mathsf{loc}\ \ell, \sigma'}\;\textsf{(LocOf)}`

$$`\dfrac{\text{the premises of MethodCall, except that } m \text{ returns } \tau\the premises of MethodCall, with } m \text{ returning } \tau\& \text{ and } \text{, with } v = \mathsf{loc}\,\ell'}{\rho, \sigma \vdash e.m(e_1, \ldots, e_k) \Rightarrow_{\ell} \ell', \sigma'}\;\textsf{(MethodLoc)}`

$$`\dfrac{\text{the premises of MethodCall, except that } m \text{ returns } \tau\the premises of MethodCall, with } m \text{ returning } \tau\& \text{ and } \text{, with } v = \mathsf{loc}\,\ell' \qquad \sigma'(\ell') = w}{\rho, \sigma \vdash e.m(e_1, \ldots, e_k) \Rightarrow w, \sigma'}\;\textsf{(MethodCallRef)}`

*Parametric polymorphism*

$$`\dfrac{\begin{array}{c} p \text{ has } \mathtt{template{<}typename\ T{>}\ class}\ C\qquad C{<}\tau{>} \text{ mentioned in } p \\ C{<}\tau{>} \notin \text{class table of } p \end{array}}{p \longrightarrow p, \mathtt{class}\ C{<}\tau{>}\ \{ \ldots [T := \tau] \ldots \}}\;\textsf{(Inst)}`

*Subtyping and inference*

$$`\dfrac{\Gamma \vdash e : \tau \qquad \mathsf{HasValues}(\tau) \qquad \mathsf{Storable}(\tau)}{\Gamma \vdash \mathtt{auto}\ x = e \dashv \Gamma[x \mapsto \tau]}\;\textsf{(T-Auto)}`
