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

#doc (Manual) "UD VI, type systems" =>

Overloading of functions and methods by the type of the arguments, operator members, class templates instantiated by substitution, subtyping and type inference. A name denotes an overload set, and a call selects one candidate. An infix operator on an object, and the indexing of an object, are the calls of the members `operator⊕` and `operator[]`, and a member may return $`\tau\&`, which is what makes `v[i] = x` work. A template is expanded before the program is checked, so instantiation costs nothing at run time and a template is never checked, only its instantiations are.

:::group "ud6"
UD VI, overloading, polymorphism, subtyping and inference.
:::

# Overloading

:::definition "overload_set" (parent := "ud6") (lean := "CoreCpp.sigOf, CoreCpp.Program.funsNamed, CoreCpp.Program.findMethods, CoreCpp.Typing.distinguishable") (uses := "fun_decl, cls_decl")
A name denotes an overload set, the functions of the program with that name, or the methods of that name along the chain of a class, one per signature. A method of a derived class replaces the one of a base with the same signature, and a different signature is another overload, so the subset has no name hiding. Two declarations of one name live together only when they differ.

$$`\dfrac{\text{arities differ, or } \exists i.\ p_i \neq q_i \text{ and neither } p_i \text{ nor } q_i \text{ is } \mathtt{std::function}}{\text{the two declarations are overloads}}\;\textsf{(Distinguishable)}`

The restriction on `std::function` is the check 5 of the design. It keeps a lambda argument from deciding a call, which would ask for the type of the lambda before the candidate that gives it is known.
:::

:::definition "overload_pick" (parent := "ud6") (lean := "CoreCpp.Typing.pickOverload, CoreCpp.Typing.resolveFun, CoreCpp.Typing.resolveMethod") (uses := "overload_set, fun_call, cls_method")
A call collects the candidates of its arity that accept the arguments, each argument by value acceptable at the type of its parameter and each argument of a reference parameter denoting a location of that type. The choice is the exact candidate when several accept.

$$`\dfrac{\begin{array}{c} A = \text{the candidates of } \mathrm{cand}(f, k) \text{ that accept } e_1, \ldots, e_k \\ A \text{ has one element whose parameters are exactly the types of the arguments, or } A \text{ is a singleton} \end{array}}{\text{the call of } f \text{ selects that candidate}}\;\textsf{(T-Overload)}`

With $`A` empty the error is the one of the single candidate of that arity, when there is one, and no overload otherwise. With two or more in $`A` and no exact one the call is ambiguous. Core C++ does not rank conversion sequences as C++ does, so the rule fits in one line on the board and the error is predictable.
:::

:::definition "overload_sig" (parent := "ud6") (lean := "CoreCpp.FunEnv.lookupSig, CoreCpp.Eval.resolve, CoreCpp.Typing.annotate") (uses := "overload_pick, judg_ev_expr")
Overloading adds no evaluation rule. The type checker writes the signature of the chosen candidate into the tree, the field `sig` of a call, and the evaluator looks a function or a method up by name and signature instead of by name alone. A program that was not annotated, which the checker rejects first, runs with the first candidate of the name.
:::

# Operator members

:::definition "op_member" (parent := "ud6") (lean := "CoreCpp.operatorName, CoreCpp.Typing.methodCall") (uses := "overload_pick, cls_method")
An infix operator whose left operand is an object, and the indexing of an object, are the calls of members. The left operand decides, so no operator on `int` or `bool` changes meaning, and `&&` and `||` are not overloaded.

$$`\dfrac{\Gamma \vdash e_1 : C \qquad C \text{ has } \mathtt{operator}\oplus \text{ visible from } \Gamma \qquad \Gamma \vdash e_1.\mathtt{operator}\oplus(e_2) : \tau}{\Gamma \vdash e_1 \oplus e_2 : \tau}\;\textsf{(T-OpBin)}`

$$`\dfrac{\Gamma \vdash e : C \qquad C \text{ has } \mathtt{operator[]} \text{ visible from } \Gamma \qquad \Gamma \vdash e.\mathtt{operator[]}(i) : \tau}{\Gamma \vdash e[i] : \tau}\;\textsf{(T-OpIndex)}`

The type checker rewrites both forms into the call of the member, and from there they are ordinary method calls, with the visibility, the overload resolution and the dispatch of UD V. The trace shows the rule `MethodCall` under the infix form, which is the point.
:::

:::definition "op_refret" (parent := "ud6") (lean := "CoreCpp.Method, CoreCpp.Typing.refReturns, CoreCpp.Typing.refRets, CoreCpp.Eval.callMethod") (uses := "op_member, judg_ev_lval")
A member may return $`\tau\&`. Every `return` of its body is then over an expression that denotes a location, checked by a walk that does not enter the body of a lambda, because the `return` of a lambda is the lambda's.

$$`\dfrac{\tau \text{ has values} \qquad \text{every return of } c \text{ is return } e \text{ with } \Gamma \vdash_{\ell} e : \tau}{\vdash \tau\&\ m(\ldots)\ \{c\} \text{ in } C}\;\textsf{(T-RetRef)}`

$$`\dfrac{\Gamma \vdash e : C \qquad C \text{ has } \tau\&\ \mathtt{operator[]} \text{ visible from } \Gamma}{\Gamma \vdash_{\ell} e[i] : \tau}\;\textsf{(T-LocOpIndex)}`

The annotation rewrites the `return e` of such a member as `return &e`, the location as a value, an expression no program writes.

$$`\dfrac{\rho, \sigma \vdash e \Rightarrow_{\ell} \ell, \sigma'}{\rho, \sigma \vdash \&e \Rightarrow \mathsf{loc}\ \ell, \sigma'}\;\textsf{(LocOf)}`

$$`\dfrac{\text{the member } m \text{ of } C \text{ returns } \tau\& \qquad \text{member } \ell\ (e_1, \ldots, e_k) \Rightarrow \mathsf{loc}\ \ell', \sigma'}{\rho, \sigma \vdash e.m(e_1, \ldots, e_k) \Rightarrow_{\ell} \ell', \sigma'}\;\textsf{(MethodLoc)}`

In value position the same call reads $`\sigma'(\ell')`. A location a member returns is that of a field or of an element of a vector of the receiver, and it survives the call because the object lives in $`\sigma`. A member that returned the location of a parameter by value would return a freed location, and reading it is `error`, by the general rule of locations outside $`\sigma`.
:::

# Parametric polymorphism

:::definition "tmpl_decl" (parent := "ud6") (lean := "CoreCpp.Decl, CoreCpp.Program.templates, CoreCpp.classType") (uses := "cls_decl, gram_full")
A class template is a class with a type parameter, `template<typename T> class C`, and it is instantiated only in type position, `C<int>`. The name of an instantiation is the chain the design prints for the type, so the name in the source and the name of the expanded class agree, and the parser builds it when it reads a type. One type parameter, by the grammar, which is the check 3 of the design.
:::

:::definition "tmpl_inst" (parent := "ud6") (lean := "CoreCpp.Templates.instantiate, CoreCpp.Templates.substClass, CoreCpp.Templates.substTy, CoreCpp.Templates.substName") (uses := "tmpl_decl")
Instantiation is substitution, and it precedes every other judgment.

$$`\dfrac{p \text{ has } \mathtt{template{<}typename\ T{>}\ class}\ C \qquad C{<}\tau{>} \text{ mentioned in } p \qquad C{<}\tau{>} \notin \text{class table of } p}{p \longrightarrow p, \mathtt{class}\ C{<}\tau{>}\ \{ \ldots [T := \tau] \ldots \}}\;\textsf{(Inst)}`

The substitution replaces the type `T` in every field, parameter, result, local declaration, vector element and class name the body mentions, and it rewrites the name of a mentioned class in its own chain, so `No<T>*` inside `Lista<T>` becomes `No<int>*` in `Lista<int>`. The rule applies to a fixed point, because the class it adds may mention another instantiation, and it is idempotent, so `check` and `runWith` may both apply it. A template is never checked, only its instantiations are, as in C++, and two instantiations of one template are two independent classes with no subtype relation between them.
:::

# Subtyping and inference

:::theorem "subtyping" (parent := "ud6") (uses := "cls_subsumption, tmpl_inst")
Subsumption is the typing rule of subtyping, and it is the only conversion between class types.

$$`\dfrac{\Gamma \vdash e : D* \qquad D \text{ derives from } B}{\Gamma \vdash e : B*}\;\textsf{(T-Sub)}`

It holds in declarations, assignments, arguments, results, comparisons and in the branches of `?:`. Subtype polymorphism and parametric polymorphism do not compose in the subset. Two instantiations of one template have no subtype relation, so `Pilha<D*>` is not a subtype of `Pilha<B*>`, and the reason is that a `Pilha<B*>` accepts an `empilha` of any `B*`, which a `Pilha<D*>` does not. The course states the reason and leaves variance out.
:::

:::definition "inference" (parent := "ud6") (lean := "CoreCpp.Cmd") (uses := "cmd_decl")
Type inference in Core C++ is local. The rule of `auto` is the one of the earlier units, and it already reaches pointers and instantiations, because a pointer has values and an instantiation is a class.

$$`\dfrac{\Gamma \vdash e : \tau \qquad \tau \text{ has values} \qquad \tau \neq \mathtt{nullptr\_t}}{\Gamma \vdash \mathtt{auto}\ x = e \dashv \Gamma[x \mapsto \tau]}\;\textsf{(T-Auto)}`

A lambda has no type of its own, so it never initialises an `auto`, which the grammar already guarantees. Inference over a whole program, as Hindley and Milner give it for Haskell, has no rule here, and the course shows it as a contrast.
:::
