import Verso
import VersoManual
import VersoBlueprint
import CoreCpp.Syntax
import CoreCpp.Fragment
import CoreCpp.Logic

open Verso.Genre
open Verso.Genre.Manual
open Informal

set_option verso.blueprint.foldCodeBlocks true

#doc (Manual) "Paradigms and fragments" =>

This chapter adds no construction to Core C++. Three of the four paradigms are read as restrictions of the core, each a predicate over the abstract syntax, and the restriction buys a property the whole language does not have. The logic paradigm has no counterpart in the core, so it gets a language of its own, a set of Horn clauses whose meaning is given by the SLD resolution judgment, written in the same notation as the rest of this blueprint.

:::group "ud7"
The paradigms as fragments of the core, and a logic language.
:::

# Fragments

:::definition "frag_pred" (parent := "ud7") (lean := "CoreCpp.Frag, CoreCpp.Reject, CoreCpp.fragment, CoreCpp.Frag.ofString?") (uses := "gram_ast")
A fragment is a set of forbidden constructions, and a program lies in the fragment when no declaration mentions one of them. The check is one walk over the tree, and the rejection names the construction and the declaration in which it occurs.

$$`\dfrac{\text{no declaration of } p \text{ mentions a construction } f \text{ forbids}}{p \in f}\;\textsf{(Frag)}`

A fragment is not a grammar. The parser and the type checker are the ones of the whole language, and the predicate runs after them, so a program outside a fragment is still a Core C++ program with the meaning the earlier units gave it.
:::

:::definition "frag_imperative" (parent := "ud7") (lean := "CoreCpp.Fragment.forbids, CoreCpp.Fragment.declBad, CoreCpp.Fragment.funBad") (uses := "frag_pred, cmd_assign, fun_decl")
The imperative fragment keeps the basic types, the variables, the assignment, the commands and the first order functions, and forbids classes, `new`, `delete`, pointers, vectors, lambdas and function values.
:::

:::theorem "frag_imperative_store" (parent := "ud7") (uses := "frag_imperative, dom_store, cmd_block")
In a program of the imperative fragment every value in σ is basic, `int` or `bool`, the store grows only by declaration and by parameter binding, and it shrinks only at the exit of the block or of the call that grew it. Locations therefore live in a stack discipline, and no location outlives the declaration that created it, so `danglingLocation` is unreachable. Verified by inspection of the rules the fragment admits, not by a Lean proof.
:::

:::definition "frag_oo" (parent := "ud7") (lean := "CoreCpp.Fragment.classBad, CoreCpp.Fragment.paramBad") (uses := "frag_pred, cls_decl, cls_dispatch, cls_delete")
The object oriented fragment is the imperative one with classes, methods, constructors, destructors, inheritance, dispatch, `new`, `delete`, pointers and vectors, and it forbids lambdas and function values.
:::

:::theorem "frag_oo_state" (parent := "ud7") (uses := "frag_oo, cls_new, cls_this")
In a program of the object oriented fragment the store no longer follows a stack discipline, because `new` allocates locations that outlive the block, and every such location is reached either through a pointer held in a variable or a field, or through `this` inside a method. The three `error` results of `delete` are therefore the only way a program of the fragment reaches a location that is gone.
:::

:::definition "frag_functional" (parent := "ud7") (lean := "CoreCpp.Fragment.exprBad, CoreCpp.Fragment.cmdBad, CoreCpp.Fragment.tyBad") (uses := "frag_pred, lambda, fun_callfn")
The functional fragment keeps the expressions, the lambdas, the function values and the calls, and forbids the assignment, the loops, the expression statement, the local reference, the reference parameter and everything that reaches an object. Recursion takes the place of iteration.
:::

:::theorem "frag_functional_write_once" (parent := "ud7") (uses := "frag_functional, cmd_decl, fun_call")
In a program of the functional fragment the store is written once. A location receives its value at the declaration or at the parameter binding that created it and is never written again, because the fragment has no assignment and no `delete`. Two consequences follow. Evaluating one expression twice under the same ρ and σ gives the same value, which is referential transparency, and the order in which the operands of $`e_1 \oplus e_2` are evaluated does not change the result, so the left to right choice of the rule {bpref "eval_order"}[] becomes invisible. Verified by inspection of the rules the fragment admits.
:::

# A logic language

:::definition "logic_syntax" (parent := "ud7") (lean := "CoreCpp.Logic.Term, CoreCpp.Logic.Atom, CoreCpp.Logic.Clause, CoreCpp.Logic.LProgram, CoreCpp.Logic.parse")
A term is a variable, an integer or a functor applied to terms, and a constant is a functor of no arguments. An atom is a predicate symbol applied to terms. A clause is a head and a body of atoms, and a fact is a clause with an empty body. A program is a list of clauses, in the order they are written, and a query is a list of atoms.

$$`\begin{array}{lcl} t & ::= & X \mid n \mid f(t_1, \ldots, t_k) \\ A & ::= & p(t_1, \ldots, t_k) \\ C & ::= & A \mid A \mathbin{\texttt{:-}} A_1, \ldots, A_m \\ P & ::= & C_1 \ldots C_n \\ G & ::= & A_1, \ldots, A_k \end{array}`

A list is the functor `.` over the constant `[]`, and the parser reads and the printer writes the bracket notation of Prolog.
:::

:::definition "logic_subst" (parent := "ud7") (lean := "CoreCpp.Logic.Subst, CoreCpp.Logic.resolve, CoreCpp.Logic.occurs, CoreCpp.Logic.renameClause") (uses := "logic_syntax")
A substitution is a finite map from variables to terms, kept triangular, so the value of a term follows the chain of each variable to its end. A clause is renamed apart before it is used, so one use shares no variable with another.
:::

:::definition "logic_unify" (parent := "ud7") (lean := "CoreCpp.Logic.unify, CoreCpp.Logic.unifyAtom") (uses := "logic_subst")
Unification is Robinson's algorithm with the occurs check, which keeps the substitution acyclic. It is the one operation that makes a logic program run in more than one direction, because it binds the variables of the query and of the clause at once.

$$`\dfrac{x \notin \mathrm{dom}\ \theta \qquad x \text{ does not occur in } t}{\theta \vdash x \doteq t \Rightarrow \theta[x \mapsto t]}\;\textsf{(U-Var)}`

$$`\dfrac{}{\theta \vdash n \doteq n \Rightarrow \theta}\;\textsf{(U-Num)} \qquad \dfrac{\theta_0 = \theta \qquad \theta_{i-1} \vdash s_i \doteq t_i \Rightarrow \theta_i}{\theta \vdash f(s_1 \ldots s_k) \doteq f(t_1 \ldots t_k) \Rightarrow \theta_k}\;\textsf{(U-Fn)}`

Nothing else unifies. Two functors of different names or of different arities fail, and so do a number and a compound term.
:::

:::definition "logic_sld" (parent := "ud7") (lean := "CoreCpp.Logic.solve, CoreCpp.Logic.resolveAtom, CoreCpp.Logic.query") (uses := "logic_unify")
The meaning of a query is given by the SLD resolution judgment, read as, under the program P and the substitution θ, the goal list G succeeds with the answer θ'. The selected atom is the leftmost one, and the clauses are tried in the order they are written, which is the depth first search with backtracking.

$$`\dfrac{}{P, \theta \vdash \varepsilon \Rightarrow \theta}\;\textsf{(SLD-Empty)}`

$$`\dfrac{\begin{array}{c} (H \mathbin{\texttt{:-}} B_1 \ldots B_m) \text{ a fresh variant of a clause of } P \\ \theta \vdash A \doteq H \Rightarrow \theta_1 \qquad P, \theta_1 \vdash B_1 \ldots B_m\, G \Rightarrow \theta' \end{array}}{P, \theta \vdash A\, G \Rightarrow \theta'}\;\textsf{(SLD-Resolve)}`

A derivation of the judgment is a proof of the query from the clauses, read as implications, which is what makes the answer an answer and not just a computation. A goal list with no derivation within the depth bound yields no answer, and that is how the implementation answers a left recursive program instead of diverging.
:::

:::definition "logic_builtin" (parent := "ud7") (lean := "CoreCpp.Logic.evalArith, CoreCpp.Logic.compareOp") (uses := "logic_sld")
Three built in predicates escape the clauses. The arithmetic of `is` evaluates its right side and unifies the result with its left side, the comparisons evaluate both sides, and `=` is unification itself.

$$`\dfrac{\mathrm{eval}(\theta, t) = n \qquad \theta \vdash s \doteq n \Rightarrow \theta_1 \qquad P, \theta_1 \vdash G \Rightarrow \theta'}{P, \theta \vdash (s \mathbin{\texttt{is}} t)\, G \Rightarrow \theta'}\;\textsf{(SLD-Is)}`

$$`\dfrac{\mathrm{eval}(\theta, s) = m \qquad \mathrm{eval}(\theta, t) = n \qquad m \bowtie n \qquad P, \theta \vdash G \Rightarrow \theta'}{P, \theta \vdash (s \bowtie t)\, G \Rightarrow \theta'}\;\textsf{(SLD-Compare)}`

A term with an unbound variable has no arithmetic value, and the goal that asked for one fails. Negation, the cut, assert and retract stay outside the language.
:::
