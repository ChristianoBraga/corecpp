import Verso
import VersoManual
import VersoBlueprint
import CoreCpp.Syntax
import CoreCpp.Typing
import CoreCpp.Eval
import CoreCpp.Templates
import CoreCpp.Grammar

open Verso.Genre
open Verso.Genre.Manual
open Informal

set_option verso.blueprint.foldCodeBlocks true

#doc (Manual) "Design restrictions" =>

The objective of Core C++ is a well behaved C++. Informally, a language is well behaved when its specification leaves no case underspecified. The subset keeps one representative construct per category, the expressions, commands, abstraction, encapsulation, type systems and library of the earlier chapters.

Each syntactic class, such as the expressions or the commands, has its own judgement. The rules of a judgement state the cases they cover, and every other case of its class is `error`. The specification achieves this pattern without error rules, {bpref "design_pattern"}[].

Core C++ is a subset of C++17, and every Core C++ program compiles with `g++ -std=c++17`. Each restriction of the subset removes a construct, or a freedom that C++17 leaves to the compiler. For each restriction, this chapter states what C++17 allows, what Core C++ admits and the property of the semantics the restriction gives.

Core C++ takes C++17 rather than C++20 for the maturity of its compiler support. Both are ISO standards, ISO/IEC 14882:2017 and ISO/IEC 14882:2020. Clang 5 and later implement every feature of C++17, and Clang supports some of the features of C++20, [clang.llvm.org](https://clang.llvm.org/cxx_status.html). GCC supports both revisions almost fully. Its support of C++20 was experimental, with an unstable ABI, until GCC 16, and its C++20 modules remain experimental, [gcc.gnu.org](https://gcc.gnu.org/projects/cxx-status.html).

The properties are those the earlier chapters state. Every construct has a typing rule and an evaluation rule. A program has at most one result, {bpref "determinism"}[]. A well typed program has a derivation, does not terminate, or reaches a case that the evaluator reports as `error`, {bpref "progress"}[]. Lean proves the first statement. The second has no Lean proof yet, so it is a property checked by inspection of the rule set.

The behaviour of C++ in this chapter comes from N4659, the final working draft of C++17, [open-std.org](https://www.open-std.org/jtc1/sc22/wg21/docs/papers/2017/n4659.pdf). It also comes from `g++ -std=c++17`, which on the machine of these tests is Apple clang 21.

:::group "design"
The restrictions of Core C++ with respect to C++17, and the properties they give.
:::

# Behaviour

:::definition "design_pattern" (parent := "design") (lean := "CoreCpp.Error, CoreCpp.Eval.expr, CoreCpp.Eval.lval, CoreCpp.Eval.cmd, CoreCpp.Semantics.Eval, CoreCpp.Semantics.LEval, CoreCpp.Semantics.Exec") (uses := "dom_error, judg_ev_expr, judg_ev_cmd")
Each syntactic class has a relation and a function of the evaluator. The expressions have `Eval` and `expr`, the expressions that denote a location `LEval` and `lval`, and the commands `Exec` and `cmd`. The relation states the cases of its class with a result. The function covers every case of the same class, and its result is that of the relation or an `error`.

The rules exclude each undefined case of C++ by a premise. The rule Div requires a divisor other than zero, and Arith and Div require a result in the range of `int`. The rule Delete requires an object at ℓ, and a virtual destructor when the static class differs from the class of the object. When one of these premises fails, the subject has no derivation. The function of the same class then gives the cause of `error` that names the premise, `divisionByZero`, `overflow`, `doubleDelete` or `deleteWithoutVirtualDtor`.

The function returns into the monad `CoreCpp.M`, the exception transformer `ExceptT Error` over a state monad. The state holds only the trace of the derivation, not the store σ. Every handler of an exception in the evaluator records the trace and throws the exception again. So an `error` of a premise is the result of the conclusion. That monad states the propagation of `error` once, and no rule repeats it. The causes of `error` are the constructors of one type, so every case outside the rules has a name.

Two kinds of cause stay outside the pattern. The causes `undeclaredVariable`, `undeclaredFunction`, `arity`, `typeError` and `notCallable` arise only in a program that skipped the type checker. The cause `outOfFuel` marks a derivation deeper than the fuel, and it is not a result of the semantics. The agreement between each relation and its function has no Lean proof, and issue #6 records the check.
:::

::::definition "design_ub" (parent := "design") (lean := "CoreCpp.Error") (uses := "dom_error, progress, design_pattern")
C++17 defines undefined behaviour as behaviour for which the standard imposes no requirements (N4659 §3.27). An expression whose result is not mathematically defined or not representable in its type has undefined behaviour (N4659 §8 ¶4). So does a zero divisor (N4659 §8.6 ¶4). So does a `delete` through a pointer to a base without a virtual destructor (N4659 §8.3.5 ¶3). The end of the storage duration of an object makes every pointer to it invalid. Indirection through an invalid pointer and its deallocation by a second `delete` have undefined behaviour (N4659 §6.7 ¶4).

Core C++ admits none of these cases, since a premise excludes each one, {bpref "design_pattern"}[]. The evaluator reports `error` with the exit code 134, {bpref "dom_error"}[].

The restriction gives every well typed program one of three outcomes, a value, `error`, or no termination. The semantics fixes the outcome, and no compiler chooses it. The examples of the repository show the difference, through `bin/compare`.

:::table +header
*
  * Example
  * `g++`
  * Core C++
*
  * `overflow.cpp`
  * 0
  * 134
*
  * `division_by_zero.cpp`
  * 0
  * 134
*
  * `out_of_bounds.cpp`
  * 0
  * 134
*
  * `null_dereference.cpp`
  * 139
  * 134
*
  * `double_delete.cpp`
  * 133
  * 134
*
  * `delete_nonvirtual.cpp`
  * 1
  * 134
:::

A non terminating program has no derivation either. This is a limitation of the inductive big step style, not a restriction of the subset (Kahn, RR-0601, §4.4, p. 11).
::::

:::definition "design_order" (parent := "design") (uses := "eval_order, determinism")
In C++17 the evaluations of the operands of an operator are unsequenced, except where the standard notes otherwise (N4659 §4.6 ¶17). The initialisations of the parameters of a call are indeterminately sequenced with respect to each other (N4659 §8.2.2 ¶5). A side effect on a memory location has undefined behaviour when it is unsequenced relative to another access to that location (N4659 §4.6 ¶17).

Core C++ evaluates left to right wherever C++17 leaves the order open, {bpref "eval_order"}[]. It keeps the orders C++17 fixes, such as the right operand before the left one in an assignment (N4659 §8.18 ¶1).

The restriction makes the order of the premises of each rule part of the rule. The store of one premise is the input of the next, so the effects of a construct happen in one order. With the mutually exclusive premises of the rules, a construct has one result, {bpref "determinism"}[].
:::

# Types and declarations

:::definition "design_types" (parent := "design") (lean := "CoreCpp.Typing.compat") (uses := "dom_int32, dom_types, cmd_decl, fun_call, overload_pick")
C++17 has five standard signed integer types, and `int` has the natural size of the architecture (N4659 §6.9.1 ¶2). A `bool` converts to an `int` by an integral promotion (N4659 §7.6 ¶6), so `g++` accepts `int x = true;`.

Core C++ has the basic types `int`, `bool` and `void`. An `int` is 32 bit two's complement, and its overflow is `error`, {bpref "dom_int32"}[]. The relation $`\mathsf{Compat}` is the identity on the basic types, so Core C++ rejects `int x = true;`, {bpref "dom_types"}[].

The restriction fixes the meaning of every arithmetic operation independently of the machine. It also removes every conversion between basic types. So the choice of an overload needs no ranking of conversion sequences, {bpref "overload_pick"}[].
:::

:::definition "design_decl" (parent := "design") (uses := "cmd_decl, fun_call, dom_store")
In C++17 an automatic object without an initialiser has an indeterminate value. An evaluation that produces it has undefined behaviour, with some exceptions (N4659 §11.6 ¶12). A program may also declare variables outside every function. The program `int main() { int x; x = 1; return x; }` compiles with `g++`.

Core C++ requires an initialiser in every local declaration, by the grammar, {bpref "cmd_decl"}[]. It has no global variables. The parser rejects the program above and every declaration of a variable outside a function.

The restriction gives every location a value from its allocation, so the store never holds an indeterminate value. The environment of a function body binds only its parameters, {bpref "fun_call"}[], and the store holds no location before `main` runs.
:::

# Syntax

:::definition "design_syntax" (parent := "design") (lean := "CoreCpp.Grammar.isLL1_grammar") (uses := "gram_ll1, cmd_if")
In C++17 the branch of an `if` and the body of a loop may be a single statement without braces. An `else` then belongs to the nearest `if` without an `else` (N4659 §9.4.1 ¶1, footnote 90).

Core C++ requires braces around every branch and every body, so `if (x == 0) x = 1;` is a syntax error, {bpref "cmd_if"}[].

With mandatory braces the grammar of Core C++ is LL(1), a theorem checked in Lean, {bpref "gram_ll1"}[]. The parser is recursive descent, with one function per nonterminal. A brace closes every branch, so no `else` needs a disambiguation rule.
:::

# Objects

:::definition "design_objects" (parent := "design") (uses := "cls_new, cls_delete, cmd_block, dom_store")
In C++17 an object may live in a variable, and a class without a declared copy constructor gets one implicitly (N4659 §15.8.1 ¶6). The destructor of an automatic object runs implicitly when its block exits (N4659 §15.4 ¶12). So `g++` accepts `C c = *p;`, which copies the object.

Core C++ creates every object with `new` and reaches it by pointer or by reference. It never copies an object, and it rejects `C c = *p;` with the message that objects live behind pointers. A destructor runs only on `delete`, {bpref "cls_delete"}[]. There are no copy constructors, no RAII and no initialiser lists.

The restriction leaves no copy and no destruction at block exit. Every constructor runs on a `new`, and every destructor runs on a `delete` of the program. The rules New of {bpref "cls_new"}[] and Delete of {bpref "cls_delete"}[] show it in the derivation. An object is one record in the store, so two names of an object hold the same location. The exit of a block frees only the locations its declarations allocated, {bpref "cmd_block"}[].
:::

:::definition "design_lambdas" (parent := "design") (uses := "lambda, fun_accept, std_function")
In C++17 a lambda may capture by reference. The call of its closure after the end of the lifetime of a captured entity is likely to have undefined behaviour (N4659 §8.1.5.2 ¶16). Each lambda also has a unique, unnamed closure type (N4659 §8.1.5.1 ¶1), which `auto` may hold.

Core C++ admits only the capture `[=]`, and the closure holds copies of the captured values, {bpref "lambda"}[]. A captured `int` or `bool` is a copy that the body reads and never writes. A lambda occurs only as the argument of `new std::function<F>(λ)`, {bpref "std_function"}[]. The parser rejects `[&]` and `auto f = [=]() -> int { return 1; };`, and `g++` accepts both.

The restriction keeps the locations of the enclosing block out of every closure, so a closure never reads a freed variable. A captured pointer still reaches its object in the store, and its dereference after a `delete` is `error`. The type of every lambda is the function type $`F` of its `std::function`, so the type checker needs no closure types, {bpref "fun_accept"}[].
:::

:::definition "design_classes" (parent := "design") (uses := "cls_decl, cls_new, cls_dispatch")
C++17 admits several base classes for one class, which `g++` accepts in `class C : public A, public B`.

Core C++ admits one public base class, and the parser rejects a second one, {bpref "cls_decl"}[]. Methods are defined inside the class.

The restriction makes the bases of a class one chain, a list from the class to its root. The order of the fields, the constructors from the root down and the destructors from the class of the object up all follow that list, {bpref "cls_new"}[]. A method call selects the method nearest the class in the list, so no member name is ambiguous between two bases, {bpref "cls_dispatch"}[].
:::

# Polymorphism

:::definition "design_poly" (parent := "design") (lean := "CoreCpp.Templates.instantiate, CoreCpp.Typing.pickOverload") (uses := "tmpl_decl, tmpl_inst, overload_pick, inference")
C++17 has function templates, class templates with several parameters, partial specialisation and the ranking of implicit conversion sequences in overload resolution (N4659 §16.3.3.2). The call `g(true)` with the overloads `g(int)` and `g(long)` selects `g(int)` in `g++`, by the promotion of `bool`.

Core C++ admits class templates with one type parameter, instantiated in type position, {bpref "tmpl_decl"}[]. Overloading selects by argument type without a ranking, {bpref "overload_pick"}[]. The keyword `auto` declares local variables only, {bpref "inference"}[].

The restriction expands every template before the type check, {bpref "tmpl_inst"}[], so the type checker and the evaluator see only classes. The choice of an overload has three outcomes, the one candidate that accepts the arguments, an exact candidate among several, or an error.
:::

# Constructs left out

:::definition "design_out" (parent := "design") (uses := "dom_ctrl, pp_language, std_vector")
Core C++ leaves out exceptions, function templates, partial specialisation, objects by value, copy constructors, RAII, multiple inheritance, arrays and separate compilation.

Arrays violate the type completeness principle of Watt, "No operation should be arbitrarily restricted in the types of its operands" (2004, §2.5.3, p. 43). Watt counts assignment, argument passing and function results among the operations a language should not restrict. Arrays of C are not first class values in his account (§11.3, p. 270), and arrays of C++17 carry the same restrictions. An array is not assignable. A parameter of array type is adjusted to a pointer (N4659 §11.3.5 ¶5), and no function returns an array (N4659 §11.3.5 ¶10). An array converts to a pointer to its first element (N4659 §7.2). The subscript `a[i]` is `*(a + i)` (N4659 §8.2.1 ¶1), and an index outside the array is undefined (N4659 §8.7 ¶4). The library type `std::vector` takes the place of arrays, {bpref "std_vector"}[]. A program creates a vector with `new`, as any object, and an index outside the vector has no derivation.

Without exceptions, the control result of a command is `normal` or `ret v`, {bpref "dom_ctrl"}[]. No program catches `error`. Without separate compilation, a program is one translation unit that the type checker sees whole. The preprocessor of Core C++ is a language of its own that runs before the compiler, {bpref "pp_language"}[].
:::
