import Verso
import VersoManual
import VersoBlueprint
import CoreCpp.Token
import CoreCpp.Lexer
import CoreCpp.Syntax
import CoreCpp.Parser
import LL1
import CoreCpp.Grammar
import Preproc

open Verso.Genre
open Verso.Genre.Manual
open Informal

set_option verso.blueprint.foldCodeBlocks true

#doc (Manual) "Lexer and grammar" =>

Core C++ has an LL(1) grammar over tokens. Three lexical and syntactic conventions remove the ambiguities of C++.

Type identifiers start with an uppercase letter and variable identifiers with a lowercase letter or `_`. The lexer classifies an identifier by its initial, and the parser uses the class to tell whether `<` opens a template argument or compares. Template instantiation occurs only in type position. A class defines its methods inside its body.

The lexer is a hand written finite automaton with the longest match rule, and the parser is recursive descent.

:::group "ud1"
Syntax, tokens and the parser.
:::

# Lexer

:::definition "lex_tokens" (parent := "ud1") (lean := "CoreCpp.Token, CoreCpp.keywords, CoreCpp.cppReserved, CoreCpp.symbols3, CoreCpp.symbols2, CoreCpp.symbols1, CoreCpp.Lexer.isIdentStart, CoreCpp.Lexer.isIdentChar")
Tokens fall in six classes, and the end token `eof` closes the array.

 * Reserved words, the 24 words `int`, `bool`, `void`, `if`, `else`, `while`, `for`, `return`, `true`, `false`, `auto`, `delete`, `new`, `nullptr`, `this`, `class`, `public`, `private`, `virtual`, `override`, `namespace`, `template`, `typename` and `operator`.
 * Type identifiers, `TypeId`, with an uppercase initial.
 * Variable identifiers, `VarId`, with a lowercase initial or `_`, naming variables, fields, functions and methods.
 * Namespace identifiers, `NsId`, the identifiers of either case that `::` follows.
 * Decimal integer literals, `IntLit`.
 * Operators and punctuation, with `[=]` as a single token by the longest match rule.

There is no token `>>`, so `Stack<Stack<int>>` closes with two tokens `>`.

$$`\begin{array}{lcl} \textit{Token} & ::= & \textit{Keyword}\ \mid\ \textit{TypeId}\ \mid\ \textit{VarId}\ \mid\ \textit{NsId}\ \mid\ \textit{IntLit}\ \mid\ \textit{Symbol} \\ \textit{Keyword} & ::= & \texttt{int}\ \mid\ \texttt{bool}\ \mid\ \texttt{void}\ \mid\ \texttt{class} \\  & \mid & \texttt{public}\ \mid\ \texttt{private}\ \mid\ \texttt{new}\ \mid\ \texttt{delete} \\  & \mid & \texttt{nullptr}\ \mid\ \texttt{this}\ \mid\ \texttt{virtual} \\  & \mid & \texttt{override}\ \mid\ \texttt{namespace}\ \mid\ \texttt{template} \\  & \mid & \texttt{typename}\ \mid\ \texttt{auto}\ \mid\ \texttt{if}\ \mid\ \texttt{else}\ \mid\ \texttt{while}\ \mid\ \texttt{for}\ \mid\ \texttt{return} \\  & \mid & \texttt{true}\ \mid\ \texttt{false}\ \mid\ \texttt{operator} \\ \textit{TypeId} & ::= & \textit{Upper}\ \textit{IdentChar}^{*} \\ \textit{VarId} & ::= & \big(\ \textit{Lower}\ \mid\ \texttt{\_}\ \big)\ \textit{IdentChar}^{*} \\ \textit{NsId} & ::= & \textit{TypeId}\ \mid\ \textit{VarId} \\ \textit{IntLit} & ::= & \textit{Digit}\ \textit{Digit}^{*} \\ \textit{Symbol} & ::= & \texttt{[=]} \\  & \mid & \texttt{==}\ \mid\ \texttt{!=}\ \mid\ \texttt{<=}\ \mid\ \texttt{>=}\ \mid\ \texttt{\&\&}\ \mid\ \texttt{||}\ \mid\ \texttt{->}\ \mid\ \texttt{::}\ \mid\ \texttt{--}\ \mid\ \texttt{++} \\  & \mid & \texttt{+}\ \mid\ \texttt{-}\ \mid\ \texttt{*}\ \mid\ \texttt{/}\ \mid\ \texttt{\%}\ \mid\ \texttt{<}\ \mid\ \texttt{>}\ \mid\ \texttt{!}\ \mid\ \texttt{?}\ \mid\ \texttt{:}\ \mid\ \texttt{=} \\  & \mid & \texttt{(}\ \mid\ \texttt{)}\ \mid\ \texttt{\{}\ \mid\ \texttt{\}}\ \mid\ \texttt{[}\ \mid\ \texttt{]}\ \mid\ \texttt{,}\ \mid\ \texttt{;}\ \mid\ \texttt{.}\ \mid\ \texttt{\&}\ \mid\ \texttt{\textasciitilde} \\ \textit{IdentChar} & ::= & \textit{Upper}\ \mid\ \textit{Lower}\ \mid\ \textit{Digit}\ \mid\ \texttt{\_} \\ \textit{Upper} & ::= & \texttt{A}\ \mid\ \ldots\ \mid\ \texttt{Z} \\ \textit{Lower} & ::= & \texttt{a}\ \mid\ \ldots\ \mid\ \texttt{z} \\ \textit{Digit} & ::= & \texttt{0}\ \mid\ \ldots\ \mid\ \texttt{9} \\ \textit{Skip} & ::= & \textit{WhiteSpace}\ \mid\ \texttt{//}\ \textit{NotNewline}^{*}\ \textit{Newline}^{?} \end{array}`

The lexer covers the input by a sequence of `Token` and `Skip`, discards `Skip`, and takes the longest match at each position. A line comment ends at a newline or at the end of the input. The automaton tries the symbols of three characters before those of two and of one.
:::

:::definition "lex_conventions" (parent := "ud1") (lean := "CoreCpp.Lexer.identifier, CoreCpp.Lexer.qualifiers") (uses := "lex_tokens")
The function `identifier` first looks an identifier up in the reserved words and then classifies it by its initial. A further pass over the token array, `qualifiers`, marks as an `NsId` every identifier whose next token is `::`, of either case.

The pass runs after the automaton, so it sees neither white space nor comments and marks `std :: vector` as it marks `std::vector`. The function `parseUnit` of {bpref "parse_program"}[] runs the automaton on each line of the Preproc output alone and the pass once on the tokens of all the lines, so a `::` that starts a line marks the identifier that ends the line before.

That class is what lets a qualified name open a type where the case convention alone would read a variable, so `std::vector<int>` needs no reserved word.
:::

:::definition "lex_automaton" (parent := "ud1") (lean := "CoreCpp.lex, CoreCpp.Lexer.run, CoreCpp.Lexer.takeWhile, CoreCpp.Lexer.matchSymbol, CoreCpp.Lexer.skipLine") (uses := "lex_tokens, lex_conventions")
The function `lex` maps a string to an array of tokens ended by `eof`. It runs the automaton `Lexer.run` and then the pass of {bpref "lex_conventions"}[]. It discards white space and line comments, reads the longest run of digits as an integer literal, the longest run of identifier characters as an identifier, and tries the symbols of three, two and one characters in that order. Any other character is a lexical error.

The lexer also rejects what C++ would read otherwise, so that every Core C++ program is a C++ program with the same meaning.

 * It rejects a keyword of C++ or an alternative representation such as `and` outside the reserved words of the subset (N4659 §5.11, Tables 5 and 6).
 * It rejects an integer literal of two or more digits with a leading `0`, which C++ reads in octal, and one above 2147483647, to which C++ gives a type wider than `int`.
 * It reads `--` and `++` as tokens that no production uses, so `5--2` fails as in C++, where the longest match gives `--`.

The automaton `Lexer.run` is `partial`, so Lean records an opaque constant that carries the type and not the body, and no property of it is proved here.
:::

# Grammar

:::definition "gram_full" (parent := "ud1") (lean := "CoreCpp.Grammar.Term, CoreCpp.Grammar.rules, CoreCpp.Grammar.grammar")
The grammar of Core C++, in EBNF. The superscript $`X^{*}` repeats $`X` zero or more times, and the superscript $`X^{?}` makes $`X` optional. Large parentheses group, the bar separates alternatives, and terminals are in typewriter font. The grammar has no left recursive production, and it is left factored.

$$`\begin{array}{lcl} \textit{Program} & ::= & \textit{Declaration}^{*} \\ \textit{Declaration} & ::= & \texttt{namespace}\ \textit{Name}\ \texttt{\{}\ \textit{Declaration}^{*}\ \texttt{\}} \\  & \mid & \texttt{template}\ \texttt{<}\ \texttt{typename}\ \textit{TypeId}\ \big(\ \texttt{,}\ \texttt{typename}\ \textit{TypeId}\ \big)^{*}\ \texttt{>} \\  & & \qquad \texttt{class}\ \big(\ \textit{TypeId}\ \textit{ClassRest}\ \mid\ \textit{VarId}\ \texttt{;}\ \big) \\  & \mid & \textit{Class} \\  & \mid & \textit{Function} \\ \textit{Name} & ::= & \textit{TypeId}\ \mid\ \textit{VarId} \\ \textit{Class} & ::= & \texttt{class}\ \textit{TypeId}\ \textit{ClassRest} \\ \textit{ClassRest} & ::= & \big(\ \texttt{:}\ \texttt{public}\ \textit{ClassType}\ \big)^{?}\ \texttt{\{}\ \textit{Member}^{*}\ \textit{Section}^{*}\ \texttt{\}}\ \texttt{;} \\ \textit{Section} & ::= & \big(\ \texttt{public}\ \mid\ \texttt{private}\ \big)\ \texttt{:}\ \textit{Member}^{*} \\ \textit{Member} & ::= & \texttt{virtual}\ \big(\ \textit{Type}\ \texttt{\&}^{?}\ \textit{MemberRest}\ \mid\ \texttt{\textasciitilde}\ \textit{TypeId}\ \texttt{(}\ \texttt{)}\ \textit{Block}\ \big) \\  & \mid & \texttt{\textasciitilde}\ \textit{TypeId}\ \texttt{(}\ \texttt{)}\ \textit{Block} \\  & \mid & \big(\ \textit{BasicType}\ \mid\ \textit{NsId}\ \texttt{::}\ \textit{QualTail}\ \texttt{*}^{?}\ \big)\ \texttt{\&}^{?}\ \textit{MemberRest} \\  & \mid & \textit{TypeId}\ \big(\ \textit{Params}\ \textit{Block} \\  & & \qquad \mid\ \textit{TemplateArgs}^{?}\ \texttt{*}^{?}\ \texttt{\&}^{?}\ \textit{MemberRest}\ \big) \\ \textit{MemberRest} & ::= & \textit{VarId}\ \big(\ \texttt{;}\ \mid\ \textit{Params}\ \texttt{override}^{?}\ \textit{Block}\ \big) \\  & \mid & \texttt{operator}\ \textit{Op}\ \textit{Params}\ \textit{Block} \\ \textit{Op} & ::= & \texttt{+}\ \mid\ \texttt{-}\ \mid\ \texttt{*}\ \mid\ \texttt{/}\ \mid\ \texttt{\%}\ \mid\ \texttt{==}\ \mid\ \texttt{!=}\ \mid\ \texttt{<}\ \mid\ \texttt{<=}\ \mid\ \texttt{>}\ \mid\ \texttt{>=}\ \mid\ \texttt{[}\ \texttt{]} \\ \textit{Function} & ::= & \textit{Type}\ \textit{VarId}\ \textit{Params}\ \big(\ \textit{Block}\ \mid\ \texttt{;}\ \big) \\  \textit{Params} & ::= & \texttt{(}\ \big(\ \textit{Param}\ \big(\ \texttt{,}\ \textit{Param}\ \big)^{*}\ \big)^{?}\ \texttt{)} \\ \textit{Param} & ::= & \textit{Type}\ \texttt{\&}^{?}\ \textit{VarId} \\ \textit{Type} & ::= & \textit{BasicType}\ \mid\ \textit{ClassType}\ \texttt{*}^{?} \\ \textit{TemplateArg} & ::= & \textit{Type}\ \big(\ \texttt{(}\ \big(\ \textit{Type}\ \big(\ \texttt{,}\ \textit{Type}\ \big)^{*}\ \big)^{?}\ \texttt{)}\ \big)^{?} \\ \textit{BasicType} & ::= & \texttt{int}\ \mid\ \texttt{bool}\ \mid\ \texttt{void} \\ \textit{ClassType} & ::= & \textit{NsId}\ \texttt{::}\ \textit{QualTail}\ \mid\ \textit{TypeId}\ \textit{TemplateArgs}^{?} \\ \textit{QualTail} & ::= & \textit{NsId}\ \texttt{::}\ \textit{QualTail}\ \mid\ \textit{Name}\ \textit{TemplateArgs}^{?} \\ \textit{TemplateArgs} & ::= & \texttt{<}\ \textit{TemplateArg}\ \big(\ \texttt{,}\ \textit{TemplateArg}\ \big)^{*}\ \texttt{>} \\ \textit{Block} & ::= & \texttt{\{}\ \textit{Statement}^{*}\ \texttt{\}} \\ \textit{Statement} & ::= & \textit{Block} \\  & \mid & \texttt{if}\ \texttt{(}\ \textit{Expr}\ \texttt{)}\ \textit{Block}\ \big(\ \texttt{else}\ \textit{Block}\ \big)^{?} \\  & \mid & \texttt{while}\ \texttt{(}\ \textit{Expr}\ \texttt{)}\ \textit{Block} \\  & \mid & \texttt{for}\ \texttt{(}\ \textit{ForInit}\ \texttt{;}\ \textit{Expr}\ \texttt{;}\ \textit{ExprStatement}\ \texttt{)}\ \textit{Block} \\  & \mid & \texttt{return}\ \textit{ArgExpr}^{?}\ \texttt{;} \\  & \mid & \texttt{delete}\ \textit{Expr}\ \texttt{;} \\  & \mid & \textit{LocalDecl}\ \texttt{;} \\  & \mid & \textit{ExprStatement}\ \texttt{;} \\ \textit{LocalDecl} & ::= & \texttt{auto}\ \textit{VarId}\ \texttt{=}\ \textit{Expr} \\  & \mid & \textit{Type}\ \texttt{\&}^{?}\ \textit{VarId}\ \texttt{=}\ \textit{ArgExpr} \\ \textit{ForInit} & ::= & \textit{LocalDecl}\ \mid\ \textit{ExprStatement} \\ \textit{ExprStatement} & ::= & \textit{Expr}\ \big(\ \texttt{=}\ \textit{Expr}\ \big)^{?} \\ \textit{Expr} & ::= & \textit{OrExpr}\ \big(\ \texttt{?}\ \textit{Expr}\ \texttt{:}\ \textit{Expr}\ \big)^{?} \\ \textit{OrExpr} & ::= & \textit{AndExpr}\ \big(\ \texttt{||}\ \textit{AndExpr}\ \big)^{*} \\ \textit{AndExpr} & ::= & \textit{EqExpr}\ \big(\ \texttt{\&\&}\ \textit{EqExpr}\ \big)^{*} \\ \textit{EqExpr} & ::= & \textit{RelExpr}\ \big(\ \big(\ \texttt{==}\ \mid\ \texttt{!=}\ \big)\ \textit{RelExpr}\ \big)^{*} \\ \textit{RelExpr} & ::= & \textit{AddExpr}\ \big(\ \big(\ \texttt{<}\ \mid\ \texttt{<=}\ \mid\ \texttt{>}\ \mid\ \texttt{>=}\ \big)\ \textit{AddExpr}\ \big)^{*} \\ \textit{AddExpr} & ::= & \textit{MulExpr}\ \big(\ \big(\ \texttt{+}\ \mid\ \texttt{-}\ \big)\ \textit{MulExpr}\ \big)^{*} \\ \textit{MulExpr} & ::= & \textit{UnaryExpr}\ \big(\ \big(\ \texttt{*}\ \mid\ \texttt{/}\ \mid\ \texttt{\%}\ \big)\ \textit{UnaryExpr}\ \big)^{*} \\ \textit{UnaryExpr} & ::= & \big(\ \texttt{!}\ \mid\ \texttt{-}\ \mid\ \texttt{*}\ \big)\ \textit{UnaryExpr}\ \mid\ \textit{PostfixExpr} \\ \textit{PostfixExpr} & ::= & \textit{Primary}\ \textit{Chain} \\ \textit{Chain} & ::= & \big(\ \texttt{[}\ \textit{Expr}\ \texttt{]}\ \textit{Chain}\ \mid\ \texttt{.}\ \textit{VarId}\ \textit{After} \\  & & \qquad \mid\ \texttt{->}\ \textit{VarId}\ \textit{After}\ \mid\ \textit{Args}\ \textit{Chain}\ \big)^{?} \\ \textit{After} & ::= & \textit{Args}\ \textit{Chain}\ \mid\ \textit{ChainNoCall} \\ \textit{ChainNoCall} & ::= & \big(\ \texttt{[}\ \textit{Expr}\ \texttt{]}\ \textit{Chain}\ \mid\ \texttt{.}\ \textit{VarId}\ \textit{After} \\  & & \qquad \mid\ \texttt{->}\ \textit{VarId}\ \textit{After}\ \big)^{?} \\  \textit{Primary} & ::= & \textit{IntLit}\ \mid\ \texttt{true}\ \mid\ \texttt{false}\ \mid\ \texttt{nullptr}\ \mid\ \texttt{this}\ \mid\ \textit{VarId} \\  & \mid & \texttt{(}\ \textit{Expr}\ \texttt{)} \\  & \mid & \texttt{new}\ \textit{ClassType}\ \textit{Args} \\ \textit{Args} & ::= & \texttt{(}\ \big(\ \textit{ArgExpr}\ \big(\ \texttt{,}\ \textit{ArgExpr}\ \big)^{*}\ \big)^{?}\ \texttt{)} \\ \textit{ArgExpr} & ::= & \textit{Lambda}\ \mid\ \textit{Expr} \\ \textit{Lambda} & ::= & \texttt{[=]}\ \textit{Params}\ \texttt{->}\ \textit{Type}\ \textit{Block} \end{array}`

A statement is a command or an expression followed by `;`. Assignment is a command, and `ExprStatement` joins the two forms that start with an expression to keep the grammar LL(1).

In the abstract syntax the commands form the type `Cmd`, and the expression statement is the command `exprStmt`, which evaluates and discards the value. The left side of an assignment must denote a location, a check made by the type checker.

A lambda expression is an `ArgExpr` and not a `Primary`, so it occurs only as argument, as initialiser of a declaration with a type and as `return` expression, and the type checker admits it only as the argument of `new std::function<F>(λ)`.

The parser rejects forms that the grammar derives and the subset excludes.

A class template with a body has one type parameter, and an instantiation of a class template of the program has one template argument. A class of the library always takes template arguments, and a base class is a class of the program.

A lambda parameter is by value, and a field is not a reference. A namespace holds only classes, templates and namespaces.

Only a header of Core C++ opens the namespace `std`, declares a function without a body or declares a class template without a body, since C++ leaves a program that adds declarations to `std` undefined (N4659 §20.5.4.2.1, paragraph 1). Preproc marks the lines that come from a header, and the parser reads the marks. The type checker then rejects a class template or a function without a body that no module of the library implements.

The parser also checks the names of the constructor and the destructor against their class. A class has at most one of each, both are public, and a field is never virtual. The public destructor is a restriction of the subset, since C++ accepts a private destructor that no code outside the class calls.
:::

:::theorem "gram_ll1" (parent := "ud1") (lean := "CoreCpp.Grammar.isLL1_grammar, CoreCpp.Grammar.table, CoreCpp.Grammar.derive, CoreCpp.Grammar.parseTree, CoreCpp.Grammar.Term.ofToken, CoreCpp.Grammar.ofEbnf, CoreCpp.Grammar.leanModule, LL1.translate, LL1.Grammar.isLL1, LL1.Grammar.table, LL1.Grammar.parse")
The grammar is LL(1).
:::

:::proof "gram_ll1"
The proof is a computation. The theorem `CoreCpp.Grammar.isLL1_grammar` builds the predictive parsing table of the grammar of {bpref "gram_full"}[] and checks that no entry holds two productions.

The grammar comes from the file `grammar/core-cpp.ebnf`, rule by rule over token classes. The generator `lake exe ebnf2lean` reads the file, maps its terminals to the token classes by `ofEbnf` and writes the rules as the module `CoreCpp/GrammarRules.lean` by `leanModule`, and the theorem is about the rules of that module.

The library `LL1` of the package `ll1-lean` translates them from EBNF to BNF. It then computes the nullable nonterminals, FIRST and FOLLOW as least fixed points, and fills the table.

Three left factorings and one restriction of the language explain the result.

In `Member`, a `TypeId` opens both a constructor and the type of a field or method. The next token decides, `(` for a constructor and any other token for a type.

In `ExprStatement`, an assignment and an expression statement share the prefix `Expr`, and the token `=` decides.

In `Declaration`, a class template with a body and a class template of the library without one share the prefix up to `class`. The case of the name decides, a `TypeId` for the first and a `VarId` for the second.

In `Statement`, the FIRST sets of `LocalDecl` and `ExprStatement` are disjoint. A local declaration starts with `auto`, `int`, `bool`, `void`, a `TypeId` or an `NsId`. An expression starts with a `VarId`, an `IntLit`, `true`, `false`, `nullptr`, `this`, `new`, `(`, `!`, `-` or `*`, and never with a `TypeId` or an `NsId`.

The restriction shapes `Chain`. After a `.` or a `->`, an argument list opens the arguments of a method, so `e.f(a)` and `e->f(a)` are method calls and never the call of a function held in a field. The nonterminal `After` says exactly that, since a field access continues through `ChainNoCall`, which no argument list may follow directly.

Without the restriction the two readings would both derive `e->f(a)` and no lookahead would separate them.

A field holds a pointer to a function object and the call goes through it, as in `(*b->handler)(3)`, and `b->handler(3)` is a type error that names the field.

The same table drives the nonrecursive predictive parser `LL1.Grammar.parse`, which `CoreCpp.Grammar.derive` runs on the tokens of a program without the end token, each mapped to its class by `Term.ofToken`, and whose output is the leftmost derivation. The function `parseTree` builds the derivation tree from that derivation.
:::

# Abstract syntax and parser

:::definition "gram_ast" (parent := "ud1") (lean := "CoreCpp.Ty, CoreCpp.UnOp, CoreCpp.BinOp, CoreCpp.Param, CoreCpp.Expr, CoreCpp.Cmd, CoreCpp.Fun, CoreCpp.Vis, CoreCpp.Field, CoreCpp.Method, CoreCpp.Ctor, CoreCpp.Dtor, CoreCpp.ClassDecl, CoreCpp.Decl, CoreCpp.Program")
The abstract syntax is the tree form of the grammar of {bpref "gram_full"}[], with one inductive type or structure per class of nonterminals. It has no parentheses and no precedence, because the tree fixes the structure. The table below gives the alternatives of every constructor of `Syntax.lean`, in the order of the file, with the constructor in the right column.

The type `Ty` has the basic types `int`, `bool` and `void`, class types, pointer types, the types of the library such as `std::vector<int>`, function types, and $`\mathsf{nullptr\_t}`, the internal type of `nullptr`.

The type `UnOp` has `!` and unary `-`, and the type `BinOp` has the arithmetic, the comparison and the logical operators.

The type `Expr` has literals and variables, operators and the conditional, and three calls, of a named function, of a method and of the `std::function` an expression denotes, as in `(*f)(ē)`. It has the two forms of `new`, `this`, field access through `.` and `->`, dereference and indexing, and the lambda.

The last constructor, `locOf`, is a form no program writes, which the function `Typing.annotate` of the type checker inserts. The form `locOf e` is the location of `e` as a value, on the `return` of a member that returns a reference.

The type `Cmd` has the block, `if`, `while`, `for` and `return`, the declarations with a type, with a reference and with `auto`, the assignment, the expression statement and `delete`.

A `Param` may be by reference. A `Fun` has a return type, a name, parameters and a body. A `Vis` is public or private.

A member is a `Field`, a `Method`, a `Ctor` or a `Dtor`. A method also records whether it is virtual, whether it overrides and whether it returns a reference, and a destructor records whether it is virtual. A `ClassDecl` has a qualified name, an optional base, fields and methods with their visibility, at most one constructor and at most one destructor.

A `Decl` is a class, a function, a class template, or a class template or a function of the library declared without a body. A `Program` is a list of declarations.

$$`\begin{array}{lcll} \textit{Ty} & ::= & \mathtt{int} \mid \mathtt{bool} \mid \mathtt{void} & \textsf{Ty.int, bool, void} \\  & \mid & C \mid \textit{Ty}\mathtt{*} & \textsf{cls, ptr} \\  & \mid & \mathtt{std{:}{:}}L\langle\textit{Ty}_1, \ldots, \textit{Ty}_k\rangle \mid \textit{Ty}(\textit{Ty}_1, \ldots, \textit{Ty}_k) & \textsf{lib, fn} \\  & \mid & \mathsf{nullptr\_t} & \textsf{nullT} \\ \textit{UnOp} & ::= & \mathtt{!} \mid \mathtt{-} & \textsf{UnOp.not, neg} \\ \textit{BinOp} & ::= & \mathtt{+} \mid \mathtt{-} \mid \mathtt{*} \mid \mathtt{/} \mid \mathtt{\%} & \textsf{BinOp.add} \ldots \textsf{mod} \\  & \mid & \mathtt{==} \mid \mathtt{!=} \mid \mathtt{<} \mid \mathtt{<=} \mid \mathtt{>} \mid \mathtt{>=} & \textsf{eq} \ldots \textsf{ge} \\  & \mid & \mathtt{\&\&} \mid \mathtt{||} & \textsf{and, or} \\ \textit{Param} & ::= & \textit{Ty}\ x \mid \textit{Ty}\mathtt{\&}\ x & \textsf{Param} \\ \textit{Expr} & ::= & n \mid b & \textsf{Expr.intLit, boolLit} \\  & \mid & \mathtt{nullptr} \mid x & \textsf{nullptr, var} \\  & \mid & \textit{UnOp}\, \textit{Expr} \mid \textit{Expr}_1 \textit{BinOp} \textit{Expr}_2 & \textsf{unop, binop} \\  & \mid & \textit{Expr}_1\ \mathtt{?}\ \textit{Expr}_2\ \mathtt{:}\ \textit{Expr}_3 & \textsf{cond} \\  & \mid & f(\textit{Expr}_1, \ldots, \textit{Expr}_k) & \textsf{call} \\  & \mid & \mathtt{new}\ C(\textit{Expr}_1, \ldots, \textit{Expr}_k) & \textsf{newObj} \\  & \mid & \mathtt{new}\ \mathtt{std{:}{:}}L\langle\textit{Ty}_1, \ldots, \textit{Ty}_k\rangle & \textsf{newLib} \\  & & \qquad (\textit{Expr}_1, \ldots, \textit{Expr}_n) &  \\  & \mid & \mathtt{this} & \textsf{this} \\  & \mid & \textit{Expr}.m(\textit{Expr}_1, \ldots, \textit{Expr}_k) & \textsf{methodCall} \\  & & \qquad \mid \textit{Expr}\texttt{->}m(\textit{Expr}_1, \ldots, \textit{Expr}_k) &  \\  & \mid & \textit{Expr}.f \mid \textit{Expr}\texttt{->}f & \textsf{field, arrow} \\  & \mid & \mathtt{*}\textit{Expr} \mid \textit{Expr}_1[\textit{Expr}_2] & \textsf{deref, index} \\  & \mid & \mathtt{[=]}(\textit{Param}_1, \ldots, \textit{Param}_k)\ \texttt{->}\ \textit{Ty} & \textsf{lambda} \\  & & \qquad \{\, \textit{Cmd}_1 \ldots \textit{Cmd}_n \,\} &  \\  & \mid & \textit{Expr}(\textit{Expr}_1, \ldots, \textit{Expr}_k) & \textsf{callFn} \\  & \mid & \mathsf{locOf}\ \textit{Expr} & \textsf{locOf} \\ \textit{Cmd} & ::= & \{\, \textit{Cmd}_1 \ldots \textit{Cmd}_n \,\} & \textsf{Cmd.block} \\  & \mid & \mathtt{if}\ (\textit{Expr})\ \{\, \textit{Cmd}_1 \ldots \textit{Cmd}_n \,\} & \textsf{ite} \\  & & \qquad \mathtt{else}\ \{\, \textit{Cmd}'_1 \ldots \textit{Cmd}'_m \,\} &  \\  & \mid & \mathtt{while}\ (\textit{Expr})\ \{\, \textit{Cmd}_1 \ldots \textit{Cmd}_n \,\} & \textsf{while} \\  & \mid & \mathtt{for}\ (\textit{Cmd}_0;\ \textit{Expr};\ \textit{Cmd}_s) & \textsf{for} \\  & & \qquad \{\, \textit{Cmd}_1 \ldots \textit{Cmd}_n \,\} &  \\  & \mid & \mathtt{return} \mid \mathtt{return}\ \textit{Expr} & \textsf{ret} \\  & \mid & \textit{Ty}\ x = \textit{Expr} \mid \textit{Ty}\mathtt{\&}\ x = \textit{Expr} & \textsf{decl, declRef} \\  & \mid & \mathtt{auto}\ x = \textit{Expr} & \textsf{declAuto} \\  & \mid & \textit{Expr}_1 = \textit{Expr}_2 & \textsf{assign} \\  & \mid & \textit{Expr}; & \textsf{exprStmt} \\  & \mid & \mathtt{delete}\ \textit{Expr} & \textsf{delete} \\ \textit{Fun} & ::= & \textit{Ty}\ f(\textit{Param}_1, \ldots, \textit{Param}_k) & \textsf{Fun} \\  & & \qquad \{\, \textit{Cmd}_1 \ldots \textit{Cmd}_n \,\} &  \\ \textit{Vis} & ::= & \mathtt{public} \mid \mathtt{private} & \textsf{Vis.pub, priv} \\ \textit{Member} & ::= & \textit{Ty}\ f; & \textsf{Field} \\  & \mid & \textit{Ty}\ m(\textit{Param}_1, \ldots, \textit{Param}_k) & \textsf{Method} \\  & & \qquad \{\, \textit{Cmd}_1 \ldots \textit{Cmd}_n \,\} &  \\  & \mid & C(\textit{Param}_1, \ldots, \textit{Param}_k)\ \{\, \textit{Cmd}_1 \ldots \textit{Cmd}_n \,\} & \textsf{Ctor} \\  & \mid & \mathtt{\sim}C()\ \{\, \textit{Cmd}_1 \ldots \textit{Cmd}_n \,\} & \textsf{Dtor} \\ \textit{ClassDecl} & ::= & \mathtt{class}\ C\ (\mathtt{:}\ \mathtt{public}\ B)^{?} & \textsf{ClassDecl} \\  & & \qquad \{\, \textit{Member}_1 \ldots \textit{Member}_n \,\} &  \\ \textit{Decl} & ::= & \textit{ClassDecl} \mid \textit{Fun} & \textsf{Decl.cls, fn} \\  & \mid & \mathtt{template}\ \langle\mathtt{typename}\ T\rangle\ \textit{ClassDecl} & \textsf{tmpl} \\  & \mid & \mathtt{template}\ \langle\mathtt{typename}\ T_1, \ldots, \mathtt{typename}\ T_k\rangle & \textsf{libTmpl} \\  & & \qquad \mathtt{class}\ L; &  \\  & \mid & \textit{Ty}\ f(\textit{Param}_1, \ldots, \textit{Param}_k); & \textsf{libFn} \\ \textit{Program} & ::= & \textit{Decl}_1 \ldots \textit{Decl}_n & \textsf{Program} \end{array}`

The symbols on the left are the nonterminals of this grammar, each named after the type of `Syntax.lean` it describes. The nonterminal `Member` stands for the four structures `Field`, `Method`, `Ctor` and `Dtor`.

The rules of the typing and of the evaluation abbreviate them, τ for a `Ty`, e for an `Expr`, c for a `Cmd` and p for a `Param`, and a subscript tells two occurrences apart.

Inside the productions, n stands for an integer literal and b for a boolean one, x for a variable, f for a field or a function and m for a method, all of them written as a `VarId`, and C for a class, B for a base, T for a template parameter and L for a library class, all of them written as a `TypeId`.

The right column names, for each alternative, the constructor of the inductive type of `Syntax.lean` that the alternative builds, `Expr.intLit` for a literal and `Cmd.block` for a block. The type is written out on the first line of a category and only the constructor afterwards.

A constructor here is a case of an inductive definition of Lean, and not the member of a class that `new` runs, which this table calls `Ctor`.

Every field and every method carries a `Vis`, which the parser takes from the section that holds it. The constructor and the destructor are public and carry no visibility.
:::

:::definition "parse_expr" (parent := "ud1") (lean := "CoreCpp.P, CoreCpp.PState, CoreCpp.expr, CoreCpp.orExpr, CoreCpp.andExpr, CoreCpp.eqExpr, CoreCpp.relExpr, CoreCpp.addExpr, CoreCpp.mulExpr, CoreCpp.unaryExpr, CoreCpp.postfixExpr, CoreCpp.primary, CoreCpp.args, CoreCpp.argExpr, CoreCpp.lambda") (uses := "gram_ast, lex_automaton")
A parser has the type `P α`, a state monad over `PState` that gives an `α` or fails with a message. The state holds the tokens, the position of the next one, the prefix of the enclosing namespaces and, for each token, whether it comes from a header.

One parser function per expression nonterminal, from `Expr` down to `Primary`, named after it. Each level of the grammar is one level of precedence, and the repetition of an operator and its operand builds a left associative tree.

The function `postfixExpr` reads `Chain`, `After` and `ChainNoCall` inline. It covers the call of a name, `call`, the call of the `std::function` any other postfix expression denotes, `callFn`, indexing, field access through `.` and `->`, and the method call in its two forms. The nonterminal `After` separates a method call from a field access.

The function `unaryExpr` reads `!`, unary `-` and the dereference `*`, and `primary` covers literals, `nullptr`, `this`, variables, parenthesised expressions and the two forms of `new`, `newObj` for a class of the program and `newLib` for a type of the library. The function `argExpr` reads a lambda in the three positions the grammar gives it.
:::

:::definition "parse_statement" (parent := "ud1") (lean := "CoreCpp.block, CoreCpp.statement, CoreCpp.localDecl, CoreCpp.forInit, CoreCpp.exprStatement, CoreCpp.isTypeStart, CoreCpp.type, CoreCpp.basicType, CoreCpp.classType, CoreCpp.qualTail, CoreCpp.templateArgs, CoreCpp.templateArg") (uses := "gram_ast, parse_expr")
One parser function per command nonterminal and per type nonterminal, named after it. The function `statement` chooses the production by the first token, and a token that opens a type, by `isTypeStart`, opens a declaration. The function `exprStatement` reads an expression and then decides between assignment and expression statement by the presence of `=`.

A `Type` is a basic type or a class type, optionally followed by `*`. A class type is a name, qualified by namespaces or not, with template arguments or without. The function `classType` reads an unqualified name in the enclosing namespace. The case of the last component of a qualified name says which type it is, an uppercase one names a class of the program and a lowercase one a class of the library, whose names are lowercase, so `Geometry::Shape` is the first and `std::vector<int>` the second.

A template argument is a type, and a function type `Type(Type, …)` as well. A local declaration with a type may be a reference, and the grammar admits a lambda as its initialiser, which the type checker then rejects, since no declared type is a function type.
:::

:::definition "parse_program" (parent := "ud1") (lean := "CoreCpp.program, CoreCpp.declaration, CoreCpp.P.name, CoreCpp.P.qualify, CoreCpp.P.inHeader, CoreCpp.classDecl, CoreCpp.classRest, CoreCpp.member, CoreCpp.operatorName, CoreCpp.function, CoreCpp.params, CoreCpp.param, CoreCpp.className, CoreCpp.runParser, CoreCpp.parseProgram, CoreCpp.parseExpr, CoreCpp.parseStatement, CoreCpp.parseUnit") (uses := "gram_ast, parse_statement")
A program is a sequence of declarations up to `eof`. Each one is a class, a class template, a namespace, a function, or a class template or a function of the library declared without a body.

The functions carry the names of their nonterminals, with three exceptions. The function `classDecl` reads `Class`, `operatorName` reads `Op` and `P.name` reads `Name`. The function `classRest` reads `Section` inline, and `member` reads `MemberRest`.

A class carries its fields, its methods, its constructor and its destructor, under the visibility of the section that holds them. The function `declaration` flattens a namespace at parse time, and every class it declares carries the prefix of the enclosing namespaces, as `N::C`, which `P.qualify` prepends to an unqualified name.

The function `runParser` runs the lexer and a parser on a string and fails when input remains. The function `parseUnit` parses the output of Preproc, runs the automaton on each line alone and the pass `qualifiers` on all the tokens, and marks the tokens of the lines that come from a header, which `P.inHeader` reads where only a header may declare.
:::

# Preprocessor

The tests of `tests/preproc/` and an inspection of the headers check the agreement stated at the end of this section. No Lean proof covers it.

:::definition "pp_language" (parent := "ud1") (lean := "Preproc.Directive, Preproc.Line, Preproc.Item, Preproc.lines, Preproc.parse, Preproc.group, Preproc.condRest")
Preproc is the preprocessor of Core C++, a language of its own that runs before the lexer of {bpref "lex_automaton"}[]. It reads a file as a sequence of lines and never lexes or parses Core C++, so the two languages share no surface. Every Preproc program is also a valid input of the preprocessor of `g++`.

The terminals of its grammar are whole lines. $`\textit{Text}` stands for any text line, and $`\textit{NL}` ends a directive line.

$$`\begin{array}{lcl} \textit{File} & ::= & \textit{Group} \\ \textit{Group} & ::= & \big(\ \textit{Line}\ \mid\ \textit{Cond}\ \big)^{*} \\ \textit{Line} & ::= & \texttt{\#include}\ \texttt{<}\ \textit{Header}\ \texttt{>}\ \textit{NL}\ \mid\ \texttt{\#define}\ \textit{FlagId}\ \textit{NL}\ \mid\ \textit{Text} \\ \textit{Cond} & ::= & \textit{Test}\ \textit{FlagId}\ \textit{NL}\ \textit{Group}\ \big(\ \texttt{\#else}\ \textit{NL}\ \textit{Group}\ \big)^{?}\ \texttt{\#endif}\ \textit{NL} \\ \textit{Test} & ::= & \texttt{\#ifdef}\ \mid\ \texttt{\#ifndef} \end{array}`

Preproc supports conditional compilation on flags, the inclusion of a subset of the standard library and of the STL, and the function `assert` of `<cassert>`. A flag has no value and never reaches the code. The design is `preproc/ccpp-preproc.md`.
:::

:::definition "pp_lexical" (parent := "ud1") (lean := "Preproc.lexLine, Preproc.directive, Preproc.checkChars, Preproc.isFlag, Preproc.words") (uses := "pp_language")
Every line satisfies five rules, including the lines of a branch that is not selected and the lines of every header. The C++ preprocessor splices lines and removes comments before it recognises directives (N4659 §5.2, phases 2 to 4), and the rules keep the line structure the same for both.

 * A directive line is exactly one of the forms of the grammar.
 * A text line does not start with `#` or with the digraph `%:`, possibly after blanks, since C++ reads `%:` as `#` (N4659 §5.5, Table 1).
 * No line contains a backslash, `/*`, a single quote or a double quote.
 * A flag has the prefix `CCPP_`, a nonempty rest of letters, digits and `_`, and no `__`, which C++ reserves (N4659 §5.10).
 * No word of a text line starts with `CCPP_`, so a flag never occurs in the code. A word is a maximal run of letters, digits and `_`.
:::

:::definition "pp_meaning" (parent := "ud1") (lean := "Preproc.run, Preproc.runItem, Preproc.Item.size, Preproc.blank, Preproc.translateLines, Preproc.translate") (uses := "pp_language, pp_headers")
The flag environment $`\varphi` is a finite set of flags, initially the flags given as `-D CCPP_X=`. The judgement $`\varphi \vdash G \Rightarrow t, \varphi'` gives the output lines $`t` of a group and the environment after it. $`H(h)` is the contents of the Core C++ header $`h`.

$$`\dfrac{}{\varphi \vdash \texttt{\#define}\ F \Rightarrow \varepsilon, \varphi \cup \{F\}}\;\textsf{(P-Define)}`

$$`\dfrac{\varphi \vdash H(h) \Rightarrow t, \varphi'}{\varphi \vdash \texttt{\#include}\ \texttt{<}h\texttt{>} \Rightarrow t, \varphi'}\;\textsf{(P-Include)}`

$$`\dfrac{F \in \varphi \qquad \varphi \vdash G_1 \Rightarrow t, \varphi'}{\varphi \vdash \texttt{\#ifdef}\ F\ G_1\ \texttt{\#else}\ G_2\ \texttt{\#endif} \Rightarrow t, \varphi'}\;\textsf{(P-IfdefT)}`

$$`\dfrac{F \notin \varphi \qquad \varphi \vdash G_2 \Rightarrow t, \varphi'}{\varphi \vdash \texttt{\#ifdef}\ F\ G_1\ \texttt{\#else}\ G_2\ \texttt{\#endif} \Rightarrow t, \varphi'}\;\textsf{(P-IfdefF)}`

The directive `#ifndef` swaps the premises $`F \in \varphi` and $`F \notin \varphi`, and a missing `#else` stands for an empty $`G_2`. A text line gives itself. An `#include` gives the output of the header, and Preproc marks those lines as lines of a header. Every other directive line and every line of a branch that is not selected gives an empty line, so a source file without `#include` keeps its line numbers.

The function `translateLines` gives the output lines of a file under the initial flags, each marked with whether it comes from a header, and `translate` joins them into one text, the output of `bin/ccpp-pre`.

The functions `run`, `runItem` and `Item.size` are `partial`, so Lean records opaque constants that carry the type and not the body, and no property of them is proved here.
:::

:::definition "pp_headers" (parent := "ud1") (lean := "Preproc.Env") (uses := "pp_language")
The headers of Core C++ are Core C++ code for the Core C++ compiler, in `preproc/include`, and `g++` uses its own headers. Each is a Preproc file whose guard makes it idempotent, as a C++ header is (N4659 §20.5.2.2, paragraph 2).

The headers `<vector>` and `<functional>` declare the class templates `std::vector` and `std::function`, and `<cassert>` declares the function `assert`. Chapter {bpref "std_library"}[] gives their semantics.

An `#include` inside a function body puts declarations inside a block, which the grammar of {bpref "gram_full"}[] rejects. Inclusion fails beyond a depth of 64, which bounds a cycle of headers without a guard.
:::

:::theorem "pp_agree" (parent := "ud1") (uses := "pp_meaning, pp_lexical, pp_headers")
Take a Preproc program $`p` whose output Core C++ accepts. Compiling $`p` with `g++` and running the output in Core C++ give the same exit status under the same `-D` options.
:::

:::proof "pp_agree"
The preprocessor of C++ selects the same lines as Preproc (N4659 §19.1, paragraphs 11 and 12), and the lexical rules keep flags out of the code. Each Core C++ header agrees with the `g++` header of the same name on the names the subset admits, one obligation per header.

The file `tests/Preproc.lean` checks the argument on the programs of `tests/preproc`, comparing the selected lines with those of `g++ -E` and the exit status with that of `g++`. No Lean proof covers it.
:::
