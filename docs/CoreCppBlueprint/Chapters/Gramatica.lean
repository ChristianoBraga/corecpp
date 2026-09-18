import Verso
import VersoManual
import VersoBlueprint
import CoreCpp.Token
import CoreCpp.Lexer
import CoreCpp.Syntax
import CoreCpp.Parser

open Verso.Genre
open Verso.Genre.Manual
open Informal

set_option verso.blueprint.foldCodeBlocks true

#doc (Manual) "UD I, lexer and grammar" =>

Core C++ has an LL(1) grammar over tokens. Three lexical and syntactic conventions remove the ambiguities of C++. Type identifiers start with an uppercase letter and variable identifiers with a lowercase one, which decides in the lexer whether `<` opens a template argument or compares. Template instantiation occurs only in type position. Methods are defined inside the class. The lexer is a hand written finite automaton with the longest match rule, and the parser is recursive descent with one function per nonterminal.

:::group "ud1"
UD I, syntax, tokens and the parser.
:::

# Lexer

:::definition "lex_tokens" (parent := "ud1") (lean := "CoreCpp.Token, CoreCpp.keywords, CoreCpp.symbols3, CoreCpp.symbols2, CoreCpp.symbols1")
Tokens fall in five classes. Reserved words, among them `int`, `bool`, `void`, `if`, `else`, `while`, `for`, `return`, `true`, `false`, `auto`, `class`, `new`, `delete`, `nullptr`, `this`, `virtual`, `override`, `namespace`, `template`, `typename` and `operator`. Type identifiers, `TypeId`, with an uppercase initial. Variable identifiers, `VarId`, with a lowercase initial, naming variables, fields, functions and methods. Decimal integer literals, `IntLit`. Operators and punctuation, with `[=]` as a single token by the longest match rule. There is no token `>>`, so `Pilha<Pilha<int>>` closes with two tokens `>`.

```
Token     ::= Keyword | TypeId | VarId | IntLit | Symbol
Keyword   ::= 'int' | 'bool' | 'void' | 'class' | 'public' | 'private' | 'new' | 'delete'
            | 'nullptr' | 'this' | 'virtual' | 'override' | 'namespace' | 'template'
            | 'typename' | 'auto' | 'if' | 'else' | 'while' | 'for' | 'return'
            | 'true' | 'false' | 'operator' | 'std::function' | 'std::vector'
TypeId    ::= Upper IdentChar*
VarId     ::= ( Lower | '_' ) IdentChar*                    -- and not a Keyword
IntLit    ::= Digit Digit*
Symbol    ::= '[=]'
            | '==' | '!=' | '<=' | '>=' | '&&' | '||' | '->' | '::'
            | '+' | '-' | '*' | '/' | '%' | '<' | '>' | '!' | '?' | ':' | '='
            | '(' | ')' | '{' | '}' | '[' | ']' | ',' | ';' | '.' | '&' | '~'
IdentChar ::= Upper | Lower | Digit | '_'
Upper     ::= 'A' | ... | 'Z'
Lower     ::= 'a' | ... | 'z'
Digit     ::= '0' | ... | '9'
Skip      ::= WhiteSpace | '//' NotNewline* Newline
```

The input is the longest sequence of `Token` and `Skip` that covers it, `Skip` is discarded, and each token is the longest match at its position. The symbols of three characters are tried before those of two and of one.
:::

:::definition "lex_conventions" (parent := "ud1") (lean := "CoreCpp.Lexer.identifier") (uses := "lex_tokens")
An identifier is classified by its initial after the reserved words are excluded. The names `std::function` and `std::vector` are one token each, recognised before the identifier rule because `std` starts with a lowercase letter.
:::

:::definition "lex_automaton" (parent := "ud1") (lean := "CoreCpp.lex, CoreCpp.Lexer.run, CoreCpp.Lexer.takeWhile, CoreCpp.Lexer.matchSymbol, CoreCpp.Lexer.skipLine") (uses := "lex_tokens, lex_conventions")
The lexer maps a string to an array of tokens ended by `eof`. It discards white space and line comments, reads the longest run of digits as an integer literal, the longest run of identifier characters as an identifier, and tries the symbols of three, two and one characters in that order. Any other character is a lexical error.
:::

# Grammar

:::definition "gram_full" (parent := "ud1")
The grammar of Core C++, in EBNF, from section 4 of the language design. The nonterminals are named as the parser functions. The postfix `X*` repeats `X` zero or more times, the postfix `X?` makes `X` optional, parentheses group, the bar separates alternatives and terminals stand between single quotes. The grammar is written without left recursion and left factored.

```
Program       ::= Declaration*
Declaration   ::= 'namespace' TypeId '{' Declaration* '}'
                | 'template' '<' 'typename' TypeId '>' Class
                | Class
                | Function

Class         ::= 'class' TypeId ( ':' 'public' ClassType )? '{' Section* '}' ';'
Section       ::= ( 'public' | 'private' ) ':' Member*
Member        ::= 'virtual' ( Type VarId Params Block | '~' TypeId '(' ')' Block )
                | '~' TypeId '(' ')' Block
                | ( BasicType | 'std::function' '<' Type '(' ( Type ( ',' Type )* )? ')' '>' | 'std::vector' '<' Type '>' '*'? ) '&'? MemberRest
                | TypeId ( Params Block | ClassTypeRest '*'? '&'? MemberRest )
MemberRest    ::= VarId ( ';' | Params 'override'? Block )
                | 'operator' Op Params Block
Op            ::= '+' | '-' | '*' | '/' | '%' | '==' | '!=' | '<' | '<=' | '>' | '>=' | '[' ']'

Function      ::= Type VarId Params Block
Params        ::= '(' ( Param ( ',' Param )* )? ')'
Param         ::= Type VarId

Type          ::= ( BasicType | ( ClassType | 'std::vector' '<' Type '>' ) '*'? | 'std::function' '<' Type '(' ( Type ( ',' Type )* )? ')' '>' ) '&'?
BasicType     ::= 'int' | 'bool' | 'void'
ClassType     ::= TypeId ClassTypeRest
ClassTypeRest ::= ( '::' TypeId )* ( '<' Type ( ',' Type )* '>' )?

Block         ::= '{' Statement* '}'
Statement     ::= Block
                | 'if' '(' Expr ')' Block ( 'else' Block )?
                | 'while' '(' Expr ')' Block
                | 'for' '(' ForInit ';' Expr ';' ExprStatement ')' Block
                | 'return' ArgExpr? ';'
                | 'delete' Expr ';'
                | LocalDecl ';'
                | ExprStatement ';'
LocalDecl     ::= 'auto' VarId '=' Expr
                | Type VarId '=' ArgExpr
ForInit       ::= LocalDecl | ExprStatement
ExprStatement ::= Expr ( '=' Expr )?

Expr          ::= OrExpr ( '?' Expr ':' Expr )?
OrExpr        ::= AndExpr ( '||' AndExpr )*
AndExpr       ::= EqExpr ( '&&' EqExpr )*
EqExpr        ::= RelExpr ( ( '==' | '!=' ) RelExpr )*
RelExpr       ::= AddExpr ( ( '<' | '<=' | '>' | '>=' ) AddExpr )*
AddExpr       ::= MulExpr ( ( '+' | '-' ) MulExpr )*
MulExpr       ::= UnaryExpr ( ( '*' | '/' | '%' ) UnaryExpr )*
UnaryExpr     ::= ( '!' | '-' | '*' ) UnaryExpr | PostfixExpr
PostfixExpr   ::= Primary ( '[' Expr ']' | '.' VarId Args? | '->' VarId Args? | Args )*
Primary       ::= IntLit | 'true' | 'false' | 'nullptr' | 'this' | VarId
                | '(' Expr ')'
                | 'new' ( ClassType | 'std::vector' '<' Type '>' ) Args
Args          ::= '(' ( ArgExpr ( ',' ArgExpr )* )? ')'
ArgExpr       ::= Lambda | Expr
Lambda        ::= '[=]' Params '->' Type Block
```

A statement is a command or an expression followed by `;`. Assignment is a command, and `ExprStatement` joins the two forms that start with an expression to keep the grammar LL(1). In the abstract syntax the commands form the type `Cmd`, and the expression statement is the command `exprStmt`, which evaluates and discards the value. The left side of an assignment must denote a location, a check made by the type checker. A lambda expression is an `ArgExpr` and not a `Primary`, so it occurs only as argument, as initialiser of a declaration and as `return` expression.
:::

:::theorem "gram_ll1" (parent := "ud1") (uses := "gram_full")
The grammar is LL(1). Two left factorings make it so. In `Member`, a token `TypeId` opens both a constructor and the type of a field or method, and the next token decides, `(` for a constructor and any other for a type. In `Statement`, a type token opens `LocalDecl` and a `VarId`, `this`, `*`, `(` or a literal opens `ExprStatement`. The FIRST sets are disjoint because types start with a reserved word or a `TypeId`, and expressions start with a `VarId`, `this`, `new`, a literal, `(`, `!`, `-` or `*`. No expression starts with a `TypeId`. The property is verified by the computation of FIRST and FOLLOW in the material of UD I, not by a Lean proof.
:::

# Abstract syntax and parser

:::definition "gram_ast" (parent := "ud1") (lean := "CoreCpp.Ty, CoreCpp.UnOp, CoreCpp.BinOp, CoreCpp.Expr, CoreCpp.Cmd, CoreCpp.Param, CoreCpp.Fun, CoreCpp.Program") (uses := "gram_full")
The abstract syntax has one inductive type per class of nonterminals. `Expr` has literals, variable, unary and binary operators, conditional and call. `Cmd` has block, `if`, `while`, `for`, `return`, declaration with a type or with `auto`, assignment and expression statement. A `Fun` has a return type, a name, parameters and a body, and a `Program` is a list of functions. The abstract grammar of the implemented subset follows, with one alternative per constructor of `Syntax.lean` and in the same order.

```
τ  ::= int | bool | void                                          Ty
⊖  ::= ! | -                                                      UnOp
⊕  ::= + | - | * | / | % | == | != | < | <= | > | >= | && | ||    BinOp
e  ::= n | b | x | ⊖ e | e₁ ⊕ e₂ | e₁ ? e₂ : e₃ | f(e₁, ..., eₖ)   Expr
c  ::= { c₁ ... cₙ }                                              Cmd.block
     | if (e) { c₁ ... cₙ } else { c'₁ ... c'ₘ }                  Cmd.ite
     | while (e) { c₁ ... cₙ }                                    Cmd.while
     | for (c₀; e; cₛ) { c₁ ... cₙ }                              Cmd.for
     | return | return e                                          Cmd.ret
     | τ x = e | auto x = e                                       Cmd.decl, Cmd.declAuto
     | e₁ = e₂                                                    Cmd.assign
     | e;                                                         Cmd.exprStmt
p  ::= τ x                                                        Param
F  ::= τ f(p₁, ..., pₖ) { c₁ ... cₙ }                              Fun
P  ::= F₁ ... Fₙ                                                  Program
```

Here $`n` is an integer, $`b` a boolean, $`x` a variable identifier and $`f` a function identifier. The abstract syntax has no parentheses and no precedence, because the tree fixes the structure.
:::

:::definition "parse_expr" (parent := "ud1") (lean := "CoreCpp.expr, CoreCpp.orExpr, CoreCpp.andExpr, CoreCpp.eqExpr, CoreCpp.relExpr, CoreCpp.addExpr, CoreCpp.mulExpr, CoreCpp.unaryExpr, CoreCpp.postfixExpr, CoreCpp.primary, CoreCpp.args") (uses := "gram_full, gram_ast, lex_automaton")
One parser function per expression nonterminal, from `Expr` down to `Primary`. Each level of the grammar is one level of precedence, and the repetition `( op Operand )*` builds a left associative tree. In the implemented subset `PostfixExpr` covers only the function call, and `Primary` covers literals, variables and parenthesised expressions.
:::

:::definition "parse_statement" (parent := "ud1") (lean := "CoreCpp.block, CoreCpp.statement, CoreCpp.localDecl, CoreCpp.forInit, CoreCpp.exprStatement") (uses := "gram_full, gram_ast, parse_expr")
One parser function per command nonterminal. The function `statement` chooses the production by the first token, and `exprStatement` reads an expression and then decides between assignment and expression statement by the presence of `=`. In the implemented subset `Type` is `BasicType`.
:::

:::definition "parse_program" (parent := "ud1") (lean := "CoreCpp.program, CoreCpp.function, CoreCpp.params, CoreCpp.param, CoreCpp.basicType, CoreCpp.runParser, CoreCpp.parseProgram, CoreCpp.parseExpr, CoreCpp.parseStatement") (uses := "gram_full, gram_ast, parse_statement")
A program is a sequence of functions up to `eof`. The function `runParser` runs the lexer and a parser on a string and requires the whole input to be consumed. In the implemented subset a `Declaration` is a `Function`.
:::
