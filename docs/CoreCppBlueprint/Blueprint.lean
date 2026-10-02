import Verso
import VersoManual
import VersoBlueprint
import VersoBlueprint.Commands.Graph
import VersoBlueprint.Commands.Summary
import CoreCppBlueprint.Chapters.Grammar
import CoreCppBlueprint.Chapters.Domains
import CoreCppBlueprint.Chapters.Expressions
import CoreCppBlueprint.Chapters.Commands
import CoreCppBlueprint.Chapters.Abstraction
import CoreCppBlueprint.Chapters.Encapsulation
import CoreCppBlueprint.Chapters.TypeSystems
import CoreCppBlueprint.Chapters.Library

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Core C++" =>

Core C++ is a subset of C++17 with an LL(1) grammar, a deterministic semantics and no undefined behaviour.

This blueprint holds the lexer, the grammar, and the typing and evaluation rules in natural semantics, in the sequent style of Kahn (1987). Each rule is a constructor of an inductive proposition in `core-cpp/CoreCpp/Semantics/`, and each node points at that relation and at the function of the type checker or the evaluator that interprets it.

The source, the interpreter and this blueprint live in the repository [github.com/ChristianoBraga/corecpp](https://github.com/ChristianoBraga/corecpp).

One chapter per group of constructions, one node per construction or nonterminal. The design lists no construction the blueprint leaves out.

{include 0 CoreCppBlueprint.Chapters.Grammar}
{include 0 CoreCppBlueprint.Chapters.Domains}
{include 0 CoreCppBlueprint.Chapters.Expressions}
{include 0 CoreCppBlueprint.Chapters.Commands}
{include 0 CoreCppBlueprint.Chapters.Abstraction}
{include 0 CoreCppBlueprint.Chapters.Encapsulation}
{include 0 CoreCppBlueprint.Chapters.TypeSystems}
{include 0 CoreCppBlueprint.Chapters.Library}

# References

* Gilles Kahn, Natural Semantics, STACS 1987, LNCS 247, Springer.
* Gilles Kahn, Natural semantics, Research Report RR-0601, INRIA, 1987, [HAL](https://inria.hal.science/inria-00075953).
* Bjarne Stroustrup, The C++ Programming Language, 4th edition, Addison-Wesley, 2013.
* ISO/IEC 14882:2017, Programming Languages, C++, cited as N4659, the final working draft of WG21, [open-std.org](https://www.open-std.org/jtc1/sc22/wg21/docs/papers/2017/n4659.pdf).
* ISO/IEC 9899:2011, Programming Languages, C, cited as N1570, the committee draft of WG14, [open-std.org](https://www.open-std.org/jtc1/sc22/wg14/www/docs/n1570.pdf).
* System V Application Binary Interface, AMD64 Architecture Processor Supplement, §3.1.2, Data Representation, [gitlab.com](https://gitlab.com/x86-psABIs/x86-64-ABI).
* Arm, Procedure Call Standard for the Arm 64-bit Architecture (AAPCS64), Arm C and C++ Language Mappings, [github.com](https://github.com/ARM-software/abi-aa/blob/main/aapcs64/aapcs64.rst).
* GCC manual, C Implementation-Defined Behavior, Integers, [gcc.gnu.org](https://gcc.gnu.org/onlinedocs/gcc/Integers-implementation.html).

{blueprint_graph}
{blueprint_summary}
