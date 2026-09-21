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
import CoreCppBlueprint.Chapters.Paradigms

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Core C++" =>

Core C++ is a subset of C++17 with an LL(1) grammar, a deterministic semantics and no undefined behaviour. This blueprint holds the lexer, the grammar, and the typing and evaluation rules in natural semantics, in the sequent style of Kahn (1987), and points each rule to the Lean code that implements it in `core-cpp/CoreCpp/`. The source, the interpreter and this blueprint live in the repository [github.com/ChristianoBraga/corecpp](https://github.com/ChristianoBraga/corecpp). One chapter per group of constructions, one node per construction or nonterminal. The design lists no construction the blueprint leaves out.

{include 0 CoreCppBlueprint.Chapters.Grammar}
{include 0 CoreCppBlueprint.Chapters.Domains}
{include 0 CoreCppBlueprint.Chapters.Expressions}
{include 0 CoreCppBlueprint.Chapters.Commands}
{include 0 CoreCppBlueprint.Chapters.Abstraction}
{include 0 CoreCppBlueprint.Chapters.Encapsulation}
{include 0 CoreCppBlueprint.Chapters.TypeSystems}
{include 0 CoreCppBlueprint.Chapters.Paradigms}

{blueprint_graph}
{blueprint_summary}
