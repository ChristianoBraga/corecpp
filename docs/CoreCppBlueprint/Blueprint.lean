import Verso
import VersoManual
import VersoBlueprint
import VersoBlueprint.Commands.Graph
import VersoBlueprint.Commands.Summary
import CoreCppBlueprint.Chapters.Dominios
import CoreCppBlueprint.Chapters.Expressoes
import CoreCppBlueprint.Chapters.Comandos
import CoreCppBlueprint.Chapters.Abstracao
import CoreCppBlueprint.Chapters.Previstas

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Core C++" =>

Core C++ is a subset of C++17 with an LL(1) grammar and no undefined behaviour, the core language of the course 09022, Linguagens de Programação, at IME. This blueprint holds the typing and evaluation rules in natural semantics, in the sequent style of Kahn (1987), and points each rule to the Lean code that implements it in `core-cpp/CoreCpp/`. One chapter per UD of the syllabus, one node per construction, and a final chapter with the planned constructions that have no rules yet.

{include 0 CoreCppBlueprint.Chapters.Dominios}
{include 0 CoreCppBlueprint.Chapters.Expressoes}
{include 0 CoreCppBlueprint.Chapters.Comandos}
{include 0 CoreCppBlueprint.Chapters.Abstracao}
{include 0 CoreCppBlueprint.Chapters.Previstas}

{blueprint_graph}
{blueprint_summary}
