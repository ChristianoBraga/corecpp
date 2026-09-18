import VersoManual
import VersoBlueprint.PreviewManifest
import CoreCppBlueprint.Blueprint

open Verso Doc
open Verso.Genre Manual

def main (args : List String) : IO UInt32 :=
  Informal.PreviewManifest.blueprintMainWithPreviewData
    (%doc CoreCppBlueprint.Blueprint)
    args
    (extensionImpls := by exact extension_impls%)
