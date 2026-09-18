import VersoManual
import VersoBlueprint.PreviewManifest
import CoreCppBlueprint.Blueprint

open Verso Doc
open Verso.Genre Manual

/-- KaTeX fixes the baseline of its vertical lists with a table cell of
`font-size: 1px`. WebKit rounds that cell to zero height when the page zoom is
at or below 80 percent, the table baseline falls to the last row, and every
formula gains blank space below it. A 2px cell survives zoom down to 50
percent and does not move the baseline noticeably. -/
def katexZoomFix : CSS := ⟨".katex .vlist-s { font-size: 2px; }"⟩

def main (args : List String) : IO UInt32 :=
  Informal.PreviewManifest.blueprintMainWithPreviewData
    (%doc CoreCppBlueprint.Blueprint)
    args
    (extensionImpls := by exact extension_impls%)
    (config := { extraCss := {katexZoomFix} })
