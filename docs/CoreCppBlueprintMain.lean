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
def katexZoomFixCss : CSS := ⟨".katex .vlist-r > .vlist-s { font-size: 2px !important; }"⟩

/-- WebKit lays the table out wrongly on its first pass even with the CSS above,
and any restyle of the cell after KaTeX has rendered corrects it. The script
restyles the cells once the page has loaded, and again for KaTeX output added
later, such as the hover previews. -/
def katexZoomFixJs : JS := ⟨"(function(){
  function fix(root){root.querySelectorAll('.katex .vlist-s').forEach(function(s){s.style.fontSize='2px';});}
  function run(){requestAnimationFrame(function(){fix(document);});}
  if(document.readyState==='complete'){run();}else{window.addEventListener('load',run);}
  new MutationObserver(function(ms){ms.forEach(function(m){m.addedNodes.forEach(function(n){
    if(n.nodeType===1&&(n.matches('.katex')||n.querySelector('.katex'))){requestAnimationFrame(function(){fix(n);});}});});})
    .observe(document.documentElement,{childList:true,subtree:true});
})();"⟩

def main (args : List String) : IO UInt32 :=
  Informal.PreviewManifest.blueprintMainWithPreviewData
    (%doc CoreCppBlueprint.Blueprint)
    args
    (extensionImpls := by exact extension_impls%)
    (config := { extraCss := {katexZoomFixCss}, extraJs := {katexZoomFixJs},
                 logo := some "logo.svg",
                 logoLink := some "https://github.com/ChristianoBraga/corecpp",
                 extraFilesHtml := [("logo.svg", "logo.svg")] })
