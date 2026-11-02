module
import VersoSlides
import Talk

open VersoSlides

-- Look and post-processing adapted from leodemoura/ETAPSTutorial2026.

def titleSlide : String :=
  "<section class=\"title-slide split\" data-state=\"title\">" ++
  "<div class=\"logo-pane\"><img class=\"logo\" src=\"logo.svg\" alt=\"Verified Cut\"></div>" ++
  "<div class=\"text-pane\"><h1>Verified Cut</h1>" ++
  "<div class=\"meta\">A FLAC audio cutter, proven correct in Lean 4<br><strong>Philippe Dumonet</strong></div>" ++
  "<div class=\"date\">2026</div>" ++
  "</div></section>"

def icon (name : String) : IO String := do
  let svg ← IO.FS.readFile ("static" / s!"{name}.svg")
  return svg.trimAscii.toString.replace "<svg " "<svg class=\"icon\" fill=\"currentColor\" aria-hidden=\"true\" "

def outroSlide : IO String := do
  let row (ic text : String) (href : Option String := none) : IO String := do
    let body := s!"{← icon ic}<span>{text}</span>"
    return match href with
      | some h => s!"<a class=\"contact\" href=\"{h}\">{body}</a>"
      | none => s!"<div class=\"contact\">{body}</div>"
  return "<section class=\"title-slide split outro\" data-state=\"title\">" ++
    "<div class=\"logo-pane\"><img class=\"logo\" src=\"logo.svg\" alt=\"Verified Cut\"></div>" ++
    "<div class=\"text-pane\"><h1>Thanks for listening!</h1><div class=\"contacts\">" ++
    (← row "mail" "philippe@dumo.net" (some "mailto:philippe@dumo.net")) ++
    (← row "x" "@real_philogy" (some "https://x.com/real_philogy")) ++
    (← row "github" "github.com/Philogy/verified-cut" (some "https://github.com/Philogy/verified-cut")) ++
    "</div></div></section>"

def slideHeader : String :=
  "<div class=\"slide-header\"></div>"

def appendixSlide : String :=
  let src (title href desc : String) :=
    s!"<li><a href=\"{href}\">{title}</a><span class=\"desc\">{desc}</span></li>"
  s!"<section>{slideHeader}<h2>Appendix: Sources</h2><ul class=\"sources\">" ++
    src "RFC 9639: Free Lossless Audio Codec (FLAC)" "https://www.rfc-editor.org/rfc/rfc9639"
      "The bitstream format; our theorems are about our own decoder, conformance is tested" ++
    src "xiph/flac (libFLAC 1.5.0)" "https://github.com/xiph/flac"
      "Reference codec for tests and benchmarks; LPC method follows it" ++
    src "C. A. R. Hoare, Proof of Correctness of Data Representations (1972)" "https://doi.org/10.1007/BF00289507"
      "Abstraction functions and data refinement, as used for the packed encoder" ++
    src "leodemoura/ETAPSTutorial2026" "https://github.com/leodemoura/ETAPSTutorial2026"
      "Slide look adapted from Leo de Moura's tutorial" ++
    src "leanprover/verso-slides" "https://github.com/leanprover/verso-slides"
      "Verso genre these slides are built with" ++
    "</ul></section>"

public def main : IO UInt32 := do
  let config : Config := { theme := "white", slideNumber := true, transition := "fade", center := false, margin := 0 }
  let rc ← slidesMain (config := config) (doc := %doc Talk)
  let out := config.outputDir
  IO.FS.writeFile (out / "custom.css") (← IO.FS.readFile ("static" / "custom.css"))
  IO.FS.writeFile (out / "logo.svg") (← IO.FS.readFile ("static" / "logo.svg"))
  -- Plots are read from bench/ at build time so the deck shows whatever was last benchmarked.
  for img in ["pareto.gif", "pareto-final.png", "flac-progress.png"] do
    IO.FS.writeBinFile (out / img) (← IO.FS.readBinFile (".." / "bench" / img))
  let htmlPath := out / "index.html"
  let html ← IO.FS.readFile htmlPath
  -- custom.css must come after the bundled stylesheets, which `extraCss` doesn't guarantee.
  let html := html.replace "</head>" "<link rel=\"stylesheet\" href=\"custom.css\"></head>"
  -- custom.css sizes slides with vh/vw, so reveal.js must not scale them.
  let html := html.replace "Reveal.initialize({" "Reveal.initialize({\n        disableLayout: true,"
  -- Registered before `Reveal.initialize`, which runs the highlight plugin.
  let html := html.replace "Reveal.initialize({" ((← IO.FS.readFile ("static" / "lean-hljs.js")) ++ "Reveal.initialize({")
  -- Slides with attributes (e.g. a background colour) are left without the header.
  let html := html.replace "<section>" s!"<section>{slideHeader}"
  let html := html.replace "<div class=\"slides\">" s!"<div class=\"slides\">{titleSlide}"
  let html := html.replace "</section></div>" s!"</section>{← outroSlide}{appendixSlide}</div>"
  IO.FS.writeFile htmlPath html
  -- Inline the hover docs: `fetch` fails when the deck is opened from `file://`.
  let docs ← IO.FS.readFile (out / "-verso-docs.json")
  for js in ["highlighting.js", "panel.js"] do
    let path := out / "lib" / js
    let src ← IO.FS.readFile path
    IO.FS.writeFile path (src.replace "fetch(\"-verso-docs.json\")" s!"Promise.resolve(\{ ok: true, json: () => ({docs}) })")
  return rc
