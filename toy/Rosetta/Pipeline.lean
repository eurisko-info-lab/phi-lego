/-
  Pipeline.lean
  cubical := parse CubicalTT.lego
  lifted := run rules cubical2rosetta.lego on cubical
  lean := run rules rosetta2lean.lego on lifted
  print lean → generated/
-/

import Lego.Runtime
import Lego.Loader

open Lego.Runtime
open Lego.Loader
open Lego

def main : IO Unit := do
  -- Step 0: Initialize runtime by loading Bootstrap.lego
  let rt ← Lego.Runtime.init

  -- cubical := parse CubicalTT.lego
  let cubicalContent ← IO.FS.readFile "./test/Redtt.lego"
  let cubical ← match parseLegoFileE rt cubicalContent with
    | .error e => IO.eprintln s!"parse CubicalTT failed: {e}"; return
    | .ok ast => pure ast

  -- lifted := run rules cubical2rosetta.lego on cubical
  let c2rContent ← IO.FS.readFile "./src/Rosetta/cubical2rosetta.lego"
  let c2rAst ← match parseLegoFileE rt c2rContent with
    | .error e => IO.eprintln s!"parse cubical2rosetta failed: {e}"; return
    | .ok ast => pure ast
  let rules1 := extractRules c2rAst
  let lifted := transform rules1 cubical

  -- lean := run rules rosetta2lean.lego on lifted
  let r2lContent ← IO.FS.readFile "./src/Rosetta/rosetta2lean.lego"
  match parseLegoFileE rt r2lContent with
  | .ok r2lAst =>
    let rules2 := extractRules r2lAst
    let lean := transform rules2 lifted
    -- write to generated/
    IO.FS.createDirAll "./generated/Cubical"
    IO.FS.writeFile "./generated/Cubical/Redtt.lean" (toString (repr lean))
    IO.println "Wrote generated/Cubical/Redtt.lean"
  | .error e =>
    IO.eprintln s!"parse rosetta2lean failed: {e}"
