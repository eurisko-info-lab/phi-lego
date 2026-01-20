/-
  Pipeline.lean
  cubical := parse CubicalTT.lego
  lifted := run rules cubical2rosetta.lego on cubical
  lean := run rules rosetta2lean.lego on lifted
  print lean → generated/
-/

import Lego.Runtime
import Lego.Bootstrap
import Lego.Loader

open Lego.Runtime
open Lego.Bootstrap
open Lego.Loader

def main : IO Unit := do
  -- cubical := parse CubicalTT.lego
  let cubicalContent ← IO.FS.readFile "./test/Redtt.lego"
  let some cubical := parseLegoFile cubicalContent | IO.eprintln "parse CubicalTT failed"; return

  -- lifted := run rules cubical2rosetta.lego on cubical
  let c2rContent ← IO.FS.readFile "./src/Rosetta/cubical2rosetta.lego"
  let some c2rAst := parseLegoFile c2rContent | IO.eprintln "parse cubical2rosetta failed"; return
  let rules1 := extractRules c2rAst
  let lifted := transform rules1 cubical

  -- lean := run rules rosetta2lean.lego on lifted
  let r2lContent ← IO.FS.readFile "./src/Rosetta/rosetta2lean.lego"
  match parseLegoFile r2lContent with
  | .some r2lAst =>
    let rules2 := extractRules r2lAst
    let lean := transform rules2 lifted
    -- write to generated/
    IO.FS.createDirAll "./generated/Cubical"
    IO.FS.writeFile "./generated/Cubical/Redtt.lean" (toString (repr lean))
    IO.println "Wrote generated/Cubical/Redtt.lean"
  | .none =>
    IO.eprintln s!"parse rosetta2lean failed"
