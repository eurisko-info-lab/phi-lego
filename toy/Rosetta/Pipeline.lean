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
  IO.println s!"rosetta2lean content length: {r2lContent.length}"
  let tokens := tokenize r2lContent
  IO.println s!"rosetta2lean tokens: {tokens.length}"
  IO.println s!"first 20 tokens: {tokens.take 20 |>.map (·.toString) |> String.intercalate " "}"
  let some r2lAst := parseLegoFile r2lContent | IO.eprintln "parse rosetta2lean failed"; return
  let rules2 := extractRules r2lAst
  let lean := transform rules2 lifted

  -- write to generated/
  IO.FS.createDirAll "./generated/Cubical"
  IO.FS.writeFile "./generated/Cubical/Redtt.lean" (toString (repr lean))
  IO.println "Wrote generated/Cubical/Redtt.lean"
