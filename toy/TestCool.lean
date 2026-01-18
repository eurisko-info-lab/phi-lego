/-
  TestCool: CoolTT-specific tests for Lego

  Tests for CoolTT library parsing.
  Run with: lake exe lego-test-cool
-/

import Lego
import Lego.Bootstrap
import Lego.Loader

open Lego
open Lego.Loader

/-! ## Test Framework -/

structure TestResult where
  name : String
  passed : Bool
  message : String := ""

def assertTrue (name : String) (cond : Bool) : TestResult :=
  { name := name, passed := cond, message := if cond then "✓" else "✗ expected true" }

/-! ## CoolTT Parsing Utilities -/

/-- Get the main token productions to try in priority order -/
def getMainTokenProdsOrdered (tokenProds : Productions) : List String :=
  let names := tokenProds.map (·.1)
  -- Priority: comments/whitespace first (to skip), then longest operators first
  -- op3 before op2 before sym to ensure longest match
  let priority := ["Token.comment", "Token.ws", "Token.string", "Token.op3", "Token.op2",
                   "Token.ident", "Token.number", "Token.sym"]
  priority.filter names.contains

/-- Split a .cooltt file into individual top-level declarations -/
def splitCoolttDecls (content : String) : List String := Id.run do
  let noComments := content.splitOn "\n"
    |>.map (fun line =>
      match line.splitOn "--" with
      | [] => ""
      | first :: _ => first)
    |> String.intercalate "\n"
  let lines := noComments.splitOn "\n"
  let mut decls : List String := []
  let mut current := ""
  for line in lines do
    let trimmed := line.trimLeft
    -- CoolTT top-level declarations start with these keywords
    let isDeclStart := trimmed.startsWith "import " || trimmed.startsWith "def " ||
       trimmed.startsWith "axiom " || trimmed.startsWith "#print " ||
       trimmed.startsWith "#normalize " || trimmed.startsWith "#fail " ||
       trimmed.startsWith "#debug " || trimmed.startsWith "#quit" ||
       trimmed.startsWith "section " || trimmed.startsWith "view " ||
       trimmed.startsWith "export " || trimmed.startsWith "repack " ||
       -- Handle modifier + decl on same line
       trimmed.startsWith "shadowing def " || trimmed.startsWith "abstract def " ||
       trimmed.startsWith "shadowing axiom " || trimmed.startsWith "abstract axiom "
    -- Standalone modifiers: "abstract" alone or "unfold X" without ":="
    let hasAssign := (trimmed.splitOn ":=").length > 1
    let isModifierOnly := trimmed == "abstract" ||
                          (trimmed.startsWith "unfold " && !hasAssign)
    -- Helper to check if a string is just modifiers
    let isJustModifiers := fun (s : String) =>
      let lns := s.splitOn "\n"
      lns.all fun l =>
        let t := l.trimLeft
        t.isEmpty || t == "abstract" ||
        (t.startsWith "unfold " && (t.splitOn ":=").length <= 1)
    if isDeclStart then
      if !current.isEmpty then
        let currentTrim := current.trim
        -- If current is just modifiers, combine with this decl
        if isJustModifiers currentTrim then
          current := current ++ "\n" ++ line
        else
          decls := decls ++ [currentTrim]
          current := line
      else
        current := line
    else if isModifierOnly then
      -- Modifier line
      if current.isEmpty then
        current := line
      else
        let currentTrim := current.trim
        -- If current is just modifiers, accumulate
        if isJustModifiers currentTrim then
          current := current ++ "\n" ++ line
        else
          -- Current has a real declaration, save it and start fresh with modifier
          decls := decls ++ [currentTrim]
          current := line
    else
      current := current ++ "\n" ++ line
  if !current.isEmpty then
    decls := decls ++ [current.trim]
  return decls.filter (fun s => !s.isEmpty)

/-- Fuel for CoolTT parsing - lower than defaultFuel to avoid stack overflow
    The CoolTT grammar has deep recursion; 10000 is enough for most declarations -/
def coolttFuel : Nat := 10000

/-- Debug parsing for a single CoolTT declaration, returning details -/
def debugCoolttParse (decl : String) : IO Unit := do
  try
    let content ← IO.FS.readFile "./test/Cooltt.lego"
    match Bootstrap.parseLegoFile content with
    | none => IO.println "Failed to load Cooltt.lego"
    | some ast =>
      let coolttProds := extractAllProductions ast
      let tokenProds := extractTokenProductions ast
      let coolttKeywords := ["abstract", "shadowing", "def", "axiom", "import",
                             "let", "in", "elim", "with", "section", "view", "export", "repack",
                             "begin", "end", "as", "sig", "struct", "open", "renaming",
                             "generalize", "unfold", "ext", "sub", "coe", "com", "hcom", "hfill"]
      let keywords := (extractKeywords coolttProds ++ coolttKeywords).eraseDups
      let mainProds := getMainTokenProdsOrdered tokenProds
      let tokens := tokenizeWithGrammar coolttFuel tokenProds mainProds decl keywords
      IO.println s!"Tokens ({tokens.length}): {tokens.take 30 |>.map reprToken}"

      let declProd := "File.topdecl"
      match coolttProds.find? (·.1 == declProd) with
      | none => IO.println "No File.topdecl production found"
      | some (_, g) =>
        let st : ParseState := { tokens := tokens, binds := [] }
        let (result, _) := parseGrammar coolttFuel coolttProds g st
        match result with
        | none => IO.println s!"Parse failed"
        | some (_, st') =>
          IO.println s!"Parse succeeded"
          IO.println s!"Remaining tokens ({st'.tokens.length}): {st'.tokens.take 20 |>.map reprToken}"
  catch e => IO.println s!"Error: {e}"

where
  reprToken : Token → String
    | .ident s => s!"id({s})"
    | .lit s => s!"lit({s})"
    | .sym s => s!"sym({s})"
    | .number s => s!"num({s})"

/-- Parse a single .cooltt file declaration using Cooltt grammar -/
def parseCoolttDecl (coolttProds : List (String × GrammarExpr))
                    (tokenProds : List (String × GrammarExpr))
                    (keywords : List String)
                    (decl : String) : Bool :=
  let declProd := "File.topdecl"
  let tokens := if tokenProds.isEmpty then
    Bootstrap.tokenize decl
  else
    let mainProds := getMainTokenProdsOrdered tokenProds
    tokenizeWithGrammar coolttFuel tokenProds mainProds decl keywords
  match coolttProds.find? (·.1 == declProd) with
  | some (_, g) =>
    let st : ParseState := { tokens := tokens, binds := [] }
    let (result, _) := parseGrammar coolttFuel coolttProds g st
    match result with
    | some (_, st') => st'.tokens.isEmpty
    | none => false
  | none => false

/-- Parse a .cooltt file and return (passed, total, list of failures) -/
def parseCoolttFileVerbose (coolttProds : List (String × GrammarExpr))
                           (tokenProds : List (String × GrammarExpr))
                           (keywords : List String)
                           (path : String) : IO (Nat × Nat × List String) := do
  try
    let content ← IO.FS.readFile path
    let decls := splitCoolttDecls content
    let mut passed := 0
    let mut total := 0
    let mut failures : List String := []
    for decl in decls do
      total := total + 1
      if parseCoolttDecl coolttProds tokenProds keywords decl then
        passed := passed + 1
      else
        let preview := if decl.length > 200 then decl.take 200 else decl
        let oneLine := preview.replace "\n" " "
        failures := failures ++ [oneLine]
    pure (passed, total, failures)
  catch _ =>
    pure (0, 0, [])

/-- Recursively find all .cooltt files in a directory -/
partial def findCoolttFiles (dir : String) : IO (List String) := do
  let mut files : List String := []
  try
    let entries ← System.FilePath.readDir dir
    for entry in entries do
      let path := entry.path.toString
      if ← System.FilePath.isDir entry.path then
        let subFiles ← findCoolttFiles path
        files := files ++ subFiles
      else if path.endsWith ".cooltt" then
        files := files ++ [path]
  catch _ =>
    pure ()
  pure files

/-! ## CoolTT Library Parsing Tests -/

def runCoolttParsingTests : IO (List TestResult) := do
  let grammarResult ← do
    try
      let content ← IO.FS.readFile "./test/Cooltt.lego"
      pure (Bootstrap.parseLegoFile content)
    catch _ =>
      pure none

  match grammarResult with
  | none => pure [{ name := "cooltt_library_parse", passed := false, message := "✗ Cooltt.lego failed to load" }]
  | some ast =>
    let coolttProds := extractAllProductions ast
    let tokenProds := extractTokenProductions ast
    -- CoolTT keywords - ONLY true reserved words that start constructs
    -- Don't include type names (nat, circle, cof) or value names (zero, suc, base, loop)
    -- as these are valid identifiers in many contexts
    let coolttKeywords := ["abstract", "shadowing", "def", "axiom", "import",
                           "let", "in", "elim", "with", "section", "view", "export", "repack",
                           "begin", "end", "as", "sig", "struct", "open", "renaming",
                           "generalize", "unfold", "ext", "sub", "coe", "com", "hcom", "hfill"]
    let keywords := (extractKeywords coolttProds ++ coolttKeywords).eraseDups

    let testPath := "../vendor/cooltt/test"
    let testFiles ← findCoolttFiles testPath
    let sortedFiles := testFiles.toArray.qsort (· < ·) |>.toList

    let mut totalParsed := 0
    let mut totalDecls := 0

    let mut failCount := 0
    IO.println "  Parsing failures (first 10):"
    for filePath in sortedFiles do
      let (parsed, total, failures) ← parseCoolttFileVerbose coolttProds tokenProds keywords filePath
      totalParsed := totalParsed + parsed
      totalDecls := totalDecls + total
      for failure in failures do
        if failCount < 10 then
          IO.println s!"  FAIL [{filePath}]: {failure.take 120}..."
          failCount := failCount + 1

    let overallRate := if totalDecls > 0 then (totalParsed * 100) / totalDecls else 0
    let allPassed := overallRate = 100
    let checkMark := if allPassed then "✓" else "✗"
    let summaryTest := {
      name := "cooltt_library"
      passed := overallRate = 100
      message := s!"{checkMark} ({totalParsed}/{totalDecls} = {overallRate}%) across {sortedFiles.length} files"
    }

    pure [summaryTest]

/-! ## Test Runner -/

def printTestGroup (name : String) (tests : List TestResult) : IO (Nat × Nat) := do
  IO.println s!"\n── {name} ──"
  let mut passed := 0
  let mut failed := 0
  for test in tests do
    if test.passed then
      IO.println s!"  ✓ {test.name}"
      passed := passed + 1
    else
      IO.println s!"  ✗ {test.name}: {test.message}"
      failed := failed + 1
  pure (passed, failed)

def main (args : List String) : IO Unit := do
  IO.println "╔═══════════════════════════════════════════════════════════════╗"
  IO.println "║            CoolTT Tests for Lego                              ║"
  IO.println "╚═══════════════════════════════════════════════════════════════╝"

  let mut totalPassed := 0
  let mut totalFailed := 0

  let coolttTests ← runCoolttParsingTests
  let (p, f) ← printTestGroup "Cooltt Library Parsing Tests" coolttTests
  totalPassed := totalPassed + p; totalFailed := totalFailed + f

  IO.println ""
  IO.println "═══════════════════════════════════════════════════════════════"
  IO.println s!"Total: {totalPassed + totalFailed} tests, {totalPassed} passed, {totalFailed} failed"
  if totalFailed == 0 then
    IO.println "All tests passed! ✓"
  else
    IO.println s!"FAILED: {totalFailed} tests"
    IO.Process.exit 1
