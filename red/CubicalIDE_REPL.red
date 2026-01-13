-- CubicalIDE_REPL.redtt
-- Interactive Lego REPL + Cubical VM integration

module CubicalIDE_REPL

import CubicalIDE_LegoIntegration

-----------------------------------------------------
-- REPL Environment
-----------------------------------------------------
data REPLState : Type where
  MkState : { grammar : Grammar
            ; defs    : List (String × LegoTerm)
            } -> REPLState

emptyState : REPLState
emptyState = MkState { grammar = mergedGrammar
                     , defs    = [] }

-----------------------------------------------------
-- Commands
-----------------------------------------------------
data Command : Type where
  Define   : String -> LegoTerm -> Command
  Eval     : LegoTerm -> Command
  Visualize: LegoTerm -> Command
  Grammar  : Grammar -> Command

-----------------------------------------------------
-- Command execution
-----------------------------------------------------
execCommand : REPLState -> Command -> (REPLState × String)
execCommand st (Define name term) =
  let newDefs = (name, term) :: st.defs
  let newState = MkState { grammar = st.grammar, defs = newDefs }
  (newState, "Defined " ++ name)

execCommand st (Eval term) =
  let compiled = compileTerm term
  let normalized = normalize compiled
  (st, show normalized)

execCommand st (Visualize term) =
  let net = toINetCell (normalize (compileTerm term))
  (st, visualize net)

execCommand st (Grammar g) =
  let merged = pushout [st.grammar, g]
  (MkState { grammar = merged, defs = st.defs }, "Grammar merged")

-----------------------------------------------------
-- REPL loop (pseudo-code)
-----------------------------------------------------
replLoop : REPLState -> IO ()
replLoop st = do
  putStr "> "
  input <- getLine
  case parseCommand input of
    nothing -> do putStrLn "Parse error"; replLoop st
    just cmd -> do
      let (newState, output) = execCommand st cmd
      putStrLn output
      replLoop newState

-- Example parseCommand (very simplified)
parseCommand : String -> Maybe Command
parseCommand s =
  if startsWith "def " s then
    let nameTerm = parseDef s
    just (Define nameTerm.0 nameTerm.1)
  else if startsWith "eval " s then
    let t = parseLegoTerm (drop 5 s)
    just (Eval t)
  else if startsWith "vis " s then
    let t = parseLegoTerm (drop 4 s)
    just (Visualize t)
  else if startsWith "gram " s then
    let g = parseGrammar (drop 5 s)
    just (Grammar g)
  else
    nothing

-----------------------------------------------------
-- Example session
-----------------------------------------------------
-- REPL would allow:
-- > def id (lam x Type x)
-- > eval (app id y)
-- > vis (lam x Type (refl x))
-- > gram myExtension
