{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE PatternSynonyms #-}
-- | Lego Evaluator: Execute Lego specifications
--
-- == Pushout Architecture
--
-- Language composition is achieved via categorical pushouts:
--
-- @
--       A (shared structure)
--      / \\
--     /   \\
--    L1   L2
--     \\   /
--      \\ /
--      L1 ⊔ L2  (pushout = coequalizer)
-- @
--
-- The 'import' directive is syntactic sugar for pushout:
--
-- @
-- lang MyLang :=
--   import Arith    -- MyLang := MyLang ⊔ Arith
--   import Bool     -- MyLang := MyLang ⊔ Bool
-- @
--
-- is equivalent to:
--
-- @
-- lang MyLang := Arith ⊔ Bool
-- @
--
-- == Package System
--
-- Packages are identified by path from known roots:
--   - prelude/ : .lego files Lego depends on
--   - examples/: example files
--
-- Import resolution uses a registry of known packages/languages.
--
-- This uses bidirectional grammar for parse/print duality.
module Lego.Eval
  ( -- * Evaluation
    evalLego
  , eval
  , normalizeWithGrammar
    -- * Loading
  , loadLang
  , loadLangFile
  , loadLangWithImports
    -- * Compiled Language
  , CompiledLang(..)
    -- * Pushout (Language Composition)
  , poCompiledLang
  , mergeLang  -- legacy alias
    -- * Parsing/Unparsing
  , parse
  , unparse
  , parseWithPiece
  , printWithPiece
  , runPrintWithEnv
    -- * Testing
  , runTestsWithGrammar
  ) where

import Lego
import Lego.GrammarParser (parseLegoFile)
import Lego.GrammarInterp (parseTerm)
import Lego.GrammarAnalysis (collectLiterals)
import Lego.Token (Token(..), tokenize)
import qualified Lego.Registry as R
import qualified Data.Map as M
import qualified Data.Set as S
import Control.Applicative ((<|>))
import System.FilePath (takeDirectory, takeBaseName)

--------------------------------------------------------------------------------
-- Def to Rule Desugaring
--------------------------------------------------------------------------------

-- | Convert a def declaration to a rewrite rule
-- 
-- def creates a simple unfolding rule:
-- def name = body
-- becomes:
-- rule name: name ~> body
--
-- This gives macro/unfold semantics where 'name' expands to its definition.
-- For function-like behavior, use rules directly:
--   rule apply_id: (app id $x) ~> $x
defToRule :: String -> Term -> Rule
defToRule name term = 
  let pat = TmLit name  -- match as literal (requires terms to be parsed with TmLit for defs)
      template = term   -- unfold to definition
  in Rule name pat template Nothing Forward  -- definitions are forward-only

--------------------------------------------------------------------------------
-- Compiled Language
--------------------------------------------------------------------------------

data CompiledLang = CompiledLang
  { clName    :: String
  , clVocab   :: S.Set String
  , clGrammar :: M.Map String (GrammarExpr ())
  , clRules   :: [Rule]
  , clTests   :: [Test]
  , clImports :: [String]  -- track imports for resolution
  } deriving (Show)

emptyCompiled :: String -> CompiledLang
emptyCompiled name = CompiledLang name S.empty M.empty [] [] []

--------------------------------------------------------------------------------
-- Language Loading
--------------------------------------------------------------------------------

loadLang :: [LegoDecl] -> Either String CompiledLang
loadLang decls = loadLangWithMap (buildLangMap decls) decls

loadLangFile :: FilePath -> IO (Either String CompiledLang)
loadLangFile path = loadLangWithImports path

-- | Load a language file with import resolution
-- 
-- Import resolution follows the same pattern as .phi files:
--   1. First check intra-file definitions (lang Name := ...)
--   2. Then resolve external imports from files in same directory
--   3. Candidates: dir/Name.lego, dir/name.lego
--
-- This is a pushout: CurrentLang ⊔ ImportedLang
loadLangWithImports :: FilePath -> IO (Either String CompiledLang)
loadLangWithImports path = loadLangWithImportsAndCache path S.empty

-- | Load with import resolution and cycle detection
--
-- Strategy: Two-phase loading
--   Phase 1: Resolve external imports (top-level `import X`) from files
--   Phase 2: Process declarations with resolved imports in scope
--
-- This ensures that when `lang Foo := Bar + Baz` is processed,
-- Bar and Baz are already available (either from langMap or resolved imports)
--
-- IMPORTANT: The current file's base name and all locally defined lang names
-- are added to the visited set to prevent circular imports when a file
-- contains `lang Foo := import Foo` patterns.
loadLangWithImportsAndCache :: FilePath -> S.Set String -> IO (Either String CompiledLang)
loadLangWithImportsAndCache path visited = do
  content <- readFile path
  case parseLegoFile content of
    Left err -> return (Left err)
    Right decls -> do
      let dir = takeDirectory srcPath
          srcPath = path
          -- Add current file's base name to visited to prevent self-imports
          currentName = takeBaseName path
          -- Also add all locally defined lang names
          localLangs = M.keysSet (buildLangMap decls)
          -- Combined visited set includes file name and local definitions
          visitedWithLocal = S.insert currentName $ S.union visited localLangs
      -- Phase 1: Collect and resolve all top-level imports
      let externalImports = collectTopLevelImports decls
      let langMap = buildLangMap decls
      -- Filter out imports that can be resolved locally
      let externalOnly = filter (`S.notMember` localLangs) externalImports
      resolvedResult <- resolveExternalImportsPhase dir visitedWithLocal externalOnly
      case resolvedResult of
        Left err -> return (Left err)
        Right resolved -> do
          -- Phase 2: Process declarations with resolved imports in scope
          -- NOTE: We do NOT add resolved imports to langMap - they go to resolvedMap
          -- This ensures that external imports use the actual CompiledLang, not empty bodies
          case loadLangWithMapAndResolved langMap resolved decls of
            Left err -> return (Left err)
            Right cl -> return (Right cl)

-- | Collect ALL import names from declarations (including inside lang bodies and parents)
-- This ensures we resolve external dependencies before processing
collectTopLevelImports :: [LegoDecl] -> [String]
collectTopLevelImports = foldr go []
  where
    go (DImport name) acc = name : acc
    go (DLang _ parents body) acc = parents ++ collectTopLevelImports body ++ acc
    go _ acc = acc

-- | Resolve external imports from files (Phase 1)
-- Uses the Registry for package-aware resolution
resolveExternalImportsPhase :: FilePath -> S.Set String -> [String] -> IO (Either String [CompiledLang])
resolveExternalImportsPhase _ _ [] = return (Right [])
resolveExternalImportsPhase dir visited imports = do
  -- Deduplicate imports
  let uniqueImports = S.toList (S.fromList imports)
  -- Build resolve context
  let currentPkg = R.pathToPackage dir
      ctx = R.ResolveContext
        { R.rcCurrentPkg = currentPkg
        , R.rcCurrentDir = dir
        , R.rcRegistry = R.emptyRegistry  -- TODO: use global registry
        , R.rcVisited = visited
        , R.rcLocalLangs = S.empty  -- filled in by caller
        }
  results <- mapM (resolveImportWithRegistry ctx) uniqueImports
  return (sequence results)

-- | Resolve a single import using the Registry
-- 
-- Resolution order:
--   1. Registry lookup (qualified or short name)
--   2. Known roots: prelude/, examples/, phi/
--   3. Current directory and siblings
--   4. Working directory
resolveImportWithRegistry :: R.ResolveContext -> String -> IO (Either String CompiledLang)
resolveImportWithRegistry ctx name
  | name `S.member` R.rcVisited ctx = 
      return (Left $ "Circular import detected: " ++ name)
  | otherwise = do
      -- Try registry-based resolution first
      result <- R.resolveImport ctx name
      case result of
        Left err -> return (Left err)
        Right (Nothing, _qname) -> 
          -- Local definition, shouldn't happen here
          return (Left $ "Import " ++ name ++ " resolved to local but no file")
        Right (Just path, _qname) -> do
          let newVisited = S.insert name (R.rcVisited ctx)
          loadLangWithImportsAndCache path newVisited

-- | Build a map of lang name -> declarations for intra-file imports
buildLangMap :: [LegoDecl] -> M.Map String [LegoDecl]
buildLangMap = go M.empty
  where
    go m [] = m
    go m (DLang name _parents body : rest) = go (M.insert name body m) rest
    go m (_ : rest) = go m rest

-- | Build a map of resolved import name -> CompiledLang
buildResolvedMap :: [CompiledLang] -> M.Map String CompiledLang
buildResolvedMap = M.fromList . map (\cl -> (clName cl, cl))

-- | Load with intra-file import resolution (for standalone loading)
loadLangWithMap :: M.Map String [LegoDecl] -> [LegoDecl] -> Either String CompiledLang
loadLangWithMap langMap decls = loadLangWithMapAndResolved langMap [] decls

-- | Load with both langMap and pre-resolved external imports
loadLangWithMapAndResolved :: M.Map String [LegoDecl] -> [CompiledLang] -> [LegoDecl] -> Either String CompiledLang
loadLangWithMapAndResolved langMap resolved decls = 
  let resolvedMap = buildResolvedMap resolved
  in foldM (processDeclWithMapAndResolved langMap resolvedMap) (emptyCompiled "unnamed") decls

processDeclWithMapAndResolved :: M.Map String [LegoDecl] -> M.Map String CompiledLang -> CompiledLang -> LegoDecl -> Either String CompiledLang
processDeclWithMapAndResolved langMap resolvedMap cl (DLang name parents body) = do
  -- lang Name (Parents) := body
  -- Parents are explicitly included in the pushout
  parentLangs <- mapM (lookupLang langMap resolvedMap) parents
  let base = foldl poCompiledLang (emptyCompiled name) parentLangs
  -- Then process body on top of parents
  inner <- loadLangWithMapAndResolved langMap (M.elems resolvedMap) body
  Right $ (poCompiledLang cl (poCompiledLang base inner)) { clName = name }
processDeclWithMapAndResolved _ _ cl (DImport name) = 
  -- import L - makes L available in scope but does NOT pushout
  -- The actual resolution happens via resolvedMap passed to loadLangWithMapAndResolved
  -- We just record that this import exists
  Right $ cl { clImports = clImports cl ++ [name] }
processDeclWithMapAndResolved langMap resolvedMap cl (DPushout name1 name2) = do
  -- Explicit pushout: L1 ⊔ L2
  l1 <- lookupLang langMap resolvedMap name1
  l2 <- lookupLang langMap resolvedMap name2
  Right $ poCompiledLang cl (poCompiledLang l1 l2)
processDeclWithMapAndResolved _ _ cl (DVocab kws syms) =
  Right $ cl { clVocab = S.union (clVocab cl) (S.fromList (kws ++ syms)) }
processDeclWithMapAndResolved _ _ cl (DGrammar name g) =
  -- Auto-extract vocabulary from grammar literals
  let vocab = S.fromList (collectLiterals g)
  in Right $ cl { clGrammar = M.insert name g (clGrammar cl)
                , clVocab = S.union (clVocab cl) vocab }
processDeclWithMapAndResolved _ _ cl (DRule rule) =
  Right $ cl { clRules = clRules cl ++ [rule] }
processDeclWithMapAndResolved _ _ cl (DDef name term) =
  -- Desugar def to rule: def f = \x. body => (f $x) ~> body
  let rule = defToRule name term
  in Right $ cl { clRules = clRules cl ++ [rule] }
processDeclWithMapAndResolved _ _ cl (DType _) =
  Right cl  -- type rules handled separately
processDeclWithMapAndResolved _ _ cl (DTest test) =
  Right $ cl { clTests = clTests cl ++ [test] }
processDeclWithMapAndResolved _ _ cl (DTestSpec spec) =
  -- Convert TestSpec to legacy Test for now (enhanced execution handled elsewhere)
  let legacyTest = case tsExpect spec of
        ExpectNorm expected -> Test (tsName spec) (tsInput spec) expected
        ExpectParse -> Test (tsName spec) (tsInput spec) (tsInput spec)
        ExpectNoChange -> Test (tsName spec) (tsInput spec) (tsInput spec)
        _ -> Test (tsName spec) (tsInput spec) (TmVar "_")
  in Right $ cl { clTests = clTests cl ++ [legacyTest] }
processDeclWithMapAndResolved langMap resolvedMap cl (DPiece name parents body) = do
  -- piece Name is Parents with: body
  -- First load all parents and compose them
  parentLangs <- mapM (lookupLang langMap resolvedMap) parents
  let base = foldl poCompiledLang (emptyCompiled name) parentLangs
  -- Then load body on top of parents
  inner <- loadLangWithMapAndResolved langMap (M.elems resolvedMap) body
  let piece = (poCompiledLang base inner) { clName = name }
  -- Add piece to the current language AND to the langMap for future references
  Right $ poCompiledLang cl piece

-- | Look up a language by name in langMap or resolvedMap
lookupLang :: M.Map String [LegoDecl] -> M.Map String CompiledLang -> String -> Either String CompiledLang
lookupLang langMap resolvedMap name = 
  case M.lookup name langMap of
    Just body -> loadLangWithMapAndResolved langMap (M.elems resolvedMap) body
    Nothing -> case M.lookup name resolvedMap of
      Just cl -> Right cl
      Nothing -> Right $ (emptyCompiled name) { clImports = [name] }

-- | Pushout of compiled languages
--
-- This IS the pushout operation (poLang) at runtime:
--   L1 ⊔ L2 = (vocab1 ∪ vocab2, grammar1 ∪ grammar2, rules1 ++ rules2)
--
-- The import directive is syntactic sugar for pushout:
--   import L  ≡  CurrentLang ⊔ L
--
-- Laws (inherited from poLang):
--   Identity:     L ⊔ ∅ = L
--   Commutativity: L1 ⊔ L2 ≅ L2 ⊔ L1 (up to ordering)
--   Associativity: (L1 ⊔ L2) ⊔ L3 = L1 ⊔ (L2 ⊔ L3)
poCompiledLang :: CompiledLang -> CompiledLang -> CompiledLang
poCompiledLang cl1 cl2 = CompiledLang
  { clName = clName cl1
  , clVocab = S.union (clVocab cl1) (clVocab cl2)
  , clGrammar = M.union (clGrammar cl1) (clGrammar cl2)
  , clRules = clRules cl1 ++ clRules cl2
  , clTests = clTests cl1 ++ clTests cl2
  , clImports = clImports cl1 ++ clImports cl2
  }

-- | Legacy alias for backwards compatibility
mergeLang :: CompiledLang -> CompiledLang -> CompiledLang
mergeLang = poCompiledLang

foldM :: Monad m => (b -> a -> m b) -> b -> [a] -> m b
foldM _ z [] = return z
foldM f z (x:xs) = f z x >>= \z' -> foldM f z' xs

--------------------------------------------------------------------------------
-- Evaluation
--------------------------------------------------------------------------------

-- | Evaluate with grammar context for parseWith/printWith builtins
evalLego :: CompiledLang -> Term -> Term
evalLego cl = normalizeWithGrammar (clGrammar cl) (clRules cl)

-- | Normalize with grammar context for parseWith/printWith
normalizeWithGrammar :: M.Map String (GrammarExpr ()) -> [Rule] -> Term -> Term
normalizeWithGrammar grammar rules = go (1000 :: Int)  -- fuel
  where
    go :: Int -> Term -> Term
    go 0 t = t  -- out of fuel
    go n t = 
      -- First, normalize subterms
      let t' = normSub t
      in case step t' of
        Nothing -> t'
        Just t'' -> go (n-1) t''
    
    normSub :: Term -> Term
    normSub (TmCon c args) = TmCon c (map (normalizeWithGrammar grammar rules) args)
    normSub t = t
    
    step :: Term -> Maybe Term
    step t = grammarBuiltin t <|> builtinStep t <|> foldr (<|>) Nothing (map (tryRule t) rules)
    
    tryRule :: Term -> Rule -> Maybe Term
    tryRule t rule = do
      binds <- matchPat (rulePattern rule) t
      return $ applyTemplate binds (ruleTemplate rule)
    
    -- | Grammar-aware builtins: parse, print, parseWith, printWith
    grammarBuiltin :: Term -> Maybe Term
    -- parse: (parse PieceName "input") or (parse "PieceName" "input") → AST
    grammarBuiltin (TmCon "parse" [TmLit pieceName, TmLit input]) =
      parseWithPiece grammar pieceName input
    grammarBuiltin (TmCon "parse" [TmVar pieceName, TmLit input]) =
      parseWithPiece grammar pieceName input
    -- parseWith: (parseWith "PieceName" "input string") → AST
    grammarBuiltin (TmCon "parseWith" [TmVar pieceName, TmLit input]) =
      parseWithPiece grammar pieceName input
    grammarBuiltin (TmCon "parseWith" [TmLit pieceName, TmLit input]) =
      parseWithPiece grammar pieceName input
    -- print: (print PieceName ast) → "output"
    grammarBuiltin (TmCon "print" [TmLit pieceName, ast]) =
      printWithPiece grammar pieceName ast
    grammarBuiltin (TmCon "print" [TmVar pieceName, ast]) =
      printWithPiece grammar pieceName ast
    -- printWith: (printWith "PieceName" ast) → "output string"
    grammarBuiltin (TmCon "printWith" [TmVar pieceName, ast]) =
      printWithPiece grammar pieceName ast
    grammarBuiltin (TmCon "printWith" [TmLit pieceName, ast]) =
      printWithPiece grammar pieceName ast
    grammarBuiltin _ = Nothing

-- | Run tests with grammar context (for parse/print builtins)
runTestsWithGrammar :: M.Map String (GrammarExpr ()) -> [Rule] -> [Test] -> [TestResult]
runTestsWithGrammar grammar rules = map runOne
  where
    runOne test
      -- Parse-only test: input == expected, just check parsing succeeded
      | testInput test == testExpected test = Pass (testName test)
      -- Eval test: normalize and compare against expected
      | otherwise =
          let actual = normalizeWithGrammar grammar rules (testInput test)
              expected = testExpected test
          in case matchTerms expected actual of
               Just _ -> Pass (testName test)
               Nothing -> Fail (testName test) expected actual

-- | Parse input using a named grammar piece
parseWithPiece :: M.Map String (GrammarExpr ()) -> String -> String -> Maybe Term
parseWithPiece grammar pieceName input = do
  -- Look up entry point: 
  --   1. PieceName.file, PieceName.expr (explicit entry points)
  --   2. PieceName (exact match)
  --   3. PieceName.* (first production in piece, e.g. Bool.bool)
  let explicitPoints = [pieceName ++ ".file", pieceName ++ ".expr", pieceName]
  let piecePrefix = pieceName ++ "."
  -- Find all grammar names starting with PieceName.
  let pieceProductions = filter (piecePrefix `isPrefixOf`) (M.keys grammar)
  let allCandidates = explicitPoints ++ pieceProductions
  entryName <- foldr (<|>) Nothing (map (\n -> if M.member n grammar then Just n else Nothing) allCandidates)
  _ <- M.lookup entryName grammar  -- Verify grammar exists
  -- Run with GRef to get proper top-level wrapping from runGrammarWithEnv
  case runGrammarWithEnv grammar (GRef entryName) (tokenize input) of
    Just (term, _) -> Just term  -- Already wrapped by GRef handler
    Nothing -> Nothing
  where
    isPrefixOf p s = take (length p) s == p

-- | Print AST using a named grammar piece
printWithPiece :: M.Map String (GrammarExpr ()) -> String -> Term -> Maybe Term
printWithPiece grammar pieceName ast = do
  -- Look up entry point (same logic as parseWithPiece)
  let explicitPoints = [pieceName ++ ".file", pieceName ++ ".expr", pieceName]
  let piecePrefix = pieceName ++ "."
  let pieceProductions = filter (piecePrefix `isPrefixOf`) (M.keys grammar)
  let allCandidates = explicitPoints ++ pieceProductions
  entryName <- foldr (<|>) Nothing (map (\n -> if M.member n grammar then Just n else Nothing) allCandidates)
  -- Unwrap if the ast is wrapped in a production name matching entry point
  let unwrapped = case ast of
        TmCon c [inner] | c `elem` ["file", "expr"] -> inner
        _ -> ast
  -- Run our env-aware printer with GRef to handle constructor unwrapping
  result <- runPrintWithEnv grammar (GRef entryName) unwrapped
  Just $ TmLit result
  where
    isPrefixOf p s = take (length p) s == p

-- | Print term using grammar with full environment for GRef resolution
runPrintWithEnv :: M.Map String (GrammarExpr ()) -> GrammarExpr () -> Term -> Maybe String
runPrintWithEnv env = go
  where
    go :: GrammarExpr () -> Term -> Maybe String
    go GEmpty _ = Just ""
    -- Content literal: must match the term (for alternation choices like "true"|"false")
    go (GLit s) t = case t of
      TmLit s' | s == s' -> Just s
      TmCon c [] | c == s -> Just s  -- constructor as literal
      _ -> Nothing  -- strict: content must match
    -- Syntax literal: always emit (for parens, operators, etc.)
    go (GSyntax s) _ = Just s
    go (GSeq g1 g2) t = do
      s1 <- go g1 t
      s2 <- go g2 t
      Just $ s1 ++ (if null s1 || null s2 then "" else " ") ++ s2
    -- For alternation, try to find the alternative that matches the term
    go (GAlt g1 g2) t = go g1 t <|> go g2 t
    go (GStar g) t = case t of
      TmCon "nil" [] -> Just ""
      TmCon "cons" [h, tl] -> do
        s1 <- go g h
        s2 <- go (GStar g) tl
        Just $ s1 ++ (if null s2 then "" else "\n") ++ s2
      _ -> Nothing  -- not a list
    go (GRef name) t = case M.lookup name env of
      Just g -> do
        -- Match production name with term constructor
        let prodName = shortName name
        case t of
          TmCon c args | c == prodName -> 
            -- Print constructor args using grammar seq
            goSeqArgs g args
          _ -> go g t  -- try anyway
      Nothing -> Nothing
    go (GBind _x g) t = goBind t <|> go g t
    go (GVar _x) (TmVar v) = Just v
    go (GVar _x) (TmLit s) = Just s
    go GAny t = goBind t
    go (GNode con gs) (TmCon c args) | c == con =
      let pairs = zip gs (args ++ repeat (TmCon "unit" []))
      in fmap unwords $ sequence [go g t | (g, t) <- pairs]
    go _ _ = Nothing
    
    goBind t = case t of
      TmVar v -> Just v
      TmLit s -> Just s
      TmCon c [] -> Just c
      _ -> Nothing
    
    -- Print constructor args matching grammar sequence structure
    goSeqArgs :: GrammarExpr () -> [Term] -> Maybe String
    goSeqArgs GEmpty [] = Just ""
    goSeqArgs (GLit s) [] = Just s
    goSeqArgs (GLit s) _ts = Just s  -- content literal doesn't consume args
    goSeqArgs (GSyntax s) ts = Just s <* Just ts  -- syntax literal always emits, preserves args
    goSeqArgs (GSeq g1 g2) ts = do
      -- Try to print first part, collect remaining args
      let (s1, rest) = printPart g1 ts
      s1' <- s1
      s2 <- goSeqArgs g2 rest
      Just $ s1' ++ (if null s1' || null s2 then "" else " ") ++ s2
    goSeqArgs g [t] = go g t
    goSeqArgs g [] = go g (TmCon "unit" [])
    goSeqArgs _g _ts = Nothing  -- mismatch
    
    -- Print one grammar part, return (result, remaining args)
    printPart :: GrammarExpr () -> [Term] -> (Maybe String, [Term])
    printPart (GLit s) ts = (Just s, ts)  -- content literal doesn't consume
    printPart (GSyntax s) ts = (Just s, ts)  -- syntax literal doesn't consume
    printPart (GBind _ _) (t:ts) = (goBind t, ts)
    printPart (GRef name) (t:ts) = (go (GRef name) t, ts)
    printPart (GStar g) (t:ts) = (go (GStar g) t, ts)  -- star consumes one arg (the list)
    printPart (GStar _) [] = (Nothing, [])
    printPart _g [] = (Nothing, [])
    printPart g (t:ts) = (go g t, ts)  -- default: consume one arg

    shortName :: String -> String
    shortName s = case break (== '.') s of
      (_, '.':rest) -> rest
      _ -> s

-- | Run grammar with full environment for recursive references
-- The production name becomes the AST node name
runGrammarWithEnv :: M.Map String (GrammarExpr ()) -> GrammarExpr () -> [Token] -> Maybe (Term, [Token])
runGrammarWithEnv env = goFuel 1000 S.empty  -- fuel to prevent infinite loops, empty set of seen productions
  where
    goFuel :: Int -> S.Set String -> GrammarExpr () -> [Token] -> Maybe (Term, [Token])
    goFuel 0 _ _ _ = Nothing  -- out of fuel
    goFuel _ _ GEmpty toks = Just (TmCon "unit" [], toks)
    -- Content literal: matches identifier/keyword
    goFuel _ _ (GLit s) toks = matchLit s toks
    -- Syntax literal: matches symbol/keyword
    goFuel _ _ (GSyntax s) toks = matchSyntax s toks
    goFuel n _ (GNode con gs) toks = do
      (args, rest) <- goManyFuel n S.empty gs toks
      Just (TmCon con args, rest)
    goFuel n seen (GSeq g1 g2) toks = do
      (t1, rest) <- goFuel (n-1) seen g1 toks
      (t2, rest') <- goFuel (n-1) seen g2 rest
      -- Combine sequence elements
      let result = combineSeq t1 t2
      Just (result, rest')
    goFuel n seen (GAlt g1 g2) toks = goFuel n seen g1 toks <|> goFuel n seen g2 toks
    goFuel n seen (GStar g) toks = 
      let toks' = skipWS toks  -- skip whitespace before each iteration
      in case goFuel (n-1) seen g toks' of
        Nothing -> Just (TmCon "nil" [], toks')
        Just (_t, rest) | rest == toks' -> Just (TmCon "nil" [], toks')  -- no progress
        Just (t, rest) -> do
          (restList, rest') <- goFuel (n-1) seen (GStar g) rest
          -- Proper cons: (cons head tail) where tail is nil or another cons
          Just (TmCon "cons" [t, restList], rest')
    goFuel n seen (GRef name) toks = 
      case M.lookup name env of
        Just g -> do
          let prodName = shortName name
          let seen' = S.insert prodName seen
          (term, rest) <- goFuel (n-1) seen' g toks
          -- Wrap if we haven't seen this production before
          if S.member prodName seen
            then Just (term, rest)  -- Already seen - don't wrap (recursion)
            else Just (TmCon prodName (flattenSeq term), rest)  -- First time - wrap
        Nothing -> Nothing  -- Unknown reference fails
    goFuel n seen (GBind _x g) toks = do
      (term, rest) <- goFuel (n-1) seen g toks
      Just (term, rest)  -- Bindings just capture, don't change structure
    goFuel _ _ (GVar _x) toks = Just (TmVar "_", toks)
    goFuel _ _ GAny (t:rest) = Just (tokenToTerm t, rest)
    goFuel n seen (GRec _x g) toks = goFuel (n-1) seen g toks  -- Simple recursion via env lookup
    goFuel _ _ _ _ = Nothing
    
    goManyFuel :: Int -> S.Set String -> [GrammarExpr ()] -> [Token] -> Maybe ([Term], [Token])
    goManyFuel _ _ [] toks = Just ([], toks)
    goManyFuel n seen (g:gs) toks = do
      (t, rest) <- goFuel (n-1) seen g toks
      (ts, rest') <- goManyFuel (n-1) seen gs rest
      Just (t:ts, rest')
    
    -- Match syntax literal (symbols, keywords, identifiers) - produces TmSyntax
    -- GSyntax can match any token type - the distinction is that it's not preserved
    matchSyntax :: String -> [Token] -> Maybe (Term, [Token])
    matchSyntax s (TSym x : rest) | x == s = Just (TmSyntax s, rest)
    matchSyntax s (TKeyword x : rest) | x == s = Just (TmSyntax s, rest)
    matchSyntax s (TIdent x : rest) | x == s = Just (TmSyntax s, rest)
    matchSyntax _ _ = Nothing

    -- Get short name: "PhiGrammar.pkg" → "pkg"
    shortName :: String -> String
    shortName s = case break (== '.') s of
      (_, '.':rest) -> rest
      _ -> s
    
    -- Combine sequence elements
    combineSeq :: Term -> Term -> Term
    combineSeq (TmCon "unit" []) t = t
    combineSeq t (TmCon "unit" []) = t
    combineSeq (TmSyntax _) t = t  -- Syntax doesn't contribute to structure
    combineSeq t (TmSyntax _) = t
    combineSeq t1 t2 = TmCon "seq" [t1, t2]
    
    -- Flatten a seq into a list of terms
    -- TmSyntax (from GSyntax) is dropped - pure syntax
    -- TmLit (from GLit) is kept - content literals
    flattenSeq :: Term -> [Term]
    flattenSeq (TmCon "seq" [t1, t2]) = flattenSeq t1 ++ flattenSeq t2
    flattenSeq (TmCon "unit" []) = []
    flattenSeq (TmSyntax _) = []  -- Skip syntax (from GSyntax)
    flattenSeq t = [t]  -- Keep TmLit, TmCon, TmVar
    
    -- Skip whitespace tokens (newlines, indents)
    skipWS :: [Token] -> [Token]
    skipWS (TNewline : rest) = skipWS rest
    skipWS (TIndent _ : rest) = skipWS rest
    skipWS toks = toks
    
    -- Match a literal that may span multiple tokens (e.g., "with:" → "with" ":")
    matchLit :: String -> [Token] -> Maybe (Term, [Token])
    matchLit s toks = 
      -- Try single-token match first
      case toks of
        (TIdent x : rest) | x == s -> Just (TmLit s, rest)
        (TKeyword k : rest) | k == s -> Just (TmLit s, rest)
        (TSym sym : rest) | sym == s -> Just (TmLit s, rest)
        (TString str : rest) | str == s -> Just (TmLit s, rest)
        _ -> 
          -- Try multi-token match: tokenize literal and match sequence
          let litToks = tokenize s
              cleanLitToks = filter isContentToken litToks
          in if null cleanLitToks || length cleanLitToks == 1
             then Nothing  -- Already tried single token
             else matchToks cleanLitToks toks
    
    -- Match a sequence of tokens against input
    matchToks :: [Token] -> [Token] -> Maybe (Term, [Token])
    matchToks [] rest = Just (TmCon "unit" [], rest)
    matchToks (lt:lts) (t:ts) | tokEq lt t = matchToks lts ts
    matchToks _ _ = Nothing
    
    tokEq (TIdent a) (TIdent b) = a == b
    tokEq (TKeyword a) (TKeyword b) = a == b
    tokEq (TSym a) (TSym b) = a == b
    tokEq (TString a) (TString b) = a == b
    tokEq _ _ = False
    
    isContentToken TNewline = False
    isContentToken (TIndent _) = False
    isContentToken _ = True

eval :: CompiledLang -> String -> Either String Term
eval cl input = do
  term <- parseTerm input
  return $ evalLego cl term

--------------------------------------------------------------------------------
-- | Parsing with Grammar (Bidirectional)
--------------------------------------------------------------------------------

parse :: CompiledLang -> String -> Either String Term
parse cl input = 
  case M.lookup "expr" (clGrammar cl) <|> M.lookup "Expr" (clGrammar cl) of
    Nothing -> parseTerm input  -- fallback to S-expr
    Just g -> parseWithBiGrammar g (words input)

-- | Parse using bidirectional grammar in Parse mode
parseWithBiGrammar :: GrammarExpr () -> [String] -> Either String Term
parseWithBiGrammar g toks = 
  case biParse g toks of
    ((term, []):_) -> Right term
    ((_term, rest):_) -> Left $ "Trailing: " ++ unwords rest
    [] -> Left "Grammar parse failed"

tokenToTerm :: Token -> Term
tokenToTerm (TIdent x) = TmVar x
tokenToTerm (TKeyword k) = TmVar k  -- Keywords are also identifiers when captured
tokenToTerm (TString s) = TmLit s
tokenToTerm (TSym s) = TmLit s
tokenToTerm _ = TmCon "unknown" []

--------------------------------------------------------------------------------
-- Unparsing (Term → String) - Bidirectional
--------------------------------------------------------------------------------

-- | Unparse using bidirectional grammar in Print mode
unparse :: CompiledLang -> Term -> String
unparse cl term = 
  case M.lookup "expr" (clGrammar cl) <|> M.lookup "Expr" (clGrammar cl) of
    Nothing -> unparseTerm term  -- fallback to S-expr
    Just g -> unwords (biPrint g term M.empty)

unparseTerm :: Term -> String
unparseTerm (TmVar x) = x
unparseTerm (TmLit s) = s
unparseTerm (TmSyntax _) = ""  -- Syntax is invisible
unparseTerm (TmReserved s) = s
unparseTerm (TmRegex s) = "/" ++ s ++ "/"
unparseTerm (TmChar s) = "'" ++ s ++ "'"
unparseTerm (TmCon c []) = c
unparseTerm (TmCon c args) = "(" ++ c ++ " " ++ unwords (map unparseTerm args) ++ ")"
-- Cubical primitives
unparseTerm TmInterval = "I"
unparseTerm TmI0 = "i0"
unparseTerm TmI1 = "i1"
unparseTerm (TmPathType a x y) = "(Path " ++ unparseTerm a ++ " " ++ unparseTerm x ++ " " ++ unparseTerm y ++ ")"
unparseTerm (TmPathAbs i e) = "(λ" ++ i ++ ". " ++ unparseTerm e ++ ")"
unparseTerm (TmPathApp p r) = "(" ++ unparseTerm p ++ " @ " ++ unparseTerm r ++ ")"
-- Composition operations
unparseTerm (TmComp a phi u a0) = "(comp " ++ unparseTerm a ++ " " ++ unparseTerm phi ++ " " ++ unparseTerm u ++ " " ++ unparseTerm a0 ++ ")"
unparseTerm (TmHComp a phi u a0) = "(hcomp " ++ unparseTerm a ++ " " ++ unparseTerm phi ++ " " ++ unparseTerm u ++ " " ++ unparseTerm a0 ++ ")"
unparseTerm (TmTransp a phi a0) = "(transp " ++ unparseTerm a ++ " " ++ unparseTerm phi ++ " " ++ unparseTerm a0 ++ ")"
