{-# LANGUAGE PatternSynonyms #-}
-- | Grammar-Based Parser: Parsing via grammar interpretation
--
-- Grammar is EXPRESSION (data), not PROCEDURE (code).
-- Grammar is loaded from Grammar.sexpr (via GrammarDef).
--
module Lego.GrammarParser
  ( parseLegoFile
  , LegoDecl(..)
  ) where

import Lego (Term, pattern TmVar, pattern TmCon, pattern TmLit,
             pattern GRef, pattern GLit, pattern GAlt, pattern GSeq, 
             pattern GStar, pattern GBind, pattern GAny, pattern GNode, pattern GEmpty,
             pattern GCut,
             GrammarExpr, LegoDecl(..), Rule(..), RuleDir(..), Test(..), Law(..),
             TestSpec(..), TestExpect(..), defaultOpts,
             Mode(..), BiState(..))
import Lego.Token (Token(..), TokenInfo(..), tokenizeWithInfo)
import Lego.GrammarDef (legoGrammar)
import Lego.GrammarInterp (runGrammar)
import qualified Data.Map as M
import qualified Data.Set as S
import Data.Maybe (mapMaybe)

--------------------------------------------------------------------------------
-- File Parsing
--------------------------------------------------------------------------------

-- | Parse a complete .lego file
parseLegoFile :: String -> Either String [LegoDecl]
parseLegoFile content = 
  let tokInfos = tokenizeWithInfo content
      toks = map tiToken tokInfos
      posMap = [(tiToken ti, tiLine ti, tiColumn ti) | ti <- tokInfos]
  in case parseFileG toks of
       Just (decls, []) -> Right decls
       Just (_, rest) -> Left $ formatError posMap rest
       Nothing -> Left $ formatError posMap toks

-- | Run File.legoFile grammar
parseFileG :: [Token] -> Maybe ([LegoDecl], [Token])
parseFileG toks = 
  case M.lookup "File.legoFile" legoGrammar of
    Nothing -> Nothing
    Just g ->
      let st0 = BiState toks [M.empty] Nothing Parse legoGrammar M.empty S.empty
      in case runGrammar g st0 of
           [] -> Nothing
           (st:_) -> 
             let decls = case bsTerm st of
                   Just t -> extractDecls t
                   Nothing -> []
             in Just (decls, bsTokens st)

--------------------------------------------------------------------------------
-- Term → LegoDecl conversion
--------------------------------------------------------------------------------

extractDecls :: Term -> [LegoDecl]
extractDecls (TmCon "seq" ts) = concatMap extractDecls ts
extractDecls (TmCon "decl" (d:_)) = extractDecls d
extractDecls t = mapMaybe termToDecl [t]

termToDecl :: Term -> Maybe LegoDecl
-- Import
termToDecl (TmCon "DImport" [TmVar name]) = Just $ DImport name
termToDecl (TmCon "DImport" [TmLit name]) = Just $ DImport name
-- Def
termToDecl (TmCon "DDef" [TmVar name, value]) = Just $ DDef name value
termToDecl (TmCon "DDef" [TmLit name, value]) = Just $ DDef name value
-- Test (basic) - filter out unit placeholders from empty grammar alternatives
termToDecl (TmCon "DTest" (TmLit name : input : rest)) = 
  -- Filter out unit placeholders produced by (alt ... (empty))
  let nonUnit = filter (/= TmCon "unit" []) rest
  in case nonUnit of
    [] -> Just $ DTest $ Test name input input  -- parse-only test
    [expected] -> Just $ DTest $ Test name input expected  -- eval test
    (expected : opts) -> 
      let baseTest = Test name input expected
      in Just $ DTestSpec $ parseTestOpts baseTest (TmCon "opts" opts)
-- Rule
termToDecl (TmCon "DRule" [TmVar name, pat, tmpl]) = 
  Just $ DRule $ Rule name pat tmpl Nothing Forward
termToDecl (TmCon "DRule" [TmLit name, pat, tmpl]) = 
  Just $ DRule $ Rule name pat tmpl Nothing Forward
-- Rule stub (empty)
termToDecl (TmCon "DRuleStub" [TmVar name]) = 
  Just $ DRule $ Rule name (TmLit "") (TmLit "") Nothing Forward
termToDecl (TmCon "DRuleStub" [TmLit name]) = 
  Just $ DRule $ Rule name (TmLit "") (TmLit "") Nothing Forward
-- Lang
termToDecl (TmCon "DLang" [TmVar name, parentsTerm, bodyTerm]) = 
  Just $ DLang name (extractNames parentsTerm) (extractBody bodyTerm)
termToDecl (TmCon "DLang" [TmLit name, parentsTerm, bodyTerm]) = 
  Just $ DLang name (extractNames parentsTerm) (extractBody bodyTerm)
-- Piece
termToDecl (TmCon "DPiece" (TmVar name : rest)) = 
  Just $ DPiece name [] (extractProds name rest)
termToDecl (TmCon "DPiece" (TmLit name : rest)) = 
  Just $ DPiece name [] (extractProds name rest)
-- Grammar production
termToDecl (TmCon "DGrammar" [TmVar name, gramTerm]) = 
  Just $ DGrammar name (termToGrammar gramTerm)
termToDecl (TmCon "DGrammar" [TmLit name, gramTerm]) = 
  Just $ DGrammar name (termToGrammar gramTerm)
-- Section marker (skip)
termToDecl (TmCon "section" _) = Nothing
-- Comment (skip)
termToDecl (TmCon "comment" _) = Nothing
-- Law (4 children: name, lhs, op, rhs - but we ignore the op for now)
termToDecl (TmCon "DLaw" [TmLit name, lhs, _, rhs]) =
  Just $ DLaw $ Law name lhs rhs
termToDecl (TmCon "DLaw" [TmVar name, lhs, _, rhs]) =
  Just $ DLaw $ Law name lhs rhs
-- Alternate: 3 children if op is not captured
termToDecl (TmCon "DLaw" [TmLit name, lhs, rhs]) =
  Just $ DLaw $ Law name lhs rhs
termToDecl (TmCon "DLaw" [TmVar name, lhs, rhs]) =
  Just $ DLaw $ Law name lhs rhs
-- Inherit
termToDecl (TmCon "DInherit" [TmVar qual]) =
  Just $ DInherit qual
termToDecl (TmCon "DInherit" [TmLit qual]) =
  Just $ DInherit qual
termToDecl (TmCon "DInherit" args) =
  Just $ DInherit (intercalateQual args)
-- Autocut
termToDecl (TmCon "DAutocut" [TmVar name]) =
  Just $ DAutocut name
termToDecl (TmCon "DAutocut" [TmLit name]) =
  Just $ DAutocut name
-- Unknown
termToDecl _ = Nothing

-- | Parse test options from AST term
parseTestOpts :: Test -> Term -> TestSpec
parseTestOpts (Test name input expected) optsTerm = 
  let baseSpec = TestSpec name input (ExpectNorm expected) defaultOpts
  in foldr applyOpt baseSpec (extractOpts optsTerm)
  where
    extractOpts (TmCon "opts" opts) = opts
    extractOpts (TmCon "seq" opts) = opts
    extractOpts t = [t]
    
    applyOpt (TmCon "via" [TmVar rn]) spec = 
      spec { tsExpect = ExpectAnd (tsExpect spec) (ExpectViaRule rn) }
    applyOpt (TmCon "via" [TmLit rn]) spec = 
      spec { tsExpect = ExpectAnd (tsExpect spec) (ExpectViaRule rn) }
    applyOpt (TmCon "steps" [TmLit n]) spec = 
      case reads n of
        [(num, "")] -> spec { tsExpect = ExpectAnd (tsExpect spec) (ExpectSteps num) }
        _ -> spec
    applyOpt (TmCon "steps" [TmCon "num" [TmLit n]]) spec = 
      case reads n of
        [(num, "")] -> spec { tsExpect = ExpectAnd (tsExpect spec) (ExpectSteps num) }
        _ -> spec
    applyOpt (TmCon "error" [TmLit msg]) spec = 
      spec { tsExpect = ExpectError msg }
    applyOpt _ spec = spec

-- | Extract qualified name from nested terms
intercalateQual :: [Term] -> String
intercalateQual [] = ""
intercalateQual [TmVar s] = s
intercalateQual [TmLit s] = s
intercalateQual (TmVar s:rest) = s ++ "." ++ intercalateQual rest
intercalateQual (TmLit s:rest) = s ++ "." ++ intercalateQual rest
intercalateQual (_:rest) = intercalateQual rest

extractNames :: Term -> [String]
extractNames (TmCon "parents" children) = mapMaybe getName children
extractNames (TmCon "seq" children) = mapMaybe getName children
extractNames _ = []

getName :: Term -> Maybe String
getName (TmVar s) = Just s
getName (TmLit s) = Just s
getName _ = Nothing

extractBody :: Term -> [LegoDecl]
extractBody (TmCon "body" children) = concatMap extractBodyItem children
extractBody (TmCon "seq" children) = concatMap extractBodyItem children
extractBody t = extractBodyItem t

extractBodyItem :: Term -> [LegoDecl]
extractBodyItem (TmCon "seq" children) = concatMap extractBodyItem children
extractBodyItem (TmCon "item" (d:_)) = mapMaybe termToDecl [d]
extractBodyItem t = mapMaybe termToDecl [t]

extractProds :: String -> [Term] -> [LegoDecl]
extractProds pn = concatMap (extractPieceDecl pn)

-- | Extract a declaration from within a piece body
-- Handles grammar productions (qualified with piece name), rules, and tests
extractPieceDecl :: String -> Term -> [LegoDecl]
extractPieceDecl pn (TmCon "seq" ts) = concatMap (extractPieceDecl pn) ts
extractPieceDecl pn (TmCon "prodWrap" (d:_)) = extractPieceDecl pn d
-- Grammar productions get qualified: piece.prodName
extractPieceDecl pn (TmCon "DGrammar" [TmVar name, gramTerm]) = 
  [DGrammar (pn ++ "." ++ name) (termToGrammar gramTerm)]
extractPieceDecl pn (TmCon "DGrammar" [TmLit name, gramTerm]) = 
  [DGrammar (pn ++ "." ++ name) (termToGrammar gramTerm)]
-- Rules within pieces (not qualified - rules are global)
extractPieceDecl _ (TmCon "DRule" [TmVar name, pat, tmpl]) = 
  [DRule $ Rule name pat tmpl Nothing Forward]
extractPieceDecl _ (TmCon "DRule" [TmLit name, pat, tmpl]) = 
  [DRule $ Rule name pat tmpl Nothing Forward]
-- Tests within pieces
extractPieceDecl _ (TmCon "DTest" [TmLit name, input]) = 
  [DTest $ Test name input input]
extractPieceDecl _ (TmCon "DTest" [TmLit name, input, expected]) = 
  [DTest $ Test name input expected]
-- Defs within pieces
extractPieceDecl _ (TmCon "DDef" [TmVar name, value]) = 
  [DDef name value]
extractPieceDecl _ (TmCon "DDef" [TmLit name, value]) = 
  [DDef name value]
-- Laws within pieces (4 children: name, lhs, op, rhs)
extractPieceDecl _ (TmCon "DLaw" [TmLit name, lhs, _, rhs]) =
  [DLaw $ Law name lhs rhs]
extractPieceDecl _ (TmCon "DLaw" [TmVar name, lhs, _, rhs]) =
  [DLaw $ Law name lhs rhs]
-- Alternate: 3 children if op is not captured
extractPieceDecl _ (TmCon "DLaw" [TmLit name, lhs, rhs]) =
  [DLaw $ Law name lhs rhs]
extractPieceDecl _ (TmCon "DLaw" [TmVar name, lhs, rhs]) =
  [DLaw $ Law name lhs rhs]
-- Inherit within pieces
extractPieceDecl _ (TmCon "DInherit" [TmVar qual]) =
  [DInherit qual]
extractPieceDecl _ (TmCon "DInherit" [TmLit qual]) =
  [DInherit qual]
extractPieceDecl _ (TmCon "DInherit" args) =
  [DInherit (intercalateQual args)]
-- Autocut within pieces
extractPieceDecl _ (TmCon "DAutocut" [TmVar name]) =
  [DAutocut name]
extractPieceDecl _ (TmCon "DAutocut" [TmLit name]) =
  [DAutocut name]
extractPieceDecl _ _ = []

--------------------------------------------------------------------------------
-- Term → GrammarExpr conversion
--------------------------------------------------------------------------------

termToGrammar :: Term -> GrammarExpr ()
termToGrammar (TmVar s) = GRef s
termToGrammar (TmLit s) = GLit s
termToGrammar (TmCon "alt" [g1, _, g2]) = GAlt (termToGrammar g1) (termToGrammar g2)
termToGrammar (TmCon "alt" [g1, g2]) = GAlt (termToGrammar g1) (termToGrammar g2)
termToGrammar (TmCon "seq" [g1, g2]) = GSeq (termToGrammar g1) (termToGrammar g2)
termToGrammar (TmCon "seq" gs) = foldr GSeq GEmpty (map termToGrammar gs)
termToGrammar (TmCon "star" [g]) = GStar (termToGrammar g)
termToGrammar (TmCon "plus" [g]) = GSeq (termToGrammar g) (GStar (termToGrammar g))
termToGrammar (TmCon "opt" [g]) = GAlt (termToGrammar g) GEmpty
termToGrammar (TmCon "cut" [g]) = GCut (termToGrammar g)  -- !g cut syntax
termToGrammar (TmCon "bind" [TmVar x]) = GBind x GAny
termToGrammar (TmCon "bind" [TmLit x]) = GBind x GAny  -- $ "string" node annotation
termToGrammar (TmCon "special" [TmVar name]) = GNode name []
termToGrammar (TmCon "empty" []) = GEmpty
termToGrammar (TmCon "unit" []) = GEmpty
termToGrammar _ = GEmpty

--------------------------------------------------------------------------------
-- Error formatting
--------------------------------------------------------------------------------

formatError :: [(Token, Int, Int)] -> [Token] -> String
formatError posMap rest = 
  let pos = case rest of
        (t:_) -> case filter (\(tok,_,_) -> tok == t) posMap of
          ((_, ln, col):_) -> " at line " ++ show ln ++ ", column " ++ show col
          [] -> ""
        [] -> ""
      toks = take 5 $ filter significant rest
      preview = unwords $ map showTok toks
  in "Parse error" ++ pos ++ ": unexpected " ++ preview

significant :: Token -> Bool
significant TNewline = False
significant (TIndent _) = False
significant _ = True

showTok :: Token -> String
showTok (TKeyword k) = "'" ++ k ++ "'"
showTok (TIdent i) = "'" ++ i ++ "'"
showTok (TSym s) = "'" ++ s ++ "'"
showTok (TString s) = show s
showTok (TReserved r) = "`" ++ r ++ "`"
showTok TNewline = "<newline>"
showTok (TIndent n) = "<indent " ++ show n ++ ">"
showTok (TRegex r) = "/" ++ r ++ "/"
showTok (TChar c) = show c
showTok (TComment c) = "-- " ++ c
