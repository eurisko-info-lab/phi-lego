{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE PatternSynonyms #-}
-- | Schema: Constructor arities and sort membership
--
-- Schema separates structure (how many children) from syntax (how to parse).
-- This is analogous to Prolog's functor/arity system: lam/2, var/1, app/2.
--
-- The grammar handles: surface syntax ↔ s-expr
-- The schema handles:  s-expr ↔ Term (with arity validation)
module Lego.Schema
  ( -- * Types
    Schema(..)
  , Arity(..)
  , SchemaError(..)
    -- * Construction
  , emptySchema
  , addConstructor
  , addSort
    -- * Validation
  , validateSExpr
  , checkArity
    -- * Conversion
  , sexprToTerm
  , termToSExpr
    -- * Built-in schemas
  , termSchema
  ) where

import Lego.SExpr (SExpr(..))
import Lego (Term, pattern TmVar, pattern TmCon, pattern TmLit)
import qualified Data.Map as M
import Data.Map (Map)

-- | Arity specification for constructors
data Arity
  = Arity Int              -- ^ Exact arity: lam/2
  | ArityAtLeast Int       -- ^ Minimum arity: app/1+ (variadic)
  | ArityRange Int Int     -- ^ Range: case/2-10
  deriving (Eq, Show)

-- | Schema errors
data SchemaError
  = UnknownConstructor String
  | ArityMismatch String Arity Int  -- constructor, expected, got
  | InvalidSExpr String             -- description
  | SortMismatch String String [String]  -- value, expected sort, valid constructors
  deriving (Eq, Show)

-- | Schema: maps constructors to arities, sorts to valid constructors
data Schema = Schema
  { schemaConstructors :: Map String Arity
  , schemaSorts        :: Map String [String]  -- sort name -> constructor names
  } deriving (Eq, Show)

-- | Empty schema
emptySchema :: Schema
emptySchema = Schema M.empty M.empty

-- | Add a constructor with its arity
addConstructor :: String -> Arity -> Schema -> Schema
addConstructor name arity s = s { schemaConstructors = M.insert name arity (schemaConstructors s) }

-- | Add constructors to a sort
addSort :: String -> [String] -> Schema -> Schema
addSort name cons s = s { schemaSorts = M.insert name cons (schemaSorts s) }

-- | Check if an arity matches a count
checkArity :: Arity -> Int -> Bool
checkArity (Arity n) count = count == n
checkArity (ArityAtLeast n) count = count >= n
checkArity (ArityRange lo hi) count = count >= lo && count <= hi

-- | Validate an s-expr against a schema
-- Returns Left on error, Right () on success
validateSExpr :: Schema -> SExpr -> Either SchemaError ()
validateSExpr schema = go
  where
    go (Atom _) = Right ()  -- atoms (variables, literals) always valid
    go (List []) = Left $ InvalidSExpr "Empty list not allowed"
    go (List (Atom con : args)) =
      case M.lookup con (schemaConstructors schema) of
        Nothing -> Right ()  -- unknown constructors allowed (extensibility)
        Just arity
          | checkArity arity (length args) -> mapM_ go args
          | otherwise -> Left $ ArityMismatch con arity (length args)
    go (List (x : _)) = Left $ InvalidSExpr $ "Constructor must be atom, got list"

-- | Convert s-expr to Term
-- Assumes validation has passed
sexprToTerm :: SExpr -> Term
sexprToTerm (Atom s) = TmVar s
sexprToTerm (List [Atom "str", Atom s]) = TmLit s
sexprToTerm (List [Atom "num", Atom n]) = TmLit n
sexprToTerm (List (Atom con : args)) = TmCon con (map sexprToTerm args)
sexprToTerm (List []) = TmCon "unit" []  -- shouldn't happen after validation

-- | Convert Term to s-expr
termToSExpr :: Term -> SExpr
termToSExpr (TmVar s) = Atom s
termToSExpr (TmLit s) = List [Atom "lit", Atom s]
termToSExpr (TmCon con args) = List (Atom con : map termToSExpr args)

-- | Built-in schema for Lego terms
-- Extracted from Grammar.sexpr node definitions
termSchema :: Schema
termSchema = Schema
  { schemaConstructors = M.fromList
      -- Term constructors
      [ ("lam", Arity 2)         -- (lam x body)
      , ("λᵢ", Arity 2)          -- (λᵢ x body) path abstraction
      , ("var", Arity 1)         -- (var x)
      , ("app", ArityAtLeast 1)  -- (app f args...)
      , ("Π", Arity 3)           -- (Π x A B)
      , ("Σ", Arity 3)           -- (Σ x A B)
      , ("∀", Arity 3)           -- (∀ x A B)
      , ("str", Arity 1)         -- (str "hello")
      , ("num", Arity 1)         -- (num 42)
      , ("hole", Arity 1)        -- (hole name)
      , ("proj", Arity 1)        -- (proj field)
      , ("metavar", Arity 1)     -- (metavar $x)
      -- Pattern constructors
      , ("litIdent", Arity 1)    -- (litIdent x)
      , ("pstr", Arity 1)        -- (pstr "s")
      -- Template constructors
      , ("tstr", Arity 1)        -- (tstr "s")
      , ("subst", Arity 3)       -- (subst x val body)
      -- Declaration constructors
      , ("DLang", ArityAtLeast 2)
      , ("DImport", Arity 1)
      , ("DInherit", Arity 1)
      , ("DRule", Arity 3)       -- (DRule name pattern template)
      , ("DLaw", Arity 3)        -- (DLaw name lhs rhs)
      , ("DDef", Arity 2)        -- (DDef name value)
      , ("DAutocut", Arity 1)
      ]
  , schemaSorts = M.fromList
      [ ("term", ["lam", "λᵢ", "var", "app", "Π", "Σ", "∀", "str", "num", "hole", "proj", "metavar"])
      , ("pattern", ["metavar", "litIdent", "pstr", "λᵢ"])
      , ("template", ["metavar", "litIdent", "tstr", "λᵢ", "lam", "subst"])
      , ("decl", ["DLang", "DImport", "DInherit", "DRule", "DLaw", "DDef", "DAutocut"])
      ]
  }
