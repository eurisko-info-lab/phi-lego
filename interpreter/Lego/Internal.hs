{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE UndecidableInstances #-}
-- | Internal types for Lego - breaks circular dependencies
--
-- This module provides the core Term type and patterns needed by
-- Lego.Builtins without importing the full Lego module.
module Lego.Internal
  ( -- * Fixed-point combinator
    Fix(..)
  , cata
  , ana
    -- * Base expression functor
  , ExprF(..)
    -- * Term type with patterns
  , Term(..)
  , pattern TmVar
  , pattern TmCon
  , pattern TmLit
  , pattern TmSyntax
  , pattern TmReserved
  , pattern TmRegex
  , pattern TmChar
    -- * Cubical patterns
  , pattern TmInterval
  , pattern TmI0
  , pattern TmI1
  , pattern TmPathType
  , pattern TmPathAbs
  , pattern TmPathApp
    -- * Composition operations
  , pattern TmComp
  , pattern TmHComp
  , pattern TmTransp
  ) where

--------------------------------------------------------------------------------
-- Fixed-Point Combinator
--------------------------------------------------------------------------------

-- | Fix: The fixed-point of a functor
--   Fix f ≅ f (Fix f)
--   This is the key to unifying Term, GrammarExpr, etc.
newtype Fix f = Fix { unFix :: f (Fix f) }

instance Eq (f (Fix f)) => Eq (Fix f) where
  Fix a == Fix b = a == b

instance Show (f (Fix f)) => Show (Fix f) where
  showsPrec d (Fix f) = showsPrec d f

-- | Catamorphism: fold over Fix using an f-algebra
cata :: Functor f => (f a -> a) -> Fix f -> a
cata alg = go where go (Fix f) = alg (fmap go f)

-- | Anamorphism: unfold into Fix using an f-coalgebra  
ana :: Functor f => (a -> f a) -> a -> Fix f
ana coalg = go where go a = Fix (fmap go (coalg a))

--------------------------------------------------------------------------------
-- Base Expression Functor
--------------------------------------------------------------------------------

-- | ExprF: The common algebraic structure for expressions
--
-- Mathematical structure:
--   ExprF forms a polynomial functor with cubical extensions
--
-- Base cases:
--   EVar: Variables (references to bindings)
--   ECon: Constructors (tagged products)
--   ELit: Content literals (semantic content, preserved)
--   ESyn: Syntax literals (structural markers, droppable)
--
-- Cubical cases (for Path types / HITs):
--   EInterval: The interval type I
--   EI0, EI1: Interval endpoints i0, i1 : I
--   EPathType: Path A a b - paths between terms
--   EPathAbs: λ(i:I). e - path abstraction
--   EPathApp: p @ r - path application at dimension r
--
data ExprF a
  = EVar String        -- Variable reference
  | ECon String [a]    -- Constructor with children
  | ELit String        -- '...' Soft keyword (context-dependent)
  | ESyn String        -- "..." Syntax literal (operators, structure)
  | EReserved String   -- `...` Reserved keyword (rejected by <ident>)
  | ERegex String      -- /.../ Regex literal
  | EChar String       -- '...' Character literal (single quotes)
  -- Cubical primitives
  | EInterval          -- I : Type (the interval)
  | EI0                -- i0 : I (left endpoint)
  | EI1                -- i1 : I (right endpoint)
  | EPathType a a a    -- Path A a b : Type
  | EPathAbs String a  -- λ(i:I). e : Path A (e[i0/i]) (e[i1/i])
  | EPathApp a a       -- p @ r : A (path application)
  -- Composition operations (Kan operations)
  | EComp a a a a      -- comp A φ u a0 : composition
  | EHComp a a a a     -- hcomp A φ u a0 : homogeneous composition
  | ETransp a a a      -- transp A φ a : transport
  deriving (Eq, Show, Functor, Foldable, Traversable)

--------------------------------------------------------------------------------
-- Term Type
--------------------------------------------------------------------------------

-- | Term = Fix ExprF (with newtype for custom Show)
newtype Term = Term { unTerm :: Fix ExprF }
  deriving (Eq)

-- Pattern synonyms for ergonomic matching
pattern TmVar :: String -> Term
pattern TmVar x = Term (Fix (EVar x))

pattern TmCon :: String -> [Term] -> Term
pattern TmCon c ts <- Term (Fix (ECon c (map Term -> ts)))
  where TmCon c ts = Term (Fix (ECon c (map unTerm ts)))

pattern TmLit :: String -> Term
pattern TmLit s = Term (Fix (ELit s))

pattern TmSyntax :: String -> Term
pattern TmSyntax s = Term (Fix (ESyn s))

pattern TmReserved :: String -> Term
pattern TmReserved s = Term (Fix (EReserved s))

pattern TmRegex :: String -> Term
pattern TmRegex s = Term (Fix (ERegex s))

pattern TmChar :: String -> Term
pattern TmChar s = Term (Fix (EChar s))

-- Cubical pattern synonyms
pattern TmInterval :: Term
pattern TmInterval = Term (Fix EInterval)

pattern TmI0 :: Term
pattern TmI0 = Term (Fix EI0)

pattern TmI1 :: Term
pattern TmI1 = Term (Fix EI1)

pattern TmPathType :: Term -> Term -> Term -> Term
pattern TmPathType a x y <- Term (Fix (EPathType (Term -> a) (Term -> x) (Term -> y)))
  where TmPathType a x y = Term (Fix (EPathType (unTerm a) (unTerm x) (unTerm y)))

pattern TmPathAbs :: String -> Term -> Term
pattern TmPathAbs i e <- Term (Fix (EPathAbs i (Term -> e)))
  where TmPathAbs i e = Term (Fix (EPathAbs i (unTerm e)))

pattern TmPathApp :: Term -> Term -> Term
pattern TmPathApp p r <- Term (Fix (EPathApp (Term -> p) (Term -> r)))
  where TmPathApp p r = Term (Fix (EPathApp (unTerm p) (unTerm r)))

-- Composition pattern synonyms
pattern TmComp :: Term -> Term -> Term -> Term -> Term
pattern TmComp a phi u a0 <- Term (Fix (EComp (Term -> a) (Term -> phi) (Term -> u) (Term -> a0)))
  where TmComp a phi u a0 = Term (Fix (EComp (unTerm a) (unTerm phi) (unTerm u) (unTerm a0)))

pattern TmHComp :: Term -> Term -> Term -> Term -> Term
pattern TmHComp a phi u a0 <- Term (Fix (EHComp (Term -> a) (Term -> phi) (Term -> u) (Term -> a0)))
  where TmHComp a phi u a0 = Term (Fix (EHComp (unTerm a) (unTerm phi) (unTerm u) (unTerm a0)))

pattern TmTransp :: Term -> Term -> Term -> Term
pattern TmTransp a phi a0 <- Term (Fix (ETransp (Term -> a) (Term -> phi) (Term -> a0)))
  where TmTransp a phi a0 = Term (Fix (ETransp (unTerm a) (unTerm phi) (unTerm a0)))

{-# COMPLETE TmVar, TmCon, TmLit, TmSyntax, TmReserved, TmRegex, TmChar, TmInterval, TmI0, TmI1, TmPathType, TmPathAbs, TmPathApp, TmComp, TmHComp, TmTransp #-}

instance Show Term where
  show (TmVar x) = x
  show (TmLit s) = show s
  show (TmSyntax _) = ""  -- Syntax is invisible in output
  show (TmReserved s) = s -- Reserved words shown as-is
  show (TmRegex s) = "/" ++ s ++ "/"  -- Regex shown with delimiters
  show (TmChar s) = "'" ++ s ++ "'"  -- Char literals with single quotes
  show TmInterval = "I"
  show TmI0 = "i0"
  show TmI1 = "i1"
  show (TmPathType a x y) = "(Path " ++ show a ++ " " ++ show x ++ " " ++ show y ++ ")"
  show (TmPathAbs i e) = "(λ" ++ i ++ ". " ++ show e ++ ")"
  show (TmPathApp p r) = "(" ++ show p ++ " @ " ++ show r ++ ")"
  show (TmComp a phi u a0) = "(comp " ++ show a ++ " " ++ show phi ++ " " ++ show u ++ " " ++ show a0 ++ ")"
  show (TmHComp a phi u a0) = "(hcomp " ++ show a ++ " " ++ show phi ++ " " ++ show u ++ " " ++ show a0 ++ ")"
  show (TmTransp a phi a0) = "(transp " ++ show a ++ " " ++ show phi ++ " " ++ show a0 ++ ")"
  show (TmCon "subst" [TmVar x, e, body]) = "[" ++ x ++ " := " ++ show e ++ "] " ++ show body
  show (TmCon c []) = c
  show (TmCon c args) = "(" ++ c ++ " " ++ unwords (map show args) ++ ")"
