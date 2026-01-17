{-# LANGUAGE LambdaCase #-}
-- | Attribute Grammar Evaluation
--
-- This module implements attribute grammars as catamorphisms (synthesized)
-- and paramorphisms (inherited) over parse trees.
--
-- Mathematical Foundation:
--
--   Grammar   →  Functor F (GrammarF)
--   Parse Tree →  Fix F (initial algebra μF)
--   Syn Attr  →  F-Algebra: alg : F A → A, computed via cata alg : Fix F → A
--   Inh Attr  →  Paramorphism: para : (F (Fix F, A) → A), carries context
--
-- Pushout Compatibility:
--   (L₁, A₁) ⊔ (L₂, A₂) = (L₁ ⊔ L₂, A₁ ⋈ A₂)
--   where A₁ ⋈ A₂ is the coproduct of attribute algebras
--
module Lego.Attr
  ( -- * Attribute Environment
    AttrEnv
  , emptyAttrEnv
  , lookupAttr
  , insertAttr
  , childAttr
    
    -- * Attribute Evaluation
  , evalSyn
  , evalInh
  , evalAttrs
  
    -- * Catamorphism / Paramorphism
  , cataAttr
  , paraAttr
  ) where

import Data.Map (Map)
import qualified Data.Map as M

import Lego (Term, AttrDef(..), AttrFlow(..), AttrRule(..), AttrPath)
import Lego.Internal (Fix(..), cata, pattern TmCon, pattern TmVar, pattern TmLit)

--------------------------------------------------------------------------------
-- Attribute Environment
--------------------------------------------------------------------------------

-- | Attribute environment: maps (node-path, attr-name) to computed value
--
-- The key is a path from the root: [] = root, ["body"] = root.body, etc.
-- This allows both synthesized (computed at node) and inherited (from parent).
type AttrEnv = Map (AttrPath, String) Term

-- | Empty attribute environment
emptyAttrEnv :: AttrEnv
emptyAttrEnv = M.empty

-- | Lookup an attribute at a given path
lookupAttr :: AttrPath -> String -> AttrEnv -> Maybe Term
lookupAttr path name env = M.lookup (path, name) env

-- | Insert an attribute at a given path
insertAttr :: AttrPath -> String -> Term -> AttrEnv -> AttrEnv
insertAttr path name val = M.insert (path, name) val

-- | Get attribute for a child node
-- childAttr ["body"] "type" env  looks up (["body"], "type")
childAttr :: String -> String -> AttrEnv -> Maybe Term
childAttr child attr env = lookupAttr [child] attr env

--------------------------------------------------------------------------------
-- Synthesized Attributes (Catamorphism)
--------------------------------------------------------------------------------

-- | Evaluate a synthesized attribute via catamorphism
--
-- The algebra takes:
--   - The node constructor name
--   - Already-computed attributes of children (as an AttrEnv)
--   - The attribute definition
-- And produces the attribute value for this node.
--
-- Mathematical structure: cata alg : Fix F → A
-- where alg : F A → A and F is the grammar functor
evalSyn :: AttrDef -> Term -> AttrEnv -> Term
evalSyn def term env = 
  -- For now, a simple structural recursion
  -- Full implementation would interpret the attribute equations
  case term of
    TmCon con children ->
      -- Find the rule for this constructor
      case findRule con (adRules def) of
        Just rule -> evalAttrExpr (arExpr rule) childEnv
          where
            -- Build environment with children's attributes
            childEnv = foldr addChild env (zip childNames children)
            childNames = map (\i -> "child" ++ show i) [0..]
            addChild (name, child) e = 
              -- Recursively compute child's attribute and add to env
              let childVal = evalSyn def child e
              in insertAttr [name] (adName def) childVal e
        Nothing -> 
          -- No rule: default to unit
          TmCon "unit" []
    
    TmVar _ -> TmCon "unit" []  -- Variables don't synthesize
    TmLit s -> TmLit s          -- Literals pass through
    _ -> TmCon "unit" []

-- | Find a rule for a given production
findRule :: String -> [AttrRule] -> Maybe AttrRule
findRule prod = foldr check Nothing
  where
    check rule acc
      | arProd rule == prod = Just rule
      | otherwise = acc

--------------------------------------------------------------------------------
-- Inherited Attributes (Paramorphism)
--------------------------------------------------------------------------------

-- | Evaluate inherited attributes via paramorphism
--
-- The coalgebra takes:
--   - The parent's inherited attributes
--   - The current node and its position among siblings
-- And produces inherited attributes for children.
--
-- Mathematical structure: para coalg : Fix F → A
-- where coalg : F (Fix F, A) → A carries both subtree and computed value
evalInh :: AttrDef -> Term -> AttrEnv -> AttrEnv
evalInh def term parentEnv =
  case term of
    TmCon con children ->
      -- Find rules that compute inherited attrs for children
      let childEnvs = zipWith (evalChildInh def con parentEnv) childNames children
          childNames = map (\i -> "child" ++ show i) [0..]
      in foldr M.union parentEnv childEnvs
    
    _ -> parentEnv  -- Leaves just inherit from parent

-- | Evaluate inherited attribute for a specific child
evalChildInh :: AttrDef -> String -> AttrEnv -> String -> Term -> AttrEnv
evalChildInh def prod parentEnv childName _childTerm =
  -- Look for rule: prod.childName.attrName = expr
  case findChildRule prod childName (adRules def) of
    Just rule -> 
      let val = evalAttrExpr (arExpr rule) parentEnv
      in insertAttr [childName] (adName def) val emptyAttrEnv
    Nothing -> 
      -- No rule: child doesn't inherit this attr
      emptyAttrEnv

-- | Find a rule for a child's inherited attribute
findChildRule :: String -> String -> [AttrRule] -> Maybe AttrRule
findChildRule prod child = foldr check Nothing
  where
    check rule acc
      | arProd rule == prod, arTarget rule == [child, "?"] = Just rule
      | otherwise = acc

--------------------------------------------------------------------------------
-- Attribute Expression Evaluation
--------------------------------------------------------------------------------

-- | Evaluate an attribute expression in an environment
--
-- Expressions can be:
--   - Attribute references: $attr or child.$attr
--   - Constructors: (Arrow $a $b)
--   - Function applications: (lookup $env $name)
evalAttrExpr :: Term -> AttrEnv -> Term
evalAttrExpr expr env = case expr of
  -- Attribute reference: $name -> look up in env
  TmVar ('$':name) ->
    case lookupAttr [] name env of
      Just v -> v
      Nothing -> TmCon "error" [TmLit $ "undefined attribute: " ++ name]
  
  -- Constructor: recursively evaluate children
  TmCon con args ->
    TmCon con (map (`evalAttrExpr` env) args)
  
  -- Literal: pass through
  TmLit s -> TmLit s
  
  -- Other: pass through
  other -> other

--------------------------------------------------------------------------------
-- Combined Evaluation
--------------------------------------------------------------------------------

-- | Evaluate all attributes for a term
--
-- This performs a two-pass evaluation:
--   1. Top-down: compute inherited attributes (paramorphism)
--   2. Bottom-up: compute synthesized attributes (catamorphism)
--
-- For circular attributes, we'd use fixpoint iteration instead.
evalAttrs :: [AttrDef] -> Term -> AttrEnv
evalAttrs defs term = synEnv
  where
    -- Separate syn and inh attributes
    (synDefs, inhDefs) = partition isSyn defs
    isSyn d = adFlow d == Syn
    
    -- First pass: inherited (top-down)
    inhEnv = foldr (\d e -> evalInh d term e) emptyAttrEnv inhDefs
    
    -- Second pass: synthesized (bottom-up)
    synEnv = foldr (\d e -> insertAttr [] (adName d) (evalSyn d term e) e) 
                   inhEnv synDefs
    
    partition p xs = (filter p xs, filter (not . p) xs)

--------------------------------------------------------------------------------
-- Generic Catamorphism / Paramorphism for Terms
--------------------------------------------------------------------------------

-- | Catamorphism over Term
--
-- This is the generic fold that attribute grammars are built on.
-- cataAttr alg t = alg (fmap (cataAttr alg) (unTerm t))
cataAttr :: (String -> [a] -> a) -> Term -> a
cataAttr alg = go
  where
    go (TmCon con args) = alg con (map go args)
    go (TmVar x) = alg x []
    go (TmLit s) = alg s []
    go _ = alg "?" []

-- | Paramorphism over Term
--
-- Like catamorphism but also gives access to the original subtree.
-- paraAttr coalg t = coalg (fmap (\x -> (x, paraAttr coalg x)) (unTerm t))
paraAttr :: (String -> [(Term, a)] -> a) -> Term -> a
paraAttr coalg = go
  where
    go t@(TmCon con args) = coalg con (map (\a -> (a, go a)) args)
    go t@(TmVar x) = coalg x []
    go t@(TmLit s) = coalg s []
    go t = coalg "?" []
