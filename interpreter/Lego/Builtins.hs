{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE PatternSynonyms #-}
-- | Built-in reduction rules for Lego
--
-- This module contains all primitive operations that cannot be expressed
-- as user-defined rewrite rules. Organized by category:
--
--   * Core: beta reduction, graph operations
--   * Arithmetic: integers and Peano naturals  
--   * Boolean: and, or, not, if
--   * List: cons, nil, map, append, head, tail
--   * Maybe: just, nothing, map, bind
--   * Either: left, right, fold, bimap
--   * String: concat, split, join, strip, etc.
--   * Combinators: S, K, I
module Lego.Builtins
  ( builtinStep
  , substTerm
  -- * Helpers
  , termToStringList
  , splitOn
  , strip
  , replaceStr
  ) where

-- Note: Lego imports Lego.Builtins, not vice versa
-- We import internal types via Lego.Internal to avoid circular deps
import Lego.Internal (Term, pattern TmVar, pattern TmCon, pattern TmLit,
                      pattern TmI0, pattern TmI1, pattern TmPathAbs, pattern TmPathApp,
                      pattern TmHComp, pattern TmTransp)
import Data.List (isPrefixOf, isSuffixOf, isInfixOf, intercalate)
import Data.Char (toUpper, toLower, isSpace)

--------------------------------------------------------------------------------
-- Built-in Evaluation Rules
--------------------------------------------------------------------------------

-- | Built-in reduction steps for core primitives
builtinStep :: Term -> Maybe Term
builtinStep = \case
  -- ============================================================
  -- Core operations
  -- ============================================================
  
  -- poGraph identity: (poGraph emptyGraph g) → g
  TmCon "poGraph" [TmCon "emptyGraph" [], g] -> Just g
  -- poGraph left identity: (poGraph g emptyGraph) → g
  TmCon "poGraph" [g, TmCon "emptyGraph" []] -> Just g
  
  -- Explicit substitution: (subst x e body) → body[x := e]
  TmCon "subst" [TmVar x, e, body] -> Just $ substTerm x e body
  TmCon "subst" [TmLit x, e, body] -> Just $ substTerm x e body
  
  -- Beta reduction: (app (lam x _ body) arg) → body[x := arg]
  TmCon "app" [TmCon "lam" [TmVar x, _, body], arg] -> 
    Just $ substTerm x arg body
  TmCon "app" [TmCon "lam" [TmLit x, _, body], arg] -> 
    Just $ substTerm x arg body
  
  -- ============================================================
  -- Cubical path operations (native)
  -- ============================================================
  
  -- Path application at endpoints: (λi. e) @ i0 → e[i0/i], (λi. e) @ i1 → e[i1/i]
  TmPathApp (TmPathAbs i e) TmI0 -> Just $ substTerm i TmI0 e
  TmPathApp (TmPathAbs i e) TmI1 -> Just $ substTerm i TmI1 e
  
  -- Transport when φ = i1 (cofibration is true): transp A i1 a → a
  TmTransp _ TmI1 a -> Just a
  
  -- Homogeneous composition when φ = i1: hcomp A i1 u a0 → u i1
  TmHComp _ TmI1 u _ -> Just $ TmPathApp u TmI1
  
  -- Composition reduces to transport + hcomp in general
  -- comp A φ u a0 ≡ hcomp (A i1) φ (λi. transp (λj. A (i ∨ j)) (φ ∨ i) (u i)) (transp A φ a0)
  -- But we only reduce simple cases here
  
  -- ============================================================
  -- Coercion (generalized transport): coe A r r' a
  -- coe : (A : I → Type) → (r r' : I) → A r → A r'
  -- ============================================================
  
  -- coe_same: coe A r r a → a (when endpoints equal)
  TmCon "coe" [_, TmCon "i0" [], TmCon "i0" [], a] -> Just a
  TmCon "coe" [_, TmVar "i0", TmVar "i0", a] -> Just a
  TmCon "coe" [_, TmCon "i1" [], TmCon "i1" [], a] -> Just a
  TmCon "coe" [_, TmVar "i1", TmVar "i1", a] -> Just a
  -- When both endpoints are the same variable
  TmCon "coe" [_, TmVar r, TmVar r', a] | r == r' -> Just a
  
  -- coe_i0_i1: standard coercion (like transp)
  -- coe (λi. A) i0 i1 a ≡ transp (λi. A) i0 a
  -- This is the general case - defers to transp semantics
  
  -- coe along constant type: coe (λi. A) r r' a → a (when A doesn't mention i)
  -- Detected structurally: if the type is a constant (no λᵢ), it's trivial
  TmCon "coe" [TmVar _, _, _, a] -> Just a  -- Constant type variable
  TmCon "coe" [TmCon c [], _, _, a] | c `notElem` ["λᵢ"] -> Just a  -- Constant type constructor
  
  -- ============================================================
  -- Cubical bridge: TmCon syntax → native reductions
  -- These match .lego parsed syntax and reduce using cubical semantics
  -- ============================================================
  
  -- Path application: (p @ i0) → p[i0], (p @ i1) → p[i1]
  TmCon "@" [TmCon "λᵢ" [TmVar i, body], TmCon "i0" []] -> 
    Just $ substTerm i (TmCon "i0" []) body
  TmCon "@" [TmCon "λᵢ" [TmVar i, body], TmVar "i0"] -> 
    Just $ substTerm i (TmVar "i0") body
  TmCon "@" [TmCon "λᵢ" [TmVar i, body], TmCon "i1" []] -> 
    Just $ substTerm i (TmCon "i1" []) body
  TmCon "@" [TmCon "λᵢ" [TmVar i, body], TmVar "i1"] -> 
    Just $ substTerm i (TmVar "i1") body
  
  -- refl application: (refl a) @ i → a
  TmCon "@" [TmCon "refl" [a], _] -> Just a
  
  -- Transport trivial: transp A i1 a → a
  TmCon "transp" [_, TmCon "i1" [], a] -> Just a
  TmCon "transp" [_, TmVar "i1", a] -> Just a
  
  -- hcomp when φ = i1: hcomp A i1 u a0 → u @ i1
  TmCon "hcomp" [_, TmCon "i1" [], u, _] -> Just $ TmCon "@" [u, TmCon "i1" []]
  TmCon "hcomp" [_, TmVar "i1", u, _] -> Just $ TmCon "@" [u, TmVar "i1"]
  
  -- Interval operations
  TmCon "∧" [TmCon "i0" [], _] -> Just $ TmCon "i0" []
  TmCon "∧" [TmVar "i0", _] -> Just $ TmVar "i0"
  TmCon "∧" [TmCon "i1" [], x] -> Just x
  TmCon "∧" [TmVar "i1", x] -> Just x
  TmCon "∨" [TmCon "i0" [], x] -> Just x
  TmCon "∨" [TmVar "i0", x] -> Just x
  TmCon "∨" [TmCon "i1" [], _] -> Just $ TmCon "i1" []
  TmCon "∨" [TmVar "i1", _] -> Just $ TmVar "i1"
  TmCon "~" [TmCon "i0" []] -> Just $ TmCon "i1" []
  TmCon "~" [TmVar "i0"] -> Just $ TmVar "i1"
  TmCon "~" [TmCon "i1" []] -> Just $ TmCon "i0" []
  TmCon "~" [TmVar "i1"] -> Just $ TmVar "i0"
  TmCon "~" [TmCon "~" [x]] -> Just x  -- double negation
  
  -- ============================================================
  -- Pair operations
  -- ============================================================
  TmCon "fst" [TmCon "pair" [a, _]] -> Just a
  TmCon "snd" [TmCon "pair" [_, b]] -> Just b
  
  -- ============================================================
  -- List operations
  -- ============================================================
  TmCon "head" [TmCon "cons" [x, _]] -> Just x
  TmCon "tail" [TmCon "cons" [_, xs]] -> Just xs
  TmCon "null" [TmCon "nil" []] -> Just $ TmVar "true"
  TmCon "null" [TmVar "nil"] -> Just $ TmVar "true"
  TmCon "null" [TmCon "cons" _ ] -> Just $ TmVar "false"
  
  -- Map for List
  TmCon "map" [_, TmCon "nil" []] -> Just $ TmCon "nil" []
  TmCon "map" [_, TmVar "nil"] -> Just $ TmCon "nil" []
  TmCon "map" [TmVar fname, TmCon "cons" [x, xs]] -> 
    Just $ TmCon "cons" [TmCon fname [x], TmCon "map" [TmVar fname, xs]]
  TmCon "map" [TmLit fname, TmCon "cons" [x, xs]] -> 
    Just $ TmCon "cons" [TmCon fname [x], TmCon "map" [TmLit fname, xs]]
  TmCon "map" [f, TmCon "cons" [x, xs]] -> 
    Just $ TmCon "cons" [TmCon "app" [f, x], TmCon "map" [f, xs]]
  
  -- Append
  TmCon "append" [TmCon "nil" [], ys] -> Just ys
  TmCon "append" [TmVar "nil", ys] -> Just ys
  TmCon "append" [TmCon "cons" [x, xs], ys] -> 
    Just $ TmCon "cons" [x, TmCon "append" [xs, ys]]
  
  -- ============================================================
  -- Boolean operations
  -- ============================================================
  TmCon "not" [TmCon "true" []] -> Just $ TmVar "false"
  TmCon "not" [TmVar "true"] -> Just $ TmVar "false"
  TmCon "not" [TmCon "false" []] -> Just $ TmVar "true"
  TmCon "not" [TmVar "false"] -> Just $ TmVar "true"
  TmCon "and" [TmCon "true" [], b] -> Just b
  TmCon "and" [TmVar "true", b] -> Just b
  TmCon "and" [TmCon "false" [], _] -> Just $ TmVar "false"
  TmCon "and" [TmVar "false", _] -> Just $ TmVar "false"
  TmCon "or" [TmCon "true" [], _] -> Just $ TmVar "true"
  TmCon "or" [TmVar "true", _] -> Just $ TmVar "true"
  TmCon "or" [TmCon "false" [], b] -> Just b
  TmCon "or" [TmVar "false", b] -> Just b
  
  -- If-then-else
  TmCon "if" [TmCon "true" [], thn, _] -> Just thn
  TmCon "if" [TmVar "true", thn, _] -> Just thn
  TmCon "if" [TmCon "false" [], _, els] -> Just els
  TmCon "if" [TmVar "false", _, els] -> Just els
  
  -- ============================================================
  -- Arithmetic (integer literals)
  -- ============================================================
  TmCon "add" [TmLit n1, TmLit n2] -> 
    case (reads n1, reads n2) of
      ([(a,_)], [(b,_)]) -> Just $ TmLit $ show (a + b :: Int)
      _ -> Nothing
  TmCon "mul" [TmLit n1, TmLit n2] ->
    case (reads n1, reads n2) of
      ([(a,_)], [(b,_)]) -> Just $ TmLit $ show (a * b :: Int)
      _ -> Nothing
  TmCon "sub" [TmLit n1, TmLit n2] ->
    case (reads n1, reads n2) of
      ([(a,_)], [(b,_)]) -> Just $ TmLit $ show (a - b :: Int)
      _ -> Nothing
  TmCon "eq" [TmLit n1, TmLit n2] ->
    Just $ TmCon (if n1 == n2 then "true" else "false") []
  TmCon "lt" [TmLit n1, TmLit n2] ->
    case (reads n1, reads n2) of
      ([(a,_)], [(b,_)]) -> Just $ TmCon (if (a :: Int) < b then "true" else "false") []
      _ -> Nothing
  TmCon "le" [TmLit n1, TmLit n2] ->
    case (reads n1, reads n2) of
      ([(a,_)], [(b,_)]) -> Just $ TmCon (if (a :: Int) <= b then "true" else "false") []
      _ -> Nothing
      
  -- ============================================================
  -- Natural number arithmetic (Peano)
  -- ============================================================
  TmCon "pred" [TmCon "succ" [n]] -> Just n
  TmCon "pred" [TmCon "zero" []] -> Just $ TmVar "zero"
  TmCon "pred" [TmVar "zero"] -> Just $ TmVar "zero"
  TmCon "isZero" [TmCon "zero" []] -> Just $ TmVar "true"
  TmCon "isZero" [TmVar "zero"] -> Just $ TmVar "true"
  TmCon "isZero" [TmCon "succ" _] -> Just $ TmVar "false"
  
  -- Nat add
  TmCon "add" [TmCon "zero" [], n] -> Just n
  TmCon "add" [TmVar "zero", n] -> Just n
  TmCon "add" [TmCon "succ" [m], n] -> 
    Just $ TmCon "succ" [TmCon "add" [m, n]]
  
  -- Nat mul
  TmCon "mul" [TmCon "zero" [], _] -> Just $ TmVar "zero"
  TmCon "mul" [TmVar "zero", _] -> Just $ TmVar "zero"
  TmCon "mul" [TmCon "succ" [m], n] -> 
    Just $ TmCon "add" [n, TmCon "mul" [m, n]]
  
  -- Nat eq
  TmCon "eq" [TmCon "zero" [], TmCon "zero" []] -> Just $ TmVar "true"
  TmCon "eq" [TmVar "zero", TmVar "zero"] -> Just $ TmVar "true"
  TmCon "eq" [TmCon "zero" [], TmVar "zero"] -> Just $ TmVar "true"
  TmCon "eq" [TmVar "zero", TmCon "zero" []] -> Just $ TmVar "true"
  TmCon "eq" [TmCon "zero" [], TmCon "succ" _] -> Just $ TmVar "false"
  TmCon "eq" [TmVar "zero", TmCon "succ" _] -> Just $ TmVar "false"
  TmCon "eq" [TmCon "succ" _, TmCon "zero" []] -> Just $ TmVar "false"
  TmCon "eq" [TmCon "succ" _, TmVar "zero"] -> Just $ TmVar "false"
  TmCon "eq" [TmCon "succ" [m], TmCon "succ" [n]] -> 
    Just $ TmCon "eq" [m, n]
  
  -- ============================================================
  -- Maybe operations
  -- ============================================================
  TmCon "fromMaybe" [def, TmCon "nothing" []] -> Just def
  TmCon "fromMaybe" [def, TmVar "nothing"] -> Just def
  TmCon "fromMaybe" [_, TmCon "just" [x]] -> Just x
  TmCon "isJust" [TmCon "just" _] -> Just $ TmVar "true"
  TmCon "isJust" [TmCon "nothing" []] -> Just $ TmVar "false"
  TmCon "isJust" [TmVar "nothing"] -> Just $ TmVar "false"
  TmCon "isNothing" [TmCon "nothing" []] -> Just $ TmVar "true"
  TmCon "isNothing" [TmVar "nothing"] -> Just $ TmVar "true"
  TmCon "isNothing" [TmCon "just" _] -> Just $ TmVar "false"
  
  -- Map for Maybe
  TmCon "map" [_, TmCon "nothing" []] -> Just $ TmVar "nothing"
  TmCon "map" [_, TmVar "nothing"] -> Just $ TmVar "nothing"
  TmCon "map" [f, TmCon "just" [x]] -> 
    Just $ TmCon "just" [TmCon "app" [f, x]]
  
  -- Bind for Maybe
  TmCon "bind" [TmCon "nothing" [], _] -> Just $ TmVar "nothing"
  TmCon "bind" [TmVar "nothing", _] -> Just $ TmVar "nothing"
  TmCon "bind" [TmCon "just" [x], f] -> 
    Just $ TmCon "app" [f, x]
  
  -- Maybe eliminator
  TmCon "maybe" [def, _, TmCon "nothing" []] -> Just def
  TmCon "maybe" [def, _, TmVar "nothing"] -> Just def
  TmCon "maybe" [_, f, TmCon "just" [x]] -> 
    Just $ TmCon "app" [f, x]
    
  -- ============================================================
  -- Either operations
  -- ============================================================
  TmCon "isLeft" [TmCon "left" _] -> Just $ TmVar "true"
  TmCon "isLeft" [TmCon "right" _] -> Just $ TmVar "false"
  TmCon "isRight" [TmCon "right" _] -> Just $ TmVar "true"
  TmCon "isRight" [TmCon "left" _] -> Just $ TmCon "false" []
  
  TmCon "mapLeft" [f, TmCon "left" [x]] -> 
    Just $ TmCon "left" [TmCon "app" [f, x]]
  TmCon "mapLeft" [_, TmCon "right" [x]] -> 
    Just $ TmCon "right" [x]
  TmCon "mapRight" [_, TmCon "left" [x]] -> 
    Just $ TmCon "left" [x]
  TmCon "mapRight" [f, TmCon "right" [x]] -> 
    Just $ TmCon "right" [TmCon "app" [f, x]]
  TmCon "bimap" [f, _, TmCon "left" [x]] -> 
    Just $ TmCon "left" [TmCon "app" [f, x]]
  TmCon "bimap" [_, g, TmCon "right" [x]] -> 
    Just $ TmCon "right" [TmCon "app" [g, x]]
  TmCon "either" [f, _, TmCon "left" [x]] -> 
    Just $ TmCon "app" [f, x]
  TmCon "either" [_, g, TmCon "right" [x]] -> 
    Just $ TmCon "app" [g, x]
  TmCon "fold" [f, _, TmCon "left" [x]] -> 
    Just $ TmCon "app" [f, x]
  TmCon "fold" [_, g, TmCon "right" [x]] -> 
    Just $ TmCon "app" [g, x]
  
  -- ============================================================
  -- String operations
  -- ============================================================
  
  -- Newline constant
  TmVar "newline" -> Just $ TmLit "\n"
  TmCon "newline" [] -> Just $ TmLit "\n"
  
  -- Concatenation
  TmCon "concat" [TmLit s1, TmLit s2] -> Just $ TmLit (s1 ++ s2)
  TmCon "concat" [TmLit s1, TmVar v] -> Just $ TmLit (s1 ++ v)
  TmCon "concat" [TmVar v, TmLit s2] -> Just $ TmLit (v ++ s2)
  TmCon "concat" [TmVar v1, TmVar v2] -> Just $ TmLit (v1 ++ v2)
  
  -- Lines/unlines
  TmCon "lines" [TmLit s] -> Just $ foldr (\l acc -> TmCon "cons" [TmLit l, acc]) 
                                          (TmCon "nil" []) (lines s)
  TmCon "unlines" [lst] -> case termToStringList lst of
    Just ss -> Just $ TmLit (unlines ss)
    Nothing -> Nothing
  
  -- Words/unwords
  TmCon "words" [TmLit s] -> Just $ foldr (\w acc -> TmCon "cons" [TmLit w, acc])
                                          (TmCon "nil" []) (words s)
  TmCon "unwords" [lst] -> case termToStringList lst of
    Just ss -> Just $ TmLit (unwords ss)
    Nothing -> Nothing
  
  -- Take/drop
  TmCon "take" [TmLit n, TmLit s] -> case reads n of
    [(i,_)] -> Just $ TmLit (take i s)
    _ -> Nothing
  TmCon "drop" [TmLit n, TmLit s] -> case reads n of
    [(i,_)] -> Just $ TmLit (drop i s)
    _ -> Nothing
  
  -- Length
  TmCon "length" [TmLit s] -> Just $ TmLit (show (length s))
  
  -- Prefix/suffix/infix
  TmCon "startsWith" [TmLit prefix, TmLit s] -> 
    Just $ TmCon (if prefix `isPrefixOf` s then "true" else "false") []
  TmCon "endsWith" [TmLit suffix, TmLit s] ->
    Just $ TmCon (if suffix `isSuffixOf` s then "true" else "false") []
  TmCon "contains" [TmLit needle, TmLit haystack] ->
    Just $ TmCon (if needle `isInfixOf` haystack then "true" else "false") []
  
  -- Replace
  TmCon "replace" [TmLit old, TmLit new, TmLit s] ->
    Just $ TmLit (replaceStr old new s)
  
  -- Split/join
  TmCon "split" [TmLit delim, TmLit s] ->
    Just $ foldr (\p acc -> TmCon "cons" [TmLit p, acc])
                 (TmCon "nil" []) (splitOn delim s)
  TmCon "join" [TmLit delim, lst] -> case termToStringList lst of
    Just ss -> Just $ TmLit (intercalate delim ss)
    Nothing -> Nothing
  
  -- Strip/trim
  TmCon "strip" [TmLit s] -> Just $ TmLit (strip s)
  TmCon "trim" [TmLit s] -> Just $ TmLit (strip s)
  
  -- Case conversion
  TmCon "toUpper" [TmLit s] -> Just $ TmLit (map toUpper s)
  TmCon "toLower" [TmLit s] -> Just $ TmLit (map toLower s)
  
  -- String equality
  TmCon "eq" [TmVar s1, TmVar s2] -> Just $ TmCon (if s1 == s2 then "true" else "false") []
  TmCon "eq" [TmVar s1, TmLit s2] -> Just $ TmCon (if s1 == s2 then "true" else "false") []
  TmCon "eq" [TmLit s1, TmVar s2] -> Just $ TmCon (if s1 == s2 then "true" else "false") []
  
  -- Character access
  TmCon "charAt" [TmLit n, TmLit s] -> case reads n of
    [(i,_)] | i >= 0 && i < length s -> Just $ TmLit [s !! i]
    _ -> Nothing
  TmCon "substring" [TmLit start, TmLit end, TmLit s] -> 
    case (reads start, reads end) of
      ([(i,_)], [(j,_)]) -> Just $ TmLit (take (j-i) (drop i s))
      _ -> Nothing
    
  -- ============================================================
  -- SKI Combinators
  -- ============================================================
  TmCon "app" [TmVar "I", x] -> Just x
  TmCon "app" [TmCon "I" [], x] -> Just x
  TmCon "app" [TmCon "app" [TmVar "K", x], _] -> Just x
  TmCon "app" [TmCon "app" [TmCon "K" [], x], _] -> Just x
  TmCon "app" [TmCon "app" [TmCon "app" [TmVar "S", f], g], x] -> 
    Just $ TmCon "app" [TmCon "app" [f, x], TmCon "app" [g, x]]
  TmCon "app" [TmCon "app" [TmCon "app" [TmCon "S" [], f], g], x] -> 
    Just $ TmCon "app" [TmCon "app" [f, x], TmCon "app" [g, x]]
  
  -- ============================================================
  -- Congruence: reduce inside constructors
  -- ============================================================
  TmCon c args -> 
    let stepped = zipWith stepArg [0..] args
        stepArg i a = (i, builtinStep a)
    in case [(i, a') | (i, Just a') <- stepped] of
         [] -> Nothing
         ((i, a'):_) -> Just $ TmCon c (take i args ++ [a'] ++ drop (i+1) args)
  
  _ -> Nothing

--------------------------------------------------------------------------------
-- Substitution
--------------------------------------------------------------------------------

-- | Substitution: t[x := s]
--   Implemented using cata for the core traversal
substTerm :: String -> Term -> Term -> Term
substTerm x s t = cataSubst x s t
  where
    cataSubst :: String -> Term -> Term -> Term
    cataSubst var sub (TmVar y) 
      | var == y  = sub
      | otherwise = TmVar y
    cataSubst _ _ (TmLit l) = TmLit l
    cataSubst var sub (TmCon "lam" [TmVar y, ty, body])
      | var == y  = TmCon "lam" [TmVar y, cataSubst var sub ty, body]  -- shadowed
      | otherwise = TmCon "lam" [TmVar y, cataSubst var sub ty, cataSubst var sub body]
    cataSubst var sub (TmCon "lam" [TmLit y, ty, body])
      | var == y  = TmCon "lam" [TmLit y, cataSubst var sub ty, body]  -- shadowed
      | otherwise = TmCon "lam" [TmLit y, cataSubst var sub ty, cataSubst var sub body]
    cataSubst var sub (TmCon "pi" [TmVar y, ty, body])
      | var == y  = TmCon "pi" [TmVar y, cataSubst var sub ty, body]  -- shadowed
      | otherwise = TmCon "pi" [TmVar y, cataSubst var sub ty, cataSubst var sub body]
    cataSubst var sub (TmCon c args) = TmCon c (map (cataSubst var sub) args)
    cataSubst _ _ t' = t'

--------------------------------------------------------------------------------
-- Helper functions
--------------------------------------------------------------------------------

-- | Extract a list of strings from a term list
termToStringList :: Term -> Maybe [String]
termToStringList (TmCon "nil" []) = Just []
termToStringList (TmVar "nil") = Just []
termToStringList (TmCon "cons" [TmLit s, rest]) = do
  ss <- termToStringList rest
  return (s : ss)
termToStringList (TmCon "cons" [TmVar s, rest]) = do
  ss <- termToStringList rest
  return (s : ss)
termToStringList _ = Nothing

-- | Split a string on a delimiter
splitOn :: String -> String -> [String]
splitOn _ "" = [""]
splitOn delim str@(c:cs)
  | delim `isPrefixOf` str = "" : splitOn delim (drop (length delim) str)
  | otherwise = case splitOn delim cs of
      (x:xs) -> (c : x) : xs
      [] -> [[c]]

-- | Strip leading and trailing whitespace
strip :: String -> String
strip = dropWhile isSpace . reverse . dropWhile isSpace . reverse

-- | Replace all occurrences of a substring
replaceStr :: String -> String -> String -> String
replaceStr _ _ "" = ""
replaceStr old new str@(c:cs)
  | old `isPrefixOf` str = new ++ replaceStr old new (drop (length old) str)
  | otherwise = c : replaceStr old new cs
