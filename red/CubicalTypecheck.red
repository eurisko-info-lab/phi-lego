-- CubicalTypecheck.red
-- Type checking/inference for Cubical terms using attribute grammars
-- Based on bidirectional type theory + cubical extensions

module CubicalTypecheck where

import CubicalIDE

-----------------------------------------------------
-- 1. Types
-----------------------------------------------------
data Type : Type where
  TyType  : Nat -> Type                -- Type_n (universe level)
  TyPi    : String -> Type -> Type -> Type  -- Π(x:A).B
  TyPath  : Type -> Term -> Term -> Type    -- Path A a b
  TySigma : String -> Type -> Type -> Type  -- Σ(x:A).B
  TyNat   : Type
  TyUnit  : Type
  TyEmpty : Type
  TyVar   : String -> Type             -- type variable
  TyHIT   : String -> List Type -> Type  -- HIT name args

-----------------------------------------------------
-- 2. Typing Context
-----------------------------------------------------
record Binding : Type where
  constructor mkBinding
  name  : String
  type  : Type
  value : Maybe Term

Context : Type
Context = List Binding

emptyCtx : Context
emptyCtx = []

extendCtx : String -> Type -> Context -> Context
extendCtx x ty ctx = mkBinding x ty Nothing :: ctx

lookupCtx : String -> Context -> Maybe Type
lookupCtx x [] = Nothing
lookupCtx x (b :: bs) = if b.name == x then Just b.type else lookupCtx x bs

-----------------------------------------------------
-- 3. Dimension Context (for cubical)
-----------------------------------------------------
DimContext : Type
DimContext = List String

emptyDimCtx : DimContext
emptyDimCtx = []

extendDimCtx : String -> DimContext -> DimContext
extendDimCtx i ctx = i :: ctx

isDim : String -> DimContext -> Bool
isDim i ctx = elem i ctx

-----------------------------------------------------
-- 4. Type Errors
-----------------------------------------------------
data Severity : Type where
  Error   : Severity
  Warning : Severity
  Info    : Severity

record SourceLoc : Type where
  constructor mkLoc
  file   : String
  line   : Nat
  column : Nat

record TypeError : Type where
  constructor mkError
  message  : String
  loc      : Maybe SourceLoc
  severity : Severity
  expected : Maybe Type
  actual   : Maybe Type

-----------------------------------------------------
-- 5. Type Checking Result (accumulates errors)
-----------------------------------------------------
data Result (A : Type) : Type where
  Ok     : A -> List TypeError -> Result A
  Failed : List TypeError -> Result A

pure : {A : Type} -> A -> Result A
pure a = Ok a []

fail : {A : Type} -> TypeError -> Result A
fail e = Failed [e]

bind : {A B : Type} -> Result A -> (A -> Result B) -> Result B
bind (Ok a errs1) f =
  case f a of
    Ok b errs2   -> Ok b (errs1 ++ errs2)
    Failed errs2 -> Failed (errs1 ++ errs2)
bind (Failed errs) _ = Failed errs

-- Monad instance
instance Monad Result where
  return = pure
  (>>=)  = bind

-- Error helpers
typeError : String -> Result a
typeError msg = fail (mkError msg Nothing Error Nothing Nothing)

typeMismatch : Type -> Type -> Result a
typeMismatch expected actual =
  fail (mkError "Type mismatch" Nothing Error (Just expected) (Just actual))

undefinedVar : String -> Result a
undefinedVar x = fail (mkError ("Undefined variable: " ++ x) Nothing Error Nothing Nothing)

-----------------------------------------------------
-- 6. Bidirectional Type Checking
-----------------------------------------------------
-- Mode: Check (against expected type) or Infer (synthesize type)
data Mode : Type where
  Check : Type -> Mode
  Infer : Mode

-----------------------------------------------------
-- 7. Core Inference Rules
-----------------------------------------------------

-- infer : Context -> DimContext -> Term -> Result Type
infer : Context -> DimContext -> Term -> Result Type

-- Type universes
infer ctx dctx (var "Type") = pure (TyType 1)

-- Variables
infer ctx dctx (var x) =
  case lookupCtx x ctx of
    Just ty -> pure ty
    Nothing -> undefinedVar x

-- Lambda (can only check, not infer without annotation)
infer ctx dctx (lam x ty body) =
  do tyTy <- infer ctx dctx ty
     bodyTy <- infer (extendCtx x (termToType ty) ctx) dctx body
     pure (TyPi x (termToType ty) bodyTy)

-- Application
infer ctx dctx (app f a) =
  do fTy <- infer ctx dctx f
     case fTy of
       TyPi x domTy codTy ->
         do check ctx dctx a domTy
            pure (substType x a codTy)
       _ -> typeError "Expected function type in application"

-- Reflexivity path
infer ctx dctx (refl t) =
  do ty <- infer ctx dctx t
     pure (TyPath ty t t)

-- Path composition
infer ctx dctx (path_comp p q) =
  do pTy <- infer ctx dctx p
     qTy <- infer ctx dctx q
     case (pTy, qTy) of
       (TyPath a x y, TyPath b y' z) ->
         if termEq y y'
         then pure (TyPath a x z)
         else typeError "Path endpoints don't match in composition"
       _ -> typeError "Expected path types in composition"

-- Path inverse
infer ctx dctx (path_inv p) =
  do pTy <- infer ctx dctx p
     case pTy of
       TyPath a x y -> pure (TyPath a y x)
       _ -> typeError "Expected path type in inverse"

-- J eliminator
infer ctx dctx (J A C d p) =
  do -- A : Type
     aTy <- infer ctx dctx A
     -- C : (x y : A) -> Path A x y -> Type
     -- d : (x : A) -> C x x (refl x)
     -- p : Path A a b
     pTy <- infer ctx dctx p
     case pTy of
       TyPath tyA a b ->
         do dTy <- infer ctx dctx d
            -- Result type is C a b p
            pure (TyVar "J_result")  -- simplified
       _ -> typeError "J eliminator expects a path"

-- Coercion
infer ctx dctx (coe A i0 i1) =
  do -- A should be a type line (i : I) -> Type
     pure (TyVar "coe_result")  -- simplified

-- HIT constructors
infer ctx dctx (hit "base") = pure (TyHIT "S1" [])
infer ctx dctx (hit "loop") = pure (TyPath (TyHIT "S1" []) (hit "base") (hit "base"))
infer ctx dctx (hit "circle") = pure (TyType 0)
infer ctx dctx (hit (susp t)) =
  do ty <- infer ctx dctx t
     pure (TyHIT "Susp" [ty])
infer ctx dctx (hit (trunc n t)) =
  do ty <- infer ctx dctx t
     pure (TyHIT "Trunc" [TyNat, ty])

-- Fallback
infer ctx dctx t = typeError ("Cannot infer type for: " ++ show t)

-----------------------------------------------------
-- 8. Type Checking (against expected type)
-----------------------------------------------------

check : Context -> DimContext -> Term -> Type -> Result ()

-- Lambda checks against Pi type
check ctx dctx (lam x _ body) (TyPi y domTy codTy) =
  check (extendCtx x domTy ctx) dctx body codTy

-- Reflexivity checks against Path type
check ctx dctx (refl t) (TyPath ty a b) =
  do check ctx dctx t ty
     if termEq t a && termEq t b
     then pure ()
     else typeError "Reflexivity term doesn't match path endpoints"

-- Subsumption: infer and compare
check ctx dctx t expected =
  do actual <- infer ctx dctx t
     if typeEq actual expected
     then pure ()
     else typeMismatch expected actual

-----------------------------------------------------
-- 9. Type Equality
-----------------------------------------------------
typeEq : Type -> Type -> Bool
typeEq (TyType n) (TyType m) = n == m
typeEq (TyPi x a b) (TyPi y c d) = typeEq a c && typeEq b d
typeEq (TyPath a x y) (TyPath b x' y') =
  typeEq a b && termEq x x' && termEq y y'
typeEq (TySigma x a b) (TySigma y c d) = typeEq a c && typeEq b d
typeEq TyNat TyNat = True
typeEq TyUnit TyUnit = True
typeEq TyEmpty TyEmpty = True
typeEq (TyVar x) (TyVar y) = x == y
typeEq (TyHIT n as) (TyHIT m bs) = n == m && all2 typeEq as bs
typeEq _ _ = False

-----------------------------------------------------
-- 10. Term Equality (structural)
-----------------------------------------------------
termEq : Term -> Term -> Bool
termEq (var x) (var y) = x == y
termEq (lam x _ b) (lam y _ c) = x == y && termEq b c
termEq (app f a) (app g b) = termEq f g && termEq a b
termEq (refl t) (refl s) = termEq t s
termEq _ _ = False  -- simplified

-----------------------------------------------------
-- 11. Type Substitution
-----------------------------------------------------
substType : String -> Term -> Type -> Type
substType x t (TyPi y a b) =
  if x == y
  then TyPi y (substType x t a) b  -- y shadows x
  else TyPi y (substType x t a) (substType x t b)
substType x t (TyPath a l r) =
  TyPath (substType x t a) (subst x t l) (subst x t r)
substType x t (TySigma y a b) =
  if x == y
  then TySigma y (substType x t a) b
  else TySigma y (substType x t a) (substType x t b)
substType x t (TyVar y) = if x == y then termToType t else TyVar y
substType x t ty = ty

-----------------------------------------------------
-- 12. Term to Type conversion
-----------------------------------------------------
termToType : Term -> Type
termToType (var "Type") = TyType 0
termToType (var "Nat") = TyNat
termToType (var "Unit") = TyUnit
termToType (var x) = TyVar x
termToType t = TyVar (show t)  -- fallback

-----------------------------------------------------
-- 13. Top-level API
-----------------------------------------------------

-- typecheck a term against a type
typecheckTerm : Term -> Type -> Result ()
typecheckTerm t ty = check emptyCtx emptyDimCtx t ty

-- infer the type of a term
inferType : Term -> Result Type
inferType t = infer emptyCtx emptyDimCtx t

-- typecheck a definition
typecheckDef : String -> Term -> Type -> Result ()
typecheckDef name body ty = check emptyCtx emptyDimCtx body ty

-- format errors for display
formatErrors : List TypeError -> String
formatErrors [] = "No errors"
formatErrors errs = concatMap formatError errs
  where
    formatError : TypeError -> String
    formatError e =
      let locStr = case e.loc of
            Just l  -> l.file ++ ":" ++ show l.line ++ ":" ++ show l.column ++ ": "
            Nothing -> ""
          sevStr = case e.severity of
            Error   -> "error: "
            Warning -> "warning: "
            Info    -> "info: "
          expStr = case e.expected of
            Just t  -> "\n  expected: " ++ showType t
            Nothing -> ""
          actStr = case e.actual of
            Just t  -> "\n  actual: " ++ showType t
            Nothing -> ""
      in locStr ++ sevStr ++ e.message ++ expStr ++ actStr ++ "\n"

showType : Type -> String
showType (TyType n) = "Type" ++ show n
showType (TyPi x a b) = "(" ++ x ++ " : " ++ showType a ++ ") -> " ++ showType b
showType (TyPath a x y) = "Path " ++ showType a ++ " " ++ show x ++ " " ++ show y
showType (TySigma x a b) = "Σ(" ++ x ++ " : " ++ showType a ++ "). " ++ showType b
showType TyNat = "Nat"
showType TyUnit = "Unit"
showType TyEmpty = "Empty"
showType (TyVar x) = x
showType (TyHIT name args) = name ++ " " ++ concatMap (\a -> showType a ++ " ") args

-----------------------------------------------------
-- 14. Tests
-----------------------------------------------------

-- Identity function: λ(x : Type). x
test_id : Result Type
test_id = inferType (lam "x" (var "Type") (var "x"))
-- Expected: Ok (TyPi "x" (TyType 0) (TyType 0))

-- Application of identity
test_id_app : Result Type
test_id_app = inferType (app (lam "x" (var "Type") (var "x")) (var "Nat"))
-- Expected: Ok TyNat

-- Reflexivity path
test_refl : Result Type
test_refl = inferType (refl (var "a"))
-- Expected: Ok (TyPath (TyVar "a_type") (var "a") (var "a"))

-- Path composition
test_comp : Result ()
test_comp = typecheckTerm
  (path_comp (refl (var "a")) (refl (var "a")))
  (TyPath (TyVar "A") (var "a") (var "a"))

-- Circle base
test_base : Result Type
test_base = inferType (hit "base")
-- Expected: Ok (TyHIT "S1" [])

-- Circle loop
test_loop : Result Type
test_loop = inferType (hit "loop")
-- Expected: Ok (TyPath (TyHIT "S1" []) (hit "base") (hit "base"))

-----------------------------------------------------
-- 15. Integration with RedttElab attributes
-----------------------------------------------------
-- The attribute grammar in RedttElab.lego defines:
--   attrs TypeCheck { syn type : Type ; inh ctx : Context ; ... }
--   attrs CubicalCheck { inh dimctx : DimContext ; syn isCofib : Bool ; }
--   attrs Bidirectional { inh mode : Mode ; syn ok : Bool ; }
--
-- This module provides the evaluation functions for those attributes.
-- The connection:
--   - TypeCheck.ctx = Context from this module
--   - TypeCheck.type = Type from this module
--   - CubicalCheck.dimctx = DimContext from this module
--   - Bidirectional.mode = Mode from this module

-- Evaluate TypeCheck.type synthesized attribute
evalTypeAttr : Context -> DimContext -> Term -> Result Type
evalTypeAttr = infer

-- Evaluate Bidirectional.ok synthesized attribute
evalBidirOk : Context -> DimContext -> Mode -> Term -> Result Bool
evalBidirOk ctx dctx Infer t =
  case infer ctx dctx t of
    Ok _ _  -> pure True
    Failed _ -> pure False
evalBidirOk ctx dctx (Check expected) t =
  case check ctx dctx t expected of
    Ok () _  -> pure True
    Failed _ -> pure False

-- Evaluate CubicalCheck.isCofib synthesized attribute
evalIsCofib : DimContext -> Term -> Bool
evalIsCofib dctx (var "1") = True   -- i1 (endpoint)
evalIsCofib dctx (var "0") = True   -- i0 (endpoint)
evalIsCofib dctx (app (var "∧") _) = True  -- meet
evalIsCofib dctx (app (var "∨") _) = True  -- join
evalIsCofib dctx (app (var "~") _) = True  -- negation
evalIsCofib dctx _ = False
