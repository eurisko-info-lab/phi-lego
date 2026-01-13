{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE DeriveFunctor #-}
-- | Rewrite Machine for Lego
--
-- A heap-based machine for term rewriting with:
--   - Handle-based allocation (interaction net style)
--   - Explicit environment stack for scoped bindings (Γ)
--   - Dimension environment for cubical interval variables (Δ)
--
-- == Key Insight: Dimension Variables ≠ Term Variables
--
-- Cubical type theory requires separating:
--   Γ: Term variables - capture-avoiding substitution, λ-binding
--   Δ: Dimension variables - algebraic substitution, De Morgan algebra
--
-- This separation is what makes cubical reduction correct.
--
-- == Instruction Set
--
-- The machine executes a sequence of instructions:
--   MATCH p   - Match pattern p against current redex
--   EMIT t    - Emit template t as result
--   PUSH_ENV  - Push new scope for bindings
--   POP_ENV   - Pop scope
--   BIND x    - Bind name x to last allocated handle
--   FAIL      - Explicit failure
--   DIM_BIND  - Bind dimension variable
--   DIM_SUBST - Substitute dimension expression
--
module Lego.RewriteMachine
  ( -- * Handles and Nodes
    Handle(..)
  , Node(..)
    -- * Dimensions (Cubical)
  , Dim(..)
  , substDim
  , normDim
  , freeDims
    -- * Terms
  , Term(..)
    -- * Patterns and Templates
  , Pattern(..)
  , Template(..)
    -- * Heap
  , Object(..)
  , Heap(..)
  , emptyHeap
    -- * Environment
  , Env(..)
  , EnvStack
  , lookupEnv
    -- * State
  , State(..)
  , emptyState
    -- * Strategies
  , Strategy(..)
    -- * Instructions
  , Instr(..)
    -- * Operations
  , freshHandle
  , freshHandles
  , pushEnvOp
  , popEnvOp
  , bindVarOp
  , bindDimOp
  , insertHeap
  , lookupHeap
    -- * Matching
  , match
    -- * Emission
  , emit
    -- * Execution
  , step
  , run
  , findRedex
  ) where

import qualified Data.Map as M
import qualified Data.Set as S
import Control.Monad (foldM)

type Name = String

--------------------------------------------------------------------------------
-- Handles and Nodes
--------------------------------------------------------------------------------

-- | Handles point to heap objects
newtype Handle = H Int
  deriving (Eq, Ord, Show)

-- | Node in interaction net style
data Node = Node
  { nodeType  :: String
  , nodePorts :: [Handle]
  } deriving (Eq, Show)

--------------------------------------------------------------------------------
-- Cubical Dimensions
--------------------------------------------------------------------------------

-- | Dimension expressions (De Morgan algebra on the interval I)
--
-- Laws:
--   D0 ∧ x = D0           (zero absorbs)
--   D1 ∧ x = x            (one is identity)
--   D0 ∨ x = x            (zero is identity)
--   D1 ∨ x = D1           (one absorbs)
--   ~D0 = D1              (reversal)
--   ~D1 = D0
--   ~~x = x               (involution)
--   ~(x ∧ y) = ~x ∨ ~y    (De Morgan)
--   ~(x ∨ y) = ~x ∧ ~y    (De Morgan)
--
data Dim
  = DVar Name     -- Dimension variable
  | D0            -- Left endpoint (i0)
  | D1            -- Right endpoint (i1)
  | DNot Dim      -- Reversal (~)
  | DAnd Dim Dim  -- Meet (∧)
  | DOr  Dim Dim  -- Join (∨)
  deriving (Eq, Ord, Show)

-- | Substitute dimension variable: d[x := e]
substDim :: Name -> Dim -> Dim -> Dim
substDim x d = \case
  DVar y | x == y -> d
  DVar y          -> DVar y
  D0              -> D0
  D1              -> D1
  DNot e          -> DNot (substDim x d e)
  DAnd a b        -> DAnd (substDim x d a) (substDim x d b)
  DOr a b         -> DOr  (substDim x d a) (substDim x d b)

-- | Normalize dimension expression (reduce algebraically)
--
-- This applies De Morgan laws and endpoint simplifications.
-- Returns normalized dimension (endpoints propagate).
normDim :: Dim -> Dim
normDim = \case
  -- Endpoint cases
  D0 -> D0
  D1 -> D1
  DVar x -> DVar x
  
  -- Reversal
  DNot D0 -> D1
  DNot D1 -> D0
  DNot (DNot x) -> normDim x              -- Involution
  DNot (DAnd a b) -> normDim (DOr (DNot a) (DNot b))   -- De Morgan
  DNot (DOr a b) -> normDim (DAnd (DNot a) (DNot b))   -- De Morgan
  DNot x -> DNot (normDim x)
  
  -- Meet (∧)
  DAnd a b -> case (normDim a, normDim b) of
    (D0, _) -> D0                         -- Zero absorbs
    (_, D0) -> D0
    (D1, y) -> y                          -- One is identity
    (x, D1) -> x
    (x, y) | x == y -> x                  -- Idempotent
    (x, y) -> DAnd x y
    
  -- Join (∨)
  DOr a b -> case (normDim a, normDim b) of
    (D1, _) -> D1                         -- One absorbs
    (_, D1) -> D1
    (D0, y) -> y                          -- Zero is identity
    (x, D0) -> x
    (x, y) | x == y -> x                  -- Idempotent
    (x, y) -> DOr x y

-- | Free dimension variables in expression
freeDims :: Dim -> S.Set Name
freeDims = \case
  DVar x -> S.singleton x
  D0 -> S.empty
  D1 -> S.empty
  DNot d -> freeDims d
  DAnd a b -> S.union (freeDims a) (freeDims b)
  DOr a b -> S.union (freeDims a) (freeDims b)

--------------------------------------------------------------------------------
-- Terms
--------------------------------------------------------------------------------

-- | Terms include both lambda terms and cubical primitives
data Term
  -- Lambda calculus
  = TVar String           -- Variable
  | TLam String Term      -- Lambda abstraction
  | TApp Term Term        -- Application
  -- Cubical primitives
  | TLamI Name Term       -- Path abstraction: (λᵢ i . body)
  | TAppI Term Dim        -- Path application: (@ p r)
  | TTransp Term Dim Term -- Transport: transp A φ a
  | TCoe Term Dim Dim Term -- Coercion: coe A r r' a (generalized transport)
  | TRefl Term            -- Reflexivity: refl a
  -- Literals and constructors
  | TLit String           -- Literal
  | TCon String [Term]    -- Constructor application
  deriving (Eq, Show)

-- | Substitute term variable in term: t[x := s]
-- (Reserved for future cubical rewriting)
_substTermVar :: Name -> Term -> Term -> Term
_substTermVar x s = go
  where
    go = \case
      TVar y | x == y  -> s
             | otherwise -> TVar y
      TLam y body
        | x == y    -> TLam y body  -- Shadowed
        | otherwise -> TLam y (go body)
      TApp f a -> TApp (go f) (go a)
      TLamI i body -> TLamI i (go body)  -- Dim binder, no capture
      TAppI p r -> TAppI (go p) r
      TTransp a phi a0 -> TTransp (go a) phi (go a0)
      TCoe a r r' a0 -> TCoe (go a) r r' (go a0)
      TRefl a -> TRefl (go a)
      TLit l -> TLit l
      TCon c args -> TCon c (map go args)

-- | Substitute dimension variable in term: t[i := r]
-- (Reserved for future cubical rewriting)
_substTermDim :: Name -> Dim -> Term -> Term
_substTermDim i r = go
  where
    go = \case
      TVar x -> TVar x
      TLam x body -> TLam x (go body)
      TApp f a -> TApp (go f) (go a)
      TLamI j body
        | i == j    -> TLamI j body  -- Shadowed
        | otherwise -> TLamI j (go body)
      TAppI p d -> TAppI (go p) (substDim i r d)
      TTransp a phi a0 -> TTransp (go a) (substDim i r phi) (go a0)
      TCoe a d0 d1 a0 -> TCoe (go a) (substDim i r d0) (substDim i r d1) (go a0)
      TRefl a -> TRefl (go a)
      TLit l -> TLit l
      TCon c args -> TCon c (map go args)

--------------------------------------------------------------------------------
-- Patterns and Templates
--------------------------------------------------------------------------------

-- | Patterns for matching
data Pattern
  = PVar Name               -- Variable (captures anything)
  | PLit String             -- Literal match
  | PNode String [Pattern]  -- Node with type and port patterns
  | PDim Dim                -- Dimension pattern (matches dimension expressions)
  | PWild                   -- Wildcard (matches anything, doesn't bind)
  deriving (Eq, Show)

-- | Templates for emission
data Template
  = TmVar Name                -- Reference to bound variable
  | TmLit String              -- Literal
  | TmNode String [Template]  -- Construct node
  | TmEdge Handle Handle      -- Create edge
  | TmDim Dim                 -- Dimension expression
  | TmSubstDim Name Dim Template  -- Dimension substitution: body[x := d]
  deriving (Eq, Show)

--------------------------------------------------------------------------------
-- Heap Objects
--------------------------------------------------------------------------------

-- | Objects stored in the heap
data Object
  = ObjTerm Term          -- A term
  | ObjNode Node          -- An interaction net node
  | ObjEdge Handle Handle -- An edge between handles
  | ObjDim Dim            -- A dimension expression (for cubical)
  deriving (Eq, Show)

data Heap = Heap
  { heapObjects :: M.Map Handle Object
  , heapCounter :: Int
  , heapRedexes :: [Handle]  -- Active redex locations (optimization)
  } deriving (Eq, Show)

emptyHeap :: Heap
emptyHeap = Heap M.empty 0 []

--------------------------------------------------------------------------------
-- Environment
--------------------------------------------------------------------------------

-- | Persistent environment (linked list of bindings)
data Env
  = Empty
  | Bind Name Handle Env
  deriving (Eq, Show)

-- | Environment stack for scoped bindings
type EnvStack = [Env]

lookupEnv :: Name -> Env -> Maybe Handle
lookupEnv _ Empty = Nothing
lookupEnv x (Bind y h rest)
  | x == y    = Just h
  | otherwise = lookupEnv x rest

--------------------------------------------------------------------------------
-- Machine State
--------------------------------------------------------------------------------

-- | Machine state with separated term and dimension environments
--
-- Key invariant: Cubical endpoints (i0, i1) are NOT heap allocated.
-- They are compile-time algebraic objects evaluated during rewriting.
data State = State
  { heap     :: Heap
  , envStack :: EnvStack       -- Γ: scoped term variable bindings
  , dimEnv   :: M.Map Name Dim -- Δ: dimension variable bindings (flat, no scoping)
  , dimStack :: [M.Map Name Dim]  -- Stack for dimension scopes
  } deriving (Eq, Show)

emptyState :: State
emptyState = State emptyHeap [Empty] M.empty []

-- | Push dimension scope
pushDimScope :: State -> State
pushDimScope st = st { dimStack = dimEnv st : dimStack st }

-- | Pop dimension scope
popDimScope :: State -> State
popDimScope st = case dimStack st of
  []     -> st
  d : ds -> st { dimEnv = d, dimStack = ds }

-- | Bind dimension variable
bindDimOp :: Name -> Dim -> State -> State
bindDimOp x d st = st { dimEnv = M.insert x d (dimEnv st) }

-- | Lookup dimension variable
-- (Reserved for future cubical rewriting)
_lookupDim :: Name -> State -> Maybe Dim
_lookupDim x st = M.lookup x (dimEnv st)

--------------------------------------------------------------------------------
-- Strategies
--------------------------------------------------------------------------------

-- | Reduction strategy
data Strategy
  = Outermost   -- Lazy evaluation
  | Innermost   -- Eager evaluation  
  | Optimal     -- Interaction net style (no duplication)
  deriving (Eq, Show)

--------------------------------------------------------------------------------
-- Instructions
--------------------------------------------------------------------------------

-- | Machine instructions
data Instr
  -- Environment control
  = PUSH_ENV              -- Push new term scope
  | POP_ENV               -- Pop term scope
  | BIND Name             -- Bind name to last allocated handle
  -- Dimension control (separate from term env!)
  | DIM_PUSH              -- Push dimension scope
  | DIM_POP               -- Pop dimension scope
  | DIM_BIND Name Dim     -- Bind dimension variable
  -- Rewriting
  | MATCH Pattern         -- Match pattern against current focus
  | EMIT Template         -- Emit result
  | FAIL                  -- Explicit failure
  -- Cubical-specific
  | NORM_DIM Name         -- Normalize dimension expression at name
  deriving (Eq, Show)

--------------------------------------------------------------------------------
-- Handle Allocation
--------------------------------------------------------------------------------

-- | Allocate a fresh handle
freshHandle :: State -> (Handle, State)
freshHandle st =
  let h = Heap { heapObjects = heapObjects (heap st)
               , heapCounter = heapCounter (heap st) + 1
               , heapRedexes = heapRedexes (heap st) }
  in (H (heapCounter (heap st)), st { heap = h })

-- | Allocate multiple fresh handles
freshHandles :: Int -> State -> ([Handle], State)
freshHandles n st =
  let start = heapCounter (heap st)
      hs = [ H i | i <- [start .. start + n - 1] ]
      h' = (heap st) { heapCounter = start + n }
  in (hs, st { heap = h' })

--------------------------------------------------------------------------------
-- Environment Operations
--------------------------------------------------------------------------------

-- | Push a new scope
pushEnvOp :: State -> State
pushEnvOp st =
  st { envStack = Empty : envStack st }

-- | Pop scope
popEnvOp :: State -> State
popEnvOp st =
  st { envStack = drop 1 (envStack st) }

-- | Bind variable in top environment
bindVarOp :: Name -> Handle -> State -> State
bindVarOp x h st =
  case envStack st of
    []     -> st { envStack = [Bind x h Empty] }
    e : es -> st { envStack = Bind x h e : es }

-- | Get last allocated handle (for BIND instruction)
lastAllocatedHandle :: State -> Maybe Handle
lastAllocatedHandle st =
  let ctr = heapCounter (heap st)
  in if ctr > 0 then Just (H (ctr - 1)) else Nothing

--------------------------------------------------------------------------------
-- Heap Operations
--------------------------------------------------------------------------------

-- | Insert object into heap
insertHeap :: Handle -> Object -> State -> State
insertHeap h obj st =
  let heap' = (heap st) { heapObjects = M.insert h obj (heapObjects (heap st)) }
  in st { heap = heap' }

-- | Lookup object in heap
lookupHeap :: Handle -> State -> Maybe Object
lookupHeap h st = M.lookup h (heapObjects (heap st))

--------------------------------------------------------------------------------
-- Pattern Matching
--------------------------------------------------------------------------------

-- | Match pattern against heap object
-- Returns updated state with bound variables on success
match :: Pattern -> Handle -> State -> Maybe State
match pat h st = do
  obj <- lookupHeap h st
  case (pat, obj) of
    -- Variable: captures anything
    (PVar x, _) ->
      Just (bindVarOp x h st)
    
    -- Wildcard: matches anything, no binding
    (PWild, _) ->
      Just st
    
    -- Literal match
    (PLit s, ObjTerm (TLit s')) | s == s' ->
      Just st
    
    -- Node match: type must match, recursively match ports
    (PNode t ps, ObjNode n)
      | nodeType n == t && length ps == length (nodePorts n) ->
          foldM (\s (p, h') -> match p h' s)
                st
                (zip ps (nodePorts n))
    
    -- Dimension pattern: match dimension expressions
    (PDim d, ObjDim d') | normDim d == normDim d' ->
      Just st
    
    _ -> Nothing

--------------------------------------------------------------------------------
-- Template Emission
--------------------------------------------------------------------------------

-- | Emit template to heap, returning handle to result
emit :: Template -> State -> (Handle, State)
emit (TmVar x) st =
  case envStack st of
    []    -> error "emit: empty environment stack"
    e : _ -> case lookupEnv x e of
      Just h  -> (h, st)
      Nothing -> 
        -- Try dimension environment
        case M.lookup x (dimEnv st) of
          Just d  -> 
            let (h, st1) = freshHandle st
            in (h, insertHeap h (ObjDim d) st1)
          Nothing -> error $ "emit: unbound variable " ++ x

emit (TmLit s) st =
  let (h, st1) = freshHandle st
  in (h, insertHeap h (ObjTerm (TLit s)) st1)

emit (TmNode ty ports) st =
  let (portHandles, st1) = emitPorts ports st
      (h, st2) = freshHandle st1
      node = Node ty portHandles
  in (h, insertHeap h (ObjNode node) st2)

emit (TmEdge h1 h2) st =
  let (h, st1) = freshHandle st
  in (h, insertHeap h (ObjEdge h1 h2) st1)

emit (TmDim d) st =
  let (h, st1) = freshHandle st
      d' = normDim d  -- Normalize dimension
  in (h, insertHeap h (ObjDim d') st1)

emit (TmSubstDim x d body) st =
  -- First, bind the dimension substitution
  let st1 = bindDimOp x d st
      (h, st2) = emit body st1
  in (h, st2)

-- | Emit list of templates
emitPorts :: [Template] -> State -> ([Handle], State)
emitPorts [] st = ([], st)
emitPorts (t:ts) st =
  let (h, st1) = emit t st
      (hs, st2) = emitPorts ts st1
  in (h:hs, st2)

--------------------------------------------------------------------------------
-- Find Redex
--------------------------------------------------------------------------------

-- | Find a redex matching the pattern
-- 
-- Searches heap for objects matching the pattern.
-- For interaction nets, this looks for active pairs (connected principal ports).
findRedex :: Pattern -> State -> Maybe Handle
findRedex pat st = 
  -- Search all heap objects for a match
  let candidates = M.toList (heapObjects (heap st))
      tryMatch (h, obj) = case pat of
        PNode t _ -> case obj of
          ObjNode n | nodeType n == t -> Just h
          _ -> Nothing
        PLit s -> case obj of
          ObjTerm (TLit s') | s == s' -> Just h
          _ -> Nothing
        PDim d -> case obj of
          ObjDim d' | normDim d == normDim d' -> Just h
          _ -> Nothing
        PVar _ -> Just h  -- Variable matches anything
        PWild -> Just h
  in case filter (\h -> tryMatch h /= Nothing) candidates of
       ((h, _):_) -> Just h
       [] -> Nothing

-- | Find active pair in interaction net (two nodes connected at principal ports)
-- (Reserved for future optimal reduction)
_findActivePair :: State -> Maybe (Handle, Handle)
_findActivePair st =
  let edges = [(h1, h2) | (_, ObjEdge h1 h2) <- M.toList (heapObjects (heap st))]
      isPrincipal h = case lookupHeap h st of
        Just (ObjNode _) -> True  -- Simplified: all nodes have principal port
        _ -> False
  in case filter (\(h1, h2) -> isPrincipal h1 && isPrincipal h2) edges of
       (pair:_) -> Just pair
       [] -> Nothing

--------------------------------------------------------------------------------
-- Instruction Execution
--------------------------------------------------------------------------------

-- | Execute a single instruction
step :: Instr -> State -> Either String State

-- Environment control
step PUSH_ENV st =
  Right (pushEnvOp st)

step POP_ENV st =
  Right (popEnvOp st)

step (BIND x) st =
  case lastAllocatedHandle st of
    Just h  -> Right (bindVarOp x h st)
    Nothing -> Left "BIND: no value to bind"

-- Dimension control
step DIM_PUSH st =
  Right (pushDimScope st)

step DIM_POP st =
  Right (popDimScope st)

step (DIM_BIND x d) st =
  -- Normalize dimension before binding
  Right (bindDimOp x (normDim d) st)

step (NORM_DIM x) st =
  case M.lookup x (dimEnv st) of
    Just d  -> Right (bindDimOp x (normDim d) st)
    Nothing -> Left $ "NORM_DIM: unbound dimension " ++ x

-- Rewriting
step (MATCH p) st =
  case findRedex p st of
    Just h  -> maybe (Left "MATCH: pattern match failed") Right (match p h st)
    Nothing -> Left "MATCH: no redex found"

step (EMIT t) st =
  let (_h, st') = emit t st
  in Right st'

step FAIL _ =
  Left "explicit failure"

--------------------------------------------------------------------------------
-- Run Machine
--------------------------------------------------------------------------------

-- | Run a sequence of instructions with a given strategy
run :: Strategy -> [Instr] -> State -> Either String State
run _ [] st = Right st
run strat (i:is) st = do
  st' <- step i st
  run strat is st'

--------------------------------------------------------------------------------
-- Cubical Reduction Rules (as instruction sequences)
--------------------------------------------------------------------------------

-- | Path beta: (λᵢ i. body) @ r → body[i := r]
-- (Reserved for cubical instruction generation)
_pathBetaInstrs :: Name -> Pattern -> Template -> [Instr]
_pathBetaInstrs dimVar bodyPat bodyTmpl =
  [ MATCH (PNode "pathapp" [PNode "pathabs" [PVar dimVar, bodyPat], PVar "r"])
  , DIM_BIND dimVar (DVar "r")  -- Bind dimension
  , EMIT bodyTmpl               -- Emit with substitution
  ]

-- | Transport at i1: transp A i1 a → a
-- (Reserved for cubical instruction generation)
_transpI1Instrs :: [Instr]
_transpI1Instrs =
  [ MATCH (PNode "transp" [PWild, PDim D1, PVar "a"])
  , EMIT (TmVar "a")
  ]

-- | Coe when endpoints equal: coe A r r a → a
-- (Reserved for cubical instruction generation)
_coeSameInstrs :: [Instr]
_coeSameInstrs =
  [ MATCH (PNode "coe" [PWild, PVar "r", PVar "r'", PVar "a"])
  -- Guard: r == r' (would need conditional instruction)
  , EMIT (TmVar "a")
  ]
