import qualified Data.Map.Strict as Map
import Control.Monad (foldM, msum)
import Data.Maybe (fromMaybe)

data Term = Var String       -- Object-level variable (matches literally)
          | MetaVar String   -- Pattern metavariable (binds to anything)
          | Str String
          | Num Int
          | Node String [Term]
          deriving (Show, Eq)

type Env = Map.Map String (Either Term [Term])

match :: Term -> Term -> Maybe Env
match (MetaVar v) t = Just (Map.singleton v (Left t))
match (Var v1) (Var v2) | v1 == v2 = Just Map.empty
match (Str s1) (Str s2) | s1 == s2 = Just Map.empty
match (Num n1) (Num n2) | n1 == n2 = Just Map.empty
match (Node l1 cs1) (Node l2 cs2) | l1 == l2 =
  let n = length cs1
  in if n == 0 
     then if null cs2 then Just Map.empty else Nothing 
     else let prefix_len = n - 1
          in if prefix_len > length cs2 
             then Nothing 
             else let prefix_cs1 = take prefix_len cs1
                      prefix_cs2 = take prefix_len cs2
                      tail_cs2 = drop prefix_len cs2
                      last_p = cs1 !! prefix_len
                      m_prefix = foldM (\acc (p, t) -> union acc <$> match p t) Map.empty (zip prefix_cs1 prefix_cs2)
                      m_tail = case last_p of
                        MetaVar v -> Just (Map.singleton v (Right tail_cs2))
                        _ -> case tail_cs2 of
                          [single] -> match last_p single  -- exact match for single element
                          _ -> Nothing  -- non-MetaVar can't match multiple elements
                  in do { penv <- m_prefix; tenv <- m_tail; return (union penv tenv) }
match _ _ = Nothing

union :: Env -> Env -> Env
union = Map.union -- assuming no conflicts for simplicity

substitute :: Env -> Term -> Term
substitute env (MetaVar v) = case Map.lookup v env of
  Just (Left t) -> substitute env t
  Just (Right ts) -> error "List variable used as scalar term"
  Nothing -> MetaVar v
substitute env (Var v) = Var v  -- Object-level vars don't get substituted
substitute env (Str s) = Str s
substitute env (Num n) = Num n
substitute env (Node l cs) = Node l (concatMap (subList env) cs)
  where
    subList :: Env -> Term -> [Term]
    subList env (MetaVar v) = case Map.lookup v env of
      Just (Left t) -> [substitute env t]
      Just (Right ts) -> map (substitute env) ts
      Nothing -> [MetaVar v]
    subList env other = [substitute env other]

type Rule = (String, Term, Term)

-- Helper for metavariables in patterns
mv :: String -> Term
mv = MetaVar

rules :: [Rule]
rules = [
  ("tokenize_scoped", Node "tokenize" [mv "piece", mv "t"], Node "node" [Var "tokenize", mv "piece", mv "t"]),
  ("syntax_literal_ok", Node "literal" [mv "x", Var "syntax"], mv "x"),
  ("content_literal_strict", Node "literal" [mv "x", Var "content"], Node "node" [Var "error", mv "x"]),
  ("pushout_tokens", Node "pushout" [mv "p1", mv "p2", mv "p3"], Node "token-scope" [mv "p3", Node "node" [Var "merge", Node "token-scope" [mv "p1"], Node "token-scope" [mv "p2"]]]),
  ("select_context", Node "select-context" [Node "budget" [mv "b"], Node "context" [mv "atoms"]], Node "context" [Node "node" [Var "filter-by-budget", mv "b", mv "atoms"]]),
  ("ide_to_prompt", Node "ide" [mv "g", mv "ctx", mv "focus"], Node "prompt" [mv "ctx"]),
  ("apply_answer", Node "node" [Var "apply", Node "answer" [mv "t"], Node "ide" [mv "g", mv "ctx", mv "focus"]], Node "ide" [mv "g", mv "ctx", mv "t"]),
  ("step_rewrite", Node "step" [Node "node" [Var "rewrite", mv "p", mv "t"]], Node "step" [mv "t"]),
  ("normalize_step", Node "normal" [Node "step" [mv "t"]], Node "normal" [mv "t"]),
  ("normalize_done", Node "normal" [mv "t"], Node "nf" [mv "t"]),
  ("grammar_to_atom", Node "grammarFrag" [mv "g"], Node "atom" [Var "grammar", mv "g", Num 5, Num 10, Num 8]),
  ("rewrite_dependency", Node "rewrite-def" [mv "r1", mv "p", mv "t"], Node "depends" [mv "r1", Node "node" [Var "find-rewrites", mv "t"]]),
  ("rewrite_to_atom", Node "rewrite-def" [mv "id", mv "p", mv "t"], Node "atom" [Var "rule", Node "node" [Var "rewrite", mv "p", mv "t"], Num 7, Num 9, Num 9]),
  ("ide_ext_to_prompt", Node "ide+" [mv "g", mv "ctx", mv "deps", mv "focus"], Node "prompt" [Node "context" [mv "ctx", Node "atom" [Var "example", mv "deps", Num 3, Num 6, Num 4]]]),
  ("visualize_node", Node "node" [mv "type", mv "id"], Node "viz-node" [mv "id", mv "type", Num 0, Num 0]),
  ("visualize_edge", Node "edge" [Node "port" [mv "n1", mv "p1"], Node "port" [mv "n2", mv "p2"]], Node "viz-edge" [mv "n1", mv "n2", Str "."]),
  ("visualize_net", Node "net" [mv "xs"], Node "viz-graph" [Node "map" [Var "visualize_node", Node "nodes" [mv "xs"]], Node "map" [Var "visualize_edge", Node "edges" [mv "xs"]]]),
  ("diff_context", Node "diff" [mv "ctx1", mv "ctx2"], Node "diff-context" [Node "map" [Var "added", Node "minus" [mv "ctx2", mv "ctx1"]], Node "map" [Var "removed", Node "minus" [mv "ctx1", mv "ctx2"]], Node "map" [Var "changed", Node "intersectChanged" [mv "ctx1", mv "ctx2"]]]),
  ("pushout_incremental", Node "pushout-state" [mv "g", mv "ctx", Node "dirty" [mv "p"]], Node "pushout-state" [Node "mergeGrammar" [mv "g", Node "grammarOf" [mv "p"]], Node "mergeContext" [mv "ctx", Node "contextOf" [mv "p"]], Var "nil"]),
  ("edit_is_path", Node "edit" [mv "t1", mv "t2"], Node "path" [Var "i", mv "t1", mv "t2"]),
  ("apply_path_i0", Node "@" [Node "path" [mv "i", mv "t1", mv "t2"], Var "i0"], mv "t1"),
  ("apply_path_i1", Node "@" [Node "path" [mv "i", mv "t1", mv "t2"], Var "i1"], mv "t2"),
  ("rewrite_as_path", Node "rewrite" [mv "p", mv "t"], Node "path" [Var "i", mv "p", mv "t"]),
  ("path_comp_def", Node "path-comp" [mv "i", Node "path" [mv "i", mv "a", mv "b"], Node "path" [mv "i", mv "b", mv "c"]], Node "path" [mv "i", mv "a", mv "c"]),
  ("path_inv_def", Node "path-inv" [Node "path" [mv "i", mv "a", mv "b"]], Node "path" [mv "i", mv "b", mv "a"]),
  ("path_comp_i0", Node "@" [Node "path-comp" [mv "i", mv "p", mv "q"], Var "i0"], Node "@" [mv "p", Var "i0"]),
  ("path_comp_i1", Node "@" [Node "path-comp" [mv "i", mv "p", mv "q"], Var "i1"], Node "@" [mv "q", Var "i1"]),
  ("atom_cost", Node "atom" [mv "k", mv "v", mv "c", mv "r", mv "p"], Node "weighted" [Node "atom-costed" [mv "k", mv "v"], mv "c"]),
  ("context_select_budget", Node "select-context" [Node "budget" [mv "b"], mv "atoms"], Node "takeWhileCost" [mv "b", Node "sortBy" [Var "relevance", mv "atoms"]]),
  ("pc_edit_sound", Node "pc-edit" [Node "edit" [mv "t1", mv "t2"], mv "pf"], Node "path" [Var "i", mv "t1", mv "t2"]),
  ("Eq_refl", Node "reflJ" [mv "t"], Node "path" [Var "i", mv "t", mv "t"]),
  ("Eq_sym", Node "symJ" [Node "path" [mv "i", mv "a", mv "b"]], Node "path" [mv "i", mv "b", mv "a"]),
  ("Eq_trans", Node "transJ" [Node "path" [mv "i", mv "a", mv "b"], Node "path" [mv "i", mv "b", mv "c"]], Node "path" [mv "i", mv "a", mv "c"]),
  ("edit_correct", Node "preserves" [Node "edit" [mv "t1", mv "t2"]], Node "Eq" [mv "t1", mv "t2"]),
  ("pc_edit_correct", Node "pc-edit" [Node "edit" [mv "t1", mv "t2"], mv "pf"], Node "Eq" [mv "t1", mv "t2"]),
  ("refactor_correct", Node "refactor" [mv "es"], Node "path" [Var "i", Node "source" [mv "es"], Node "target" [mv "es"]]),
  ("refactor_assoc", Node "path-comp" [mv "i", Node "path-comp" [mv "i", mv "p", mv "q"], mv "r"], Node "path-comp" [mv "i", mv "p", Node "path-comp" [mv "i", mv "q", mv "r"]]),
  ("budget_context_sound", Node "select-context" [Node "budget" [mv "b"], mv "ctx"], Node "contextEq" [Node "select-context" [Node "budget" [mv "b"], mv "ctx"], mv "ctx"]),
  ("grammar_pushout_coherent", Node "pushout" [mv "G1", mv "G2"], Node "coherent" [Node "pushout" [mv "G1", mv "G2"]]),
  ("rewrite_confluence", Node "rewrite" [mv "t"], Node "Eq" [Node "normalize" [mv "t"], Node "normalize" [Node "rewrite" [mv "t"]]]),
  ("IDE_correct", Node "correctIDE" [Node "IDE" [mv "G", mv "C", mv "E"]], Node "forall" [Var "t", Node "Eq" [Var "t", Node "apply-edits" [Node "suggest" [mv "E", Node "select-context" [Node "budget" [mv "b"], mv "C"]], Var "t"]]]),
  ("normal_lam", Node "normal" [Node "λ" [mv "x", mv "body"]], Var "true"),
  ("normal_path", Node "normal" [Node "λᵢ" [mv "i", mv "body"]], Var "true"),
  ("normal_constr", Node "normal" [mv "c", mv "args"], Node "all-normal" [mv "args"]),
  ("neutral_var", Node "neutral" [mv "x"], Var "true"),
  ("normal_neutral", Node "neutral" [mv "t"], Node "normal" [mv "t"]),
  ("rewrite_step", Node "rewrite" [mv "t"], Node "step" [mv "t", Node "normalize" [mv "t"]]),
  ("terminates_def", Node "terminates" [mv "t"], Node "exists" [Var "n", Node "normal" [Node "normalize^" [Var "n", mv "t"]]]),
  ("global_termination", Node "wellformed" [mv "t"], Node "SN" [mv "t"]),
  ("SN_implies_terminates", Node "SN" [mv "t"], Node "terminates" [mv "t"]),
  ("canonical_bool_true", Node "canonical" [Var "true"], Var "true"),
  ("canonical_bool_false", Node "canonical" [Var "false"], Var "true"),
  ("canonical_nat_zero", Node "canonical" [Var "zero"], Var "true"),
  ("canonical_nat_succ", Node "canonical" [Node "succ" [mv "n"]], Node "canonical" [mv "n"]),
  ("canonicity_thm", Node "closed" [mv "t"], Node "exists" [Var "v", Node "∧" [Node "canonical" [Var "v"], Node "Eq" [Node "normalize" [mv "t"], Var "v"]]]),
  ("path_endpoint_canonicity", Node "path" [mv "i", mv "a", mv "b"], Node "∧" [Node "canonical" [mv "a"], Node "canonical" [mv "b"]]),
  ("IDE_normalizes", Node "correctIDE" [mv "ide"], Node "forall" [Var "t", Node "terminates" [Node "apply-edits" [Node "suggest" [mv "ide", Var "ctx"], Var "t"]]]),
  ("IDE_canonical", Node "correctIDE" [mv "ide"], Node "forall" [Var "t", Node "=" [Node "canonical" [Node "normalize" [Var "t"]], Node "canonical" [Node "normalize" [Node "apply-edits" [Node "suggest" [mv "ide", Var "ctx"], Var "t"]]]]]),
  ("joinable_def", Node "joinable" [mv "t", mv "u", mv "v"], Node "∧" [Node "reduces*" [mv "t", mv "v"], Node "reduces*" [mv "u", mv "v"]]),
  ("confluence_thm", Node "wellformed" [mv "t"], Node "forall" [Var "u1", Var "u2", Node "→" [Node "∧" [Node "step*" [mv "t", Var "u1"], Node "step*" [mv "t", Var "u2"]], Node "exists" [Var "v", Node "joinable" [Var "u1", Var "u2", Var "v"]]]]),
  ("canonical_circle", Node "hitCanonical" [Var "S¹"], Node "∧" [Node "canonical" [Var "base"], Node "forall" [Var "i", Node "canonical" [Node "loop" [Var "@", Var "i"]]]]),
  ("canonical_suspension", Node "hitCanonical" [Node "Σ" [mv "A"]], Node "∧" [Node "canonical" [Var "north"], Node "canonical" [Var "south"], Node "forall" [Var "a", Node "canonical" [Node "merid" [Var "a"]]]]),
  ("canonical_pushout", Node "hitCanonical" [Node "Pushout" [mv "A", mv "B", mv "C"]], Node "∧" [Node "forall" [Var "a", Node "canonical" [Node "inl" [Var "a"]]], Node "∧" [Node "forall" [Var "b", Node "canonical" [Node "inr" [Var "b"]]], Node "forall" [Var "c", Node "canonical" [Node "push" [Var "c"]]]]]),
  ("canonical_torus", Node "hitCanonical" [Var "T²"], Node "∧" [Node "canonical" [Var "tbase"], Node "∧" [Node "forall" [Var "i", Node "canonical" [Node "tline1" [Var "@", Var "i"]]], Node "∧" [Node "forall" [Var "i", Node "canonical" [Node "tline2" [Var "@", Var "i"]]], Node "forall" [Var "i", Var "j", Node "canonical" [Node "tsquare" [Var "@", Var "i", Var "@", Var "j"]]]]]]),
  ("hit_canonicity_thm", Node "∧" [Node "closed" [mv "t"], Node "=" [Node "typeOf" [mv "t"], Var "HIT"]], Node "exists" [Var "v", Node "∧" [Node "hitCanonical" [Var "v"], Node "Eq" [Node "normalize" [mv "t"], Var "v"]]]),
  ("pushout_merge", Node "pushoutComplete" [mv "g1", mv "g2"], Node "forall" [Var "p", Node "→" [Node "∨" [Node "belongsTo" [Var "p", mv "g1"], Node "belongsTo" [Var "p", mv "g2"]], Node "exists" [Var "q", Node "∧" [Node "belongsTo" [Var "q", Node "pushout" [mv "g1", mv "g2"]], Node "Eq" [Var "p", Var "q"]]]]]),
  ("token_context_merge", Node "∧" [Node "pushoutComplete" [mv "g1", mv "g2"], Node "∧" [Node "piece" [mv "g1", mv "frag"], Node "piece" [mv "g2", mv "frag2"]]], Node "forall" [Var "sym", Node "→" [Node "∨" [Node "symbolInContext" [Var "sym", mv "frag"], Node "symbolInContext" [Var "sym", mv "frag2"]], Node "symbolInContext" [Var "sym", Node "pushout" [mv "g1", mv "g2"]]]])
  ]

oneStep :: [Rule] -> Term -> Maybe Term
oneStep rules t = msum [substitute <$> match pattern t <*> pure template | (_, pattern, template) <- rules]

-- Fuel pattern to prevent infinite loops
normalize :: [Rule] -> Term -> Term
normalize rules = normalize' 100
  where
    normalize' 0 t = t  -- fuel exhausted
    normalize' n t = case oneStep rules t of
      Nothing -> case t of
        Node l cs -> Node l (map (normalize' n) cs)
        _ -> t
      Just t' -> normalize' (n-1) t'

-- Cooltt projection rules
coolttRules :: [Rule]
coolttRules =
  [ -- Path types
    ("path_to_cooltt", Node "path" [mv "i", mv "a", mv "b"],
         Node "cooltt" [Str "ext", mv "i", Str "=>", Str "_", Str "with",
           Node "boundary" [Node "eq0" [mv "i", mv "a"],
                           Node "eq1" [mv "i", mv "b"]]])
  , ("Path_to_cooltt", Node "Path" [mv "A", mv "a", mv "b"],
         Node "cooltt-path" [mv "A", mv "a", mv "b"])
  -- Lambda/Pi
  , ("lam_to_cooltt", Node "lam" [mv "x", mv "body"],
         Node "cooltt-lam" [mv "x", mv "body"])
  , ("pi_to_cooltt", Node "Pi" [mv "x", mv "A", mv "B"],
         Node "cooltt-pi" [mv "x", mv "A", mv "B"])
  , ("app_to_cooltt", Node "app" [mv "f", mv "a"],
         Node "cooltt-app" [mv "f", mv "a"])
  -- Path operations
  , ("inv_to_cooltt", Node "path-inv" [mv "p"],
         Node "cooltt-symm" [mv "p"])
  , ("comp_to_cooltt", Node "path-comp" [mv "i", mv "p", mv "q"],
         Node "cooltt-trans" [mv "p", mv "q"])
  , ("refl_to_cooltt", Node "reflJ" [mv "t"],
         Node "cooltt-refl" [mv "t"])
  -- Cubical ops
  , ("hcom_to_cooltt", Node "hcom" [mv "A", mv "r", mv "s", mv "phi", mv "u"],
         Node "cooltt-hcom" [mv "A", mv "r", mv "s", mv "phi", mv "u"])
  , ("coe_to_cooltt", Node "coe" [mv "A", mv "r", mv "s", mv "a"],
         Node "cooltt-coe" [mv "A", mv "r", mv "s", mv "a"])
  -- HITs
  , ("s1_to_cooltt", Node "S1" [], Node "cooltt" [Str "circle"])
  , ("base_to_cooltt", Node "base" [], Node "cooltt" [Str "base"])
  , ("loop_to_cooltt", Node "loop" [mv "i"],
         Node "cooltt-loop" [mv "i"])
  -- Definitions
  , ("def_to_cooltt", Node "define" [mv "n", mv "t", mv "b"],
         Node "cooltt-def" [mv "n", mv "t", mv "b"])
  , ("norm_to_cooltt", Node "normalize" [mv "t"],
         Node "cooltt-normalize" [mv "t"])
  ]

-- Pretty-print cooltt terms to string
showCooltt :: Term -> String
showCooltt (Node "cooltt" [Str s]) = s
showCooltt (Node "cooltt-path" [a, x, y]) =
  "path " ++ showCooltt a ++ " " ++ showCooltt x ++ " " ++ showCooltt y
showCooltt (Node "cooltt-lam" [Var x, body]) =
  x ++ " => " ++ showCooltt body
showCooltt (Node "cooltt-lam" [MetaVar x, body]) =
  x ++ " => " ++ showCooltt body
showCooltt (Node "cooltt-pi" [Var x, a, b]) =
  "(" ++ x ++ " : " ++ showCooltt a ++ ") → " ++ showCooltt b
showCooltt (Node "cooltt-pi" [MetaVar x, a, b]) =
  "(" ++ x ++ " : " ++ showCooltt a ++ ") → " ++ showCooltt b
showCooltt (Node "cooltt-app" [f, a]) =
  "{" ++ showCooltt f ++ " " ++ showCooltt a ++ "}"
showCooltt (Node "cooltt-symm" [p]) =
  "symm _ {i => " ++ showCooltt p ++ "}"
showCooltt (Node "cooltt-trans" [p, q]) =
  "trans _ {i => " ++ showCooltt p ++ "} {i => " ++ showCooltt q ++ "}"
showCooltt (Node "cooltt-refl" [t]) =
  "refl _ " ++ showCooltt t
showCooltt (Node "cooltt-hcom" [a, r, s, phi, u]) =
  "hcom " ++ showCooltt a ++ " " ++ showCooltt r ++ " " ++ showCooltt s ++
  " {" ++ showCooltt phi ++ "} {" ++ showCooltt u ++ "}"
showCooltt (Node "cooltt-coe" [a, r, s, x]) =
  "coe {i => " ++ showCooltt a ++ " i} " ++ showCooltt r ++ " " ++
  showCooltt s ++ " " ++ showCooltt x
showCooltt (Node "cooltt-loop" [i]) =
  "loop " ++ showCooltt i
showCooltt (Node "cooltt-def" [Var n, t, b]) =
  "def " ++ n ++ " : " ++ showCooltt t ++ " := " ++ showCooltt b
showCooltt (Node "cooltt-def" [MetaVar n, t, b]) =
  "def " ++ n ++ " : " ++ showCooltt t ++ " := " ++ showCooltt b
showCooltt (Node "cooltt-normalize" [t]) =
  "#normalize " ++ showCooltt t
showCooltt (Node "cooltt" parts) = unwords (map showCooltt parts)
showCooltt (Node "boundary" [Node "eq0" [i, a], Node "eq1" [_, b]]) =
  "[" ++ showCooltt i ++ "=0 => " ++ showCooltt a ++ " | " ++
  showCooltt i ++ "=1 => " ++ showCooltt b ++ "]"
showCooltt (Var x) = x
showCooltt (MetaVar x) = x
showCooltt (Str s) = s
showCooltt (Num n) = show n
showCooltt (Node l cs) = "(" ++ l ++ " " ++ unwords (map showCooltt cs) ++ ")"

-- Convert to cooltt and pretty-print
toCooltt :: Term -> String
toCooltt t = showCooltt (normalize coolttRules t)

main :: IO ()
main = do
  let testTokenScope = Node "tokenize" [Var "Interval", Var "∧"]
  print $ "Test token_scope: " ++ show (normalize rules testTokenScope)

  let testContextBudget = Node "select-context" [Node "budget" [Num 10], Node "context" [Node "atom" [Var "grammar", Var "g1", Num 5, Num 10, Num 10], Node "atom" [Var "grammar", Var "g2", Num 20, Num 1, Num 1]]]
  print $ "Test context_budget: " ++ show (normalize rules testContextBudget)

  let testSyntaxLiteral = Node "literal" [Str "(", Var "syntax"]
  print $ "Test syntax_literal: " ++ show (normalize rules testSyntaxLiteral)

  let testContentLiteral = Node "literal" [Str "true", Var "content"]
  print $ "Test content_literal: " ++ show (normalize rules testContentLiteral)

  -- Cooltt projection tests
  putStrLn "\n=== Cooltt Projection Tests ==="

  let testPath = Node "path" [Var "i", Var "a", Var "b"]
  putStrLn $ "path i a b  →  " ++ toCooltt testPath

  let testLam = Node "lam" [Var "x", Node "app" [Var "f", Var "x"]]
  putStrLn $ "λx. f x  →  " ++ toCooltt testLam

  let testPi = Node "Pi" [Var "A", Var "Type", Node "Pi" [Var "x", Var "A", Var "A"]]
  putStrLn $ "Π(A:Type). A → A  →  " ++ toCooltt testPi

  let testRefl = Node "reflJ" [Var "a"]
  putStrLn $ "refl a  →  " ++ toCooltt testRefl

  let testSymm = Node "path-inv" [Node "path" [Var "i", Var "a", Var "b"]]
  putStrLn $ "symm (path i a b)  →  " ++ toCooltt testSymm

  let testDef = Node "define" [Var "id", Node "Pi" [Var "A", Var "Type", Node "Pi" [Var "x", Var "A", Var "A"]], Node "lam" [Var "A", Node "lam" [Var "x", Var "x"]]]
  putStrLn $ "def id  →  " ++ toCooltt testDef