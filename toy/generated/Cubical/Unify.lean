(DImport import (modulePath Core) ;)

(DImport import (modulePath GlobalEnv) ;)

(DImport import (modulePath Visitor) ;)

namespace Unify

  section MetaInfo

    def metaInfo : Parser :=
      (annotated str "metaInfo" str "name:" (special <gname>) str "ctx:" many ((special <expr>)) str "ty:" (special <expr>) str "solution:" optional ((special <expr>)) → metaInfo)

    def metaInfoName (t : Term) : Term :=
      match t with
      | (metaInfoName (metaInfo (labeledArg name : $n) (labeledArg ctx : $c) (labeledArg ty : $t) (labeledArg solution : $s))) => $n
      | _ => t

    def metaInfoCtx (t : Term) : Term :=
      match t with
      | (metaInfoCtx (metaInfo (labeledArg name : $n) (labeledArg ctx : $c) (labeledArg ty : $t) (labeledArg solution : $s))) => $c
      | _ => t

    def metaInfoTy (t : Term) : Term :=
      match t with
      | (metaInfoTy (metaInfo (labeledArg name : $n) (labeledArg ctx : $c) (labeledArg ty : $t) (labeledArg solution : $s))) => $t
      | _ => t

    def metaInfoSolution (t : Term) : Term :=
      match t with
      | (metaInfoSolution (metaInfo (labeledArg name : $n) (labeledArg ctx : $c) (labeledArg ty : $t) (labeledArg solution : $s))) => $s
      | _ => t

  end MetaInfo

  section UnifyState

    def unifyState : Parser :=
      (annotated str "unifyState" str "metas:" many ((special <metaInfo>)) str "nextId:" (special <number>) str "postponed:" many ((special <constraint>)) → unifyState)

    def constraint : Parser :=
      (annotated str "(" (special <expr>) str "≡" (special <expr>) str ")" → constraint)

    def unifyStateEmpty (t : Term) : Term :=
      match t with
      | (unifyStateEmpty) => (unifyState (labeledArg metas : (unit ( ))) (labeledArg nextId : (num (number 0))) (labeledArg postponed : (unit ( ))))
      | _ => t

    def unifyStateFreshMeta (t : Term) : Term :=
      match t with
      | (unifyStateFreshMeta (unifyState (labeledArg metas : $metas) (labeledArg nextId : $n) (labeledArg postponed : $p)) $ctx $ty) => (letIn ( let name = (gnameFresh str "?" $n) in (letIn let info = (metaInfo (labeledArg name : (name)) (labeledArg ctx : $ctx) (labeledArg ty : $ty) (labeledArg solution : (none))) in (record ( result : (unifyState (labeledArg metas : (info $metas)) (labeledArg nextId : (suc $n)) (labeledArg postponed : $p)) (labeledArg name : (name)) ))) ))
      | _ => t

    def unifyStateLookupMeta (t : Term) : Term :=
      match t with
      | (unifyStateLookupMeta (unifyState (labeledArg metas : $metas) (labeledArg nextId : $n) (labeledArg postponed : $p)) $name) => (findMeta $metas $name)
      | _ => t

    def findMetaNil (t : Term) : Term :=
      match t with
      | (findMeta (unit ( )) $name) => (none)
      | _ => t

    def findMetaMatch (t : Term) : Term :=
      match t with
      | (findMeta (( ( metaInfo (labeledArg name : $name) (labeledArg ctx : $c) (labeledArg ty : $t) (labeledArg solution : $s) ) $rest )) $name) => (some (metaInfo (labeledArg name : $name) (labeledArg ctx : $c) (labeledArg ty : $t) (labeledArg solution : $s)))
      | _ => t

    def findMetaMiss (t : Term) : Term :=
      match t with
      | (findMeta ($m $rest) $name) => (findMeta $rest $name)
      | _ => t

    def unifyStateSolveMeta (t : Term) : Term :=
      match t with
      | (unifyStateSolveMeta (unifyState (labeledArg metas : $metas) (labeledArg nextId : $n) (labeledArg postponed : $p)) $name $sol) => (unifyState (labeledArg metas : (solveMeta $metas $name $sol)) (labeledArg nextId : $n) (labeledArg postponed : $p))
      | _ => t

    def solveMetaNil (t : Term) : Term :=
      match t with
      | (solveMeta (unit ( )) $name $sol) => (unit ( ))
      | _ => t

    def solveMetaMatch (t : Term) : Term :=
      match t with
      | (solveMeta (( ( metaInfo (labeledArg name : $name) (labeledArg ctx : $c) (labeledArg ty : $t) (labeledArg solution : $old) ) $rest )) $name $sol) => ((( (metaInfo) (labeledArg name : $name) (labeledArg ctx : $c) (labeledArg ty : $t) (labeledArg solution : (some $sol)) )) $rest)
      | _ => t

    def solveMetaMiss (t : Term) : Term :=
      match t with
      | (solveMeta ($m $rest) $name $sol) => ($m (solveMeta $rest $name $sol))
      | _ => t

    def unifyStateIsSolved (t : Term) : Term :=
      match t with
      | (unifyStateIsSolved $st $name) => (caseExpr ( case (unifyStateLookupMeta $st $name) (arm ( some (metaInfo (labeledArg name : (_)) (labeledArg ctx : (_)) (labeledArg ty : (_)) (labeledArg solution : (some (_)))) ) => (true)) (arm _ => (false)) ))
      | _ => t

    def unifyStateUnsolved (t : Term) : Term :=
      match t with
      | (unifyStateUnsolved (unifyState (labeledArg metas : $metas) (labeledArg nextId : $n) (labeledArg postponed : $p))) => (filter (fun (m) (=>) (isNone (metaInfoSolution (m)))) $metas)
      | _ => t

    def unifyStatePostpone (t : Term) : Term :=
      match t with
      | (unifyStatePostpone (unifyState (labeledArg metas : $metas) (labeledArg nextId : $n) (labeledArg postponed : $p)) $t1 $t2) => (unifyState (labeledArg metas : $metas) (labeledArg nextId : $n) (labeledArg postponed : ((( $t1 (≡) $t2 )) $p)))
      | _ => t

    def unifyStateTakePostponed (t : Term) : Term :=
      match t with
      | (unifyStateTakePostponed (unifyState (labeledArg metas : $metas) (labeledArg nextId : $n) (labeledArg postponed : $p))) => (record ( result : (unifyState (labeledArg metas : $metas) (labeledArg nextId : $n) (labeledArg postponed : (unit ( )))) (labeledArg constraints : $p) ))
      | _ => t

  end UnifyState

  section UnifyResult

    def unifySuccess : Parser :=
      (annotated str "success" (special <unifyState>) → unifyResult)

    def unifyFailure : Parser :=
      (annotated str "failure" (special <string>) → unifyResult)

    def unifyStuck : Parser :=
      (annotated str "stuck" (special <unifyState>) → unifyResult)

  end UnifyResult

  section SpineElem

    def spineTermVar : Parser :=
      (annotated str "termVar" (special <number>) → spineElem)

    def spineDimVar : Parser :=
      (annotated str "dimVar" (special <number>) → spineElem)

    def spineOther : Parser :=
      (annotated str "other" (special <expr>) → spineElem)

    def classifySpineArg (t : Term) : Term :=
      match t with
      | (classifySpineArg (ix $n)) => (termVar $n)
      | _ => t

    def classifySpineArgDim (t : Term) : Term :=
      match t with
      | (classifySpineArg (dimVar $n)) => (dimVar $n)
      | _ => t

    def classifySpineArgOther (t : Term) : Term :=
      match t with
      | (classifySpineArg $e) => (other $e)
      | _ => t

  end SpineElem

  section Spine

    def collectSpine (t : Term) : Term :=
      match t with
      | (collectSpine $e) => (collectSpine' $e (unit ( )))
      | _ => t

    def collectSpine'App (t : Term) : Term :=
      match t with
      | (collectSpine' (app $f $a) $acc) => (collectSpine' $f ($acc $a))
      | _ => t

    def collectSpine'Papp (t : Term) : Term :=
      match t with
      | (collectSpine' (papp $f $a) $acc) => (collectSpine' $f ($acc $a))
      | _ => t

    def collectSpine'Other (t : Term) : Term :=
      match t with
      | (collectSpine' $e $acc) => (tuple ( $e , $acc ))
      | _ => t

    def isPatternSpine (t : Term) : Term :=
      match t with
      | (isPatternSpine $args) => (letIn ( let elems = (map (classifySpineArg) $args) in (letIn let allVars = (all (isSpineVar) (elems)) in (letIn let distinct = (eq (length (eraseDups (elems))) (length (elems))) in (and (allVars) (distinct)))) ))
      | _ => t

    def isSpineVar (t : Term) : Term :=
      match t with
      | (isSpineVar (termVar $n)) => (true)
      | _ => t

    def isSpineVarDim (t : Term) : Term :=
      match t with
      | (isSpineVar (dimVar $n)) => (true)
      | _ => t

    def isSpineVarOther (t : Term) : Term :=
      match t with
      | (isSpineVar (other $e)) => (false)
      | _ => t

    def spineToVars (t : Term) : Term :=
      match t with
      | (spineToVars $args) => (filterMap (extractVarIndex (map (classifySpineArg) $args)))
      | _ => t

    def extractVarIndex (t : Term) : Term :=
      match t with
      | (extractVarIndex (termVar $n)) => (some $n)
      | _ => t

    def extractVarIndexDim (t : Term) : Term :=
      match t with
      | (extractVarIndex (dimVar $n)) => (some $n)
      | _ => t

    def extractVarIndexOther (t : Term) : Term :=
      match t with
      | (extractVarIndex (other $e)) => (none)
      | _ => t

    def isMeta (t : Term) : Term :=
      match t with
      | (isMeta (lit $name)) => (caseExpr ( case (startsWith $name str "?") (arm true => (some $name)) (arm false => (none)) ))
      | _ => t

    def isMetaOther (t : Term) : Term :=
      match t with
      | (isMeta $e) => (none)
      | _ => t

  end Spine

  section Invert

    def invertTerm (t : Term) : Term :=
      match t with
      | (invertTerm $spineVars $term) => (invertTerm' $spineVars $term (num (number 0)) (length $spineVars))
      | _ => t

    def invertTerm'Ix (t : Term) : Term :=
      match t with
      | (invertTerm' $spineVars (ix $n) $depth $len) => (caseExpr ( case (findIndex $spineVars $n) (arm ( some $i ) => (some (ix (plus $depth (minus (minus $len $i) (num (number 1))))))) (arm none => (caseExpr ( case (gte $n $len) (arm true => (some (ix (plus $depth (minus $n $len))))) (arm false => (none)) ))) ))
      | _ => t

    def invertTerm'Lam (t : Term) : Term :=
      match t with
      | (invertTerm' $spineVars (lam $body) $depth $len) => (caseExpr ( case (invertTerm' $spineVars $body (suc $depth) $len) (arm ( some $body' ) => (some (lam $body'))) (arm none => (none)) ))
      | _ => t

    def invertTerm'App (t : Term) : Term :=
      match t with
      | (invertTerm' $spineVars (app $f $a) $depth $len) => (caseExpr ( case (invertTerm' $spineVars $f $depth $len) (arm ( some $f' ) => (caseExpr ( case (invertTerm' $spineVars $a $depth $len) (arm ( some $a' ) => (some (app $f' $a'))) (arm none => (none)) ))) (arm none => (none)) ))
      | _ => t

    def invertTerm'Pi (t : Term) : Term :=
      match t with
      | (invertTerm' $spineVars (pi $dom $cod) $depth $len) => (caseExpr ( case (invertTerm' $spineVars $dom $depth $len) (arm ( some $dom' ) => (caseExpr ( case (invertTerm' $spineVars $cod (suc $depth) $len) (arm ( some $cod' ) => (some (pi $dom' $cod'))) (arm none => (none)) ))) (arm none => (none)) ))
      | _ => t

    def invertTerm'Lit (t : Term) : Term :=
      match t with
      | (invertTerm' $spineVars (lit $s) $depth $len) => (some (lit $s))
      | _ => t

    def invertTerm'Dim0 (t : Term) : Term :=
      match t with
      | (invertTerm' $spineVars (dim0) $depth $len) => (some (dim0))
      | _ => t

    def invertTerm'Dim1 (t : Term) : Term :=
      match t with
      | (invertTerm' $spineVars (dim1) $depth $len) => (some (dim1))
      | _ => t

    def invertTerm'Default (t : Term) : Term :=
      match t with
      | (invertTerm' $spineVars $e $depth $len) => (some $e)
      | _ => t

  end Invert

  section FlexRigid

    def solveFlexRigid (t : Term) : Term :=
      match t with
      | (solveFlexRigid $st $metaName $args $term) => (letIn ( let gname = (gnameNamed $metaName) in (caseExpr case (occurs (gname) $term) (arm true => (failure (concat str "occurs check failed: " $metaName str " occurs in solution"))) (arm false => (solveFlexRigid' $st $metaName $args $term (gname)))) ))
      | _ => t

    def solveFlexRigid' (t : Term) : Term :=
      match t with
      | (solveFlexRigid' $st $metaName $args $term $gname) => (caseExpr ( case (isPatternSpine $args) (arm false => (stuck (unifyStatePostpone $st (lit $metaName) $term))) (arm true => (letIn ( let spineVars = (spineToVars $args) in (caseExpr case (invertTerm (spineVars) $term) (arm none => (stuck (unifyStatePostpone $st (lit $metaName) $term))) (arm ( some $invertedTerm ) => (letIn ( let solution = (buildSolution $args $invertedTerm) in (success (unifyStateSolveMeta $st $gname (solution))) )))) ))) ))
      | _ => t

    def buildSolution (t : Term) : Term :=
      match t with
      | (buildSolution (unit ( )) $body) => $body
      | _ => t

    def buildSolutionCons (t : Term) : Term :=
      match t with
      | (buildSolution ($a $rest) $body) => (lam (buildSolution $rest $body))
      | _ => t

  end FlexRigid

  section Unify

    def unify (t : Term) : Term :=
      match t with
      | (unify $st $t1 $t2) => (caseExpr ( case (conv $t1 $t2) (arm true => (success $st)) (arm false => (letIn ( let h1Args1 = (collectSpine $t1) in (letIn let h2Args2 = (collectSpine $t2) in (unifyHeads $st (fst (h1Args1)) (snd (h1Args1)) (fst (h2Args2)) (snd (h2Args2)))) ))) ))
      | _ => t

    def unifyHeads (t : Term) : Term :=
      match t with
      | (unifyHeads $st $h1 $args1 $h2 $args2) => (case (isMeta $h1) (isMeta $h2) (some $m) (none) (=>) (solveFlexRigid $st $m $args1 (foldl (app) $h2 $args2)) (none (some $m)) (=>) (solveFlexRigid $st $m $args2 (foldl (app) $h1 $args1)) (some $m1) (some $m2) (=>) (caseExpr ( case (eq $m1 $m2) (arm true => (flexFlexSame $st $m1 $args1 $args2)) (arm false => (flexFlexDiff $st $m1 $args1 $m2 $args2)) )) (none) (none) (=>) (unifyRigid $st (foldl (app) $h1 $args1) (foldl (app) $h2 $args2)))
      | _ => t

  end Unify

  section FlexFlexSame

    def flexFlexSame (t : Term) : Term :=
      match t with
      | (flexFlexSame $st $metaName $args1 $args2) => (caseExpr ( case (eq (length $args1) (length $args2)) (arm false => (failure str "flex-flex: spine length mismatch")) (arm true => (caseExpr ( case (and (isPatternSpine $args1) (isPatternSpine $args2)) (arm false => (stuck (unifyStatePostpone $st (lit $metaName) (lit $metaName)))) (arm true => (flexFlexSamePattern $st $metaName (spineToVars $args1) (spineToVars $args2))) ))) ))
      | _ => t

    def flexFlexSamePattern (t : Term) : Term :=
      match t with
      | (flexFlexSamePattern $st $metaName $vars1 $vars2) => (letIn ( let pairs = (zip $vars1 $vars2) in (letIn let commonCount = (length (filter (fun (p) (=>) (eq (fst (p)) (snd (p)))) (pairs))) in (caseExpr case (eq (commonCount (length $vars1))) (arm true => (success $st)) (arm false => (stuck (unifyStatePostpone $st (lit $metaName) (lit $metaName)))))) ))
      | _ => t

  end FlexFlexSame

  section FlexFlexDiff

    def flexFlexDiff (t : Term) : Term :=
      match t with
      | (flexFlexDiff $st $m1 $args1 $m2 $args2) => (caseExpr ( case (and (isPatternSpine $args1) (isPatternSpine $args2)) (arm false => (stuck (unifyStatePostpone $st (lit $m1) (lit $m2)))) (arm true => (letIn ( let vars1 = (spineToVars $args1) in (letIn let vars2 = (spineToVars $args2) in (flexFlexDiff' $st $m1 $args1 (vars1) $m2 $args2 (vars2))) ))) ))
      | _ => t

    def flexFlexDiff' (t : Term) : Term :=
      match t with
      | (flexFlexDiff' $st $m1 $args1 $vars1 $m2 $args2 $vars2) => (letIn ( let subset21 = (all (fun (v) (=>) (contains $vars1 (v))) $vars2) in (letIn let subset12 = (all (fun (v) (=>) (contains $vars2 (v))) $vars1) in (caseExpr case (subset21) (arm true => (letIn ( let body = (buildMetaApp $m1 $vars1 $vars2) in (letIn let solution = (buildSolution $args2 (body)) in (success (unifyStateSolveMeta $st (gnameNamed $m2) (solution)))) ))) (arm false => (caseExpr ( case (subset12) (arm true => (letIn ( let body = (buildMetaApp $m2 $vars2 $vars1) in (letIn let solution = (buildSolution $args1 (body)) in (success (unifyStateSolveMeta $st (gnameNamed $m1) (solution)))) ))) (arm false => (stuck (unifyStatePostpone $st (lit $m1) (lit $m2)))) ))))) ))
      | _ => t

    def buildMetaApp (t : Term) : Term :=
      match t with
      | (buildMetaApp $m $sourceVars $targetVars) => (letIn ( let reindexed = (map (fun (v) (=>) (findIndexOr0 $sourceVars (v))) $targetVars) in (foldl (app (lit $m) (map (ix) (reindexed)))) ))
      | _ => t

    def findIndexOr0 (t : Term) : Term :=
      match t with
      | (findIndexOr0 $xs $v) => (caseExpr ( case (findIndex $xs $v) (arm ( some $i ) => $i) (arm none => (num (number 0))) ))
      | _ => t

  end FlexFlexDiff

  section UnifyRigid

    def unifyRigidIx (t : Term) : Term :=
      match t with
      | (unifyRigid $st (ix $n1) (ix $n2)) => (caseExpr ( case (eq $n1 $n2) (arm true => (success $st)) (arm false => (failure str "variable mismatch")) ))
      | _ => t

    def unifyRigidLit (t : Term) : Term :=
      match t with
      | (unifyRigid $st (lit $l1) (lit $l2)) => (caseExpr ( case (eq $l1 $l2) (arm true => (success $st)) (arm false => (failure (concat str "literal mismatch: " $l1 str " ≠ " $l2))) ))
      | _ => t

    def unifyRigidUniv (t : Term) : Term :=
      match t with
      | (unifyRigid $st (univ $l1) (univ $l2)) => (caseExpr ( case (levelEq $l1 $l2) (arm true => (success $st)) (arm false => (failure str "universe level mismatch")) ))
      | _ => t

    def unifyRigidLam (t : Term) : Term :=
      match t with
      | (unifyRigid $st (lam $b1) (lam $b2)) => (unify $st $b1 $b2)
      | _ => t

    def unifyRigidApp (t : Term) : Term :=
      match t with
      | (unifyRigid $st (app $f1 $a1) (app $f2 $a2)) => (caseExpr ( case (unify $st $f1 $f2) (arm ( success $st' ) => (unify $st' $a1 $a2)) (varArm $ other => $other) ))
      | _ => t

    def unifyRigidPi (t : Term) : Term :=
      match t with
      | (unifyRigid $st (pi $d1 $c1) (pi $d2 $c2)) => (caseExpr ( case (unify $st $d1 $d2) (arm ( success $st' ) => (unify $st' $c1 $c2)) (varArm $ other => $other) ))
      | _ => t

    def unifyRigidSigma (t : Term) : Term :=
      match t with
      | (unifyRigid $st (sigma $d1 $c1) (sigma $d2 $c2)) => (caseExpr ( case (unify $st $d1 $d2) (arm ( success $st' ) => (unify $st' $c1 $c2)) (varArm $ other => $other) ))
      | _ => t

    def unifyRigidPair (t : Term) : Term :=
      match t with
      | (unifyRigid $st (pair $a1 $b1) (pair $a2 $b2)) => (caseExpr ( case (unify $st $a1 $a2) (arm ( success $st' ) => (unify $st' $b1 $b2)) (varArm $ other => $other) ))
      | _ => t

    def unifyRigidFst (t : Term) : Term :=
      match t with
      | (unifyRigid $st (fst $p1) (fst $p2)) => (unify $st $p1 $p2)
      | _ => t

    def unifyRigidSnd (t : Term) : Term :=
      match t with
      | (unifyRigid $st (snd $p1) (snd $p2)) => (unify $st $p1 $p2)
      | _ => t

    def unifyRigidPath (t : Term) : Term :=
      match t with
      | (unifyRigid $st (path $t1 $a1 $b1) (path $t2 $a2 $b2)) => (caseExpr ( case (unify $st $t1 $t2) (arm ( success $st' ) => (caseExpr ( case (unify $st' $a1 $a2) (arm ( success $st'' ) => (unify $st'' $b1 $b2)) (varArm $ other => $other) ))) (varArm $ other => $other) ))
      | _ => t

    def unifyRigidPlam (t : Term) : Term :=
      match t with
      | (unifyRigid $st (plam $b1) (plam $b2)) => (unify $st $b1 $b2)
      | _ => t

    def unifyRigidPapp (t : Term) : Term :=
      match t with
      | (unifyRigid $st (papp $p1 $r1) (papp $p2 $r2)) => (caseExpr ( case (unify $st $p1 $p2) (arm ( success $st' ) => (unify $st' $r1 $r2)) (varArm $ other => $other) ))
      | _ => t

    def unifyRigidDim0 (t : Term) : Term :=
      match t with
      | (unifyRigid $st (dim0) (dim0)) => (success $st)
      | _ => t

    def unifyRigidDim1 (t : Term) : Term :=
      match t with
      | (unifyRigid $st (dim1) (dim1)) => (success $st)
      | _ => t

    def unifyRigidNat (t : Term) : Term :=
      match t with
      | (unifyRigid $st (nat) (nat)) => (success $st)
      | _ => t

    def unifyRigidZero (t : Term) : Term :=
      match t with
      | (unifyRigid $st (zero) (zero)) => (success $st)
      | _ => t

    def unifyRigidSuc (t : Term) : Term :=
      match t with
      | (unifyRigid $st (suc $n1) (suc $n2)) => (unify $st $n1 $n2)
      | _ => t

    def unifyRigidCircle (t : Term) : Term :=
      match t with
      | (unifyRigid $st (circle) (circle)) => (success $st)
      | _ => t

    def unifyRigidBase (t : Term) : Term :=
      match t with
      | (unifyRigid $st (base) (base)) => (success $st)
      | _ => t

    def unifyRigidLoop (t : Term) : Term :=
      match t with
      | (unifyRigid $st (loop $r1) (loop $r2)) => (unify $st $r1 $r2)
      | _ => t

    def unifyRigidCofTop (t : Term) : Term :=
      match t with
      | (unifyRigid $st (cof_top) (cof_top)) => (success $st)
      | _ => t

    def unifyRigidCofBot (t : Term) : Term :=
      match t with
      | (unifyRigid $st (cof_bot) (cof_bot)) => (success $st)
      | _ => t

    def unifyRigidDefault (t : Term) : Term :=
      match t with
      | (unifyRigid $st $t1 $t2) => (failure str "structural mismatch")
      | _ => t

  end UnifyRigid

  section ApplyMetas

    def applyMetas (t : Term) : Term :=
      match t with
      | (applyMetas $st $e) => (applyMetas' $st $e)
      | _ => t

    def applyMetas'Lit (t : Term) : Term :=
      match t with
      | (applyMetas' $st (lit $name)) => (caseExpr ( case (startsWith $name str "?") (arm true => (caseExpr ( case (unifyStateLookupMeta $st (gnameNamed $name)) (arm ( some (metaInfo (labeledArg name : (_)) (labeledArg ctx : (_)) (labeledArg ty : (_)) (labeledArg solution : (some $sol))) ) => $sol) (arm _ => (lit $name)) ))) (arm false => (lit $name)) ))
      | _ => t

    def applyMetas'Lam (t : Term) : Term :=
      match t with
      | (applyMetas' $st (lam $b)) => (lam (applyMetas' $st $b))
      | _ => t

    def applyMetas'App (t : Term) : Term :=
      match t with
      | (applyMetas' $st (app $f $a)) => (app (applyMetas' $st $f) (applyMetas' $st $a))
      | _ => t

    def applyMetas'Pi (t : Term) : Term :=
      match t with
      | (applyMetas' $st (pi $d $c)) => (pi (applyMetas' $st $d) (applyMetas' $st $c))
      | _ => t

    def applyMetas'Default (t : Term) : Term :=
      match t with
      | (applyMetas' $st $e) => $e
      | _ => t

  end ApplyMetas

  section SolveAll

    def processPostponed (t : Term) : Term :=
      match t with
      | (processPostponed $st) => (caseExpr ( case (unifyStateTakePostponed $st) (arm ( result (:) $st' (labeledArg constraints : (unit ( ))) ) => (record ( result : $st' (labeledArg progress : (false)) ))) (arm ( result (:) $st' (labeledArg constraints : $constraints) ) => (processConstraints $st' $constraints (false))) ))
      | _ => t

    def processConstraints (t : Term) : Term :=
      match t with
      | (processConstraints $st (unit ( )) $progress) => (record ( result : $st (labeledArg progress : $progress) ))
      | _ => t

    def processConstraintsCons (t : Term) : Term :=
      match t with
      | (processConstraints $st (( ( ( $t1 (≡) $t2 ) ) $rest )) $progress) => (letIn ( let t1' = (applyMetas $st $t1) in (letIn let t2' = (applyMetas $st $t2) in (caseExpr case (unify $st (t1') (t2')) (arm ( success $newSt ) => (processConstraints $newSt $rest (true))) (arm ( stuck $newSt ) => (processConstraints $newSt $rest $progress)) (arm ( failure (_) ) => (processConstraints (unifyStatePostpone $st (t1') (t2')) $rest $progress)))) ))
      | _ => t

    def solveAll (t : Term) : Term :=
      match t with
      | (solveAll $st $fuel) => (solveAll' $st $fuel)
      | _ => t

    def solveAll'0 (t : Term) : Term :=
      match t with
      | (solveAll' $st (num (number 0))) => $st
      | _ => t

    def solveAll' (t : Term) : Term :=
      match t with
      | (solveAll' $st (suc $fuel)) => (caseExpr ( case (processPostponed $st) (arm ( result (:) $st' (labeledArg progress : (true)) ) => (solveAll' $st' $fuel)) (arm ( result (:) $st' (labeledArg progress : (false)) ) => $st') ))
      | _ => t

  end SolveAll

  section TopLevel

    def tryUnify (t : Term) : Term :=
      match t with
      | (tryUnify $st $t1 $t2) => (caseExpr ( case (unify $st $t1 $t2) (arm ( success $st' ) => (some $st')) (arm ( stuck $st' ) => (some $st')) (arm ( failure (_) ) => (none)) ))
      | _ => t

    def unifyAndSolve (t : Term) : Term :=
      match t with
      | (unifyAndSolve $st $t1 $t2) => (caseExpr ( case (unify $st $t1 $t2) (arm ( success $st' ) => (some (solveAll $st' (num (number 100))))) (arm ( stuck $st' ) => (some (solveAll $st' (num (number 100))))) (arm ( failure (_) ) => (none)) ))
      | _ => t

    def hole (t : Term) : Term :=
      match t with
      | (hole $st $ctx $ty) => (caseExpr ( case (unifyStateFreshMeta $st $ctx $ty) (arm ( result (:) $st' (labeledArg name : $name) ) => (record ( result : $st' (labeledArg expr : (lit (gnameName $name))) ))) ))
      | _ => t

    def allSolved (t : Term) : Term :=
      match t with
      | (allSolved $st) => (isEmpty (unifyStateUnsolved $st))
      | _ => t

  end TopLevel

end Unify