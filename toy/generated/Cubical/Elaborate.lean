(DImport import (modulePath Core) ;)

(DImport import (modulePath GlobalEnv) ;)

(DImport import (modulePath Unify) ;)

(DImport import (modulePath Quote) ;)

(DImport import (modulePath Datatype) ;)

namespace Elaborate

  section Surface

    def surfVar : Parser :=
      (annotated str "var" (special <symbol>) → surface)

    def surfLit : Parser :=
      (annotated str "lit" (special <string>) → surface)

    def surfLam : Parser :=
      (annotated str "λ" (special <symbol>) str "." (special <surface>) → surface)

    def surfApp : Parser :=
      (annotated str "app" (special <surface>) (special <surface>) → surface)

    def surfAppImpl : Parser :=
      (annotated str "appImpl" (special <surface>) (special <surface>) → surface)

    def surfPi : Parser :=
      (annotated str "Π" str "(" (special <symbol>) str ":" (special <surface>) str ")" (special <surface>) → surface)

    def surfPiImpl : Parser :=
      (annotated str "{" (special <symbol>) str ":" (special <surface>) str "}" str "→" (special <surface>) → surface)

    def surfSigma : Parser :=
      (annotated str "Σ" str "(" (special <symbol>) str ":" (special <surface>) str ")" (special <surface>) → surface)

    def surfPair : Parser :=
      (annotated str "⟨" (special <surface>) str "," (special <surface>) str "⟩" → surface)

    def surfFst : Parser :=
      (annotated str "fst" (special <surface>) → surface)

    def surfSnd : Parser :=
      (annotated str "snd" (special <surface>) → surface)

    def surfLetIn : Parser :=
      (annotated str "let" (special <symbol>) str ":" (special <surface>) str "=" (special <surface>) str "in" (special <surface>) → surface)

    def surfUniv : Parser :=
      (annotated str "Type" (special <number>) → surface)

    def surfHole : Parser :=
      (annotated str "?" optional ((special <symbol>)) → surface)

    def surfAnn : Parser :=
      (annotated str "(" (special <surface>) str ":" (special <surface>) str ")" → surface)

    def surfDim0 : Parser :=
      (annotated str "0" → surface)

    def surfDim1 : Parser :=
      (annotated str "1" → surface)

    def surfPath : Parser :=
      (annotated str "Path" (special <surface>) (special <surface>) (special <surface>) → surface)

    def surfPlam : Parser :=
      (annotated str "λ" (special <symbol>) str "." (special <surface>) → surface)

    def surfPapp : Parser :=
      (annotated (special <surface>) str "@" (special <surface>) → surface)

    def surfRefl : Parser :=
      (annotated str "refl" (special <surface>) → surface)

    def surfData : Parser :=
      (annotated str "data" (special <symbol>) many ((special <surface>)) → surface)

    def surfIntro : Parser :=
      (annotated str "intro" (special <symbol>) str "." (special <symbol>) many ((special <surface>)) → surface)

    def surfElim : Parser :=
      (annotated str "elim" (special <surface>) str "motive" (special <surface>) many ((special <elimClause>)) → surface)

    def elimClause : Parser :=
      (annotated str "|" (special <symbol>) many ((special <symbol>)) str "=>" (special <surface>) → elimClause)

  end Surface

  section MetaEntry

    def metaEntry : Parser :=
      (annotated str "meta" str "ty:" (special <expr>) str "solution:" optional ((special <expr>)) → metaEntry)

    def metaEntryTy (t : Term) : Term :=
      match t with
      | (metaEntryTy (meta (labeledArg ty : $ty) (labeledArg solution : $sol))) => $ty
      | _ => t

    def metaEntrySol (t : Term) : Term :=
      match t with
      | (metaEntrySol (meta (labeledArg ty : $ty) (labeledArg solution : $sol))) => $sol
      | _ => t

  end MetaEntry

  section MetaCtx

    def metaCtx : Parser :=
      (annotated str "metaCtx" many ((special <metaBinding>)) → metaCtx)

    def metaBinding : Parser :=
      (annotated str "(" (special <number>) str "↦" (special <metaEntry>) str ")" → metaBinding)

    def metaCtxEmpty (t : Term) : Term :=
      match t with
      | (metaCtxEmpty) => (metaCtx (unit ( )))
      | _ => t

    def metaCtxLookup (t : Term) : Term :=
      match t with
      | (metaCtxLookup (metaCtx $bindings) $id) => (lookupMeta $bindings $id)
      | _ => t

    def metaCtxInsert (t : Term) : Term :=
      match t with
      | (metaCtxInsert (metaCtx $bindings) $id $entry) => (metaCtx ($bindings ($id (↦) $entry)))
      | _ => t

  end MetaCtx

  section LocalBinding

    def localBinding : Parser :=
      (annotated str "local" str "name:" (special <symbol>) str "ty:" (special <expr>) str "isDim:" (special <bool>) → localBinding)

    def localBindingName (t : Term) : Term :=
      match t with
      | (localBindingName (local (labeledArg name : $n) (labeledArg ty : $ty) (labeledArg isDim : $d))) => $n
      | _ => t

    def localBindingTy (t : Term) : Term :=
      match t with
      | (localBindingTy (local (labeledArg name : $n) (labeledArg ty : $ty) (labeledArg isDim : $d))) => $ty
      | _ => t

    def localBindingIsDim (t : Term) : Term :=
      match t with
      | (localBindingIsDim (local (labeledArg name : $n) (labeledArg ty : $ty) (labeledArg isDim : $d))) => $d
      | _ => t

  end LocalBinding

  section ElabCtx

    def elabCtx : Parser :=
      (annotated str "elabCtx" str "locals:" many ((special <localBinding>)) str "global:" (special <globalEnv>) str "meta:" (special <metaCtx>) str "nextMeta:" (special <number>) → elabCtx)

    def elabCtxEmpty (t : Term) : Term :=
      match t with
      | (elabCtxEmpty) => (elabCtx (labeledArg locals : (unit ( ))) (labeledArg global : (globalEnvEmpty)) (labeledArg meta : (metaCtxEmpty)) (labeledArg nextMeta : (num (number 0))))
      | _ => t

    def elabCtxWithGlobals (t : Term) : Term :=
      match t with
      | (elabCtxWithGlobals $env) => (elabCtx (labeledArg locals : (unit ( ))) (labeledArg global : $env) (labeledArg meta : (metaCtxEmpty)) (labeledArg nextMeta : (num (number 0))))
      | _ => t

    def elabCtxExtend (t : Term) : Term :=
      match t with
      | (elabCtxExtend (elabCtx (labeledArg locals : $locals) (labeledArg global : $g) (labeledArg meta : $m) (labeledArg nextMeta : $n)) $name $ty) => (elabCtx (labeledArg locals : ((( (local) (labeledArg name : $name) (labeledArg ty : $ty) (labeledArg isDim : (false)) )) $locals)) (labeledArg global : $g) (labeledArg meta : $m) (labeledArg nextMeta : $n))
      | _ => t

    def elabCtxExtendDim (t : Term) : Term :=
      match t with
      | (elabCtxExtendDim (elabCtx (labeledArg locals : $locals) (labeledArg global : $g) (labeledArg meta : $m) (labeledArg nextMeta : $n)) $name) => (elabCtx (labeledArg locals : ((( (local) (labeledArg name : $name) (labeledArg ty : (lit str "𝕀")) (labeledArg isDim : (true)) )) $locals)) (labeledArg global : $g) (labeledArg meta : $m) (labeledArg nextMeta : $n))
      | _ => t

    def elabCtxLookupLocal (t : Term) : Term :=
      match t with
      | (elabCtxLookupLocal (elabCtx (labeledArg locals : $locals) (labeledArg global : $g) (labeledArg meta : $m) (labeledArg nextMeta : $n)) $name) => (lookupLocal $locals $name (num (number 0)))
      | _ => t

    def lookupLocalNil (t : Term) : Term :=
      match t with
      | (lookupLocal (unit ( )) $name $idx) => (none)
      | _ => t

    def lookupLocalConsMatch (t : Term) : Term :=
      match t with
      | (lookupLocal (( ( local (labeledArg name : $name) (labeledArg ty : $ty) (labeledArg isDim : $d) ) $rest )) $name $idx) => (some (tuple ( $idx , $ty )))
      | _ => t

    def lookupLocalConsMiss (t : Term) : Term :=
      match t with
      | (lookupLocal (( ( local (labeledArg name : $n) (labeledArg ty : $ty) (labeledArg isDim : $d) ) $rest )) $name $idx) => (lookupLocal $rest $name (suc $idx))
      | _ => t

    def elabCtxDepth (t : Term) : Term :=
      match t with
      | (elabCtxDepth (elabCtx (labeledArg locals : $locals) (labeledArg global : $g) (labeledArg meta : $m) (labeledArg nextMeta : $n))) => (length $locals)
      | _ => t

    def elabCtxFreshMeta (t : Term) : Term :=
      match t with
      | (elabCtxFreshMeta (elabCtx (labeledArg locals : $locals) (labeledArg global : $g) (labeledArg meta : $m) (labeledArg nextMeta : $n)) $ty) => (record ( result : (elabCtx (labeledArg locals : $locals) (labeledArg global : $g) (labeledArg meta : (metaCtxInsert $m $n (meta (labeledArg ty : $ty) (labeledArg solution : (none))))) (labeledArg nextMeta : (suc $n))) (labeledArg meta : (lit (concat str "meta." $n))) ))
      | _ => t

  end ElabCtx

  section ElabResult

    def elabOk : Parser :=
      (annotated str "ok" str "term:" (special <expr>) str "type:" (special <expr>) str "ctx:" (special <elabCtx>) → elabResult)

    def elabErr : Parser :=
      (annotated str "error" (special <string>) → elabResult)

    def elabResultTerm (t : Term) : Term :=
      match t with
      | (elabResultTerm (ok (labeledArg term : $t) (labeledArg type : $ty) (labeledArg ctx : $c))) => $t
      | _ => t

    def elabResultType (t : Term) : Term :=
      match t with
      | (elabResultType (ok (labeledArg term : $t) (labeledArg type : $ty) (labeledArg ctx : $c))) => $ty
      | _ => t

    def elabResultCtx (t : Term) : Term :=
      match t with
      | (elabResultCtx (ok (labeledArg term : $t) (labeledArg type : $ty) (labeledArg ctx : $c))) => $c
      | _ => t

  end ElabResult

  section Infer

    def inferVar (t : Term) : Term :=
      match t with
      | (infer $ctx (var $name)) => (caseExpr ( case (elabCtxLookupLocal $ctx $name) (arm ( some (tuple ( $idx , $ty )) ) => (ok (labeledArg term : (ix $idx)) (labeledArg type : $ty) (labeledArg ctx : $ctx))) (arm none => (error (concat str "Unknown variable: " $name))) ))
      | _ => t

    def inferLit (t : Term) : Term :=
      match t with
      | (infer $ctx (lit $s)) => (ok (labeledArg term : (lit $s)) (labeledArg type : (univ (lzero))) (labeledArg ctx : $ctx))
      | _ => t

    def inferUniv (t : Term) : Term :=
      match t with
      | (infer $ctx (Type $n)) => (ok (labeledArg term : (univ (levelOfNat $n))) (labeledArg type : (univ (levelOfNat (suc $n)))) (labeledArg ctx : $ctx))
      | _ => t

    def inferPi (t : Term) : Term :=
      match t with
      | (infer $ctx (Π (ann ( $x : $dom )) $cod)) => (caseExpr ( case (infer $ctx $dom) (arm ( ok (labeledArg term : $domCore) (labeledArg type : $domTy) (labeledArg ctx : $ctx') ) => (caseExpr ( case (infer (elabCtxExtend $ctx' $x $domCore) $cod) (arm ( ok (labeledArg term : $codCore) (labeledArg type : $codTy) (labeledArg ctx : $ctx'') ) => (ok (labeledArg term : (pi $domCore $codCore)) (labeledArg type : (univ (lmax (levelOf $domTy) (levelOf $codTy)))) (labeledArg ctx : $ctx''))) (varArm $ err => $err) ))) (varArm $ err => $err) ))
      | _ => t

    def inferSigma (t : Term) : Term :=
      match t with
      | (infer $ctx (Σ (ann ( $x : $dom )) $cod)) => (caseExpr ( case (infer $ctx $dom) (arm ( ok (labeledArg term : $domCore) (labeledArg type : $domTy) (labeledArg ctx : $ctx') ) => (caseExpr ( case (infer (elabCtxExtend $ctx' $x $domCore) $cod) (arm ( ok (labeledArg term : $codCore) (labeledArg type : $codTy) (labeledArg ctx : $ctx'') ) => (ok (labeledArg term : (sigma $domCore $codCore)) (labeledArg type : (univ (lmax (levelOf $domTy) (levelOf $codTy)))) (labeledArg ctx : $ctx''))) (varArm $ err => $err) ))) (varArm $ err => $err) ))
      | _ => t

    def inferApp (t : Term) : Term :=
      match t with
      | (infer $ctx (app $f $x)) => (caseExpr ( case (infer $ctx $f) (arm ( ok (labeledArg term : $fCore) (labeledArg type : (pi $dom $cod)) (labeledArg ctx : $ctx') ) => (caseExpr ( case (check $ctx' $x $dom) (arm ( ok (labeledArg term : $xCore) (labeledArg type : (_)) (labeledArg ctx : $ctx'') ) => (ok (labeledArg term : (app $fCore $xCore)) (labeledArg type : (subst (num (number 0)) $xCore $cod)) (labeledArg ctx : $ctx''))) (varArm $ err => $err) ))) (arm ( ok (labeledArg term : (_)) (labeledArg type : $ty) (labeledArg ctx : (_)) ) => (error (concat str "Expected function type, got " $ty))) (varArm $ err => $err) ))
      | _ => t

    def inferPair (t : Term) : Term :=
      match t with
      | (infer $ctx (⟨ $a (,) $b (⟩))) => (caseExpr ( case (infer $ctx $a) (arm ( ok (labeledArg term : $aCore) (labeledArg type : $aTy) (labeledArg ctx : $ctx') ) => (caseExpr ( case (infer $ctx' $b) (arm ( ok (labeledArg term : $bCore) (labeledArg type : $bTy) (labeledArg ctx : $ctx'') ) => (ok (labeledArg term : (pair $aCore $bCore)) (labeledArg type : (sigma $aTy (shift (num (number 0)) (num (number 1)) $bTy))) (labeledArg ctx : $ctx''))) (varArm $ err => $err) ))) (varArm $ err => $err) ))
      | _ => t

    def inferFst (t : Term) : Term :=
      match t with
      | (infer $ctx (fst $p)) => (caseExpr ( case (infer $ctx $p) (arm ( ok (labeledArg term : $pCore) (labeledArg type : (sigma $dom $cod)) (labeledArg ctx : $ctx') ) => (ok (labeledArg term : (fst $pCore)) (labeledArg type : $dom) (labeledArg ctx : $ctx'))) (arm ( ok (labeledArg term : (_)) (labeledArg type : $ty) (labeledArg ctx : (_)) ) => (error str "Expected sigma type for fst")) (varArm $ err => $err) ))
      | _ => t

    def inferSnd (t : Term) : Term :=
      match t with
      | (infer $ctx (snd $p)) => (caseExpr ( case (infer $ctx $p) (arm ( ok (labeledArg term : $pCore) (labeledArg type : (sigma $dom $cod)) (labeledArg ctx : $ctx') ) => (ok (labeledArg term : (snd $pCore)) (labeledArg type : (subst (num (number 0)) (fst $pCore) $cod)) (labeledArg ctx : $ctx'))) (arm ( ok (labeledArg term : (_)) (labeledArg type : $ty) (labeledArg ctx : (_)) ) => (error str "Expected sigma type for snd")) (varArm $ err => $err) ))
      | _ => t

    def inferAnn (t : Term) : Term :=
      match t with
      | (infer $ctx (ann ( ( $tm : $ty ) ))) => (caseExpr ( case (infer $ctx $ty) (arm ( ok (labeledArg term : $tyCore) (labeledArg type : (_)) (labeledArg ctx : $ctx') ) => (caseExpr ( case (check $ctx' $tm $tyCore) (arm ( ok (labeledArg term : $tmCore) (labeledArg type : (_)) (labeledArg ctx : $ctx'') ) => (ok (labeledArg term : $tmCore) (labeledArg type : $tyCore) (labeledArg ctx : $ctx''))) (varArm $ err => $err) ))) (varArm $ err => $err) ))
      | _ => t

    def inferHole (t : Term) : Term :=
      match t with
      | (infer $ctx (? $name)) => (caseExpr ( case (elabCtxFreshMeta $ctx (univ (lzero))) (arm ( result (:) $ctx' (labeledArg meta : $typeMeta) ) => (caseExpr ( case (elabCtxFreshMeta $ctx' $typeMeta) (arm ( result (:) $ctx'' (labeledArg meta : $termMeta) ) => (ok (labeledArg term : $termMeta) (labeledArg type : $typeMeta) (labeledArg ctx : $ctx''))) ))) ))
      | _ => t

    def inferDim0 (t : Term) : Term :=
      match t with
      | (infer $ctx (num (number 0))) => (ok (labeledArg term : (dim0)) (labeledArg type : (lit str "𝕀")) (labeledArg ctx : $ctx))
      | _ => t

    def inferDim1 (t : Term) : Term :=
      match t with
      | (infer $ctx (num (number 1))) => (ok (labeledArg term : (dim1)) (labeledArg type : (lit str "𝕀")) (labeledArg ctx : $ctx))
      | _ => t

    def inferPath (t : Term) : Term :=
      match t with
      | (infer $ctx (Path $A $a $b)) => (caseExpr ( case (infer $ctx $A) (arm ( ok (labeledArg term : $ACore) (labeledArg type : $ATy) (labeledArg ctx : $ctx') ) => (caseExpr ( case (infer $ctx' $a) (arm ( ok (labeledArg term : $aCore) (labeledArg type : (_)) (labeledArg ctx : $ctx'') ) => (caseExpr ( case (infer $ctx'' $b) (arm ( ok (labeledArg term : $bCore) (labeledArg type : (_)) (labeledArg ctx : $ctx''') ) => (ok (labeledArg term : (path $ACore $aCore $bCore)) (labeledArg type : (univ (levelOf $ATy))) (labeledArg ctx : $ctx'''))) (varArm $ err => $err) ))) (varArm $ err => $err) ))) (varArm $ err => $err) ))
      | _ => t

    def inferPapp (t : Term) : Term :=
      match t with
      | (infer $ctx ($p (@) $r)) => (caseExpr ( case (infer $ctx $p) (arm ( ok (labeledArg term : $pCore) (labeledArg type : (path $A $l $ep)) (labeledArg ctx : $ctx') ) => (caseExpr ( case (infer $ctx' $r) (arm ( ok (labeledArg term : $rCore) (labeledArg type : (_)) (labeledArg ctx : $ctx'') ) => (ok (labeledArg term : (papp $pCore $rCore)) (labeledArg type : $A) (labeledArg ctx : $ctx''))) (varArm $ err => $err) ))) (arm ( ok (labeledArg term : (_)) (labeledArg type : $ty) (labeledArg ctx : (_)) ) => (error str "Expected path type for @")) (varArm $ err => $err) ))
      | _ => t

    def inferRefl (t : Term) : Term :=
      match t with
      | (infer $ctx (refl $a)) => (caseExpr ( case (infer $ctx $a) (arm ( ok (labeledArg term : $aCore) (labeledArg type : $aTy) (labeledArg ctx : $ctx') ) => (ok (labeledArg term : (refl $aCore)) (labeledArg type : (path $aTy $aCore $aCore)) (labeledArg ctx : $ctx'))) (varArm $ err => $err) ))
      | _ => t

  end Infer

  section Check

    def checkLam (t : Term) : Term :=
      match t with
      | (check $ctx (λ (binder $ x . $body)) (pi $dom $cod)) => (caseExpr ( case (check (elabCtxExtend $ctx $x $dom) $body $cod) (arm ( ok (labeledArg term : $bodyCore) (labeledArg type : (_)) (labeledArg ctx : $ctx') ) => (ok (labeledArg term : (lam $bodyCore)) (labeledArg type : (pi $dom $cod)) (labeledArg ctx : $ctx'))) (varArm $ err => $err) ))
      | _ => t

    def checkPlam (t : Term) : Term :=
      match t with
      | (check $ctx (λ (binder $ i . $body)) (path $A $l $r)) => (caseExpr ( case (check (elabCtxExtendDim $ctx $i) $body $A) (arm ( ok (labeledArg term : $bodyCore) (labeledArg type : (_)) (labeledArg ctx : $ctx') ) => (ok (labeledArg term : (plam $bodyCore)) (labeledArg type : (path $A $l $r)) (labeledArg ctx : $ctx'))) (varArm $ err => $err) ))
      | _ => t

    def checkPair (t : Term) : Term :=
      match t with
      | (check $ctx (⟨ $a (,) $b (⟩)) (sigma $dom $cod)) => (caseExpr ( case (check $ctx $a $dom) (arm ( ok (labeledArg term : $aCore) (labeledArg type : (_)) (labeledArg ctx : $ctx') ) => (letIn ( let codSubst = (subst (num (number 0)) $aCore $cod) in (caseExpr case (check $ctx' $b (codSubst)) (arm ( ok (labeledArg term : $bCore) (labeledArg type : (_)) (labeledArg ctx : $ctx'') ) => (ok (labeledArg term : (pair $aCore $bCore)) (labeledArg type : (sigma $dom $cod)) (labeledArg ctx : $ctx''))) (varArm $ err => $err)) ))) (varArm $ err => $err) ))
      | _ => t

    def checkLet (t : Term) : Term :=
      match t with
      | (check $ctx (let (typedVar $ x : $ty) (=) $val (in) $body) $expected) => (caseExpr ( case (infer $ctx $ty) (arm ( ok (labeledArg term : $tyCore) (labeledArg type : (_)) (labeledArg ctx : $ctx') ) => (caseExpr ( case (check $ctx' $val $tyCore) (arm ( ok (labeledArg term : $valCore) (labeledArg type : (_)) (labeledArg ctx : $ctx'') ) => (caseExpr ( case (check (elabCtxExtend $ctx'' $x $tyCore) $body $expected) (arm ( ok (labeledArg term : $bodyCore) (labeledArg type : (_)) (labeledArg ctx : $ctx''') ) => (ok (labeledArg term : (letE $tyCore $valCore $bodyCore)) (labeledArg type : $expected) (labeledArg ctx : $ctx'''))) (varArm $ err => $err) ))) (varArm $ err => $err) ))) (varArm $ err => $err) ))
      | _ => t

    def checkHole (t : Term) : Term :=
      match t with
      | (check $ctx (? $name) $expected) => (caseExpr ( case (elabCtxFreshMeta $ctx $expected) (arm ( result (:) $ctx' (labeledArg meta : $termMeta) ) => (ok (labeledArg term : $termMeta) (labeledArg type : $expected) (labeledArg ctx : $ctx'))) ))
      | _ => t

    def checkRefl (t : Term) : Term :=
      match t with
      | (check $ctx (refl $a) (path $A $l $r)) => (caseExpr ( case (check $ctx $a $l) (arm ( ok (labeledArg term : $aCore) (labeledArg type : (_)) (labeledArg ctx : $ctx') ) => (ok (labeledArg term : (refl $aCore)) (labeledArg type : (path $A $l $r)) (labeledArg ctx : $ctx'))) (varArm $ err => $err) ))
      | _ => t

    def checkFallback (t : Term) : Term :=
      match t with
      | (check $ctx $s $expected) => (caseExpr ( case (infer $ctx $s) (arm ( ok (labeledArg term : $core) (labeledArg type : $inferred) (labeledArg ctx : $ctx') ) => (caseExpr ( case (conv $inferred $expected) (arm true => (ok (labeledArg term : $core) (labeledArg type : $expected) (labeledArg ctx : $ctx'))) (arm false => (error (concat str "Type mismatch: expected " $expected str ", got " $inferred))) ))) (varArm $ err => $err) ))
      | _ => t

  end Check

  section Conv

    def conv (t : Term) : Term :=
      match t with
      | (conv $t1 $t2) => (letIn ( let t1' = (normalize (num (number 100)) $t1) in (letIn let t2' = (normalize (num (number 100)) $t2) in (eq (t1') (t2'))) ))
      | _ => t

  end Conv

  section TopLevel

    def elaborate (t : Term) : Term :=
      match t with
      | (elaborate $env $s $ty) => (caseExpr ( case (check (elabCtxWithGlobals $env) $s $ty) (arm ( ok (labeledArg term : $result) (labeledArg type : (_)) (labeledArg ctx : (_)) ) => (ok $result)) (arm ( error $msg ) => (error $msg)) ))
      | _ => t

    def elaborateInfer (t : Term) : Term :=
      match t with
      | (elaborateInfer $env $s) => (caseExpr ( case (infer (elabCtxWithGlobals $env) $s) (arm ( ok (labeledArg term : $t) (labeledArg type : $ty) (labeledArg ctx : (_)) ) => (ok (tuple ( $t , $ty )))) (arm ( error $msg ) => (error $msg)) ))
      | _ => t

  end TopLevel

  section CheckType

    def checkType (t : Term) : Term :=
      match t with
      | (checkType $ctx $s) => (caseExpr ( case (infer $ctx $s) (arm ( ok (labeledArg term : $tyCore) (labeledArg type : (univ $level)) (labeledArg ctx : $ctx') ) => (ok (record ( type : $tyCore (labeledArg level : $level) (labeledArg ctx : $ctx') )))) (arm ( ok (labeledArg term : (_)) (labeledArg type : $ty) (labeledArg ctx : (_)) ) => (error (concat str "Expected a type, got " $ty))) (varArm $ err => $err) ))
      | _ => t

    def checkTypeAtLevel (t : Term) : Term :=
      match t with
      | (checkTypeAtLevel $ctx $s $expected) => (caseExpr ( case (checkType $ctx $s) (arm ( ok (type (:) $tyCore (labeledArg level : $level) (labeledArg ctx : $ctx')) ) => (caseExpr ( case (levelLeq $level $expected) (arm true => (ok (labeledArg term : $tyCore) (labeledArg ctx : $ctx'))) (arm false => (error (concat str "Universe level mismatch: expected ≤ " $expected str ", got " $level))) ))) (varArm $ err => $err) ))
      | _ => t

  end CheckType

  section Telescope

    def teleEntry : Parser :=
      (annotated str "teleEntry" str "name:" (special <symbol>) str "surface:" (special <surface>) → teleEntry)

    def checkTelescope (t : Term) : Term :=
      match t with
      | (checkTelescope $ctx (unit ( ))) => (ok (record ( tele : (unit ( )) (labeledArg ctx : $ctx) )))
      | _ => t

    def checkTelescopeCons (t : Term) : Term :=
      match t with
      | (checkTelescope $ctx (( ( teleEntry (labeledArg name : $name) (labeledArg surface : $s) ) $rest ))) => (caseExpr ( case (checkType $ctx $s) (arm ( ok (type (:) $tyCore (labeledArg level : (_)) (labeledArg ctx : $ctx')) ) => (caseExpr ( case (checkTelescope (elabCtxExtend $ctx' $name $tyCore) $rest) (arm ( ok (tele (:) $restTele (labeledArg ctx : $ctx'')) ) => (ok (record ( tele : ((tuple ( $name , $tyCore )) $restTele) (labeledArg ctx : $ctx'') )))) (varArm $ err => $err) ))) (varArm $ err => $err) ))
      | _ => t

    def teleToPi (t : Term) : Term :=
      match t with
      | (teleToPi (unit ( )) $cod) => $cod
      | _ => t

    def teleToPiCons (t : Term) : Term :=
      match t with
      | (teleToPi (( ( $x (,) $dom ) $rest )) $cod) => (pi $dom (teleToPi $rest $cod))
      | _ => t

  end Telescope

  section SurfaceExt

    def surfExtBase : Parser :=
      (annotated str "base" (special <surface>) → surfaceExt)

    def surfCofEq : Parser :=
      (annotated str "cof_eq" (special <surfaceExt>) (special <surfaceExt>) → surfaceExt)

    def surfCofAnd : Parser :=
      (annotated str "cof_and" (special <surfaceExt>) (special <surfaceExt>) → surfaceExt)

    def surfCofOr : Parser :=
      (annotated str "cof_or" (special <surfaceExt>) (special <surfaceExt>) → surfaceExt)

    def surfCofTop : Parser :=
      (annotated str "cof_top" → surfaceExt)

    def surfCofBot : Parser :=
      (annotated str "cof_bot" → surfaceExt)

    def surfBoundary : Parser :=
      (annotated str "boundary" (special <surfaceExt>) → surfaceExt)

    def surfCoe : Parser :=
      (annotated str "coe" (special <surfaceExt>) (special <surfaceExt>) (special <surfaceExt>) (special <surfaceExt>) → surfaceExt)

    def surfHcom : Parser :=
      (annotated str "hcom" (special <surfaceExt>) (special <surfaceExt>) (special <surfaceExt>) (special <surfaceExt>) (special <surfaceExt>) → surfaceExt)

    def surfCom : Parser :=
      (annotated str "com" (special <surfaceExt>) (special <surfaceExt>) (special <surfaceExt>) many ((special <sysEntry>)) (special <surfaceExt>) → surfaceExt)

    def sysEntry : Parser :=
      (annotated str "[" (special <surfaceExt>) str "↦" (special <surfaceExt>) str "]" → sysEntry)

    def surfVType : Parser :=
      (annotated str "V" (special <surfaceExt>) (special <surfaceExt>) (special <surfaceExt>) (special <surfaceExt>) → surfaceExt)

    def surfVIn : Parser :=
      (annotated str "vin" (special <surfaceExt>) (special <surfaceExt>) (special <surfaceExt>) → surfaceExt)

    def surfVProj : Parser :=
      (annotated str "vproj" (special <surfaceExt>) (special <surfaceExt>) → surfaceExt)

    def surfExt : Parser :=
      (annotated str "ext" (special <number>) (special <surfaceExt>) (special <surfaceExt>) (special <surfaceExt>) → surfaceExt)

    def surfExtLam : Parser :=
      (annotated str "extLam" (special <number>) (special <surfaceExt>) → surfaceExt)

    def surfExtApp : Parser :=
      (annotated str "extApp" (special <surfaceExt>) many ((special <surfaceExt>)) → surfaceExt)

    def surfSub : Parser :=
      (annotated str "sub" (special <surfaceExt>) (special <surfaceExt>) (special <surfaceExt>) → surfaceExt)

    def surfSubIn : Parser :=
      (annotated str "subIn" (special <surfaceExt>) → surfaceExt)

    def surfSubOut : Parser :=
      (annotated str "subOut" (special <surfaceExt>) → surfaceExt)

  end SurfaceExt

  section Helpers

    def mkPiNil (t : Term) : Term :=
      match t with
      | (mkPi (unit ( )) $cod) => $cod
      | _ => t

    def mkPiCons (t : Term) : Term :=
      match t with
      | (mkPi (( ( $x (,) $ty ) $rest )) $cod) => (Π (typed ( $x : $ty )) (mkPi $rest $cod))
      | _ => t

    def mkLamNil (t : Term) : Term :=
      match t with
      | (mkLam (unit ( )) $body) => $body
      | _ => t

    def mkLamCons (t : Term) : Term :=
      match t with
      | (mkLam ($x $rest) $body) => (λ (binder $ x . (mkLam $rest $body)))
      | _ => t

    def mkAppsNil (t : Term) : Term :=
      match t with
      | (mkApps $f (unit ( ))) => $f
      | _ => t

    def mkAppsCons (t : Term) : Term :=
      match t with
      | (mkApps $f ($a $rest)) => (mkApps (app $f $a) $rest)
      | _ => t

  end Helpers

  section Examples

    def idSurface (t : Term) : Term :=
      match t with
      | (idSurface) => (lamParen ( λ x . (var (x)) ))
      | _ => t

    def idTypeSurface (t : Term) : Term :=
      match t with
      | (idTypeSurface) => (Π (typed ( (A) : (Type (num (number 0))) )) (Π (typed ( (x) : (var (A)) )) (var (A))))
      | _ => t

    def constSurface (t : Term) : Term :=
      match t with
      | (constSurface) => (lamParen ( λ x . (lamParen ( λ y . (var (x)) )) ))
      | _ => t

    def flipSurface (t : Term) : Term :=
      match t with
      | (flipSurface) => (lamParen ( λ f . (lamParen ( λ x . (lamParen ( λ y . (app (app (var (f)) (var (y))) (var (x))) )) )) ))
      | _ => t

    def zeroSurface (t : Term) : Term :=
      match t with
      | (zeroSurface) => (introExpr ( intro Nat . zero (unit ( )) ))
      | _ => t

    def sucSurface (t : Term) : Term :=
      match t with
      | (sucSurface $n) => (introExpr ( intro Nat . suc ($n) ))
      | _ => t

    def twoSurface (t : Term) : Term :=
      match t with
      | (twoSurface) => (sucSurface (sucSurface (zeroSurface)))
      | _ => t

  end Examples

end Elaborate