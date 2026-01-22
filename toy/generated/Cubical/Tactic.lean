(DImport import (modulePath Core) ;)

(DImport import (modulePath Cofibration) ;)

(DImport import (modulePath Splice) ;)

namespace Tactic

  section TacResult

    def tacResult : Parser :=
      ((annotated str "tacOk" (special <any>) → tacOk) <|> (annotated str "tacError" (special <name>) → tacError))

    def isTacOk (t : Term) : Term :=
      match t with
      | (isTacOk (tacOk $a)) => (true)
      | _ => t

    def isTacOkErr (t : Term) : Term :=
      match t with
      | (isTacOk (tacError $msg)) => (false)
      | _ => t

    def tacResultMap (t : Term) : Term :=
      match t with
      | (tacResultMap $f (tacOk $a)) => (tacOk ($f $a))
      | _ => t

    def tacResultMapErr (t : Term) : Term :=
      match t with
      | (tacResultMap $f (tacError $msg)) => (tacError $msg)
      | _ => t

    def tacResultBind (t : Term) : Term :=
      match t with
      | (tacResultBind (tacOk $a) $f) => ($f $a)
      | _ => t

    def tacResultBindErr (t : Term) : Term :=
      match t with
      | (tacResultBind (tacError $msg) $f) => (tacError $msg)
      | _ => t

    def tacResultPure (t : Term) : Term :=
      match t with
      | (tacResultPure $a) => (tacOk $a)
      | _ => t

    def tacResultGetOrElse (t : Term) : Term :=
      match t with
      | (tacResultGetOrElse (tacOk $a) $default) => $a
      | _ => t

    def tacResultGetOrElseErr (t : Term) : Term :=
      match t with
      | (tacResultGetOrElse (tacError $msg) $default) => $default
      | _ => t

  end TacResult

  section TpCtx

    def tpCtx : Parser :=
      (annotated str "tpCtx" str "types:" many ((special <expr>)) str "cofs:" many ((special <expr>)) → tpCtx)

    def tpCtxEmpty (t : Term) : Term :=
      match t with
      | (tpCtxEmpty) => (tpCtx (labeledArg types : (unit ( ))) (labeledArg cofs : (unit ( ))))
      | _ => t

    def tpCtxExtend (t : Term) : Term :=
      match t with
      | (tpCtxExtend (tpCtx (labeledArg types : $ts) (labeledArg cofs : $cs)) $ty) => (tpCtx (labeledArg types : ($ty $ts)) (labeledArg cofs : $cs))
      | _ => t

    def tpCtxLookup (t : Term) : Term :=
      match t with
      | (tpCtxLookup (tpCtx (labeledArg types : $ts) (labeledArg cofs : $cs)) $n) => (listGet $ts $n)
      | _ => t

    def tpCtxSize (t : Term) : Term :=
      match t with
      | (tpCtxSize (tpCtx (labeledArg types : $ts) (labeledArg cofs : $cs))) => (length $ts)
      | _ => t

    def tpCtxAssume (t : Term) : Term :=
      match t with
      | (tpCtxAssume (tpCtx (labeledArg types : $ts) (labeledArg cofs : $cs)) $φ) => (tpCtx (labeledArg types : $ts) (labeledArg cofs : ($φ $cs)))
      | _ => t

    def tpCtxIsConsistent (t : Term) : Term :=
      match t with
      | (tpCtxIsConsistent (tpCtx (labeledArg types : $ts) (labeledArg cofs : $cs))) => (cofIsConsistent (meetAll $cs))
      | _ => t

    def meetAll (t : Term) : Term :=
      match t with
      | (meetAll (unit ( ))) => (cof_top)
      | _ => t

    def meetAllCons (t : Term) : Term :=
      match t with
      | (meetAll ($φ $rest)) => (cof_and $φ (meetAll $rest))
      | _ => t

  end TpCtx

  section ChkGoal

    def chkGoal : Parser :=
      (annotated str "chkGoal" str "tp:" (special <expr>) str "cof:" (special <expr>) str "bdry:" (special <expr>) → chkGoal)

    def chkGoalSimple (t : Term) : Term :=
      match t with
      | (chkGoalSimple $ty) => (chkGoal (labeledArg tp : $ty) (labeledArg cof : (cof_top)) (labeledArg bdry : (lit str "unit")))
      | _ => t

    def chkGoalWithBoundary (t : Term) : Term :=
      match t with
      | (chkGoalWithBoundary $ty $φ $bdry) => (chkGoal (labeledArg tp : $ty) (labeledArg cof : $φ) (labeledArg bdry : $bdry))
      | _ => t

    def chkGoalTp (t : Term) : Term :=
      match t with
      | (chkGoalTp (chkGoal (labeledArg tp : $t) (labeledArg cof : $c) (labeledArg bdry : $b))) => $t
      | _ => t

    def chkGoalCof (t : Term) : Term :=
      match t with
      | (chkGoalCof (chkGoal (labeledArg tp : $t) (labeledArg cof : $c) (labeledArg bdry : $b))) => $c
      | _ => t

    def chkGoalBdry (t : Term) : Term :=
      match t with
      | (chkGoalBdry (chkGoal (labeledArg tp : $t) (labeledArg cof : $c) (labeledArg bdry : $b))) => $b
      | _ => t

  end ChkGoal

  section TpTac

    def tpTacRun (t : Term) : Term :=
      match t with
      | (tpTacRun $tac $ctx) => ($tac $ctx)
      | _ => t

    def tpTacPure (t : Term) : Term :=
      match t with
      | (tpTacPure $e $ctx) => (tacOk $e)
      | _ => t

    def tpTacNat (t : Term) : Term :=
      match t with
      | (tpTacNat $ctx) => (tacOk (nat))
      | _ => t

    def tpTacCircle (t : Term) : Term :=
      match t with
      | (tpTacCircle $ctx) => (tacOk (S1))
      | _ => t

    def tpTacUniv (t : Term) : Term :=
      match t with
      | (tpTacUniv $ctx) => (tacOk (univ (num (number 0))))
      | _ => t

    def tpTacDim (t : Term) : Term :=
      match t with
      | (tpTacDim $ctx) => (tacOk (lit str "𝕀"))
      | _ => t

    def tpTacCof (t : Term) : Term :=
      match t with
      | (tpTacCof $ctx) => (tacOk (lit str "Cof"))
      | _ => t

    def tpTacPi (t : Term) : Term :=
      match t with
      | (tpTacPi $domTac $codTac $ctx) => (tacResultBind ($domTac $ctx) (lam (letIn ( let $ ctx' = (tpCtxExtend $ctx (ix (num (number 0)))) in (tacResultBind ($codTac (ix (num (number 0))) $ctx') (lam (tacOk (pi (ix (num (number 1))) (ix (num (number 0))))))) ))))
      | _ => t

    def tpTacSigma (t : Term) : Term :=
      match t with
      | (tpTacSigma $baseTac $famTac $ctx) => (tacResultBind ($baseTac $ctx) (lam (letIn ( let $ ctx' = (tpCtxExtend $ctx (ix (num (number 0)))) in (tacResultBind ($famTac (ix (num (number 0))) $ctx') (lam (tacOk (sigma (ix (num (number 1))) (ix (num (number 0))))))) ))))
      | _ => t

    def tpTacPath (t : Term) : Term :=
      match t with
      | (tpTacPath $tyLineTac $left $right $ctx) => (tacResultBind ($tyLineTac $ctx) (lam (tacOk (path (ix (num (number 0))) $left $right))))
      | _ => t

    def tpTacSub (t : Term) : Term :=
      match t with
      | (tpTacSub $tyTac $φ $tm $ctx) => (tacResultBind ($tyTac $ctx) (lam (tacOk (sub (ix (num (number 0))) $φ $tm))))
      | _ => t

    def tpTacMap (t : Term) : Term :=
      match t with
      | (tpTacMap $f $tac $ctx) => (tacResultMap $f ($tac $ctx))
      | _ => t

  end TpTac

  section ChkTac

    def chkTacRun (t : Term) : Term :=
      match t with
      | (chkTacRun $tac $ctx $tp) => ($tac $ctx (chkGoalSimple $tp))
      | _ => t

    def chkTacBRun (t : Term) : Term :=
      match t with
      | (chkTacBRun $tac $ctx $tp $φ $bdry) => ($tac $ctx (chkGoalWithBoundary $tp $φ $bdry))
      | _ => t

    def chkTacPure (t : Term) : Term :=
      match t with
      | (chkTacPure $e $ctx $goal) => (tacOk $e)
      | _ => t

    def chkTacZero (t : Term) : Term :=
      match t with
      | (chkTacZero $ctx $goal) => (caseExpr ( case (chkGoalTp $goal) (arm nat => (tacOk (zero))) (arm _ => (tacError str "expected Nat")) ))
      | _ => t

    def chkTacSuc (t : Term) : Term :=
      match t with
      | (chkTacSuc $tac $ctx $goal) => (caseExpr ( case (chkGoalTp $goal) (arm nat => (tacResultBind ($tac $ctx (chkGoalSimple (nat))) (lam (tacOk (suc (ix (num (number 0)))))))) (arm _ => (tacError str "expected Nat")) ))
      | _ => t

    def chkTacLam (t : Term) : Term :=
      match t with
      | (chkTacLam $bodyTac $ctx $goal) => (caseExpr ( case (chkGoalTp $goal) (arm ( pi $dom $cod ) => (letIn ( let $ ctx' = (tpCtxExtend $ctx $dom) in (letIn ( let $ goalCod = (chkGoalSimple $cod) in (tacResultBind ($bodyTac (ix (num (number 0))) $ctx' $goalCod) (lam (tacOk (lam (ix (num (number 0))))))) )) ))) (arm _ => (tacError str "expected Pi type")) ))
      | _ => t

    def chkTacPair (t : Term) : Term :=
      match t with
      | (chkTacPair $fstTac $sndTac $ctx $goal) => (caseExpr ( case (chkGoalTp $goal) (arm ( sigma $base $fam ) => (tacResultBind ($fstTac $ctx (chkGoalSimple $base)) (lam (letIn ( let $ famSubst = (subst (num (number 0)) (ix (num (number 0))) $fam) in (tacResultBind ($sndTac $ctx (chkGoalSimple $famSubst)) (lam (tacOk (pair (ix (num (number 1))) (ix (num (number 0))))))) ))))) (arm _ => (tacError str "expected Sigma type")) ))
      | _ => t

    def chkTacPlam (t : Term) : Term :=
      match t with
      | (chkTacPlam $bodyTac $ctx $goal) => (letIn ( let $ ctx' = (tpCtxExtend $ctx (lit str "𝕀")) in (tacResultBind ($bodyTac (ix (num (number 0))) $ctx' (chkGoalSimple (chkGoalTp $goal))) (lam (tacOk (plam (ix (num (number 0))))))) ))
      | _ => t

    def chkTacBase (t : Term) : Term :=
      match t with
      | (chkTacBase $ctx $goal) => (caseExpr ( case (chkGoalTp $goal) (arm S1 => (tacOk (base))) (arm _ => (tacError str "expected Circle")) ))
      | _ => t

    def chkTacLoop (t : Term) : Term :=
      match t with
      | (chkTacLoop $dimTac $ctx $goal) => (caseExpr ( case (chkGoalTp $goal) (arm S1 => (tacResultBind ($dimTac $ctx (chkGoalSimple (lit str "𝕀"))) (lam (tacOk (loop (ix (num (number 0)))))))) (arm _ => (tacError str "expected Circle")) ))
      | _ => t

    def chkTacSubIn (t : Term) : Term :=
      match t with
      | (chkTacSubIn $tac $ctx $goal) => (caseExpr ( case (chkGoalTp $goal) (arm ( sub $a $φ $t ) => (tacResultBind ($tac $ctx (chkGoalSimple $a)) (lam (tacOk (subIn (ix (num (number 0)))))))) (arm _ => (tacError str "expected Sub type")) ))
      | _ => t

  end ChkTac

  section SynTac

    def synTacRun (t : Term) : Term :=
      match t with
      | (synTacRun $tac $ctx) => ($tac $ctx)
      | _ => t

    def synTacPure (t : Term) : Term :=
      match t with
      | (synTacPure $e $ty $ctx) => (tacOk (tuple ( $e , $ty )))
      | _ => t

    def synTacVar (t : Term) : Term :=
      match t with
      | (synTacVar $n $ctx) => (caseExpr ( case (tpCtxLookup $ctx $n) (arm ( some $ty ) => (tacOk (tuple ( (ix $n) , $ty )))) (arm none => (tacError str "unbound variable")) ))
      | _ => t

    def synTacApp (t : Term) : Term :=
      match t with
      | (synTacApp $fnTac $argTac $ctx) => (tacResultBind ($fnTac $ctx) (lam (caseExpr ( case (snd (ix (num (number 0)))) (arm ( pi $dom $cod ) => (tacResultBind ($argTac $ctx (chkGoalSimple $dom)) (lam (letIn ( let $ codSubst = (subst (num (number 0)) (ix (num (number 0))) $cod) in (tacOk (tuple ( (app (fst (ix (num (number 1)))) (ix (num (number 0)))) , $codSubst ))) ))))) (arm _ => (tacError str "expected function type")) ))))
      | _ => t

    def synTacFst (t : Term) : Term :=
      match t with
      | (synTacFst $pairTac $ctx) => (tacResultBind ($pairTac $ctx) (lam (caseExpr ( case (snd (ix (num (number 0)))) (arm ( sigma $base $fam ) => (tacOk (tuple ( (fst (fst (ix (num (number 0))))) , $base )))) (arm _ => (tacError str "expected Sigma type")) ))))
      | _ => t

    def synTacSnd (t : Term) : Term :=
      match t with
      | (synTacSnd $pairTac $ctx) => (tacResultBind ($pairTac $ctx) (lam (caseExpr ( case (snd (ix (num (number 0)))) (arm ( sigma $base $fam ) => (letIn ( let $ fstVal = (fst (fst (ix (num (number 0))))) in (letIn ( let $ famSubst = (subst (num (number 0)) $fstVal $fam) in (tacOk (tuple ( (snd (fst (ix (num (number 0))))) , $famSubst ))) )) ))) (arm _ => (tacError str "expected Sigma type")) ))))
      | _ => t

    def synTacPApp (t : Term) : Term :=
      match t with
      | (synTacPApp $pathTac $dimTac $ctx) => (tacResultBind ($pathTac $ctx) (lam (tacResultBind ($dimTac $ctx (chkGoalSimple (lit str "𝕀"))) (lam (tacOk (tuple ( (papp (fst (ix (num (number 1)))) (ix (num (number 0)))) , (lit str "path-fiber") )))))))
      | _ => t

    def synTacSubOut (t : Term) : Term :=
      match t with
      | (synTacSubOut $subTac $ctx) => (tacResultBind ($subTac $ctx) (lam (caseExpr ( case (snd (ix (num (number 0)))) (arm ( sub $a $φ $t ) => (tacOk (tuple ( (subOut (fst (ix (num (number 0))))) , $a )))) (arm _ => (tacError str "expected Sub type")) ))))
      | _ => t

  end SynTac

  section VarTac

    def varTacIntro (t : Term) : Term :=
      match t with
      | (varTacIntro $name $ty $k $ctx) => (letIn ( let $ ctx' = (tpCtxExtend $ctx $ty) in ($k (ix (num (number 0))) $ctx') ))
      | _ => t

    def varTacDim (t : Term) : Term :=
      match t with
      | (varTacDim $name $k $ctx) => (letIn ( let $ ctx' = (tpCtxExtend $ctx (lit str "𝕀")) in ($k (ix (num (number 0))) $ctx') ))
      | _ => t

    def varTacCof (t : Term) : Term :=
      match t with
      | (varTacCof $φ $k $ctx) => (letIn ( let $ ctx' = (tpCtxAssume $ctx $φ) in ($k $ctx') ))
      | _ => t

  end VarTac

  section TacHelpers

    def tacSequence (t : Term) : Term :=
      match t with
      | (tacSequence (unit ( )) $ctx $goal) => (tacOk (unit ( )))
      | _ => t

    def tacSequenceCons (t : Term) : Term :=
      match t with
      | (tacSequence ($tac $rest) $ctx $goal) => (tacResultBind ($tac $ctx $goal) (lam (tacResultBind (tacSequence $rest $ctx $goal) (lam (tacOk ((( (ix) (num (number 1)) )) (ix (num (number 0)))))))))
      | _ => t

    def tacChoice (t : Term) : Term :=
      match t with
      | (tacChoice (unit ( )) $ctx $goal) => (tacError str "no tactics succeeded")
      | _ => t

    def tacChoiceCons (t : Term) : Term :=
      match t with
      | (tacChoice ($tac $rest) $ctx $goal) => (caseExpr ( case ($tac $ctx $goal) (arm ( tacOk $a ) => (tacOk $a)) (arm ( tacError $msg ) => (tacChoice $rest $ctx $goal)) ))
      | _ => t

    def tacWithFreshVar (t : Term) : Term :=
      match t with
      | (tacWithFreshVar $ty $bodyTac $ctx $goal) => (letIn ( let $ ctx' = (tpCtxExtend $ctx $ty) in ($bodyTac (ix (num (number 0))) $ctx' $goal) ))
      | _ => t

    def tacWithCofAssump (t : Term) : Term :=
      match t with
      | (tacWithCofAssump $φ $bodyTac $ctx $goal) => (letIn ( let $ ctx' = (tpCtxAssume $ctx $φ) in ($bodyTac $ctx' $goal) ))
      | _ => t

  end TacHelpers

end Tactic