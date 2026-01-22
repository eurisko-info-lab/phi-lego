(DImport import (modulePath Core) ;)

(DImport import (modulePath Cofibration) ;)

(DImport import (modulePath Visitor) ;)

namespace Splice

  section SpliceEnv

    def spliceEnv : Parser :=
      (annotated str "spliceEnv" str "conEnv:" many (term) str "tpEnv:" many (term) → spliceEnv)

    def spliceEnvEmpty (t : Term) : Term :=
      match t with
      | (spliceEnvEmpty) => (spliceEnv (labeledArg conEnv : (unit ( ))) (labeledArg tpEnv : (unit ( ))))
      | _ => t

    def spliceEnvAddCon (t : Term) : Term :=
      match t with
      | (spliceEnvAddCon $e (spliceEnv (labeledArg conEnv : $cs) (labeledArg tpEnv : $ts))) => (spliceEnv (labeledArg conEnv : ($e $cs)) (labeledArg tpEnv : $ts))
      | _ => t

    def spliceEnvAddTp (t : Term) : Term :=
      match t with
      | (spliceEnvAddTp $e (spliceEnv (labeledArg conEnv : $cs) (labeledArg tpEnv : $ts))) => (spliceEnv (labeledArg conEnv : $cs) (labeledArg tpEnv : ($e $ts)))
      | _ => t

    def spliceEnvConLevel (t : Term) : Term :=
      match t with
      | (spliceEnvConLevel (spliceEnv (labeledArg conEnv : $cs) (labeledArg tpEnv : $ts))) => (length $cs)
      | _ => t

    def spliceEnvTpLevel (t : Term) : Term :=
      match t with
      | (spliceEnvTpLevel (spliceEnv (labeledArg conEnv : $cs) (labeledArg tpEnv : $ts))) => (length $ts)
      | _ => t

  end SpliceEnv

  section SpliceM

    def spliceRun (t : Term) : Term :=
      match t with
      | (spliceRun $s) => ($s (spliceEnvEmpty))
      | _ => t

    def spliceEval (t : Term) : Term :=
      match t with
      | (spliceEval $s) => (fst (spliceRun $s))
      | _ => t

    def spliceGetEnv (t : Term) : Term :=
      match t with
      | (spliceGetEnv $s) => (snd (spliceRun $s))
      | _ => t

    def splicePure (t : Term) : Term :=
      match t with
      | (splicePure $a $env) => (tuple ( $a , $env ))
      | _ => t

    def spliceBind (t : Term) : Term :=
      match t with
      | (spliceBind $m $f $env) => (letTupleIn ( let ( $a , $env' ) = ($m $env) in ((( $f $a )) $env') ))
      | _ => t

    def spliceRead (t : Term) : Term :=
      match t with
      | (spliceRead $env) => (tuple ( $env , $env ))
      | _ => t

    def spliceModify (t : Term) : Term :=
      match t with
      | (spliceModify $f $env) => (tuple ( (unit ( )) , ($f $env) ))
      | _ => t

  end SpliceM

  section Foreign

    def foreign (t : Term) : Term :=
      match t with
      | (foreign $con $k $env) => (letIn ( let $ lvl = (spliceEnvConLevel $env) in (letIn ( let $ env' = (spliceEnvAddCon $con $env) in (letIn ( let $ var = (ix $lvl) in ((( $k $var )) $env') )) )) ))
      | _ => t

    def foreignList (t : Term) : Term :=
      match t with
      | (foreignList (unit ( )) $k $env) => ((( $k (unit ( )) )) $env)
      | _ => t

    def foreignListCons (t : Term) : Term :=
      match t with
      | (foreignList ($c $cs) $k $env) => (foreign $c (lam (foreignList $cs (lam ((( $k ((( (ix) (num (number 1)) )) (ix (num (number 0)))) )))) $env')) $env)
      | _ => t

    def foreignDim (t : Term) : Term :=
      match t with
      | (foreignDim $d $k $env) => (foreign $d $k $env)
      | _ => t

    def foreignCof (t : Term) : Term :=
      match t with
      | (foreignCof $φ $k $env) => (foreign $φ $k $env)
      | _ => t

    def foreignClo (t : Term) : Term :=
      match t with
      | (foreignClo $clo $k $env) => (foreign (lam $clo) $k $env)
      | _ => t

    def foreignTp (t : Term) : Term :=
      match t with
      | (foreignTp $tp $k $env) => (letIn ( let $ lvl = (spliceEnvTpLevel $env) in (letIn ( let $ env' = (spliceEnvAddTp $tp $env) in (letIn ( let $ var = (ix $lvl) in ((( $k $var )) $env') )) )) ))
      | _ => t

  end Foreign

  section SpliceBuilders

    def spliceLam (t : Term) : Term :=
      match t with
      | (spliceLam $name $bodyBuilder $env) => (letTupleIn ( let ( $body , $env' ) = ($bodyBuilder (spliceEnvAddCon (ix (spliceEnvConLevel $env)) $env)) in (tuple ( (lam $body) , $env' )) ))
      | _ => t

    def splicePi (t : Term) : Term :=
      match t with
      | (splicePi $name $domBuilder $codBuilder $env) => (letTupleIn ( let ( $dom , $env1 ) = ($domBuilder $env) in (letTupleIn ( let ( $cod , $env2 ) = ($codBuilder (spliceEnvAddCon (ix (spliceEnvConLevel $env1)) $env1)) in (tuple ( (pi $dom $cod) , $env2 )) )) ))
      | _ => t

    def spliceSigma (t : Term) : Term :=
      match t with
      | (spliceSigma $name $fstTyBuilder $sndTyBuilder $env) => (letTupleIn ( let ( $fstTy , $env1 ) = ($fstTyBuilder $env) in (letTupleIn ( let ( $sndTy , $env2 ) = ($sndTyBuilder (spliceEnvAddCon (ix (spliceEnvConLevel $env1)) $env1)) in (tuple ( (sigma $fstTy $sndTy) , $env2 )) )) ))
      | _ => t

    def splicePlam (t : Term) : Term :=
      match t with
      | (splicePlam $bodyBuilder $env) => (letTupleIn ( let ( $body , $env' ) = ($bodyBuilder (spliceEnvAddCon (ix (spliceEnvConLevel $env)) $env)) in (tuple ( (plam $body) , $env' )) ))
      | _ => t

    def splicePath (t : Term) : Term :=
      match t with
      | (splicePath $aBuilder $lBuilder $rBuilder $env) => (letTupleIn ( let ( $a , $env1 ) = ($aBuilder $env) in (letTupleIn ( let ( $l , $env2 ) = ($lBuilder $env1) in (letTupleIn ( let ( $r , $env3 ) = ($rBuilder $env2) in (tuple ( (path $a $l $r) , $env3 )) )) )) ))
      | _ => t

  end SpliceBuilders

  section SpliceDim

    def spliceDim0 (t : Term) : Term :=
      match t with
      | (spliceDim0 $env) => (tuple ( (dim0) , $env ))
      | _ => t

    def spliceDim1 (t : Term) : Term :=
      match t with
      | (spliceDim1 $env) => (tuple ( (dim1) , $env ))
      | _ => t

    def spliceDimVar (t : Term) : Term :=
      match t with
      | (spliceDimVar $i $env) => (tuple ( (ix $i) , $env ))
      | _ => t

    def spliceDimMeet (t : Term) : Term :=
      match t with
      | (spliceDimMeet $d1Builder $d2Builder $env) => (letTupleIn ( let ( $d1 , $env1 ) = ($d1Builder $env) in (letTupleIn ( let ( $d2 , $env2 ) = ($d2Builder $env1) in (tuple ( (dim_and $d1 $d2) , $env2 )) )) ))
      | _ => t

    def spliceDimJoin (t : Term) : Term :=
      match t with
      | (spliceDimJoin $d1Builder $d2Builder $env) => (letTupleIn ( let ( $d1 , $env1 ) = ($d1Builder $env) in (letTupleIn ( let ( $d2 , $env2 ) = ($d2Builder $env1) in (tuple ( (dim_or $d1 $d2) , $env2 )) )) ))
      | _ => t

    def spliceDimNeg (t : Term) : Term :=
      match t with
      | (spliceDimNeg $dBuilder $env) => (letTupleIn ( let ( $d , $env' ) = ($dBuilder $env) in (tuple ( (dim_neg $d) , $env' )) ))
      | _ => t

  end SpliceDim

  section SpliceCof

    def spliceCofTop (t : Term) : Term :=
      match t with
      | (spliceCofTop $env) => (tuple ( (cof_top) , $env ))
      | _ => t

    def spliceCofBot (t : Term) : Term :=
      match t with
      | (spliceCofBot $env) => (tuple ( (cof_bot) , $env ))
      | _ => t

    def spliceCofEq (t : Term) : Term :=
      match t with
      | (spliceCofEq $d1Builder $d2Builder $env) => (letTupleIn ( let ( $d1 , $env1 ) = ($d1Builder $env) in (letTupleIn ( let ( $d2 , $env2 ) = ($d2Builder $env1) in (tuple ( (cof_eq $d1 $d2) , $env2 )) )) ))
      | _ => t

    def spliceCofAnd (t : Term) : Term :=
      match t with
      | (spliceCofAnd $φ1Builder $φ2Builder $env) => (letTupleIn ( let ( $φ1 , $env1 ) = ($φ1Builder $env) in (letTupleIn ( let ( $φ2 , $env2 ) = ($φ2Builder $env1) in (tuple ( (cof_and $φ1 $φ2) , $env2 )) )) ))
      | _ => t

    def spliceCofOr (t : Term) : Term :=
      match t with
      | (spliceCofOr $φ1Builder $φ2Builder $env) => (letTupleIn ( let ( $φ1 , $env1 ) = ($φ1Builder $env) in (letTupleIn ( let ( $φ2 , $env2 ) = ($φ2Builder $env1) in (tuple ( (cof_disj $φ1 $φ2) , $env2 )) )) ))
      | _ => t

  end SpliceCof

  section SpliceKan

    def spliceCoe (t : Term) : Term :=
      match t with
      | (spliceCoe $rBuilder $r'Builder $tyLineBuilder $elBuilder $env) => (letTupleIn ( let ( $r , $env1 ) = ($rBuilder $env) in (letTupleIn ( let ( $r' , $env2 ) = ($r'Builder $env1) in (letTupleIn ( let ( $tyLine , $env3 ) = ($tyLineBuilder $env2) in (letTupleIn ( let ( $el , $env4 ) = ($elBuilder $env3) in (tuple ( (coe $r $r' $tyLine $el) , $env4 )) )) )) )) ))
      | _ => t

    def spliceHcom (t : Term) : Term :=
      match t with
      | (spliceHcom $rBuilder $r'Builder $tyBuilder $φBuilder $tubesBuilder $capBuilder $env) => (letTupleIn ( let ( $r , $env1 ) = ($rBuilder $env) in (letTupleIn ( let ( $r' , $env2 ) = ($r'Builder $env1) in (letTupleIn ( let ( $ty , $env3 ) = ($tyBuilder $env2) in (letTupleIn ( let ( $φ , $env4 ) = ($φBuilder $env3) in (letTupleIn ( let ( $tubes , $env5 ) = ($tubesBuilder $env4) in (letTupleIn ( let ( $cap , $env6 ) = ($capBuilder $env5) in (tuple ( (hcom $ty $r $r' $φ $tubes $cap) , $env6 )) )) )) )) )) )) ))
      | _ => t

    def spliceCom (t : Term) : Term :=
      match t with
      | (spliceCom $rBuilder $r'Builder $tyLineBuilder $φBuilder $tubesBuilder $capBuilder $env) => (letTupleIn ( let ( $r , $env1 ) = ($rBuilder $env) in (letTupleIn ( let ( $r' , $env2 ) = ($r'Builder $env1) in (letTupleIn ( let ( $tyLine , $env3 ) = ($tyLineBuilder $env2) in (letTupleIn ( let ( $φ , $env4 ) = ($φBuilder $env3) in (letTupleIn ( let ( $tubes , $env5 ) = ($tubesBuilder $env4) in (letTupleIn ( let ( $cap , $env6 ) = ($capBuilder $env5) in (tuple ( (com $tyLine $r $r' $φ $tubes $cap) , $env6 )) )) )) )) )) )) ))
      | _ => t

  end SpliceKan

  section Compile

    def compile (t : Term) : Term :=
      match t with
      | (compile $splice) => (spliceRun $splice)
      | _ => t

    def compileResult (t : Term) : Term :=
      match t with
      | (compileResult $splice) => (spliceEval $splice)
      | _ => t

    def compileEnv (t : Term) : Term :=
      match t with
      | (compileEnv $splice) => (spliceGetEnv $splice)
      | _ => t

  end Compile

  section SpliceEval

    def spliceEvalTerm (t : Term) : Term :=
      match t with
      | (spliceEvalTerm $term (spliceEnv (labeledArg conEnv : $cs) (labeledArg tpEnv : $ts))) => (substMany $term $cs)
      | _ => t

    def substMany (t : Term) : Term :=
      match t with
      | (substMany $term (unit ( ))) => $term
      | _ => t

    def substManyCons (t : Term) : Term :=
      match t with
      | (substMany $term ($v $rest)) => (substMany (subst (num (number 0)) $v $term) $rest)
      | _ => t

  end SpliceEval

end Splice