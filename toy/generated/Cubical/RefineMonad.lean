(DImport import (modulePath Core) ;)

(DImport import (modulePath Cofibration) ;)

(DImport import (modulePath Conversion) ;)

namespace RefineMonad

  section RefineError

    def refineError : Parser :=
      ((annotated str "unboundVariable" (special <name>) → unboundVariable) <|> ((annotated str "expectedType" (special <expr>) → expectedType) <|> ((annotated str "typeMismatch" (special <expr>) (special <expr>) → typeMismatch) <|> ((annotated str "expectedConnective" (special <name>) (special <expr>) → expectedConnective) <|> ((annotated str "conversionFailed" (special <name>) → conversionFailed) <|> ((annotated str "unboundMeta" (special <nat>) → unboundMeta) <|> (annotated str "otherError" (special <name>) → otherError)))))))

    def refineErrorToString (t : Term) : Term :=
      match t with
      | (refineErrorToString (unboundVariable $n)) => (strConcat str "Unbound variable: " $n)
      | _ => t

    def refineErrorToStringExpected (t : Term) : Term :=
      match t with
      | (refineErrorToString (expectedType $e)) => (strConcat str "Expected type, got: " (exprToString $e))
      | _ => t

    def refineErrorToStringMismatch (t : Term) : Term :=
      match t with
      | (refineErrorToString (typeMismatch $e1 $e2)) => (strConcat str "Type mismatch: " (strConcat (exprToString $e1) (strConcat str " vs " (exprToString $e2))))
      | _ => t

    def refineErrorToStringConnective (t : Term) : Term :=
      match t with
      | (refineErrorToString (expectedConnective $n $e)) => (strConcat str "Expected " (strConcat $n (strConcat str ", got: " (exprToString $e))))
      | _ => t

    def refineErrorToStringConv (t : Term) : Term :=
      match t with
      | (refineErrorToString (conversionFailed $n)) => (strConcat str "Conversion failed: " $n)
      | _ => t

    def refineErrorToStringMeta (t : Term) : Term :=
      match t with
      | (refineErrorToString (unboundMeta $n)) => (strConcat str "Unbound meta: " (natToString $n))
      | _ => t

    def refineErrorToStringOther (t : Term) : Term :=
      match t with
      | (refineErrorToString (otherError $n)) => $n
      | _ => t

  end RefineError

  section Ident

    def ident : Parser :=
      ((annotated str "anon" → anon) <|> ((annotated str "user" (special <name>) → userIdent) <|> (annotated str "machine" (special <name>) → machineIdent)))

    def identName (t : Term) : Term :=
      match t with
      | (identName (anon)) => (none)
      | _ => t

    def identNameUser (t : Term) : Term :=
      match t with
      | (identName (userIdent $s)) => (some $s)
      | _ => t

    def identNameMachine (t : Term) : Term :=
      match t with
      | (identName (machineIdent $s)) => (some $s)
      | _ => t

    def identToString (t : Term) : Term :=
      match t with
      | (identToString (anon)) => str "_"
      | _ => t

    def identToStringUser (t : Term) : Term :=
      match t with
      | (identToString (userIdent $s)) => $s
      | _ => t

    def identToStringMachine (t : Term) : Term :=
      match t with
      | (identToString (machineIdent $s)) => $s
      | _ => t

  end Ident

  section Cell

    def cell : Parser :=
      (annotated str "cell" str "id:" (special <ident>) str "tp:" (special <expr>) str "val:" (special <option>) → cell)

    def cellIdent (t : Term) : Term :=
      match t with
      | (cellIdent (cell (labeledArg id : $i) (labeledArg tp : $t) (labeledArg val : $v))) => $i
      | _ => t

    def cellTp (t : Term) : Term :=
      match t with
      | (cellTp (cell (labeledArg id : $i) (labeledArg tp : $t) (labeledArg val : $v))) => $t
      | _ => t

    def cellVal (t : Term) : Term :=
      match t with
      | (cellVal (cell (labeledArg id : $i) (labeledArg tp : $t) (labeledArg val : $v))) => $v
      | _ => t

    def mkCell (t : Term) : Term :=
      match t with
      | (mkCell $ident $tp) => (cell (labeledArg id : $ident) (labeledArg tp : $tp) (labeledArg val : (none)))
      | _ => t

    def mkCellVal (t : Term) : Term :=
      match t with
      | (mkCellVal $ident $tp $val) => (cell (labeledArg id : $ident) (labeledArg tp : $tp) (labeledArg val : (some $val)))
      | _ => t

  end Cell

  section LocalEnv

    def localEnv : Parser :=
      (annotated str "localEnv" str "cells:" many ((special <cell>)) str "cof:" (special <expr>) → localEnv)

    def localEnvEmpty (t : Term) : Term :=
      match t with
      | (localEnvEmpty) => (localEnv (labeledArg cells : (unit ( ))) (labeledArg cof : (cof_top)))
      | _ => t

    def localEnvSize (t : Term) : Term :=
      match t with
      | (localEnvSize (localEnv (labeledArg cells : $cs) (labeledArg cof : $φ))) => (length $cs)
      | _ => t

    def localEnvExtend (t : Term) : Term :=
      match t with
      | (localEnvExtend (localEnv (labeledArg cells : $cs) (labeledArg cof : $φ)) $ident $tp) => (localEnv (labeledArg cells : ($cs (mkCell $ident $tp))) (labeledArg cof : $φ))
      | _ => t

    def localEnvExtendVal (t : Term) : Term :=
      match t with
      | (localEnvExtendVal (localEnv (labeledArg cells : $cs) (labeledArg cof : $φ)) $ident $tp $val) => (localEnv (labeledArg cells : ($cs (mkCellVal $ident $tp $val))) (labeledArg cof : $φ))
      | _ => t

    def localEnvGetLocal (t : Term) : Term :=
      match t with
      | (localEnvGetLocal (localEnv (labeledArg cells : $cs) (labeledArg cof : $φ)) $ix) => (listGet $cs (minus (length $cs) (num (number 1)) $ix))
      | _ => t

    def localEnvGetLocalTp (t : Term) : Term :=
      match t with
      | (localEnvGetLocalTp $env $ix) => (caseExpr ( case (localEnvGetLocal $env $ix) (arm ( some $c ) => (some (cellTp $c))) (arm none => (none)) ))
      | _ => t

    def localEnvResolve (t : Term) : Term :=
      match t with
      | (localEnvResolve (localEnv (labeledArg cells : $cs) (labeledArg cof : $φ)) $name) => (localEnvResolveRec $cs $name (num (number 0)))
      | _ => t

    def localEnvResolveRec (t : Term) : Term :=
      match t with
      | (localEnvResolveRec (unit ( )) $name $i) => (none)
      | _ => t

    def localEnvResolveRecCons (t : Term) : Term :=
      match t with
      | (localEnvResolveRec ($cs $c) $name $i) => (caseExpr ( case (identName (cellIdent $c)) (arm ( some $n ) => (if (eq $n $name) (then (some $i) else) (localEnvResolveRec $cs $name (succ $i)))) (arm none => (localEnvResolveRec $cs $name (succ $i))) ))
      | _ => t

    def localEnvAssume (t : Term) : Term :=
      match t with
      | (localEnvAssume (localEnv (labeledArg cells : $cs) (labeledArg cof : $φ)) $ψ) => (localEnv (labeledArg cells : $cs) (labeledArg cof : (cof_and $φ $ψ)))
      | _ => t

  end LocalEnv

  section GlobalDef

    def globalDef : Parser :=
      (annotated str "globalDef" str "name:" (special <name>) str "tp:" (special <expr>) str "val:" (special <option>) → globalDef)

    def globalDefName (t : Term) : Term :=
      match t with
      | (globalDefName (globalDef (labeledArg name : $n) (labeledArg tp : $t) (labeledArg val : $v))) => $n
      | _ => t

    def globalDefTp (t : Term) : Term :=
      match t with
      | (globalDefTp (globalDef (labeledArg name : $n) (labeledArg tp : $t) (labeledArg val : $v))) => $t
      | _ => t

    def globalDefVal (t : Term) : Term :=
      match t with
      | (globalDefVal (globalDef (labeledArg name : $n) (labeledArg tp : $t) (labeledArg val : $v))) => $v
      | _ => t

  end GlobalDef

  section GlobalEnvState

    def globalEnvState : Parser :=
      (annotated str "globalEnvState" str "defs:" many ((special <globalDef>)) str "holes:" many ((special <holeEntry>)) str "nextHole:" (special <nat>) str "nextMeta:" (special <nat>) → globalEnvState)

    def holeEntry : Parser :=
      (annotated str "(" (special <nat>) str "," (special <expr>) str "," (special <option>) str ")" → holeEntry)

    def globalEnvStateEmpty (t : Term) : Term :=
      match t with
      | (globalEnvStateEmpty) => (globalEnvState (labeledArg defs : (unit ( ))) (labeledArg holes : (unit ( ))) (labeledArg nextHole : (num (number 0))) (labeledArg nextMeta : (num (number 0))))
      | _ => t

    def globalEnvStateAddDef (t : Term) : Term :=
      match t with
      | (globalEnvStateAddDef $name $tp $val (globalEnvState (labeledArg defs : $ds) (labeledArg holes : $hs) (labeledArg nextHole : $nh) (labeledArg nextMeta : $nm))) => (globalEnvState (labeledArg defs : ($ds (globalDef (labeledArg name : $name) (labeledArg tp : $tp) (labeledArg val : $val)))) (labeledArg holes : $hs) (labeledArg nextHole : $nh) (labeledArg nextMeta : $nm))
      | _ => t

    def globalEnvStateLookupDef (t : Term) : Term :=
      match t with
      | (globalEnvStateLookupDef $name (globalEnvState (labeledArg defs : $ds) (labeledArg holes : $hs) (labeledArg nextHole : $nh) (labeledArg nextMeta : $nm))) => (lookupDef $name $ds)
      | _ => t

    def lookupDef (t : Term) : Term :=
      match t with
      | (lookupDef $name (unit ( ))) => (none)
      | _ => t

    def lookupDefMatch (t : Term) : Term :=
      match t with
      | (lookupDef $name ($ds (globalDef (labeledArg name : $name) (labeledArg tp : $t) (labeledArg val : $v)))) => (some (globalDef (labeledArg name : $name) (labeledArg tp : $t) (labeledArg val : $v)))
      | _ => t

    def lookupDefMiss (t : Term) : Term :=
      match t with
      | (lookupDef $name ($ds $d)) => (lookupDef $name $ds)
      | _ => t

    def globalEnvStateAddHole (t : Term) : Term :=
      match t with
      | (globalEnvStateAddHole $tp (globalEnvState (labeledArg defs : $ds) (labeledArg holes : $hs) (labeledArg nextHole : $nh) (labeledArg nextMeta : $nm))) => (tuple ( (globalEnvState (labeledArg defs : $ds) (labeledArg holes : ($hs (nTuple ( $nh , $tp , (none) )))) (labeledArg nextHole : (succ $nh)) (labeledArg nextMeta : $nm)) , $nh ))
      | _ => t

    def globalEnvStateFreshMeta (t : Term) : Term :=
      match t with
      | (globalEnvStateFreshMeta (globalEnvState (labeledArg defs : $ds) (labeledArg holes : $hs) (labeledArg nextHole : $nh) (labeledArg nextMeta : $nm))) => (tuple ( (globalEnvState (labeledArg defs : $ds) (labeledArg holes : $hs) (labeledArg nextHole : $nh) (labeledArg nextMeta : (succ $nm))) , $nm ))
      | _ => t

    def globalEnvStateSolveHole (t : Term) : Term :=
      match t with
      | (globalEnvStateSolveHole $id $sol (globalEnvState (labeledArg defs : $ds) (labeledArg holes : $hs) (labeledArg nextHole : $nh) (labeledArg nextMeta : $nm))) => (globalEnvState (labeledArg defs : $ds) (labeledArg holes : (solveHoleInList $id $sol $hs)) (labeledArg nextHole : $nh) (labeledArg nextMeta : $nm))
      | _ => t

    def solveHoleInList (t : Term) : Term :=
      match t with
      | (solveHoleInList $id $sol (unit ( ))) => (unit ( ))
      | _ => t

    def solveHoleInListMatch (t : Term) : Term :=
      match t with
      | (solveHoleInList $id $sol (( ( $id (,) $tp (,) $old ) $rest ))) => ((nTuple ( $id , $tp , (some $sol) )) (solveHoleInList $id $sol $rest))
      | _ => t

    def solveHoleInListMiss (t : Term) : Term :=
      match t with
      | (solveHoleInList $id $sol (( ( $hid (,) $tp (,) $old ) $rest ))) => ((nTuple ( $hid , $tp , $old )) (solveHoleInList $id $sol $rest))
      | _ => t

    def globalEnvStateGetHoleSolution (t : Term) : Term :=
      match t with
      | (globalEnvStateGetHoleSolution $id (globalEnvState (labeledArg defs : $ds) (labeledArg holes : $hs) (labeledArg nextHole : $nh) (labeledArg nextMeta : $nm))) => (getHoleSolution $id $hs)
      | _ => t

    def getHoleSolution (t : Term) : Term :=
      match t with
      | (getHoleSolution $id (unit ( ))) => (none)
      | _ => t

    def getHoleSolutionMatch (t : Term) : Term :=
      match t with
      | (getHoleSolution $id (( ( $id (,) $tp (,) $sol ) $rest ))) => $sol
      | _ => t

    def getHoleSolutionMiss (t : Term) : Term :=
      match t with
      | (getHoleSolution $id (( ( $hid (,) $tp (,) $sol ) $rest ))) => (getHoleSolution $id $rest)
      | _ => t

  end GlobalEnvState

  section SourceLoc

    def sourceLoc : Parser :=
      (annotated str "sourceLoc" str "file:" (special <name>) str "line:" (special <nat>) str "col:" (special <nat>) → sourceLoc)

    def sourceLocFile (t : Term) : Term :=
      match t with
      | (sourceLocFile (sourceLoc (labeledArg file : $f) (labeledArg line : $l) (labeledArg col : $c))) => $f
      | _ => t

    def sourceLocLine (t : Term) : Term :=
      match t with
      | (sourceLocLine (sourceLoc (labeledArg file : $f) (labeledArg line : $l) (labeledArg col : $c))) => $l
      | _ => t

    def sourceLocCol (t : Term) : Term :=
      match t with
      | (sourceLocCol (sourceLoc (labeledArg file : $f) (labeledArg line : $l) (labeledArg col : $c))) => $c
      | _ => t

  end SourceLoc

  section RefineCtx

    def refineCtx : Parser :=
      (annotated str "refineCtx" str "local:" (special <localEnv>) str "loc:" (special <option>) → refineCtx)

    def refineCtxEmpty (t : Term) : Term :=
      match t with
      | (refineCtxEmpty) => (refineCtx (labeledArg local : (localEnvEmpty)) (labeledArg loc : (none)))
      | _ => t

    def refineCtxLocalEnv (t : Term) : Term :=
      match t with
      | (refineCtxLocalEnv (refineCtx (labeledArg local : $l) (labeledArg loc : $s))) => $l
      | _ => t

    def refineCtxLoc (t : Term) : Term :=
      match t with
      | (refineCtxLoc (refineCtx (labeledArg local : $l) (labeledArg loc : $s))) => $s
      | _ => t

    def refineCtxSetLocal (t : Term) : Term :=
      match t with
      | (refineCtxSetLocal $env (refineCtx (labeledArg local : $l) (labeledArg loc : $s))) => (refineCtx (labeledArg local : $env) (labeledArg loc : $s))
      | _ => t

    def refineCtxSetLoc (t : Term) : Term :=
      match t with
      | (refineCtxSetLoc $loc (refineCtx (labeledArg local : $l) (labeledArg loc : $s))) => (refineCtx (labeledArg local : $l) (labeledArg loc : (some $loc)))
      | _ => t

  end RefineCtx

  section RefineState

    def refineState : Parser :=
      (annotated str "refineState" str "global:" (special <globalEnvState>) → refineState)

    def refineStateEmpty (t : Term) : Term :=
      match t with
      | (refineStateEmpty) => (refineState (labeledArg global : (globalEnvStateEmpty)))
      | _ => t

    def refineStateGlobal (t : Term) : Term :=
      match t with
      | (refineStateGlobal (refineState (labeledArg global : $g))) => $g
      | _ => t

    def refineStateSetGlobal (t : Term) : Term :=
      match t with
      | (refineStateSetGlobal $g (refineState (labeledArg global : $old))) => (refineState (labeledArg global : $g))
      | _ => t

  end RefineState

  section RefineResult

    def refineResult : Parser :=
      ((annotated str "refineOk" (special <any>) (special <refineState>) → refineOk) <|> (annotated str "refineError" (special <refineError>) (special <option>) → refineErr))

    def isRefineOk (t : Term) : Term :=
      match t with
      | (isRefineOk (refineOk $a $s)) => (true)
      | _ => t

    def isRefineOkErr (t : Term) : Term :=
      match t with
      | (isRefineOk (refineErr $e $l)) => (false)
      | _ => t

    def refineResultVal (t : Term) : Term :=
      match t with
      | (refineResultVal (refineOk $a $s)) => (some $a)
      | _ => t

    def refineResultValErr (t : Term) : Term :=
      match t with
      | (refineResultVal (refineErr $e $l)) => (none)
      | _ => t

    def refineResultState (t : Term) : Term :=
      match t with
      | (refineResultState (refineOk $a $s)) => (some $s)
      | _ => t

    def refineResultStateErr (t : Term) : Term :=
      match t with
      | (refineResultState (refineErr $e $l)) => (none)
      | _ => t

  end RefineResult

  section RefineM

    def refinePure (t : Term) : Term :=
      match t with
      | (refinePure $a $ctx $st) => (refineOk $a $st)
      | _ => t

    def refineBind (t : Term) : Term :=
      match t with
      | (refineBind $ma $f $ctx $st) => (caseExpr ( case ($ma $ctx $st) (arm ( refineOk $a $st' ) => ((( $f $a )) $ctx $st')) (arm ( refineErr $e $l ) => (refineErr $e $l)) ))
      | _ => t

    def refineGetLocalEnv (t : Term) : Term :=
      match t with
      | (refineGetLocalEnv $ctx $st) => (refineOk (refineCtxLocalEnv $ctx) $st)
      | _ => t

    def refineGetGlobalEnv (t : Term) : Term :=
      match t with
      | (refineGetGlobalEnv $ctx $st) => (refineOk (refineStateGlobal $st) $st)
      | _ => t

    def refineModifyGlobal (t : Term) : Term :=
      match t with
      | (refineModifyGlobal $f $ctx $st) => (refineOk (unit ( )) (refineStateSetGlobal ($f (refineStateGlobal $st)) $st))
      | _ => t

    def refineWithLocal (t : Term) : Term :=
      match t with
      | (refineWithLocal $f $ma $ctx $st) => ($ma (refineCtxSetLocal ($f (refineCtxLocalEnv $ctx)) $ctx) $st)
      | _ => t

    def refineWithLoc (t : Term) : Term :=
      match t with
      | (refineWithLoc $loc $ma $ctx $st) => ($ma (refineCtxSetLoc $loc $ctx) $st)
      | _ => t

    def refineThrow (t : Term) : Term :=
      match t with
      | (refineThrow $e $ctx $st) => (refineErr $e (refineCtxLoc $ctx))
      | _ => t

  end RefineM

  section VarOps

    def refineAbstract (t : Term) : Term :=
      match t with
      | (refineAbstract $ident $tp $k $ctx $st) => (letIn ( let $ var = (ix (localEnvSize (refineCtxLocalEnv $ctx))) in (letIn ( let $ newEnv = (localEnvExtend (refineCtxLocalEnv $ctx) $ident $tp) in ((( $k $var )) (refineCtxSetLocal $newEnv $ctx) $st) )) ))
      | _ => t

    def refineGetLocalTp (t : Term) : Term :=
      match t with
      | (refineGetLocalTp $ix $ctx $st) => (caseExpr ( case (localEnvGetLocalTp (refineCtxLocalEnv $ctx) $ix) (arm ( some $tp ) => (refineOk $tp $st)) (arm none => (refineErr (unboundVariable (natToString $ix)) (refineCtxLoc $ctx))) ))
      | _ => t

    def refineResolveName (t : Term) : Term :=
      match t with
      | (refineResolveName $name $ctx $st) => (caseExpr ( case (localEnvResolve (refineCtxLocalEnv $ctx) $name) (arm ( some $ix ) => (refineOk (inl $ix) $st)) (arm none => (caseExpr ( case (globalEnvStateLookupDef $name (refineStateGlobal $st)) (arm ( some $def ) => (refineOk (inr $def) $st)) (arm none => (refineErr (unboundVariable $name) (refineCtxLoc $ctx))) ))) ))
      | _ => t

  end VarOps

  section HoleOps

    def refineFreshHole (t : Term) : Term :=
      match t with
      | (refineFreshHole $tp $ctx $st) => (letTupleIn ( let ( $st' , $id ) = (globalEnvStateAddHole $tp (refineStateGlobal $st)) in (refineOk (tuple ( $id , (lit (strConcat str "?" (natToString $id))) )) (refineStateSetGlobal $st' $st)) ))
      | _ => t

    def refineFreshMeta (t : Term) : Term :=
      match t with
      | (refineFreshMeta $ctx $st) => (letTupleIn ( let ( $g' , $id ) = (globalEnvStateFreshMeta (refineStateGlobal $st)) in (refineOk $id (refineStateSetGlobal $g' $st)) ))
      | _ => t

    def refineSolveHole (t : Term) : Term :=
      match t with
      | (refineSolveHole $id $sol $ctx $st) => (refineOk (unit ( )) (refineStateSetGlobal (globalEnvStateSolveHole $id $sol (refineStateGlobal $st)) $st))
      | _ => t

    def refineGetHoleSolution (t : Term) : Term :=
      match t with
      | (refineGetHoleSolution $id $ctx $st) => (refineOk (globalEnvStateGetHoleSolution $id (refineStateGlobal $st)) $st)
      | _ => t

  end HoleOps

end RefineMonad