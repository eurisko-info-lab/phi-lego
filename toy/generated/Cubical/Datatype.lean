(DImport import (modulePath Core) ;)

(DImport import (modulePath GlobalEnv) ;)

namespace Datatype

  section DataType

    def mkData (t : Term) : Term :=
      match t with
      | (mkData $dlbl (unit ( ))) => (lit (concat str "data." $dlbl))
      | _ => t

    def mkDataParams (t : Term) : Term :=
      match t with
      | (mkData $dlbl ($p $rest)) => (app (mkData $dlbl $rest) $p)
      | _ => t

    def isData (t : Term) : Term :=
      match t with
      | (isData $e) => (getDataHead $e (unit ( )))
      | _ => t

    def getDataHeadLit (t : Term) : Term :=
      match t with
      | (getDataHead (lit $s) $acc) => (caseExpr ( case (startsWith $s str "data.") (arm true => (some (tuple ( (drop (num (number 5)) $s) , $acc )))) (arm false => (none)) ))
      | _ => t

    def getDataHeadApp (t : Term) : Term :=
      match t with
      | (getDataHead (app $f $a) $acc) => (getDataHead $f ($a $acc))
      | _ => t

    def getDataHeadOther (t : Term) : Term :=
      match t with
      | (getDataHead $e $acc) => (none)
      | _ => t

  end DataType

  section Intro

    def mkIntro (t : Term) : Term :=
      match t with
      | (mkIntro $dlbl $clbl $params $args) => (mkIntro' $dlbl $clbl (length $params) $params $args)
      | _ => t

    def mkIntro' (t : Term) : Term :=
      match t with
      | (mkIntro' $dlbl $clbl $paramCount (unit ( )) (unit ( ))) => (lit (concat str "intro." $dlbl str "." $clbl str "." $paramCount))
      | _ => t

    def mkIntro'Params (t : Term) : Term :=
      match t with
      | (mkIntro' $dlbl $clbl $paramCount ($p $rest) $args) => (app (mkIntro' $dlbl $clbl $paramCount $rest $args) $p)
      | _ => t

    def mkIntro'Args (t : Term) : Term :=
      match t with
      | (mkIntro' $dlbl $clbl $paramCount (unit ( )) ($a $rest)) => (app (mkIntro' $dlbl $clbl $paramCount (unit ( )) $rest) $a)
      | _ => t

    def isIntro (t : Term) : Term :=
      match t with
      | (isIntro $e) => (letIn ( let headArgs = (collectArgs $e (unit ( ))) in (parseIntro (fst (headArgs)) (snd (headArgs))) ))
      | _ => t

    def collectArgsApp (t : Term) : Term :=
      match t with
      | (collectArgs (app $f $a) $acc) => (collectArgs $f ($a $acc))
      | _ => t

    def collectArgsOther (t : Term) : Term :=
      match t with
      | (collectArgs $e $acc) => (tuple ( $e , $acc ))
      | _ => t

    def parseIntro (t : Term) : Term :=
      match t with
      | (parseIntro (lit $s) $allArgs) => (caseExpr ( case (startsWith $s str "intro.") (arm true => (parseIntroRest (drop (num (number 6)) $s) $allArgs)) (arm false => (none)) ))
      | _ => t

    def parseIntroOther (t : Term) : Term :=
      match t with
      | (parseIntro $e $args) => (none)
      | _ => t

    def parseIntroRest (t : Term) : Term :=
      match t with
      | (parseIntroRest $rest $allArgs) => (caseExpr ( case (splitOn $rest str ".") (arm ( $dlbl $clbl $countStr ) => (letIn ( let paramCount = (toNat $countStr) in (letIn let params = (take (paramCount) $allArgs) in (letIn let args = (drop (paramCount) $allArgs) in (some (nTuple ( $dlbl , $clbl , (params) ,

(args) ))))) ))) (arm ( $dlbl $clbl ) => (some (nTuple ( $dlbl , $clbl , (unit ( )) ,

$allArgs )))) (arm _ => (none)) ))
      | _ => t

  end Intro

  section ElimClause

    def elimClause : Parser :=
      (annotated str "clause" str "clbl:" (special <string>) str "body:" (special <expr>) → elimClause)

    def elimClauseClbl (t : Term) : Term :=
      match t with
      | (elimClauseClbl (clause (labeledArg clbl : $c) (labeledArg body : $b))) => $c
      | _ => t

    def elimClauseBody (t : Term) : Term :=
      match t with
      | (elimClauseBody (clause (labeledArg clbl : $c) (labeledArg body : $b))) => $b
      | _ => t

  end ElimClause

  section Elim

    def mkElim (t : Term) : Term :=
      match t with
      | (mkElim $dlbl $params $mot $clauses $scrut) => (letIn ( let base = (lit (concat str "elim." $dlbl)) in (letIn let withParams = (foldl (app) (base) $params) in (letIn let withMot = (app (withParams) $mot) in (letIn let clauseExpr = (encodeClauseList $clauses) in (letIn let withClauses = (app (withMot) (clauseExpr)) in (app (withClauses) $scrut))))) ))
      | _ => t

    def encodeClauseListNil (t : Term) : Term :=
      match t with
      | (encodeClauseList (unit ( ))) => (lit str "clauses.nil")
      | _ => t

    def encodeClauseListCons (t : Term) : Term :=
      match t with
      | (encodeClauseList (( ( clause (labeledArg clbl : $c) (labeledArg body : $b) ) $rest ))) => (letIn ( let tag = (lit (concat str "clause." $c)) in (letIn let thisClause = (app (tag) $b) in (app (app (lit str "clauses.cons") (thisClause)) (encodeClauseList $rest))) ))
      | _ => t

    def isElim (t : Term) : Term :=
      match t with
      | (isElim $e) => (letIn ( let headArgs = (collectArgs $e (unit ( ))) in (parseElim (fst (headArgs)) (snd (headArgs))) ))
      | _ => t

    def parseElim (t : Term) : Term :=
      match t with
      | (parseElim (lit $s) $args) => (caseExpr ( case (startsWith $s str "elim.") (arm true => (some (drop (num (number 5)) $s))) (arm false => (none)) ))
      | _ => t

    def parseElimOther (t : Term) : Term :=
      match t with
      | (parseElim $e $args) => (none)
      | _ => t

  end Elim

  section EvalIntro

    def evalIntroZero (t : Term) : Term :=
      match t with
      | (evalIntro (lit str "intro.Nat.zero.0") (unit ( ))) => (zero)
      | _ => t

    def evalIntroSuc (t : Term) : Term :=
      match t with
      | (evalIntro (lit str "intro.Nat.suc.0") ($n)) => (suc $n)
      | _ => t

    def evalIntroNil (t : Term) : Term :=
      match t with
      | (evalIntro (lit str "intro.List.nil.1") ($A)) => (nil $A)
      | _ => t

    def evalIntroCons (t : Term) : Term :=
      match t with
      | (evalIntro (lit str "intro.List.cons.1") ($A $x $xs)) => (cons $A $x $xs)
      | _ => t

    def evalIntroBase (t : Term) : Term :=
      match t with
      | (evalIntro (lit str "intro.Circle.base.0") (unit ( ))) => (base)
      | _ => t

    def evalIntroLoop (t : Term) : Term :=
      match t with
      | (evalIntro (lit str "intro.Circle.loop.0") ($r)) => (loop $r)
      | _ => t

    def evalIntroDefault (t : Term) : Term :=
      match t with
      | (evalIntro $head $args) => (foldl (app) $head $args)
      | _ => t

  end EvalIntro

  section EvalElim

    def evalElimNatZero (t : Term) : Term :=
      match t with
      | (evalElim str "Nat" $mot $clauses (zero)) => (lookupClause $clauses str "zero")
      | _ => t

    def evalElimNatSuc (t : Term) : Term :=
      match t with
      | (evalElim str "Nat" $mot $clauses (suc $n)) => (letIn ( let sucClause = (lookupClause $clauses str "suc") in (letIn let ih = (evalElim str "Nat" $mot $clauses $n) in (app (app (sucClause) $n) (ih))) ))
      | _ => t

    def evalElimListNil (t : Term) : Term :=
      match t with
      | (evalElim str "List" $mot $clauses (nil $A)) => (lookupClause $clauses str "nil")
      | _ => t

    def evalElimListCons (t : Term) : Term :=
      match t with
      | (evalElim str "List" $mot $clauses (cons $A $x $xs)) => (letIn ( let consClause = (lookupClause $clauses str "cons") in (letIn let ih = (evalElim str "List" $mot $clauses $xs) in (app (app (app (consClause) $x) $xs) (ih))) ))
      | _ => t

    def evalElimCircleBase (t : Term) : Term :=
      match t with
      | (evalElim str "Circle" $mot $clauses (base)) => (lookupClause $clauses str "base")
      | _ => t

    def evalElimDefault (t : Term) : Term :=
      match t with
      | (evalElim $dlbl $mot $clauses $scrut) => (mkElim $dlbl (unit ( )) $mot $clauses $scrut)
      | _ => t

    def lookupClauseNil (t : Term) : Term :=
      match t with
      | (lookupClause (lit str "clauses.nil") $clbl) => (lit str "clause-not-found")
      | _ => t

    def lookupClauseCons (t : Term) : Term :=
      match t with
      | (lookupClause (app (app (lit str "clauses.cons") $clause) $rest) $clbl) => (letIn ( let clauseTag = (getClauseTag $clause) in (caseExpr case (eq (clauseTag) $clbl) (arm true => (getClauseBody $clause)) (arm false => (lookupClause $rest $clbl))) ))
      | _ => t

    def getClauseTag (t : Term) : Term :=
      match t with
      | (getClauseTag (app (lit $tag) $body)) => (drop (num (number 7)) $tag)
      | _ => t

    def getClauseBody (t : Term) : Term :=
      match t with
      | (getClauseBody (app (lit $tag) $body)) => $body
      | _ => t

  end EvalElim

  section TypeOfIntro

    def typeOfIntro (t : Term) : Term :=
      match t with
      | (typeOfIntro $env $dlbl $clbl $params $args) => (caseExpr ( case (globalEnvLookupDatatype $env (gnameNamed $dlbl)) (arm ( some $desc ) => (typeOfIntro' $desc $clbl $params $args)) (arm none => (none)) ))
      | _ => t

    def typeOfIntro' (t : Term) : Term :=
      match t with
      | (typeOfIntro' $desc $clbl $params $args) => (caseExpr ( case (findConstructor (gdataDescConstrs $desc) $clbl) (arm ( some $constr ) => (some (computeConstrType $desc $constr $params $args))) (arm none => (none)) ))
      | _ => t

    def findConstructorNil (t : Term) : Term :=
      match t with
      | (findConstructor (unit ( )) $clbl) => (none)
      | _ => t

    def findConstructorMatch (t : Term) : Term :=
      match t with
      | (findConstructor (( ( constructor (labeledArg name : $clbl) (labeledArg args : $a) (labeledArg boundary : $b) ) $rest )) $clbl) => (some (constructor (labeledArg name : $clbl) (labeledArg args : $a) (labeledArg boundary : $b)))
      | _ => t

    def findConstructorMiss (t : Term) : Term :=
      match t with
      | (findConstructor ($c $rest) $clbl) => (findConstructor $rest $clbl)
      | _ => t

    def computeConstrType (t : Term) : Term :=
      match t with
      | (computeConstrType $desc $constr $params $args) => (mkData (gnameName (gdataDescName $desc)) $params)
      | _ => t

  end TypeOfIntro

  section TypeOfElim

    def typeOfElim (t : Term) : Term :=
      match t with
      | (typeOfElim $env $dlbl $params $mot $clauses $scrut) => (app $mot $scrut)
      | _ => t

  end TypeOfElim

  section BuiltinDatatypes

    def natDesc (t : Term) : Term :=
      match t with
      | (natDesc) => (dataDesc (labeledArg name : (gnameNamed str "Nat")) (labeledArg params : (unit ( ))) (labeledArg level : (lzero)) (labeledArg constrs : ((( (constructor) (labeledArg name : str "zero") (labeledArg args : (unit ( ))) (labeledArg boundary : (unit ( ))) )) (constructor (labeledArg name : str "suc") (labeledArg args : ((typed ( str "n" : (recursive) )))) (labeledArg boundary : (unit ( )))))))
      | _ => t

    def listDesc (t : Term) : Term :=
      match t with
      | (listDesc) => (dataDesc (labeledArg name : (gnameNamed str "List")) (labeledArg params : ((typed ( str "A" : (univ (lzero)) )))) (labeledArg level : (lzero)) (labeledArg constrs : ((( (constructor) (labeledArg name : str "nil") (labeledArg args : (unit ( ))) (labeledArg boundary : (unit ( ))) )) (constructor (labeledArg name : str "cons") (labeledArg args : ((typed ( str "x" : (const (ix (num (number 0)))) )) (typed ( str "xs" : (recursive) )))) (labeledArg boundary : (unit ( )))))))
      | _ => t

    def circleDesc (t : Term) : Term :=
      match t with
      | (circleDesc) => (dataDesc (labeledArg name : (gnameNamed str "Circle")) (labeledArg params : (unit ( ))) (labeledArg level : (lzero)) (labeledArg constrs : ((( (constructor) (labeledArg name : str "base") (labeledArg args : (unit ( ))) (labeledArg boundary : (unit ( ))) )) (constructor (labeledArg name : str "loop") (labeledArg args : ((typed ( str "i" : (dim) )))) (labeledArg boundary : ((tuple ( (cof_eq (ix (num (number 0))) dim0) , (base) )) (tuple ( (cof_eq (ix (num (number 0))) dim1) , (base) ))))))))
      | _ => t

    def boolDesc (t : Term) : Term :=
      match t with
      | (boolDesc) => (dataDesc (labeledArg name : (gnameNamed str "Bool")) (labeledArg params : (unit ( ))) (labeledArg level : (lzero)) (labeledArg constrs : ((( (constructor) (labeledArg name : str "true") (labeledArg args : (unit ( ))) (labeledArg boundary : (unit ( ))) )) (constructor (labeledArg name : str "false") (labeledArg args : (unit ( ))) (labeledArg boundary : (unit ( )))))))
      | _ => t

    def unitDesc (t : Term) : Term :=
      match t with
      | (unitDesc) => (dataDesc (labeledArg name : (gnameNamed str "Unit")) (labeledArg params : (unit ( ))) (labeledArg level : (lzero)) (labeledArg constrs : ((( (constructor) (labeledArg name : str "tt") (labeledArg args : (unit ( ))) (labeledArg boundary : (unit ( ))) )))))
      | _ => t

  end BuiltinDatatypes

  section StdEnv

    def stdEnv (t : Term) : Term :=
      match t with
      | (stdEnv) => (letIn ( let env0 = (globalEnvEmpty) in (letIn let env1 = (globalEnvDeclareDatatype (env0) (natDesc)) in (letIn let env2 = (globalEnvDeclareDatatype (env1) (listDesc)) in (letIn let env3 = (globalEnvDeclareDatatype (env2) (circleDesc)) in (letIn let env4 = (globalEnvDeclareDatatype (env3) (boolDesc)) in (letIn let env5 = (globalEnvDeclareDatatype (env4) (unitDesc)) in (env5)))))) ))
      | _ => t

  end StdEnv

end Datatype