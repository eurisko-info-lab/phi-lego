(DImport import (modulePath Core) ;)

namespace Visitor

  section VisitorState

    def vstate : Parser :=
      (annotated str "vstate" (special <number>) → vstate)

    def vstateEmpty (t : Term) : Term :=
      match t with
      | (vstateEmpty) => (vstate (num (number 0)))
      | _ => t

    def vstateDepth (t : Term) : Term :=
      match t with
      | (vstateDepth (vstate $d)) => $d
      | _ => t

    def vstateIncr (t : Term) : Term :=
      match t with
      | (vstateIncr (vstate $d)) => (vstate (suc $d))
      | _ => t

  end VisitorState

  section BinderInfo

    def binfo : Parser :=
      ((annotated str "binfoNone" → binfoNone) <|> ((annotated str "binfoTerm" (special <number>) → binfoTerm) <|> (annotated str "binfoDim" (special <number>) → binfoDim)))

  end BinderInfo

  section Child

    def child : Parser :=
      (annotated str "child" term binfo → child)

    def childExpr (t : Term) : Term :=
      match t with
      | (childExpr (child $e $bi)) => $e
      | _ => t

    def childBinder (t : Term) : Term :=
      match t with
      | (childBinder (child $e $bi)) => $bi
      | _ => t

  end Child

  section ExprShape

    def shape : Parser :=
      (annotated str "shape" children (special <ident>) → shape)

    def children : Parser :=
      (annotated many (child) → children)

  end ExprShape

  section Shape

    def shapeIx (t : Term) : Term :=
      match t with
      | (exprShape (ix $n)) => (shape (unit ( )) str "ix")
      | _ => t

    def shapeLit (t : Term) : Term :=
      match t with
      | (exprShape (lit $s)) => (shape (unit ( )) str "lit")
      | _ => t

    def shapeDim0 (t : Term) : Term :=
      match t with
      | (exprShape (dim0)) => (shape (unit ( )) str "dim0")
      | _ => t

    def shapeDim1 (t : Term) : Term :=
      match t with
      | (exprShape (dim1)) => (shape (unit ( )) str "dim1")
      | _ => t

    def shapeDimVar (t : Term) : Term :=
      match t with
      | (exprShape (dimVar $n)) => (shape (unit ( )) str "dimVar")
      | _ => t

    def shapeCofTop (t : Term) : Term :=
      match t with
      | (exprShape (cof_top)) => (shape (unit ( )) str "cof_top")
      | _ => t

    def shapeCofBot (t : Term) : Term :=
      match t with
      | (exprShape (cof_bot)) => (shape (unit ( )) str "cof_bot")
      | _ => t

    def shapeNat (t : Term) : Term :=
      match t with
      | (exprShape (nat)) => (shape (unit ( )) str "nat")
      | _ => t

    def shapeZero (t : Term) : Term :=
      match t with
      | (exprShape (zero)) => (shape (unit ( )) str "zero")
      | _ => t

    def shapeCircle (t : Term) : Term :=
      match t with
      | (exprShape (circle)) => (shape (unit ( )) str "circle")
      | _ => t

    def shapeBase (t : Term) : Term :=
      match t with
      | (exprShape (base)) => (shape (unit ( )) str "base")
      | _ => t

    def shapeUniv (t : Term) : Term :=
      match t with
      | (exprShape (univ $l)) => (shape (unit ( )) str "univ")
      | _ => t

    def shapeFst (t : Term) : Term :=
      match t with
      | (exprShape (fst $e)) => (shape ((( (child) $e (binfoNone) ))) str "fst")
      | _ => t

    def shapeSnd (t : Term) : Term :=
      match t with
      | (exprShape (snd $e)) => (shape ((( (child) $e (binfoNone) ))) str "snd")
      | _ => t

    def shapeSuc (t : Term) : Term :=
      match t with
      | (exprShape (suc $e)) => (shape ((( (child) $e (binfoNone) ))) str "suc")
      | _ => t

    def shapeRefl (t : Term) : Term :=
      match t with
      | (exprShape (refl $e)) => (shape ((( (child) $e (binfoNone) ))) str "refl")
      | _ => t

    def shapeLoop (t : Term) : Term :=
      match t with
      | (exprShape (loop $r)) => (shape ((( (child) $r (binfoNone) ))) str "loop")
      | _ => t

    def shapeSubIn (t : Term) : Term :=
      match t with
      | (exprShape (subIn $e)) => (shape ((( (child) $e (binfoNone) ))) str "subIn")
      | _ => t

    def shapeSubOut (t : Term) : Term :=
      match t with
      | (exprShape (subOut $e)) => (shape ((( (child) $e (binfoNone) ))) str "subOut")
      | _ => t

    def shapeLam (t : Term) : Term :=
      match t with
      | (exprShape (lam $body)) => (shape ((( (child) $body (binfoTerm (num (number 1))) ))) str "lam")
      | _ => t

    def shapePlam (t : Term) : Term :=
      match t with
      | (exprShape (plam $body)) => (shape ((( (child) $body (binfoDim (num (number 1))) ))) str "plam")
      | _ => t

    def shapeApp (t : Term) : Term :=
      match t with
      | (exprShape (app $f $a)) => (shape ((( (child) $f (binfoNone) )) (child $a (binfoNone))) str "app")
      | _ => t

    def shapePair (t : Term) : Term :=
      match t with
      | (exprShape (pair $a $b)) => (shape ((( (child) $a (binfoNone) )) (child $b (binfoNone))) str "pair")
      | _ => t

    def shapePapp (t : Term) : Term :=
      match t with
      | (exprShape (papp $p $r)) => (shape ((( (child) $p (binfoNone) )) (child $r (binfoNone))) str "papp")
      | _ => t

    def shapeCofEq (t : Term) : Term :=
      match t with
      | (exprShape (cof_eq $r $s)) => (shape ((( (child) $r (binfoNone) )) (child $s (binfoNone))) str "cof_eq")
      | _ => t

    def shapeCofAnd (t : Term) : Term :=
      match t with
      | (exprShape (cof_and $φ $ψ)) => (shape ((( (child) $φ (binfoNone) )) (child $ψ (binfoNone))) str "cof_and")
      | _ => t

    def shapeCofOr (t : Term) : Term :=
      match t with
      | (exprShape (cof_or $φ $ψ)) => (shape ((( (child) $φ (binfoNone) )) (child $ψ (binfoNone))) str "cof_or")
      | _ => t

    def shapePi (t : Term) : Term :=
      match t with
      | (exprShape (pi $dom $cod)) => (shape ((( (child) $dom (binfoNone) )) (child $cod (binfoTerm (num (number 1))))) str "pi")
      | _ => t

    def shapeSigma (t : Term) : Term :=
      match t with
      | (exprShape (sigma $dom $cod)) => (shape ((( (child) $dom (binfoNone) )) (child $cod (binfoTerm (num (number 1))))) str "sigma")
      | _ => t

    def shapePath (t : Term) : Term :=
      match t with
      | (exprShape (path $A $a $b)) => (shape ((( (child) $A (binfoNone) )) (child $a (binfoNone)) (child $b (binfoNone))) str "path")
      | _ => t

    def shapeSub (t : Term) : Term :=
      match t with
      | (exprShape (sub $A $φ $t)) => (shape ((( (child) $A (binfoNone) )) (child $φ (binfoNone)) (child $t (binfoNone))) str "sub")
      | _ => t

    def shapeLetE (t : Term) : Term :=
      match t with
      | (exprShape (letE $ty $val $body)) => (shape ((( (child) $ty (binfoNone) )) (child $val (binfoNone)) (child $body (binfoTerm (num (number 1))))) str "letE")
      | _ => t

    def shapeCoe (t : Term) : Term :=
      match t with
      | (exprShape (coe $r $r' $A $a)) => (shape ((( (child) $r (binfoNone) )) (child $r' (binfoNone)) (child $A (binfoDim (num (number 1)))) (child $a (binfoNone))) str "coe")
      | _ => t

    def shapeNatElim (t : Term) : Term :=
      match t with
      | (exprShape (natElim $P $z $s $n)) => (shape ((( (child) $P (binfoNone) )) (child $z (binfoNone)) (child $s (binfoTerm (num (number 2)))) (child $n (binfoNone))) str "natElim")
      | _ => t

    def shapeCircleElim (t : Term) : Term :=
      match t with
      | (exprShape (circleElim $P $b $l $x)) => (shape ((( (child) $P (binfoNone) )) (child $b (binfoNone)) (child $l (binfoDim (num (number 1)))) (child $x (binfoNone))) str "circleElim")
      | _ => t

  end Shape

  section Reconstruct

    def reconstructIx (t : Term) : Term :=
      match t with
      | (reconstruct str "ix" (unit ( )) $orig) => $orig
      | _ => t

    def reconstructLit (t : Term) : Term :=
      match t with
      | (reconstruct str "lit" (unit ( )) $orig) => $orig
      | _ => t

    def reconstructLam (t : Term) : Term :=
      match t with
      | (reconstruct str "lam" ($body) (lam $oldBody)) => (lam $body)
      | _ => t

    def reconstructApp (t : Term) : Term :=
      match t with
      | (reconstruct str "app" ($f $a) (app $oldF $oldA)) => (app $f $a)
      | _ => t

    def reconstructPi (t : Term) : Term :=
      match t with
      | (reconstruct str "pi" ($dom $cod) (pi $oldDom $oldCod)) => (pi $dom $cod)
      | _ => t

    def reconstructSigma (t : Term) : Term :=
      match t with
      | (reconstruct str "sigma" ($dom $cod) (sigma $oldDom $oldCod)) => (sigma $dom $cod)
      | _ => t

    def reconstructPair (t : Term) : Term :=
      match t with
      | (reconstruct str "pair" ($a $b) (pair $oldA $oldB)) => (pair $a $b)
      | _ => t

    def reconstructFst (t : Term) : Term :=
      match t with
      | (reconstruct str "fst" ($e) (fst $oldE)) => (fst $e)
      | _ => t

    def reconstructSnd (t : Term) : Term :=
      match t with
      | (reconstruct str "snd" ($e) (snd $oldE)) => (snd $e)
      | _ => t

    def reconstructPlam (t : Term) : Term :=
      match t with
      | (reconstruct str "plam" ($body) (plam $oldBody)) => (plam $body)
      | _ => t

    def reconstructPapp (t : Term) : Term :=
      match t with
      | (reconstruct str "papp" ($p $r) (papp $oldP $oldR)) => (papp $p $r)
      | _ => t

    def reconstructPath (t : Term) : Term :=
      match t with
      | (reconstruct str "path" ($A $a $b) (path $oldA $oldA' $oldB)) => (path $A $a $b)
      | _ => t

    def reconstructRefl (t : Term) : Term :=
      match t with
      | (reconstruct str "refl" ($a) (refl $oldA)) => (refl $a)
      | _ => t

    def reconstructCofEq (t : Term) : Term :=
      match t with
      | (reconstruct str "cof_eq" ($r $s) (cof_eq $oldR $oldS)) => (cof_eq $r $s)
      | _ => t

    def reconstructCofAnd (t : Term) : Term :=
      match t with
      | (reconstruct str "cof_and" ($φ $ψ) (cof_and $oldPhi $oldPsi)) => (cof_and $φ $ψ)
      | _ => t

    def reconstructCofOr (t : Term) : Term :=
      match t with
      | (reconstruct str "cof_or" ($φ $ψ) (cof_or $oldPhi $oldPsi)) => (cof_or $φ $ψ)
      | _ => t

    def reconstructCoe (t : Term) : Term :=
      match t with
      | (reconstruct str "coe" ($r $r' $A $a) (coe $oldR $oldR' $oldA $oldA')) => (coe $r $r' $A $a)
      | _ => t

    def reconstructSuc (t : Term) : Term :=
      match t with
      | (reconstruct str "suc" ($n) (suc $oldN)) => (suc $n)
      | _ => t

    def reconstructNatElim (t : Term) : Term :=
      match t with
      | (reconstruct str "natElim" ($P $z $s $n) (natElim $oldP $oldZ $oldS $oldN)) => (natElim $P $z $s $n)
      | _ => t

    def reconstructLoop (t : Term) : Term :=
      match t with
      | (reconstruct str "loop" ($r) (loop $oldR)) => (loop $r)
      | _ => t

    def reconstructCircleElim (t : Term) : Term :=
      match t with
      | (reconstruct str "circleElim" ($P $b $l $x) (circleElim $oldP $oldB $oldL $oldX)) => (circleElim $P $b $l $x)
      | _ => t

    def reconstructSub (t : Term) : Term :=
      match t with
      | (reconstruct str "sub" ($A $φ $t) (sub $oldA $oldPhi $oldT)) => (sub $A $φ $t)
      | _ => t

    def reconstructSubIn (t : Term) : Term :=
      match t with
      | (reconstruct str "subIn" ($e) (subIn $oldE)) => (subIn $e)
      | _ => t

    def reconstructSubOut (t : Term) : Term :=
      match t with
      | (reconstruct str "subOut" ($e) (subOut $oldE)) => (subOut $e)
      | _ => t

    def reconstructLetE (t : Term) : Term :=
      match t with
      | (reconstruct str "letE" ($ty $val $body) (letE $oldTy $oldVal $oldBody)) => (letE $ty $val $body)
      | _ => t

  end Reconstruct

  section FreeVars

    def freeVarsIx (t : Term) : Term :=
      match t with
      | (freeVars' $depth (ix $n)) => (if (geq $n $depth) (cons $n (nil)) (nil))
      | _ => t

    def freeVarsLit (t : Term) : Term :=
      match t with
      | (freeVars' $depth (lit $s)) => (nil)
      | _ => t

    def freeVarsLam (t : Term) : Term :=
      match t with
      | (freeVars' $depth (lam $body)) => (freeVars' (suc $depth) $body)
      | _ => t

    def freeVarsApp (t : Term) : Term :=
      match t with
      | (freeVars' $depth (app $f $a)) => (append (freeVars' $depth $f) (freeVars' $depth $a))
      | _ => t

    def freeVarsPi (t : Term) : Term :=
      match t with
      | (freeVars' $depth (pi $dom $cod)) => (append (freeVars' $depth $dom) (freeVars' (suc $depth) $cod))
      | _ => t

    def freeVarsSigma (t : Term) : Term :=
      match t with
      | (freeVars' $depth (sigma $dom $cod)) => (append (freeVars' $depth $dom) (freeVars' (suc $depth) $cod))
      | _ => t

    def freeVarsPair (t : Term) : Term :=
      match t with
      | (freeVars' $depth (pair $a $b)) => (append (freeVars' $depth $a) (freeVars' $depth $b))
      | _ => t

    def freeVarsFst (t : Term) : Term :=
      match t with
      | (freeVars' $depth (fst $e)) => (freeVars' $depth $e)
      | _ => t

    def freeVarsSnd (t : Term) : Term :=
      match t with
      | (freeVars' $depth (snd $e)) => (freeVars' $depth $e)
      | _ => t

    def freeVarsPlam (t : Term) : Term :=
      match t with
      | (freeVars' $depth (plam $body)) => (freeVars' $depth $body)
      | _ => t

    def freeVarsPapp (t : Term) : Term :=
      match t with
      | (freeVars' $depth (papp $p $r)) => (freeVars' $depth $p)
      | _ => t

    def freeVarsUniv (t : Term) : Term :=
      match t with
      | (freeVars' $depth (univ $l)) => (nil)
      | _ => t

    def freeVarsPath (t : Term) : Term :=
      match t with
      | (freeVars' $depth (path $A $a $b)) => (append (freeVars' $depth $A) (append (freeVars' $depth $a) (freeVars' $depth $b)))
      | _ => t

    def freeVars (t : Term) : Term :=
      match t with
      | (freeVars $e) => (freeVars' (num (number 0)) $e)
      | _ => t

  end FreeVars

  section FreeIn

    def freeIn (t : Term) : Term :=
      match t with
      | (freeIn $n $e) => (elem $n (freeVars $e))
      | _ => t

  end FreeIn

  section WHNF

    def whnfAppLam (t : Term) : Term :=
      match t with
      | (whnfStep (app (lam $body) $arg)) => (some (subst (num (number 0)) $arg $body))
      | _ => t

    def whnfAppOther (t : Term) : Term :=
      match t with
      | (whnfStep (app $f $a)) => (none)
      | _ => t

    def whnfFstPair (t : Term) : Term :=
      match t with
      | (whnfStep (fst (pair $a $b))) => (some $a)
      | _ => t

    def whnfSndPair (t : Term) : Term :=
      match t with
      | (whnfStep (snd (pair $a $b))) => (some $b)
      | _ => t

    def whnfFstOther (t : Term) : Term :=
      match t with
      | (whnfStep (fst $p)) => (none)
      | _ => t

    def whnfSndOther (t : Term) : Term :=
      match t with
      | (whnfStep (snd $p)) => (none)
      | _ => t

    def whnfPappPlam (t : Term) : Term :=
      match t with
      | (whnfStep (papp (plam $body) $r)) => (some (substDim (num (number 0)) $r $body))
      | _ => t

    def whnfPappRefl (t : Term) : Term :=
      match t with
      | (whnfStep (papp (refl $a) $r)) => (some $a)
      | _ => t

    def whnfPappOther (t : Term) : Term :=
      match t with
      | (whnfStep (papp $p $r)) => (none)
      | _ => t

    def whnfLet (t : Term) : Term :=
      match t with
      | (whnfStep (letE $ty $val $body)) => (some (subst (num (number 0)) $val $body))
      | _ => t

    def whnfStepDefault (t : Term) : Term :=
      match t with
      | (whnfStep $e) => (none)
      | _ => t

    def whnf' (t : Term) : Term :=
      match t with
      | (whnf' $fuel $e) => (whnfLoop $fuel $e)
      | _ => t

    def whnf'Zero (t : Term) : Term :=
      match t with
      | (whnf' (num (number 0)) $e) => $e
      | _ => t

    def whnfLoop (t : Term) : Term :=
      match t with
      | (whnfLoop $fuel $e) => (match (whnfStep $e) (with) (|) (some $e') (=>) (whnf' (sub $fuel (num (number 1))) $e') (|) (none) (=>) $e)
      | _ => t

  end WHNF

  section TryBetaReduce

    def tryBetaApp (t : Term) : Term :=
      match t with
      | (tryBetaReduce (app (lam $body) $arg)) => (some (subst (num (number 0)) $arg $body))
      | _ => t

    def tryBetaFst (t : Term) : Term :=
      match t with
      | (tryBetaReduce (fst (pair $a $b))) => (some $a)
      | _ => t

    def tryBetaSnd (t : Term) : Term :=
      match t with
      | (tryBetaReduce (snd (pair $a $b))) => (some $b)
      | _ => t

    def tryBetaPapp (t : Term) : Term :=
      match t with
      | (tryBetaReduce (papp (plam $body) $r)) => (some (substDim (num (number 0)) $r $body))
      | _ => t

    def tryBetaRefl (t : Term) : Term :=
      match t with
      | (tryBetaReduce (papp (refl $a) $r)) => (some $a)
      | _ => t

    def tryBetaNone (t : Term) : Term :=
      match t with
      | (tryBetaReduce $e) => (none)
      | _ => t

  end TryBetaReduce

end Visitor