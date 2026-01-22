(DImport import (modulePath Core) ;)

namespace Signature

  section Label

    def label : Parser :=
      ((annotated str "userLabel" (special <name>) → userLabel) <|> (annotated str "anonLabel" (special <nat>) → anonLabel))

    def labelToString (t : Term) : Term :=
      match t with
      | (labelToString (userLabel $s)) => $s
      | _ => t

    def labelToStringAnon (t : Term) : Term :=
      match t with
      | (labelToString (anonLabel $n)) => (strConcat str "_" (natToString $n))
      | _ => t

    def isAnonLabel (t : Term) : Term :=
      match t with
      | (isAnonLabel (anonLabel $n)) => (true)
      | _ => t

    def isAnonLabelUser (t : Term) : Term :=
      match t with
      | (isAnonLabel (userLabel $s)) => (false)
      | _ => t

    def labelEq (t : Term) : Term :=
      match t with
      | (labelEq (userLabel $s1) (userLabel $s2)) => (eq $s1 $s2)
      | _ => t

    def labelEqAnon (t : Term) : Term :=
      match t with
      | (labelEq (anonLabel $n1) (anonLabel $n2)) => (eq $n1 $n2)
      | _ => t

    def labelEqMix (t : Term) : Term :=
      match t with
      | (labelEq $l1 $l2) => (false)
      | _ => t

  end Label

  section Cell

    def teleCell : Parser :=
      (annotated str "teleCell" str "label:" (special <label>) str "ty:" (special <expr>) → teleCell)

    def cellLabel (t : Term) : Term :=
      match t with
      | (cellLabel (teleCell (labeledArg label : $l) (labeledArg ty : $t))) => $l
      | _ => t

    def cellTy (t : Term) : Term :=
      match t with
      | (cellTy (teleCell (labeledArg label : $l) (labeledArg ty : $t))) => $t
      | _ => t

  end Cell

  section Telescope

    def telescope : Parser :=
      (annotated str "telescope" many ((special <teleCell>)) → telescope)

    def telescopeEmpty (t : Term) : Term :=
      match t with
      | (telescopeEmpty) => (telescope)
      | _ => t

    def telescopeExtend (t : Term) : Term :=
      match t with
      | (telescopeExtend (telescope $cells) $lbl $ty) => (telescope $cells (teleCell (labeledArg label : $lbl) (labeledArg ty : $ty)))
      | _ => t

    def telescopeLength (t : Term) : Term :=
      match t with
      | (telescopeLength (telescope)) => (num (number 0))
      | _ => t

    def telescopeLengthCons (t : Term) : Term :=
      match t with
      | (telescopeLength (telescope $cells $c)) => (succ (telescopeLength (telescope $cells)))
      | _ => t

    def telescopeLabels (t : Term) : Term :=
      match t with
      | (telescopeLabels (telescope)) => (unit ( ))
      | _ => t

    def telescopeLabelsCons (t : Term) : Term :=
      match t with
      | (telescopeLabels (telescope $cells $c)) => ((( (telescopeLabels (telescope $cells)) )) (cellLabel $c))
      | _ => t

    def telescopeFindByLabel (t : Term) : Term :=
      match t with
      | (telescopeFindByLabel (telescope) $lbl) => (none)
      | _ => t

    def telescopeFindByLabelMatch (t : Term) : Term :=
      match t with
      | (telescopeFindByLabel (telescope $cells (teleCell (labeledArg label : $lbl) (labeledArg ty : $t))) $lbl) => (some (tuple ( (telescopeLength (telescope $cells)) , (teleCell (labeledArg label : $lbl) (labeledArg ty : $t)) )))
      | _ => t

    def telescopeFindByLabelMiss (t : Term) : Term :=
      match t with
      | (telescopeFindByLabel (telescope $cells $c) $lbl) => (telescopeFindByLabel (telescope $cells) $lbl)
      | _ => t

    def telescopeTypeAt (t : Term) : Term :=
      match t with
      | (telescopeTypeAt (telescope) $idx) => (none)
      | _ => t

    def telescopeTypeAtHit (t : Term) : Term :=
      match t with
      | (telescopeTypeAt (telescope $cells $c) (num (number 0))) => (some (cellTy $c))
      | _ => t

    def telescopeTypeAtMiss (t : Term) : Term :=
      match t with
      | (telescopeTypeAt (telescope $cells $c) (succ $n)) => (telescopeTypeAt (telescope $cells) $n)
      | _ => t

    def telescopeShiftAll (t : Term) : Term :=
      match t with
      | (telescopeShiftAll $delta (telescope)) => (telescope)
      | _ => t

    def telescopeShiftAllCons (t : Term) : Term :=
      match t with
      | (telescopeShiftAll $delta (telescope $cells $c)) => (telescope (telescopeShiftAll $delta (telescope $cells)) (teleCell (labeledArg label : (cellLabel $c)) (labeledArg ty : (shift (num (number 0)) $delta (cellTy $c)))))
      | _ => t

  end Telescope

  section KCell

    def kCell : Parser :=
      (annotated str "kCell" str "label:" (special <label>) str "code:" (special <expr>) → kCell)

    def kCellLabel (t : Term) : Term :=
      match t with
      | (kCellLabel (kCell (labeledArg label : $l) (labeledArg code : $c))) => $l
      | _ => t

    def kCellCode (t : Term) : Term :=
      match t with
      | (kCellCode (kCell (labeledArg label : $l) (labeledArg code : $c))) => $c
      | _ => t

  end KCell

  section KTelescope

    def kTelescope : Parser :=
      (annotated str "kTelescope" many ((special <kCell>)) → kTelescope)

    def kTelescopeEmpty (t : Term) : Term :=
      match t with
      | (kTelescopeEmpty) => (kTelescope)
      | _ => t

    def kTelescopeExtend (t : Term) : Term :=
      match t with
      | (kTelescopeExtend (kTelescope $cells) $lbl $code) => (kTelescope $cells (kCell (labeledArg label : $lbl) (labeledArg code : $code)))
      | _ => t

    def kTelescopeLength (t : Term) : Term :=
      match t with
      | (kTelescopeLength (kTelescope)) => (num (number 0))
      | _ => t

    def kTelescopeLengthCons (t : Term) : Term :=
      match t with
      | (kTelescopeLength (kTelescope $cells $c)) => (succ (kTelescopeLength (kTelescope $cells)))
      | _ => t

    def kTelescopeToTelescope (t : Term) : Term :=
      match t with
      | (kTelescopeToTelescope (kTelescope)) => (telescope)
      | _ => t

    def kTelescopeToTelescopeCons (t : Term) : Term :=
      match t with
      | (kTelescopeToTelescope (kTelescope $cells $c)) => (telescope (kTelescopeToTelescope (kTelescope $cells)) (teleCell (labeledArg label : (kCellLabel $c)) (labeledArg ty : (kCellCode $c))))
      | _ => t

  end KTelescope

  section SignatureType

    def signatureType : Parser :=
      (annotated str "sigType" (special <telescope>) → sigType)

    def sigTypeEmpty (t : Term) : Term :=
      match t with
      | (sigTypeEmpty) => (sigType (telescopeEmpty))
      | _ => t

    def sigTypeSingle (t : Term) : Term :=
      match t with
      | (sigTypeSingle $lbl $ty) => (sigType (telescopeExtend (telescopeEmpty) $lbl $ty))
      | _ => t

    def sigTypeExtend (t : Term) : Term :=
      match t with
      | (sigTypeExtend (sigType $tele) $lbl $ty) => (sigType (telescopeExtend $tele $lbl $ty))
      | _ => t

    def sigTypeNumFields (t : Term) : Term :=
      match t with
      | (sigTypeNumFields (sigType $tele)) => (telescopeLength $tele)
      | _ => t

    def sigTypeLabels (t : Term) : Term :=
      match t with
      | (sigTypeLabels (sigType $tele)) => (telescopeLabels $tele)
      | _ => t

    def sigTypeFindField (t : Term) : Term :=
      match t with
      | (sigTypeFindField (sigType $tele) $lbl) => (caseExpr ( case (telescopeFindByLabel $tele $lbl) (arm ( some (tuple ( $idx , $cell )) ) => (some $idx)) (arm none => (none)) ))
      | _ => t

    def sigTypeFieldType (t : Term) : Term :=
      match t with
      | (sigTypeFieldType (sigType $tele) $idx) => (telescopeTypeAt $tele $idx)
      | _ => t

    def sigTypeToSigma (t : Term) : Term :=
      match t with
      | (sigTypeToSigma (sigType (telescope))) => (univ (num (number 0)))
      | _ => t

    def sigTypeToSigmaSingle (t : Term) : Term :=
      match t with
      | (sigTypeToSigma (sigType (telescope ($c)))) => (cellTy $c)
      | _ => t

    def sigTypeToSigmaMulti (t : Term) : Term :=
      match t with
      | (sigTypeToSigma (sigType (telescope $cells $c))) => (sigma (cellTy (head $cells)) (sigTypeToSigma (sigType (telescope (tail $cells) $c))))
      | _ => t

    def head (t : Term) : Term :=
      match t with
      | (head ($x $rest)) => $x
      | _ => t

    def tail (t : Term) : Term :=
      match t with
      | (tail ($x $rest)) => $rest
      | _ => t

  end SignatureType

  section Field

    def field : Parser :=
      (annotated str "field" str "label:" (special <label>) str "value:" (special <expr>) → field)

    def fieldLabel (t : Term) : Term :=
      match t with
      | (fieldLabel (field (labeledArg label : $l) (labeledArg value : $v))) => $l
      | _ => t

    def fieldValue (t : Term) : Term :=
      match t with
      | (fieldValue (field (labeledArg label : $l) (labeledArg value : $v))) => $v
      | _ => t

  end Field

  section Struct

    def struct : Parser :=
      (annotated str "struct" many ((special <field>)) → struct)

    def structEmpty (t : Term) : Term :=
      match t with
      | (structEmpty) => (struct)
      | _ => t

    def structSingle (t : Term) : Term :=
      match t with
      | (structSingle $lbl $val) => (struct (field (labeledArg label : $lbl) (labeledArg value : $val)))
      | _ => t

    def structExtend (t : Term) : Term :=
      match t with
      | (structExtend (struct $fields) $lbl $val) => (struct $fields (field (labeledArg label : $lbl) (labeledArg value : $val)))
      | _ => t

    def structNumFields (t : Term) : Term :=
      match t with
      | (structNumFields (struct)) => (num (number 0))
      | _ => t

    def structNumFieldsCons (t : Term) : Term :=
      match t with
      | (structNumFields (struct $fields $f)) => (succ (structNumFields (struct $fields)))
      | _ => t

    def structLabels (t : Term) : Term :=
      match t with
      | (structLabels (struct)) => (unit ( ))
      | _ => t

    def structLabelsCons (t : Term) : Term :=
      match t with
      | (structLabels (struct $fields $f)) => ((( (structLabels (struct $fields)) )) (fieldLabel $f))
      | _ => t

    def structValues (t : Term) : Term :=
      match t with
      | (structValues (struct)) => (unit ( ))
      | _ => t

    def structValuesCons (t : Term) : Term :=
      match t with
      | (structValues (struct $fields $f)) => ((( (structValues (struct $fields)) )) (fieldValue $f))
      | _ => t

    def structFindField (t : Term) : Term :=
      match t with
      | (structFindField (struct) $lbl) => (none)
      | _ => t

    def structFindFieldMatch (t : Term) : Term :=
      match t with
      | (structFindField (struct $fields (field (labeledArg label : $lbl) (labeledArg value : $v))) $lbl) => (some (field (labeledArg label : $lbl) (labeledArg value : $v)))
      | _ => t

    def structFindFieldMiss (t : Term) : Term :=
      match t with
      | (structFindField (struct $fields $f) $lbl) => (structFindField (struct $fields) $lbl)
      | _ => t

    def structGetField (t : Term) : Term :=
      match t with
      | (structGetField $s $lbl) => (caseExpr ( case (structFindField $s $lbl) (arm ( some $f ) => (some (fieldValue $f))) (arm none => (none)) ))
      | _ => t

    def structGetAt (t : Term) : Term :=
      match t with
      | (structGetAt (struct) $idx) => (none)
      | _ => t

    def structGetAtHit (t : Term) : Term :=
      match t with
      | (structGetAt (struct $fields $f) (num (number 0))) => (some (fieldValue $f))
      | _ => t

    def structGetAtMiss (t : Term) : Term :=
      match t with
      | (structGetAt (struct $fields $f) (succ $n)) => (structGetAt (struct $fields) $n)
      | _ => t

    def structToPair (t : Term) : Term :=
      match t with
      | (structToPair (struct)) => (lit str "unit")
      | _ => t

    def structToPairSingle (t : Term) : Term :=
      match t with
      | (structToPair (struct ($f))) => (fieldValue $f)
      | _ => t

    def structToPairMulti (t : Term) : Term :=
      match t with
      | (structToPair (struct $fields $f)) => (pair (fieldValue (head $fields)) (structToPair (struct (tail $fields) $f)))
      | _ => t

    def structFromList (t : Term) : Term :=
      match t with
      | (structFromList (unit ( ))) => (structEmpty)
      | _ => t

    def structFromListCons (t : Term) : Term :=
      match t with
      | (structFromList (( ( $lbl (,) $val ) $rest ))) => (structExtend (structFromList $rest) $lbl $val)
      | _ => t

  end Struct

  section Projection

    def projAt (t : Term) : Term :=
      match t with
      | (projAt $e (num (number 0))) => (fst $e)
      | _ => t

    def projAtSucc (t : Term) : Term :=
      match t with
      | (projAt $e (succ $n)) => (projAt (snd $e) $n)
      | _ => t

    def mkProj (t : Term) : Term :=
      match t with
      | (mkProj $struct $lbl $idx) => (projAt $struct $idx)
      | _ => t

  end Projection

  section Unpack

    def unpack (t : Term) : Term :=
      match t with
      | (unpack $s) => (structValues $s)
      | _ => t

  end Unpack

  section SignatureKan

    def mcoeTele (t : Term) : Term :=
      match t with
      | (mcoeTele $r $r' (kTelescope) $struct) => $struct
      | _ => t

    def mcoeTeleCons (t : Term) : Term :=
      match t with
      | (mcoeTele $r $r' (kTelescope $cells $c) $struct) => (letIn ( let $ coedFirst = (coe $r $r' (kCellCode $c) (structGetAt $struct (num (number 0)))) in (structExtend (mcoeTele $r $r' (kTelescope $cells) (structTail $struct)) (kCellLabel $c) $coedFirst) ))
      | _ => t

    def structTail (t : Term) : Term :=
      match t with
      | (structTail (struct $f $rest)) => (struct $rest)
      | _ => t

    def mcomTele (t : Term) : Term :=
      match t with
      | (mcomTele $r $r' (kTelescope) $φ $tubes $cap) => $cap
      | _ => t

    def mcomTeleCons (t : Term) : Term :=
      match t with
      | (mcomTele $r $r' (kTelescope $cells $c) $φ $tubes $cap) => (letIn ( let $ comFirst = (com (kCellCode $c) $r $r' $φ (lam (lam (structGetAt (app (app (shift (num (number 0)) (num (number 2)) $tubes) (ix (num (number 1)))) (ix (num (number 0)))) (num (number 0))))) (structGetAt $cap (num (number 0)))) in (structExtend (mcomTele $r $r' (kTelescope $cells) $φ (lam (lam (structTail (app (app (shift (num (number 0)) (num (number 2)) $tubes) (ix (num (number 1)))) (ix (num (number 0))))))) (structTail $cap)) (kCellLabel $c) $comFirst) ))
      | _ => t

  end SignatureKan

end Signature