(DImport import (modulePath Core) ;)

namespace GlobalEnv

  section GName

    def gname : Parser :=
      (annotated str "gname" (special <string>) str "source:" optional ((special <string>)) → gname)

    def gnameNamed (t : Term) : Term :=
      match t with
      | (gnameNamed $s) => (gname $s (labeledArg source : (none)))
      | _ => t

    def gnameFresh (t : Term) : Term :=
      match t with
      | (gnameFresh $base $counter) => (gname (concat $base str "_" $counter) (labeledArg source : (none)))
      | _ => t

    def gnameAnonymous (t : Term) : Term :=
      match t with
      | (gnameAnonymous) => (gname str "_" (labeledArg source : (none)))
      | _ => t

    def gnameName (t : Term) : Term :=
      match t with
      | (gnameName (gname $n (labeledArg source : $s))) => $n
      | _ => t

    def gnameSource (t : Term) : Term :=
      match t with
      | (gnameSource (gname $n (labeledArg source : $s))) => $s
      | _ => t

    def gnameEq (t : Term) : Term :=
      match t with
      | (gnameEq (gname $n1 (labeledArg source : $s1)) (gname $n2 (labeledArg source : $s2))) => (eq $n1 $n2)
      | _ => t

  end GName

  section GArgSpec

    def argConst : Parser :=
      (annotated str "const" (special <expr>) → gArgSpec)

    def argRecursive : Parser :=
      (annotated str "recursive" → gArgSpec)

    def argDim : Parser :=
      (annotated str "dim" → gArgSpec)

  end GArgSpec

  section GConstructor

    def gconstructor : Parser :=
      (annotated str "constructor" str "name:" (special <string>) str "args:" many ((special <constructorArg>)) str "boundary:" many ((special <boundary>)) → gconstructor)

    def constructorArg : Parser :=
      (annotated str "(" (special <string>) str ":" (special <gArgSpec>) str ")" → constructorArg)

    def boundary : Parser :=
      (annotated str "[" (special <expr>) str "↦" (special <expr>) str "]" → boundary)

    def gconstructorName (t : Term) : Term :=
      match t with
      | (gconstructorName (constructor (labeledArg name : $n) (labeledArg args : $a) (labeledArg boundary : $b))) => $n
      | _ => t

    def gconstructorArgs (t : Term) : Term :=
      match t with
      | (gconstructorArgs (constructor (labeledArg name : $n) (labeledArg args : $a) (labeledArg boundary : $b))) => $a
      | _ => t

    def gconstructorBoundary (t : Term) : Term :=
      match t with
      | (gconstructorBoundary (constructor (labeledArg name : $n) (labeledArg args : $a) (labeledArg boundary : $b))) => $b
      | _ => t

  end GConstructor

  section GDataDesc

    def gdataDesc : Parser :=
      (annotated str "dataDesc" str "name:" (special <gname>) str "params:" many ((special <param>)) str "level:" (special <level>) str "constrs:" many ((special <gconstructor>)) → gdataDesc)

    def param : Parser :=
      (annotated str "(" (special <string>) str ":" (special <expr>) str ")" → param)

    def gdataDescName (t : Term) : Term :=
      match t with
      | (gdataDescName (dataDesc (labeledArg name : $n) (labeledArg params : $p) (labeledArg level : $l) (labeledArg constrs : $c))) => $n
      | _ => t

    def gdataDescParams (t : Term) : Term :=
      match t with
      | (gdataDescParams (dataDesc (labeledArg name : $n) (labeledArg params : $p) (labeledArg level : $l) (labeledArg constrs : $c))) => $p
      | _ => t

    def gdataDescLevel (t : Term) : Term :=
      match t with
      | (gdataDescLevel (dataDesc (labeledArg name : $n) (labeledArg params : $p) (labeledArg level : $l) (labeledArg constrs : $c))) => $l
      | _ => t

    def gdataDescConstrs (t : Term) : Term :=
      match t with
      | (gdataDescConstrs (dataDesc (labeledArg name : $n) (labeledArg params : $p) (labeledArg level : $l) (labeledArg constrs : $c))) => $c
      | _ => t

  end GDataDesc

  section GEntry

    def gEntryParam : Parser :=
      (annotated str "param" (special <expr>) → gEntry)

    def gEntryDefn : Parser :=
      (annotated str "defn" str "type:" (special <expr>) str "value:" (special <expr>) → gEntry)

    def gEntryDatatype : Parser :=
      (annotated str "datatype" (special <gdataDesc>) → gEntry)

    def gEntryDimVar : Parser :=
      (annotated str "dimVar" → gEntry)

    def gEntryMetaVar : Parser :=
      (annotated str "metaVar" str "type:" (special <expr>) str "solution:" optional ((special <expr>)) → gEntry)

    def gEntryGetType (t : Term) : Term :=
      match t with
      | (gEntryGetType (param $ty)) => (some $ty)
      | _ => t

    def gEntryGetTypeDefn (t : Term) : Term :=
      match t with
      | (gEntryGetType (defn (labeledArg type : $ty) (labeledArg value : $v))) => (some $ty)
      | _ => t

    def gEntryGetTypeDatatype (t : Term) : Term :=
      match t with
      | (gEntryGetType (datatype $desc)) => (some (univ (gdataDescLevel $desc)))
      | _ => t

    def gEntryGetTypeDimVar (t : Term) : Term :=
      match t with
      | (gEntryGetType (dimVar)) => (some (lit str "𝕀"))
      | _ => t

    def gEntryGetTypeMeta (t : Term) : Term :=
      match t with
      | (gEntryGetType (metaVar (labeledArg type : $ty) (labeledArg solution : $sol))) => (some $ty)
      | _ => t

  end GEntry

  section GlobalEnv

    def globalEnv : Parser :=
      (annotated str "globalEnv" str "entries:" many ((special <envEntry>)) str "order:" many ((special <gname>)) → globalEnv)

    def envEntry : Parser :=
      (annotated str "(" (special <gname>) str "↦" (special <gEntry>) str ")" → envEntry)

    def globalEnvEmpty (t : Term) : Term :=
      match t with
      | (globalEnvEmpty) => (globalEnv (labeledArg entries : (unit ( ))) (labeledArg order : (unit ( ))))
      | _ => t

    def globalEnvExtend (t : Term) : Term :=
      match t with
      | (globalEnvExtend (globalEnv (labeledArg entries : $entries) (labeledArg order : $order)) $nm $entry) => (globalEnv (labeledArg entries : ($entries ((( $nm (↦) $entry ))))) (labeledArg order : ($nm $order)))
      | _ => t

    def globalEnvDefine (t : Term) : Term :=
      match t with
      | (globalEnvDefine $env $nm $ty $tm) => (globalEnvExtend $env $nm (defn (labeledArg type : $ty) (labeledArg value : $tm)))
      | _ => t

    def globalEnvDeclareParam (t : Term) : Term :=
      match t with
      | (globalEnvDeclareParam $env $nm $ty) => (globalEnvExtend $env $nm (param $ty))
      | _ => t

    def globalEnvDeclareDim (t : Term) : Term :=
      match t with
      | (globalEnvDeclareDim $env $nm) => (globalEnvExtend $env $nm (dimVar))
      | _ => t

    def globalEnvDeclareDatatype (t : Term) : Term :=
      match t with
      | (globalEnvDeclareDatatype $env $desc) => (globalEnvExtend $env (gdataDescName $desc) (datatype $desc))
      | _ => t

    def globalEnvCreateMeta (t : Term) : Term :=
      match t with
      | (globalEnvCreateMeta $env $nm $ty) => (globalEnvExtend $env $nm (metaVar (labeledArg type : $ty) (labeledArg solution : (none))))
      | _ => t

    def globalEnvSolveMeta (t : Term) : Term :=
      match t with
      | (globalEnvSolveMeta (globalEnv (labeledArg entries : $entries) (labeledArg order : $order)) $nm $solution) => (globalEnv (labeledArg entries : (solveMeta' $entries $nm $solution)) (labeledArg order : $order))
      | _ => t

    def solveMeta'Nil (t : Term) : Term :=
      match t with
      | (solveMeta' (unit ( )) $nm $sol) => (unit ( ))
      | _ => t

    def solveMeta'Match (t : Term) : Term :=
      match t with
      | (solveMeta' (( ( ( $nm (↦) (metaVar (labeledArg type : $ty) (labeledArg solution : $old)) ) ) $rest )) $nm $sol) => ((( ($nm (↦) (metaVar (labeledArg type : $ty) (labeledArg solution : (some $sol)))) )) $rest)
      | _ => t

    def solveMeta'Miss (t : Term) : Term :=
      match t with
      | (solveMeta' (( ( $entry ) $rest )) $nm $sol) => ((( $entry )) (solveMeta' $rest $nm $sol))
      | _ => t

  end GlobalEnv

  section Lookup

    def globalEnvLookup (t : Term) : Term :=
      match t with
      | (globalEnvLookup (globalEnv (labeledArg entries : $entries) (labeledArg order : $order)) $nm) => (lookupEntry $entries $nm)
      | _ => t

    def lookupEntryNil (t : Term) : Term :=
      match t with
      | (lookupEntry (unit ( )) $nm) => (none)
      | _ => t

    def lookupEntryMatch (t : Term) : Term :=
      match t with
      | (lookupEntry (( ( ( $nm (↦) $entry ) ) $rest )) $nm) => (some $entry)
      | _ => t

    def lookupEntryMiss (t : Term) : Term :=
      match t with
      | (lookupEntry (( ( ( $nm' (↦) $entry ) ) $rest )) $nm) => (lookupEntry $rest $nm)
      | _ => t

    def globalEnvLookupType (t : Term) : Term :=
      match t with
      | (globalEnvLookupType $env $nm) => (caseExpr ( case (globalEnvLookup $env $nm) (arm ( some $entry ) => (gEntryGetType $entry)) (arm none => (none)) ))
      | _ => t

    def globalEnvLookupValue (t : Term) : Term :=
      match t with
      | (globalEnvLookupValue (globalEnv (labeledArg entries : $entries) (labeledArg order : $order)) $nm) => (caseExpr ( case (lookupEntry $entries $nm) (arm ( some (defn (labeledArg type : $ty) (labeledArg value : $v)) ) => (some $v)) (arm _ => (none)) ))
      | _ => t

    def globalEnvLookupDatatype (t : Term) : Term :=
      match t with
      | (globalEnvLookupDatatype (globalEnv (labeledArg entries : $entries) (labeledArg order : $order)) $nm) => (caseExpr ( case (lookupEntry $entries $nm) (arm ( some (datatype $desc) ) => (some $desc)) (arm _ => (none)) ))
      | _ => t

    def globalEnvLookupMeta (t : Term) : Term :=
      match t with
      | (globalEnvLookupMeta (globalEnv (labeledArg entries : $entries) (labeledArg order : $order)) $nm) => (caseExpr ( case (lookupEntry $entries $nm) (arm ( some (metaVar (labeledArg type : $ty) (labeledArg solution : $sol)) ) => (some (record ( type : $ty (labeledArg solution : $sol) )))) (arm _ => (none)) ))
      | _ => t

  end Lookup

  section Query

    def globalEnvIsDefined (t : Term) : Term :=
      match t with
      | (globalEnvIsDefined $env $nm) => (caseExpr ( case (globalEnvLookup $env $nm) (arm ( some (_) ) => (true)) (arm none => (false)) ))
      | _ => t

    def globalEnvIsMetaSolved (t : Term) : Term :=
      match t with
      | (globalEnvIsMetaSolved $env $nm) => (caseExpr ( case (globalEnvLookupMeta $env $nm) (arm ( some (type (:) $ty (labeledArg solution : (some $sol))) ) => (true)) (arm _ => (false)) ))
      | _ => t

    def globalEnvAllNames (t : Term) : Term :=
      match t with
      | (globalEnvAllNames (globalEnv (labeledArg entries : $entries) (labeledArg order : $order))) => $order
      | _ => t

    def globalEnvFilterByKind (t : Term) : Term :=
      match t with
      | (globalEnvFilterByKind (globalEnv (labeledArg entries : $entries) (labeledArg order : $order)) $kind) => (filter (fun (nm) (=>) (matchKind (lookupEntry $entries (nm)) $kind)) $order)
      | _ => t

    def matchKindDefn (t : Term) : Term :=
      match t with
      | (matchKind (some (defn (labeledArg type : $t) (labeledArg value : $v))) (defn)) => (true)
      | _ => t

    def matchKindParam (t : Term) : Term :=
      match t with
      | (matchKind (some (param $t)) (param)) => (true)
      | _ => t

    def matchKindDatatype (t : Term) : Term :=
      match t with
      | (matchKind (some (datatype $d)) (datatype)) => (true)
      | _ => t

    def matchKindDimVar (t : Term) : Term :=
      match t with
      | (matchKind (some (dimVar)) (dimVar)) => (true)
      | _ => t

    def matchKindMetaVar (t : Term) : Term :=
      match t with
      | (matchKind (some (metaVar (labeledArg type : $t) (labeledArg solution : $s))) (metaVar)) => (true)
      | _ => t

    def matchKindOther (t : Term) : Term :=
      match t with
      | (matchKind $entry $kind) => (false)
      | _ => t

  end Query

  section Unfold

    def unfoldOne (t : Term) : Term :=
      match t with
      | (unfoldOne $env (lit $name)) => (caseExpr ( case (globalEnvLookupValue $env (gnameNamed $name)) (arm ( some $val ) => $val) (arm none => (lit $name)) ))
      | _ => t

    def unfoldOneOther (t : Term) : Term :=
      match t with
      | (unfoldOne $env $e) => $e
      | _ => t

    def unfoldAll (t : Term) : Term :=
      match t with
      | (unfoldAll $env $e) => (unfoldAll' $env $e (num (number 100)))
      | _ => t

    def unfoldAll'0 (t : Term) : Term :=
      match t with
      | (unfoldAll' $env $e (num (number 0))) => $e
      | _ => t

    def unfoldAll' (t : Term) : Term :=
      match t with
      | (unfoldAll' $env $e (suc $fuel)) => (letIn ( let e' = (unfoldStep $env $e) in (caseExpr case (eq (e') $e) (arm true => (e')) (arm false => (unfoldAll' $env (e') $fuel))) ))
      | _ => t

    def unfoldStepLit (t : Term) : Term :=
      match t with
      | (unfoldStep $env (lit $name)) => (caseExpr ( case (globalEnvLookupValue $env (gnameNamed $name)) (arm ( some $val ) => $val) (arm none => (lit $name)) ))
      | _ => t

    def unfoldStepApp (t : Term) : Term :=
      match t with
      | (unfoldStep $env (app $f $a)) => (app (unfoldStep $env $f) (unfoldStep $env $a))
      | _ => t

    def unfoldStepLam (t : Term) : Term :=
      match t with
      | (unfoldStep $env (lam $body)) => (lam (unfoldStep $env $body))
      | _ => t

    def unfoldStepPi (t : Term) : Term :=
      match t with
      | (unfoldStep $env (pi $dom $cod)) => (pi (unfoldStep $env $dom) (unfoldStep $env $cod))
      | _ => t

    def unfoldStepOther (t : Term) : Term :=
      match t with
      | (unfoldStep $env $e) => $e
      | _ => t

  end Unfold

  section Print

    def globalEnvPrint (t : Term) : Term :=
      match t with
      | (globalEnvPrint (globalEnv (labeledArg entries : $entries) (labeledArg order : $order))) => (mapReverse (fun (nm) (=>) (printEntry (nm (lookupEntry $entries (nm))))) $order)
      | _ => t

    def printEntry (t : Term) : Term :=
      match t with
      | (printEntry $nm (some (defn (labeledArg type : $ty) (labeledArg value : $v)))) => (concat str "def " (gnameName $nm) str " : " (show $ty) str " := " (show $v))
      | _ => t

    def printEntryParam (t : Term) : Term :=
      match t with
      | (printEntry $nm (some (param $ty))) => (concat str "param " (gnameName $nm) str " : " (show $ty))
      | _ => t

    def printEntryDatatype (t : Term) : Term :=
      match t with
      | (printEntry $nm (some (datatype $desc))) => (concat str "data " (gnameName $nm) str " ...")
      | _ => t

    def printEntryDimVar (t : Term) : Term :=
      match t with
      | (printEntry $nm (some (dimVar))) => (concat str "dim " (gnameName $nm))
      | _ => t

    def printEntryMetaVar (t : Term) : Term :=
      match t with
      | (printEntry $nm (some (metaVar (labeledArg type : $ty) (labeledArg solution : $sol)))) => (concat str "meta " (gnameName $nm) str " : " (show $ty))
      | _ => t

    def printEntryNone (t : Term) : Term :=
      match t with
      | (printEntry $nm (none)) => (concat str "unknown " (gnameName $nm))
      | _ => t

  end Print

end GlobalEnv