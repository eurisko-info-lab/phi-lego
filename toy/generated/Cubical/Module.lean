(DImport import (modulePath Core) ;)

(DImport import (modulePath GlobalEnv) ;)

(DImport import (modulePath Elaborate) ;)

namespace Module

  section Selector

    def selector : Parser :=
      (annotated str "selector" many ((special <name>)) → selector)

    def selectorToPath (t : Term) : Term :=
      match t with
      | (selectorToPath (selector)) => str ""
      | _ => t

    def selectorToPathCons (t : Term) : Term :=
      match t with
      | (selectorToPath (selector $n $rest)) => (strConcat $n str "." (selectorToPath (selector $rest)))
      | _ => t

    def selectorFromPath (t : Term) : Term :=
      match t with
      | (selectorFromPath $path) => (selector (strSplit $path str "."))
      | _ => t

    def selectorToFilePath (t : Term) : Term :=
      match t with
      | (selectorToFilePath $base (selector $parts) $ext) => (strConcat $base str "/" (strJoin str "/" $parts) $ext)
      | _ => t

  end Selector

  section Visibility

    def visibility : Parser :=
      ((annotated str "pub" → pub) <|> (annotated str "priv" → priv))

    def isPublic (t : Term) : Term :=
      match t with
      | (isPublic (pub)) => (true)
      | _ => t

    def isPublicPriv (t : Term) : Term :=
      match t with
      | (isPublic (priv)) => (false)
      | _ => t

    def visibilityToString (t : Term) : Term :=
      match t with
      | (visibilityToString (pub)) => str "public"
      | _ => t

    def visibilityToStringPriv (t : Term) : Term :=
      match t with
      | (visibilityToString (priv)) => str "private"
      | _ => t

  end Visibility

  section ModDecl

    def modDecl : Parser :=
      ((annotated str "importMod" (special <visibility>) (special <selector>) → importMod) <|> ((annotated str "define" (special <visibility>) (special <name>) str ":" (special <expr>) str ":=" (special <expr>) → define) <|> ((annotated str "dataDecl" (special <visibility>) (special <dataDesc>) → dataDecl) <|> (annotated str "axiomDecl" (special <visibility>) (special <name>) str ":" (special <expr>) → axiomDecl))))

    def modDeclVisibility (t : Term) : Term :=
      match t with
      | (modDeclVisibility (importMod $v $s)) => $v
      | _ => t

    def modDeclVisibilityDef (t : Term) : Term :=
      match t with
      | (modDeclVisibility (define $v (typedVar $ n : $t) (:=) $b)) => $v
      | _ => t

    def modDeclVisibilityData (t : Term) : Term :=
      match t with
      | (modDeclVisibility (dataDecl $v $d)) => $v
      | _ => t

    def modDeclVisibilityAxiom (t : Term) : Term :=
      match t with
      | (modDeclVisibility (axiomDecl $v (typedVar $ n : $t))) => $v
      | _ => t

    def modDeclName (t : Term) : Term :=
      match t with
      | (modDeclName (define $v (typedVar $ n : $t) (:=) $b)) => (some $n)
      | _ => t

    def modDeclNameData (t : Term) : Term :=
      match t with
      | (modDeclName (dataDecl $v $d)) => (some (dataDescName $d))
      | _ => t

    def modDeclNameAxiom (t : Term) : Term :=
      match t with
      | (modDeclName (axiomDecl $v (typedVar $ n : $t))) => (some $n)
      | _ => t

    def modDeclNameImport (t : Term) : Term :=
      match t with
      | (modDeclName (importMod $v $s)) => (none)
      | _ => t

  end ModDecl

  section ModuleStruct

    def module : Parser :=
      (annotated str "module" (special <selector>) str "{" many ((special <modDecl>)) str "}" → module)

    def moduleName (t : Term) : Term :=
      match t with
      | (moduleName (module $sel (brace { $decls }))) => $sel
      | _ => t

    def moduleDecls (t : Term) : Term :=
      match t with
      | (moduleDecls (module $sel (brace { $decls }))) => $decls
      | _ => t

  end ModuleStruct

  section Resolution

    def resolution : Parser :=
      ((annotated str "localIx" (special <nat>) → localIx) <|> (annotated str "globalRes" (special <gname>) → globalRes))

    def isLocalResolution (t : Term) : Term :=
      match t with
      | (isLocalResolution (localIx $n)) => (true)
      | _ => t

    def isLocalResolutionGlobal (t : Term) : Term :=
      match t with
      | (isLocalResolution (globalRes $g)) => (false)
      | _ => t

    def isGlobalResolution (t : Term) : Term :=
      match t with
      | (isGlobalResolution (globalRes $g)) => (true)
      | _ => t

    def isGlobalResolutionLocal (t : Term) : Term :=
      match t with
      | (isGlobalResolution (localIx $n)) => (false)
      | _ => t

    def resolutionIndex (t : Term) : Term :=
      match t with
      | (resolutionIndex (localIx $n)) => $n
      | _ => t

    def resolutionGName (t : Term) : Term :=
      match t with
      | (resolutionGName (globalRes $g)) => $g
      | _ => t

  end Resolution

  section ImportInfo

    def importInfo : Parser :=
      (annotated str "importInfo" str "name:" (special <gname>) str "vis:" (special <visibility>) str "from:" (special <selector>) → importInfo)

    def importInfoName (t : Term) : Term :=
      match t with
      | (importInfoName (importInfo (labeledArg name : $n) (labeledArg vis : $v) (labeledArg from : $s))) => $n
      | _ => t

    def importInfoVis (t : Term) : Term :=
      match t with
      | (importInfoVis (importInfo (labeledArg name : $n) (labeledArg vis : $v) (labeledArg from : $s))) => $v
      | _ => t

    def importInfoFrom (t : Term) : Term :=
      match t with
      | (importInfoFrom (importInfo (labeledArg name : $n) (labeledArg vis : $v) (labeledArg from : $s))) => $s
      | _ => t

  end ImportInfo

  section ResEnv

    def resEnv : Parser :=
      (annotated str "resEnv" str "locals:" many ((special <name>)) str "globals:" many ((special <importEntry>)) str "natives:" many ((special <gname>)) → resEnv)

    def importEntry : Parser :=
      (annotated str "[" (special <name>) str "↦" (special <importInfo>) str "]" → importEntry)

    def resEnvEmpty (t : Term) : Term :=
      match t with
      | (resEnvEmpty) => (resEnv (labeledArg locals : (unit ( ))) (labeledArg globals : (unit ( ))) (labeledArg natives : (unit ( ))))
      | _ => t

    def resEnvBind (t : Term) : Term :=
      match t with
      | (resEnvBind $x (resEnv (labeledArg locals : $ls) (labeledArg globals : $gs) (labeledArg natives : $ns))) => (resEnv (labeledArg locals : ($x $ls)) (labeledArg globals : $gs) (labeledArg natives : $ns))
      | _ => t

    def resEnvBindN (t : Term) : Term :=
      match t with
      | (resEnvBindN (unit ( )) $env) => $env
      | _ => t

    def resEnvBindNCons (t : Term) : Term :=
      match t with
      | (resEnvBindN ($x $xs) $env) => (resEnvBindN $xs (resEnvBind $x $env))
      | _ => t

    def resEnvGet (t : Term) : Term :=
      match t with
      | (resEnvGet $x (resEnv (labeledArg locals : $ls) (labeledArg globals : $gs) (labeledArg natives : $ns))) => (resEnvLookup $x $ls $gs (num (number 0)))
      | _ => t

    def resEnvLookup (t : Term) : Term :=
      match t with
      | (resEnvLookup $x (unit ( )) $gs $idx) => (resEnvLookupGlobal $x $gs)
      | _ => t

    def resEnvLookupMatch (t : Term) : Term :=
      match t with
      | (resEnvLookup $x ($x $rest) $gs $idx) => (some (localIx $idx))
      | _ => t

    def resEnvLookupMiss (t : Term) : Term :=
      match t with
      | (resEnvLookup $x ($y $rest) $gs $idx) => (resEnvLookup $x $rest $gs (succ $idx))
      | _ => t

    def resEnvLookupGlobal (t : Term) : Term :=
      match t with
      | (resEnvLookupGlobal $x (unit ( ))) => (none)
      | _ => t

    def resEnvLookupGlobalMatch (t : Term) : Term :=
      match t with
      | (resEnvLookupGlobal $x (( ( [ $x (↦) $info ] ) $rest ))) => (some (globalRes (importInfoName $info)))
      | _ => t

    def resEnvLookupGlobalMiss (t : Term) : Term :=
      match t with
      | (resEnvLookupGlobal $x (( ( $entry ) $rest ))) => (resEnvLookupGlobal $x $rest)
      | _ => t

    def resEnvAddNative (t : Term) : Term :=
      match t with
      | (resEnvAddNative $vis $gname (resEnv (labeledArg locals : $ls) (labeledArg globals : $gs) (labeledArg natives : $ns))) => (resEnv (labeledArg locals : $ls) (labeledArg globals : ((( (bracket [ (gnameName $gname) (↦) (importInfo (labeledArg name : $gname) (labeledArg vis : $vis) (labeledArg from : (selector))) ]) )) $gs)) (labeledArg natives : ($gname $ns)))
      | _ => t

    def resEnvImportGlobal (t : Term) : Term :=
      match t with
      | (resEnvImportGlobal $vis $gname $fromMod (resEnv (labeledArg locals : $ls) (labeledArg globals : $gs) (labeledArg natives : $ns))) => (resEnv (labeledArg locals : $ls) (labeledArg globals : ((( (bracket [ (gnameName $gname) (↦) (importInfo (labeledArg name : $gname) (labeledArg vis : $vis) (labeledArg from : $fromMod)) ]) )) $gs)) (labeledArg natives : $ns))
      | _ => t

    def resEnvExports (t : Term) : Term :=
      match t with
      | (resEnvExports (resEnv (labeledArg locals : $ls) (labeledArg globals : $gs) (labeledArg natives : $ns))) => (resEnvCollectExports $gs (unit ( )))
      | _ => t

    def resEnvCollectExports (t : Term) : Term :=
      match t with
      | (resEnvCollectExports (unit ( )) $acc) => $acc
      | _ => t

    def resEnvCollectExportsPub (t : Term) : Term :=
      match t with
      | (resEnvCollectExports (( ( [ $n (↦) (importInfo (labeledArg name : $g) (labeledArg vis : (pub)) (labeledArg from : $f)) ] ) $rest )) $acc) => (resEnvCollectExports $rest ($g $acc))
      | _ => t

    def resEnvCollectExportsPriv (t : Term) : Term :=
      match t with
      | (resEnvCollectExports (( ( [ $n (↦) (importInfo (labeledArg name : $g) (labeledArg vis : (priv)) (labeledArg from : $f)) ] ) $rest )) $acc) => (resEnvCollectExports $rest $acc)
      | _ => t

  end ResEnv

  section ModuleCache

    def moduleCache : Parser :=
      (annotated str "moduleCache" str "loaded:" many ((special <cacheEntry>)) str "loading:" many ((special <selector>)) → moduleCache)

    def cacheEntry : Parser :=
      (annotated str "[" (special <selector>) str "↦" (special <resEnv>) str "," (special <globalEnv>) str "]" → cacheEntry)

    def moduleCacheEmpty (t : Term) : Term :=
      match t with
      | (moduleCacheEmpty) => (moduleCache (labeledArg loaded : (unit ( ))) (labeledArg loading : (unit ( ))))
      | _ => t

    def moduleCacheIsLoaded (t : Term) : Term :=
      match t with
      | (moduleCacheIsLoaded $sel (moduleCache (labeledArg loaded : $ls) (labeledArg loading : $ing))) => (cacheContains $sel $ls)
      | _ => t

    def cacheContains (t : Term) : Term :=
      match t with
      | (cacheContains $sel (unit ( ))) => (false)
      | _ => t

    def cacheContainsMatch (t : Term) : Term :=
      match t with
      | (cacheContains $sel (( ( [ $sel (↦) $r (,) $e ] ) $rest ))) => (true)
      | _ => t

    def cacheContainsMiss (t : Term) : Term :=
      match t with
      | (cacheContains $sel (( ( $entry ) $rest ))) => (cacheContains $sel $rest)
      | _ => t

    def moduleCacheIsCyclic (t : Term) : Term :=
      match t with
      | (moduleCacheIsCyclic $sel (moduleCache (labeledArg loaded : $ls) (labeledArg loading : $ing))) => (listContains $sel $ing)
      | _ => t

    def moduleCacheStartLoading (t : Term) : Term :=
      match t with
      | (moduleCacheStartLoading $sel (moduleCache (labeledArg loaded : $ls) (labeledArg loading : $ing))) => (moduleCache (labeledArg loaded : $ls) (labeledArg loading : ($sel $ing)))
      | _ => t

    def moduleCacheStore (t : Term) : Term :=
      match t with
      | (moduleCacheStore $sel $res $env (moduleCache (labeledArg loaded : $ls) (labeledArg loading : $ing))) => (moduleCache (labeledArg loaded : ((( (bracket [ $sel (↦) $res (,) $env ]) )) $ls)) (labeledArg loading : (listRemove $sel $ing)))
      | _ => t

    def moduleCacheGetModule (t : Term) : Term :=
      match t with
      | (moduleCacheGetModule $sel (moduleCache (labeledArg loaded : $ls) (labeledArg loading : $ing))) => (cacheLookup $sel $ls)
      | _ => t

    def cacheLookup (t : Term) : Term :=
      match t with
      | (cacheLookup $sel (unit ( ))) => (none)
      | _ => t

    def cacheLookupMatch (t : Term) : Term :=
      match t with
      | (cacheLookup $sel (( ( [ $sel (↦) $r (,) $e ] ) $rest ))) => (some (tuple ( $r , $e )))
      | _ => t

    def cacheLookupMiss (t : Term) : Term :=
      match t with
      | (cacheLookup $sel (( ( $entry ) $rest ))) => (cacheLookup $sel $rest)
      | _ => t

  end ModuleCache

  section ProcessDecl

    def processImport (t : Term) : Term :=
      match t with
      | (processDecl (importMod $vis $sel) $resEnv $globEnv $loadImport) => (letIn ( let $ importedRes = (apply $loadImport $sel) in (tuple ( $resEnv , $globEnv )) ))
      | _ => t

    def processDefine (t : Term) : Term :=
      match t with
      | (processDecl (define $vis (typedVar $ name : $ty) (:=) $tm) $resEnv $globEnv $loadImport) => (letIn ( let $ gname = (gname $name) in (letIn ( let $ globEnv' = (globalEnvDefine $gname $ty $tm $globEnv) in (letIn ( let $ resEnv' = (resEnvAddNative $vis $gname $resEnv) in (tuple ( $resEnv' , $globEnv' )) )) )) ))
      | _ => t

    def processDataDecl (t : Term) : Term :=
      match t with
      | (processDecl (dataDecl $vis $desc) $resEnv $globEnv $loadImport) => (letIn ( let $ globEnv' = (globalEnvDeclareDatatype $desc $globEnv) in (letIn ( let $ resEnv' = (resEnvAddNative $vis (dataDescName $desc) $resEnv) in (tuple ( $resEnv' , $globEnv' )) )) ))
      | _ => t

    def processAxiom (t : Term) : Term :=
      match t with
      | (processDecl (axiomDecl $vis (typedVar $ name : $ty)) $resEnv $globEnv $loadImport) => (letIn ( let $ gname = (gname $name) in (letIn ( let $ globEnv' = (globalEnvDeclareParam $gname $ty $globEnv) in (letIn ( let $ resEnv' = (resEnvAddNative $vis $gname $resEnv) in (tuple ( $resEnv' , $globEnv' )) )) )) ))
      | _ => t

  end ProcessDecl

  section QualifiedName

    def resolveQualified (t : Term) : Term :=
      match t with
      | (resolveQualified ($name) $env $cache) => (resEnvGet $name $env)
      | _ => t

    def resolveQualifiedMulti (t : Term) : Term :=
      match t with
      | (resolveQualified ($modPart $rest) $env $cache) => (caseExpr ( case (moduleCacheGetModule (selector ($modPart $rest)) $cache) (arm ( some (tuple ( $res , $genv )) ) => (resEnvGet (last ($modPart $rest)) $res)) (arm none => (none)) ))
      | _ => t

    def last (t : Term) : Term :=
      match t with
      | (last ($x)) => $x
      | _ => t

    def lastCons (t : Term) : Term :=
      match t with
      | (last ($x $y $rest)) => (last ($y $rest))
      | _ => t

  end QualifiedName

end Module