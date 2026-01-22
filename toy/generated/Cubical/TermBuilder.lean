/-
  AUTO-GENERATED from .lego files
  Do not edit directly.
-/

import Lego.Algebra

open Lego

namespace TermBuilder

  section BuildCtx

    def bctxEmpty (t : Term) : Term :=
      match t with
      | .con "bctxEmpty" [] => Term.con "app" [Term.var "bctx", Term.con "num" [Term.con "number" [Term.lit "0"]]]
      | _ => t

    def bctxLevel (t : Term) : Term :=
      match t with
      | .con "app" [.var "bctxLevel", .con "app" [.var "bctx", l]] => l
      | _ => t

    def bctxNext (t : Term) : Term :=
      match t with
      | .con "app" [.var "bctxNext", .con "app" [.var "bctx", l]] => Term.con "app" [Term.var "bctx", Term.con "app" [Term.var "suc", l]]
      | _ => t

    def bctxFreshVar (t : Term) : Term :=
      match t with
      | .con "app" [.var "bctxFreshVar", .con "app" [.var "bctx", l]] => Term.con "app" [Term.var "ix", l]
      | _ => t

  end BuildCtx

  section BuildM

    def runBuild (t : Term) : Term :=
      match t with
      | .con "app" [.var "runBuild", ma] => Term.con "tuple" [ma, Term.con "bctxEmpty" []]
      | _ => t

    def getCtx (t : Term) : Term :=
      match t with
      | .con "app" [.var "getCtx", ctx] => ctx
      | _ => t

    def getLevel (t : Term) : Term :=
      match t with
      | .con "app" [.var "getLevel", ctx] => Term.con "app" [Term.var "bctxLevel", ctx]
      | _ => t

    def withBinder (t : Term) : Term :=
      match t with
      | .con "withBinder" [k, ctx] => Term.con "tuple" [k, Term.con "app" [Term.var "bctxFreshVar", ctx], Term.con "app" [Term.var "bctxNext", ctx]]
      | _ => t

  end BuildM

  section LamBuilder

    def buildLam (t : Term) : Term :=
      match t with
      | .con "buildLam" [k, ctx] => Term.con "app" [Term.var "lam", Term.con "tuple" [k, Term.con "app" [Term.var "bctxFreshVar", ctx], Term.con "app" [Term.var "bctxNext", ctx]]]
      | _ => t

    -- Test: test
    -- ()

  end LamBuilder

  section PiBuilder

    def buildPi (t : Term) : Term :=
      match t with
      | .con "buildPi" [dom, k, ctx] => Term.con "pi" [Term.con "tuple" [dom, ctx], Term.con "tuple" [k, Term.con "app" [Term.var "bctxFreshVar", ctx], Term.con "app" [Term.var "bctxNext", ctx]]]
      | _ => t

    def buildArrow (t : Term) : Term :=
      match t with
      | .con "buildArrow" [dom, cod, ctx] => Term.con "pi" [Term.con "tuple" [dom, ctx], Term.con "shift" [Term.con "num" [Term.con "number" [Term.lit "0"]], Term.con "num" [Term.con "number" [Term.lit "1"]], Term.con "tuple" [cod, ctx]]]
      | _ => t

  end PiBuilder

  section SigmaBuilder

    def buildSigma (t : Term) : Term :=
      match t with
      | .con "buildSigma" [fst, k, ctx] => Term.con "sigma" [Term.con "tuple" [fst, ctx], Term.con "tuple" [k, Term.con "app" [Term.var "bctxFreshVar", ctx], Term.con "app" [Term.var "bctxNext", ctx]]]
      | _ => t

    def buildProd (t : Term) : Term :=
      match t with
      | .con "buildProd" [A, B, ctx] => Term.con "sigma" [Term.con "tuple" [A, ctx], Term.con "shift" [Term.con "num" [Term.con "number" [Term.lit "0"]], Term.con "num" [Term.con "number" [Term.lit "1"]], Term.con "tuple" [B, ctx]]]
      | _ => t

  end SigmaBuilder

  section PairBuilder

    def buildPair (t : Term) : Term :=
      match t with
      | .con "buildPair" [a, b, ctx] => Term.con "pair" [Term.con "tuple" [a, ctx], Term.con "tuple" [b, ctx]]
      | _ => t

    def buildFst (t : Term) : Term :=
      match t with
      | .con "buildFst" [p, ctx] => Term.con "app" [Term.var "fst", Term.con "tuple" [p, ctx]]
      | _ => t

    def buildSnd (t : Term) : Term :=
      match t with
      | .con "buildSnd" [p, ctx] => Term.con "app" [Term.var "snd", Term.con "tuple" [p, ctx]]
      | _ => t

  end PairBuilder

  section PathBuilder

    def buildPath (t : Term) : Term :=
      match t with
      | .con "buildPath" [tp, l, r, ctx] => Term.con "path" [Term.con "tuple" [tp, ctx], Term.con "tuple" [l, ctx], Term.con "tuple" [r, ctx]]
      | _ => t

    def buildPlam (t : Term) : Term :=
      match t with
      | .con "buildPlam" [k, ctx] => Term.con "app" [Term.var "plam", Term.con "tuple" [k, Term.con "app" [Term.var "bctxFreshVar", ctx], Term.con "app" [Term.var "bctxNext", ctx]]]
      | _ => t

    def buildPapp (t : Term) : Term :=
      match t with
      | .con "buildPapp" [p, dim, ctx] => Term.con "papp" [Term.con "tuple" [p, ctx], dim]
      | _ => t

    def buildRefl (t : Term) : Term :=
      match t with
      | .con "buildRefl" [a, ctx] => Term.con "app" [Term.var "refl", Term.con "tuple" [a, ctx]]
      | _ => t

  end PathBuilder

  section SubBuilder

    def buildSub (t : Term) : Term :=
      match t with
      | .con "buildSub" [tp, φ, k, ctx] => Term.con "sub" [Term.con "tuple" [tp, ctx], Term.con "tuple" [φ, ctx], Term.con "tuple" [k, Term.con "app" [Term.var "bctxFreshVar", ctx], Term.con "app" [Term.var "bctxNext", ctx]]]
      | _ => t

    def buildSubIn (t : Term) : Term :=
      match t with
      | .con "buildSubIn" [e, ctx] => Term.con "app" [Term.var "subIn", Term.con "tuple" [e, ctx]]
      | _ => t

    def buildSubOut (t : Term) : Term :=
      match t with
      | .con "buildSubOut" [e, ctx] => Term.con "app" [Term.var "subOut", Term.con "tuple" [e, ctx]]
      | _ => t

  end SubBuilder

  section CoeBuilder

    def buildCoe (t : Term) : Term :=
      match t with
      | .con "buildCoe" [r, r', line, a, ctx] => Term.con "coe" [r, r', Term.con "app" [Term.var "plam", Term.con "tuple" [line, Term.con "app" [Term.var "bctxFreshVar", ctx], Term.con "app" [Term.var "bctxNext", ctx]]], Term.con "tuple" [a, ctx]]
      | _ => t

    def buildCoeSimple (t : Term) : Term :=
      match t with
      | .con "buildCoeSimple" [r, r', line, a, ctx] => Term.con "coe" [r, r', Term.con "tuple" [line, ctx], Term.con "tuple" [a, ctx]]
      | _ => t

  end CoeBuilder

  section HComBuilder

    def buildHCom (t : Term) : Term :=
      match t with
      | .con "buildHCom" [r, r', A, φ, tube, cap, ctx] => Term.con "hcom" [r, r', Term.con "tuple" [A, ctx], Term.con "tuple" [φ, ctx], Term.con "tuple" [tube, ctx], Term.con "tuple" [cap, ctx]]
      | _ => t

  end HComBuilder

  section ComBuilder

    def buildCom (t : Term) : Term :=
      match t with
      | .con "buildCom" [r, r', line, φ, tube, cap, ctx] => Term.con "com" [r, r', Term.con "app" [Term.var "plam", Term.con "tuple" [line, Term.con "app" [Term.var "bctxFreshVar", ctx], Term.con "app" [Term.var "bctxNext", ctx]]], Term.con "tuple" [φ, ctx], Term.con "tuple" [tube, ctx], Term.con "tuple" [cap, ctx]]
      | _ => t

  end ComBuilder

  section ExtBuilder

    def buildExt (t : Term) : Term :=
      match t with
      | .con "buildExt" [n, fam, cof, bdry, ctx] => Term.con "ext" [n, Term.con "tuple" [fam, ctx], Term.con "tuple" [cof, ctx], Term.con "tuple" [bdry, ctx]]
      | _ => t

    def buildExtLam (t : Term) : Term :=
      match t with
      | .con "buildExtLam" [n, body, ctx] => Term.con "extLam" [n, Term.con "tuple" [body, ctx]]
      | _ => t

    def buildExtApp (t : Term) : Term :=
      match t with
      | .con "buildExtApp" [e, dims, ctx] => Term.con "extApp" [Term.con "tuple" [e, ctx], dims]
      | _ => t

  end ExtBuilder

  section NatBuilder

    def buildNat (t : Term) : Term :=
      match t with
      | .con "app" [.var "buildNat", ctx] => Term.con "nat" []
      | _ => t

    def buildZero (t : Term) : Term :=
      match t with
      | .con "app" [.var "buildZero", ctx] => Term.con "zero" []
      | _ => t

    def buildSuc (t : Term) : Term :=
      match t with
      | .con "buildSuc" [n, ctx] => Term.con "app" [Term.var "suc", Term.con "tuple" [n, ctx]]
      | _ => t

    def buildNatElim (t : Term) : Term :=
      match t with
      | .con "buildNatElim" [P, z, s, n, ctx] => Term.con "natElim" [Term.con "tuple" [P, ctx], Term.con "tuple" [z, ctx], Term.con "tuple" [s, ctx], Term.con "tuple" [n, ctx]]
      | _ => t

  end NatBuilder

  section CircleBuilder

    def buildCircle (t : Term) : Term :=
      match t with
      | .con "app" [.var "buildCircle", ctx] => Term.con "circle" []
      | _ => t

    def buildBase (t : Term) : Term :=
      match t with
      | .con "app" [.var "buildBase", ctx] => Term.con "base" []
      | _ => t

    def buildLoop (t : Term) : Term :=
      match t with
      | .con "buildLoop" [r, ctx] => Term.con "app" [Term.var "loop", r]
      | _ => t

    def buildCircleElim (t : Term) : Term :=
      match t with
      | .con "buildCircleElim" [P, b, l, x, ctx] => Term.con "circleElim" [Term.con "tuple" [P, ctx], Term.con "tuple" [b, ctx], Term.con "tuple" [l, ctx], Term.con "tuple" [x, ctx]]
      | _ => t

  end CircleBuilder

  section UnivBuilder

    def buildUniv (t : Term) : Term :=
      match t with
      | .con "buildUniv" [l, ctx] => Term.con "app" [Term.var "univ", l]
      | _ => t

    def buildType (t : Term) : Term :=
      match t with
      | .con "app" [.var "buildType", ctx] => Term.con "app" [Term.var "univ", Term.con "lzero" []]
      | _ => t

    def buildTypeAt (t : Term) : Term :=
      match t with
      | .con "buildTypeAt" [n, ctx] => Term.con "app" [Term.var "univ", Term.con "app" [Term.var "levelOfNat", n]]
      | _ => t

    def levelOfNat0 (t : Term) : Term :=
      match t with
      | .con "app" [.var "levelOfNat", .con "num" [.con "number" [.lit "0"]]] => Term.con "lzero" []
      | _ => t

    def levelOfNatS (t : Term) : Term :=
      match t with
      | .con "app" [.var "levelOfNat", .con "app" [.var "suc", n]] => Term.con "app" [Term.var "lsuc", Term.con "app" [Term.var "levelOfNat", n]]
      | _ => t

  end UnivBuilder

  section VTypeBuilder

    def buildVType (t : Term) : Term :=
      match t with
      | .con "buildVType" [r, A, B, equiv, ctx] => Term.con "vtype" [r, Term.con "tuple" [A, ctx], Term.con "tuple" [B, ctx], Term.con "tuple" [equiv, ctx]]
      | _ => t

    def buildVIn (t : Term) : Term :=
      match t with
      | .con "buildVIn" [r, a, b, ctx] => Term.con "vin" [r, Term.con "tuple" [a, ctx], Term.con "tuple" [b, ctx]]
      | _ => t

    def buildVProj (t : Term) : Term :=
      match t with
      | .con "buildVProj" [r, A, B, equiv, v, ctx] => Term.con "vproj" [r, Term.con "tuple" [A, ctx], Term.con "tuple" [B, ctx], Term.con "tuple" [equiv, ctx], Term.con "tuple" [v, ctx]]
      | _ => t

  end VTypeBuilder

  section AppBuilder

    def buildApp (t : Term) : Term :=
      match t with
      | .con "buildApp" [f, a, ctx] => Term.con "app" [Term.con "tuple" [f, ctx], Term.con "tuple" [a, ctx]]
      | _ => t

    def buildApps0 (t : Term) : Term :=
      match t with
      | .con "buildApps" [f, .con "unit" [.lit "(", .lit ")"], ctx] => Term.con "tuple" [f, ctx]
      | _ => t

    def buildApps1 (t : Term) : Term :=
      match t with
      | .con "buildApps" [f, .con "tuple" [a, rest], ctx] => Term.con "buildApps" [Term.con "fun" [Term.con "c" [], Term.lit "=>", Term.con "app" [Term.con "tuple" [f, Term.con "c" []], Term.con "tuple" [a, Term.con "c" []]]], rest, ctx]
      | _ => t

  end AppBuilder

  section LetBuilder

    def buildLet (t : Term) : Term :=
      match t with
      | .con "buildLet" [ty, val, k, ctx] => Term.con "letE" [Term.con "tuple" [ty, ctx], Term.con "tuple" [val, ctx], Term.con "tuple" [k, Term.con "app" [Term.var "bctxFreshVar", ctx], Term.con "app" [Term.var "bctxNext", ctx]]]
      | _ => t

  end LetBuilder

end TermBuilder