/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/

import Scott2026.LambdaModels.DomainTheory.InternalEvalFamily
import Scott2026.LambdaModels.DomainTheory.InternalEvalComplete.InternalReflexiveModel.evalAtGraph
import Scott2026.LambdaModels.DomainTheory.InternalEvalComplete.InternalReflexiveModel.pointwiseSupGraph
import Scott2026.LambdaModels.DomainTheory.InternalEvalComplete.degreePairSetoid
import Scott2026.LambdaModels.DomainTheory.InternalEvalComplete.graphImageB
import Scott2026.LambdaModels.DomainTheory.InternalEvalComplete.interpDKAbsFamilyGraph
import Scott2026.LambdaModels.DomainTheory.InternalEvalComplete.zeroPairGraph
import Scott2026.LambdaModels.DomainTheory.InternalEvalComplete.Proofs.Core
import Scott2026.LambdaModels.DomainTheory.InternalEvalComplete.Proofs.CoreCont
import Scott2026.LambdaModels.DomainTheory.InternalEvalComplete.Proofs.CoreContCont
import Scott2026.LambdaModels.DomainTheory.InternalEval.Proofs.CoreCont

namespace Scott2026

universe u


open AName InternalReflexiveModel

variable {A : Type u} [CompleteBooleanAlgebra A]

/-- A generalized element transports its coefficients along target equality. -/
theorem interpDKBodyGraph_app_apply_mono
    (𝓜 : InternalReflexiveModel (A := A))
    (V K : AName.{u} A) (hK : subsetB K 𝓜.D = ⊤)
    (hV : (oid V).IsTotal)
    (η : RelFun (oid V) (oid 𝓜.D))
    (x : V.idx) (P Q : LamDK V.idx K.idx) (a : A)
    (hPsc : a ≤ isScottContinuousB
      (interpDKBodyGraph 𝓜 V K hK hV η x P) 𝓜.D 𝓜.D 𝓜.R 𝓜.R)
    (hQsc : a ≤ isScottContinuousB
      (interpDKBodyGraph 𝓜 V K hK hV η x Q) 𝓜.D 𝓜.D 𝓜.R 𝓜.R)
    (u u' v v' : AName.{u} A) :
    a ⊓ memB (opairB u v)
        (interpDKBodyGraph 𝓜 V K hK hV η x (.app P Q)) ⊓
      memB (opairB u' v')
        (interpDKBodyGraph 𝓜 V K hK hV η x (.app P Q)) ⊓
      relB 𝓜.R u u' ≤
    relB 𝓜.R v v' := by
  let Fapp := interpDKBodyGraph 𝓜 V K hK hV η x (.app P Q)
  let t0 :=
    a ⊓ memB (opairB u v) Fapp ⊓ memB (opairB u' v') Fapp ⊓
      relB 𝓜.R u u'
  change t0 ≤ relB 𝓜.R v v'
  have ht0A : t0 ≤ a :=
    inf_le_left.trans (inf_le_left.trans inf_le_left)
  have ht0uv : t0 ≤ memB (opairB u v) Fapp :=
    inf_le_left.trans (inf_le_left.trans inf_le_right)
  have ht0u'v' : t0 ≤ memB (opairB u' v') Fapp :=
    inf_le_left.trans inf_le_right
  have hdec :
      t0 ≤ ⨆ p : AName A, ⨆ q : AName A, ⨆ c : AName A,
        memB (opairB u p)
          (interpDKBodyGraph 𝓜 V K hK hV η x P) ⊓
        memB (opairB u q)
          (interpDKBodyGraph 𝓜 V K hK hV η x Q) ⊓
        memB (opairB p c) 𝓜.Fun ⊓
        memB c 𝓜.C ⊓
        memB (opairB q v) c :=
    (interpDKBodyGraph_app_mem_decompose
        𝓜 V K hK hV η x P Q a u v).trans' <|
      le_inf ht0A ht0uv
  refine (le_inf le_rfl hdec).trans ?_
  rw [inf_iSup_eq]
  refine iSup_le fun p => ?_
  rw [inf_iSup_eq]
  refine iSup_le fun q => ?_
  rw [inf_iSup_eq]
  refine iSup_le fun c => ?_
  let t1 :=
    t0 ⊓
      (memB (opairB u p)
          (interpDKBodyGraph 𝓜 V K hK hV η x P) ⊓
        memB (opairB u q)
          (interpDKBodyGraph 𝓜 V K hK hV η x Q) ⊓
        memB (opairB p c) 𝓜.Fun ⊓
        memB c 𝓜.C ⊓
        memB (opairB q v) c)
  have hdec' :
      t1 ≤ ⨆ p' : AName A, ⨆ q' : AName A, ⨆ c' : AName A,
        memB (opairB u' p')
          (interpDKBodyGraph 𝓜 V K hK hV η x P) ⊓
        memB (opairB u' q')
          (interpDKBodyGraph 𝓜 V K hK hV η x Q) ⊓
        memB (opairB p' c') 𝓜.Fun ⊓
        memB c' 𝓜.C ⊓
        memB (opairB q' v') c' :=
    (interpDKBodyGraph_app_mem_decompose
        𝓜 V K hK hV η x P Q a u' v').trans' <|
      le_inf (inf_le_left.trans ht0A) (inf_le_left.trans ht0u'v')
  refine (le_inf le_rfl hdec').trans ?_
  rw [inf_iSup_eq]
  refine iSup_le fun p' => ?_
  rw [inf_iSup_eq]
  refine iSup_le fun q' => ?_
  rw [inf_iSup_eq]
  refine iSup_le fun c' => ?_
  let t2 :=
    t1 ⊓
      (memB (opairB u' p')
          (interpDKBodyGraph 𝓜 V K hK hV η x P) ⊓
        memB (opairB u' q')
          (interpDKBodyGraph 𝓜 V K hK hV η x Q) ⊓
        memB (opairB p' c') 𝓜.Fun ⊓
        memB c' 𝓜.C ⊓
        memB (opairB q' v') c')
  change t2 ≤ relB 𝓜.R v v'
  have ht2t0 : t2 ≤ t0 :=
    inf_le_left.trans inf_le_left
  have ht1φ : t2 ≤
      memB (opairB u p)
          (interpDKBodyGraph 𝓜 V K hK hV η x P) ⊓
        memB (opairB u q)
          (interpDKBodyGraph 𝓜 V K hK hV η x Q) ⊓
        memB (opairB p c) 𝓜.Fun ⊓
        memB c 𝓜.C ⊓
        memB (opairB q v) c :=
    inf_le_left.trans inf_le_right
  have ht2ψ : t2 ≤
      memB (opairB u' p')
          (interpDKBodyGraph 𝓜 V K hK hV η x P) ⊓
        memB (opairB u' q')
          (interpDKBodyGraph 𝓜 V K hK hV η x Q) ⊓
        memB (opairB p' c') 𝓜.Fun ⊓
        memB c' 𝓜.C ⊓
        memB (opairB q' v') c' :=
    inf_le_right
  exact (interpDKBodyGraph_app_bi_mono
      𝓜 V K hK hV η x P Q a hPsc hQsc
      u u' u u' p p' q q' c c' v v').trans' <|
    le_inf (le_inf (le_inf (le_inf
        (ht2t0.trans ht0A)
        (le_inf (le_inf
            (ht1φ.trans (inf_le_left.trans
              (inf_le_left.trans (inf_le_left.trans inf_le_left))))
            (ht2ψ.trans (inf_le_left.trans
              (inf_le_left.trans (inf_le_left.trans inf_le_left)))))
          (ht2t0.trans inf_le_right)))
        (le_inf (le_inf
            (ht1φ.trans (inf_le_left.trans
              (inf_le_left.trans (inf_le_left.trans inf_le_right))))
            (ht2ψ.trans (inf_le_left.trans
              (inf_le_left.trans (inf_le_left.trans inf_le_right)))))
          (ht2t0.trans inf_le_right)))
      (le_inf
        (ht1φ.trans (inf_le_left.trans
          (inf_le_left.trans inf_le_right)))
        (ht2ψ.trans (inf_le_left.trans
          (inf_le_left.trans inf_le_right)))))
      (le_inf
        (ht1φ.trans inf_le_right)
        (ht2ψ.trans inf_le_right))

/-- Directed-supremum preservation for the application body graph. -/
theorem interpDKBodyGraph_app_mapsToSup
    (𝓜 : InternalReflexiveModel (A := A))
    (V K : AName.{u} A) (hK : subsetB K 𝓜.D = ⊤)
    (hV : (oid V).IsTotal)
    (η : RelFun (oid V) (oid 𝓜.D))
    (x : V.idx) (P Q : LamDK V.idx K.idx) (a : A)
    (hfun : a ≤ isFunctionB
      (interpDKBodyGraph 𝓜 V K hK hV η x (.app P Q)) 𝓜.D 𝓜.D)
    (hPsc : a ≤ isScottContinuousB
      (interpDKBodyGraph 𝓜 V K hK hV η x P) 𝓜.D 𝓜.D 𝓜.R 𝓜.R)
    (hQsc : a ≤ isScottContinuousB
      (interpDKBodyGraph 𝓜 V K hK hV η x Q) 𝓜.D 𝓜.D 𝓜.R 𝓜.R)
    (S u v : AName.{u} A) :
    a ⊓ isDirectedRelB S 𝓜.D 𝓜.R ⊓ isSupRelB u S 𝓜.R ⊓
        memB (opairB u v)
          (interpDKBodyGraph 𝓜 V K hK hV η x (.app P Q)) ≤
      mapsToSupB
        (interpDKBodyGraph 𝓜 V K hK hV η x (.app P Q))
        S v 𝓜.R := by
  let FP := interpDKBodyGraph 𝓜 V K hK hV η x P
  let FQ := interpDKBodyGraph 𝓜 V K hK hV η x Q
  let Fapp := interpDKBodyGraph 𝓜 V K hK hV η x (.app P Q)
  have hfunApp : a ≤ isFunctionB Fapp 𝓜.D 𝓜.D := hfun
  unfold mapsToSupB
  refine le_inf ?_ ?_
  · refine le_iInf fun w => le_iInf fun z => ?_
    rw [le_himp_iff]
    let t :=
      (a ⊓ isDirectedRelB S 𝓜.D 𝓜.R ⊓ isSupRelB u S 𝓜.R ⊓
        memB (opairB u v) Fapp) ⊓
      (memB w S ⊓ memB (opairB w z) Fapp)
    change t ≤ relB 𝓜.R z v
    have htA : t ≤ a :=
      inf_le_left.trans (inf_le_left.trans
        (inf_le_left.trans inf_le_left))
    have htu : t ≤ isSupRelB u S 𝓜.R :=
      inf_le_left.trans (inf_le_left.trans inf_le_right)
    have htuv : t ≤ memB (opairB u v) Fapp :=
      inf_le_left.trans inf_le_right
    have htwS : t ≤ memB w S :=
      inf_le_right.trans inf_le_left
    have htwz : t ≤ memB (opairB w z) Fapp :=
      inf_le_right.trans inf_le_right
    have hwu : t ≤ relB 𝓜.R w u :=
      (isUpperBoundRelB_apply u S 𝓜.R w).trans' <|
        le_inf (htu.trans inf_le_left) htwS
    exact (interpDKBodyGraph_app_apply_mono
        𝓜 V K hK hV η x P Q a hPsc hQsc w u z v).trans' <|
      le_inf (le_inf (le_inf htA htwz) htuv) hwu
  · refine le_iInf fun b => ?_
    rw [le_himp_iff]
    let upper :=
      ⨅ w : AName A, ⨅ z : AName A,
        memB w S ⊓ memB (opairB w z) Fapp ⇨ relB 𝓜.R z b
    let t :=
      (a ⊓ isDirectedRelB S 𝓜.D 𝓜.R ⊓ isSupRelB u S 𝓜.R ⊓
        memB (opairB u v) Fapp) ⊓ upper
    change t ≤ relB 𝓜.R v b
    have htA : t ≤ a :=
      inf_le_left.trans (inf_le_left.trans
        (inf_le_left.trans inf_le_left))
    have htDir : t ≤ isDirectedRelB S 𝓜.D 𝓜.R :=
      inf_le_left.trans (inf_le_left.trans
        (inf_le_left.trans inf_le_right))
    have htSup : t ≤ isSupRelB u S 𝓜.R :=
      inf_le_left.trans (inf_le_left.trans inf_le_right)
    have htuv : t ≤ memB (opairB u v) Fapp :=
      inf_le_left.trans inf_le_right
    have htUpper : t ≤ upper := inf_le_right
    have hdec :
        t ≤ ⨆ p : AName A, ⨆ q : AName A, ⨆ c : AName A,
          memB (opairB u p) FP ⊓
          memB (opairB u q) FQ ⊓
          memB (opairB p c) 𝓜.Fun ⊓
          memB c 𝓜.C ⊓
          memB (opairB q v) c :=
      (interpDKBodyGraph_app_mem_decompose
          𝓜 V K hK hV η x P Q a u v).trans' <|
        le_inf htA htuv
    refine (le_inf le_rfl hdec).trans ?_
    rw [inf_iSup_eq]
    refine iSup_le fun p => ?_
    rw [inf_iSup_eq]
    refine iSup_le fun q => ?_
    rw [inf_iSup_eq]
    refine iSup_le fun c => ?_
    let s :=
      t ⊓
        (memB (opairB u p) FP ⊓
          memB (opairB u q) FQ ⊓
          memB (opairB p c) 𝓜.Fun ⊓
          memB c 𝓜.C ⊓
          memB (opairB q v) c)
    change s ≤ relB 𝓜.R v b
    have hsT : s ≤ t := inf_le_left
    have hsφ : s ≤
        memB (opairB u p) FP ⊓
          memB (opairB u q) FQ ⊓
          memB (opairB p c) 𝓜.Fun ⊓
          memB c 𝓜.C ⊓
          memB (opairB q v) c :=
      inf_le_right
    have hsup : s ≤
        memB (opairB u p) FP :=
      hsφ.trans (inf_le_left.trans
        (inf_le_left.trans (inf_le_left.trans inf_le_left)))
    have hsuq : s ≤ memB (opairB u q) FQ :=
      hsφ.trans (inf_le_left.trans
        (inf_le_left.trans (inf_le_left.trans inf_le_right)))
    have hspc : s ≤ memB (opairB p c) 𝓜.Fun :=
      hsφ.trans (inf_le_left.trans
        (inf_le_left.trans inf_le_right))
    have hscC : s ≤ memB c 𝓜.C :=
      hsφ.trans (inf_le_left.trans inf_le_right)
    have hsqv : s ≤ memB (opairB q v) c :=
      hsφ.trans inf_le_right
    have hPimg :
        s ≤ isDirectedRelB (graphImageB FP S 𝓜.D) 𝓜.D 𝓜.R ⊓
          isSupRelB p (graphImageB FP S 𝓜.D) 𝓜.R :=
      (scottContinuous_image_sup (hF := hsT.trans htA |>.trans hPsc)
          FP S 𝓜.D 𝓜.D 𝓜.R 𝓜.R u p).trans' <|
        le_inf (le_inf (le_inf le_rfl (hsT.trans htDir))
          (hsT.trans htSup)) hsup
    have hFunsc : (⊤ : A) ≤
        isScottContinuousB 𝓜.Fun 𝓜.D 𝓜.C 𝓜.R 𝓜.Q :=
      le_top.trans 𝓜.fun_continuous.ge
    have hFunimg :
        s ≤ isDirectedRelB
            (graphImageB 𝓜.Fun (graphImageB FP S 𝓜.D) 𝓜.C)
            𝓜.C 𝓜.Q ⊓
          isSupRelB c
            (graphImageB 𝓜.Fun (graphImageB FP S 𝓜.D) 𝓜.C)
            𝓜.Q :=
      (scottContinuous_image_sup (hF := hFunsc)
          𝓜.Fun (graphImageB FP S 𝓜.D) 𝓜.D 𝓜.C 𝓜.R 𝓜.Q
          p c).trans' <|
        le_inf (le_inf (le_inf (le_top.trans le_top)
            (hPimg.trans inf_le_left))
          (hPimg.trans inf_le_right)) hspc
    have hQimg :
        s ≤ isDirectedRelB (graphImageB FQ S 𝓜.D) 𝓜.D 𝓜.R ⊓
          isSupRelB q (graphImageB FQ S 𝓜.D) 𝓜.R :=
      (scottContinuous_image_sup (hF := hsT.trans htA |>.trans hQsc)
          FQ S 𝓜.D 𝓜.D 𝓜.R 𝓜.R u q).trans' <|
        le_inf (le_inf (le_inf le_rfl (hsT.trans htDir))
          (hsT.trans htSup)) hsuq
    have hqD : s ≤ memB q 𝓜.D :=
      (local_function_edge_le_domain
          ((𝓜.mem_mapSpace_le_function c).trans' hscC) q v).trans' <|
        le_inf le_rfl hsqv
    have hvD : s ≤ memB v 𝓜.D :=
      (local_function_edge_le_codomain
          ((𝓜.mem_mapSpace_le_function c).trans' hscC) q v).trans' <|
        le_inf le_rfl hsqv
    have hvsup : s ≤
        isSupRelB v
          (graphImageB (𝓜.evalAtGraph q)
            (graphImageB 𝓜.Fun (graphImageB FP S 𝓜.D) 𝓜.C)
            𝓜.D)
          𝓜.R :=
      (𝓜.eval_preserves_Q_sup
          (graphImageB 𝓜.Fun (graphImageB FP S 𝓜.D) 𝓜.C)
          c q v).trans' <|
        le_inf (le_inf (le_inf (le_inf (le_inf
            (hFunimg.trans inf_le_left) hscC)
          (hFunimg.trans inf_le_right))
          hqD) hvD) hsqv
    have hupperb : s ≤ isUpperBoundRelB b
        (graphImageB (𝓜.evalAtGraph q)
          (graphImageB 𝓜.Fun (graphImageB FP S 𝓜.D) 𝓜.C)
          𝓜.D)
        𝓜.R := by
      refine le_iInf fun y => ?_
      rw [le_himp_iff, memB_graphImageB, ← inf_assoc, inf_iSup_eq]
      refine iSup_le fun F => ?_
      let sy :=
        (s ⊓ memB y 𝓜.D) ⊓
          (memB F
              (graphImageB 𝓜.Fun (graphImageB FP S 𝓜.D) 𝓜.C) ⊓
            memB (opairB F y) (𝓜.evalAtGraph q))
      change sy ≤ relB 𝓜.R y b
      have hsyS : sy ≤ s := inf_le_left.trans inf_le_left
      have hyD : sy ≤ memB y 𝓜.D := inf_le_left.trans inf_le_right
      have hFimg : sy ≤
          memB F (graphImageB 𝓜.Fun (graphImageB FP S 𝓜.D) 𝓜.C) :=
        inf_le_right.trans inf_le_left
      have hFy : sy ≤ memB (opairB F y) (𝓜.evalAtGraph q) :=
        inf_le_right.trans inf_le_right
      have hFeval := (𝓜.memB_evalAtGraph_le q F y).trans' hFy
      have hFC : sy ≤ memB F 𝓜.C := hFeval.trans inf_le_left
      have hqy : sy ≤ memB (opairB q y) F := hFeval.trans inf_le_right
      rw [memB_graphImageB] at hFimg
      have hFimg' : sy ≤
          memB F 𝓜.C ⊓
            ⨆ pₛ : AName A,
              memB pₛ (graphImageB FP S 𝓜.D) ⊓
                memB (opairB pₛ F) 𝓜.Fun :=
        hFimg
      refine (le_inf le_rfl (hFimg'.trans inf_le_right)).trans ?_
      rw [inf_iSup_eq]
      refine iSup_le fun pₛ => ?_
      let sp :=
        sy ⊓
          (memB pₛ (graphImageB FP S 𝓜.D) ⊓
            memB (opairB pₛ F) 𝓜.Fun)
      change sp ≤ relB 𝓜.R y b
      have hspS : sp ≤ sy := inf_le_left
      have hpₛImg : sp ≤ memB pₛ (graphImageB FP S 𝓜.D) :=
        inf_le_right.trans inf_le_left
      have hpₛF : sp ≤ memB (opairB pₛ F) 𝓜.Fun :=
        inf_le_right.trans inf_le_right
      rw [memB_graphImageB] at hpₛImg
      have hpₛImg' : sp ≤
          memB pₛ 𝓜.D ⊓
            ⨆ w : AName A,
              memB w S ⊓ memB (opairB w pₛ) FP :=
        hpₛImg
      refine (le_inf le_rfl (hpₛImg'.trans inf_le_right)).trans ?_
      rw [inf_iSup_eq]
      refine iSup_le fun w => ?_
      let sw :=
        sp ⊓ (memB w S ⊓ memB (opairB w pₛ) FP)
      change sw ≤ relB 𝓜.R y b
      have hswS : sw ≤ s :=
        inf_le_left.trans (hspS.trans hsyS)
      have hwS : sw ≤ memB w S :=
        inf_le_right.trans inf_le_left
      have hwpₛ : sw ≤ memB (opairB w pₛ) FP :=
        inf_le_right.trans inf_le_right
      have hFsc : sw ≤
          isScottContinuousB F 𝓜.D 𝓜.D 𝓜.R 𝓜.R :=
        (𝓜.mem_mapSpace_le_scottContinuous F).trans' <|
          inf_le_left.trans (hspS.trans hFC)
      have hyFsup : sw ≤
          isSupRelB y (graphImageB F (graphImageB FQ S 𝓜.D) 𝓜.D)
            𝓜.R :=
        ((scottContinuous_image_sup (hF := hFsc)
            F (graphImageB FQ S 𝓜.D) 𝓜.D 𝓜.D 𝓜.R 𝓜.R
            q y).trans inf_le_right).trans' <|
          le_inf (le_inf (le_inf le_rfl
              (hswS.trans (hQimg.trans inf_le_left)))
            (hswS.trans (hQimg.trans inf_le_right)))
            (inf_le_left.trans (hspS.trans hqy))
      have hbF : sw ≤ isUpperBoundRelB b
          (graphImageB F (graphImageB FQ S 𝓜.D) 𝓜.D) 𝓜.R := by
        refine le_iInf fun z => ?_
        rw [le_himp_iff, memB_graphImageB, ← inf_assoc, inf_iSup_eq]
        refine iSup_le fun qₜ => ?_
        let sz :=
          (sw ⊓ memB z 𝓜.D) ⊓
            (memB qₜ (graphImageB FQ S 𝓜.D) ⊓
              memB (opairB qₜ z) F)
        change sz ≤ relB 𝓜.R z b
        have hszS : sz ≤ sw := inf_le_left.trans inf_le_left
        have hzD : sz ≤ memB z 𝓜.D := inf_le_left.trans inf_le_right
        have hqₜImg : sz ≤ memB qₜ (graphImageB FQ S 𝓜.D) :=
          inf_le_right.trans inf_le_left
        have hqₜz : sz ≤ memB (opairB qₜ z) F :=
          inf_le_right.trans inf_le_right
        rw [memB_graphImageB] at hqₜImg
        have hqₜImg' : sz ≤
            memB qₜ 𝓜.D ⊓
              ⨆ t₀ : AName A,
                memB t₀ S ⊓ memB (opairB t₀ qₜ) FQ :=
          hqₜImg
        refine (le_inf le_rfl (hqₜImg'.trans inf_le_right)).trans ?_
        rw [inf_iSup_eq]
        refine iSup_le fun t₀ => ?_
        let st :=
          sz ⊓ (memB t₀ S ⊓ memB (opairB t₀ qₜ) FQ)
        change st ≤ relB 𝓜.R z b
        have hstS : st ≤ s :=
          inf_le_left.trans (hszS.trans hswS)
        have ht₀S : st ≤ memB t₀ S :=
          inf_le_right.trans inf_le_left
        have ht₀q : st ≤ memB (opairB t₀ qₜ) FQ :=
          inf_le_right.trans inf_le_right
        have hwS' : st ≤ memB w S :=
          inf_le_left.trans (hszS.trans hwS)
        have hcommon :
            st ≤ ⨆ r : AName A,
              memB r S ⊓ relB 𝓜.R w r ⊓ relB 𝓜.R t₀ r :=
          (isDirectedRelB_upper_apply S 𝓜.D 𝓜.R w t₀).trans' <|
            le_inf (le_inf (hstS.trans (hsT.trans htDir)) hwS') ht₀S
        refine (le_inf le_rfl hcommon).trans ?_
        rw [inf_iSup_eq]
        refine iSup_le fun r => ?_
        let sr :=
          st ⊓ (memB r S ⊓ relB 𝓜.R w r ⊓ relB 𝓜.R t₀ r)
        change sr ≤ relB 𝓜.R z b
        have hsrS : sr ≤ s := inf_le_left.trans hstS
        have hrS : sr ≤ memB r S :=
          inf_le_right.trans (inf_le_left.trans inf_le_left)
        have hwr : sr ≤ relB 𝓜.R w r :=
          inf_le_right.trans (inf_le_left.trans inf_le_right)
        have ht₀r : sr ≤ relB 𝓜.R t₀ r :=
          inf_le_right.trans inf_le_right
        have hrD : sr ≤ memB r 𝓜.D :=
          (memB_of_subsetB r S 𝓜.D).trans' <|
            le_inf hrS (hsrS.trans (hsT.trans htDir) |>.trans
              (isDirectedRelB_subset S 𝓜.D 𝓜.R))
        have htotApp : sr ≤ ⨆ zᵣ : AName A,
            memB (opairB r zᵣ) Fapp :=
          (isTotalB_apply Fapp 𝓜.D r).trans' <|
            le_inf
              ((hsrS.trans (hsT.trans htA) |>.trans hfunApp).trans
                inf_le_right)
              hrD
        refine (le_inf le_rfl htotApp).trans ?_
        rw [inf_iSup_eq]
        refine iSup_le fun zᵣ => ?_
        let szr := sr ⊓ memB (opairB r zᵣ) Fapp
        change szr ≤ relB 𝓜.R z b
        have hszrS : szr ≤ s := inf_le_left.trans hsrS
        have hrzᵣ : szr ≤ memB (opairB r zᵣ) Fapp := inf_le_right
        have hzᵣb : szr ≤ relB 𝓜.R zᵣ b := by
          have hu := iInf_le
            (fun w' : AName A => ⨅ z' : AName A,
              memB w' S ⊓ memB (opairB w' z') Fapp ⇨
                relB 𝓜.R z' b) r
          have hz := (iInf_le
            (fun z' : AName A =>
              memB r S ⊓ memB (opairB r z') Fapp ⇨
                relB 𝓜.R z' b) zᵣ).trans' hu
          exact (le_himp_iff.mp hz).trans' <|
            le_inf (hszrS.trans (hsT.trans htUpper))
              (le_inf (inf_le_left.trans hrS) hrzᵣ)
        have hdecR :
            szr ≤ ⨆ pᵣ : AName A, ⨆ qᵣ : AName A, ⨆ cᵣ : AName A,
              memB (opairB r pᵣ) FP ⊓
              memB (opairB r qᵣ) FQ ⊓
              memB (opairB pᵣ cᵣ) 𝓜.Fun ⊓
              memB cᵣ 𝓜.C ⊓
              memB (opairB qᵣ zᵣ) cᵣ :=
          (interpDKBodyGraph_app_mem_decompose
              𝓜 V K hK hV η x P Q a r zᵣ).trans' <|
            le_inf (hszrS.trans (hsT.trans htA)) hrzᵣ
        refine (le_inf le_rfl hdecR).trans ?_
        rw [inf_iSup_eq]
        refine iSup_le fun pᵣ => ?_
        rw [inf_iSup_eq]
        refine iSup_le fun qᵣ => ?_
        rw [inf_iSup_eq]
        refine iSup_le fun cᵣ => ?_
        let sc :=
          szr ⊓
            (memB (opairB r pᵣ) FP ⊓
              memB (opairB r qᵣ) FQ ⊓
              memB (opairB pᵣ cᵣ) 𝓜.Fun ⊓
              memB cᵣ 𝓜.C ⊓
              memB (opairB qᵣ zᵣ) cᵣ)
        change sc ≤ relB 𝓜.R z b
        have hscS : sc ≤ s := inf_le_left.trans hszrS
        have hscφ : sc ≤
            memB (opairB r pᵣ) FP ⊓
              memB (opairB r qᵣ) FQ ⊓
              memB (opairB pᵣ cᵣ) 𝓜.Fun ⊓
              memB cᵣ 𝓜.C ⊓
              memB (opairB qᵣ zᵣ) cᵣ :=
          inf_le_right
        have hscA : sc ≤ a := hscS.trans (hsT.trans htA)
        have hsc_wp : sc ≤ memB (opairB w pₛ) FP :=
          inf_le_left.trans (inf_le_left.trans (inf_le_left.trans
            (inf_le_left.trans (inf_le_left.trans
              (inf_le_left.trans hwpₛ)))))
        have hsc_rp : sc ≤ memB (opairB r pᵣ) FP :=
          hscφ.trans (inf_le_left.trans (inf_le_left.trans
            (inf_le_left.trans inf_le_left)))
        have hsc_wr : sc ≤ relB 𝓜.R w r :=
          inf_le_left.trans (inf_le_left.trans hwr)
        have hsc_tq : sc ≤ memB (opairB t₀ qₜ) FQ :=
          inf_le_left.trans (inf_le_left.trans
            (inf_le_left.trans ht₀q))
        have hsc_rq : sc ≤ memB (opairB r qᵣ) FQ :=
          hscφ.trans (inf_le_left.trans (inf_le_left.trans
            (inf_le_left.trans inf_le_right)))
        have hsc_tr : sc ≤ relB 𝓜.R t₀ r :=
          inf_le_left.trans (inf_le_left.trans ht₀r)
        have hsc_pF : sc ≤ memB (opairB pₛ F) 𝓜.Fun :=
          inf_le_left.trans (inf_le_left.trans (inf_le_left.trans
            (inf_le_left.trans (inf_le_left.trans (inf_le_left.trans
              (inf_le_left.trans hpₛF))))))
        have hsc_pc : sc ≤ memB (opairB pᵣ cᵣ) 𝓜.Fun :=
          hscφ.trans (inf_le_left.trans
            (inf_le_left.trans inf_le_right))
        have hsc_qz : sc ≤ memB (opairB qₜ z) F :=
          inf_le_left.trans (inf_le_left.trans (inf_le_left.trans
            (inf_le_left.trans hqₜz)))
        have hsc_qz' : sc ≤ memB (opairB qᵣ zᵣ) cᵣ :=
          hscφ.trans inf_le_right
        have hzzᵣ : sc ≤ relB 𝓜.R z zᵣ :=
          (interpDKBodyGraph_app_bi_mono
              𝓜 V K hK hV η x P Q a hPsc hQsc
              w r t₀ r pₛ pᵣ qₜ qᵣ F cᵣ z zᵣ).trans' <|
            le_inf (le_inf (le_inf (le_inf
                hscA
                (le_inf (le_inf hsc_wp hsc_rp) hsc_wr))
              (le_inf (le_inf hsc_tq hsc_rq) hsc_tr))
              (le_inf hsc_pF hsc_pc))
              (le_inf hsc_qz hsc_qz')
        have hzᵣb' : sc ≤ relB 𝓜.R zᵣ b :=
          inf_le_left.trans hzᵣb
        exact (𝓜.relR_trans z zᵣ b).trans' (le_inf hzzᵣ hzᵣb')
      exact (isSupRelB_least y
          (graphImageB F (graphImageB FQ S 𝓜.D) 𝓜.D)
          𝓜.R b).trans' <|
        le_inf hyFsup hbF
    exact (isSupRelB_least v
        (graphImageB (𝓜.evalAtGraph q)
          (graphImageB 𝓜.Fun (graphImageB FP S 𝓜.D) 𝓜.C)
          𝓜.D)
        𝓜.R b).trans' <|
      le_inf hvsup hupperb

/-- Degree-local Scott continuity of the application body graph. -/
theorem interpDKBodyGraph_app_le_scottContinuous
    (𝓜 : InternalReflexiveModel (A := A))
    (V K : AName.{u} A) (hK : subsetB K 𝓜.D = ⊤)
    (hV : (oid V).IsTotal)
    (η : RelFun (oid V) (oid 𝓜.D))
    (x : V.idx) (P Q : LamDK V.idx K.idx) (a : A)
    (hP : ∀ d, IsRelElementAt 𝓜.D a
      (interpDKRelVal 𝓜 V K hK hV
        (η.update hV 𝓜.total x d) P))
    (hQ : ∀ d, IsRelElementAt 𝓜.D a
      (interpDKRelVal 𝓜 V K hK hV
        (η.update hV 𝓜.total x d) Q))
    (hPsc : a ≤ isScottContinuousB
      (interpDKBodyGraph 𝓜 V K hK hV η x P) 𝓜.D 𝓜.D 𝓜.R 𝓜.R)
    (hQsc : a ≤ isScottContinuousB
      (interpDKBodyGraph 𝓜 V K hK hV η x Q) 𝓜.D 𝓜.D 𝓜.R 𝓜.R) :
    a ≤ isScottContinuousB
      (interpDKBodyGraph 𝓜 V K hK hV η x (.app P Q))
      𝓜.D 𝓜.D 𝓜.R 𝓜.R := by
  unfold isScottContinuousB
  refine le_inf (le_inf ?_ ?_) ?_
  · exact interpDKBodyGraph_app_le_isFunctionB
      𝓜 V K hK hV η x P Q a hP hQ
  · refine le_iInf fun u => le_iInf fun u' =>
      le_iInf fun v => le_iInf fun v' => ?_
    rw [le_himp_iff]
    exact (interpDKBodyGraph_app_apply_mono
        𝓜 V K hK hV η x P Q a hPsc hQsc u u' v v').trans' <| by
      apply le_of_eq
      ac_rfl
  · refine le_iInf fun S => le_iInf fun u => le_iInf fun v => ?_
    rw [le_himp_iff]
    exact (interpDKBodyGraph_app_mapsToSup
        𝓜 V K hK hV η x P Q a
        (interpDKBodyGraph_app_le_isFunctionB
          𝓜 V K hK hV η x P Q a hP hQ)
        hPsc hQsc S u v).trans' <| by
      apply le_of_eq
      ac_rfl

/-!
## Abstraction constructor
-/

/-- Complementary Boolean pieces of a degree reassemble. -/
theorem le_of_compl_cover {a p q : A}
    (hp : a ⊓ p ≤ q) (hpc : a ⊓ pᶜ ≤ q) : a ≤ q := by
  have : a = (a ⊓ p) ⊔ (a ⊓ pᶜ) := by
    rw [← inf_sup_left, sup_compl_eq_top, inf_top_eq]
  rw [this]
  exact sup_le hp hpc

/-- Distinct keys are disjoint from a common source at the complement of
key equality. -/
theorem setoidEq_keys_disjoint {X : Type*}
    (S : ASetoid (A := A) X) (x y i : X) :
    (S.eq x y)ᶜ ⊓ S.eq i x ⊓ S.eq i y ≤ ⊥ := by
  have hxy : S.eq i x ⊓ S.eq i y ≤ S.eq x y := by
    refine (S.trans x i y).trans' (le_inf ?_ inf_le_right)
    rw [S.symm x i]
    exact inf_le_left
  have hre : (S.eq x y)ᶜ ⊓ S.eq i x ⊓ S.eq i y =
      (S.eq x y)ᶜ ⊓ (S.eq i x ⊓ S.eq i y) := by
    ac_rfl
  rw [hre]
  exact (inf_le_inf le_rfl hxy).trans_eq (compl_inf_self _)

/-- Overwriting a key equal to an earlier key makes the first update
irrelevant. -/
theorem setoidEq_overwrite_disjoint {X : Type*}
    (S : ASetoid (A := A) X) (x y i : X) :
    S.eq x y ⊓ (S.eq i x)ᶜ ⊓ S.eq i y ≤ ⊥ := by
  have hix : S.eq i y ⊓ S.eq x y ≤ S.eq i x := by
    refine (S.trans i y x).trans' (le_inf inf_le_left ?_)
    rw [S.symm y x]
    exact inf_le_right
  have hre : S.eq x y ⊓ (S.eq i x)ᶜ ⊓ S.eq i y =
      (S.eq i y ⊓ S.eq x y) ⊓ (S.eq i x)ᶜ := by
    ac_rfl
  rw [hre]
  exact (inf_le_inf hix le_rfl).trans_eq (inf_compl_eq_bot)

/-- `p ⊓ q ⊓ r ≤ ⊥` yields `p ⊓ q ≤ rᶜ`. -/
theorem le_compl_of_inf_bot {p q r : A} (h : p ⊓ q ⊓ r ≤ ⊥) :
    p ⊓ q ≤ rᶜ := by
  rw [le_compl_iff_disjoint_left, disjoint_iff]
  exact le_bot_iff.mp (h.trans' (by apply le_of_eq; ac_rfl))

/-- Degree-local commutation of successive environment updates, on the
complement of key equality. -/
theorem RelFun.update_commute_val
    {X Y : Type*} {S : ASetoid (A := A) X} {T : ASetoid (A := A) Y}
    (f : RelFun S T) (hS : S.IsTotal) (hT : T.IsTotal)
    (x y : X) (d z : Y) (i : X) (j : Y) :
    (S.eq x y)ᶜ ⊓
        ((f.update hS hT y d).update hS hT x z).val i j ≤
      ((f.update hS hT x z).update hS hT y d).val i j := by
  have hdisj := setoidEq_keys_disjoint S x y i
  rw [RelFun.update_val, RelFun.update_val, RelFun.update_val,
    RelFun.update_val]
  rw [inf_sup_left]
  refine sup_le ?_ ?_
  · apply le_sup_of_le_right
    refine le_inf ?_ ?_
    · exact (le_compl_of_inf_bot hdisj).trans' <|
        le_inf inf_le_left (inf_le_right.trans inf_le_left)
    · apply le_sup_of_le_left
      exact inf_le_right
  · rw [← inf_assoc, inf_sup_left]
    refine sup_le ?_ ?_
    · apply le_sup_of_le_left
      refine le_inf (inf_le_right.trans inf_le_left)
        (inf_le_right.trans inf_le_right)
    · apply le_sup_of_le_right
      refine le_inf (inf_le_right.trans inf_le_left) ?_
      apply le_sup_of_le_right
      refine le_inf (inf_le_left.trans inf_le_right)
        (inf_le_right.trans inf_le_right)

/-- The other direction of `RelFun.update_commute_val`. -/
theorem RelFun.update_commute_val_symm
    {X Y : Type*} {S : ASetoid (A := A) X} {T : ASetoid (A := A) Y}
    (f : RelFun S T) (hS : S.IsTotal) (hT : T.IsTotal)
    (x y : X) (d z : Y) (i : X) (j : Y) :
    (S.eq x y)ᶜ ⊓
        ((f.update hS hT x z).update hS hT y d).val i j ≤
      ((f.update hS hT y d).update hS hT x z).val i j := by
  have h := RelFun.update_commute_val f hS hT y x z d i j
  rwa [S.symm y x] at h

/-- The second update at an equal key overwrites the first. -/
theorem RelFun.update_overwrite_val
    {X Y : Type*} {S : ASetoid (A := A) X} {T : ASetoid (A := A) Y}
    (f : RelFun S T) (hS : S.IsTotal) (hT : T.IsTotal)
    (x y : X) (d z : Y) (i : X) (j : Y) :
    S.eq x y ⊓
        ((f.update hS hT y d).update hS hT x z).val i j ≤
      (f.update hS hT x z).val i j := by
  have hdisj := setoidEq_overwrite_disjoint S x y i
  rw [RelFun.update_val, RelFun.update_val, RelFun.update_val]
  rw [inf_sup_left]
  refine sup_le ?_ ?_
  · apply le_sup_of_le_left
    exact inf_le_right
  · rw [← inf_assoc, inf_sup_left]
    refine sup_le ?_ ?_
    · exact (hdisj.trans bot_le).trans' <|
        le_inf inf_le_left (inf_le_right.trans inf_le_left)
    · apply le_sup_of_le_right
      refine le_inf (inf_le_left.trans inf_le_right)
        (inf_le_right.trans inf_le_right)

/-- The converse of `RelFun.update_overwrite_val`. -/
theorem RelFun.update_overwrite_val_symm
    {X Y : Type*} {S : ASetoid (A := A) X} {T : ASetoid (A := A) Y}
    (f : RelFun S T) (hS : S.IsTotal) (hT : T.IsTotal)
    (x y : X) (d z : Y) (i : X) (j : Y) :
    S.eq x y ⊓ (f.update hS hT x z).val i j ≤
      ((f.update hS hT y d).update hS hT x z).val i j := by
  have hdisj := setoidEq_overwrite_disjoint S x y i
  rw [RelFun.update_val, RelFun.update_val, RelFun.update_val]
  rw [inf_sup_left]
  refine sup_le ?_ ?_
  · apply le_sup_of_le_left
    exact inf_le_right
  · apply le_sup_of_le_right
    refine le_inf (inf_le_right.trans inf_le_left) ?_
    apply le_sup_of_le_right
    refine le_inf ?_ ?_
    · exact (le_compl_of_inf_bot hdisj).trans' <|
        le_inf inf_le_left (inf_le_right.trans inf_le_left)
    · exact inf_le_right.trans inf_le_right

/-- Interpretation transports along a mutual degree-local comparison of
environments. -/
theorem interpDKRelVal_le_of_env
    (𝓜 : InternalReflexiveModel (A := A))
    (V K : AName.{u} A) (hK : subsetB K 𝓜.D = ⊤)
    (hV : (oid V).IsTotal)
    (η₁ η₂ : RelFun (oid V) (oid 𝓜.D)) (a : A)
    (hη : ∀ i j, a ⊓ η₁.val i j ≤ η₂.val i j)
    (hη' : ∀ i j, a ⊓ η₂.val i j ≤ η₁.val i j)
    (M : LamDK V.idx K.idx) (d : 𝓜.D.idx) :
    a ⊓ interpDKRelVal 𝓜 V K hK hV η₁ M d ≤
      interpDKRelVal 𝓜 V K hK hV η₂ M d := by
  let ηs : Bool → RelFun (oid V) (oid 𝓜.D) :=
    fun b => if b then η₁ else η₂
  have hηs : RelFun.IsPointwiseFamily (degreePairSetoid a) ηs := by
    intro b1 b2 i j
    by_cases h : b1 = b2
    · have : (degreePairSetoid a).eq b1 b2 = ⊤ := by
        simp [degreePairSetoid, h]
      rw [this, top_inf_eq, h]
    · have : (degreePairSetoid a).eq b1 b2 = a := by
        simp [degreePairSetoid, h]
      rw [this]
      cases b1 <;> cases b2
      · exact (h rfl).elim
      · exact hη' i j
      · exact hη i j
      · exact (h rfl).elim
  have h := interpDKRelVal_isPointwiseFamily 𝓜 V K hK hV
    (degreePairSetoid a) ηs hηs M true false d
  simpa [degreePairSetoid, ηs] using h

/-- Commuting updates transport the interpretation at the complement of
key equality. -/
theorem interpDKRelVal_update_commute
    (𝓜 : InternalReflexiveModel (A := A))
    (V K : AName.{u} A) (hK : subsetB K 𝓜.D = ⊤)
    (hV : (oid V).IsTotal)
    (η : RelFun (oid V) (oid 𝓜.D))
    (x y : V.idx) (d e : 𝓜.D.idx)
    (P : LamDK V.idx K.idx) (w : 𝓜.D.idx) :
    ((oid V).eq x y)ᶜ ⊓
        interpDKRelVal 𝓜 V K hK hV
          ((η.update hV 𝓜.total y d).update hV 𝓜.total x e) P w ≤
      interpDKRelVal 𝓜 V K hK hV
        ((η.update hV 𝓜.total x e).update hV 𝓜.total y d) P w :=
  interpDKRelVal_le_of_env 𝓜 V K hK hV _ _ ((oid V).eq x y)ᶜ
    (fun i j => RelFun.update_commute_val η hV 𝓜.total x y d e i j)
    (fun i j => RelFun.update_commute_val_symm η hV 𝓜.total x y d e i j)
    P w

/-- The other direction of `interpDKRelVal_update_commute`. -/
theorem interpDKRelVal_update_commute_symm
    (𝓜 : InternalReflexiveModel (A := A))
    (V K : AName.{u} A) (hK : subsetB K 𝓜.D = ⊤)
    (hV : (oid V).IsTotal)
    (η : RelFun (oid V) (oid 𝓜.D))
    (x y : V.idx) (d e : 𝓜.D.idx)
    (P : LamDK V.idx K.idx) (w : 𝓜.D.idx) :
    ((oid V).eq x y)ᶜ ⊓
        interpDKRelVal 𝓜 V K hK hV
          ((η.update hV 𝓜.total x e).update hV 𝓜.total y d) P w ≤
      interpDKRelVal 𝓜 V K hK hV
        ((η.update hV 𝓜.total y d).update hV 𝓜.total x e) P w :=
  interpDKRelVal_le_of_env 𝓜 V K hK hV _ _ ((oid V).eq x y)ᶜ
    (fun i j => RelFun.update_commute_val_symm η hV 𝓜.total x y d e i j)
    (fun i j => RelFun.update_commute_val η hV 𝓜.total x y d e i j)
    P w

/-- Overwriting an equal key forgets the earlier update. -/
theorem interpDKRelVal_update_overwrite
    (𝓜 : InternalReflexiveModel (A := A))
    (V K : AName.{u} A) (hK : subsetB K 𝓜.D = ⊤)
    (hV : (oid V).IsTotal)
    (η : RelFun (oid V) (oid 𝓜.D))
    (x y : V.idx) (d e : 𝓜.D.idx)
    (P : LamDK V.idx K.idx) (w : 𝓜.D.idx) :
    (oid V).eq x y ⊓
        interpDKRelVal 𝓜 V K hK hV
          ((η.update hV 𝓜.total y d).update hV 𝓜.total x e) P w ≤
      interpDKRelVal 𝓜 V K hK hV (η.update hV 𝓜.total x e) P w :=
  interpDKRelVal_le_of_env 𝓜 V K hK hV _ _ ((oid V).eq x y)
    (fun i j => RelFun.update_overwrite_val η hV 𝓜.total x y d e i j)
    (fun i j => RelFun.update_overwrite_val_symm η hV 𝓜.total x y d e i j)
    P w

/-- The converse of `interpDKRelVal_update_overwrite`. -/
theorem interpDKRelVal_update_overwrite_symm
    (𝓜 : InternalReflexiveModel (A := A))
    (V K : AName.{u} A) (hK : subsetB K 𝓜.D = ⊤)
    (hV : (oid V).IsTotal)
    (η : RelFun (oid V) (oid 𝓜.D))
    (x y : V.idx) (d e : 𝓜.D.idx)
    (P : LamDK V.idx K.idx) (w : 𝓜.D.idx) :
    (oid V).eq x y ⊓
        interpDKRelVal 𝓜 V K hK hV (η.update hV 𝓜.total x e) P w ≤
      interpDKRelVal 𝓜 V K hK hV
        ((η.update hV 𝓜.total y d).update hV 𝓜.total x e) P w :=
  interpDKRelVal_le_of_env 𝓜 V K hK hV _ _ ((oid V).eq x y)
    (fun i j => RelFun.update_overwrite_val_symm η hV 𝓜.total x y d e i j)
    (fun i j => RelFun.update_overwrite_val η hV 𝓜.total x y d e i j)
    P w

/-- A name whose coefficients lie below `a` is empty at `aᶜ`. -/
theorem eqB_mk_zero_of_val_le {I : Type u}
    (child : I → AName.{u} A) (v : I → A) (a : A)
    (hv : ∀ i, v i ≤ a) :
    aᶜ ≤ eqB (mk I child v) (mk I child (fun _ => ⊥)) :=
  le_eqB_mk_of_le_val child v (fun _ => ⊥) aᶜ
    (fun i =>
      ((inf_le_inf le_rfl (hv i)).trans_eq (compl_inf_self _)))
    (fun _ => inf_le_right.trans bot_le)

/-- The empty pair graph is not a member of the continuous-map space. -/
theorem memB_zeroPairGraph_mapSpace
    (𝓜 : InternalReflexiveModel (A := A)) :
    memB (zeroPairGraph 𝓜.D) 𝓜.C = ⊥ := by
  have i : 𝓜.D.idx := Classical.choice 𝓜.complete.nonempty
  have hi : memB (𝓜.D.child i) 𝓜.D = ⊤ := by
    rw [← oid_eps]
    exact 𝓜.total i
  have htot :
      memB (zeroPairGraph 𝓜.D) 𝓜.C ≤
        isTotalB (zeroPairGraph 𝓜.D) 𝓜.D :=
    (𝓜.mem_mapSpace_le_function (zeroPairGraph 𝓜.D)).trans inf_le_right
  have hempty :
      (⨆ y : AName A,
        memB (opairB (𝓜.D.child i) y) (zeroPairGraph 𝓜.D)) = ⊥ := by
    apply le_bot_iff.mp
    refine iSup_le fun y => ?_
    unfold zeroPairGraph
    rw [memB_mk]
    exact iSup_le fun _ => inf_le_right.trans bot_le
  have hnototal : isTotalB (zeroPairGraph 𝓜.D) 𝓜.D ≤ ⊥ := by
    have happ :=
      isTotalB_apply (zeroPairGraph 𝓜.D) 𝓜.D (𝓜.D.child i)
    rw [hi, inf_top_eq, hempty] at happ
    exact happ
  exact eq_bot_iff.mpr (htot.trans hnototal)

end Scott2026
