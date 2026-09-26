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
import Scott2026.LambdaModels.DomainTheory.InternalEvalComplete.Proofs.CoreContContCont
import Scott2026.LambdaModels.DomainTheory.InternalEvalComplete.Proofs.CoreContContContCont
import Scott2026.LambdaModels.DomainTheory.InternalEvalComplete.Proofs.CoreContContContCont
import Scott2026.LambdaModels.DomainTheory.InternalEvalComplete.interpDKAbsFamilyImageLawsC
import Scott2026.LambdaModels.DomainTheory.InternalEval.Proofs.CoreCont

namespace Scott2026

universe u


open AName InternalReflexiveModel

variable {A : Type u} [CompleteBooleanAlgebra A]

/-- A generalized element transports its coefficients along target equality. -/
theorem interpDKAbsFamily_image_isSupRelB
    (𝓜 : InternalReflexiveModel (A := A))
    (V K : AName.{u} A) (hK : subsetB K 𝓜.D = ⊤)
    (hV : (oid V).IsTotal)
    (η : RelFun (oid V) (oid 𝓜.D))
    (y x : V.idx) (P : LamDK V.idx K.idx) (a : A)
    (hInner : ∀ d, a ≤ isScottContinuousB
      (interpDKBodyGraph 𝓜 V K hK hV (η.update hV 𝓜.total y d) x P)
      𝓜.D 𝓜.D 𝓜.R 𝓜.R)
    (hOuter : ∀ z, a ≤ isScottContinuousB
      (interpDKBodyGraph 𝓜 V K hK hV (η.update hV 𝓜.total x z) y P)
      𝓜.D 𝓜.D 𝓜.R 𝓜.R)
    (hInnerRows : ∀ d, ∀ e, IsRelElementAt 𝓜.D a
      (interpDKRelVal 𝓜 V K hK hV
        ((η.update hV 𝓜.total y d).update hV 𝓜.total x e) P))
    (hOuterRows : ∀ z, ∀ d, IsRelElementAt 𝓜.D a
      (interpDKRelVal 𝓜 V K hK hV
        ((η.update hV 𝓜.total x z).update hV 𝓜.total y d) P))
    (S : AName.{u} A) (d : 𝓜.D.idx) :
    ((oid V).eq x y)ᶜ ⊓ a ⊓
        isDirectedRelB S 𝓜.D 𝓜.R ⊓
        isSupRelB (𝓜.D.child d) S 𝓜.R ≤
      isSupRelB
        (interpDKBodyGraph 𝓜 V K hK hV (η.update hV 𝓜.total y d) x P)
        (graphImageB
          (interpDKAbsFamilyGraph 𝓜 V K hK hV η y x P) S 𝓜.C)
        𝓜.Q := by
  unfold isSupRelB
  refine le_inf ?_ ?_
  · refine le_iInf fun G => ?_
    rw [le_himp_iff]
    exact (interpDKAbsFamily_image_upper 𝓜 V K hK hV η y x P a
        hInner hOuter hInnerRows hOuterRows S d G).trans' <|
      le_inf (le_inf (le_inf
          (inf_le_left.trans (inf_le_left.trans
            (inf_le_left.trans inf_le_left)))
          (inf_le_left.trans (inf_le_left.trans
            (inf_le_left.trans inf_le_right))))
        (inf_le_left.trans (inf_le_right.trans inf_le_left)))
        inf_le_right
  · refine le_iInf fun G => ?_
    rw [le_himp_iff]
    exact interpDKAbsFamily_image_least 𝓜 V K hK hV η y x P a
      hInner hOuter hInnerRows hOuterRows S d G

/-- Directed-supremum preservation for the abs body graph, off the
diagonal. -/
theorem interpDKBodyGraph_abs_mapsToSup
    (𝓜 : InternalReflexiveModel (A := A))
    (V K : AName.{u} A) (hK : subsetB K 𝓜.D = ⊤)
    (hV : (oid V).IsTotal)
    (η : RelFun (oid V) (oid 𝓜.D))
    (y x : V.idx) (P : LamDK V.idx K.idx) (a : A)
    (hInner : ∀ d, a ≤ isScottContinuousB
      (interpDKBodyGraph 𝓜 V K hK hV (η.update hV 𝓜.total y d) x P)
      𝓜.D 𝓜.D 𝓜.R 𝓜.R)
    (hOuter : ∀ z, a ≤ isScottContinuousB
      (interpDKBodyGraph 𝓜 V K hK hV (η.update hV 𝓜.total x z) y P)
      𝓜.D 𝓜.D 𝓜.R 𝓜.R)
    (hInnerRows : ∀ d, ∀ e, IsRelElementAt 𝓜.D a
      (interpDKRelVal 𝓜 V K hK hV
        ((η.update hV 𝓜.total y d).update hV 𝓜.total x e) P))
    (hOuterRows : ∀ z, ∀ d, IsRelElementAt 𝓜.D a
      (interpDKRelVal 𝓜 V K hK hV
        ((η.update hV 𝓜.total x z).update hV 𝓜.total y d) P))
    (S u v : AName.{u} A) :
    ((oid V).eq x y)ᶜ ⊓ a ⊓ lamDKVal V K (.abs x P) ⊓
        isDirectedRelB S 𝓜.D 𝓜.R ⊓ isSupRelB u S 𝓜.R ⊓
        memB (opairB u v)
          (interpDKBodyGraph 𝓜 V K hK hV η y (.abs x P)) ≤
      mapsToSupB
        (interpDKBodyGraph 𝓜 V K hK hV η y (.abs x P))
        S v 𝓜.R := by
  let Fabs := interpDKBodyGraph 𝓜 V K hK hV η y (.abs x P)
  let Fg := interpDKAbsFamilyGraph 𝓜 V K hK hV η y x P
  let b := a ⊓ lamDKVal V K (.abs x P)
  have hfun : b ≤ isFunctionB Fabs 𝓜.D 𝓜.D :=
    interpDKBodyGraph_abs_le_isFunctionB 𝓜 V K hK hV η y x P a
      hInner hInnerRows
  unfold mapsToSupB
  refine le_inf ?_ ?_
  · refine le_iInf fun w => le_iInf fun z => ?_
    rw [le_himp_iff]
    let t :=
      (((oid V).eq x y)ᶜ ⊓ a ⊓ lamDKVal V K (.abs x P) ⊓
        isDirectedRelB S 𝓜.D 𝓜.R ⊓ isSupRelB u S 𝓜.R ⊓
        memB (opairB u v) Fabs) ⊓
      (memB w S ⊓ memB (opairB w z) Fabs)
    change t ≤ relB 𝓜.R z v
    have htEq : t ≤ ((oid V).eq x y)ᶜ :=
      inf_le_left.trans (inf_le_left.trans (inf_le_left.trans
        (inf_le_left.trans (inf_le_left.trans inf_le_left))))
    have htA : t ≤ a :=
      inf_le_left.trans (inf_le_left.trans (inf_le_left.trans
        (inf_le_left.trans (inf_le_left.trans inf_le_right))))
    have htLam : t ≤ lamDKVal V K (.abs x P) :=
      inf_le_left.trans (inf_le_left.trans (inf_le_left.trans
        (inf_le_left.trans inf_le_right)))
    have htuv : t ≤ memB (opairB u v) Fabs :=
      inf_le_left.trans inf_le_right
    have htwS : t ≤ memB w S := inf_le_right.trans inf_le_left
    have htwz : t ≤ memB (opairB w z) Fabs :=
      inf_le_right.trans inf_le_right
    have htu : t ≤ isSupRelB u S 𝓜.R :=
      inf_le_left.trans (inf_le_left.trans inf_le_right)
    have hwu : t ≤ relB 𝓜.R w u :=
      (isUpperBoundRelB_apply u S 𝓜.R w).trans' <|
        le_inf (htu.trans inf_le_left) htwS
    exact (interpDKBodyGraph_abs_apply_mono 𝓜 V K hK hV η y x P a
        hInner hOuter hInnerRows hOuterRows w u z v).trans' <|
      le_inf (le_inf (le_inf (le_inf (le_inf
          htEq htA) htLam) htwz) htuv) hwu
  · refine le_iInf fun c => ?_
    rw [le_himp_iff]
    let upper :=
      ⨅ w : AName A, ⨅ z : AName A,
        memB w S ⊓ memB (opairB w z) Fabs ⇨ relB 𝓜.R z c
    let t :=
      (((oid V).eq x y)ᶜ ⊓ a ⊓ lamDKVal V K (.abs x P) ⊓
        isDirectedRelB S 𝓜.D 𝓜.R ⊓ isSupRelB u S 𝓜.R ⊓
        memB (opairB u v) Fabs) ⊓ upper
    change t ≤ relB 𝓜.R v c
    have htEq : t ≤ ((oid V).eq x y)ᶜ :=
      inf_le_left.trans (inf_le_left.trans (inf_le_left.trans
        (inf_le_left.trans (inf_le_left.trans inf_le_left))))
    have htA : t ≤ a :=
      inf_le_left.trans (inf_le_left.trans (inf_le_left.trans
        (inf_le_left.trans (inf_le_left.trans inf_le_right))))
    have htLam : t ≤ lamDKVal V K (.abs x P) :=
      inf_le_left.trans (inf_le_left.trans (inf_le_left.trans
        (inf_le_left.trans inf_le_right)))
    have htB : t ≤ b := le_inf htA htLam
    have htDir : t ≤ isDirectedRelB S 𝓜.D 𝓜.R :=
      inf_le_left.trans (inf_le_left.trans
        (inf_le_left.trans inf_le_right))
    have htSup : t ≤ isSupRelB u S 𝓜.R :=
      inf_le_left.trans (inf_le_left.trans inf_le_right)
    have htuv : t ≤ memB (opairB u v) Fabs :=
      inf_le_left.trans inf_le_right
    have htUpper : t ≤ upper := inf_le_right
    have hdec :
        t ≤ ⨆ p : 𝓜.D.idx × 𝓜.D.idx,
          eqB (opairB u v)
            (opairB (𝓜.D.child p.1) (𝓜.D.child p.2)) ⊓
          memB (opairB (𝓜.D.child p.1) (𝓜.D.child p.2)) Fabs :=
      (inf_memB_le_iSup_matrix (hsub := (htB.trans hfun).trans
          (inf_le_left.trans inf_le_left)) (opairB u v)).trans' <|
        le_inf le_rfl htuv
    refine (le_inf le_rfl hdec).trans ?_
    rw [inf_iSup_eq (α := A)]
    refine iSup_le fun p => ?_
    let s :=
      t ⊓
        (eqB (opairB u v)
          (opairB (𝓜.D.child p.1) (𝓜.D.child p.2)) ⊓
        memB (opairB (𝓜.D.child p.1) (𝓜.D.child p.2)) Fabs)
    change s ≤ relB 𝓜.R v c
    have hsT : s ≤ t := inf_le_left
    have hsp : s ≤
        memB (opairB (𝓜.D.child p.1) (𝓜.D.child p.2)) Fabs :=
      inf_le_right.trans inf_le_right
    have hop : s ≤
        eqB (opairB u v)
          (opairB (𝓜.D.child p.1) (𝓜.D.child p.2)) :=
      inf_le_right.trans inf_le_left
    have hup : s ≤ eqB u (𝓜.D.child p.1) := by
      rw [eqB_opairB] at hop
      exact hop.trans inf_le_left
    have hvp : s ≤ eqB v (𝓜.D.child p.2) := by
      rw [eqB_opairB] at hop
      exact hop.trans inf_le_right
    have hsupP : s ≤ isSupRelB (𝓜.D.child p.1) S 𝓜.R :=
      (isSupRelB_congr u (𝓜.D.child p.1) S 𝓜.R).trans' <|
        le_inf hup (hsT.trans htSup)
    have hFdSup : s ≤
        isSupRelB
          (interpDKBodyGraph 𝓜 V K hK hV
            (η.update hV 𝓜.total y p.1) x P)
          (graphImageB Fg S 𝓜.C) 𝓜.Q :=
      (interpDKAbsFamily_image_isSupRelB 𝓜 V K hK hV η y x P a
          hInner hOuter hInnerRows hOuterRows S p.1).trans' <|
        le_inf (le_inf (le_inf (hsT.trans htEq) (hsT.trans htA))
          (hsT.trans htDir)) hsupP
    have hImgDir : s ≤
        isDirectedRelB (graphImageB Fg S 𝓜.C) 𝓜.C 𝓜.Q :=
      (interpDKAbsFamilyGraph_image_directed 𝓜 V K hK hV η y x P a
          hInner hOuter hInnerRows hOuterRows S).trans' <|
        le_inf (le_inf (hsT.trans htEq) (hsT.trans htA))
          (hsT.trans htDir)
    have hmemLam : s ≤
        memB (opairB
          (interpDKBodyGraph 𝓜 V K hK hV
            (η.update hV 𝓜.total y p.1) x P)
          (𝓜.D.child p.2)) 𝓜.Lam :=
      (interpDKBodyGraph_abs_mem_eq_lam 𝓜 V K hK hV η y x P a
          hInner hInnerRows p.1 p.2).le.trans' (le_inf (hsT.trans htB) hsp)
        |>.trans inf_le_right
    have hLam : (⊤ : A) ≤
        isScottContinuousB 𝓜.Lam 𝓜.C 𝓜.D 𝓜.Q 𝓜.R :=
      le_top.trans 𝓜.lam_continuous.ge
    have hLamImg : s ≤
        isDirectedRelB
          (graphImageB 𝓜.Lam (graphImageB Fg S 𝓜.C) 𝓜.D)
          𝓜.D 𝓜.R ⊓
        isSupRelB (𝓜.D.child p.2)
          (graphImageB 𝓜.Lam (graphImageB Fg S 𝓜.C) 𝓜.D)
          𝓜.R :=
      (scottContinuous_image_sup (hF := hLam)
          𝓜.Lam (graphImageB Fg S 𝓜.C) 𝓜.C 𝓜.D 𝓜.Q 𝓜.R
          (interpDKBodyGraph 𝓜 V K hK hV
            (η.update hV 𝓜.total y p.1) x P)
          (𝓜.D.child p.2)).trans' <|
        le_inf (le_inf (le_inf (le_top.trans le_top) hImgDir)
          hFdSup) hmemLam
    have hcub : s ≤
        isUpperBoundRelB c
          (graphImageB 𝓜.Lam (graphImageB Fg S 𝓜.C) 𝓜.D)
          𝓜.R := by
      refine le_iInf fun z => ?_
      rw [le_himp_iff, memB_graphImageB]
      refine (le_inf le_rfl (inf_le_right.trans inf_le_right)).trans ?_
      rw [inf_iSup_eq (α := A)]
      refine iSup_le fun G => ?_
      refine (le_inf (inf_le_left.trans inf_le_left) inf_le_right).trans ?_
      let sz :=
        s ⊓ (memB G (graphImageB Fg S 𝓜.C) ⊓ memB (opairB G z) 𝓜.Lam)
      change sz ≤ relB 𝓜.R z c
      have hszS : sz ≤ s := inf_le_left
      have hGimg : sz ≤ memB G (graphImageB Fg S 𝓜.C) :=
        inf_le_right.trans inf_le_left
      have hGz : sz ≤ memB (opairB G z) 𝓜.Lam :=
        inf_le_right.trans inf_le_right
      rw [memB_graphImageB] at hGimg
      have hdecG : sz ≤ ⨆ w : AName A,
          memB w S ⊓ memB (opairB w G) Fg :=
        hGimg.trans inf_le_right
      refine (le_inf le_rfl hdecG).trans ?_
      rw [inf_iSup_eq (α := A)]
      refine iSup_le fun w => ?_
      let sw :=
        sz ⊓ (memB w S ⊓ memB (opairB w G) Fg)
      change sw ≤ relB 𝓜.R z c
      have hswS : sw ≤ s := inf_le_left.trans hszS
      have hwS : sw ≤ memB w S := inf_le_right.trans inf_le_left
      have hwG : sw ≤ memB (opairB w G) Fg :=
        inf_le_right.trans inf_le_right
      have hdecW :
          sw ≤ ⨆ k : 𝓜.D.idx,
            eqB w (𝓜.D.child k) ⊓
              eqB G
                (interpDKBodyGraph 𝓜 V K hK hV
                  (η.update hV 𝓜.total y k) x P) :=
        hwG.trans_eq
          (memB_interpDKAbsFamilyGraph 𝓜 V K hK hV η y x P w G)
      refine (le_inf le_rfl hdecW).trans ?_
      rw [inf_iSup_eq (α := A)]
      refine iSup_le fun k => ?_
      let sk :=
        sw ⊓
          (eqB w (𝓜.D.child k) ⊓
            eqB G
              (interpDKBodyGraph 𝓜 V K hK hV
                (η.update hV 𝓜.total y k) x P))
      change sk ≤ relB 𝓜.R z c
      have hskW : sk ≤ sw := inf_le_left
      have hwk : sk ≤ eqB w (𝓜.D.child k) :=
        inf_le_right.trans inf_le_left
      have hGk : sk ≤
          eqB G
            (interpDKBodyGraph 𝓜 V K hK hV
              (η.update hV 𝓜.total y k) x P) :=
        inf_le_right.trans inf_le_right
      have hLamk : sk ≤
          memB (opairB
            (interpDKBodyGraph 𝓜 V K hK hV
              (η.update hV 𝓜.total y k) x P)
            z) 𝓜.Lam :=
        (memB_opairB_congr 𝓜.Lam G
            (interpDKBodyGraph 𝓜 V K hK hV
              (η.update hV 𝓜.total y k) x P)
            z z).trans' <|
          le_inf (le_inf hGk
              (le_top.trans (eqB_self (A := A) z).ge))
            (hskW.trans (inf_le_left.trans hGz))
      have hsubLam : subsetB 𝓜.Lam (prodB 𝓜.C 𝓜.D) = ⊤ :=
        isFunctionB_subset 𝓜.lam_function
      have hdecZ :
          sk ≤ ⨆ p : 𝓜.C.idx × 𝓜.D.idx,
            eqB (opairB
                (interpDKBodyGraph 𝓜 V K hK hV
                  (η.update hV 𝓜.total y k) x P)
                z)
              (opairB (𝓜.C.child p.1) (𝓜.D.child p.2)) ⊓
            memB (opairB (𝓜.C.child p.1) (𝓜.D.child p.2)) 𝓜.Lam :=
        (inf_memB_le_iSup_matrix
            (hsub := le_top.trans hsubLam.ge)
            (opairB
              (interpDKBodyGraph 𝓜 V K hK hV
                (η.update hV 𝓜.total y k) x P)
              z)).trans' <|
          le_inf le_rfl hLamk
      refine (le_inf le_rfl hdecZ).trans ?_
      rw [inf_iSup_eq (α := A)]
      refine iSup_le fun p => ?_
      let sn :=
        sk ⊓
          (eqB (opairB
              (interpDKBodyGraph 𝓜 V K hK hV
                (η.update hV 𝓜.total y k) x P)
              z)
            (opairB (𝓜.C.child p.1) (𝓜.D.child p.2)) ⊓
          memB (opairB (𝓜.C.child p.1) (𝓜.D.child p.2)) 𝓜.Lam)
      change sn ≤ relB 𝓜.R z c
      have hsnK : sn ≤ sk := inf_le_left
      have hop : sn ≤
          eqB (opairB
              (interpDKBodyGraph 𝓜 V K hK hV
                (η.update hV 𝓜.total y k) x P)
              z)
            (opairB (𝓜.C.child p.1) (𝓜.D.child p.2)) :=
        inf_le_right.trans inf_le_left
      have hzn : sn ≤ eqB z (𝓜.D.child p.2) := by
        rw [eqB_opairB] at hop
        exact hop.trans inf_le_right
      have hLamn : sn ≤
          memB (opairB
            (interpDKBodyGraph 𝓜 V K hK hV
              (η.update hV 𝓜.total y k) x P)
            (𝓜.D.child p.2)) 𝓜.Lam :=
        (memB_opairB_congr 𝓜.Lam (𝓜.C.child p.1)
            (interpDKBodyGraph 𝓜 V K hK hV
              (η.update hV 𝓜.total y k) x P)
            (𝓜.D.child p.2) (𝓜.D.child p.2)).trans' <|
          le_inf (le_inf
              (by
                rw [eqB_opairB] at hop
                exact hop.trans inf_le_left |>.trans_eq
                  (eqB_comm
                    (interpDKBodyGraph 𝓜 V K hK hV
                      (η.update hV 𝓜.total y k) x P)
                    (𝓜.C.child p.1)))
              (le_top.trans (eqB_self (A := A) (𝓜.D.child p.2)).ge))
            (inf_le_right.trans inf_le_right)
      have hFabsn : sn ≤
          memB (opairB (𝓜.D.child k) (𝓜.D.child p.2)) Fabs := by
        have hmeet : sn ≤
            a ⊓ lamDKVal V K (.abs x P) ⊓
              memB (opairB
                (interpDKBodyGraph 𝓜 V K hK hV
                  (η.update hV 𝓜.total y k) x P)
                (𝓜.D.child p.2)) 𝓜.Lam :=
          le_inf (hsnK.trans (hskW.trans (hswS.trans (hsT.trans htB)))) hLamn
        exact ((interpDKBodyGraph_abs_mem_eq_lam 𝓜 V K hK hV η y x P a
            hInner hInnerRows k p.2).symm.le.trans' hmeet).trans
          inf_le_right
      have hFabsz : sn ≤ memB (opairB (𝓜.D.child k) z) Fabs :=
        (memB_opairB_congr Fabs (𝓜.D.child k) (𝓜.D.child k)
            (𝓜.D.child p.2) z).trans' <|
          le_inf (le_inf
              (le_top.trans (eqB_self (A := A) (𝓜.D.child k)).ge)
              (hzn.trans_eq (eqB_comm z (𝓜.D.child p.2))))
            hFabsn
      have hkS : sn ≤ memB (𝓜.D.child k) S :=
        (memB_eqB_left w S (𝓜.D.child k)).trans' <|
          le_inf (hsnK.trans (hskW.trans hwS))
            (hsnK.trans hwk)
      have hupper : sn ≤
          (memB (𝓜.D.child k) S ⊓
            memB (opairB (𝓜.D.child k) z) Fabs ⇨
              relB 𝓜.R z c) :=
        (iInf_le (fun z' : AName A =>
            memB (𝓜.D.child k) S ⊓
              memB (opairB (𝓜.D.child k) z') Fabs ⇨
                relB 𝓜.R z' c) z).trans' <|
          (iInf_le (fun w' : AName A =>
              ⨅ z' : AName A,
                memB w' S ⊓ memB (opairB w' z') Fabs ⇨
                  relB 𝓜.R z' c) (𝓜.D.child k)).trans'
            (hsnK.trans (hskW.trans (hswS.trans (hsT.trans htUpper))))
      exact (le_himp_iff.mp hupper).trans' <|
        le_inf le_rfl (le_inf hkS hFabsz)
    have hpc : s ≤ relB 𝓜.R (𝓜.D.child p.2) c :=
      (isSupRelB_least (𝓜.D.child p.2)
          (graphImageB 𝓜.Lam (graphImageB Fg S 𝓜.C) 𝓜.D)
          𝓜.R c).trans' <|
        le_inf (hLamImg.trans inf_le_right) hcub
    exact (relB_congr 𝓜.R (𝓜.D.child p.2) v c c).trans' <|
      le_inf (le_inf
          (hvp.trans_eq (eqB_comm v (𝓜.D.child p.2)))
          (le_top.trans (eqB_self (A := A) c).ge))
        hpc

/-- Off-diagonal Scott continuity of the abs body graph. -/
theorem interpDKBodyGraph_abs_le_scottContinuous_ne
    (𝓜 : InternalReflexiveModel (A := A))
    (V K : AName.{u} A) (hK : subsetB K 𝓜.D = ⊤)
    (hV : (oid V).IsTotal)
    (η : RelFun (oid V) (oid 𝓜.D))
    (y x : V.idx) (P : LamDK V.idx K.idx) (a : A)
    (hInner : ∀ d, a ≤ isScottContinuousB
      (interpDKBodyGraph 𝓜 V K hK hV (η.update hV 𝓜.total y d) x P)
      𝓜.D 𝓜.D 𝓜.R 𝓜.R)
    (hInnerRows : ∀ d, ∀ e, IsRelElementAt 𝓜.D a
      (interpDKRelVal 𝓜 V K hK hV
        ((η.update hV 𝓜.total y d).update hV 𝓜.total x e) P))
    (hOuter : ∀ z, a ≤ isScottContinuousB
      (interpDKBodyGraph 𝓜 V K hK hV (η.update hV 𝓜.total x z) y P)
      𝓜.D 𝓜.D 𝓜.R 𝓜.R)
    (hOuterRows : ∀ z, ∀ d, IsRelElementAt 𝓜.D a
      (interpDKRelVal 𝓜 V K hK hV
        ((η.update hV 𝓜.total x z).update hV 𝓜.total y d) P)) :
    ((oid V).eq x y)ᶜ ⊓ a ⊓ lamDKVal V K (.abs x P) ≤
      isScottContinuousB
        (interpDKBodyGraph 𝓜 V K hK hV η y (.abs x P))
        𝓜.D 𝓜.D 𝓜.R 𝓜.R := by
  unfold isScottContinuousB
  refine le_inf (le_inf ?_ ?_) ?_
  · exact (le_inf (inf_le_left.trans inf_le_right) inf_le_right).trans
      (interpDKBodyGraph_abs_le_isFunctionB 𝓜 V K hK hV η y x P a
        hInner hInnerRows)
  · refine le_iInf fun u => le_iInf fun u' =>
      le_iInf fun v => le_iInf fun v' => ?_
    rw [le_himp_iff]
    exact (interpDKBodyGraph_abs_apply_mono 𝓜 V K hK hV η y x P a
        hInner hOuter hInnerRows hOuterRows u u' v v').trans' <|
      le_inf (le_inf (le_inf inf_le_left
          (inf_le_right.trans (inf_le_left.trans inf_le_left)))
        (inf_le_right.trans (inf_le_left.trans inf_le_right)))
        (inf_le_right.trans inf_le_right)
  · refine le_iInf fun S => le_iInf fun u => le_iInf fun v => ?_
    rw [le_himp_iff]
    exact (interpDKBodyGraph_abs_mapsToSup 𝓜 V K hK hV η y x P a
        hInner hOuter hInnerRows hOuterRows S u v).trans' <|
      le_inf (le_inf (le_inf inf_le_left
          (inf_le_right.trans (inf_le_left.trans inf_le_left)))
        (inf_le_right.trans (inf_le_left.trans inf_le_right)))
        (inf_le_right.trans inf_le_right)

/-- Degree-local Scott continuity of an abstraction body graph. -/
theorem interpDKBodyGraph_abs_le_scottContinuous
    (𝓜 : InternalReflexiveModel (A := A))
    (V K : AName.{u} A) (hK : subsetB K 𝓜.D = ⊤)
    (hV : (oid V).IsTotal)
    (η : RelFun (oid V) (oid 𝓜.D))
    (y x : V.idx) (P : LamDK V.idx K.idx) (a : A)
    (hInner : ∀ d, a ≤ isScottContinuousB
      (interpDKBodyGraph 𝓜 V K hK hV (η.update hV 𝓜.total y d) x P)
      𝓜.D 𝓜.D 𝓜.R 𝓜.R)
    (hInnerRows : ∀ d, ∀ e, IsRelElementAt 𝓜.D a
      (interpDKRelVal 𝓜 V K hK hV
        ((η.update hV 𝓜.total y d).update hV 𝓜.total x e) P))
    (hOuter : ∀ z, a ≤ isScottContinuousB
      (interpDKBodyGraph 𝓜 V K hK hV (η.update hV 𝓜.total x z) y P)
      𝓜.D 𝓜.D 𝓜.R 𝓜.R)
    (hOuterRows : ∀ z, ∀ d, IsRelElementAt 𝓜.D a
      (interpDKRelVal 𝓜 V K hK hV
        ((η.update hV 𝓜.total x z).update hV 𝓜.total y d) P)) :
    a ⊓ memB (V.child x) V ⊓ lamDKVal V K P ≤
      isScottContinuousB
        (interpDKBodyGraph 𝓜 V K hK hV η y (.abs x P))
        𝓜.D 𝓜.D 𝓜.R 𝓜.R := by
  have hdeg : a ⊓ memB (V.child x) V ⊓ lamDKVal V K P =
      a ⊓ lamDKVal V K (.abs x P) :=
    inf_assoc a (memB (V.child x) V) (lamDKVal V K P)
  rw [hdeg]
  refine le_of_compl_cover (p := (oid V).eq x y) ?_ ?_
  · exact (interpDKBodyGraph_abs_le_scottContinuous_eq 𝓜 V K hK hV η y x P a
        hInner hInnerRows).trans' <|
      le_inf (le_inf inf_le_right (inf_le_left.trans inf_le_left))
        (inf_le_left.trans inf_le_right)
  · exact (interpDKBodyGraph_abs_le_scottContinuous_ne 𝓜 V K hK hV η y x P a
        hInner hInnerRows hOuter hOuterRows).trans' <|
      le_inf (le_inf inf_le_right (inf_le_left.trans inf_le_left))
        (inf_le_left.trans inf_le_right)


end Scott2026
