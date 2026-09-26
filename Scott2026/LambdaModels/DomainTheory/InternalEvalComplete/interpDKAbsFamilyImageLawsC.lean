/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/

import Scott2026.LambdaModels.DomainTheory.InternalEvalComplete.interpDKAbsFamilyImageLawsB

namespace Scott2026

universe u

open AName InternalReflexiveModel

variable {A : Type u} [CompleteBooleanAlgebra A]
theorem interpDKAbsFamily_image_least
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
    (S : AName.{u} A) (d : 𝓜.D.idx) (G : AName.{u} A) :
    ((oid V).eq x y)ᶜ ⊓ a ⊓
        isDirectedRelB S 𝓜.D 𝓜.R ⊓
        isSupRelB (𝓜.D.child d) S 𝓜.R ⊓
        isUpperBoundRelB G
          (graphImageB
            (interpDKAbsFamilyGraph 𝓜 V K hK hV η y x P) S 𝓜.C)
          𝓜.Q ≤
      relB 𝓜.Q
        (interpDKBodyGraph 𝓜 V K hK hV (η.update hV 𝓜.total y d) x P)
        G := by
  let Fg := interpDKAbsFamilyGraph 𝓜 V K hK hV η y x P
  let Fd :=
    interpDKBodyGraph 𝓜 V K hK hV (η.update hV 𝓜.total y d) x P
  let Img := graphImageB Fg S 𝓜.C
  let t :=
    ((oid V).eq x y)ᶜ ⊓ a ⊓
      isDirectedRelB S 𝓜.D 𝓜.R ⊓
      isSupRelB (𝓜.D.child d) S 𝓜.R ⊓
      isUpperBoundRelB G Img 𝓜.Q
  change t ≤ relB 𝓜.Q Fd G
  have htEq : t ≤ ((oid V).eq x y)ᶜ :=
    inf_le_left.trans (inf_le_left.trans
      (inf_le_left.trans inf_le_left))
  have htA : t ≤ a :=
    inf_le_left.trans (inf_le_left.trans
      (inf_le_left.trans inf_le_right))
  have htDir : t ≤ isDirectedRelB S 𝓜.D 𝓜.R :=
    inf_le_left.trans (inf_le_left.trans inf_le_right)
  have htSup : t ≤ isSupRelB (𝓜.D.child d) S 𝓜.R :=
    inf_le_left.trans inf_le_right
  have htUb : t ≤ isUpperBoundRelB G Img 𝓜.Q := inf_le_right
  have hImgDir : t ≤ isDirectedRelB Img 𝓜.C 𝓜.Q :=
    (interpDKAbsFamilyGraph_image_directed 𝓜 V K hK hV η y x P a
        hInner hOuter hInnerRows hOuterRows S).trans' <|
      le_inf (le_inf htEq htA) htDir
  have hFC : t ≤ memB Fd 𝓜.C :=
    htA.trans (interpDKAbsFamily_mem_mapSpace 𝓜 V K hK hV η y x P a
      hInner d)
  have hGC : t ≤ memB G 𝓜.C :=
    (𝓜.isUpperBoundRelB_le_mem_mapSpace G Img).trans' <|
      le_inf (hImgDir.trans (isDirectedRelB_nonempty Img 𝓜.C 𝓜.Q))
        htUb
  have hfunG : t ≤ isFunctionB G 𝓜.D 𝓜.D :=
    (𝓜.mem_mapSpace_le_function G).trans' hGC
  have hsubG : t ≤ subsetB G (prodB 𝓜.D 𝓜.D) :=
    hfunG.trans (inf_le_left.trans inf_le_left)
  have hfunF : t ≤ isFunctionB Fd 𝓜.D 𝓜.D :=
    (𝓜.mem_mapSpace_le_function Fd).trans' hFC
  have hsubF : t ≤ subsetB Fd (prodB 𝓜.D 𝓜.D) :=
    hfunF.trans (inf_le_left.trans inf_le_left)
  have hpw : t ≤ pointwiseLeB Fd G 𝓜.D 𝓜.R := by
    unfold pointwiseLeB
    refine le_iInf fun s => le_iInf fun v => le_iInf fun v' => ?_
    rw [le_himp_iff]
    let u :=
      t ⊓ (memB s 𝓜.D ⊓ memB (opairB s v) Fd ⊓ memB (opairB s v') G)
    change u ≤ relB 𝓜.R v v'
    have huT : u ≤ t := inf_le_left
    have huF : u ≤ memB (opairB s v) Fd :=
      inf_le_right.trans (inf_le_left.trans inf_le_right)
    have huG : u ≤ memB (opairB s v') G :=
      inf_le_right.trans inf_le_right
    have hdec :
        u ≤ ⨆ p : 𝓜.D.idx × 𝓜.D.idx,
          eqB (opairB s v)
            (opairB (𝓜.D.child p.1) (𝓜.D.child p.2)) ⊓
          memB (opairB (𝓜.D.child p.1) (𝓜.D.child p.2)) Fd :=
      (inf_memB_le_iSup_matrix (hsub := huT.trans hsubF)
          (opairB s v)).trans' <|
        le_inf le_rfl huF
    have hdec' :
        u ≤ ⨆ q : 𝓜.D.idx × 𝓜.D.idx,
          eqB (opairB s v')
            (opairB (𝓜.D.child q.1) (𝓜.D.child q.2)) ⊓
          memB (opairB (𝓜.D.child q.1) (𝓜.D.child q.2)) G :=
      (inf_memB_le_iSup_matrix (hsub := huT.trans hsubG)
          (opairB s v')).trans' <|
        le_inf le_rfl huG
    refine (le_inf (le_inf le_rfl hdec) hdec').trans ?_
    rw [inf_iSup_eq (α := A)]
    refine iSup_le fun q => ?_
    rw [inf_right_comm, inf_iSup_eq (α := A)]
    refine iSup_le fun p => ?_
    let r :=
      u ⊓
        (eqB (opairB s v')
          (opairB (𝓜.D.child q.1) (𝓜.D.child q.2)) ⊓
          memB (opairB (𝓜.D.child q.1) (𝓜.D.child q.2)) G) ⊓
        (eqB (opairB s v)
          (opairB (𝓜.D.child p.1) (𝓜.D.child p.2)) ⊓
          memB (opairB (𝓜.D.child p.1) (𝓜.D.child p.2)) Fd)
    change r ≤ relB 𝓜.R v v'
    have hrU : r ≤ u := inf_le_left.trans inf_le_left
    have hrp : r ≤
        memB (opairB (𝓜.D.child p.1) (𝓜.D.child p.2)) Fd :=
      inf_le_right.trans inf_le_right
    have hrq : r ≤
        memB (opairB (𝓜.D.child q.1) (𝓜.D.child q.2)) G :=
      inf_le_left.trans (inf_le_right.trans inf_le_right)
    have hop : r ≤
        eqB (opairB s v)
          (opairB (𝓜.D.child p.1) (𝓜.D.child p.2)) :=
      inf_le_right.trans inf_le_left
    have hoq : r ≤
        eqB (opairB s v')
          (opairB (𝓜.D.child q.1) (𝓜.D.child q.2)) :=
      inf_le_left.trans (inf_le_right.trans inf_le_left)
    have hvp : r ≤ eqB v (𝓜.D.child p.2) := by
      rw [eqB_opairB] at hop
      exact hop.trans inf_le_right
    have hvq : r ≤ eqB v' (𝓜.D.child q.2) := by
      rw [eqB_opairB] at hoq
      exact hoq.trans inf_le_right
    have hsp : r ≤ eqB s (𝓜.D.child p.1) := by
      rw [eqB_opairB] at hop
      exact hop.trans inf_le_left
    have hsq : r ≤ eqB s (𝓜.D.child q.1) := by
      rw [eqB_opairB] at hoq
      exact hoq.trans inf_le_left
    have heq : r ≤ eqB (𝓜.D.child p.1) (𝓜.D.child q.1) :=
      (eqB_trans (𝓜.D.child p.1) s (𝓜.D.child q.1)).trans' <|
        le_inf (by rw [eqB_comm]; exact hsp) hsq
    have hGsame : r ≤
        memB (opairB (𝓜.D.child p.1) (𝓜.D.child q.2)) G :=
      (memB_opairB_congr G (𝓜.D.child q.1) (𝓜.D.child p.1)
          (𝓜.D.child q.2) (𝓜.D.child q.2)).trans' <|
        le_inf (le_inf
            (heq.trans_eq (eqB_comm (𝓜.D.child p.1) (𝓜.D.child q.1)))
            (le_top.trans (eqB_self (A := A) (𝓜.D.child q.2)).ge))
          hrq
    have hmts : r ≤
        mapsToSupB
          (interpDKBodyGraph 𝓜 V K hK hV
            (η.update hV 𝓜.total x p.1) y P)
          S (𝓜.D.child p.2) 𝓜.R :=
      (interpDKAbsFamily_inner_mapsToSup_outer 𝓜 V K hK hV η y x P a
          hOuter hInnerRows hOuterRows S d p.1 p.2).trans' <|
        le_inf (le_inf (le_inf (le_inf
            (hrU.trans (huT.trans htEq))
            (hrU.trans (huT.trans htA)))
          (hrU.trans (huT.trans htDir)))
          (hrU.trans (huT.trans htSup)))
          hrp
    have hub : r ≤
        isUpperBoundRelB (𝓜.D.child q.2)
          (graphImageB
            (interpDKBodyGraph 𝓜 V K hK hV
              (η.update hV 𝓜.total x p.1) y P)
            S 𝓜.D)
          𝓜.R := by
      refine le_iInf fun y₀ => ?_
      rw [le_himp_iff, memB_graphImageB]
      refine (le_inf inf_le_left (inf_le_right.trans inf_le_right)).trans ?_
      rw [inf_iSup_eq (α := A)]
      refine iSup_le fun z => ?_
      let sz :=
        r ⊓
          (memB z S ⊓
            memB (opairB z y₀)
              (interpDKBodyGraph 𝓜 V K hK hV
                (η.update hV 𝓜.total x p.1) y P))
      change sz ≤ relB 𝓜.R y₀ (𝓜.D.child q.2)
      have hszR : sz ≤ r := inf_le_left
      have hzS : sz ≤ memB z S := inf_le_right.trans inf_le_left
      have hzY : sz ≤
          memB (opairB z y₀)
            (interpDKBodyGraph 𝓜 V K hK hV
              (η.update hV 𝓜.total x p.1) y P) :=
        inf_le_right.trans inf_le_right
      have hzD : sz ≤ memB z 𝓜.D :=
        (memB_of_subsetB z S 𝓜.D).trans' <|
          le_inf hzS
            ((hszR.trans (hrU.trans (huT.trans htDir))).trans
              (isDirectedRelB_subset S 𝓜.D 𝓜.R))
      refine (le_inf le_rfl hzD).trans ?_
      rw [memB_eq (x := z) (y := 𝓜.D), inf_iSup_eq (α := A)]
      refine iSup_le fun k => ?_
      let sk :=
        sz ⊓ (eqB z (𝓜.D.child k) ⊓ 𝓜.D.val k)
      change sk ≤ relB 𝓜.R y₀ (𝓜.D.child q.2)
      have hskS : sk ≤ sz := inf_le_left
      have hzk : sk ≤ eqB z (𝓜.D.child k) :=
        inf_le_right.trans inf_le_left
      have hGe : sk ≤
          memB (opairB (𝓜.D.child k) y₀)
            (interpDKBodyGraph 𝓜 V K hK hV
              (η.update hV 𝓜.total x p.1) y P) :=
        (memB_opairB_congr
            (interpDKBodyGraph 𝓜 V K hK hV
              (η.update hV 𝓜.total x p.1) y P)
            z (𝓜.D.child k) y₀ y₀).trans' <|
          le_inf (le_inf hzk
              (le_top.trans (eqB_self (A := A) y₀).ge))
            (hskS.trans hzY)
      have hFk : sk ≤
          memB (opairB (𝓜.D.child p.1) y₀)
            (interpDKBodyGraph 𝓜 V K hK hV
              (η.update hV 𝓜.total y k) x P) :=
        (interpDKAbsFamily_outer_mem_le_inner 𝓜 V K hK hV η y x P a
            hInnerRows hOuter hOuterRows k p.1 y₀).trans' <|
          le_inf (le_inf
              (hskS.trans (hszR.trans (hrU.trans (huT.trans htEq))))
              (hskS.trans (hszR.trans (hrU.trans (huT.trans htA)))))
            hGe
      have hFkC : sk ≤
          memB (interpDKBodyGraph 𝓜 V K hK hV
              (η.update hV 𝓜.total y k) x P) 𝓜.C :=
        (hskS.trans (hszR.trans (hrU.trans (huT.trans htA)))).trans
          (interpDKAbsFamily_mem_mapSpace 𝓜 V K hK hV η y x P a
            hInner k)
      have hFkImg : sk ≤
          memB (interpDKBodyGraph 𝓜 V K hK hV
              (η.update hV 𝓜.total y k) x P) Img := by
        rw [memB_graphImageB]
        refine le_inf hFkC (le_iSup_of_le (𝓜.D.child k) ?_)
        refine le_inf ?_ ?_
        · exact (memB_eqB_left z S (𝓜.D.child k)).trans' <|
            le_inf (hskS.trans hzS) hzk
        · exact le_top.trans
            (memB_interpDKAbsFamilyGraph_child
              𝓜 V K hK hV η y x P k).ge
      have hQk : sk ≤
          relB 𝓜.Q
            (interpDKBodyGraph 𝓜 V K hK hV
              (η.update hV 𝓜.total y k) x P) G :=
        (isUpperBoundRelB_apply G Img 𝓜.Q
            (interpDKBodyGraph 𝓜 V K hK hV
              (η.update hV 𝓜.total y k) x P)).trans' <|
          le_inf (hskS.trans (hszR.trans (hrU.trans (huT.trans htUb))))
            hFkImg
      exact (𝓜.relQ_apply
          (interpDKBodyGraph 𝓜 V K hK hV
            (η.update hV 𝓜.total y k) x P)
          G (𝓜.D.child p.1) y₀ (𝓜.D.child q.2)).trans' <|
        le_inf (le_inf (le_inf hFkC
            (hskS.trans (hszR.trans (hrU.trans (huT.trans hGC)))))
          hQk)
          (le_inf (le_inf
              (le_top.trans (by
                rw [← oid_eps]
                exact (𝓜.total p.1).ge))
              hFk)
            (hskS.trans (hszR.trans hGsame)))
    have hfunGe : r ≤
        isFunctionB
          (interpDKBodyGraph 𝓜 V K hK hV
            (η.update hV 𝓜.total x p.1) y P)
          𝓜.D 𝓜.D :=
      (hrU.trans (huT.trans htA)).trans
        ((hOuter p.1).trans (inf_le_left.trans inf_le_left))
    have hisup : r ≤
        isSupRelB (𝓜.D.child p.2)
          (graphImageB
            (interpDKBodyGraph 𝓜 V K hK hV
              (η.update hV 𝓜.total x p.1) y P)
            S 𝓜.D)
          𝓜.R :=
      (mapsToSupB_le_isSup_graphImageB
          (interpDKBodyGraph 𝓜 V K hK hV
            (η.update hV 𝓜.total x p.1) y P)
          S 𝓜.D 𝓜.D 𝓜.R (𝓜.D.child p.2) hfunGe).trans' <|
        le_inf le_rfl hmts
    have hpq : r ≤ relB 𝓜.R (𝓜.D.child p.2) (𝓜.D.child q.2) :=
      (isSupRelB_least (𝓜.D.child p.2)
          (graphImageB
            (interpDKBodyGraph 𝓜 V K hK hV
              (η.update hV 𝓜.total x p.1) y P)
            S 𝓜.D)
          𝓜.R (𝓜.D.child q.2)).trans' <|
        le_inf hisup hub
    exact (relB_congr 𝓜.R (𝓜.D.child p.2) v (𝓜.D.child q.2) v').trans' <|
      le_inf (le_inf
          (hvp.trans_eq (eqB_comm v (𝓜.D.child p.2)))
          (hvq.trans_eq (eqB_comm v' (𝓜.D.child q.2))))
        hpq
  exact (𝓜.pointwise_le_relQ Fd G).trans' <|
    le_inf (le_inf hFC hGC) hpw

end Scott2026
