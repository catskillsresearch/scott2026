/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/

import Scott2026.LambdaModels.DomainTheory.InternalEvalComplete.interpDKAbsFamilyGraph
import Scott2026.LambdaModels.DomainTheory.InternalEvalComplete.Proofs.CoreContContContCont

namespace Scott2026

universe u

open AName InternalReflexiveModel

variable {A : Type u} [CompleteBooleanAlgebra A]

theorem interpDKBodyGraph_abs_apply_mono
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
    (u u' v v' : AName.{u} A) :
    ((oid V).eq x y)ᶜ ⊓ a ⊓ lamDKVal V K (.abs x P) ⊓
        memB (opairB u v)
          (interpDKBodyGraph 𝓜 V K hK hV η y (.abs x P)) ⊓
        memB (opairB u' v')
          (interpDKBodyGraph 𝓜 V K hK hV η y (.abs x P)) ⊓
        relB 𝓜.R u u' ≤
      relB 𝓜.R v v' := by
  let Fabs := interpDKBodyGraph 𝓜 V K hK hV η y (.abs x P)
  let b := a ⊓ lamDKVal V K (.abs x P)
  have hfun : b ≤ isFunctionB Fabs 𝓜.D 𝓜.D :=
    interpDKBodyGraph_abs_le_isFunctionB 𝓜 V K hK hV η y x P a
      hInner hInnerRows
  have hrows :=
    interpDKBodyGraph_abs_rows_isRelElementAt 𝓜 V K hK hV η y x P a
      hInner hInnerRows
  let t :=
    ((oid V).eq x y)ᶜ ⊓ a ⊓ lamDKVal V K (.abs x P) ⊓
      memB (opairB u v) Fabs ⊓ memB (opairB u' v') Fabs ⊓
      relB 𝓜.R u u'
  change t ≤ relB 𝓜.R v v'
  have htEq : t ≤ ((oid V).eq x y)ᶜ :=
    inf_le_left.trans (inf_le_left.trans
      (inf_le_left.trans (inf_le_left.trans inf_le_left)))
  have htA : t ≤ a :=
    inf_le_left.trans (inf_le_left.trans
      (inf_le_left.trans (inf_le_left.trans inf_le_right)))
  have htLam : t ≤ lamDKVal V K (.abs x P) :=
    inf_le_left.trans (inf_le_left.trans
      (inf_le_left.trans inf_le_right))
  have htB : t ≤ b := le_inf htA htLam
  have htuv : t ≤ memB (opairB u v) Fabs :=
    inf_le_left.trans (inf_le_left.trans inf_le_right)
  have htu'v' : t ≤ memB (opairB u' v') Fabs :=
    inf_le_left.trans inf_le_right
  have htR : t ≤ relB 𝓜.R u u' := inf_le_right
  have hdec :
      t ≤ ⨆ p : 𝓜.D.idx × 𝓜.D.idx,
        eqB (opairB u v)
          (opairB (𝓜.D.child p.1) (𝓜.D.child p.2)) ⊓
        memB (opairB (𝓜.D.child p.1) (𝓜.D.child p.2)) Fabs :=
    (inf_memB_le_iSup_matrix (hsub := (htB.trans hfun).trans
        (inf_le_left.trans inf_le_left)) (opairB u v)).trans' <|
      le_inf le_rfl htuv
  have hdec' :
      t ≤ ⨆ q : 𝓜.D.idx × 𝓜.D.idx,
        eqB (opairB u' v')
          (opairB (𝓜.D.child q.1) (𝓜.D.child q.2)) ⊓
        memB (opairB (𝓜.D.child q.1) (𝓜.D.child q.2)) Fabs :=
    (inf_memB_le_iSup_matrix (hsub := (htB.trans hfun).trans
        (inf_le_left.trans inf_le_left)) (opairB u' v')).trans' <|
      le_inf le_rfl htu'v'
  refine (le_inf (le_inf le_rfl hdec) hdec').trans ?_
  rw [inf_iSup_eq (α := A)]
  refine iSup_le fun q => ?_
  rw [inf_right_comm, inf_iSup_eq (α := A)]
  refine iSup_le fun p => ?_
  let s :=
    t ⊓
      (eqB (opairB u' v')
        (opairB (𝓜.D.child q.1) (𝓜.D.child q.2)) ⊓
        memB (opairB (𝓜.D.child q.1) (𝓜.D.child q.2)) Fabs) ⊓
      (eqB (opairB u v)
        (opairB (𝓜.D.child p.1) (𝓜.D.child p.2)) ⊓
        memB (opairB (𝓜.D.child p.1) (𝓜.D.child p.2)) Fabs)
  change s ≤ relB 𝓜.R v v'
  have hsT : s ≤ t := inf_le_left.trans inf_le_left
  have hsp : s ≤
      memB (opairB (𝓜.D.child p.1) (𝓜.D.child p.2)) Fabs :=
    inf_le_right.trans inf_le_right
  have hsq : s ≤
      memB (opairB (𝓜.D.child q.1) (𝓜.D.child q.2)) Fabs :=
    inf_le_left.trans (inf_le_right.trans inf_le_right)
  have hop : s ≤
      eqB (opairB u v)
        (opairB (𝓜.D.child p.1) (𝓜.D.child p.2)) :=
    inf_le_right.trans inf_le_left
  have hoq : s ≤
      eqB (opairB u' v')
        (opairB (𝓜.D.child q.1) (𝓜.D.child q.2)) :=
    inf_le_left.trans (inf_le_right.trans inf_le_left)
  have hup : s ≤ eqB u (𝓜.D.child p.1) := by
    rw [eqB_opairB] at hop
    exact hop.trans inf_le_left
  have huq : s ≤ eqB u' (𝓜.D.child q.1) := by
    rw [eqB_opairB] at hoq
    exact hoq.trans inf_le_left
  have hvp : s ≤ eqB v (𝓜.D.child p.2) := by
    rw [eqB_opairB] at hop
    exact hop.trans inf_le_right
  have hvq : s ≤ eqB v' (𝓜.D.child q.2) := by
    rw [eqB_opairB] at hoq
    exact hoq.trans inf_le_right
  have hRpq : s ≤ relB 𝓜.R (𝓜.D.child p.1) (𝓜.D.child q.1) :=
    (relB_congr 𝓜.R u (𝓜.D.child p.1) u' (𝓜.D.child q.1)).trans' <|
      le_inf (le_inf hup huq) (hsT.trans htR)
  have hQ : s ≤
      relB 𝓜.Q
        (interpDKBodyGraph 𝓜 V K hK hV
          (η.update hV 𝓜.total y p.1) x P)
        (interpDKBodyGraph 𝓜 V K hK hV
          (η.update hV 𝓜.total y q.1) x P) :=
    (interpDKAbsFamily_relQ 𝓜 V K hK hV η y x P a
        hInner hOuter hInnerRows hOuterRows p.1 q.1).trans' <|
      le_inf (le_inf (hsT.trans htEq) (hsT.trans htA)) hRpq
  have hmemp : s ≤
      memB (opairB
        (interpDKBodyGraph 𝓜 V K hK hV
          (η.update hV 𝓜.total y p.1) x P)
        (𝓜.D.child p.2)) 𝓜.Lam := by
    have h :=
      (interpDKBodyGraph_abs_mem_eq_lam 𝓜 V K hK hV η y x P a
          hInner hInnerRows p.1 p.2).le
    exact h.trans' (le_inf (hsT.trans htB) hsp) |>.trans inf_le_right
  have hmemq : s ≤
      memB (opairB
        (interpDKBodyGraph 𝓜 V K hK hV
          (η.update hV 𝓜.total y q.1) x P)
        (𝓜.D.child q.2)) 𝓜.Lam := by
    have h :=
      (interpDKBodyGraph_abs_mem_eq_lam 𝓜 V K hK hV η y x P a
          hInner hInnerRows q.1 q.2).le
    exact h.trans' (le_inf (hsT.trans htB) hsq) |>.trans inf_le_right
  have hLam : (⊤ : A) ≤
      isScottContinuousB 𝓜.Lam 𝓜.C 𝓜.D 𝓜.Q 𝓜.R :=
    le_top.trans 𝓜.lam_continuous.ge
  have hpq : s ≤ relB 𝓜.R (𝓜.D.child p.2) (𝓜.D.child q.2) :=
    (scottContinuous_apply_mono hLam
        (interpDKBodyGraph 𝓜 V K hK hV
          (η.update hV 𝓜.total y p.1) x P)
        (interpDKBodyGraph 𝓜 V K hK hV
          (η.update hV 𝓜.total y q.1) x P)
        (𝓜.D.child p.2) (𝓜.D.child q.2)).trans' <|
      le_inf (le_inf (le_inf (le_top.trans le_top) hmemp) hmemq) hQ
  exact (relB_congr 𝓜.R (𝓜.D.child p.2) v (𝓜.D.child q.2) v').trans' <|
    le_inf (le_inf
        (hvp.trans_eq (eqB_comm v (𝓜.D.child p.2)))
        (hvq.trans_eq (eqB_comm v' (𝓜.D.child q.2))))
      hpq

/-- Inner body graphs respect equality of the outer argument. -/
theorem interpDKAbsFamily_eqB_of_arg
    (𝓜 : InternalReflexiveModel (A := A))
    (V K : AName.{u} A) (hK : subsetB K 𝓜.D = ⊤)
    (hV : (oid V).IsTotal)
    (η : RelFun (oid V) (oid 𝓜.D))
    (y x : V.idx) (d d' : 𝓜.D.idx) (P : LamDK V.idx K.idx) :
    (oid 𝓜.D).eq d d' ≤
      eqB (interpDKBodyGraph 𝓜 V K hK hV (η.update hV 𝓜.total y d) x P)
        (interpDKBodyGraph 𝓜 V K hK hV
          (η.update hV 𝓜.total y d') x P) := by
  let body (w : 𝓜.D.idx) :=
    interpDKBodyGraph 𝓜 V K hK hV (η.update hV 𝓜.total y w) x P
  have hη : RelFun.IsPointwiseFamily (oid 𝓜.D)
      (fun w => η.update hV 𝓜.total y w) :=
    RelFun.isPointwiseFamily_update η hV 𝓜.total y
  have htransport : ∀ w₁ w₂ p, (oid 𝓜.D).eq w₁ w₂ ⊓
      (body w₁).val p ≤ (body w₂).val p := by
    intro w₁ w₂ p
    let replacement : 𝓜.D.idx → 𝓜.D.idx := fun _ => p.1
    have hrepl : APoset.Functional (oid 𝓜.D) (oid 𝓜.D) replacement := by
      intro z₁ z₂
      change (oid 𝓜.D).eq z₁ z₂ ≤ (oid 𝓜.D).eps p.1
      rw [𝓜.total p.1]
      exact le_top
    have hupd := hη.update hV 𝓜.total x replacement hrepl
    exact interpDKRelVal_isPointwiseFamily 𝓜 V K hK hV
      (oid 𝓜.D) (fun w => (η.update hV 𝓜.total y w).update hV 𝓜.total x p.1)
      hupd P w₁ w₂ p.2
  exact le_eqB_mk_of_le_val
    (fun p : 𝓜.D.idx × 𝓜.D.idx =>
      opairB (𝓜.D.child p.1) (𝓜.D.child p.2))
    (body d).val (body d').val ((oid 𝓜.D).eq d d')
    (fun p => htransport d d' p)
    (fun p => by
      have h := htransport d' d p
      rwa [(oid 𝓜.D).symm d' d] at h)

/-- The graph of the inner family `d ↦ ⟦P⟧ρ[y:=d]` as a map `D → C`. -/
theorem memB_interpDKAbsFamilyGraph
    (𝓜 : InternalReflexiveModel (A := A))
    (V K : AName.{u} A) (hK : subsetB K 𝓜.D = ⊤)
    (hV : (oid V).IsTotal)
    (η : RelFun (oid V) (oid 𝓜.D))
    (y x : V.idx) (P : LamDK V.idx K.idx)
    (u G : AName.{u} A) :
    memB (opairB u G)
        (interpDKAbsFamilyGraph 𝓜 V K hK hV η y x P) =
      ⨆ d : 𝓜.D.idx,
        eqB u (𝓜.D.child d) ⊓
          eqB G
            (interpDKBodyGraph 𝓜 V K hK hV
              (η.update hV 𝓜.total y d) x P) := by
  unfold interpDKAbsFamilyGraph
  rw [memB_mk]
  refine iSup_congr fun d => ?_
  rw [eqB_opairB, inf_top_eq]

/-- Displayed family-graph edges recover the inner body graph. -/
theorem memB_interpDKAbsFamilyGraph_child
    (𝓜 : InternalReflexiveModel (A := A))
    (V K : AName.{u} A) (hK : subsetB K 𝓜.D = ⊤)
    (hV : (oid V).IsTotal)
    (η : RelFun (oid V) (oid 𝓜.D))
    (y x : V.idx) (P : LamDK V.idx K.idx) (d : 𝓜.D.idx) :
    memB (opairB (𝓜.D.child d)
        (interpDKBodyGraph 𝓜 V K hK hV (η.update hV 𝓜.total y d) x P))
      (interpDKAbsFamilyGraph 𝓜 V K hK hV η y x P) = ⊤ := by
  rw [memB_interpDKAbsFamilyGraph]
  refine top_unique (le_iSup_of_le d ?_)
  rw [eqB_self, eqB_self, top_inf_eq]

/-- The inner family graph is a degree-local function `D → C`. -/
theorem interpDKAbsFamilyGraph_le_isFunctionB
    (𝓜 : InternalReflexiveModel (A := A))
    (V K : AName.{u} A) (hK : subsetB K 𝓜.D = ⊤)
    (hV : (oid V).IsTotal)
    (η : RelFun (oid V) (oid 𝓜.D))
    (y x : V.idx) (P : LamDK V.idx K.idx) (a : A)
    (hInner : ∀ d, a ≤ isScottContinuousB
      (interpDKBodyGraph 𝓜 V K hK hV (η.update hV 𝓜.total y d) x P)
      𝓜.D 𝓜.D 𝓜.R 𝓜.R) :
    a ≤ isFunctionB
      (interpDKAbsFamilyGraph 𝓜 V K hK hV η y x P) 𝓜.D 𝓜.C := by
  let Fg := interpDKAbsFamilyGraph 𝓜 V K hK hV η y x P
  unfold isFunctionB
  refine le_inf (le_inf ?_ ?_) ?_
  · unfold interpDKAbsFamilyGraph
    rw [subsetB_mk]
    refine le_iInf fun d => ?_
    rw [le_himp_iff, memB_opairB_prodB]
    have hD : memB (𝓜.D.child d) 𝓜.D = ⊤ := by
      rw [← oid_eps]
      exact 𝓜.total d
    rw [hD, top_inf_eq]
    exact inf_le_left.trans
      (interpDKAbsFamily_mem_mapSpace 𝓜 V K hK hV η y x P a hInner d)
  · refine le_iInf fun u => le_iInf fun G => le_iInf fun G' => ?_
    rw [le_himp_iff]
    let t0 :=
      a ⊓
        (memB (opairB u G)
          (interpDKAbsFamilyGraph 𝓜 V K hK hV η y x P) ⊓
        memB (opairB u G')
          (interpDKAbsFamilyGraph 𝓜 V K hK hV η y x P))
    change t0 ≤ eqB G G'
    have hdec :
        t0 ≤ ⨆ d : 𝓜.D.idx,
          eqB u (𝓜.D.child d) ⊓
            eqB G
              (interpDKBodyGraph 𝓜 V K hK hV
                (η.update hV 𝓜.total y d) x P) :=
      (inf_le_right.trans inf_le_left).trans_eq
        (memB_interpDKAbsFamilyGraph 𝓜 V K hK hV η y x P u G)
    have hdec' :
        t0 ≤ ⨆ d' : 𝓜.D.idx,
          eqB u (𝓜.D.child d') ⊓
            eqB G'
              (interpDKBodyGraph 𝓜 V K hK hV
                (η.update hV 𝓜.total y d') x P) :=
      (inf_le_right.trans inf_le_right).trans_eq
        (memB_interpDKAbsFamilyGraph 𝓜 V K hK hV η y x P u G')
    refine (le_inf (le_inf le_rfl hdec) hdec').trans ?_
    rw [inf_iSup_eq (α := A)]
    refine iSup_le fun d' => ?_
    rw [inf_right_comm, inf_iSup_eq (α := A)]
    refine iSup_le fun d => ?_
    let t :=
      t0 ⊓
        (eqB u (𝓜.D.child d') ⊓
          eqB G'
            (interpDKBodyGraph 𝓜 V K hK hV
              (η.update hV 𝓜.total y d') x P)) ⊓
        (eqB u (𝓜.D.child d) ⊓
          eqB G
            (interpDKBodyGraph 𝓜 V K hK hV
              (η.update hV 𝓜.total y d) x P))
    change t ≤ eqB G G'
    have hdd' : t ≤ (oid 𝓜.D).eq d d' := by
      rw [oid_eq_of_total 𝓜.D 𝓜.total]
      exact (eqB_trans (𝓜.D.child d) u (𝓜.D.child d')).trans' <|
        le_inf (by
            rw [eqB_comm]
            exact inf_le_right.trans inf_le_left)
          (inf_le_left.trans (inf_le_right.trans inf_le_left))
    have hbody :=
      interpDKAbsFamily_eqB_of_arg 𝓜 V K hK hV η y x d d' P
    have hGG' : t ≤
        eqB
          (interpDKBodyGraph 𝓜 V K hK hV
            (η.update hV 𝓜.total y d) x P)
          (interpDKBodyGraph 𝓜 V K hK hV
            (η.update hV 𝓜.total y d') x P) :=
      hdd'.trans hbody
    exact (eqB_trans G
        (interpDKBodyGraph 𝓜 V K hK hV
          (η.update hV 𝓜.total y d) x P) G').trans' <|
      le_inf (inf_le_right.trans inf_le_right)
        ((eqB_trans
            (interpDKBodyGraph 𝓜 V K hK hV
              (η.update hV 𝓜.total y d) x P)
            (interpDKBodyGraph 𝓜 V K hK hV
              (η.update hV 𝓜.total y d') x P)
            G').trans' <|
          le_inf hGG'
            (by
              rw [eqB_comm]
              exact inf_le_left.trans (inf_le_right.trans inf_le_right)))
  · refine le_iInf fun u => ?_
    rw [le_himp_iff]
    have hfunD : a ⊓ memB u 𝓜.D ≤
        ⨆ d : 𝓜.D.idx, eqB u (𝓜.D.child d) := by
      rw [memB_eq (x := u) (y := 𝓜.D), inf_iSup_eq]
      refine iSup_le fun d => le_iSup_of_le d ?_
      exact inf_le_right.trans inf_le_left
    refine (le_inf le_rfl hfunD).trans ?_
    rw [inf_iSup_eq (α := A)]
    refine iSup_le fun d => le_iSup_of_le
        (interpDKBodyGraph 𝓜 V K hK hV
          (η.update hV 𝓜.total y d) x P) ?_
    rw [memB_interpDKAbsFamilyGraph]
    refine le_iSup_of_le d ?_
    exact le_inf inf_le_right
      (le_top.trans
        (eqB_self (A := A)
          (interpDKBodyGraph 𝓜 V K hK hV
            (η.update hV 𝓜.total y d) x P)).ge)

/-- Off-diagonal, the inner family graph is `Q`-monotone. -/
theorem interpDKAbsFamilyGraph_apply_mono
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
    (u u' G G' : AName.{u} A) :
    ((oid V).eq x y)ᶜ ⊓ a ⊓
        memB (opairB u G)
          (interpDKAbsFamilyGraph 𝓜 V K hK hV η y x P) ⊓
        memB (opairB u' G')
          (interpDKAbsFamilyGraph 𝓜 V K hK hV η y x P) ⊓
        relB 𝓜.R u u' ≤
      relB 𝓜.Q G G' := by
  let t0 :=
    ((oid V).eq x y)ᶜ ⊓ a ⊓
      memB (opairB u G)
        (interpDKAbsFamilyGraph 𝓜 V K hK hV η y x P) ⊓
      memB (opairB u' G')
        (interpDKAbsFamilyGraph 𝓜 V K hK hV η y x P) ⊓
      relB 𝓜.R u u'
  change t0 ≤ relB 𝓜.Q G G'
  have htEq : t0 ≤ ((oid V).eq x y)ᶜ :=
    inf_le_left.trans (inf_le_left.trans
      (inf_le_left.trans inf_le_left))
  have htA : t0 ≤ a :=
    inf_le_left.trans (inf_le_left.trans
      (inf_le_left.trans inf_le_right))
  have htR : t0 ≤ relB 𝓜.R u u' := inf_le_right
  have hdec :
      t0 ≤ ⨆ d : 𝓜.D.idx,
        eqB u (𝓜.D.child d) ⊓
          eqB G
            (interpDKBodyGraph 𝓜 V K hK hV
              (η.update hV 𝓜.total y d) x P) :=
    (inf_le_left.trans (inf_le_left.trans inf_le_right)).trans_eq
      (memB_interpDKAbsFamilyGraph 𝓜 V K hK hV η y x P u G)
  have hdec' :
      t0 ≤ ⨆ d' : 𝓜.D.idx,
        eqB u' (𝓜.D.child d') ⊓
          eqB G'
            (interpDKBodyGraph 𝓜 V K hK hV
              (η.update hV 𝓜.total y d') x P) :=
    (inf_le_left.trans inf_le_right).trans_eq
      (memB_interpDKAbsFamilyGraph 𝓜 V K hK hV η y x P u' G')
  refine (le_inf (le_inf le_rfl hdec) hdec').trans ?_
  rw [inf_iSup_eq (α := A)]
  refine iSup_le fun d' => ?_
  rw [inf_right_comm, inf_iSup_eq (α := A)]
  refine iSup_le fun d => ?_
  let s :=
    t0 ⊓
      (eqB u' (𝓜.D.child d') ⊓
        eqB G'
          (interpDKBodyGraph 𝓜 V K hK hV
            (η.update hV 𝓜.total y d') x P)) ⊓
      (eqB u (𝓜.D.child d) ⊓
        eqB G
          (interpDKBodyGraph 𝓜 V K hK hV
            (η.update hV 𝓜.total y d) x P))
  change s ≤ relB 𝓜.Q G G'
  have hsT : s ≤ t0 := inf_le_left.trans inf_le_left
  have hup : s ≤ eqB u (𝓜.D.child d) :=
    inf_le_right.trans inf_le_left
  have huq : s ≤ eqB u' (𝓜.D.child d') :=
    inf_le_left.trans (inf_le_right.trans inf_le_left)
  have hGp : s ≤
      eqB G
        (interpDKBodyGraph 𝓜 V K hK hV
          (η.update hV 𝓜.total y d) x P) :=
    inf_le_right.trans inf_le_right
  have hGq : s ≤
      eqB G'
        (interpDKBodyGraph 𝓜 V K hK hV
          (η.update hV 𝓜.total y d') x P) :=
    inf_le_left.trans (inf_le_right.trans inf_le_right)
  have hRpq : s ≤ relB 𝓜.R (𝓜.D.child d) (𝓜.D.child d') :=
    (relB_congr 𝓜.R u (𝓜.D.child d) u' (𝓜.D.child d')).trans' <|
      le_inf (le_inf hup huq) (hsT.trans htR)
  have hQ : s ≤
      relB 𝓜.Q
        (interpDKBodyGraph 𝓜 V K hK hV
          (η.update hV 𝓜.total y d) x P)
        (interpDKBodyGraph 𝓜 V K hK hV
          (η.update hV 𝓜.total y d') x P) :=
    (interpDKAbsFamily_relQ 𝓜 V K hK hV η y x P a
        hInner hOuter hInnerRows hOuterRows d d').trans' <|
      le_inf (le_inf (hsT.trans htEq) (hsT.trans htA)) hRpq
  exact (relB_congr 𝓜.Q
      (interpDKBodyGraph 𝓜 V K hK hV
        (η.update hV 𝓜.total y d) x P) G
      (interpDKBodyGraph 𝓜 V K hK hV
        (η.update hV 𝓜.total y d') x P) G').trans' <|
    le_inf (le_inf
        (hGp.trans_eq (eqB_comm G
          (interpDKBodyGraph 𝓜 V K hK hV
            (η.update hV 𝓜.total y d) x P)))
        (hGq.trans_eq (eqB_comm G'
          (interpDKBodyGraph 𝓜 V K hK hV
            (η.update hV 𝓜.total y d') x P))))
      hQ

end Scott2026
