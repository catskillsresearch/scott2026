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
import Scott2026.LambdaModels.DomainTheory.InternalEval.Proofs.CoreCont

namespace Scott2026

universe u


open AName InternalReflexiveModel

variable {A : Type u} [CompleteBooleanAlgebra A]

/-- A generalized element transports its coefficients along target equality. -/
theorem interpDKBodyGraph_val_le
    (𝓜 : InternalReflexiveModel (A := A))
    (V K : AName.{u} A) (hK : subsetB K 𝓜.D = ⊤)
    (hV : (oid V).IsTotal)
    (η : RelFun (oid V) (oid 𝓜.D))
    (x : V.idx) (P : LamDK V.idx K.idx) (a : A)
    (hP : ∀ d, IsRelElementAt 𝓜.D a
      (interpDKRelVal 𝓜 V K hK hV
        (η.update hV 𝓜.total x d) P))
    (p : 𝓜.D.idx × 𝓜.D.idx) :
    (interpDKBodyGraph 𝓜 V K hK hV η x P).val p ≤ a :=
  (hP p.1).2.1 p.2 |>.trans inf_le_left

/-- A degree-local body graph is empty at the complementary degree. -/
theorem interpDKBodyGraph_eqB_zero
    (𝓜 : InternalReflexiveModel (A := A))
    (V K : AName.{u} A) (hK : subsetB K 𝓜.D = ⊤)
    (hV : (oid V).IsTotal)
    (η : RelFun (oid V) (oid 𝓜.D))
    (x : V.idx) (P : LamDK V.idx K.idx) (a : A)
    (hP : ∀ d, IsRelElementAt 𝓜.D a
      (interpDKRelVal 𝓜 V K hK hV
        (η.update hV 𝓜.total x d) P)) :
    aᶜ ≤ eqB (interpDKBodyGraph 𝓜 V K hK hV η x P)
      (zeroPairGraph 𝓜.D) :=
  eqB_mk_zero_of_val_le
    (fun p : 𝓜.D.idx × 𝓜.D.idx =>
      opairB (𝓜.D.child p.1) (𝓜.D.child p.2))
    (fun p =>
      interpDKRelVal 𝓜 V K hK hV
        (η.update hV 𝓜.total x p.1) P p.2)
    a
    (interpDKBodyGraph_val_le 𝓜 V K hK hV η x P a hP)

/-- Lam applied to a degree-local body graph is supported by that degree. -/
theorem interpDKRelVal_abs_memB_le
    (𝓜 : InternalReflexiveModel (A := A))
    (V K : AName.{u} A) (hK : subsetB K 𝓜.D = ⊤)
    (hV : (oid V).IsTotal)
    (η : RelFun (oid V) (oid 𝓜.D))
    (x : V.idx) (P : LamDK V.idx K.idx) (a : A)
    (hP : ∀ d, IsRelElementAt 𝓜.D a
      (interpDKRelVal 𝓜 V K hK hV
        (η.update hV 𝓜.total x d) P))
    (d : 𝓜.D.idx) :
    memB (opairB (interpDKBodyGraph 𝓜 V K hK hV η x P)
        (𝓜.D.child d)) 𝓜.Lam ≤ a := by
  have heq :=
    interpDKBodyGraph_eqB_zero 𝓜 V K hK hV η x P a hP
  have hcongr :
      aᶜ ⊓ memB (opairB
          (interpDKBodyGraph 𝓜 V K hK hV η x P)
          (𝓜.D.child d)) 𝓜.Lam ≤
        memB (opairB (zeroPairGraph 𝓜.D) (𝓜.D.child d)) 𝓜.Lam :=
    (memB_opairB_congr 𝓜.Lam
        (interpDKBodyGraph 𝓜 V K hK hV η x P)
        (zeroPairGraph 𝓜.D)
        (𝓜.D.child d) (𝓜.D.child d)).trans' <|
      le_inf (le_inf (inf_le_left.trans heq)
          (le_top.trans (eqB_self (A := A) (𝓜.D.child d)).ge))
        inf_le_right
  have hsub : subsetB 𝓜.Lam (prodB 𝓜.C 𝓜.D) = ⊤ :=
    isFunctionB_subset 𝓜.lam_function
  have hC :
      memB (opairB (zeroPairGraph 𝓜.D) (𝓜.D.child d)) 𝓜.Lam ≤
        memB (zeroPairGraph 𝓜.D) 𝓜.C :=
    (memB_opairB_le_of_subsetB hsub
        (zeroPairGraph 𝓜.D) (𝓜.D.child d)).trans
      inf_le_left
  have : aᶜ ⊓ memB (opairB
      (interpDKBodyGraph 𝓜 V K hK hV η x P)
      (𝓜.D.child d)) 𝓜.Lam ≤ ⊥ :=
    (hcongr.trans hC).trans_eq (memB_zeroPairGraph_mapSpace 𝓜)
  have hx : memB (opairB
      (interpDKBodyGraph 𝓜 V K hK hV η x P)
      (𝓜.D.child d)) 𝓜.Lam ≤ aᶜᶜ := by
    rw [le_compl_iff_disjoint_left, disjoint_iff]
    exact le_bot_iff.mp (this.trans' (by apply le_of_eq; ac_rfl))
  rwa [compl_compl] at hx

/-- Abstraction rows are generalized elements at the meet of the body
degree and the abstraction support. -/
theorem interpDKRelVal_abs_isRelElementAt
    (𝓜 : InternalReflexiveModel (A := A))
    (V K : AName.{u} A) (hK : subsetB K 𝓜.D = ⊤)
    (hV : (oid V).IsTotal)
    (η : RelFun (oid V) (oid 𝓜.D))
    (x : V.idx) (P : LamDK V.idx K.idx) (a : A)
    (hPsc : a ≤ isScottContinuousB
      (interpDKBodyGraph 𝓜 V K hK hV η x P) 𝓜.D 𝓜.D 𝓜.R 𝓜.R)
    (hP : ∀ d, IsRelElementAt 𝓜.D a
      (interpDKRelVal 𝓜 V K hK hV
        (η.update hV 𝓜.total x d) P)) :
    IsRelElementAt 𝓜.D (a ⊓ lamDKVal V K (.abs x P))
      (interpDKRelVal 𝓜 V K hK hV η (.abs x P)) := by
  let body := interpDKBodyGraph 𝓜 V K hK hV η x P
  let r (d : 𝓜.D.idx) :=
    interpDKRelVal 𝓜 V K hK hV η (.abs x P) d
  have hsub : subsetB 𝓜.Lam (prodB 𝓜.C 𝓜.D) = ⊤ :=
    isFunctionB_subset 𝓜.lam_function
  have hbodyC : a ≤ memB body 𝓜.C :=
    hPsc.trans (𝓜.scottContinuous_le_mem_mapSpace body)
  refine ⟨?respects, ?le_eps, ?single, ?total⟩
  · intro d e
    rw [interpDKRelVal_abs, interpDKRelVal_abs]
    refine le_inf (inf_le_right.trans inf_le_left) ?_
    refine (memB_opairB_congr 𝓜.Lam body body
        (𝓜.D.child d) (𝓜.D.child e)).trans' ?_
    refine le_inf (le_inf ?_ ?_) ?_
    · exact le_top.trans (eqB_self (A := A) body).ge
    · rw [oid_eq_of_total 𝓜.D 𝓜.total]
      exact inf_le_left
    · exact inf_le_right.trans inf_le_right
  · intro d
    rw [interpDKRelVal_abs]
    refine le_inf (le_inf ?_ inf_le_left) ?_
    · exact (interpDKRelVal_abs_memB_le 𝓜 V K hK hV η x P a hP d).trans' <|
        inf_le_right
    · have heps :
          memB (opairB body (𝓜.D.child d)) 𝓜.Lam ≤
            memB (𝓜.D.child d) 𝓜.D :=
        (memB_opairB_le_of_subsetB hsub body (𝓜.D.child d)).trans
          inf_le_right
      rw [oid_eps]
      exact inf_le_right.trans heps
  · intro d e
    rw [interpDKRelVal_abs, interpDKRelVal_abs]
    have hsv :=
      isSingleValuedB_apply 𝓜.Lam body (𝓜.D.child d) (𝓜.D.child e)
    rw [isFunctionB_single 𝓜.lam_function, top_inf_eq] at hsv
    rw [oid_eq_of_total 𝓜.D 𝓜.total]
    exact hsv.trans' <|
      le_inf (inf_le_left.trans inf_le_right)
        (inf_le_right.trans inf_le_right)
  · have htot :
        memB body 𝓜.C ≤
          ⨆ y : AName A, memB (opairB body y) 𝓜.Lam :=
      (isTotalB_apply 𝓜.Lam 𝓜.C body).trans' <|
        le_inf (le_top.trans (isFunctionB_total 𝓜.lam_function).ge)
          le_rfl
    have hproj : a ≤
        ⨆ j : 𝓜.D.idx, memB (opairB body (𝓜.D.child j)) 𝓜.Lam := by
      refine (le_inf le_rfl (htot.trans' hbodyC)).trans ?_
      rw [inf_iSup_eq]
      refine iSup_le fun y =>
        inf_memB_opairB_le_iSup_child
          (hsub := le_top.trans hsub.ge) body y
    refine (le_inf inf_le_right (inf_le_left.trans hproj)).trans ?_
    rw [inf_iSup_eq]
    refine iSup_le fun j => le_iSup_of_le j ?_
    rw [interpDKRelVal_abs]

/-- Every updated abs row is a generalized element at the active degree. -/
theorem interpDKBodyGraph_abs_rows_isRelElementAt
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
        ((η.update hV 𝓜.total y d).update hV 𝓜.total x e) P)) :
    ∀ d, IsRelElementAt 𝓜.D (a ⊓ lamDKVal V K (.abs x P))
      (interpDKRelVal 𝓜 V K hK hV
        (η.update hV 𝓜.total y d) (.abs x P)) :=
  fun d =>
    interpDKRelVal_abs_isRelElementAt 𝓜 V K hK hV
      (η.update hV 𝓜.total y d) x P a (hInner d) (hInnerRows d)

/-- Rowwise abs elements make the abs body graph a degree-local function. -/
theorem interpDKBodyGraph_abs_le_isFunctionB
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
        ((η.update hV 𝓜.total y d).update hV 𝓜.total x e) P)) :
    a ⊓ lamDKVal V K (.abs x P) ≤
      isFunctionB
        (interpDKBodyGraph 𝓜 V K hK hV η y (.abs x P))
        𝓜.D 𝓜.D :=
  interpDKBodyGraph_le_isFunctionB 𝓜 V K hK hV η y (.abs x P)
    (a ⊓ lamDKVal V K (.abs x P))
    (interpDKBodyGraph_abs_rows_isRelElementAt
      𝓜 V K hK hV η y x P a hInner hInnerRows)

/-- Boolean equality of graphs transports Scott continuity at the same
degree, through the exact map space. -/
theorem InternalReflexiveModel.eqB_le_scottContinuous
    (𝓜 : InternalReflexiveModel (A := A))
    (F G : AName.{u} A) (a : A)
    (heq : a ≤ eqB F G)
    (hF : a ≤ isScottContinuousB F 𝓜.D 𝓜.D 𝓜.R 𝓜.R) :
    a ≤ isScottContinuousB G 𝓜.D 𝓜.D 𝓜.R 𝓜.R := by
  have hFC : a ≤ memB F 𝓜.C :=
    hF.trans (𝓜.scottContinuous_le_mem_mapSpace F)
  have hGC : a ≤ memB G 𝓜.C :=
    (memB_eqB_left F 𝓜.C G).trans' (le_inf hFC heq)
  exact hGC.trans (𝓜.mem_mapSpace_le_scottContinuous G)

/-- Overwriting an equal key does not change the body graph. -/
theorem interpDKBodyGraph_update_overwrite_eqB
    (𝓜 : InternalReflexiveModel (A := A))
    (V K : AName.{u} A) (hK : subsetB K 𝓜.D = ⊤)
    (hV : (oid V).IsTotal)
    (η : RelFun (oid V) (oid 𝓜.D))
    (x y : V.idx) (d : 𝓜.D.idx) (P : LamDK V.idx K.idx) :
    (oid V).eq x y ≤
      eqB (interpDKBodyGraph 𝓜 V K hK hV (η.update hV 𝓜.total y d) x P)
        (interpDKBodyGraph 𝓜 V K hK hV η x P) :=
  le_eqB_mk_of_le_val
    (fun p : 𝓜.D.idx × 𝓜.D.idx =>
      opairB (𝓜.D.child p.1) (𝓜.D.child p.2))
    (fun p =>
      interpDKRelVal 𝓜 V K hK hV
        ((η.update hV 𝓜.total y d).update hV 𝓜.total x p.1) P p.2)
    (fun p =>
      interpDKRelVal 𝓜 V K hK hV
        (η.update hV 𝓜.total x p.1) P p.2)
    ((oid V).eq x y)
    (fun p =>
      interpDKRelVal_update_overwrite 𝓜 V K hK hV η x y d p.1 P p.2)
    (fun p =>
      interpDKRelVal_update_overwrite_symm 𝓜 V K hK hV η x y d p.1 P p.2)

/-- Inner body graphs at equal keys are equal, independently of the
overwritten value. -/
theorem interpDKAbsFamily_eqB_of_eq_keys
    (𝓜 : InternalReflexiveModel (A := A))
    (V K : AName.{u} A) (hK : subsetB K 𝓜.D = ⊤)
    (hV : (oid V).IsTotal)
    (η : RelFun (oid V) (oid 𝓜.D))
    (x y : V.idx) (d d' : 𝓜.D.idx) (P : LamDK V.idx K.idx) :
    (oid V).eq x y ≤
      eqB (interpDKBodyGraph 𝓜 V K hK hV (η.update hV 𝓜.total y d) x P)
        (interpDKBodyGraph 𝓜 V K hK hV (η.update hV 𝓜.total y d') x P) := by
  have hd :=
    interpDKBodyGraph_update_overwrite_eqB 𝓜 V K hK hV η x y d P
  have hd' :=
    interpDKBodyGraph_update_overwrite_eqB 𝓜 V K hK hV η x y d' P
  exact (eqB_trans
      (interpDKBodyGraph 𝓜 V K hK hV (η.update hV 𝓜.total y d) x P)
      (interpDKBodyGraph 𝓜 V K hK hV η x P)
      (interpDKBodyGraph 𝓜 V K hK hV (η.update hV 𝓜.total y d') x P)).trans' <|
    le_inf hd (hd'.trans_eq (eqB_comm
      (interpDKBodyGraph 𝓜 V K hK hV (η.update hV 𝓜.total y d') x P)
      (interpDKBodyGraph 𝓜 V K hK hV η x P)))

/-- On the diagonal `x = y`, abs body-graph outputs coincide. -/
theorem interpDKBodyGraph_abs_apply_const
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
    (u u' v v' : AName.{u} A) :
    (oid V).eq x y ⊓ a ⊓ lamDKVal V K (.abs x P) ⊓
        memB (opairB u v)
          (interpDKBodyGraph 𝓜 V K hK hV η y (.abs x P)) ⊓
        memB (opairB u' v')
          (interpDKBodyGraph 𝓜 V K hK hV η y (.abs x P)) ≤
      eqB v v' := by
  let Fabs := interpDKBodyGraph 𝓜 V K hK hV η y (.abs x P)
  let b := a ⊓ lamDKVal V K (.abs x P)
  have hfun : b ≤ isFunctionB Fabs 𝓜.D 𝓜.D :=
    interpDKBodyGraph_abs_le_isFunctionB 𝓜 V K hK hV η y x P a
      hInner hInnerRows
  have hrows :=
    interpDKBodyGraph_abs_rows_isRelElementAt 𝓜 V K hK hV η y x P a
      hInner hInnerRows
  let t :=
    (oid V).eq x y ⊓ a ⊓ lamDKVal V K (.abs x P) ⊓
      memB (opairB u v) Fabs ⊓ memB (opairB u' v') Fabs
  change t ≤ eqB v v'
  have htEq : t ≤ (oid V).eq x y :=
    inf_le_left.trans (inf_le_left.trans (inf_le_left.trans inf_le_left))
  have htA : t ≤ a :=
    inf_le_left.trans (inf_le_left.trans (inf_le_left.trans inf_le_right))
  have htLam : t ≤ lamDKVal V K (.abs x P) :=
    inf_le_left.trans (inf_le_left.trans inf_le_right)
  have htB : t ≤ b := le_inf htA htLam
  have htuv : t ≤ memB (opairB u v) Fabs :=
    inf_le_left.trans inf_le_right
  have htu'v' : t ≤ memB (opairB u' v') Fabs :=
    inf_le_right
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
  change s ≤ eqB v v'
  have hsT : s ≤ t := inf_le_left.trans inf_le_left
  have hsp : s ≤
      memB (opairB (𝓜.D.child p.1) (𝓜.D.child p.2)) Fabs :=
    inf_le_right.trans inf_le_right
  have hsq : s ≤
      memB (opairB (𝓜.D.child q.1) (𝓜.D.child q.2)) Fabs :=
    inf_le_left.trans (inf_le_right.trans inf_le_right)
  have hvp : s ≤ eqB v (𝓜.D.child p.2) := by
    have hop : s ≤
        eqB (opairB u v)
          (opairB (𝓜.D.child p.1) (𝓜.D.child p.2)) :=
      inf_le_right.trans inf_le_left
    rw [eqB_opairB] at hop
    exact hop.trans inf_le_right
  have hvq : s ≤ eqB v' (𝓜.D.child q.2) := by
    have hop : s ≤
        eqB (opairB u' v')
          (opairB (𝓜.D.child q.1) (𝓜.D.child q.2)) :=
      inf_le_left.trans (inf_le_right.trans inf_le_left)
    rw [eqB_opairB] at hop
    exact hop.trans inf_le_right
  have hnormp :=
    (interpDKBodyGraph_mem_normalize 𝓜 V K hK hV η y (.abs x P)
      b hrows p.1 p.2).2
  have hnormq :=
    (interpDKBodyGraph_mem_normalize 𝓜 V K hK hV η y (.abs x P)
      b hrows q.1 q.2).2
  have hvalp : s ≤
      interpDKRelVal 𝓜 V K hK hV
        (η.update hV 𝓜.total y p.1) (.abs x P) p.2 :=
    hnormp.trans' (le_inf (hsT.trans htB) hsp)
  have hvalq : s ≤
      interpDKRelVal 𝓜 V K hK hV
        (η.update hV 𝓜.total y q.1) (.abs x P) q.2 :=
    hnormq.trans' (le_inf (hsT.trans htB) hsq)
  rw [interpDKRelVal_abs] at hvalp
  rw [interpDKRelVal_abs] at hvalq
  have hbodyEq :=
    interpDKAbsFamily_eqB_of_eq_keys 𝓜 V K hK hV η x y p.1 q.1 P
  have hmemp : s ≤
      memB (opairB
        (interpDKBodyGraph 𝓜 V K hK hV
          (η.update hV 𝓜.total y p.1) x P)
        (𝓜.D.child p.2)) 𝓜.Lam :=
    hvalp.trans inf_le_right
  have hmemq : s ≤
      memB (opairB
        (interpDKBodyGraph 𝓜 V K hK hV
          (η.update hV 𝓜.total y q.1) x P)
        (𝓜.D.child q.2)) 𝓜.Lam :=
    hvalq.trans inf_le_right
  have hmemq' : s ≤
      memB (opairB
        (interpDKBodyGraph 𝓜 V K hK hV
          (η.update hV 𝓜.total y p.1) x P)
        (𝓜.D.child q.2)) 𝓜.Lam :=
    (memB_opairB_congr 𝓜.Lam
        (interpDKBodyGraph 𝓜 V K hK hV
          (η.update hV 𝓜.total y q.1) x P)
        (interpDKBodyGraph 𝓜 V K hK hV
          (η.update hV 𝓜.total y p.1) x P)
        (𝓜.D.child q.2) (𝓜.D.child q.2)).trans' <|
      le_inf (le_inf
          ((hsT.trans htEq).trans hbodyEq |>.trans_eq
            (eqB_comm
              (interpDKBodyGraph 𝓜 V K hK hV
                (η.update hV 𝓜.total y p.1) x P)
              (interpDKBodyGraph 𝓜 V K hK hV
                (η.update hV 𝓜.total y q.1) x P)))
          (le_top.trans (eqB_self (A := A) (𝓜.D.child q.2)).ge))
        hmemq
  have hsv :=
    isSingleValuedB_apply 𝓜.Lam
      (interpDKBodyGraph 𝓜 V K hK hV
        (η.update hV 𝓜.total y p.1) x P)
      (𝓜.D.child p.2) (𝓜.D.child q.2)
  rw [isFunctionB_single 𝓜.lam_function, top_inf_eq] at hsv
  have hpq : s ≤ eqB (𝓜.D.child p.2) (𝓜.D.child q.2) :=
    hsv.trans' (le_inf hmemp hmemq')
  exact (eqB_trans v (𝓜.D.child p.2) v').trans' <|
    le_inf hvp <|
      (eqB_trans (𝓜.D.child p.2) (𝓜.D.child q.2) v').trans' <|
        le_inf hpq (by rw [eqB_comm]; exact hvq)

/-- Degree-local Scott continuity of the abs body graph on the diagonal. -/
theorem interpDKBodyGraph_abs_le_scottContinuous_eq
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
        ((η.update hV 𝓜.total y d).update hV 𝓜.total x e) P)) :
    (oid V).eq x y ⊓ a ⊓ lamDKVal V K (.abs x P) ≤
      isScottContinuousB
        (interpDKBodyGraph 𝓜 V K hK hV η y (.abs x P))
        𝓜.D 𝓜.D 𝓜.R 𝓜.R := by
  let Fabs := interpDKBodyGraph 𝓜 V K hK hV η y (.abs x P)
  have hfun : a ⊓ lamDKVal V K (.abs x P) ≤
      isFunctionB Fabs 𝓜.D 𝓜.D :=
    interpDKBodyGraph_abs_le_isFunctionB 𝓜 V K hK hV η y x P a
      hInner hInnerRows
  refine 𝓜.constantMap_le_scottContinuous Fabs
      ((oid V).eq x y ⊓ a ⊓ lamDKVal V K (.abs x P)) ?_ ?_
  · exact (le_inf (inf_le_left.trans inf_le_right) inf_le_right).trans hfun
  · exact interpDKBodyGraph_abs_apply_const 𝓜 V K hK hV η y x P a
      hInner hInnerRows

/-- Inner body graphs of `P` lie in the exact map space. -/
theorem interpDKAbsFamily_mem_mapSpace
    (𝓜 : InternalReflexiveModel (A := A))
    (V K : AName.{u} A) (hK : subsetB K 𝓜.D = ⊤)
    (hV : (oid V).IsTotal)
    (η : RelFun (oid V) (oid 𝓜.D))
    (y x : V.idx) (P : LamDK V.idx K.idx) (a : A)
    (hInner : ∀ d, a ≤ isScottContinuousB
      (interpDKBodyGraph 𝓜 V K hK hV (η.update hV 𝓜.total y d) x P)
      𝓜.D 𝓜.D 𝓜.R 𝓜.R)
    (d : 𝓜.D.idx) :
    a ≤ memB
        (interpDKBodyGraph 𝓜 V K hK hV (η.update hV 𝓜.total y d) x P)
        𝓜.C :=
  (hInner d).trans
    (𝓜.scottContinuous_le_mem_mapSpace
      (interpDKBodyGraph 𝓜 V K hK hV (η.update hV 𝓜.total y d) x P))

/-- Outer body graphs of `P` lie in the exact map space. -/
theorem interpDKAbsOuter_mem_mapSpace
    (𝓜 : InternalReflexiveModel (A := A))
    (V K : AName.{u} A) (hK : subsetB K 𝓜.D = ⊤)
    (hV : (oid V).IsTotal)
    (η : RelFun (oid V) (oid 𝓜.D))
    (y x : V.idx) (P : LamDK V.idx K.idx) (a : A)
    (hOuter : ∀ z, a ≤ isScottContinuousB
      (interpDKBodyGraph 𝓜 V K hK hV (η.update hV 𝓜.total x z) y P)
      𝓜.D 𝓜.D 𝓜.R 𝓜.R)
    (z : 𝓜.D.idx) :
    a ≤ memB
        (interpDKBodyGraph 𝓜 V K hK hV (η.update hV 𝓜.total x z) y P)
        𝓜.C :=
  (hOuter z).trans
    (𝓜.scottContinuous_le_mem_mapSpace
      (interpDKBodyGraph 𝓜 V K hK hV (η.update hV 𝓜.total x z) y P))

/-- Off-diagonal, an inner body-graph edge is an outer body-graph edge. -/
theorem interpDKAbsFamily_inner_le_outer
    (𝓜 : InternalReflexiveModel (A := A))
    (V K : AName.{u} A) (hK : subsetB K 𝓜.D = ⊤)
    (hV : (oid V).IsTotal)
    (η : RelFun (oid V) (oid 𝓜.D))
    (y x : V.idx) (P : LamDK V.idx K.idx) (a : A)
    (hInnerRows : ∀ d, ∀ e, IsRelElementAt 𝓜.D a
      (interpDKRelVal 𝓜 V K hK hV
        ((η.update hV 𝓜.total y d).update hV 𝓜.total x e) P))
    (hOuterRows : ∀ z, ∀ d, IsRelElementAt 𝓜.D a
      (interpDKRelVal 𝓜 V K hK hV
        ((η.update hV 𝓜.total x z).update hV 𝓜.total y d) P))
    (d e w : 𝓜.D.idx) :
    ((oid V).eq x y)ᶜ ⊓ a ⊓
        memB (opairB (𝓜.D.child e) (𝓜.D.child w))
          (interpDKBodyGraph 𝓜 V K hK hV
            (η.update hV 𝓜.total y d) x P) ≤
      memB (opairB (𝓜.D.child d) (𝓜.D.child w))
        (interpDKBodyGraph 𝓜 V K hK hV
          (η.update hV 𝓜.total x e) y P) := by
  let t :=
    ((oid V).eq x y)ᶜ ⊓ a ⊓
      memB (opairB (𝓜.D.child e) (𝓜.D.child w))
        (interpDKBodyGraph 𝓜 V K hK hV
          (η.update hV 𝓜.total y d) x P)
  change t ≤
    memB (opairB (𝓜.D.child d) (𝓜.D.child w))
      (interpDKBodyGraph 𝓜 V K hK hV
        (η.update hV 𝓜.total x e) y P)
  have htEq : t ≤ ((oid V).eq x y)ᶜ :=
    inf_le_left.trans inf_le_left
  have htA : t ≤ a := inf_le_left.trans inf_le_right
  have htmem : t ≤
      memB (opairB (𝓜.D.child e) (𝓜.D.child w))
        (interpDKBodyGraph 𝓜 V K hK hV
          (η.update hV 𝓜.total y d) x P) :=
    inf_le_right
  have hval :
      t ≤ interpDKRelVal 𝓜 V K hK hV
        ((η.update hV 𝓜.total y d).update hV 𝓜.total x e) P w :=
    (interpDKBodyGraph_mem_normalize 𝓜 V K hK hV
        (η.update hV 𝓜.total y d) x P a (hInnerRows d) e w).2.trans' <|
      le_inf htA htmem
  have hcomm :
      t ≤ interpDKRelVal 𝓜 V K hK hV
        ((η.update hV 𝓜.total x e).update hV 𝓜.total y d) P w :=
    (interpDKRelVal_update_commute 𝓜 V K hK hV η x y d e P w).trans' <|
      le_inf htEq hval
  exact (interpDKBodyGraph_mem_normalize 𝓜 V K hK hV
      (η.update hV 𝓜.total x e) y P a (hOuterRows e) d w).1.trans' hcomm

/-- The converse of `interpDKAbsFamily_inner_le_outer`. -/
theorem interpDKAbsFamily_outer_le_inner
    (𝓜 : InternalReflexiveModel (A := A))
    (V K : AName.{u} A) (hK : subsetB K 𝓜.D = ⊤)
    (hV : (oid V).IsTotal)
    (η : RelFun (oid V) (oid 𝓜.D))
    (y x : V.idx) (P : LamDK V.idx K.idx) (a : A)
    (hInnerRows : ∀ d, ∀ e, IsRelElementAt 𝓜.D a
      (interpDKRelVal 𝓜 V K hK hV
        ((η.update hV 𝓜.total y d).update hV 𝓜.total x e) P))
    (hOuterRows : ∀ z, ∀ d, IsRelElementAt 𝓜.D a
      (interpDKRelVal 𝓜 V K hK hV
        ((η.update hV 𝓜.total x z).update hV 𝓜.total y d) P))
    (d e w : 𝓜.D.idx) :
    ((oid V).eq x y)ᶜ ⊓ a ⊓
        memB (opairB (𝓜.D.child d) (𝓜.D.child w))
          (interpDKBodyGraph 𝓜 V K hK hV
            (η.update hV 𝓜.total x e) y P) ≤
      memB (opairB (𝓜.D.child e) (𝓜.D.child w))
        (interpDKBodyGraph 𝓜 V K hK hV
          (η.update hV 𝓜.total y d) x P) := by
  let t :=
    ((oid V).eq x y)ᶜ ⊓ a ⊓
      memB (opairB (𝓜.D.child d) (𝓜.D.child w))
        (interpDKBodyGraph 𝓜 V K hK hV
          (η.update hV 𝓜.total x e) y P)
  change t ≤
    memB (opairB (𝓜.D.child e) (𝓜.D.child w))
      (interpDKBodyGraph 𝓜 V K hK hV
        (η.update hV 𝓜.total y d) x P)
  have htEq : t ≤ ((oid V).eq x y)ᶜ :=
    inf_le_left.trans inf_le_left
  have htA : t ≤ a := inf_le_left.trans inf_le_right
  have htmem : t ≤
      memB (opairB (𝓜.D.child d) (𝓜.D.child w))
        (interpDKBodyGraph 𝓜 V K hK hV
          (η.update hV 𝓜.total x e) y P) :=
    inf_le_right
  have hval :
      t ≤ interpDKRelVal 𝓜 V K hK hV
        ((η.update hV 𝓜.total x e).update hV 𝓜.total y d) P w :=
    (interpDKBodyGraph_mem_normalize 𝓜 V K hK hV
        (η.update hV 𝓜.total x e) y P a (hOuterRows e) d w).2.trans' <|
      le_inf htA htmem
  have hcomm :
      t ≤ interpDKRelVal 𝓜 V K hK hV
        ((η.update hV 𝓜.total y d).update hV 𝓜.total x e) P w :=
    (interpDKRelVal_update_commute_symm 𝓜 V K hK hV η x y d e P w).trans' <|
      le_inf htEq hval
  exact (interpDKBodyGraph_mem_normalize 𝓜 V K hK hV
      (η.update hV 𝓜.total y d) x P a (hInnerRows d) e w).1.trans' hcomm

/-- Displayed abs-body edges are `Lam` applied to the inner graph. -/
theorem interpDKBodyGraph_abs_mem_eq_lam
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
    (d e : 𝓜.D.idx) :
    a ⊓ lamDKVal V K (.abs x P) ⊓
        memB (opairB (𝓜.D.child d) (𝓜.D.child e))
          (interpDKBodyGraph 𝓜 V K hK hV η y (.abs x P)) =
      a ⊓ lamDKVal V K (.abs x P) ⊓
        memB (opairB
          (interpDKBodyGraph 𝓜 V K hK hV
            (η.update hV 𝓜.total y d) x P)
          (𝓜.D.child e)) 𝓜.Lam := by
  have hrows :=
    interpDKBodyGraph_abs_rows_isRelElementAt 𝓜 V K hK hV η y x P a
      hInner hInnerRows
  have hnorm :=
    inf_memB_interpDKBodyGraph_eq 𝓜 V K hK hV η y (.abs x P)
      (a ⊓ lamDKVal V K (.abs x P)) hrows d e
  have hinterp :
      interpDKRelVal 𝓜 V K hK hV
          (η.update hV 𝓜.total y d) (.abs x P) e =
        lamDKVal V K (.abs x P) ⊓
          memB (opairB
            (interpDKBodyGraph 𝓜 V K hK hV
              (η.update hV 𝓜.total y d) x P)
            (𝓜.D.child e)) 𝓜.Lam := by
    rw [interpDKRelVal_abs]
  apply le_antisymm
  · have h := hnorm.le.trans_eq hinterp
    exact le_inf inf_le_left (h.trans inf_le_right)
  · have h : a ⊓ lamDKVal V K (.abs x P) ⊓
        memB (opairB
          (interpDKBodyGraph 𝓜 V K hK hV
            (η.update hV 𝓜.total y d) x P)
          (𝓜.D.child e)) 𝓜.Lam ≤
        interpDKRelVal 𝓜 V K hK hV
          (η.update hV 𝓜.total y d) (.abs x P) e := by
      rw [hinterp]
      exact le_inf (inf_le_left.trans inf_le_right) inf_le_right
    exact h.trans hnorm.ge

/-- Off-diagonal, inner evaluations at a shared argument are monotone in
the outer variable, via the outer body graph. -/
theorem interpDKAbsFamily_eval_mono
    (𝓜 : InternalReflexiveModel (A := A))
    (V K : AName.{u} A) (hK : subsetB K 𝓜.D = ⊤)
    (hV : (oid V).IsTotal)
    (η : RelFun (oid V) (oid 𝓜.D))
    (y x : V.idx) (P : LamDK V.idx K.idx) (a : A)
    (hOuter : ∀ z, a ≤ isScottContinuousB
      (interpDKBodyGraph 𝓜 V K hK hV (η.update hV 𝓜.total x z) y P)
      𝓜.D 𝓜.D 𝓜.R 𝓜.R)
    (hInnerRows : ∀ d, ∀ e, IsRelElementAt 𝓜.D a
      (interpDKRelVal 𝓜 V K hK hV
        ((η.update hV 𝓜.total y d).update hV 𝓜.total x e) P))
    (hOuterRows : ∀ z, ∀ d, IsRelElementAt 𝓜.D a
      (interpDKRelVal 𝓜 V K hK hV
        ((η.update hV 𝓜.total x z).update hV 𝓜.total y d) P))
    (d d' e w w' : 𝓜.D.idx) :
    ((oid V).eq x y)ᶜ ⊓ a ⊓
        relB 𝓜.R (𝓜.D.child d) (𝓜.D.child d') ⊓
        memB (opairB (𝓜.D.child e) (𝓜.D.child w))
          (interpDKBodyGraph 𝓜 V K hK hV
            (η.update hV 𝓜.total y d) x P) ⊓
        memB (opairB (𝓜.D.child e) (𝓜.D.child w'))
          (interpDKBodyGraph 𝓜 V K hK hV
            (η.update hV 𝓜.total y d') x P) ≤
      relB 𝓜.R (𝓜.D.child w) (𝓜.D.child w') := by
  let Fd :=
    interpDKBodyGraph 𝓜 V K hK hV (η.update hV 𝓜.total y d) x P
  let Fd' :=
    interpDKBodyGraph 𝓜 V K hK hV (η.update hV 𝓜.total y d') x P
  let Ge :=
    interpDKBodyGraph 𝓜 V K hK hV (η.update hV 𝓜.total x e) y P
  let t :=
    ((oid V).eq x y)ᶜ ⊓ a ⊓
      relB 𝓜.R (𝓜.D.child d) (𝓜.D.child d') ⊓
      memB (opairB (𝓜.D.child e) (𝓜.D.child w)) Fd ⊓
      memB (opairB (𝓜.D.child e) (𝓜.D.child w')) Fd'
  change t ≤ relB 𝓜.R (𝓜.D.child w) (𝓜.D.child w')
  have htEq : t ≤ ((oid V).eq x y)ᶜ :=
    inf_le_left.trans (inf_le_left.trans
      (inf_le_left.trans inf_le_left))
  have htA : t ≤ a :=
    inf_le_left.trans (inf_le_left.trans
      (inf_le_left.trans inf_le_right))
  have htR : t ≤ relB 𝓜.R (𝓜.D.child d) (𝓜.D.child d') :=
    inf_le_left.trans (inf_le_left.trans inf_le_right)
  have hFd : t ≤
      memB (opairB (𝓜.D.child e) (𝓜.D.child w)) Fd :=
    inf_le_left.trans inf_le_right
  have hFd' : t ≤
      memB (opairB (𝓜.D.child e) (𝓜.D.child w')) Fd' :=
    inf_le_right
  have hGd : t ≤
      memB (opairB (𝓜.D.child d) (𝓜.D.child w)) Ge :=
    (interpDKAbsFamily_inner_le_outer 𝓜 V K hK hV η y x P a
        hInnerRows hOuterRows d e w).trans' <|
      le_inf (le_inf htEq htA) hFd
  have hGd' : t ≤
      memB (opairB (𝓜.D.child d') (𝓜.D.child w')) Ge :=
    (interpDKAbsFamily_inner_le_outer 𝓜 V K hK hV η y x P a
        hInnerRows hOuterRows d' e w').trans' <|
      le_inf (le_inf htEq htA) hFd'
  exact (scottContinuous_apply_mono (hOuter e)
      (𝓜.D.child d) (𝓜.D.child d')
      (𝓜.D.child w) (𝓜.D.child w')).trans' <|
    le_inf (le_inf (le_inf htA hGd) hGd') htR

/-- Off-diagonal, the inner family is `Q`-monotone on displayed inputs. -/
theorem interpDKAbsFamily_relQ
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
    (d d' : 𝓜.D.idx) :
    ((oid V).eq x y)ᶜ ⊓ a ⊓
        relB 𝓜.R (𝓜.D.child d) (𝓜.D.child d') ≤
      relB 𝓜.Q
        (interpDKBodyGraph 𝓜 V K hK hV (η.update hV 𝓜.total y d) x P)
        (interpDKBodyGraph 𝓜 V K hK hV
          (η.update hV 𝓜.total y d') x P) := by
  let Fd :=
    interpDKBodyGraph 𝓜 V K hK hV (η.update hV 𝓜.total y d) x P
  let Fd' :=
    interpDKBodyGraph 𝓜 V K hK hV (η.update hV 𝓜.total y d') x P
  let t :=
    ((oid V).eq x y)ᶜ ⊓ a ⊓
      relB 𝓜.R (𝓜.D.child d) (𝓜.D.child d')
  change t ≤ relB 𝓜.Q Fd Fd'
  have htEq : t ≤ ((oid V).eq x y)ᶜ :=
    inf_le_left.trans inf_le_left
  have htA : t ≤ a := inf_le_left.trans inf_le_right
  have htR : t ≤ relB 𝓜.R (𝓜.D.child d) (𝓜.D.child d') :=
    inf_le_right
  have hFC : t ≤ memB Fd 𝓜.C :=
    htA.trans (interpDKAbsFamily_mem_mapSpace 𝓜 V K hK hV η y x P a
      hInner d)
  have hFC' : t ≤ memB Fd' 𝓜.C :=
    htA.trans (interpDKAbsFamily_mem_mapSpace 𝓜 V K hK hV η y x P a
      hInner d')
  have hfun : t ≤ isFunctionB Fd 𝓜.D 𝓜.D :=
    (𝓜.mem_mapSpace_le_function Fd).trans' hFC
  have hfun' : t ≤ isFunctionB Fd' 𝓜.D 𝓜.D :=
    (𝓜.mem_mapSpace_le_function Fd').trans' hFC'
  have hsub : t ≤ subsetB Fd (prodB 𝓜.D 𝓜.D) :=
    hfun.trans (inf_le_left.trans inf_le_left)
  have hsub' : t ≤ subsetB Fd' (prodB 𝓜.D 𝓜.D) :=
    hfun'.trans (inf_le_left.trans inf_le_left)
  have hpw : t ≤ pointwiseLeB Fd Fd' 𝓜.D 𝓜.R := by
    unfold pointwiseLeB
    refine le_iInf fun s => le_iInf fun v => le_iInf fun v' => ?_
    rw [le_himp_iff]
    let u :=
      t ⊓ (memB s 𝓜.D ⊓ memB (opairB s v) Fd ⊓
        memB (opairB s v') Fd')
    change u ≤ relB 𝓜.R v v'
    have huT : u ≤ t := inf_le_left
    have huD : u ≤ memB s 𝓜.D :=
      inf_le_right.trans (inf_le_left.trans inf_le_left)
    have huF : u ≤ memB (opairB s v) Fd :=
      inf_le_right.trans (inf_le_left.trans inf_le_right)
    have huF' : u ≤ memB (opairB s v') Fd' :=
      inf_le_right.trans inf_le_right
    have hdec :
        u ≤ ⨆ p : 𝓜.D.idx × 𝓜.D.idx,
          eqB (opairB s v)
            (opairB (𝓜.D.child p.1) (𝓜.D.child p.2)) ⊓
          memB (opairB (𝓜.D.child p.1) (𝓜.D.child p.2)) Fd :=
      (inf_memB_le_iSup_matrix (hsub := huT.trans hsub)
          (opairB s v)).trans' <|
        le_inf le_rfl huF
    have hdec' :
        u ≤ ⨆ q : 𝓜.D.idx × 𝓜.D.idx,
          eqB (opairB s v')
            (opairB (𝓜.D.child q.1) (𝓜.D.child q.2)) ⊓
          memB (opairB (𝓜.D.child q.1) (𝓜.D.child q.2)) Fd' :=
      (inf_memB_le_iSup_matrix (hsub := huT.trans hsub')
          (opairB s v')).trans' <|
        le_inf le_rfl huF'
    refine (le_inf (le_inf le_rfl hdec) hdec').trans ?_
    rw [inf_iSup_eq (α := A)]
    refine iSup_le fun q => ?_
    rw [inf_right_comm, inf_iSup_eq (α := A)]
    refine iSup_le fun p => ?_
    let r :=
      u ⊓
        (eqB (opairB s v')
          (opairB (𝓜.D.child q.1) (𝓜.D.child q.2)) ⊓
          memB (opairB (𝓜.D.child q.1) (𝓜.D.child q.2)) Fd') ⊓
        (eqB (opairB s v)
          (opairB (𝓜.D.child p.1) (𝓜.D.child p.2)) ⊓
          memB (opairB (𝓜.D.child p.1) (𝓜.D.child p.2)) Fd)
    change r ≤ relB 𝓜.R v v'
    have hrU : r ≤ u := inf_le_left.trans inf_le_left
    have hrp : r ≤
        memB (opairB (𝓜.D.child p.1) (𝓜.D.child p.2)) Fd :=
      inf_le_right.trans inf_le_right
    have hrq : r ≤
        memB (opairB (𝓜.D.child q.1) (𝓜.D.child q.2)) Fd' :=
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
    have hsameArg : r ≤
        memB (opairB (𝓜.D.child p.1) (𝓜.D.child q.2)) Fd' :=
      (memB_opairB_congr Fd' (𝓜.D.child q.1) (𝓜.D.child p.1)
          (𝓜.D.child q.2) (𝓜.D.child q.2)).trans' <|
        le_inf (le_inf
            (heq.trans_eq (eqB_comm (𝓜.D.child p.1) (𝓜.D.child q.1)))
            (le_top.trans (eqB_self (A := A) (𝓜.D.child q.2)).ge))
          hrq
    have hmono : r ≤
        relB 𝓜.R (𝓜.D.child p.2) (𝓜.D.child q.2) :=
      (interpDKAbsFamily_eval_mono 𝓜 V K hK hV η y x P a
          hOuter hInnerRows hOuterRows d d' p.1 p.2 q.2).trans' <|
        le_inf (le_inf (le_inf (le_inf
            (hrU.trans (huT.trans htEq))
            (hrU.trans (huT.trans htA)))
          (hrU.trans (huT.trans htR)))
          hrp) hsameArg
    exact (relB_congr 𝓜.R (𝓜.D.child p.2) v (𝓜.D.child q.2) v').trans' <|
      le_inf (le_inf
          (hvp.trans_eq (eqB_comm v (𝓜.D.child p.2)))
          (hvq.trans_eq (eqB_comm v' (𝓜.D.child q.2))))
        hmono
  exact (𝓜.pointwise_le_relQ Fd Fd').trans' <|
    le_inf (le_inf hFC hFC') hpw

end Scott2026
