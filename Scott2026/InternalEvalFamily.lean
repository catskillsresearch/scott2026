/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/

import Scott2026.InternalInterp
import Scott2026.InternalEval

/-!
# Parametricity of the internal evaluator

The abstraction case of Theorem 26 requires induction over a whole
Boolean-valued family of environments.  This module proves the extensional
transport part of that strong induction.
-/

universe u

namespace Scott2026

open AName

variable {A : Type u} [CompleteBooleanAlgebra A]

/-- Two names with the same displayed children are Boolean-equal to degree
`a` when their coefficients transport in both directions to degree `a`. -/
theorem le_eqB_mk_of_le_val {I : Type u} (child : I → AName.{u} A)
    (v w : I → A) (a : A)
    (hvw : ∀ i, a ⊓ v i ≤ w i)
    (hwv : ∀ i, a ⊓ w i ≤ v i) :
    a ≤ eqB (mk I child v) (mk I child w) := by
  rw [eqB_eq_subset]
  refine le_inf ?_ ?_
  · rw [subsetB_mk]
    refine le_iInf fun i => ?_
    rw [le_himp_iff]
    exact (hvw i).trans (val_le_memB (mk I child w) i)
  · rw [subsetB_mk]
    refine le_iInf fun i => ?_
    rw [le_himp_iff]
    exact (hwv i).trans (val_le_memB (mk I child v) i)

/-- The recursive interpretation transports pointwise along every
extensional family of relational environments. This is deliberately
quantified over the family: abstraction updates do not commute strictly for
fuzzy variable equality. -/
theorem interpDKRelVal_isPointwiseFamily
    (𝓜 : InternalReflexiveModel (A := A))
    (V K : AName.{u} A) (hK : subsetB K 𝓜.D = ⊤)
    (hV : (oid V).IsTotal)
    {U : Type*} (S : ASetoid (A := A) U)
    (η : U → RelFun (oid V) (oid 𝓜.D))
    (hη : RelFun.IsPointwiseFamily S η)
    (M : LamDK V.idx K.idx) :
    ∀ u v d, S.eq u v ⊓
        interpDKRelVal 𝓜 V K hK hV (η u) M d ≤
      interpDKRelVal 𝓜 V K hK hV (η v) M d := by
  induction M generalizing U with
  | var x =>
      intro u v d
      rw [interpDKRelVal_var, interpDKRelVal_var]
      exact hη u v x d
  | const k =>
      intro u v d
      rw [interpDKRelVal_const, interpDKRelVal_const]
      exact inf_le_right
  | app P Q ihP ihQ =>
      intro u v d
      rw [interpDKRelVal_app, interpDKRelVal_app, inf_iSup_eq]
      refine iSup_le fun c => le_iSup_of_le c ?_
      rw [inf_iSup_eq]
      refine iSup_le fun q' => le_iSup_of_le q' ?_
      rw [inf_iSup_eq]
      refine iSup_le fun p => le_iSup_of_le p ?_
      rw [inf_iSup_eq]
      refine iSup_le fun q => le_iSup_of_le q ?_
      let z : A :=
        memB (opairB (𝓜.D.child p) (𝓜.C.child c)) 𝓜.Fun ⊓
          (oid 𝓜.D).eq q q' ⊓
          memB (𝓜.C.child c) 𝓜.C ⊓
          memB (opairB (𝓜.D.child q') (𝓜.D.child d))
            (𝓜.C.child c)
      have hP := ihP S η hη u v p
      have hQ := ihQ S η hη u v q
      have hPQ : S.eq u v ⊓
          (interpDKRelVal 𝓜 V K hK hV (η u) P p ⊓
            interpDKRelVal 𝓜 V K hK hV (η u) Q q) ≤
          interpDKRelVal 𝓜 V K hK hV (η v) P p ⊓
            interpDKRelVal 𝓜 V K hK hV (η v) Q q := by
        calc
          S.eq u v ⊓
              (interpDKRelVal 𝓜 V K hK hV (η u) P p ⊓
                interpDKRelVal 𝓜 V K hK hV (η u) Q q) ≤
            (S.eq u v ⊓
                interpDKRelVal 𝓜 V K hK hV (η u) P p) ⊓
              (S.eq u v ⊓
                interpDKRelVal 𝓜 V K hK hV (η u) Q q) := by
                  apply le_of_eq
                  ac_rfl
          _ ≤ _ := inf_le_inf hP hQ
      calc
        _ = (S.eq u v ⊓
            (interpDKRelVal 𝓜 V K hK hV (η u) P p ⊓
              interpDKRelVal 𝓜 V K hK hV (η u) Q q)) ⊓ z := by
                dsimp [z]
                ac_rfl
        _ ≤ (interpDKRelVal 𝓜 V K hK hV (η v) P p ⊓
              interpDKRelVal 𝓜 V K hK hV (η v) Q q) ⊓ z :=
          inf_le_inf hPQ le_rfl
        _ = _ := by
          dsimp [z]
          ac_rfl
  | abs x P ih =>
      intro u v d
      rw [interpDKRelVal_abs, interpDKRelVal_abs]
      let body (w : U) :=
        interpDKBodyGraph 𝓜 V K hK hV (η w) x P
      have hbody_transport : ∀ w₁ w₂ p, S.eq w₁ w₂ ⊓
          (body w₁).val p ≤ (body w₂).val p := by
        intro w₁ w₂ p
        let replacement : U → 𝓜.D.idx := fun _ => p.1
        have hrepl : APoset.Functional S (oid 𝓜.D) replacement := by
          intro z₁ z₂
          change S.eq z₁ z₂ ≤ (oid 𝓜.D).eps p.1
          rw [𝓜.total p.1]
          exact le_top
        have hupd := hη.update hV 𝓜.total x replacement hrepl
        exact ih S (fun w => (η w).update hV 𝓜.total x p.1)
          hupd w₁ w₂ p.2
      have hbody_fwd : ∀ p, S.eq u v ⊓
          (body u).val p ≤ (body v).val p :=
        hbody_transport u v
      have hbody_rev : ∀ p, S.eq u v ⊓
          (body v).val p ≤ (body u).val p := by
        intro p
        have h := hbody_transport v u p
        rwa [S.symm v u] at h
      have heq : S.eq u v ≤ eqB (body u) (body v) := by
        exact le_eqB_mk_of_le_val
          (fun p : 𝓜.D.idx × 𝓜.D.idx =>
            opairB (𝓜.D.child p.1) (𝓜.D.child p.2))
          (body u).val (body v).val (S.eq u v) hbody_fwd hbody_rev
      let fixed := memB (V.child x) V ⊓ lamDKVal V K P
      change S.eq u v ⊓
          (fixed ⊓ memB (opairB (body u) (𝓜.D.child d)) 𝓜.Lam) ≤
        fixed ⊓ memB (opairB (body v) (𝓜.D.child d)) 𝓜.Lam
      refine le_inf (inf_le_right.trans inf_le_left) ?_
      refine (memB_opairB_congr 𝓜.Lam (body u) (body v)
        (𝓜.D.child d) (𝓜.D.child d)).trans' ?_
      refine le_inf (le_inf ?_ ?_) ?_
      · exact inf_le_left.trans heq
      · exact le_top.trans (eqB_self (A := A) (𝓜.D.child d)).ge
      · exact inf_le_right.trans inf_le_right

end Scott2026
