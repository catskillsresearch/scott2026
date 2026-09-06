/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/

import Scott2026.InternalInterp
import Scott2026.LambdaConstVA
import Scott2026.ReflexiveVA

/-!
# Internal Definition 25 evaluation

This file develops the valuation-parametric recursion omitted from the
paper's proof of Theorem 26.
-/

universe u

namespace Scott2026

open AName

variable {A : Type u} [CompleteBooleanAlgebra A]

/-- The internal reflexive-dcpo data and the external setoid hypotheses of
Theorem 26. -/
structure InternalReflexiveModel where
  D : AName.{u} A
  R : AName.{u} A
  C : AName.{u} A
  Q : AName.{u} A
  Fun : AName.{u} A
  Lam : AName.{u} A
  valid : isReflexiveDcpoB D R C Q Fun Lam = ⊤
  strict : (oid D).IsStrict
  total : (oid D).IsTotal
  complete : (oid D).IsComplete.{u}

namespace InternalReflexiveModel

variable (M : InternalReflexiveModel (A := A))

/-- The six clauses packed by internal Definition 19. -/
theorem valid_components :
    isDcpoWithBottomB M.D M.R = ⊤ ∧
      isContinuousMapSpaceB M.C M.D M.R = ⊤ ∧
      isPointwiseOrderB M.Q M.C M.D M.R = ⊤ ∧
      isScottContinuousB M.Fun M.D M.C M.R M.Q = ⊤ ∧
      isScottContinuousB M.Lam M.C M.D M.Q M.R = ⊤ ∧
      eqB (compB M.Fun M.Lam M.C M.C) (idB M.C) = ⊤ := by
  have hv := M.valid
  unfold isReflexiveDcpoB at hv
  have h₅ := inf_eq_top_iff.mp hv
  have h₄ := inf_eq_top_iff.mp h₅.1
  have h₃ := inf_eq_top_iff.mp h₄.1
  have h₂ := inf_eq_top_iff.mp h₃.1
  have h₁ := inf_eq_top_iff.mp h₂.1
  exact ⟨h₁.1, h₁.2, h₂.2, h₃.2, h₄.2, h₅.2⟩

theorem dcpo_valid : isDcpoWithBottomB M.D M.R = ⊤ :=
  M.valid_components.1

theorem mapSpace_valid : isContinuousMapSpaceB M.C M.D M.R = ⊤ :=
  M.valid_components.2.1

theorem pointwise_valid : isPointwiseOrderB M.Q M.C M.D M.R = ⊤ :=
  M.valid_components.2.2.1

theorem fun_continuous :
    isScottContinuousB M.Fun M.D M.C M.R M.Q = ⊤ :=
  M.valid_components.2.2.2.1

theorem lam_continuous :
    isScottContinuousB M.Lam M.C M.D M.Q M.R = ⊤ :=
  M.valid_components.2.2.2.2.1

theorem retract_valid :
    eqB (compB M.Fun M.Lam M.C M.C) (idB M.C) = ⊤ :=
  M.valid_components.2.2.2.2.2

/-- Scott continuity includes being an internal function. -/
theorem function_of_scottContinuous {F X Y P Q : AName.{u} A}
    (h : isScottContinuousB F X Y P Q = ⊤) :
    isFunctionB F X Y = ⊤ := by
  unfold isScottContinuousB at h
  exact (inf_eq_top_iff.mp (inf_eq_top_iff.mp h).1).1

theorem fun_function : isFunctionB M.Fun M.D M.C = ⊤ :=
  function_of_scottContinuous M.fun_continuous

theorem lam_function : isFunctionB M.Lam M.C M.D = ⊤ :=
  function_of_scottContinuous M.lam_continuous

/-- The reverse half of “`C` consists exactly of the Scott-continuous
self-maps of `D`.” -/
theorem mem_mapSpace_of_scottContinuous (F : AName.{u} A)
    (hF : isScottContinuousB F M.D M.D M.R M.R = ⊤) :
    memB F M.C = ⊤ := by
  have hparts := inf_eq_top_iff.mp M.mapSpace_valid
  have hall : (⨅ G : AName.{u} A,
      (memB G M.C ⇨ isScottContinuousB G M.D M.D M.R M.R) ⊓
        (isScottContinuousB G M.D M.D M.R M.R ⇨ memB G M.C)) = ⊤ :=
    hparts.2
  have hG := iInf_eq_top.mp hall F
  have himp :
      isScottContinuousB F M.D M.D M.R M.R ⇨ memB F M.C = ⊤ :=
    (inf_eq_top_iff.mp hG).2
  apply top_unique
  exact (himp_eq_top_iff.mp himp).trans' (by rw [hF])

end InternalReflexiveModel

/-!
## The recursive Boolean matrix
-/

/-- Definition 25 as a Boolean relational matrix. The environment is already
total. In the abstraction case the recursive calls form the graph of the
meta-function `d ↦ ⟦M⟧ρ[x:=d]`, which is then passed to the internal `Lam`
graph. -/
noncomputable def interpDKRelVal
    (𝓜 : InternalReflexiveModel (A := A))
    (V K : AName.{u} A) (hK : subsetB K 𝓜.D = ⊤)
    (hV : (oid V).IsTotal)
    (η : RelFun (oid V) (oid 𝓜.D)) :
    LamDK V.idx K.idx → 𝓜.D.idx → A
  | .var x, d => η.val x d
  | .const k, d => (oidSubsetRel K 𝓜.D hK).val k d
  | .app P Q, d =>
      ⨆ p : 𝓜.D.idx, ⨆ q : 𝓜.D.idx, ⨆ F : AName.{u} A,
        interpDKRelVal 𝓜 V K hK hV η P p ⊓
          interpDKRelVal 𝓜 V K hK hV η Q q ⊓
          memB (opairB (𝓜.D.child p) F) 𝓜.Fun ⊓
          memB (opairB (𝓜.D.child q) (𝓜.D.child d)) F
  | .abs x P, d =>
      (memB (V.child x) V ⊓ lamDKVal V K P) ⊓
        memB
          (opairB
            (mk (𝓜.D.idx × 𝓜.D.idx)
              (fun p => opairB (𝓜.D.child p.1) (𝓜.D.child p.2))
              (fun p => interpDKRelVal 𝓜 V K hK hV
                (η.update hV 𝓜.total x p.1) P p.2))
            (𝓜.D.child d))
          𝓜.Lam
termination_by M => sizeOf M

@[simp] theorem interpDKRelVal_var
    (𝓜 : InternalReflexiveModel (A := A))
    (V K : AName.{u} A) (hK : subsetB K 𝓜.D = ⊤)
    (hV : (oid V).IsTotal)
    (η : RelFun (oid V) (oid 𝓜.D)) (x : V.idx) (d : 𝓜.D.idx) :
    interpDKRelVal 𝓜 V K hK hV η (.var x) d = η.val x d :=
  by rw [interpDKRelVal]

@[simp] theorem interpDKRelVal_const
    (𝓜 : InternalReflexiveModel (A := A))
    (V K : AName.{u} A) (hK : subsetB K 𝓜.D = ⊤)
    (hV : (oid V).IsTotal)
    (η : RelFun (oid V) (oid 𝓜.D)) (k : K.idx) (d : 𝓜.D.idx) :
    interpDKRelVal 𝓜 V K hK hV η (.const k) d =
      (oidSubsetRel K 𝓜.D hK).val k d :=
  by rw [interpDKRelVal]

@[simp] theorem interpDKRelVal_app
    (𝓜 : InternalReflexiveModel (A := A))
    (V K : AName.{u} A) (hK : subsetB K 𝓜.D = ⊤)
    (hV : (oid V).IsTotal)
    (η : RelFun (oid V) (oid 𝓜.D))
    (P Q : LamDK V.idx K.idx) (d : 𝓜.D.idx) :
    interpDKRelVal 𝓜 V K hK hV η (.app P Q) d =
      ⨆ p : 𝓜.D.idx, ⨆ q : 𝓜.D.idx, ⨆ F : AName.{u} A,
        interpDKRelVal 𝓜 V K hK hV η P p ⊓
          interpDKRelVal 𝓜 V K hK hV η Q q ⊓
          memB (opairB (𝓜.D.child p) F) 𝓜.Fun ⊓
          memB (opairB (𝓜.D.child q) (𝓜.D.child d)) F :=
  by rw [interpDKRelVal]

/-- The internal graph of the meta-function in the abstraction clause. -/
noncomputable def interpDKBodyGraph
    (𝓜 : InternalReflexiveModel (A := A))
    (V K : AName.{u} A) (hK : subsetB K 𝓜.D = ⊤)
    (hV : (oid V).IsTotal)
    (η : RelFun (oid V) (oid 𝓜.D))
    (x : V.idx) (P : LamDK V.idx K.idx) : AName.{u} A :=
  mk (𝓜.D.idx × 𝓜.D.idx)
    (fun p => opairB (𝓜.D.child p.1) (𝓜.D.child p.2))
    (fun p => interpDKRelVal 𝓜 V K hK hV
      (η.update hV 𝓜.total x p.1) P p.2)

@[simp] theorem interpDKRelVal_abs
    (𝓜 : InternalReflexiveModel (A := A))
    (V K : AName.{u} A) (hK : subsetB K 𝓜.D = ⊤)
    (hV : (oid V).IsTotal)
    (η : RelFun (oid V) (oid 𝓜.D))
    (x : V.idx) (P : LamDK V.idx K.idx) (d : 𝓜.D.idx) :
    interpDKRelVal 𝓜 V K hK hV η (.abs x P) d =
      lamDKVal V K (.abs x P) ⊓
        memB (opairB (interpDKBodyGraph 𝓜 V K hK hV η x P)
          (𝓜.D.child d)) 𝓜.Lam :=
  by rw [interpDKRelVal, interpDKBodyGraph, lamDKVal]

/-- A Boolean row representing one element of `D` at extent `a`. -/
def IsRelElementAt (D : AName.{u} A) (a : A) (r : D.idx → A) : Prop :=
  (∀ d e, (oid D).eq d e ⊓ r d ≤ r e) ∧
    (∀ d, r d ≤ a ⊓ (oid D).eps d) ∧
    (∀ d e, r d ⊓ r e ≤ (oid D).eq d e) ∧
    (a ≤ ⨆ d, r d)

/-- `IsRelElementAt` is exactly a relational function out of the singleton
setoid with extent `a`. -/
noncomputable def relFunOfIsRelElementAt
    {D : AName.{u} A} {a : A} {r : D.idx → A}
    (h : IsRelElementAt D a r) :
    RelFun (extentSetoid a) (oid D) where
  val _ d := r d
  respects := by
    intro _ _ d e
    refine le_inf ?_ ?_ <;> rw [le_himp_iff]
    · exact h.1 d e |>.trans' <|
        le_inf (inf_le_left.trans inf_le_right) inf_le_right
    · have hde := h.1 e d
      rw [(oid D).symm e d] at hde
      exact hde.trans' <|
        le_inf (inf_le_left.trans inf_le_right) inf_le_right
  le_eps := fun _ d => h.2.1 d
  single_valued := fun _ d e => h.2.2.1 d e
  total := fun _ => h.2.2.2

@[simp] theorem relFunOfIsRelElementAt_val
    {D : AName.{u} A} {a : A} {r : D.idx → A}
    (h : IsRelElementAt D a r) (i : PUnit) (d : D.idx) :
    (relFunOfIsRelElementAt h).val i d = r d :=
  rfl

/-- Every relational map from a singleton extent is a generalized
element at that extent. -/
theorem isRelElementAt_of_relFun
    {D : AName.{u} A} {a : A}
    (f : RelFun (extentSetoid a) (oid D)) :
    IsRelElementAt D a (fun d => f.val PUnit.unit d) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro d e
    exact f.subst_right PUnit.unit d e
  · intro d
    exact f.le_eps PUnit.unit d
  · intro d e
    exact f.single_valued PUnit.unit d e
  · exact f.total PUnit.unit

/-- Variable case of the extent-indexed fundamental relation lemma. -/
theorem interpDKRelVal_var_isRelElementAt
    (𝓜 : InternalReflexiveModel (A := A))
    (V K : AName.{u} A) (hK : subsetB K 𝓜.D = ⊤)
    (hV : (oid V).IsTotal)
    (η : RelFun (oid V) (oid 𝓜.D)) (x : V.idx) :
    IsRelElementAt 𝓜.D (lamDKVal V K (.var x))
      (interpDKRelVal 𝓜 V K hK hV η (.var x)) := by
  have h := isRelElementAt_of_relFun (η.at x)
  change IsRelElementAt 𝓜.D (memB (V.child x) V) _
  have heval :
      interpDKRelVal 𝓜 V K hK hV η (.var x) =
        fun d => η.val x d := by
    funext d
    rw [interpDKRelVal_var]
  rw [heval]
  simpa only [oid_eps, RelFun.at_val] using h

/-- Constant case of the extent-indexed fundamental relation lemma. -/
theorem interpDKRelVal_const_isRelElementAt
    (𝓜 : InternalReflexiveModel (A := A))
    (V K : AName.{u} A) (hK : subsetB K 𝓜.D = ⊤)
    (hV : (oid V).IsTotal)
    (η : RelFun (oid V) (oid 𝓜.D)) (k : K.idx) :
    IsRelElementAt 𝓜.D (lamDKVal V K (.const k))
      (interpDKRelVal 𝓜 V K hK hV η (.const k)) := by
  have h := isRelElementAt_of_relFun ((oidSubsetRel K 𝓜.D hK).at k)
  change IsRelElementAt 𝓜.D (memB (K.child k) K) _
  have heval :
      interpDKRelVal 𝓜 V K hK hV η (.const k) =
        fun d => (oidSubsetRel K 𝓜.D hK).val k d := by
    funext d
    rw [interpDKRelVal_const]
  rw [heval]
  simpa only [oid_eps, RelFun.at_val] using h

end Scott2026
