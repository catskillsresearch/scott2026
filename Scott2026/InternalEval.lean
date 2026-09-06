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
      ⨆ c : 𝓜.C.idx, ⨆ q' : 𝓜.D.idx, ⨆ p : 𝓜.D.idx,
        ⨆ q : 𝓜.D.idx,
        interpDKRelVal 𝓜 V K hK hV η P p ⊓
          interpDKRelVal 𝓜 V K hK hV η Q q ⊓
          memB (opairB (𝓜.D.child p) (𝓜.C.child c)) 𝓜.Fun ⊓
          (oid 𝓜.D).eq q q' ⊓
          memB (𝓜.C.child c) 𝓜.C ⊓
          memB (opairB (𝓜.D.child q') (𝓜.D.child d))
            (𝓜.C.child c)
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
      ⨆ c : 𝓜.C.idx, ⨆ q' : 𝓜.D.idx, ⨆ p : 𝓜.D.idx,
        ⨆ q : 𝓜.D.idx,
        interpDKRelVal 𝓜 V K hK hV η P p ⊓
          interpDKRelVal 𝓜 V K hK hV η Q q ⊓
          memB (opairB (𝓜.D.child p) (𝓜.C.child c)) 𝓜.Fun ⊓
          (oid 𝓜.D).eq q q' ⊓
          memB (𝓜.C.child c) 𝓜.C ⊓
          memB (opairB (𝓜.D.child q') (𝓜.D.child d))
            (𝓜.C.child c) :=
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

/-!
## Internal evaluation of continuous maps
-/

/-- Membership in the internal continuous-map space entails Scott continuity
at the same Boolean degree. -/
theorem InternalReflexiveModel.mem_mapSpace_le_scottContinuous
    (𝓜 : InternalReflexiveModel (A := A)) (F : AName.{u} A) :
    memB F 𝓜.C ≤ isScottContinuousB F 𝓜.D 𝓜.D 𝓜.R 𝓜.R := by
  have hall := (inf_eq_top_iff.mp 𝓜.mapSpace_valid).2
  have hF := iInf_eq_top.mp hall F
  exact himp_eq_top_iff.mp (inf_eq_top_iff.mp hF).1

/-- Membership in the internal continuous-map space entails the internal
function predicate, at the same Boolean degree. -/
theorem InternalReflexiveModel.mem_mapSpace_le_function
    (𝓜 : InternalReflexiveModel (A := A)) (F : AName.{u} A) :
    memB F 𝓜.C ≤ isFunctionB F 𝓜.D 𝓜.D := by
  have hcont := 𝓜.mem_mapSpace_le_scottContinuous F
  unfold isScottContinuousB at hcont
  exact hcont.trans (inf_le_left.trans inf_le_left)

/-- The graph used by the abstraction clause is Scott-continuous at every
Boolean degree at which it belongs to the internal map space. -/
theorem interpDKBodyGraph_mem_le_scottContinuous
    (𝓜 : InternalReflexiveModel (A := A))
    (V K : AName.{u} A) (hK : subsetB K 𝓜.D = ⊤)
    (hV : (oid V).IsTotal)
    (η : RelFun (oid V) (oid 𝓜.D))
    (x : V.idx) (P : LamDK V.idx K.idx) :
    memB (interpDKBodyGraph 𝓜 V K hK hV η x P) 𝓜.C ≤
      isScottContinuousB
        (interpDKBodyGraph 𝓜 V K hK hV η x P)
        𝓜.D 𝓜.D 𝓜.R 𝓜.R :=
  𝓜.mem_mapSpace_le_scottContinuous _

/-- Degree-indexed version of choosing the codomain component of a pair from
the presented domain of an internal relation. -/
theorem inf_memB_opairB_le_iSup_child {a : A} {F X Y : AName.{u} A}
    (hsub : a ≤ subsetB F (prodB X Y)) (x y : AName.{u} A) :
    a ⊓ memB (opairB x y) F ≤
      ⨆ j : Y.idx, memB (opairB x (Y.child j)) F := by
  have hmem : a ⊓ memB (opairB x y) F ≤ memB y Y := by
    have h := (memB_of_subsetB (opairB x y) F (prodB X Y)).trans' <|
      le_inf inf_le_right (inf_le_left.trans hsub)
    rw [memB_opairB_prodB] at h
    exact h.trans inf_le_right
  refine (le_inf le_rfl hmem).trans ?_
  rw [memB_eq (x := y) (y := Y), inf_iSup_eq]
  refine iSup_le fun j => le_iSup_of_le j ?_
  refine (memB_opairB_congr F x x y (Y.child j)).trans' ?_
  refine le_inf (le_inf ?_ (inf_le_right.trans inf_le_left)) ?_
  · exact le_top.trans (eqB_self (A := A) x).ge
  · exact inf_le_left.trans inf_le_right

/-- Evaluation is a relational function from an internal continuous map and
an argument to its value. This is the internal analogue of continuous-map
application at the underlying setoid level. -/
noncomputable def InternalReflexiveModel.evalRel
    (𝓜 : InternalReflexiveModel (A := A)) :
    RelFun ((oid 𝓜.C).prod (oid 𝓜.D)) (oid 𝓜.D) where
  val p y :=
    memB (𝓜.C.child p.1) 𝓜.C ⊓
      memB (opairB (𝓜.D.child p.2) (𝓜.D.child y)) (𝓜.C.child p.1)
  respects := by
    intro p₁ p₂ y₁ y₂
    refine le_inf ?_ ?_ <;> rw [le_himp_iff]
    · let t :=
        ((oid 𝓜.C).prod (oid 𝓜.D)).eq p₁ p₂ ⊓
          (oid 𝓜.D).eq y₁ y₂ ⊓
            (memB (𝓜.C.child p₁.1) 𝓜.C ⊓
              memB (opairB (𝓜.D.child p₁.2) (𝓜.D.child y₁))
                (𝓜.C.child p₁.1))
      change t ≤ _
      have hs : t ≤ ((oid 𝓜.C).prod (oid 𝓜.D)).eq p₁ p₂ := by
        dsimp [t]
        exact inf_le_left.trans inf_le_left
      have ht : t ≤ (oid 𝓜.D).eq y₁ y₂ := by
        dsimp [t]
        exact inf_le_left.trans inf_le_right
      have hv0 : t ≤ memB (𝓜.C.child p₁.1) 𝓜.C ⊓
          memB (opairB (𝓜.D.child p₁.2) (𝓜.D.child y₁))
            (𝓜.C.child p₁.1) := by
        dsimp [t]
        exact inf_le_right
      have hC₂ : t ≤ memB (𝓜.C.child p₂.1) 𝓜.C := by
        have h := hs.trans
          (((oid 𝓜.C).prod (oid 𝓜.D)).eq_le_eps_right p₁ p₂)
        change t ≤ (oid 𝓜.C).eps p₂.1 ⊓ (oid 𝓜.D).eps p₂.2 at h
        rw [oid_eps] at h
        exact h.trans inf_le_left
      have hFF : t ≤ eqB (𝓜.C.child p₁.1) (𝓜.C.child p₂.1) := by
        have h : ((oid 𝓜.C).prod (oid 𝓜.D)).eq p₁ p₂ ≤
            (oid 𝓜.C).eq p₁.1 p₂.1 := by
          rw [ASetoid.prod_eq]
          exact inf_le_left
        exact hs.trans h |>.trans (by rw [oid_eq]; exact inf_le_right)
      have hxx : t ≤ eqB (𝓜.D.child p₁.2) (𝓜.D.child p₂.2) := by
        have h : ((oid 𝓜.C).prod (oid 𝓜.D)).eq p₁ p₂ ≤
            (oid 𝓜.D).eq p₁.2 p₂.2 := by
          rw [ASetoid.prod_eq]
          exact inf_le_right
        exact hs.trans h |>.trans (by rw [oid_eq]; exact inf_le_right)
      have hyy : t ≤ eqB (𝓜.D.child y₁) (𝓜.D.child y₂) := by
        exact ht.trans (by rw [oid_eq]; exact inf_le_right)
      have hv : t ≤ memB
          (opairB (𝓜.D.child p₁.2) (𝓜.D.child y₁))
          (𝓜.C.child p₁.1) := by
        exact hv0.trans inf_le_right
      refine le_inf hC₂ ?_
      refine (memB_eqB_right (𝓜.C.child p₁.1)
        (opairB (𝓜.D.child p₂.2) (𝓜.D.child y₂))
        (𝓜.C.child p₂.1)).trans' (le_inf ?_ hFF)
      exact (memB_opairB_congr (𝓜.C.child p₁.1)
        (𝓜.D.child p₁.2) (𝓜.D.child p₂.2)
        (𝓜.D.child y₁) (𝓜.D.child y₂)).trans'
          (le_inf (le_inf hxx hyy) hv)
    · let t :=
        ((oid 𝓜.C).prod (oid 𝓜.D)).eq p₁ p₂ ⊓
          (oid 𝓜.D).eq y₁ y₂ ⊓
            (memB (𝓜.C.child p₂.1) 𝓜.C ⊓
              memB (opairB (𝓜.D.child p₂.2) (𝓜.D.child y₂))
                (𝓜.C.child p₂.1))
      change t ≤ _
      have hs : t ≤ ((oid 𝓜.C).prod (oid 𝓜.D)).eq p₁ p₂ := by
        dsimp [t]
        exact inf_le_left.trans inf_le_left
      have ht : t ≤ (oid 𝓜.D).eq y₁ y₂ := by
        dsimp [t]
        exact inf_le_left.trans inf_le_right
      have hv0 : t ≤ memB (𝓜.C.child p₂.1) 𝓜.C ⊓
          memB (opairB (𝓜.D.child p₂.2) (𝓜.D.child y₂))
            (𝓜.C.child p₂.1) := by
        dsimp [t]
        exact inf_le_right
      have hC₁ : t ≤ memB (𝓜.C.child p₁.1) 𝓜.C := by
        have h := hs.trans
          (((oid 𝓜.C).prod (oid 𝓜.D)).eq_le_eps_left p₁ p₂)
        change t ≤ (oid 𝓜.C).eps p₁.1 ⊓ (oid 𝓜.D).eps p₁.2 at h
        rw [oid_eps] at h
        exact h.trans inf_le_left
      have hFF : t ≤ eqB (𝓜.C.child p₂.1) (𝓜.C.child p₁.1) := by
        have h : ((oid 𝓜.C).prod (oid 𝓜.D)).eq p₁ p₂ ≤
            (oid 𝓜.C).eq p₁.1 p₂.1 := by
          rw [ASetoid.prod_eq]
          exact inf_le_left
        have h' := hs.trans h
        rw [(oid 𝓜.C).symm p₁.1 p₂.1, oid_eq] at h'
        exact h'.trans inf_le_right
      have hxx : t ≤ eqB (𝓜.D.child p₂.2) (𝓜.D.child p₁.2) := by
        have h : ((oid 𝓜.C).prod (oid 𝓜.D)).eq p₁ p₂ ≤
            (oid 𝓜.D).eq p₁.2 p₂.2 := by
          rw [ASetoid.prod_eq]
          exact inf_le_right
        have h' := hs.trans h
        rw [(oid 𝓜.D).symm p₁.2 p₂.2, oid_eq] at h'
        exact h'.trans inf_le_right
      have hyy : t ≤ eqB (𝓜.D.child y₂) (𝓜.D.child y₁) := by
        have h := ht
        rw [(oid 𝓜.D).symm y₁ y₂, oid_eq] at h
        exact h.trans inf_le_right
      have hv : t ≤ memB
          (opairB (𝓜.D.child p₂.2) (𝓜.D.child y₂))
          (𝓜.C.child p₂.1) := by
        exact hv0.trans inf_le_right
      refine le_inf hC₁ ?_
      refine (memB_eqB_right (𝓜.C.child p₂.1)
        (opairB (𝓜.D.child p₁.2) (𝓜.D.child y₁))
        (𝓜.C.child p₁.1)).trans' (le_inf ?_ hFF)
      exact (memB_opairB_congr (𝓜.C.child p₂.1)
        (𝓜.D.child p₂.2) (𝓜.D.child p₁.2)
        (𝓜.D.child y₂) (𝓜.D.child y₁)).trans'
          (le_inf (le_inf hxx hyy) hv)
  le_eps := by
    intro p y
    change (memB (𝓜.C.child p.1) 𝓜.C ⊓
      memB (opairB (𝓜.D.child p.2) (𝓜.D.child y))
        (𝓜.C.child p.1)) ≤
      ((oid 𝓜.C).eps p.1 ⊓ (oid 𝓜.D).eps p.2) ⊓
        (oid 𝓜.D).eps y
    have hfun := 𝓜.mem_mapSpace_le_function (𝓜.C.child p.1)
    have hmem : memB (𝓜.C.child p.1) 𝓜.C ⊓
        memB (opairB (𝓜.D.child p.2) (𝓜.D.child y))
          (𝓜.C.child p.1) ≤
        memB (𝓜.D.child p.2) 𝓜.D ⊓
          memB (𝓜.D.child y) 𝓜.D := by
      have hsub : memB (𝓜.C.child p.1) 𝓜.C ≤
          subsetB (𝓜.C.child p.1) (prodB 𝓜.D 𝓜.D) :=
        hfun.trans (inf_le_left.trans inf_le_left)
      have hm := (memB_of_subsetB
        (opairB (𝓜.D.child p.2) (𝓜.D.child y))
        (𝓜.C.child p.1) (prodB 𝓜.D 𝓜.D)).trans' <|
          le_inf inf_le_right (inf_le_left.trans hsub)
      rwa [memB_opairB_prodB] at hm
    rw [oid_eps, oid_eps, oid_eps]
    exact le_inf
      (le_inf inf_le_left (hmem.trans inf_le_left))
      (hmem.trans inf_le_right)
  single_valued := by
    intro p y₁ y₂
    have hfun := 𝓜.mem_mapSpace_le_function (𝓜.C.child p.1)
    have hsv := isSingleValuedB_apply (𝓜.C.child p.1)
      (𝓜.D.child p.2) (𝓜.D.child y₁) (𝓜.D.child y₂)
    have hsupport (y : 𝓜.D.idx) :
        memB (𝓜.C.child p.1) 𝓜.C ⊓
            memB (opairB (𝓜.D.child p.2) (𝓜.D.child y))
              (𝓜.C.child p.1) ≤
          memB (𝓜.D.child p.2) 𝓜.D ⊓ memB (𝓜.D.child y) 𝓜.D := by
      have hsub : memB (𝓜.C.child p.1) 𝓜.C ≤
          subsetB (𝓜.C.child p.1) (prodB 𝓜.D 𝓜.D) :=
        hfun.trans (inf_le_left.trans inf_le_left)
      have hm := (memB_of_subsetB
        (opairB (𝓜.D.child p.2) (𝓜.D.child y))
        (𝓜.C.child p.1) (prodB 𝓜.D 𝓜.D)).trans' <|
          le_inf inf_le_right (inf_le_left.trans hsub)
      rwa [memB_opairB_prodB] at hm
    change _ ≤ (oid 𝓜.D).eq y₁ y₂
    rw [oid_eq]
    refine le_inf (le_inf ?_ ?_) ?_
    · exact inf_le_left.trans (hsupport y₁) |>.trans inf_le_right
    · exact inf_le_right.trans (hsupport y₂) |>.trans inf_le_right
    · exact hsv.trans' <| le_inf
        (le_inf
          (inf_le_left.trans inf_le_left |>.trans hfun |>.trans
            (inf_le_left.trans inf_le_right))
          (inf_le_left.trans inf_le_right))
        (inf_le_right.trans inf_le_right)
  total := by
    intro p
    change (oid 𝓜.C).eps p.1 ⊓ (oid 𝓜.D).eps p.2 ≤
      ⨆ y, memB (𝓜.C.child p.1) 𝓜.C ⊓
        memB (opairB (𝓜.D.child p.2) (𝓜.D.child y))
          (𝓜.C.child p.1)
    rw [oid_eps, oid_eps]
    have hfun := 𝓜.mem_mapSpace_le_function (𝓜.C.child p.1)
    have htotal := isTotalB_apply (𝓜.C.child p.1) 𝓜.D
      (𝓜.D.child p.2)
    have hgraph : memB (𝓜.C.child p.1) 𝓜.C ⊓
        memB (𝓜.D.child p.2) 𝓜.D ≤
        ⨆ y, memB (opairB (𝓜.D.child p.2) (𝓜.D.child y))
          (𝓜.C.child p.1) := by
      have hall := htotal.trans' (le_inf
        (inf_le_left.trans hfun |>.trans
          inf_le_right)
        inf_le_right)
      refine (le_inf inf_le_left hall).trans ?_
      rw [inf_iSup_eq]
      refine iSup_le fun y => ?_
      exact (inf_memB_opairB_le_iSup_child
        (hfun.trans (inf_le_left.trans inf_le_left))
        (𝓜.D.child p.2) y)
    refine (le_inf inf_le_left hgraph).trans ?_
    rw [inf_iSup_eq]

/-- Application of two generalized elements, assembled entirely by
composition in `SetoidR_A`. -/
noncomputable def applyRelOfElements
    (𝓜 : InternalReflexiveModel (A := A))
    {a b : A} {r s : 𝓜.D.idx → A}
    (hr : IsRelElementAt 𝓜.D a r)
    (hs : IsRelElementAt 𝓜.D b s) :
    RelFun ((extentSetoid a).prod (extentSetoid b)) (oid 𝓜.D) :=
  𝓜.evalRel.comp <|
    ((oidRel 𝓜.D 𝓜.C 𝓜.Fun 𝓜.fun_function).prod
      (RelFun.id (oid 𝓜.D))).comp <|
        (relFunOfIsRelElementAt hr).prod (relFunOfIsRelElementAt hs)

@[simp] theorem applyRelOfElements_val
    (𝓜 : InternalReflexiveModel (A := A))
    {a b : A} {r s : 𝓜.D.idx → A}
    (hr : IsRelElementAt 𝓜.D a r)
    (hs : IsRelElementAt 𝓜.D b s)
    (i : PUnit.{u + 1} × PUnit.{u + 1}) (d : 𝓜.D.idx) :
    (applyRelOfElements 𝓜 hr hs).val i d =
      ⨆ c : 𝓜.C.idx, ⨆ q' : 𝓜.D.idx, ⨆ p : 𝓜.D.idx,
        ⨆ q : 𝓜.D.idx,
          r p ⊓ s q ⊓
          memB (opairB (𝓜.D.child p) (𝓜.C.child c)) 𝓜.Fun ⊓
          (oid 𝓜.D).eq q q' ⊓
          memB (𝓜.C.child c) 𝓜.C ⊓
          memB (opairB (𝓜.D.child q') (𝓜.D.child d))
            (𝓜.C.child c) := by
  simp only [applyRelOfElements, RelFun.comp_val, RelFun.prod_val,
    relFunOfIsRelElementAt_val, oidRel_val, RelFun.id,
    InternalReflexiveModel.evalRel]
  simp_rw [iSup_prod]
  simp_rw [iSup_inf_eq]
  apply iSup_congr
  intro c
  apply iSup_congr
  intro q'
  apply iSup_congr
  intro p
  apply iSup_congr
  intro q
  ac_rfl

/-- Application case of the extent-indexed fundamental relation lemma. -/
theorem interpDKRelVal_app_isRelElementAt
    (𝓜 : InternalReflexiveModel (A := A))
    (V K : AName.{u} A) (hK : subsetB K 𝓜.D = ⊤)
    (hV : (oid V).IsTotal)
    (η : RelFun (oid V) (oid 𝓜.D))
    (P Q : LamDK V.idx K.idx)
    (hP : IsRelElementAt 𝓜.D (lamDKVal V K P)
      (interpDKRelVal 𝓜 V K hK hV η P))
    (hQ : IsRelElementAt 𝓜.D (lamDKVal V K Q)
      (interpDKRelVal 𝓜 V K hK hV η Q)) :
    IsRelElementAt 𝓜.D (lamDKVal V K (.app P Q))
      (interpDKRelVal 𝓜 V K hK hV η (.app P Q)) := by
  let f := applyRelOfElements 𝓜 hP hQ
  have h := isRelElementAt_of_relFun
    (f.at (PUnit.unit, PUnit.unit))
  change IsRelElementAt 𝓜.D
    (lamDKVal V K P ⊓ lamDKVal V K Q)
    (fun d => f.val (PUnit.unit, PUnit.unit) d) at h
  change IsRelElementAt 𝓜.D
    (lamDKVal V K P ⊓ lamDKVal V K Q) _
  have heval :
      interpDKRelVal 𝓜 V K hK hV η (.app P Q) =
        fun d => f.val (PUnit.unit, PUnit.unit) d := by
    funext d
    rw [interpDKRelVal_app]
    exact (applyRelOfElements_val 𝓜 hP hQ
      (PUnit.unit, PUnit.unit) d).symm
  rw [heval]
  exact h

end Scott2026
