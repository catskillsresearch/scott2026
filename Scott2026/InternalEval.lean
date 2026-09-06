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

/-- Scott continuity entails membership in the exact internal map space at
the same Boolean degree. -/
theorem InternalReflexiveModel.scottContinuous_le_mem_mapSpace
    (𝓜 : InternalReflexiveModel (A := A)) (F : AName.{u} A) :
    isScottContinuousB F 𝓜.D 𝓜.D 𝓜.R 𝓜.R ≤ memB F 𝓜.C := by
  have hall := (inf_eq_top_iff.mp 𝓜.mapSpace_valid).2
  have hF := iInf_eq_top.mp hall F
  exact himp_eq_top_iff.mp (inf_eq_top_iff.mp hF).2

/-- Equality at a Boolean degree transports membership at that degree. -/
theorem inf_eqB_memB_le_memB
    (a : A) (F G C : AName.{u} A) :
    a ⊓ eqB F G ⊓ memB G C ≤ memB F C := by
  rw [eqB_comm F G]
  exact (memB_eqB_left G C F).trans' <| by
    exact le_inf inf_le_right
      (inf_le_left.trans inf_le_right)

/-- Two complementary local proofs cover the full Boolean truth value. -/
theorem eq_top_of_degree_compl_le {a p : A}
    (ha : a ≤ p) (hac : aᶜ ≤ p) : p = ⊤ := by
  apply top_unique
  rw [← sup_compl_eq_top]
  exact sup_le ha hac

/-- Scott continuity can be glued from complementary Boolean pieces by first
gluing membership in the exact internal continuous-map space. -/
theorem InternalReflexiveModel.scottContinuous_of_mapSpace_cover
    (𝓜 : InternalReflexiveModel (A := A)) (F : AName.{u} A) (a : A)
    (ha : a ≤ memB F 𝓜.C) (hac : aᶜ ≤ memB F 𝓜.C) :
    isScottContinuousB F 𝓜.D 𝓜.D 𝓜.R 𝓜.R = ⊤ := by
  have hmem : memB F 𝓜.C = ⊤ :=
    eq_top_of_degree_compl_le ha hac
  apply top_unique
  exact (𝓜.mem_mapSpace_le_scottContinuous F).trans' <| by rw [hmem]

/-- Internal relations respect Boolean equality in both arguments. -/
theorem relB_congr (R x x' y y' : AName.{u} A) :
    eqB x x' ⊓ eqB y y' ⊓ relB R x y ≤ relB R x' y' := by
  unfold relB
  exact memB_opairB_congr R x x' y y'

/-- Reflexivity of the internal dcpo order, localized at membership in `D`. -/
theorem InternalReflexiveModel.mem_le_rel_self
    (𝓜 : InternalReflexiveModel (A := A)) (x : AName.{u} A) :
    memB x 𝓜.D ≤ relB 𝓜.R x x := by
  have hdc := 𝓜.dcpo_valid
  unfold isDcpoWithBottomB at hdc
  have hpo := (inf_eq_top_iff.mp (inf_eq_top_iff.mp hdc).1).1
  unfold isPartialOrderB at hpo
  have hrefl :=
    (inf_eq_top_iff.mp
      (inf_eq_top_iff.mp
        (inf_eq_top_iff.mp hpo).1).1).2
  exact himp_eq_top_iff.mp (iInf_eq_top.mp hrefl x)

/-- Transitivity of the internally valid order on `D`. -/
theorem InternalReflexiveModel.relR_trans
    (𝓜 : InternalReflexiveModel (A := A))
    (x y z : AName.{u} A) :
    relB 𝓜.R x y ⊓ relB 𝓜.R y z ≤ relB 𝓜.R x z := by
  have hdc := 𝓜.dcpo_valid
  unfold isDcpoWithBottomB at hdc
  have hpo := (inf_eq_top_iff.mp (inf_eq_top_iff.mp hdc).1).1
  unfold isPartialOrderB at hpo
  have htrans := (inf_eq_top_iff.mp hpo).2
  have hx := iInf_eq_top.mp htrans x
  have hy := iInf_eq_top.mp hx y
  have hz := iInf_eq_top.mp hy z
  exact himp_eq_top_iff.mp hz

/-- A function whose outputs are all equal at degree `a` is Scott-continuous
at that degree.  The directed-supremum argument uses nonemptiness to select an
input at which the alleged upper bound can be tested. -/
theorem InternalReflexiveModel.constantMap_le_scottContinuous
    (𝓜 : InternalReflexiveModel (A := A))
    (F : AName.{u} A) (a : A)
    (hfun : a ≤ isFunctionB F 𝓜.D 𝓜.D)
    (hconst : ∀ x x' y y' : AName.{u} A,
      a ⊓ memB (opairB x y) F ⊓ memB (opairB x' y') F ≤ eqB y y') :
    a ≤ isScottContinuousB F 𝓜.D 𝓜.D 𝓜.R 𝓜.R := by
  have hout (x y : AName.{u} A) :
      a ⊓ memB (opairB x y) F ≤ memB y 𝓜.D := by
    have hsub : a ≤ subsetB F (prodB 𝓜.D 𝓜.D) :=
      hfun.trans (inf_le_left.trans inf_le_left)
    have hm := (memB_of_subsetB (opairB x y) F
      (prodB 𝓜.D 𝓜.D)).trans' <|
        le_inf inf_le_right (inf_le_left.trans hsub)
    rw [memB_opairB_prodB] at hm
    exact hm.trans inf_le_right
  unfold isScottContinuousB
  refine le_inf (le_inf hfun ?_) ?_
  · refine le_iInf fun x => le_iInf fun x' =>
      le_iInf fun y => le_iInf fun y' => ?_
    rw [le_himp_iff]
    let t := a ⊓
      (memB (opairB x y) F ⊓ memB (opairB x' y') F ⊓
        relB 𝓜.R x x')
    change t ≤ relB 𝓜.R y y'
    have htA : t ≤ a := by dsimp [t]; exact inf_le_left
    have htFxy : t ≤ memB (opairB x y) F := by
      dsimp [t]
      exact inf_le_right.trans (inf_le_left.trans inf_le_left)
    have htFx'y' : t ≤ memB (opairB x' y') F := by
      dsimp [t]
      exact inf_le_right.trans (inf_le_left.trans inf_le_right)
    have hyy' : t ≤ eqB y y' :=
      (hconst x x' y y').trans' <| le_inf
        (le_inf htA htFxy) htFx'y'
    have hyD : t ≤ memB y 𝓜.D :=
      (hout x y).trans' (le_inf htA htFxy)
    exact (relB_congr 𝓜.R y y y y').trans' <| le_inf
      (le_inf (le_top.trans (eqB_self (A := A) y).ge) hyy')
      (hyD.trans (𝓜.mem_le_rel_self y))
  · refine le_iInf fun S => le_iInf fun x => le_iInf fun y => ?_
    rw [le_himp_iff]
    unfold mapsToSupB
    refine le_inf ?_ ?_
    · refine le_iInf fun w => le_iInf fun z => ?_
      rw [le_himp_iff]
      let t := (a ⊓
          (isDirectedRelB S 𝓜.D 𝓜.R ⊓ isSupRelB x S 𝓜.R ⊓
            memB (opairB x y) F)) ⊓
        (memB w S ⊓ memB (opairB w z) F)
      change t ≤ relB 𝓜.R z y
      have htA : t ≤ a := by
        dsimp [t]
        exact inf_le_left.trans inf_le_left
      have htFxy : t ≤ memB (opairB x y) F := by
        dsimp [t]
        exact inf_le_left.trans (inf_le_right.trans inf_le_right)
      have htFwz : t ≤ memB (opairB w z) F := by
        dsimp [t]
        exact inf_le_right.trans inf_le_right
      have hzy : t ≤ eqB z y :=
        (hconst w x z y).trans' <| le_inf
          (le_inf htA htFwz) htFxy
      have hzD : t ≤ memB z 𝓜.D :=
        (hout w z).trans' (le_inf htA htFwz)
      exact (relB_congr 𝓜.R z z z y).trans' <| le_inf
        (le_inf (le_top.trans (eqB_self (A := A) z).ge) hzy)
        (hzD.trans (𝓜.mem_le_rel_self z))
    · refine le_iInf fun u => ?_
      rw [le_himp_iff]
      let upper :=
        ⨅ w : AName A, ⨅ z : AName A,
          memB w S ⊓ memB (opairB w z) F ⇨ relB 𝓜.R z u
      let t := (a ⊓
          (isDirectedRelB S 𝓜.D 𝓜.R ⊓ isSupRelB x S 𝓜.R ⊓
            memB (opairB x y) F)) ⊓ upper
      change t ≤ relB 𝓜.R y u
      have htA : t ≤ a := by
        dsimp [t]
        exact inf_le_left.trans inf_le_left
      have htDir : t ≤ isDirectedRelB S 𝓜.D 𝓜.R := by
        dsimp [t]
        exact inf_le_left.trans (inf_le_right.trans
          (inf_le_left.trans inf_le_left))
      have htFxy : t ≤ memB (opairB x y) F := by
        dsimp [t]
        exact inf_le_left.trans (inf_le_right.trans inf_le_right)
      have htUpper : t ≤ upper := by
        dsimp [t]
        exact inf_le_right
      have hnonempty :
          isDirectedRelB S 𝓜.D 𝓜.R ≤
            ⨆ w : AName A, memB w S := by
        unfold isDirectedRelB
        exact inf_le_left.trans inf_le_right
      refine (le_inf le_rfl (htDir.trans hnonempty)).trans ?_
      rw [inf_iSup_eq]
      refine iSup_le fun w => ?_
      let tw := t ⊓ memB w S
      change tw ≤ relB 𝓜.R y u
      have htwT : tw ≤ t := by dsimp [tw]; exact inf_le_left
      have htwMem : tw ≤ memB w S := by dsimp [tw]; exact inf_le_right
      have hsub :
          isDirectedRelB S 𝓜.D 𝓜.R ≤ subsetB S 𝓜.D := by
        unfold isDirectedRelB
        exact inf_le_left.trans inf_le_left
      have hwD : tw ≤ memB w 𝓜.D := by
        exact (memB_of_subsetB w S 𝓜.D).trans' <| le_inf
          htwMem (htwT.trans htDir |>.trans hsub)
      have htotal :
          isFunctionB F 𝓜.D 𝓜.D ⊓ memB w 𝓜.D ≤
            ⨆ z : AName A, memB (opairB w z) F :=
        (isTotalB_apply F 𝓜.D w).trans' <| le_inf
          (inf_le_left.trans inf_le_right) inf_le_right
      have hex : tw ≤ ⨆ z : AName A, memB (opairB w z) F :=
        htotal.trans' <| le_inf
          (htwT.trans htA |>.trans hfun) hwD
      refine (le_inf le_rfl hex).trans ?_
      rw [inf_iSup_eq]
      refine iSup_le fun z => ?_
      let twz := tw ⊓ memB (opairB w z) F
      change twz ≤ relB 𝓜.R y u
      have htwzT : twz ≤ t := by
        dsimp [twz, tw]
        exact inf_le_left.trans inf_le_left
      have htwzMemW : twz ≤ memB w S := by
        dsimp [twz, tw]
        exact inf_le_left.trans inf_le_right
      have htwzFwz : twz ≤ memB (opairB w z) F := by
        dsimp [twz]
        exact inf_le_right
      have hzu : twz ≤ relB 𝓜.R z u := by
        have hall := iInf_le
          (fun q : AName A => ⨅ v : AName A,
            memB q S ⊓ memB (opairB q v) F ⇨ relB 𝓜.R v u) w
        have hall' := (iInf_le
          (fun v : AName A =>
            memB w S ⊓ memB (opairB w v) F ⇨ relB 𝓜.R v u) z).trans' hall
        exact (le_himp_iff.mp hall').trans' <| le_inf
          (htwzT.trans htUpper) (le_inf htwzMemW htwzFwz)
      have hyz : twz ≤ eqB y z :=
        (hconst x w y z).trans' <| le_inf
          (le_inf (htwzT.trans htA) (htwzT.trans htFxy)) htwzFwz
      have hzy : twz ≤ eqB z y := by
        rw [eqB_comm]
        exact hyz
      exact (relB_congr 𝓜.R z y u u).trans' <| le_inf
        (le_inf hzy (le_top.trans (eqB_self (A := A) u).ge)) hzu

/-- A degree-local constant map belongs to the exact internal continuous-map
space at that degree. -/
theorem InternalReflexiveModel.constantMap_le_mapSpace
    (𝓜 : InternalReflexiveModel (A := A))
    (F : AName.{u} A) (a : A)
    (hfun : a ≤ isFunctionB F 𝓜.D 𝓜.D)
    (hconst : ∀ x x' y y' : AName.{u} A,
      a ⊓ memB (opairB x y) F ⊓ memB (opairB x' y') F ≤ eqB y y') :
    a ≤ memB F 𝓜.C :=
  (𝓜.constantMap_le_scottContinuous F a hfun hconst).trans
    (𝓜.scottContinuous_le_mem_mapSpace F)

/-- Raw graph of a constant generalized element. -/
noncomputable def constantRowGraph
    (D : AName.{u} A) (r : D.idx → A) : AName.{u} A :=
  mk (D.idx × D.idx)
    (fun p => opairB (D.child p.1) (D.child p.2))
    (fun p => r p.2)

/-- A generalized element gives a degree-local internal constant function. -/
theorem constantRowGraph_le_isFunctionB
    (D : AName.{u} A) (hD : (oid D).IsTotal)
    {a : A} {r : D.idx → A} (hr : IsRelElementAt D a r) :
    a ≤ isFunctionB (constantRowGraph D r) D D := by
  unfold isFunctionB
  refine le_inf (le_inf ?_ ?_) ?_
  · unfold constantRowGraph
    rw [subsetB_mk]
    refine le_iInf fun p => ?_
    rw [le_himp_iff, memB_opairB_prodB]
    have hp : r p.2 ≤ memB (D.child p.2) D := by
      have h := (hr.2.1 p.2).trans inf_le_right
      rwa [oid_eps] at h
    have hi : memB (D.child p.1) D = ⊤ := by
      rw [← oid_eps]
      exact hD p.1
    rw [hi, top_inf_eq]
    exact inf_le_right.trans hp
  · refine le_iInf fun x => le_iInf fun y => le_iInf fun z => ?_
    rw [le_himp_iff, constantRowGraph, memB_mk, memB_mk,
      inf_iSup_eq]
    rw [inf_iSup_eq]
    apply iSup_le
    intro p
    rw [← inf_assoc, inf_iSup_eq]
    rw [iSup_inf_eq]
    apply iSup_le
    intro q
    rw [eqB_opairB, eqB_opairB]
    let t :=
      a ⊓
        (eqB x (D.child q.1) ⊓ eqB y (D.child q.2) ⊓ r q.2) ⊓
          (eqB x (D.child p.1) ⊓ eqB z (D.child p.2) ⊓ r p.2)
    change t ≤ eqB y z
    have hyq : t ≤ eqB y (D.child q.2) := by
      dsimp [t]
      exact inf_le_left.trans
        (inf_le_right.trans (inf_le_left.trans inf_le_right))
    have hzp : t ≤ eqB (D.child p.2) z := by
      have h : t ≤ eqB z (D.child p.2) := by
        dsimp [t]
        exact inf_le_right.trans (inf_le_left.trans inf_le_right)
      rwa [eqB_comm] at h
    have hqp : t ≤ eqB (D.child q.2) (D.child p.2) := by
      have hrq : t ≤ r q.2 := by
        dsimp [t]
        exact inf_le_left.trans (inf_le_right.trans inf_le_right)
      have hrp : t ≤ r p.2 := by
        dsimp [t]
        exact inf_le_right.trans inf_le_right
      have h : t ≤ (oid D).eq q.2 p.2 :=
        (hr.2.2.1 q.2 p.2).trans' (le_inf hrq hrp)
      rw [oid_eq] at h
      exact h.trans inf_le_right
    exact (eqB_trans y (D.child q.2) z).trans' <| le_inf hyq <|
      (eqB_trans (D.child q.2) (D.child p.2) z).trans' <|
        le_inf hqp hzp
  · refine le_iInf fun x => ?_
    rw [le_himp_iff]
    refine (le_inf inf_le_right (inf_le_left.trans hr.2.2.2)).trans ?_
    rw [memB_eq (x := x) (y := D), iSup_inf_eq]
    refine iSup_le fun i => ?_
    rw [inf_iSup_eq]
    refine iSup_le fun j => le_iSup_of_le (D.child j) ?_
    unfold constantRowGraph
    rw [memB_mk]
    refine le_iSup_of_le (i, j) ?_
    rw [eqB_opairB, eqB_self, inf_top_eq]
    exact le_inf (inf_le_left.trans inf_le_left) inf_le_right

/-- Outputs of a raw constant graph are equal independently of their inputs,
at the generalized element's active degree. -/
theorem constantRowGraph_outputs_eq
    (D : AName.{u} A) {a : A} {r : D.idx → A}
    (hr : IsRelElementAt D a r)
    (x x' y y' : AName.{u} A) :
    a ⊓ memB (opairB x y) (constantRowGraph D r) ⊓
        memB (opairB x' y') (constantRowGraph D r) ≤ eqB y y' := by
  rw [constantRowGraph, memB_mk, memB_mk, inf_iSup_eq]
  apply iSup_le
  intro p
  rw [inf_iSup_eq, iSup_inf_eq]
  apply iSup_le
  intro q
  rw [eqB_opairB, eqB_opairB]
  let t :=
    a ⊓
      (eqB x (D.child q.1) ⊓ eqB y (D.child q.2) ⊓ r q.2) ⊓
        (eqB x' (D.child p.1) ⊓ eqB y' (D.child p.2) ⊓ r p.2)
  change t ≤ eqB y y'
  have hyq : t ≤ eqB y (D.child q.2) := by
    dsimp [t]
    exact inf_le_left.trans
      (inf_le_right.trans (inf_le_left.trans inf_le_right))
  have hy'p : t ≤ eqB (D.child p.2) y' := by
    have h : t ≤ eqB y' (D.child p.2) := by
      dsimp [t]
      exact inf_le_right.trans (inf_le_left.trans inf_le_right)
    rwa [eqB_comm] at h
  have hqp : t ≤ eqB (D.child q.2) (D.child p.2) := by
    have hrq : t ≤ r q.2 := by
      dsimp [t]
      exact inf_le_left.trans (inf_le_right.trans inf_le_right)
    have hrp : t ≤ r p.2 := by
      dsimp [t]
      exact inf_le_right.trans inf_le_right
    have h : t ≤ (oid D).eq q.2 p.2 :=
      (hr.2.2.1 q.2 p.2).trans' (le_inf hrq hrp)
    rw [oid_eq] at h
    exact h.trans inf_le_right
  exact (eqB_trans y (D.child q.2) y').trans' <| le_inf hyq <|
    (eqB_trans (D.child q.2) (D.child p.2) y').trans' <|
      le_inf hqp hy'p

/-- Raw constant rows are Scott-continuous at their generalized extent. -/
theorem InternalReflexiveModel.constantRowGraph_le_scottContinuous
    (𝓜 : InternalReflexiveModel (A := A))
    {a : A} {r : 𝓜.D.idx → A} (hr : IsRelElementAt 𝓜.D a r) :
    a ≤ isScottContinuousB (constantRowGraph 𝓜.D r)
      𝓜.D 𝓜.D 𝓜.R 𝓜.R :=
  𝓜.constantMap_le_scottContinuous _ a
    (constantRowGraph_le_isFunctionB 𝓜.D 𝓜.total hr)
    (constantRowGraph_outputs_eq 𝓜.D hr)

/-- Constant syntax produces exactly the raw constant graph of its interpreted
generalized element. -/
theorem interpDKBodyGraph_const_eq_constantRowGraph
    (𝓜 : InternalReflexiveModel (A := A))
    (V K : AName.{u} A) (hK : subsetB K 𝓜.D = ⊤)
    (hV : (oid V).IsTotal)
    (η : RelFun (oid V) (oid 𝓜.D))
    (x : V.idx) (k : K.idx) :
    interpDKBodyGraph 𝓜 V K hK hV η x (.const k) =
      constantRowGraph 𝓜.D
        (fun d => (oidSubsetRel K 𝓜.D hK).val k d) := by
  unfold interpDKBodyGraph constantRowGraph
  congr 1
  funext p
  rw [interpDKRelVal_const]

/-- Degree-indexed Scott continuity for constant-term body graphs. -/
theorem interpDKBodyGraph_const_le_scottContinuous
    (𝓜 : InternalReflexiveModel (A := A))
    (V K : AName.{u} A) (hK : subsetB K 𝓜.D = ⊤)
    (hV : (oid V).IsTotal)
    (η : RelFun (oid V) (oid 𝓜.D))
    (x : V.idx) (k : K.idx) :
    lamDKVal V K (.const k) ≤
      isScottContinuousB
        (interpDKBodyGraph 𝓜 V K hK hV η x (.const k))
        𝓜.D 𝓜.D 𝓜.R 𝓜.R := by
  rw [interpDKBodyGraph_const_eq_constantRowGraph]
  have hr :=
    interpDKRelVal_const_isRelElementAt 𝓜 V K hK hV η k
  have heval :
      interpDKRelVal 𝓜 V K hK hV η (.const k) =
        fun d => (oidSubsetRel K 𝓜.D hK).val k d := by
    funext d
    rw [interpDKRelVal_const]
  rw [heval] at hr
  exact 𝓜.constantRowGraph_le_scottContinuous
    hr

/-- Same-child names are equal at every degree at which their coefficients
transport in both directions. -/
theorem le_eqB_mk_same_children {I : Type u}
    (child : I → AName.{u} A) (v w : I → A) (a : A)
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

/-- A variable body is locally the identity on the equality part of update,
and locally the old environment row on the complementary part. -/
theorem interpDKBodyGraph_var_local_eq
    (𝓜 : InternalReflexiveModel (A := A))
    (V K : AName.{u} A) (hK : subsetB K 𝓜.D = ⊤)
    (hV : (oid V).IsTotal)
    (η : RelFun (oid V) (oid 𝓜.D)) (x y : V.idx) :
    let e := (oid V).eq y x
    e ≤ eqB
      (interpDKBodyGraph 𝓜 V K hK hV η x (.var y))
      (interpDKBodyGraph 𝓜 V K hK hV η x (.var x)) ∧
    eᶜ ≤ eqB
      (interpDKBodyGraph 𝓜 V K hK hV η x (.var y))
      (constantRowGraph 𝓜.D (fun d => η.val y d)) := by
  dsimp
  constructor
  · refine le_eqB_mk_same_children
      (fun p : 𝓜.D.idx × 𝓜.D.idx =>
        opairB (𝓜.D.child p.1) (𝓜.D.child p.2)) _ _ _ ?_ ?_
    · intro p
      rw [interpDKRelVal_var, interpDKRelVal_var]
      exact (η.update hV 𝓜.total x p.1).subst_left y x p.2
    · intro p
      rw [interpDKRelVal_var, interpDKRelVal_var]
      have h := (η.update hV 𝓜.total x p.1).subst_left x y p.2
      rwa [(oid V).symm x y] at h
  · refine le_eqB_mk_same_children
      (fun p : 𝓜.D.idx × 𝓜.D.idx =>
        opairB (𝓜.D.child p.1) (𝓜.D.child p.2)) _ _ _ ?_ ?_
    · intro p
      rw [interpDKRelVal_var, RelFun.update_val, inf_sup_left]
      refine sup_le ?_ ?_
      · exact (show ((oid V).eq y x)ᶜ ⊓
            ((oid V).eq y x ⊓ (oid 𝓜.D).eq p.1 p.2) ≤ ⊥ by
          calc
            _ ≤ ((oid V).eq y x)ᶜ ⊓ (oid V).eq y x :=
              le_inf inf_le_left (inf_le_right.trans inf_le_left)
            _ = ⊥ := compl_inf_self _).trans bot_le
      · exact inf_le_right.trans inf_le_right
    · intro p
      rw [interpDKRelVal_var, RelFun.update_val]
      exact le_sup_of_le_right le_rfl

/-- The identity graph is Scott-continuous in every internally valid dcpo. -/
theorem InternalReflexiveModel.id_scottContinuous
    (𝓜 : InternalReflexiveModel (A := A)) :
    isScottContinuousB (idB 𝓜.D) 𝓜.D 𝓜.D 𝓜.R 𝓜.R = ⊤ := by
  unfold isScottContinuousB
  refine inf_eq_top_iff.mpr ⟨inf_eq_top_iff.mpr
    ⟨isFunctionB_id 𝓜.D, ?_⟩, ?_⟩
  · refine iInf_eq_top.mpr fun x => iInf_eq_top.mpr fun x' =>
      iInf_eq_top.mpr fun y => iInf_eq_top.mpr fun y' =>
        himp_eq_top_iff.mpr ?_
    rw [memB_opairB_idB, memB_opairB_idB]
    exact (relB_congr 𝓜.R x y x' y').trans' <| by
      refine le_inf (le_inf ?_ ?_) inf_le_right
      · exact inf_le_left.trans (inf_le_left.trans inf_le_right)
      · exact inf_le_left.trans (inf_le_right.trans inf_le_right)
  · refine iInf_eq_top.mpr fun S => iInf_eq_top.mpr fun x =>
      iInf_eq_top.mpr fun y => himp_eq_top_iff.mpr ?_
    unfold mapsToSupB
    refine le_inf ?_ ?_
    · refine le_iInf fun w => le_iInf fun z => ?_
      rw [le_himp_iff, memB_opairB_idB]
      have hsup :
          isSupRelB x S 𝓜.R ≤ isUpperBoundRelB x S 𝓜.R :=
        inf_le_left
      have hub :
          isUpperBoundRelB x S 𝓜.R ⊓ memB w S ≤ relB 𝓜.R w x := by
        exact le_himp_iff.mp (iInf_le
          (fun q : AName A => memB q S ⇨ relB 𝓜.R q x) w)
      have hwz :
          memB (opairB w z) (idB 𝓜.D) ≤ eqB w z := by
        rw [memB_opairB_idB]
        exact inf_le_right
      exact (relB_congr 𝓜.R w z x y).trans' <| by
        refine le_inf (le_inf ?_ ?_) ?_
        · exact inf_le_right.trans inf_le_right |>.trans hwz
        · exact inf_le_left.trans (inf_le_right.trans inf_le_right)
        · exact hub.trans' <| le_inf
            (inf_le_left.trans (inf_le_left.trans inf_le_right) |>.trans hsup)
            (inf_le_right.trans inf_le_left)
    · refine le_iInf fun u => ?_
      rw [le_himp_iff]
      have hleast :
          isSupRelB x S 𝓜.R ⊓ isUpperBoundRelB u S 𝓜.R ≤
            relB 𝓜.R x u := by
        exact (le_himp_iff.mp (iInf_le
          (fun q : AName A =>
            isUpperBoundRelB q S 𝓜.R ⇨ relB 𝓜.R x q) u)).trans' <|
              le_inf (inf_le_left.trans inf_le_right) inf_le_right
      have hubu :
          (⨅ w : AName A, ⨅ z : AName A,
              memB w S ⊓ memB (opairB w z) (idB 𝓜.D) ⇨
                relB 𝓜.R z u) ⊓
              isDirectedRelB S 𝓜.D 𝓜.R ≤
            isUpperBoundRelB u S 𝓜.R := by
        refine le_iInf fun w => ?_
        rw [le_himp_iff]
        let t :=
          ((⨅ q : AName A, ⨅ z : AName A,
              memB q S ⊓ memB (opairB q z) (idB 𝓜.D) ⇨
                relB 𝓜.R z u) ⊓
            isDirectedRelB S 𝓜.D 𝓜.R) ⊓ memB w S
        change t ≤ relB 𝓜.R w u
        have htAll :
            t ≤ ⨅ q : AName A, ⨅ z : AName A,
              memB q S ⊓ memB (opairB q z) (idB 𝓜.D) ⇨
                relB 𝓜.R z u := by
          dsimp [t]
          exact inf_le_left.trans inf_le_left
        have htDir : t ≤ isDirectedRelB S 𝓜.D 𝓜.R := by
          dsimp [t]
          exact inf_le_left.trans inf_le_right
        have htMem : t ≤ memB w S := by
          dsimp [t]
          exact inf_le_right
        have hsub :
            isDirectedRelB S 𝓜.D 𝓜.R ≤ subsetB S 𝓜.D := by
          unfold isDirectedRelB
          exact inf_le_left.trans inf_le_left
        have hwD' :
            subsetB S 𝓜.D ⊓ memB w S ≤ memB w 𝓜.D :=
          by rw [inf_comm]; exact memB_of_subsetB w S 𝓜.D
        have hid :
            memB w 𝓜.D ≤ memB (opairB w w) (idB 𝓜.D) := by
          rw [memB_opairB_idB, eqB_self, inf_top_eq]
        have hall := iInf_le
          (fun q : AName A => ⨅ z : AName A,
            memB q S ⊓ memB (opairB q z) (idB 𝓜.D) ⇨
              relB 𝓜.R z u) w
        have hall' := (iInf_le
          (fun z : AName A =>
            memB w S ⊓ memB (opairB w z) (idB 𝓜.D) ⇨
              relB 𝓜.R z u) w).trans' hall
        exact (le_himp_iff.mp hall').trans' <| by
          refine le_inf htAll (le_inf htMem ?_)
          exact (hwD'.trans' <|
            le_inf (htDir.trans hsub) htMem).trans hid
      exact (relB_congr 𝓜.R x y u u).trans' <| by
        refine le_inf (le_inf ?_ ?_) ?_
        · have hxy :
              memB (opairB x y) (idB 𝓜.D) ≤ eqB x y := by
            rw [memB_opairB_idB]
            exact inf_le_right
          exact inf_le_left.trans inf_le_right |>.trans hxy
        · exact le_top.trans (eqB_self (A := A) u).ge
        · exact hleast.trans' <| le_inf
            (inf_le_left.trans (inf_le_left.trans inf_le_right))
            (hubu.trans' <| le_inf inf_le_right
              (inf_le_left.trans (inf_le_left.trans inf_le_left)))

/-- The body graph of the overwritten variable is the identity relation,
extensionally in the Boolean-valued universe. -/
theorem interpDKBodyGraph_var_eq_id
    (𝓜 : InternalReflexiveModel (A := A))
    (V K : AName.{u} A) (hK : subsetB K 𝓜.D = ⊤)
    (hV : (oid V).IsTotal)
    (η : RelFun (oid V) (oid 𝓜.D)) (x : V.idx) :
    eqB (interpDKBodyGraph 𝓜 V K hK hV η x (.var x))
      (idB 𝓜.D) = ⊤ := by
  have hgraph :
      interpDKBodyGraph 𝓜 V K hK hV η x (.var x) =
        relFunGraphName 𝓜.D 𝓜.D (RelFun.id (oid 𝓜.D)) := by
    unfold interpDKBodyGraph relFunGraphName
    congr 1
    funext p
    rw [interpDKRelVal_var, RelFun.update_self]
    rfl
  rw [hgraph]
  apply eqB_top_of_function_matrix
    (isFunctionB_relFunGraphName 𝓜.D 𝓜.D (RelFun.id (oid 𝓜.D)))
    (isFunctionB_id 𝓜.D)
  intro i j
  rw [memB_opairB_relFunGraphName, memB_opairB_idB]
  change (oid 𝓜.D).eq i j =
    memB (𝓜.D.child i) 𝓜.D ⊓ eqB (𝓜.D.child i) (𝓜.D.child j)
  have hi : memB (𝓜.D.child i) 𝓜.D = ⊤ := by
    rw [← oid_eps]
    exact 𝓜.total i
  have hj : memB (𝓜.D.child j) 𝓜.D = ⊤ := by
    rw [← oid_eps]
    exact 𝓜.total j
  rw [oid_eq, hi, hj, top_inf_eq]

/-- Degree-indexed Scott continuity of the body-variable map in the branch
where the body variable is the overwritten abstraction variable. -/
theorem interpDKBodyGraph_var_scottContinuous
    (𝓜 : InternalReflexiveModel (A := A))
    (V K : AName.{u} A) (hK : subsetB K 𝓜.D = ⊤)
    (hV : (oid V).IsTotal)
    (η : RelFun (oid V) (oid 𝓜.D)) (x : V.idx) :
    isScottContinuousB
      (interpDKBodyGraph 𝓜 V K hK hV η x (.var x))
      𝓜.D 𝓜.D 𝓜.R 𝓜.R = ⊤ := by
  let F := interpDKBodyGraph 𝓜 V K hK hV η x (.var x)
  have heq : eqB F (idB 𝓜.D) = ⊤ :=
    interpDKBodyGraph_var_eq_id 𝓜 V K hK hV η x
  have hidC : memB (idB 𝓜.D) 𝓜.C = ⊤ :=
    𝓜.mem_mapSpace_of_scottContinuous (idB 𝓜.D) 𝓜.id_scottContinuous
  have hFC : memB F 𝓜.C = ⊤ := by
    apply top_unique
    exact (memB_eqB_left (idB 𝓜.D) 𝓜.C F).trans' <| by
      rw [eqB_comm, heq, hidC, inf_top_eq]
  apply top_unique
  exact (𝓜.mem_mapSpace_le_scottContinuous F).trans' <| by rw [hFC]

/-- Scott continuity of every variable body graph.  Boolean equality with the
overwritten variable selects the identity branch; its complement selects the
constant old-environment row. -/
theorem interpDKBodyGraph_any_var_scottContinuous
    (𝓜 : InternalReflexiveModel (A := A))
    (V K : AName.{u} A) (hK : subsetB K 𝓜.D = ⊤)
    (hV : (oid V).IsTotal)
    (η : RelFun (oid V) (oid 𝓜.D)) (x y : V.idx) :
    isScottContinuousB
      (interpDKBodyGraph 𝓜 V K hK hV η x (.var y))
      𝓜.D 𝓜.D 𝓜.R 𝓜.R = ⊤ := by
  let e := (oid V).eq y x
  let F := interpDKBodyGraph 𝓜 V K hK hV η x (.var y)
  let I := interpDKBodyGraph 𝓜 V K hK hV η x (.var x)
  let C₀ := constantRowGraph 𝓜.D (fun d => η.val y d)
  have heq := interpDKBodyGraph_var_local_eq 𝓜 V K hK hV η x y
  change e ≤ eqB F I ∧ eᶜ ≤ eqB F C₀ at heq
  have hIC : memB I 𝓜.C = ⊤ := by
    apply top_unique
    exact (𝓜.scottContinuous_le_mem_mapSpace I).trans' <| by
      rw [show isScottContinuousB I 𝓜.D 𝓜.D 𝓜.R 𝓜.R = ⊤ from
        interpDKBodyGraph_var_scottContinuous 𝓜 V K hK hV η x]
  have hr : IsRelElementAt 𝓜.D ⊤ (fun d => η.val y d) := by
    have h := isRelElementAt_of_relFun (η.at y)
    rw [← hV y]
    simpa only [RelFun.at_val] using h
  have hC₀C : memB C₀ 𝓜.C = ⊤ := by
    apply top_unique
    exact (𝓜.scottContinuous_le_mem_mapSpace C₀).trans' <| by
      exact 𝓜.constantRowGraph_le_scottContinuous hr
  apply 𝓜.scottContinuous_of_mapSpace_cover F e
  · exact (inf_eqB_memB_le_memB e F I 𝓜.C).trans' <|
      le_inf (le_inf le_rfl heq.1) (le_top.trans hIC.ge)
  · exact (inf_eqB_memB_le_memB eᶜ F C₀ 𝓜.C).trans' <|
      le_inf (le_inf le_rfl heq.2) (le_top.trans hC₀C.ge)

/-- Membership in the internal continuous-map space entails the internal
function predicate, at the same Boolean degree. -/
theorem InternalReflexiveModel.mem_mapSpace_le_function
    (𝓜 : InternalReflexiveModel (A := A)) (F : AName.{u} A) :
    memB F 𝓜.C ≤ isFunctionB F 𝓜.D 𝓜.D := by
  have hcont := 𝓜.mem_mapSpace_le_scottContinuous F
  unfold isScottContinuousB at hcont
  exact hcont.trans (inf_le_left.trans inf_le_left)

/-- The internal order on `C` entails pointwise order at the same degree. -/
theorem InternalReflexiveModel.relQ_le_pointwise
    (𝓜 : InternalReflexiveModel (A := A))
    (F G : AName.{u} A) :
    memB F 𝓜.C ⊓ memB G 𝓜.C ⊓ relB 𝓜.Q F G ≤
      pointwiseLeB F G 𝓜.D 𝓜.R := by
  have hall := (inf_eq_top_iff.mp 𝓜.pointwise_valid).2
  have hFG := iInf_eq_top.mp (iInf_eq_top.mp hall F) G
  have houter := himp_eq_top_iff.mp hFG
  have hfwd :
      memB F 𝓜.C ⊓ memB G 𝓜.C ≤
        relB 𝓜.Q F G ⇨ pointwiseLeB F G 𝓜.D 𝓜.R :=
    houter.trans inf_le_left
  exact le_himp_iff.mp hfwd

/-- Pointwise comparison of two members of `C` entails their `Q`-order. -/
theorem InternalReflexiveModel.pointwise_le_relQ
    (𝓜 : InternalReflexiveModel (A := A))
    (F G : AName.{u} A) :
    memB F 𝓜.C ⊓ memB G 𝓜.C ⊓
        pointwiseLeB F G 𝓜.D 𝓜.R ≤
      relB 𝓜.Q F G := by
  have hall := (inf_eq_top_iff.mp 𝓜.pointwise_valid).2
  have hFG := iInf_eq_top.mp (iInf_eq_top.mp hall F) G
  have houter := himp_eq_top_iff.mp hFG
  have hrev :
      memB F 𝓜.C ⊓ memB G 𝓜.C ≤
        pointwiseLeB F G 𝓜.D 𝓜.R ⇨ relB 𝓜.Q F G :=
    houter.trans inf_le_right
  exact le_himp_iff.mp hrev

/-- Pointwise order compares outputs of two internal continuous maps at a
common argument. -/
theorem InternalReflexiveModel.relQ_apply
    (𝓜 : InternalReflexiveModel (A := A))
    (F G x y z : AName.{u} A) :
    (memB F 𝓜.C ⊓ memB G 𝓜.C ⊓ relB 𝓜.Q F G) ⊓
        (memB x 𝓜.D ⊓ memB (opairB x y) F ⊓
          memB (opairB x z) G) ≤
      relB 𝓜.R y z := by
  have hp := 𝓜.relQ_le_pointwise F G
  unfold pointwiseLeB at hp
  have hx := iInf_le
    (fun w : AName A => ⨅ y' : AName A, ⨅ z' : AName A,
      memB w 𝓜.D ⊓ memB (opairB w y') F ⊓
        memB (opairB w z') G ⇨ relB 𝓜.R y' z') x
  have hy := (iInf_le
    (fun y' : AName A => ⨅ z' : AName A,
      memB x 𝓜.D ⊓ memB (opairB x y') F ⊓
        memB (opairB x z') G ⇨ relB 𝓜.R y' z') y).trans' hx
  have hz := (iInf_le
    (fun z' : AName A =>
      memB x 𝓜.D ⊓ memB (opairB x y) F ⊓
        memB (opairB x z') G ⇨ relB 𝓜.R y z') z).trans' hy
  exact (le_himp_iff.mp hz).trans' <| le_inf
    (inf_le_left.trans hp) inf_le_right

/-- Every member of the exact map space is monotone on `D`, in an immediately
applicable degree-local form. -/
theorem InternalReflexiveModel.mem_mapSpace_apply_mono
    (𝓜 : InternalReflexiveModel (A := A))
    (F x x' y y' : AName.{u} A) :
    memB F 𝓜.C ⊓ memB (opairB x y) F ⊓
        memB (opairB x' y') F ⊓ relB 𝓜.R x x' ≤
      relB 𝓜.R y y' := by
  have hc := 𝓜.mem_mapSpace_le_scottContinuous F
  unfold isScottContinuousB at hc
  have hm : memB F 𝓜.C ≤
      ⨅ u : AName A, ⨅ u' : AName A,
        ⨅ v : AName A, ⨅ v' : AName A,
          memB (opairB u v) F ⊓ memB (opairB u' v') F ⊓
              relB 𝓜.R u u' ⇨ relB 𝓜.R v v' :=
    hc.trans (inf_le_left.trans inf_le_right)
  have hx := (iInf_le
    (fun u : AName A => ⨅ u' : AName A,
      ⨅ v : AName A, ⨅ v' : AName A,
        memB (opairB u v) F ⊓ memB (opairB u' v') F ⊓
          relB 𝓜.R u u' ⇨ relB 𝓜.R v v') x).trans' hm
  have hx' := (iInf_le
    (fun u' : AName A => ⨅ v : AName A, ⨅ v' : AName A,
      memB (opairB x v) F ⊓ memB (opairB u' v') F ⊓
        relB 𝓜.R x u' ⇨ relB 𝓜.R v v') x').trans' hx
  have hy := (iInf_le
    (fun v : AName A => ⨅ v' : AName A,
      memB (opairB x v) F ⊓ memB (opairB x' v') F ⊓
        relB 𝓜.R x x' ⇨ relB 𝓜.R v v') y).trans' hx'
  have hy' := (iInf_le
    (fun v' : AName A =>
      memB (opairB x y) F ⊓ memB (opairB x' v') F ⊓
        relB 𝓜.R x x' ⇨ relB 𝓜.R y v') y').trans' hy
  refine (le_himp_iff.mp hy').trans' ?_
  apply le_of_eq
  ac_rfl

/-- Degree-local monotonicity projection from Scott continuity. -/
theorem scottContinuous_apply_mono
    {F D E R Q : AName.{u} A} {a : A}
    (hF : a ≤ isScottContinuousB F D E R Q)
    (x x' y y' : AName.{u} A) :
    a ⊓ memB (opairB x y) F ⊓
        memB (opairB x' y') F ⊓ relB R x x' ≤
      relB Q y y' := by
  unfold isScottContinuousB at hF
  have hm := hF.trans (inf_le_left.trans inf_le_right)
  have hx := (iInf_le
    (fun u : AName A => ⨅ u' : AName A,
      ⨅ v : AName A, ⨅ v' : AName A,
        memB (opairB u v) F ⊓ memB (opairB u' v') F ⊓
          relB R u u' ⇨ relB Q v v') x).trans' hm
  have hx' := (iInf_le
    (fun u' : AName A => ⨅ v : AName A, ⨅ v' : AName A,
      memB (opairB x v) F ⊓ memB (opairB u' v') F ⊓
        relB R x u' ⇨ relB Q v v') x').trans' hx
  have hy := (iInf_le
    (fun v : AName A => ⨅ v' : AName A,
      memB (opairB x v) F ⊓ memB (opairB x' v') F ⊓
        relB R x x' ⇨ relB Q v v') y).trans' hx'
  have hy' := (iInf_le
    (fun v' : AName A =>
      memB (opairB x y) F ⊓ memB (opairB x' v') F ⊓
        relB R x x' ⇨ relB Q y v') y').trans' hy
  refine (le_himp_iff.mp hy').trans' ?_
  apply le_of_eq
  ac_rfl

/-- Degree-local directed-supremum projection from Scott continuity. -/
theorem scottContinuous_mapsToSup
    {F D E R Q : AName.{u} A} {a : A}
    (hF : a ≤ isScottContinuousB F D E R Q)
    (S x y : AName.{u} A) :
    a ⊓ isDirectedRelB S D R ⊓ isSupRelB x S R ⊓
        memB (opairB x y) F ≤
      mapsToSupB F S y Q := by
  unfold isScottContinuousB at hF
  have hs := hF.trans inf_le_right
  have hS := (iInf_le
    (fun T : AName A => ⨅ u : AName A, ⨅ v : AName A,
      isDirectedRelB T D R ⊓ isSupRelB u T R ⊓
        memB (opairB u v) F ⇨ mapsToSupB F T v Q) S).trans' hs
  have hx := (iInf_le
    (fun u : AName A => ⨅ v : AName A,
      isDirectedRelB S D R ⊓ isSupRelB u S R ⊓
        memB (opairB u v) F ⇨ mapsToSupB F S v Q) x).trans' hS
  have hy := (iInf_le
    (fun v : AName A =>
      isDirectedRelB S D R ⊓ isSupRelB x S R ⊓
        memB (opairB x v) F ⇨ mapsToSupB F S v Q) y).trans' hx
  refine (le_himp_iff.mp hy).trans' ?_
  apply le_of_eq
  ac_rfl

/-- The displayed index type of an internal Cartesian product. -/
noncomputable def prodBIdxEquiv (X Y : AName.{u} A) :
    (prodB X Y).idx ≃ X.idx × Y.idx := by
  unfold prodB
  exact Equiv.refl _

noncomputable def prodBIdxOf
    (X Y : AName.{u} A) (i : X.idx) (j : Y.idx) :
    (prodB X Y).idx :=
  (prodBIdxEquiv X Y).symm (i, j)

@[simp] theorem prodBIdxEquiv_idxOf
    (X Y : AName.{u} A) (i : X.idx) (j : Y.idx) :
    prodBIdxEquiv X Y (prodBIdxOf X Y i j) = (i, j) :=
  (prodBIdxEquiv X Y).apply_symm_apply (i, j)

@[simp] theorem prodB_child_eq
    (X Y : AName.{u} A) (p : (prodB X Y).idx) :
    (prodB X Y).child p =
      opairB (X.child ((prodBIdxEquiv X Y p).1))
        (Y.child ((prodBIdxEquiv X Y p).2)) := by
  unfold prodBIdxEquiv prodB
  rfl

@[simp] theorem prodB_child_idxOf
    (X Y : AName.{u} A) (i : X.idx) (j : Y.idx) :
    (prodB X Y).child (prodBIdxOf X Y i j) =
      opairB (X.child i) (Y.child j) := by
  rw [prodB_child_eq, prodBIdxEquiv_idxOf]

@[simp] theorem prodB_val_eq
    (X Y : AName.{u} A) (p : (prodB X Y).idx) :
    (prodB X Y).val p =
      memB (X.child ((prodBIdxEquiv X Y p).1)) X ⊓
        memB (Y.child ((prodBIdxEquiv X Y p).2)) Y := by
  unfold prodBIdxEquiv prodB
  rfl

@[simp] theorem prodB_val_idxOf
    (X Y : AName.{u} A) (i : X.idx) (j : Y.idx) :
    (prodB X Y).val (prodBIdxOf X Y i j) =
      memB (X.child i) X ⊓ memB (Y.child j) Y := by
  rw [prodB_val_eq, prodBIdxEquiv_idxOf]

theorem oid_prodB_eq
    (X Y : AName.{u} A) (p q : (prodB X Y).idx) :
    (oid (prodB X Y)).eq p q =
      ((oid X).prod (oid Y)).eq
        (prodBIdxEquiv X Y p) (prodBIdxEquiv X Y q) := by
  rw [oid_eq, ASetoid.prod_eq, oid_eq, oid_eq,
    prodB_child_eq, prodB_child_eq,
    memB_opairB_prodB, memB_opairB_prodB, eqB_opairB]
  ac_rfl

theorem oid_prodB_eps
    (X Y : AName.{u} A) (p : (prodB X Y).idx) :
    (oid (prodB X Y)).eps p =
      ((oid X).prod (oid Y)).eps (prodBIdxEquiv X Y p) := by
  rw [ASetoid.eps, ASetoid.eps, oid_prodB_eq]

/-- Transport a relational map on the displayed product setoid to the `Oid`
of the internal product name. -/
noncomputable def relFunOnProdB
    (X Y Z : AName.{u} A)
    (f : RelFun ((oid X).prod (oid Y)) (oid Z)) :
    RelFun (oid (prodB X Y)) (oid Z) where
  val p z := f.val (prodBIdxEquiv X Y p) z
  respects := by
    intro p q z w
    rw [oid_prodB_eq]
    exact f.respects _ _ z w
  le_eps := by
    intro p z
    rw [oid_prodB_eps]
    exact f.le_eps _ z
  single_valued := by
    intro p z w
    exact f.single_valued _ z w
  total := by
    intro p
    rw [oid_prodB_eps]
    exact f.total _

@[simp] theorem relFunOnProdB_val
    (X Y Z : AName.{u} A)
    (f : RelFun ((oid X).prod (oid Y)) (oid Z))
    (p : (prodB X Y).idx) (z : Z.idx) :
    (relFunOnProdB X Y Z f).val p z =
      f.val (prodBIdxEquiv X Y p) z :=
  rfl

/-- The componentwise relation on an internal Cartesian product, using the
displayed product coordinates rather than any definitional identification of
`(prodB X Y).idx`. -/
noncomputable def prodOrderRelB
    (X Y RX RY : AName.{u} A) : AName.{u} A :=
  mk ((X.idx × Y.idx) × (X.idx × Y.idx))
    (fun p =>
      opairB
        (opairB (X.child p.1.1) (Y.child p.1.2))
        (opairB (X.child p.2.1) (Y.child p.2.2)))
    (fun p =>
      relB RX (X.child p.1.1) (X.child p.2.1) ⊓
        relB RY (Y.child p.1.2) (Y.child p.2.2))

theorem le_relB_prodOrderRelB
    (X Y RX RY : AName.{u} A)
    (i i' : X.idx) (j j' : Y.idx) :
    relB RX (X.child i) (X.child i') ⊓
        relB RY (Y.child j) (Y.child j') ≤
      relB (prodOrderRelB X Y RX RY)
        (opairB (X.child i) (Y.child j))
        (opairB (X.child i') (Y.child j')) := by
  unfold relB prodOrderRelB
  rw [memB_mk]
  refine le_iSup_of_le ((i, j), (i', j')) ?_
  rw [eqB_self, top_inf_eq]
  exact le_rfl

@[simp] theorem relB_prodOrderRelB
    (X Y RX RY : AName.{u} A)
    (i i' : X.idx) (j j' : Y.idx) :
    relB (prodOrderRelB X Y RX RY)
        (opairB (X.child i) (Y.child j))
        (opairB (X.child i') (Y.child j')) =
      relB RX (X.child i) (X.child i') ⊓
        relB RY (Y.child j) (Y.child j') := by
  apply le_antisymm
  · unfold relB prodOrderRelB
    rw [memB_mk]
    refine iSup_le fun p => ?_
    rw [eqB_opairB, eqB_opairB, eqB_opairB]
    let t :=
      ((eqB (X.child i) (X.child p.1.1) ⊓
          eqB (Y.child j) (Y.child p.1.2)) ⊓
        (eqB (X.child i') (X.child p.2.1) ⊓
          eqB (Y.child j') (Y.child p.2.2))) ⊓
        (relB RX (X.child p.1.1) (X.child p.2.1) ⊓
          relB RY (Y.child p.1.2) (Y.child p.2.2))
    change t ≤ _
    have hxi : t ≤ eqB (X.child p.1.1) (X.child i) := by
      rw [eqB_comm]
      exact inf_le_left.trans (inf_le_left.trans inf_le_left)
    have hxi' : t ≤ eqB (X.child p.2.1) (X.child i') := by
      rw [eqB_comm]
      exact inf_le_left.trans (inf_le_right.trans inf_le_left)
    have hyj : t ≤ eqB (Y.child p.1.2) (Y.child j) := by
      rw [eqB_comm]
      exact inf_le_left.trans (inf_le_left.trans inf_le_right)
    have hyj' : t ≤ eqB (Y.child p.2.2) (Y.child j') := by
      rw [eqB_comm]
      exact inf_le_left.trans (inf_le_right.trans inf_le_right)
    refine le_inf ?_ ?_
    · exact (relB_congr RX
        (X.child p.1.1) (X.child i)
        (X.child p.2.1) (X.child i')).trans' <|
          le_inf (le_inf hxi hxi') (inf_le_right.trans inf_le_left)
    · exact (relB_congr RY
        (Y.child p.1.2) (Y.child j)
        (Y.child p.2.2) (Y.child j')).trans' <|
          le_inf (le_inf hyj hyj') (inf_le_right.trans inf_le_right)
  · exact le_relB_prodOrderRelB X Y RX RY i i' j j'

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

/-- Evaluation reconstructed as an internal function graph on the internal
Cartesian product `C × D`. -/
noncomputable def InternalReflexiveModel.evalGraph
    (𝓜 : InternalReflexiveModel (A := A)) : AName.{u} A :=
  relFunGraphName (prodB 𝓜.C 𝓜.D) 𝓜.D <|
    relFunOnProdB 𝓜.C 𝓜.D 𝓜.D 𝓜.evalRel

theorem InternalReflexiveModel.evalGraph_function
    (𝓜 : InternalReflexiveModel (A := A)) :
    isFunctionB 𝓜.evalGraph (prodB 𝓜.C 𝓜.D) 𝓜.D = ⊤ :=
  isFunctionB_relFunGraphName _ _ _

@[simp] theorem InternalReflexiveModel.memB_evalGraph
    (𝓜 : InternalReflexiveModel (A := A))
    (p : (prodB 𝓜.C 𝓜.D).idx) (y : 𝓜.D.idx) :
    memB
        (opairB ((prodB 𝓜.C 𝓜.D).child p) (𝓜.D.child y))
        𝓜.evalGraph =
      memB (𝓜.C.child (prodBIdxEquiv 𝓜.C 𝓜.D p).1) 𝓜.C ⊓
        memB
          (opairB
            (𝓜.D.child (prodBIdxEquiv 𝓜.C 𝓜.D p).2)
            (𝓜.D.child y))
          (𝓜.C.child (prodBIdxEquiv 𝓜.C 𝓜.D p).1) := by
  rw [InternalReflexiveModel.evalGraph,
    memB_opairB_relFunGraphName, relFunOnProdB_val]
  rfl

@[simp] theorem InternalReflexiveModel.memB_evalGraph_at
    (𝓜 : InternalReflexiveModel (A := A))
    (c : 𝓜.C.idx) (x y : 𝓜.D.idx) :
    memB
        (opairB
          (opairB (𝓜.C.child c) (𝓜.D.child x))
          (𝓜.D.child y))
        𝓜.evalGraph =
      memB (𝓜.C.child c) 𝓜.C ⊓
        memB (opairB (𝓜.D.child x) (𝓜.D.child y))
          (𝓜.C.child c) := by
  simpa using
    𝓜.memB_evalGraph (prodBIdxOf 𝓜.C 𝓜.D c x) y

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
