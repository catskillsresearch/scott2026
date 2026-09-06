/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/

import Scott2026.SetCategory

/-!
# Relational infrastructure for internal interpretation

This file develops the dependencies of the Definition 25 recursion.  In
particular, an internal inclusion `X ⊆ Y` induces the relational function
used to interpret constants from `X` as elements of `Y`.
-/

universe u

namespace Scott2026

open AName

variable {A : Type u} [CompleteBooleanAlgebra A]

/-- A partial valuation from `V` to `D`, with domain of definition `Dom`. -/
noncomputable def isValuationB
    (V D Dom Rho : AName.{u} A) : A :=
  subsetB Dom V ⊓ isFunctionB Rho Dom D

/-- Boolean non-membership is extensional in its element argument. -/
theorem eqB_inf_compl_memB_le_compl
    (x y S : AName.{u} A) :
    eqB x y ⊓ (memB x S)ᶜ ≤ (memB y S)ᶜ := by
  rw [le_compl_iff_disjoint_left, disjoint_iff]
  apply le_bot_iff.mp
  have hmem : memB y S ⊓ eqB x y ≤ memB x S := by
    rw [eqB_comm x y]
    exact memB_eqB_left y S x
  calc
    memB y S ⊓ (eqB x y ⊓ (memB x S)ᶜ)
        = (memB x S)ᶜ ⊓ (memB y S ⊓ eqB x y) := by
          ac_rfl
    _ ≤ (memB x S)ᶜ ⊓ memB x S := inf_le_inf le_rfl hmem
    _ = ⊥ := compl_inf_self _

/-- The identity graph on `X` is also an internal function `X → Y` whenever
`X ⊆ Y`. -/
theorem isFunctionB_id_of_subset {X Y : AName.{u} A}
    (hXY : subsetB X Y = ⊤) :
    isFunctionB (idB X) X Y = ⊤ := by
  unfold isFunctionB
  refine inf_eq_top_iff.mpr ⟨inf_eq_top_iff.mpr ⟨?_, ?_⟩, ?_⟩
  · unfold idB
    rw [subsetB_mk]
    refine iInf_eq_top.mpr fun i => himp_eq_top_iff.mpr ?_
    rw [memB_opairB_prodB]
    have hmem : memB (X.child i) X ≤ memB (X.child i) Y := by
      have := memB_of_subsetB (X.child i) X Y
      rwa [hXY, inf_top_eq] at this
    exact le_inf le_rfl hmem
  · exact isFunctionB_single (isFunctionB_id X)
  · exact isFunctionB_total (isFunctionB_id X)

/-- Inclusion of internal sets as a relational function of their `Oid`
setoids. -/
noncomputable def oidSubsetRel
    (X Y : AName.{u} A) (hXY : subsetB X Y = ⊤) :
    RelFun (oid X) (oid Y) :=
  oidRel X Y (idB X) (isFunctionB_id_of_subset hXY)

@[simp] theorem oidSubsetRel_val
    (X Y : AName.{u} A) (hXY : subsetB X Y = ⊤)
    (i : X.idx) (j : Y.idx) :
    (oidSubsetRel X Y hXY).val i j =
      memB (X.child i) X ⊓ eqB (X.child i) (Y.child j) := by
  rw [oidSubsetRel, oidRel_val, memB_opairB_idB]

/-- The inclusion matrix already entails the target extent. -/
theorem oidSubsetRel_val_le_target
    (X Y : AName.{u} A) (hXY : subsetB X Y = ⊤)
    (i : X.idx) (j : Y.idx) :
    (oidSubsetRel X Y hXY).val i j ≤ memB (Y.child j) Y := by
  rw [← oid_eps Y j]
  exact ((oidSubsetRel X Y hXY).le_eps i j).trans inf_le_right

/-- A convenient consequence of an internal inclusion holding at `⊤`. -/
theorem memB_le_of_subsetB_top {X Y : AName.{u} A}
    (hXY : subsetB X Y = ⊤) (x : AName.{u} A) :
    memB x X ≤ memB x Y := by
  have h := memB_of_subsetB x X Y
  rwa [hXY, inf_top_eq] at h

/-- On a total `Oid`, its equality matrix has no extent factors. -/
theorem oid_eq_of_total (X : AName.{u} A) (hX : (oid X).IsTotal)
    (i j : X.idx) :
    (oid X).eq i j = eqB (X.child i) (X.child j) := by
  rw [oid_eq, ← oid_eps X i, ← oid_eps X j, hX i, hX j,
    top_inf_eq, top_inf_eq]

/-- Matrix of a partial valuation extended by a fixed default value outside
its domain.  Boolean complementation is taken after the extensional lookup
`‖x ∈ Dom‖`, so the definition is independent of presentations of `x`. -/
noncomputable def totalizedValuationVal
    (V D Dom Rho : AName.{u} A) (default : D.idx)
    (i : V.idx) (j : D.idx) : A :=
  memB (opairB (V.child i) (D.child j)) Rho ⊔
    (memB (V.child i) V ⊓ (memB (V.child i) Dom)ᶜ ⊓
      (oid D).eq default j)

/-- A partial internal valuation extends to a total relational valuation by
using `default` away from its domain. -/
noncomputable def totalizedValuationRel
    (V D Dom Rho : AName.{u} A)
    (hDom : subsetB Dom V = ⊤)
    (hRho : isFunctionB Rho Dom D = ⊤)
    (hDTotal : (oid D).IsTotal)
    (default : D.idx) :
    RelFun (oid V) (oid D) where
  val := totalizedValuationVal V D Dom Rho default
  respects := by
    have key : ∀ i₁ i₂ j₁ j₂,
        (oid V).eq i₁ i₂ ⊓ (oid D).eq j₁ j₂ ⊓
          totalizedValuationVal V D Dom Rho default i₁ j₁ ≤
          totalizedValuationVal V D Dom Rho default i₂ j₂ := by
      intro i₁ i₂ j₁ j₂
      unfold totalizedValuationVal
      rw [oid_eq_of_total D hDTotal j₁ j₂,
        oid_eq_of_total D hDTotal default j₁,
        oid_eq_of_total D hDTotal default j₂]
      rw [inf_sup_left]
      refine sup_le ?_ ?_
      · exact le_sup_of_le_left <|
          (memB_opairB_congr Rho (V.child i₁) (V.child i₂)
            (D.child j₁) (D.child j₂)).trans' <| by
              refine le_inf (le_inf ?_ ?_) inf_le_right
              · exact (inf_le_left.trans inf_le_left).trans <| by
                  simp only [oid_eq]
                  exact inf_le_right
              · exact inf_le_left.trans inf_le_right
      · apply le_sup_of_le_right
        simp only [oid_eq]
        refine le_inf (le_inf
          (inf_le_left.trans
            (inf_le_left.trans (inf_le_left.trans inf_le_right))) ?_) ?_
        · exact (eqB_inf_compl_memB_le_compl
            (V.child i₁) (V.child i₂) Dom).trans' <| by
              exact le_inf
                ((inf_le_left.trans inf_le_left).trans inf_le_right)
                (inf_le_right.trans (inf_le_left.trans inf_le_right))
        · exact (eqB_trans (D.child default) (D.child j₁)
            (D.child j₂)).trans' <| le_inf
              (inf_le_right.trans inf_le_right)
              (inf_le_left.trans inf_le_right)
    intro i₁ i₂ j₁ j₂
    refine le_inf ?_ ?_ <;> rw [le_himp_iff]
    · exact key i₁ i₂ j₁ j₂
    · have h := key i₂ i₁ j₂ j₁
      rwa [(oid V).symm i₂ i₁, (oid D).symm j₂ j₁] at h
  le_eps := by
    intro i j
    unfold totalizedValuationVal
    refine sup_le ?_ ?_
    · have hpair := memB_opairB_le_of_subsetB
          (isFunctionB_subset hRho) (V.child i) (D.child j)
      rw [oid_eps, oid_eps]
      exact le_inf
        ((hpair.trans inf_le_left).trans
          (memB_le_of_subsetB_top hDom (V.child i)))
        (hpair.trans inf_le_right)
    · rw [oid_eps]
      exact le_inf (inf_le_of_left_le inf_le_left)
        (inf_le_right.trans ((oid D).eq_le_eps_right default j))
  single_valued := by
    intro i j₁ j₂
    let r₁ := memB (opairB (V.child i) (D.child j₁)) Rho
    let r₂ := memB (opairB (V.child i) (D.child j₂)) Rho
    let f₁ := memB (V.child i) V ⊓ (memB (V.child i) Dom)ᶜ ⊓
      (oid D).eq default j₁
    let f₂ := memB (V.child i) V ⊓ (memB (V.child i) Dom)ᶜ ⊓
      (oid D).eq default j₂
    have hrr : r₁ ⊓ r₂ ≤ (oid D).eq j₁ j₂ := by
      rw [oid_eq_of_total D hDTotal j₁ j₂]
      exact (isSingleValuedB_apply Rho (V.child i)
          (D.child j₁) (D.child j₂)).trans' <| by
            rw [isFunctionB_single hRho, top_inf_eq]
    have hrf : r₁ ⊓ f₂ ≤ (oid D).eq j₁ j₂ := by
      have hpair := memB_opairB_le_of_subsetB
          (isFunctionB_subset hRho) (V.child i) (D.child j₁)
      exact (show r₁ ⊓ f₂ ≤ ⊥ by
        calc
          r₁ ⊓ f₂ ≤
              memB (V.child i) Dom ⊓ (memB (V.child i) Dom)ᶜ :=
            le_inf (inf_le_left.trans (hpair.trans inf_le_left))
              (inf_le_right.trans (inf_le_left.trans inf_le_right))
          _ = ⊥ := inf_compl_eq_bot).trans bot_le
    have hfr : f₁ ⊓ r₂ ≤ (oid D).eq j₁ j₂ := by
      have hpair := memB_opairB_le_of_subsetB
          (isFunctionB_subset hRho) (V.child i) (D.child j₂)
      exact (show f₁ ⊓ r₂ ≤ ⊥ by
        calc
          f₁ ⊓ r₂ ≤
              (memB (V.child i) Dom)ᶜ ⊓ memB (V.child i) Dom :=
            le_inf (inf_le_left.trans (inf_le_left.trans inf_le_right))
              (inf_le_right.trans (hpair.trans inf_le_left))
          _ = ⊥ := compl_inf_self _).trans bot_le
    have hff : f₁ ⊓ f₂ ≤ (oid D).eq j₁ j₂ := by
      refine ((oid D).trans j₁ default j₂).trans' (le_inf ?_ ?_)
      · rw [(oid D).symm j₁ default]
        exact inf_le_left.trans inf_le_right
      · exact inf_le_right.trans inf_le_right
    change (r₁ ⊔ f₁) ⊓ (r₂ ⊔ f₂) ≤ (oid D).eq j₁ j₂
    calc
      (r₁ ⊔ f₁) ⊓ (r₂ ⊔ f₂) =
          (r₁ ⊓ (r₂ ⊔ f₂)) ⊔ (f₁ ⊓ (r₂ ⊔ f₂)) :=
            inf_sup_right r₁ f₁ (r₂ ⊔ f₂)
      _ =
          (r₁ ⊓ r₂ ⊔ r₁ ⊓ f₂) ⊔ (f₁ ⊓ r₂ ⊔ f₁ ⊓ f₂) := by
            exact congrArg₂ (· ⊔ ·)
              (inf_sup_left r₁ r₂ f₂) (inf_sup_left f₁ r₂ f₂)
      _ ≤ (oid D).eq j₁ j₂ :=
        sup_le (sup_le hrr hrf) (sup_le hfr hff)
  total := by
    intro i
    rw [oid_eps]
    let p := memB (V.child i) Dom
    have hsplit : memB (V.child i) V =
        (memB (V.child i) V ⊓ p) ⊔
          (memB (V.child i) V ⊓ pᶜ) := by
      rw [← inf_sup_left, sup_compl_eq_top, inf_top_eq]
    rw [hsplit]
    refine sup_le ?_ ?_
    · have htot := isTotalB_apply Rho Dom (V.child i)
      rw [isFunctionB_total hRho, top_inf_eq] at htot
      refine (inf_le_right.trans htot).trans <|
        iSup_le fun y => ?_
      refine (memB_opairB_le_iSup_child
        (isFunctionB_subset hRho) (V.child i) y).trans <|
          iSup_le fun j => le_iSup_of_le j ?_
      unfold totalizedValuationVal
      exact le_sup_of_le_left le_rfl
    · have hdef : (oid D).eps default = ⊤ := hDTotal default
      have htot : ⊤ ≤ ⨆ j, (oid D).eq default j := by
        rw [← hdef]
        exact (RelFun.id (oid D)).total default
      have hcoeff : memB (V.child i) V ⊓ pᶜ ≤
          (memB (V.child i) V ⊓ pᶜ) ⊓
            ⨆ j, (oid D).eq default j :=
        le_inf le_rfl (le_top.trans htot)
      refine hcoeff.trans ?_
      rw [inf_iSup_eq]
      refine iSup_le fun j => le_iSup_of_le j ?_
      unfold totalizedValuationVal
      exact le_sup_of_le_right (by
        change memB (V.child i) V ⊓ pᶜ ⊓ (oid D).eq default j ≤ _
        exact le_rfl)

@[simp] theorem totalizedValuationRel_val
    (V D Dom Rho : AName.{u} A)
    (hDom : subsetB Dom V = ⊤)
    (hRho : isFunctionB Rho Dom D = ⊤)
    (hDTotal : (oid D).IsTotal) (default : D.idx)
    (i : V.idx) (j : D.idx) :
    (totalizedValuationRel V D Dom Rho hDom hRho hDTotal default).val i j =
      totalizedValuationVal V D Dom Rho default i j :=
  rfl

/-- Totalization agrees with the original valuation wherever the latter is
defined. -/
theorem totalizedValuationVal_agrees
    (V D Dom Rho : AName.{u} A) (default : D.idx)
    (i : V.idx) (j : D.idx) :
    memB (V.child i) Dom ⊓
        totalizedValuationVal V D Dom Rho default i j =
      memB (V.child i) Dom ⊓
        memB (opairB (V.child i) (D.child j)) Rho := by
  unfold totalizedValuationVal
  rw [inf_sup_left]
  apply sup_eq_left.mpr
  calc
    memB (V.child i) Dom ⊓
        (memB (V.child i) V ⊓ (memB (V.child i) Dom)ᶜ ⊓
          (oid D).eq default j)
      ≤ memB (V.child i) Dom ⊓ (memB (V.child i) Dom)ᶜ := by
        exact le_inf inf_le_left
          (inf_le_right.trans (inf_le_left.trans inf_le_right))
    _ = ⊥ := inf_compl_eq_bot
    _ ≤ memB (V.child i) Dom ⊓
        memB (opairB (V.child i) (D.child j)) Rho := bot_le

/-- A canonical external representative used only to totalize a partial
valuation. Completeness guarantees that the domain carrier is inhabited. -/
noncomputable def valuationDefault
    (D : AName.{u} A) (hD : (oid D).IsComplete.{u}) : D.idx :=
  Classical.choice (hD.nonempty)

/-- Totalize a valuation directly from its paper-facing validity
hypothesis. -/
noncomputable def totalizedValuationRelOfValid
    (V D Dom Rho : AName.{u} A)
    (hVal : isValuationB V D Dom Rho = ⊤)
    (hDTotal : (oid D).IsTotal)
    (hD : (oid D).IsComplete.{u}) :
    RelFun (oid V) (oid D) := by
  have h := inf_eq_top_iff.mp hVal
  exact totalizedValuationRel V D Dom Rho h.1 h.2 hDTotal
    (valuationDefault D hD)

section RelationalUpdate

variable {X Y : Type*}
variable {S : ASetoid (A := A) X} {T : ASetoid (A := A) Y}

/-- Equality-complement substitution in an `A`-setoid. -/
theorem setoidEq_inf_compl_le_compl (x₁ x₂ z : X) :
    S.eq x₁ x₂ ⊓ (S.eq x₁ z)ᶜ ≤ (S.eq x₂ z)ᶜ := by
  rw [le_compl_iff_disjoint_left, disjoint_iff]
  apply le_bot_iff.mp
  have hback : S.eq x₂ z ⊓ S.eq x₁ x₂ ≤ S.eq x₁ z := by
    rw [inf_comm]
    exact S.trans x₁ x₂ z
  calc
    S.eq x₂ z ⊓ (S.eq x₁ x₂ ⊓ (S.eq x₁ z)ᶜ)
        = (S.eq x₁ z)ᶜ ⊓ (S.eq x₂ z ⊓ S.eq x₁ x₂) := by
          ac_rfl
    _ ≤ (S.eq x₁ z)ᶜ ⊓ S.eq x₁ z := inf_le_inf le_rfl hback
    _ = ⊥ := compl_inf_self _

/-- Boolean matrix for overwriting a relational function at `x` by `d`. -/
def RelFun.updateVal (f : RelFun S T) (x : X) (d : Y)
    (i : X) (j : Y) : A :=
  (S.eq i x ⊓ T.eq d j) ⊔ ((S.eq i x)ᶜ ⊓ f.val i j)

/-- Relational environment update. The source and target are total in the
paper's application, so equality and its complement partition every input
with full extent. -/
noncomputable def RelFun.update (f : RelFun S T)
    (hS : S.IsTotal) (hT : T.IsTotal) (x : X) (d : Y) :
    RelFun S T where
  val := f.updateVal x d
  respects := by
    have key : ∀ i₁ i₂ j₁ j₂,
        S.eq i₁ i₂ ⊓ T.eq j₁ j₂ ⊓ f.updateVal x d i₁ j₁ ≤
          f.updateVal x d i₂ j₂ := by
      intro i₁ i₂ j₁ j₂
      unfold RelFun.updateVal
      rw [inf_sup_left]
      refine sup_le ?_ ?_
      · apply le_sup_of_le_left
        refine le_inf ?_ ?_
        · exact (S.trans i₂ i₁ x).trans' <| le_inf
            ((inf_le_left.trans inf_le_left).trans_eq (S.symm i₁ i₂))
            (inf_le_right.trans inf_le_left)
        · exact (T.trans d j₁ j₂).trans' <| le_inf
            (inf_le_right.trans inf_le_right)
            (inf_le_left.trans inf_le_right)
      · apply le_sup_of_le_right
        refine le_inf ?_ ?_
        · exact (setoidEq_inf_compl_le_compl i₁ i₂ x).trans' <|
            le_inf (inf_le_left.trans inf_le_left)
              (inf_le_right.trans inf_le_left)
        · exact (f.subst_right i₂ j₁ j₂).trans' <| le_inf
            (inf_le_left.trans inf_le_right)
            ((f.subst_left i₁ i₂ j₁).trans' <| le_inf
              (inf_le_left.trans inf_le_left)
              (inf_le_right.trans inf_le_right))
    intro i₁ i₂ j₁ j₂
    refine le_inf ?_ ?_ <;> rw [le_himp_iff]
    · exact key i₁ i₂ j₁ j₂
    · have h := key i₂ i₁ j₂ j₁
      rwa [S.symm i₂ i₁, T.symm j₂ j₁] at h
  le_eps := by
    intro i j
    rw [hS i, hT j, top_inf_eq]
    exact le_top
  single_valued := by
    intro i j₁ j₂
    let u₁ := S.eq i x ⊓ T.eq d j₁
    let u₂ := S.eq i x ⊓ T.eq d j₂
    let o₁ := (S.eq i x)ᶜ ⊓ f.val i j₁
    let o₂ := (S.eq i x)ᶜ ⊓ f.val i j₂
    have huu : u₁ ⊓ u₂ ≤ T.eq j₁ j₂ := by
      refine (T.trans j₁ d j₂).trans' (le_inf ?_ ?_)
      · rw [T.symm j₁ d]
        exact inf_le_left.trans inf_le_right
      · exact inf_le_right.trans inf_le_right
    have huo : u₁ ⊓ o₂ ≤ T.eq j₁ j₂ := by
      exact (show u₁ ⊓ o₂ ≤ ⊥ by
        calc
          u₁ ⊓ o₂ ≤ S.eq i x ⊓ (S.eq i x)ᶜ :=
            le_inf (inf_le_left.trans inf_le_left)
              (inf_le_right.trans inf_le_left)
          _ = ⊥ := inf_compl_eq_bot).trans bot_le
    have hou : o₁ ⊓ u₂ ≤ T.eq j₁ j₂ := by
      exact (show o₁ ⊓ u₂ ≤ ⊥ by
        calc
          o₁ ⊓ u₂ ≤ (S.eq i x)ᶜ ⊓ S.eq i x :=
            le_inf (inf_le_left.trans inf_le_left)
              (inf_le_right.trans inf_le_left)
          _ = ⊥ := compl_inf_self _).trans bot_le
    have hoo : o₁ ⊓ o₂ ≤ T.eq j₁ j₂ :=
      (f.single_valued i j₁ j₂).trans' <| le_inf
        (inf_le_left.trans inf_le_right)
        (inf_le_right.trans inf_le_right)
    change (u₁ ⊔ o₁) ⊓ (u₂ ⊔ o₂) ≤ T.eq j₁ j₂
    calc
      (u₁ ⊔ o₁) ⊓ (u₂ ⊔ o₂) =
          (u₁ ⊓ (u₂ ⊔ o₂)) ⊔ (o₁ ⊓ (u₂ ⊔ o₂)) :=
            inf_sup_right u₁ o₁ (u₂ ⊔ o₂)
      _ = (u₁ ⊓ u₂ ⊔ u₁ ⊓ o₂) ⊔
          (o₁ ⊓ u₂ ⊔ o₁ ⊓ o₂) :=
        congrArg₂ (· ⊔ ·) (inf_sup_left u₁ u₂ o₂)
          (inf_sup_left o₁ u₂ o₂)
      _ ≤ T.eq j₁ j₂ :=
        sup_le (sup_le huu huo) (sup_le hou hoo)
  total := by
    intro i
    rw [hS i]
    have hsplit : (⊤ : A) = S.eq i x ⊔ (S.eq i x)ᶜ :=
      (sup_compl_eq_top).symm
    rw [hsplit]
    refine sup_le ?_ ?_
    · have hd : T.eps d = ⊤ := hT d
      have htot : ⊤ ≤ ⨆ j, T.eq d j := by
        rw [← hd]
        exact (RelFun.id T).total d
      refine (le_inf le_rfl (le_top.trans htot)).trans ?_
      rw [inf_iSup_eq]
      exact iSup_le fun j => le_iSup_of_le j <|
        le_sup_of_le_left le_rfl
    · have htot : ⊤ ≤ ⨆ j, f.val i j := by
        rw [← hS i]
        exact f.total i
      refine (le_inf le_rfl (le_top.trans htot)).trans ?_
      rw [inf_iSup_eq]
      exact iSup_le fun j => le_iSup_of_le j <|
        le_sup_of_le_right le_rfl

@[simp] theorem RelFun.update_val (f : RelFun S T)
    (hS : S.IsTotal) (hT : T.IsTotal) (x : X) (d : Y)
    (i : X) (j : Y) :
    (f.update hS hT x d).val i j =
      (S.eq i x ⊓ T.eq d j) ⊔ ((S.eq i x)ᶜ ⊓ f.val i j) :=
  rfl

/-- Lookup at the overwritten key. -/
theorem RelFun.update_self (f : RelFun S T)
    (hS : S.IsTotal) (hT : T.IsTotal) (x : X) (d j : Y) :
    (f.update hS hT x d).val x j = T.eq d j := by
  have hxx := hS x
  change S.eq x x = ⊤ at hxx
  rw [RelFun.update_val, hxx, top_inf_eq, compl_top, bot_inf_eq,
    sup_bot_eq]

/-- Simultaneous extensional variation of an environment and its replacement
value.  The Boolean degree `a` may encode equality of parameters in an
arbitrary indexing setoid. -/
theorem RelFun.updateVal_le_updateVal
    (f g : RelFun S T) (x : X) (d₁ d₂ : Y) (a : A)
    (hfg : ∀ i j, a ⊓ f.val i j ≤ g.val i j)
    (hd : a ≤ T.eq d₁ d₂) (i : X) (j : Y) :
    a ⊓ f.updateVal x d₁ i j ≤ g.updateVal x d₂ i j := by
  unfold RelFun.updateVal
  rw [inf_sup_left]
  refine sup_le ?_ ?_
  · apply le_sup_of_le_left
    refine le_inf (inf_le_right.trans inf_le_left) ?_
    refine (T.trans d₂ d₁ j).trans' (le_inf ?_ ?_)
    · exact (inf_le_left.trans hd).trans_eq (T.symm d₁ d₂)
    · exact inf_le_right.trans inf_le_right
  · apply le_sup_of_le_right
    refine le_inf (inf_le_right.trans inf_le_left) ?_
    exact (hfg i j).trans' <| le_inf inf_le_left
      (inf_le_right.trans inf_le_right)

/-- Exact congruence of update under pointwise equality of environments and
setoid equality `⊤` of replacement values. -/
theorem RelFun.update_congr
    (f g : RelFun S T) (hS : S.IsTotal) (hT : T.IsTotal)
    (x : X) (d₁ d₂ : Y)
    (hfg : ∀ i j, f.val i j = g.val i j)
    (hd : T.eq d₁ d₂ = ⊤) :
    f.update hS hT x d₁ = g.update hS hT x d₂ := by
  apply RelFun.ext
  intro i j
  apply le_antisymm
  · change f.updateVal x d₁ i j ≤ g.updateVal x d₂ i j
    simpa only [top_inf_eq] using
      f.updateVal_le_updateVal g x d₁ d₂ ⊤
        (fun i j => by rw [top_inf_eq, hfg i j])
        (by rw [hd]) i j
  · change g.updateVal x d₂ i j ≤ f.updateVal x d₁ i j
    simpa only [top_inf_eq] using
      g.updateVal_le_updateVal f x d₂ d₁ ⊤
        (fun i j => by rw [top_inf_eq, hfg i j])
        (by rw [T.symm d₂ d₁, hd]) i j

/-- A family of relational functions varying extensionally pointwise over
an `A`-setoid of parameters.  This is the hypothesis needed to run a
valuation-parametric induction: equality of parameters transports every
matrix coefficient of the environment. -/
def RelFun.IsPointwiseFamily {U : Type*}
    (R : ASetoid (A := A) U) (F : U → RelFun S T) : Prop :=
  ∀ u v i j, R.eq u v ⊓ (F u).val i j ≤ (F v).val i j

/-- A constant environment is a pointwise relational family. -/
theorem RelFun.isPointwiseFamily_const {U : Type*}
    (R : ASetoid (A := A) U) (f : RelFun S T) :
    RelFun.IsPointwiseFamily R (fun _ => f) := by
  intro u v i j
  exact inf_le_right

/-- Updating a pointwise family by an equality-preserving replacement family
again gives a pointwise family.  Both the ambient environment and the
replacement are allowed to vary with the parameter. -/
theorem RelFun.IsPointwiseFamily.update {U : Type*}
    {R : ASetoid (A := A) U} {F : U → RelFun S T}
    (hF : RelFun.IsPointwiseFamily R F)
    (hS : S.IsTotal) (hT : T.IsTotal) (x : X)
    (d : U → Y) (hd : APoset.Functional R T d) :
    RelFun.IsPointwiseFamily R
      (fun u => (F u).update hS hT x (d u)) := by
  intro u v i j
  rw [RelFun.update_val, RelFun.update_val]
  exact (RelFun.updateVal_le_updateVal
    (F u) (F v) x (d u) (d v) (R.eq u v)
    (hF u v) (hd u v) i j)

/-- The abstraction family `d ↦ η[x := d]` is pointwise relational over the
codomain setoid itself. -/
theorem RelFun.isPointwiseFamily_update
    (f : RelFun S T) (hS : S.IsTotal) (hT : T.IsTotal) (x : X) :
    RelFun.IsPointwiseFamily T
      (fun d => f.update hS hT x d) :=
  (RelFun.isPointwiseFamily_const T f).update hS hT x _root_.id
    APoset.Functional.id

end RelationalUpdate

/-- An updated relational environment represented as an internal function
name. -/
noncomputable def updateEnvName
    (V D : AName.{u} A) (f : RelFun (oid V) (oid D))
    (hV : (oid V).IsTotal) (hD : (oid D).IsTotal)
    (x : V.idx) (d : D.idx) : AName.{u} A :=
  relFunGraphName V D (f.update hV hD x d)

/-- The graph reconstructed from an updated relational environment is an
internal function. -/
theorem isFunctionB_updateEnvName
    (V D : AName.{u} A) (f : RelFun (oid V) (oid D))
    (hV : (oid V).IsTotal) (hD : (oid D).IsTotal)
    (x : V.idx) (d : D.idx) :
    isFunctionB (updateEnvName V D f hV hD x d) V D = ⊤ :=
  isFunctionB_relFunGraphName V D (f.update hV hD x d)

/-!
## Single extents
-/

/-- One generalized element with prescribed Boolean extent. -/
def extentSetoid (a : A) : ASetoid (A := A) PUnit.{u + 1} where
  eq _ _ := a
  symm _ _ := rfl
  trans _ _ _ := inf_le_left

@[simp] theorem extentSetoid_eq (a : A) (i j : PUnit.{u + 1}) :
    (extentSetoid a).eq i j = a :=
  rfl

@[simp] theorem extentSetoid_eps (a : A) (i : PUnit.{u + 1}) :
    (extentSetoid a).eps i = a :=
  rfl

/-- Restrict a relational function to one source element. -/
def RelFun.at {X Y : Type*}
    {S : ASetoid (A := A) X} {T : ASetoid (A := A) Y}
    (f : RelFun S T) (x : X) :
    RelFun (extentSetoid (S.eps x)) T where
  val _ y := f.val x y
  respects := by
    intro _ _ y₁ y₂
    refine le_inf ?_ ?_ <;> rw [le_himp_iff]
    · exact (f.subst_right x y₁ y₂).trans' <|
        le_inf (inf_le_left.trans inf_le_right) inf_le_right
    · have h := f.subst_right x y₂ y₁
      rw [T.symm y₂ y₁, inf_comm] at h
      exact h.trans' <| le_inf inf_le_right
        (inf_le_left.trans inf_le_right)
  le_eps := fun _ y => f.le_eps x y
  single_valued := fun _ => f.single_valued x
  total := fun _ => f.total x

@[simp] theorem RelFun.at_val {X Y : Type*}
    {S : ASetoid (A := A) X} {T : ASetoid (A := A) Y}
    (f : RelFun S T) (x : X) (i : PUnit.{u + 1}) (y : Y) :
    (f.at x).val i y = f.val x y :=
  rfl

section Product

variable {X₁ X₂ Y₁ Y₂ : Type*}
variable {S₁ : ASetoid (A := A) X₁} {S₂ : ASetoid (A := A) X₂}
variable {T₁ : ASetoid (A := A) Y₁} {T₂ : ASetoid (A := A) Y₂}

/-- Product of relational functions. -/
def RelFun.prod (f : RelFun S₁ T₁) (g : RelFun S₂ T₂) :
    RelFun (S₁.prod S₂) (T₁.prod T₂) where
  val x y := f.val x.1 y.1 ⊓ g.val x.2 y.2
  respects := by
    have key : ∀ x₁ x₂ y₁ y₂,
        (S₁.prod S₂).eq x₁ x₂ ⊓ (T₁.prod T₂).eq y₁ y₂ ⊓
            (f.val x₁.1 y₁.1 ⊓ g.val x₁.2 y₁.2) ≤
          f.val x₂.1 y₂.1 ⊓ g.val x₂.2 y₂.2 := by
      intro x₁ x₂ y₁ y₂
      refine le_inf ?_ ?_
      · exact (f.subst_right x₂.1 y₁.1 y₂.1).trans' <| le_inf
          (inf_le_left.trans (inf_le_right.trans inf_le_left))
          ((f.subst_left x₁.1 x₂.1 y₁.1).trans' <| le_inf
            (inf_le_left.trans (inf_le_left.trans inf_le_left))
            (inf_le_right.trans inf_le_left))
      · exact (g.subst_right x₂.2 y₁.2 y₂.2).trans' <| le_inf
          (inf_le_left.trans (inf_le_right.trans inf_le_right))
          ((g.subst_left x₁.2 x₂.2 y₁.2).trans' <| le_inf
            (inf_le_left.trans (inf_le_left.trans inf_le_right))
            (inf_le_right.trans inf_le_right))
    intro x₁ x₂ y₁ y₂
    refine le_inf ?_ ?_ <;> rw [le_himp_iff]
    · exact key x₁ x₂ y₁ y₂
    · have h := key x₂ x₁ y₂ y₁
      rwa [(S₁.prod S₂).symm x₂ x₁, (T₁.prod T₂).symm y₂ y₁] at h
  le_eps := by
    intro x y
    change f.val x.1 y.1 ⊓ g.val x.2 y.2 ≤
      (S₁.eps x.1 ⊓ S₂.eps x.2) ⊓ (T₁.eps y.1 ⊓ T₂.eps y.2)
    refine le_inf (le_inf ?_ ?_) (le_inf ?_ ?_)
    · exact inf_le_left.trans ((f.le_eps x.1 y.1).trans inf_le_left)
    · exact inf_le_right.trans ((g.le_eps x.2 y.2).trans inf_le_left)
    · exact inf_le_left.trans ((f.le_eps x.1 y.1).trans inf_le_right)
    · exact inf_le_right.trans ((g.le_eps x.2 y.2).trans inf_le_right)
  single_valued := by
    intro x y₁ y₂
    rw [ASetoid.prod_eq]
    exact inf_pair_le (f.single_valued x.1 y₁.1 y₂.1)
      (g.single_valued x.2 y₁.2 y₂.2)
  total := by
    intro x
    change S₁.eps x.1 ⊓ S₂.eps x.2 ≤
      ⨆ y : Y₁ × Y₂, f.val x.1 y.1 ⊓ g.val x.2 y.2
    refine (inf_le_inf (f.total x.1) (g.total x.2)).trans ?_
    rw [iSup_inf_eq]
    refine iSup_le fun y₁ => ?_
    rw [inf_iSup_eq]
    refine iSup_le fun y₂ => le_iSup_of_le (y₁, y₂) le_rfl

@[simp] theorem RelFun.prod_val (f : RelFun S₁ T₁) (g : RelFun S₂ T₂)
    (x : X₁ × X₂) (y : Y₁ × Y₂) :
    (f.prod g).val x y = f.val x.1 y.1 ⊓ g.val x.2 y.2 :=
  rfl

end Product

end Scott2026
