/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/

import Scott2026.Oid

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

end Scott2026
