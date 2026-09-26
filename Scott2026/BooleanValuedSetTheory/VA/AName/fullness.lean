/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/

import Mathlib.Order.CompleteBooleanAlgebra
import Mathlib.Order.Zorn
import Scott2026.BooleanValuedSetTheory.VA.AName.memEq
import Scott2026.BooleanValuedSetTheory.VA.AName.eqBLaws
import Scott2026.BooleanValuedSetTheory.VA.AName.mix

namespace Scott2026

namespace AName

variable {A : Type u}
variable [CompleteBooleanAlgebra A]

theorem fullness (φ : AName.{u} A → A)
    (hcongr : ∀ x y, eqB x y ⊓ φ x ≤ φ y) :
    ∃ a, φ a = ⨆ x, φ x := by
  classical
  let D : Set A := {u | ∃ a, u ≤ φ a}
  let S : Set (Set A) :=
    {W | W ⊆ D ∧ Set.Pairwise W fun a b => a ⊓ b = ⊥}
  have hunion (c : Set (Set A)) (hcS : c ⊆ S) (hchain : IsChain (· ⊆ ·) c) :
      ⋃₀ c ∈ S ∧ ∀ s ∈ c, s ⊆ ⋃₀ c := by
    refine ⟨⟨?_, ?_⟩, fun _ => Set.subset_sUnion_of_mem⟩
    · intro u hu
      obtain ⟨W, hWc, huW⟩ := hu
      exact (hcS hWc).1 huW
    · intro a ha b hb hab
      obtain ⟨W₁, hW₁c, haW⟩ := ha
      obtain ⟨W₂, hW₂c, hbW⟩ := hb
      rcases eq_or_ne W₁ W₂ with hW | hW
      · subst hW
        exact (hcS hW₁c).2 haW hbW hab
      · rcases hchain hW₁c hW₂c hW with h | h
        · exact (hcS hW₂c).2 (h haW) hbW hab
        · exact (hcS hW₁c).2 haW (h hbW) hab
  obtain ⟨W, hWmax⟩ := zorn_subset S fun c hcS hchain =>
    ⟨⋃₀ c, (hunion c hcS hchain).1, (hunion c hcS hchain).2⟩
  have hWS : W ∈ S := hWmax.1
  have hWD : W ⊆ D := hWS.1
  have hWpair : Set.Pairwise W fun a b => a ⊓ b = ⊥ := hWS.2
  let au : W → AName.{u} A := fun u => Classical.choose (hWD u.property)
  have hau : ∀ u : W, (u : A) ≤ φ (au u) :=
    fun u => Classical.choose_spec (hWD u.property)
  have hdis : Pairwise fun (i j : W) => (i : A) ⊓ (j : A) = ⊥ := by
    intro i j hij
    exact hWpair i.property j.property (Subtype.coe_ne_coe.mpr hij)
  let a : AName.{u} A := mix (fun u : W => (u : A)) au
  have hmix (u : W) : (u : A) ≤ eqB a (au u) :=
    mix_le_eqB (fun u : W => (u : A)) au hdis u
  have hWle : ∀ u : W, (u : A) ≤ φ a := fun u => by
    have : (u : A) ≤ eqB (au u) a ⊓ φ (au u) :=
      le_inf (by rw [eqB_comm]; exact hmix u) (hau u)
    exact this.trans (hcongr (au u) a)
  let u0 : A := ⨆ x, φ x
  let g : A := ⨆ u : W, (u : A)
  have hu0_le : u0 ≤ g := by
    by_contra hne
    have hiff : u0 ≤ g ↔ u0 ⊓ gᶜ = ⊥ := by
      rw [← disjoint_compl_right_iff, disjoint_iff]
    have hvne : u0 ⊓ gᶜ ≠ ⊥ := mt hiff.mpr hne
    let v : A := u0 ⊓ gᶜ
    have : ⨆ x, v ⊓ φ x ≠ ⊥ := by
      rw [← inf_iSup_eq, show v ⊓ u0 = v from inf_eq_left.mpr inf_le_left]
      exact hvne
    obtain ⟨x, hx⟩ : ∃ x, v ⊓ φ x ≠ ⊥ := by
      contrapose! this
      exact iSup_eq_bot.mpr this
    let d : A := v ⊓ φ x
    have hdD : d ∈ D := ⟨x, inf_le_right⟩
    have hdisj (w : A) (hw : w ∈ W) : d ⊓ w = ⊥ := by
      have hdg : d ⊓ g ≤ ⊥ := by
        have : d ≤ gᶜ := inf_le_of_left_le inf_le_right
        exact (inf_le_inf_right g this).trans (inf_comm (a := gᶜ) (b := g) ▸ inf_compl_eq_bot.le)
      exact bot_unique <| (inf_le_inf_left d (le_iSup (fun u : W => (u : A)) ⟨w, hw⟩)).trans hdg
    have hinsert : insert d W ∈ S :=
      ⟨Set.insert_subset_iff.mpr ⟨hdD, hWD⟩,
        hWpair.insert fun w hw _ => ⟨hdisj w hw, by rw [inf_comm]; exact hdisj w hw⟩⟩
    have hdW : d ∈ W := Maximal.mem_of_prop_insert hWmax hinsert
    have : d ≤ ⊥ :=
      (le_inf (le_iSup (fun u : W => (u : A)) ⟨d, hdW⟩)
        (inf_le_of_left_le inf_le_right)).trans inf_compl_eq_bot.le
    exact hx (le_bot_iff.mp this)
  refine ⟨a, le_antisymm (le_iSup φ a) (hu0_le.trans (iSup_le fun u => hWle u))⟩

end AName

end Scott2026
