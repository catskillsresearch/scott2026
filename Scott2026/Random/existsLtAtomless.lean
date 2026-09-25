/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/

import Mathlib.Order.CompleteBooleanAlgebra
import Mathlib.Order.Atoms
import Scott2026.Random.IsAtomic

namespace Scott2026

theorem exists_pos_atomless_of_not_isAtomic {A : Type*} [CompleteBooleanAlgebra A]
    (h : ¬IsAtomic A) :
    ∃ a : A, a ≠ ⊥ ∧ ∀ b, IsAtom b → ¬b ≤ a := by
  let p := sSup {a : A | IsAtom a}
  have hp : p ≠ ⊤ := by
    intro htop
    refine h fun a ha => ?_
    have ha' : a = sSup ((fun b : A => a ⊓ b) '' {b | IsAtom b}) := by
      calc
        a = a ⊓ ⊤ := (inf_top_eq a).symm
        _ = a ⊓ sSup {b | IsAtom b} := by rw [← htop]
        _ = ⨆ b ∈ {b | IsAtom b}, a ⊓ b := inf_sSup_eq
        _ = sSup ((fun b => a ⊓ b) '' {b | IsAtom b}) := sSup_image.symm
    have hex : ∃ b, IsAtom b ∧ a ⊓ b ≠ ⊥ := by
      by_contra hempty
      push Not at hempty
      have hbot : sSup ((fun b : A => a ⊓ b) '' {b | IsAtom b}) = ⊥ :=
        sSup_eq_bot.mpr fun d hd => by
          obtain ⟨b, hb, rfl⟩ := hd
          exact hempty b hb
      exact ha (ha'.trans hbot)
    obtain ⟨b, hb, hne⟩ := hex
    have heq : a ⊓ b = b := by
      rcases lt_or_eq_of_le (inf_le_right (a := a) (b := b)) with hlt | heq
      · exact False.elim (hne (hb.2 (a ⊓ b) hlt))
      · exact heq
    exact ⟨b, hb, (inf_eq_right (a := a) (b := b)).mp heq⟩
  refine ⟨pᶜ, mt compl_eq_bot.mp hp, fun b hb hle => ?_⟩
  have hmem : b ∈ {a : A | IsAtom a} := hb
  have hbot : b ≤ ⊥ :=
    (le_inf (le_sSup hmem) hle).trans_eq inf_compl_eq_bot
  exact hb.1 (le_bot_iff.mp hbot)

theorem exists_lt_atomless {A : Type*} [CompleteBooleanAlgebra A] {a : A}
    (hne : a ≠ ⊥) (hna : ∀ b, IsAtom b → ¬b ≤ a) :
    ∃ c : A, c ≠ ⊥ ∧ c < a ∧ ∀ b, IsAtom b → ¬b ≤ c := by
  have hnot : ¬IsAtom a := fun ha => hna a ha le_rfl
  obtain ⟨c, hclt, hcne⟩ : ∃ c, c < a ∧ c ≠ ⊥ := by
    by_contra h
    push Not at h
    exact hnot ⟨hne, fun c hc => h c hc⟩
  exact ⟨c, hcne, hclt, fun b hb hle => hna b hb (hle.trans hclt.le)⟩

end Scott2026
