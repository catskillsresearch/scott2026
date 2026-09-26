/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/

import Mathlib.MeasureTheory.MeasurableSpace.Basic
import Scott2026.RandomVariables.NegligibilitySpace
import Scott2026.RandomVariables.Random.AssociatedAlgebra
import Scott2026.RandomVariables.Random.AssociatedAlgebra.Le
import Scott2026.RandomVariables.Random.AssociatedAlgebra.mk
import Scott2026.RandomVariables.Random.AssociatedAlgebra.inf
import Scott2026.RandomVariables.Random.AssociatedAlgebra.sup
import Scott2026.RandomVariables.Random.AssociatedAlgebra.compl
import Scott2026.RandomVariables.Random.AssociatedAlgebra.bot
import Scott2026.RandomVariables.Random.AssociatedAlgebra.top
import Scott2026.RandomVariables.Random.AssociatedAlgebra.sSup
import Scott2026.RandomVariables.Random.AssociatedAlgebra.sInf
import Scott2026.RandomVariables.Random.aeEq
import Scott2026.RandomVariables.Random.symmDiff

namespace Scott2026

open MeasureTheory Set

variable {X : Type*} [MeasurableSpace X] (N : NegligibilitySpace X)

namespace AssociatedAlgebra

theorem le_refl (a : AssociatedAlgebra N) : Le N a a := by
  simpa [Le] using N.empty

theorem le_trans (a b c : AssociatedAlgebra N)
    (hab : Le N a b) (hbc : Le N b c) : Le N a c := by
  have hsub : Quotient.out a \ Quotient.out c ⊆
      (Quotient.out a \ Quotient.out b) ∪ (Quotient.out b \ Quotient.out c) := by
    intro x hx
    simp only [mem_union, mem_sdiff] at hx ⊢
    tauto
  exact N.mono hsub (N.union₂ hab hbc)

theorem le_antisymm (a b : AssociatedAlgebra N)
    (hab : Le N a b) (hba : Le N b a) : a = b := by
  have : aeEq N (Quotient.out a) (Quotient.out b) := by
    simpa [aeEq, symmDiff_def] using N.union₂ hab hba
  calc a = mk N (Quotient.out a) := (mk_out N a).symm
    _ = mk N (Quotient.out b) := (mk_eq_iff N).mpr this
    _ = b := mk_out N b

theorem inf_le_left (a b : AssociatedAlgebra N) : Le N (inf N a b) a := by
  rw [show a = mk N (Quotient.out a) from (mk_out N a).symm]
  unfold inf
  refine (le_mk N).mpr ?_
  have : (Quotient.out a ∩ Quotient.out b) \ Quotient.out a = ∅ := by
    ext x; simp only [mem_empty_iff_false, mem_sdiff, mem_inter_iff]; tauto
  simpa [this] using N.empty

theorem inf_le_right (a b : AssociatedAlgebra N) : Le N (inf N a b) b := by
  rw [show b = mk N (Quotient.out b) from (mk_out N b).symm]
  unfold inf
  refine (le_mk N).mpr ?_
  have : (Quotient.out a ∩ Quotient.out b) \ Quotient.out b = ∅ := by
    ext x; simp only [mem_empty_iff_false, mem_sdiff, mem_inter_iff]; tauto
  simpa [this] using N.empty

theorem le_inf (a b c : AssociatedAlgebra N)
    (hab : Le N a b) (hac : Le N a c) : Le N a (inf N b c) := by
  rw [show a = mk N (Quotient.out a) from (mk_out N a).symm]
  unfold inf
  refine (le_mk N).mpr ?_
  have hsub : Quotient.out a \ (Quotient.out b ∩ Quotient.out c) =
      (Quotient.out a \ Quotient.out b) ∪ (Quotient.out a \ Quotient.out c) := by
    ext x; simp; tauto
  exact hsub ▸ N.union₂ hab hac

theorem le_sup_left (a b : AssociatedAlgebra N) : Le N a (sup N a b) := by
  rw [show a = mk N (Quotient.out a) from (mk_out N a).symm]
  unfold sup
  refine (le_mk N).mpr ?_
  have : Quotient.out a \ (Quotient.out a ∪ Quotient.out b) = ∅ := by
    ext x; simp only [mem_empty_iff_false, mem_sdiff, mem_union]; tauto
  simpa [this] using N.empty

theorem le_sup_right (a b : AssociatedAlgebra N) : Le N b (sup N a b) := by
  rw [show b = mk N (Quotient.out b) from (mk_out N b).symm]
  unfold sup
  refine (le_mk N).mpr ?_
  have : Quotient.out b \ (Quotient.out a ∪ Quotient.out b) = ∅ := by
    ext x; simp only [mem_empty_iff_false, mem_sdiff, mem_union]; tauto
  simpa [this] using N.empty

theorem sup_le (a b c : AssociatedAlgebra N)
    (hac : Le N a c) (hbc : Le N b c) : Le N (sup N a b) c := by
  rw [show c = mk N (Quotient.out c) from (mk_out N c).symm]
  unfold sup
  refine (le_mk N).mpr ?_
  have hsub : (Quotient.out a ∪ Quotient.out b) \ Quotient.out c =
      (Quotient.out a \ Quotient.out c) ∪ (Quotient.out b \ Quotient.out c) := by
    ext x; simp [or_and_right]
  exact hsub ▸ N.union₂ hac hbc

theorem le_top (a : AssociatedAlgebra N) : Le N a (top N) := by
  rw [show a = mk N (Quotient.out a) from (mk_out N a).symm]
  unfold top
  refine (le_mk N).mpr ?_
  have : Quotient.out a \ Set.univ = ∅ :=
    diff_eq_empty.mpr (subset_univ _)
  simpa [this] using N.empty

theorem bot_le (a : AssociatedAlgebra N) : Le N (bot N) a := by
  rw [show a = mk N (Quotient.out a) from (mk_out N a).symm]
  unfold bot
  refine (le_mk N).mpr ?_
  have : (∅ \ Quotient.out a) = ∅ := empty_diff _
  simpa [this] using N.empty

theorem inf_compl_le_bot (a : AssociatedAlgebra N) :
    Le N (inf N a (compl N a)) (bot N) := by
  have hempty : Quotient.out a ∩ (Quotient.out a)ᶜ = ∅ := by
    ext x; simp only [mem_inter_iff, mem_compl_iff]; tauto
  have : inf N a (compl N a) = mk N ∅ := by
    unfold inf compl
    refine (mk_eq_iff N).mpr ?_
    have hΔ : aeEq N
        (Quotient.out a ∩ Quotient.out (mk N (Quotient.out a)ᶜ))
        (Quotient.out a ∩ (Quotient.out a)ᶜ) :=
      aeEq_inter N (aeEq_refl N _) (aeEq_out N)
    simpa [hempty] using hΔ
  rw [this, bot]
  exact le_refl N _

theorem top_le_sup_compl (a : AssociatedAlgebra N) :
    Le N (top N) (sup N a (compl N a)) := by
  have huniv : Quotient.out a ∪ (Quotient.out a)ᶜ = Set.univ := by
    ext x; simp only [mem_union, mem_compl_iff]; tauto
  have : sup N a (compl N a) = mk N Set.univ := by
    unfold sup compl
    refine (mk_eq_iff N).mpr ?_
    have hΔ : aeEq N
        (Quotient.out a ∪ Quotient.out (mk N (Quotient.out a)ᶜ))
        (Quotient.out a ∪ (Quotient.out a)ᶜ) :=
      aeEq_union N (aeEq_refl N _) (aeEq_out N)
    simpa [huniv] using hΔ
  rw [this, top]
  exact le_refl N _

theorem le_sup_inf (a b c : AssociatedAlgebra N) :
    Le N (inf N (sup N a b) (sup N a c)) (sup N a (inf N b c)) := by
  have hL : inf N (sup N a b) (sup N a c) =
      mk N ((Quotient.out a ∪ Quotient.out b) ∩ (Quotient.out a ∪ Quotient.out c)) := by
    change mk N (Quotient.out (sup N a b) ∩ Quotient.out (sup N a c)) = _
    exact (mk_eq_iff N).mpr (aeEq_inter N
      (aeEq_out (s := Quotient.out a ∪ Quotient.out b) N)
      (aeEq_out (s := Quotient.out a ∪ Quotient.out c) N))
  have hR : sup N a (inf N b c) =
      mk N (Quotient.out a ∪ (Quotient.out b ∩ Quotient.out c)) := by
    change mk N (Quotient.out a ∪ Quotient.out (inf N b c)) = _
    exact (mk_eq_iff N).mpr (aeEq_union N (aeEq_refl N _)
      (aeEq_out (s := Quotient.out b ∩ Quotient.out c) N))
  rw [hL, hR]
  refine (le_mk N).mpr ?_
  have : ((Quotient.out a ∪ Quotient.out b) ∩ (Quotient.out a ∪ Quotient.out c)) \
      (Quotient.out a ∪ (Quotient.out b ∩ Quotient.out c)) = ∅ := by
    ext x; simp only [mem_empty_iff_false, mem_sdiff, mem_inter_iff, mem_union]; tauto
  simpa [this] using N.empty

theorem sSup_spec (S : Set (AssociatedAlgebra N)) :
    (∀ a ∈ S, Le N a (sSup N S)) ∧
      ∀ b, (∀ a ∈ S, Le N a b) → Le N (sSup N S) b := by
  let f : S → Set X := fun a => Quotient.out (a : AssociatedAlgebra N)
  obtain ⟨hu, hleast⟩ := Classical.choose_spec (N.essentialSup f)
  constructor
  · intro a ha
    unfold sSup
    rw [show a = mk N (Quotient.out a) from (mk_out N a).symm]
    exact (le_mk N).mpr (hu ⟨a, ha⟩)
  · intro b hb
    unfold sSup
    rw [show b = mk N (Quotient.out b) from (mk_out N b).symm]
    refine (le_mk N).mpr ?_
    have hv : ∀ a : S, N.negligible (f a \ Quotient.out b) := fun a => hb a.1 a.2
    exact hleast (Quotient.out b) hv

theorem compl_compl_mk (a : AssociatedAlgebra N) : compl N (compl N a) = a := by
  unfold compl
  change mk N (Quotient.out (mk N (Quotient.out a)ᶜ))ᶜ = a
  have h : mk N (Quotient.out (mk N (Quotient.out a)ᶜ))ᶜ =
      mk N ((Quotient.out a)ᶜ)ᶜ :=
    (mk_eq_iff N).mpr (aeEq_compl N (aeEq_out N))
  rw [h, compl_compl, mk_out]

theorem le_compl_of_le {a b : AssociatedAlgebra N} (h : Le N a b) :
    Le N (compl N b) (compl N a) := by
  unfold compl
  refine (le_mk N).mpr ?_
  have heq : (Quotient.out b)ᶜ \ (Quotient.out a)ᶜ =
      Quotient.out a \ Quotient.out b := by
    ext x; simp; tauto
  exact heq ▸ h

theorem le_compl_comm {a b : AssociatedAlgebra N} :
    Le N a b ↔ Le N (compl N b) (compl N a) := by
  constructor
  · exact le_compl_of_le N
  · intro h
    simpa [compl_compl_mk] using le_compl_of_le N h

theorem sInf_spec (S : Set (AssociatedAlgebra N)) :
    (∀ a ∈ S, Le N (sInf N S) a) ∧
      ∀ b, (∀ a ∈ S, Le N b a) → Le N b (sInf N S) := by
  constructor
  · intro a ha
    unfold sInf
    have hmem : compl N a ∈ compl N '' S := ⟨a, ha, rfl⟩
    have hle := (sSup_spec N (compl N '' S)).1 (compl N a) hmem
    exact (le_compl_comm (a := sInf N S) (b := a)).mpr
      (by simpa [sInf, compl_compl_mk] using hle)
  · intro b hb
    unfold sInf
    have hle : ∀ c ∈ compl N '' S, Le N c (compl N b) := by
      intro c hc
      obtain ⟨a, ha, rfl⟩ := hc
      exact (le_compl_comm (a := b) (b := a)).mp (hb a ha)
    have hsup := (sSup_spec N (compl N '' S)).2 (compl N b) hle
    exact (le_compl_comm (a := b) (b := sInf N S)).mpr
      (by simpa [sInf, compl_compl_mk] using hsup)

theorem le_sSup (S : Set (AssociatedAlgebra N)) {a : AssociatedAlgebra N}
    (ha : a ∈ S) : Le N a (sSup N S) :=
  (sSup_spec N S).1 a ha

theorem sSup_le (S : Set (AssociatedAlgebra N)) {b : AssociatedAlgebra N}
    (h : ∀ a ∈ S, Le N a b) : Le N (sSup N S) b :=
  (sSup_spec N S).2 b h

theorem sInf_le (S : Set (AssociatedAlgebra N)) {a : AssociatedAlgebra N}
    (ha : a ∈ S) : Le N (sInf N S) a :=
  (sInf_spec N S).1 a ha

theorem le_sInf (S : Set (AssociatedAlgebra N)) {b : AssociatedAlgebra N}
    (h : ∀ a ∈ S, Le N b a) : Le N b (sInf N S) :=
  (sInf_spec N S).2 b h

noncomputable instance instPartialOrder : PartialOrder (AssociatedAlgebra N) where
  le := Le N
  le_refl := le_refl N
  le_trans := le_trans N
  lt a b := Le N a b ∧ ¬ Le N b a
  lt_iff_le_not_ge _ _ := Iff.rfl
  le_antisymm := le_antisymm N

noncomputable instance instLattice : Lattice (AssociatedAlgebra N) where
  __ := instPartialOrder N
  sup := sup N
  inf := inf N
  le_sup_left := le_sup_left N
  le_sup_right := le_sup_right N
  sup_le := fun a b c => sup_le N a b c
  inf_le_left := inf_le_left N
  inf_le_right := inf_le_right N
  le_inf := fun a b c => le_inf N a b c

noncomputable instance instCompleteLattice : CompleteLattice (AssociatedAlgebra N) where
  __ := instLattice N
  sSup := sSup N
  sInf := sInf N
  isLUB_sSup S := ⟨fun a ha => le_sSup N S ha, fun b hb => sSup_le N S hb⟩
  isGLB_sInf S := ⟨fun a ha => sInf_le N S ha, fun b hb => le_sInf N S hb⟩
  top := top N
  bot := bot N
  le_top := le_top N
  bot_le := bot_le N

noncomputable instance instBooleanAlgebra : BooleanAlgebra (AssociatedAlgebra N) where
  __ := instCompleteLattice N
  compl := compl N
  sdiff a b := inf N a (compl N b)
  himp a b := sup N b (compl N a)
  inf_compl_le_bot := inf_compl_le_bot N
  top_le_sup_compl := top_le_sup_compl N
  le_top := le_top N
  bot_le := bot_le N
  sdiff_eq _ _ := rfl
  himp_eq _ _ := rfl
  le_sup_inf := le_sup_inf N

noncomputable instance instCompleteBooleanAlgebra :
    CompleteBooleanAlgebra (AssociatedAlgebra N) where
  __ := instCompleteLattice N
  __ := instBooleanAlgebra N

theorem mk_bot : mk N ∅ = (⊥ : AssociatedAlgebra N) := rfl

theorem mk_top : mk N Set.univ = (⊤ : AssociatedAlgebra N) := rfl

end AssociatedAlgebra

end Scott2026
