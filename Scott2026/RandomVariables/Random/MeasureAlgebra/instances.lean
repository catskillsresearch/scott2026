/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/

import Mathlib.MeasureTheory.MeasurableSpace.Basic
import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
import Scott2026.RandomVariables.Random.MeasureAlgebra
import Scott2026.RandomVariables.Random.MeasureAlgebra.Le
import Scott2026.RandomVariables.Random.MeasureAlgebra.mk
import Scott2026.RandomVariables.Random.MeasureAlgebra.inf
import Scott2026.RandomVariables.Random.MeasureAlgebra.sup
import Scott2026.RandomVariables.Random.MeasureAlgebra.compl
import Scott2026.RandomVariables.Random.MeasureAlgebra.bot
import Scott2026.RandomVariables.Random.MeasureAlgebra.top
import Scott2026.RandomVariables.Random.MeasureAlgebra.sSup
import Scott2026.RandomVariables.Random.MeasureAlgebra.sInf
import Scott2026.RandomVariables.Random.MeasureAlgebra.outAe
import Scott2026.RandomVariables.Random.MeasureAlgebra.sSupWitness
import Scott2026.RandomVariables.Random.symmDiff

namespace Scott2026

open MeasureTheory Set

variable {X : Type*} [MeasurableSpace X] (μ : MeasureTheory.Measure X)

namespace MeasureAlgebra

theorem le_refl (a : _root_.Scott2026.MeasureAlgebra μ) : Le μ a a := by
  simp [Le]

theorem le_trans (a b c : _root_.Scott2026.MeasureAlgebra μ)
    (hab : Le μ a b) (hbc : Le μ b c) : Le μ a c := by
  have hsub : (Quotient.out a).val \ (Quotient.out c).val ⊆
      ((Quotient.out a).val \ (Quotient.out b).val) ∪
        ((Quotient.out b).val \ (Quotient.out c).val) := by
    intro x hx
    simp only [mem_union, mem_sdiff] at hx ⊢
    tauto
  exact measure_mono_null hsub (measure_union_null hab hbc)

theorem le_antisymm (a b : _root_.Scott2026.MeasureAlgebra μ)
    (hab : Le μ a b) (hba : Le μ b a) : a = b := by
  have : μ (symmDiff (Quotient.out a).val (Quotient.out b).val) = 0 := by
    simpa [symmDiff_def] using measure_union_null hab hba
  calc a = mk μ (Quotient.out a).val (Quotient.out a).property := (mk_out μ a).symm
    _ = mk μ (Quotient.out b).val (Quotient.out b).property := (mk_eq_iff μ).mpr this
    _ = b := mk_out μ b

theorem inf_le_left (a b : _root_.Scott2026.MeasureAlgebra μ) : Le μ (inf μ a b) a := by
  rw [show a = mk μ (Quotient.out a).val (Quotient.out a).property from
    (mk_out μ a).symm]
  unfold inf
  refine (le_mk μ).mpr ?_
  have : ((Quotient.out a).val ∩ (Quotient.out b).val) \
      (Quotient.out a).val = ∅ := by
    ext x; simp only [mem_empty_iff_false, mem_sdiff, mem_inter_iff]; tauto
  simpa [this] using measure_empty

theorem inf_le_right (a b : _root_.Scott2026.MeasureAlgebra μ) : Le μ (inf μ a b) b := by
  rw [show b = mk μ (Quotient.out b).val (Quotient.out b).property from
    (mk_out μ b).symm]
  unfold inf
  refine (le_mk μ).mpr ?_
  have : ((Quotient.out a).val ∩ (Quotient.out b).val) \
      (Quotient.out b).val = ∅ := by
    ext x; simp only [mem_empty_iff_false, mem_sdiff, mem_inter_iff]; tauto
  simpa [this] using measure_empty

theorem le_inf (a b c : _root_.Scott2026.MeasureAlgebra μ)
    (hab : Le μ a b) (hac : Le μ a c) : Le μ a (inf μ b c) := by
  rw [show a = mk μ (Quotient.out a).val (Quotient.out a).property from
    (mk_out μ a).symm]
  unfold inf
  refine (le_mk μ).mpr ?_
  have hsub : (Quotient.out a).val \
      ((Quotient.out b).val ∩ (Quotient.out c).val) =
      ((Quotient.out a).val \ (Quotient.out b).val) ∪
        ((Quotient.out a).val \ (Quotient.out c).val) := by
    ext x; simp; tauto
  exact hsub ▸ measure_union_null hab hac

theorem le_sup_left (a b : _root_.Scott2026.MeasureAlgebra μ) : Le μ a (sup μ a b) := by
  rw [show a = mk μ (Quotient.out a).val (Quotient.out a).property from
    (mk_out μ a).symm]
  unfold sup
  refine (le_mk μ).mpr ?_
  have : (Quotient.out a).val \
      ((Quotient.out a).val ∪ (Quotient.out b).val) = ∅ := by
    ext x; simp only [mem_empty_iff_false, mem_sdiff, mem_union]; tauto
  simpa [this] using measure_empty

theorem le_sup_right (a b : _root_.Scott2026.MeasureAlgebra μ) : Le μ b (sup μ a b) := by
  rw [show b = mk μ (Quotient.out b).val (Quotient.out b).property from
    (mk_out μ b).symm]
  unfold sup
  refine (le_mk μ).mpr ?_
  have : (Quotient.out b).val \
      ((Quotient.out a).val ∪ (Quotient.out b).val) = ∅ := by
    ext x; simp only [mem_empty_iff_false, mem_sdiff, mem_union]; tauto
  simpa [this] using measure_empty

theorem sup_le (a b c : _root_.Scott2026.MeasureAlgebra μ)
    (hac : Le μ a c) (hbc : Le μ b c) : Le μ (sup μ a b) c := by
  rw [show c = mk μ (Quotient.out c).val (Quotient.out c).property from
    (mk_out μ c).symm]
  unfold sup
  refine (le_mk μ).mpr ?_
  have hsub : ((Quotient.out a).val ∪ (Quotient.out b).val) \
      (Quotient.out c).val =
      ((Quotient.out a).val \ (Quotient.out c).val) ∪
        ((Quotient.out b).val \ (Quotient.out c).val) := by
    ext x; simp [or_and_right]
  exact hsub ▸ measure_union_null hac hbc

theorem le_top (a : _root_.Scott2026.MeasureAlgebra μ) : Le μ a (top μ) := by
  rw [show a = mk μ (Quotient.out a).val (Quotient.out a).property from
    (mk_out μ a).symm]
  unfold top
  refine (le_mk μ).mpr ?_
  have : (Quotient.out a).val \ Set.univ = ∅ :=
    diff_eq_empty.mpr (subset_univ _)
  simpa [this] using measure_empty

theorem bot_le (a : _root_.Scott2026.MeasureAlgebra μ) : Le μ (bot μ) a := by
  rw [show a = mk μ (Quotient.out a).val (Quotient.out a).property from
    (mk_out μ a).symm]
  unfold bot
  refine (le_mk μ).mpr ?_
  have : (∅ \ (Quotient.out a).val) = ∅ := empty_diff _
  simpa [this] using measure_empty

theorem inf_compl_le_bot (a : _root_.Scott2026.MeasureAlgebra μ) :
    Le μ (inf μ a (compl μ a)) (bot μ) := by
  have hempty : (Quotient.out a).val ∩ (Quotient.out a).valᶜ = ∅ := by
    ext x; simp only [mem_inter_iff, mem_compl_iff]; tauto
  have : inf μ a (compl μ a) = mk μ ∅ MeasurableSet.empty := by
    unfold inf compl
    refine (mk_eq_iff μ).mpr ?_
    have hΔ : μ (symmDiff
        ((Quotient.out a).val ∩
          (Quotient.out (mk μ (Quotient.out a).valᶜ
            (Quotient.out a).property.compl)).val)
        ((Quotient.out a).val ∩ (Quotient.out a).valᶜ)) = 0 :=
      measAe_inter (by simp [symmDiff_self])
        (measAe_symm (mk_out_ae (Quotient.out a).property.compl))
    simpa [hempty] using hΔ
  rw [this, bot]
  exact le_refl μ _

theorem top_le_sup_compl (a : _root_.Scott2026.MeasureAlgebra μ) :
    Le μ (top μ) (sup μ a (compl μ a)) := by
  have huniv : (Quotient.out a).val ∪ (Quotient.out a).valᶜ = Set.univ := by
    ext x; simp only [mem_union, mem_compl_iff]; tauto
  have : sup μ a (compl μ a) = mk μ Set.univ MeasurableSet.univ := by
    unfold sup compl
    refine (mk_eq_iff μ).mpr ?_
    have hΔ : μ (symmDiff
        ((Quotient.out a).val ∪
          (Quotient.out (mk μ (Quotient.out a).valᶜ
            (Quotient.out a).property.compl)).val)
        ((Quotient.out a).val ∪ (Quotient.out a).valᶜ)) = 0 :=
      measAe_union (by simp [symmDiff_self])
        (measAe_symm (mk_out_ae (Quotient.out a).property.compl))
    simpa [huniv] using hΔ
  rw [this, top]
  exact le_refl μ _

theorem le_sup_inf (a b c : _root_.Scott2026.MeasureAlgebra μ) :
    Le μ (inf μ (sup μ a b) (sup μ a c)) (sup μ a (inf μ b c)) := by
  have hL : inf μ (sup μ a b) (sup μ a c) =
      mk μ (((Quotient.out a).val ∪ (Quotient.out b).val) ∩
        ((Quotient.out a).val ∪ (Quotient.out c).val))
        (((Quotient.out a).property.union (Quotient.out b).property).inter
          ((Quotient.out a).property.union (Quotient.out c).property)) := by
    change mk μ
        ((Quotient.out (sup μ a b)).val ∩ (Quotient.out (sup μ a c)).val) _ = _
    exact (mk_eq_iff μ).mpr (measAe_inter
      (measAe_symm (mk_out_ae (μ := μ)
        (s := (Quotient.out a).val ∪ (Quotient.out b).val)
        ((Quotient.out a).property.union (Quotient.out b).property)))
      (measAe_symm (mk_out_ae (μ := μ)
        (s := (Quotient.out a).val ∪ (Quotient.out c).val)
        ((Quotient.out a).property.union (Quotient.out c).property))))
  have hR : sup μ a (inf μ b c) =
      mk μ ((Quotient.out a).val ∪
        ((Quotient.out b).val ∩ (Quotient.out c).val))
        ((Quotient.out a).property.union
          ((Quotient.out b).property.inter (Quotient.out c).property)) := by
    change mk μ ((Quotient.out a).val ∪ (Quotient.out (inf μ b c)).val) _ = _
    exact (mk_eq_iff μ).mpr (measAe_union (by simp [symmDiff_self])
      (measAe_symm (mk_out_ae (μ := μ)
        (s := (Quotient.out b).val ∩ (Quotient.out c).val)
        ((Quotient.out b).property.inter (Quotient.out c).property))))
  rw [hL, hR]
  refine (le_mk μ).mpr ?_
  have : (((Quotient.out a).val ∪ (Quotient.out b).val) ∩
      ((Quotient.out a).val ∪ (Quotient.out c).val)) \
      ((Quotient.out a).val ∪ ((Quotient.out b).val ∩ (Quotient.out c).val)) =
      ∅ := by
    ext x; simp only [mem_empty_iff_false, mem_sdiff, mem_inter_iff, mem_union]; tauto
  simpa [this] using measure_empty

theorem sSup_spec [IsFiniteMeasure μ] (S : Set (_root_.Scott2026.MeasureAlgebra μ)) :
    (∀ a ∈ S, Le μ a (sSup μ S)) ∧
      ∀ b, (∀ a ∈ S, Le μ a b) → Le μ (sSup μ S) b := by
  obtain ⟨hu, hleast⟩ := (Classical.choose_spec (sSupWitness μ S)).2
  constructor
  · intro a ha
    unfold sSup
    rw [show a = mk μ (Quotient.out a).val (Quotient.out a).property from
      (mk_out μ a).symm]
    exact (le_mk μ).mpr (hu ⟨a, ha⟩)
  · intro b hb
    unfold sSup
    rw [show b = mk μ (Quotient.out b).val (Quotient.out b).property from
      (mk_out μ b).symm]
    refine (le_mk μ).mpr ?_
    exact hleast (Quotient.out b).val fun a => hb a.1 a.2

theorem compl_compl_mk (a : _root_.Scott2026.MeasureAlgebra μ) : compl μ (compl μ a) = a := by
  unfold compl
  have h : mk μ
      (Quotient.out (mk μ (Quotient.out a).valᶜ
        (Quotient.out a).property.compl)).valᶜ
      (Quotient.out (mk μ (Quotient.out a).valᶜ
        (Quotient.out a).property.compl)).property.compl =
      mk μ ((Quotient.out a).valᶜ)ᶜ (Quotient.out a).property.compl.compl :=
    (mk_eq_iff μ).mpr (measAe_compl (measAe_symm (mk_out_ae (μ := μ)
      (s := (Quotient.out a).valᶜ) (Quotient.out a).property.compl)))
  refine h.trans ?_
  have h2 : mk μ ((Quotient.out a).valᶜ)ᶜ (Quotient.out a).property.compl.compl =
      mk μ (Quotient.out a).val (Quotient.out a).property := by
    refine (mk_eq_iff μ).mpr ?_
    have heq : ((Quotient.out a).valᶜ)ᶜ = (Quotient.out a).val := compl_compl _
    simpa [heq, symmDiff_self]
  exact h2.trans (mk_out μ a)

theorem le_compl_of_le {a b : _root_.Scott2026.MeasureAlgebra μ} (h : Le μ a b) :
    Le μ (compl μ b) (compl μ a) := by
  unfold compl
  refine (le_mk μ).mpr ?_
  have heq : (Quotient.out b).valᶜ \ (Quotient.out a).valᶜ =
      (Quotient.out a).val \ (Quotient.out b).val := by
    ext x; simp; tauto
  exact heq ▸ h

theorem le_compl_comm {a b : _root_.Scott2026.MeasureAlgebra μ} :
    Le μ a b ↔ Le μ (compl μ b) (compl μ a) := by
  constructor
  · exact le_compl_of_le μ
  · intro h
    simpa [compl_compl_mk] using le_compl_of_le μ h

theorem sInf_spec [IsFiniteMeasure μ] (S : Set (_root_.Scott2026.MeasureAlgebra μ)) :
    (∀ a ∈ S, Le μ (sInf μ S) a) ∧
      ∀ b, (∀ a ∈ S, Le μ b a) → Le μ b (sInf μ S) := by
  constructor
  · intro a ha
    unfold sInf
    have hmem : compl μ a ∈ compl μ '' S := ⟨a, ha, rfl⟩
    have hle := (sSup_spec μ (compl μ '' S)).1 (compl μ a) hmem
    exact (le_compl_comm (a := sInf μ S) (b := a)).mpr
      (by simpa [sInf, compl_compl_mk] using hle)
  · intro b hb
    unfold sInf
    have hle : ∀ c ∈ compl μ '' S, Le μ c (compl μ b) := by
      intro c hc
      obtain ⟨a, ha, rfl⟩ := hc
      exact (le_compl_comm (a := b) (b := a)).mp (hb a ha)
    have hsup := (sSup_spec μ (compl μ '' S)).2 (compl μ b) hle
    exact (le_compl_comm (a := b) (b := sInf μ S)).mpr
      (by simpa [sInf, compl_compl_mk] using hsup)

theorem le_sSup [IsFiniteMeasure μ] (S : Set (_root_.Scott2026.MeasureAlgebra μ))
    {a : _root_.Scott2026.MeasureAlgebra μ} (ha : a ∈ S) : Le μ a (sSup μ S) :=
  (sSup_spec μ S).1 a ha

theorem sSup_le [IsFiniteMeasure μ] (S : Set (_root_.Scott2026.MeasureAlgebra μ))
    {b : _root_.Scott2026.MeasureAlgebra μ} (h : ∀ a ∈ S, Le μ a b) : Le μ (sSup μ S) b :=
  (sSup_spec μ S).2 b h

theorem sInf_le [IsFiniteMeasure μ] (S : Set (_root_.Scott2026.MeasureAlgebra μ))
    {a : _root_.Scott2026.MeasureAlgebra μ} (ha : a ∈ S) : Le μ (sInf μ S) a :=
  (sInf_spec μ S).1 a ha

theorem le_sInf [IsFiniteMeasure μ] (S : Set (_root_.Scott2026.MeasureAlgebra μ))
    {b : _root_.Scott2026.MeasureAlgebra μ} (h : ∀ a ∈ S, Le μ b a) : Le μ b (sInf μ S) :=
  (sInf_spec μ S).2 b h

noncomputable instance instPartialOrder [IsFiniteMeasure μ] :
    PartialOrder (_root_.Scott2026.MeasureAlgebra μ) where
  le := Le μ
  le_refl := le_refl μ
  le_trans := le_trans μ
  lt a b := Le μ a b ∧ ¬ Le μ b a
  lt_iff_le_not_ge _ _ := Iff.rfl
  le_antisymm := le_antisymm μ

noncomputable instance instLattice [IsFiniteMeasure μ] :
    Lattice (_root_.Scott2026.MeasureAlgebra μ) where
  __ := instPartialOrder μ
  sup := sup μ
  inf := inf μ
  le_sup_left := le_sup_left μ
  le_sup_right := le_sup_right μ
  sup_le := fun a b c => sup_le μ a b c
  inf_le_left := inf_le_left μ
  inf_le_right := inf_le_right μ
  le_inf := fun a b c => le_inf μ a b c

noncomputable instance instCompleteLattice [IsFiniteMeasure μ] :
    CompleteLattice (_root_.Scott2026.MeasureAlgebra μ) where
  __ := instLattice μ
  sSup := sSup μ
  sInf := sInf μ
  isLUB_sSup S := ⟨fun a ha => le_sSup μ S ha, fun b hb => sSup_le μ S hb⟩
  isGLB_sInf S := ⟨fun a ha => sInf_le μ S ha, fun b hb => le_sInf μ S hb⟩
  top := top μ
  bot := bot μ
  le_top := le_top μ
  bot_le := bot_le μ

noncomputable instance instBooleanAlgebra [IsFiniteMeasure μ] :
    BooleanAlgebra (_root_.Scott2026.MeasureAlgebra μ) where
  __ := instCompleteLattice μ
  compl := compl μ
  sdiff a b := inf μ a (compl μ b)
  himp a b := sup μ b (compl μ a)
  inf_compl_le_bot := inf_compl_le_bot μ
  top_le_sup_compl := top_le_sup_compl μ
  le_top := le_top μ
  bot_le := bot_le μ
  sdiff_eq _ _ := rfl
  himp_eq _ _ := rfl
  le_sup_inf := le_sup_inf μ

noncomputable instance instCompleteBooleanAlgebra [IsFiniteMeasure μ] :
    CompleteBooleanAlgebra (_root_.Scott2026.MeasureAlgebra μ) where
  __ := instCompleteLattice μ
  __ := instBooleanAlgebra μ

theorem mk_bot [IsFiniteMeasure μ] :
    mk μ ∅ MeasurableSet.empty = (⊥ : _root_.Scott2026.MeasureAlgebra μ) :=
  rfl

theorem mk_top [IsFiniteMeasure μ] :
    mk μ Set.univ MeasurableSet.univ = (⊤ : _root_.Scott2026.MeasureAlgebra μ) :=
  rfl

theorem mk_eq_bot [IsFiniteMeasure μ] {s : Set X} {hs : MeasurableSet s} :
    mk μ s hs = (⊥ : _root_.Scott2026.MeasureAlgebra μ) ↔ μ s = 0 := by
  rw [← mk_bot, mk_eq_iff, ae_empty_iff]

theorem mk_eq_top [IsFiniteMeasure μ] {s : Set X} {hs : MeasurableSet s} :
    mk μ s hs = (⊤ : _root_.Scott2026.MeasureAlgebra μ) ↔ μ sᶜ = 0 := by
  rw [← mk_top, mk_eq_iff]
  have : symmDiff s (Set.univ : Set X) = sᶜ := by
    ext x
    simp [symmDiff]
  simp [this]

end MeasureAlgebra

end Scott2026
