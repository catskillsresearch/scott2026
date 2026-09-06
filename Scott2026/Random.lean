/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/

import Mathlib.MeasureTheory.MeasurableSpace.Basic
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import Mathlib.Order.Atoms
import Mathlib.Data.Countable.Defs
import Mathlib.Data.Countable.Small
import Mathlib.Logic.Encodable.Basic
import Mathlib.Order.CompleteLattice.Finset
import Scott2026.Setoid
import Scott2026.PowerSet
import Scott2026.Engeler

/-!
# Domain-valued random variables (Definitions 37–41, Propositions 39–40)

`ℒ⁰(X; 𝒫(Y))` is the set of measurable maps `X → Set Y`. Quotienting by a
σ-ideal of negligible sets yields an `A(X)`-poset (Lemma 38). `G_X` is the
strict `A(X)`-poset isomorphism of Proposition 39; application is the
homomorphism of Proposition 40.
-/

open MeasureTheory Set

namespace Scott2026

variable {X Y : Type*} [MeasurableSpace X]

/-- Positive / Scott subbasic sets `B_y = {S | y ∈ S}` (paper §5). -/
def posBasic (y : Y) : Set (Set Y) := {S | y ∈ S}

/-- Definition 37: measurable maps into `Set Y` (Borel of the positive topology).
We take measurability of all preimages of `B_y`, which generate that σ-algebra
when `Y` is countable. -/
def IsL0 (a : X → Set Y) : Prop :=
  ∀ y : Y, MeasurableSet (a ⁻¹' posBasic y)

/-- Definition 37: `ℒ⁰`-valued order. -/
def l0Le (a b : X → Set Y) : Set X := {x | a x ⊆ b x}

/-- Definition 37: `ℒ⁰`-valued equality. -/
def l0Eq (a b : X → Set Y) : Set X := {x | a x = b x}

theorem l0Le_refl (a : X → Set Y) : l0Le a a = Set.univ := by
  ext x; simp [l0Le]

theorem l0Le_trans (a b c : X → Set Y) : l0Le a b ∩ l0Le b c ⊆ l0Le a c := by
  intro x hx
  simp [l0Le] at hx ⊢
  exact hx.1.trans hx.2

theorem l0Eq_eq_le (a b : X → Set Y) : l0Eq a b = l0Le a b ∩ l0Le b a := by
  ext x
  simp [l0Eq, l0Le]
  exact Set.Subset.antisymm_iff

/-- Definition 37: the three clauses. -/
theorem definition_37 (a b : X → Set Y) :
    IsL0 a = (∀ y : Y, MeasurableSet (a ⁻¹' posBasic y)) ∧
      l0Le a b = {x | a x ⊆ b x} ∧
      l0Eq a b = {x | a x = b x} :=
  ⟨rfl, rfl, rfl⟩

/-- Lemma 38, unquotiented: `ℒ⁰` is an `A`-poset for `A = Set X`. -/
def l0APoset : APoset (A := Set X) (X → Set Y) where
  le := l0Le
  trans := fun a b c => l0Le_trans a b c
  le_le_refl := fun a b => by
    intro x _hx
    exact ⟨by simp [l0Le], by simp [l0Le]⟩

/-- A negligibility space (paper §5): a measurable space with a σ-ideal `N`
such that `Σ / N` is complete, not merely σ-complete. Completeness is
packaged as existence of essential suprema. -/
structure NegligibilitySpace (X : Type*) [MeasurableSpace X] where
  negligible : Set X → Prop
  empty : negligible ∅
  mono : ∀ {s t}, s ⊆ t → negligible t → negligible s
  union : ∀ s : ℕ → Set X, (∀ n, negligible (s n)) → negligible (⋃ n, s n)
  essentialSup : ∀ {ι : Type*} (s : ι → Set X),
    ∃ u : Set X,
      (∀ i, negligible (s i \ u)) ∧
        ∀ v : Set X, (∀ i, negligible (s i \ v)) → negligible (u \ v)
  /-- Every set is a.e. equal to a measurable representative (`A(X) = Σ/𝒩`). -/
  measurableRep : ∀ s : Set X, ∃ t : Set X, MeasurableSet t ∧ negligible (symmDiff s t)

namespace NegligibilitySpace

variable {X : Type*} [MeasurableSpace X] (N : NegligibilitySpace X)

noncomputable def measRep (s : Set X) : Set X :=
  Classical.choose (N.measurableRep s)

theorem measRep_measurable (s : Set X) : MeasurableSet (N.measRep s) :=
  (Classical.choose_spec (N.measurableRep s)).1

theorem measRep_symmDiff (s : Set X) : N.negligible (symmDiff s (N.measRep s)) :=
  (Classical.choose_spec (N.measurableRep s)).2

theorem union_countable {ι : Type*} [Countable ι] (s : ι → Set X)
    (hs : ∀ i, N.negligible (s i)) : N.negligible (⋃ i, s i) := by
  cases isEmpty_or_nonempty ι with
  | inl _ =>
    simp [iUnion_of_empty]; exact N.empty
  | inr hne =>
    obtain ⟨f, hf⟩ := exists_surjective_nat ι
    have : ⋃ i, s i = ⋃ n, s (f n) := by
      ext x
      constructor
      · intro hx
        obtain ⟨i, hi⟩ := mem_iUnion.mp hx
        obtain ⟨n, rfl⟩ := hf i
        exact mem_iUnion.mpr ⟨n, hi⟩
      · intro hx
        obtain ⟨n, hn⟩ := mem_iUnion.mp hx
        exact mem_iUnion.mpr ⟨f n, hn⟩
    exact this ▸ N.union (fun n => s (f n)) (fun n => hs _)

theorem union₂ {s t : Set X} (hs : N.negligible s) (ht : N.negligible t) :
    N.negligible (s ∪ t) := by
  let f : ℕ → Set X := fun n => if n = 0 then s else t
  have hf : ∀ n, N.negligible (f n) := fun n => by
    by_cases hn : n = 0
    · subst hn; exact hs
    · simp [f, hn, ht]
  have hunion := N.union f hf
  have : ⋃ n, f n = s ∪ t := by
    ext x
    constructor
    · intro hx
      obtain ⟨n, hx⟩ := mem_iUnion.mp hx
      by_cases hn : n = 0
      · exact Or.inl (by simpa [f, hn] using hx)
      · exact Or.inr (by simpa [f, hn] using hx)
    · intro hx
      rcases hx with hxs | hxt
      · exact mem_iUnion.mpr ⟨0, by simp [f, hxs]⟩
      · exact mem_iUnion.mpr ⟨1, by simp [f, hxt]⟩
  exact this ▸ hunion

end NegligibilitySpace

/-! ## Set identities for symmetric difference -/

theorem symmDiff_triangle_subset {α : Type*} (s t u : Set α) :
    symmDiff s u ⊆ symmDiff s t ∪ symmDiff t u := by
  intro x
  simp only [mem_union, mem_symmDiff]
  tauto

theorem union_symmDiff_subset {α : Type*} (s t s' t' : Set α) :
    symmDiff (s ∪ t) (s' ∪ t') ⊆ symmDiff s s' ∪ symmDiff t t' := by
  intro x
  simp only [mem_union, mem_symmDiff]
  tauto

theorem inter_symmDiff_subset {α : Type*} (s t s' t' : Set α) :
    symmDiff (s ∩ t) (s' ∩ t') ⊆ symmDiff s s' ∪ symmDiff t t' := by
  intro x
  simp only [mem_union, mem_inter_iff, mem_symmDiff]
  tauto

theorem sdiff_symmDiff_subset {α : Type*} (s t s' t' : Set α) :
    symmDiff (s \ t) (s' \ t') ⊆ symmDiff s s' ∪ symmDiff t t' := by
  intro x
  simp only [mem_union, mem_sdiff, mem_symmDiff]
  tauto

theorem sdiff_subset_symmDiff {α : Type*} (s t : Set α) : s \ t ⊆ symmDiff s t :=
  subset_union_left

/-!
## `A(X) = Σ / 𝒩` as a complete Boolean algebra
-/

def aeEq (N : NegligibilitySpace X) (s t : Set X) : Prop :=
  N.negligible (symmDiff s t)

theorem aeEq_refl (N : NegligibilitySpace X) (s : Set X) : aeEq N s s := by
  simpa [aeEq, symmDiff_self] using N.empty

theorem aeEq_symm (N : NegligibilitySpace X) {s t : Set X} (h : aeEq N s t) :
    aeEq N t s := by
  simpa [aeEq, symmDiff_comm] using h

theorem aeEq_trans (N : NegligibilitySpace X) {s t u : Set X}
    (hst : aeEq N s t) (htu : aeEq N t u) : aeEq N s u :=
  N.mono (symmDiff_triangle_subset s t u) (N.union₂ hst htu)

theorem aeEq_iseqv (N : NegligibilitySpace X) : Equivalence (aeEq N) :=
  ⟨aeEq_refl N, fun {_ _} => aeEq_symm N, fun {_ _ _} => aeEq_trans N⟩

def aeSetoid (N : NegligibilitySpace X) : Setoid (Set X) where
  r := aeEq N
  iseqv := aeEq_iseqv N

/-- The complete Boolean algebra associated to a negligibility space. -/
abbrev AssociatedAlgebra (N : NegligibilitySpace X) : Type _ :=
  Quotient (aeSetoid N)

namespace AssociatedAlgebra

variable {X : Type*} [MeasurableSpace X] (N : NegligibilitySpace X)

def mk (s : Set X) : AssociatedAlgebra N :=
  Quotient.mk (aeSetoid N) s

theorem mk_eq_iff {s t : Set X} : mk N s = mk N t ↔ aeEq N s t :=
  Quotient.eq

@[simp] theorem mk_out (a : AssociatedAlgebra N) : mk N (Quotient.out a) = a :=
  Quotient.out_eq a

theorem aeEq_out {s : Set X} : aeEq N (Quotient.out (mk N s)) s :=
  (mk_eq_iff N).mp (mk_out N (mk N s))

theorem aeEq_empty_iff {s : Set X} : aeEq N s ∅ ↔ N.negligible s := by
  constructor
  · intro h
    simpa [aeEq, symmDiff_def] using h
  · intro hs
    simpa [aeEq, symmDiff_def] using hs

theorem aeEq_union {s s' t t' : Set X} (hs : aeEq N s s') (ht : aeEq N t t') :
    aeEq N (s ∪ t) (s' ∪ t') :=
  N.mono (union_symmDiff_subset s t s' t') (N.union₂ hs ht)

theorem aeEq_inter {s s' t t' : Set X} (hs : aeEq N s s') (ht : aeEq N t t') :
    aeEq N (s ∩ t) (s' ∩ t') :=
  N.mono (inter_symmDiff_subset s t s' t') (N.union₂ hs ht)

theorem aeEq_compl {s t : Set X} (h : aeEq N s t) : aeEq N sᶜ tᶜ := by
  have : symmDiff sᶜ tᶜ = symmDiff s t := by
    ext x
    simp only [mem_symmDiff, mem_compl_iff]
    tauto
  unfold aeEq at h ⊢
  rwa [this]

theorem aeEq_sdiff {s s' t t' : Set X} (hs : aeEq N s s') (ht : aeEq N t t') :
    aeEq N (s \ t) (s' \ t') :=
  N.mono (sdiff_symmDiff_subset s t s' t') (N.union₂ hs ht)

noncomputable def inf (a b : AssociatedAlgebra N) : AssociatedAlgebra N :=
  mk N (Quotient.out a ∩ Quotient.out b)

noncomputable def sup (a b : AssociatedAlgebra N) : AssociatedAlgebra N :=
  mk N (Quotient.out a ∪ Quotient.out b)

noncomputable def compl (a : AssociatedAlgebra N) : AssociatedAlgebra N :=
  mk N (Quotient.out a)ᶜ

def top : AssociatedAlgebra N := mk N Set.univ

def bot : AssociatedAlgebra N := mk N ∅

theorem mk_union (s t : Set X) : mk N (s ∪ t) = sup N (mk N s) (mk N t) := by
  unfold sup
  exact (mk_eq_iff N).mpr
    (aeEq_union N (aeEq_symm N (aeEq_out N)) (aeEq_symm N (aeEq_out N)))

theorem mk_inter (s t : Set X) : mk N (s ∩ t) = inf N (mk N s) (mk N t) := by
  unfold inf
  exact (mk_eq_iff N).mpr
    (aeEq_inter N (aeEq_symm N (aeEq_out N)) (aeEq_symm N (aeEq_out N)))

theorem mk_compl (s : Set X) : mk N sᶜ = compl N (mk N s) := by
  unfold compl
  exact (mk_eq_iff N).mpr (aeEq_compl N (aeEq_symm N (aeEq_out N)))

/-- Order: `[s] ≤ [t]` iff `s \ t` is negligible. -/
def Le (a b : AssociatedAlgebra N) : Prop :=
  N.negligible (Quotient.out a \ Quotient.out b)

theorem le_mk {s t : Set X} : Le N (mk N s) (mk N t) ↔ N.negligible (s \ t) := by
  have hΔ : aeEq N (Quotient.out (mk N s) \ Quotient.out (mk N t)) (s \ t) :=
    aeEq_sdiff N (aeEq_out N) (aeEq_out N)
  constructor
  · intro h
    change N.negligible (Quotient.out (mk N s) \ Quotient.out (mk N t)) at h
    have hsub : s \ t ⊆
        (Quotient.out (mk N s) \ Quotient.out (mk N t)) ∪
          symmDiff (Quotient.out (mk N s) \ Quotient.out (mk N t)) (s \ t) := by
      intro x; simp [mem_union, mem_symmDiff, mem_sdiff]; tauto
    exact N.mono hsub (N.union₂ h hΔ)
  · intro h
    change N.negligible (Quotient.out (mk N s) \ Quotient.out (mk N t))
    have hsub : Quotient.out (mk N s) \ Quotient.out (mk N t) ⊆
        (s \ t) ∪
          symmDiff (Quotient.out (mk N s) \ Quotient.out (mk N t)) (s \ t) := by
      intro x; simp [mem_union, mem_symmDiff, mem_sdiff]; tauto
    exact N.mono hsub (N.union₂ h hΔ)

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

noncomputable def sSup (S : Set (AssociatedAlgebra N)) : AssociatedAlgebra N :=
  mk N (Classical.choose
    (N.essentialSup fun a : S => Quotient.out (a : AssociatedAlgebra N)))

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

noncomputable def sInf (S : Set (AssociatedAlgebra N)) : AssociatedAlgebra N :=
  compl N (sSup N (compl N '' S))

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

theorem mk_eq_bot {s : Set X} : mk N s = (⊥ : AssociatedAlgebra N) ↔ N.negligible s := by
  rw [← mk_bot, mk_eq_iff, aeEq_empty_iff]

theorem measRep_aeEq (s : Set X) : aeEq N s (N.measRep s) :=
  N.measRep_symmDiff s

theorem mk_measRep (s : Set X) : mk N (N.measRep s) = mk N s :=
  (mk_eq_iff N).mpr (aeEq_symm N (measRep_aeEq N s))

theorem inf_mk (s t : Set X) : mk N s ⊓ mk N t = mk N (s ∩ t) := by
  change inf N (mk N s) (mk N t) = mk N (s ∩ t)
  unfold inf
  exact (mk_eq_iff N).mpr
    (aeEq_inter N (aeEq_out N) (aeEq_out N))

theorem sup_mk (s t : Set X) : mk N s ⊔ mk N t = mk N (s ∪ t) := by
  change sup N (mk N s) (mk N t) = mk N (s ∪ t)
  unfold sup
  exact (mk_eq_iff N).mpr
    (aeEq_union N (aeEq_out N) (aeEq_out N))

theorem compl_mk (s : Set X) : (mk N s)ᶜ = mk N sᶜ :=
  (mk_compl N s).symm

theorem himp_mk (s t : Set X) : mk N s ⇨ mk N t = mk N (sᶜ ∪ t) := by
  rw [himp_eq, compl_mk, sup_mk, union_comm]

theorem iSup_mk {ι : Type*} [Countable ι] (s : ι → Set X) :
    (⨆ i, mk N (s i)) = mk N (⋃ i, s i) := by
  refine _root_.le_antisymm (iSup_le fun i => ?upper) ?least
  · change Le N (mk N (s i)) (mk N (⋃ j, s j))
    refine (le_mk N).mpr ?_
    have : s i \ ⋃ j, s j = ∅ := by
      ext x; simp only [mem_empty_iff_false, mem_sdiff, mem_iUnion]; tauto
    simpa [this] using N.empty
  · set u := ⨆ i, mk N (s i)
    have hu : u = mk N (Quotient.out u) := (mk_out N u).symm
    have hi : ∀ i, N.negligible (s i \ Quotient.out u) := fun i => by
      have hle : mk N (s i) ≤ u := le_iSup (fun j => mk N (s j)) i
      have : Le N (mk N (s i)) (mk N (Quotient.out u)) := by
        rwa [← hu]
      exact (le_mk N).mp this
    have hunion : N.negligible ((⋃ i, s i) \ Quotient.out u) := by
      have heq : (⋃ i, s i) \ Quotient.out u = ⋃ i, s i \ Quotient.out u := by
        ext x; simp only [mem_sdiff, mem_iUnion]; tauto
      exact heq ▸ N.union_countable (fun i => s i \ Quotient.out u) hi
    change Le N (mk N (⋃ i, s i)) u
    rw [hu]
    exact (le_mk N).mpr hunion

theorem iInf_mk {ι : Type*} [Countable ι] (s : ι → Set X) :
    (⨅ i, mk N (s i)) = mk N (⋂ i, s i) := by
  have hcompl : (⨅ i, mk N (s i)) = (⨆ i, (mk N (s i))ᶜ)ᶜ := by
    rw [← compl_compl (x := ⨅ i, mk N (s i))]
    congr 1
    exact compl_iInf (f := fun i => mk N (s i))
  rw [hcompl]
  simp_rw [compl_mk]
  rw [iSup_mk, compl_mk, compl_iUnion]
  simp_rw [compl_compl]

end AssociatedAlgebra

/-- Lemma 41 shape: the constant random variable `K_S` has check-image `Š`. -/
def constRV (S : Set Y) : X → Set Y := fun _ => S

theorem constRV_isL0 (S : Set Y) : IsL0 (X := X) (constRV S) := by
  intro y
  by_cases hy : y ∈ S
  · have : constRV (X := X) S ⁻¹' posBasic y = Set.univ := by
      ext x; simp [constRV, posBasic, hy]
    simpa [this] using MeasurableSet.univ
  · have : constRV (X := X) S ⁻¹' posBasic y = ∅ := by
      ext x; simp [constRV, posBasic, hy]
    simpa [this] using MeasurableSet.empty

/-- Equation (4): `G_X([a])(y̌) = [a⁻¹(B_y)]`, as an `A`-subset when `A = Set X`
(before quotienting by null sets). -/
def G_pre (a : X → Set Y) : ASubset (Set X) Y :=
  fun y => a ⁻¹' posBasic y

/-- Lemma 41: the constant random variable `K_S` is sent to the check-set `Š`. -/
theorem lemma_41 (S : Set Y) :
    G_pre (constRV (X := X) S) = checkSet (A := Set X) S := by
  ext y
  by_cases hy : y ∈ S
  · simp [G_pre, constRV, posBasic, checkSet, hy]
  · simp [G_pre, constRV, posBasic, checkSet, hy]

theorem G_pre_const (S : Set Y) :
    G_pre (constRV (X := X) S) = checkSet (A := Set X) S :=
  lemma_41 S

/-!
## `L⁰` modulo a.e. (Lemma 38) and `G_X` (Proposition 39)
-/

/-- Measurable random variables, before a.e. quotient. -/
def L0Fun (X Y : Type*) [MeasurableSpace X] :=
  {a : X → Set Y // IsL0 a}

def l0AE (N : NegligibilitySpace X) (a b : L0Fun X Y) : Prop :=
  N.negligible (l0Eq a.val b.val)ᶜ

theorem l0AE_refl (N : NegligibilitySpace X) (a : L0Fun X Y) : l0AE N a a := by
  simpa [l0AE, l0Eq] using N.empty

theorem l0AE_symm (N : NegligibilitySpace X) {a b : L0Fun X Y} (h : l0AE N a b) :
    l0AE N b a := by
  have : l0Eq a.val b.val = l0Eq b.val a.val := by
    ext x; simp [l0Eq, eq_comm]
  simpa [l0AE, this] using h

theorem l0AE_trans (N : NegligibilitySpace X) {a b c : L0Fun X Y}
    (hab : l0AE N a b) (hbc : l0AE N b c) : l0AE N a c := by
  have hsub : (l0Eq a.val c.val)ᶜ ⊆ (l0Eq a.val b.val)ᶜ ∪ (l0Eq b.val c.val)ᶜ := by
    intro x hx
    have hac : a.val x ≠ c.val x := by simpa [l0Eq] using hx
    simp only [mem_union, mem_compl_iff, l0Eq]
    exact not_and_or.mp fun ⟨hab, hbc⟩ => hac (hab.trans hbc)
  exact N.mono hsub (N.union₂ hab hbc)

def l0Setoid (N : NegligibilitySpace X) (Y : Type*) : Setoid (L0Fun X Y) where
  r := l0AE N
  iseqv := ⟨l0AE_refl N, fun {_ _} => l0AE_symm N, fun {_ _ _} => l0AE_trans N⟩

/-- Paper `L⁰(X; 𝒫(Y))`: measurable maps modulo a.e. equality. -/
abbrev L0 (N : NegligibilitySpace X) (Y : Type*) :=
  Quotient (l0Setoid N Y)

def L0.mk (N : NegligibilitySpace X) (a : L0Fun X Y) : L0 N Y :=
  Quotient.mk (l0Setoid N Y) a

theorem l0Le_subset_of_ae (N : NegligibilitySpace X) (a a' b b' : X → Set Y) :
    symmDiff (l0Le a b) (l0Le a' b') ⊆ (l0Eq a a')ᶜ ∪ (l0Eq b b')ᶜ := by
  intro x hx
  by_contra hne
  have heq : a x = a' x ∧ b x = b' x := by
    simp only [mem_union, mem_compl_iff, l0Eq] at hne
    exact ⟨not_not.mp (not_or.mp hne).1, not_not.mp (not_or.mp hne).2⟩
  rcases (mem_symmDiff.mp hx) with h | h
  · have : a' x ⊆ b' x := by rw [← heq.1, ← heq.2]; exact h.1
    exact h.2 this
  · have : a x ⊆ b x := by rw [heq.1, heq.2]; exact h.1
    exact h.2 this

theorem l0Le_aeEq (N : NegligibilitySpace X) {a a' b b' : L0Fun X Y}
    (ha : l0AE N a a') (hb : l0AE N b b') :
    aeEq N (l0Le a.val b.val) (l0Le a'.val b'.val) :=
  N.mono (l0Le_subset_of_ae N a.val a'.val b.val b'.val) (N.union₂ ha hb)

noncomputable def L0.le (N : NegligibilitySpace X) (a b : L0 N Y) :
    AssociatedAlgebra N :=
  Quotient.lift₂ (fun a b => AssociatedAlgebra.mk N (l0Le a.val b.val))
    (fun a b a' b' ha hb =>
      (AssociatedAlgebra.mk_eq_iff N).mpr (l0Le_aeEq N ha hb)) a b

theorem L0.le_mk (N : NegligibilitySpace X) (a b : L0Fun X Y) :
    L0.le N (L0.mk N a) (L0.mk N b) = AssociatedAlgebra.mk N (l0Le a.val b.val) :=
  rfl

theorem L0.le_trans (N : NegligibilitySpace X) (a b c : L0 N Y) :
    L0.le N a b ⊓ L0.le N b c ≤ L0.le N a c := by
  refine Quotient.inductionOn₃ a b c fun a b c => ?_
  simp only [L0.le, L0.mk, Quotient.lift₂_mk]
  rw [AssociatedAlgebra.inf_mk]
  change AssociatedAlgebra.Le N
    (AssociatedAlgebra.mk N (l0Le a.val b.val ∩ l0Le b.val c.val))
    (AssociatedAlgebra.mk N (l0Le a.val c.val))
  refine (AssociatedAlgebra.le_mk N).mpr ?_
  have : (l0Le a.val b.val ∩ l0Le b.val c.val) \ l0Le a.val c.val = ∅ := by
    ext x
    simp only [mem_empty_iff_false, mem_sdiff, mem_inter_iff, l0Le]
    exact iff_false_intro fun ⟨⟨hab, hbc⟩, hn⟩ => hn (Set.Subset.trans hab hbc)
  simpa [this] using N.empty

theorem L0.le_le_refl (N : NegligibilitySpace X) (a b : L0 N Y) :
    L0.le N a b ≤ L0.le N a a ⊓ L0.le N b b := by
  refine Quotient.inductionOn₂ a b fun a b => ?_
  simp only [L0.le, L0.mk, Quotient.lift₂_mk]
  rw [AssociatedAlgebra.inf_mk, l0Le_refl, l0Le_refl, inter_self]
  change AssociatedAlgebra.Le N
    (AssociatedAlgebra.mk N (l0Le a.val b.val))
    (AssociatedAlgebra.mk N Set.univ)
  refine (AssociatedAlgebra.le_mk N).mpr ?_
  have : l0Le a.val b.val \ Set.univ = ∅ :=
    (sdiff_eq_empty.2 (subset_univ _))
  simpa [this] using N.empty

/-- Lemma 38: `L⁰` is an `A(X)`-poset. -/
noncomputable def l0Poset (N : NegligibilitySpace X) :
    APoset (A := AssociatedAlgebra N) (L0 N Y) where
  le := L0.le N
  trans := L0.le_trans N
  le_le_refl := L0.le_le_refl N

theorem lemma_38 (N : NegligibilitySpace X) :
    (l0Poset (Y := Y) N).le = L0.le N ∧
      (∀ a b c, (l0Poset (Y := Y) N).le a b ⊓ (l0Poset (Y := Y) N).le b c ≤
        (l0Poset (Y := Y) N).le a c) ∧
      (∀ a b, (l0Poset (Y := Y) N).le a b ≤
        (l0Poset (Y := Y) N).le a a ⊓ (l0Poset (Y := Y) N).le b b) :=
  ⟨rfl, L0.le_trans N, L0.le_le_refl N⟩

theorem G_pre_aeEq (N : NegligibilitySpace X) {a b : L0Fun X Y} (h : l0AE N a b)
    (y : Y) : aeEq N (G_pre a.val y) (G_pre b.val y) := by
  have hsub : symmDiff (G_pre a.val y) (G_pre b.val y) ⊆ (l0Eq a.val b.val)ᶜ := by
    intro x hx
    simp only [mem_compl_iff, l0Eq]
    intro heq
    simp only [G_pre, posBasic, mem_symmDiff, mem_preimage, mem_setOf] at hx
    rw [heq] at hx
    exact hx.elim (fun h => h.2 h.1) (fun h => h.2 h.1)
  exact N.mono hsub h

/-- Equation (4) on the a.e. quotient: `G_X([a])(y̌) = [a⁻¹(B_y)]`. -/
noncomputable def G_X (N : NegligibilitySpace X) (a : L0 N Y) :
    ASubset (AssociatedAlgebra N) Y :=
  Quotient.lift (fun a y => AssociatedAlgebra.mk N (G_pre a.val y))
    (fun a b h => funext fun y =>
      (AssociatedAlgebra.mk_eq_iff N).mpr (G_pre_aeEq N h y)) a

theorem G_X_mk (N : NegligibilitySpace X) (a : L0Fun X Y) (y : Y) :
    G_X N (L0.mk N a) y = AssociatedAlgebra.mk N (G_pre a.val y) :=
  rfl

theorem G_X_le (N : NegligibilitySpace X) [Countable Y] (a b : L0 N Y) :
    subsetB (G_X N a) (G_X N b) = L0.le N a b := by
  refine Quotient.inductionOn₂ a b fun a b => ?_
  unfold subsetB
  simp only [G_X, L0.le, L0.mk, Quotient.lift_mk, Quotient.lift₂_mk]
  have : (⨅ y, AssociatedAlgebra.mk N (G_pre a.val y) ⇨
        AssociatedAlgebra.mk N (G_pre b.val y)) =
      AssociatedAlgebra.mk N (⋂ y, (G_pre a.val y)ᶜ ∪ G_pre b.val y) := by
    rw [← AssociatedAlgebra.iInf_mk]
    congr 1
    ext y
    exact AssociatedAlgebra.himp_mk N _ _
  refine this.trans (congrArg (AssociatedAlgebra.mk N) ?_)
  ext x
  constructor
  · intro hx y hy
    have hyx := mem_iInter.mp hx y
    simp only [mem_union, mem_compl_iff, G_pre, posBasic, mem_preimage, mem_setOf] at hyx
    exact hyx.resolve_left (not_not.mpr hy)
  · intro hx
    refine mem_iInter.mpr fun y => ?_
    simp only [mem_union, mem_compl_iff, G_pre, posBasic, mem_preimage, mem_setOf, l0Le] at hx ⊢
    exact or_iff_not_imp_left.mpr fun hy => hx (not_not.mp hy)

/-- Inverse of `G_X`: `a(x) = {y | x ∈ measurable representative of b(y)}`. -/
noncomputable def G_X_inv (N : NegligibilitySpace X) (b : ASubset (AssociatedAlgebra N) Y) :
    L0Fun X Y :=
  ⟨fun x => {y | x ∈ N.measRep (Quotient.out (b y))}, fun y => by
    have : (fun x : X => {y : Y | x ∈ N.measRep (Quotient.out (b y))}) ⁻¹' posBasic y =
        N.measRep (Quotient.out (b y)) := by
      ext x; simp [posBasic]
    simpa [this] using N.measRep_measurable _⟩

theorem G_X_inv_right (N : NegligibilitySpace X) (b : ASubset (AssociatedAlgebra N) Y) :
    G_X N (L0.mk N (G_X_inv N b)) = b := by
  funext y
  rw [G_X_mk]
  simp only [G_X_inv, G_pre, posBasic]
  have : (fun x : X => {y : Y | x ∈ N.measRep (Quotient.out (b y))}) ⁻¹' {S | y ∈ S} =
      N.measRep (Quotient.out (b y)) := by
    ext x; simp
  rw [this, AssociatedAlgebra.mk_measRep, AssociatedAlgebra.mk_out]

theorem G_X_inv_left (N : NegligibilitySpace X) [Countable Y] (a : L0 N Y) :
    L0.mk N (G_X_inv N (G_X N a)) = a := by
  refine Quotient.inductionOn a fun a => Quotient.sound ?_
  change l0AE N (G_X_inv N (G_X N (L0.mk N a))) a
  unfold l0AE
  let a' := (G_X_inv N (G_X N (L0.mk N a))).val
  have hy : ∀ y, N.negligible (symmDiff
      (N.measRep (Quotient.out (AssociatedAlgebra.mk N (G_pre a.val y))))
      (G_pre a.val y)) := fun y =>
    aeEq_trans N (aeEq_symm N (N.measRep_symmDiff _))
      (AssociatedAlgebra.aeEq_out N)
  have hsub : (l0Eq a' a.val)ᶜ ⊆
      ⋃ y, symmDiff
        (N.measRep (Quotient.out (AssociatedAlgebra.mk N (G_pre a.val y))))
        (G_pre a.val y) := by
    intro x hx
    have hne : a' x ≠ a.val x := by
      simpa [l0Eq] using hx
    obtain ⟨y, hyx⟩ : ∃ y, ¬ (y ∈ a' x ↔ y ∈ a.val x) :=
      not_forall.mp (mt Set.ext hne)
    refine mem_iUnion.mpr ⟨y, ?_⟩
    have hab : y ∈ a' x ↔
        x ∈ N.measRep (Quotient.out (AssociatedAlgebra.mk N (G_pre a.val y))) := by
      simp [a', G_X_inv, G_X_mk]
    have hyx' : ¬ (x ∈ N.measRep (Quotient.out (AssociatedAlgebra.mk N (G_pre a.val y))) ↔
        y ∈ a.val x) := by
      rwa [← hab]
    rw [mem_symmDiff, G_pre, posBasic]
    by_cases hP : x ∈ N.measRep (Quotient.out (AssociatedAlgebra.mk N (G_pre a.val y)))
    · exact Or.inl ⟨hP, fun hQ => hyx' (iff_of_true hP hQ)⟩
    · refine Or.inr ⟨?_, hP⟩
      by_contra hQ
      exact hyx' (iff_of_false hP hQ)
  exact N.mono hsub (N.union_countable _ hy)

/-- Proposition 39: `G_X` is a strict isomorphism of `A(X)`-posets. -/
noncomputable def proposition_39 (N : NegligibilitySpace X) [Countable Y] :
    APoset.StrictIso (l0Poset (Y := Y) N) (powerPoset (A := AssociatedAlgebra N) (X := Y)) where
  toFun := G_X N
  invFun := fun b => L0.mk N (G_X_inv N b)
  left_inv := G_X_inv_left N
  right_inv := G_X_inv_right N
  preserve_le := fun a b => by
    change subsetB (G_X N a) (G_X N b) = L0.le N a b
    exact G_X_le N a b

/-!
## Proposition 40: pointwise Engeler application is an application homomorphism
-/

/-- Boolean-valued Engeler application on `A`-subsets of a ground type
(the formula in the proof of Proposition 40). -/
noncomputable def engelerAppA {A E : Type*} [CompleteBooleanAlgebra A] [DecidableEq E]
    (pair : Finset E × E → E) (F X : ASubset A E) : ASubset A E :=
  fun q => ⨆ K : Finset E, F (pair (K, q)) ⊓ ⨅ k ∈ K, X k

/-- Pointwise Engeler application on random variables. -/
def l0App [DecidableEq E] (pair : Finset E × E → E)
    (a b : X → Set E) : X → Set E :=
  fun x => engelerApp pair (a x) (b x)

theorem l0App_preimage [DecidableEq E] (pair : Finset E × E → E)
    (a b : X → Set E) (q : E) :
    l0App pair a b ⁻¹' posBasic q =
      ⋃ K : Finset E,
        (a ⁻¹' posBasic (pair (K, q))) ∩ ⋂ k ∈ K, b ⁻¹' posBasic k := by
  ext x
  simp only [l0App, posBasic, mem_preimage, mem_setOf, mem_iUnion, mem_inter_iff,
    mem_iInter, engelerApp]
  constructor
  · intro ⟨K, hK, hp⟩
    exact ⟨K, hp, fun k hk => hK hk⟩
  · intro ⟨K, hp, hK⟩
    exact ⟨K, fun k hk => hK k hk, hp⟩

theorem l0App_isL0 [DecidableEq E] [Countable E] (pair : Finset E × E → E)
    {a b : X → Set E} (ha : IsL0 a) (hb : IsL0 b) : IsL0 (l0App pair a b) := by
  intro q
  rw [l0App_preimage]
  refine MeasurableSet.iUnion fun K => (ha (pair (K, q))).inter ?_
  exact Finset.measurableSet_biInter K fun k _ => hb k

theorem l0App_ae [DecidableEq E] [Countable E] (N : NegligibilitySpace X)
    (pair : Finset E × E → E) {a a' b b' : L0Fun X E}
    (ha : l0AE N a a') (hb : l0AE N b b') :
    l0AE N ⟨l0App pair a.val b.val, l0App_isL0 pair a.property b.property⟩
      ⟨l0App pair a'.val b'.val, l0App_isL0 pair a'.property b'.property⟩ := by
  have hsub : (l0Eq (l0App pair a.val b.val) (l0App pair a'.val b'.val))ᶜ ⊆
      (l0Eq a.val a'.val)ᶜ ∪ (l0Eq b.val b'.val)ᶜ := by
    intro x hx
    simp only [mem_union, mem_compl_iff, l0Eq, l0App] at hx ⊢
    exact not_and_or.mp fun ⟨haeq, hbeq⟩ => hx (by
      change a.val x = a'.val x at haeq
      change b.val x = b'.val x at hbeq
      change l0App pair a.val b.val x = l0App pair a'.val b'.val x
      simp only [l0App]
      rw [haeq, hbeq])
  exact N.mono hsub (N.union₂ ha hb)

/-- Quotiented pointwise application `[a] · [b] = [a · b]`. -/
noncomputable def L0.app [DecidableEq E] [Countable E] (N : NegligibilitySpace X)
    (pair : Finset E × E → E) (a b : L0 N E) : L0 N E :=
  Quotient.lift₂
    (fun a b => L0.mk N ⟨l0App pair a.val b.val, l0App_isL0 pair a.property b.property⟩)
    (fun a b a' b' ha hb => by
      refine Quotient.sound ?_
      exact l0App_ae N pair ha hb) a b

theorem L0.app_mk [DecidableEq E] [Countable E] (N : NegligibilitySpace X)
    (pair : Finset E × E → E) (a b : L0Fun X E) :
    L0.app N pair (L0.mk N a) (L0.mk N b) =
      L0.mk N ⟨l0App pair a.val b.val, l0App_isL0 pair a.property b.property⟩ :=
  rfl

namespace AssociatedAlgebra

variable {X : Type*} [MeasurableSpace X] (N : NegligibilitySpace X)

theorem iInf_mk_finset {ι : Type*} [DecidableEq ι] (K : Finset ι) (s : ι → Set X) :
    (⨅ k ∈ K, mk N (s k)) = mk N (⋂ k ∈ K, s k) := by
  induction K using Finset.induction with
  | empty =>
    have h1 : (⨅ k ∈ (∅ : Finset ι), mk N (s k)) = ⊤ := by simp
    have h2 : (⋂ k ∈ (∅ : Finset ι), s k) = Set.univ := by simp
    rw [h1, h2, mk_top]
  | insert a K ha ih =>
    rw [Finset.iInf_insert, Finset.set_biInter_insert, ih, inf_mk]

end AssociatedAlgebra

theorem G_pre_l0App [DecidableEq E] (pair : Finset E × E → E)
    (a b : X → Set E) (q : E) :
    G_pre (l0App pair a b) q =
      ⋃ K : Finset E, G_pre a (pair (K, q)) ∩ ⋂ k ∈ K, G_pre b k :=
  l0App_preimage pair a b q

/-- Proposition 40: `G_X` is an application homomorphism. -/
theorem proposition_40 [DecidableEq E] [Countable E] (N : NegligibilitySpace X)
    (pair : Finset E × E → E) (a b : L0 N E) :
    G_X N (L0.app N pair a b) = engelerAppA pair (G_X N a) (G_X N b) := by
  refine Quotient.inductionOn₂ a b fun a b => ?_
  funext q
  have happ :
      L0.app N pair (Quotient.mk (l0Setoid N E) a) (Quotient.mk (l0Setoid N E) b) =
        L0.mk N ⟨l0App pair a.val b.val, l0App_isL0 pair a.property b.property⟩ :=
    rfl
  rw [happ]
  have hG : G_X N (L0.mk N ⟨l0App pair a.val b.val, l0App_isL0 pair a.property b.property⟩) q =
      AssociatedAlgebra.mk N (G_pre (l0App pair a.val b.val) q) :=
    rfl
  rw [hG, G_pre_l0App]
  haveI : Countable (Finset E) := inferInstance
  have hunion :
      AssociatedAlgebra.mk N
          (⋃ K : Finset E, G_pre a.val (pair (K, q)) ∩ ⋂ k ∈ K, G_pre b.val k) =
        ⨆ K : Finset E,
          AssociatedAlgebra.mk N
            (G_pre a.val (pair (K, q)) ∩ ⋂ k ∈ K, G_pre b.val k) :=
    (AssociatedAlgebra.iSup_mk N
      (fun K : Finset E => G_pre a.val (pair (K, q)) ∩ ⋂ k ∈ K, G_pre b.val k)).symm
  rw [hunion]
  refine iSup_congr fun K => ?_
  have haG : G_X N (Quotient.mk (l0Setoid N E) a) (pair (K, q)) =
      AssociatedAlgebra.mk N (G_pre a.val (pair (K, q))) := rfl
  have hbG : ∀ k, G_X N (Quotient.mk (l0Setoid N E) b) k =
      AssociatedAlgebra.mk N (G_pre b.val k) := fun _ => rfl
  simp_rw [haG, hbG]
  rw [AssociatedAlgebra.iInf_mk_finset, ← AssociatedAlgebra.inf_mk]

/-- Proposition 44 records that `L⁰` is typically *not* a continuous dcpo
externally; the paper proves this when the associated algebra is non-atomic. -/
def IsAtomic (A : Type*) [CompleteBooleanAlgebra A] : Prop :=
  ∀ a : A, a ≠ ⊥ → ∃ b : A, IsAtom b ∧ b ≤ a

/-!
## Complete lattice structure on `L⁰` along `G_X`, and Proposition 44
-/

/-- `G_X` as a type equivalence (Proposition 39). -/
noncomputable def L0.equivPower (N : NegligibilitySpace X) [Countable Y] :
    L0 N Y ≃ ASubset (AssociatedAlgebra N) Y where
  toFun := G_X N
  invFun := fun b => L0.mk N (G_X_inv N b)
  left_inv := G_X_inv_left N
  right_inv := G_X_inv_right N

theorem G_X_equiv (N : NegligibilitySpace X) [Countable Y] (a : L0 N Y) :
    G_X N a = L0.equivPower (Y := Y) N a :=
  rfl

theorem G_X_symm (N : NegligibilitySpace X) [Countable Y]
    (b : ASubset (AssociatedAlgebra N) Y) :
    G_X N ((L0.equivPower (Y := Y) N).symm b) = b := by
  rw [G_X_equiv]
  exact Equiv.apply_symm_apply _ _

/-- Order on `L⁰` transported along `G_X`. -/
noncomputable instance instPartialOrderL0
    {X Y : Type*} [MeasurableSpace X] (N : NegligibilitySpace X) [Countable Y] :
    PartialOrder (L0 N Y) where
  le a b := G_X N a ≤ G_X N b
  le_refl _ := le_rfl
  le_trans _ _ _ := le_trans
  le_antisymm a b hab hba :=
    (L0.equivPower (Y := Y) N).injective (le_antisymm hab hba)

noncomputable instance instSupSetL0
    {X Y : Type*} [MeasurableSpace X] (N : NegligibilitySpace X) [Countable Y] :
    SupSet (L0 N Y) where
  sSup S := (L0.equivPower (Y := Y) N).symm (sSup (G_X N '' S))

/-- External complete lattice on `L⁰`, transported along `G_X`. -/
noncomputable instance instCompleteLatticeL0
    {X Y : Type*} [MeasurableSpace X] (N : NegligibilitySpace X) [Countable Y] :
    CompleteLattice (L0 N Y) :=
  completeLatticeOfSup (L0 N Y) fun S => by
    constructor
    · intro a ha
      change G_X N a ≤ G_X N ((L0.equivPower (Y := Y) N).symm (sSup (G_X N '' S)))
      rw [G_X_symm]
      exact le_sSup (mem_image_of_mem (G_X N) ha)
    · intro b hb
      change G_X N ((L0.equivPower (Y := Y) N).symm (sSup (G_X N '' S))) ≤ G_X N b
      rw [G_X_symm]
      exact sSup_le fun x hx => by
        obtain ⟨a, ha, rfl⟩ := (mem_image _ _ _).1 hx
        exact hb ha

theorem L0.le_iff_G_X (N : NegligibilitySpace X) [Countable Y] (a b : L0 N Y) :
    a ≤ b ↔ G_X N a ≤ G_X N b :=
  Iff.rfl

theorem L0.le_iff_pointwise (N : NegligibilitySpace X) [Countable Y] (a b : L0 N Y) :
    a ≤ b ↔ ∀ y, G_X N a y ≤ G_X N b y :=
  Iff.rfl

theorem G_X_sSup {X Y : Type*} [MeasurableSpace X] [Countable Y]
    (N : NegligibilitySpace X) (S : Set (L0 N Y)) :
    G_X N (sSup S) = sSup (G_X N '' S) := by
  change G_X N ((L0.equivPower (Y := Y) N).symm (sSup (G_X N '' S))) =
    sSup (G_X N '' S)
  exact G_X_symm N _

theorem G_X_bot {X Y : Type*} [MeasurableSpace X] [Countable Y]
    (N : NegligibilitySpace X) :
    G_X N (⊥ : L0 N Y) = (⊥ : ASubset (AssociatedAlgebra N) Y) := by
  change G_X N (sSup (∅ : Set (L0 N Y))) = ⊥
  rw [G_X_sSup, image_empty, sSup_empty]

theorem L0.eq_bot_iff_G_X {X Y : Type*} [MeasurableSpace X] [Countable Y]
    (N : NegligibilitySpace X) (a : L0 N Y) :
    a = ⊥ ↔ G_X N a = (⊥ : ASubset (AssociatedAlgebra N) Y) := by
  constructor
  · intro h; rw [h]; exact G_X_bot N
  · intro h
    apply (L0.equivPower (Y := Y) N).injective
    rw [← G_X_equiv, ← G_X_equiv, h, G_X_bot]

theorem wayBelow_bot {D : Type*} [CompleteLattice D] (d : D) : (⊥ : D) ≪ d := by
  intro S hne _hdir _hle
  obtain ⟨s, hs⟩ := hne
  exact ⟨s, hs, bot_le⟩

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
      push_neg at hempty
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
    push_neg at h
    exact hnot ⟨hne, fun c hc => h c hc⟩
  exact ⟨c, hcne, hclt, fun b hb hle => hna b hb (hle.trans hclt.le)⟩

noncomputable def atomlessSeqAux {A : Type*} [CompleteBooleanAlgebra A] {a : A}
    (hne : a ≠ ⊥) (hna : ∀ b, IsAtom b → ¬b ≤ a) :
    ℕ → Σ' x : A, x ≠ ⊥ ∧ (∀ b, IsAtom b → ¬b ≤ x)
  | 0 =>
    let h := Classical.choose_spec (exists_lt_atomless hne hna)
    ⟨Classical.choose (exists_lt_atomless hne hna), h.1, h.2.2⟩
  | n + 1 =>
    let prev := atomlessSeqAux hne hna n
    let hex := exists_lt_atomless prev.2.1 prev.2.2
    let h := Classical.choose_spec hex
    ⟨Classical.choose hex, h.1, h.2.2⟩

noncomputable def atomlessSeq {A : Type*} [CompleteBooleanAlgebra A] {a : A}
    (hne : a ≠ ⊥) (hna : ∀ b, IsAtom b → ¬b ≤ a) : ℕ → A :=
  fun n => (atomlessSeqAux hne hna n).1

theorem atomlessSeq_ne {A : Type*} [CompleteBooleanAlgebra A] {a : A}
    (hne : a ≠ ⊥) (hna : ∀ b, IsAtom b → ¬b ≤ a) (n : ℕ) :
    atomlessSeq hne hna n ≠ ⊥ :=
  (atomlessSeqAux hne hna n).2.1

theorem atomlessSeq_atomless {A : Type*} [CompleteBooleanAlgebra A] {a : A}
    (hne : a ≠ ⊥) (hna : ∀ b, IsAtom b → ¬b ≤ a) (n : ℕ) :
    ∀ b, IsAtom b → ¬b ≤ atomlessSeq hne hna n :=
  (atomlessSeqAux hne hna n).2.2

theorem atomlessSeq_succ_lt {A : Type*} [CompleteBooleanAlgebra A] {a : A}
    (hne : a ≠ ⊥) (hna : ∀ b, IsAtom b → ¬b ≤ a) (n : ℕ) :
    atomlessSeq hne hna (n + 1) < atomlessSeq hne hna n := by
  change (atomlessSeqAux hne hna (n + 1)).1 < (atomlessSeqAux hne hna n).1
  let prev := atomlessSeqAux hne hna n
  exact (Classical.choose_spec (exists_lt_atomless prev.2.1 prev.2.2)).2.1

theorem atomlessSeq_antitone {A : Type*} [CompleteBooleanAlgebra A] {a : A}
    (hne : a ≠ ⊥) (hna : ∀ b, IsAtom b → ¬b ≤ a) :
    Antitone (atomlessSeq hne hna) :=
  antitone_nat_of_succ_le fun n => (atomlessSeq_succ_lt hne hna n).le

noncomputable def meetlessSeq {A : Type*} [CompleteBooleanAlgebra A] (f : ℕ → A) : ℕ → A :=
  fun n => f n ⊓ (⨅ k, f k)ᶜ

theorem meetlessSeq_iInf_bot {A : Type*} [CompleteBooleanAlgebra A] (f : ℕ → A) :
    ⨅ n, meetlessSeq f n = ⊥ := by
  refine le_bot_iff.mp ?_
  have hle : ⨅ n, meetlessSeq f n ≤ (⨅ n, f n) ⊓ (⨅ k, f k)ᶜ :=
    le_inf (iInf_mono fun n => inf_le_left) (iInf_le_of_le 0 inf_le_right)
  exact hle.trans_eq inf_compl_eq_bot

theorem meetlessSeq_succ_lt {A : Type*} [CompleteBooleanAlgebra A] {f : ℕ → A}
    (hstrict : ∀ n, f (n + 1) < f n) (n : ℕ) :
    meetlessSeq f (n + 1) < meetlessSeq f n := by
  set m := ⨅ k, f k
  refine lt_of_le_of_ne (inf_le_inf_right mᶜ (hstrict n).le) ?_
  intro heq
  have hcalc : (f n ⊓ mᶜ) ⊓ (f (n + 1) ⊓ mᶜ)ᶜ = f n ⊓ (f (n + 1))ᶜ ⊓ mᶜ := by
    rw [compl_inf, compl_compl, inf_sup_left]
    have hz : f n ⊓ mᶜ ⊓ m = ⊥ := by
      rw [inf_assoc, inf_comm (a := mᶜ), inf_compl_eq_bot, inf_bot_eq]
    rw [hz, sup_bot_eq]
    ac_rfl
  have hbot : f n ⊓ (f (n + 1))ᶜ ⊓ mᶜ = ⊥ := by
    have : (f n ⊓ mᶜ) ⊓ (f (n + 1) ⊓ mᶜ)ᶜ = ⊥ := by
      change meetlessSeq f n ⊓ (meetlessSeq f (n + 1))ᶜ = ⊥
      rw [heq, inf_compl_eq_bot]
    rwa [← hcalc]
  have hle : f n ⊓ (f (n + 1))ᶜ ≤ m :=
    (disjoint_compl_right_iff (x := f n ⊓ (f (n + 1))ᶜ) (y := m)).mp
      (disjoint_iff.mpr hbot)
  have hz : f n ⊓ (f (n + 1))ᶜ = ⊥ :=
    le_bot_iff.mp ((le_inf (hle.trans (iInf_le f (n + 1))) inf_le_right).trans_eq
      inf_compl_eq_bot)
  exact (hstrict n).not_ge
    ((disjoint_compl_right_iff (x := f n) (y := f (n + 1))).mp (disjoint_iff.mpr hz))

theorem meetlessSeq_ne {A : Type*} [CompleteBooleanAlgebra A] {f : ℕ → A}
    (hstrict : ∀ n, f (n + 1) < f n) (n : ℕ) : meetlessSeq f n ≠ ⊥ := by
  intro hbot
  have : f n ≤ ⨅ k, f k :=
    (disjoint_compl_right_iff (x := f n) (y := ⨅ k, f k)).mp
      (disjoint_iff.mpr (by simpa [meetlessSeq] using hbot))
  exact (hstrict n).not_ge (this.trans (iInf_le f (n + 1)))

theorem atomlessSeq_lt {A : Type*} [CompleteBooleanAlgebra A] {a : A}
    (hne : a ≠ ⊥) (hna : ∀ b, IsAtom b → ¬b ≤ a) (n : ℕ) :
    atomlessSeq hne hna n < a := by
  induction n with
  | zero => exact (Classical.choose_spec (exists_lt_atomless hne hna)).2.1
  | succ n ih => exact (atomlessSeq_succ_lt hne hna n).trans ih

theorem directedOn_range_monotone {α : Type*} [Preorder α] {f : ℕ → α}
    (hf : Monotone f) : DirectedOn (· ≤ ·) (Set.range f) := by
  intro x hx y hy
  obtain ⟨i, rfl⟩ := hx
  obtain ⟨j, rfl⟩ := hy
  exact ⟨f (max i j), ⟨max i j, rfl⟩, hf (le_max_left i j), hf (le_max_right i j)⟩


/-- If `A` is not atomic and `Y` is nonempty, then `Y → A` is not a
continuous lattice. Constant functions are the paper's indicator RVs
after transport along `G_X`. -/
theorem not_isContinuousLattice_fun_of_not_atomic
    {A Y : Type*} [CompleteBooleanAlgebra A] [Nonempty Y]
    (hA : ¬IsAtomic A) : ¬IsContinuousLattice (Y → A) := by
  obtain ⟨u, hu, hna⟩ := exists_pos_atomless_of_not_isAtomic hA
  let b : Y → A := fun _ => u
  have hb_ne : b ≠ ⊥ := by
    intro h
    exact hu (by simpa [Pi.bot_apply] using congrFun h (Classical.arbitrary Y))
  have honly : ∀ e : Y → A, e ≪ b → e = ⊥ := by
    intro e he
    by_contra hene
    have hele : e ≤ b := wayBelow_le he
    have ht_ne : ⨆ y, e y ≠ ⊥ := by
      intro hbot
      exact hene (funext fun y =>
        le_bot_iff.mp ((le_iSup e y).trans_eq hbot))
    have ht_le : ⨆ y, e y ≤ u := iSup_le fun y => hele y
    let t := ⨆ y, e y
    have ht_na : ∀ c, IsAtom c → ¬c ≤ t :=
      fun c hc hcle => hna c hc (hcle.trans ht_le)
    let f := atomlessSeq ht_ne ht_na
    have hf_lt : ∀ n, f (n + 1) < f n := atomlessSeq_succ_lt ht_ne ht_na
    let w := meetlessSeq f
    have hw_lt : ∀ n, w (n + 1) < w n := meetlessSeq_succ_lt hf_lt
    have hw_ne : ∀ n, w n ≠ ⊥ := meetlessSeq_ne hf_lt
    have hw_le : ∀ n, w n ≤ t := fun n =>
      inf_le_left.trans (atomlessSeq_lt ht_ne ht_na n).le
    let c : ℕ → (Y → A) := fun n _ => t ⊓ (w n)ᶜ ⊔ u ⊓ tᶜ
    have hc_mono : Monotone c := by
      intro i j hij y
      refine sup_le_sup ?_ le_rfl
      exact inf_le_inf_left t (compl_le_compl
        ((antitone_nat_of_succ_le fun n => (hw_lt n).le) hij))
    have hc_sup : sSup (Set.range c) = b := by
      funext y
      have : sSup (Set.range c) y = ⨆ n, c n y := by
        rw [sSup_range, iSup_apply]
      rw [this]
      have hdist :
          ⨆ n, t ⊓ (w n)ᶜ ⊔ u ⊓ tᶜ = (⨆ n, t ⊓ (w n)ᶜ) ⊔ u ⊓ tᶜ := by
        rw [← iSup_sup]
      rw [hdist, ← inf_iSup_eq, ← compl_iInf, meetlessSeq_iInf_bot, compl_bot,
        inf_top_eq, sup_inf_left, sup_compl_eq_top, inf_top_eq]
      exact sup_eq_right.mpr ht_le
    have hmeet (n : ℕ) : t ⊓ (t ⊓ (w n)ᶜ ⊔ u ⊓ tᶜ)ᶜ = w n := by
      rw [compl_sup, compl_inf, compl_inf, compl_compl, compl_compl]
      have htw : t ⊓ (tᶜ ⊔ w n) = t ⊓ w n := by
        rw [inf_sup_left, inf_compl_eq_bot, bot_sup_eq]
      rw [← inf_assoc, htw, inf_sup_left]
      have htu : t ⊓ uᶜ = ⊥ :=
        disjoint_iff.mp ((disjoint_compl_right_iff (x := t) (y := u)).mpr ht_le)
      have hz : t ⊓ w n ⊓ uᶜ = ⊥ :=
        le_bot_iff.mp ((inf_le_inf_right uᶜ inf_le_left).trans_eq htu)
      have hidem : t ⊓ w n ⊓ t = t ⊓ w n := by
        calc
          t ⊓ w n ⊓ t = t ⊓ t ⊓ w n := by ac_rfl
          _ = t ⊓ w n := by rw [inf_idem]
      rw [hz, bot_sup_eq, hidem, inf_eq_right.mpr (hw_le n)]
    have he_nle : ∀ n, ¬e ≤ c n := by
      intro n hle
      have ht_nle : t ≤ t ⊓ (w n)ᶜ ⊔ u ⊓ tᶜ :=
        iSup_le fun y => hle y
      have hne' : t ⊓ (t ⊓ (w n)ᶜ ⊔ u ⊓ tᶜ)ᶜ ≠ ⊥ := by
        rw [hmeet n]
        exact hw_ne n
      have hbot : t ⊓ (t ⊓ (w n)ᶜ ⊔ u ⊓ tᶜ)ᶜ = ⊥ :=
        disjoint_iff.mp ((disjoint_compl_right_iff
          (x := t) (y := t ⊓ (w n)ᶜ ⊔ u ⊓ tᶜ)).mpr ht_nle)
      exact hne' hbot
    obtain ⟨z, hz, hez⟩ := he (S := Set.range c)
      ⟨c 0, Set.mem_range_self 0⟩ (directedOn_range_monotone hc_mono)
      (le_of_eq hc_sup.symm)
    obtain ⟨n, rfl⟩ := hz
    exact he_nle n hez
  intro hcont
  have hsup := (hcont b).2
  have hset : {e : Y → A | e ≪ b} = {⊥} := by
    ext e
    constructor
    · exact honly e
    · intro he
      rw [mem_singleton_iff.mp he]
      exact wayBelow_bot b
  rw [hset, sSup_singleton] at hsup
  exact hb_ne hsup

theorem L0.le_symm {X Y : Type*} [MeasurableSpace X] [Countable Y]
    (N : NegligibilitySpace X) {x y : ASubset (AssociatedAlgebra N) Y} :
    (L0.equivPower (Y := Y) N).symm x ≤ (L0.equivPower (Y := Y) N).symm y ↔
      x ≤ y := by
  change G_X N ((L0.equivPower (Y := Y) N).symm x) ≤
      G_X N ((L0.equivPower (Y := Y) N).symm y) ↔ x ≤ y
  rw [G_X_symm, G_X_symm]

theorem G_X_image_symm {X Y : Type*} [MeasurableSpace X] [Countable Y]
    (N : NegligibilitySpace X) (S : Set (ASubset (AssociatedAlgebra N) Y)) :
    G_X N '' ((L0.equivPower (Y := Y) N).symm '' S) = S := by
  ext x
  constructor
  · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩
    rwa [G_X_symm]
  · intro hx
    exact ⟨(L0.equivPower (Y := Y) N).symm x, ⟨x, hx, rfl⟩, G_X_symm N x⟩

theorem wayBelow_iff_G_X {X Y : Type*} [MeasurableSpace X] [Countable Y]
    (N : NegligibilitySpace X) (a b : L0 N Y) :
    a ≪ b ↔ G_X N a ≪ G_X N b := by
  constructor
  · intro h S hne hdir hle
    let S' : Set (L0 N Y) := (L0.equivPower (Y := Y) N).symm '' S
    have hne' : S'.Nonempty := hne.image _
    have hdir' : DirectedOn (· ≤ ·) S' := by
      intro x hx y hy
      obtain ⟨sx, hsx, rfl⟩ := hx
      obtain ⟨sy, hsy, rfl⟩ := hy
      obtain ⟨z, hz, hzx, hzy⟩ := hdir sx hsx sy hsy
      exact ⟨(L0.equivPower (Y := Y) N).symm z, ⟨z, hz, rfl⟩,
        (L0.le_symm N).mpr hzx, (L0.le_symm N).mpr hzy⟩
    have hle' : b ≤ sSup S' := by
      change G_X N b ≤ G_X N (sSup S')
      rw [G_X_sSup, G_X_image_symm]
      exact hle
    obtain ⟨w, hw, haw⟩ := h hne' hdir' hle'
    obtain ⟨z, hz, rfl⟩ := hw
    change G_X N a ≤ G_X N ((L0.equivPower (Y := Y) N).symm z) at haw
    rw [G_X_symm] at haw
    exact ⟨z, hz, haw⟩
  · intro h S hne hdir hle
    let S' : Set (ASubset (AssociatedAlgebra N) Y) := G_X N '' S
    have hne' : S'.Nonempty := hne.image _
    have hdir' : DirectedOn (· ≤ ·) S' := by
      intro x hx y hy
      obtain ⟨sx, hsx, rfl⟩ := hx
      obtain ⟨sy, hsy, rfl⟩ := hy
      obtain ⟨z, hz, hzx, hzy⟩ := hdir sx hsx sy hsy
      exact ⟨G_X N z, ⟨z, hz, rfl⟩, hzx, hzy⟩
    have hle' : G_X N b ≤ sSup S' := by
      rwa [← G_X_sSup]
    obtain ⟨w, hw, haw⟩ := h hne' hdir' hle'
    obtain ⟨z, hz, rfl⟩ := hw
    exact ⟨z, hz, haw⟩

theorem isContinuousLattice_iff_G_X {X Y : Type*} [MeasurableSpace X] [Countable Y]
    (N : NegligibilitySpace X) :
    IsContinuousLattice (L0 N Y) ↔
      IsContinuousLattice (ASubset (AssociatedAlgebra N) Y) := by
  constructor
  · intro h d
    let d' := (L0.equivPower (Y := Y) N).symm d
    obtain ⟨hdir, hsup⟩ := h d'
    have himg : G_X N '' {e | e ≪ d'} = {f | f ≪ d} := by
      ext f
      constructor
      · intro hf
        obtain ⟨e, he, rfl⟩ := (mem_image _ _ _).1 hf
        have : G_X N e ≪ G_X N d' := (wayBelow_iff_G_X N e d').mp he
        rwa [G_X_symm] at this
      · intro hf
        refine ⟨(L0.equivPower (Y := Y) N).symm f, ?_, G_X_symm N f⟩
        refine (wayBelow_iff_G_X N _ d').mpr ?_
        rwa [G_X_symm, G_X_symm]
    constructor
    · intro x hx y hy
      have hx' : x ∈ G_X N '' {e | e ≪ d'} := by rwa [himg]
      have hy' : y ∈ G_X N '' {e | e ≪ d'} := by rwa [himg]
      obtain ⟨ex, hex, rfl⟩ := (mem_image _ _ _).1 hx'
      obtain ⟨ey, hey, rfl⟩ := (mem_image _ _ _).1 hy'
      obtain ⟨z, hz, hzx, hzy⟩ := hdir ex hex ey hey
      refine ⟨G_X N z, ?_, hzx, hzy⟩
      exact himg ▸ ⟨z, hz, rfl⟩
    · calc
        d = G_X N d' := (G_X_symm N d).symm
        _ = G_X N (sSup {e | e ≪ d'}) := congrArg (G_X N) hsup
        _ = sSup (G_X N '' {e | e ≪ d'}) := G_X_sSup N _
        _ = sSup {f | f ≪ d} := by rw [himg]
  · intro h d
    obtain ⟨hdir, hsup⟩ := h (G_X N d)
    have himg : (L0.equivPower (Y := Y) N).symm '' {f | f ≪ G_X N d} =
        {e | e ≪ d} := by
      ext e
      constructor
      · intro he
        obtain ⟨f, hf, rfl⟩ := (mem_image _ _ _).1 he
        exact (wayBelow_iff_G_X N _ d).mpr (by rwa [G_X_symm])
      · intro he
        refine ⟨G_X N e, (wayBelow_iff_G_X N e d).mp he, Equiv.symm_apply_apply _ _⟩
    constructor
    · intro x hx y hy
      have hx' : x ∈ (L0.equivPower (Y := Y) N).symm '' {f | f ≪ G_X N d} := by
        rwa [himg]
      have hy' : y ∈ (L0.equivPower (Y := Y) N).symm '' {f | f ≪ G_X N d} := by
        rwa [himg]
      obtain ⟨fx, hfx, rfl⟩ := (mem_image _ _ _).1 hx'
      obtain ⟨fy, hfy, rfl⟩ := (mem_image _ _ _).1 hy'
      obtain ⟨z, hz, hzx, hzy⟩ := hdir fx hfx fy hfy
      refine ⟨(L0.equivPower (Y := Y) N).symm z, ?_,
        (L0.le_symm N).mpr hzx, (L0.le_symm N).mpr hzy⟩
      exact himg ▸ ⟨z, hz, rfl⟩
    · apply (L0.equivPower (Y := Y) N).injective
      rw [← G_X_equiv, ← G_X_equiv]
      calc
        G_X N d = sSup {f | f ≪ G_X N d} := hsup
        _ = sSup (G_X N '' ((L0.equivPower (Y := Y) N).symm ''
              {f | f ≪ G_X N d})) :=
          congrArg sSup (G_X_image_symm N {f | f ≪ G_X N d}).symm
        _ = sSup (G_X N '' {e | e ≪ d}) := by rw [himg]
        _ = G_X N (sSup {e | e ≪ d}) := (G_X_sSup N _).symm

/-- Proposition 44: if `A(X)` is not atomic and `Y` is nonempty countable,
then `L⁰(X; 𝒫(Y))` is not a continuous dcpo. -/
theorem proposition_44 {X Y : Type*} [MeasurableSpace X] [Countable Y] [Nonempty Y]
    (N : NegligibilitySpace X) (hA : ¬IsAtomic (AssociatedAlgebra N)) :
    ¬IsContinuousLattice (L0 N Y) :=
  fun h => not_isContinuousLattice_fun_of_not_atomic (Y := Y) hA
    ((isContinuousLattice_iff_G_X (Y := Y) N).mp h)

end Scott2026
