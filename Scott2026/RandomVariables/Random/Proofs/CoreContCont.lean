/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/

import Mathlib.MeasureTheory.MeasurableSpace.Basic
import Mathlib.MeasureTheory.Measure.Basic
import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
import Mathlib.Order.Atoms
import Mathlib.Basic.Countable.Defs
import Mathlib.Basic.Countable.Small
import Mathlib.Logic.Encodable.Basic
import Mathlib.Order.CompleteLattice.Finset
import Mathlib.Order.Hom.Basic
import Scott2026.RandomVariables.NegligibilitySpace
import Scott2026.Setoids.Setoid
import Scott2026.Setoids.PowerSet
import Scott2026.LambdaModels.Engeler.Engeler
import Scott2026.RandomVariables.Random.AssociatedAlgebra
import Scott2026.RandomVariables.Random.AssociatedAlgebra.Le
import Scott2026.RandomVariables.Random.AssociatedAlgebra.bot
import Scott2026.RandomVariables.Random.AssociatedAlgebra.compl
import Scott2026.RandomVariables.Random.AssociatedAlgebra.inf
import Scott2026.RandomVariables.Random.AssociatedAlgebra.mk
import Scott2026.RandomVariables.Random.AssociatedAlgebra.sInf
import Scott2026.RandomVariables.Random.AssociatedAlgebra.sSup
import Scott2026.RandomVariables.Random.AssociatedAlgebra.sup
import Scott2026.RandomVariables.Random.AssociatedAlgebra.top
import Scott2026.RandomVariables.Random.G_X
import Scott2026.RandomVariables.Random.G_X_inv
import Scott2026.RandomVariables.Random.G_X_measure
import Scott2026.RandomVariables.Random.G_X_measure_inv
import Scott2026.RandomVariables.Random.G_X_measure_invLaws
import Scott2026.RandomVariables.Random.G_pre
import Scott2026.RandomVariables.Random.IsAtomic
import Scott2026.RandomVariables.Random.IsL0
import Scott2026.RandomVariables.Random.L0
import Scott2026.RandomVariables.Random.L0.app
import Scott2026.RandomVariables.Random.L0.app_measure
import Scott2026.RandomVariables.Random.L0.equivPower
import Scott2026.RandomVariables.Random.L0.equivPower_measure
import Scott2026.RandomVariables.Random.L0.le
import Scott2026.RandomVariables.Random.L0.le_measure
import Scott2026.RandomVariables.Random.L0.mk
import Scott2026.RandomVariables.Random.L0.mk_measure
import Scott2026.RandomVariables.Random.L0Fun
import Scott2026.RandomVariables.Random.L0Measure
import Scott2026.RandomVariables.Random.MeasurableSetoid
import Scott2026.RandomVariables.Random.MeasureAlgebra
import Scott2026.RandomVariables.Random.MeasureAlgebra.Le
import Scott2026.RandomVariables.Random.MeasureAlgebra.bot
import Scott2026.RandomVariables.Random.MeasureAlgebra.compl
import Scott2026.RandomVariables.Random.MeasureAlgebra.inf
import Scott2026.RandomVariables.Random.MeasureAlgebra.mk
import Scott2026.RandomVariables.Random.MeasureAlgebra.sInf
import Scott2026.RandomVariables.Random.MeasureAlgebra.sSup
import Scott2026.RandomVariables.Random.MeasureAlgebra.sup
import Scott2026.RandomVariables.Random.MeasureAlgebra.toAssociated
import Scott2026.RandomVariables.Random.MeasureAlgebra.top
import Scott2026.RandomVariables.Random.MeasureAlgebra.instances
import Scott2026.RandomVariables.Random.MeasureAlgebra.supMk
import Scott2026.RandomVariables.Random.MeasureAlgebra.iInfMkFinset
import Scott2026.RandomVariables.Random.G_pre
import Scott2026.RandomVariables.Random.NegligibilitySpace.measRep
import Scott2026.RandomVariables.Random.NegligibilitySpace.ofMeasure
import Scott2026.RandomVariables.Random.aeEq
import Scott2026.RandomVariables.Random.aeSetoid
import Scott2026.RandomVariables.Random.atomlessSeq
import Scott2026.RandomVariables.Random.atomlessSeqAux
import Scott2026.RandomVariables.Random.existsLtAtomless
import Scott2026.RandomVariables.Random.constRV
import Scott2026.RandomVariables.Random.engelerAppA
import Scott2026.RandomVariables.Random.l0AE
import Scott2026.RandomVariables.Random.l0AE_measure
import Scott2026.RandomVariables.Random.l0APoset
import Scott2026.RandomVariables.Random.l0App
import Scott2026.RandomVariables.Random.l0Eq
import Scott2026.RandomVariables.Random.l0Le
import Scott2026.RandomVariables.Random.l0Poset
import Scott2026.RandomVariables.Random.l0Poset_measure
import Scott2026.RandomVariables.Random.l0Setoid
import Scott2026.RandomVariables.Random.l0Setoid_measure
import Scott2026.RandomVariables.Random.meetlessSeq
import Scott2026.RandomVariables.Random.posBasic
import Scott2026.RandomVariables.Random.proposition_39
import Scott2026.RandomVariables.Random.G_X_measureLe
import Scott2026.RandomVariables.Random.l0AppAeMeasure
import Scott2026.RandomVariables.Random.Proofs.Core
import Scott2026.RandomVariables.Random.Proofs.CoreCont

namespace Scott2026

open MeasureTheory Set
open scoped ENNReal


variable {X Y : Type*} [MeasurableSpace X]

/-- Definition 37: measurable maps into `Set Y` (Borel of the positive topology).
We take measurability of all preimages of `B_y`, which generate that σ-algebra
when `Y` is countable. -/
theorem lemma_41_measure (μ : Measure X) [IsFiniteMeasure μ] [Countable Y]
    (S : Set Y) :
    G_X_measure μ (L0.L0.mk_measure μ
        ⟨constRV (X := X) S, constRV_isL0 (X := X) S⟩) =
      checkSet (A := MeasureAlgebra μ) S := by
  let a : L0Fun X Y := ⟨constRV (X := X) S, constRV_isL0 (X := X) S⟩
  change G_X_measure μ (L0.L0.mk_measure μ a) = checkSet (A := MeasureAlgebra μ) S
  funext y
  rw [G_X_measure_mk]
  by_cases hy : y ∈ S
  · have hpre : G_pre a.val y = Set.univ := by
      ext x
      simp [G_pre, posBasic, show a.val x = S from rfl, hy]
    refine (MeasureAlgebra.mk_congr (ht := MeasurableSet.univ) μ hpre).trans ?_
    rw [MeasureAlgebra.mk_top, checkSet_mem hy]
  · have hpre : G_pre a.val y = (∅ : Set X) := by
      ext x
      simp [G_pre, posBasic, show a.val x = S from rfl, hy]
    refine (MeasureAlgebra.mk_congr (ht := MeasurableSet.empty) μ hpre).trans ?_
    rw [MeasureAlgebra.mk_bot, checkSet_not_mem hy]
theorem proposition_40_measure [DecidableEq E] [Countable E] (μ : Measure X)
    [IsFiniteMeasure μ] (pair : Finset E × E → E) (a b : L0Measure μ E) :
    G_X_measure μ (L0.L0.app_measure μ pair a b) =
      engelerAppA pair (G_X_measure μ a) (G_X_measure μ b) := by
  refine Quotient.inductionOn₂ a b fun a b => ?_
  funext q
  have happ :
      L0.L0.app_measure μ pair (Quotient.mk (l0Setoid_measure μ E) a)
        (Quotient.mk (l0Setoid_measure μ E) b) =
        L0.L0.mk_measure μ ⟨l0App pair a.val b.val,
          l0App_isL0 pair a.property b.property⟩ :=
    rfl
  rw [happ]
  have hG : G_X_measure μ (L0.L0.mk_measure μ
        ⟨l0App pair a.val b.val, l0App_isL0 pair a.property b.property⟩) q =
      MeasureAlgebra.mk μ (G_pre (l0App pair a.val b.val) q)
        (l0App_isL0 pair a.property b.property q) :=
    rfl
  rw [hG]
  have hpre : G_pre (l0App pair a.val b.val) q =
      ⋃ K : Finset E, G_pre a.val (pair (K, q)) ∩ ⋂ k ∈ K, G_pre b.val k :=
    G_pre_l0App pair a.val b.val q
  let hsU : MeasurableSet
      (⋃ K : Finset E, G_pre a.val (pair (K, q)) ∩ ⋂ k ∈ K, G_pre b.val k) :=
    MeasurableSet.iUnion fun K =>
      (a.property (pair (K, q))).inter
        (Finset.measurableSet_biInter K fun k _ => b.property k)
  refine (MeasureAlgebra.mk_congr (ht := hsU) μ hpre).trans ?_
  haveI : Countable (Finset E) := inferInstance
  have hunion :
      MeasureAlgebra.mk μ
          (⋃ K : Finset E,
            G_pre a.val (pair (K, q)) ∩ ⋂ k ∈ K, G_pre b.val k) hsU =
        ⨆ K : Finset E,
          MeasureAlgebra.mk μ
            (G_pre a.val (pair (K, q)) ∩ ⋂ k ∈ K, G_pre b.val k)
            ((a.property (pair (K, q))).inter
              (Finset.measurableSet_biInter K fun k _ => b.property k)) :=
    (MeasureAlgebra.iSup_mk μ
      (fun K : Finset E =>
        G_pre a.val (pair (K, q)) ∩ ⋂ k ∈ K, G_pre b.val k)
      (fun K => (a.property (pair (K, q))).inter
        (Finset.measurableSet_biInter K fun k _ => b.property k))).symm
  refine hunion.trans ?_
  refine iSup_congr fun K => ?_
  have haG : G_X_measure μ (Quotient.mk (l0Setoid_measure μ E) a) (pair (K, q)) =
      MeasureAlgebra.mk μ (G_pre a.val (pair (K, q)))
        (a.property (pair (K, q))) := rfl
  have hbG : ∀ k, G_X_measure μ (Quotient.mk (l0Setoid_measure μ E) b) k =
      MeasureAlgebra.mk μ (G_pre b.val k) (b.property k) := fun _ => rfl
  simp_rw [haG, hbG]
  rw [MeasureAlgebra.iInf_mk_finset μ K (fun k => G_pre b.val k)
    (fun k => b.property k)]
  exact (MeasureAlgebra.inf_mk μ (G_pre a.val (pair (K, q)))
      (⋂ k ∈ K, G_pre b.val k) (a.property (pair (K, q)))
      (Finset.measurableSet_biInter K fun k _ => b.property k)).symm

/-- Proposition 44 records that `L⁰` is typically *not* a continuous dcpo
externally; the paper proves this when the associated algebra is non-atomic. -/
theorem G_X_equiv (N : NegligibilitySpace X) [Countable Y] (a : L0 N Y) :
    G_X N a = (L0.equivPower (Y := Y) N).toFun a :=
  rfl

theorem G_X_symm (N : NegligibilitySpace X) [Countable Y]
    (b : ASubset (AssociatedAlgebra N) Y) :
    G_X N ((L0.equivPower (Y := Y) N).invFun b) = b := by
  change (L0.equivPower (Y := Y) N).toFun
      ((L0.equivPower (Y := Y) N).invFun b) = b
  exact APoset.StrictIso.right_inv _ _

/-- Order on `L⁰` transported along `G_X`. -/
noncomputable instance instPartialOrderL0
    {X Y : Type*} [MeasurableSpace X] (N : NegligibilitySpace X) [Countable Y] :
    PartialOrder (L0 N Y) where
  le a b := G_X N a ≤ G_X N b
  le_refl _ := le_rfl
  le_trans _ _ _ := le_trans
  le_antisymm a b hab hba :=
    APoset.StrictIso.injective (L0.equivPower (Y := Y) N) (le_antisymm hab hba)

noncomputable instance instSupSetL0
    {X Y : Type*} [MeasurableSpace X] (N : NegligibilitySpace X) [Countable Y] :
    SupSet (L0 N Y) where
  sSup S := (L0.equivPower (Y := Y) N).invFun (sSup (G_X N '' S))

/-- External complete lattice on `L⁰`, transported along `G_X`. -/
noncomputable instance instCompleteLatticeL0
    {X Y : Type*} [MeasurableSpace X] (N : NegligibilitySpace X) [Countable Y] :
    CompleteLattice (L0 N Y) :=
  completeLatticeOfSup (L0 N Y) fun S => by
    constructor
    · intro a ha
      change G_X N a ≤ G_X N ((L0.equivPower (Y := Y) N).invFun (sSup (G_X N '' S)))
      rw [G_X_symm]
      exact le_sSup (mem_image_of_mem (G_X N) ha)
    · intro b hb
      change G_X N ((L0.equivPower (Y := Y) N).invFun (sSup (G_X N '' S))) ≤ G_X N b
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
  change G_X N ((L0.equivPower (Y := Y) N).invFun (sSup (G_X N '' S))) =
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
    apply APoset.StrictIso.injective (L0.equivPower (Y := Y) N)
    rw [← G_X_equiv, ← G_X_equiv, h, G_X_bot]

theorem wayBelow_bot {D : Type*} [CompleteLattice D] (d : D) : (⊥ : D) ≪ d := by
  intro S hne _hdir _hle
  obtain ⟨s, hs⟩ := hne
  exact ⟨s, hs, bot_le⟩

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
    (L0.equivPower (Y := Y) N).invFun x ≤ (L0.equivPower (Y := Y) N).invFun y ↔
      x ≤ y := by
  change G_X N ((L0.equivPower (Y := Y) N).invFun x) ≤
      G_X N ((L0.equivPower (Y := Y) N).invFun y) ↔ x ≤ y
  rw [G_X_symm, G_X_symm]

theorem G_X_image_symm {X Y : Type*} [MeasurableSpace X] [Countable Y]
    (N : NegligibilitySpace X) (S : Set (ASubset (AssociatedAlgebra N) Y)) :
    G_X N '' ((L0.equivPower (Y := Y) N).invFun '' S) = S := by
  ext x
  constructor
  · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩
    rwa [G_X_symm]
  · intro hx
    exact ⟨(L0.equivPower (Y := Y) N).invFun x, ⟨x, hx, rfl⟩, G_X_symm N x⟩

theorem wayBelow_iff_G_X {X Y : Type*} [MeasurableSpace X] [Countable Y]
    (N : NegligibilitySpace X) (a b : L0 N Y) :
    a ≪ b ↔ G_X N a ≪ G_X N b := by
  constructor
  · intro h S hne hdir hle
    let S' : Set (L0 N Y) := (L0.equivPower (Y := Y) N).invFun '' S
    have hne' : S'.Nonempty := hne.image _
    have hdir' : DirectedOn (· ≤ ·) S' := by
      intro x hx y hy
      obtain ⟨sx, hsx, rfl⟩ := hx
      obtain ⟨sy, hsy, rfl⟩ := hy
      obtain ⟨z, hz, hzx, hzy⟩ := hdir sx hsx sy hsy
      exact ⟨(L0.equivPower (Y := Y) N).invFun z, ⟨z, hz, rfl⟩,
        (L0.le_symm N).mpr hzx, (L0.le_symm N).mpr hzy⟩
    have hle' : b ≤ sSup S' := by
      change G_X N b ≤ G_X N (sSup S')
      rw [G_X_sSup, G_X_image_symm]
      exact hle
    obtain ⟨w, hw, haw⟩ := h hne' hdir' hle'
    obtain ⟨z, hz, rfl⟩ := hw
    change G_X N a ≤ G_X N ((L0.equivPower (Y := Y) N).invFun z) at haw
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
    let d' := (L0.equivPower (Y := Y) N).invFun d
    obtain ⟨hdir, hsup⟩ := h d'
    have himg : G_X N '' {e | e ≪ d'} = {f | f ≪ d} := by
      ext f
      constructor
      · intro hf
        obtain ⟨e, he, rfl⟩ := (mem_image _ _ _).1 hf
        have : G_X N e ≪ G_X N d' := (wayBelow_iff_G_X N e d').mp he
        rwa [G_X_symm] at this
      · intro hf
        refine ⟨(L0.equivPower (Y := Y) N).invFun f, ?_, G_X_symm N f⟩
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
    have himg : (L0.equivPower (Y := Y) N).invFun '' {f | f ≪ G_X N d} =
        {e | e ≪ d} := by
      ext e
      constructor
      · intro he
        obtain ⟨f, hf, rfl⟩ := (mem_image _ _ _).1 he
        exact (wayBelow_iff_G_X N _ d).mpr (by rwa [G_X_symm])
      · intro he
        refine ⟨G_X N e, (wayBelow_iff_G_X N e d).mp he, ?_⟩
        exact APoset.StrictIso.left_inv (L0.equivPower (Y := Y) N) e
    constructor
    · intro x hx y hy
      have hx' : x ∈ (L0.equivPower (Y := Y) N).invFun '' {f | f ≪ G_X N d} := by
        rwa [himg]
      have hy' : y ∈ (L0.equivPower (Y := Y) N).invFun '' {f | f ≪ G_X N d} := by
        rwa [himg]
      obtain ⟨fx, hfx, rfl⟩ := (mem_image _ _ _).1 hx'
      obtain ⟨fy, hfy, rfl⟩ := (mem_image _ _ _).1 hy'
      obtain ⟨z, hz, hzx, hzy⟩ := hdir fx hfx fy hfy
      refine ⟨(L0.equivPower (Y := Y) N).invFun z, ?_,
        (L0.le_symm N).mpr hzx, (L0.le_symm N).mpr hzy⟩
      exact himg ▸ ⟨z, hz, rfl⟩
    · apply APoset.StrictIso.injective (L0.equivPower (Y := Y) N)
      rw [← G_X_equiv, ← G_X_equiv]
      calc
        G_X N d = sSup {f | f ≪ G_X N d} := hsup
        _ = sSup (G_X N '' ((L0.equivPower (Y := Y) N).invFun ''
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

/-- Paper Proposition 44 wording. On a complete lattice the paper’s
“continuous dcpo” is `IsContinuousDcpo` (`IsContinuousLattice`); this
does not claim failure of directed-completeness. -/
theorem proposition_44_dcpo {X Y : Type*} [MeasurableSpace X] [Countable Y]
    [Nonempty Y] (N : NegligibilitySpace X)
    (hA : ¬IsAtomic (AssociatedAlgebra N)) :
    ¬IsContinuousDcpo (L0 N Y) :=
  proposition_44 N hA

theorem G_X_measure_symm (μ : Measure X) [Countable Y]
    (b : ASubset (MeasureAlgebra μ) Y) :
    G_X_measure μ ((L0.equivPower_measure (Y := Y) μ).symm b) = b :=
  (L0.equivPower_measure (Y := Y) μ).apply_symm_apply b

/-- Order on `L⁰` transported along `G_X_measure`. -/
noncomputable instance instPartialOrderL0Measure
    {X Y : Type*} [MeasurableSpace X] (μ : Measure X) [IsFiniteMeasure μ]
    [Countable Y] :
    PartialOrder (L0Measure μ Y) where
  le a b := G_X_measure μ a ≤ G_X_measure μ b
  le_refl _ := le_rfl
  le_trans _ _ _ := le_trans
  le_antisymm a b hab hba :=
    (L0.equivPower_measure (Y := Y) μ).injective (le_antisymm hab hba)

noncomputable instance instSupSetL0Measure
    {X Y : Type*} [MeasurableSpace X] (μ : Measure X) [IsFiniteMeasure μ]
    [Countable Y] :
    SupSet (L0Measure μ Y) where
  sSup S := (L0.equivPower_measure (Y := Y) μ).symm (sSup (G_X_measure μ '' S))

/-- External complete lattice on paper `L⁰`, transported along `G_X_measure`. -/
noncomputable instance instCompleteLatticeL0Measure
    {X Y : Type*} [MeasurableSpace X] (μ : Measure X) [IsFiniteMeasure μ]
    [Countable Y] :
    CompleteLattice (L0Measure μ Y) :=
  completeLatticeOfSup (L0Measure μ Y) fun S => by
    constructor
    · intro a ha
      change G_X_measure μ a ≤
        G_X_measure μ ((L0.equivPower_measure (Y := Y) μ).symm
          (sSup (G_X_measure μ '' S)))
      rw [G_X_measure_symm]
      exact le_sSup (mem_image_of_mem (G_X_measure μ) ha)
    · intro b hb
      change G_X_measure μ ((L0.equivPower_measure (Y := Y) μ).symm
          (sSup (G_X_measure μ '' S))) ≤ G_X_measure μ b
      rw [G_X_measure_symm]
      exact sSup_le fun x hx => by
        obtain ⟨a, ha, rfl⟩ := (mem_image _ _ _).1 hx
        exact hb ha

theorem G_X_measure_sSup {X Y : Type*} [MeasurableSpace X] {μ : Measure X}
    [IsFiniteMeasure μ] [Countable Y] (S : Set (L0Measure μ Y)) :
    G_X_measure μ (sSup S) = sSup (G_X_measure μ '' S) :=
  G_X_measure_symm μ _

theorem isLUB_orderIso {A B : Type*} [PartialOrder A] [PartialOrder B]
    (e : A ≃o B) {s : Set A} {a : A} (h : IsLUB s a) :
    IsLUB (e '' s) (e a) := by
  constructor
  · intro x hx
    obtain ⟨y, hy, rfl⟩ := hx
    exact e.le_iff_le.mpr (h.1 hy)
  · intro b hb
    have : a ≤ e.symm b := h.2 fun y hy => by
      have : e.symm (e y) ≤ e.symm b :=
        e.symm.le_iff_le.mpr (hb (mem_image_of_mem e hy))
      simpa using this
    exact (e.le_iff_le.mpr this).trans_eq (e.apply_symm_apply b)

theorem orderIso_map_sSup {A B : Type*} [CompleteLattice A] [CompleteLattice B]
    (e : A ≃o B) (s : Set A) : e (sSup s) = sSup (e '' s) :=
  (isLUB_orderIso e (isLUB_sSup s)).unique (isLUB_sSup (e '' s))

theorem wayBelow_map_orderIso {A B : Type*} [CompleteLattice A] [CompleteLattice B]
    (e : A ≃o B) {x y : A} (h : x ≪ y) : e x ≪ e y := by
  intro S hne hdir hle
  let S' : Set A := e.symm '' S
  have hne' : S'.Nonempty := hne.image _
  have hdir' : DirectedOn (· ≤ ·) S' := by
    intro p hp q hq
    obtain ⟨sp, hsp, rfl⟩ := hp
    obtain ⟨sq, hsq, rfl⟩ := hq
    obtain ⟨z, hz, hzp, hzq⟩ := hdir sp hsp sq hsq
    exact ⟨e.symm z, ⟨z, hz, rfl⟩,
      e.symm.le_iff_le.mpr hzp, e.symm.le_iff_le.mpr hzq⟩
  have hle' : y ≤ sSup S' := by
    have : e.symm (e y) ≤ e.symm (sSup S) := e.symm.le_iff_le.mpr hle
    simpa [orderIso_map_sSup e.symm] using this
  obtain ⟨w, hw, hxw⟩ := h hne' hdir' hle'
  obtain ⟨z, hz, rfl⟩ := hw
  exact ⟨z, hz, (e.le_iff_le.mpr hxw).trans_eq (e.apply_symm_apply z)⟩

theorem wayBelow_orderIso {A B : Type*} [CompleteLattice A] [CompleteLattice B]
    (e : A ≃o B) {x y : A} : x ≪ y ↔ e x ≪ e y :=
  ⟨wayBelow_map_orderIso e, fun h => by
    simpa using wayBelow_map_orderIso e.symm h⟩

theorem isContinuousLattice_of_orderIso {A B : Type*}
    [CompleteLattice A] [CompleteLattice B]
    (e : A ≃o B) (hB : IsContinuousLattice B) : IsContinuousLattice A := by
  intro a
  obtain ⟨hdir, hsup⟩ := hB (e a)
  have himg : e.symm '' {f | f ≪ e a} = {x | x ≪ a} := by
    ext x
    constructor
    · rintro ⟨f, hf, rfl⟩
      exact (wayBelow_orderIso e).mpr (by simpa using hf)
    · intro hx
      exact ⟨e x, (wayBelow_orderIso e).mp hx, Equiv.symm_apply_apply _ _⟩
  constructor
  · intro p hp q hq
    have hp' : p ∈ e.symm '' {f | f ≪ e a} := by rwa [himg]
    have hq' : q ∈ e.symm '' {f | f ≪ e a} := by rwa [himg]
    obtain ⟨fp, hfp, rfl⟩ := (mem_image _ _ _).1 hp'
    obtain ⟨fq, hfq, rfl⟩ := (mem_image _ _ _).1 hq'
    obtain ⟨z, hz, hzp, hzq⟩ := hdir fp hfp fq hfq
    refine ⟨e.symm z, ?_, e.symm.le_iff_le.mpr hzp, e.symm.le_iff_le.mpr hzq⟩
    exact himg ▸ ⟨z, hz, rfl⟩
  · have := congrArg e.symm hsup
    simpa [orderIso_map_sSup e.symm, himg] using this

theorem isContinuousLattice_iff_orderIso {A B : Type*}
    [CompleteLattice A] [CompleteLattice B] (e : A ≃o B) :
    IsContinuousLattice A ↔ IsContinuousLattice B :=
  ⟨fun hA => isContinuousLattice_of_orderIso e.symm hA,
    isContinuousLattice_of_orderIso e⟩

namespace L0

noncomputable def orderIsoPower_measure (μ : Measure X) [IsFiniteMeasure μ]
    [Countable Y] :
    L0Measure μ Y ≃o ASubset (MeasureAlgebra μ) Y where
  toEquiv := equivPower_measure μ
  map_rel_iff' := Iff.rfl

end L0

theorem isContinuousLattice_iff_G_X_measure {X Y : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsFiniteMeasure μ] [Countable Y] :
    IsContinuousLattice (L0Measure μ Y) ↔
      IsContinuousLattice (ASubset (MeasureAlgebra μ) Y) :=
  isContinuousLattice_iff_orderIso (L0.orderIsoPower_measure (Y := Y) μ)
theorem not_isAtom_mk_of_proper_subset {X : Type*} [MeasurableSpace X]
    {μ : Measure X} [IsFiniteMeasure μ] {s t : Set X}
    (hs : MeasurableSet s) (ht : MeasurableSet t)
    (hsub : t ⊆ s) (ht0 : μ t ≠ 0) (hlt : μ t < μ s) :
    ¬IsAtom (MeasureAlgebra.mk μ s hs) := by
  intro hAtom
  let a := MeasureAlgebra.mk μ s hs
  let b := MeasureAlgebra.mk μ t ht
  have hle : b ≤ a :=
    (MeasureAlgebra.le_mk μ).mpr (by
      have : t \ s = ∅ := diff_eq_empty.mpr hsub
      simpa [this] using measure_empty)
  have hne : b ≠ ⊥ := fun hb =>
    ht0 ((MeasureAlgebra.mk_eq_bot μ).mp (show b = MeasureAlgebra.bot μ from hb))
  have hna : ¬a ≤ b := by
    intro hab
    have hst : μ (s \ t) = 0 := (MeasureAlgebra.le_mk μ).mp hab
    have hadd := measure_inter_add_sdiff (μ := μ) s ht
    have hinter : s ∩ t = t := inter_eq_right.mpr hsub
    rw [hinter, hst, add_zero] at hadd
    exact (ne_of_lt hlt) hadd
  exact hne (hAtom.2 b ⟨hle, hna⟩)

theorem not_isAtomic_measureAlgebra_of_splits {X : Type*} [MeasurableSpace X]
    {μ : Measure X} [IsFiniteMeasure μ] (hpos : μ Set.univ ≠ 0)
    (hsplit : ∀ ⦃s : Set X⦄, MeasurableSet s → μ s ≠ 0 →
      ∃ t, MeasurableSet t ∧ t ⊆ s ∧ μ t ≠ 0 ∧ μ t < μ s) :
    ¬IsAtomic (MeasureAlgebra μ) := by
  intro h
  have htop : (⊤ : MeasureAlgebra μ) ≠ ⊥ := by
    intro hbot
    have : MeasureAlgebra.mk μ Set.univ MeasurableSet.univ = ⊥ := by
      rwa [MeasureAlgebra.mk_top]
    exact hpos ((MeasureAlgebra.mk_eq_bot μ).mp this)
  obtain ⟨b, hb, _⟩ := h ⊤ htop
  let s := (Quotient.out b).val
  have hs := (Quotient.out b).property
  have hbmk : MeasureAlgebra.mk μ s hs = b := MeasureAlgebra.mk_out μ b
  have hs0 : μ s ≠ 0 := by
    intro h0
    have : b = ⊥ := by
      rw [← hbmk]
      exact (MeasureAlgebra.mk_eq_bot μ).mpr h0
    exact hb.1 this
  obtain ⟨t, ht, hsub, ht0, hlt⟩ := hsplit hs hs0
  exact not_isAtom_mk_of_proper_subset hs ht hsub ht0 hlt (by rwa [hbmk])

/-- Proposition 44 on the paper algebra `A(X) = Σ/N(μ)`. -/
theorem proposition_44_measure {X Y : Type*} [MeasurableSpace X]
    {μ : Measure X} [IsFiniteMeasure μ] [Countable Y] [Nonempty Y]
    (hA : ¬IsAtomic (MeasureAlgebra μ)) :
    ¬IsContinuousDcpo (L0Measure μ Y) :=
  fun h => not_isContinuousLattice_fun_of_not_atomic (Y := Y) hA
    ((isContinuousLattice_iff_G_X_measure (Y := Y) μ).mp h)


end Scott2026
