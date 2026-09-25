/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/

import Mathlib.Data.Multiset.DershowitzManna
import Mathlib.Logic.Pairwise
import Mathlib.Order.CompleteBooleanAlgebra
import Mathlib.Order.Heyting.Basic
import Mathlib.Order.Zorn
import Mathlib.SetTheory.Cardinal.Order
import Mathlib.SetTheory.Ordinal.Family
import Mathlib.SetTheory.ZFC.PSet
import Scott2026.BooleanLogic
import Scott2026.VA.SetFormula
import Scott2026.VA.D0Formula
import Scott2026.VA.AName
import Scott2026.VA.AName.child
import Scott2026.VA.AName.idx
import Scott2026.VA.AName.meas
import Scott2026.VA.AName.measLt
import Scott2026.VA.AName.rank
import Scott2026.VA.AName.val
import Scott2026.VA.AName.eqBLaws
import Scott2026.VA.AName.fullness
import Scott2026.VA.AName.check
import Scott2026.VA.AName.mix
import Scott2026.VA.D0Formula.bval
import Scott2026.VA.D0Formula.consName
import Scott2026.VA.D0Formula.iInfFinSucc
import Scott2026.VA.D0Formula.consPSet
import Scott2026.VA.D0Formula.realize
import Scott2026.VA.HomName
import Scott2026.VA.SetFormula.bval
import Scott2026.VA.SetFormula.iff
import Scott2026.VA.SetFormula.implies
import Scott2026.VA.SetFormula.inst
import Scott2026.VA.SetFormula.lift
import Scott2026.VA.SetFormula.or
import Scott2026.VA.SetFormula.rename
import Scott2026.VA.canonVal
import Scott2026.VA.choiceAxiom
import Scott2026.VA.colRename
import Scott2026.VA.collectB
import Scott2026.VA.collectionAxiom
import Scott2026.VA.compB
import Scott2026.VA.eqLeibnizAxiom
import Scott2026.VA.eqLeibnizRenameX
import Scott2026.VA.eqLeibnizRenameY
import Scott2026.VA.extensionalityAxiom
import Scott2026.VA.finsetB
import Scott2026.VA.funsB
import Scott2026.VA.homB
import Scott2026.VA.idB
import Scott2026.VA.infinityAxiom
import Scott2026.VA.insertB
import Scott2026.VA.isFiniteB
import Scott2026.VA.isFunctionB
import Scott2026.VA.isInductiveB
import Scott2026.VA.isOpairF
import Scott2026.VA.isSingleValuedB
import Scott2026.VA.isSingletonF
import Scott2026.VA.isTotalB
import Scott2026.VA.isUPairF
import Scott2026.VA.leastIdx
import Scott2026.VA.nameSetoid
import Scott2026.VA.opairB
import Scott2026.VA.opairMemF
import Scott2026.VA.pOpair
import Scott2026.VA.pairB
import Scott2026.VA.pairingAxiom
import Scott2026.VA.pfin
import Scott2026.VA.pfinB
import Scott2026.VA.pfinEnum
import Scott2026.VA.powerAxiom
import Scott2026.VA.powerB
import Scott2026.VA.prodB
import Scott2026.VA.regularityAxiom
import Scott2026.VA.restrictName
import Scott2026.VA.sepB
import Scott2026.VA.sepRename
import Scott2026.VA.separationAxiom
import Scott2026.VA.singletonB
import Scott2026.VA.succB
import Scott2026.VA.unionAxiom
import Scott2026.VA.unionB
import Scott2026.VA.wellOrderAxiom
import Scott2026.VA.wellOrderB
import Scott2026.VA.worDisj
import Scott2026.VA.worITE
import Scott2026.VA.worLe
import Scott2026.VA.worPredSup

namespace Scott2026

universe u


namespace AName

variable {A : Type u}

theorem rank_mk (α : Type u) (f : α → AName A) (v : α → A) :
    rank (mk α f v) = ⨆ i : α, rank (f i) + 1 :=
  rfl

variable [CompleteBooleanAlgebra A]

end AName

open AName

namespace D0Formula

variable {A : Type u} [CompleteBooleanAlgebra A]

omit [CompleteBooleanAlgebra A] in
@[simp] theorem consName_zero {n : ℕ} (x : AName.{u} A) (ρ : Fin n → AName.{u} A) :
    consName x ρ 0 = x := by
  simp [consName]
omit [CompleteBooleanAlgebra A] in
@[simp] theorem consName_succ {n : ℕ} (x : AName.{u} A) (ρ : Fin n → AName.{u} A)
    (i : Fin n) : consName x ρ i.succ = ρ i := by
  simp [consName]

theorem eqB_iInf_cons {n : ℕ} (y : AName.{u} A) (ρ σ : Fin n → AName.{u} A) :
    (⨅ i, eqB (consName y ρ i) (consName y σ i)) = ⨅ i, eqB (ρ i) (σ i) := by
  rw [iInf_fin_succ (fun i => eqB (consName y ρ i) (consName y σ i))]
  simp [eqB_self]

theorem inf_compl_le_compl_iff {a b c : A} : a ⊓ bᶜ ≤ cᶜ ↔ a ⊓ c ≤ b := by
  rw [le_compl_iff_disjoint_right, disjoint_iff, inf_right_comm, ← disjoint_iff,
    disjoint_compl_right_iff]

/-- Equality of names is a congruence for Boolean values of `Δ₀` formulas. -/
theorem bval_congr {n : ℕ} (φ : D0Formula n) (ρ σ : Fin n → AName.{u} A) :
    (⨅ i, eqB (ρ i) (σ i)) ⊓ bval φ ρ ≤ bval φ σ := by
  induction φ with
  | mem i j =>
    have hij : (⨅ k, eqB (ρ k) (σ k)) ≤ eqB (ρ i) (σ i) ⊓ eqB (ρ j) (σ j) :=
      le_inf (iInf_le _ i) (iInf_le _ j)
    refine (inf_le_inf_right (memB (ρ i) (ρ j)) hij).trans ?_
    have h₁ : eqB (ρ i) (σ i) ⊓ memB (ρ i) (ρ j) ≤ memB (σ i) (ρ j) := by
      rw [inf_comm]; exact memB_eqB_left (ρ i) (ρ j) (σ i)
    have h₂ : memB (σ i) (ρ j) ⊓ eqB (ρ j) (σ j) ≤ memB (σ i) (σ j) :=
      memB_eqB_right (ρ j) (σ i) (σ j)
    refine le_trans ?_ h₂
    refine le_inf ?_ ?_
    · refine le_trans ?_ h₁
      exact le_inf (inf_le_of_left_le inf_le_left) inf_le_right
    · exact inf_le_of_left_le inf_le_right
  | eq i j =>
    have hij : (⨅ k, eqB (ρ k) (σ k)) ≤ eqB (ρ i) (σ i) ⊓ eqB (ρ j) (σ j) :=
      le_inf (iInf_le _ i) (iInf_le _ j)
    refine (inf_le_inf_right (eqB (ρ i) (ρ j)) hij).trans ?_
    have h₁ : eqB (σ i) (ρ i) ⊓ eqB (ρ i) (ρ j) ≤ eqB (σ i) (ρ j) :=
      eqB_trans (σ i) (ρ i) (ρ j)
    have h₂ : eqB (σ i) (ρ j) ⊓ eqB (ρ j) (σ j) ≤ eqB (σ i) (σ j) :=
      eqB_trans (σ i) (ρ j) (σ j)
    refine le_trans ?_ h₂
    refine le_inf ?_ ?_
    · refine le_trans ?_ h₁
      rw [eqB_comm (x := ρ i) (y := σ i)]
      exact le_inf (inf_le_of_left_le inf_le_left) inf_le_right
    · exact inf_le_of_left_le inf_le_right
  | not φ ih =>
    rw [bval_not, bval_not, inf_compl_le_compl_iff]
    have hcomm : (⨅ i, eqB (σ i) (ρ i)) = ⨅ i, eqB (ρ i) (σ i) :=
      iInf_congr fun i => eqB_comm (σ i) (ρ i)
    simpa [hcomm] using ih σ ρ
  | and φ ψ ihφ ihψ =>
    rw [bval_and, bval_and]
    refine le_inf ?_ ?_
    · exact (inf_le_inf_left _ inf_le_left).trans (ihφ ρ σ)
    · exact (inf_le_inf_left _ inf_le_right).trans (ihψ ρ σ)
  | bExists k φ ih =>
    rw [bval_bExists, bval_bExists,
      inf_iSup_eq (a := (⨅ i, eqB (ρ i) (σ i) : A))]
    refine iSup_le fun y => ?_
    refine le_trans ?_ (le_iSup
      (fun y' : AName A => (memB y' (σ k) ⊓ bval φ (consName y' σ) : A)) y)
    refine le_inf ?_ ?_
    · have hmem : memB y (ρ k) ⊓ eqB (ρ k) (σ k) ≤ memB y (σ k) :=
        memB_eqB_right (ρ k) y (σ k)
      refine le_trans ?_ hmem
      refine le_inf (inf_le_of_right_le inf_le_left) ?_
      exact inf_le_of_left_le (iInf_le _ k)
    · have hcons := eqB_iInf_cons y ρ σ
      have := ih (consName y ρ) (consName y σ)
      refine le_trans ?_ this
      rw [← hcons]
      exact le_inf inf_le_left (inf_le_of_right_le inf_le_right)
  | bForall k φ ih =>
    rw [bval_bForall, bval_bForall]
    refine le_iInf fun y => ?_
    rw [le_himp_iff]
    have hcons := eqB_iInf_cons y ρ σ
    have hmem : (⨅ i, eqB (ρ i) (σ i)) ⊓ memB y (σ k) ≤ memB y (ρ k) := by
      have := memB_eqB_right (σ k) y (ρ k)
      refine le_trans ?_ this
      refine le_inf inf_le_right ?_
      rw [eqB_comm (x := σ k) (y := ρ k)]
      exact inf_le_of_left_le (iInf_le _ k)
    have hto_body :
        (⨅ i, eqB (ρ i) (σ i)) ⊓
          (⨅ y', memB y' (ρ k) ⇨ bval φ (consName y' ρ)) ⊓ memB y (σ k) ≤
        bval φ (consName y ρ) := by
      have hmp : (⨅ y', memB y' (ρ k) ⇨ bval φ (consName y' ρ)) ⊓ memB y (ρ k) ≤
          bval φ (consName y ρ) :=
        le_himp_iff.mp (iInf_le _ y)
      refine le_trans ?_ hmp
      refine le_inf (inf_le_of_left_le inf_le_right) ?_
      exact (inf_le_inf_right (memB y (σ k)) inf_le_left).trans hmem
    have := ih (consName y ρ) (consName y σ)
    refine le_trans ?_ this
    refine le_inf ?_ hto_body
    rw [← hcons]
    exact inf_le_of_left_le inf_le_left

/-- Substitution of equal names into the first free variable. -/
theorem bval_subst {n : ℕ} (φ : D0Formula (n + 1)) (x y : AName.{u} A)
    (ρ : Fin n → AName.{u} A) :
    eqB x y ⊓ bval φ (consName x ρ) ≤ bval φ (consName y ρ) := by
  have h := bval_congr φ (consName x ρ) (consName y ρ)
  have hcons : (⨅ i, eqB (consName x ρ i) (consName y ρ i)) = eqB x y := by
    rw [iInf_fin_succ (fun i => eqB (consName x ρ i) (consName y ρ i))]
    simp [eqB_self]
  rwa [hcons] at h

theorem check_cons {n : ℕ} (x : PSet.{u}) (ρ : Fin n → PSet.{u}) :
    consName (check (A := A) x) (fun i => check (ρ i)) =
      fun i => check (consPSet x ρ i) := by
  ext i
  refine Fin.cases ?_ ?_ i
  · simp [consName, consPSet]
  · intro i
    simp [consName, consPSet]

end D0Formula

open D0Formula

variable {A : Type u} [CompleteBooleanAlgebra A]

/-- Jech Lemma 14.19 / CSL Theorem 1(iii): fullness, for a congruent predicate. -/
theorem jech_lemma_14_19 {n : ℕ} (φ : D0Formula (n + 1))
    (ρ : Fin n → AName.{u} A) :
    ∃ a, bval φ (consName a ρ) = ⨆ x, bval φ (consName x ρ) :=
  fullness (fun x => bval φ (consName x ρ)) fun x y => bval_subst φ x y ρ

/-- CSL Theorem 1(iii): if `‖∃x Φ(x)‖ = a` then some name realizes value `a`. -/
theorem theorem_1_iii (φ : AName.{u} A → A)
    (hcongr : ∀ x y, eqB x y ⊓ φ x ≤ φ y) :
    ∀ a, a = ⨆ x, φ x → ∃ x, φ x = a :=
  fun _a ha => (fullness φ hcongr).imp fun _ h => ha ▸ h

theorem iInf_top_bot {ι : Sort*} [Nontrivial A] (f : ι → A)
    (hf : ∀ i, f i = ⊤ ∨ f i = ⊥) :
    ((⨅ i, f i) = ⊤ ↔ ∀ i, f i = ⊤) ∧ ((⨅ i, f i) = ⊥ ↔ ∃ i, f i = ⊥) := by
  constructor
  · exact iInf_eq_top
  · constructor
    · intro hbot
      by_contra hall
      push Not at hall
      have htop : ∀ i, f i = ⊤ := fun i => (hf i).resolve_right (hall i)
      have : (⨅ i, f i) = ⊤ := iInf_eq_top.mpr htop
      rw [hbot] at this
      exact absurd this bot_ne_top
    · intro ⟨i, hi⟩
      exact bot_unique (hi ▸ iInf_le _ i)

theorem iSup_top_bot {ι : Sort*} [Nontrivial A] (f : ι → A)
    (hf : ∀ i, f i = ⊤ ∨ f i = ⊥) :
    ((⨆ i, f i) = ⊤ ↔ ∃ i, f i = ⊤) ∧ ((⨆ i, f i) = ⊥ ↔ ∀ i, f i = ⊥) := by
  constructor
  · constructor
    · intro htop
      by_contra hall
      push Not at hall
      have hbot : ∀ i, f i = ⊥ := fun i => (hf i).resolve_left (hall i)
      have : (⨆ i, f i) = ⊥ := iSup_eq_bot.mpr hbot
      rw [this] at htop
      exact absurd htop bot_ne_top
    · intro ⟨i, hi⟩
      exact top_unique (hi ▸ le_iSup f i)
  · exact iSup_eq_bot

/-- Check-names are two-valued on atomic equality and membership. -/
theorem check_atomic [Nontrivial A] (x y : PSet.{u}) :
    (eqB (check (A := A) x) (check y) = ⊤ ↔ PSet.Equiv x y) ∧
    (eqB (check (A := A) x) (check y) = ⊥ ↔ ¬ PSet.Equiv x y) ∧
    (memB (check (A := A) x) (check y) = ⊤ ↔ x ∈ y) ∧
    (memB (check (A := A) x) (check y) = ⊥ ↔ x ∉ y) := by
  let R : PSet.{u} × PSet.{u} → PSet.{u} × PSet.{u} → Prop :=
    InvImage measLt fun p => meas (check (A := A) p.1) (check p.2)
  have hwf : WellFounded R :=
    InvImage.wf _ (WellFounded.prod_lex wellFounded_lt
      (WellFounded.prod_lex wellFounded_lt wellFounded_lt))
  refine hwf.induction (x, y)
    (C := fun p =>
      (eqB (check (A := A) p.1) (check p.2) = ⊤ ↔ PSet.Equiv p.1 p.2) ∧
      (eqB (check (A := A) p.1) (check p.2) = ⊥ ↔ ¬ PSet.Equiv p.1 p.2) ∧
      (memB (check (A := A) p.1) (check p.2) = ⊤ ↔ p.1 ∈ p.2) ∧
      (memB (check (A := A) p.1) (check p.2) = ⊥ ↔ p.1 ∉ p.2))
    fun p ih => ?_
  rcases p with ⟨x, y⟩
  cases x with
  | mk α f =>
    cases y with
    | mk β g =>
      have ihL (i : α) :=
        ih (f i, PSet.mk β g)
          (measLt_of_rank_left (rank_child_lt (check (A := A) (PSet.mk α f)) i))
      have ihR (j : β) :=
        ih (PSet.mk α f, g j)
          (measLt_of_rank_right (rank_child_lt (check (A := A) (PSet.mk β g)) j))
      have ihS (j : β) :=
        ih (g j, PSet.mk α f)
          (measLt_of_rank_swap (rank_child_lt (check (A := A) (PSet.mk β g)) j))
      have hmemL (i : α) := (ihL i).2.2
      have hmemS (j : β) := (ihS j).2.2
      have heqR (j : β) : _ ∧ _ := ⟨(ihR j).1, (ihR j).2.1⟩
      have hI1f (i : α) :
          memB (check (A := A) (f i)) (check (PSet.mk β g)) = ⊤ ∨
          memB (check (A := A) (f i)) (check (PSet.mk β g)) = ⊥ := by
        by_cases h : f i ∈ PSet.mk β g
        · exact Or.inl ((hmemL i).1.mpr h)
        · exact Or.inr ((hmemL i).2.mpr h)
      have hI2f (j : β) :
          memB (check (A := A) (g j)) (check (PSet.mk α f)) = ⊤ ∨
          memB (check (A := A) (g j)) (check (PSet.mk α f)) = ⊥ := by
        by_cases h : g j ∈ PSet.mk α f
        · exact Or.inl ((hmemS j).1.mpr h)
        · exact Or.inr ((hmemS j).2.mpr h)
      have hEqf (j : β) :
          eqB (check (A := A) (PSet.mk α f)) (check (g j)) = ⊤ ∨
          eqB (check (A := A) (PSet.mk α f)) (check (g j)) = ⊥ := by
        by_cases h : PSet.Equiv (PSet.mk α f) (g j)
        · exact Or.inl ((heqR j).1.mpr h)
        · exact Or.inr ((heqR j).2.mpr h)
      have hequiv :
          PSet.Equiv (PSet.mk α f) (PSet.mk β g) ↔
            (∀ i, f i ∈ PSet.mk β g) ∧ ∀ j, g j ∈ PSet.mk α f := by
        rw [PSet.equiv_iff]
        refine and_congr (forall_congr' fun _ => Iff.rfl) (forall_congr' fun _ => ?_)
        exact exists_congr fun _ => PSet.Equiv.comm
      have heq_def :
          eqB (check (A := A) (PSet.mk α f)) (check (PSet.mk β g)) =
            (⨅ i, memB (check (A := A) (f i)) (check (PSet.mk β g))) ⊓
              (⨅ j, memB (check (A := A) (g j)) (check (PSet.mk α f))) := by
        rw [check_mk (A := A) α f, check_mk (A := A) β g, eqB_mk]
        simp [top_himp]
      have hmem_def :
          memB (check (A := A) (PSet.mk α f)) (check (PSet.mk β g)) =
            ⨆ j, eqB (check (A := A) (PSet.mk α f)) (check (g j)) := by
        rw [check_mk (A := A) β g, memB_mk]
        simp
      have hI1 := iInf_top_bot (fun i : α =>
          memB (check (A := A) (f i)) (check (PSet.mk β g))) hI1f
      have hI2 := iInf_top_bot (fun j : β =>
          memB (check (A := A) (g j)) (check (PSet.mk α f))) hI2f
      have hS := iSup_top_bot (fun j : β =>
          eqB (check (A := A) (PSet.mk α f)) (check (g j))) hEqf
      have hI1top :
          ((⨅ i, memB (check (A := A) (f i)) (check (PSet.mk β g))) = ⊤ ↔
            ∀ i, f i ∈ PSet.mk β g) := by
        rw [hI1.1]; exact forall_congr' fun i => (hmemL i).1
      have hI2top :
          ((⨅ j, memB (check (A := A) (g j)) (check (PSet.mk α f))) = ⊤ ↔
            ∀ j, g j ∈ PSet.mk α f) := by
        rw [hI2.1]; exact forall_congr' fun j => (hmemS j).1
      have hI1bot :
          ((⨅ i, memB (check (A := A) (f i)) (check (PSet.mk β g))) = ⊥ ↔
            ∃ i, f i ∉ PSet.mk β g) := by
        rw [hI1.2]; exact exists_congr fun i => (hmemL i).2
      have hI2bot :
          ((⨅ j, memB (check (A := A) (g j)) (check (PSet.mk α f))) = ⊥ ↔
            ∃ j, g j ∉ PSet.mk α f) := by
        rw [hI2.2]; exact exists_congr fun j => (hmemS j).2
      refine ⟨?eq_top, ?eq_bot, ?mem_top, ?mem_bot⟩
      · rw [heq_def, inf_eq_top_iff, hI1top, hI2top, hequiv]
      · constructor
        · intro hbot hE
          have htop :
              (⨅ i, memB (check (A := A) (f i)) (check (PSet.mk β g))) ⊓
                (⨅ j, memB (check (A := A) (g j)) (check (PSet.mk α f))) = ⊤ := by
            rw [inf_eq_top_iff, hI1top, hI2top]
            exact hequiv.mp (by simpa using hE)
          exact absurd (htop.symm.trans (heq_def ▸ hbot)) top_ne_bot
        · intro hne
          rw [heq_def]
          rw [hequiv, not_and_or] at hne
          rcases hne with h | h
          · rw [hI1bot.mpr (by simpa [not_forall] using h), bot_inf_eq]
          · rw [hI2bot.mpr (by simpa [not_forall] using h), inf_bot_eq]
      · rw [hmem_def, hS.1, PSet.mem_def]
        exact exists_congr fun j => (heqR j).1
      · rw [hmem_def, hS.2, PSet.mem_def, not_exists]
        exact forall_congr' fun j => (heqR j).2

/-- Boolean values of `Δ₀` formulas at check-names are two-valued and agree with `PSet`. -/
theorem d0_invariance [Nontrivial A] {n : ℕ} (φ : D0Formula n)
    (ρ : Fin n → PSet.{u}) :
    (φ.realize ρ → bval (A := A) φ (fun i => check (ρ i)) = ⊤) ∧
    (¬ φ.realize ρ → bval (A := A) φ (fun i => check (ρ i)) = ⊥) := by
  induction φ with
  | mem i j =>
    exact ⟨(check_atomic (ρ i) (ρ j)).2.2.1.mpr, (check_atomic (ρ i) (ρ j)).2.2.2.mpr⟩
  | eq i j =>
    exact ⟨(check_atomic (ρ i) (ρ j)).1.mpr, (check_atomic (ρ i) (ρ j)).2.1.mpr⟩
  | not φ ih =>
    constructor
    · intro h
      have : bval (A := A) φ (fun i => check (ρ i)) = ⊥ := (ih ρ).2 h
      rw [bval_not, this, compl_bot]
    · intro h
      have : bval (A := A) φ (fun i => check (ρ i)) = ⊤ :=
        (ih ρ).1 (Classical.not_not.mp h)
      rw [bval_not, this, compl_top]
  | and φ ψ ihφ ihψ =>
    constructor
    · intro ⟨hφ, hψ⟩
      rw [bval_and, (ihφ ρ).1 hφ, (ihψ ρ).1 hψ, top_inf_eq]
    · intro h
      rw [realize, not_and_or] at h
      rw [bval_and]
      rcases h with h | h
      · rw [(ihφ ρ).2 h, bot_inf_eq]
      · rw [(ihψ ρ).2 h, inf_bot_eq]
  | bExists k φ ih =>
    constructor
    · intro ⟨y, hymem, hy⟩
      rw [bval_bExists]
      have hmem : memB (check (A := A) y) (check (ρ k)) = ⊤ :=
        (check_atomic y (ρ k)).2.2.1.mpr hymem
      have hb : bval (A := A) φ (fun i => check (consPSet y ρ i)) = ⊤ :=
        (ih (consPSet y ρ)).1 hy
      refine top_unique (le_trans ?_
        (le_iSup (fun z : AName A =>
          (memB z (check (A := A) (ρ k)) ⊓
            bval φ (consName z fun i => check (ρ i)) : A)) (check y)))
      rw [check_cons, hmem, hb, top_inf_eq]
    · intro h
      rw [bval_bExists, iSup_eq_bot]
      intro z
      cases hk : ρ k with
      | mk β g =>
        have hk' : ρ k = PSet.mk β g := hk
        rw [check_mk, memB_mk, inf_comm, inf_iSup_eq]
        refine iSup_eq_bot.mpr fun j => ?_
        simp only [inf_top_eq]
        have hsubst := bval_subst (A := A) φ z (check (g j)) (fun i => check (ρ i))
        have hmemg : g j ∈ ρ k := by
          rw [hk']; exact PSet.Mem.mk g j
        have hbot : bval (A := A) φ (fun i => check (consPSet (g j) ρ i)) = ⊥ :=
          (ih (consPSet (g j) ρ)).2 (fun hφ => h ⟨g j, hmemg, hφ⟩)
        rw [check_cons] at hsubst
        rw [inf_comm]
        exact eq_bot_iff.mpr (hsubst.trans hbot.le)
  | bForall k φ ih =>
    constructor
    · intro h
      rw [bval_bForall]
      refine iInf_eq_top.mpr fun z => himp_eq_top_iff.mpr ?_
      cases hk : ρ k with
      | mk β g =>
        have hk' : ρ k = PSet.mk β g := hk
        rw [check_mk, memB_mk]
        simp only [inf_top_eq]
        refine iSup_le fun j => ?_
        have hmemg : g j ∈ ρ k := by
          rw [hk']; exact PSet.Mem.mk g j
        have htop : bval (A := A) φ (fun i => check (consPSet (g j) ρ i)) = ⊤ :=
          (ih (consPSet (g j) ρ)).1 (h (g j) hmemg)
        have hsubst := bval_subst (A := A) φ (check (g j)) z (fun i => check (ρ i))
        rw [check_cons, htop, inf_top_eq, eqB_comm] at hsubst
        exact hsubst
    · intro h
      rw [realize, not_forall] at h
      obtain ⟨y, hy⟩ := h
      have hymem : y ∈ ρ k := (Classical.not_imp.mp hy).1
      have hn : ¬ φ.realize (consPSet y ρ) := (Classical.not_imp.mp hy).2
      have hbot : bval (A := A) φ (fun i => check (consPSet y ρ i)) = ⊥ :=
        (ih (consPSet y ρ)).2 hn
      have hmem : memB (check (A := A) y) (check (ρ k)) = ⊤ :=
        (check_atomic y (ρ k)).2.2.1.mpr hymem
      rw [bval_bForall]
      refine bot_unique ((iInf_le (fun z : AName A =>
          memB z (check (A := A) (ρ k)) ⇨
            bval φ (consName z fun i => check (ρ i))) (check y)).trans ?_)
      rw [check_cons, hmem, hbot, top_himp]

/-- Jech Lemma 14.21 / CSL Theorem 2: `Δ₀` invariance. -/
theorem jech_lemma_14_21 [Nontrivial A] {n : ℕ} (φ : D0Formula n)
    (ρ : Fin n → PSet.{u}) :
    φ.realize ρ ↔ bval (A := A) φ (fun i => check (ρ i)) = ⊤ := by
  constructor
  · exact (d0_invariance φ ρ).1
  · intro htop
    by_contra h
    have : bval (A := A) φ (fun i => check (ρ i)) = ⊥ := (d0_invariance φ ρ).2 h
    exact absurd (htop.symm.trans this) top_ne_bot

/-!
## Internal set constructions (CSL 2026, §2 after Theorem 1)
-/

/-- Membership is downward closed under Boolean inclusion. -/
theorem memB_of_subsetB (z x y : AName.{u} A) :
    memB z x ⊓ subsetB x y ≤ memB z y := by
  rw [memB_eq (x := z) (y := x), iSup_inf_eq]
  refine iSup_le fun i => ?_
  have hval : x.val i ⊓ subsetB x y ≤ memB (x.child i) y := by
    rw [inf_comm]; exact subsetB_apply x y i
  have hsub : eqB z (x.child i) ⊓ memB (x.child i) y ≤ memB z y := by
    rw [eqB_comm (x := z) (y := x.child i), inf_comm]
    exact memB_eqB_left (x.child i) y z
  refine le_trans ?_ hsub
  refine le_inf ?_ ?_
  · exact inf_le_of_left_le inf_le_left
  · refine le_trans ?_ hval
    exact le_inf (inf_le_of_left_le inf_le_right) inf_le_right

/-- Boolean inclusion is transitive. -/
theorem AName.subsetB_trans (x y z : AName.{u} A) :
    subsetB x y ⊓ subsetB y z ≤ subsetB x z := by
  refine le_iInf fun i => ?_
  rw [le_himp_iff]
  have hxy : subsetB x y ⊓ x.val i ≤ memB (x.child i) y := subsetB_apply x y i
  refine le_trans ?_ (memB_of_subsetB (x.child i) y z)
  refine le_inf ?_ ?_
  · exact hxy.trans' (le_inf (inf_le_of_left_le inf_le_left) inf_le_right)
  · exact inf_le_of_left_le inf_le_right

theorem memB_singletonB (z x : AName.{u} A) :
    memB z (singletonB x) = eqB z x := by
  rw [singletonB, memB_mk, iSup_unique (α := A) (ι := PUnit.{u + 1}), inf_top_eq]

theorem iSup_ulift_bool (f : ULift.{u} Bool → A) :
    (⨆ b, f b) = f ⟨true⟩ ⊔ f ⟨false⟩ :=
  le_antisymm
    (iSup_le fun b => by
      rcases b with ⟨b⟩
      cases b with
      | false => exact le_sup_right
      | true => exact le_sup_left)
    (sup_le (le_iSup f ⟨true⟩) (le_iSup f ⟨false⟩))

theorem memB_pairB (z x y : AName.{u} A) :
    memB z (pairB x y) = eqB z x ⊔ eqB z y := by
  unfold pairB
  rw [memB_mk, iSup_ulift_bool]
  simp

theorem iSup_option {β : Type u} (f : Option β → A) :
    (⨆ o, f o) = f none ⊔ ⨆ i, f (some i) :=
  le_antisymm
    (iSup_le fun o =>
      match o with
      | none => le_sup_left
      | some i => le_sup_of_le_right (le_iSup (fun j => f (some j)) i))
    (sup_le (le_iSup f none) (iSup_le fun i => le_iSup f (some i)))

theorem memB_insertB (z x y : AName.{u} A) :
    memB z (insertB x y) = eqB z x ⊔ memB z y := by
  unfold insertB
  rw [memB_mk, iSup_option, memB_eq]
  simp

end Scott2026
