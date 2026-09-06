/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/

import Scott2026.Lemma31

/-!
# Corollary 34: check/VA numerals on the Theorem 30 carrier

Furber–Mardare–Panangaden–Scott, CSL 2026, Corollary 34. The paper says
the Engeler model in `V^A` (Theorem 30) is a reflexive continuous lattice
with numerals, given check of the Church Booleans and numerals, with the
whole statement interpreted in `V^A`.

The internal `≪` / continuous-lattice language (subset order) lives in
`InternalDomain.lean`. The Lean name remains `corollary_34_check`, not
`corollary_34`: the paper type still needs `isContinuousLatticeSubsetB
(powerB (check ω)) = ⊤`. Internal `≪ ↔` finite `⊆` is
`wayBelowSubsetB_eq_finite_subset`.

Proof sketch (vision ll.786–788):
* Lemma 31: `‖⟦check M⟧^A = check(⟦M⟧)‖ = 1` for closed Church `⊤`, `⊥`,
  `c_n`.
* Definition 32(i) is `Δ₀` (`¬ x = y`), so Theorem 2 (`jech_lemma_14_21`)
  applied to Proposition 33’s ground distinctness.
* Parts (ii)–(iv) transfer by `interpClosedVA_sound_full` /
  `theorem_26_sound_full` (`[Infinite Var]`, `ℕ`). Example 24
  (`example_24_subset`) places those `λ`-equations in `check(λ) ⊆ λ^A`.
-/

universe u

namespace Scott2026

open AName
open Classical

variable {A : Type u} [CompleteBooleanAlgebra A]

noncomputable section

/-!
## Boolean-equality transport
-/

theorem eqB_top_congr_left {x x' y : AName.{u} A} (h : eqB x x' = ⊤) :
    eqB x y = eqB x' y := by
  refine le_antisymm ?le ?ge
  · have htr := eqB_trans x' x y
    rw [eqB_comm (x := x') (y := x), h, top_inf_eq] at htr
    exact htr
  · have htr := eqB_trans x x' y
    rw [h, top_inf_eq] at htr
    exact htr

theorem eqB_top_congr_right {x y y' : AName.{u} A} (h : eqB y y' = ⊤) :
    eqB x y = eqB x y' := by
  rw [eqB_comm x y, eqB_comm x y', eqB_top_congr_left h]

theorem eqB_top_congr {x x' y y' : AName.{u} A}
    (hx : eqB x x' = ⊤) (hy : eqB y y' = ⊤) :
    eqB x y = eqB x' y' := by
  rw [eqB_top_congr_left hx, eqB_top_congr_right hy]

/-!
## Check/VA commutation (Lemma 31 on Church terms)
-/

variable {Var : Type*} [DecidableEq Var]

/-- Lemma 31, closed case, specialized to a closed term. -/
theorem lemma_31_closed_term (M : Lam Var) (hcl : M.fv = ∅) :
    eqB (childΩ (interpClosedVA (A := A) M))
      (childΩ (setToCanonical (interpClosed
        (engelerReflexiveDcpo engelerPair engelerPair_injective) M))) = ⊤ :=
  lemma_31_closed (A := A) M hcl

/-- Strictness of the canonical carrier upgrades Lemma 31’s `eqB = ⊤` to
index equality `interpClosedVA M = setToCanonical ⟦M⟧`. -/
theorem interpClosedVA_eq_setToCanonical (M : Lam Var) (hcl : M.fv = ∅) :
    interpClosedVA (A := A) M =
      setToCanonical (interpClosed
        (engelerReflexiveDcpo engelerPair engelerPair_injective) M) := by
  refine (canonicalPowerSetoid_isStrict (check (A := A) PSet.omega))
    (interpClosedVA (A := A) M)
    (setToCanonical (interpClosed
      (engelerReflexiveDcpo engelerPair engelerPair_injective) M)) ?_
  rw [canonicalPowerSetoid_eq, oid_eq_powerB]
  exact lemma_31_closed (A := A) M hcl

theorem lemma_31_closed_churchTrue :
    eqB (childΩ (interpClosedVA (A := A) churchTrue))
      (childΩ (setToCanonical (interpClosed
        (engelerReflexiveDcpo engelerPair engelerPair_injective)
        churchTrue))) = ⊤ :=
  lemma_31_closed (A := A) churchTrue churchTrue_fv

theorem lemma_31_closed_churchFalse :
    eqB (childΩ (interpClosedVA (A := A) churchFalse))
      (childΩ (setToCanonical (interpClosed
        (engelerReflexiveDcpo engelerPair engelerPair_injective)
        churchFalse))) = ⊤ :=
  lemma_31_closed (A := A) churchFalse churchFalse_fv

theorem lemma_31_closed_churchNum (n : ℕ) :
    eqB (childΩ (interpClosedVA (A := A) (churchNum n)))
      (childΩ (setToCanonical (interpClosed
        (engelerReflexiveDcpo engelerPair engelerPair_injective)
        (churchNum n)))) = ⊤ :=
  lemma_31_closed (A := A) (churchNum n) (churchNum_fv n)

theorem lemma_31_closed_churchTrueN :
    eqB (childΩ (interpClosedVA (A := A) churchTrueN))
      (childΩ (setToCanonical (interpClosed
        (engelerReflexiveDcpo engelerPair engelerPair_injective)
        churchTrueN))) = ⊤ :=
  lemma_31_closed (A := A) churchTrueN churchTrueN_fv

theorem lemma_31_closed_churchFalseN :
    eqB (childΩ (interpClosedVA (A := A) churchFalseN))
      (childΩ (setToCanonical (interpClosed
        (engelerReflexiveDcpo engelerPair engelerPair_injective)
        churchFalseN))) = ⊤ :=
  lemma_31_closed (A := A) churchFalseN churchFalseN_fv

theorem lemma_31_closed_churchNumN (n : ℕ) :
    eqB (childΩ (interpClosedVA (A := A) (churchNumN n)))
      (childΩ (setToCanonical (interpClosed
        (engelerReflexiveDcpo engelerPair engelerPair_injective)
        (churchNumN n)))) = ⊤ :=
  lemma_31_closed (A := A) (churchNumN n) (churchNumN_fv n)

theorem interpClosedVA_churchTrue :
    interpClosedVA (A := A) churchTrue =
      setToCanonical (interpClosed
        (engelerReflexiveDcpo engelerPair engelerPair_injective)
        churchTrue) :=
  interpClosedVA_eq_setToCanonical (A := A) churchTrue churchTrue_fv

theorem interpClosedVA_churchFalse :
    interpClosedVA (A := A) churchFalse =
      setToCanonical (interpClosed
        (engelerReflexiveDcpo engelerPair engelerPair_injective)
        churchFalse) :=
  interpClosedVA_eq_setToCanonical (A := A) churchFalse churchFalse_fv

theorem interpClosedVA_churchNum (n : ℕ) :
    interpClosedVA (A := A) (churchNum n) =
      setToCanonical (interpClosed
        (engelerReflexiveDcpo engelerPair engelerPair_injective)
        (churchNum n)) :=
  interpClosedVA_eq_setToCanonical (A := A) (churchNum n) (churchNum_fv n)

theorem interpClosedVA_churchTrueN :
    interpClosedVA (A := A) churchTrueN =
      setToCanonical (interpClosed
        (engelerReflexiveDcpo engelerPair engelerPair_injective)
        churchTrueN) :=
  interpClosedVA_eq_setToCanonical (A := A) churchTrueN churchTrueN_fv

theorem interpClosedVA_churchFalseN :
    interpClosedVA (A := A) churchFalseN =
      setToCanonical (interpClosed
        (engelerReflexiveDcpo engelerPair engelerPair_injective)
        churchFalseN) :=
  interpClosedVA_eq_setToCanonical (A := A) churchFalseN churchFalseN_fv

theorem interpClosedVA_churchNumN (n : ℕ) :
    interpClosedVA (A := A) (churchNumN n) =
      setToCanonical (interpClosed
        (engelerReflexiveDcpo engelerPair engelerPair_injective)
        (churchNumN n)) :=
  interpClosedVA_eq_setToCanonical (A := A) (churchNumN n) (churchNumN_fv n)

theorem setToCanonical_injective [Nontrivial A] :
    Function.Injective (setToCanonical (A := A)) := by
  intro S T hST
  ext n
  have hmem : memOfNat (A := A) (setToCanonical S) n =
      memOfNat (setToCanonical T) n := by rw [hST]
  rw [memOfNat_setToCanonical, memOfNat_setToCanonical] at hmem
  by_cases hS : n ∈ S
  · rw [if_pos hS] at hmem
    by_cases hT : n ∈ T
    · exact iff_of_true hS hT
    · rw [if_neg hT] at hmem
      exact (top_ne_bot hmem).elim
  · rw [if_neg hS] at hmem
    by_cases hT : n ∈ T
    · rw [if_pos hT] at hmem
      exact (bot_ne_top hmem).elim
    · exact iff_of_false hS hT

/-!
## Definition 32(i) as a `Δ₀` statement (Theorem 2)
-/

/-- Ground Church Booleans remain distinct as `setPSet` pre-sets. -/
theorem churchTrue_interp_setPSet_not_equiv :
    ¬ PSet.Equiv.{u, u}
        (setPSet (interpClosed
          (engelerReflexiveDcpo engelerPair engelerPair_injective)
          churchTrue))
        (setPSet (interpClosed
          (engelerReflexiveDcpo engelerPair engelerPair_injective)
          churchFalse)) :=
  setPSet_not_equiv_of_ne
    (churchTrue_interp_ne_churchFalse engelerPair engelerPair_injective)

/-- Assignment for the `Δ₀` formula `¬ x₀ = x₁`. -/
def setPSetAssign (S T : Set ℕ) : Fin 2 → PSet.{u} :=
  D0Formula.consPSet (setPSet S) (fun _ : Fin 1 => setPSet T)

theorem setPSetAssign_zero (S T : Set ℕ) :
    setPSetAssign S T 0 = setPSet S :=
  D0Formula.consPSet_zero _ _

theorem setPSetAssign_one (S T : Set ℕ) :
    setPSetAssign S T 1 = setPSet T := by
  change D0Formula.consPSet (setPSet S) (fun _ : Fin 1 => setPSet T) 1 =
    setPSet T
  rw [show (1 : Fin 2) = Fin.succ 0 from rfl]
  exact D0Formula.consPSet_succ (setPSet S) (fun _ : Fin 1 => setPSet T) 0

/-- Theorem 2 on `¬ x = y`: inequivalent ground sets have
`‖check(setPSet S) = check(setPSet T)‖ = 0`. `Subsingleton A` collapses
`⊤ = ⊥`. -/
theorem eqB_check_setPSet_of_ne {S T : Set ℕ} (hne : S ≠ T) :
    eqB (check (A := A) (setPSet S)) (check (setPSet T)) = ⊥ := by
  rcases subsingleton_or_nontrivial A with hA | hA
  · exact Subsingleton.elim _ _
  · have : Nontrivial A := hA
    let φ : D0Formula 2 := D0Formula.not (D0Formula.eq 0 1)
    have hreal : φ.realize (setPSetAssign S T) := by
      change ¬ PSet.Equiv (setPSetAssign S T 0) (setPSetAssign S T 1)
      rw [setPSetAssign_zero, setPSetAssign_one]
      exact setPSet_not_equiv_of_ne hne
    have htop : D0Formula.bval (A := A) φ
        (fun i => check (setPSetAssign S T i)) = ⊤ :=
      (jech_lemma_14_21 (A := A) φ (setPSetAssign S T)).mp hreal
    have hcompl :
        (eqB (check (A := A) (setPSetAssign S T 0))
          (check (setPSetAssign S T 1)))ᶜ = ⊤ := htop
    rw [setPSetAssign_zero S T, setPSetAssign_one S T] at hcompl
    rw [← compl_compl (eqB (check (A := A) (setPSet S)) (check (setPSet T))),
      hcompl, compl_top]

theorem eqB_check_setPSet_churchTrue_churchFalse :
    eqB (check (A := A)
        (setPSet (interpClosed
          (engelerReflexiveDcpo engelerPair engelerPair_injective)
          churchTrue)))
      (check (setPSet (interpClosed
          (engelerReflexiveDcpo engelerPair engelerPair_injective)
          churchFalse))) = ⊥ :=
  eqB_check_setPSet_of_ne (A := A)
    (churchTrue_interp_ne_churchFalse engelerPair engelerPair_injective)

/-- Transport Lemma 31 and `eqB_setToCanonical` through the `Δ₀` fact. -/
theorem eqB_interpClosedVA_churchTrue_churchFalse :
    eqB (childΩ (interpClosedVA (A := A) churchTrue))
      (childΩ (interpClosedVA churchFalse)) = ⊥ := by
  have hT := lemma_31_closed_churchTrue (A := A)
  have hF := lemma_31_closed_churchFalse (A := A)
  have hTc := eqB_setToCanonical (A := A)
    (interpClosed (engelerReflexiveDcpo engelerPair engelerPair_injective)
      churchTrue)
  have hFc := eqB_setToCanonical (A := A)
    (interpClosed (engelerReflexiveDcpo engelerPair engelerPair_injective)
      churchFalse)
  have hbot := eqB_check_setPSet_churchTrue_churchFalse (A := A)
  rw [eqB_top_congr hT hF, eqB_top_congr hTc hFc]
  exact hbot

/-- Under `Subsingleton A` every Boolean value collapses, so numeral
`eqB` never separates `n` from `m`. Injectivity therefore needs
`Nontrivial A`. -/
theorem eqB_interpClosedVA_churchNum_subsingleton [Subsingleton A]
    (n m : ℕ) :
    eqB (childΩ (interpClosedVA (A := A) (churchNum n)))
      (childΩ (interpClosedVA (churchNum m))) = ⊤ :=
  Subsingleton.elim _ _

/-- Check/VA numeral injectivity: `‖⟦c_n⟧^A = ⟦c_m⟧^A‖ = 1` implies
`n = m`, via Lemma 31 and `churchNum_interp_injective`. -/
theorem churchNum_interpClosedVA_injective [Nontrivial A] {n m : ℕ}
    (h : eqB (childΩ (interpClosedVA (A := A) (churchNum n)))
      (childΩ (interpClosedVA (churchNum m))) = ⊤) : n = m := by
  have hn := lemma_31_closed_churchNum (A := A) n
  have hm := lemma_31_closed_churchNum (A := A) m
  have hcn := eqB_setToCanonical (A := A)
    (interpClosed (engelerReflexiveDcpo engelerPair engelerPair_injective)
      (churchNum n))
  have hcm := eqB_setToCanonical (A := A)
    (interpClosed (engelerReflexiveDcpo engelerPair engelerPair_injective)
      (churchNum m))
  have hground : eqB
      (check (A := A) (setPSet (interpClosed
        (engelerReflexiveDcpo engelerPair engelerPair_injective)
        (churchNum n))))
      (check (setPSet (interpClosed
        (engelerReflexiveDcpo engelerPair engelerPair_injective)
        (churchNum m)))) = ⊤ := by
    rwa [eqB_top_congr hn hm, eqB_top_congr hcn hcm] at h
  have hequiv :
      PSet.Equiv
        (setPSet (interpClosed
          (engelerReflexiveDcpo engelerPair engelerPair_injective)
          (churchNum n)))
        (setPSet (interpClosed
          (engelerReflexiveDcpo engelerPair engelerPair_injective)
          (churchNum m))) :=
    (check_atomic (A := A)
      (setPSet (interpClosed
        (engelerReflexiveDcpo engelerPair engelerPair_injective)
        (churchNum n)))
      (setPSet (interpClosed
        (engelerReflexiveDcpo engelerPair engelerPair_injective)
        (churchNum m)))).1.mp hground
  have hsets :
      interpClosed (engelerReflexiveDcpo engelerPair engelerPair_injective)
          (churchNum n) =
        interpClosed (engelerReflexiveDcpo engelerPair engelerPair_injective)
          (churchNum m) :=
    setPSet_equiv_iff.mp hequiv
  exact churchNum_interp_injective engelerPair engelerPair_injective hsets

/-!
## Definition 32(ii)–(iv) on the Theorem 30 carrier

Do not re-prove `definition_32`. Transfer the `LamEq` identities by
`interpClosedVA_sound_full` / `theorem_26_sound_full`. The same identities
lie in `check(λ) ⊆ λ^A` by Example 24 (`example_24_subset`).
-/

theorem interpClosedVA_churchIfN_true (M N : Lam ℕ) :
    interpClosedVA (A := A) (((churchIfN.app churchTrueN).app M).app N) =
      interpClosedVA M :=
  interpClosedVA_sound_full (A := A) (churchIfN_true M N)

theorem interpClosedVA_churchIfN_false (M N : Lam ℕ) :
    interpClosedVA (A := A) (((churchIfN.app churchFalseN).app M).app N) =
      interpClosedVA N :=
  interpClosedVA_sound_full (A := A) (churchIfN_false M N)

theorem interpClosedVA_churchSucc (n : ℕ) :
    interpClosedVA (A := A) (churchSucc.app (churchNumN n)) =
      interpClosedVA (churchNumN (n + 1)) :=
  interpClosedVA_sound_full (A := A) (churchSucc_num n)

theorem interpClosedVA_churchPred_succ (n : ℕ) :
    interpClosedVA (A := A) (churchPred.app (churchNumN (n + 1))) =
      interpClosedVA (churchNumN n) :=
  interpClosedVA_sound_full (A := A) (churchPred_succ n)

theorem interpClosedVA_churchPred_zero :
    interpClosedVA (A := A) (churchPred.app (churchNumN 0)) =
      interpClosedVA (churchNumN 0) :=
  interpClosedVA_sound_full (A := A) churchPred_zero

theorem interpClosedVA_churchIsZero_zero :
    interpClosedVA (A := A) (churchIsZero.app (churchNumN 0)) =
      interpClosedVA churchTrueN :=
  interpClosedVA_sound_full (A := A) churchIsZero_zero

theorem interpClosedVA_churchIsZero_succ (n : ℕ) :
    interpClosedVA (A := A) (churchIsZero.app (churchNumN (n + 1))) =
      interpClosedVA churchFalseN :=
  interpClosedVA_sound_full (A := A) (churchIsZero_succ n)

/-- Definition 32(ii)–(iv) as equalities of `interpClosedVA`. -/
theorem definition_32_interpClosedVA :
    (∀ M N : Lam ℕ,
      interpClosedVA (A := A) (((churchIfN.app churchTrueN).app M).app N) =
        interpClosedVA M) ∧
    (∀ M N : Lam ℕ,
      interpClosedVA (A := A) (((churchIfN.app churchFalseN).app M).app N) =
        interpClosedVA N) ∧
    (∀ n, interpClosedVA (A := A) (churchSucc.app (churchNumN n)) =
      interpClosedVA (churchNumN (n + 1))) ∧
    (∀ n, interpClosedVA (A := A) (churchPred.app (churchNumN (n + 1))) =
      interpClosedVA (churchNumN n)) ∧
    interpClosedVA (A := A) (churchPred.app (churchNumN 0)) =
      interpClosedVA (churchNumN 0) ∧
    interpClosedVA (A := A) (churchIsZero.app (churchNumN 0)) =
      interpClosedVA churchTrueN ∧
    (∀ n, interpClosedVA (A := A) (churchIsZero.app (churchNumN (n + 1))) =
      interpClosedVA churchFalseN) :=
  ⟨interpClosedVA_churchIfN_true (A := A),
    interpClosedVA_churchIfN_false (A := A),
    interpClosedVA_churchSucc (A := A),
    interpClosedVA_churchPred_succ (A := A),
    interpClosedVA_churchPred_zero (A := A),
    interpClosedVA_churchIsZero_zero (A := A),
    interpClosedVA_churchIsZero_succ (A := A)⟩

/-- Corollary 34, check/VA fragment. Not named `corollary_34`: that paper
name is the internal statement “`P^A(check E)` is a reflexive continuous
lattice with numerals”. The numerals half is here; the continuous-lattice
clause needs `isContinuousLatticeSubsetB (powerB (check ω)) = ⊤`. -/
theorem corollary_34_check :
    (interpClosedVA (A := A) churchTrue =
      setToCanonical (interpClosed
        (engelerReflexiveDcpo engelerPair engelerPair_injective)
        churchTrue)) ∧
    (interpClosedVA (A := A) churchFalse =
      setToCanonical (interpClosed
        (engelerReflexiveDcpo engelerPair engelerPair_injective)
        churchFalse)) ∧
    (∀ n, interpClosedVA (A := A) (churchNum n) =
      setToCanonical (interpClosed
        (engelerReflexiveDcpo engelerPair engelerPair_injective)
        (churchNum n))) ∧
    (eqB (childΩ (interpClosedVA (A := A) churchTrue))
      (childΩ (interpClosedVA churchFalse)) = ⊥) ∧
    (Nontrivial A →
      ∀ n m, eqB (childΩ (interpClosedVA (A := A) (churchNum n)))
          (childΩ (interpClosedVA (churchNum m))) = ⊤ → n = m) ∧
    (∀ M N : Lam ℕ,
      interpClosedVA (A := A) (((churchIfN.app churchTrueN).app M).app N) =
        interpClosedVA M) ∧
    (∀ M N : Lam ℕ,
      interpClosedVA (A := A) (((churchIfN.app churchFalseN).app M).app N) =
        interpClosedVA N) ∧
    (∀ n, interpClosedVA (A := A) (churchSucc.app (churchNumN n)) =
      interpClosedVA (churchNumN (n + 1))) ∧
    (∀ n, interpClosedVA (A := A) (churchPred.app (churchNumN (n + 1))) =
      interpClosedVA (churchNumN n)) ∧
    interpClosedVA (A := A) (churchPred.app (churchNumN 0)) =
      interpClosedVA (churchNumN 0) ∧
    interpClosedVA (A := A) (churchIsZero.app (churchNumN 0)) =
      interpClosedVA churchTrueN ∧
    (∀ n, interpClosedVA (A := A) (churchIsZero.app (churchNumN (n + 1))) =
      interpClosedVA churchFalseN) :=
  ⟨interpClosedVA_churchTrue (A := A),
    interpClosedVA_churchFalse (A := A),
    interpClosedVA_churchNum (A := A),
    eqB_interpClosedVA_churchTrue_churchFalse (A := A),
    fun hA n m h =>
      haveI : Nontrivial A := hA
      churchNum_interpClosedVA_injective (A := A) (n := n) (m := m) h,
    interpClosedVA_churchIfN_true (A := A),
    interpClosedVA_churchIfN_false (A := A),
    interpClosedVA_churchSucc (A := A),
    interpClosedVA_churchPred_succ (A := A),
    interpClosedVA_churchPred_zero (A := A),
    interpClosedVA_churchIsZero_zero (A := A),
    interpClosedVA_churchIsZero_succ (A := A)⟩

end

end Scott2026
