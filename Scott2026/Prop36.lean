/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/

import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Nat.Pairing
import Scott2026.Interp
import Scott2026.Lemma35General

-- `Lemma35General` pulls in Scott 1972 `specializationPreorder`, which
-- diamonds with `ENNReal`'s order in `Coin`. Keep the lattice/order
-- instances of later modules (measure theory) as Mathlib's.
attribute [-instance] Scott1972.ContinuousLattice.specializationPreorder

/-!
# Proposition 36: many-one comparison via a numeral-to-numeral combinator

Furber–Mardare–Panangaden–Scott, CSL 2026, Proposition 36.
`proposition_36_of` is the paper type on an arbitrary reflexive
continuous lattice with Church numerals (`churchWithNumerals`).
Engeler `proposition_36` remains the special case, also recovered as
`proposition_36_via_general`.

Paper (i) and (ii) are equivalent: a closed `M` that sends Church
numerals to Church numerals (`MapsNumerals`) reduces `S₁` to `S₂` at
some pair of `χ`-oracles iff it does so at every such pair.

`ManyOneLe` remains the algebraic predicate (any `f : ℕ → ℕ`, no
λ-term). Paper (i) implies `ManyOneLe`; the converse would require a
closed λ-term for `f`, which is false for a general `f`
(`exists_nat_fun_not_lambda_definable`).
-/

open Set Function Classical

namespace Scott2026

noncomputable section

/-!
## Numeral-to-numeral combinators

Church `Fin 2`/`ℕ` closed-interpretation agreement lives in
`Lemma35General` (`churchNum_interpClosed_eq_churchNumN`).
-/

/-- Closed `M` sending each Church numeral to a Church numeral. -/
def MapsNumerals (M : Lam ℕ) : Prop :=
  M.fv = ∅ ∧ ∀ n, ∃ m, LamEq (M.app (churchNumN n)) (churchNumN m)

theorem churchSucc_mapsNumerals : MapsNumerals churchSucc :=
  ⟨churchSucc_fv, fun n => ⟨n + 1, churchSucc_num n⟩⟩

theorem churchPred_mapsNumerals : MapsNumerals churchPred :=
  ⟨churchPred_fv, fun n =>
    match n with
    | 0 => ⟨0, churchPred_zero⟩
    | n + 1 => ⟨n, churchPred_succ n⟩⟩

/-- `λ ⊢ c_n = c_m` implies `n = m`, via soundness, Fin2/ℕ alignment, and
`numeral_inj` (`churchNum_interp_injective`). -/
theorem churchNumN_lamEq_injective {n m : ℕ}
    (h : LamEq (churchNumN n) (churchNumN m)) : n = m := by
  have himg :
      interpClosed engelerWithNumerals.toReflexiveDcpo (churchNumN n) =
        interpClosed engelerWithNumerals.toReflexiveDcpo (churchNumN m) :=
    interpClosed_sound_full engelerWithNumerals.toReflexiveDcpo h
  have hnum : engelerWithNumerals.numeral n = engelerWithNumerals.numeral m := by
    rw [numeral_eq_interpClosed_churchNumN, numeral_eq_interpClosed_churchNumN, himg]
  exact engelerWithNumerals.numeral_inj hnum

/-- Domain-general injectivity of Church numerals under `LamEq`, via
`m?` (`numeral_inj_of_churchTest`). -/
theorem churchNumN_lamEq_injective_of {D : Type*} [CompleteLattice D]
    (R : ReflexiveDcpo D)
    (hbool : interpClosed R churchTrueN ≠ interpClosed R churchFalseN)
    {n m : ℕ} (h : LamEq (churchNumN n) (churchNumN m)) : n = m :=
  numeral_inj_of_churchTest R hbool (interpClosed_sound_full R h)

theorem mapsNumerals_unique {M : Lam ℕ} (_hM : MapsNumerals M) {n m m' : ℕ}
    (hm : LamEq (M.app (churchNumN n)) (churchNumN m))
    (hm' : LamEq (M.app (churchNumN n)) (churchNumN m')) : m = m' :=
  churchNumN_lamEq_injective (hm.symm.trans hm')

/-- Classically extracted reduction `f` of a `MapsNumerals` witness. -/
def mapsNumeralsFun (M : Lam ℕ) (hM : MapsNumerals M) : ℕ → ℕ :=
  fun n => Classical.choose (hM.2 n)

theorem mapsNumeralsFun_spec (M : Lam ℕ) (hM : MapsNumerals M) (n : ℕ) :
    LamEq (M.app (churchNumN n)) (churchNumN (mapsNumeralsFun M hM n)) :=
  Classical.choose_spec (hM.2 n)

theorem mapsNumeralsFun_unique {M : Lam ℕ} (hM : MapsNumerals M) {n m : ℕ}
    (hm : LamEq (M.app (churchNumN n)) (churchNumN m)) :
    mapsNumeralsFun M hM n = m :=
  mapsNumerals_unique hM (mapsNumeralsFun_spec M hM n) hm

theorem mapsNumerals_interp_numeral {M : Lam ℕ} (hM : MapsNumerals M) (n : ℕ) :
    interpClosed engelerWithNumerals.toReflexiveDcpo (M.app (churchNumN n)) =
      engelerWithNumerals.numeral (mapsNumeralsFun M hM n) := by
  rw [interpClosed_sound_full engelerWithNumerals.toReflexiveDcpo
      (mapsNumeralsFun_spec M hM n), numeral_eq_interpClosed_churchNumN]

theorem mapsNumerals_interp_numeral_of {D : Type*} [CompleteLattice D]
    (R : ReflexiveDcpo D) {M : Lam ℕ} (hM : MapsNumerals M) (n : ℕ) :
    interpClosed R (M.app (churchNumN n)) =
      interpClosed R (churchNumN (mapsNumeralsFun M hM n)) :=
  interpClosed_sound_full R (mapsNumeralsFun_spec M hM n)

/-!
## Oracles (reuse Lemma 35(ii) on Engeler)

`Interp.gbar` / `numeralFingerprint` / `lemma_35_ii` supply a
Scott-continuous extension of `χ_S`. Do not redeclare `gbar`.
-/

/-- Oracle for `S`: `lam` of the Scott-continuous extension `gbar S`. -/
noncomputable def chiOracle (S : Set ℕ) : Set ℕ :=
  engelerWithNumerals.lam (gbar S)

theorem chiOracle_spec (S : Set ℕ) (n : ℕ) :
    engelerWithNumerals.app (chiOracle S) (engelerWithNumerals.numeral n) =
      chiNum engelerWithNumerals S n :=
  lemma_35_ii_of_extension engelerWithNumerals S (gbar S)
    (gbar_scottContinuous S) (gbar_numeral S) n

/-!
## Characteristic values
-/

theorem chiNum_eq_iff {D : Type*} [CompleteLattice D]
    (R : ReflexiveDcpoWithNumerals D) (S T : Set ℕ) (n m : ℕ) :
    chiNum R S n = chiNum R T m ↔ (n ∈ S ↔ m ∈ T) := by
  simp only [chiNum]
  by_cases hn : n ∈ S
  · by_cases hm : m ∈ T
    · simp [hn, hm]
    · rw [if_pos hn, if_neg hm]
      exact iff_of_false R.bool_ne.symm (fun hiff => hm (hiff.mp hn))
  · by_cases hm : m ∈ T
    · rw [if_neg hn, if_pos hm]
      exact iff_of_false R.bool_ne (fun hiff => hn (hiff.mpr hm))
    · simp [hn, hm]

/-!
## Proposition 36 (paper type on `engelerWithNumerals`)
-/

/-- An oracle for `S` represents `χ_S` on numerals. -/
def IsOracle {D : Type*} [CompleteLattice D]
    (R : ReflexiveDcpoWithNumerals D) (d : D) (S : Set ℕ) : Prop :=
  ∀ n, R.app d (R.numeral n) = chiNum R S n

theorem chiOracle_isOracle (S : Set ℕ) :
    IsOracle engelerWithNumerals (chiOracle S) S :=
  chiOracle_spec S

/-- Proposition 36(i): some closed numeral-to-numeral `M` and some oracles. -/
def proposition_36_i (S₁ S₂ : Set ℕ) : Prop :=
  ∃ M : Lam ℕ, MapsNumerals M ∧
    ∃ d₁ d₂ : Set ℕ,
      IsOracle engelerWithNumerals d₁ S₁ ∧
      IsOracle engelerWithNumerals d₂ S₂ ∧
      ∀ n, engelerWithNumerals.app d₂
          (interpClosed engelerWithNumerals.toReflexiveDcpo (M.app (churchNumN n))) =
        engelerWithNumerals.app d₁ (engelerWithNumerals.numeral n)

/-- Proposition 36(ii): some closed numeral-to-numeral `M`, for every oracle pair. -/
def proposition_36_ii (S₁ S₂ : Set ℕ) : Prop :=
  ∃ M : Lam ℕ, MapsNumerals M ∧
    ∀ d₁ d₂ : Set ℕ,
      IsOracle engelerWithNumerals d₁ S₁ →
      IsOracle engelerWithNumerals d₂ S₂ →
      ∀ n, engelerWithNumerals.app d₂
          (interpClosed engelerWithNumerals.toReflexiveDcpo (M.app (churchNumN n))) =
        engelerWithNumerals.app d₁ (engelerWithNumerals.numeral n)

theorem proposition_36_ii_of_i {S₁ S₂ : Set ℕ} (h : proposition_36_i S₁ S₂) :
    proposition_36_ii S₁ S₂ := by
  obtain ⟨M, hM, d₁, d₂, hd₁, hd₂, hagree⟩ := h
  refine ⟨M, hM, ?_⟩
  intro e₁ e₂ he₁ he₂ n
  set R := engelerWithNumerals
  set f := mapsNumeralsFun M hM
  have hMn : interpClosed R.toReflexiveDcpo (M.app (churchNumN n)) =
      R.numeral (f n) := mapsNumerals_interp_numeral hM n
  have hchi : chiNum R S₂ (f n) = chiNum R S₁ n := by
    calc
      chiNum R S₂ (f n) = R.app d₂ (R.numeral (f n)) := (hd₂ (f n)).symm
      _ = R.app d₂ (interpClosed R.toReflexiveDcpo (M.app (churchNumN n))) := by
          rw [hMn]
      _ = R.app d₁ (R.numeral n) := hagree n
      _ = chiNum R S₁ n := hd₁ n
  calc
    R.app e₂ (interpClosed R.toReflexiveDcpo (M.app (churchNumN n)))
        = R.app e₂ (R.numeral (f n)) := by rw [hMn]
    _ = chiNum R S₂ (f n) := he₂ (f n)
    _ = chiNum R S₁ n := hchi
    _ = R.app e₁ (R.numeral n) := (he₁ n).symm

theorem proposition_36_i_of_ii {S₁ S₂ : Set ℕ} (h : proposition_36_ii S₁ S₂) :
    proposition_36_i S₁ S₂ := by
  obtain ⟨M, hM, hforall⟩ := h
  refine ⟨M, hM, chiOracle S₁, chiOracle S₂, chiOracle_isOracle S₁,
    chiOracle_isOracle S₂, ?_⟩
  exact hforall (chiOracle S₁) (chiOracle S₂)
    (chiOracle_isOracle S₁) (chiOracle_isOracle S₂)

/-- Proposition 36: paper (i) ↔ (ii) on `engelerWithNumerals`. -/
theorem proposition_36 (S₁ S₂ : Set ℕ) :
    proposition_36_i S₁ S₂ ↔ proposition_36_ii S₁ S₂ :=
  ⟨proposition_36_ii_of_i, proposition_36_i_of_ii⟩

/-!
## Proposition 36 at paper type (`churchWithNumerals`)
-/

/-- Proposition 36(i) on an arbitrary reflexive dcpo with Church numerals. -/
def proposition_36_i_of {D : Type*} [CompleteLattice D] (R : ReflexiveDcpo D)
    (hbool : interpClosed R churchTrueN ≠ interpClosed R churchFalseN)
    (S₁ S₂ : Set ℕ) : Prop :=
  ∃ M : Lam ℕ, MapsNumerals M ∧
    ∃ d₁ d₂ : D,
      IsOracle (churchWithNumerals R hbool) d₁ S₁ ∧
      IsOracle (churchWithNumerals R hbool) d₂ S₂ ∧
      ∀ n, R.app d₂ (interpClosed R (M.app (churchNumN n))) =
           R.app d₁ (interpClosed R (churchNumN n))

/-- Proposition 36(ii) on an arbitrary reflexive dcpo with Church numerals. -/
def proposition_36_ii_of {D : Type*} [CompleteLattice D] (R : ReflexiveDcpo D)
    (hbool : interpClosed R churchTrueN ≠ interpClosed R churchFalseN)
    (S₁ S₂ : Set ℕ) : Prop :=
  ∃ M : Lam ℕ, MapsNumerals M ∧
    ∀ d₁ d₂ : D,
      IsOracle (churchWithNumerals R hbool) d₁ S₁ →
      IsOracle (churchWithNumerals R hbool) d₂ S₂ →
      ∀ n, R.app d₂ (interpClosed R (M.app (churchNumN n))) =
           R.app d₁ (interpClosed R (churchNumN n))

/-- Paper (i) → (ii): agreement at some oracles plus numeral-mapping
soundness implies agreement at every oracle pair. No oracle existence. -/
theorem proposition_36_ii_of_i_of {D : Type*} [CompleteLattice D]
    (R : ReflexiveDcpo D)
    (hbool : interpClosed R churchTrueN ≠ interpClosed R churchFalseN)
    {S₁ S₂ : Set ℕ} (h : proposition_36_i_of R hbool S₁ S₂) :
    proposition_36_ii_of R hbool S₁ S₂ := by
  obtain ⟨M, hM, d₁, d₂, hd₁, hd₂, hagree⟩ := h
  refine ⟨M, hM, ?_⟩
  intro e₁ e₂ he₁ he₂ n
  set RN := churchWithNumerals R hbool
  set f := mapsNumeralsFun M hM
  have hMn : interpClosed R (M.app (churchNumN n)) =
      interpClosed R (churchNumN (f n)) := mapsNumerals_interp_numeral_of R hM n
  have hchi : chiNum RN S₂ (f n) = chiNum RN S₁ n := by
    calc
      chiNum RN S₂ (f n) = RN.app d₂ (RN.numeral (f n)) := (hd₂ (f n)).symm
      _ = R.app d₂ (interpClosed R (churchNumN (f n))) := rfl
      _ = R.app d₂ (interpClosed R (M.app (churchNumN n))) := by rw [hMn]
      _ = R.app d₁ (interpClosed R (churchNumN n)) := hagree n
      _ = RN.app d₁ (RN.numeral n) := rfl
      _ = chiNum RN S₁ n := hd₁ n
  calc
    R.app e₂ (interpClosed R (M.app (churchNumN n)))
        = R.app e₂ (interpClosed R (churchNumN (f n))) := by rw [hMn]
    _ = RN.app e₂ (RN.numeral (f n)) := rfl
    _ = chiNum RN S₂ (f n) := he₂ (f n)
    _ = chiNum RN S₁ n := hchi
    _ = RN.app e₁ (RN.numeral n) := (he₁ n).symm

/-- Paper (ii) → (i): Lemma 35(ii) supplies oracles on a continuous lattice. -/
theorem proposition_36_i_of_ii_of {D : Type*} [CompleteLattice D]
    (R : ReflexiveDcpo D)
    (hbool : interpClosed R churchTrueN ≠ interpClosed R churchFalseN)
    (hcont : Scott1972.ContinuousLattice.IsContinuousLattice D)
    {S₁ S₂ : Set ℕ} (h : proposition_36_ii_of R hbool S₁ S₂) :
    proposition_36_i_of R hbool S₁ S₂ := by
  obtain ⟨M, hM, hforall⟩ := h
  obtain ⟨d₁, hd₁⟩ := lemma_35_ii_of R hbool hcont S₁
  obtain ⟨d₂, hd₂⟩ := lemma_35_ii_of R hbool hcont S₂
  refine ⟨M, hM, d₁, d₂, hd₁, hd₂, ?_⟩
  exact hforall d₁ d₂ hd₁ hd₂

/-- Proposition 36 at paper type: (i) ↔ (ii) on a reflexive continuous
lattice with Church numerals. Oracle existence (ii) → (i) uses
`lemma_35_ii_of`. -/
theorem proposition_36_of {D : Type*} [CompleteLattice D] (R : ReflexiveDcpo D)
    (hbool : interpClosed R churchTrueN ≠ interpClosed R churchFalseN)
    (hcont : Scott1972.ContinuousLattice.IsContinuousLattice D)
    (S₁ S₂ : Set ℕ) :
    proposition_36_i_of R hbool S₁ S₂ ↔ proposition_36_ii_of R hbool S₁ S₂ :=
  ⟨proposition_36_ii_of_i_of R hbool,
    proposition_36_i_of_ii_of R hbool hcont⟩

theorem chiNum_churchWithNumerals_engeler (S : Set ℕ) (n : ℕ) :
    chiNum (churchWithNumerals engelerWithNumerals.toReflexiveDcpo
        engeler_churchTrueN_ne_churchFalseN) S n =
      chiNum engelerWithNumerals S n := by
  simp [chiNum, churchWithNumerals_engeler_boolTop,
    churchWithNumerals_engeler_boolBot]

theorem isOracle_churchWithNumerals_engeler (d : Set ℕ) (S : Set ℕ) :
    IsOracle (churchWithNumerals engelerWithNumerals.toReflexiveDcpo
        engeler_churchTrueN_ne_churchFalseN) d S ↔
    IsOracle engelerWithNumerals d S := by
  constructor
  · intro hd n
    rw [← churchWithNumerals_engeler_numeral n, ← chiNum_churchWithNumerals_engeler]
    exact hd n
  · intro hd n
    rw [churchWithNumerals_engeler_numeral n, chiNum_churchWithNumerals_engeler]
    exact hd n

theorem proposition_36_i_iff_of (S₁ S₂ : Set ℕ) :
    proposition_36_i_of engelerWithNumerals.toReflexiveDcpo
      engeler_churchTrueN_ne_churchFalseN S₁ S₂ ↔
    proposition_36_i S₁ S₂ := by
  constructor
  · intro ⟨M, hM, d₁, d₂, hd₁, hd₂, hagree⟩
    refine ⟨M, hM, d₁, d₂, (isOracle_churchWithNumerals_engeler d₁ S₁).mp hd₁,
      (isOracle_churchWithNumerals_engeler d₂ S₂).mp hd₂, ?_⟩
    intro n
    rw [numeral_eq_interpClosed_churchNumN n]
    exact hagree n
  · intro ⟨M, hM, d₁, d₂, hd₁, hd₂, hagree⟩
    refine ⟨M, hM, d₁, d₂, (isOracle_churchWithNumerals_engeler d₁ S₁).mpr hd₁,
      (isOracle_churchWithNumerals_engeler d₂ S₂).mpr hd₂, ?_⟩
    intro n
    rw [← numeral_eq_interpClosed_churchNumN n]
    exact hagree n

theorem proposition_36_ii_iff_of (S₁ S₂ : Set ℕ) :
    proposition_36_ii_of engelerWithNumerals.toReflexiveDcpo
      engeler_churchTrueN_ne_churchFalseN S₁ S₂ ↔
    proposition_36_ii S₁ S₂ := by
  constructor
  · intro ⟨M, hM, hforall⟩
    refine ⟨M, hM, ?_⟩
    intro d₁ d₂ hd₁ hd₂ n
    have hd₁' := (isOracle_churchWithNumerals_engeler d₁ S₁).mpr hd₁
    have hd₂' := (isOracle_churchWithNumerals_engeler d₂ S₂).mpr hd₂
    rw [numeral_eq_interpClosed_churchNumN n]
    exact hforall d₁ d₂ hd₁' hd₂' n
  · intro ⟨M, hM, hforall⟩
    refine ⟨M, hM, ?_⟩
    intro d₁ d₂ hd₁ hd₂ n
    have hd₁' := (isOracle_churchWithNumerals_engeler d₁ S₁).mp hd₁
    have hd₂' := (isOracle_churchWithNumerals_engeler d₂ S₂).mp hd₂
    rw [← numeral_eq_interpClosed_churchNumN n]
    exact hforall d₁ d₂ hd₁' hd₂' n

/-- Engeler `proposition_36` follows from `proposition_36_of` after
Church `Fin 2`/`ℕ` agreement. The original Engeler proof is unchanged. -/
theorem proposition_36_via_general (S₁ S₂ : Set ℕ) :
    proposition_36_i S₁ S₂ ↔ proposition_36_ii S₁ S₂ := by
  have hcont : Scott1972.ContinuousLattice.IsContinuousLattice (Set ℕ) :=
    isContinuousLattice_set_1972 ℕ
  rw [← proposition_36_i_iff_of, ← proposition_36_ii_iff_of]
  exact proposition_36_of engelerWithNumerals.toReflexiveDcpo
    engeler_churchTrueN_ne_churchFalseN hcont S₁ S₂

/-!
## Relation to the algebraic predicate `ManyOneLe`
-/

theorem manyOneLe_of_proposition_36_i {S₁ S₂ : Set ℕ}
    (h : proposition_36_i S₁ S₂) :
    ManyOneLe engelerWithNumerals S₁ S₂ := by
  obtain ⟨M, hM, d₁, d₂, hd₁, hd₂, hagree⟩ := h
  refine ⟨mapsNumeralsFun M hM, d₁, d₂, hd₁, hd₂, ?_⟩
  intro n
  have hMn := mapsNumerals_interp_numeral hM n
  rw [← hMn]
  exact hagree n

theorem manyOneLe_of_proposition_36_ii {S₁ S₂ : Set ℕ}
    (h : proposition_36_ii S₁ S₂) :
    ManyOneLe engelerWithNumerals S₁ S₂ :=
  manyOneLe_of_proposition_36_i (proposition_36_i_of_ii h)

/-- Algebraic many-one comparison: some (not necessarily λ-definable) `f`
with `χ_{S₂}(f n) = χ_{S₁}(n)`. Oracles always exist via `lemma_35_ii`. -/
theorem manyOneLe_iff_chi (S₁ S₂ : Set ℕ) :
    ManyOneLe engelerWithNumerals S₁ S₂ ↔
      ∃ f : ℕ → ℕ, ∀ n,
        chiNum engelerWithNumerals S₂ (f n) = chiNum engelerWithNumerals S₁ n := by
  constructor
  · intro ⟨f, d₁, d₂, hd₁, hd₂, hf⟩
    refine ⟨f, fun n => ?_⟩
    calc
      chiNum engelerWithNumerals S₂ (f n)
          = engelerWithNumerals.app d₂ (engelerWithNumerals.numeral (f n)) :=
        (hd₂ (f n)).symm
      _ = engelerWithNumerals.app d₁ (engelerWithNumerals.numeral n) := hf n
      _ = chiNum engelerWithNumerals S₁ n := hd₁ n
  · intro ⟨f, hf⟩
    refine ⟨f, chiOracle S₁, chiOracle S₂, chiOracle_spec S₁, chiOracle_spec S₂, ?_⟩
    intro n
    calc
      engelerWithNumerals.app (chiOracle S₂) (engelerWithNumerals.numeral (f n))
          = chiNum engelerWithNumerals S₂ (f n) := chiOracle_spec S₂ (f n)
      _ = chiNum engelerWithNumerals S₁ n := hf n
      _ = engelerWithNumerals.app (chiOracle S₁) (engelerWithNumerals.numeral n) :=
        (chiOracle_spec S₁ n).symm

theorem manyOneLe_of_proposition_36_i_of {D : Type*} [CompleteLattice D]
    (R : ReflexiveDcpo D)
    (hbool : interpClosed R churchTrueN ≠ interpClosed R churchFalseN)
    {S₁ S₂ : Set ℕ} (h : proposition_36_i_of R hbool S₁ S₂) :
    ManyOneLe (churchWithNumerals R hbool) S₁ S₂ := by
  obtain ⟨M, hM, d₁, d₂, hd₁, hd₂, hagree⟩ := h
  refine ⟨mapsNumeralsFun M hM, d₁, d₂, hd₁, hd₂, ?_⟩
  intro n
  have hMn := mapsNumerals_interp_numeral_of R hM n
  change R.app d₂ (interpClosed R (churchNumN (mapsNumeralsFun M hM n))) =
    R.app d₁ (interpClosed R (churchNumN n))
  rw [← hMn]
  exact hagree n

/-- Algebraic many-one comparison on `churchWithNumerals`. Oracles exist
via `lemma_35_ii_of` (not `chiOracle` / `gbar`). -/
theorem manyOneLe_iff_chi_of {D : Type*} [CompleteLattice D]
    (R : ReflexiveDcpo D)
    (hbool : interpClosed R churchTrueN ≠ interpClosed R churchFalseN)
    (hcont : Scott1972.ContinuousLattice.IsContinuousLattice D)
    (S₁ S₂ : Set ℕ) :
    ManyOneLe (churchWithNumerals R hbool) S₁ S₂ ↔
      ∃ f : ℕ → ℕ, ∀ n,
        chiNum (churchWithNumerals R hbool) S₂ (f n) =
        chiNum (churchWithNumerals R hbool) S₁ n := by
  set RN := churchWithNumerals R hbool
  constructor
  · intro ⟨f, d₁, d₂, hd₁, hd₂, hf⟩
    refine ⟨f, fun n => ?_⟩
    calc
      chiNum RN S₂ (f n) = RN.app d₂ (RN.numeral (f n)) := (hd₂ (f n)).symm
      _ = RN.app d₁ (RN.numeral n) := hf n
      _ = chiNum RN S₁ n := hd₁ n
  · intro ⟨f, hf⟩
    obtain ⟨d₁, hd₁⟩ := lemma_35_ii_of R hbool hcont S₁
    obtain ⟨d₂, hd₂⟩ := lemma_35_ii_of R hbool hcont S₂
    refine ⟨f, d₁, d₂, hd₁, hd₂, ?_⟩
    intro n
    calc
      RN.app d₂ (RN.numeral (f n)) = chiNum RN S₂ (f n) := hd₂ (f n)
      _ = chiNum RN S₁ n := hf n
      _ = RN.app d₁ (RN.numeral n) := (hd₁ n).symm

/-!
## Not every `f : ℕ → ℕ` is given by a closed λ-term
-/

/-- Injective encoding of `Lam ℕ` into `ℕ`. -/
def lamEncode : Lam ℕ → ℕ
  | .var x => Nat.pair 0 x
  | .abs x M => Nat.pair 1 (Nat.pair x (lamEncode M))
  | .app M N => Nat.pair 2 (Nat.pair (lamEncode M) (lamEncode N))

theorem lamEncode_injective : Function.Injective lamEncode := by
  intro M
  induction M with
  | var x =>
    intro N h
    cases N with
    | var y =>
      exact congrArg Lam.var (Nat.pair_eq_pair.mp h).2
    | abs _ _ =>
      exact absurd (Nat.pair_eq_pair.mp h).1 (by decide)
    | app _ _ =>
      exact absurd (Nat.pair_eq_pair.mp h).1 (by decide)
  | abs x M ih =>
    intro N h
    cases N with
    | var _ =>
      exact absurd (Nat.pair_eq_pair.mp h).1 (by decide)
    | abs y N =>
      have hp : Nat.pair x (lamEncode M) = Nat.pair y (lamEncode N) :=
        (Nat.pair_eq_pair.mp h).2
      have hx : x = y := (Nat.pair_eq_pair.mp hp).1
      have hbody : lamEncode M = lamEncode N := (Nat.pair_eq_pair.mp hp).2
      exact congrArg₂ Lam.abs hx (ih hbody)
    | app _ _ =>
      exact absurd (Nat.pair_eq_pair.mp h).1 (by decide)
  | app M₁ M₂ ih₁ ih₂ =>
    intro N h
    cases N with
    | var _ =>
      exact absurd (Nat.pair_eq_pair.mp h).1 (by decide)
    | abs _ _ =>
      exact absurd (Nat.pair_eq_pair.mp h).1 (by decide)
    | app N₁ N₂ =>
      have hp : Nat.pair (lamEncode M₁) (lamEncode M₂) =
          Nat.pair (lamEncode N₁) (lamEncode N₂) :=
        (Nat.pair_eq_pair.mp h).2
      have h1 : lamEncode M₁ = lamEncode N₁ := (Nat.pair_eq_pair.mp hp).1
      have h2 : lamEncode M₂ = lamEncode N₂ := (Nat.pair_eq_pair.mp hp).2
      exact congrArg₂ Lam.app (ih₁ h1) (ih₂ h2)

/-- Partial inverse of `lamEncode`. -/
def lamOfCode (n : ℕ) : Lam ℕ :=
  if h : ∃ M, lamEncode M = n then Classical.choose h else Lam.var 0

theorem lamOfCode_encode (M : Lam ℕ) : lamOfCode (lamEncode M) = M := by
  have h : ∃ N, lamEncode N = lamEncode M := ⟨M, rfl⟩
  simp only [lamOfCode, dif_pos h]
  exact lamEncode_injective (Classical.choose_spec h)

/-- A witness `m` for `M c_n = c_m`, or `0` if none exists. -/
def representedAt (M : Lam ℕ) (n : ℕ) : ℕ :=
  if h : ∃ m, LamEq (M.app (churchNumN n)) (churchNumN m) then
    Classical.choose h else 0

theorem representedAt_eq {M : Lam ℕ} {n m : ℕ}
    (h : LamEq (M.app (churchNumN n)) (churchNumN m)) :
    representedAt M n = m := by
  have hex : ∃ k, LamEq (M.app (churchNumN n)) (churchNumN k) := ⟨m, h⟩
  simp only [representedAt, dif_pos hex]
  exact churchNumN_lamEq_injective ((Classical.choose_spec hex).symm.trans h)

/-- Not every `f : ℕ → ℕ` is represented by a closed λ-term. A “Church
numeral of an arbitrary function” is therefore not a λ-term. -/
theorem exists_nat_fun_not_lambda_definable :
    ∃ f : ℕ → ℕ, ∀ M : Lam ℕ,
      ¬(M.fv = ∅ ∧ ∀ n, LamEq (M.app (churchNumN n)) (churchNumN (f n))) := by
  let f : ℕ → ℕ := fun n => representedAt (lamOfCode n) n + 1
  refine ⟨f, fun M hM => ?_⟩
  obtain ⟨_hfv, hrep⟩ := hM
  set n := lamEncode M
  have hMcode : lamOfCode n = M := lamOfCode_encode M
  have hAt : representedAt M n = f n := representedAt_eq (hrep n)
  have hfval : f n = representedAt M n + 1 := by
    change representedAt (lamOfCode n) n + 1 = representedAt M n + 1
    rw [hMcode]
  have : representedAt M n = representedAt M n + 1 :=
    hAt.trans hfval
  exact Nat.succ_ne_self (representedAt M n) this.symm

end

end Scott2026
