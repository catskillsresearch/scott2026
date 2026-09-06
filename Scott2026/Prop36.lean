/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/

import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Nat.Pairing
import Scott2026.Interp

/-!
# Proposition 36: many-one comparison via a numeral-to-numeral combinator

Furber–Mardare–Panangaden–Scott, CSL 2026, Proposition 36, on
`engelerWithNumerals`. Paper (i) and (ii) are equivalent: a closed
`M` that sends Church numerals to Church numerals (`MapsNumerals`)
reduces `S₁` to `S₂` at some pair of `χ`-oracles iff it does so at
every such pair.

`ManyOneLe` remains the algebraic predicate (any `f : ℕ → ℕ`, no
λ-term). Paper (i) implies `ManyOneLe`; the converse would require a
closed λ-term for `f`, which is false for a general `f`
(`exists_nat_fun_not_lambda_definable`).
-/

open Set Function Classical

namespace Scott2026

noncomputable section

/-!
## Church numerals: `Fin 2` vs `ℕ`

`engelerWithNumerals.numeral n` interprets `churchNum n : Lam (Fin 2)`.
Paper identities live on `churchNumN : ℕ → Lam ℕ`. Both unfold to the
same meta-lambdas, so their closed interpretations agree.
-/

theorem churchNum_interpClosed_zero {D : Type*} [CompleteLattice D]
    (R : ReflexiveDcpo D) :
    interpClosed R (churchNum 0) = R.lam fun _ => R.lam fun Y => Y := by
  simp [interpClosed, churchNum, interp, Valuation.update, Valuation.empty,
    Function.update]

theorem churchNumN_interpClosed_zero {D : Type*} [CompleteLattice D]
    (R : ReflexiveDcpo D) :
    interpClosed R (churchNumN 0) = R.lam fun _ => R.lam fun Y => Y := by
  simp [interpClosed, churchNumN, interp, Valuation.update, Valuation.empty,
    Function.update]

theorem churchNum_interpClosed_succ {D : Type*} [CompleteLattice D]
    (R : ReflexiveDcpo D) (n : ℕ) :
    interpClosed R (churchNum (n + 1)) =
      R.lam fun F => R.lam fun X =>
        R.app F (R.app (R.app (interpClosed R (churchNum n)) F) X) := by
  have h1 : interpClosed R (churchNum (n + 1)) =
      R.lam fun F =>
        interp R
          (Lam.abs 1
            (Lam.app (Lam.var 0)
              (Lam.app (Lam.app (churchNum n) (Lam.var 0)) (Lam.var 1))))
          (Valuation.empty.update (0 : Fin 2) F) := by
    simp [interpClosed, churchNum, interp]
  refine h1.trans ?_
  congr 1
  funext F
  simp only [interp]
  congr 1
  funext X
  have hcn : interp R (churchNum n)
      ((Valuation.empty.update (0 : Fin 2) F).update 1 X) =
        interpClosed R (churchNum n) :=
    interp_closed_of_fv_empty R (churchNum n) _ (churchNum_fv n)
  have h0 : ((Valuation.empty.update (0 : Fin 2) F).update 1 X).toFun 0 = F :=
    Valuation.update_toFun_of_ne (Valuation.empty.update (0 : Fin 2) F)
      (x := 1) (y := 0) X Fin.zero_ne_one
  have hX : ((Valuation.empty.update (0 : Fin 2) F).update 1 X).toFun 1 = X :=
    Valuation.update_toFun_self _ 1 X
  simp [interp, h0, hX, hcn]

theorem churchNumN_interpClosed_succ {D : Type*} [CompleteLattice D]
    (R : ReflexiveDcpo D) (n : ℕ) :
    interpClosed R (churchNumN (n + 1)) =
      R.lam fun F => R.lam fun X =>
        R.app F (R.app (R.app (interpClosed R (churchNumN n)) F) X) := by
  have h1 : interpClosed R (churchNumN (n + 1)) =
      R.lam fun F =>
        interp R
          (Lam.abs 1
            (Lam.app (Lam.var 0)
              (Lam.app (Lam.app (churchNumN n) (Lam.var 0)) (Lam.var 1))))
          (Valuation.empty.update (0 : ℕ) F) := by
    simp [interpClosed, churchNumN, interp]
  refine h1.trans ?_
  congr 1
  funext F
  simp only [interp]
  congr 1
  funext X
  have hcn : interp R (churchNumN n)
      ((Valuation.empty.update (0 : ℕ) F).update 1 X) =
        interpClosed R (churchNumN n) :=
    interp_closed_of_fv_empty R (churchNumN n) _ (churchNumN_fv n)
  have h0 : ((Valuation.empty.update (0 : ℕ) F).update 1 X).toFun 0 = F :=
    Valuation.update_toFun_of_ne (Valuation.empty.update (0 : ℕ) F)
      (x := 1) (y := 0) X (by decide)
  have hX : ((Valuation.empty.update (0 : ℕ) F).update 1 X).toFun 1 = X :=
    Valuation.update_toFun_self _ 1 X
  simp [interp, h0, hX, hcn]

/-- Closed interpretations of `churchNum` (`Fin 2`) and `churchNumN` (`ℕ`)
agree: binders are only names. -/
theorem churchNum_interpClosed_eq_churchNumN {D : Type*} [CompleteLattice D]
    (R : ReflexiveDcpo D) (n : ℕ) :
    interpClosed R (churchNum n) = interpClosed R (churchNumN n) := by
  induction n with
  | zero =>
    rw [churchNum_interpClosed_zero, churchNumN_interpClosed_zero]
  | succ n ih =>
    rw [churchNum_interpClosed_succ, churchNumN_interpClosed_succ, ih]

theorem numeral_eq_interpClosed_churchNumN (n : ℕ) :
    engelerWithNumerals.numeral n =
      interpClosed engelerWithNumerals.toReflexiveDcpo (churchNumN n) := by
  rw [← churchNum_interpClosed_eq_churchNumN]
  rfl

/-!
## Numeral-to-numeral combinators
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
