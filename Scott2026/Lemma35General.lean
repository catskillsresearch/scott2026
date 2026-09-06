/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/

import Scott2026.Interp
import Scott1972.ContinuousLattice.Constructions

/-!
# Lemma 35 for arbitrary reflexive dcpos with numerals

The paper derives numeral-separating closed terms from Definition 32.
`NumeralSeparators` records their denotations.  `churchWithNumerals` plus
`numeralSeparators_church` instantiate that interface from Church
interpretations, so the paper-named theorems `lemma_35_i_of` /
`lemma_35_ii_of` / `lemma_35_of` do not take `NumeralSeparators` as an
extra hypothesis.  Engeler `lemma_35` keeps its original name and proof.
-/

universe u

namespace Scott2026

open Set

/-- Denotations of negation and the derived `m?` tests used in the proof of
Lemma 35(i). -/
structure NumeralSeparators (D : Type u) [CompleteLattice D]
    (R : ReflexiveDcpoWithNumerals D) where
  neg : D
  neg_top : R.app neg R.boolTop = R.boolBot
  neg_bot : R.app neg R.boolBot = R.boolTop
  test : ℕ → D
  test_spec : ∀ m n,
    R.app (test m) (R.numeral n) =
      if n = m then R.boolTop else R.boolBot

/-- The two Boolean denotations can be separated by Scott opens in both
directions, using denotational negation exactly as in the paper. -/
theorem lemma_35_bool_discrete_general {D : Type u} [CompleteLattice D]
    (R : ReflexiveDcpoWithNumerals D) (H : NumeralSeparators D R) :
    ∃ U V : Set D, ScottOpen U ∧ ScottOpen V ∧
      R.boolTop ∈ U ∧ R.boolBot ∉ U ∧
      R.boolBot ∈ V ∧ R.boolTop ∉ V := by
  have hsep : ¬R.boolBot ≤ R.boolTop ∨ ¬R.boolTop ≤ R.boolBot := by
    by_contra h
    push Not at h
    exact R.bool_ne (le_antisymm h.1 h.2)
  rcases hsep with hbt | htb
  · let V : Set D := {z | ¬z ≤ R.boolTop}
    let U : Set D := (fun z => R.app H.neg z) ⁻¹' V
    have hV : ScottOpen V := scottOpen_not_le R.boolTop
    have happ : IsScottContinuous (fun z => R.app H.neg z) :=
      R.fun_scott_pt H.neg
    have hU : ScottOpen U := scottOpen_preimage happ hV
    refine ⟨U, V, hU, hV, ?_, ?_, ?_, ?_⟩
    · change R.app H.neg R.boolTop ∈ V
      rw [H.neg_top]
      exact hbt
    · intro h
      change R.app H.neg R.boolBot ∈ V at h
      rw [H.neg_bot] at h
      exact h le_rfl
    · exact hbt
    · intro h
      exact h le_rfl
  · let U : Set D := {z | ¬z ≤ R.boolBot}
    let V : Set D := (fun z => R.app H.neg z) ⁻¹' U
    have hU : ScottOpen U := scottOpen_not_le R.boolBot
    have happ : IsScottContinuous (fun z => R.app H.neg z) :=
      R.fun_scott_pt H.neg
    have hV : ScottOpen V := scottOpen_preimage happ hU
    refine ⟨U, V, hU, hV, ?_, ?_, ?_, ?_⟩
    · exact htb
    · intro h
      exact h le_rfl
    · change R.app H.neg R.boolBot ∈ U
      rw [H.neg_bot]
      exact htb
    · intro h
      change R.app H.neg R.boolTop ∈ U at h
      rw [H.neg_top] at h
      exact h le_rfl

/-- Every numeral is isolated in the numeral subspace by a Scott-open set. -/
theorem lemma_35_numeral_discrete_general {D : Type u} [CompleteLattice D]
    (R : ReflexiveDcpoWithNumerals D) (H : NumeralSeparators D R) :
    ∀ m : ℕ, ∃ W : Set D, ScottOpen W ∧
      R.numeral m ∈ W ∧
      ∀ n, n ≠ m → R.numeral n ∉ W := by
  obtain ⟨U, _V, hU, _hV, htop, hbot, _⟩ :=
    lemma_35_bool_discrete_general R H
  intro m
  let W : Set D := (fun z => R.app (H.test m) z) ⁻¹' U
  have hW : ScottOpen W :=
    scottOpen_preimage (R.fun_scott_pt (H.test m)) hU
  refine ⟨W, hW, ?_, ?_⟩
  · change R.app (H.test m) (R.numeral m) ∈ U
    rw [H.test_spec, if_pos rfl]
    exact htop
  · intro n hnm hn
    change R.app (H.test m) (R.numeral n) ∈ U at hn
    rw [H.test_spec, if_neg hnm] at hn
    exact hbot hn

/-- Lemma 35(i) at the paper's arbitrary-domain type. -/
theorem lemma_35_i_general {D : Type u} [CompleteLattice D]
    (R : ReflexiveDcpoWithNumerals D) (H : NumeralSeparators D R) :
    (∃ U V : Set D, ScottOpen U ∧ ScottOpen V ∧
      R.boolTop ∈ U ∧ R.boolBot ∉ U ∧
      R.boolBot ∈ V ∧ R.boolTop ∉ V) ∧
    (∀ m : ℕ, ∃ W : Set D, ScottOpen W ∧
      R.numeral m ∈ W ∧
      ∀ n, n ≠ m → R.numeral n ∉ W) ∧
    Function.Injective R.numeral :=
  ⟨lemma_35_bool_discrete_general R H,
    lemma_35_numeral_discrete_general R H,
    R.numeral_inj⟩

/-!
## Church numerals as the paper's distinguished elements

Definition 32's Booleans and numerals are Church interpretations.  The
algebraic `ReflexiveDcpoWithNumerals` does not store `if`/`pred`/`0?`;
those appear only as closed-term denotations.
-/

noncomputable section

open Topology

theorem churchTrue_interpClosed {D : Type u} [CompleteLattice D]
    (R : ReflexiveDcpo D) :
    interpClosed R churchTrue = R.lam fun X => R.lam fun _ => X := by
  simp [interpClosed, churchTrue, interp, Valuation.update, Valuation.empty,
    Function.update]

theorem churchTrueN_interpClosed {D : Type u} [CompleteLattice D]
    (R : ReflexiveDcpo D) :
    interpClosed R churchTrueN = R.lam fun X => R.lam fun _ => X := by
  simp [interpClosed, churchTrueN, interp, Valuation.update, Valuation.empty,
    Function.update]

theorem churchFalse_interpClosed {D : Type u} [CompleteLattice D]
    (R : ReflexiveDcpo D) :
    interpClosed R churchFalse = R.lam fun _ => R.lam fun Y => Y := by
  simp [interpClosed, churchFalse, interp, Valuation.update, Valuation.empty,
    Function.update]

theorem churchFalseN_interpClosed {D : Type u} [CompleteLattice D]
    (R : ReflexiveDcpo D) :
    interpClosed R churchFalseN = R.lam fun _ => R.lam fun Y => Y := by
  simp [interpClosed, churchFalseN, interp, Valuation.update, Valuation.empty,
    Function.update]

theorem churchTrue_interpClosed_eq_churchTrueN {D : Type u} [CompleteLattice D]
    (R : ReflexiveDcpo D) :
    interpClosed R churchTrue = interpClosed R churchTrueN := by
  rw [churchTrue_interpClosed, churchTrueN_interpClosed]

theorem churchFalse_interpClosed_eq_churchFalseN {D : Type u} [CompleteLattice D]
    (R : ReflexiveDcpo D) :
    interpClosed R churchFalse = interpClosed R churchFalseN := by
  rw [churchFalse_interpClosed, churchFalseN_interpClosed]

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

theorem interpClosed_app {D : Type u} [CompleteLattice D] {Var : Type*}
    [DecidableEq Var] (R : ReflexiveDcpo D) (M N : Lam Var) :
    interpClosed R (M.app N) = R.app (interpClosed R M) (interpClosed R N) :=
  rfl

theorem interpClosed_churchNotN_true {D : Type u} [CompleteLattice D]
    (R : ReflexiveDcpo D) :
    R.app (interpClosed R churchNotN) (interpClosed R churchTrueN) =
      interpClosed R churchFalseN := by
  rw [← interpClosed_app]
  exact interpClosed_sound_full (Var := ℕ) R churchNotN_true

theorem interpClosed_churchNotN_false {D : Type u} [CompleteLattice D]
    (R : ReflexiveDcpo D) :
    R.app (interpClosed R churchNotN) (interpClosed R churchFalseN) =
      interpClosed R churchTrueN := by
  rw [← interpClosed_app]
  exact interpClosed_sound_full (Var := ℕ) R churchNotN_false

theorem interpClosed_churchTest_num {D : Type u} [CompleteLattice D]
    (R : ReflexiveDcpo D) (m n : ℕ) :
    R.app (interpClosed R (churchTest m)) (interpClosed R (churchNumN n)) =
      if n = m then interpClosed R churchTrueN
      else interpClosed R churchFalseN := by
  rw [← interpClosed_app]
  have h := interpClosed_sound_full (Var := ℕ) R (churchTest_num m n)
  rw [h]
  split_ifs <;> rfl

/-- Paper: `fun(⟦m?⟧)(⟦c_m⟧) ≠ fun(⟦m?⟧)(⟦c_n⟧)` for `m ≠ n`, so numerals
are distinct. -/
theorem numeral_inj_of_churchTest {D : Type u} [CompleteLattice D]
    (R : ReflexiveDcpo D)
    (hbool : interpClosed R churchTrueN ≠ interpClosed R churchFalseN) :
    Function.Injective (fun n => interpClosed R (churchNumN n)) := by
  intro m n hmn
  by_contra hne
  have hm :
      R.app (interpClosed R (churchTest m)) (interpClosed R (churchNumN m)) =
        interpClosed R churchTrueN := by
    rw [interpClosed_churchTest_num, if_pos rfl]
  have hn :
      R.app (interpClosed R (churchTest m)) (interpClosed R (churchNumN n)) =
        interpClosed R churchFalseN := by
    rw [interpClosed_churchTest_num, if_neg (Ne.symm hne)]
  have happ :
      R.app (interpClosed R (churchTest m)) (interpClosed R (churchNumN m)) =
        R.app (interpClosed R (churchTest m)) (interpClosed R (churchNumN n)) :=
    congrArg (fun z => R.app (interpClosed R (churchTest m)) z) hmn
  exact hbool (hm.symm.trans (happ.trans hn))

/-- Church Booleans and numerals on an arbitrary reflexive dcpo. Distinctness
of numerals is the paper's `m?` argument, so it is not an extra hypothesis. -/
noncomputable def churchWithNumerals {D : Type u} [CompleteLattice D]
    (R : ReflexiveDcpo D)
    (hbool : interpClosed R churchTrueN ≠ interpClosed R churchFalseN) :
    ReflexiveDcpoWithNumerals D where
  toReflexiveDcpo := R
  boolBot := interpClosed R churchFalseN
  boolTop := interpClosed R churchTrueN
  numeral := fun n => interpClosed R (churchNumN n)
  bool_ne := hbool.symm
  numeral_inj := numeral_inj_of_churchTest R hbool

/-- Denotations of `¬` and `m?` on `churchWithNumerals`. -/
noncomputable def numeralSeparators_church {D : Type u} [CompleteLattice D]
    (R : ReflexiveDcpo D)
    (hbool : interpClosed R churchTrueN ≠ interpClosed R churchFalseN) :
    NumeralSeparators D (churchWithNumerals R hbool) where
  neg := interpClosed R churchNotN
  neg_top := interpClosed_churchNotN_true R
  neg_bot := interpClosed_churchNotN_false R
  test := fun m => interpClosed R (churchTest m)
  test_spec := interpClosed_churchTest_num R

/-- When an existing numeral structure is already the Church interpretation,
the paper separators are the interpretations of `churchNotN` and `churchTest`. -/
noncomputable def numeralSeparators_of_churchInterp {D : Type u} [CompleteLattice D]
    (R : ReflexiveDcpoWithNumerals D)
    (hTop : R.boolTop = interpClosed R.toReflexiveDcpo churchTrueN)
    (hBot : R.boolBot = interpClosed R.toReflexiveDcpo churchFalseN)
    (hNum : ∀ n, R.numeral n = interpClosed R.toReflexiveDcpo (churchNumN n)) :
    NumeralSeparators D R where
  neg := interpClosed R.toReflexiveDcpo churchNotN
  neg_top := by
    rw [hTop, hBot]
    exact interpClosed_churchNotN_true R.toReflexiveDcpo
  neg_bot := by
    rw [hTop, hBot]
    exact interpClosed_churchNotN_false R.toReflexiveDcpo
  test := fun m => interpClosed R.toReflexiveDcpo (churchTest m)
  test_spec := by
    intro m n
    rw [hNum n, hTop, hBot]
    exact interpClosed_churchTest_num R.toReflexiveDcpo m n

/-- Lemma 35(i) at paper type: discreteness from Church `¬` and `m?`, with
numeral injectivity derived from the test equations. -/
theorem lemma_35_i_of {D : Type u} [CompleteLattice D] (R : ReflexiveDcpo D)
    (hbool : interpClosed R churchTrueN ≠ interpClosed R churchFalseN) :
    (∃ U V : Set D, ScottOpen U ∧ ScottOpen V ∧
      (churchWithNumerals R hbool).boolTop ∈ U ∧
      (churchWithNumerals R hbool).boolBot ∉ U ∧
      (churchWithNumerals R hbool).boolBot ∈ V ∧
      (churchWithNumerals R hbool).boolTop ∉ V) ∧
    (∀ m : ℕ, ∃ W : Set D, ScottOpen W ∧
      (churchWithNumerals R hbool).numeral m ∈ W ∧
      ∀ n, n ≠ m → (churchWithNumerals R hbool).numeral n ∉ W) ∧
    Function.Injective (fun n => interpClosed R (churchNumN n)) :=
  lemma_35_i_general (churchWithNumerals R hbool) (numeralSeparators_church R hbool)

/-- Scott-topology continuity implies Mathlib directed-sup preservation
(lattice order, not the specialization `Preorder`). -/
theorem isScottContinuous_of_continuous {E F : Type*}
    [CompleteLattice E] [CompleteLattice F] {f : E → F}
    (hf : @Continuous E F Scott1972.ContinuousLattice.scottTopologicalSpace
      Scott1972.ContinuousLattice.scottTopologicalSpace f) :
    IsScottContinuous f := by
  have hE : @IsScott E univ _ (Topology.scott E univ) :=
    @IsScott.mk E univ _ (Topology.scott E univ) rfl
  have hF : @IsScott F univ _ (Topology.scott F univ) :=
    @IsScott.mk F univ _ (Topology.scott F univ) rfl
  exact scottContinuousOn_univ.1 <|
    (@Topology.IsScott.scottContinuousOn_iff_continuous E F _
      (Topology.scott E univ) _ (Topology.scott F univ) hF f univ hE
      (fun _ _ _ => trivial)).2 hf

/-- Characteristic values of `S` on the Church-numeral subspace. -/
noncomputable def churchNumeralChi {D : Type u} [CompleteLattice D]
    (R : ReflexiveDcpo D)
    (hbool : interpClosed R churchTrueN ≠ interpClosed R churchFalseN)
    (S : Set ℕ) (x : ↥(range (churchWithNumerals R hbool).numeral)) : D :=
  chiNum (churchWithNumerals R hbool) S (Classical.choose x.property)

theorem churchNumeralChi_numeral {D : Type u} [CompleteLattice D]
    (R : ReflexiveDcpo D)
    (hbool : interpClosed R churchTrueN ≠ interpClosed R churchFalseN)
    (S : Set ℕ) (n : ℕ) :
    churchNumeralChi R hbool S
        ⟨(churchWithNumerals R hbool).numeral n, ⟨n, rfl⟩⟩ =
      chiNum (churchWithNumerals R hbool) S n := by
  have h := Classical.choose_spec
    (⟨n, rfl⟩ : ∃ k, (churchWithNumerals R hbool).numeral k =
      (churchWithNumerals R hbool).numeral n)
  exact congrArg (chiNum (churchWithNumerals R hbool) S)
    ((churchWithNumerals R hbool).numeral_inj h)

theorem churchNumeral_subspace_singleton_open {D : Type u} [CompleteLattice D]
    (R : ReflexiveDcpo D)
    (hbool : interpClosed R churchTrueN ≠ interpClosed R churchFalseN)
    (x : ↥(range (churchWithNumerals R hbool).numeral)) :
    letI : TopologicalSpace D := Scott1972.ContinuousLattice.scottTopologicalSpace
    IsOpen ({x} : Set ↥(range (churchWithNumerals R hbool).numeral)) := by
  let : TopologicalSpace D := Scott1972.ContinuousLattice.scottTopologicalSpace
  obtain ⟨m, hm⟩ := x.property
  obtain ⟨W, hWopen, hmW, hsep⟩ :=
    lemma_35_numeral_discrete_general (churchWithNumerals R hbool)
      (numeralSeparators_church R hbool) m
  have hW : IsOpen W :=
    Scott1972.ContinuousLattice.isOpen_iff_scottOpen.mpr hWopen
  have hpre :
      ({x} : Set ↥(range (churchWithNumerals R hbool).numeral)) =
        (Subtype.val : ↥(range (churchWithNumerals R hbool).numeral) → D) ⁻¹'
          W := by
    ext y
    constructor
    · intro hy
      have hyx : y = x := mem_singleton_iff.mp hy
      rw [hyx]
      change (x : D) ∈ W
      rw [← hm]
      exact hmW
    · intro hy
      obtain ⟨n, hn⟩ := y.property
      have hne : n = m := by
        by_contra hnm
        have : (churchWithNumerals R hbool).numeral n ∉ W := hsep n hnm
        rw [hn] at this
        exact this hy
      apply Subtype.ext
      rw [← hn, hne, hm]
  rw [hpre]
  exact IsOpen.preimage continuous_subtype_val hW

theorem scottOpen_supseteq {X : Type*} {S : Set X} (hS : S.Finite) :
    ScottOpen {V : Set X | S ⊆ V} := by
  refine ⟨?upper, ?inacc⟩
  · intro A B hAB hA
    exact hA.trans hAB
  · intro 𝒟 _hne hdir hmem
    have hSunion : S ⊆ ⋃₀ 𝒟 := by
      simpa [sSup_eq_sUnion] using hmem
    refine Set.Finite.induction_on
      (motive := fun S' _ => S' ⊆ ⋃₀ 𝒟 → ∃ U ∈ 𝒟, S' ⊆ U) S hS ?empty ?insert
      hSunion
    · intro _
      obtain ⟨U, hU⟩ := _hne
      exact ⟨U, hU, empty_subset U⟩
    · intro a s _ha _hs ih hsT
      have hs_sub : s ⊆ ⋃₀ 𝒟 := (subset_insert a s).trans hsT
      obtain ⟨U, hU, hUs⟩ := ih hs_sub
      have haU : a ∈ ⋃₀ 𝒟 := hsT (mem_insert a s)
      obtain ⟨V, hV, haV⟩ := mem_sUnion.mp haU
      obtain ⟨W, hW, hUW, hVW⟩ := hdir U hU V hV
      exact ⟨W, hW, insert_subset (hVW haV) (hUs.trans hUW)⟩

theorem finite_subset_wayBelow_1972 {X : Type*} {S T : Set X}
    (hS : S.Finite) (hST : S ⊆ T) :
    Scott1972.ContinuousLattice.WayBelow S T :=
  ⟨{V | S ⊆ V}, scottOpen_supseteq hS, hST, fun _ hV => hV⟩

/-- `𝒫(X)` is a continuous lattice in the Scott 1972 sense used by
`scottExtend`. -/
theorem isContinuousLattice_set_1972 (X : Type*) :
    Scott1972.ContinuousLattice.IsContinuousLattice (Set X) := by
  intro T
  constructor
  · intro S hS
    exact Scott1972.ContinuousLattice.WayBelow.le hS
  · intro b hb x hx
    have hsing : ({x} : Set X) ⊆ b :=
      hb (finite_subset_wayBelow_1972 (finite_singleton x)
        (singleton_subset_iff.mpr hx))
    exact hsing (mem_singleton x)

/-- Lemma 35(ii) at paper type: the discrete numeral subspace map extends
along Scott 1972 injectivity (`scottExtend`), then `d_g = lam ḡ`. -/
theorem lemma_35_ii_of {D : Type u} [CompleteLattice D] (R : ReflexiveDcpo D)
    (hbool : interpClosed R churchTrueN ≠ interpClosed R churchFalseN)
    (hcont : Scott1972.ContinuousLattice.IsContinuousLattice D) (S : Set ℕ) :
    ∃ d : D, ∀ n,
      R.app d (interpClosed R (churchNumN n)) =
        chiNum (churchWithNumerals R hbool) S n := by
  let : TopologicalSpace D := Scott1972.ContinuousLattice.scottTopologicalSpace
  let RN := churchWithNumerals R hbool
  let N := ↥(range RN.numeral)
  let e : N → D := Subtype.val
  have he : IsEmbedding e := IsEmbedding.subtypeVal
  let g : N → D := churchNumeralChi R hbool S
  have hg : @Continuous N D _ Scott1972.ContinuousLattice.scottTopologicalSpace g := by
    rw [continuous_def]
    intro U _hU
    have hcov : g ⁻¹' U = ⋃ x ∈ g ⁻¹' U, ({x} : Set N) := by
      ext y
      constructor
      · intro hy
        exact mem_iUnion.mpr ⟨y, mem_iUnion.mpr ⟨hy, mem_singleton y⟩⟩
      · intro hy
        obtain ⟨x, hx⟩ := mem_iUnion.mp hy
        obtain ⟨hxU, hyx⟩ := mem_iUnion.mp hx
        rw [mem_singleton_iff] at hyx
        subst hyx
        exact hxU
    rw [hcov]
    exact isOpen_biUnion fun x _ =>
      churchNumeral_subspace_singleton_open R hbool x
  let gbarD : D → D := Scott1972.ContinuousLattice.scottExtend e g
  have hgbar_top :
      @Continuous D D Scott1972.ContinuousLattice.scottTopologicalSpace
        Scott1972.ContinuousLattice.scottTopologicalSpace gbarD :=
    Scott1972.ContinuousLattice.scottExtend_continuous hcont e g
  have hgbar_sc := isScottContinuous_of_continuous hgbar_top
  refine ⟨RN.lam gbarD, fun n => ?_⟩
  have hgS : ∀ k, gbarD (RN.numeral k) = chiNum RN S k := by
    intro k
    have hpt := Scott1972.ContinuousLattice.scottExtend_eq_of_continuous
      hcont e he g hg (⟨RN.numeral k, ⟨k, rfl⟩⟩ : N)
    change Scott1972.ContinuousLattice.scottExtend e g (RN.numeral k) =
      chiNum RN S k
    have heq : e ⟨RN.numeral k, ⟨k, rfl⟩⟩ = RN.numeral k := rfl
    rw [← heq, hpt]
    exact churchNumeralChi_numeral R hbool S k
  exact lemma_35_ii_of_extension RN S gbarD hgbar_sc hgS n

/-- Lemma 35 at paper type on an arbitrary reflexive continuous lattice
whose distinguished elements are Church interpretations. -/
theorem lemma_35_of {D : Type u} [CompleteLattice D] (R : ReflexiveDcpo D)
    (hbool : interpClosed R churchTrueN ≠ interpClosed R churchFalseN)
    (hcont : Scott1972.ContinuousLattice.IsContinuousLattice D) :
    (∃ U V : Set D, ScottOpen U ∧ ScottOpen V ∧
      (churchWithNumerals R hbool).boolTop ∈ U ∧
      (churchWithNumerals R hbool).boolBot ∉ U ∧
      (churchWithNumerals R hbool).boolBot ∈ V ∧
      (churchWithNumerals R hbool).boolTop ∉ V) ∧
    (∀ m : ℕ, ∃ W : Set D, ScottOpen W ∧
      (churchWithNumerals R hbool).numeral m ∈ W ∧
      ∀ n, n ≠ m → (churchWithNumerals R hbool).numeral n ∉ W) ∧
    Function.Injective (fun n => interpClosed R (churchNumN n)) ∧
    ∀ S : Set ℕ, ∃ d : D, ∀ n,
      R.app d (interpClosed R (churchNumN n)) =
        chiNum (churchWithNumerals R hbool) S n :=
  ⟨(lemma_35_i_of R hbool).1, (lemma_35_i_of R hbool).2.1,
    (lemma_35_i_of R hbool).2.2, fun S => lemma_35_ii_of R hbool hcont S⟩

/-- Engeler `hbool` after Church `Fin 2`/`ℕ` agreement. -/
theorem engeler_churchTrueN_ne_churchFalseN :
    interpClosed engelerWithNumerals.toReflexiveDcpo churchTrueN ≠
      interpClosed engelerWithNumerals.toReflexiveDcpo churchFalseN := by
  rw [← churchTrue_interpClosed_eq_churchTrueN (D := Set ℕ),
    ← churchFalse_interpClosed_eq_churchFalseN (D := Set ℕ)]
  exact churchTrue_interp_ne_churchFalse engelerPair engelerPair_injective

theorem churchWithNumerals_engeler_boolTop :
    (churchWithNumerals (D := Set ℕ) engelerWithNumerals.toReflexiveDcpo
        engeler_churchTrueN_ne_churchFalseN).boolTop =
      engelerWithNumerals.boolTop :=
  (churchTrue_interpClosed_eq_churchTrueN (D := Set ℕ)
    engelerWithNumerals.toReflexiveDcpo).symm

theorem churchWithNumerals_engeler_boolBot :
    (churchWithNumerals (D := Set ℕ) engelerWithNumerals.toReflexiveDcpo
        engeler_churchTrueN_ne_churchFalseN).boolBot =
      engelerWithNumerals.boolBot :=
  (churchFalse_interpClosed_eq_churchFalseN (D := Set ℕ)
    engelerWithNumerals.toReflexiveDcpo).symm

theorem churchWithNumerals_engeler_numeral (n : ℕ) :
    (churchWithNumerals (D := Set ℕ) engelerWithNumerals.toReflexiveDcpo
        engeler_churchTrueN_ne_churchFalseN).numeral n =
      engelerWithNumerals.numeral n :=
  (churchNum_interpClosed_eq_churchNumN (D := Set ℕ)
    engelerWithNumerals.toReflexiveDcpo n).symm

/-- Engeler `lemma_35_i` follows from `lemma_35_i_of` after Church agreement.
The original Engeler proof of `lemma_35_i` is unchanged. -/
theorem lemma_35_i_via_general :
    (∃ U V : Set (Set ℕ), ScottOpen U ∧ ScottOpen V ∧
      engelerWithNumerals.boolTop ∈ U ∧ engelerWithNumerals.boolBot ∉ U ∧
      engelerWithNumerals.boolBot ∈ V ∧ engelerWithNumerals.boolTop ∉ V) ∧
    (∀ m : ℕ, ∃ W : Set (Set ℕ), ScottOpen W ∧
      engelerWithNumerals.numeral m ∈ W ∧
      ∀ n, n ≠ m → engelerWithNumerals.numeral n ∉ W) ∧
    Function.Injective engelerWithNumerals.numeral := by
  have h := lemma_35_i_of engelerWithNumerals.toReflexiveDcpo
    engeler_churchTrueN_ne_churchFalseN
  rw [churchWithNumerals_engeler_boolTop, churchWithNumerals_engeler_boolBot] at h
  refine ⟨h.1, ?_, ?_⟩
  · intro m
    obtain ⟨W, hW, hmW, hsep⟩ := h.2.1 m
    refine ⟨W, hW, ?_, ?_⟩
    · rwa [← churchWithNumerals_engeler_numeral m]
    · intro n hnm hn
      exact hsep n hnm (churchWithNumerals_engeler_numeral n ▸ hn)
  · intro m n hmn
    rw [← churchWithNumerals_engeler_numeral m,
      ← churchWithNumerals_engeler_numeral n] at hmn
    exact h.2.2 hmn

/-- Engeler `lemma_35_ii` follows from `lemma_35_ii_of`. The original
`gbar` proof of `lemma_35_ii` is unchanged. -/
theorem lemma_35_ii_via_general (S : Set ℕ) :
    ∃ d : Set ℕ, ∀ n,
      engelerWithNumerals.app d (engelerWithNumerals.numeral n) =
        chiNum engelerWithNumerals S n := by
  have hcont : Scott1972.ContinuousLattice.IsContinuousLattice (Set ℕ) :=
    isContinuousLattice_set_1972 ℕ
  obtain ⟨d, hd⟩ :=
    lemma_35_ii_of engelerWithNumerals.toReflexiveDcpo
      engeler_churchTrueN_ne_churchFalseN hcont S
  refine ⟨d, fun n => ?_⟩
  have hchi : chiNum (churchWithNumerals engelerWithNumerals.toReflexiveDcpo
      engeler_churchTrueN_ne_churchFalseN) S n =
      chiNum engelerWithNumerals S n := by
    simp [chiNum, churchWithNumerals_engeler_boolTop,
      churchWithNumerals_engeler_boolBot]
  rw [← hchi, ← churchWithNumerals_engeler_numeral n]
  exact hd n

/-- Engeler `lemma_35` follows from `lemma_35_of`. The original Engeler
proof is unchanged. -/
theorem lemma_35_via_general :
    (∃ U V : Set (Set ℕ), ScottOpen U ∧ ScottOpen V ∧
      engelerWithNumerals.boolTop ∈ U ∧ engelerWithNumerals.boolBot ∉ U ∧
      engelerWithNumerals.boolBot ∈ V ∧ engelerWithNumerals.boolTop ∉ V) ∧
    (∀ m : ℕ, ∃ W : Set (Set ℕ), ScottOpen W ∧
      engelerWithNumerals.numeral m ∈ W ∧
      ∀ n, n ≠ m → engelerWithNumerals.numeral n ∉ W) ∧
    Function.Injective engelerWithNumerals.numeral ∧
    ∀ S : Set ℕ, ∃ d : Set ℕ, ∀ n,
      engelerWithNumerals.app d (engelerWithNumerals.numeral n) =
        chiNum engelerWithNumerals S n :=
  ⟨lemma_35_i_via_general.1, lemma_35_i_via_general.2.1,
    lemma_35_i_via_general.2.2, lemma_35_ii_via_general⟩

end

end Scott2026
