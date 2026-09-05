/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/

import Mathlib.Data.Finset.Basic
import Mathlib.Order.ScottContinuity
import Scott2026.Domain

/-!
# The Engeler model (Proposition 29) and numerals (Definition 32)
-/

open Set

namespace Scott2026

variable {E : Type*}

/-- Application in the Engeler model (Proposition 29). -/
def engelerApp [DecidableEq E] (pair : Finset E × E → E) (F X : Set E) : Set E :=
  {q | ∃ K : Finset E, (↑K : Set E) ⊆ X ∧ pair (K, q) ∈ F}

/-- Abstraction in the Engeler model (Proposition 29). -/
def engelerLam [DecidableEq E] (pair : Finset E × E → E) (f : Set E → Set E) : Set E :=
  {x | ∃ K : Finset E, ∃ q ∈ f (↑K), x = pair (K, q)}

/-- Proposition 29, retract identity: `lam f · X = ⋃ {f K | K ⊆ X finite}`
when `pair` is injective. -/
theorem engelerApp_lam [DecidableEq E] (pair : Finset E × E → E)
    (hpair : Function.Injective pair) (f : Set E → Set E) (X : Set E) :
    engelerApp pair (engelerLam pair f) X = {q | ∃ K : Finset E, (↑K : Set E) ⊆ X ∧ q ∈ f (↑K)} := by
  ext q
  simp only [engelerApp, engelerLam, Set.mem_setOf_eq]
  constructor
  · intro ⟨K, hK, hx⟩
    obtain ⟨K', q', hq', heq⟩ := hx
    have hKK : (K, q) = (K', q') := hpair heq
    cases hKK
    exact ⟨K, hK, hq'⟩
  · intro ⟨K, hK, hq⟩
    exact ⟨K, hK, ⟨K, q, hq, rfl⟩⟩

/-- A map `Set E → Set E` is determined by its values on finite sets iff it
preserves directed unions of finite subsets. This is the Scott-continuity
criterion used in Proposition 29. -/
def DeterminedByFinite (f : Set E → Set E) : Prop :=
  ∀ X : Set E, f X = {q | ∃ K : Finset E, (↑K : Set E) ⊆ X ∧ q ∈ f (↑K)}

/-- Proposition 29: if `f` is determined by finite sets, then `fun ∘ lam = id`. -/
theorem prop29_retract [DecidableEq E] (pair : Finset E × E → E)
    (hpair : Function.Injective pair) {f : Set E → Set E} (hf : DeterminedByFinite f) (X : Set E) :
    engelerApp pair (engelerLam pair f) X = f X := by
  rw [engelerApp_lam pair hpair, hf X]

/-- Determined-by-finite maps are monotone. -/
theorem DeterminedByFinite.monotone {f : Set E → Set E} (hf : DeterminedByFinite f) :
    Monotone f := by
  intro X Y hXY q hq
  have hq' : q ∈ {q | ∃ K : Finset E, (↑K : Set E) ⊆ X ∧ q ∈ f (↑K)} := by
    simpa [hf X] using hq
  obtain ⟨K, hK, hqK⟩ := hq'
  have : q ∈ {q | ∃ K : Finset E, (↑K : Set E) ⊆ Y ∧ q ∈ f (↑K)} :=
    ⟨K, hK.trans hXY, hqK⟩
  simpa [hf Y] using this

/-- Scott-continuous maps `Set E → Set E` are determined by finite sets. -/
theorem determinedByFinite_of_scottContinuous {f : Set E → Set E}
    (hf : ScottContinuous f) : DeterminedByFinite f := by
  intro X
  let 𝒟 : Set (Set E) := {S | S.Finite ∧ S ⊆ X}
  have hdir := finite_subsets_directed X
  have hne : 𝒟.Nonempty := ⟨∅, finite_empty, empty_subset _⟩
  have hlub : IsLUB 𝒟 X := by
    refine ⟨?upper, ?least⟩
    · intro S hS
      exact hS.2
    · intro T hT
      rw [← sUnion_finite_subsets X]
      intro x hx
      obtain ⟨S, hS, hxS⟩ := (mem_sUnion.mp hx)
      exact hT hS hxS
  have hsup : ⋃₀ (f '' 𝒟) = f X := by
    simpa [sSup_eq_sUnion] using (hf hne hdir hlub).sSup_eq
  ext q
  constructor
  · intro hq
    have : q ∈ ⋃₀ (f '' 𝒟) := by rwa [hsup]
    obtain ⟨t, ht, hqt⟩ := mem_sUnion.mp this
    obtain ⟨S, hS, rfl⟩ := (Set.mem_image _ _ _).mp ht
    refine ⟨hS.1.toFinset, ?_, ?_⟩
    · simpa [hS.1.coe_toFinset] using hS.2
    · simpa [hS.1.coe_toFinset] using hqt
  · intro ⟨K, hK, hq⟩
    have ht : f (↑K) ∈ f '' 𝒟 := ⟨↑K, ⟨K.finite_toSet, hK⟩, rfl⟩
    have : q ∈ ⋃₀ (f '' 𝒟) := mem_sUnion.mpr ⟨f (↑K), ht, hq⟩
    rwa [hsup] at this

/-- A finite set contained in the directed lub of `𝒟` sits in some member
of `𝒟` (Proposition 27). -/
theorem finset_subset_of_directed_isLUB {𝒟 : Set (Set E)} {X : Set E}
    (hne : 𝒟.Nonempty) (hdir : DirectedOn (· ≤ ·) 𝒟) (hlub : IsLUB 𝒟 X)
    {K : Finset E} (hK : (↑K : Set E) ⊆ X) :
    ∃ Y ∈ 𝒟, (↑K : Set E) ⊆ Y :=
  prop27_wayBelow_finite K.finite_toSet hK hne hdir (le_of_eq hlub.sSup_eq.symm)

/-- Application is Scott-continuous in the argument, for each fixed function
graph `F`. -/
theorem engelerApp_scottContinuous_right [DecidableEq E]
    (pair : Finset E × E → E) (F : Set E) :
    ScottContinuous (engelerApp pair F) := by
  intro 𝒟 hne hdir X hlub
  have hunion : ⋃₀ (engelerApp pair F '' 𝒟) = engelerApp pair F X := by
    ext q
    constructor
    · intro hq
      obtain ⟨Y, hY, hqY⟩ := mem_sUnion.mp hq
      obtain ⟨S, hS, rfl⟩ := (mem_image _ _ _).mp hY
      obtain ⟨K, hK, hp⟩ := hqY
      exact ⟨K, hK.trans (hlub.1 hS), hp⟩
    · intro hq
      obtain ⟨K, hK, hp⟩ := hq
      obtain ⟨S, hS, hKS⟩ := finset_subset_of_directed_isLUB hne hdir hlub hK
      exact mem_sUnion.mpr ⟨engelerApp pair F S, mem_image_of_mem _ hS, ⟨K, hKS, hp⟩⟩
  simpa [sSup_eq_sUnion, hunion] using isLUB_sSup (engelerApp pair F '' 𝒟)

/-- Application is Scott-continuous (in fact completely additive) in the
function graph, for each fixed argument `X`. -/
theorem engelerApp_scottContinuous_left [DecidableEq E]
    (pair : Finset E × E → E) (X : Set E) :
    ScottContinuous (fun F => engelerApp pair F X) := by
  intro 𝒮 _hne _hdir G hlub
  have hunion : ⋃₀ ((fun F => engelerApp pair F X) '' 𝒮) = engelerApp pair G X := by
    ext q
    constructor
    · intro hq
      obtain ⟨Y, hY, hqY⟩ := mem_sUnion.mp hq
      obtain ⟨F, hF, rfl⟩ := (mem_image _ _ _).mp hY
      obtain ⟨K, hK, hp⟩ := hqY
      exact ⟨K, hK, hlub.1 hF hp⟩
    · intro hq
      obtain ⟨K, hK, hp⟩ := hq
      have : pair (K, q) ∈ ⋃₀ 𝒮 := by
        rwa [← sSup_eq_sUnion, hlub.sSup_eq]
      obtain ⟨F, hF, hFp⟩ := mem_sUnion.mp this
      exact mem_sUnion.mpr
        ⟨engelerApp pair F X, mem_image_of_mem _ hF, ⟨K, hK, hFp⟩⟩
  simpa [sSup_eq_sUnion, hunion] using
    isLUB_sSup ((fun F => engelerApp pair F X) '' 𝒮)

/-- Uncurried application `funMap := engelerApp pair` is Scott-continuous as a
map `𝒫(E) → (𝒫(E) → 𝒫(E))` into the pointwise function space. -/
theorem engelerApp_scottContinuous [DecidableEq E]
    (pair : Finset E × E → E) :
    ScottContinuous (engelerApp pair) := by
  intro 𝒮 hne hdir G hlub
  refine isLUB_pi.mpr fun X => ?_
  have himg : Function.eval X '' (engelerApp pair '' 𝒮) =
      (fun F => engelerApp pair F X) '' 𝒮 := by
    rw [← image_comp]
    rfl
  rw [himg]
  exact engelerApp_scottContinuous_left pair X hne hdir hlub

/-- Abstraction preserves arbitrary suprema (complete additivity). Pair
injectivity is not required. -/
theorem engelerLam_sSup [DecidableEq E] (pair : Finset E × E → E)
    (𝒟 : Set (Set E → Set E)) :
    engelerLam pair (sSup 𝒟) = ⋃₀ (engelerLam pair '' 𝒟) := by
  ext x
  constructor
  · intro hx
    obtain ⟨K, q, hq, rfl⟩ := hx
    have hq' : q ∈ ⋃₀ (Function.eval (↑K : Set E) '' 𝒟) := by
      simpa [sSup_apply_eq_sSup_image, sSup_eq_sUnion] using hq
    obtain ⟨Y, hY, hqY⟩ := mem_sUnion.mp hq'
    obtain ⟨f, hf, rfl⟩ := (mem_image _ _ _).mp hY
    exact mem_sUnion.mpr ⟨engelerLam pair f, mem_image_of_mem _ hf, ⟨K, q, hqY, rfl⟩⟩
  · intro hx
    obtain ⟨Y, hY, hxY⟩ := mem_sUnion.mp hx
    obtain ⟨f, hf, rfl⟩ := (mem_image _ _ _).mp hY
    obtain ⟨K, q, hq, rfl⟩ := hxY
    refine ⟨K, q, ?_, rfl⟩
    have : q ∈ sSup (Function.eval (↑K : Set E) '' 𝒟) := by
      simpa [sSup_eq_sUnion] using
        (mem_sUnion.mpr ⟨f (↑K), mem_image_of_mem _ hf, hq⟩ : q ∈ ⋃₀ (Function.eval (↑K : Set E) '' 𝒟))
    simpa [sSup_apply_eq_sSup_image] using this

/-- Abstraction is Scott-continuous as a map `[𝒫(E) → 𝒫(E)] → 𝒫(E)`. -/
theorem engelerLam_scottContinuous [DecidableEq E]
    (pair : Finset E × E → E) :
    ScottContinuous (engelerLam pair) := by
  intro 𝒟 _hne _hdir f hlub
  have hunion : ⋃₀ (engelerLam pair '' 𝒟) = engelerLam pair f := by
    rw [← engelerLam_sSup, hlub.sSup_eq]
  simpa [sSup_eq_sUnion, hunion] using isLUB_sSup (engelerLam pair '' 𝒟)

/-- Proposition 29 retract on Scott-continuous maps: `fun ∘ lam = id` on
`[𝒫(E) → 𝒫(E)]`. -/
theorem engeler_retract_scott [DecidableEq E] (pair : Finset E × E → E)
    (hpair : Function.Injective pair) {f : Set E → Set E}
    (hf : ScottContinuous f) (X : Set E) :
    engelerApp pair (engelerLam pair f) X = f X :=
  prop29_retract pair hpair (determinedByFinite_of_scottContinuous hf) X

/-- The Engeler model `(𝒫(E), ⊆, ·, lam)` as a reflexive dcpo. -/
def engelerReflexiveDcpo [DecidableEq E]
    (pair : Finset E × E → E) (hpair : Function.Injective pair) :
    ReflexiveDcpo (Set E) where
  funMap := engelerApp pair
  lam := engelerLam pair
  fun_scott := engelerApp_scottContinuous pair
  lam_scott := engelerLam_scottContinuous pair
  fun_scott_pt := fun F => engelerApp_scottContinuous_right pair F
  retract := fun f hf => funext (engeler_retract_scott (f := f) pair hpair hf)

/-- Proposition 29 (paper): `(𝒫(E), ⊆, ·, lam)` is a reflexive dcpo.
Application and abstraction are Scott-continuous, and `fun ∘ lam = id` on
Scott-continuous maps `𝒫(E) → 𝒫(E)`. The existing `proposition_29` is the
weaker retract on `DeterminedByFinite`. -/
theorem proposition_29_full [DecidableEq E] (pair : Finset E × E → E)
    (hpair : Function.Injective pair) :
    (engelerReflexiveDcpo pair hpair).funMap =
      (fun F X => engelerApp pair F X) ∧
    (engelerReflexiveDcpo pair hpair).lam = engelerLam pair ∧
    IsScottContinuous (engelerReflexiveDcpo pair hpair).funMap ∧
    IsScottContinuous (engelerReflexiveDcpo pair hpair).lam ∧
    (∀ F, IsScottContinuous ((engelerReflexiveDcpo pair hpair).funMap F)) ∧
    (∀ f : Set E → Set E, IsScottContinuous f →
      (engelerReflexiveDcpo pair hpair).funMap
        ((engelerReflexiveDcpo pair hpair).lam f) = f) :=
  ⟨rfl, rfl,
    (engelerReflexiveDcpo pair hpair).fun_scott,
    (engelerReflexiveDcpo pair hpair).lam_scott,
    (engelerReflexiveDcpo pair hpair).fun_scott_pt,
    (engelerReflexiveDcpo pair hpair).retract⟩

/-- Definition 32: a reflexive dcpo with numerals. We record the algebraic
interface (distinct Booleans, `if`/`succ`/`pred`/`0?`) without a particular
encoding of closed terms as domain elements. -/
structure ReflexiveDcpoWithNumerals (D : Type*) [CompleteLattice D]
    extends ReflexiveDcpo D where
  boolBot : D
  boolTop : D
  numeral : ℕ → D
  bool_ne : boolBot ≠ boolTop
  numeral_inj : Function.Injective numeral

/-- Characteristic function of a set of numerals, valued in `{⊥, ⊤}` (before Lemma 35). -/
noncomputable def chiNum {D : Type*} [CompleteLattice D] (R : ReflexiveDcpoWithNumerals D)
    (S : Set ℕ) (n : ℕ) : D :=
  @ite D (n ∈ S) (Classical.propDecidable _) R.boolTop R.boolBot

/-- Lemma 35(ii), given a Scott-continuous extension of `χ_A` off the numerals. -/
theorem lemma_35_ii_of_extension {D : Type*} [CompleteLattice D]
    (R : ReflexiveDcpoWithNumerals D) (S : Set ℕ) (g : D → D)
    (hg : IsScottContinuous g) (hgS : ∀ n, g (R.numeral n) = chiNum R S n) (n : ℕ) :
    R.app (R.lam g) (R.numeral n) = chiNum R S n := by
  rw [ReflexiveDcpo.app, R.retract g hg, hgS]

/-- Proposition 36: `S₁ ≤_m S₂` via a numeral-to-numeral λ-term `f` and oracles. -/
def ManyOneLe {D : Type*} [CompleteLattice D] (R : ReflexiveDcpoWithNumerals D)
    (S₁ S₂ : Set ℕ) : Prop :=
  ∃ f : ℕ → ℕ,
    ∃ d₁ d₂ : D,
      (∀ n, R.app d₁ (R.numeral n) = chiNum R S₁ n) ∧
      (∀ n, R.app d₂ (R.numeral n) = chiNum R S₂ n) ∧
      (∀ n, R.app d₂ (R.numeral (f n)) = R.app d₁ (R.numeral n))

end Scott2026
