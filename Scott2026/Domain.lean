/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/

import Mathlib.Order.CompleteLattice.Basic
import Mathlib.Order.ScottContinuity
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Set.Lattice
import Mathlib.Data.Set.Countable
import Scott1972.ContinuousLattice.WayBelow

/-!
# Domain theory background (CSL 2026, §4.1) and Proposition 27

§4.1 uses the order-theoretic way-below relation. The 1972 topological
form lives in `Scott1972.ContinuousLattice` and implies this one.
-/

open Set

namespace Scott2026

variable {D E : Type*}

/-- Way-below relation of §4.1, on a complete lattice. -/
def WayBelow [CompleteLattice D] (d e : D) : Prop :=
  ∀ ⦃S : Set D⦄, S.Nonempty → DirectedOn (· ≤ ·) S → e ≤ sSup S → ∃ s ∈ S, d ≤ s

notation:50 d " ≪ " e:50 => WayBelow d e

theorem wayBelow_le [CompleteLattice D] {d e : D} (h : d ≪ e) : d ≤ e := by
  obtain ⟨s, hs, hds⟩ := h (S := {e}) ⟨e, mem_singleton e⟩
    (directedOn_singleton e) (by simp)
  rwa [mem_singleton_iff.mp hs] at hds

/-- Scott 1972 topological `≪` implies the §4.1 interpolative `≪`. -/
theorem wayBelow_of_scott1972 [CompleteLattice D] {d e : D}
    (h : Scott1972.ContinuousLattice.WayBelow d e) : WayBelow d e := by
  intro S hne hdir hele
  obtain ⟨U, hU, heU, hsub⟩ := h
  have : sSup S ∈ U := hU.1 hele heU
  obtain ⟨s, hsS, hsU⟩ := hU.2 hne hdir this
  exact ⟨s, hsS, hsub hsU⟩

/-- A complete lattice is continuous as a dcpo when every element is the
directed supremum of elements way-below it (§4.1). -/
def IsContinuousLattice (D : Type*) [CompleteLattice D] : Prop :=
  ∀ d : D, DirectedOn (· ≤ ·) {e | e ≪ d} ∧ d = sSup {e | e ≪ d}

/-- Scott-continuous maps of §4.1. -/
abbrev IsScottContinuous [Preorder D] [Preorder E] (f : D → E) : Prop :=
  ScottContinuous f

/-- Definition 19: a reflexive dcpo, specialized to complete lattices. -/
structure ReflexiveDcpo (D : Type*) [CompleteLattice D] where
  funMap : D → (D → D)
  lam : (D → D) → D
  fun_scott : IsScottContinuous funMap
  lam_scott : IsScottContinuous lam
  fun_scott_pt : ∀ d, IsScottContinuous (funMap d)
  retract : ∀ f : D → D, IsScottContinuous f → funMap (lam f) = f

/-- Uncurried application associated to a reflexive dcpo. -/
def ReflexiveDcpo.app {D : Type*} [CompleteLattice D] (R : ReflexiveDcpo D)
    (d e : D) : D :=
  R.funMap d e

/-- Finite subsets of `T` are directed under inclusion. -/
theorem finite_subsets_directed {X : Type*} (T : Set X) :
    DirectedOn (· ⊆ ·) {S : Set X | S.Finite ∧ S ⊆ T} := by
  intro S hS U hU
  exact ⟨S ∪ U, ⟨hS.1.union hU.1, union_subset hS.2 hU.2⟩,
    subset_union_left, subset_union_right⟩

/-- The union of the finite subsets of `T` is `T`. -/
theorem sUnion_finite_subsets {X : Type*} (T : Set X) :
    ⋃₀ {S : Set X | S.Finite ∧ S ⊆ T} = T := by
  ext x
  constructor
  · intro hx
    obtain ⟨S, hS, hxS⟩ := mem_sUnion.mp hx
    exact hS.2 hxS
  · intro hx
    exact mem_sUnion.mpr ⟨{x}, ⟨finite_singleton x, singleton_subset_iff.mpr hx⟩,
      mem_singleton x⟩

/-- Proposition 27, one direction: if `S ≪ T` in `Set X`, then `S` is finite
and `S ⊆ T`. -/
theorem prop27_wayBelow_of {X : Type*} {S T : Set X}
    (h : WayBelow (D := Set X) S T) : S.Finite ∧ S ⊆ T := by
  have hdir := finite_subsets_directed T
  have hne : {U : Set X | U.Finite ∧ U ⊆ T}.Nonempty :=
    ⟨∅, finite_empty, empty_subset _⟩
  have hle : T ≤ sSup {U : Set X | U.Finite ∧ U ⊆ T} := by
    intro x hx
    have : x ∈ ⋃₀ {U : Set X | U.Finite ∧ U ⊆ T} := by
      rw [sUnion_finite_subsets]; exact hx
    simpa [sSup_eq_sUnion] using this
  obtain ⟨U, hU, hSU⟩ := h hne hdir hle
  exact ⟨hU.1.subset hSU, hSU.trans hU.2⟩

/-- Proposition 27, converse: a finite subset of `T` is way-below `T`. -/
theorem prop27_wayBelow_finite {X : Type*} {S T : Set X}
    (hS : S.Finite) (hST : S ⊆ T) : WayBelow (D := Set X) S T := by
  intro 𝒟 hne hdir hTle
  have hT : T ⊆ ⋃₀ 𝒟 := by simpa [sSup_eq_sUnion] using hTle
  have : ∀ {S' : Set X} (_hS' : S'.Finite), S' ⊆ T → ∃ U ∈ 𝒟, S' ⊆ U := by
    intro S' hS'
    refine Set.Finite.induction_on (motive := fun S' _ => S' ⊆ T → ∃ U ∈ 𝒟, S' ⊆ U)
      S' hS' ?empty ?insert
    · intro _
      obtain ⟨U, hU⟩ := hne
      exact ⟨U, hU, empty_subset U⟩
    · intro a s ha hs ih hsT
      have hs_sub : s ⊆ T := (subset_insert a s).trans hsT
      obtain ⟨U, hU, hUs⟩ := ih hs_sub
      have haT : a ∈ T := hsT (mem_insert a s)
      obtain ⟨V, hV, haV⟩ := mem_sUnion.mp (hT haT)
      obtain ⟨W, hW, hUW, hVW⟩ := hdir U hU V hV
      exact ⟨W, hW, insert_subset (hVW haV) (hUs.trans hUW)⟩
  exact this hS hST

/-- Proposition 27: `S ≪ T` in `𝒫(X)` iff `S` is finite and `S ⊆ T`. -/
theorem prop27_wayBelow_iff {X : Type*} {S T : Set X} :
    WayBelow (D := Set X) S T ↔ S.Finite ∧ S ⊆ T :=
  ⟨prop27_wayBelow_of, fun h => prop27_wayBelow_finite h.1 h.2⟩

/-- The way-below sets in `𝒫(X)` are exactly the finite subsets. -/
theorem wayBelow_set_eq {X : Type*} (T : Set X) :
    {S : Set X | S ≪ T} = {S | S.Finite ∧ S ⊆ T} := by
  ext S
  exact prop27_wayBelow_iff

/-- Proposition 27: `𝒫(X)` is a continuous lattice, with finite subsets as a base. -/
theorem isContinuousLattice_set (X : Type*) : IsContinuousLattice (Set X) := by
  intro T
  rw [wayBelow_set_eq]
  exact ⟨finite_subsets_directed T,
    ((sSup_eq_sUnion _).trans (sUnion_finite_subsets T)).symm⟩

/-- If `X` is countable, its finite subsets form a countable family. -/
theorem finite_subsets_countable {X : Type*} [Countable X] :
    Set.Countable {S : Set X | S.Finite} := by
  classical
  have hrange :
      {S : Set X | S.Finite} =
        Set.range (fun s : Finset X => (s : Set X)) := by
    ext S
    constructor
    · intro hS
      exact ⟨hS.toFinset, hS.coe_toFinset⟩
    · rintro ⟨s, rfl⟩
      exact s.finite_toSet
  rw [hrange]
  exact Set.countable_range _

/-- All clauses of Proposition 27. The ambient `CompleteLattice (Set X)`
instance supplies the complete-lattice (hence dcpo) clause. -/
def Proposition27Statement (X : Type*) : Prop :=
  IsContinuousLattice (Set X) ∧
    (∀ S T : Set X, WayBelow (D := Set X) S T ↔ S.Finite ∧ S ⊆ T) ∧
    (∀ T : Set X,
      DirectedOn (· ⊆ ·) {S : Set X | S.Finite ∧ S ⊆ T} ∧
        T = sSup {S : Set X | S.Finite ∧ S ⊆ T}) ∧
    (Countable X → Set.Countable {S : Set X | S.Finite})

/-- Proposition 27 with its lattice, way-below, finite-base, and countable-base
clauses packaged together. -/
theorem proposition27_full (X : Type*) : Proposition27Statement X := by
  refine ⟨isContinuousLattice_set X, fun _ _ => prop27_wayBelow_iff,
    fun T => ⟨finite_subsets_directed T, ?_⟩, ?_⟩
  · exact ((sSup_eq_sUnion _).trans (sUnion_finite_subsets T)).symm
  · intro hX
    letI : Countable X := hX
    exact finite_subsets_countable

/-!
## Scott-open sets (Lemma 35(i))

Wrappers around Scott 1972 `ScottOpen` used to separate Booleans and
numerals in the Scott topology of a complete lattice (and of `𝒫(X)`).
-/

/-- Scott-open sets of a complete lattice (Scott 1972 induced topology). -/
abbrev ScottOpen {D : Type*} [CompleteLattice D] (U : Set D) : Prop :=
  Scott1972.ContinuousLattice.ScottOpen U

/-- The complement of a principal down-set is Scott-open. -/
theorem scottOpen_not_le {D : Type*} [CompleteLattice D] (L : D) :
    ScottOpen {z : D | ¬ z ≤ L} := by
  refine ⟨fun a b hab ha hb => ha (le_trans hab hb), fun S _hSne _hSdir hmem => ?_⟩
  by_contra hcon
  refine hmem (sSup_le fun s hs => ?_)
  by_contra hsL
  exact hcon ⟨s, hs, hsL⟩

/-- Membership sets `{s | a ∈ s}` are Scott-open in `𝒫(X)`. -/
theorem scottOpen_mem {X : Type*} (a : X) :
    ScottOpen {s : Set X | a ∈ s} := by
  refine ⟨?upper, ?inacc⟩
  · intro s t hst hs
    have hsub : s ⊆ t := hst
    exact hsub hs
  · intro 𝒟 _hne _hdir hmem
    have : a ∈ ⋃₀ 𝒟 := by
      simpa [sSup_eq_sUnion] using hmem
    obtain ⟨s, hs𝒟, has⟩ := mem_sUnion.mp this
    exact ⟨s, hs𝒟, has⟩

/-- Scott topologies of complete lattices are T₀: unequal points are
separated by a Scott-open. -/
theorem exists_scottOpen_separates {D : Type*} [CompleteLattice D]
    {x y : D} (h : x ≠ y) :
    ∃ U : Set D, ScottOpen U ∧ ((x ∈ U ∧ y ∉ U) ∨ (y ∈ U ∧ x ∉ U)) := by
  by_cases hxy : x ≤ y
  · have hyx : ¬ y ≤ x := fun hyx => h (le_antisymm hxy hyx)
    refine ⟨{z | ¬ z ≤ x}, scottOpen_not_le x, Or.inr ⟨hyx, ?_⟩⟩
    exact fun hx => hx le_rfl
  · refine ⟨{z | ¬ z ≤ y}, scottOpen_not_le y, Or.inl ⟨hxy, ?_⟩⟩
    exact fun hy => hy le_rfl

/-- Preimages of Scott-open sets under Scott-continuous maps are Scott-open. -/
theorem scottOpen_preimage {D E : Type*} [CompleteLattice D] [CompleteLattice E]
    {f : D → E} (hf : IsScottContinuous f) {U : Set E} (hU : ScottOpen U) :
    ScottOpen (f ⁻¹' U) := by
  have hmono : Monotone f := hf.monotone
  refine ⟨fun a b hab ha => hU.1 (hmono hab) ha, fun S hS hSdir hmem => ?_⟩
  have hfS : IsLUB (f '' S) (f (sSup S)) := hf hS hSdir (isLUB_sSup S)
  have hsupU : sSup (f '' S) ∈ U := by
    rwa [hfS.sSup_eq]
  have hdirf : DirectedOn (· ≤ ·) (f '' S) := by
    intro y hy z hz
    obtain ⟨s, hs, rfl⟩ := (mem_image _ _ _).mp hy
    obtain ⟨t, ht, rfl⟩ := (mem_image _ _ _).mp hz
    obtain ⟨u, hu, hsu, htu⟩ := hSdir s hs t ht
    exact ⟨f u, mem_image_of_mem f hu, hmono hsu, hmono htu⟩
  obtain ⟨y, hyS, hyU⟩ := hU.2 (hS.image f) hdirf hsupU
  obtain ⟨a, haS, rfl⟩ := (mem_image _ _ _).mp hyS
  exact ⟨a, haS, hyU⟩

end Scott2026
