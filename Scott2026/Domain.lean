/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/

import Mathlib.Order.CompleteLattice.Basic
import Mathlib.Order.ScottContinuity
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Set.Lattice
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

end Scott2026
