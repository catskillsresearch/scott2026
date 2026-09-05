/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/

import Scott2026.BooleanLogic
import Scott2026.Setoid
import Scott2026.RelFun
import Scott2026.PowerSet
import Scott2026.Domain
import Scott2026.Lambda
import Scott2026.Engeler
import Scott2026.Random

/-!
# Scott 2026 — Interpreting Lambda Calculus in Domain-Valued Random Variables

Primary source: Furber, Mardare, Panangaden, and Scott, LIPIcs CSL 2026, Article 48.
Working transcription: `sources/Scott2026_vision.md`.

This module re-exports the sorry-free development.
-/

namespace Scott2026

/-- Temporary Palomar hook; replace once the compared inventory is chosen. -/
theorem scaffold_placeholder : True := trivial

/-- Lemma 12: `A`-monotone maps are functional. -/
theorem lemma_12 {A : Type*} [CompleteBooleanAlgebra A] {X Y : Type*}
    (P : APoset (A := A) X) (Q : APoset (A := A) Y) {f : X → Y}
    (hf : APoset.AMonotone P Q f) :
    APoset.Functional P.toASetoid Q.toASetoid f :=
  APoset.AMonotone.functional (P := P) (Q := Q) hf

/-- Theorem 17, mixing witness on `A`-subsets. -/
theorem theorem_17_mix {A : Type*} [CompleteBooleanAlgebra A] {X ι : Type*}
    (a : ι → A) (u : ι → ASubset A X) (x : X) :
    mixSubset a u x = ⨆ i, a i ⊓ u i x :=
  rfl

/-- Proposition 27: `S ≪ T` in `𝒫(X)` iff `S` is finite and `S ⊆ T`. -/
theorem proposition_27 {X : Type*} {S T : Set X} :
    WayBelow (D := Set X) S T ↔ S.Finite ∧ S ⊆ T :=
  prop27_wayBelow_iff

/-- Proposition 27: `𝒫(X)` is a continuous lattice. -/
theorem proposition_27_continuous (X : Type*) : IsContinuousLattice (Set X) :=
  isContinuousLattice_set X

/-- Theorem 17: `𝒫^A(X)` is a complete `A`-setoid. -/
theorem theorem_17_complete {A : Type*} [CompleteBooleanAlgebra A] {X : Type*} :
    (powerSetoid (A := A) (X := X)).IsComplete :=
  powerSetoid_isComplete

/-- Proposition 28, totality and strictness of `𝒫^A(X)` on a ground type. -/
theorem proposition_28_total {A : Type*} [CompleteBooleanAlgebra A] {X : Type*} :
    (powerSetoid (A := A) (X := X)).IsTotal :=
  powerSetoid_isTotal

theorem proposition_28_strict {A : Type*} [CompleteBooleanAlgebra A] {X : Type*} :
    (powerSetoid (A := A) (X := X)).IsStrict :=
  powerSetoid_isStrict

/-- Proposition 29, retract identity for maps determined by finite sets. -/
theorem proposition_29 {E : Type*} [DecidableEq E] (pair : Finset E × E → E)
    (hpair : Function.Injective pair) {f : Set E → Set E}
    (hf : DeterminedByFinite f) (X : Set E) :
    engelerApp pair (engelerLam pair f) X = f X :=
  prop29_retract pair hpair hf X

/-- Lemma 41: constant random variables map to check-sets. -/
theorem lemma_41_const {X Y : Type*} [MeasurableSpace X] (S : Set Y) :
    G_pre (constRV (X := X) S) = checkSet (A := Set X) S :=
  lemma_41 S

end Scott2026
