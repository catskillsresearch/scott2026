/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/

import Scott2026.BooleanLogic
import Scott2026.Setoid
import Scott2026.RelFun
import Scott2026.PowerSet
import Scott2026.Oid
import Scott2026.Domain
import Scott2026.Lambda
import Scott2026.Engeler
import Scott2026.Random
import Scott2026.VA

universe u

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

/-- Definition 4: the two completeness conditions on an `A`-setoid agree. The converse
direction refines a compatible family by a maximal pairwise disjoint family with the
same join. -/
theorem definition_4 {A : Type*} [CompleteBooleanAlgebra A] {X : Type*}
    (S : ASetoid (A := A) X) : S.IsComplete ↔ S.IsCompleteDisjoint :=
  ASetoid.isComplete_iff_isCompleteDisjoint S

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

/-- Jech 14.15: `‖x = x‖ = 1` in `V^A`. -/
theorem jech_lemma_14_15 {A : Type*} [CompleteBooleanAlgebra A] (x : AName A) :
    AName.eqB x x = ⊤ :=
  AName.eqB_self x

/-- Jech 14.16: transitivity of equality and substitution into membership. -/
theorem jech_lemma_14_16 {A : Type u} [CompleteBooleanAlgebra A]
    (x y z : AName A) :
    (AName.eqB x y ⊓ AName.eqB y z ≤ AName.eqB x z) ∧
    (AName.memB x y ⊓ AName.eqB x z ≤ AName.memB z y) ∧
    (AName.memB y x ⊓ AName.eqB x z ≤ AName.memB y z) :=
  AName.model_laws x y z

/-- Jech 14.18: mix of an antichain of names. -/
theorem jech_lemma_14_18 {A ι : Type u} [CompleteBooleanAlgebra A]
    (u : ι → A) (xs : ι → AName A)
    (hdis : Pairwise fun i j => u i ⊓ u j = ⊥) (i : ι) :
    u i ≤ AName.eqB (AName.mix u xs) (xs i) :=
  AName.mix_le_eqB u xs hdis i

/-- Definition 14: `Oid(X)` is the `A`-setoid on `dom(X)` whose equality is equation (3),
`‖x = y‖_X = ‖x ∈ X‖ ⊓ ‖y ∈ X‖ ⊓ ‖x = y‖`. Symmetry and transitivity are the
`ASetoid` fields of `oid`. -/
theorem definition_14 {A : Type u} [CompleteBooleanAlgebra A]
    (X : AName.{u} A) (i j : X.idx) :
    (oid X).eq i j =
      AName.memB (X.child i) X ⊓ AName.memB (X.child j) X ⊓
        AName.eqB (X.child i) (X.child j) :=
  oid_eq X i j

/-- Definition 15: for `‖S ⊆ X‖ = 1`, `e(S)(x) = ‖x ∈ S‖` is a predicate on `Oid(X)`;
`ePred` carries the two predicate conditions of Definition 7. -/
theorem definition_15 {A : Type u} [CompleteBooleanAlgebra A]
    (X S : AName.{u} A) (h : AName.subsetB S X = ⊤) (i : X.idx) :
    (ePred X S h).val i = AName.memB (X.child i) S :=
  ePred_val X S h i

/-- Definition 16 on objects and morphisms: `Oid(F)(x, y) = ‖(x,y)^A ∈ F‖` is a
relational function `Oid(X) → Oid(Y)` for every function name `F : X →_A Y`. -/
theorem definition_16 {A : Type u} [CompleteBooleanAlgebra A]
    (X Y F : AName.{u} A) (h : isFunctionB F X Y = ⊤) (i : X.idx) (j : Y.idx) :
    (oidRel X Y F h).val i j = AName.memB (opairB (X.child i) (Y.child j)) F :=
  oidRel_val X Y F h i j

/-- Definition 16, functoriality on identities. -/
theorem definition_16_id {A : Type u} [CompleteBooleanAlgebra A]
    (X : AName.{u} A) (i j : X.idx) :
    (oidRel X X (idB X) (isFunctionB_id X)).val i j = (RelFun.id (oid X)).val i j :=
  oidRel_id X i j

/-- Definition 16, functoriality on composites. -/
theorem definition_16_comp {A : Type u} [CompleteBooleanAlgebra A]
    {X Y Z f g : AName.{u} A} (hf : isFunctionB f X Y = ⊤) (hg : isFunctionB g Y Z = ⊤)
    (i : X.idx) (k : Z.idx) :
    (oidRel X Z (compB g f X Z) (isFunctionB_comp hf hg)).val i k =
      ((oidRel Y Z g hg).comp (oidRel X Y f hf)).val i k :=
  oidRel_comp hf hg i k

-- Jech 14.19, CSL Theorem 1(iii), and Jech 14.21 are `jech_lemma_14_19`,
-- `theorem_1_iii`, and `jech_lemma_14_21` from `Scott2026.VA`.
--
-- After Theorem 2 (CSL p.3–4): `memB_powerB`, pairing identities
-- `eqB_singletonB` / `eqB_pairB` / `eqB_opairB`, check commutation
-- `check_singleton` / `check_pair` / `check_opair`, inductiveness and
-- leastness of `check ω` (`check_omega_inductive`, `check_omega_least`),
-- CSL Proposition 3 (`proposition_3`), and the internal function object
-- (`isFunctionB`, `funsB`, `homB`, `idB`, `compB`, `isFunctionB_id`,
-- `isFunctionB_comp`, `compB_congr`) are from `Scott2026.VA`.
-- This is not Theorem 1(i) or 1(ii).
--
-- §3 through Definition 16 (CSL p.4–6): `oid` / `oid_eq` / `oid_eps` (Definition 14),
-- `ePred` / `ePredPowerB` (Definition 15), `oidRel` / `oidRel_id` / `oidRel_comp`
-- (Definition 16) from `Scott2026.Oid`, with `RelFun.comp` (Definition 8 composition)
-- from `Scott2026.RelFun`. Definition 16 is proved only as functor data: fullness,
-- faithfulness and essential surjectivity of `Oid`, hence `Set_A ≃ SetoidR_A`, are not
-- claimed, and neither are Theorem 17, Corollary 18 or Proposition 28 at the
-- `Oid(P^A(X))` level (`theorem_17_*` / `proposition_28_*` are ground-type results).

end Scott2026
