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
import Scott2026.RawPowerStrict
import Scott2026.Domain
import Scott2026.Lambda
import Scott2026.Interp
import Scott2026.InterpVA
import Scott2026.Lemma31
import Scott2026.Corollary34
import Scott2026.Prop36
import Scott2026.LambdaVA
import Scott2026.Engeler
import Scott2026.EngelerVA
import Scott2026.Random
import Scott2026.Coin
import Scott2026.VA

universe u v

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
    (S : ASetoid (A := A) X) :
    ASetoid.IsComplete.{v} S ↔ ASetoid.IsCompleteDisjoint.{v} S :=
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

/-- Theorem 17 at the `V^A` level: `Oid(P^A(X))` is complete. This is not the
ground-type `theorem_17_complete`. -/
theorem theorem_17_va_complete {A : Type u} [CompleteBooleanAlgebra A]
    (X : AName.{u} A) : (oid (powerB X)).IsComplete :=
  oid_powerB_isComplete X

/-- Theorem 17, totality of `Oid(P^A(X))`. -/
theorem theorem_17_va_total {A : Type u} [CompleteBooleanAlgebra A]
    (X : AName.{u} A) : (oid (powerB X)).IsTotal :=
  oid_powerB_isTotal X

/-- Theorem 17, moreover: a congruent predicate on subsets of `X` is realized
by an element of `Oid(P^A(X))`. -/
theorem theorem_17_va_full {A : Type u} [CompleteBooleanAlgebra A]
    (X : AName.{u} A) (Φ : AName.{u} A → A)
    (hcongr : ∀ S T, AName.eqB S T ⊓ Φ S ≤ Φ T) (a : A)
    (ha : a = ⨆ S, AName.memB S (powerB X) ⊓ Φ S) :
    ∃ p : (powerB X).idx, Φ ((powerB X).child p) = a :=
  oid_powerB_full X Φ hcongr a ha

/-- Proposition 28: `Oid(P^A(X))` is complete. Thin export of Theorem 17. This is
not ground-type `theorem_17_complete`. -/
theorem proposition_28_va_complete {A : Type u} [CompleteBooleanAlgebra A]
    (X : AName.{u} A) : (oid (powerB X)).IsComplete :=
  theorem_17_va_complete X

/-- Proposition 28: `Oid(P^A(X))` is total. Thin export of Theorem 17. This is
not ground-type `proposition_28_total`. -/
theorem proposition_28_va_total {A : Type u} [CompleteBooleanAlgebra A]
    (X : AName.{u} A) : (oid (powerB X)).IsTotal :=
  theorem_17_va_total X

/-- Proposition 28, canonical equality at `X = check Y`: Boolean equality of
children implies equality of the canonical names. This is not index-level
`IsStrict` and is not ground-type `proposition_28_strict`. -/
theorem proposition_28_va_canonical_eq {A : Type u} [CompleteBooleanAlgebra A]
    (Y : PSet.{u}) {p q : (powerB (AName.check (A := A) Y)).idx}
    (h : (oid (powerB (AName.check (A := A) Y))).eq p q = ⊤) :
    restrictName ((powerB (AName.check (A := A) Y)).child p)
      (AName.check (A := A) Y) =
    restrictName ((powerB (AName.check (A := A) Y)).child q)
      (AName.check (A := A) Y) :=
  oid_powerB_check_canonical_eq Y h

/-- Definition 11 on `P^A(X)`: symmetrized Boolean inclusion is `Oid(P^A(X))`
equality. -/
theorem definition_11_powerB {A : Type u} [CompleteBooleanAlgebra A]
    (X : AName.{u} A) (p q : (powerB X).idx) :
    (powerBPoset X).eq p q = (oid (powerB X)).eq p q :=
  powerBPoset_eq X p q

/-- Proposition 28, totality of the canonical (fixed-point) carrier of `P^A(X)`.
This is not raw `proposition_28_va_total`. -/
theorem proposition_28_va_canonical_total {A : Type u} [CompleteBooleanAlgebra A]
    (X : AName.{u} A) : (canonicalPowerSetoid X).IsTotal :=
  canonicalPowerSetoid_isTotal X

/-- Proposition 28, strictness of the canonical (fixed-point) carrier of
`P^A(X)`. Boolean equality at `⊤` equates membership values; fixed-point
hypotheses equate indices. This is not raw index-level `IsStrict` and is not
ground-type `proposition_28_strict`. -/
theorem proposition_28_va_canonical_strict {A : Type u} [CompleteBooleanAlgebra A]
    (X : AName.{u} A) : (canonicalPowerSetoid X).IsStrict :=
  canonicalPowerSetoid_isStrict X

/-- Proposition 28, completeness of the canonical carrier: mix on the raw
carrier, then normalize. This is not raw `proposition_28_va_complete`. -/
theorem proposition_28_va_canonical_complete {A : Type u}
    [CompleteBooleanAlgebra A] (X : AName.{u} A) :
    (canonicalPowerSetoid X).IsComplete :=
  canonicalPowerSetoid_isComplete X

/-- Definition 11 on the canonical carrier: symmetrized inclusion is canonical
`Oid` equality. -/
theorem definition_11_canonicalPowerB {A : Type u} [CompleteBooleanAlgebra A]
    (X : AName.{u} A) (p q : CanonicalPowerIdx X) :
    (canonicalPowerPoset X).eq p q = (canonicalPowerSetoid X).eq p q :=
  canonicalPowerPoset_eq X p q

/-- Corollary 18: `Oid(P^A(X ×_A Y))` is complete. -/
theorem corollary_18_prod {A : Type u} [CompleteBooleanAlgebra A]
    (X Y : AName.{u} A) : (oid (powerB (prodB X Y))).IsComplete :=
  oid_prodB_isComplete X Y

/-- Corollary 18: `Oid({X →_A Y})` is complete. -/
theorem corollary_18_funs {A : Type u} [CompleteBooleanAlgebra A]
    (X Y : AName.{u} A) : (oid (funsB X Y)).IsComplete :=
  oid_funsB_isComplete X Y

/-- Corollary 18, fullness for relations. -/
theorem corollary_18_prod_full {A : Type u} [CompleteBooleanAlgebra A]
    (X Y : AName.{u} A) (Φ : AName.{u} A → A)
    (hcongr : ∀ S T, AName.eqB S T ⊓ Φ S ≤ Φ T) (a : A)
    (ha : a = ⨆ S, AName.memB S (powerB (prodB X Y)) ⊓ Φ S) :
    ∃ p : (powerB (prodB X Y)).idx, Φ ((powerB (prodB X Y)).child p) = a :=
  oid_prodB_full X Y Φ hcongr a ha

/-- Corollary 18, fullness for functions. -/
theorem corollary_18_funs_full {A : Type u} [CompleteBooleanAlgebra A]
    (X Y : AName.{u} A) (Φ : AName.{u} A → A)
    (hcongr : ∀ F G, AName.eqB F G ⊓ Φ F ≤ Φ G) (a : A)
    (ha : a = ⨆ F, AName.memB F (funsB X Y) ⊓ Φ F) :
    ∃ p : (funsB X Y).idx,
      AName.memB ((funsB X Y).child p) (funsB X Y) ⊓
        Φ ((funsB X Y).child p) = a :=
  oid_funsB_full X Y Φ hcongr a ha

/-- Definition 13: on a complete codomain, `F(f)` is functional and `γ(F(f)) = f`.
This is not the hom-object isomorphism `SetoidR_A(X,Y) ≅ SetoidF_A(X,Y)`. -/
theorem definition_13 {A : Type*} [CompleteBooleanAlgebra A] {X Y : Type*}
    {S : ASetoid (A := A) X} {T : ASetoid (A := A) Y}
    (hT : T.IsComplete) (f : RelFun S T) :
    APoset.Functional S T (functionalOfRel hT f) ∧
      (∀ x y, gamma S T (functionalOfRel hT f) x y = f.val x y) :=
  ⟨functionalOfRel_functional hT f, functionalOfRel_gamma hT f⟩

/-- Theorem 30, retract at Boolean value `⊤`:
`‖lam(f) · X = f(X)‖ = 1` for determined-by-finite `f`. This is a name
calculation, not Theorem 1(i). -/
theorem theorem_30_retract {A : Type u} [CompleteBooleanAlgebra A]
    (f : CanonicalPowerIdx (AName.check (A := A) PSet.omega) →
      CanonicalPowerIdx (AName.check (A := A) PSet.omega))
    (hf : DeterminedByFiniteVA (A := A) f)
    (X : CanonicalPowerIdx (AName.check (A := A) PSet.omega)) :
    AName.eqB
      ((powerB (AName.check (A := A) PSet.omega)).child
        (engelerAppVA (A := A) (engelerLamVA (A := A) f) X).1)
      ((powerB (AName.check (A := A) PSet.omega)).child (f X).1) = ⊤ :=
  engelerVA_retract (A := A) f hf X

/-- Theorem 30, retract as canonical `Oid` equality at `⊤`. -/
theorem theorem_30_retract_oid {A : Type u} [CompleteBooleanAlgebra A]
    (f : CanonicalPowerIdx (AName.check (A := A) PSet.omega) →
      CanonicalPowerIdx (AName.check (A := A) PSet.omega))
    (hf : DeterminedByFiniteVA (A := A) f)
    (X : CanonicalPowerIdx (AName.check (A := A) PSet.omega)) :
    (canonicalPowerSetoid (AName.check (A := A) PSet.omega)).eq
      (engelerAppVA (A := A) (engelerLamVA (A := A) f) X) (f X) = ⊤ :=
  engelerVA_retract_oid (A := A) f hf X

/-- Theorem 30 data: `(P^A(check E), ‖⊆‖, ·, lam)` on the canonical carrier. -/
noncomputable def theorem_30_model {A : Type u} [CompleteBooleanAlgebra A] :
    AValuedReflexiveDcpo A
      (CanonicalPowerIdx (AName.check (A := A) PSet.omega)) :=
  engelerVA_model (A := A)

theorem theorem_30_complete {A : Type u} [CompleteBooleanAlgebra A] :
    (canonicalPowerSetoid (AName.check (A := A) PSet.omega)).IsComplete :=
  engelerVA_complete (A := A)

theorem theorem_30_total {A : Type u} [CompleteBooleanAlgebra A] :
    (canonicalPowerSetoid (AName.check (A := A) PSet.omega)).IsTotal :=
  engelerVA_total (A := A)

/-- Canonical-carrier strictness only; the raw index carrier is not strict. -/
theorem theorem_30_strict {A : Type u} [CompleteBooleanAlgebra A] :
    (canonicalPowerSetoid (AName.check (A := A) PSet.omega)).IsStrict :=
  engelerVA_strict (A := A)

/-- Theorem 30: `(P^A(check E), ‖⊆‖, ·, lam)` is an `A`-valued reflexive
dcpo (operations and retract at `⊤`). Not an internal continuous lattice
and not a countable-base claim. -/
theorem theorem_30 {A : Type u} [CompleteBooleanAlgebra A] :
    (theorem_30_model (A := A)).poset =
      canonicalPowerPoset (AName.check (A := A) PSet.omega) ∧
    (∀ F X, (theorem_30_model (A := A)).app F X =
      engelerAppVA (A := A) F X) ∧
    (∀ f, (theorem_30_model (A := A)).lam f = engelerLamVA (A := A) f) ∧
    (∀ f X, DeterminedByFiniteVA (A := A) f →
      (canonicalPowerSetoid (AName.check (A := A) PSet.omega)).eq
        (engelerAppVA (A := A) (engelerLamVA (A := A) f) X) (f X) = ⊤) ∧
    (canonicalPowerSetoid (AName.check (A := A) PSet.omega)).IsComplete ∧
    (canonicalPowerSetoid (AName.check (A := A) PSet.omega)).IsTotal ∧
    (canonicalPowerSetoid (AName.check (A := A) PSet.omega)).IsStrict :=
  engelerVA (A := A)

-- Jech 14.19, CSL Theorem 1(iii), and Jech 14.21 are `jech_lemma_14_19`,
-- `theorem_1_iii`, and `jech_lemma_14_21` from `Scott2026.VA`.
-- CSL Theorem 1(ii) is `theorem_1_ii` (FOL MP, `∀`-intro/elim, equality
-- congruence on `SetFormula` / `𝔏_Set(V^A)`). CSL Theorem 1(i) is
-- `theorem_1_i`: a ZFC theorem has Boolean value `1` at every assignment.
-- Choice is `axiom_choice_valid` (Jech 14.27) via `wellOrderB` and the
-- remaining well-order conjuncts (antisymmetry, totality, transitivity,
-- least element) over pair-index `iSup`.
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
-- §3 through Corollary 18 (CSL p.4–7): `oid` / `oid_eq` / `oid_eps` (Definition 14),
-- `ePred` / `ePredPowerB` (Definition 15), `oidRel` / `oidRel_id` / `oidRel_comp`
-- (Definition 16) from `Scott2026.Oid`, with `RelFun.comp` (Definition 8 composition)
-- and `functionalOfRel` (Definition 13) from `Scott2026.RelFun`. Definition 16 is
-- proved only as functor data: fullness, faithfulness and essential surjectivity of
-- `Oid`, hence `Set_A ≃ SetoidR_A`, are not claimed. Theorem 17 / Corollary 18 at
-- the `Oid(P^A(X))` level are `theorem_17_va_*` / `corollary_18_*`
-- (`theorem_17_complete` / `proposition_28_total` / `proposition_28_strict`
-- remain ground-type). Proposition 28 at `V^A` is `proposition_28_va_complete`
-- / `proposition_28_va_total` (thin-export Theorem 17 on the raw carrier),
-- `proposition_28_va_canonical_eq` (canonical names on `check Y`, not raw
-- `IsStrict`), `definition_11_powerB` / `powerBPoset`, and the fixed-point
-- carrier `CanonicalPowerIdx` with `proposition_28_va_canonical_strict` /
-- `proposition_28_va_canonical_total` / `proposition_28_va_canonical_complete`
-- / `definition_11_canonicalPowerB`. Raw index-level `IsStrict` is false
-- (`oid_powerB_not_strict`); there is no `proposition_28_va_strict`.
-- The continuous-lattice-with-base clause is not stated (no internal
-- formula language for way-below / continuous lattices in `V^A`).
--
-- Theorem 30 (CSL p.7): `(P^A(check E), ‖⊆‖, ·, lam)` is an `A`-valued
-- reflexive dcpo on the canonical carrier (`theorem_30` / `theorem_30_model`
-- / `theorem_30_retract` / `theorem_30_retract_oid`). The pairing on
-- `P_fin(ℕ) × ℕ` is `engelerPair` (not the empty initial algebra of
-- `P_fin × Id`). Internal `·` / `lam` are `engelerAppVA` / `engelerLamVA`.
-- The retract is a name calculation at `⊤` for `DeterminedByFiniteVA`;
-- this is not Theorem 1(i), Definition 19 at `V^A`, an internal
-- continuous lattice, or a countable-base claim. Canonical strictness
-- is `theorem_30_strict`; the raw index carrier is not claimed strict.
--
-- Example 21 at `V^A` and Proposition 22 (CSL p.8–9): pure λ-terms are
-- encoded by tags `(0,x)`, `(1,(x,M))`, `(2,(M,N))` (`pLamVar` /
-- `pLamAbs` / `pLamApp`, no constant tag 3). `lamInductiveB` is the
-- Boolean `Λ(V)`-inductive clause; `lamB (check Var)` is
-- `Λ(check Var)^A`. Inductiveness and leastness are `example_21_va` /
-- `proposition_22` / `proposition_22_least` (the `check_omega_least`
-- pattern, with Theorem 1(iii) for witnesses). Check-equality
-- `‖check (Λ(Var)) = lamB (check Var)‖ = 1` is
-- `proposition_22_check_eq`. This is not `Λ(D, check Var, 𝔎)^A` or
-- an interpretation.
--
-- Example 24 (CSL p.9): `λ` is encoded as pairs of tagged terms
-- (`encodeEq` / `encodeEqB` via `pOpair` / `opairB`). `lamEqInductiveB`
-- is the Boolean `λ`-inductive clause (not required to be `Δ₀`); `β`
-- uses paper substitution `Lam.substCA`, and `α` is included. `lamEqB
-- (checkVar Var)` is `λ^A`, where `checkVar Var` is the unfolding of
-- `check Var` (`check_eq_mk`, so `idx` is `Var.Type`). Inductiveness and
-- `‖check(λ) ⊆ lamEqB (checkVar Var)‖ = 1` are `example_24` /
-- `example_24_va` / `example_24_subset` (induction on `LamEq`). The
-- paper only claims `⊆`; equality is not exported. This is not
-- `Λ(D, check Var, 𝔎)^A` or Theorem 26.
--
-- Definition 25 (CSL p.10): ground `⟦·⟧_ρ` on `ReflexiveDcpo` is `interp`
-- (`interp_var` / `interp_app` / `interp_abs` / `interpClosed`). Valuations
-- are Finset-supported (`Valuation` / `Valuation.update` / `Valuation.empty`).
-- The meta-lambda is Scott-continuous (`interp_update_scott`), so `lam` is
-- applied to a map in the retract class. There is no constant clause.
-- [4, Theorem 5.4.4] is `interp_sound` / `definition_25_sound` on the
-- capture-free fragment `LamEqNC` (`interp_subst` needs `Lam.FreeFor`;
-- `Lam.subst` is naive and does not rename). Full paper soundness is
-- `interp_sound_full` / `definition_25_sound_full` (`LamEq`, CA-β + α,
-- `[Infinite Var]`). Naive capture is `interp_substNaive_captures`.
-- This is not `SetoidF_A(Λ^A, D)`, not A-valued `⟦·⟧^A_ρ`, and not
-- Theorem 26.
--
-- Theorem 26, pure-term fragment (CSL p.10): `interpVA` interprets
-- `Λ(Var)` on the Theorem 30 carrier (`CanonicalPowerIdx` of `check ω`)
-- by the Definition 25 clauses with `engelerAppVA` / `engelerLamVA`.
-- The meta-lambda is `DeterminedByFiniteVA` (`theorem_26_update_determined`),
-- so `theorem_30_retract` applies. Capture-free soundness remains
-- `interpVA_sound` / `theorem_26_sound` (`LamEqNC`). Full paper
-- soundness on this carrier is `interpVA_sound_full` /
-- `theorem_26_sound_full` (`LamEq`, CA-β + α, `[Infinite Var]`).
-- This is not `Λ(D, check Var, 𝔎)^A`, not tag 3, not an internal
-- reflexive-dcpo hypothesis, and not `SetoidF_A` membership.
-- The missing lemma for `SetoidF_A(oid(lamB (check Var)),
-- canonicalPowerSetoid)` (or `oid(check (pLamSet Var))`) is congruence
-- of `interpVA` under `eqB (encodeLamB M) (encodeLamB N)`, equivalently
-- injectivity of `encodeLamB` at every Boolean value (pairwise
-- Boolean-unequal variable children). Definition 16 `oidRel` would need
-- a function name with `isFunctionB = ⊤` and the same single-valuedness.
--
-- Lemma 31 (CSL p.11): `lemma_31` / `lemma_31_closed` are Boolean
-- equality at `⊤` between `interpVA` of a checked valuation and the
-- check (`setToCanonical`) of ground `interp` on
-- `engelerReflexiveDcpo engelerPair`. Pairings match.
--
-- Definition 32 (CSL p.11): `definition_32` is the syntactic package
-- (closed Church `⊥`, `⊤`, `(c_n)`, and the `if`/`succ`/`pred`/`0?`
-- identities). Distinctness (i) is `churchTrue_interp_ne_churchFalse`.
-- `ReflexiveDcpoWithNumerals` stays algebraic.
--
-- Proposition 33 (CSL p.11): `proposition_33` packages the Engeler
-- model as a reflexive continuous lattice with Church numerals
-- (`engelerWithNumerals`, `IsContinuousLattice (Set ℕ)`).
--
-- Corollary 34 (CSL p.11): the paper name is the internal V^A statement
-- “reflexive continuous lattice with numerals”. There is no internal
-- way-below language (same limit as `theorem_30`). The Lean package is
-- `corollary_34_check` (Lemma 31 check/VA Church images, Δ₀ Boolean
-- distinctness via Theorem 2, (ii)–(iv) on `interpClosedVA`).
-- `eqB_interpClosedVA_churchNum_subsingleton` records that numeral
-- injectivity needs `[Nontrivial A]`.
--
-- Lemma 35 (CSL p.12): `lemma_35` / `lemma_35_i` / `lemma_35_ii` are
-- Engeler-only (`engelerWithNumerals` on `𝒫(ℕ)`). Scott-discrete
-- Booleans/numerals via Scott-open separators (`ScottOpen`); oracles
-- via `gbar` and the retract. `lemma_35_ii_of_extension` stays the
-- weaker “given a Scott-continuous extension” lemma. A general
-- `ReflexiveDcpoWithNumerals` statement is blocked: the structure does
-- not store `if`/`succ`/`pred`/`0?`.
--
-- Proposition 36 (CSL p.12): `proposition_36` is paper (i) ↔ (ii) on
-- `engelerWithNumerals` with a closed numeral-to-numeral `M`
-- (`MapsNumerals`). `ManyOneLe` stays algebraic (any `f : ℕ → ℕ`).
-- `exists_nat_fun_not_lambda_definable` is why
-- `ManyOneLe → proposition_36_i` is not claimed.
--
-- §5 Random Variables (CSL p.13–15): `definition_37`, `lemma_38`,
-- `G_X`, `proposition_39`, `proposition_40`, `lemma_41` /
-- `lemma_41_const` are paper-named. `AssociatedAlgebra` is `A(X)=Σ/𝒩`.
-- `proposition_42` is the measure-theoretic Boolean-value-0 reading
-- (`coinMeasure`; Borel coin space is not a `NegligibilitySpace`).
-- Weaker lemmas `proposition_42_finite` / `_finite_image` /
-- `_finite_swap` / `_infinite_image` keep weaker names.
-- `theorem_43` is the external-oracle form (same paper type) via
-- `chiOracle` / `lemma_35_ii` / `proposition_36`; the paper's internal
-- Corollary 34 + Theorem 1 appeal is unavailable
-- (`corollary_34_check` only). `proposition_44` transports
-- `CompleteLattice` along `G_X` and records `¬IsContinuousLattice`
-- when `¬IsAtomic`.

/-- Example 21, ground: `Λ(Var)` is the least inductive set of pure terms. -/
theorem example_21 {Var : Type*} {S : Set (Lam Var)} (h : Lam.IsInductive S) :
    ∀ M : Lam Var, M ∈ S :=
  Lam.lam_least_inductive h

/-- Example 21 at `V^A`: `‖lamInductiveB (lamB (check Var))‖ = 1`. -/
theorem example_21_va {A : Type u} [CompleteBooleanAlgebra A] (Var : PSet.{u}) :
    lamInductiveB (AName.check (A := A) Var)
      (lamB (AName.check (A := A) Var)) = ⊤ :=
  lamInductiveB_lamB (AName.check (A := A) Var)

/-- Proposition 22: `lamB (check Var)` is `Λ(check Var)`-inductive and least. -/
theorem proposition_22 {A : Type u} [CompleteBooleanAlgebra A] (Var : PSet.{u}) :
    lamInductiveB (AName.check (A := A) Var)
      (lamB (AName.check (A := A) Var)) = ⊤ ∧
      ∀ X : AName.{u} A,
        lamInductiveB (AName.check (A := A) Var) X = ⊤ →
          AName.subsetB (lamB (AName.check (A := A) Var)) X = ⊤ :=
  ⟨lamInductiveB_lamB (AName.check (A := A) Var),
    fun _X h => lamB_least h⟩

/-- Proposition 22, leastness: if `‖lamInductiveB X‖ = 1` then
`‖lamB (check Var) ⊆ X‖ = 1`. -/
theorem proposition_22_least {A : Type u} [CompleteBooleanAlgebra A]
    {Var : PSet.{u}} {X : AName.{u} A}
    (h : lamInductiveB (AName.check (A := A) Var) X = ⊤) :
    AName.subsetB (lamB (AName.check (A := A) Var)) X = ⊤ :=
  lamB_least h

/-- Proposition 22, check-equality:
`‖check (Λ(Var)) = lamB (check Var)‖ = 1`. -/
theorem proposition_22_check_eq {A : Type u} [CompleteBooleanAlgebra A]
    (Var : PSet.{u}) :
    AName.eqB (AName.check (A := A) (pLamSet Var))
      (lamB (AName.check (A := A) Var)) = ⊤ :=
  lamB_check_eq (A := A) Var

/-- Example 24: `lamEqB (checkVar Var)` is `λ`-inductive and contains `check(λ)`.
`checkVar Var` is the unfolding of `check Var` (`check_eq_mk`). -/
theorem example_24 {A : Type u} [CompleteBooleanAlgebra A] (Var : PSet.{u})
    [DecidableEq Var.Type] :
    lamEqInductiveB (checkVar (A := A) Var)
      (lamEqB (checkVar (A := A) Var)) = ⊤ ∧
      AName.subsetB (AName.check (A := A) (pLamEqSet Var))
        (lamEqB (checkVar (A := A) Var)) = ⊤ :=
  ⟨lamEqInductiveB_lamEqB (checkVar (A := A) Var),
    lamEq_check_subset (A := A) Var⟩

/-- Example 24 at `V^A`: `‖lamEqInductiveB (lamEqB (checkVar Var))‖ = 1`. -/
theorem example_24_va {A : Type u} [CompleteBooleanAlgebra A] (Var : PSet.{u})
    [DecidableEq Var.Type] :
    lamEqInductiveB (checkVar (A := A) Var)
      (lamEqB (checkVar (A := A) Var)) = ⊤ :=
  lamEqInductiveB_lamEqB (checkVar (A := A) Var)

/-- Example 24, subset: `‖check(λ) ⊆ lamEqB (checkVar Var)‖ = 1`. -/
theorem example_24_subset {A : Type u} [CompleteBooleanAlgebra A]
    (Var : PSet.{u}) [DecidableEq Var.Type] :
    AName.subsetB (AName.check (A := A) (pLamEqSet Var))
      (lamEqB (checkVar (A := A) Var)) = ⊤ :=
  lamEq_check_subset (A := A) Var

/-- Definition 25: the four ground interpretation clauses. -/
theorem definition_25 {Var D : Type*} [DecidableEq Var] [CompleteLattice D]
    (R : ReflexiveDcpo D) (x : Var) (M N : Lam Var) (ρ : Valuation Var D)
    (hx : x ∈ ρ.domain) :
    interp R (Lam.var x) ρ = ρ.lookup x hx ∧
      interp R (M.app N) ρ = R.app (interp R M ρ) (interp R N ρ) ∧
      interp R (Lam.abs x M) ρ =
        R.lam (fun d => interp R M (ρ.update x d)) ∧
      interpClosed R N = interp R N Valuation.empty :=
  ⟨interp_var R x ρ hx, interp_app R M N ρ, interp_abs R x M ρ, interp_closed R N⟩

/-- Definition 25, variable clause: `⟦x⟧_ρ = ρ(x)`. -/
theorem definition_25_var {Var D : Type*} [DecidableEq Var] [CompleteLattice D]
    (R : ReflexiveDcpo D) (x : Var) (ρ : Valuation Var D) (h : x ∈ ρ.domain) :
    interp R (Lam.var x) ρ = ρ.lookup x h :=
  interp_var R x ρ h

/-- Definition 25, application clause: `⟦MN⟧_ρ = ⟦M⟧_ρ · ⟦N⟧_ρ`. -/
theorem definition_25_app {Var D : Type*} [DecidableEq Var] [CompleteLattice D]
    (R : ReflexiveDcpo D) (M N : Lam Var) (ρ : Valuation Var D) :
    interp R (M.app N) ρ = R.app (interp R M ρ) (interp R N ρ) :=
  interp_app R M N ρ

/-- Definition 25, abstraction clause:
`⟦λx. M⟧_ρ = lam(λd. ⟦M⟧_{ρ(x := d)})`. -/
theorem definition_25_abs {Var D : Type*} [DecidableEq Var] [CompleteLattice D]
    (R : ReflexiveDcpo D) (x : Var) (M : Lam Var) (ρ : Valuation Var D) :
    interp R (Lam.abs x M) ρ = R.lam fun d => interp R M (ρ.update x d) :=
  interp_abs R x M ρ

/-- Definition 25, closed terms: `⟦M⟧ := ⟦M⟧_∅`. -/
theorem definition_25_closed {Var D : Type*} [DecidableEq Var] [CompleteLattice D]
    (R : ReflexiveDcpo D) (M : Lam Var) :
    interpClosed R M = interp R M Valuation.empty :=
  interp_closed R M

/-- [4, Theorem 5.4.4] substitution lemma, restricted to `N` free for `x`.
Unrestricted `interp_subst` is false: `Lam.subst` does not rename. -/
theorem definition_25_subst {Var D : Type*} [DecidableEq Var] [CompleteLattice D]
    (R : ReflexiveDcpo D) (M N : Lam Var) (x : Var) (ρ : Valuation Var D)
    (hfree : M.FreeFor x N) :
    interp R (M.subst x N) ρ = interp R M (ρ.update x (interp R N ρ)) :=
  interp_subst R M N x ρ hfree

/-- [4, Theorem 5.4.4] β-soundness when `N` is free for `x` in `M`.
Capturing β is not claimed. -/
theorem definition_25_sound_beta {Var D : Type*} [DecidableEq Var]
    [CompleteLattice D] (R : ReflexiveDcpo D) (x : Var) (M N : Lam Var)
    (ρ : Valuation Var D) (hfree : M.FreeFor x N) :
    interp R ((Lam.abs x M).app N) ρ = interp R (M.subst x N) ρ :=
  interp_sound_beta R x M N ρ hfree

/-- [4, Theorem 5.4.4] on the capture-free fragment: `LamEqNC M N` implies
`⟦M⟧_ρ = ⟦N⟧_ρ`. Not unrestricted `LamEq` (no α-rule; capturing β is
unsound for this `subst`). -/
theorem definition_25_sound {Var D : Type*} [DecidableEq Var] [CompleteLattice D]
    (R : ReflexiveDcpo D) {M N : Lam Var} (h : LamEqNC M N)
    (ρ : Valuation Var D) :
    interp R M ρ = interp R N ρ :=
  interp_sound R h ρ

/-- [4, Theorem 5.4.4], closed form: capture-free equations are sound at
`⟦·⟧_∅`. -/
theorem definition_25_sound_closed {Var D : Type*} [DecidableEq Var]
    [CompleteLattice D] (R : ReflexiveDcpo D) {M N : Lam Var}
    (h : LamEqNC M N) :
    interpClosed R M = interpClosed R N :=
  interpClosed_sound R h

/-- Theorem 26, pure-term fragment: the four Definition 25 clauses on the
Theorem 30 carrier. Not `Λ(D, check Var, 𝔎)^A`, not tag 3, and not
`SetoidF_A` membership. -/
theorem theorem_26_pure {A : Type u} [CompleteBooleanAlgebra A] {Var : Type*}
    [DecidableEq Var] (x : Var) (M N : Lam Var)
    (ρ : Valuation Var (EngelerCarrier (A := A)))
    (hx : x ∈ ρ.domain) :
    interpVA (A := A) (Lam.var x) ρ = ρ.lookup x hx ∧
      interpVA (A := A) (M.app N) ρ =
        engelerAppVA (A := A) (interpVA (A := A) M ρ)
          (interpVA (A := A) N ρ) ∧
      interpVA (A := A) (Lam.abs x M) ρ =
        engelerLamVA (A := A)
          (fun d => interpVA (A := A) M (ρ.update x d)) ∧
      interpClosedVA (A := A) N =
        interpVA (A := A) N
          (Valuation.default (finsetToCanonical (A := A) ∅)) :=
  ⟨interpVA_var (A := A) x ρ hx, interpVA_app (A := A) M N ρ,
    interpVA_abs (A := A) x M ρ, interpVA_closed (A := A) N⟩

/-- Theorem 26, variable clause: `⟦x⟧^A_ρ = ρ(x)`. -/
theorem theorem_26_var {A : Type u} [CompleteBooleanAlgebra A] {Var : Type*}
    [DecidableEq Var] (x : Var) (ρ : Valuation Var (EngelerCarrier (A := A)))
    (h : x ∈ ρ.domain) :
    interpVA (A := A) (Lam.var x) ρ = ρ.lookup x h :=
  interpVA_var (A := A) x ρ h

/-- Theorem 26, application clause: `⟦MN⟧^A_ρ = ⟦M⟧^A_ρ · ⟦N⟧^A_ρ`. -/
theorem theorem_26_app {A : Type u} [CompleteBooleanAlgebra A] {Var : Type*}
    [DecidableEq Var] (M N : Lam Var)
    (ρ : Valuation Var (EngelerCarrier (A := A))) :
    interpVA (A := A) (M.app N) ρ =
      engelerAppVA (A := A) (interpVA (A := A) M ρ)
        (interpVA (A := A) N ρ) :=
  interpVA_app (A := A) M N ρ

/-- Theorem 26, abstraction clause:
`⟦λx. M⟧^A_ρ = lam(λd. ⟦M⟧^A_{ρ(x := d)})`. -/
theorem theorem_26_abs {A : Type u} [CompleteBooleanAlgebra A] {Var : Type*}
    [DecidableEq Var] (x : Var) (M : Lam Var)
    (ρ : Valuation Var (EngelerCarrier (A := A))) :
    interpVA (A := A) (Lam.abs x M) ρ =
      engelerLamVA (A := A) fun d => interpVA (A := A) M (ρ.update x d) :=
  interpVA_abs (A := A) x M ρ

/-- Theorem 26, closed terms: `⟦M⟧^A := ⟦M⟧^A_∅`. -/
theorem theorem_26_closed {A : Type u} [CompleteBooleanAlgebra A] {Var : Type*}
    [DecidableEq Var] (M : Lam Var) :
    interpClosedVA (A := A) M =
      interpVA (A := A) M
        (Valuation.default (finsetToCanonical (A := A) ∅)) :=
  interpVA_closed (A := A) M

/-- Theorem 26, substitution on the capture-free fragment. -/
theorem theorem_26_subst {A : Type u} [CompleteBooleanAlgebra A] {Var : Type*}
    [DecidableEq Var] (M N : Lam Var) (x : Var)
    (ρ : Valuation Var (EngelerCarrier (A := A)))
    (hfree : M.FreeFor x N) :
    interpVA (A := A) (M.subst x N) ρ =
      interpVA (A := A) M (ρ.update x (interpVA (A := A) N ρ)) :=
  interpVA_subst (A := A) M N x ρ hfree

/-- Theorem 26, β-soundness when `N` is free for `x` in `M`. -/
theorem theorem_26_sound_beta {A : Type u} [CompleteBooleanAlgebra A]
    {Var : Type*} [DecidableEq Var] (x : Var) (M N : Lam Var)
    (ρ : Valuation Var (EngelerCarrier (A := A)))
    (hfree : M.FreeFor x N) :
    interpVA (A := A) ((Lam.abs x M).app N) ρ =
      interpVA (A := A) (M.subst x N) ρ :=
  interpVA_sound_beta (A := A) x M N ρ hfree

/-- Theorem 26, capture-free soundness on the Theorem 30 carrier. -/
theorem theorem_26_sound {A : Type u} [CompleteBooleanAlgebra A] {Var : Type*}
    [DecidableEq Var] {M N : Lam Var} (h : LamEqNC M N)
    (ρ : Valuation Var (EngelerCarrier (A := A))) :
    interpVA (A := A) M ρ = interpVA (A := A) N ρ :=
  interpVA_sound (A := A) h ρ

/-- Theorem 26, closed form of capture-free soundness. -/
theorem theorem_26_sound_closed {A : Type u} [CompleteBooleanAlgebra A]
    {Var : Type*} [DecidableEq Var] {M N : Lam Var} (h : LamEqNC M N) :
    interpClosedVA (A := A) M = interpClosedVA (A := A) N :=
  interpClosedVA_sound (A := A) h

/-- Theorem 26: the meta-lambda is `DeterminedByFiniteVA`. -/
theorem theorem_26_update_determined {A : Type u} [CompleteBooleanAlgebra A]
    {Var : Type*} [DecidableEq Var] (M : Lam Var)
    (ρ : Valuation Var (EngelerCarrier (A := A))) (x : Var) :
    DeterminedByFiniteVA (A := A)
      (fun d => interpVA (A := A) M (ρ.update x d)) :=
  interpVA_update_determined (A := A) M ρ x

/-- Theorem 26, packaged: clauses, determinedness of the meta-lambda, and
capture-free soundness on the Theorem 30 carrier. The paper’s full
statement (constants / tag 3, internal reflexive-dcpo hypothesis,
`SetoidF_A(Λ^A, D)`, unrestricted `λ ⊢ M = N`) is out of scope. -/
theorem theorem_26 {A : Type u} [CompleteBooleanAlgebra A] {Var : Type*}
    [DecidableEq Var] (x : Var) (M N : Lam Var)
    (ρ : Valuation Var (EngelerCarrier (A := A)))
    (hx : x ∈ ρ.domain) (hfree : M.FreeFor x N) {P Q : Lam Var}
    (heq : LamEqNC P Q) :
    interpVA (A := A) (Lam.var x) ρ = ρ.lookup x hx ∧
      interpVA (A := A) (M.app N) ρ =
        engelerAppVA (A := A) (interpVA (A := A) M ρ)
          (interpVA (A := A) N ρ) ∧
      interpVA (A := A) (Lam.abs x M) ρ =
        engelerLamVA (A := A)
          (fun d => interpVA (A := A) M (ρ.update x d)) ∧
      DeterminedByFiniteVA (A := A)
        (fun d => interpVA (A := A) M (ρ.update x d)) ∧
      interpVA (A := A) ((Lam.abs x M).app N) ρ =
        interpVA (A := A) (M.subst x N) ρ ∧
      interpVA (A := A) P ρ = interpVA (A := A) Q ρ :=
  ⟨interpVA_var (A := A) x ρ hx, interpVA_app (A := A) M N ρ,
    interpVA_abs (A := A) x M ρ,
    interpVA_update_determined (A := A) M ρ x,
    interpVA_sound_beta (A := A) x M N ρ hfree,
    interpVA_sound (A := A) heq ρ⟩

/-- Theorem 26, closed form of full `LamEq` soundness. The open form is
`theorem_26_sound_full` in `InterpVA`. Capture-free closed soundness
remains `theorem_26_sound_closed`. -/
theorem theorem_26_sound_closed_full {A : Type u} [CompleteBooleanAlgebra A]
    {Var : Type*} [DecidableEq Var] [Infinite Var] {M N : Lam Var}
    (h : LamEq M N) :
    interpClosedVA (A := A) M = interpClosedVA (A := A) N :=
  interpClosedVA_sound_full (A := A) h

end Scott2026
