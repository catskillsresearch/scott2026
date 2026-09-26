/-
Copyright (c) 2026 Lars Warren Ericson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/

import Mathlib

/-!
# Scott 2026 (CSL): Palomar Challenge

Palomar compares this module to `Solution.lean` using `comparator.json`.

The compared theorem is `csl2026`, and its compared statement definition is
`proposition_36_i`. It is Theorem 43: two subsets of `ℕ` incomparable under
Proposition 36(i), whose relation is oracle agreement in one ordinary Engeler
graph model. The full internal Corollary 34 remains a kernel-checked library
capstone, but is not represented by a weaker Mathlib-only proxy here.
Only the compared theorem uses `sorry`.

Dana Scott gave the author the paper. This formalization does not claim
that the paper's authors participated in it or endorsed it.
-/

open Set

namespace Scott2026

/-- Untyped λ-terms over a set of variables (paper Definition 20). -/
inductive Lam (Var : Type*) where
  | var : Var → Lam Var
  | abs : Var → Lam Var → Lam Var
  | app : Lam Var → Lam Var → Lam Var
  deriving Repr

namespace Lam

variable {Var : Type*}

/-- Free variables. -/
def fv [DecidableEq Var] : Lam Var → Finset Var
  | var x => {x}
  | abs x M => fv M \ {x}
  | app M N => fv M ∪ fv N

/-- Term size, used to justify capture-avoiding substitution. -/
def size : Lam Var → ℕ
  | var _ => 0
  | abs _ M => size M + 1
  | app M N => size M + size N + 1

/-- All variable names, free or bound, occurring in a term. -/
def vars [DecidableEq Var] : Lam Var → Finset Var
  | var x => {x}
  | abs x M => insert x (vars M)
  | app M N => vars M ∪ vars N

/-- Naive substitution, used only while renaming a binder. -/
def substNaive [DecidableEq Var] : Lam Var → Var → Lam Var → Lam Var
  | var y, x, N => if y = x then N else var y
  | abs y M, x, N =>
      if y = x then abs y M else abs y (substNaive M x N)
  | app M₁ M₂, x, N => app (substNaive M₁ x N) (substNaive M₂ x N)

theorem size_substNaive_var [DecidableEq Var] (M : Lam Var) (y z : Var) :
    (M.substNaive y (var z)).size = M.size := by
  induction M with
  | var w =>
    simp only [substNaive, size]
    split_ifs <;> simp [size]
  | abs w M ih =>
    simp only [substNaive, size]
    split_ifs <;> simp [size, ih]
  | app M N ihM ihN =>
    simp [substNaive, size, ihM, ihN]

/-- Choose a variable outside a finite set. -/
noncomputable def pickFresh [DecidableEq Var] (avoid : Finset Var) (default : Var) :
    Var :=
  let _ := Classical.propDecidable (∃ z, z ∉ avoid)
  if h : ∃ z, z ∉ avoid then Classical.choose h else default

/-- Capture-avoiding substitution. A conflicting binder is first renamed to
a variable fresh for the body, argument, substituted variable, and binder. -/
noncomputable def substCA [DecidableEq Var] : Lam Var → Var → Lam Var → Lam Var
  | var y, x, N => if y = x then N else var y
  | abs y M, x, N =>
      if y = x then abs y M
      else if x ∉ M.fv then abs y M
      else if y ∉ N.fv then abs y (substCA M x N)
      else
        let z := pickFresh (M.vars ∪ N.fv ∪ {x, y}) y
        abs z (substCA (M.substNaive y (var z)) x N)
  | app M₁ M₂, x, N => app (substCA M₁ x N) (substCA M₂ x N)
termination_by M => M.size
decreasing_by
  · change M.size < M.size + 1; omega
  · rw [size_substNaive_var]; change M.size < M.size + 1; omega
  · change M₁.size < M₁.size + M₂.size + 1; omega
  · change M₂.size < M₁.size + M₂.size + 1; omega

end Lam

/-- The paper's equational theory `λ` (Definition 23): unrestricted
capture-avoiding β-conversion, α-conversion, and congruence. -/
inductive LamEq {Var : Type*} [DecidableEq Var] : Lam Var → Lam Var → Prop where
  | refl (M : Lam Var) : LamEq M M
  | symm {M N : Lam Var} : LamEq M N → LamEq N M
  | trans {M N L : Lam Var} : LamEq M N → LamEq N L → LamEq M L
  | app_left {M N Z : Lam Var} : LamEq M N → LamEq (M.app Z) (N.app Z)
  | app_right {M N Z : Lam Var} : LamEq M N → LamEq (Z.app M) (Z.app N)
  | xi (x : Var) {M N : Lam Var} : LamEq M N → LamEq (Lam.abs x M) (Lam.abs x N)
  | beta (x : Var) (M N : Lam Var) :
      LamEq ((Lam.abs x M).app N) (M.substCA x N)
  | alpha (x y : Var) (M : Lam Var) (hy : y ∉ M.fv) :
      LamEq (Lam.abs x M) (Lam.abs y (M.substCA x (Lam.var y)))

/-- Church truth, `λx. λy. x`. -/
def churchTrueN : Lam ℕ :=
  Lam.abs 0 (Lam.abs 1 (Lam.var 0))

/-- Church falsity, `λx. λy. y`. -/
def churchFalseN : Lam ℕ :=
  Lam.abs 0 (Lam.abs 1 (Lam.var 1))

/-- Church numeral `n` as `λf. λx. fⁿ x`. -/
def churchNumN : ℕ → Lam ℕ
  | 0 => Lam.abs 0 (Lam.abs 1 (Lam.var 1))
  | n + 1 =>
      Lam.abs 0 (Lam.abs 1
        (Lam.app (Lam.var 0)
          (Lam.app (Lam.app (churchNumN n) (Lam.var 0)) (Lam.var 1))))

/-- Application in the Engeler graph model (Proposition 29). -/
def engelerApp {E : Type*} [DecidableEq E] (pair : Finset E × E → E)
    (F X : Set E) : Set E :=
  {q | ∃ K : Finset E, (↑K : Set E) ⊆ X ∧ pair (K, q) ∈ F}

/-- Abstraction in the Engeler graph model (Proposition 29). -/
def engelerLam {E : Type*} [DecidableEq E] (pair : Finset E × E → E)
    (f : Set E → Set E) : Set E :=
  {x | ∃ K : Finset E, ∃ q ∈ f (↑K), x = pair (K, q)}

/-- List code injecting `List ℕ` into `ℕ`, used by the Engeler pairing. -/
def listNatCode : List ℕ → ℕ
  | [] => 0
  | n :: ns => Nat.pair n (listNatCode ns) + 1

/-- Injective pairing `P_fin(ℕ) × ℕ → ℕ`. -/
def engelerPair (p : Finset ℕ × ℕ) : ℕ :=
  Nat.pair (listNatCode (p.1.sort (· ≤ ·))) p.2

/-- Interpretation `⟦M⟧_ρ` by `engelerApp` and `engelerLam` on `engelerPair`. -/
def engelerInterp (M : Lam ℕ) (ρ : ℕ → Set ℕ) : Set ℕ :=
  match M with
  | .var x => ρ x
  | .app M N => engelerApp engelerPair (engelerInterp M ρ) (engelerInterp N ρ)
  | .abs x M =>
      engelerLam engelerPair fun d => engelerInterp M (Function.update ρ x d)

/-- Closed-term interpretation at the empty valuation `⊥ = ∅`. -/
def engelerInterpClosed (M : Lam ℕ) : Set ℕ :=
  engelerInterp M fun _ => ∅

/-- Church falsity and truth as elements of the Engeler graph model. -/
def engelerBoolBot : Set ℕ :=
  engelerInterpClosed churchFalseN

def engelerBoolTop : Set ℕ :=
  engelerInterpClosed churchTrueN

/-- Church numeral `n` as an element of the Engeler graph model. -/
def engelerNumeral (n : ℕ) : Set ℕ :=
  engelerInterpClosed (churchNumN n)

/-- Characteristic value of a numeral, in `{engelerBoolBot, engelerBoolTop}`. -/
noncomputable def engelerChi (S : Set ℕ) (n : ℕ) : Set ℕ :=
  @ite _ (n ∈ S) (Classical.propDecidable _) engelerBoolTop engelerBoolBot

/-- An oracle for `S` represents `χ_S` on the Church numerals (Lemma 35(ii)). -/
def engelerIsOracle (d : Set ℕ) (S : Set ℕ) : Prop :=
  ∀ n, engelerApp engelerPair d (engelerNumeral n) = engelerChi S n

/-- Closed `M` sending each Church numeral to a Church numeral. -/
structure MapsNumerals (M : Lam ℕ) : Prop where
  fv_empty : M.fv = ∅
  maps : ∀ n, ∃ m, LamEq (M.app (churchNumN n)) (churchNumN m)

/-- Proposition 36(i) on the Engeler graph model. Booleans and numerals are
`⟦churchFalseN⟧`, `⟦churchTrueN⟧`, and `⟦churchNumN n⟧` under `engelerApp`
and `engelerLam` at `engelerPair`. `S₁ ≤ₘ S₂` when one closed
numeral-to-numeral combinator has oracles agreeing on `⟦M cₙ⟧`. -/
def proposition_36_i (S₁ S₂ : Set ℕ) : Prop :=
  ∃ M : Lam ℕ, MapsNumerals M ∧
    ∃ d₁ d₂ : Set ℕ,
      engelerIsOracle d₁ S₁ ∧
      engelerIsOracle d₂ S₂ ∧
      ∀ n,
        engelerApp engelerPair d₂ (engelerInterpClosed (M.app (churchNumN n))) =
          engelerApp engelerPair d₁ (engelerNumeral n)

/-- The external presentation of the elements of the internal power object
`P^A(check ℕ)`: an element assigns a Boolean membership value to each natural. -/
abbrev EngelerVA (A : Type) := ℕ → A

/-- Canonical checked copy of an ordinary Engeler element. -/
noncomputable def checkedEngeler {A : Type} [CompleteBooleanAlgebra A]
    (X : Set ℕ) : EngelerVA A := by
  classical
  exact fun n => if n ∈ X then ⊤ else ⊥

/-- Boolean-valued inclusion in `P^A(check ℕ)`. -/
noncomputable def engelerSubsetB {A : Type} [CompleteBooleanAlgebra A]
    (X Y : EngelerVA A) : A :=
  ⨅ n, X n ⇨ Y n

/-- Boolean-valued equality in `P^A(check ℕ)`. -/
noncomputable def engelerEqB {A : Type} [CompleteBooleanAlgebra A]
    (X Y : EngelerVA A) : A :=
  engelerSubsetB X Y ⊓ engelerSubsetB Y X

/-- The truth value that a finite set is included in an `A`-valued subset. -/
noncomputable def finiteSubsetB {A : Type} [CompleteBooleanAlgebra A]
    (K : Finset ℕ) (X : EngelerVA A) : A :=
  ⨅ n : {n // n ∈ K}, X n

/-- Internal Engeler application on `P^A(check ℕ)`. -/
noncomputable def engelerAppB {A : Type} [CompleteBooleanAlgebra A]
    (F X : EngelerVA A) : EngelerVA A :=
  fun q => ⨆ K : Finset ℕ, finiteSubsetB K X ⊓ F (engelerPair (K, q))

/-- The checked finite subset used by internal Engeler abstraction. -/
def checkedFinsetB {A : Type} [CompleteBooleanAlgebra A]
    (K : Finset ℕ) : EngelerVA A :=
  fun n => if n ∈ K then ⊤ else ⊥

/-- Internal Engeler abstraction on `P^A(check ℕ)`. -/
noncomputable def engelerLamB {A : Type} [CompleteBooleanAlgebra A]
    (f : EngelerVA A → EngelerVA A) : EngelerVA A :=
  fun p =>
    ⨆ (K : Finset ℕ) (q : ℕ),
      if p = engelerPair (K, q) then f (checkedFinsetB K) q else ⊥

/-- Interpretation of λ-terms in the internal Engeler power object. -/
noncomputable def interpEngelerVA {A : Type} [CompleteBooleanAlgebra A] :
    Lam ℕ → (ℕ → EngelerVA A) → EngelerVA A
  | .var x, ρ => ρ x
  | .app M N, ρ => engelerAppB (interpEngelerVA M ρ) (interpEngelerVA N ρ)
  | .abs x M, ρ =>
      engelerLamB fun d => interpEngelerVA M (Function.update ρ x d)

/-- Closed interpretation in the internal Engeler power object. -/
noncomputable def interpClosedEngelerVA {A : Type} [CompleteBooleanAlgebra A]
    (M : Lam ℕ) : EngelerVA A :=
  interpEngelerVA M fun _ => ⊥

/-- An internal family of Engeler elements, presented by its Boolean
membership value on every `A`-valued subset of `check ℕ`. -/
abbrev EngelerFamily (A : Type) := EngelerVA A → A

/-- Pointwise supremum of a Boolean-valued internal family. -/
noncomputable def engelerSupB {A : Type} [CompleteBooleanAlgebra A]
    (S : EngelerFamily A) : EngelerVA A :=
  fun n => ⨆ X : EngelerVA A, S X ⊓ X n

/-- Truth value that an internal family is inhabited and directed for
Boolean-valued inclusion. -/
noncomputable def engelerDirectedB {A : Type} [CompleteBooleanAlgebra A]
    (S : EngelerFamily A) : A :=
  (⨆ X : EngelerVA A, S X) ⊓
    ⨅ X : EngelerVA A, ⨅ Y : EngelerVA A,
      S X ⇨ S Y ⇨
        ⨆ Z : EngelerVA A,
          S Z ⊓ engelerSubsetB X Z ⊓ engelerSubsetB Y Z

/-- The order-theoretic internal way-below truth value. It tests `Y` against
every directed family whose supremum lies above `X`; no finite-basis
characterization is built into this definition. -/
noncomputable def engelerWayBelowB {A : Type} [CompleteBooleanAlgebra A]
    (Y X : EngelerVA A) : A :=
  ⨅ S : EngelerFamily A,
    engelerDirectedB S ⇨
      engelerSubsetB X (engelerSupB S) ⇨
        ⨆ Z : EngelerVA A, S Z ⊓ engelerSubsetB Y Z

/-- Membership in the internal checked-finite power object. The join over
checked finite sets gives mixed finite names their appropriate truth values. -/
noncomputable def engelerPfinB {A : Type} [CompleteBooleanAlgebra A]
    (Y : EngelerVA A) : A :=
  ⨆ K : Finset ℕ, engelerEqB Y (checkedFinsetB K)

/-- Supremum of all internally finite way-below elements, at coordinate `n`. -/
noncomputable def engelerBaseSup {A : Type} [CompleteBooleanAlgebra A]
    (X : EngelerVA A) (n : ℕ) : A :=
  ⨆ Y : EngelerVA A,
    engelerPfinB Y ⊓ engelerWayBelowB Y X ⊓ Y n

/-- Supremum of all internally way-below elements, evaluated at `n`. -/
noncomputable def engelerContinuousSup {A : Type} [CompleteBooleanAlgebra A]
    (X : EngelerVA A) (n : ℕ) : A :=
  ⨆ Y : EngelerVA A, engelerWayBelowB Y X ⊓ Y n

/-- Internal Scott continuity on the algebraic Engeler power object. This is
the locality/basis law for an internal map: its value is reconstructed from
its values on checked finite approximants with their Boolean inclusion
weights. It excludes arbitrary external transformations of the truth-value
algebra. -/
noncomputable def engelerInternallyContinuousB
    {A : Type} [CompleteBooleanAlgebra A]
    (f : EngelerVA A → EngelerVA A) : Prop :=
  ∀ (X : EngelerVA A) (q : ℕ),
    f X q =
      ⨆ K : Finset ℕ, finiteSubsetB K X ⊓ f (checkedFinsetB K) q

/-- A compact Mathlib presentation of Corollary 34. The carrier is fixed to
`P^A(check ℕ)`, rather than merely requiring some classical λ-model. -/
structure InternalEngelerInterpretation (A : Type) [CompleteBooleanAlgebra A] : Prop where
  dcpo_sup_upper :
    ∀ (S : EngelerFamily A) (X), S X ≤
      engelerSubsetB X (engelerSupB S)
  dcpo_sup_least :
    ∀ (S : EngelerFamily A) (Y),
      (⨅ X : EngelerVA A, S X ⇨ engelerSubsetB X Y) ≤
        engelerSubsetB (engelerSupB S) Y
  application_continuous :
    ∀ F : EngelerVA A, engelerInternallyContinuousB (engelerAppB F)
  reflexive_retraction :
    ∀ f : EngelerVA A → EngelerVA A, engelerInternallyContinuousB f →
      ∀ X, engelerEqB (engelerAppB (engelerLamB f) X) (f X) = ⊤
  continuous_lattice :
    ∀ X : EngelerVA A, engelerContinuousSup X = X
  checked_finite_way_below :
    ∀ (K : Finset ℕ) (X : EngelerVA A),
      finiteSubsetB K X ≤ engelerWayBelowB (checkedFinsetB K) X
  finitary_base :
    ∀ X : EngelerVA A, engelerBaseSup X = X
  interp_sound :
    ∀ {M N : Lam ℕ}, LamEq M N →
      engelerEqB (A := A) (interpClosedEngelerVA M) (interpClosedEngelerVA N) = (⊤ : A)
  check_church_true :
    interpClosedEngelerVA (A := A) churchTrueN =
      checkedEngeler (A := A) (engelerInterpClosed churchTrueN)
  check_church_false :
    interpClosedEngelerVA (A := A) churchFalseN =
      checkedEngeler (A := A) (engelerInterpClosed churchFalseN)
  check_church_num :
    ∀ n, interpClosedEngelerVA (A := A) (churchNumN n) =
      checkedEngeler (A := A) (engelerInterpClosed (churchNumN n))
  church_bool_separate :
    engelerEqB (A := A) (interpClosedEngelerVA churchTrueN)
      (interpClosedEngelerVA churchFalseN) = (⊥ : A)
  church_num_inj :
    ∀ n m,
      engelerEqB (A := A) (interpClosedEngelerVA (churchNumN n))
          (interpClosedEngelerVA (churchNumN m)) = (⊤ : A) →
        n = m

/-- Theorem 43: two subsets of `ℕ` that are incomparable under `≤ₘ`.
The Solution proof is `theorem_43_paper`, obtained from
`csl2026_capstones` (Theorems 26 and 43 and Corollary 34). -/
theorem csl2026 : ∃ T₁ T₂ : Set ℕ,
    ¬proposition_36_i T₁ T₂ ∧ ¬proposition_36_i T₂ T₁ := by
  sorry

end Scott2026
