/-
Copyright (c) 2026 Lars Warren Ericson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/

import Mathlib

/-!
# Scott 2026 (CSL): Palomar Challenge

Palomar compares this module to `Solution.lean` using `comparator.json`.

The compared theorems are `csl2026_internal_interpretation` and `csl2026`.
`csl2026_internal_interpretation` is an `A`-valued λ-interpretation with
equational soundness, separation of the Church Booleans, and injectivity of
the Church numerals. That statement does not identify the carrier with `V^A`;
the Solution witness is the internal Engeler model. `csl2026` is Theorem 43:
two subsets of `ℕ` incomparable under Proposition 36(i). `proposition_36_i`
is oracle agreement in one Engeler graph model on `Set ℕ`, whose Booleans
and numerals are the interpretations of the Church Booleans and Church
numerals. The `sorry`s are the proof holes.

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

/-- An `A`-valued interpretation of the equational λ-theory: soundness,
separation of the Church Booleans, and injectivity of the Church numerals.
This structure does not require the carrier to be the internal Engeler
model in `V^A`. -/
structure InternalInterpretation (A : Type) [CompleteBooleanAlgebra A] where
  D : Type
  V : Type
  eqA : D → D → A
  app : D → D → D
  lam : (D → D) → D
  interp : Lam ℕ → V → D
  lookup : V → ℕ → D
  update : V → ℕ → D → V
  empty : V
  eq_refl : ∀ d, eqA d d = ⊤
  eq_symm : ∀ d e, eqA d e = eqA e d
  eq_trans : ∀ d e f, eqA d e ⊓ eqA e f ≤ eqA d f
  interp_var : ∀ ρ x, interp (Lam.var x) ρ = lookup ρ x
  interp_app : ∀ ρ M N, interp (M.app N) ρ = app (interp M ρ) (interp N ρ)
  interp_abs :
    ∀ ρ x M, interp (Lam.abs x M) ρ = lam (fun d => interp M (update ρ x d))
  interp_sound :
    ∀ ρ {M N : Lam ℕ}, LamEq M N → eqA (interp M ρ) (interp N ρ) = ⊤
  church_bool_separate :
    eqA (interp churchTrueN empty) (interp churchFalseN empty) = ⊥
  church_num_inj :
    ∀ n m,
      eqA (interp (churchNumN n) empty) (interp (churchNumN m) empty) = ⊤ → n = m

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

/-- Every nontrivial complete Boolean algebra carries an `A`-valued
interpretation in the sense of `InternalInterpretation`. The Solution
witness is the internal Engeler model in `V^A`. -/
def internal_interpretation_statement : Prop :=
  ∀ (A : Type) [CompleteBooleanAlgebra A] [Nontrivial A],
    Nonempty (InternalInterpretation A)

/-- Theorem 26 and Corollary 34 through the auditable statement above. -/
theorem csl2026_internal_interpretation :
    internal_interpretation_statement := by
  sorry

/-- Theorem 43: two subsets of `ℕ` that are incomparable under `≤ₘ`.
The Solution proof is `theorem_43_paper`, obtained from
`csl2026_capstones` (Theorems 26 and 43 and Corollary 34). -/
theorem csl2026 : ∃ T₁ T₂ : Set ℕ,
    ¬proposition_36_i T₁ T₂ ∧ ¬proposition_36_i T₂ T₁ := by
  sorry

end Scott2026
