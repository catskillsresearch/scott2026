/-
Copyright (c) 2026 Lars Warren Ericson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/

import Mathlib

/-!
# Scott 2026 (CSL): Palomar Challenge

Palomar compares this module to `Solution.lean` using `comparator.json`.

The compared theorems are `csl2026_internal_interpretation`, a Mathlib-only
face of the Boolean-valued λ-interpretation of Theorem 26 and the internal
Engeler consequences of Corollary 34, and `csl2026`: Theorem 43, two subsets
of `ℕ` incomparable under the λ-definable many-one preorder of Proposition 36.
`proposition_36_i` is oracle agreement in every reflexive dcpo whose
application and abstraction are the Engeler graph operations of
`engelerPair`. `InternalInterpretation` likewise requires that ground
retract, not only equational soundness. The `sorry`s are the proof holes.

The paper's authors were not contacted and did not participate in, review,
or endorse this formalization.
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

/-- Definition 25: a valuation is a partial map `Var → D`. -/
structure Valuation (Var : Type*) (D : Type*) where
  domain : Finset Var
  toFun : Var → D

namespace Valuation

def default {Var : Type*} {D : Type*} (d : D) : Valuation Var D where
  domain := ∅
  toFun := fun _ => d

def empty {Var : Type*} {D : Type*} [CompleteLattice D] : Valuation Var D :=
  default (⊥ : D)

def update {Var : Type*} {D : Type*} [DecidableEq Var] (ρ : Valuation Var D) (x : Var) (d : D) :
    Valuation Var D where
  domain := insert x ρ.domain
  toFun := Function.update ρ.toFun x d

end Valuation

/-- Definition 19: a reflexive dcpo on a complete lattice. `fun` and `lam`
are Scott-continuous and `fun ∘ lam = id` on Scott-continuous endomaps. -/
structure ReflexiveDcpo (D : Type*) [CompleteLattice D] where
  funMap : D → (D → D)
  lam : (D → D) → D
  fun_scott : ScottContinuous funMap
  lam_scott : ScottContinuous lam
  fun_scott_pt : ∀ d, ScottContinuous (funMap d)
  retract : ∀ f : D → D, ScottContinuous f → funMap (lam f) = f

def ReflexiveDcpo.app {D : Type*} [CompleteLattice D] (R : ReflexiveDcpo D)
    (d e : D) : D :=
  R.funMap d e

/-- Definition 32: a reflexive dcpo with distinct Booleans and injective numerals. -/
structure ReflexiveDcpoWithNumerals (D : Type*) [CompleteLattice D]
    extends ReflexiveDcpo D where
  boolBot : D
  boolTop : D
  numeral : ℕ → D
  bool_ne : boolBot ≠ boolTop
  numeral_inj : Function.Injective numeral

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

/-- Closed-term interpretation `⟦M⟧_ρ` in a reflexive dcpo. -/
def interp {Var : Type*} {D : Type*} [DecidableEq Var] [CompleteLattice D]
    (R : ReflexiveDcpo D) : Lam Var → Valuation Var D → D
  | .var x, ρ => ρ.toFun x
  | .app M N, ρ => R.app (interp R M ρ) (interp R N ρ)
  | .abs x M, ρ => R.lam fun d => interp R M (Valuation.update ρ x d)

/-- Closed-term interpretation `⟦M⟧ := ⟦M⟧_∅`. -/
def interpClosed {Var : Type*} {D : Type*} [DecidableEq Var] [CompleteLattice D]
    (R : ReflexiveDcpo D) (M : Lam Var) : D :=
  interp R M Valuation.empty

/-- Characteristic value of a numeral, in `{boolBot, boolTop}`. -/
noncomputable def chiNum {D : Type*} [CompleteLattice D]
    (R : ReflexiveDcpoWithNumerals D) (S : Set ℕ) (n : ℕ) : D :=
  @ite D (n ∈ S) (Classical.propDecidable _) R.boolTop R.boolBot

/-- An oracle for `S` represents `χ_S` on numerals (Lemma 35(ii)). -/
def IsOracle {D : Type*} [CompleteLattice D]
    (R : ReflexiveDcpoWithNumerals D) (d : D) (S : Set ℕ) : Prop :=
  ∀ n, R.toReflexiveDcpo.app d (R.numeral n) = chiNum R S n

/-- Closed `M` sending each Church numeral to a Church numeral. -/
structure MapsNumerals (M : Lam ℕ) : Prop where
  fv_empty : M.fv = ∅
  maps : ∀ n, ∃ m, LamEq (M.app (churchNumN n)) (churchNumN m)

/-- An `A`-valued internal interpretation whose ground model is the Engeler
graph retract (Proposition 29) with Church numerals (Definition 32).
Soundness, Boolean separation, and numeral injectivity are not enough:
`ground_app` and `ground_lam` force application and abstraction to be
`engelerApp` and `engelerLam` on `engelerPair`, and `numeral_link` ties
the Boolean-valued Church numerals to those ground numerals. -/
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
  ground : ReflexiveDcpoWithNumerals (Set ℕ)
  ground_app : ground.toReflexiveDcpo.funMap = engelerApp engelerPair
  ground_lam : ground.toReflexiveDcpo.lam = engelerLam engelerPair
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
  numeral_link :
    ∀ n m,
      eqA (interp (churchNumN n) empty) (interp (churchNumN m) empty) = ⊤ ↔
        ground.numeral n = ground.numeral m

/-- The numeral function computed by a numeral-to-numeral combinator. -/
noncomputable def mapsNumeralsFun (M : Lam ℕ) (hM : MapsNumerals M) : ℕ → ℕ :=
  fun n => Classical.choose (hM.maps n)

/-- Proposition 36(i): `S₁ ≤ₘ S₂` by a closed numeral-to-numeral combinator
whose oracle agreement is computed in the Engeler graph model. Every
reflexive dcpo with numerals whose application and abstraction are
`engelerApp engelerPair` and `engelerLam engelerPair` must carry oracles
`d₁`, `d₂` agreeing on `⟦M cₙ⟧`. -/
def proposition_36_i (S₁ S₂ : Set ℕ) : Prop :=
  ∃ M : Lam ℕ, MapsNumerals M ∧
    ∀ R : ReflexiveDcpoWithNumerals (Set ℕ),
      R.toReflexiveDcpo.funMap = engelerApp engelerPair →
      R.toReflexiveDcpo.lam = engelerLam engelerPair →
      ∃ d₁ d₂ : Set ℕ,
        IsOracle R d₁ S₁ ∧
        IsOracle R d₂ S₂ ∧
        ∀ n,
          R.toReflexiveDcpo.app d₂
              (interpClosed R.toReflexiveDcpo (M.app (churchNumN n))) =
            R.toReflexiveDcpo.app d₁ (R.numeral n)

/-- Mathlib-only face of Theorem 26 and Corollary 34: every nontrivial complete
Boolean algebra carries an internal interpretation. The Solution instantiates
`InternalInterpretation` with the formalized Engeler model in `V^A`. -/
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
