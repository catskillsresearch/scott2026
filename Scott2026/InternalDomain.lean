/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/

import Scott2026.VA

/-!
# Internal way-below / continuous-lattice language in `V^A`

Furber–Mardare–Panangaden–Scott, CSL 2026, §4.1 and Proposition 28 / Corollary 34.
The paper interprets “continuous lattice” and `≪` in `V^A`. This module supplies
the `𝔏_Set(V^A)` formulas (subset order) and matching semantic Boolean values.

`corollary_34` remains unnamed: the paper type is the internal statement that
`P^A(check E)` is a reflexive continuous lattice with numerals. The numerals
half is `corollary_34_check`. The continuous-lattice half is
`isContinuousLatticeSubsetB_powerB`. This file proves the language, `≪ → ⊆`,
directedness of `P_fin^A`, `T ⊆ ⋃ P_fin^A(T)`, `isFiniteB_of_subset`,
both directions of `≪ ↔` finite `⊆` under weaker names
(`wayBelowSubsetB_le_finite_subset`, `wayBelowSubsetB_of_finite_subset`),
the ⊆-sup of a family in `P^A(X)` via the tight union `sUnionB`
(`isCompleteLatticeSubsetB_powerB`), and directed-down / joins-down at
each `d ∈ P^A(X)`. Not `proposition_27` (that name is the ground `Set X`
statement). Fat `unionB` remains the one-sided ZFC witness
(`memB_unionB_of_mem` only).
-/

universe u

namespace Scott2026

open AName
open SetFormula
open D0Formula (consName consName_zero consName_succ)
open Classical

variable {A : Type u} [CompleteBooleanAlgebra A]

noncomputable section

/-!
## Semantic Boolean values (subset order)
-/

/-- `x ⊆ x` at Boolean value `1`. -/
theorem subsetB_refl (x : AName.{u} A) : subsetB x x = ⊤ :=
  iInf_eq_top.mpr fun i => himp_eq_top_iff.mpr (val_le_memB x i)

/-- `S` is nonempty. -/
noncomputable def nonemptyB (S : AName.{u} A) : A :=
  ⨆ x : AName.{u} A, memB x S

/-- `e ⊆ ⋃ S`. -/
noncomputable def subsetUnionB (e S : AName.{u} A) : A :=
  ⨅ x : AName.{u} A, memB x e ⇨ ⨆ y : AName.{u} A, memB y S ⊓ memB x y

/-- `x` is a `⊆`-upper bound of `S`. -/
noncomputable def isUpperBoundSubsetB (x S : AName.{u} A) : A :=
  ⨅ y : AName.{u} A, memB y S ⇨ subsetB y x

/-- `x` is the `⊆`-supremum of `S`. -/
noncomputable def isSupSubsetB (x S : AName.{u} A) : A :=
  isUpperBoundSubsetB x S ⊓
    ⨅ y : AName.{u} A, isUpperBoundSubsetB y S ⇨ subsetB x y

/-- `S` is directed under `⊆`. -/
noncomputable def isDirectedSubsetB (S : AName.{u} A) : A :=
  nonemptyB S ⊓
    ⨅ u : AName.{u} A, ⨅ v : AName.{u} A,
      memB u S ⊓ memB v S ⇨
        ⨆ w : AName.{u} A, memB w S ⊓ subsetB u w ⊓ subsetB v w

/-- `d ≪ e` in the subset order (CSL §4.1). -/
noncomputable def wayBelowSubsetB (d e : AName.{u} A) : A :=
  ⨅ S : AName.{u} A,
    isDirectedSubsetB S ⇨
      subsetUnionB e S ⇨
        ⨆ s : AName.{u} A, memB s S ⊓ subsetB d s

/-- `D` is a complete lattice under `⊆`. -/
noncomputable def isCompleteLatticeSubsetB (D : AName.{u} A) : A :=
  ⨅ S : AName.{u} A, subsetB S D ⇨
    ⨆ s : AName.{u} A, memB s D ⊓ isSupSubsetB s S

/-- `e ∈ D` and `e ≪ d`. -/
noncomputable def inWayBelowDownB (e d D : AName.{u} A) : A :=
  memB e D ⊓ wayBelowSubsetB e d

/-- `{e ∈ D | e ≪ d}` is directed. -/
noncomputable def directedDownB (d D : AName.{u} A) : A :=
  (⨆ e : AName.{u} A, inWayBelowDownB e d D) ⊓
    ⨅ e1 : AName.{u} A, ⨅ e2 : AName.{u} A,
      inWayBelowDownB e1 d D ⊓ inWayBelowDownB e2 d D ⇨
        ⨆ e3 : AName.{u} A,
          inWayBelowDownB e3 d D ⊓ subsetB e1 e3 ⊓ subsetB e2 e3

/-- `d = ⋃ {e ∈ D | e ≪ d}`. -/
noncomputable def joinsDownB (d D : AName.{u} A) : A :=
  ⨅ x : AName.{u} A,
    (memB x d ⇨ ⨆ e : AName.{u} A, inWayBelowDownB e d D ⊓ memB x e) ⊓
      ((⨆ e : AName.{u} A, inWayBelowDownB e d D ⊓ memB x e) ⇨ memB x d)

/-- Continuity of `D` at `d` (subset order). -/
noncomputable def isContinuousAtSubsetB (d D : AName.{u} A) : A :=
  directedDownB d D ⊓ joinsDownB d D

/-- `D` is a continuous lattice under `⊆`. -/
noncomputable def isContinuousLatticeSubsetB (D : AName.{u} A) : A :=
  isCompleteLatticeSubsetB D ⊓
    ⨅ d : AName.{u} A, memB d D ⇨ isContinuousAtSubsetB d D

/-- `B` is a base for `D` under `⊆`. -/
noncomputable def isBaseSubsetB (B D : AName.{u} A) : A :=
  subsetB B D ⊓
    ⨅ d : AName.{u} A, memB d D ⇨
      (⨆ e : AName.{u} A, memB e B ⊓ wayBelowSubsetB e d) ⊓
        ⨅ e1 : AName.{u} A, ⨅ e2 : AName.{u} A,
          memB e1 B ⊓ wayBelowSubsetB e1 d ⊓
            (memB e2 B ⊓ wayBelowSubsetB e2 d) ⇨
            ⨆ e3 : AName.{u} A,
              memB e3 B ⊓ wayBelowSubsetB e3 d ⊓
                subsetB e1 e3 ⊓ subsetB e2 e3 ⊓
        ⨅ x : AName.{u} A,
          (memB x d ⇨
            ⨆ e : AName.{u} A, memB e B ⊓ wayBelowSubsetB e d ⊓ memB x e) ⊓
            ((⨆ e : AName.{u} A, memB e B ⊓ wayBelowSubsetB e d ⊓ memB x e) ⇨
              memB x d)

/-!
## `𝔏_Set` formulas
-/

/-- `x ⊆ y` as `∀z (z ∈ x → z ∈ y)`. -/
def subsetF {n} (i j : Fin n) : SetFormula n :=
  .all (implies (.mem 0 i.succ) (.mem 0 j.succ))

/-- `∃x. x ∈ S`. -/
def nonemptyF {n} (S : Fin n) : SetFormula n :=
  .ex (.mem 0 S.succ)

/-- `e ⊆ ⋃ S` as `∀x (x ∈ e → ∃y (y ∈ S ∧ x ∈ y))`. -/
def subsetUnionF {n} (e S : Fin n) : SetFormula n :=
  .all (implies (.mem 0 e.succ)
    (.ex (.and (.mem 0 S.succ.succ) (.mem 1 0))))

/-- `x` is a `⊆`-upper bound of `S`. -/
def isUpperBoundSubsetF {n} (x S : Fin n) : SetFormula n :=
  .all (implies (.mem 0 S.succ) (subsetF 0 x.succ))

/-- `x` is the `⊆`-supremum of `S`. -/
def isSupSubsetF {n} (x S : Fin n) : SetFormula n :=
  (isUpperBoundSubsetF x S).and
    (.all (implies (isUpperBoundSubsetF 0 S.succ) (subsetF x.succ 0)))

/-- `S` is directed under `⊆`. -/
def isDirectedSubsetF {n} (S : Fin n) : SetFormula n :=
  (nonemptyF S).and
    (.all (.all (implies
      (.and (.mem 1 S.succ.succ) (.mem 0 S.succ.succ))
      (.ex (.and (.mem 0 S.succ.succ.succ)
        (.and (subsetF 2 0) (subsetF 1 0)))))))

/-- `d ≪ e` under `⊆`. -/
def wayBelowSubsetF {n} (d e : Fin n) : SetFormula n :=
  .all (implies (isDirectedSubsetF 0)
    (implies (subsetUnionF e.succ 0)
      (.ex (.and (.mem 0 1) (subsetF d.succ.succ 0)))))

/-- `D` is a complete lattice under `⊆`. -/
def isCompleteLatticeSubsetF {n} (D : Fin n) : SetFormula n :=
  .all (implies (subsetF 0 D.succ)
    (.ex (.and (.mem 0 D.succ.succ) (isSupSubsetF 0 1))))

/-- `e ∈ D ∧ e ≪ d`. -/
def inWayBelowDownF {n} (e d D : Fin n) : SetFormula n :=
  SetFormula.and (.mem e D) (wayBelowSubsetF e d)

/-- `{e ∈ D | e ≪ d}` is directed. -/
def directedDownF {n} (d D : Fin n) : SetFormula n :=
  SetFormula.and (.ex (inWayBelowDownF 0 d.succ D.succ))
    (.all (.all (implies
      (SetFormula.and (inWayBelowDownF 1 d.succ.succ D.succ.succ)
        (inWayBelowDownF 0 d.succ.succ D.succ.succ))
      (.ex (SetFormula.and (inWayBelowDownF 0 d.succ.succ.succ D.succ.succ.succ)
        (SetFormula.and (subsetF 2 0) (subsetF 1 0)))))))

/-- `d = ⋃ {e ∈ D | e ≪ d}`. -/
def joinsDownF {n} (d D : Fin n) : SetFormula n :=
  .all (iff (.mem 0 d.succ)
    (.ex (.and (inWayBelowDownF 0 d.succ.succ D.succ.succ) (.mem 1 0))))

/-- Continuity of `D` at `d`. -/
def isContinuousAtSubsetF {n} (d D : Fin n) : SetFormula n :=
  SetFormula.and (directedDownF d D) (joinsDownF d D)

/-- `D` is a continuous lattice under `⊆`. -/
def isContinuousLatticeSubsetF {n} (D : Fin n) : SetFormula n :=
  SetFormula.and (isCompleteLatticeSubsetF D)
    (.all (implies (.mem 0 D.succ) (isContinuousAtSubsetF 0 D.succ)))

/-- `≪` implies `⊆`, as a closed `𝔏_Set` sentence. -/
def wayBelow_le_formula : SetFormula 0 :=
  .all (.all (implies (wayBelowSubsetF 0 1) (subsetF 0 1)))

/-!
## Boolean values of the formulas
-/

theorem bval_subsetF {n} (i j : Fin n) (ρ : Fin n → AName.{u} A) :
    bval (subsetF i j) ρ = subsetB (ρ i) (ρ j) := by
  unfold subsetF
  rw [bval_all, subsetB_eq_iInf]
  refine iInf_congr fun z => ?_
  have hi : consName z ρ i.succ = ρ i := consName_succ z ρ i
  have hj : consName z ρ j.succ = ρ j := consName_succ z ρ j
  simp [bval_implies, bval_mem, hi, hj]

theorem bval_nonemptyF {n} (S : Fin n) (ρ : Fin n → AName.{u} A) :
    bval (nonemptyF S) ρ = nonemptyB (ρ S) := by
  unfold nonemptyF nonemptyB
  rw [bval_ex]
  refine iSup_congr fun x => ?_
  simp [bval_mem, consName_succ]

omit [CompleteBooleanAlgebra A] in
theorem consName_one {n} (v u : AName.{u} A) (ρ : Fin n → AName.{u} A) :
    consName v (consName u ρ) (1 : Fin (n + 2)) = u := by
  rw [show (1 : Fin (n + 2)) = (0 : Fin (n + 1)).succ from rfl,
    consName_succ, consName_zero]

omit [CompleteBooleanAlgebra A] in
theorem consName_two {n} (w v u : AName.{u} A) (ρ : Fin n → AName.{u} A) :
    consName w (consName v (consName u ρ)) (2 : Fin (n + 3)) = u := by
  rw [show (2 : Fin (n + 3)) = (1 : Fin (n + 2)).succ from rfl, consName_succ,
    consName_one]

theorem bval_subsetUnionF {n} (e S : Fin n) (ρ : Fin n → AName.{u} A) :
    bval (subsetUnionF e S) ρ = subsetUnionB (ρ e) (ρ S) := by
  unfold subsetUnionF subsetUnionB
  rw [bval_all]
  refine iInf_congr fun x => ?_
  have he : consName x ρ e.succ = ρ e := consName_succ x ρ e
  simp only [bval_implies, bval_mem, he]
  refine congrArg (fun t => memB x (ρ e) ⇨ t) ?_
  rw [bval_ex]
  refine iSup_congr fun y => ?_
  have hy0 : consName y (consName x ρ) 0 = y := consName_zero _ _
  have hx1 : consName y (consName x ρ) (1 : Fin (n + 2)) = x :=
    consName_one y x ρ
  have hS : consName y (consName x ρ) S.succ.succ = ρ S := by
    rw [consName_succ, consName_succ]
  simp [bval_and, bval_mem, hy0, hx1, hS]

theorem bval_isUpperBoundSubsetF {n} (x S : Fin n) (ρ : Fin n → AName.{u} A) :
    bval (isUpperBoundSubsetF x S) ρ = isUpperBoundSubsetB (ρ x) (ρ S) := by
  unfold isUpperBoundSubsetF isUpperBoundSubsetB
  rw [bval_all]
  refine iInf_congr fun y => ?_
  have hS : consName y ρ S.succ = ρ S := consName_succ y ρ S
  have hx : consName y ρ x.succ = ρ x := consName_succ y ρ x
  simp [bval_implies, bval_mem, bval_subsetF, hS, hx]

theorem bval_isSupSubsetF {n} (x S : Fin n) (ρ : Fin n → AName.{u} A) :
    bval (isSupSubsetF x S) ρ = isSupSubsetB (ρ x) (ρ S) := by
  unfold isSupSubsetF isSupSubsetB
  rw [bval_and, bval_isUpperBoundSubsetF]
  refine congrArg (fun t => isUpperBoundSubsetB (ρ x) (ρ S) ⊓ t) ?_
  rw [bval_all]
  refine iInf_congr fun y => ?_
  have hS : consName y ρ S.succ = ρ S := consName_succ y ρ S
  have hx : consName y ρ x.succ = ρ x := consName_succ y ρ x
  have hy0 : consName y ρ 0 = y := consName_zero _ _
  simp [bval_implies, bval_isUpperBoundSubsetF, bval_subsetF, hS, hx, hy0]

theorem bval_isDirectedSubsetF {n} (S : Fin n) (ρ : Fin n → AName.{u} A) :
    bval (isDirectedSubsetF S) ρ = isDirectedSubsetB (ρ S) := by
  unfold isDirectedSubsetF isDirectedSubsetB
  rw [bval_and, bval_nonemptyF]
  refine congrArg (fun t => nonemptyB (ρ S) ⊓ t) ?_
  rw [bval_all]
  refine iInf_congr fun u => ?_
  rw [bval_all]
  refine iInf_congr fun v => ?_
  have hS : consName v (consName u ρ) S.succ.succ = ρ S := by
    rw [consName_succ, consName_succ]
  have hu : consName v (consName u ρ) (1 : Fin (n + 2)) = u :=
    consName_one v u ρ
  have hv : consName v (consName u ρ) 0 = v := consName_zero _ _
  simp only [bval_implies, bval_and, bval_mem, hS, hu, hv]
  refine congrArg (fun t => memB u (ρ S) ⊓ memB v (ρ S) ⇨ t) ?_
  rw [bval_ex]
  refine iSup_congr fun w => ?_
  have hw0 : consName w (consName v (consName u ρ)) 0 = w := consName_zero _ _
  have hv1 : consName w (consName v (consName u ρ)) (1 : Fin (n + 3)) = v := by
    rw [show (1 : Fin (n + 3)) = (0 : Fin (n + 2)).succ from rfl,
      consName_succ, consName_zero]
  have hu2 : consName w (consName v (consName u ρ)) (2 : Fin (n + 3)) = u :=
    consName_two w v u ρ
  have hS' : consName w (consName v (consName u ρ)) S.succ.succ.succ = ρ S := by
    rw [consName_succ, consName_succ, consName_succ]
  simp [bval_and, bval_mem, bval_subsetF, hw0, hv1, hu2, hS']
  ac_rfl

theorem bval_wayBelowSubsetF {n} (d e : Fin n) (ρ : Fin n → AName.{u} A) :
    bval (wayBelowSubsetF d e) ρ = wayBelowSubsetB (ρ d) (ρ e) := by
  unfold wayBelowSubsetF wayBelowSubsetB
  rw [bval_all]
  refine iInf_congr fun S => ?_
  have h0 : consName S ρ 0 = S := consName_zero _ _
  have he : consName S ρ e.succ = ρ e := consName_succ S ρ e
  rw [bval_implies, bval_isDirectedSubsetF, h0]
  refine congrArg (fun t => isDirectedSubsetB S ⇨ t) ?_
  rw [bval_implies, bval_subsetUnionF, he, h0]
  refine congrArg (fun t => subsetUnionB (ρ e) S ⇨ t) ?_
  rw [bval_ex]
  refine iSup_congr fun s => ?_
  have hs0 : consName s (consName S ρ) 0 = s := consName_zero _ _
  have hS1 : consName s (consName S ρ) (1 : Fin (n + 2)) = S :=
    consName_one s S ρ
  have hd : consName s (consName S ρ) d.succ.succ = ρ d := by
    rw [consName_succ, consName_succ]
  simp [bval_and, bval_mem, bval_subsetF, hs0, hS1, hd]

theorem bval_isCompleteLatticeSubsetF {n} (D : Fin n)
    (ρ : Fin n → AName.{u} A) :
    bval (isCompleteLatticeSubsetF D) ρ =
      isCompleteLatticeSubsetB (ρ D) := by
  unfold isCompleteLatticeSubsetF isCompleteLatticeSubsetB
  rw [bval_all]
  refine iInf_congr fun S => ?_
  have hD : consName S ρ D.succ = ρ D := consName_succ S ρ D
  have h0 : consName S ρ 0 = S := consName_zero _ _
  simp only [bval_implies, bval_subsetF, hD, h0]
  refine congrArg (fun t => subsetB S (ρ D) ⇨ t) ?_
  rw [bval_ex]
  refine iSup_congr fun s => ?_
  have hs0 : consName s (consName S ρ) 0 = s := consName_zero _ _
  have hS1 : consName s (consName S ρ) (1 : Fin (n + 2)) = S :=
    consName_one s S ρ
  have hD' : consName s (consName S ρ) D.succ.succ = ρ D := by
    rw [consName_succ, consName_succ]
  simp [bval_and, bval_mem, bval_isSupSubsetF, hs0, hS1, hD']

theorem bval_inWayBelowDownF {n} (e d D : Fin n) (ρ : Fin n → AName.{u} A) :
    bval (inWayBelowDownF e d D) ρ = inWayBelowDownB (ρ e) (ρ d) (ρ D) := by
  unfold inWayBelowDownF inWayBelowDownB
  simp [bval_and, bval_mem, bval_wayBelowSubsetF]

/-!
## First content lemmas: `≪` implies `⊆`
-/

theorem nonemptyB_singleton (x : AName.{u} A) :
    nonemptyB (singletonB x) = ⊤ := by
  unfold nonemptyB
  refine top_unique (le_iSup_of_le x ?_)
  rw [memB_singletonB, eqB_self]

theorem isDirectedSubsetB_singleton (x : AName.{u} A) :
    isDirectedSubsetB (singletonB x) = ⊤ := by
  unfold isDirectedSubsetB
  rw [nonemptyB_singleton, top_inf_eq]
  refine iInf_eq_top.mpr fun u => iInf_eq_top.mpr fun v => ?_
  rw [himp_eq_top_iff, memB_singletonB, memB_singletonB]
  refine le_iSup_of_le x ?_
  rw [memB_singletonB, eqB_self, top_inf_eq]
  exact le_inf (inf_le_of_left_le (eqB_le_subsetB u x))
    (inf_le_of_right_le (eqB_le_subsetB v x))

theorem subsetUnionB_singleton (e : AName.{u} A) :
    subsetUnionB e (singletonB e) = ⊤ := by
  unfold subsetUnionB
  refine iInf_eq_top.mpr fun x => himp_eq_top_iff.mpr ?_
  refine le_iSup_of_le e ?_
  rw [memB_singletonB, eqB_self, top_inf_eq]

theorem subsetB_eqB_right (s e d : AName.{u} A) :
    subsetB d s ⊓ eqB s e ≤ subsetB d e := by
  have hse : eqB s e ≤ subsetB s e := eqB_le_subsetB s e
  exact (subsetB_trans d s e).trans' (le_inf inf_le_left (inf_le_of_right_le hse))

/-- CSL §4.1: `d ≪ e` implies `d ⊆ e` (take the directed set `{e}`). -/
theorem wayBelowSubsetB_le_subsetB (d e : AName.{u} A) :
    wayBelowSubsetB d e ≤ subsetB d e := by
  have hinst :=
    iInf_le (fun S : AName.{u} A =>
      isDirectedSubsetB S ⇨
        subsetUnionB e S ⇨
          ⨆ s : AName.{u} A, memB s S ⊓ subsetB d s) (singletonB e)
  have hdir : isDirectedSubsetB (singletonB e) = ⊤ :=
    isDirectedSubsetB_singleton e
  have hun : subsetUnionB e (singletonB e) = ⊤ :=
    subsetUnionB_singleton e
  have himp : (⊤ : A) ⇨ (⊤ ⇨ ⨆ s, memB s (singletonB e) ⊓ subsetB d s) =
      ⨆ s, memB s (singletonB e) ⊓ subsetB d s := by
    simp
  have hle : wayBelowSubsetB d e ≤
      ⨆ s, memB s (singletonB e) ⊓ subsetB d s := by
    unfold wayBelowSubsetB
    convert hinst using 1
    rw [hdir, hun]
    exact himp.symm
  refine hle.trans (iSup_le fun s => ?_)
  rw [memB_singletonB, inf_comm]
  exact subsetB_eqB_right s e d

/-- The closed sentence “`≪` implies `⊆`” has Boolean value `1`. -/
theorem wayBelow_le_formula_valid (ρ : Fin 0 → AName.{u} A) :
    bval wayBelow_le_formula ρ = ⊤ := by
  unfold wayBelow_le_formula
  refine iInf_eq_top.mpr fun e => iInf_eq_top.mpr fun d => ?_
  have hd : consName d (consName e ρ) (0 : Fin 2) = d := consName_zero _ _
  have he : consName d (consName e ρ) (1 : Fin 2) = e := consName_one d e ρ
  rw [bval_implies, himp_eq_top_iff, bval_wayBelowSubsetF, bval_subsetF, hd, he]
  exact wayBelowSubsetB_le_subsetB d e

/-!
## Finite names and `P_fin^A`
-/

theorem memB_pfinB (S X : AName.{u} A) :
    memB S (pfinB X) = subsetB S X ⊓ isFiniteB S := by
  rw [pfinB, memB_sepB S (powerB X) isFiniteB isFiniteB_congr, memB_powerB]

theorem eqB_of_memB_iff (X Y : AName.{u} A)
    (h : ∀ z, memB z X = memB z Y) : eqB X Y = ⊤ := by
  rw [eqB_eq_iInf]
  refine iInf_eq_top.mpr fun z => ?_
  rw [h, himp_self, inf_top_eq]

theorem memB_finsetB {n} (z : AName.{u} A) (xs : Fin n → AName.{u} A) :
    memB z (finsetB xs) = ⨆ i : Fin n, eqB z (xs i) := by
  unfold finsetB
  rw [memB_mk]
  refine le_antisymm ?le ?ge
  · refine iSup_le fun i => ?_
    rw [inf_top_eq]
    exact le_iSup (fun j : Fin n => eqB z (xs j)) i.down
  · refine iSup_le fun i => ?_
    refine le_iSup_of_le ⟨i⟩ ?_
    rw [inf_top_eq]

theorem isFiniteB_finsetB {n} (xs : Fin n → AName.{u} A) :
    isFiniteB (finsetB xs) = ⊤ := by
  unfold isFiniteB
  refine top_unique (le_iSup_of_le n (le_iSup_of_le xs ?_))
  rw [eqB_self]

theorem eqB_check_empty_finsetB0 :
    eqB (check (A := A) (∅ : PSet.{u}))
      (finsetB (fun i : Fin 0 => i.elim0)) = ⊤ := by
  have hempty : (∅ : PSet.{u}) = PSet.mk PEmpty PEmpty.elim := PSet.empty_def
  refine eqB_of_memB_iff _ _ fun z => ?_
  rw [memB_check_empty, memB_finsetB, iSup_of_empty]

theorem isFiniteB_empty :
    isFiniteB (check (A := A) (∅ : PSet.{u})) = ⊤ := by
  unfold isFiniteB
  refine top_unique (le_iSup_of_le (0 : ℕ)
    (le_iSup_of_le (fun i : Fin 0 => i.elim0) ?_))
  exact eqB_check_empty_finsetB0.ge

theorem eqB_singletonB_finsetB1 (x : AName.{u} A) :
    eqB (singletonB x) (finsetB (fun _ : Fin 1 => x)) = ⊤ := by
  refine eqB_of_memB_iff _ _ fun z => ?_
  rw [memB_singletonB, memB_finsetB]
  refine le_antisymm ?le ?ge
  · exact le_iSup_of_le (0 : Fin 1) le_rfl
  · exact iSup_le fun _ => le_rfl

theorem isFiniteB_singleton (x : AName.{u} A) :
    isFiniteB (singletonB x) = ⊤ := by
  unfold isFiniteB
  refine top_unique (le_iSup_of_le (1 : ℕ)
    (le_iSup_of_le (fun _ : Fin 1 => x) ?_))
  exact (eqB_singletonB_finsetB1 x).ge

/-- Binary union name, as the disjoint union of domains. -/
noncomputable def union2B (U V : AName.{u} A) : AName.{u} A :=
  mk (ULift.{u} (Sum U.idx V.idx))
    (fun i => match i.down with
      | .inl j => U.child j
      | .inr k => V.child k)
    (fun i => match i.down with
      | .inl j => U.val j
      | .inr k => V.val k)

theorem memB_union2B (z U V : AName.{u} A) :
    memB z (union2B U V) = memB z U ⊔ memB z V := by
  unfold union2B
  rw [memB_mk, memB_eq (x := z) (y := U), memB_eq (x := z) (y := V)]
  refine le_antisymm ?le ?ge
  · refine iSup_le fun i => ?_
    cases i.down with
    | inl j =>
      exact le_sup_of_le_left (le_iSup_of_le j le_rfl)
    | inr k =>
      exact le_sup_of_le_right (le_iSup_of_le k le_rfl)
  · refine sup_le ?_ ?_
    · refine iSup_le fun j => ?_
      exact le_iSup_of_le ⟨.inl j⟩ le_rfl
    · refine iSup_le fun k => ?_
      exact le_iSup_of_le ⟨.inr k⟩ le_rfl

theorem subsetB_union2B_left (U V : AName.{u} A) :
    subsetB U (union2B U V) = ⊤ := by
  rw [subsetB_eq_iInf]
  refine iInf_eq_top.mpr fun z => himp_eq_top_iff.mpr ?_
  rw [memB_union2B]
  exact le_sup_left

theorem subsetB_union2B_right (U V : AName.{u} A) :
    subsetB V (union2B U V) = ⊤ := by
  rw [subsetB_eq_iInf]
  refine iInf_eq_top.mpr fun z => himp_eq_top_iff.mpr ?_
  rw [memB_union2B]
  exact le_sup_right

theorem himp_sup_eq (a b c : A) : (a ⊔ b) ⇨ c = (a ⇨ c) ⊓ (b ⇨ c) :=
  le_antisymm
    (le_inf (himp_le_himp_right le_sup_left) (himp_le_himp_right le_sup_right))
    (le_himp_iff.mpr (by
      have hcomm : (a ⇨ c) ⊓ (b ⇨ c) ⊓ (a ⊔ b) =
          (a ⊔ b) ⊓ ((a ⇨ c) ⊓ (b ⇨ c)) := inf_comm _ _
      rw [hcomm, inf_sup_right]
      refine sup_le ?_ ?_
      · have : a ⊓ ((a ⇨ c) ⊓ (b ⇨ c)) = (a ⇨ c) ⊓ (b ⇨ c) ⊓ a := by ac_rfl
        rw [this]
        exact (inf_le_inf_right a inf_le_left).trans himp_inf_le
      · have : b ⊓ ((a ⇨ c) ⊓ (b ⇨ c)) = (a ⇨ c) ⊓ (b ⇨ c) ⊓ b := by ac_rfl
        rw [this]
        exact (inf_le_inf_right b inf_le_right).trans himp_inf_le))

theorem subsetB_union2B (U V T : AName.{u} A) :
    subsetB (union2B U V) T = subsetB U T ⊓ subsetB V T := by
  rw [subsetB_eq_iInf, subsetB_eq_iInf, subsetB_eq_iInf]
  refine le_antisymm ?le ?ge
  · refine le_inf (le_iInf fun z => ?_) (le_iInf fun z => ?_)
    · have hz := iInf_le (fun z : AName.{u} A => memB z (union2B U V) ⇨ memB z T) z
      rw [memB_union2B] at hz
      exact hz.trans (himp_le_himp_right
        (le_sup_left : memB z U ≤ memB z U ⊔ memB z V))
    · have hz := iInf_le (fun z : AName.{u} A => memB z (union2B U V) ⇨ memB z T) z
      rw [memB_union2B] at hz
      exact hz.trans (himp_le_himp_right
        (le_sup_right : memB z V ≤ memB z U ⊔ memB z V))
  · refine le_iInf fun z => ?_
    have hU := iInf_le (fun z : AName.{u} A => memB z U ⇨ memB z T) z
    have hV := iInf_le (fun z : AName.{u} A => memB z V ⇨ memB z T) z
    rw [memB_union2B, himp_sup_eq]
    exact le_inf (inf_le_of_left_le hU) (inf_le_of_right_le hV)

theorem eqB_union2B_congr (U U' V V' : AName.{u} A) :
    eqB U U' ⊓ eqB V V' ≤ eqB (union2B U V) (union2B U' V') := by
  rw [eqB_eq_iInf (union2B U V) (union2B U' V')]
  refine le_iInf (α := A) (ι := AName.{u} A) fun z => ?_
  have hU : eqB U U' ⊓ memB z U ≤ memB z U' := by
    rw [inf_comm]; exact memB_eqB_right U z U'
  have hV : eqB V V' ⊓ memB z V ≤ memB z V' := by
    rw [inf_comm]; exact memB_eqB_right V z V'
  have hU' : eqB U U' ⊓ memB z U' ≤ memB z U := by
    rw [eqB_comm (x := U) (y := U'), inf_comm]
    exact memB_eqB_right U' z U
  have hV' : eqB V V' ⊓ memB z V' ≤ memB z V := by
    rw [eqB_comm (x := V) (y := V'), inf_comm]
    exact memB_eqB_right V' z V
  refine le_inf ?fwd ?bwd
  · rw [le_himp_iff, memB_union2B, memB_union2B]
    refine (inf_le_inf_left _ le_rfl).trans ?_
    rw [inf_sup_left]
    exact sup_le
      (le_sup_of_le_left (hU.trans' (inf_le_inf_right _ inf_le_left)))
      (le_sup_of_le_right (hV.trans' (inf_le_inf_right _ inf_le_right)))
  · rw [le_himp_iff, memB_union2B, memB_union2B]
    refine (inf_le_inf_left _ le_rfl).trans ?_
    rw [inf_sup_left]
    exact sup_le
      (le_sup_of_le_left (hU'.trans' (inf_le_inf_right _ inf_le_left)))
      (le_sup_of_le_right (hV'.trans' (inf_le_inf_right _ inf_le_right)))

theorem memB_finsetB_addCases {n m} (z : AName.{u} A)
    (xs : Fin n → AName.{u} A) (ys : Fin m → AName.{u} A) :
    memB z (finsetB (Fin.addCases (motive := fun _ => AName.{u} A) xs ys)) =
      memB z (finsetB xs) ⊔ memB z (finsetB ys) := by
  rw [memB_finsetB, memB_finsetB, memB_finsetB]
  refine le_antisymm ?le ?ge
  · refine iSup_le fun i => ?_
    refine Fin.addCases (motive := fun i =>
        eqB z (Fin.addCases (motive := fun _ => AName.{u} A) xs ys i) ≤
          (⨆ j : Fin n, eqB z (xs j)) ⊔ ⨆ k : Fin m, eqB z (ys k)) ?l ?r i
    · intro j
      rw [Fin.addCases_left]
      exact le_sup_of_le_left (le_iSup (fun j' => eqB z (xs j')) j)
    · intro k
      rw [Fin.addCases_right]
      exact le_sup_of_le_right (le_iSup (fun k' => eqB z (ys k')) k)
  · refine sup_le ?_ ?_
    · refine iSup_le fun j => ?_
      exact le_iSup_of_le (Fin.castAdd m j) (by
        rw [Fin.addCases_left])
    · refine iSup_le fun k => ?_
      exact le_iSup_of_le (Fin.natAdd n k) (by
        rw [Fin.addCases_right])

theorem eqB_union2B_finsetB {n m} (xs : Fin n → AName.{u} A)
    (ys : Fin m → AName.{u} A) :
    eqB (union2B (finsetB xs) (finsetB ys))
      (finsetB (Fin.addCases (motive := fun _ => AName.{u} A) xs ys)) = ⊤ := by
  refine eqB_of_memB_iff _ _ fun z => ?_
  rw [memB_union2B, memB_finsetB_addCases]

theorem isFiniteB_union2B (U V : AName.{u} A) :
    isFiniteB U ⊓ isFiniteB V ≤ isFiniteB (union2B U V) := by
  unfold isFiniteB
  rw [iSup_inf_eq]
  refine iSup_le fun n => ?_
  rw [iSup_inf_eq]
  refine iSup_le fun xs => ?_
  rw [inf_iSup_eq]
  refine iSup_le fun m => ?_
  rw [inf_iSup_eq]
  refine iSup_le fun ys => ?_
  refine le_iSup_of_le (n + m)
    (le_iSup_of_le (Fin.addCases (motive := fun _ => AName.{u} A) xs ys) ?_)
  have hcongr := eqB_union2B_congr U (finsetB xs) V (finsetB ys)
  have hfin := eqB_union2B_finsetB (A := A) xs ys
  have htrans :=
    eqB_trans (union2B U V) (union2B (finsetB xs) (finsetB ys))
      (finsetB (Fin.addCases (motive := fun _ => AName.{u} A) xs ys))
  refine htrans.trans' (le_inf hcongr ?_)
  exact le_top.trans hfin.ge

theorem nonemptyB_pfinB (T : AName.{u} A) :
    nonemptyB (pfinB T) = ⊤ := by
  unfold nonemptyB
  refine top_unique (le_iSup_of_le (check (A := A) (∅ : PSet.{u})) ?_)
  rw [memB_pfinB]
  have hemp : subsetB (check (A := A) (∅ : PSet.{u})) T = ⊤ := by
    rw [subsetB_eq_iInf]
    refine iInf_eq_top.mpr fun z => himp_eq_top_iff.mpr ?_
    rw [memB_check_empty]
    exact bot_le
  rw [hemp, isFiniteB_empty, inf_top_eq]

theorem isDirectedSubsetB_pfinB (T : AName.{u} A) :
    isDirectedSubsetB (pfinB T) = ⊤ := by
  unfold isDirectedSubsetB
  rw [nonemptyB_pfinB, top_inf_eq]
  refine iInf_eq_top.mpr fun U => iInf_eq_top.mpr fun V => ?_
  rw [himp_eq_top_iff, memB_pfinB, memB_pfinB]
  refine le_iSup_of_le (union2B U V) ?_
  have hmem : subsetB U T ⊓ isFiniteB U ⊓ (subsetB V T ⊓ isFiniteB V) ≤
      memB (union2B U V) (pfinB T) := by
    rw [memB_pfinB, subsetB_union2B]
    refine le_inf ?sub ?fin
    · exact le_inf (inf_le_of_left_le inf_le_left)
        (inf_le_of_right_le inf_le_left)
    · exact (isFiniteB_union2B U V).trans'
        (le_inf (inf_le_of_left_le inf_le_right)
          (inf_le_of_right_le inf_le_right))
  refine le_inf (le_inf hmem ?_) ?_
  · exact le_top.trans (subsetB_union2B_left U V).ge
  · exact le_top.trans (subsetB_union2B_right U V).ge

theorem subsetUnionB_pfinB (T : AName.{u} A) :
    subsetUnionB T (pfinB T) = ⊤ := by
  unfold subsetUnionB
  refine iInf_eq_top.mpr fun x => himp_eq_top_iff.mpr ?_
  refine le_iSup_of_le (singletonB x) ?_
  have hmem : memB x T ≤ memB (singletonB x) (pfinB T) := by
    rw [memB_pfinB, subsetB_singletonB, isFiniteB_singleton, inf_top_eq]
  have hx : memB x (singletonB x) = ⊤ := by
    rw [memB_singletonB, eqB_self]
  refine le_inf hmem ?_
  exact le_top.trans hx.ge

/-- Instantiating `≪` at `P_fin^A(T)`: some finite `U ⊆ T` has `S ⊆ U`.
Not `proposition_27`: that paper name is the ground `Set X` statement. -/
theorem wayBelowSubsetB_le_exists_pfin (S T : AName.{u} A) :
    wayBelowSubsetB S T ≤
      ⨆ U : AName.{u} A, memB U (pfinB T) ⊓ subsetB S U := by
  have hinst :=
    iInf_le (fun 𝒟 : AName.{u} A =>
      isDirectedSubsetB 𝒟 ⇨
        subsetUnionB T 𝒟 ⇨
          ⨆ U : AName.{u} A, memB U 𝒟 ⊓ subsetB S U) (pfinB T)
  have hdir : isDirectedSubsetB (pfinB T) = ⊤ := isDirectedSubsetB_pfinB T
  have hun : subsetUnionB T (pfinB T) = ⊤ := subsetUnionB_pfinB T
  unfold wayBelowSubsetB
  convert hinst using 1
  rw [hdir, hun]
  simp

/-!
## Subsets of finite names are finite
-/

theorem isFiniteB_of_eqB (S T : AName.{u} A) :
    eqB S T ⊓ isFiniteB T ≤ isFiniteB S := by
  rw [eqB_comm (x := S) (y := T)]
  exact isFiniteB_congr T S

theorem subsetB_restrictName (S X : AName.{u} A) :
    subsetB (restrictName S X) X = ⊤ :=
  subsetB_of_le_val X (fun i => X.val i ⊓ memB (X.child i) S) (fun _ => inf_le_left)

theorem memB_restrictName (z S X : AName.{u} A) :
    memB z (restrictName S X) = memB z S ⊓ memB z X := by
  unfold restrictName
  rw [memB_mk, memB_eq (x := z) (y := X)]
  refine le_antisymm ?le ?ge
  · refine iSup_le fun i => ?_
    have hS : eqB z (X.child i) ⊓ memB (X.child i) S ≤ memB z S := by
      rw [eqB_comm (x := z) (y := X.child i), inf_comm]
      exact memB_eqB_left (X.child i) S z
    have hX : eqB z (X.child i) ⊓ X.val i ≤
        ⨆ j, eqB z (X.child j) ⊓ X.val j :=
      le_iSup_of_le i le_rfl
    refine le_inf ?_ ?_
    · exact hS.trans' (le_inf inf_le_left (inf_le_of_right_le inf_le_right))
    · exact hX.trans' (le_inf inf_le_left (inf_le_of_right_le inf_le_left))
  · rw [inf_iSup_eq]
    refine iSup_le fun i => ?_
    refine le_iSup_of_le i ?_
    have hS : memB z S ⊓ eqB z (X.child i) ≤ memB (X.child i) S :=
      memB_eqB_left z S (X.child i)
    refine le_inf (inf_le_of_right_le inf_le_left) ?_
    exact le_inf (inf_le_of_right_le inf_le_right)
      (hS.trans' (le_inf inf_le_left (inf_le_of_right_le inf_le_left)))

theorem memB_union2B_restrict (z S U V : AName.{u} A) :
    memB z (union2B (restrictName S U) (restrictName S V)) =
      memB z S ⊓ memB z (union2B U V) := by
  rw [memB_union2B, memB_restrictName, memB_restrictName, memB_union2B,
    inf_sup_left]

theorem himp_inf_self (a b : A) : a ⇨ a ⊓ b = a ⇨ b := by
  refine le_antisymm ?fwd ?bwd
  · rw [le_himp_iff]
    exact (himp_inf_le (a := a) (b := a ⊓ b)).trans inf_le_right
  · rw [le_himp_iff]
    exact le_inf inf_le_right himp_inf_le

theorem eqB_union2B_restrict (S U V : AName.{u} A) :
    eqB S (union2B (restrictName S U) (restrictName S V)) =
      subsetB S (union2B U V) := by
  rw [eqB_eq_iInf, subsetB_eq_iInf]
  refine iInf_congr fun z => ?_
  rw [memB_union2B_restrict]
  have hbwd : (memB z S ⊓ memB z (union2B U V) ⇨ memB z S) = ⊤ :=
    himp_eq_top_iff.mpr inf_le_left
  rw [himp_inf_self, hbwd, inf_top_eq]

theorem memB_finsetB_succ {n} (z : AName.{u} A) (xs : Fin (n + 1) → AName.{u} A) :
    memB z (finsetB xs) =
      eqB z (xs 0) ⊔ memB z (finsetB (fun i : Fin n => xs i.succ)) := by
  rw [memB_finsetB, memB_finsetB]
  refine le_antisymm ?le ?ge
  · refine iSup_le fun i => ?_
    refine Fin.cases ?_ ?_ i
    · exact le_sup_left
    · intro j
      exact le_sup_of_le_right (le_iSup (fun k : Fin n => eqB z (xs k.succ)) j)
  · refine sup_le ?_ ?_
    · exact le_iSup_of_le (0 : Fin (n + 1)) le_rfl
    · refine iSup_le fun j => ?_
      exact le_iSup_of_le j.succ le_rfl

theorem eqB_finsetB_cons {n} (xs : Fin (n + 1) → AName.{u} A) :
    eqB (finsetB xs)
      (union2B (singletonB (xs 0)) (finsetB (fun i : Fin n => xs i.succ))) = ⊤ := by
  refine eqB_of_memB_iff _ _ fun z => ?_
  rw [memB_finsetB_succ, memB_union2B, memB_singletonB]

theorem subsetB_finsetB0 {n} (xs : Fin n → AName.{u} A) (S : AName.{u} A)
    (hn : n = 0) :
    subsetB (finsetB xs) S = ⊤ := by
  subst hn
  unfold finsetB
  rw [subsetB_mk]
  exact iInf_eq_top.mpr fun i => nomatch i.down

theorem memB_finsetB0 {n} (z : AName.{u} A) (xs : Fin n → AName.{u} A)
    (hn : n = 0) : memB z (finsetB xs) = ⊥ := by
  subst hn
  rw [memB_finsetB]
  exact iSup_of_empty _

/-- A name contained in a singleton is empty or that singleton. -/
theorem isFiniteB_of_subset_singleton (S x : AName.{u} A) :
    subsetB S (singletonB x) ≤ isFiniteB S := by
  have hsplit : subsetB S (singletonB x) =
      (subsetB S (singletonB x) ⊓ memB x S) ⊔
        (subsetB S (singletonB x) ⊓ (memB x S)ᶜ) := by
    have htop : memB x S ⊔ (memB x S)ᶜ = ⊤ := sup_compl_eq_top
    calc subsetB S (singletonB x)
        = subsetB S (singletonB x) ⊓ ⊤ := (inf_top_eq _).symm
      _ = subsetB S (singletonB x) ⊓ (memB x S ⊔ (memB x S)ᶜ) := by rw [htop]
      _ = (subsetB S (singletonB x) ⊓ memB x S) ⊔
            (subsetB S (singletonB x) ⊓ (memB x S)ᶜ) := inf_sup_left _ _ _
  rw [hsplit]
  refine sup_le ?yes ?no
  · have heq : subsetB S (singletonB x) ⊓ memB x S = eqB S (singletonB x) := by
      rw [eqB_eq_subset, subsetB_singletonB]
    rw [heq]
    exact (isFiniteB_of_eqB S (singletonB x)).trans'
      (le_inf le_rfl (le_top.trans (isFiniteB_singleton x).ge))
  · have hempty : subsetB S (singletonB x) ⊓ (memB x S)ᶜ ≤
        subsetB S (finsetB (fun i : Fin 0 => i.elim0)) := by
      rw [subsetB_eq_iInf S (finsetB (fun i : Fin 0 => i.elim0))]
      refine le_iInf fun z => ?_
      rw [le_himp_iff, memB_finsetB0 z _ rfl]
      have hzx : subsetB S (singletonB x) ⊓ memB z S ≤ eqB z x := by
        have h := memB_of_subsetB z S (singletonB x)
        rw [memB_singletonB, inf_comm] at h
        exact h
      have hx : eqB z x ⊓ memB z S ≤ memB x S := by
        rw [inf_comm]
        exact memB_eqB_left z S x
      have hbot : subsetB S (singletonB x) ⊓ (memB x S)ᶜ ⊓ memB z S ≤ ⊥ := by
        have hre :
            subsetB S (singletonB x) ⊓ (memB x S)ᶜ ⊓ memB z S ≤
              subsetB S (singletonB x) ⊓ memB z S ⊓ (memB x S)ᶜ :=
          le_inf
            (le_inf (inf_le_of_left_le inf_le_left) inf_le_right)
            (inf_le_of_left_le inf_le_right)
        have hmem : subsetB S (singletonB x) ⊓ memB z S ⊓ (memB x S)ᶜ ≤ ⊥ := by
          have h1 : subsetB S (singletonB x) ⊓ memB z S ⊓ (memB x S)ᶜ ≤
              eqB z x ⊓ memB z S ⊓ (memB x S)ᶜ :=
            inf_le_inf_right _ (le_inf hzx inf_le_right)
          have h2 : eqB z x ⊓ memB z S ⊓ (memB x S)ᶜ ≤ memB x S ⊓ (memB x S)ᶜ :=
            inf_le_inf_right _ hx
          exact h1.trans (h2.trans (le_of_eq inf_compl_eq_bot))
        exact hre.trans hmem
      exact hbot
    have heq : subsetB S (finsetB (fun i : Fin 0 => i.elim0)) ≤
        eqB S (finsetB (fun i : Fin 0 => i.elim0)) := by
      rw [eqB_eq_subset, subsetB_finsetB0 (fun i : Fin 0 => i.elim0) S rfl,
        inf_top_eq]
    refine (hempty.trans heq).trans ?_
    exact (isFiniteB_of_eqB S (finsetB (fun i : Fin 0 => i.elim0))).trans'
      (le_inf le_rfl (le_top.trans (isFiniteB_finsetB _).ge))

/-- A name contained in a finite enumeration is finite. -/
theorem isFiniteB_of_subset_finsetB {n} (S : AName.{u} A)
    (xs : Fin n → AName.{u} A) :
    subsetB S (finsetB xs) ≤ isFiniteB S := by
  induction n generalizing S with
  | zero =>
    have hempty : subsetB (finsetB xs) S = ⊤ := subsetB_finsetB0 xs S rfl
    have heq : subsetB S (finsetB xs) ≤ eqB S (finsetB xs) := by
      rw [eqB_eq_subset, hempty, inf_top_eq]
    exact heq.trans ((isFiniteB_of_eqB S (finsetB xs)).trans'
      (le_inf le_rfl (le_top.trans (isFiniteB_finsetB xs).ge)))
  | succ n ih =>
    have hcons : eqB (finsetB xs)
        (union2B (singletonB (xs 0))
          (finsetB (fun i : Fin n => xs i.succ))) = ⊤ :=
      eqB_finsetB_cons xs
    have hsub : subsetB S (finsetB xs) ≤
        subsetB S (union2B (singletonB (xs 0))
          (finsetB (fun i : Fin n => xs i.succ))) := by
      have hle : subsetB (finsetB xs)
          (union2B (singletonB (xs 0))
            (finsetB (fun i : Fin n => xs i.succ))) = ⊤ :=
        top_unique (hcons.ge.trans (eqB_le_subsetB _ _))
      have htr := subsetB_trans S (finsetB xs)
        (union2B (singletonB (xs 0))
          (finsetB (fun i : Fin n => xs i.succ)))
      rw [hle, inf_top_eq] at htr
      exact htr
    refine hsub.trans ?_
    set head := xs 0
    set rest := fun i : Fin n => xs i.succ
    set S0 := restrictName S (singletonB head)
    set S1 := restrictName S (finsetB rest)
    have hS0 : isFiniteB S0 = ⊤ :=
      top_unique ((subsetB_restrictName S (singletonB head)).ge.trans
        (isFiniteB_of_subset_singleton S0 head))
    have hS1 : isFiniteB S1 = ⊤ :=
      top_unique ((subsetB_restrictName S (finsetB rest)).ge.trans (ih S1 rest))
    have hU : isFiniteB (union2B S0 S1) = ⊤ :=
      top_unique ((le_inf hS0.ge hS1.ge).trans (isFiniteB_union2B S0 S1))
    have heq : subsetB S (union2B (singletonB head) (finsetB rest)) ≤
        eqB S (union2B S0 S1) := (eqB_union2B_restrict S (singletonB head)
          (finsetB rest)).ge
    exact heq.trans ((isFiniteB_of_eqB S (union2B S0 S1)).trans'
      (le_inf le_rfl (le_top.trans hU.ge)))

/-- A ⊆-subset of a finite name is finite. -/
theorem isFiniteB_of_subset (S U : AName.{u} A) :
    subsetB S U ⊓ isFiniteB U ≤ isFiniteB S := by
  unfold isFiniteB
  rw [inf_iSup_eq]
  refine iSup_le fun n => ?_
  rw [inf_iSup_eq]
  refine iSup_le fun xs => ?_
  have hsub : subsetB S U ⊓ eqB U (finsetB xs) ≤ subsetB S (finsetB xs) := by
    have htr := subsetB_trans S U (finsetB xs)
    exact htr.trans' (le_inf inf_le_left
      (inf_le_of_right_le (eqB_le_subsetB U (finsetB xs))))
  exact hsub.trans (isFiniteB_of_subset_finsetB S xs)

/-- `≪` implies finite and `⊆`. Not `proposition_27`. -/
theorem wayBelowSubsetB_le_finite_subset (S T : AName.{u} A) :
    wayBelowSubsetB S T ≤ isFiniteB S ⊓ subsetB S T := by
  refine le_inf ?fin ?sub
  · refine (wayBelowSubsetB_le_exists_pfin S T).trans (iSup_le fun U => ?_)
    rw [memB_pfinB]
    exact (isFiniteB_of_subset S U).trans'
      (le_inf inf_le_right (inf_le_of_left_le inf_le_right))
  · exact wayBelowSubsetB_le_subsetB S T

/-!
## Converse: finite `⊆` implies `≪`
-/

theorem subsetB_eqB_congr_left {X Y Z : AName.{u} A} (h : eqB X Y = ⊤) :
    subsetB X Z = subsetB Y Z := by
  refine le_antisymm ?_ ?_
  · have := subsetB_of_eqB X Y Z
    rw [h, top_inf_eq] at this
    exact this
  · have := subsetB_of_eqB Y X Z
    rw [eqB_comm (x := Y) (y := X), h, top_inf_eq] at this
    exact this

theorem subsetUnionB_apply (T 𝒟 x : AName.{u} A) :
    memB x T ⊓ subsetUnionB T 𝒟 ≤ ⨆ y, memB y 𝒟 ⊓ memB x y := by
  unfold subsetUnionB
  have h :=
    iInf_le (fun x' : AName.{u} A =>
      memB x' T ⇨ ⨆ y, memB y 𝒟 ⊓ memB x' y) x
  refine (le_himp_iff.mp h).trans' ?_
  rw [inf_comm]

theorem isDirectedSubsetB_apply (𝒟 u v : AName.{u} A) :
    isDirectedSubsetB 𝒟 ⊓ memB u 𝒟 ⊓ memB v 𝒟 ≤
      ⨆ w, memB w 𝒟 ⊓ subsetB u w ⊓ subsetB v w := by
  unfold isDirectedSubsetB
  have hp :=
    iInf_le (fun u' : AName.{u} A =>
      ⨅ v' : AName.{u} A,
        memB u' 𝒟 ⊓ memB v' 𝒟 ⇨
          ⨆ w, memB w 𝒟 ⊓ subsetB u' w ⊓ subsetB v' w) u
  have hp' :=
    iInf_le (fun v' : AName.{u} A =>
      memB u 𝒟 ⊓ memB v' 𝒟 ⇨
        ⨆ w, memB w 𝒟 ⊓ subsetB u w ⊓ subsetB v' w) v
  have hle := hp.trans hp'
  have hpair : (⨅ u' : AName.{u} A, ⨅ v' : AName.{u} A,
        memB u' 𝒟 ⊓ memB v' 𝒟 ⇨
          ⨆ w, memB w 𝒟 ⊓ subsetB u' w ⊓ subsetB v' w) ⊓
      memB u 𝒟 ⊓ memB v 𝒟 ≤
      ⨆ w, memB w 𝒟 ⊓ subsetB u w ⊓ subsetB v w := by
    have h := le_himp_iff.mp hle
    refine h.trans' ?_
    exact le_inf (inf_le_of_left_le inf_le_left)
      (le_inf (inf_le_of_left_le inf_le_right) inf_le_right)
  refine hpair.trans' ?_
  exact inf_le_inf_right _ (inf_le_inf_right _ inf_le_right)

theorem iSup_inf_iSup_eq {ι κ : Type*} (f : ι → A) (g : κ → A) :
    (⨆ i, f i) ⊓ ⨆ j, g j = ⨆ i, ⨆ j, f i ⊓ g j := by
  refine le_antisymm ?le ?ge
  · have h : (⨆ i, f i) ⊓ ⨆ j, g j = ⨆ j, (⨆ i, f i) ⊓ g j :=
      inf_iSup_eq _ _
    rw [h]
    refine iSup_le fun j => ?_
    have h' : (⨆ i, f i) ⊓ g j = ⨆ i, f i ⊓ g j := by
      rw [inf_comm, inf_iSup_eq]
      exact iSup_congr fun i => inf_comm (a := g j) (b := f i)
    rw [h']
    refine iSup_le fun i => le_iSup_of_le i (le_iSup_of_le j le_rfl)
  · refine iSup_le fun i => iSup_le fun j =>
      le_inf (le_iSup_of_le i inf_le_left) (le_iSup_of_le j inf_le_right)

/-- A finite enumeration contained in `T ⊆ ⋃ 𝒟` for directed `𝒟` sits
inside some member of `𝒟`. -/
theorem finsetB_le_exists_directed {n} (xs : Fin n → AName.{u} A)
    (T 𝒟 : AName.{u} A) :
    subsetB (finsetB xs) T ⊓ isDirectedSubsetB 𝒟 ⊓ subsetUnionB T 𝒟 ≤
      ⨆ U, memB U 𝒟 ⊓ subsetB (finsetB xs) U := by
  induction n generalizing T 𝒟 with
  | zero =>
    have hempty (U : AName.{u} A) : subsetB (finsetB xs) U = ⊤ :=
      subsetB_finsetB0 xs U rfl
    have hne : nonemptyB 𝒟 ≤
        ⨆ U, memB U 𝒟 ⊓ subsetB (finsetB xs) U := by
      unfold nonemptyB
      refine iSup_mono fun U => ?_
      rw [hempty, inf_top_eq]
    refine hne.trans' ?_
    unfold isDirectedSubsetB
    exact inf_le_of_left_le (inf_le_of_right_le inf_le_left)
  | succ n ih =>
    have hcons : eqB (finsetB xs)
        (union2B (singletonB (xs 0))
          (finsetB (fun i : Fin n => xs i.succ))) = ⊤ :=
      eqB_finsetB_cons xs
    set head := xs 0
    set rest := fun i : Fin n => xs i.succ
    have hsubT : subsetB (finsetB xs) T =
        memB head T ⊓ subsetB (finsetB rest) T := by
      have h1 : subsetB (finsetB xs) T =
          subsetB (union2B (singletonB head) (finsetB rest)) T :=
        subsetB_eqB_congr_left hcons
      rw [h1, subsetB_union2B, subsetB_singletonB]
    rw [hsubT]
    set G :=
      memB head T ⊓ subsetB (finsetB rest) T ⊓ isDirectedSubsetB 𝒟 ⊓
        subsetUnionB T 𝒟
    have hto_rest : G ≤ subsetB (finsetB rest) T ⊓ isDirectedSubsetB 𝒟 ⊓
        subsetUnionB T 𝒟 :=
      le_inf (le_inf (inf_le_of_left_le (inf_le_of_left_le inf_le_right))
          (inf_le_of_left_le inf_le_right))
        inf_le_right
    have hto_head : G ≤ memB head T ⊓ subsetUnionB T 𝒟 :=
      le_inf (inf_le_of_left_le (inf_le_of_left_le inf_le_left)) inf_le_right
    have hto_dir : G ≤ isDirectedSubsetB 𝒟 :=
      inf_le_of_left_le inf_le_right
    have hrest := (ih rest T 𝒟).trans' hto_rest
    have hhead := (subsetUnionB_apply T 𝒟 head).trans' hto_head
    have hcomb : G ≤
        (⨆ U1, memB U1 𝒟 ⊓ subsetB (finsetB rest) U1) ⊓
          (⨆ U2, memB U2 𝒟 ⊓ memB head U2) ⊓ isDirectedSubsetB 𝒟 :=
      le_inf (le_inf hrest hhead) hto_dir
    refine hcomb.trans ?_
    rw [iSup_inf_iSup_eq]
    rw [iSup_inf_eq]
    refine iSup_le fun U1 => ?_
    rw [iSup_inf_eq]
    refine iSup_le fun U2 => ?_
    have hdir := isDirectedSubsetB_apply 𝒟 U1 U2
    have hto_uv :
        (memB U1 𝒟 ⊓ subsetB (finsetB rest) U1) ⊓
          (memB U2 𝒟 ⊓ memB head U2) ⊓ isDirectedSubsetB 𝒟 ≤
          isDirectedSubsetB 𝒟 ⊓ memB U1 𝒟 ⊓ memB U2 𝒟 :=
      le_inf
        (le_inf inf_le_right (inf_le_of_left_le (inf_le_of_left_le inf_le_left)))
        (inf_le_of_left_le (inf_le_of_right_le inf_le_left))
    have hW := hdir.trans' hto_uv
    have hkeep_rest :
        (memB U1 𝒟 ⊓ subsetB (finsetB rest) U1) ⊓
          (memB U2 𝒟 ⊓ memB head U2) ⊓ isDirectedSubsetB 𝒟 ≤
          subsetB (finsetB rest) U1 :=
      inf_le_of_left_le (inf_le_of_left_le inf_le_right)
    have hkeep_head :
        (memB U1 𝒟 ⊓ subsetB (finsetB rest) U1) ⊓
          (memB U2 𝒟 ⊓ memB head U2) ⊓ isDirectedSubsetB 𝒟 ≤
          memB head U2 :=
      inf_le_of_left_le (inf_le_of_right_le inf_le_right)
    have hjoin :
        (memB U1 𝒟 ⊓ subsetB (finsetB rest) U1) ⊓
          (memB U2 𝒟 ⊓ memB head U2) ⊓ isDirectedSubsetB 𝒟 ≤
          (⨆ W, memB W 𝒟 ⊓ subsetB U1 W ⊓ subsetB U2 W) ⊓
            (subsetB (finsetB rest) U1 ⊓ memB head U2) :=
      le_inf hW (le_inf hkeep_rest hkeep_head)
    refine hjoin.trans ?_
    rw [iSup_inf_eq (f := fun W : AName.{u} A =>
      memB W 𝒟 ⊓ subsetB U1 W ⊓ subsetB U2 W)]
    refine iSup_le fun W => ?_
    have hrestW : subsetB (finsetB rest) U1 ⊓ subsetB U1 W ≤
        subsetB (finsetB rest) W :=
      (subsetB_trans (finsetB rest) U1 W).trans'
        (le_inf inf_le_left inf_le_right)
    have hheadW : memB head U2 ⊓ subsetB U2 W ≤ memB head W :=
      memB_of_subsetB head U2 W
    have hsubW :
        (memB W 𝒟 ⊓ subsetB U1 W ⊓ subsetB U2 W) ⊓
          (subsetB (finsetB rest) U1 ⊓ memB head U2) ≤
        memB W 𝒟 ⊓ subsetB (finsetB xs) W := by
      have hfin : subsetB (union2B (singletonB head) (finsetB rest)) W =
          subsetB (finsetB xs) W := (subsetB_eqB_congr_left hcons).symm
      have hun : subsetB (union2B (singletonB head) (finsetB rest)) W =
          memB head W ⊓ subsetB (finsetB rest) W := by
        rw [subsetB_union2B, subsetB_singletonB]
      refine le_inf (inf_le_of_left_le (inf_le_of_left_le inf_le_left)) ?_
      rw [← hfin, hun]
      refine le_inf ?_ ?_
      · exact hheadW.trans'
          (le_inf (inf_le_of_right_le inf_le_right)
            (inf_le_of_left_le inf_le_right))
      · exact hrestW.trans'
          (le_inf (inf_le_of_right_le inf_le_left)
            (inf_le_of_left_le (inf_le_of_left_le inf_le_right)))
    exact le_iSup_of_le W hsubW

/-- Finite `⊆` implies `≪`. Not `proposition_27`. -/
theorem wayBelowSubsetB_of_finite_subset (S T : AName.{u} A) :
    isFiniteB S ⊓ subsetB S T ≤ wayBelowSubsetB S T := by
  unfold wayBelowSubsetB
  refine le_iInf fun 𝒟 => ?_
  rw [le_himp_iff, le_himp_iff]
  have hre : isFiniteB S ⊓ subsetB S T ⊓ isDirectedSubsetB 𝒟 ⊓
      subsetUnionB T 𝒟 ≤
      isFiniteB S ⊓ (subsetB S T ⊓ isDirectedSubsetB 𝒟 ⊓ subsetUnionB T 𝒟) :=
    le_inf (inf_le_of_left_le (inf_le_of_left_le inf_le_left))
      (le_inf (le_inf
          (inf_le_of_left_le (inf_le_of_left_le inf_le_right))
          (inf_le_of_left_le inf_le_right))
        inf_le_right)
  refine hre.trans ?_
  unfold isFiniteB
  rw [iSup_inf_eq (f := fun n : ℕ =>
    ⨆ xs : Fin n → AName.{u} A, eqB S (finsetB xs))]
  refine iSup_le fun n => ?_
  rw [iSup_inf_eq (f := fun xs : Fin n → AName.{u} A => eqB S (finsetB xs))]
  refine iSup_le fun xs => ?_
  have hto : eqB S (finsetB xs) ⊓ (subsetB S T ⊓ isDirectedSubsetB 𝒟 ⊓
      subsetUnionB T 𝒟) ≤
      eqB S (finsetB xs) ⊓ (subsetB (finsetB xs) T ⊓ isDirectedSubsetB 𝒟 ⊓
        subsetUnionB T 𝒟) := by
    refine le_inf inf_le_left (le_inf (le_inf ?sub ?dir) ?un)
    · exact (subsetB_of_eqB S (finsetB xs) T).trans'
        (le_inf inf_le_left
          (inf_le_of_right_le (inf_le_of_left_le inf_le_left)))
    · exact inf_le_of_right_le (inf_le_of_left_le inf_le_right)
    · exact inf_le_of_right_le inf_le_right
  refine hto.trans ?_
  refine (inf_le_inf_left (eqB S (finsetB xs))
    (finsetB_le_exists_directed xs T 𝒟)).trans ?_
  rw [inf_iSup_eq]
  refine iSup_le fun U => ?_
  refine le_iSup_of_le U ?_
  refine le_inf (inf_le_of_right_le inf_le_left) ?_
  have h := subsetB_of_eqB (finsetB xs) S U
  refine h.trans' ?_
  refine le_inf ?_ (inf_le_of_right_le inf_le_right)
  rw [eqB_comm]
  exact inf_le_left

/-- Internal subset-order `≪` is finite `⊆`. Not `proposition_27`. -/
theorem wayBelowSubsetB_eq_finite_subset (S T : AName.{u} A) :
    wayBelowSubsetB S T = isFiniteB S ⊓ subsetB S T :=
  le_antisymm (wayBelowSubsetB_le_finite_subset S T)
    (wayBelowSubsetB_of_finite_subset S T)

/-!
## Tight union and ⊆-sup in `P^A(X)`

Fat `unionB` sets every child’s membership degree to `⊤`, so it has only
the one-sided law `memB_unionB_of_mem`. The tight union `sUnionB` (Jech
mix of the children by their own values) satisfies
`‖v ∈ ⋃ S‖ = ⨆ u, ‖u ∈ S‖ ⊓ ‖v ∈ u‖`, and is the ⊆-supremum of `S`.
When `S ⊆ P^A(X)`, that sup lies in `P^A(X)`.
-/

/-- Semantic union membership: `∃ u (u ∈ X ∧ v ∈ u)`. -/
noncomputable def existsMemB (v X : AName.{u} A) : A :=
  ⨆ u : AName.{u} A, memB u X ⊓ memB v u

/-- Tight union name: domain is the disjoint union of the children’s
domains, with Boolean values `X(i) ⊓ X.child(i)(j)`. This is `mix` of
the children; it is not fat `unionB`. -/
noncomputable def sUnionB (X : AName.{u} A) : AName.{u} A :=
  mix X.val X.child

theorem existsMemB_eq_iSup_child (X v : AName.{u} A) :
    existsMemB v X = ⨆ i : X.idx, X.val i ⊓ memB v (X.child i) := by
  unfold existsMemB
  refine le_antisymm ?le ?ge
  · refine iSup_le fun u => ?_
    rw [memB_eq (x := u) (y := X), iSup_inf_eq]
    refine iSup_le fun i => ?_
    have h : eqB u (X.child i) ⊓ memB v u ≤ memB v (X.child i) := by
      rw [inf_comm]; exact memB_eqB_right u v (X.child i)
    refine le_iSup_of_le i ?_
    exact le_inf (inf_le_of_left_le inf_le_right)
      (h.trans' (le_inf (inf_le_of_left_le inf_le_left) inf_le_right))
  · refine iSup_le fun i => ?_
    refine le_iSup_of_le (X.child i) ?_
    exact inf_le_inf_right _ (val_le_memB X i)

theorem existsMemB_le_memB_unionB (X v : AName.{u} A) :
    existsMemB v X ≤ memB v (unionB X) := by
  unfold existsMemB
  refine iSup_le fun u => memB_unionB_of_mem X u v

theorem memB_sUnionB (v X : AName.{u} A) :
    memB v (sUnionB X) = existsMemB v X := by
  unfold sUnionB
  rw [memB_eq, existsMemB_eq_iSup_child]
  refine le_antisymm ?le ?ge
  · refine iSup_le fun p => ?_
    rcases p with ⟨i, j⟩
    refine le_iSup_of_le i ?_
    have hmem : eqB v ((X.child i).child j) ⊓ (X.child i).val j ≤
        memB v (X.child i) := by
      rw [memB_eq]
      exact le_iSup_of_le j le_rfl
    refine le_inf (inf_le_of_right_le inf_le_left) ?_
    exact hmem.trans' (le_inf inf_le_left (inf_le_of_right_le inf_le_right))
  · refine iSup_le fun i => ?_
    rw [memB_eq (x := v) (y := X.child i), inf_iSup_eq]
    refine iSup_le fun j => ?_
    refine le_iSup_of_le (⟨i, j⟩ : Σ k : X.idx, (X.child k).idx) ?_
    refine le_inf (inf_le_of_right_le inf_le_left) ?_
    exact le_inf inf_le_left (inf_le_of_right_le inf_le_right)

theorem subsetB_sUnionB_eq_subsetUnionB (e S : AName.{u} A) :
    subsetB e (sUnionB S) = subsetUnionB e S := by
  rw [subsetB_eq_iInf]
  unfold subsetUnionB
  refine iInf_congr fun x => ?_
  rw [memB_sUnionB]
  rfl

theorem isUpperBoundSubsetB_apply (x S y : AName.{u} A) :
    isUpperBoundSubsetB x S ⊓ memB y S ≤ subsetB y x :=
  le_himp_iff.mp (iInf_le (fun y' : AName.{u} A =>
    memB y' S ⇨ subsetB y' x) y)

theorem isUpperBoundSubsetB_sUnionB (S : AName.{u} A) :
    isUpperBoundSubsetB (sUnionB S) S = ⊤ := by
  unfold isUpperBoundSubsetB
  refine iInf_eq_top.mpr fun u => himp_eq_top_iff.mpr ?_
  rw [subsetB_eq_iInf]
  refine le_iInf fun v => ?_
  rw [le_himp_iff, memB_sUnionB]
  exact le_iSup_of_le u le_rfl

theorem subsetB_sUnionB_of_upperBound (S Y : AName.{u} A) :
    isUpperBoundSubsetB Y S ≤ subsetB (sUnionB S) Y := by
  rw [subsetB_eq_iInf]
  refine le_iInf fun v => ?_
  rw [le_himp_iff, memB_sUnionB]
  unfold existsMemB
  rw [inf_iSup_eq]
  refine iSup_le fun u => ?_
  have hsub : isUpperBoundSubsetB Y S ⊓ memB u S ≤ subsetB u Y :=
    isUpperBoundSubsetB_apply Y S u
  have hmem : memB v u ⊓ subsetB u Y ≤ memB v Y :=
    memB_of_subsetB v u Y
  refine hmem.trans' (le_inf ?_ ?_)
  · exact inf_le_of_right_le inf_le_right
  · exact hsub.trans' (le_inf inf_le_left (inf_le_of_right_le inf_le_left))

/-- Tight union is the ⊆-supremum of its members. Fat `unionB` is not
claimed to be least: it can add extra membership. -/
theorem isSupSubsetB_sUnionB (S : AName.{u} A) :
    isSupSubsetB (sUnionB S) S = ⊤ := by
  unfold isSupSubsetB
  rw [isUpperBoundSubsetB_sUnionB, top_inf_eq]
  refine iInf_eq_top.mpr fun Y => himp_eq_top_iff.mpr ?_
  exact subsetB_sUnionB_of_upperBound S Y

theorem subsetB_sUnionB_of_mem_powerB (S X : AName.{u} A) :
    subsetB S (powerB X) ≤ subsetB (sUnionB S) X := by
  rw [subsetB_eq_iInf (sUnionB S) X]
  refine le_iInf fun v => ?_
  rw [le_himp_iff, memB_sUnionB]
  unfold existsMemB
  rw [inf_iSup_eq]
  refine iSup_le fun u => ?_
  refine (memB_of_subsetB v u X).trans' (le_inf ?vu ?sub)
  · exact inf_le_of_right_le inf_le_right
  · have hpow : memB u S ⊓ subsetB S (powerB X) ≤ subsetB u X := by
      rw [← memB_powerB u X]
      exact memB_of_subsetB u S (powerB X)
    exact hpow.trans' (le_inf (inf_le_of_right_le inf_le_left) inf_le_left)

theorem memB_sUnionB_powerB (S X : AName.{u} A) :
    subsetB S (powerB X) ≤ memB (sUnionB S) (powerB X) := by
  rw [memB_powerB]
  exact subsetB_sUnionB_of_mem_powerB S X

/-- `P^A(X)` is a complete lattice under `⊆`: the ⊆-sup of `S ⊆ P^A(X)`
is the tight union `sUnionB S`, which lies in `P^A(X)`. -/
theorem isCompleteLatticeSubsetB_powerB (X : AName.{u} A) :
    isCompleteLatticeSubsetB (powerB X) = ⊤ := by
  unfold isCompleteLatticeSubsetB
  refine iInf_eq_top.mpr fun S => himp_eq_top_iff.mpr ?_
  refine le_iSup_of_le (sUnionB S) ?_
  exact le_inf (memB_sUnionB_powerB S X)
    (le_top.trans (isSupSubsetB_sUnionB S).ge)

/-!
## Continuity of `P^A(X)` at each `d`

`e ≪ d` is finite `⊆` (`wayBelowSubsetB_eq_finite_subset`), so
`{e ∈ P^A(X) | e ≪ d}` agrees with `P_fin^A(d)` once `d ⊆ X`.
Directedness is binary union; joins-down uses `T ⊆ ⋃ P_fin^A(T)` and
that every finite subset of `T` is `⊆ T`.
-/

theorem subsetB_check_empty (T : AName.{u} A) :
    subsetB (check (A := A) (∅ : PSet.{u})) T = ⊤ := by
  rw [subsetB_eq_iInf]
  refine iInf_eq_top.mpr fun z => himp_eq_top_iff.mpr ?_
  rw [memB_check_empty]
  exact bot_le

theorem inWayBelowDownB_powerB (e d X : AName.{u} A) :
    inWayBelowDownB e d (powerB X) =
      memB e (powerB X) ⊓ isFiniteB e ⊓ subsetB e d := by
  unfold inWayBelowDownB
  rw [wayBelowSubsetB_eq_finite_subset]
  ac_rfl

theorem inWayBelowDownB_le_memB_pfinB (e d X : AName.{u} A) :
    inWayBelowDownB e d (powerB X) ≤ memB e (pfinB d) := by
  rw [inWayBelowDownB_powerB, memB_pfinB]
  exact le_inf inf_le_right (inf_le_of_left_le inf_le_right)

theorem memB_pfinB_le_inWayBelowDownB (e d X : AName.{u} A) :
    memB e (pfinB d) ⊓ subsetB d X ≤ inWayBelowDownB e d (powerB X) := by
  rw [inWayBelowDownB_powerB, memB_pfinB, memB_powerB]
  refine le_inf (le_inf ?subX ?fin) ?subd
  · exact (subsetB_trans e d X).trans'
      (le_inf (inf_le_of_left_le inf_le_left) inf_le_right)
  · exact inf_le_of_left_le inf_le_right
  · exact inf_le_of_left_le inf_le_left

theorem nonempty_inWayBelowDownB_powerB (d X : AName.{u} A) :
    (⨆ e : AName.{u} A, inWayBelowDownB e d (powerB X)) = ⊤ := by
  refine top_unique (le_iSup_of_le (check (A := A) (∅ : PSet.{u})) ?_)
  rw [inWayBelowDownB_powerB, memB_powerB, isFiniteB_empty,
    subsetB_check_empty, subsetB_check_empty, inf_top_eq, inf_top_eq]

theorem directedDownB_powerB (d X : AName.{u} A) :
    directedDownB d (powerB X) = ⊤ := by
  unfold directedDownB
  rw [nonempty_inWayBelowDownB_powerB, top_inf_eq]
  refine iInf_eq_top.mpr fun e1 => iInf_eq_top.mpr fun e2 => ?_
  rw [himp_eq_top_iff]
  refine le_iSup_of_le (union2B e1 e2) ?_
  have hle1 : subsetB e1 (union2B e1 e2) = ⊤ := subsetB_union2B_left e1 e2
  have hle2 : subsetB e2 (union2B e1 e2) = ⊤ := subsetB_union2B_right e1 e2
  refine le_inf (le_inf ?in3 (le_top.trans hle1.ge)) (le_top.trans hle2.ge)
  rw [inWayBelowDownB_powerB e1 d X, inWayBelowDownB_powerB e2 d X,
    inWayBelowDownB_powerB (union2B e1 e2) d X, memB_powerB, memB_powerB,
    memB_powerB, subsetB_union2B, subsetB_union2B]
  refine le_inf (le_inf ?subX ?fin) ?subd
  · exact le_inf
      (inf_le_of_left_le (inf_le_of_left_le inf_le_left))
      (inf_le_of_right_le (inf_le_of_left_le inf_le_left))
  · exact (isFiniteB_union2B e1 e2).trans'
      (le_inf (inf_le_of_left_le (inf_le_of_left_le inf_le_right))
        (inf_le_of_right_le (inf_le_of_left_le inf_le_right)))
  · exact le_inf (inf_le_of_left_le inf_le_right)
      (inf_le_of_right_le inf_le_right)

theorem isUpperBoundSubsetB_pfinB (T : AName.{u} A) :
    isUpperBoundSubsetB T (pfinB T) = ⊤ := by
  unfold isUpperBoundSubsetB
  refine iInf_eq_top.mpr fun U => himp_eq_top_iff.mpr ?_
  rw [memB_pfinB]
  exact inf_le_left

theorem subsetB_sUnionB_pfinB (T : AName.{u} A) :
    subsetB (sUnionB (pfinB T)) T = ⊤ :=
  top_unique ((isUpperBoundSubsetB_pfinB T).ge.trans
    (subsetB_sUnionB_of_upperBound (pfinB T) T))

theorem joinsDownB_powerB (d X : AName.{u} A) :
    memB d (powerB X) ≤ joinsDownB d (powerB X) := by
  unfold joinsDownB
  refine le_iInf fun x => le_inf ?fwd ?bwd
  · rw [le_himp_iff]
    refine le_iSup_of_le (singletonB x) ?_
    rw [memB_powerB d X, inWayBelowDownB_powerB (singletonB x) d X,
      memB_powerB (singletonB x) X, subsetB_singletonB x X,
      isFiniteB_singleton x, inf_top_eq, subsetB_singletonB x d,
      memB_singletonB x x, eqB_self, inf_top_eq]
    refine le_inf ?memX inf_le_right
    exact (memB_of_subsetB x d X).trans' (le_inf inf_le_right inf_le_left)
  · rw [le_himp_iff]
    refine inf_le_of_right_le ?_
    refine iSup_le fun e => ?_
    have hsub : inWayBelowDownB e d (powerB X) ≤ subsetB e d := by
      rw [inWayBelowDownB_powerB]
      exact inf_le_right
    exact (memB_of_subsetB x e d).trans' (le_inf inf_le_right
      (hsub.trans' inf_le_left))

theorem isContinuousAtSubsetB_powerB (d X : AName.{u} A) :
    memB d (powerB X) ≤ isContinuousAtSubsetB d (powerB X) := by
  unfold isContinuousAtSubsetB
  exact le_inf (le_top.trans (directedDownB_powerB d X).ge)
    (joinsDownB_powerB d X)

/-- `P^A(X)` is an internal continuous lattice under `⊆`. Not
`proposition_27` / `proposition_28` (those names are the ground `Set X`
statements) and not `corollary_34` (that paper type still needs numerals
as one internal statement; numerals remain `corollary_34_check`). -/
theorem isContinuousLatticeSubsetB_powerB (X : AName.{u} A) :
    isContinuousLatticeSubsetB (powerB X) = ⊤ := by
  unfold isContinuousLatticeSubsetB
  rw [isCompleteLatticeSubsetB_powerB, top_inf_eq]
  refine iInf_eq_top.mpr fun d => himp_eq_top_iff.mpr ?_
  exact isContinuousAtSubsetB_powerB d X

end

end Scott2026
