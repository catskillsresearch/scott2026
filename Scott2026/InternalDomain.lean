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
half is `corollary_34_check`. The continuous-lattice half is blocked by the
internal Proposition 27 equivalence (finite ⊆ ↔ way-below), of which this
file proves the language, `≪ → ⊆`, directedness of `P_fin^A`, and
`T ⊆ ⋃ P_fin^A(T)`. The missing lemma is `isFiniteB_of_subset`
(a ⊆-subset of a finite name is finite), needed to finish
`wayBelowSubsetB S T ≤ isFiniteB S ⊓ subsetB S T`.
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
Not `proposition_27`: that paper name needs the further lemma
`isFiniteB_of_subset` (`S ⊆ U` and `U` finite imply `S` finite). -/
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

end

end Scott2026
