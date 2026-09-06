/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/

import Scott2026.ExtensionalVA
import Scott2026.InternalDomain

/-!
# Proposition 28

This module joins the syntactic `𝔏_Set` formulas with their semantic Boolean
values and packages all clauses of Proposition 28.  For the checked case we
use `checkExt`, the extensional presentation of `check` whose domain has one
index per extensional set. This is exactly the representation needed by the
paper's pointwise strictness argument.
-/

universe u

namespace Scott2026

open AName SetFormula

variable {A : Type u} [CompleteBooleanAlgebra A]

/-- Extensional equality of parameters is preserved by `P_fin^A`. -/
theorem eqB_pfinB_congr {X Y : AName.{u} A} (h : eqB X Y = ⊤) :
    eqB (pfinB X) (pfinB Y) = ⊤ := by
  rw [eqB_eq_iInf]
  refine iInf_eq_top.mpr fun z => ?_
  have hs : subsetB z X = subsetB z Y := by
    rw [subsetB_eq_iInf, subsetB_eq_iInf]
    exact iInf_congr fun w =>
      congrArg (fun t => memB w z ⇨ t) (eqB_top_memB_right (z := w) h)
  rw [memB_pfinB, memB_pfinB, hs, himp_self, top_inf_eq]

theorem eqB_top_trans {X Y Z : AName.{u} A}
    (hXY : eqB X Y = ⊤) (hYZ : eqB Y Z = ⊤) :
    eqB X Z = ⊤ :=
  top_unique ((eqB_trans X Y Z).trans' (le_inf hXY.ge hYZ.ge))

/-- Extensional version of Proposition 3:
`checkExt(P_fin(Y)) = P_fin^A(checkExt Y)` with Boolean value one. -/
theorem proposition_3_ext (Y : PSet.{u}) [Nontrivial A] :
    eqB (pfinB (checkExt (A := A) Y))
      (checkExt (A := A) (pfin Y)) = ⊤ := by
  have hp :=
    eqB_pfinB_congr (eqB_check_checkExt (A := A) Y)
  have hp' :
      eqB (pfinB (checkExt (A := A) Y))
        (pfinB (check (A := A) Y)) = ⊤ := by
    rw [eqB_comm]
    exact hp
  exact eqB_top_trans (eqB_top_trans hp' (proposition_3 (A := A) Y))
    (eqB_check_checkExt (A := A) (pfin Y))

/-- The checked finite subsets form a base for the power of the extensional
checked presentation. -/
theorem isBaseSubsetB_checkExt_pfin_powerB (Y : PSet.{u}) [Nontrivial A] :
    isBaseSubsetB (checkExt (A := A) (pfin Y))
      (powerB (checkExt (A := A) Y)) = ⊤ := by
  rw [← isBaseSubsetB_eqB_congr_left (proposition_3_ext (A := A) Y)]
  exact isBaseSubsetB_pfinB_powerB (checkExt (A := A) Y)

/-- The checked finite subsets of a paper-facing extensional ZFC set. -/
noncomputable def checkPfinZF (Y : ZFSet.{u}) : AName.{u} A :=
  checkExt (A := A) (pfin Y.out)

/-- Proposition 3 at the extensional ZFC boundary. -/
theorem proposition_3_zf (Y : ZFSet.{u}) [Nontrivial A] :
    eqB (pfinB (checkZF (A := A) Y)) (checkPfinZF (A := A) Y) = ⊤ :=
  proposition_3_ext (A := A) Y.out

/-- Checked finite subsets form a base, stated on Mathlib's extensional ZFC
universe rather than on a chosen pre-set presentation. -/
theorem isBaseSubsetB_checkZF_pfin_powerB (Y : ZFSet.{u}) [Nontrivial A] :
    isBaseSubsetB (checkPfinZF (A := A) Y)
      (powerB (checkZF (A := A) Y)) = ⊤ :=
  isBaseSubsetB_checkExt_pfin_powerB (A := A) Y.out

/-- Proposition 28's continuous-lattice assertion as the Boolean value of its
actual `𝔏_Set` formula. -/
theorem proposition_28_continuous_value (X : AName.{u} A) :
    bval (isContinuousLatticeSubsetF (0 : Fin 1))
      (fun _ => powerB X) = ⊤ := by
  rw [bval_isContinuousLatticeSubsetF]
  exact isContinuousLatticeSubsetB_powerB X

/-- Proposition 28's base assertion as the Boolean value of its actual
`𝔏_Set` formula. -/
theorem proposition_28_base_value (X : AName.{u} A) :
    bval (isBaseSubsetF (0 : Fin 2) (1 : Fin 2))
      (fun i => if i = 0 then pfinB X else powerB X) = ⊤ := by
  rw [bval_isBaseSubsetF]
  change isBaseSubsetB (pfinB X) (powerB X) = ⊤
  exact isBaseSubsetB_pfinB_powerB X

/-- The complete paper statement of Proposition 28 for an `A`-name `X`.
The final implication is the paper's `X = check Y` clause, with the
paper-exact extensional checked presentation. -/
def Proposition28Statement (X : AName.{u} A) : Prop :=
  bval (isContinuousLatticeSubsetF (0 : Fin 1))
      (fun _ => powerB X) = ⊤ ∧
    bval (isBaseSubsetF (0 : Fin 2) (1 : Fin 2))
      (fun i => if i = 0 then pfinB X else powerB X) = ⊤ ∧
    (oid (powerB X)).IsComplete.{u} ∧
    (oid (powerB X)).IsTotal ∧
    ∀ Y : ZFSet.{u}, X = checkZF (A := A) Y →
      isBaseSubsetB (checkPfinZF (A := A) Y) (powerB X) = ⊤ ∧
        (oid (powerB X)).IsStrict

/-- Proposition 28, with all clauses in one theorem. -/
theorem proposition_28 (X : AName.{u} A) [Nontrivial A] :
    Proposition28Statement X := by
  refine ⟨proposition_28_continuous_value X,
    proposition_28_base_value X,
    oid_powerB_isComplete X,
    oid_powerB_isTotal X, ?_⟩
  intro Y hX
  subst X
  exact ⟨isBaseSubsetB_checkZF_pfin_powerB Y,
    oid_powerB_checkExt_isStrict Y.out⟩

end Scott2026
