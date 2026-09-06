/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/

import Scott2026.ExtensionalVA

/-!
# Regression test for raw presentation indices

Isolated counterexample: a pre-set that lists `∅` twice admits two different
valuations on `dom(P^A(check Y))` that are Boolean-equal at `⊤`. This is not a
paper counterexample: `PSet` presentations are implementation details, while
the paper works with extensional ZFC sets. It records why public checked-set
theorems use `checkZF`/`checkExt` rather than raw `check`.
-/

namespace Scott2026

open AName

/-- A pre-set presenting `∅` twice. -/
def psetDupEmpty : PSet.{0} :=
  PSet.mk (ULift Bool) (fun _ => PSet.empty)

/-- Valuation `⊤` on the first copy of `∅` and `⊥` on the second. -/
noncomputable def rawPowerTrueFalse :
    (powerB (check (A := Prop) psetDupEmpty)).idx :=
  ⟨fun i => if i.down then ⊤ else ⊥, fun _ => le_top⟩

/-- Valuation `⊥` on the first copy of `∅` and `⊤` on the second. -/
noncomputable def rawPowerFalseTrue :
    (powerB (check (A := Prop) psetDupEmpty)).idx :=
  ⟨fun i => if i.down then ⊥ else ⊤, fun _ => le_top⟩

theorem rawPowerTrueFalse_ne :
    rawPowerTrueFalse ≠ rawPowerFalseTrue := by
  intro h
  have := congrFun (congrArg Subtype.val h) ⟨true⟩
  simp [rawPowerTrueFalse, rawPowerFalseTrue] at this

theorem check_psetDupEmpty_child
    (i : (check (A := Prop) psetDupEmpty).idx) :
    (check (A := Prop) psetDupEmpty).child i =
      check (A := Prop) PSet.empty :=
  rfl

theorem memB_child_raw_dup
    (v : (powerB (check (A := Prop) psetDupEmpty)).idx)
    (i : (check (A := Prop) psetDupEmpty).idx) :
    memB ((check (A := Prop) psetDupEmpty).child i)
      ((powerB (check (A := Prop) psetDupEmpty)).child v) =
      ⨆ j, v.1 j := by
  change memB ((check (A := Prop) psetDupEmpty).child i)
      (mk (check (A := Prop) psetDupEmpty).idx
        (check (A := Prop) psetDupEmpty).child v.1) =
    ⨆ j, v.1 j
  rw [memB_mk]
  refine iSup_congr fun j => ?_
  rw [check_psetDupEmpty_child, check_psetDupEmpty_child, eqB_self, top_inf_eq]

theorem memB_child_raw_dup_top
    {v : (powerB (check (A := Prop) psetDupEmpty)).idx}
    (hv : v.1 ⟨true⟩ ⊔ v.1 ⟨false⟩ = ⊤)
    (i : (check (A := Prop) psetDupEmpty).idx) :
    memB ((check (A := Prop) psetDupEmpty).child i)
      ((powerB (check (A := Prop) psetDupEmpty)).child v) = ⊤ := by
  rw [memB_child_raw_dup]
  refine top_unique ?_
  rw [← hv]
  exact sup_le (le_iSup (fun j => v.1 j) ⟨true⟩) (le_iSup (fun j => v.1 j) ⟨false⟩)

theorem subsetB_raw_dup
    (v w : (powerB (check (A := Prop) psetDupEmpty)).idx)
    (hw : w.1 ⟨true⟩ ⊔ w.1 ⟨false⟩ = ⊤) :
    subsetB ((powerB (check (A := Prop) psetDupEmpty)).child v)
      ((powerB (check (A := Prop) psetDupEmpty)).child w) = ⊤ := by
  change subsetB
      (mk (check (A := Prop) psetDupEmpty).idx
        (check (A := Prop) psetDupEmpty).child v.1)
      ((powerB (check (A := Prop) psetDupEmpty)).child w) = ⊤
  rw [subsetB_mk]
  refine iInf_eq_top.mpr fun i => himp_eq_top_iff.mpr ?_
  rw [memB_child_raw_dup_top hw]
  exact le_top

theorem eqB_raw_dup :
    eqB ((powerB (check (A := Prop) psetDupEmpty)).child rawPowerTrueFalse)
      ((powerB (check (A := Prop) psetDupEmpty)).child rawPowerFalseTrue) = ⊤ := by
  have h₁ : rawPowerTrueFalse.1 ⟨true⟩ ⊔ rawPowerTrueFalse.1 ⟨false⟩ = ⊤ := by
    simp [rawPowerTrueFalse]
  have h₂ : rawPowerFalseTrue.1 ⟨true⟩ ⊔ rawPowerFalseTrue.1 ⟨false⟩ = ⊤ := by
    simp [rawPowerFalseTrue]
  rw [eqB_eq_subset, subsetB_raw_dup rawPowerTrueFalse rawPowerFalseTrue h₂,
    subsetB_raw_dup rawPowerFalseTrue rawPowerTrueFalse h₁, inf_top_eq]

/-- Raw index-level strictness fails: duplicate children of a `PSet` give two
    distinct valuations that are Boolean-equal at `⊤`. -/
theorem oid_powerB_not_strict :
    ¬ (oid (powerB (check (A := Prop) psetDupEmpty))).IsStrict := by
  intro hstrict
  exact rawPowerTrueFalse_ne
    (hstrict rawPowerTrueFalse rawPowerFalseTrue (by
      rw [oid_eq_powerB]
      exact eqB_raw_dup))

/-- The extensional checked presentation removes precisely the duplicate-key
artifact exercised by this regression test. -/
theorem oid_powerB_checkExt_psetDupEmpty_strict :
    (oid (powerB (checkExt (A := Prop) psetDupEmpty))).IsStrict :=
  oid_powerB_checkExt_isStrict psetDupEmpty

end Scott2026
