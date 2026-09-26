/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/

import Scott2026.LambdaModels.DomainTheory.InternalInterp
import Scott2026.LambdaModels.DomainTheory.InternalReflexiveModel
import Scott2026.LambdaModels.Engeler.LambdaConstVA
import Scott2026.LambdaModels.DomainTheory.ReflexiveVA

universe u

namespace Scott2026

open AName

variable {A : Type u} [CompleteBooleanAlgebra A]

theorem inf_memB_opairB_le_iSup_child {a : A} {F X Y : AName.{u} A}
    (hsub : a ≤ subsetB F (prodB X Y)) (x y : AName.{u} A) :
    a ⊓ memB (opairB x y) F ≤
      ⨆ j : Y.idx, memB (opairB x (Y.child j)) F := by
  have hmem : a ⊓ memB (opairB x y) F ≤ memB y Y := by
    have h := (memB_of_subsetB (opairB x y) F (prodB X Y)).trans' <|
      le_inf inf_le_right (inf_le_left.trans hsub)
    rw [memB_opairB_prodB] at h
    exact h.trans inf_le_right
  refine (le_inf le_rfl hmem).trans ?_
  rw [memB_eq (x := y) (y := Y), inf_iSup_eq]
  refine iSup_le fun j => le_iSup_of_le j ?_
  refine (memB_opairB_congr F x x y (Y.child j)).trans' ?_
  refine le_inf (le_inf ?_ (inf_le_right.trans inf_le_left)) ?_
  · exact le_top.trans (eqB_self (A := A) x).ge
  · exact inf_le_left.trans inf_le_right

end Scott2026
