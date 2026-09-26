/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/

import Scott2026.LambdaModels.DomainTheory.InternalInterp
import Scott2026.LambdaModels.DomainTheory.InternalReflexiveModel
import Scott2026.LambdaModels.Engeler.LambdaConstVA
import Scott2026.LambdaModels.DomainTheory.ReflexiveVA
import Scott2026.LambdaModels.DomainTheory.InternalEval.prodBIdxEquiv

universe u

namespace Scott2026

open AName
variable {A : Type u} [CompleteBooleanAlgebra A]
variable (M : InternalReflexiveModel (A := A))

noncomputable def prodBIdxOf
    (X Y : AName.{u} A) (i : X.idx) (j : Y.idx) :
    (prodB X Y).idx :=
  (prodBIdxEquiv X Y).symm (i, j)

@[simp] theorem prodBIdxEquiv_idxOf
    (X Y : AName.{u} A) (i : X.idx) (j : Y.idx) :
    prodBIdxEquiv X Y (prodBIdxOf X Y i j) = (i, j) :=
  (prodBIdxEquiv X Y).apply_symm_apply (i, j)

@[simp] theorem prodB_child_eq
    (X Y : AName.{u} A) (p : (prodB X Y).idx) :
    (prodB X Y).child p =
      opairB (X.child ((prodBIdxEquiv X Y p).1))
        (Y.child ((prodBIdxEquiv X Y p).2)) := by
  unfold prodBIdxEquiv prodB
  rfl

@[simp] theorem prodB_child_idxOf
    (X Y : AName.{u} A) (i : X.idx) (j : Y.idx) :
    (prodB X Y).child (prodBIdxOf X Y i j) =
      opairB (X.child i) (Y.child j) := by
  rw [prodB_child_eq, prodBIdxEquiv_idxOf]

@[simp] theorem prodB_val_eq
    (X Y : AName.{u} A) (p : (prodB X Y).idx) :
    (prodB X Y).val p =
      memB (X.child ((prodBIdxEquiv X Y p).1)) X ⊓
        memB (Y.child ((prodBIdxEquiv X Y p).2)) Y := by
  unfold prodBIdxEquiv prodB
  rfl

@[simp] theorem prodB_val_idxOf
    (X Y : AName.{u} A) (i : X.idx) (j : Y.idx) :
    (prodB X Y).val (prodBIdxOf X Y i j) =
      memB (X.child i) X ⊓ memB (Y.child j) Y := by
  rw [prodB_val_eq, prodBIdxEquiv_idxOf]



end Scott2026
