/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/

import Scott2026.InternalInterp
import Scott2026.InternalReflexiveModel
import Scott2026.LambdaConstVA
import Scott2026.ReflexiveVA
import Scott2026.InternalEval.prodBIdxEquiv
import Scott2026.InternalEval.oidProdBLaws

universe u

namespace Scott2026

open AName
variable {A : Type u} [CompleteBooleanAlgebra A]
variable (M : InternalReflexiveModel (A := A))

noncomputable def relFunOnProdB
    (X Y Z : AName.{u} A)
    (f : RelFun ((oid X).prod (oid Y)) (oid Z)) :
    RelFun (oid (prodB X Y)) (oid Z) where
  val p z := f.val (prodBIdxEquiv X Y p) z
  respects := by
    intro p q z w
    rw [oid_prodB_eq]
    exact f.respects _ _ z w
  le_eps := by
    intro p z
    rw [oid_prodB_eps]
    exact f.le_eps _ z
  single_valued := by
    intro p z w
    exact f.single_valued _ z w
  total := by
    intro p
    rw [oid_prodB_eps]
    exact f.total _

@[simp] theorem relFunOnProdB_val
    (X Y Z : AName.{u} A)
    (f : RelFun ((oid X).prod (oid Y)) (oid Z))
    (p : (prodB X Y).idx) (z : Z.idx) :
    (relFunOnProdB X Y Z f).val p z =
      f.val (prodBIdxEquiv X Y p) z :=
  rfl



end Scott2026
