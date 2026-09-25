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
import Scott2026.InternalEval.prodBIdxOf

universe u

namespace Scott2026

open AName

variable {A : Type u} [CompleteBooleanAlgebra A]

theorem oid_prodB_eq
    (X Y : AName.{u} A) (p q : (prodB X Y).idx) :
    (oid (prodB X Y)).eq p q =
      ((oid X).prod (oid Y)).eq
        (prodBIdxEquiv X Y p) (prodBIdxEquiv X Y q) := by
  rw [oid_eq, ASetoid.prod_eq, oid_eq, oid_eq,
    prodB_child_eq, prodB_child_eq,
    memB_opairB_prodB, memB_opairB_prodB, eqB_opairB]
  ac_rfl

theorem oid_prodB_eps
    (X Y : AName.{u} A) (p : (prodB X Y).idx) :
    (oid (prodB X Y)).eps p =
      ((oid X).prod (oid Y)).eps (prodBIdxEquiv X Y p) := by
  rw [ASetoid.eps, ASetoid.eps, oid_prodB_eq]

end Scott2026
