/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/

import Scott2026.LambdaModels.DomainTheory.InternalInterp
import Scott2026.LambdaModels.DomainTheory.InternalReflexiveModel
import Scott2026.LambdaModels.Engeler.LambdaConstVA
import Scott2026.LambdaModels.DomainTheory.ReflexiveVA
import Scott2026.LambdaModels.DomainTheory.InternalEval.IsRelElementAt

universe u

namespace Scott2026

open AName
variable {A : Type u} [CompleteBooleanAlgebra A]
variable (M : InternalReflexiveModel (A := A))

noncomputable def relFunOfIsRelElementAt
    {D : AName.{u} A} {a : A} {r : D.idx → A}
    (h : IsRelElementAt D a r) :
    RelFun (extentSetoid a) (oid D) where
  val _ d := r d
  respects := by
    intro _ _ d e
    refine le_inf ?_ ?_ <;> rw [le_himp_iff]
    · exact h.1 d e |>.trans' <|
        le_inf (inf_le_left.trans inf_le_right) inf_le_right
    · have hde := h.1 e d
      rw [(oid D).symm e d] at hde
      exact hde.trans' <|
        le_inf (inf_le_left.trans inf_le_right) inf_le_right
  le_eps := fun _ d => h.2.1 d
  single_valued := fun _ d e => h.2.2.1 d e
  total := fun _ => h.2.2.2

@[simp] theorem relFunOfIsRelElementAt_val
    {D : AName.{u} A} {a : A} {r : D.idx → A}
    (h : IsRelElementAt D a r) (i : PUnit) (d : D.idx) :
    (relFunOfIsRelElementAt h).val i d = r d :=
  rfl



end Scott2026
