/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/

import Scott2026.InternalInterp
import Scott2026.InternalReflexiveModel
import Scott2026.LambdaConstVA
import Scott2026.ReflexiveVA

universe u

namespace Scott2026

open AName

variable {A : Type u} [CompleteBooleanAlgebra A]

namespace InternalReflexiveModel

variable (M : InternalReflexiveModel (A := A))

theorem valid_components :
    isDcpoWithBottomB M.D M.R = ⊤ ∧
      isContinuousMapSpaceB M.C M.D M.R = ⊤ ∧
      isPointwiseOrderB M.Q M.C M.D M.R = ⊤ ∧
      isScottContinuousB M.Fun M.D M.C M.R M.Q = ⊤ ∧
      isScottContinuousB M.Lam M.C M.D M.Q M.R = ⊤ ∧
      eqB (compB M.Fun M.Lam M.C M.C) (idB M.C) = ⊤ := by
  have hv := M.valid
  unfold isReflexiveDcpoB at hv
  have h₅ := inf_eq_top_iff.mp hv
  have h₄ := inf_eq_top_iff.mp h₅.1
  have h₃ := inf_eq_top_iff.mp h₄.1
  have h₂ := inf_eq_top_iff.mp h₃.1
  have h₁ := inf_eq_top_iff.mp h₂.1
  exact ⟨h₁.1, h₁.2, h₂.2, h₃.2, h₄.2, h₅.2⟩

theorem mapSpace_valid : isContinuousMapSpaceB M.C M.D M.R = ⊤ :=
  M.valid_components.2.1

theorem fun_continuous :
    isScottContinuousB M.Fun M.D M.C M.R M.Q = ⊤ :=
  M.valid_components.2.2.2.1

theorem function_of_scottContinuous {F X Y P Q : AName.{u} A}
    (h : isScottContinuousB F X Y P Q = ⊤) :
    isFunctionB F X Y = ⊤ := by
  unfold isScottContinuousB at h
  exact (inf_eq_top_iff.mp (inf_eq_top_iff.mp h).1).1

theorem fun_function : isFunctionB M.Fun M.D M.C = ⊤ :=
  function_of_scottContinuous M.fun_continuous

end InternalReflexiveModel

end Scott2026
