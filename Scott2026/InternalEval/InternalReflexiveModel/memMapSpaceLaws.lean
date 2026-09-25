/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/

import Scott2026.InternalEval.InternalReflexiveModel.validComponents

universe u

namespace Scott2026

open AName

variable {A : Type u} [CompleteBooleanAlgebra A]

namespace InternalReflexiveModel

theorem mem_mapSpace_le_scottContinuous
    (𝓜 : InternalReflexiveModel (A := A)) (F : AName.{u} A) :
    memB F 𝓜.C ≤ isScottContinuousB F 𝓜.D 𝓜.D 𝓜.R 𝓜.R := by
  have hall := (inf_eq_top_iff.mp 𝓜.mapSpace_valid).2
  have hF := iInf_eq_top.mp hall F
  exact himp_eq_top_iff.mp (inf_eq_top_iff.mp hF).1

theorem mem_mapSpace_le_function
    (𝓜 : InternalReflexiveModel (A := A)) (F : AName.{u} A) :
    memB F 𝓜.C ≤ isFunctionB F 𝓜.D 𝓜.D := by
  have hcont := 𝓜.mem_mapSpace_le_scottContinuous F
  unfold isScottContinuousB at hcont
  exact hcont.trans (inf_le_left.trans inf_le_left)

end InternalReflexiveModel

end Scott2026
