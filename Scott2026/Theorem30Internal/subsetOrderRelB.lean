/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/

import Scott2026.EngelerVA
import Scott2026.ReflexiveVA
import Scott2026.ExtensionalVA
import Scott2026.InternalDomain
import Scott2026.InternalEvalComplete
import Scott2026.Theorem30Internal.subsetPairPred

universe u

namespace Scott2026

open AName
variable {A : Type u} [CompleteBooleanAlgebra A]

noncomputable def subsetOrderRelB (D : AName.{u} A) : AName.{u} A :=
  sepB (prodB D D) subsetPairPred



end Scott2026
