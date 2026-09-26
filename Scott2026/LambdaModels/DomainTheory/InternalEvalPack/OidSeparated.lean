/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/

import Scott2026.LambdaModels.DomainTheory.InternalEvalComplete

universe u

namespace Scott2026

open AName
variable {A : Type u} [CompleteBooleanAlgebra A]
open InternalReflexiveModel

def OidSeparated (V : AName.{u} A) : Prop :=
  ∀ i j : V.idx, i ≠ j → (oid V).eq i j = ⊥



end Scott2026
