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

universe u

namespace Scott2026

open AName
variable {A : Type u} [CompleteBooleanAlgebra A]

noncomputable def engelerLamGraphPred (G x : AName.{u} A) : A :=
  ⨆ K : Finset ℕ, ⨆ n : ℕ, ⨆ Y : AName.{u} A,
    eqB x (pairApplyB (A := A) K n) ⊓
      memB (opairB (check (A := A) (finsetPSet K)) Y) G ⊓
        memB (check (PSet.ofNat n)) Y



end Scott2026
