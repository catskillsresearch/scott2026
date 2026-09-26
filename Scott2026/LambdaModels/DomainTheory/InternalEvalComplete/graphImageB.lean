/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/

import Scott2026.LambdaModels.DomainTheory.InternalEvalFamily

universe u

namespace Scott2026

open AName
variable {A : Type u} [CompleteBooleanAlgebra A]

noncomputable def graphImageB
    (F S E : AName.{u} A) : AName.{u} A :=
  sepB E (fun y =>
    ⨆ x : AName.{u} A, memB x S ⊓ memB (opairB x y) F)



end Scott2026
