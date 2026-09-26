/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/

import Scott2026.LambdaModels.DomainTheory.InternalEvalComplete
import Scott2026.LambdaModels.DomainTheory.InternalEvalPack.LamDK

universe u

namespace Scott2026

open AName
variable {A : Type u} [CompleteBooleanAlgebra A]
open InternalReflexiveModel
namespace LamDK

def weight {Var Const : Type u} : LamDK Var Const → ℕ
  | .var _ => 1
  | .const _ => 1
  | .abs _ M => weight M + 1
  | .app M N => weight M + weight N + 1


end LamDK

end Scott2026
