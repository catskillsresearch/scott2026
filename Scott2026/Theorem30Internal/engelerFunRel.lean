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
import Scott2026.Theorem30Internal.engelerD
import Scott2026.Theorem30Internal.engelerC
import Scott2026.Theorem30Internal.engelerFunIdx
import Scott2026.Theorem30Internal.Proofs.FunIdx

universe u

namespace Scott2026

open AName
variable {A : Type u} [CompleteBooleanAlgebra A]

noncomputable def engelerFunRel [Nontrivial A] :
    RelFun (oid (engelerD (A := A))) (oid (engelerC (A := A))) :=
  RelFun.ofFunctional _ _ (engelerFunIdx (A := A))
    (engelerFunIdx_functional (A := A))

end Scott2026
