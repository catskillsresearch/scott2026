/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/

import Scott2026.InternalInterp
import Scott2026.ReflexiveVA

namespace Scott2026

variable {A : Type u} [CompleteBooleanAlgebra A]

/-- The internal reflexive-dcpo data and the external setoid hypotheses of
Theorem 26. -/
structure InternalReflexiveModel where
  D : AName.{u} A
  R : AName.{u} A
  C : AName.{u} A
  Q : AName.{u} A
  Fun : AName.{u} A
  Lam : AName.{u} A
  valid : isReflexiveDcpoB D R C Q Fun Lam = ⊤
  strict : (oid D).IsStrict
  total : (oid D).IsTotal
  complete : (oid D).IsComplete.{u}

end Scott2026
