/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/

import Scott2026.VA

namespace Scott2026

variable {A : Type u} [CompleteBooleanAlgebra A]

/-- Bundled objects of `Set_A`. -/
structure SetAObj (A : Type u) [CompleteBooleanAlgebra A] where
  name : AName.{u} A

end Scott2026
