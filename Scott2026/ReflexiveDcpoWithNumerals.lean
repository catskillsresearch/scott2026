/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/

import Scott2026.ReflexiveDcpo

namespace Scott2026

/-- Definition 32: a reflexive dcpo with numerals. We record the algebraic
interface (distinct Booleans, `if`/`succ`/`pred`/`0?`) without a particular
encoding of closed terms as domain elements. -/
structure ReflexiveDcpoWithNumerals (D : Type*) [CompleteLattice D]
    extends ReflexiveDcpo D where
  boolBot : D
  boolTop : D
  numeral : ℕ → D
  bool_ne : boolBot ≠ boolTop
  numeral_inj : Function.Injective numeral

end Scott2026
