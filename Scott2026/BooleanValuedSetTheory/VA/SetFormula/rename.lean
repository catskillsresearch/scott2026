/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/

import Mathlib.Data.Multiset.DershowitzManna
import Mathlib.Logic.Pairwise
import Mathlib.Order.CompleteBooleanAlgebra
import Mathlib.Order.Heyting.Basic
import Mathlib.Order.Zorn
import Mathlib.SetTheory.Cardinal.Order
import Mathlib.SetTheory.Ordinal.Family
import Mathlib.SetTheory.ZFC.PSet
import Scott2026.BooleanValuedSetTheory.BooleanLogic
import Scott2026.BooleanValuedSetTheory.VA.SetFormula
import Scott2026.BooleanValuedSetTheory.VA.D0Formula
import Scott2026.BooleanValuedSetTheory.VA.AName
import Scott2026.BooleanValuedSetTheory.VA.AName.child
import Scott2026.BooleanValuedSetTheory.VA.AName.idx
import Scott2026.BooleanValuedSetTheory.VA.AName.meas
import Scott2026.BooleanValuedSetTheory.VA.AName.measLt
import Scott2026.BooleanValuedSetTheory.VA.AName.rank
import Scott2026.BooleanValuedSetTheory.VA.AName.val

universe u

namespace Scott2026

namespace SetFormula

/-- Rename free variables. Under a binder, index `0` stays bound. -/
def rename : ∀ {n m}, (Fin n → Fin m) → SetFormula n → SetFormula m
  | _, _, σ, .mem i j => .mem (σ i) (σ j)
  | _, _, σ, .eq i j => .eq (σ i) (σ j)
  | _, _, σ, .not φ => .not (rename σ φ)
  | _, _, σ, .and φ ψ => .and (rename σ φ) (rename σ ψ)
  | _, _, σ, .ex φ => .ex (rename (Fin.cons 0 (Fin.succ ∘ σ)) φ)
  | _, _, σ, .all φ => .all (rename (Fin.cons 0 (Fin.succ ∘ σ)) φ)


end SetFormula

end Scott2026
