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
import Scott2026.BooleanLogic
import Scott2026.VA.AName

namespace Scott2026

inductive SetFormula : ℕ → Type
  | mem {n} (i j : Fin n) : SetFormula n
  | eq {n} (i j : Fin n) : SetFormula n
  | not {n} : SetFormula n → SetFormula n
  | and {n} : SetFormula n → SetFormula n → SetFormula n
  | ex {n} : SetFormula (n + 1) → SetFormula n
  | all {n} : SetFormula (n + 1) → SetFormula n


end Scott2026
