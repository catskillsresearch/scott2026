/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/

import Mathlib.MeasureTheory.MeasurableSpace.Basic
import Mathlib.MeasureTheory.Measure.Basic
import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
import Mathlib.Order.Atoms
import Mathlib.Basic.Countable.Defs
import Mathlib.Basic.Countable.Small
import Mathlib.Logic.Encodable.Basic
import Mathlib.Order.CompleteLattice.Finset
import Mathlib.Order.Hom.Basic
import Scott2026.NegligibilitySpace
import Scott2026.Setoid
import Scott2026.PowerSet
import Scott2026.Engeler
import Scott2026.Random.L0
import Scott2026.Random.L0.mk
import Scott2026.Random.L0.le
import Scott2026.Random.L0.app
import Scott2026.Random.L0.mk_measure
import Scott2026.Random.L0Measure
import Scott2026.Random.l0App
import Scott2026.Random.l0AppLaws
import Scott2026.Random.l0AppAeMeasure

namespace Scott2026

open MeasureTheory Set

variable {X : Type*} [MeasurableSpace X] {E : Type*}
namespace L0

noncomputable def L0.app_measure [DecidableEq E] [Countable E] (μ : MeasureTheory.Measure X)
    (pair : Finset E × E → E) (a b : _root_.Scott2026.L0Measure μ E) : _root_.Scott2026.L0Measure μ E :=
  Quotient.lift₂
    (fun a b => L0.mk_measure μ
      ⟨l0App pair a.val b.val, l0App_isL0 pair a.property b.property⟩)
    (fun a b a' b' ha hb => by
      refine Quotient.sound ?_
      exact l0App_ae_measure μ pair ha hb) a b

theorem L0.app_measure_mk [DecidableEq E] [Countable E] (μ : Measure X)
    (pair : Finset E × E → E) (a b : L0Fun X E) :
    L0.app_measure μ pair (L0.L0.mk_measure μ a) (L0.L0.mk_measure μ b) =
      L0.L0.mk_measure μ ⟨l0App pair a.val b.val,
        l0App_isL0 pair a.property b.property⟩ :=
  rfl

end L0

end Scott2026
