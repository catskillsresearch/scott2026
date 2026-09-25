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
import Scott2026.Random.AssociatedAlgebra
import Scott2026.Random.AssociatedAlgebra.Le
import Scott2026.Random.AssociatedAlgebra.bot
import Scott2026.Random.AssociatedAlgebra.compl
import Scott2026.Random.AssociatedAlgebra.inf
import Scott2026.Random.AssociatedAlgebra.mk
import Scott2026.Random.AssociatedAlgebra.sInf
import Scott2026.Random.AssociatedAlgebra.sSup
import Scott2026.Random.AssociatedAlgebra.sup
import Scott2026.Random.AssociatedAlgebra.top
import Scott2026.Random.G_X
import Scott2026.Random.G_X_inv
import Scott2026.Random.G_X_measure
import Scott2026.Random.G_X_measure_inv
import Scott2026.Random.G_pre
import Scott2026.Random.IsAtomic
import Scott2026.Random.IsL0
import Scott2026.Random.L0
import Scott2026.Random.L0.app
import Scott2026.Random.L0.app_measure
import Scott2026.Random.L0.equivPower
import Scott2026.Random.L0.equivPower_measure
import Scott2026.Random.L0.le
import Scott2026.Random.L0.le_measure
import Scott2026.Random.L0.mk
import Scott2026.Random.L0.mk_measure
import Scott2026.Random.L0Fun
import Scott2026.Random.L0Measure
import Scott2026.Random.MeasurableSetoid
import Scott2026.Random.MeasureAlgebra
import Scott2026.Random.MeasureAlgebra.Le
import Scott2026.Random.MeasureAlgebra.bot
import Scott2026.Random.MeasureAlgebra.compl
import Scott2026.Random.MeasureAlgebra.inf
import Scott2026.Random.MeasureAlgebra.mk
import Scott2026.Random.MeasureAlgebra.sInf
import Scott2026.Random.MeasureAlgebra.sSup
import Scott2026.Random.MeasureAlgebra.sup
import Scott2026.Random.MeasureAlgebra.toAssociated
import Scott2026.Random.MeasureAlgebra.top
import Scott2026.Random.MeasureAlgebra.instances
import Scott2026.Random.MeasureAlgebra.himpMk
import Scott2026.Random.MeasureAlgebra.supMk
import Scott2026.Random.MeasureAlgebra.iInfMkFinset
import Scott2026.Random.MeasureAlgebra.iffMk
import Scott2026.Random.NegligibilitySpace.measRep
import Scott2026.Random.NegligibilitySpace.ofMeasure
import Scott2026.Random.aeEq
import Scott2026.Random.aeSetoid
import Scott2026.Random.atomlessSeq
import Scott2026.Random.atomlessSeqAux
import Scott2026.Random.constRV
import Scott2026.Random.engelerAppA
import Scott2026.Random.l0AE
import Scott2026.Random.l0AE_measure
import Scott2026.Random.l0APoset
import Scott2026.Random.l0App
import Scott2026.Random.l0Eq
import Scott2026.Random.l0Le
import Scott2026.Random.l0Poset
import Scott2026.Random.l0Poset_measure
import Scott2026.Random.l0Setoid
import Scott2026.Random.l0Setoid_measure
import Scott2026.Random.meetlessSeq
import Scott2026.Random.posBasic
import Scott2026.Random.proposition_39
import Scott2026.Random.proposition_39_measure
import Scott2026.Random.paperRV
import Scott2026.Random.Proofs.Core
import Scott2026.Random.Proofs.CoreCont
import Scott2026.Random.Proofs.CoreContCont

/-!
# Domain-valued random variables (Definitions 37–41, Propositions 39–40)

`ℒ⁰(X; 𝒫(Y))` is the set of measurable maps `X → Set Y`. Quotienting by a
σ-ideal of negligible sets yields an `A(X)`-poset (Lemma 38). `G_X` is the
strict `A(X)`-poset isomorphism of Proposition 39; application is the
homomorphism of Proposition 40.
-/

open MeasureTheory Set
open scoped ENNReal

namespace Scott2026

variable {X Y : Type*} [MeasurableSpace X]

end Scott2026
