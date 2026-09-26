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
import Scott2026.BooleanValuedSetTheory.VA.AName.memEq
import Scott2026.BooleanValuedSetTheory.VA.AName.rank
import Scott2026.BooleanValuedSetTheory.VA.AName.val
import Scott2026.BooleanValuedSetTheory.VA.D0Formula.bval
import Scott2026.BooleanValuedSetTheory.VA.D0Formula.consName
import Scott2026.BooleanValuedSetTheory.VA.D0Formula.consPSet
import Scott2026.BooleanValuedSetTheory.VA.D0Formula.realize
import Scott2026.BooleanValuedSetTheory.VA.HomName
import Scott2026.BooleanValuedSetTheory.VA.SetFormula.bval
import Scott2026.BooleanValuedSetTheory.VA.SetFormula.iff
import Scott2026.BooleanValuedSetTheory.VA.SetFormula.implies
import Scott2026.BooleanValuedSetTheory.VA.SetFormula.inst
import Scott2026.BooleanValuedSetTheory.VA.SetFormula.lift
import Scott2026.BooleanValuedSetTheory.VA.SetFormula.or
import Scott2026.BooleanValuedSetTheory.VA.SetFormula.rename
import Scott2026.BooleanValuedSetTheory.VA.canonVal
import Scott2026.BooleanValuedSetTheory.VA.choiceAxiom
import Scott2026.BooleanValuedSetTheory.VA.colRename
import Scott2026.BooleanValuedSetTheory.VA.collectB
import Scott2026.BooleanValuedSetTheory.VA.collectionAxiom
import Scott2026.BooleanValuedSetTheory.VA.compB
import Scott2026.BooleanValuedSetTheory.VA.eqLeibnizAxiom
import Scott2026.BooleanValuedSetTheory.VA.eqLeibnizRenameX
import Scott2026.BooleanValuedSetTheory.VA.eqLeibnizRenameY
import Scott2026.BooleanValuedSetTheory.VA.extensionalityAxiom
import Scott2026.BooleanValuedSetTheory.VA.finsetB
import Scott2026.BooleanValuedSetTheory.VA.funsB
import Scott2026.BooleanValuedSetTheory.VA.homB
import Scott2026.BooleanValuedSetTheory.VA.idB
import Scott2026.BooleanValuedSetTheory.VA.infinityAxiom
import Scott2026.BooleanValuedSetTheory.VA.insertB
import Scott2026.BooleanValuedSetTheory.VA.isFiniteB
import Scott2026.BooleanValuedSetTheory.VA.isFunctionB
import Scott2026.BooleanValuedSetTheory.VA.isInductiveB
import Scott2026.BooleanValuedSetTheory.VA.isOpairF
import Scott2026.BooleanValuedSetTheory.VA.isSingleValuedB
import Scott2026.BooleanValuedSetTheory.VA.isSingletonF
import Scott2026.BooleanValuedSetTheory.VA.isTotalB
import Scott2026.BooleanValuedSetTheory.VA.isUPairF
import Scott2026.BooleanValuedSetTheory.VA.leastIdx
import Scott2026.BooleanValuedSetTheory.VA.nameSetoid
import Scott2026.BooleanValuedSetTheory.VA.opairB
import Scott2026.BooleanValuedSetTheory.VA.opairMemF
import Scott2026.BooleanValuedSetTheory.VA.pOpair
import Scott2026.BooleanValuedSetTheory.VA.pairB
import Scott2026.BooleanValuedSetTheory.VA.pairingAxiom
import Scott2026.BooleanValuedSetTheory.VA.pfin
import Scott2026.BooleanValuedSetTheory.VA.pfinB
import Scott2026.BooleanValuedSetTheory.VA.pfinEnum
import Scott2026.BooleanValuedSetTheory.VA.powerAxiom
import Scott2026.BooleanValuedSetTheory.VA.powerB
import Scott2026.BooleanValuedSetTheory.VA.prodB
import Scott2026.BooleanValuedSetTheory.VA.regularityAxiom
import Scott2026.BooleanValuedSetTheory.VA.restrictName
import Scott2026.BooleanValuedSetTheory.VA.sepB
import Scott2026.BooleanValuedSetTheory.VA.sepRename
import Scott2026.BooleanValuedSetTheory.VA.separationAxiom
import Scott2026.BooleanValuedSetTheory.VA.singletonB
import Scott2026.BooleanValuedSetTheory.VA.succB
import Scott2026.BooleanValuedSetTheory.VA.unionAxiom
import Scott2026.BooleanValuedSetTheory.VA.unionB
import Scott2026.BooleanValuedSetTheory.VA.wellOrderAxiom
import Scott2026.BooleanValuedSetTheory.VA.wellOrderB
import Scott2026.BooleanValuedSetTheory.VA.worDisj
import Scott2026.BooleanValuedSetTheory.VA.worITE
import Scott2026.BooleanValuedSetTheory.VA.worLe
import Scott2026.BooleanValuedSetTheory.VA.worPredSup
import Scott2026.BooleanValuedSetTheory.VA.Proofs.Core
import Scott2026.BooleanValuedSetTheory.VA.Proofs.CoreCont
import Scott2026.BooleanValuedSetTheory.VA.Proofs.CoreContCont
import Scott2026.BooleanValuedSetTheory.VA.Proofs.CoreContContCont

/-!
# The Boolean-valued universe `V^A`

Furber–Mardare–Panangaden–Scott, CSL 2026, §2, and Jech, *Set Theory* (2003),
Chapter 14: names, Boolean values of membership and equality, the substitution
laws (Lemma 14.16), mixing (14.18), fullness (14.19 = CSL Theorem 1(iii)), and
`Δ₀` invariance (14.21 = CSL Theorem 2).

An `A`-name is a well-founded tree of pairs `(child, Boolean value)`, the
standard encoding of Jech’s `V^B` (display (14.15)).
-/

universe u

namespace Scott2026

namespace AName

variable {A : Type u}

end AName

end Scott2026
