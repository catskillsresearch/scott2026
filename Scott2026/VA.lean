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
import Scott2026.VA.SetFormula
import Scott2026.VA.D0Formula
import Scott2026.VA.AName
import Scott2026.VA.AName.child
import Scott2026.VA.AName.idx
import Scott2026.VA.AName.meas
import Scott2026.VA.AName.measLt
import Scott2026.VA.AName.memEq
import Scott2026.VA.AName.rank
import Scott2026.VA.AName.val
import Scott2026.VA.D0Formula.bval
import Scott2026.VA.D0Formula.consName
import Scott2026.VA.D0Formula.consPSet
import Scott2026.VA.D0Formula.realize
import Scott2026.VA.HomName
import Scott2026.VA.SetFormula.bval
import Scott2026.VA.SetFormula.iff
import Scott2026.VA.SetFormula.implies
import Scott2026.VA.SetFormula.inst
import Scott2026.VA.SetFormula.lift
import Scott2026.VA.SetFormula.or
import Scott2026.VA.SetFormula.rename
import Scott2026.VA.canonVal
import Scott2026.VA.choiceAxiom
import Scott2026.VA.colRename
import Scott2026.VA.collectB
import Scott2026.VA.collectionAxiom
import Scott2026.VA.compB
import Scott2026.VA.eqLeibnizAxiom
import Scott2026.VA.eqLeibnizRenameX
import Scott2026.VA.eqLeibnizRenameY
import Scott2026.VA.extensionalityAxiom
import Scott2026.VA.finsetB
import Scott2026.VA.funsB
import Scott2026.VA.homB
import Scott2026.VA.idB
import Scott2026.VA.infinityAxiom
import Scott2026.VA.insertB
import Scott2026.VA.isFiniteB
import Scott2026.VA.isFunctionB
import Scott2026.VA.isInductiveB
import Scott2026.VA.isOpairF
import Scott2026.VA.isSingleValuedB
import Scott2026.VA.isSingletonF
import Scott2026.VA.isTotalB
import Scott2026.VA.isUPairF
import Scott2026.VA.leastIdx
import Scott2026.VA.nameSetoid
import Scott2026.VA.opairB
import Scott2026.VA.opairMemF
import Scott2026.VA.pOpair
import Scott2026.VA.pairB
import Scott2026.VA.pairingAxiom
import Scott2026.VA.pfin
import Scott2026.VA.pfinB
import Scott2026.VA.pfinEnum
import Scott2026.VA.powerAxiom
import Scott2026.VA.powerB
import Scott2026.VA.prodB
import Scott2026.VA.regularityAxiom
import Scott2026.VA.restrictName
import Scott2026.VA.sepB
import Scott2026.VA.sepRename
import Scott2026.VA.separationAxiom
import Scott2026.VA.singletonB
import Scott2026.VA.succB
import Scott2026.VA.unionAxiom
import Scott2026.VA.unionB
import Scott2026.VA.wellOrderAxiom
import Scott2026.VA.wellOrderB
import Scott2026.VA.worDisj
import Scott2026.VA.worITE
import Scott2026.VA.worLe
import Scott2026.VA.worPredSup
import Scott2026.VA.Proofs.Core
import Scott2026.VA.Proofs.CoreCont
import Scott2026.VA.Proofs.CoreContCont
import Scott2026.VA.Proofs.CoreContContCont

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
