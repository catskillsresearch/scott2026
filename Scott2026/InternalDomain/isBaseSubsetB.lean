/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/

import Scott2026.VA
import Scott2026.InternalDomain.wayBelowSubsetB

universe u

namespace Scott2026

open AName
open SetFormula
open D0Formula (consName consName_zero consName_succ)
open Classical
variable {A : Type u} [CompleteBooleanAlgebra A]

/-- `B` is a base for `D` under `⊆`. -/
noncomputable def isBaseSubsetB (B D : AName.{u} A) : A :=
  subsetB B D ⊓
    ⨅ d : AName.{u} A, memB d D ⇨
      ((⨆ e : AName.{u} A, memB e B ⊓ wayBelowSubsetB e d) ⊓
        ⨅ e1 : AName.{u} A, ⨅ e2 : AName.{u} A,
          memB e1 B ⊓ wayBelowSubsetB e1 d ⊓
            (memB e2 B ⊓ wayBelowSubsetB e2 d) ⇨
            ⨆ e3 : AName.{u} A,
              memB e3 B ⊓ wayBelowSubsetB e3 d ⊓
                subsetB e1 e3 ⊓ subsetB e2 e3) ⊓
        ⨅ x : AName.{u} A,
          (memB x d ⇨
            ⨆ e : AName.{u} A, memB e B ⊓ wayBelowSubsetB e d ⊓ memB x e) ⊓
            ((⨆ e : AName.{u} A, memB e B ⊓ wayBelowSubsetB e d ⊓ memB x e) ⇨
              memB x d)



end Scott2026
