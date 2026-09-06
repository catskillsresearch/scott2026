/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/

import Scott2026.InterpConstVA
import Scott2026.OidEssential
import Scott2026.ReflexiveVA

/-!
# Theorem 26: internal interpretation boundary

This module isolates the final categorical step in the paper's proof. The
remaining mathematical obligation is the internal Definition 25 recursion
that constructs the two function names; once those names are available,
Definition 16 and completeness give the required `SetoidF_A` morphisms.
-/

universe u

namespace Scott2026

open AName

variable {A : Type u} [CompleteBooleanAlgebra A]

/-- A partial valuation from the variable name `V` to the domain `D`, with
domain of definition `Dom`. -/
noncomputable def isValuationB
    (V D Dom Rho : AName.{u} A) : A :=
  subsetB Dom V ⊓ isFunctionB Rho Dom D

/-- Turn an internal function-name witness into its `SetoidF_A` map. This is
Definition 16 followed by Definition 13, exactly as in the proof of
Theorem 26. -/
noncomputable def functionNameToSetoidFHom
    (X D I : AName.{u} A)
    (hI : isFunctionB I X D = ⊤)
    (hD : (oid D).IsComplete.{u}) :
    SetoidFHom (oid X) (oid D) :=
  SetoidFHom.ofRelFun hD (oidRel X D I hI)

/-- Full constant-bearing interpretation, conditional only on the internal
recursion's function-name witness. -/
noncomputable def theorem26FullOfFunctionName
    (D V K I : AName.{u} A)
    (hI : isFunctionB I (lamDKB D V K) D = ⊤)
    (hD : (oid D).IsComplete.{u}) :
    SetoidFHom (oid (lamDKB D V K)) (oid D) :=
  functionNameToSetoidFHom (lamDKB D V K) D I hI hD

/-- Pure interpretation, conditional only on its internal function-name
witness. -/
noncomputable def theorem26PureOfFunctionName
    (D V I : AName.{u} A)
    (hI : isFunctionB I (lamB V) D = ⊤)
    (hD : (oid D).IsComplete.{u}) :
    SetoidFHom (oid (lamB V)) (oid D) :=
  functionNameToSetoidFHom (lamB V) D I hI hD

/-- Evaluation of the resulting functional representative has exactly the
same Boolean graph as the original internal interpretation name. -/
theorem theorem26FullOfFunctionName_gamma
    (D V K I : AName.{u} A)
    (hI : isFunctionB I (lamDKB D V K) D = ⊤)
    (hD : (oid D).IsComplete.{u})
    (M : (lamDKB D V K).idx) (d : D.idx) :
    gamma (oid (lamDKB D V K)) (oid D)
      (functionalOfRel hD
        (oidRel (lamDKB D V K) D I hI)) M d =
      memB (opairB ((lamDKB D V K).child M) (D.child d)) I := by
  rw [functionalOfRel_gamma]
  rfl

/-- Pure counterpart of `theorem26FullOfFunctionName_gamma`. -/
theorem theorem26PureOfFunctionName_gamma
    (D V I : AName.{u} A)
    (hI : isFunctionB I (lamB V) D = ⊤)
    (hD : (oid D).IsComplete.{u})
    (M : (lamB V).idx) (d : D.idx) :
    gamma (oid (lamB V)) (oid D)
      (functionalOfRel hD (oidRel (lamB V) D I hI)) M d =
      memB (opairB ((lamB V).child M) (D.child d)) I := by
  rw [functionalOfRel_gamma]
  rfl

end Scott2026
