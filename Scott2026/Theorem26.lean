/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/

import Scott2026.InterpConstVA
import Scott2026.InternalEvalPack
import Scott2026.OidEssential

/-!
# Theorem 26: internal interpretation

The Definition 25 evaluator name is assembled in `InternalEvalPack` and
shown to be an internal function `lamDKB D V K → D`. The four clauses
are `interpDKGraph_var/const/app/abs` (and their `_val` unfoldings) at
the term’s `lamDKVal` extent. Definition 16 and completeness give the
`SetoidF_A` morphisms `theorem26Full` / `theorem26Pure`. Checked
pure-term soundness is `theorem26Pure_sound`: `LamEq M N` implies
Boolean equality of the internal interpretations, using the substitution
lemma, the retract `Fun ∘ Lam = id` on `C`, and `OidSeparated` for
crisp variables. Engeler `theorem_26` / `theorem_26_sound_full` remain
the weaker carrier packaging and are not renamed.
-/

universe u

namespace Scott2026

open AName

variable {A : Type u} [CompleteBooleanAlgebra A]

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

/-- Exact internal Theorem 26, full constant-bearing fragment. -/
noncomputable def theorem26Full
    (𝓜 : InternalReflexiveModel (A := A))
    (V K : AName.{u} A) (hK : subsetB K 𝓜.D = ⊤)
    (hV : (oid V).IsTotal)
    (η : RelFun (oid V) (oid 𝓜.D)) :
    SetoidFHom (oid (lamDKB 𝓜.D V K)) (oid 𝓜.D) :=
  theorem26FullOfFunctionName 𝓜.D V K
    (InternalReflexiveModel.interpDKGraph 𝓜 V K hK hV η)
    (InternalReflexiveModel.interpDKGraph_isFunctionB 𝓜 V K hK hV η)
    𝓜.complete

/-- Paper-facing entry: any valid internal valuation totalizes to a
`SetoidF_A` interpretation of `lamDKB`. -/
noncomputable def theorem26Full_of_valuation
    (𝓜 : InternalReflexiveModel (A := A))
    (V K : AName.{u} A) (hK : subsetB K 𝓜.D = ⊤)
    (hV : (oid V).IsTotal)
    (Dom Rho : AName.{u} A)
    (hVal : isValuationB V 𝓜.D Dom Rho = ⊤) :
    SetoidFHom (oid (lamDKB 𝓜.D V K)) (oid 𝓜.D) :=
  theorem26Full 𝓜 V K hK hV
    (totalizedValuationRelOfValid V 𝓜.D Dom Rho hVal
      𝓜.total 𝓜.complete)

/-- Exact internal Theorem 26, pure-term fragment. -/
noncomputable def theorem26Pure
    (𝓜 : InternalReflexiveModel (A := A))
    (V K : AName.{u} A) (hK : subsetB K 𝓜.D = ⊤)
    (hV : (oid V).IsTotal)
    (η : RelFun (oid V) (oid 𝓜.D)) :
    SetoidFHom (oid (lamB V)) (oid 𝓜.D) :=
  theorem26PureOfFunctionName 𝓜.D V
    (InternalReflexiveModel.interpDKPureGraph 𝓜 V K hK hV η)
    (InternalReflexiveModel.interpDKPureGraph_isFunctionB 𝓜 V K hK hV η)
    𝓜.complete

/-- Paper-facing pure entry from a valid internal valuation. -/
noncomputable def theorem26Pure_of_valuation
    (𝓜 : InternalReflexiveModel (A := A))
    (V K : AName.{u} A) (hK : subsetB K 𝓜.D = ⊤)
    (hV : (oid V).IsTotal)
    (Dom Rho : AName.{u} A)
    (hVal : isValuationB V 𝓜.D Dom Rho = ⊤) :
    SetoidFHom (oid (lamB V)) (oid 𝓜.D) :=
  theorem26Pure 𝓜 V K hK hV
    (totalizedValuationRelOfValid V 𝓜.D Dom Rho hVal
      𝓜.total 𝓜.complete)

/-- `SetoidF_A` evaluation of `theorem26Full` recovers the evaluator graph. -/
theorem theorem26Full_gamma
    (𝓜 : InternalReflexiveModel (A := A))
    (V K : AName.{u} A) (hK : subsetB K 𝓜.D = ⊤)
    (hV : (oid V).IsTotal)
    (η : RelFun (oid V) (oid 𝓜.D))
    (M : (lamDKB 𝓜.D V K).idx) (d : 𝓜.D.idx) :
    gamma (oid (lamDKB 𝓜.D V K)) (oid 𝓜.D)
      (functionalOfRel 𝓜.complete
        (oidRel (lamDKB 𝓜.D V K) 𝓜.D
          (InternalReflexiveModel.interpDKGraph 𝓜 V K hK hV η)
          (InternalReflexiveModel.interpDKGraph_isFunctionB
            𝓜 V K hK hV η))) M d =
      memB (opairB ((lamDKB 𝓜.D V K).child M) (𝓜.D.child d))
        (InternalReflexiveModel.interpDKGraph 𝓜 V K hK hV η) :=
  theorem26FullOfFunctionName_gamma 𝓜.D V K
    (InternalReflexiveModel.interpDKGraph 𝓜 V K hK hV η)
    (InternalReflexiveModel.interpDKGraph_isFunctionB 𝓜 V K hK hV η)
    𝓜.complete M d

/-- Definition 25 at a `lamDKB` index, via the `SetoidF_A` representative. -/
theorem theorem26Full_eval
    (𝓜 : InternalReflexiveModel (A := A))
    (V K : AName.{u} A) (hK : subsetB K 𝓜.D = ⊤)
    (hV : (oid V).IsTotal)
    (η : RelFun (oid V) (oid 𝓜.D))
    (M : (lamDKB 𝓜.D V K).idx) (d : 𝓜.D.idx) :
    lamDKVal V K (asLamDK 𝓜.D V K M) ⊓
        gamma (oid (lamDKB 𝓜.D V K)) (oid 𝓜.D)
          (functionalOfRel 𝓜.complete
            (oidRel (lamDKB 𝓜.D V K) 𝓜.D
              (InternalReflexiveModel.interpDKGraph 𝓜 V K hK hV η)
              (InternalReflexiveModel.interpDKGraph_isFunctionB
                𝓜 V K hK hV η))) M d =
      interpDKRelVal 𝓜 V K hK hV η (asLamDK 𝓜.D V K M) d := by
  rw [theorem26Full_gamma, ← asLamDK_encode]
  exact InternalReflexiveModel.interpDKGraph_eval 𝓜 V K hK hV η
    (asLamDK 𝓜.D V K M) d

theorem theorem26Full_var
    (𝓜 : InternalReflexiveModel (A := A))
    (V K : AName.{u} A) (hK : subsetB K 𝓜.D = ⊤)
    (hV : (oid V).IsTotal)
    (η : RelFun (oid V) (oid 𝓜.D))
    (x : V.idx) (d : 𝓜.D.idx) :
    lamDKVal V K (.var x) ⊓
        memB (opairB (encodeLamDKB V K (.var x)) (𝓜.D.child d))
          (InternalReflexiveModel.interpDKGraph 𝓜 V K hK hV η) =
      η.val x d :=
  InternalReflexiveModel.interpDKGraph_var_val 𝓜 V K hK hV η x d

theorem theorem26Full_const
    (𝓜 : InternalReflexiveModel (A := A))
    (V K : AName.{u} A) (hK : subsetB K 𝓜.D = ⊤)
    (hV : (oid V).IsTotal)
    (η : RelFun (oid V) (oid 𝓜.D))
    (k : K.idx) (d : 𝓜.D.idx) :
    lamDKVal V K (.const k) ⊓
        memB (opairB (encodeLamDKB V K (.const k)) (𝓜.D.child d))
          (InternalReflexiveModel.interpDKGraph 𝓜 V K hK hV η) =
      (oidSubsetRel K 𝓜.D hK).val k d :=
  InternalReflexiveModel.interpDKGraph_const_val 𝓜 V K hK hV η k d

theorem theorem26Full_app
    (𝓜 : InternalReflexiveModel (A := A))
    (V K : AName.{u} A) (hK : subsetB K 𝓜.D = ⊤)
    (hV : (oid V).IsTotal)
    (η : RelFun (oid V) (oid 𝓜.D))
    (P Q : LamDK V.idx K.idx) (d : 𝓜.D.idx) :
    lamDKVal V K (.app P Q) ⊓
        memB (opairB (encodeLamDKB V K (.app P Q)) (𝓜.D.child d))
          (InternalReflexiveModel.interpDKGraph 𝓜 V K hK hV η) =
      interpDKRelVal 𝓜 V K hK hV η (.app P Q) d :=
  InternalReflexiveModel.interpDKGraph_app 𝓜 V K hK hV η P Q d

theorem theorem26Full_abs
    (𝓜 : InternalReflexiveModel (A := A))
    (V K : AName.{u} A) (hK : subsetB K 𝓜.D = ⊤)
    (hV : (oid V).IsTotal)
    (η : RelFun (oid V) (oid 𝓜.D))
    (x : V.idx) (P : LamDK V.idx K.idx) (d : 𝓜.D.idx) :
    lamDKVal V K (.abs x P) ⊓
        memB (opairB (encodeLamDKB V K (.abs x P)) (𝓜.D.child d))
          (InternalReflexiveModel.interpDKGraph 𝓜 V K hK hV η) =
      lamDKVal V K (.abs x P) ⊓
        memB (opairB (interpDKBodyGraph 𝓜 V K hK hV η x P)
          (𝓜.D.child d)) 𝓜.Lam :=
  InternalReflexiveModel.interpDKGraph_abs_val 𝓜 V K hK hV η x P d

/-- `SetoidF_A` evaluation of `theorem26Pure` recovers the pure graph. -/
theorem theorem26Pure_gamma
    (𝓜 : InternalReflexiveModel (A := A))
    (V K : AName.{u} A) (hK : subsetB K 𝓜.D = ⊤)
    (hV : (oid V).IsTotal)
    (η : RelFun (oid V) (oid 𝓜.D))
    (M : (lamB V).idx) (d : 𝓜.D.idx) :
    gamma (oid (lamB V)) (oid 𝓜.D)
      (functionalOfRel 𝓜.complete
        (oidRel (lamB V) 𝓜.D
          (InternalReflexiveModel.interpDKPureGraph 𝓜 V K hK hV η)
          (InternalReflexiveModel.interpDKPureGraph_isFunctionB
            𝓜 V K hK hV η))) M d =
      memB (opairB ((lamB V).child M) (𝓜.D.child d))
        (InternalReflexiveModel.interpDKPureGraph 𝓜 V K hK hV η) :=
  theorem26PureOfFunctionName_gamma 𝓜.D V
    (InternalReflexiveModel.interpDKPureGraph 𝓜 V K hK hV η)
    (InternalReflexiveModel.interpDKPureGraph_isFunctionB 𝓜 V K hK hV η)
    𝓜.complete M d

end Scott2026
