/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/

import Scott2026.InternalEvalComplete
import Scott2026.InternalReflexiveModel
import Scott2026.InternalEvalPack.InternalReflexiveModel.interpDKRel
import Scott2026.InternalEvalPack.LamDKLaws

universe u

namespace Scott2026

open AName
variable {A : Type u} [CompleteBooleanAlgebra A]
open InternalReflexiveModel
namespace InternalReflexiveModel

noncomputable def interpDKPureRel
    (𝓜 : InternalReflexiveModel (A := A))
    (V K : AName.{u} A) (hK : subsetB K 𝓜.D = ⊤)
    (hV : (oid V).IsTotal)
    (η : RelFun (oid V) (oid 𝓜.D)) :
    RelFun (oid (lamB V)) (oid 𝓜.D) where
  val M d :=
    interpDKRelVal 𝓜 V K hK hV η (LamDK.ofLam (asLam V M)) d
  respects := by
    intro M N d e
    refine le_inf ?_ ?_ <;> rw [le_himp_iff]
    · let t :=
        (oid (lamB V)).eq M N ⊓ (oid 𝓜.D).eq d e ⊓
          interpDKRelVal 𝓜 V K hK hV η (LamDK.ofLam (asLam V M)) d
      have henc :
          t ≤ eqB (encodeLamDKB V K (LamDK.ofLam (asLam V M)))
            (encodeLamDKB V K (LamDK.ofLam (asLam V N))) := by
        rw [encodeLamDKB_ofLam_asLam, encodeLamDKB_ofLam_asLam]
        exact (oid_eq_le_eqB_child _ M N).trans'
          (inf_le_left.trans inf_le_left)
      have hval :
          t ≤ interpDKRelVal 𝓜 V K hK hV η
            (LamDK.ofLam (asLam V M)) d := inf_le_right
      have hN :
          t ≤ interpDKRelVal 𝓜 V K hK hV η
            (LamDK.ofLam (asLam V N)) d :=
        (interpDKRelVal_encode_congr 𝓜 V K hK hV η
          (LamDK.ofLam (asLam V M)) (LamDK.ofLam (asLam V N)) d).trans'
          (le_inf henc hval)
      have hde : t ≤ (oid 𝓜.D).eq d e := inf_le_left.trans inf_le_right
      exact (interpDKRelVal_isRelElementAt 𝓜 V K hK hV η
          (LamDK.ofLam (asLam V N))).respects d e |>.trans'
        (le_inf hde hN)
    · let t :=
        (oid (lamB V)).eq M N ⊓ (oid 𝓜.D).eq d e ⊓
          interpDKRelVal 𝓜 V K hK hV η (LamDK.ofLam (asLam V N)) e
      have henc :
          t ≤ eqB (encodeLamDKB V K (LamDK.ofLam (asLam V N)))
            (encodeLamDKB V K (LamDK.ofLam (asLam V M))) := by
        rw [encodeLamDKB_ofLam_asLam, encodeLamDKB_ofLam_asLam, eqB_comm]
        exact (oid_eq_le_eqB_child _ M N).trans'
          (inf_le_left.trans inf_le_left)
      have hval :
          t ≤ interpDKRelVal 𝓜 V K hK hV η
            (LamDK.ofLam (asLam V N)) e := inf_le_right
      have hM :
          t ≤ interpDKRelVal 𝓜 V K hK hV η
            (LamDK.ofLam (asLam V M)) e :=
        (interpDKRelVal_encode_congr 𝓜 V K hK hV η
          (LamDK.ofLam (asLam V N)) (LamDK.ofLam (asLam V M)) e).trans'
          (le_inf henc hval)
      have hde : t ≤ (oid 𝓜.D).eq e d := by
        rw [(oid 𝓜.D).symm]
        exact inf_le_left.trans inf_le_right
      exact (interpDKRelVal_isRelElementAt 𝓜 V K hK hV η
          (LamDK.ofLam (asLam V M))).respects e d |>.trans'
        (le_inf hde hM)
  le_eps := by
    intro M d
    have h :=
      (interpDKRelVal_isRelElementAt 𝓜 V K hK hV η
        (LamDK.ofLam (asLam V M))).2.1 d
    rw [lamDKVal_ofLam V K hV (asLam V M), top_inf_eq] at h
    rw [oid_eps, oid_eps]
    refine le_inf ?_ ?_
    · have hmem : memB ((lamB V).child M) (lamB V) = ⊤ := by
        rw [← asLam_encode V M]
        exact memB_encodeLamB V (asLam V M)
      exact le_top.trans hmem.ge
    · rw [oid_eps] at h
      exact h
  single_valued := by
    intro M d e
    exact (interpDKRelVal_isRelElementAt 𝓜 V K hK hV η
      (LamDK.ofLam (asLam V M))).2.2.1 d e
  total := by
    intro M
    rw [oid_eps]
    have hmem : memB ((lamB V).child M) (lamB V) = ⊤ := by
      rw [← asLam_encode V M]
      exact memB_encodeLamB V (asLam V M)
    rw [hmem]
    have htot :=
      (interpDKRelVal_isRelElementAt 𝓜 V K hK hV η
        (LamDK.ofLam (asLam V M))).2.2.2
    rwa [lamDKVal_ofLam V K hV (asLam V M)] at htot


end InternalReflexiveModel

end Scott2026
