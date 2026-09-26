/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/

import Scott2026.LambdaModels.DomainTheory.InternalEvalComplete
import Scott2026.LambdaModels.DomainTheory.InternalReflexiveModel
import Scott2026.LambdaModels.DomainTheory.InternalEvalPack.asLamDK
import Scott2026.LambdaModels.DomainTheory.InternalEvalPack.Proofs.Core

universe u

namespace Scott2026

open AName
variable {A : Type u} [CompleteBooleanAlgebra A]
open InternalReflexiveModel
namespace InternalReflexiveModel

/-- Relational function assembled from the term-indexed evaluation rows. -/
noncomputable def interpDKRel
    (𝓜 : InternalReflexiveModel (A := A))
    (V K : AName.{u} A) (hK : subsetB K 𝓜.D = ⊤)
    (hV : (oid V).IsTotal)
    (η : RelFun (oid V) (oid 𝓜.D)) :
    RelFun (oid (lamDKB 𝓜.D V K)) (oid 𝓜.D) where
  val M d :=
    interpDKRelVal 𝓜 V K hK hV η (asLamDK 𝓜.D V K M) d
  respects := by
    intro M N d e
    refine le_inf ?_ ?_ <;> rw [le_himp_iff]
    · let t :=
        (oid (lamDKB 𝓜.D V K)).eq M N ⊓ (oid 𝓜.D).eq d e ⊓
          interpDKRelVal 𝓜 V K hK hV η (asLamDK 𝓜.D V K M) d
      have henc :
          t ≤ eqB (encodeLamDKB V K (asLamDK 𝓜.D V K M))
            (encodeLamDKB V K (asLamDK 𝓜.D V K N)) := by
        rw [asLamDK_encode, asLamDK_encode]
        exact (oid_eq_le_eqB_child _ M N).trans'
          (inf_le_left.trans inf_le_left)
      have hval :
          t ≤ interpDKRelVal 𝓜 V K hK hV η (asLamDK 𝓜.D V K M) d :=
        inf_le_right
      have hN :
          t ≤ interpDKRelVal 𝓜 V K hK hV η (asLamDK 𝓜.D V K N) d :=
        (interpDKRelVal_encode_congr 𝓜 V K hK hV η
          (asLamDK 𝓜.D V K M) (asLamDK 𝓜.D V K N) d).trans'
          (le_inf henc hval)
      have hde : t ≤ (oid 𝓜.D).eq d e := inf_le_left.trans inf_le_right
      exact (interpDKRelVal_isRelElementAt 𝓜 V K hK hV η
          (asLamDK 𝓜.D V K N)).respects d e |>.trans' (le_inf hde hN)
    · let t :=
        (oid (lamDKB 𝓜.D V K)).eq M N ⊓ (oid 𝓜.D).eq d e ⊓
          interpDKRelVal 𝓜 V K hK hV η (asLamDK 𝓜.D V K N) e
      have henc :
          t ≤ eqB (encodeLamDKB V K (asLamDK 𝓜.D V K N))
            (encodeLamDKB V K (asLamDK 𝓜.D V K M)) := by
        rw [asLamDK_encode, asLamDK_encode, eqB_comm]
        exact (oid_eq_le_eqB_child _ M N).trans'
          (inf_le_left.trans inf_le_left)
      have hval :
          t ≤ interpDKRelVal 𝓜 V K hK hV η (asLamDK 𝓜.D V K N) e :=
        inf_le_right
      have hM :
          t ≤ interpDKRelVal 𝓜 V K hK hV η (asLamDK 𝓜.D V K M) e :=
        (interpDKRelVal_encode_congr 𝓜 V K hK hV η
          (asLamDK 𝓜.D V K N) (asLamDK 𝓜.D V K M) e).trans'
          (le_inf henc hval)
      have hde : t ≤ (oid 𝓜.D).eq e d := by
        rw [(oid 𝓜.D).symm]
        exact inf_le_left.trans inf_le_right
      exact (interpDKRelVal_isRelElementAt 𝓜 V K hK hV η
          (asLamDK 𝓜.D V K M)).respects e d |>.trans' (le_inf hde hM)
  le_eps := by
    intro M d
    have h :=
      (interpDKRelVal_isRelElementAt 𝓜 V K hK hV η
        (asLamDK 𝓜.D V K M)).2.1 d
    rw [oid_eps, oid_eps]
    refine le_inf ?_ ?_
    · have hmem :=
        lamDKVal_le_memB 𝓜.D V K (asLamDK 𝓜.D V K M)
      rw [asLamDK_encode] at hmem
      exact hmem.trans' (h.trans inf_le_left)
    · rw [oid_eps] at h
      exact h.trans inf_le_right
  single_valued := by
    intro M d e
    exact (interpDKRelVal_isRelElementAt 𝓜 V K hK hV η
      (asLamDK 𝓜.D V K M)).2.2.1 d e
  total := by
    intro M
    rw [oid_eps, memB_lamDKB]
    refine iSup_le fun N => ?_
    have htot :=
      (interpDKRelVal_isRelElementAt 𝓜 V K hK hV η N).2.2.2
    refine (le_inf le_rfl (inf_le_right.trans htot)).trans ?_
    rw [inf_iSup_eq]
    refine iSup_le fun d => le_iSup_of_le d ?_
    refine (interpDKRelVal_encode_congr 𝓜 V K hK hV η N
      (asLamDK 𝓜.D V K M) d).trans' ?_
    calc
      eqB ((lamDKB 𝓜.D V K).child M) (encodeLamDKB V K N) ⊓
          lamDKVal V K N ⊓ interpDKRelVal 𝓜 V K hK hV η N d
        = eqB (encodeLamDKB V K (asLamDK 𝓜.D V K M))
            (encodeLamDKB V K N) ⊓
          lamDKVal V K N ⊓ interpDKRelVal 𝓜 V K hK hV η N d := by
            rw [asLamDK_encode]
      _ ≤ eqB (encodeLamDKB V K (asLamDK 𝓜.D V K M))
            (encodeLamDKB V K N) ⊓
          interpDKRelVal 𝓜 V K hK hV η N d :=
            le_inf (inf_le_left.trans inf_le_left) inf_le_right
      _ = eqB (encodeLamDKB V K N)
            (encodeLamDKB V K (asLamDK 𝓜.D V K M)) ⊓
          interpDKRelVal 𝓜 V K hK hV η N d := by
            rw [eqB_comm (encodeLamDKB V K (asLamDK 𝓜.D V K M))
              (encodeLamDKB V K N)]

@[simp] theorem interpDKRel_val
    (𝓜 : InternalReflexiveModel (A := A))
    (V K : AName.{u} A) (hK : subsetB K 𝓜.D = ⊤)
    (hV : (oid V).IsTotal)
    (η : RelFun (oid V) (oid 𝓜.D))
    (M : (lamDKB 𝓜.D V K).idx) (d : 𝓜.D.idx) :
    (interpDKRel 𝓜 V K hK hV η).val M d =
      interpDKRelVal 𝓜 V K hK hV η (asLamDK 𝓜.D V K M) d :=
  rfl


end InternalReflexiveModel

end Scott2026
