/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/

import Mathlib.Logic.Pairwise
import Mathlib.Order.CompleteBooleanAlgebra
import Scott2026.BooleanValuedSetTheory.VA.AName
import Scott2026.BooleanValuedSetTheory.VA.AName.child
import Scott2026.BooleanValuedSetTheory.VA.AName.idx
import Scott2026.BooleanValuedSetTheory.VA.AName.val
import Scott2026.BooleanValuedSetTheory.VA.AName.memEq
import Scott2026.BooleanValuedSetTheory.VA.AName.eqBLaws

namespace Scott2026

namespace AName

variable {A : Type u}
variable [CompleteBooleanAlgebra A]

/-- Jech Lemma 14.18: mix of an antichain of names. -/
noncomputable def mix {ι : Type u} (u : ι → A) (xs : ι → AName.{u} A) : AName.{u} A :=
  mk (Σ i : ι, (xs i).idx)
    (fun p => (xs p.1).child p.2)
    (fun p => u p.1 ⊓ (xs p.1).val p.2)

theorem mix_le_eqB {ι : Type u} (u : ι → A) (xs : ι → AName.{u} A)
    (hdis : Pairwise fun i j => u i ⊓ u j = ⊥) (i : ι) :
    u i ≤ eqB (mix u xs) (xs i) := by
  rw [eqB_eq_subset]
  refine le_inf ?le_mix ?mix_le
  · refine le_iInf fun p => ?_
    rw [le_himp_iff]
    rcases p with ⟨j, t⟩
    by_cases hij : i = j
    · subst hij
      have hval : (mix u xs).val ⟨i, t⟩ = u i ⊓ (xs i).val t := rfl
      rw [hval]
      exact (inf_le_of_right_le inf_le_right).trans (val_le_memB (xs i) t)
    · have : u i ⊓ u j = ⊥ := hdis hij
      have : u i ⊓ (u j ⊓ (xs j).val t) = ⊥ := by
        rw [← inf_assoc, this, bot_inf_eq]
      exact this.le.trans bot_le
  · refine le_iInf fun t => ?_
    rw [le_himp_iff]
    have : u i ⊓ (xs i).val t ≤
        eqB ((xs i).child t) ((xs i).child t) ⊓ (u i ⊓ (xs i).val t) := by
      rw [eqB_self]; exact le_inf le_top le_rfl
    refine this.trans ?_
    rw [memB_eq]
    exact le_iSup_of_le ⟨i, t⟩ le_rfl

end AName

end Scott2026
