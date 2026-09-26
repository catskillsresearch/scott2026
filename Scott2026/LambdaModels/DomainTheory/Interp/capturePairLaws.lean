/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/

import Scott2026.LambdaModels.DomainTheory.Interp.captureListCode
import Scott2026.LambdaModels.DomainTheory.Interp.capturePair

namespace Scott2026

open Set Function

theorem captureListCode_injective : Function.Injective captureListCode := by
  intro xs
  induction xs with
  | nil =>
    intro ys h
    cases ys with
    | nil => rfl
    | cons _ _ => simp [captureListCode] at h
  | cons a as ih =>
    intro ys h
    cases ys with
    | nil => simp [captureListCode] at h
    | cons b bs =>
      have hpair : Nat.pair a (captureListCode as) = Nat.pair b (captureListCode bs) :=
        Nat.succ_injective (by simpa [captureListCode] using h)
      have hab := Nat.pair_eq_pair.mp hpair
      exact congr_arg₂ List.cons hab.1 (ih hab.2)

theorem capturePair_injective : Function.Injective capturePair := by
  intro p q h
  have hpq := Nat.pair_eq_pair.mp h
  have hlist : p.1.sort (· ≤ ·) = q.1.sort (· ≤ ·) :=
    captureListCode_injective hpq.1
  refine Prod.ext ?_ hpq.2
  apply Finset.ext
  intro x
  rw [← Finset.mem_sort (s := p.1) (r := (· ≤ ·)) (a := x), hlist]
  exact Finset.mem_sort (s := q.1) (r := (· ≤ ·)) (a := x)

end Scott2026
