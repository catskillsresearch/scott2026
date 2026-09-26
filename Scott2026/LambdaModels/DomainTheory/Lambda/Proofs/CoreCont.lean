/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/

import Scott2026.LambdaModels.DomainTheory.Lambda.Lam
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.EquivFin
import Scott2026.LambdaModels.DomainTheory.Lambda.Lam.FreeFor
import Scott2026.LambdaModels.DomainTheory.Lambda.Lam.IsInductive
import Scott2026.LambdaModels.DomainTheory.Lambda.Lam.fv
import Scott2026.LambdaModels.DomainTheory.Lambda.Lam.pickFresh
import Scott2026.LambdaModels.DomainTheory.Lambda.Lam.size
import Scott2026.LambdaModels.DomainTheory.Lambda.Lam.subst
import Scott2026.LambdaModels.DomainTheory.Lambda.Lam.substCA
import Scott2026.LambdaModels.DomainTheory.Lambda.Lam.substNaive
import Scott2026.LambdaModels.DomainTheory.Lambda.Lam.vars
import Scott2026.LambdaModels.DomainTheory.Lambda.churchFalse
import Scott2026.LambdaModels.DomainTheory.Lambda.churchFalseN
import Scott2026.LambdaModels.DomainTheory.Lambda.churchFalseN'
import Scott2026.LambdaModels.DomainTheory.Lambda.churchId
import Scott2026.LambdaModels.DomainTheory.Lambda.churchIf
import Scott2026.LambdaModels.DomainTheory.Lambda.churchIfN
import Scott2026.LambdaModels.DomainTheory.Lambda.churchIsZero
import Scott2026.LambdaModels.DomainTheory.Lambda.churchIter
import Scott2026.LambdaModels.DomainTheory.Lambda.churchNotN
import Scott2026.LambdaModels.DomainTheory.Lambda.churchNum
import Scott2026.LambdaModels.DomainTheory.Lambda.churchNumBind
import Scott2026.LambdaModels.DomainTheory.Lambda.churchNumN
import Scott2026.LambdaModels.DomainTheory.Lambda.churchPred
import Scott2026.LambdaModels.DomainTheory.Lambda.churchPredBase
import Scott2026.LambdaModels.DomainTheory.Lambda.churchShift
import Scott2026.LambdaModels.DomainTheory.Lambda.churchShiftIter
import Scott2026.LambdaModels.DomainTheory.Lambda.churchSucc
import Scott2026.LambdaModels.DomainTheory.Lambda.churchTest
import Scott2026.LambdaModels.DomainTheory.Lambda.churchTrue
import Scott2026.LambdaModels.DomainTheory.Lambda.churchTrueN
import Scott2026.LambdaModels.DomainTheory.Lambda.churchTrueN'
import Scott2026.LambdaModels.DomainTheory.Lambda.Proofs.Core

namespace Scott2026

theorem churchTrueN'_lamEq : LamEq churchTrueN' churchTrueN := by
  have hα1 : (0 : ℕ) ∉ (Lam.abs 2 (Lam.var 1)).fv := by simp [Lam.fv]
  refine (LamEq.alpha 1 0 (Lam.abs 2 (Lam.var 1)) hα1).trans ?_
  have hsub1 : Lam.substCA (Lam.abs 2 (Lam.var 1)) 1 (Lam.var 0) =
      Lam.abs 2 (Lam.var 0) := by
    rw [substCA_abs_of_no_capture 2 1 (Lam.var 1) (Lam.var 0) (by decide)
      (by simp [Lam.fv]) (by simp [Lam.fv])]
    simp [Lam.substCA_var]
  rw [hsub1]
  have hα2 : (1 : ℕ) ∉ (Lam.var 0).fv := by simp [Lam.fv]
  refine (LamEq.xi 0 (LamEq.alpha 2 1 (Lam.var 0) hα2)).trans ?_
  simp [Lam.substCA_var, churchTrueN]
  exact LamEq.refl _

theorem churchFalseN'_lamEq : LamEq churchFalseN' churchFalseN := by
  have hα1 : (0 : ℕ) ∉ (Lam.abs 2 (Lam.var 2)).fv := by simp [Lam.fv]
  refine (LamEq.alpha 1 0 (Lam.abs 2 (Lam.var 2)) hα1).trans ?_
  have hsub1 : Lam.substCA (Lam.abs 2 (Lam.var 2)) 1 (Lam.var 0) =
      Lam.abs 2 (Lam.var 2) :=
    Lam.substCA_fresh _ (by simp [Lam.fv])
  rw [hsub1]
  have hα2 : (1 : ℕ) ∉ (Lam.var 2).fv := by simp [Lam.fv]
  refine (LamEq.xi 0 (LamEq.alpha 2 1 (Lam.var 2) hα2)).trans ?_
  simp [Lam.substCA_var, churchFalseN]
  exact LamEq.refl _

theorem churchIsZero_app (n : ℕ) :
    LamEq (churchIsZero.app (churchNumN n))
      (((churchNumN n).app (Lam.abs 1 churchFalseN')).app churchTrueN') := by
  refine (lamEq_beta_closed 0 _ (churchNumN n) (churchNumN_fv n)).trans ?_
  simp [churchIsZero, Lam.substNaive]
  exact LamEq.refl _

theorem churchIsZero_zero :
    LamEq (churchIsZero.app (churchNumN 0)) churchTrueN := by
  refine (churchIsZero_app 0).trans ?_
  have h1 : LamEq ((churchNumN 0).app (Lam.abs 1 churchFalseN'))
      (Lam.abs 1 (Lam.var 1)) := by
    refine (LamEq.beta 0 (Lam.abs 1 (Lam.var 1)) _).trans ?_
    rw [Lam.substCA_fresh]
    · exact LamEq.refl _
    · simp [Lam.fv]
  refine (LamEq.app_left h1).trans ?_
  refine (LamEq.beta 1 (Lam.var 1) churchTrueN').trans ?_
  rw [Lam.substCA_var, ite_eq_left rfl]
  exact churchTrueN'_lamEq

theorem churchIsZero_succ (n : ℕ) :
    LamEq (churchIsZero.app (churchNumN (n + 1))) churchFalseN := by
  refine (churchIsZero_app (n + 1)).trans ?_
  have hF : (Lam.abs 1 churchFalseN').fv = ∅ := by
    simp [Lam.fv, churchFalseN'_fv]
  have h1 : LamEq ((churchNumN (n + 1)).app (Lam.abs 1 churchFalseN'))
      (Lam.abs 1 (Lam.app (Lam.abs 1 churchFalseN')
        (Lam.app (Lam.app (churchNumN n) (Lam.abs 1 churchFalseN')) (Lam.var 1)))) := by
    refine (lamEq_beta_closed 0 _ (Lam.abs 1 churchFalseN') hF).trans ?_
    simp [Lam.substNaive]
    have hfresh :
        (churchNumN n).substNaive 0 (Lam.abs 1 churchFalseN') = churchNumN n :=
      Lam.subst_fresh (Lam.abs 1 churchFalseN') (by simp [churchNumN_fv n])
    rw [hfresh]
    exact LamEq.refl _
  refine (LamEq.app_left h1).trans ?_
  refine (lamEq_beta_closed 1 _ churchTrueN' churchTrueN'_fv).trans ?_
  have hbody :
      (Lam.app (Lam.abs 1 churchFalseN')
        (Lam.app (Lam.app (churchNumN n) (Lam.abs 1 churchFalseN'))
          (Lam.var 1))).substNaive 1 churchTrueN' =
        (Lam.abs 1 churchFalseN').app
          ((churchNumN n).app (Lam.abs 1 churchFalseN') |>.app churchTrueN') := by
    simp [Lam.substNaive]
    exact Lam.subst_fresh churchTrueN' (by simp [churchNumN_fv n])
  rw [hbody]
  have hFapp : LamEq
      ((Lam.abs 1 churchFalseN').app
        ((churchNumN n).app (Lam.abs 1 churchFalseN') |>.app churchTrueN'))
      churchFalseN' := by
    refine (LamEq.beta 1 churchFalseN' _).trans ?_
    rw [Lam.substCA_fresh]
    · exact LamEq.refl _
    · simp [churchFalseN'_fv]
  exact hFapp.trans churchFalseN'_lamEq

/-!
## Definition 32(iii): predecessor
-/

theorem churchShift_app (G : Lam ℕ) (hG : 4 ∉ G.fv) :
    LamEq (churchShift.app G)
      (Lam.abs 4 (Lam.app (Lam.var 4) (Lam.app G (Lam.var 1)))) := by
  refine (LamEq.beta 3
      (Lam.abs 4 (Lam.app (Lam.var 4) (Lam.app (Lam.var 3) (Lam.var 1)))) G).trans ?_
  rw [substCA_abs_of_no_capture 4 3 _ G (by decide) (by simp [Lam.fv]) hG]
  simp [Lam.substCA_app, Lam.substCA_var]
  exact LamEq.refl _

theorem churchShiftIter_succ_form (n : ℕ) :
    LamEq (churchShiftIter (n + 1))
      (Lam.abs 4 (Lam.app (Lam.var 4) (churchIter n (Lam.var 1) (Lam.var 2)))) := by
  induction n with
  | zero =>
    have h4 : (4 : ℕ) ∉ churchPredBase.fv := by simp [churchPredBase_fv]
    refine (churchShift_app churchPredBase h4).trans ?_
    have hβ : LamEq (churchPredBase.app (Lam.var 1)) (Lam.var 2) := by
      refine (LamEq.beta 3 (Lam.var 2) (Lam.var 1)).trans ?_
      simp [Lam.substCA_var]
      exact LamEq.refl _
    exact LamEq.xi 4 (LamEq.app_right hβ)
  | succ n ih =>
    refine (LamEq.app_right ih).trans ?_
    let W := churchIter n (Lam.var 1) (Lam.var 2)
    let G := Lam.abs 4 (Lam.app (Lam.var 4) W)
    have hG : (4 : ℕ) ∉ G.fv := by simp [G, Lam.fv]
    refine (churchShift_app G hG).trans ?_
    have hW4 : (4 : ℕ) ∉ W.fv :=
      churchIter_var_not_mem n 1 2 4 (by decide) (by decide)
    have hβ : LamEq (G.app (Lam.var 1)) (Lam.app (Lam.var 1) W) := by
      refine (LamEq.beta 4 (Lam.app (Lam.var 4) W) (Lam.var 1)).trans ?_
      simp [Lam.substCA_app, Lam.substCA_var, Lam.substCA_fresh (N := Lam.var 1) hW4]
      exact LamEq.refl _
    exact LamEq.xi 4 (LamEq.app_right hβ)

theorem churchShiftIter_zero_app_id :
    LamEq (churchShiftIter 0 |>.app churchId) (Lam.var 2) := by
  change LamEq (churchPredBase.app churchId) (Lam.var 2)
  refine (LamEq.beta 3 (Lam.var 2) churchId).trans ?_
  simp [Lam.substCA_var]
  exact LamEq.refl _

theorem churchShiftIter_succ_app_id (n : ℕ) :
    LamEq (churchShiftIter (n + 1) |>.app churchId)
      (churchIter n (Lam.var 1) (Lam.var 2)) := by
  refine (LamEq.app_left (churchShiftIter_succ_form n)).trans ?_
  let W := churchIter n (Lam.var 1) (Lam.var 2)
  have hW4 : (4 : ℕ) ∉ W.fv :=
    churchIter_var_not_mem n 1 2 4 (by decide) (by decide)
  refine (lamEq_beta_closed 4 (Lam.app (Lam.var 4) W) churchId churchId_fv).trans ?_
  have hsub : (Lam.app (Lam.var 4) W).substNaive 4 churchId = churchId.app W := by
    simp [Lam.substNaive, Lam.subst_fresh (N := churchId) hW4]
  rw [hsub]
  refine (LamEq.beta 3 (Lam.var 3) W).trans ?_
  simp [Lam.substCA_var]
  exact LamEq.refl _

theorem churchPred_app_num (n : ℕ) :
    LamEq (churchPred.app (churchNumN n))
      (Lam.abs 1 (Lam.abs 2
        (Lam.app (Lam.app (Lam.app (churchNumN n) churchShift) churchPredBase)
          churchId))) := by
  have hdef : churchPred =
      Lam.abs 0 (Lam.abs 1 (Lam.abs 2
        (Lam.app (Lam.app (Lam.app (Lam.var 0) churchShift) churchPredBase) churchId))) :=
    rfl
  rw [hdef]
  refine (lamEq_beta_closed 0 _ (churchNumN n) (churchNumN_fv n)).trans ?_
  simp [Lam.substNaive, churchShift_fv, churchPredBase_fv, churchId_fv]
  exact LamEq.refl _

theorem churchNumN_renamed (n : ℕ) :
    LamEq (Lam.abs 1 (Lam.abs 2 (churchIter n (Lam.var 1) (Lam.var 2))))
      (churchNumN n) := by
  have hα1 : (0 : ℕ) ∉ (Lam.abs 2 (churchIter n (Lam.var 1) (Lam.var 2))).fv := by
    intro h
    simp [Lam.fv] at h
    exact churchIter_var_not_mem n 1 2 0 (by decide) (by decide) h
  refine (LamEq.alpha 1 0 _ hα1).trans ?_
  have hsub1 :
      Lam.substCA (Lam.abs 2 (churchIter n (Lam.var 1) (Lam.var 2))) 1 (Lam.var 0) =
        Lam.abs 2 (churchIter n (Lam.var 0) (Lam.var 2)) := by
    rw [Lam.substCA_abs]
    have hne : (2 : ℕ) ≠ 1 := by decide
    rw [ite_eq_right hne]
    by_cases hx : (1 : ℕ) ∉ (churchIter n (Lam.var 1) (Lam.var 2)).fv
    · rw [ite_eq_left hx]
      have h1 := Lam.substCA_fresh (N := Lam.var 0) hx
      have h2 := substCA_churchIter n (Lam.var 1) (Lam.var 2) 1 (Lam.var 0)
      simp [Lam.substCA_var] at h2
      exact congrArg (Lam.abs 2) (h1.symm.trans h2)
    · have hy : (2 : ℕ) ∉ (Lam.var 0).fv := by simp [Lam.fv]
      rw [ite_eq_right hx, ite_eq_left hy, substCA_churchIter]
      simp [Lam.substCA_var]
  rw [hsub1]
  have hα2 : (1 : ℕ) ∉ (churchIter n (Lam.var 0) (Lam.var 2)).fv :=
    churchIter_var_not_mem n 0 2 1 (by decide) (by decide)
  refine (LamEq.xi 0 (LamEq.alpha 2 1 _ hα2)).trans ?_
  have hsub2 :
      Lam.substCA (churchIter n (Lam.var 0) (Lam.var 2)) 2 (Lam.var 1) =
        churchIter n (Lam.var 0) (Lam.var 1) := by
    rw [substCA_churchIter]
    simp [Lam.substCA_var]
  rw [hsub2]
  exact (churchNumN_lamEq_iter n).symm

theorem churchPred_zero :
    LamEq (churchPred.app (churchNumN 0)) (churchNumN 0) := by
  refine (churchPred_app_num 0).trans ?_
  have h1 : LamEq ((churchNumN 0).app churchShift) (Lam.abs 1 (Lam.var 1)) := by
    refine (LamEq.beta 0 (Lam.abs 1 (Lam.var 1)) churchShift).trans ?_
    rw [Lam.substCA_fresh]
    · exact LamEq.refl _
    · simp [Lam.fv]
  have h2 : LamEq (((churchNumN 0).app churchShift).app churchPredBase)
      churchPredBase := by
    refine (LamEq.app_left h1).trans ?_
    refine (LamEq.beta 1 (Lam.var 1) churchPredBase).trans ?_
    simp [Lam.substCA_var]
    exact LamEq.refl _
  have h3 : LamEq
      ((((churchNumN 0).app churchShift).app churchPredBase).app churchId)
      (Lam.var 2) :=
    (LamEq.app_left h2).trans churchShiftIter_zero_app_id
  refine (LamEq.xi 1 (LamEq.xi 2 h3)).trans ?_
  have hα1 : (0 : ℕ) ∉ (Lam.abs 2 (Lam.var 2)).fv := by simp [Lam.fv]
  refine (LamEq.alpha 1 0 _ hα1).trans ?_
  rw [Lam.substCA_fresh _ (by simp [Lam.fv])]
  have hα2 : (1 : ℕ) ∉ (Lam.var 2).fv := by simp [Lam.fv]
  refine (LamEq.xi 0 (LamEq.alpha 2 1 _ hα2)).trans ?_
  simp [Lam.substCA_var, churchNumN]
  exact LamEq.refl _

theorem churchPred_succ (n : ℕ) :
    LamEq (churchPred.app (churchNumN (n + 1))) (churchNumN n) := by
  refine (churchPred_app_num (n + 1)).trans ?_
  have h6 : (6 : ℕ) ∉ churchShift.fv := by simp [churchShift_fv]
  have hiter : LamEq
      (((churchNumN (n + 1)).app churchShift).app churchPredBase)
      (churchShiftIter (n + 1)) := by
    have h := churchNumBind_iter (n + 1) churchShift churchPredBase h6
    rw [churchShiftIter_eq_iter]
    exact (LamEq.app_congr (LamEq.app_left (churchNumN_fresh (n + 1)))
      (LamEq.refl churchPredBase)).trans h
  have hbody : LamEq
      ((((churchNumN (n + 1)).app churchShift).app churchPredBase).app churchId)
      (churchIter n (Lam.var 1) (Lam.var 2)) :=
    (LamEq.app_left hiter).trans (churchShiftIter_succ_app_id n)
  exact (LamEq.xi 1 (LamEq.xi 2 hbody)).trans (churchNumN_renamed n)

/-- Definition 32: Church Booleans/numerals and combinators are closed and
satisfy the paper's `λ ⊢` identities (ii)–(iv). Distinctness (i) is
semantic and lives in `Interp`. -/
theorem definition_32 :
    churchTrueN.fv = ∅ ∧ churchFalseN.fv = ∅ ∧ (∀ n, (churchNumN n).fv = ∅) ∧
    churchIfN.fv = ∅ ∧ churchSucc.fv = ∅ ∧ churchPred.fv = ∅ ∧ churchIsZero.fv = ∅ ∧
    (∀ M N : Lam ℕ, LamEq (((churchIfN.app churchTrueN).app M).app N) M) ∧
    (∀ M N : Lam ℕ, LamEq (((churchIfN.app churchFalseN).app M).app N) N) ∧
    (∀ n, LamEq (churchSucc.app (churchNumN n)) (churchNumN (n + 1))) ∧
    (∀ n, LamEq (churchPred.app (churchNumN (n + 1))) (churchNumN n)) ∧
    LamEq (churchPred.app (churchNumN 0)) (churchNumN 0) ∧
    LamEq (churchIsZero.app (churchNumN 0)) churchTrueN ∧
    (∀ n, LamEq (churchIsZero.app (churchNumN (n + 1))) churchFalseN) :=
  ⟨churchTrueN_fv, churchFalseN_fv, churchNumN_fv,
    churchIfN_fv, churchSucc_fv, churchPred_fv, churchIsZero_fv,
    churchIfN_true, churchIfN_false, churchSucc_num, churchPred_succ,
    churchPred_zero, churchIsZero_zero, churchIsZero_succ⟩

/-!
## Lemma 35(i) combinators: negation and `m?`

Paper: `¬` is Church negation, `1? = λm. if (0? m) ⊥ (0? (pred m))`,
and `n? = λm. (n-1)? (pred m)` for `n ≥ 2`. `0?` is `churchIsZero`.
These stay on `ℕ`; `churchNot` on `Fin 2` is unchanged.
-/

theorem churchNotN_fv : churchNotN.fv = ∅ := by
  simp [churchNotN, churchFalseN_fv, churchTrueN_fv, Lam.fv]

theorem churchNotN_true :
    LamEq (churchNotN.app churchTrueN) churchFalseN := by
  refine (lamEq_beta_closed 0 _ churchTrueN churchTrueN_fv).trans ?_
  have hF : churchFalseN.substNaive 0 churchTrueN = churchFalseN :=
    Lam.subst_fresh churchTrueN (by simp [churchFalseN_fv])
  have hT : churchTrueN.substNaive 0 churchTrueN = churchTrueN :=
    Lam.subst_fresh churchTrueN (by simp [churchTrueN_fv])
  simp [Lam.substNaive, hF, hT]
  exact churchTrueN_app churchFalseN churchTrueN

theorem churchNotN_false :
    LamEq (churchNotN.app churchFalseN) churchTrueN := by
  refine (lamEq_beta_closed 0 _ churchFalseN churchFalseN_fv).trans ?_
  have hF : churchFalseN.substNaive 0 churchFalseN = churchFalseN :=
    Lam.subst_fresh churchFalseN (by simp [churchFalseN_fv])
  have hT : churchTrueN.substNaive 0 churchFalseN = churchTrueN :=
    Lam.subst_fresh churchFalseN (by simp [churchTrueN_fv])
  simp [Lam.substNaive, hF, hT]
  exact churchFalseN_app churchFalseN churchTrueN

/-- Paper `m?`: `0?` is `churchIsZero`; `1?` and `n?` (`n ≥ 2`) follow the
paper's closed-term recurrences. Binder `0` is free only in the applied
argument; the combinators are closed. -/
theorem churchTest_fv : ∀ m, (churchTest m).fv = ∅
  | 0 => churchIsZero_fv
  | 1 => by
    simp [churchTest, churchIfN_fv, churchIsZero_fv, churchFalseN_fv,
      churchPred_fv, Lam.fv]
  | n + 2 => by
    simp [churchTest, churchTest_fv (n + 1), churchPred_fv, Lam.fv]

theorem churchTest_one_app (N : Lam ℕ) (hN : N.fv = ∅) :
    LamEq ((churchTest 1).app N)
      (((churchIfN.app (churchIsZero.app N)).app churchFalseN).app
        (churchIsZero.app (churchPred.app N))) := by
  refine (lamEq_beta_closed 0 _ N hN).trans ?_
  have hIf : churchIfN.substNaive 0 N = churchIfN :=
    Lam.subst_fresh N (by simp [churchIfN_fv])
  have hZ : churchIsZero.substNaive 0 N = churchIsZero :=
    Lam.subst_fresh N (by simp [churchIsZero_fv])
  have hF : churchFalseN.substNaive 0 N = churchFalseN :=
    Lam.subst_fresh N (by simp [churchFalseN_fv])
  have hP : churchPred.substNaive 0 N = churchPred :=
    Lam.subst_fresh N (by simp [churchPred_fv])
  simp [Lam.substNaive, hIf, hZ, hF, hP]
  exact LamEq.refl _

theorem churchTest_succ_app (m : ℕ) (N : Lam ℕ) (hN : N.fv = ∅) :
    LamEq ((churchTest (m + 2)).app N)
      ((churchTest (m + 1)).app (churchPred.app N)) := by
  refine (lamEq_beta_closed 0 _ N hN).trans ?_
  have hT : (churchTest (m + 1)).substNaive 0 N = churchTest (m + 1) :=
    Lam.subst_fresh N (by simp [churchTest_fv (m + 1)])
  have hP : churchPred.substNaive 0 N = churchPred :=
    Lam.subst_fresh N (by simp [churchPred_fv])
  simp [Lam.substNaive, hT, hP]
  exact LamEq.refl _

theorem churchTest_num : ∀ m n : ℕ,
    LamEq ((churchTest m).app (churchNumN n))
      (if n = m then churchTrueN else churchFalseN)
  | 0, n => by
    change LamEq (churchIsZero.app (churchNumN n))
      (if n = 0 then churchTrueN else churchFalseN)
    by_cases hn : n = 0
    · subst hn
      simpa using churchIsZero_zero
    · obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
      simpa using churchIsZero_succ k
  | 1, n => by
    refine (churchTest_one_app (churchNumN n) (churchNumN_fv n)).trans ?_
    match n with
    | 0 =>
      have hif : LamEq
          (((churchIfN.app (churchIsZero.app (churchNumN 0))).app churchFalseN).app
            (churchIsZero.app (churchPred.app (churchNumN 0))))
          (((churchIfN.app churchTrueN).app churchFalseN).app
            (churchIsZero.app (churchPred.app (churchNumN 0)))) :=
        LamEq.app_left (LamEq.app_left (LamEq.app_right churchIsZero_zero))
      refine hif.trans ?_
      simpa using churchIfN_true churchFalseN
        (churchIsZero.app (churchPred.app (churchNumN 0)))
    | 1 =>
      have hZ : LamEq (churchIsZero.app (churchNumN 1)) churchFalseN :=
        churchIsZero_succ 0
      have hif : LamEq
          (((churchIfN.app (churchIsZero.app (churchNumN 1))).app churchFalseN).app
            (churchIsZero.app (churchPred.app (churchNumN 1))))
          (((churchIfN.app churchFalseN).app churchFalseN).app
            (churchIsZero.app (churchPred.app (churchNumN 1)))) :=
        LamEq.app_left (LamEq.app_left (LamEq.app_right hZ))
      refine hif.trans ?_
      have helse : LamEq
          (((churchIfN.app churchFalseN).app churchFalseN).app
            (churchIsZero.app (churchPred.app (churchNumN 1))))
          (churchIsZero.app (churchPred.app (churchNumN 1))) :=
        churchIfN_false churchFalseN (churchIsZero.app (churchPred.app (churchNumN 1)))
      refine helse.trans ?_
      have hp : LamEq (churchPred.app (churchNumN 1)) (churchNumN 0) :=
        churchPred_succ 0
      exact (LamEq.app_right hp).trans churchIsZero_zero
    | k + 2 =>
      have hZ : LamEq (churchIsZero.app (churchNumN (k + 2))) churchFalseN :=
        churchIsZero_succ (k + 1)
      have hif : LamEq
          (((churchIfN.app (churchIsZero.app (churchNumN (k + 2)))).app
            churchFalseN).app
            (churchIsZero.app (churchPred.app (churchNumN (k + 2)))))
          (((churchIfN.app churchFalseN).app churchFalseN).app
            (churchIsZero.app (churchPred.app (churchNumN (k + 2))))) :=
        LamEq.app_left (LamEq.app_left (LamEq.app_right hZ))
      refine hif.trans ?_
      have helse : LamEq
          (((churchIfN.app churchFalseN).app churchFalseN).app
            (churchIsZero.app (churchPred.app (churchNumN (k + 2)))))
          (churchIsZero.app (churchPred.app (churchNumN (k + 2)))) :=
        churchIfN_false churchFalseN
          (churchIsZero.app (churchPred.app (churchNumN (k + 2))))
      refine helse.trans ?_
      have hp : LamEq (churchPred.app (churchNumN (k + 2))) (churchNumN (k + 1)) :=
        churchPred_succ (k + 1)
      exact (LamEq.app_right hp).trans (churchIsZero_succ k)
  | m + 2, n => by
    refine (churchTest_succ_app m (churchNumN n) (churchNumN_fv n)).trans ?_
    match n with
    | 0 =>
      have hp : LamEq (churchPred.app (churchNumN 0)) (churchNumN 0) :=
        churchPred_zero
      refine (LamEq.app_right hp).trans ?_
      have ih := churchTest_num (m + 1) 0
      have hne : ¬(0 = m + 1) := (Nat.succ_ne_zero m).symm
      have hne' : ¬(0 = m + 2) := (Nat.succ_ne_zero (m + 1)).symm
      simpa [hne, hne'] using ih
    | j + 1 =>
      have hp : LamEq (churchPred.app (churchNumN (j + 1))) (churchNumN j) :=
        churchPred_succ j
      refine (LamEq.app_right hp).trans ?_
      have ih := churchTest_num (m + 1) j
      by_cases hj : j = m + 1
      · subst hj
        simpa using ih
      · have hj' : ¬(j + 1 = m + 2) := by
          intro h
          exact hj (Nat.succ_injective h)
        simpa [hj, hj'] using ih

end Scott2026
