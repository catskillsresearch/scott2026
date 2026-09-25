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
import Scott2026.VA.AName.rank
import Scott2026.VA.AName.val
import Scott2026.VA.AName.eqBLaws
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

namespace Scott2026

universe u

variable {A : Type u}
variable [CompleteBooleanAlgebra A]

open AName SetFormula D0Formula

theorem allInst_sound {n} (φ : SetFormula (n + 1)) (t : Fin n)
    (ρ : Fin n → AName.{u} A) :
    bval (implies (.all φ) (inst φ t)) ρ = ⊤ := by
  rw [SetFormula.bval_implies, SetFormula.bval_all, SetFormula.bval_inst,
    himp_eq_top_iff]
  exact iInf_le _ (ρ t)

theorem eqRefl_sound (ρ : Fin 0 → AName.{u} A) :
    bval (.all (.eq 0 0)) ρ = ⊤ := by
  rw [SetFormula.bval_all]
  refine iInf_eq_top.mpr fun x => ?_
  simp [SetFormula.bval_eq, consName, eqB_self]

theorem bval_eqLeibnizRenameX {n} (φ : SetFormula (n + 1))
    (y x : AName.{u} A) (ρ : Fin n → AName.{u} A) :
    SetFormula.bval (rename eqLeibnizRenameX φ) (consName y (consName x ρ)) =
      SetFormula.bval φ (consName x ρ) := by
  rw [SetFormula.bval_rename]
  congr 1
  funext i
  refine Fin.cases ?_ (fun i => ?_) i
  · rfl
  · simp [eqLeibnizRenameX, consName]

theorem bval_eqLeibnizRenameY {n} (φ : SetFormula (n + 1))
    (y x : AName.{u} A) (ρ : Fin n → AName.{u} A) :
    SetFormula.bval (rename eqLeibnizRenameY φ) (consName y (consName x ρ)) =
      SetFormula.bval φ (consName y ρ) := by
  rw [SetFormula.bval_rename]
  congr 1
  funext i
  refine Fin.cases ?_ (fun i => ?_) i
  · rfl
  · simp [eqLeibnizRenameY, consName]

theorem eqLeibniz_sound {n} (φ : SetFormula (n + 1))
    (ρ : Fin n → AName.{u} A) :
    bval (eqLeibnizAxiom φ) ρ = ⊤ := by
  unfold eqLeibnizAxiom
  rw [all_valid_iff]
  intro x
  rw [all_valid_iff]
  intro y
  rw [SetFormula.bval_implies, SetFormula.bval_implies, himp_eq_top_iff,
    le_himp_iff]
  have hx : consName y (consName x ρ) (1 : Fin (n + 2)) = x := rfl
  have hy : consName y (consName x ρ) (0 : Fin (n + 2)) = y := rfl
  simp only [SetFormula.bval_eq, hx, hy]
  rw [bval_eqLeibnizRenameX, bval_eqLeibnizRenameY]
  exact SetFormula.bval_subst φ x y ρ

theorem memB_opairB (z x y : AName.{u} A) :
    memB z (opairB x y) = eqB z (singletonB x) ⊔ eqB z (pairB x y) := by
  rw [opairB, memB_pairB]

theorem bval_isSingletonF {n} (z a : Fin n) (ρ : Fin n → AName.{u} A) :
    bval (isSingletonF z a) ρ = eqB (ρ z) (singletonB (ρ a)) := by
  unfold isSingletonF
  rw [SetFormula.bval_all]
  refine Eq.trans (iInf_congr fun w => ?_)
    (eqB_eq_iInf (ρ z) (singletonB (ρ a))).symm
  have hz : consName w ρ z.succ = ρ z := by simp [consName]
  have ha : consName w ρ a.succ = ρ a := by simp [consName]
  simp [SetFormula.bval_iff, SetFormula.bval_mem, SetFormula.bval_eq, hz, ha,
    memB_singletonB]

theorem bval_isUPairF {n} (z a b : Fin n) (ρ : Fin n → AName.{u} A) :
    bval (isUPairF z a b) ρ = eqB (ρ z) (pairB (ρ a) (ρ b)) := by
  unfold isUPairF
  rw [SetFormula.bval_all]
  refine Eq.trans (iInf_congr fun w => ?_)
    (eqB_eq_iInf (ρ z) (pairB (ρ a) (ρ b))).symm
  have hz : consName w ρ z.succ = ρ z := by simp [consName]
  have ha : consName w ρ a.succ = ρ a := by simp [consName]
  have hb : consName w ρ b.succ = ρ b := by simp [consName]
  simp [SetFormula.bval_iff, SetFormula.bval_or, SetFormula.bval_mem,
    SetFormula.bval_eq, hz, ha, hb, memB_pairB]

theorem bval_isOpairF {n} (p a b : Fin n) (ρ : Fin n → AName.{u} A) :
    bval (isOpairF p a b) ρ = eqB (ρ p) (opairB (ρ a) (ρ b)) := by
  unfold isOpairF
  rw [SetFormula.bval_all]
  refine Eq.trans (iInf_congr fun w => ?_)
    (eqB_eq_iInf (ρ p) (opairB (ρ a) (ρ b))).symm
  have hp : consName w ρ p.succ = ρ p := by simp [consName]
  have ha : consName w ρ a.succ = ρ a := by simp [consName]
  have hb : consName w ρ b.succ = ρ b := by simp [consName]
  have hw0 : consName w ρ 0 = w := rfl
  simp only [SetFormula.bval_iff, SetFormula.bval_or, SetFormula.bval_mem,
    bval_isSingletonF, bval_isUPairF, hw0, hp, ha, hb]
  rw [memB_opairB]

theorem bval_opairMemF {n} (a b r : Fin n) (ρ : Fin n → AName.{u} A) :
    bval (opairMemF a b r) ρ = memB (opairB (ρ a) (ρ b)) (ρ r) := by
  unfold opairMemF
  rw [SetFormula.bval_ex]
  refine Eq.trans (iSup_congr fun p => ?_)
    (iSup_eqB_inf_memB (opairB (ρ a) (ρ b)) (ρ r))
  simp [SetFormula.bval_and, SetFormula.bval_mem, bval_isOpairF, consName]

open Classical

omit [CompleteBooleanAlgebra A] in
theorem worITE_pos {p : Prop} {t e : A} (hp : p) : worITE p t e = t :=
  ite_eq_left hp

omit [CompleteBooleanAlgebra A] in
theorem worITE_neg {p : Prop} {t e : A} (hp : ¬p) : worITE p t e = e :=
  ite_eq_right hp

theorem worLe_refl {α : Type u} (i : α) : worLe (A := A) i i = ⊤ :=
  worITE_pos (Or.inr rfl)

theorem worLe_total {α : Type u} (i j : α) :
    worLe (A := A) i j ⊔ worLe (A := A) j i = ⊤ := by
  unfold worLe worITE
  rcases trichotomous (r := WellOrderingRel) i j with h | h | h
  · simp [h]
  · simp [h]
  · simp [h]

theorem worLe_of_eq {α : Type u} {i j : α} (h : i = j) :
    worLe (A := A) i j = ⊤ := by
  subst h; exact worLe_refl i

theorem worLe_trans {α : Type u} (i j k : α) :
    worLe (A := A) i j ⊓ worLe (A := A) j k ≤ worLe (A := A) i k := by
  unfold worLe worITE
  by_cases hij : WellOrderingRel i j ∨ i = j
  · by_cases hjk : WellOrderingRel j k ∨ j = k
    · have hik : WellOrderingRel i k ∨ i = k := by
        rcases hij with hij | hij <;> rcases hjk with hjk | hjk
        · exact Or.inl (IsTrans.trans (r := WellOrderingRel) i j k hij hjk)
        · subst hjk; exact Or.inl hij
        · subst hij; exact Or.inl hjk
        · subst hij; subst hjk; exact Or.inr rfl
      simp [hij, hjk, hik]
    · simp [hij, hjk]
  · simp [hij]

theorem worLe_antisymm {α : Type u} (i j : α) :
    worLe (A := A) i j ⊓ worLe (A := A) j i ≤ worITE (i = j) (⊤ : A) ⊥ := by
  unfold worLe
  by_cases hij : i = j
  · simp [worITE, hij]
  · by_cases hlt : WellOrderingRel i j
    · have hn : ¬WellOrderingRel j i := asymm hlt
      have hne : ¬(WellOrderingRel j i ∨ j = i) := by
        rintro (h | h)
        · exact hn h
        · exact hij h.symm
      simp [worITE, hij, hlt, hne]
    · have hne : ¬(WellOrderingRel i j ∨ i = j) := by
        rintro (h | h) <;> contradiction
      simp [worITE, hne]

theorem worPred_compl {α : Type u} (a : α → A) (i : α) :
    (⨅ j : α, worITE (WellOrderingRel j i) (a j)ᶜ ⊤) = (worPredSup a i)ᶜ := by
  have h : ∀ j : α,
      worITE (WellOrderingRel j i) (a j)ᶜ ⊤ =
        (worITE (WellOrderingRel j i) (a j) ⊥)ᶜ := by
    intro j
    by_cases hj : WellOrderingRel j i
    · rw [worITE_pos hj, worITE_pos hj]
    · rw [worITE_neg hj, worITE_neg hj, compl_bot]
  simp_rw [h]
  rw [← compl_iSup]
  rfl

theorem worDisj_decomp {α : Type u} (a : α → A) (i : α) :
    a i = worDisj a i ⊔ (a i ⊓ worPredSup a i) := by
  unfold worDisj
  rw [worPred_compl, ← inf_sup_left, sup_comm, sup_compl_eq_top, inf_top_eq]

theorem worDisj_le_compl {α : Type u} (a : α → A) {i j : α}
    (hij : WellOrderingRel j i) : worDisj a i ≤ (a j)ᶜ := by
  refine inf_le_right.trans ?_
  have := iInf_le (fun k : α => worITE (WellOrderingRel k i) (a k)ᶜ ⊤) j
  rwa [worITE_pos hij] at this

theorem worDisj_pairwise {α : Type u} (a : α → A) :
    Pairwise fun i j : α => worDisj a i ⊓ worDisj a j = ⊥ := by
  intro i j hij
  apply bot_unique
  rcases trichotomous (r := WellOrderingRel) i j with h | h | h
  · have hi : worDisj a i ≤ a i := inf_le_left
    have hj : worDisj a j ≤ (a i)ᶜ := worDisj_le_compl a h
    exact (inf_le_inf hi hj).trans inf_compl_eq_bot.le
  · exact (hij h).elim
  · have hj : worDisj a j ≤ a j := inf_le_left
    have hi : worDisj a i ≤ (a j)ᶜ := worDisj_le_compl a h
    exact (inf_le_inf hi hj).trans <| by
      rw [inf_comm]
      exact inf_compl_eq_bot.le

theorem worDisj_iSup {α : Type u} (a : α → A) :
    (⨆ i, worDisj a i) = ⨆ i, a i := by
  refine le_antisymm (iSup_mono fun i => inf_le_left) (iSup_le fun i => ?_)
  refine WellOrderingRel.isWellOrder.wf.induction
    (C := fun i : α => a i ≤ ⨆ k, worDisj a k) i fun i ih => ?_
  have hdecomp := worDisj_decomp (A := A) a i
  have hpred : worPredSup a i ≤ ⨆ k, worDisj a k := by
    unfold worPredSup
    refine iSup_le fun j => ?_
    by_cases hj : WellOrderingRel j i
    · rw [worITE_pos hj]
      exact ih j hj
    · rw [worITE_neg hj]
      exact bot_le
  exact hdecomp.le.trans (sup_le (le_iSup (worDisj a) i)
    (hpred.trans' inf_le_right))

theorem inf_compl_congr {a d e : A} (h : a ⊓ d = a ⊓ e) : a ⊓ dᶜ = a ⊓ eᶜ := by
  have hd : a ⊓ dᶜ = a ⊓ (a ⊓ d)ᶜ := by
    rw [compl_inf, inf_sup_left, inf_compl_eq_bot, bot_sup_eq]
  have he : a ⊓ eᶜ = a ⊓ (a ⊓ e)ᶜ := by
    rw [compl_inf, inf_sup_left, inf_compl_eq_bot, bot_sup_eq]
  rw [hd, he, h]

theorem eqB_inf_child (X u : AName.{u} A) (i j : X.idx) :
    eqB u (X.child i) ⊓ eqB (X.child i) (X.child j) =
      eqB u (X.child i) ⊓ eqB u (X.child j) :=
  le_antisymm
    (le_inf inf_le_left (eqB_trans u (X.child i) (X.child j)))
    (le_inf inf_le_left ((eqB_trans (X.child i) u (X.child j)).trans'
      (le_inf (by rw [eqB_comm]; exact inf_le_left) inf_le_right)))

theorem leastIdx_eq_worDisj (X u : AName.{u} A) (i : X.idx) :
    leastIdx X u i =
      worDisj (fun j : X.idx => eqB u (X.child j) ⊓ X.val j) i := by
  unfold leastIdx canonVal worDisj
  let eu : A := eqB u (X.child i)
  have hpt (j : X.idx) :
      eu ⊓ worITE (WellOrderingRel j i)
          (eqB (X.child i) (X.child j) ⊓ X.val j)ᶜ ⊤ =
        eu ⊓ worITE (WellOrderingRel j i)
          (eqB u (X.child j) ⊓ X.val j)ᶜ ⊤ := by
    by_cases hj : WellOrderingRel j i
    · simp only [worITE_pos hj]
      refine inf_compl_congr ?_
      have heq := eqB_inf_child X u i j
      calc eu ⊓ (eqB (X.child i) (X.child j) ⊓ X.val j)
          = (eu ⊓ eqB (X.child i) (X.child j)) ⊓ X.val j := by ac_rfl
        _ = (eu ⊓ eqB u (X.child j)) ⊓ X.val j := by
            change (eqB u (X.child i) ⊓ eqB (X.child i) (X.child j)) ⊓ X.val j =
              (eqB u (X.child i) ⊓ eqB u (X.child j)) ⊓ X.val j
            rw [heq]
        _ = eu ⊓ (eqB u (X.child j) ⊓ X.val j) := by ac_rfl
    · simp [worITE_neg hj]
  have hinf :
      eu ⊓ ⨅ j : X.idx,
          worITE (WellOrderingRel j i)
            (eqB (X.child i) (X.child j) ⊓ X.val j)ᶜ ⊤ =
        eu ⊓ ⨅ j : X.idx,
          worITE (WellOrderingRel j i)
            (eqB u (X.child j) ⊓ X.val j)ᶜ ⊤ := by
    refine le_antisymm ?_ ?_
    · refine le_inf inf_le_left (le_iInf fun j => ?_)
      have hf := iInf_le (fun k : X.idx =>
        worITE (WellOrderingRel k i)
          (eqB (X.child i) (X.child k) ⊓ X.val k)ᶜ ⊤) j
      have := inf_le_inf_left eu hf
      rw [hpt j] at this
      exact this.trans inf_le_right
    · refine le_inf inf_le_left (le_iInf fun j => ?_)
      have hg := iInf_le (fun k : X.idx =>
        worITE (WellOrderingRel k i)
          (eqB u (X.child k) ⊓ X.val k)ᶜ ⊤) j
      have := inf_le_inf_left eu hg
      rw [← hpt j] at this
      exact this.trans inf_le_right
  change eu ⊓ (X.val i ⊓ ⨅ j : X.idx,
      worITE (WellOrderingRel j i)
        (eqB (X.child i) (X.child j) ⊓ X.val j)ᶜ ⊤) =
    (eu ⊓ X.val i) ⊓ ⨅ j : X.idx,
      worITE (WellOrderingRel j i)
        (eqB u (X.child j) ⊓ X.val j)ᶜ ⊤
  calc eu ⊓ (X.val i ⊓ ⨅ j : X.idx,
          worITE (WellOrderingRel j i)
            (eqB (X.child i) (X.child j) ⊓ X.val j)ᶜ ⊤)
      = X.val i ⊓ (eu ⊓ ⨅ j : X.idx,
          worITE (WellOrderingRel j i)
            (eqB (X.child i) (X.child j) ⊓ X.val j)ᶜ ⊤) := by ac_rfl
    _ = X.val i ⊓ (eu ⊓ ⨅ j : X.idx,
          worITE (WellOrderingRel j i)
            (eqB u (X.child j) ⊓ X.val j)ᶜ ⊤) := by rw [hinf]
    _ = (eu ⊓ X.val i) ⊓ ⨅ j : X.idx,
          worITE (WellOrderingRel j i)
            (eqB u (X.child j) ⊓ X.val j)ᶜ ⊤ := by ac_rfl

theorem leastIdx_iSup (X u : AName.{u} A) :
    (⨆ i : X.idx, leastIdx X u i) = memB u X := by
  simp_rw [leastIdx_eq_worDisj]
  rw [worDisj_iSup, memB_eq]

theorem memB_opairB_wellOrderB (u v X : AName.{u} A) :
    memB (opairB u v) (wellOrderB X) =
      ⨆ i : X.idx, ⨆ j : X.idx,
        leastIdx X u i ⊓ leastIdx X v j ⊓ worLe i j := by
  unfold wellOrderB
  rw [memB_mk, iSup_prod]
  refine iSup_congr fun i => iSup_congr fun j => ?_
  rw [eqB_opairB]
  unfold leastIdx
  ac_rfl

theorem leastIdx_unique (X u : AName.{u} A) (i j : X.idx) :
    leastIdx X u i ⊓ leastIdx X u j ≤ worITE (i = j) (⊤ : A) ⊥ := by
  by_cases hij : i = j
  · simp [worITE, hij]
  · simp only [worITE, hij, ↓reduceIte]
    rcases trichotomous (r := WellOrderingRel) i j with h | h | h
    · have hj := worDisj_le_compl
        (fun k : X.idx => eqB u (X.child k) ⊓ X.val k) h
      rw [← leastIdx_eq_worDisj] at hj
      have hi : leastIdx X u i ≤ eqB u (X.child i) ⊓ X.val i := by
        rw [leastIdx_eq_worDisj]; exact inf_le_left
      exact (inf_le_inf hi hj).trans inf_compl_eq_bot.le
    · exact (hij h).elim
    · have hi := worDisj_le_compl
        (fun k : X.idx => eqB u (X.child k) ⊓ X.val k) h
      rw [← leastIdx_eq_worDisj] at hi
      have hj : leastIdx X u j ≤ eqB u (X.child j) ⊓ X.val j := by
        rw [leastIdx_eq_worDisj]; exact inf_le_left
      exact (inf_le_inf hi hj).trans <| by
        rw [inf_comm]; exact inf_compl_eq_bot.le

theorem wellOrderB_relOn (X u v : AName.{u} A) :
    memB (opairB u v) (wellOrderB X) ≤ memB u X ⊓ memB v X := by
  rw [memB_opairB_wellOrderB]
  refine iSup_le fun i => iSup_le fun j => ?_
  have hu : leastIdx X u i ≤ memB u X :=
    (le_iSup (leastIdx X u) i).trans (leastIdx_iSup X u).le
  have hv : leastIdx X v j ≤ memB v X :=
    (le_iSup (leastIdx X v) j).trans (leastIdx_iSup X v).le
  exact le_inf (hu.trans' (inf_le_of_left_le inf_le_left))
    (hv.trans' (inf_le_of_left_le inf_le_right))

theorem wellOrderB_refl (X u : AName.{u} A) :
    memB u X ≤ memB (opairB u u) (wellOrderB X) := by
  rw [memB_opairB_wellOrderB, ← leastIdx_iSup]
  refine iSup_le fun i => le_iSup_of_le i (le_iSup_of_le i ?_)
  rw [worLe_refl, inf_top_eq, inf_idem]

theorem memB_opairB_wellOrderB_pair (u v X : AName.{u} A) :
    memB (opairB u v) (wellOrderB X) =
      ⨆ p : X.idx × X.idx,
        leastIdx X u p.1 ⊓ leastIdx X v p.2 ⊓ worLe p.1 p.2 := by
  rw [memB_opairB_wellOrderB]
  exact (iSup_prod (f := fun p : X.idx × X.idx =>
    leastIdx X u p.1 ⊓ leastIdx X v p.2 ⊓ worLe p.1 p.2)).symm

theorem inf_iSup_inf_iSup_pair {α : Type u} (f g : α → A) :
    (⨆ i : α, f i) ⊓ (⨆ j : α, g j) = ⨆ p : α × α, f p.1 ⊓ g p.2 := by
  refine le_antisymm ?_ ?_
  · have h := inf_iSup_eq (a := ⨆ i : α, f i) (f := g)
    rw [h]
    refine iSup_le fun j => ?_
    have h' := inf_iSup_eq (a := g j) (f := f)
    rw [inf_comm, h']
    refine iSup_le fun i => ?_
    rw [inf_comm]
    exact le_iSup (fun p : α × α => f p.1 ⊓ g p.2) (i, j)
  · refine iSup_le fun p => inf_le_inf (le_iSup f p.1) (le_iSup g p.2)

theorem inf_iSup_pair_le {α : Type u} (f g : α × α → A) :
    (⨆ p : α × α, f p) ⊓ (⨆ q : α × α, g q) ≤
      ⨆ p : α × α, ⨆ q : α × α, f p ⊓ g q := by
  have h := inf_iSup_eq (a := ⨆ p : α × α, f p) (f := g)
  rw [h]
  refine iSup_le fun q => ?_
  have h' := inf_iSup_eq (a := g q) (f := f)
  rw [inf_comm, h']
  refine iSup_le fun p => ?_
  rw [inf_comm]
  exact le_iSup_of_le p (le_iSup_of_le q le_rfl)

theorem leastIdx_le_eqB (X u : AName.{u} A) (i : X.idx) :
    leastIdx X u i ≤ eqB u (X.child i) := by
  rw [leastIdx_eq_worDisj]; exact inf_le_of_left_le inf_le_left

theorem leastIdx_le_val (X u : AName.{u} A) (i : X.idx) :
    leastIdx X u i ≤ X.val i := by
  rw [leastIdx_eq_worDisj]; exact inf_le_of_left_le inf_le_right

theorem leastIdx_child (X : AName.{u} A) (i : X.idx) :
    leastIdx X (X.child i) i = canonVal X i := by
  unfold leastIdx
  rw [eqB_self, top_inf_eq]

theorem leastIdx_eqB_same (X u v : AName.{u} A) (i : X.idx) :
    leastIdx X u i ⊓ leastIdx X v i ≤ eqB u v := by
  refine (inf_le_inf (leastIdx_le_eqB X u i) (leastIdx_le_eqB X v i)).trans ?_
  rw [eqB_comm (x := v) (y := X.child i)]
  exact eqB_trans u (X.child i) v

theorem wellOrderB_antisym (X u v : AName.{u} A) :
    memB (opairB u v) (wellOrderB X) ⊓ memB (opairB v u) (wellOrderB X) ≤
      eqB u v := by
  rw [memB_opairB_wellOrderB_pair, memB_opairB_wellOrderB_pair]
  refine (inf_iSup_pair_le _ _).trans ?_
  refine iSup_le fun p => iSup_le fun q => ?_
  by_cases hil : p.1 = q.2
  · by_cases hjk : p.2 = q.1
    · by_cases hij : p.1 = p.2
      · refine (le_inf ?hu ?hv).trans (leastIdx_eqB_same X u v p.1)
        · exact inf_le_of_left_le (inf_le_of_left_le inf_le_left)
        · rw [← hij]
          exact inf_le_of_left_le (inf_le_of_left_le inf_le_right)
      · have hbot := worLe_antisymm (A := A) p.1 p.2
        simp only [worITE, hij, ↓reduceIte] at hbot
        refine (hbot.trans' (le_inf ?_ ?_)).trans bot_le
        · exact inf_le_of_left_le inf_le_right
        · have hle : leastIdx X v q.1 ⊓ leastIdx X u q.2 ⊓ worLe q.1 q.2 ≤
              worLe p.2 p.1 := by
            rw [hjk, hil]; exact inf_le_right
          exact hle.trans' inf_le_right
    · have hbot := leastIdx_unique X v p.2 q.1
      simp only [worITE, hjk, ↓reduceIte] at hbot
      refine (hbot.trans' (le_inf ?_ ?_)).trans bot_le
      · exact inf_le_of_left_le (inf_le_of_left_le inf_le_right)
      · exact inf_le_of_right_le (inf_le_of_left_le inf_le_left)
  · have hbot := leastIdx_unique X u p.1 q.2
    simp only [worITE, hil, ↓reduceIte] at hbot
    refine (hbot.trans' (le_inf ?_ ?_)).trans bot_le
    · exact inf_le_of_left_le (inf_le_of_left_le inf_le_left)
    · exact inf_le_of_right_le (inf_le_of_left_le inf_le_right)

theorem wellOrderB_total (X u v : AName.{u} A) :
    memB u X ⊓ memB v X ≤
      memB (opairB u v) (wellOrderB X) ⊔ memB (opairB v u) (wellOrderB X) := by
  rw [← leastIdx_iSup (X := X) (u := u), ← leastIdx_iSup (X := X) (u := v)]
  rw [inf_iSup_inf_iSup_pair, memB_opairB_wellOrderB_pair,
    memB_opairB_wellOrderB_pair]
  refine iSup_le fun p => ?_
  have hsplit :
      leastIdx X u p.1 ⊓ leastIdx X v p.2 =
        (leastIdx X u p.1 ⊓ leastIdx X v p.2 ⊓ worLe p.1 p.2) ⊔
          (leastIdx X u p.1 ⊓ leastIdx X v p.2 ⊓ worLe p.2 p.1) := by
    rw [← inf_sup_left, worLe_total, inf_top_eq]
  rw [hsplit]
  refine sup_le ?_ ?_
  · exact le_sup_of_le_left (le_iSup (fun q : X.idx × X.idx =>
      leastIdx X u q.1 ⊓ leastIdx X v q.2 ⊓ worLe q.1 q.2) p)
  · refine le_sup_of_le_right
      ((le_iSup (fun q : X.idx × X.idx =>
        leastIdx X v q.1 ⊓ leastIdx X u q.2 ⊓ worLe q.1 q.2) (p.2, p.1)).trans' ?_)
    exact le_inf
      (le_inf (inf_le_of_left_le inf_le_right) (inf_le_of_left_le inf_le_left))
      inf_le_right

theorem wellOrderB_trans (X u v w : AName.{u} A) :
    memB (opairB u v) (wellOrderB X) ⊓ memB (opairB v w) (wellOrderB X) ≤
      memB (opairB u w) (wellOrderB X) := by
  rw [memB_opairB_wellOrderB_pair, memB_opairB_wellOrderB_pair,
    memB_opairB_wellOrderB_pair]
  refine (inf_iSup_pair_le _ _).trans ?_
  refine iSup_le fun p => iSup_le fun q => ?_
  by_cases hjk : p.2 = q.1
  · refine (le_iSup (fun r : X.idx × X.idx =>
        leastIdx X u r.1 ⊓ leastIdx X w r.2 ⊓ worLe r.1 r.2)
        (p.1, q.2)).trans' ?_
    refine le_inf ?_ ?_
    · exact le_inf (inf_le_of_left_le (inf_le_of_left_le inf_le_left))
        (inf_le_of_right_le (inf_le_of_left_le inf_le_right))
    · refine (worLe_trans (A := A) p.1 p.2 q.2).trans' ?_
      refine le_inf (inf_le_of_left_le inf_le_right) ?_
      have hle : leastIdx X v q.1 ⊓ leastIdx X w q.2 ⊓ worLe q.1 q.2 ≤
          worLe p.2 q.2 := by
        rw [hjk]; exact inf_le_right
      exact hle.trans' inf_le_right
  · have hbot := leastIdx_unique X v p.2 q.1
    simp only [worITE, hjk, ↓reduceIte] at hbot
    exact (hbot.trans' (le_inf
      (inf_le_of_left_le (inf_le_of_left_le inf_le_right))
      (inf_le_of_right_le (inf_le_of_left_le inf_le_left)))).trans bot_le

theorem subset_nonempty_le_childMemY (X Y : AName.{u} A) :
    subsetB Y X ⊓ ⨆ z, memB z Y ≤
      ⨆ i : X.idx, memB (X.child i) Y ⊓ X.val i := by
  have h := inf_iSup_eq (a := subsetB Y X) (f := fun z : AName.{u} A => memB z Y)
  rw [h]
  refine iSup_le fun z => ?_
  have hz : subsetB Y X ⊓ memB z Y ≤ memB z Y ⊓ memB z X :=
    le_inf inf_le_right (by rw [inf_comm]; exact memB_of_subsetB z Y X)
  refine hz.trans ?_
  have hx := memB_eq (x := z) (y := X)
  rw [hx]
  have h' := inf_iSup_eq (a := memB z Y)
    (f := fun i : X.idx => eqB z (X.child i) ⊓ X.val i)
  rw [h']
  refine iSup_le fun i => ?_
  refine (le_iSup (fun j : X.idx => memB (X.child j) Y ⊓ X.val j) i).trans' ?_
  have heq : memB z Y ⊓ eqB z (X.child i) ≤ memB (X.child i) Y :=
    memB_eqB_left z Y (X.child i)
  refine le_inf ?_ ?_
  · exact heq.trans' (le_inf inf_le_left (inf_le_of_right_le inf_le_left))
  · exact inf_le_of_right_le inf_le_right

theorem worDisj_childMemY_le_canonVal (X Y : AName.{u} A) (i : X.idx) :
    worDisj (fun j : X.idx => memB (X.child j) Y ⊓ X.val j) i ≤
      canonVal X i := by
  set a := fun j : X.idx => memB (X.child j) Y ⊓ X.val j
  refine le_inf (inf_le_of_left_le inf_le_right) (le_iInf fun j => ?_)
  by_cases hj : WellOrderingRel j i
  · rw [worITE_pos hj]
    refine le_compl_iff_disjoint_right.mpr (disjoint_iff.mpr (bot_unique ?_))
    have hdj : worDisj a i ≤ (a j)ᶜ := worDisj_le_compl a hj
    have hmem : worDisj a i ⊓ eqB (X.child i) (X.child j) ≤
        memB (X.child j) Y := by
      have hai : worDisj a i ≤ memB (X.child i) Y :=
        inf_le_of_left_le inf_le_left
      exact (memB_eqB_left (X.child i) Y (X.child j)).trans'
        (le_inf (hai.trans' inf_le_left) inf_le_right)
    have : worDisj a i ⊓ (eqB (X.child i) (X.child j) ⊓ X.val j) ≤
        a j ⊓ (a j)ᶜ :=
      le_inf
        (le_inf (hmem.trans' (le_inf inf_le_left (inf_le_of_right_le inf_le_left)))
          (inf_le_of_right_le inf_le_right))
        (hdj.trans' inf_le_left)
    exact this.trans inf_compl_eq_bot.le
  · rw [worITE_neg hj]
    exact le_top

theorem worDisj_childMemY_le_leastIdx (X Y : AName.{u} A) (i : X.idx) :
    worDisj (fun j : X.idx => memB (X.child j) Y ⊓ X.val j) i ≤
      leastIdx X (X.child i) i := by
  rw [leastIdx_child]
  exact worDisj_childMemY_le_canonVal X Y i

theorem wellOrderB_least_mem (X Y : AName.{u} A) (i : X.idx) (y : AName.{u} A) :
    subsetB Y X ⊓
      worDisj (fun j : X.idx => memB (X.child j) Y ⊓ X.val j) i ⊓
      memB y Y ≤
      memB (opairB (X.child i) y) (wellOrderB X) := by
  set a := fun j : X.idx => memB (X.child j) Y ⊓ X.val j
  have hyX : subsetB Y X ⊓ memB y Y ≤ memB y X := by
    rw [inf_comm]; exact memB_of_subsetB y Y X
  have hreduce :
      subsetB Y X ⊓ worDisj a i ⊓ memB y Y ≤
        worDisj a i ⊓ memB y Y ⊓ memB y X :=
    le_inf
      (le_inf (inf_le_of_left_le inf_le_right) inf_le_right)
      (hyX.trans' (le_inf (inf_le_of_left_le inf_le_left) inf_le_right))
  rw [memB_opairB_wellOrderB_pair]
  refine hreduce.trans ?_
  rw [← leastIdx_iSup (X := X) (u := y)]
  have hdist := inf_iSup_eq (a := worDisj a i ⊓ memB y Y)
    (f := fun k : X.idx => leastIdx X y k)
  rw [hdist]
  refine iSup_le fun k => ?_
  by_cases hle : WellOrderingRel i k ∨ i = k
  · have hwor : worLe (A := A) i k = ⊤ := worITE_pos hle
    refine le_iSup_of_le (i, k) ?_
    rw [hwor, inf_top_eq]
    refine le_inf ?_ inf_le_right
    exact (worDisj_childMemY_le_leastIdx X Y i).trans'
      (inf_le_of_left_le inf_le_left)
  · have hlt : WellOrderingRel k i := by
      rcases trichotomous (r := WellOrderingRel) i k with h | h | h
      · exact (hle (Or.inl h)).elim
      · exact (hle (Or.inr h)).elim
      · exact h
    have h_ak : memB y Y ⊓ leastIdx X y k ≤ a k :=
      le_inf
        ((memB_eqB_left y Y (X.child k)).trans'
          (le_inf inf_le_left ((leastIdx_le_eqB X y k).trans' inf_le_right)))
        ((leastIdx_le_val X y k).trans' inf_le_right)
    have hbot : worDisj a i ⊓ memB y Y ⊓ leastIdx X y k ≤ ⊥ := by
      have : worDisj a i ⊓ memB y Y ⊓ leastIdx X y k ≤ (a k)ᶜ ⊓ a k :=
        le_inf
          ((worDisj_le_compl a hlt).trans' (inf_le_of_left_le inf_le_left))
          (h_ak.trans' (le_inf (inf_le_of_left_le inf_le_right) inf_le_right))
      exact this.trans (by rw [inf_comm]; exact inf_compl_eq_bot.le)
    exact hbot.trans bot_le

theorem wellOrderB_least_at (X Y : AName.{u} A) (i : X.idx) :
    subsetB Y X ⊓
      worDisj (fun j : X.idx => memB (X.child j) Y ⊓ X.val j) i ≤
      memB (X.child i) Y ⊓
        ⨅ y, memB y Y ⇨ memB (opairB (X.child i) y) (wellOrderB X) :=
  le_inf
    (inf_le_of_right_le (inf_le_of_left_le inf_le_left))
    (le_iInf fun y => le_himp_iff.mpr (wellOrderB_least_mem X Y i y))

theorem wellOrderB_least (X Y : AName.{u} A) :
    subsetB Y X ⊓ ⨆ z, memB z Y ≤
      ⨆ m, memB m Y ⊓
        ⨅ y, memB y Y ⇨ memB (opairB m y) (wellOrderB X) := by
  set a := fun j : X.idx => memB (X.child j) Y ⊓ X.val j
  have hchild := subset_nonempty_le_childMemY (A := A) X Y
  rw [← worDisj_iSup a] at hchild
  have hsub : subsetB Y X ⊓ ⨆ z, memB z Y ≤ subsetB Y X ⊓ ⨆ i, worDisj a i :=
    le_inf inf_le_left hchild
  have hdist := inf_iSup_eq (a := subsetB Y X) (f := worDisj a)
  rw [hdist] at hsub
  refine hsub.trans (iSup_le fun i => ?_)
  refine (le_iSup (fun m : AName.{u} A =>
      memB m Y ⊓ ⨅ y, memB y Y ⇨ memB (opairB m y) (wellOrderB X))
      (X.child i)).trans' ?_
  exact wellOrderB_least_at X Y i

theorem wellOrderB_satisfies (X : AName.{u} A) (ρ : Fin 0 → AName.{u} A) :
    bval wellOrderAxiom (consName (wellOrderB X) (consName X ρ)) = ⊤ := by
  unfold wellOrderAxiom
  simp only [SetFormula.bval_and]
  refine inf_eq_top_iff.mpr ⟨?relOn, inf_eq_top_iff.mpr ⟨?refl,
    inf_eq_top_iff.mpr ⟨?antisym, inf_eq_top_iff.mpr ⟨?total,
      inf_eq_top_iff.mpr ⟨?trans, ?least⟩⟩⟩⟩⟩
  · refine iInf_eq_top.mpr fun u => iInf_eq_top.mpr fun v => ?_
    rw [SetFormula.bval_implies, himp_eq_top_iff]
    have hu : consName v (consName u (consName (wellOrderB X) (consName X ρ)))
        (1 : Fin 4) = u := rfl
    have hv : consName v (consName u (consName (wellOrderB X) (consName X ρ)))
        (0 : Fin 4) = v := rfl
    have hR : consName v (consName u (consName (wellOrderB X) (consName X ρ)))
        (2 : Fin 4) = wellOrderB X := rfl
    have hX : consName v (consName u (consName (wellOrderB X) (consName X ρ)))
        (3 : Fin 4) = X := rfl
    simp only [SetFormula.bval_and, SetFormula.bval_mem, bval_opairMemF,
      hu, hv, hR, hX]
    exact wellOrderB_relOn X u v
  · refine iInf_eq_top.mpr fun u => ?_
    rw [SetFormula.bval_implies, himp_eq_top_iff]
    have hu : consName u (consName (wellOrderB X) (consName X ρ))
        (0 : Fin 3) = u := rfl
    have hR : consName u (consName (wellOrderB X) (consName X ρ))
        (1 : Fin 3) = wellOrderB X := rfl
    have hX : consName u (consName (wellOrderB X) (consName X ρ))
        (2 : Fin 3) = X := rfl
    simp only [SetFormula.bval_mem, bval_opairMemF, hu, hR, hX]
    exact wellOrderB_refl X u
  · refine iInf_eq_top.mpr fun u => iInf_eq_top.mpr fun v => ?_
    rw [SetFormula.bval_implies, himp_eq_top_iff]
    have hu : consName v (consName u (consName (wellOrderB X) (consName X ρ)))
        (1 : Fin 4) = u := rfl
    have hv : consName v (consName u (consName (wellOrderB X) (consName X ρ)))
        (0 : Fin 4) = v := rfl
    have hR : consName v (consName u (consName (wellOrderB X) (consName X ρ)))
        (2 : Fin 4) = wellOrderB X := rfl
    simp only [SetFormula.bval_and, SetFormula.bval_eq, bval_opairMemF,
      hu, hv, hR]
    exact wellOrderB_antisym X u v
  · refine iInf_eq_top.mpr fun u => iInf_eq_top.mpr fun v => ?_
    rw [SetFormula.bval_implies, himp_eq_top_iff]
    have hu : consName v (consName u (consName (wellOrderB X) (consName X ρ)))
        (1 : Fin 4) = u := rfl
    have hv : consName v (consName u (consName (wellOrderB X) (consName X ρ)))
        (0 : Fin 4) = v := rfl
    have hR : consName v (consName u (consName (wellOrderB X) (consName X ρ)))
        (2 : Fin 4) = wellOrderB X := rfl
    have hX : consName v (consName u (consName (wellOrderB X) (consName X ρ)))
        (3 : Fin 4) = X := rfl
    simp only [SetFormula.bval_and, SetFormula.bval_or, SetFormula.bval_mem,
      bval_opairMemF, hu, hv, hR, hX]
    exact wellOrderB_total X u v
  · refine iInf_eq_top.mpr fun u => iInf_eq_top.mpr fun v =>
      iInf_eq_top.mpr fun w => ?_
    rw [SetFormula.bval_implies, himp_eq_top_iff]
    have hu : consName w (consName v (consName u
        (consName (wellOrderB X) (consName X ρ)))) (2 : Fin 5) = u := rfl
    have hv : consName w (consName v (consName u
        (consName (wellOrderB X) (consName X ρ)))) (1 : Fin 5) = v := rfl
    have hw : consName w (consName v (consName u
        (consName (wellOrderB X) (consName X ρ)))) (0 : Fin 5) = w := rfl
    have hR : consName w (consName v (consName u
        (consName (wellOrderB X) (consName X ρ)))) (3 : Fin 5) =
      wellOrderB X := rfl
    simp only [SetFormula.bval_and, bval_opairMemF, hu, hv, hw, hR]
    exact wellOrderB_trans X u v w
  · refine iInf_eq_top.mpr fun Y => ?_
    rw [SetFormula.bval_implies, himp_eq_top_iff]
    have hY : consName Y (consName (wellOrderB X) (consName X ρ))
        (0 : Fin 3) = Y := rfl
    have hR : consName Y (consName (wellOrderB X) (consName X ρ))
        (1 : Fin 3) = wellOrderB X := rfl
    have hX : consName Y (consName (wellOrderB X) (consName X ρ))
        (2 : Fin 3) = X := rfl
    have hsub :
        SetFormula.bval (.all (implies (.mem 0 1) (.mem 0 3)))
          (consName Y (consName (wellOrderB X) (consName X ρ))) =
          subsetB Y X := by
      rw [subsetB_eq_iInf]
      refine iInf_congr fun z => ?_
      have hz0 : consName z (consName Y (consName (wellOrderB X) (consName X ρ)))
          (0 : Fin 4) = z := rfl
      have hz1 : consName z (consName Y (consName (wellOrderB X) (consName X ρ)))
          (1 : Fin 4) = Y := rfl
      have hz3 : consName z (consName Y (consName (wellOrderB X) (consName X ρ)))
          (3 : Fin 4) = X := rfl
      simp [SetFormula.bval_implies, SetFormula.bval_mem, hz0, hz1, hz3]
    have hne :
        SetFormula.bval (.ex (.mem 0 1))
          (consName Y (consName (wellOrderB X) (consName X ρ))) =
          ⨆ z, memB z Y := by
      refine iSup_congr fun z => ?_
      have hz0 : consName z (consName Y (consName (wellOrderB X) (consName X ρ)))
          (0 : Fin 4) = z := rfl
      have hz1 : consName z (consName Y (consName (wellOrderB X) (consName X ρ)))
          (1 : Fin 4) = Y := rfl
      simp [SetFormula.bval_mem, hz0, hz1]
    have hrhs :
        SetFormula.bval
          (.ex (.and (.mem 0 1)
            (.all (implies (.mem 0 2) (opairMemF 1 0 3)))))
          (consName Y (consName (wellOrderB X) (consName X ρ))) =
          ⨆ m, memB m Y ⊓
            ⨅ y, memB y Y ⇨ memB (opairB m y) (wellOrderB X) := by
      refine iSup_congr fun m => ?_
      have hm0 : consName m (consName Y (consName (wellOrderB X) (consName X ρ)))
          (0 : Fin 4) = m := rfl
      have hm1 : consName m (consName Y (consName (wellOrderB X) (consName X ρ)))
          (1 : Fin 4) = Y := rfl
      simp only [SetFormula.bval_and, SetFormula.bval_mem, SetFormula.bval_all,
        SetFormula.bval_implies, hm0, hm1]
      refine congrArg (fun t => memB m Y ⊓ t) (iInf_congr fun y => ?_)
      have hy0 : consName y (consName m
          (consName Y (consName (wellOrderB X) (consName X ρ))))
          (0 : Fin 5) = y := rfl
      have hy1 : consName y (consName m
          (consName Y (consName (wellOrderB X) (consName X ρ))))
          (1 : Fin 5) = m := rfl
      have hy2 : consName y (consName m
          (consName Y (consName (wellOrderB X) (consName X ρ))))
          (2 : Fin 5) = Y := rfl
      have hy3 : consName y (consName m
          (consName Y (consName (wellOrderB X) (consName X ρ))))
          (3 : Fin 5) = wellOrderB X := rfl
      simp [bval_opairMemF, hy0, hy1, hy2, hy3]
    simp only [SetFormula.bval_and]
    rw [hsub, hne, hrhs]
    exact wellOrderB_least X Y

/-- Jech 14.27: every name is well-orderable in `V^A`. -/
theorem axiom_choice_valid (ρ : Fin 0 → AName.{u} A) :
    bval choiceAxiom ρ = ⊤ := by
  unfold choiceAxiom
  rw [all_valid_iff]
  intro X
  exact bval_ex_eq_top_of (wellOrderB X) (wellOrderB_satisfies X ρ)

theorem zfcAxiom_valid {n : ℕ} {φ : SetFormula n} (h : ZFCAxiom φ)
    (ρ : Fin n → AName.{u} A) : bval φ ρ = ⊤ := by
  cases h with
  | extensionality => exact axiom_extensionality_valid ρ
  | pairing => exact axiom_pairing_valid ρ
  | union => exact axiom_union_valid ρ
  | power => exact axiom_power_valid ρ
  | infinity => exact axiom_infinity_valid ρ
  | regularity => exact axiom_regularity_valid ρ
  | choice => exact axiom_choice_valid ρ
  | separation φ => exact axiom_separation_valid φ ρ
  | collection φ => exact axiom_collection_valid φ ρ

/-- CSL Theorem 1(i): a ZFC theorem has Boolean value `1` at every
assignment in `V^A`. -/
theorem theorem_1_i {n : ℕ} (φ : SetFormula n) (h : ZFCProvable φ)
    (ρ : Fin n → AName.{u} A) : bval φ ρ = ⊤ := by
  refine h.rec
    (motive := fun {n} (φ : SetFormula n) _ =>
      ∀ ρ : Fin n → AName.{u} A, bval φ ρ = ⊤)
    ?ax ?mp ?gen ?hilbertK ?hilbertS ?hilbertDNE ?allImp ?allVac ?allInst
    ?eqRefl ?eqLeibniz ρ
  · intro n φ hax ρ; exact zfcAxiom_valid hax ρ
  · intro n φ ψ _ _ ihimp ihφ ρ
    exact mp_valid φ ψ ρ (ihimp ρ) (ihφ ρ)
  · intro n φ _ ih ρ
    rw [all_valid_iff]
    exact fun x => ih (consName x ρ)
  · intro n φ ψ ρ; exact hilbertK_sound φ ψ ρ
  · intro n φ ψ χ ρ; exact hilbertS_sound φ ψ χ ρ
  · intro n φ ψ ρ; exact hilbertDNE_sound φ ψ ρ
  · intro n φ ψ ρ; exact allImp_sound φ ψ ρ
  · intro n φ ψ ρ; exact allVac_sound φ ψ ρ
  · intro n φ t ρ; exact allInst_sound φ t ρ
  · intro n ρ
    rw [SetFormula.bval_all]
    refine iInf_eq_top.mpr fun x => ?_
    simp [SetFormula.bval_eq, consName, eqB_self]
  · intro n φ ρ; exact eqLeibniz_sound φ ρ

end Scott2026
