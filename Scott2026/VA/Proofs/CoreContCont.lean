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

namespace Scott2026

universe u

variable {A : Type u}
variable [CompleteBooleanAlgebra A]

open AName

theorem isFunctionB_subset {F X Y : AName.{u} A} (h : isFunctionB F X Y = ⊤) :
    subsetB F (prodB X Y) = ⊤ :=
  (inf_eq_top_iff.mp (inf_eq_top_iff.mp h).1).1

theorem isFunctionB_single {F X Y : AName.{u} A} (h : isFunctionB F X Y = ⊤) :
    isSingleValuedB F = ⊤ :=
  (inf_eq_top_iff.mp (inf_eq_top_iff.mp h).1).2

theorem isFunctionB_total {F X Y : AName.{u} A} (h : isFunctionB F X Y = ⊤) :
    isTotalB F X = ⊤ :=
  (inf_eq_top_iff.mp h).2

theorem isFunctionB_comp {X Y Z f g : AName.{u} A}
    (hf : isFunctionB f X Y = ⊤) (hg : isFunctionB g Y Z = ⊤) :
    isFunctionB (compB g f X Z) X Z = ⊤ := by
  unfold isFunctionB
  refine inf_eq_top_iff.mpr ⟨inf_eq_top_iff.mpr ⟨?sub, ?sv⟩, ?tot⟩
  · unfold compB
    rw [subsetB_mk]
    refine iInf_eq_top.mpr fun p => himp_eq_top_iff.mpr ?_
    refine iSup_le fun y => ?_
    have hfmem : memB (opairB (X.child p.1) y) f ≤
        memB (X.child p.1) X ⊓ memB y Y := by
      have := memB_of_subsetB (opairB (X.child p.1) y) f (prodB X Y)
      rwa [isFunctionB_subset hf, inf_top_eq, memB_opairB_prodB] at this
    have hgmem : memB (opairB y (Z.child p.2)) g ≤
        memB y Y ⊓ memB (Z.child p.2) Z := by
      have := memB_of_subsetB (opairB y (Z.child p.2)) g (prodB Y Z)
      rwa [isFunctionB_subset hg, inf_top_eq, memB_opairB_prodB] at this
    rw [memB_opairB_prodB]
    exact le_inf (inf_le_of_left_le (hfmem.trans inf_le_left))
      (inf_le_of_right_le (hgmem.trans inf_le_right))
  · refine iInf_eq_top.mpr fun x => iInf_eq_top.mpr fun z1 =>
      iInf_eq_top.mpr fun z2 => himp_eq_top_iff.mpr ?_
    have hle1 := memB_opairB_compB_le (A := A) g f X Z x z1
    have hle2 := memB_opairB_compB_le (A := A) g f X Z x z2
    have hsvf : ∀ y1 y2 : AName A,
        memB (opairB x y1) f ⊓ memB (opairB x y2) f ≤ eqB y1 y2 := fun y1 y2 =>
      (isSingleValuedB_apply f x y1 y2).trans'
        (le_inf (le_inf (le_top.trans (isFunctionB_single hf).ge) inf_le_left) inf_le_right)
    have hsvg : ∀ y z1' z2' : AName A,
        memB (opairB y z1') g ⊓ memB (opairB y z2') g ≤ eqB z1' z2' := fun y z1' z2' =>
      (isSingleValuedB_apply g y z1' z2').trans'
        (le_inf (le_inf (le_top.trans (isFunctionB_single hg).ge) inf_le_left) inf_le_right)
    refine (inf_le_inf hle1 hle2).trans ?_
    rw [iSup_inf_eq]
    refine iSup_le fun y1 => ?_
    rw [inf_iSup_eq]
    refine iSup_le fun y2 => ?_
    have hy : memB (opairB x y1) f ⊓ memB (opairB x y2) f ≤ eqB y1 y2 := hsvf y1 y2
    have hsubst : eqB y1 y2 ⊓ memB (opairB y2 z2) g ≤ memB (opairB y1 z2) g := by
      have heq : eqB (opairB y1 z2) (opairB y2 z2) = eqB y1 y2 := by
        rw [eqB_opairB, eqB_self (A := A) z2, inf_top_eq]
      rw [← heq]
      exact memB_eqB_left' (opairB y2 z2) g (opairB y1 z2)
    have hgpair : memB (opairB y1 z1) g ⊓ memB (opairB y1 z2) g ≤ eqB z1 z2 :=
      hsvg y1 z1 z2
    have hproj :
        memB (opairB x y1) f ⊓ memB (opairB y1 z1) g ⊓
          (memB (opairB x y2) f ⊓ memB (opairB y2 z2) g) ≤
        memB (opairB y1 z1) g ⊓ memB (opairB y1 z2) g := by
      refine le_inf (inf_le_of_left_le inf_le_right) ?_
      refine hsubst.trans' ?_
      refine le_inf ?_ (inf_le_of_right_le inf_le_right)
      exact hy.trans' (le_inf (inf_le_of_left_le inf_le_left) (inf_le_of_right_le inf_le_left))
    exact hgpair.trans' hproj
  · refine iInf_eq_top.mpr fun x => himp_eq_top_iff.mpr ?_
    have hftot : memB x X ≤ ⨆ y : AName A, memB (opairB x y) f :=
      (isTotalB_apply f X x).trans' (le_inf (le_top.trans (isFunctionB_total hf).ge) le_rfl)
    refine hftot.trans ?_
    refine iSup_le fun y => ?_
    have hyY : memB (opairB x y) f ≤ memB y Y := by
      have := memB_of_subsetB (opairB x y) f (prodB X Y)
      have h := this.trans (le_of_eq (by rw [memB_opairB_prodB]))
      exact (h.trans' (le_inf le_rfl (le_top.trans (isFunctionB_subset hf).ge))).trans
        inf_le_right
    have hgtot : memB y Y ≤ ⨆ z : AName A, memB (opairB y z) g :=
      (isTotalB_apply g Y y).trans' (le_inf (le_top.trans (isFunctionB_total hg).ge) le_rfl)
    have : memB (opairB x y) f ≤ memB (opairB x y) f ⊓ memB y Y :=
      le_inf le_rfl hyY
    refine this.trans ?_
    refine (inf_le_inf_left _ hgtot).trans ?_
    rw [inf_iSup_eq]
    refine iSup_le fun z => ?_
    refine (le_memB_opairB_compB (A := A) g f X Y Z x y z
      (isFunctionB_subset hf) (isFunctionB_subset hg)).trans ?_
    exact le_iSup (fun z' : AName A => memB (opairB x z') (compB g f X Z)) z

theorem compB_congr {X Z f f' g g' : AName.{u} A}
    (hf : eqB f f' = ⊤) (hg : eqB g g' = ⊤) :
    eqB (compB g f X Z) (compB g' f' X Z) = ⊤ := by
  have hval : (fun p : X.idx × Z.idx =>
      ⨆ y : AName A, memB (opairB (X.child p.1) y) f ⊓
        memB (opairB y (Z.child p.2)) g) =
      fun p => ⨆ y : AName A, memB (opairB (X.child p.1) y) f' ⊓
        memB (opairB y (Z.child p.2)) g' := by
    funext p
    refine iSup_congr fun y => ?_
    rw [eqB_top_memB_right (x := f) (y := f') (z := opairB (X.child p.1) y) hf,
      eqB_top_memB_right (x := g) (y := g') (z := opairB y (Z.child p.2)) hg]
  have heq : compB g f X Z = compB g' f' X Z := by
    unfold compB
    exact congr_arg (fun v => mk (X.idx × Z.idx)
      (fun p => opairB (X.child p.1) (Z.child p.2)) v) hval
  rw [heq, eqB_self]

theorem isHom_id (X : AName.{u} A) : memB (idB X) (funsB X X) = ⊤ :=
  memB_idB_funsB X

theorem isHom_comp {X Y Z f g : AName.{u} A}
    (hf : memB f (funsB X Y) = ⊤) (hg : memB g (funsB Y Z) = ⊤) :
    memB (compB g f X Z) (funsB X Z) = ⊤ := by
  rw [memB_funsB] at hf hg ⊢
  exact isFunctionB_comp hf hg

/-!
## `𝔏_Set(V^A)` and CSL Theorem 1(i)–(ii)

The paper's language of set theory with constants from `V^A` is the first-order
language with `∈` and `=` , evaluated at an assignment of `A`-names. Bounded
`Δ₀` formulas remain `D0Formula`. Unbounded quantifiers are `SetFormula.ex`
and `SetFormula.all`, interpreted as joins and meets (CSL §2).
-/

namespace SetFormula

variable {A : Type u} [CompleteBooleanAlgebra A]

open D0Formula AName

@[simp] theorem bval_not {n} (φ : SetFormula n) (ρ : Fin n → AName.{u} A) :
    bval (.not φ) ρ = (bval φ ρ)ᶜ := rfl
@[simp] theorem bval_and {n} (φ ψ : SetFormula n) (ρ : Fin n → AName.{u} A) :
    bval (.and φ ψ) ρ = bval φ ρ ⊓ bval ψ ρ := rfl
@[simp] theorem bval_ex {n} (φ : SetFormula (n + 1)) (ρ : Fin n → AName.{u} A) :
    bval (.ex φ) ρ = ⨆ x : AName.{u} A, bval φ (consName x ρ) := rfl
@[simp] theorem bval_all {n} (φ : SetFormula (n + 1)) (ρ : Fin n → AName.{u} A) :
    bval (.all φ) ρ = ⨅ x : AName.{u} A, bval φ (consName x ρ) := rfl
@[simp] theorem bval_mem {n} (i j : Fin n) (ρ : Fin n → AName.{u} A) :
    bval (.mem i j) ρ = memB (ρ i) (ρ j) := rfl
@[simp] theorem bval_eq {n} (i j : Fin n) (ρ : Fin n → AName.{u} A) :
    bval (.eq i j) ρ = eqB (ρ i) (ρ j) := rfl

theorem bval_or {n} (φ ψ : SetFormula n) (ρ : Fin n → AName.{u} A) :
    bval (or φ ψ) ρ = bval φ ρ ⊔ bval ψ ρ := by
  simp [or, compl_inf, compl_compl]

theorem bval_implies {n} (φ ψ : SetFormula n) (ρ : Fin n → AName.{u} A) :
    bval (implies φ ψ) ρ = bval φ ρ ⇨ bval ψ ρ := by
  rw [implies, bval_or, bval_not, himp_eq, sup_comm]

theorem bval_iff {n} (φ ψ : SetFormula n) (ρ : Fin n → AName.{u} A) :
    bval (iff φ ψ) ρ = (bval φ ρ ⇨ bval ψ ρ) ⊓ (bval ψ ρ ⇨ bval φ ρ) := by
  simp [iff, bval_implies]

theorem bval_rename {n m} (σ : Fin n → Fin m) (φ : SetFormula n)
    (ρ : Fin m → AName.{u} A) :
    bval (rename σ φ) ρ = bval φ (fun i => ρ (σ i)) := by
  induction φ generalizing m ρ with
  | mem i j => rfl
  | eq i j => rfl
  | not φ ih => simp [rename, ih]
  | and φ ψ ihφ ihψ => simp [rename, ihφ, ihψ]
  | ex φ ih =>
    simp only [rename, bval_ex]
    refine iSup_congr fun x => ?_
    rw [ih]
    congr 1
    funext i
    exact Fin.cases (by simp [consName]) (fun i => by simp [consName]) i
  | all φ ih =>
    simp only [rename, bval_all]
    refine iInf_congr fun x => ?_
    rw [ih]
    congr 1
    funext i
    exact Fin.cases (by simp [consName]) (fun i => by simp [consName]) i

theorem bval_lift {n} (φ : SetFormula n) (x : AName.{u} A)
    (ρ : Fin n → AName.{u} A) :
    bval (lift φ) (consName x ρ) = bval φ ρ := by
  simp [lift, bval_rename, consName]

theorem bval_inst {n} (φ : SetFormula (n + 1)) (t : Fin n)
    (ρ : Fin n → AName.{u} A) :
    bval (inst φ t) ρ = bval φ (consName (ρ t) ρ) := by
  simp [inst, bval_rename]
  congr 1
  funext i
  exact Fin.cases (by simp [consName]) (fun i => by simp [consName]) i

/-- Equality of names is a congruence for Boolean values of `𝔏_Set` formulas. -/
theorem bval_congr {n : ℕ} (φ : SetFormula n) (ρ σ : Fin n → AName.{u} A) :
    (⨅ i, eqB (ρ i) (σ i)) ⊓ bval φ ρ ≤ bval φ σ := by
  induction φ with
  | mem i j =>
    have hij : (⨅ k, eqB (ρ k) (σ k)) ≤ eqB (ρ i) (σ i) ⊓ eqB (ρ j) (σ j) :=
      le_inf (iInf_le _ i) (iInf_le _ j)
    refine (inf_le_inf_right (memB (ρ i) (ρ j)) hij).trans ?_
    have h₁ : eqB (ρ i) (σ i) ⊓ memB (ρ i) (ρ j) ≤ memB (σ i) (ρ j) := by
      rw [inf_comm]; exact memB_eqB_left (ρ i) (ρ j) (σ i)
    have h₂ : memB (σ i) (ρ j) ⊓ eqB (ρ j) (σ j) ≤ memB (σ i) (σ j) :=
      memB_eqB_right (ρ j) (σ i) (σ j)
    refine le_trans ?_ h₂
    refine le_inf ?_ ?_
    · refine le_trans ?_ h₁
      exact le_inf (inf_le_of_left_le inf_le_left) inf_le_right
    · exact inf_le_of_left_le inf_le_right
  | eq i j =>
    have hij : (⨅ k, eqB (ρ k) (σ k)) ≤ eqB (ρ i) (σ i) ⊓ eqB (ρ j) (σ j) :=
      le_inf (iInf_le _ i) (iInf_le _ j)
    refine (inf_le_inf_right (eqB (ρ i) (ρ j)) hij).trans ?_
    have h₁ : eqB (σ i) (ρ i) ⊓ eqB (ρ i) (ρ j) ≤ eqB (σ i) (ρ j) :=
      eqB_trans (σ i) (ρ i) (ρ j)
    have h₂ : eqB (σ i) (ρ j) ⊓ eqB (ρ j) (σ j) ≤ eqB (σ i) (σ j) :=
      eqB_trans (σ i) (ρ j) (σ j)
    refine le_trans ?_ h₂
    refine le_inf ?_ ?_
    · refine le_trans ?_ h₁
      rw [eqB_comm (x := ρ i) (y := σ i)]
      exact le_inf (inf_le_of_left_le inf_le_left) inf_le_right
    · exact inf_le_of_left_le inf_le_right
  | not φ ih =>
    rw [bval_not, bval_not, inf_compl_le_compl_iff]
    have hcomm : (⨅ i, eqB (σ i) (ρ i)) = ⨅ i, eqB (ρ i) (σ i) :=
      iInf_congr fun i => eqB_comm (σ i) (ρ i)
    simpa [hcomm] using ih σ ρ
  | and φ ψ ihφ ihψ =>
    rw [bval_and, bval_and]
    refine le_inf ?_ ?_
    · exact (inf_le_inf_left _ inf_le_left).trans (ihφ ρ σ)
    · exact (inf_le_inf_left _ inf_le_right).trans (ihψ ρ σ)
  | ex φ ih =>
    rw [bval_ex, bval_ex, inf_iSup_eq (a := (⨅ i, eqB (ρ i) (σ i) : A))]
    refine iSup_le fun y => ?_
    refine le_trans ?_ (le_iSup
      (fun y' : AName A => bval φ (consName y' σ)) y)
    have hcons := eqB_iInf_cons (A := A) y ρ σ
    have := ih (consName y ρ) (consName y σ)
    simpa [hcons] using this
  | all φ ih =>
    rw [bval_all, bval_all]
    refine le_iInf fun y => ?_
    have hcons := eqB_iInf_cons (A := A) y ρ σ
    have := ih (consName y ρ) (consName y σ)
    refine le_trans ?_ this
    refine le_inf ?_ ?_
    · rw [← hcons]
      exact inf_le_of_left_le le_rfl
    · exact inf_le_of_right_le (iInf_le _ y)

theorem bval_subst {n : ℕ} (φ : SetFormula (n + 1)) (x y : AName.{u} A)
    (ρ : Fin n → AName.{u} A) :
    eqB x y ⊓ bval φ (consName x ρ) ≤ bval φ (consName y ρ) := by
  have h := bval_congr φ (consName x ρ) (consName y ρ)
  have hcons : (⨅ i, eqB (consName x ρ i) (consName y ρ i)) = eqB x y := by
    rw [iInf_fin_succ (fun i => eqB (consName x ρ i) (consName y ρ i))]
    simp [eqB_self]
  rwa [hcons] at h

theorem himp_iInf_eq {ι : Sort*} (a : A) (f : ι → A) :
    a ⇨ ⨅ i, f i = ⨅ i, a ⇨ f i :=
  le_antisymm
    (le_iInf fun i => himp_le_himp_left (iInf_le _ i))
    (le_himp_iff.mpr (le_iInf fun i =>
      ((inf_le_inf_right a (iInf_le (fun j => a ⇨ f j) i)).trans himp_inf_le)))

theorem iInf_himp_le_himp_iInf {ι : Sort*} (f g : ι → A) :
    (⨅ i, f i ⇨ g i) ≤ (⨅ i, f i) ⇨ ⨅ i, g i := by
  rw [le_himp_iff]
  refine le_iInf fun i =>
    ((inf_le_inf (iInf_le (fun j => f j ⇨ g j) i) (iInf_le f i)).trans
      himp_inf_le)

/-- Modus ponens is sound for the Boolean valuation. -/
theorem mp_valid {n} (φ ψ : SetFormula n) (ρ : Fin n → AName.{u} A)
    (himp : bval (implies φ ψ) ρ = ⊤) (hφ : bval φ ρ = ⊤) :
    bval ψ ρ = ⊤ := by
  have : bval φ ρ ⇨ bval ψ ρ = ⊤ := by rwa [bval_implies] at himp
  exact top_unique ((himp_eq_top_iff.mp this).trans' hφ.ge)

/-- Universal generalization / instantiation for the Boolean valuation. -/
theorem all_valid_iff {n} (φ : SetFormula (n + 1)) (ρ : Fin n → AName.{u} A) :
    bval (.all φ) ρ = ⊤ ↔ ∀ x, bval φ (consName x ρ) = ⊤ :=
  iInf_eq_top

end SetFormula

open SetFormula

variable {A : Type u} [CompleteBooleanAlgebra A]

open AName D0Formula SetFormula

/-- CSL Theorem 1(ii): the inference rules of first-order logic are sound for
the Boolean valuation of `𝔏_Set(V^A)`. They apply to arbitrary assignments
(statements about elements of `V^A`), hence also to ZFC theorems (Theorem 1(i)).
The three clauses are modus ponens, `∀`-introduction/elimination, and
substitution of equal names (Jech (14.9) and the paragraph after it). -/
theorem theorem_1_ii {n : ℕ} (φ ψ : SetFormula n) (ρ : Fin n → AName.{u} A) :
    (bval (implies φ ψ) ρ = ⊤ → bval φ ρ = ⊤ → bval ψ ρ = ⊤) ∧
    (∀ χ : SetFormula (n + 1),
      bval (.all χ) ρ = ⊤ ↔ ∀ x, bval χ (consName x ρ) = ⊤) ∧
    (∀ (χ : SetFormula n) (σ : Fin n → AName.{u} A),
      (⨅ i, eqB (ρ i) (σ i)) ⊓ bval χ ρ ≤ bval χ σ) :=
  ⟨mp_valid φ ψ ρ, fun χ => all_valid_iff χ ρ, fun χ σ => bval_congr χ ρ σ⟩

/-- Jech Lemma 14.17: `V^A` is extensional. -/
theorem jech_lemma_14_17 (X Y : AName.{u} A) :
    (⨅ u : AName.{u} A, (memB u X ⇨ memB u Y) ⊓ (memB u Y ⇨ memB u X)) ≤
      eqB X Y := by
  have hsub (U V : AName A) :
      (⨅ u : AName A, memB u U ⇨ memB u V) ≤ subsetB U V := by
    refine le_iInf fun i => ?_
    have hch := iInf_le (fun u : AName A => memB u U ⇨ memB u V) (U.child i)
    have hval : U.val i ≤ memB (U.child i) U := val_le_memB U i
    exact (himp_le_himp_right hval).trans' hch
  rw [eqB_eq_subset]
  refine le_inf ?_ ?_
  · exact (hsub X Y).trans' (iInf_mono fun _ => inf_le_left)
  · exact (hsub Y X).trans' (iInf_mono fun _ => inf_le_right)

theorem subsetB_eq_iInf (X Y : AName.{u} A) :
    subsetB X Y = ⨅ u : AName.{u} A, memB u X ⇨ memB u Y :=
  le_antisymm
    (le_iInf fun u => le_himp_iff.mpr (by
      rw [inf_comm]; exact memB_of_subsetB u X Y))
    (le_iInf fun i =>
      (iInf_le (fun u : AName A => memB u X ⇨ memB u Y) (X.child i)).trans
        (himp_le_himp_right (val_le_memB X i)))

theorem eqB_eq_iInf (X Y : AName.{u} A) :
    eqB X Y = ⨅ u : AName.{u} A, (memB u X ⇨ memB u Y) ⊓ (memB u Y ⇨ memB u X) :=
  le_antisymm
    (le_iInf fun u => le_inf
      (le_himp_iff.mpr (by rw [inf_comm]; exact memB_eqB_right X u Y))
      (le_himp_iff.mpr (by
        rw [inf_comm, eqB_comm (x := X) (y := Y)]
        exact memB_eqB_right Y u X)))
    (jech_lemma_14_17 X Y)

/-!
## ZFC axioms in `V^A` (Jech Theorem 14.24)
-/

theorem collectB_spec (X : AName.{u} A) (φ : AName.{u} A → AName.{u} A → A)
    (hcongr : ∀ u v w, eqB v w ⊓ φ u v ≤ φ u w) (i : X.idx) :
    φ (X.child i) ((collectB X φ hcongr).child i) = ⨆ v, φ (X.child i) v :=
  Classical.choose_spec (fullness (φ (X.child i)) (hcongr (X.child i)))

inductive ZFCAxiom : {n : ℕ} → SetFormula n → Prop
  | extensionality : ZFCAxiom extensionalityAxiom
  | pairing : ZFCAxiom pairingAxiom
  | union : ZFCAxiom unionAxiom
  | power : ZFCAxiom powerAxiom
  | infinity : ZFCAxiom infinityAxiom
  | regularity : ZFCAxiom regularityAxiom
  | choice : ZFCAxiom choiceAxiom
  | separation {n} (φ : SetFormula (n + 1)) : ZFCAxiom (separationAxiom φ)
  | collection {n} (φ : SetFormula (n + 2)) : ZFCAxiom (collectionAxiom φ)

/-- Hilbert-style first-order deduction from the ZFC axioms. -/
inductive ZFCProvable : {n : ℕ} → SetFormula n → Prop
  | ax {n} {φ : SetFormula n} : ZFCAxiom φ → ZFCProvable φ
  | mp {n} {φ ψ : SetFormula n} :
      ZFCProvable (implies φ ψ) → ZFCProvable φ → ZFCProvable ψ
  | gen {n} {φ : SetFormula (n + 1)} :
      ZFCProvable φ → ZFCProvable (.all φ)
  | hilbertK {n} (φ ψ : SetFormula n) :
      ZFCProvable (implies φ (implies ψ φ))
  | hilbertS {n} (φ ψ χ : SetFormula n) :
      ZFCProvable (implies (implies φ (implies ψ χ))
        (implies (implies φ ψ) (implies φ χ)))
  | hilbertDNE {n} (φ ψ : SetFormula n) :
      ZFCProvable (implies (implies φ.not ψ.not) (implies ψ φ))
  | allImp {n} (φ ψ : SetFormula (n + 1)) :
      ZFCProvable (implies (.all (implies φ ψ))
        (implies (.all φ) (.all ψ)))
  | allVac {n} (φ : SetFormula n) (ψ : SetFormula (n + 1)) :
      ZFCProvable (implies (.all (implies φ.lift ψ)) (implies φ (.all ψ)))
  | allInst {n} (φ : SetFormula (n + 1)) (t : Fin n) :
      ZFCProvable (implies (.all φ) (inst φ t))
  | eqRefl : ZFCProvable (.all (.eq 0 0))
  | eqLeibniz {n} (φ : SetFormula (n + 1)) :
      ZFCProvable (eqLeibnizAxiom φ)

theorem memB_unionB_of_mem (X u v : AName.{u} A) :
    memB u X ⊓ memB v u ≤ memB v (unionB X) := by
  rw [memB_eq (x := u) (y := X), iSup_inf_eq]
  refine iSup_le fun i => ?_
  have hvu : eqB u (X.child i) ⊓ memB v u ≤ memB v (X.child i) := by
    rw [inf_comm]; exact memB_eqB_right u v (X.child i)
  have hto : eqB u (X.child i) ⊓ X.val i ⊓ memB v u ≤ memB v (X.child i) :=
    hvu.trans' (le_inf (inf_le_of_left_le inf_le_left) inf_le_right)
  refine hto.trans ?_
  rw [memB_eq (x := v) (y := X.child i)]
  refine iSup_le fun j => ?_
  unfold unionB
  rw [memB_mk]
  refine le_iSup_of_le ⟨i, j⟩ ?_
  exact le_inf inf_le_left le_top

theorem axiom_extensionality_valid (ρ : Fin 0 → AName.{u} A) :
    bval extensionalityAxiom ρ = ⊤ := by
  refine iInf_eq_top.mpr fun X => iInf_eq_top.mpr fun Y => ?_
  rw [bval_implies, himp_eq_top_iff]
  have hx : consName Y (consName X ρ) (1 : Fin 2) = X := rfl
  have hy : consName Y (consName X ρ) (0 : Fin 2) = Y := rfl
  simp only [bval_eq, hx, hy]
  refine (eqB_eq_iInf X Y).ge.trans' (le_of_eq (iInf_congr fun u => ?_))
  have hx' : consName u (consName Y (consName X ρ)) (2 : Fin 3) = X := rfl
  have hy' : consName u (consName Y (consName X ρ)) (1 : Fin 3) = Y := rfl
  simp [bval_iff, bval_mem, hx', hy']

theorem addNat_succ' {n m} (i : Fin n) :
    i.addNat (m + 1) = (i.addNat m).succ :=
  Fin.ext (by simp [Fin.addNat]; ac_rfl)

omit [CompleteBooleanAlgebra A] in
theorem consName_addNat3 {n} (z Y X : AName.{u} A) (ρ : Fin n → AName.{u} A)
    (i : Fin n) :
    consName z (consName Y (consName X ρ)) (i.addNat 3) = ρ i := by
  rw [show i.addNat 3 = (i.addNat 2).succ from addNat_succ' (m := 2) i,
    consName_succ,
    show i.addNat 2 = (i.addNat 1).succ from addNat_succ' (m := 1) i,
    consName_succ,
    show i.addNat 1 = i.succ from addNat_succ' (m := 0) i,
    consName_succ]

theorem bval_ex_eq_top_of {n} {φ : SetFormula (n + 1)}
    {ρ : Fin n → AName.{u} A} (x : AName.{u} A)
    (hx : SetFormula.bval φ (consName x ρ) = ⊤) :
    SetFormula.bval (.ex φ) ρ = ⊤ :=
  top_unique (hx.ge.trans (le_iSup (fun y : AName.{u} A =>
    SetFormula.bval φ (consName y ρ)) x))

theorem axiom_pairing_valid (ρ : Fin 0 → AName.{u} A) :
    bval pairingAxiom ρ = ⊤ := by
  unfold pairingAxiom
  rw [all_valid_iff]
  intro x
  rw [all_valid_iff]
  intro y
  refine bval_ex_eq_top_of (pairB x y) ?_
  have hx : consName (pairB x y) (consName y (consName x ρ)) (2 : Fin 3) = x :=
    rfl
  have hy : consName (pairB x y) (consName y (consName x ρ)) (1 : Fin 3) = y :=
    rfl
  have hz : consName (pairB x y) (consName y (consName x ρ)) (0 : Fin 3) =
      pairB x y := rfl
  simp [SetFormula.bval_and, SetFormula.bval_mem, hx, hy, hz, memB_pairB,
    eqB_self]

theorem axiom_union_valid (ρ : Fin 0 → AName.{u} A) :
    bval unionAxiom ρ = ⊤ := by
  unfold unionAxiom
  rw [all_valid_iff]
  intro X
  refine bval_ex_eq_top_of (unionB X) ?_
  rw [all_valid_iff]
  intro u
  rw [all_valid_iff]
  intro v
  rw [SetFormula.bval_implies, SetFormula.bval_implies, himp_eq_top_iff,
    le_himp_iff]
  have hX : consName v (consName u (consName (unionB X) (consName X ρ)))
      (3 : Fin 4) = X := rfl
  have hY : consName v (consName u (consName (unionB X) (consName X ρ)))
      (2 : Fin 4) = unionB X := rfl
  have hu : consName v (consName u (consName (unionB X) (consName X ρ)))
      (1 : Fin 4) = u := rfl
  have hv : consName v (consName u (consName (unionB X) (consName X ρ)))
      (0 : Fin 4) = v := rfl
  simp [SetFormula.bval_mem, hX, hY, hu, hv]
  exact memB_unionB_of_mem X u v

theorem axiom_power_valid (ρ : Fin 0 → AName.{u} A) :
    bval powerAxiom ρ = ⊤ := by
  unfold powerAxiom
  rw [all_valid_iff]
  intro X
  refine bval_ex_eq_top_of (powerB X) ?_
  rw [all_valid_iff]
  intro u
  rw [SetFormula.bval_implies, himp_eq_top_iff]
  have hY : consName u (consName (powerB X) (consName X ρ)) (1 : Fin 3) =
      powerB X := rfl
  have hu : consName u (consName (powerB X) (consName X ρ)) (0 : Fin 3) = u :=
    rfl
  simp only [SetFormula.bval_all, SetFormula.bval_implies, SetFormula.bval_mem,
    hY, hu]
  have hsub :
      (⨅ z : AName A,
        memB (consName z (consName u (consName (powerB X) (consName X ρ)))
            (0 : Fin 4))
          (consName z (consName u (consName (powerB X) (consName X ρ)))
            (1 : Fin 4)) ⇨
        memB (consName z (consName u (consName (powerB X) (consName X ρ)))
            (0 : Fin 4))
          (consName z (consName u (consName (powerB X) (consName X ρ)))
            (3 : Fin 4))) = subsetB u X := by
    refine Eq.trans (iInf_congr fun z => ?_) (subsetB_eq_iInf u X).symm
    have hz0 : consName z (consName u (consName (powerB X) (consName X ρ)))
        (0 : Fin 4) = z := rfl
    have hz1 : consName z (consName u (consName (powerB X) (consName X ρ)))
        (1 : Fin 4) = u := rfl
    have hz3 : consName z (consName u (consName (powerB X) (consName X ρ)))
        (3 : Fin 4) = X := rfl
    simp [hz0, hz1, hz3]
  rw [hsub, memB_powerB]

theorem bval_sepRename {n} (φ : SetFormula (n + 1)) (z Y X : AName.{u} A)
    (ρ : Fin n → AName.{u} A) :
    bval (rename sepRename φ) (consName z (consName Y (consName X ρ))) =
      bval φ (consName z ρ) := by
  rw [SetFormula.bval_rename]
  congr 1
  funext i
  refine Fin.cases ?_ ?_ i
  · rfl
  · intro i
    exact consName_addNat3 z Y X ρ i

theorem axiom_separation_valid {n} (φ : SetFormula (n + 1))
    (ρ : Fin n → AName.{u} A) :
    bval (separationAxiom φ) ρ = ⊤ := by
  unfold separationAxiom
  rw [all_valid_iff]
  intro X
  refine bval_ex_eq_top_of (sepB X (fun z => bval φ (consName z ρ))) ?_
  rw [all_valid_iff]
  intro z
  rw [SetFormula.bval_iff]
  have hY : consName z (consName (sepB X (fun w => bval φ (consName w ρ)))
      (consName X ρ)) (1 : Fin (n + 3)) =
      sepB X (fun w => bval φ (consName w ρ)) := rfl
  have hX : consName z (consName (sepB X (fun w => bval φ (consName w ρ)))
      (consName X ρ)) (2 : Fin (n + 3)) = X := rfl
  have hz : consName z (consName (sepB X (fun w => bval φ (consName w ρ)))
      (consName X ρ)) (0 : Fin (n + 3)) = z := rfl
  simp only [SetFormula.bval_and, SetFormula.bval_mem, hY, hX, hz]
  rw [bval_sepRename, memB_sepB (A := A) z X (fun w => bval φ (consName w ρ))
    (fun x y => SetFormula.bval_subst φ x y ρ)]
  simp [himp_self]

theorem memB_check_empty (z : AName.{u} A) :
    memB z (check (A := A) (∅ : PSet.{u})) = ⊥ := by
  have hempty : (∅ : PSet.{u}) = PSet.mk PEmpty PEmpty.elim := PSet.empty_def
  rw [hempty, check_mk, memB_mk]
  exact iSup_of_empty _

theorem iSup_eqB_inf_memB (s X : AName.{u} A) :
    (⨆ t, eqB t s ⊓ memB t X) = memB s X :=
  le_antisymm
    (iSup_le fun t => by
      rw [inf_comm]
      exact memB_eqB_left t X s)
    (le_iSup_of_le s (by rw [eqB_self]; exact le_inf le_top le_rfl))

theorem eqB_eq_insert_succ (s y : AName.{u} A) :
    (⨅ z : AName.{u} A, (memB z s ⇨ memB z y ⊔ eqB z y) ⊓
      (memB z y ⊔ eqB z y ⇨ memB z s)) = eqB s (succB y) := by
  have h : ∀ z, memB z (succB y) = memB z y ⊔ eqB z y := fun z => by
    rw [succB, memB_insertB, sup_comm]
  refine Eq.trans (iInf_congr fun z => by rw [← h z]) (eqB_eq_iInf s (succB y)).symm

theorem axiom_infinity_valid (ρ : Fin 0 → AName.{u} A) :
    bval infinityAxiom ρ = ⊤ := by
  unfold infinityAxiom
  refine bval_ex_eq_top_of (check (A := A) PSet.omega) ?_
  rw [SetFormula.bval_and]
  refine inf_eq_top_iff.mpr ⟨?empty, ?succ⟩
  · refine bval_ex_eq_top_of (check (A := A) (∅ : PSet.{u})) ?_
    rw [SetFormula.bval_and]
    refine inf_eq_top_iff.mpr ⟨?emp, ?mem⟩
    · rw [SetFormula.bval_all]
      refine iInf_eq_top.mpr fun z => ?_
      simp [SetFormula.bval_not, SetFormula.bval_mem, consName,
        memB_check_empty, compl_bot]
    · simp [SetFormula.bval_mem, consName]
      exact memB_check_ofNat_of_inductive (A := A) (check PSet.omega)
        check_omega_inductive 0
  · rw [all_valid_iff]
    intro y
    rw [SetFormula.bval_implies, himp_eq_top_iff]
    have hy : consName y (consName (check (A := A) PSet.omega) ρ) (0 : Fin 2) =
        y := rfl
    have hω : consName y (consName (check (A := A) PSet.omega) ρ) (1 : Fin 2) =
        check (A := A) PSet.omega := rfl
    simp only [SetFormula.bval_mem, hy, hω]
    have hcl : memB y (check (A := A) PSet.omega) ≤
        memB (succB y) (check PSet.omega) :=
      himp_eq_top_iff.mp (iInf_eq_top.mp
        (inf_eq_top_iff.mp (check_omega_inductive (A := A))).2 y)
    refine hcl.trans ?_
    have hform :
        SetFormula.bval
          (.ex (.and
            (.all (iff (.mem 0 1) (.or (.mem 0 2) (.eq 0 2))))
            (.mem 0 2)))
          (consName y (consName (check (A := A) PSet.omega) ρ)) =
          ⨆ s : AName.{u} A,
            eqB s (succB y) ⊓ memB s (check (A := A) PSet.omega) := by
      refine iSup_congr fun s => ?_
      have hs : consName s (consName y (consName (check (A := A) PSet.omega) ρ))
          (0 : Fin 3) = s := rfl
      have hω' : consName s (consName y (consName (check (A := A) PSet.omega) ρ))
          (2 : Fin 3) = check (A := A) PSet.omega := rfl
      simp only [SetFormula.bval_and, SetFormula.bval_all, SetFormula.bval_iff,
        SetFormula.bval_or, SetFormula.bval_mem, SetFormula.bval_eq, hs, hω']
      refine congrArg (fun a => a ⊓ memB s (check (A := A) PSet.omega)) ?_
      refine Eq.trans (iInf_congr fun z => ?_) (eqB_eq_insert_succ s y)
      have hz1 : consName z (consName s (consName y
          (consName (check (A := A) PSet.omega) ρ))) (1 : Fin 4) = s := rfl
      have hz2 : consName z (consName s (consName y
          (consName (check (A := A) PSet.omega) ρ))) (2 : Fin 4) = y := rfl
      simp [hz1, hz2]
    rw [hform, iSup_eqB_inf_memB]

theorem regularity_core_compl (X y : AName.{u} A) :
    (⨅ z : AName.{u} A, memB z y ⇨ (memB z X)ᶜ) =
      (⨆ z : AName.{u} A, memB z y ⊓ memB z X)ᶜ := by
  have h : ∀ z : AName.{u} A,
      memB z y ⇨ (memB z X)ᶜ = (memB z y ⊓ memB z X)ᶜ := by
    intro z
    rw [himp_eq, ← compl_inf, inf_comm]
  simp_rw [h]
  rw [← compl_iSup]

theorem memB_decomp_regularity (X y : AName.{u} A) :
    memB y X =
      (memB y X ⊓ ⨅ z : AName.{u} A, memB z y ⇨ (memB z X)ᶜ) ⊔
        (memB y X ⊓ ⨆ z : AName.{u} A, memB z y ⊓ memB z X) := by
  rw [regularity_core_compl, ← inf_sup_left, sup_comm, sup_compl_eq_top,
    inf_top_eq]

/-- Jech 14.26: a nonempty name has a Boolean-minimal element, by rank. -/
theorem regularity_semantic (X : AName.{u} A) :
    (⨆ y : AName.{u} A, memB y X) ≤
      ⨆ y : AName.{u} A,
        memB y X ⊓ ⨅ z : AName.{u} A, memB z y ⇨ (memB z X)ᶜ := by
  have hwf : WellFounded fun x y : AName.{u} A => rank x < rank y :=
    InvImage.wf rank wellFounded_lt
  refine iSup_le fun y => ?_
  refine hwf.induction (C := fun y : AName.{u} A =>
      memB y X ≤ ⨆ w : AName.{u} A,
        memB w X ⊓ ⨅ z : AName.{u} A, memB z w ⇨ (memB z X)ᶜ)
    y fun y ih => ?_
  have hdecomp := memB_decomp_regularity (A := A) X y
  have hcore :
      memB y X ⊓ ⨆ z : AName.{u} A, memB z y ⊓ memB z X ≤
        ⨆ w : AName.{u} A,
          memB w X ⊓ ⨅ z : AName.{u} A, memB z w ⇨ (memB z X)ᶜ := by
    refine inf_le_of_right_le (iSup_le fun z => ?_)
    rw [memB_eq (x := z) (y := y), iSup_inf_eq]
    refine iSup_le fun i => ?_
    have hchild :
        eqB z (y.child i) ⊓ y.val i ⊓ memB z X ≤ memB (y.child i) X := by
      have : eqB z (y.child i) ⊓ memB z X ≤ memB (y.child i) X := by
        rw [inf_comm]; exact memB_eqB_left z X (y.child i)
      exact this.trans' (le_inf (inf_le_of_left_le inf_le_left) inf_le_right)
    exact hchild.trans (ih (y.child i) (rank_child_lt y i))
  have hgood :
      memB y X ⊓ ⨅ z : AName.{u} A, memB z y ⇨ (memB z X)ᶜ ≤
        ⨆ w : AName.{u} A,
          memB w X ⊓ ⨅ z : AName.{u} A, memB z w ⇨ (memB z X)ᶜ :=
    le_iSup_of_le y le_rfl
  exact hdecomp.le.trans (sup_le hgood hcore)

theorem axiom_regularity_valid (ρ : Fin 0 → AName.{u} A) :
    bval regularityAxiom ρ = ⊤ := by
  unfold regularityAxiom
  rw [all_valid_iff]
  intro X
  rw [SetFormula.bval_implies, himp_eq_top_iff]
  have hlhs :
      SetFormula.bval (.ex (.mem 0 1)) (consName X ρ) =
        ⨆ y : AName.{u} A, memB y X := by
    refine iSup_congr fun y => ?_
    have hy : consName y (consName X ρ) (0 : Fin 2) = y := rfl
    have hX : consName y (consName X ρ) (1 : Fin 2) = X := rfl
    simp [SetFormula.bval_mem, hy, hX]
  have hrhs :
      SetFormula.bval
        (.ex (.and (.mem 0 1)
          (.all (implies (.mem 0 1) (.not (.mem 0 2))))))
        (consName X ρ) =
        ⨆ y : AName.{u} A,
          memB y X ⊓ ⨅ z : AName.{u} A, memB z y ⇨ (memB z X)ᶜ := by
    refine iSup_congr fun y => ?_
    have hy : consName y (consName X ρ) (0 : Fin 2) = y := rfl
    have hX : consName y (consName X ρ) (1 : Fin 2) = X := rfl
    simp only [SetFormula.bval_and, SetFormula.bval_mem, SetFormula.bval_all,
      SetFormula.bval_implies, SetFormula.bval_not, hy, hX]
    refine congrArg (fun a => memB y X ⊓ a) (iInf_congr fun z => ?_)
    have hz0 : consName z (consName y (consName X ρ)) (0 : Fin 3) = z := rfl
    have hz1 : consName z (consName y (consName X ρ)) (1 : Fin 3) = y := rfl
    have hz2 : consName z (consName y (consName X ρ)) (2 : Fin 3) = X := rfl
    simp [hz0, hz1, hz2]
  rw [hlhs, hrhs]
  exact regularity_semantic X

omit [CompleteBooleanAlgebra A] in
theorem consName_addNat4 {n} (v u Y X : AName.{u} A) (ρ : Fin n → AName.{u} A)
    (i : Fin n) :
    consName v (consName u (consName Y (consName X ρ))) (i.addNat 4) = ρ i := by
  rw [show i.addNat 4 = (i.addNat 3).succ from addNat_succ' (m := 3) i,
    consName_succ]
  exact consName_addNat3 u Y X ρ i

theorem bval_colRename {n} (φ : SetFormula (n + 2))
    (v u Y X : AName.{u} A) (ρ : Fin n → AName.{u} A) :
    SetFormula.bval (rename colRename φ)
      (consName v (consName u (consName Y (consName X ρ)))) =
      SetFormula.bval φ (consName v (consName u ρ)) := by
  rw [SetFormula.bval_rename]
  congr 1
  funext i
  refine Fin.cases ?_ (fun i => Fin.cases ?_ (fun i => ?_) i) i
  · rfl
  · rfl
  · exact consName_addNat4 v u Y X ρ i

theorem axiom_collection_valid {n} (φ : SetFormula (n + 2))
    (ρ : Fin n → AName.{u} A) :
    bval (collectionAxiom φ) ρ = ⊤ := by
  unfold collectionAxiom
  rw [all_valid_iff]
  intro X
  let Φ : AName.{u} A → AName.{u} A → A :=
    fun u v => SetFormula.bval φ (consName v (consName u ρ))
  have hcongr : ∀ u v w, eqB v w ⊓ Φ u v ≤ Φ u w :=
    fun u v w => SetFormula.bval_subst φ v w (consName u ρ)
  have hcongr_u (u u' v : AName.{u} A) : eqB u u' ⊓ Φ u v ≤ Φ u' v := by
    have h := SetFormula.bval_congr φ (consName v (consName u ρ))
      (consName v (consName u' ρ))
    have hcons :
        (⨅ i, eqB (consName v (consName u ρ) i)
          (consName v (consName u' ρ) i)) = eqB u u' := by
      rw [iInf_fin_succ (fun i => eqB (consName v (consName u ρ) i)
        (consName v (consName u' ρ) i))]
      rw [iInf_fin_succ (fun i : Fin (n + 1) =>
        eqB (consName v (consName u ρ) i.succ)
          (consName v (consName u' ρ) i.succ))]
      simp [consName, eqB_self]
    rwa [hcons] at h
  refine bval_ex_eq_top_of (collectB X Φ hcongr) ?_
  rw [all_valid_iff]
  intro u
  rw [SetFormula.bval_implies, SetFormula.bval_implies, himp_eq_top_iff,
    le_himp_iff]
  have hX : consName u (consName (collectB X Φ hcongr) (consName X ρ))
      (2 : Fin (n + 3)) = X := rfl
  have hY : consName u (consName (collectB X Φ hcongr) (consName X ρ))
      (1 : Fin (n + 3)) = collectB X Φ hcongr := rfl
  have hu : consName u (consName (collectB X Φ hcongr) (consName X ρ))
      (0 : Fin (n + 3)) = u := rfl
  have hex :
      SetFormula.bval (.ex (rename colRename φ))
        (consName u (consName (collectB X Φ hcongr) (consName X ρ))) =
        ⨆ v : AName.{u} A, Φ u v := by
    refine iSup_congr fun v => ?_
    rw [bval_colRename]
  have hexY :
      SetFormula.bval
        (.ex (.and (.mem 0 2) (rename colRename φ)))
        (consName u (consName (collectB X Φ hcongr) (consName X ρ))) =
        ⨆ v : AName.{u} A, memB v (collectB X Φ hcongr) ⊓ Φ u v := by
    refine iSup_congr fun v => ?_
    have hv : consName v
        (consName u (consName (collectB X Φ hcongr) (consName X ρ)))
        (0 : Fin (n + 4)) = v := rfl
    have hY' : consName v
        (consName u (consName (collectB X Φ hcongr) (consName X ρ)))
        (2 : Fin (n + 4)) = collectB X Φ hcongr := rfl
    simp only [SetFormula.bval_and, SetFormula.bval_mem, hv, hY']
    rw [bval_colRename]
  simp only [SetFormula.bval_mem, hX, hu]
  rw [hex, hexY]
  rw [memB_eq (x := u) (y := X), iSup_inf_eq]
  refine iSup_le fun i => ?_
  have hto :
      eqB u (X.child i) ⊓ X.val i ⊓ ⨆ v : AName.{u} A, Φ u v ≤
        eqB u (X.child i) ⊓
          Φ (X.child i) ((collectB X Φ hcongr).child i) := by
    refine le_inf (inf_le_of_left_le inf_le_left) ?_
    have hswap :
        eqB u (X.child i) ⊓ ⨆ v : AName.{u} A, Φ u v ≤
          ⨆ v : AName.{u} A, Φ (X.child i) v := by
      rw [inf_iSup_eq]
      refine iSup_le fun v => ?_
      exact (hcongr_u u (X.child i) v).trans
        (le_iSup (fun w => Φ (X.child i) w) v)
    exact (collectB_spec X Φ hcongr i).ge.trans'
      (hswap.trans' (le_inf (inf_le_of_left_le inf_le_left) inf_le_right))
  refine hto.trans ?_
  have hmemY : (⊤ : A) ≤
      memB ((collectB X Φ hcongr).child i) (collectB X Φ hcongr) :=
    val_le_memB (collectB X Φ hcongr) i
  have hback : eqB u (X.child i) ⊓
      Φ (X.child i) ((collectB X Φ hcongr).child i) ≤
        Φ u ((collectB X Φ hcongr).child i) := by
    simpa [eqB_comm (x := u) (y := X.child i)] using
      hcongr_u (X.child i) u ((collectB X Φ hcongr).child i)
  refine (le_inf (hmemY.trans' le_top) hback).trans
    (le_iSup (fun v : AName.{u} A =>
      memB v (collectB X Φ hcongr) ⊓ Φ u v)
      ((collectB X Φ hcongr).child i))

theorem hilbertK_sound {n} (φ ψ : SetFormula n) (ρ : Fin n → AName.{u} A) :
    bval (implies φ (implies ψ φ)) ρ = ⊤ := by
  simp only [SetFormula.bval_implies]
  rw [himp_eq_top_iff, le_himp_iff]
  exact inf_le_left

theorem hilbertS_sound {n} (φ ψ χ : SetFormula n) (ρ : Fin n → AName.{u} A) :
    bval (implies (implies φ (implies ψ χ))
      (implies (implies φ ψ) (implies φ χ))) ρ = ⊤ := by
  simp only [SetFormula.bval_implies]
  rw [himp_eq_top_iff, le_himp_iff, le_himp_iff]
  set a := SetFormula.bval φ ρ
  set b := SetFormula.bval ψ ρ
  set c := SetFormula.bval χ ρ
  change (a ⇨ (b ⇨ c)) ⊓ (a ⇨ b) ⊓ a ≤ c
  have hre : (a ⇨ (b ⇨ c)) ⊓ (a ⇨ b) ⊓ a = a ⊓ (a ⇨ (b ⇨ c)) ⊓ (a ⇨ b) := by
    ac_rfl
  rw [hre]
  have h1 : a ⊓ (a ⇨ (b ⇨ c)) ≤ b ⇨ c := by
    rw [inf_comm]; exact himp_inf_le (a := a) (b := b ⇨ c)
  have h2 : a ⊓ (a ⇨ b) ≤ b := by
    rw [inf_comm]; exact himp_inf_le (a := a) (b := b)
  have h3 : a ⊓ (a ⇨ (b ⇨ c)) ⊓ (a ⇨ b) ≤ (b ⇨ c) ⊓ b :=
    le_inf (h1.trans' inf_le_left)
      (h2.trans' (le_inf (inf_le_of_left_le inf_le_left) inf_le_right))
  exact h3.trans (himp_inf_le (a := b) (b := c))

theorem hilbertDNE_sound {n} (φ ψ : SetFormula n) (ρ : Fin n → AName.{u} A) :
    bval (implies (implies φ.not ψ.not) (implies ψ φ)) ρ = ⊤ := by
  simp only [SetFormula.bval_implies, SetFormula.bval_not]
  rw [himp_eq_top_iff]
  simp only [himp_eq, compl_compl]
  exact (sup_comm (a := (SetFormula.bval ψ ρ)ᶜ) (b := SetFormula.bval φ ρ)).le

theorem allImp_sound {n} (φ ψ : SetFormula (n + 1)) (ρ : Fin n → AName.{u} A) :
    bval (implies (.all (implies φ ψ)) (implies (.all φ) (.all ψ))) ρ = ⊤ := by
  simp only [SetFormula.bval_implies, SetFormula.bval_all]
  rw [himp_eq_top_iff]
  exact iInf_himp_le_himp_iInf
    (fun x => SetFormula.bval φ (consName x ρ))
    (fun x => SetFormula.bval ψ (consName x ρ))

theorem allVac_sound {n} (φ : SetFormula n) (ψ : SetFormula (n + 1))
    (ρ : Fin n → AName.{u} A) :
    bval (implies (.all (implies φ.lift ψ)) (implies φ (.all ψ))) ρ = ⊤ := by
  simp only [SetFormula.bval_implies, SetFormula.bval_all, SetFormula.bval_lift]
  rw [himp_eq_top_iff]
  exact (SetFormula.himp_iInf_eq (SetFormula.bval φ ρ)
    (fun x => SetFormula.bval ψ (consName x ρ))).ge

end Scott2026
