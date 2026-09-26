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
import Scott2026.BooleanValuedSetTheory.BooleanLogic
import Scott2026.BooleanValuedSetTheory.VA.SetFormula
import Scott2026.BooleanValuedSetTheory.VA.D0Formula
import Scott2026.BooleanValuedSetTheory.VA.AName
import Scott2026.BooleanValuedSetTheory.VA.AName.child
import Scott2026.BooleanValuedSetTheory.VA.AName.idx
import Scott2026.BooleanValuedSetTheory.VA.AName.meas
import Scott2026.BooleanValuedSetTheory.VA.AName.measLt
import Scott2026.BooleanValuedSetTheory.VA.AName.rank
import Scott2026.BooleanValuedSetTheory.VA.AName.val
import Scott2026.BooleanValuedSetTheory.VA.AName.eqBLaws
import Scott2026.BooleanValuedSetTheory.VA.D0Formula.bval
import Scott2026.BooleanValuedSetTheory.VA.D0Formula.consName
import Scott2026.BooleanValuedSetTheory.VA.D0Formula.iInfFinSucc
import Scott2026.BooleanValuedSetTheory.VA.D0Formula.consPSet
import Scott2026.BooleanValuedSetTheory.VA.D0Formula.realize
import Scott2026.BooleanValuedSetTheory.VA.HomName
import Scott2026.BooleanValuedSetTheory.VA.SetFormula.bval
import Scott2026.BooleanValuedSetTheory.VA.SetFormula.iff
import Scott2026.BooleanValuedSetTheory.VA.SetFormula.implies
import Scott2026.BooleanValuedSetTheory.VA.SetFormula.inst
import Scott2026.BooleanValuedSetTheory.VA.SetFormula.lift
import Scott2026.BooleanValuedSetTheory.VA.SetFormula.or
import Scott2026.BooleanValuedSetTheory.VA.SetFormula.rename
import Scott2026.BooleanValuedSetTheory.VA.canonVal
import Scott2026.BooleanValuedSetTheory.VA.choiceAxiom
import Scott2026.BooleanValuedSetTheory.VA.colRename
import Scott2026.BooleanValuedSetTheory.VA.collectB
import Scott2026.BooleanValuedSetTheory.VA.collectionAxiom
import Scott2026.BooleanValuedSetTheory.VA.compB
import Scott2026.BooleanValuedSetTheory.VA.eqLeibnizAxiom
import Scott2026.BooleanValuedSetTheory.VA.eqLeibnizRenameX
import Scott2026.BooleanValuedSetTheory.VA.eqLeibnizRenameY
import Scott2026.BooleanValuedSetTheory.VA.extensionalityAxiom
import Scott2026.BooleanValuedSetTheory.VA.finsetB
import Scott2026.BooleanValuedSetTheory.VA.funsB
import Scott2026.BooleanValuedSetTheory.VA.homB
import Scott2026.BooleanValuedSetTheory.VA.idB
import Scott2026.BooleanValuedSetTheory.VA.infinityAxiom
import Scott2026.BooleanValuedSetTheory.VA.insertB
import Scott2026.BooleanValuedSetTheory.VA.isFiniteB
import Scott2026.BooleanValuedSetTheory.VA.isFunctionB
import Scott2026.BooleanValuedSetTheory.VA.isInductiveB
import Scott2026.BooleanValuedSetTheory.VA.isOpairF
import Scott2026.BooleanValuedSetTheory.VA.isSingleValuedB
import Scott2026.BooleanValuedSetTheory.VA.isSingletonF
import Scott2026.BooleanValuedSetTheory.VA.isTotalB
import Scott2026.BooleanValuedSetTheory.VA.isUPairF
import Scott2026.BooleanValuedSetTheory.VA.leastIdx
import Scott2026.BooleanValuedSetTheory.VA.nameSetoid
import Scott2026.BooleanValuedSetTheory.VA.opairB
import Scott2026.BooleanValuedSetTheory.VA.opairMemF
import Scott2026.BooleanValuedSetTheory.VA.pOpair
import Scott2026.BooleanValuedSetTheory.VA.pairB
import Scott2026.BooleanValuedSetTheory.VA.pairingAxiom
import Scott2026.BooleanValuedSetTheory.VA.pfin
import Scott2026.BooleanValuedSetTheory.VA.pfinB
import Scott2026.BooleanValuedSetTheory.VA.pfinEnum
import Scott2026.BooleanValuedSetTheory.VA.powerAxiom
import Scott2026.BooleanValuedSetTheory.VA.powerB
import Scott2026.BooleanValuedSetTheory.VA.prodB
import Scott2026.BooleanValuedSetTheory.VA.regularityAxiom
import Scott2026.BooleanValuedSetTheory.VA.restrictName
import Scott2026.BooleanValuedSetTheory.VA.sepB
import Scott2026.BooleanValuedSetTheory.VA.sepRename
import Scott2026.BooleanValuedSetTheory.VA.separationAxiom
import Scott2026.BooleanValuedSetTheory.VA.singletonB
import Scott2026.BooleanValuedSetTheory.VA.succB
import Scott2026.BooleanValuedSetTheory.VA.unionAxiom
import Scott2026.BooleanValuedSetTheory.VA.unionB
import Scott2026.BooleanValuedSetTheory.VA.wellOrderAxiom
import Scott2026.BooleanValuedSetTheory.VA.wellOrderB
import Scott2026.BooleanValuedSetTheory.VA.worDisj
import Scott2026.BooleanValuedSetTheory.VA.worITE
import Scott2026.BooleanValuedSetTheory.VA.worLe
import Scott2026.BooleanValuedSetTheory.VA.worPredSup
import Scott2026.BooleanValuedSetTheory.VA.Proofs.Core

namespace Scott2026

universe u

variable {A : Type u}
variable [CompleteBooleanAlgebra A]

open AName

theorem eqB_of_memB_singletons (z x y : AName.{u} A) :
    memB z (singletonB x) ⊓ memB z (singletonB y) ≤ eqB x y := by
  rw [memB_singletonB, memB_singletonB, eqB_comm (x := z) (y := x)]
  exact eqB_trans x z y

theorem subsetB_singletonB (x y : AName.{u} A) :
    subsetB (singletonB x) y = memB x y := by
  rw [singletonB, subsetB_mk, iInf_unique (α := A) (ι := PUnit.{u + 1}), top_himp]

theorem subsetB_pairB (x y z : AName.{u} A) :
    subsetB (pairB x y) z = memB x z ⊓ memB y z := by
  unfold pairB
  rw [subsetB_mk]
  refine le_antisymm ?_ ?_
  · refine le_inf ?_ ?_
    · have := iInf_le (fun b : ULift.{u} Bool =>
          (⊤ : A) ⇨ memB (if b.down then x else y) z) ⟨true⟩
      simpa using this
    · have := iInf_le (fun b : ULift.{u} Bool =>
          (⊤ : A) ⇨ memB (if b.down then x else y) z) ⟨false⟩
      simpa using this
  · refine le_iInf fun b => ?_
    rw [top_himp]
    rcases b with ⟨b⟩
    cases b <;> simp

theorem eqB_singletonB (x y : AName.{u} A) :
    eqB (singletonB x) (singletonB y) = eqB x y := by
  rw [eqB_eq_subset, subsetB_singletonB, subsetB_singletonB, memB_singletonB,
    memB_singletonB, eqB_comm (x := y) (y := x), inf_idem]

theorem eqB_pairB (x y u v : AName.{u} A) :
    eqB (pairB x y) (pairB u v) =
      (eqB x u ⊓ eqB y v) ⊔ (eqB x v ⊓ eqB y u) := by
  have hsub (a b c d : AName A) :
      subsetB (pairB a b) (pairB c d) = (eqB a c ⊔ eqB a d) ⊓ (eqB b c ⊔ eqB b d) := by
    rw [subsetB_pairB, memB_pairB, memB_pairB]
  rw [eqB_eq_subset, hsub x y u v, hsub u v x y, eqB_comm (x := u) (y := x),
    eqB_comm (x := v) (y := y), eqB_comm (x := v) (y := x), eqB_comm (x := u) (y := y)]
  set Ax := eqB x u
  set Bx := eqB x v
  set Cx := eqB y u
  set Dx := eqB y v
  change ((Ax ⊔ Bx) ⊓ (Cx ⊔ Dx)) ⊓ ((Ax ⊔ Cx) ⊓ (Bx ⊔ Dx)) = (Ax ⊓ Dx) ⊔ (Bx ⊓ Cx)
  have hre : ((Ax ⊔ Bx) ⊓ (Cx ⊔ Dx)) ⊓ ((Ax ⊔ Cx) ⊓ (Bx ⊔ Dx)) =
      ((Ax ⊔ Bx) ⊓ (Ax ⊔ Cx)) ⊓ ((Cx ⊔ Dx) ⊓ (Bx ⊔ Dx)) := by ac_rfl
  have h1 : (Ax ⊔ Bx) ⊓ (Ax ⊔ Cx) = Ax ⊔ Bx ⊓ Cx := (sup_inf_left Ax Bx Cx).symm
  have h2 : (Cx ⊔ Dx) ⊓ (Bx ⊔ Dx) = Dx ⊔ Bx ⊓ Cx := by
    calc (Cx ⊔ Dx) ⊓ (Bx ⊔ Dx)
        = (Dx ⊔ Cx) ⊓ (Dx ⊔ Bx) := by rw [sup_comm (a := Cx), sup_comm (a := Bx)]
      _ = Dx ⊔ Cx ⊓ Bx := (sup_inf_left Dx Cx Bx).symm
      _ = Dx ⊔ Bx ⊓ Cx := by rw [inf_comm (a := Cx)]
  rw [hre, h1, h2]
  have h3 : (Ax ⊔ Bx ⊓ Cx) ⊓ (Dx ⊔ Bx ⊓ Cx) = (Bx ⊓ Cx) ⊔ Ax ⊓ Dx := by
    rw [sup_comm (a := Ax), sup_comm (a := Dx)]
    exact (sup_inf_left (Bx ⊓ Cx) Ax Dx).symm
  rw [h3, sup_comm]

theorem eqB_pairB_of_eq (x y u v : AName.{u} A) :
    eqB x u ⊓ eqB y v ≤ eqB (pairB x y) (pairB u v) := by
  rw [eqB_pairB]
  exact le_sup_left

theorem eqB_singletonB_pairB (x u v : AName.{u} A) :
    eqB (singletonB x) (pairB u v) = eqB x u ⊓ eqB x v := by
  rw [eqB_eq_subset, subsetB_singletonB, subsetB_pairB, memB_pairB, memB_singletonB,
    memB_singletonB, eqB_comm (x := u) (y := x), eqB_comm (x := v) (y := x)]
  exact le_antisymm inf_le_right (le_inf (le_sup_of_le_left inf_le_left) le_rfl)

theorem eqB_opairB (x y u v : AName.{u} A) :
    eqB (opairB x y) (opairB u v) = eqB x u ⊓ eqB y v := by
  rw [opairB, opairB, eqB_pairB, eqB_singletonB, eqB_pairB, eqB_singletonB_pairB]
  have hR : eqB (pairB x y) (singletonB u) = eqB x u ⊓ eqB y u := by
    rw [eqB_comm, eqB_singletonB_pairB, eqB_comm (x := u) (y := x),
      eqB_comm (x := u) (y := y)]
  rw [hR]
  have htrans : eqB x u ⊓ eqB x v ⊓ eqB y u ≤ eqB y v := by
    have h1 : eqB y u ⊓ eqB u x ≤ eqB y x := eqB_trans y u x
    have h2 : eqB y x ⊓ eqB x v ≤ eqB y v := eqB_trans y x v
    refine le_trans ?_ h2
    refine le_inf ?_ ?_
    · refine le_trans ?_ h1
      rw [eqB_comm (x := u) (y := x)]
      exact le_inf inf_le_right (inf_le_of_left_le inf_le_left)
    · exact inf_le_of_left_le inf_le_right
  refine le_antisymm ?_ ?_
  · refine sup_le ?_ ?_
    · rw [inf_sup_left]
      refine sup_le inf_le_right ?_
      refine le_inf inf_le_left ?_
      exact htrans.trans' (le_of_eq (inf_assoc _ _ _).symm)
    · refine le_inf (inf_le_of_left_le inf_le_left) ?_
      exact htrans.trans' (le_inf inf_le_left (inf_le_of_right_le inf_le_right))
  · refine le_sup_of_le_left (le_inf inf_le_left (le_sup_of_le_left ?_))
    exact le_inf inf_le_left inf_le_right

theorem subsetB_of_le_val (X : AName.{u} A) (v : X.idx → A)
    (hv : ∀ i, v i ≤ X.val i) :
    subsetB (mk X.idx X.child v) X = ⊤ :=
  iInf_eq_top.mpr fun i => himp_eq_top_iff.mpr ((hv i).trans (val_le_memB X i))

theorem subsetB_restrictName_self (S X : AName.{u} A) :
    subsetB (restrictName S X) S = ⊤ :=
  iInf_eq_top.mpr fun _ => himp_eq_top_iff.mpr inf_le_right

theorem subsetB_le_subsetB_restrict (S X : AName.{u} A) :
    subsetB S X ≤ subsetB S (restrictName S X) := by
  refine le_iInf fun i => ?_
  rw [le_himp_iff]
  have hSX : subsetB S X ⊓ S.val i ≤ memB (S.child i) X := subsetB_apply S X i
  have hmemS : S.val i ≤ memB (S.child i) S := val_le_memB S i
  rw [memB_eq]
  have : subsetB S X ⊓ S.val i ≤
      (⨆ j, eqB (S.child i) (X.child j) ⊓ X.val j) ⊓ memB (S.child i) S :=
    le_inf (hSX.trans (le_of_eq (memB_eq (S.child i) X)))
      (inf_le_of_right_le hmemS)
  refine this.trans ?_
  rw [iSup_inf_eq]
  refine iSup_le fun j => ?_
  refine le_iSup_of_le j ?_
  have hchild : (restrictName S X).child j = X.child j := rfl
  have hval : (restrictName S X).val j = X.val j ⊓ memB (X.child j) S := rfl
  rw [hchild, hval]
  have hsubst : eqB (S.child i) (X.child j) ⊓ memB (S.child i) S ≤
      memB (X.child j) S := by
    rw [inf_comm]; exact memB_eqB_left (S.child i) S (X.child j)
  refine le_inf (inf_le_of_left_le inf_le_left) ?_
  refine le_inf (inf_le_of_left_le inf_le_right) ?_
  exact hsubst.trans' (le_inf (inf_le_of_left_le inf_le_left) inf_le_right)

theorem subsetB_le_eqB_restrict (S X : AName.{u} A) :
    subsetB S X ≤ eqB S (restrictName S X) := by
  rw [eqB_eq_subset, subsetB_restrictName_self, inf_top_eq]
  exact subsetB_le_subsetB_restrict S X

/-- Paper: `‖S ∈ P^A(X)‖ = ‖S ⊆ X‖`. -/
theorem memB_powerB (S X : AName.{u} A) :
    memB S (powerB X) = subsetB S X := by
  refine le_antisymm ?_ ?_
  · rw [memB_eq]
    refine iSup_le fun p => ?_
    have htop : subsetB (mk X.idx X.child p.1) X = ⊤ := subsetB_of_le_val X p.1 p.2
    have hle : eqB S (mk X.idx X.child p.1) ≤ subsetB S X := by
      have htrans := subsetB_trans S (mk X.idx X.child p.1) X
      rw [htop, inf_top_eq] at htrans
      exact (eqB_le_subsetB S (mk X.idx X.child p.1)).trans htrans
    exact inf_le_of_left_le hle
  · refine (subsetB_le_eqB_restrict S X).trans ?_
    rw [memB_eq]
    refine le_iSup_of_le ⟨fun i => X.val i ⊓ memB (X.child i) S, fun _ => inf_le_left⟩ ?_
    exact le_inf le_rfl le_top

theorem sepB_val (X : AName.{u} A) (φ : AName.{u} A → A) (i : X.idx) :
    (sepB X φ).val i = X.val i ⊓ φ (X.child i) :=
  rfl

theorem prodB_val (X Y : AName.{u} A) (i : X.idx) (j : Y.idx) :
    (prodB X Y).val (i, j) = memB (X.child i) X ⊓ memB (Y.child j) Y :=
  rfl

/-!
## Theorem 2 consequences: check commutes with finite set formers
-/

theorem check_insert (x y : PSet.{u}) :
    check (A := A) (insert x y) =
      mk (Option y.Type)
        (fun o => Option.casesOn o (check (A := A) x) (fun i => check (y.Func i)))
        (fun _ => ⊤) := by
  simp only [insert, PSet.insert]
  cases y with
  | mk α f =>
    rw [check_mk]
    refine congr_arg (fun child => mk (Option α) child (fun _ => ⊤)) ?_
    funext o
    cases o <;> rfl

theorem check_singleton (x : PSet.{u}) :
    eqB (check (A := A) ({x} : PSet)) (singletonB (check x)) = ⊤ := by
  have hx : ({x} : PSet) = insert x (∅ : PSet) := rfl
  rw [eqB_eq_subset, hx]
  refine inf_eq_top_iff.mpr ⟨?fwd, ?bwd⟩
  · rw [check_insert, subsetB_mk]
    refine iInf_eq_top.mpr fun o => himp_eq_top_iff.mpr ?_
    rw [memB_singletonB (A := A)]
    cases o with
    | none =>
      change ⊤ ≤ eqB (check (A := A) x) (check x)
      exact (eqB_self (A := A) (check x)).ge
    | some i =>
      have : IsEmpty (PSet.Type (∅ : PSet)) := inferInstance
      exact this.elim i
  · rw [subsetB_singletonB, check_insert, memB_mk]
    refine top_unique (le_iSup_of_le none ?_)
    simp [eqB_self (A := A)]

theorem check_pair (x y : PSet.{u}) :
    eqB (check (A := A) ({x, y} : PSet)) (pairB (check x) (check y)) = ⊤ := by
  have hxy : ({x, y} : PSet) = insert x ({y} : PSet) := rfl
  have hy : ({y} : PSet) = insert y (∅ : PSet) := rfl
  rw [eqB_eq_subset, hxy]
  refine inf_eq_top_iff.mpr ⟨?fwd, ?bwd⟩
  · rw [check_insert, subsetB_mk]
    refine iInf_eq_top.mpr fun o => himp_eq_top_iff.mpr ?_
    rw [memB_pairB (A := A)]
    cases o with
    | none => exact le_sup_of_le_left (eqB_self (A := A) (check x)).ge
    | some i =>
      revert i
      rw [hy]
      intro i
      cases i with
      | none =>
        simp [insert, PSet.insert]
        exact top_unique (le_sup_of_le_right (eqB_self (A := A) (check y)).ge)
      | some j =>
        have : IsEmpty (PSet.Type (∅ : PSet)) := inferInstance
        exact this.elim j
  · rw [subsetB_pairB]
    refine inf_eq_top_iff.mpr ⟨?hx, ?hy⟩
    · rw [check_insert, memB_mk]
      refine top_unique (le_iSup_of_le none ?_)
      simp [eqB_self (A := A)]
    · rw [check_insert, memB_mk, hy]
      refine top_unique (le_iSup_of_le (some none) ?_)
      simp [insert, PSet.insert]
      exact eqB_self (A := A) (check y)

theorem eqB_pairB_congr (x x' y y' : AName.{u} A) :
    eqB x x' ⊓ eqB y y' ≤ eqB (pairB x y) (pairB x' y') :=
  eqB_pairB_of_eq (x := x) (y := y) (u := x') (v := y')

theorem check_opair (x y : PSet.{u}) :
    eqB (check (A := A) (pOpair x y)) (opairB (check x) (check y)) = ⊤ := by
  unfold pOpair opairB
  have h₁ := check_pair (A := A) ({x} : PSet) ({x, y} : PSet)
  have h₂ := check_singleton (A := A) x
  have h₃ := check_pair (A := A) x y
  have hcong : eqB (check (A := A) ({x} : PSet)) (singletonB (check x)) ⊓
      eqB (check ({x, y} : PSet)) (pairB (check x) (check y)) ≤
      eqB (pairB (check ({x} : PSet)) (check ({x, y} : PSet)))
        (pairB (singletonB (check x)) (pairB (check x) (check y))) :=
    eqB_pairB_of_eq (A := A)
      (check (A := A) ({x} : PSet)) (check (A := A) ({x, y} : PSet))
      (singletonB (check (A := A) x))
      (pairB (check (A := A) x) (check y))
  have htop : eqB (check (A := A) ({x} : PSet)) (singletonB (check x)) ⊓
      eqB (check ({x, y} : PSet)) (pairB (check x) (check y)) = ⊤ := by
    rw [h₂, h₃, top_inf_eq]
  have hpair : eqB (check (A := A) (insert ({x} : PSet) {({x, y} : PSet)}))
      (pairB (check ({x} : PSet)) (check ({x, y} : PSet))) = ⊤ :=
    check_pair (A := A) ({x} : PSet) ({x, y} : PSet)
  refine top_unique ?_
  have := eqB_trans
    (check (A := A) (insert ({x} : PSet) {({x, y} : PSet)}))
    (pairB (check ({x} : PSet)) (check ({x, y} : PSet)))
    (pairB (singletonB (check x)) (pairB (check x) (check y)))
  exact (le_inf hpair.ge (htop.ge.trans hcong)).trans this

/-!
## Check of `ω`: inductive and least in `V^A`
-/

theorem insertB_check (x y : PSet.{u}) :
    insertB (check (A := A) x) (check y) = check (insert x y) := by
  rw [check_insert]
  unfold insertB
  cases y with
  | mk α f =>
    rw [check_mk]
    refine congr_arg₂ (fun c v => mk (Option α) c v)
      (funext fun o => by cases o <;> rfl)
      (funext fun o => by cases o <;> rfl)

theorem check_succ (n : ℕ) :
    check (A := A) (PSet.ofNat (n + 1)) = succB (check (PSet.ofNat n)) :=
  (insertB_check (PSet.ofNat n) (PSet.ofNat n)).symm

theorem subsetB_insertB (x y z : AName.{u} A) :
    subsetB (insertB x y) z = memB x z ⊓ subsetB y z := by
  have hx : insertB x y =
      mk (Option y.idx)
        (fun o => match o with | none => x | some i => y.child i)
        (fun o => match o with | none => ⊤ | some i => y.val i) := rfl
  rw [hx, subsetB_mk]
  refine le_antisymm ?_ ?_
  · refine le_inf ?_ ?_
    · exact (iInf_le _ none).trans (by simp [top_himp])
    · refine le_iInf fun i => iInf_le _ (some i)
  · refine le_iInf fun o => ?_
    cases o with
    | none =>
      simp [top_himp]
    | some i =>
      change memB x z ⊓ subsetB y z ≤ y.val i ⇨ memB (y.child i) z
      rw [le_himp_iff]
      refine le_trans ?_ (subsetB_apply y z i)
      exact le_inf (inf_le_of_left_le inf_le_right) inf_le_right

theorem eqB_insertB (x x' y y' : AName.{u} A) :
    eqB x x' ⊓ eqB y y' ≤ eqB (insertB x y) (insertB x' y') := by
  rw [eqB_eq_subset (x := insertB x y) (y := insertB x' y')]
  refine le_inf ?_ ?_
  · rw [subsetB_insertB, memB_insertB]
    refine le_inf ?_ ?_
    · exact inf_le_of_left_le (le_sup_of_le_left le_rfl)
    · have hsub : eqB y y' ≤ subsetB y (insertB x' y') := by
        have : subsetB y y' ≤ subsetB y (insertB x' y') := by
          refine le_iInf fun i => ?_
          rw [le_himp_iff]
          have := subsetB_apply y y' i
          refine this.trans ?_
          rw [memB_insertB]
          exact le_sup_right
        exact (eqB_le_subsetB y y').trans this
      exact inf_le_of_right_le hsub
  · rw [subsetB_insertB, memB_insertB, eqB_comm (x := x) (y := x'),
      eqB_comm (x := y) (y := y')]
    refine le_inf ?_ ?_
    · exact inf_le_of_left_le (le_sup_of_le_left le_rfl)
    · have hsub : eqB y' y ≤ subsetB y' (insertB x y) := by
        have : subsetB y' y ≤ subsetB y' (insertB x y) := by
          refine le_iInf fun i => ?_
          rw [le_himp_iff]
          have := subsetB_apply y' y i
          refine this.trans ?_
          rw [memB_insertB]
          exact le_sup_right
        exact (eqB_le_subsetB y' y).trans this
      exact inf_le_of_right_le hsub

theorem eqB_succB (n m : AName.{u} A) :
    eqB n m ≤ eqB (succB n) (succB m) :=
  (eqB_insertB n m n m).trans' (le_inf le_rfl le_rfl)

/-- `ωˇ` is inductive in `V^A`. Leastness is `check_omega_least`. -/
theorem check_omega_eq :
    check (A := A) PSet.omega =
      mk (ULift.{u} ℕ) (fun n => check (PSet.ofNat n.down)) (fun _ => ⊤) := by
  rw [show PSet.omega = PSet.mk (ULift.{u} ℕ) (fun n => PSet.ofNat n.down) from rfl]
  exact check_mk _ _

theorem check_omega_inductive :
    isInductiveB (A := A) (check PSet.omega) = ⊤ := by
  rw [isInductiveB, check_omega_eq]
  refine inf_eq_top_iff.mpr ⟨?empty, ?succ⟩
  · rw [memB_mk]
    refine top_unique (le_iSup_of_le (⟨0⟩ : ULift ℕ) ?_)
    simp [PSet.ofNat]
    exact eqB_self (A := A) (check ∅)
  · refine iInf_eq_top.mpr fun n => himp_eq_top_iff.mpr ?_
    rw [memB_mk]
    refine iSup_le fun k => ?_
    have hsucc : eqB n (check (A := A) (PSet.ofNat k.down)) ≤
        eqB (succB n) (succB (check (PSet.ofNat k.down))) :=
      eqB_succB (A := A) n (check (PSet.ofNat k.down))
    have hdef : succB (check (A := A) (PSet.ofNat k.down)) =
        check (PSet.ofNat (k.down + 1)) :=
      (check_succ (A := A) k.down).symm
    refine (inf_le_of_left_le hsucc).trans ?_
    rw [hdef, memB_mk]
    refine le_iSup_of_le (⟨k.down + 1⟩ : ULift ℕ) ?_
    exact le_inf le_rfl le_top

/-- Every von Neumann numeral is a member of an inductive name, by induction on `ℕ`. -/
theorem memB_check_ofNat_of_inductive (X : AName.{u} A)
    (h : isInductiveB X = ⊤) (n : ℕ) :
    memB (check (A := A) (PSet.ofNat n)) X = ⊤ := by
  have hparts := inf_eq_top_iff.mp h
  induction n with
  | zero =>
    exact hparts.1
  | succ n ih =>
    have hcl := iInf_eq_top.mp hparts.2 (check (A := A) (PSet.ofNat n))
    have hle : memB (check (A := A) (PSet.ofNat n)) X ≤
        memB (succB (check (PSet.ofNat n))) X :=
      himp_eq_top_iff.mp hcl
    have : memB (succB (check (A := A) (PSet.ofNat n))) X = ⊤ :=
      top_unique (ih.ge.trans hle)
    rwa [← check_succ (A := A) n] at this

/-- Leastness of `ωˇ`: if `X` is inductive at Boolean value 1, then `ωˇ ⊆ X`
at Boolean value 1. Together with `check_omega_inductive` this is the
Theorem 2 consequence that `ωˇ` is inductive and least (the `ω` of `V^A`).
The argument inducts on the `ULift ℕ` index of `check_omega_eq`, not on
ordinal rank. -/
theorem check_omega_least {X : AName.{u} A} (h : isInductiveB X = ⊤) :
    subsetB (check (A := A) PSet.omega) X = ⊤ := by
  rw [check_omega_eq, subsetB_mk]
  refine iInf_eq_top.mpr fun n => himp_eq_top_iff.mpr ?_
  exact (memB_check_ofNat_of_inductive (A := A) X h n.down).ge

/-!
## Finite subsets and CSL Proposition 3
-/

/-- `S` is finite: it equals some finite enumeration (external form of
`∃ n ∈ ω, ∃ f : n → V, S = im(f)`). -/
theorem check_pfinEnum {n : ℕ} (xs : Fin n → PSet.{u}) :
    check (A := A) (pfinEnum xs) = finsetB (fun i => check (xs i)) := by
  unfold pfinEnum finsetB
  rw [check_mk]

theorem eqB_finsetB {n : ℕ} (xs ys : Fin n → AName.{u} A) :
    (⨅ i, eqB (xs i) (ys i)) ≤ eqB (finsetB xs) (finsetB ys) := by
  rw [eqB_eq_subset]
  refine le_inf ?_ ?_
  · unfold finsetB
    rw [subsetB_mk]
    refine le_iInf fun i => ?_
    rw [top_himp, memB_mk]
    refine (iInf_le (fun j : Fin n => eqB (xs j) (ys j)) i.down).trans ?_
    exact le_iSup_of_le i (le_inf le_rfl le_top)
  · unfold finsetB
    rw [subsetB_mk]
    refine le_iInf fun i => ?_
    rw [top_himp, memB_mk]
    refine (iInf_le (fun j : Fin n => eqB (xs j) (ys j)) i.down).trans ?_
    refine le_iSup_of_le i ?_
    rw [eqB_comm]
    exact le_inf le_rfl le_top

theorem isFiniteB_congr (S T : AName.{u} A) :
    eqB S T ⊓ isFiniteB S ≤ isFiniteB T := by
  unfold isFiniteB
  rw [inf_iSup_eq]
  refine iSup_le fun n => ?_
  rw [inf_iSup_eq]
  refine iSup_le fun xs => ?_
  refine le_iSup_of_le n (le_iSup_of_le xs ?_)
  have : eqB T S ⊓ eqB S (finsetB xs) ≤ eqB T (finsetB xs) :=
    eqB_trans T S (finsetB xs)
  exact this.trans' (le_inf (by rw [eqB_comm]; exact inf_le_left) inf_le_right)

/-- Finite meets distribute over arbitrary joins (Sikorski 3.1.11). -/
theorem iInf_iSup_fun {n : ℕ} {ι : Type*} (f : Fin n → ι → A) :
    (⨅ i, ⨆ j, f i j) = ⨆ g : Fin n → ι, ⨅ i, f i (g i) := by
  induction n with
  | zero =>
    have : Nonempty (Fin 0 → ι) := ⟨fun i => nomatch i⟩
    have hL : (⨅ i : Fin 0, ⨆ j, f i j) = ⊤ := iInf_of_empty _
    have hR : (⨆ g : Fin 0 → ι, ⨅ i, f i (g i)) = ⊤ := by
      have hg : ∀ g : Fin 0 → ι, (⨅ i, f i (g i)) = ⊤ := fun _ => iInf_of_empty _
      simp_rw [hg]
      exact iSup_const
    rw [hL, hR]
  | succ n ih =>
    have hsplit : (⨅ i : Fin (n + 1), ⨆ j, f i j) =
        (⨆ j, f 0 j) ⊓ ⨅ i : Fin n, ⨆ j, f i.succ j :=
      D0Formula.iInf_fin_succ fun i => ⨆ j, f i j
    rw [hsplit, ih (fun i j => f i.succ j), inf_comm, iSup_inf_eq]
    refine le_antisymm ?fwd ?bwd
    · refine iSup_le fun g => ?_
      have hdis :
          (⨅ i : Fin n, f i.succ (g i)) ⊓ ⨆ a : ι, f 0 a =
            ⨆ a : ι, (⨅ i : Fin n, f i.succ (g i)) ⊓ f 0 a :=
        inf_iSup_eq (⨅ i : Fin n, f i.succ (g i)) (fun a : ι => f 0 a)
      rw [hdis]
      refine iSup_le fun a => ?_
      refine le_iSup_of_le (Fin.cons (α := fun _ : Fin (n + 1) => ι) a g) ?_
      have hcons :
          (⨅ i : Fin (n + 1),
              f i (Fin.cons (α := fun _ : Fin (n + 1) => ι) a g i)) =
            f 0 a ⊓ ⨅ i : Fin n, f i.succ (g i) := by
        rw [D0Formula.iInf_fin_succ
          (fun i => f i (Fin.cons (α := fun _ : Fin (n + 1) => ι) a g i))]
        simp [Fin.cons]
      rw [inf_comm]
      exact hcons.ge
    · refine iSup_le fun h => ?_
      refine le_iSup_of_le (fun i : Fin n => h i.succ) ?_
      refine le_inf ?_ ?_
      · exact le_iInf fun i => iInf_le (fun j : Fin (n + 1) => f j (h j)) i.succ
      · exact (iInf_le (fun j : Fin (n + 1) => f j (h j)) 0).trans
          (le_iSup (fun a : ι => f 0 a) (h 0))

theorem memB_sepB_ge (S X : AName.{u} A) (φ : AName.{u} A → A)
    (hcongr : ∀ x y, eqB x y ⊓ φ x ≤ φ y) :
    memB S X ⊓ φ S ≤ memB S (sepB X φ) := by
  rw [memB_eq, memB_eq, iSup_inf_eq]
  refine iSup_le fun i => ?_
  refine le_iSup_of_le i ?_
  have hchild : (sepB X φ).child i = X.child i := rfl
  have hval : (sepB X φ).val i = X.val i ⊓ φ (X.child i) := rfl
  rw [hchild, hval]
  refine le_inf (inf_le_of_left_le inf_le_left) ?_
  refine le_inf (inf_le_of_left_le inf_le_right) ?_
  exact (hcongr S (X.child i)).trans'
    (le_inf (inf_le_of_left_le inf_le_left) inf_le_right)

theorem subsetB_check_pfinEnum {n : ℕ} (X : PSet.{u})
    (g : Fin n → X.Type) :
    subsetB (check (A := A) (pfinEnum (fun i => X.Func (g i)))) (check X) = ⊤ := by
  cases X with
  | mk α f =>
    rw [check_pfinEnum, finsetB, subsetB_mk]
    refine iInf_eq_top.mpr fun i => himp_eq_top_iff.mpr ?_
    refine (eqB_self (A := A) (check (f (g i.down)))).ge.trans ?_
    rw [check_mk (A := A) α f, memB_mk]
    exact le_iSup_of_le (g i.down) (le_inf le_rfl le_top)

theorem check_pfin_mk {α : Type u} (f : α → PSet.{u}) :
    check (A := A) (pfin (PSet.mk α f)) =
      mk (Σ n : ℕ, ULift.{u} (Fin n → α))
        (fun p => check (pfinEnum (fun i => f (p.2.down i)))) (fun _ => ⊤) := by
  change check (A := A)
      (PSet.mk (Σ n : ℕ, ULift.{u} (Fin n → α))
        (fun p => pfinEnum (fun i => f (p.2.down i)))) = _
  rw [check_mk]

/-- CSL Proposition 3: `‖P_fin^A(Xˇ) = (P_fin X)ˇ‖ = 1`. -/
theorem proposition_3 (X : PSet.{u}) :
    eqB (pfinB (check (A := A) X)) (check (pfin X)) = ⊤ := by
  cases X with
  | mk α f =>
    rw [eqB_eq_subset]
    refine inf_eq_top_iff.mpr ⟨?fwd, ?bwd⟩
    · refine iInf_eq_top.mpr fun p => himp_eq_top_iff.mpr ?_
      set u := (pfinB (check (A := A) (PSet.mk α f))).child p
      have hval : (pfinB (check (A := A) (PSet.mk α f))).val p = isFiniteB u := by
        change ⊤ ⊓ isFiniteB u = isFiniteB u
        rw [top_inf_eq]
      rw [hval]
      have hu : u = mk (check (A := A) (PSet.mk α f)).idx
          (check (PSet.mk α f)).child p.1 := rfl
      have hsubU : subsetB u (check (PSet.mk α f)) = ⊤ := by
        rw [hu]
        exact subsetB_of_le_val (check (A := A) (PSet.mk α f)) p.1 p.2
      unfold isFiniteB
      refine iSup_le fun n => iSup_le fun xs => ?_
      have hmem : eqB (A := A) u (finsetB xs) ≤
          ⨅ i, memB (xs i) (check (PSet.mk α f)) := by
        have h1 : eqB u (finsetB xs) ≤ subsetB (finsetB xs) u := by
          rw [eqB_comm]
          exact eqB_le_subsetB (finsetB xs) u
        have h2 : eqB u (finsetB xs) ≤
            subsetB (finsetB xs) (check (PSet.mk α f)) :=
          (le_inf h1 (le_top.trans hsubU.ge)).trans
            (subsetB_trans (finsetB xs) u (check (PSet.mk α f)))
        unfold finsetB at h2
        rw [subsetB_mk] at h2
        refine h2.trans (le_iInf fun i => ?_)
        have hi := iInf_le (fun j : ULift.{u} (Fin n) =>
            (⊤ : A) ⇨ memB (xs j.down) (check (PSet.mk α f))) ⟨i⟩
        simpa [top_himp] using hi
      have hdist :
          (⨅ i, memB (xs i) (check (A := A) (PSet.mk α f))) =
            ⨆ g : Fin n → α, ⨅ i, eqB (xs i) (check (f (g i))) := by
        have : ∀ i, memB (xs i) (check (PSet.mk α f)) =
            ⨆ j : α, eqB (xs i) (check (f j)) := by
          intro i
          rw [check_mk, memB_mk]
          exact iSup_congr fun _ => inf_top_eq _
        simp only [this]
        exact iInf_iSup_fun fun i j => eqB (xs i) (check (f j))
      have heq := inf_eq_left.mpr hmem
      rw [← heq, hdist, inf_iSup_eq]
      refine iSup_le fun g => ?_
      have henum : (⨅ i, eqB (xs i) (check (A := A) (f (g i)))) ≤
          eqB (finsetB xs) (finsetB fun i => check (f (g i))) :=
        eqB_finsetB (A := A) xs fun i => check (f (g i))
      have hto : eqB u (finsetB xs) ⊓ eqB (finsetB xs)
          (finsetB fun i => check (f (g i))) ≤
          eqB u (finsetB fun i => check (f (g i))) :=
        eqB_trans u (finsetB xs) (finsetB fun i => check (f (g i)))
      refine ((le_inf inf_le_left (inf_le_of_right_le henum)).trans hto).trans ?_
      rw [← check_pfinEnum, check_pfin_mk, memB_mk]
      refine le_iSup_of_le (⟨n, ⟨g⟩⟩ : Σ k : ℕ, ULift.{u} (Fin k → α)) ?_
      exact le_inf le_rfl le_top
    · rw [check_pfin_mk, subsetB_mk]
      refine iInf_eq_top.mpr fun p => himp_eq_top_iff.mpr ?_
      set xs := fun i : Fin p.1 => f (p.2.down i)
      have hfin : isFiniteB (check (A := A) (pfinEnum xs)) = ⊤ := by
        unfold isFiniteB
        refine top_unique
          (le_iSup_of_le p.1 (le_iSup_of_le (fun i => check (xs i)) ?_))
        rw [← check_pfinEnum]
        exact (eqB_self (A := A) (check (pfinEnum xs))).ge
      have hsub : subsetB (check (A := A) (pfinEnum xs))
          (check (PSet.mk α f)) = ⊤ :=
        subsetB_check_pfinEnum (A := A) (PSet.mk α f) p.2.down
      have hpow : memB (check (A := A) (pfinEnum xs))
          (powerB (check (PSet.mk α f))) = ⊤ := by
        rw [memB_powerB, hsub]
      exact (le_inf hpow.ge hfin.ge).trans
        (memB_sepB_ge (A := A) (check (pfinEnum xs))
          (powerB (check (PSet.mk α f))) isFiniteB isFiniteB_congr)

/-!
## Internal functions and `Set_A` (CSL 2026, §2 last paragraph)

`isFunctionB F X Y` is the Boolean value of “`F ⊆ X ×_A Y` is a functional
total relation”. `funsB X Y` is `{F ∈ P^A(X ×_A Y) | isFunctionB F X Y}^A`.
`homB X Y` is `Set_A(X,Y)`: names with `‖F ∈ funsB X Y‖ = 1`, modulo
`‖F = G‖ = 1`. Identity is the identity relation; composition is relation
composition. This is not Theorem 1(i) or 1(ii).
-/

theorem eqB_top_memB_right {x y z : AName.{u} A} (h : eqB x y = ⊤) :
    memB z x = memB z y :=
  le_antisymm
    ((memB_eqB_right (A := A) x z y).trans' (by rw [h]; exact le_inf le_rfl le_top))
    ((memB_eqB_right (A := A) y z x).trans'
      (by rw [eqB_comm (x := y) (y := x), h]; exact le_inf le_rfl le_top))

theorem eqB_top_memB_left {x y z : AName.{u} A} (h : eqB x y = ⊤) :
    memB x z = memB y z :=
  le_antisymm
    ((memB_eqB_left (A := A) x z y).trans' (by rw [h]; exact le_inf le_rfl le_top))
    ((memB_eqB_left (A := A) y z x).trans'
      (by rw [eqB_comm (x := y) (y := x), h]; exact le_inf le_rfl le_top))

/-- `F = G` and `F ⊆ P` imply `G ⊆ P`. -/
theorem subsetB_of_eqB (F G P : AName.{u} A) :
    eqB F G ⊓ subsetB F P ≤ subsetB G P :=
  (le_inf (inf_le_of_left_le ((eqB_comm (A := A) F G).le.trans (eqB_le_subsetB G F)))
      inf_le_right).trans
    (AName.subsetB_trans G F P)

theorem memB_eqB_left' (x y z : AName.{u} A) :
    eqB z x ⊓ memB x y ≤ memB z y := by
  rw [inf_comm, eqB_comm (x := z) (y := x)]
  exact memB_eqB_left x y z

theorem inf_pair_le {a b c d u v : A} (hu : a ⊓ c ≤ u) (hv : b ⊓ d ≤ v) :
    (a ⊓ b) ⊓ (c ⊓ d) ≤ u ⊓ v :=
  le_inf
    (hu.trans' (le_inf (inf_le_of_left_le inf_le_left) (inf_le_of_right_le inf_le_left)))
    (hv.trans' (le_inf (inf_le_of_left_le inf_le_right) (inf_le_of_right_le inf_le_right)))

theorem inf_swap4 {a b c d : A} : (a ⊓ c) ⊓ (b ⊓ d) ≤ (a ⊓ b) ⊓ (c ⊓ d) :=
  le_inf (le_inf (inf_le_of_left_le inf_le_left) (inf_le_of_right_le inf_le_left))
    (le_inf (inf_le_of_left_le inf_le_right) (inf_le_of_right_le inf_le_right))

/-- `‖(x,y)^A ∈ X ×_A Y‖ = ‖x ∈ X‖ ⊓ ‖y ∈ Y‖`. -/
theorem memB_opairB_prodB (x y X Y : AName.{u} A) :
    memB (opairB x y) (prodB X Y) = memB x X ⊓ memB y Y := by
  unfold prodB
  rw [memB_mk]
  refine le_antisymm ?fwd ?bwd
  · refine iSup_le fun p => ?_
    rcases p with ⟨i, j⟩
    rw [eqB_opairB]
    exact inf_pair_le (A := A)
      (memB_eqB_left' (X.child i) X x) (memB_eqB_left' (Y.child j) Y y)
  · rw [memB_eq (x := x) (y := X), memB_eq (x := y) (y := Y), iSup_inf_eq]
    refine iSup_le fun i => ?_
    rw [inf_iSup_eq]
    refine iSup_le fun j => ?_
    refine le_iSup_of_le (i, j) ?_
    rw [eqB_opairB]
    exact (inf_swap4 (A := A)).trans
      (inf_le_inf le_rfl (inf_le_inf (val_le_memB X i) (val_le_memB Y j)))

theorem memB_sepB (S X : AName.{u} A) (φ : AName.{u} A → A)
    (hcongr : ∀ x y, eqB x y ⊓ φ x ≤ φ y) :
    memB S (sepB X φ) = memB S X ⊓ φ S := by
  refine le_antisymm ?le (memB_sepB_ge (A := A) S X φ hcongr)
  rw [memB_eq (x := S) (y := sepB X φ), memB_eq (x := S) (y := X)]
  refine iSup_le fun i => ?_
  have hchild : (sepB X φ).child i = X.child i := rfl
  have hval : (sepB X φ).val i = X.val i ⊓ φ (X.child i) := rfl
  rw [hchild, hval, ← inf_assoc]
  have hφ : eqB S (X.child i) ⊓ φ (X.child i) ≤ φ S := by
    rw [eqB_comm (x := S) (y := X.child i)]
    exact hcongr (X.child i) S
  refine le_inf ?_ ?_
  · exact le_iSup_of_le i inf_le_left
  · exact hφ.trans' (le_inf (inf_le_of_left_le inf_le_left) inf_le_right)

theorem isSingleValuedB_apply (F x y1 y2 : AName.{u} A) :
    isSingleValuedB F ⊓ memB (opairB x y1) F ⊓ memB (opairB x y2) F ≤ eqB y1 y2 := by
  have h := iInf_le (fun x' : AName A =>
      ⨅ y1' : AName A, ⨅ y2' : AName A,
        memB (opairB x' y1') F ⊓ memB (opairB x' y2') F ⇨ eqB y1' y2') x
  have h1 := (iInf_le (fun y1' : AName A =>
      ⨅ y2' : AName A,
        memB (opairB x y1') F ⊓ memB (opairB x y2') F ⇨ eqB y1' y2') y1).trans'
    h
  have h2 := (iInf_le (fun y2' : AName A =>
      memB (opairB x y1) F ⊓ memB (opairB x y2') F ⇨ eqB y1 y2') y2).trans' h1
  rw [inf_assoc]
  exact le_himp_iff.mp h2

theorem isTotalB_apply (F X x : AName.{u} A) :
    isTotalB F X ⊓ memB x X ≤ ⨆ y : AName.{u} A, memB (opairB x y) F :=
  le_himp_iff.mp (iInf_le (fun x' : AName A =>
      memB x' X ⇨ ⨆ y : AName A, memB (opairB x' y) F) x)

theorem isSingleValuedB_congr (F G : AName.{u} A) :
    eqB F G ⊓ isSingleValuedB F ≤ isSingleValuedB G := by
  refine le_iInf fun x => le_iInf fun y1 => le_iInf fun y2 => ?_
  rw [le_himp_iff]
  have hF1 : memB (opairB x y1) G ⊓ eqB G F ≤ memB (opairB x y1) F :=
    memB_eqB_right G (opairB x y1) F
  have hF2 : memB (opairB x y2) G ⊓ eqB G F ≤ memB (opairB x y2) F :=
    memB_eqB_right G (opairB x y2) F
  have hGF : eqB F G = eqB G F := eqB_comm F G
  refine (isSingleValuedB_apply F x y1 y2).trans' ?_
  refine le_inf (le_inf (inf_le_of_left_le inf_le_right) ?_) ?_
  · refine hF1.trans' ?_
    rw [← hGF]
    exact le_inf (inf_le_of_right_le inf_le_left) (inf_le_of_left_le inf_le_left)
  · refine hF2.trans' ?_
    rw [← hGF]
    exact le_inf (inf_le_of_right_le inf_le_right) (inf_le_of_left_le inf_le_left)

theorem isTotalB_congr (F G X : AName.{u} A) :
    eqB F G ⊓ isTotalB F X ≤ isTotalB G X := by
  refine le_iInf fun x => ?_
  rw [le_himp_iff]
  have htot : isTotalB F X ⊓ memB x X ≤ ⨆ y : AName A, memB (opairB x y) F :=
    isTotalB_apply F X x
  have hle : eqB F G ⊓ isTotalB F X ⊓ memB x X ≤
      eqB F G ⊓ ⨆ y : AName A, memB (opairB x y) F :=
    le_inf (inf_le_of_left_le inf_le_left)
      (htot.trans' (le_inf (inf_le_of_left_le inf_le_right) inf_le_right))
  refine hle.trans ?_
  rw [inf_iSup_eq]
  refine iSup_le fun y => le_iSup_of_le y ?_
  rw [inf_comm]
  exact memB_eqB_right F (opairB x y) G

theorem isFunctionB_congr (F G X Y : AName.{u} A) :
    eqB F G ⊓ isFunctionB F X Y ≤ isFunctionB G X Y := by
  unfold isFunctionB
  refine le_inf (le_inf ?sub ?sv) ?tot
  · exact (subsetB_of_eqB F G (prodB X Y)).trans'
      (le_inf inf_le_left (inf_le_of_right_le (inf_le_of_left_le inf_le_left)))
  · exact (isSingleValuedB_congr F G).trans'
      (le_inf inf_le_left (inf_le_of_right_le (inf_le_of_left_le inf_le_right)))
  · exact (isTotalB_congr F G X).trans'
      (le_inf inf_le_left (inf_le_of_right_le inf_le_right))

theorem memB_funsB (F X Y : AName.{u} A) :
    memB F (funsB X Y) = isFunctionB F X Y := by
  unfold funsB
  rw [memB_sepB (A := A) F (powerB (prodB X Y)) (fun G => isFunctionB G X Y)
      (fun G H => isFunctionB_congr G H X Y), memB_powerB]
  refine inf_eq_right.mpr ?_
  unfold isFunctionB
  exact inf_le_of_left_le inf_le_left

theorem memB_opairB_idB (x y X : AName.{u} A) :
    memB (opairB x y) (idB X) = memB x X ⊓ eqB x y := by
  unfold idB
  rw [memB_mk]
  refine le_antisymm ?fwd ?bwd
  · refine iSup_le fun i => ?_
    rw [eqB_opairB]
    have hx : eqB x (X.child i) ⊓ memB (X.child i) X ≤ memB x X :=
      memB_eqB_left' (X.child i) X x
    have heq : eqB x (X.child i) ⊓ eqB y (X.child i) ≤ eqB x y := by
      have : eqB y (X.child i) = eqB (X.child i) y :=
        eqB_comm (A := A) y (X.child i)
      rw [this]
      exact eqB_trans x (X.child i) y
    have h₁ : eqB x (X.child i) ⊓ eqB y (X.child i) ⊓ memB (X.child i) X ≤
        eqB x (X.child i) ⊓ memB (X.child i) X :=
      le_inf (inf_le_of_left_le inf_le_left) inf_le_right
    have h₂ : eqB x (X.child i) ⊓ eqB y (X.child i) ⊓ memB (X.child i) X ≤
        eqB x (X.child i) ⊓ eqB y (X.child i) :=
      inf_le_left
    exact le_inf (h₁.trans hx) (h₂.trans heq)
  · rw [memB_eq (x := x) (y := X), iSup_inf_eq]
    refine iSup_le fun i => ?_
    refine le_iSup_of_le i ?_
    rw [eqB_opairB]
    have hy : eqB x y ⊓ eqB x (X.child i) ≤ eqB y (X.child i) := by
      have : eqB x y = eqB y x := eqB_comm (A := A) x y
      rw [this]
      exact eqB_trans y x (X.child i)
    have h₁ : eqB x (X.child i) ⊓ X.val i ⊓ eqB x y ≤ eqB x (X.child i) :=
      inf_le_of_left_le inf_le_left
    have h₂ : eqB x (X.child i) ⊓ X.val i ⊓ eqB x y ≤ eqB y (X.child i) :=
      hy.trans' (le_inf inf_le_right (inf_le_of_left_le inf_le_left))
    have h₃ : eqB x (X.child i) ⊓ X.val i ⊓ eqB x y ≤ memB (X.child i) X :=
      inf_le_of_left_le (inf_le_of_right_le (val_le_memB X i))
    exact le_inf (le_inf h₁ h₂) h₃

theorem isFunctionB_id (X : AName.{u} A) :
    isFunctionB (idB X) X X = ⊤ := by
  unfold isFunctionB
  refine inf_eq_top_iff.mpr ⟨inf_eq_top_iff.mpr ⟨?sub, ?sv⟩, ?tot⟩
  · unfold idB
    rw [subsetB_mk]
    refine iInf_eq_top.mpr fun i => himp_eq_top_iff.mpr ?_
    rw [memB_opairB_prodB, inf_idem]
  · refine iInf_eq_top.mpr fun x => iInf_eq_top.mpr fun y1 =>
      iInf_eq_top.mpr fun y2 => himp_eq_top_iff.mpr ?_
    rw [memB_opairB_idB, memB_opairB_idB]
    have h : eqB x y1 ⊓ eqB x y2 ≤ eqB y1 y2 := by
      rw [eqB_comm (x := x) (y := y1)]
      exact eqB_trans y1 x y2
    exact h.trans'
      (le_inf (inf_le_of_left_le inf_le_right) (inf_le_of_right_le inf_le_right))
  · refine iInf_eq_top.mpr fun x => himp_eq_top_iff.mpr ?_
    refine le_iSup_of_le x ?_
    rw [memB_opairB_idB, eqB_self (A := A) x, inf_top_eq]

theorem memB_idB_funsB (X : AName.{u} A) :
    memB (idB X) (funsB X X) = ⊤ := by
  rw [memB_funsB, isFunctionB_id]

theorem memB_opairB_compB_le (g f : AName.{u} A) (X Z x z : AName.{u} A) :
    memB (opairB x z) (compB g f X Z) ≤
      ⨆ y : AName.{u} A, memB (opairB x y) f ⊓ memB (opairB y z) g := by
  unfold compB
  rw [memB_mk]
  refine iSup_le fun p => ?_
  rw [eqB_opairB, inf_iSup_eq]
  refine iSup_le fun y => ?_
  refine le_iSup_of_le y ?_
  have hx : eqB x (X.child p.1) ⊓ memB (opairB (X.child p.1) y) f ≤
      memB (opairB x y) f := by
    have heq : eqB (opairB x y) (opairB (X.child p.1) y) = eqB x (X.child p.1) := by
      rw [eqB_opairB, eqB_self (A := A) y, inf_top_eq]
    rw [← heq]
    exact memB_eqB_left' (opairB (X.child p.1) y) f (opairB x y)
  have hz : eqB z (Z.child p.2) ⊓ memB (opairB y (Z.child p.2)) g ≤
      memB (opairB y z) g := by
    have heq : eqB (opairB y z) (opairB y (Z.child p.2)) = eqB z (Z.child p.2) := by
      rw [eqB_opairB, eqB_self (A := A) y, top_inf_eq]
    rw [← heq]
    exact memB_eqB_left' (opairB y (Z.child p.2)) g (opairB y z)
  refine le_inf ?_ ?_
  · exact hx.trans' (le_inf (inf_le_of_left_le inf_le_left) (inf_le_of_right_le inf_le_left))
  · exact hz.trans' (le_inf (inf_le_of_left_le inf_le_right)
      (inf_le_of_right_le inf_le_right))

theorem inf_iSup_iSup {ι κ : Type*} (p : A) (a : ι → A) (b : κ → A) :
    p ⊓ (⨆ i, a i) ⊓ (⨆ k, b k) = ⨆ i, ⨆ k, p ⊓ a i ⊓ b k := by
  have h1 : p ⊓ (⨆ i, a i) ⊓ (⨆ k, b k) = (p ⊓ ⨆ k, b k) ⊓ ⨆ i, a i := by
    ac_rfl
  rw [h1, inf_iSup_eq]
  refine iSup_congr fun i => ?_
  have h2 : (p ⊓ ⨆ k, b k) ⊓ a i = (p ⊓ a i) ⊓ ⨆ k, b k := by
    ac_rfl
  rw [h2, inf_iSup_eq]

theorem le_memB_opairB_compB (g f : AName.{u} A) (X Y Z x y z : AName.{u} A)
    (hf : subsetB f (prodB X Y) = ⊤) (hg : subsetB g (prodB Y Z) = ⊤) :
    memB (opairB x y) f ⊓ memB (opairB y z) g ≤
      memB (opairB x z) (compB g f X Z) := by
  have hfmem : memB (opairB x y) f ≤ memB x X ⊓ memB y Y := by
    have := memB_of_subsetB (opairB x y) f (prodB X Y)
    rwa [hf, inf_top_eq, memB_opairB_prodB] at this
  have hgmem : memB (opairB y z) g ≤ memB y Y ⊓ memB z Z := by
    have := memB_of_subsetB (opairB y z) g (prodB Y Z)
    rwa [hg, inf_top_eq, memB_opairB_prodB] at this
  have hx : memB (opairB x y) f ⊓ memB (opairB y z) g ≤ memB x X :=
    inf_le_of_left_le (hfmem.trans inf_le_left)
  have hz : memB (opairB x y) f ⊓ memB (opairB y z) g ≤ memB z Z :=
    inf_le_of_right_le (hgmem.trans inf_le_right)
  have hkeep : memB (opairB x y) f ⊓ memB (opairB y z) g ≤
      memB (opairB x y) f ⊓ memB (opairB y z) g ⊓ memB x X ⊓ memB z Z :=
    le_inf (le_inf le_rfl hx) hz
  rw [memB_eq (x := x) (y := X), memB_eq (x := z) (y := Z),
    inf_iSup_iSup (A := A)] at hkeep
  refine hkeep.trans ?_
  refine iSup_le fun i => iSup_le fun k => ?_
  unfold compB
  rw [memB_mk]
  refine le_iSup_of_le (i, k) ?_
  rw [eqB_opairB]
  have hxF : eqB x (X.child i) ⊓ memB (opairB x y) f ≤
      memB (opairB (X.child i) y) f := by
    have heq : eqB (opairB x y) (opairB (X.child i) y) = eqB x (X.child i) := by
      rw [eqB_opairB, eqB_self (A := A) y, inf_top_eq]
    rw [← heq, inf_comm]
    exact memB_eqB_left (opairB x y) f (opairB (X.child i) y)
  have hzG : eqB z (Z.child k) ⊓ memB (opairB y z) g ≤
      memB (opairB y (Z.child k)) g := by
    have heq : eqB (opairB y z) (opairB y (Z.child k)) = eqB z (Z.child k) := by
      rw [eqB_opairB, eqB_self (A := A) y, top_inf_eq]
    rw [← heq, inf_comm]
    exact memB_eqB_left (opairB y z) g (opairB y (Z.child k))
  have hp : memB (opairB x y) f ⊓ memB (opairB y z) g ⊓
      (eqB x (X.child i) ⊓ X.val i) ⊓ (eqB z (Z.child k) ⊓ Z.val k) ≤
      memB (opairB x y) f ⊓ memB (opairB y z) g :=
    inf_le_of_left_le inf_le_left
  have ha : memB (opairB x y) f ⊓ memB (opairB y z) g ⊓
      (eqB x (X.child i) ⊓ X.val i) ⊓ (eqB z (Z.child k) ⊓ Z.val k) ≤
      eqB x (X.child i) :=
    inf_le_of_left_le (inf_le_of_right_le inf_le_left)
  have hb : memB (opairB x y) f ⊓ memB (opairB y z) g ⊓
      (eqB x (X.child i) ⊓ X.val i) ⊓ (eqB z (Z.child k) ⊓ Z.val k) ≤
      eqB z (Z.child k) :=
    inf_le_of_right_le inf_le_left
  refine le_inf (le_inf ha hb) ?_
  refine le_iSup_of_le y (le_inf ?_ ?_)
  · exact hxF.trans' (le_inf ha (hp.trans inf_le_left))
  · exact hzG.trans' (le_inf hb (hp.trans inf_le_right))

end Scott2026
