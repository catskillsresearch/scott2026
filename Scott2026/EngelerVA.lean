/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/

import Mathlib.Data.Finset.Sort
import Mathlib.Data.Nat.Pairing
import Scott2026.Engeler
import Scott2026.Oid

/-!
# Theorem 30: the Engeler model in `V^A`

The paper (CSL 2026, before Proposition 29) takes a set `E` with an injective
structure map `P_fin(E) × E → E`. The initial algebra of `P_fin × Id` is empty
and is not used. We construct such an `E` as `ℕ` / `ω`, internalize `·` and
`lam` on `P^A(check E)`, and prove the retract at Boolean value `⊤` by a
direct calculation on names. This is not Theorem 1(i), Definition 19 at `V^A`,
or an internal continuous lattice.
-/

universe u

namespace Scott2026

open AName

/-!
## The set `E` before Proposition 29
-/

/-- List encoding used to inject `List ℕ` into `ℕ`. The `+ 1` keeps the empty
list off the image of `Nat.pair`. -/
def listNatCode : List ℕ → ℕ
  | [] => 0
  | n :: ns => Nat.pair n (listNatCode ns) + 1

theorem listNatCode_injective : Function.Injective listNatCode := by
  intro xs
  induction xs with
  | nil =>
    intro ys h
    cases ys with
    | nil => rfl
    | cons b bs =>
      simp [listNatCode] at h
  | cons a as ih =>
    intro ys h
    cases ys with
    | nil =>
      simp [listNatCode] at h
    | cons b bs =>
      have hpair : Nat.pair a (listNatCode as) = Nat.pair b (listNatCode bs) :=
        Nat.succ_injective (by simpa [listNatCode] using h)
      have hab := Nat.pair_eq_pair.mp hpair
      exact congr_arg₂ List.cons hab.1 (ih hab.2)

/-- Injective pairing `P_fin(ℕ) × ℕ → ℕ` (paper before Proposition 29). -/
def engelerPair (p : Finset ℕ × ℕ) : ℕ :=
  Nat.pair (listNatCode (p.1.sort (· ≤ ·))) p.2

theorem sort_finset_injective :
    Function.Injective (fun s : Finset ℕ => s.sort (· ≤ ·)) := by
  intro s t h
  apply Finset.ext
  intro x
  rw [← Finset.mem_sort (s := s) (r := (· ≤ ·)) (a := x)]
  rw [show s.sort (· ≤ ·) = t.sort (· ≤ ·) from h]
  exact Finset.mem_sort (s := t) (r := (· ≤ ·)) (a := x)

theorem engelerPair_injective : Function.Injective engelerPair := by
  intro p q h
  have hpq := Nat.pair_eq_pair.mp h
  have hlist : p.1.sort (· ≤ ·) = q.1.sort (· ≤ ·) :=
    listNatCode_injective hpq.1
  exact Prod.ext (sort_finset_injective hlist) hpq.2

/-- The set `E` of the paper, as a pre-set: von Neumann `ω`. -/
def engelerE : PSet.{u} := PSet.omega

/-!
## Von Neumann numerals
-/

theorem ofNat_spec_sum.{v} (N : ℕ) :
    ∀ n m, n + m = N →
      (PSet.ofNat.{v} n ∈ PSet.ofNat.{v} m ↔ n < m) ∧
      (PSet.Equiv (PSet.ofNat.{v} n) (PSet.ofNat.{v} m) ↔ n = m) := by
  induction N using Nat.strongRecOn with
  | ind N ih =>
    have hmem : ∀ n m, n + m = N →
        (PSet.ofNat.{v} n ∈ PSet.ofNat.{v} m ↔ n < m) := by
      intro n m hN
      cases m with
      | zero =>
        constructor
        · intro h
          simp [PSet.ofNat] at h
        · intro h
          exact (Nat.not_lt_zero n h).elim
      | succ m =>
        change PSet.ofNat.{v} n ∈ insert (PSet.ofNat.{v} m) (PSet.ofNat.{v} m) ↔
          n < m + 1
        rw [PSet.mem_insert_iff]
        have hspec := ih (n + m) (by omega) n m rfl
        constructor
        · intro h
          rcases h with hE | hM
          · exact (hspec.2.mp hE) ▸ Nat.lt_succ_self m
          · exact Nat.lt_succ_of_lt (hspec.1.mp hM)
        · intro h
          rcases (le_iff_lt_or_eq.mp (Nat.lt_succ_iff.mp h)) with hlt | heq
          · exact Or.inr (hspec.1.mpr hlt)
          · exact Or.inl (hspec.2.mpr heq)
    have hequiv : ∀ n m, n + m = N →
        (PSet.Equiv (PSet.ofNat.{v} n) (PSet.ofNat.{v} m) ↔ n = m) := by
      intro n m hN
      constructor
      · intro hEqv
        by_contra hne
        rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
        · have hin : PSet.ofNat.{v} n ∈ PSet.ofNat.{v} m :=
            (hmem n m hN).mpr hlt
          exact PSet.mem_irrefl _
            ((@PSet.Mem.congr_right (PSet.ofNat.{v} n) (PSet.ofNat.{v} m) hEqv
              (PSet.ofNat.{v} n)).mpr hin)
        · have hin : PSet.ofNat.{v} m ∈ PSet.ofNat.{v} n :=
            (hmem m n (by omega)).mpr hgt
          exact PSet.mem_irrefl _
            ((@PSet.Mem.congr_right (PSet.ofNat.{v} m) (PSet.ofNat.{v} n) hEqv.symm
              (PSet.ofNat.{v} m)).mpr hin)
      · rintro rfl
        exact PSet.Equiv.rfl (x := PSet.ofNat.{v} n)
    exact fun n m hN => ⟨hmem n m hN, hequiv n m hN⟩

theorem ofNat_mem_iff {n m : ℕ} : PSet.ofNat.{u} n ∈ PSet.ofNat.{u} m ↔ n < m :=
  (ofNat_spec_sum.{u} (n + m) n m rfl).1

theorem ofNat_equiv_iff {n m : ℕ} :
    PSet.Equiv (PSet.ofNat.{u} n) (PSet.ofNat.{u} m) ↔ n = m :=
  (ofNat_spec_sum.{u} (n + m) n m rfl).2

/-!
## Check of equivalent pre-sets
-/

theorem eqB_check_of_equiv {A : Type u} [CompleteBooleanAlgebra A] :
    ∀ {x y : PSet.{u}}, PSet.Equiv x y →
      eqB (check (A := A) x) (check y) = ⊤ := by
  intro x
  induction x with
  | mk α f ih =>
    intro y h
    cases y with
    | mk β g =>
      rw [eqB_eq_subset]
      refine inf_eq_top_iff.mpr ⟨?fwd, ?bwd⟩
      · rw [check_mk, subsetB_mk]
        refine iInf_eq_top.mpr fun i => himp_eq_top_iff.mpr ?_
        obtain ⟨j, hij⟩ := h.1 i
        have hch : eqB (check (A := A) (f i)) (check (g j)) = ⊤ := ih i hij
        rw [check_mk (A := A), memB_mk]
        have : (⊤ : A) ≤ eqB (check (A := A) (f i)) (check (g j)) ⊓ ⊤ := by
          rw [hch, top_inf_eq]
        exact this.trans
          (le_iSup (fun k => eqB (check (A := A) (f i)) (check (g k)) ⊓ (⊤ : A)) j)
      · rw [check_mk, subsetB_mk]
        refine iInf_eq_top.mpr fun j => himp_eq_top_iff.mpr ?_
        obtain ⟨i, hji⟩ := h.2 j
        have hch : eqB (check (A := A) (f i)) (check (g j)) = ⊤ := ih i hji
        rw [eqB_comm (x := check (A := A) (f i)) (y := check (g j))] at hch
        rw [check_mk (A := A), memB_mk]
        have : (⊤ : A) ≤ eqB (check (A := A) (g j)) (check (f i)) ⊓ ⊤ := by
          rw [hch, top_inf_eq]
        exact this.trans
          (le_iSup (fun k => eqB (check (A := A) (g j)) (check (f k)) ⊓ (⊤ : A)) i)

theorem memB_check_of_mem {A : Type u} [CompleteBooleanAlgebra A]
    {x y : PSet.{u}} (h : x ∈ y) :
    memB (check (A := A) x) (check y) = ⊤ := by
  obtain ⟨i, hi⟩ := h
  cases y with
  | mk β g =>
    rw [check_mk, memB_mk]
    exact top_unique
      ((eqB_check_of_equiv (A := A) hi).ge.trans
        (le_iSup_of_le i (le_inf le_rfl le_top)))

/-!
## Finite subsets of `ω` as pre-sets
-/

/-- Finite subset of `ω` indexed by the elements of `K`. -/
def finsetPSet (K : Finset ℕ) : PSet.{u} :=
  PSet.mk (ULift.{u} {n : ℕ // n ∈ K}) (fun n => PSet.ofNat n.down.val)

theorem orderEmb_symm_apply (K : Finset ℕ) (n : {n : ℕ // n ∈ K}) :
    K.orderEmbOfFin rfl ((K.orderIsoOfFin rfl).symm n) = n.1 :=
  (Finset.coe_orderIsoOfFin_apply K rfl ((K.orderIsoOfFin rfl).symm n)).trans
    (congrArg Subtype.val ((K.orderIsoOfFin rfl).apply_symm_apply n))

theorem finsetPSet_equiv_enum (K : Finset ℕ) :
    PSet.Equiv.{u, u} (finsetPSet K)
      (pfinEnum (fun i : Fin K.card => PSet.ofNat.{u} (K.orderEmbOfFin rfl i))) :=
  ⟨fun i =>
    ⟨⟨(K.orderIsoOfFin rfl).symm i.down⟩, by
      change PSet.Equiv.{u, u} (PSet.ofNat.{u} i.down.val)
        (PSet.ofNat.{u} (K.orderEmbOfFin rfl ((K.orderIsoOfFin rfl).symm i.down)))
      rw [orderEmb_symm_apply K i.down]⟩,
    fun j =>
      ⟨⟨K.orderEmbOfFin rfl j.down, K.orderEmbOfFin_mem rfl j.down⟩,
        PSet.Equiv.refl (PSet.ofNat.{u} (K.orderEmbOfFin rfl j.down))⟩⟩

theorem finsetPSet_mem_pfin (K : Finset ℕ) :
    finsetPSet K ∈ pfin (PSet.omega : PSet.{u}) := by
  refine ⟨⟨K.card, ⟨fun i => ⟨K.orderEmbOfFin rfl i⟩⟩⟩, ?_⟩
  simpa [pfin, PSet.omega, pfinEnum] using finsetPSet_equiv_enum K

variable {A : Type u} [CompleteBooleanAlgebra A]

theorem memB_check_ofNat_omega (n : ℕ) :
    memB (check (A := A) (PSet.ofNat n)) (check PSet.omega) = ⊤ :=
  memB_check_of_mem (A := A) ⟨⟨n⟩, PSet.Equiv.rfl⟩

theorem subsetB_finsetPSet (K : Finset ℕ) (X : AName.{u} A) :
    subsetB (check (A := A) (finsetPSet K)) X =
      ⨅ n : {n : ℕ // n ∈ K}, memB (check (PSet.ofNat n.1)) X := by
  rw [finsetPSet, check_mk, subsetB_mk]
  refine le_antisymm ?_ ?_
  · refine le_iInf fun n => ?_
    have := iInf_le (fun i : ULift.{u} {n : ℕ // n ∈ K} =>
        (⊤ : A) ⇨ memB (check (PSet.ofNat i.down.val)) X) ⟨n⟩
    simpa [top_himp] using this
  · refine le_iInf fun i => ?_
    rw [top_himp]
    exact iInf_le (fun n : {n : ℕ // n ∈ K} =>
      memB (check (PSet.ofNat n.1)) X) i.down

/-- Proposition 3 moves checked finite subsets into `P_fin^A(check ω)`. -/
theorem memB_finsetPSet_pfinB (K : Finset ℕ) :
    memB (check (A := A) (finsetPSet K)) (pfinB (check PSet.omega)) = ⊤ := by
  have hcheck : memB (check (A := A) (finsetPSet K)) (check (pfin PSet.omega)) = ⊤ :=
    memB_check_of_mem (A := A) (finsetPSet_mem_pfin K)
  have hprop3 : eqB (pfinB (check (A := A) PSet.omega)) (check (pfin PSet.omega)) = ⊤ :=
    proposition_3 (A := A) PSet.omega
  rw [eqB_top_memB_right (x := pfinB (check (A := A) PSet.omega))
    (y := check (pfin PSet.omega)) hprop3]
  exact hcheck

/-!
## Check of the classical pairing
-/

/-- Check of the classical Engeler pairing on a finite set and an atom. -/
noncomputable def pairApplyB (K : Finset ℕ) (q : ℕ) : AName.{u} A :=
  check (PSet.ofNat (engelerPair (K, q)))

theorem pairApplyB_mem_omega (K : Finset ℕ) (q : ℕ) :
    memB (pairApplyB (A := A) K q) (check PSet.omega) = ⊤ :=
  memB_check_ofNat_omega (engelerPair (K, q))

/-- Kuratowski pair of a checked finite subset and a checked atom. -/
noncomputable def pairDomainB (K : Finset ℕ) (q : ℕ) : AName.{u} A :=
  opairB (check (finsetPSet K)) (check (PSet.ofNat q))

theorem pairDomainB_mem_prod_check (K : Finset ℕ) (q : ℕ) :
    memB (pairDomainB (A := A) K q)
      (prodB (check (pfin PSet.omega)) (check PSet.omega)) = ⊤ := by
  rw [pairDomainB, memB_opairB_prodB]
  exact inf_eq_top_iff.mpr
    ⟨memB_check_of_mem (A := A) (finsetPSet_mem_pfin K), memB_check_ofNat_omega q⟩

/-- By Proposition 3, the same pair lands in `P_fin^A(check ω) ×_A check ω`. -/
theorem pairDomainB_mem_prod_pfinB (K : Finset ℕ) (q : ℕ) :
    memB (pairDomainB (A := A) K q)
      (prodB (pfinB (check PSet.omega)) (check PSet.omega)) = ⊤ := by
  rw [pairDomainB, memB_opairB_prodB]
  exact inf_eq_top_iff.mpr ⟨memB_finsetPSet_pfinB K, memB_check_ofNat_omega q⟩

theorem pairApplyB_eqB_iff [Nontrivial A] {K₁ K₂ : Finset ℕ} {q₁ q₂ : ℕ} :
    eqB (A := A) (pairApplyB K₁ q₁) (pairApplyB K₂ q₂) = ⊤ ↔
      K₁ = K₂ ∧ q₁ = q₂ := by
  constructor
  · intro h
    have hequiv :=
      (check_atomic (A := A) (PSet.ofNat (engelerPair (K₁, q₁)))
        (PSet.ofNat (engelerPair (K₂, q₂)))).1.mp h
    exact Prod.mk_inj.mp (engelerPair_injective (ofNat_equiv_iff.mp hequiv))
  · rintro ⟨rfl, rfl⟩
    exact eqB_self (A := A) _

theorem ofNat_mem_finsetPSet {K : Finset ℕ} {n : ℕ} :
    PSet.ofNat.{u} n ∈ finsetPSet K ↔ n ∈ K := by
  constructor
  · intro hmem
    obtain ⟨⟨m, hm⟩, hmn⟩ := hmem
    change PSet.Equiv (PSet.ofNat.{u} n) (PSet.ofNat.{u} m) at hmn
    exact ofNat_equiv_iff.mp hmn ▸ hm
  · intro hn
    exact ⟨⟨n, hn⟩, PSet.Equiv.rfl⟩

/-- Injectivity of the checked pairing on crisp arguments, via `eqB_opairB`. -/
theorem pairDomainB_injective [Nontrivial A] {K₁ K₂ : Finset ℕ} {q₁ q₂ : ℕ}
    (h : eqB (A := A) (pairDomainB K₁ q₁) (pairDomainB K₂ q₂) = ⊤) :
    K₁ = K₂ ∧ q₁ = q₂ := by
  have hsplit :
      eqB (A := A) (check (finsetPSet K₁)) (check (finsetPSet K₂)) ⊓
        eqB (check (PSet.ofNat q₁)) (check (PSet.ofNat q₂)) = ⊤ := by
    rwa [pairDomainB, pairDomainB, eqB_opairB] at h
  have hq : q₁ = q₂ :=
    ofNat_equiv_iff.mp
      ((check_atomic (A := A) (PSet.ofNat q₁) (PSet.ofNat q₂)).1.mp
        (top_unique (hsplit.ge.trans inf_le_right)))
  have hK : PSet.Equiv (finsetPSet K₁) (finsetPSet K₂) :=
    (check_atomic (A := A) (finsetPSet K₁) (finsetPSet K₂)).1.mp
      (top_unique (hsplit.ge.trans inf_le_left))
  refine ⟨?_, hq⟩
  ext n
  rw [← ofNat_mem_finsetPSet (K := K₁) (n := n),
    ← ofNat_mem_finsetPSet (K := K₂) (n := n)]
  exact PSet.equiv_iff_mem.mp hK

/-- The checked pairing is an injective map on crisp elements of
`P_fin^A(check E) ×_A check E` (Proposition 3 + `eqB_opairB`). -/
theorem theorem_30_pair_injective [Nontrivial A] {K₁ K₂ : Finset ℕ} {q₁ q₂ : ℕ}
    (h : eqB (A := A) (pairApplyB K₁ q₁) (pairApplyB K₂ q₂) = ⊤) :
    eqB (A := A) (pairDomainB K₁ q₁) (pairDomainB K₂ q₂) = ⊤ := by
  obtain ⟨rfl, rfl⟩ := (pairApplyB_eqB_iff (A := A)).mp h
  exact eqB_self (A := A) _

/-!
## Internal `lam` and `·` on names
-/

/-- Characteristic canonical index of a finite set of numerals. -/
noncomputable def finsetToPowerIdx (K : Finset ℕ) :
    (powerB (check (A := A) PSet.omega)).idx :=
  restrictPowerIdx (check (finsetPSet K)) (check (A := A) PSet.omega)

noncomputable def finsetToCanonical (K : Finset ℕ) :
    CanonicalPowerIdx (check (A := A) PSet.omega) :=
  normalizePowerIdx (check (A := A) PSet.omega) (finsetToPowerIdx (A := A) K)

/-- Boolean value of `∃ K finite, q ∈ f(K)` along ground finite sets. -/
noncomputable def finiteApproxPred
    (f : CanonicalPowerIdx (check (A := A) PSet.omega) →
      CanonicalPowerIdx (check (A := A) PSet.omega))
    (X q : AName.{u} A) : A :=
  ⨆ K : Finset ℕ, ⨆ n : ℕ,
    eqB q (check (PSet.ofNat n)) ⊓
      subsetB (check (finsetPSet K)) X ⊓
      memB (check (PSet.ofNat n))
        ((powerB (check (A := A) PSet.omega)).child (f (finsetToCanonical (A := A) K)).1)

theorem finiteApproxPred_congr
    (f : CanonicalPowerIdx (check (A := A) PSet.omega) →
      CanonicalPowerIdx (check (A := A) PSet.omega))
    (X q q' : AName.{u} A) :
    eqB q q' ⊓ finiteApproxPred (A := A) f X q ≤
      finiteApproxPred (A := A) f X q' := by
  unfold finiteApproxPred
  rw [inf_iSup_eq]
  refine iSup_le fun K => ?_
  rw [inf_iSup_eq]
  refine iSup_le fun n => ?_
  refine le_iSup_of_le K (le_iSup_of_le n ?_)
  have htrans : eqB q q' ⊓ eqB q (check (PSet.ofNat n)) ≤
      eqB q' (check (PSet.ofNat n)) := by
    rw [eqB_comm (x := q) (y := q')]
    exact eqB_trans q' q (check (PSet.ofNat n))
  refine le_inf (le_inf ?_ (inf_le_of_right_le (inf_le_of_left_le inf_le_right)))
    (inf_le_of_right_le inf_le_right)
  exact htrans.trans'
    (le_inf inf_le_left (inf_le_of_right_le (inf_le_of_left_le inf_le_left)))

/-- Internal application:
`F · X = {q | ∃ K ∈ P_fin^A(check E). K ⊆ X ∧ (K,q) ∈ F}`,
interpreted on ground finite sets (Proposition 3). -/
noncomputable def engelerAppPred (F X q : AName.{u} A) : A :=
  ⨆ K : Finset ℕ, ⨆ n : ℕ,
    eqB q (check (PSet.ofNat n)) ⊓
      subsetB (check (finsetPSet K)) X ⊓
      memB (pairApplyB (A := A) K n) F

theorem engelerAppPred_congr (F X q q' : AName.{u} A) :
    eqB q q' ⊓ engelerAppPred F X q ≤ engelerAppPred F X q' := by
  unfold engelerAppPred
  rw [inf_iSup_eq]
  refine iSup_le fun K => ?_
  rw [inf_iSup_eq]
  refine iSup_le fun n => ?_
  refine le_iSup_of_le K (le_iSup_of_le n ?_)
  have htrans : eqB q q' ⊓ eqB q (check (PSet.ofNat n)) ≤
      eqB q' (check (PSet.ofNat n)) := by
    rw [eqB_comm (x := q) (y := q')]
    exact eqB_trans q' q (check (PSet.ofNat n))
  refine le_inf (le_inf ?_ (inf_le_of_right_le (inf_le_of_left_le inf_le_right)))
    (inf_le_of_right_le inf_le_right)
  exact htrans.trans'
    (le_inf inf_le_left (inf_le_of_right_le (inf_le_of_left_le inf_le_left)))

noncomputable def engelerAppName (F X : AName.{u} A) : AName.{u} A :=
  sepB (check PSet.omega) (engelerAppPred F X)

theorem memB_engelerAppName (F X q : AName.{u} A) :
    memB q (engelerAppName F X) =
      memB q (check PSet.omega) ⊓ engelerAppPred F X q :=
  memB_sepB q (check PSet.omega) (engelerAppPred F X) (engelerAppPred_congr F X)

/-- Internal abstraction: `lam(f) = {(K,q) | q ∈ f(K)}`. -/
noncomputable def engelerLamPred
    (f : CanonicalPowerIdx (check (A := A) PSet.omega) →
      CanonicalPowerIdx (check (A := A) PSet.omega))
    (x : AName.{u} A) : A :=
  ⨆ K : Finset ℕ, ⨆ n : ℕ,
    eqB x (pairApplyB (A := A) K n) ⊓
      memB (check (PSet.ofNat n))
        ((powerB (check (A := A) PSet.omega)).child
          (f (finsetToCanonical (A := A) K)).1)

theorem engelerLamPred_congr
    (f : CanonicalPowerIdx (check (A := A) PSet.omega) →
      CanonicalPowerIdx (check (A := A) PSet.omega))
    (x x' : AName.{u} A) :
    eqB x x' ⊓ engelerLamPred (A := A) f x ≤ engelerLamPred (A := A) f x' := by
  unfold engelerLamPred
  rw [inf_iSup_eq]
  refine iSup_le fun K => ?_
  rw [inf_iSup_eq]
  refine iSup_le fun n => ?_
  refine le_iSup_of_le K (le_iSup_of_le n ?_)
  have htrans : eqB x x' ⊓ eqB x (pairApplyB (A := A) K n) ≤
      eqB x' (pairApplyB (A := A) K n) := by
    rw [eqB_comm (x := x) (y := x')]
    exact eqB_trans x' x (pairApplyB (A := A) K n)
  exact le_inf
    (htrans.trans' (le_inf inf_le_left (inf_le_of_right_le inf_le_left)))
    (inf_le_of_right_le inf_le_right)

noncomputable def engelerLamName
    (f : CanonicalPowerIdx (check (A := A) PSet.omega) →
      CanonicalPowerIdx (check (A := A) PSet.omega)) : AName.{u} A :=
  sepB (check PSet.omega) (engelerLamPred (A := A) f)

theorem memB_engelerLamName
    (f : CanonicalPowerIdx (check (A := A) PSet.omega) →
      CanonicalPowerIdx (check (A := A) PSet.omega))
    (x : AName.{u} A) :
    memB x (engelerLamName (A := A) f) =
      memB x (check PSet.omega) ⊓ engelerLamPred (A := A) f x :=
  memB_sepB x (check PSet.omega) (engelerLamPred (A := A) f)
    (engelerLamPred_congr (A := A) f)

theorem subsetB_sepB_omega (φ : AName.{u} A → A) :
    subsetB (sepB (check (A := A) PSet.omega) φ) (check PSet.omega) = ⊤ := by
  refine iInf_eq_top.mpr fun i => himp_eq_top_iff.mpr ?_
  have hle : (sepB (check (A := A) PSet.omega) φ).val i ≤
      (check (A := A) PSet.omega).val i := inf_le_left
  exact hle.trans (val_le_memB (check (A := A) PSet.omega) i)

/-!
## Canonical-carrier operations
-/

noncomputable def engelerLamVA
    (f : CanonicalPowerIdx (check (A := A) PSet.omega) →
      CanonicalPowerIdx (check (A := A) PSet.omega)) :
    CanonicalPowerIdx (check (A := A) PSet.omega) :=
  ⟨restrictPowerIdx (engelerLamName (A := A) f) (check (A := A) PSet.omega),
    restrictPowerIdx_isCanonical _ _⟩

noncomputable def engelerAppVA
    (F X : CanonicalPowerIdx (check (A := A) PSet.omega)) :
    CanonicalPowerIdx (check (A := A) PSet.omega) :=
  ⟨restrictPowerIdx
      (engelerAppName ((powerB (check (A := A) PSet.omega)).child F.1)
        ((powerB (check (A := A) PSet.omega)).child X.1))
      (check (A := A) PSet.omega),
    restrictPowerIdx_isCanonical _ _⟩

theorem engelerLamVA_eqB
    (f : CanonicalPowerIdx (check (A := A) PSet.omega) →
      CanonicalPowerIdx (check (A := A) PSet.omega)) :
    eqB ((powerB (check (A := A) PSet.omega)).child (engelerLamVA (A := A) f).1)
      (engelerLamName (A := A) f) = ⊤ := by
  rw [eqB_comm]
  exact eqB_restrictName_of_subsetB _ _ (subsetB_sepB_omega _)

theorem engelerAppVA_eqB
    (F X : CanonicalPowerIdx (check (A := A) PSet.omega)) :
    eqB ((powerB (check (A := A) PSet.omega)).child (engelerAppVA (A := A) F X).1)
      (engelerAppName ((powerB (check (A := A) PSet.omega)).child F.1)
        ((powerB (check (A := A) PSet.omega)).child X.1)) = ⊤ := by
  rw [eqB_comm]
  exact eqB_restrictName_of_subsetB _ _ (subsetB_sepB_omega _)

/-- `A`-valued determined-by-finite condition: `f(X)` is the join of `f(K)`
over ground finite `K ⊆ X`. This is the Proposition 29 criterion, internalized
at Boolean value `⊤`. -/
def DeterminedByFiniteVA
    (f : CanonicalPowerIdx (check (A := A) PSet.omega) →
      CanonicalPowerIdx (check (A := A) PSet.omega)) : Prop :=
  ∀ X : CanonicalPowerIdx (check (A := A) PSet.omega),
    eqB ((powerB (check (A := A) PSet.omega)).child (f X).1)
      (sepB (check PSet.omega) (finiteApproxPred (A := A) f
        ((powerB (check (A := A) PSet.omega)).child X.1))) = ⊤

/-!
## Retract calculation
-/

theorem eqB_check_ofNat_bot [Nontrivial A] {n m : ℕ} (hne : n ≠ m) :
    eqB (A := A) (check (PSet.ofNat n)) (check (PSet.ofNat m)) = ⊥ :=
  (check_atomic (A := A) (PSet.ofNat n) (PSet.ofNat m)).2.1.mpr
    (mt ofNat_equiv_iff.mp hne)

theorem memB_pairApplyB_lam
    (f : CanonicalPowerIdx (check (A := A) PSet.omega) →
      CanonicalPowerIdx (check (A := A) PSet.omega))
    (K : Finset ℕ) (n : ℕ) :
    memB (pairApplyB (A := A) K n) (engelerLamName (A := A) f) =
      memB (check (PSet.ofNat n))
        ((powerB (check (A := A) PSet.omega)).child
          (f (finsetToCanonical (A := A) K)).1) := by
  rw [memB_engelerLamName, pairApplyB_mem_omega, top_inf_eq]
  unfold engelerLamPred
  refine le_antisymm ?le ?ge
  · refine iSup_le fun K' => iSup_le fun n' => ?_
    rcases subsingleton_or_nontrivial A with hA | hA
    · exact (Subsingleton.elim (α := A) _ _).le
    · have : Nontrivial A := hA
      cases eq_or_ne (engelerPair (K, n)) (engelerPair (K', n')) with
      | inl hpair =>
        obtain ⟨rfl, rfl⟩ := Prod.mk_inj.mp (engelerPair_injective hpair)
        exact inf_le_right
      | inr hne =>
        have hbot : eqB (A := A) (pairApplyB K n) (pairApplyB K' n') = ⊥ :=
          eqB_check_ofNat_bot (A := A) hne
        rw [hbot, bot_inf_eq]
        exact bot_le (α := A)
  · refine le_iSup_of_le K (le_iSup_of_le n ?_)
    rw [eqB_self (A := A) (pairApplyB K n), top_inf_eq]

theorem memB_check_ofNat_app_lam
    (f : CanonicalPowerIdx (check (A := A) PSet.omega) →
      CanonicalPowerIdx (check (A := A) PSet.omega))
    (X : CanonicalPowerIdx (check (A := A) PSet.omega))
    (n : ℕ) :
    memB (check (PSet.ofNat n))
        (engelerAppName (engelerLamName (A := A) f)
          ((powerB (check (A := A) PSet.omega)).child X.1)) =
      ⨆ K : Finset ℕ,
        subsetB (check (finsetPSet K))
            ((powerB (check (A := A) PSet.omega)).child X.1) ⊓
          memB (check (PSet.ofNat n))
            ((powerB (check (A := A) PSet.omega)).child
              (f (finsetToCanonical (A := A) K)).1) := by
  rw [memB_engelerAppName, memB_check_ofNat_omega, top_inf_eq]
  unfold engelerAppPred
  refine le_antisymm ?le ?ge
  · refine iSup_le fun K => iSup_le fun m => ?_
    rcases subsingleton_or_nontrivial A with hA | hA
    · exact (Subsingleton.elim (α := A) _ _).le
    · have : Nontrivial A := hA
      cases eq_or_ne n m with
      | inl hnm =>
        subst hnm
        rw [memB_pairApplyB_lam]
        exact le_iSup_of_le K
          (le_inf (inf_le_of_left_le inf_le_right) inf_le_right)
      | inr hne =>
        have hbot : eqB (A := A) (check (PSet.ofNat n)) (check (PSet.ofNat m)) = ⊥ :=
          eqB_check_ofNat_bot (A := A) hne
        rw [hbot]
        simp only [bot_inf_eq]
        exact bot_le (α := A)
  · refine iSup_le fun K => ?_
    refine le_iSup_of_le K (le_iSup_of_le n ?_)
    rw [memB_pairApplyB_lam, eqB_self (A := A) (check (PSet.ofNat n)), top_inf_eq]

theorem finiteApproxPred_check_ofNat
    (f : CanonicalPowerIdx (check (A := A) PSet.omega) →
      CanonicalPowerIdx (check (A := A) PSet.omega))
    (X : CanonicalPowerIdx (check (A := A) PSet.omega))
    (n : ℕ) :
    finiteApproxPred (A := A) f
        ((powerB (check (A := A) PSet.omega)).child X.1)
        (check (PSet.ofNat n)) =
      ⨆ K : Finset ℕ,
        subsetB (check (finsetPSet K))
            ((powerB (check (A := A) PSet.omega)).child X.1) ⊓
          memB (check (PSet.ofNat n))
            ((powerB (check (A := A) PSet.omega)).child
              (f (finsetToCanonical (A := A) K)).1) := by
  unfold finiteApproxPred
  refine le_antisymm ?le ?ge
  · refine iSup_le fun K => iSup_le fun m => ?_
    rcases subsingleton_or_nontrivial A with hA | hA
    · exact (Subsingleton.elim (α := A) _ _).le
    · have : Nontrivial A := hA
      cases eq_or_ne n m with
      | inl hnm =>
        subst hnm
        exact le_iSup_of_le K
          (le_inf (inf_le_of_left_le inf_le_right) inf_le_right)
      | inr hne =>
        have hbot : eqB (A := A) (check (PSet.ofNat n)) (check (PSet.ofNat m)) = ⊥ :=
          eqB_check_ofNat_bot (A := A) hne
        rw [hbot]
        simp only [bot_inf_eq]
        exact bot_le (α := A)
  · refine iSup_le fun K =>
      le_iSup_of_le K (le_iSup_of_le n ?_)
    rw [eqB_self (A := A) (check (PSet.ofNat n)), top_inf_eq]

theorem memB_sepB_finiteApprox
    (f : CanonicalPowerIdx (check (A := A) PSet.omega) →
      CanonicalPowerIdx (check (A := A) PSet.omega))
    (X : CanonicalPowerIdx (check (A := A) PSet.omega))
    (n : ℕ) :
    memB (check (PSet.ofNat n))
        (sepB (check PSet.omega) (finiteApproxPred (A := A) f
          ((powerB (check (A := A) PSet.omega)).child X.1))) =
      ⨆ K : Finset ℕ,
        subsetB (check (finsetPSet K))
            ((powerB (check (A := A) PSet.omega)).child X.1) ⊓
          memB (check (PSet.ofNat n))
            ((powerB (check (A := A) PSet.omega)).child
              (f (finsetToCanonical (A := A) K)).1) := by
  rw [memB_sepB (check (PSet.ofNat n)) (check PSet.omega)
      (finiteApproxPred (A := A) f _) (finiteApproxPred_congr (A := A) f _),
    memB_check_ofNat_omega, top_inf_eq, finiteApproxPred_check_ofNat]

theorem canonical_val_eq_memB
    (p : CanonicalPowerIdx (check (A := A) PSet.omega)) (n : ℕ) :
    p.1.1 ⟨n⟩ =
      memB (check (PSet.ofNat n))
        ((powerB (check (A := A) PSet.omega)).child p.1) := by
  have hrestr :
      (restrictPowerIdx ((powerB (check (A := A) PSet.omega)).child p.1)
        (check (A := A) PSet.omega)).1 ⟨n⟩ = p.1.1 ⟨n⟩ :=
    congrArg (fun v : (powerB (check (A := A) PSet.omega)).idx => v.1 ⟨n⟩) p.2
  change (⊤ : A) ⊓
      memB (check (PSet.ofNat n))
        ((powerB (check (A := A) PSet.omega)).child p.1) = p.1.1 ⟨n⟩ at hrestr
  rw [top_inf_eq] at hrestr
  exact hrestr.symm

/-- On the canonical carrier, numeral membership determines Boolean equality. -/
theorem eqB_canonical_of_memB_ofNat
    {p q : CanonicalPowerIdx (check (A := A) PSet.omega)}
    (h : ∀ n : ℕ,
      memB (check (PSet.ofNat n))
          ((powerB (check (A := A) PSet.omega)).child p.1) =
      memB (check (PSet.ofNat n))
          ((powerB (check (A := A) PSet.omega)).child q.1)) :
    eqB ((powerB (check (A := A) PSet.omega)).child p.1)
      ((powerB (check (A := A) PSet.omega)).child q.1) = ⊤ := by
  have hpq : p = q := by
    refine Subtype.ext ?_
    refine Subtype.ext (funext fun i => ?_)
    cases i
    rename_i n
    rw [canonical_val_eq_memB (A := A) p n, canonical_val_eq_memB (A := A) q n, h n]
  rw [hpq]
  exact eqB_self _

theorem engelerAppPred_eqB {F F' X : AName.{u} A} (h : eqB F F' = ⊤)
    (q : AName.{u} A) :
    engelerAppPred F X q = engelerAppPred F' X q := by
  unfold engelerAppPred
  refine iSup_congr fun K => iSup_congr fun n => ?_
  rw [eqB_top_memB_right h]

theorem engelerAppName_eqB {F F' X : AName.{u} A} (h : eqB F F' = ⊤) :
    eqB (engelerAppName F X) (engelerAppName F' X) = ⊤ := by
  have : engelerAppPred F X = engelerAppPred F' X :=
    funext (engelerAppPred_eqB h)
  unfold engelerAppName
  rw [this]
  exact eqB_self _

/-- Theorem 30, retract at Boolean value `⊤`:
`‖lam(f) · X = f(X)‖ = 1` for determined-by-finite `f`. -/
theorem engelerVA_retract
    (f : CanonicalPowerIdx (check (A := A) PSet.omega) →
      CanonicalPowerIdx (check (A := A) PSet.omega))
    (hf : DeterminedByFiniteVA (A := A) f)
    (X : CanonicalPowerIdx (check (A := A) PSet.omega)) :
    eqB ((powerB (check (A := A) PSet.omega)).child
        (engelerAppVA (A := A) (engelerLamVA (A := A) f) X).1)
      ((powerB (check (A := A) PSet.omega)).child (f X).1) = ⊤ := by
  refine eqB_canonical_of_memB_ofNat (A := A) fun n => ?_
  have happ : memB (check (PSet.ofNat n))
      ((powerB (check (A := A) PSet.omega)).child
        (engelerAppVA (A := A) (engelerLamVA (A := A) f) X).1) =
      memB (check (PSet.ofNat n))
        (engelerAppName
          ((powerB (check (A := A) PSet.omega)).child (engelerLamVA (A := A) f).1)
          ((powerB (check (A := A) PSet.omega)).child X.1)) :=
    eqB_top_memB_right (engelerAppVA_eqB (A := A) (engelerLamVA (A := A) f) X)
  have hlam : eqB
      ((powerB (check (A := A) PSet.omega)).child (engelerLamVA (A := A) f).1)
      (engelerLamName (A := A) f) = ⊤ :=
    engelerLamVA_eqB (A := A) f
  have happ' : memB (check (PSet.ofNat n))
      (engelerAppName
        ((powerB (check (A := A) PSet.omega)).child (engelerLamVA (A := A) f).1)
        ((powerB (check (A := A) PSet.omega)).child X.1)) =
      memB (check (PSet.ofNat n))
        (engelerAppName (engelerLamName (A := A) f)
          ((powerB (check (A := A) PSet.omega)).child X.1)) :=
    eqB_top_memB_right (engelerAppName_eqB hlam)
  have hfX : memB (check (PSet.ofNat n))
      ((powerB (check (A := A) PSet.omega)).child (f X).1) =
      memB (check (PSet.ofNat n))
        (sepB (check PSet.omega) (finiteApproxPred (A := A) f
          ((powerB (check (A := A) PSet.omega)).child X.1))) :=
    eqB_top_memB_right (hf X)
  rw [happ, happ', hfX, memB_check_ofNat_app_lam, memB_sepB_finiteApprox]

theorem engelerVA_retract_oid
    (f : CanonicalPowerIdx (check (A := A) PSet.omega) →
      CanonicalPowerIdx (check (A := A) PSet.omega))
    (hf : DeterminedByFiniteVA (A := A) f)
    (X : CanonicalPowerIdx (check (A := A) PSet.omega)) :
    (canonicalPowerSetoid (check (A := A) PSet.omega)).eq
      (engelerAppVA (A := A) (engelerLamVA (A := A) f) X) (f X) = ⊤ := by
  rw [canonicalPowerSetoid_eq, oid_eq_powerB]
  exact engelerVA_retract (A := A) f hf X

/-!
## Ground pairing retract (Proposition 29 on the constructed `E`)
-/

theorem engelerPair_prop29_retract {f : Set ℕ → Set ℕ}
    (hf : DeterminedByFinite f) (X : Set ℕ) :
    engelerApp engelerPair (engelerLam engelerPair f) X = f X :=
  prop29_retract engelerPair engelerPair_injective hf X

/-!
## Theorem 30 package
-/

/-- Theorem 30 data: an `A`-valued reflexive dcpo recorded as the poset
`‖⊆‖`, application, abstraction, and the retract at Boolean value `⊤` for
maps determined by finite sets. This is not Definition 19 inside `V^A`. -/
structure AValuedReflexiveDcpo (A : Type u) [CompleteBooleanAlgebra A]
    (X : Type u) where
  poset : APoset (A := A) X
  app : X → X → X
  lam : (X → X) → X
  determined : (X → X) → Prop
  retract : ∀ f x, determined f → poset.eq (app (lam f) x) (f x) = ⊤

/-- Theorem 30: `(P^A(check E), ‖⊆‖, ·, lam)` is an `A`-valued reflexive dcpo
on the canonical carrier (operations and retract at `⊤`). Strictness is the
canonical-carrier fact `canonicalPowerSetoid_isStrict`; the raw index carrier
is not claimed strict. -/
noncomputable def engelerVA_model :
    AValuedReflexiveDcpo A
      (CanonicalPowerIdx (check (A := A) PSet.omega)) where
  poset := canonicalPowerPoset (check (A := A) PSet.omega)
  app := engelerAppVA (A := A)
  lam := engelerLamVA (A := A)
  determined := DeterminedByFiniteVA (A := A)
  retract f X hf := by
    rw [canonicalPowerPoset_eq]
    exact engelerVA_retract_oid (A := A) f hf X

theorem engelerVA_complete :
    (canonicalPowerSetoid (check (A := A) PSet.omega)).IsComplete :=
  canonicalPowerSetoid_isComplete _

theorem engelerVA_total :
    (canonicalPowerSetoid (check (A := A) PSet.omega)).IsTotal :=
  canonicalPowerSetoid_isTotal _

theorem engelerVA_strict :
    (canonicalPowerSetoid (check (A := A) PSet.omega)).IsStrict :=
  canonicalPowerSetoid_isStrict _

/-- Theorem 30: the packaged `A`-valued reflexive dcpo
`(P^A(check E), ‖⊆‖, ·, lam)` on the canonical carrier. -/
theorem engelerVA :
    (engelerVA_model (A := A)).poset =
      canonicalPowerPoset (check (A := A) PSet.omega) ∧
    (∀ F X, (engelerVA_model (A := A)).app F X =
      engelerAppVA (A := A) F X) ∧
    (∀ f, (engelerVA_model (A := A)).lam f = engelerLamVA (A := A) f) ∧
    (∀ f X, DeterminedByFiniteVA (A := A) f →
      (canonicalPowerSetoid (check (A := A) PSet.omega)).eq
        (engelerAppVA (A := A) (engelerLamVA (A := A) f) X) (f X) = ⊤) ∧
    (canonicalPowerSetoid (check (A := A) PSet.omega)).IsComplete ∧
    (canonicalPowerSetoid (check (A := A) PSet.omega)).IsTotal ∧
    (canonicalPowerSetoid (check (A := A) PSet.omega)).IsStrict :=
  ⟨rfl, fun _ _ => rfl, fun _ => rfl,
    fun f X hf => engelerVA_retract_oid (A := A) f hf X,
    engelerVA_complete (A := A), engelerVA_total (A := A),
    engelerVA_strict (A := A)⟩

end Scott2026
