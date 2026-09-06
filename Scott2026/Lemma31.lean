/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/

import Scott2026.InterpVA

/-!
# Lemma 31: check commutation of the Engeler interpretation

Furber–Mardare–Panangaden–Scott, CSL 2026, Lemma 31. For a pure term
`M ∈ Λ(Var)` and a valuation `ρ` with `fv(M) ⊆ dom(ρ)`,

  `‖⟦check M⟧^A_{check ρ} = ⟦M⟧_ρ‖ = 1`

on `P^A(check E)` versus `P(E)`. The closed case follows from
`∅ = check ∅`.

Ground interpretation uses the same pairing as the VA model:
`engelerReflexiveDcpo engelerPair engelerPair_injective`. The VA side
is `interpVA` / `interpClosedVA` on `EngelerCarrier`.
-/

universe u

namespace Scott2026

open AName
open Classical

variable {A : Type u} [CompleteBooleanAlgebra A]

noncomputable section

/-- Ground Engeler dcpo with the Theorem 30 pairing. -/
abbrev engelerDcpo : ReflexiveDcpo (Set ℕ) :=
  engelerReflexiveDcpo engelerPair engelerPair_injective

/-!
## Check of ground sets
-/

/-- Arbitrary subset of `ω` indexed by its elements (mirrors `finsetPSet`). -/
def setPSet (S : Set ℕ) : PSet.{u} :=
  PSet.mk (ULift.{u} {n : ℕ // n ∈ S}) (fun n => PSet.ofNat n.down.val)

theorem ofNat_mem_setPSet {S : Set ℕ} {n : ℕ} :
    PSet.ofNat.{u} n ∈ setPSet S ↔ n ∈ S := by
  constructor
  · intro hmem
    obtain ⟨⟨m, hm⟩, hmn⟩ := hmem
    change PSet.Equiv (PSet.ofNat.{u} n) (PSet.ofNat.{u} m) at hmn
    exact ofNat_equiv_iff.mp hmn ▸ hm
  · intro hn
    exact ⟨⟨n, hn⟩, PSet.Equiv.rfl⟩

/-- Children of `setPSet` are von Neumann numerals, so inequivalent
ground sets of `ℕ` remain inequivalent as pre-sets. -/
theorem setPSet_equiv_iff {S T : Set ℕ} :
    PSet.Equiv.{u, u} (setPSet S) (setPSet T) ↔ S = T := by
  constructor
  · intro h
    ext n
    constructor
    · intro hn
      exact ofNat_mem_setPSet.mp
        ((PSet.Mem.congr_right (x := setPSet S) (y := setPSet T) h).mp
          (ofNat_mem_setPSet.mpr hn))
    · intro hn
      exact ofNat_mem_setPSet.mp
        ((PSet.Mem.congr_right (x := setPSet T) (y := setPSet S) h.symm).mp
          (ofNat_mem_setPSet.mpr hn))
  · rintro rfl
    exact PSet.Equiv.rfl (x := setPSet S)

theorem setPSet_not_equiv_of_ne {S T : Set ℕ} (hne : S ≠ T) :
    ¬ PSet.Equiv.{u, u} (setPSet S) (setPSet T) :=
  mt setPSet_equiv_iff.mp hne

theorem subsetB_setPSet (S : Set ℕ) (X : AName.{u} A) :
    subsetB (check (A := A) (setPSet S)) X =
      ⨅ n : {n : ℕ // n ∈ S}, memB (check (PSet.ofNat n.1)) X := by
  rw [setPSet, check_mk, subsetB_mk]
  refine le_antisymm ?_ ?_
  · refine le_iInf fun n => ?_
    have := iInf_le (fun i : ULift.{u} {n : ℕ // n ∈ S} =>
        (⊤ : A) ⇨ memB (check (PSet.ofNat i.down.val)) X) ⟨n⟩
    simpa [top_himp] using this
  · refine le_iInf fun i => ?_
    rw [top_himp]
    exact iInf_le (fun n : {n : ℕ // n ∈ S} =>
      memB (check (PSet.ofNat n.1)) X) i.down

theorem subsetB_setPSet_omega (S : Set ℕ) :
    subsetB (check (A := A) (setPSet S)) (check PSet.omega) = ⊤ := by
  rw [subsetB_setPSet]
  exact iInf_eq_top.mpr fun _ => memB_check_ofNat_omega _

theorem memB_check_ofNat_setPSet (S : Set ℕ) (n : ℕ) :
    memB (check (A := A) (PSet.ofNat n)) (check (setPSet S)) =
      if n ∈ S then ⊤ else ⊥ := by
  rw [setPSet, check_mk, memB_mk]
  by_cases hn : n ∈ S
  · rw [if_pos hn]
    refine top_unique (le_iSup_of_le ⟨⟨n, hn⟩⟩ ?_)
    rw [eqB_self (A := A), top_inf_eq]
  · rw [if_neg hn]
    refine le_antisymm ?_ bot_le
    refine iSup_le fun i => ?_
    rcases subsingleton_or_nontrivial A with hA | hA
    · exact (Subsingleton.elim (α := A) _ _).le
    · have : Nontrivial A := hA
      have hne : n ≠ i.down.val := fun h => hn (h ▸ i.down.property)
      rw [eqB_check_ofNat_bot (A := A) hne, bot_inf_eq]

noncomputable def setToPowerIdx (S : Set ℕ) :
    (powerB (check (A := A) PSet.omega)).idx :=
  restrictPowerIdx (check (setPSet S)) (check (A := A) PSet.omega)

/-- Check/embedding of a ground `Set ℕ` into the Theorem 30 carrier. -/
noncomputable def setToCanonical (S : Set ℕ) : EngelerCarrier (A := A) :=
  normalizePowerIdx (check (A := A) PSet.omega) (setToPowerIdx (A := A) S)

theorem eqB_setToCanonical (S : Set ℕ) :
    eqB (childΩ (A := A) (setToCanonical (A := A) S))
      (check (setPSet S)) = ⊤ := by
  have hnorm : eqB
      ((powerB (check (A := A) PSet.omega)).child
        (setToCanonical (A := A) S).1)
      ((powerB (check (A := A) PSet.omega)).child
        (setToPowerIdx (A := A) S)) = ⊤ := by
    rw [eqB_comm]
    exact normalizePowerIdx_eqB (check (A := A) PSet.omega)
      (setToPowerIdx (A := A) S)
  have hrest : eqB
      ((powerB (check (A := A) PSet.omega)).child
        (setToPowerIdx (A := A) S))
      (check (setPSet S)) = ⊤ := by
    rw [setToPowerIdx, restrictPowerIdx_child, eqB_comm]
    exact eqB_restrictName_of_subsetB _ _ (subsetB_setPSet_omega S)
  exact eqB_top_trans (A := A) hnorm hrest

theorem memOfNat_setToCanonical (S : Set ℕ) (n : ℕ) :
    memOfNat (A := A) (setToCanonical (A := A) S) n =
      if n ∈ S then ⊤ else ⊥ := by
  have h := eqB_setToCanonical (A := A) S
  unfold memOfNat
  rw [eqB_top_memB_right h, memB_check_ofNat_setPSet]

theorem setToCanonical_coe (K : Finset ℕ) :
    setToCanonical (A := A) (↑K) = finsetToCanonical (A := A) K := by
  have hmem : ∀ n : ℕ,
      memB (check (PSet.ofNat n))
          ((powerB (check (A := A) PSet.omega)).child
            (setToCanonical (A := A) (↑K : Set ℕ)).1) =
      memB (check (PSet.ofNat n))
          ((powerB (check (A := A) PSet.omega)).child
            (finsetToCanonical (A := A) K).1) := by
    intro n
    change memOfNat (A := A) (setToCanonical (A := A) (↑K : Set ℕ)) n =
      memOfNat (A := A) (finsetToCanonical (A := A) K) n
    rw [memOfNat_setToCanonical, memB_finsetToCanonical]
    by_cases hn : n ∈ K
    · rw [if_pos (Finset.mem_coe.mpr hn), if_pos hn]
    · rw [if_neg (mt Finset.mem_coe.mp hn), if_neg hn]
  have heq : eqB (childΩ (A := A) (setToCanonical (A := A) (↑K : Set ℕ)))
      (childΩ (finsetToCanonical (A := A) K)) = ⊤ :=
    eqB_canonical_of_memB_ofNat (A := A) hmem
  refine (canonicalPowerSetoid_isStrict (check (A := A) PSet.omega))
    (setToCanonical (A := A) (↑K : Set ℕ)) (finsetToCanonical (A := A) K) ?_
  rw [canonicalPowerSetoid_eq, oid_eq_powerB]
  exact heq

theorem setToCanonical_empty :
    setToCanonical (A := A) (∅ : Set ℕ) = finsetToCanonical (A := A) ∅ := by
  simpa using setToCanonical_coe (A := A) (∅ : Finset ℕ)

/-!
## Finite-subset Boolean value against a checked ground set
-/

theorem subsetB_finsetPSet_setPSet (K : Finset ℕ) (S : Set ℕ) :
    subsetB (check (A := A) (finsetPSet K)) (check (setPSet S)) =
      ⨅ k : {k // k ∈ K}, if k.1 ∈ S then (⊤ : A) else ⊥ := by
  rw [subsetB_finsetPSet]
  refine iInf_congr fun k => memB_check_ofNat_setPSet (A := A) S k.1

theorem subsetB_finsetPSet_setPSet_eq (K : Finset ℕ) (S : Set ℕ) :
    subsetB (check (A := A) (finsetPSet K)) (check (setPSet S)) =
      if (↑K : Set ℕ) ⊆ S then ⊤ else ⊥ := by
  rw [subsetB_finsetPSet_setPSet]
  rcases subsingleton_or_nontrivial A with hA | hA
  · exact Subsingleton.elim _ _
  · clear hA
    by_cases hKS : (↑K : Set ℕ) ⊆ S
    · rw [if_pos hKS]
      refine iInf_eq_top.mpr fun k => ?_
      have hk : k.1 ∈ S := hKS (Finset.mem_coe.mpr k.2)
      rw [if_pos hk]
    · rw [if_neg hKS]
      obtain ⟨k, hkK, hkS⟩ := Set.not_subset.mp hKS
      have hkK' : k ∈ K := Finset.mem_coe.mp hkK
      refine le_antisymm ?_ bot_le
      have hle := iInf_le (fun k : {k // k ∈ K} =>
          if k.1 ∈ S then (⊤ : A) else ⊥) ⟨k, hkK'⟩
      rw [if_neg hkS] at hle
      exact hle

theorem eqB_ofNat_pairApplyB (n : ℕ) (K : Finset ℕ) (m : ℕ) :
    eqB (A := A) (check (PSet.ofNat n)) (pairApplyB K m) =
      if n = engelerPair (K, m) then ⊤ else ⊥ := by
  rcases subsingleton_or_nontrivial A with hA | hA
  · exact Subsingleton.elim _ _
  · have : Nontrivial A := hA
    by_cases h : n = engelerPair (K, m)
    · rw [if_pos h, h, pairApplyB, eqB_self (A := A)]
    · rw [if_neg h, pairApplyB, eqB_check_ofNat_bot (A := A) h]

theorem iSup_indicator_engelerApp (S_M S_N : Set ℕ) (n : ℕ) :
    (⨆ K : Finset ℕ,
      (if (↑K : Set ℕ) ⊆ S_N then (⊤ : A) else ⊥) ⊓
        (if engelerPair (K, n) ∈ S_M then ⊤ else ⊥)) =
      if n ∈ engelerApp engelerPair S_M S_N then ⊤ else ⊥ := by
  rcases subsingleton_or_nontrivial A with hA | hA
  · exact Subsingleton.elim _ _
  · have : Nontrivial A := hA
    by_cases hn : n ∈ engelerApp engelerPair S_M S_N
    · rw [if_pos hn]
      rw [engelerApp, Set.mem_setOf_eq] at hn
      obtain ⟨K, hK, hp⟩ := hn
      refine top_unique (le_iSup_of_le K ?_)
      rw [if_pos hK, if_pos hp, top_inf_eq]
    · rw [if_neg hn]
      refine le_antisymm ?_ bot_le
      refine iSup_le fun K => ?_
      by_cases hK : (↑K : Set ℕ) ⊆ S_N
      · by_cases hp : engelerPair (K, n) ∈ S_M
        · have : n ∈ engelerApp engelerPair S_M S_N := by
            rw [engelerApp, Set.mem_setOf_eq]
            exact ⟨K, hK, hp⟩
          exact (hn this).elim
        · rw [if_pos hK, if_neg hp, inf_bot_eq]
      · rw [if_neg hK, bot_inf_eq]

theorem iSup_indicator_engelerLam (f : Set ℕ → Set ℕ) (n : ℕ) :
    (⨆ K : Finset ℕ, ⨆ m : ℕ,
      (if n = engelerPair (K, m) then (⊤ : A) else ⊥) ⊓
        (if m ∈ f (↑K) then ⊤ else ⊥)) =
      if n ∈ engelerLam engelerPair f then ⊤ else ⊥ := by
  rcases subsingleton_or_nontrivial A with hA | hA
  · exact Subsingleton.elim _ _
  · have : Nontrivial A := hA
    by_cases hn : n ∈ engelerLam engelerPair f
    · rw [if_pos hn]
      rw [engelerLam, Set.mem_setOf_eq] at hn
      obtain ⟨K, m, hm, heq⟩ := hn
      refine top_unique (le_iSup_of_le K (le_iSup_of_le m ?_))
      rw [if_pos heq, if_pos hm, top_inf_eq]
    · rw [if_neg hn]
      refine le_antisymm ?_ bot_le
      refine iSup_le fun K => iSup_le fun m => ?_
      by_cases heq : n = engelerPair (K, m)
      · by_cases hm : m ∈ f (↑K)
        · have : n ∈ engelerLam engelerPair f := by
            rw [engelerLam, Set.mem_setOf_eq]
            exact ⟨K, m, hm, heq⟩
          exact (hn this).elim
        · rw [if_pos heq, if_neg hm, inf_bot_eq]
      · rw [if_neg heq, bot_inf_eq]

/-!
## Check of a valuation
-/

variable {Var : Type*} [DecidableEq Var]

/-- Check of a ground valuation: same domain, each value embedded by
`setToCanonical`. -/
def checkVal (ρ : Valuation Var (Set ℕ)) :
    Valuation Var (EngelerCarrier (A := A)) where
  domain := ρ.domain
  toFun := fun x => setToCanonical (ρ.toFun x)

theorem checkVal_update (ρ : Valuation Var (Set ℕ)) (x : Var) (d : Set ℕ) :
    checkVal (A := A) (ρ.update x d) =
      (checkVal (A := A) ρ).update x (setToCanonical (A := A) d) := by
  refine Valuation.ext rfl ?_
  funext y
  change setToCanonical (A := A) ((ρ.update x d).toFun y) =
    ((checkVal (A := A) ρ).update x (setToCanonical (A := A) d)).toFun y
  by_cases hy : y = x
  · subst hy
    rw [Valuation.update_toFun_self, Valuation.update_toFun_self]
  · rw [Valuation.update_toFun_of_ne ρ d hy,
      Valuation.update_toFun_of_ne (checkVal (A := A) ρ)
        (setToCanonical (A := A) d) hy]
    rfl

omit [DecidableEq Var] in
theorem checkVal_empty :
    checkVal (A := A) (Valuation.empty : Valuation Var (Set ℕ)) =
      Valuation.default (finsetToCanonical (A := A) ∅) := by
  refine Valuation.ext ?_ ?_
  · rfl
  · funext _x
    exact setToCanonical_empty (A := A)

/-!
## Membership commutation
-/

theorem interpVA_checkVal_mem (M : Lam Var) (ρ : Valuation Var (Set ℕ))
    (n : ℕ) :
    memOfNat (A := A) (interpVA (A := A) M (checkVal (A := A) ρ)) n =
      if n ∈ interp (engelerReflexiveDcpo engelerPair engelerPair_injective)
          M ρ then ⊤ else ⊥ := by
  induction M generalizing ρ n with
  | var x =>
    change memOfNat (A := A) (setToCanonical (A := A) (ρ.toFun x)) n =
      if n ∈ ρ.toFun x then ⊤ else ⊥
    exact memOfNat_setToCanonical (A := A) (ρ.toFun x) n
  | app M N ihM ihN =>
    simp only [interpVA]
    rw [memB_ofNat_engelerAppVA]
    have hN : eqB (childΩ (A := A) (interpVA (A := A) N (checkVal ρ)))
        (check (setPSet (interp engelerDcpo N ρ))) = ⊤ := by
      refine eqB_top_trans (A := A) ?_
        (eqB_setToCanonical (A := A) (interp engelerDcpo N ρ))
      refine eqB_canonical_of_memB_ofNat (A := A) fun k => ?_
      change memOfNat (A := A) (interpVA (A := A) N (checkVal ρ)) k =
        memOfNat (A := A) (setToCanonical (interp engelerDcpo N ρ)) k
      rw [ihN ρ k, memOfNat_setToCanonical]
    have hsubset (K : Finset ℕ) :
        subsetB (check (A := A) (finsetPSet K))
          (childΩ (interpVA (A := A) N (checkVal ρ))) =
        if (↑K : Set ℕ) ⊆ interp engelerDcpo N ρ then ⊤ else ⊥ := by
      rw [eqB_top_subsetB_right hN, subsetB_finsetPSet_setPSet_eq]
    have hpair (K : Finset ℕ) :
        memB (pairApplyB (A := A) K n)
          (childΩ (interpVA (A := A) M (checkVal ρ))) =
        if engelerPair (K, n) ∈ interp engelerDcpo M ρ then ⊤ else ⊥ := by
      change memOfNat (A := A) (interpVA (A := A) M (checkVal ρ))
        (engelerPair (K, n)) = _
      exact ihM ρ (engelerPair (K, n))
    have hcalc :
        (⨆ K : Finset ℕ,
          subsetB (check (finsetPSet K))
              (childΩ (interpVA (A := A) N (checkVal ρ))) ⊓
            memB (pairApplyB (A := A) K n)
              (childΩ (interpVA (A := A) M (checkVal ρ)))) =
        if n ∈ engelerApp engelerPair
            (interp engelerDcpo M ρ) (interp engelerDcpo N ρ)
          then ⊤ else ⊥ := by
      refine Eq.trans (iSup_congr fun K => ?_)
        (iSup_indicator_engelerApp (A := A)
          (interp engelerDcpo M ρ) (interp engelerDcpo N ρ) n)
      rw [hsubset K, hpair K]
    refine hcalc.trans ?_
    rw [interp_app, ReflexiveDcpo.app]
    rfl
  | abs x M ih =>
    simp only [interpVA]
    rw [memB_ofNat_engelerLamVA]
    have hf (K : Finset ℕ) :
        interpVA (A := A) M
            ((checkVal (A := A) ρ).update x
              (finsetToCanonical (A := A) K)) =
          interpVA (A := A) M
            (checkVal (A := A) (ρ.update x (↑K : Set ℕ))) := by
      rw [← setToCanonical_coe, ← checkVal_update]
    have hmem (K : Finset ℕ) (m : ℕ) :
        memOfNat (A := A)
            (interpVA (A := A) M
              ((checkVal ρ).update x (finsetToCanonical (A := A) K))) m =
          if m ∈ interp engelerDcpo M (ρ.update x (↑K : Set ℕ))
            then ⊤ else ⊥ := by
      rw [hf K]
      exact ih (ρ.update x (↑K : Set ℕ)) m
    have hcalc :
        (⨆ K : Finset ℕ, ⨆ m : ℕ,
          eqB (check (PSet.ofNat n)) (pairApplyB (A := A) K m) ⊓
            memOfNat (interpVA (A := A) M
              ((checkVal ρ).update x (finsetToCanonical (A := A) K))) m) =
        if n ∈ engelerLam engelerPair
            (fun d => interp engelerDcpo M (ρ.update x d))
          then ⊤ else ⊥ := by
      refine Eq.trans
        (iSup_congr fun K => iSup_congr fun m => ?_)
        (iSup_indicator_engelerLam (A := A)
          (fun d => interp engelerDcpo M (ρ.update x d)) n)
      rw [eqB_ofNat_pairApplyB, hmem]
    refine hcalc.trans ?_
    rw [interp_abs]
    rfl

/-!
## Paper names
-/

/-- Lemma 31: `‖⟦check M⟧^A_{check ρ} = ⟦M⟧_ρ‖ = 1`. The free-variable
side condition is the paper’s hypothesis; interpretation uses `toFun`. -/
theorem lemma_31 (M : Lam Var) (ρ : Valuation Var (Set ℕ))
    (hfv : M.fv ⊆ ρ.domain) :
    eqB (childΩ (A := A) (interpVA (A := A) M (checkVal (A := A) ρ)))
      (childΩ (setToCanonical (A := A)
        (interp (engelerReflexiveDcpo engelerPair engelerPair_injective)
          M ρ))) = ⊤ := by
  let _ := hfv
  refine eqB_canonical_of_memB_ofNat (A := A) fun n => ?_
  change memOfNat (A := A) (interpVA (A := A) M (checkVal ρ)) n =
    memOfNat (A := A)
      (setToCanonical (interp
        (engelerReflexiveDcpo engelerPair engelerPair_injective) M ρ)) n
  rw [interpVA_checkVal_mem, memOfNat_setToCanonical]

/-- Lemma 31, closed case: `‖⟦check M⟧^A = ⟦M⟧‖ = 1`, since `∅ = check ∅`. -/
theorem lemma_31_closed (M : Lam Var) (hcl : M.fv = ∅) :
    eqB (childΩ (interpClosedVA (A := A) M))
      (childΩ (setToCanonical (interpClosed
        (engelerReflexiveDcpo engelerPair engelerPair_injective) M))) = ⊤ := by
  have hfv : M.fv ⊆ (Valuation.empty : Valuation Var (Set ℕ)).domain := by
    rw [hcl, Valuation.empty_domain]
  rw [interpClosedVA, ← checkVal_empty, interpClosed]
  exact lemma_31 (A := A) M Valuation.empty hfv

end

end Scott2026
