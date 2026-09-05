/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/

import Scott2026.EngelerVA
import Scott2026.Interp
import Scott2026.LambdaVA

/-!
# Theorem 26, pure-term fragment, on the Theorem 30 carrier

Furber–Mardare–Panangaden–Scott, CSL 2026, Theorem 26, restricted to
`Λ(Var)` (no constants / tag 3) and the Engeler carrier of Theorem 30
(`CanonicalPowerIdx` of `check ω`). This is not the paper’s full
statement: there is no `Λ(D, check Var, 𝔎)^A`, no internal
“is a reflexive dcpo” hypothesis, and no Theorem 1 transfer.

The interpretation `interpVA` uses the Definition 25 clauses with
`engelerAppVA` / `engelerLamVA`. The meta-lambda is
`DeterminedByFiniteVA`, so `theorem_30_retract` applies. Soundness is
the capture-free fragment `LamEqNC` (`FreeFor` at β), matching
`interp_sound` on the ground `ReflexiveDcpo`. Capturing `LamEq.beta`
is not claimed.

`SetoidF_A` packaging of this Lean map as a `RelFun` /
`functionalOfRel` on `oid(lamB (check Var))` or
`oid(check (pLamSet Var))` is not proved. The missing lemma is
congruence of `interpVA` under `eqB (encodeLamB M) (encodeLamB N)`
(or injectivity of `encodeLamB` at every Boolean value, which needs
pairwise Boolean-unequal variable children). Definition 16 `oidRel`
would need a function *name* with `isFunctionB = ⊤`, which has the
same single-valuedness obligation. This is not Theorem 1(i).
-/

universe u

namespace Scott2026

open AName

variable {A : Type u} [CompleteBooleanAlgebra A]

noncomputable section

/-!
## Carrier abbreviations
-/

/-- Theorem 30 carrier: canonical indices of `P^A(check ω)`. -/
abbrev EngelerCarrier : Type u :=
  CanonicalPowerIdx (check (A := A) PSet.omega)

/-- Child name of a canonical Engeler element. -/
abbrev childΩ (p : EngelerCarrier (A := A)) : AName.{u} A :=
  (powerB (check (A := A) PSet.omega)).child p.1

/-- Numeral membership in a canonical Engeler element. -/
abbrev memOfNat (p : EngelerCarrier (A := A)) (n : ℕ) : A :=
  memB (check (PSet.ofNat n)) (childΩ (A := A) p)

/-!
## Finite-subset calculations
-/

theorem subsetB_finsetPSet_empty (X : AName.{u} A) :
    subsetB (check (A := A) (finsetPSet (∅ : Finset ℕ))) X = ⊤ := by
  rw [subsetB_finsetPSet]
  exact iInf_eq_top.mpr fun n => (Finset.notMem_empty n.1 n.2).elim

theorem subsetB_finsetPSet_singleton (n : ℕ) (X : AName.{u} A) :
    subsetB (check (A := A) (finsetPSet {n})) X =
      memB (check (PSet.ofNat n)) X := by
  rw [subsetB_finsetPSet]
  refine le_antisymm ?le ?ge
  · exact iInf_le (fun k : {k // k ∈ ({n} : Finset ℕ)} =>
      memB (check (PSet.ofNat k.1)) X) ⟨n, Finset.mem_singleton_self n⟩
  · refine le_iInf fun k => ?_
    have hk : k.1 = n := Finset.mem_singleton.mp k.2
    rw [hk]

theorem subsetB_finsetPSet_union (K L : Finset ℕ) (X : AName.{u} A) :
    subsetB (check (A := A) (finsetPSet (K ∪ L))) X =
      subsetB (check (finsetPSet K)) X ⊓
        subsetB (check (finsetPSet L)) X := by
  rw [subsetB_finsetPSet, subsetB_finsetPSet, subsetB_finsetPSet]
  refine le_antisymm ?le ?ge
  · refine le_inf (le_iInf fun n => ?_) (le_iInf fun n => ?_)
    · exact iInf_le (fun k : {k // k ∈ K ∪ L} =>
        memB (check (PSet.ofNat k.1)) X)
        ⟨n.1, Finset.mem_union_left L n.2⟩
    · exact iInf_le (fun k : {k // k ∈ K ∪ L} =>
        memB (check (PSet.ofNat k.1)) X)
        ⟨n.1, Finset.mem_union_right K n.2⟩
  · refine le_iInf fun n => ?_
    rcases Finset.mem_union.mp n.2 with hK | hL
    · exact inf_le_of_left_le
        (iInf_le (fun k : {k // k ∈ K} =>
          memB (check (PSet.ofNat k.1)) X) ⟨n.1, hK⟩)
    · exact inf_le_of_right_le
        (iInf_le (fun k : {k // k ∈ L} =>
          memB (check (PSet.ofNat k.1)) X) ⟨n.1, hL⟩)

theorem subsetB_finsetPSet_of_subset {K L : Finset ℕ} (h : K ⊆ L)
    (X : AName.{u} A) :
    subsetB (check (A := A) (finsetPSet L)) X ≤
      subsetB (check (finsetPSet K)) X := by
  rw [subsetB_finsetPSet, subsetB_finsetPSet]
  exact le_iInf fun n =>
    iInf_le (fun k : {k // k ∈ L} => memB (check (PSet.ofNat k.1)) X)
      ⟨n.1, h n.2⟩

theorem iInf_insert_subtype {ι : Type*} [DecidableEq ι]
    (a : ι) (s : Finset ι) (_ha : a ∉ s) (f : ι → A) :
    (⨅ i : {x // x ∈ insert a s}, f i.1) =
      f a ⊓ ⨅ i : {x // x ∈ s}, f i.1 := by
  refine le_antisymm ?le ?ge
  · exact le_inf
      (iInf_le (fun i : {x // x ∈ insert a s} => f i.1)
        ⟨a, Finset.mem_insert_self a s⟩)
      (le_iInf fun i =>
        iInf_le (fun j : {x // x ∈ insert a s} => f j.1)
          ⟨i.1, Finset.mem_insert_of_mem i.2⟩)
  · refine le_iInf fun i => ?_
    rcases Finset.mem_insert.mp i.2 with hi | hi
    · rw [show i.1 = a from hi]
      exact inf_le_left
    · exact inf_le_of_right_le
        (iInf_le (fun j : {x // x ∈ s} => f j.1) ⟨i.1, hi⟩)

theorem subsetB_finsetPSet_sup {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (F : ι → Finset ℕ) (X : AName.{u} A) :
    subsetB (check (A := A) (finsetPSet (s.sup F))) X =
      ⨅ i : {x // x ∈ s}, subsetB (check (finsetPSet (F i.1))) X := by
  induction s using Finset.induction with
  | empty =>
    have hsup : (∅ : Finset ι).sup F = ∅ := Finset.sup_empty
    rw [hsup, subsetB_finsetPSet_empty]
    exact (iInf_eq_top.mpr fun i => (Finset.notMem_empty i.1 i.2).elim).symm
  | @insert a s ha ih =>
    have hsup : (insert a s).sup F = F a ∪ s.sup F := Finset.sup_insert
    rw [hsup, subsetB_finsetPSet_union, ih]
    exact (iInf_insert_subtype a s ha
      (fun i => subsetB (check (A := A) (finsetPSet (F i))) X)).symm

/-- Finite meets of joins, indexed by a finite subset (via `iInf_iSup_fun`). -/
theorem iInf_iSup_attach {ι : Type*} (K : Finset ℕ) (f : ℕ → ι → A) :
    (⨅ k : {n // n ∈ K}, ⨆ i : ι, f k.1 i) =
      ⨆ g : ({n // n ∈ K} → ι), ⨅ k, f k.1 (g k) := by
  let e := K.orderIsoOfFin rfl
  have hL :
      (⨅ k : {n // n ∈ K}, ⨆ i : ι, f k.1 i) =
        ⨅ i : Fin K.card, ⨆ j : ι, f (e i).1 j := by
    refine le_antisymm ?_ ?_
    · exact le_iInf fun i => iInf_le _ (e i)
    · refine le_iInf fun k => ?_
      simpa [Equiv.apply_symm_apply] using
        iInf_le (fun i : Fin K.card => ⨆ j : ι, f (e i).1 j) (e.symm k)
  rw [hL, iInf_iSup_fun (fun i j => f (e i).1 j)]
  refine le_antisymm ?le ?ge
  · refine iSup_le fun G =>
      le_iSup_of_le (fun k => G (e.symm k)) ?_
    refine le_iInf fun k => ?_
    simpa [Equiv.apply_symm_apply] using
      iInf_le (fun i : Fin K.card => f (e i).1 (G i)) (e.symm k)
  · refine iSup_le fun F =>
      le_iSup_of_le (fun i => F (e i)) ?_
    exact le_iInf fun i => iInf_le (fun k => f k.1 (F k)) (e i)

theorem memB_check_ofNat_finsetPSet (K : Finset ℕ) (n : ℕ) :
    memB (check (A := A) (PSet.ofNat n)) (check (finsetPSet K)) =
      if n ∈ K then ⊤ else ⊥ := by
  rw [finsetPSet, check_mk, memB_mk]
  by_cases hn : n ∈ K
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

theorem subsetB_finsetPSet_omega (K : Finset ℕ) :
    subsetB (check (A := A) (finsetPSet K)) (check PSet.omega) = ⊤ := by
  rw [subsetB_finsetPSet]
  exact iInf_eq_top.mpr fun _ => memB_check_ofNat_omega _

theorem eqB_finsetToCanonical (K : Finset ℕ) :
    eqB (childΩ (A := A) (finsetToCanonical (A := A) K))
      (check (finsetPSet K)) = ⊤ := by
  have hnorm : eqB
      ((powerB (check (A := A) PSet.omega)).child
        (finsetToCanonical (A := A) K).1)
      ((powerB (check (A := A) PSet.omega)).child
        (finsetToPowerIdx (A := A) K)) = ⊤ := by
    rw [eqB_comm]
    exact normalizePowerIdx_eqB (check (A := A) PSet.omega)
      (finsetToPowerIdx (A := A) K)
  have hrest : eqB
      ((powerB (check (A := A) PSet.omega)).child
        (finsetToPowerIdx (A := A) K))
      (check (finsetPSet K)) = ⊤ := by
    rw [finsetToPowerIdx, restrictPowerIdx_child, eqB_comm]
    exact eqB_restrictName_of_subsetB _ _ (subsetB_finsetPSet_omega K)
  exact eqB_top_trans (A := A) hnorm hrest

theorem memB_finsetToCanonical (K : Finset ℕ) (n : ℕ) :
    memOfNat (A := A) (finsetToCanonical (A := A) K) n =
      if n ∈ K then ⊤ else ⊥ := by
  have h := eqB_finsetToCanonical (A := A) K
  unfold memOfNat
  rw [eqB_top_memB_right h, memB_check_ofNat_finsetPSet]

theorem memB_finsetToCanonical_mem {K : Finset ℕ} {n : ℕ} (h : n ∈ K) :
    memOfNat (A := A) (finsetToCanonical (A := A) K) n = ⊤ := by
  rw [memB_finsetToCanonical, if_pos h]

theorem memB_finsetToCanonical_not {K : Finset ℕ} {n : ℕ} (h : n ∉ K) :
    memOfNat (A := A) (finsetToCanonical (A := A) K) n = ⊥ := by
  rw [memB_finsetToCanonical, if_neg h]

theorem subsetB_finset_canonical {K : Finset ℕ}
    (X : EngelerCarrier (A := A)) :
    subsetB (check (A := A) (finsetPSet K)) (childΩ X) =
      subsetB (childΩ (finsetToCanonical (A := A) K)) (childΩ X) :=
  (eqB_top_subsetB_left (eqB_finsetToCanonical (A := A) K)).symm

theorem subsetB_finset_canonical_of_subset {K L : Finset ℕ} (h : K ⊆ L) :
    subsetB (check (A := A) (finsetPSet K))
      (childΩ (finsetToCanonical (A := A) L)) = ⊤ := by
  have hL : eqB (childΩ (A := A) (finsetToCanonical (A := A) L))
      (check (finsetPSet L)) = ⊤ :=
    eqB_finsetToCanonical (A := A) L
  rw [eqB_top_subsetB_right hL, subsetB_finsetPSet]
  refine iInf_eq_top.mpr fun n => ?_
  have hn : n.1 ∈ L := h n.2
  rw [memB_check_ofNat_finsetPSet, if_pos hn]

/-!
## Membership in `·` and `lam`
-/

theorem memB_ofNat_engelerAppVA
    (F X : EngelerCarrier (A := A)) (n : ℕ) :
    memOfNat (A := A) (engelerAppVA (A := A) F X) n =
      ⨆ K : Finset ℕ,
        subsetB (check (finsetPSet K)) (childΩ X) ⊓
          memB (pairApplyB (A := A) K n) (childΩ F) := by
  unfold memOfNat
  have happ : memB (check (PSet.ofNat n)) (childΩ (engelerAppVA (A := A) F X)) =
      memB (check (PSet.ofNat n))
        (engelerAppName (childΩ F) (childΩ X)) :=
    eqB_top_memB_right (engelerAppVA_eqB (A := A) F X)
  rw [happ, memB_engelerAppName, memB_check_ofNat_omega, top_inf_eq]
  unfold engelerAppPred
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

theorem memB_ofNat_engelerLamVA
    (f : EngelerCarrier (A := A) → EngelerCarrier (A := A)) (n : ℕ) :
    memOfNat (A := A) (engelerLamVA (A := A) f) n =
      ⨆ K : Finset ℕ, ⨆ m : ℕ,
        eqB (check (PSet.ofNat n)) (pairApplyB (A := A) K m) ⊓
          memOfNat (f (finsetToCanonical (A := A) K)) m := by
  unfold memOfNat
  have hlam : memB (check (PSet.ofNat n))
      (childΩ (engelerLamVA (A := A) f)) =
      memB (check (PSet.ofNat n)) (engelerLamName (A := A) f) :=
    eqB_top_memB_right (engelerLamVA_eqB (A := A) f)
  rw [hlam, memB_engelerLamName, memB_check_ofNat_omega, top_inf_eq]
  rfl

/-!
## `DeterminedByFiniteVA` calculus
-/

theorem determinedByFiniteVA_mem
    {f : EngelerCarrier (A := A) → EngelerCarrier (A := A)}
    (hf : DeterminedByFiniteVA (A := A) f)
    (X : EngelerCarrier (A := A)) (n : ℕ) :
    memOfNat (f X) n =
      ⨆ K : Finset ℕ,
        subsetB (check (finsetPSet K)) (childΩ X) ⊓
          memOfNat (f (finsetToCanonical (A := A) K)) n := by
  unfold memOfNat
  have hfX : memB (check (PSet.ofNat n)) (childΩ (f X)) =
      memB (check (PSet.ofNat n))
        (sepB (check PSet.omega) (finiteApproxPred (A := A) f (childΩ X))) :=
    eqB_top_memB_right (hf X)
  rw [hfX, memB_sepB_finiteApprox]

theorem determinedByFiniteVA_of_mem
    (f : EngelerCarrier (A := A) → EngelerCarrier (A := A))
    (h : ∀ X : EngelerCarrier (A := A), ∀ n : ℕ,
      memOfNat (f X) n =
        ⨆ K : Finset ℕ,
          subsetB (check (finsetPSet K)) (childΩ X) ⊓
            memOfNat (f (finsetToCanonical (A := A) K)) n) :
    DeterminedByFiniteVA (A := A) f := by
  intro X
  let W : EngelerCarrier (A := A) :=
    ⟨restrictPowerIdx
        (sepB (check PSet.omega) (finiteApproxPred (A := A) f (childΩ X)))
        (check (A := A) PSet.omega),
      restrictPowerIdx_isCanonical _ _⟩
  have hW : eqB (childΩ W)
      (sepB (check PSet.omega) (finiteApproxPred (A := A) f (childΩ X))) = ⊤ := by
    unfold childΩ
    change eqB
        ((powerB (check (A := A) PSet.omega)).child
          (restrictPowerIdx
            (sepB (check PSet.omega) (finiteApproxPred (A := A) f (childΩ X)))
            (check (A := A) PSet.omega)))
        (sepB (check PSet.omega) (finiteApproxPred (A := A) f (childΩ X))) = ⊤
    rw [restrictPowerIdx_child, eqB_comm]
    exact eqB_restrictName_of_subsetB _ _ (subsetB_sepB_omega _)
  have hmem : ∀ n : ℕ,
      memB (check (PSet.ofNat n)) (childΩ (f X)) =
      memB (check (PSet.ofNat n)) (childΩ W) := by
    intro n
    have hWn : memB (check (PSet.ofNat n)) (childΩ W) =
        memB (check (PSet.ofNat n))
          (sepB (check PSet.omega) (finiteApproxPred (A := A) f (childΩ X))) :=
      eqB_top_memB_right hW
    rw [show memB (check (PSet.ofNat n)) (childΩ (f X)) = memOfNat (f X) n from rfl,
      h X n, hWn, memB_sepB_finiteApprox]
  have hpq : eqB (childΩ (f X)) (childΩ W) = ⊤ :=
    eqB_canonical_of_memB_ofNat (A := A) hmem
  exact eqB_top_trans (A := A) hpq hW

theorem determinedByFiniteVA_const (c : EngelerCarrier (A := A)) :
    DeterminedByFiniteVA (A := A) (fun _ => c) := by
  refine determinedByFiniteVA_of_mem (A := A) (fun _ => c) fun X n => ?_
  refine le_antisymm ?le ?ge
  · exact le_iSup_of_le (∅ : Finset ℕ)
      (le_inf (by rw [subsetB_finsetPSet_empty]; exact le_top) le_rfl)
  · exact iSup_le fun _ => inf_le_right

theorem determinedByFiniteVA_id :
    DeterminedByFiniteVA (A := A) id := by
  refine determinedByFiniteVA_of_mem (A := A) id fun X n => ?_
  simp only [id]
  refine le_antisymm ?le ?ge
  · refine le_iSup_of_le {n} ?_
    rw [subsetB_finsetPSet_singleton,
      memB_finsetToCanonical_mem (Finset.mem_singleton_self n)]
    exact le_inf le_rfl le_top
  · refine iSup_le fun K => ?_
    by_cases hn : n ∈ K
    · have hle : subsetB (check (A := A) (finsetPSet K)) (childΩ X) ≤
          memOfNat X n := by
        rw [subsetB_finsetPSet]
        exact iInf_le (fun k : {k // k ∈ K} =>
          memB (check (PSet.ofNat k.1)) (childΩ X)) ⟨n, hn⟩
      rw [memB_finsetToCanonical_mem (A := A) hn, inf_top_eq]
      exact hle
    · rw [memB_finsetToCanonical_not (A := A) hn, inf_bot_eq]
      exact bot_le

/-- Boolean monotonicity of a determined-by-finite map. -/
theorem determinedByFiniteVA_le
    {f : EngelerCarrier (A := A) → EngelerCarrier (A := A)}
    (hf : DeterminedByFiniteVA (A := A) f)
    (X Y : EngelerCarrier (A := A)) (n : ℕ) :
    subsetB (childΩ X) (childΩ Y) ⊓ memOfNat (f X) n ≤ memOfNat (f Y) n := by
  rw [determinedByFiniteVA_mem hf X n, determinedByFiniteVA_mem hf Y n, inf_iSup_eq]
  refine iSup_le fun K => ?_
  refine le_iSup_of_le K ?_
  have hsub : subsetB (childΩ X) (childΩ Y) ⊓
      subsetB (check (finsetPSet K)) (childΩ X) ≤
      subsetB (check (finsetPSet K)) (childΩ Y) := by
    have h := subsetB_trans (check (A := A) (finsetPSet K)) (childΩ X) (childΩ Y)
    exact h.trans' (le_inf inf_le_right inf_le_left)
  exact le_inf (hsub.trans' (le_inf inf_le_left (inf_le_of_right_le inf_le_left)))
    (inf_le_of_right_le inf_le_right)

theorem determinedByFiniteVA_le_finset
    {f : EngelerCarrier (A := A) → EngelerCarrier (A := A)}
    (hf : DeterminedByFiniteVA (A := A) f)
    (K : Finset ℕ) (X : EngelerCarrier (A := A)) (n : ℕ) :
    subsetB (check (A := A) (finsetPSet K)) (childΩ X) ⊓
      memOfNat (f (finsetToCanonical (A := A) K)) n ≤ memOfNat (f X) n := by
  have hmono := determinedByFiniteVA_le (A := A) hf (finsetToCanonical (A := A) K) X n
  rw [← subsetB_finset_canonical] at hmono
  exact hmono

theorem determinedByFiniteVA_app
    {g h : EngelerCarrier (A := A) → EngelerCarrier (A := A)}
    (hg : DeterminedByFiniteVA (A := A) g)
    (hh : DeterminedByFiniteVA (A := A) h) :
    DeterminedByFiniteVA (A := A)
      (fun d => engelerAppVA (A := A) (g d) (h d)) := by
  refine determinedByFiniteVA_of_mem (A := A)
    (fun d => engelerAppVA (A := A) (g d) (h d)) fun X n => ?_
  rw [memB_ofNat_engelerAppVA]
  refine le_antisymm ?le ?ge
  · refine iSup_le fun K' => ?_
    have hgX : memB (pairApplyB (A := A) K' n) (childΩ (g X)) =
        ⨆ Kg : Finset ℕ,
          subsetB (check (finsetPSet Kg)) (childΩ X) ⊓
            memB (pairApplyB (A := A) K' n)
              (childΩ (g (finsetToCanonical (A := A) Kg))) := by
      have := determinedByFiniteVA_mem (A := A) hg X (engelerPair (K', n))
      simpa [memOfNat, pairApplyB] using this
    have hhX : subsetB (check (A := A) (finsetPSet K')) (childΩ (h X)) =
        ⨅ k : {m // m ∈ K'},
          ⨆ Kh : Finset ℕ,
            subsetB (check (finsetPSet Kh)) (childΩ X) ⊓
              memOfNat (h (finsetToCanonical (A := A) Kh)) k.1 := by
      rw [subsetB_finsetPSet]
      refine iInf_congr fun k => ?_
      exact determinedByFiniteVA_mem (A := A) hh X k.1
    rw [hhX, iInf_iSup_attach (K := K')
      (fun k Kh =>
        subsetB (check (A := A) (finsetPSet Kh)) (childΩ X) ⊓
          memOfNat (h (finsetToCanonical (A := A) Kh)) k),
      hgX, inf_comm, inf_iSup_eq]
    refine iSup_le fun F => ?_
    rw [inf_comm, inf_iSup_eq]
    refine iSup_le fun Kg => ?_
    let U : Finset ℕ :=
      (Finset.univ : Finset {m // m ∈ K'}).sup F ∪ Kg
    have hsplit :
        (⨅ k : {m // m ∈ K'},
            subsetB (check (A := A) (finsetPSet (F k))) (childΩ X) ⊓
              memOfNat (h (finsetToCanonical (A := A) (F k))) k.1) =
          (⨅ k : {m // m ∈ K'},
              subsetB (check (finsetPSet (F k))) (childΩ X)) ⊓
            ⨅ k : {m // m ∈ K'},
              memOfNat (h (finsetToCanonical (A := A) (F k))) k.1 := by
      refine le_antisymm ?_ ?_
      · exact le_inf
          (le_iInf fun k => (iInf_le _ k).trans inf_le_left)
          (le_iInf fun k => (iInf_le _ k).trans inf_le_right)
      · exact le_iInf fun k =>
          le_inf (inf_le_of_left_le (iInf_le _ k))
            (inf_le_of_right_le (iInf_le _ k))
    have hU_sub :
        (⨅ k : {m // m ∈ K'},
            subsetB (check (A := A) (finsetPSet (F k))) (childΩ X)) ⊓
          subsetB (check (finsetPSet Kg)) (childΩ X) ≤
          subsetB (check (finsetPSet U)) (childΩ X) := by
      rw [subsetB_finsetPSet_union,
        subsetB_finsetPSet_sup
          (s := (Finset.univ : Finset {m // m ∈ K'})) F (childΩ X)]
      refine le_inf ?_ inf_le_right
      exact le_iInf fun i =>
        inf_le_of_left_le
          (iInf_le (fun k : {m // m ∈ K'} =>
            subsetB (check (A := A) (finsetPSet (F k))) (childΩ X)) i.1)
    have hKgU : Kg ⊆ U := Finset.subset_union_right
    have hFU (k : {m // m ∈ K'}) : F k ⊆ U :=
      (Finset.le_sup (Finset.mem_univ k)).trans Finset.subset_union_left
    have hgU : memB (pairApplyB (A := A) K' n)
        (childΩ (g (finsetToCanonical (A := A) Kg))) ≤
        memB (pairApplyB (A := A) K' n)
          (childΩ (g (finsetToCanonical (A := A) U))) := by
      have hsub : subsetB
          (childΩ (finsetToCanonical (A := A) Kg))
          (childΩ (finsetToCanonical (A := A) U)) = ⊤ := by
        rw [← subsetB_finset_canonical]
        exact subsetB_finset_canonical_of_subset hKgU
      have := determinedByFiniteVA_le (A := A) hg
        (finsetToCanonical (A := A) Kg) (finsetToCanonical (A := A) U)
        (engelerPair (K', n))
      rw [hsub, top_inf_eq] at this
      simpa [memOfNat, pairApplyB] using this
    have hhU :
        (⨅ k : {m // m ∈ K'},
            memOfNat (h (finsetToCanonical (A := A) (F k))) k.1) ≤
          subsetB (check (A := A) (finsetPSet K'))
            (childΩ (h (finsetToCanonical (A := A) U))) := by
      rw [subsetB_finsetPSet]
      refine le_iInf fun k => ?_
      have hsub : subsetB
          (childΩ (finsetToCanonical (A := A) (F k)))
          (childΩ (finsetToCanonical (A := A) U)) = ⊤ := by
        rw [← subsetB_finset_canonical]
        exact subsetB_finset_canonical_of_subset (hFU k)
      have := determinedByFiniteVA_le (A := A) hh
        (finsetToCanonical (A := A) (F k)) (finsetToCanonical (A := A) U) k.1
      rw [hsub, top_inf_eq] at this
      exact this.trans'
        (iInf_le (fun j : {m // m ∈ K'} =>
          memOfNat (h (finsetToCanonical (A := A) (F j))) j.1) k)
    refine le_iSup_of_le U ?_
    rw [memB_ofNat_engelerAppVA, hsplit]
    refine le_inf ?_ (le_iSup_of_le K' ?_)
    · refine hU_sub.trans' (le_inf ?_ ?_)
      · exact inf_le_of_left_le inf_le_left
      · exact inf_le_of_right_le inf_le_left
    · refine le_inf ?_ ?_
      · exact hhU.trans' (inf_le_of_left_le inf_le_right)
      · exact hgU.trans' (inf_le_of_right_le inf_le_right)
  · refine iSup_le fun K => ?_
    rw [memB_ofNat_engelerAppVA, inf_iSup_eq]
    refine iSup_le fun K' => ?_
    refine le_iSup_of_le K' ?_
    have hhK : subsetB (check (A := A) (finsetPSet K)) (childΩ X) ⊓
        subsetB (check (finsetPSet K'))
          (childΩ (h (finsetToCanonical (A := A) K))) ≤
        subsetB (check (finsetPSet K')) (childΩ (h X)) := by
      rw [subsetB_finsetPSet (K := K'), subsetB_finsetPSet (K := K')]
      refine le_iInf fun k => ?_
      have := determinedByFiniteVA_le_finset (A := A) hh K X k.1
      exact this.trans'
        (le_inf inf_le_left (inf_le_of_right_le
          (iInf_le (fun j : {m // m ∈ K'} =>
            memOfNat (h (finsetToCanonical (A := A) K)) j.1) k)))
    have hgK : subsetB (check (A := A) (finsetPSet K)) (childΩ X) ⊓
        memB (pairApplyB (A := A) K' n)
          (childΩ (g (finsetToCanonical (A := A) K))) ≤
        memB (pairApplyB (A := A) K' n) (childΩ (g X)) := by
      have := determinedByFiniteVA_le_finset (A := A) hg K X (engelerPair (K', n))
      simpa [memOfNat, pairApplyB] using this
    exact le_inf
      (hhK.trans' (le_inf inf_le_left (inf_le_of_right_le inf_le_left)))
      (hgK.trans' (le_inf inf_le_left (inf_le_of_right_le inf_le_right)))

theorem determinedByFiniteVA_lam
    {g : EngelerCarrier (A := A) → EngelerCarrier (A := A) →
      EngelerCarrier (A := A)}
    (hg : ∀ e, DeterminedByFiniteVA (A := A) (fun d => g d e)) :
    DeterminedByFiniteVA (A := A)
      (fun d => engelerLamVA (A := A) (g d)) := by
  refine determinedByFiniteVA_of_mem (A := A)
    (fun d => engelerLamVA (A := A) (g d)) fun X n => ?_
  rw [memB_ofNat_engelerLamVA]
  refine le_antisymm ?le ?ge
  · refine iSup_le fun K' => iSup_le fun m => ?_
    have him : memOfNat (g X (finsetToCanonical (A := A) K')) m =
        ⨆ K : Finset ℕ,
          subsetB (check (finsetPSet K)) (childΩ X) ⊓
            memOfNat (g (finsetToCanonical (A := A) K)
              (finsetToCanonical (A := A) K')) m :=
      determinedByFiniteVA_mem (A := A) (hg (finsetToCanonical (A := A) K')) X m
    rw [him, inf_iSup_eq]
    refine iSup_le fun K => le_iSup_of_le K (le_inf ?_ ?_)
    · exact inf_le_of_right_le inf_le_left
    · rw [memB_ofNat_engelerLamVA]
      exact le_iSup_of_le K' (le_iSup_of_le m
        (le_inf inf_le_left (inf_le_of_right_le inf_le_right)))
  · refine iSup_le fun K => ?_
    rw [memB_ofNat_engelerLamVA, inf_iSup_eq]
    refine iSup_le fun K' => ?_
    rw [inf_iSup_eq]
    refine iSup_le fun m => ?_
    refine le_iSup_of_le K' (le_iSup_of_le m (le_inf ?_ ?_))
    · exact inf_le_of_right_le inf_le_left
    · exact (determinedByFiniteVA_le_finset (A := A)
        (hg (finsetToCanonical (A := A) K')) K X m).trans'
        (le_inf inf_le_left (inf_le_of_right_le inf_le_right))

/-!
## Interpretation
-/

variable {Var : Type*} [DecidableEq Var]

/-- Theorem 26, pure-term fragment: `⟦M⟧^A_ρ` on the Theorem 30 carrier. -/
noncomputable def interpVA :
    Lam Var → Valuation Var (EngelerCarrier (A := A)) →
      EngelerCarrier (A := A)
  | .var x, ρ => ρ.toFun x
  | .app M N, ρ => engelerAppVA (A := A) (interpVA M ρ) (interpVA N ρ)
  | .abs x M, ρ =>
      engelerLamVA (A := A) fun d => interpVA M (ρ.update x d)

/-- Closed-term interpretation `⟦M⟧^A := ⟦M⟧^A_∅`. -/
noncomputable def interpClosedVA (M : Lam Var) : EngelerCarrier (A := A) :=
  interpVA (A := A) M (Valuation.default (finsetToCanonical (A := A) ∅))

theorem interpVA_var (x : Var) (ρ : Valuation Var (EngelerCarrier (A := A)))
    (h : x ∈ ρ.domain) :
    interpVA (A := A) (Lam.var x) ρ = ρ.lookup x h :=
  rfl

theorem interpVA_app (M N : Lam Var)
    (ρ : Valuation Var (EngelerCarrier (A := A))) :
    interpVA (A := A) (M.app N) ρ =
      engelerAppVA (A := A) (interpVA (A := A) M ρ) (interpVA (A := A) N ρ) :=
  rfl

theorem interpVA_abs (x : Var) (M : Lam Var)
    (ρ : Valuation Var (EngelerCarrier (A := A))) :
    interpVA (A := A) (Lam.abs x M) ρ =
      engelerLamVA (A := A) fun d => interpVA (A := A) M (ρ.update x d) :=
  rfl

theorem interpVA_closed (M : Lam Var) :
    interpClosedVA (A := A) M =
      interpVA (A := A) M
        (Valuation.default (finsetToCanonical (A := A) ∅)) :=
  rfl

/-- Interpretations agree when valuations agree on `fv(M)`. -/
theorem interpVA_agree (M : Lam Var)
    (ρ σ : Valuation Var (EngelerCarrier (A := A)))
    (h : ∀ x ∈ M.fv, ρ.toFun x = σ.toFun x) :
    interpVA (A := A) M ρ = interpVA (A := A) M σ := by
  induction M generalizing ρ σ with
  | var x =>
    have hx : ρ.toFun x = σ.toFun x := h x (by simp [Lam.fv])
    simpa [interpVA] using hx
  | app M N ihM ihN =>
    have hM : ∀ x ∈ M.fv, ρ.toFun x = σ.toFun x := fun x hx =>
      h x (Finset.mem_union_left N.fv hx)
    have hN : ∀ x ∈ N.fv, ρ.toFun x = σ.toFun x := fun x hx =>
      h x (Finset.mem_union_right M.fv hx)
    simp only [interpVA]
    rw [ihM ρ σ hM, ihN ρ σ hN]
  | abs x M ih =>
    simp only [interpVA]
    congr 1
    funext d
    refine ih (ρ.update x d) (σ.update x d) ?_
    intro y hy
    by_cases hyx : y = x
    · subst hyx
      simp
    · simp [Valuation.update_toFun_of_ne _ _ hyx]
      exact h y (Finset.mem_sdiff.mpr ⟨hy, mt Finset.mem_singleton.mp hyx⟩)

/-- Updating a variable that is not free does not change the interpretation. -/
theorem interpVA_update_fresh (M : Lam Var)
    (ρ : Valuation Var (EngelerCarrier (A := A))) (x : Var)
    (d : EngelerCarrier (A := A)) (h : x ∉ M.fv) :
    interpVA (A := A) M (ρ.update x d) = interpVA (A := A) M ρ := by
  refine interpVA_agree (A := A) M _ _ ?_
  intro y hy
  have hyx : y ≠ x := fun hxy => h (hxy ▸ hy)
  exact Valuation.update_toFun_of_ne ρ d hyx

/-- The meta-lambda `d ↦ ⟦M⟧^A_{ρ(x := d)}` is determined by finite sets. -/
theorem interpVA_update_determined (M : Lam Var)
    (ρ : Valuation Var (EngelerCarrier (A := A))) (x : Var) :
    DeterminedByFiniteVA (A := A)
      (fun d => interpVA (A := A) M (ρ.update x d)) := by
  induction M generalizing ρ x with
  | var y =>
    by_cases hyx : y = x
    · subst hyx
      convert determinedByFiniteVA_id (A := A) using 1
      funext d
      simp [interpVA]
    · convert determinedByFiniteVA_const (A := A) (ρ.toFun y) using 1
      funext d
      simp [interpVA, hyx]
  | app M N ihM ihN =>
    simp only [interpVA]
    exact determinedByFiniteVA_app (A := A) (ihM ρ x) (ihN ρ x)
  | abs y M ih =>
    simp only [interpVA]
    by_cases hxy : x = y
    · subst hxy
      convert determinedByFiniteVA_const (A := A)
        (engelerLamVA (A := A) fun e => interpVA (A := A) M (ρ.update x e)) using 1
      funext d
      congr 1
      funext e
      simp [Valuation.update_overwrite]
    · convert determinedByFiniteVA_lam (A := A)
        (g := fun d e => interpVA (A := A) M ((ρ.update y e).update x d))
        (fun e => ih (ρ.update y e) x) using 1
      funext d
      congr 1
      funext e
      simp [Valuation.update_comm hxy]

/-- Substitution lemma, restricted to `N` free for `x` in `M`. -/
theorem interpVA_subst (M N : Lam Var) (x : Var)
    (ρ : Valuation Var (EngelerCarrier (A := A)))
    (hfree : M.FreeFor x N) :
    interpVA (A := A) (M.subst x N) ρ =
      interpVA (A := A) M (ρ.update x (interpVA (A := A) N ρ)) := by
  induction M generalizing ρ with
  | var y =>
    simp only [Lam.subst, Lam.substNaive]
    by_cases hyx : y = x
    · subst hyx
      simp [interpVA]
    · simp [hyx, interpVA]
  | app M₁ M₂ ih₁ ih₂ =>
    obtain ⟨h₁, h₂⟩ := hfree
    simp only [Lam.subst, Lam.substNaive, interpVA]
    rw [ih₁ ρ h₁, ih₂ ρ h₂]
  | abs y M ih =>
    simp only [Lam.subst, Lam.substNaive]
    split_ifs with hyx
    · subst hyx
      simp only [interpVA]
      congr 1
      funext d
      rw [Valuation.update_overwrite]
    · obtain ⟨hM, hcap⟩ := Lam.freeFor_abs_of_ne hyx hfree
      simp only [interpVA]
      congr 1
      funext d
      cases hcap with
      | inl hyN =>
        have hN : interpVA (A := A) N (ρ.update y d) =
            interpVA (A := A) N ρ :=
          interpVA_update_fresh (A := A) N ρ y d hyN
        rw [ih (ρ.update y d) hM, hN, Valuation.update_comm hyx]
      | inr hxM =>
        have hsf : M.substNaive x N = M := Lam.subst_fresh N hxM
        rw [hsf]
        refine interpVA_agree (A := A) M _ _ ?_
        intro z hz
        have hzx : z ≠ x := fun hzx => hxM (hzx ▸ hz)
        by_cases hzy : z = y
        · subst hzy
          simp
        · simp [Valuation.update_toFun_of_ne ρ d hzy,
            Valuation.update_toFun_of_ne
              (ρ.update x (interpVA (A := A) N ρ)) d hzy,
            Valuation.update_toFun_of_ne ρ (interpVA (A := A) N ρ) hzx]

/-- [4, Theorem 5.4.4] β-case on the Theorem 30 carrier, when `N` is free
for `x` in `M`. Uses `theorem_30_retract`. Capturing β is not claimed. -/
theorem interpVA_sound_beta (x : Var) (M N : Lam Var)
    (ρ : Valuation Var (EngelerCarrier (A := A)))
    (hfree : M.FreeFor x N) :
    interpVA (A := A) ((Lam.abs x M).app N) ρ =
      interpVA (A := A) (M.subst x N) ρ := by
  have hf : DeterminedByFiniteVA (A := A)
      (fun d => interpVA (A := A) M (ρ.update x d)) :=
    interpVA_update_determined (A := A) M ρ x
  have hretract :=
    engelerVA_retract_oid (A := A)
      (fun d => interpVA (A := A) M (ρ.update x d)) hf
      (interpVA (A := A) N ρ)
  have hstrict : (canonicalPowerSetoid
      (check (A := A) PSet.omega)).IsStrict :=
    canonicalPowerSetoid_isStrict _
  have happ :
      interpVA (A := A) ((Lam.abs x M).app N) ρ =
        engelerAppVA (A := A)
          (engelerLamVA (A := A) fun d => interpVA (A := A) M (ρ.update x d))
          (interpVA (A := A) N ρ) :=
    rfl
  have happly :
      engelerAppVA (A := A)
          (engelerLamVA (A := A) fun d => interpVA (A := A) M (ρ.update x d))
          (interpVA (A := A) N ρ) =
        interpVA (A := A) M (ρ.update x (interpVA (A := A) N ρ)) :=
    hstrict _ _ hretract
  exact happ.trans (happly.trans (interpVA_subst (A := A) M N x ρ hfree).symm)

/-- Capture-free soundness: `LamEqNC M N` implies `⟦M⟧^A_ρ = ⟦N⟧^A_ρ`. -/
theorem interpVA_sound {M N : Lam Var} (h : LamEqNC M N)
    (ρ : Valuation Var (EngelerCarrier (A := A))) :
    interpVA (A := A) M ρ = interpVA (A := A) N ρ := by
  induction h generalizing ρ with
  | refl M =>
    rfl
  | symm _ ih =>
    exact (ih ρ).symm
  | trans _ _ ih1 ih2 =>
    exact (ih1 ρ).trans (ih2 ρ)
  | app_left _ ih =>
    simp only [interpVA]
    rw [ih ρ]
  | app_right _ ih =>
    simp only [interpVA]
    rw [ih ρ]
  | xi x _ ih =>
    simp only [interpVA]
    congr 1
    funext d
    exact ih (ρ.update x d)
  | beta x M N hfree =>
    exact interpVA_sound_beta (A := A) x M N ρ hfree

theorem interpClosedVA_sound {M N : Lam Var} (h : LamEqNC M N) :
    interpClosedVA (A := A) M = interpClosedVA (A := A) N :=
  interpVA_sound (A := A) h
    (Valuation.default (finsetToCanonical (A := A) ∅))

end

end Scott2026
