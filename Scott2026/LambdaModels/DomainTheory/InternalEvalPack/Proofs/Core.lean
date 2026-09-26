/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/

import Scott2026.LambdaModels.DomainTheory.InternalEvalComplete
import Scott2026.LambdaModels.DomainTheory.InternalEvalPack.LamDK.weight
import Scott2026.LambdaModels.DomainTheory.InternalEvalPack.OidSeparated
import Scott2026.LambdaModels.DomainTheory.InternalEvalPack.asLam
import Scott2026.LambdaModels.DomainTheory.InternalEvalPack.asLamDK
import Scott2026.LambdaModels.DomainTheory.InternalEval.applyRelOfElements
import Scott2026.LambdaModels.DomainTheory.InternalEval.Proofs.Core

namespace Scott2026

universe u


open AName

variable {A : Type u} [CompleteBooleanAlgebra A]

/-!
## Generalized-element restriction
-/

namespace IsRelElementAt

/-- Restrict a generalized element to a smaller extent by cutting its
coefficients.  Shrinking the degree on the original row is not automatic:
`r d ≤ a ⊓ eps` becomes stronger. -/
theorem inf {D : AName.{u} A} {a b : A} {r : D.idx → A}
    (h : IsRelElementAt D a r) :
    IsRelElementAt D (a ⊓ b) (fun d => r d ⊓ b) := by
  refine ⟨?respects, ?le_eps, ?single, ?total⟩
  · intro d e
    refine le_inf ?_ (inf_le_right.trans inf_le_right)
    have h1 : (oid D).eq d e ⊓ (r d ⊓ b) ≤ (oid D).eq d e ⊓ r d :=
      le_inf inf_le_left (inf_le_right.trans inf_le_left)
    exact (h.1 d e).trans' h1
  · intro d
    have hr := h.2.1 d
    refine le_inf (le_inf ?_ inf_le_right) ?_
    · exact (hr.trans inf_le_left).trans' inf_le_left
    · exact (hr.trans inf_le_right).trans' inf_le_left
  · intro d e
    exact h.2.2.1 d e |>.trans' <|
      le_inf (inf_le_left.trans inf_le_left) (inf_le_right.trans inf_le_left)
  · have htot : a ≤ ⨆ d, r d := h.2.2.2
    have : a ⊓ b ≤ (⨆ d, r d) ⊓ b := inf_le_inf htot le_rfl
    rwa [iSup_inf_eq] at this

/-- Same-row restriction when the coefficients are already supported by the
smaller degree. -/
theorem of_le {D : AName.{u} A} {a b : A} {r : D.idx → A}
    (h : IsRelElementAt D a r) (hle : b ≤ a)
    (hsupp : ∀ d, r d ≤ b) :
    IsRelElementAt D b r :=
  ⟨h.1, fun d => le_inf (hsupp d) ((h.2.1 d).trans inf_le_right),
    h.2.2.1, hle.trans h.2.2.2⟩

theorem congr_degree {D : AName.{u} A} {a b : A} {r : D.idx → A}
    (h : IsRelElementAt D a r) (e : a = b) :
    IsRelElementAt D b r :=
  e ▸ h

end IsRelElementAt

/-- Extent factors drop out of `Oid` equality. -/
theorem oid_eq_le_eqB_child (X : AName.{u} A) (i j : X.idx) :
    (oid X).eq i j ≤ eqB (X.child i) (X.child j) := by
  simp only [oid_eq]
  exact inf_le_right

theorem asLamDK_encode (D V K : AName.{u} A)
    (M : (lamDKB D V K).idx) :
    encodeLamDKB V K (asLamDK D V K M) = (lamDKB D V K).child M := by
  unfold asLamDK lamDKB
  rfl

theorem asLamDK_val (D V K : AName.{u} A)
    (M : (lamDKB D V K).idx) :
    lamDKVal V K (asLamDK D V K M) = (lamDKB D V K).val M := by
  unfold asLamDK lamDKB
  rfl

/-!
## Environment update in the source key
-/

/-- The family `x ↦ η[x := d]` is pointwise over the source setoid. -/
theorem RelFun.isPointwiseFamily_update_key
    {X Y : Type*} {S : ASetoid (A := A) X} {T : ASetoid (A := A) Y}
    (f : RelFun S T) (hS : S.IsTotal) (hT : T.IsTotal) (d : Y) :
    RelFun.IsPointwiseFamily S (fun x => f.update hS hT x d) := by
  intro x y i j
  rw [RelFun.update_val, RelFun.update_val, inf_sup_left]
  refine sup_le ?_ ?_
  · apply le_sup_of_le_left
    refine le_inf ?_ (inf_le_right.trans inf_le_right)
    exact (S.trans i x y).trans' <|
      le_inf (inf_le_right.trans inf_le_left) inf_le_left
  · apply le_sup_of_le_right
    refine le_inf ?_ (inf_le_right.trans inf_le_right)
    have hgoal : S.eq x y ⊓ (S.eq x i)ᶜ ≤ (S.eq y i)ᶜ :=
      setoidEq_inf_compl_le_compl x y i
    rw [S.symm i y, S.symm i x]
    exact hgoal.trans' (le_inf inf_le_left (inf_le_right.trans inf_le_left))

/-- Interpretation transports along source-key equality of an update. -/
theorem interpDKRelVal_update_key
    (𝓜 : InternalReflexiveModel (A := A))
    (V K : AName.{u} A) (hK : subsetB K 𝓜.D = ⊤)
    (hV : (oid V).IsTotal)
    (η : RelFun (oid V) (oid 𝓜.D))
    (x y : V.idx) (d : 𝓜.D.idx) (P : LamDK V.idx K.idx)
    (e : 𝓜.D.idx) :
    (oid V).eq x y ⊓
        interpDKRelVal 𝓜 V K hK hV (η.update hV 𝓜.total x d) P e ≤
      interpDKRelVal 𝓜 V K hK hV (η.update hV 𝓜.total y d) P e :=
  interpDKRelVal_isPointwiseFamily 𝓜 V K hK hV (oid V)
    (fun z => η.update hV 𝓜.total z d)
    (RelFun.isPointwiseFamily_update_key η hV 𝓜.total d) P x y e

/-!
## Tag calculus for `encodeLamDKB`
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

theorem ofNat_equiv_iff {n m : ℕ} :
    PSet.Equiv (PSet.ofNat.{u} n) (PSet.ofNat.{u} m) ↔ n = m :=
  (ofNat_spec_sum.{u} (n + m) n m rfl).2

theorem eqB_check_ofNat_bot [Nontrivial A] {n m : ℕ} (hne : n ≠ m) :
    eqB (A := A) (check (PSet.ofNat n)) (check (PSet.ofNat m)) = ⊥ :=
  (check_atomic (A := A) (PSet.ofNat n) (PSet.ofNat m)).2.1.mpr
    (mt ofNat_equiv_iff.mp hne)

theorem eqB_lamTag_mismatch_le {n m : ℕ} (hne : n ≠ m)
    (x y : AName.{u} A) {a b : A} :
    eqB (opairB (check (PSet.ofNat n)) x)
        (opairB (check (PSet.ofNat m)) y) ⊓ a ≤ b := by
  rcases subsingleton_or_nontrivial A with hA | hA
  · exact (Subsingleton.elim (α := A) _ _).le
  · have : Nontrivial A := hA
    rw [eqB_opairB, eqB_check_ofNat_bot (A := A) hne, bot_inf_eq, bot_inf_eq]
    exact bot_le

@[simp] theorem eqB_encodeLamDKB_var_var (V K : AName.{u} A)
    (x y : V.idx) :
    eqB (encodeLamDKB V K (.var x)) (encodeLamDKB V K (.var y)) =
      eqB (V.child x) (V.child y) :=
  eqB_lamVarB (V.child x) (V.child y)

@[simp] theorem eqB_encodeLamDKB_const_const (V K : AName.{u} A)
    (i j : K.idx) :
    eqB (encodeLamDKB V K (.const i)) (encodeLamDKB V K (.const j)) =
      eqB (K.child i) (K.child j) :=
  eqB_lamConstB (K.child i) (K.child j)

@[simp] theorem eqB_encodeLamDKB_abs_abs (V K : AName.{u} A)
    (x y : V.idx) (P Q : LamDK V.idx K.idx) :
    eqB (encodeLamDKB V K (.abs x P)) (encodeLamDKB V K (.abs y Q)) =
      eqB (V.child x) (V.child y) ⊓
        eqB (encodeLamDKB V K P) (encodeLamDKB V K Q) :=
  eqB_lamAbsB (V.child x) (encodeLamDKB V K P)
    (V.child y) (encodeLamDKB V K Q)

@[simp] theorem eqB_encodeLamDKB_app_app (V K : AName.{u} A)
    (P Q P' Q' : LamDK V.idx K.idx) :
    eqB (encodeLamDKB V K (.app P Q)) (encodeLamDKB V K (.app P' Q')) =
      eqB (encodeLamDKB V K P) (encodeLamDKB V K P') ⊓
        eqB (encodeLamDKB V K Q) (encodeLamDKB V K Q') :=
  eqB_lamAppB (encodeLamDKB V K P) (encodeLamDKB V K Q)
    (encodeLamDKB V K P') (encodeLamDKB V K Q')

/-!
## Encoding congruence of extents and interpretations
-/

theorem eqB_inf_memB_le (x y S : AName.{u} A) :
    eqB x y ⊓ memB x S ≤ memB y S :=
  (memB_eqB_left x S y).trans' (le_inf inf_le_right inf_le_left)

theorem lamDKVal_encode_congr (V K : AName.{u} A)
    (M N : LamDK V.idx K.idx) :
    eqB (encodeLamDKB V K M) (encodeLamDKB V K N) ⊓ lamDKVal V K M ≤
      lamDKVal V K N := by
  have : ∀ n M N, M.weight + N.weight = n →
      eqB (encodeLamDKB V K M) (encodeLamDKB V K N) ⊓
        lamDKVal V K M ≤ lamDKVal V K N := by
    intro n
    induction n using Nat.strongRecOn with
    | ind n ih =>
      intro M N hsum
      cases M with
      | var x =>
        cases N with
        | var y =>
          rw [eqB_encodeLamDKB_var_var, lamDKVal, lamDKVal]
          exact eqB_inf_memB_le (V.child x) (V.child y) V
        | const j =>
          exact eqB_lamTag_mismatch_le (by decide : (0 : ℕ) ≠ 3)
            (V.child x) (K.child j)
        | abs y Q =>
          exact eqB_lamTag_mismatch_le (by decide : (0 : ℕ) ≠ 1)
            (V.child x) (opairB (V.child y) (encodeLamDKB V K Q))
        | app P' Q' =>
          exact eqB_lamTag_mismatch_le (by decide : (0 : ℕ) ≠ 2)
            (V.child x) (opairB (encodeLamDKB V K P') (encodeLamDKB V K Q'))
      | const i =>
        cases N with
        | var y =>
          exact eqB_lamTag_mismatch_le (by decide : (3 : ℕ) ≠ 0)
            (K.child i) (V.child y)
        | const j =>
          rw [eqB_encodeLamDKB_const_const, lamDKVal, lamDKVal]
          exact eqB_inf_memB_le (K.child i) (K.child j) K
        | abs y Q =>
          exact eqB_lamTag_mismatch_le (by decide : (3 : ℕ) ≠ 1)
            (K.child i) (opairB (V.child y) (encodeLamDKB V K Q))
        | app P' Q' =>
          exact eqB_lamTag_mismatch_le (by decide : (3 : ℕ) ≠ 2)
            (K.child i) (opairB (encodeLamDKB V K P') (encodeLamDKB V K Q'))
      | abs x P =>
        cases N with
        | var y =>
          exact eqB_lamTag_mismatch_le (by decide : (1 : ℕ) ≠ 0)
            (opairB (V.child x) (encodeLamDKB V K P)) (V.child y)
        | const j =>
          exact eqB_lamTag_mismatch_le (by decide : (1 : ℕ) ≠ 3)
            (opairB (V.child x) (encodeLamDKB V K P)) (K.child j)
        | abs y Q =>
          rw [eqB_encodeLamDKB_abs_abs, lamDKVal, lamDKVal]
          refine le_inf ?_ ?_
          · exact (eqB_inf_memB_le (V.child x) (V.child y) V).trans' <|
              le_inf (inf_le_left.trans inf_le_left)
                (inf_le_right.trans inf_le_left)
          · have hlt : P.weight + Q.weight < n := by
              rw [← hsum]
              simp [LamDK.weight]
              omega
            exact (ih (P.weight + Q.weight) hlt P Q rfl).trans' <|
              le_inf (inf_le_left.trans inf_le_right)
                (inf_le_right.trans inf_le_right)
        | app P' Q' =>
          exact eqB_lamTag_mismatch_le (by decide : (1 : ℕ) ≠ 2)
            (opairB (V.child x) (encodeLamDKB V K P))
            (opairB (encodeLamDKB V K P') (encodeLamDKB V K Q'))
      | app P Q =>
        cases N with
        | var y =>
          exact eqB_lamTag_mismatch_le (by decide : (2 : ℕ) ≠ 0)
            (opairB (encodeLamDKB V K P) (encodeLamDKB V K Q)) (V.child y)
        | const j =>
          exact eqB_lamTag_mismatch_le (by decide : (2 : ℕ) ≠ 3)
            (opairB (encodeLamDKB V K P) (encodeLamDKB V K Q)) (K.child j)
        | abs y Q' =>
          exact eqB_lamTag_mismatch_le (by decide : (2 : ℕ) ≠ 1)
            (opairB (encodeLamDKB V K P) (encodeLamDKB V K Q))
            (opairB (V.child y) (encodeLamDKB V K Q'))
        | app P' Q' =>
          rw [eqB_encodeLamDKB_app_app, lamDKVal, lamDKVal]
          refine le_inf ?_ ?_
          · have hlt : P.weight + P'.weight < n := by
              rw [← hsum]
              simp [LamDK.weight]
              omega
            exact (ih (P.weight + P'.weight) hlt P P' rfl).trans' <|
              le_inf (inf_le_left.trans inf_le_left)
                (inf_le_right.trans inf_le_left)
          · have hlt : Q.weight + Q'.weight < n := by
              rw [← hsum]
              simp [LamDK.weight]
              omega
            exact (ih (Q.weight + Q'.weight) hlt Q Q' rfl).trans' <|
              le_inf (inf_le_left.trans inf_le_right)
                (inf_le_right.trans inf_le_right)
  exact this _ M N rfl

theorem interpDKRelVal_encode_congr
    (𝓜 : InternalReflexiveModel (A := A))
    (V K : AName.{u} A) (hK : subsetB K 𝓜.D = ⊤)
    (hV : (oid V).IsTotal)
    (η : RelFun (oid V) (oid 𝓜.D))
    (M N : LamDK V.idx K.idx) (d : 𝓜.D.idx) :
    eqB (encodeLamDKB V K M) (encodeLamDKB V K N) ⊓
        interpDKRelVal 𝓜 V K hK hV η M d ≤
      interpDKRelVal 𝓜 V K hK hV η N d := by
  have : ∀ n M N (η : RelFun (oid V) (oid 𝓜.D)) (d : 𝓜.D.idx),
      M.weight + N.weight = n →
      eqB (encodeLamDKB V K M) (encodeLamDKB V K N) ⊓
          interpDKRelVal 𝓜 V K hK hV η M d ≤
        interpDKRelVal 𝓜 V K hK hV η N d := by
    intro n
    induction n using Nat.strongRecOn with
    | ind n ih =>
      intro M N η d hsum
      cases M with
      | var x =>
        cases N with
        | var y =>
          rw [eqB_encodeLamDKB_var_var, interpDKRelVal_var, interpDKRelVal_var]
          have hxy : eqB (V.child x) (V.child y) = (oid V).eq x y :=
            (oid_eq_of_total V hV x y).symm
          rw [hxy]
          exact η.subst_left x y d
        | const j =>
          exact eqB_lamTag_mismatch_le (by decide : (0 : ℕ) ≠ 3)
            (V.child x) (K.child j)
        | abs y Q =>
          exact eqB_lamTag_mismatch_le (by decide : (0 : ℕ) ≠ 1)
            (V.child x) (opairB (V.child y) (encodeLamDKB V K Q))
        | app P' Q' =>
          exact eqB_lamTag_mismatch_le (by decide : (0 : ℕ) ≠ 2)
            (V.child x) (opairB (encodeLamDKB V K P') (encodeLamDKB V K Q'))
      | const i =>
        cases N with
        | var y =>
          exact eqB_lamTag_mismatch_le (by decide : (3 : ℕ) ≠ 0)
            (K.child i) (V.child y)
        | const j =>
          rw [eqB_encodeLamDKB_const_const, interpDKRelVal_const,
            interpDKRelVal_const, oidSubsetRel_val, oidSubsetRel_val]
          refine le_inf ?_ ?_
          · exact (memB_eqB_left (K.child i) K (K.child j)).trans' <|
              le_inf (inf_le_right.trans inf_le_left) inf_le_left
          · exact (eqB_trans (K.child j) (K.child i) (𝓜.D.child d)).trans' <|
              le_inf (inf_le_left.trans_eq (eqB_comm (K.child i) (K.child j)))
                (inf_le_right.trans inf_le_right)
        | abs y Q =>
          exact eqB_lamTag_mismatch_le (by decide : (3 : ℕ) ≠ 1)
            (K.child i) (opairB (V.child y) (encodeLamDKB V K Q))
        | app P' Q' =>
          exact eqB_lamTag_mismatch_le (by decide : (3 : ℕ) ≠ 2)
            (K.child i) (opairB (encodeLamDKB V K P') (encodeLamDKB V K Q'))
      | abs x P =>
        cases N with
        | var y =>
          exact eqB_lamTag_mismatch_le (by decide : (1 : ℕ) ≠ 0)
            (opairB (V.child x) (encodeLamDKB V K P)) (V.child y)
        | const j =>
          exact eqB_lamTag_mismatch_le (by decide : (1 : ℕ) ≠ 3)
            (opairB (V.child x) (encodeLamDKB V K P)) (K.child j)
        | abs y Q =>
          rw [eqB_encodeLamDKB_abs_abs, interpDKRelVal_abs, interpDKRelVal_abs]
          refine le_inf ?_ ?_
          · exact (lamDKVal_encode_congr V K (.abs x P) (.abs y Q)).trans' <|
              le_inf (by
                rw [eqB_encodeLamDKB_abs_abs]
                exact inf_le_left) (inf_le_right.trans inf_le_left)
          · have hlt : P.weight + Q.weight < n := by
              rw [← hsum]
              simp [LamDK.weight]
              omega
            have hbody :
                eqB (V.child x) (V.child y) ⊓
                    eqB (encodeLamDKB V K P) (encodeLamDKB V K Q) ≤
                  eqB (interpDKBodyGraph 𝓜 V K hK hV η x P)
                    (interpDKBodyGraph 𝓜 V K hK hV η y Q) := by
              apply le_eqB_mk_of_le_val
                (fun p : 𝓜.D.idx × 𝓜.D.idx =>
                  opairB (𝓜.D.child p.1) (𝓜.D.child p.2))
              · intro p
                have hkey :=
                  interpDKRelVal_update_key 𝓜 V K hK hV η x y p.1 P p.2
                have hxy : eqB (V.child x) (V.child y) = (oid V).eq x y :=
                  (oid_eq_of_total V hV x y).symm
                have hPQ :=
                  ih (P.weight + Q.weight) hlt P Q
                    (η.update hV 𝓜.total y p.1) p.2 rfl
                let s :=
                  (eqB (V.child x) (V.child y) ⊓
                      eqB (encodeLamDKB V K P) (encodeLamDKB V K Q)) ⊓
                    interpDKRelVal 𝓜 V K hK hV
                      (η.update hV 𝓜.total x p.1) P p.2
                have hxy' : s ≤ (oid V).eq x y := by
                  rw [← hxy]
                  exact inf_le_left.trans inf_le_left
                have hPx : s ≤ interpDKRelVal 𝓜 V K hK hV
                    (η.update hV 𝓜.total x p.1) P p.2 := inf_le_right
                have hPy : s ≤ interpDKRelVal 𝓜 V K hK hV
                    (η.update hV 𝓜.total y p.1) P p.2 :=
                  hkey.trans' (le_inf hxy' hPx)
                have henc : s ≤ eqB (encodeLamDKB V K P)
                    (encodeLamDKB V K Q) :=
                  inf_le_left.trans inf_le_right
                exact hPQ.trans' (le_inf henc hPy)
              · intro p
                have hkey :=
                  interpDKRelVal_update_key 𝓜 V K hK hV η y x p.1 Q p.2
                have hyx : eqB (V.child y) (V.child x) = (oid V).eq y x :=
                  (oid_eq_of_total V hV y x).symm
                have hQP :=
                  ih (Q.weight + P.weight) (by
                      rw [← hsum]
                      simp [LamDK.weight]
                      omega)
                    Q P (η.update hV 𝓜.total x p.1) p.2 rfl
                let s :=
                  (eqB (V.child x) (V.child y) ⊓
                      eqB (encodeLamDKB V K P) (encodeLamDKB V K Q)) ⊓
                    interpDKRelVal 𝓜 V K hK hV
                      (η.update hV 𝓜.total y p.1) Q p.2
                have hyx' : s ≤ (oid V).eq y x := by
                  rw [← hyx, eqB_comm]
                  exact inf_le_left.trans inf_le_left
                have hQy : s ≤ interpDKRelVal 𝓜 V K hK hV
                    (η.update hV 𝓜.total y p.1) Q p.2 := inf_le_right
                have hQx : s ≤ interpDKRelVal 𝓜 V K hK hV
                    (η.update hV 𝓜.total x p.1) Q p.2 :=
                  hkey.trans' (le_inf hyx' hQy)
                have henc : s ≤ eqB (encodeLamDKB V K Q)
                    (encodeLamDKB V K P) := by
                  rw [eqB_comm]
                  exact inf_le_left.trans inf_le_right
                exact hQP.trans' (le_inf henc hQx)
            refine (memB_opairB_congr 𝓜.Lam
                (interpDKBodyGraph 𝓜 V K hK hV η x P)
                (interpDKBodyGraph 𝓜 V K hK hV η y Q)
                (𝓜.D.child d) (𝓜.D.child d)).trans' ?_
            refine le_inf (le_inf ?_ ?_) ?_
            · exact (inf_le_left.trans hbody)
            · exact le_top.trans (eqB_self (A := A) (𝓜.D.child d)).ge
            · exact inf_le_right.trans inf_le_right
        | app P' Q' =>
          exact eqB_lamTag_mismatch_le (by decide : (1 : ℕ) ≠ 2)
            (opairB (V.child x) (encodeLamDKB V K P))
            (opairB (encodeLamDKB V K P') (encodeLamDKB V K Q'))
      | app P Q =>
        cases N with
        | var y =>
          exact eqB_lamTag_mismatch_le (by decide : (2 : ℕ) ≠ 0)
            (opairB (encodeLamDKB V K P) (encodeLamDKB V K Q)) (V.child y)
        | const j =>
          exact eqB_lamTag_mismatch_le (by decide : (2 : ℕ) ≠ 3)
            (opairB (encodeLamDKB V K P) (encodeLamDKB V K Q)) (K.child j)
        | abs y Q' =>
          exact eqB_lamTag_mismatch_le (by decide : (2 : ℕ) ≠ 1)
            (opairB (encodeLamDKB V K P) (encodeLamDKB V K Q))
            (opairB (V.child y) (encodeLamDKB V K Q'))
        | app P' Q' =>
          rw [eqB_encodeLamDKB_app_app, interpDKRelVal_app, interpDKRelVal_app]
          rw [inf_iSup_eq]
          refine iSup_le fun c => le_iSup_of_le c ?_
          rw [inf_iSup_eq]
          refine iSup_le fun q' => le_iSup_of_le q' ?_
          rw [inf_iSup_eq]
          refine iSup_le fun p => le_iSup_of_le p ?_
          rw [inf_iSup_eq]
          refine iSup_le fun q => le_iSup_of_le q ?_
          let t :=
            (eqB (encodeLamDKB V K P) (encodeLamDKB V K P') ⊓
                eqB (encodeLamDKB V K Q) (encodeLamDKB V K Q')) ⊓
              (interpDKRelVal 𝓜 V K hK hV η P p ⊓
                interpDKRelVal 𝓜 V K hK hV η Q q ⊓
                memB (opairB (𝓜.D.child p) (𝓜.C.child c)) 𝓜.Fun ⊓
                (oid 𝓜.D).eq q q' ⊓
                memB (𝓜.C.child c) 𝓜.C ⊓
                memB (opairB (𝓜.D.child q') (𝓜.D.child d))
                  (𝓜.C.child c))
          change t ≤
            interpDKRelVal 𝓜 V K hK hV η P' p ⊓
              interpDKRelVal 𝓜 V K hK hV η Q' q ⊓
              memB (opairB (𝓜.D.child p) (𝓜.C.child c)) 𝓜.Fun ⊓
              (oid 𝓜.D).eq q q' ⊓
              memB (𝓜.C.child c) 𝓜.C ⊓
              memB (opairB (𝓜.D.child q') (𝓜.D.child d))
                (𝓜.C.child c)
          have hP : P.weight + P'.weight < n := by
            rw [← hsum]
            simp [LamDK.weight]
            omega
          have hQlt : Q.weight + Q'.weight < n := by
            rw [← hsum]
            simp [LamDK.weight]
            omega
          have hPval :=
            ih (P.weight + P'.weight) hP P P' η p rfl
          have hQval :=
            ih (Q.weight + Q'.weight) hQlt Q Q' η q rfl
          refine le_inf (le_inf (le_inf (le_inf (le_inf ?_ ?_) ?_) ?_) ?_) ?_
          · exact hPval.trans' <|
              le_inf (inf_le_left.trans inf_le_left)
                (inf_le_right.trans (inf_le_left.trans
                  (inf_le_left.trans (inf_le_left.trans
                    (inf_le_left.trans inf_le_left)))))
          · exact hQval.trans' <|
              le_inf (inf_le_left.trans inf_le_right)
                (inf_le_right.trans (inf_le_left.trans
                  (inf_le_left.trans (inf_le_left.trans
                    (inf_le_left.trans inf_le_right)))))
          · exact inf_le_right.trans (inf_le_left.trans
              (inf_le_left.trans (inf_le_left.trans inf_le_right)))
          · exact inf_le_right.trans (inf_le_left.trans
              (inf_le_left.trans inf_le_right))
          · exact inf_le_right.trans (inf_le_left.trans inf_le_right)
          · exact inf_le_right.trans inf_le_right
  exact this _ M N η d rfl

open InternalReflexiveModel

/-- Application case of the extent-indexed fundamental relation lemma. -/
theorem interpDKRelVal_app_isRelElementAt
    (𝓜 : InternalReflexiveModel (A := A))
    (V K : AName.{u} A) (hK : subsetB K 𝓜.D = ⊤)
    (hV : (oid V).IsTotal)
    (η : RelFun (oid V) (oid 𝓜.D))
    (P Q : LamDK V.idx K.idx)
    (hP : IsRelElementAt 𝓜.D (lamDKVal V K P)
      (interpDKRelVal 𝓜 V K hK hV η P))
    (hQ : IsRelElementAt 𝓜.D (lamDKVal V K Q)
      (interpDKRelVal 𝓜 V K hK hV η Q)) :
    IsRelElementAt 𝓜.D (lamDKVal V K (.app P Q))
      (interpDKRelVal 𝓜 V K hK hV η (.app P Q)) := by
  let f := applyRelOfElements 𝓜 hP hQ
  have h := isRelElementAt_of_relFun (f.at (PUnit.unit, PUnit.unit))
  change IsRelElementAt 𝓜.D
    (lamDKVal V K P ⊓ lamDKVal V K Q)
    (fun d => f.val (PUnit.unit, PUnit.unit) d) at h
  change IsRelElementAt 𝓜.D
    (lamDKVal V K P ⊓ lamDKVal V K Q) _
  have heval :
      interpDKRelVal 𝓜 V K hK hV η (.app P Q) =
        fun d => f.val (PUnit.unit, PUnit.unit) d := by
    funext d
    rw [interpDKRelVal_app]
    exact (applyRelOfElements_val 𝓜 hP hQ (PUnit.unit, PUnit.unit) d).symm
  rw [heval]
  exact h

/-!
## Application wrapper at native degrees
-/

/-- Induction-ready application continuity: constructor IHs arrive at
`lamDKVal P` and `lamDKVal Q` separately. -/
theorem interpDKBodyGraph_app_le_scottContinuous_meet
    (𝓜 : InternalReflexiveModel (A := A))
    (V K : AName.{u} A) (hK : subsetB K 𝓜.D = ⊤)
    (hV : (oid V).IsTotal)
    (η : RelFun (oid V) (oid 𝓜.D))
    (x : V.idx) (P Q : LamDK V.idx K.idx)
    (hP : ∀ d, IsRelElementAt 𝓜.D (lamDKVal V K P)
      (interpDKRelVal 𝓜 V K hK hV
        (η.update hV 𝓜.total x d) P))
    (hQ : ∀ d, IsRelElementAt 𝓜.D (lamDKVal V K Q)
      (interpDKRelVal 𝓜 V K hK hV
        (η.update hV 𝓜.total x d) Q))
    (hPsc : lamDKVal V K P ≤ isScottContinuousB
      (interpDKBodyGraph 𝓜 V K hK hV η x P) 𝓜.D 𝓜.D 𝓜.R 𝓜.R)
    (hQsc : lamDKVal V K Q ≤ isScottContinuousB
      (interpDKBodyGraph 𝓜 V K hK hV η x Q) 𝓜.D 𝓜.D 𝓜.R 𝓜.R) :
    lamDKVal V K P ⊓ lamDKVal V K Q ≤
      isScottContinuousB
        (interpDKBodyGraph 𝓜 V K hK hV η x (.app P Q))
        𝓜.D 𝓜.D 𝓜.R 𝓜.R := by
  let a := lamDKVal V K P ⊓ lamDKVal V K Q
  have happ : ∀ d, IsRelElementAt 𝓜.D a
      (interpDKRelVal 𝓜 V K hK hV
        (η.update hV 𝓜.total x d) (.app P Q)) :=
    fun d =>
      interpDKRelVal_app_isRelElementAt 𝓜 V K hK hV
        (η.update hV 𝓜.total x d) P Q (hP d) (hQ d)
  have hfun : a ≤ isFunctionB
      (interpDKBodyGraph 𝓜 V K hK hV η x (.app P Q)) 𝓜.D 𝓜.D :=
    interpDKBodyGraph_le_isFunctionB 𝓜 V K hK hV η x (.app P Q) a happ
  have hPsc' : a ≤ isScottContinuousB
      (interpDKBodyGraph 𝓜 V K hK hV η x P) 𝓜.D 𝓜.D 𝓜.R 𝓜.R :=
    inf_le_left.trans hPsc
  have hQsc' : a ≤ isScottContinuousB
      (interpDKBodyGraph 𝓜 V K hK hV η x Q) 𝓜.D 𝓜.D 𝓜.R 𝓜.R :=
    inf_le_right.trans hQsc
  unfold isScottContinuousB
  refine le_inf (le_inf ?_ ?_) ?_
  · exact hfun
  · refine le_iInf fun u => le_iInf fun u' =>
      le_iInf fun v => le_iInf fun v' => ?_
    rw [le_himp_iff]
    exact (interpDKBodyGraph_app_apply_mono
        𝓜 V K hK hV η x P Q (lamDKVal V K P ⊓ lamDKVal V K Q)
        hPsc' hQsc' u u' v v').trans' <| by
      apply le_of_eq
      ac_rfl
  · refine le_iInf fun S => le_iInf fun u => le_iInf fun v => ?_
    rw [le_himp_iff]
    exact (interpDKBodyGraph_app_mapsToSup
        𝓜 V K hK hV η x P Q (lamDKVal V K P ⊓ lamDKVal V K Q)
        hfun hPsc' hQsc' S u v).trans' <| by
      apply le_of_eq
      ac_rfl

/-!
## Term induction
-/

theorem interpDK_term_induction
    (𝓜 : InternalReflexiveModel (A := A))
    (V K : AName.{u} A) (hK : subsetB K 𝓜.D = ⊤)
    (hV : (oid V).IsTotal)
    (M : LamDK V.idx K.idx) :
    ∀ (η : RelFun (oid V) (oid 𝓜.D)),
      IsRelElementAt 𝓜.D (lamDKVal V K M)
        (interpDKRelVal 𝓜 V K hK hV η M) ∧
      ∀ (x : V.idx),
        lamDKVal V K M ≤
          isScottContinuousB
            (interpDKBodyGraph 𝓜 V K hK hV η x M)
            𝓜.D 𝓜.D 𝓜.R 𝓜.R := by
  induction M with
  | var x =>
    intro η
    exact ⟨interpDKRelVal_var_isRelElementAt 𝓜 V K hK hV η x,
      fun y => le_top.trans
        (interpDKBodyGraph_any_var_scottContinuous 𝓜 V K hK hV η y x).ge⟩
  | const k =>
    intro η
    exact ⟨interpDKRelVal_const_isRelElementAt 𝓜 V K hK hV η k,
      fun y => interpDKBodyGraph_const_le_scottContinuous
        𝓜 V K hK hV η y k⟩
  | app P Q ihP ihQ =>
    intro η
    refine ⟨interpDKRelVal_app_isRelElementAt 𝓜 V K hK hV η P Q
        (ihP η).1 (ihQ η).1, fun x => ?_⟩
    exact interpDKBodyGraph_app_le_scottContinuous_meet
      𝓜 V K hK hV η x P Q
      (fun d => (ihP (η.update hV 𝓜.total x d)).1)
      (fun d => (ihQ (η.update hV 𝓜.total x d)).1)
      ((ihP η).2 x) ((ihQ η).2 x)
  | abs x P ih =>
    intro η
    constructor
    · have h :=
        interpDKRelVal_abs_isRelElementAt 𝓜 V K hK hV η x P
          (lamDKVal V K P) ((ih η).2 x)
          (fun d => (ih (η.update hV 𝓜.total x d)).1)
      refine IsRelElementAt.congr_degree h ?_
      change lamDKVal V K P ⊓
          (memB (V.child x) V ⊓ lamDKVal V K P) =
        memB (V.child x) V ⊓ lamDKVal V K P
      ac_rfl
    · intro y
      have h :=
        interpDKBodyGraph_abs_le_scottContinuous 𝓜 V K hK hV η y x P
          (lamDKVal V K P)
          (fun d => (ih (η.update hV 𝓜.total y d)).2 x)
          (fun d e =>
            (ih ((η.update hV 𝓜.total y d).update hV 𝓜.total x e)).1)
          (fun z => (ih (η.update hV 𝓜.total x z)).2 y)
          (fun z d =>
            (ih ((η.update hV 𝓜.total x z).update hV 𝓜.total y d)).1)
      refine h.trans' ?_
      rw [lamDKVal]
      exact le_inf (le_inf inf_le_right inf_le_left) inf_le_right

theorem interpDKRelVal_isRelElementAt
    (𝓜 : InternalReflexiveModel (A := A))
    (V K : AName.{u} A) (hK : subsetB K 𝓜.D = ⊤)
    (hV : (oid V).IsTotal)
    (η : RelFun (oid V) (oid 𝓜.D))
    (M : LamDK V.idx K.idx) :
    IsRelElementAt 𝓜.D (lamDKVal V K M)
      (interpDKRelVal 𝓜 V K hK hV η M) :=
  (interpDK_term_induction 𝓜 V K hK hV M η).1

theorem interpDKBodyGraph_le_scottContinuous
    (𝓜 : InternalReflexiveModel (A := A))
    (V K : AName.{u} A) (hK : subsetB K 𝓜.D = ⊤)
    (hV : (oid V).IsTotal)
    (η : RelFun (oid V) (oid 𝓜.D))
    (x : V.idx) (M : LamDK V.idx K.idx) :
    lamDKVal V K M ≤
      isScottContinuousB
        (interpDKBodyGraph 𝓜 V K hK hV η x M)
        𝓜.D 𝓜.D 𝓜.R 𝓜.R :=
  (interpDK_term_induction 𝓜 V K hK hV M η).2 x

end Scott2026
