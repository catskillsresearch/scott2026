/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/

import Scott2026.InternalEvalComplete

/-!
# Term induction and the Theorem 26 evaluator name

This module closes Definition 25 by induction on `LamDK`, assembles the
internal evaluator graph, and proves it is an internal function
`lamDKB D V K → D`.
-/

universe u

namespace Scott2026

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

/-- `AName.idx` is not unfolded by rewrite, so we reify the `lamDKB` carrier. -/
noncomputable def asLamDK (D V K : AName.{u} A)
    (M : (lamDKB D V K).idx) : LamDK V.idx K.idx :=
  cast (by rw [lamDKB, idx_mk]) M

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

noncomputable def asLam (V : AName.{u} A) (M : (lamB V).idx) : Lam V.idx :=
  cast (by rw [lamB, idx_mk]) M

theorem asLam_encode (V : AName.{u} A) (M : (lamB V).idx) :
    encodeLamB V (asLam V M) = (lamB V).child M := by
  unfold asLam lamB
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

def LamDK.weight {Var Const : Type u} : LamDK Var Const → ℕ
  | .var _ => 1
  | .const _ => 1
  | .abs _ M => M.weight + 1
  | .app M N => M.weight + N.weight + 1

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

/-!
## Evaluator name
-/

/-- Relational function assembled from the term-indexed evaluation rows. -/
noncomputable def InternalReflexiveModel.interpDKRel
    (𝓜 : InternalReflexiveModel (A := A))
    (V K : AName.{u} A) (hK : subsetB K 𝓜.D = ⊤)
    (hV : (oid V).IsTotal)
    (η : RelFun (oid V) (oid 𝓜.D)) :
    RelFun (oid (lamDKB 𝓜.D V K)) (oid 𝓜.D) where
  val M d :=
    interpDKRelVal 𝓜 V K hK hV η (asLamDK 𝓜.D V K M) d
  respects := by
    intro M N d e
    refine le_inf ?_ ?_ <;> rw [le_himp_iff]
    · let t :=
        (oid (lamDKB 𝓜.D V K)).eq M N ⊓ (oid 𝓜.D).eq d e ⊓
          interpDKRelVal 𝓜 V K hK hV η (asLamDK 𝓜.D V K M) d
      have henc :
          t ≤ eqB (encodeLamDKB V K (asLamDK 𝓜.D V K M))
            (encodeLamDKB V K (asLamDK 𝓜.D V K N)) := by
        rw [asLamDK_encode, asLamDK_encode]
        exact (oid_eq_le_eqB_child _ M N).trans'
          (inf_le_left.trans inf_le_left)
      have hval :
          t ≤ interpDKRelVal 𝓜 V K hK hV η (asLamDK 𝓜.D V K M) d :=
        inf_le_right
      have hN :
          t ≤ interpDKRelVal 𝓜 V K hK hV η (asLamDK 𝓜.D V K N) d :=
        (interpDKRelVal_encode_congr 𝓜 V K hK hV η
          (asLamDK 𝓜.D V K M) (asLamDK 𝓜.D V K N) d).trans'
          (le_inf henc hval)
      have hde : t ≤ (oid 𝓜.D).eq d e := inf_le_left.trans inf_le_right
      exact (interpDKRelVal_isRelElementAt 𝓜 V K hK hV η
          (asLamDK 𝓜.D V K N)).respects d e |>.trans' (le_inf hde hN)
    · let t :=
        (oid (lamDKB 𝓜.D V K)).eq M N ⊓ (oid 𝓜.D).eq d e ⊓
          interpDKRelVal 𝓜 V K hK hV η (asLamDK 𝓜.D V K N) e
      have henc :
          t ≤ eqB (encodeLamDKB V K (asLamDK 𝓜.D V K N))
            (encodeLamDKB V K (asLamDK 𝓜.D V K M)) := by
        rw [asLamDK_encode, asLamDK_encode, eqB_comm]
        exact (oid_eq_le_eqB_child _ M N).trans'
          (inf_le_left.trans inf_le_left)
      have hval :
          t ≤ interpDKRelVal 𝓜 V K hK hV η (asLamDK 𝓜.D V K N) e :=
        inf_le_right
      have hM :
          t ≤ interpDKRelVal 𝓜 V K hK hV η (asLamDK 𝓜.D V K M) e :=
        (interpDKRelVal_encode_congr 𝓜 V K hK hV η
          (asLamDK 𝓜.D V K N) (asLamDK 𝓜.D V K M) e).trans'
          (le_inf henc hval)
      have hde : t ≤ (oid 𝓜.D).eq e d := by
        rw [(oid 𝓜.D).symm]
        exact inf_le_left.trans inf_le_right
      exact (interpDKRelVal_isRelElementAt 𝓜 V K hK hV η
          (asLamDK 𝓜.D V K M)).respects e d |>.trans' (le_inf hde hM)
  le_eps := by
    intro M d
    have h :=
      (interpDKRelVal_isRelElementAt 𝓜 V K hK hV η
        (asLamDK 𝓜.D V K M)).2.1 d
    rw [oid_eps, oid_eps]
    refine le_inf ?_ ?_
    · have hmem :=
        lamDKVal_le_memB 𝓜.D V K (asLamDK 𝓜.D V K M)
      rw [asLamDK_encode] at hmem
      exact hmem.trans' (h.trans inf_le_left)
    · rw [oid_eps] at h
      exact h.trans inf_le_right
  single_valued := by
    intro M d e
    exact (interpDKRelVal_isRelElementAt 𝓜 V K hK hV η
      (asLamDK 𝓜.D V K M)).2.2.1 d e
  total := by
    intro M
    rw [oid_eps, memB_lamDKB]
    refine iSup_le fun N => ?_
    have htot :=
      (interpDKRelVal_isRelElementAt 𝓜 V K hK hV η N).2.2.2
    refine (le_inf le_rfl (inf_le_right.trans htot)).trans ?_
    rw [inf_iSup_eq]
    refine iSup_le fun d => le_iSup_of_le d ?_
    refine (interpDKRelVal_encode_congr 𝓜 V K hK hV η N
      (asLamDK 𝓜.D V K M) d).trans' ?_
    calc
      eqB ((lamDKB 𝓜.D V K).child M) (encodeLamDKB V K N) ⊓
          lamDKVal V K N ⊓ interpDKRelVal 𝓜 V K hK hV η N d
        = eqB (encodeLamDKB V K (asLamDK 𝓜.D V K M))
            (encodeLamDKB V K N) ⊓
          lamDKVal V K N ⊓ interpDKRelVal 𝓜 V K hK hV η N d := by
            rw [asLamDK_encode]
      _ ≤ eqB (encodeLamDKB V K (asLamDK 𝓜.D V K M))
            (encodeLamDKB V K N) ⊓
          interpDKRelVal 𝓜 V K hK hV η N d :=
            le_inf (inf_le_left.trans inf_le_left) inf_le_right
      _ = eqB (encodeLamDKB V K N)
            (encodeLamDKB V K (asLamDK 𝓜.D V K M)) ⊓
          interpDKRelVal 𝓜 V K hK hV η N d := by
            rw [eqB_comm (encodeLamDKB V K (asLamDK 𝓜.D V K M))
              (encodeLamDKB V K N)]

@[simp] theorem InternalReflexiveModel.interpDKRel_val
    (𝓜 : InternalReflexiveModel (A := A))
    (V K : AName.{u} A) (hK : subsetB K 𝓜.D = ⊤)
    (hV : (oid V).IsTotal)
    (η : RelFun (oid V) (oid 𝓜.D))
    (M : (lamDKB 𝓜.D V K).idx) (d : 𝓜.D.idx) :
    (interpDKRel 𝓜 V K hK hV η).val M d =
      interpDKRelVal 𝓜 V K hK hV η (asLamDK 𝓜.D V K M) d :=
  rfl

noncomputable def InternalReflexiveModel.interpDKGraph
    (𝓜 : InternalReflexiveModel (A := A))
    (V K : AName.{u} A) (hK : subsetB K 𝓜.D = ⊤)
    (hV : (oid V).IsTotal)
    (η : RelFun (oid V) (oid 𝓜.D)) :
    AName.{u} A :=
  AName.mk (LamDK V.idx K.idx × 𝓜.D.idx)
    (fun p => opairB (encodeLamDKB V K p.1) (𝓜.D.child p.2))
    (fun p => interpDKRelVal 𝓜 V K hK hV η p.1 p.2)

theorem InternalReflexiveModel.interpDKGraph_eq_relFunGraphName
    (𝓜 : InternalReflexiveModel (A := A))
    (V K : AName.{u} A) (hK : subsetB K 𝓜.D = ⊤)
    (hV : (oid V).IsTotal)
    (η : RelFun (oid V) (oid 𝓜.D)) :
    interpDKGraph 𝓜 V K hK hV η =
      relFunGraphName (lamDKB 𝓜.D V K) 𝓜.D
        (interpDKRel 𝓜 V K hK hV η) := by
  unfold interpDKGraph relFunGraphName interpDKRel lamDKB asLamDK
  rfl

theorem InternalReflexiveModel.interpDKGraph_isFunctionB
    (𝓜 : InternalReflexiveModel (A := A))
    (V K : AName.{u} A) (hK : subsetB K 𝓜.D = ⊤)
    (hV : (oid V).IsTotal)
    (η : RelFun (oid V) (oid 𝓜.D)) :
    isFunctionB (interpDKGraph 𝓜 V K hK hV η)
      (lamDKB 𝓜.D V K) 𝓜.D = ⊤ := by
  rw [interpDKGraph_eq_relFunGraphName]
  exact isFunctionB_relFunGraphName _ _ _

theorem InternalReflexiveModel.interpDKGraph_isFunctionB_of_valuation
    (𝓜 : InternalReflexiveModel (A := A))
    (V K : AName.{u} A) (hK : subsetB K 𝓜.D = ⊤)
    (hV : (oid V).IsTotal)
    (Dom Rho : AName.{u} A)
    (hVal : isValuationB V 𝓜.D Dom Rho = ⊤) :
    isFunctionB
      (interpDKGraph 𝓜 V K hK hV
        (totalizedValuationRelOfValid V 𝓜.D Dom Rho hVal
          𝓜.total 𝓜.complete))
      (lamDKB 𝓜.D V K) 𝓜.D = ⊤ :=
  interpDKGraph_isFunctionB 𝓜 V K hK hV _

/-!
## Pure-term restriction
-/

theorem encodeLamDKB_ofLam (V K : AName.{u} A) (M : Lam V.idx) :
    encodeLamDKB V K (LamDK.ofLam M) = encodeLamB V M := by
  induction M with
  | var x => rfl
  | abs x P ih =>
    simp only [LamDK.ofLam, encodeLamDKB, encodeLamB, ih]
  | app P Q ihP ihQ =>
    simp only [LamDK.ofLam, encodeLamDKB, encodeLamB, ihP, ihQ]

theorem encodeLamDKB_ofLam_asLam
    (V K : AName.{u} A) (M : (lamB V).idx) :
    encodeLamDKB V K (LamDK.ofLam (asLam V M)) = (lamB V).child M := by
  rw [encodeLamDKB_ofLam, asLam_encode]

theorem lamDKVal_ofLam (V K : AName.{u} A) (hV : (oid V).IsTotal)
    (M : Lam V.idx) :
    lamDKVal V K (LamDK.ofLam M) = ⊤ := by
  induction M with
  | var x =>
    change memB (V.child x) V = ⊤
    rw [← oid_eps]
    exact hV x
  | abs x P ih =>
    rw [LamDK.ofLam, lamDKVal, ih, inf_top_eq]
    rw [← oid_eps]
    exact hV x
  | app P Q ihP ihQ =>
    rw [LamDK.ofLam, lamDKVal, ihP, ihQ, inf_top_eq]

noncomputable def InternalReflexiveModel.interpDKPureRel
    (𝓜 : InternalReflexiveModel (A := A))
    (V K : AName.{u} A) (hK : subsetB K 𝓜.D = ⊤)
    (hV : (oid V).IsTotal)
    (η : RelFun (oid V) (oid 𝓜.D)) :
    RelFun (oid (lamB V)) (oid 𝓜.D) where
  val M d :=
    interpDKRelVal 𝓜 V K hK hV η (LamDK.ofLam (asLam V M)) d
  respects := by
    intro M N d e
    refine le_inf ?_ ?_ <;> rw [le_himp_iff]
    · let t :=
        (oid (lamB V)).eq M N ⊓ (oid 𝓜.D).eq d e ⊓
          interpDKRelVal 𝓜 V K hK hV η (LamDK.ofLam (asLam V M)) d
      have henc :
          t ≤ eqB (encodeLamDKB V K (LamDK.ofLam (asLam V M)))
            (encodeLamDKB V K (LamDK.ofLam (asLam V N))) := by
        rw [encodeLamDKB_ofLam_asLam, encodeLamDKB_ofLam_asLam]
        exact (oid_eq_le_eqB_child _ M N).trans'
          (inf_le_left.trans inf_le_left)
      have hval :
          t ≤ interpDKRelVal 𝓜 V K hK hV η
            (LamDK.ofLam (asLam V M)) d := inf_le_right
      have hN :
          t ≤ interpDKRelVal 𝓜 V K hK hV η
            (LamDK.ofLam (asLam V N)) d :=
        (interpDKRelVal_encode_congr 𝓜 V K hK hV η
          (LamDK.ofLam (asLam V M)) (LamDK.ofLam (asLam V N)) d).trans'
          (le_inf henc hval)
      have hde : t ≤ (oid 𝓜.D).eq d e := inf_le_left.trans inf_le_right
      exact (interpDKRelVal_isRelElementAt 𝓜 V K hK hV η
          (LamDK.ofLam (asLam V N))).respects d e |>.trans'
        (le_inf hde hN)
    · let t :=
        (oid (lamB V)).eq M N ⊓ (oid 𝓜.D).eq d e ⊓
          interpDKRelVal 𝓜 V K hK hV η (LamDK.ofLam (asLam V N)) e
      have henc :
          t ≤ eqB (encodeLamDKB V K (LamDK.ofLam (asLam V N)))
            (encodeLamDKB V K (LamDK.ofLam (asLam V M))) := by
        rw [encodeLamDKB_ofLam_asLam, encodeLamDKB_ofLam_asLam, eqB_comm]
        exact (oid_eq_le_eqB_child _ M N).trans'
          (inf_le_left.trans inf_le_left)
      have hval :
          t ≤ interpDKRelVal 𝓜 V K hK hV η
            (LamDK.ofLam (asLam V N)) e := inf_le_right
      have hM :
          t ≤ interpDKRelVal 𝓜 V K hK hV η
            (LamDK.ofLam (asLam V M)) e :=
        (interpDKRelVal_encode_congr 𝓜 V K hK hV η
          (LamDK.ofLam (asLam V N)) (LamDK.ofLam (asLam V M)) e).trans'
          (le_inf henc hval)
      have hde : t ≤ (oid 𝓜.D).eq e d := by
        rw [(oid 𝓜.D).symm]
        exact inf_le_left.trans inf_le_right
      exact (interpDKRelVal_isRelElementAt 𝓜 V K hK hV η
          (LamDK.ofLam (asLam V M))).respects e d |>.trans'
        (le_inf hde hM)
  le_eps := by
    intro M d
    have h :=
      (interpDKRelVal_isRelElementAt 𝓜 V K hK hV η
        (LamDK.ofLam (asLam V M))).2.1 d
    rw [lamDKVal_ofLam V K hV (asLam V M), top_inf_eq] at h
    rw [oid_eps, oid_eps]
    refine le_inf ?_ ?_
    · have hmem : memB ((lamB V).child M) (lamB V) = ⊤ := by
        rw [← asLam_encode V M]
        exact memB_encodeLamB V (asLam V M)
      exact le_top.trans hmem.ge
    · rw [oid_eps] at h
      exact h
  single_valued := by
    intro M d e
    exact (interpDKRelVal_isRelElementAt 𝓜 V K hK hV η
      (LamDK.ofLam (asLam V M))).2.2.1 d e
  total := by
    intro M
    rw [oid_eps]
    have hmem : memB ((lamB V).child M) (lamB V) = ⊤ := by
      rw [← asLam_encode V M]
      exact memB_encodeLamB V (asLam V M)
    rw [hmem]
    have htot :=
      (interpDKRelVal_isRelElementAt 𝓜 V K hK hV η
        (LamDK.ofLam (asLam V M))).2.2.2
    rwa [lamDKVal_ofLam V K hV (asLam V M)] at htot

noncomputable def InternalReflexiveModel.interpDKPureGraph
    (𝓜 : InternalReflexiveModel (A := A))
    (V K : AName.{u} A) (hK : subsetB K 𝓜.D = ⊤)
    (hV : (oid V).IsTotal)
    (η : RelFun (oid V) (oid 𝓜.D)) :
    AName.{u} A :=
  relFunGraphName (lamB V) 𝓜.D (interpDKPureRel 𝓜 V K hK hV η)

theorem InternalReflexiveModel.interpDKPureGraph_eq_relFunGraphName
    (𝓜 : InternalReflexiveModel (A := A))
    (V K : AName.{u} A) (hK : subsetB K 𝓜.D = ⊤)
    (hV : (oid V).IsTotal)
    (η : RelFun (oid V) (oid 𝓜.D)) :
    interpDKPureGraph 𝓜 V K hK hV η =
      relFunGraphName (lamB V) 𝓜.D
        (interpDKPureRel 𝓜 V K hK hV η) :=
  rfl

theorem InternalReflexiveModel.interpDKPureGraph_isFunctionB
    (𝓜 : InternalReflexiveModel (A := A))
    (V K : AName.{u} A) (hK : subsetB K 𝓜.D = ⊤)
    (hV : (oid V).IsTotal)
    (η : RelFun (oid V) (oid 𝓜.D)) :
    isFunctionB (interpDKPureGraph 𝓜 V K hK hV η) (lamB V) 𝓜.D = ⊤ := by
  rw [interpDKPureGraph_eq_relFunGraphName]
  exact isFunctionB_relFunGraphName _ _ _

theorem InternalReflexiveModel.interpDKPureGraph_isFunctionB_of_valuation
    (𝓜 : InternalReflexiveModel (A := A))
    (V K : AName.{u} A) (hK : subsetB K 𝓜.D = ⊤)
    (hV : (oid V).IsTotal)
    (Dom Rho : AName.{u} A)
    (hVal : isValuationB V 𝓜.D Dom Rho = ⊤) :
    isFunctionB
      (interpDKPureGraph 𝓜 V K hK hV
        (totalizedValuationRelOfValid V 𝓜.D Dom Rho hVal
          𝓜.total 𝓜.complete))
      (lamB V) 𝓜.D = ⊤ :=
  interpDKPureGraph_isFunctionB 𝓜 V K hK hV _

/-!
## Definition 25 clauses at the term extent
-/

/-- Graph membership recovers the evaluation row at the term’s Boolean
extent. -/
theorem InternalReflexiveModel.interpDKGraph_eval
    (𝓜 : InternalReflexiveModel (A := A))
    (V K : AName.{u} A) (hK : subsetB K 𝓜.D = ⊤)
    (hV : (oid V).IsTotal)
    (η : RelFun (oid V) (oid 𝓜.D))
    (M : LamDK V.idx K.idx) (d : 𝓜.D.idx) :
    lamDKVal V K M ⊓
        memB (opairB (encodeLamDKB V K M) (𝓜.D.child d))
          (interpDKGraph 𝓜 V K hK hV η) =
      interpDKRelVal 𝓜 V K hK hV η M d := by
  apply le_antisymm
  · unfold interpDKGraph
    rw [memB_mk, inf_iSup_eq]
    refine iSup_le fun p => ?_
    rw [eqB_opairB]
    let t :=
      lamDKVal V K M ⊓
        ((eqB (encodeLamDKB V K M) (encodeLamDKB V K p.1) ⊓
            eqB (𝓜.D.child d) (𝓜.D.child p.2)) ⊓
          interpDKRelVal 𝓜 V K hK hV η p.1 p.2)
    change t ≤ interpDKRelVal 𝓜 V K hK hV η M d
    have henc : t ≤ eqB (encodeLamDKB V K p.1) (encodeLamDKB V K M) := by
      rw [eqB_comm]
      exact inf_le_right.trans (inf_le_left.trans inf_le_left)
    have hval : t ≤ interpDKRelVal 𝓜 V K hK hV η p.1 p.2 :=
      inf_le_right.trans inf_le_right
    have hM :
        t ≤ interpDKRelVal 𝓜 V K hK hV η M p.2 :=
      (interpDKRelVal_encode_congr 𝓜 V K hK hV η p.1 M p.2).trans'
        (le_inf henc hval)
    have hde : t ≤ (oid 𝓜.D).eq p.2 d := by
      rw [oid_eq_of_total 𝓜.D 𝓜.total, eqB_comm]
      exact inf_le_right.trans (inf_le_left.trans inf_le_right)
    exact (interpDKRelVal_isRelElementAt 𝓜 V K hK hV η M).respects p.2 d
      |>.trans' (le_inf hde hM)
  · have hsupp :
        interpDKRelVal 𝓜 V K hK hV η M d ≤ lamDKVal V K M :=
      ((interpDKRelVal_isRelElementAt 𝓜 V K hK hV η M).2.1 d).trans
        inf_le_left
    exact le_inf hsupp
      (val_le_memB (interpDKGraph 𝓜 V K hK hV η) (M, d))

/-- Definition 25, variable clause, at the term extent. -/
theorem InternalReflexiveModel.interpDKGraph_var
    (𝓜 : InternalReflexiveModel (A := A))
    (V K : AName.{u} A) (hK : subsetB K 𝓜.D = ⊤)
    (hV : (oid V).IsTotal)
    (η : RelFun (oid V) (oid 𝓜.D))
    (x : V.idx) (d : 𝓜.D.idx) :
    lamDKVal V K (.var x) ⊓
        memB (opairB (encodeLamDKB V K (.var x)) (𝓜.D.child d))
          (interpDKGraph 𝓜 V K hK hV η) =
      interpDKRelVal 𝓜 V K hK hV η (.var x) d :=
  interpDKGraph_eval 𝓜 V K hK hV η (.var x) d

theorem InternalReflexiveModel.interpDKGraph_var_val
    (𝓜 : InternalReflexiveModel (A := A))
    (V K : AName.{u} A) (hK : subsetB K 𝓜.D = ⊤)
    (hV : (oid V).IsTotal)
    (η : RelFun (oid V) (oid 𝓜.D))
    (x : V.idx) (d : 𝓜.D.idx) :
    lamDKVal V K (.var x) ⊓
        memB (opairB (encodeLamDKB V K (.var x)) (𝓜.D.child d))
          (interpDKGraph 𝓜 V K hK hV η) =
      η.val x d := by
  rw [interpDKGraph_var, interpDKRelVal_var]

/-- Definition 25, constant clause, at the term extent. -/
theorem InternalReflexiveModel.interpDKGraph_const
    (𝓜 : InternalReflexiveModel (A := A))
    (V K : AName.{u} A) (hK : subsetB K 𝓜.D = ⊤)
    (hV : (oid V).IsTotal)
    (η : RelFun (oid V) (oid 𝓜.D))
    (k : K.idx) (d : 𝓜.D.idx) :
    lamDKVal V K (.const k) ⊓
        memB (opairB (encodeLamDKB V K (.const k)) (𝓜.D.child d))
          (interpDKGraph 𝓜 V K hK hV η) =
      interpDKRelVal 𝓜 V K hK hV η (.const k) d :=
  interpDKGraph_eval 𝓜 V K hK hV η (.const k) d

theorem InternalReflexiveModel.interpDKGraph_const_val
    (𝓜 : InternalReflexiveModel (A := A))
    (V K : AName.{u} A) (hK : subsetB K 𝓜.D = ⊤)
    (hV : (oid V).IsTotal)
    (η : RelFun (oid V) (oid 𝓜.D))
    (k : K.idx) (d : 𝓜.D.idx) :
    lamDKVal V K (.const k) ⊓
        memB (opairB (encodeLamDKB V K (.const k)) (𝓜.D.child d))
          (interpDKGraph 𝓜 V K hK hV η) =
      (oidSubsetRel K 𝓜.D hK).val k d := by
  rw [interpDKGraph_const, interpDKRelVal_const]

/-- Definition 25, application clause, at the term extent. -/
theorem InternalReflexiveModel.interpDKGraph_app
    (𝓜 : InternalReflexiveModel (A := A))
    (V K : AName.{u} A) (hK : subsetB K 𝓜.D = ⊤)
    (hV : (oid V).IsTotal)
    (η : RelFun (oid V) (oid 𝓜.D))
    (P Q : LamDK V.idx K.idx) (d : 𝓜.D.idx) :
    lamDKVal V K (.app P Q) ⊓
        memB (opairB (encodeLamDKB V K (.app P Q)) (𝓜.D.child d))
          (interpDKGraph 𝓜 V K hK hV η) =
      interpDKRelVal 𝓜 V K hK hV η (.app P Q) d :=
  interpDKGraph_eval 𝓜 V K hK hV η (.app P Q) d

theorem InternalReflexiveModel.interpDKGraph_app_val
    (𝓜 : InternalReflexiveModel (A := A))
    (V K : AName.{u} A) (hK : subsetB K 𝓜.D = ⊤)
    (hV : (oid V).IsTotal)
    (η : RelFun (oid V) (oid 𝓜.D))
    (P Q : LamDK V.idx K.idx) (d : 𝓜.D.idx) :
    lamDKVal V K (.app P Q) ⊓
        memB (opairB (encodeLamDKB V K (.app P Q)) (𝓜.D.child d))
          (interpDKGraph 𝓜 V K hK hV η) =
      ⨆ c : 𝓜.C.idx, ⨆ q' : 𝓜.D.idx, ⨆ p : 𝓜.D.idx,
        ⨆ q : 𝓜.D.idx,
        interpDKRelVal 𝓜 V K hK hV η P p ⊓
          interpDKRelVal 𝓜 V K hK hV η Q q ⊓
          memB (opairB (𝓜.D.child p) (𝓜.C.child c)) 𝓜.Fun ⊓
          (oid 𝓜.D).eq q q' ⊓
          memB (𝓜.C.child c) 𝓜.C ⊓
          memB (opairB (𝓜.D.child q') (𝓜.D.child d))
            (𝓜.C.child c) := by
  rw [interpDKGraph_app, interpDKRelVal_app]

/-- Definition 25, abstraction clause, at the term extent. -/
theorem InternalReflexiveModel.interpDKGraph_abs
    (𝓜 : InternalReflexiveModel (A := A))
    (V K : AName.{u} A) (hK : subsetB K 𝓜.D = ⊤)
    (hV : (oid V).IsTotal)
    (η : RelFun (oid V) (oid 𝓜.D))
    (x : V.idx) (P : LamDK V.idx K.idx) (d : 𝓜.D.idx) :
    lamDKVal V K (.abs x P) ⊓
        memB (opairB (encodeLamDKB V K (.abs x P)) (𝓜.D.child d))
          (interpDKGraph 𝓜 V K hK hV η) =
      interpDKRelVal 𝓜 V K hK hV η (.abs x P) d :=
  interpDKGraph_eval 𝓜 V K hK hV η (.abs x P) d

theorem InternalReflexiveModel.interpDKGraph_abs_val
    (𝓜 : InternalReflexiveModel (A := A))
    (V K : AName.{u} A) (hK : subsetB K 𝓜.D = ⊤)
    (hV : (oid V).IsTotal)
    (η : RelFun (oid V) (oid 𝓜.D))
    (x : V.idx) (P : LamDK V.idx K.idx) (d : 𝓜.D.idx) :
    lamDKVal V K (.abs x P) ⊓
        memB (opairB (encodeLamDKB V K (.abs x P)) (𝓜.D.child d))
          (interpDKGraph 𝓜 V K hK hV η) =
      lamDKVal V K (.abs x P) ⊓
        memB (opairB (interpDKBodyGraph 𝓜 V K hK hV η x P)
          (𝓜.D.child d)) 𝓜.Lam := by
  rw [interpDKGraph_abs, interpDKRelVal_abs]

theorem asLam_cast (V : AName.{u} A) (M : Lam V.idx) :
    asLam V (cast (Eq.symm (by rw [lamB, idx_mk] : (lamB V).idx = Lam V.idx)) M) =
      M := by
  apply eq_of_heq
  unfold asLam
  exact (cast_heq _ _).trans (cast_heq _ _)

/-- Pure-graph counterpart of `interpDKGraph_eval`. -/
theorem interpDKPureGraph_eval
    (𝓜 : InternalReflexiveModel (A := A))
    (V K : AName.{u} A) (hK : subsetB K 𝓜.D = ⊤)
    (hV : (oid V).IsTotal)
    (η : RelFun (oid V) (oid 𝓜.D))
    (M : Lam V.idx) (d : 𝓜.D.idx) :
    memB (opairB (encodeLamB V M) (𝓜.D.child d))
        (InternalReflexiveModel.interpDKPureGraph 𝓜 V K hK hV η) =
      interpDKRelVal 𝓜 V K hK hV η (LamDK.ofLam M) d := by
  let i : (lamB V).idx :=
    cast (Eq.symm (by rw [lamB, idx_mk] : (lamB V).idx = Lam V.idx)) M
  have hchild : (lamB V).child i = encodeLamB V M := by
    rw [← asLam_encode, asLam_cast]
  rw [InternalReflexiveModel.interpDKPureGraph, ← hchild,
    memB_opairB_relFunGraphName]
  change interpDKRelVal 𝓜 V K hK hV η (LamDK.ofLam (asLam V i)) d =
    interpDKRelVal 𝓜 V K hK hV η (LamDK.ofLam M) d
  rw [asLam_cast]

/-!
## Pure-term names and internal `LamEq` soundness
-/

/-- Distinct source keys are Boolean-unequal. This is the discreteness of a
crisp variable set, needed so environment update matches `Lam.substCA`. -/
def OidSeparated (V : AName.{u} A) : Prop :=
  ∀ i j : V.idx, i ≠ j → (oid V).eq i j = ⊥

theorem RelFun.update_of_ne
    {X Y : Type*} {S : ASetoid (A := A) X} {T : ASetoid (A := A) Y}
    (f : RelFun S T) (hS : S.IsTotal) (hT : T.IsTotal)
    (x i : X) (d j : Y) (hne : S.eq i x = ⊥) :
    (f.update hS hT x d).val i j = f.val i j := by
  rw [RelFun.update_val, hne, bot_inf_eq, bot_sup_eq, compl_bot, top_inf_eq]

theorem RelFun.update_overwrite
    {X Y : Type*} {S : ASetoid (A := A) X} {T : ASetoid (A := A) Y}
    (f : RelFun S T) (hS : S.IsTotal) (hT : T.IsTotal)
    (x : X) (d z : Y) :
    (f.update hS hT x d).update hS hT x z = f.update hS hT x z := by
  apply RelFun.ext
  intro i j
  have hxx : S.eq x x = ⊤ := hS x
  apply le_antisymm
  · simpa only [hxx, top_inf_eq] using
      RelFun.update_overwrite_val f hS hT x x d z i j
  · simpa only [hxx, top_inf_eq] using
      RelFun.update_overwrite_val_symm f hS hT x x d z i j

theorem RelFun.update_commute
    {X Y : Type*} {S : ASetoid (A := A) X} {T : ASetoid (A := A) Y}
    (f : RelFun S T) (hS : S.IsTotal) (hT : T.IsTotal)
    (x y : X) (d z : Y) (hne : S.eq x y = ⊥) :
    (f.update hS hT y d).update hS hT x z =
      (f.update hS hT x z).update hS hT y d := by
  apply RelFun.ext
  intro i j
  apply le_antisymm
  · simpa only [hne, compl_bot, top_inf_eq] using
      RelFun.update_commute_val f hS hT x y d z i j
  · simpa only [hne, compl_bot, top_inf_eq] using
      RelFun.update_commute_val_symm f hS hT x y d z i j

/-- Mix a Definition 25 row to a `D`-index via completeness. -/
noncomputable def InternalReflexiveModel.interpDKName
    (𝓜 : InternalReflexiveModel (A := A))
    (V K : AName.{u} A) (hK : subsetB K 𝓜.D = ⊤)
    (hV : (oid V).IsTotal)
    (η : RelFun (oid V) (oid 𝓜.D))
    (M : LamDK V.idx K.idx) : 𝓜.D.idx :=
  functionalOfRel 𝓜.complete
    (relFunOfIsRelElementAt
      (interpDKRelVal_isRelElementAt 𝓜 V K hK hV η M))
    PUnit.unit

theorem InternalReflexiveModel.interpDKRelVal_eq_oid
    (𝓜 : InternalReflexiveModel (A := A))
    (V K : AName.{u} A) (hK : subsetB K 𝓜.D = ⊤)
    (hV : (oid V).IsTotal)
    (η : RelFun (oid V) (oid 𝓜.D))
    (M : LamDK V.idx K.idx)
    (hval : lamDKVal V K M = ⊤) (d : 𝓜.D.idx) :
    interpDKRelVal 𝓜 V K hK hV η M d =
      (oid 𝓜.D).eq (interpDKName 𝓜 V K hK hV η M) d := by
  have hgamma :=
    functionalOfRel_gamma 𝓜.complete
      (relFunOfIsRelElementAt
        (interpDKRelVal_isRelElementAt 𝓜 V K hK hV η M))
      PUnit.unit d
  simp only [gamma, relFunOfIsRelElementAt_val, extentSetoid_eps] at hgamma
  have heq :
      lamDKVal V K M ⊓
          (oid 𝓜.D).eq (interpDKName 𝓜 V K hK hV η M) d =
        (oid 𝓜.D).eq (interpDKName 𝓜 V K hK hV η M) d := by
    rw [hval, top_inf_eq]
  exact hgamma.symm.trans heq

theorem interpDKRelVal_ofLam_eq_oid
    (𝓜 : InternalReflexiveModel (A := A))
    (V K : AName.{u} A) (hK : subsetB K 𝓜.D = ⊤)
    (hV : (oid V).IsTotal)
    (η : RelFun (oid V) (oid 𝓜.D))
    (M : Lam V.idx) (d : 𝓜.D.idx) :
    interpDKRelVal 𝓜 V K hK hV η (LamDK.ofLam M) d =
      (oid 𝓜.D).eq
        (InternalReflexiveModel.interpDKName 𝓜 V K hK hV η
          (LamDK.ofLam M)) d :=
  InternalReflexiveModel.interpDKRelVal_eq_oid 𝓜 V K hK hV η
    (LamDK.ofLam M) (lamDKVal_ofLam V K hV M) d

theorem InternalReflexiveModel.interpDKName_spec
    (𝓜 : InternalReflexiveModel (A := A))
    (V K : AName.{u} A) (hK : subsetB K 𝓜.D = ⊤)
    (hV : (oid V).IsTotal)
    (η : RelFun (oid V) (oid 𝓜.D))
    (M : LamDK V.idx K.idx)
    (hval : lamDKVal V K M = ⊤) :
    interpDKRelVal 𝓜 V K hK hV η M (interpDKName 𝓜 V K hK hV η M) = ⊤ := by
  rw [InternalReflexiveModel.interpDKRelVal_eq_oid 𝓜 V K hK hV η M hval]
  exact 𝓜.total _

open InternalReflexiveModel
  (interpDKName interpDKPureGraph interpDKRelVal_eq_oid interpDKName_spec
    interpDKGraph)

theorem interpDKBodyGraph_eq_of
    (𝓜 : InternalReflexiveModel (A := A))
    (V K : AName.{u} A) (hK : subsetB K 𝓜.D = ⊤)
    (hV : (oid V).IsTotal)
    (η₁ η₂ : RelFun (oid V) (oid 𝓜.D))
    (x y : V.idx) (P Q : LamDK V.idx K.idx)
    (h : ∀ d e, interpDKRelVal 𝓜 V K hK hV (η₁.update hV 𝓜.total x d) P e =
      interpDKRelVal 𝓜 V K hK hV (η₂.update hV 𝓜.total y d) Q e) :
    interpDKBodyGraph 𝓜 V K hK hV η₁ x P =
      interpDKBodyGraph 𝓜 V K hK hV η₂ y Q := by
  refine congr_arg
      (AName.mk (𝓜.D.idx × 𝓜.D.idx)
        (fun p => opairB (𝓜.D.child p.1) (𝓜.D.child p.2))) ?_
  exact funext fun p => h p.1 p.2

/-- Environment update is invisible to a term that does not mention the key. -/
theorem interpDKRelVal_update_fresh
    (𝓜 : InternalReflexiveModel (A := A))
    (V K : AName.{u} A) (hK : subsetB K 𝓜.D = ⊤)
    (hV : (oid V).IsTotal)
    (hVsep : OidSeparated V)
    [DecidableEq V.idx]
    (η : RelFun (oid V) (oid 𝓜.D))
    (M : Lam V.idx) (x : V.idx) (hx : x ∉ M.fv)
    (d e : 𝓜.D.idx) :
    interpDKRelVal 𝓜 V K hK hV (η.update hV 𝓜.total x d)
        (LamDK.ofLam M) e =
      interpDKRelVal 𝓜 V K hK hV η (LamDK.ofLam M) e := by
  induction M generalizing η d e with
  | var y =>
    have hyx : y ≠ x := by
      intro h
      subst h
      exact hx (by simp [Lam.fv])
    simp only [LamDK.ofLam, interpDKRelVal_var]
    rw [RelFun.update_of_ne (hne := hVsep y x hyx)]
  | app P Q ihP ihQ =>
    have hP : x ∉ P.fv := fun h =>
      hx (Finset.mem_union.mpr (Or.inl h))
    have hQ : x ∉ Q.fv := fun h =>
      hx (Finset.mem_union.mpr (Or.inr h))
    simp only [LamDK.ofLam, interpDKRelVal_app]
    refine iSup_congr fun c => iSup_congr fun q' =>
      iSup_congr fun p => iSup_congr fun q => ?_
    rw [ihP η hP d p, ihQ η hQ d q]
  | abs y P ih =>
    simp only [LamDK.ofLam, interpDKRelVal_abs]
    have hval : lamDKVal V K (LamDK.ofLam (Lam.abs y P)) = ⊤ :=
      lamDKVal_ofLam V K hV (Lam.abs y P)
    simp only [LamDK.ofLam] at hval
    simp only [hval, top_inf_eq]
    apply congr_arg (fun G => memB (opairB G (𝓜.D.child e)) 𝓜.Lam)
    apply interpDKBodyGraph_eq_of
    intro q e'
    by_cases hyx : y = x
    · subst hyx
      rw [RelFun.update_overwrite]
    · have hxP : x ∉ P.fv := by
        intro h
        exact hx (by
          simp only [Lam.fv, Finset.mem_sdiff, Finset.mem_singleton]
          exact ⟨h, Ne.symm hyx⟩)
      rw [RelFun.update_commute η hV 𝓜.total y x d q (hVsep y x hyx)]
      exact ih (η.update hV 𝓜.total y q) hxP d e'

theorem RelFun.update_eq_of_target
    {X Y : Type*} {S : ASetoid (A := A) X} {T : ASetoid (A := A) Y}
    (f : RelFun S T) (hS : S.IsTotal) (hT : T.IsTotal)
    (x : X) (d₁ d₂ : Y) (hd : T.eq d₁ d₂ = ⊤) :
    f.update hS hT x d₁ = f.update hS hT x d₂ :=
  RelFun.update_congr f f hS hT x d₁ d₂ (fun _ _ => rfl) hd

theorem InternalReflexiveModel.interpDKName_oid_eq_of_relVal
    (𝓜 : InternalReflexiveModel (A := A))
    (V K : AName.{u} A) (hK : subsetB K 𝓜.D = ⊤)
    (hV : (oid V).IsTotal)
    (η : RelFun (oid V) (oid 𝓜.D))
    (M : LamDK V.idx K.idx)
    (hval : lamDKVal V K M = ⊤)
    (d : 𝓜.D.idx)
    (h : ∀ e, interpDKRelVal 𝓜 V K hK hV η M e = (oid 𝓜.D).eq d e) :
    (oid 𝓜.D).eq (interpDKName 𝓜 V K hK hV η M) d = ⊤ := by
  rw [← InternalReflexiveModel.interpDKRelVal_eq_oid 𝓜 V K hK hV η M hval, h]
  exact 𝓜.total d

theorem interpDKName_oid_eq_of_fresh
    (𝓜 : InternalReflexiveModel (A := A))
    (V K : AName.{u} A) (hK : subsetB K 𝓜.D = ⊤)
    (hV : (oid V).IsTotal)
    (hVsep : OidSeparated V)
    [DecidableEq V.idx]
    (η : RelFun (oid V) (oid 𝓜.D))
    (M : Lam V.idx) (x : V.idx) (hx : x ∉ M.fv) (d : 𝓜.D.idx) :
    (oid 𝓜.D).eq
        (interpDKName 𝓜 V K hK hV (η.update hV 𝓜.total x d)
          (LamDK.ofLam M))
        (interpDKName 𝓜 V K hK hV η (LamDK.ofLam M)) = ⊤ := by
  rw [← interpDKRelVal_ofLam_eq_oid 𝓜 V K hK hV
      (η.update hV 𝓜.total x d) M
      (interpDKName 𝓜 V K hK hV η (LamDK.ofLam M))]
  rw [interpDKRelVal_update_fresh 𝓜 V K hK hV hVsep η M x hx d]
  exact interpDKName_spec 𝓜 V K hK hV η (LamDK.ofLam M)
    (lamDKVal_ofLam V K hV M)

/-- Capture-free substitution: `⟦M[x := N]⟧_η = ⟦M⟧_{η[x := ⟦N⟧]}` when
`N` is free for `x` in `M`. -/
theorem interpDKRelVal_substNaive
    (𝓜 : InternalReflexiveModel (A := A))
    (V K : AName.{u} A) (hK : subsetB K 𝓜.D = ⊤)
    (hV : (oid V).IsTotal)
    (hVsep : OidSeparated V)
    [DecidableEq V.idx]
    (η : RelFun (oid V) (oid 𝓜.D))
    (M N : Lam V.idx) (x : V.idx)
    (hfree : M.FreeFor x N) (d : 𝓜.D.idx) :
    interpDKRelVal 𝓜 V K hK hV η
        (LamDK.ofLam (M.substNaive x N)) d =
      interpDKRelVal 𝓜 V K hK hV
        (η.update hV 𝓜.total x
          (interpDKName 𝓜 V K hK hV η (LamDK.ofLam N)))
        (LamDK.ofLam M) d := by
  induction M generalizing η d with
  | var y =>
    simp only [Lam.substNaive]
    by_cases hyx : y = x
    · subst hyx
      simp only [LamDK.ofLam, interpDKRelVal_var, RelFun.update_self]
      exact interpDKRelVal_ofLam_eq_oid 𝓜 V K hK hV η N d
    · rw [if_neg hyx]
      simp only [LamDK.ofLam, interpDKRelVal_var]
      rw [RelFun.update_of_ne (hne := hVsep y x hyx)]
  | app M₁ M₂ ih₁ ih₂ =>
    obtain ⟨h₁, h₂⟩ := hfree
    simp only [Lam.substNaive, LamDK.ofLam, interpDKRelVal_app]
    refine iSup_congr fun c => iSup_congr fun q' =>
      iSup_congr fun p => iSup_congr fun q => ?_
    rw [ih₁ η h₁ p, ih₂ η h₂ q]
  | abs y P ih =>
    simp only [Lam.substNaive]
    split_ifs with hyx
    · simp only [LamDK.ofLam, interpDKRelVal_abs]
      have hval : lamDKVal V K (LamDK.ofLam (Lam.abs y P)) = ⊤ :=
        lamDKVal_ofLam V K hV (Lam.abs y P)
      simp only [LamDK.ofLam] at hval
      simp only [hval, top_inf_eq]
      apply congr_arg (fun G => memB (opairB G (𝓜.D.child d)) 𝓜.Lam)
      apply interpDKBodyGraph_eq_of
      intro q e
      cases hyx
      rw [RelFun.update_overwrite]
    · obtain ⟨hP, hcap⟩ := Lam.freeFor_abs_of_ne hyx hfree
      simp only [LamDK.ofLam, interpDKRelVal_abs]
      have hvalL : lamDKVal V K (LamDK.ofLam (Lam.abs y (P.substNaive x N))) = ⊤ :=
        lamDKVal_ofLam V K hV (Lam.abs y (P.substNaive x N))
      have hvalR : lamDKVal V K (LamDK.ofLam (Lam.abs y P)) = ⊤ :=
        lamDKVal_ofLam V K hV (Lam.abs y P)
      simp only [LamDK.ofLam] at hvalL hvalR
      simp only [hvalL, hvalR, top_inf_eq]
      apply congr_arg (fun G => memB (opairB G (𝓜.D.child d)) 𝓜.Lam)
      apply interpDKBodyGraph_eq_of
      intro q e
      have hcomm :
          (η.update hV 𝓜.total x
              (interpDKName 𝓜 V K hK hV η (LamDK.ofLam N))).update
            hV 𝓜.total y q =
          (η.update hV 𝓜.total y q).update hV 𝓜.total x
            (interpDKName 𝓜 V K hK hV η (LamDK.ofLam N)) :=
        RelFun.update_commute η hV 𝓜.total y x
          (interpDKName 𝓜 V K hK hV η (LamDK.ofLam N)) q
          (hVsep y x hyx)
      cases hcap with
      | inl hyN =>
        have hname :
            (oid 𝓜.D).eq
              (interpDKName 𝓜 V K hK hV
                (η.update hV 𝓜.total y q) (LamDK.ofLam N))
              (interpDKName 𝓜 V K hK hV η (LamDK.ofLam N)) = ⊤ :=
          interpDKName_oid_eq_of_fresh 𝓜 V K hK hV hVsep η N y hyN q
        have hupd :=
          RelFun.update_eq_of_target (η.update hV 𝓜.total y q)
            hV 𝓜.total x
            (interpDKName 𝓜 V K hK hV
              (η.update hV 𝓜.total y q) (LamDK.ofLam N))
            (interpDKName 𝓜 V K hK hV η (LamDK.ofLam N)) hname
        rw [hcomm, ← hupd]
        exact ih (η.update hV 𝓜.total y q) hP e
      | inr hxP =>
        have hsf : P.substNaive x N = P := Lam.subst_fresh N hxP
        rw [hsf, hcomm]
        exact (interpDKRelVal_update_fresh 𝓜 V K hK hV hVsep
          (η.update hV 𝓜.total y q) P x hxP
          (interpDKName 𝓜 V K hK hV η (LamDK.ofLam N)) e).symm

/-- Internal substitution lemma: `⟦M[x := N]⟧_η = ⟦M⟧_{η[x := ⟦N⟧]}`. -/
theorem interpDKRelVal_substCA
    (𝓜 : InternalReflexiveModel (A := A))
    (V K : AName.{u} A) (hK : subsetB K 𝓜.D = ⊤)
    (hV : (oid V).IsTotal)
    (hVsep : OidSeparated V)
    [DecidableEq V.idx] [Infinite V.idx]
    (η : RelFun (oid V) (oid 𝓜.D))
    (M N : Lam V.idx) (x : V.idx) (d : 𝓜.D.idx) :
    interpDKRelVal 𝓜 V K hK hV η
        (LamDK.ofLam (Lam.substCA M x N)) d =
      interpDKRelVal 𝓜 V K hK hV
        (η.update hV 𝓜.total x
          (interpDKName 𝓜 V K hK hV η (LamDK.ofLam N)))
        (LamDK.ofLam M) d := by
  induction hsize : M.size using Nat.strong_induction_on
    generalizing M N x η d with
  | h k ih =>
    match M with
    | .var y =>
      rw [Lam.substCA_var]
      by_cases hyx : y = x
      · subst hyx
        simp only [LamDK.ofLam, interpDKRelVal_var, RelFun.update_self]
        exact interpDKRelVal_ofLam_eq_oid 𝓜 V K hK hV η N d
      · rw [if_neg hyx]
        simp only [LamDK.ofLam, interpDKRelVal_var]
        rw [RelFun.update_of_ne (hne := hVsep y x hyx)]
    | .app M₁ M₂ =>
      have h₁ : M₁.size < k := by
        simp [Lam.size] at hsize; omega
      have h₂ : M₂.size < k := by
        simp [Lam.size] at hsize; omega
      simp only [Lam.substCA_app, LamDK.ofLam, interpDKRelVal_app]
      refine iSup_congr fun c => iSup_congr fun q' =>
        iSup_congr fun p => iSup_congr fun q => ?_
      rw [ih M₁.size h₁ η M₁ N x p rfl, ih M₂.size h₂ η M₂ N x q rfl]
    | .abs y P =>
      rw [Lam.substCA_abs]
      by_cases hyx : y = x
      · rw [if_pos hyx]
        simp only [LamDK.ofLam, interpDKRelVal_abs]
        have hval : lamDKVal V K (LamDK.ofLam (Lam.abs y P)) = ⊤ :=
          lamDKVal_ofLam V K hV (Lam.abs y P)
        simp only [LamDK.ofLam] at hval
        simp only [hval, top_inf_eq]
        apply congr_arg (fun G => memB (opairB G (𝓜.D.child d)) 𝓜.Lam)
        apply interpDKBodyGraph_eq_of
        intro q e
        cases hyx
        rw [RelFun.update_overwrite]
      · rw [if_neg hyx]
        by_cases hxP : x ∉ P.fv
        · rw [if_pos hxP]
          simp only [LamDK.ofLam, interpDKRelVal_abs]
          have hvalL : lamDKVal V K (LamDK.ofLam (Lam.abs y P)) = ⊤ :=
            lamDKVal_ofLam V K hV (Lam.abs y P)
          simp only [LamDK.ofLam] at hvalL
          simp only [hvalL, top_inf_eq]
          apply congr_arg (fun G => memB (opairB G (𝓜.D.child d)) 𝓜.Lam)
          apply interpDKBodyGraph_eq_of
          intro q e
          have hcomm :
              (η.update hV 𝓜.total x
                  (interpDKName 𝓜 V K hK hV η (LamDK.ofLam N))).update
                hV 𝓜.total y q =
              (η.update hV 𝓜.total y q).update hV 𝓜.total x
                (interpDKName 𝓜 V K hK hV η (LamDK.ofLam N)) :=
            RelFun.update_commute η hV 𝓜.total y x
              (interpDKName 𝓜 V K hK hV η (LamDK.ofLam N)) q
              (hVsep y x hyx)
          rw [hcomm]
          exact (interpDKRelVal_update_fresh 𝓜 V K hK hV hVsep
            (η.update hV 𝓜.total y q) P x hxP
            (interpDKName 𝓜 V K hK hV η (LamDK.ofLam N)) e).symm
        · rw [if_neg hxP]
          by_cases hyN : y ∉ N.fv
          · rw [if_pos hyN]
            simp only [LamDK.ofLam, interpDKRelVal_abs]
            have hvalL :
                lamDKVal V K (LamDK.ofLam (Lam.abs y (P.substCA x N))) = ⊤ :=
              lamDKVal_ofLam V K hV (Lam.abs y (P.substCA x N))
            have hvalR : lamDKVal V K (LamDK.ofLam (Lam.abs y P)) = ⊤ :=
              lamDKVal_ofLam V K hV (Lam.abs y P)
            simp only [LamDK.ofLam] at hvalL hvalR
            simp only [hvalL, hvalR, top_inf_eq]
            apply congr_arg (fun G => memB (opairB G (𝓜.D.child d)) 𝓜.Lam)
            apply interpDKBodyGraph_eq_of
            intro q e
            have hMs : P.size < k := by
              simp [Lam.size] at hsize; omega
            rw [ih P.size hMs (η.update hV 𝓜.total y q) P N x e rfl]
            have hname :
                (oid 𝓜.D).eq
                  (interpDKName 𝓜 V K hK hV
                    (η.update hV 𝓜.total y q) (LamDK.ofLam N))
                  (interpDKName 𝓜 V K hK hV η (LamDK.ofLam N)) = ⊤ :=
              interpDKName_oid_eq_of_fresh 𝓜 V K hK hV hVsep η N y hyN q
            have hupd :=
              RelFun.update_eq_of_target (η.update hV 𝓜.total y q)
                hV 𝓜.total x
                (interpDKName 𝓜 V K hK hV
                  (η.update hV 𝓜.total y q) (LamDK.ofLam N))
                (interpDKName 𝓜 V K hK hV η (LamDK.ofLam N)) hname
            rw [hupd, RelFun.update_commute η hV 𝓜.total x y q
              (interpDKName 𝓜 V K hK hV η (LamDK.ofLam N))
              (hVsep x y (Ne.symm hyx))]
          · rw [if_neg hyN]
            set z := Lam.pickFresh (P.vars ∪ N.fv ∪ {x, y}) y
            have hz : z ∉ P.vars ∪ N.fv ∪ {x, y} :=
              Lam.pickFresh_not_mem _ y
            have hzP : z ∉ P.vars := fun h =>
              hz (Finset.mem_union.mpr (Or.inl
                (Finset.mem_union.mpr (Or.inl h))))
            have hzN : z ∉ N.fv := fun h =>
              hz (Finset.mem_union.mpr (Or.inl
                (Finset.mem_union.mpr (Or.inr h))))
            have hzx : z ≠ x := fun h => hz (by simp [h])
            have hzy : z ≠ y := fun h => hz (by simp [h])
            have hMs : P.size < k := by
              simp [Lam.size] at hsize; omega
            have hren : (P.substNaive y (Lam.var z)).size = P.size :=
              Lam.size_substNaive_var P y z
            simp only [LamDK.ofLam, interpDKRelVal_abs]
            have hvalL :
                lamDKVal V K
                  (LamDK.ofLam
                    (Lam.abs z ((P.substNaive y (Lam.var z)).substCA x N))) =
                  ⊤ :=
              lamDKVal_ofLam V K hV
                (Lam.abs z ((P.substNaive y (Lam.var z)).substCA x N))
            have hvalR : lamDKVal V K (LamDK.ofLam (Lam.abs y P)) = ⊤ :=
              lamDKVal_ofLam V K hV (Lam.abs y P)
            simp only [LamDK.ofLam] at hvalL hvalR
            simp only [hvalL, hvalR, top_inf_eq]
            apply congr_arg (fun G => memB (opairB G (𝓜.D.child d)) 𝓜.Lam)
            apply interpDKBodyGraph_eq_of
            intro q e
            rw [ih P.size hMs (η.update hV 𝓜.total z q)
              (P.substNaive y (Lam.var z)) N x e hren]
            have hname :
                (oid 𝓜.D).eq
                  (interpDKName 𝓜 V K hK hV
                    (η.update hV 𝓜.total z q) (LamDK.ofLam N))
                  (interpDKName 𝓜 V K hK hV η (LamDK.ofLam N)) = ⊤ :=
              interpDKName_oid_eq_of_fresh 𝓜 V K hK hV hVsep η N z hzN q
            have hupd :=
              RelFun.update_eq_of_target (η.update hV 𝓜.total z q)
                hV 𝓜.total x
                (interpDKName 𝓜 V K hK hV
                  (η.update hV 𝓜.total z q) (LamDK.ofLam N))
                (interpDKName 𝓜 V K hK hV η (LamDK.ofLam N)) hname
            rw [hupd, RelFun.update_commute η hV 𝓜.total x z q
              (interpDKName 𝓜 V K hK hV η (LamDK.ofLam N))
              (hVsep x z (Ne.symm hzx))]
            have hfree : P.FreeFor y (Lam.var z) :=
              Lam.freeFor_of_not_mem_vars y hzP
            have hsub :=
              interpDKRelVal_substNaive 𝓜 V K hK hV hVsep
                ((η.update hV 𝓜.total x
                    (interpDKName 𝓜 V K hK hV η (LamDK.ofLam N))).update
                  hV 𝓜.total z q)
                P (Lam.var z) y hfree e
            have hzoid :
                (oid 𝓜.D).eq
                  (interpDKName 𝓜 V K hK hV
                    ((η.update hV 𝓜.total x
                        (interpDKName 𝓜 V K hK hV η
                          (LamDK.ofLam N))).update hV 𝓜.total z q)
                    (LamDK.ofLam (Lam.var z)))
                  q = ⊤ := by
              rw [← interpDKRelVal_ofLam_eq_oid]
              simp only [LamDK.ofLam, interpDKRelVal_var, RelFun.update_self]
              exact 𝓜.total q
            have hup :=
              RelFun.update_eq_of_target
                ((η.update hV 𝓜.total x
                    (interpDKName 𝓜 V K hK hV η
                      (LamDK.ofLam N))).update hV 𝓜.total z q)
                hV 𝓜.total y
                (interpDKName 𝓜 V K hK hV
                  ((η.update hV 𝓜.total x
                      (interpDKName 𝓜 V K hK hV η
                        (LamDK.ofLam N))).update hV 𝓜.total z q)
                  (LamDK.ofLam (Lam.var z)))
                q hzoid
            rw [hsub, hup]
            have hzPf : z ∉ P.fv := fun h => hzP (Lam.fv_subset_vars P h)
            rw [RelFun.update_commute
              (η.update hV 𝓜.total x
                (interpDKName 𝓜 V K hK hV η (LamDK.ofLam N)))
              hV 𝓜.total y z q q (hVsep y z (Ne.symm hzy))]
            exact interpDKRelVal_update_fresh 𝓜 V K hK hV hVsep
              ((η.update hV 𝓜.total x
                  (interpDKName 𝓜 V K hK hV η (LamDK.ofLam N))).update
                hV 𝓜.total y q)
              P z hzPf q e

/-!
## Body graphs of pure terms, and `LamEq` soundness
-/

theorem interpDKBodyGraph_ofLam_mem_C
    (𝓜 : InternalReflexiveModel (A := A))
    (V K : AName.{u} A) (hK : subsetB K 𝓜.D = ⊤)
    (hV : (oid V).IsTotal)
    (η : RelFun (oid V) (oid 𝓜.D))
    (x : V.idx) (M : Lam V.idx) :
    memB (interpDKBodyGraph 𝓜 V K hK hV η x (LamDK.ofLam M)) 𝓜.C = ⊤ := by
  apply top_unique
  have hsc :=
    interpDKBodyGraph_le_scottContinuous 𝓜 V K hK hV η x (LamDK.ofLam M)
  rw [lamDKVal_ofLam V K hV M] at hsc
  exact hsc.trans (𝓜.scottContinuous_le_mem_mapSpace _)

theorem memB_interpDKBodyGraph_ofLam
    (𝓜 : InternalReflexiveModel (A := A))
    (V K : AName.{u} A) (hK : subsetB K 𝓜.D = ⊤)
    (hV : (oid V).IsTotal)
    (η : RelFun (oid V) (oid 𝓜.D))
    (x : V.idx) (M : Lam V.idx) (q d : 𝓜.D.idx) :
    memB (opairB (𝓜.D.child q) (𝓜.D.child d))
        (interpDKBodyGraph 𝓜 V K hK hV η x (LamDK.ofLam M)) =
      interpDKRelVal 𝓜 V K hK hV
        (η.update hV 𝓜.total x q) (LamDK.ofLam M) d := by
  have hP : ∀ z, IsRelElementAt 𝓜.D ⊤
      (interpDKRelVal 𝓜 V K hK hV
        (η.update hV 𝓜.total x z) (LamDK.ofLam M)) := by
    intro z
    simpa [lamDKVal_ofLam V K hV M] using
      interpDKRelVal_isRelElementAt 𝓜 V K hK hV
        (η.update hV 𝓜.total x z) (LamDK.ofLam M)
  simpa using
    inf_memB_interpDKBodyGraph_eq 𝓜 V K hK hV η x
      (LamDK.ofLam M) ⊤ hP q d

theorem InternalReflexiveModel.fun_total_child
    (𝓜 : InternalReflexiveModel (A := A)) (p : 𝓜.D.idx) :
    (⨆ c : 𝓜.C.idx,
        memB (opairB (𝓜.D.child p) (𝓜.C.child c)) 𝓜.Fun) = ⊤ := by
  apply top_unique
  have htot := isTotalB_apply 𝓜.Fun 𝓜.D (𝓜.D.child p)
  have hp : memB (𝓜.D.child p) 𝓜.D = ⊤ := by
    rw [← oid_eps]
    exact 𝓜.total p
  have hjoin : ⨆ y : AName A, memB (opairB (𝓜.D.child p) y) 𝓜.Fun = ⊤ := by
    apply top_unique
    exact htot.trans' (le_inf
      (le_top.trans (isFunctionB_total 𝓜.fun_function).ge) (le_top.trans hp.ge))
  have hsub : subsetB 𝓜.Fun (prodB 𝓜.D 𝓜.C) = ⊤ :=
    isFunctionB_subset 𝓜.fun_function
  refine (le_top.trans hjoin.ge).trans ?_
  refine iSup_le fun y =>
    memB_opairB_le_iSup_child hsub (𝓜.D.child p) y

theorem InternalReflexiveModel.lam_total_child
    (𝓜 : InternalReflexiveModel (A := A)) (F : AName.{u} A)
    (hF : memB F 𝓜.C = ⊤) :
    (⨆ p : 𝓜.D.idx, memB (opairB F (𝓜.D.child p)) 𝓜.Lam) = ⊤ := by
  apply top_unique
  have htot := isTotalB_apply 𝓜.Lam 𝓜.C F
  have hjoin : ⨆ y : AName A, memB (opairB F y) 𝓜.Lam = ⊤ := by
    apply top_unique
    exact htot.trans' (le_inf
      (le_top.trans (isFunctionB_total 𝓜.lam_function).ge) (le_top.trans hF.ge))
  have hsub : subsetB 𝓜.Lam (prodB 𝓜.C 𝓜.D) = ⊤ :=
    isFunctionB_subset 𝓜.lam_function
  refine (le_top.trans hjoin.ge).trans ?_
  refine iSup_le fun y =>
    memB_opairB_le_iSup_child hsub F y

/-- Retract `Fun ∘ Lam = id` on a body graph that lands in `C`. -/
theorem InternalReflexiveModel.retract_body_eq
    (𝓜 : InternalReflexiveModel (A := A))
    (body : AName.{u} A) (c : 𝓜.C.idx)
    (hC : memB body 𝓜.C = ⊤) :
    (⨆ p : 𝓜.D.idx,
        memB (opairB body (𝓜.D.child p)) 𝓜.Lam ⊓
          memB (opairB (𝓜.D.child p) (𝓜.C.child c)) 𝓜.Fun) =
      eqB body (𝓜.C.child c) := by
  have hsubLam : subsetB 𝓜.Lam (prodB 𝓜.C 𝓜.D) = ⊤ :=
    isFunctionB_subset 𝓜.lam_function
  have hsubFun : subsetB 𝓜.Fun (prodB 𝓜.D 𝓜.C) = ⊤ :=
    isFunctionB_subset 𝓜.fun_function
  have hcomp :
      memB (opairB body (𝓜.C.child c)) (compB 𝓜.Fun 𝓜.Lam 𝓜.C 𝓜.C) =
        ⨆ p : 𝓜.D.idx,
          memB (opairB body (𝓜.D.child p)) 𝓜.Lam ⊓
            memB (opairB (𝓜.D.child p) (𝓜.C.child c)) 𝓜.Fun :=
    memB_opairB_compB hsubLam hsubFun body (𝓜.C.child c)
  have hid :
      memB (opairB body (𝓜.C.child c)) (compB 𝓜.Fun 𝓜.Lam 𝓜.C 𝓜.C) =
        memB (opairB body (𝓜.C.child c)) (idB 𝓜.C) :=
    eqB_top_memB_right 𝓜.retract_valid
  rw [← hcomp, hid, memB_opairB_idB, hC, top_inf_eq]

/-- Capture-avoiding β: `⟦(λx. M) N⟧_η = ⟦M[x := N]⟧_η`. -/
theorem interpDKRelVal_sound_beta
    (𝓜 : InternalReflexiveModel (A := A))
    (V K : AName.{u} A) (hK : subsetB K 𝓜.D = ⊤)
    (hV : (oid V).IsTotal)
    (hVsep : OidSeparated V)
    [DecidableEq V.idx] [Infinite V.idx]
    (η : RelFun (oid V) (oid 𝓜.D))
    (x : V.idx) (M N : Lam V.idx) (d : 𝓜.D.idx) :
    interpDKRelVal 𝓜 V K hK hV η
        (LamDK.ofLam ((Lam.abs x M).app N)) d =
      interpDKRelVal 𝓜 V K hK hV η
        (LamDK.ofLam (Lam.substCA M x N)) d := by
  let body := interpDKBodyGraph 𝓜 V K hK hV η x (LamDK.ofLam M)
  have hbodyC : memB body 𝓜.C = ⊤ :=
    interpDKBodyGraph_ofLam_mem_C 𝓜 V K hK hV η x M
  have hvalAbs : lamDKVal V K (LamDK.ofLam (Lam.abs x M)) = ⊤ :=
    lamDKVal_ofLam V K hV (Lam.abs x M)
  have hnameN :
      interpDKRelVal 𝓜 V K hK hV η (LamDK.ofLam N)
        (interpDKName 𝓜 V K hK hV η (LamDK.ofLam N)) = ⊤ :=
    interpDKName_spec 𝓜 V K hK hV η (LamDK.ofLam N)
      (lamDKVal_ofLam V K hV N)
  have hsub :=
    interpDKRelVal_substCA 𝓜 V K hK hV hVsep η M N x d
  rw [hsub]
  have hsubFun : subsetB 𝓜.Fun (prodB 𝓜.D 𝓜.C) = ⊤ :=
    isFunctionB_subset 𝓜.fun_function
  apply le_antisymm
  · simp only [LamDK.ofLam, interpDKRelVal_app, interpDKRelVal_abs]
    simp only [LamDK.ofLam] at hvalAbs
    simp only [hvalAbs, top_inf_eq]
    refine iSup_le fun c => iSup_le fun q' =>
      iSup_le fun p => iSup_le fun q => ?_
    set t :=
      memB (opairB body (𝓜.D.child p)) 𝓜.Lam ⊓
        interpDKRelVal 𝓜 V K hK hV η (LamDK.ofLam N) q ⊓
        memB (opairB (𝓜.D.child p) (𝓜.C.child c)) 𝓜.Fun ⊓
        (oid 𝓜.D).eq q q' ⊓
        memB (𝓜.C.child c) 𝓜.C ⊓
        memB (opairB (𝓜.D.child q') (𝓜.D.child d)) (𝓜.C.child c)
    have htA : t ≤ memB (opairB body (𝓜.D.child p)) 𝓜.Lam :=
      inf_le_of_left_le (inf_le_of_left_le (inf_le_of_left_le
        (inf_le_of_left_le inf_le_left)))
    have htB : t ≤ interpDKRelVal 𝓜 V K hK hV η (LamDK.ofLam N) q :=
      inf_le_of_left_le (inf_le_of_left_le (inf_le_of_left_le
        (inf_le_of_left_le inf_le_right)))
    have htC : t ≤ memB (opairB (𝓜.D.child p) (𝓜.C.child c)) 𝓜.Fun :=
      inf_le_of_left_le (inf_le_of_left_le (inf_le_of_left_le inf_le_right))
    have htD : t ≤ (oid 𝓜.D).eq q q' :=
      inf_le_of_left_le (inf_le_of_left_le inf_le_right)
    have htF : t ≤
        memB (opairB (𝓜.D.child q') (𝓜.D.child d)) (𝓜.C.child c) :=
      inf_le_right
    have hretract : t ≤ eqB body (𝓜.C.child c) := by
      have hpair :
          t ≤
            memB (opairB body (𝓜.D.child p)) 𝓜.Lam ⊓
              memB (opairB (𝓜.D.child p) (𝓜.C.child c)) 𝓜.Fun :=
        le_inf htA htC
      have hjoin :
          memB (opairB body (𝓜.D.child p)) 𝓜.Lam ⊓
              memB (opairB (𝓜.D.child p) (𝓜.C.child c)) 𝓜.Fun ≤
            ⨆ p' : 𝓜.D.idx,
              memB (opairB body (𝓜.D.child p')) 𝓜.Lam ⊓
                memB (opairB (𝓜.D.child p') (𝓜.C.child c)) 𝓜.Fun :=
        le_iSup (fun p' : 𝓜.D.idx =>
          memB (opairB body (𝓜.D.child p')) 𝓜.Lam ⊓
            memB (opairB (𝓜.D.child p') (𝓜.C.child c)) 𝓜.Fun) p
      rw [𝓜.retract_body_eq body c hbodyC] at hjoin
      exact hpair.trans hjoin
    have hevalBody : t ≤
        memB (opairB (𝓜.D.child q') (𝓜.D.child d)) body := by
      have hsubeq : eqB body (𝓜.C.child c) ≤
          subsetB (𝓜.C.child c) body := by
        rw [eqB_comm, eqB_eq_subset]
        exact inf_le_left
      exact (memB_of_subsetB
          (opairB (𝓜.D.child q') (𝓜.D.child d))
          (𝓜.C.child c) body).trans' (le_inf htF (hretract.trans hsubeq))
    have hrow :
        t ≤ interpDKRelVal 𝓜 V K hK hV
          (η.update hV 𝓜.total x q') (LamDK.ofLam M) d := by
      rw [← memB_interpDKBodyGraph_ofLam]
      exact hevalBody
    have hNq' : t ≤ interpDKRelVal 𝓜 V K hK hV η (LamDK.ofLam N) q' :=
      (interpDKRelVal_isRelElementAt 𝓜 V K hK hV η (LamDK.ofLam N)).respects
        q q' |>.trans' (le_inf htD htB)
    have hoidN : t ≤ (oid 𝓜.D).eq
        (interpDKName 𝓜 V K hK hV η (LamDK.ofLam N)) q' := by
      rw [interpDKRelVal_ofLam_eq_oid] at hNq'
      exact hNq'
    have hpt :=
      interpDKRelVal_isPointwiseFamily 𝓜 V K hK hV (oid 𝓜.D)
        (fun z => η.update hV 𝓜.total x z)
        (RelFun.isPointwiseFamily_update η hV 𝓜.total x)
        (LamDK.ofLam M) q'
        (interpDKName 𝓜 V K hK hV η (LamDK.ofLam N)) d
    refine hpt.trans' (le_inf ?_ hrow)
    rw [(oid 𝓜.D).symm]
    exact hoidN
  · simp only [LamDK.ofLam, interpDKRelVal_app, interpDKRelVal_abs]
    simp only [LamDK.ofLam] at hvalAbs
    simp only [hvalAbs, top_inf_eq]
    have hLamTot :
        (⨆ p : 𝓜.D.idx, memB (opairB body (𝓜.D.child p)) 𝓜.Lam) = ⊤ :=
      𝓜.lam_total_child body hbodyC
    have hbodyEval :
        interpDKRelVal 𝓜 V K hK hV
            (η.update hV 𝓜.total x
              (interpDKName 𝓜 V K hK hV η (LamDK.ofLam N)))
            (LamDK.ofLam M) d =
          memB (opairB
              (𝓜.D.child (interpDKName 𝓜 V K hK hV η (LamDK.ofLam N)))
              (𝓜.D.child d)) body :=
      (memB_interpDKBodyGraph_ofLam 𝓜 V K hK hV η x M
        (interpDKName 𝓜 V K hK hV η (LamDK.ofLam N)) d).symm
    rw [hbodyEval]
    conv => lhs; rw [← inf_top_eq (a :=
      memB (opairB
        (𝓜.D.child (interpDKName 𝓜 V K hK hV η (LamDK.ofLam N)))
        (𝓜.D.child d)) body)]
    rw [← hLamTot, inf_iSup_eq]
    refine iSup_le fun p => ?_
    have hFunTot := 𝓜.fun_total_child p
    refine (le_inf le_rfl (le_top.trans hFunTot.ge)).trans ?_
    rw [inf_iSup_eq]
    refine iSup_le fun c => ?_
    refine le_iSup_of_le c (le_iSup_of_le
        (interpDKName 𝓜 V K hK hV η (LamDK.ofLam N))
        (le_iSup_of_le p (le_iSup_of_le
          (interpDKName 𝓜 V K hK hV η (LamDK.ofLam N)) ?_)))
    have hretract :
        memB (opairB body (𝓜.D.child p)) 𝓜.Lam ⊓
            memB (opairB (𝓜.D.child p) (𝓜.C.child c)) 𝓜.Fun ≤
          eqB body (𝓜.C.child c) := by
      have hjoin := le_iSup (fun p' : 𝓜.D.idx =>
          memB (opairB body (𝓜.D.child p')) 𝓜.Lam ⊓
            memB (opairB (𝓜.D.child p') (𝓜.C.child c)) 𝓜.Fun) p
      rw [𝓜.retract_body_eq body c hbodyC] at hjoin
      exact hjoin
    have hFunC :
        memB (opairB (𝓜.D.child p) (𝓜.C.child c)) 𝓜.Fun ≤
          memB (𝓜.C.child c) 𝓜.C :=
      (memB_opairB_le_of_subsetB hsubFun (𝓜.D.child p) (𝓜.C.child c)).trans
        inf_le_right
    have hevalC :
        memB (opairB
            (𝓜.D.child (interpDKName 𝓜 V K hK hV η (LamDK.ofLam N)))
            (𝓜.D.child d)) body ⊓
          memB (opairB body (𝓜.D.child p)) 𝓜.Lam ⊓
          memB (opairB (𝓜.D.child p) (𝓜.C.child c)) 𝓜.Fun ≤
        memB (opairB
            (𝓜.D.child (interpDKName 𝓜 V K hK hV η (LamDK.ofLam N)))
            (𝓜.D.child d)) (𝓜.C.child c) := by
      have hsubeq : eqB body (𝓜.C.child c) ≤ subsetB body (𝓜.C.child c) := by
        rw [eqB_eq_subset]
        exact inf_le_left
      refine (memB_of_subsetB
          (opairB
            (𝓜.D.child (interpDKName 𝓜 V K hK hV η (LamDK.ofLam N)))
            (𝓜.D.child d))
          body (𝓜.C.child c)).trans' ?_
      have hLF :
          memB (opairB
              (𝓜.D.child (interpDKName 𝓜 V K hK hV η (LamDK.ofLam N)))
              (𝓜.D.child d)) body ⊓
            memB (opairB body (𝓜.D.child p)) 𝓜.Lam ⊓
            memB (opairB (𝓜.D.child p) (𝓜.C.child c)) 𝓜.Fun ≤
          memB (opairB body (𝓜.D.child p)) 𝓜.Lam ⊓
            memB (opairB (𝓜.D.child p) (𝓜.C.child c)) 𝓜.Fun :=
        le_inf (inf_le_of_left_le inf_le_right) inf_le_right
      refine le_inf (inf_le_of_left_le inf_le_left)
        ((hLF.trans hretract).trans hsubeq)
    have hxx : (oid 𝓜.D).eq
        (interpDKName 𝓜 V K hK hV η (LamDK.ofLam N))
        (interpDKName 𝓜 V K hK hV η (LamDK.ofLam N)) = ⊤ :=
      𝓜.total _
    refine le_inf (le_inf (le_inf (le_inf (le_inf ?_ ?_) ?_) ?_) ?_) ?_
    · exact inf_le_of_left_le inf_le_right
    · exact le_top.trans hnameN.ge
    · exact inf_le_right
    · exact le_top.trans hxx.ge
    · exact inf_le_right.trans hFunC
    · exact hevalC

/-- α-soundness: `⟦λx. M⟧_η = ⟦λy. M[x := y]⟧_η` when `y ∉ fv(M)`. -/
theorem interpDKRelVal_sound_alpha
    (𝓜 : InternalReflexiveModel (A := A))
    (V K : AName.{u} A) (hK : subsetB K 𝓜.D = ⊤)
    (hV : (oid V).IsTotal)
    (hVsep : OidSeparated V)
    [DecidableEq V.idx] [Infinite V.idx]
    (η : RelFun (oid V) (oid 𝓜.D))
    (x y : V.idx) (M : Lam V.idx) (hy : y ∉ M.fv) (d : 𝓜.D.idx) :
    interpDKRelVal 𝓜 V K hK hV η (LamDK.ofLam (Lam.abs x M)) d =
      interpDKRelVal 𝓜 V K hK hV η
        (LamDK.ofLam (Lam.abs y (Lam.substCA M x (Lam.var y)))) d := by
  simp only [LamDK.ofLam, interpDKRelVal_abs]
  have hvalL : lamDKVal V K (LamDK.ofLam (Lam.abs x M)) = ⊤ :=
    lamDKVal_ofLam V K hV (Lam.abs x M)
  have hvalR :
      lamDKVal V K
        (LamDK.ofLam (Lam.abs y (Lam.substCA M x (Lam.var y)))) = ⊤ :=
    lamDKVal_ofLam V K hV (Lam.abs y (Lam.substCA M x (Lam.var y)))
  simp only [LamDK.ofLam] at hvalL hvalR
  simp only [hvalL, hvalR, top_inf_eq]
  apply congr_arg (fun G => memB (opairB G (𝓜.D.child d)) 𝓜.Lam)
  apply interpDKBodyGraph_eq_of
  intro q e
  rw [interpDKRelVal_substCA 𝓜 V K hK hV hVsep
    (η.update hV 𝓜.total y q) M (Lam.var y) x e]
  have hzoid :
      (oid 𝓜.D).eq
        (interpDKName 𝓜 V K hK hV (η.update hV 𝓜.total y q)
          (LamDK.ofLam (Lam.var y))) q = ⊤ := by
    rw [← interpDKRelVal_ofLam_eq_oid]
    simp only [LamDK.ofLam, interpDKRelVal_var, RelFun.update_self]
    exact 𝓜.total q
  have hup :=
    RelFun.update_eq_of_target (η.update hV 𝓜.total y q)
      hV 𝓜.total x
      (interpDKName 𝓜 V K hK hV (η.update hV 𝓜.total y q)
        (LamDK.ofLam (Lam.var y)))
      q hzoid
  rw [hup]
  by_cases hyx : y = x
  · cases hyx
    rw [RelFun.update_overwrite]
  · rw [← RelFun.update_commute η hV 𝓜.total y x q q (hVsep y x hyx)]
    exact (interpDKRelVal_update_fresh 𝓜 V K hK hV hVsep
      (η.update hV 𝓜.total x q) M y hy q e).symm

/-- Internal [4, Theorem 5.4.4]: `LamEq` is sound for Definition 25. -/
theorem interpDKRelVal_sound_ofLam
    (𝓜 : InternalReflexiveModel (A := A))
    (V K : AName.{u} A) (hK : subsetB K 𝓜.D = ⊤)
    (hV : (oid V).IsTotal)
    (hVsep : OidSeparated V)
    [DecidableEq V.idx] [Infinite V.idx]
    (η : RelFun (oid V) (oid 𝓜.D))
    {M N : Lam V.idx} (h : LamEq M N) (d : 𝓜.D.idx) :
    interpDKRelVal 𝓜 V K hK hV η (LamDK.ofLam M) d =
      interpDKRelVal 𝓜 V K hK hV η (LamDK.ofLam N) d := by
  induction h generalizing η d with
  | refl M =>
    rfl
  | symm _ ih =>
    exact (ih η d).symm
  | trans _ _ ih1 ih2 =>
    exact (ih1 η d).trans (ih2 η d)
  | app_left _ ih =>
    simp only [LamDK.ofLam, interpDKRelVal_app]
    refine iSup_congr fun c => iSup_congr fun q' =>
      iSup_congr fun p => iSup_congr fun q => ?_
    rw [ih η p]
  | app_right _ ih =>
    simp only [LamDK.ofLam, interpDKRelVal_app]
    refine iSup_congr fun c => iSup_congr fun q' =>
      iSup_congr fun p => iSup_congr fun q => ?_
    rw [ih η q]
  | @xi z P Q hPQ ih =>
    simp only [LamDK.ofLam, interpDKRelVal_abs]
    have hvalL : lamDKVal V K (LamDK.ofLam (Lam.abs z P)) = ⊤ :=
      lamDKVal_ofLam V K hV (Lam.abs z P)
    have hvalR : lamDKVal V K (LamDK.ofLam (Lam.abs z Q)) = ⊤ :=
      lamDKVal_ofLam V K hV (Lam.abs z Q)
    simp only [LamDK.ofLam] at hvalL hvalR
    simp only [hvalL, hvalR, top_inf_eq]
    apply congr_arg (fun G => memB (opairB G (𝓜.D.child d)) 𝓜.Lam)
    apply interpDKBodyGraph_eq_of
    intro q e
    exact ih (η.update hV 𝓜.total z q) e
  | beta z P Q =>
    exact interpDKRelVal_sound_beta 𝓜 V K hK hV hVsep η z P Q d
  | alpha z w P hy =>
    exact interpDKRelVal_sound_alpha 𝓜 V K hK hV hVsep η z w P hy d

/-- The two internal `D`-names of `λ`-equal pure terms are Boolean-equal. -/
theorem theorem26Pure_sound
    (𝓜 : InternalReflexiveModel (A := A))
    (V K : AName.{u} A) (hK : subsetB K 𝓜.D = ⊤)
    (hV : (oid V).IsTotal)
    (hVsep : OidSeparated V)
    [DecidableEq V.idx] [Infinite V.idx]
    (η : RelFun (oid V) (oid 𝓜.D))
    {M N : Lam V.idx} (h : LamEq M N) (d : 𝓜.D.idx) :
    interpDKRelVal 𝓜 V K hK hV η (LamDK.ofLam M) d =
      interpDKRelVal 𝓜 V K hK hV η (LamDK.ofLam N) d :=
  interpDKRelVal_sound_ofLam 𝓜 V K hK hV hVsep η h d

theorem theorem26Pure_sound_eqB
    (𝓜 : InternalReflexiveModel (A := A))
    (V K : AName.{u} A) (hK : subsetB K 𝓜.D = ⊤)
    (hV : (oid V).IsTotal)
    (hVsep : OidSeparated V)
    [DecidableEq V.idx] [Infinite V.idx]
    (η : RelFun (oid V) (oid 𝓜.D))
    {M N : Lam V.idx} (h : LamEq M N) :
    eqB
        (𝓜.D.child (interpDKName 𝓜 V K hK hV η (LamDK.ofLam M)))
        (𝓜.D.child (interpDKName 𝓜 V K hK hV η (LamDK.ofLam N))) = ⊤ := by
  have hoid :
      (oid 𝓜.D).eq
        (interpDKName 𝓜 V K hK hV η (LamDK.ofLam M))
        (interpDKName 𝓜 V K hK hV η (LamDK.ofLam N)) = ⊤ := by
    rw [← interpDKRelVal_ofLam_eq_oid]
    rw [theorem26Pure_sound 𝓜 V K hK hV hVsep η h]
    exact interpDKName_spec 𝓜 V K hK hV η (LamDK.ofLam N)
      (lamDKVal_ofLam V K hV N)
  rwa [← oid_eq_of_total 𝓜.D 𝓜.total]

/-- Ground `LamEq` lands in `lamEqB`, so Example 24 applies to checked
equations. Soundness itself is `theorem26Pure_sound`. -/
theorem theorem26Pure_sound_encodeEq
    (𝓜 : InternalReflexiveModel (A := A))
    (V K : AName.{u} A) (hK : subsetB K 𝓜.D = ⊤)
    (hV : (oid V).IsTotal)
    (hVsep : OidSeparated V)
    [DecidableEq V.idx] [Infinite V.idx]
    (η : RelFun (oid V) (oid 𝓜.D))
    {M N : Lam V.idx} (h : LamEq M N) :
    memB (encodeEqB V M N) (lamEqB V) = ⊤ ∧
      (∀ d, interpDKRelVal 𝓜 V K hK hV η (LamDK.ofLam M) d =
        interpDKRelVal 𝓜 V K hK hV η (LamDK.ofLam N) d) :=
  ⟨memB_encodeEqB V M N h,
    fun d => theorem26Pure_sound 𝓜 V K hK hV hVsep η h d⟩

end Scott2026
