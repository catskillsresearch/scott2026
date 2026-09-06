/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/

import Scott2026.LambdaVA

/-!
# Constant-bearing lambda syntax in `V^A`

This is Example 21 and Definition 20 with the paper's fourth tag `(3,d)`.
Unlike the pure checked-variable presentation, an arbitrary Boolean-valued
constant set need not have extent `⊤`; term extents are therefore propagated
recursively through the inductive constructors.
-/

universe u

namespace Scott2026

open AName

/-- Definition 20 syntax, with variables and denotational constants kept as
separate index types. -/
inductive LamDK (Var Const : Type u) : Type u where
  | var (x : Var)
  | const (d : Const)
  | abs (x : Var) (M : LamDK Var Const)
  | app (M N : LamDK Var Const)

/-- Paper tag `3`: a constant appears as `(3,d)`. -/
def pLamConst (d : PSet.{u}) : PSet.{u} :=
  pOpair (PSet.ofNat 3) d

/-- Ground tagged encoding of Definition 20 terms. -/
def encodeLamDK {Var Const : Type u} (f : Var → PSet.{u})
    (g : Const → PSet.{u}) : LamDK Var Const → PSet.{u}
  | .var x => pLamVar (f x)
  | .const d => pLamConst (g d)
  | .abs x M => pLamAbs (f x) (encodeLamDK f g M)
  | .app M N => pLamApp (encodeLamDK f g M) (encodeLamDK f g N)

/-- Ground set `Λ(D,Var,K)`; `D` is part of the notation while the syntax
depends only on `Var` and `K`. -/
def pLamDKSet (D Var K : PSet.{u}) : PSet.{u} :=
  PSet.mk (LamDK Var.Type K.Type) (encodeLamDK Var.Func K.Func)

variable {A : Type u} [CompleteBooleanAlgebra A]

/-- Internal constant encoding `(3,d)^A`. -/
noncomputable def lamConstB (d : AName.{u} A) : AName.{u} A :=
  opairB (check (PSet.ofNat 3)) d

/-- Internal tagged encoding of Definition 20 terms. -/
noncomputable def encodeLamDKB (V K : AName.{u} A) :
    LamDK V.idx K.idx → AName.{u} A
  | .var x => lamVarB (V.child x)
  | .const d => lamConstB (K.child d)
  | .abs x M => lamAbsB (V.child x) (encodeLamDKB V K M)
  | .app M N => lamAppB (encodeLamDKB V K M) (encodeLamDKB V K N)

/-- Boolean extent of a Definition 20 term. -/
noncomputable def lamDKVal (V K : AName.{u} A) :
    LamDK V.idx K.idx → A
  | .var x => memB (V.child x) V
  | .const d => memB (K.child d) K
  | .abs x M => memB (V.child x) V ⊓ lamDKVal V K M
  | .app M N => lamDKVal V K M ⊓ lamDKVal V K N

/-- `Λ(D,V,K)^A`. The parameter `D` records the ambient denotational domain;
well-formed uses require `K ⊆ D`. -/
noncomputable def lamDKB (D V K : AName.{u} A) : AName.{u} A :=
  mk (LamDK V.idx K.idx) (encodeLamDKB V K) (lamDKVal V K)

/-- Boolean value of the paper's constant-bearing inductive clause. -/
noncomputable def lamDKInductiveB
    (D V K X : AName.{u} A) : A :=
  lamInductiveB V X ⊓
    ⨅ d : AName.{u} A, memB d K ⇨
      ⨆ p : AName.{u} A, memB p X ⊓ eqB p (lamConstB d)

theorem eqB_lamConstB (d e : AName.{u} A) :
    eqB (lamConstB d) (lamConstB e) = eqB d e := by
  rw [lamConstB, lamConstB, eqB_opairB, eqB_self, top_inf_eq]

theorem memB_lamDKB (z D V K : AName.{u} A) :
    memB z (lamDKB D V K) =
      ⨆ M : LamDK V.idx K.idx,
        eqB z (encodeLamDKB V K M) ⊓ lamDKVal V K M := by
  rw [lamDKB, memB_mk]

theorem lamDKVal_le_memB (D V K : AName.{u} A)
    (M : LamDK V.idx K.idx) :
    lamDKVal V K M ≤ memB (encodeLamDKB V K M) (lamDKB D V K) := by
  rw [memB_lamDKB]
  refine le_iSup_of_le M ?_
  rw [eqB_self, top_inf_eq]

/-- Constant constructor closure. -/
theorem lamDKInductiveB_const (D V K : AName.{u} A) :
    (⨅ d : AName.{u} A, memB d K ⇨
      ⨆ p : AName.{u} A,
        memB p (lamDKB D V K) ⊓ eqB p (lamConstB d)) = ⊤ := by
  refine iInf_eq_top.mpr fun d => himp_eq_top_iff.mpr ?_
  rw [memB_eq]
  refine iSup_le fun i => ?_
  refine le_iSup_of_le (encodeLamDKB V K (.const i)) ?_
  change eqB d (K.child i) ⊓ K.val i ≤
    memB (lamConstB (K.child i)) (lamDKB D V K) ⊓
      eqB (lamConstB (K.child i)) (lamConstB d)
  refine le_inf ?_ ?_
  · exact (lamDKVal_le_memB D V K (.const i)).trans'
      (inf_le_right.trans (val_le_memB K i))
  · rw [eqB_lamConstB, eqB_comm]
    exact inf_le_left

/-- Variable constructor closure. -/
theorem lamDKInductiveB_var (D V K : AName.{u} A) :
    (⨅ x : AName.{u} A, memB x V ⇨
      ⨆ p : AName.{u} A,
        memB p (lamDKB D V K) ⊓ eqB p (lamVarB x)) = ⊤ := by
  refine iInf_eq_top.mpr fun x => himp_eq_top_iff.mpr ?_
  rw [memB_eq]
  refine iSup_le fun i => ?_
  refine le_iSup_of_le (encodeLamDKB V K (.var i)) ?_
  change eqB x (V.child i) ⊓ V.val i ≤
    memB (lamVarB (V.child i)) (lamDKB D V K) ⊓
      eqB (lamVarB (V.child i)) (lamVarB x)
  refine le_inf ?_ ?_
  · exact (lamDKVal_le_memB D V K (.var i)).trans'
      (inf_le_right.trans (val_le_memB V i))
  · rw [eqB_lamVarB, eqB_comm]
    exact inf_le_left

/-- Abstraction constructor closure. -/
theorem lamDKInductiveB_abs (D V K : AName.{u} A) :
    (⨅ x : AName.{u} A, memB x V ⇨
      ⨅ M : AName.{u} A, memB M (lamDKB D V K) ⇨
        ⨆ p : AName.{u} A,
          memB p (lamDKB D V K) ⊓ eqB p (lamAbsB x M)) = ⊤ := by
  refine iInf_eq_top.mpr fun x => himp_eq_top_iff.mpr ?_
  refine le_iInf fun M => ?_
  rw [le_himp_iff, memB_eq (x := x) (y := V), memB_lamDKB, iSup_inf_eq]
  refine iSup_le fun i => ?_
  rw [inf_iSup_eq]
  refine iSup_le fun N => ?_
  refine le_iSup_of_le (encodeLamDKB V K (.abs i N)) ?_
  change (eqB x (V.child i) ⊓ V.val i) ⊓
      (eqB M (encodeLamDKB V K N) ⊓ lamDKVal V K N) ≤
    memB (lamAbsB (V.child i) (encodeLamDKB V K N)) (lamDKB D V K) ⊓
      eqB (lamAbsB (V.child i) (encodeLamDKB V K N)) (lamAbsB x M)
  refine le_inf ?_ ?_
  · refine (lamDKVal_le_memB D V K (.abs i N)).trans' (le_inf ?_ ?_)
    · exact (val_le_memB V i).trans' (inf_le_left.trans inf_le_right)
    · exact inf_le_right.trans inf_le_right
  · rw [eqB_lamAbsB, eqB_comm (x := V.child i) (y := x),
      eqB_comm (x := encodeLamDKB V K N) (y := M)]
    exact le_inf (inf_le_left.trans inf_le_left)
      (inf_le_right.trans inf_le_left)

/-- Application constructor closure. -/
theorem lamDKInductiveB_app (D V K : AName.{u} A) :
    (⨅ M : AName.{u} A, memB M (lamDKB D V K) ⇨
      ⨅ N : AName.{u} A, memB N (lamDKB D V K) ⇨
        ⨆ p : AName.{u} A,
          memB p (lamDKB D V K) ⊓ eqB p (lamAppB M N)) = ⊤ := by
  refine iInf_eq_top.mpr fun M => himp_eq_top_iff.mpr ?_
  refine le_iInf fun N => ?_
  rw [le_himp_iff, memB_lamDKB (z := M), memB_lamDKB (z := N), iSup_inf_eq]
  refine iSup_le fun M' => ?_
  rw [inf_iSup_eq]
  refine iSup_le fun N' => ?_
  refine le_iSup_of_le (encodeLamDKB V K (.app M' N')) ?_
  change (eqB M (encodeLamDKB V K M') ⊓ lamDKVal V K M') ⊓
      (eqB N (encodeLamDKB V K N') ⊓ lamDKVal V K N') ≤
    memB (lamAppB (encodeLamDKB V K M') (encodeLamDKB V K N'))
        (lamDKB D V K) ⊓
      eqB (lamAppB (encodeLamDKB V K M') (encodeLamDKB V K N'))
        (lamAppB M N)
  refine le_inf ?_ ?_
  · exact (lamDKVal_le_memB D V K (.app M' N')).trans'
      (le_inf (inf_le_left.trans inf_le_right)
        (inf_le_right.trans inf_le_right))
  · rw [eqB_lamAppB, eqB_comm (x := encodeLamDKB V K M') (y := M),
      eqB_comm (x := encodeLamDKB V K N') (y := N)]
    exact le_inf (inf_le_left.trans inf_le_left)
      (inf_le_right.trans inf_le_left)

/-- `Λ(D,V,K)^A` satisfies all four Example 21 clauses. -/
theorem lamDKInductiveB_lamDKB (D V K : AName.{u} A) :
    lamDKInductiveB D V K (lamDKB D V K) = ⊤ := by
  unfold lamDKInductiveB lamInductiveB
  refine inf_eq_top_iff.mpr ⟨?_, lamDKInductiveB_const D V K⟩
  refine inf_eq_top_iff.mpr ⟨?_, lamDKInductiveB_app D V K⟩
  exact inf_eq_top_iff.mpr
    ⟨lamDKInductiveB_var D V K, lamDKInductiveB_abs D V K⟩

/-- Equality witnesses in a name evaluate below membership of their target. -/
theorem iSup_memB_inf_eqB_le (X t : AName.{u} A) :
    (⨆ p : AName.{u} A, memB p X ⊓ eqB p t) ≤ memB t X :=
  iSup_le fun p => memB_eqB_left p X t

theorem lamDKInductiveB_pure_part {D V K X : AName.{u} A}
    (h : lamDKInductiveB D V K X = ⊤) :
    lamInductiveB V X = ⊤ :=
  (inf_eq_top_iff.mp h).1

theorem lamDKInductiveB_const_le {D V K X : AName.{u} A}
    (h : lamDKInductiveB D V K X = ⊤) (d : AName.{u} A) :
    memB d K ≤
      ⨆ p : AName.{u} A, memB p X ⊓ eqB p (lamConstB d) :=
  himp_eq_top_iff.mp
    (iInf_eq_top.mp (inf_eq_top_iff.mp h).2 d)

/-- Structural leastness estimate for arbitrary Boolean-valued variables and
constants. -/
theorem lamDKVal_le_memB_of_inductive {D V K X : AName.{u} A}
    (h : lamDKInductiveB D V K X = ⊤)
    (M : LamDK V.idx K.idx) :
    lamDKVal V K M ≤ memB (encodeLamDKB V K M) X := by
  induction M with
  | var x =>
    exact (lamInductiveB_var_le (lamDKInductiveB_pure_part h) (V.child x)).trans
      (iSup_memB_inf_eqB_le X (lamVarB (V.child x)))
  | const d =>
    exact (lamDKInductiveB_const_le h (K.child d)).trans
      (iSup_memB_inf_eqB_le X (lamConstB (K.child d)))
  | abs x M ih =>
    calc
      lamDKVal V K (.abs x M) ≤
          memB (V.child x) V ⊓ memB (encodeLamDKB V K M) X :=
        le_inf inf_le_left (inf_le_right.trans ih)
      _ ≤ ⨆ p : AName.{u} A,
          memB p X ⊓ eqB p
            (lamAbsB (V.child x) (encodeLamDKB V K M)) :=
        lamInductiveB_abs_le (lamDKInductiveB_pure_part h)
          (V.child x) (encodeLamDKB V K M)
      _ ≤ memB (encodeLamDKB V K (.abs x M)) X :=
        iSup_memB_inf_eqB_le X
          (lamAbsB (V.child x) (encodeLamDKB V K M))
  | app M N ihM ihN =>
    calc
      lamDKVal V K (.app M N) ≤
          memB (encodeLamDKB V K M) X ⊓ memB (encodeLamDKB V K N) X :=
        le_inf (inf_le_left.trans ihM) (inf_le_right.trans ihN)
      _ ≤ ⨆ p : AName.{u} A,
          memB p X ⊓ eqB p
            (lamAppB (encodeLamDKB V K M) (encodeLamDKB V K N)) :=
        lamInductiveB_app_le (lamDKInductiveB_pure_part h)
          (encodeLamDKB V K M) (encodeLamDKB V K N)
      _ ≤ memB (encodeLamDKB V K (.app M N)) X :=
        iSup_memB_inf_eqB_le X
          (lamAppB (encodeLamDKB V K M) (encodeLamDKB V K N))

/-- `Λ(D,V,K)^A` is the least name satisfying the four inductive clauses. -/
theorem lamDKB_least {D V K X : AName.{u} A}
    (h : lamDKInductiveB D V K X = ⊤) :
    subsetB (lamDKB D V K) X = ⊤ := by
  rw [lamDKB, subsetB_mk]
  refine iInf_eq_top.mpr fun M => himp_eq_top_iff.mpr ?_
  exact lamDKVal_le_memB_of_inductive h M

/-- Every ground checked term has full Boolean extent. -/
theorem lamDKVal_check (Var K : PSet.{u})
    (M : LamDK (check (A := A) Var).idx (check (A := A) K).idx) :
    lamDKVal (check (A := A) Var) (check (A := A) K) M = ⊤ := by
  induction M with
  | var x => exact memB_check_child Var x
  | const d => exact memB_check_child K d
  | abs x M ih => rw [lamDKVal, memB_check_child, ih, top_inf_eq]
  | app M N ihM ihN => rw [lamDKVal, ihM, ihN, top_inf_eq]

/-- Ground and internal tag encodings agree for all four constructors. -/
theorem check_encodeLamDK (Var K : PSet.{u})
    (M : LamDK Var.Type K.Type) :
    eqB (check (A := A) (encodeLamDK Var.Func K.Func M))
      (encodeLamDKB
        (mk Var.Type (fun i => check (A := A) (Var.Func i)) (fun _ => ⊤))
        (mk K.Type (fun i => check (A := A) (K.Func i)) (fun _ => ⊤)) M) = ⊤ := by
  induction M with
  | var x => exact check_opair (A := A) (PSet.ofNat 0) (Var.Func x)
  | const d => exact check_opair (A := A) (PSet.ofNat 3) (K.Func d)
  | abs x M ih =>
    exact eqB_top_trans
      (eqB_top_trans
        (check_opair (A := A) (PSet.ofNat 1)
          (pOpair (Var.Func x) (encodeLamDK Var.Func K.Func M)))
        (eqB_opairB_top (eqB_self _)
          (check_opair (A := A) (Var.Func x)
            (encodeLamDK Var.Func K.Func M))))
      (eqB_opairB_top (eqB_self _)
        (eqB_opairB_top (eqB_self _) ih))
  | app M N ihM ihN =>
    exact eqB_top_trans
      (eqB_top_trans
        (check_opair (A := A) (PSet.ofNat 2)
          (pOpair (encodeLamDK Var.Func K.Func M)
            (encodeLamDK Var.Func K.Func N)))
        (eqB_opairB_top (eqB_self _)
          (check_opair (A := A) (encodeLamDK Var.Func K.Func M)
            (encodeLamDK Var.Func K.Func N))))
      (eqB_opairB_top (eqB_self _) (eqB_opairB_top ihM ihN))

/-- Check commutation for the full Definition 20 syntax. -/
theorem lamDKB_check_eq (D Var K : PSet.{u}) :
    eqB (check (A := A) (pLamDKSet D Var K))
      (lamDKB (check (A := A) D) (check (A := A) Var)
        (check (A := A) K)) = ⊤ := by
  rw [check_eq_mk (A := A) D, check_eq_mk (A := A) Var,
    check_eq_mk (A := A) K, pLamDKSet, check_mk, lamDKB]
  have hv :
      lamDKVal
        (mk Var.Type (fun i => check (A := A) (Var.Func i)) (fun _ => ⊤))
        (mk K.Type (fun i => check (A := A) (K.Func i)) (fun _ => ⊤)) =
        fun _ => ⊤ := by
    funext M
    have hV (i :
        (mk Var.Type (fun j => check (A := A) (Var.Func j)) (fun _ => ⊤)).idx) :
        memB
          ((mk Var.Type (fun j => check (A := A) (Var.Func j))
            (fun _ => ⊤)).child i)
          (mk Var.Type (fun j => check (A := A) (Var.Func j)) (fun _ => ⊤)) = ⊤ := by
      apply top_unique
      exact (val_le_memB
        (mk Var.Type (fun j => check (A := A) (Var.Func j)) (fun _ => ⊤)) i)
    have hK (i :
        (mk K.Type (fun j => check (A := A) (K.Func j)) (fun _ => ⊤)).idx) :
        memB
          ((mk K.Type (fun j => check (A := A) (K.Func j))
            (fun _ => ⊤)).child i)
          (mk K.Type (fun j => check (A := A) (K.Func j)) (fun _ => ⊤)) = ⊤ := by
      apply top_unique
      exact (val_le_memB
        (mk K.Type (fun j => check (A := A) (K.Func j)) (fun _ => ⊤)) i)
    induction M with
    | var x => exact hV x
    | const d => exact hK d
    | abs x M ih => rw [lamDKVal, hV, ih, top_inf_eq]
    | app M N ihM ihN => rw [lamDKVal, ihM, ihN, top_inf_eq]
  rw [hv]
  exact eqB_mk_top _ _ (check_encodeLamDK (A := A) Var K)

end Scott2026
