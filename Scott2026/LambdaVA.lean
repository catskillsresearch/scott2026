/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/

import Scott2026.Lambda
import Scott2026.VA

/-!
# Pure λ-syntax in `V^A` (Example 21 at `V^A` and Proposition 22)

Furber–Mardare–Panangaden–Scott, CSL 2026, Example 21 and Proposition 22.
Pure terms are encoded as pre-sets by the paper’s tags: `(0,x)` a variable,
`(1,(x,M))` an abstraction, `(2,(M,N))` an application. There is no constant
tag `3` in this module, and no claim of `Λ(D, check Var, 𝔎)^A`, `λ^A`, or an
interpretation.

`Λ(check Var)^A` is the name `lamB (check Var)` whose children are the
internally paired encodings. Proposition 22’s check-equality identifies this
name with `check (Λ(Var))`.
-/

universe u

namespace Scott2026

open AName

/-!
## Ground tagged encoding (Example 21)
-/

/-- Paper tag `0`: a variable appears as `(0, x)`. -/
def pLamVar (x : PSet.{u}) : PSet.{u} :=
  pOpair (PSet.ofNat 0) x

/-- Paper tag `1`: an abstraction appears as `(1, (x, M))`. -/
def pLamAbs (x M : PSet.{u}) : PSet.{u} :=
  pOpair (PSet.ofNat 1) (pOpair x M)

/-- Paper tag `2`: an application appears as `(2, (M, N))`. -/
def pLamApp (M N : PSet.{u}) : PSet.{u} :=
  pOpair (PSet.ofNat 2) (pOpair M N)

/-- Encode a ground pure λ-term by the paper’s tags. -/
def encodeLam {α : Type u} (f : α → PSet.{u}) : Lam α → PSet.{u}
  | .var x => pLamVar (f x)
  | .abs x M => pLamAbs (f x) (encodeLam f M)
  | .app M N => pLamApp (encodeLam f M) (encodeLam f N)

/-- Ground set `Λ(Var)` of encoded pure λ-terms. -/
def pLamSet (Var : PSet.{u}) : PSet.{u} :=
  PSet.mk (Lam Var.Type) (encodeLam Var.Func)

/-!
## Internal pairing of tags
-/

variable {A : Type u} [CompleteBooleanAlgebra A]

/-- Internal variable encoding `(0, x)^A`. -/
noncomputable def lamVarB (x : AName.{u} A) : AName.{u} A :=
  opairB (check (PSet.ofNat 0)) x

/-- Internal abstraction encoding `(1, (x, M))^A`. -/
noncomputable def lamAbsB (x M : AName.{u} A) : AName.{u} A :=
  opairB (check (PSet.ofNat 1)) (opairB x M)

/-- Internal application encoding `(2, (M, N))^A`. -/
noncomputable def lamAppB (M N : AName.{u} A) : AName.{u} A :=
  opairB (check (PSet.ofNat 2)) (opairB M N)

/-- Encode a term using the children of a variable name `V`. -/
noncomputable def encodeLamB (V : AName.{u} A) : Lam V.idx → AName.{u} A
  | .var x => lamVarB (V.child x)
  | .abs x M => lamAbsB (V.child x) (encodeLamB V M)
  | .app M N => lamAppB (encodeLamB V M) (encodeLamB V N)

/-- `Λ(V)^A`: the name whose children are the tagged encodings over `dom(V)`. -/
noncomputable def lamB (V : AName.{u} A) : AName.{u} A :=
  mk (Lam V.idx) (encodeLamB V) (fun _ => ⊤)

/-- Boolean value of the paper’s `Λ(V)`-inductive clause (Example 21 at `V^A`).
Pairing atoms are `eqB` of `opairB` encodings, as permitted by `eqB_opairB`. -/
noncomputable def lamInductiveB (V X : AName.{u} A) : A :=
  (⨅ x : AName.{u} A, memB x V ⇨
      ⨆ p : AName.{u} A, memB p X ⊓ eqB p (lamVarB x)) ⊓
    (⨅ x : AName.{u} A, memB x V ⇨
      ⨅ M : AName.{u} A, memB M X ⇨
        ⨆ p : AName.{u} A, memB p X ⊓ eqB p (lamAbsB x M)) ⊓
    (⨅ M : AName.{u} A, memB M X ⇨
      ⨅ N : AName.{u} A, memB N X ⇨
        ⨆ p : AName.{u} A, memB p X ⊓ eqB p (lamAppB M N))

/-!
## Name calculations
-/

theorem eqB_top_trans {x y z : AName.{u} A}
    (hxy : eqB x y = ⊤) (hyz : eqB y z = ⊤) : eqB x z = ⊤ :=
  top_unique ((le_inf hxy.ge hyz.ge).trans (eqB_trans x y z))

theorem eqB_opairB_top {x y u v : AName.{u} A}
    (hx : eqB x u = ⊤) (hy : eqB y v = ⊤) :
    eqB (opairB x y) (opairB u v) = ⊤ := by
  rw [eqB_opairB, hx, hy, top_inf_eq]

theorem eqB_lamVarB (x y : AName.{u} A) :
    eqB (lamVarB x) (lamVarB y) = eqB x y := by
  rw [lamVarB, lamVarB, eqB_opairB, eqB_self, top_inf_eq]

theorem eqB_lamAbsB (x M y N : AName.{u} A) :
    eqB (lamAbsB x M) (lamAbsB y N) = eqB x y ⊓ eqB M N := by
  rw [lamAbsB, lamAbsB, eqB_opairB, eqB_self, top_inf_eq, eqB_opairB]

theorem eqB_lamAppB (M N M' N' : AName.{u} A) :
    eqB (lamAppB M N) (lamAppB M' N') = eqB M M' ⊓ eqB N N' := by
  rw [lamAppB, lamAppB, eqB_opairB, eqB_self, top_inf_eq, eqB_opairB]

theorem memB_lamB (z V : AName.{u} A) :
    memB z (lamB V) = ⨆ M : Lam V.idx, eqB z (encodeLamB V M) := by
  rw [lamB, memB_mk]
  exact iSup_congr fun _ => inf_top_eq _

theorem memB_encodeLamB (V : AName.{u} A) (M : Lam V.idx) :
    memB (encodeLamB V M) (lamB V) = ⊤ := by
  rw [memB_lamB]
  exact top_unique ((eqB_self (encodeLamB V M)).ge.trans
    (le_iSup (fun N : Lam V.idx => eqB (encodeLamB V M) (encodeLamB V N)) M))

theorem check_eq_mk (x : PSet.{u}) :
    check (A := A) x = mk x.Type (fun i => check (x.Func i)) (fun _ => ⊤) := by
  cases x
  rfl

theorem memB_check_child (Var : PSet.{u}) (i : (check (A := A) Var).idx) :
    memB ((check Var).child i) (check Var) = ⊤ := by
  rw [memB_eq]
  refine top_unique (le_iSup_of_le i ?_)
  rw [check_val (A := A) Var i, eqB_self]
  exact le_inf le_top le_top

theorem eqB_mk_top {α : Type u} (f g : α → AName.{u} A)
    (h : ∀ i, eqB (f i) (g i) = ⊤) :
    eqB (mk α f (fun _ => ⊤)) (mk α g (fun _ => ⊤)) = ⊤ := by
  rw [eqB_mk]
  refine inf_eq_top_iff.mpr ⟨?fwd, ?bwd⟩
  · refine iInf_eq_top.mpr fun i => himp_eq_top_iff.mpr ?_
    rw [memB_mk]
    refine le_iSup_of_le i ?_
    rw [h i, top_inf_eq]
  · refine iInf_eq_top.mpr fun j => himp_eq_top_iff.mpr ?_
    rw [memB_mk]
    refine le_iSup_of_le j ?_
    rw [eqB_comm (x := g j) (y := f j), h j, top_inf_eq]

/-- If `‖∃ p ∈ X. p = t‖ = 1`, then `‖t ∈ X‖ = 1`. Congruence uses
substitution of equality; the witness is Theorem 1(iii). -/
theorem memB_of_exists_eqB (X t : AName.{u} A)
    (htop : (⨆ p : AName.{u} A, memB p X ⊓ eqB p t) = ⊤) :
    memB t X = ⊤ := by
  let φ : AName.{u} A → A := fun p => memB p X ⊓ eqB p t
  have hcongr : ∀ p q, eqB p q ⊓ φ p ≤ φ q := by
    intro p q
    refine le_inf ?mem ?eq
    · have hmem : memB p X ⊓ eqB p q ≤ memB q X := memB_eqB_left p X q
      refine hmem.trans' ?_
      exact le_inf (inf_le_of_right_le inf_le_left) inf_le_left
    · have htrans : eqB q p ⊓ eqB p t ≤ eqB q t := eqB_trans q p t
      refine htrans.trans' ?_
      rw [eqB_comm (x := q) (y := p)]
      exact le_inf inf_le_left (inf_le_of_right_le inf_le_right)
  obtain ⟨p, hp⟩ := theorem_1_iii φ hcongr ⊤ htop.symm
  have hmem : memB p X = ⊤ := top_unique (hp.ge.trans inf_le_left)
  have heq : eqB p t = ⊤ := top_unique (hp.ge.trans inf_le_right)
  rwa [eqB_top_memB_left (x := p) (y := t) (z := X) heq] at hmem

/-!
## Example 21 at `V^A`: `lamB V` is inductive
-/

theorem lamInductiveB_var (V : AName.{u} A) :
    (⨅ x : AName.{u} A, memB x V ⇨
      ⨆ p : AName.{u} A, memB p (lamB V) ⊓ eqB p (lamVarB x)) = ⊤ := by
  refine iInf_eq_top.mpr fun x => himp_eq_top_iff.mpr ?_
  rw [memB_eq]
  refine iSup_le fun i => ?_
  refine le_trans (inf_le_left (b := V.val i)) ?_
  refine le_iSup_of_le (lamVarB (V.child i)) ?_
  have hmem : memB (lamVarB (V.child i)) (lamB V) = ⊤ :=
    memB_encodeLamB V (Lam.var i)
  rw [hmem, eqB_lamVarB, eqB_comm (x := V.child i) (y := x), top_inf_eq]

theorem lamInductiveB_abs (V : AName.{u} A) :
    (⨅ x : AName.{u} A, memB x V ⇨
      ⨅ M : AName.{u} A, memB M (lamB V) ⇨
        ⨆ p : AName.{u} A, memB p (lamB V) ⊓ eqB p (lamAbsB x M)) = ⊤ := by
  refine iInf_eq_top.mpr fun x => himp_eq_top_iff.mpr ?_
  refine le_iInf fun M => ?_
  rw [le_himp_iff]
  rw [memB_eq (x := x) (y := V), memB_lamB, iSup_inf_eq]
  refine iSup_le fun i => ?_
  rw [inf_iSup_eq]
  refine iSup_le fun N => ?_
  refine le_iSup_of_le (encodeLamB V (Lam.abs i N)) ?_
  have hmem : memB (encodeLamB V (Lam.abs i N)) (lamB V) = ⊤ :=
    memB_encodeLamB V (Lam.abs i N)
  change _ ≤ memB (encodeLamB V (Lam.abs i N)) (lamB V) ⊓
    eqB (lamAbsB (V.child i) (encodeLamB V N)) (lamAbsB x M)
  rw [hmem, eqB_lamAbsB, top_inf_eq]
  refine le_inf ?_ ?_
  · rw [eqB_comm (x := V.child i) (y := x)]
    exact inf_le_of_left_le inf_le_left
  · rw [eqB_comm (x := encodeLamB V N) (y := M)]
    exact inf_le_right

theorem lamInductiveB_app (V : AName.{u} A) :
    (⨅ M : AName.{u} A, memB M (lamB V) ⇨
      ⨅ N : AName.{u} A, memB N (lamB V) ⇨
        ⨆ p : AName.{u} A, memB p (lamB V) ⊓ eqB p (lamAppB M N)) = ⊤ := by
  refine iInf_eq_top.mpr fun M => himp_eq_top_iff.mpr ?_
  refine le_iInf fun N => ?_
  rw [le_himp_iff]
  rw [memB_lamB (z := M), memB_lamB (z := N), iSup_inf_eq]
  refine iSup_le fun M' => ?_
  rw [inf_iSup_eq]
  refine iSup_le fun N' => ?_
  refine le_iSup_of_le (encodeLamB V (Lam.app M' N')) ?_
  have hmem : memB (encodeLamB V (Lam.app M' N')) (lamB V) = ⊤ :=
    memB_encodeLamB V (Lam.app M' N')
  change _ ≤ memB (encodeLamB V (Lam.app M' N')) (lamB V) ⊓
    eqB (lamAppB (encodeLamB V M') (encodeLamB V N')) (lamAppB M N)
  rw [hmem, eqB_lamAppB, top_inf_eq]
  refine le_inf ?_ ?_
  · rw [eqB_comm (x := encodeLamB V M') (y := M)]
    exact inf_le_left
  · rw [eqB_comm (x := encodeLamB V N') (y := N)]
    exact inf_le_right

/-- `lamB V` satisfies the Example 21 clauses at Boolean value `1`. -/
theorem lamInductiveB_lamB (V : AName.{u} A) :
    lamInductiveB V (lamB V) = ⊤ := by
  rw [lamInductiveB]
  refine inf_eq_top_iff.mpr ⟨?varAbs, lamInductiveB_app V⟩
  exact inf_eq_top_iff.mpr ⟨lamInductiveB_var V, lamInductiveB_abs V⟩

/-!
## Leastness, following `check_omega_least`
-/

theorem lamInductiveB_parts {V X : AName.{u} A} (h : lamInductiveB V X = ⊤) :
    (⨅ x : AName.{u} A, memB x V ⇨
        ⨆ p : AName.{u} A, memB p X ⊓ eqB p (lamVarB x)) = ⊤ ∧
      (⨅ x : AName.{u} A, memB x V ⇨
        ⨅ M : AName.{u} A, memB M X ⇨
          ⨆ p : AName.{u} A, memB p X ⊓ eqB p (lamAbsB x M)) = ⊤ ∧
      (⨅ M : AName.{u} A, memB M X ⇨
        ⨅ N : AName.{u} A, memB N X ⇨
          ⨆ p : AName.{u} A, memB p X ⊓ eqB p (lamAppB M N)) = ⊤ := by
  have hsplit := inf_eq_top_iff.mp h
  exact ⟨(inf_eq_top_iff.mp hsplit.1).1, (inf_eq_top_iff.mp hsplit.1).2, hsplit.2⟩

theorem lamInductiveB_var_le {V X : AName.{u} A} (h : lamInductiveB V X = ⊤)
    (x : AName.{u} A) :
    memB x V ≤ ⨆ p : AName.{u} A, memB p X ⊓ eqB p (lamVarB x) :=
  himp_eq_top_iff.mp (iInf_eq_top.mp (lamInductiveB_parts h).1 x)

theorem lamInductiveB_abs_le {V X : AName.{u} A} (h : lamInductiveB V X = ⊤)
    (x M : AName.{u} A) :
    memB x V ⊓ memB M X ≤
      ⨆ p : AName.{u} A, memB p X ⊓ eqB p (lamAbsB x M) := by
  have hx : memB x V ≤
      ⨅ M' : AName.{u} A, memB M' X ⇨
        ⨆ p : AName.{u} A, memB p X ⊓ eqB p (lamAbsB x M') :=
    himp_eq_top_iff.mp (iInf_eq_top.mp (lamInductiveB_parts h).2.1 x)
  exact le_himp_iff.mp (hx.trans (iInf_le _ M))

theorem lamInductiveB_app_le {V X : AName.{u} A} (h : lamInductiveB V X = ⊤)
    (M N : AName.{u} A) :
    memB M X ⊓ memB N X ≤
      ⨆ p : AName.{u} A, memB p X ⊓ eqB p (lamAppB M N) := by
  have hM : memB M X ≤
      ⨅ N' : AName.{u} A, memB N' X ⇨
        ⨆ p : AName.{u} A, memB p X ⊓ eqB p (lamAppB M N') :=
    himp_eq_top_iff.mp (iInf_eq_top.mp (lamInductiveB_parts h).2.2 M)
  exact le_himp_iff.mp (hM.trans (iInf_le _ N))

/-- Every encoded term over `check Var` belongs to an inductive name, by
induction on `Lam` (the `check_omega_least` pattern). -/
theorem memB_encodeLamB_of_inductive (Var : PSet.{u}) {X : AName.{u} A}
    (h : lamInductiveB (check Var) X = ⊤)
    (M : Lam (check (A := A) Var).idx) :
    memB (encodeLamB (check Var) M) X = ⊤ := by
  induction M with
  | var x =>
    have hx : memB ((check (A := A) Var).child x) (check Var) = ⊤ :=
      memB_check_child (A := A) Var x
    have hex : (⨆ p : AName.{u} A,
        memB p X ⊓ eqB p (lamVarB ((check (A := A) Var).child x))) = ⊤ :=
      top_unique (hx.ge.trans (lamInductiveB_var_le h ((check Var).child x)))
    exact memB_of_exists_eqB X (lamVarB ((check (A := A) Var).child x)) hex
  | abs x M ih =>
    have hx : memB ((check (A := A) Var).child x) (check Var) = ⊤ :=
      memB_check_child (A := A) Var x
    have hex : (⨆ p : AName.{u} A,
        memB p X ⊓ eqB p (lamAbsB ((check (A := A) Var).child x)
          (encodeLamB (check Var) M))) = ⊤ :=
      top_unique ((le_inf hx.ge ih.ge).trans
        (lamInductiveB_abs_le h ((check Var).child x) (encodeLamB (check Var) M)))
    exact memB_of_exists_eqB X
      (lamAbsB ((check (A := A) Var).child x) (encodeLamB (check Var) M)) hex
  | app M N ihM ihN =>
    have hex : (⨆ p : AName.{u} A,
        memB p X ⊓ eqB p (lamAppB (encodeLamB (check Var) M)
          (encodeLamB (check Var) N))) = ⊤ :=
      top_unique ((le_inf ihM.ge ihN.ge).trans
        (lamInductiveB_app_le h (encodeLamB (check Var) M)
          (encodeLamB (check Var) N)))
    exact memB_of_exists_eqB X
      (lamAppB (encodeLamB (check Var) M) (encodeLamB (check Var) N)) hex

/-- Leastness of `Λ(check Var)^A`: if `X` is `Λ(check Var)`-inductive at
Boolean value 1, then `lamB (check Var) ⊆ X` at Boolean value 1. -/
theorem lamB_least {Var : PSet.{u}} {X : AName.{u} A}
    (h : lamInductiveB (check (A := A) Var) X = ⊤) :
    subsetB (lamB (check Var)) X = ⊤ := by
  rw [lamB, subsetB_mk]
  refine iInf_eq_top.mpr fun M => himp_eq_top_iff.mpr ?_
  exact (memB_encodeLamB_of_inductive (A := A) Var h M).ge

/-!
## Check commutation: `‖check (Λ(Var)) = lamB (check Var)‖ = 1`
-/

theorem check_encodeLam (Var : PSet.{u}) (M : Lam Var.Type) :
    eqB (check (A := A) (encodeLam Var.Func M))
      (encodeLamB
        (mk Var.Type (fun i => check (A := A) (Var.Func i)) (fun _ => ⊤)) M) =
      ⊤ := by
  induction M with
  | var x =>
    exact check_opair (A := A) (PSet.ofNat 0) (Var.Func x)
  | abs x M ih =>
    have hAB :=
      check_opair (A := A) (PSet.ofNat 1)
        (pOpair (Var.Func x) (encodeLam Var.Func M))
    have hinner := check_opair (A := A) (Var.Func x) (encodeLam Var.Func M)
    have hBC :=
      eqB_opairB_top (A := A) (eqB_self (check (PSet.ofNat 1))) hinner
    have hCD :=
      eqB_opairB_top (A := A) (eqB_self (check (PSet.ofNat 1)))
        (eqB_opairB_top (eqB_self (check (Var.Func x))) ih)
    exact eqB_top_trans (eqB_top_trans hAB hBC) hCD
  | app M N ihM ihN =>
    have hAB :=
      check_opair (A := A) (PSet.ofNat 2)
        (pOpair (encodeLam Var.Func M) (encodeLam Var.Func N))
    have hinner :=
      check_opair (A := A) (encodeLam Var.Func M) (encodeLam Var.Func N)
    have hBC :=
      eqB_opairB_top (A := A) (eqB_self (check (PSet.ofNat 2))) hinner
    have hCD :=
      eqB_opairB_top (A := A) (eqB_self (check (PSet.ofNat 2)))
        (eqB_opairB_top ihM ihN)
    exact eqB_top_trans (eqB_top_trans hAB hBC) hCD

/-- Proposition 22, check-equality: `‖check (Λ(Var)) = lamB (check Var)‖ = 1`. -/
theorem lamB_check_eq (Var : PSet.{u}) :
    eqB (check (A := A) (pLamSet Var)) (lamB (check Var)) = ⊤ := by
  rw [check_eq_mk (A := A) Var]
  change eqB
      (check (A := A) (PSet.mk (Lam Var.Type) (encodeLam Var.Func)))
      (lamB (mk Var.Type (fun i => check (A := A) (Var.Func i)) (fun _ => ⊤))) =
    ⊤
  rw [check_mk]
  exact eqB_mk_top _ _ fun M => check_encodeLam (A := A) Var M

end Scott2026
