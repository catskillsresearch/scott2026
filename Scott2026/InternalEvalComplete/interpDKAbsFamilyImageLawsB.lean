/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/

import Scott2026.InternalEvalComplete.interpDKAbsFamilyImageLawsA

namespace Scott2026

universe u

open AName InternalReflexiveModel

variable {A : Type u} [CompleteBooleanAlgebra A]
theorem interpDKAbsFamilyGraph_image_directed
    (𝓜 : InternalReflexiveModel (A := A))
    (V K : AName.{u} A) (hK : subsetB K 𝓜.D = ⊤)
    (hV : (oid V).IsTotal)
    (η : RelFun (oid V) (oid 𝓜.D))
    (y x : V.idx) (P : LamDK V.idx K.idx) (a : A)
    (hInner : ∀ d, a ≤ isScottContinuousB
      (interpDKBodyGraph 𝓜 V K hK hV (η.update hV 𝓜.total y d) x P)
      𝓜.D 𝓜.D 𝓜.R 𝓜.R)
    (hOuter : ∀ z, a ≤ isScottContinuousB
      (interpDKBodyGraph 𝓜 V K hK hV (η.update hV 𝓜.total x z) y P)
      𝓜.D 𝓜.D 𝓜.R 𝓜.R)
    (hInnerRows : ∀ d, ∀ e, IsRelElementAt 𝓜.D a
      (interpDKRelVal 𝓜 V K hK hV
        ((η.update hV 𝓜.total y d).update hV 𝓜.total x e) P))
    (hOuterRows : ∀ z, ∀ d, IsRelElementAt 𝓜.D a
      (interpDKRelVal 𝓜 V K hK hV
        ((η.update hV 𝓜.total x z).update hV 𝓜.total y d) P))
    (S : AName.{u} A) :
    ((oid V).eq x y)ᶜ ⊓ a ⊓ isDirectedRelB S 𝓜.D 𝓜.R ≤
      isDirectedRelB
        (graphImageB
          (interpDKAbsFamilyGraph 𝓜 V K hK hV η y x P) S 𝓜.C)
        𝓜.C 𝓜.Q :=
  isDirectedRelB_graphImageB
    (interpDKAbsFamilyGraph 𝓜 V K hK hV η y x P)
    S 𝓜.D 𝓜.C 𝓜.R 𝓜.Q
    (inf_le_right.trans
      (interpDKAbsFamilyGraph_le_isFunctionB 𝓜 V K hK hV η y x P a
        hInner))
    (fun u u' G G' =>
      interpDKAbsFamilyGraph_apply_mono 𝓜 V K hK hV η y x P a
        hInner hOuter hInnerRows hOuterRows u u' G G')

/-- A displayed inner graph is a `Q`-upper bound of the family image. -/
theorem interpDKAbsFamily_image_upper
    (𝓜 : InternalReflexiveModel (A := A))
    (V K : AName.{u} A) (hK : subsetB K 𝓜.D = ⊤)
    (hV : (oid V).IsTotal)
    (η : RelFun (oid V) (oid 𝓜.D))
    (y x : V.idx) (P : LamDK V.idx K.idx) (a : A)
    (hInner : ∀ d, a ≤ isScottContinuousB
      (interpDKBodyGraph 𝓜 V K hK hV (η.update hV 𝓜.total y d) x P)
      𝓜.D 𝓜.D 𝓜.R 𝓜.R)
    (hOuter : ∀ z, a ≤ isScottContinuousB
      (interpDKBodyGraph 𝓜 V K hK hV (η.update hV 𝓜.total x z) y P)
      𝓜.D 𝓜.D 𝓜.R 𝓜.R)
    (hInnerRows : ∀ d, ∀ e, IsRelElementAt 𝓜.D a
      (interpDKRelVal 𝓜 V K hK hV
        ((η.update hV 𝓜.total y d).update hV 𝓜.total x e) P))
    (hOuterRows : ∀ z, ∀ d, IsRelElementAt 𝓜.D a
      (interpDKRelVal 𝓜 V K hK hV
        ((η.update hV 𝓜.total x z).update hV 𝓜.total y d) P))
    (S : AName.{u} A) (d : 𝓜.D.idx) (G : AName.{u} A) :
    ((oid V).eq x y)ᶜ ⊓ a ⊓
        isUpperBoundRelB (𝓜.D.child d) S 𝓜.R ⊓
        memB G
          (graphImageB
            (interpDKAbsFamilyGraph 𝓜 V K hK hV η y x P) S 𝓜.C) ≤
      relB 𝓜.Q G
        (interpDKBodyGraph 𝓜 V K hK hV (η.update hV 𝓜.total y d) x P) := by
  let Fg := interpDKAbsFamilyGraph 𝓜 V K hK hV η y x P
  let Fd :=
    interpDKBodyGraph 𝓜 V K hK hV (η.update hV 𝓜.total y d) x P
  let t :=
    ((oid V).eq x y)ᶜ ⊓ a ⊓
      isUpperBoundRelB (𝓜.D.child d) S 𝓜.R ⊓
      memB G (graphImageB Fg S 𝓜.C)
  change t ≤ relB 𝓜.Q G Fd
  have htEq : t ≤ ((oid V).eq x y)ᶜ :=
    inf_le_left.trans (inf_le_left.trans inf_le_left)
  have htA : t ≤ a :=
    inf_le_left.trans (inf_le_left.trans inf_le_right)
  have htUb : t ≤ isUpperBoundRelB (𝓜.D.child d) S 𝓜.R :=
    inf_le_left.trans inf_le_right
  have htG : t ≤ memB G (graphImageB Fg S 𝓜.C) := inf_le_right
  rw [memB_graphImageB] at htG
  have htGC : t ≤ memB G 𝓜.C := htG.trans inf_le_left
  have hdec : t ≤ ⨆ w : AName A,
      memB w S ⊓ memB (opairB w G) Fg :=
    htG.trans inf_le_right
  refine (le_inf le_rfl hdec).trans ?_
  rw [inf_iSup_eq (α := A)]
  refine iSup_le fun w => ?_
  let s := t ⊓ (memB w S ⊓ memB (opairB w G) Fg)
  change s ≤ relB 𝓜.Q G Fd
  have hsT : s ≤ t := inf_le_left
  have hwS : s ≤ memB w S := inf_le_right.trans inf_le_left
  have hwG : s ≤ memB (opairB w G) Fg := inf_le_right.trans inf_le_right
  have hwd : s ≤ relB 𝓜.R w (𝓜.D.child d) :=
    (isUpperBoundRelB_apply (𝓜.D.child d) S 𝓜.R w).trans' <|
      le_inf (hsT.trans htUb) hwS
  have hFd : s ≤ memB (opairB (𝓜.D.child d) Fd) Fg :=
    le_top.trans (memB_interpDKAbsFamilyGraph_child
      𝓜 V K hK hV η y x P d).ge
  exact (interpDKAbsFamilyGraph_apply_mono 𝓜 V K hK hV η y x P a
      hInner hOuter hInnerRows hOuterRows w (𝓜.D.child d) G Fd).trans' <|
    le_inf (le_inf (le_inf (le_inf
        (hsT.trans htEq) (hsT.trans htA)) hwG) hFd) hwd

/-- Off-diagonal, a displayed inner value is the outer image-supremum. -/
theorem interpDKAbsFamily_inner_mapsToSup_outer
    (𝓜 : InternalReflexiveModel (A := A))
    (V K : AName.{u} A) (hK : subsetB K 𝓜.D = ⊤)
    (hV : (oid V).IsTotal)
    (η : RelFun (oid V) (oid 𝓜.D))
    (y x : V.idx) (P : LamDK V.idx K.idx) (a : A)
    (hOuter : ∀ z, a ≤ isScottContinuousB
      (interpDKBodyGraph 𝓜 V K hK hV (η.update hV 𝓜.total x z) y P)
      𝓜.D 𝓜.D 𝓜.R 𝓜.R)
    (hInnerRows : ∀ d, ∀ e, IsRelElementAt 𝓜.D a
      (interpDKRelVal 𝓜 V K hK hV
        ((η.update hV 𝓜.total y d).update hV 𝓜.total x e) P))
    (hOuterRows : ∀ z, ∀ d, IsRelElementAt 𝓜.D a
      (interpDKRelVal 𝓜 V K hK hV
        ((η.update hV 𝓜.total x z).update hV 𝓜.total y d) P))
    (S : AName.{u} A) (d e w : 𝓜.D.idx) :
    ((oid V).eq x y)ᶜ ⊓ a ⊓
        isDirectedRelB S 𝓜.D 𝓜.R ⊓
        isSupRelB (𝓜.D.child d) S 𝓜.R ⊓
        memB (opairB (𝓜.D.child e) (𝓜.D.child w))
          (interpDKBodyGraph 𝓜 V K hK hV
            (η.update hV 𝓜.total y d) x P) ≤
      mapsToSupB
        (interpDKBodyGraph 𝓜 V K hK hV (η.update hV 𝓜.total x e) y P)
        S (𝓜.D.child w) 𝓜.R := by
  let Fd :=
    interpDKBodyGraph 𝓜 V K hK hV (η.update hV 𝓜.total y d) x P
  let Ge :=
    interpDKBodyGraph 𝓜 V K hK hV (η.update hV 𝓜.total x e) y P
  let t :=
    ((oid V).eq x y)ᶜ ⊓ a ⊓
      isDirectedRelB S 𝓜.D 𝓜.R ⊓
      isSupRelB (𝓜.D.child d) S 𝓜.R ⊓
      memB (opairB (𝓜.D.child e) (𝓜.D.child w)) Fd
  change t ≤ mapsToSupB Ge S (𝓜.D.child w) 𝓜.R
  have htEq : t ≤ ((oid V).eq x y)ᶜ :=
    inf_le_left.trans (inf_le_left.trans
      (inf_le_left.trans inf_le_left))
  have htA : t ≤ a :=
    inf_le_left.trans (inf_le_left.trans
      (inf_le_left.trans inf_le_right))
  have htDir : t ≤ isDirectedRelB S 𝓜.D 𝓜.R :=
    inf_le_left.trans (inf_le_left.trans inf_le_right)
  have htSup : t ≤ isSupRelB (𝓜.D.child d) S 𝓜.R :=
    inf_le_left.trans inf_le_right
  have htmem : t ≤ memB (opairB (𝓜.D.child e) (𝓜.D.child w)) Fd :=
    inf_le_right
  have hGe : t ≤ memB (opairB (𝓜.D.child d) (𝓜.D.child w)) Ge :=
    (interpDKAbsFamily_inner_le_outer 𝓜 V K hK hV η y x P a
        hInnerRows hOuterRows d e w).trans' <|
      le_inf (le_inf htEq htA) htmem
  exact (scottContinuous_mapsToSup (hOuter e) S
      (𝓜.D.child d) (𝓜.D.child w)).trans' <|
    le_inf (le_inf (le_inf htA htDir) htSup) hGe

/-- Off-diagonal outer edges at a displayed source transport to inner
edges, for an arbitrary target name. -/
theorem interpDKAbsFamily_outer_mem_le_inner
    (𝓜 : InternalReflexiveModel (A := A))
    (V K : AName.{u} A) (hK : subsetB K 𝓜.D = ⊤)
    (hV : (oid V).IsTotal)
    (η : RelFun (oid V) (oid 𝓜.D))
    (y x : V.idx) (P : LamDK V.idx K.idx) (a : A)
    (hInnerRows : ∀ d, ∀ e, IsRelElementAt 𝓜.D a
      (interpDKRelVal 𝓜 V K hK hV
        ((η.update hV 𝓜.total y d).update hV 𝓜.total x e) P))
    (hOuter : ∀ z, a ≤ isScottContinuousB
      (interpDKBodyGraph 𝓜 V K hK hV (η.update hV 𝓜.total x z) y P)
      𝓜.D 𝓜.D 𝓜.R 𝓜.R)
    (hOuterRows : ∀ z, ∀ d, IsRelElementAt 𝓜.D a
      (interpDKRelVal 𝓜 V K hK hV
        ((η.update hV 𝓜.total x z).update hV 𝓜.total y d) P))
    (d e : 𝓜.D.idx) (w : AName.{u} A) :
    ((oid V).eq x y)ᶜ ⊓ a ⊓
        memB (opairB (𝓜.D.child d) w)
          (interpDKBodyGraph 𝓜 V K hK hV
            (η.update hV 𝓜.total x e) y P) ≤
      memB (opairB (𝓜.D.child e) w)
        (interpDKBodyGraph 𝓜 V K hK hV
          (η.update hV 𝓜.total y d) x P) := by
  let Ge :=
    interpDKBodyGraph 𝓜 V K hK hV (η.update hV 𝓜.total x e) y P
  let Fd :=
    interpDKBodyGraph 𝓜 V K hK hV (η.update hV 𝓜.total y d) x P
  let t :=
    ((oid V).eq x y)ᶜ ⊓ a ⊓ memB (opairB (𝓜.D.child d) w) Ge
  change t ≤ memB (opairB (𝓜.D.child e) w) Fd
  have htEq : t ≤ ((oid V).eq x y)ᶜ :=
    inf_le_left.trans inf_le_left
  have htA : t ≤ a := inf_le_left.trans inf_le_right
  have htmem : t ≤ memB (opairB (𝓜.D.child d) w) Ge := inf_le_right
  have hsub : t ≤ subsetB Ge (prodB 𝓜.D 𝓜.D) :=
    htA.trans ((hOuter e).trans
      ((inf_le_left.trans inf_le_left).trans
        (inf_le_left.trans inf_le_left)))
  have hdec :
      t ≤ ⨆ p : 𝓜.D.idx × 𝓜.D.idx,
        eqB (opairB (𝓜.D.child d) w)
          (opairB (𝓜.D.child p.1) (𝓜.D.child p.2)) ⊓
        memB (opairB (𝓜.D.child p.1) (𝓜.D.child p.2)) Ge :=
    (inf_memB_le_iSup_matrix (hsub := hsub)
        (opairB (𝓜.D.child d) w)).trans' <|
      le_inf le_rfl htmem
  refine (le_inf le_rfl hdec).trans ?_
  rw [inf_iSup_eq (α := A)]
  refine iSup_le fun p => ?_
  let s :=
    t ⊓
      (eqB (opairB (𝓜.D.child d) w)
        (opairB (𝓜.D.child p.1) (𝓜.D.child p.2)) ⊓
      memB (opairB (𝓜.D.child p.1) (𝓜.D.child p.2)) Ge)
  change s ≤ memB (opairB (𝓜.D.child e) w) Fd
  have hsT : s ≤ t := inf_le_left
  have hsp : s ≤
      memB (opairB (𝓜.D.child p.1) (𝓜.D.child p.2)) Ge :=
    inf_le_right.trans inf_le_right
  have hop : s ≤
      eqB (opairB (𝓜.D.child d) w)
        (opairB (𝓜.D.child p.1) (𝓜.D.child p.2)) :=
    inf_le_right.trans inf_le_left
  have hsrc : s ≤ eqB (𝓜.D.child d) (𝓜.D.child p.1) := by
    rw [eqB_opairB] at hop
    exact hop.trans inf_le_left
  have hout : s ≤ eqB w (𝓜.D.child p.2) := by
    rw [eqB_opairB] at hop
    exact hop.trans inf_le_right
  have hsame : s ≤
      memB (opairB (𝓜.D.child d) (𝓜.D.child p.2)) Ge :=
    (memB_opairB_congr Ge (𝓜.D.child p.1) (𝓜.D.child d)
        (𝓜.D.child p.2) (𝓜.D.child p.2)).trans' <|
      le_inf (le_inf
          (hsrc.trans_eq (eqB_comm (𝓜.D.child d) (𝓜.D.child p.1)))
          (le_top.trans (eqB_self (A := A) (𝓜.D.child p.2)).ge))
        hsp
  have hinner : s ≤
      memB (opairB (𝓜.D.child e) (𝓜.D.child p.2)) Fd :=
    (interpDKAbsFamily_outer_le_inner 𝓜 V K hK hV η y x P a
        hInnerRows hOuterRows d e p.2).trans' <|
      le_inf (le_inf (hsT.trans htEq) (hsT.trans htA)) hsame
  exact (memB_opairB_congr Fd (𝓜.D.child e) (𝓜.D.child e)
      (𝓜.D.child p.2) w).trans' <|
    le_inf (le_inf
        (le_top.trans (eqB_self (A := A) (𝓜.D.child e)).ge)
        (hout.trans_eq (eqB_comm w (𝓜.D.child p.2))))
      hinner

end Scott2026
