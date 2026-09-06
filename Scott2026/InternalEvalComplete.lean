/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/

import Scott2026.InternalEvalFamily

/-!
# Completion of internal evaluation

This module supplies the degree-local normalization of abstraction body
graphs, the directed-image calculus, fixed-argument evaluation, and the
pointwise-supremum graph of a directed family in `C`.
-/

universe u

namespace Scott2026

open AName

variable {A : Type u} [CompleteBooleanAlgebra A]

namespace IsRelElementAt

/-- A generalized element transports its coefficients along target equality. -/
theorem respects {D : AName.{u} A} {a : A} {r : D.idx → A}
    (h : IsRelElementAt D a r) (d e : D.idx) :
    (oid D).eq d e ⊓ r d ≤ r e :=
  h.1 d e

end IsRelElementAt

/-- At the active degree of all its rows, membership in an evaluator body
graph is normalized by its displayed coefficient. -/
theorem interpDKBodyGraph_mem_normalize
    (𝓜 : InternalReflexiveModel (A := A))
    (V K : AName.{u} A) (hK : subsetB K 𝓜.D = ⊤)
    (hV : (oid V).IsTotal)
    (η : RelFun (oid V) (oid 𝓜.D))
    (x : V.idx) (P : LamDK V.idx K.idx) (a : A)
    (hP : ∀ d, IsRelElementAt 𝓜.D a
      (interpDKRelVal 𝓜 V K hK hV
        (η.update hV 𝓜.total x d) P))
    (d e : 𝓜.D.idx) :
    interpDKRelVal 𝓜 V K hK hV
        (η.update hV 𝓜.total x d) P e ≤
      memB (opairB (𝓜.D.child d) (𝓜.D.child e))
        (interpDKBodyGraph 𝓜 V K hK hV η x P) ∧
    a ⊓ memB (opairB (𝓜.D.child d) (𝓜.D.child e))
        (interpDKBodyGraph 𝓜 V K hK hV η x P) ≤
      interpDKRelVal 𝓜 V K hK hV
        (η.update hV 𝓜.total x d) P e := by
  constructor
  · exact val_le_memB
      (interpDKBodyGraph 𝓜 V K hK hV η x P) (d, e)
  · unfold interpDKBodyGraph
    rw [memB_mk, inf_iSup_eq]
    refine iSup_le fun p => ?_
    rw [eqB_opairB]
    let r (q : 𝓜.D.idx) :=
      interpDKRelVal 𝓜 V K hK hV
        (η.update hV 𝓜.total x q) P
    let t := a ⊓
      ((eqB (𝓜.D.child d) (𝓜.D.child p.1) ⊓
        eqB (𝓜.D.child e) (𝓜.D.child p.2)) ⊓ r p.1 p.2)
    change t ≤ r d e
    have hsrc : t ≤ (oid 𝓜.D).eq p.1 d := by
      rw [oid_eq_of_total 𝓜.D 𝓜.total, eqB_comm]
      exact inf_le_right.trans (inf_le_left.trans inf_le_left)
    have hout : t ≤ (oid 𝓜.D).eq p.2 e := by
      rw [oid_eq_of_total 𝓜.D 𝓜.total, eqB_comm]
      exact inf_le_right.trans (inf_le_left.trans inf_le_right)
    have hval : t ≤ r p.1 p.2 := by
      exact inf_le_right.trans inf_le_right
    have hparam :
        (oid 𝓜.D).eq p.1 d ⊓ r p.1 p.2 ≤ r d p.2 := by
      exact interpDKRelVal_isPointwiseFamily 𝓜 V K hK hV
        (oid 𝓜.D)
        (fun q => η.update hV 𝓜.total x q)
        (RelFun.isPointwiseFamily_update η hV 𝓜.total x)
        P p.1 d p.2
    exact (hP d).respects p.2 e |>.trans' <|
      le_inf hout (hparam.trans' (le_inf hsrc hval))

/-- Equality form of `interpDKBodyGraph_mem_normalize`: the row hypothesis
also says that the raw coefficient is already supported by `a`. -/
theorem inf_memB_interpDKBodyGraph_eq
    (𝓜 : InternalReflexiveModel (A := A))
    (V K : AName.{u} A) (hK : subsetB K 𝓜.D = ⊤)
    (hV : (oid V).IsTotal)
    (η : RelFun (oid V) (oid 𝓜.D))
    (x : V.idx) (P : LamDK V.idx K.idx) (a : A)
    (hP : ∀ d, IsRelElementAt 𝓜.D a
      (interpDKRelVal 𝓜 V K hK hV
        (η.update hV 𝓜.total x d) P))
    (d e : 𝓜.D.idx) :
    a ⊓ memB (opairB (𝓜.D.child d) (𝓜.D.child e))
        (interpDKBodyGraph 𝓜 V K hK hV η x P) =
      interpDKRelVal 𝓜 V K hK hV
        (η.update hV 𝓜.total x d) P e := by
  apply le_antisymm
  · exact (interpDKBodyGraph_mem_normalize
      𝓜 V K hK hV η x P a hP d e).2
  · have hsupp :
        interpDKRelVal 𝓜 V K hK hV
            (η.update hV 𝓜.total x d) P e ≤ a :=
      ((hP d).2.1 e).trans inf_le_left
    exact le_inf hsupp
      (interpDKBodyGraph_mem_normalize
        𝓜 V K hK hV η x P a hP d e).1

/-- The internal image of `S` under a graph `F`, presented with the displayed
codomain of `E`.  Separation makes codomain membership explicit. -/
noncomputable def graphImageB
    (F S E : AName.{u} A) : AName.{u} A :=
  sepB E (fun y =>
    ⨆ x : AName.{u} A, memB x S ⊓ memB (opairB x y) F)

/-- Membership in the canonical graph image. -/
@[simp] theorem memB_graphImageB
    (F S E y : AName.{u} A) :
    memB y (graphImageB F S E) =
      memB y E ⊓
        ⨆ x : AName.{u} A, memB x S ⊓ memB (opairB x y) F := by
  unfold graphImageB
  apply memB_sepB
  intro y₁ y₂
  rw [inf_iSup_eq]
  refine iSup_le fun x => le_iSup_of_le x ?_
  refine le_inf (inf_le_right.trans inf_le_left) ?_
  exact (memB_opairB_congr F x x y₁ y₂).trans' <| by
    refine le_inf (le_inf ?_ ?_) ?_
    · exact le_top.trans (eqB_self (A := A) x).ge
    · exact inf_le_left
    · exact inf_le_right.trans inf_le_right

/-- The upper-bound projection of `mapsToSupB`. -/
theorem mapsToSupB_upper_apply
    (F S y Q x z : AName.{u} A) :
    mapsToSupB F S y Q ⊓ memB x S ⊓ memB (opairB x z) F ≤
      relB Q z y := by
  unfold mapsToSupB
  have hx := iInf_le
    (fun w : AName A => ⨅ v : AName A,
      memB w S ⊓ memB (opairB w v) F ⇨ relB Q v y) x
  have hz := (iInf_le
    (fun v : AName A =>
      memB x S ⊓ memB (opairB x v) F ⇨ relB Q v y) z).trans' hx
  refine (le_himp_iff.mp hz).trans' (le_inf ?_ ?_)
  · exact (inf_le_left.trans inf_le_left).trans inf_le_left
  · exact le_inf (inf_le_left.trans inf_le_right) inf_le_right

/-- The least-upper-bound projection of `mapsToSupB`. -/
theorem mapsToSupB_least_apply
    (F S y Q u : AName.{u} A) :
    mapsToSupB F S y Q ⊓
        (⨅ x : AName A, ⨅ z : AName A,
          memB x S ⊓ memB (opairB x z) F ⇨ relB Q z u) ≤
      relB Q y u := by
  unfold mapsToSupB
  have hu := iInf_le
    (fun v : AName A =>
      (⨅ x : AName A, ⨅ z : AName A,
        memB x S ⊓ memB (opairB x z) F ⇨ relB Q z v) ⇨
          relB Q y v) u
  refine (le_himp_iff.mp hu).trans' (le_inf ?_ inf_le_right)
  exact inf_le_left.trans inf_le_right

/-- Binary directedness applied to two members. -/
theorem isDirectedRelB_upper_apply
    (S D R x y : AName.{u} A) :
    isDirectedRelB S D R ⊓ memB x S ⊓ memB y S ≤
      ⨆ z : AName A,
        memB z S ⊓ relB R x z ⊓ relB R y z := by
  unfold isDirectedRelB
  have hx := iInf_le
    (fun u : AName A => ⨅ v : AName A,
      memB u S ⊓ memB v S ⇨
        ⨆ z : AName A,
          memB z S ⊓ relB R u z ⊓ relB R v z) x
  have hy := (iInf_le
    (fun v : AName A =>
      memB x S ⊓ memB v S ⇨
        ⨆ z : AName A,
          memB z S ⊓ relB R x z ⊓ relB R v z) y).trans' hx
  refine (le_himp_iff.mp hy).trans' (le_inf ?_ ?_)
  · exact (inf_le_left.trans inf_le_left).trans inf_le_right
  · exact le_inf (inf_le_left.trans inf_le_right) inf_le_right

/-- The value selected by an `a`-local function edge belongs to its
codomain at degree `a`. -/
theorem local_function_edge_le_codomain
    {a : A} {F D E : AName.{u} A}
    (hF : a ≤ isFunctionB F D E) (x y : AName.{u} A) :
    a ⊓ memB (opairB x y) F ≤ memB y E := by
  have hsub : a ≤ subsetB F (prodB D E) :=
    hF.trans (inf_le_left.trans inf_le_left)
  have hm := memB_of_subsetB (opairB x y) F (prodB D E)
  have hp : a ⊓ memB (opairB x y) F ≤
      memB (opairB x y) (prodB D E) :=
    hm.trans' (le_inf inf_le_right (inf_le_left.trans hsub))
  rw [memB_opairB_prodB] at hp
  exact hp.trans inf_le_right

/-- The source of an `a`-local function edge belongs to its domain. -/
theorem local_function_edge_le_domain
    {a : A} {F D E : AName.{u} A}
    (hF : a ≤ isFunctionB F D E) (x y : AName.{u} A) :
    a ⊓ memB (opairB x y) F ≤ memB x D := by
  have hsub : a ≤ subsetB F (prodB D E) :=
    hF.trans (inf_le_left.trans inf_le_left)
  have hm := memB_of_subsetB (opairB x y) F (prodB D E)
  have hp : a ⊓ memB (opairB x y) F ≤
      memB (opairB x y) (prodB D E) :=
    hm.trans' (le_inf inf_le_right (inf_le_left.trans hsub))
  rw [memB_opairB_prodB] at hp
  exact hp.trans inf_le_left

/-- If `F` maps the supremum of `S` to `y`, then `y` is the supremum of the
canonical image of `S`. -/
theorem mapsToSupB_le_isSup_graphImageB
    {a : A} (F S D E Q y : AName.{u} A)
    (hF : a ≤ isFunctionB F D E) :
    a ⊓ mapsToSupB F S y Q ≤
      isSupRelB y (graphImageB F S E) Q := by
  unfold isSupRelB
  refine le_inf ?_ ?_
  · unfold isUpperBoundRelB
    refine le_iInf fun (z : AName A) => ?_
    rw [le_himp_iff, memB_graphImageB, inf_iSup_eq (α := A)]
    rw [inf_iSup_eq]
    apply iSup_le
    intro x
    change (a ⊓ mapsToSupB F S y Q) ⊓
        (memB z E ⊓
          (memB x S ⊓ memB (opairB x z) F)) ≤ relB Q z y
    refine (mapsToSupB_upper_apply F S y Q x z).trans' ?_
    refine le_inf (le_inf ?_ ?_) ?_
    · exact inf_le_left.trans inf_le_right
    · exact inf_le_right.trans (inf_le_right.trans inf_le_left)
    · exact inf_le_right.trans (inf_le_right.trans inf_le_right)
  · refine le_iInf fun u => ?_
    rw [le_himp_iff]
    let upper :=
      ⨅ z : AName A, memB z (graphImageB F S E) ⇨ relB Q z u
    have hpoint :
        a ⊓ upper ≤
          ⨅ x : AName A, ⨅ z : AName A,
            memB x S ⊓ memB (opairB x z) F ⇨ relB Q z u := by
      refine le_iInf fun x => le_iInf fun z => ?_
      rw [le_himp_iff]
      have hzE :
          a ⊓ memB (opairB x z) F ≤ memB z E :=
        local_function_edge_le_codomain hF x z
      have hzImage :
          a ⊓ memB x S ⊓ memB (opairB x z) F ≤
            memB z (graphImageB F S E) := by
        rw [memB_graphImageB]
        refine le_inf ?_ ?_
        · exact hzE.trans' <| by
            exact le_inf (inf_le_left.trans inf_le_left) inf_le_right
        · refine le_iSup_of_le x ?_
          exact le_inf (inf_le_left.trans inf_le_right) inf_le_right
      have hu := iInf_le
        (fun v : AName A =>
          memB v (graphImageB F S E) ⇨ relB Q v u) z
      exact (le_himp_iff.mp hu).trans' <| le_inf
        (inf_le_left.trans inf_le_right)
        (hzImage.trans' <| le_inf
          (le_inf (inf_le_left.trans inf_le_left)
            (inf_le_right.trans inf_le_left))
          (inf_le_right.trans inf_le_right))
    exact (mapsToSupB_least_apply F S y Q u).trans' <|
      le_inf (inf_le_left.trans inf_le_right) <|
        hpoint.trans' <| le_inf
          (inf_le_left.trans inf_le_left) inf_le_right

/-- A degree-local function that is monotone on a locally directed set
sends that set to a locally directed canonical image. Scott continuity is
not required. -/
theorem isDirectedRelB_graphImageB
    {a : A} (F S D E R Q : AName.{u} A)
    (hF : a ≤ isFunctionB F D E)
    (hmono : ∀ x x' y y' : AName.{u} A,
      a ⊓ memB (opairB x y) F ⊓
        memB (opairB x' y') F ⊓ relB R x x' ≤
      relB Q y y') :
    a ⊓ isDirectedRelB S D R ≤
      isDirectedRelB (graphImageB F S E) E Q := by
  change a ⊓ isDirectedRelB S D R ≤
    (subsetB (graphImageB F S E) E ⊓
      (⨆ y : AName A, memB y (graphImageB F S E))) ⊓
      ⨅ y : AName A, ⨅ z : AName A,
        memB y (graphImageB F S E) ⊓
          memB z (graphImageB F S E) ⇨
            ⨆ v : AName A,
              memB v (graphImageB F S E) ⊓
                relB Q y v ⊓ relB Q z v
  refine le_inf (le_inf ?_ ?_) ?_
  · unfold graphImageB sepB
    rw [subsetB_mk]
    refine le_iInf fun i => ?_
    rw [le_himp_iff]
    exact (inf_le_right.trans inf_le_left).trans (val_le_memB E i)
  · have hnonempty :
        isDirectedRelB S D R ≤ ⨆ x : AName A, memB x S := by
      unfold isDirectedRelB
      exact inf_le_left.trans inf_le_right
    refine (le_inf le_rfl (inf_le_right.trans hnonempty)).trans ?_
    rw [inf_iSup_eq]
    refine iSup_le fun x => ?_
    have hxD :
        a ⊓ isDirectedRelB S D R ⊓ memB x S ≤ memB x D := by
      have hsub :
          isDirectedRelB S D R ≤ subsetB S D := by
        unfold isDirectedRelB
        exact inf_le_left.trans inf_le_left
      exact (memB_of_subsetB x S D).trans' <| le_inf
        inf_le_right ((inf_le_left.trans inf_le_right).trans hsub)
    have htotal :
        a ⊓ isDirectedRelB S D R ⊓ memB x S ≤
          ⨆ y : AName A, memB (opairB x y) F := by
      exact (isTotalB_apply F D x).trans' <| le_inf
        ((inf_le_left.trans inf_le_left).trans hF |>.trans
          inf_le_right)
        hxD
    refine (le_inf le_rfl htotal).trans ?_
    rw [inf_iSup_eq]
    refine iSup_le fun y => le_iSup_of_le y ?_
    rw [memB_graphImageB]
    have hyE :
        a ⊓ memB (opairB x y) F ≤ memB y E :=
      local_function_edge_le_codomain hF x y
    refine le_inf ?_ (le_iSup_of_le x ?_)
    · exact hyE.trans' <| le_inf
        (inf_le_left.trans (inf_le_left.trans inf_le_left)) inf_le_right
    · exact le_inf
        (inf_le_left.trans inf_le_right) inf_le_right
  · refine le_iInf fun y => le_iInf fun z => ?_
    rw [le_himp_iff, memB_graphImageB, memB_graphImageB]
    rw [inf_iSup_eq (α := A)]
    rw [← inf_assoc, inf_iSup_eq (α := A)]
    rw [iSup_inf_eq (α := A)]
    apply iSup_le
    intro x
    rw [inf_iSup_eq (α := A)]
    rw [inf_iSup_eq (α := A)]
    apply iSup_le
    intro x'
    let t :=
      (a ⊓ isDirectedRelB S D R ⊓
        (memB y E ⊓
          (memB x S ⊓ memB (opairB x y) F))) ⊓
        (memB z E ⊓
          (memB x' S ⊓ memB (opairB x' z) F))
    change t ≤ ⨆ v : AName A,
      memB v (graphImageB F S E) ⊓ relB Q y v ⊓ relB Q z v
    have hcommon :
        t ≤ ⨆ w : AName A,
          memB w S ⊓ relB R x w ⊓ relB R x' w := by
      exact (isDirectedRelB_upper_apply S D R x x').trans' <| by
        refine le_inf (le_inf ?_ ?_) ?_
        · exact inf_le_left.trans (inf_le_left.trans inf_le_right)
        · exact inf_le_left.trans
            (inf_le_right.trans (inf_le_right.trans inf_le_left))
        · exact inf_le_right.trans (inf_le_right.trans inf_le_left)
    refine (le_inf le_rfl hcommon).trans ?_
    rw [inf_iSup_eq]
    refine iSup_le fun w => ?_
    have hwD : t ⊓
        (memB w S ⊓ relB R x w ⊓ relB R x' w) ≤ memB w D := by
      have hsub :
          isDirectedRelB S D R ≤ subsetB S D := by
        unfold isDirectedRelB
        exact inf_le_left.trans inf_le_left
      exact (memB_of_subsetB w S D).trans' <| le_inf
        (inf_le_right.trans (inf_le_left.trans inf_le_left))
        ((inf_le_left.trans
          (inf_le_left.trans (inf_le_left.trans inf_le_right))).trans hsub)
    have hv :
        t ⊓ (memB w S ⊓ relB R x w ⊓ relB R x' w) ≤
          ⨆ v : AName A, memB (opairB w v) F := by
      exact (isTotalB_apply F D w).trans' <| le_inf
        ((inf_le_left.trans (inf_le_left.trans
          (inf_le_left.trans inf_le_left))).trans hF |>.trans
          inf_le_right)
        hwD
    refine (le_inf le_rfl hv).trans ?_
    rw [inf_iSup_eq]
    refine iSup_le fun v => le_iSup_of_le v ?_
    let twv :=
      (t ⊓ (memB w S ⊓ relB R x w ⊓ relB R x' w)) ⊓
        memB (opairB w v) F
    change twv ≤
      memB v (graphImageB F S E) ⊓ relB Q y v ⊓ relB Q z v
    have hvE : twv ≤ memB v E := by
      exact (local_function_edge_le_codomain hF w v).trans' <| le_inf
        (inf_le_left.trans (inf_le_left.trans (inf_le_left.trans
          (inf_le_left.trans inf_le_left)))) inf_le_right
    have hvImage : twv ≤ memB v (graphImageB F S E) := by
      rw [memB_graphImageB]
      refine le_inf hvE (le_iSup_of_le w ?_)
      exact le_inf
        (inf_le_left.trans
          (inf_le_right.trans (inf_le_left.trans inf_le_left))) inf_le_right
    have hyv : twv ≤ relB Q y v := by
      exact (hmono x w y v).trans' <| by
        refine le_inf (le_inf (le_inf ?_ ?_) ?_) ?_
        · exact inf_le_left.trans (inf_le_left.trans (inf_le_left.trans
            (inf_le_left.trans inf_le_left)))
        · exact inf_le_left.trans (inf_le_left.trans
            (inf_le_left.trans (inf_le_right.trans
              (inf_le_right.trans inf_le_right))))
        · exact inf_le_right
        · exact inf_le_left.trans
            (inf_le_right.trans (inf_le_left.trans inf_le_right))
    have hzv : twv ≤ relB Q z v := by
      exact (hmono x' w z v).trans' <| by
        refine le_inf (le_inf (le_inf ?_ ?_) ?_) ?_
        · exact inf_le_left.trans (inf_le_left.trans (inf_le_left.trans
            (inf_le_left.trans inf_le_left)))
        · exact inf_le_left.trans (inf_le_left.trans
            (inf_le_right.trans (inf_le_right.trans inf_le_right)))
        · exact inf_le_right
        · exact inf_le_left.trans
            (inf_le_right.trans inf_le_right)
    exact le_inf (le_inf hvImage hyv) hzv

/-- A compact bridge from Scott continuity at a source supremum to the
directed image and its displayed supremum. -/
theorem scottContinuous_image_sup
    {a : A} (F S D E R Q x y : AName.{u} A)
    (hF : a ≤ isScottContinuousB F D E R Q) :
    a ⊓ isDirectedRelB S D R ⊓ isSupRelB x S R ⊓
        memB (opairB x y) F ≤
      isDirectedRelB (graphImageB F S E) E Q ⊓
        isSupRelB y (graphImageB F S E) Q := by
  have hfun : a ≤ isFunctionB F D E :=
    hF.trans (inf_le_left.trans inf_le_left)
  refine le_inf ?_ ?_
  · exact (isDirectedRelB_graphImageB F S D E R Q hfun
        (fun u u' v v' => scottContinuous_apply_mono hF u u' v v')).trans' <| by
      exact le_inf (inf_le_left.trans (inf_le_left.trans inf_le_left))
        (inf_le_left.trans (inf_le_left.trans inf_le_right))
  · exact (mapsToSupB_le_isSup_graphImageB F S D E Q y hfun).trans' <|
      le_inf
        (inf_le_left.trans (inf_le_left.trans inf_le_left))
        (scottContinuous_mapsToSup hF S x y |>.trans' <| by
          apply le_of_eq
          ac_rfl)

/-- The slice of the verified evaluation graph at a fixed argument `x`.
An edge `(F, y)` means `F ∈ C` and `(x, y) ∈ F`, i.e. `y = F(x)`. -/
noncomputable def InternalReflexiveModel.evalAtGraph
    (𝓜 : InternalReflexiveModel (A := A)) (x : AName.{u} A) :
    AName.{u} A :=
  AName.mk (𝓜.C.idx × 𝓜.D.idx)
    (fun p => opairB (𝓜.C.child p.1) (𝓜.D.child p.2))
    (fun p =>
      memB (𝓜.C.child p.1) 𝓜.C ⊓
        memB (opairB x (𝓜.D.child p.2)) (𝓜.C.child p.1))

/-- On displayed children the slice recovers the verified `evalGraph`. -/
theorem InternalReflexiveModel.evalAtGraph_val_eq_memB_evalGraph
    (𝓜 : InternalReflexiveModel (A := A))
    (c : 𝓜.C.idx) (x y : 𝓜.D.idx) :
    (evalAtGraph 𝓜 (𝓜.D.child x)).val (c, y) =
      memB
        (opairB
          (opairB (𝓜.C.child c) (𝓜.D.child x))
          (𝓜.D.child y))
        𝓜.evalGraph := by
  unfold evalAtGraph
  exact (𝓜.memB_evalGraph_at c x y).symm

/-- Graph membership in the fixed-argument slice projects to evaluation. -/
theorem InternalReflexiveModel.memB_evalAtGraph_le
    (𝓜 : InternalReflexiveModel (A := A))
    (x F y : AName.{u} A) :
    memB (opairB F y) (evalAtGraph 𝓜 x) ≤
      memB F 𝓜.C ⊓ memB (opairB x y) F := by
  unfold InternalReflexiveModel.evalAtGraph
  rw [memB_mk]
  refine iSup_le fun p => ?_
  rw [eqB_opairB]
  let t :=
    (eqB F (𝓜.C.child p.1) ⊓ eqB y (𝓜.D.child p.2)) ⊓
      (memB (𝓜.C.child p.1) 𝓜.C ⊓
        memB (opairB x (𝓜.D.child p.2)) (𝓜.C.child p.1))
  change t ≤ memB F 𝓜.C ⊓ memB (opairB x y) F
  have hFC : t ≤ memB F 𝓜.C := by
    refine (memB_eqB_left (𝓜.C.child p.1) 𝓜.C F).trans' ?_
    refine le_inf (inf_le_right.trans inf_le_left) ?_
    rw [eqB_comm]
    exact inf_le_left.trans inf_le_left
  have hFy : t ≤ memB (opairB x y) F := by
    have hchild : t ≤ memB (opairB x y) (𝓜.C.child p.1) := by
      refine (memB_opairB_congr (𝓜.C.child p.1) x x
        (𝓜.D.child p.2) y).trans' ?_
      refine le_inf (le_inf ?_ ?_) ?_
      · exact le_top.trans (eqB_self (A := A) x).ge
      · rw [eqB_comm]
        exact inf_le_left.trans inf_le_right
      · exact inf_le_right.trans inf_le_right
    refine (memB_eqB_right (𝓜.C.child p.1) (opairB x y) F).trans' ?_
    refine le_inf hchild ?_
    rw [eqB_comm]
    exact inf_le_left.trans inf_le_left
  exact le_inf hFC hFy

/-- At the degree of its argument, fixed-argument evaluation is an
internal function `C → D`. -/
theorem InternalReflexiveModel.evalAtGraph_le_isFunctionB
    (𝓜 : InternalReflexiveModel (A := A))
    (x : AName.{u} A) :
    memB x 𝓜.D ≤ isFunctionB (evalAtGraph 𝓜 x) 𝓜.C 𝓜.D := by
  unfold isFunctionB
  refine le_inf (le_inf ?_ ?_) ?_
  · unfold evalAtGraph
    rw [subsetB_mk]
    refine le_iInf fun p => ?_
    rw [le_himp_iff, memB_opairB_prodB]
    let t :=
      memB x 𝓜.D ⊓
        (memB (𝓜.C.child p.1) 𝓜.C ⊓
          memB (opairB x (𝓜.D.child p.2)) (𝓜.C.child p.1))
    change t ≤
      memB (𝓜.C.child p.1) 𝓜.C ⊓ memB (𝓜.D.child p.2) 𝓜.D
    refine le_inf (inf_le_right.trans inf_le_left) ?_
    have hfun :
        memB (𝓜.C.child p.1) 𝓜.C ≤
          isFunctionB (𝓜.C.child p.1) 𝓜.D 𝓜.D :=
      𝓜.mem_mapSpace_le_function (𝓜.C.child p.1)
    have hsub :
        memB (𝓜.C.child p.1) 𝓜.C ≤
          subsetB (𝓜.C.child p.1) (prodB 𝓜.D 𝓜.D) :=
      hfun.trans (inf_le_left.trans inf_le_left)
    have hm : t ≤
        memB (opairB x (𝓜.D.child p.2)) (prodB 𝓜.D 𝓜.D) :=
      (memB_of_subsetB
        (opairB x (𝓜.D.child p.2))
        (𝓜.C.child p.1) (prodB 𝓜.D 𝓜.D)).trans' <|
        le_inf (inf_le_right.trans inf_le_right)
          (inf_le_right.trans (inf_le_left.trans hsub))
    rw [memB_opairB_prodB] at hm
    exact hm.trans inf_le_right
  · refine le_iInf fun F => le_iInf fun y => le_iInf fun z => ?_
    rw [le_himp_iff]
    let t :=
      memB x 𝓜.D ⊓
        (memB (opairB F y) (evalAtGraph 𝓜 x) ⊓
          memB (opairB F z) (evalAtGraph 𝓜 x))
    change t ≤ eqB y z
    have hy : t ≤ memB F 𝓜.C ⊓ memB (opairB x y) F :=
      (𝓜.memB_evalAtGraph_le x F y).trans' <|
        inf_le_right.trans inf_le_left
    have hz : t ≤ memB F 𝓜.C ⊓ memB (opairB x z) F :=
      (𝓜.memB_evalAtGraph_le x F z).trans' <|
        inf_le_right.trans inf_le_right
    have hfun : t ≤ isFunctionB F 𝓜.D 𝓜.D :=
      (𝓜.mem_mapSpace_le_function F).trans' (hy.trans inf_le_left)
    exact (isSingleValuedB_apply F x y z).trans' <|
      le_inf (le_inf (hfun.trans (inf_le_left.trans inf_le_right))
        (hy.trans inf_le_right))
        (hz.trans inf_le_right)
  · refine le_iInf fun F => ?_
    rw [le_himp_iff]
    have hfunF : memB F 𝓜.C ≤ isFunctionB F 𝓜.D 𝓜.D :=
      𝓜.mem_mapSpace_le_function F
    have htot :
        memB x 𝓜.D ⊓ memB F 𝓜.C ≤
          ⨆ y : AName A, memB (opairB x y) F :=
      (isTotalB_apply F 𝓜.D x).trans' <| le_inf
        ((inf_le_right.trans hfunF).trans inf_le_right) inf_le_left
    refine (le_inf le_rfl htot).trans ?_
    rw [inf_iSup_eq]
    refine iSup_le fun y => ?_
    have hsub : memB F 𝓜.C ≤ subsetB F (prodB 𝓜.D 𝓜.D) :=
      hfunF.trans (inf_le_left.trans inf_le_left)
    have hyd :
        (memB x 𝓜.D ⊓ memB F 𝓜.C) ⊓ memB (opairB x y) F ≤
          ⨆ d : 𝓜.D.idx, memB (opairB x (𝓜.D.child d)) F :=
      (inf_memB_opairB_le_iSup_child hsub x y).trans' <|
        le_inf (inf_le_left.trans inf_le_right) inf_le_right
    refine (le_inf le_rfl hyd).trans ?_
    rw [inf_iSup_eq]
    refine iSup_le fun d => le_iSup_of_le (𝓜.D.child d) ?_
    let t :=
      ((memB x 𝓜.D ⊓ memB F 𝓜.C) ⊓ memB (opairB x y) F) ⊓
        memB (opairB x (𝓜.D.child d)) F
    change t ≤ memB (opairB F (𝓜.D.child d)) (evalAtGraph 𝓜 x)
    have hFC : t ≤ memB F 𝓜.C :=
      inf_le_left.trans (inf_le_left.trans inf_le_right)
    have hFd : t ≤ memB (opairB x (𝓜.D.child d)) F := inf_le_right
    refine (le_inf hFC hFd).trans ?_
    rw [memB_eq (x := F) (y := 𝓜.C), iSup_inf_eq]
    refine iSup_le fun c => ?_
    unfold InternalReflexiveModel.evalAtGraph
    rw [memB_mk]
    refine le_iSup_of_le (c, d) ?_
    rw [eqB_opairB, eqB_self, inf_top_eq]
    let s :=
      (eqB F (𝓜.C.child c) ⊓ (𝓜.C.val c)) ⊓
        memB (opairB x (𝓜.D.child d)) F
    change s ≤
      eqB F (𝓜.C.child c) ⊓
        (memB (𝓜.C.child c) 𝓜.C ⊓
          memB (opairB x (𝓜.D.child d)) (𝓜.C.child c))
    refine le_inf (inf_le_left.trans inf_le_left) (le_inf ?_ ?_)
    · exact (val_le_memB 𝓜.C c).trans' (inf_le_left.trans inf_le_right)
    · exact (memB_eqB_right F (opairB x (𝓜.D.child d))
        (𝓜.C.child c)).trans' <|
          le_inf inf_le_right (inf_le_left.trans inf_le_left)

/-- Fixed-argument evaluation is monotone from `(C, Q)` to `(D, R)` by
the pointwise comparison `relQ_apply`. -/
theorem InternalReflexiveModel.evalAtGraph_apply_mono
    (𝓜 : InternalReflexiveModel (A := A))
    (x F G y z : AName.{u} A) :
    memB x 𝓜.D ⊓
        memB (opairB F y) (evalAtGraph 𝓜 x) ⊓
        memB (opairB G z) (evalAtGraph 𝓜 x) ⊓
        relB 𝓜.Q F G ≤
      relB 𝓜.R y z := by
  have hF : memB (opairB F y) (evalAtGraph 𝓜 x) ≤
      memB F 𝓜.C ⊓ memB (opairB x y) F :=
    𝓜.memB_evalAtGraph_le x F y
  have hG : memB (opairB G z) (evalAtGraph 𝓜 x) ≤
      memB G 𝓜.C ⊓ memB (opairB x z) G :=
    𝓜.memB_evalAtGraph_le x G z
  exact (𝓜.relQ_apply F G x y z).trans' <| by
    refine le_inf (le_inf (le_inf ?_ ?_) ?_)
      (le_inf (le_inf ?_ ?_) ?_)
    · exact inf_le_left.trans (inf_le_left.trans inf_le_right) |>.trans
        (hF.trans inf_le_left)
    · exact inf_le_left.trans inf_le_right |>.trans (hG.trans inf_le_left)
    · exact inf_le_right
    · exact inf_le_left.trans (inf_le_left.trans inf_le_left)
    · exact inf_le_left.trans (inf_le_left.trans inf_le_right) |>.trans
        (hF.trans inf_le_right)
    · exact inf_le_left.trans inf_le_right |>.trans (hG.trans inf_le_right)

/-- The image of a locally directed subset of `C` under evaluation at a
fixed argument is locally directed in `D`. -/
theorem InternalReflexiveModel.evalAtGraph_image_directed
    (𝓜 : InternalReflexiveModel (A := A))
    {a : A} (x S : AName.{u} A)
    (hx : a ≤ memB x 𝓜.D) :
    a ⊓ isDirectedRelB S 𝓜.C 𝓜.Q ≤
      isDirectedRelB (graphImageB (evalAtGraph 𝓜 x) S 𝓜.D) 𝓜.D 𝓜.R :=
  isDirectedRelB_graphImageB
    (evalAtGraph 𝓜 x) S 𝓜.C 𝓜.D 𝓜.Q 𝓜.R
    (hx.trans (𝓜.evalAtGraph_le_isFunctionB x))
    (fun F G y z =>
      (𝓜.evalAtGraph_apply_mono x F G y z).trans' <| by
        refine le_inf (le_inf (le_inf ?_ ?_) ?_) ?_
        · exact inf_le_left.trans (inf_le_left.trans
            (inf_le_left.trans hx))
        · exact inf_le_left.trans (inf_le_left.trans inf_le_right)
        · exact inf_le_left.trans inf_le_right
        · exact inf_le_right)

/-- An upper bound applied to a member of the set. -/
theorem isUpperBoundRelB_apply
    (x S R y : AName.{u} A) :
    isUpperBoundRelB x S R ⊓ memB y S ≤ relB R y x :=
  le_himp_iff.mp (iInf_le
    (fun z : AName A => memB z S ⇨ relB R z x) y)

/-- A supremum is below every upper bound. -/
theorem isSupRelB_least
    (x S R y : AName.{u} A) :
    isSupRelB x S R ⊓ isUpperBoundRelB y S R ≤ relB R x y := by
  unfold isSupRelB
  exact (le_himp_iff.mp (iInf_le
    (fun z : AName A =>
      isUpperBoundRelB z S R ⇨ relB R x z) y)).trans' <|
    le_inf (inf_le_left.trans inf_le_right) inf_le_right

/-- Upper bounds transport along equality of the bound. -/
theorem isUpperBoundRelB_congr
    (x x' S R : AName.{u} A) :
    eqB x x' ⊓ isUpperBoundRelB x S R ≤ isUpperBoundRelB x' S R := by
  refine le_iInf fun y => ?_
  rw [le_himp_iff]
  exact (relB_congr R y y x x').trans' <| by
    refine le_inf (le_inf ?_ ?_) ?_
    · exact le_top.trans (eqB_self (A := A) y).ge
    · exact inf_le_left.trans inf_le_left
    · exact (isUpperBoundRelB_apply x S R y).trans' <|
        le_inf (inf_le_left.trans inf_le_right) inf_le_right

/-- Suprema transport along equality of the realizing name. -/
theorem isSupRelB_congr
    (x x' S R : AName.{u} A) :
    eqB x x' ⊓ isSupRelB x S R ≤ isSupRelB x' S R := by
  unfold isSupRelB
  refine le_inf ?_ ?_
  · exact (isUpperBoundRelB_congr x x' S R).trans' <|
      le_inf inf_le_left (inf_le_right.trans inf_le_left)
  · refine le_iInf fun y => ?_
    rw [le_himp_iff]
    exact (relB_congr R x x' y y).trans' <| by
      refine le_inf (le_inf (inf_le_left.trans inf_le_left) ?_) ?_
      · exact le_top.trans (eqB_self (A := A) y).ge
      · exact (isSupRelB_least x S R y).trans' <|
          le_inf (inf_le_left.trans inf_le_right) inf_le_right

/-- Upper bounds transport along equality of the set. -/
theorem isUpperBoundRelB_congr_set
    (x S S' R : AName.{u} A) :
    eqB S S' ⊓ isUpperBoundRelB x S R ≤ isUpperBoundRelB x S' R := by
  refine le_iInf fun y => ?_
  rw [le_himp_iff]
  exact (isUpperBoundRelB_apply x S R y).trans' <|
    le_inf (inf_le_left.trans inf_le_right)
      ((memB_eqB_right S' y S).trans' <|
        le_inf inf_le_right (by
          rw [eqB_comm]
          exact inf_le_left.trans inf_le_left))

/-- Suprema transport along equality of the set. -/
theorem isSupRelB_congr_set
    (x S S' R : AName.{u} A) :
    eqB S S' ⊓ isSupRelB x S R ≤ isSupRelB x S' R := by
  unfold isSupRelB
  refine le_inf ?_ ?_
  · exact (isUpperBoundRelB_congr_set x S S' R).trans' <|
      le_inf inf_le_left (inf_le_right.trans inf_le_left)
  · refine le_iInf fun y => ?_
    rw [le_himp_iff]
    exact (isSupRelB_least x S R y).trans' <|
      le_inf (inf_le_left.trans inf_le_right)
        ((isUpperBoundRelB_congr_set y S' S R).trans' <|
          le_inf (by rw [eqB_comm]; exact inf_le_left.trans inf_le_left)
            inf_le_right)

/-- Simultaneous transport of a supremum in the realizing name and the set. -/
theorem isSupRelB_congr_pair
    (x x' S S' R : AName.{u} A) :
    eqB x x' ⊓ eqB S S' ⊓ isSupRelB x S R ≤ isSupRelB x' S' R :=
  (isSupRelB_congr x x' S' R).trans' <|
    le_inf (inf_le_left.trans inf_le_left)
      ((isSupRelB_congr_set x S S' R).trans' <|
        le_inf (inf_le_left.trans inf_le_right) inf_le_right)

/-- The dcpo existence predicate is congruent, as required by fullness. -/
theorem mem_isSupRelB_congr
    (D S R d e : AName.{u} A) :
    eqB d e ⊓ (memB d D ⊓ isSupRelB d S R) ≤
      memB e D ⊓ isSupRelB e S R :=
  le_inf
    ((memB_eqB_left d D e).trans' <|
      le_inf (inf_le_right.trans inf_le_left) inf_le_left)
    ((isSupRelB_congr d e S R).trans' <|
      le_inf inf_le_left (inf_le_right.trans inf_le_right))

/-- Canonical images transport along equality of the acting graph. -/
theorem eqB_graphImageB
    (F F' S E : AName.{u} A) :
    eqB F F' ≤ eqB (graphImageB F S E) (graphImageB F' S E) := by
  unfold graphImageB sepB
  refine le_eqB_mk_of_le_val (I := E.idx) E.child
    (fun i => E.val i ⊓
      ⨆ x : AName.{u} A, memB x S ⊓ memB (opairB x (E.child i)) F)
    (fun i => E.val i ⊓
      ⨆ x : AName.{u} A, memB x S ⊓ memB (opairB x (E.child i)) F')
    (eqB F F') ?_ ?_
  · intro i
    refine le_inf (inf_le_right.trans inf_le_left) ?_
    refine (le_inf inf_le_left (inf_le_right.trans inf_le_right)).trans ?_
    rw [inf_iSup_eq (α := A)]
    refine iSup_le fun x => le_iSup_of_le x ?_
    refine le_inf (inf_le_right.trans inf_le_left) ?_
    exact (memB_eqB_right F (opairB x (E.child i)) F').trans' <|
      le_inf (inf_le_right.trans inf_le_right) inf_le_left
  · intro i
    refine le_inf (inf_le_right.trans inf_le_left) ?_
    refine (le_inf inf_le_left (inf_le_right.trans inf_le_right)).trans ?_
    rw [inf_iSup_eq (α := A)]
    refine iSup_le fun x => le_iSup_of_le x ?_
    refine le_inf (inf_le_right.trans inf_le_left) ?_
    exact (memB_eqB_right F' (opairB x (E.child i)) F).trans' <|
      le_inf (inf_le_right.trans inf_le_right)
        (by rw [eqB_comm]; exact inf_le_left)

/-- Fixed-argument evaluation graphs transport along equality of the argument. -/
theorem InternalReflexiveModel.evalAtGraph_congr
    (𝓜 : InternalReflexiveModel (A := A))
    (x x' : AName.{u} A) :
    eqB x x' ≤ eqB (evalAtGraph 𝓜 x) (evalAtGraph 𝓜 x') := by
  unfold InternalReflexiveModel.evalAtGraph
  refine le_eqB_mk_of_le_val (I := 𝓜.C.idx × 𝓜.D.idx)
    (fun p : 𝓜.C.idx × 𝓜.D.idx =>
      opairB (𝓜.C.child p.1) (𝓜.D.child p.2))
    (fun p : 𝓜.C.idx × 𝓜.D.idx =>
      memB (𝓜.C.child p.1) 𝓜.C ⊓
        memB (opairB x (𝓜.D.child p.2)) (𝓜.C.child p.1))
    (fun p : 𝓜.C.idx × 𝓜.D.idx =>
      memB (𝓜.C.child p.1) 𝓜.C ⊓
        memB (opairB x' (𝓜.D.child p.2)) (𝓜.C.child p.1))
    (eqB x x') ?_ ?_
  · intro p
    refine le_inf (inf_le_right.trans inf_le_left) ?_
    refine (memB_opairB_congr (𝓜.C.child p.1) x x'
        (𝓜.D.child p.2) (𝓜.D.child p.2)).trans' ?_
    refine le_inf (le_inf inf_le_left ?_)
      (inf_le_right.trans inf_le_right)
    exact le_top.trans (eqB_self (A := A) (𝓜.D.child p.2)).ge
  · intro p
    refine le_inf (inf_le_right.trans inf_le_left) ?_
    refine (memB_opairB_congr (𝓜.C.child p.1) x' x
        (𝓜.D.child p.2) (𝓜.D.child p.2)).trans' ?_
    refine le_inf (le_inf ?_ ?_)
      (inf_le_right.trans inf_le_right)
    · rw [eqB_comm]
      exact inf_le_left
    · exact le_top.trans (eqB_self (A := A) (𝓜.D.child p.2)).ge

/-- Evaluation images transport along equality of the argument. -/
theorem InternalReflexiveModel.eqB_evalAtGraph_image
    (𝓜 : InternalReflexiveModel (A := A))
    (x x' S : AName.{u} A) :
    eqB x x' ≤
      eqB (graphImageB (evalAtGraph 𝓜 x) S 𝓜.D)
        (graphImageB (evalAtGraph 𝓜 x') S 𝓜.D) :=
  (eqB_graphImageB (evalAtGraph 𝓜 x) (evalAtGraph 𝓜 x') S 𝓜.D).trans'
    (𝓜.evalAtGraph_congr x x')

/-- Antisymmetry of the internally valid order on `D`. -/
theorem InternalReflexiveModel.relR_antisymm
    (𝓜 : InternalReflexiveModel (A := A))
    (x y : AName.{u} A) :
    memB x 𝓜.D ⊓ memB y 𝓜.D ⊓
        relB 𝓜.R x y ⊓ relB 𝓜.R y x ≤
      eqB x y := by
  have hdc := 𝓜.dcpo_valid
  unfold isDcpoWithBottomB at hdc
  have hpo := (inf_eq_top_iff.mp (inf_eq_top_iff.mp hdc).1).1
  unfold isPartialOrderB at hpo
  have hanti := (inf_eq_top_iff.mp (inf_eq_top_iff.mp hpo).1).2
  have hx := iInf_eq_top.mp hanti x
  exact himp_eq_top_iff.mp (iInf_eq_top.mp hx y)

/-- Directed subsets of the internally valid dcpo have a supremum. -/
theorem InternalReflexiveModel.dcpo_directed_has_sup
    (𝓜 : InternalReflexiveModel (A := A))
    (S : AName.{u} A) :
    isDirectedRelB S 𝓜.D 𝓜.R ≤
      ⨆ d : AName.{u} A, memB d 𝓜.D ⊓ isSupRelB d S 𝓜.R := by
  have hdc := 𝓜.dcpo_valid
  unfold isDcpoWithBottomB at hdc
  exact himp_eq_top_iff.mp
    (iInf_eq_top.mp (inf_eq_top_iff.mp hdc).2 S)

/-- Suprema in a partial order are unique. -/
theorem InternalReflexiveModel.isSupRelB_unique
    (𝓜 : InternalReflexiveModel (A := A))
    (x y S : AName.{u} A) :
    memB x 𝓜.D ⊓ memB y 𝓜.D ⊓
        isSupRelB x S 𝓜.R ⊓ isSupRelB y S 𝓜.R ≤
      eqB x y := by
  have hxy :
      isSupRelB x S 𝓜.R ⊓ isSupRelB y S 𝓜.R ≤ relB 𝓜.R x y :=
    (isSupRelB_least x S 𝓜.R y).trans' <|
      le_inf inf_le_left (inf_le_right.trans inf_le_left)
  have hyx :
      isSupRelB x S 𝓜.R ⊓ isSupRelB y S 𝓜.R ≤ relB 𝓜.R y x :=
    (isSupRelB_least y S 𝓜.R x).trans' <|
      le_inf inf_le_right (inf_le_left.trans inf_le_left)
  exact (𝓜.relR_antisymm x y).trans' <| by
    refine le_inf (le_inf (le_inf ?_ ?_) ?_) ?_
    · exact inf_le_left.trans (inf_le_left.trans inf_le_left)
    · exact inf_le_left.trans (inf_le_left.trans inf_le_right)
    · exact hxy.trans' <|
        le_inf (inf_le_left.trans inf_le_right) inf_le_right
    · exact hyx.trans' <|
        le_inf (inf_le_left.trans inf_le_right) inf_le_right

/-- The graph of pointwise directed suprema of evaluation images: an edge
`(D.child i, D.child j)` means `D.child j` is an `R`-supremum of the
canonical image of `S` under evaluation at `D.child i`. -/
noncomputable def InternalReflexiveModel.pointwiseSupGraph
    (𝓜 : InternalReflexiveModel (A := A)) (S : AName.{u} A) :
    AName.{u} A :=
  AName.mk (𝓜.D.idx × 𝓜.D.idx)
    (fun p => opairB (𝓜.D.child p.1) (𝓜.D.child p.2))
    (fun p =>
      memB (𝓜.D.child p.1) 𝓜.D ⊓
        isSupRelB (𝓜.D.child p.2)
          (graphImageB (evalAtGraph 𝓜 (𝓜.D.child p.1)) S 𝓜.D)
          𝓜.R)

/-- Graph membership implies the semantic supremum statement, with
codomain support. -/
theorem InternalReflexiveModel.memB_pointwiseSupGraph_le
    (𝓜 : InternalReflexiveModel (A := A))
    (S x y : AName.{u} A) :
    memB (opairB x y) (pointwiseSupGraph 𝓜 S) ≤
      memB x 𝓜.D ⊓ memB y 𝓜.D ⊓
        isSupRelB y (graphImageB (evalAtGraph 𝓜 x) S 𝓜.D) 𝓜.R := by
  unfold InternalReflexiveModel.pointwiseSupGraph
  rw [memB_mk]
  refine iSup_le fun p => ?_
  rw [eqB_opairB]
  let t :=
    (eqB x (𝓜.D.child p.1) ⊓ eqB y (𝓜.D.child p.2)) ⊓
      (memB (𝓜.D.child p.1) 𝓜.D ⊓
        isSupRelB (𝓜.D.child p.2)
          (graphImageB (evalAtGraph 𝓜 (𝓜.D.child p.1)) S 𝓜.D)
          𝓜.R)
  change t ≤
    memB x 𝓜.D ⊓ memB y 𝓜.D ⊓
      isSupRelB y (graphImageB (evalAtGraph 𝓜 x) S 𝓜.D) 𝓜.R
  have hxD : t ≤ memB x 𝓜.D := by
    refine (memB_eqB_left (𝓜.D.child p.1) 𝓜.D x).trans' ?_
    refine le_inf (inf_le_right.trans inf_le_left) ?_
    rw [eqB_comm]
    exact inf_le_left.trans inf_le_left
  have hyD : t ≤ memB y 𝓜.D := by
    have hj : memB (𝓜.D.child p.2) 𝓜.D = ⊤ := by
      rw [← oid_eps]
      exact 𝓜.total p.2
    refine (memB_eqB_left (𝓜.D.child p.2) 𝓜.D y).trans' ?_
    refine le_inf (le_top.trans hj.ge) ?_
    rw [eqB_comm]
    exact inf_le_left.trans inf_le_right
  have hsup :
      t ≤ isSupRelB y (graphImageB (evalAtGraph 𝓜 x) S 𝓜.D) 𝓜.R := by
    refine (isSupRelB_congr_pair (𝓜.D.child p.2) y
        (graphImageB (evalAtGraph 𝓜 (𝓜.D.child p.1)) S 𝓜.D)
        (graphImageB (evalAtGraph 𝓜 x) S 𝓜.D)
        𝓜.R).trans' ?_
    refine le_inf (le_inf ?_ ?_) (inf_le_right.trans inf_le_right)
    · rw [eqB_comm]
      exact inf_le_left.trans inf_le_right
    · exact (𝓜.eqB_evalAtGraph_image (𝓜.D.child p.1) x S).trans'
        (by rw [eqB_comm]; exact inf_le_left.trans inf_le_left)
  exact le_inf (le_inf hxD hyD) hsup

/-- The semantic supremum statement, with source and target support, implies
graph membership. -/
theorem InternalReflexiveModel.le_memB_pointwiseSupGraph
    (𝓜 : InternalReflexiveModel (A := A))
    (S x y : AName.{u} A) :
    memB x 𝓜.D ⊓ memB y 𝓜.D ⊓
        isSupRelB y (graphImageB (evalAtGraph 𝓜 x) S 𝓜.D) 𝓜.R ≤
      memB (opairB x y) (pointwiseSupGraph 𝓜 S) := by
  rw [memB_eq (x := x) (y := 𝓜.D), inf_assoc, iSup_inf_eq]
  refine iSup_le fun i => ?_
  rw [memB_eq (x := y) (y := 𝓜.D)]
  refine (le_inf
      (le_inf inf_le_left (inf_le_right.trans inf_le_right))
      (inf_le_right.trans inf_le_left)).trans ?_
  rw [inf_iSup_eq (α := A)]
  refine iSup_le fun j => ?_
  let u :=
    (eqB x (𝓜.D.child i) ⊓ 𝓜.D.val i) ⊓
      isSupRelB y (graphImageB (evalAtGraph 𝓜 x) S 𝓜.D) 𝓜.R ⊓
      (eqB y (𝓜.D.child j) ⊓ 𝓜.D.val j)
  change u ≤ memB (opairB x y) (pointwiseSupGraph 𝓜 S)
  unfold InternalReflexiveModel.pointwiseSupGraph
  rw [memB_mk]
  refine le_iSup_of_le (i, j) ?_
  rw [eqB_opairB]
  refine le_inf (le_inf ?_ ?_) (le_inf ?_ ?_)
  · exact inf_le_left.trans (inf_le_left.trans inf_le_left)
  · exact inf_le_right.trans inf_le_left
  · exact (val_le_memB 𝓜.D i).trans' <|
      inf_le_left.trans (inf_le_left.trans inf_le_right)
  · refine (isSupRelB_congr_pair y (𝓜.D.child j)
        (graphImageB (evalAtGraph 𝓜 x) S 𝓜.D)
        (graphImageB (evalAtGraph 𝓜 (𝓜.D.child i)) S 𝓜.D)
        𝓜.R).trans' ?_
    refine le_inf (le_inf ?_ ?_) (inf_le_left.trans inf_le_right)
    · exact inf_le_right.trans inf_le_left
    · exact (𝓜.eqB_evalAtGraph_image x (𝓜.D.child i) S).trans' <|
        inf_le_left.trans (inf_le_left.trans inf_le_left)

/-- Exact edge/sup membership normalization at an arbitrary pair. -/
theorem InternalReflexiveModel.inf_memB_pointwiseSupGraph_eq
    (𝓜 : InternalReflexiveModel (A := A))
    (S x y : AName.{u} A) :
    memB x 𝓜.D ⊓ memB y 𝓜.D ⊓
        memB (opairB x y) (pointwiseSupGraph 𝓜 S) =
      memB x 𝓜.D ⊓ memB y 𝓜.D ⊓
        isSupRelB y (graphImageB (evalAtGraph 𝓜 x) S 𝓜.D) 𝓜.R := by
  apply le_antisymm
  · exact le_inf
      (le_inf (inf_le_left.trans inf_le_left)
        (inf_le_left.trans inf_le_right))
      ((𝓜.memB_pointwiseSupGraph_le S x y).trans' inf_le_right |>.trans
        inf_le_right)
  · exact le_inf
      (le_inf (inf_le_left.trans inf_le_left)
        (inf_le_left.trans inf_le_right))
      (𝓜.le_memB_pointwiseSupGraph S x y)

/-- Displayed-child form of the edge/sup membership equation. -/
theorem InternalReflexiveModel.memB_pointwiseSupGraph_child
    (𝓜 : InternalReflexiveModel (A := A)) (S : AName.{u} A)
    (i j : 𝓜.D.idx) :
    memB (opairB (𝓜.D.child i) (𝓜.D.child j))
        (pointwiseSupGraph 𝓜 S) =
      memB (𝓜.D.child i) 𝓜.D ⊓
        isSupRelB (𝓜.D.child j)
          (graphImageB (evalAtGraph 𝓜 (𝓜.D.child i)) S 𝓜.D)
          𝓜.R := by
  apply le_antisymm
  · exact (𝓜.memB_pointwiseSupGraph_le S (𝓜.D.child i) (𝓜.D.child j)).trans <|
      le_inf (inf_le_left.trans inf_le_left) inf_le_right
  · exact val_le_memB (pointwiseSupGraph 𝓜 S) (i, j)

/-- The pointwise-supremum graph is a relation on `D`. -/
theorem InternalReflexiveModel.subsetB_pointwiseSupGraph
    (𝓜 : InternalReflexiveModel (A := A)) (S : AName.{u} A) :
    subsetB (pointwiseSupGraph 𝓜 S) (prodB 𝓜.D 𝓜.D) = ⊤ := by
  unfold InternalReflexiveModel.pointwiseSupGraph
  rw [subsetB_mk]
  refine iInf_eq_top.mpr fun p => himp_eq_top_iff.mpr ?_
  rw [memB_opairB_prodB]
  refine le_inf inf_le_left ?_
  have hj : memB (𝓜.D.child p.2) 𝓜.D = ⊤ := by
    rw [← oid_eps]
    exact 𝓜.total p.2
  exact le_top.trans hj.ge

/-- Uniqueness of displayed suprema yields single-valuedness. -/
theorem InternalReflexiveModel.pointwiseSupGraph_le_isSingleValuedB
    (𝓜 : InternalReflexiveModel (A := A)) (S : AName.{u} A) :
    isSingleValuedB (pointwiseSupGraph 𝓜 S) = ⊤ := by
  unfold isSingleValuedB
  refine iInf_eq_top.mpr fun x => iInf_eq_top.mpr fun y =>
    iInf_eq_top.mpr fun z => himp_eq_top_iff.mpr ?_
  let t :=
    memB (opairB x y) (pointwiseSupGraph 𝓜 S) ⊓
      memB (opairB x z) (pointwiseSupGraph 𝓜 S)
  change t ≤ eqB y z
  exact (𝓜.isSupRelB_unique y z
      (graphImageB (evalAtGraph 𝓜 x) S 𝓜.D)).trans' <| by
    refine le_inf (le_inf (le_inf ?_ ?_) ?_) ?_
    · exact (𝓜.memB_pointwiseSupGraph_le S x y).trans' inf_le_left |>.trans
        (inf_le_left.trans inf_le_right)
    · exact (𝓜.memB_pointwiseSupGraph_le S x z).trans' inf_le_right |>.trans
        (inf_le_left.trans inf_le_right)
    · exact (𝓜.memB_pointwiseSupGraph_le S x y).trans' inf_le_left |>.trans
        inf_le_right
    · exact (𝓜.memB_pointwiseSupGraph_le S x z).trans' inf_le_right |>.trans
        inf_le_right

/-- Directedness of `S` in `C` supplies an output index at every input of
`D`, after fullness realizes a supremum name and `memB_eq` reduces it to a
child. -/
theorem InternalReflexiveModel.pointwiseSupGraph_le_isTotalB
    (𝓜 : InternalReflexiveModel (A := A)) (S : AName.{u} A) :
    isDirectedRelB S 𝓜.C 𝓜.Q ≤
      isTotalB (pointwiseSupGraph 𝓜 S) 𝓜.D := by
  refine le_iInf fun x => ?_
  rw [le_himp_iff, memB_eq (x := x) (y := 𝓜.D), inf_iSup_eq]
  refine iSup_le fun i => ?_
  have hdir_img :
      isDirectedRelB S 𝓜.C 𝓜.Q ⊓
          (eqB x (𝓜.D.child i) ⊓ 𝓜.D.val i) ≤
        isDirectedRelB
          (graphImageB (evalAtGraph 𝓜 (𝓜.D.child i)) S 𝓜.D)
          𝓜.D 𝓜.R :=
    (𝓜.evalAtGraph_image_directed (a :=
        isDirectedRelB S 𝓜.C 𝓜.Q ⊓
          (eqB x (𝓜.D.child i) ⊓ 𝓜.D.val i))
      (𝓜.D.child i) S
      ((val_le_memB 𝓜.D i).trans' (inf_le_right.trans inf_le_right))).trans' <|
      le_inf le_rfl (inf_le_left)
  obtain ⟨d0, hd0⟩ := fullness
    (fun d =>
      memB d 𝓜.D ⊓
        isSupRelB d
          (graphImageB (evalAtGraph 𝓜 (𝓜.D.child i)) S 𝓜.D)
          𝓜.R)
    (fun d e =>
      mem_isSupRelB_congr 𝓜.D
        (graphImageB (evalAtGraph 𝓜 (𝓜.D.child i)) S 𝓜.D)
        𝓜.R d e)
  have hφ :
      isDirectedRelB S 𝓜.C 𝓜.Q ⊓
          (eqB x (𝓜.D.child i) ⊓ 𝓜.D.val i) ≤
        memB d0 𝓜.D ⊓
          isSupRelB d0
            (graphImageB (evalAtGraph 𝓜 (𝓜.D.child i)) S 𝓜.D)
            𝓜.R := by
    exact hdir_img.trans
      ((𝓜.dcpo_directed_has_sup
          (graphImageB (evalAtGraph 𝓜 (𝓜.D.child i)) S 𝓜.D)).trans
        (le_of_eq hd0.symm))
  have hred :
      memB d0 𝓜.D ⊓
          isSupRelB d0
            (graphImageB (evalAtGraph 𝓜 (𝓜.D.child i)) S 𝓜.D)
            𝓜.R ≤
        ⨆ j : 𝓜.D.idx,
          (eqB d0 (𝓜.D.child j) ⊓ 𝓜.D.val j) ⊓
            isSupRelB (𝓜.D.child j)
              (graphImageB (evalAtGraph 𝓜 (𝓜.D.child i)) S 𝓜.D)
              𝓜.R := by
    rw [memB_eq (x := d0) (y := 𝓜.D), iSup_inf_eq]
    refine iSup_le fun j => le_iSup_of_le j ?_
    refine le_inf inf_le_left ?_
    exact (isSupRelB_congr d0 (𝓜.D.child j)
        (graphImageB (evalAtGraph 𝓜 (𝓜.D.child i)) S 𝓜.D)
        𝓜.R).trans' <|
      le_inf (inf_le_left.trans inf_le_left) inf_le_right
  refine (le_inf le_rfl (hφ.trans hred)).trans ?_
  rw [inf_iSup_eq]
  refine iSup_le fun j => le_iSup_of_le (𝓜.D.child j) ?_
  let w :=
    (isDirectedRelB S 𝓜.C 𝓜.Q ⊓
        (eqB x (𝓜.D.child i) ⊓ 𝓜.D.val i)) ⊓
      ((eqB d0 (𝓜.D.child j) ⊓ 𝓜.D.val j) ⊓
        isSupRelB (𝓜.D.child j)
          (graphImageB (evalAtGraph 𝓜 (𝓜.D.child i)) S 𝓜.D)
          𝓜.R)
  change w ≤
    memB (opairB x (𝓜.D.child j)) (pointwiseSupGraph 𝓜 S)
  unfold InternalReflexiveModel.pointwiseSupGraph
  rw [memB_mk]
  refine le_iSup_of_le (i, j) ?_
  rw [eqB_opairB, eqB_self, inf_top_eq]
  refine le_inf ?_ (le_inf ?_ ?_)
  · exact inf_le_left.trans (inf_le_right.trans inf_le_left)
  · exact (val_le_memB 𝓜.D i).trans' <|
      inf_le_left.trans (inf_le_right.trans inf_le_right)
  · exact inf_le_right.trans inf_le_right

/-- Degree-local functionhood of the pointwise-supremum graph. -/
theorem InternalReflexiveModel.pointwiseSupGraph_le_isFunctionB
    (𝓜 : InternalReflexiveModel (A := A)) (S : AName.{u} A) :
    isDirectedRelB S 𝓜.C 𝓜.Q ≤
      isFunctionB (pointwiseSupGraph 𝓜 S) 𝓜.D 𝓜.D := by
  unfold isFunctionB
  refine le_inf (le_inf ?_ ?_) ?_
  · exact le_top.trans (𝓜.subsetB_pointwiseSupGraph S).ge
  · exact le_top.trans (𝓜.pointwiseSupGraph_le_isSingleValuedB S).ge
  · exact 𝓜.pointwiseSupGraph_le_isTotalB S

/-- Semantic evaluation of a map-space member is membership in the
fixed-argument slice. -/
theorem InternalReflexiveModel.le_memB_evalAtGraph
    (𝓜 : InternalReflexiveModel (A := A))
    (x F y : AName.{u} A) :
    memB F 𝓜.C ⊓ memB (opairB x y) F ≤
      memB (opairB F y) (evalAtGraph 𝓜 x) := by
  have hfunF : memB F 𝓜.C ≤ isFunctionB F 𝓜.D 𝓜.D :=
    𝓜.mem_mapSpace_le_function F
  have hsub : memB F 𝓜.C ≤ subsetB F (prodB 𝓜.D 𝓜.D) :=
    hfunF.trans (inf_le_left.trans inf_le_left)
  have hyd :
      memB F 𝓜.C ⊓ memB (opairB x y) F ≤
        ⨆ d : 𝓜.D.idx, memB (opairB x (𝓜.D.child d)) F :=
    (inf_memB_opairB_le_iSup_child hsub x y).trans' <|
      le_inf inf_le_left inf_le_right
  refine (le_inf le_rfl hyd).trans ?_
  rw [inf_iSup_eq]
  refine iSup_le fun d => ?_
  let t :=
    (memB F 𝓜.C ⊓ memB (opairB x y) F) ⊓
      memB (opairB x (𝓜.D.child d)) F
  change t ≤ memB (opairB F y) (evalAtGraph 𝓜 x)
  have hFd : t ≤
      memB (opairB F (𝓜.D.child d)) (evalAtGraph 𝓜 x) := by
    have hFC : t ≤ memB F 𝓜.C := inf_le_left.trans inf_le_left
    have hval : t ≤ memB (opairB x (𝓜.D.child d)) F := inf_le_right
    refine (le_inf hFC hval).trans ?_
    rw [memB_eq (x := F) (y := 𝓜.C), iSup_inf_eq]
    refine iSup_le fun c => ?_
    unfold InternalReflexiveModel.evalAtGraph
    rw [memB_mk]
    refine le_iSup_of_le (c, d) ?_
    rw [eqB_opairB, eqB_self, inf_top_eq]
    let s :=
      (eqB F (𝓜.C.child c) ⊓ (𝓜.C.val c)) ⊓
        memB (opairB x (𝓜.D.child d)) F
    change s ≤
      eqB F (𝓜.C.child c) ⊓
        (memB (𝓜.C.child c) 𝓜.C ⊓
          memB (opairB x (𝓜.D.child d)) (𝓜.C.child c))
    refine le_inf (inf_le_left.trans inf_le_left) (le_inf ?_ ?_)
    · exact (val_le_memB 𝓜.C c).trans' (inf_le_left.trans inf_le_right)
    · exact (memB_eqB_right F (opairB x (𝓜.D.child d))
        (𝓜.C.child c)).trans' <|
          le_inf inf_le_right (inf_le_left.trans inf_le_left)
  have hyeq : t ≤ eqB y (𝓜.D.child d) :=
    (isSingleValuedB_apply F x y (𝓜.D.child d)).trans' <|
      le_inf (le_inf
        ((inf_le_left.trans inf_le_left).trans
          (hfunF.trans (inf_le_left.trans inf_le_right)))
        (inf_le_left.trans inf_le_right))
        inf_le_right
  exact (memB_opairB_congr (evalAtGraph 𝓜 x) F F
      (𝓜.D.child d) y).trans' <|
    le_inf (le_inf
      (le_top.trans (eqB_self (A := A) F).ge)
      (by rw [eqB_comm]; exact hyeq))
      hFd

/-- The pointwise-supremum graph is monotone: a larger argument yields a
larger directed-evaluation supremum. -/
theorem InternalReflexiveModel.pointwiseSupGraph_apply_mono
    (𝓜 : InternalReflexiveModel (A := A)) (S : AName.{u} A)
    (x x' y y' : AName.{u} A) :
    isDirectedRelB S 𝓜.C 𝓜.Q ⊓
        memB (opairB x y) (pointwiseSupGraph 𝓜 S) ⊓
        memB (opairB x' y') (pointwiseSupGraph 𝓜 S) ⊓
        relB 𝓜.R x x' ≤
      relB 𝓜.R y y' := by
  let t :=
    isDirectedRelB S 𝓜.C 𝓜.Q ⊓
      memB (opairB x y) (pointwiseSupGraph 𝓜 S) ⊓
      memB (opairB x' y') (pointwiseSupGraph 𝓜 S) ⊓
      relB 𝓜.R x x'
  change t ≤ relB 𝓜.R y y'
  have htDir : t ≤ isDirectedRelB S 𝓜.C 𝓜.Q :=
    inf_le_left.trans (inf_le_left.trans inf_le_left)
  have htxy : t ≤ memB (opairB x y) (pointwiseSupGraph 𝓜 S) :=
    inf_le_left.trans (inf_le_left.trans inf_le_right)
  have htx'y' : t ≤ memB (opairB x' y') (pointwiseSupGraph 𝓜 S) :=
    inf_le_left.trans inf_le_right
  have htR : t ≤ relB 𝓜.R x x' := inf_le_right
  have hxy := (𝓜.memB_pointwiseSupGraph_le S x y).trans' htxy
  have hx'y' := (𝓜.memB_pointwiseSupGraph_le S x' y').trans' htx'y'
  have hx'D : t ≤ memB x' 𝓜.D :=
    hx'y'.trans (inf_le_left.trans inf_le_left)
  have hsupy : t ≤
      isSupRelB y (graphImageB (evalAtGraph 𝓜 x) S 𝓜.D) 𝓜.R :=
    hxy.trans inf_le_right
  have hsupy' : t ≤
      isSupRelB y' (graphImageB (evalAtGraph 𝓜 x') S 𝓜.D) 𝓜.R :=
    hx'y'.trans inf_le_right
  have hSsub : isDirectedRelB S 𝓜.C 𝓜.Q ≤ subsetB S 𝓜.C := by
    unfold isDirectedRelB
    exact inf_le_left.trans inf_le_left
  have hupper : t ≤ isUpperBoundRelB y'
      (graphImageB (evalAtGraph 𝓜 x) S 𝓜.D) 𝓜.R := by
    refine le_iInf fun z => ?_
    rw [le_himp_iff, memB_graphImageB, ← inf_assoc, inf_iSup_eq]
    refine iSup_le fun F => ?_
    let s :=
      (t ⊓ memB z 𝓜.D) ⊓
        (memB F S ⊓ memB (opairB F z) (evalAtGraph 𝓜 x))
    change s ≤ relB 𝓜.R z y'
    have hsT : s ≤ t := inf_le_left.trans inf_le_left
    have hFS : s ≤ memB F S := inf_le_right.trans inf_le_left
    have hFz : s ≤ memB (opairB F z) (evalAtGraph 𝓜 x) :=
      inf_le_right.trans inf_le_right
    have hFC : s ≤ memB F 𝓜.C :=
      (memB_of_subsetB F S 𝓜.C).trans' <|
        le_inf hFS (hsT.trans htDir |>.trans hSsub)
    have hxz : s ≤ memB (opairB x z) F :=
      (𝓜.memB_evalAtGraph_le x F z).trans' hFz |>.trans inf_le_right
    have htot :
        s ≤ ⨆ w : AName A,
          memB (opairB F w) (evalAtGraph 𝓜 x') :=
      (isTotalB_apply (evalAtGraph 𝓜 x') 𝓜.C F).trans' <|
        le_inf
          ((hsT.trans hx'D).trans (𝓜.evalAtGraph_le_isFunctionB x') |>.trans
            inf_le_right)
          hFC
    refine (le_inf le_rfl htot).trans ?_
    rw [inf_iSup_eq]
    refine iSup_le fun w => ?_
    let sw := s ⊓ memB (opairB F w) (evalAtGraph 𝓜 x')
    change sw ≤ relB 𝓜.R z y'
    have hswT : sw ≤ t := inf_le_left.trans hsT
    have hFw : sw ≤ memB (opairB F w) (evalAtGraph 𝓜 x') := inf_le_right
    have hx'w : sw ≤ memB (opairB x' w) F :=
      (𝓜.memB_evalAtGraph_le x' F w).trans' hFw |>.trans inf_le_right
    have hzw : sw ≤ relB 𝓜.R z w :=
      (𝓜.mem_mapSpace_apply_mono F x x' z w).trans' <| by
        refine le_inf (le_inf (le_inf ?_ ?_) ?_) ?_
        · exact inf_le_left.trans hFC
        · exact inf_le_left.trans hxz
        · exact hx'w
        · exact hswT.trans htR
    have hwD : sw ≤ memB w 𝓜.D :=
      (local_function_edge_le_codomain
          ((hswT.trans hx'D).trans (𝓜.evalAtGraph_le_isFunctionB x'))
          F w).trans' <|
        le_inf le_rfl hFw
    have hwImage : sw ≤
        memB w (graphImageB (evalAtGraph 𝓜 x') S 𝓜.D) := by
      rw [memB_graphImageB]
      refine le_inf hwD (le_iSup_of_le F ?_)
      exact le_inf (inf_le_left.trans hFS) hFw
    have hwy' : sw ≤ relB 𝓜.R w y' :=
      (isUpperBoundRelB_apply y'
          (graphImageB (evalAtGraph 𝓜 x') S 𝓜.D) 𝓜.R w).trans' <|
        le_inf (hswT.trans hsupy' |>.trans inf_le_left) hwImage
    exact (𝓜.relR_trans z w y').trans' (le_inf hzw hwy')
  exact (isSupRelB_least y
      (graphImageB (evalAtGraph 𝓜 x) S 𝓜.D) 𝓜.R y').trans' <|
    le_inf hsupy hupper

/-- Directed-supremum preservation for the pointwise-supremum graph. -/
theorem InternalReflexiveModel.pointwiseSupGraph_mapsToSup
    (𝓜 : InternalReflexiveModel (A := A))
    (S T x y : AName.{u} A) :
    isDirectedRelB S 𝓜.C 𝓜.Q ⊓
        isDirectedRelB T 𝓜.D 𝓜.R ⊓
        isSupRelB x T 𝓜.R ⊓
        memB (opairB x y) (pointwiseSupGraph 𝓜 S) ≤
      mapsToSupB (pointwiseSupGraph 𝓜 S) T y 𝓜.R := by
  unfold mapsToSupB
  refine le_inf ?_ ?_
  · refine le_iInf fun w => le_iInf fun z => ?_
    rw [le_himp_iff]
    let t :=
      (isDirectedRelB S 𝓜.C 𝓜.Q ⊓
        isDirectedRelB T 𝓜.D 𝓜.R ⊓
        isSupRelB x T 𝓜.R ⊓
        memB (opairB x y) (pointwiseSupGraph 𝓜 S)) ⊓
      (memB w T ⊓ memB (opairB w z) (pointwiseSupGraph 𝓜 S))
    change t ≤ relB 𝓜.R z y
    have hwx : t ≤ relB 𝓜.R w x :=
      (isUpperBoundRelB_apply x T 𝓜.R w).trans' <|
        le_inf
          (inf_le_left.trans (inf_le_left.trans inf_le_right) |>.trans
            inf_le_left)
          (inf_le_right.trans inf_le_left)
    exact (𝓜.pointwiseSupGraph_apply_mono S w x z y).trans' <|
      le_inf (le_inf (le_inf
          (inf_le_left.trans (inf_le_left.trans
            (inf_le_left.trans inf_le_left)))
          (inf_le_right.trans inf_le_right))
        (inf_le_left.trans inf_le_right))
        hwx
  · refine le_iInf fun u => ?_
    rw [le_himp_iff]
    let upper :=
      ⨅ w : AName A, ⨅ z : AName A,
        memB w T ⊓ memB (opairB w z) (pointwiseSupGraph 𝓜 S) ⇨
          relB 𝓜.R z u
    let t :=
      (isDirectedRelB S 𝓜.C 𝓜.Q ⊓
        isDirectedRelB T 𝓜.D 𝓜.R ⊓
        isSupRelB x T 𝓜.R ⊓
        memB (opairB x y) (pointwiseSupGraph 𝓜 S)) ⊓ upper
    change t ≤ relB 𝓜.R y u
    have htS : t ≤ isDirectedRelB S 𝓜.C 𝓜.Q :=
      inf_le_left.trans (inf_le_left.trans
        (inf_le_left.trans inf_le_left))
    have htT : t ≤ isDirectedRelB T 𝓜.D 𝓜.R :=
      inf_le_left.trans (inf_le_left.trans
        (inf_le_left.trans inf_le_right))
    have htx : t ≤ isSupRelB x T 𝓜.R :=
      inf_le_left.trans (inf_le_left.trans inf_le_right)
    have htxy : t ≤ memB (opairB x y) (pointwiseSupGraph 𝓜 S) :=
      inf_le_left.trans inf_le_right
    have htUpper : t ≤ upper := inf_le_right
    have hSsub : isDirectedRelB S 𝓜.C 𝓜.Q ≤ subsetB S 𝓜.C := by
      unfold isDirectedRelB
      exact inf_le_left.trans inf_le_left
    have hTsub : isDirectedRelB T 𝓜.D 𝓜.R ≤ subsetB T 𝓜.D := by
      unfold isDirectedRelB
      exact inf_le_left.trans inf_le_left
    have hsupy : t ≤
        isSupRelB y (graphImageB (evalAtGraph 𝓜 x) S 𝓜.D) 𝓜.R :=
      (𝓜.memB_pointwiseSupGraph_le S x y).trans' htxy |>.trans inf_le_right
    have hupperu : t ≤ isUpperBoundRelB u
        (graphImageB (evalAtGraph 𝓜 x) S 𝓜.D) 𝓜.R := by
      refine le_iInf fun v => ?_
      rw [le_himp_iff, memB_graphImageB, ← inf_assoc, inf_iSup_eq]
      refine iSup_le fun F => ?_
      let s :=
        (t ⊓ memB v 𝓜.D) ⊓
          (memB F S ⊓ memB (opairB F v) (evalAtGraph 𝓜 x))
      change s ≤ relB 𝓜.R v u
      have hsT : s ≤ t := inf_le_left.trans inf_le_left
      have hFS : s ≤ memB F S := inf_le_right.trans inf_le_left
      have hFv : s ≤ memB (opairB F v) (evalAtGraph 𝓜 x) :=
        inf_le_right.trans inf_le_right
      have hFC : s ≤ memB F 𝓜.C :=
        (memB_of_subsetB F S 𝓜.C).trans' <|
          le_inf hFS (hsT.trans htS |>.trans hSsub)
      have hxv : s ≤ memB (opairB x v) F :=
        (𝓜.memB_evalAtGraph_le x F v).trans' hFv |>.trans inf_le_right
      have hcont : s ≤ isScottContinuousB F 𝓜.D 𝓜.D 𝓜.R 𝓜.R :=
        (𝓜.mem_mapSpace_le_scottContinuous F).trans' hFC
      have hvsup : s ≤
          isSupRelB v (graphImageB F T 𝓜.D) 𝓜.R :=
        ((scottContinuous_image_sup (hF := hcont)
            F T 𝓜.D 𝓜.D 𝓜.R 𝓜.R x v).trans inf_le_right).trans' <|
          le_inf (le_inf (le_inf le_rfl (hsT.trans htT))
            (hsT.trans htx)) hxv
      have huF : s ≤ isUpperBoundRelB u (graphImageB F T 𝓜.D) 𝓜.R := by
        refine le_iInf fun p => ?_
        rw [le_himp_iff, memB_graphImageB, ← inf_assoc, inf_iSup_eq]
        refine iSup_le fun w => ?_
        let sp :=
          (s ⊓ memB p 𝓜.D) ⊓
            (memB w T ⊓ memB (opairB w p) F)
        change sp ≤ relB 𝓜.R p u
        have hspS : sp ≤ s := inf_le_left.trans inf_le_left
        have hpD : sp ≤ memB p 𝓜.D := inf_le_left.trans inf_le_right
        have hwT : sp ≤ memB w T := inf_le_right.trans inf_le_left
        have hwp : sp ≤ memB (opairB w p) F :=
          inf_le_right.trans inf_le_right
        have hwD : sp ≤ memB w 𝓜.D :=
          (memB_of_subsetB w T 𝓜.D).trans' <|
            le_inf hwT (hspS.trans hsT |>.trans htT |>.trans hTsub)
        have htot : sp ≤
            ⨆ z : AName A,
              memB (opairB w z) (pointwiseSupGraph 𝓜 S) :=
          (isTotalB_apply (pointwiseSupGraph 𝓜 S) 𝓜.D w).trans' <|
            le_inf
              ((hspS.trans hsT |>.trans htS).trans
                (𝓜.pointwiseSupGraph_le_isTotalB S))
              hwD
        refine (le_inf le_rfl htot).trans ?_
        rw [inf_iSup_eq]
        refine iSup_le fun z => ?_
        let sz :=
          sp ⊓ memB (opairB w z) (pointwiseSupGraph 𝓜 S)
        change sz ≤ relB 𝓜.R p u
        have hszsp : sz ≤ sp := inf_le_left
        have hzw : sz ≤ memB (opairB w z) (pointwiseSupGraph 𝓜 S) :=
          inf_le_right
        have hpEval : sz ≤ memB (opairB F p) (evalAtGraph 𝓜 w) :=
          (𝓜.le_memB_evalAtGraph w F p).trans' <|
            le_inf (hszsp.trans hspS |>.trans hFC)
              (hszsp.trans hwp)
        have hpImage : sz ≤
            memB p (graphImageB (evalAtGraph 𝓜 w) S 𝓜.D) := by
          rw [memB_graphImageB]
          refine le_inf (hszsp.trans hpD) (le_iSup_of_le F ?_)
          exact le_inf (hszsp.trans hspS |>.trans hFS) hpEval
        have hpz : sz ≤ relB 𝓜.R p z :=
          (isUpperBoundRelB_apply z
              (graphImageB (evalAtGraph 𝓜 w) S 𝓜.D) 𝓜.R p).trans' <|
            le_inf
              ((𝓜.memB_pointwiseSupGraph_le S w z).trans' hzw |>.trans
                (inf_le_right.trans inf_le_left))
              hpImage
        have hzu : sz ≤ relB 𝓜.R z u := by
          have hu := iInf_le
            (fun w' : AName A => ⨅ z' : AName A,
              memB w' T ⊓ memB (opairB w' z') (pointwiseSupGraph 𝓜 S) ⇨
                relB 𝓜.R z' u) w
          have hz := (iInf_le
            (fun z' : AName A =>
              memB w T ⊓ memB (opairB w z') (pointwiseSupGraph 𝓜 S) ⇨
                relB 𝓜.R z' u) z).trans' hu
          exact (le_himp_iff.mp hz).trans' <|
            le_inf (hszsp.trans hspS |>.trans hsT |>.trans htUpper)
              (le_inf (hszsp.trans hwT) hzw)
        exact (𝓜.relR_trans p z u).trans' (le_inf hpz hzu)
      exact (isSupRelB_least v (graphImageB F T 𝓜.D) 𝓜.R u).trans' <|
        le_inf hvsup huF
    exact (isSupRelB_least y
        (graphImageB (evalAtGraph 𝓜 x) S 𝓜.D) 𝓜.R u).trans' <|
      le_inf hsupy hupperu

/-- Degree-local Scott continuity of the pointwise-supremum graph as a
self-map of `D`. -/
theorem InternalReflexiveModel.pointwiseSupGraph_le_isScottContinuousB
    (𝓜 : InternalReflexiveModel (A := A)) (S : AName.{u} A) :
    isDirectedRelB S 𝓜.C 𝓜.Q ≤
      isScottContinuousB (pointwiseSupGraph 𝓜 S) 𝓜.D 𝓜.D 𝓜.R 𝓜.R := by
  unfold isScottContinuousB
  refine le_inf (le_inf ?_ ?_) ?_
  · exact 𝓜.pointwiseSupGraph_le_isFunctionB S
  · refine le_iInf fun x => le_iInf fun x' =>
      le_iInf fun y => le_iInf fun y' => ?_
    rw [le_himp_iff]
    exact (𝓜.pointwiseSupGraph_apply_mono S x x' y y').trans' <| by
      apply le_of_eq
      ac_rfl
  · refine le_iInf fun T => le_iInf fun x => le_iInf fun y => ?_
    rw [le_himp_iff]
    exact (𝓜.pointwiseSupGraph_mapsToSup S T x y).trans' <| by
      apply le_of_eq
      ac_rfl

/-- Directed `S ⊆ D` projects to Boolean inclusion. -/
theorem isDirectedRelB_subset
    (S D R : AName.{u} A) :
    isDirectedRelB S D R ≤ subsetB S D := by
  unfold isDirectedRelB
  exact inf_le_left.trans inf_le_left

/-- Directed `S` is internally nonempty. -/
theorem isDirectedRelB_nonempty
    (S D R : AName.{u} A) :
    isDirectedRelB S D R ≤ ⨆ x : AName A, memB x S := by
  unfold isDirectedRelB
  exact inf_le_left.trans inf_le_right

/-- At the degree of a relation contained in a product, membership of an
arbitrary name reduces to the displayed pair matrix. -/
theorem inf_memB_le_iSup_matrix {a : A} {F X Y : AName.{u} A}
    (hsub : a ≤ subsetB F (prodB X Y)) (w : AName.{u} A) :
    a ⊓ memB w F ≤
      ⨆ p : X.idx × Y.idx,
        eqB w (opairB (X.child p.1) (Y.child p.2)) ⊓
          memB (opairB (X.child p.1) (Y.child p.2)) F := by
  have hw : a ⊓ memB w F ≤ memB w (prodB X Y) :=
    (memB_of_subsetB w F (prodB X Y)).trans' <|
      le_inf inf_le_right (inf_le_left.trans hsub)
  have hprod :
      memB w (prodB X Y) =
        ⨆ p : X.idx × Y.idx,
          eqB w (opairB (X.child p.1) (Y.child p.2)) ⊓
            (memB (X.child p.1) X ⊓ memB (Y.child p.2) Y) := by
    rw [memB_eq]
    unfold prodB
    rfl
  refine (le_inf le_rfl hw).trans ?_
  rw [hprod, inf_iSup_eq]
  refine iSup_le fun p => le_iSup_of_le p ?_
  refine le_inf (inf_le_right.trans inf_le_left) ?_
  exact (memB_eqB_left w F
      (opairB (X.child p.1) (Y.child p.2))).trans' <|
    le_inf (inf_le_left.trans inf_le_right)
      (inf_le_right.trans inf_le_left)

/-- Graph inclusion from agreeing on every displayed pair, at the degree
where the source is a relation on `X × Y`. -/
theorem subsetB_of_same_pairs {a : A} {F G X Y : AName.{u} A}
    (hsub : a ≤ subsetB F (prodB X Y))
    (hsame : ∀ x y : AName.{u} A,
      a ⊓ memB x X ⊓ memB (opairB x y) F ≤
        memB (opairB x y) G) :
    a ≤ subsetB F G := by
  rw [subsetB_eq_iInf]
  refine le_iInf fun w => ?_
  rw [le_himp_iff]
  refine (le_inf inf_le_left (inf_memB_le_iSup_matrix hsub w)).trans ?_
  rw [inf_iSup_eq]
  refine iSup_le fun p => ?_
  let pair := opairB (X.child p.1) (Y.child p.2)
  change a ⊓ (eqB w pair ⊓ memB pair F) ≤ memB w G
  have hx : a ⊓ memB pair F ≤ memB (X.child p.1) X := by
    have h := (memB_of_subsetB pair F (prodB X Y)).trans' <|
      le_inf inf_le_right (inf_le_left.trans hsub)
    rw [memB_opairB_prodB] at h
    exact h.trans inf_le_left
  have hG : a ⊓ memB pair F ≤ memB pair G :=
    (hsame (X.child p.1) (Y.child p.2)).trans' <|
      le_inf (le_inf inf_le_left hx) inf_le_right
  exact (memB_eqB_left' pair G w).trans' <|
    le_inf (inf_le_right.trans inf_le_left)
      (hG.trans' <|
        le_inf inf_le_left (inf_le_right.trans inf_le_right))

/-- Mutual `Q`-comparison of members of `C` equates their values at a
common argument. -/
theorem InternalReflexiveModel.relQ_antisymm_apply
    (𝓜 : InternalReflexiveModel (A := A))
    (F G x y z : AName.{u} A) :
    memB F 𝓜.C ⊓ memB G 𝓜.C ⊓
        relB 𝓜.Q F G ⊓ relB 𝓜.Q G F ⊓
        memB x 𝓜.D ⊓ memB (opairB x y) F ⊓
          memB (opairB x z) G ≤
      eqB y z := by
  let t :=
    memB F 𝓜.C ⊓ memB G 𝓜.C ⊓
      relB 𝓜.Q F G ⊓ relB 𝓜.Q G F ⊓
      memB x 𝓜.D ⊓ memB (opairB x y) F ⊓
        memB (opairB x z) G
  change t ≤ eqB y z
  have hF : t ≤ memB F 𝓜.C :=
    inf_le_left.trans (inf_le_left.trans
      (inf_le_left.trans (inf_le_left.trans
        (inf_le_left.trans inf_le_left))))
  have hG : t ≤ memB G 𝓜.C :=
    inf_le_left.trans (inf_le_left.trans
      (inf_le_left.trans (inf_le_left.trans
        (inf_le_left.trans inf_le_right))))
  have hFG : t ≤ relB 𝓜.Q F G :=
    inf_le_left.trans (inf_le_left.trans
      (inf_le_left.trans (inf_le_left.trans inf_le_right)))
  have hGF : t ≤ relB 𝓜.Q G F :=
    inf_le_left.trans (inf_le_left.trans
      (inf_le_left.trans inf_le_right))
  have hx : t ≤ memB x 𝓜.D :=
    inf_le_left.trans (inf_le_left.trans inf_le_right)
  have hFy : t ≤ memB (opairB x y) F :=
    inf_le_left.trans inf_le_right
  have hGz : t ≤ memB (opairB x z) G :=
    inf_le_right
  have hyD : t ≤ memB y 𝓜.D :=
    (local_function_edge_le_codomain
      (hF.trans (𝓜.mem_mapSpace_le_function F)) x y).trans' <|
      le_inf le_rfl hFy
  have hzD : t ≤ memB z 𝓜.D :=
    (local_function_edge_le_codomain
      (hG.trans (𝓜.mem_mapSpace_le_function G)) x z).trans' <|
      le_inf le_rfl hGz
  have hRyz : t ≤ relB 𝓜.R y z :=
    (𝓜.relQ_apply F G x y z).trans' <|
      le_inf (le_inf (le_inf hF hG) hFG)
        (le_inf (le_inf hx hFy) hGz)
  have hRzy : t ≤ relB 𝓜.R z y :=
    (𝓜.relQ_apply G F x z y).trans' <|
      le_inf (le_inf (le_inf hG hF) hGF)
        (le_inf (le_inf hx hGz) hFy)
  exact (𝓜.relR_antisymm y z).trans' <|
    le_inf (le_inf (le_inf hyD hzD) hRyz) hRzy

/-- Antisymmetry of `Q` on members of `C`, from the pointwise order and
function uniqueness. -/
theorem InternalReflexiveModel.relQ_antisymm
    (𝓜 : InternalReflexiveModel (A := A))
    (F G : AName.{u} A) :
    memB F 𝓜.C ⊓ memB G 𝓜.C ⊓
        relB 𝓜.Q F G ⊓ relB 𝓜.Q G F ≤
      eqB F G := by
  let t :=
    memB F 𝓜.C ⊓ memB G 𝓜.C ⊓
      relB 𝓜.Q F G ⊓ relB 𝓜.Q G F
  change t ≤ eqB F G
  have hF : t ≤ memB F 𝓜.C :=
    inf_le_left.trans (inf_le_left.trans inf_le_left)
  have hG : t ≤ memB G 𝓜.C :=
    inf_le_left.trans (inf_le_left.trans inf_le_right)
  have hFG : t ≤ relB 𝓜.Q F G :=
    inf_le_left.trans inf_le_right
  have hGF : t ≤ relB 𝓜.Q G F :=
    inf_le_right
  have hfunF : t ≤ isFunctionB F 𝓜.D 𝓜.D :=
    (𝓜.mem_mapSpace_le_function F).trans' hF
  have hfunG : t ≤ isFunctionB G 𝓜.D 𝓜.D :=
    (𝓜.mem_mapSpace_le_function G).trans' hG
  have hsubF : t ≤ subsetB F (prodB 𝓜.D 𝓜.D) :=
    hfunF.trans (inf_le_left.trans inf_le_left)
  have hsubG : t ≤ subsetB G (prodB 𝓜.D 𝓜.D) :=
    hfunG.trans (inf_le_left.trans inf_le_left)
  have hsameFG (x y : AName.{u} A) :
      t ⊓ memB x 𝓜.D ⊓ memB (opairB x y) F ≤
        memB (opairB x y) G := by
    have htot :
        t ⊓ memB x 𝓜.D ⊓ memB (opairB x y) F ≤
          ⨆ z : AName A, memB (opairB x z) G :=
      (isTotalB_apply G 𝓜.D x).trans' <|
        le_inf
          ((inf_le_left.trans (inf_le_left.trans hfunG)).trans
            inf_le_right)
          (inf_le_left.trans inf_le_right)
    refine (le_inf le_rfl htot).trans ?_
    rw [inf_iSup_eq]
    refine iSup_le fun z => ?_
    let s :=
      (t ⊓ memB x 𝓜.D ⊓ memB (opairB x y) F) ⊓
        memB (opairB x z) G
    change s ≤ memB (opairB x y) G
    have hsT : s ≤ t :=
      inf_le_left.trans (inf_le_left.trans inf_le_left)
    have hsx : s ≤ memB x 𝓜.D :=
      inf_le_left.trans (inf_le_left.trans inf_le_right)
    have hsFy : s ≤ memB (opairB x y) F :=
      inf_le_left.trans inf_le_right
    have hsGz : s ≤ memB (opairB x z) G :=
      inf_le_right
    have hyz : s ≤ eqB y z :=
      (𝓜.relQ_antisymm_apply F G x y z).trans' <|
        le_inf (le_inf (le_inf (le_inf (le_inf (le_inf
          (hsT.trans hF) (hsT.trans hG)) (hsT.trans hFG))
          (hsT.trans hGF)) hsx) hsFy) hsGz
    exact (memB_opairB_congr G x x z y).trans' <|
      le_inf (le_inf
        (le_top.trans (eqB_self (A := A) x).ge)
        (by rw [eqB_comm]; exact hyz))
        hsGz
  have hsameGF (x y : AName.{u} A) :
      t ⊓ memB x 𝓜.D ⊓ memB (opairB x y) G ≤
        memB (opairB x y) F := by
    have htot :
        t ⊓ memB x 𝓜.D ⊓ memB (opairB x y) G ≤
          ⨆ z : AName A, memB (opairB x z) F :=
      (isTotalB_apply F 𝓜.D x).trans' <|
        le_inf
          ((inf_le_left.trans (inf_le_left.trans hfunF)).trans
            inf_le_right)
          (inf_le_left.trans inf_le_right)
    refine (le_inf le_rfl htot).trans ?_
    rw [inf_iSup_eq]
    refine iSup_le fun z => ?_
    let s :=
      (t ⊓ memB x 𝓜.D ⊓ memB (opairB x y) G) ⊓
        memB (opairB x z) F
    change s ≤ memB (opairB x y) F
    have hsT : s ≤ t :=
      inf_le_left.trans (inf_le_left.trans inf_le_left)
    have hsx : s ≤ memB x 𝓜.D :=
      inf_le_left.trans (inf_le_left.trans inf_le_right)
    have hsGy : s ≤ memB (opairB x y) G :=
      inf_le_left.trans inf_le_right
    have hsFz : s ≤ memB (opairB x z) F :=
      inf_le_right
    have hyz : s ≤ eqB y z :=
      (𝓜.relQ_antisymm_apply G F x y z).trans' <|
        le_inf (le_inf (le_inf (le_inf (le_inf (le_inf
          (hsT.trans hG) (hsT.trans hF)) (hsT.trans hGF))
          (hsT.trans hFG)) hsx) hsGy) hsFz
    exact (memB_opairB_congr F x x z y).trans' <|
      le_inf (le_inf
        (le_top.trans (eqB_self (A := A) x).ge)
        (by rw [eqB_comm]; exact hyz))
        hsFz
  rw [eqB_eq_subset]
  exact le_inf
    (subsetB_of_same_pairs hsubF hsameFG)
    (subsetB_of_same_pairs hsubG hsameGF)

/-- Scott continuity of the pointwise-supremum graph places it in `C`. -/
theorem InternalReflexiveModel.pointwiseSupGraph_le_mem_mapSpace
    (𝓜 : InternalReflexiveModel (A := A)) (S : AName.{u} A) :
    isDirectedRelB S 𝓜.C 𝓜.Q ≤
      memB (pointwiseSupGraph 𝓜 S) 𝓜.C :=
  (𝓜.scottContinuous_le_mem_mapSpace (pointwiseSupGraph 𝓜 S)).trans'
    (𝓜.pointwiseSupGraph_le_isScottContinuousB S)

/-- The internal order `Q` is a relation on `C`. -/
theorem InternalReflexiveModel.subsetB_Q
    (𝓜 : InternalReflexiveModel (A := A)) :
    subsetB 𝓜.Q (prodB 𝓜.C 𝓜.C) = ⊤ := by
  have hpo := 𝓜.pointwise_valid
  unfold isPointwiseOrderB at hpo
  exact (inf_eq_top_iff.mp hpo).1

/-- A `Q`-related pair consists of members of `C`. -/
theorem InternalReflexiveModel.relQ_le_mem_mapSpace
    (𝓜 : InternalReflexiveModel (A := A))
    (F G : AName.{u} A) :
    relB 𝓜.Q F G ≤ memB F 𝓜.C ⊓ memB G 𝓜.C := by
  have h := (memB_of_subsetB (opairB F G) 𝓜.Q (prodB 𝓜.C 𝓜.C)).trans' <|
    le_inf le_rfl (le_top.trans (𝓜.subsetB_Q).ge)
  rw [memB_opairB_prodB] at h
  exact h

/-- A `Q`-upper bound of a nonempty family of members of `C` itself
belongs to `C`. -/
theorem InternalReflexiveModel.isUpperBoundRelB_le_mem_mapSpace
    (𝓜 : InternalReflexiveModel (A := A))
    (F S : AName.{u} A) :
    (⨆ G : AName A, memB G S) ⊓ isUpperBoundRelB F S 𝓜.Q ≤
      memB F 𝓜.C := by
  rw [inf_comm, inf_iSup_eq]
  refine iSup_le fun G => ?_
  have hQG :
      isUpperBoundRelB F S 𝓜.Q ⊓ memB G S ≤ relB 𝓜.Q G F :=
    isUpperBoundRelB_apply F S 𝓜.Q G
  exact (𝓜.relQ_le_mem_mapSpace G F).trans' hQG |>.trans inf_le_right

/-- Every member of directed `S ⊆ C` is `Q`-below the pointwise-supremum
graph, because each value `G(x)` lies in the eval-image whose `R`-supremum
is the pointwise-sup output. -/
theorem InternalReflexiveModel.pointwiseSupGraph_upper_apply
    (𝓜 : InternalReflexiveModel (A := A))
    (S G : AName.{u} A) :
    isDirectedRelB S 𝓜.C 𝓜.Q ⊓ memB G S ≤
      relB 𝓜.Q G (pointwiseSupGraph 𝓜 S) := by
  let t := isDirectedRelB S 𝓜.C 𝓜.Q ⊓ memB G S
  change t ≤ relB 𝓜.Q G (pointwiseSupGraph 𝓜 S)
  have htDir : t ≤ isDirectedRelB S 𝓜.C 𝓜.Q := inf_le_left
  have htG : t ≤ memB G S := inf_le_right
  have hGC : t ≤ memB G 𝓜.C :=
    (memB_of_subsetB G S 𝓜.C).trans' <|
      le_inf htG (htDir.trans (isDirectedRelB_subset S 𝓜.C 𝓜.Q))
  have hsupC : t ≤ memB (pointwiseSupGraph 𝓜 S) 𝓜.C :=
    (𝓜.pointwiseSupGraph_le_mem_mapSpace S).trans' htDir
  have hpw : t ≤
      pointwiseLeB G (pointwiseSupGraph 𝓜 S) 𝓜.D 𝓜.R := by
    unfold pointwiseLeB
    refine le_iInf fun x => le_iInf fun y => le_iInf fun z => ?_
    rw [le_himp_iff]
    let s :=
      t ⊓ (memB x 𝓜.D ⊓ memB (opairB x y) G ⊓
        memB (opairB x z) (pointwiseSupGraph 𝓜 S))
    change s ≤ relB 𝓜.R y z
    have hsT : s ≤ t := inf_le_left
    have hxD : s ≤ memB x 𝓜.D :=
      inf_le_right.trans (inf_le_left.trans inf_le_left)
    have hxy : s ≤ memB (opairB x y) G :=
      inf_le_right.trans (inf_le_left.trans inf_le_right)
    have hxz : s ≤
        memB (opairB x z) (pointwiseSupGraph 𝓜 S) :=
      inf_le_right.trans inf_le_right
    have hyD : s ≤ memB y 𝓜.D :=
      (local_function_edge_le_codomain
        ((hsT.trans hGC).trans (𝓜.mem_mapSpace_le_function G))
        x y).trans' <|
        le_inf le_rfl hxy
    have hyEval : s ≤ memB (opairB G y) (evalAtGraph 𝓜 x) :=
      (𝓜.le_memB_evalAtGraph x G y).trans' <|
        le_inf (hsT.trans hGC) hxy
    have hyImage : s ≤
        memB y (graphImageB (evalAtGraph 𝓜 x) S 𝓜.D) := by
      rw [memB_graphImageB]
      refine le_inf hyD (le_iSup_of_le G ?_)
      exact le_inf (hsT.trans htG) hyEval
    have hsupz : s ≤
        isSupRelB z (graphImageB (evalAtGraph 𝓜 x) S 𝓜.D) 𝓜.R :=
      (𝓜.memB_pointwiseSupGraph_le S x z).trans' hxz |>.trans
        inf_le_right
    exact (isUpperBoundRelB_apply z
        (graphImageB (evalAtGraph 𝓜 x) S 𝓜.D) 𝓜.R y).trans' <|
      le_inf (hsupz.trans inf_le_left) hyImage
  exact (𝓜.pointwise_le_relQ G (pointwiseSupGraph 𝓜 S)).trans' <|
    le_inf (le_inf hGC hsupC) hpw

/-- If `F` is a `Q`-upper bound of directed `S`, then the pointwise-supremum
graph is `Q`-below `F`: each `G(x) ≤ F(x)`, so the eval-image `R`-supremum
is `≤ F(x)`. -/
theorem InternalReflexiveModel.pointwiseSupGraph_least_apply
    (𝓜 : InternalReflexiveModel (A := A))
    (S F : AName.{u} A) :
    isDirectedRelB S 𝓜.C 𝓜.Q ⊓ isUpperBoundRelB F S 𝓜.Q ≤
      relB 𝓜.Q (pointwiseSupGraph 𝓜 S) F := by
  let t :=
    isDirectedRelB S 𝓜.C 𝓜.Q ⊓ isUpperBoundRelB F S 𝓜.Q
  change t ≤ relB 𝓜.Q (pointwiseSupGraph 𝓜 S) F
  have htDir : t ≤ isDirectedRelB S 𝓜.C 𝓜.Q := inf_le_left
  have htUpper : t ≤ isUpperBoundRelB F S 𝓜.Q := inf_le_right
  have hFC : t ≤ memB F 𝓜.C :=
    (𝓜.isUpperBoundRelB_le_mem_mapSpace F S).trans' <|
      le_inf (htDir.trans (isDirectedRelB_nonempty S 𝓜.C 𝓜.Q))
        htUpper
  have hsupC : t ≤ memB (pointwiseSupGraph 𝓜 S) 𝓜.C :=
    (𝓜.pointwiseSupGraph_le_mem_mapSpace S).trans' htDir
  have hpw : t ≤
      pointwiseLeB (pointwiseSupGraph 𝓜 S) F 𝓜.D 𝓜.R := by
    unfold pointwiseLeB
    refine le_iInf fun x => le_iInf fun y => le_iInf fun z => ?_
    rw [le_himp_iff]
    let s :=
      t ⊓ (memB x 𝓜.D ⊓
        memB (opairB x y) (pointwiseSupGraph 𝓜 S) ⊓
        memB (opairB x z) F)
    change s ≤ relB 𝓜.R y z
    have hsT : s ≤ t := inf_le_left
    have hxD : s ≤ memB x 𝓜.D :=
      inf_le_right.trans (inf_le_left.trans inf_le_left)
    have hxy : s ≤
        memB (opairB x y) (pointwiseSupGraph 𝓜 S) :=
      inf_le_right.trans (inf_le_left.trans inf_le_right)
    have hxz : s ≤ memB (opairB x z) F :=
      inf_le_right.trans inf_le_right
    have hsupy : s ≤
        isSupRelB y (graphImageB (evalAtGraph 𝓜 x) S 𝓜.D) 𝓜.R :=
      (𝓜.memB_pointwiseSupGraph_le S x y).trans' hxy |>.trans
        inf_le_right
    have hupperz : s ≤ isUpperBoundRelB z
        (graphImageB (evalAtGraph 𝓜 x) S 𝓜.D) 𝓜.R := by
      refine le_iInf fun v => ?_
      rw [le_himp_iff, memB_graphImageB, ← inf_assoc, inf_iSup_eq]
      refine iSup_le fun G => ?_
      let u :=
        (s ⊓ memB v 𝓜.D) ⊓
          (memB G S ⊓ memB (opairB G v) (evalAtGraph 𝓜 x))
      change u ≤ relB 𝓜.R v z
      have huS : u ≤ s := inf_le_left.trans inf_le_left
      have hGS : u ≤ memB G S := inf_le_right.trans inf_le_left
      have hGv : u ≤ memB (opairB G v) (evalAtGraph 𝓜 x) :=
        inf_le_right.trans inf_le_right
      have hGC : u ≤ memB G 𝓜.C :=
        (memB_of_subsetB G S 𝓜.C).trans' <|
          le_inf hGS (huS.trans hsT |>.trans htDir |>.trans
            (isDirectedRelB_subset S 𝓜.C 𝓜.Q))
      have hxv : u ≤ memB (opairB x v) G :=
        (𝓜.memB_evalAtGraph_le x G v).trans' hGv |>.trans
          inf_le_right
      have hQGF : u ≤ relB 𝓜.Q G F :=
        (isUpperBoundRelB_apply F S 𝓜.Q G).trans' <|
          le_inf (huS.trans hsT |>.trans htUpper) hGS
      exact (𝓜.relQ_apply G F x v z).trans' <|
        le_inf (le_inf (le_inf hGC (huS.trans hsT |>.trans hFC))
          hQGF)
          (le_inf (le_inf (huS.trans hxD) hxv)
            (huS.trans hxz))
    exact (isSupRelB_least y
        (graphImageB (evalAtGraph 𝓜 x) S 𝓜.D) 𝓜.R z).trans' <|
      le_inf hsupy hupperz
  exact (𝓜.pointwise_le_relQ (pointwiseSupGraph 𝓜 S) F).trans' <|
    le_inf (le_inf hsupC hFC) hpw

/-- The pointwise-supremum graph is a `Q`-supremum of directed `S`. -/
theorem InternalReflexiveModel.pointwiseSupGraph_le_isSupRelB
    (𝓜 : InternalReflexiveModel (A := A)) (S : AName.{u} A) :
    isDirectedRelB S 𝓜.C 𝓜.Q ≤
      isSupRelB (pointwiseSupGraph 𝓜 S) S 𝓜.Q := by
  unfold isSupRelB
  refine le_inf ?_ ?_
  · unfold isUpperBoundRelB
    refine le_iInf fun G => ?_
    rw [le_himp_iff]
    exact 𝓜.pointwiseSupGraph_upper_apply S G
  · refine le_iInf fun F => ?_
    rw [le_himp_iff]
    exact 𝓜.pointwiseSupGraph_least_apply S F

/-- Any `Q`-supremum of directed `S` in `C` is Boolean-equal to the
pointwise-supremum graph. -/
theorem InternalReflexiveModel.isSupRelB_le_eqB_pointwiseSupGraph
    (𝓜 : InternalReflexiveModel (A := A)) (S F : AName.{u} A) :
    isDirectedRelB S 𝓜.C 𝓜.Q ⊓ memB F 𝓜.C ⊓ isSupRelB F S 𝓜.Q ≤
      eqB F (pointwiseSupGraph 𝓜 S) := by
  let t :=
    isDirectedRelB S 𝓜.C 𝓜.Q ⊓ memB F 𝓜.C ⊓
      isSupRelB F S 𝓜.Q
  change t ≤ eqB F (pointwiseSupGraph 𝓜 S)
  have htDir : t ≤ isDirectedRelB S 𝓜.C 𝓜.Q :=
    inf_le_left.trans inf_le_left
  have htF : t ≤ memB F 𝓜.C :=
    inf_le_left.trans inf_le_right
  have htSup : t ≤ isSupRelB F S 𝓜.Q := inf_le_right
  have hsupC : t ≤ memB (pointwiseSupGraph 𝓜 S) 𝓜.C :=
    (𝓜.pointwiseSupGraph_le_mem_mapSpace S).trans' htDir
  have hsupS : t ≤ isSupRelB (pointwiseSupGraph 𝓜 S) S 𝓜.Q :=
    (𝓜.pointwiseSupGraph_le_isSupRelB S).trans' htDir
  have hFQ : t ≤ relB 𝓜.Q F (pointwiseSupGraph 𝓜 S) :=
    (isSupRelB_least F S 𝓜.Q (pointwiseSupGraph 𝓜 S)).trans' <|
      le_inf htSup (hsupS.trans inf_le_left)
  have hQF : t ≤ relB 𝓜.Q (pointwiseSupGraph 𝓜 S) F :=
    (isSupRelB_least (pointwiseSupGraph 𝓜 S) S 𝓜.Q F).trans' <|
      le_inf hsupS (htSup.trans inf_le_left)
  exact (𝓜.relQ_antisymm F (pointwiseSupGraph 𝓜 S)).trans' <|
    le_inf (le_inf (le_inf htF hsupC) hFQ) hQF

/-- The converse of `mapsToSupB_le_isSup_graphImageB`: a supremum of
the canonical image is the displayed image-supremum of the graph. -/
theorem isSup_graphImageB_le_mapsToSupB
    {a : A} (F S D E Q y : AName.{u} A)
    (hF : a ≤ isFunctionB F D E) :
    a ⊓ isSupRelB y (graphImageB F S E) Q ≤
      mapsToSupB F S y Q := by
  unfold mapsToSupB
  refine le_inf ?_ ?_
  · refine le_iInf fun x => le_iInf fun z => ?_
    rw [le_himp_iff]
    let t :=
      (a ⊓ isSupRelB y (graphImageB F S E) Q) ⊓
        (memB x S ⊓ memB (opairB x z) F)
    change t ≤ relB Q z y
    have hzE : t ≤ memB z E :=
      (local_function_edge_le_codomain
        ((inf_le_left.trans inf_le_left).trans hF) x z).trans' <|
        le_inf le_rfl (inf_le_right.trans inf_le_right)
    have hzImage : t ≤ memB z (graphImageB F S E) := by
      rw [memB_graphImageB]
      refine le_inf hzE (le_iSup_of_le x ?_)
      exact inf_le_right
    exact (isUpperBoundRelB_apply y (graphImageB F S E) Q z).trans' <|
      le_inf (inf_le_left.trans inf_le_right |>.trans inf_le_left)
        hzImage
  · refine le_iInf fun u => ?_
    rw [le_himp_iff]
    let upper :=
      ⨅ x : AName A, ⨅ z : AName A,
        memB x S ⊓ memB (opairB x z) F ⇨ relB Q z u
    let t :=
      (a ⊓ isSupRelB y (graphImageB F S E) Q) ⊓ upper
    change t ≤ relB Q y u
    have hupperu : t ≤ isUpperBoundRelB u (graphImageB F S E) Q := by
      refine le_iInf fun v => ?_
      rw [le_himp_iff, memB_graphImageB, ← inf_assoc, inf_iSup_eq]
      refine iSup_le fun x => ?_
      let s :=
        (t ⊓ memB v E) ⊓ (memB x S ⊓ memB (opairB x v) F)
      change s ≤ relB Q v u
      have hu := iInf_le
        (fun w : AName A => ⨅ z : AName A,
          memB w S ⊓ memB (opairB w z) F ⇨ relB Q z u) x
      have hz := (iInf_le
        (fun z : AName A =>
          memB x S ⊓ memB (opairB x z) F ⇨ relB Q z u) v).trans' hu
      exact (le_himp_iff.mp hz).trans' <|
        le_inf (inf_le_left.trans (inf_le_left.trans inf_le_right))
          inf_le_right
    exact (isSupRelB_least y (graphImageB F S E) Q u).trans' <|
      le_inf (inf_le_left.trans inf_le_right) hupperu

/-- If `F` is a `Q`-supremum of directed `S`, then each value `F(x)` is
an `R`-supremum of the evaluation image of `S` at `x`. -/
theorem InternalReflexiveModel.eval_preserves_Q_sup
    (𝓜 : InternalReflexiveModel (A := A))
    (S F x y : AName.{u} A) :
    isDirectedRelB S 𝓜.C 𝓜.Q ⊓ memB F 𝓜.C ⊓ isSupRelB F S 𝓜.Q ⊓
        memB x 𝓜.D ⊓ memB y 𝓜.D ⊓ memB (opairB x y) F ≤
      isSupRelB y (graphImageB (evalAtGraph 𝓜 x) S 𝓜.D) 𝓜.R := by
  let t :=
    isDirectedRelB S 𝓜.C 𝓜.Q ⊓ memB F 𝓜.C ⊓ isSupRelB F S 𝓜.Q ⊓
      memB x 𝓜.D ⊓ memB y 𝓜.D ⊓ memB (opairB x y) F
  change t ≤
    isSupRelB y (graphImageB (evalAtGraph 𝓜 x) S 𝓜.D) 𝓜.R
  have htEq : t ≤ eqB F (pointwiseSupGraph 𝓜 S) :=
    (𝓜.isSupRelB_le_eqB_pointwiseSupGraph S F).trans' <|
      inf_le_left.trans (inf_le_left.trans inf_le_left)
  have hFy : t ≤ memB (opairB x y) F := inf_le_right
  have hP : t ≤ memB (opairB x y) (pointwiseSupGraph 𝓜 S) :=
    (memB_eqB_right F (opairB x y) (pointwiseSupGraph 𝓜 S)).trans' <|
      le_inf hFy htEq
  exact (𝓜.memB_pointwiseSupGraph_le S x y).trans' hP |>.trans
    inf_le_right

/-- Conversely, if `y` is the `R`-supremum of the evaluation image of
directed `S` at `x`, then `(x, y)` is an edge of any `Q`-supremum `F`. -/
theorem InternalReflexiveModel.le_memB_of_eval_Q_sup
    (𝓜 : InternalReflexiveModel (A := A))
    (S F x y : AName.{u} A) :
    isDirectedRelB S 𝓜.C 𝓜.Q ⊓ memB F 𝓜.C ⊓ isSupRelB F S 𝓜.Q ⊓
        memB x 𝓜.D ⊓ memB y 𝓜.D ⊓
        isSupRelB y (graphImageB (evalAtGraph 𝓜 x) S 𝓜.D) 𝓜.R ≤
      memB (opairB x y) F := by
  let t :=
    isDirectedRelB S 𝓜.C 𝓜.Q ⊓ memB F 𝓜.C ⊓ isSupRelB F S 𝓜.Q ⊓
      memB x 𝓜.D ⊓ memB y 𝓜.D ⊓
      isSupRelB y (graphImageB (evalAtGraph 𝓜 x) S 𝓜.D) 𝓜.R
  change t ≤ memB (opairB x y) F
  have htEq : t ≤ eqB F (pointwiseSupGraph 𝓜 S) :=
    (𝓜.isSupRelB_le_eqB_pointwiseSupGraph S F).trans' <|
      inf_le_left.trans (inf_le_left.trans inf_le_left)
  have hxD : t ≤ memB x 𝓜.D :=
    inf_le_left.trans (inf_le_left.trans inf_le_right)
  have hyD : t ≤ memB y 𝓜.D :=
    inf_le_left.trans inf_le_right
  have hsup : t ≤
      isSupRelB y (graphImageB (evalAtGraph 𝓜 x) S 𝓜.D) 𝓜.R :=
    inf_le_right
  have hP : t ≤ memB (opairB x y) (pointwiseSupGraph 𝓜 S) :=
    (𝓜.le_memB_pointwiseSupGraph S x y).trans' <|
      le_inf (le_inf hxD hyD) hsup
  exact (memB_eqB_right (pointwiseSupGraph 𝓜 S) (opairB x y) F).trans' <|
    le_inf hP (by rw [eqB_comm]; exact htEq)

/-- Edge membership in a `Q`-supremum is the evaluation-image supremum
statement, at the degree of directedness and support. -/
theorem InternalReflexiveModel.inf_memB_of_eval_Q_sup_eq
    (𝓜 : InternalReflexiveModel (A := A))
    (S F x y : AName.{u} A) :
    isDirectedRelB S 𝓜.C 𝓜.Q ⊓ memB F 𝓜.C ⊓ isSupRelB F S 𝓜.Q ⊓
        memB x 𝓜.D ⊓ memB y 𝓜.D ⊓ memB (opairB x y) F =
      isDirectedRelB S 𝓜.C 𝓜.Q ⊓ memB F 𝓜.C ⊓ isSupRelB F S 𝓜.Q ⊓
        memB x 𝓜.D ⊓ memB y 𝓜.D ⊓
        isSupRelB y (graphImageB (evalAtGraph 𝓜 x) S 𝓜.D) 𝓜.R := by
  apply le_antisymm
  · exact le_inf inf_le_left (𝓜.eval_preserves_Q_sup S F x y)
  · exact le_inf inf_le_left (𝓜.le_memB_of_eval_Q_sup S F x y)

/-- Packaged image-sup form: a `Q`-supremum evaluates to the displayed
supremum of the fixed-argument image. -/
theorem InternalReflexiveModel.evalAtGraph_mapsToSup_of_Q_sup
    (𝓜 : InternalReflexiveModel (A := A))
    (S F x y : AName.{u} A) :
    isDirectedRelB S 𝓜.C 𝓜.Q ⊓ memB F 𝓜.C ⊓ isSupRelB F S 𝓜.Q ⊓
        memB x 𝓜.D ⊓ memB (opairB x y) F ≤
      mapsToSupB (evalAtGraph 𝓜 x) S y 𝓜.R := by
  let t :=
    isDirectedRelB S 𝓜.C 𝓜.Q ⊓ memB F 𝓜.C ⊓ isSupRelB F S 𝓜.Q ⊓
      memB x 𝓜.D ⊓ memB (opairB x y) F
  change t ≤ mapsToSupB (evalAtGraph 𝓜 x) S y 𝓜.R
  have hxD : t ≤ memB x 𝓜.D :=
    inf_le_left.trans inf_le_right
  have hFy : t ≤ memB (opairB x y) F := inf_le_right
  have hFC : t ≤ memB F 𝓜.C :=
    inf_le_left.trans (inf_le_left.trans
      (inf_le_left.trans inf_le_right))
  have hyD : t ≤ memB y 𝓜.D :=
    (local_function_edge_le_codomain
      (hFC.trans (𝓜.mem_mapSpace_le_function F)) x y).trans' <|
      le_inf le_rfl hFy
  have hsup : t ≤
      isSupRelB y (graphImageB (evalAtGraph 𝓜 x) S 𝓜.D) 𝓜.R :=
    (𝓜.eval_preserves_Q_sup S F x y).trans' <|
      le_inf (le_inf inf_le_left hyD) inf_le_right
  exact (isSup_graphImageB_le_mapsToSupB
      (evalAtGraph 𝓜 x) S 𝓜.C 𝓜.D 𝓜.R y
      (hxD.trans (𝓜.evalAtGraph_le_isFunctionB x))).trans' <|
    le_inf le_rfl hsup

/-- Application rows are generalized elements at any common degree at which
both factors are. -/
theorem interpDKRelVal_app_isRelElementAt_at
    (𝓜 : InternalReflexiveModel (A := A))
    (V K : AName.{u} A) (hK : subsetB K 𝓜.D = ⊤)
    (hV : (oid V).IsTotal)
    (η : RelFun (oid V) (oid 𝓜.D))
    (P Q : LamDK V.idx K.idx) (a : A)
    (hP : IsRelElementAt 𝓜.D a
      (interpDKRelVal 𝓜 V K hK hV η P))
    (hQ : IsRelElementAt 𝓜.D a
      (interpDKRelVal 𝓜 V K hK hV η Q)) :
    IsRelElementAt 𝓜.D a
      (interpDKRelVal 𝓜 V K hK hV η (.app P Q)) := by
  let f := applyRelOfElements 𝓜 hP hQ
  have h := isRelElementAt_of_relFun
    (f.at (PUnit.unit, PUnit.unit))
  change IsRelElementAt 𝓜.D (a ⊓ a)
    (fun d => f.val (PUnit.unit, PUnit.unit) d) at h
  have heval :
      interpDKRelVal 𝓜 V K hK hV η (.app P Q) =
        fun d => f.val (PUnit.unit, PUnit.unit) d := by
    funext d
    rw [interpDKRelVal_app]
    exact (applyRelOfElements_val 𝓜 hP hQ
      (PUnit.unit, PUnit.unit) d).symm
  rw [heval]
  simpa [inf_idem] using h

/-- Every updated app row is a generalized element at the active degree. -/
theorem interpDKBodyGraph_app_rows_isRelElementAt
    (𝓜 : InternalReflexiveModel (A := A))
    (V K : AName.{u} A) (hK : subsetB K 𝓜.D = ⊤)
    (hV : (oid V).IsTotal)
    (η : RelFun (oid V) (oid 𝓜.D))
    (x : V.idx) (P Q : LamDK V.idx K.idx) (a : A)
    (hP : ∀ d, IsRelElementAt 𝓜.D a
      (interpDKRelVal 𝓜 V K hK hV
        (η.update hV 𝓜.total x d) P))
    (hQ : ∀ d, IsRelElementAt 𝓜.D a
      (interpDKRelVal 𝓜 V K hK hV
        (η.update hV 𝓜.total x d) Q)) :
    ∀ d, IsRelElementAt 𝓜.D a
      (interpDKRelVal 𝓜 V K hK hV
        (η.update hV 𝓜.total x d) (.app P Q)) :=
  fun d =>
    interpDKRelVal_app_isRelElementAt_at 𝓜 V K hK hV
      (η.update hV 𝓜.total x d) P Q a (hP d) (hQ d)

/-- Rowwise generalized elements make an evaluator body graph a
degree-local internal function `D → D`. -/
theorem interpDKBodyGraph_le_isFunctionB
    (𝓜 : InternalReflexiveModel (A := A))
    (V K : AName.{u} A) (hK : subsetB K 𝓜.D = ⊤)
    (hV : (oid V).IsTotal)
    (η : RelFun (oid V) (oid 𝓜.D))
    (x : V.idx) (P : LamDK V.idx K.idx) (a : A)
    (hP : ∀ d, IsRelElementAt 𝓜.D a
      (interpDKRelVal 𝓜 V K hK hV
        (η.update hV 𝓜.total x d) P)) :
    a ≤ isFunctionB
      (interpDKBodyGraph 𝓜 V K hK hV η x P) 𝓜.D 𝓜.D := by
  let F := interpDKBodyGraph 𝓜 V K hK hV η x P
  let r (d : 𝓜.D.idx) :=
    interpDKRelVal 𝓜 V K hK hV (η.update hV 𝓜.total x d) P
  unfold isFunctionB
  refine le_inf (le_inf ?_ ?_) ?_
  · unfold interpDKBodyGraph
    rw [subsetB_mk]
    refine le_iInf fun p => ?_
    rw [le_himp_iff, memB_opairB_prodB]
    have hp : r p.1 p.2 ≤ memB (𝓜.D.child p.2) 𝓜.D := by
      have h := (hP p.1).2.1 p.2 |>.trans inf_le_right
      rwa [oid_eps] at h
    have hi : memB (𝓜.D.child p.1) 𝓜.D = ⊤ := by
      rw [← oid_eps]
      exact 𝓜.total p.1
    rw [hi, top_inf_eq]
    exact inf_le_right.trans hp
  · refine le_iInf fun u => le_iInf fun v => le_iInf fun w => ?_
    rw [le_himp_iff]
    unfold interpDKBodyGraph
    rw [memB_mk, memB_mk, inf_iSup_eq]
    rw [inf_iSup_eq]
    apply iSup_le
    intro pair
    rw [← inf_assoc, inf_iSup_eq]
    rw [iSup_inf_eq]
    apply iSup_le
    intro pair'
    rw [eqB_opairB, eqB_opairB]
    let t :=
      a ⊓
        (eqB u (𝓜.D.child pair'.1) ⊓ eqB v (𝓜.D.child pair'.2) ⊓
          r pair'.1 pair'.2) ⊓
        (eqB u (𝓜.D.child pair.1) ⊓ eqB w (𝓜.D.child pair.2) ⊓
          r pair.1 pair.2)
    change t ≤ eqB v w
    have hvu : t ≤ eqB v (𝓜.D.child pair'.2) :=
      inf_le_left.trans (inf_le_right.trans
        (inf_le_left.trans inf_le_right))
    have hwu : t ≤ eqB (𝓜.D.child pair.2) w := by
      have h : t ≤ eqB w (𝓜.D.child pair.2) :=
        inf_le_right.trans (inf_le_left.trans inf_le_right)
      rwa [eqB_comm] at h
    have hsrc : t ≤ (oid 𝓜.D).eq pair'.1 pair.1 := by
      rw [oid_eq_of_total 𝓜.D 𝓜.total]
      have h1 : t ≤ eqB u (𝓜.D.child pair'.1) :=
        inf_le_left.trans (inf_le_right.trans
          (inf_le_left.trans inf_le_left))
      have h2 : t ≤ eqB u (𝓜.D.child pair.1) :=
        inf_le_right.trans (inf_le_left.trans inf_le_left)
      exact (eqB_trans (𝓜.D.child pair'.1) u (𝓜.D.child pair.1)).trans' <|
        le_inf (by rw [eqB_comm]; exact h1) h2
    have hval' : t ≤ r pair'.1 pair'.2 :=
      inf_le_left.trans (inf_le_right.trans inf_le_right)
    have hparam :
        (oid 𝓜.D).eq pair'.1 pair.1 ⊓ r pair'.1 pair'.2 ≤
          r pair.1 pair'.2 :=
      interpDKRelVal_isPointwiseFamily 𝓜 V K hK hV
        (oid 𝓜.D)
        (fun q => η.update hV 𝓜.total x q)
        (RelFun.isPointwiseFamily_update η hV 𝓜.total x)
        P pair'.1 pair.1 pair'.2
    have htransp : t ≤ r pair.1 pair'.2 :=
      hparam.trans' (le_inf hsrc hval')
    have hval : t ≤ r pair.1 pair.2 :=
      inf_le_right.trans inf_le_right
    have hout : t ≤ (oid 𝓜.D).eq pair'.2 pair.2 :=
      (hP pair.1).2.2.1 pair'.2 pair.2 |>.trans' (le_inf htransp hval)
    have hvw : t ≤ eqB (𝓜.D.child pair'.2) (𝓜.D.child pair.2) := by
      rw [oid_eq_of_total 𝓜.D 𝓜.total] at hout
      exact hout
    exact (eqB_trans v (𝓜.D.child pair'.2) w).trans' <|
      le_inf hvu <|
        (eqB_trans (𝓜.D.child pair'.2) (𝓜.D.child pair.2) w).trans' <|
          le_inf hvw hwu
  · refine le_iInf fun u => ?_
    rw [le_himp_iff, memB_eq (x := u) (y := 𝓜.D), inf_iSup_eq]
    refine iSup_le fun i => ?_
    refine (le_inf le_rfl (inf_le_left.trans (hP i).2.2.2)).trans ?_
    rw [inf_iSup_eq]
    refine iSup_le fun j => le_iSup_of_le (𝓜.D.child j) ?_
    let s :=
      (a ⊓ (eqB u (𝓜.D.child i) ⊓ 𝓜.D.val i)) ⊓ r i j
    change s ≤ memB (opairB u (𝓜.D.child j)) F
    have hval : s ≤ memB
        (opairB (𝓜.D.child i) (𝓜.D.child j)) F :=
      (val_le_memB F (i, j)).trans' inf_le_right
    exact (memB_opairB_congr F (𝓜.D.child i) u
        (𝓜.D.child j) (𝓜.D.child j)).trans' <|
      le_inf (le_inf
          (by
            have h : s ≤ eqB u (𝓜.D.child i) :=
              inf_le_left.trans (inf_le_right.trans inf_le_left)
            rw [eqB_comm]
            exact h)
          (le_top.trans (eqB_self (A := A) (𝓜.D.child j)).ge))
        hval

/-- The application body graph is a degree-local internal function. -/
theorem interpDKBodyGraph_app_le_isFunctionB
    (𝓜 : InternalReflexiveModel (A := A))
    (V K : AName.{u} A) (hK : subsetB K 𝓜.D = ⊤)
    (hV : (oid V).IsTotal)
    (η : RelFun (oid V) (oid 𝓜.D))
    (x : V.idx) (P Q : LamDK V.idx K.idx) (a : A)
    (hP : ∀ d, IsRelElementAt 𝓜.D a
      (interpDKRelVal 𝓜 V K hK hV
        (η.update hV 𝓜.total x d) P))
    (hQ : ∀ d, IsRelElementAt 𝓜.D a
      (interpDKRelVal 𝓜 V K hK hV
        (η.update hV 𝓜.total x d) Q)) :
    a ≤ isFunctionB
      (interpDKBodyGraph 𝓜 V K hK hV η x (.app P Q))
      𝓜.D 𝓜.D :=
  interpDKBodyGraph_le_isFunctionB 𝓜 V K hK hV η x (.app P Q) a
    (interpDKBodyGraph_app_rows_isRelElementAt
      𝓜 V K hK hV η x P Q a hP hQ)

/-- An application-body edge decomposes into evaluation of `P`, application
of `Fun`, and evaluation of that map at the value of `Q`. -/
theorem interpDKBodyGraph_app_mem_decompose
    (𝓜 : InternalReflexiveModel (A := A))
    (V K : AName.{u} A) (hK : subsetB K 𝓜.D = ⊤)
    (hV : (oid V).IsTotal)
    (η : RelFun (oid V) (oid 𝓜.D))
    (x : V.idx) (P Q : LamDK V.idx K.idx) (a : A)
    (u v : AName.{u} A) :
    a ⊓ memB (opairB u v)
        (interpDKBodyGraph 𝓜 V K hK hV η x (.app P Q)) ≤
      ⨆ p : AName A, ⨆ q : AName A, ⨆ c : AName A,
        memB (opairB u p)
          (interpDKBodyGraph 𝓜 V K hK hV η x P) ⊓
        memB (opairB u q)
          (interpDKBodyGraph 𝓜 V K hK hV η x Q) ⊓
        memB (opairB p c) 𝓜.Fun ⊓
        memB c 𝓜.C ⊓
        memB (opairB q v) c := by
  unfold interpDKBodyGraph
  rw [memB_mk, inf_iSup_eq]
  refine iSup_le fun pair => ?_
  rw [eqB_opairB, interpDKRelVal_app]
  rw [← inf_assoc, inf_iSup_eq]
  refine iSup_le fun ci => ?_
  rw [inf_iSup_eq]
  refine iSup_le fun q' => ?_
  rw [inf_iSup_eq]
  refine iSup_le fun pi => ?_
  rw [inf_iSup_eq]
  refine iSup_le fun qi =>
    le_iSup_of_le (𝓜.D.child pi) <|
      le_iSup_of_le (𝓜.D.child qi) <|
      le_iSup_of_le (𝓜.C.child ci) ?_
  let t :=
    (a ⊓ (eqB u (𝓜.D.child pair.1) ⊓ eqB v (𝓜.D.child pair.2))) ⊓
      (interpDKRelVal 𝓜 V K hK hV
          (η.update hV 𝓜.total x pair.1) P pi ⊓
        interpDKRelVal 𝓜 V K hK hV
          (η.update hV 𝓜.total x pair.1) Q qi ⊓
        memB (opairB (𝓜.D.child pi) (𝓜.C.child ci)) 𝓜.Fun ⊓
        (oid 𝓜.D).eq qi q' ⊓
        memB (𝓜.C.child ci) 𝓜.C ⊓
        memB (opairB (𝓜.D.child q') (𝓜.D.child pair.2))
          (𝓜.C.child ci))
  change t ≤
    memB (opairB u (𝓜.D.child pi))
        (interpDKBodyGraph 𝓜 V K hK hV η x P) ⊓
      memB (opairB u (𝓜.D.child qi))
        (interpDKBodyGraph 𝓜 V K hK hV η x Q) ⊓
      memB (opairB (𝓜.D.child pi) (𝓜.C.child ci)) 𝓜.Fun ⊓
      memB (𝓜.C.child ci) 𝓜.C ⊓
      memB (opairB (𝓜.D.child qi) v) (𝓜.C.child ci)
  have hPval : t ≤
      memB (opairB (𝓜.D.child pair.1) (𝓜.D.child pi))
        (interpDKBodyGraph 𝓜 V K hK hV η x P) :=
    (val_le_memB
        (interpDKBodyGraph 𝓜 V K hK hV η x P) (pair.1, pi)).trans' <|
      inf_le_right.trans (inf_le_left.trans
        (inf_le_left.trans (inf_le_left.trans
          (inf_le_left.trans inf_le_left))))
  have hQval : t ≤
      memB (opairB (𝓜.D.child pair.1) (𝓜.D.child qi))
        (interpDKBodyGraph 𝓜 V K hK hV η x Q) :=
    (val_le_memB
        (interpDKBodyGraph 𝓜 V K hK hV η x Q) (pair.1, qi)).trans' <|
      inf_le_right.trans (inf_le_left.trans
        (inf_le_left.trans (inf_le_left.trans
          (inf_le_left.trans inf_le_right))))
  have hu : t ≤ eqB (𝓜.D.child pair.1) u := by
    have h : t ≤ eqB u (𝓜.D.child pair.1) :=
      inf_le_left.trans (inf_le_right.trans inf_le_left)
    rwa [eqB_comm] at h
  have hPedge : t ≤
      memB (opairB u (𝓜.D.child pi))
        (interpDKBodyGraph 𝓜 V K hK hV η x P) :=
    (memB_opairB_congr
        (interpDKBodyGraph 𝓜 V K hK hV η x P)
        (𝓜.D.child pair.1) u
        (𝓜.D.child pi) (𝓜.D.child pi)).trans' <|
      le_inf (le_inf hu
          (le_top.trans (eqB_self (A := A) (𝓜.D.child pi)).ge))
        hPval
  have hQedge : t ≤
      memB (opairB u (𝓜.D.child qi))
        (interpDKBodyGraph 𝓜 V K hK hV η x Q) :=
    (memB_opairB_congr
        (interpDKBodyGraph 𝓜 V K hK hV η x Q)
        (𝓜.D.child pair.1) u
        (𝓜.D.child qi) (𝓜.D.child qi)).trans' <|
      le_inf (le_inf hu
          (le_top.trans (eqB_self (A := A) (𝓜.D.child qi)).ge))
        hQval
  have hFun : t ≤
      memB (opairB (𝓜.D.child pi) (𝓜.C.child ci)) 𝓜.Fun :=
    inf_le_right.trans (inf_le_left.trans
      (inf_le_left.trans (inf_le_left.trans inf_le_right)))
  have hC : t ≤ memB (𝓜.C.child ci) 𝓜.C :=
    inf_le_right.trans (inf_le_left.trans inf_le_right)
  have heval0 : t ≤
      memB (opairB (𝓜.D.child q') (𝓜.D.child pair.2))
        (𝓜.C.child ci) :=
    inf_le_right.trans inf_le_right
  have hqq' : t ≤ eqB (𝓜.D.child q') (𝓜.D.child qi) := by
    have h : t ≤ (oid 𝓜.D).eq qi q' :=
      inf_le_right.trans (inf_le_left.trans
        (inf_le_left.trans inf_le_right))
    rw [oid_eq_of_total 𝓜.D 𝓜.total, eqB_comm] at h
    exact h
  have hv : t ≤ eqB (𝓜.D.child pair.2) v := by
    have h : t ≤ eqB v (𝓜.D.child pair.2) :=
      inf_le_left.trans (inf_le_right.trans inf_le_right)
    rwa [eqB_comm] at h
  have heval : t ≤
      memB (opairB (𝓜.D.child qi) v) (𝓜.C.child ci) :=
    (memB_opairB_congr (𝓜.C.child ci)
        (𝓜.D.child q') (𝓜.D.child qi)
        (𝓜.D.child pair.2) v).trans' <|
      le_inf (le_inf hqq' hv) heval0
  exact le_inf (le_inf (le_inf (le_inf hPedge hQedge) hFun) hC) heval

/-- Converse of `interpDKBodyGraph_app_mem_decompose`: semantic components
rebuild an application-body edge. -/
theorem interpDKBodyGraph_app_mem_of_components
    (𝓜 : InternalReflexiveModel (A := A))
    (V K : AName.{u} A) (hK : subsetB K 𝓜.D = ⊤)
    (hV : (oid V).IsTotal)
    (η : RelFun (oid V) (oid 𝓜.D))
    (x : V.idx) (P Q : LamDK V.idx K.idx) (a : A)
    (hP : ∀ d, IsRelElementAt 𝓜.D a
      (interpDKRelVal 𝓜 V K hK hV
        (η.update hV 𝓜.total x d) P))
    (hQ : ∀ d, IsRelElementAt 𝓜.D a
      (interpDKRelVal 𝓜 V K hK hV
        (η.update hV 𝓜.total x d) Q))
    (u v p q c : AName.{u} A) :
    a ⊓ memB (opairB u p)
        (interpDKBodyGraph 𝓜 V K hK hV η x P) ⊓
      memB (opairB u q)
        (interpDKBodyGraph 𝓜 V K hK hV η x Q) ⊓
      memB (opairB p c) 𝓜.Fun ⊓
      memB c 𝓜.C ⊓
      memB (opairB q v) c ≤
    memB (opairB u v)
      (interpDKBodyGraph 𝓜 V K hK hV η x (.app P Q)) := by
  let FP := interpDKBodyGraph 𝓜 V K hK hV η x P
  let FQ := interpDKBodyGraph 𝓜 V K hK hV η x Q
  let t :=
    a ⊓ memB (opairB u p) FP ⊓ memB (opairB u q) FQ ⊓
      memB (opairB p c) 𝓜.Fun ⊓ memB c 𝓜.C ⊓
      memB (opairB q v) c
  change t ≤ memB (opairB u v)
    (interpDKBodyGraph 𝓜 V K hK hV η x (.app P Q))
  have htA : t ≤ a :=
    inf_le_left.trans (inf_le_left.trans
      (inf_le_left.trans (inf_le_left.trans inf_le_left)))
  have htFP : t ≤ memB (opairB u p) FP :=
    inf_le_left.trans (inf_le_left.trans
      (inf_le_left.trans (inf_le_left.trans inf_le_right)))
  have htFQ : t ≤ memB (opairB u q) FQ :=
    inf_le_left.trans (inf_le_left.trans
      (inf_le_left.trans inf_le_right))
  have htFun : t ≤ memB (opairB p c) 𝓜.Fun :=
    inf_le_left.trans (inf_le_left.trans inf_le_right)
  have htC : t ≤ memB c 𝓜.C :=
    inf_le_left.trans inf_le_right
  have htEval : t ≤ memB (opairB q v) c :=
    inf_le_right
  have hfunP : a ≤ isFunctionB FP 𝓜.D 𝓜.D :=
    interpDKBodyGraph_le_isFunctionB 𝓜 V K hK hV η x P a hP
  have hfunQ : a ≤ isFunctionB FQ 𝓜.D 𝓜.D :=
    interpDKBodyGraph_le_isFunctionB 𝓜 V K hK hV η x Q a hQ
  have huD : t ≤ memB u 𝓜.D :=
    (local_function_edge_le_domain (htA.trans hfunP) u p).trans' <|
      le_inf le_rfl htFP
  have hpD : t ≤ memB p 𝓜.D :=
    (local_function_edge_le_codomain (htA.trans hfunP) u p).trans' <|
      le_inf le_rfl htFP
  have hqD : t ≤ memB q 𝓜.D :=
    (local_function_edge_le_codomain (htA.trans hfunQ) u q).trans' <|
      le_inf le_rfl htFQ
  have hfunC : t ≤ isFunctionB c 𝓜.D 𝓜.D :=
    (𝓜.mem_mapSpace_le_function c).trans' htC
  have hvD : t ≤ memB v 𝓜.D :=
    (local_function_edge_le_codomain hfunC q v).trans' <|
      le_inf le_rfl htEval
  refine (le_inf le_rfl huD).trans ?_
  rw [memB_eq (x := u) (y := 𝓜.D), inf_iSup_eq]
  refine iSup_le fun i => ?_
  let t1 := t ⊓ (eqB u (𝓜.D.child i) ⊓ 𝓜.D.val i)
  refine (le_inf le_rfl (inf_le_left.trans hpD)).trans ?_
  rw [memB_eq (x := p) (y := 𝓜.D), inf_iSup_eq]
  refine iSup_le fun pi => ?_
  let t2 := t1 ⊓ (eqB p (𝓜.D.child pi) ⊓ 𝓜.D.val pi)
  refine (le_inf le_rfl
      (inf_le_left.trans (inf_le_left.trans hqD))).trans ?_
  rw [memB_eq (x := q) (y := 𝓜.D), inf_iSup_eq]
  refine iSup_le fun qi => ?_
  let t3 := t2 ⊓ (eqB q (𝓜.D.child qi) ⊓ 𝓜.D.val qi)
  refine (le_inf le_rfl
      (inf_le_left.trans (inf_le_left.trans
        (inf_le_left.trans hvD)))).trans ?_
  rw [memB_eq (x := v) (y := 𝓜.D), inf_iSup_eq]
  refine iSup_le fun e => ?_
  let t4 := t3 ⊓ (eqB v (𝓜.D.child e) ⊓ 𝓜.D.val e)
  refine (le_inf le_rfl
      (inf_le_left.trans (inf_le_left.trans
        (inf_le_left.trans (inf_le_left.trans htC))))).trans ?_
  rw [memB_eq (x := c) (y := 𝓜.C), inf_iSup_eq]
  refine iSup_le fun ci => ?_
  let t5 := t4 ⊓ (eqB c (𝓜.C.child ci) ⊓ 𝓜.C.val ci)
  change t5 ≤ memB (opairB u v)
    (interpDKBodyGraph 𝓜 V K hK hV η x (.app P Q))
  have ht5t : t5 ≤ t :=
    inf_le_left.trans (inf_le_left.trans
      (inf_le_left.trans (inf_le_left.trans inf_le_left)))
  have ht5A : t5 ≤ a := ht5t.trans htA
  have huEq : t5 ≤ eqB u (𝓜.D.child i) :=
    inf_le_left.trans (inf_le_left.trans
      (inf_le_left.trans (inf_le_left.trans
        (inf_le_right.trans inf_le_left))))
  have hpEq : t5 ≤ eqB p (𝓜.D.child pi) :=
    inf_le_left.trans (inf_le_left.trans
      (inf_le_left.trans (inf_le_right.trans inf_le_left)))
  have hqEq : t5 ≤ eqB q (𝓜.D.child qi) :=
    inf_le_left.trans (inf_le_left.trans
      (inf_le_right.trans inf_le_left))
  have hvEq : t5 ≤ eqB v (𝓜.D.child e) :=
    inf_le_left.trans (inf_le_right.trans inf_le_left)
  have hcEq : t5 ≤ eqB c (𝓜.C.child ci) :=
    inf_le_right.trans inf_le_left
  have hFPch : t5 ≤
      memB (opairB (𝓜.D.child i) (𝓜.D.child pi)) FP :=
    (memB_opairB_congr FP u (𝓜.D.child i) p (𝓜.D.child pi)).trans' <|
      le_inf (le_inf huEq hpEq) (ht5t.trans htFP)
  have hFQch : t5 ≤
      memB (opairB (𝓜.D.child i) (𝓜.D.child qi)) FQ :=
    (memB_opairB_congr FQ u (𝓜.D.child i) q (𝓜.D.child qi)).trans' <|
      le_inf (le_inf huEq hqEq) (ht5t.trans htFQ)
  have hPraw : t5 ≤
      interpDKRelVal 𝓜 V K hK hV
        (η.update hV 𝓜.total x i) P pi := by
    rw [← inf_memB_interpDKBodyGraph_eq 𝓜 V K hK hV η x P a hP i pi]
    exact le_inf ht5A hFPch
  have hQraw : t5 ≤
      interpDKRelVal 𝓜 V K hK hV
        (η.update hV 𝓜.total x i) Q qi := by
    rw [← inf_memB_interpDKBodyGraph_eq 𝓜 V K hK hV η x Q a hQ i qi]
    exact le_inf ht5A hFQch
  have hFunch : t5 ≤
      memB (opairB (𝓜.D.child pi) (𝓜.C.child ci)) 𝓜.Fun :=
    (memB_opairB_congr 𝓜.Fun p (𝓜.D.child pi) c (𝓜.C.child ci)).trans' <|
      le_inf (le_inf hpEq hcEq) (ht5t.trans htFun)
  have hCch : t5 ≤ memB (𝓜.C.child ci) 𝓜.C :=
    (val_le_memB 𝓜.C ci).trans' (inf_le_right.trans inf_le_right)
  have heval : t5 ≤
      memB (opairB (𝓜.D.child qi) (𝓜.D.child e))
        (𝓜.C.child ci) := by
    have h0 : t5 ≤ memB (opairB q v) (𝓜.C.child ci) :=
      (memB_eqB_right c (opairB q v) (𝓜.C.child ci)).trans' <|
        le_inf (ht5t.trans htEval) hcEq
    exact (memB_opairB_congr (𝓜.C.child ci)
        q (𝓜.D.child qi) v (𝓜.D.child e)).trans' <|
      le_inf (le_inf hqEq hvEq) h0
  have hqq : t5 ≤ (oid 𝓜.D).eq qi qi := by
    rw [oid_eq_of_total 𝓜.D 𝓜.total]
    exact le_top.trans (eqB_self (A := A) (𝓜.D.child qi)).ge
  unfold interpDKBodyGraph
  rw [memB_mk]
  refine le_iSup_of_le (i, e) ?_
  rw [eqB_opairB, interpDKRelVal_app]
  refine le_inf (le_inf huEq hvEq)
    (le_iSup_of_le ci <| le_iSup_of_le qi <|
      le_iSup_of_le pi <| le_iSup_of_le qi ?_)
  exact le_inf (le_inf (le_inf (le_inf (le_inf hPraw hQraw) hFunch)
    hqq) hCch) heval

/-- Application is jointly monotone in the `P`-value and the `Q`-value:
`Fun(P(s))(Q(t)) ≤ Fun(P(s'))(Q(t'))` whenever `s ≤ s'` and `t ≤ t'`. -/
theorem interpDKBodyGraph_app_bi_mono
    (𝓜 : InternalReflexiveModel (A := A))
    (V K : AName.{u} A) (hK : subsetB K 𝓜.D = ⊤)
    (hV : (oid V).IsTotal)
    (η : RelFun (oid V) (oid 𝓜.D))
    (x : V.idx) (P Q : LamDK V.idx K.idx) (a : A)
    (hPsc : a ≤ isScottContinuousB
      (interpDKBodyGraph 𝓜 V K hK hV η x P) 𝓜.D 𝓜.D 𝓜.R 𝓜.R)
    (hQsc : a ≤ isScottContinuousB
      (interpDKBodyGraph 𝓜 V K hK hV η x Q) 𝓜.D 𝓜.D 𝓜.R 𝓜.R)
    (s s' t t' p p' q q' c c' y y' : AName.{u} A) :
    a ⊓
        (memB (opairB s p)
          (interpDKBodyGraph 𝓜 V K hK hV η x P) ⊓
          memB (opairB s' p')
            (interpDKBodyGraph 𝓜 V K hK hV η x P) ⊓
          relB 𝓜.R s s') ⊓
        (memB (opairB t q)
          (interpDKBodyGraph 𝓜 V K hK hV η x Q) ⊓
          memB (opairB t' q')
            (interpDKBodyGraph 𝓜 V K hK hV η x Q) ⊓
          relB 𝓜.R t t') ⊓
        (memB (opairB p c) 𝓜.Fun ⊓
          memB (opairB p' c') 𝓜.Fun) ⊓
        (memB (opairB q y) c ⊓
          memB (opairB q' y') c') ≤
      relB 𝓜.R y y' := by
  let FP := interpDKBodyGraph 𝓜 V K hK hV η x P
  let FQ := interpDKBodyGraph 𝓜 V K hK hV η x Q
  let u :=
    a ⊓
      (memB (opairB s p) FP ⊓
        memB (opairB s' p') FP ⊓
        relB 𝓜.R s s') ⊓
      (memB (opairB t q) FQ ⊓
        memB (opairB t' q') FQ ⊓
        relB 𝓜.R t t') ⊓
      (memB (opairB p c) 𝓜.Fun ⊓
        memB (opairB p' c') 𝓜.Fun) ⊓
      (memB (opairB q y) c ⊓
        memB (opairB q' y') c')
  change u ≤ relB 𝓜.R y y'
  have ha : u ≤ a :=
    inf_le_left.trans (inf_le_left.trans
      (inf_le_left.trans inf_le_left))
  have hPgrp : u ≤
      memB (opairB s p) FP ⊓
        memB (opairB s' p') FP ⊓
        relB 𝓜.R s s' :=
    inf_le_left.trans (inf_le_left.trans
      (inf_le_left.trans inf_le_right))
  have hQgrp : u ≤
      memB (opairB t q) FQ ⊓
        memB (opairB t' q') FQ ⊓
        relB 𝓜.R t t' :=
    inf_le_left.trans (inf_le_left.trans inf_le_right)
  have hFgrp : u ≤
      memB (opairB p c) 𝓜.Fun ⊓
        memB (opairB p' c') 𝓜.Fun :=
    inf_le_left.trans inf_le_right
  have hEgrp : u ≤
      memB (opairB q y) c ⊓
        memB (opairB q' y') c' :=
    inf_le_right
  have hsp : u ≤ memB (opairB s p) FP :=
    hPgrp.trans (inf_le_left.trans inf_le_left)
  have hsp' : u ≤ memB (opairB s' p') FP :=
    hPgrp.trans (inf_le_left.trans inf_le_right)
  have hss' : u ≤ relB 𝓜.R s s' :=
    hPgrp.trans inf_le_right
  have htq : u ≤ memB (opairB t q) FQ :=
    hQgrp.trans (inf_le_left.trans inf_le_left)
  have htq' : u ≤ memB (opairB t' q') FQ :=
    hQgrp.trans (inf_le_left.trans inf_le_right)
  have htt' : u ≤ relB 𝓜.R t t' :=
    hQgrp.trans inf_le_right
  have hpc : u ≤ memB (opairB p c) 𝓜.Fun :=
    hFgrp.trans inf_le_left
  have hpc' : u ≤ memB (opairB p' c') 𝓜.Fun :=
    hFgrp.trans inf_le_right
  have hqy : u ≤ memB (opairB q y) c :=
    hEgrp.trans inf_le_left
  have hqy' : u ≤ memB (opairB q' y') c' :=
    hEgrp.trans inf_le_right
  have hpp' : u ≤ relB 𝓜.R p p' :=
    (scottContinuous_apply_mono hPsc s s' p p').trans' <|
      le_inf (le_inf (le_inf ha hsp) hsp') hss'
  have hFunsc : (⊤ : A) ≤
      isScottContinuousB 𝓜.Fun 𝓜.D 𝓜.C 𝓜.R 𝓜.Q :=
    le_top.trans 𝓜.fun_continuous.ge
  have hcc' : u ≤ relB 𝓜.Q c c' :=
    (scottContinuous_apply_mono hFunsc p p' c c').trans' <|
      le_inf (le_inf (le_inf (le_top.trans le_top) hpc) hpc') hpp'
  have hqq' : u ≤ relB 𝓜.R q q' :=
    (scottContinuous_apply_mono hQsc t t' q q').trans' <|
      le_inf (le_inf (le_inf ha htq) htq') htt'
  have hcC : u ≤ memB c 𝓜.C :=
    (local_function_edge_le_codomain
        (le_top.trans 𝓜.fun_function.ge) p c).trans' <|
      le_inf (le_top.trans le_top) hpc
  have hc'C : u ≤ memB c' 𝓜.C :=
    (local_function_edge_le_codomain
        (le_top.trans 𝓜.fun_function.ge) p' c').trans' <|
      le_inf (le_top.trans le_top) hpc'
  have hfun' : u ≤ isFunctionB c' 𝓜.D 𝓜.D :=
    (𝓜.mem_mapSpace_le_function c').trans' hc'C
  have hfunc : u ≤ isFunctionB c 𝓜.D 𝓜.D :=
    (𝓜.mem_mapSpace_le_function c).trans' hcC
  have hqD : u ≤ memB q 𝓜.D :=
    (local_function_edge_le_domain hfunc q y).trans' <|
      le_inf le_rfl hqy
  have htot : u ≤ ⨆ w : AName A, memB (opairB q w) c' :=
    (isTotalB_apply c' 𝓜.D q).trans' <|
      le_inf (hfun'.trans inf_le_right) hqD
  refine (le_inf le_rfl htot).trans ?_
  rw [inf_iSup_eq]
  refine iSup_le fun w => ?_
  let sw := u ⊓ memB (opairB q w) c'
  change sw ≤ relB 𝓜.R y y'
  have hswu : sw ≤ u := inf_le_left
  have hqw : sw ≤ memB (opairB q w) c' := inf_le_right
  have hyw : sw ≤ relB 𝓜.R y w :=
    (𝓜.relQ_apply c c' q y w).trans' <|
      le_inf
        (le_inf (le_inf (hswu.trans hcC) (hswu.trans hc'C))
          (hswu.trans hcc'))
        (le_inf (le_inf (hswu.trans hqD) (hswu.trans hqy)) hqw)
  have hwy' : sw ≤ relB 𝓜.R w y' :=
    (𝓜.mem_mapSpace_apply_mono c' q q' w y').trans' <|
      le_inf (le_inf (le_inf (hswu.trans hc'C) hqw)
        (hswu.trans hqy'))
        (hswu.trans hqq')
  exact (𝓜.relR_trans y w y').trans' (le_inf hyw hwy')

/-- Degree-local monotonicity of the application body graph. -/
theorem interpDKBodyGraph_app_apply_mono
    (𝓜 : InternalReflexiveModel (A := A))
    (V K : AName.{u} A) (hK : subsetB K 𝓜.D = ⊤)
    (hV : (oid V).IsTotal)
    (η : RelFun (oid V) (oid 𝓜.D))
    (x : V.idx) (P Q : LamDK V.idx K.idx) (a : A)
    (hPsc : a ≤ isScottContinuousB
      (interpDKBodyGraph 𝓜 V K hK hV η x P) 𝓜.D 𝓜.D 𝓜.R 𝓜.R)
    (hQsc : a ≤ isScottContinuousB
      (interpDKBodyGraph 𝓜 V K hK hV η x Q) 𝓜.D 𝓜.D 𝓜.R 𝓜.R)
    (u u' v v' : AName.{u} A) :
    a ⊓ memB (opairB u v)
        (interpDKBodyGraph 𝓜 V K hK hV η x (.app P Q)) ⊓
      memB (opairB u' v')
        (interpDKBodyGraph 𝓜 V K hK hV η x (.app P Q)) ⊓
      relB 𝓜.R u u' ≤
    relB 𝓜.R v v' := by
  let Fapp := interpDKBodyGraph 𝓜 V K hK hV η x (.app P Q)
  let t0 :=
    a ⊓ memB (opairB u v) Fapp ⊓ memB (opairB u' v') Fapp ⊓
      relB 𝓜.R u u'
  change t0 ≤ relB 𝓜.R v v'
  have ht0A : t0 ≤ a :=
    inf_le_left.trans (inf_le_left.trans inf_le_left)
  have ht0uv : t0 ≤ memB (opairB u v) Fapp :=
    inf_le_left.trans (inf_le_left.trans inf_le_right)
  have ht0u'v' : t0 ≤ memB (opairB u' v') Fapp :=
    inf_le_left.trans inf_le_right
  have hdec :
      t0 ≤ ⨆ p : AName A, ⨆ q : AName A, ⨆ c : AName A,
        memB (opairB u p)
          (interpDKBodyGraph 𝓜 V K hK hV η x P) ⊓
        memB (opairB u q)
          (interpDKBodyGraph 𝓜 V K hK hV η x Q) ⊓
        memB (opairB p c) 𝓜.Fun ⊓
        memB c 𝓜.C ⊓
        memB (opairB q v) c :=
    (interpDKBodyGraph_app_mem_decompose
        𝓜 V K hK hV η x P Q a u v).trans' <|
      le_inf ht0A ht0uv
  refine (le_inf le_rfl hdec).trans ?_
  rw [inf_iSup_eq]
  refine iSup_le fun p => ?_
  rw [inf_iSup_eq]
  refine iSup_le fun q => ?_
  rw [inf_iSup_eq]
  refine iSup_le fun c => ?_
  let t1 :=
    t0 ⊓
      (memB (opairB u p)
          (interpDKBodyGraph 𝓜 V K hK hV η x P) ⊓
        memB (opairB u q)
          (interpDKBodyGraph 𝓜 V K hK hV η x Q) ⊓
        memB (opairB p c) 𝓜.Fun ⊓
        memB c 𝓜.C ⊓
        memB (opairB q v) c)
  have hdec' :
      t1 ≤ ⨆ p' : AName A, ⨆ q' : AName A, ⨆ c' : AName A,
        memB (opairB u' p')
          (interpDKBodyGraph 𝓜 V K hK hV η x P) ⊓
        memB (opairB u' q')
          (interpDKBodyGraph 𝓜 V K hK hV η x Q) ⊓
        memB (opairB p' c') 𝓜.Fun ⊓
        memB c' 𝓜.C ⊓
        memB (opairB q' v') c' :=
    (interpDKBodyGraph_app_mem_decompose
        𝓜 V K hK hV η x P Q a u' v').trans' <|
      le_inf (inf_le_left.trans ht0A) (inf_le_left.trans ht0u'v')
  refine (le_inf le_rfl hdec').trans ?_
  rw [inf_iSup_eq]
  refine iSup_le fun p' => ?_
  rw [inf_iSup_eq]
  refine iSup_le fun q' => ?_
  rw [inf_iSup_eq]
  refine iSup_le fun c' => ?_
  let t2 :=
    t1 ⊓
      (memB (opairB u' p')
          (interpDKBodyGraph 𝓜 V K hK hV η x P) ⊓
        memB (opairB u' q')
          (interpDKBodyGraph 𝓜 V K hK hV η x Q) ⊓
        memB (opairB p' c') 𝓜.Fun ⊓
        memB c' 𝓜.C ⊓
        memB (opairB q' v') c')
  change t2 ≤ relB 𝓜.R v v'
  have ht2t0 : t2 ≤ t0 :=
    inf_le_left.trans inf_le_left
  have ht1φ : t2 ≤
      memB (opairB u p)
          (interpDKBodyGraph 𝓜 V K hK hV η x P) ⊓
        memB (opairB u q)
          (interpDKBodyGraph 𝓜 V K hK hV η x Q) ⊓
        memB (opairB p c) 𝓜.Fun ⊓
        memB c 𝓜.C ⊓
        memB (opairB q v) c :=
    inf_le_left.trans inf_le_right
  have ht2ψ : t2 ≤
      memB (opairB u' p')
          (interpDKBodyGraph 𝓜 V K hK hV η x P) ⊓
        memB (opairB u' q')
          (interpDKBodyGraph 𝓜 V K hK hV η x Q) ⊓
        memB (opairB p' c') 𝓜.Fun ⊓
        memB c' 𝓜.C ⊓
        memB (opairB q' v') c' :=
    inf_le_right
  exact (interpDKBodyGraph_app_bi_mono
      𝓜 V K hK hV η x P Q a hPsc hQsc
      u u' u u' p p' q q' c c' v v').trans' <|
    le_inf (le_inf (le_inf (le_inf
        (ht2t0.trans ht0A)
        (le_inf (le_inf
            (ht1φ.trans (inf_le_left.trans
              (inf_le_left.trans (inf_le_left.trans inf_le_left))))
            (ht2ψ.trans (inf_le_left.trans
              (inf_le_left.trans (inf_le_left.trans inf_le_left)))))
          (ht2t0.trans inf_le_right)))
        (le_inf (le_inf
            (ht1φ.trans (inf_le_left.trans
              (inf_le_left.trans (inf_le_left.trans inf_le_right))))
            (ht2ψ.trans (inf_le_left.trans
              (inf_le_left.trans (inf_le_left.trans inf_le_right)))))
          (ht2t0.trans inf_le_right)))
      (le_inf
        (ht1φ.trans (inf_le_left.trans
          (inf_le_left.trans inf_le_right)))
        (ht2ψ.trans (inf_le_left.trans
          (inf_le_left.trans inf_le_right)))))
      (le_inf
        (ht1φ.trans inf_le_right)
        (ht2ψ.trans inf_le_right))

/-- Directed-supremum preservation for the application body graph. -/
theorem interpDKBodyGraph_app_mapsToSup
    (𝓜 : InternalReflexiveModel (A := A))
    (V K : AName.{u} A) (hK : subsetB K 𝓜.D = ⊤)
    (hV : (oid V).IsTotal)
    (η : RelFun (oid V) (oid 𝓜.D))
    (x : V.idx) (P Q : LamDK V.idx K.idx) (a : A)
    (hfun : a ≤ isFunctionB
      (interpDKBodyGraph 𝓜 V K hK hV η x (.app P Q)) 𝓜.D 𝓜.D)
    (hPsc : a ≤ isScottContinuousB
      (interpDKBodyGraph 𝓜 V K hK hV η x P) 𝓜.D 𝓜.D 𝓜.R 𝓜.R)
    (hQsc : a ≤ isScottContinuousB
      (interpDKBodyGraph 𝓜 V K hK hV η x Q) 𝓜.D 𝓜.D 𝓜.R 𝓜.R)
    (S u v : AName.{u} A) :
    a ⊓ isDirectedRelB S 𝓜.D 𝓜.R ⊓ isSupRelB u S 𝓜.R ⊓
        memB (opairB u v)
          (interpDKBodyGraph 𝓜 V K hK hV η x (.app P Q)) ≤
      mapsToSupB
        (interpDKBodyGraph 𝓜 V K hK hV η x (.app P Q))
        S v 𝓜.R := by
  let FP := interpDKBodyGraph 𝓜 V K hK hV η x P
  let FQ := interpDKBodyGraph 𝓜 V K hK hV η x Q
  let Fapp := interpDKBodyGraph 𝓜 V K hK hV η x (.app P Q)
  have hfunApp : a ≤ isFunctionB Fapp 𝓜.D 𝓜.D := hfun
  unfold mapsToSupB
  refine le_inf ?_ ?_
  · refine le_iInf fun w => le_iInf fun z => ?_
    rw [le_himp_iff]
    let t :=
      (a ⊓ isDirectedRelB S 𝓜.D 𝓜.R ⊓ isSupRelB u S 𝓜.R ⊓
        memB (opairB u v) Fapp) ⊓
      (memB w S ⊓ memB (opairB w z) Fapp)
    change t ≤ relB 𝓜.R z v
    have htA : t ≤ a :=
      inf_le_left.trans (inf_le_left.trans
        (inf_le_left.trans inf_le_left))
    have htu : t ≤ isSupRelB u S 𝓜.R :=
      inf_le_left.trans (inf_le_left.trans inf_le_right)
    have htuv : t ≤ memB (opairB u v) Fapp :=
      inf_le_left.trans inf_le_right
    have htwS : t ≤ memB w S :=
      inf_le_right.trans inf_le_left
    have htwz : t ≤ memB (opairB w z) Fapp :=
      inf_le_right.trans inf_le_right
    have hwu : t ≤ relB 𝓜.R w u :=
      (isUpperBoundRelB_apply u S 𝓜.R w).trans' <|
        le_inf (htu.trans inf_le_left) htwS
    exact (interpDKBodyGraph_app_apply_mono
        𝓜 V K hK hV η x P Q a hPsc hQsc w u z v).trans' <|
      le_inf (le_inf (le_inf htA htwz) htuv) hwu
  · refine le_iInf fun b => ?_
    rw [le_himp_iff]
    let upper :=
      ⨅ w : AName A, ⨅ z : AName A,
        memB w S ⊓ memB (opairB w z) Fapp ⇨ relB 𝓜.R z b
    let t :=
      (a ⊓ isDirectedRelB S 𝓜.D 𝓜.R ⊓ isSupRelB u S 𝓜.R ⊓
        memB (opairB u v) Fapp) ⊓ upper
    change t ≤ relB 𝓜.R v b
    have htA : t ≤ a :=
      inf_le_left.trans (inf_le_left.trans
        (inf_le_left.trans inf_le_left))
    have htDir : t ≤ isDirectedRelB S 𝓜.D 𝓜.R :=
      inf_le_left.trans (inf_le_left.trans
        (inf_le_left.trans inf_le_right))
    have htSup : t ≤ isSupRelB u S 𝓜.R :=
      inf_le_left.trans (inf_le_left.trans inf_le_right)
    have htuv : t ≤ memB (opairB u v) Fapp :=
      inf_le_left.trans inf_le_right
    have htUpper : t ≤ upper := inf_le_right
    have hdec :
        t ≤ ⨆ p : AName A, ⨆ q : AName A, ⨆ c : AName A,
          memB (opairB u p) FP ⊓
          memB (opairB u q) FQ ⊓
          memB (opairB p c) 𝓜.Fun ⊓
          memB c 𝓜.C ⊓
          memB (opairB q v) c :=
      (interpDKBodyGraph_app_mem_decompose
          𝓜 V K hK hV η x P Q a u v).trans' <|
        le_inf htA htuv
    refine (le_inf le_rfl hdec).trans ?_
    rw [inf_iSup_eq]
    refine iSup_le fun p => ?_
    rw [inf_iSup_eq]
    refine iSup_le fun q => ?_
    rw [inf_iSup_eq]
    refine iSup_le fun c => ?_
    let s :=
      t ⊓
        (memB (opairB u p) FP ⊓
          memB (opairB u q) FQ ⊓
          memB (opairB p c) 𝓜.Fun ⊓
          memB c 𝓜.C ⊓
          memB (opairB q v) c)
    change s ≤ relB 𝓜.R v b
    have hsT : s ≤ t := inf_le_left
    have hsφ : s ≤
        memB (opairB u p) FP ⊓
          memB (opairB u q) FQ ⊓
          memB (opairB p c) 𝓜.Fun ⊓
          memB c 𝓜.C ⊓
          memB (opairB q v) c :=
      inf_le_right
    have hsup : s ≤
        memB (opairB u p) FP :=
      hsφ.trans (inf_le_left.trans
        (inf_le_left.trans (inf_le_left.trans inf_le_left)))
    have hsuq : s ≤ memB (opairB u q) FQ :=
      hsφ.trans (inf_le_left.trans
        (inf_le_left.trans (inf_le_left.trans inf_le_right)))
    have hspc : s ≤ memB (opairB p c) 𝓜.Fun :=
      hsφ.trans (inf_le_left.trans
        (inf_le_left.trans inf_le_right))
    have hscC : s ≤ memB c 𝓜.C :=
      hsφ.trans (inf_le_left.trans inf_le_right)
    have hsqv : s ≤ memB (opairB q v) c :=
      hsφ.trans inf_le_right
    have hPimg :
        s ≤ isDirectedRelB (graphImageB FP S 𝓜.D) 𝓜.D 𝓜.R ⊓
          isSupRelB p (graphImageB FP S 𝓜.D) 𝓜.R :=
      (scottContinuous_image_sup (hF := hsT.trans htA |>.trans hPsc)
          FP S 𝓜.D 𝓜.D 𝓜.R 𝓜.R u p).trans' <|
        le_inf (le_inf (le_inf le_rfl (hsT.trans htDir))
          (hsT.trans htSup)) hsup
    have hFunsc : (⊤ : A) ≤
        isScottContinuousB 𝓜.Fun 𝓜.D 𝓜.C 𝓜.R 𝓜.Q :=
      le_top.trans 𝓜.fun_continuous.ge
    have hFunimg :
        s ≤ isDirectedRelB
            (graphImageB 𝓜.Fun (graphImageB FP S 𝓜.D) 𝓜.C)
            𝓜.C 𝓜.Q ⊓
          isSupRelB c
            (graphImageB 𝓜.Fun (graphImageB FP S 𝓜.D) 𝓜.C)
            𝓜.Q :=
      (scottContinuous_image_sup (hF := hFunsc)
          𝓜.Fun (graphImageB FP S 𝓜.D) 𝓜.D 𝓜.C 𝓜.R 𝓜.Q
          p c).trans' <|
        le_inf (le_inf (le_inf (le_top.trans le_top)
            (hPimg.trans inf_le_left))
          (hPimg.trans inf_le_right)) hspc
    have hQimg :
        s ≤ isDirectedRelB (graphImageB FQ S 𝓜.D) 𝓜.D 𝓜.R ⊓
          isSupRelB q (graphImageB FQ S 𝓜.D) 𝓜.R :=
      (scottContinuous_image_sup (hF := hsT.trans htA |>.trans hQsc)
          FQ S 𝓜.D 𝓜.D 𝓜.R 𝓜.R u q).trans' <|
        le_inf (le_inf (le_inf le_rfl (hsT.trans htDir))
          (hsT.trans htSup)) hsuq
    have hqD : s ≤ memB q 𝓜.D :=
      (local_function_edge_le_domain
          ((𝓜.mem_mapSpace_le_function c).trans' hscC) q v).trans' <|
        le_inf le_rfl hsqv
    have hvD : s ≤ memB v 𝓜.D :=
      (local_function_edge_le_codomain
          ((𝓜.mem_mapSpace_le_function c).trans' hscC) q v).trans' <|
        le_inf le_rfl hsqv
    have hvsup : s ≤
        isSupRelB v
          (graphImageB (𝓜.evalAtGraph q)
            (graphImageB 𝓜.Fun (graphImageB FP S 𝓜.D) 𝓜.C)
            𝓜.D)
          𝓜.R :=
      (𝓜.eval_preserves_Q_sup
          (graphImageB 𝓜.Fun (graphImageB FP S 𝓜.D) 𝓜.C)
          c q v).trans' <|
        le_inf (le_inf (le_inf (le_inf (le_inf
            (hFunimg.trans inf_le_left) hscC)
          (hFunimg.trans inf_le_right))
          hqD) hvD) hsqv
    have hupperb : s ≤ isUpperBoundRelB b
        (graphImageB (𝓜.evalAtGraph q)
          (graphImageB 𝓜.Fun (graphImageB FP S 𝓜.D) 𝓜.C)
          𝓜.D)
        𝓜.R := by
      refine le_iInf fun y => ?_
      rw [le_himp_iff, memB_graphImageB, ← inf_assoc, inf_iSup_eq]
      refine iSup_le fun F => ?_
      let sy :=
        (s ⊓ memB y 𝓜.D) ⊓
          (memB F
              (graphImageB 𝓜.Fun (graphImageB FP S 𝓜.D) 𝓜.C) ⊓
            memB (opairB F y) (𝓜.evalAtGraph q))
      change sy ≤ relB 𝓜.R y b
      have hsyS : sy ≤ s := inf_le_left.trans inf_le_left
      have hyD : sy ≤ memB y 𝓜.D := inf_le_left.trans inf_le_right
      have hFimg : sy ≤
          memB F (graphImageB 𝓜.Fun (graphImageB FP S 𝓜.D) 𝓜.C) :=
        inf_le_right.trans inf_le_left
      have hFy : sy ≤ memB (opairB F y) (𝓜.evalAtGraph q) :=
        inf_le_right.trans inf_le_right
      have hFeval := (𝓜.memB_evalAtGraph_le q F y).trans' hFy
      have hFC : sy ≤ memB F 𝓜.C := hFeval.trans inf_le_left
      have hqy : sy ≤ memB (opairB q y) F := hFeval.trans inf_le_right
      rw [memB_graphImageB] at hFimg
      have hFimg' : sy ≤
          memB F 𝓜.C ⊓
            ⨆ pₛ : AName A,
              memB pₛ (graphImageB FP S 𝓜.D) ⊓
                memB (opairB pₛ F) 𝓜.Fun :=
        hFimg
      refine (le_inf le_rfl (hFimg'.trans inf_le_right)).trans ?_
      rw [inf_iSup_eq]
      refine iSup_le fun pₛ => ?_
      let sp :=
        sy ⊓
          (memB pₛ (graphImageB FP S 𝓜.D) ⊓
            memB (opairB pₛ F) 𝓜.Fun)
      change sp ≤ relB 𝓜.R y b
      have hspS : sp ≤ sy := inf_le_left
      have hpₛImg : sp ≤ memB pₛ (graphImageB FP S 𝓜.D) :=
        inf_le_right.trans inf_le_left
      have hpₛF : sp ≤ memB (opairB pₛ F) 𝓜.Fun :=
        inf_le_right.trans inf_le_right
      rw [memB_graphImageB] at hpₛImg
      have hpₛImg' : sp ≤
          memB pₛ 𝓜.D ⊓
            ⨆ w : AName A,
              memB w S ⊓ memB (opairB w pₛ) FP :=
        hpₛImg
      refine (le_inf le_rfl (hpₛImg'.trans inf_le_right)).trans ?_
      rw [inf_iSup_eq]
      refine iSup_le fun w => ?_
      let sw :=
        sp ⊓ (memB w S ⊓ memB (opairB w pₛ) FP)
      change sw ≤ relB 𝓜.R y b
      have hswS : sw ≤ s :=
        inf_le_left.trans (hspS.trans hsyS)
      have hwS : sw ≤ memB w S :=
        inf_le_right.trans inf_le_left
      have hwpₛ : sw ≤ memB (opairB w pₛ) FP :=
        inf_le_right.trans inf_le_right
      have hFsc : sw ≤
          isScottContinuousB F 𝓜.D 𝓜.D 𝓜.R 𝓜.R :=
        (𝓜.mem_mapSpace_le_scottContinuous F).trans' <|
          inf_le_left.trans (hspS.trans hFC)
      have hyFsup : sw ≤
          isSupRelB y (graphImageB F (graphImageB FQ S 𝓜.D) 𝓜.D)
            𝓜.R :=
        ((scottContinuous_image_sup (hF := hFsc)
            F (graphImageB FQ S 𝓜.D) 𝓜.D 𝓜.D 𝓜.R 𝓜.R
            q y).trans inf_le_right).trans' <|
          le_inf (le_inf (le_inf le_rfl
              (hswS.trans (hQimg.trans inf_le_left)))
            (hswS.trans (hQimg.trans inf_le_right)))
            (inf_le_left.trans (hspS.trans hqy))
      have hbF : sw ≤ isUpperBoundRelB b
          (graphImageB F (graphImageB FQ S 𝓜.D) 𝓜.D) 𝓜.R := by
        refine le_iInf fun z => ?_
        rw [le_himp_iff, memB_graphImageB, ← inf_assoc, inf_iSup_eq]
        refine iSup_le fun qₜ => ?_
        let sz :=
          (sw ⊓ memB z 𝓜.D) ⊓
            (memB qₜ (graphImageB FQ S 𝓜.D) ⊓
              memB (opairB qₜ z) F)
        change sz ≤ relB 𝓜.R z b
        have hszS : sz ≤ sw := inf_le_left.trans inf_le_left
        have hzD : sz ≤ memB z 𝓜.D := inf_le_left.trans inf_le_right
        have hqₜImg : sz ≤ memB qₜ (graphImageB FQ S 𝓜.D) :=
          inf_le_right.trans inf_le_left
        have hqₜz : sz ≤ memB (opairB qₜ z) F :=
          inf_le_right.trans inf_le_right
        rw [memB_graphImageB] at hqₜImg
        have hqₜImg' : sz ≤
            memB qₜ 𝓜.D ⊓
              ⨆ t₀ : AName A,
                memB t₀ S ⊓ memB (opairB t₀ qₜ) FQ :=
          hqₜImg
        refine (le_inf le_rfl (hqₜImg'.trans inf_le_right)).trans ?_
        rw [inf_iSup_eq]
        refine iSup_le fun t₀ => ?_
        let st :=
          sz ⊓ (memB t₀ S ⊓ memB (opairB t₀ qₜ) FQ)
        change st ≤ relB 𝓜.R z b
        have hstS : st ≤ s :=
          inf_le_left.trans (hszS.trans hswS)
        have ht₀S : st ≤ memB t₀ S :=
          inf_le_right.trans inf_le_left
        have ht₀q : st ≤ memB (opairB t₀ qₜ) FQ :=
          inf_le_right.trans inf_le_right
        have hwS' : st ≤ memB w S :=
          inf_le_left.trans (hszS.trans hwS)
        have hcommon :
            st ≤ ⨆ r : AName A,
              memB r S ⊓ relB 𝓜.R w r ⊓ relB 𝓜.R t₀ r :=
          (isDirectedRelB_upper_apply S 𝓜.D 𝓜.R w t₀).trans' <|
            le_inf (le_inf (hstS.trans (hsT.trans htDir)) hwS') ht₀S
        refine (le_inf le_rfl hcommon).trans ?_
        rw [inf_iSup_eq]
        refine iSup_le fun r => ?_
        let sr :=
          st ⊓ (memB r S ⊓ relB 𝓜.R w r ⊓ relB 𝓜.R t₀ r)
        change sr ≤ relB 𝓜.R z b
        have hsrS : sr ≤ s := inf_le_left.trans hstS
        have hrS : sr ≤ memB r S :=
          inf_le_right.trans (inf_le_left.trans inf_le_left)
        have hwr : sr ≤ relB 𝓜.R w r :=
          inf_le_right.trans (inf_le_left.trans inf_le_right)
        have ht₀r : sr ≤ relB 𝓜.R t₀ r :=
          inf_le_right.trans inf_le_right
        have hrD : sr ≤ memB r 𝓜.D :=
          (memB_of_subsetB r S 𝓜.D).trans' <|
            le_inf hrS (hsrS.trans (hsT.trans htDir) |>.trans
              (isDirectedRelB_subset S 𝓜.D 𝓜.R))
        have htotApp : sr ≤ ⨆ zᵣ : AName A,
            memB (opairB r zᵣ) Fapp :=
          (isTotalB_apply Fapp 𝓜.D r).trans' <|
            le_inf
              ((hsrS.trans (hsT.trans htA) |>.trans hfunApp).trans
                inf_le_right)
              hrD
        refine (le_inf le_rfl htotApp).trans ?_
        rw [inf_iSup_eq]
        refine iSup_le fun zᵣ => ?_
        let szr := sr ⊓ memB (opairB r zᵣ) Fapp
        change szr ≤ relB 𝓜.R z b
        have hszrS : szr ≤ s := inf_le_left.trans hsrS
        have hrzᵣ : szr ≤ memB (opairB r zᵣ) Fapp := inf_le_right
        have hzᵣb : szr ≤ relB 𝓜.R zᵣ b := by
          have hu := iInf_le
            (fun w' : AName A => ⨅ z' : AName A,
              memB w' S ⊓ memB (opairB w' z') Fapp ⇨
                relB 𝓜.R z' b) r
          have hz := (iInf_le
            (fun z' : AName A =>
              memB r S ⊓ memB (opairB r z') Fapp ⇨
                relB 𝓜.R z' b) zᵣ).trans' hu
          exact (le_himp_iff.mp hz).trans' <|
            le_inf (hszrS.trans (hsT.trans htUpper))
              (le_inf (inf_le_left.trans hrS) hrzᵣ)
        have hdecR :
            szr ≤ ⨆ pᵣ : AName A, ⨆ qᵣ : AName A, ⨆ cᵣ : AName A,
              memB (opairB r pᵣ) FP ⊓
              memB (opairB r qᵣ) FQ ⊓
              memB (opairB pᵣ cᵣ) 𝓜.Fun ⊓
              memB cᵣ 𝓜.C ⊓
              memB (opairB qᵣ zᵣ) cᵣ :=
          (interpDKBodyGraph_app_mem_decompose
              𝓜 V K hK hV η x P Q a r zᵣ).trans' <|
            le_inf (hszrS.trans (hsT.trans htA)) hrzᵣ
        refine (le_inf le_rfl hdecR).trans ?_
        rw [inf_iSup_eq]
        refine iSup_le fun pᵣ => ?_
        rw [inf_iSup_eq]
        refine iSup_le fun qᵣ => ?_
        rw [inf_iSup_eq]
        refine iSup_le fun cᵣ => ?_
        let sc :=
          szr ⊓
            (memB (opairB r pᵣ) FP ⊓
              memB (opairB r qᵣ) FQ ⊓
              memB (opairB pᵣ cᵣ) 𝓜.Fun ⊓
              memB cᵣ 𝓜.C ⊓
              memB (opairB qᵣ zᵣ) cᵣ)
        change sc ≤ relB 𝓜.R z b
        have hscS : sc ≤ s := inf_le_left.trans hszrS
        have hscφ : sc ≤
            memB (opairB r pᵣ) FP ⊓
              memB (opairB r qᵣ) FQ ⊓
              memB (opairB pᵣ cᵣ) 𝓜.Fun ⊓
              memB cᵣ 𝓜.C ⊓
              memB (opairB qᵣ zᵣ) cᵣ :=
          inf_le_right
        have hscA : sc ≤ a := hscS.trans (hsT.trans htA)
        have hsc_wp : sc ≤ memB (opairB w pₛ) FP :=
          inf_le_left.trans (inf_le_left.trans (inf_le_left.trans
            (inf_le_left.trans (inf_le_left.trans
              (inf_le_left.trans hwpₛ)))))
        have hsc_rp : sc ≤ memB (opairB r pᵣ) FP :=
          hscφ.trans (inf_le_left.trans (inf_le_left.trans
            (inf_le_left.trans inf_le_left)))
        have hsc_wr : sc ≤ relB 𝓜.R w r :=
          inf_le_left.trans (inf_le_left.trans hwr)
        have hsc_tq : sc ≤ memB (opairB t₀ qₜ) FQ :=
          inf_le_left.trans (inf_le_left.trans
            (inf_le_left.trans ht₀q))
        have hsc_rq : sc ≤ memB (opairB r qᵣ) FQ :=
          hscφ.trans (inf_le_left.trans (inf_le_left.trans
            (inf_le_left.trans inf_le_right)))
        have hsc_tr : sc ≤ relB 𝓜.R t₀ r :=
          inf_le_left.trans (inf_le_left.trans ht₀r)
        have hsc_pF : sc ≤ memB (opairB pₛ F) 𝓜.Fun :=
          inf_le_left.trans (inf_le_left.trans (inf_le_left.trans
            (inf_le_left.trans (inf_le_left.trans (inf_le_left.trans
              (inf_le_left.trans hpₛF))))))
        have hsc_pc : sc ≤ memB (opairB pᵣ cᵣ) 𝓜.Fun :=
          hscφ.trans (inf_le_left.trans
            (inf_le_left.trans inf_le_right))
        have hsc_qz : sc ≤ memB (opairB qₜ z) F :=
          inf_le_left.trans (inf_le_left.trans (inf_le_left.trans
            (inf_le_left.trans hqₜz)))
        have hsc_qz' : sc ≤ memB (opairB qᵣ zᵣ) cᵣ :=
          hscφ.trans inf_le_right
        have hzzᵣ : sc ≤ relB 𝓜.R z zᵣ :=
          (interpDKBodyGraph_app_bi_mono
              𝓜 V K hK hV η x P Q a hPsc hQsc
              w r t₀ r pₛ pᵣ qₜ qᵣ F cᵣ z zᵣ).trans' <|
            le_inf (le_inf (le_inf (le_inf
                hscA
                (le_inf (le_inf hsc_wp hsc_rp) hsc_wr))
              (le_inf (le_inf hsc_tq hsc_rq) hsc_tr))
              (le_inf hsc_pF hsc_pc))
              (le_inf hsc_qz hsc_qz')
        have hzᵣb' : sc ≤ relB 𝓜.R zᵣ b :=
          inf_le_left.trans hzᵣb
        exact (𝓜.relR_trans z zᵣ b).trans' (le_inf hzzᵣ hzᵣb')
      exact (isSupRelB_least y
          (graphImageB F (graphImageB FQ S 𝓜.D) 𝓜.D)
          𝓜.R b).trans' <|
        le_inf hyFsup hbF
    exact (isSupRelB_least v
        (graphImageB (𝓜.evalAtGraph q)
          (graphImageB 𝓜.Fun (graphImageB FP S 𝓜.D) 𝓜.C)
          𝓜.D)
        𝓜.R b).trans' <|
      le_inf hvsup hupperb

/-- Degree-local Scott continuity of the application body graph. -/
theorem interpDKBodyGraph_app_le_scottContinuous
    (𝓜 : InternalReflexiveModel (A := A))
    (V K : AName.{u} A) (hK : subsetB K 𝓜.D = ⊤)
    (hV : (oid V).IsTotal)
    (η : RelFun (oid V) (oid 𝓜.D))
    (x : V.idx) (P Q : LamDK V.idx K.idx) (a : A)
    (hP : ∀ d, IsRelElementAt 𝓜.D a
      (interpDKRelVal 𝓜 V K hK hV
        (η.update hV 𝓜.total x d) P))
    (hQ : ∀ d, IsRelElementAt 𝓜.D a
      (interpDKRelVal 𝓜 V K hK hV
        (η.update hV 𝓜.total x d) Q))
    (hPsc : a ≤ isScottContinuousB
      (interpDKBodyGraph 𝓜 V K hK hV η x P) 𝓜.D 𝓜.D 𝓜.R 𝓜.R)
    (hQsc : a ≤ isScottContinuousB
      (interpDKBodyGraph 𝓜 V K hK hV η x Q) 𝓜.D 𝓜.D 𝓜.R 𝓜.R) :
    a ≤ isScottContinuousB
      (interpDKBodyGraph 𝓜 V K hK hV η x (.app P Q))
      𝓜.D 𝓜.D 𝓜.R 𝓜.R := by
  unfold isScottContinuousB
  refine le_inf (le_inf ?_ ?_) ?_
  · exact interpDKBodyGraph_app_le_isFunctionB
      𝓜 V K hK hV η x P Q a hP hQ
  · refine le_iInf fun u => le_iInf fun u' =>
      le_iInf fun v => le_iInf fun v' => ?_
    rw [le_himp_iff]
    exact (interpDKBodyGraph_app_apply_mono
        𝓜 V K hK hV η x P Q a hPsc hQsc u u' v v').trans' <| by
      apply le_of_eq
      ac_rfl
  · refine le_iInf fun S => le_iInf fun u => le_iInf fun v => ?_
    rw [le_himp_iff]
    exact (interpDKBodyGraph_app_mapsToSup
        𝓜 V K hK hV η x P Q a
        (interpDKBodyGraph_app_le_isFunctionB
          𝓜 V K hK hV η x P Q a hP hQ)
        hPsc hQsc S u v).trans' <| by
      apply le_of_eq
      ac_rfl

/-!
## Abstraction constructor
-/

/-- Complementary Boolean pieces of a degree reassemble. -/
theorem le_of_compl_cover {a p q : A}
    (hp : a ⊓ p ≤ q) (hpc : a ⊓ pᶜ ≤ q) : a ≤ q := by
  have : a = (a ⊓ p) ⊔ (a ⊓ pᶜ) := by
    rw [← inf_sup_left, sup_compl_eq_top, inf_top_eq]
  rw [this]
  exact sup_le hp hpc

/-- Distinct keys are disjoint from a common source at the complement of
key equality. -/
theorem setoidEq_keys_disjoint {X : Type*}
    (S : ASetoid (A := A) X) (x y i : X) :
    (S.eq x y)ᶜ ⊓ S.eq i x ⊓ S.eq i y ≤ ⊥ := by
  have hxy : S.eq i x ⊓ S.eq i y ≤ S.eq x y := by
    refine (S.trans x i y).trans' (le_inf ?_ inf_le_right)
    rw [S.symm x i]
    exact inf_le_left
  have hre : (S.eq x y)ᶜ ⊓ S.eq i x ⊓ S.eq i y =
      (S.eq x y)ᶜ ⊓ (S.eq i x ⊓ S.eq i y) := by
    ac_rfl
  rw [hre]
  exact (inf_le_inf le_rfl hxy).trans_eq (compl_inf_self _)

/-- Overwriting a key equal to an earlier key makes the first update
irrelevant. -/
theorem setoidEq_overwrite_disjoint {X : Type*}
    (S : ASetoid (A := A) X) (x y i : X) :
    S.eq x y ⊓ (S.eq i x)ᶜ ⊓ S.eq i y ≤ ⊥ := by
  have hix : S.eq i y ⊓ S.eq x y ≤ S.eq i x := by
    refine (S.trans i y x).trans' (le_inf inf_le_left ?_)
    rw [S.symm y x]
    exact inf_le_right
  have hre : S.eq x y ⊓ (S.eq i x)ᶜ ⊓ S.eq i y =
      (S.eq i y ⊓ S.eq x y) ⊓ (S.eq i x)ᶜ := by
    ac_rfl
  rw [hre]
  exact (inf_le_inf hix le_rfl).trans_eq (inf_compl_eq_bot)

/-- `p ⊓ q ⊓ r ≤ ⊥` yields `p ⊓ q ≤ rᶜ`. -/
theorem le_compl_of_inf_bot {p q r : A} (h : p ⊓ q ⊓ r ≤ ⊥) :
    p ⊓ q ≤ rᶜ := by
  rw [le_compl_iff_disjoint_left, disjoint_iff]
  exact le_bot_iff.mp (h.trans' (by apply le_of_eq; ac_rfl))

/-- Degree-local commutation of successive environment updates, on the
complement of key equality. -/
theorem RelFun.update_commute_val
    {X Y : Type*} {S : ASetoid (A := A) X} {T : ASetoid (A := A) Y}
    (f : RelFun S T) (hS : S.IsTotal) (hT : T.IsTotal)
    (x y : X) (d z : Y) (i : X) (j : Y) :
    (S.eq x y)ᶜ ⊓
        ((f.update hS hT y d).update hS hT x z).val i j ≤
      ((f.update hS hT x z).update hS hT y d).val i j := by
  have hdisj := setoidEq_keys_disjoint S x y i
  rw [RelFun.update_val, RelFun.update_val, RelFun.update_val,
    RelFun.update_val]
  rw [inf_sup_left]
  refine sup_le ?_ ?_
  · apply le_sup_of_le_right
    refine le_inf ?_ ?_
    · exact (le_compl_of_inf_bot hdisj).trans' <|
        le_inf inf_le_left (inf_le_right.trans inf_le_left)
    · apply le_sup_of_le_left
      exact inf_le_right
  · rw [← inf_assoc, inf_sup_left]
    refine sup_le ?_ ?_
    · apply le_sup_of_le_left
      refine le_inf (inf_le_right.trans inf_le_left)
        (inf_le_right.trans inf_le_right)
    · apply le_sup_of_le_right
      refine le_inf (inf_le_right.trans inf_le_left) ?_
      apply le_sup_of_le_right
      refine le_inf (inf_le_left.trans inf_le_right)
        (inf_le_right.trans inf_le_right)

/-- The other direction of `RelFun.update_commute_val`. -/
theorem RelFun.update_commute_val_symm
    {X Y : Type*} {S : ASetoid (A := A) X} {T : ASetoid (A := A) Y}
    (f : RelFun S T) (hS : S.IsTotal) (hT : T.IsTotal)
    (x y : X) (d z : Y) (i : X) (j : Y) :
    (S.eq x y)ᶜ ⊓
        ((f.update hS hT x z).update hS hT y d).val i j ≤
      ((f.update hS hT y d).update hS hT x z).val i j := by
  have h := RelFun.update_commute_val f hS hT y x z d i j
  rwa [S.symm y x] at h

/-- The second update at an equal key overwrites the first. -/
theorem RelFun.update_overwrite_val
    {X Y : Type*} {S : ASetoid (A := A) X} {T : ASetoid (A := A) Y}
    (f : RelFun S T) (hS : S.IsTotal) (hT : T.IsTotal)
    (x y : X) (d z : Y) (i : X) (j : Y) :
    S.eq x y ⊓
        ((f.update hS hT y d).update hS hT x z).val i j ≤
      (f.update hS hT x z).val i j := by
  have hdisj := setoidEq_overwrite_disjoint S x y i
  rw [RelFun.update_val, RelFun.update_val, RelFun.update_val]
  rw [inf_sup_left]
  refine sup_le ?_ ?_
  · apply le_sup_of_le_left
    exact inf_le_right
  · rw [← inf_assoc, inf_sup_left]
    refine sup_le ?_ ?_
    · exact (hdisj.trans bot_le).trans' <|
        le_inf inf_le_left (inf_le_right.trans inf_le_left)
    · apply le_sup_of_le_right
      refine le_inf (inf_le_left.trans inf_le_right)
        (inf_le_right.trans inf_le_right)

/-- The converse of `RelFun.update_overwrite_val`. -/
theorem RelFun.update_overwrite_val_symm
    {X Y : Type*} {S : ASetoid (A := A) X} {T : ASetoid (A := A) Y}
    (f : RelFun S T) (hS : S.IsTotal) (hT : T.IsTotal)
    (x y : X) (d z : Y) (i : X) (j : Y) :
    S.eq x y ⊓ (f.update hS hT x z).val i j ≤
      ((f.update hS hT y d).update hS hT x z).val i j := by
  have hdisj := setoidEq_overwrite_disjoint S x y i
  rw [RelFun.update_val, RelFun.update_val, RelFun.update_val]
  rw [inf_sup_left]
  refine sup_le ?_ ?_
  · apply le_sup_of_le_left
    exact inf_le_right
  · apply le_sup_of_le_right
    refine le_inf (inf_le_right.trans inf_le_left) ?_
    apply le_sup_of_le_right
    refine le_inf ?_ ?_
    · exact (le_compl_of_inf_bot hdisj).trans' <|
        le_inf inf_le_left (inf_le_right.trans inf_le_left)
    · exact inf_le_right.trans inf_le_right

/-- Two-point setoid whose off-diagonal equality is the degree `a`. -/
def degreePairSetoid (a : A) : ASetoid (A := A) Bool where
  eq b1 b2 := if b1 = b2 then ⊤ else a
  symm := by
    intro b1 b2
    by_cases h : b1 = b2
    · simp [h]
    · simp [h, Ne.symm h]
  trans := by
    intro b1 b2 b3
    by_cases h12 : b1 = b2
    · by_cases h23 : b2 = b3
      · simp [h12, h23, h12.trans h23]
      · have h13 : b1 ≠ b3 := mt (fun h => h12.symm.trans h) h23
        simp [h12, h23, h13]
    · by_cases h23 : b2 = b3
      · have h13 : b1 ≠ b3 := mt (fun h => h.trans h23.symm) h12
        simp [h12, h23, h13]
      · by_cases h13 : b1 = b3
        · simp [h12, h23, h13]
        · simp [h12, h23, h13]

/-- Interpretation transports along a mutual degree-local comparison of
environments. -/
theorem interpDKRelVal_le_of_env
    (𝓜 : InternalReflexiveModel (A := A))
    (V K : AName.{u} A) (hK : subsetB K 𝓜.D = ⊤)
    (hV : (oid V).IsTotal)
    (η₁ η₂ : RelFun (oid V) (oid 𝓜.D)) (a : A)
    (hη : ∀ i j, a ⊓ η₁.val i j ≤ η₂.val i j)
    (hη' : ∀ i j, a ⊓ η₂.val i j ≤ η₁.val i j)
    (M : LamDK V.idx K.idx) (d : 𝓜.D.idx) :
    a ⊓ interpDKRelVal 𝓜 V K hK hV η₁ M d ≤
      interpDKRelVal 𝓜 V K hK hV η₂ M d := by
  let ηs : Bool → RelFun (oid V) (oid 𝓜.D) :=
    fun b => if b then η₁ else η₂
  have hηs : RelFun.IsPointwiseFamily (degreePairSetoid a) ηs := by
    intro b1 b2 i j
    by_cases h : b1 = b2
    · have : (degreePairSetoid a).eq b1 b2 = ⊤ := by
        simp [degreePairSetoid, h]
      rw [this, top_inf_eq, h]
    · have : (degreePairSetoid a).eq b1 b2 = a := by
        simp [degreePairSetoid, h]
      rw [this]
      cases b1 <;> cases b2
      · exact (h rfl).elim
      · exact hη' i j
      · exact hη i j
      · exact (h rfl).elim
  have h := interpDKRelVal_isPointwiseFamily 𝓜 V K hK hV
    (degreePairSetoid a) ηs hηs M true false d
  simpa [degreePairSetoid, ηs] using h

/-- Commuting updates transport the interpretation at the complement of
key equality. -/
theorem interpDKRelVal_update_commute
    (𝓜 : InternalReflexiveModel (A := A))
    (V K : AName.{u} A) (hK : subsetB K 𝓜.D = ⊤)
    (hV : (oid V).IsTotal)
    (η : RelFun (oid V) (oid 𝓜.D))
    (x y : V.idx) (d e : 𝓜.D.idx)
    (P : LamDK V.idx K.idx) (w : 𝓜.D.idx) :
    ((oid V).eq x y)ᶜ ⊓
        interpDKRelVal 𝓜 V K hK hV
          ((η.update hV 𝓜.total y d).update hV 𝓜.total x e) P w ≤
      interpDKRelVal 𝓜 V K hK hV
        ((η.update hV 𝓜.total x e).update hV 𝓜.total y d) P w :=
  interpDKRelVal_le_of_env 𝓜 V K hK hV _ _ ((oid V).eq x y)ᶜ
    (fun i j => RelFun.update_commute_val η hV 𝓜.total x y d e i j)
    (fun i j => RelFun.update_commute_val_symm η hV 𝓜.total x y d e i j)
    P w

/-- The other direction of `interpDKRelVal_update_commute`. -/
theorem interpDKRelVal_update_commute_symm
    (𝓜 : InternalReflexiveModel (A := A))
    (V K : AName.{u} A) (hK : subsetB K 𝓜.D = ⊤)
    (hV : (oid V).IsTotal)
    (η : RelFun (oid V) (oid 𝓜.D))
    (x y : V.idx) (d e : 𝓜.D.idx)
    (P : LamDK V.idx K.idx) (w : 𝓜.D.idx) :
    ((oid V).eq x y)ᶜ ⊓
        interpDKRelVal 𝓜 V K hK hV
          ((η.update hV 𝓜.total x e).update hV 𝓜.total y d) P w ≤
      interpDKRelVal 𝓜 V K hK hV
        ((η.update hV 𝓜.total y d).update hV 𝓜.total x e) P w :=
  interpDKRelVal_le_of_env 𝓜 V K hK hV _ _ ((oid V).eq x y)ᶜ
    (fun i j => RelFun.update_commute_val_symm η hV 𝓜.total x y d e i j)
    (fun i j => RelFun.update_commute_val η hV 𝓜.total x y d e i j)
    P w

/-- Overwriting an equal key forgets the earlier update. -/
theorem interpDKRelVal_update_overwrite
    (𝓜 : InternalReflexiveModel (A := A))
    (V K : AName.{u} A) (hK : subsetB K 𝓜.D = ⊤)
    (hV : (oid V).IsTotal)
    (η : RelFun (oid V) (oid 𝓜.D))
    (x y : V.idx) (d e : 𝓜.D.idx)
    (P : LamDK V.idx K.idx) (w : 𝓜.D.idx) :
    (oid V).eq x y ⊓
        interpDKRelVal 𝓜 V K hK hV
          ((η.update hV 𝓜.total y d).update hV 𝓜.total x e) P w ≤
      interpDKRelVal 𝓜 V K hK hV (η.update hV 𝓜.total x e) P w :=
  interpDKRelVal_le_of_env 𝓜 V K hK hV _ _ ((oid V).eq x y)
    (fun i j => RelFun.update_overwrite_val η hV 𝓜.total x y d e i j)
    (fun i j => RelFun.update_overwrite_val_symm η hV 𝓜.total x y d e i j)
    P w

/-- The converse of `interpDKRelVal_update_overwrite`. -/
theorem interpDKRelVal_update_overwrite_symm
    (𝓜 : InternalReflexiveModel (A := A))
    (V K : AName.{u} A) (hK : subsetB K 𝓜.D = ⊤)
    (hV : (oid V).IsTotal)
    (η : RelFun (oid V) (oid 𝓜.D))
    (x y : V.idx) (d e : 𝓜.D.idx)
    (P : LamDK V.idx K.idx) (w : 𝓜.D.idx) :
    (oid V).eq x y ⊓
        interpDKRelVal 𝓜 V K hK hV (η.update hV 𝓜.total x e) P w ≤
      interpDKRelVal 𝓜 V K hK hV
        ((η.update hV 𝓜.total y d).update hV 𝓜.total x e) P w :=
  interpDKRelVal_le_of_env 𝓜 V K hK hV _ _ ((oid V).eq x y)
    (fun i j => RelFun.update_overwrite_val_symm η hV 𝓜.total x y d e i j)
    (fun i j => RelFun.update_overwrite_val η hV 𝓜.total x y d e i j)
    P w

/-- The empty `D × D` graph. -/
noncomputable def zeroPairGraph (D : AName.{u} A) : AName.{u} A :=
  mk (D.idx × D.idx)
    (fun p => opairB (D.child p.1) (D.child p.2))
    (fun _ => ⊥)

/-- A name whose coefficients lie below `a` is empty at `aᶜ`. -/
theorem eqB_mk_zero_of_val_le {I : Type u}
    (child : I → AName.{u} A) (v : I → A) (a : A)
    (hv : ∀ i, v i ≤ a) :
    aᶜ ≤ eqB (mk I child v) (mk I child (fun _ => ⊥)) :=
  le_eqB_mk_of_le_val child v (fun _ => ⊥) aᶜ
    (fun i =>
      ((inf_le_inf le_rfl (hv i)).trans_eq (compl_inf_self _)))
    (fun _ => inf_le_right.trans bot_le)

/-- The empty pair graph is not a member of the continuous-map space. -/
theorem memB_zeroPairGraph_mapSpace
    (𝓜 : InternalReflexiveModel (A := A)) :
    memB (zeroPairGraph 𝓜.D) 𝓜.C = ⊥ := by
  apply le_bot_iff.mp
  have i : 𝓜.D.idx := Classical.choice 𝓜.complete.nonempty
  have hi : memB (𝓜.D.child i) 𝓜.D = ⊤ := by
    rw [← oid_eps]
    exact 𝓜.total i
  have htot :
      memB (zeroPairGraph 𝓜.D) 𝓜.C ≤
        isTotalB (zeroPairGraph 𝓜.D) 𝓜.D :=
    (𝓜.mem_mapSpace_le_function (zeroPairGraph 𝓜.D)).trans inf_le_right
  have hempty :
      (⨆ y : AName A,
        memB (opairB (𝓜.D.child i) y) (zeroPairGraph 𝓜.D)) = ⊥ := by
    apply le_bot_iff.mp
    refine iSup_le fun y => ?_
    unfold zeroPairGraph
    rw [memB_mk]
    exact iSup_le fun _ => inf_le_right.trans bot_le
  have : isTotalB (zeroPairGraph 𝓜.D) 𝓜.D ≤ ⊥ := by
    have happ :=
      isTotalB_apply (zeroPairGraph 𝓜.D) 𝓜.D (𝓜.D.child i)
    rw [hi, inf_top_eq, hempty] at happ
    exact happ
  exact htot.trans this

/-- Body-graph coefficients are supported by the row degree. -/
theorem interpDKBodyGraph_val_le
    (𝓜 : InternalReflexiveModel (A := A))
    (V K : AName.{u} A) (hK : subsetB K 𝓜.D = ⊤)
    (hV : (oid V).IsTotal)
    (η : RelFun (oid V) (oid 𝓜.D))
    (x : V.idx) (P : LamDK V.idx K.idx) (a : A)
    (hP : ∀ d, IsRelElementAt 𝓜.D a
      (interpDKRelVal 𝓜 V K hK hV
        (η.update hV 𝓜.total x d) P))
    (p : 𝓜.D.idx × 𝓜.D.idx) :
    (interpDKBodyGraph 𝓜 V K hK hV η x P).val p ≤ a :=
  (hP p.1).2.1 p.2 |>.trans inf_le_left

/-- A degree-local body graph is empty at the complementary degree. -/
theorem interpDKBodyGraph_eqB_zero
    (𝓜 : InternalReflexiveModel (A := A))
    (V K : AName.{u} A) (hK : subsetB K 𝓜.D = ⊤)
    (hV : (oid V).IsTotal)
    (η : RelFun (oid V) (oid 𝓜.D))
    (x : V.idx) (P : LamDK V.idx K.idx) (a : A)
    (hP : ∀ d, IsRelElementAt 𝓜.D a
      (interpDKRelVal 𝓜 V K hK hV
        (η.update hV 𝓜.total x d) P)) :
    aᶜ ≤ eqB (interpDKBodyGraph 𝓜 V K hK hV η x P)
      (zeroPairGraph 𝓜.D) :=
  eqB_mk_zero_of_val_le
    (fun p : 𝓜.D.idx × 𝓜.D.idx =>
      opairB (𝓜.D.child p.1) (𝓜.D.child p.2))
    (fun p =>
      interpDKRelVal 𝓜 V K hK hV
        (η.update hV 𝓜.total x p.1) P p.2)
    a
    (interpDKBodyGraph_val_le 𝓜 V K hK hV η x P a hP)

/-- Lam applied to a degree-local body graph is supported by that degree. -/
theorem interpDKRelVal_abs_memB_le
    (𝓜 : InternalReflexiveModel (A := A))
    (V K : AName.{u} A) (hK : subsetB K 𝓜.D = ⊤)
    (hV : (oid V).IsTotal)
    (η : RelFun (oid V) (oid 𝓜.D))
    (x : V.idx) (P : LamDK V.idx K.idx) (a : A)
    (hP : ∀ d, IsRelElementAt 𝓜.D a
      (interpDKRelVal 𝓜 V K hK hV
        (η.update hV 𝓜.total x d) P))
    (d : 𝓜.D.idx) :
    memB (opairB (interpDKBodyGraph 𝓜 V K hK hV η x P)
        (𝓜.D.child d)) 𝓜.Lam ≤ a := by
  have heq :=
    interpDKBodyGraph_eqB_zero 𝓜 V K hK hV η x P a hP
  have hcongr :
      aᶜ ⊓ memB (opairB
          (interpDKBodyGraph 𝓜 V K hK hV η x P)
          (𝓜.D.child d)) 𝓜.Lam ≤
        memB (opairB (zeroPairGraph 𝓜.D) (𝓜.D.child d)) 𝓜.Lam :=
    (memB_opairB_congr 𝓜.Lam
        (interpDKBodyGraph 𝓜 V K hK hV η x P)
        (zeroPairGraph 𝓜.D)
        (𝓜.D.child d) (𝓜.D.child d)).trans' <|
      le_inf (le_inf (inf_le_left.trans heq)
          (le_top.trans (eqB_self (A := A) (𝓜.D.child d)).ge))
        inf_le_right
  have hsub : subsetB 𝓜.Lam (prodB 𝓜.C 𝓜.D) = ⊤ :=
    isFunctionB_subset 𝓜.lam_function
  have hC :
      memB (opairB (zeroPairGraph 𝓜.D) (𝓜.D.child d)) 𝓜.Lam ≤
        memB (zeroPairGraph 𝓜.D) 𝓜.C :=
    (memB_opairB_le_of_subsetB hsub
        (zeroPairGraph 𝓜.D) (𝓜.D.child d)).trans
      inf_le_left
  have : aᶜ ⊓ memB (opairB
      (interpDKBodyGraph 𝓜 V K hK hV η x P)
      (𝓜.D.child d)) 𝓜.Lam ≤ ⊥ :=
    (hcongr.trans hC).trans_eq (memB_zeroPairGraph_mapSpace 𝓜)
  have hx : memB (opairB
      (interpDKBodyGraph 𝓜 V K hK hV η x P)
      (𝓜.D.child d)) 𝓜.Lam ≤ aᶜᶜ := by
    rw [le_compl_iff_disjoint_left, disjoint_iff]
    exact le_bot_iff.mp (this.trans' (by apply le_of_eq; ac_rfl))
  rwa [compl_compl] at hx

/-- Abstraction rows are generalized elements at the meet of the body
degree and the abstraction support. -/
theorem interpDKRelVal_abs_isRelElementAt
    (𝓜 : InternalReflexiveModel (A := A))
    (V K : AName.{u} A) (hK : subsetB K 𝓜.D = ⊤)
    (hV : (oid V).IsTotal)
    (η : RelFun (oid V) (oid 𝓜.D))
    (x : V.idx) (P : LamDK V.idx K.idx) (a : A)
    (hPsc : a ≤ isScottContinuousB
      (interpDKBodyGraph 𝓜 V K hK hV η x P) 𝓜.D 𝓜.D 𝓜.R 𝓜.R)
    (hP : ∀ d, IsRelElementAt 𝓜.D a
      (interpDKRelVal 𝓜 V K hK hV
        (η.update hV 𝓜.total x d) P)) :
    IsRelElementAt 𝓜.D (a ⊓ lamDKVal V K (.abs x P))
      (interpDKRelVal 𝓜 V K hK hV η (.abs x P)) := by
  let body := interpDKBodyGraph 𝓜 V K hK hV η x P
  let r (d : 𝓜.D.idx) :=
    interpDKRelVal 𝓜 V K hK hV η (.abs x P) d
  have hsub : subsetB 𝓜.Lam (prodB 𝓜.C 𝓜.D) = ⊤ :=
    isFunctionB_subset 𝓜.lam_function
  have hbodyC : a ≤ memB body 𝓜.C :=
    hPsc.trans (𝓜.scottContinuous_le_mem_mapSpace body)
  refine ⟨?respects, ?le_eps, ?single, ?total⟩
  · intro d e
    rw [interpDKRelVal_abs, interpDKRelVal_abs]
    refine le_inf (inf_le_right.trans inf_le_left) ?_
    refine (memB_opairB_congr 𝓜.Lam body body
        (𝓜.D.child d) (𝓜.D.child e)).trans' ?_
    refine le_inf (le_inf ?_ ?_) ?_
    · exact le_top.trans (eqB_self (A := A) body).ge
    · rw [oid_eq_of_total 𝓜.D 𝓜.total]
      exact inf_le_left
    · exact inf_le_right.trans inf_le_right
  · intro d
    rw [interpDKRelVal_abs]
    refine le_inf (le_inf ?_ inf_le_left) ?_
    · exact (interpDKRelVal_abs_memB_le 𝓜 V K hK hV η x P a hP d).trans' <|
        inf_le_right
    · have heps :
          memB (opairB body (𝓜.D.child d)) 𝓜.Lam ≤
            memB (𝓜.D.child d) 𝓜.D :=
        (memB_opairB_le_of_subsetB hsub body (𝓜.D.child d)).trans
          inf_le_right
      rw [oid_eps]
      exact inf_le_right.trans heps
  · intro d e
    rw [interpDKRelVal_abs, interpDKRelVal_abs]
    have hsv :=
      isSingleValuedB_apply 𝓜.Lam body (𝓜.D.child d) (𝓜.D.child e)
    rw [isFunctionB_single 𝓜.lam_function, top_inf_eq] at hsv
    rw [oid_eq_of_total 𝓜.D 𝓜.total]
    exact hsv.trans' <|
      le_inf (inf_le_left.trans inf_le_right)
        (inf_le_right.trans inf_le_right)
  · have htot :
        memB body 𝓜.C ≤
          ⨆ y : AName A, memB (opairB body y) 𝓜.Lam :=
      (isTotalB_apply 𝓜.Lam 𝓜.C body).trans' <|
        le_inf (le_top.trans (isFunctionB_total 𝓜.lam_function).ge)
          le_rfl
    have hproj : a ≤
        ⨆ j : 𝓜.D.idx, memB (opairB body (𝓜.D.child j)) 𝓜.Lam := by
      refine (le_inf le_rfl (htot.trans' hbodyC)).trans ?_
      rw [inf_iSup_eq]
      refine iSup_le fun y =>
        inf_memB_opairB_le_iSup_child
          (hsub := le_top.trans hsub.ge) body y
    refine (le_inf inf_le_right (inf_le_left.trans hproj)).trans ?_
    rw [inf_iSup_eq]
    refine iSup_le fun j => le_iSup_of_le j ?_
    rw [interpDKRelVal_abs]

/-- Every updated abs row is a generalized element at the active degree. -/
theorem interpDKBodyGraph_abs_rows_isRelElementAt
    (𝓜 : InternalReflexiveModel (A := A))
    (V K : AName.{u} A) (hK : subsetB K 𝓜.D = ⊤)
    (hV : (oid V).IsTotal)
    (η : RelFun (oid V) (oid 𝓜.D))
    (y x : V.idx) (P : LamDK V.idx K.idx) (a : A)
    (hInner : ∀ d, a ≤ isScottContinuousB
      (interpDKBodyGraph 𝓜 V K hK hV (η.update hV 𝓜.total y d) x P)
      𝓜.D 𝓜.D 𝓜.R 𝓜.R)
    (hInnerRows : ∀ d, ∀ e, IsRelElementAt 𝓜.D a
      (interpDKRelVal 𝓜 V K hK hV
        ((η.update hV 𝓜.total y d).update hV 𝓜.total x e) P)) :
    ∀ d, IsRelElementAt 𝓜.D (a ⊓ lamDKVal V K (.abs x P))
      (interpDKRelVal 𝓜 V K hK hV
        (η.update hV 𝓜.total y d) (.abs x P)) :=
  fun d =>
    interpDKRelVal_abs_isRelElementAt 𝓜 V K hK hV
      (η.update hV 𝓜.total y d) x P a (hInner d) (hInnerRows d)

/-- Rowwise abs elements make the abs body graph a degree-local function. -/
theorem interpDKBodyGraph_abs_le_isFunctionB
    (𝓜 : InternalReflexiveModel (A := A))
    (V K : AName.{u} A) (hK : subsetB K 𝓜.D = ⊤)
    (hV : (oid V).IsTotal)
    (η : RelFun (oid V) (oid 𝓜.D))
    (y x : V.idx) (P : LamDK V.idx K.idx) (a : A)
    (hInner : ∀ d, a ≤ isScottContinuousB
      (interpDKBodyGraph 𝓜 V K hK hV (η.update hV 𝓜.total y d) x P)
      𝓜.D 𝓜.D 𝓜.R 𝓜.R)
    (hInnerRows : ∀ d, ∀ e, IsRelElementAt 𝓜.D a
      (interpDKRelVal 𝓜 V K hK hV
        ((η.update hV 𝓜.total y d).update hV 𝓜.total x e) P)) :
    a ⊓ lamDKVal V K (.abs x P) ≤
      isFunctionB
        (interpDKBodyGraph 𝓜 V K hK hV η y (.abs x P))
        𝓜.D 𝓜.D :=
  interpDKBodyGraph_le_isFunctionB 𝓜 V K hK hV η y (.abs x P)
    (a ⊓ lamDKVal V K (.abs x P))
    (interpDKBodyGraph_abs_rows_isRelElementAt
      𝓜 V K hK hV η y x P a hInner hInnerRows)

/-- Boolean equality of graphs transports Scott continuity at the same
degree, through the exact map space. -/
theorem InternalReflexiveModel.eqB_le_scottContinuous
    (𝓜 : InternalReflexiveModel (A := A))
    (F G : AName.{u} A) (a : A)
    (heq : a ≤ eqB F G)
    (hF : a ≤ isScottContinuousB F 𝓜.D 𝓜.D 𝓜.R 𝓜.R) :
    a ≤ isScottContinuousB G 𝓜.D 𝓜.D 𝓜.R 𝓜.R := by
  have hFC : a ≤ memB F 𝓜.C :=
    hF.trans (𝓜.scottContinuous_le_mem_mapSpace F)
  have hGC : a ≤ memB G 𝓜.C :=
    (memB_eqB_left F 𝓜.C G).trans' (le_inf hFC heq)
  exact hGC.trans (𝓜.mem_mapSpace_le_scottContinuous G)

/-- Overwriting an equal key does not change the body graph. -/
theorem interpDKBodyGraph_update_overwrite_eqB
    (𝓜 : InternalReflexiveModel (A := A))
    (V K : AName.{u} A) (hK : subsetB K 𝓜.D = ⊤)
    (hV : (oid V).IsTotal)
    (η : RelFun (oid V) (oid 𝓜.D))
    (x y : V.idx) (d : 𝓜.D.idx) (P : LamDK V.idx K.idx) :
    (oid V).eq x y ≤
      eqB (interpDKBodyGraph 𝓜 V K hK hV (η.update hV 𝓜.total y d) x P)
        (interpDKBodyGraph 𝓜 V K hK hV η x P) :=
  le_eqB_mk_of_le_val
    (fun p : 𝓜.D.idx × 𝓜.D.idx =>
      opairB (𝓜.D.child p.1) (𝓜.D.child p.2))
    (fun p =>
      interpDKRelVal 𝓜 V K hK hV
        ((η.update hV 𝓜.total y d).update hV 𝓜.total x p.1) P p.2)
    (fun p =>
      interpDKRelVal 𝓜 V K hK hV
        (η.update hV 𝓜.total x p.1) P p.2)
    ((oid V).eq x y)
    (fun p =>
      interpDKRelVal_update_overwrite 𝓜 V K hK hV η x y d p.1 P p.2)
    (fun p =>
      interpDKRelVal_update_overwrite_symm 𝓜 V K hK hV η x y d p.1 P p.2)

/-- Inner body graphs at equal keys are equal, independently of the
overwritten value. -/
theorem interpDKAbsFamily_eqB_of_eq_keys
    (𝓜 : InternalReflexiveModel (A := A))
    (V K : AName.{u} A) (hK : subsetB K 𝓜.D = ⊤)
    (hV : (oid V).IsTotal)
    (η : RelFun (oid V) (oid 𝓜.D))
    (x y : V.idx) (d d' : 𝓜.D.idx) (P : LamDK V.idx K.idx) :
    (oid V).eq x y ≤
      eqB (interpDKBodyGraph 𝓜 V K hK hV (η.update hV 𝓜.total y d) x P)
        (interpDKBodyGraph 𝓜 V K hK hV (η.update hV 𝓜.total y d') x P) := by
  have hd :=
    interpDKBodyGraph_update_overwrite_eqB 𝓜 V K hK hV η x y d P
  have hd' :=
    interpDKBodyGraph_update_overwrite_eqB 𝓜 V K hK hV η x y d' P
  exact (eqB_trans
      (interpDKBodyGraph 𝓜 V K hK hV (η.update hV 𝓜.total y d) x P)
      (interpDKBodyGraph 𝓜 V K hK hV η x P)
      (interpDKBodyGraph 𝓜 V K hK hV (η.update hV 𝓜.total y d') x P)).trans' <|
    le_inf hd (hd'.trans_eq (eqB_comm
      (interpDKBodyGraph 𝓜 V K hK hV (η.update hV 𝓜.total y d') x P)
      (interpDKBodyGraph 𝓜 V K hK hV η x P)))

/-- On the diagonal `x = y`, abs body-graph outputs coincide. -/
theorem interpDKBodyGraph_abs_apply_const
    (𝓜 : InternalReflexiveModel (A := A))
    (V K : AName.{u} A) (hK : subsetB K 𝓜.D = ⊤)
    (hV : (oid V).IsTotal)
    (η : RelFun (oid V) (oid 𝓜.D))
    (y x : V.idx) (P : LamDK V.idx K.idx) (a : A)
    (hInner : ∀ d, a ≤ isScottContinuousB
      (interpDKBodyGraph 𝓜 V K hK hV (η.update hV 𝓜.total y d) x P)
      𝓜.D 𝓜.D 𝓜.R 𝓜.R)
    (hInnerRows : ∀ d, ∀ e, IsRelElementAt 𝓜.D a
      (interpDKRelVal 𝓜 V K hK hV
        ((η.update hV 𝓜.total y d).update hV 𝓜.total x e) P))
    (u u' v v' : AName.{u} A) :
    (oid V).eq x y ⊓ a ⊓ lamDKVal V K (.abs x P) ⊓
        memB (opairB u v)
          (interpDKBodyGraph 𝓜 V K hK hV η y (.abs x P)) ⊓
        memB (opairB u' v')
          (interpDKBodyGraph 𝓜 V K hK hV η y (.abs x P)) ≤
      eqB v v' := by
  let Fabs := interpDKBodyGraph 𝓜 V K hK hV η y (.abs x P)
  let b := a ⊓ lamDKVal V K (.abs x P)
  have hfun : b ≤ isFunctionB Fabs 𝓜.D 𝓜.D :=
    interpDKBodyGraph_abs_le_isFunctionB 𝓜 V K hK hV η y x P a
      hInner hInnerRows
  have hrows :=
    interpDKBodyGraph_abs_rows_isRelElementAt 𝓜 V K hK hV η y x P a
      hInner hInnerRows
  let t :=
    (oid V).eq x y ⊓ a ⊓ lamDKVal V K (.abs x P) ⊓
      memB (opairB u v) Fabs ⊓ memB (opairB u' v') Fabs
  change t ≤ eqB v v'
  have htEq : t ≤ (oid V).eq x y :=
    inf_le_left.trans (inf_le_left.trans (inf_le_left.trans inf_le_left))
  have htA : t ≤ a :=
    inf_le_left.trans (inf_le_left.trans (inf_le_left.trans inf_le_right))
  have htLam : t ≤ lamDKVal V K (.abs x P) :=
    inf_le_left.trans (inf_le_left.trans inf_le_right)
  have htB : t ≤ b := le_inf htA htLam
  have htuv : t ≤ memB (opairB u v) Fabs :=
    inf_le_left.trans inf_le_right
  have htu'v' : t ≤ memB (opairB u' v') Fabs :=
    inf_le_right
  have hdec :
      t ≤ ⨆ p : 𝓜.D.idx × 𝓜.D.idx,
        eqB (opairB u v)
          (opairB (𝓜.D.child p.1) (𝓜.D.child p.2)) ⊓
        memB (opairB (𝓜.D.child p.1) (𝓜.D.child p.2)) Fabs :=
    (inf_memB_le_iSup_matrix (hsub := (htB.trans hfun).trans
        (inf_le_left.trans inf_le_left)) (opairB u v)).trans' <|
      le_inf le_rfl htuv
  have hdec' :
      t ≤ ⨆ q : 𝓜.D.idx × 𝓜.D.idx,
        eqB (opairB u' v')
          (opairB (𝓜.D.child q.1) (𝓜.D.child q.2)) ⊓
        memB (opairB (𝓜.D.child q.1) (𝓜.D.child q.2)) Fabs :=
    (inf_memB_le_iSup_matrix (hsub := (htB.trans hfun).trans
        (inf_le_left.trans inf_le_left)) (opairB u' v')).trans' <|
      le_inf le_rfl htu'v'
  refine (le_inf (le_inf le_rfl hdec) hdec').trans ?_
  rw [inf_iSup_eq (α := A)]
  refine iSup_le fun q => ?_
  rw [inf_right_comm, inf_iSup_eq (α := A)]
  refine iSup_le fun p => ?_
  let s :=
    t ⊓
      (eqB (opairB u' v')
        (opairB (𝓜.D.child q.1) (𝓜.D.child q.2)) ⊓
        memB (opairB (𝓜.D.child q.1) (𝓜.D.child q.2)) Fabs) ⊓
      (eqB (opairB u v)
        (opairB (𝓜.D.child p.1) (𝓜.D.child p.2)) ⊓
        memB (opairB (𝓜.D.child p.1) (𝓜.D.child p.2)) Fabs)
  change s ≤ eqB v v'
  have hsT : s ≤ t := inf_le_left.trans inf_le_left
  have hsp : s ≤
      memB (opairB (𝓜.D.child p.1) (𝓜.D.child p.2)) Fabs :=
    inf_le_right.trans inf_le_right
  have hsq : s ≤
      memB (opairB (𝓜.D.child q.1) (𝓜.D.child q.2)) Fabs :=
    inf_le_left.trans (inf_le_right.trans inf_le_right)
  have hvp : s ≤ eqB v (𝓜.D.child p.2) := by
    have hop : s ≤
        eqB (opairB u v)
          (opairB (𝓜.D.child p.1) (𝓜.D.child p.2)) :=
      inf_le_right.trans inf_le_left
    rw [eqB_opairB] at hop
    exact hop.trans inf_le_right
  have hvq : s ≤ eqB v' (𝓜.D.child q.2) := by
    have hop : s ≤
        eqB (opairB u' v')
          (opairB (𝓜.D.child q.1) (𝓜.D.child q.2)) :=
      inf_le_left.trans (inf_le_right.trans inf_le_left)
    rw [eqB_opairB] at hop
    exact hop.trans inf_le_right
  have hnormp :=
    (interpDKBodyGraph_mem_normalize 𝓜 V K hK hV η y (.abs x P)
      b hrows p.1 p.2).2
  have hnormq :=
    (interpDKBodyGraph_mem_normalize 𝓜 V K hK hV η y (.abs x P)
      b hrows q.1 q.2).2
  have hvalp : s ≤
      interpDKRelVal 𝓜 V K hK hV
        (η.update hV 𝓜.total y p.1) (.abs x P) p.2 :=
    hnormp.trans' (le_inf (hsT.trans htB) hsp)
  have hvalq : s ≤
      interpDKRelVal 𝓜 V K hK hV
        (η.update hV 𝓜.total y q.1) (.abs x P) q.2 :=
    hnormq.trans' (le_inf (hsT.trans htB) hsq)
  rw [interpDKRelVal_abs] at hvalp
  rw [interpDKRelVal_abs] at hvalq
  have hbodyEq :=
    interpDKAbsFamily_eqB_of_eq_keys 𝓜 V K hK hV η x y p.1 q.1 P
  have hmemp : s ≤
      memB (opairB
        (interpDKBodyGraph 𝓜 V K hK hV
          (η.update hV 𝓜.total y p.1) x P)
        (𝓜.D.child p.2)) 𝓜.Lam :=
    hvalp.trans inf_le_right
  have hmemq : s ≤
      memB (opairB
        (interpDKBodyGraph 𝓜 V K hK hV
          (η.update hV 𝓜.total y q.1) x P)
        (𝓜.D.child q.2)) 𝓜.Lam :=
    hvalq.trans inf_le_right
  have hmemq' : s ≤
      memB (opairB
        (interpDKBodyGraph 𝓜 V K hK hV
          (η.update hV 𝓜.total y p.1) x P)
        (𝓜.D.child q.2)) 𝓜.Lam :=
    (memB_opairB_congr 𝓜.Lam
        (interpDKBodyGraph 𝓜 V K hK hV
          (η.update hV 𝓜.total y q.1) x P)
        (interpDKBodyGraph 𝓜 V K hK hV
          (η.update hV 𝓜.total y p.1) x P)
        (𝓜.D.child q.2) (𝓜.D.child q.2)).trans' <|
      le_inf (le_inf
          ((hsT.trans htEq).trans hbodyEq |>.trans_eq
            (eqB_comm
              (interpDKBodyGraph 𝓜 V K hK hV
                (η.update hV 𝓜.total y p.1) x P)
              (interpDKBodyGraph 𝓜 V K hK hV
                (η.update hV 𝓜.total y q.1) x P)))
          (le_top.trans (eqB_self (A := A) (𝓜.D.child q.2)).ge))
        hmemq
  have hsv :=
    isSingleValuedB_apply 𝓜.Lam
      (interpDKBodyGraph 𝓜 V K hK hV
        (η.update hV 𝓜.total y p.1) x P)
      (𝓜.D.child p.2) (𝓜.D.child q.2)
  rw [isFunctionB_single 𝓜.lam_function, top_inf_eq] at hsv
  have hpq : s ≤ eqB (𝓜.D.child p.2) (𝓜.D.child q.2) :=
    hsv.trans' (le_inf hmemp hmemq')
  exact (eqB_trans v (𝓜.D.child p.2) v').trans' <|
    le_inf hvp <|
      (eqB_trans (𝓜.D.child p.2) (𝓜.D.child q.2) v').trans' <|
        le_inf hpq (by rw [eqB_comm]; exact hvq)

/-- Degree-local Scott continuity of the abs body graph on the diagonal. -/
theorem interpDKBodyGraph_abs_le_scottContinuous_eq
    (𝓜 : InternalReflexiveModel (A := A))
    (V K : AName.{u} A) (hK : subsetB K 𝓜.D = ⊤)
    (hV : (oid V).IsTotal)
    (η : RelFun (oid V) (oid 𝓜.D))
    (y x : V.idx) (P : LamDK V.idx K.idx) (a : A)
    (hInner : ∀ d, a ≤ isScottContinuousB
      (interpDKBodyGraph 𝓜 V K hK hV (η.update hV 𝓜.total y d) x P)
      𝓜.D 𝓜.D 𝓜.R 𝓜.R)
    (hInnerRows : ∀ d, ∀ e, IsRelElementAt 𝓜.D a
      (interpDKRelVal 𝓜 V K hK hV
        ((η.update hV 𝓜.total y d).update hV 𝓜.total x e) P)) :
    (oid V).eq x y ⊓ a ⊓ lamDKVal V K (.abs x P) ≤
      isScottContinuousB
        (interpDKBodyGraph 𝓜 V K hK hV η y (.abs x P))
        𝓜.D 𝓜.D 𝓜.R 𝓜.R := by
  let Fabs := interpDKBodyGraph 𝓜 V K hK hV η y (.abs x P)
  have hfun : a ⊓ lamDKVal V K (.abs x P) ≤
      isFunctionB Fabs 𝓜.D 𝓜.D :=
    interpDKBodyGraph_abs_le_isFunctionB 𝓜 V K hK hV η y x P a
      hInner hInnerRows
  refine 𝓜.constantMap_le_scottContinuous Fabs
      ((oid V).eq x y ⊓ a ⊓ lamDKVal V K (.abs x P)) ?_ ?_
  · exact (le_inf (inf_le_left.trans inf_le_right) inf_le_right).trans hfun
  · exact interpDKBodyGraph_abs_apply_const 𝓜 V K hK hV η y x P a
      hInner hInnerRows

/-- Inner body graphs of `P` lie in the exact map space. -/
theorem interpDKAbsFamily_mem_mapSpace
    (𝓜 : InternalReflexiveModel (A := A))
    (V K : AName.{u} A) (hK : subsetB K 𝓜.D = ⊤)
    (hV : (oid V).IsTotal)
    (η : RelFun (oid V) (oid 𝓜.D))
    (y x : V.idx) (P : LamDK V.idx K.idx) (a : A)
    (hInner : ∀ d, a ≤ isScottContinuousB
      (interpDKBodyGraph 𝓜 V K hK hV (η.update hV 𝓜.total y d) x P)
      𝓜.D 𝓜.D 𝓜.R 𝓜.R)
    (d : 𝓜.D.idx) :
    a ≤ memB
        (interpDKBodyGraph 𝓜 V K hK hV (η.update hV 𝓜.total y d) x P)
        𝓜.C :=
  (hInner d).trans
    (𝓜.scottContinuous_le_mem_mapSpace
      (interpDKBodyGraph 𝓜 V K hK hV (η.update hV 𝓜.total y d) x P))

/-- Outer body graphs of `P` lie in the exact map space. -/
theorem interpDKAbsOuter_mem_mapSpace
    (𝓜 : InternalReflexiveModel (A := A))
    (V K : AName.{u} A) (hK : subsetB K 𝓜.D = ⊤)
    (hV : (oid V).IsTotal)
    (η : RelFun (oid V) (oid 𝓜.D))
    (y x : V.idx) (P : LamDK V.idx K.idx) (a : A)
    (hOuter : ∀ z, a ≤ isScottContinuousB
      (interpDKBodyGraph 𝓜 V K hK hV (η.update hV 𝓜.total x z) y P)
      𝓜.D 𝓜.D 𝓜.R 𝓜.R)
    (z : 𝓜.D.idx) :
    a ≤ memB
        (interpDKBodyGraph 𝓜 V K hK hV (η.update hV 𝓜.total x z) y P)
        𝓜.C :=
  (hOuter z).trans
    (𝓜.scottContinuous_le_mem_mapSpace
      (interpDKBodyGraph 𝓜 V K hK hV (η.update hV 𝓜.total x z) y P))

/-- Off-diagonal, an inner body-graph edge is an outer body-graph edge. -/
theorem interpDKAbsFamily_inner_le_outer
    (𝓜 : InternalReflexiveModel (A := A))
    (V K : AName.{u} A) (hK : subsetB K 𝓜.D = ⊤)
    (hV : (oid V).IsTotal)
    (η : RelFun (oid V) (oid 𝓜.D))
    (y x : V.idx) (P : LamDK V.idx K.idx) (a : A)
    (hInnerRows : ∀ d, ∀ e, IsRelElementAt 𝓜.D a
      (interpDKRelVal 𝓜 V K hK hV
        ((η.update hV 𝓜.total y d).update hV 𝓜.total x e) P))
    (hOuterRows : ∀ z, ∀ d, IsRelElementAt 𝓜.D a
      (interpDKRelVal 𝓜 V K hK hV
        ((η.update hV 𝓜.total x z).update hV 𝓜.total y d) P))
    (d e w : 𝓜.D.idx) :
    ((oid V).eq x y)ᶜ ⊓ a ⊓
        memB (opairB (𝓜.D.child e) (𝓜.D.child w))
          (interpDKBodyGraph 𝓜 V K hK hV
            (η.update hV 𝓜.total y d) x P) ≤
      memB (opairB (𝓜.D.child d) (𝓜.D.child w))
        (interpDKBodyGraph 𝓜 V K hK hV
          (η.update hV 𝓜.total x e) y P) := by
  let t :=
    ((oid V).eq x y)ᶜ ⊓ a ⊓
      memB (opairB (𝓜.D.child e) (𝓜.D.child w))
        (interpDKBodyGraph 𝓜 V K hK hV
          (η.update hV 𝓜.total y d) x P)
  change t ≤
    memB (opairB (𝓜.D.child d) (𝓜.D.child w))
      (interpDKBodyGraph 𝓜 V K hK hV
        (η.update hV 𝓜.total x e) y P)
  have htEq : t ≤ ((oid V).eq x y)ᶜ :=
    inf_le_left.trans inf_le_left
  have htA : t ≤ a := inf_le_left.trans inf_le_right
  have htmem : t ≤
      memB (opairB (𝓜.D.child e) (𝓜.D.child w))
        (interpDKBodyGraph 𝓜 V K hK hV
          (η.update hV 𝓜.total y d) x P) :=
    inf_le_right
  have hval :
      t ≤ interpDKRelVal 𝓜 V K hK hV
        ((η.update hV 𝓜.total y d).update hV 𝓜.total x e) P w :=
    (interpDKBodyGraph_mem_normalize 𝓜 V K hK hV
        (η.update hV 𝓜.total y d) x P a (hInnerRows d) e w).2.trans' <|
      le_inf htA htmem
  have hcomm :
      t ≤ interpDKRelVal 𝓜 V K hK hV
        ((η.update hV 𝓜.total x e).update hV 𝓜.total y d) P w :=
    (interpDKRelVal_update_commute 𝓜 V K hK hV η x y d e P w).trans' <|
      le_inf htEq hval
  exact (interpDKBodyGraph_mem_normalize 𝓜 V K hK hV
      (η.update hV 𝓜.total x e) y P a (hOuterRows e) d w).1.trans' hcomm

/-- The converse of `interpDKAbsFamily_inner_le_outer`. -/
theorem interpDKAbsFamily_outer_le_inner
    (𝓜 : InternalReflexiveModel (A := A))
    (V K : AName.{u} A) (hK : subsetB K 𝓜.D = ⊤)
    (hV : (oid V).IsTotal)
    (η : RelFun (oid V) (oid 𝓜.D))
    (y x : V.idx) (P : LamDK V.idx K.idx) (a : A)
    (hInnerRows : ∀ d, ∀ e, IsRelElementAt 𝓜.D a
      (interpDKRelVal 𝓜 V K hK hV
        ((η.update hV 𝓜.total y d).update hV 𝓜.total x e) P))
    (hOuterRows : ∀ z, ∀ d, IsRelElementAt 𝓜.D a
      (interpDKRelVal 𝓜 V K hK hV
        ((η.update hV 𝓜.total x z).update hV 𝓜.total y d) P))
    (d e w : 𝓜.D.idx) :
    ((oid V).eq x y)ᶜ ⊓ a ⊓
        memB (opairB (𝓜.D.child d) (𝓜.D.child w))
          (interpDKBodyGraph 𝓜 V K hK hV
            (η.update hV 𝓜.total x e) y P) ≤
      memB (opairB (𝓜.D.child e) (𝓜.D.child w))
        (interpDKBodyGraph 𝓜 V K hK hV
          (η.update hV 𝓜.total y d) x P) := by
  let t :=
    ((oid V).eq x y)ᶜ ⊓ a ⊓
      memB (opairB (𝓜.D.child d) (𝓜.D.child w))
        (interpDKBodyGraph 𝓜 V K hK hV
          (η.update hV 𝓜.total x e) y P)
  change t ≤
    memB (opairB (𝓜.D.child e) (𝓜.D.child w))
      (interpDKBodyGraph 𝓜 V K hK hV
        (η.update hV 𝓜.total y d) x P)
  have htEq : t ≤ ((oid V).eq x y)ᶜ :=
    inf_le_left.trans inf_le_left
  have htA : t ≤ a := inf_le_left.trans inf_le_right
  have htmem : t ≤
      memB (opairB (𝓜.D.child d) (𝓜.D.child w))
        (interpDKBodyGraph 𝓜 V K hK hV
          (η.update hV 𝓜.total x e) y P) :=
    inf_le_right
  have hval :
      t ≤ interpDKRelVal 𝓜 V K hK hV
        ((η.update hV 𝓜.total x e).update hV 𝓜.total y d) P w :=
    (interpDKBodyGraph_mem_normalize 𝓜 V K hK hV
        (η.update hV 𝓜.total x e) y P a (hOuterRows e) d w).2.trans' <|
      le_inf htA htmem
  have hcomm :
      t ≤ interpDKRelVal 𝓜 V K hK hV
        ((η.update hV 𝓜.total y d).update hV 𝓜.total x e) P w :=
    (interpDKRelVal_update_commute_symm 𝓜 V K hK hV η x y d e P w).trans' <|
      le_inf htEq hval
  exact (interpDKBodyGraph_mem_normalize 𝓜 V K hK hV
      (η.update hV 𝓜.total y d) x P a (hInnerRows d) e w).1.trans' hcomm

/-- Displayed abs-body edges are `Lam` applied to the inner graph. -/
theorem interpDKBodyGraph_abs_mem_eq_lam
    (𝓜 : InternalReflexiveModel (A := A))
    (V K : AName.{u} A) (hK : subsetB K 𝓜.D = ⊤)
    (hV : (oid V).IsTotal)
    (η : RelFun (oid V) (oid 𝓜.D))
    (y x : V.idx) (P : LamDK V.idx K.idx) (a : A)
    (hInner : ∀ d, a ≤ isScottContinuousB
      (interpDKBodyGraph 𝓜 V K hK hV (η.update hV 𝓜.total y d) x P)
      𝓜.D 𝓜.D 𝓜.R 𝓜.R)
    (hInnerRows : ∀ d, ∀ e, IsRelElementAt 𝓜.D a
      (interpDKRelVal 𝓜 V K hK hV
        ((η.update hV 𝓜.total y d).update hV 𝓜.total x e) P))
    (d e : 𝓜.D.idx) :
    a ⊓ lamDKVal V K (.abs x P) ⊓
        memB (opairB (𝓜.D.child d) (𝓜.D.child e))
          (interpDKBodyGraph 𝓜 V K hK hV η y (.abs x P)) =
      a ⊓ lamDKVal V K (.abs x P) ⊓
        memB (opairB
          (interpDKBodyGraph 𝓜 V K hK hV
            (η.update hV 𝓜.total y d) x P)
          (𝓜.D.child e)) 𝓜.Lam := by
  have hrows :=
    interpDKBodyGraph_abs_rows_isRelElementAt 𝓜 V K hK hV η y x P a
      hInner hInnerRows
  have hnorm :=
    inf_memB_interpDKBodyGraph_eq 𝓜 V K hK hV η y (.abs x P)
      (a ⊓ lamDKVal V K (.abs x P)) hrows d e
  have hinterp :
      interpDKRelVal 𝓜 V K hK hV
          (η.update hV 𝓜.total y d) (.abs x P) e =
        lamDKVal V K (.abs x P) ⊓
          memB (opairB
            (interpDKBodyGraph 𝓜 V K hK hV
              (η.update hV 𝓜.total y d) x P)
            (𝓜.D.child e)) 𝓜.Lam := by
    rw [interpDKRelVal_abs]
  apply le_antisymm
  · have h := hnorm.le.trans_eq hinterp
    exact le_inf inf_le_left (h.trans inf_le_right)
  · have h : a ⊓ lamDKVal V K (.abs x P) ⊓
        memB (opairB
          (interpDKBodyGraph 𝓜 V K hK hV
            (η.update hV 𝓜.total y d) x P)
          (𝓜.D.child e)) 𝓜.Lam ≤
        interpDKRelVal 𝓜 V K hK hV
          (η.update hV 𝓜.total y d) (.abs x P) e := by
      rw [hinterp]
      exact le_inf (inf_le_left.trans inf_le_right) inf_le_right
    exact h.trans hnorm.ge

/-- Off-diagonal, inner evaluations at a shared argument are monotone in
the outer variable, via the outer body graph. -/
theorem interpDKAbsFamily_eval_mono
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
    (d d' e w w' : 𝓜.D.idx) :
    ((oid V).eq x y)ᶜ ⊓ a ⊓
        relB 𝓜.R (𝓜.D.child d) (𝓜.D.child d') ⊓
        memB (opairB (𝓜.D.child e) (𝓜.D.child w))
          (interpDKBodyGraph 𝓜 V K hK hV
            (η.update hV 𝓜.total y d) x P) ⊓
        memB (opairB (𝓜.D.child e) (𝓜.D.child w'))
          (interpDKBodyGraph 𝓜 V K hK hV
            (η.update hV 𝓜.total y d') x P) ≤
      relB 𝓜.R (𝓜.D.child w) (𝓜.D.child w') := by
  let Fd :=
    interpDKBodyGraph 𝓜 V K hK hV (η.update hV 𝓜.total y d) x P
  let Fd' :=
    interpDKBodyGraph 𝓜 V K hK hV (η.update hV 𝓜.total y d') x P
  let Ge :=
    interpDKBodyGraph 𝓜 V K hK hV (η.update hV 𝓜.total x e) y P
  let t :=
    ((oid V).eq x y)ᶜ ⊓ a ⊓
      relB 𝓜.R (𝓜.D.child d) (𝓜.D.child d') ⊓
      memB (opairB (𝓜.D.child e) (𝓜.D.child w)) Fd ⊓
      memB (opairB (𝓜.D.child e) (𝓜.D.child w')) Fd'
  change t ≤ relB 𝓜.R (𝓜.D.child w) (𝓜.D.child w')
  have htEq : t ≤ ((oid V).eq x y)ᶜ :=
    inf_le_left.trans (inf_le_left.trans
      (inf_le_left.trans inf_le_left))
  have htA : t ≤ a :=
    inf_le_left.trans (inf_le_left.trans
      (inf_le_left.trans inf_le_right))
  have htR : t ≤ relB 𝓜.R (𝓜.D.child d) (𝓜.D.child d') :=
    inf_le_left.trans (inf_le_left.trans inf_le_right)
  have hFd : t ≤
      memB (opairB (𝓜.D.child e) (𝓜.D.child w)) Fd :=
    inf_le_left.trans inf_le_right
  have hFd' : t ≤
      memB (opairB (𝓜.D.child e) (𝓜.D.child w')) Fd' :=
    inf_le_right
  have hGd : t ≤
      memB (opairB (𝓜.D.child d) (𝓜.D.child w)) Ge :=
    (interpDKAbsFamily_inner_le_outer 𝓜 V K hK hV η y x P a
        hInnerRows hOuterRows d e w).trans' <|
      le_inf (le_inf htEq htA) hFd
  have hGd' : t ≤
      memB (opairB (𝓜.D.child d') (𝓜.D.child w')) Ge :=
    (interpDKAbsFamily_inner_le_outer 𝓜 V K hK hV η y x P a
        hInnerRows hOuterRows d' e w').trans' <|
      le_inf (le_inf htEq htA) hFd'
  exact (scottContinuous_apply_mono (hOuter e)
      (𝓜.D.child d) (𝓜.D.child d')
      (𝓜.D.child w) (𝓜.D.child w')).trans' <|
    le_inf (le_inf (le_inf htA hGd) hGd') htR

/-- Off-diagonal, the inner family is `Q`-monotone on displayed inputs. -/
theorem interpDKAbsFamily_relQ
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
    (d d' : 𝓜.D.idx) :
    ((oid V).eq x y)ᶜ ⊓ a ⊓
        relB 𝓜.R (𝓜.D.child d) (𝓜.D.child d') ≤
      relB 𝓜.Q
        (interpDKBodyGraph 𝓜 V K hK hV (η.update hV 𝓜.total y d) x P)
        (interpDKBodyGraph 𝓜 V K hK hV
          (η.update hV 𝓜.total y d') x P) := by
  let Fd :=
    interpDKBodyGraph 𝓜 V K hK hV (η.update hV 𝓜.total y d) x P
  let Fd' :=
    interpDKBodyGraph 𝓜 V K hK hV (η.update hV 𝓜.total y d') x P
  let t :=
    ((oid V).eq x y)ᶜ ⊓ a ⊓
      relB 𝓜.R (𝓜.D.child d) (𝓜.D.child d')
  change t ≤ relB 𝓜.Q Fd Fd'
  have htEq : t ≤ ((oid V).eq x y)ᶜ :=
    inf_le_left.trans inf_le_left
  have htA : t ≤ a := inf_le_left.trans inf_le_right
  have htR : t ≤ relB 𝓜.R (𝓜.D.child d) (𝓜.D.child d') :=
    inf_le_right
  have hFC : t ≤ memB Fd 𝓜.C :=
    htA.trans (interpDKAbsFamily_mem_mapSpace 𝓜 V K hK hV η y x P a
      hInner d)
  have hFC' : t ≤ memB Fd' 𝓜.C :=
    htA.trans (interpDKAbsFamily_mem_mapSpace 𝓜 V K hK hV η y x P a
      hInner d')
  have hfun : t ≤ isFunctionB Fd 𝓜.D 𝓜.D :=
    (𝓜.mem_mapSpace_le_function Fd).trans' hFC
  have hfun' : t ≤ isFunctionB Fd' 𝓜.D 𝓜.D :=
    (𝓜.mem_mapSpace_le_function Fd').trans' hFC'
  have hsub : t ≤ subsetB Fd (prodB 𝓜.D 𝓜.D) :=
    hfun.trans (inf_le_left.trans inf_le_left)
  have hsub' : t ≤ subsetB Fd' (prodB 𝓜.D 𝓜.D) :=
    hfun'.trans (inf_le_left.trans inf_le_left)
  have hpw : t ≤ pointwiseLeB Fd Fd' 𝓜.D 𝓜.R := by
    unfold pointwiseLeB
    refine le_iInf fun s => le_iInf fun v => le_iInf fun v' => ?_
    rw [le_himp_iff]
    let u :=
      t ⊓ (memB s 𝓜.D ⊓ memB (opairB s v) Fd ⊓
        memB (opairB s v') Fd')
    change u ≤ relB 𝓜.R v v'
    have huT : u ≤ t := inf_le_left
    have huD : u ≤ memB s 𝓜.D :=
      inf_le_right.trans (inf_le_left.trans inf_le_left)
    have huF : u ≤ memB (opairB s v) Fd :=
      inf_le_right.trans (inf_le_left.trans inf_le_right)
    have huF' : u ≤ memB (opairB s v') Fd' :=
      inf_le_right.trans inf_le_right
    have hdec :
        u ≤ ⨆ p : 𝓜.D.idx × 𝓜.D.idx,
          eqB (opairB s v)
            (opairB (𝓜.D.child p.1) (𝓜.D.child p.2)) ⊓
          memB (opairB (𝓜.D.child p.1) (𝓜.D.child p.2)) Fd :=
      (inf_memB_le_iSup_matrix (hsub := huT.trans hsub)
          (opairB s v)).trans' <|
        le_inf le_rfl huF
    have hdec' :
        u ≤ ⨆ q : 𝓜.D.idx × 𝓜.D.idx,
          eqB (opairB s v')
            (opairB (𝓜.D.child q.1) (𝓜.D.child q.2)) ⊓
          memB (opairB (𝓜.D.child q.1) (𝓜.D.child q.2)) Fd' :=
      (inf_memB_le_iSup_matrix (hsub := huT.trans hsub')
          (opairB s v')).trans' <|
        le_inf le_rfl huF'
    refine (le_inf (le_inf le_rfl hdec) hdec').trans ?_
    rw [inf_iSup_eq (α := A)]
    refine iSup_le fun q => ?_
    rw [inf_right_comm, inf_iSup_eq (α := A)]
    refine iSup_le fun p => ?_
    let r :=
      u ⊓
        (eqB (opairB s v')
          (opairB (𝓜.D.child q.1) (𝓜.D.child q.2)) ⊓
          memB (opairB (𝓜.D.child q.1) (𝓜.D.child q.2)) Fd') ⊓
        (eqB (opairB s v)
          (opairB (𝓜.D.child p.1) (𝓜.D.child p.2)) ⊓
          memB (opairB (𝓜.D.child p.1) (𝓜.D.child p.2)) Fd)
    change r ≤ relB 𝓜.R v v'
    have hrU : r ≤ u := inf_le_left.trans inf_le_left
    have hrp : r ≤
        memB (opairB (𝓜.D.child p.1) (𝓜.D.child p.2)) Fd :=
      inf_le_right.trans inf_le_right
    have hrq : r ≤
        memB (opairB (𝓜.D.child q.1) (𝓜.D.child q.2)) Fd' :=
      inf_le_left.trans (inf_le_right.trans inf_le_right)
    have hop : r ≤
        eqB (opairB s v)
          (opairB (𝓜.D.child p.1) (𝓜.D.child p.2)) :=
      inf_le_right.trans inf_le_left
    have hoq : r ≤
        eqB (opairB s v')
          (opairB (𝓜.D.child q.1) (𝓜.D.child q.2)) :=
      inf_le_left.trans (inf_le_right.trans inf_le_left)
    have hvp : r ≤ eqB v (𝓜.D.child p.2) := by
      rw [eqB_opairB] at hop
      exact hop.trans inf_le_right
    have hvq : r ≤ eqB v' (𝓜.D.child q.2) := by
      rw [eqB_opairB] at hoq
      exact hoq.trans inf_le_right
    have hsp : r ≤ eqB s (𝓜.D.child p.1) := by
      rw [eqB_opairB] at hop
      exact hop.trans inf_le_left
    have hsq : r ≤ eqB s (𝓜.D.child q.1) := by
      rw [eqB_opairB] at hoq
      exact hoq.trans inf_le_left
    have heq : r ≤ eqB (𝓜.D.child p.1) (𝓜.D.child q.1) :=
      (eqB_trans (𝓜.D.child p.1) s (𝓜.D.child q.1)).trans' <|
        le_inf (by rw [eqB_comm]; exact hsp) hsq
    have hsameArg : r ≤
        memB (opairB (𝓜.D.child p.1) (𝓜.D.child q.2)) Fd' :=
      (memB_opairB_congr Fd' (𝓜.D.child q.1) (𝓜.D.child p.1)
          (𝓜.D.child q.2) (𝓜.D.child q.2)).trans' <|
        le_inf (le_inf
            (heq.trans_eq (eqB_comm (𝓜.D.child p.1) (𝓜.D.child q.1)))
            (le_top.trans (eqB_self (A := A) (𝓜.D.child q.2)).ge))
          hrq
    have hmono : r ≤
        relB 𝓜.R (𝓜.D.child p.2) (𝓜.D.child q.2) :=
      (interpDKAbsFamily_eval_mono 𝓜 V K hK hV η y x P a
          hOuter hInnerRows hOuterRows d d' p.1 p.2 q.2).trans' <|
        le_inf (le_inf (le_inf (le_inf
            (hrU.trans (huT.trans htEq))
            (hrU.trans (huT.trans htA)))
          (hrU.trans (huT.trans htR)))
          hrp) hsameArg
    exact (relB_congr 𝓜.R (𝓜.D.child p.2) v (𝓜.D.child q.2) v').trans' <|
      le_inf (le_inf
          (hvp.trans_eq (eqB_comm v (𝓜.D.child p.2)))
          (hvq.trans_eq (eqB_comm v' (𝓜.D.child q.2))))
        hmono
  exact (𝓜.pointwise_le_relQ Fd Fd').trans' <|
    le_inf (le_inf hFC hFC') hpw

/-- Off-diagonal monotonicity of the abs body graph. -/
theorem interpDKBodyGraph_abs_apply_mono
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
    (u u' v v' : AName.{u} A) :
    ((oid V).eq x y)ᶜ ⊓ a ⊓ lamDKVal V K (.abs x P) ⊓
        memB (opairB u v)
          (interpDKBodyGraph 𝓜 V K hK hV η y (.abs x P)) ⊓
        memB (opairB u' v')
          (interpDKBodyGraph 𝓜 V K hK hV η y (.abs x P)) ⊓
        relB 𝓜.R u u' ≤
      relB 𝓜.R v v' := by
  let Fabs := interpDKBodyGraph 𝓜 V K hK hV η y (.abs x P)
  let b := a ⊓ lamDKVal V K (.abs x P)
  have hfun : b ≤ isFunctionB Fabs 𝓜.D 𝓜.D :=
    interpDKBodyGraph_abs_le_isFunctionB 𝓜 V K hK hV η y x P a
      hInner hInnerRows
  have hrows :=
    interpDKBodyGraph_abs_rows_isRelElementAt 𝓜 V K hK hV η y x P a
      hInner hInnerRows
  let t :=
    ((oid V).eq x y)ᶜ ⊓ a ⊓ lamDKVal V K (.abs x P) ⊓
      memB (opairB u v) Fabs ⊓ memB (opairB u' v') Fabs ⊓
      relB 𝓜.R u u'
  change t ≤ relB 𝓜.R v v'
  have htEq : t ≤ ((oid V).eq x y)ᶜ :=
    inf_le_left.trans (inf_le_left.trans
      (inf_le_left.trans (inf_le_left.trans inf_le_left)))
  have htA : t ≤ a :=
    inf_le_left.trans (inf_le_left.trans
      (inf_le_left.trans (inf_le_left.trans inf_le_right)))
  have htLam : t ≤ lamDKVal V K (.abs x P) :=
    inf_le_left.trans (inf_le_left.trans
      (inf_le_left.trans inf_le_right))
  have htB : t ≤ b := le_inf htA htLam
  have htuv : t ≤ memB (opairB u v) Fabs :=
    inf_le_left.trans (inf_le_left.trans inf_le_right)
  have htu'v' : t ≤ memB (opairB u' v') Fabs :=
    inf_le_left.trans inf_le_right
  have htR : t ≤ relB 𝓜.R u u' := inf_le_right
  have hdec :
      t ≤ ⨆ p : 𝓜.D.idx × 𝓜.D.idx,
        eqB (opairB u v)
          (opairB (𝓜.D.child p.1) (𝓜.D.child p.2)) ⊓
        memB (opairB (𝓜.D.child p.1) (𝓜.D.child p.2)) Fabs :=
    (inf_memB_le_iSup_matrix (hsub := (htB.trans hfun).trans
        (inf_le_left.trans inf_le_left)) (opairB u v)).trans' <|
      le_inf le_rfl htuv
  have hdec' :
      t ≤ ⨆ q : 𝓜.D.idx × 𝓜.D.idx,
        eqB (opairB u' v')
          (opairB (𝓜.D.child q.1) (𝓜.D.child q.2)) ⊓
        memB (opairB (𝓜.D.child q.1) (𝓜.D.child q.2)) Fabs :=
    (inf_memB_le_iSup_matrix (hsub := (htB.trans hfun).trans
        (inf_le_left.trans inf_le_left)) (opairB u' v')).trans' <|
      le_inf le_rfl htu'v'
  refine (le_inf (le_inf le_rfl hdec) hdec').trans ?_
  rw [inf_iSup_eq (α := A)]
  refine iSup_le fun q => ?_
  rw [inf_right_comm, inf_iSup_eq (α := A)]
  refine iSup_le fun p => ?_
  let s :=
    t ⊓
      (eqB (opairB u' v')
        (opairB (𝓜.D.child q.1) (𝓜.D.child q.2)) ⊓
        memB (opairB (𝓜.D.child q.1) (𝓜.D.child q.2)) Fabs) ⊓
      (eqB (opairB u v)
        (opairB (𝓜.D.child p.1) (𝓜.D.child p.2)) ⊓
        memB (opairB (𝓜.D.child p.1) (𝓜.D.child p.2)) Fabs)
  change s ≤ relB 𝓜.R v v'
  have hsT : s ≤ t := inf_le_left.trans inf_le_left
  have hsp : s ≤
      memB (opairB (𝓜.D.child p.1) (𝓜.D.child p.2)) Fabs :=
    inf_le_right.trans inf_le_right
  have hsq : s ≤
      memB (opairB (𝓜.D.child q.1) (𝓜.D.child q.2)) Fabs :=
    inf_le_left.trans (inf_le_right.trans inf_le_right)
  have hop : s ≤
      eqB (opairB u v)
        (opairB (𝓜.D.child p.1) (𝓜.D.child p.2)) :=
    inf_le_right.trans inf_le_left
  have hoq : s ≤
      eqB (opairB u' v')
        (opairB (𝓜.D.child q.1) (𝓜.D.child q.2)) :=
    inf_le_left.trans (inf_le_right.trans inf_le_left)
  have hup : s ≤ eqB u (𝓜.D.child p.1) := by
    rw [eqB_opairB] at hop
    exact hop.trans inf_le_left
  have huq : s ≤ eqB u' (𝓜.D.child q.1) := by
    rw [eqB_opairB] at hoq
    exact hoq.trans inf_le_left
  have hvp : s ≤ eqB v (𝓜.D.child p.2) := by
    rw [eqB_opairB] at hop
    exact hop.trans inf_le_right
  have hvq : s ≤ eqB v' (𝓜.D.child q.2) := by
    rw [eqB_opairB] at hoq
    exact hoq.trans inf_le_right
  have hRpq : s ≤ relB 𝓜.R (𝓜.D.child p.1) (𝓜.D.child q.1) :=
    (relB_congr 𝓜.R u (𝓜.D.child p.1) u' (𝓜.D.child q.1)).trans' <|
      le_inf (le_inf hup huq) (hsT.trans htR)
  have hQ : s ≤
      relB 𝓜.Q
        (interpDKBodyGraph 𝓜 V K hK hV
          (η.update hV 𝓜.total y p.1) x P)
        (interpDKBodyGraph 𝓜 V K hK hV
          (η.update hV 𝓜.total y q.1) x P) :=
    (interpDKAbsFamily_relQ 𝓜 V K hK hV η y x P a
        hInner hOuter hInnerRows hOuterRows p.1 q.1).trans' <|
      le_inf (le_inf (hsT.trans htEq) (hsT.trans htA)) hRpq
  have hmemp : s ≤
      memB (opairB
        (interpDKBodyGraph 𝓜 V K hK hV
          (η.update hV 𝓜.total y p.1) x P)
        (𝓜.D.child p.2)) 𝓜.Lam := by
    have h :=
      (interpDKBodyGraph_abs_mem_eq_lam 𝓜 V K hK hV η y x P a
          hInner hInnerRows p.1 p.2).le
    exact h.trans' (le_inf (hsT.trans htB) hsp) |>.trans inf_le_right
  have hmemq : s ≤
      memB (opairB
        (interpDKBodyGraph 𝓜 V K hK hV
          (η.update hV 𝓜.total y q.1) x P)
        (𝓜.D.child q.2)) 𝓜.Lam := by
    have h :=
      (interpDKBodyGraph_abs_mem_eq_lam 𝓜 V K hK hV η y x P a
          hInner hInnerRows q.1 q.2).le
    exact h.trans' (le_inf (hsT.trans htB) hsq) |>.trans inf_le_right
  have hLam : (⊤ : A) ≤
      isScottContinuousB 𝓜.Lam 𝓜.C 𝓜.D 𝓜.Q 𝓜.R :=
    le_top.trans 𝓜.lam_continuous.ge
  have hpq : s ≤ relB 𝓜.R (𝓜.D.child p.2) (𝓜.D.child q.2) :=
    (scottContinuous_apply_mono hLam
        (interpDKBodyGraph 𝓜 V K hK hV
          (η.update hV 𝓜.total y p.1) x P)
        (interpDKBodyGraph 𝓜 V K hK hV
          (η.update hV 𝓜.total y q.1) x P)
        (𝓜.D.child p.2) (𝓜.D.child q.2)).trans' <|
      le_inf (le_inf (le_inf (le_top.trans le_top) hmemp) hmemq) hQ
  exact (relB_congr 𝓜.R (𝓜.D.child p.2) v (𝓜.D.child q.2) v').trans' <|
    le_inf (le_inf
        (hvp.trans_eq (eqB_comm v (𝓜.D.child p.2)))
        (hvq.trans_eq (eqB_comm v' (𝓜.D.child q.2))))
      hpq

/-- Inner body graphs respect equality of the outer argument. -/
theorem interpDKAbsFamily_eqB_of_arg
    (𝓜 : InternalReflexiveModel (A := A))
    (V K : AName.{u} A) (hK : subsetB K 𝓜.D = ⊤)
    (hV : (oid V).IsTotal)
    (η : RelFun (oid V) (oid 𝓜.D))
    (y x : V.idx) (d d' : 𝓜.D.idx) (P : LamDK V.idx K.idx) :
    (oid 𝓜.D).eq d d' ≤
      eqB (interpDKBodyGraph 𝓜 V K hK hV (η.update hV 𝓜.total y d) x P)
        (interpDKBodyGraph 𝓜 V K hK hV
          (η.update hV 𝓜.total y d') x P) := by
  let body (w : 𝓜.D.idx) :=
    interpDKBodyGraph 𝓜 V K hK hV (η.update hV 𝓜.total y w) x P
  have hη : RelFun.IsPointwiseFamily (oid 𝓜.D)
      (fun w => η.update hV 𝓜.total y w) :=
    RelFun.isPointwiseFamily_update η hV 𝓜.total y
  have htransport : ∀ w₁ w₂ p, (oid 𝓜.D).eq w₁ w₂ ⊓
      (body w₁).val p ≤ (body w₂).val p := by
    intro w₁ w₂ p
    let replacement : 𝓜.D.idx → 𝓜.D.idx := fun _ => p.1
    have hrepl : APoset.Functional (oid 𝓜.D) (oid 𝓜.D) replacement := by
      intro z₁ z₂
      change (oid 𝓜.D).eq z₁ z₂ ≤ (oid 𝓜.D).eps p.1
      rw [𝓜.total p.1]
      exact le_top
    have hupd := hη.update hV 𝓜.total x replacement hrepl
    exact interpDKRelVal_isPointwiseFamily 𝓜 V K hK hV
      (oid 𝓜.D) (fun w => (η.update hV 𝓜.total y w).update hV 𝓜.total x p.1)
      hupd P w₁ w₂ p.2
  exact le_eqB_mk_of_le_val
    (fun p : 𝓜.D.idx × 𝓜.D.idx =>
      opairB (𝓜.D.child p.1) (𝓜.D.child p.2))
    (body d).val (body d').val ((oid 𝓜.D).eq d d')
    (fun p => htransport d d' p)
    (fun p => by
      have h := htransport d' d p
      rwa [(oid 𝓜.D).symm d' d] at h)

/-- The graph of the inner family `d ↦ ⟦P⟧ρ[y:=d]` as a map `D → C`. -/
noncomputable def interpDKAbsFamilyGraph
    (𝓜 : InternalReflexiveModel (A := A))
    (V K : AName.{u} A) (hK : subsetB K 𝓜.D = ⊤)
    (hV : (oid V).IsTotal)
    (η : RelFun (oid V) (oid 𝓜.D))
    (y x : V.idx) (P : LamDK V.idx K.idx) : AName.{u} A :=
  mk 𝓜.D.idx
    (fun d =>
      opairB (𝓜.D.child d)
        (interpDKBodyGraph 𝓜 V K hK hV (η.update hV 𝓜.total y d) x P))
    (fun _ => ⊤)

theorem memB_interpDKAbsFamilyGraph
    (𝓜 : InternalReflexiveModel (A := A))
    (V K : AName.{u} A) (hK : subsetB K 𝓜.D = ⊤)
    (hV : (oid V).IsTotal)
    (η : RelFun (oid V) (oid 𝓜.D))
    (y x : V.idx) (P : LamDK V.idx K.idx)
    (u G : AName.{u} A) :
    memB (opairB u G)
        (interpDKAbsFamilyGraph 𝓜 V K hK hV η y x P) =
      ⨆ d : 𝓜.D.idx,
        eqB u (𝓜.D.child d) ⊓
          eqB G
            (interpDKBodyGraph 𝓜 V K hK hV
              (η.update hV 𝓜.total y d) x P) := by
  unfold interpDKAbsFamilyGraph
  rw [memB_mk]
  refine iSup_congr fun d => ?_
  rw [eqB_opairB, inf_top_eq]

/-- Displayed family-graph edges recover the inner body graph. -/
theorem memB_interpDKAbsFamilyGraph_child
    (𝓜 : InternalReflexiveModel (A := A))
    (V K : AName.{u} A) (hK : subsetB K 𝓜.D = ⊤)
    (hV : (oid V).IsTotal)
    (η : RelFun (oid V) (oid 𝓜.D))
    (y x : V.idx) (P : LamDK V.idx K.idx) (d : 𝓜.D.idx) :
    memB (opairB (𝓜.D.child d)
        (interpDKBodyGraph 𝓜 V K hK hV (η.update hV 𝓜.total y d) x P))
      (interpDKAbsFamilyGraph 𝓜 V K hK hV η y x P) = ⊤ := by
  rw [memB_interpDKAbsFamilyGraph]
  refine top_unique (le_iSup_of_le d ?_)
  rw [eqB_self, eqB_self, top_inf_eq]

/-- The inner family graph is a degree-local function `D → C`. -/
theorem interpDKAbsFamilyGraph_le_isFunctionB
    (𝓜 : InternalReflexiveModel (A := A))
    (V K : AName.{u} A) (hK : subsetB K 𝓜.D = ⊤)
    (hV : (oid V).IsTotal)
    (η : RelFun (oid V) (oid 𝓜.D))
    (y x : V.idx) (P : LamDK V.idx K.idx) (a : A)
    (hInner : ∀ d, a ≤ isScottContinuousB
      (interpDKBodyGraph 𝓜 V K hK hV (η.update hV 𝓜.total y d) x P)
      𝓜.D 𝓜.D 𝓜.R 𝓜.R) :
    a ≤ isFunctionB
      (interpDKAbsFamilyGraph 𝓜 V K hK hV η y x P) 𝓜.D 𝓜.C := by
  let Fg := interpDKAbsFamilyGraph 𝓜 V K hK hV η y x P
  unfold isFunctionB
  refine le_inf (le_inf ?_ ?_) ?_
  · unfold interpDKAbsFamilyGraph
    rw [subsetB_mk]
    refine le_iInf fun d => ?_
    rw [le_himp_iff, memB_opairB_prodB]
    have hD : memB (𝓜.D.child d) 𝓜.D = ⊤ := by
      rw [← oid_eps]
      exact 𝓜.total d
    rw [hD, top_inf_eq]
    exact inf_le_left.trans
      (interpDKAbsFamily_mem_mapSpace 𝓜 V K hK hV η y x P a hInner d)
  · refine le_iInf fun u => le_iInf fun G => le_iInf fun G' => ?_
    rw [le_himp_iff]
    let t0 :=
      a ⊓
        (memB (opairB u G)
          (interpDKAbsFamilyGraph 𝓜 V K hK hV η y x P) ⊓
        memB (opairB u G')
          (interpDKAbsFamilyGraph 𝓜 V K hK hV η y x P))
    change t0 ≤ eqB G G'
    have hdec :
        t0 ≤ ⨆ d : 𝓜.D.idx,
          eqB u (𝓜.D.child d) ⊓
            eqB G
              (interpDKBodyGraph 𝓜 V K hK hV
                (η.update hV 𝓜.total y d) x P) :=
      (inf_le_right.trans inf_le_left).trans_eq
        (memB_interpDKAbsFamilyGraph 𝓜 V K hK hV η y x P u G)
    have hdec' :
        t0 ≤ ⨆ d' : 𝓜.D.idx,
          eqB u (𝓜.D.child d') ⊓
            eqB G'
              (interpDKBodyGraph 𝓜 V K hK hV
                (η.update hV 𝓜.total y d') x P) :=
      (inf_le_right.trans inf_le_right).trans_eq
        (memB_interpDKAbsFamilyGraph 𝓜 V K hK hV η y x P u G')
    refine (le_inf (le_inf le_rfl hdec) hdec').trans ?_
    rw [inf_iSup_eq (α := A)]
    refine iSup_le fun d' => ?_
    rw [inf_right_comm, inf_iSup_eq (α := A)]
    refine iSup_le fun d => ?_
    let t :=
      t0 ⊓
        (eqB u (𝓜.D.child d') ⊓
          eqB G'
            (interpDKBodyGraph 𝓜 V K hK hV
              (η.update hV 𝓜.total y d') x P)) ⊓
        (eqB u (𝓜.D.child d) ⊓
          eqB G
            (interpDKBodyGraph 𝓜 V K hK hV
              (η.update hV 𝓜.total y d) x P))
    change t ≤ eqB G G'
    have hdd' : t ≤ (oid 𝓜.D).eq d d' := by
      rw [oid_eq_of_total 𝓜.D 𝓜.total]
      exact (eqB_trans (𝓜.D.child d) u (𝓜.D.child d')).trans' <|
        le_inf (by
            rw [eqB_comm]
            exact inf_le_right.trans inf_le_left)
          (inf_le_left.trans (inf_le_right.trans inf_le_left))
    have hbody :=
      interpDKAbsFamily_eqB_of_arg 𝓜 V K hK hV η y x d d' P
    have hGG' : t ≤
        eqB
          (interpDKBodyGraph 𝓜 V K hK hV
            (η.update hV 𝓜.total y d) x P)
          (interpDKBodyGraph 𝓜 V K hK hV
            (η.update hV 𝓜.total y d') x P) :=
      hdd'.trans hbody
    exact (eqB_trans G
        (interpDKBodyGraph 𝓜 V K hK hV
          (η.update hV 𝓜.total y d) x P) G').trans' <|
      le_inf (inf_le_right.trans inf_le_right)
        ((eqB_trans
            (interpDKBodyGraph 𝓜 V K hK hV
              (η.update hV 𝓜.total y d) x P)
            (interpDKBodyGraph 𝓜 V K hK hV
              (η.update hV 𝓜.total y d') x P)
            G').trans' <|
          le_inf hGG'
            (by
              rw [eqB_comm]
              exact inf_le_left.trans (inf_le_right.trans inf_le_right)))
  · refine le_iInf fun u => ?_
    rw [le_himp_iff]
    have hfunD : a ⊓ memB u 𝓜.D ≤
        ⨆ d : 𝓜.D.idx, eqB u (𝓜.D.child d) := by
      rw [memB_eq (x := u) (y := 𝓜.D), inf_iSup_eq]
      refine iSup_le fun d => le_iSup_of_le d ?_
      exact inf_le_right.trans inf_le_left
    refine (le_inf le_rfl hfunD).trans ?_
    rw [inf_iSup_eq (α := A)]
    refine iSup_le fun d => le_iSup_of_le
        (interpDKBodyGraph 𝓜 V K hK hV
          (η.update hV 𝓜.total y d) x P) ?_
    rw [memB_interpDKAbsFamilyGraph]
    refine le_iSup_of_le d ?_
    exact le_inf inf_le_right
      (le_top.trans
        (eqB_self (A := A)
          (interpDKBodyGraph 𝓜 V K hK hV
            (η.update hV 𝓜.total y d) x P)).ge)

/-- Off-diagonal, the inner family graph is `Q`-monotone. -/
theorem interpDKAbsFamilyGraph_apply_mono
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
    (u u' G G' : AName.{u} A) :
    ((oid V).eq x y)ᶜ ⊓ a ⊓
        memB (opairB u G)
          (interpDKAbsFamilyGraph 𝓜 V K hK hV η y x P) ⊓
        memB (opairB u' G')
          (interpDKAbsFamilyGraph 𝓜 V K hK hV η y x P) ⊓
        relB 𝓜.R u u' ≤
      relB 𝓜.Q G G' := by
  let t0 :=
    ((oid V).eq x y)ᶜ ⊓ a ⊓
      memB (opairB u G)
        (interpDKAbsFamilyGraph 𝓜 V K hK hV η y x P) ⊓
      memB (opairB u' G')
        (interpDKAbsFamilyGraph 𝓜 V K hK hV η y x P) ⊓
      relB 𝓜.R u u'
  change t0 ≤ relB 𝓜.Q G G'
  have htEq : t0 ≤ ((oid V).eq x y)ᶜ :=
    inf_le_left.trans (inf_le_left.trans
      (inf_le_left.trans inf_le_left))
  have htA : t0 ≤ a :=
    inf_le_left.trans (inf_le_left.trans
      (inf_le_left.trans inf_le_right))
  have htR : t0 ≤ relB 𝓜.R u u' := inf_le_right
  have hdec :
      t0 ≤ ⨆ d : 𝓜.D.idx,
        eqB u (𝓜.D.child d) ⊓
          eqB G
            (interpDKBodyGraph 𝓜 V K hK hV
              (η.update hV 𝓜.total y d) x P) :=
    (inf_le_left.trans (inf_le_left.trans inf_le_right)).trans_eq
      (memB_interpDKAbsFamilyGraph 𝓜 V K hK hV η y x P u G)
  have hdec' :
      t0 ≤ ⨆ d' : 𝓜.D.idx,
        eqB u' (𝓜.D.child d') ⊓
          eqB G'
            (interpDKBodyGraph 𝓜 V K hK hV
              (η.update hV 𝓜.total y d') x P) :=
    (inf_le_left.trans inf_le_right).trans_eq
      (memB_interpDKAbsFamilyGraph 𝓜 V K hK hV η y x P u' G')
  refine (le_inf (le_inf le_rfl hdec) hdec').trans ?_
  rw [inf_iSup_eq (α := A)]
  refine iSup_le fun d' => ?_
  rw [inf_right_comm, inf_iSup_eq (α := A)]
  refine iSup_le fun d => ?_
  let s :=
    t0 ⊓
      (eqB u' (𝓜.D.child d') ⊓
        eqB G'
          (interpDKBodyGraph 𝓜 V K hK hV
            (η.update hV 𝓜.total y d') x P)) ⊓
      (eqB u (𝓜.D.child d) ⊓
        eqB G
          (interpDKBodyGraph 𝓜 V K hK hV
            (η.update hV 𝓜.total y d) x P))
  change s ≤ relB 𝓜.Q G G'
  have hsT : s ≤ t0 := inf_le_left.trans inf_le_left
  have hup : s ≤ eqB u (𝓜.D.child d) :=
    inf_le_right.trans inf_le_left
  have huq : s ≤ eqB u' (𝓜.D.child d') :=
    inf_le_left.trans (inf_le_right.trans inf_le_left)
  have hGp : s ≤
      eqB G
        (interpDKBodyGraph 𝓜 V K hK hV
          (η.update hV 𝓜.total y d) x P) :=
    inf_le_right.trans inf_le_right
  have hGq : s ≤
      eqB G'
        (interpDKBodyGraph 𝓜 V K hK hV
          (η.update hV 𝓜.total y d') x P) :=
    inf_le_left.trans (inf_le_right.trans inf_le_right)
  have hRpq : s ≤ relB 𝓜.R (𝓜.D.child d) (𝓜.D.child d') :=
    (relB_congr 𝓜.R u (𝓜.D.child d) u' (𝓜.D.child d')).trans' <|
      le_inf (le_inf hup huq) (hsT.trans htR)
  have hQ : s ≤
      relB 𝓜.Q
        (interpDKBodyGraph 𝓜 V K hK hV
          (η.update hV 𝓜.total y d) x P)
        (interpDKBodyGraph 𝓜 V K hK hV
          (η.update hV 𝓜.total y d') x P) :=
    (interpDKAbsFamily_relQ 𝓜 V K hK hV η y x P a
        hInner hOuter hInnerRows hOuterRows d d').trans' <|
      le_inf (le_inf (hsT.trans htEq) (hsT.trans htA)) hRpq
  exact (relB_congr 𝓜.Q
      (interpDKBodyGraph 𝓜 V K hK hV
        (η.update hV 𝓜.total y d) x P) G
      (interpDKBodyGraph 𝓜 V K hK hV
        (η.update hV 𝓜.total y d') x P) G').trans' <|
    le_inf (le_inf
        (hGp.trans_eq (eqB_comm G
          (interpDKBodyGraph 𝓜 V K hK hV
            (η.update hV 𝓜.total y d) x P)))
        (hGq.trans_eq (eqB_comm G'
          (interpDKBodyGraph 𝓜 V K hK hV
            (η.update hV 𝓜.total y d') x P))))
      hQ

/-- The inner family sends directed subsets of `D` to directed subsets of `C`. -/
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

/-- The displayed inner graph is below every `Q`-upper bound of the
family image. -/
theorem interpDKAbsFamily_image_least
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
        isDirectedRelB S 𝓜.D 𝓜.R ⊓
        isSupRelB (𝓜.D.child d) S 𝓜.R ⊓
        isUpperBoundRelB G
          (graphImageB
            (interpDKAbsFamilyGraph 𝓜 V K hK hV η y x P) S 𝓜.C)
          𝓜.Q ≤
      relB 𝓜.Q
        (interpDKBodyGraph 𝓜 V K hK hV (η.update hV 𝓜.total y d) x P)
        G := by
  let Fg := interpDKAbsFamilyGraph 𝓜 V K hK hV η y x P
  let Fd :=
    interpDKBodyGraph 𝓜 V K hK hV (η.update hV 𝓜.total y d) x P
  let Img := graphImageB Fg S 𝓜.C
  let t :=
    ((oid V).eq x y)ᶜ ⊓ a ⊓
      isDirectedRelB S 𝓜.D 𝓜.R ⊓
      isSupRelB (𝓜.D.child d) S 𝓜.R ⊓
      isUpperBoundRelB G Img 𝓜.Q
  change t ≤ relB 𝓜.Q Fd G
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
  have htUb : t ≤ isUpperBoundRelB G Img 𝓜.Q := inf_le_right
  have hImgDir : t ≤ isDirectedRelB Img 𝓜.C 𝓜.Q :=
    (interpDKAbsFamilyGraph_image_directed 𝓜 V K hK hV η y x P a
        hInner hOuter hInnerRows hOuterRows S).trans' <|
      le_inf (le_inf htEq htA) htDir
  have hFC : t ≤ memB Fd 𝓜.C :=
    htA.trans (interpDKAbsFamily_mem_mapSpace 𝓜 V K hK hV η y x P a
      hInner d)
  have hGC : t ≤ memB G 𝓜.C :=
    (𝓜.isUpperBoundRelB_le_mem_mapSpace G Img).trans' <|
      le_inf (hImgDir.trans (isDirectedRelB_nonempty Img 𝓜.C 𝓜.Q))
        htUb
  have hfunG : t ≤ isFunctionB G 𝓜.D 𝓜.D :=
    (𝓜.mem_mapSpace_le_function G).trans' hGC
  have hsubG : t ≤ subsetB G (prodB 𝓜.D 𝓜.D) :=
    hfunG.trans (inf_le_left.trans inf_le_left)
  have hfunF : t ≤ isFunctionB Fd 𝓜.D 𝓜.D :=
    (𝓜.mem_mapSpace_le_function Fd).trans' hFC
  have hsubF : t ≤ subsetB Fd (prodB 𝓜.D 𝓜.D) :=
    hfunF.trans (inf_le_left.trans inf_le_left)
  have hpw : t ≤ pointwiseLeB Fd G 𝓜.D 𝓜.R := by
    unfold pointwiseLeB
    refine le_iInf fun s => le_iInf fun v => le_iInf fun v' => ?_
    rw [le_himp_iff]
    let u :=
      t ⊓ (memB s 𝓜.D ⊓ memB (opairB s v) Fd ⊓ memB (opairB s v') G)
    change u ≤ relB 𝓜.R v v'
    have huT : u ≤ t := inf_le_left
    have huF : u ≤ memB (opairB s v) Fd :=
      inf_le_right.trans (inf_le_left.trans inf_le_right)
    have huG : u ≤ memB (opairB s v') G :=
      inf_le_right.trans inf_le_right
    have hdec :
        u ≤ ⨆ p : 𝓜.D.idx × 𝓜.D.idx,
          eqB (opairB s v)
            (opairB (𝓜.D.child p.1) (𝓜.D.child p.2)) ⊓
          memB (opairB (𝓜.D.child p.1) (𝓜.D.child p.2)) Fd :=
      (inf_memB_le_iSup_matrix (hsub := huT.trans hsubF)
          (opairB s v)).trans' <|
        le_inf le_rfl huF
    have hdec' :
        u ≤ ⨆ q : 𝓜.D.idx × 𝓜.D.idx,
          eqB (opairB s v')
            (opairB (𝓜.D.child q.1) (𝓜.D.child q.2)) ⊓
          memB (opairB (𝓜.D.child q.1) (𝓜.D.child q.2)) G :=
      (inf_memB_le_iSup_matrix (hsub := huT.trans hsubG)
          (opairB s v')).trans' <|
        le_inf le_rfl huG
    refine (le_inf (le_inf le_rfl hdec) hdec').trans ?_
    rw [inf_iSup_eq (α := A)]
    refine iSup_le fun q => ?_
    rw [inf_right_comm, inf_iSup_eq (α := A)]
    refine iSup_le fun p => ?_
    let r :=
      u ⊓
        (eqB (opairB s v')
          (opairB (𝓜.D.child q.1) (𝓜.D.child q.2)) ⊓
          memB (opairB (𝓜.D.child q.1) (𝓜.D.child q.2)) G) ⊓
        (eqB (opairB s v)
          (opairB (𝓜.D.child p.1) (𝓜.D.child p.2)) ⊓
          memB (opairB (𝓜.D.child p.1) (𝓜.D.child p.2)) Fd)
    change r ≤ relB 𝓜.R v v'
    have hrU : r ≤ u := inf_le_left.trans inf_le_left
    have hrp : r ≤
        memB (opairB (𝓜.D.child p.1) (𝓜.D.child p.2)) Fd :=
      inf_le_right.trans inf_le_right
    have hrq : r ≤
        memB (opairB (𝓜.D.child q.1) (𝓜.D.child q.2)) G :=
      inf_le_left.trans (inf_le_right.trans inf_le_right)
    have hop : r ≤
        eqB (opairB s v)
          (opairB (𝓜.D.child p.1) (𝓜.D.child p.2)) :=
      inf_le_right.trans inf_le_left
    have hoq : r ≤
        eqB (opairB s v')
          (opairB (𝓜.D.child q.1) (𝓜.D.child q.2)) :=
      inf_le_left.trans (inf_le_right.trans inf_le_left)
    have hvp : r ≤ eqB v (𝓜.D.child p.2) := by
      rw [eqB_opairB] at hop
      exact hop.trans inf_le_right
    have hvq : r ≤ eqB v' (𝓜.D.child q.2) := by
      rw [eqB_opairB] at hoq
      exact hoq.trans inf_le_right
    have hsp : r ≤ eqB s (𝓜.D.child p.1) := by
      rw [eqB_opairB] at hop
      exact hop.trans inf_le_left
    have hsq : r ≤ eqB s (𝓜.D.child q.1) := by
      rw [eqB_opairB] at hoq
      exact hoq.trans inf_le_left
    have heq : r ≤ eqB (𝓜.D.child p.1) (𝓜.D.child q.1) :=
      (eqB_trans (𝓜.D.child p.1) s (𝓜.D.child q.1)).trans' <|
        le_inf (by rw [eqB_comm]; exact hsp) hsq
    have hGsame : r ≤
        memB (opairB (𝓜.D.child p.1) (𝓜.D.child q.2)) G :=
      (memB_opairB_congr G (𝓜.D.child q.1) (𝓜.D.child p.1)
          (𝓜.D.child q.2) (𝓜.D.child q.2)).trans' <|
        le_inf (le_inf
            (heq.trans_eq (eqB_comm (𝓜.D.child p.1) (𝓜.D.child q.1)))
            (le_top.trans (eqB_self (A := A) (𝓜.D.child q.2)).ge))
          hrq
    have hmts : r ≤
        mapsToSupB
          (interpDKBodyGraph 𝓜 V K hK hV
            (η.update hV 𝓜.total x p.1) y P)
          S (𝓜.D.child p.2) 𝓜.R :=
      (interpDKAbsFamily_inner_mapsToSup_outer 𝓜 V K hK hV η y x P a
          hOuter hInnerRows hOuterRows S d p.1 p.2).trans' <|
        le_inf (le_inf (le_inf (le_inf
            (hrU.trans (huT.trans htEq))
            (hrU.trans (huT.trans htA)))
          (hrU.trans (huT.trans htDir)))
          (hrU.trans (huT.trans htSup)))
          hrp
    have hub : r ≤
        isUpperBoundRelB (𝓜.D.child q.2)
          (graphImageB
            (interpDKBodyGraph 𝓜 V K hK hV
              (η.update hV 𝓜.total x p.1) y P)
            S 𝓜.D)
          𝓜.R := by
      refine le_iInf fun y₀ => ?_
      rw [le_himp_iff, memB_graphImageB]
      refine (le_inf inf_le_left (inf_le_right.trans inf_le_right)).trans ?_
      rw [inf_iSup_eq (α := A)]
      refine iSup_le fun z => ?_
      let sz :=
        r ⊓
          (memB z S ⊓
            memB (opairB z y₀)
              (interpDKBodyGraph 𝓜 V K hK hV
                (η.update hV 𝓜.total x p.1) y P))
      change sz ≤ relB 𝓜.R y₀ (𝓜.D.child q.2)
      have hszR : sz ≤ r := inf_le_left
      have hzS : sz ≤ memB z S := inf_le_right.trans inf_le_left
      have hzY : sz ≤
          memB (opairB z y₀)
            (interpDKBodyGraph 𝓜 V K hK hV
              (η.update hV 𝓜.total x p.1) y P) :=
        inf_le_right.trans inf_le_right
      have hzD : sz ≤ memB z 𝓜.D :=
        (memB_of_subsetB z S 𝓜.D).trans' <|
          le_inf hzS
            ((hszR.trans (hrU.trans (huT.trans htDir))).trans
              (isDirectedRelB_subset S 𝓜.D 𝓜.R))
      refine (le_inf le_rfl hzD).trans ?_
      rw [memB_eq (x := z) (y := 𝓜.D), inf_iSup_eq (α := A)]
      refine iSup_le fun k => ?_
      let sk :=
        sz ⊓ (eqB z (𝓜.D.child k) ⊓ 𝓜.D.val k)
      change sk ≤ relB 𝓜.R y₀ (𝓜.D.child q.2)
      have hskS : sk ≤ sz := inf_le_left
      have hzk : sk ≤ eqB z (𝓜.D.child k) :=
        inf_le_right.trans inf_le_left
      have hGe : sk ≤
          memB (opairB (𝓜.D.child k) y₀)
            (interpDKBodyGraph 𝓜 V K hK hV
              (η.update hV 𝓜.total x p.1) y P) :=
        (memB_opairB_congr
            (interpDKBodyGraph 𝓜 V K hK hV
              (η.update hV 𝓜.total x p.1) y P)
            z (𝓜.D.child k) y₀ y₀).trans' <|
          le_inf (le_inf hzk
              (le_top.trans (eqB_self (A := A) y₀).ge))
            (hskS.trans hzY)
      have hFk : sk ≤
          memB (opairB (𝓜.D.child p.1) y₀)
            (interpDKBodyGraph 𝓜 V K hK hV
              (η.update hV 𝓜.total y k) x P) :=
        (interpDKAbsFamily_outer_mem_le_inner 𝓜 V K hK hV η y x P a
            hInnerRows hOuter hOuterRows k p.1 y₀).trans' <|
          le_inf (le_inf
              (hskS.trans (hszR.trans (hrU.trans (huT.trans htEq))))
              (hskS.trans (hszR.trans (hrU.trans (huT.trans htA)))))
            hGe
      have hFkC : sk ≤
          memB (interpDKBodyGraph 𝓜 V K hK hV
              (η.update hV 𝓜.total y k) x P) 𝓜.C :=
        (hskS.trans (hszR.trans (hrU.trans (huT.trans htA)))).trans
          (interpDKAbsFamily_mem_mapSpace 𝓜 V K hK hV η y x P a
            hInner k)
      have hFkImg : sk ≤
          memB (interpDKBodyGraph 𝓜 V K hK hV
              (η.update hV 𝓜.total y k) x P) Img := by
        rw [memB_graphImageB]
        refine le_inf hFkC (le_iSup_of_le (𝓜.D.child k) ?_)
        refine le_inf ?_ ?_
        · exact (memB_eqB_left z S (𝓜.D.child k)).trans' <|
            le_inf (hskS.trans hzS) hzk
        · exact le_top.trans
            (memB_interpDKAbsFamilyGraph_child
              𝓜 V K hK hV η y x P k).ge
      have hQk : sk ≤
          relB 𝓜.Q
            (interpDKBodyGraph 𝓜 V K hK hV
              (η.update hV 𝓜.total y k) x P) G :=
        (isUpperBoundRelB_apply G Img 𝓜.Q
            (interpDKBodyGraph 𝓜 V K hK hV
              (η.update hV 𝓜.total y k) x P)).trans' <|
          le_inf (hskS.trans (hszR.trans (hrU.trans (huT.trans htUb))))
            hFkImg
      exact (𝓜.relQ_apply
          (interpDKBodyGraph 𝓜 V K hK hV
            (η.update hV 𝓜.total y k) x P)
          G (𝓜.D.child p.1) y₀ (𝓜.D.child q.2)).trans' <|
        le_inf (le_inf (le_inf hFkC
            (hskS.trans (hszR.trans (hrU.trans (huT.trans hGC)))))
          hQk)
          (le_inf (le_inf
              (le_top.trans (by
                rw [← oid_eps]
                exact (𝓜.total p.1).ge))
              hFk)
            (hskS.trans (hszR.trans hGsame)))
    have hfunGe : r ≤
        isFunctionB
          (interpDKBodyGraph 𝓜 V K hK hV
            (η.update hV 𝓜.total x p.1) y P)
          𝓜.D 𝓜.D :=
      (hrU.trans (huT.trans htA)).trans
        ((hOuter p.1).trans (inf_le_left.trans inf_le_left))
    have hisup : r ≤
        isSupRelB (𝓜.D.child p.2)
          (graphImageB
            (interpDKBodyGraph 𝓜 V K hK hV
              (η.update hV 𝓜.total x p.1) y P)
            S 𝓜.D)
          𝓜.R :=
      (mapsToSupB_le_isSup_graphImageB
          (interpDKBodyGraph 𝓜 V K hK hV
            (η.update hV 𝓜.total x p.1) y P)
          S 𝓜.D 𝓜.D 𝓜.R (𝓜.D.child p.2) hfunGe).trans' <|
        le_inf le_rfl hmts
    have hpq : r ≤ relB 𝓜.R (𝓜.D.child p.2) (𝓜.D.child q.2) :=
      (isSupRelB_least (𝓜.D.child p.2)
          (graphImageB
            (interpDKBodyGraph 𝓜 V K hK hV
              (η.update hV 𝓜.total x p.1) y P)
            S 𝓜.D)
          𝓜.R (𝓜.D.child q.2)).trans' <|
        le_inf hisup hub
    exact (relB_congr 𝓜.R (𝓜.D.child p.2) v (𝓜.D.child q.2) v').trans' <|
      le_inf (le_inf
          (hvp.trans_eq (eqB_comm v (𝓜.D.child p.2)))
          (hvq.trans_eq (eqB_comm v' (𝓜.D.child q.2))))
        hpq
  exact (𝓜.pointwise_le_relQ Fd G).trans' <|
    le_inf (le_inf hFC hGC) hpw

/-- A displayed inner graph is the `Q`-supremum of the family image. -/
theorem interpDKAbsFamily_image_isSupRelB
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
    (S : AName.{u} A) (d : 𝓜.D.idx) :
    ((oid V).eq x y)ᶜ ⊓ a ⊓
        isDirectedRelB S 𝓜.D 𝓜.R ⊓
        isSupRelB (𝓜.D.child d) S 𝓜.R ≤
      isSupRelB
        (interpDKBodyGraph 𝓜 V K hK hV (η.update hV 𝓜.total y d) x P)
        (graphImageB
          (interpDKAbsFamilyGraph 𝓜 V K hK hV η y x P) S 𝓜.C)
        𝓜.Q := by
  unfold isSupRelB
  refine le_inf ?_ ?_
  · refine le_iInf fun G => ?_
    rw [le_himp_iff]
    exact (interpDKAbsFamily_image_upper 𝓜 V K hK hV η y x P a
        hInner hOuter hInnerRows hOuterRows S d G).trans' <|
      le_inf (le_inf (le_inf
          (inf_le_left.trans (inf_le_left.trans
            (inf_le_left.trans inf_le_left)))
          (inf_le_left.trans (inf_le_left.trans
            (inf_le_left.trans inf_le_right))))
        (inf_le_left.trans (inf_le_right.trans inf_le_left)))
        inf_le_right
  · refine le_iInf fun G => ?_
    rw [le_himp_iff]
    exact interpDKAbsFamily_image_least 𝓜 V K hK hV η y x P a
      hInner hOuter hInnerRows hOuterRows S d G

/-- Directed-supremum preservation for the abs body graph, off the
diagonal. -/
theorem interpDKBodyGraph_abs_mapsToSup
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
    (S u v : AName.{u} A) :
    ((oid V).eq x y)ᶜ ⊓ a ⊓ lamDKVal V K (.abs x P) ⊓
        isDirectedRelB S 𝓜.D 𝓜.R ⊓ isSupRelB u S 𝓜.R ⊓
        memB (opairB u v)
          (interpDKBodyGraph 𝓜 V K hK hV η y (.abs x P)) ≤
      mapsToSupB
        (interpDKBodyGraph 𝓜 V K hK hV η y (.abs x P))
        S v 𝓜.R := by
  let Fabs := interpDKBodyGraph 𝓜 V K hK hV η y (.abs x P)
  let Fg := interpDKAbsFamilyGraph 𝓜 V K hK hV η y x P
  let b := a ⊓ lamDKVal V K (.abs x P)
  have hfun : b ≤ isFunctionB Fabs 𝓜.D 𝓜.D :=
    interpDKBodyGraph_abs_le_isFunctionB 𝓜 V K hK hV η y x P a
      hInner hInnerRows
  unfold mapsToSupB
  refine le_inf ?_ ?_
  · refine le_iInf fun w => le_iInf fun z => ?_
    rw [le_himp_iff]
    let t :=
      (((oid V).eq x y)ᶜ ⊓ a ⊓ lamDKVal V K (.abs x P) ⊓
        isDirectedRelB S 𝓜.D 𝓜.R ⊓ isSupRelB u S 𝓜.R ⊓
        memB (opairB u v) Fabs) ⊓
      (memB w S ⊓ memB (opairB w z) Fabs)
    change t ≤ relB 𝓜.R z v
    have htEq : t ≤ ((oid V).eq x y)ᶜ :=
      inf_le_left.trans (inf_le_left.trans (inf_le_left.trans
        (inf_le_left.trans (inf_le_left.trans inf_le_left))))
    have htA : t ≤ a :=
      inf_le_left.trans (inf_le_left.trans (inf_le_left.trans
        (inf_le_left.trans (inf_le_left.trans inf_le_right))))
    have htLam : t ≤ lamDKVal V K (.abs x P) :=
      inf_le_left.trans (inf_le_left.trans (inf_le_left.trans
        (inf_le_left.trans inf_le_right)))
    have htuv : t ≤ memB (opairB u v) Fabs :=
      inf_le_left.trans inf_le_right
    have htwS : t ≤ memB w S := inf_le_right.trans inf_le_left
    have htwz : t ≤ memB (opairB w z) Fabs :=
      inf_le_right.trans inf_le_right
    have htu : t ≤ isSupRelB u S 𝓜.R :=
      inf_le_left.trans (inf_le_left.trans inf_le_right)
    have hwu : t ≤ relB 𝓜.R w u :=
      (isUpperBoundRelB_apply u S 𝓜.R w).trans' <|
        le_inf (htu.trans inf_le_left) htwS
    exact (interpDKBodyGraph_abs_apply_mono 𝓜 V K hK hV η y x P a
        hInner hOuter hInnerRows hOuterRows w u z v).trans' <|
      le_inf (le_inf (le_inf (le_inf (le_inf
          htEq htA) htLam) htwz) htuv) hwu
  · refine le_iInf fun c => ?_
    rw [le_himp_iff]
    let upper :=
      ⨅ w : AName A, ⨅ z : AName A,
        memB w S ⊓ memB (opairB w z) Fabs ⇨ relB 𝓜.R z c
    let t :=
      (((oid V).eq x y)ᶜ ⊓ a ⊓ lamDKVal V K (.abs x P) ⊓
        isDirectedRelB S 𝓜.D 𝓜.R ⊓ isSupRelB u S 𝓜.R ⊓
        memB (opairB u v) Fabs) ⊓ upper
    change t ≤ relB 𝓜.R v c
    have htEq : t ≤ ((oid V).eq x y)ᶜ :=
      inf_le_left.trans (inf_le_left.trans (inf_le_left.trans
        (inf_le_left.trans (inf_le_left.trans inf_le_left))))
    have htA : t ≤ a :=
      inf_le_left.trans (inf_le_left.trans (inf_le_left.trans
        (inf_le_left.trans (inf_le_left.trans inf_le_right))))
    have htLam : t ≤ lamDKVal V K (.abs x P) :=
      inf_le_left.trans (inf_le_left.trans (inf_le_left.trans
        (inf_le_left.trans inf_le_right)))
    have htB : t ≤ b := le_inf htA htLam
    have htDir : t ≤ isDirectedRelB S 𝓜.D 𝓜.R :=
      inf_le_left.trans (inf_le_left.trans
        (inf_le_left.trans inf_le_right))
    have htSup : t ≤ isSupRelB u S 𝓜.R :=
      inf_le_left.trans (inf_le_left.trans inf_le_right)
    have htuv : t ≤ memB (opairB u v) Fabs :=
      inf_le_left.trans inf_le_right
    have htUpper : t ≤ upper := inf_le_right
    have hdec :
        t ≤ ⨆ p : 𝓜.D.idx × 𝓜.D.idx,
          eqB (opairB u v)
            (opairB (𝓜.D.child p.1) (𝓜.D.child p.2)) ⊓
          memB (opairB (𝓜.D.child p.1) (𝓜.D.child p.2)) Fabs :=
      (inf_memB_le_iSup_matrix (hsub := (htB.trans hfun).trans
          (inf_le_left.trans inf_le_left)) (opairB u v)).trans' <|
        le_inf le_rfl htuv
    refine (le_inf le_rfl hdec).trans ?_
    rw [inf_iSup_eq (α := A)]
    refine iSup_le fun p => ?_
    let s :=
      t ⊓
        (eqB (opairB u v)
          (opairB (𝓜.D.child p.1) (𝓜.D.child p.2)) ⊓
        memB (opairB (𝓜.D.child p.1) (𝓜.D.child p.2)) Fabs)
    change s ≤ relB 𝓜.R v c
    have hsT : s ≤ t := inf_le_left
    have hsp : s ≤
        memB (opairB (𝓜.D.child p.1) (𝓜.D.child p.2)) Fabs :=
      inf_le_right.trans inf_le_right
    have hop : s ≤
        eqB (opairB u v)
          (opairB (𝓜.D.child p.1) (𝓜.D.child p.2)) :=
      inf_le_right.trans inf_le_left
    have hup : s ≤ eqB u (𝓜.D.child p.1) := by
      rw [eqB_opairB] at hop
      exact hop.trans inf_le_left
    have hvp : s ≤ eqB v (𝓜.D.child p.2) := by
      rw [eqB_opairB] at hop
      exact hop.trans inf_le_right
    have hsupP : s ≤ isSupRelB (𝓜.D.child p.1) S 𝓜.R :=
      (isSupRelB_congr u (𝓜.D.child p.1) S 𝓜.R).trans' <|
        le_inf hup (hsT.trans htSup)
    have hFdSup : s ≤
        isSupRelB
          (interpDKBodyGraph 𝓜 V K hK hV
            (η.update hV 𝓜.total y p.1) x P)
          (graphImageB Fg S 𝓜.C) 𝓜.Q :=
      (interpDKAbsFamily_image_isSupRelB 𝓜 V K hK hV η y x P a
          hInner hOuter hInnerRows hOuterRows S p.1).trans' <|
        le_inf (le_inf (le_inf (hsT.trans htEq) (hsT.trans htA))
          (hsT.trans htDir)) hsupP
    have hImgDir : s ≤
        isDirectedRelB (graphImageB Fg S 𝓜.C) 𝓜.C 𝓜.Q :=
      (interpDKAbsFamilyGraph_image_directed 𝓜 V K hK hV η y x P a
          hInner hOuter hInnerRows hOuterRows S).trans' <|
        le_inf (le_inf (hsT.trans htEq) (hsT.trans htA))
          (hsT.trans htDir)
    have hmemLam : s ≤
        memB (opairB
          (interpDKBodyGraph 𝓜 V K hK hV
            (η.update hV 𝓜.total y p.1) x P)
          (𝓜.D.child p.2)) 𝓜.Lam :=
      (interpDKBodyGraph_abs_mem_eq_lam 𝓜 V K hK hV η y x P a
          hInner hInnerRows p.1 p.2).le.trans' (le_inf (hsT.trans htB) hsp)
        |>.trans inf_le_right
    have hLam : (⊤ : A) ≤
        isScottContinuousB 𝓜.Lam 𝓜.C 𝓜.D 𝓜.Q 𝓜.R :=
      le_top.trans 𝓜.lam_continuous.ge
    have hLamImg : s ≤
        isDirectedRelB
          (graphImageB 𝓜.Lam (graphImageB Fg S 𝓜.C) 𝓜.D)
          𝓜.D 𝓜.R ⊓
        isSupRelB (𝓜.D.child p.2)
          (graphImageB 𝓜.Lam (graphImageB Fg S 𝓜.C) 𝓜.D)
          𝓜.R :=
      (scottContinuous_image_sup (hF := hLam)
          𝓜.Lam (graphImageB Fg S 𝓜.C) 𝓜.C 𝓜.D 𝓜.Q 𝓜.R
          (interpDKBodyGraph 𝓜 V K hK hV
            (η.update hV 𝓜.total y p.1) x P)
          (𝓜.D.child p.2)).trans' <|
        le_inf (le_inf (le_inf (le_top.trans le_top) hImgDir)
          hFdSup) hmemLam
    have hcub : s ≤
        isUpperBoundRelB c
          (graphImageB 𝓜.Lam (graphImageB Fg S 𝓜.C) 𝓜.D)
          𝓜.R := by
      refine le_iInf fun z => ?_
      rw [le_himp_iff, memB_graphImageB]
      refine (le_inf le_rfl (inf_le_right.trans inf_le_right)).trans ?_
      rw [inf_iSup_eq (α := A)]
      refine iSup_le fun G => ?_
      refine (le_inf (inf_le_left.trans inf_le_left) inf_le_right).trans ?_
      let sz :=
        s ⊓ (memB G (graphImageB Fg S 𝓜.C) ⊓ memB (opairB G z) 𝓜.Lam)
      change sz ≤ relB 𝓜.R z c
      have hszS : sz ≤ s := inf_le_left
      have hGimg : sz ≤ memB G (graphImageB Fg S 𝓜.C) :=
        inf_le_right.trans inf_le_left
      have hGz : sz ≤ memB (opairB G z) 𝓜.Lam :=
        inf_le_right.trans inf_le_right
      rw [memB_graphImageB] at hGimg
      have hdecG : sz ≤ ⨆ w : AName A,
          memB w S ⊓ memB (opairB w G) Fg :=
        hGimg.trans inf_le_right
      refine (le_inf le_rfl hdecG).trans ?_
      rw [inf_iSup_eq (α := A)]
      refine iSup_le fun w => ?_
      let sw :=
        sz ⊓ (memB w S ⊓ memB (opairB w G) Fg)
      change sw ≤ relB 𝓜.R z c
      have hswS : sw ≤ s := inf_le_left.trans hszS
      have hwS : sw ≤ memB w S := inf_le_right.trans inf_le_left
      have hwG : sw ≤ memB (opairB w G) Fg :=
        inf_le_right.trans inf_le_right
      have hdecW :
          sw ≤ ⨆ k : 𝓜.D.idx,
            eqB w (𝓜.D.child k) ⊓
              eqB G
                (interpDKBodyGraph 𝓜 V K hK hV
                  (η.update hV 𝓜.total y k) x P) :=
        hwG.trans_eq
          (memB_interpDKAbsFamilyGraph 𝓜 V K hK hV η y x P w G)
      refine (le_inf le_rfl hdecW).trans ?_
      rw [inf_iSup_eq (α := A)]
      refine iSup_le fun k => ?_
      let sk :=
        sw ⊓
          (eqB w (𝓜.D.child k) ⊓
            eqB G
              (interpDKBodyGraph 𝓜 V K hK hV
                (η.update hV 𝓜.total y k) x P))
      change sk ≤ relB 𝓜.R z c
      have hskW : sk ≤ sw := inf_le_left
      have hwk : sk ≤ eqB w (𝓜.D.child k) :=
        inf_le_right.trans inf_le_left
      have hGk : sk ≤
          eqB G
            (interpDKBodyGraph 𝓜 V K hK hV
              (η.update hV 𝓜.total y k) x P) :=
        inf_le_right.trans inf_le_right
      have hLamk : sk ≤
          memB (opairB
            (interpDKBodyGraph 𝓜 V K hK hV
              (η.update hV 𝓜.total y k) x P)
            z) 𝓜.Lam :=
        (memB_opairB_congr 𝓜.Lam G
            (interpDKBodyGraph 𝓜 V K hK hV
              (η.update hV 𝓜.total y k) x P)
            z z).trans' <|
          le_inf (le_inf hGk
              (le_top.trans (eqB_self (A := A) z).ge))
            (hskW.trans (inf_le_left.trans hGz))
      have hsubLam : subsetB 𝓜.Lam (prodB 𝓜.C 𝓜.D) = ⊤ :=
        isFunctionB_subset 𝓜.lam_function
      have hdecZ :
          sk ≤ ⨆ p : 𝓜.C.idx × 𝓜.D.idx,
            eqB (opairB
                (interpDKBodyGraph 𝓜 V K hK hV
                  (η.update hV 𝓜.total y k) x P)
                z)
              (opairB (𝓜.C.child p.1) (𝓜.D.child p.2)) ⊓
            memB (opairB (𝓜.C.child p.1) (𝓜.D.child p.2)) 𝓜.Lam :=
        (inf_memB_le_iSup_matrix
            (hsub := le_top.trans hsubLam.ge)
            (opairB
              (interpDKBodyGraph 𝓜 V K hK hV
                (η.update hV 𝓜.total y k) x P)
              z)).trans' <|
          le_inf le_rfl hLamk
      refine (le_inf le_rfl hdecZ).trans ?_
      rw [inf_iSup_eq (α := A)]
      refine iSup_le fun p => ?_
      let sn :=
        sk ⊓
          (eqB (opairB
              (interpDKBodyGraph 𝓜 V K hK hV
                (η.update hV 𝓜.total y k) x P)
              z)
            (opairB (𝓜.C.child p.1) (𝓜.D.child p.2)) ⊓
          memB (opairB (𝓜.C.child p.1) (𝓜.D.child p.2)) 𝓜.Lam)
      change sn ≤ relB 𝓜.R z c
      have hsnK : sn ≤ sk := inf_le_left
      have hop : sn ≤
          eqB (opairB
              (interpDKBodyGraph 𝓜 V K hK hV
                (η.update hV 𝓜.total y k) x P)
              z)
            (opairB (𝓜.C.child p.1) (𝓜.D.child p.2)) :=
        inf_le_right.trans inf_le_left
      have hzn : sn ≤ eqB z (𝓜.D.child p.2) := by
        rw [eqB_opairB] at hop
        exact hop.trans inf_le_right
      have hLamn : sn ≤
          memB (opairB
            (interpDKBodyGraph 𝓜 V K hK hV
              (η.update hV 𝓜.total y k) x P)
            (𝓜.D.child p.2)) 𝓜.Lam :=
        (memB_opairB_congr 𝓜.Lam (𝓜.C.child p.1)
            (interpDKBodyGraph 𝓜 V K hK hV
              (η.update hV 𝓜.total y k) x P)
            (𝓜.D.child p.2) (𝓜.D.child p.2)).trans' <|
          le_inf (le_inf
              (by
                rw [eqB_opairB] at hop
                exact hop.trans inf_le_left |>.trans_eq
                  (eqB_comm
                    (interpDKBodyGraph 𝓜 V K hK hV
                      (η.update hV 𝓜.total y k) x P)
                    (𝓜.C.child p.1)))
              (le_top.trans (eqB_self (A := A) (𝓜.D.child p.2)).ge))
            (inf_le_right.trans inf_le_right)
      have hFabsn : sn ≤
          memB (opairB (𝓜.D.child k) (𝓜.D.child p.2)) Fabs := by
        have hmeet : sn ≤
            a ⊓ lamDKVal V K (.abs x P) ⊓
              memB (opairB
                (interpDKBodyGraph 𝓜 V K hK hV
                  (η.update hV 𝓜.total y k) x P)
                (𝓜.D.child p.2)) 𝓜.Lam :=
          le_inf (hsnK.trans (hskW.trans (hswS.trans (hsT.trans htB)))) hLamn
        exact ((interpDKBodyGraph_abs_mem_eq_lam 𝓜 V K hK hV η y x P a
            hInner hInnerRows k p.2).symm.le.trans' hmeet).trans
          inf_le_right
      have hFabsz : sn ≤ memB (opairB (𝓜.D.child k) z) Fabs :=
        (memB_opairB_congr Fabs (𝓜.D.child k) (𝓜.D.child k)
            (𝓜.D.child p.2) z).trans' <|
          le_inf (le_inf
              (le_top.trans (eqB_self (A := A) (𝓜.D.child k)).ge)
              (hzn.trans_eq (eqB_comm z (𝓜.D.child p.2))))
            hFabsn
      have hkS : sn ≤ memB (𝓜.D.child k) S :=
        (memB_eqB_left w S (𝓜.D.child k)).trans' <|
          le_inf (hsnK.trans (hskW.trans hwS))
            (hsnK.trans hwk)
      have hupper : sn ≤
          (memB (𝓜.D.child k) S ⊓
            memB (opairB (𝓜.D.child k) z) Fabs ⇨
              relB 𝓜.R z c) :=
        (iInf_le (fun z' : AName A =>
            memB (𝓜.D.child k) S ⊓
              memB (opairB (𝓜.D.child k) z') Fabs ⇨
                relB 𝓜.R z' c) z).trans' <|
          (iInf_le (fun w' : AName A =>
              ⨅ z' : AName A,
                memB w' S ⊓ memB (opairB w' z') Fabs ⇨
                  relB 𝓜.R z' c) (𝓜.D.child k)).trans'
            (hsnK.trans (hskW.trans (hswS.trans (hsT.trans htUpper))))
      exact (le_himp_iff.mp hupper).trans' <|
        le_inf le_rfl (le_inf hkS hFabsz)
    have hpc : s ≤ relB 𝓜.R (𝓜.D.child p.2) c :=
      (isSupRelB_least (𝓜.D.child p.2)
          (graphImageB 𝓜.Lam (graphImageB Fg S 𝓜.C) 𝓜.D)
          𝓜.R c).trans' <|
        le_inf (hLamImg.trans inf_le_right) hcub
    exact (relB_congr 𝓜.R (𝓜.D.child p.2) v c c).trans' <|
      le_inf (le_inf
          (hvp.trans_eq (eqB_comm v (𝓜.D.child p.2)))
          (le_top.trans (eqB_self (A := A) c).ge))
        hpc

/-- Off-diagonal Scott continuity of the abs body graph. -/
theorem interpDKBodyGraph_abs_le_scottContinuous_ne
    (𝓜 : InternalReflexiveModel (A := A))
    (V K : AName.{u} A) (hK : subsetB K 𝓜.D = ⊤)
    (hV : (oid V).IsTotal)
    (η : RelFun (oid V) (oid 𝓜.D))
    (y x : V.idx) (P : LamDK V.idx K.idx) (a : A)
    (hInner : ∀ d, a ≤ isScottContinuousB
      (interpDKBodyGraph 𝓜 V K hK hV (η.update hV 𝓜.total y d) x P)
      𝓜.D 𝓜.D 𝓜.R 𝓜.R)
    (hInnerRows : ∀ d, ∀ e, IsRelElementAt 𝓜.D a
      (interpDKRelVal 𝓜 V K hK hV
        ((η.update hV 𝓜.total y d).update hV 𝓜.total x e) P))
    (hOuter : ∀ z, a ≤ isScottContinuousB
      (interpDKBodyGraph 𝓜 V K hK hV (η.update hV 𝓜.total x z) y P)
      𝓜.D 𝓜.D 𝓜.R 𝓜.R)
    (hOuterRows : ∀ z, ∀ d, IsRelElementAt 𝓜.D a
      (interpDKRelVal 𝓜 V K hK hV
        ((η.update hV 𝓜.total x z).update hV 𝓜.total y d) P)) :
    ((oid V).eq x y)ᶜ ⊓ a ⊓ lamDKVal V K (.abs x P) ≤
      isScottContinuousB
        (interpDKBodyGraph 𝓜 V K hK hV η y (.abs x P))
        𝓜.D 𝓜.D 𝓜.R 𝓜.R := by
  unfold isScottContinuousB
  refine le_inf (le_inf ?_ ?_) ?_
  · exact (le_inf (inf_le_left.trans inf_le_right) inf_le_right).trans
      (interpDKBodyGraph_abs_le_isFunctionB 𝓜 V K hK hV η y x P a
        hInner hInnerRows)
  · refine le_iInf fun u => le_iInf fun u' =>
      le_iInf fun v => le_iInf fun v' => ?_
    rw [le_himp_iff]
    exact (interpDKBodyGraph_abs_apply_mono 𝓜 V K hK hV η y x P a
        hInner hOuter hInnerRows hOuterRows u u' v v').trans' <|
      le_inf (le_inf (le_inf inf_le_left
          (inf_le_right.trans (inf_le_left.trans inf_le_left)))
        (inf_le_right.trans (inf_le_left.trans inf_le_right)))
        (inf_le_right.trans inf_le_right)
  · refine le_iInf fun S => le_iInf fun u => le_iInf fun v => ?_
    rw [le_himp_iff]
    exact (interpDKBodyGraph_abs_mapsToSup 𝓜 V K hK hV η y x P a
        hInner hOuter hInnerRows hOuterRows S u v).trans' <|
      le_inf (le_inf (le_inf inf_le_left
          (inf_le_right.trans (inf_le_left.trans inf_le_left)))
        (inf_le_right.trans (inf_le_left.trans inf_le_right)))
        (inf_le_right.trans inf_le_right)

/-- Degree-local Scott continuity of an abstraction body graph. -/
theorem interpDKBodyGraph_abs_le_scottContinuous
    (𝓜 : InternalReflexiveModel (A := A))
    (V K : AName.{u} A) (hK : subsetB K 𝓜.D = ⊤)
    (hV : (oid V).IsTotal)
    (η : RelFun (oid V) (oid 𝓜.D))
    (y x : V.idx) (P : LamDK V.idx K.idx) (a : A)
    (hInner : ∀ d, a ≤ isScottContinuousB
      (interpDKBodyGraph 𝓜 V K hK hV (η.update hV 𝓜.total y d) x P)
      𝓜.D 𝓜.D 𝓜.R 𝓜.R)
    (hInnerRows : ∀ d, ∀ e, IsRelElementAt 𝓜.D a
      (interpDKRelVal 𝓜 V K hK hV
        ((η.update hV 𝓜.total y d).update hV 𝓜.total x e) P))
    (hOuter : ∀ z, a ≤ isScottContinuousB
      (interpDKBodyGraph 𝓜 V K hK hV (η.update hV 𝓜.total x z) y P)
      𝓜.D 𝓜.D 𝓜.R 𝓜.R)
    (hOuterRows : ∀ z, ∀ d, IsRelElementAt 𝓜.D a
      (interpDKRelVal 𝓜 V K hK hV
        ((η.update hV 𝓜.total x z).update hV 𝓜.total y d) P)) :
    a ⊓ memB (V.child x) V ⊓ lamDKVal V K P ≤
      isScottContinuousB
        (interpDKBodyGraph 𝓜 V K hK hV η y (.abs x P))
        𝓜.D 𝓜.D 𝓜.R 𝓜.R := by
  have hdeg : a ⊓ memB (V.child x) V ⊓ lamDKVal V K P =
      a ⊓ lamDKVal V K (.abs x P) :=
    inf_assoc a (memB (V.child x) V) (lamDKVal V K P)
  rw [hdeg]
  refine le_of_compl_cover (p := (oid V).eq x y) ?_ ?_
  · exact (interpDKBodyGraph_abs_le_scottContinuous_eq 𝓜 V K hK hV η y x P a
        hInner hInnerRows).trans' <|
      le_inf (le_inf inf_le_right (inf_le_left.trans inf_le_left))
        (inf_le_left.trans inf_le_right)
  · exact (interpDKBodyGraph_abs_le_scottContinuous_ne 𝓜 V K hK hV η y x P a
        hInner hInnerRows hOuter hOuterRows).trans' <|
      le_inf (le_inf inf_le_right (inf_le_left.trans inf_le_left))
        (inf_le_left.trans inf_le_right)

end Scott2026
