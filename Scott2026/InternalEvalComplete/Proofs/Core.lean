/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/

import Scott2026.InternalEvalFamily
import Scott2026.InternalEvalComplete.InternalReflexiveModel.evalAtGraph
import Scott2026.InternalEvalComplete.InternalReflexiveModel.pointwiseSupGraph
import Scott2026.InternalEvalComplete.degreePairSetoid
import Scott2026.InternalEvalComplete.graphImageB
import Scott2026.InternalEvalComplete.interpDKAbsFamilyGraph
import Scott2026.InternalEvalComplete.zeroPairGraph
import Scott2026.InternalEval.InternalReflexiveModel.evalGraph
import Scott2026.InternalEval.InternalReflexiveModel.memMapSpaceLaws
import Scott2026.InternalEval.InternalReflexiveModel.validComponents
import Scott2026.InternalEval.infMemBOpairBLaws
import Scott2026.InternalEval.Proofs.CoreCont
import Scott2026.InternalEval.Proofs.Core

namespace Scott2026

universe u


open AName InternalReflexiveModel

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

/-- Membership in the canonical graph image (internal image of `S` under `F`). -/
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

/-- On displayed children the slice recovers the verified `evalGraph`. -/
theorem InternalReflexiveModel.evalAtGraph_val_eq_memB_evalGraph
    (𝓜 : InternalReflexiveModel (A := A))
    (c : 𝓜.C.idx) (x y : 𝓜.D.idx) :
    (evalAtGraph 𝓜 (𝓜.D.child x)).val (c, y) =
      memB
        (opairB
          (opairB (𝓜.C.child c) (𝓜.D.child x))
          (𝓜.D.child y))
        (evalGraph 𝓜) := by
  unfold evalAtGraph
  exact (memB_evalGraph_at 𝓜 c x y).symm

/-- Graph membership in the fixed-argument slice projects to evaluation. -/
theorem InternalReflexiveModel.memB_evalAtGraph_le
    (𝓜 : InternalReflexiveModel (A := A))
    (x F y : AName.{u} A) :
    memB (opairB F y) (evalAtGraph 𝓜 x) ≤
      memB F 𝓜.C ⊓ memB (opairB x y) F := by
  unfold evalAtGraph
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
    unfold evalAtGraph
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

/-- Graph membership in `pointwiseSupGraph` implies the semantic supremum. -/
theorem InternalReflexiveModel.memB_pointwiseSupGraph_le
    (𝓜 : InternalReflexiveModel (A := A))
    (S x y : AName.{u} A) :
    memB (opairB x y) (pointwiseSupGraph 𝓜 S) ≤
      memB x 𝓜.D ⊓ memB y 𝓜.D ⊓
        isSupRelB y (graphImageB (evalAtGraph 𝓜 x) S 𝓜.D) 𝓜.R := by
  unfold pointwiseSupGraph
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

end Scott2026
