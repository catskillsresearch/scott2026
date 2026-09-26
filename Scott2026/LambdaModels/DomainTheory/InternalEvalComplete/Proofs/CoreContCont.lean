/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/

import Scott2026.LambdaModels.DomainTheory.InternalEvalFamily
import Scott2026.LambdaModels.DomainTheory.InternalEvalComplete.InternalReflexiveModel.evalAtGraph
import Scott2026.LambdaModels.DomainTheory.InternalEvalComplete.InternalReflexiveModel.pointwiseSupGraph
import Scott2026.LambdaModels.DomainTheory.InternalEvalComplete.degreePairSetoid
import Scott2026.LambdaModels.DomainTheory.InternalEvalComplete.graphImageB
import Scott2026.LambdaModels.DomainTheory.InternalEvalComplete.interpDKAbsFamilyGraph
import Scott2026.LambdaModels.DomainTheory.InternalEvalComplete.zeroPairGraph
import Scott2026.LambdaModels.DomainTheory.InternalEvalComplete.Proofs.Core
import Scott2026.LambdaModels.DomainTheory.InternalEvalComplete.Proofs.CoreCont
import Scott2026.LambdaModels.DomainTheory.InternalEval.Proofs.CoreCont

namespace Scott2026

universe u


open AName InternalReflexiveModel

variable {A : Type u} [CompleteBooleanAlgebra A]

/-- A generalized element transports its coefficients along target equality. -/
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

end Scott2026
