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
import Scott2026.LambdaModels.DomainTheory.InternalEval.Proofs.CoreCont

namespace Scott2026

universe u


open AName InternalReflexiveModel

variable {A : Type u} [CompleteBooleanAlgebra A]

/-- A generalized element transports its coefficients along target equality. -/
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
  unfold pointwiseSupGraph
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
  unfold pointwiseSupGraph
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
  unfold pointwiseSupGraph
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

end Scott2026
