/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/

import Scott2026.InternalInterp
import Scott2026.InternalReflexiveModel
import Scott2026.LambdaConstVA
import Scott2026.ReflexiveVA
import Scott2026.InternalEval.InternalReflexiveModel.memMapSpaceLaws
import Scott2026.InternalEval.infMemBOpairBLaws

universe u

namespace Scott2026

open AName
variable {A : Type u} [CompleteBooleanAlgebra A]
namespace InternalReflexiveModel

noncomputable def evalRel
    (𝓜 : InternalReflexiveModel (A := A)) :
    RelFun ((oid 𝓜.C).prod (oid 𝓜.D)) (oid 𝓜.D) where
  val p y :=
    memB (𝓜.C.child p.1) 𝓜.C ⊓
      memB (opairB (𝓜.D.child p.2) (𝓜.D.child y)) (𝓜.C.child p.1)
  respects := by
    intro p₁ p₂ y₁ y₂
    refine le_inf ?_ ?_ <;> rw [le_himp_iff]
    · let t :=
        ((oid 𝓜.C).prod (oid 𝓜.D)).eq p₁ p₂ ⊓
          (oid 𝓜.D).eq y₁ y₂ ⊓
            (memB (𝓜.C.child p₁.1) 𝓜.C ⊓
              memB (opairB (𝓜.D.child p₁.2) (𝓜.D.child y₁))
                (𝓜.C.child p₁.1))
      change t ≤ _
      have hs : t ≤ ((oid 𝓜.C).prod (oid 𝓜.D)).eq p₁ p₂ := by
        dsimp [t]
        exact inf_le_left.trans inf_le_left
      have ht : t ≤ (oid 𝓜.D).eq y₁ y₂ := by
        dsimp [t]
        exact inf_le_left.trans inf_le_right
      have hv0 : t ≤ memB (𝓜.C.child p₁.1) 𝓜.C ⊓
          memB (opairB (𝓜.D.child p₁.2) (𝓜.D.child y₁))
            (𝓜.C.child p₁.1) := by
        dsimp [t]
        exact inf_le_right
      have hC₂ : t ≤ memB (𝓜.C.child p₂.1) 𝓜.C := by
        have h := hs.trans
          (((oid 𝓜.C).prod (oid 𝓜.D)).eq_le_eps_right p₁ p₂)
        change t ≤ (oid 𝓜.C).eps p₂.1 ⊓ (oid 𝓜.D).eps p₂.2 at h
        rw [oid_eps] at h
        exact h.trans inf_le_left
      have hFF : t ≤ eqB (𝓜.C.child p₁.1) (𝓜.C.child p₂.1) := by
        have h : ((oid 𝓜.C).prod (oid 𝓜.D)).eq p₁ p₂ ≤
            (oid 𝓜.C).eq p₁.1 p₂.1 := by
          rw [ASetoid.prod_eq]
          exact inf_le_left
        exact hs.trans h |>.trans (by rw [oid_eq]; exact inf_le_right)
      have hxx : t ≤ eqB (𝓜.D.child p₁.2) (𝓜.D.child p₂.2) := by
        have h : ((oid 𝓜.C).prod (oid 𝓜.D)).eq p₁ p₂ ≤
            (oid 𝓜.D).eq p₁.2 p₂.2 := by
          rw [ASetoid.prod_eq]
          exact inf_le_right
        exact hs.trans h |>.trans (by rw [oid_eq]; exact inf_le_right)
      have hyy : t ≤ eqB (𝓜.D.child y₁) (𝓜.D.child y₂) := by
        exact ht.trans (by rw [oid_eq]; exact inf_le_right)
      have hv : t ≤ memB
          (opairB (𝓜.D.child p₁.2) (𝓜.D.child y₁))
          (𝓜.C.child p₁.1) := by
        exact hv0.trans inf_le_right
      refine le_inf hC₂ ?_
      refine (memB_eqB_right (𝓜.C.child p₁.1)
        (opairB (𝓜.D.child p₂.2) (𝓜.D.child y₂))
        (𝓜.C.child p₂.1)).trans' (le_inf ?_ hFF)
      exact (memB_opairB_congr (𝓜.C.child p₁.1)
        (𝓜.D.child p₁.2) (𝓜.D.child p₂.2)
        (𝓜.D.child y₁) (𝓜.D.child y₂)).trans'
          (le_inf (le_inf hxx hyy) hv)
    · let t :=
        ((oid 𝓜.C).prod (oid 𝓜.D)).eq p₁ p₂ ⊓
          (oid 𝓜.D).eq y₁ y₂ ⊓
            (memB (𝓜.C.child p₂.1) 𝓜.C ⊓
              memB (opairB (𝓜.D.child p₂.2) (𝓜.D.child y₂))
                (𝓜.C.child p₂.1))
      change t ≤ _
      have hs : t ≤ ((oid 𝓜.C).prod (oid 𝓜.D)).eq p₁ p₂ := by
        dsimp [t]
        exact inf_le_left.trans inf_le_left
      have ht : t ≤ (oid 𝓜.D).eq y₁ y₂ := by
        dsimp [t]
        exact inf_le_left.trans inf_le_right
      have hv0 : t ≤ memB (𝓜.C.child p₂.1) 𝓜.C ⊓
          memB (opairB (𝓜.D.child p₂.2) (𝓜.D.child y₂))
            (𝓜.C.child p₂.1) := by
        dsimp [t]
        exact inf_le_right
      have hC₁ : t ≤ memB (𝓜.C.child p₁.1) 𝓜.C := by
        have h := hs.trans
          (((oid 𝓜.C).prod (oid 𝓜.D)).eq_le_eps_left p₁ p₂)
        change t ≤ (oid 𝓜.C).eps p₁.1 ⊓ (oid 𝓜.D).eps p₁.2 at h
        rw [oid_eps] at h
        exact h.trans inf_le_left
      have hFF : t ≤ eqB (𝓜.C.child p₂.1) (𝓜.C.child p₁.1) := by
        have h : ((oid 𝓜.C).prod (oid 𝓜.D)).eq p₁ p₂ ≤
            (oid 𝓜.C).eq p₁.1 p₂.1 := by
          rw [ASetoid.prod_eq]
          exact inf_le_left
        have h' := hs.trans h
        rw [(oid 𝓜.C).symm p₁.1 p₂.1, oid_eq] at h'
        exact h'.trans inf_le_right
      have hxx : t ≤ eqB (𝓜.D.child p₂.2) (𝓜.D.child p₁.2) := by
        have h : ((oid 𝓜.C).prod (oid 𝓜.D)).eq p₁ p₂ ≤
            (oid 𝓜.D).eq p₁.2 p₂.2 := by
          rw [ASetoid.prod_eq]
          exact inf_le_right
        have h' := hs.trans h
        rw [(oid 𝓜.D).symm p₁.2 p₂.2, oid_eq] at h'
        exact h'.trans inf_le_right
      have hyy : t ≤ eqB (𝓜.D.child y₂) (𝓜.D.child y₁) := by
        have h := ht
        rw [(oid 𝓜.D).symm y₁ y₂, oid_eq] at h
        exact h.trans inf_le_right
      have hv : t ≤ memB
          (opairB (𝓜.D.child p₂.2) (𝓜.D.child y₂))
          (𝓜.C.child p₂.1) := by
        exact hv0.trans inf_le_right
      refine le_inf hC₁ ?_
      refine (memB_eqB_right (𝓜.C.child p₂.1)
        (opairB (𝓜.D.child p₁.2) (𝓜.D.child y₁))
        (𝓜.C.child p₁.1)).trans' (le_inf ?_ hFF)
      exact (memB_opairB_congr (𝓜.C.child p₂.1)
        (𝓜.D.child p₂.2) (𝓜.D.child p₁.2)
        (𝓜.D.child y₂) (𝓜.D.child y₁)).trans'
          (le_inf (le_inf hxx hyy) hv)
  le_eps := by
    intro p y
    change (memB (𝓜.C.child p.1) 𝓜.C ⊓
      memB (opairB (𝓜.D.child p.2) (𝓜.D.child y))
        (𝓜.C.child p.1)) ≤
      ((oid 𝓜.C).eps p.1 ⊓ (oid 𝓜.D).eps p.2) ⊓
        (oid 𝓜.D).eps y
    have hfun := 𝓜.mem_mapSpace_le_function (𝓜.C.child p.1)
    have hmem : memB (𝓜.C.child p.1) 𝓜.C ⊓
        memB (opairB (𝓜.D.child p.2) (𝓜.D.child y))
          (𝓜.C.child p.1) ≤
        memB (𝓜.D.child p.2) 𝓜.D ⊓
          memB (𝓜.D.child y) 𝓜.D := by
      have hsub : memB (𝓜.C.child p.1) 𝓜.C ≤
          subsetB (𝓜.C.child p.1) (prodB 𝓜.D 𝓜.D) :=
        hfun.trans (inf_le_left.trans inf_le_left)
      have hm := (memB_of_subsetB
        (opairB (𝓜.D.child p.2) (𝓜.D.child y))
        (𝓜.C.child p.1) (prodB 𝓜.D 𝓜.D)).trans' <|
          le_inf inf_le_right (inf_le_left.trans hsub)
      rwa [memB_opairB_prodB] at hm
    rw [oid_eps, oid_eps, oid_eps]
    exact le_inf
      (le_inf inf_le_left (hmem.trans inf_le_left))
      (hmem.trans inf_le_right)
  single_valued := by
    intro p y₁ y₂
    have hfun := 𝓜.mem_mapSpace_le_function (𝓜.C.child p.1)
    have hsv := isSingleValuedB_apply (𝓜.C.child p.1)
      (𝓜.D.child p.2) (𝓜.D.child y₁) (𝓜.D.child y₂)
    have hsupport (y : 𝓜.D.idx) :
        memB (𝓜.C.child p.1) 𝓜.C ⊓
            memB (opairB (𝓜.D.child p.2) (𝓜.D.child y))
              (𝓜.C.child p.1) ≤
          memB (𝓜.D.child p.2) 𝓜.D ⊓ memB (𝓜.D.child y) 𝓜.D := by
      have hsub : memB (𝓜.C.child p.1) 𝓜.C ≤
          subsetB (𝓜.C.child p.1) (prodB 𝓜.D 𝓜.D) :=
        hfun.trans (inf_le_left.trans inf_le_left)
      have hm := (memB_of_subsetB
        (opairB (𝓜.D.child p.2) (𝓜.D.child y))
        (𝓜.C.child p.1) (prodB 𝓜.D 𝓜.D)).trans' <|
          le_inf inf_le_right (inf_le_left.trans hsub)
      rwa [memB_opairB_prodB] at hm
    change _ ≤ (oid 𝓜.D).eq y₁ y₂
    rw [oid_eq]
    refine le_inf (le_inf ?_ ?_) ?_
    · exact inf_le_left.trans (hsupport y₁) |>.trans inf_le_right
    · exact inf_le_right.trans (hsupport y₂) |>.trans inf_le_right
    · exact hsv.trans' <| le_inf
        (le_inf
          (inf_le_left.trans inf_le_left |>.trans hfun |>.trans
            (inf_le_left.trans inf_le_right))
          (inf_le_left.trans inf_le_right))
        (inf_le_right.trans inf_le_right)
  total := by
    intro p
    change (oid 𝓜.C).eps p.1 ⊓ (oid 𝓜.D).eps p.2 ≤
      ⨆ y, memB (𝓜.C.child p.1) 𝓜.C ⊓
        memB (opairB (𝓜.D.child p.2) (𝓜.D.child y))
          (𝓜.C.child p.1)
    rw [oid_eps, oid_eps]
    have hfun := 𝓜.mem_mapSpace_le_function (𝓜.C.child p.1)
    have htotal := isTotalB_apply (𝓜.C.child p.1) 𝓜.D
      (𝓜.D.child p.2)
    have hgraph : memB (𝓜.C.child p.1) 𝓜.C ⊓
        memB (𝓜.D.child p.2) 𝓜.D ≤
        ⨆ y, memB (opairB (𝓜.D.child p.2) (𝓜.D.child y))
          (𝓜.C.child p.1) := by
      have hall := htotal.trans' (le_inf
        (inf_le_left.trans hfun |>.trans
          inf_le_right)
        inf_le_right)
      refine (le_inf inf_le_left hall).trans ?_
      rw [inf_iSup_eq]
      refine iSup_le fun y => ?_
      exact (inf_memB_opairB_le_iSup_child
        (hfun.trans (inf_le_left.trans inf_le_left))
        (𝓜.D.child p.2) y)
    refine (le_inf inf_le_left hgraph).trans ?_
    rw [inf_iSup_eq]


end InternalReflexiveModel

end Scott2026
