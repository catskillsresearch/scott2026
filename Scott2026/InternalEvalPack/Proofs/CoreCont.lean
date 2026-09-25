/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/

import Scott2026.InternalEvalComplete
import Scott2026.InternalEvalPack.InternalReflexiveModel.interpDKGraph
import Scott2026.InternalEvalPack.InternalReflexiveModel.interpDKName
import Scott2026.InternalEvalPack.InternalReflexiveModel.interpDKPureGraph
import Scott2026.InternalEvalPack.InternalReflexiveModel.interpDKPureRel
import Scott2026.InternalEvalPack.InternalReflexiveModel.interpDKRel
import Scott2026.InternalEvalPack.LamDK.weight
import Scott2026.InternalEvalPack.OidSeparated
import Scott2026.InternalEvalPack.asLam
import Scott2026.InternalEvalPack.asLamDK
import Scott2026.InternalEvalPack.Proofs.Core
import Scott2026.InternalEvalPack.Proofs.CorePost

namespace Scott2026

universe u


open AName

variable {A : Type u} [CompleteBooleanAlgebra A]

open InternalReflexiveModel

/-!
## Definition 25 graph clauses (continued)
-/

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
    · rw [ite_eq_right hyx]
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
      · rw [ite_eq_right hyx]
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
      · rw [ite_eq_left hyx]
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
      · rw [ite_eq_right hyx]
        by_cases hxP : x ∉ P.fv
        · rw [ite_eq_left hxP]
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
        · rw [ite_eq_right hxP]
          by_cases hyN : y ∉ N.fv
          · rw [ite_eq_left hyN]
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
          · rw [ite_eq_right hyN]
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

end Scott2026
