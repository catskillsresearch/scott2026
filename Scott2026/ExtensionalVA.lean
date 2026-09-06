/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/

import Mathlib.SetTheory.ZFC.Basic
import Scott2026.Oid

/-!
# Extensional domains of Boolean-valued names

The paper defines an `A`-name as a partial function whose domain is a set of
names. `AName` uses an indexed presentation, so its raw index type can list
Boolean-equal children more than once. This module supplies the extensional
domain used by the paper-facing constructions: indices are identified exactly
when their children have Boolean equality `⊤`.

The recursive Boolean semantics remain those of `AName.memB` and `AName.eqB`.
For checked names, `check_atomic` identifies this quotient with extensional
equality of the corresponding `PSet` children.
-/

universe u

namespace Scott2026

open AName

variable {A : Type u} [CompleteBooleanAlgebra A]

/-- Equality of indices induced by Boolean equality of their child names. -/
def AName.domSetoid (X : AName.{u} A) : Setoid X.idx :=
  Setoid.comap X.child (nameSetoid (A := A))

/-- The extensional domain of an `A`-name. -/
def AName.Dom (X : AName.{u} A) : Type u :=
  Quotient X.domSetoid

/-- The class of a raw presentation index in the extensional domain. -/
def AName.domMk (X : AName.{u} A) (i : X.idx) : X.Dom :=
  Quotient.mk X.domSetoid i

/-- A chosen presentation index for an extensional-domain element. -/
noncomputable def AName.domOut (X : AName.{u} A) (i : X.Dom) : X.idx :=
  Quotient.out i

/-- A chosen child name representing an extensional-domain element. -/
noncomputable def AName.domChild (X : AName.{u} A) (i : X.Dom) : AName.{u} A :=
  X.child (X.domOut i)

/-- The semantic membership degree of an extensional-domain element. This is
the canonical extent `‖t ∈ X‖`, not the coefficient of the partial-function
presentation; see `fiberVal`. -/
noncomputable def AName.domVal (X : AName.{u} A) (i : X.Dom) : A :=
  memB (X.domChild i) X

/-- The coefficient of an extensional-domain key: the join of all raw
coefficients presenting that key. -/
noncomputable def AName.fiberVal (X : AName.{u} A) (i : X.Dom) : A :=
  ⨆ j : {j : X.idx // X.domMk j = i}, X.val j.1

/-- Collapse duplicate presentations of a name while joining their
coefficients. -/
noncomputable def AName.extensionalize (X : AName.{u} A) : AName.{u} A :=
  mk X.Dom X.domChild X.fiberVal

theorem AName.domMk_eq_iff (X : AName.{u} A) (i j : X.idx) :
    X.domMk i = X.domMk j ↔ eqB (X.child i) (X.child j) = ⊤ :=
  Quotient.eq

/-- A raw child and the chosen representative of its domain class are
Boolean-equal with value `⊤`. -/
theorem AName.eqB_child_domChild (X : AName.{u} A) (i : X.idx) :
    eqB (X.child i) (X.domChild (X.domMk i)) = ⊤ := by
  change X.domSetoid.r i (X.domOut (X.domMk i))
  apply Quotient.exact
  exact (Quotient.out_eq (X.domMk i)).symm

theorem AName.domVal_domMk (X : AName.{u} A) (i : X.idx) :
    X.domVal (X.domMk i) = memB (X.child i) X := by
  unfold domVal
  rw [eqB_top_memB_left (eqB_child_domChild X i)]

/-- Collapsing duplicate domain presentations and joining their coefficients
does not change Boolean membership. -/
theorem AName.memB_extensionalize (z X : AName.{u} A) :
    memB z X.extensionalize = memB z X := by
  rw [extensionalize, memB_mk, memB_eq]
  apply le_antisymm
  · refine iSup_le fun q => ?_
    rw [fiberVal, inf_iSup_eq]
    refine iSup_le fun j => ?_
    refine le_iSup_of_le j.1 ?_
    have hj : eqB (X.child j.1) (X.domChild q) = ⊤ := by
      have h := X.eqB_child_domChild j.1
      rwa [j.2] at h
    have hz : eqB z (X.domChild q) ≤ eqB z (X.child j.1) := by
      have h := eqB_trans z (X.domChild q) (X.child j.1)
      rw [eqB_comm (X.domChild q) (X.child j.1), hj, inf_top_eq] at h
      exact h
    exact inf_le_inf hz le_rfl
  · refine iSup_le fun j => ?_
    refine le_iSup_of_le (X.domMk j) ?_
    have hz : eqB z (X.child j) ≤ eqB z (X.domChild (X.domMk j)) := by
      have h := eqB_trans z (X.child j) (X.domChild (X.domMk j))
      rw [X.eqB_child_domChild j, inf_top_eq] at h
      exact h
    refine le_inf (inf_le_left.trans hz) ?_
    exact inf_le_right.trans
      (le_iSup (fun k : {k : X.idx // X.domMk k = X.domMk j} => X.val k.1) ⟨j, rfl⟩)

/-- The extensionalized presentation is Boolean-equal to the original name. -/
theorem AName.eqB_extensionalize (X : AName.{u} A) :
    eqB X X.extensionalize = ⊤ := by
  rw [eqB_eq_subset, subsetB_eq_iInf, subsetB_eq_iInf]
  apply inf_eq_top_iff.mpr
  constructor
  · exact iInf_eq_top.mpr fun z => by
      rw [memB_extensionalize z X, himp_self]
  · exact iInf_eq_top.mpr fun z => by
      rw [memB_extensionalize z X, himp_self]

/-- The domain class of an element in a checked pre-set. -/
noncomputable def AName.checkDomMk (X : PSet.{u}) (i : X.Type) :
    (check (A := A) X).Dom :=
  match X with
  | .mk α f => (check (A := A) (PSet.mk α f)).domMk i

/-- The quotient presentation of the elements of a ground pre-set. -/
def psetElemSetoid (X : PSet.{u}) : Setoid X.Type :=
  Setoid.comap X.Func PSet.setoid

/-- The extensional elements of a ground pre-set. -/
def PSetElem (X : PSet.{u}) : Type u :=
  Quotient (psetElemSetoid X)

/-- `dom(check X)` is the extensional quotient of the elements of `X`. -/
noncomputable def AName.checkDomEquiv [Nontrivial A] (X : PSet.{u}) :
    (check (A := A) X).Dom ≃ PSetElem X :=
  match X with
  | .mk α f =>
    { toFun := Quotient.map id fun i j h => by
        change eqB (check (A := A) (f i)) (check (f j)) = ⊤ at h
        exact (check_atomic (A := A) (f i) (f j)).1.mp h
      invFun := Quotient.map id fun i j h => by
        change PSet.Equiv (f i) (f j) at h
        exact (check_atomic (A := A) (f i) (f j)).1.mpr h
      left_inv := by
        intro i
        induction i using Quotient.inductionOn
        rfl
      right_inv := by
        intro i
        induction i using Quotient.inductionOn
        rfl }

/-- Every coefficient of the extensional presentation of a checked name is
`⊤`. -/
theorem AName.fiberVal_check (X : PSet.{u})
    (i : (check (A := A) X).Dom) :
    (check (A := A) X).fiberVal i = ⊤ := by
  cases X with
  | mk α f =>
    apply top_unique
    let j : {j : (check (A := A) (PSet.mk α f)).idx //
        (check (A := A) (PSet.mk α f)).domMk j = i} :=
      ⟨(check (A := A) (PSet.mk α f)).domOut i, Quotient.out_eq i⟩
    refine le_iSup_of_le j ?_
    exact le_rfl

/-- A checked name whose raw keys have already been quotiented by extensional
`PSet` equality. -/
noncomputable def checkExt (X : PSet.{u}) : AName.{u} A :=
  mk (PSetElem X)
    (fun i => check (A := A) (X.Func (Quotient.out i)))
    (fun _ => ⊤)

/-- Quotienting the keys of a checked name does not change membership. -/
theorem memB_checkExt (z : AName.{u} A) (X : PSet.{u}) [Nontrivial A] :
    memB z (checkExt (A := A) X) = memB z (check (A := A) X) := by
  cases X with
  | mk α f =>
    rw [checkExt, check_mk, memB_mk, memB_mk]
    apply le_antisymm
    · refine iSup_le fun q => ?_
      exact le_iSup_of_le (Quotient.out q) le_rfl
    · refine iSup_le fun i => ?_
      let q : PSetElem (PSet.mk α f) :=
        Quotient.mk (psetElemSetoid (PSet.mk α f)) i
      refine le_iSup_of_le q ?_
      rw [inf_top_eq, inf_top_eq]
      have hout : PSet.Equiv (f (Quotient.out q)) (f i) := by
        exact Quotient.exact (Quotient.out_eq q)
      have heq :
          eqB (check (A := A) (f i))
            (check (A := A) (f (Quotient.out q))) = ⊤ :=
        (check_atomic (A := A) _ _).1.mpr hout.symm
      exact (eqB_trans z (check (A := A) (f i))
        (check (A := A) (f (Quotient.out q)))).trans'
          (le_inf le_rfl (le_top.trans heq.ge))

/-- The extensional checked presentation denotes the ordinary checked name. -/
theorem eqB_check_checkExt (X : PSet.{u}) [Nontrivial A] :
    eqB (check (A := A) X) (checkExt (A := A) X) = ⊤ := by
  rw [eqB_eq_iInf]
  refine iInf_eq_top.mpr fun z => inf_eq_top_iff.mpr ⟨?_, ?_⟩
  · rw [memB_checkExt, himp_self]
  · rw [memB_checkExt, himp_self]

/-- `checkExt` depends only on the extensional ZFC set represented by a
pre-set, not on the chosen pre-set presentation. -/
theorem eqB_checkExt_congr {X Y : PSet.{u}} [Nontrivial A]
    (h : PSet.Equiv X Y) :
    eqB (checkExt (A := A) X) (checkExt (A := A) Y) = ⊤ := by
  have hX : eqB (checkExt (A := A) X) (check (A := A) X) = ⊤ := by
    rw [eqB_comm]
    exact eqB_check_checkExt X
  have hXY : eqB (check (A := A) X) (check (A := A) Y) = ⊤ :=
    (check_atomic (A := A) X Y).1.mpr h
  have hY : eqB (check (A := A) Y) (checkExt (A := A) Y) = ⊤ :=
    eqB_check_checkExt Y
  have hXY' :
      eqB (checkExt (A := A) X) (check (A := A) Y) = ⊤ := by
    apply top_unique
    exact (le_inf hX.ge hXY.ge).trans (eqB_trans _ _ _)
  apply top_unique
  exact (le_inf hXY'.ge hY.ge).trans (eqB_trans _ _ _)

/-- Paper-facing check embedding from Mathlib's extensional ZFC universe.
The use of `out` is hidden behind `eqB_checkZF_mk`, so no theorem can observe
which pre-set representative was chosen. -/
noncomputable def checkZF (X : ZFSet.{u}) : AName.{u} A :=
  checkExt (A := A) X.out

/-- A small, extensional type of variables/elements for a paper-facing ZFC
set. Unlike `PSet.Type`, this carrier has no duplicate presentations. -/
abbrev ZFSetElem (X : ZFSet.{u}) : Type u :=
  (checkZF (A := A) X).idx

/-- The checked name attached to a paper-facing ZFC set has exactly its
extensional small element carrier as domain. -/
theorem checkZF_idx (X : ZFSet.{u}) :
    (checkZF (A := A) X).idx = ZFSetElem (A := A) X :=
  rfl

/-- Checking a quotient class agrees, at Boolean equality `⊤`, with checking
any pre-set representative of that class. -/
theorem eqB_checkZF_mk (X : PSet.{u}) [Nontrivial A] :
    eqB (checkZF (A := A) (ZFSet.mk X)) (checkExt (A := A) X) = ⊤ := by
  apply eqB_checkExt_congr
  apply ZFSet.eq.mp
  exact (ZFSet.mk_out (ZFSet.mk X)).trans (ZFSet.mk_eq X).symm

/-- The paper-facing check embedding is definitionally congruent for equality
in the extensional ZFC universe. -/
theorem checkZF_congr {X Y : ZFSet.{u}} (h : X = Y) :
    checkZF (A := A) X = checkZF (A := A) Y :=
  congrArg (checkZF (A := A)) h

/-- Extensional equality of parameters is preserved by `powerB`. -/
theorem eqB_powerB_congr {X Y : AName.{u} A} (h : eqB X Y = ⊤) :
    eqB (powerB X) (powerB Y) = ⊤ := by
  rw [eqB_eq_iInf]
  refine iInf_eq_top.mpr fun z => ?_
  have hs : subsetB z X = subsetB z Y := by
    rw [subsetB_eq_iInf, subsetB_eq_iInf]
    exact iInf_congr fun u =>
      congrArg (fun t => memB u z ⇨ t) (eqB_top_memB_right (z := u) h)
  apply inf_eq_top_iff.mpr
  constructor
  · rw [memB_powerB, memB_powerB, hs, himp_self]
  · rw [memB_powerB, memB_powerB, hs, himp_self]

/-- Distinct keys of `checkExt X` have Boolean equality `⊥`. -/
theorem eqB_checkExt_child (X : PSet.{u}) [Nontrivial A]
    (i j : (checkExt (A := A) X).idx) :
    (i = j →
      eqB ((checkExt (A := A) X).child i)
        ((checkExt (A := A) X).child j) = ⊤) ∧
    (i ≠ j →
      eqB ((checkExt (A := A) X).child i)
        ((checkExt (A := A) X).child j) = ⊥) := by
  constructor
  · intro hij
    subst j
    exact eqB_self _
  · intro hij
    apply (check_atomic (A := A) _ _).2.1.mpr
    intro hequiv
    apply hij
    have hout :
        Quotient.mk (psetElemSetoid X) (Quotient.out i) =
          Quotient.mk (psetElemSetoid X) (Quotient.out j) :=
      Quotient.sound hequiv
    exact (Quotient.out_eq i).symm.trans (hout.trans (Quotient.out_eq j))

/-- Membership in a name over the discrete keys of `checkExt X` is pointwise
evaluation. -/
theorem memB_child_mk_checkExt (X : PSet.{u}) [Nontrivial A]
    (v : (checkExt (A := A) X).idx → A)
    (i : (checkExt (A := A) X).idx) :
    memB ((checkExt (A := A) X).child i)
      (mk (checkExt (A := A) X).idx (checkExt (A := A) X).child v) = v i := by
  classical
  rw [memB_mk]
  apply le_antisymm
  · refine iSup_le fun j => ?_
    by_cases hij : i = j
    · subst j
      rw [(eqB_checkExt_child (A := A) X i i).1 rfl, top_inf_eq]
    · rw [(eqB_checkExt_child (A := A) X i j).2 hij, bot_inf_eq]
      exact bot_le
  · exact le_iSup_of_le i (by rw [eqB_self, top_inf_eq])

/-- Membership in a subset of `checkExt X` is pointwise evaluation. -/
theorem memB_child_powerB_checkExt (X : PSet.{u}) [Nontrivial A]
    (v : (powerB (checkExt (A := A) X)).idx)
    (i : (checkExt (A := A) X).idx) :
    memB ((checkExt (A := A) X).child i)
      ((powerB (checkExt (A := A) X)).child v) = v.1 i := by
  change memB ((checkExt (A := A) X).child i)
    (mk (checkExt (A := A) X).idx (checkExt (A := A) X).child v.1) = v.1 i
  exact memB_child_mk_checkExt X v.1 i

/-- The raw `powerB` construction is strict when its checked base has
extensional keys. This is the paper's strictness argument without duplicate
`PSet` presentations. -/
theorem oid_powerB_checkExt_isStrict (X : PSet.{u}) [Nontrivial A] :
    (oid (powerB (checkExt (A := A) X))).IsStrict := by
  classical
  intro v w h
  rw [oid_eq_powerB] at h
  apply Subtype.ext
  funext i
  apply le_antisymm
  · have hsub : subsetB
        ((powerB (checkExt (A := A) X)).child v)
        ((powerB (checkExt (A := A) X)).child w) = ⊤ :=
      top_unique (h.ge.trans (eqB_le_subsetB _ _))
    change subsetB
      (mk (checkExt (A := A) X).idx (checkExt (A := A) X).child v.1)
      (mk (checkExt (A := A) X).idx (checkExt (A := A) X).child w.1) = ⊤ at hsub
    rw [subsetB_mk] at hsub
    have hi := iInf_eq_top.mp hsub i
    rw [himp_eq_top_iff, memB_child_mk_checkExt X w.1 i] at hi
    exact hi
  · have heq : eqB
        ((powerB (checkExt (A := A) X)).child w)
        ((powerB (checkExt (A := A) X)).child v) = ⊤ := by
      rwa [eqB_comm]
    have hsub : subsetB
        ((powerB (checkExt (A := A) X)).child w)
        ((powerB (checkExt (A := A) X)).child v) = ⊤ :=
      top_unique (heq.ge.trans (eqB_le_subsetB _ _))
    change subsetB
      (mk (checkExt (A := A) X).idx (checkExt (A := A) X).child w.1)
      (mk (checkExt (A := A) X).idx (checkExt (A := A) X).child v.1) = ⊤ at hsub
    rw [subsetB_mk] at hsub
    have hi := iInf_eq_top.mp hsub i
    rw [himp_eq_top_iff, memB_child_mk_checkExt X v.1 i] at hi
    exact hi

/-- Extensional valuations bounded by the partial-function coefficients of
`X`. These are the functions that form the paper-facing `P^A(X)`. -/
def ExtensionalPowerIdx (X : AName.{u} A) : Type u :=
  {v : X.Dom → A // ∀ i, v i ≤ X.fiberVal i}

/-- The name represented by an extensional bounded valuation. -/
noncomputable def extensionalPowerName (X : AName.{u} A)
    (v : ExtensionalPowerIdx X) : AName.{u} A :=
  mk X.Dom X.domChild v.1

/-- A representative of an element of `dom(check X)` is itself a checked
ground set. -/
theorem AName.exists_eq_check_domChild (X : PSet.{u})
    (i : (check (A := A) X).Dom) :
    ∃ x : PSet.{u}, (check (A := A) X).domChild i = check (A := A) x := by
  cases X with
  | mk α f =>
    exact ⟨f ((check (A := A) (PSet.mk α f)).domOut i), rfl⟩

/-- Checked ground-set elements are Boolean-discrete after quotienting the
presentation domain by equality at `⊤`. -/
theorem AName.eqB_check_domChild (X : PSet.{u}) [Nontrivial A]
    (i j : (check (A := A) X).Dom) :
    (i = j →
      eqB ((check (A := A) X).domChild i) ((check (A := A) X).domChild j) = ⊤) ∧
    (i ≠ j →
      eqB ((check (A := A) X).domChild i) ((check (A := A) X).domChild j) = ⊥) := by
  classical
  obtain ⟨x, hx⟩ := AName.exists_eq_check_domChild (A := A) X i
  obtain ⟨y, hy⟩ := AName.exists_eq_check_domChild (A := A) X j
  constructor
  · intro hij
    subst j
    rw [eqB_self]
  · intro hij
    rw [hx, hy]
    apply (check_atomic (A := A) _ _).2.1.mpr
    intro hequiv
    apply hij
    have hrel : (check (A := A) X).domSetoid.r
        (Quotient.out i) (Quotient.out j) := by
      change eqB ((check (A := A) X).domChild i)
        ((check (A := A) X).domChild j) = ⊤
      rw [hx, hy]
      exact (check_atomic (A := A) x y).1.mpr hequiv
    have hout :
        Quotient.mk (check (A := A) X).domSetoid (Quotient.out i) =
          Quotient.mk (check (A := A) X).domSetoid (Quotient.out j) :=
      Quotient.sound hrel
    exact (Quotient.out_eq i).symm.trans (hout.trans (Quotient.out_eq j))

/-- Membership in an extensional subset of a checked set is evaluation of its
valuation. This is the calculation used in the paper's strictness proof. -/
theorem memB_domChild_extensionalPowerName_check (X : PSet.{u}) [Nontrivial A]
    (v : ExtensionalPowerIdx (check (A := A) X))
    (i : (check (A := A) X).Dom) :
    memB ((check (A := A) X).domChild i)
      (extensionalPowerName (check (A := A) X) v) = v.1 i := by
  classical
  rw [extensionalPowerName, memB_mk]
  refine le_antisymm (iSup_le fun j => ?_) ?_
  · by_cases hij : i = j
    · subst j
      rw [(AName.eqB_check_domChild X i i).1 rfl, top_inf_eq]
    · rw [(AName.eqB_check_domChild X i j).2 hij, bot_inf_eq]
      exact bot_le
  · exact le_iSup_of_le i (by rw [eqB_self, top_inf_eq])

/-- The paper-facing setoid of `P^A(X)` on extensional bounded valuations. -/
noncomputable def extensionalPowerSetoid (X : AName.{u} A) :
    ASetoid (A := A) (ExtensionalPowerIdx X) where
  eq v w := eqB (extensionalPowerName X v) (extensionalPowerName X w)
  symm v w := eqB_comm _ _
  trans v w z := eqB_trans _ _ _

/-- Proposition 28 strictness calculation on the paper's extensional
presentation of `P^A(check X)`. -/
theorem extensionalPowerSetoid_check_isStrict (X : PSet.{u}) [Nontrivial A] :
    (extensionalPowerSetoid (check (A := A) X)).IsStrict := by
  classical
  intro v w h
  apply Subtype.ext
  funext i
  apply le_antisymm
  · have hsub : subsetB
        (extensionalPowerName (check (A := A) X) v)
        (extensionalPowerName (check (A := A) X) w) = ⊤ := by
      exact top_unique (h.ge.trans (eqB_le_subsetB _ _))
    rw [extensionalPowerName, subsetB_mk] at hsub
    have hi := iInf_eq_top.mp hsub i
    rw [himp_eq_top_iff,
      memB_domChild_extensionalPowerName_check X w i] at hi
    exact hi
  · have heq : eqB
        (extensionalPowerName (check (A := A) X) w)
        (extensionalPowerName (check (A := A) X) v) = ⊤ := by
      rwa [eqB_comm]
    have hsub : subsetB
        (extensionalPowerName (check (A := A) X) w)
        (extensionalPowerName (check (A := A) X) v) = ⊤ :=
      top_unique (heq.ge.trans (eqB_le_subsetB _ _))
    rw [extensionalPowerName, subsetB_mk] at hsub
    have hi := iInf_eq_top.mp hsub i
    rw [himp_eq_top_iff,
      memB_domChild_extensionalPowerName_check X v i] at hi
    exact hi

end Scott2026
