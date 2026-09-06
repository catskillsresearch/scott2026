/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/

import Mathlib.SetTheory.ZFC.Basic
import Scott2026.Setoid
import Scott2026.VA

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

/-- The semantic membership degree of an extensional-domain element. -/
noncomputable def AName.domVal (X : AName.{u} A) (i : X.Dom) : A :=
  memB (X.domChild i) X

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

/-- Extensional valuations bounded by the membership degrees of `X`. These are
the partial functions that form the paper's `P^A(X)`. -/
def ExtensionalPowerIdx (X : AName.{u} A) : Type u :=
  {v : X.Dom → A // ∀ i, v i ≤ X.domVal i}

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
