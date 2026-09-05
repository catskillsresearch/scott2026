/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/

import Scott2026.Setoid

/-!
# Relational and functional maps of `A`-setoids (Definitions 8–10, 13)
-/

namespace Scott2026

variable {A : Type*} [CompleteBooleanAlgebra A] {X Y : Type*}

/-- Definition 8: a relation that is single-valued and total in the `A`-valued sense. -/
structure RelFun (S : ASetoid (A := A) X) (T : ASetoid (A := A) Y) where
  val : X → Y → A
  respects : ∀ x₁ x₂ y₁ y₂,
    S.eq x₁ x₂ ⊓ T.eq y₁ y₂ ≤
      himp (val x₁ y₁) (val x₂ y₂) ⊓ himp (val x₂ y₂) (val x₁ y₁)
  le_eps : ∀ x y, val x y ≤ S.eps x ⊓ T.eps y
  single_valued : ∀ x y₁ y₂, val x y₁ ⊓ val x y₂ ≤ T.eq y₁ y₂
  total : ∀ x, S.eps x ≤ ⨆ y, val x y

/-- Definition 10: graph of a functional map, `γ(f)(x,y) = ε(x) ⊓ ‖f(x) = y‖`. -/
def gamma (S : ASetoid (A := A) X) (T : ASetoid (A := A) Y) (f : X → Y) (x : X) (y : Y) : A :=
  S.eps x ⊓ T.eq (f x) y

/-- Definition 9: `X ⊸ Y` is the set of equality-preserving maps. -/
def functionalMaps (S : ASetoid (A := A) X) (T : ASetoid (A := A) Y) : Set (X → Y) :=
  {f | APoset.Functional S T f}

/-- Definition 9: `A`-valued equality of functional maps. -/
def functionalEq (S : ASetoid (A := A) X) (T : ASetoid (A := A) Y) (f₁ f₂ : X → Y) : A :=
  ⨅ x, himp (S.eps x) (T.eq (f₁ x) (f₂ x))

/-- Definition 8: identity relational function `id(x,y) = ‖x = y‖`. -/
def RelFun.id (S : ASetoid (A := A) X) : RelFun S S where
  val := S.eq
  respects := fun x₁ x₂ y₁ y₂ => by
    refine le_inf ?fwd ?bwd
    · rw [le_himp_iff]
      calc
        S.eq x₁ x₂ ⊓ S.eq y₁ y₂ ⊓ S.eq x₁ y₁
          = S.eq x₂ x₁ ⊓ S.eq y₁ y₂ ⊓ S.eq x₁ y₁ := by rw [S.symm x₁ x₂]
        _ = S.eq x₂ x₁ ⊓ (S.eq y₁ y₂ ⊓ S.eq x₁ y₁) := inf_assoc _ _ _
        _ = S.eq x₂ x₁ ⊓ (S.eq x₁ y₁ ⊓ S.eq y₁ y₂) := by rw [inf_comm (S.eq y₁ y₂)]
        _ = (S.eq x₂ x₁ ⊓ S.eq x₁ y₁) ⊓ S.eq y₁ y₂ := (inf_assoc _ _ _).symm
        _ ≤ S.eq x₂ y₁ ⊓ S.eq y₁ y₂ := inf_le_inf (S.trans x₂ x₁ y₁) le_rfl
        _ ≤ S.eq x₂ y₂ := S.trans x₂ y₁ y₂
    · rw [le_himp_iff]
      calc
        S.eq x₁ x₂ ⊓ S.eq y₁ y₂ ⊓ S.eq x₂ y₂
          = S.eq x₁ x₂ ⊓ (S.eq y₁ y₂ ⊓ S.eq x₂ y₂) := inf_assoc _ _ _
        _ = S.eq x₁ x₂ ⊓ (S.eq y₂ y₁ ⊓ S.eq x₂ y₂) := by rw [S.symm y₁ y₂]
        _ = S.eq x₁ x₂ ⊓ (S.eq x₂ y₂ ⊓ S.eq y₂ y₁) := by
            rw [inf_comm (S.eq y₂ y₁), S.symm x₂ y₂]
        _ = (S.eq x₁ x₂ ⊓ S.eq x₂ y₂) ⊓ S.eq y₂ y₁ := (inf_assoc _ _ _).symm
        _ ≤ S.eq x₁ y₂ ⊓ S.eq y₂ y₁ := inf_le_inf (S.trans x₁ x₂ y₂) le_rfl
        _ ≤ S.eq x₁ y₁ := S.trans x₁ y₂ y₁
  le_eps := fun x y => le_inf (S.eq_le_eps_left x y) (S.eq_le_eps_right x y)
  single_valued := fun x y₁ y₂ => by
    calc
      S.eq x y₁ ⊓ S.eq x y₂ = S.eq y₁ x ⊓ S.eq x y₂ := by rw [S.symm x y₁]
      _ ≤ S.eq y₁ y₂ := S.trans y₁ x y₂
  total := fun x => le_trans (le_rfl : S.eps x ≤ S.eq x x) (le_iSup (S.eq x) x)

/-- A functional map satisfies `ε(x) ≤ ε(f(x))`. -/
theorem functional_eps_le {S : ASetoid (A := A) X} {T : ASetoid (A := A) Y}
    {f : X → Y} (hf : APoset.Functional S T f) (x : X) :
    S.eps x ≤ T.eps (f x) :=
  hf x x

/-- Definition 10: the graph of a functional map is a relational function. -/
def RelFun.ofFunctional (S : ASetoid (A := A) X) (T : ASetoid (A := A) Y)
    (f : X → Y) (hf : APoset.Functional S T f) : RelFun S T where
  val := gamma S T f
  respects := fun x₁ x₂ y₁ y₂ => by
    unfold gamma
    refine le_inf ?fwd ?bwd
    · rw [le_himp_iff]
      refine le_inf ?eps₁ ?eq₁
      · exact (S.eq_le_eps_right x₁ x₂).trans' (inf_le_left.trans inf_le_left)
      · have h₁ : S.eq x₁ x₂ ⊓ T.eq (f x₁) y₁ ≤ T.eq (f x₂) y₁ := by
          have step : T.eq (f x₂) (f x₁) ⊓ T.eq (f x₁) y₁ ≤ T.eq (f x₂) y₁ :=
            T.trans (f x₂) (f x₁) y₁
          have hsymm : S.eq x₁ x₂ ≤ T.eq (f x₂) (f x₁) := by
            rw [T.symm]; exact hf x₁ x₂
          exact (inf_le_inf hsymm le_rfl).trans step
        have : S.eq x₁ x₂ ⊓ T.eq y₁ y₂ ⊓ (S.eps x₁ ⊓ T.eq (f x₁) y₁)
            ≤ T.eq (f x₂) y₂ := by
          calc
            S.eq x₁ x₂ ⊓ T.eq y₁ y₂ ⊓ (S.eps x₁ ⊓ T.eq (f x₁) y₁)
              ≤ S.eq x₁ x₂ ⊓ T.eq y₁ y₂ ⊓ T.eq (f x₁) y₁ :=
                inf_le_inf le_rfl inf_le_right
            _ = (S.eq x₁ x₂ ⊓ T.eq (f x₁) y₁) ⊓ T.eq y₁ y₂ := by
                rw [inf_right_comm, inf_assoc]
            _ ≤ T.eq (f x₂) y₁ ⊓ T.eq y₁ y₂ := inf_le_inf h₁ le_rfl
            _ ≤ T.eq (f x₂) y₂ := T.trans (f x₂) y₁ y₂
        exact this
    · rw [le_himp_iff]
      refine le_inf ?eps₂ ?eq₂
      · exact (S.eq_le_eps_left x₁ x₂).trans' (inf_le_left.trans inf_le_left)
      · have h₁ : S.eq x₁ x₂ ⊓ T.eq (f x₂) y₂ ≤ T.eq (f x₁) y₂ := by
          have step : T.eq (f x₁) (f x₂) ⊓ T.eq (f x₂) y₂ ≤ T.eq (f x₁) y₂ :=
            T.trans (f x₁) (f x₂) y₂
          exact (inf_le_inf (hf x₁ x₂) le_rfl).trans step
        calc
          S.eq x₁ x₂ ⊓ T.eq y₁ y₂ ⊓ (S.eps x₂ ⊓ T.eq (f x₂) y₂)
            ≤ S.eq x₁ x₂ ⊓ T.eq y₁ y₂ ⊓ T.eq (f x₂) y₂ :=
              inf_le_inf le_rfl inf_le_right
          _ = (S.eq x₁ x₂ ⊓ T.eq (f x₂) y₂) ⊓ T.eq y₁ y₂ := by
              rw [inf_right_comm, inf_assoc]
          _ ≤ T.eq (f x₁) y₂ ⊓ T.eq y₁ y₂ := inf_le_inf h₁ le_rfl
          _ ≤ T.eq (f x₁) y₁ := by
              have step : T.eq (f x₁) y₂ ⊓ T.eq y₂ y₁ ≤ T.eq (f x₁) y₁ :=
                T.trans (f x₁) y₂ y₁
              rw [T.symm y₁ y₂]; exact step
  le_eps := fun x y => by
    unfold gamma
    exact le_inf inf_le_left ((T.eq_le_eps_right (f x) y).trans' inf_le_right)
  single_valued := fun x y₁ y₂ => by
    unfold gamma
    calc
      (S.eps x ⊓ T.eq (f x) y₁) ⊓ (S.eps x ⊓ T.eq (f x) y₂)
        ≤ T.eq (f x) y₁ ⊓ T.eq (f x) y₂ := inf_le_inf inf_le_right inf_le_right
      _ = T.eq y₁ (f x) ⊓ T.eq (f x) y₂ := by rw [T.symm (f x) y₁]
      _ ≤ T.eq y₁ y₂ := T.trans y₁ (f x) y₂
  total := fun x => by
    unfold gamma
    have hε : S.eps x ≤ T.eps (f x) := functional_eps_le hf x
    have : S.eps x ≤ S.eps x ⊓ T.eq (f x) (f x) :=
      le_inf le_rfl (by simpa [ASetoid.eps] using hε)
    exact this.trans (le_iSup (fun y => S.eps x ⊓ T.eq (f x) y) (f x))

end Scott2026
