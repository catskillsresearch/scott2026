/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/

import Mathlib.Order.CompleteBooleanAlgebra

/-!
# Boolean-valued propositional and first-order connectives

Furber–Mardare–Panangaden–Scott, CSL 2026, §2: a complete Boolean algebra `A`
interprets the connectives of propositional logic; completeness interprets
`∀` as a meet and `∃` as a join. Validity means Boolean value `⊤`.
-/

namespace Scott2026

variable {A : Type*} [CompleteBooleanAlgebra A]

/-- A statement with Boolean value `a` is *valid* when `a = ⊤`. -/
def IsValid (a : A) : Prop := a = ⊤

@[simp] theorem isValid_top : IsValid (⊤ : A) := rfl

theorem isValid_inf {a b : A} (ha : IsValid a) (hb : IsValid b) : IsValid (a ⊓ b) := by
  unfold IsValid at ha hb ⊢
  rw [ha, hb, top_inf_eq]

theorem valid_of_le_valid {a b : A} (h : a ≤ b) (ha : IsValid a) : IsValid b := by
  unfold IsValid at ha ⊢
  exact top_unique (ha ▸ h)

/-- Existential quantification as a join (paper §2). -/
def bExists {ι : Sort*} (f : ι → A) : A := ⨆ i, f i

/-- Universal quantification as a meet (paper §2). -/
def bForall {ι : Sort*} (f : ι → A) : A := ⨅ i, f i

theorem bExists_le_iff {ι : Sort*} {f : ι → A} {a : A} :
    bExists f ≤ a ↔ ∀ i, f i ≤ a := iSup_le_iff

theorem le_bForall_iff {ι : Sort*} {f : ι → A} {a : A} :
    a ≤ bForall f ↔ ∀ i, a ≤ f i := le_iInf_iff

/-- Mixing / “maximum principle” shape used in Theorem 1 (iii) and Definition 4. -/
def Compatible {ι : Sort*} (eq : ι → ι → A) (a : ι → A) : Prop :=
  ∀ i j, a i ⊓ a j ≤ eq i j

end Scott2026
