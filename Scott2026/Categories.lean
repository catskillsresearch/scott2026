/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/

import Mathlib.CategoryTheory.Category.Basic
import Scott2026.RelFun

/-!
# Categories of Boolean-valued setoids

This module bundles the object types suppressed in Definitions 8 and 9 and
installs the category structures using Mathlib's category library.
-/

universe u

namespace Scott2026

open CategoryTheory

variable (A : Type u) [CompleteBooleanAlgebra A]

/-- A bundled `A`-setoid, used as an object of `SetoidR_A`. -/
structure SetoidRObj where
  carrier : Type u
  setoid : ASetoid (A := A) carrier

namespace SetoidRObj

instance : CoeSort (SetoidRObj A) (Type u) :=
  ⟨SetoidRObj.carrier⟩

instance : CategoryStruct (SetoidRObj A) where
  Hom X Y := RelFun X.setoid Y.setoid
  id X := RelFun.id X.setoid
  comp f g := g.comp f

instance : Category (SetoidRObj A) where
  id_comp f := RelFun.comp_id f
  comp_id f := RelFun.id_comp f
  assoc f g h := (RelFun.comp_assoc h g f).symm

@[simp] theorem id_val (X : SetoidRObj A) (x y : X) :
    (𝟙 X : X ⟶ X).val x y = X.setoid.eq x y :=
  rfl

@[simp] theorem comp_val {X Y Z : SetoidRObj A}
    (f : X ⟶ Y) (g : Y ⟶ Z) (x : X) (z : Z) :
    (f ≫ g).val x z = ⨆ y : Y, f.val x y ⊓ g.val y z :=
  rfl

end SetoidRObj

/-- A separately bundled `A`-setoid, used as an object of `SetoidF_A`. -/
structure SetoidFObj where
  carrier : Type u
  setoid : ASetoid (A := A) carrier

namespace SetoidFObj

instance : CoeSort (SetoidFObj A) (Type u) :=
  ⟨SetoidFObj.carrier⟩

instance : CategoryStruct (SetoidFObj A) where
  Hom X Y := SetoidFHom X.setoid Y.setoid
  id X := SetoidFHom.id X.setoid
  comp f g := SetoidFHom.comp g f

theorem id_comp_hom {X Y : SetoidFObj A} (f : X ⟶ Y) :
    SetoidFHom.comp f (SetoidFHom.id X.setoid) = f := by
  induction f using Quotient.inductionOn with
  | _ f =>
    apply Quotient.sound
    intro x
    exact functional_eps_le f.2 x

theorem comp_id_hom {X Y : SetoidFObj A} (f : X ⟶ Y) :
    SetoidFHom.comp (SetoidFHom.id Y.setoid) f = f := by
  induction f using Quotient.inductionOn with
  | _ f =>
    apply Quotient.sound
    intro x
    exact functional_eps_le f.2 x

theorem assoc_hom {W X Y Z : SetoidFObj A}
    (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z) :
    SetoidFHom.comp h (SetoidFHom.comp g f) =
      SetoidFHom.comp (SetoidFHom.comp h g) f := by
  induction f using Quotient.inductionOn with
  | _ f =>
    induction g using Quotient.inductionOn with
    | _ g =>
      induction h using Quotient.inductionOn with
      | _ h =>
        apply Quotient.sound
        intro x
        exact functional_eps_le
          (APoset.Functional.comp f.2
            (APoset.Functional.comp g.2 h.2)) x

instance : Category (SetoidFObj A) where
  id_comp := id_comp_hom (A := A)
  comp_id := comp_id_hom (A := A)
  assoc := assoc_hom (A := A)

end SetoidFObj

end Scott2026
