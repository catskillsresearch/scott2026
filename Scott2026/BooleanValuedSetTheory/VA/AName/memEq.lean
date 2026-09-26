/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/

import Mathlib.Order.CompleteBooleanAlgebra
import Scott2026.BooleanValuedSetTheory.VA.AName
import Scott2026.BooleanValuedSetTheory.VA.AName.child
import Scott2026.BooleanValuedSetTheory.VA.AName.meas
import Scott2026.BooleanValuedSetTheory.VA.AName.measLt
import Scott2026.BooleanValuedSetTheory.VA.AName.rank
import Scott2026.BooleanValuedSetTheory.VA.AName.val

namespace Scott2026

namespace AName

variable {A : Type u}

theorem measLt_of_rank_left {x x' y : AName.{u} A} (h : rank x' < rank x) :
    measLt (meas x' y) (meas x y) := by
  dsimp [measLt, meas]
  rcases lt_or_eq_of_le (sup_le_sup_right h.le (rank y)) with hlt | heq
  · exact Prod.Lex.left _ _ hlt
  · rw [heq]
    exact Prod.Lex.right _ (Prod.Lex.left _ _ h)

theorem measLt_of_rank_right {x y y' : AName.{u} A} (h : rank y' < rank y) :
    measLt (meas x y') (meas x y) := by
  dsimp [measLt, meas]
  rcases lt_or_ge (rank x) (rank y) with hxy | hyx
  · have : rank x ⊔ rank y' < rank x ⊔ rank y := by
      rw [sup_eq_right.mpr hxy.le]
      exact max_lt hxy h
    exact Prod.Lex.left _ _ this
  · have hmeq : rank x ⊔ rank y' = rank x ⊔ rank y := by
      rw [sup_eq_left.mpr hyx, sup_eq_left.mpr (h.le.trans hyx)]
    rw [hmeq]
    exact Prod.Lex.right _ (Prod.Lex.right _ h)

/-- From `eqB x y`, one recursive call is `memB (child y) x` (arguments swapped). -/
theorem measLt_of_rank_swap {x y y' : AName.{u} A} (h : rank y' < rank y) :
    measLt (meas y' x) (meas x y) := by
  dsimp [measLt, meas]
  rcases lt_or_ge (rank x) (rank y) with hxy | hyx
  · have : rank y' ⊔ rank x < rank x ⊔ rank y := by
      rw [sup_comm (rank x), sup_eq_left.mpr hxy.le]
      exact max_lt h hxy
    exact Prod.Lex.left _ _ this
  · have hmeq : rank y' ⊔ rank x = rank x ⊔ rank y := by
      rw [sup_eq_right.mpr (h.le.trans hyx), sup_eq_left.mpr hyx]
    rw [hmeq]
    exact Prod.Lex.right _ (Prod.Lex.left _ _ (h.trans_le hyx))

mutual
  noncomputable def memB [CompleteBooleanAlgebra A] : AName.{u} A → AName.{u} A → A
    | x, mk _ g b => ⨆ j, eqB x (g j) ⊓ b j
  termination_by x y => meas x y
  decreasing_by
    exact measLt_of_rank_right (rank_child_lt (mk _ g b) j)

  noncomputable def eqB [CompleteBooleanAlgebra A] : AName.{u} A → AName.{u} A → A
    | mk _ f a, mk _ g b =>
        (⨅ i, a i ⇨ memB (f i) (mk _ g b)) ⊓ (⨅ j, b j ⇨ memB (g j) (mk _ f a))
  termination_by x y => meas x y
  decreasing_by
    · exact measLt_of_rank_left (rank_child_lt (mk _ f a) i)
    · exact measLt_of_rank_swap (rank_child_lt (mk _ g b) j)
end

variable [CompleteBooleanAlgebra A]

noncomputable def subsetB (x y : AName.{u} A) : A :=
  ⨅ i : x.idx, x.val i ⇨ memB (x.child i) y

end AName

end Scott2026
