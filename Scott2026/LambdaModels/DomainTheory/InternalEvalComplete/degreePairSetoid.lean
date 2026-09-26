/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/

import Scott2026.LambdaModels.DomainTheory.InternalEvalFamily

universe u

namespace Scott2026

open AName
variable {A : Type u} [CompleteBooleanAlgebra A]

/-- Two-point setoid whose off-diagonal equality is the degree `a`. -/
def degreePairSetoid (a : A) : ASetoid (A := A) Bool where
  eq b1 b2 := if b1 = b2 then ⊤ else a
  symm := by
    intro b1 b2
    by_cases h : b1 = b2
    · simp [h]
    · simp [h, Ne.symm h]
  trans := by
    intro b1 b2 b3
    by_cases h12 : b1 = b2
    · by_cases h23 : b2 = b3
      · simp [h12, h23]
      · have h13 : b1 ≠ b3 := mt (fun h => h12.symm.trans h) h23
        simp [h12, h23]
    · by_cases h23 : b2 = b3
      · have h13 : b1 ≠ b3 := mt (fun h => h.trans h23.symm) h12
        simp [h23, h13]
      · by_cases h13 : b1 = b3
        · simp [h23, h13]
        · simp [h12, h23, h13]



end Scott2026
