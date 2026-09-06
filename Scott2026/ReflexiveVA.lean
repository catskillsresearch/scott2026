/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/

import Scott2026.InternalDomain

/-!
# Definition 19 inside `V^A`

These are the Boolean values of the order-theoretic clauses in Definition 19.
Functions are represented by their internal graphs. The function-space name
`C` is required extensionally to contain exactly the Scott-continuous
self-maps of `D`, and its order is required to be the pointwise order.
-/

universe u

namespace Scott2026

open AName

variable {A : Type u} [CompleteBooleanAlgebra A]

/-- Evaluation of an internal binary relation. -/
noncomputable def relB (R x y : AName.{u} A) : A :=
  memB (opairB x y) R

/-- `x` is an upper bound of `S` for the relation `R`. -/
noncomputable def isUpperBoundRelB
    (x S R : AName.{u} A) : A :=
  ⨅ y : AName.{u} A, memB y S ⇨ relB R y x

/-- `x` is the least upper bound of `S` for `R`. -/
noncomputable def isSupRelB
    (x S R : AName.{u} A) : A :=
  isUpperBoundRelB x S R ⊓
    ⨅ y : AName.{u} A,
      isUpperBoundRelB y S R ⇨ relB R x y

/-- `S` is a nonempty directed subset of `D` for `R`. -/
noncomputable def isDirectedRelB
    (S D R : AName.{u} A) : A :=
  subsetB S D ⊓
    (⨆ x : AName.{u} A, memB x S) ⊓
    ⨅ x : AName.{u} A, ⨅ y : AName.{u} A,
      memB x S ⊓ memB y S ⇨
        ⨆ z : AName.{u} A,
          memB z S ⊓ relB R x z ⊓ relB R y z

/-- `R` is a partial order on the internal set `D`. -/
noncomputable def isPartialOrderB
    (D R : AName.{u} A) : A :=
  subsetB R (prodB D D) ⊓
    (⨅ x : AName.{u} A, memB x D ⇨ relB R x x) ⊓
    (⨅ x : AName.{u} A, ⨅ y : AName.{u} A,
      memB x D ⊓ memB y D ⊓ relB R x y ⊓ relB R y x ⇨ eqB x y) ⊓
    ⨅ x : AName.{u} A, ⨅ y : AName.{u} A, ⨅ z : AName.{u} A,
      relB R x y ⊓ relB R y z ⇨ relB R x z

/-- `D` is a dcpo with bottom under `R`. -/
noncomputable def isDcpoWithBottomB
    (D R : AName.{u} A) : A :=
  isPartialOrderB D R ⊓
    (⨆ b : AName.{u} A,
      memB b D ⊓
        ⨅ x : AName.{u} A, memB x D ⇨ relB R b x) ⊓
    ⨅ S : AName.{u} A,
      isDirectedRelB S D R ⇨
        ⨆ d : AName.{u} A, memB d D ⊓ isSupRelB d S R

/-- The output values of `F` on `S` have least upper bound `y`. -/
noncomputable def mapsToSupB
    (F S y R : AName.{u} A) : A :=
  (⨅ x : AName.{u} A, ⨅ z : AName.{u} A,
      memB x S ⊓ memB (opairB x z) F ⇨ relB R z y) ⊓
    ⨅ u : AName.{u} A,
      (⨅ x : AName.{u} A, ⨅ z : AName.{u} A,
        memB x S ⊓ memB (opairB x z) F ⇨ relB R z u) ⇨
          relB R y u

/-- `F : D → E` is Scott-continuous for the internal orders `R` and `Q`. -/
noncomputable def isScottContinuousB
    (F D E R Q : AName.{u} A) : A :=
  isFunctionB F D E ⊓
    (⨅ x : AName.{u} A, ⨅ x' : AName.{u} A,
      ⨅ y : AName.{u} A, ⨅ y' : AName.{u} A,
        memB (opairB x y) F ⊓ memB (opairB x' y') F ⊓ relB R x x' ⇨
          relB Q y y') ⊓
    ⨅ S : AName.{u} A, ⨅ x : AName.{u} A, ⨅ y : AName.{u} A,
      isDirectedRelB S D R ⊓ isSupRelB x S R ⊓
          memB (opairB x y) F ⇨
        mapsToSupB F S y Q

/-- Boolean value saying that `C` contains exactly the Scott-continuous
internal self-maps of `D`. -/
noncomputable def isContinuousMapSpaceB
    (C D R : AName.{u} A) : A :=
  subsetB C (funsB D D) ⊓
    ⨅ F : AName.{u} A,
      (memB F C ⇨ isScottContinuousB F D D R R) ⊓
        (isScottContinuousB F D D R R ⇨ memB F C)

/-- Pointwise order of internal functions. -/
noncomputable def pointwiseLeB
    (F G D R : AName.{u} A) : A :=
  ⨅ x : AName.{u} A, ⨅ y : AName.{u} A, ⨅ z : AName.{u} A,
    memB x D ⊓ memB (opairB x y) F ⊓ memB (opairB x z) G ⇨ relB R y z

/-- `Q` is the pointwise order on the continuous-map space `C`. -/
noncomputable def isPointwiseOrderB
    (Q C D R : AName.{u} A) : A :=
  subsetB Q (prodB C C) ⊓
    ⨅ F : AName.{u} A, ⨅ G : AName.{u} A,
      memB F C ⊓ memB G C ⇨
        (relB Q F G ⇨ pointwiseLeB F G D R) ⊓
          (pointwiseLeB F G D R ⇨ relB Q F G)

/-- Definition 19 interpreted in `V^A`.

`Fun : D → C` and `Lam : C → D` are graph names. The last conjunct is the
retraction equation `Fun ∘ Lam = id_C`. -/
noncomputable def isReflexiveDcpoB
    (D R C Q Fun Lam : AName.{u} A) : A :=
  isDcpoWithBottomB D R ⊓
    isContinuousMapSpaceB C D R ⊓
    isPointwiseOrderB Q C D R ⊓
    isScottContinuousB Fun D C R Q ⊓
    isScottContinuousB Lam C D Q R ⊓
    eqB (compB Fun Lam C C) (idB C)

/-- Definition 19's extensionality clause inside `V^A`. -/
noncomputable def isExtensionalReflexiveDcpoB
    (D R C Q Fun Lam : AName.{u} A) : A :=
  isReflexiveDcpoB D R C Q Fun Lam ⊓
    eqB (compB Lam Fun D D) (idB D)

/-- Paper-facing name for internal Definition 19. -/
noncomputable abbrev definition_19_va := @isReflexiveDcpoB

end Scott2026
