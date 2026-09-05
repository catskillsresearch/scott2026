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

namespace RelFun

variable {S : ASetoid (A := A) X} {T : ASetoid (A := A) Y}

/-- Definition 8 (i): substitution of equals on the source. -/
theorem subst_left (f : RelFun S T) (x₁ x₂ : X) (y : Y) :
    S.eq x₁ x₂ ⊓ f.val x₁ y ≤ f.val x₂ y := by
  have hy : f.val x₁ y ≤ T.eq y y := (f.le_eps x₁ y).trans inf_le_right
  have hmp : S.eq x₁ x₂ ⊓ T.eq y y ⊓ f.val x₁ y ≤ f.val x₂ y :=
    le_himp_iff.mp (le_inf_iff.mp (f.respects x₁ x₂ y y)).1
  exact hmp.trans' (le_inf (le_inf inf_le_left (inf_le_right.trans hy)) inf_le_right)

/-- Definition 8 (i): substitution of equals on the target. -/
theorem subst_right (f : RelFun S T) (x : X) (y₁ y₂ : Y) :
    T.eq y₁ y₂ ⊓ f.val x y₁ ≤ f.val x y₂ := by
  have hx : f.val x y₁ ≤ S.eq x x := (f.le_eps x y₁).trans inf_le_left
  have hmp : S.eq x x ⊓ T.eq y₁ y₂ ⊓ f.val x y₁ ≤ f.val x y₂ :=
    le_himp_iff.mp (le_inf_iff.mp (f.respects x x y₁ y₂)).1
  exact hmp.trans' (le_inf (le_inf (inf_le_right.trans hx) inf_le_left) inf_le_right)

@[ext]
theorem ext {f g : RelFun S T} (h : ∀ x y, f.val x y = g.val x y) : f = g := by
  cases f
  cases g
  simp only [RelFun.mk.injEq]
  exact funext fun x => funext (h x)

end RelFun

variable {Z : Type*}

/-- Definition 8: composition value, `(g ∘ f)(x, z) = ⨆_y f(x,y) ⊓ g(y,z)`. -/
def relCompVal {S : ASetoid (A := A) X} {T : ASetoid (A := A) Y} {U : ASetoid (A := A) Z}
    (g : RelFun T U) (f : RelFun S T) (x : X) (z : Z) : A :=
  ⨆ y : Y, f.val x y ⊓ g.val y z

/-- Definition 8: composition in `SetoidR_A`. -/
def RelFun.comp {S : ASetoid (A := A) X} {T : ASetoid (A := A) Y} {U : ASetoid (A := A) Z}
    (g : RelFun T U) (f : RelFun S T) : RelFun S U where
  val := relCompVal g f
  respects := fun x₁ x₂ z₁ z₂ => by
    have key : ∀ (u₁ u₂ : X) (w₁ w₂ : Z),
        S.eq u₁ u₂ ⊓ U.eq w₁ w₂ ⊓ relCompVal g f u₁ w₁ ≤ relCompVal g f u₂ w₂ := by
      intro u₁ u₂ w₁ w₂
      unfold relCompVal
      rw [inf_iSup_eq]
      refine iSup_le fun y => le_iSup_of_le y (le_inf ?_ ?_)
      · exact (f.subst_left u₁ u₂ y).trans'
          (le_inf (inf_le_of_left_le inf_le_left) (inf_le_of_right_le inf_le_left))
      · exact (g.subst_right y w₁ w₂).trans'
          (le_inf (inf_le_of_left_le inf_le_right) (inf_le_of_right_le inf_le_right))
    refine le_inf ?_ ?_ <;> rw [le_himp_iff]
    · exact key x₁ x₂ z₁ z₂
    · have h := key x₂ x₁ z₂ z₁
      rwa [S.symm x₂ x₁, U.symm z₂ z₁] at h
  le_eps := fun x z => by
    refine iSup_le fun y => le_inf ?_ ?_
    · exact inf_le_of_left_le ((f.le_eps x y).trans inf_le_left)
    · exact inf_le_of_right_le ((g.le_eps y z).trans inf_le_right)
  single_valued := fun x z₁ z₂ => by
    unfold relCompVal
    rw [iSup_inf_eq]
    refine iSup_le fun y₁ => ?_
    rw [inf_iSup_eq]
    refine iSup_le fun y₂ => ?_
    have hy : f.val x y₁ ⊓ f.val x y₂ ≤ T.eq y₁ y₂ := f.single_valued x y₁ y₂
    have hg2 : T.eq y₁ y₂ ⊓ g.val y₂ z₂ ≤ g.val y₁ z₂ := by
      have h := g.subst_left y₂ y₁ z₂
      rwa [T.symm y₂ y₁] at h
    refine (g.single_valued y₁ z₁ z₂).trans' (le_inf (inf_le_of_left_le inf_le_right) ?_)
    refine hg2.trans' (le_inf ?_ (inf_le_of_right_le inf_le_right))
    exact hy.trans' (le_inf (inf_le_of_left_le inf_le_left) (inf_le_of_right_le inf_le_left))
  total := fun x => by
    refine (f.total x).trans (iSup_le fun y => ?_)
    have hy : f.val x y ≤ T.eps y := (f.le_eps x y).trans inf_le_right
    have hstep : f.val x y ≤ f.val x y ⊓ ⨆ z, g.val y z :=
      le_inf le_rfl (hy.trans (g.total y))
    refine hstep.trans ?_
    rw [inf_iSup_eq]
    refine iSup_le fun z => le_iSup_of_le z ?_
    exact le_iSup (fun y' : Y => f.val x y' ⊓ g.val y' z) y

@[simp] theorem RelFun.comp_val {S : ASetoid (A := A) X} {T : ASetoid (A := A) Y}
    {U : ASetoid (A := A) Z} (g : RelFun T U) (f : RelFun S T) (x : X) (z : Z) :
    (g.comp f).val x z = ⨆ y : Y, f.val x y ⊓ g.val y z := rfl

/-- Definition 10: graph of a functional map, `γ(f)(x,y) = ε(x) ⊓ ‖f(x) = y‖`. -/
def gamma (S : ASetoid (A := A) X) (T : ASetoid (A := A) Y) (f : X → Y) (x : X) (y : Y) : A :=
  S.eps x ⊓ T.eq (f x) y

/-- Definition 9: `X ⊸ Y` is the set of equality-preserving maps. -/
def functionalMaps (S : ASetoid (A := A) X) (T : ASetoid (A := A) Y) : Set (X → Y) :=
  {f | APoset.Functional S T f}

/-- Definition 9: `A`-valued equality of functional maps. -/
def functionalEq (S : ASetoid (A := A) X) (T : ASetoid (A := A) Y) (f₁ f₂ : X → Y) : A :=
  ⨅ x, himp (S.eps x) (T.eq (f₁ x) (f₂ x))

/-- Definition 9: the generating relation of the `SetoidF_A` hom-quotient,
`f₁ ~ f₂` iff `∀ x, ε(x) ≤ ‖f₁(x) = f₂(x)‖`. -/
def FunctionalEquiv (S : ASetoid (A := A) X) (T : ASetoid (A := A) Y)
    (f₁ f₂ : X → Y) : Prop :=
  ∀ x, S.eps x ≤ T.eq (f₁ x) (f₂ x)

theorem functionalEq_eq_top_iff {S : ASetoid (A := A) X} {T : ASetoid (A := A) Y}
    (f₁ f₂ : X → Y) :
    functionalEq S T f₁ f₂ = ⊤ ↔ FunctionalEquiv S T f₁ f₂ := by
  unfold functionalEq FunctionalEquiv
  rw [iInf_eq_top]
  exact forall_congr' fun _ => himp_eq_top_iff

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

/-- Left unit: `id_T ∘ f = f`. -/
theorem RelFun.id_comp {S : ASetoid (A := A) X} {T : ASetoid (A := A) Y}
    (f : RelFun S T) : (RelFun.id T).comp f = f := by
  refine RelFun.ext fun x z => ?_
  change (⨆ y : Y, f.val x y ⊓ T.eq y z) = f.val x z
  refine le_antisymm ?le ?ge
  · refine iSup_le fun y => ?_
    rw [inf_comm]
    exact f.subst_right x y z
  · have : f.val x z ≤ f.val x z ⊓ T.eq z z :=
      le_inf le_rfl ((f.le_eps x z).trans inf_le_right)
    exact this.trans (le_iSup (fun y => f.val x y ⊓ T.eq y z) z)

/-- Right unit: `f ∘ id_S = f`. -/
theorem RelFun.comp_id {S : ASetoid (A := A) X} {T : ASetoid (A := A) Y}
    (f : RelFun S T) : f.comp (RelFun.id S) = f := by
  refine RelFun.ext fun x z => ?_
  change (⨆ y : X, S.eq x y ⊓ f.val y z) = f.val x z
  refine le_antisymm ?le ?ge
  · refine iSup_le fun y => ?_
    have h := f.subst_left y x z
    rwa [S.symm y x] at h
  · have : f.val x z ≤ S.eq x x ⊓ f.val x z :=
      le_inf ((f.le_eps x z).trans inf_le_left) le_rfl
    exact this.trans (le_iSup (fun y => S.eq x y ⊓ f.val y z) x)

/-- Associativity of relational composition. -/
theorem RelFun.comp_assoc {V : Type*}
    {S : ASetoid (A := A) X} {T : ASetoid (A := A) Y}
    {U : ASetoid (A := A) Z} {R : ASetoid (A := A) V}
    (h : RelFun U R) (g : RelFun T U) (f : RelFun S T) :
    (h.comp g).comp f = h.comp (g.comp f) := by
  refine RelFun.ext fun x z => ?_
  simp only [RelFun.comp_val]
  calc ⨆ y, f.val x y ⊓ ⨆ w, g.val y w ⊓ h.val w z
      = ⨆ y, ⨆ w, f.val x y ⊓ (g.val y w ⊓ h.val w z) := by
        refine iSup_congr fun y => inf_iSup_eq (f.val x y) _
    _ = ⨆ y, ⨆ w, (f.val x y ⊓ g.val y w) ⊓ h.val w z := by
        refine iSup_congr fun y => iSup_congr fun w => (inf_assoc _ _ _).symm
    _ = ⨆ w, ⨆ y, (f.val x y ⊓ g.val y w) ⊓ h.val w z := iSup_comm
    _ = ⨆ w, (⨆ y, f.val x y ⊓ g.val y w) ⊓ h.val w z := by
        refine iSup_congr fun w =>
          Eq.symm (iSup_inf_eq (fun y => f.val x y ⊓ g.val y w) (h.val w z))

/-- Definition 8: identity and composition data, plus category laws. -/
theorem definition_8 {V : Type*}
    {S : ASetoid (A := A) X} {T : ASetoid (A := A) Y}
    {U : ASetoid (A := A) Z} {R : ASetoid (A := A) V}
    (f : RelFun S T) (g : RelFun T U) (h : RelFun U R)
    (x₁ x₂ : X) (x : X) (z : Z) :
    (RelFun.id S).val x₁ x₂ = S.eq x₁ x₂ ∧
      (g.comp f).val x z = ⨆ y : Y, f.val x y ⊓ g.val y z ∧
      (RelFun.id T).comp f = f ∧
      f.comp (RelFun.id S) = f ∧
      (h.comp g).comp f = h.comp (g.comp f) :=
  ⟨rfl, RelFun.comp_val g f x z, RelFun.id_comp f, RelFun.comp_id f,
    RelFun.comp_assoc h g f⟩

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

/-- Definition 9: `~` is an equivalence on functional maps. -/
def functionalSetoid (S : ASetoid (A := A) X) (T : ASetoid (A := A) Y) :
    Setoid {f : X → Y // APoset.Functional S T f} where
  r f g := FunctionalEquiv S T f.1 g.1
  iseqv := {
    refl := fun f x => functional_eps_le f.2 x
    symm := fun {f g} h x => (h x).trans_eq (T.symm (f.1 x) (g.1 x))
    trans := fun {f g h} hfg hgh x =>
      (le_inf (hfg x) (hgh x)).trans (T.trans (f.1 x) (g.1 x) (h.1 x))
  }

/-- Definition 9: `SetoidF_A(X,Y)` is the quotient of `X ⊸ Y` by `~`. -/
def SetoidFHom (S : ASetoid (A := A) X) (T : ASetoid (A := A) Y) : Type _ :=
  Quotient (functionalSetoid S T)

namespace SetoidFHom

/-- Identity morphism of `SetoidF_A`. -/
def id (S : ASetoid (A := A) X) : SetoidFHom S S :=
  Quotient.mk (functionalSetoid S S) ⟨_root_.id, APoset.Functional.id⟩

/-- Composition is well-defined on the hom-quotient (Definition 9). -/
theorem comp_respects_equiv {Z : Type*}
    {S : ASetoid (A := A) X} {T : ASetoid (A := A) Y} {U : ASetoid (A := A) Z}
    {f₁ f₂ : X → Y} {g₁ g₂ : Y → Z}
    (hf₁ : APoset.Functional S T f₁) (_hf₂ : APoset.Functional S T f₂)
    (_hg₁ : APoset.Functional T U g₁) (hg₂ : APoset.Functional T U g₂)
    (hf : FunctionalEquiv S T f₁ f₂) (hg : FunctionalEquiv T U g₁ g₂) :
    FunctionalEquiv S U (g₁ ∘ f₁) (g₂ ∘ f₂) := by
  intro x
  have hfg : S.eps x ≤ T.eq (f₁ x) (f₂ x) := hf x
  have hg1 : S.eps x ≤ U.eq (g₁ (f₁ x)) (g₂ (f₁ x)) :=
    (functional_eps_le hf₁ x).trans (hg (f₁ x))
  have hg2 : S.eps x ≤ U.eq (g₂ (f₁ x)) (g₂ (f₂ x)) :=
    hfg.trans (hg₂ (f₁ x) (f₂ x))
  exact (le_inf hg1 hg2).trans (U.trans _ _ _)

/-- Composition of `SetoidF_A` morphisms. -/
def comp {Z : Type*} {S : ASetoid (A := A) X} {T : ASetoid (A := A) Y}
    {U : ASetoid (A := A) Z} (g : SetoidFHom T U) (f : SetoidFHom S T) :
    SetoidFHom S U :=
  Quotient.liftOn₂ g f
    (fun g f =>
      Quotient.mk (functionalSetoid S U)
        ⟨g.1 ∘ f.1, APoset.Functional.comp f.2 g.2⟩)
    (fun g₁ f₁ g₂ f₂ hg hf =>
      Quotient.sound
        (@comp_respects_equiv A _ X Y Z S T U f₁.1 f₂.1 g₁.1 g₂.1
          f₁.2 f₂.2 g₁.2 g₂.2 hf hg))

end SetoidFHom

/-- Definition 9: hom-object is the quotient, and id/comp are well-defined. -/
theorem definition_9 {Z : Type*}
    (S : ASetoid (A := A) X) (T : ASetoid (A := A) Y) (U : ASetoid (A := A) Z) :
    FunctionalEquiv S S id id ∧
      APoset.Functional S S id ∧
      (∀ {f₁ f₂ : X → Y} {g₁ g₂ : Y → Z},
        APoset.Functional S T f₁ → APoset.Functional S T f₂ →
        APoset.Functional T U g₁ → APoset.Functional T U g₂ →
        FunctionalEquiv S T f₁ f₂ → FunctionalEquiv T U g₁ g₂ →
          FunctionalEquiv S U (g₁ ∘ f₁) (g₂ ∘ f₂)) :=
  ⟨fun _ => le_rfl, APoset.Functional.id, SetoidFHom.comp_respects_equiv⟩

/-- Definition 10: `γ` is well-defined on `~`. -/
theorem gamma_equiv {S : ASetoid (A := A) X} {T : ASetoid (A := A) Y}
    {f g : X → Y} (h : FunctionalEquiv S T f g) (x : X) (y : Y) :
    gamma S T f x y = gamma S T g x y := by
  unfold gamma
  refine le_antisymm ?le ?ge
  · have : S.eps x ⊓ T.eq (f x) y ≤ T.eq (g x) y :=
      (inf_le_inf ((h x).trans_eq (T.symm (f x) (g x))) (le_refl _)).trans
        (T.trans (g x) (f x) y)
    exact le_inf inf_le_left this
  · have : S.eps x ⊓ T.eq (g x) y ≤ T.eq (f x) y :=
      (inf_le_inf (h x) (le_refl _)).trans (T.trans (f x) (g x) y)
    exact le_inf inf_le_left this

/-- Definition 10: `γ` preserves identities. -/
theorem gamma_id (S : ASetoid (A := A) X) (x y : X) :
    gamma S S id x y = (RelFun.id S).val x y := by
  unfold gamma RelFun.id
  exact inf_eq_right.mpr (S.eq_le_eps_left x y)

/-- Definition 10: `γ` preserves composition. -/
theorem gamma_comp {Z : Type*}
    {S : ASetoid (A := A) X} {T : ASetoid (A := A) Y} {U : ASetoid (A := A) Z}
    {f : X → Y} {g : Y → Z}
    (hf : APoset.Functional S T f) (hg : APoset.Functional T U g)
    (x : X) (z : Z) :
    gamma S U (g ∘ f) x z =
      relCompVal (RelFun.ofFunctional T U g hg) (RelFun.ofFunctional S T f hf) x z := by
  unfold gamma relCompVal RelFun.ofFunctional
  refine le_antisymm ?le ?ge
  · have hε : S.eps x ≤ T.eps (f x) := functional_eps_le hf x
    have : S.eps x ⊓ U.eq (g (f x)) z ≤
        S.eps x ⊓ T.eq (f x) (f x) ⊓ (T.eps (f x) ⊓ U.eq (g (f x)) z) :=
      le_inf (le_inf inf_le_left (inf_le_left.trans hε))
        (le_inf (inf_le_left.trans hε) inf_le_right)
    exact this.trans (le_iSup (fun y =>
      (S.eps x ⊓ T.eq (f x) y) ⊓ (T.eps y ⊓ U.eq (g y) z)) (f x))
  · refine iSup_le fun y => ?_
    have hmap : T.eq (f x) y ≤ U.eq (g (f x)) (g y) := hg (f x) y
    have : S.eps x ⊓ T.eq (f x) y ⊓ (T.eps y ⊓ U.eq (g y) z) ≤
        S.eps x ⊓ U.eq (g (f x)) z :=
      le_inf (inf_le_of_left_le inf_le_left)
        ((le_inf (inf_le_of_left_le inf_le_right) (inf_le_of_right_le inf_le_right)).trans
          ((le_inf (inf_le_left.trans hmap) inf_le_right).trans
            (U.trans (g (f x)) (g y) z)))
    exact this

/-- Definition 10: `γ` is faithful on representatives. -/
theorem gamma_faithful {S : ASetoid (A := A) X} {T : ASetoid (A := A) Y}
    {f g : X → Y} (hf : APoset.Functional S T f) (hg : APoset.Functional S T g)
    (h : RelFun.ofFunctional S T f hf = RelFun.ofFunctional S T g hg) :
    FunctionalEquiv S T f g := by
  intro x
  have hval : gamma S T f x (f x) = gamma S T g x (f x) := by
    simpa [RelFun.ofFunctional] using
      congrArg (fun r : RelFun S T => r.val x (f x)) h
  have hfx : gamma S T f x (f x) = S.eps x :=
    inf_eq_left.mpr (functional_eps_le hf x)
  have : S.eps x = S.eps x ⊓ T.eq (g x) (f x) := by
    calc S.eps x = gamma S T f x (f x) := hfx.symm
      _ = gamma S T g x (f x) := hval
      _ = S.eps x ⊓ T.eq (g x) (f x) := rfl
  exact ((le_inf_iff.mp this.le).2).trans_eq (T.symm (g x) (f x))

/-- Definition 10: `γ` is a faithful functor `SetoidF_A → SetoidR_A`. -/
theorem definition_10 {Z : Type*}
    {S : ASetoid (A := A) X} {T : ASetoid (A := A) Y} {U : ASetoid (A := A) Z}
    {f : X → Y} {g : Y → Z}
    (hf : APoset.Functional S T f) (hg : APoset.Functional T U g)
    {f' : X → Y} (hf' : APoset.Functional S T f')
    (hequiv : FunctionalEquiv S T f f')
    (hgraph : RelFun.ofFunctional S T f hf = RelFun.ofFunctional S T f' hf')
    (x : X) (y : Y) (z : Z) :
    gamma S T f x y = gamma S T f' x y ∧
      gamma S S id x x = (RelFun.id S).val x x ∧
      gamma S U (g ∘ f) x z =
        relCompVal (RelFun.ofFunctional T U g hg)
          (RelFun.ofFunctional S T f hf) x z ∧
      FunctionalEquiv S T f f' :=
  ⟨gamma_equiv hequiv x y, gamma_id S x x, gamma_comp hf hg x z,
    gamma_faithful hf hf' hgraph⟩

/-!
## Definition 13: realizing a relational function on a complete codomain
-/

variable {S : ASetoid (A := A) X} {T : ASetoid (A := A) Y}

/-- The family `y ↦ f(x,y)` is compatible by single-valuedness. -/
theorem RelFun.val_compatible (f : RelFun S T) (x : X) (y₁ y₂ : Y) :
    f.val x y₁ ⊓ f.val x y₂ ≤ T.eq y₁ y₂ :=
  f.single_valued x y₁ y₂

/-- Definition 13: choose `F(f)(x)` by mixing `f(x, –)` in a complete codomain. -/
noncomputable def functionalOfRel (hT : T.IsComplete) (f : RelFun S T) : X → Y :=
  fun x =>
    Classical.choose (hT Y (fun y => f.val x y) id (f.val_compatible x))

theorem functionalOfRel_le (hT : T.IsComplete) (f : RelFun S T) (x : X) (y : Y) :
    f.val x y ≤ T.eq y (functionalOfRel hT f x) :=
  Classical.choose_spec (hT Y (fun y => f.val x y) id (f.val_compatible x)) y

/-- Definition 13: `F(f)` preserves `A`-valued equality. -/
theorem functionalOfRel_functional (hT : T.IsComplete) (f : RelFun S T) :
    APoset.Functional S T (functionalOfRel hT f) := by
  intro x₁ x₂
  have hx : S.eq x₁ x₂ ≤ ⨆ y, f.val x₁ y :=
    (S.eq_le_eps_left x₁ x₂).trans (f.total x₁)
  refine (le_inf (le_refl (S.eq x₁ x₂)) hx).trans ?_
  rw [inf_iSup_eq]
  refine iSup_le fun y => ?_
  have h₁ : S.eq x₁ x₂ ⊓ f.val x₁ y ≤ T.eq y (functionalOfRel hT f x₁) :=
    inf_le_right.trans (functionalOfRel_le hT f x₁ y)
  have h₂ : S.eq x₁ x₂ ⊓ f.val x₁ y ≤ T.eq y (functionalOfRel hT f x₂) :=
    (f.subst_left x₁ x₂ y).trans (functionalOfRel_le hT f x₂ y)
  have : S.eq x₁ x₂ ⊓ f.val x₁ y ≤
      T.eq (functionalOfRel hT f x₁) y ⊓ T.eq y (functionalOfRel hT f x₂) :=
    le_inf (by rw [T.symm]; exact h₁) h₂
  exact this.trans (T.trans _ _ _)

/-- Definition 13: `γ(F(f)) = f`. -/
theorem functionalOfRel_gamma (hT : T.IsComplete) (f : RelFun S T) (x : X) (y : Y) :
    gamma S T (functionalOfRel hT f) x y = f.val x y := by
  unfold gamma
  refine le_antisymm ?le ?ge
  · have htot : S.eps x ≤ ⨆ y', f.val x y' := f.total x
    refine (inf_le_inf htot (le_refl (T.eq (functionalOfRel hT f x) y))).trans ?_
    rw [iSup_inf_eq]
    refine iSup_le fun y' => ?_
    have hy' : f.val x y' ≤ T.eq y' (functionalOfRel hT f x) :=
      functionalOfRel_le hT f x y'
    have heq : f.val x y' ⊓ T.eq (functionalOfRel hT f x) y ≤ T.eq y' y :=
      (le_inf (inf_le_left.trans hy') inf_le_right).trans
        (T.trans y' (functionalOfRel hT f x) y)
    exact (f.subst_right x y' y).trans' (le_inf heq inf_le_left)
  · exact le_inf ((f.le_eps x y).trans inf_le_left)
      (by rw [T.symm]; exact functionalOfRel_le hT f x y)

/-- Definition 13, inverse step: `ℱ(γ(f)) ~ f`. -/
theorem functionalOfRel_ofFunctional (hT : T.IsComplete)
    (f : X → Y) (hf : APoset.Functional S T f) (x : X) :
    S.eps x ≤ T.eq (functionalOfRel hT (RelFun.ofFunctional S T f hf) x) (f x) := by
  have heq := functionalOfRel_gamma hT (RelFun.ofFunctional S T f hf) x (f x)
  change S.eps x ⊓ T.eq (functionalOfRel hT (RelFun.ofFunctional S T f hf) x) (f x) =
      S.eps x ⊓ T.eq (f x) (f x) at heq
  have hR : S.eps x ⊓ T.eq (f x) (f x) = S.eps x :=
    inf_eq_left.mpr (functional_eps_le hf x)
  rw [hR] at heq
  exact (le_inf_iff.mp heq.ge).2

/-- `γ` as a map on the `SetoidF_A` hom-quotient. -/
def SetoidFHom.toRelFun {S : ASetoid (A := A) X} {T : ASetoid (A := A) Y}
    (f : SetoidFHom S T) : RelFun S T :=
  Quotient.lift (fun f => RelFun.ofFunctional S T f.1 f.2)
    (fun _ _ h => RelFun.ext fun x y => gamma_equiv h x y) f

/-- `ℱ` as a map from relational homs into the `SetoidF_A` quotient. -/
noncomputable def SetoidFHom.ofRelFun {S : ASetoid (A := A) X}
    {T : ASetoid (A := A) Y} (hT : T.IsComplete) (f : RelFun S T) :
    SetoidFHom S T :=
  Quotient.mk (functionalSetoid S T)
    ⟨functionalOfRel hT f, functionalOfRel_functional hT f⟩

theorem SetoidFHom.toRelFun_ofRelFun {S : ASetoid (A := A) X}
    {T : ASetoid (A := A) Y} (hT : T.IsComplete) (f : RelFun S T) :
    SetoidFHom.toRelFun (SetoidFHom.ofRelFun hT f) = f :=
  RelFun.ext fun x y => functionalOfRel_gamma hT f x y

theorem SetoidFHom.ofRelFun_toRelFun {S : ASetoid (A := A) X}
    {T : ASetoid (A := A) Y} (hT : T.IsComplete) (f : SetoidFHom S T) :
    SetoidFHom.ofRelFun hT (SetoidFHom.toRelFun f) = f := by
  refine Quotient.inductionOn f fun f => ?_
  refine Quotient.sound ?_
  intro x
  exact functionalOfRel_ofFunctional hT f.1 f.2 x

/-- Definition 13: if `Y` is complete, `ℱ` is inverse to `γ` on homs,
`SetoidR_A(X,Y) ≅ SetoidF_A(X,Y)`. Existing `definition_13` is only
`γ ∘ ℱ = id` on representatives. -/
theorem definition_13_iso {S : ASetoid (A := A) X} {T : ASetoid (A := A) Y}
    (hT : T.IsComplete) :
    (∀ f : RelFun S T,
      SetoidFHom.toRelFun (SetoidFHom.ofRelFun hT f) = f) ∧
    (∀ f : SetoidFHom S T,
      SetoidFHom.ofRelFun hT (SetoidFHom.toRelFun f) = f) :=
  ⟨SetoidFHom.toRelFun_ofRelFun hT, SetoidFHom.ofRelFun_toRelFun hT⟩

end Scott2026
