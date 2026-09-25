/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/



import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Nat.Pairing
import Mathlib.Logic.Function.Basic
import Mathlib.Order.Bounds.Image
import Mathlib.Order.CompleteLattice.Basic
import Scott2026.Domain
import Scott2026.Engeler
import Scott2026.EngelerVA
import Scott2026.Lambda
import Scott2026.Valuation
import Scott2026.Interp.Valuation.default
import Scott2026.Interp.Valuation.empty
import Scott2026.Interp.Valuation.lookup
import Scott2026.Interp.Valuation.update
import Scott2026.Interp.captureDcpo
import Scott2026.Interp.captureListCode
import Scott2026.Interp.capturePair
import Scott2026.Interp.captureVal
import Scott2026.Interp.chiBundle
import Scott2026.Interp.churchBoolSepWitness
import Scott2026.Interp.churchNot
import Scott2026.Interp.churchNotGraph
import Scott2026.Interp.engelerWithNumerals
import Scott2026.Interp.gbar
import Scott2026.Interp.interp
import Scott2026.Interp.interpClosed
import Scott2026.Interp.lemma_35_boolOpenBot
import Scott2026.Interp.lemma_35_boolOpenTop
import Scott2026.Interp.lemma_35_numeralOpen
import Scott2026.Interp.numeralFingerprint
import Scott2026.Interp.numeralSuccGraph
import Scott2026.Interp.Proofs.Core
import Scott2026.Interp.Proofs.CoreCont

/-!
# Interpretation of pure λ-terms in a reflexive dcpo (Definition 25)

Furber–Mardare–Panangaden–Scott, CSL 2026, Definition 25, following
[4, Definition 5.4.2]. This is the ground interpretation on
`ReflexiveDcpo` (Definition 19). There is no constant clause, no tag 3,
and no `Λ(D, Var, 𝔎)`.

A valuation is a Finset-supported partial function `Var → D`. The paper
requires `fv(M) ⊆ dom(ρ)`. The three clauses are

* `⟦x⟧_ρ = ρ(x)`
* `⟦MN⟧_ρ = ⟦M⟧_ρ · ⟦N⟧_ρ`
* `⟦λx. M⟧_ρ = lam(λd. ⟦M⟧_{ρ(x := d)})`

with `ρ(x := d)` the paper’s update (`dom(ρ) ∪ {x}`, overwrite at `x`).
For closed terms, `⟦M⟧ := ⟦M⟧_∅`.

The meta-lambda `d ↦ ⟦M⟧_{ρ(x := d)}` is Scott-continuous
(`interp_update_scott`), so `ReflexiveDcpo.lam` is applied to a map in
the retract’s Scott-continuous class.

[4, Theorem 5.4.4] on the capture-free fragment is `interp_sound` /
`definition_25_sound` (`LamEqNC`, `Lam.FreeFor`, naive `Lam.subst`).
Unrestricted naive substitution is false (`interp_substNaive_captures`).
The paper theory is `LamEq` (CA-β + α). Full ground soundness is
`interp_sound_full` / `definition_25_sound_full` under `[Infinite Var]`.
There is no `SetoidF_A` map, no A-valued `⟦·⟧^A_ρ`, and no Theorem 26.
-/

open Set Function

namespace Scott2026

variable {Var : Type*} {D : Type*}

end Scott2026
