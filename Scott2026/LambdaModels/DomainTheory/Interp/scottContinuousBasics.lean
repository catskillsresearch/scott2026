/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/

import Mathlib.Data.Set.Image
import Scott2026.LambdaModels.DomainTheory.Domain
import Scott2026.LambdaModels.Engeler.Engeler

namespace Scott2026

open Set Function

variable {D : Type*} [CompleteLattice D]

theorem scottContinuous_eval {E F : Type*} [Preorder E] [Preorder F] (e : E) :
    IsScottContinuous (fun f : E → F => f e) := by
  intro S _hSne _hSdir a hlub
  exact (isLUB_pi.mp hlub) e

theorem directedOn_image_monotone {α β : Type*} [Preorder α] [Preorder β]
    {S : Set α} {f : α → β} (hdir : DirectedOn (· ≤ ·) S) (hf : Monotone f) :
    DirectedOn (· ≤ ·) (f '' S) := by
  intro y hy z hz
  obtain ⟨s, hs, rfl⟩ := (mem_image _ _ _).mp hy
  obtain ⟨t, ht, rfl⟩ := (mem_image _ _ _).mp hz
  obtain ⟨u, hu, hsu, htu⟩ := hdir s hs t ht
  exact ⟨f u, mem_image_of_mem f hu, hf hsu, hf htu⟩

theorem scottContinuous_apply {E F : Type*} [CompleteLattice E] [CompleteLattice F]
    {H : D → E → F} {g : D → E} (hH : IsScottContinuous H)
    (hHpt : ∀ d, IsScottContinuous (H d)) (hg : IsScottContinuous g) :
    IsScottContinuous (fun d => H d (g d)) := by
  intro S hne hdir a hlub
  have hHs : IsLUB (H '' S) (H a) := hH hne hdir hlub
  have hgs : IsLUB (g '' S) (g a) := hg hne hdir hlub
  have hmonoH : Monotone H := hH.monotone
  have hmono_g : Monotone g := hg.monotone
  have hdirH : DirectedOn (· ≤ ·) (H '' S) := directedOn_image_monotone hdir hmonoH
  have hdirg : DirectedOn (· ≤ ·) (g '' S) := directedOn_image_monotone hdir hmono_g
  have hSneH : (H '' S).Nonempty := hne.image H
  have hSneg : (g '' S).Nonempty := hne.image g
  refine ⟨?upper, ?least⟩
  · intro y hy
    obtain ⟨s, hs, rfl⟩ := (mem_image _ _ _).mp hy
    exact le_trans (hmonoH (hlub.1 hs) (g s)) ((hHpt a).monotone (hmono_g (hlub.1 hs)))
  · intro b hb
    have hst : ∀ s ∈ S, ∀ t ∈ S, H s (g t) ≤ b := by
      intro s hs t ht
      obtain ⟨u, hu, hsu, htu⟩ := hdir s hs t ht
      have hsu_eval : H s (g t) ≤ H u (g t) := hmonoH hsu (g t)
      have htu_eval : H u (g t) ≤ H u (g u) := (hHpt u).monotone (hmono_g htu)
      have hu_b : H u (g u) ≤ b := hb (mem_image_of_mem _ hu)
      exact (hsu_eval.trans htu_eval).trans hu_b
    have hsa : ∀ s ∈ S, H s (g a) ≤ b := by
      intro s hs
      have hHs_s : IsLUB (H s '' (g '' S)) (H s (g a)) :=
        hHpt s hSneg hdirg hgs
      refine hHs_s.2 ?_
      intro y hy
      obtain ⟨z, hz, rfl⟩ := (mem_image _ _ _).mp hy
      obtain ⟨t, ht, rfl⟩ := (mem_image _ _ _).mp hz
      exact hst s hs t ht
    have heval : IsLUB ((fun f : E → F => f (g a)) '' (H '' S)) (H a (g a)) :=
      scottContinuous_eval (g a) hSneH hdirH hHs
    refine heval.2 ?_
    intro y hy
    obtain ⟨f, hf, rfl⟩ := (mem_image _ _ _).mp hy
    obtain ⟨s, hs, rfl⟩ := (mem_image _ _ _).mp hf
    exact hsa s hs

theorem scottContinuous_of_pi {E F : Type*} [Preorder E] [Preorder F]
    {H : D → E → F} (hpt : ∀ e, IsScottContinuous (fun d => H d e)) :
    IsScottContinuous H := by
  intro S hne hdir a hlub
  refine isLUB_pi.mpr fun e => ?_
  have himg : Function.eval e '' (H '' S) = (fun d => H d e) '' S := by
    rw [← image_comp]
    rfl
  rw [himg]
  exact hpt e hne hdir hlub

theorem ReflexiveDcpo.app_comp_scott (R : ReflexiveDcpo D) {f g : D → D}
    (hf : IsScottContinuous f) (hg : IsScottContinuous g) :
    IsScottContinuous (fun d => R.app (f d) (g d)) :=
  scottContinuous_apply (hf.comp R.fun_scott)
    (fun d => R.fun_scott_pt (f d)) hg

end Scott2026
