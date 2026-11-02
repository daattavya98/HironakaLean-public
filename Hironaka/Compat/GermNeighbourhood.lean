/-
Copyright (c) 2026 Daattavya Aggarwal, Minhyong Kim, Oisin Kim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daattavya Aggarwal, Minhyong Kim, Oisin Kim
-/
module

public import Hironaka.Compat.FrameCoordinates

/-!
# Finitely many germ conditions hold on a common neighbourhood (Compat API for Corollary 2)

Hironaka, Ch. 0, proof of Corollary 2 (p. 145), works with elements of the local rings `O_{X,x}` and then with
sections over a neighbourhood.  This module collects the elementary spreading-out lemmas for finitely many
conditions:

* `Hironaka.exists_opens_le_of_finite`: finitely many open neighbourhoods of a point have a common
  open neighbourhood inside each;
* `Hironaka.exists_sections_of_stalks`: finitely many elements of the stalk at `x` are the germs of sections over
  a common neighbourhood;
* `Hironaka.exists_opens_resO_eq_of_germ_eq`: finitely many equalities of germs hold, as equalities of sections,
  on a common neighbourhood.

This is infrastructure (no statement of the paper); it is not a deviation.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme TopologicalSpace Opposite

namespace Hironaka

universe u

variable {X : Scheme.{u}}

/-- Restriction of functions commutes with finite sums. -/
theorem resO_sum {W V : X.Opens} (h : V ≤ W) {κ : Type*} (t : Finset κ) (a : κ → Γ(X, W)) :
    resO X h (∑ k ∈ t, a k) = ∑ k ∈ t, resO X h (a k) :=
  map_sum (X.presheaf.map (homOfLE h).op).hom _ _

/-- Finitely many open neighbourhoods of `x` have a common open neighbourhood inside each of them. -/
theorem exists_opens_le_of_finite {κ : Type*} [Finite κ] {x : X} (T : κ → X.Opens)
    (hT : ∀ k, x ∈ T k) : ∃ (V : X.Opens) (_ : x ∈ V), ∀ k, V ≤ T k :=
  ⟨⟨⋂ k, (T k : Set X), isOpen_iInter_of_finite fun k => (T k).isOpen⟩, Set.mem_iInter.mpr hT,
    fun k _ hz => Set.mem_iInter.mp hz k⟩

/-- Finitely many elements of the stalk at `x` are the germs of sections over a common open neighbourhood. -/
theorem exists_sections_of_stalks {κ : Type*} [Finite κ] {x : X} (e : κ → X.presheaf.stalk x) :
    ∃ (V : X.Opens) (hx : x ∈ V) (s : κ → Γ(X, V)), ∀ k, (X.presheaf.germ V x hx).hom (s k) = e k := by
  have h1 : ∀ k, ∃ (T : X.Opens) (hx : x ∈ T) (s : Γ(X, T)), (X.presheaf.germ T x hx).hom s = e k :=
    fun k => X.presheaf.exists_germ_eq (e k)
  choose T hxT s hs using h1
  obtain ⟨V, hxV, hV⟩ := exists_opens_le_of_finite T hxT
  refine ⟨V, hxV, fun k => (X.presheaf.map (homOfLE (hV k)).op).hom (s k), fun k => ?_⟩
  rw [TopCat.Presheaf.germ_res_apply]
  exact hs k

/-- Finitely many equalities of germs at `x` between sections over `V` hold as equalities of sections over a
common open neighbourhood `V' ≤ V` of `x`. -/
theorem exists_opens_resO_eq_of_germ_eq {κ : Type*} [Finite κ] {x : X} {V : X.Opens} (hx : x ∈ V)
    (s t : κ → Γ(X, V))
    (h : ∀ k, (X.presheaf.germ V x hx).hom (s k) = (X.presheaf.germ V x hx).hom (t k)) :
    ∃ (V' : X.Opens) (_ : x ∈ V') (hV' : V' ≤ V), ∀ k, resO X hV' (s k) = resO X hV' (t k) := by
  have h1 : ∀ k, ∃ (T : X.Opens) (hxT : x ∈ T) (hT : T ≤ V), resO X hT (s k) = resO X hT (t k) := by
    intro k
    obtain ⟨T, hxT, iU, iV, e⟩ := TopCat.Presheaf.germ_eq X.presheaf x hx hx (s k) (t k) (h k)
    exact ⟨T, hxT, iU.le, e⟩
  choose T hxT hT he using h1
  obtain ⟨V₀, hxV₀, hV₀T⟩ := exists_opens_le_of_finite T hxT
  refine ⟨V₀ ⊓ V, ⟨hxV₀, hx⟩, inf_le_right, fun k => ?_⟩
  have := congrArg (resO X (inf_le_left.trans (hV₀T k) : V₀ ⊓ V ≤ T k)) (he k)
  rw [resO_resO, resO_resO] at this
  exact this

end Hironaka
