/-
Copyright (c) 2026 Daattavya Aggarwal, Minhyong Kim, Oisin Kim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daattavya Aggarwal, Minhyong Kim, Oisin Kim
-/
module

public import Hironaka.Compat.OModulesRestrict
public import Hironaka.Compat.RModuleRestrict

/-!
# Ch. 0 §2 (pp. 124–125): locality of blowing-ups

> The assertions of (a) and (b) follow from this fact and the result stated in the preceding paragraph. (p. 125)

The derivation of assertions (a) and (b) of p. 124 passes to an open set of the target of a blowing-up, where
the blown-up module is compared with Grothendieck's `P(A, J)` (p. 124).  The paper does not state that the
part of a blowing-up over an open set is a blowing-up of the restriction; the lemma of this file fills this gap.

* `Hironaka.isBlowingUp_restrictMap`: if `Φ : N ⟶ M` is a blowing-up in `𝓜(ℛ)` and `U` is open in the space of `M`,
  then the induced morphism `N|Φ⁻¹(U) ⟶ M|U` is a blowing-up in `𝓜(ℛ)`.
-/

@[expose] public section

open CategoryTheory TopologicalSpace

noncomputable section

universe u

namespace Hironaka

open RModule

/-- Gap filled: the part of a blowing-up over an open set is a blowing-up of the restriction.

The paper does not state this; it is needed to compare a blowing-up of a quasi-coherent module, over an open set
of the target, with Grothendieck's `P(A, J)` (p. 124).  If `Φ : N ⟶ M` is a blowing-up of `M` in `𝓜(ℛ)` and
`U` is open in the space of `M`, then the induced morphism `N|Φ⁻¹(U) ⟶ M|U` is a blowing-up of `M|U` in `𝓜(ℛ)`.

Proof: `N|Φ⁻¹(U)` is invertible, being the inverse image of an invertible module along an open immersion.  Given
`Ψ : Q ⟶ M|U` with `Q` invertible, the universal property of `Φ` applied to `Ψ ≫ M|U ⟶ M` gives a unique `Ξ : Q ⟶ N`;
its underlying map lands in `Φ⁻¹(U)`, so it factors uniquely through `N|Φ⁻¹(U)`. -/
theorem isBlowingUp_restrictMap {N M : RModule.{u}} (Φ : N ⟶ M)
    (h : IsBlowingUp (𝟭 RModule.{u}) Φ) (U : Opens M.X) :
    IsBlowingUp (𝟭 RModule.{u}) (RModule.restrictMap Φ U) := by
  refine ⟨?_, ?_⟩
  · exact OModules.isInvertible_pullback_of_isOpenImmersion
      (N.X.ofRestrict ((Opens.map Φ.f.base).obj U).isOpenEmbedding) N.J h.invertible
  · intro Q Ψ hQ
    obtain ⟨Ξ, hΞ, hΞu⟩ := h.universal Q (Ψ ≫ restrictIncl M U) hQ
    have hmem : ∀ q, Ξ.f.base q ∈ (Opens.map Φ.f.base).obj U := by
      intro q
      have hq : (Ξ ≫ Φ).f.base q = (Ψ ≫ restrictIncl M U).f.base q := by rw [hΞ]
      change Φ.f.base (Ξ.f.base q) ∈ U
      have h2 : Φ.f.base (Ξ.f.base q) = (M.X.ofRestrict U.isOpenEmbedding).base (Ψ.f.base q) := hq
      rw [h2]
      exact (Ψ.f.base q).2
    refine ⟨restrictLift _ Ξ hmem, ?_, ?_⟩
    · apply restrictIncl_cancel
      rw [Category.assoc, restrictMap_incl, ← Category.assoc, restrictLift_incl, hΞ]
    · intro Ξ' hΞ'
      apply restrictLift_unique
      apply hΞu
      change (Ξ' ≫ restrictIncl N _) ≫ Φ = Ψ ≫ restrictIncl M U
      rw [Category.assoc, ← restrictMap_incl, ← Category.assoc, hΞ']

end Hironaka
