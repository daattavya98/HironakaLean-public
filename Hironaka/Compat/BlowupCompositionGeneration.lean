/-
Copyright (c) 2026 Daattavya Aggarwal, Minhyong Kim, Oisin Kim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daattavya Aggarwal, Minhyong Kim, Oisin Kim
-/
module

public import Hironaka.Compat.BlowupCompositionIdeals

/-!
# Ch. 0 §3 (p. 133): the sheaf of ideals `J(m)`

"for a sufficiently large integer `m` there exists a coherent sheaf of ideals `J(m)` on `X₀` such
that `f₀⁻¹(J(m)) = f₀⁻¹(J₀)ᵐ J₁`."
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open scoped nonZeroDivisors

namespace Hironaka

universe u

namespace MonoidalTransformation

variable {X : Scheme.{u}} {B : Subscheme X} (t : MonoidalTransformation X B) (U : X.affineOpens)
  {a : Γ(X, U)}

/-! ### The chart `V_a` as an affine open of `X'` with ring `Γ(X, U)[I/a]` -/

/-- The open `V_a ⊆ X'`, the image of the chart. -/
noncomputable def chartV (ha : a ∈ B.ideal U) : t.X'.Opens :=
  have := t.isOpenImmersion_chart U ha
  t.chart U ha ''ᵁ ⊤

theorem chartV_eq_chartOpen (ha : a ∈ B.ideal U) : t.chartV U ha = t.chartOpen U a := by
  have := t.isOpenImmersion_chart U ha
  ext y
  change y ∈ t.chart U ha ''ᵁ ⊤ ↔ _
  rw [Scheme.Hom.image_top_eq_opensRange, ← t.range_chart U ha]
  rfl

theorem isAffineOpen_chartV (ha : a ∈ B.ideal U) : IsAffineOpen (t.chartV U ha) := by
  have := t.isOpenImmersion_chart U ha
  exact (isAffineOpen_top (Spec (chartRing B U a))).image_of_isOpenImmersion (t.chart U ha)

theorem chartV_le (ha : a ∈ B.ideal U) : t.chartV U ha ≤ t.f ⁻¹ᵁ U.1 := by
  have := t.isOpenImmersion_chart U ha
  rintro y ⟨z, -, rfl⟩
  show t.f (t.chart U ha z) ∈ U.1
  rw [← Scheme.Hom.comp_apply, chart_f]
  exact chartToBase_apply_mem B U a z

/-- The chart `V_a` as an affine open. -/
noncomputable def chartAff (ha : a ∈ B.ideal U) : t.X'.affineOpens :=
  ⟨t.chartV U ha, t.isAffineOpen_chartV U ha⟩

/-- The isomorphism `Γ(X', V_a) ≅ Γ(X, U)[I/a]` (inverse direction). -/
noncomputable def chartVEquiv (ha : a ∈ B.ideal U) :
    chartAlgebra (B.ideal U) a ≃+* Γ(t.X', t.chartV U ha) :=
  have := t.isOpenImmersion_chart U ha
  ((Scheme.ΓSpecIso (chartRing B U a)).symm ≪≫
    ((t.chart U ha).appIso ⊤).symm).commRingCatIsoToRingEquiv

theorem chartVEquiv_algebraMap (ha : a ∈ B.ideal U) (y : Γ(X, U)) :
    t.chartVEquiv U ha (algebraMap Γ(X, U) (chartAlgebra (B.ideal U) a) y) =
      t.f.appLE U (t.chartV U ha) (t.chartV_le U ha) y := by
  have := t.isOpenImmersion_chart U ha
  have key : ∀ (g : Spec (chartRing B U a) ⟶ X) (hg : t.chart U ha ≫ t.f = g)
      (h : ⊤ ≤ (t.chart U ha ≫ t.f) ⁻¹ᵁ U.1),
      (t.chart U ha ≫ t.f).appLE U.1 ⊤ h = g.appLE U.1 ⊤ (hg ▸ h) := by
    intro g hg h; subst hg; rfl
  have h1 := Scheme.Hom.appLE_comp_appLE (t.chart U ha) t.f U.1 (t.chartV U ha) ⊤
    (t.chartV_le U ha) (by rintro z -; exact ⟨z, trivial, rfl⟩)
  have h2 : ((t.chart U ha).appIso ⊤).hom
      (t.f.appLE U (t.chartV U ha) (t.chartV_le U ha) y) =
      (Scheme.ΓSpecIso (chartRing B U a)).inv (algebraMap Γ(X, U) (chartAlgebra (B.ideal U) a) y) := by
    have e1 := congrArg (fun φ => φ y) (congrArg CommRingCat.Hom.hom h1)
    simp only [CommRingCat.hom_comp, RingHom.comp_apply] at e1
    rw [key (chartToBase B U a) (t.chart_f U ha), chartToBase_appLE] at e1
    rw [Scheme.Hom.appIso_hom']
    exact e1.trans rfl
  change ((t.chart U ha).appIso ⊤).inv ((Scheme.ΓSpecIso (chartRing B U a)).inv _) = _
  rw [← h2]
  exact (CommRingCat.hom_inv_apply _ _) 

end MonoidalTransformation

end Hironaka
