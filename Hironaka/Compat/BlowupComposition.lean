/-
Copyright (c) 2026 Daattavya Aggarwal, Minhyong Kim, Oisin Kim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daattavya Aggarwal, Minhyong Kim, Oisin Kim
-/
module

public import Hironaka.Compat.BlowupCompositionIdeals

/-!
# Ch. 0 §3 (pp. 132-133): a finite succession of monoidal transformations is one monoidal
transformation

Hironaka (p. 132 end, p. 133): "One can see that, in general, a morphism obtained by a finite
succession of monoidal transformations can be also obtained by a single monoidal transformation
with suitably chosen center. In fact, let `f₁ : X₂ → X₁` and `f₀ : X₁ → X₀` be respectively the
monoidal transformation of `X₁` with center `D₁`, and of `X₀` with center `D₀`. Let `J₁` and `J₀`
denote respectively the sheaf of ideals of `D₁` on `X₁` and of `D₀` on `X₀`. Then we can see that
for a sufficiently large integer `m` there exists a coherent sheaf of ideals `J(m)` on `X₀` such
that `f₀⁻¹(J(m)) = f₀⁻¹(J₀)ᵐ J₁`. Let `D'` be the algebraic sucheme [sic] of `X₀` defined by
`J(m) J₀`. We can then easily see that if `f' : X' → X₀` is the monoidal transformation of `X₀`
with center `D'`, there exists a unique isomorphism `h : X' → X₂` such that `f' = f₀ ∘ f₁ ∘ h`."

Neither "we can see" is proved or cited in the paper.  This file proves the second one (the
universal-property combination, `MonoidalTransformation.comp`); the existence of `J(m)` is in
`Hironaka.Compat.BlowupCompositionGeneration`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace Hironaka

universe u

namespace MonoidalTransformation

variable {X : Scheme.{u}} {D₀ : Subscheme X}

/-- "We can then easily see that if `f' : X' → X₀` is the monoidal transformation of `X₀` with
center `D'` [defined by `J(m) J₀`] ..." (p. 133): the composite `f₀ ∘ f₁` is a monoidal
transformation of `X₀` with center `J * D₀`, whenever `f₀⁻¹(J) = f₀⁻¹(J₀)ᵐ J₁`.

Gap filled (the paper only says "we can then easily see"): `(f₀ ∘ f₁)⁻¹(J J₀)` is
`f₁⁻¹(f₀⁻¹(J₀))ᵐ⁺¹ f₁⁻¹(J₁)`, invertible; and if `g⁻¹(J J₀)` is invertible, so are `g⁻¹(J₀)` (so
`g = g₁ ∘ f₀`) and then `g₁⁻¹(J₁)` (so `g₁ = h ∘ f₁`). -/
noncomputable def comp (t₀ : MonoidalTransformation X D₀) {D₁ : Subscheme t₀.X'}
    (t₁ : MonoidalTransformation t₀.X' D₁) {m : ℕ} {J : Subscheme X}
    (hJ : Subscheme.totalTransform t₀.f J = t₀.exceptional ^ m * D₁) :
    MonoidalTransformation X (J * D₀) where
  X' := t₁.X'
  f := t₁.f ≫ t₀.f
  invertible := by
    have hkey : Subscheme.totalTransform t₀.f (J * D₀) =
        t₀.exceptional ^ m * D₁ * t₀.exceptional := by
      rw [Subscheme.totalTransform_mul, hJ]; rfl
    rw [Subscheme.totalTransform_comp, hkey, Subscheme.totalTransform_mul,
      Subscheme.totalTransform_mul, Subscheme.totalTransform_pow]
    have hE := t₁.isInvertibleIdeal_totalTransform t₀.invertible
    exact ((hE.pow m).mul t₁.invertible).mul hE
  universal := by
    intro Y f' hf'
    have hkey : Subscheme.totalTransform t₀.f (J * D₀) =
        t₀.exceptional ^ m * D₁ * t₀.exceptional := by
      rw [Subscheme.totalTransform_mul, hJ]; rfl
    have hD₀ : (Subscheme.totalTransform f' D₀).IsInvertibleIdeal := by
      have h := hf'
      rw [Subscheme.totalTransform_mul, mul_comm] at h
      exact h.of_mul_left
    obtain ⟨g₁, hg₁, huniq₁⟩ := t₀.universal Y f' hD₀
    have hgE : Subscheme.totalTransform g₁ t₀.exceptional = Subscheme.totalTransform f' D₀ := by
      rw [← hg₁, Subscheme.totalTransform_comp]; rfl
    have hD₁ : (Subscheme.totalTransform g₁ D₁).IsInvertibleIdeal := by
      have e : Subscheme.totalTransform f' (J * D₀) = Subscheme.totalTransform g₁ D₁ *
          (Subscheme.totalTransform g₁ t₀.exceptional ^ m *
            Subscheme.totalTransform g₁ t₀.exceptional) := by
        rw [← hg₁, Subscheme.totalTransform_comp, hkey, Subscheme.totalTransform_mul,
          Subscheme.totalTransform_mul, Subscheme.totalTransform_pow]
        ring
      rw [e] at hf'
      exact hf'.of_mul_left
    obtain ⟨h, hh, huniq⟩ := t₁.universal Y g₁ hD₁
    refine ⟨h, ?_, fun h' hh' => ?_⟩
    · show h ≫ t₁.f ≫ t₀.f = f'
      rw [← Category.assoc, hh, hg₁]
    · have hh'' : h' ≫ t₁.f ≫ t₀.f = f' := hh'
      exact huniq h' (huniq₁ (h' ≫ t₁.f) (by show (h' ≫ t₁.f) ≫ t₀.f = f'; rw [Category.assoc]; exact hh''))

@[simp] theorem comp_X' (t₀ : MonoidalTransformation X D₀) {D₁ : Subscheme t₀.X'}
    (t₁ : MonoidalTransformation t₀.X' D₁) {m : ℕ} {J : Subscheme X}
    (hJ : Subscheme.totalTransform t₀.f J = t₀.exceptional ^ m * D₁) :
    (t₀.comp t₁ hJ).X' = t₁.X' := rfl

theorem comp_f (t₀ : MonoidalTransformation X D₀) {D₁ : Subscheme t₀.X'}
    (t₁ : MonoidalTransformation t₀.X' D₁) {m : ℕ} {J : Subscheme X}
    (hJ : Subscheme.totalTransform t₀.f J = t₀.exceptional ^ m * D₁) :
    (t₀.comp t₁ hJ).f = t₁.f ≫ t₀.f := rfl

/-- "...there exists a unique isomorphism `h : X' → X₂` such that `f' = f₀ ∘ f₁ ∘ h`" (p. 133):
any monoidal transformation `f' : X' → X₀` with center `J J₀` is `f₀ ∘ f₁` up to a unique
isomorphism. -/
theorem existsUnique_iso_comp (t₀ : MonoidalTransformation X D₀) {D₁ : Subscheme t₀.X'}
    (t₁ : MonoidalTransformation t₀.X' D₁) {m : ℕ} {J : Subscheme X}
    (hJ : Subscheme.totalTransform t₀.f J = t₀.exceptional ^ m * D₁)
    (t' : MonoidalTransformation X (J * D₀)) :
    ∃! h : t'.X' ≅ t₁.X', h.hom ≫ t₁.f ≫ t₀.f = t'.f :=
  unique_up_to_iso t' (t₀.comp t₁ hJ)

end MonoidalTransformation

end Hironaka
