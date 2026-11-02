/-
Copyright (c) 2026 Daattavya Aggarwal, Minhyong Kim, Oisin Kim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daattavya Aggarwal, Minhyong Kim, Oisin Kim
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.Order.CompletePartialOrder
public import Architect
public import Hironaka.Ch0.Blowup
public import Hironaka.Compat.BlowupCharts
public import Hironaka.Compat.BlowupBaseChange

/-!
# Strict transforms and flat maps without the preimmersion hypothesis

Colon ideals commute with flat extension, and hence strict transforms commute with the pull-back
along a flat map `j'` in a commutative square of monoidal transformations (no preimmersion needed,
as in `strictTransform_of_square`).  Used for `X̄_s = c_s⁻¹(F(s))` (Ch. IV, p. 297), where
`c_s : X̂_s → X_s` is flat but not a preimmersion.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

universe u

namespace Hironaka

open TensorProduct in
/-- Colon ideals commute with flat extension: `(I A' : x A') ⊆ (I : x) A'` for `A'` flat over `A`. -/
theorem Ideal.colon_map_le_map_colon_of_flat {A A' : Type u} [CommRing A] [CommRing A']
    [Algebra A A'] [Module.Flat A A'] (I : Ideal A) (x : A) :
    (I.map (algebraMap A A')).colon ({algebraMap A A' x} : Set A') ≤
      (I.colon ({x} : Set A)).map (algebraMap A A') := by
  intro a ha
  let ψ : A →ₗ[A] (A ⧸ I) := I.mkQ.comp (LinearMap.lsmul A A x)
  have hker : LinearMap.ker ψ = I.colon ({x} : Set A) := by
    ext r
    simp only [LinearMap.mem_ker, ψ, LinearMap.comp_apply, LinearMap.lsmul_apply,
      Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, Submodule.mem_colon,
      Set.mem_singleton_iff, forall_eq, smul_eq_mul]
    rw [mul_comm]
  have hexact := Module.Flat.ker_lTensor_eq A' A' ψ
  have ha' : a ⊗ₜ[A] (1 : A) ∈
      LinearMap.ker (TensorProduct.AlgebraTensorModule.lTensor A' A' ψ) := by
    rw [LinearMap.mem_ker, TensorProduct.AlgebraTensorModule.lTensor_tmul]
    apply (TensorProduct.tensorQuotEquivQuotSMul A' I).injective
    change TensorProduct.tensorQuotEquivQuotSMul A' I (a ⊗ₜ[A] Ideal.Quotient.mk I (x * 1)) = _
    rw [TensorProduct.tensorQuotEquivQuotSMul_tmul_mk, map_zero, Submodule.Quotient.mk_eq_zero,
      Ideal.smul_top_eq_map, Submodule.restrictScalars_mem]
    have := (Submodule.mem_colon_singleton.mp ha)
    simpa [Algebra.smul_def, mul_comm] using this
  rw [hexact, LinearMap.mem_range] at ha'
  obtain ⟨w, hw⟩ := ha'
  have key : ∀ w : A' ⊗[A] (LinearMap.ker ψ),
      TensorProduct.AlgebraTensorModule.rid A A' A'
        (TensorProduct.AlgebraTensorModule.lTensor A' A' (LinearMap.ker ψ).subtype w) ∈
        (I.colon ({x} : Set A)).map (algebraMap A A') := by
    intro w
    induction w using TensorProduct.inductionOn with
    | tmul b k =>
      rw [TensorProduct.AlgebraTensorModule.lTensor_tmul, Submodule.subtype_apply,
        TensorProduct.AlgebraTensorModule.rid_tmul, Algebra.smul_def]
      have hk : (k : A) ∈ I.colon ({x} : Set A) := by rw [← hker]; exact k.2
      exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ hk)
    | add x y hx hy =>
      rw [map_add, map_add]
      exact Ideal.add_mem _ hx hy
  have := key w
  rwa [hw, TensorProduct.AlgebraTensorModule.rid_tmul, one_smul] at this



/-- Strict transforms commute with flat base change (no preimmersion needed): in a commutative square
`j' ≫ t.f = ts.f ≫ j` of monoidal transformations, `t` with center `B` and `ts` with center `j⁻¹(B)`,
with `j'` flat, `j'⁻¹(strict transform of V) = strict transform of j⁻¹(V)`.

Deviation from the paper (gap filled): the paper asserts that strict transforms commute with the
flat base change `c_s` (p. 297: "for the case in which `ℜ = (ℜ^N_II, F)`, we have `X̄_s = c_s⁻¹(F(s))`")
without proof; this is `strictTransform_of_square` for flat maps that are not preimmersions
(`c_s : X̂_s → X_s` is not), proved stalkwise with `Ideal.colon_map_le_map_colon_of_flat`. -/
theorem MonoidalTransformation.totalTransform_strictTransform_of_flat_square
    {Y Z : Scheme.{u}} {B : Subscheme Y} (t : MonoidalTransformation Y B)
    {Bs : Subscheme Z} (ts : MonoidalTransformation Z Bs) (j : Z ⟶ Y) (j' : ts.X' ⟶ t.X')
    [Flat j'] (hsq : j' ≫ t.f = ts.f ≫ j) (hB : Subscheme.totalTransform j B = Bs)
    (V : Subscheme Y) :
    Subscheme.totalTransform j' (Subscheme.strictTransform t V) =
      Subscheme.strictTransform ts (Subscheme.totalTransform j V) := by
  have hexc := MonoidalTransformation.totalTransform_exceptional_of_square t ts j j'
    hsq hB
  have htot : Subscheme.totalTransform j' (Subscheme.totalTransform t.f V) =
      Subscheme.totalTransform ts.f (Subscheme.totalTransform j V) := by
    rw [← Subscheme.totalTransform_comp, hsq, Subscheme.totalTransform_comp]
  refine Subscheme.ext_stalkIdeal fun z => ?_
  have hflat : (j'.stalkMap z).hom.Flat := Flat.stalkMap j' z
  let : Algebra (t.X'.presheaf.stalk (j'.base z)) (ts.X'.presheaf.stalk z) :=
    (j'.stalkMap z).hom.toAlgebra
  have : Module.Flat (t.X'.presheaf.stalk (j'.base z)) (ts.X'.presheaf.stalk z) := hflat
  rw [stalkIdeal_totalTransform, Subscheme.strictTransform_stalkIdeal,
    Subscheme.strictTransform_stalkIdeal, Ideal.map_iSup]
  refine iSup_congr fun n => ?_
  obtain ⟨g, hg, -⟩ := t.invertible.exists_stalkIdeal_eq_span (j'.base z)
  have hE : ts.exceptional.stalkIdeal z = (t.exceptional.stalkIdeal (j'.base z)).map
      (j'.stalkMap z).hom := by
    rw [← hexc, stalkIdeal_totalTransform]
  have hI : (Subscheme.totalTransform ts.f (Subscheme.totalTransform j V)).stalkIdeal z =
      ((Subscheme.totalTransform t.f V).stalkIdeal (j'.base z)).map (j'.stalkMap z).hom := by
    rw [← htot, stalkIdeal_totalTransform]
  have hg' : t.exceptional.stalkIdeal (j'.base z) = Ideal.span {g} := hg
  rw [hE, hI, ← Ideal.map_pow, hg', Ideal.span_singleton_pow, Ideal.map_span, Set.image_singleton,
    Ideal.colon_span, Ideal.colon_span]
  refine le_antisymm ?_ (Ideal.colon_map_le_map_colon_of_flat (A := t.X'.presheaf.stalk (j'.base z))
    (A' := ts.X'.presheaf.stalk z) _ (g ^ n))
  rw [Ideal.map_le_iff_le_comap]
  intro a ha
  rw [Ideal.mem_comap, Submodule.mem_colon_singleton]
  rw [Submodule.mem_colon_singleton] at ha
  rw [smul_eq_mul, ← map_mul]
  exact Ideal.mem_map_of_mem _ (by simpa using ha)

end Hironaka
