/-
Copyright (c) 2026 Daattavya Aggarwal, Minhyong Kim, Oisin Kim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daattavya Aggarwal, Minhyong Kim, Oisin Kim
-/
module

public import Mathlib.RingTheory.GradedAlgebra.HomogeneousLocalization
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.Tactic.FieldSimp

/-!
# Embedding of homogeneous localizations into a field (computation device for the p. 132 lemma)

For a graded ring `A` with a ring homomorphism `j : A → K` into a field and `f ∈ A` with `j f ≠ 0`, the degree-zero
localization `A_(f)` maps to `K` by `x / f ^ n ↦ j x / (j f) ^ n`.  If `A` is a domain and `j` is injective, this map
is injective.  It turns identities between fractions in `A_(f)` (needed to compare the charts of two different
`Proj`s inside the function field) into identities in the field `K`.

Used in `Hironaka/Compat/BlowupProjectiveMaps.lean` (steps L1c of `MonoidalTransformation.isProjectiveOver`, the
unproved, uncited step of the Corollary on p. 132).  Nothing here is printed.
-/

@[expose] public section

open HomogeneousLocalization

namespace Hironaka

section

variable {σ : Type*} {A : Type*} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A] (𝒜 : ℕ → σ)
  [GradedRing 𝒜] {K : Type*} [Field K] (j : A →+* K)

/-- The embedding `A_(f) → A_f → K`, `x / f ^ n ↦ j x / (j f) ^ n` (for `j f ≠ 0`). -/
noncomputable def awayEmb (f : A) (hf : j f ≠ 0) : Away 𝒜 f →+* K :=
  (Localization.awayLift j f hf.isUnit).comp (algebraMap (Away 𝒜 f) (Localization.Away f))

variable {𝒜 j}

/-- `awayEmb` on the fraction `x / f ^ n`. -/
theorem awayEmb_mk {f : A} (hf0 : j f ≠ 0) {d : ℕ} (hf : f ∈ 𝒜 d) (n : ℕ) (x : A)
    (hx : x ∈ 𝒜 (n • d)) : awayEmb 𝒜 j f hf0 (Away.mk 𝒜 hf n x hx) = j x / j f ^ n := by
  have hv : j f * (j f)⁻¹ = 1 := mul_inv_cancel₀ hf0
  rw [awayEmb, RingHom.comp_apply, HomogeneousLocalization.algebraMap_apply, Away.val_mk]
  have := Localization.awayLift_mk j f x (j f)⁻¹ hv n
  rw [this, inv_pow, div_eq_mul_inv]

/-- `awayEmb` on the image of `A₀`. -/
theorem awayEmb_algebraMap {f : A} (hf0 : j f ≠ 0) (c : 𝒜 0) :
    awayEmb 𝒜 j f hf0 (algebraMap (𝒜 0) (Away 𝒜 f) c) = j (c : A) := by
  rw [awayEmb, RingHom.comp_apply, HomogeneousLocalization.algebraMap_apply,
    HomogeneousLocalization.algebraMap_eq]
  have : (HomogeneousLocalization.fromZeroRingHom 𝒜 (Submonoid.powers f) c).val =
      algebraMap A (Localization.Away f) (c : A) := by
    show Localization.mk (c : A) 1 = _
    rw [← Localization.mk_one_eq_algebraMap]
  rw [this]
  exact IsLocalization.lift_eq _ _

/-- `awayEmb` is injective when `A` is a domain and `j` is injective. -/
theorem awayEmb_injective [IsDomain A] (hj : Function.Injective j) {f : A} (hf0 : j f ≠ 0) :
    Function.Injective (awayEmb 𝒜 j f hf0) := by
  have hfne : f ≠ 0 := fun h => hf0 (by rw [h, map_zero])
  refine Function.Injective.comp (g := Localization.awayLift j f hf0.isUnit) ?_
    (HomogeneousLocalization.val_injective _)
  have hunit : ∀ y : Submonoid.powers f, IsUnit (j y) := by
    rintro ⟨_, k, rfl⟩
    simpa using hf0.isUnit.pow k
  show Function.Injective (IsLocalization.lift (M := Submonoid.powers f) hunit)
  rw [IsLocalization.lift_injective_iff]
  intro x y
  constructor
  · intro h
    rw [IsLocalization.eq_iff_exists (Submonoid.powers f)] at h
    obtain ⟨⟨_, k, rfl⟩, hk⟩ := h
    have hfk : f ^ k ≠ 0 := pow_ne_zero _ hfne
    have := mul_left_cancel₀ hfk hk
    rw [this]
  · intro h
    rw [hj h]

/-- `awayEmb` is compatible with `awayMap`. -/
theorem awayEmb_awayMap {f g x : A} {d e : ℕ} (hf : f ∈ 𝒜 d) (hg : g ∈ 𝒜 e) (hx : x = f * g)
    (hf0 : j f ≠ 0) (hx0 : j x ≠ 0) (z : Away 𝒜 f) :
    awayEmb 𝒜 j x hx0 (awayMap 𝒜 hg hx z) = awayEmb 𝒜 j f hf0 z := by
  obtain ⟨n, a, ha, rfl⟩ := Away.mk_surjective 𝒜 hf z
  rw [awayMap_mk, awayEmb_mk hx0, awayEmb_mk hf0]
  have hg0 : j g ≠ 0 := by
    intro h; apply hx0; rw [hx, map_mul, h, mul_zero]
  rw [hx, map_mul, map_mul, map_pow, mul_pow]
  field_simp

end

end Hironaka
