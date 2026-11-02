/-
Copyright (c) 2026 Daattavya Aggarwal, Minhyong Kim, Oisin Kim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daattavya Aggarwal, Minhyong Kim, Oisin Kim
-/
module

public import Mathlib.AlgebraicGeometry.Noetherian

/-!
# Stalks at a generization are localizations

For a generization `η ⤳ y` of a point `y` of a scheme, the stalk `O_η` is the localization of `O_y`, via the
specialization map, at the prime ideal of the germs vanishing at `η`. This is infrastructure (no statement of the
paper), used in Ch. II (`Ch2/GradedIdeal.lean`, `Ch2/AscendingChain.lean`), Ch. III (`Ch3/Stability.lean`) and Ch. IV.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace Hironaka

section Generization

variable {Y : Scheme.{u}}

/-- For a generization `η ⤳ y`, the stalk `O_η` is the localization of `O_y` (via the
specialization map) at the prime `{a | a(η) = 0}`. -/
theorem isLocalization_stalkSpecializes_of_specializes {η y : Y} (h : η ⤳ y) :
    letI := (Y.presheaf.stalkSpecializes h).hom.toAlgebra
    IsLocalization.AtPrime (Y.presheaf.stalk η) ((IsLocalRing.maximalIdeal
      (Y.presheaf.stalk η)).comap (Y.presheaf.stalkSpecializes h).hom) := by
  let := (Y.presheaf.stalkSpecializes h).hom.toAlgebra
  obtain ⟨_, ⟨V, hV, rfl⟩, hyV, -⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ y) isOpen_univ
  have hηV : η ∈ V := h.mem_open V.isOpen hyV
  let : Algebra Γ(Y, V) (Y.presheaf.stalk y) :=
    TopCat.Presheaf.algebra_section_stalk Y.presheaf ⟨y, hyV⟩
  let : Algebra Γ(Y, V) (Y.presheaf.stalk η) :=
    TopCat.Presheaf.algebra_section_stalk Y.presheaf ⟨η, hηV⟩
  have hy := hV.isLocalization_stalk ⟨y, hyV⟩
  have hη := hV.isLocalization_stalk ⟨η, hηV⟩
  have hsp : ∀ s : Γ(Y, V), (Y.presheaf.stalkSpecializes h).hom
      (algebraMap Γ(Y, V) (Y.presheaf.stalk y) s) = algebraMap Γ(Y, V) (Y.presheaf.stalk η) s :=
    fun s => TopCat.Presheaf.germ_stalkSpecializes_apply Y.presheaf hyV h s
  have : IsScalarTower Γ(Y, V) (Y.presheaf.stalk y) (Y.presheaf.stalk η) :=
    IsScalarTower.of_algebraMap_eq fun s => (hsp s).symm
  set py := (hV.primeIdealOf ⟨y, hyV⟩).asIdeal
  set pη := (hV.primeIdealOf ⟨η, hηV⟩).asIdeal
  -- `pη ⊆ py`.
  have hle : py.primeCompl ≤ pη.primeCompl := by
    intro s hs
    have hu : IsUnit (algebraMap Γ(Y, V) (Y.presheaf.stalk y) s) :=
      (IsLocalization.AtPrime.isUnit_to_map_iff _ py s).mpr hs
    have hu' := hu.map (Y.presheaf.stalkSpecializes h).hom
    rw [hsp] at hu'
    exact (IsLocalization.AtPrime.isUnit_to_map_iff _ pη s).mp hu'
  have := IsLocalization.isLocalization_of_submonoid_le (Y.presheaf.stalk y)
    (Y.presheaf.stalk η) py.primeCompl pη.primeCompl hle
  refine IsLocalization.isLocalization_of_is_exists_mul_mem (Y.presheaf.stalk η)
    (pη.primeCompl.map (algebraMap Γ(Y, V) (Y.presheaf.stalk y))) _ ?_ ?_
  · rintro _ ⟨s, hs, rfl⟩
    show (Y.presheaf.stalkSpecializes h).hom _ ∉ IsLocalRing.maximalIdeal _
    rw [hsp, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, not_not]
    exact (IsLocalization.AtPrime.isUnit_to_map_iff _ pη s).mpr hs
  · rintro ⟨z, hz⟩
    obtain ⟨⟨a, b⟩, hab⟩ := IsLocalization.surj py.primeCompl z
    refine ⟨algebraMap Γ(Y, V) (Y.presheaf.stalk y) b, a, ?_, ?_⟩
    · -- `a ∉ pη`: `a(η) = z(η) b(η)` is a unit.
      show a ∈ pη.primeCompl
      rw [← IsLocalization.AtPrime.isUnit_to_map_iff (Y.presheaf.stalk η) pη a, ← hsp]
      dsimp only at hab
      rw [← hab, map_mul]
      refine IsUnit.mul ?_ ?_
      · have : (Y.presheaf.stalkSpecializes h).hom z ∉ IsLocalRing.maximalIdeal _ := hz
        rwa [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, not_not] at this
      · exact ((IsLocalization.AtPrime.isUnit_to_map_iff _ py b).mpr b.2).map _
    · dsimp only at hab ⊢
      rw [mul_comm, hab]

end Generization

end Hironaka
