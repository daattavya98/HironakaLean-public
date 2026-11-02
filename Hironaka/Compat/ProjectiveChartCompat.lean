/-
Copyright (c) 2026 Daattavya Aggarwal, Minhyong Kim, Oisin Kim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daattavya Aggarwal, Minhyong Kim, Oisin Kim
-/
module

public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
public import Hironaka.Compat.HomogeneousLocalizationEmbedding

/-!
# Agreement of two chart maps on the overlap (gluing device for the p. 132 lemma)

Let `𝒜` and `ℬ` be graded rings (domains), `s, t ∈ A₁` and `f, f' ∈ B₁` of degree one, and
`ρ : A_(s) → B_(f)`, `ρ' : A_(t) → B_(f')` ring homomorphisms.  The chart maps
`Spec B_(f) → Spec A_(s) → Proj A` and `Spec B_(f') → Spec A_(t) → Proj A` are to be glued along the overlap
`D₊(f) ∩ D₊(f') = D₊(f f') = Spec B_(f f')`.  This file shows that the two composites `Spec B_(f f') → Proj A` agree,
provided
* `ρ` and `ρ'` are compatible with the embeddings of `A_(s)`, `B_(f)`, … into a common field `K`
  (`awayEmb`: `x / s ^ n ↦ x / s ^ n` in `K`), and
* the element `t / s` becomes a unit in `B_(f f')` (it is mapped into `B_(f f')` by `ρ`).

The proof produces a ring map `φ : A_(s t) → B_(f f')` by the universal property of `A_(s t) = A_(s)[s / t]`
(`HomogeneousLocalization.Away.isLocalization_mul`) and shows that both chart maps factor through `Spec φ` followed by
`awayι (s t)` (`Proj.SpecMap_awayMap_awayι`).

Used in `Hironaka/Compat/BlowupProjectiveMaps.lean` (step L1c of `MonoidalTransformation.isProjectiveOver`, the unproved,
uncited step of the Corollary on p. 132).  Nothing here is printed.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory HomogeneousLocalization

namespace Hironaka

universe u

namespace ProjChart

variable {σ : Type*} {A : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A] {𝒜 : ℕ → σ} [GradedRing 𝒜]
  {τ : Type*} {B : Type u} [CommRing B] [SetLike τ B] [AddSubgroupClass τ B] {ℬ : ℕ → τ} [GradedRing ℬ]
  {K : Type*} [Field K] {jA : A →+* K} {jB : B →+* K}

/-- **Ring-level agreement on the overlap.**  There is `φ : A_(s t) → B_(f f')` whose restrictions along
`A_(s) → A_(s t)` and `A_(t) → A_(s t)` are `ρ` and `ρ'` followed by `B_(f) → B_(f f')`, `B_(f') → B_(f f')`. -/
theorem exists_overlap_ringHom [IsDomain B] (hjB : Function.Injective jB) {s t : A} (hs : s ∈ 𝒜 1)
    (ht : t ∈ 𝒜 1) {f f' : B} (hf : f ∈ ℬ 1) (hf' : f' ∈ ℬ 1) (hs0 : jA s ≠ 0) (ht0 : jA t ≠ 0)
    (hf0 : jB f ≠ 0) (hf'0 : jB f' ≠ 0) (hw0 : jB (f * f') ≠ 0)
    (ρ : Away 𝒜 s →+* Away ℬ f) (ρ' : Away 𝒜 t →+* Away ℬ f')
    (hρ : ∀ z, awayEmb ℬ jB f hf0 (ρ z) = awayEmb 𝒜 jA s hs0 z)
    (hρ' : ∀ z, awayEmb ℬ jB f' hf'0 (ρ' z) = awayEmb 𝒜 jA t ht0 z)
    (hinv : ∃ z : Away ℬ (f * f'), awayEmb ℬ jB (f * f') hw0 z * (jA t / jA s) = 1) :
    ∃ φ : Away 𝒜 (s * t) →+* Away ℬ (f * f'),
      φ.comp (awayMap 𝒜 ht rfl) = (awayMap ℬ hf' rfl).comp ρ ∧
      φ.comp (awayMap 𝒜 hs (mul_comm s t)) =
        (awayMap ℬ hf (mul_comm f f')).comp ρ' := by
  have hst0 : jA (s * t) ≠ 0 := by rw [map_mul]; exact mul_ne_zero hs0 ht0
  have hEinj := awayEmb_injective (𝒜 := ℬ) hjB hw0
  let ψ1 : Away 𝒜 s →+* Away ℬ (f * f') := (awayMap ℬ hf' rfl).comp ρ
  -- the key identity: `awayEmb ∘ ψ1 = awayEmb`
  have hψ1 : ∀ z, awayEmb ℬ jB (f * f') hw0 (ψ1 z) = awayEmb 𝒜 jA s hs0 z := fun z => by
    rw [RingHom.comp_apply, awayEmb_awayMap hf hf' rfl hf0 hw0, hρ]
  let _ : Algebra (Away 𝒜 s) (Away 𝒜 (s * t)) := (awayMap 𝒜 ht (rfl : s * t = s * t)).toAlgebra
  have hloc : IsLocalization.Away (Away.isLocalizationElem (𝒜 := 𝒜) hs ht) (Away 𝒜 (s * t)) :=
    Away.isLocalization_mul hs ht rfl one_ne_zero
  have hunit : IsUnit (ψ1 (Away.isLocalizationElem (𝒜 := 𝒜) hs ht)) := by
    obtain ⟨z, hz⟩ := hinv
    refine isUnit_iff_exists_inv.mpr ⟨z, hEinj ?_⟩
    rw [map_mul, hψ1, map_one, Away.isLocalizationElem, awayEmb_mk hs0, pow_one, pow_one]
    rw [mul_comm]; exact hz
  let φ : Away 𝒜 (s * t) →+* Away ℬ (f * f') := IsLocalization.Away.lift _ hunit
  have hφ1 : φ.comp (awayMap 𝒜 ht (rfl : s * t = s * t)) = ψ1 :=
    IsLocalization.lift_comp (M := Submonoid.powers (Away.isLocalizationElem (𝒜 := 𝒜) hs ht)) _
  -- `awayEmb ∘ φ = awayEmb`
  have hφE : ∀ z, awayEmb ℬ jB (f * f') hw0 (φ z) = awayEmb 𝒜 jA (s * t) hst0 z := by
    have : (awayEmb ℬ jB (f * f') hw0).comp φ = awayEmb 𝒜 jA (s * t) hst0 := by
      refine IsLocalization.ringHom_ext (Submonoid.powers (Away.isLocalizationElem (𝒜 := 𝒜) hs ht)) ?_
      ext z
      have h1 : (φ.comp (algebraMap _ _)) z = ψ1 z := RingHom.congr_fun hφ1 z
      simp only [RingHom.comp_apply, RingHom.algebraMap_toAlgebra] at h1 ⊢
      rw [h1, hψ1, awayEmb_awayMap hs ht rfl hs0 hst0]
    exact fun z => RingHom.congr_fun this z
  refine ⟨φ, hφ1, ?_⟩
  refine RingHom.ext fun z => hEinj ?_
  have e1 := hφE (awayMap 𝒜 hs (mul_comm s t) z)
  simp only [RingHom.comp_apply]
  rw [e1, awayEmb_awayMap ht hs (mul_comm s t) ht0 hst0, awayEmb_awayMap hf' hf (mul_comm f f') hf'0 hw0,
    hρ']

/-- **The two chart maps agree on `Spec B_(f f')`.** -/
theorem specMap_comp_awayι_eq [IsDomain B] (hjB : Function.Injective jB) {s t : A} (hs : s ∈ 𝒜 1)
    (ht : t ∈ 𝒜 1) {f f' : B} (hf : f ∈ ℬ 1) (hf' : f' ∈ ℬ 1) (hs0 : jA s ≠ 0) (ht0 : jA t ≠ 0)
    (hf0 : jB f ≠ 0) (hf'0 : jB f' ≠ 0) (hw0 : jB (f * f') ≠ 0)
    (ρ : Away 𝒜 s →+* Away ℬ f) (ρ' : Away 𝒜 t →+* Away ℬ f')
    (hρ : ∀ z, awayEmb ℬ jB f hf0 (ρ z) = awayEmb 𝒜 jA s hs0 z)
    (hρ' : ∀ z, awayEmb ℬ jB f' hf'0 (ρ' z) = awayEmb 𝒜 jA t ht0 z)
    (hinv : ∃ z : Away ℬ (f * f'), awayEmb ℬ jB (f * f') hw0 z * (jA t / jA s) = 1) :
    Spec.map (CommRingCat.ofHom ((awayMap ℬ hf' rfl).comp ρ)) ≫ Proj.awayι 𝒜 s hs one_pos =
      Spec.map (CommRingCat.ofHom ((awayMap ℬ hf (mul_comm f f')).comp ρ')) ≫
        Proj.awayι 𝒜 t ht one_pos := by
  obtain ⟨φ, h1, h2⟩ := exists_overlap_ringHom hjB hs ht hf hf' hs0 ht0 hf0 hf'0 hw0 ρ ρ' hρ hρ' hinv
  rw [← h1, ← h2]
  simp only [CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc]
  rw [Proj.SpecMap_awayMap_awayι 𝒜 hs one_pos ht rfl,
    Proj.SpecMap_awayMap_awayι 𝒜 ht one_pos hs (mul_comm s t)]

/-- **Gluing condition for the chart maps**: on the overlap `D₊(f) ∩ D₊(f')` of the two charts of `Proj B`, the two
maps to `Proj A` agree. -/
theorem pullback_fst_comp_eq [IsDomain B] (hjB : Function.Injective jB) {s t : A} (hs : s ∈ 𝒜 1)
    (ht : t ∈ 𝒜 1) {f f' : B} (hf : f ∈ ℬ 1) (hf' : f' ∈ ℬ 1) (hs0 : jA s ≠ 0) (ht0 : jA t ≠ 0)
    (hf0 : jB f ≠ 0) (hf'0 : jB f' ≠ 0) (hw0 : jB (f * f') ≠ 0)
    (ρ : Away 𝒜 s →+* Away ℬ f) (ρ' : Away 𝒜 t →+* Away ℬ f')
    (hρ : ∀ z, awayEmb ℬ jB f hf0 (ρ z) = awayEmb 𝒜 jA s hs0 z)
    (hρ' : ∀ z, awayEmb ℬ jB f' hf'0 (ρ' z) = awayEmb 𝒜 jA t ht0 z)
    (hinv : ∃ z : Away ℬ (f * f'), awayEmb ℬ jB (f * f') hw0 z * (jA t / jA s) = 1) :
    Limits.pullback.fst (Proj.awayι ℬ f hf one_pos) (Proj.awayι ℬ f' hf' one_pos) ≫
        (Spec.map (CommRingCat.ofHom ρ) ≫ Proj.awayι 𝒜 s hs one_pos) =
      Limits.pullback.snd (Proj.awayι ℬ f hf one_pos) (Proj.awayι ℬ f' hf' one_pos) ≫
        (Spec.map (CommRingCat.ofHom ρ') ≫ Proj.awayι 𝒜 t ht one_pos) := by
  have e := specMap_comp_awayι_eq hjB hs ht hf hf' hs0 ht0 hf0 hf'0 hw0 ρ ρ' hρ hρ' hinv
  rw [← Proj.pullbackAwayιIso_hom_SpecMap_awayMap_left ℬ hf one_pos hf' one_pos
      (rfl : f * f' = f * f'),
    ← Proj.pullbackAwayιIso_hom_SpecMap_awayMap_right ℬ hf one_pos hf' one_pos
      (rfl : f * f' = f * f')]
  simp only [Category.assoc]
  rw [← Category.assoc (Spec.map (CommRingCat.ofHom (awayMap ℬ hf' rfl))),
    ← Category.assoc (Spec.map (CommRingCat.ofHom (awayMap ℬ hf _)))]
  simp only [← Spec.map_comp]
  convert congrArg (fun m => (Proj.pullbackAwayιIso ℬ hf one_pos hf' one_pos (rfl : f * f' = f * f')).hom ≫ m) e
    using 2

end ProjChart

end Hironaka
