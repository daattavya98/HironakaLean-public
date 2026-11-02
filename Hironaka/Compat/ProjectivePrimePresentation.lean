/-
Copyright (c) 2026 Daattavya Aggarwal, Minhyong Kim, Oisin Kim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daattavya Aggarwal, Minhyong Kim, Oisin Kim
-/
module

public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Functor
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Scheme
public import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Maps
public import Architect
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import Hironaka.Compat.ProjectiveVocabulary
public import Hironaka.Compat.ProjectiveIdealForms

/-!
# An integral projective scheme has a presentation by a homogeneous prime ideal (step R0 of the p. 132 lemma)

Step R0 of the proof of `MonoidalTransformation.isProjectiveOver` (`Hironaka/Compat/BlowupProjective.lean`, the unproved,
uncited step of the Corollary on p. 132).  p. 132 calls `X` projective if it is `Proj(H)` with `H = B[T₀, …, T_{n-1}] ⧸ 𝔞`
for a homogeneous ideal `𝔞`; such an `H` need not be a domain even when `Proj H` is integral (`H = B[x, y]/(xy, y²)`: the
element `y` is killed by a power of the irrelevant ideal).  This file replaces `𝔞` by the homogeneous prime `𝔭` of the
generic point: `Proj(B[T]/𝔭) → Proj(B[T]/𝔞)` is an isomorphism over `Spec B` when `Proj(B[T]/𝔞)` is integral.

Nothing here is printed: it is part of the proof of a gap filled.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory MvPolynomial

namespace Hironaka

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

set_option linter.unusedSectionVars false

section Construction

variable {B : Type u} [Field B] {n : ℕ} (𝔞 : HomogeneousIdeal (homogeneousSubmodule (Fin n) B))

/-- The quotient map `B[T] → B[T]/𝔞` as a graded ring homomorphism. -/
noncomputable def mkGraded :
    (homogeneousSubmodule (Fin n) B) →+*ᵍ (quotientGrading 𝔞) :=
  ⟨Ideal.Quotient.mk 𝔞.toIdeal, fun hx => mk_mem_quotientGrading 𝔞 hx⟩

variable [IsIntegral (Proj (quotientGrading 𝔞))]

/-- The homogeneous prime ideal of `B[T]/𝔞` of the generic point of `Proj (B[T]/𝔞)`. -/
noncomputable def genericIdeal : HomogeneousIdeal (quotientGrading 𝔞) :=
  (genericPoint (Proj (quotientGrading 𝔞))).asHomogeneousIdeal

instance genericIdeal_isPrime : (genericIdeal 𝔞).toIdeal.IsPrime :=
  (genericPoint (Proj (quotientGrading 𝔞))).isPrime

/-- The generic point is contained in every point: `𝔮 ≤ y` for every `y ∈ Proj (B[T]/𝔞)`. -/
theorem genericIdeal_le (y : Proj (quotientGrading 𝔞)) : genericIdeal 𝔞 ≤ y.asHomogeneousIdeal := by
  have h : genericPoint (Proj (quotientGrading 𝔞)) ⤳ y := genericPoint_specializes y
  rw [specializes_iff_mem_closure] at h
  exact (ProjectiveSpectrum.le_iff_mem_closure (quotientGrading 𝔞) (genericPoint (Proj (quotientGrading 𝔞))) y).mpr h

/-- The homogeneous prime `𝔭` of `B[T]` of the generic point of `Proj (B[T]/𝔞)`. -/
noncomputable def primeOf : HomogeneousIdeal (homogeneousSubmodule (Fin n) B) :=
  (genericIdeal 𝔞).comap (mkGraded 𝔞)

instance primeOf_isPrime : (primeOf 𝔞).toIdeal.IsPrime :=
  HomogeneousIdeal.isPrime_comap (mkGraded 𝔞) (J := genericIdeal 𝔞)

theorem le_primeOf : 𝔞 ≤ primeOf 𝔞 := by
  intro a ha
  show Ideal.Quotient.mk 𝔞.toIdeal a ∈ (genericIdeal 𝔞).toIdeal
  rw [Ideal.Quotient.eq_zero_iff_mem.mpr ha]
  exact zero_mem _

/-- The quotient map `B[T]/𝔞 → B[T]/𝔭`. -/
noncomputable def qRing : MvPolynomial (Fin n) B ⧸ 𝔞.toIdeal →+* MvPolynomial (Fin n) B ⧸ (primeOf 𝔞).toIdeal :=
  Ideal.Quotient.lift 𝔞.toIdeal (Ideal.Quotient.mk (primeOf 𝔞).toIdeal) fun _ ha =>
    Ideal.Quotient.eq_zero_iff_mem.mpr (le_primeOf 𝔞 ha)

theorem qRing_mk (a : MvPolynomial (Fin n) B) :
    qRing 𝔞 (Ideal.Quotient.mk 𝔞.toIdeal a) = Ideal.Quotient.mk (primeOf 𝔞).toIdeal a := rfl

theorem qRing_surjective : Function.Surjective (qRing 𝔞) := by
  intro x
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  exact ⟨Ideal.Quotient.mk 𝔞.toIdeal a, rfl⟩

/-- `x ↦ 0` under `B[T]/𝔞 → B[T]/𝔭` exactly when `x ∈ 𝔮`. -/
theorem qRing_eq_zero_iff (x : MvPolynomial (Fin n) B ⧸ 𝔞.toIdeal) :
    qRing 𝔞 x = 0 ↔ x ∈ (genericIdeal 𝔞).toIdeal := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [qRing_mk, Ideal.Quotient.eq_zero_iff_mem]
  rfl

/-- The quotient map `B[T]/𝔞 → B[T]/𝔭` as a graded ring homomorphism. -/
noncomputable def qGraded : quotientGrading 𝔞 →+*ᵍ quotientGrading (primeOf 𝔞) :=
  ⟨qRing 𝔞, fun {d x} hx => by
    obtain ⟨a, ha, hax⟩ := hx
    have : x = Ideal.Quotient.mk 𝔞.toIdeal a := hax.symm
    rw [this]
    exact mk_mem_quotientGrading _ ha⟩

theorem qGraded_apply (x : MvPolynomial (Fin n) B ⧸ 𝔞.toIdeal) : qGraded 𝔞 x = qRing 𝔞 x := rfl

/-- Every element of `H_𝔭` of degree `d` is the image of an element of `H_𝔞` of degree `d`. -/
theorem exists_qRing_eq {d : ℕ} {z : MvPolynomial (Fin n) B ⧸ (primeOf 𝔞).toIdeal}
    (hz : z ∈ quotientGrading (primeOf 𝔞) d) : ∃ y ∈ quotientGrading 𝔞 d, qRing 𝔞 y = z := by
  obtain ⟨a, ha, haz⟩ := hz
  exact ⟨Ideal.Quotient.mk 𝔞.toIdeal a, mk_mem_quotientGrading _ ha, haz⟩

theorem irrelevant_le_map_qGraded : (HomogeneousIdeal.irrelevant (quotientGrading (primeOf 𝔞))) ≤
    (HomogeneousIdeal.irrelevant (quotientGrading 𝔞)).map (qGraded 𝔞) := by
  classical
  intro x hx
  rw [← DirectSum.sum_support_decompose (quotientGrading (primeOf 𝔞)) x]
  refine Ideal.sum_mem _ fun d hd => ?_
  have hd0 : d ≠ 0 := by
    rintro rfl
    have h := (HomogeneousIdeal.mem_irrelevant_iff _ _).mp hx
    exact (DFinsupp.mem_support_iff.mp hd) (Subtype.ext (by simpa [GradedRing.proj_apply] using h))
  obtain ⟨y, hy, hyx⟩ := exists_qRing_eq 𝔞
    (DirectSum.decompose (quotientGrading (primeOf 𝔞)) x d).2
  have hy' : y ∈ HomogeneousIdeal.irrelevant (quotientGrading 𝔞) :=
    HomogeneousIdeal.mem_irrelevant_of_mem _ (Nat.pos_of_ne_zero hd0) hy
  have : ((DirectSum.decompose (quotientGrading (primeOf 𝔞)) x d : quotientGrading (primeOf 𝔞) d) :
      MvPolynomial (Fin n) B ⧸ (primeOf 𝔞).toIdeal) =
      qGraded 𝔞 y := hyx.symm
  rw [this]
  exact Ideal.mem_map_of_mem _ hy'

instance isDomain_primeOf : IsDomain (MvPolynomial (Fin n) B ⧸ (primeOf 𝔞).toIdeal) :=
  Ideal.Quotient.isDomain _

theorem qGraded_mem_irrelevant {x : MvPolynomial (Fin n) B ⧸ 𝔞.toIdeal}
    (hx : x ∈ HomogeneousIdeal.irrelevant (quotientGrading 𝔞)) :
    qGraded 𝔞 x ∈ HomogeneousIdeal.irrelevant (quotientGrading (primeOf 𝔞)) := by
  classical
  rw [← DirectSum.sum_support_decompose (quotientGrading 𝔞) x, map_sum]
  refine Ideal.sum_mem _ fun d hd => ?_
  have hd0 : d ≠ 0 := by
    rintro rfl
    have h := (HomogeneousIdeal.mem_irrelevant_iff _ _).mp hx
    exact (DFinsupp.mem_support_iff.mp hd) (Subtype.ext (by simpa [GradedRing.proj_apply] using h))
  exact HomogeneousIdeal.mem_irrelevant_of_mem _ (Nat.pos_of_ne_zero hd0)
    ((qGraded 𝔞).map_mem (DirectSum.decompose (quotientGrading 𝔞) x d).2)

/-- The morphism `Proj (B[T]/𝔭) → Proj (B[T]/𝔞)` induced by the quotient map. -/
noncomputable def mapProj : Proj (quotientGrading (primeOf 𝔞)) ⟶ Proj (quotientGrading 𝔞) :=
  Proj.map (qGraded 𝔞) (irrelevant_le_map_qGraded 𝔞)

/-- The point `0` of `Proj (B[T]/𝔭)`; it maps to the generic point of `Proj (B[T]/𝔞)`. -/
noncomputable def zeroPoint : ProjectiveSpectrum (quotientGrading (primeOf 𝔞)) where
  asHomogeneousIdeal := ⊥
  isPrime := by rw [HomogeneousIdeal.toIdeal_bot]; exact inferInstance
  not_irrelevant_le := by
    intro h
    have hnle := (genericPoint (Proj (quotientGrading 𝔞))).not_irrelevant_le
    obtain ⟨x, hx, hxq⟩ : ∃ x ∈ HomogeneousIdeal.irrelevant (quotientGrading 𝔞),
        x ∉ (genericPoint (Proj (quotientGrading 𝔞))).asHomogeneousIdeal := by
      by_contra hcon
      apply hnle
      intro x hx
      by_contra hxq
      exact hcon ⟨x, hx, hxq⟩
    have h1 := h (qGraded_mem_irrelevant 𝔞 hx)
    have h2 : qGraded 𝔞 x = 0 := (Submodule.mem_bot _).mp h1
    exact hxq ((qRing_eq_zero_iff 𝔞 x).mp h2)

theorem mapProj_zeroPoint :
    mapProj 𝔞 (zeroPoint 𝔞) = genericPoint (Proj (quotientGrading 𝔞)) := by
  refine ProjectiveSpectrum.ext (HomogeneousIdeal.ext (Ideal.ext fun x => ?_))
  show qGraded 𝔞 x ∈ (⊥ : HomogeneousIdeal (quotientGrading (primeOf 𝔞))).toIdeal ↔ x ∈ (genericIdeal 𝔞).toIdeal
  rw [HomogeneousIdeal.toIdeal_bot, Ideal.mem_bot]
  exact qRing_eq_zero_iff 𝔞 x

omit [IsIntegral (Proj (quotientGrading 𝔞))] in
/-- The irrelevant ideal of `H = B[T]/𝔞` is spanned by the coordinates `uᵢ`. -/
theorem irrelevant_le_span_var :
    (HomogeneousIdeal.irrelevant (quotientGrading 𝔞)).toIdeal ≤
      Ideal.span (Set.range (quotientGrading.var 𝔞)) := by
  classical
  set 𝒬 := quotientGrading 𝔞
  intro x hx
  convert_to x - GradedRing.projZeroRingHom 𝒬 x ∈ _
  · rw [GradedRing.projZeroRingHom_apply, ← GradedRing.proj_apply,
      (HomogeneousIdeal.mem_irrelevant_iff _ _).mp hx, sub_zero]
  clear hx
  have := (eq_iff_iff.mp congr(x ∈ $(quotientGrading.adjoin_range_var 𝔞))).mpr trivial
  induction this using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    rw [GradedRing.projZeroRingHom_apply, DirectSum.decompose_of_mem_ne 𝒬
      (quotientGrading.var_mem 𝔞 i) one_ne_zero, sub_zero]
    exact Ideal.subset_span ⟨_, rfl⟩
  | algebraMap r =>
    convert! zero_mem (Ideal.span _)
    rw [sub_eq_zero]
    exact (DirectSum.decompose_of_mem_same 𝒬 r.2).symm
  | add x y hx hy _ _ =>
    rw [map_add, add_sub_add_comm]
    exact add_mem ‹_› ‹_›
  | mul x y hx hy hx' hy' =>
    convert!
      add_mem (Ideal.mul_mem_left _ x hy')
        (Ideal.mul_mem_right (GradedRing.projZeroRingHom 𝒬 y) _ hx') using 1
    rw [map_mul]
    ring

/-- The cover of `Proj (B[T]/𝔞)` by the standard charts `D₊(uᵢ)`. -/
noncomputable def varCover : (Proj (quotientGrading 𝔞)).OpenCover :=
  (Proj.affineOpenCoverOfIrrelevantLESpan (quotientGrading 𝔞) (quotientGrading.var 𝔞) (m := fun _ => 1)
    (quotientGrading.var_mem 𝔞) (fun _ => one_pos) (irrelevant_le_span_var 𝔞)).openCover

theorem awayMap_q_surjective (b : Fin n) :
    Function.Surjective (HomogeneousLocalization.Away.map (qGraded 𝔞) (quotientGrading.var 𝔞 b)) := by
  intro z
  obtain ⟨d, y, hy, rfl⟩ := HomogeneousLocalization.Away.mk_surjective (quotientGrading (primeOf 𝔞))
    ((qGraded 𝔞).map_mem (quotientGrading.var_mem 𝔞 b)) z
  obtain ⟨x, hx, hxy⟩ := exists_qRing_eq 𝔞 (by simpa using hy)
  refine ⟨HomogeneousLocalization.Away.mk (quotientGrading 𝔞) (quotientGrading.var_mem 𝔞 b) d x
    (by simpa using hx), ?_⟩
  rw [HomogeneousLocalization.Away.map_mk]
  congr 1

set_option maxHeartbeats 400000 in
/-- Over the chart `D₊(uᵢ)`, `mapProj` is a closed immersion: it is `Spec` of the surjection `H_(uᵢ) → H̄_(ūᵢ)`. -/
theorem isClosedImmersion_pullbackHom (b : Fin n) :
    IsClosedImmersion ((varCover 𝔞).pullbackHom (mapProj 𝔞) b) := by
  have hq := (qGraded 𝔞).map_mem (quotientGrading.var_mem 𝔞 b)
  have hirr := irrelevant_le_map_qGraded 𝔞
  have H : Proj.awayι (quotientGrading (primeOf 𝔞)) (qGraded 𝔞 (quotientGrading.var 𝔞 b)) hq one_pos ≫
      mapProj 𝔞 = Spec.map (CommRingCat.ofHom (HomogeneousLocalization.Away.map (qGraded 𝔞)
        (quotientGrading.var 𝔞 b))) ≫ Proj.awayι (quotientGrading 𝔞) (quotientGrading.var 𝔞 b)
          (quotientGrading.var_mem 𝔞 b) one_pos :=
    Proj.awayι_comp_map (qGraded 𝔞) hirr one_pos _ (quotientGrading.var_mem 𝔞 b)
  have H' : mapProj 𝔞 ⁻¹ᵁ (Proj.awayι (quotientGrading 𝔞) (quotientGrading.var 𝔞 b)
      (quotientGrading.var_mem 𝔞 b) one_pos).opensRange =
      (Proj.awayι (quotientGrading (primeOf 𝔞)) (qGraded 𝔞 (quotientGrading.var 𝔞 b)) hq one_pos).opensRange := by
    rw [Proj.opensRange_awayι, Proj.opensRange_awayι]
    rfl
  have hpb := (IsOpenImmersion.isPullback _ _ _ _ H H').flip
  have hφ : IsClosedImmersion (Spec.map (CommRingCat.ofHom (HomogeneousLocalization.Away.map
      (qGraded 𝔞) (quotientGrading.var 𝔞 b)))) :=
    IsClosedImmersion.spec_of_surjective _ (awayMap_q_surjective 𝔞 b)
  have e : hpb.isoPullback.hom ≫ Limits.pullback.snd (mapProj 𝔞) (Proj.awayι (quotientGrading 𝔞)
      (quotientGrading.var 𝔞 b) (quotientGrading.var_mem 𝔞 b) one_pos) = Spec.map (CommRingCat.ofHom
        (HomogeneousLocalization.Away.map (qGraded 𝔞) (quotientGrading.var 𝔞 b))) :=
    hpb.isoPullback_hom_snd
  show IsClosedImmersion (Limits.pullback.snd (mapProj 𝔞) (Proj.awayι (quotientGrading 𝔞)
      (quotientGrading.var 𝔞 b) (quotientGrading.var_mem 𝔞 b) one_pos))
  have : Limits.pullback.snd (mapProj 𝔞) (Proj.awayι (quotientGrading 𝔞)
      (quotientGrading.var 𝔞 b) (quotientGrading.var_mem 𝔞 b) one_pos) =
      hpb.isoPullback.inv ≫ Spec.map (CommRingCat.ofHom
        (HomogeneousLocalization.Away.map (qGraded 𝔞) (quotientGrading.var 𝔞 b))) :=
    (Iso.eq_inv_comp hpb.isoPullback).mpr e
  rw [this]
  infer_instance

theorem isClosedImmersion_mapProj : IsClosedImmersion (mapProj 𝔞) := by
  rw [IsZariskiLocalAtTarget.iff_of_openCover (P := @IsClosedImmersion) (varCover 𝔞)]
  exact isClosedImmersion_pullbackHom 𝔞

instance isDominant_mapProj : IsDominant (mapProj 𝔞) := by
  refine ⟨?_⟩
  have h : closure {genericPoint (Proj (quotientGrading 𝔞))} = Set.univ :=
    (genericPoint_spec (Proj (quotientGrading 𝔞))).def
  have hmem : genericPoint (Proj (quotientGrading 𝔞)) ∈ Set.range (mapProj 𝔞) :=
    ⟨zeroPoint 𝔞, mapProj_zeroPoint 𝔞⟩
  intro x
  have : x ∈ closure {genericPoint (Proj (quotientGrading 𝔞))} := by rw [h]; trivial
  exact closure_mono (Set.singleton_subset_iff.mpr hmem) this

/-- **`Proj (B[T]/𝔭) ≅ Proj (B[T]/𝔞)`** when the latter is integral: `mapProj` is a closed immersion, surjective since it
hits the generic point, and the target is reduced. -/
theorem isIso_mapProj : IsIso (mapProj 𝔞) := by
  have := isClosedImmersion_mapProj 𝔞
  have : Surjective (mapProj 𝔞) :=
    surjective_of_isDominant_of_isClosed_range _ (mapProj 𝔞).isClosedEmbedding.isClosed_range
  exact isIso_of_isClosedImmersion_of_surjective (mapProj 𝔞)

/-- The cover of `Proj (B[T]/𝔭)` by the charts `D₊(ūᵢ)`. -/
noncomputable def coverZ : (Proj (quotientGrading (primeOf 𝔞))).OpenCover :=
  (Proj.affineOpenCoverOfIrrelevantLESpan (quotientGrading (primeOf 𝔞))
    (fun b => qGraded 𝔞 (quotientGrading.var 𝔞 b)) (m := fun _ => 1)
    (fun b => (qGraded 𝔞).map_mem (quotientGrading.var_mem 𝔞 b)) (fun _ => one_pos)
    (irrelevant_le_span_var (primeOf 𝔞))).openCover

omit [IsIntegral (Proj (quotientGrading 𝔞))] in
/-- A graded ring homomorphism maps the image of `A₀` in `A_(f)` to the image of `B₀` in `B_(g f)`. -/
theorem away_map_algebraMap {ι A B' σ τ : Type*} [AddCommMonoid ι] [DecidableEq ι] [CommRing A]
    [CommRing B'] [SetLike σ A] [SetLike τ B'] [AddSubgroupClass σ A] [AddSubgroupClass τ B']
    {𝒜 : ι → σ} {ℬ : ι → τ} [GradedRing 𝒜] [GradedRing ℬ] (g : 𝒜 →+*ᵍ ℬ) (f : A) (c : 𝒜 0) :
    HomogeneousLocalization.Away.map g f (algebraMap (𝒜 0) (HomogeneousLocalization.Away 𝒜 f) c) =
      algebraMap (ℬ 0) (HomogeneousLocalization.Away ℬ (g f)) ⟨g c, g.map_mem c.2⟩ := by
  apply HomogeneousLocalization.val_injective
  change (HomogeneousLocalization.map g _ (HomogeneousLocalization.mk ⟨0, c, 1, one_mem _⟩)).val =
    (HomogeneousLocalization.mk ⟨0, ⟨g c, g.map_mem c.2⟩, 1, one_mem _⟩).val
  rw [HomogeneousLocalization.map_mk]
  simp only [HomogeneousLocalization.val_mk]
  congr 1
  ext
  simp

set_option maxHeartbeats 400000 in
/-- The structure maps are compatible with the chart maps: `B → H̄₀ → H̄_(ūᵢ)` equals `B → H₀ → H_(uᵢ) → H̄_(ūᵢ)`. -/
theorem ring_q (b : Fin n) :
    CommRingCat.ofHom (algebraMap B (quotientGrading 𝔞 0)) ≫
        CommRingCat.ofHom (algebraMap (quotientGrading 𝔞 0)
          (HomogeneousLocalization.Away (quotientGrading 𝔞) (quotientGrading.var 𝔞 b))) ≫
        CommRingCat.ofHom (HomogeneousLocalization.Away.map (qGraded 𝔞) (quotientGrading.var 𝔞 b)) =
      CommRingCat.ofHom (algebraMap B (quotientGrading (primeOf 𝔞) 0)) ≫
        CommRingCat.ofHom (algebraMap (quotientGrading (primeOf 𝔞) 0)
          (HomogeneousLocalization.Away (quotientGrading (primeOf 𝔞)) (qGraded 𝔞 (quotientGrading.var 𝔞 b)))) := by
  refine CommRingCat.hom_ext (RingHom.ext fun b' => ?_)
  show HomogeneousLocalization.Away.map (qGraded 𝔞) (quotientGrading.var 𝔞 b)
    (algebraMap (quotientGrading 𝔞 0) _ (algebraMap B (quotientGrading 𝔞 0) b')) =
    algebraMap (quotientGrading (primeOf 𝔞) 0) _ (algebraMap B (quotientGrading (primeOf 𝔞) 0) b')
  rw [away_map_algebraMap]
  congr 1

set_option maxHeartbeats 400000 in
/-- `mapProj` is compatible with the structure maps to `Spec B`. -/
theorem mapProj_comp_structure : mapProj 𝔞 ≫ projStructure 𝔞 = projStructure (primeOf 𝔞) := by
  refine (coverZ 𝔞).hom_ext _ _ fun b => ?_
  have hq := (qGraded 𝔞).map_mem (quotientGrading.var_mem 𝔞 b)
  have H : Proj.awayι (quotientGrading (primeOf 𝔞)) (qGraded 𝔞 (quotientGrading.var 𝔞 b)) hq one_pos ≫
      mapProj 𝔞 = Spec.map (CommRingCat.ofHom (HomogeneousLocalization.Away.map (qGraded 𝔞)
        (quotientGrading.var 𝔞 b))) ≫ Proj.awayι (quotientGrading 𝔞) (quotientGrading.var 𝔞 b)
          (quotientGrading.var_mem 𝔞 b) one_pos :=
    Proj.awayι_comp_map (qGraded 𝔞) (irrelevant_le_map_qGraded 𝔞) one_pos _ (quotientGrading.var_mem 𝔞 b)
  have h1 : Proj.awayι (quotientGrading (primeOf 𝔞)) (qGraded 𝔞 (quotientGrading.var 𝔞 b)) hq one_pos ≫
      mapProj 𝔞 ≫ projStructure 𝔞 = Spec.map (CommRingCat.ofHom (HomogeneousLocalization.Away.map
        (qGraded 𝔞) (quotientGrading.var 𝔞 b))) ≫ (Proj.awayι (quotientGrading 𝔞)
          (quotientGrading.var 𝔞 b) (quotientGrading.var_mem 𝔞 b) one_pos ≫ projStructure 𝔞) :=
    (Category.assoc _ _ _).symm.trans ((congrArg (fun m => m ≫ projStructure 𝔞) H).trans
      (Category.assoc _ _ _))
  have e1 : Proj.awayι (quotientGrading 𝔞) (quotientGrading.var 𝔞 b)
      (quotientGrading.var_mem 𝔞 b) one_pos ≫ projStructure 𝔞 =
      Spec.map (CommRingCat.ofHom (algebraMap (quotientGrading 𝔞 0)
        (HomogeneousLocalization.Away (quotientGrading 𝔞) (quotientGrading.var 𝔞 b)))) ≫
        Spec.map (CommRingCat.ofHom (algebraMap B (quotientGrading 𝔞 0))) :=
    (Category.assoc _ _ _).symm.trans (congrArg (fun m => m ≫ _) (Proj.awayι_toSpecZero _ _ _ _))
  have e2 : Proj.awayι (quotientGrading (primeOf 𝔞)) (qGraded 𝔞 (quotientGrading.var 𝔞 b)) hq one_pos ≫
      projStructure (primeOf 𝔞) =
      Spec.map (CommRingCat.ofHom (algebraMap (quotientGrading (primeOf 𝔞) 0)
        (HomogeneousLocalization.Away (quotientGrading (primeOf 𝔞)) (qGraded 𝔞 (quotientGrading.var 𝔞 b))))) ≫
        Spec.map (CommRingCat.ofHom (algebraMap B (quotientGrading (primeOf 𝔞) 0))) :=
    (Category.assoc _ _ _).symm.trans (congrArg (fun m => m ≫ _) (Proj.awayι_toSpecZero _ _ _ _))
  refine h1.trans ((congrArg (fun m => Spec.map (CommRingCat.ofHom (HomogeneousLocalization.Away.map
    (qGraded 𝔞) (quotientGrading.var 𝔞 b))) ≫ m) e1).trans (Eq.trans ?_ e2.symm))
  have := congrArg Spec.map (ring_q 𝔞 b)
  simp only [Spec.map_comp, Category.assoc] at this
  exact this

end Construction

/-- **R0.**  If `X` is integral and projective over `B` (p. 132), then it is `Proj(B[T]/𝔭)` for a homogeneous *prime* ideal
`𝔭`, over `Spec B`. -/
theorem exists_prime_presentation {B : Type u} [Field B] {X : Scheme.{u}} [IsIntegral X]
    (p : X ⟶ Spec (CommRingCat.of B)) (hp : IsProjectiveOver X p) :
    ∃ (n : ℕ) (𝔭 : HomogeneousIdeal (homogeneousSubmodule (Fin n) B)) (_ : 𝔭.toIdeal.IsPrime)
      (e : X ≅ Proj (quotientGrading 𝔭)), e.hom ≫ projStructure 𝔭 = p := by
  obtain ⟨n, 𝔞, ι, hι⟩ := hp
  have hne : Nonempty (Proj (quotientGrading 𝔞)) := ⟨ι.hom (Classical.arbitrary X)⟩
  have hint : IsIntegral (Proj (quotientGrading 𝔞)) := isIntegral_of_isOpenImmersion ι.inv
  have hiso := isIso_mapProj 𝔞
  refine ⟨n, primeOf 𝔞, primeOf_isPrime 𝔞, ι ≪≫ (asIso (mapProj 𝔞)).symm, ?_⟩
  show (ι.hom ≫ inv (mapProj 𝔞)) ≫ projStructure (primeOf 𝔞) = p
  rw [Category.assoc, ← mapProj_comp_structure 𝔞, IsIso.inv_hom_id_assoc, hι]

end Hironaka
