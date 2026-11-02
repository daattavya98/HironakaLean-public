/-
Copyright (c) 2026 Daattavya Aggarwal, Minhyong Kim, Oisin Kim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daattavya Aggarwal, Minhyong Kim, Oisin Kim
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.KrullDimension.Polynomial
public import Mathlib.RingTheory.KrullDimension.Regular
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Architect
public import Hironaka.Ch3.Transforms
public import Hironaka.Compat.BlowupCharts
public import Hironaka.Compat.BlowupBaseChange

/-!
# Dimension of a monoidal transform (Ch. I §1, Remark 1, p. 169)

> Then we have dim(X') = dim(X) = N, unless X = B. If X = B, then X' is the empty algebraic
> scheme.

For a non-singular algebraic `X` and a non-singular center `B` the local rings of `X'` are monoidal
transforms `R'` of those `R` of `X` (`compat:blowup-stalk-monoidal-transform`), so
`dim R' ≤ dim R`, with equality when `R'` is residually algebraic over `R` (p. 210,
`lem:III.2-dim`); over a point `x ∈ B` the chart `Spec R[P/z_t]` contains the point
`z_v/z_t = 0` of the fibre, whose local ring is residually rational over `R`, and off `B` the
transformation is a local isomorphism.

Deviation from the paper (gap filled): the paper states the equality without proof; this module
supplies one, using the local theory of Ch. III §2.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry IsLocalRing

namespace Hironaka

universe u

/-! ### Algebra: dimension of a monoidal transform of a regular local ring -/

section Algebra

open IsLocalRing

variable {R : Type u} [CommRing R] [IsRegularLocalRing R] [IsDomain R] {P : Ideal R}

/-- `dim R' ≤ dim R` for every monoidal transform `R'` of `R` (the inequality established in
passing in the proof of `lem:III.2-dim`, p. 210): `dim R' = ht q + 1` for a prime `q` of
`(R/P)[T₁, …, T_r]`, and `ht q ≤ dim R/P + r = dim R − 1`. -/
theorem MonoidalTransform.ringKrullDim_ring_le (t : MonoidalTransform R P) (hP : P.IsPrime)
    (hS : IsRegularLocalRing (R ⧸ P)) : ringKrullDim t.ring ≤ ringKrullDim R := by
  classical
  have := hP
  have hP0 : P ≠ ⊥ := fun h => t.x_ne_zero ((Submodule.mem_bot _).mp (le_of_eq h t.x_mem))
  obtain ⟨S, r, z, hSM, hScard, hinj, hzS, hz0, hzP⟩ := t.exists_minimal_generators hS
  obtain ⟨q, hq, e, hqC, -, -, -⟩ :=
    t.exists_quotient_equiv_localization hS hSM hScard hinj hzS hz0 hzP
  have hPM : P ≤ maximalIdeal R := IsLocalRing.le_maximalIdeal hP.ne_top
  have hxM : t.x ∈ maximalIdeal R := hPM t.x_mem
  have := (t.isRegularLocalRing_and_isLocalHom_and_span_xR_eq_map hP hP0 hS).1
  -- `dim R' = ht q + 1`
  have hX0 : t.toRing t.x ≠ 0 := fun h =>
    t.x_ne_zero (MonoidalTransform.toRing_injective t (h.trans (map_zero _).symm))
  have hdimR' : ringKrullDim t.ring = (q.height : WithBot ℕ∞) + 1 := by
    have h1 := Module.ringKrullDim_quotient_add_one_of_mem_nonZeroDivisors
      (mem_nonZeroDivisors_of_ne_zero hX0) (p := maximalIdeal t.ring)
      IsLocalRing.maximalIdeal_height_eq_ringKrullDim (map_nonunit t.toRing t.x hxM)
    rw [← h1, ← IsLocalization.AtPrime.ringKrullDim_eq_height q (Localization.AtPrime q),
      ringKrullDim_eq_of_ringEquiv e]
    rfl
  -- `dim R = #Y + r + 1` and `dim R/P ≤ #Y`
  let Y : Finset R := S \ Finset.image z Finset.univ
  have hcardS : S.card = r + 1 + Y.card := by
    have h1 : (Finset.image z Finset.univ).card = r + 1 := by
      rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]
    have h2 : Finset.image z Finset.univ ⊆ S := fun a ha => by
      obtain ⟨k, -, rfl⟩ := Finset.mem_image.mp ha
      exact hzS k
    have := Finset.card_sdiff_add_card_eq_card h2
    have hY : Y.card = (S \ Finset.image z Finset.univ).card := rfl
    omega
  have hMS : (maximalIdeal R).map (Ideal.Quotient.mk P) = maximalIdeal (R ⧸ P) :=
    IsLocalRing.map_maximalIdeal_of_surjective _ Ideal.Quotient.mk_surjective
  have hMSle : (maximalIdeal (R ⧸ P)).height ≤ Y.card := by
    have hspan : maximalIdeal (R ⧸ P) =
        Ideal.span ((Y.image (Ideal.Quotient.mk P) : Finset (R ⧸ P)) : Set (R ⧸ P)) := by
      apply le_antisymm
      · rw [← hMS, ← hSM, Ideal.map_span, Ideal.span_le]
        rintro _ ⟨a, ha, rfl⟩
        by_cases haz : a ∈ Finset.image z Finset.univ
        · obtain ⟨k, -, rfl⟩ := Finset.mem_image.mp haz
          rw [Ideal.Quotient.eq_zero_iff_mem.mpr (hzP ▸ Ideal.subset_span ⟨k, rfl⟩)]
          exact zero_mem _
        · exact Ideal.subset_span (Finset.mem_coe.mpr
            (Finset.mem_image_of_mem _ (Finset.mem_sdiff.mpr ⟨ha, haz⟩)))
      · rw [Ideal.span_le]
        intro w hw
        obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hw)
        rw [← hMS]
        exact Ideal.mem_map_of_mem _ (hSM ▸ Ideal.subset_span (Finset.mem_sdiff.mp ha).1)
    refine (Ideal.height_le_spanFinrank (maximalIdeal (R ⧸ P))
      (Ideal.IsPrime.ne_top inferInstance)).trans ?_
    rw [hspan]
    have h1 := Submodule.spanFinrank_span_le_ncard_of_finite (R := R ⧸ P)
      (Finset.finite_toSet (Y.image (Ideal.Quotient.mk P)))
    rw [Set.ncard_coe_finset] at h1
    exact_mod_cast h1.trans Finset.card_image_le
  have hdimR : ringKrullDim R = ((Y.card + r : ℕ) : WithBot ℕ∞) + 1 := by
    rw [← IsRegularLocalRing.spanFinrank_maximalIdeal, ← hScard, hcardS]
    push_cast
    ring
  -- `ht q ≤ dim (R/P)[T] = dim R/P + r`
  have := hS
  have hqle : (q.height : WithBot ℕ∞) ≤ ((Y.card + r : ℕ) : WithBot ℕ∞) := by
    have h1 := Ideal.height_le_ringKrullDim_of_ne_top (Ideal.IsPrime.ne_top hq)
    rw [MvPolynomial.ringKrullDim_of_isNoetherianRing_of_finite,
      ← IsLocalRing.maximalIdeal_height_eq_ringKrullDim, Nat.card_eq_fintype_card,
      Fintype.card_fin] at h1
    refine h1.trans ?_
    have h2 : ((maximalIdeal (R ⧸ P)).height : WithBot ℕ∞) ≤ ((Y.card : ℕ∞) : WithBot ℕ∞) :=
      WithBot.coe_le_coe.mpr hMSle
    push_cast
    exact add_le_add_left h2 _
  rw [hdimR', hdimR]
  exact add_le_add_left hqle 1

omit [IsDomain R] in
/-- In a regular local ring, `x ∉ M²` implies `xᴺ ∉ M^{N+1}` (orders are additive). -/
theorem pow_notMem_maximalIdeal_pow_succ {x : R} (hxM : x ∈ maximalIdeal R)
    (hx2 : x ∉ maximalIdeal R ^ 2) (N : ℕ) : x ^ N ∉ maximalIdeal R ^ (N + 1) := by
  have h1 : Ideal.ordElem (maximalIdeal R) x = 1 :=
    le_antisymm (by exact_mod_cast Ideal.ordElem_le_of_notMem (m := 1) hx2)
      (by exact_mod_cast Ideal.le_ordElem (ν := 1) (by rwa [pow_one]))
  have hN : ∀ N : ℕ, Ideal.ordElem (maximalIdeal R) (x ^ N) = N := by
    intro N
    induction N with
    | zero =>
      have h0 : (x ^ 0 : R) ∉ maximalIdeal R ^ (0 + 1) := by
        rw [pow_zero, zero_add, pow_one]
        exact fun h => (maximalIdeal.isMaximal R).ne_top ((Ideal.eq_top_iff_one _).mpr h)
      exact le_antisymm (by exact_mod_cast Ideal.ordElem_le_of_notMem h0) zero_le
    | succ n ih =>
      rw [pow_succ, ordElem_mul_maximalIdeal, ih, h1]
      push_cast
      rfl
  intro h
  have := Ideal.le_ordElem h
  rw [hN] at this
  norm_cast at this
  omega

/-- If `x ∈ P ⊆ M` and `x ∉ M²`, then `M R[x⁻¹P] ≠ R[x⁻¹P]` (every element of `M R[x⁻¹P]` is
`c/xᴺ` with `c ∈ M^{N+1}`, and `xᴺ ∉ M^{N+1}`). Hence `R[x⁻¹P]` has a maximal ideal over `M`. -/
theorem map_maximalIdeal_blowupAlgebra_ne_top {x : R} (hxP : x ∈ P) (hPM : P ≤ maximalIdeal R)
    (hx2 : x ∉ maximalIdeal R ^ 2) :
    (maximalIdeal R).map (algebraMap R (blowupAlgebra R P x)) ≠ ⊤ := by
  have hxM : x ∈ maximalIdeal R := hPM hxP
  have hx0 : x ≠ 0 := fun h => hx2 (h ▸ zero_mem _)
  set K := FractionRing R
  let J : Ideal (blowupAlgebra R P x) :=
    { carrier := {w | ∃ (N : ℕ) (c : R), c ∈ maximalIdeal R ^ (N + 1) ∧
        (w : K) * algebraMap R K x ^ N = algebraMap R K c}
      add_mem' := by
        rintro w₁ w₂ ⟨N₁, c₁, hc₁, h₁⟩ ⟨N₂, c₂, hc₂, h₂⟩
        refine ⟨N₁ + N₂, c₁ * x ^ N₂ + c₂ * x ^ N₁, ?_, ?_⟩
        · refine add_mem ?_ ?_
          · have := Ideal.mul_mem_mul hc₁ (Ideal.pow_mem_pow hxM N₂)
            rw [← pow_add] at this
            convert this using 2
            ring
          · have := Ideal.mul_mem_mul hc₂ (Ideal.pow_mem_pow hxM N₁)
            rw [← pow_add] at this
            convert this using 2
            ring
        · simp only [AddMemClass.coe_add, map_add, map_mul, map_pow]
          rw [← h₁, ← h₂]
          ring
      zero_mem' := ⟨0, 0, zero_mem _, by simp⟩
      smul_mem' := by
        rintro a w ⟨N, c, hc, h⟩
        obtain ⟨m, g, hg, hag⟩ :=
          MonoidalTransform.exists_mul_pow_eq_of_mem_blowupAlgebra hxP hx0 a.2
        refine ⟨N + m, g * c, ?_, ?_⟩
        · have := Ideal.mul_mem_mul (Ideal.pow_right_mono hPM m hg) hc
          rw [← pow_add] at this
          convert this using 2
          ring
        · simp only [smul_eq_mul, MulMemClass.coe_mul, map_mul]
          rw [← hag, ← h]
          ring }
  intro htop
  have hle : (maximalIdeal R).map (algebraMap R (blowupAlgebra R P x)) ≤ J := by
    rw [Ideal.map_le_iff_le_comap]
    intro m hm
    exact ⟨0, m, by rwa [zero_add, pow_one], by
      simp only [pow_zero, mul_one]; exact Subalgebra.coe_algebraMap _ _⟩
  obtain ⟨N, c, hc, h⟩ : (1 : blowupAlgebra R P x) ∈ J := hle (htop ▸ Submodule.mem_top)
  rw [OneMemClass.coe_one, one_mul, ← map_pow] at h
  exact pow_notMem_maximalIdeal_pow_succ hxM hx2 N
    (IsFractionRing.injective R K h ▸ hc)

omit [IsDomain R] in
/-- A prime `P ≠ 0` of a regular local ring with `R/P` regular is not contained in `M²`
(it is spanned by part of a minimal system of generators of `M`). -/
theorem exists_mem_notMem_maximalIdeal_sq (hP : P.IsPrime) (hS : IsRegularLocalRing (R ⧸ P))
    (hP0 : P ≠ ⊥) : ∃ b ∈ P, b ∉ maximalIdeal R ^ 2 := by
  classical
  obtain ⟨S, T, hSM, hScard, hTS, hTP⟩ := exists_finset_span_eq_prime R P hS
  obtain ⟨b, hb⟩ : T.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    rintro rfl
    exact hP0 (by rw [← hTP, Finset.coe_empty, Ideal.span_empty])
  refine ⟨b, hTP ▸ Ideal.subset_span hb, fun hb2 => ?_⟩
  have h1 := span_erase_eq_of_mem hSM (hTS hb) (Ideal.mem_sup_right hb2)
  have h2 : (maximalIdeal R).spanFinrank ≤ (S.erase b).card := by
    rw [← h1, ← Set.ncard_coe_finset]
    exact Submodule.spanFinrank_span_le_ncard_of_finite (Finset.finite_toSet _)
  have h3 := Finset.card_erase_add_one (hTS hb)
  omega

/-- The residually rational point of the fibre in a chart (p. 169 / p. 210): if `R = A_p` is
regular, `P = IR` is a prime with `R/P` regular and `a ∈ I` has image outside `M²`, then the
chart algebra `A[I/a]` has a prime `q` over `p` with `dim A[I/a]_q = dim R`. (Take a maximal
ideal `M''` of `R[a⁻¹P]` over `M`, which exists by `map_maximalIdeal_blowupAlgebra_ne_top`; the
monoidal transform `R[a⁻¹P]_{M''}` is residually algebraic over `R`, so has dimension `dim R`
by `lem:III.2-dim`, and it is `A[I/a]_q` for `q = M'' ∩ A[I/a]`.) -/
theorem exists_prime_chartAlgebra_ringKrullDim_eq {A : Type u} [CommRing A] {I : Ideal A} {a : A}
    [Algebra A R] (ha : a ∈ I) (p : Ideal A) [p.IsPrime] [IsLocalization.AtPrime R p]
    (hP : (I.map (algebraMap A R)).IsPrime) (hS : IsRegularLocalRing (R ⧸ I.map (algebraMap A R)))
    (ha2 : algebraMap A R a ∉ maximalIdeal R ^ 2) :
    ∃ (q : Ideal (chartAlgebra I a)) (_ : q.IsPrime),
      q.comap (algebraMap A (chartAlgebra I a)) = p ∧
      ringKrullDim (Localization.AtPrime q) = ringKrullDim R := by
  have ha0 : algebraMap A R a ≠ 0 := fun h => ha2 (h ▸ zero_mem _)
  have hPM : I.map (algebraMap A R) ≤ maximalIdeal R := IsLocalRing.le_maximalIdeal hP.ne_top
  have hP0 : I.map (algebraMap A R) ≠ ⊥ := fun h =>
    ha0 ((Submodule.mem_bot _).mp (h ▸ Ideal.mem_map_of_mem _ ha))
  obtain ⟨φ, hφ⟩ := exists_chartAlgebra_toBlowup (I := I) ha0
  have hloc := isLocalization_chartAlgebra_toBlowup ha ha0 p φ hφ
  obtain ⟨M'', hM''max, hle⟩ := Ideal.exists_le_maximal _
    (map_maximalIdeal_blowupAlgebra_ne_top (Ideal.mem_map_of_mem _ ha) hPM ha2)
  let s : MonoidalTransform R (I.map (algebraMap A R)) :=
    { x := algebraMap A R a
      x_mem := Ideal.mem_map_of_mem _ ha
      x_ne_zero := ha0
      M' := M''
      isPrime := hM''max.isPrime
      le := hle }
  have hqprime : (M''.comap φ).IsPrime := Ideal.comap_isPrime φ M''
  obtain ⟨e, -⟩ := MonoidalTransform.exists_ringEquiv_of_isLocalization s φ _ hloc
    (M''.comap φ) rfl
  refine ⟨M''.comap φ, hqprime, ?_, ?_⟩
  · have hMR : M''.comap (algebraMap R (blowupAlgebra R (I.map (algebraMap A R))
        (algebraMap A R a))) = maximalIdeal R :=
      ((maximalIdeal.isMaximal R).eq_of_le (Ideal.comap_isPrime _ M'').ne_top
        (Ideal.map_le_iff_le_comap.mp hle)).symm
    rw [Ideal.comap_comap, hφ, ← Ideal.comap_comap, hMR]
    exact IsLocalization.AtPrime.under_maximalIdeal R p
  · rw [ringKrullDim_eq_of_ringEquiv e]
    exact (s.ringKrullDim_eq_iff hP hP0 hS).mpr
      ((s.isMaximal_iff_isResiduallyAlgebraic).mp hM''max)

end Algebra

namespace MonoidalTransformation

variable {X : Scheme.{u}} {B : Subscheme X}

/-- A monoidal transform of an algebraic scheme is algebraic (`t.f` is proper). (Copy of
`MonoidalTransformation.isAlgebraicScheme` of `Hironaka/Ch1/ResolutionData.lean`, which is not
imported here.) -/
private theorem isAlgebraicScheme_X' [Hironaka.Cited.MonoidalTransformationExistsIsProper.{u}] [IsAlgebraicScheme X] (t : MonoidalTransformation X B) :
    IsAlgebraicScheme t.X' := by
  obtain ⟨S, i1, i2, i3, p, hp1, hp2⟩ := IsAlgebraicScheme.exists_base (X := X)
  have := IsAlgebraicScheme.isNoetherian X
  have := t.isProper
  exact ⟨⟨S, i1, i2, i3, CategoryTheory.CategoryStruct.comp t.f p, inferInstance,
    inferInstance⟩⟩

open CategoryTheory.Limits in
/-- Over a point outside `B` there is a point of `X'` (the base change of `t` to `X − B` is an
isomorphism). -/
theorem exists_apply_eq_of_notMem (t : MonoidalTransformation X B) {x : X} (hx : x ∉ B.pts) :
    ∃ y : t.X', t.f y = x := by
  let U : X.Opens := ⟨B.ptsᶜ, B.support.isClosed.isOpen_compl⟩
  have hBU : Subscheme.totalTransform U.ι B = Subscheme.empty := by
    refine Subscheme.eq_empty_of_pts_eq_empty ?_
    rw [FlatPreimm.pts_totalTransform]
    ext z
    simp only [Set.mem_preimage, Set.mem_empty_iff_false, iff_false]
    exact (U.ι_apply z ▸ z.2 : _)
  have hiso : IsIso (pullback.snd t.f U.ι) := isIso_of_eq_empty (t.baseChange U.ι) hBU
  obtain ⟨v, hv⟩ : ∃ v : U.toScheme, U.ι v = x := ⟨⟨x, hx⟩, rfl⟩
  have h1 : (pullback.snd t.f U.ι) (inv (pullback.snd t.f U.ι) v) = v := by
    rw [← Scheme.Hom.comp_apply, IsIso.inv_hom_id]
    rfl
  refine ⟨pullback.fst t.f U.ι (inv (pullback.snd t.f U.ι) v), ?_⟩
  rw [← Scheme.Hom.comp_apply, pullback.condition, Scheme.Hom.comp_apply, h1, hv]

/-- `dim R' ≤ dim R` at every point: `dim_{x'} X' ≤ dim_{f(x')} X`. -/
theorem dimAt_le (hX : X.IsNonsingular) (hB : B.IsNonsingular) (t : MonoidalTransformation X B)
    (y : t.X') : t.X'.dimAt y ≤ X.dimAt (t.f y) := by
  have : IsRegularLocalRing (X.presheaf.stalk (t.f y)) := hX _
  have := Transforms.isDomain_of_isRegularLocalRing (X.presheaf.stalk (t.f y))
  by_cases hy : t.f y ∈ B.pts
  · have hP := Subscheme.isPrime_stalkIdeal_of_isNonsingular hB hy
    have hS := Subscheme.isRegularLocalRing_quotient_of_isNonsingular hB hy
    obtain ⟨s, e, -⟩ := t.exists_monoidalTransform_stalk y
    change ringKrullDim _ ≤ ringKrullDim _
    rw [← ringKrullDim_eq_of_ringEquiv e]
    exact s.ringKrullDim_ring_le hP hS
  · exact (ringKrullDim_eq_of_ringEquiv
      (RingEquiv.ofBijective (t.f.stalkMap y).hom (t.bijective_stalkMap_of_notMem y hy))).ge

/-- Every point `x ∈ X` has a point `x'` over it with `dim_{x'} X' = dim_x X` (off `B` by the
local isomorphism, over `B` by a residually rational point of the fibre, p. 210), provided `B`
is not a neighbourhood of `x` (`B_x ≠ 0`; otherwise there is no point over `x`). -/
theorem exists_dimAt_eq (hX : X.IsNonsingular) (hB : B.IsNonsingular)
    (t : MonoidalTransformation X B) (x : X) (hx : B.stalkIdeal x ≠ ⊥) :
    ∃ y : t.X', t.f y = x ∧ t.X'.dimAt y = X.dimAt x := by
  have : IsRegularLocalRing (X.presheaf.stalk x) := hX x
  have := Transforms.isDomain_of_isRegularLocalRing (X.presheaf.stalk x)
  by_cases hxB : x ∉ B.pts
  · obtain ⟨y, rfl⟩ := t.exists_apply_eq_of_notMem hxB
    exact ⟨y, rfl, ringKrullDim_eq_of_ringEquiv
      (RingEquiv.ofBijective (t.f.stalkMap y).hom (t.bijective_stalkMap_of_notMem y hxB)).symm⟩
  rw [not_not] at hxB
  -- an affine chart `U = Spec A` around `x`, with `R = A_p`, `P = I R`
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  let W : X.affineOpens := ⟨U, hU⟩
  let := TopCat.Presheaf.algebra_section_stalk X.presheaf (⟨x, hxU⟩ : (U : X.Opens))
  have hloc := hU.isLocalization_stalk ⟨x, hxU⟩
  set p := (hU.primeIdealOf ⟨x, hxU⟩).asIdeal with hpdef
  have hP : (B.ideal W).map (algebraMap Γ(X, U) (X.presheaf.stalk x)) = B.stalkIdeal x :=
    (stalkIdeal_eq_map_germ B W hxU).symm
  have hPp := Subscheme.isPrime_stalkIdeal_of_isNonsingular hB hxB
  have hSr := Subscheme.isRegularLocalRing_quotient_of_isNonsingular hB hxB
  -- an element `a ∈ I` outside `M²`
  obtain ⟨b, hbP, hb2⟩ := exists_mem_notMem_maximalIdeal_sq hPp hSr hx
  obtain ⟨a, ha, ha2⟩ : ∃ a ∈ B.ideal W,
      algebraMap Γ(X, U) (X.presheaf.stalk x) a ∉ maximalIdeal (X.presheaf.stalk x) ^ 2 := by
    by_contra hcon
    push Not at hcon
    apply hb2
    rw [← hP] at hbP
    exact (Ideal.map_le_iff_le_comap.mpr hcon) hbP
  rw [← hP] at hPp hSr
  obtain ⟨q, hq, hqp, hdim⟩ := exists_prime_chartAlgebra_ringKrullDim_eq ha p hPp hSr ha2
  let z : Spec (chartRing B W a) := ⟨q, hq⟩
  have := t.isOpenImmersion_chart W ha
  refine ⟨t.chart W ha z, ?_, ?_⟩
  · rw [← Scheme.Hom.comp_apply, t.chart_f, chartToBase, Scheme.Hom.comp_apply]
    have hz : Spec.map (chartAlgebraMap B W a) z = hU.primeIdealOf ⟨x, hxU⟩ :=
      PrimeSpectrum.ext hqp
    rw [hz]
    exact hU.fromSpec_primeIdealOf ⟨x, hxU⟩
  · change ringKrullDim _ = ringKrullDim _
    rw [← hdim]
    exact ringKrullDim_eq_of_ringEquiv (asIso ((t.chart W ha).stalkMap z) ≪≫
      Spec.stalkIso _ z).commRingCatIsoToRingEquiv

/-- Remark 1, p. 169: `dim(X') = dim(X)` unless `X = B`. -/
@[blueprint "compat:blowup-dim"
  (statement := /-- Let $X$ be a non-singular irreducible algebraic scheme and $f\colon X'\to X$
    the monoidal transformation with a non-singular center $B\ne X$. Then $X'$ is irreducible and
    $\dim X'=\dim X$. (Remark~1, p.~169: ``we have $\dim(X')=\dim(X)=N$, unless $X=B$''.) -/)
  (proof := /-- Irreducibility: $f$ is an isomorphism over the dense open $X-B$ and $f^{-1}(B)$ is
    nowhere dense. Dimension: every local ring $R'$ of $X'$ is a monoidal transform of the local
    ring $R$ of $X$ below it (\cref{compat:blowup-stalk-monoidal-transform}), so $\dim R'\le\dim
    R$ (\cref{lem:III.2-dim}); conversely a point $x$ with $\dim\mathcal O_{X,x}=\dim X$ has a
    point over it with the same dimension, by \cref{compat:blowup-local-iso} if $x\notin B$, and
    otherwise the point $z_v/z_t=0$ of the fibre in a chart, which is residually rational over
    $x$ (\cref{lem:III.2-dim}). -/)
  (latexEnv := "lemma")]
theorem irreducibleSpace_and_dim_eq [Hironaka.Cited.MonoidalTransformationExistsIsProper.{u}] [IsAlgebraicScheme X] [IrreducibleSpace X]
    (hX : X.IsNonsingular) (hB : B.IsNonsingular) (t : MonoidalTransformation X B)
    (hBX : B.pts ≠ Set.univ) : IrreducibleSpace t.X' ∧ t.X'.dim = X.dim := by
  have := isAlgebraicScheme_X' t
  refine ⟨t.irreducibleSpace hBX, le_antisymm ?_ ?_⟩
  · exact iSup_le fun y => (dimAt_le hX hB t y).trans (le_iSup (fun x => X.dimAt x) (t.f y))
  · refine iSup_le fun x => ?_
    -- `B_x ≠ 0`: otherwise the generic point `η` of `X` would lie in `B`
    have hne : B.stalkIdeal x ≠ ⊥ := by
      intro hbot
      set η := genericPoint X
      have hηB : η ∉ B.pts := by
        intro h
        apply hBX
        have h1 : closure {η} ⊆ B.pts :=
          B.support.isClosed.closure_subset_iff.mpr (Set.singleton_subset_iff.mpr h)
        rw [(genericPoint_spec X).def] at h1
        exact Set.eq_univ_of_univ_subset h1
      obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
        X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
      have hsp : η ⤳ x := genericPoint_specializes x
      have hηU : η ∈ U := hsp.mem_open U.isOpen hxU
      have htop := Subscheme.stalkIdeal_eq_top_of_notMem_pts hηB
      rw [stalkIdeal_eq_map_germ B ⟨U, hU⟩ hηU] at htop
      have hle : (B.ideal ⟨U, hU⟩).map (X.presheaf.germ U η hηU).hom ≤ ⊥ := by
        rw [Ideal.map_le_iff_le_comap]
        intro c hc
        have h0 : X.presheaf.germ U x hxU c = 0 := by
          have : (X.presheaf.germ U x hxU).hom c ∈ B.stalkIdeal x := by
            rw [stalkIdeal_eq_map_germ B ⟨U, hU⟩ hxU]
            exact Ideal.mem_map_of_mem _ hc
          rw [hbot] at this
          exact (Submodule.mem_bot _).mp this
        rw [Ideal.mem_comap, Submodule.mem_bot, ← X.presheaf.germ_stalkSpecializes hxU hsp]
        change (X.presheaf.stalkSpecializes hsp) (X.presheaf.germ U x hxU c) = 0
        rw [h0, map_zero]
      rw [htop] at hle
      exact top_ne_bot (le_bot_iff.mp hle)
    obtain ⟨y, -, hy⟩ := exists_dimAt_eq hX hB t x hne
    exact hy ▸ le_iSup (fun y => t.X'.dimAt y) y

end MonoidalTransformation

end Hironaka

