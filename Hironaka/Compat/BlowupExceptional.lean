/-
Copyright (c) 2026 Daattavya Aggarwal, Minhyong Kim, Oisin Kim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daattavya Aggarwal, Minhyong Kim, Oisin Kim
-/
module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Architect
public import Hironaka.Ch3.Transforms
public import Hironaka.Compat.BlowupCharts
public import Hironaka.Compat.BlowupBaseChange
public import Hironaka.Compat.ComponentStalk

/-!
# Irreducibility of the exceptional subscheme (used in Ch. I §1, Remark 1, p. 169)

For a non-singular algebraic scheme `X` and a non-singular irreducible center `B`, the exceptional
subscheme `f⁻¹(B)` of the monoidal transformation `f : X' → X` is irreducible: it is the projective
bundle of the normal cone of `B`, whose fibres over `B` are projective spaces.  Remark 1 uses this
without comment when it asserts that `E_{α+1} = f⁻¹(B)` is a non-singular irreducible subscheme of
codimension one (Definition 3 (II)(ii)).

The proof works with the points `η` of `E = f⁻¹(B)` which have no proper generization in `E` (the
generic points of the irreducible components of `E`):

* the stalk `E_η = xR'` is prime (`R'/xR'` is regular, p. 210), hence the maximal ideal of
  `R' = O_{X', η}`; since `xR' ∩ R = P` (`MonoidalTransform.mem_pow_of_toRing_mem`), `B_{f η}` is
  the maximal ideal of `R = O_{X, f η}`, so `f η` is the generic point `ξ` of `B`;
* for an affine open `U ∋ ξ` and `a ∈ B(U)` whose germ is not in `B_ξ²`, the germ of `a` generates
  `E_η = xR'`, so every such `η` lies in the chart `V_a = Spec Γ(X,U)[B(U)/a]`;
* in that chart the prime of `η` is determined by `B_ξ`-adic orders: `g/aⁿ` lies in it iff
  `g ∈ B_ξⁿ⁺¹` (the `x`-adic order in `R'` is the `P`-adic order in `R`, p. 215).

Hence all components of `E` have the same generic point.

Deviation from the paper (gap filled): the paper uses this without comment; this module
supplies a proof (using Ch. III facts, pp. 210 and 215).
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry IsLocalRing
open scoped nonZeroDivisors

namespace Hironaka

universe u

/-! ### Points of a subscheme without proper generizations -/

namespace Subscheme

variable {Z : Scheme.{u}}

/-- Every point of a subscheme `D` is a specialization of a point `η` of `D` without proper
generizations in `D` (the generic point of an irreducible component of `D` through it). -/
theorem exists_maximalGeneric_specializes (D : Subscheme Z) {p : Z} (hp : p ∈ D.pts) :
    ∃ η ∈ D.pts, (∀ w ∈ D.pts, w ⤳ η → w = η) ∧ η ⤳ p := by
  obtain ⟨y₀, rfl⟩ := Subscheme.exists_ι_eq_of_mem_pts D hp
  obtain ⟨C, hC, hy₀C⟩ :=
    exists_mem_irreducibleComponents_subset_of_isIrreducible {y₀} isIrreducible_singleton
  have hCirr : _root_.IsIrreducible C := hC.1
  have hCcl : IsClosed C := isClosed_of_mem_irreducibleComponents C hC
  set y := hCirr.genericPoint
  have hyC : closure {y} = C := by
    rw [hCirr.isGenericPoint_genericPoint_closure.def, hCcl.closure_eq]
  have hyy₀ : y ⤳ y₀ := specializes_iff_mem_closure.mpr (by rw [hyC]; exact hy₀C rfl)
  have hgen : ∀ w, w ⤳ y → w = y := by
    intro w hw
    have hCw : C ⊆ closure {w} := by
      rw [← hyC]
      exact closure_minimal (Set.singleton_subset_iff.mpr (specializes_iff_mem_closure.mp hw))
        isClosed_closure
    have hwC : closure {w} = C := (hC.2 isIrreducible_singleton.closure hCw).antisymm hCw
    have hyw : y ⤳ w :=
      specializes_iff_mem_closure.mpr (by rw [hyC, ← hwC]; exact subset_closure rfl)
    exact (hw.antisymm hyw).eq
  refine ⟨D.ι y, Subscheme.mem_pts_ι D y, fun w hw hwy => ?_,
    hyy₀.map D.ι.base.hom.continuous⟩
  obtain ⟨w', rfl⟩ := Subscheme.exists_ι_eq_of_mem_pts D hw
  rw [hgen w' (D.ι.isEmbedding.isInducing.specializes_iff.mp hwy)]

/-- If the stalk of `D` at a point `η` without proper generizations in `D` is prime, it is the
maximal ideal: the prime `D_η` corresponds to a generization of `η` lying on `D`. -/
theorem stalkIdeal_eq_maximalIdeal_of_maximalGeneric (D : Subscheme Z) {η : Z}
    (hη : η ∈ D.pts) (hgen : ∀ w ∈ D.pts, w ⤳ η → w = η) (hprime : (D.stalkIdeal η).IsPrime) :
    D.stalkIdeal η = maximalIdeal (Z.presheaf.stalk η) := by
  obtain ⟨W, hηW⟩ := Subscheme.exists_affineOpen_mem η
  let _ : Algebra Γ(Z, W) (Z.presheaf.stalk η) :=
    TopCat.Presheaf.algebra_section_stalk Z.presheaf (⟨η, hηW⟩ : (W : Z.Opens))
  have hloc : IsLocalization.AtPrime (Z.presheaf.stalk η) (W.2.primeIdealOf ⟨η, hηW⟩).asIdeal :=
    W.2.isLocalization_stalk ⟨η, hηW⟩
  have hDη : D.stalkIdeal η = (D.ideal W).map (algebraMap Γ(Z, W) (Z.presheaf.stalk η)) :=
    Subscheme.stalkIdeal_eq_map_germ_affine D W hηW
  -- the prime `q = D_η ∩ Γ(Z, W)` gives a point of `D` specializing to `η`
  let q : PrimeSpectrum Γ(Z, W) :=
    ⟨(D.stalkIdeal η).comap (algebraMap Γ(Z, W) (Z.presheaf.stalk η)), Ideal.IsPrime.comap _⟩
  have hDq : D.ideal W ≤ q.asIdeal := by
    show D.ideal W ≤ (D.stalkIdeal η).comap _
    rw [hDη]
    exact Ideal.le_comap_map
  have hqη : q.asIdeal ≤ (W.2.primeIdealOf ⟨η, hηW⟩).asIdeal := by
    intro c hc
    have h1 : algebraMap Γ(Z, W) (Z.presheaf.stalk η) c ∈ maximalIdeal _ :=
      Subscheme.stalkIdeal_le_maximalIdeal D hη hc
    exact (IsLocalization.AtPrime.to_map_mem_maximal_iff _ _ c).mp h1
  have hw : W.2.fromSpec q ∈ D.pts :=
    (Subscheme.compStalk_fromSpec_mem_pts_iff D W.2 q).mpr hDq
  have hsp : W.2.fromSpec q ⤳ η := by
    have := (Subscheme.compStalk_fromSpec_specializes_iff W.2 q _).mpr hqη
    rwa [W.2.fromSpec_primeIdealOf] at this
  -- so it is `η`, and `D_η` is the extension of the prime of `η`
  have hηq : η ⤳ W.2.fromSpec q := by rw [hgen _ hw hsp]
  have hpq : (W.2.primeIdealOf ⟨η, hηW⟩).asIdeal ≤ q.asIdeal := by
    rw [← Subscheme.compStalk_fromSpec_specializes_iff W.2, W.2.fromSpec_primeIdealOf]
    exact hηq
  have hqeq : q.asIdeal = (W.2.primeIdealOf ⟨η, hηW⟩).asIdeal := le_antisymm hqη hpq
  rw [← IsLocalization.map_under (W.2.primeIdealOf ⟨η, hηW⟩).asIdeal.primeCompl
    (Z.presheaf.stalk η) (D.stalkIdeal η)]
  change q.asIdeal.map _ = _
  rw [hqeq]
  exact IsLocalization.AtPrime.map_eq_maximalIdeal _ _

/-- A point `ξ` of `D` specializing to a point `x` at which the stalk of `D` is the maximal ideal
is `x` itself. -/
theorem eq_of_specializes_of_stalkIdeal_eq_maximalIdeal (D : Subscheme Z) {ξ x : Z}
    (hξ : ξ ∈ D.pts) (hsp : ξ ⤳ x)
    (hmax : D.stalkIdeal x = maximalIdeal (Z.presheaf.stalk x)) : ξ = x := by
  obtain ⟨W, hxW⟩ := Subscheme.exists_affineOpen_mem x
  have hξW : ξ ∈ (W : Z.Opens) := hsp.mem_open W.1.isOpen hxW
  let _ : Algebra Γ(Z, W) (Z.presheaf.stalk x) :=
    TopCat.Presheaf.algebra_section_stalk Z.presheaf (⟨x, hxW⟩ : (W : Z.Opens))
  have hloc : IsLocalization.AtPrime (Z.presheaf.stalk x) (W.2.primeIdealOf ⟨x, hxW⟩).asIdeal :=
    W.2.isLocalization_stalk ⟨x, hxW⟩
  -- `D(W) ⊆ p_ξ ⊆ p_x`
  have hDξ : D.ideal W ≤ (W.2.primeIdealOf ⟨ξ, hξW⟩).asIdeal :=
    (Subscheme.compStalk_fromSpec_mem_pts_iff D W.2 _).mp
      (by rw [W.2.fromSpec_primeIdealOf]; exact hξ)
  have hξx : (W.2.primeIdealOf ⟨ξ, hξW⟩).asIdeal ≤ (W.2.primeIdealOf ⟨x, hxW⟩).asIdeal := by
    rw [← Subscheme.compStalk_fromSpec_specializes_iff W.2, W.2.fromSpec_primeIdealOf,
      W.2.fromSpec_primeIdealOf]
    exact hsp
  -- `M_x = D_x ⊆ p_ξ O_x`, so `p_x ⊆ p_ξ`
  have h1 : maximalIdeal (Z.presheaf.stalk x) ≤
      (W.2.primeIdealOf ⟨ξ, hξW⟩).asIdeal.map (algebraMap Γ(Z, W) _) := by
    rw [← hmax, Subscheme.stalkIdeal_eq_map_germ_affine D W hxW]
    exact Ideal.map_mono hDξ
  have h2 : (W.2.primeIdealOf ⟨x, hxW⟩).asIdeal ≤ (W.2.primeIdealOf ⟨ξ, hξW⟩).asIdeal := by
    intro c hc
    have h3 : algebraMap Γ(Z, W) (Z.presheaf.stalk x) c ∈ maximalIdeal _ :=
      (IsLocalization.AtPrime.to_map_mem_maximal_iff _ _ c).mpr hc
    have h4 := h1 h3
    rwa [← Ideal.mem_comap, Subscheme.compStalk_under_map _ _ hξx] at h4
  have hpeq : W.2.primeIdealOf ⟨ξ, hξW⟩ = W.2.primeIdealOf ⟨x, hxW⟩ :=
    PrimeSpectrum.ext (le_antisymm hξx h2)
  have e1 := W.2.fromSpec_primeIdealOf ⟨ξ, hξW⟩
  have e2 := W.2.fromSpec_primeIdealOf ⟨x, hxW⟩
  rw [hpeq, e2] at e1
  exact e1.symm

end Subscheme

/-! ### Local algebra of `f⁻¹(B)` -/

namespace MonoidalTransformation

variable {X : Scheme.{u}} {B : Subscheme X}

/-- The stalk of `f⁻¹(B)` is never zero (`X` non-singular): it is `xR'` with `x ≠ 0`. -/
theorem stalkIdeal_exceptional_ne_bot (hX : X.IsNonsingular) (t : MonoidalTransformation X B)
    (y : t.X') : t.exceptional.stalkIdeal y ≠ ⊥ := by
  have : IsRegularLocalRing (X.presheaf.stalk (t.f y)) := hX _
  have := isDomain_of_isRegularLocalRing (X.presheaf.stalk (t.f y))
  obtain ⟨s, e, -, hE⟩ := t.exists_monoidalTransform_stalk_exceptional y
  rw [hE, Ne, Ideal.span_singleton_eq_bot, map_eq_zero_iff e e.injective]
  intro h
  exact s.x_ne_zero (s.toRing_injective (h.trans (map_zero _).symm))

/-- `E_yᵏ ∩ O_{X, f y} = B_{f y}ᵏ` for `E = f⁻¹(B)` and `y ∈ E` (`X`, `B` non-singular): the
`P`-adic order in `R` is the `x`-adic order in the monoidal transform `R'` (p. 215). -/
theorem stalkMap_mem_exceptional_pow_iff (hX : X.IsNonsingular) (hBns : B.IsNonsingular)
    (t : MonoidalTransformation X B) {y : t.X'} (hy : y ∈ t.exceptional.pts) (k : ℕ)
    (g : X.presheaf.stalk (t.f y)) :
    t.f.stalkMap y g ∈ t.exceptional.stalkIdeal y ^ k ↔ g ∈ B.stalkIdeal (t.f y) ^ k := by
  constructor
  · intro hg
    have : IsRegularLocalRing (X.presheaf.stalk (t.f y)) := hX _
    have := isDomain_of_isRegularLocalRing (X.presheaf.stalk (t.f y))
    have hfy := t.mem_pts_of_mem_exceptional hy
    have hP := Subscheme.isPrime_stalkIdeal_of_isNonsingular hBns hfy
    have hS := Subscheme.isRegularLocalRing_quotient_of_isNonsingular hBns hfy
    obtain ⟨s, e, he, hE⟩ := t.exists_monoidalTransform_stalk_exceptional y
    refine s.mem_pow_of_toRing_mem hP hS ?_
    have h1 : t.f.stalkMap y g = e (s.toRing g) := (RingHom.congr_fun he g).symm
    rw [hE, h1, Ideal.span_singleton_pow, Ideal.mem_span_singleton, ← map_pow] at hg
    rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    exact (map_dvd_iff e).mp hg
  · intro hg
    rw [exceptional, stalkIdeal_totalTransform, ← Ideal.map_pow]
    exact Ideal.mem_map_of_mem _ hg

/-- At a point `y` of `E = f⁻¹(B)` where `E_y` is the maximal ideal, every `b ∈ B_{f y} − B_{f y}²`
generates `E_y`. -/
theorem stalkIdeal_exceptional_eq_span_of_notMem_sq (hX : X.IsNonsingular)
    (hBns : B.IsNonsingular) (t : MonoidalTransformation X B) {y : t.X'}
    (hy : y ∈ t.exceptional.pts)
    (hmax : t.exceptional.stalkIdeal y = maximalIdeal (t.X'.presheaf.stalk y))
    {b : X.presheaf.stalk (t.f y)} (hb : b ∈ B.stalkIdeal (t.f y))
    (hb2 : b ∉ B.stalkIdeal (t.f y) ^ 2) :
    t.exceptional.stalkIdeal y = Ideal.span {t.f.stalkMap y b} := by
  have hbE : t.f.stalkMap y b ∈ t.exceptional.stalkIdeal y := by
    rw [← pow_one (t.exceptional.stalkIdeal y), stalkMap_mem_exceptional_pow_iff hX hBns t hy,
      pow_one]
    exact hb
  have hb2' : t.f.stalkMap y b ∉ t.exceptional.stalkIdeal y ^ 2 := by
    rwa [stalkMap_mem_exceptional_pow_iff hX hBns t hy]
  have : IsRegularLocalRing (X.presheaf.stalk (t.f y)) := hX _
  have := isDomain_of_isRegularLocalRing (X.presheaf.stalk (t.f y))
  obtain ⟨s, e, -, hE⟩ := t.exists_monoidalTransform_stalk_exceptional y
  rw [hE] at hbE hb2' hmax ⊢
  -- `b = x w` with `w` outside `xR' = M'`, i.e. a unit
  obtain ⟨w, hw⟩ := Ideal.mem_span_singleton'.mp hbE
  have hwu : IsUnit w := by
    by_contra hw'
    have hwm : w ∈ maximalIdeal (t.X'.presheaf.stalk y) := (mem_maximalIdeal _).mpr hw'
    rw [← hmax] at hwm
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp hwm
    apply hb2'
    rw [← hw, ← hc, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    exact ⟨c, by ring⟩
  rw [← hw, Ideal.span_singleton_mul_left_unit hwu]

/-- Converse of `stalkIdeal_exceptional_of_mem_chartOpen`: a point `y` over `U` at which the stalk
of `f⁻¹(B)` is generated by `a ∈ B(U)` lies in the chart `V_a`. -/
theorem mem_chartOpen_of_stalkIdeal_exceptional_eq (t : MonoidalTransformation X B)
    {U : X.affineOpens} {a : Γ(X, U)} (ha : a ∈ B.ideal U) {y : t.X'} (hfy : t.f y ∈ U.1)
    (hE : t.exceptional.stalkIdeal y =
      Ideal.span {t.f.stalkMap y (X.presheaf.germ U (t.f y) hfy a)}) :
    y ∈ t.chartOpen U a := by
  -- near `y`, `f⁻¹(B)` is generated by a non-zero-divisor `s₁` on `D(r) ⊆ f⁻¹(U)`, and `a = s₁ u`
  obtain ⟨W₀, hyW₀, s, hs, hsnzd⟩ := t.invertible y
  change t.exceptional.ideal W₀ = _ at hs
  obtain ⟨r, hrle, hyr⟩ := (isAffineOpen_of_mem_affineOpens W₀).exists_basicOpen_le
    (V := t.f ⁻¹ᵁ U) ⟨y, hfy⟩ hyW₀
  have hs₁ := ideal_affBasicOpen_eq_span _ hs r
  have hs₁nzd := res_basicOpen_mem_nonZeroDivisors W₀ hsnzd r
  set s₁ := t.X'.presheaf.map (homOfLE (t.X'.basicOpen_le r)).op s
  have hW₁U : ((affBasicOpen W₀ r : t.X'.affineOpens) : t.X'.Opens) ≤ t.f ⁻¹ᵁ U := hrle
  have hid : t.exceptional.ideal (affBasicOpen W₀ r) =
      (B.ideal U).map (t.f.appLE U _ hW₁U).hom :=
    ideal_comap_eq_map_appLE t.f B U _ hW₁U
  obtain ⟨u, hu⟩ : ∃ u, t.f.appLE U _ hW₁U a = s₁ * u := by
    have : t.f.appLE U _ hW₁U a ∈ t.exceptional.ideal (affBasicOpen W₀ r) :=
      hid ▸ Ideal.mem_map_of_mem _ ha
    rw [hs₁, Ideal.mem_span_singleton'] at this
    obtain ⟨u, hu⟩ := this
    exact ⟨u, by rw [← hu, mul_comm]⟩
  -- it suffices that `u` is a unit at `y`
  suffices hunit : IsUnit (t.X'.presheaf.germ (t.X'.basicOpen r) y hyr u) by
    rw [mem_chartOpen_iff]
    exact ⟨_, isChartDomain_basicOpen t U hW₁U hs₁ hs₁nzd hu,
      (Scheme.mem_basicOpen _ _ _ hyr).mpr hunit⟩
  set γ := t.X'.presheaf.germ (t.X'.basicOpen r) y hyr
  have hγa : γ (t.f.appLE U _ hW₁U a) = t.f.stalkMap y (X.presheaf.germ U (t.f y) hfy a) := by
    rw [← CommRingCat.comp_apply, appLE_germ t.f U _ hW₁U y hyr hfy, CommRingCat.comp_apply]
  have hs₁E : γ s₁ ∈ t.exceptional.stalkIdeal y := by
    rw [stalkIdeal_eq_map_germ _ (affBasicOpen W₀ r) hyr]
    exact Ideal.mem_map_of_mem _ (by rw [hs₁]; exact Ideal.mem_span_singleton_self _)
  -- `s₁ = w a = w s₁ u` at `y`, and `s₁` is a non-zero-divisor of the stalk
  rw [hE, Ideal.mem_span_singleton'] at hs₁E
  obtain ⟨w, hw⟩ := hs₁E
  rw [← hγa, hu, map_mul] at hw
  have hnzd : γ s₁ ∈ (t.X'.presheaf.stalk y)⁰ := by
    let _ := TopCat.Presheaf.algebra_section_stalk t.X'.presheaf
      (⟨y, hyr⟩ : ((affBasicOpen W₀ r : t.X'.affineOpens) : t.X'.Opens))
    have := (affBasicOpen W₀ r).2.isLocalization_stalk ⟨y, hyr⟩
    exact algebraMap_mem_nonZeroDivisors_of_isLocalization (S := t.X'.presheaf.stalk y)
      ((affBasicOpen W₀ r).2.primeIdealOf ⟨y, hyr⟩).asIdeal.primeCompl hs₁nzd
  have h1 : (w * γ u - 1) * γ s₁ = 0 := by linear_combination hw
  rw [mul_right_mem_nonZeroDivisors_eq_zero_iff hnzd, sub_eq_zero] at h1
  exact IsUnit.of_mul_eq_one w (by rw [mul_comm]; exact h1)

/-- A point `η` of `f⁻¹(B)` over `x ∈ U`, at which the stalk of `f⁻¹(B)` is the maximal ideal, lies
in the chart `V_a` of every `a ∈ B(U)` whose germ at `x` is not in `B_x²`. -/
theorem mem_chartOpen_of_stalkIdeal_exceptional_eq_maximalIdeal (hX : X.IsNonsingular)
    (hBns : B.IsNonsingular) (t : MonoidalTransformation X B) {U : X.affineOpens}
    {a : Γ(X, U)} (ha : a ∈ B.ideal U) {x : X} (hxU : x ∈ U.1)
    (hord : X.presheaf.germ U x hxU a ∉ B.stalkIdeal x ^ 2) {η : t.X'} (hfη : t.f η = x)
    (hη : η ∈ t.exceptional.pts)
    (hmax : t.exceptional.stalkIdeal η = maximalIdeal (t.X'.presheaf.stalk η)) :
    η ∈ t.chartOpen U a := by
  subst hfη
  refine mem_chartOpen_of_stalkIdeal_exceptional_eq t ha hxU ?_
  exact stalkIdeal_exceptional_eq_span_of_notMem_sq hX hBns t hη hmax
    (Ideal.subset_span ⟨U, hxU, a, ha, rfl⟩) hord

/-- In the chart `Spec Γ(X,U)[B(U)/a]`, a point `z` whose image in `X'` has the maximal ideal as
the stalk of `f⁻¹(B)` is determined by `B_x`-adic orders, `x` being its image in `X`: an element
`c = g/aⁿ` of the chart ring lies in `z` iff `g ∈ B_xⁿ⁺¹`. -/
theorem mem_asIdeal_chart_iff (hX : X.IsNonsingular) (hBns : B.IsNonsingular)
    (t : MonoidalTransformation X B) {U : X.affineOpens} {a : Γ(X, U)} (ha : a ∈ B.ideal U)
    (z : Spec (chartRing B U a)) {x : X} (hxU : x ∈ U.1) (hfz : t.f (t.chart U ha z) = x)
    (hmax : t.exceptional.stalkIdeal (t.chart U ha z) =
      maximalIdeal (t.X'.presheaf.stalk (t.chart U ha z)))
    (c : chartAlgebra (B.ideal U) a) (n : ℕ) (g : Γ(X, U))
    (hcg : c * algebraMap Γ(X, U) (chartAlgebra (B.ideal U) a) a ^ n =
      algebraMap Γ(X, U) (chartAlgebra (B.ideal U) a) g) :
    c ∈ PrimeSpectrum.asIdeal z ↔ X.presheaf.germ U x hxU g ∈ B.stalkIdeal x ^ (n + 1) := by
  subst hfz
  have hy : t.chart U ha z ∈ t.exceptional.pts := Subscheme.mem_pts_iff_stalkIdeal_ne_top.mpr
    (by rw [hmax]; exact (maximalIdeal.isMaximal _).ne_top)
  have hEa := t.stalkIdeal_exceptional_of_mem_chartOpen (t.chart_apply_mem_chartOpen U ha z) hxU
  -- `O_{X', y} ≅ Γ(X,U)[B(U)/a]_z` compatibly with `Γ(X, U)`
  have := t.isOpenImmersion_chart U ha
  have : (PrimeSpectrum.asIdeal z).IsPrime := PrimeSpectrum.isPrime z
  let e1 : t.X'.presheaf.stalk (t.chart U ha z) ≃+*
      Localization.AtPrime (PrimeSpectrum.asIdeal z) :=
    (asIso ((t.chart U ha).stalkMap z) ≪≫ Spec.stalkIso _ z).commRingCatIsoToRingEquiv
  have he1 : ∀ r : Γ(X, U), e1 (t.f.stalkMap _ (X.presheaf.germ U _ hxU r)) =
      algebraMap _ (Localization.AtPrime (PrimeSpectrum.asIdeal z))
        (algebraMap Γ(X, U) (chartAlgebra (B.ideal U) a) r) := by
    intro r
    change (X.presheaf.germ U _ hxU ≫ t.f.stalkMap _ ≫ (t.chart U ha).stalkMap z ≫
      (Spec.stalkIso _ z).hom) r = _
    rw [t.germ_stalkMap_chart_stalkIso ha z hxU]
    rfl
  have : IsRegularLocalRing (t.X'.presheaf.stalk (t.chart U ha z)) :=
    t.isRegularLocalRing_stalk hX hBns _
  have := isDomain_of_isRegularLocalRing (t.X'.presheaf.stalk (t.chart U ha z))
  -- `α`, the germ of `a`, generates `E_y`, and `c' α ⁿ = g` for the image `c'` of `c`
  set α := t.f.stalkMap (t.chart U ha z) (X.presheaf.germ U _ hxU a) with hα
  have hα0 : α ≠ 0 := by
    intro h0
    have h1 := he1 a
    rw [← hα, h0, map_zero] at h1
    exact nonZeroDivisors.ne_zero (algebraMap_mem_nonZeroDivisors_chartAlgebra_localization
      (S := Localization.AtPrime (PrimeSpectrum.asIdeal z))
        (PrimeSpectrum.asIdeal z).primeCompl) h1.symm
  set c' := e1.symm (algebraMap _ (Localization.AtPrime (PrimeSpectrum.asIdeal z)) c) with hc'
  have hc'g : c' * α ^ n = t.f.stalkMap _ (X.presheaf.germ U _ hxU g) := by
    apply e1.injective
    rw [map_mul, map_pow, hc', RingEquiv.apply_symm_apply, hα, he1, he1, ← hcg, map_mul,
      map_pow]
  have step1 : c ∈ PrimeSpectrum.asIdeal z ↔
      c' ∈ maximalIdeal (t.X'.presheaf.stalk (t.chart U ha z)) := by
    rw [← IsLocalization.AtPrime.to_map_mem_maximal_iff
      (Localization.AtPrime (PrimeSpectrum.asIdeal z)) (PrimeSpectrum.asIdeal z) c]
    constructor
    · intro h
      rw [mem_maximalIdeal, mem_nonunits_iff] at h ⊢
      intro hu
      have hu' := hu.map e1
      rw [hc', RingEquiv.apply_symm_apply] at hu'
      exact h hu'
    · intro h
      rw [mem_maximalIdeal, mem_nonunits_iff] at h ⊢
      exact fun hu => h (hu.map e1.symm)
  -- `c' ∈ (α) ⟺ c' αⁿ ∈ (α)ⁿ⁺¹ = E_yⁿ⁺¹ ⟺ g ∈ B_xⁿ⁺¹`
  rw [step1, ← hmax, hEa, Ideal.mem_span_singleton,
    ← stalkMap_mem_exceptional_pow_iff hX hBns t hy, hEa, Ideal.span_singleton_pow,
    Ideal.mem_span_singleton, ← hc'g, pow_succ, mul_comm c',
    mul_dvd_mul_iff_left (pow_ne_zero n hα0)]

/-- `f⁻¹(B)` is irreducible for a non-singular irreducible center `B` of a non-singular algebraic
`X` (used without comment in Remark 1, p. 169). -/
@[blueprint "compat:blowup-exceptional-irreducible"
  (statement := /-- Let $X$ be a non-singular algebraic scheme, $B$ a non-singular irreducible
    subscheme and $f\colon X'\to X$ the monoidal transformation with center $B$. If $f^{-1}(B)$ is
    non-empty, it is irreducible. (Used without comment in Remark~1, p.~169.) -/)
  (proof := /-- Let $\eta$ be a point of $E=f^{-1}(B)$ without proper generization in $E$. The
    local ring of $E$ at $\eta$ is $R'/xR'$, $R'$ a monoidal transform of $R=\mathcal O_{X,f\eta}$
    with center $P=B_{f\eta}$ (\cref{compat:blowup-stalk-monoidal-transform}), which is regular
    (\cref{lem:III.2-monoidal-transform-regular}), hence a domain; so $xR'$ is prime, hence the
    maximal ideal of $R'$. As $x^kR'\cap R=P^k$, $P$ is the maximal ideal of $R$ and $f\eta$ is the
    generic point $\xi$ of $B$. Fix an affine open $U\ni\xi$ and $a\in B(U)$ with
    $a\notin B_\xi^2$; then $a$ generates $xR'$, so $\eta$ lies in the chart $V_a$
    (\cref{compat:blowup-chart-open-immersion}). In this chart the prime of $\eta$ consists of the
    $g/a^n$ with $g\in B_\xi^{n+1}$, independently of $\eta$. Hence all irreducible components of
    $E$ have the same generic point. -/)
  (latexEnv := "lemma")]
theorem isIrreducible_exceptional [IsAlgebraicScheme X] (hX : X.IsNonsingular)
    (hBns : B.IsNonsingular) (hBirr : B.IsIrreducible) (t : MonoidalTransformation X B)
    (hne : t.exceptional.pts.Nonempty) : t.exceptional.IsIrreducible := by
  obtain ⟨ξ, hξ⟩ := Subscheme.exists_isGenericPoint hBirr
  -- the points of `E = f⁻¹(B)` without proper generization in `E` lie over `ξ`, and the stalk of
  -- `E` there is the maximal ideal
  have key : ∀ η ∈ t.exceptional.pts, (∀ w ∈ t.exceptional.pts, w ⤳ η → w = η) →
      t.exceptional.stalkIdeal η = maximalIdeal (t.X'.presheaf.stalk η) ∧ t.f η = ξ := by
    intro η hη hgen
    have hprime : (t.exceptional.stalkIdeal η).IsPrime := by
      have := t.isRegularLocalRing_quotient_exceptional hX hBns hη
      have := isDomain_of_isRegularLocalRing
        (t.X'.presheaf.stalk η ⧸ t.exceptional.stalkIdeal η)
      exact (Ideal.Quotient.isDomain_iff_prime _).mp this
    have hmax := Subscheme.stalkIdeal_eq_maximalIdeal_of_maximalGeneric t.exceptional hη hgen
      hprime
    refine ⟨hmax, ?_⟩
    have hfη := t.mem_pts_of_mem_exceptional hη
    have hBmax : B.stalkIdeal (t.f η) = maximalIdeal (X.presheaf.stalk (t.f η)) := by
      refine le_antisymm (Subscheme.stalkIdeal_le_maximalIdeal B hfη) fun g hg => ?_
      rw [← pow_one (B.stalkIdeal _), ← stalkMap_mem_exceptional_pow_iff hX hBns t hη 1 g,
        pow_one, hmax]
      exact map_nonunit (t.f.stalkMap η).hom g hg
    exact (Subscheme.eq_of_specializes_of_stalkIdeal_eq_maximalIdeal B hξ.mem
      (hξ.specializes hfη) hBmax).symm
  obtain ⟨y₀, hy₀⟩ := hne
  obtain ⟨η₀, hη₀, hgen₀, -⟩ := Subscheme.exists_maximalGeneric_specializes t.exceptional hy₀
  obtain ⟨hmax₀, hfη₀⟩ := key η₀ hη₀ hgen₀
  subst hfη₀
  obtain ⟨U, hU⟩ := Subscheme.exists_affineOpen_mem (t.f η₀)
  obtain ⟨a, ha, hη₀a⟩ := t.exists_mem_chartOpen U hU
  -- the germ of `a` at the generic point of `B` is not in `B_ξ²`
  have hord : X.presheaf.germ U (t.f η₀) hU a ∉ B.stalkIdeal (t.f η₀) ^ 2 := by
    intro h2
    have hEa := t.stalkIdeal_exceptional_of_mem_chartOpen hη₀a hU
    have h3 := (stalkMap_mem_exceptional_pow_iff hX hBns t hη₀ 2 _).mpr h2
    rw [hEa, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at h3
    have : IsRegularLocalRing (t.X'.presheaf.stalk η₀) := t.isRegularLocalRing_stalk hX hBns η₀
    have := isDomain_of_isRegularLocalRing (t.X'.presheaf.stalk η₀)
    set α := t.f.stalkMap η₀ (X.presheaf.germ U (t.f η₀) hU a)
    have hα0 : α ≠ 0 := fun h0 => stalkIdeal_exceptional_ne_bot hX t η₀
      (by rw [hEa, h0, Ideal.span_singleton_eq_bot])
    obtain ⟨c, hc⟩ := h3
    have hu : α * c = 1 := by
      have h4 : α * (α * c - 1) = 0 := by linear_combination -hc
      rcases mul_eq_zero.mp h4 with h | h
      · exact absurd h hα0
      · exact sub_eq_zero.mp h
    exact Subscheme.mem_pts_iff_stalkIdeal_ne_top.mp hη₀
      (by rw [hEa]; exact Ideal.span_singleton_eq_top.mpr (IsUnit.of_mul_eq_one c hu))
  -- all points of `E` without proper generization in `E` coincide with `η₀`
  have huniq : ∀ η ∈ t.exceptional.pts, (∀ w ∈ t.exceptional.pts, w ⤳ η → w = η) →
      η = η₀ := by
    intro η hη hgen
    obtain ⟨hmax, hfη⟩ := key η hη hgen
    have hηa := mem_chartOpen_of_stalkIdeal_exceptional_eq_maximalIdeal hX hBns t ha hU hord
      hfη hη hmax
    obtain ⟨z, hz⟩ : η ∈ Set.range (t.chart U ha) := by rw [t.range_chart U ha]; exact hηa
    obtain ⟨z₀, hz₀⟩ : η₀ ∈ Set.range (t.chart U ha) := by rw [t.range_chart U ha]; exact hη₀a
    have hfz : t.f (t.chart U ha z) = t.f η₀ := by rw [hz]; exact hfη
    have hfz₀ : t.f (t.chart U ha z₀) = t.f η₀ := by rw [hz₀]
    have hmz : t.exceptional.stalkIdeal (t.chart U ha z) =
        maximalIdeal (t.X'.presheaf.stalk (t.chart U ha z)) := by rw [hz]; exact hmax
    have hmz₀ : t.exceptional.stalkIdeal (t.chart U ha z₀) =
        maximalIdeal (t.X'.presheaf.stalk (t.chart U ha z₀)) := by rw [hz₀]; exact hmax₀
    have hzz : z = z₀ := by
      refine PrimeSpectrum.ext (Ideal.ext fun c => ?_)
      show c ∈ PrimeSpectrum.asIdeal z ↔ c ∈ PrimeSpectrum.asIdeal z₀
      obtain ⟨n, g, -, hg⟩ := (mem_chartAlgebra_iff ha).mp c.2
      have hcg : c * algebraMap Γ(X, U) (chartAlgebra (B.ideal U) a) a ^ n =
          algebraMap Γ(X, U) (chartAlgebra (B.ideal U) a) g := by
        apply Subtype.ext
        simp only [MulMemClass.coe_mul, SubmonoidClass.coe_pow, Subalgebra.coe_algebraMap]
        rw [hg, mul_assoc, ← mul_pow, mul_comm (IsLocalization.Away.invSelf a),
          IsLocalization.Away.mul_invSelf, one_pow, mul_one]
      rw [mem_asIdeal_chart_iff hX hBns t ha z hU hfz hmz c n g hcg,
        mem_asIdeal_chart_iff hX hBns t ha z₀ hU hfz₀ hmz₀ c n g hcg]
    rw [← hz, ← hz₀, hzz]
  -- hence `E = closure {η₀}`
  refine Subscheme.isIrreducible_of_pts _ ?_
  have hpts : t.exceptional.pts = closure {η₀} := by
    apply le_antisymm
    · intro y hy
      obtain ⟨η, hη, hgen, hηy⟩ := Subscheme.exists_maximalGeneric_specializes t.exceptional hy
      rw [huniq η hη hgen] at hηy
      exact specializes_iff_mem_closure.mp hηy
    · exact closure_minimal (Set.singleton_subset_iff.mpr hη₀) t.exceptional.support.isClosed
  rw [hpts]
  exact isIrreducible_singleton.closure

end MonoidalTransformation

end Hironaka

