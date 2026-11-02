/-
Copyright (c) 2026 Daattavya Aggarwal, Minhyong Kim, Oisin Kim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daattavya Aggarwal, Minhyong Kim, Oisin Kim
-/
module

public import Hironaka.Ch0.Blowup
public import Hironaka.Compat.BlowupCharts

/-!
# Algebra of invertible sheaves of ideals, for the composition of monoidal transformations

Ch. 0 §3 (p. 133) composes two monoidal transformations into one; the proof of the printed
"we can then easily see" uses the following facts about sheaves of ideals, none of which
Hironaka states:

* the total transform is multiplicative: `f⁻¹(I K) = f⁻¹(I) f⁻¹(K)` and `f⁻¹(Iⁿ) = f⁻¹(I)ⁿ`;
* products and powers of invertible sheaves of ideals are invertible;
* a factor of an invertible product is invertible;
* the total transform of an invertible sheaf of ideals by a monoidal transformation is invertible.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open scoped nonZeroDivisors

namespace Hironaka

universe u

/-! ### Affine covers adapted to a morphism -/

section Cover

variable {X X' : Scheme.{u}} (f : X' ⟶ X)

/-- The affine opens of `X'` lying over some affine open of `X` cover `X'`. -/
theorem iSup_affineOpens_le_preimage :
    ⨆ i : {V : X'.affineOpens // ∃ U : X.affineOpens, (V : X'.Opens) ≤ f ⁻¹ᵁ U},
      ((i.1 : X'.affineOpens) : X'.Opens) = ⊤ := by
  refine eq_top_iff.mpr fun x _ => ?_
  obtain ⟨U, hU⟩ := Subscheme.exists_affineOpen_mem (f x)
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVU⟩ := X'.isBasis_affineOpens.exists_subset_of_mem_open
    (show x ∈ f ⁻¹ᵁ (U : X.Opens) from hU) (f ⁻¹ᵁ (U : X.Opens)).isOpen
  exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨⟨V, hV⟩, U, hVU⟩, hxV⟩

/-- The total transform is multiplicative. -/
theorem Subscheme.totalTransform_mul (I K : Subscheme X) :
    Subscheme.totalTransform f (I * K) =
      Subscheme.totalTransform f I * Subscheme.totalTransform f K := by
  refine Scheme.IdealSheafData.ext_of_iSup_eq_top (fun i : {V : X'.affineOpens // ∃ U : X.affineOpens, (V : X'.Opens) ≤ f ⁻¹ᵁ U} => i.1)
    (iSup_affineOpens_le_preimage f) ?_
  rintro ⟨V, U, hVU⟩
  change ((I * K).comap f).ideal V = ((I.comap f) * (K.comap f)).ideal V
  rw [ideal_comap_eq_map_appLE f _ U V hVU]
  change _ = (I.comap f).ideal V * (K.comap f).ideal V
  rw [ideal_comap_eq_map_appLE f _ U V hVU, ideal_comap_eq_map_appLE f _ U V hVU]
  exact Ideal.map_mul _ _ _

/-- The total transform of a power is the power of the total transform. -/
theorem Subscheme.totalTransform_pow (I : Subscheme X) (n : ℕ) :
    Subscheme.totalTransform f (I ^ n) = Subscheme.totalTransform f I ^ n := by
  induction n with
  | zero => simpa using Subscheme.totalTransform_top f
  | succ n ih => rw [pow_succ, Subscheme.totalTransform_mul, ih, pow_succ]

end Cover

/-! ### Restriction of generators to smaller affine opens -/

section Restrict

variable {X : Scheme.{u}}

/-- A section of an affine open that is a non-zero-divisor has non-zero-divisor germs. -/
theorem germ_mem_nonZeroDivisors_of_isAffineOpen {V : X.affineOpens} {s : Γ(X, V)}
    (hs : s ∈ Γ(X, V)⁰) (z : X) (hz : z ∈ (V : X.Opens)) :
    X.presheaf.germ V z hz s ∈ (X.presheaf.stalk z)⁰ := by
  let := TopCat.Presheaf.algebra_section_stalk X.presheaf (⟨z, hz⟩ : (V : X.Opens))
  have := V.2.isLocalization_stalk ⟨z, hz⟩
  exact algebraMap_mem_nonZeroDivisors_of_isLocalization (S := X.presheaf.stalk z)
    (V.2.primeIdealOf ⟨z, hz⟩).asIdeal.primeCompl hs

/-- The restriction of a non-zero-divisor to a smaller affine open is a non-zero-divisor. -/
theorem res_mem_nonZeroDivisors_of_le {W V : X.affineOpens} (h : (W : X.Opens) ≤ V) {s : Γ(X, V)}
    (hs : s ∈ Γ(X, V)⁰) :
    X.presheaf.map (homOfLE h).op s ∈ Γ(X, W)⁰ :=
  mem_nonZeroDivisors_of_germ fun z hz => by
    rw [TopCat.Presheaf.germ_res_apply]
    exact germ_mem_nonZeroDivisors_of_isAffineOpen hs z _

/-- A principal ideal sheaf generated on `V` by `s` is generated on a smaller affine open by the
restriction of `s`. -/
theorem Subscheme.ideal_eq_span_res {D : Subscheme X} {W V : X.affineOpens} (h : W ≤ V)
    {s : Γ(X, V)} (hs : D.ideal V = Ideal.span {s}) :
    D.ideal W = Ideal.span {X.presheaf.map (homOfLE h).op s} := by
  rw [← D.map_ideal h, hs, Ideal.map_span, Set.image_singleton]

/-- Two affine neighbourhoods of `x` contain a common affine neighbourhood of `x`. -/
theorem exists_affineOpen_le_inter (U V : X.affineOpens) {x : X} (hU : x ∈ (U : X.Opens))
    (hV : x ∈ (V : X.Opens)) :
    ∃ W : X.affineOpens, x ∈ (W : X.Opens) ∧ W ≤ U ∧ W ≤ V := by
  obtain ⟨f, g, hfg, hxf⟩ := exists_basicOpen_le_affine_inter U.2 V.2 x ⟨hU, hV⟩
  refine ⟨affBasicOpen U f, hxf, X.basicOpen_le f, ?_⟩
  show X.basicOpen f ≤ V.1
  rw [hfg]; exact X.basicOpen_le g

end Restrict

namespace Subscheme

variable {X : Scheme.{u}}

/-- A product of invertible sheaves of ideals is invertible. -/
theorem IsInvertibleIdeal.mul {I K : Subscheme X} (hI : I.IsInvertibleIdeal)
    (hK : K.IsInvertibleIdeal) : (I * K).IsInvertibleIdeal := by
  intro x
  obtain ⟨U, hxU, a, ha, hanzd⟩ := hI x
  obtain ⟨V, hxV, b, hb, hbnzd⟩ := hK x
  obtain ⟨W, hxW, hWU, hWV⟩ := exists_affineOpen_le_inter U V hxU hxV
  refine ⟨W, hxW, X.presheaf.map (homOfLE hWU).op a * X.presheaf.map (homOfLE hWV).op b, ?_,
    Submonoid.mul_mem _ (res_mem_nonZeroDivisors_of_le hWU hanzd)
      (res_mem_nonZeroDivisors_of_le hWV hbnzd)⟩
  change I.ideal W * K.ideal W = _
  rw [ideal_eq_span_res hWU ha, ideal_eq_span_res hWV hb, Ideal.span_singleton_mul_span_singleton]

/-- A power of an invertible sheaf of ideals is invertible. -/
theorem IsInvertibleIdeal.pow {I : Subscheme X} (hI : I.IsInvertibleIdeal) (n : ℕ) :
    (I ^ n).IsInvertibleIdeal := by
  induction n with
  | zero => simpa using isInvertibleIdeal_top (X := X)
  | succ n ih => rw [pow_succ]; exact ih.mul hI

/-- A factor of an invertible product of sheaves of ideals is invertible.

At a point `x`, with `(I K)(U) = (c)`, `c` a non-zero-divisor: if every product `a b`,
`a ∈ I(U)`, `b ∈ K(U)`, were `c r` with `r` in the prime `p` of `x`, then `c ∈ c p` and
`1 ∈ p`; so some `a b = c r` has `r ∉ p`.  On `D(r)` the ideal `I` is generated by `a`, since
`a' b = c s` gives `a' r = a s`, and `a` is a non-zero-divisor because `a b = c r` is. -/
theorem IsInvertibleIdeal.of_mul_left {I K : Subscheme X} (h : (I * K).IsInvertibleIdeal) :
    I.IsInvertibleIdeal := by
  intro x
  obtain ⟨U, hxU, c, hc, hcnzd⟩ := h x
  change I.ideal U * K.ideal U = Ideal.span {c} at hc
  set p : Ideal Γ(X, U) := (IsLocalRing.maximalIdeal (X.presheaf.stalk x)).comap
    (X.presheaf.germ U x hxU).hom with hp
  have key : ∃ a ∈ I.ideal U, ∃ b ∈ K.ideal U, ∃ r, r ∉ p ∧ a * b = c * r := by
    by_contra hcon
    push Not at hcon
    have hle : I.ideal U * K.ideal U ≤ Ideal.span {c} * p := by
      rw [Ideal.mul_le]
      intro a ha b hb
      have hab : a * b ∈ Ideal.span {c} := hc ▸ Ideal.mul_mem_mul ha hb
      obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.mp hab
      refine Ideal.mem_span_singleton_mul.mpr ⟨r, ?_, by rw [mul_comm]; exact hr⟩
      by_contra hrp
      exact hcon a ha b hb r hrp (by rw [← hr, mul_comm])
    have hcmem : c ∈ Ideal.span {c} * p := hle (hc ▸ Ideal.mem_span_singleton_self c)
    obtain ⟨t, ht, hct⟩ := Ideal.mem_span_singleton_mul.mp hcmem
    have h1 : c * (t - 1) = 0 := by rw [mul_sub, hct, mul_one, sub_self]
    have h2 : t = 1 := sub_eq_zero.mp ((mul_left_mem_nonZeroDivisors_eq_zero_iff hcnzd).mp h1)
    rw [h2] at ht
    have h3 : (1 : Γ(X, U)) ∈ p := ht
    rw [hp, Ideal.mem_comap, map_one] at h3
    exact (IsLocalRing.maximalIdeal.isMaximal _).ne_top ((Ideal.eq_top_iff_one _).mpr h3)
  obtain ⟨a, ha, b, hb, r, hr, hab⟩ := key
  have hxr : x ∈ X.basicOpen r := by
    refine (Scheme.mem_basicOpen _ _ _ hxU).mpr ?_
    simpa [hp, Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] using hr
  have hle : (affBasicOpen U r : X.affineOpens) ≤ U := X.basicOpen_le r
  have hunit : IsUnit (X.presheaf.map (homOfLE (X.basicOpen_le r)).op r) :=
    X.toRingedSpace.isUnit_res_basicOpen r
  set ρ : Γ(X, U) →+* Γ(X, X.basicOpen r) := (X.presheaf.map (homOfLE (X.basicOpen_le r)).op).hom
  refine ⟨affBasicOpen U r, hxr, ρ a, ?_, ?_⟩
  · rw [← I.map_ideal hle]
    apply le_antisymm
    · rw [Ideal.map_le_iff_le_comap]
      intro a' ha'
      have hab' : a' * b ∈ Ideal.span {c} := hc ▸ Ideal.mul_mem_mul ha' hb
      obtain ⟨s, hs⟩ := Ideal.mem_span_singleton'.mp hab'
      have h1 : c * (a' * r - a * s) = 0 := by
        have : a' * (a * b) = a * (a' * b) := by ring
        rw [hab, ← hs] at this
        linear_combination this
      have h2 : a' * r = a * s :=
        sub_eq_zero.mp ((mul_left_mem_nonZeroDivisors_eq_zero_iff hcnzd).mp h1)
      obtain ⟨u, hu⟩ := hunit
      rw [Ideal.mem_comap, Ideal.mem_span_singleton']
      refine ⟨ρ s * ↑u⁻¹, ?_⟩
      have h3 : ρ a' * ρ r = ρ a * ρ s := by rw [← map_mul, ← map_mul, h2]
      have h4 : (ρ r : Γ(X, X.basicOpen r)) = u := hu.symm
      calc ρ s * ↑u⁻¹ * ρ a = ρ a * ρ s * ↑u⁻¹ := by ring
        _ = ρ a' * ρ r * ↑u⁻¹ := by rw [h3]
        _ = ρ a' := by rw [h4]; simp
    · rw [Ideal.span_le, Set.singleton_subset_iff]
      exact Ideal.mem_map_of_mem _ ha
  · have hprod : ρ a * ρ b ∈ Γ(X, X.basicOpen r)⁰ := by
      rw [← map_mul, hab, map_mul]
      exact Submonoid.mul_mem _ (res_mem_nonZeroDivisors_of_le hle hcnzd)
        hunit.mem_nonZeroDivisors
    exact (mul_mem_nonZeroDivisors.mp hprod).1

end Subscheme

namespace MonoidalTransformation

variable {X : Scheme.{u}} {B : Subscheme X} (t : MonoidalTransformation X B)

/-- The image of a non-zero-divisor of `A` in the chart ring `A[I/a] ⊆ A_a` is a
non-zero-divisor. -/
theorem algebraMap_mem_nonZeroDivisors_chartAlgebra_of_mem {A : Type*} [CommRing A] {I : Ideal A}
    {a e : A} (he : e ∈ A⁰) : algebraMap A (chartAlgebra I a) e ∈ (chartAlgebra I a)⁰ := by
  rw [mem_nonZeroDivisors_iff_right]
  intro x hx
  have h1 := algebraMap_mem_nonZeroDivisors_of_isLocalization (S := Localization.Away a)
    (Submonoid.powers a) he
  have hx' : (x : Localization.Away a) * algebraMap A (Localization.Away a) e = 0 :=
    congrArg Subtype.val hx
  exact Subtype.ext ((mem_nonZeroDivisors_iff_right.mp h1) _ hx')

/-- The total transform of an invertible sheaf of ideals by a monoidal transformation is
invertible.  (Used on p. 133 for `f₁⁻¹(f₀⁻¹(J₀))`.)  At a point of a chart `V_a` over an affine
open `U` on which `E = (e)`, the pull-back of `e` to the chart ring `A[I/a] ⊆ A_a` is a
non-zero-divisor, since `A → A_a` is a localization. -/
theorem isInvertibleIdeal_totalTransform {E : Subscheme X} (hE : E.IsInvertibleIdeal) :
    (Subscheme.totalTransform t.f E).IsInvertibleIdeal := by
  intro y
  obtain ⟨U, hfy, e, he, henzd⟩ := hE (t.f y)
  obtain ⟨a, ha, hya⟩ := t.exists_mem_chartOpen U hfy
  obtain ⟨W, hW, hyW⟩ := (t.mem_chartOpen_iff U).mp hya
  have hWU : (W : t.X'.Opens) ≤ t.f ⁻¹ᵁ U := hW.1
  refine ⟨W, hyW, t.f.appLE U W hWU e, ?_, ?_⟩
  · change (E.comap t.f).ideal W = _
    rw [ideal_comap_eq_map_appLE t.f E U W hWU, he, Ideal.map_span, Set.image_singleton]
  · refine mem_nonZeroDivisors_of_germ fun z hz => ?_
    have hz' : z ∈ t.chartOpen U a := (t.mem_chartOpen_iff U).mpr ⟨W, hW, hz⟩
    have hz'' : z ∈ Set.range (t.chart U ha) := by rw [t.range_chart U ha]; exact hz'
    obtain ⟨z', rfl⟩ := hz''
    have := t.isOpenImmersion_chart U ha
    have hsq := appLE_germ_stalkMap (t.chart U ha) t.f U.1 W hWU z' hz (chartToBase B U a)
      (t.chart_f U ha) (chartToBase_preimage B U a).ge
    have hge := congrArg (fun φ => φ e) (congrArg CommRingCat.Hom.hom hsq)
    simp only [CommRingCat.hom_comp, RingHom.comp_apply] at hge
    have hnz : (chartToBase B U a).appLE U.1 ⊤ (chartToBase_preimage B U a).ge e ∈
        Γ(Spec (chartRing B U a), ⊤)⁰ := by
      rw [chartToBase_appLE]
      exact iso_hom_mem_nonZeroDivisors (Scheme.ΓSpecIso (chartRing B U a)).symm
        (algebraMap_mem_nonZeroDivisors_chartAlgebra_of_mem henzd)
    have hnz2 := germ_mem_nonZeroDivisors_of_isAffine hnz z'
    rw [← hge] at hnz2
    have h5 := isIso_mem_nonZeroDivisors (inv ((t.chart U ha).stalkMap z')) hnz2
    rwa [← CommRingCat.comp_apply, IsIso.hom_inv_id, CommRingCat.id_apply] at h5

end MonoidalTransformation

end Hironaka
