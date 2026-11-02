/-
Copyright (c) 2026 Daattavya Aggarwal, Minhyong Kim, Oisin Kim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daattavya Aggarwal, Minhyong Kim, Oisin Kim
-/
module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.Order.CompletePartialOrder
public import Hironaka.Ch0.AlgebraicScheme
public import Hironaka.Compat.SubschemeStalk

/-!
# Compatibility layer: stalks of sheaves of ideals

Hironaka computes with sheaves of ideals through their stalks: the weak and strict transforms of
Ch. III §2 (Remarks 2–4, pp. 214–215), the division `f⁻¹(J)·P⁻ᵛ` of Ch. 0 §5 (p. 142) and the
saturation description of the strict transform (Ch. 0 §2, p. 130) are all stated or verified
stalkwise.  This file provides the stalk calculus for `Subscheme X = X.IdealSheafData`:

* the stalk at `x` is the image of the sections over any affine open containing `x`;
* stalks commute with suprema, products, powers and intersections of ideal sheaves, and an
  inequality of ideal sheaves may be checked on stalks;
* on an affine open the sections of an invertible sheaf of ideals form a finitely generated ideal,
  so the colon sheaf `(I : Pᵛ)` is a sheaf of ideals, with stalks `(I_x : P_xᵛ)`;
* consequently the largest `K` with `K Pᵛ ⊆ I` (the paper's `I P⁻ᵛ`) has stalks `(I_x : P_xᵛ)`,
  and the largest subscheme agreeing with `I` off `P` has stalks `⋃ₙ (I_x : P_xⁿ)`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open scoped nonZeroDivisors

namespace Hironaka

universe u

/-! ### Colon ideals and localization -/

/-- Localization commutes with colon ideals by finitely generated ideals:
`(I : J) A' = (I A' : J A')` for `A'` a localization of `A` and `J` finitely generated. -/
theorem Ideal.map_colon_of_isLocalization {A A' : Type*} [CommRing A] [CommRing A']
    [Algebra A A'] (M : Submonoid A) [IsLocalization M A'] (I J : Ideal A) (hJ : J.FG) :
    (I.colon (J : Set A)).map (algebraMap A A') =
      (I.map (algebraMap A A')).colon (J.map (algebraMap A A') : Set A') := by
  classical
  have hspan : ∀ K : Ideal A', (K.colon (J.map (algebraMap A A') : Set A')) =
      K.colon (algebraMap A A' '' (J : Set A)) := fun K => by
    rw [Ideal.map, Ideal.colon_span]
  apply le_antisymm
  · rw [Ideal.map_le_iff_le_comap]
    intro r hr
    rw [Ideal.mem_comap, hspan, Submodule.mem_colon]
    rintro _ ⟨j, hj, rfl⟩
    rw [smul_eq_mul, ← map_mul]
    exact Ideal.mem_map_of_mem _ ((Submodule.mem_colon.mp hr) j hj)
  · intro z hz
    rw [hspan, Submodule.mem_colon] at hz
    obtain ⟨T, rfl⟩ := hJ
    obtain ⟨⟨r, s⟩, hrs⟩ := IsLocalization.mk'_surjective M z
    simp only at hrs
    have H : ∀ t ∈ T, ∃ c : M, (c : A) * r * t ∈ I := by
      intro t ht
      have h1 := hz (algebraMap A A' t) ⟨t, Ideal.subset_span ht, rfl⟩
      rw [smul_eq_mul] at h1
      obtain ⟨⟨⟨a, ha⟩, m⟩, hm⟩ := (IsLocalization.mem_map_algebraMap_iff M A').mp h1
      simp only at hm
      rw [← hrs] at hm
      have h2 : algebraMap A A' (r * t * m) = algebraMap A A' (a * s) := by
        rw [map_mul, map_mul, map_mul, ← hm, ← IsLocalization.mk'_spec A' r s]
        ring
      obtain ⟨c, hc⟩ := (IsLocalization.eq_iff_exists M A').mp h2
      refine ⟨c * m, ?_⟩
      have : (c : A) * (a * s) ∈ I := I.mul_mem_left _ (I.mul_mem_right _ ha)
      rw [← hc] at this
      simp only [Submonoid.coe_mul]
      convert this using 1
      ring
    choose c hc using H
    let N : A := ∏ t ∈ T.attach, (c t.1 t.2 : A)
    have hN : N ∈ M := Submonoid.prod_mem _ fun t _ => (c t.1 t.2).2
    have hNr : N * r ∈ I.colon ((Ideal.span (T : Set A) : Ideal A) : Set A) := by
      rw [Ideal.colon_span, Submodule.mem_colon]
      intro t ht
      have hdvd : (c t ht : A) ∣ N := Finset.dvd_prod_of_mem (fun t : T => (c t.1 t.2 : A))
        (Finset.mem_attach T ⟨t, ht⟩)
      obtain ⟨k, hk⟩ := hdvd
      rw [smul_eq_mul, hk]
      convert I.mul_mem_left k (hc t ht) using 1
      ring
    rw [← hrs, IsLocalization.mk'_mem_map_algebraMap_iff M]
    exact ⟨N, hN, hNr⟩

/-! ### Sections of pulled-back sheaves of ideals

(Moved here from `Hironaka/Compat/BlowupCharts.lean`, where they were first proved, so that
Ch. 0 can use them.) -/

open Scheme.IdealSheafData in
theorem ideal_comap_top_of_isAffine {Y Z : Scheme.{u}} [IsAffine Y] [IsAffine Z] (g : Y ⟶ Z)
    (J : Z.IdealSheafData) :
    (J.comap g).ideal ⟨⊤, isAffineOpen_top Y⟩ =
      (J.ideal ⟨⊤, isAffineOpen_top Z⟩).map g.appTop.hom := by
  have hmap : ∀ K : Y.IdealSheafData, (K.map g).ideal ⟨⊤, isAffineOpen_top Z⟩ =
      (K.ideal ⟨⊤, isAffineOpen_top Y⟩).comap g.appTop.hom := fun K =>
    ideal_map K g ⟨⊤, isAffineOpen_top Z⟩ (isAffineOpen_top Y)
  apply le_antisymm
  · have : J.comap g ≤ ofIdealTop ((J.ideal ⟨⊤, isAffineOpen_top Z⟩).map g.appTop.hom) := by
      rw [← le_map_iff_comap_le]
      apply le_of_isAffine
      rw [hmap, ← Ideal.map_le_iff_le_comap]
      simp
    refine (this _).trans ?_
    simp
  · rw [Ideal.map_le_iff_le_comap, ← hmap]
    exact le_map_comap J g _

open Scheme.IdealSheafData in
theorem ideal_comap_ι_top {X : Scheme.{u}} (K : X.IdealSheafData) (W : X.affineOpens) :
    (K.comap W.1.ι).ideal ⟨⊤, isAffineOpen_top _⟩ = (K.ideal W).map W.1.topIso.inv.hom := by
  have hmem : W.1.ι ''ᵁ ⊤ ∈ X.affineOpens := (isAffineOpen_top _).image_of_isOpenImmersion _
  have hle : (⟨_, hmem⟩ : X.affineOpens) ≤ W := by
    show W.1.ι ''ᵁ ⊤ ≤ W.1
    rw [Scheme.Opens.ι_image_top]
  have e0 := ideal_comap_of_isOpenImmersion K W.1.ι ⟨⊤, isAffineOpen_top _⟩
  rw [Scheme.Opens.ι_appIso] at e0
  have e1 : (K.comap W.1.ι).ideal ⟨⊤, isAffineOpen_top _⟩ = K.ideal ⟨_, hmem⟩ := e0
  have e3 := K.map_ideal hle
  have e4 : W.1.topIso.inv = X.presheaf.map (homOfLE hle).op := by
    simp only [Scheme.Opens.topIso_inv]
    congr 1
  refine e1.trans (e3.symm.trans ?_)
  rw [e4]
  rfl

open Scheme.IdealSheafData in
theorem ideal_comap_eq_map_appLE {X X' : Scheme.{u}} (f : X' ⟶ X) (D : X.IdealSheafData)
    (U : X.affineOpens) (V : X'.affineOpens) (h : (V : X'.Opens) ≤ f ⁻¹ᵁ U) :
    (D.comap f).ideal V = (D.ideal U).map (f.appLE U V h).hom := by
  have key : (D.comap f).comap V.1.ι = (D.comap U.1.ι).comap (f.resLE U V h) := by
    rw [← comap_comp, ← comap_comp, Scheme.Hom.resLE_comp_ι]
  have e1 := congrArg (fun K => K.ideal ⟨⊤, isAffineOpen_top _⟩) key
  simp only at e1
  rw [ideal_comap_top_of_isAffine (f.resLE U V h), ideal_comap_ι_top, ideal_comap_ι_top] at e1
  have e2 := congrArg (Ideal.map V.1.topIso.hom.hom) e1
  rw [Ideal.map_map, Ideal.map_map, Ideal.map_map, ← CommRingCat.hom_comp,
    ← CommRingCat.hom_comp, ← CommRingCat.hom_comp, Iso.inv_hom_id, CommRingCat.hom_id,
    Ideal.map_id] at e2
  rw [e2]
  congr 2
  rw [Scheme.Hom.appTop, Scheme.Hom.resLE_app_top]
  simp only [Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id]

theorem appLE_germ {X X' : Scheme.{u}} (f : X' ⟶ X) (U : X.Opens) (V : X'.Opens)
    (h : V ≤ f ⁻¹ᵁ U) (y : X') (hy : y ∈ V) (hfy : f y ∈ U) :
    f.appLE U V h ≫ X'.presheaf.germ V y hy = X.presheaf.germ U (f y) hfy ≫ f.stalkMap y := by
  rw [Scheme.Hom.germ_stalkMap, Scheme.Hom.appLE, Category.assoc, TopCat.Presheaf.germ_res]

/-- A section all of whose germs are non-zero-divisors is a non-zero-divisor. -/
theorem mem_nonZeroDivisors_of_germ {Y : Scheme.{u}} {T : Y.Opens} {s : Γ(Y, T)}
    (h : ∀ (z : Y) (hz : z ∈ T), Y.presheaf.germ T z hz s ∈ (Y.presheaf.stalk z)⁰) :
    s ∈ Γ(Y, T)⁰ := by
  rw [mem_nonZeroDivisors_iff_right]
  intro x hx
  refine TopCat.Presheaf.section_ext Y.sheaf T x 0 fun z hz => ?_
  change Y.presheaf.germ T z hz x = Y.presheaf.germ T z hz 0
  have := congrArg (Y.presheaf.germ T z hz) hx
  rw [map_mul, map_zero] at this
  rw [map_zero]
  exact (mul_right_mem_nonZeroDivisors_eq_zero_iff (h z hz)).mp this

namespace Subscheme

variable {X : Scheme.{u}}

/-! ### Stalks through affine opens -/

/-- The stalk of a sheaf of ideals at `x` is the image of its sections over any affine open
containing `x`. -/
theorem stalkIdeal_eq_map_germ_affine (D : Subscheme X) (W : X.affineOpens) {x : X}
    (hx : x ∈ (W : X.Opens)) :
    D.stalkIdeal x = (D.ideal W).map (X.presheaf.germ W x hx).hom := by
  apply le_antisymm
  · refine Ideal.span_le.mpr ?_
    rintro _ ⟨U, hxU, s, hs, rfl⟩
    obtain ⟨f, g, hfg, hxf⟩ := exists_basicOpen_le_affine_inter U.2 W.2 x ⟨hxU, hx⟩
    have hOU : X.affineBasicOpen g ≤ U := by
      show X.basicOpen g ≤ U.1
      rw [← hfg]; exact X.basicOpen_le f
    have hxO : x ∈ ((X.affineBasicOpen g : X.affineOpens) : X.Opens) := by
      show x ∈ X.basicOpen g
      rw [← hfg]; exact hxf
    have h2 := D.ideal_le_comap_ideal hOU hs
    rw [Ideal.mem_comap, ← D.map_ideal (X.affineBasicOpen_le g)] at h2
    have h3 := Ideal.mem_map_of_mem
      (X.presheaf.germ ((X.affineBasicOpen g : X.affineOpens) : X.Opens) x hxO).hom h2
    rw [Ideal.map_map, ← CommRingCat.hom_comp, TopCat.Presheaf.germ_res'] at h3
    rw [← TopCat.Presheaf.germ_res_apply X.presheaf (homOfLE hOU) x hxO]
    exact h3
  · rw [Ideal.map_le_iff_le_comap]
    intro s hs
    exact Ideal.subset_span ⟨W, hx, s, hs, rfl⟩

/-- For a generization `η ⤳ y`, `D_η = D_y O_η`: the ideal at `η` is generated by the image of the ideal
at `y` under the specialization map. -/
theorem stalkIdeal_eq_map_stalkSpecializes (D : Subscheme X) {η y : X} (h : η ⤳ y) :
    D.stalkIdeal η = (D.stalkIdeal y).map (X.presheaf.stalkSpecializes h).hom := by
  obtain ⟨_, ⟨V, hV, rfl⟩, hyV, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ y) isOpen_univ
  have hηV : η ∈ V := h.mem_open V.isOpen hyV
  rw [stalkIdeal_eq_map_germ_affine D ⟨V, hV⟩ hyV, stalkIdeal_eq_map_germ_affine D ⟨V, hV⟩ hηV,
    Ideal.map_map, ← CommRingCat.hom_comp, TopCat.Presheaf.germ_stalkSpecializes]

theorem exists_affineOpen_mem (x : X) : ∃ W : X.affineOpens, x ∈ (W : X.Opens) := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  exact ⟨⟨U, hU⟩, hxU⟩

/-- An inequality of sheaves of ideals can be checked on stalks. -/
theorem le_iff_stalkIdeal_le {I J : Subscheme X} : I ≤ J ↔ ∀ x, I.stalkIdeal x ≤ J.stalkIdeal x := by
  constructor
  · intro h x
    obtain ⟨W, hx⟩ := exists_affineOpen_mem x
    rw [stalkIdeal_eq_map_germ_affine I W hx, stalkIdeal_eq_map_germ_affine J W hx]
    exact Ideal.map_mono (h W)
  · intro h
    rw [Scheme.IdealSheafData.le_def]
    intro W
    rw [W.2.ideal_le_iff]
    intro x hx
    rw [← stalkIdeal_eq_map_germ_affine I W hx, ← stalkIdeal_eq_map_germ_affine J W hx]
    exact h x

theorem ext_stalkIdeal {I J : Subscheme X} (h : ∀ x, I.stalkIdeal x = J.stalkIdeal x) : I = J :=
  le_antisymm (le_iff_stalkIdeal_le.mpr fun x => (h x).le)
    (le_iff_stalkIdeal_le.mpr fun x => (h x).ge)

theorem stalkIdeal_mono {I J : Subscheme X} (h : I ≤ J) (x : X) :
    I.stalkIdeal x ≤ J.stalkIdeal x :=
  le_iff_stalkIdeal_le.mp h x

/-- Stalks commute with suprema of sheaves of ideals. -/
theorem stalkIdeal_sSup_eq (S : Set (Subscheme X)) (x : X) :
    (sSup S).stalkIdeal x = ⨆ K ∈ S, K.stalkIdeal x := by
  obtain ⟨W, hx⟩ := exists_affineOpen_mem x
  rw [stalkIdeal_eq_map_germ_affine _ W hx, Scheme.IdealSheafData.ideal_sSup, sSup_image,
    iSup_apply]
  simp_rw [iSup_apply, Ideal.map_iSup, stalkIdeal_eq_map_germ_affine _ W hx]

theorem stalkIdeal_iSup_eq {ι : Type*} (K : ι → Subscheme X) (x : X) :
    (⨆ i, K i).stalkIdeal x = ⨆ i, (K i).stalkIdeal x := by
  rw [← sSup_range, stalkIdeal_sSup_eq, iSup_range]

theorem stalkIdeal_mul_eq (I J : Subscheme X) (x : X) :
    (I * J).stalkIdeal x = I.stalkIdeal x * J.stalkIdeal x := by
  obtain ⟨W, hx⟩ := exists_affineOpen_mem x
  rw [stalkIdeal_eq_map_germ_affine _ W hx, stalkIdeal_eq_map_germ_affine _ W hx,
    stalkIdeal_eq_map_germ_affine _ W hx, Scheme.IdealSheafData.ideal_mul, Pi.mul_apply,
    Ideal.map_mul]

theorem stalkIdeal_pow_eq (I : Subscheme X) (n : ℕ) (x : X) :
    (I ^ n).stalkIdeal x = I.stalkIdeal x ^ n := by
  obtain ⟨W, hx⟩ := exists_affineOpen_mem x
  rw [stalkIdeal_eq_map_germ_affine _ W hx, stalkIdeal_eq_map_germ_affine _ W hx,
    Scheme.IdealSheafData.ideal_pow, Pi.pow_apply, Ideal.map_pow]

theorem stalkIdeal_top_eq (x : X) : (⊤ : Subscheme X).stalkIdeal x = ⊤ := by
  obtain ⟨W, hx⟩ := exists_affineOpen_mem x
  rw [stalkIdeal_eq_map_germ_affine _ W hx, Scheme.IdealSheafData.ideal_top, Pi.top_apply,
    Ideal.map_top]

/-- Stalks commute with intersections of sheaves of ideals (localization is flat). -/
theorem stalkIdeal_inf_eq (I J : Subscheme X) (x : X) :
    (I ⊓ J).stalkIdeal x = I.stalkIdeal x ⊓ J.stalkIdeal x := by
  obtain ⟨W, hx⟩ := exists_affineOpen_mem x
  let := TopCat.Presheaf.algebra_section_stalk X.presheaf (⟨x, hx⟩ : (W : X.Opens))
  have := W.2.isLocalization_stalk ⟨x, hx⟩
  rw [stalkIdeal_eq_map_germ_affine _ W hx, stalkIdeal_eq_map_germ_affine _ W hx,
    stalkIdeal_eq_map_germ_affine _ W hx, Scheme.IdealSheafData.ideal_inf, Pi.inf_apply]
  exact IsLocalization.map_inf (S := X.presheaf.stalk x)
    (W.2.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl _ _

/-! ### Support -/

/-- Off the support of a subscheme the stalk of its ideal sheaf is the unit ideal. -/
theorem stalkIdeal_eq_top_of_notMem_pts {D : Subscheme X} {x : X}
    (hx : x ∉ D.pts) : D.stalkIdeal x = ⊤ := by
  have : ¬ ∀ U : X.affineOpens, x ∈ X.zeroLocus (U := U.1) (D.ideal U) := fun h =>
    hx (Scheme.IdealSheafData.mem_support_iff.mpr h)
  push Not at this
  obtain ⟨U, hU⟩ := this
  rw [Scheme.mem_zeroLocus_iff] at hU
  push Not at hU
  obtain ⟨f, hf, hxf⟩ := hU
  have hxU : x ∈ U.1 := X.basicOpen_le f hxf
  refine Ideal.eq_top_of_isUnit_mem _ (Ideal.subset_span ⟨U, hxU, f, hf, rfl⟩) ?_
  exact (Scheme.mem_basicOpen _ _ _ hxU).mp hxf

/-- At a point of the support, the stalk of the ideal sheaf lies in the maximal ideal. -/
theorem stalkIdeal_le_maximalIdeal (D : Subscheme X) {x : X} (hx : x ∈ D.pts) :
    D.stalkIdeal x ≤ IsLocalRing.maximalIdeal (X.presheaf.stalk x) := by
  refine Ideal.span_le.mpr ?_
  rintro a ⟨U, hxU, s, hs, rfl⟩
  have h1 := (Scheme.IdealSheafData.mem_support_iff.mp hx) U
  rw [Scheme.mem_zeroLocus_iff] at h1
  have h2 := h1 s hs
  rw [Scheme.mem_basicOpen _ _ _ hxU] at h2
  exact (IsLocalRing.mem_maximalIdeal _).mpr h2

/-- A point lies in the support of a subscheme iff the stalk of its ideal sheaf is proper. -/
theorem mem_pts_iff_stalkIdeal_ne_top {D : Subscheme X} {x : X} :
    x ∈ D.pts ↔ D.stalkIdeal x ≠ ⊤ := by
  refine ⟨fun hx h => ?_, fun h => by_contra fun hx => h (stalkIdeal_eq_top_of_notMem_pts hx)⟩
  have := stalkIdeal_le_maximalIdeal D hx
  rw [h, top_le_iff] at this
  exact IsLocalRing.maximalIdeal.isMaximal _ |>.ne_top this

/-! ### Invertible sheaves of ideals -/

/-- At every point, the stalk of an invertible sheaf of ideals is generated by a
non-zero-divisor. -/
theorem IsInvertibleIdeal.exists_stalkIdeal_eq_span {P : Subscheme X} (hP : P.IsInvertibleIdeal)
    (x : X) : ∃ g, P.stalkIdeal x = Ideal.span {g} ∧ g ∈ (X.presheaf.stalk x)⁰ := by
  obtain ⟨W, hxW, a, ha, hanzd⟩ := hP x
  let := TopCat.Presheaf.algebra_section_stalk X.presheaf (⟨x, hxW⟩ : (W : X.Opens))
  have hloc := W.2.isLocalization_stalk ⟨x, hxW⟩
  refine ⟨X.presheaf.germ W x hxW a, ?_, ?_⟩
  · rw [stalkIdeal_eq_map_germ_affine P W hxW, ha, Ideal.map_span, Set.image_singleton]
  · rw [mem_nonZeroDivisors_iff_right]
    intro z hz
    obtain ⟨⟨c, s⟩, rfl⟩ := IsLocalization.mk'_surjective
      (W.2.primeIdealOf ⟨x, hxW⟩).asIdeal.primeCompl z
    change IsLocalization.mk' _ c s * algebraMap Γ(X, W) _ a = 0 at hz
    rw [← IsLocalization.mk'_one (M := (W.2.primeIdealOf ⟨x, hxW⟩).asIdeal.primeCompl)
      (X.presheaf.stalk x) a, ← IsLocalization.mk'_mul, mul_one,
      IsLocalization.mk'_eq_zero_iff] at hz
    obtain ⟨m, hm⟩ := hz
    rw [IsLocalization.mk'_eq_zero_iff]
    refine ⟨m, (mul_right_mem_nonZeroDivisors_eq_zero_iff hanzd).mp ?_⟩
    rw [← hm]; ring

/-- On an affine open, the sections of an invertible sheaf of ideals form a finitely generated
ideal (it is locally principal and `U` is quasi-compact). -/
theorem IsInvertibleIdeal.ideal_fg {P : Subscheme X} (hP : P.IsInvertibleIdeal)
    (U : X.affineOpens) : (P.ideal U).FG := by
  let t : Set Γ(X, U) := {g | (P.ideal (X.affineBasicOpen g)).FG}
  have ht : Ideal.span t = ⊤ := by
    rw [← U.2.self_le_iSup_basicOpen_iff]
    intro x hx
    obtain ⟨W, hxW, a, ha, -⟩ := hP x
    obtain ⟨g, hgW, hxg⟩ := U.2.exists_basicOpen_le (V := W.1) ⟨x, hxW⟩ hx
    have hg : g ∈ t := by
      show (P.ideal (X.affineBasicOpen g)).FG
      rw [← P.map_ideal (show X.affineBasicOpen g ≤ W from hgW), ha, Ideal.map_span,
        Set.image_singleton]
      exact Submodule.fg_span_singleton _
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨g, hg⟩, hxg⟩
  apply Ideal.fg_of_localizationSpan t ht
  rintro ⟨g, hg⟩
  have := U.2.isLocalization_basicOpen g
  let e := IsLocalization.algEquiv (Submonoid.powers g) Γ(X, X.basicOpen g) (Localization.Away g)
  have h1 : algebraMap Γ(X, U) (Localization.Away g) =
      (e : Γ(X, X.basicOpen g) →+* Localization.Away g).comp
        (algebraMap Γ(X, U) Γ(X, X.basicOpen g)) := by
    ext r
    exact (e.commutes r).symm
  have h2 : (P.ideal U).map (algebraMap Γ(X, U) Γ(X, X.basicOpen g)) =
      P.ideal (X.affineBasicOpen g) := P.map_ideal_basicOpen U g
  rw [h1, ← Ideal.map_map]
  refine Ideal.FG.map ?_ _
  rw [h2]
  exact hg

/-! ### The colon sheaf -/

/-- The colon sheaf of ideals `(I : J)` for a sheaf of ideals `J` whose sections over affine
opens are finitely generated: its sections over an affine open `U` are `(I(U) : J(U))`. -/
noncomputable def colonOfFG (I J : Subscheme X) (hJ : ∀ U, (J.ideal U).FG) : Subscheme X where
  ideal U := (I.ideal U).colon (J.ideal U : Set Γ(X, U))
  map_ideal_basicOpen U f := by
    have := U.2.isLocalization_basicOpen f
    rw [← I.map_ideal_basicOpen U f, ← J.map_ideal_basicOpen U f]
    exact Ideal.map_colon_of_isLocalization (Submonoid.powers f) _ _ (hJ U)

theorem stalkIdeal_colonOfFG (I J : Subscheme X) (hJ : ∀ U, (J.ideal U).FG) (x : X) :
    (colonOfFG I J hJ).stalkIdeal x =
      (I.stalkIdeal x).colon (J.stalkIdeal x : Set (X.presheaf.stalk x)) := by
  obtain ⟨W, hx⟩ := exists_affineOpen_mem x
  let := TopCat.Presheaf.algebra_section_stalk X.presheaf (⟨x, hx⟩ : (W : X.Opens))
  have := W.2.isLocalization_stalk ⟨x, hx⟩
  rw [stalkIdeal_eq_map_germ_affine _ W hx, stalkIdeal_eq_map_germ_affine I W hx,
    stalkIdeal_eq_map_germ_affine J W hx]
  exact Ideal.map_colon_of_isLocalization (W.2.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl _ _
    (hJ W)

/-- The stalks of the largest `K` with `K Pᵛ ⊆ I` (checked on stalks), `P` invertible, are the
colon ideals `(I_x : P_xᵛ)` (Ch. 0 §5, p. 142: "the sheaf of ideals obtained by this
division"). -/
theorem stalkIdeal_sSup_mul_pow_le {I P : Subscheme X} (hP : P.IsInvertibleIdeal) (ν : ℕ)
    (x : X) :
    (sSup {K : Subscheme X | ∀ z, K.stalkIdeal z * P.stalkIdeal z ^ ν ≤ I.stalkIdeal z}).stalkIdeal x
      = (I.stalkIdeal x).colon ((P.stalkIdeal x ^ ν : Ideal _) : Set (X.presheaf.stalk x)) := by
  apply le_antisymm
  · rw [stalkIdeal_sSup_eq]
    refine iSup₂_le fun K hK => fun k hk => Submodule.mem_colon.mpr fun p hp => ?_
    exact hK x (Ideal.mul_mem_mul hk hp)
  · have hfg : ∀ U, ((P ^ ν).ideal U).FG := fun U => by
      rw [Scheme.IdealSheafData.ideal_pow, Pi.pow_apply]
      exact (hP.ideal_fg U).pow
    have hmem : colonOfFG I (P ^ ν) hfg ∈
        {K : Subscheme X | ∀ z, K.stalkIdeal z * P.stalkIdeal z ^ ν ≤ I.stalkIdeal z} := by
      intro z
      rw [stalkIdeal_colonOfFG, stalkIdeal_pow_eq, Ideal.mul_le]
      intro c hc p hp
      exact Submodule.mem_colon.mp hc p hp
    have := stalkIdeal_mono (le_sSup hmem) x
    rwa [stalkIdeal_colonOfFG, stalkIdeal_pow_eq] at this

/-- The stalks of the largest subscheme agreeing with `I` off the support of the invertible
sheaf of ideals `E` are the saturations `⋃ₙ (I_x : E_xⁿ)` (Ch. 0 §2, p. 130). -/
theorem stalkIdeal_sSup_eq_off {I E : Subscheme X} (hE : E.IsInvertibleIdeal) (x : X) :
    (sSup {V : Subscheme X | ∀ z, z ∉ E.pts → V.stalkIdeal z = I.stalkIdeal z}).stalkIdeal x
      = ⨆ n : ℕ, (I.stalkIdeal x).colon
          ((E.stalkIdeal x ^ n : Ideal _) : Set (X.presheaf.stalk x)) := by
  set S := {V : Subscheme X | ∀ z, z ∉ E.pts → V.stalkIdeal z = I.stalkIdeal z}
  set D : ℕ → Subscheme X := fun n =>
    sSup {K : Subscheme X | ∀ z, K.stalkIdeal z * E.stalkIdeal z ^ n ≤ I.stalkIdeal z}
  have hD : ∀ n z, (D n).stalkIdeal z = (I.stalkIdeal z).colon
      ((E.stalkIdeal z ^ n : Ideal _) : Set (X.presheaf.stalk z)) :=
    fun n z => stalkIdeal_sSup_mul_pow_le hE n z
  apply le_antisymm
  · rw [stalkIdeal_sSup_eq]
    refine iSup₂_le fun V hV => ?_
    obtain ⟨W, hxW, s, hs, hsnzd⟩ := hE x
    rw [stalkIdeal_eq_map_germ_affine V W hxW, Ideal.map_le_iff_le_comap]
    intro h hh
    rw [Ideal.mem_comap]
    -- on `D(s) ⊆ W`, which misses `E`, the sections of `V` and `I` agree
    have hVD : V.ideal (X.affineBasicOpen s) = I.ideal (X.affineBasicOpen s) := by
      rw [(X.affineBasicOpen s).2.ideal_ext_iff]
      intro z hz
      rw [← stalkIdeal_eq_map_germ_affine V _ hz, ← stalkIdeal_eq_map_germ_affine I _ hz]
      refine hV z fun hzE => mem_pts_iff_stalkIdeal_ne_top.mp hzE ?_
      have hzW : z ∈ (W : X.Opens) := X.basicOpen_le s hz
      rw [stalkIdeal_eq_map_germ_affine E W hzW, hs, Ideal.map_span, Set.image_singleton]
      exact Ideal.span_singleton_eq_top.mpr ((Scheme.mem_basicOpen _ _ _ hzW).mp hz)
    have hres : X.presheaf.map (homOfLE (X.basicOpen_le s)).op h ∈
        (I.ideal W).map (X.presheaf.map (homOfLE (X.basicOpen_le s)).op).hom := by
      rw [I.map_ideal_basicOpen W s, ← hVD, ← V.map_ideal_basicOpen W s]
      exact Ideal.mem_map_of_mem _ hh
    have := W.2.isLocalization_basicOpen s
    obtain ⟨⟨⟨a, ha⟩, ⟨_, n, rfl⟩⟩, hna⟩ :=
      (IsLocalization.mem_map_algebraMap_iff (Submonoid.powers s) Γ(X, X.basicOpen s)).mp hres
    simp only at hna
    have h1 : algebraMap Γ(X, W) Γ(X, X.basicOpen s) (h * s ^ n) =
        algebraMap Γ(X, W) Γ(X, X.basicOpen s) a := by
      rw [map_mul]; exact hna
    obtain ⟨⟨_, k, rfl⟩, hk⟩ := (IsLocalization.eq_iff_exists (Submonoid.powers s) _).mp h1
    simp only at hk
    have hmem : h * s ^ (n + k) ∈ I.ideal W := by
      rw [pow_add, ← mul_assoc, mul_comm _ (s ^ k), hk]
      exact (I.ideal W).mul_mem_left _ ha
    have hE' : E.stalkIdeal x = Ideal.span {X.presheaf.germ W x hxW s} := by
      rw [stalkIdeal_eq_map_germ_affine E W hxW, hs, Ideal.map_span, Set.image_singleton]
    refine Ideal.mem_iSup_of_mem (n + k) (Submodule.mem_colon.mpr fun p hp => ?_)
    rw [hE', Ideal.span_singleton_pow, SetLike.mem_coe, Ideal.mem_span_singleton'] at hp
    obtain ⟨c, rfl⟩ := hp
    rw [stalkIdeal_eq_map_germ_affine I W hxW, smul_eq_mul]
    have := Ideal.mem_map_of_mem (X.presheaf.germ W x hxW).hom hmem
    rw [map_mul, map_pow] at this
    convert (Ideal.map _ (I.ideal W)).mul_mem_left c this using 1
    ring
  · have hmem : (⨆ n, D n) ∈ S := by
      intro z hz
      rw [stalkIdeal_iSup_eq]
      simp only [hD, stalkIdeal_eq_top_of_notMem_pts hz, Ideal.top_pow, Submodule.top_coe,
        Submodule.colon_univ, iSup_const]
    have := stalkIdeal_mono (le_sSup hmem) x
    rwa [stalkIdeal_iSup_eq, show (fun n => (D n).stalkIdeal x) = fun n => (I.stalkIdeal x).colon
      ((E.stalkIdeal x ^ n : Ideal _) : Set (X.presheaf.stalk x)) from funext fun n => hD n x]
      at this

/-! ### Pull-backs -/

theorem stalkIdeal_bot_eq (x : X) : (⊥ : Subscheme X).stalkIdeal x = ⊥ := by
  obtain ⟨W, hx⟩ := exists_affineOpen_mem x
  rw [stalkIdeal_eq_map_germ_affine _ W hx, Scheme.IdealSheafData.ideal_bot, Pi.bot_apply,
    Ideal.map_bot]

/-- The stalk of the pull-back `f⁻¹(D)` of a sheaf of ideals is generated by that of `D`. -/
theorem stalkIdeal_comap {X' : Scheme.{u}} (D : Subscheme X) (f : X' ⟶ X) (y : X') :
    Subscheme.stalkIdeal (D.comap f) y = (D.stalkIdeal (f y)).map (f.stalkMap y).hom := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hyU, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (f y)) isOpen_univ
  obtain ⟨_, ⟨V, hV, rfl⟩, hyV, hVU⟩ := X'.isBasis_affineOpens.exists_subset_of_mem_open
    (show y ∈ f ⁻¹ᵁ U from hyU) (f ⁻¹ᵁ U).isOpen
  have hVU' : V ≤ f ⁻¹ᵁ U := hVU
  rw [stalkIdeal_eq_map_germ_affine _ ⟨V, hV⟩ hyV, stalkIdeal_eq_map_germ_affine _ ⟨U, hU⟩ hyU,
    ideal_comap_eq_map_appLE f D ⟨U, hU⟩ ⟨V, hV⟩ hVU', Ideal.map_map, Ideal.map_map,
    ← CommRingCat.hom_comp, ← CommRingCat.hom_comp, appLE_germ f U V hVU' y hyV hyU]

/-- If `a = u b` with `b` a non-zero-divisor generating the same principal ideal, then `a` is a
non-zero-divisor. -/
theorem mem_nonZeroDivisors_of_span_eq {A : Type*} [CommRing A] {a b : A}
    (h : Ideal.span {a} = Ideal.span {b}) (hb : b ∈ A⁰) : a ∈ A⁰ := by
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp (h ▸ Ideal.mem_span_singleton_self b :
    b ∈ Ideal.span {a})
  obtain ⟨d, hd⟩ := Ideal.mem_span_singleton'.mp (h ▸ Ideal.mem_span_singleton_self a :
    a ∈ Ideal.span {b})
  rw [mem_nonZeroDivisors_iff_right]
  intro z hz
  have h1 : z * b = 0 := by rw [← hc, mul_comm c, ← mul_assoc, hz, zero_mul]
  exact (mul_right_mem_nonZeroDivisors_eq_zero_iff hb).mp h1

/-- The pull-back of an invertible sheaf of ideals `E` to a closed subscheme `K` is invertible,
provided `K` is saturated with respect to `E` (i.e. `(K_x : E_x) = K_x` for all `x`): a local
generator of `E` stays a non-zero-divisor modulo `K`. -/
theorem IsInvertibleIdeal.comap_subschemeι {E K : Subscheme X} (hE : E.IsInvertibleIdeal)
    (hsat : ∀ x, (K.stalkIdeal x).colon (E.stalkIdeal x : Set (X.presheaf.stalk x)) ≤
      K.stalkIdeal x) :
    Subscheme.IsInvertibleIdeal (E.comap K.subschemeι) := by
  intro w
  obtain ⟨W, hxW, s, hs, -⟩ := hE (K.subschemeι w)
  have hWa : IsAffineOpen (K.subschemeι ⁻¹ᵁ (W : X.Opens)) := W.2.preimage K.subschemeι
  refine ⟨⟨_, hWa⟩, hxW, K.subschemeι.appLE W.1 (K.subschemeι ⁻¹ᵁ W.1) le_rfl s, ?_, ?_⟩
  · rw [ideal_comap_eq_map_appLE K.subschemeι E W ⟨_, hWa⟩ le_rfl, hs, Ideal.map_span,
      Set.image_singleton]
  · apply mem_nonZeroDivisors_of_germ
    intro z hz
    have hz' : K.subschemeι z ∈ (W : X.Opens) := hz
    rw [← CommRingCat.comp_apply, appLE_germ K.subschemeι W.1 _ le_rfl z hz hz',
      CommRingCat.comp_apply]
    rw [mem_nonZeroDivisors_iff_right]
    intro c hc
    obtain ⟨d, rfl⟩ := K.subschemeι.stalkMap_surjective z c
    rw [← map_mul] at hc
    have hker := stalkIdeal_eq_ker_stalkMap K z
    have h1 : d * X.presheaf.germ W (K.subschemeι z) hz' s ∈ K.stalkIdeal (K.subschemeι z) := by
      rw [hker]; exact hc
    have h2 : d ∈ K.stalkIdeal (K.subschemeι z) := by
      refine hsat _ (Submodule.mem_colon.mpr fun p hp => ?_)
      rw [stalkIdeal_eq_map_germ_affine E W hz', hs, Ideal.map_span, Set.image_singleton,
        SetLike.mem_coe, Ideal.mem_span_singleton'] at hp
      obtain ⟨c, rfl⟩ := hp
      rw [smul_eq_mul, show d * (c * X.presheaf.germ W (K.subschemeι z) hz' s) =
        c * (d * X.presheaf.germ W (K.subschemeι z) hz' s) by ring]
      exact Ideal.mul_mem_left _ _ h1
    rw [hker] at h2
    exact h2

end Subscheme

end Hironaka

