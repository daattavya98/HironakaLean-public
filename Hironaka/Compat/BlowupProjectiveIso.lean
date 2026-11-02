/-
Copyright (c) 2026 Daattavya Aggarwal, Minhyong Kim, Oisin Kim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daattavya Aggarwal, Minhyong Kim, Oisin Kim
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.IsIso
public import Architect
public import Hironaka.Compat.BlowupCharts
public import Hironaka.Compat.BlowupProjectiveMaps

/-!
# A blow-up of `Proj H` is `Proj H'` (step L1d of the p. 132 lemma)

Step L1d of the proof of `MonoidalTransformation.isProjectiveOver` (`Hironaka/Compat/BlowupProjective.lean`, the
unproved, uncited step "a monoidal transformation of a projective scheme is projective" of the Corollary on p. 132).
Let `H = B[T₀, …, T_{n-1}] ⧸ 𝔭` (`𝔭` homogeneous prime), `D` a subscheme of `Proj H` and `t` a monoidal transformation
of `Proj H` with center `D`.  With the forms `g_a` of step L1a and the ring `H'` of step L1b, this file shows
`t.X' ≅ Proj H'` over `Spec B`:

* `exists_mem_chartOpen_of_span`: the charts `V_{γ}` of `t` (`BlowupCharts`) for generators `γ` of the ideal of the
  center already cover `f⁻¹(U)`;
* `blowupGlue : Proj H' ⟶ t.X'`, glued (`Scheme.OpenCover.glueMorphisms`) from `Spec θ_{ab} ≫ t.chart`, where
  `θ_{ab} : Γ(D₊(u_b))[I/γ_{ab}] ≅ H'_(y_{ab})` (`exists_theta`);
* the gluing condition is the uniqueness in (ii) (`MonoidalTransformation.hom_ext`) plus `pullback_fst_comp_eq`;
* `blowupGlue` is an open immersion (locally `Spec` of an isomorphism followed by a chart, an open immersion) and
  surjective, hence an isomorphism.

Nothing here is printed: it is part of the proof of a gap filled.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory MvPolynomial HomogeneousLocalization

namespace Hironaka

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

set_option linter.unusedSectionVars false

/-- `Proj 𝒜` is irreducible for a graded domain `A` whose irrelevant ideal is nonzero (the zero ideal is a generic
point). -/
theorem irreducibleSpace_proj {σ : Type*} {A : Type u} [CommRing A] [IsDomain A] [SetLike σ A]
    [AddSubgroupClass σ A] (𝒜 : ℕ → σ) [GradedRing 𝒜] {x : A} (hx0 : x ≠ 0)
    (hx : x ∈ (HomogeneousIdeal.irrelevant 𝒜).toIdeal) : IrreducibleSpace (Proj 𝒜) := by
  let η : ProjectiveSpectrum 𝒜 :=
    { asHomogeneousIdeal := ⊥
      isPrime := by rw [HomogeneousIdeal.toIdeal_bot]; exact inferInstance
      not_irrelevant_le := fun h => hx0 (by have := h hx; exact (Submodule.mem_bot A).mp this) }
  have hcl : closure ({η} : Set (ProjectiveSpectrum 𝒜)) = Set.univ := by
    refine Set.eq_univ_of_forall fun y => ?_
    rw [← ProjectiveSpectrum.le_iff_mem_closure]
    exact (ProjectiveSpectrum.as_ideal_le_as_ideal 𝒜 η y).mp bot_le
  have : IsIrreducible (Set.univ : Set (ProjectiveSpectrum 𝒜)) := by
    rw [← hcl]; exact isIrreducible_singleton.closure
  exact (irreducibleSpace_def _).mpr this

namespace MonoidalTransformation

variable {X : Scheme.{u}} {B : Subscheme X} (t : MonoidalTransformation X B) (U : X.affineOpens)

/-- The opens `V_γ` for a *generating family* `a` of the ideal `B(U)` cover `f⁻¹(U)` (the version of
`exists_mem_chartOpen` with generators instead of all elements of `B(U)`). -/
theorem exists_mem_chartOpen_of_span {ι : Type*} (a : ι → Γ(X, U))
    (hspan : B.ideal U = Ideal.span (Set.range a)) {y : t.X'} (hy : t.f y ∈ U.1) :
    ∃ i, y ∈ t.chartOpen U (a i) := by
  obtain ⟨W₀, hyW₀, s, hs, hsnzd⟩ := t.invertible y
  change t.exceptional.ideal W₀ = _ at hs
  obtain ⟨r, hrle, hyr⟩ := (isAffineOpen_of_mem_affineOpens W₀).exists_basicOpen_le
    (V := t.f ⁻¹ᵁ U) ⟨y, hy⟩ hyW₀
  have hs₁ := ideal_affBasicOpen_eq_span _ hs r
  have hs₁nzd := res_basicOpen_mem_nonZeroDivisors W₀ hsnzd r
  set s₁ := t.X'.presheaf.map (homOfLE (t.X'.basicOpen_le r)).op s
  have hW₁U : ((affBasicOpen W₀ r : t.X'.affineOpens) : t.X'.Opens) ≤ t.f ⁻¹ᵁ U := hrle
  have hid : t.exceptional.ideal (affBasicOpen W₀ r) =
      (B.ideal U).map (t.f.appLE U _ hW₁U).hom :=
    ideal_comap_eq_map_appLE t.f B U _ hW₁U
  by_contra hcon
  simp only [not_exists] at hcon
  set 𝔪 := (IsLocalRing.maximalIdeal (t.X'.presheaf.stalk y)).comap
    (t.X'.presheaf.germ (t.X'.basicOpen r) y hyr).hom
  have hle : (B.ideal U).map (t.f.appLE U _ hW₁U).hom ≤ Ideal.span {s₁} * 𝔪 := by
    rw [Ideal.map_le_iff_le_comap, hspan, Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    have hi : a i ∈ B.ideal U := hspan ▸ Ideal.subset_span ⟨i, rfl⟩
    have : t.f.appLE U _ hW₁U (a i) ∈ t.exceptional.ideal (affBasicOpen W₀ r) :=
      hid ▸ Ideal.mem_map_of_mem _ hi
    rw [hs₁, Ideal.mem_span_singleton'] at this
    obtain ⟨u, hu⟩ := this
    rw [SetLike.mem_coe, Ideal.mem_comap, ← hu, mul_comm u s₁]
    refine Ideal.mul_mem_mul (Ideal.mem_span_singleton_self _) ?_
    by_contra hu'
    have hunit : IsUnit (t.X'.presheaf.germ (t.X'.basicOpen r) y hyr u) := by
      simpa [𝔪, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] using hu'
    exact hcon i ((t.mem_chartOpen_iff U).mpr ⟨_, isChartDomain_basicOpen t U hW₁U hs₁
      hs₁nzd (by rw [← hu, mul_comm]), (Scheme.mem_basicOpen _ _ _ hyr).mpr hunit⟩)
  have hs₁mem : s₁ ∈ Ideal.span {s₁} * 𝔪 := by
    apply hle
    rw [← hid, hs₁]
    exact Ideal.mem_span_singleton_self _
  obtain ⟨m, hm, hsm⟩ := Ideal.mem_span_singleton_mul.mp hs₁mem
  have h1 : (1 - m) * s₁ = 0 := by linear_combination -hsm
  rw [mul_right_mem_nonZeroDivisors_eq_zero_iff hs₁nzd, sub_eq_zero] at h1
  rw [← h1] at hm
  simp [𝔪] at hm

end MonoidalTransformation

section Glue

open BlowupRing

variable {B : Type u} [Field B] {n N e : ℕ} (𝔭 : HomogeneousIdeal (homogeneousSubmodule (Fin n) B))
  [IsDomain (MvPolynomial (Fin n) B ⧸ 𝔭.toIdeal)]
  (g : Fin N → MvPolynomial (Fin n) B ⧸ 𝔭.toIdeal) (hg : ∀ a, g a ∈ quotientGrading 𝔭 e)

/-- The canonical map `H_(u_b) → Γ(D₊(u_b))` (typed with the affine open `chartU`). -/
noncomputable abbrev awayToChart (b : Fin n) :
    CommRingCat.of (Away (quotientGrading 𝔭) (quotientGrading.var 𝔭 b)) ⟶
      Γ(Proj (quotientGrading 𝔭), (chartU 𝔭 b : _)) :=
  Proj.awayToSection (quotientGrading 𝔭) (quotientGrading.var 𝔭 b)

/-- The affine open `D₊(u_b)` is the image of `Spec H_(u_b)`: `fromSpec = Spec (awayToSection) ≫ awayι`. -/
theorem fromSpec_chartU (b : Fin n) :
    (isAffineOpen_of_mem_affineOpens (chartU 𝔭 b)).fromSpec =
      Spec.map (awayToChart 𝔭 b) ≫
        Proj.awayι (quotientGrading 𝔭) (quotientGrading.var 𝔭 b) (quotientGrading.var_mem 𝔭 b) one_pos := by
  have hU : IsAffineOpen (Proj.basicOpen (quotientGrading 𝔭) (quotientGrading.var 𝔭 b)) :=
    Proj.isAffineOpen_basicOpen _ _ (quotientGrading.var_mem 𝔭 b) one_pos
  show hU.fromSpec = Spec.map (Proj.awayToSection (quotientGrading 𝔭) (quotientGrading.var 𝔭 b)) ≫
    Proj.awayι (quotientGrading 𝔭) (quotientGrading.var 𝔭 b) (quotientGrading.var_mem 𝔭 b) one_pos
  have h1 : hU.isoSpec.hom ≫ Spec.map (Proj.awayToSection (quotientGrading 𝔭) (quotientGrading.var 𝔭 b)) =
      (Proj.basicOpenIsoSpec (quotientGrading 𝔭) (quotientGrading.var 𝔭 b)
        (quotientGrading.var_mem 𝔭 b) one_pos).hom := by
    rw [Proj.basicOpenIsoSpec_hom, IsAffineOpen.isoSpec_hom]; rfl
  have h2 : Spec.map (Proj.awayToSection (quotientGrading 𝔭) (quotientGrading.var 𝔭 b)) ≫
      (Proj.basicOpenIsoSpec (quotientGrading 𝔭) (quotientGrading.var 𝔭 b)
        (quotientGrading.var_mem 𝔭 b) one_pos).inv = hU.isoSpec.inv := by
    rw [← cancel_epi hU.isoSpec.hom, ← Category.assoc, h1, Iso.hom_inv_id, Iso.hom_inv_id]
  rw [← IsAffineOpen.isoSpec_inv_ι, Proj.awayι, ← Category.assoc, h2]

section Pieces

variable {D : Subscheme (Proj (quotientGrading 𝔭))} (t : MonoidalTransformation (Proj (quotientGrading 𝔭)) D)
  (hI : ∀ b, D.ideal (chartU 𝔭 b) = Ideal.span (Set.range (gammaSec 𝔭 g hg b)))

/-- A nonempty chart index has `jB (y_{ab}) ≠ 0`. -/
theorem NZIdx.jB_ne_zero (p : NZIdx 𝔭 g hg) : jB 𝔭 g hg (fab 𝔭 g hg p.1.1 p.1.2) ≠ 0 :=
  fun h => p.2 (jB_injective 𝔭 g hg (h.trans (map_zero _).symm))

include hI in
/-- `γ_{ab} = g_a / u_b ^ e` lies in the ideal of the center on `D₊(u_b)`. -/
theorem gammaSec_mem (a : Fin N) (b : Fin n) : gammaSec 𝔭 g hg b a ∈ D.ideal (chartU 𝔭 b) := by
  rw [hI b]; exact Ideal.subset_span ⟨a, rfl⟩

include hI in
/-- The ring isomorphism `θ_{ab} : Γ(D₊(u_b))[I/γ_{ab}] → H'_(y_{ab})` (chosen). -/
theorem exists_thetaOf (p : NZIdx 𝔭 g hg) :
    ∃ θ : chartAlgebra (D.ideal (chartU 𝔭 p.1.2)) (gammaSec 𝔭 g hg p.1.2 p.1.1) →+*
        Away (quotientGrading (kerIdeal 𝔭 g hg)) (fab 𝔭 g hg p.1.1 p.1.2),
      θ.comp (algebraMap _ _) = psi 𝔭 g hg p.1.1 p.1.2 ∧ Function.Bijective θ :=
  exists_theta 𝔭 g hg p.1.1 p.1.2 (NZIdx.jB_ne_zero 𝔭 g hg p) _ (hI p.1.2)

/-- The ring isomorphism `θ_{ab}`. -/
noncomputable def thetaOf (p : NZIdx 𝔭 g hg) :
    chartAlgebra (D.ideal (chartU 𝔭 p.1.2)) (gammaSec 𝔭 g hg p.1.2 p.1.1) →+*
      Away (quotientGrading (kerIdeal 𝔭 g hg)) (fab 𝔭 g hg p.1.1 p.1.2) :=
  (exists_thetaOf 𝔭 g hg hI p).choose

theorem thetaOf_comp (p : NZIdx 𝔭 g hg) :
    (thetaOf 𝔭 g hg hI p).comp (algebraMap _ _) = psi 𝔭 g hg p.1.1 p.1.2 :=
  (exists_thetaOf 𝔭 g hg hI p).choose_spec.1

theorem thetaOf_bijective (p : NZIdx 𝔭 g hg) : Function.Bijective (thetaOf 𝔭 g hg hI p) :=
  (exists_thetaOf 𝔭 g hg hI p).choose_spec.2

/-- The piece `Spec H'_(y_{ab}) → Spec Γ(D₊(u_b))[I/γ_{ab}] → t.X'` of the map `Proj H' → t.X'`. -/
noncomputable def jPiece (p : NZIdx 𝔭 g hg) :
    Spec (CommRingCat.of (Away (quotientGrading (kerIdeal 𝔭 g hg)) (fab 𝔭 g hg p.1.1 p.1.2))) ⟶ t.X' :=
  Spec.map (CommRingCat.ofHom (thetaOf 𝔭 g hg hI p)) ≫
    t.chart (chartU 𝔭 p.1.2) (gammaSec_mem 𝔭 g hg hI p.1.1 p.1.2)

set_option maxHeartbeats 400000 in
/-- The ring maps `H_(u_b) → Γ(D₊(u_b)) → Γ(D₊(u_b))[I/γ_{ab}] → H'_(y_{ab})` compose to `ρ_{ab}`. -/
theorem thetaOf_ring (p : NZIdx 𝔭 g hg) :
    awayToChart 𝔭 p.1.2 ≫
      (chartAlgebraMap D (chartU 𝔭 p.1.2) (gammaSec 𝔭 g hg p.1.2 p.1.1) ≫
        CommRingCat.ofHom (thetaOf 𝔭 g hg hI p)) = CommRingCat.ofHom (rho 𝔭 g hg p.1.1 p.1.2) := by
  refine CommRingCat.hom_ext (RingHom.ext fun x => ?_)
  have h1 := RingHom.congr_fun (thetaOf_comp 𝔭 g hg hI p) (sigma 𝔭 p.1.2 x)
  have h2 : psi 𝔭 g hg p.1.1 p.1.2 (sigma 𝔭 p.1.2 x) = rho 𝔭 g hg p.1.1 p.1.2 x := by
    simp only [psi, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
      RingEquiv.symm_apply_apply]
  exact h1.trans h2

/-- `jPiece ≫ t.f` is `Spec θ ≫ chartToBase`. -/
theorem jPiece_comp_f_aux (p : NZIdx 𝔭 g hg) :
    jPiece 𝔭 g hg t hI p ≫ t.f = Spec.map (CommRingCat.ofHom (thetaOf 𝔭 g hg hI p)) ≫
      chartToBase D (chartU 𝔭 p.1.2) (gammaSec 𝔭 g hg p.1.2 p.1.1) := by
  exact (Category.assoc _ _ _).trans (congrArg (fun m => Spec.map (CommRingCat.ofHom (thetaOf 𝔭 g hg hI p)) ≫ m)
    (t.chart_f (chartU 𝔭 p.1.2) (gammaSec_mem 𝔭 g hg hI p.1.1 p.1.2)))

/-- `Spec` of the ring maps of `thetaOf_ring`. -/
theorem thetaOf_spec (p : NZIdx 𝔭 g hg) :
    Spec.map (CommRingCat.ofHom (thetaOf 𝔭 g hg hI p)) ≫
      Spec.map (chartAlgebraMap D (chartU 𝔭 p.1.2) (gammaSec 𝔭 g hg p.1.2 p.1.1)) ≫
      Spec.map (awayToChart 𝔭 p.1.2) = Spec.map (CommRingCat.ofHom (rho 𝔭 g hg p.1.1 p.1.2)) := by
  calc _ = Spec.map (awayToChart 𝔭 p.1.2 ≫ (chartAlgebraMap D (chartU 𝔭 p.1.2)
        (gammaSec 𝔭 g hg p.1.2 p.1.1) ≫ CommRingCat.ofHom (thetaOf 𝔭 g hg hI p))) := by
          simp only [Spec.map_comp, Category.assoc]
    _ = _ := congrArg Spec.map (thetaOf_ring 𝔭 g hg hI p)

/-- `jPiece ≫ t.f` is the chart map `Spec ρ_{ab} ≫ awayι` into `Proj H`. -/
theorem jPiece_comp_f (p : NZIdx 𝔭 g hg) :
    jPiece 𝔭 g hg t hI p ≫ t.f =
      Spec.map (CommRingCat.ofHom (rho 𝔭 g hg p.1.1 p.1.2)) ≫
        Proj.awayι (quotientGrading 𝔭) (quotientGrading.var 𝔭 p.1.2)
          (quotientGrading.var_mem 𝔭 p.1.2) one_pos := by
  refine (jPiece_comp_f_aux 𝔭 g hg t hI p).trans ?_
  refine (congrArg (fun m => Spec.map (CommRingCat.ofHom (thetaOf 𝔭 g hg hI p)) ≫
    Spec.map (chartAlgebraMap D (chartU 𝔭 p.1.2) (gammaSec 𝔭 g hg p.1.2 p.1.1)) ≫ m)
    (fromSpec_chartU 𝔭 p.1.2)).trans ?_
  simp only [← Category.assoc]
  exact congrArg (fun m => m ≫ Proj.awayι (quotientGrading 𝔭) (quotientGrading.var 𝔭 p.1.2)
    (quotientGrading.var_mem 𝔭 p.1.2) one_pos) (thetaOf_spec 𝔭 g hg hI p)

/-- `jPiece` is an open immersion: `Spec θ` is an isomorphism and the chart of `t` is an open immersion. -/
theorem isOpenImmersion_jPiece (p : NZIdx 𝔭 g hg) : IsOpenImmersion (jPiece 𝔭 g hg t hI p) := by
  have : IsIso (CommRingCat.ofHom (thetaOf 𝔭 g hg hI p)) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr (thetaOf_bijective 𝔭 g hg hI p)
  have := t.isOpenImmersion_chart (chartU 𝔭 p.1.2) (gammaSec_mem 𝔭 g hg hI p.1.1 p.1.2)
  exact IsOpenImmersion.comp _ _

set_option maxHeartbeats 400000 in
/-- The gluing condition for the pieces `jPiece` over the cover `chartCover` of `Proj H'`. -/
theorem jPiece_overlap (p q : NZIdx 𝔭 g hg) :
    Limits.pullback.fst ((chartCover 𝔭 g hg).f p) ((chartCover 𝔭 g hg).f q) ≫ jPiece 𝔭 g hg t hI p =
      Limits.pullback.snd ((chartCover 𝔭 g hg).f p) ((chartCover 𝔭 g hg).f q) ≫ jPiece 𝔭 g hg t hI q := by
  have hopen : IsOpenImmersion ((chartCover 𝔭 g hg).f q) := (chartCover 𝔭 g hg).map_prop q
  have hopen' : IsOpenImmersion ((chartCover 𝔭 g hg).f p) := (chartCover 𝔭 g hg).map_prop p
  have hjp := isOpenImmersion_jPiece 𝔭 g hg t hI p
  have h0 : IsOpenImmersion (Limits.pullback.fst ((chartCover 𝔭 g hg).f p) ((chartCover 𝔭 g hg).f q)) :=
    inferInstance
  have h1 : IsOpenImmersion (Limits.pullback.fst ((chartCover 𝔭 g hg).f p) ((chartCover 𝔭 g hg).f q) ≫
      jPiece 𝔭 g hg t hI p) := @IsOpenImmersion.comp _ _ _ _ _ h0 hjp
  have hc := pullback_fst_comp_eq 𝔭 g hg (NZIdx.jB_ne_zero 𝔭 g hg p) (NZIdx.jB_ne_zero 𝔭 g hg q)
  have e1 := jPiece_comp_f 𝔭 g hg t hI p
  have e2 := jPiece_comp_f 𝔭 g hg t hI q
  refine MonoidalTransformation.hom_ext (t := t) ?_ ?_
  · exact (Category.assoc _ _ _).trans ((congrArg (fun m => Limits.pullback.fst
      ((chartCover 𝔭 g hg).f p) ((chartCover 𝔭 g hg).f q) ≫ m) e1).trans (hc.trans
      ((congrArg (fun m => Limits.pullback.snd ((chartCover 𝔭 g hg).f p)
        ((chartCover 𝔭 g hg).f q) ≫ m) e2).symm.trans (Category.assoc _ _ _).symm)))
  · rw [Subscheme.totalTransform_comp]
    exact @isInvertibleIdeal_totalTransform_of_isOpenImmersion _ _ _ t.invertible _ h1

set_option maxHeartbeats 400000 in
/-- The morphism `j : Proj H' ⟶ t.X'`, glued from the pieces `jPiece` over the charts `D₊(y_{ab})` of `Proj H'`
(Mathlib's `Scheme.OpenCover.glueMorphisms`). -/
noncomputable def blowupGlue : Proj (quotientGrading (kerIdeal 𝔭 g hg)) ⟶ t.X' :=
  (chartCover 𝔭 g hg).glueMorphisms (fun p => jPiece 𝔭 g hg t hI p) (jPiece_overlap 𝔭 g hg t hI)

set_option maxHeartbeats 400000 in
/-- On the chart `D₊(y_{ab})`, `j` is `jPiece`. -/
theorem awayι_comp_blowupGlue (p : NZIdx 𝔭 g hg) :
    (chartCover 𝔭 g hg).f p ≫ blowupGlue 𝔭 g hg t hI = jPiece 𝔭 g hg t hI p :=
  (chartCover 𝔭 g hg).ι_glueMorphisms _ _ p

set_option maxHeartbeats 400000 in
/-- Over the chart `V_p`, `j` is an isomorphism: the section `Spec H'_(y_p) → j⁻¹(V_p)` is a closed (as `j` is
separated) and open immersion into an irreducible, hence connected, space. -/
theorem isIso_snd_blowupGlue (p : NZIdx 𝔭 g hg) :
    IsIso (Limits.pullback.snd (blowupGlue 𝔭 g hg t hI) (jPiece 𝔭 g hg t hI p)) := by
  have hdom := isDomain_quotient 𝔭 g hg
  have hjp := isOpenImmersion_jPiece 𝔭 g hg t hI p
  have hirr : IrreducibleSpace (Proj (quotientGrading (kerIdeal 𝔭 g hg))) :=
    irreducibleSpace_proj (quotientGrading (kerIdeal 𝔭 g hg)) p.2
      (HomogeneousIdeal.mem_irrelevant_of_mem _ one_pos (fab_mem 𝔭 g hg p.1.1 p.1.2))
  let s : Spec (CommRingCat.of (Away (quotientGrading (kerIdeal 𝔭 g hg)) (fab 𝔭 g hg p.1.1 p.1.2))) ⟶
      Limits.pullback (blowupGlue 𝔭 g hg t hI) (jPiece 𝔭 g hg t hI p) :=
    Limits.pullback.lift ((chartCover 𝔭 g hg).f p) (𝟙 _)
      ((awayι_comp_blowupGlue 𝔭 g hg t hI p).trans (Category.id_comp _).symm)
  have hs : s ≫ Limits.pullback.snd (blowupGlue 𝔭 g hg t hI) (jPiece 𝔭 g hg t hI p) = 𝟙 _ :=
    Limits.pullback.lift_snd _ _ _
  have hsf : s ≫ Limits.pullback.fst (blowupGlue 𝔭 g hg t hI) (jPiece 𝔭 g hg t hI p) =
      (chartCover 𝔭 g hg).f p := Limits.pullback.lift_fst _ _ _
  have hopen : IsOpenImmersion ((chartCover 𝔭 g hg).f p) := (chartCover 𝔭 g hg).map_prop p
  have hfst : IsOpenImmersion (Limits.pullback.fst (blowupGlue 𝔭 g hg t hI) (jPiece 𝔭 g hg t hI p)) :=
    inferInstance
  have hsopen : IsOpenImmersion s := by
    have : IsOpenImmersion (s ≫ Limits.pullback.fst (blowupGlue 𝔭 g hg t hI) (jPiece 𝔭 g hg t hI p)) := by
      rw [hsf]; exact hopen
    exact IsOpenImmersion.of_comp s (Limits.pullback.fst (blowupGlue 𝔭 g hg t hI) (jPiece 𝔭 g hg t hI p))
  have hsclosed : IsClosedImmersion s := by
    have : IsClosedImmersion (s ≫ Limits.pullback.snd (blowupGlue 𝔭 g hg t hI)
        (jPiece 𝔭 g hg t hI p)) := by rw [hs]; infer_instance
    have hsep : IsSeparated (Limits.pullback.snd (blowupGlue 𝔭 g hg t hI) (jPiece 𝔭 g hg t hI p)) :=
      inferInstance
    exact IsClosedImmersion.of_comp s (Limits.pullback.snd (blowupGlue 𝔭 g hg t hI) (jPiece 𝔭 g hg t hI p))
  have hirr' : IrreducibleSpace ↥(Limits.pullback (blowupGlue 𝔭 g hg t hI) (jPiece 𝔭 g hg t hI p)) := by
    have : Nonempty ↥(Limits.pullback (blowupGlue 𝔭 g hg t hI) (jPiece 𝔭 g hg t hI p)) := by
      have hnt : Nontrivial (Away (quotientGrading (kerIdeal 𝔭 g hg)) (fab 𝔭 g hg p.1.1 p.1.2)) :=
        (embS 𝔭 g hg p.1.1 p.1.2 (NZIdx.jB_ne_zero 𝔭 g hg p)).domain_nontrivial
      have : Nonempty (Spec (CommRingCat.of (Away (quotientGrading (kerIdeal 𝔭 g hg))
          (fab 𝔭 g hg p.1.1 p.1.2)))) := inferInstanceAs (Nonempty (PrimeSpectrum _))
      exact ⟨s this.some⟩
    exact (Limits.pullback.fst (blowupGlue 𝔭 g hg t hI) (jPiece 𝔭 g hg t hI p)).isOpenEmbedding.irreducibleSpace
  have hclopen : IsClopen (Set.range s) := ⟨hsclosed.isClosedEmbedding.isClosed_range, hsopen.base_open.isOpen_range⟩
  have hne : (Set.range s).Nonempty := by
    have hnt : Nontrivial (Away (quotientGrading (kerIdeal 𝔭 g hg)) (fab 𝔭 g hg p.1.1 p.1.2)) :=
      (embS 𝔭 g hg p.1.1 p.1.2 (NZIdx.jB_ne_zero 𝔭 g hg p)).domain_nontrivial
    have : Nonempty (Spec (CommRingCat.of (Away (quotientGrading (kerIdeal 𝔭 g hg))
        (fab 𝔭 g hg p.1.1 p.1.2)))) := inferInstanceAs (Nonempty (PrimeSpectrum _))
    exact ⟨s this.some, this.some, rfl⟩
  have hall : Set.range s = Set.univ := (isClopen_iff.mp hclopen).resolve_left hne.ne_empty
  have hsurj : Surjective s := ⟨Set.range_eq_univ.mp hall⟩
  have hsiso : IsIso s := (isIso_iff_isOpenImmersion_and_surjective s).mpr ⟨hsopen, hsurj⟩
  have : Limits.pullback.snd (blowupGlue 𝔭 g hg t hI) (jPiece 𝔭 g hg t hI p) = inv s := by
    rw [← cancel_epi s, hs, IsIso.hom_inv_id]
  rw [this]
  infer_instance

set_option maxHeartbeats 400000 in
/-- If `V_{γ_{ab}}` contains a point over `D₊(u_b)`, then `y_{ab} ≠ 0`. -/
theorem fab_ne_zero_of_mem_chartOpen (a : Fin N) (b : Fin n) {y : t.X'}
    (hy : t.f y ∈ (chartU 𝔭 b : TopologicalSpace.Opens (Proj (quotientGrading 𝔭))))
    (hyV : y ∈ t.chartOpen (chartU 𝔭 b) (gammaSec 𝔭 g hg b a)) : fab 𝔭 g hg a b ≠ 0 := by
  intro h0
  have hj := congrArg (jB 𝔭 g hg) h0
  rw [jB_fab, map_zero] at hj
  rcases mul_eq_zero.mp hj with hga | hub
  · have hga0 : g a = 0 := jA_injective 𝔭 (hga.trans (map_zero _).symm)
    have hfrac0 : ∀ (x : MvPolynomial (Fin n) B ⧸ 𝔭.toIdeal) (hx : x ∈ quotientGrading 𝔭 e), x = 0 →
        ProjChart.frac (quotientGrading 𝔭) (quotientGrading.var_mem 𝔭 b) e x hx = 0 := by
      intro x hx h
      subst h
      apply HomogeneousLocalization.val_injective
      simp only [ProjChart.frac, Away.val_mk, HomogeneousLocalization.val_zero]
      exact Localization.mk_zero _
    have hγ : gammaSec 𝔭 g hg b a = 0 := by
      rw [gammaSec, hfrac0 _ _ hga0, map_zero]
    obtain ⟨W, ⟨hW, _, hnzd⟩, hyW⟩ := (t.mem_chartOpen_iff _).mp hyV
    rw [hγ, map_zero] at hnzd
    have hsub : Subsingleton Γ(t.X', W) := ⟨fun x y => by
      have h := (mem_nonZeroDivisors_iff.mp hnzd).2 (x - y) (by simp)
      exact sub_eq_zero.mp h⟩
    have hnt : Nontrivial Γ(t.X', W) := (t.X'.presheaf.germ W y hyW).hom.domain_nontrivial
    exact (not_subsingleton Γ(t.X', W)) hsub
  · have hu0 : quotientGrading.var 𝔭 b = 0 := jA_injective 𝔭 (hub.trans (map_zero _).symm)
    have := (Proj.mem_basicOpen (quotientGrading 𝔭) (quotientGrading.var 𝔭 b) (t.f y)).mp hy
    exact this (by rw [hu0]; exact zero_mem _)

set_option maxHeartbeats 400000 in
/-- Every point of `t.X'` is in the image of some `jPiece`. -/
theorem exists_jPiece (y : t.X') : ∃ (p : NZIdx 𝔭 g hg) (z : Spec (CommRingCat.of
    (Away (quotientGrading (kerIdeal 𝔭 g hg)) (fab 𝔭 g hg p.1.1 p.1.2)))), jPiece 𝔭 g hg t hI p z = y := by
  have hy : t.f y ∈ (⊤ : TopologicalSpace.Opens (Proj (quotientGrading 𝔭))) := trivial
  rw [← quotientGrading.iSup_basicOpen_var 𝔭] at hy
  obtain ⟨b, hb⟩ := TopologicalSpace.Opens.mem_iSup.mp hy
  obtain ⟨a, ha⟩ := t.exists_mem_chartOpen_of_span (chartU 𝔭 b) (gammaSec 𝔭 g hg b) (hI b) hb
  have hne := fab_ne_zero_of_mem_chartOpen 𝔭 g hg t a b hb ha
  let p : NZIdx 𝔭 g hg := ⟨(a, b), hne⟩
  have hmem := gammaSec_mem 𝔭 g hg hI a b
  have hrange : y ∈ Set.range (t.chart (chartU 𝔭 b) hmem) := by
    rw [t.range_chart (chartU 𝔭 b) hmem]; exact ha
  obtain ⟨w, hw⟩ := hrange
  have hiso : IsIso (CommRingCat.ofHom (thetaOf 𝔭 g hg hI p)) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr (thetaOf_bijective 𝔭 g hg hI p)
  have hsurj : Surjective (Spec.map (CommRingCat.ofHom (thetaOf 𝔭 g hg hI p))) := inferInstance
  obtain ⟨z, hz⟩ := hsurj.surj w
  exact ⟨p, z, by rw [jPiece, Scheme.Hom.comp_apply, hz]; exact hw⟩

/-- The open cover of `t.X'` by the images of the pieces `jPiece`. -/
noncomputable def pieceCover : t.X'.OpenCover :=
  ⟨⟨NZIdx 𝔭 g hg, fun p => Spec (CommRingCat.of (Away (quotientGrading (kerIdeal 𝔭 g hg))
    (fab 𝔭 g hg p.1.1 p.1.2))), fun p => jPiece 𝔭 g hg t hI p⟩,
    ⟨by simpa using fun y => exists_jPiece 𝔭 g hg t hI y,
      by rintro Y g ⟨p⟩; exact isOpenImmersion_jPiece 𝔭 g hg t hI p⟩⟩

set_option maxHeartbeats 400000 in
/-- **`Proj H' ≅ t.X'`**: the glued map `j` is an isomorphism, since it is one over each chart `V_p`. -/
theorem isIso_blowupGlue : IsIso (blowupGlue 𝔭 g hg t hI) := by
  have h : MorphismProperty.isomorphisms Scheme (blowupGlue 𝔭 g hg t hI) := by
    refine IsZariskiLocalAtTarget.of_openCover (pieceCover 𝔭 g hg t hI) fun p => ?_
    exact isIso_snd_blowupGlue 𝔭 g hg t hI p
  exact (MorphismProperty.isomorphisms.iff _).mp h

set_option maxHeartbeats 400000 in
/-- The structure maps of `Proj H'` and `Proj H` agree on the chart rings: `B → H'_0 → H'_(y_{ab})` is
`B → H_0 → H_(u_b) → H'_(y_{ab})`. -/
theorem structure_ring (p : NZIdx 𝔭 g hg) :
    CommRingCat.ofHom (algebraMap B (quotientGrading 𝔭 0)) ≫
        CommRingCat.ofHom (algebraMap (quotientGrading 𝔭 0) (Away (quotientGrading 𝔭)
          (quotientGrading.var 𝔭 p.1.2))) ≫ CommRingCat.ofHom (rho 𝔭 g hg p.1.1 p.1.2) =
      CommRingCat.ofHom (algebraMap B (quotientGrading (kerIdeal 𝔭 g hg) 0)) ≫
        CommRingCat.ofHom (algebraMap (quotientGrading (kerIdeal 𝔭 g hg) 0)
          (Away (quotientGrading (kerIdeal 𝔭 g hg)) (fab 𝔭 g hg p.1.1 p.1.2))) := by
  have hdom := isDomain_quotient 𝔭 g hg
  have hab := NZIdx.jB_ne_zero 𝔭 g hg p
  have hb0 := jA_var_ne_zero 𝔭 g hg hab
  refine CommRingCat.hom_ext (RingHom.ext fun b' => ?_)
  have l := awayEmb_rho 𝔭 g hg p.1.1 p.1.2 hab hb0
    (algebraMap (quotientGrading 𝔭 0) _ (algebraMap B (quotientGrading 𝔭 0) b'))
  rw [awayEmb_algebraMap] at l
  have r : awayEmb (quotientGrading (kerIdeal 𝔭 g hg)) (jB 𝔭 g hg) (fab 𝔭 g hg p.1.1 p.1.2) hab
      (algebraMap (quotientGrading (kerIdeal 𝔭 g hg) 0) _
        (algebraMap B (quotientGrading (kerIdeal 𝔭 g hg) 0) b')) =
      jB 𝔭 g hg ((algebraMap B (quotientGrading (kerIdeal 𝔭 g hg) 0) b' :
        quotientGrading (kerIdeal 𝔭 g hg) 0) : _) := awayEmb_algebraMap hab _
  have m : jA 𝔭 ((algebraMap B (quotientGrading 𝔭 0) b' : quotientGrading 𝔭 0) :
      MvPolynomial (Fin n) B ⧸ 𝔭.toIdeal) =
      jB 𝔭 g hg ((algebraMap B (quotientGrading (kerIdeal 𝔭 g hg) 0) b' :
        quotientGrading (kerIdeal 𝔭 g hg) 0) : _) := by
    rw [jB_apply]
    exact congrArg (jA 𝔭) ((incl 𝔭 g hg).commutes b').symm
  exact embS_injective 𝔭 g hg p.1.1 p.1.2 hab (l.trans (m.trans r.symm))

set_option maxHeartbeats 400000 in
/-- `j` is compatible with the structure maps to `Spec B`. -/
theorem blowupGlue_comp_structure :
    blowupGlue 𝔭 g hg t hI ≫ t.f ≫ projStructure 𝔭 = projStructure (kerIdeal 𝔭 g hg) := by
  refine (chartCover 𝔭 g hg).hom_ext _ _ fun p => ?_
  have h1 : (chartCover 𝔭 g hg).f p ≫ blowupGlue 𝔭 g hg t hI ≫ t.f ≫ projStructure 𝔭 =
      Spec.map (CommRingCat.ofHom (rho 𝔭 g hg p.1.1 p.1.2)) ≫
        (Proj.awayι (quotientGrading 𝔭) (quotientGrading.var 𝔭 p.1.2)
          (quotientGrading.var_mem 𝔭 p.1.2) one_pos ≫ projStructure 𝔭) :=
    (Category.assoc _ _ _).symm.trans
      ((congrArg (fun m => m ≫ t.f ≫ projStructure 𝔭) (awayι_comp_blowupGlue 𝔭 g hg t hI p)).trans
        ((Category.assoc _ _ _).symm.trans
          ((congrArg (fun m => m ≫ projStructure 𝔭) (jPiece_comp_f 𝔭 g hg t hI p)).trans
            (Category.assoc _ _ _))))
  refine h1.trans ?_
  have e1 : Proj.awayι (quotientGrading 𝔭) (quotientGrading.var 𝔭 p.1.2)
      (quotientGrading.var_mem 𝔭 p.1.2) one_pos ≫ projStructure 𝔭 =
      Spec.map (CommRingCat.ofHom (algebraMap (quotientGrading 𝔭 0) (Away (quotientGrading 𝔭)
        (quotientGrading.var 𝔭 p.1.2)))) ≫
        Spec.map (CommRingCat.ofHom (algebraMap B (quotientGrading 𝔭 0))) :=
    (Category.assoc _ _ _).symm.trans (congrArg (fun m => m ≫ _) (Proj.awayι_toSpecZero _ _ _ _))
  have e2 : (chartCover 𝔭 g hg).f p ≫ projStructure (kerIdeal 𝔭 g hg) =
      Spec.map (CommRingCat.ofHom (algebraMap (quotientGrading (kerIdeal 𝔭 g hg) 0)
        (Away (quotientGrading (kerIdeal 𝔭 g hg)) (fab 𝔭 g hg p.1.1 p.1.2)))) ≫
        Spec.map (CommRingCat.ofHom (algebraMap B (quotientGrading (kerIdeal 𝔭 g hg) 0))) :=
    (Category.assoc _ _ _).symm.trans (congrArg (fun m => m ≫ _) (Proj.awayι_toSpecZero _ _ _ _))
  rw [e1, e2]
  have := congrArg Spec.map (structure_ring 𝔭 g hg p)
  simp only [Spec.map_comp, Category.assoc] at this
  exact this

end Pieces

set_option maxHeartbeats 400000 in
/-- **A monoidal transformation of `Proj H` (`H = B[T]/𝔭`, `𝔭` homogeneous prime) is `Proj H'`**: with the forms
`g_a` of step L1a there are `m` and a homogeneous ideal `𝔟` of `B[V₁, …, V_m]` and an isomorphism
`t.X' ≅ Proj(B[V]/𝔟)` over `Spec B`. -/
theorem exists_iso_proj_quotient {D : Subscheme (Proj (quotientGrading 𝔭))}
    (t : MonoidalTransformation (Proj (quotientGrading 𝔭)) D) :
    ∃ (m : ℕ) (𝔟 : HomogeneousIdeal (homogeneousSubmodule (Fin m) B))
      (Φ : t.X' ≅ Proj (quotientGrading 𝔟)), Φ.hom ≫ projStructure 𝔟 = t.f ≫ projStructure 𝔭 := by
  obtain ⟨e, N, g, hg, h⟩ := quotientGrading.exists_forms_generating 𝔭 D
  have hI : ∀ b, D.ideal (chartU 𝔭 b) = Ideal.span (Set.range (gammaSec 𝔭 g hg b)) := fun b => (h b).2
  have hiso := isIso_blowupGlue 𝔭 g hg t hI
  refine ⟨N * n, kerIdeal 𝔭 g hg, (asIso (blowupGlue 𝔭 g hg t hI)).symm, ?_⟩
  have := blowupGlue_comp_structure 𝔭 g hg t hI
  show inv (blowupGlue 𝔭 g hg t hI) ≫ projStructure (kerIdeal 𝔭 g hg) = _
  rw [← this, IsIso.inv_hom_id_assoc]

end Glue

end Hironaka
