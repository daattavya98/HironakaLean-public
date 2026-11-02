/-
Copyright (c) 2026 Daattavya Aggarwal, Minhyong Kim, Oisin Kim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daattavya Aggarwal, Minhyong Kim, Oisin Kim
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Architect
public import Hironaka.Ch0.AlgebraicScheme

/-!
# Compatibility layer: stalks of subschemes and the simple locus

Facts about subschemes (ideal sheaves, `Hironaka/Ch0/AlgebraicScheme.lean`) that Hironaka uses
without comment: the stalk `D_y` of the ideal sheaf of `D` at a point of `D` is the kernel of
the stalk map of the closed immersion `D → X`, so that `O_{D,y} ≅ O_{X,y}/D_y`; a subscheme of
an algebraic scheme is algebraic; the simple points of an algebraic scheme form an open set
(from (iii) of p. 161); and the elementary relations between `pts`, containment and stalks.
(First proved for Ch. IV §1, Lemma 1.)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace IsLocalRing

namespace Hironaka

universe u

/-- The stalk `D_y` of the ideal sheaf of a subscheme `D` at a point `y = ι(y')` of `D` is the
kernel of the (surjective) stalk map `O_{X,y} → O_{D,y'}` of the closed immersion `ι`. -/
theorem stalkIdeal_eq_ker_stalkMap {X : Scheme.{u}} (D : Subscheme X) (y : D.toScheme) :
    D.stalkIdeal (D.ι y) = RingHom.ker (D.ι.stalkMap y).hom := by
  apply le_antisymm
  · refine Ideal.span_le.mpr ?_
    rintro a ⟨U, hxU, s, hs, rfl⟩
    show _ ∈ RingHom.ker _
    have h0 : (D.ι.app U).hom s = 0 := by
      have := (Scheme.IdealSheafData.ker_subschemeι_app D U).ge hs
      exact this
    rw [RingHom.mem_ker, Scheme.Hom.germ_stalkMap_apply, h0, map_zero]
  · intro a ha
    rw [RingHom.mem_ker] at ha
    obtain ⟨U₁, hyU₁, s₁, rfl⟩ := X.presheaf.exists_germ_eq a
    obtain ⟨_, ⟨U, hU, rfl⟩, hyU, hUU₁⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open hyU₁ U₁.isOpen
    let s : Γ(X, U) := X.presheaf.map (homOfLE hUU₁).op s₁
    have hs : X.presheaf.germ U (D.ι y) hyU s = X.presheaf.germ U₁ (D.ι y) hyU₁ s₁ :=
      X.presheaf.germ_res_apply _ _ _ _
    rw [← hs, Scheme.Hom.germ_stalkMap_apply] at ha
    rw [← hs]
    have ha' : D.toScheme.presheaf.germ (D.ι ⁻¹ᵁ U) y hyU ((D.ι.app U).hom s) =
        D.toScheme.presheaf.germ (D.ι ⁻¹ᵁ U) y hyU 0 := by
      rw [ha, map_zero]
    obtain ⟨W', hyW', iW, iW₂, hW⟩ := D.toScheme.presheaf.germ_eq y hyU hyU _ _ ha'
    rw [map_zero] at hW
    obtain ⟨O, hO, hOW⟩ := D.ι.isEmbedding.isInducing.isOpen_iff.mp W'.isOpen
    obtain ⟨g, hg, hyg⟩ := hU.exists_basicOpen_le (V := U ⊓ ⟨O, hO⟩)
      ⟨D.ι y, hyU, by
        show D.ι y ∈ O
        have : y ∈ (W' : Set D.toScheme) := hyW'
        rw [← hOW] at this
        exact this⟩ hyU
    let V : X.affineOpens := ⟨X.basicOpen g, hU.basicOpen g⟩
    have hVU : (V : X.Opens) ≤ U := hg.trans inf_le_left
    let s' : Γ(X, V) := X.presheaf.map (homOfLE hVU).op s
    have hs' : s' ∈ D.ideal V := by
      rw [← Scheme.IdealSheafData.ker_subschemeι_app D V, RingHom.mem_ker]
      have hle : D.ι ⁻¹ᵁ (V : X.Opens) ≤ W' := by
        intro z hz
        have : D.ι z ∈ O := (hg hz).2
        rw [← SetLike.mem_coe, ← hOW]
        exact this
      have hnat : (D.ι.app V).hom (X.presheaf.map (homOfLE hVU).op s) =
          (D.toScheme.presheaf.map ((Opens.map D.ι.base).map (homOfLE hVU)).op).hom
            ((D.ι.app U).hom s) := by
        rw [← CommRingCat.comp_apply, D.ι.naturality, CommRingCat.comp_apply]
        rfl
      simp only [s']
      rw [hnat]
      have e : ((Opens.map D.ι.base).map (homOfLE hVU)).op = iW.op ≫ (homOfLE hle).op :=
        Subsingleton.elim _ _
      rw [e, Functor.map_comp, CommRingCat.comp_apply, hW, map_zero]
    exact Ideal.subset_span ⟨V, hyg, s', hs', X.presheaf.germ_res_apply _ _ _ _⟩

/-- A subscheme of an algebraic scheme is an algebraic scheme. -/
theorem isAlgebraicScheme_toScheme {X : Scheme.{u}} [IsAlgebraicScheme X]
    (D : Subscheme X) : IsAlgebraicScheme D.toScheme := by
  obtain ⟨S, i1, i2, i3, p, hp, hq⟩ := IsAlgebraicScheme.exists_base (X := X)
  exact ⟨⟨S, i1, i2, i3, D.ι ≫ p, inferInstance, inferInstance⟩⟩

/-- On an affine open `U` of a scheme, the point `U.fromSpec y` is simple iff `y` lies in the
regular locus of `Γ(Z, U)`. -/
theorem isSimpleAt_fromSpec_iff {Z : Scheme.{u}} {U : Z.Opens} (hU : IsAffineOpen U)
    (y : PrimeSpectrum Γ(Z, U)) :
    Z.IsSimpleAt (hU.fromSpec y) ↔ y ∈ regularLocus Γ(Z, U) := by
  have hy : hU.fromSpec y ∈ U := by
    rw [← SetLike.mem_coe, ← hU.range_fromSpec]
    exact ⟨y, rfl⟩
  let := TopCat.Presheaf.algebra_section_stalk Z.presheaf ⟨hU.fromSpec y, hy⟩
  have hloc : IsLocalization y.asIdeal.primeCompl (Z.presheaf.stalk (hU.fromSpec y)) :=
    hU.isLocalization_stalk' y hy
  let e := IsLocalization.algEquiv (R := Γ(Z, U)) y.asIdeal.primeCompl
    (Localization.AtPrime y.asIdeal) (Z.presheaf.stalk (hU.fromSpec y))
  constructor
  · intro h
    have : IsRegularLocalRing (Z.presheaf.stalk (hU.fromSpec y)) := h
    exact IsRegularLocalRing.of_ringEquiv e.symm.toRingEquiv
  · intro h
    have : IsRegularLocalRing (Localization.AtPrime y.asIdeal) := h
    exact IsRegularLocalRing.of_ringEquiv e.toRingEquiv

/-- The simple points of an algebraic scheme form an open subset (Ch. 0, (iii), p. 161). -/
theorem isOpen_setOf_isSimpleAt [Hironaka.Cited.IsHironakaBaseIsClosedSingularLocus.{u}] (Z : Scheme.{u}) [IsAlgebraicScheme Z] :
    IsOpen {z : Z | Z.IsSimpleAt z} := by
  obtain ⟨S, i1, i2, i3, p, hp, -⟩ := IsAlgebraicScheme.exists_base (X := Z)
  have hU : ∀ U : Z.affineOpens, IsOpen (U.2.fromSpec '' regularLocus Γ(Z, U)) := by
    intro U
    have hUa : IsAffineOpen (U : Z.Opens) := U.2
    refine hUa.fromSpec.isOpenEmbedding.isOpenMap _ ?_
    let φ : S →+* Γ(Z, U) :=
      (p.appLE ⊤ U le_top).hom.comp (Scheme.ΓSpecIso (CommRingCat.of S)).inv.hom
    let : Algebra S Γ(Z, U) := φ.toAlgebra
    have hφ : φ.FiniteType := by
      refine RingHom.FiniteType.comp ?_ (RingHom.FiniteType.of_surjective _ ?_)
      · exact HasRingHomProperty.appLE @LocallyOfFiniteType p hp
          ⟨⊤, isAffineOpen_top _⟩ U le_top
      · exact (Scheme.ΓSpecIso (CommRingCat.of S)).commRingCatIsoToRingEquiv.symm.surjective
    have : Algebra.FiniteType S Γ(Z, U) := hφ
    exact isClosed_compl_iff.mp (IsHironakaBase.isClosed_singularLocus S Γ(Z, U))
  have heq : {z : Z | Z.IsSimpleAt z} = ⋃ U : Z.affineOpens,
      U.2.fromSpec '' regularLocus Γ(Z, U) := by
    ext z
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion]
    constructor
    · intro hz
      obtain ⟨_, ⟨U, hUa, rfl⟩, hzU, -⟩ :=
        Z.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ z) isOpen_univ
      have : z ∈ Set.range (hUa.fromSpec) := by rw [hUa.range_fromSpec]; exact hzU
      obtain ⟨y, rfl⟩ := this
      exact ⟨⟨U, hUa⟩, y, (isSimpleAt_fromSpec_iff hUa y).mp hz, rfl⟩
    · rintro ⟨U, y, hy, rfl⟩
      exact (isSimpleAt_fromSpec_iff U.2 y).mpr hy
  rw [heq]
  exact isOpen_iUnion hU

/-- The quotient `O_{X,y}/D_y` is the local ring of the subscheme `D` at `y`. -/
theorem nonempty_stalk_quot_equiv {X : Scheme.{u}} (D : Subscheme X) (y : D.toScheme) :
    Nonempty ((X.presheaf.stalk (D.ι y) ⧸ D.stalkIdeal (D.ι y)) ≃+*
      D.toScheme.presheaf.stalk y) :=
  ⟨(Ideal.quotEquivOfEq (stalkIdeal_eq_ker_stalkMap D y)).trans
    (RingHom.quotientKerEquivOfSurjective (D.ι.stalkMap_surjective y))⟩

/-- At a point `ξ` of a reduced subscheme `D` whose closure is an irreducible component of `D`,
the stalk of the ideal sheaf of `D` is the maximal ideal. -/
theorem stalkIdeal_eq_maximalIdeal_of_isReduced {X : Scheme.{u}} (D : Subscheme X)
    (hD : D.IsReduced) (ξ : D.toScheme) (hξ : closure {ξ} ∈ irreducibleComponents D.toScheme) :
    D.stalkIdeal (D.ι ξ) = IsLocalRing.maximalIdeal (X.presheaf.stalk (D.ι ξ)) := by
  have : IsReduced D.toScheme := hD
  have hF := isField_stalk_of_closure_mem_irreducibleComponents D.toScheme ξ hξ
  obtain ⟨e⟩ := nonempty_stalk_quot_equiv D ξ
  have hF' := MulEquiv.isField hF e.toMulEquiv
  exact IsLocalRing.eq_maximalIdeal (Ideal.Quotient.maximal_of_isField _ hF')

theorem pts_subset_of_isContainedIn {X : Scheme.{u}} {V W : Subscheme X}
    (hWV : W.IsContainedIn V) : W.pts ⊆ V.pts :=
  Scheme.IdealSheafData.support_antitone (fun U => hWV U)

/-- The stalk of the ideal sheaf of a subscheme at a point of its support is contained in the
maximal ideal. -/
theorem stalkIdeal_le_maximalIdeal_of_mem_pts {X : Scheme.{u}} (D : Subscheme X)
    {x : X} (hx : x ∈ D.pts) :
    D.stalkIdeal x ≤ IsLocalRing.maximalIdeal (X.presheaf.stalk x) := by
  refine Ideal.span_le.mpr ?_
  rintro a ⟨U, hxU, s, hs, rfl⟩
  have h1 := (Scheme.IdealSheafData.mem_support_iff.mp hx) U
  rw [Scheme.mem_zeroLocus_iff] at h1
  have h2 := h1 s hs
  rw [Scheme.mem_basicOpen _ _ _ hxU] at h2
  exact (IsLocalRing.mem_maximalIdeal _).mpr h2

end Hironaka
