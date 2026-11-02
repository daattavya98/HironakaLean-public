/-
Copyright (c) 2026 Daattavya Aggarwal, Minhyong Kim, Oisin Kim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daattavya Aggarwal, Minhyong Kim, Oisin Kim
-/
module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.Order.CompletePartialOrder
public import Architect
public import Hironaka.Compat.ExtendSuccession
public import Hironaka.Compat.LocalizeSuccessionII

/-!
# Extension of successions from an open subscheme, type II data (Ch. IV §4, p. 312)

> As is easily seen, by replacing `X` by `X − S(J)` where `S(J) = {x ∈ X | ν(J_x) ≥ 1}`, we may
> assume that `J` is the sheaf of local rings `O_X` of `X`. (p. 312, proof of Lemma (D.1))

The restriction of a type II datum to an open subscheme is `DatumII.Raw.pullback`
(`Compat/LocalizeSuccessionII.lean`).  This file proves the extension, back over `X`, of a
permissible succession of the open subscheme, for type II data: the analogue of
`MonoidalSuccession.exists_extension` (`Compat/ExtendSuccession.lean`, p. 291, step 7) with the
transform of the datum and the permissibility.  The hypothesis replacing "the centers are closed
in `X`" is that the set `S(ℜ)` is closed and contained in the open subscheme, since every center
of a permissible succession lies in the transforms of `S(ℜ)`.

Gap filled (the paper's "as is easily seen"): that the transforms of `ℜ` over `X` restrict to the
transforms of the restriction (`DatumII.Raw.pullback_transform_of_lift`, with the equality
`ν(ℜ_Z) = ν(ℜ)` and the containment of the centers in the same `E_i`), that a permissible center
of the restriction has closure a permissible center for `ℜ`, and that `S` of the transform over
`X` stays in the open subscheme.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

namespace Hironaka

universe u

namespace DatumII.Raw

variable {Z Y : Scheme.{u}}

/-- `ν` does not drop under the pull-back along a flat preimmersion whose range contains `S(ℜ)`. -/
theorem nu_pullback_eq (j : Z ⟶ Y) [Flat j] [IsPreimmersion j] (ℜ : Raw Y)
    (h : ℜ.S ⊆ Set.range j.base) : (ℜ.pullback j).nu = ℜ.nu := by
  refine le_antisymm (nu_pullback_le j ℜ) (iSup₂_le fun y hy => ?_)
  obtain ⟨z, rfl⟩ := h hy
  have hz : z ∈ (ℜ.pullback j).S := (mem_S_pullback j ℜ z).mpr hy
  rw [← nuAt_pullback j ℜ z]
  exact le_iSup₂ (f := fun x (_ : x ∈ (ℜ.pullback j).S) => (ℜ.pullback j).nuAt x) z hz

/-- A reduced subscheme `BY` of `Y` contained in the range of a flat preimmersion `j : Z → Y`,
whose total transform is a permissible center of the restriction `ℜ_Z` (and with `ν(ℜ_Z) = ν(ℜ)`),
is a permissible center for `ℜ`: type II analogue of `DatumI.Raw.isPermissible_of_isPermissible_pullback`. -/
theorem isPermissible_of_isPermissible_pullback (j : Z ⟶ Y) [Flat j] [IsPreimmersion j]
    {ℜ : Raw Y} {BY : Subscheme Y} {B : Subscheme Z}
    (htt : Subscheme.totalTransform j BY = B) (hpts : BY.pts ⊆ Set.range j.base)
    (hν : (ℜ.pullback j).nu = ℜ.nu) (hperm : (ℜ.pullback j).IsPermissible B) :
    ℜ.IsPermissible BY := by
  have hBYpts : BY.pts = j.base '' B.pts := by
    rw [← htt, FlatPreimm.pts_totalTransform, Set.image_preimage_eq_of_subset hpts]
  refine ⟨DatumI.Raw.isCenter_of_totalTransform_eq j htt hpts hperm.1, fun y hy => ?_,
    fun y hy => ?_⟩
  · obtain ⟨z, hz, rfl⟩ : y ∈ j.base '' B.pts := hBYpts ▸ hy
    have h1 : z ∈ (ℜ.pullback j).sStar := hperm.2.1 hz
    have h2 : z ∈ (ℜ.pullback j).sNu (ℜ.pullback j).nu := h1
    rw [mem_sNu_pullback] at h2
    rw [hν] at h2
    exact h2
  · obtain ⟨z, hz, rfl⟩ : y ∈ j.base '' B.pts := hBYpts ▸ hy
    have h := hperm.2.2 z hz
    rw [← FlatPreimm.hasOnlyNormalCrossingsWithAt_totalTransform_iff j ℜ.eUnion BY z, htt]
    refine (Subscheme.hasOnlyNormalCrossingsWithAt_congr ?_ B z).mpr h
    rw [FlatPreimm.pts_totalTransform, pts_eUnion_pullback]


/-- The restriction of a type II datum to the source of a flat preimmersion is a datum (Remark 1,
p. 276; for an open subscheme, p. 312). -/
theorem isDatum_pullback (g : Z ⟶ Y) [Flat g] [IsPreimmersion g] {ℜ : Raw Y} (hℜ : ℜ.IsDatum) :
    (ℜ.pullback g).IsDatum := by
  obtain ⟨hb, hE, hnc, hJ⟩ := hℜ
  refine ⟨hb, fun i => ?_, fun z => ?_, fun z => ?_⟩
  · show (Subscheme.totalTransform g (ℜ.E i)).IsNonsingularIrreducibleCodimOne
    rcases hE i with h | ⟨hns, hirr, hcod⟩
    · left
      rw [h]
      exact Subscheme.totalTransform_empty g
    · rcases FlatPreimm.empty_or_isIrreducible_totalTransform g _ hirr with h | h
      · exact Or.inl h
      · refine Or.inr ⟨FlatPreimm.isNonsingular_totalTransform g _ hns, h, ?_⟩
        obtain ⟨z, hz⟩ := (Subscheme.isIrreducible_pts _ h).nonempty
        have hz' : g z ∈ (ℜ.E i).pts := by
          rwa [FlatPreimm.pts_totalTransform] at hz
        rw [Subscheme.codim_eq_height _ (FlatPreimm.isNonsingular_totalTransform g _ hns) h hz]
        have h1 : (Subscheme.totalTransform g (ℜ.E i)).codimAt z = (ℜ.E i).codimAt (g z) :=
          FlatPreimm.codimAt_totalTransform g _ z
        have h2 := Subscheme.codim_eq_height (ℜ.E i) hns hirr hz'
        exact h1.trans (h2.symm.trans hcod)
  · show (pullback g ℜ).eUnion.HasOnlyNormalCrossingsWithAt ⊥ z
    have h1 := (FlatPreimm.hasOnlyNormalCrossingsWithAt_totalTransform_iff g ℜ.eUnion ⊥ z).mpr
      (hnc _)
    rw [show Subscheme.totalTransform g (⊥ : Subscheme Y) = ⊥ from
      Scheme.IdealSheafData.comap_bot _] at h1
    refine (Subscheme.hasOnlyNormalCrossingsWithAt_congr ?_ ⊥ z).mp h1
    rw [FlatPreimm.pts_totalTransform, pts_eUnion_pullback]
  · show (Subscheme.totalTransform g ℜ.J).stalkIdeal z ≠ ⊥
    rw [FlatPreimm.stalkIdeal_totalTransform]
    exact fun h => hJ (g z) ((Ideal.map_eq_bot_iff_of_injective
      (FlatPreimm.stalkEquiv g z).injective).mp h)

end DatumII.Raw

namespace MonoidalSuccession

variable {Z Z' Y : Scheme.{u}}

/-- **Extension of a permissible succession of an open piece, type II** (p. 312, "by replacing `X`
by `X − S(J)`"): let `j : Z → Y` be a flat preimmersion, `ℜ` a type II datum on the non-singular
algebraic scheme `Y` and `C ⊇ S(ℜ)` a closed subset contained in `j(Z)`.  Every succession `s` of
`Z` permissible for the restriction `ℜ_Z` is induced by a succession of `Y` permissible for `ℜ`,
whose transform of `ℜ` restricts to the transform of `ℜ_Z`, and `S` of which stays in the image
of `Z'`. -/
theorem exists_extensionII [Hironaka.Cited.IsHironakaBaseIsClosedSingularLocus.{u}] [Hironaka.Cited.MonoidalTransformationExistsIsProper.{u}] [Hironaka.Cited.CurveFiniteIntegralClosure.{u}] [Hironaka.Cited.IsRegularLocalRingLocalizationOfIsRegularLocalRing.{u}] (s : MonoidalSuccession Z Z') :
    ∀ {Y : Scheme.{u}} (j : Z ⟶ Y) [Flat j] [IsPreimmersion j] [IsAlgebraicScheme Y]
      (_ : Y.IsNonsingular) (ℜ : DatumII.Raw Y) (_ : ℜ.IsDatum) (C : Set Y), IsClosed C →
      C ⊆ Set.range j.base → ℜ.S ⊆ C → s.IsPermissibleII (ℜ.pullback j) →
      ∃ (Y' : Scheme.{u}) (sY : MonoidalSuccession Y Y') (j' : Z' ⟶ Y'), Flat j' ∧
        IsPreimmersion j' ∧ j' ≫ sY.composite = s.composite ≫ j ∧
        Set.range j'.base = sY.composite.base ⁻¹' Set.range j.base ∧
        (∀ V, Subscheme.totalTransform j' (sY.strictTransform V) =
          s.strictTransform (Subscheme.totalTransform j V)) ∧
        (sY.transformII ℜ).pullback j' = s.transformII (ℜ.pullback j) ∧
        sY.IsPermissibleII ℜ ∧ (sY.transformII ℜ).S ⊆ Set.range j'.base := by
  induction s with
  | nil Z =>
    intro Y j _ _ _ _ ℜ _ C _ hCj hSC _
    exact ⟨Y, nil Y, j, inferInstance, inferInstance, by simp, by simp, fun V => rfl, rfl,
      trivial, hSC.trans hCj⟩
  | cons B ts rest ih =>
    intro Y j _ _ _ hY ℜ hℜ C hC hCj hSC hs
    have hXa : IsAlgebraicScheme Y := inferInstance
    obtain ⟨hperm, hrest⟩ := hs
    have hν : (ℜ.pullback j).nu = ℜ.nu := DatumII.Raw.nu_pullback_eq j ℜ (hSC.trans hCj)
    have hBred : B.IsReduced := hperm.1.isReduced
    -- the image of the center is closed: it lies in `S(ℜ) ⊆ C ⊆ j(Z)`
    have hBC : j.base '' B.pts ⊆ C := by
      rintro _ ⟨z, hz, rfl⟩
      have h1 : z ∈ (ℜ.pullback j).sStar := hperm.2.1 hz
      have h2 : z ∈ (ℜ.pullback j).S := h1.1
      exact hSC ((DatumII.Raw.mem_S_pullback j ℜ z).mp h2)
    have hcl : IsClosed (j.base '' B.pts) := by
      have h1 : closure (j.base '' B.pts) ⊆ C := closure_minimal hBC hC
      have h2 := FlatPreimm.pts_closureLift_inter_range j B
      rw [FlatPreimm.pts_closureLift] at h2
      rw [← h2, Set.inter_eq_left.mpr (h1.trans hCj)]
      exact isClosed_closure
    obtain ⟨BY, tY, j', hfl, hpre, hBYred, hBYpts, htt, hsq, hrange, hexc, hst⟩ :=
      MonoidalTransformation.exists_extend_step j hBred hcl ts
    have hrng : BY.pts ⊆ Set.range j.base := by
      rw [hBYpts]; rintro _ ⟨z, -, rfl⟩; exact ⟨z, rfl⟩
    have hpBY : ℜ.IsPermissible BY :=
      DatumII.Raw.isPermissible_of_isPermissible_pullback j htt hrng hν hperm
    -- the new exponent: `BY` lies in exactly those `E_i` whose restrictions contain `B`
    have hcont : ∀ i, BY.IsContainedIn (ℜ.E i) ↔
        B.IsContainedIn (Subscheme.totalTransform j (ℜ.E i)) := by
      intro i
      constructor
      · intro hc
        rw [← htt]
        exact fun U => FlatPreimm.totalTransform_mono j (show _ ≤ BY from fun U => hc U) U
      · intro hc
        refine Subscheme.isContainedIn_of_pts_subset hBYred ?_
        rw [hBYpts]
        rintro _ ⟨z, hz, rfl⟩
        have := pts_subset_of_isContainedIn hc hz
        rwa [FlatPreimm.pts_totalTransform] at this
    have htr1 : (ℜ.transform tY).pullback j' = (ℜ.pullback j).transform ts :=
      DatumII.Raw.pullback_transform_of_lift tY j ts j' hsq hexc hst ℜ hcont hν
    -- the hypotheses for the next step
    have hY1a : IsAlgebraicScheme tY.X' := tY.isAlgebraicScheme
    have hY1 : tY.X'.IsNonsingular :=
      (tY.isNonsingular_and_isNonsingular_exceptional hY hpBY.1.isNonsingular).1
    have hℜ1 : (ℜ.transform tY).IsDatum :=
      (DatumII.Raw.transform_isDatum hY ℜ hℜ tY hpBY).1
    have hS1 : (ℜ.transform tY).S ⊆ tY.f.base ⁻¹' C := fun y hy =>
      hSC (DatumII.Raw.mem_S_of_mem_S_transform hY ℜ hℜ tY hpBY hy)
    obtain ⟨Y', sY, j'', hfl', hpre', hcomp, hrange', hst', htr, hpermY, hSY⟩ :=
      ih j' hY1 (ℜ.transform tY) hℜ1 (tY.f.base ⁻¹' C) (hC.preimage tY.f.continuous)
        (fun y hy => by rw [hrange]; exact hCj hy) hS1 (by rw [htr1]; exact hrest)
    refine ⟨Y', cons BY tY sY, j'', hfl', hpre', ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [composite_cons, composite_cons, ← Category.assoc, hcomp, Category.assoc, hsq,
        Category.assoc]
    · rw [hrange', composite_cons, hrange]
      rfl
    · intro V
      rw [strictTransform_cons, strictTransform_cons, hst', hst]
    · rw [transformII_cons, transformII_cons, htr, htr1]
    · exact ⟨hpBY, hpermY⟩
    · rw [transformII_cons]; exact hSY

end MonoidalSuccession

end Hironaka
