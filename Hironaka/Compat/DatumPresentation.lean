/-
Copyright (c) 2026 Daattavya Aggarwal, Minhyong Kim, Oisin Kim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daattavya Aggarwal, Minhyong Kim, Oisin Kim
-/
module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Basic
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Architect
public import Hironaka.Ch4.Preparation
public import Hironaka.Compat.DatumPresentationBase

/-!
# Irreducible components of subschemes and the presentation `(⋃ E_i; V_1, …, V_β; W)` of a datum

Ch. IV, p. 274 (introduction): "we shall often find it convenient to express a resolution datum of
type `ℜ^{N,n}_I` on a non-singular irreducible algebraic scheme `X` in the following form:
`ℜ^{N,n}_I = (⋃_{i=1}^α E_i; V_1, V_2, …, V_β; W)`.  We agree once for all that whenever this
expression is taken, all the `E_j` denote non-singular irreducible subschemes of `X` of
codimension one."

The paper uses the presentation without ever saying that every datum has one.  The proof that every
datum has one (`DatumI.Raw.isUnionOfDivisors_of_isDatum`) and the facts on irreducible components it uses are
in `Hironaka/Compat/DatumPresentationBase.lean`, upstream of `Hironaka/Ch4/Preparation.lean` (Lemma 4 of
Ch. IV §2 needs the presentation).

This file collects the other general facts on the irreducible components of a subscheme of a
noetherian scheme that are used for the same purpose elsewhere (the splitting of a non-singular
subscheme of pure codimension one into its connected components, which are its irreducible
components: they are finite in number, pairwise disjoint, open and closed in it, and have the stalk
ideals of the subscheme at their points).
-/

@[expose] public section

open AlgebraicGeometry TopologicalSpace IsLocalRing

namespace Hironaka

universe u

namespace Subscheme

variable {X : Scheme.{u}}

/-! ### Components of a non-singular subscheme -/

/-- The irreducible components of a non-singular subscheme are pairwise disjoint (its local rings
are domains). -/
theorem disjoint_pts_of_mem_irreducibleComponents {D C₁ C₂ : Subscheme X} (hD : D.IsNonsingular)
    (h₁ : C₁ ∈ D.irreducibleComponents) (h₂ : C₂ ∈ D.irreducibleComponents)
    (hne : C₁ ≠ C₂) : Disjoint C₁.pts C₂.pts := by
  rw [Set.disjoint_left]
  intro x hx₁ hx₂
  have hxD : x ∈ D.pts := pts_subset_of_mem_irreducibleComponents h₁ hx₁
  have hp := isPrime_stalkIdeal_of_isNonsingular_of_mem_pts D hD hxD
  exact hne (eq_of_stalkIdeal_eq h₁ h₂ hx₁ hx₂
    ((stalkIdeal_eq_of_mem_irreducibleComponents_of_isPrime h₁ hx₁ hp).trans
      (stalkIdeal_eq_of_mem_irreducibleComponents_of_isPrime h₂ hx₂ hp).symm))

/-- An irreducible component of a non-singular subscheme `D` of pure codimension one is a
non-singular irreducible subscheme of codimension one. -/
theorem isNonsingularIrreducibleCodimOne_of_mem_irreducibleComponents_of_isNonsingular
    {D C : Subscheme X} (hD : D.IsNonsingular) (hcod : D.IsEverywhereCodimOne)
    (hC : C ∈ D.irreducibleComponents) : C.IsNonsingularIrreducibleCodimOne := by
  refine Or.inr ⟨isNonsingular_of_stalk_quot C fun z hz => ?_,
    isIrreducible_of_mem_irreducibleComponents hC, ?_⟩
  · have hzD : z ∈ D.pts := pts_subset_of_mem_irreducibleComponents hC hz
    have hp := isPrime_stalkIdeal_of_isNonsingular_of_mem_pts D hD hzD
    rw [stalkIdeal_eq_of_mem_irreducibleComponents_of_isPrime hC hz hp]
    exact isRegular_stalk_quot D hD hzD
  · obtain ⟨z₀, hz₀⟩ := nonempty_pts_of_mem_irreducibleComponents hC
    have hcodim : ∀ z ∈ C.pts, C.codimAt z = 1 := fun z hz => by
      have hzD : z ∈ D.pts := pts_subset_of_mem_irreducibleComponents hC hz
      have hp := isPrime_stalkIdeal_of_isNonsingular_of_mem_pts D hD hzD
      show (C.stalkIdeal z).height = 1
      rw [stalkIdeal_eq_of_mem_irreducibleComponents_of_isPrime hC hz hp]
      exact hcod z hzD
    exact le_antisymm ((iInf₂_le z₀ hz₀).trans (hcodim z₀ hz₀).le)
      (le_iInf₂ fun z hz => (hcodim z hz).ge)

/-- The irreducible components of a non-singular subscheme `D` of pure codimension one on a
scheme with noetherian underlying space: there are finitely many, they are non-singular
irreducible of codimension one, pairwise disjoint, have at their points the stalk ideals of `D`,
and their union is `D`. -/
theorem exists_family_of_isNonsingular [NoetherianSpace X] {D : Subscheme X}
    (hD : D.IsNonsingular) (hcod : D.IsEverywhereCodimOne) :
    ∃ (α : ℕ) (C : Fin α → Subscheme X), (∀ i, C i ∈ D.irreducibleComponents) ∧
      (∀ i, (C i).IsNonsingularIrreducibleCodimOne) ∧
      (∀ i j, i ≠ j → Disjoint (C i).pts (C j).pts) ∧
      (∀ i, ∀ x ∈ (C i).pts, (C i).stalkIdeal x = D.stalkIdeal x) ∧ D = ⨅ i, C i := by
  obtain ⟨α, C, hC, hinj, hcov⟩ := exists_family_irreducibleComponents D
  refine ⟨α, C, hC, fun i =>
      isNonsingularIrreducibleCodimOne_of_mem_irreducibleComponents_of_isNonsingular hD hcod
        (hC i),
    fun i j hij => disjoint_pts_of_mem_irreducibleComponents hD (hC i) (hC j) (hinj.ne hij),
    fun i x hx => stalkIdeal_eq_of_mem_irreducibleComponents_of_isPrime (hC i) hx
      (isPrime_stalkIdeal_of_isNonsingular_of_mem_pts D hD
        (pts_subset_of_mem_irreducibleComponents (hC i) hx)),
    eq_iInf_of_isReduced (DatumTransform.isReduced_of_isNonsingular hD) C hC hcov⟩

/-! ### Components and a closed restriction -/

/-- If `W − F` is dense in `W`, no irreducible component of `W` lies in `F`. -/
theorem not_pts_subset_of_mem_irreducibleComponents_of_subset_closure_diff [NoetherianSpace X]
    {W F C : Subscheme X} (hC : C ∈ W.irreducibleComponents)
    (hdense : W.pts ⊆ closure (W.pts \ F.pts)) : ¬ C.pts ⊆ F.pts := by
  classical
  intro hCF
  set ℱ : Set (Set X) := (fun C' : Subscheme X => C'.pts) ''
    {C' | C' ∈ W.irreducibleComponents ∧ C' ≠ C} with hℱ
  have hfin : ℱ.Finite := ((finite_irreducibleComponents_of_noetherianSpace W).subset fun C' hC' => hC'.1).image _
  have hcl : ∀ B ∈ ℱ, IsClosed B := by
    rintro _ ⟨C', -, rfl⟩
    exact C'.support.isClosed
  have hcl' : IsClosed (⋃₀ ℱ) := (hfin.isClosed_sUnion hcl)
  have hsub : W.pts \ F.pts ⊆ ⋃₀ ℱ := by
    intro y hy
    obtain ⟨C', hC', hyC'⟩ := exists_mem_irreducibleComponents_of_mem_pts W hy.1
    refine ⟨C'.pts, ⟨C', ⟨hC', fun h => hy.2 (hCF (h ▸ hyC'))⟩, rfl⟩, hyC'⟩
  have hCW : C.pts ⊆ ⋃₀ ℱ :=
    (pts_subset_of_mem_irreducibleComponents hC).trans (hdense.trans (closure_minimal hsub hcl'))
  obtain ⟨Z, hZ, rfl⟩ := hC
  rw [pts_ofClosed] at hCW hCF
  obtain ⟨B, ⟨C', ⟨⟨Z', hZ', rfl⟩, hne⟩, rfl⟩, hZB⟩ :=
    isIrreducible_subset_of_finite_sUnion hZ.1.1 hfin hcl hCW
  have hZB' : (Z : Set X) ⊆ Z' := by rw [← pts_ofClosed Z']; exact hZB
  have : Z' ≤ Z := hZ.2 hZ'.1 hZB'
  exact hne (by rw [le_antisymm this hZB'])

/-- At a point `y` of a reduced subscheme `D` with no proper generization in `D`, the stalk of the
ideal sheaf is the maximal ideal: every minimal prime of the (radical) stalk is the stalk of a
component through `y`, whose generic point is a generization of `y` lying on `D`. -/
theorem stalkIdeal_eq_maximalIdeal_of_forall_specializes {D : Subscheme X} (hD : D.IsReduced)
    {y : X} (hy : y ∈ D.pts) (hmin : ∀ y' ∈ D.pts, y' ⤳ y → y' = y) :
    D.stalkIdeal y = maximalIdeal (X.presheaf.stalk y) := by
  refine le_antisymm (stalkIdeal_le_maximalIdeal D hy) ?_
  rw [← (isRadical_stalkIdeal_of_isReduced hD y).radical, ← Ideal.sInf_minimalPrimes]
  refine le_sInf fun p hp => ?_
  obtain ⟨C, hC, hyC, rfl⟩ := exists_mem_irreducibleComponents_of_mem_minimalPrimes D y hp
  obtain ⟨Z, hZ, rfl⟩ := hC
  rw [pts_ofClosed] at hyC
  obtain ⟨η, hη⟩ : ∃ η, IsGenericPoint η (Z : Set X) := QuasiSober.sober hZ.1.1 Z.isClosed
  have hηy : η ⤳ y := specializes_iff_mem_closure.mpr (by rw [hη.def]; exact hyC)
  have hηD : η ∈ D.pts := hZ.1.2 hη.mem
  obtain rfl : η = y := hmin η hηD hηy
  rw [stalkIdeal_eq_maximalIdeal_of_isGenericPoint (ofClosed_isReduced Z)
    (by rw [pts_ofClosed]; exact hZ.1.1) (by rw [pts_ofClosed]; exact hη)]

/-! ### The components of a datum's boundary -/


end Subscheme

end Hironaka
