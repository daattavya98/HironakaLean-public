/-
Copyright (c) 2026 Daattavya Aggarwal, Minhyong Kim, Oisin Kim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daattavya Aggarwal, Minhyong Kim, Oisin Kim
-/
module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Hironaka.Ch3.Transforms
public import Hironaka.Compat.BlowupBaseChange
public import Hironaka.Compat.SubschemeStalk

/-!
# Lemma 4 of Ch. IV §2 near a point: the open-neighbourhood lemmas

The proofs of Lemma (AB.1) (p. 294), of Proposition 5 (p. 290) and of Remark 1 of §3 (p. 307) cite
"Lemma 4, §2, Ch. IV" (with Corollary 2 of Theorem 5, §6, Ch. III) for a datum `ℜ` which is resolved
only at the point `x` considered, whereas Lemma 4 is stated for a non-singular irreducible `W`, with
`E = E_1 ∪ ⋯ ∪ E_α` having only normal crossings with `W` and with `B`, at *every* point.  The citation
implicitly localizes: near `x` the hypotheses of Lemma 4 hold on an open neighbourhood `O` of `x`.  The
localization itself is `DatumI.Raw.hasOnlyNormalCrossingsWithAt_transform_of_resolvedAt_localized`
(`Hironaka/Ch4/Preparation.lean`, right after Lemma 4); this file contains the general facts on subschemes
and open subschemes that it uses and that do not depend on Lemma 4:
* `Subscheme.exists_isOpen_isSimpleAt`: the simple points of `W` form the trace of an open set (Ch. 0 (iii), p. 161);
* `Subscheme.mem_pts_iff_le_primeIdealOf`, `Subscheme.isIrreducible_pts_inter_of_isPrime`: if the ideal of
  `D` in an affine open `V` is prime, `D ∩ V` is irreducible;
* `FlatPreimm.totalTransform_iInf`: pull-back along a flat preimmersion commutes with finite unions.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

universe u

namespace Hironaka

/-! ### Open sets of simple points and irreducible neighbourhoods -/

namespace Subscheme

variable {Z : Scheme.{u}}

/-- The simple points of `W` form the trace of an open subset (Ch. 0 (iii), p. 161). -/
theorem exists_isOpen_isSimpleAt [Hironaka.Cited.IsHironakaBaseIsClosedSingularLocus.{u}] [IsAlgebraicScheme Z] (W : Subscheme Z) :
    ∃ O : Set Z, IsOpen O ∧ ∀ y ∈ W.pts, (W.IsSimpleAt y ↔ y ∈ O) := by
  have := isAlgebraicScheme_toScheme W
  obtain ⟨Os, hOs, hOsW⟩ :=
    W.ι.isEmbedding.isInducing.isOpen_iff.mp (isOpen_setOf_isSimpleAt W.toScheme)
  refine ⟨Os, hOs, fun y hy => ?_⟩
  obtain ⟨y', rfl⟩ := exists_ι_eq_of_mem_pts W hy
  obtain ⟨e⟩ := nonempty_stalk_quot_equiv W y'
  rw [← Set.mem_preimage, hOsW]
  constructor
  · rintro ⟨-, h⟩
    have : IsRegularLocalRing (Z.presheaf.stalk (W.ι y') ⧸ W.stalkIdeal (W.ι y')) := h
    exact IsRegularLocalRing.of_ringEquiv e
  · intro h
    have : IsRegularLocalRing (W.toScheme.presheaf.stalk y') := h
    exact ⟨hy, IsRegularLocalRing.of_ringEquiv e.symm⟩

/-- On an affine open `V`, a point `z` of `V` lies on `D` iff the ideal of `D` in `Γ(Z, V)` is
contained in the prime of `z`. -/
theorem mem_pts_iff_le_primeIdealOf (D : Subscheme Z) {V : Z.Opens} (hV : IsAffineOpen V) {z : Z}
    (hz : z ∈ V) :
    z ∈ D.pts ↔ D.ideal ⟨V, hV⟩ ≤ (hV.primeIdealOf ⟨z, hz⟩).asIdeal := by
  rw [mem_pts_iff_of_affine D (U := ⟨V, hV⟩) hz]
  constructor
  · intro h f hf
    rw [Subscheme.mem_primeIdealOf_iff hV hz f, Scheme.mem_basicOpen _ _ _ hz]
    exact h f hf
  · intro h f hf hu
    have := (Subscheme.mem_primeIdealOf_iff hV hz f).mp (h hf)
    exact this ((Scheme.mem_basicOpen _ _ _ hz).mpr hu)

/-- If the ideal of `D` in an affine open `V` is prime, then `D ∩ V` is irreducible. -/
theorem isIrreducible_pts_inter_of_isPrime (D : Subscheme Z) {V : Z.Opens} (hV : IsAffineOpen V)
    (hP : (D.ideal ⟨V, hV⟩).IsPrime) : _root_.IsIrreducible (D.pts ∩ (V : Set Z)) := by
  have hS : D.pts ∩ (V : Set Z) = hV.fromSpec '' PrimeSpectrum.zeroLocus (D.ideal ⟨V, hV⟩ : Set _) := by
    ext z
    constructor
    · rintro ⟨hzD, hzV⟩
      refine ⟨hV.primeIdealOf ⟨z, hzV⟩, ?_, hV.fromSpec_primeIdealOf ⟨z, hzV⟩⟩
      exact (mem_pts_iff_le_primeIdealOf D hV hzV).mp hzD
    · rintro ⟨q, hq, rfl⟩
      have hzV : hV.fromSpec q ∈ V := by
        rw [← SetLike.mem_coe, ← hV.range_fromSpec]; exact ⟨q, rfl⟩
      have hprime : hV.primeIdealOf ⟨hV.fromSpec q, hzV⟩ = q := by
        apply hV.fromSpec.isOpenEmbedding.injective
        exact hV.fromSpec_primeIdealOf ⟨hV.fromSpec q, hzV⟩
      refine ⟨(mem_pts_iff_le_primeIdealOf D hV hzV).mpr ?_, hzV⟩
      rw [hprime]; exact hq
  rw [hS]
  exact ((PrimeSpectrum.isIrreducible_zeroLocus_iff _).mpr (by rwa [hP.radical])).image _
    hV.fromSpec.continuous.continuousOn

end Subscheme

namespace FlatPreimm

variable {Y Y' : Scheme.{u}} (g : Y' ⟶ Y) [Flat g] [IsPreimmersion g]

/-- Pull-back along a flat preimmersion commutes with finite unions of subschemes. -/
theorem totalTransform_iInf {ι : Type*} [Fintype ι] (E : ι → Subscheme Y) :
    Subscheme.totalTransform g (⨅ i, E i) = ⨅ i, Subscheme.totalTransform g (E i) := by
  classical
  have key : ∀ s : Finset ι, Subscheme.totalTransform g (⨅ i ∈ s, E i) =
      ⨅ i ∈ s, Subscheme.totalTransform g (E i) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simpa using Subscheme.totalTransform_top g
    | insert a s ha ih => rw [Finset.iInf_insert, Finset.iInf_insert, totalTransform_inf, ih]
  simpa using key Finset.univ

end FlatPreimm

end Hironaka
