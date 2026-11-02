/-
Copyright (c) 2026 Daattavya Aggarwal, Minhyong Kim, Oisin Kim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daattavya Aggarwal, Minhyong Kim, Oisin Kim
-/
module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Architect
public import Hironaka.Ch1.ResolutionData
public import Hironaka.Compat.LocalizeSuccessionII
public import Hironaka.Compat.BlowupCompositionIdeals

/-!
# Weak transforms of products of sheaves of ideals (Ch. 0 §5, pp. 143–144, proof of Corollary 1)

The proof of Corollary 1 of Main Theorem II (p. 143) applies Main Theorem II to the product
`∏_{j=1}^e J_j` of a system of sheaves of ideals and then follows the weak transforms `J_j(i)` of the
individual factors.  The paper uses without comment that the two agree: the weak transform of the
product is the product of the weak transforms (the orders `ν((∏ J_j)_x) = ∑_j ν((J_j)_x)` add up).

This file collects the facts on `ν`, on the weak transform `f⁻¹(J)·P_E⁻ᵛ` of Remark 2 (p. 214) and on
points of products which are needed for that:

* `Subscheme.nu_stalkIdeal_prod`: `ν((∏ J_j)_x) = ∑ ν((J_j)_x)` on a non-singular scheme;
* `Subscheme.weakTransform_eq_divPow`, `Subscheme.totalTransform_eq_weakTransform_mul_pow`: Remark 2 on the
  nose, `J' = f⁻¹(J)·P_E⁻ᵛ` with `ν = ν(J_ξ)` and `f⁻¹(J) = J'·P_Eᵛ`;
* `Subscheme.weakTransform_prod`: the weak transform of a finite product of sheaves of non-zero ideals is the
  product of the weak transforms (unprinted: gap filled);
* `Subscheme.pts_preimage_eq_pts_weakTransform_union`: `f⁻¹(V(J)) = V(J') ∪ f⁻¹(D)` when `ν(J_z) ≥ 1` on the
  center `D`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace IsLocalRing

namespace Hironaka

universe u

/-! ### The order `ν` of a non-zero ideal is finite, and bounded on an algebraic scheme -/

section Order

/-- A non-zero ideal of a regular local ring has finite order `ν` (Krull's intersection theorem). -/
theorem Ideal.nu_ne_top_of_ne_bot {R : Type*} [CommRing R] [IsRegularLocalRing R] {I : Ideal R}
    (hI : I ≠ ⊥) : Ideal.nu I ≠ ⊤ := by
  have hbot := Ideal.iInf_pow_eq_bot_of_isLocalRing (maximalIdeal R)
    (maximalIdeal.isMaximal _).ne_top
  obtain ⟨n, hn⟩ : ∃ n, ¬ I ≤ maximalIdeal R ^ n := by
    by_contra h
    push Not at h
    exact hI (eq_bot_iff.mpr (hbot ▸ le_iInf h))
  refine ne_top_of_le_ne_top (ENat.natCast_ne_top n) (Ideal.ord_le fun ν hν => ?_)
  by_contra hlt
  push Not at hlt
  exact hn (hν.trans (Ideal.pow_le_pow_right (Nat.cast_lt.mp hlt).le))

/-- The order of a non-zero ideal of a regular local ring is a natural number. -/
theorem Ideal.exists_nu_eq_natCast {R : Type*} [CommRing R] [IsRegularLocalRing R] {I : Ideal R}
    (hI : I ≠ ⊥) : ∃ m : ℕ, Ideal.nu I = m := by
  obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.mp (Ideal.nu_ne_top_of_ne_bot hI)
  exact ⟨m, hm.symm⟩

variable {X : Scheme.{u}}

/-- On an algebraic scheme the orders `ν(J_x)` of a sheaf of non-zero ideals `J` are bounded (the open sets
`{x | ν(J_x) ≤ n}` cover the quasi-compact `X`; the argument of `DatumII.Raw.nu_ne_top`, p. 169). -/
theorem Subscheme.exists_forall_nu_stalkIdeal_le [Hironaka.Cited.IsHironakaBaseIsClosedSingularLocus.{u}] [Hironaka.Cited.CurveFiniteIntegralClosure.{u}] [Hironaka.Cited.IsRegularLocalRingLocalizationOfIsRegularLocalRing.{u}] [IsAlgebraicScheme X] (hX : X.IsNonsingular)
    (J : Subscheme X) (hJ : ∀ x, J.stalkIdeal x ≠ ⊥) : ∃ n : ℕ, ∀ x, Ideal.nu (J.stalkIdeal x) ≤ n := by
  have hfin : ∀ x : X, ∃ n : ℕ, Ideal.nu (J.stalkIdeal x) ≤ n := by
    intro x
    have : IsRegularLocalRing (X.presheaf.stalk x) := hX x
    obtain ⟨m, hm⟩ := Ideal.exists_nu_eq_natCast (hJ x)
    exact ⟨m, hm.le⟩
  choose U hUo hUmem using fun n : ℕ => exists_isOpen_nu_stalk_le X hX J n
  have := IsAlgebraicScheme.isNoetherian X
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover U hUo (fun x _ => by
    obtain ⟨n, hn⟩ := hfin x
    exact Set.mem_iUnion.mpr ⟨n, (hUmem n x).mpr hn⟩)
  refine ⟨s.sup id, fun x => ?_⟩
  obtain ⟨n, hn, hxn⟩ := Set.mem_iUnion₂.mp (hs (Set.mem_univ x))
  exact ((hUmem n x).mp hxn).trans (by exact_mod_cast Finset.le_sup (f := id) hn)

/-- `ν((∏_{i ∈ s} J_i)_x) = ∑_{i ∈ s} ν((J_i)_x)` on a non-singular scheme (additivity of `ν` in the regular local
ring `O_{X,x}`, `Ideal.nu_prod_eq`). -/
theorem Subscheme.nu_stalkIdeal_prod (hX : X.IsNonsingular) {ι : Type*} (s : Finset ι)
    (J : ι → Subscheme X) (x : X) :
    Ideal.nu ((∏ i ∈ s, J i).stalkIdeal x) = ∑ i ∈ s, Ideal.nu ((J i).stalkIdeal x) := by
  have : IsRegularLocalRing (X.presheaf.stalk x) := hX x
  rw [Subscheme.stalkIdeal_prod, Ideal.nu_prod_eq]

end Order

/-! ### Total transforms and points of products -/

section Points

variable {X X' : Scheme.{u}}

/-- The total transform of a finite product is the product of the total transforms. -/
theorem Subscheme.totalTransform_prod (f : X' ⟶ X) {ι : Type*} (s : Finset ι) (J : ι → Subscheme X) :
    Subscheme.totalTransform f (∏ i ∈ s, J i) = ∏ i ∈ s, Subscheme.totalTransform f (J i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    have : (1 : Subscheme X) = ⊤ := rfl
    have h' : (1 : Subscheme X') = ⊤ := rfl
    rw [Finset.prod_empty, Finset.prod_empty, this, h']
    exact Subscheme.totalTransform_top f
  | insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.prod_insert hi, Subscheme.totalTransform_mul, ih]

/-- The points of a product of sheaves of ideals are the union of the points of the factors (the stalk `I_x K_x` of
the local ring `O_{X,x}` is the unit ideal iff both factors are). -/
theorem Subscheme.pts_mul (I K : Subscheme X) : (I * K).pts = I.pts ∪ K.pts := by
  ext x
  simp only [Set.mem_union, Subscheme.mem_pts_iff_stalkIdeal_ne_top, Subscheme.stalkIdeal_mul_eq]
  constructor
  · intro h
    by_contra hcon
    push Not at hcon
    rw [hcon.1, hcon.2] at h
    exact h (by simp)
  · rintro (h | h) htop
    · exact h (top_le_iff.mp (htop.symm.le.trans Ideal.mul_le_left))
    · exact h (top_le_iff.mp (htop.symm.le.trans Ideal.mul_le_right))

/-- The points of a power of a sheaf of ideals with positive exponent are those of the sheaf. -/
theorem Subscheme.pts_pow (I : Subscheme X) {m : ℕ} (hm : 1 ≤ m) : (I ^ m).pts = I.pts := by
  ext x
  simp only [Subscheme.mem_pts_iff_stalkIdeal_ne_top, Subscheme.stalkIdeal_pow_eq]
  constructor
  · intro h htop
    exact h (by rw [htop]; simp)
  · intro h htop
    exact h (top_le_iff.mp (htop.symm.le.trans (Ideal.pow_le_self (by omega))))

end Points

/-! ### Remark 2 on the nose, and the weak transform of a product -/

section WeakTransform

variable {X : Scheme.{u}} {B : Subscheme X}

/-- Remark 2 (p. 214): "If `J_ξ` is not a zero ideal then `ν(J_ξ)` is a non-negative integer and we have
`J' = f⁻¹(J)·P_E⁻ᵛ` with `ν = ν(J_ξ)`": the increasing union defining the weak transform is attained at its last
term. -/
theorem Subscheme.weakTransform_eq_divPow (t : MonoidalTransformation X B) (J : Subscheme X) {ξ : X}
    (hξ : IsGenericPoint ξ B.pts) {m : ℕ} (hm : Ideal.nu (J.stalkIdeal ξ) = m) :
    Subscheme.weakTransform t J =
      Subscheme.divPow (Subscheme.totalTransform t.f J) t.exceptional m := by
  rw [Subscheme.weakTransform_eq t J hξ, hm]
  refine le_antisymm (iSup₂_le fun ν hν => Subscheme.divPow_mono _ _ (by exact_mod_cast hν)) ?_
  exact le_iSup₂_of_le m le_rfl le_rfl

/-- Remark 2 (p. 214): `f⁻¹(J) = J'·P_Eᵛ` with `ν = ν(J_ξ)` (`f⁻¹(J)` is divisible by `P_Eᵛ`, and `J'` is the
quotient). -/
theorem Subscheme.totalTransform_eq_weakTransform_mul_pow (hX : X.IsNonsingular)
    (hBns : B.IsNonsingular) (t : MonoidalTransformation X B) (J : Subscheme X) {ξ : X}
    (hξ : IsGenericPoint ξ B.pts) {m : ℕ} (hm : Ideal.nu (J.stalkIdeal ξ) = m) :
    Subscheme.totalTransform t.f J = Subscheme.weakTransform t J * t.exceptional ^ m := by
  rw [Subscheme.weakTransform_eq_divPow t J hξ hm]
  exact (Subscheme.divPow_mul_pow_eq t.invertible
    (Subscheme.totalTransform_le_exceptional_pow hX hBns t J hξ hm.ge)).symm

/-- Cancellation of a power of an invertible sheaf of ideals: `(K·Pᵛ)·P⁻ᵛ = K` (the generator of `P_x` is a
non-zero-divisor). -/
theorem Subscheme.divPow_mul_pow_self {P : Subscheme X} (hP : P.IsInvertibleIdeal) (K : Subscheme X)
    (m : ℕ) : Subscheme.divPow (K * P ^ m) P m = K := by
  refine Subscheme.ext_stalkIdeal fun x => ?_
  obtain ⟨g, hg, hnz⟩ := hP.exists_stalkIdeal_eq_span x
  rw [Subscheme.stalkIdeal_divPow hP, Subscheme.stalkIdeal_mul_eq, Subscheme.stalkIdeal_pow_eq, hg,
    Ideal.span_singleton_pow]
  ext a
  rw [Submodule.mem_colon]
  constructor
  · intro h
    have h1 := h (g ^ m) (by simp)
    rw [Ideal.mem_mul_span_singleton] at h1
    obtain ⟨z, hz, hza⟩ := h1
    have : z = a := by
      have h2 : (z - a) * g ^ m = 0 := by rw [sub_mul, hza, smul_eq_mul, sub_self]
      have := (mem_nonZeroDivisors_iff.mp (pow_mem hnz m)).2 _ h2
      exact sub_eq_zero.mp this
    exact this ▸ hz
  · intro ha p hp
    have hp' : p ∈ Ideal.span {g ^ m} := hp
    rw [Ideal.mem_span_singleton'] at hp'
    obtain ⟨c, rfl⟩ := hp'
    rw [Ideal.mem_mul_span_singleton]
    exact ⟨a * c, Ideal.mul_mem_right _ _ ha, by rw [smul_eq_mul]; ring⟩

/-- A center with a point is a non-singular irreducible subscheme: the generic point exists exactly for the
non-empty centers. -/
theorem Subscheme.IsCenter.isNonsingular_of_isGenericPoint (hB : B.IsCenter) {ξ : X}
    (hξ : IsGenericPoint ξ B.pts) : B.IsNonsingular := by
  rcases hB with h | h
  · exfalso
    have : B.pts = ∅ := by rw [h]; exact Subscheme.pts_empty
    have hξ' : ξ ∈ B.pts := hξ.mem
    rw [this] at hξ'
    exact hξ'
  · exact h.1

/-- **The weak transform of a product is the product of the weak transforms** (used on p. 144, proof of
Corollary 1, where Main Theorem II is applied to `∏ J_j` and the weak transforms `J_j(i)` of the factors are then
followed): for a sheaf of non-zero ideals `J_i` on a non-singular algebraic scheme and a monoidal transformation
with center `B` (non-singular irreducible, or empty),
`weakTransform (∏ J_i) = ∏ weakTransform J_i`.  By Remark 2, `f⁻¹(J_i) = J_i'·P_E^{m_i}` with
`m_i = ν((J_i)_ξ)`, so `f⁻¹(∏ J_i) = (∏ J_i')·P_E^{∑ m_i}` and `∑ m_i = ν((∏ J_i)_ξ)`. -/
theorem Subscheme.weakTransform_prod (hX : X.IsNonsingular) (hB : B.IsCenter)
    (t : MonoidalTransformation X B) {ι : Type*} (s : Finset ι) (J : ι → Subscheme X)
    (hJ : ∀ i x, (J i).stalkIdeal x ≠ ⊥) :
    Subscheme.weakTransform t (∏ i ∈ s, J i) = ∏ i ∈ s, Subscheme.weakTransform t (J i) := by
  classical
  by_cases h : ∃ ξ : X, IsGenericPoint ξ B.pts
  swap
  · have hw : ∀ K : Subscheme X,
        Subscheme.weakTransform t K = Subscheme.totalTransform t.f K := fun K => by
      unfold Subscheme.weakTransform
      simp only [h, dite_false]
    rw [hw, Subscheme.totalTransform_prod]
    exact Finset.prod_congr rfl fun i _ => (hw _).symm
  obtain ⟨ξ, hξ⟩ := h
  have hBns : B.IsNonsingular := hB.isNonsingular_of_isGenericPoint hξ
  have : IsRegularLocalRing (X.presheaf.stalk ξ) := hX ξ
  choose m hm using fun i => Ideal.exists_nu_eq_natCast (hJ i ξ)
  have hM : Ideal.nu ((∏ i ∈ s, J i).stalkIdeal ξ) = ((∑ i ∈ s, m i : ℕ) : ℕ∞) := by
    rw [Subscheme.nu_stalkIdeal_prod hX, Nat.cast_sum]
    exact Finset.sum_congr rfl fun i _ => hm i
  rw [Subscheme.weakTransform_eq_divPow t _ hξ hM, Subscheme.totalTransform_prod]
  have hprod : ∏ i ∈ s, Subscheme.totalTransform t.f (J i) =
      (∏ i ∈ s, Subscheme.weakTransform t (J i)) * t.exceptional ^ (∑ i ∈ s, m i) := by
    rw [← Finset.prod_pow_eq_pow_sum, ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun i _ =>
      Subscheme.totalTransform_eq_weakTransform_mul_pow hX hBns t (J i) hξ (hm i)
  rw [hprod]
  exact Subscheme.divPow_mul_pow_self t.invertible _ _

/-- The points of the weak transform: if `ν(J_z) ≥ 1` at the points `z` of the center `D` (that is, `D ⊆ V(J)`), then
`f⁻¹(V(J)) = V(J') ∪ f⁻¹(D)` (by Remark 2, `f⁻¹(J) = J'·P_Eᵛ` with `ν = ν(J_ξ) ≥ 1`; for an empty center
`J' = f⁻¹(J)`). -/
theorem Subscheme.pts_preimage_eq_pts_weakTransform_union (hX : X.IsNonsingular) (hB : B.IsCenter)
    (t : MonoidalTransformation X B) (J : Subscheme X) (hJ : ∀ x, J.stalkIdeal x ≠ ⊥)
    (h1 : ∀ z ∈ B.pts, 1 ≤ Ideal.nu (J.stalkIdeal z)) :
    t.f ⁻¹' J.pts = (Subscheme.weakTransform t J).pts ∪ t.f ⁻¹' B.pts := by
  by_cases h : ∃ ξ : X, IsGenericPoint ξ B.pts
  swap
  · have hw : Subscheme.weakTransform t J = Subscheme.totalTransform t.f J := by
      unfold Subscheme.weakTransform
      simp only [h, dite_false]
    have hB0 : B.pts = ∅ := by
      rcases hB with hB | hB
      · rw [hB]; exact Subscheme.pts_empty
      · obtain ⟨ξ, hξ⟩ := Subscheme.exists_isGenericPoint hB.2
        exact absurd ⟨ξ, hξ⟩ h
    rw [hw, FlatPreimm.pts_totalTransform, hB0]
    simp
  obtain ⟨ξ, hξ⟩ := h
  have hBns : B.IsNonsingular := hB.isNonsingular_of_isGenericPoint hξ
  have : IsRegularLocalRing (X.presheaf.stalk ξ) := hX ξ
  obtain ⟨m, hm⟩ := Ideal.exists_nu_eq_natCast (hJ ξ)
  have hm1 : 1 ≤ m := by
    have := h1 ξ hξ.mem
    rw [hm] at this
    exact_mod_cast this
  have hpts := congrArg Subscheme.pts
    (Subscheme.totalTransform_eq_weakTransform_mul_pow hX hBns t J hξ hm)
  rw [FlatPreimm.pts_totalTransform, Subscheme.pts_mul, Subscheme.pts_pow _ hm1,
    MonoidalTransformation.pts_exceptional] at hpts
  exact hpts

end WeakTransform

end Hironaka
