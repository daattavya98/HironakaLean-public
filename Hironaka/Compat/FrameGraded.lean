/-
Copyright (c) 2026 Daattavya Aggarwal, Minhyong Kim, Oisin Kim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daattavya Aggarwal, Minhyong Kim, Oisin Kim
-/
module

public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
public import Mathlib.RingTheory.MvPowerSeries.Order
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Architect
public import Hironaka.Compat.CoefficientField
public import Hironaka.Compat.TauZSystem
public import Hironaka.Ch3.PermissibleEffects

/-!
# Compatibility layer: the graded ring of a regular frame (Ch. III §7 and §10, pp. 246–248, 269–270)

For a regular frame `(S; z₁, …, z_r)` of `R` (Definition 9) and the power series expansion
`g = Σ_A c_A z^A`, `c_A ∈ S`, of an element `g` of `R` (p. 246) the paper uses, without comment,
that `gr_M(R)` is `gr_N(S)[Z₁, …, Z_r]` and that the initial form of `g` is read off from the
`c_A` ("`Let φ_A be the initial form of h_A in gr_M(R) only for those A with |A| + ν_M(h_A) = ν.
Then φ = Σ_A φ_A Z^A`", p. 270).  This file proves it:

* `RegularFrame.maximalIdeal_eq_idealZ_sup_map`: `M = (z)R + NR`;
* `RegularFrame.mem_maximalIdeal_pow_iff_coeff_mem_pow`: `g ∈ Mᵈ` iff `c_A(g) ∈ N^{d-|A|}` for all
  `A` with `|A| ≤ d` (so `ν_M(g) = min_A (|A| + ν_N(c_A))`);
* `RegularFrame.mk_eq_sum_grMap_mul`: for `g ∈ Mᵈ`, the class of `g` in `grᵈ_M(R)` is
  `Σ_{|A| ≤ d} [c_A]_{d-|A|} Z^A`, where `[c]_k = F.grMap k c` is the class of `c ∈ N^k` in
  `gr^k_N(S) → gr^k_M(R)` (zero if `c ∉ N^k`) and `Z_j = frameForm F.z j`.

The statements are for an arbitrary power series expansion map `e` (`RegularFrame.IsExpansion`,
which exists and is unique: `RegularFrame.idealZ_isPrime_and_completion`).
-/

@[expose] public section

open IsLocalRing

namespace Hironaka

universe u

namespace RegularFrame

section Order

variable {R : Type u} [CommRing R] [IsRegularLocalRing R] (F : RegularFrame R)

/-- `M = (z₁, …, z_r)R + NR` for a regular frame `(S; z₁, …, z_r)` of `R`, `N` the maximal ideal
of `S` (the retraction `R → R/P ≅ S` maps `M` into `N`). -/
theorem maximalIdeal_eq_idealZ_sup_map :
    maximalIdeal R = F.idealZ ⊔ (maximalIdeal F.S).map (algebraMap F.S R) := by
  classical
  have hP : F.idealZ ≤ maximalIdeal R := by
    obtain ⟨s₀, hsub, hs₀⟩ := F.extends_rsop
    refine Ideal.span_le.mpr ?_
    rintro _ ⟨i, rfl⟩
    rw [← hs₀.1]
    exact Ideal.subset_span (hsub (Finset.mem_image_of_mem _ (Finset.mem_univ i)))
  refine le_antisymm (fun m hm => ?_) (sup_le hP (map_maximalIdeal_le _))
  let e := RingEquiv.ofBijective _ F.quot_bijective
  let π : R →+* F.S := e.symm.toRingHom.comp (Ideal.Quotient.mk F.idealZ)
  have hπ : ∀ t, π (algebraMap F.S R t) = t := fun t => e.symm_apply_apply t
  have hsub : m - algebraMap F.S R (π m) ∈ F.idealZ := by
    rw [← Ideal.Quotient.eq]
    exact (e.apply_symm_apply (Ideal.Quotient.mk _ m)).symm
  have h2 : algebraMap F.S R (π m) ∈ maximalIdeal R := by
    have := sub_mem hm (hP hsub)
    rwa [sub_sub_cancel] at this
  have h3 : π m ∈ maximalIdeal F.S := by
    rw [mem_maximalIdeal, mem_nonunits_iff] at h2 ⊢
    exact fun hu => h2 (hu.map (algebraMap F.S R))
  have : m = (m - algebraMap F.S R (π m)) + algebraMap F.S R (π m) := by ring
  rw [this]
  exact Submodule.add_mem_sup hsub (Ideal.mem_map_of_mem _ h3)

end Order


section Coeff

variable {R : Type u} [CommRing R] [IsRegularLocalRing R] (F : RegularFrame R)

open Classical in
/-- `𝒬_d = {g ∈ R | c_A(g) ∈ N^{d - |A|} for all A with |A| ≤ d}`, `c_A` the coefficients of the
power series expansion `e`: an ideal of `R`. -/
def coeffPowIdeal (e : R →+* MvPowerSeries (Fin F.r) F.S) (d : ℕ) : Ideal R where
  carrier := {g | ∀ A : Fin F.r →₀ ℕ, A.degree ≤ d →
    MvPowerSeries.coeff A (e g) ∈ maximalIdeal F.S ^ (d - A.degree)}
  add_mem' := by
    intro a b ha hb A hA
    rw [map_add, map_add]
    exact add_mem (ha A hA) (hb A hA)
  zero_mem' := by
    intro A hA
    rw [map_zero, map_zero]
    exact zero_mem _
  smul_mem' := by
    intro c g hg A hA
    rw [smul_eq_mul, map_mul, MvPowerSeries.coeff_mul]
    refine Ideal.sum_mem _ fun p hp => ?_
    have hp' := Finset.HasAntidiagonal.mem_antidiagonal.mp hp
    have hdeg : p.2.degree ≤ A.degree := by
      rw [← hp', map_add]
      exact Nat.le_add_left _ _
    exact Ideal.mul_mem_left _ _
      (Ideal.pow_le_pow_right (by omega : d - A.degree ≤ d - p.2.degree)
        (hg p.2 (hdeg.trans hA)))


omit [IsRegularLocalRing R] in
theorem span_mul_le_of_forall {I J K : Ideal R} {G : Set R} (hI : I = Ideal.span G)
    (h : ∀ g ∈ G, ∀ s ∈ J, g * s ∈ K) : I * J ≤ K := by
  rw [Ideal.mul_le]
  intro r hr s hs
  subst hI
  induction hr using Submodule.span_induction with
  | mem g hg => exact h g hg s hs
  | zero => simp
  | add x y _ _ hx hy => rw [add_mul]; exact add_mem hx hy
  | smul c x _ hx => rw [smul_eq_mul, mul_assoc]; exact K.mul_mem_left c hx

/-- `M · 𝒬_d ⊆ 𝒬_{d+1}`: multiplication by a `z_j` or by an element of `N` shifts the
coefficients. -/
theorem maximalIdeal_mul_coeffPowIdeal_le {e : R →+* MvPowerSeries (Fin F.r) F.S}
    (he : F.IsExpansion e) (d : ℕ) :
    maximalIdeal R * F.coeffPowIdeal e d ≤ F.coeffPowIdeal e (d + 1) := by
  rw [F.maximalIdeal_eq_idealZ_sup_map, Ideal.sup_mul]
  refine sup_le (span_mul_le_of_forall (G := Set.range F.z) rfl ?_)
    (span_mul_le_of_forall (G := algebraMap F.S R '' (maximalIdeal F.S : Set F.S))
      rfl ?_)
  · rintro _ ⟨j, rfl⟩ s hs A hA
    rw [map_mul, he.map_z]
    have hX : (MvPowerSeries.X j : MvPowerSeries (Fin F.r) F.S) =
        MvPowerSeries.monomial (Finsupp.single j 1) 1 := rfl
    rw [hX, MvPowerSeries.coeff_monomial_mul]
    split_ifs with hle
    · rw [one_mul]
      have hdeg : (A - Finsupp.single j 1).degree + 1 = A.degree := by
        have := congrArg Finsupp.degree (tsub_add_cancel_of_le hle)
        rwa [map_add, Finsupp.degree_single] at this
      have := hs (A - Finsupp.single j 1) (by omega)
      rw [show d + 1 - A.degree = d - (A - Finsupp.single j 1).degree by omega]
      exact this
    · exact zero_mem _
  · rintro _ ⟨n, hn, rfl⟩ s hs A hA
    rw [map_mul, he.map_algebraMap, MvPowerSeries.coeff_C_mul]
    by_cases hAd : A.degree ≤ d
    · have := hs A hAd
      rw [show d + 1 - A.degree = (d - A.degree) + 1 by omega, pow_succ']
      exact Ideal.mul_mem_mul hn this
    · rw [show d + 1 - A.degree = 0 by omega, pow_zero, Ideal.one_eq_top]
      trivial


theorem maximalIdeal_pow_le_coeffPowIdeal {e : R →+* MvPowerSeries (Fin F.r) F.S}
    (he : F.IsExpansion e) (d : ℕ) : maximalIdeal R ^ d ≤ F.coeffPowIdeal e d := by
  induction d with
  | zero =>
    intro g _ A _
    rw [Nat.zero_sub, pow_zero, Ideal.one_eq_top]
    trivial
  | succ d ih =>
    rw [pow_succ']
    exact (Ideal.mul_mono_right ih).trans (F.maximalIdeal_mul_coeffPowIdeal_le he d)

/-- Every `x ∈ R` is, modulo `Pⁿ`, a polynomial in `z₁, …, z_r` with coefficients in `S`. -/
theorem exists_aeval_sub_mem_idealZ_pow (n : ℕ) (g : R) :
    ∃ G : MvPolynomial (Fin F.r) F.S, g - MvPolynomial.aeval F.z G ∈ F.idealZ ^ n := by
  induction n with
  | zero => exact ⟨0, by simp⟩
  | succ n ih =>
    obtain ⟨G, hG⟩ := ih
    obtain ⟨p, -, hp⟩ := F.exists_isHomogeneous_sub_mem_pow n _ hG
    refine ⟨G + p, ?_⟩
    have : g - MvPolynomial.aeval F.z (G + p) =
        g - MvPolynomial.aeval F.z G - MvPolynomial.aeval F.z p := by
      rw [map_add]; ring
    rw [this, sub_sub] at *
    simpa [sub_sub, add_comm] using hp

omit [IsRegularLocalRing R] in
theorem prod_mem_pow_of_forall {ι : Type*} (I : Ideal R) (s : Finset ι) (a : ι → R) (n : ι → ℕ)
    (h : ∀ i ∈ s, a i ∈ I ^ n i) : ∏ i ∈ s, a i ∈ I ^ ∑ i ∈ s, n i := by
  have := Ideal.prod_mem_prod (s := s) (I := fun i => I ^ n i) h
  rwa [Finset.prod_pow_eq_pow_sum] at this

/-- `p(z) ∈ Mᵈ` when the coefficient `c_A` of every monomial `z^A` of degree `≤ d` lies in
`N^{d - |A|}`. -/
theorem aeval_mem_maximalIdeal_pow (d : ℕ) (G : MvPolynomial (Fin F.r) F.S)
    (hG : ∀ A : Fin F.r →₀ ℕ, A.degree ≤ d → G.coeff A ∈ maximalIdeal F.S ^ (d - A.degree)) :
    MvPolynomial.aeval F.z G ∈ maximalIdeal R ^ d := by
  classical
  have hzM : ∀ i, F.z i ∈ maximalIdeal R := fun i =>
    F.maximalIdeal_eq_idealZ_sup_map ▸ Ideal.mem_sup_left (Ideal.subset_span ⟨i, rfl⟩)
  rw [G.as_sum, map_sum]
  refine Ideal.sum_mem _ fun A _ => ?_
  rw [MvPolynomial.aeval_monomial]
  have hprod : ∏ i ∈ A.support, F.z i ^ A i ∈ maximalIdeal R ^ A.degree := by
    have := prod_mem_pow_of_forall (maximalIdeal R) A.support (fun i => F.z i ^ A i) (fun i => A i)
      (fun i _ => Ideal.pow_mem_pow (hzM i) _)
    rwa [← Finsupp.degree_apply] at this
  show algebraMap F.S R (G.coeff A) * (A.prod fun i k => F.z i ^ k) ∈ _
  rw [Finsupp.prod]
  by_cases hA : A.degree ≤ d
  · have h1 : algebraMap F.S R (G.coeff A) ∈ maximalIdeal R ^ (d - A.degree) := by
      have := Ideal.mem_map_of_mem (algebraMap F.S R) (hG A hA)
      rw [Ideal.map_pow] at this
      exact Ideal.pow_right_mono (map_maximalIdeal_le _) _ this
    have := Ideal.mul_mem_mul h1 hprod
    rwa [← pow_add, Nat.sub_add_cancel hA] at this
  · exact Ideal.mul_mem_left _ _ (Ideal.pow_le_pow_right (by omega) hprod)

theorem coeffPowIdeal_le_maximalIdeal_pow {e : R →+* MvPowerSeries (Fin F.r) F.S}
    (he : F.IsExpansion e) (d : ℕ) : F.coeffPowIdeal e d ≤ maximalIdeal R ^ d := by
  intro g hg
  obtain ⟨G, hG⟩ := F.exists_aeval_sub_mem_idealZ_pow (d + 1) g
  have hcoeff : ∀ A : Fin F.r →₀ ℕ, A.degree ≤ d →
      G.coeff A = MvPowerSeries.coeff A (e g) := by
    intro A hA
    have h1 := he.map_pow (d + 1) _ hG
    have h2 : MvPowerSeries.coeff A (e (g - MvPolynomial.aeval F.z G)) = 0 :=
      MvPowerSeries.coeff_of_lt_order ((show ((A.degree : ℕ) : ℕ∞) < ((d + 1 : ℕ) : ℕ∞) by
        exact_mod_cast (show A.degree < d + 1 by omega)).trans_le
          (MvPowerSeries.le_order_of_mem_pow_span_range_X _ h1))
    rw [map_sub, he.map_aeval, map_sub, MvPolynomial.coeff_coe, sub_eq_zero] at h2
    exact h2.symm
  have hP : F.idealZ ≤ maximalIdeal R := by
    rw [F.maximalIdeal_eq_idealZ_sup_map]
    exact le_sup_left
  have h3 : g - MvPolynomial.aeval F.z G ∈ maximalIdeal R ^ d :=
    Ideal.pow_le_pow_right (Nat.le_succ d) (Ideal.pow_right_mono hP _ hG)
  have h4 : MvPolynomial.aeval F.z G ∈ maximalIdeal R ^ d :=
    F.aeval_mem_maximalIdeal_pow d G fun A hA => by
      rw [hcoeff A hA]
      exact hg A hA
  have := add_mem h3 h4
  rwa [sub_add_cancel] at this

/-- **The order in a regular frame** (p. 270: "`g = Σ h_A z^A` with `h_A ∈ S`"): `g ∈ Mᵈ` iff
`c_A(g) ∈ N^{d - |A|}` for all `A` with `|A| ≤ d`, i.e. `ν_M(g) = min_A(|A| + ν_N(c_A))`. -/
theorem mem_maximalIdeal_pow_iff_coeff_mem_pow {e : R →+* MvPowerSeries (Fin F.r) F.S}
    (he : F.IsExpansion e) (d : ℕ) (g : R) :
    g ∈ maximalIdeal R ^ d ↔ ∀ A : Fin F.r →₀ ℕ, A.degree ≤ d →
      MvPowerSeries.coeff A (e g) ∈ maximalIdeal F.S ^ (d - A.degree) :=
  ⟨fun h => F.maximalIdeal_pow_le_coeffPowIdeal he d h,
    fun h => F.coeffPowIdeal_le_maximalIdeal_pow he d h⟩


omit [IsRegularLocalRing R] in
/-- A product of classes: `∏ [a_i Xⁿⁱ] = [∏ a_i X^{Σ nᵢ}]`. -/
theorem prod_mk_eq {ι : Type*} (I : Ideal R) (s : Finset ι) (n : ι → ℕ) (a : ι → R)
    (ha : ∀ i, a i ∈ I ^ n i) (hp : ∏ i ∈ s, a i ∈ I ^ ∑ i ∈ s, n i) :
    ∏ i ∈ s, AssocGraded.mk I (n i) (a i) (ha i) =
      AssocGraded.mk I (∑ i ∈ s, n i) (∏ i ∈ s, a i) hp := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.prod_empty, Finset.sum_empty]
    rfl
  | insert j s hj ih =>
    have hp' : ∏ i ∈ s, a i ∈ I ^ ∑ i ∈ s, n i := by
      have := Ideal.prod_mem_prod (s := s) (I := fun i => I ^ n i) (fun i _ => ha i)
      rwa [Finset.prod_pow_eq_pow_sum] at this
    rw [Finset.prod_insert hj, ih hp', AssocGraded.mk_mul_mk]
    refine mk_congr_of_eq I (by rw [Finset.sum_insert hj]) (by rw [Finset.prod_insert hj]) _ _

/-- The class in `gr^k_M(R)` of the image of `c ∈ N^k` (`N` the maximal ideal of `S`), and `0` if
`c ∉ N^k`: the map `gr^k_N(S) → gr^k_M(R)` induced by the local homomorphism `S → R`, on
representatives. -/
noncomputable def grMap (k : ℕ) (c : F.S) : AssocGraded (maximalIdeal R) :=
  open Classical in
  if h : c ∈ maximalIdeal F.S ^ k then
    AssocGraded.mk (maximalIdeal R) k (algebraMap F.S R c) (by
      have := Ideal.mem_map_of_mem (algebraMap F.S R) h
      rw [Ideal.map_pow] at this
      exact Ideal.pow_right_mono (map_maximalIdeal_le _) _ this)
  else 0

/-- `Z_j`, the initial form of `z_j` in `gr_M(R)` is the class of `z_j` in `M/M²` (`z_j ∉ M²`). -/
theorem frameForm_eq_mk_one (j : Fin F.r) (h : F.z j ∈ maximalIdeal R ^ 1) :
    frameForm F.z j = AssocGraded.mk (maximalIdeal R) 1 (F.z j) h := by
  obtain ⟨-, hord⟩ := linearIndependent_frameForm F.z_injective F.extends_rsop
  exact initialForm_eq_mk _ (hord j)


omit [IsRegularLocalRing R] in
/-- `[a X]ⁿ = [aⁿ Xⁿ]`. -/
theorem mk_one_pow (I : Ideal R) (a : R) (ha : a ∈ I ^ 1) (n : ℕ) :
    AssocGraded.mk I 1 a ha ^ n =
      AssocGraded.mk I n (a ^ n) (Ideal.pow_mem_pow (by simpa using ha) n) := by
  induction n with
  | zero =>
    rw [pow_zero]
    have : (1 : AssocGraded I) = AssocGraded.mk I 0 1 (by simp) := by
      rw [AssocGraded.mk_zero_eq_algebraMap, map_one, map_one]
    exact this.trans (mk_congr_of_eq I rfl (pow_zero a).symm _ _)
  | succ n ih =>
    rw [pow_succ, ih, AssocGraded.mk_mul_mk]
    exact mk_congr_of_eq I (by omega) (by rw [pow_succ]) _ _

/-- **The initial form in a regular frame** (p. 270: "Let `φ_A` be the initial form of `h_A` in
`gr_M(R)` only for those `A` with `|A| + ν_M(h_A) = ν`. Then `φ = Σ_A φ_A Z^A`"): for `g ∈ Mᵈ`
with expansion `Σ c_A z^A`, the class of `g` in `grᵈ_M(R)` is `Σ_{|A| ≤ d} [c_A]_{d-|A|} Z^A`, where
`[c]_k` is the class of `c ∈ N^k` in `gr^k_N(S) → gr^k_M(R)` (zero if `c ∈ N^{k+1}`). -/
theorem mk_eq_sum_grMap_mul {e : R →+* MvPowerSeries (Fin F.r) F.S} (he : F.IsExpansion e)
    {d : ℕ} {g : R} (hg : g ∈ maximalIdeal R ^ d) :
    AssocGraded.mk (maximalIdeal R) d g hg =
      ∑ A ∈ (Finsupp.finite_of_degree_le (σ := Fin F.r) d).toFinset,
        F.grMap (d - A.degree) (MvPowerSeries.coeff A (e g)) * ∏ i, frameForm F.z i ^ A i := by
  classical
  set Sd := (Finsupp.finite_of_degree_le (σ := Fin F.r) d).toFinset with hSd
  have hmemSd : ∀ A, A ∈ Sd ↔ A.degree ≤ d := fun A => by simp [hSd]
  have hc : ∀ A : Fin F.r →₀ ℕ, A.degree ≤ d →
      MvPowerSeries.coeff A (e g) ∈ maximalIdeal F.S ^ (d - A.degree) :=
    (F.mem_maximalIdeal_pow_iff_coeff_mem_pow he d g).mp hg
  set H : MvPolynomial (Fin F.r) F.S :=
    ∑ A ∈ Sd, MvPolynomial.monomial A (MvPowerSeries.coeff A (e g)) with hHdef
  have hHcoeff : ∀ A, H.coeff A = if A.degree ≤ d then MvPowerSeries.coeff A (e g) else 0 := by
    intro A
    rw [hHdef, MvPolynomial.coeff_sum]
    simp only [MvPolynomial.coeff_monomial]
    by_cases hA : A ∈ Sd
    · rw [Finset.sum_eq_single_of_mem A hA (fun B _ hB => by simp [hB])]
      simp [(hmemSd A).mp hA]
    · have hAd : ¬ A.degree ≤ d := fun h => hA ((hmemSd A).mpr h)
      rw [Finset.sum_eq_zero (fun B hB => by
        have : B ≠ A := fun h => hA (h ▸ hB)
        simp [this])]
      simp [hAd]
  have hH : MvPolynomial.aeval F.z H ∈ maximalIdeal R ^ d :=
    F.aeval_mem_maximalIdeal_pow d H fun A hA => by
      rw [hHcoeff]
      simp only [hA, ↓reduceIte]
      exact hc A hA
  have hdiff : g - MvPolynomial.aeval F.z H ∈ maximalIdeal R ^ (d + 1) := by
    rw [F.mem_maximalIdeal_pow_iff_coeff_mem_pow he]
    intro A hA
    rw [map_sub, he.map_aeval, map_sub, MvPolynomial.coeff_coe, hHcoeff]
    by_cases hAd : A.degree ≤ d
    · simp only [hAd, ↓reduceIte, sub_self]
      exact zero_mem _
    · rw [show d + 1 - A.degree = 0 by omega, pow_zero, Ideal.one_eq_top]
      trivial
  rw [AssocGraded.mk_eq_mk_of_sub_mem_pow_succ _ d hg hH hdiff]
  -- `aeval z H = Σ_A c_A z^A`
  have haeval : MvPolynomial.aeval F.z H =
      ∑ A ∈ Sd, algebraMap F.S R (MvPowerSeries.coeff A (e g)) * ∏ i, F.z i ^ A i := by
    rw [hHdef, map_sum]
    refine Finset.sum_congr rfl fun A _ => ?_
    rw [MvPolynomial.aeval_monomial, Finsupp.prod_fintype _ _ (fun i => pow_zero _)]
  have hzM : ∀ i, F.z i ∈ maximalIdeal R ^ 1 := fun i => by
    rw [pow_one, F.maximalIdeal_eq_idealZ_sup_map]
    exact Ideal.mem_sup_left (Ideal.subset_span ⟨i, rfl⟩)
  -- the terms
  have hterm : ∀ A : Sd, algebraMap F.S R (MvPowerSeries.coeff (A : Fin F.r →₀ ℕ) (e g)) *
      ∏ i, F.z i ^ (A : Fin F.r →₀ ℕ) i ∈ maximalIdeal R ^ d := by
    intro A
    have hAd := (hmemSd A).mp A.2
    have h1 : algebraMap F.S R (MvPowerSeries.coeff (A : Fin F.r →₀ ℕ) (e g)) ∈
        maximalIdeal R ^ (d - (A : Fin F.r →₀ ℕ).degree) := by
      have := Ideal.mem_map_of_mem (algebraMap F.S R) (hc A hAd)
      rw [Ideal.map_pow] at this
      exact Ideal.pow_right_mono (map_maximalIdeal_le _) _ this
    have h2 : ∏ i, F.z i ^ (A : Fin F.r →₀ ℕ) i ∈ maximalIdeal R ^ (A : Fin F.r →₀ ℕ).degree := by
      have := prod_mem_pow_of_forall (maximalIdeal R) Finset.univ
        (fun i => F.z i ^ (A : Fin F.r →₀ ℕ) i) (fun i => (A : Fin F.r →₀ ℕ) i)
        (fun i _ => Ideal.pow_mem_pow (by simpa using hzM i) _)
      rwa [← Finsupp.degree_eq_sum] at this
    have := Ideal.mul_mem_mul h1 h2
    rwa [← pow_add, Nat.sub_add_cancel hAd] at this
  have hsum : ∑ A ∈ Sd, algebraMap F.S R (MvPowerSeries.coeff A (e g)) * ∏ i, F.z i ^ A i =
      ∑ A : Sd, algebraMap F.S R (MvPowerSeries.coeff (A : Fin F.r →₀ ℕ) (e g)) *
        ∏ i, F.z i ^ (A : Fin F.r →₀ ℕ) i :=
    (Finset.sum_coe_sort Sd (fun A => algebraMap F.S R (MvPowerSeries.coeff A (e g)) *
      ∏ i, F.z i ^ A i)).symm
  rw [AssocGraded.mk_congr _ hH haeval, AssocGraded.mk_congr _ (haeval ▸ hH) hsum,
    AssocGraded.mk_sum _ d Finset.univ _ hterm]
  rw [← Finset.sum_coe_sort Sd (fun A => F.grMap (d - A.degree) (MvPowerSeries.coeff A (e g)) *
    ∏ i, frameForm F.z i ^ A i)]
  refine Finset.sum_congr rfl fun A _ => ?_
  have hAd := (hmemSd A).mp A.2
  have h2 : ∏ i, F.z i ^ (A : Fin F.r →₀ ℕ) i ∈ maximalIdeal R ^ (A : Fin F.r →₀ ℕ).degree := by
    have := prod_mem_pow_of_forall (maximalIdeal R) Finset.univ
      (fun i => F.z i ^ (A : Fin F.r →₀ ℕ) i) (fun i => (A : Fin F.r →₀ ℕ) i)
      (fun i _ => Ideal.pow_mem_pow (by simpa using hzM i) _)
    rwa [← Finsupp.degree_eq_sum] at this
  have hprodF : ∏ i, frameForm F.z i ^ (A : Fin F.r →₀ ℕ) i =
      AssocGraded.mk (maximalIdeal R) (A : Fin F.r →₀ ℕ).degree
        (∏ i, F.z i ^ (A : Fin F.r →₀ ℕ) i) h2 := by
    rw [Finset.prod_congr rfl (fun i _ => by
      rw [F.frameForm_eq_mk_one i (hzM i), mk_one_pow])]
    rw [prod_mk_eq (maximalIdeal R) Finset.univ (fun i => (A : Fin F.r →₀ ℕ) i)
      (fun i => F.z i ^ (A : Fin F.r →₀ ℕ) i)
      (fun i => Ideal.pow_mem_pow (by simpa using hzM i) _)
      (by rw [← Finsupp.degree_eq_sum]; exact h2)]
    exact mk_congr_of_eq _ (by rw [Finsupp.degree_eq_sum]) rfl _ _
  have hgm : F.grMap (d - (A : Fin F.r →₀ ℕ).degree)
      (MvPowerSeries.coeff (A : Fin F.r →₀ ℕ) (e g)) =
      AssocGraded.mk (maximalIdeal R) (d - (A : Fin F.r →₀ ℕ).degree)
        (algebraMap F.S R (MvPowerSeries.coeff (A : Fin F.r →₀ ℕ) (e g))) (by
          have := Ideal.mem_map_of_mem (algebraMap F.S R) (hc A hAd)
          rw [Ideal.map_pow] at this
          exact Ideal.pow_right_mono (map_maximalIdeal_le _) _ this) := by
    simp only [grMap, hc A hAd, ↓reduceDIte]
  rw [hprodF, hgm, AssocGraded.mk_mul_mk]
  exact mk_congr_of_eq (maximalIdeal R) (Nat.sub_add_cancel hAd).symm rfl _ _

end Coeff

end RegularFrame

end Hironaka
