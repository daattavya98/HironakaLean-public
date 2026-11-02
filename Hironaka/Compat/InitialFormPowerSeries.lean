/-
Copyright (c) 2026 Daattavya Aggarwal, Minhyong Kim, Oisin Kim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daattavya Aggarwal, Minhyong Kim, Oisin Kim
-/
module

public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
public import Mathlib.RingTheory.MvPowerSeries.Rename
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Hironaka.Compat.FrameGraded
public import Hironaka.Compat.WeierstrassCoordinates

/-!
# Initial forms through an isomorphism with a formal power series ring

For a regular local ring `R` with an isomorphism `Φ : R ≃ k⟦X₁, …, X_N⟧` sending a regular system of
parameters `v` to the variables, the coefficient field `σ(k)` to the constants, and preserving the
order, the class of `a ∈ Mⁿ` in `grⁿ_M(R)` is the value, at the classes `[v_i]`, of the
homogeneous component of degree `n` of `Φ(a)` (`mk_eq_aeval_homogPart`).  This is the identification
"the graded `k`-algebra `gr_M(R)` can be identified with the polynomial ring
`k[Z₁, …, Z_r, X₁, …, X_s]`" of the proof of Lemma 25 (p. 269--270).
-/

@[expose] public section

open IsLocalRing MvPowerSeries

namespace Hironaka

universe u

section HomogPart

variable {N : ℕ} {K : Type*} [CommRing K]

/-- The homogeneous component of degree `ν` of a power series, as a polynomial. -/
noncomputable def homogPart (ν : ℕ) (g : MvPowerSeries (Fin N) K) : MvPolynomial (Fin N) K :=
  MvPowerSeries.truncTotal (ν + 1) (MvPowerSeries.homogeneousComponent ν g)

theorem coeff_homogPart (ν : ℕ) (g : MvPowerSeries (Fin N) K) (d : Fin N →₀ ℕ) :
    (homogPart ν g).coeff d = if d.degree = ν then MvPowerSeries.coeff d g else 0 := by
  rw [homogPart, MvPowerSeries.coeff_truncTotal_eq_ite, MvPowerSeries.coeff_homogeneousComponent]
  by_cases h : d.degree = ν
  · simp [h]
  · by_cases h' : d.degree < ν + 1
    · simp [h, h']
    · simp [h, h']

theorem isHomogeneous_homogPart (ν : ℕ) (g : MvPowerSeries (Fin N) K) :
    (homogPart ν g).IsHomogeneous ν := by
  intro d hd
  rw [coeff_homogPart] at hd
  split_ifs at hd with h
  · show Finsupp.weight (fun _ => 1) d = ν
    rw [← Finsupp.degree_eq_weight_one]
    exact h
  · exact absurd rfl hd

theorem succ_le_order_sub_homogPart (ν : ℕ) {g : MvPowerSeries (Fin N) K}
    (hg : (ν : ℕ∞) ≤ g.order) :
    ((ν + 1 : ℕ) : ℕ∞) ≤ (g - (homogPart ν g : MvPowerSeries (Fin N) K)).order := by
  apply MvPowerSeries.le_order
  intro d hd
  rw [map_sub, MvPolynomial.coeff_coe, coeff_homogPart]
  have hd' : d.degree < ν + 1 := by exact_mod_cast hd
  by_cases h : d.degree = ν
  · simp [h]
  · simp only [h, ite_false, sub_zero]
    exact MvPowerSeries.coeff_of_lt_order (lt_of_lt_of_le (by exact_mod_cast (by omega :
      d.degree < ν)) hg)

end HomogPart

section GradedLift

variable {R : Type u} [CommRing R] [IsRegularLocalRing R] {N : ℕ}

/-- The class of `σ(c) · ∏ v_i^{d_i}` in `grⁿ_M(R)` for `|d| = n`. -/
theorem mk_mul_prod_pow_eq (v : Fin N → R) (hv : ∀ i, v i ∈ maximalIdeal R ^ 1)
    (c : R) (d : Fin N →₀ ℕ) {n : ℕ} (hd : d.degree = n) :
    ∃ h : c * d.prod (fun i e => v i ^ e) ∈ maximalIdeal R ^ n,
      AssocGraded.mk (maximalIdeal R) n _ h = Ideal.Quotient.mk (maximalIdeal R) c •
        d.prod (fun i e => AssocGraded.mk (maximalIdeal R) 1 (v i) (hv i) ^ e) := by
  classical
  have hpow : ∀ i, v i ^ (d i) ∈ maximalIdeal R ^ (d i) := fun i =>
    Ideal.pow_mem_pow (by simpa using hv i) _
  have hprod : ∏ i ∈ d.support, v i ^ (d i) ∈ maximalIdeal R ^ n := by
    have := Ideal.prod_mem_prod (s := d.support) (I := fun i => maximalIdeal R ^ (d i))
      (fun i _ => hpow i)
    rw [Finset.prod_pow_eq_pow_sum] at this
    rwa [show ∑ i ∈ d.support, d i = n from hd] at this
  have hmem : c * d.prod (fun i e => v i ^ e) ∈ maximalIdeal R ^ n :=
    Ideal.mul_mem_left _ _ hprod
  refine ⟨hmem, ?_⟩
  show AssocGraded.mk (maximalIdeal R) n (c * ∏ i ∈ d.support, v i ^ (d i)) _ =
    Ideal.Quotient.mk (maximalIdeal R) c •
      ∏ i ∈ d.support, AssocGraded.mk (maximalIdeal R) 1 (v i) (hv i) ^ (d i)
  rw [← AssocGraded.smul_mk (maximalIdeal R) n c _ hprod]
  congr 1
  have hp : ∏ i ∈ d.support, v i ^ (d i) ∈ maximalIdeal R ^ ∑ i ∈ d.support, d i := by
    rwa [show ∑ i ∈ d.support, d i = n from hd]
  have h1 := RegularFrame.prod_mk_eq (maximalIdeal R) d.support (fun i => d i)
    (fun i => v i ^ (d i)) hpow hp
  rw [show (AssocGraded.mk (maximalIdeal R) n _ hprod) =
      AssocGraded.mk (maximalIdeal R) (∑ i ∈ d.support, d i) (∏ i ∈ d.support, v i ^ (d i)) hp from
    mk_congr_of_eq _ hd.symm rfl _ _, ← h1]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [RegularFrame.mk_one_pow]

end GradedLift

section InitialForm

variable {R : Type u} [CommRing R] [IsRegularLocalRing R] {N : ℕ}

omit [IsRegularLocalRing R] in
theorem mk_finset_sum_eq (I : Ideal R) (n : ℕ) {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (a : ι → R) (t : ι → AssocGraded I) (ha : ∀ i ∈ s, a i ∈ I ^ n)
    (ht : ∀ i (hi : i ∈ s), AssocGraded.mk I n (a i) (ha i hi) = t i) :
    ∃ h : ∑ i ∈ s, a i ∈ I ^ n, AssocGraded.mk I n (∑ i ∈ s, a i) h = ∑ i ∈ s, t i := by
  induction s using Finset.induction_on with
  | empty =>
    refine ⟨by simp, ?_⟩
    simp only [Finset.sum_empty]
    exact map_zero (AssocGraded.mkLinear I n)
  | insert j s hj ih =>
    obtain ⟨h1, h2⟩ := ih (fun i hi => ha i (Finset.mem_insert_of_mem hi))
      (fun i hi => ht i (Finset.mem_insert_of_mem hi))
    have hjm : a j ∈ I ^ n := ha j (Finset.mem_insert_self _ _)
    refine ⟨by rw [Finset.sum_insert hj]; exact add_mem hjm h1, ?_⟩
    simp only [Finset.sum_insert hj]
    rw [AssocGraded.mk_add I n _ _ hjm h1, h2, ht j (Finset.mem_insert_self _ _)]

open Classical in
/-- **The initial form through a Cohen isomorphism**: let `Φ : R ≃ K{X₁, …, X_N}` map the system
`v` to the variables and the coefficient field `σ(K)` to the constants, preserving the order. For
`a ∈ Mⁿ`, the class of `a` in `grⁿ_M(R)` is the value, at the classes `[v_i]`, of the homogeneous
component of degree `n` of `Φ(a)`. -/
theorem mk_eq_aeval_homogPart (v : Fin N → R) (hv : ∀ i, v i ∈ maximalIdeal R ^ 1)
    (σ : R ⧸ maximalIdeal R →+* R)
    (hσ : (Ideal.Quotient.mk (maximalIdeal R)).comp σ = RingHom.id _)
    (Φ : R ≃+* MvPowerSeries (Fin N) (R ⧸ maximalIdeal R))
    (hΦv : ∀ i, Φ (v i) = MvPowerSeries.X i) (hΦσ : ∀ c, Φ (σ c) = MvPowerSeries.C c)
    (hΦo : ∀ a, (Φ a).order = Ideal.ordElem (maximalIdeal R) a)
    {n : ℕ} {a : R} (ha : a ∈ maximalIdeal R ^ n) :
    AssocGraded.mk (maximalIdeal R) n a ha = MvPolynomial.aeval (R := R ⧸ maximalIdeal R)
      (fun i => AssocGraded.mk (maximalIdeal R) 1 (v i) (hv i)) (homogPart n (Φ a)) := by
  set P := homogPart n (Φ a) with hP
  have hPhom := isHomogeneous_homogPart n (Φ a)
  have hdeg : ∀ d ∈ P.support, d.degree = n := fun d hd => by
    have := hPhom (MvPolynomial.mem_support_iff.mp hd)
    rwa [Finsupp.degree_eq_weight_one]
  set q : R := ∑ d ∈ P.support, σ (P.coeff d) * d.prod (fun i e => v i ^ e) with hq
  -- `Φ q = P`
  have hΦq : Φ q = (P : MvPowerSeries (Fin N) (R ⧸ maximalIdeal R)) := by
    have hmono : ∀ (d : Fin N →₀ ℕ) (c : R ⧸ maximalIdeal R),
        ((MvPolynomial.monomial d c : MvPolynomial (Fin N) (R ⧸ maximalIdeal R)) :
          MvPowerSeries (Fin N) (R ⧸ maximalIdeal R)) =
          MvPowerSeries.C c * d.prod (fun i e => (MvPowerSeries.X i) ^ e) := by
      intro d c
      have := map_prod (MvPolynomial.coeToMvPowerSeries.ringHom (σ := Fin N)
        (R := R ⧸ maximalIdeal R))
        (fun i => (MvPolynomial.X i : MvPolynomial (Fin N) (R ⧸ maximalIdeal R)) ^ d i) d.support
      simp only [MvPolynomial.coeToMvPowerSeries.ringHom_apply, MvPolynomial.coe_pow,
        MvPolynomial.coe_X] at this
      rw [MvPolynomial.monomial_eq, MvPolynomial.coe_mul, MvPolynomial.coe_C]
      simp only [Finsupp.prod]
      rw [this]
    have hPsum : (P : MvPowerSeries (Fin N) (R ⧸ maximalIdeal R)) =
        ∑ d ∈ P.support, MvPowerSeries.C (P.coeff d) * d.prod (fun i e => X i ^ e) := by
      have h1 := map_sum (MvPolynomial.coeToMvPowerSeries.ringHom (σ := Fin N)
        (R := R ⧸ maximalIdeal R)) (fun d => MvPolynomial.monomial d (P.coeff d)) P.support
      rw [← P.as_sum] at h1
      simp only [MvPolynomial.coeToMvPowerSeries.ringHom_apply] at h1
      rw [h1]
      exact Finset.sum_congr rfl fun d _ => hmono d _
    rw [hPsum, hq, map_sum]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [map_mul, hΦσ, Finsupp.prod, map_prod]
    simp only [map_pow, hΦv]
    rfl
  -- membership of `q`
  have hterm : ∀ d ∈ P.support, ∃ h : σ (P.coeff d) * d.prod (fun i e => v i ^ e) ∈
      maximalIdeal R ^ n, AssocGraded.mk (maximalIdeal R) n _ h =
        MvPolynomial.aeval (R := R ⧸ maximalIdeal R)
          (fun i => AssocGraded.mk (maximalIdeal R) 1 (v i) (hv i))
          (MvPolynomial.monomial d (P.coeff d)) := by
    intro d hd
    obtain ⟨h, hmk⟩ := mk_mul_prod_pow_eq v hv (σ (P.coeff d)) d (hdeg d hd)
    refine ⟨h, ?_⟩
    rw [hmk, MvPolynomial.aeval_monomial, Algebra.smul_def]
    have : Ideal.Quotient.mk (maximalIdeal R) (σ (P.coeff d)) = P.coeff d :=
      congrArg (fun f => f (P.coeff d)) hσ
    rw [this]
  choose hmem hmk using hterm
  obtain ⟨hqmem, hqmk⟩ := mk_finset_sum_eq (maximalIdeal R) n P.support
    (fun d => σ (P.coeff d) * d.prod (fun i e => v i ^ e))
    (fun d => MvPolynomial.aeval (R := R ⧸ maximalIdeal R)
      (fun i => AssocGraded.mk (maximalIdeal R) 1 (v i) (hv i)) (MvPolynomial.monomial d (P.coeff d)))
    (fun d hd => hmem d hd) (fun d hd => hmk d hd)
  -- the difference
  have hdiff : a - q ∈ maximalIdeal R ^ (n + 1) := by
    refine Ideal.mem_pow_of_le_ordElem ?_
    rw [← hΦo, map_sub, hΦq]
    exact_mod_cast succ_le_order_sub_homogPart n (g := Φ a) (by
      rw [hΦo]; exact Ideal.le_ordElem ha)
  rw [AssocGraded.mk_eq_mk_of_sub_mem_pow_succ (maximalIdeal R) n ha hqmem hdiff, hqmk,
    ← map_sum]
  congr 1
  exact P.as_sum.symm

end InitialForm

section Rename

variable {N M : ℕ} {K : Type*} [CommRing K]

/-- The homogeneous component of a renamed power series is the renamed component. -/
theorem homogPart_rename (e : Fin N → Fin M) (he : Function.Injective e) (k : ℕ)
    (g : MvPowerSeries (Fin N) K) :
    homogPart k (MvPowerSeries.rename e g) = MvPolynomial.rename e (homogPart k g) := by
  classical
  ext d
  rw [coeff_homogPart]
  by_cases hd : d ∈ Set.range (Finsupp.mapDomain e)
  · obtain ⟨u, rfl⟩ := hd
    rw [MvPolynomial.coeff_rename_mapDomain e he, coeff_homogPart, Finsupp.degree_mapDomain]
    have := MvPowerSeries.coeff_embDomain_rename ⟨e, he⟩ g u
    rw [Finsupp.embDomain_eq_mapDomain] at this
    simp only [Function.Embedding.coeFn_mk] at this
    rw [this]
  · rw [MvPolynomial.coeff_rename_eq_zero e _ d (fun u hu => absurd ⟨u, hu⟩ hd)]
    rw [MvPowerSeries.coeff_rename_eq_zero e g hd]
    simp

end Rename

section SpanX

variable {σ : Type*} {K : Type*} [CommRing K]

open Classical in
/-- A homogeneous polynomial of degree one involving only the variables of a set `V` lies in the
span of these variables. -/
theorem mem_span_X_of_isHomogeneous_one {P : MvPolynomial σ K} (hP : P.IsHomogeneous 1)
    (V : Set σ) (hV : ∀ d ∈ P.support, ∀ i ∈ d.support, i ∈ V) :
    P ∈ Submodule.span K (MvPolynomial.X '' V) := by
  classical
  rw [P.as_sum]
  refine Submodule.sum_mem _ fun d hd => ?_
  have hdeg : d.degree = 1 := by
    have := hP (MvPolynomial.mem_support_iff.mp hd)
    rwa [Finsupp.degree_eq_weight_one]
  obtain ⟨i, rfl⟩ := exists_eq_single_one_of_degree_eq_one d hdeg
  have hi : i ∈ V := hV _ hd i (by simp)
  rw [MvPolynomial.monomial_eq, MvPolynomial.C_mul']
  simp only [Finsupp.prod_single_index, pow_one, pow_zero]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, hi, rfl⟩)

end SpanX

end Hironaka
