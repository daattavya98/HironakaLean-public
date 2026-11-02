/-
Copyright (c) 2026 Daattavya Aggarwal, Minhyong Kim, Oisin Kim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daattavya Aggarwal, Minhyong Kim, Oisin Kim
-/
module

public import Mathlib.Algebra.Torsor.Defs
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.RingTheory.ReesAlgebra
public import Architect
public import Hironaka.Compat.Graded
public import Hironaka.Compat.RegularGraded
public import Hironaka.Compat.QuotientPolynomialGraded

/-!
# Compatibility layer: `gr` and localization at a prime (Ch. II, Theorem 3, p. 201)

Theorem 3 (p. 201) passes from `gr_Q(R)` to `gr_{QR_Q}(R_Q)`: "Let `K` denote the field of
quotients of `R''`.  Then we get in a natural way the identification
`gr_Q(R)_Q = gr_{QR_Q}(R_Q) = K[Z₁, …, Z_r, Y₁, …, Y_s]`".  This file provides the two pieces of
infrastructure for that step which are not specific to Theorem 3 (the name `mapLE` is used
because `Hironaka.AssocGraded.map` (the case `I' = I.map f`) is defined later, in Ch. III):

* `AssocGraded.mapLE`: the canonical ring homomorphism `gr_I(A) → gr_{I'}(B)` induced by a ring
  homomorphism `f : A → B` with `f(I) ⊆ I'` (sending the class of `a Xⁿ` to that of `f(a) Xⁿ`);
  the homomorphism `gr_Q(R) → gr_{QR_Q}(R_Q)` of the identification is the case `A → A_Q`.
* `isQuasiRegular_map_localization`: a quasi-regular family generating a prime `Q` stays
  quasi-regular in the localization `R_Q` (so `gr_{QR_Q}(R_Q)` is again a polynomial ring over
  its residue field, by `yzFormHom_bijective`).
* `residueMap`: `R'' = R/Q → K = R_Q/QR_Q`, injective, `K` being the field of quotients of `R''`
  (`exists_residueMap_mul_eq`), with a common denominator in `R - Q` for the coefficients of a
  polynomial over `K` (`exists_map_residueMap_eq_C_mul`).
-/

@[expose] public section

namespace Hironaka

universe u

section Map

open Polynomial

variable {A B : Type*} [CommRing A] [CommRing B] (f : A →+* B) (I : Ideal A) (I' : Ideal B)

/-- The map of Rees algebras `⊕ Iⁿ Xⁿ → ⊕ I'ⁿ Xⁿ` induced by `f : A → B` with `f(I) ⊆ I'`
(coefficientwise application of `f`). -/
noncomputable def reesMapLE (h : I.map f ≤ I') : reesAlgebra I →+* reesAlgebra I' where
  toFun p := ⟨(p : A[X]).map f, (mem_reesAlgebra_iff _ _).mpr fun i => by
    rw [coeff_map]
    exact Ideal.pow_right_mono h i (by
      rw [← Ideal.map_pow]
      exact Ideal.mem_map_of_mem f ((mem_reesAlgebra_iff I _).mp p.2 i))⟩
  map_one' := Subtype.ext (by simp)
  map_mul' x y := Subtype.ext (by simp)
  map_zero' := Subtype.ext (by simp)
  map_add' x y := Subtype.ext (by simp)

theorem reesMapLE_coe (h : I.map f ≤ I') (p : reesAlgebra I) :
    (reesMapLE f I I' h p : B[X]) = (p : A[X]).map f := rfl

/-- The canonical ring homomorphism `gr_I(A) → gr_{I'}(B)` induced by `f : A → B` with
`f(I) ⊆ I'` (the class of `a Xⁿ` goes to that of `f(a) Xⁿ`). -/
noncomputable def AssocGraded.mapLE (h : I.map f ≤ I') : AssocGraded I →+* AssocGraded I' :=
  Ideal.quotientMap (Ideal.map (algebraMap B (reesAlgebra I')) I') (reesMapLE f I I' h)
    (by
      intro x hx
      rw [Ideal.mem_comap, mem_map_algebraMap_reesAlgebra_iff]
      rw [mem_map_algebraMap_reesAlgebra_iff] at hx
      intro n
      rw [reesMapLE_coe, coeff_map]
      refine Ideal.pow_right_mono h (n + 1) ?_
      rw [← Ideal.map_pow]
      exact Ideal.mem_map_of_mem f (hx n))

theorem AssocGraded.mapLE_mk (h : I.map f ≤ I') (n : ℕ) (a : A) (ha : a ∈ I ^ n) :
    AssocGraded.mapLE f I I' h (AssocGraded.mk I n a ha) =
      AssocGraded.mk I' n (f a) (Ideal.pow_right_mono h n (by
        rw [← Ideal.map_pow]; exact Ideal.mem_map_of_mem f ha)) := by
  show Ideal.Quotient.mk _ (reesMapLE f I I' h ⟨monomial n a, reesAlgebra.monomial_mem.mpr ha⟩) =
    Ideal.Quotient.mk _ ⟨monomial n (f a), _⟩
  exact congrArg (Ideal.Quotient.mk _)
    (Subtype.ext (by rw [reesMapLE_coe]; exact Polynomial.map_monomial _))

theorem AssocGraded.mapLE_algebraMap (h : I.map f ≤ I') (a : A) :
    AssocGraded.mapLE f I I' h (algebraMap A (AssocGraded I) a) =
      algebraMap B (AssocGraded I') (f a) := by
  have h1 : algebraMap A (AssocGraded I) a = AssocGraded.mk I 0 a (by simp) := rfl
  have h2 : algebraMap B (AssocGraded I') (f a) = AssocGraded.mk I' 0 (f a) (by simp) := rfl
  rw [h1, h2, AssocGraded.mapLE_mk]

end Map

section QuasiRegularLocalization

open MvPolynomial

variable {R : Type u} [CommRing R]

/-- A quasi-regular family generating a prime ideal `Q` stays quasi-regular in `R_Q`: if
`F ∈ S[X]` is a form of degree `d` with `F(x) ∈ (QS)ᵈ⁺¹`, clear the denominators of `F` by an
element `b ∉ Q` and one of the equation by `u ∉ Q`; the integral form `u b F` then has `(ubF)(x)
∈ Qᵈ⁺¹`, so all its coefficients lie in `Q`, and `Q` is prime. -/
theorem isQuasiRegular_map_localization (Q : Ideal R) [Q.IsPrime] {σ : Type*} (x : σ → R)
    (hqr : IsQuasiRegular x) (hQ : Ideal.span (Set.range x) = Q) (S : Type*) [CommRing S]
    [Algebra R S] [IsLocalization.AtPrime S Q] :
    IsQuasiRegular (fun i => algebraMap R S (x i)) := by
  classical
  intro d F hF hFx m
  have hspan : Ideal.span (Set.range fun i => algebraMap R S (x i)) = Q.map (algebraMap R S) := by
    rw [← hQ, Ideal.map_span, ← Set.range_comp]
    rfl
  rw [hspan]
  rw [hspan, ← Ideal.map_pow] at hFx
  -- clear the denominators of `F`
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples Q.primeCompl F.support
    (fun m => F.coeff m)
  have hb' : ∀ m ∈ F.support, ∃ r : R, algebraMap R S r = (b : R) • F.coeff m :=
    fun m hm => hb m hm
  choose! r hr using hb'
  set F₀ : MvPolynomial σ R := ∑ m ∈ F.support, monomial m (r m) with hF₀
  have hF₀h : F₀.IsHomogeneous d := by
    refine MvPolynomial.IsHomogeneous.sum _ _ _ fun m hm => isHomogeneous_monomial _ ?_
    by_contra h
    exact (mem_support_iff.mp hm) (hF.coeff_eq_zero h)
  have hF₀c : ∀ m, F₀.coeff m = if m ∈ F.support then r m else 0 := by
    intro m
    simp only [hF₀, coeff_sum, coeff_monomial]
    rw [Finset.sum_ite_eq']
  have hmap : MvPolynomial.map (algebraMap R S) F₀ = C (algebraMap R S (b : R)) * F := by
    ext m
    rw [coeff_map, coeff_C_mul, hF₀c]
    by_cases hm : m ∈ F.support
    · simp only [hm, ↓reduceIte]
      rw [hr m hm, Algebra.smul_def]
    · simp only [hm, ↓reduceIte]
      rw [map_zero, MvPolynomial.notMem_support_iff.mp hm, mul_zero]
  have heval : ∀ G : MvPolynomial σ R, algebraMap R S (eval x G) =
      eval (fun i => algebraMap R S (x i)) (MvPolynomial.map (algebraMap R S) G) := by
    intro G
    induction G using MvPolynomial.induction_on <;> simp_all
  have h1 : algebraMap R S (eval x F₀) ∈ (Q ^ (d + 1)).map (algebraMap R S) := by
    rw [heval, hmap, eval_mul, eval_C]
    exact Ideal.mul_mem_left _ _ hFx
  obtain ⟨u, hu0, hu⟩ := (IsLocalization.algebraMap_mem_map_algebraMap_iff Q.primeCompl S _ _).mp h1
  have h2 := hqr d (C (u : R) * F₀) (hF₀h.C_mul _) (by
    rw [eval_mul, eval_C, hQ]
    exact hu) m
  rw [hQ, coeff_C_mul] at h2
  have h3 : F₀.coeff m ∈ Q := (Ideal.IsPrime.mem_or_mem inferInstance h2).resolve_left hu0
  by_cases hm : m ∈ F.support
  · rw [hF₀c] at h3
    simp only [hm, ↓reduceIte] at h3
    obtain ⟨v, hv⟩ := (IsLocalization.map_units S b).exists_right_inv
    have : F.coeff m = v * algebraMap R S (r m) := by
      rw [hr m hm, Algebra.smul_def, ← mul_assoc, mul_comm v, hv, one_mul]
    rw [this]
    exact Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _ h3)
  · rw [MvPolynomial.notMem_support_iff.mp hm]
    exact zero_mem _

end QuasiRegularLocalization

section ResidueField

variable {R : Type u} [CommRing R] (Q : Ideal R) [Q.IsPrime]

/-- The comap of the maximal ideal of `R_Q` to `R` is `Q`. -/
theorem comap_maximalIdeal_localization :
    (IsLocalRing.maximalIdeal (Localization.AtPrime Q)).comap
      (algebraMap R (Localization.AtPrime Q)) = Q :=
  Ideal.ext fun x => IsLocalization.AtPrime.to_map_mem_maximal_iff (Localization.AtPrime Q) Q x

/-- `R/Q → R_Q/QR_Q`: the embedding of `R'' = R/Q` into its field of quotients
`K = R_Q/QR_Q` (Theorem 3, p. 201: "Let `K` denote the field of quotients of `R''`"). -/
noncomputable def residueMap : R ⧸ Q →+*
    Localization.AtPrime Q ⧸ IsLocalRing.maximalIdeal (Localization.AtPrime Q) :=
  Ideal.quotientMap _ (algebraMap R (Localization.AtPrime Q))
    (comap_maximalIdeal_localization Q).ge

theorem residueMap_mk (a : R) :
    residueMap Q (Ideal.Quotient.mk Q a) =
      Ideal.Quotient.mk _ (algebraMap R (Localization.AtPrime Q) a) := rfl

/-- `R'' = R/Q → K = R_Q/QR_Q` is injective. -/
theorem residueMap_injective : Function.Injective (residueMap Q) :=
  Ideal.quotientMap_injective' (comap_maximalIdeal_localization Q).le

/-- Every element of `K = R_Q/QR_Q` is a fraction of elements of `R'' = R/Q`: `K` is the field of
quotients of `R''`. -/
theorem exists_residueMap_mul_eq (x : Localization.AtPrime Q ⧸
    IsLocalRing.maximalIdeal (Localization.AtPrime Q)) :
    ∃ (t a : R), t ∉ Q ∧ residueMap Q (Ideal.Quotient.mk Q t) * x =
      residueMap Q (Ideal.Quotient.mk Q a) := by
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨⟨a, t⟩, h⟩ := IsLocalization.surj Q.primeCompl x
  refine ⟨t, a, t.2, ?_⟩
  rw [residueMap_mk, residueMap_mk, ← map_mul, mul_comm]
  exact congrArg _ h

/-- A polynomial over `K` has a common denominator in `R - Q`: `p · t̄ ∈ R''[X]`. -/
theorem exists_map_residueMap_eq_C_mul {σ : Type*}
    (p : MvPolynomial σ (Localization.AtPrime Q ⧸
      IsLocalRing.maximalIdeal (Localization.AtPrime Q))) :
    ∃ t : R, t ∉ Q ∧ ∃ B : MvPolynomial σ (R ⧸ Q), MvPolynomial.map (residueMap Q) B =
      MvPolynomial.C (residueMap Q (Ideal.Quotient.mk Q t)) * p := by
  classical
  -- common denominator of the coefficients, by clearing denominators in `R_Q`
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples Q.primeCompl p.support
    (fun m => Quotient.out (p.coeff m))
  have hb' : ∀ m ∈ p.support, ∃ a : R, residueMap Q (Ideal.Quotient.mk Q a) =
      residueMap Q (Ideal.Quotient.mk Q (b : R)) * p.coeff m := by
    intro m hm
    obtain ⟨a, ha⟩ := hb m hm
    refine ⟨a, ?_⟩
    rw [residueMap_mk, residueMap_mk, ha, Algebra.smul_def, map_mul, Ideal.Quotient.mk_out]
  choose! a ha using hb'
  refine ⟨b, b.2, ∑ m ∈ p.support, MvPolynomial.monomial m (Ideal.Quotient.mk Q (a m)), ?_⟩
  ext m
  rw [MvPolynomial.coeff_map, MvPolynomial.coeff_C_mul]
  simp only [MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial]
  rw [Finset.sum_ite_eq']
  by_cases hm : m ∈ p.support
  · simp only [hm, ↓reduceIte]
    exact ha m hm
  · simp only [hm, ↓reduceIte]
    rw [map_zero, MvPolynomial.notMem_support_iff.mp hm, mul_zero]

end ResidueField

end Hironaka
