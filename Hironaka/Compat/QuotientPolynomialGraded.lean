/-
Copyright (c) 2026 Daattavya Aggarwal, Minhyong Kim, Oisin Kim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daattavya Aggarwal, Minhyong Kim, Oisin Kim
-/
module

public import Mathlib.Algebra.MvPolynomial.Monad
public import Mathlib.RingTheory.Ideal.Quotient.Defs
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Architect
public import Hironaka.Compat.Graded
public import Hironaka.Compat.RegularGraded

/-!
# Compatibility layer: `gr_Q(R)` as an iterated polynomial ring `((R/Q)[Z])[Y]`

For a quasi-regular generating family `(y, z)` of an ideal `Q` of a commutative ring `R`
(`Hironaka/Compat/RegularGraded.lean`), the associated graded ring `gr_Q(R)` is the polynomial
ring `K[Z, Y]`, `K = R/Q`, with `Z_i`, `Y_j` the classes of `z_i`, `y_j` in `Q/Q²`
(Ch. II, Lemma 7, p. 191: "we can identify `gr_Q(R)` with the polynomial ring
`K[Z, Y] = K[Z₁, …, Z_r, Y₁, …, Y_s]` of `r + s` variables over `K`").  Here the polynomial ring
is written as `((R/Q)[Z])[Y] = MvPolynomial κ (MvPolynomial ι (R ⧸ Q))`, so that the
decomposition `ψ = Σ_α T_α(Y) ξ_α(Z)` of p. 191 (distinct monomials `T_α` in the `Y_j`, forms
`ξ_α` in the `Z_i`) is `MvPolynomial.coeff`.  The index types are arbitrary (the paper's `r`,
`s` are the cardinalities of `ι`, `κ`).

* `zFormHom`, `yzFormHom`: `(R/Q)[Z] → gr_Q(R)` and `((R/Q)[Z])[Y] → gr_Q(R)`;
  `yzFormHom_bijective`: the latter is bijective for a quasi-regular generating family.
* `evYZ`, `redYZ`: evaluation `R[Z][Y] → R` and coefficientwise reduction `R[Z][Y] → K[Z][Y]`.
* `IsBiHomogeneous μ d H`: `H` is a sum of `Y^m A_m(Z)` with `|m| = μ` and `A_m` a form of
  degree `d`; `exists_isBiHomogeneous_evYZ_eq_of_mem_mul_pow`: every element of `(y)^μ (z)^d`
  is the value of such an `H`, whose image in `gr_Q(R)` is the class of the element.
-/

@[expose] public section

open IsLocalRing MvPolynomial

namespace Hironaka

universe u

section PolyGr

variable {R : Type u} [CommRing R] (Q : Ideal R) {κ ι : Type*} (y : κ → R) (z : ι → R)
  (hy : ∀ i, y i ∈ Q ^ 1) (hz : ∀ i, z i ∈ Q ^ 1)

/-- `(R/Q)[Z] → gr_Q(R)`, `Z_i ↦ [z_i]`. -/
noncomputable def zFormHom : MvPolynomial ι (R ⧸ Q) →+* AssocGraded Q :=
  (aeval (R := R ⧸ Q) fun i => AssocGraded.mk Q 1 (z i) (hz i)).toRingHom

/-- `((R/Q)[Z])[Y] → gr_Q(R)`, `Z_i ↦ [z_i]`, `Y_j ↦ [y_j]`. -/
noncomputable def yzFormHom : MvPolynomial κ (MvPolynomial ι (R ⧸ Q)) →+*
    AssocGraded Q :=
  eval₂Hom (zFormHom Q z hz) fun j => AssocGraded.mk Q 1 (y j) (hy j)

/-- `((R/Q)[Z])[Y] → gr_Q(R)` restricted to the constants `C a` is `(R/Q)[Z] → gr_Q(R)`. -/
theorem yzFormHom_C (a : MvPolynomial ι (R ⧸ Q)) :
    yzFormHom Q y z hy hz (C a) = zFormHom Q z hz a := by
  simp [yzFormHom]

/-- `Y_j ↦ [y_j]`. -/
theorem yzFormHom_X (j : κ) :
    yzFormHom Q y z hy hz (X j) = AssocGraded.mk Q 1 (y j) (hy j) := by
  simp [yzFormHom]

private theorem sumRingEquiv_symm_C_eq_rename (a : MvPolynomial ι (R ⧸ Q)) :
    (sumRingEquiv (R ⧸ Q) κ ι).symm (C a) = rename Sum.inr a := by
  have : ((sumRingEquiv (R ⧸ Q) κ ι).symm.toRingHom.comp
      (C : MvPolynomial ι (R ⧸ Q) →+* _)) = (rename Sum.inr : _ →ₐ[R ⧸ Q] _).toRingHom := by
    refine MvPolynomial.ringHom_ext (fun a => ?_) (fun i => ?_)
    · simp [sumRingEquiv_symm_C_C]
    · simp [sumRingEquiv_symm_C_X]
  exact congrArg (fun f => f a) this

/-- `((R/Q)[Z])[Y] → gr_Q(R)` is bijective when `(y, z)` is a quasi-regular generating family. -/
theorem yzFormHom_bijective (hqr : IsQuasiRegular (Sum.elim y z))
    (hI : Ideal.span (Set.range (Sum.elim y z)) = Q) :
    Function.Bijective (yzFormHom Q y z hy hz) := by
  have hx : ∀ i, (Sum.elim y z) i ∈ Q ^ 1 := fun i => by
    rcases i with i | i
    · exact hy i
    · exact hz i
  have hb : Function.Bijective (aeval (R := R ⧸ Q)
      fun i => AssocGraded.mk Q 1 ((Sum.elim y z) i) (hx i)) :=
    ⟨aeval_mk_injective_of_isQuasiRegular Q _ hx hqr hI, aeval_mk_surjective Q _ hx hI⟩
  have heq : yzFormHom Q y z hy hz = (aeval (R := R ⧸ Q)
      fun i => AssocGraded.mk Q 1 ((Sum.elim y z) i) (hx i)).toRingHom.comp
        (sumRingEquiv (R ⧸ Q) κ ι).symm.toRingHom := by
    refine MvPolynomial.ringHom_ext (fun a => ?_) (fun j => ?_)
    · rw [RingHom.comp_apply, yzFormHom_C]
      show _ = (aeval _) ((sumRingEquiv _ _ _).symm (C a))
      rw [sumRingEquiv_symm_C_eq_rename, aeval_rename]
      simp [zFormHom]
      rfl
    · rw [RingHom.comp_apply, yzFormHom_X]
      show _ = (aeval _) ((sumRingEquiv _ _ _).symm (X j))
      rw [sumRingEquiv_symm_X]
      simp
  rw [heq]
  exact hb.comp (sumRingEquiv (R ⧸ Q) κ ι).symm.bijective


/-- Evaluation `((R)[Z])[Y] → R`, `Z_i ↦ z_i`, `Y_j ↦ y_j`. -/
noncomputable def evYZ : MvPolynomial κ (MvPolynomial ι R) →+* R :=
  eval₂Hom (eval z) y

/-- Coefficientwise reduction mod `Q`. -/
noncomputable def redYZ :
    MvPolynomial κ (MvPolynomial ι R) →+*
      MvPolynomial κ (MvPolynomial ι (R ⧸ Q)) :=
  MvPolynomial.map (MvPolynomial.map (Ideal.Quotient.mk Q))

include hz in
/-- The image in `gr_Q(R)` of (the reduction of) a form `A` of degree `d` in `Z` is the class of
`A(z)` in `Qᵈ/Qᵈ⁺¹`. -/
theorem zFormHom_map_of_isHomogeneous {A : MvPolynomial ι R} {d : ℕ}
    (hA : A.IsHomogeneous d) :
    zFormHom Q z hz (A.map (Ideal.Quotient.mk Q)) =
      AssocGraded.mk Q d (eval z A) (eval_mem_pow_of_isHomogeneous Q z hz hA) :=
  aeval_mk_map_of_isHomogeneous Q z hz hA

include hy hz in
/-- `F(y) · A(z) ∈ Q^{μ + d}` for forms `F` of degree `μ` in `Y` and `A` of degree `d` in `Z`. -/
theorem eval_mul_mem_pow_add {F : MvPolynomial κ R} {μ : ℕ}
    (hF : F.IsHomogeneous μ) {A : MvPolynomial ι R} {d : ℕ} (hA : A.IsHomogeneous d) :
    eval y F * eval z A ∈ Q ^ (μ + d) := by
  rw [pow_add]
  exact Ideal.mul_mem_mul (eval_mem_pow_of_isHomogeneous Q y hy hF)
    (eval_mem_pow_of_isHomogeneous Q z hz hA)

include hy hz in
/-- The image in `gr_Q(R)` of `F̄(Y) · Ā(Z)` is the class of `F(y) A(z)` in degree `μ + d`. -/
theorem yzFormHom_redYZ_map_C_mul_C {F : MvPolynomial κ R} {μ : ℕ}
    (hF : F.IsHomogeneous μ) {A : MvPolynomial ι R} {d : ℕ} (hA : A.IsHomogeneous d) :
    yzFormHom Q y z hy hz (redYZ Q
      (MvPolynomial.map (C : R →+* MvPolynomial ι R) F * C A)) =
      AssocGraded.mk Q (μ + d) (eval y F * eval z A) (eval_mul_mem_pow_add Q y z hy hz hF hA) := by
  rw [← AssocGraded.mk_mul_mk Q (eval_mem_pow_of_isHomogeneous Q y hy hF)
    (eval_mem_pow_of_isHomogeneous Q z hz hA), ← zFormHom_map_of_isHomogeneous Q z hz hA]
  simp only [redYZ, map_mul, MvPolynomial.map_C, yzFormHom_C]
  congr 1
  rw [MvPolynomial.map_map, ← aeval_mk_map_of_isHomogeneous Q y hy hF]
  simp only [yzFormHom, aeval_def, eval₂_map]
  rw [MvPolynomial.eval₂Hom_map_hom]
  have : (zFormHom Q z hz).comp ((MvPolynomial.map (Ideal.Quotient.mk Q)).comp C) =
      (algebraMap (R ⧸ Q) (AssocGraded Q)).comp (Ideal.Quotient.mk Q) :=
    RingHom.ext fun a => by simp [zFormHom]
  rw [this]
  rfl


/-- `H` is bihomogeneous of bidegree `(μ, d)`: it is a sum of `Y^m · A_m(Z)` with `|m| = μ` and
`A_m` homogeneous of degree `d`. -/
def IsBiHomogeneous (μ d : ℕ) (H : MvPolynomial κ (MvPolynomial ι R)) : Prop :=
  ∀ m, (H.coeff m).IsHomogeneous d ∧ (H.coeff m ≠ 0 → m.degree = μ)

/-- Bihomogeneous polynomials of the same bidegree are closed under addition. -/
theorem IsBiHomogeneous.add {μ d : ℕ} {H H' : MvPolynomial κ (MvPolynomial ι R)}
    (h : IsBiHomogeneous μ d H) (h' : IsBiHomogeneous μ d H') : IsBiHomogeneous μ d (H + H') := by
  intro m
  refine ⟨by simpa using (h m).1.add (h' m).1, fun hne => ?_⟩
  have hne : H.coeff m + H'.coeff m ≠ 0 := hne
  by_cases h0 : H.coeff m = 0
  · rw [h0, zero_add] at hne
    exact (h' m).2 hne
  · exact (h m).2 h0

include hy hz in
/-- Every element `h₀` of `(y)^μ (z)^d` is the value `H(y, z)` of a bihomogeneous polynomial `H`
of bidegree `(μ, d)` whose reduction has image the class of `h₀` in `gr_Q(R)`. -/
theorem exists_isBiHomogeneous_evYZ_eq_of_mem_mul_pow {μ d : ℕ} {h₀ : R}
    (hh : h₀ ∈ Ideal.span (Set.range y) ^ μ * Ideal.span (Set.range z) ^ d) :
    ∃ H : MvPolynomial κ (MvPolynomial ι R), IsBiHomogeneous μ d H ∧
      evYZ y z H = h₀ ∧ ∃ hQ : h₀ ∈ Q ^ (μ + d),
        yzFormHom Q y z hy hz (redYZ Q H) = AssocGraded.mk Q (μ + d) h₀ hQ := by
  refine Submodule.mul_induction_on hh (fun i hi j hj => ?_) (fun a b ha hb => ?_)
  · obtain ⟨F, hF, rfl⟩ := (Ideal.mem_span_pow_iff_exists_isHomogeneous y i).mp hi
    obtain ⟨A, hA, rfl⟩ := (Ideal.mem_span_pow_iff_exists_isHomogeneous z j).mp hj
    refine ⟨MvPolynomial.map (C : R →+* MvPolynomial ι R) F * C A, ?_, ?_,
      eval_mul_mem_pow_add Q y z hy hz hF hA, yzFormHom_redYZ_map_C_mul_C Q y z hy hz hF hA⟩
    · intro m
      rw [mul_comm, coeff_C_mul, coeff_map]
      refine ⟨?_, fun hne => ?_⟩
      · simpa using hA.mul (isHomogeneous_C ι (F.coeff m))
      · by_contra hdeg
        exact hne (by rw [hF.coeff_eq_zero hdeg]; simp)
    · have hc : (eval z).comp (C : R →+* MvPolynomial ι R) = RingHom.id R :=
        RingHom.ext fun a => eval_C a
      simp [evYZ, hc]
  · obtain ⟨H, hH, hHe, hQ, hHm⟩ := ha
    obtain ⟨H', hH', hHe', hQ', hHm'⟩ := hb
    refine ⟨H + H', hH.add hH', by rw [map_add, hHe, hHe'], add_mem hQ hQ', ?_⟩
    rw [map_add, map_add, hHm, hHm']
    exact (AssocGraded.mk_add Q _ _ _ hQ hQ').symm


end PolyGr

end Hironaka
