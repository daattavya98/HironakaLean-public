/-
Copyright (c) 2026 Daattavya Aggarwal, Minhyong Kim, Oisin Kim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daattavya Aggarwal, Minhyong Kim, Oisin Kim
-/
module

public import Mathlib.RingTheory.Ideal.AssociatedPrime.Localization
public import Mathlib.RingTheory.Ideal.AssociatedPrime.Finiteness
public import Mathlib.RingTheory.Ideal.MinimalPrime.Colon

/-!
# Associated primes of quotient rings

Ring-theoretic facts about associated primes used for Lemma 4 of Ch. III (p. 211): the associated
primes of `B/J` correspond to those of `C/πJ` for a surjection `π : B → C` with `ker π ≤ J`
(Hironaka: "The associated prime ideals of `M'Ã'` correspond to the associated prime ideals of
`m̄'k̃[X₂,…,X_r]` in a one to one fashion by the natural homomorphism of `Ã'` onto
`k̃[X₂,…,X_r]`"), and the minimal primes of an ideal of a noetherian ring are associated primes.
-/

@[expose] public section

namespace Hironaka

theorem annihilator_quotient_eq (R : Type*) [CommRing R] (I : Ideal R) :
    Module.annihilator R (R ⧸ I) = I := by
  ext r
  rw [Module.mem_annihilator]
  constructor
  · intro h
    have := h 1
    simpa [Algebra.smul_def, Ideal.Quotient.algebraMap_eq, Ideal.Quotient.eq_zero_iff_mem] using this
  · intro h x
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [Algebra.smul_def, Ideal.Quotient.algebraMap_eq, ← map_mul, Ideal.Quotient.eq_zero_iff_mem]
    exact I.mul_mem_right _ h

/-- Scalar multiplication on `R/I` by classes of elements of `R`. -/
theorem smul_quotient_mk {R : Type*} [CommRing R] (I : Ideal R) (r b : R) :
    r • (Ideal.Quotient.mk I b : R ⧸ I) = Ideal.Quotient.mk I (r * b) := rfl

/-- The minimal primes of an ideal `I` of a noetherian ring are associated primes of `R/I`. -/
theorem minimalPrimes_subset_associatedPrimes_quotient {R : Type*} [CommRing R]
    [IsNoetherianRing R] (I : Ideal R) : I.minimalPrimes ⊆ associatedPrimes R (R ⧸ I) := by
  have h := Module.associatedPrimes.minimalPrimes_annihilator_subset_associatedPrimes R (R ⧸ I)
  rwa [annihilator_quotient_eq] at h

/-- An associated prime of `R/I` contains `I`. -/
theorem le_of_mem_associatedPrimes_quotient {R : Type*} [CommRing R] {I p : Ideal R}
    (h : p ∈ associatedPrimes R (R ⧸ I)) : I ≤ p := by
  have h1 := IsAssociatedPrime.annihilator_le h
  rwa [Submodule.annihilator_top, annihilator_quotient_eq] at h1

section Surjective

variable {B C : Type*} [CommRing B] [CommRing C] (π : B →+* C) (hπ : Function.Surjective π)
  {J : Ideal B} (hJ : RingHom.ker π ≤ J)

include hπ hJ

theorem mem_colon_quotient_iff_map (b r : B) :
    r ∈ (⊥ : Submodule B (B ⧸ J)).colon {Ideal.Quotient.mk J b} ↔
      π r ∈ (⊥ : Submodule C (C ⧸ J.map π)).colon {Ideal.Quotient.mk (J.map π) (π b)} := by
  rw [Submodule.mem_colon_singleton, Submodule.mem_colon_singleton, Submodule.mem_bot,
    Submodule.mem_bot, Algebra.smul_def, Algebra.smul_def, Ideal.Quotient.algebraMap_eq,
    Ideal.Quotient.algebraMap_eq, ← map_mul, ← map_mul, Ideal.Quotient.eq_zero_iff_mem,
    Ideal.Quotient.eq_zero_iff_mem, ← map_mul, Ideal.mem_map_iff_of_surjective π hπ]
  constructor
  · intro h
    exact ⟨r * b, h, rfl⟩
  · rintro ⟨y, hy, hyπ⟩
    have : r * b - y ∈ RingHom.ker π := by rw [RingHom.mem_ker, map_sub, hyπ, sub_self]
    have h2 : r * b = (r * b - y) + y := by ring
    rw [h2]
    exact add_mem (hJ this) hy

variable [IsNoetherianRing B] [IsNoetherianRing C]

/-- Associated primes of `B/J` and of `C/πJ` for a surjection `π : B → C` with `ker π ≤ J`
(p. 211, "the associated prime ideals of `M'Ã'` correspond to the associated prime ideals of
`m̄'k̃[X₂,…,X_r]` in a one to one fashion by the natural homomorphism of `Ã'` onto `k̃[X₂,…,X_r]`"):
a prime `p` of `B` is associated to `B/J` iff it contains `ker π` and its image is associated to
`C/πJ`. -/
theorem mem_associatedPrimes_quotient_iff_map (p : Ideal B) :
    p ∈ associatedPrimes B (B ⧸ J) ↔
      RingHom.ker π ≤ p ∧ p.map π ∈ associatedPrimes C (C ⧸ J.map π) := by
  constructor
  · intro h
    have hp : p.IsPrime := h.1
    obtain ⟨hp', x, hx⟩ := isAssociatedPrime_iff.mp h
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective x
    have hker : RingHom.ker π ≤ p := by
      intro r hr
      rw [hx, Submodule.mem_colon_singleton, Submodule.mem_bot]
      rw [RingHom.mem_ker] at hr
      have : r ∈ J := hJ (by rwa [RingHom.mem_ker])
      rw [Algebra.smul_def, Ideal.Quotient.algebraMap_eq, ← map_mul, Ideal.Quotient.eq_zero_iff_mem]
      exact J.mul_mem_right _ this
    refine ⟨hker, ?_⟩
    have hmap : p.map π = (⊥ : Submodule C (C ⧸ J.map π)).colon {Ideal.Quotient.mk (J.map π) (π b)} := by
      ext c
      obtain ⟨r, rfl⟩ := hπ c
      rw [Ideal.mem_map_iff_of_surjective π hπ, ← mem_colon_quotient_iff_map π hπ hJ, ← hx]
      constructor
      · rintro ⟨r', hr', hr'π⟩
        have : r - r' ∈ RingHom.ker π := by rw [RingHom.mem_ker, map_sub, hr'π, sub_self]
        have h2 : r = (r - r') + r' := by ring
        rw [h2]
        exact add_mem (hker this) hr'
      · intro hr
        exact ⟨r, hr, rfl⟩
    refine isAssociatedPrime_iff.mpr ⟨Ideal.map_isPrime_of_surjective hπ hker, Ideal.Quotient.mk (J.map π) (π b), hmap⟩
  · rintro ⟨hker, h⟩
    obtain ⟨hq, x, hx⟩ := isAssociatedPrime_iff.mp h
    obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨b, rfl⟩ := hπ c
    have hpp : p = (p.map π).comap π := by
      rw [Ideal.comap_map_of_surjective _ hπ, ← RingHom.ker_eq_comap_bot, sup_eq_left.mpr hker]
    refine isAssociatedPrime_iff.mpr ⟨?_, Ideal.Quotient.mk J b, ?_⟩
    · rw [hpp]
      exact Ideal.comap_isPrime π _
    · ext r
      rw [mem_colon_quotient_iff_map π hπ hJ, ← hx, hpp, Ideal.mem_comap, ← hpp]

end Surjective

end Hironaka
