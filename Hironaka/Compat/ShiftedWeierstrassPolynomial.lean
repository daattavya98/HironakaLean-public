/-
Copyright (c) 2026 Daattavya Aggarwal, Minhyong Kim, Oisin Kim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daattavya Aggarwal, Minhyong Kim, Oisin Kim
-/
module

public import Mathlib.Algebra.Polynomial.Coeff

/-!
# The Weierstrass polynomial after the substitution `T ↦ T - b`

Lemma 25, p. 270: "Therefore, we may replace `x₁` by `x₁ + e⁻¹ p'₁` […] Thus we may assume that
`h_Ā = u(x₁^e + p₂x₁^{e-2} + ⋯ + p_e)`": for a monic polynomial `T^e + a₁T^{e-1} + ⋯ + a_e`
over a commutative ring and `b` with `e b = a₁`, the polynomial obtained by the substitution
`T ↦ T - b` has no term in `T^{e-1}`.  (Tschirnhaus transformation; the identity is purely
polynomial.)
-/

@[expose] public section

open Polynomial

namespace Hironaka

universe u

section TaylorShape

variable {B : Type u} [CommRing B]

/-- The Weierstrass polynomial after the substitution `T ↦ T - b`. -/
noncomputable def shiftedWeierstrass (e : ℕ) (a : Fin e → B) (b : B) : B[X] :=
  (X + C (-b)) ^ e + ∑ l : Fin e, C (a l) * (X + C (-b)) ^ (e - ((l : ℕ) + 1))

theorem coeff_shiftedWeierstrass_self (e : ℕ) (a : Fin e → B) (b : B) :
    (shiftedWeierstrass e a b).coeff e = 1 := by
  unfold shiftedWeierstrass
  rw [coeff_add, coeff_X_add_C_pow, finsetSum_coeff]
  rw [Finset.sum_eq_zero]
  · simp
  · intro l _
    rw [coeff_C_mul, coeff_X_add_C_pow]
    have : (e - ((l : ℕ) + 1)).choose e = 0 :=
      Nat.choose_eq_zero_of_lt (by have := l.2; omega)
    simp [this]

theorem coeff_shiftedWeierstrass_of_lt (e : ℕ) (a : Fin e → B) (b : B) {i : ℕ} (hi : e < i) :
    (shiftedWeierstrass e a b).coeff i = 0 := by
  unfold shiftedWeierstrass
  rw [coeff_add, coeff_X_add_C_pow, finsetSum_coeff]
  rw [Finset.sum_eq_zero]
  · simp [Nat.choose_eq_zero_of_lt hi]
  · intro l _
    rw [coeff_C_mul, coeff_X_add_C_pow]
    have : (e - ((l : ℕ) + 1)).choose i = 0 :=
      Nat.choose_eq_zero_of_lt (by have := l.2; omega)
    simp [this]

theorem coeff_shiftedWeierstrass_pred (e : ℕ) (he : 0 < e) (a : Fin e → B) (b : B)
    (hb : (e : B) * b = a ⟨0, he⟩) : (shiftedWeierstrass e a b).coeff (e - 1) = 0 := by
  unfold shiftedWeierstrass
  rw [coeff_add, coeff_X_add_C_pow, finsetSum_coeff]
  have h1 : ∑ l : Fin e, (C (a l) * (X + C (-b)) ^ (e - ((l : ℕ) + 1))).coeff (e - 1) =
      a ⟨0, he⟩ := by
    rw [Finset.sum_eq_single (⟨0, he⟩ : Fin e)]
    · rw [coeff_C_mul, coeff_X_add_C_pow]
      simp
    · intro l _ hl
      rw [coeff_C_mul, coeff_X_add_C_pow]
      have hl0 : (l : ℕ) ≠ 0 := fun h => hl (Fin.ext h)
      have : (e - ((l : ℕ) + 1)).choose (e - 1) = 0 :=
        Nat.choose_eq_zero_of_lt (by have := l.2; omega)
      simp [this]
    · intro h; exact absurd (Finset.mem_univ _) h
  rw [h1]
  have h2 : e.choose (e - 1) = e := by
    obtain ⟨e', rfl⟩ : ∃ e', e = e' + 1 := ⟨e - 1, by omega⟩
    simp
  have h3 : (-b) ^ (e - (e - 1)) * (e.choose (e - 1) : B) = - ((e : B) * b) := by
    rw [show e - (e - 1) = 1 by omega, pow_one, h2]
    ring
  rw [h3, hb]
  ring

theorem shiftedWeierstrass_eq (e : ℕ) (he : 0 < e) (a : Fin e → B) (b : B)
    (hb : (e : B) * b = a ⟨0, he⟩) :
    shiftedWeierstrass e a b = X ^ e + ∑ j ∈ Finset.Icc 2 e,
      C ((shiftedWeierstrass e a b).coeff (e - j)) * X ^ (e - j) := by
  ext i
  rw [coeff_add, coeff_X_pow, finsetSum_coeff]
  simp only [coeff_C_mul_X_pow]
  by_cases hie : i = e
  · subst hie
    rw [coeff_shiftedWeierstrass_self]
    rw [Finset.sum_eq_zero]
    · simp
    · intro j hj
      have := (Finset.mem_Icc.mp hj).1
      have hne : ¬ (i = i - j) := by omega
      simp [hne]
  · have hne : ¬ (i = e) := hie
    by_cases hgt : e < i
    · rw [coeff_shiftedWeierstrass_of_lt e a b hgt]
      rw [Finset.sum_eq_zero]
      · simp [hne]
      intro j hj
      have := (Finset.mem_Icc.mp hj)
      have hne' : ¬ (i = e - j) := by omega
      simp [hne']
    · by_cases hpred : i = e - 1
      · subst hpred
        rw [coeff_shiftedWeierstrass_pred e he a b hb]
        rw [Finset.sum_eq_zero]
        · simp [hne]
        intro j hj
        have := (Finset.mem_Icc.mp hj)
        have hne' : ¬ (e - 1 = e - j) := by omega
        simp [hne']
      · have hj : e - i ∈ Finset.Icc 2 e := by
          rw [Finset.mem_Icc]; omega
        rw [Finset.sum_eq_single (e - i)]
        · have : i = e - (e - i) := by omega
          simp [hne, ← this]
        · intro j hjmem hne2
          have := Finset.mem_Icc.mp hjmem
          have hne' : ¬ (i = e - j) := by omega
          simp [hne']
        · intro h; exact absurd hj h

end TaylorShape

end Hironaka
