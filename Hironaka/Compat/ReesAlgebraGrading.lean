/-
Copyright (c) 2026 Daattavya Aggarwal, Minhyong Kim, Oisin Kim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daattavya Aggarwal, Minhyong Kim, Oisin Kim
-/
module

public import Mathlib.RingTheory.ReesAlgebra
public import Mathlib.RingTheory.GradedAlgebra.Basic

/-!
# The grading of the Rees algebra

The Rees algebra `reesAlgebra J` of an ideal `J` of `A` (Mathlib: the subalgebra of `A[X]` whose
`n`-th coefficient lies in `J ^ n`) is the direct sum `⊕ₙ Jⁿ` as a graded `A`-algebra
(Ch. 0 §2, p. 128: `S*_A(J)`).  Mathlib does not give it a grading; this file gives the
decomposition into the pieces `reesPiece J n`, consisting of the elements all of whose coefficients
outside degree `n` vanish, so that `Proj` can be formed.
-/

@[expose] public section

open Polynomial

namespace Rees

variable {A : Type*} [CommRing A] (J : Ideal A)

/-- The homogeneous part of degree `n` of the Rees algebra `⊕ₙ Jⁿ`: the elements of
`reesAlgebra J` that are supported in degree `n`; it is `Jⁿ Xⁿ`. -/
def reesPiece (n : ℕ) : Submodule A (reesAlgebra J) where
  carrier := {p | ∀ i, i ≠ n → p.1.coeff i = 0}
  add_mem' ha hb i hi := by simp [ha i hi, hb i hi]
  zero_mem' i _ := by simp
  smul_mem' c p hp i hi := by
    show (c • p.1).coeff i = 0
    simp [hp i hi]

theorem mem_reesPiece {n : ℕ} {p : reesAlgebra J} :
    p ∈ reesPiece J n ↔ ∀ i, i ≠ n → p.1.coeff i = 0 := Iff.rfl

theorem eq_monomial_of_mem_reesPiece {n : ℕ} {p : reesAlgebra J} (hp : p ∈ reesPiece J n) :
    p.1 = monomial n (p.1.coeff n) := by
  ext i
  by_cases h : i = n
  · subst h; simp
  · rw [hp i h]; simp [coeff_monomial, Ne.symm h]

instance : SetLike.GradedMonoid (reesPiece J) where
  one_mem := by
    intro i hi
    show (1 : A[X]).coeff i = 0
    simp [coeff_one, hi]
  mul_mem := by
    intro i j p q hp hq k hk
    show (p.1 * q.1).coeff k = 0
    rw [eq_monomial_of_mem_reesPiece J hp, eq_monomial_of_mem_reesPiece J hq,
      monomial_mul_monomial, coeff_monomial]
    simp [Ne.symm hk]

open scoped DirectSum

theorem coe_coeff_sum (d : ⨁ n, reesPiece J n) (j : ℕ) :
    ((DirectSum.coeLinearMap (reesPiece J) d : reesAlgebra J) : A[X]).coeff j =
      ((d j : reesPiece J j) : reesAlgebra J).1.coeff j := by
  induction d using DirectSum.induction_on with
  | zero => simp
  | of i x =>
    rw [DirectSum.coeLinearMap_of, DirectSum.of_apply]
    by_cases h : i = j
    · subst h; simp
    · simp [h, x.2 j (Ne.symm h)]
  | add x y hx hy => simp [hx, hy]

theorem isInternal_reesPiece : DirectSum.IsInternal (reesPiece J) := by
  constructor
  · intro d e hde
    have hde' : DirectSum.coeLinearMap (reesPiece J) d = DirectSum.coeLinearMap (reesPiece J) e :=
      hde
    have : ∀ j, d j = e j := by
      intro j
      have h := congrArg (fun p : reesAlgebra J => p.1.coeff j) hde'
      simp only [coe_coeff_sum] at h
      apply Subtype.ext
      apply Subtype.ext
      ext i
      by_cases hij : i = j
      · subst hij; exact h
      · rw [(d j).2 i hij, (e j).2 i hij]
    exact DFinsupp.ext this
  · intro p
    refine ⟨∑ i ∈ p.1.support, DirectSum.of (fun n => reesPiece J n) i
      ⟨⟨monomial i (p.1.coeff i), reesAlgebra.monomial_coeff_mem p i⟩, ?_⟩, ?_⟩
    · intro k hk
      simp [coeff_monomial, Ne.symm hk]
    · change DirectSum.coeLinearMap (reesPiece J) _ = p
      rw [map_sum]
      simp only [DirectSum.coeLinearMap_of]
      exact (reesAlgebra.as_sum_support p).symm

/-- The Rees algebra `⊕ₙ Jⁿ` is a graded `A`-algebra, the piece of degree `n` being `Jⁿ Xⁿ`
(Ch. 0 §2, p. 128: `S*_A(J)`). -/
noncomputable instance gradedAlgebra : GradedAlgebra (reesPiece J) :=
  (isInternal_reesPiece J).gradedAlgebra

/-- The inclusion `J → S*(J)₁`, `j ↦ j X`. -/
noncomputable def toDegreeOne : J →ₗ[A] reesAlgebra J where
  toFun j := ⟨monomial 1 j.1, reesAlgebra.monomial_mem.mpr (by simp)⟩
  map_add' a b := Subtype.ext (by simp)
  map_smul' c a := Subtype.ext (by
    show monomial 1 (c * a.1) = c • monomial 1 a.1
    rw [Polynomial.smul_monomial]; rfl)

theorem toDegreeOne_mem (j : J) : toDegreeOne J j ∈ reesPiece J 1 := by
  intro i hi
  show (monomial 1 j.1 : A[X]).coeff i = 0
  rw [coeff_monomial]
  simp [Ne.symm hi]

end Rees
