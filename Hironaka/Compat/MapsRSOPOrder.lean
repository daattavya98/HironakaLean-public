/-
Copyright (c) 2026 Daattavya Aggarwal, Minhyong Kim, Oisin Kim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daattavya Aggarwal, Minhyong Kim, Oisin Kim
-/
module

public import Mathlib.RingTheory.MvPolynomial.Ideal
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Hironaka.Ch3.Basic
public import Hironaka.Compat.RegularGraded

/-!
# `MR̄ = M̄` and `α⁻¹(M_R̄ⁿ) = M_Rⁿ` for a local homomorphism transforming a regular system of parameters

Used for the orders of elements in `gr_M(R)` and `gr_{M'}(R')` (the Corollary to Lemma 2, p. 207: "we
can easily see that `σ̄(φ_j)` is the initial form of `α(f_j)`") and in Lemma 4 (p. 212,
`RingHom.MapsRSOP.injective`).  Moved here from `Ch3/Transforms.lean` so that `Ch3/NuStar.lean`
can use it.
-/

@[expose] public section

open IsLocalRing

namespace Hironaka

universe u

section MapsRSOPOrder

variable {R Rb : Type u} [CommRing R] [IsRegularLocalRing R] [CommRing Rb] [IsRegularLocalRing Rb]

/-- p. 210: if `α : R → R̄` transforms a regular system of parameters of `R` into one of `R̄`,
then `MR̄ = M̄`. -/
theorem RingHom.MapsRSOP.map_maximalIdeal {α : R →+* Rb} (hα : RingHom.MapsRSOP α) :
    (maximalIdeal R).map α = maximalIdeal Rb := by
  classical
  obtain ⟨s, hs, hs', -⟩ := hα
  rw [← hs.1, Ideal.map_span, ← hs'.1, Finset.coe_image]

open MvPolynomial in
/-- The graded pieces of `R` and `R̄` agree along a local homomorphism `α` which transforms a regular
system of parameters `(x₁, …, x_n)` of `R` into one of the regular local ring `R̄`:
`α⁻¹(M_R̄ᵏ) = M_Rᵏ`.  Writing `a ∈ M_Rᵏ` as a form `F(x)` of degree `k` (`M_Rᵏ = (x)ᵏ`), the
quasi-regularity of `(αx₁, …, αx_n)` in `R̄` (`gr_{M_R̄}(R̄) = k̄[X]`, `X_i ↦ [αx_i]`) shows that
`α(a) ∈ M_R̄ᵏ⁺¹` forces all the coefficients of `F` into `M_R`, i.e. `a ∈ M_Rᵏ⁺¹`. -/
theorem RingHom.MapsRSOP.comap_maximalIdeal_pow {α : R →+* Rb} [IsLocalHom α]
    (hα : RingHom.MapsRSOP α) (k : ℕ) : ((maximalIdeal Rb) ^ k).comap α = maximalIdeal R ^ k := by
  classical
  obtain ⟨s, hs, hαs, hinj⟩ := hα
  apply le_antisymm
  · -- the common regular system of parameters `x : Fin n → A`, `z = α ∘ x`
    let x : Fin s.card → R := fun i => ((s.equivFin.symm i : s) : R)
    have hxrange : Set.range x = (s : Set R) := by
      ext y
      constructor
      · rintro ⟨i, rfl⟩
        exact (s.equivFin.symm i).2
      · intro hy
        exact ⟨s.equivFin ⟨y, hy⟩, by simp [x]⟩
    have hxspan : Ideal.span (Set.range x) = maximalIdeal R := by rw [hxrange, hs.1]
    let z : Fin s.card → Rb := α ∘ x
    have hzrange : Set.range z = ((s.image α : Finset Rb) : Set Rb) := by
      rw [Finset.coe_image, ← hxrange, ← Set.range_comp]
    have hzspan : Ideal.span (Set.range z) = maximalIdeal Rb := by rw [hzrange, hαs.1]
    have hzinj : Function.Injective z := by
      intro i j hij
      have := hinj (s.equivFin.symm i).2 (s.equivFin.symm j).2 hij
      exact s.equivFin.symm.injective (Subtype.ext this)
    have hzqr : IsQuasiRegular z := by
      have hcard : (s.image α).card = (maximalIdeal Rb).spanFinrank := by
        have h1 := IsRegularLocalRing.spanFinrank_maximalIdeal (R := Rb)
        rw [← hαs.2] at h1
        exact (by exact_mod_cast h1 : (maximalIdeal Rb).spanFinrank = _).symm
      exact isQuasiRegular_of_minimal hαs.1 hcard hzinj
        (fun i => Finset.mem_image_of_mem α (s.equivFin.symm i).2)
    induction k with
    | zero => simp
    | succ k ih =>
      intro a ha
      have ha' : a ∈ (maximalIdeal Rb ^ k).comap α :=
        Ideal.comap_mono (Ideal.pow_le_pow_right (Nat.le_succ k)) ha
      have hak : a ∈ maximalIdeal R ^ k := ih ha'
      rw [← hxspan] at hak
      obtain ⟨F, hF, rfl⟩ := (Ideal.mem_span_pow_iff_exists_isHomogeneous x a).mp hak
      have hαF : α (eval x F) = eval z (F.map α) := by
        rw [eval_map, show eval x F = eval₂ (RingHom.id R) x F from rfl, hom_eval₂]
        rfl
      have hmem : eval z (F.map α) ∈ Ideal.span (Set.range z) ^ (k + 1) := by
        rw [← hαF, hzspan]
        exact ha
      have hcoeff := hzqr k (F.map α) (hF.map α) hmem
      have hc : ∀ μ, F.coeff μ ∈ maximalIdeal R := by
        intro μ
        have h1 := hcoeff μ
        rw [coeff_map, hzspan] at h1
        by_contra h2
        exact ((IsLocalRing.mem_maximalIdeal _).mp h1)
          (((IsLocalRing.mem_maximalIdeal _).not.mp h2 |> not_not.mp).map _)
      have := eval_mem_mul_span_pow_of_coeff_mem (y := x) hF hc
      rwa [hxspan, ← pow_succ'] at this
  · have hmn : (maximalIdeal R).map α ≤ maximalIdeal Rb := by
      rw [Ideal.map_le_iff_le_comap]
      intro a ha
      exact map_nonunit α a ha
    rw [← Ideal.map_le_iff_le_comap, Ideal.map_pow]
    exact Ideal.pow_right_mono hmn k

end MapsRSOPOrder

end Hironaka
