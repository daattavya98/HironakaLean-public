/-
Copyright (c) 2026 Daattavya Aggarwal, Minhyong Kim, Oisin Kim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daattavya Aggarwal, Minhyong Kim, Oisin Kim
-/
module

public import Mathlib.RingTheory.Etale.Weakly
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.TotallySplit
public import Architect
public import Hironaka.Ch3.TauStar

/-!
# Compatibility layer: the polynomial-algebra core of Lemma 21 (Ch. III, pp. 257-258)

The proof of Lemma 21 ends (p. 257) with a computation in polynomial rings over the common residue
field `k`: with `gr_M(R) = k[Z, X_1, …, X_t, X, Y]` and `gr_{M₁}(R₁) = k[W, U, X, Y]` identified with
one polynomial ring `𝒫 = k[Z, A, B]` (`A` the variables `X_j ↔ U_j`, `B = (X, Y)`), `θ = projOut`
the substitution `B ↦ 0` ("the homomorphism `gr_{M₁}(R₁) → k[Z, X_1, …, X_t]` which maps `W_j` to
`Z_j`, `U_j` to `X_j`, `X → 0` and `Y_j → 0`"), the paper shows that `θ` induces an isomorphism
`T*_a → T_a` (`map_projOut_eq_and_injOn`: "should induce a surjective homomorphism `T*_a → T_a`.
But `T*_a` has the same rank as `T_a` by (12). This homomorphism `T*_a → T_a` is an isomorphism of
`k`-modules"); the rest (`ψ = φ(W, U_1 + L_1, …)`, whence `τ_{(w)}(g) = τ_{(z)}(f)`) is in
`Compat/TauZAdapted.lean`.  Everything here is about `MvPolynomial (Fin n) K` for a field `K`.
-/

@[expose] public section

open MvPolynomial
open scoped Classical

namespace Hironaka

universe u

section PolyCore

variable {K : Type u} [Field K] {n : ℕ}

/-- The substitution `X_i ↦ X_i` for `i ∈ U`, `X_i ↦ 0` for `i ∉ U`: the paper's homomorphism
`gr_{M₁}(R₁) → k[Z, X_1, …, X_t]` sending `X` and `Y_j` to `0` (p. 257). -/
noncomputable def projOut (U : Set (Fin n)) : MvPolynomial (Fin n) K →ₐ[K] MvPolynomial (Fin n) K :=
  aeval fun i => if i ∈ U then X i else 0

/-- The ideal `(X_b)_{b ∉ U}`: the paper's `(X, Y_1, …, Y_s) gr_{M₁}(R₁)`. -/
noncomputable def outIdeal (U : Set (Fin n)) : Ideal (MvPolynomial (Fin n) K) :=
  Ideal.span (X '' Uᶜ)

variable (U : Set (Fin n))

theorem projOut_X (i : Fin n) : projOut (K := K) U (X i) = if i ∈ U then X i else 0 := by
  simp [projOut]

theorem projOut_of_mem_supported {p : MvPolynomial (Fin n) K} (hp : p ∈ supported K U) :
    projOut U p = p := by
  rw [supported_eq_adjoin_X] at hp
  have hle : Algebra.adjoin K (X '' U) ≤ AlgHom.equalizer (projOut U) (AlgHom.id K _) := by
    refine Algebra.adjoin_le ?_
    rintro _ ⟨i, hi, rfl⟩
    simp [AlgHom.equalizer, projOut_X, hi]
  exact hle hp

theorem sub_projOut_mem_outIdeal (p : MvPolynomial (Fin n) K) :
    p - projOut U p ∈ outIdeal (K := K) U := by
  induction p using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq =>
    have := add_mem hp hq
    rwa [map_add, show p + q - (projOut U p + projOut U q) = p - projOut U p + (q - projOut U q)
      by ring]
  | mul_X p i hp =>
    rw [map_mul, projOut_X]
    split_ifs with hi
    · have : p * X i - projOut U p * X i = (p - projOut U p) * X i := by ring
      rw [this]
      exact Ideal.mul_mem_right _ _ hp
    · have : p * X i - projOut U p * 0 = p * X i := by ring
      rw [this]
      exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨i, hi, rfl⟩)

theorem projOut_eq_zero_iff (p : MvPolynomial (Fin n) K) :
    projOut U p = 0 ↔ p ∈ outIdeal (K := K) U := by
  constructor
  · intro h
    have := sub_projOut_mem_outIdeal U p
    rwa [h, sub_zero] at this
  · intro h
    have hle : outIdeal (K := K) U ≤ RingHom.ker (projOut (K := K) U).toRingHom := by
      refine Ideal.span_le.mpr ?_
      rintro _ ⟨i, hi, rfl⟩
      simpa [projOut_X] using hi
    exact hle h

theorem projOut_sub_of_mem_outIdeal {p q : MvPolynomial (Fin n) K}
    (h : p - q ∈ outIdeal (K := K) U) : projOut U p = projOut U q := by
  have := (projOut_eq_zero_iff U _).mpr h
  rwa [map_sub, sub_eq_zero] at this

theorem projOut_homogeneous {p : MvPolynomial (Fin n) K} {d : ℕ}
    (hp : p ∈ homogeneousSubmodule (Fin n) K d) :
    projOut U p ∈ homogeneousSubmodule (Fin n) K d := by
  rw [mem_homogeneousSubmodule] at hp ⊢
  have h := hp.eval₂ (algebraMap K (MvPolynomial (Fin n) K))
    (fun i => if i ∈ U then (X i : MvPolynomial (Fin n) K) else 0)
    (fun r => isHomogeneous_C _ r) (n := 1) (fun i => by
      by_cases hi : i ∈ U
      · simpa [hi] using isHomogeneous_X K i
      · simpa [hi] using isHomogeneous_zero (Fin n) K 1)
  have e : projOut (K := K) U p = eval₂ (algebraMap K (MvPolynomial (Fin n) K))
      (fun i => if i ∈ U then (X i : MvPolynomial (Fin n) K) else 0) p := rfl
  rw [e]
  simpa using h


theorem finiteDimensional_of_le_homogeneous_one {T : Submodule K (MvPolynomial (Fin n) K)}
    (hT : T ≤ homogeneousSubmodule (Fin n) K 1) : FiniteDimensional K T := by
  have : FiniteDimensional K (homogeneousSubmodule (Fin n) K 1) := by
    rw [homogeneousSubmodule_one_eq_span_X]
    exact FiniteDimensional.span_of_finite _ (Set.finite_range _)
  exact Submodule.finiteDimensional_of_le hT

theorem projOut_map_homogeneous_one {T : Submodule K (MvPolynomial (Fin n) K)}
    (hT : T ≤ homogeneousSubmodule (Fin n) K 1) :
    T.map (projOut (K := K) U).toLinearMap ≤ homogeneousSubmodule (Fin n) K 1 := by
  rintro _ ⟨t, ht, rfl⟩
  exact projOut_homogeneous U (hT ht)

/-- **Step 1 of the poly core**: `θ(T₁)` has the property of Definition 6 for `(q)` up to `μb`
as soon as `q_i = θ(q₁_i)` with `q₁_i ∈ k[T₁]`. -/
theorem isTauSubmoduleMv_map_projOut {ι : Type*} (q q₁ : ι → MvPolynomial (Fin n) K) (μb : ℕ)
    (hqU : ∀ i, q i ∈ supported K U) (hq₁ : ∀ i, q₁ i - q i ∈ outIdeal (K := K) U)
    (T₁ : Submodule K (MvPolynomial (Fin n) K)) (hT₁ : T₁ ≤ homogeneousSubmodule (Fin n) K 1)
    (hq₁T₁ : ∀ i, q₁ i ∈ Algebra.adjoin K (T₁ : Set (MvPolynomial (Fin n) K))) :
    IsTauSubmoduleMv K n (Ideal.span (Set.range q)) (T₁.map (projOut (K := K) U).toLinearMap) μb := by
  refine ⟨projOut_map_homogeneous_one U hT₁, fun μ _ ψ _ => ⟨fun hψ => ?_, fun hψ => ?_⟩⟩
  · refine (Ideal.span_le.mpr ?_ : Ideal.span (Set.range q) ≤ _) hψ
    rintro _ ⟨i, rfl⟩
    refine Ideal.subset_span ⟨Ideal.subset_span ⟨i, rfl⟩, ?_⟩
    have h1 : projOut U (q₁ i) = q i := by
      rw [projOut_sub_of_mem_outIdeal U (hq₁ i), projOut_of_mem_supported U (hqU i)]
    have h2 : projOut U (q₁ i) ∈ (Algebra.adjoin K (T₁ : Set (MvPolynomial (Fin n) K))).map
        (projOut (K := K) U) := ⟨q₁ i, hq₁T₁ i, rfl⟩
    rw [AlgHom.map_adjoin, h1] at h2
    refine Algebra.adjoin_mono ?_ h2
    rintro _ ⟨t, ht, rfl⟩
    exact ⟨t, ht, rfl⟩
  · exact (Ideal.span_le.mpr fun x hx => hx.1) hψ

/-- **The poly core, part A** (p. 257: "the homomorphism `gr_{M₁}(R₁) → k[Z, X_1, …, X_t]` … should
induce a surjective homomorphism `T*_a → T_a`.  But `T*_a` has the same rank as `T_a` by (12).
This homomorphism `T*_a → T_a` is an isomorphism of `k`-modules"). -/
theorem map_projOut_eq_and_injOn {ι : Type*} (q q₁ : ι → MvPolynomial (Fin n) K) (μb : ℕ)
    (hqU : ∀ i, q i ∈ supported K U) (hq₁ : ∀ i, q₁ i - q i ∈ outIdeal (K := K) U)
    (T₀ T₁ : Submodule K (MvPolynomial (Fin n) K))
    (hT₀ : IsTauSubmoduleMv K n (Ideal.span (Set.range q)) T₀ μb)
    (hT₀min : ∀ T, IsTauSubmoduleMv K n (Ideal.span (Set.range q)) T μb → T₀ ≤ T)
    (hT₁ : T₁ ≤ homogeneousSubmodule (Fin n) K 1)
    (hq₁T₁ : ∀ i, q₁ i ∈ Algebra.adjoin K (T₁ : Set (MvPolynomial (Fin n) K)))
    (hrank : Module.finrank K T₁ = Module.finrank K T₀) :
    T₀ = T₁.map (projOut (K := K) U).toLinearMap ∧ Set.InjOn (projOut (K := K) U) (T₁ : Set _) := by
  have := finiteDimensional_of_le_homogeneous_one hT₁
  have := finiteDimensional_of_le_homogeneous_one hT₀.1
  set θ : MvPolynomial (Fin n) K →ₗ[K] MvPolynomial (Fin n) K := (projOut (K := K) U).toLinearMap
  have hle : T₀ ≤ T₁.map θ :=
    hT₀min _ (isTauSubmoduleMv_map_projOut U q q₁ μb hqU hq₁ T₁ hT₁ hq₁T₁)
  have h1 : Module.finrank K (T₁.map θ) ≤ Module.finrank K T₁ := Submodule.finrank_map_le θ T₁
  have h2 : Module.finrank K T₀ ≤ Module.finrank K (T₁.map θ) := Submodule.finrank_mono hle
  have h3 : Module.finrank K (T₁.map θ) = Module.finrank K T₁ := by omega
  refine ⟨Submodule.eq_of_le_of_finrank_eq hle (by omega), ?_⟩
  -- injectivity on `T₁`
  let f : T₁ →ₗ[K] MvPolynomial (Fin n) K := θ.domRestrict T₁
  have hrange : LinearMap.range f = T₁.map θ := LinearMap.range_domRestrict T₁ θ
  have hker : Module.finrank K (LinearMap.ker f) = 0 := by
    have := LinearMap.finrank_range_add_finrank_ker f
    rw [hrange] at this
    omega
  have hker' : LinearMap.ker f = ⊥ := Submodule.finrank_eq_zero.mp hker
  intro a ha b hb hab
  have : f ⟨a, ha⟩ = f ⟨b, hb⟩ := hab
  have := LinearMap.ker_eq_bot.mp hker' this
  exact congrArg Subtype.val this

end PolyCore

end Hironaka
