/-
Copyright (c) 2026 Daattavya Aggarwal, Minhyong Kim, Oisin Kim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daattavya Aggarwal, Minhyong Kim, Oisin Kim
-/
module

public import Mathlib.Algebra.MvPolynomial.Supported
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Hironaka.Compat.WeierstrassTauLift

/-!
# Lemma 25, (ii) of (c) (p. 273): "`eL = 0`, hence `L = 0`"

In the proof of (ii) of (c) of Lemma 25 the paper has found linear forms `(L, L₁, …, L_τ)` in the
exceptional variables `Y, X₁, …, X_a` with `φ̄ = φ(Z̄, W̄ + L, Ȳ₁ + L₁, …)` (p. 272, see
`exists_lift` in `WeierstrassTauLift.lean`), and concludes on p. 273, from the shapes of `φ` and `φ̄`,
that "`eL = 0`, hence `L = 0`".  This file proves that step for polynomials over a field of
characteristic `0` (`eq_zero_of_aeval_add_of_coeff`): comparing the coefficients of
`Z̄^Ā W̄^{e-1} X_b` (`b` an exceptional variable) in `φ̄ = σ φ`.

The auxiliary lemmas describe the monomials of `σ (X^m)`, `σ = aeval (fun v => X v + ℓ v)`: the
exponents at the `Z`'s are those of `m` (weighted homogeneity), the exponent at `W` is at most that
of `m` (`degreeOf`), and `σ (X^(Ā + e W)) = X^Ā (X_W + L)^e`.
-/

@[expose] public section

open MvPolynomial

namespace Hironaka

section Support

variable {K : Type*} [Field K] {ι : Type*} [DecidableEq ι]

omit [DecidableEq ι] in
/-- A linear form in the variables of `s` is a polynomial in those variables. -/
theorem mem_supported_of_mem_linSpan {s : Set ι} {t : MvPolynomial ι K}
    (ht : t ∈ linSpan (k := K) s) : t ∈ supported K s := by
  have h : linSpan (k := K) s ≤ Subalgebra.toSubmodule (supported K s) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨v, hv, rfl⟩
    exact (X_mem_supported (R := K)).2 hv
  exact h ht

/-- Every monomial of a linear form in the variables of `s` is a single variable of `s`. -/
theorem eq_single_of_mem_support_of_mem_linSpan {s : Set ι} {t : MvPolynomial ι K}
    (ht : t ∈ linSpan (k := K) s) {m : ι →₀ ℕ} (hm : m ∈ t.support) :
    ∃ b ∈ s, m = Finsupp.single b 1 := by
  revert m
  refine Submodule.span_induction (p := fun t _ => ∀ {m : ι →₀ ℕ}, m ∈ t.support →
    ∃ b ∈ s, m = Finsupp.single b 1) ?_ ?_ ?_ ?_ ht
  · rintro _ ⟨v, hv, rfl⟩ m hm
    rw [support_X, Finset.mem_singleton] at hm
    exact ⟨v, hv, hm⟩
  · intro m hm
    simp at hm
  · intro a b _ _ ha hb m hm
    rcases Finset.mem_union.1 (support_add hm) with h | h
    · exact ha h
    · exact hb h
  · intro c a _ ha m hm
    exact ha (support_smul hm)

omit [DecidableEq ι] in
/-- A polynomial in the variables of `s` has exponent `0` at every variable outside `s`. -/
theorem apply_eq_zero_of_mem_support_of_mem_supported {s : Set ι} {g : MvPolynomial ι K}
    (hg : g ∈ supported K s) {m : ι →₀ ℕ} (hm : m ∈ g.support) {a : ι} (ha : a ∉ s) :
    m a = 0 := by
  by_contra h
  apply ha
  exact mem_supported.1 hg
    ((mem_vars_iff_mem_support (p := g) a).2 ⟨m, hm, Finsupp.mem_support_iff.2 h⟩)

omit [DecidableEq ι] in
/-- A polynomial in the variables of `s` has coefficient `0` at a monomial involving a variable
outside `s`. -/
theorem coeff_eq_zero_of_mem_supported {s : Set ι} {g : MvPolynomial ι K}
    (hg : g ∈ supported K s) {m : ι →₀ ℕ} {a : ι} (ha : a ∉ s) (hm : m a ≠ 0) :
    g.coeff m = 0 := by
  by_contra h
  exact hm (apply_eq_zero_of_mem_support_of_mem_supported hg (mem_support_iff.2 h) ha)

/-- A polynomial in the variables of `s` is weighted homogeneous of weight `0` for the weight
counting the exponent of a variable `i ∉ s`. -/
theorem isWeightedHomogeneous_single_of_mem_supported {s : Set ι} {g : MvPolynomial ι K}
    (hg : g ∈ supported K s) {i : ι} (hi : i ∉ s) :
    IsWeightedHomogeneous (Pi.single i (1 : ℕ)) g 0 := by
  intro m hm
  rw [Finsupp.weight_single_one_apply]
  exact apply_eq_zero_of_mem_support_of_mem_supported hg (mem_support_iff.2 hm) hi

/-- The substitution `X v ↦ X v + ℓ v` carries a monomial `X^m` to a weighted homogeneous
polynomial of weight `m i` for the weight counting the exponent of `X i`, `i ∈ zS`. -/
theorem isWeightedHomogeneous_aeval_monomial {B zS : Set ι} (hzB : ∀ i ∈ zS, i ∉ B)
    {ℓ : ι → MvPolynomial ι K} (hℓ : ∀ v, ℓ v ∈ supported K B) (hℓz : ∀ v ∈ zS, ℓ v = 0)
    (m : ι →₀ ℕ) {i : ι} (hi : i ∈ zS) :
    IsWeightedHomogeneous (Pi.single i (1 : ℕ))
      (aeval (fun v => X v + ℓ v) (monomial m (1 : K))) (m i) := by
  have hw : m.sum (fun v c => c • (Pi.single i (1 : ℕ) : ι → ℕ) v) = m i := by
    rw [← Finsupp.weight_apply, Finsupp.weight_single_one_apply]
  rw [aeval_monomial, map_one, one_mul, Finsupp.prod, ← hw, Finsupp.sum]
  refine IsWeightedHomogeneous.prod _ _ _ (fun v _ => ?_)
  refine IsWeightedHomogeneous.pow (m := (Pi.single i (1 : ℕ) : ι → ℕ) v) ?_ (m v)
  by_cases hvi : v = i
  · subst hvi
    rw [hℓz v hi, add_zero]
    exact isWeightedHomogeneous_X K _ v
  · have h0 : (Pi.single i (1 : ℕ) : ι → ℕ) v = 0 := Pi.single_eq_of_ne hvi _
    have hX := isWeightedHomogeneous_X K (Pi.single i (1 : ℕ) : ι → ℕ) v
    have hL : IsWeightedHomogeneous (Pi.single i (1 : ℕ)) (ℓ v)
        ((Pi.single i (1 : ℕ) : ι → ℕ) v) := by
      rw [h0]
      exact isWeightedHomogeneous_single_of_mem_supported (hℓ v) (hzB i hi)
    exact hX.add hL

/-- Step 1 (zS-exponents): every monomial of `σ (X^m)` has the same exponents as `m` at `i ∈ zS`. -/
theorem apply_eq_of_mem_support_aeval_monomial {B zS : Set ι} (hzB : ∀ i ∈ zS, i ∉ B)
    {ℓ : ι → MvPolynomial ι K} (hℓ : ∀ v, ℓ v ∈ supported K B) (hℓz : ∀ v ∈ zS, ℓ v = 0)
    (m : ι →₀ ℕ) {m' : ι →₀ ℕ}
    (hm' : m' ∈ (aeval (fun v => X v + ℓ v) (monomial m (1 : K))).support) {i : ι}
    (hi : i ∈ zS) : m' i = m i := by
  have := isWeightedHomogeneous_aeval_monomial hzB hℓ hℓz m hi (mem_support_iff.1 hm')
  rwa [Finsupp.weight_single_one_apply] at this

/-- Step 1 (`wI`-exponent): no monomial of `σ (X^m)` has a larger exponent at `wI ∉ B` than `m`. -/
theorem apply_le_of_mem_support_aeval_monomial {B : Set ι} {wI : ι} (hwB : wI ∉ B)
    {ℓ : ι → MvPolynomial ι K} (hℓ : ∀ v, ℓ v ∈ supported K B)
    (m : ι →₀ ℕ) {m' : ι →₀ ℕ}
    (hm' : m' ∈ (aeval (fun v => X v + ℓ v) (monomial m (1 : K))).support) : m' wI ≤ m wI := by
  have hw : m.sum (fun v c => c • (Pi.single wI (1 : ℕ) : ι → ℕ) v) = m wI := by
    rw [← Finsupp.weight_apply, Finsupp.weight_single_one_apply]
  have hdeg : ∀ v, degreeOf wI (X v + ℓ v : MvPolynomial ι K) ≤
      (Pi.single wI (1 : ℕ) : ι → ℕ) v := by
    intro v
    have hℓ0 : degreeOf wI (ℓ v) = 0 := by
      refine Nat.le_zero.1 (degreeOf_le_iff.2 fun m hm => ?_)
      exact (apply_eq_zero_of_mem_support_of_mem_supported (hℓ v) hm hwB).le
    refine (degreeOf_add_le wI _ _).trans ?_
    rw [hℓ0, degreeOf_X, Nat.max_zero]
    by_cases h : v = wI
    · subst h
      simp
    · rw [Pi.single_eq_of_ne h]
      simp [Ne.symm h]
  refine (monomial_le_degreeOf wI hm').trans ?_
  rw [aeval_monomial, map_one, one_mul, Finsupp.prod, ← hw, Finsupp.sum]
  refine (degreeOf_prod_le _ _ _).trans (Finset.sum_le_sum fun v _ => ?_)
  refine (degreeOf_pow_le _ _ _).trans ?_
  rw [smul_eq_mul]
  exact Nat.mul_le_mul_left _ (hdeg v)

omit [DecidableEq ι] in
/-- The binomial expansion in the computation of `σ (X^(Ā + e W))` (p. 273): if `L` is a polynomial
in variables other than `wI`, the coefficient of `X wI ^ e' * X b` in `(X wI + L) ^ (e' + 1)` is
`e' + 1` times the coefficient of `X b` in `L`. -/
theorem coeff_single_add_single_X_add_pow {B : Set ι} {wI b : ι} (hwB : wI ∉ B) (hbw : b ≠ wI)
    {L : MvPolynomial ι K} (hL : L ∈ supported K B) (e' : ℕ) :
    ((X wI + L) ^ (e' + 1)).coeff (Finsupp.single wI e' + Finsupp.single b 1) =
      (e' + 1 : K) * L.coeff (Finsupp.single b 1) := by
  have hm : (Finsupp.single wI e' + Finsupp.single b 1 : ι →₀ ℕ) wI = e' := by
    simp [hbw.symm]
  rw [add_pow, coeff_sum, Finset.sum_eq_single e']
  · have hc : (Nat.choose (e' + 1) e' : MvPolynomial ι K) = C ((e' + 1 : ℕ) : K) := by
      rw [Nat.choose_succ_self_right, map_natCast]
    have : (X wI : MvPolynomial ι K) ^ e' * L ^ (e' + 1 - e') *
        (Nat.choose (e' + 1) e' : MvPolynomial ι K) =
        monomial (Finsupp.single wI e') 1 * (C ((e' + 1 : ℕ) : K) * L) := by
      rw [Nat.add_sub_cancel_left, hc, X_pow_eq_monomial, pow_one]
      ring
    rw [this, coeff_monomial_mul']
    split_ifs with hle
    · rw [one_mul, add_tsub_cancel_left, coeff_C_mul]
      push_cast
      rfl
    · exact absurd le_self_add hle
  · intro k hk hne
    have hg : L ^ (e' + 1 - k) * (Nat.choose (e' + 1) k : MvPolynomial ι K) ∈ supported K B :=
      Subalgebra.mul_mem _ (Subalgebra.pow_mem _ hL _) (Subalgebra.natCast_mem _ _)
    have : (X wI : MvPolynomial ι K) ^ k * L ^ (e' + 1 - k) *
        (Nat.choose (e' + 1) k : MvPolynomial ι K) = monomial (Finsupp.single wI k) 1 *
          (L ^ (e' + 1 - k) * (Nat.choose (e' + 1) k : MvPolynomial ι K)) := by
      rw [X_pow_eq_monomial]
      ring
    rw [this, coeff_monomial_mul']
    split_ifs with hle
    · have hk' : k ≤ e' := by
        have := hle wI
        simpa [hm] using this
      refine mul_eq_zero_of_right _ (coeff_eq_zero_of_mem_supported hg hwB ?_)
      rw [Finsupp.tsub_apply, hm]
      simp only [Finsupp.single_eq_same]
      omega
    · rfl
  · intro h
    exact absurd (Finset.mem_range.2 (Nat.lt_succ_self _ |>.trans_le (by omega))) h

omit [DecidableEq ι] in
/-- Step 3 (the monomial `Z̄^Ā W̄^e`): the substitution fixes `X^Ā` for `Ā` supported in `zS`, so
`σ (X^(Ā + e W)) = X^Ā * (X wI + ℓ wI)^e`. -/
theorem aeval_monomial_add_single {zS : Set ι} {ℓ : ι → MvPolynomial ι K}
    (hℓz : ∀ v ∈ zS, ℓ v = 0) {Ā : ι →₀ ℕ} (hĀ : ∀ i ∉ zS, Ā i = 0) (wI : ι) (e : ℕ) :
    aeval (fun v => X v + ℓ v) (monomial (Ā + Finsupp.single wI e) (1 : K)) =
      monomial Ā 1 * (X wI + ℓ wI) ^ e := by
  have h1 : aeval (fun v => X v + ℓ v) (monomial Ā (1 : K)) = monomial Ā 1 := by
    rw [aeval_monomial, map_one, one_mul, monomial_eq, map_one, one_mul]
    refine Finsupp.prod_congr fun v hv => ?_
    have hvz : v ∈ zS := by
      by_contra h
      exact (Finsupp.mem_support_iff.1 hv) (hĀ v h)
    rw [hℓz v hvz, add_zero]
  rw [monomial_add_single, map_mul, h1, map_pow, aeval_X]

omit [DecidableEq ι] in
/-- Step 3 (the coefficient of `Z̄^Ā W̄^{e-1}` in `σ (X^(Ā + e W))`): the coefficient of
`X^Ā * X wI ^ (e - 1) * X b` in `σ (X^(Ā + e W))` is `e` times the coefficient of `X b` in
`ℓ wI`. -/
theorem coeff_aeval_monomial_add_single {B zS : Set ι} {ℓ : ι → MvPolynomial ι K}
    (hℓ : ∀ v, ℓ v ∈ supported K B) (hℓz : ∀ v ∈ zS, ℓ v = 0) {Ā : ι →₀ ℕ}
    (hĀ : ∀ i ∉ zS, Ā i = 0) {wI b : ι} (hwB : wI ∉ B) (hbw : b ≠ wI) (e' : ℕ) :
    (aeval (fun v => X v + ℓ v) (monomial (Ā + Finsupp.single wI (e' + 1)) (1 : K))).coeff
        (Ā + (Finsupp.single wI e' + Finsupp.single b 1)) =
      (e' + 1 : K) * (ℓ wI).coeff (Finsupp.single b 1) := by
  rw [aeval_monomial_add_single hℓz hĀ, coeff_monomial_mul']
  split_ifs with hle
  · rw [one_mul, add_tsub_cancel_left]
    exact coeff_single_add_single_X_add_pow hwB hbw (hℓ wI) e'
  · exact absurd le_self_add hle

end Support

universe u

/-- **"`eL = 0`, hence `L = 0`"** (p. 273, proof of (ii) of (c) of Lemma 25).  The sentence of the
paper is: "Therefore the equality `φ̄ = φ(Z̄₁, …, Z̄_r, W̄ + L, Ȳ₁, …, Ȳ_τ)` implies that
`W̄^e + λ̄₂W̄^{e−2} + ⋯ + λ̄_e = (W̄ + L)^e + λ₂(W̄ + L)^{e−2} + ⋯ + λ_e`.  It follows that `eL = 0`,
hence `L = 0`."

Pure polynomial algebra over a field `K` of characteristic `0`, in the variables `X v` (`v : ι`),
a variable being of type `A` if `isA v` (the `Z`'s, `W`, and the `Y`'s kept) and otherwise of type
`B` (the exceptional variables `Y, X₁, …, X_a`): `σ = aeval (fun v => X v + ℓ v)` is the
substitution `Z̄ ↦ Z̄`, `W̄ ↦ W̄ + L`, … by linear forms `ℓ v` in the `B`-variables, and `q = σ p`
(`p` is `φ`, `q` is `φ̄` restricted to the `A`-variables as in `exists_lift`).  The hypotheses `hp`
and `hp₀` say that the part of `p` over the monomial `Z^Ā` has the shape `c · W^e + (terms in W of
degree ≤ e - 2)` with `c ≠ 0` (the shape (4) of `f` on pp. 272--273,
`φ = ψ + cZ^Ā(W^e + λ₂W^{e−2} + ⋯ + λ_e)`), and `hq'` says that the same part of `q` has no `W^{e-1}`
term (the shape (4) of `f̄`: `W̄^e + λ̄₂W̄^{e−2} + ⋯`).  The conclusion is `L = ℓ wI = 0`.

The proof is the paper's: the coefficient of `Z̄^Ā W̄^{e-1} X_b` (`b` a `B`-variable) in `q` is, on
the one hand, `0` by `hq'`, and, on the other hand, by the substitution, `e` times
`c` times the coefficient of `X_b` in `L`; since `e ≠ 0` and `c ≠ 0`, `L` has no linear term.  The
hypothesis `hℓA` (the substitution fixes the `B`-variables) is not used. -/
theorem eq_zero_of_aeval_add_of_coeff {K : Type u} [Field K] [CharZero K] {ι : Type*} [Fintype ι]
    [DecidableEq ι] (isA : ι → Prop) [DecidablePred isA] (zS : Set ι) (wI : ι) (hwA : isA wI)
    (hwz : wI ∉ zS) (hzA : ∀ i ∈ zS, isA i)
    (ℓ : ι → MvPolynomial ι K) (hℓB : ∀ v, ℓ v ∈ linSpan (k := K) {v | ¬ isA v})
    (hℓA : ∀ v, ¬ isA v → ℓ v = 0) (hℓz : ∀ v ∈ zS, ℓ v = 0)
    (p q : MvPolynomial ι K) (hq : q = aeval (fun v => X v + ℓ v) p)
    (Ā : ι →₀ ℕ) (hĀ : ∀ i ∉ zS, Ā i = 0) (e : ℕ) (he : 0 < e)
    (hp₀ : p.coeff (Ā + Finsupp.single wI e) ≠ 0)
    (hp : ∀ m ∈ p.support, (∀ i ∈ zS, m i = Ā i) → m = Ā + Finsupp.single wI e ∨ m wI + 2 ≤ e)
    (hq' : ∀ m ∈ q.support, (∀ i ∈ zS, m i = Ā i) → m wI + 1 ≠ e) :
    ℓ wI = 0 := by
  have _ := hℓA
  obtain ⟨e', rfl⟩ : ∃ e', e = e' + 1 := ⟨e - 1, by omega⟩
  set B : Set ι := {v | ¬ isA v} with hB
  have hℓ : ∀ v, ℓ v ∈ supported K B := fun v => mem_supported_of_mem_linSpan (hℓB v)
  have hzB : ∀ i ∈ zS, i ∉ B := fun i hi hiB => hiB (hzA i hi)
  have hwB : wI ∉ B := fun h => h hwA
  have hĀwI : Ā wI = 0 := hĀ wI hwz
  -- the coefficient of `X b` in `L = ℓ wI` vanishes, for every `B`-variable `b`
  have key : ∀ b ∈ B, (ℓ wI).coeff (Finsupp.single b 1) = 0 := by
    intro b hbB
    have hbw : b ≠ wI := fun h => hwB (h ▸ hbB)
    have hbz : b ∉ zS := fun h => hzB b h hbB
    -- the monomial `Z̄^Ā W̄^{e-1} X_b`
    set m₀ : ι →₀ ℕ := Ā + Finsupp.single wI (e' + 1) with hm₀
    set m' : ι →₀ ℕ := Ā + (Finsupp.single wI e' + Finsupp.single b 1) with hm'
    have hm'z : ∀ i ∈ zS, m' i = Ā i := by
      intro i hi
      have hiw : i ≠ wI := fun h => hwz (h ▸ hi)
      have hib : i ≠ b := fun h => hbz (h ▸ hi)
      simp [m', hiw.symm, hib.symm]
    have hm'w : m' wI = e' := by
      simp [m', hĀwI, hbw.symm]
    -- by the shape of `f̄`, this coefficient of `q` vanishes
    have h0 : q.coeff m' = 0 := by
      by_contra hne
      exact hq' m' (mem_support_iff.2 hne) hm'z (by omega)
    -- the same coefficient, computed from `q = σ p`
    have hexp : q.coeff m' =
        ∑ m ∈ p.support,
          p.coeff m * (aeval (fun v => X v + ℓ v) (monomial m (1 : K))).coeff m' := by
      rw [hq]
      conv_lhs => rw [p.as_sum]
      simp only [map_sum, coeff_sum]
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [show monomial m (p.coeff m) = p.coeff m • monomial m (1 : K) by
        rw [smul_monomial, smul_eq_mul, mul_one], map_smul, coeff_smul, smul_eq_mul]
    rw [Finset.sum_eq_single m₀] at hexp
    · rw [h0, coeff_aeval_monomial_add_single hℓ hℓz hĀ hwB hbw e'] at hexp
      rcases mul_eq_zero.1 hexp.symm with h | h
      · exact absurd h hp₀
      · rcases mul_eq_zero.1 h with h | h
        · exact absurd h (Nat.cast_add_one_ne_zero e')
        · exact h
    · -- only the monomial `Z̄^Ā W̄^e` of `p` contributes
      intro m hm hne
      by_contra hcoef
      have hmem := mem_support_iff.2 (right_ne_zero_of_mul hcoef)
      have h1 : ∀ i ∈ zS, m' i = m i := fun i hi =>
        apply_eq_of_mem_support_aeval_monomial hzB hℓ hℓz m hmem hi
      have h2 := apply_le_of_mem_support_aeval_monomial hwB hℓ m hmem
      rcases hp m hm (fun i hi => ((h1 i hi).symm.trans (hm'z i hi))) with h | h
      · exact hne h
      · omega
    · intro hm
      exact absurd (notMem_support_iff.1 hm) hp₀
  -- `L = ℓ wI` is a linear form in the `B`-variables without linear term
  refine support_eq_empty.1 (Finset.eq_empty_of_forall_notMem fun m hm => ?_)
  obtain ⟨b, hb, rfl⟩ := eq_single_of_mem_support_of_mem_linSpan (hℓB wI) hm
  exact mem_support_iff.1 hm (key b hb)

end Hironaka
