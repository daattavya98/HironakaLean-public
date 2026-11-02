/-
Copyright (c) 2026 Daattavya Aggarwal, Minhyong Kim, Oisin Kim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daattavya Aggarwal, Minhyong Kim, Oisin Kim
-/
module

public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.MvPowerSeries.Equiv
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Hironaka.Compat.GenericWeierstrass
public import Hironaka.Compat.ShiftedWeierstrassPolynomial

/-!
# The choice of `w` in Lemma 25 (p. 270): Weierstrass preparation and the Tschirnhaus substitution

The coordinate part of the proof of Lemma 25 (pp. 269--270), in the power series ring
`k[[X₀, …, X_n]]` over a field of characteristic `0` (the complete regular local ring `S` of the
proof, after Cohen's structure theorem):

> "By taking a suitable linear (non-singular) transformation of `(x₁, …, x_t)` with coefficients
> in `k`, we may assume that `φ_Ā` has the term of `X₁^e` with non-zero coefficient in `k`. Then by
> the Weierstrass preparation theorem, we can write `h_Ā = u(x₁^e + p'₁x₁^{e-1} + ⋯ + p'_e)`, where
> `u` is a unit element of `S` and `p'_j ∈ S₀` […]. Since `φ_Ā` is a form in `X₁, …, X_t`, the class
> of `p'₁` in `M/M²` must be a form only in `X₂, …, X_t`, which may be zero. Therefore, we may
> replace `x₁` by `x₁ + e⁻¹p'₁` without affecting the assumption that `(x₁, …, x_t)` is a regular
> system of `τ_{(z)}`-parameters of `R` for `f`. Thus we may assume that
> `h_Ā = u(x₁^e + p₂x₁^{e-2} + ⋯ + p_e)`."

`exists_weierstrass_coordinates`: if the leading form of `g` (of degree `e ≥ 1`) involves only the
variables `X_i`, `i < t`, there is an automorphism `ψ` of `k[[X]]` (with inverse `ψ'`) taking `g`
to `u (X₀^e + p₂ X₀^{e-2} + ⋯ + p_e)` with `p_j ∈ k[[X₁, …, X_n]]`, such that `ψ'(X₀)` has no
constant term and no linear term in the variables `X_i`, `i ≥ t` (so the new coordinate `ψ'(X₀)`
has its class in the span of `X₀, …, X_{t-1}`).

The "suitable linear transformation" is carried out as printed, on `(x₁, …, x_t)` alone
(`X₀, …, X_{t-1}` here): it is the shift `X_{j+1} ↦ X_{j+1} + c_j X₀` (`genericShift c` of
`Compat/GenericWeierstrass.lean`) with `c_j ∈ k` and `c_j = 0` for `j + 1 ≥ t`, a non-singular
(unitriangular) linear transformation of `(x₁, …, x_t)` with coefficients in `k`.  The coefficients
are chosen by `exists_point_of_suppLt`: the form `φ_Ā` is non-zero and involves only
`X₀, …, X_{t-1}`, so it does not vanish at some point `(1, c)` with `c_j = 0` for `j + 1 ≥ t`
(`k` is infinite); then the coefficient of `X₀^e` of the shifted form is `φ_Ā(1, c) ≠ 0`
("`φ_Ā` has the term of `X₁^e` with non-zero coefficient in `k`").  The Weierstrass preparation
theorem is Mathlib's (`exists_weierstrass_form`, used in `exists_shift_weierstrass_form`); the
Tschirnhaus step is `tschirnhaus`, and the vanishing of the linear part of `p'₁` outside
`X₁, …, X_{t-1}` is proved by comparing the monomials `X₀^{e-1} X_j` in the leading forms
(`coeff_genericShift_eq_zero_of_suppLt`).
-/

@[expose] public section

open IsLocalRing MvPowerSeries

namespace Hironaka

universe u

section Tail

variable {k : Type u} [Field k] {n : ℕ}

theorem coeff_cons_coeffRingInclusion_eq_ite (a : MvPowerSeries (Fin n) k) (j : ℕ)
    (x : Fin n →₀ ℕ) :
    coeff (Finsupp.cons j x) (coeffRingInclusion k n a) = if j = 0 then coeff x a else 0 := by
  have h := MvPowerSeries.coeff_coeff_finSuccEquiv (coeffRingInclusion k n a) (k := j) (x := x)
  have h2 : MvPowerSeries.finSuccEquiv k n (coeffRingInclusion k n a) = PowerSeries.C a := by
    simp [coeffRingInclusion]
  rw [h2] at h
  rw [← h]
  rw [PowerSeries.coeff_C]
  split_ifs <;> simp

theorem coeffRingInclusion_eq_rename (a : MvPowerSeries (Fin n) k) :
    coeffRingInclusion k n a = rename Fin.succ a := by
  ext d
  obtain ⟨j, x, rfl⟩ : ∃ j x, d = Finsupp.cons j x :=
    ⟨d 0, Finsupp.tail d, (Finsupp.cons_tail d).symm⟩
  rw [coeff_cons_coeffRingInclusion_eq_ite]
  split_ifs with hj
  · subst hj
    have h : Finsupp.cons 0 x = Finsupp.embDomain ⟨Fin.succ, Fin.succ_injective n⟩ x := by
      ext i
      refine Fin.cases ?_ (fun i => ?_) i
      · rw [Finsupp.cons_zero]
        exact (Finsupp.embDomain_of_notMem_range _ _ _ (by
          rintro ⟨y, hy⟩
          exact Fin.succ_ne_zero y hy)).symm
      · rw [Finsupp.cons_succ]
        exact (Finsupp.embDomain_apply_self ⟨Fin.succ, Fin.succ_injective n⟩ x i).symm
    rw [h]
    exact (coeff_embDomain_rename ⟨Fin.succ, Fin.succ_injective n⟩ a x).symm
  · refine (coeff_rename_eq_zero _ a ?_).symm
    rintro ⟨y, hy⟩
    have := congrArg (fun f => f 0) hy
    simp only [Finsupp.cons_zero] at this
    rw [Finsupp.mapDomain_of_notMem_range _ _
      (by rintro ⟨i, hi⟩; exact Fin.succ_ne_zero i hi)] at this
    exact hj this.symm

end Tail

section Support

variable {k : Type u} [Field k] {n : ℕ}

/-- `f` involves only the variables `X_i`, `i < t`. -/
def SuppLt (t : ℕ) (f : MvPowerSeries (Fin (n + 1)) k) : Prop :=
  ∀ d, coeff d f ≠ 0 → ∀ i : Fin (n + 1), t ≤ (i : ℕ) → d i = 0

theorem SuppLt.mul {t : ℕ} {f g : MvPowerSeries (Fin (n + 1)) k} (hf : SuppLt t f)
    (hg : SuppLt t g) : SuppLt t (f * g) := by
  intro d hd i hi
  rw [coeff_mul] at hd
  obtain ⟨p, hp, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hd
  have h1 : coeff p.1 f ≠ 0 := left_ne_zero_of_mul hne
  have h2 : coeff p.2 g ≠ 0 := right_ne_zero_of_mul hne
  have := Finset.HasAntidiagonal.mem_antidiagonal.mp hp
  rw [← this, Finsupp.add_apply, hf p.1 h1 i hi, hg p.2 h2 i hi]

theorem SuppLt.one {t : ℕ} : SuppLt t (1 : MvPowerSeries (Fin (n + 1)) k) := by
  intro d hd i _
  by_cases h : d = 0
  · simp [h]
  · simp [coeff_one, h] at hd

theorem SuppLt.pow {t : ℕ} {f : MvPowerSeries (Fin (n + 1)) k} (hf : SuppLt t f) (m : ℕ) :
    SuppLt t (f ^ m) := by
  induction m with
  | zero => rw [pow_zero]; exact SuppLt.one
  | succ m ih => rw [pow_succ]; exact ih.mul hf

theorem SuppLt.prod {t : ℕ} {ι : Type*} (s : Finset ι) (f : ι → MvPowerSeries (Fin (n + 1)) k)
    (h : ∀ i ∈ s, SuppLt t (f i)) : SuppLt t (∏ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.prod_empty]; exact SuppLt.one
  | insert a s ha ih =>
    rw [Finset.prod_insert ha]
    exact (h a (Finset.mem_insert_self _ _)).mul
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem SuppLt.add {t : ℕ} {f g : MvPowerSeries (Fin (n + 1)) k} (hf : SuppLt t f)
    (hg : SuppLt t g) : SuppLt t (f + g) := by
  intro d hd i hi
  rw [map_add] at hd
  by_cases h1 : coeff d f = 0
  · rw [h1, zero_add] at hd
    exact hg d hd i hi
  · exact hf d h1 i hi

theorem SuppLt.C_mul {t : ℕ} (c : k) {f : MvPowerSeries (Fin (n + 1)) k} (hf : SuppLt t f) :
    SuppLt t (MvPowerSeries.C c * f) := by
  intro d hd i hi
  rw [coeff_C_mul] at hd
  exact hf d (right_ne_zero_of_mul hd) i hi

theorem SuppLt.X {t : ℕ} (s : Fin (n + 1)) (hs : (s : ℕ) < t) :
    SuppLt t (MvPowerSeries.X s : MvPowerSeries (Fin (n + 1)) k) := by
  intro d hd i hi
  rw [coeff_X] at hd
  by_cases h : d = Finsupp.single s 1
  · rw [h]
    have : s ≠ i := fun hsi => by rw [hsi] at hs; omega
    simp [this]
  · simp [h] at hd

/-- The substitution data of `genericShift c` are supported on the variables `< t` as soon as the
variable itself is (`X₀ ↦ X₀`, `X_{j+1} ↦ X_{j+1} + c_j X₀`). -/
theorem suppLt_genericShiftData {t : ℕ} (ht : 1 ≤ t) (c : Fin n → k) (s : Fin (n + 1))
    (hs : (s : ℕ) < t) : SuppLt t (genericShiftData c s) := by
  induction s using Fin.cases with
  | zero =>
    rw [genericShiftData_zero]
    exact SuppLt.X 0 (by show (0 : ℕ) < t; omega)
  | succ j =>
    rw [genericShiftData_succ]
    exact (SuppLt.X (k := k) (n := n) j.succ hs).add
      (SuppLt.C_mul _ (SuppLt.X (k := k) (n := n) 0 (by show (0 : ℕ) < t; omega)))

end Support

section LeadingForm

variable {k : Type u} [Field k] {n : ℕ}

/-- **The generic shift does not create the variables outside the support of the leading form**:
if every monomial of degree `e` of `g` involves only `X_i`, `i < t`, and `g` has order `≥ e`, then
the degree-`e` monomials of `genericShift c g` which involve an `X_i`, `i ≥ t`, have coefficient
zero. -/
theorem coeff_genericShift_eq_zero_of_suppLt {t : ℕ} (ht : 1 ≤ t) (c : Fin n → k)
    {g : MvPowerSeries (Fin (n + 1)) k} {e : ℕ} (hord : (e : ℕ∞) ≤ g.order)
    (hsupp : ∀ d' : Fin (n + 1) →₀ ℕ, d'.degree = e → coeff d' g ≠ 0 →
      ∀ i : Fin (n + 1), t ≤ (i : ℕ) → d' i = 0)
    (d : Fin (n + 1) →₀ ℕ) (hd : d.degree = e) (i0 : Fin (n + 1)) (hi0 : t ≤ (i0 : ℕ))
    (hdi : d i0 ≠ 0) : coeff d (genericShift c g) = 0 := by
  rw [genericShift_apply, coeff_subst (hasSubst_genericShiftData c)]
  refine finsum_eq_zero_of_forall_eq_zero fun d' => ?_
  by_cases h0 : coeff d' g = 0
  · simp [h0]
  have h1 : (e : ℕ∞) ≤ d'.degree := hord.trans (MvPowerSeries.order_le h0)
  have h1' : e ≤ d'.degree := by exact_mod_cast h1
  have h2 := le_order_prod_pow (constantCoeff_genericShiftData c) d'
  rcases h1'.lt_or_eq with hlt | heq
  · rw [MvPowerSeries.coeff_of_lt_order (lt_of_lt_of_le (by rw [hd]; exact_mod_cast hlt) h2),
      smul_zero]
  · have hs := hsupp d' heq.symm h0
    have hprod : SuppLt t (d'.prod fun s e => genericShiftData c s ^ e) := by
      unfold Finsupp.prod
      refine SuppLt.prod _ _ fun s hs' => SuppLt.pow ?_ _
      have hst : (s : ℕ) < t := by
        by_contra hcon
        push Not at hcon
        exact (Finsupp.mem_support_iff.mp hs') (hs s hcon)
      exact suppLt_genericShiftData ht c s hst
    have : coeff d (d'.prod fun s e => genericShiftData c s ^ e) = 0 := by
      by_contra hne
      exact hdi (hprod d hne i0 hi0)
    rw [this, smul_zero]

end LeadingForm

section Linear

variable {k : Type u} [Field k] {n : ℕ}

theorem exists_eq_single_one_of_degree_eq_one {σ : Type*} (d : σ →₀ ℕ) (h : d.degree = 1) :
    ∃ s, d = Finsupp.single s 1 := by
  classical
  have hd0 : d ≠ 0 := by
    rintro rfl
    simp at h
  obtain ⟨s, hs⟩ : ∃ s, d s ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hd0 (Finsupp.ext hcon)
  have hle := Finsupp.le_degree s d
  rw [h] at hle
  have hds : d s = 1 := by omega
  refine ⟨s, ?_⟩
  have hsum := Finsupp.single_add_erase s d
  have hdeg : (Finsupp.single s (d s) + Finsupp.erase s d).degree = 1 := by rw [hsum]; exact h
  rw [map_add, Finsupp.degree_single, hds] at hdeg
  have : (Finsupp.erase s d).degree = 0 := by omega
  rw [Finsupp.degree_eq_zero_iff] at this
  rw [← hsum, this, add_zero, hds]

/-- The generic shift does not change the coefficients of the variables `X_{j+1}` in the linear
part. -/
theorem coeff_single_succ_genericShift (c : Fin n → k) {f : MvPowerSeries (Fin (n + 1)) k}
    (hf : constantCoeff f = 0) (j : Fin n) :
    coeff (Finsupp.single j.succ 1) (genericShift c f) =
      coeff (Finsupp.single j.succ 1) f := by
  classical
  rw [genericShift_apply, coeff_subst (hasSubst_genericShiftData c)]
  rw [finsum_eq_single _ (Finsupp.single j.succ 1)]
  · rw [Finsupp.prod_single_index (by simp), pow_one, genericShiftData_succ]
    simp [coeff_X, coeff_C_mul, Finsupp.single_eq_single_iff]
  · intro d hd
    by_cases h0 : coeff d f = 0
    · simp [h0]
    have hd0 : d ≠ 0 := by
      rintro rfl
      rw [coeff_zero_eq_constantCoeff_apply] at h0
      exact h0 hf
    have h2 := le_order_prod_pow (constantCoeff_genericShiftData c) d
    by_cases hdeg : d.degree = 1
    · obtain ⟨s, rfl⟩ := exists_eq_single_one_of_degree_eq_one d hdeg
      have hs : s ≠ j.succ := fun h => hd (by rw [h])
      rw [Finsupp.prod_single_index (by simp), pow_one]
      have : coeff (Finsupp.single j.succ 1) (genericShiftData c s) = 0 := by
        induction s using Fin.cases with
        | zero =>
          rw [genericShiftData_zero, coeff_X]
          simp [Finsupp.single_eq_single_iff]
        | succ s' =>
          rw [genericShiftData_succ]
          have hs' : s' ≠ j := fun h => hs (by rw [h])
          simp [coeff_X, coeff_C_mul, Finsupp.single_eq_single_iff, Ne.symm hs']
      rw [this, smul_zero]
    · have hdeg2 : 2 ≤ d.degree := by
        have : d.degree ≠ 0 := fun h => hd0 ((Finsupp.degree_eq_zero_iff d).mp h)
        omega
      rw [MvPowerSeries.coeff_of_lt_order (lt_of_lt_of_le (by
        rw [Finsupp.degree_single]; exact_mod_cast (show 1 < d.degree by omega)) h2), smul_zero]

end Linear

section WCoeff

variable {k : Type u} [Field k] {n : ℕ}

theorem le_order_rename_succ (a : MvPowerSeries (Fin n) k) :
    a.order ≤ (rename Fin.succ a : MvPowerSeries (Fin (n + 1)) k).order := by
  refine MvPowerSeries.le_order fun d hd => ?_
  rw [coeff_rename]
  refine Finset.sum_eq_zero fun x hx => ?_
  have hx' : Finsupp.mapDomain Fin.succ x = d := by
    simpa using (Set.Finite.mem_toFinset
      (Filter.TendstoCofinite.finite_preimage_singleton (Finsupp.mapDomain Fin.succ) d)).mp hx
  have hdeg : x.degree = d.degree := by rw [← hx', Finsupp.degree_mapDomain]
  exact coeff_of_lt_order (by rw [hdeg]; exact hd)

/-- `W = X₀ᵉ + ∑ₗ a_l X₀^{e-l-1}` with `a_l ∈ k[[X₁, …, X_n]]`. -/
noncomputable def weierstrassSeries (e : ℕ) (a : Fin e → MvPowerSeries (Fin n) k) :
    MvPowerSeries (Fin (n + 1)) k :=
  X 0 ^ e + ∑ l : Fin e, rename Fin.succ (a l) * X 0 ^ (e - ((l : ℕ) + 1))

theorem le_order_weierstrassSeries (e : ℕ) (a : Fin e → MvPowerSeries (Fin n) k)
    (ha : ∀ l : Fin e, (((l : ℕ) + 1 : ℕ) : ℕ∞) ≤ (a l).order) :
    (e : ℕ∞) ≤ (weierstrassSeries e a).order := by
  refine MvPowerSeries.le_order fun d hd => ?_
  unfold weierstrassSeries
  rw [map_add, map_sum]
  have h0 : (e : ℕ∞) ≤ (X 0 ^ e : MvPowerSeries (Fin (n + 1)) k).order :=
    le_order_pow_of_constantCoeff_eq_zero e (by simp)
  rw [coeff_of_lt_order (lt_of_lt_of_le hd h0), zero_add]
  refine Finset.sum_eq_zero fun l _ => ?_
  have h1 : (((l : ℕ) + 1 : ℕ) : ℕ∞) ≤ (rename Fin.succ (a l) :
      MvPowerSeries (Fin (n + 1)) k).order := (ha l).trans (le_order_rename_succ _)
  have h2 : ((e - ((l : ℕ) + 1) : ℕ) : ℕ∞) ≤ (X 0 ^ (e - ((l : ℕ) + 1)) :
      MvPowerSeries (Fin (n + 1)) k).order :=
    le_order_pow_of_constantCoeff_eq_zero _ (by simp)
  have h3 := le_order_mul (f := (rename Fin.succ (a l) : MvPowerSeries (Fin (n + 1)) k))
    (g := X 0 ^ (e - ((l : ℕ) + 1)))
  have h4 : (e : ℕ∞) ≤ (((l : ℕ) + 1 : ℕ) : ℕ∞) + ((e - ((l : ℕ) + 1) : ℕ) : ℕ∞) := by
    have : ((l : ℕ) + 1) + (e - ((l : ℕ) + 1)) = e := by have := l.2; omega
    rw [← Nat.cast_add, this]
  exact coeff_of_lt_order (lt_of_lt_of_le hd (h4.trans ((add_le_add h1 h2).trans h3)))

/-- The coefficient of `X₀^p · x` in `a(X₁, …) · X₀^m` (`m ≤ p`). -/
theorem coeff_cons_rename_mul_X_zero_pow (a : MvPowerSeries (Fin n) k) (m p : ℕ)
    (hmp : m ≤ p) (x : Fin n →₀ ℕ) :
    coeff (Finsupp.cons p x) (rename Fin.succ a * X 0 ^ m : MvPowerSeries (Fin (n + 1)) k) =
      if p = m then coeff x a else 0 := by
  classical
  rw [X_pow_eq]
  have hsplit : Finsupp.cons p x = Finsupp.cons (p - m) x + Finsupp.single 0 m := by
    ext i
    refine Fin.cases ?_ (fun i => ?_) i
    · simp; omega
    · simp
  rw [hsplit, coeff_add_mul_monomial, mul_one, ← coeffRingInclusion_eq_rename,
    coeff_cons_coeffRingInclusion_eq_ite]
  by_cases h : p = m
  · simp [h]
  · simp [h, show p - m ≠ 0 by omega]

/-- The coefficient of `X₀^{e-1} X_{j+1}` in the Weierstrass series is the linear coefficient of
`a₁`, the coefficient of `X₀^{e-1}`. -/
theorem coeff_weierstrassSeries_cons (e : ℕ) (he : 0 < e) (a : Fin e → MvPowerSeries (Fin n) k)
    (j : Fin n) :
    coeff (Finsupp.cons (e - 1) (Finsupp.single j 1)) (weierstrassSeries e a) =
      coeff (Finsupp.single j 1) (a ⟨0, he⟩) := by
  classical
  unfold weierstrassSeries
  rw [map_add, map_sum]
  have h0 : coeff (Finsupp.cons (e - 1) (Finsupp.single j 1)) (X 0 ^ e :
      MvPowerSeries (Fin (n + 1)) k) = 0 := by
    rw [X_pow_eq, coeff_monomial]
    have hne : Finsupp.cons (e - 1) (Finsupp.single j 1) ≠ Finsupp.single (0 : Fin (n + 1)) e := by
      intro h
      have := congrArg (fun f => f j.succ) h
      simp at this
    simp [hne]
  rw [h0, zero_add, Finset.sum_eq_single (⟨0, he⟩ : Fin e)]
  · rw [coeff_cons_rename_mul_X_zero_pow _ _ _ (by simp)]
    simp
  · intro l _ hl
    have hl0 : (l : ℕ) ≠ 0 := fun h => hl (Fin.ext h)
    rw [coeff_cons_rename_mul_X_zero_pow _ _ _ (by have := l.2; omega)]
    have : ¬ (e - 1 = e - ((l : ℕ) + 1)) := by have := l.2; omega
    simp [this]
  · intro h; exact absurd (Finset.mem_univ _) h

end WCoeff

section Tschirnhaus

variable {k : Type u} [Field k] {n : ℕ}

/-- Substitution data `X₀ ↦ X₀ - b`, `X_{j+1} ↦ X_{j+1}`. -/
noncomputable def tschirnhausData (b : MvPowerSeries (Fin (n + 1)) k) :
    Fin (n + 1) → MvPowerSeries (Fin (n + 1)) k :=
  Fin.cons (X 0 - b) (fun j => X j.succ)

theorem constantCoeff_tschirnhausData {b : MvPowerSeries (Fin (n + 1)) k}
    (hb : constantCoeff b = 0) (s : Fin (n + 1)) : constantCoeff (tschirnhausData b s) = 0 := by
  refine Fin.cases ?_ (fun j => ?_) s <;> simp [tschirnhausData, hb]

theorem hasSubst_tschirnhausData {b : MvPowerSeries (Fin (n + 1)) k} (hb : constantCoeff b = 0) :
    HasSubst (tschirnhausData b) :=
  hasSubst_of_constantCoeff_zero (constantCoeff_tschirnhausData hb)

theorem constantCoeff_rename_succ_eq_zero {b : MvPowerSeries (Fin n) k}
    (hb : constantCoeff b = 0) :
    constantCoeff (rename Fin.succ b : MvPowerSeries (Fin (n + 1)) k) = 0 := by
  rw [constantCoeff_rename, hb]

/-- The Tschirnhaus substitution `X₀ ↦ X₀ - b`, for `b ∈ k[[X₁, …, X_n]]` without constant term. -/
noncomputable def tschirnhaus (b : MvPowerSeries (Fin n) k) (hb : constantCoeff b = 0) :
    MvPowerSeries (Fin (n + 1)) k →ₐ[k] MvPowerSeries (Fin (n + 1)) k :=
  substAlgHom (hasSubst_tschirnhausData (constantCoeff_rename_succ_eq_zero hb))

theorem tschirnhaus_X_zero (b : MvPowerSeries (Fin n) k) (hb : constantCoeff b = 0) :
    tschirnhaus b hb (X 0) = X 0 - rename Fin.succ b := by
  rw [tschirnhaus, substAlgHom_X]
  simp [tschirnhausData]

theorem tschirnhaus_X_succ (b : MvPowerSeries (Fin n) k) (hb : constantCoeff b = 0) (j : Fin n) :
    tschirnhaus b hb (X j.succ) = X j.succ := by
  rw [tschirnhaus, substAlgHom_X]
  simp [tschirnhausData]

theorem tschirnhaus_rename (b : MvPowerSeries (Fin n) k) (hb : constantCoeff b = 0)
    (a : MvPowerSeries (Fin n) k) : tschirnhaus b hb (rename Fin.succ a) = rename Fin.succ a := by
  have hs := hasSubst_tschirnhausData (constantCoeff_rename_succ_eq_zero hb)
  rw [rename_eq_subst, tschirnhaus, substAlgHom_apply,
    subst_comp_subst_apply (HasSubst.X_comp _) hs]
  congr 1
  funext s
  rw [Function.comp_apply, subst_X hs]
  simp [tschirnhausData]

theorem tschirnhaus_neg_tschirnhaus (b : MvPowerSeries (Fin n) k) (hb : constantCoeff b = 0)
    (f : MvPowerSeries (Fin (n + 1)) k) :
    tschirnhaus (-b) (by simp [hb]) (tschirnhaus b hb f) = f := by
  have hb' : constantCoeff (-b) = 0 := by simp [hb]
  have h1 := hasSubst_tschirnhausData (constantCoeff_rename_succ_eq_zero hb)
  have h2 := hasSubst_tschirnhausData (constantCoeff_rename_succ_eq_zero hb')
  unfold tschirnhaus
  rw [substAlgHom_comp_substAlgHom_apply]
  have : (fun s => substAlgHom h2 (tschirnhausData (rename Fin.succ b) s)) =
      (X : Fin (n + 1) → MvPowerSeries (Fin (n + 1)) k) := by
    funext s
    refine Fin.cases ?_ (fun j => ?_) s
    · have := tschirnhaus_X_zero (-b) hb'
      have h3 := tschirnhaus_rename (-b) hb' b
      simp only [tschirnhausData, Fin.cons_zero, map_sub]
      change tschirnhaus (-b) hb' (X 0) - tschirnhaus (-b) hb' (rename Fin.succ b) = X 0
      rw [tschirnhaus_X_zero, h3, map_neg]
      ring
    · simp only [tschirnhausData, Fin.cons_succ]
      exact tschirnhaus_X_succ (-b) hb' j
  rw [substAlgHom_apply, this, subst_self]
  rfl

end Tschirnhaus

section Assembly

variable {k : Type u} [Field k] {n : ℕ}

theorem tschirnhaus_congr {b b' : MvPowerSeries (Fin n) k} (h : b = b')
    (hb : constantCoeff b = 0) (hb' : constantCoeff b' = 0) :
    tschirnhaus b hb = tschirnhaus b' hb' := by
  subst h
  rfl

theorem tschirnhaus_tschirnhaus_neg (b : MvPowerSeries (Fin n) k) (hb : constantCoeff b = 0)
    (f : MvPowerSeries (Fin (n + 1)) k) :
    tschirnhaus b hb (tschirnhaus (-b) (by simp [hb]) f) = f := by
  have hb' : constantCoeff (-b) = 0 := by simp [hb]
  have := tschirnhaus_neg_tschirnhaus (-b) hb' f
  rwa [tschirnhaus_congr (neg_neg b) (by simp [hb]) hb] at this

theorem genericShift_genericShift_neg (c : Fin n → k) (f : MvPowerSeries (Fin (n + 1)) k) :
    genericShift c (genericShift (-c) f) = f := by
  have := genericShift_neg_genericShift (-c) f
  rwa [neg_neg] at this

theorem genericShift_X_zero (c : Fin n → k) :
    genericShift c (X 0 : MvPowerSeries (Fin (n + 1)) k) = X 0 := by
  rw [genericShift_apply, subst_X (hasSubst_genericShiftData c), genericShiftData_zero]

/-- The coefficient of a monomial of degree `e` in `u · W`, for `W` of order `≥ e`, is the constant
coefficient of `u` times that of `W`. -/
theorem coeff_mul_of_le_order (u W : MvPowerSeries (Fin (n + 1)) k) {e : ℕ}
    (hW : (e : ℕ∞) ≤ W.order) (d : Fin (n + 1) →₀ ℕ) (hd : d.degree = e) :
    coeff d (u * W) = constantCoeff u * coeff d W := by
  have h1 : u = MvPowerSeries.C (constantCoeff u) + (u - MvPowerSeries.C (constantCoeff u)) := by
    ring
  have h2 : 1 ≤ (u - MvPowerSeries.C (constantCoeff u)).order := by
    rw [one_le_order_iff_constCoeff_eq_zero]
    simp
  have h3 := le_order_mul (f := u - MvPowerSeries.C (constantCoeff u)) (g := W)
  have h4 : coeff d ((u - MvPowerSeries.C (constantCoeff u)) * W) = 0 := by
    refine coeff_of_lt_order (lt_of_lt_of_le ?_ (((add_le_add h2 hW)).trans h3))
    rw [hd]
    have : (e : ℕ∞) < 1 + (e : ℕ∞) := by
      rw [add_comm]
      exact ENat.lt_add_one_iff (ENat.natCast_ne_top e) |>.mpr le_rfl
    exact this
  conv_lhs => rw [h1, add_mul, map_add, h4, add_zero, coeff_C_mul]

theorem tschirnhaus_weierstrassSeries (ν : ℕ) (a : Fin ν → MvPowerSeries (Fin n) k)
    (b : MvPowerSeries (Fin n) k) (hb : constantCoeff b = 0) :
    tschirnhaus b hb (weierstrassSeries ν a) =
      Polynomial.eval₂ (rename Fin.succ : MvPowerSeries (Fin n) k →ₐ[k]
        MvPowerSeries (Fin (n + 1)) k).toRingHom (X 0) (shiftedWeierstrass ν a b) := by
  unfold weierstrassSeries shiftedWeierstrass
  simp only [map_add, map_sum, map_mul, map_pow, tschirnhaus_rename, tschirnhaus_X_zero,
    Polynomial.eval₂_add, Polynomial.eval₂_pow, Polynomial.eval₂_X, Polynomial.eval₂_finsetSum,
    Polynomial.eval₂_mul, Polynomial.eval₂_C]
  simp only [map_neg, sub_eq_add_neg]
  rfl

/-- The distinguished polynomial after the Tschirnhaus transformation, as a power series. -/
theorem eval₂_shiftedWeierstrass_eq (ν : ℕ) (hν : 0 < ν) (a : Fin ν → MvPowerSeries (Fin n) k)
    (b : MvPowerSeries (Fin n) k) (hbe : (ν : MvPowerSeries (Fin n) k) * b = a ⟨0, hν⟩) :
    Polynomial.eval₂ (rename Fin.succ : MvPowerSeries (Fin n) k →ₐ[k]
        MvPowerSeries (Fin (n + 1)) k).toRingHom (X 0) (shiftedWeierstrass ν a b) =
      X 0 ^ ν + ∑ j ∈ Finset.Icc 2 ν,
        rename Fin.succ ((shiftedWeierstrass ν a b).coeff (ν - j)) * X 0 ^ (ν - j) := by
  have hQ := shiftedWeierstrass_eq ν hν a b hbe
  conv_lhs => rw [hQ]
  simp only [Polynomial.eval₂_add, Polynomial.eval₂_pow, Polynomial.eval₂_X,
    Polynomial.eval₂_finsetSum, Polynomial.eval₂_mul, Polynomial.eval₂_C]
  rfl

/-- The core of the choice of `w` (p. 270), once the Weierstrass preparation of the shifted
series has been performed. -/
theorem exists_weierstrass_coordinates_aux [CharZero k] {t : ℕ} (ht : 1 ≤ t)
    (g : MvPowerSeries (Fin (n + 1)) k) (ν : ℕ) (he : 0 < ν) (hordg : (ν : ℕ∞) ≤ g.order)
    (hsupp : ∀ d : Fin (n + 1) →₀ ℕ, d.degree = ν → coeff d g ≠ 0 →
      ∀ i : Fin (n + 1), t ≤ (i : ℕ) → d i = 0)
    (c : Fin n → k) (u : (MvPowerSeries (Fin (n + 1)) k)ˣ) (a : Fin ν → MvPowerSeries (Fin n) k)
    (hshift : genericShift c g = (u : MvPowerSeries (Fin (n + 1)) k) *
      (X 0 ^ ν + ∑ l : Fin ν, coeffRingInclusion k n (a l) * X 0 ^ (ν - ((l : ℕ) + 1))))
    (hord : ∀ l : Fin ν, (((l : ℕ) + 1 : ℕ) : ℕ∞) ≤ (a l).order) :
    ∃ (ψ ψ' : MvPowerSeries (Fin (n + 1)) k →ₐ[k] MvPowerSeries (Fin (n + 1)) k)
      (u' : (MvPowerSeries (Fin (n + 1)) k)ˣ) (p : ℕ → MvPowerSeries (Fin n) k),
      (∀ f, ψ' (ψ f) = f) ∧ (∀ f, ψ (ψ' f) = f) ∧
      ψ g = (u' : MvPowerSeries (Fin (n + 1)) k) *
        (X 0 ^ ν + ∑ j ∈ Finset.Icc 2 ν, rename Fin.succ (p j) * X 0 ^ (ν - j)) ∧
      constantCoeff (ψ' (X 0)) = 0 ∧
      ∀ i : Fin (n + 1), t ≤ (i : ℕ) → coeff (Finsupp.single i 1) (ψ' (X 0)) = 0 := by
  classical
  have hW : genericShift c g = (u : MvPowerSeries (Fin (n + 1)) k) * weierstrassSeries ν a := by
    rw [hshift]
    simp only [weierstrassSeries, coeffRingInclusion_eq_rename]
  have ha0 : 1 ≤ (a ⟨0, he⟩).order := by simpa using hord ⟨0, he⟩
  have hcc0 : constantCoeff (a ⟨0, he⟩) = 0 := (one_le_order_iff_constCoeff_eq_zero).mp ha0
  have hνk : (ν : k) ≠ 0 := Nat.cast_ne_zero.mpr he.ne'
  obtain ⟨b, hbdef⟩ : ∃ b : MvPowerSeries (Fin n) k,
      b = MvPowerSeries.C ((ν : k)⁻¹) * a ⟨0, he⟩ := ⟨_, rfl⟩
  have hb0 : constantCoeff b = 0 := by simp [hbdef, hcc0]
  have hbe : (ν : MvPowerSeries (Fin n) k) * b = a ⟨0, he⟩ := by
    rw [hbdef, ← mul_assoc]
    have : (ν : MvPowerSeries (Fin n) k) * MvPowerSeries.C ((ν : k)⁻¹) = 1 := by
      rw [← map_natCast (MvPowerSeries.C (σ := Fin n) (R := k)), ← map_mul,
        mul_inv_cancel₀ hνk, map_one]
    rw [this, one_mul]
  have hb0' : constantCoeff (-b) = 0 := by simp [hb0]
  have hrb0 : constantCoeff (rename Fin.succ b : MvPowerSeries (Fin (n + 1)) k) = 0 :=
    constantCoeff_rename_succ_eq_zero hb0
  have hψ'X : (genericShift (-c)).comp (tschirnhaus (-b) hb0') (X 0) =
      X 0 + genericShift (-c) (rename Fin.succ b) := by
    simp only [AlgHom.comp_apply]
    rw [tschirnhaus_X_zero, map_neg, sub_neg_eq_add, map_add, genericShift_X_zero]
  refine ⟨(tschirnhaus b hb0).comp (genericShift c), (genericShift (-c)).comp
    (tschirnhaus (-b) hb0'), Units.map (tschirnhaus b hb0 : _ →* _) u,
    fun j => (shiftedWeierstrass ν a b).coeff (ν - j), ?_, ?_, ?_, ?_, ?_⟩
  · intro f
    simp only [AlgHom.comp_apply]
    rw [tschirnhaus_neg_tschirnhaus, genericShift_neg_genericShift]
  · intro f
    simp only [AlgHom.comp_apply]
    rw [genericShift_genericShift_neg, tschirnhaus_tschirnhaus_neg]
  · simp only [AlgHom.comp_apply]
    rw [hW, map_mul, tschirnhaus_weierstrassSeries, eval₂_shiftedWeierstrass_eq ν he a b hbe,
      Units.coe_map]
    rfl
  · rw [hψ'X, map_add, constantCoeff_X, zero_add, genericShift_apply]
    exact constantCoeff_subst_eq_zero (hasSubst_genericShiftData _)
      (constantCoeff_genericShiftData _) hrb0
  · intro i hi
    have hi0 : i ≠ 0 := by
      intro h
      rw [h] at hi
      simp at hi
      omega
    obtain ⟨j, rfl⟩ := Fin.exists_succ_eq.mpr hi0
    rw [hψ'X, map_add, coeff_single_succ_genericShift (-c) hrb0 j]
    have h1 : coeff (Finsupp.single j.succ 1) (X 0 : MvPowerSeries (Fin (n + 1)) k) = 0 := by
      rw [coeff_X]
      have hne : Finsupp.single j.succ 1 ≠ Finsupp.single (0 : Fin (n + 1)) 1 := by
        intro h
        have := congrArg (fun f => f j.succ) h
        simp at this
      simp [hne]
    have h2 : coeff (Finsupp.single j.succ 1) (rename Fin.succ b : MvPowerSeries (Fin (n + 1)) k) =
        coeff (Finsupp.single j 1) b := by
      have : Finsupp.single j.succ 1 =
          Finsupp.embDomain ⟨Fin.succ, Fin.succ_injective n⟩ (Finsupp.single j 1) := by
        rw [Finsupp.embDomain_single]
        rfl
      rw [this]
      exact coeff_embDomain_rename ⟨Fin.succ, Fin.succ_injective n⟩ b _
    have hα : coeff (Finsupp.single j 1) (a ⟨0, he⟩) = 0 := by
      set d : Fin (n + 1) →₀ ℕ := Finsupp.cons (ν - 1) (Finsupp.single j 1) with hd
      have hdeg : d.degree = ν := by
        rw [hd, degree_cons, Finsupp.degree_single]
        omega
      have hdj : d j.succ ≠ 0 := by simp [hd]
      have h0 := coeff_genericShift_eq_zero_of_suppLt ht c hordg hsupp d hdeg j.succ hi hdj
      have hWord : (ν : ℕ∞) ≤ (weierstrassSeries ν a).order := le_order_weierstrassSeries ν a hord
      rw [hW, coeff_mul_of_le_order _ _ hWord d hdeg, coeff_weierstrassSeries_cons ν he a j]
        at h0
      have hu0 : constantCoeff (u : MvPowerSeries (Fin (n + 1)) k) ≠ 0 :=
        ((MvPowerSeries.isUnit_iff_constantCoeff).mp u.isUnit).ne_zero
      exact (mul_eq_zero.mp h0).resolve_left hu0
    rw [h1, h2, zero_add, hbdef, coeff_C_mul, hα, mul_zero]

/-- **"A suitable linear (non-singular) transformation of `(x₁, …, x_t)` with coefficients in `k`"**
(p. 270), the choice of the coefficients: a non-zero homogeneous polynomial `F` of degree `e` in
`X₀, …, X_{t-1}` does not vanish at some point `(1, c)` with `c_j = 0` for `j + 1 ≥ t`.  (Here
`X₀, …, X_{t-1}` stand for the printed `x₁, …, x_t`; `k` is infinite.) -/
theorem exists_point_of_suppLt [Infinite k] {t : ℕ} (ht : 1 ≤ t) {e : ℕ}
    {F : MvPolynomial (Fin (n + 1)) k} (hFh : F.IsHomogeneous e) (hF0 : F ≠ 0)
    (hFs : ∀ d : Fin (n + 1) →₀ ℕ, F.coeff d ≠ 0 → ∀ i : Fin (n + 1), t ≤ (i : ℕ) → d i = 0) :
    ∃ c : Fin n → k, (∀ j : Fin n, t ≤ (j : ℕ) + 1 → c j = 0) ∧
      MvPolynomial.eval (Fin.cons 1 c : Fin (n + 1) → k) F ≠ 0 := by
  classical
  have hQh : (F * MvPolynomial.X 0).IsHomogeneous (e + 1) :=
    hFh.mul (MvPolynomial.isHomogeneous_X _ _)
  have hQ0 : F * MvPolynomial.X 0 ≠ 0 := mul_ne_zero hF0 (MvPolynomial.X_ne_zero _)
  obtain ⟨r, hr⟩ : ∃ r : Fin (n + 1) → k, MvPolynomial.eval r (F * MvPolynomial.X 0) ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hQ0 (hQh.eq_zero_of_forall_eval_eq_zero hcon)
  set r' : Fin (n + 1) → k := fun i => if (i : ℕ) < t then r i else 0 with hr'
  have hev : MvPolynomial.eval r' F = MvPolynomial.eval r F := by
    rw [MvPolynomial.eval_eq', MvPolynomial.eval_eq']
    refine Finset.sum_congr rfl fun d hd => ?_
    congr 1
    refine Finset.prod_congr rfl fun i _ => ?_
    by_cases hi : (i : ℕ) < t
    · simp [hr', hi]
    · have := hFs d (MvPolynomial.mem_support_iff.mp hd) i (not_lt.mp hi)
      simp [this]
  have h0t : 0 < t := by omega
  have hr0 : r 0 ≠ 0 ∧ MvPolynomial.eval r F ≠ 0 := by
    rw [map_mul, MvPolynomial.eval_X] at hr
    exact ⟨(mul_ne_zero_iff.mp hr).2, (mul_ne_zero_iff.mp hr).1⟩
  refine ⟨fun j => r' j.succ / r 0, fun j hj => ?_, ?_⟩
  · have h1 : ¬ ((j.succ : Fin (n + 1)) : ℕ) < t := by simp only [Fin.val_succ]; omega
    have h2 : r' j.succ = 0 := ite_eq_right_iff.mpr (fun h => absurd h h1)
    show r' j.succ / r 0 = 0
    rw [h2, zero_div]
  · have hx : (Fin.cons 1 (fun j => r' j.succ / r 0) : Fin (n + 1) → k) = (r 0)⁻¹ • r' := by
      funext s
      refine Fin.cases ?_ (fun j => ?_) s
      · simp [hr', h0t, hr0.1]
      · simp [div_eq_inv_mul]
    rw [hx, eval_smul_of_isHomogeneous hFh, hev]
    exact mul_ne_zero (pow_ne_zero _ (inv_ne_zero hr0.1)) hr0.2

/-- **The Weierstrass form after a suitable linear transformation of `(x₁, …, x_t)`** (p. 270): if
the leading form of `g` (of degree `e`) involves only `X_i`, `i < t`, there are `c_j ∈ k`, with
`c_j = 0` for `j + 1 ≥ t`, such that after the linear transformation `X_{j+1} ↦ X_{j+1} + c_j X₀`
(which involves only the variables `X₁, …, X_{t-1}` and `X₀`) the series `g` is a unit times a
distinguished polynomial in `X₀` of degree `e`: "we may assume that `φ_Ā` has the term of `X₁^e`
with non-zero coefficient in `k`.  Then by the Weierstrass preparation theorem, we can write
`h_Ā = u(x₁^e + p'₁x₁^{e-1} + ⋯ + p'_e)`". -/
theorem exists_shift_weierstrass_form [CharZero k] {t : ℕ} (ht : 1 ≤ t)
    (g : MvPowerSeries (Fin (n + 1)) k) {e : ℕ} (hg : g.order = e)
    (hsupp : ∀ d : Fin (n + 1) →₀ ℕ, d.degree = e → coeff d g ≠ 0 →
      ∀ i : Fin (n + 1), t ≤ (i : ℕ) → d i = 0) :
    ∃ c : Fin n → k, (∀ j : Fin n, t ≤ (j : ℕ) + 1 → c j = 0) ∧
      ∃ (u : (MvPowerSeries (Fin (n + 1)) k)ˣ) (a : Fin e → MvPowerSeries (Fin n) k),
        genericShift c g = (u : MvPowerSeries (Fin (n + 1)) k) *
          (X 0 ^ e + ∑ l : Fin e, coeffRingInclusion k n (a l) * X 0 ^ (e - ((l : ℕ) + 1))) ∧
        ∀ l : Fin e, (((l : ℕ) + 1 : ℕ) : ℕ∞) ≤ (a l).order := by
  classical
  have hg0 : g ≠ 0 := by
    rintro rfl
    simp at hg
  have hν : g.order.toNat = e := by rw [hg]; simp
  have hFh : (leadingForm e g).IsHomogeneous e := isHomogeneous_leadingForm _ _
  have hF0 : leadingForm e g ≠ 0 := by
    have := leadingForm_ne_zero g hg0
    rwa [hν] at this
  have hFs : ∀ d : Fin (n + 1) →₀ ℕ, (leadingForm e g).coeff d ≠ 0 →
      ∀ i : Fin (n + 1), t ≤ (i : ℕ) → d i = 0 := by
    intro d hd i hi
    rw [coeff_leadingForm] at hd
    split_ifs at hd with h
    · exact hsupp d h hd i hi
    · exact absurd rfl hd
  obtain ⟨c, hc0, hcF⟩ := exists_point_of_suppLt ht hFh hF0 hFs
  refine ⟨c, hc0, ?_⟩
  have hord : (e : ℕ∞) ≤ (genericShift c g).order := by
    rw [← hg]; exact le_order_genericShift c g
  have hsplit : genericShift c g =
      genericShift c ((leadingForm e g : MvPolynomial (Fin (n + 1)) k) :
        MvPowerSeries (Fin (n + 1)) k) +
      genericShift c (g - (leadingForm e g : MvPolynomial (Fin (n + 1)) k)) := by
    rw [← map_add]; congr 1; ring
  have hsub := succ_le_order_sub_leadingForm g hg0
  rw [hν] at hsub
  have hcoeff : MvPowerSeries.coeff (Finsupp.cons e 0) (genericShift c g) ≠ 0 := by
    rw [hsplit, map_add, coeff_genericShift_homogeneous c hFh]
    have h2 : MvPowerSeries.coeff (Finsupp.cons e 0)
        (genericShift c (g - (leadingForm e g : MvPolynomial (Fin (n + 1)) k))) = 0 := by
      refine MvPowerSeries.coeff_of_lt_order (lt_of_lt_of_le ?_
        (hsub.trans (le_order_genericShift c _)))
      rw [degree_cons]
      simp only [map_zero, add_zero]
      exact_mod_cast Nat.lt_succ_self e
    rw [h2, add_zero]
    exact hcF
  obtain ⟨u, f, hm, hdeg, hh, hbound⟩ := exists_weierstrass_form n e _ hord hcoeff
  refine ⟨u, fun l => f.coeff (e - ((l : ℕ) + 1)), ?_, fun l => ?_⟩
  · rw [hh, expansion_of_monic f hm e hdeg]
  · have := hbound (e - ((l : ℕ) + 1)) (by have := l.2; omega)
    have e' : e - (e - ((l : ℕ) + 1)) = (l : ℕ) + 1 := by have := l.2; omega
    rwa [e'] at this

/-- **The choice of `w`** (p. 270), concrete form: for `g ∈ k[[X₀, …, X_n]]` of order `e ≥ 1`
whose leading form involves only `X_i`, `i < t`, there is an automorphism `ψ` of `k[[X]]` (given
with its inverse `ψ'`) with `ψ(g) = u (X₀^e + p₂ X₀^{e-2} + ⋯ + p_e)`, `u` a unit and
`p_j ∈ k[[X₁, …, X_n]]`, and such that `ψ'(X₀)` has no constant term and no linear term in the
variables `X_i`, `i ≥ t`. -/
theorem exists_weierstrass_coordinates [CharZero k] {t : ℕ} (ht : 1 ≤ t)
    (g : MvPowerSeries (Fin (n + 1)) k) {e : ℕ} (he : 0 < e) (hg : g.order = e)
    (hsupp : ∀ d : Fin (n + 1) →₀ ℕ, d.degree = e → coeff d g ≠ 0 →
      ∀ i : Fin (n + 1), t ≤ (i : ℕ) → d i = 0) :
    ∃ (ψ ψ' : MvPowerSeries (Fin (n + 1)) k →ₐ[k] MvPowerSeries (Fin (n + 1)) k)
      (u : (MvPowerSeries (Fin (n + 1)) k)ˣ) (p : ℕ → MvPowerSeries (Fin n) k),
      (∀ f, ψ' (ψ f) = f) ∧ (∀ f, ψ (ψ' f) = f) ∧
      ψ g = (u : MvPowerSeries (Fin (n + 1)) k) *
        (X 0 ^ e + ∑ j ∈ Finset.Icc 2 e, rename Fin.succ (p j) * X 0 ^ (e - j)) ∧
      constantCoeff (ψ' (X 0)) = 0 ∧
      ∀ i : Fin (n + 1), t ≤ (i : ℕ) → coeff (Finsupp.single i 1) (ψ' (X 0)) = 0 := by
  classical
  obtain ⟨c, -, u, a, hshift, hord⟩ := exists_shift_weierstrass_form ht g hg hsupp
  exact exists_weierstrass_coordinates_aux ht g e he hg.ge hsupp c u a hshift hord

end Assembly

end Hironaka
