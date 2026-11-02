/-
Copyright (c) 2026 Daattavya Aggarwal, Minhyong Kim, Oisin Kim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daattavya Aggarwal, Minhyong Kim, Oisin Kim
-/
module

public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.LocalProperties.Reduced
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Architect
public import Hironaka.Ch3.Transforms
public import Hironaka.Ch3.Frames
public import Hironaka.Compat.RSOPProducts
public import Hironaka.Compat.RegularGraded

/-!
# Compatibility layer: the criterion for frame transforms (Ch. III §8, p. 254)

> "We see that `(S; z₁, …, z_r)` admits a frame transform in `R₁` if and only if there exist
> `x ∈ P ∩ S` such that `PR₁ = (x)R₁` and `(z₁/x, …, z_r/x)` are all non-units of `R₁`."  (p. 254)

The paper gives no argument for the "if" direction; `Hironaka/Ch3/FrameTransforms.lean`
(`RegularFrame.admitsFrameTransform_iff`) fills the gap, and this file contains the ring-theoretic
tools of that proof, none of which depends on the private lemmas of that file.

Contents.

* `blowupAlgebra.exists_eq_div_pow`, `blowupAlgebra.div_pow_mem`: the elements of `R[x⁻¹P]` are
  exactly the fractions `c/xⁿ` with `c ∈ Pⁿ`;
* `blowupAlgebra.exists_ringHom_fractionRing`: a ring homomorphism `f : R → R'` with `f x ≠ 0`
  (`R'` a domain) induces `R[x⁻¹P] → Frac R'`, `c/xⁿ ↦ f c/(f x)ⁿ`;
  `blowupAlgebra.exists_ringHom_of_map_mem`: it takes values in `R'` if `f P ⊆ (f x) R'`;
* `exists_eq_sum_mul_of_mem_span_of_mem_pow` ("Lemma K"): for a prime `P` with `R/P` regular and
  `z₁, …, z_r ∈ P` part of a regular system of parameters, `(z_i)_{i ∈ I} ∩ Pⁿ = Σ z_i Pⁿ⁻¹`;
* `MonoidalTransform.exists_ringHom_fractionRing_ker_eq`: for a monoidal transform `R₁` of `R` with
  centre `P`, `PR₁ = (x₁)R₁`, `z_j = x₁ w_j` (`w_j ∈ M₁`), a retraction `f : R → R'` with kernel
  `(z_i)_{i ∈ I}` extends to `ρ : R₁ → Frac R'` with kernel `(w_i)_{i ∈ I}R₁`;
* `RegularFrame.retraction`: the canonical retraction `R → R/(z)R ≅ S` of a regular frame.
-/

@[expose] public section

open IsLocalRing

namespace Hironaka

universe u

/-! ### Elements of `R[x⁻¹P]` and homomorphisms out of it -/

section ChartMap

variable {R : Type u} [CommRing R] [IsRegularLocalRing R] [IsDomain R] {P : Ideal R}

/-- Every element of `R[x⁻¹P]` is `c/xⁿ` with `c ∈ Pⁿ` (for `x ∈ P`). -/
theorem blowupAlgebra.exists_eq_div_pow {x : R} (hx : x ∈ P) (hx0 : x ≠ 0)
    (a : blowupAlgebra R P x) :
    ∃ (n : ℕ) (c : R), c ∈ P ^ n ∧
      (a : FractionRing R) = algebraMap R (FractionRing R) c /
        algebraMap R (FractionRing R) x ^ n := by
  have hx0' : algebraMap R (FractionRing R) x ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective R (FractionRing R))).mpr hx0
  obtain ⟨a, ha⟩ := a
  simp only
  induction ha using Algebra.adjoin_induction with
  | mem y hy =>
    obtain ⟨p, hp, rfl⟩ := hy
    exact ⟨1, p, by rwa [pow_one], by rw [pow_one]⟩
  | algebraMap r => exact ⟨0, r, by simp, by simp⟩
  | add y z _ _ hy hz =>
    obtain ⟨n, c, hc, rfl⟩ := hy
    obtain ⟨m, d, hd, rfl⟩ := hz
    refine ⟨n + m, c * x ^ m + d * x ^ n, add_mem ?_ ?_, ?_⟩
    · rw [pow_add]
      exact Ideal.mul_mem_mul hc (Ideal.pow_mem_pow hx m)
    · rw [pow_add, mul_comm (P ^ n)]
      exact Ideal.mul_mem_mul hd (Ideal.pow_mem_pow hx n)
    · rw [div_add_div _ _ (pow_ne_zero _ hx0') (pow_ne_zero _ hx0')]
      simp only [map_add, map_mul, map_pow, pow_add]
      ring
  | mul y z _ _ hy hz =>
    obtain ⟨n, c, hc, rfl⟩ := hy
    obtain ⟨m, d, hd, rfl⟩ := hz
    refine ⟨n + m, c * d, by rw [pow_add]; exact Ideal.mul_mem_mul hc hd, ?_⟩
    rw [map_mul, pow_add, div_mul_div_comm]

/-- `c/xⁿ ∈ R[x⁻¹P]` for `c ∈ Pⁿ`. -/
theorem blowupAlgebra.div_pow_mem {x : R} {n : ℕ} {c : R} (hc : c ∈ P ^ n) :
    algebraMap R (FractionRing R) c / algebraMap R (FractionRing R) x ^ n ∈
      blowupAlgebra R P x := by
  induction n generalizing c with
  | zero => simp
  | succ n ih =>
    rw [pow_succ] at hc
    refine Submodule.mul_induction_on (C := fun c => algebraMap R (FractionRing R) c /
      algebraMap R (FractionRing R) x ^ (n + 1) ∈ blowupAlgebra R P x) hc ?_ ?_
    · intro a ha b hb
      rw [map_mul, pow_succ, mul_div_mul_comm]
      exact Subalgebra.mul_mem _ (ih ha) (Algebra.subset_adjoin ⟨b, hb, rfl⟩)
    · intro a b ha hb
      rw [map_add, add_div]
      exact Subalgebra.add_mem _ ha hb

/-- `c/xⁿ = d/xᵐ` in `Frac R` implies `f c/(f x)ⁿ = f d/(f x)ᵐ` in `Frac R'`. -/
private theorem blowupAlgebra.map_div_eq_map_div_aux {R' : Type*} [CommRing R'] [IsDomain R']
    {x : R} (hx0 : x ≠ 0) (f : R →+* R') (hf : f x ≠ 0) {n m : ℕ} {c d : R}
    (h : algebraMap R (FractionRing R) c / algebraMap R (FractionRing R) x ^ n =
      algebraMap R (FractionRing R) d / algebraMap R (FractionRing R) x ^ m) :
    algebraMap R' (FractionRing R') (f c) / algebraMap R' (FractionRing R') (f x) ^ n =
      algebraMap R' (FractionRing R') (f d) / algebraMap R' (FractionRing R') (f x) ^ m := by
  have hx0' : algebraMap R (FractionRing R) x ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective R (FractionRing R))).mpr hx0
  have hf0 : algebraMap R' (FractionRing R') (f x) ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective R' (FractionRing R'))).mpr hf
  rw [div_eq_div_iff (pow_ne_zero _ hx0') (pow_ne_zero _ hx0')] at h
  have h' : c * x ^ m = d * x ^ n := by
    apply IsFractionRing.injective R (FractionRing R)
    simpa only [map_mul, map_pow] using h
  have h'' := congrArg (fun y => algebraMap R' (FractionRing R') (f y)) h'
  simp only [map_mul, map_pow] at h''
  rw [div_eq_div_iff (pow_ne_zero _ hf0) (pow_ne_zero _ hf0)]
  exact h''

/-- The ring homomorphism `R[x⁻¹P] → Frac R'` induced by `f : R → R'` with `f x ≠ 0`. -/
theorem blowupAlgebra.exists_ringHom_fractionRing {R' : Type*} [CommRing R'] [IsDomain R']
    {x : R} (hx : x ∈ P) (hx0 : x ≠ 0) (f : R →+* R') (hf : f x ≠ 0) :
    ∃ Φ : blowupAlgebra R P x →+* FractionRing R',
      ∀ (n : ℕ) (c : R) (b : blowupAlgebra R P x),
        (b : FractionRing R) = algebraMap R (FractionRing R) c /
          algebraMap R (FractionRing R) x ^ n →
        Φ b = algebraMap R' (FractionRing R') (f c) /
          algebraMap R' (FractionRing R') (f x) ^ n := by
  classical
  have hx0' : algebraMap R (FractionRing R) x ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective R (FractionRing R))).mpr hx0
  have hf0 : algebraMap R' (FractionRing R') (f x) ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective R' (FractionRing R'))).mpr hf
  have hrep := fun b : blowupAlgebra R P x => blowupAlgebra.exists_eq_div_pow hx hx0 b
  let val : blowupAlgebra R P x → FractionRing R' := fun b =>
    algebraMap R' (FractionRing R') (f (hrep b).choose_spec.choose) /
      algebraMap R' (FractionRing R') (f x) ^ (hrep b).choose
  have hval : ∀ (n : ℕ) (c : R) (b : blowupAlgebra R P x),
      (b : FractionRing R) = algebraMap R (FractionRing R) c /
        algebraMap R (FractionRing R) x ^ n →
      val b = algebraMap R' (FractionRing R') (f c) /
        algebraMap R' (FractionRing R') (f x) ^ n := by
    intro n c b hb
    exact blowupAlgebra.map_div_eq_map_div_aux hx0 f hf (by
      rw [← hb]
      exact (hrep b).choose_spec.choose_spec.2.symm)
  refine ⟨{ toFun := val
            map_one' := ?_
            map_mul' := ?_
            map_zero' := ?_
            map_add' := ?_ }, fun n c b hb => hval n c b hb⟩
  · have := hval 0 1 1 (by simp)
    simpa using this
  · intro a b
    obtain ⟨n, c, -, ha⟩ := hrep a
    obtain ⟨m, d, -, hb⟩ := hrep b
    have hab : ((a * b : blowupAlgebra R P x) : FractionRing R) =
        algebraMap R (FractionRing R) (c * d) / algebraMap R (FractionRing R) x ^ (n + m) := by
      rw [Subalgebra.coe_mul, ha, hb, map_mul, pow_add, div_mul_div_comm]
    rw [hval _ _ _ hab, hval n c a ha, hval m d b hb, map_mul, pow_add, div_mul_div_comm]
    simp only [map_mul]
  · have := hval 0 0 0 (by simp)
    simpa using this
  · intro a b
    obtain ⟨n, c, -, ha⟩ := hrep a
    obtain ⟨m, d, -, hb⟩ := hrep b
    have hab : ((a + b : blowupAlgebra R P x) : FractionRing R) =
        algebraMap R (FractionRing R) (c * x ^ m + d * x ^ n) /
          algebraMap R (FractionRing R) x ^ (n + m) := by
      rw [Subalgebra.coe_add, ha, hb, div_add_div _ _ (pow_ne_zero _ hx0') (pow_ne_zero _ hx0')]
      simp only [map_add, map_mul, map_pow, pow_add]
      ring
    show val (a + b) = val a + val b
    rw [hval _ _ _ hab, hval n c a ha, hval m d b hb,
      div_add_div _ _ (pow_ne_zero _ hf0) (pow_ne_zero _ hf0)]
    simp only [map_add, map_mul, map_pow, pow_add]
    ring

/-- A lift of `f : R → R₁` to `R[x⁻¹P]` with values in `R₁` when `f P ⊆ (f x) R₁`. -/
theorem blowupAlgebra.exists_ringHom_of_map_mem {R₁ : Type*} [CommRing R₁] [IsDomain R₁]
    {x : R} (hx : x ∈ P) (hx0 : x ≠ 0) (f : R →+* R₁) (hf : f x ≠ 0)
    (hP : ∀ p ∈ P, ∃ y : R₁, f x * y = f p) :
    ∃ γ : blowupAlgebra R P x →+* R₁,
      (∀ s : R, γ (algebraMap R _ s) = f s) ∧
      ∀ (n : ℕ) (c : R) (b : blowupAlgebra R P x),
        (b : FractionRing R) = algebraMap R (FractionRing R) c /
          algebraMap R (FractionRing R) x ^ n → f x ^ n * γ b = f c := by
  obtain ⟨Φ, hΦ⟩ := blowupAlgebra.exists_ringHom_fractionRing hx hx0 f hf
  have hι : Function.Injective (algebraMap R₁ (FractionRing R₁)) :=
    IsFractionRing.injective R₁ (FractionRing R₁)
  have hf0 : algebraMap R₁ (FractionRing R₁) (f x) ≠ 0 :=
    (map_ne_zero_iff _ hι).mpr hf
  -- `f c ∈ (f x)ⁿ R₁` for `c ∈ Pⁿ`
  have hmem : ∀ (n : ℕ) (c : R), c ∈ P ^ n → ∃ y : R₁, f x ^ n * y = f c := by
    intro n c hc
    have h1 : P.map f ≤ Ideal.span {f x} := by
      rw [Ideal.map_le_iff_le_comap]
      intro p hp
      obtain ⟨y, hy⟩ := hP p hp
      rw [Ideal.mem_comap, Ideal.mem_span_singleton']
      exact ⟨y, by rw [mul_comm, hy]⟩
    have h2 : f c ∈ (Ideal.span {f x}) ^ n := by
      refine Ideal.pow_right_mono h1 n ?_
      rw [← Ideal.map_pow]
      exact Ideal.mem_map_of_mem f hc
    rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton'] at h2
    obtain ⟨y, hy⟩ := h2
    exact ⟨y, by rw [mul_comm, hy]⟩
  have hrange : ∀ b : blowupAlgebra R P x, Φ b ∈ (algebraMap R₁ (FractionRing R₁)).range := by
    intro b
    obtain ⟨n, c, hc, hb⟩ := blowupAlgebra.exists_eq_div_pow hx hx0 b
    obtain ⟨y, hy⟩ := hmem n c hc
    refine ⟨y, ?_⟩
    rw [hΦ n c b hb, eq_div_iff (pow_ne_zero _ hf0)]
    rw [← map_pow, ← map_mul, mul_comm, hy]
  let e : R₁ ≃+* (algebraMap R₁ (FractionRing R₁)).range :=
    RingEquiv.ofBijective (algebraMap R₁ (FractionRing R₁)).rangeRestrict
      ⟨fun a b h => hι (congrArg Subtype.val h), RingHom.rangeRestrict_surjective _⟩
  have he : ∀ z : R₁, ((e z : (algebraMap R₁ (FractionRing R₁)).range) : FractionRing R₁) =
      algebraMap R₁ (FractionRing R₁) z := fun z => rfl
  have key : ∀ b : blowupAlgebra R P x,
      algebraMap R₁ (FractionRing R₁) (e.symm (Φ.codRestrict _ hrange b)) = Φ b := by
    intro b
    rw [← he, e.apply_symm_apply]
    rfl
  refine ⟨e.symm.toRingHom.comp (Φ.codRestrict _ hrange), ?_, ?_⟩
  · intro s
    have hb : ((algebraMap R (blowupAlgebra R P x) s : blowupAlgebra R P x) : FractionRing R) =
        algebraMap R (FractionRing R) s / algebraMap R (FractionRing R) x ^ 0 := by simp
    apply hι
    have h1 := key (algebraMap R _ s)
    simp only [RingHom.coe_comp, Function.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe]
    rw [h1, hΦ 0 s _ hb]
    simp
  · intro n c b hb
    apply hι
    have h1 := key b
    simp only [RingHom.coe_comp, Function.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe]
    rw [map_mul, map_pow, h1, hΦ n c b hb]
    field_simp

end ChartMap

/-! ### "Lemma K": `(z_I) ∩ Pⁿ = (z_I) Pⁿ⁻¹` -/

open Classical in
/-- **Lemma K.**  Let `z₁, …, z_r` be part of a regular system of parameters of a regular local
ring `R` and `P` a prime with `R/P` regular and `z_i ∈ P`.  If `c ∈ (z_i)_{i ∈ I} ∩ Pⁿ`, then
`c = Σ_{i ∈ I} z_i d_i` with `d_i ∈ Pⁿ⁻¹`. -/
theorem exists_eq_sum_mul_of_mem_span_of_mem_pow {R : Type u} [CommRing R] [IsRegularLocalRing R]
    {r : ℕ} {z : Fin r → R} (hz : Function.Injective z)
    (hext : ExtendsToRSOP R (Finset.image z Finset.univ)) {P : Ideal R} [P.IsPrime]
    (hPreg : IsRegularLocalRing (R ⧸ P)) (hzP : ∀ i, z i ∈ P) (I : Finset (Fin r)) {n : ℕ}
    {c : R} (hc : c ∈ Ideal.span ((I.image z : Finset R) : Set R)) (hcP : c ∈ P ^ n) :
    ∃ d : Fin r → R, (∀ i, d i ∈ P ^ (n - 1)) ∧ c = ∑ i ∈ I, z i * d i := by
  classical
  have hPM : P ≤ maximalIdeal R := le_maximalIdeal (Ideal.IsPrime.ne_top ‹_›)
  induction I using Finset.induction_on generalizing n c with
  | empty =>
    simp only [Finset.image_empty, Finset.coe_empty, Ideal.span_empty, Ideal.mem_bot] at hc
    exact ⟨0, fun i => zero_mem _, by simp [hc]⟩
  | insert k I' hk ih =>
    rw [Finset.image_insert, Finset.coe_insert, Ideal.span_insert] at hc
    obtain ⟨y, hy, κ, hκ, hyκ⟩ := Submodule.mem_sup.mp hc
    obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.mp hy
    have hsum : ∀ (d' : Fin r → R) (t : R),
        ∑ i ∈ insert k I', z i * (Function.update d' k t) i =
          z k * t + ∑ i ∈ I', z i * d' i := by
      intro d' t
      rw [Finset.sum_insert hk, Function.update_self]
      congr 1
      exact Finset.sum_congr rfl fun i hi => by
        rw [Function.update_of_ne (fun h => hk (by rwa [h] at hi))]
    cases n with
    | zero =>
      obtain ⟨d', -, hd'⟩ := ih (n := 0) (c := κ) hκ (by simp)
      refine ⟨Function.update d' k a, fun i => by simp, ?_⟩
      rw [hsum, ← hd', ← hyκ]
      ring
    | succ m =>
      -- work in `R̄ = R/(z_i)_{i ∈ I'}`
      set K := Ideal.span ((I'.image z : Finset R) : Set R) with hK
      have hKext : ExtendsToRSOP R (I'.image z) :=
        ExtendsToRSOP.mono hext (Finset.image_subset_image (Finset.subset_univ _))
      have hKP : K ≤ P := Ideal.span_le.mpr fun y hy => by
        obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hy)
        exact hzP i
      have hRbar : IsRegularLocalRing (R ⧸ K) := ExtendsToRSOP.isRegularLocalRing_quotient hKext
      have hPbar : (P.map (Ideal.Quotient.mk K)).IsPrime :=
        Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by rwa [Ideal.mk_ker])
      have hPbreg : IsRegularLocalRing ((R ⧸ K) ⧸ P.map (Ideal.Quotient.mk K)) :=
        IsRegularLocalRing.of_ringEquiv (DoubleQuot.quotQuotEquivQuotOfLE hKP).symm
      have hdom : IsDomain (AssocGraded (P.map (Ideal.Quotient.mk K))) :=
        isDomain_assocGraded _ hPbreg
      set mk := Ideal.Quotient.mk K with hmk
      set Pb := P.map mk with hPb
      have hpow : ∀ m : ℕ, Pb ^ m = (P ^ m).map mk := fun m => (Ideal.map_pow mk P m).symm
      -- `ν_{P̄}(z_k) = 1`
      have hord1 : Ideal.ordElem Pb (mk (z k)) = 1 := by
        refine le_antisymm (Ideal.ordElem_le_of_notMem (m := 1) fun h => ?_) ?_
        · rw [hpow, Ideal.mem_quotient_iff_mem_sup] at h
          obtain ⟨Z, hsub, hZ⟩ := hext
          have hkZ : z k ∈ Z := hsub (Finset.mem_image_of_mem z (Finset.mem_univ k))
          have hTZ : I'.image z ⊆ Z := fun y hy => by
            obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hy
            exact hsub (Finset.mem_image_of_mem z (Finset.mem_univ i))
          have hkT : z k ∉ I'.image z := fun h' => by
            obtain ⟨i, hi, hik⟩ := Finset.mem_image.mp h'
            exact hk (hz hik ▸ hi)
          refine rsop_notMem_span_sup_sq hZ hTZ hkZ hkT ?_
          rw [sup_comm] at h
          exact sup_le_sup_left (Ideal.pow_right_mono hPM (1 + 1)) _ h
        · exact_mod_cast Ideal.le_ordElem (I := Pb) (f := mk (z k)) (ν := 1)
            (by rw [pow_one]; exact Ideal.mem_map_of_mem _ (hzP k))
      -- `ν_{P̄}(c̄) ≥ n`
      have hcb : ((m + 1 : ℕ) : ℕ∞) ≤ Ideal.ordElem Pb (mk (a * z k)) := by
        have hκ0 : mk κ = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hκ
        have : mk (a * z k) = mk c := by
          rw [← hyκ, map_add, hκ0, add_zero]
        rw [this]
        exact Ideal.le_ordElem (by rw [hpow]; exact Ideal.mem_map_of_mem _ hcP)
      rw [map_mul, ordElem_mul_of_isDomain, hord1] at hcb
      have hab : (m : ℕ∞) ≤ Ideal.ordElem Pb (mk a) := by
        have h1 : (m : ℕ∞) + 1 ≤ Ideal.ordElem Pb (mk a) + 1 := by
          simpa [Nat.cast_add] using hcb
        exact (ENat.add_le_add_iff_right (by simp)).mp h1
      have ha : mk a ∈ Pb ^ m := Ideal.mem_pow_of_le_ordElem hab
      rw [hpow, Ideal.mem_quotient_iff_mem_sup] at ha
      obtain ⟨a', ha', κ', hκ', haκ⟩ := Submodule.mem_sup.mp ha
      -- `c - a' z_k ∈ K ∩ Pⁿ`
      have hres : c - z k * a' ∈ K := by
        have : c - z k * a' = κ + z k * κ' := by
          rw [← hyκ, ← haκ]; ring
        rw [this]
        exact add_mem hκ (Ideal.mul_mem_left _ _ hκ')
      have hresP : c - z k * a' ∈ P ^ (m + 1) := by
        refine sub_mem hcP ?_
        rw [pow_succ']
        exact Ideal.mul_mem_mul (hzP k) ha'
      obtain ⟨d', hd', hsum'⟩ := ih (n := m + 1) hres hresP
      refine ⟨Function.update d' k a', fun i => ?_, ?_⟩
      · by_cases hik : i = k
        · subst hik; simpa using ha'
        · rw [Function.update_of_ne hik]; exact hd' i
      · rw [hsum, ← hsum']; ring

/-! ### Retractions of a monoidal transform -/

section RetractionKernel

/-- If `b = c/xⁿ` in `R[x⁻¹P]`, then `b · xⁿ = c` in `R₁`. -/
theorem MonoidalTransform.algebraMap_mul_xR_pow_eq {R : Type u} [CommRing R]
    [IsRegularLocalRing R] [IsDomain R]
    {P : Ideal R} (T : MonoidalTransform R P) :
    ∀ (n : ℕ) (c : R) (b : blowupAlgebra R P T.x),
      (b : FractionRing R) = algebraMap R (FractionRing R) c /
        algebraMap R (FractionRing R) T.x ^ n →
      algebraMap _ T.ring b * T.xR ^ n = T.toRing c := by
    intro n c b hb
    have hx0 : algebraMap R (FractionRing R) T.x ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective R (FractionRing R))).mpr T.x_ne_zero
    have h1 : b * (algebraMap R (blowupAlgebra R P T.x) T.x) ^ n =
        algebraMap R (blowupAlgebra R P T.x) c := by
      apply Subtype.ext
      simp only [MulMemClass.coe_mul, SubmonoidClass.coe_pow, Subalgebra.coe_algebraMap, hb]
      field_simp
    have h2 := congrArg (algebraMap (blowupAlgebra R P T.x) T.ring) h1
    have e1 : T.xR = algebraMap _ T.ring (algebraMap R (blowupAlgebra R P T.x) T.x) := rfl
    have e2 : T.toRing c = algebraMap _ T.ring (algebraMap R (blowupAlgebra R P T.x) c) := rfl
    rw [e1, e2]
    simpa only [map_mul, map_pow] using h2

open Classical in
/-- **Retraction with kernel.**  Let `R` be a regular local ring, `P` a prime with `R/P` regular,
`z₁, …, z_r ∈ P` part of a regular system of parameters, `T` a monoidal transform of `R` with
center `P` such that `P R₁ = (x₁) R₁` and `z_j = x₁ w_j` with `w_j ∈ M₁`.  Let `f : R → R'` be
a ring homomorphism to a domain with kernel `(z_i)_{i ∈ I}` and `f(T.x) ≠ 0`.  Then `f` extends
to a homomorphism `ρ : R₁ → Frac R'` (`c/x ↦ f c / f x`) whose kernel is `(w_i)_{i ∈ I} R₁`. -/
theorem MonoidalTransform.exists_ringHom_fractionRing_ker_eq {R : Type u} [CommRing R]
    [IsRegularLocalRing R] [IsDomain R]
    {P : Ideal R} [P.IsPrime] (hPreg : IsRegularLocalRing (R ⧸ P))
    {r : ℕ} {z : Fin r → R} (hz : Function.Injective z)
    (hext : ExtendsToRSOP R (Finset.image z Finset.univ)) (hzP : ∀ i, z i ∈ P)
    (T : MonoidalTransform R P) [IsLocalHom T.toRing] [IsRegularLocalRing T.ring]
    {x₁ : T.ring} (hx₁ : P.map T.toRing = Ideal.span {x₁})
    {w : Fin r → T.ring} (hw : ∀ j, x₁ * w j = T.toRing (z j))
    (hwM : ∀ j, w j ∈ maximalIdeal T.ring)
    {R' : Type*} [CommRing R'] [IsDomain R'] (f : R →+* R') (I : Finset (Fin r))
    (hker : ∀ c, f c = 0 ↔ c ∈ Ideal.span ((I.image z : Finset R) : Set R))
    (hfx : f T.x ≠ 0) :
    ∃ ρ : T.ring →+* FractionRing R',
      (∀ c, ρ (T.toRing c) = algebraMap R' (FractionRing R') (f c)) ∧
      RingHom.ker ρ = Ideal.span (w '' (I : Set (Fin r))) := by
  classical
  have hX0 : T.xR ≠ 0 := fun h => T.x_ne_zero (T.toRing_injective (h.trans (map_zero _).symm))
  obtain ⟨u, hu⟩ : ∃ u : T.ring ˣ, T.xR * u = x₁ :=
    Ideal.span_singleton_eq_span_singleton.mp (T.span_xR_eq_map.trans hx₁)
  obtain ⟨Φ, hΦ⟩ := blowupAlgebra.exists_ringHom_fractionRing T.x_mem T.x_ne_zero f hfx
  set 𝔴 := Ideal.span (w '' (I : Set (Fin r))) with h𝔴
  have hwmem : ∀ i ∈ I, w i ∈ 𝔴 := fun i hi => Ideal.subset_span ⟨i, hi, rfl⟩
  have h𝔴M : 𝔴 ≤ maximalIdeal T.ring :=
    Ideal.span_le.mpr (by rintro _ ⟨j, -, rfl⟩; exact hwM j)
  have hfx' : algebraMap R' (FractionRing R') (f T.x) ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective R' (FractionRing R'))).mpr hfx
  have hyb := MonoidalTransform.algebraMap_mul_xR_pow_eq T
  -- elements of `Pᵐ` are `Xᵐ` times elements of `R₁`
  have hPm : ∀ (m : ℕ) (d : R), d ∈ P ^ m → ∃ e : T.ring, T.toRing d = T.xR ^ m * e := by
    intro m d hd
    have h1 : T.toRing d ∈ (P ^ m).map T.toRing := Ideal.mem_map_of_mem _ hd
    rw [Ideal.map_pow, ← T.span_xR_eq_map, Ideal.span_singleton_pow,
      Ideal.mem_span_singleton'] at h1
    obtain ⟨e, he⟩ := h1
    exact ⟨e, by rw [← he, mul_comm]⟩
  -- the kernel of `Φ`
  have hker1 : ∀ b : blowupAlgebra R P T.x, Φ b = 0 → algebraMap _ T.ring b ∈ 𝔴 := by
    intro b hb0
    obtain ⟨n, c, hc, hb⟩ := blowupAlgebra.exists_eq_div_pow T.x_mem T.x_ne_zero b
    rw [hΦ n c b hb, div_eq_zero_iff] at hb0
    have hfc : f c = 0 := by
      rcases hb0 with h | h
      · exact (map_eq_zero_iff _ (IsFractionRing.injective R' (FractionRing R'))).mp h
      · exact absurd (pow_eq_zero_iff'.mp h).1 hfx'
    obtain ⟨d, hd, hcd⟩ := exists_eq_sum_mul_of_mem_span_of_mem_pow hz hext hPreg hzP I
      ((hker c).mp hfc) hc
    choose e he using fun i => hPm (n - 1) (d i) (hd i)
    have hTc : T.toRing c = ∑ i ∈ I, x₁ * w i * (T.xR ^ (n - 1) * e i) := by
      rw [hcd, map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_mul, he i, hw i]
    have hyb' := hyb n c b hb
    cases n with
    | zero =>
      simp only [pow_zero, mul_one] at hyb' hTc
      rw [hyb', hTc]
      refine Ideal.sum_mem _ fun i hi => ?_
      have : x₁ * w i * (e i) = w i * (x₁ * e i) := by ring
      simp only [Nat.zero_sub, pow_zero, one_mul] at this ⊢
      rw [this]
      exact Ideal.mul_mem_right _ _ (hwmem i hi)
    | succ m =>
      simp only [Nat.add_sub_cancel] at hTc
      have : algebraMap _ T.ring b * T.xR ^ (m + 1) =
          T.xR ^ (m + 1) * ((u : T.ring) * ∑ i ∈ I, w i * e i) := by
        rw [hyb', hTc, Finset.mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [← hu]
        ring
      have h2 := mul_right_cancel₀ (pow_ne_zero (m + 1) hX0)
        (this.trans (mul_comm _ _))
      rw [h2]
      refine Ideal.mul_mem_left _ _ (Ideal.sum_mem _ fun i hi => ?_)
      exact Ideal.mul_mem_right _ _ (hwmem i hi)
  -- units
  have hne : ∀ s : T.M'.primeCompl, Φ s ≠ 0 := by
    intro s hs0
    exact s.2 ((IsLocalization.AtPrime.to_map_mem_maximal_iff T.ring T.M' _).mp
      (h𝔴M (hker1 s hs0)))
  have hg : ∀ s : T.M'.primeCompl, IsUnit (Φ s) := fun s => (hne s).isUnit
  set ρ : T.ring →+* FractionRing R' :=
    IsLocalization.lift (M := T.M'.primeCompl) (S := T.ring) hg with hρ
  have hρb : ∀ b : blowupAlgebra R P T.x, ρ (algebraMap _ T.ring b) = Φ b :=
    fun b => IsLocalization.lift_eq hg b
  refine ⟨ρ, ?_, ?_⟩
  · intro c
    have h1 : T.toRing c = algebraMap (blowupAlgebra R P T.x) T.ring
        (algebraMap R (blowupAlgebra R P T.x) c) := rfl
    rw [h1, hρb]
    have := hΦ 0 c (algebraMap R (blowupAlgebra R P T.x) c) (by simp)
    simpa using this
  · apply le_antisymm
    · intro v hv
      rw [RingHom.mem_ker] at hv
      obtain ⟨⟨a, s⟩, hmk⟩ := IsLocalization.mk'_surjective T.M'.primeCompl v
      have hmk' : IsLocalization.mk' T.ring a s = v := hmk
      rw [← hmk'] at hv ⊢
      have h1 : ρ (IsLocalization.mk' T.ring a s) * Φ (s : blowupAlgebra R P T.x) = Φ a := by
        rw [← hρb a, ← hρb (s : blowupAlgebra R P T.x), ← map_mul, IsLocalization.mk'_spec]
      rw [hv, zero_mul] at h1
      have h2 := hker1 a h1.symm
      have h3 : IsLocalization.mk' T.ring a s * algebraMap _ T.ring (s : blowupAlgebra R P T.x) =
          algebraMap _ T.ring a := IsLocalization.mk'_spec _ a s
      have hsunit : IsUnit
          (algebraMap (blowupAlgebra R P T.x) T.ring (s : blowupAlgebra R P T.x)) :=
        IsLocalization.map_units T.ring s
      obtain ⟨t, ht⟩ := hsunit
      have : IsLocalization.mk' T.ring a s = algebraMap _ T.ring a * (↑t⁻¹ : T.ring) := by
        rw [← h3, ← ht, mul_assoc, Units.mul_inv, mul_one]
      rw [this]
      exact Ideal.mul_mem_right _ _ h2
    · rw [h𝔴, Ideal.span_le]
      rintro _ ⟨i, hi, rfl⟩
      rw [SetLike.mem_coe, RingHom.mem_ker]
      -- `w_i = u⁻¹ (z_i / x)`
      have hzi : z i ∈ P ^ 1 := by rw [pow_one]; exact hzP i
      let ω : blowupAlgebra R P T.x :=
        ⟨_, blowupAlgebra.div_pow_mem (P := P) (x := T.x) (n := 1) hzi⟩
      have hωb : ((ω : blowupAlgebra R P T.x) : FractionRing R) =
          algebraMap R (FractionRing R) (z i) / algebraMap R (FractionRing R) T.x ^ 1 := rfl
      have hΦω : Φ ω = 0 := by
        rw [hΦ 1 (z i) ω hωb]
        have : f (z i) = 0 := (hker _).mpr (Ideal.subset_span
          (by simpa using ⟨i, hi, rfl⟩ : z i ∈ ((I.image z : Finset R) : Set R)))
        simp [this]
      have hyω := hyb 1 (z i) ω hωb
      have hwu : algebraMap _ T.ring ω = (u : T.ring) * w i := by
        have h1 : algebraMap _ T.ring ω * T.xR = (u : T.ring) * w i * T.xR := by
          rw [pow_one] at hyω
          rw [hyω, ← hw i, ← hu]
          ring
        exact mul_right_cancel₀ hX0 h1
      have hwi : w i = (↑u⁻¹ : T.ring) * algebraMap _ T.ring ω := by
        rw [hwu, ← mul_assoc, Units.inv_mul, one_mul]
      rw [hwi, map_mul, hρb, hΦω, mul_zero]

end RetractionKernel

/-! ### The retraction of a regular frame -/

namespace RegularFrame

section Retraction

variable {R : Type u} [CommRing R] [IsRegularLocalRing R] (F : RegularFrame R)

/-- `S → R` is injective (`R/(z)R ≅ S`). -/
theorem algebraMap_injective : Function.Injective (algebraMap F.S R) := fun a b hab =>
  F.quot_bijective.1 (by simp only [RingHom.comp_apply]; rw [hab])

/-- The canonical retraction `R → R/(z)R ≅ S` of a regular frame `(S; z)`. -/
noncomputable def retraction : R →+* F.S :=
  ((RingEquiv.ofBijective _ F.quot_bijective).symm.toRingHom).comp
    (Ideal.Quotient.mk (Ideal.span (Set.range F.z)))

/-- The retraction `R → S` is a left inverse of the structure map `S → R`. -/
theorem retraction_algebraMap (s : F.S) : F.retraction (algebraMap F.S R s) = s := by
  have := (RingEquiv.ofBijective _ F.quot_bijective).symm_apply_apply s
  simpa [retraction] using this

/-- The kernel of the retraction `R → S` is `(z₁, …, z_r)R`. -/
theorem retraction_eq_zero_iff (c : R) : F.retraction c = 0 ↔ c ∈ F.idealZ := by
  unfold retraction
  simp only [RingHom.coe_comp, Function.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe,
    map_eq_zero_iff _ (RingEquiv.injective _)]
  exact Ideal.Quotient.eq_zero_iff_mem

/-- `c - φ(ρ c) ∈ (z₁, …, z_r)R` for the structure map `φ : S → R` and the retraction `ρ`. -/
theorem sub_algebraMap_retraction_mem (c : R) :
    c - algebraMap F.S R (F.retraction c) ∈ F.idealZ := by
  have h := (RingEquiv.ofBijective _ F.quot_bijective).apply_symm_apply
    (Ideal.Quotient.mk (Ideal.span (Set.range F.z)) c)
  have h' : (Ideal.Quotient.mk (Ideal.span (Set.range F.z))) (algebraMap F.S R (F.retraction c)) =
      Ideal.Quotient.mk (Ideal.span (Set.range F.z)) c := by
    exact h
  show _ ∈ Ideal.span (Set.range F.z)
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, h', sub_self]

/-- If `P ⊇ (z)R`, the retraction maps `P` into `P ∩ S`. -/
theorem retraction_mem_comap {P : Ideal R} (hzP : F.idealZ ≤ P) {c : R} (hc : c ∈ P) :
    F.retraction c ∈ P.comap (algebraMap F.S R) := by
  rw [Ideal.mem_comap]
  have := hzP (F.sub_algebraMap_retraction_mem c)
  have h2 := sub_mem hc this
  simpa using h2

end Retraction

end RegularFrame

end Hironaka
