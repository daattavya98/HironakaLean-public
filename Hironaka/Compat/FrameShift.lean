/-
Copyright (c) 2026 Daattavya Aggarwal, Minhyong Kim, Oisin Kim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daattavya Aggarwal, Minhyong Kim, Oisin Kim
-/
module

public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.Algebra.Polynomial.Taylor
public import Architect
public import Hironaka.Compat.FrameTransformCriterion
public import Hironaka.Compat.FrameLocalization
public import Hironaka.Compat.FrameCore
public import Hironaka.Ch3.TransformsCompletion

/-!
# Compatibility layer: the shift `z = x - h` of a regular frame of a complete regular local ring
(Ch. III §10, proof of Lemma 22, pp. 265–267)

> "We shall first prove the assertion under the additional assumptions that there exists a
> non-unit element `h` of `S` such that `x - h ∈ P` and that `R` is complete. In fact, let
> `z = x - h`. We write `f` in the form `f = z^ν + g'_1 z^{ν-1} + ⋯ + g'_ν` with `g'_j ∈ S`
> `(1 ≤ j ≤ ν)`. Then `g'_1 = νh`. Let `R' = R_P` and `S' = S_{P ∩ S}`. Obviously `(S'; z)` is a
> regular frame of `R'`." (pp. 265–266)
>
> "Let `x* = x/y - u`. Let `S₁` be the monoidal transform of `S` with center `N` […] such that we
> have a local canonical homomorphism `S₁ → R₁`. Then `(S₁; x*)` is a regular frame of `R₁`."
> (p. 267)

Both sentences use, without saying so, that for a regular frame `(S; x)` (`r = 1`) of a *complete*
regular local ring `R` and a non-unit `h ∈ S`, the system `(S; x - h)` is again a regular frame of
`R`: `R/(x - h)R` is canonically isomorphic to `S`.  (Completeness is needed: for the localization
`R` of `S[x][w]/(w² - 1 - x)` at `(t, x, w - 1)`, `S = ℚ[t]_{(t)}`, `(S; x)` is a regular frame but
`R/(x - t)R ≅ S[√(1 + t)]_{loc} ≠ S`.)  This file proves it:

* `RegularFrame.eq_zero_of_algebraMap_mem_span_sub`: `S ∩ (x - h)R = 0` (no completeness needed:
  `T = S ∩ (x - h)R` satisfies `T ⊆ hT`, and Krull's intersection theorem);
* `RegularFrame.exists_sub_algebraMap_mem_span_sub`: `R = S + (x - h)R` for complete `R` (successive
  approximation `c ≡ Σ_k ρ(c_k) h^k`, the retraction `ρ : R → S`, and the closedness of the ideal
  `(x - h)R`);
* `RegularFrame.shift`: the regular frame `(S; x - h)`.

It also contains the bookkeeping of the polynomial `p` with `f = p(x)` used in the proof of
Lemma 22: the coefficient of `z^{ν-1}` after the substitution `x = z + c` is `νc` when the
coefficient of `x^{ν-1}` is zero ("Then `g'_1 = νh`"), and the passage to the sums
`z^n + Σ_{i<n} c_i z^{n-(i+1)}` of `RegularFrame.coeff_mem_comap_pow_of_mem_pow`.
-/

@[expose] public section

open IsLocalRing

namespace Hironaka

universe u

noncomputable section

namespace RegularFrame

variable {R : Type u} [CommRing R] [IsRegularLocalRing R] (F : RegularFrame R)

/-- For a frame with `r = 1` and `z₁ = x`, the set of the `z_j` is `{x}`. -/
theorem range_z_eq_singleton {x : R} (hr : F.r = 1) (hx : ∀ j, F.z j = x) :
    Set.range F.z = {x} := by
  ext a
  simp only [Set.mem_range, Set.mem_singleton_iff]
  constructor
  · rintro ⟨j, rfl⟩
    exact hx j
  · rintro rfl
    exact ⟨⟨0, by rw [hr]; exact Nat.one_pos⟩, hx _⟩

/-- `F.idealZ = (x)` for a frame with `r = 1` and `z₁ = x`. -/
theorem idealZ_eq_span_singleton {x : R} (hr : F.r = 1) (hx : ∀ j, F.z j = x) :
    F.idealZ = Ideal.span {x} := by
  rw [idealZ, F.range_z_eq_singleton hr hx]

/-- `x` is a non-zero element of the maximal ideal. -/
theorem mem_maximalIdeal_and_ne_zero {x : R} (hr : F.r = 1) (hx : ∀ j, F.z j = x) :
    x ∈ maximalIdeal R ∧ x ≠ 0 := by
  classical
  have hmem : x ∈ Finset.image F.z Finset.univ :=
    Finset.mem_image.mpr ⟨⟨0, by rw [hr]; exact Nat.one_pos⟩, Finset.mem_univ _, hx _⟩
  obtain ⟨s, hsub, hs⟩ := F.extends_rsop
  refine ⟨?_, fun h0 => ?_⟩
  · rw [← hs.1]
    exact Ideal.subset_span (hsub hmem)
  · exact F.extends_rsop.ne_zero hmem h0

/-- `R = S + xR`: every `c` is `ρ(c) + x c'`, `ρ` the retraction. -/
theorem exists_eq_algebraMap_retraction_add_mul {x : R} (hr : F.r = 1) (hx : ∀ j, F.z j = x)
    (c : R) : ∃ c' : R, c = algebraMap F.S R (F.retraction c) + x * c' := by
  have h := F.sub_algebraMap_retraction_mem c
  rw [F.idealZ_eq_span_singleton hr hx, Ideal.mem_span_singleton'] at h
  obtain ⟨c', hc'⟩ := h
  exact ⟨c', by rw [mul_comm x c', hc']; ring⟩

/-- `S ∩ (x - h)R = 0` for a non-unit `h ∈ S`: the ideal `T = S ∩ (x - h)R` satisfies
`T ⊆ hT` (if `s = (x - h)b` with `b = b₀ + xb'`, then `s = -hb₀` and `b₀ = -(x - h)b'`), so
`T ⊆ ⋂ Nⁿ = 0` (Krull's intersection theorem). -/
theorem eq_zero_of_algebraMap_mem_span_sub {x : R} (hr : F.r = 1) (hx : ∀ j, F.z j = x)
    {h : F.S} (hh : h ∈ maximalIdeal F.S) {s : F.S}
    (hs : algebraMap F.S R s ∈ Ideal.span {x - algebraMap F.S R h}) : s = 0 := by
  have hdom := isDomain_of_isRegularLocalRing R
  set a := algebraMap F.S R with ha
  have hx0 := (F.mem_maximalIdeal_and_ne_zero hr hx).2
  set T : Ideal F.S := (Ideal.span {x - a h}).comap a with hT
  have key : ∀ s ∈ T, ∃ t ∈ T, s = -(h * t) := by
    intro s hs
    obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.mp (Ideal.mem_comap.mp hs)
    obtain ⟨b', hb'⟩ := F.exists_eq_algebraMap_retraction_add_mul hr hx b
    set b₀ := F.retraction b
    have h1 : a (s + h * b₀) ∈ F.idealZ := by
      rw [F.idealZ_eq_span_singleton hr hx, Ideal.mem_span_singleton']
      refine ⟨b' * (x - a h) + a b₀, ?_⟩
      rw [map_add, map_mul, ← hb, hb']
      ring
    have h2 : s = -(h * b₀) := by
      have := F.eq_zero_of_algebraMap_mem_idealZ h1
      linear_combination this
    refine ⟨b₀, ?_, h2⟩
    rw [Ideal.mem_comap, Ideal.mem_span_singleton']
    have h3 : x * (a b₀ + b' * (x - a h)) = 0 := by
      have e1 : a s = (a b₀ + x * b') * (x - a h) := by rw [← hb, ← hb']
      have e2 : a s = -(a h * a b₀) := by rw [h2, map_neg, map_mul]
      linear_combination e1.symm.trans e2
    have h4 := (mul_eq_zero.mp h3).resolve_left hx0
    exact ⟨-b', by linear_combination -h4⟩
  have hpow : ∀ n : ℕ, ∀ s ∈ T, s ∈ maximalIdeal F.S ^ n := by
    intro n
    induction n with
    | zero => intro s _; simp
    | succ n ih =>
      intro s hs
      obtain ⟨t, ht, rfl⟩ := key s hs
      rw [pow_succ']
      exact neg_mem (Ideal.mul_mem_mul hh (ih t ht))
  have hmem : s ∈ ⨅ n : ℕ, maximalIdeal F.S ^ n :=
    Submodule.mem_iInf _ |>.mpr fun n => hpow n s (Ideal.mem_comap.mpr hs)
  rw [Ideal.iInf_pow_eq_bot_of_isLocalRing _ (maximalIdeal.isMaximal _).ne_top] at hmem
  exact hmem

/-- The retraction `ρ : R → S` maps `Mⁿ` into `Nⁿ` (it is surjective). -/
theorem retraction_mem_pow {c : R} {n : ℕ} (hc : c ∈ maximalIdeal R ^ n) :
    F.retraction c ∈ maximalIdeal F.S ^ n := by
  have hsurj : Function.Surjective F.retraction := fun s =>
    ⟨algebraMap F.S R s, F.retraction_algebraMap s⟩
  have hmap : (maximalIdeal R).map F.retraction = maximalIdeal F.S :=
    map_maximalIdeal_of_surjective _ hsurj
  rw [← hmap, ← Ideal.map_pow]
  exact Ideal.mem_map_of_mem _ hc

/-- The structure map `S → R` maps `Nⁿ` into `Mⁿ`. -/
theorem algebraMap_mem_pow {s : F.S} {n : ℕ} (hs : s ∈ maximalIdeal F.S ^ n) :
    algebraMap F.S R s ∈ maximalIdeal R ^ n := by
  have hle : (maximalIdeal F.S).map (algebraMap F.S R) ≤ maximalIdeal R := by
    rw [Ideal.map_le_iff_le_comap]
    intro t ht
    exact (IsLocalRing.mem_maximalIdeal _).mpr fun hu =>
      (IsLocalRing.mem_maximalIdeal _).mp ht (isUnit_of_map_unit _ _ hu)
  have := Ideal.mem_map_of_mem (algebraMap F.S R) hs
  rw [Ideal.map_pow] at this
  exact Ideal.pow_right_mono hle n this

/-- `R = S + (x - h)R` for a complete `R` and a non-unit `h ∈ S`.  Write `c = c₀`,
`c_k = ρ(c_k) + x c_{k+1}`; then `c ≡ Σ_{k<n} ρ(c_k)hᵏ + hⁿc_n` modulo `(x - h)`, the partial sums
converge in `R` to some `L`, and `c - ρ(L) ∈ (x - h)R + Mⁿ` for all `n`, hence
`c - ρ(L) ∈ (x - h)R` (Krull). -/
theorem exists_sub_algebraMap_mem_span_sub [IsAdicComplete (maximalIdeal R) R] {x : R}
    (hr : F.r = 1) (hx : ∀ j, F.z j = x) {h : F.S} (hh : h ∈ maximalIdeal F.S) (c : R) :
    ∃ s : F.S, c - algebraMap F.S R s ∈ Ideal.span {x - algebraMap F.S R h} := by
  classical
  set a := algebraMap F.S R with ha
  set I : Ideal R := Ideal.span {x - a h} with hI
  choose next hnext using fun c : R => F.exists_eq_algebraMap_retraction_add_mul hr hx c
  let sq : ℕ → R := fun n => next^[n] c
  have hsq : ∀ n, sq (n + 1) = next (sq n) := fun n =>
    Function.iterate_succ_apply' next n c
  let σ : ℕ → F.S := fun n => ∑ k ∈ Finset.range n, F.retraction (sq k) * h ^ k
  -- `c ≡ σ n + hⁿ c_n` modulo `(x - h)`
  have hA : ∀ n, c - a (σ n) - a h ^ n * sq n ∈ I := by
    intro n
    induction n with
    | zero => simp [σ, sq]
    | succ n ih =>
      have hstep : sq n = a (F.retraction (sq n)) + x * sq (n + 1) := by
        rw [hsq]; exact hnext (sq n)
      have : c - a (σ (n + 1)) - a h ^ (n + 1) * sq (n + 1) =
          (c - a (σ n) - a h ^ n * sq n) + a h ^ n * (x - a h) * sq (n + 1) := by
        simp only [σ, Finset.sum_range_succ, map_add, map_mul, map_pow]
        linear_combination (a h ^ n) * hstep
      rw [this]
      exact add_mem ih (Ideal.mul_mem_right _ _ (Ideal.mul_mem_left _ _
        (Ideal.mem_span_singleton_self _)))
  -- the partial sums form a Cauchy sequence
  have hcauchy : ∀ {m n : ℕ}, m ≤ n → a (σ n) - a (σ m) ∈ maximalIdeal R ^ m := by
    intro m n hmn
    have : σ n - σ m = ∑ k ∈ Finset.Ico m n, F.retraction (sq k) * h ^ k := by
      simp only [σ]
      rw [← Finset.sum_range_add_sum_Ico _ hmn]
      ring
    rw [← map_sub, this]
    refine F.algebraMap_mem_pow (Ideal.sum_mem _ fun k hk => ?_)
    refine Ideal.mul_mem_left _ _ ?_
    exact Ideal.pow_le_pow_right (Finset.mem_Ico.mp hk).1 (Ideal.pow_mem_pow hh k)
  obtain ⟨L, hL⟩ := IsPrecomplete.prec' (I := maximalIdeal R) (fun n => a (σ n)) (by
    intro m n hmn
    rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, ← neg_sub, neg_mem_iff]
    exact hcauchy hmn)
  have hL' : ∀ n, a (σ n) - L ∈ maximalIdeal R ^ n := fun n => by
    have := hL n
    rwa [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top] at this
  refine ⟨F.retraction L, ?_⟩
  have hfin : ∀ n, c - a (F.retraction L) ∈ I ⊔ maximalIdeal R ^ n := by
    intro n
    have h1 : a (F.retraction L) - a (σ n) ∈ maximalIdeal R ^ n := by
      have : a (F.retraction L) - a (σ n) = a (F.retraction (L - a (σ n))) := by
        rw [map_sub, map_sub, F.retraction_algebraMap]
      rw [this, ← neg_sub]
      exact F.algebraMap_mem_pow (by rw [map_neg]; exact neg_mem (F.retraction_mem_pow (hL' n)))
    have h2 : a h ^ n * sq n ∈ maximalIdeal R ^ n := by
      rw [← map_pow]
      exact Ideal.mul_mem_right _ _ (F.algebraMap_mem_pow (Ideal.pow_mem_pow hh n))
    have : c - a (F.retraction L) = (c - a (σ n) - a h ^ n * sq n) +
        (a h ^ n * sq n - (a (F.retraction L) - a (σ n))) := by ring
    rw [this]
    exact add_mem (Ideal.mem_sup_left (hA n)) (Ideal.mem_sup_right (sub_mem h2 h1))
  have := (iInf_sup_maximalIdeal_pow_eq I).le (Submodule.mem_iInf _ |>.mpr hfin)
  exact this

/-- `x - h` is a non-zero element of `M` with `R/(x - h)R ≅ S`. -/
theorem bijective_quotient_span_sub [IsAdicComplete (maximalIdeal R) R] {x : R}
    (hr : F.r = 1) (hx : ∀ j, F.z j = x) {h : F.S} (hh : h ∈ maximalIdeal F.S) :
    Function.Bijective ((Ideal.Quotient.mk (Ideal.span {x - algebraMap F.S R h})).comp
      (algebraMap F.S R)) := by
  refine ⟨fun s t hst => ?_, fun q => ?_⟩
  · have : algebraMap F.S R (s - t) ∈ Ideal.span {x - algebraMap F.S R h} := by
      rw [map_sub, ← Ideal.Quotient.eq]
      exact hst
    exact sub_eq_zero.mp (F.eq_zero_of_algebraMap_mem_span_sub hr hx hh this)
  · obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective q
    obtain ⟨s, hs⟩ := F.exists_sub_algebraMap_mem_span_sub hr hx hh c
    refine ⟨s, ?_⟩
    rw [RingHom.comp_apply, Ideal.Quotient.eq]
    have := neg_mem hs
    rwa [neg_sub] at this

/-- **The shift of a regular frame** (proof of Lemma 22, p. 265: "let `z = x - h`"; p. 267:
"`x* = x/y - u`"): for a regular frame `(S; x)` (`r = 1`) of a complete regular local ring `R` and
a non-unit `h ∈ S`, `(S; x - h)` is a regular frame of `R`. -/
def shift [IsAdicComplete (maximalIdeal R) R] {x : R} (hr : F.r = 1) (hx : ∀ j, F.z j = x)
    (h : F.S) (hh : h ∈ maximalIdeal F.S) : RegularFrame R where
  S := F.S
  r := 1
  z := fun _ => x - algebraMap F.S R h
  z_injective := Function.injective_of_subsingleton _
  extends_rsop := by
    classical
    have hb := F.bijective_quotient_span_sub hr hx hh
    have hxM := F.mem_maximalIdeal_and_ne_zero hr hx
    have hmem : x - algebraMap F.S R h ∈ maximalIdeal R :=
      sub_mem hxM.1 (by simpa using F.algebraMap_mem_pow (n := 1) (by simpa using hh))
    have hne : x - algebraMap F.S R h ≠ 0 := by
      intro h0
      apply hxM.2
      have hh0 : h = 0 := by
        apply F.eq_zero_of_algebraMap_mem_idealZ
        rw [F.idealZ_eq_span_singleton hr hx, ← sub_eq_zero.mp h0]
        exact Ideal.mem_span_singleton_self _
      rw [sub_eq_zero.mp h0, hh0, map_zero]
    have : IsRegularLocalRing (R ⧸ Ideal.span {x - algebraMap F.S R h}) :=
      IsRegularLocalRing.of_ringEquiv (RingEquiv.ofBijective _ hb)
    have himg : Finset.image (fun _ : Fin 1 => x - algebraMap F.S R h) Finset.univ =
        {x - algebraMap F.S R h} := by
      ext w; simp
    rw [himg]
    exact extendsToRSOP_singleton_of_isRegularLocalRing_quotient hmem hne
  quot_bijective := by
    have hrange : Set.range (fun _ : Fin 1 => x - algebraMap F.S R h) =
        {x - algebraMap F.S R h} := by
      ext w; simp
    rw [hrange]
    exact F.bijective_quotient_span_sub hr hx hh

end RegularFrame

/-! ### The polynomial `Z^n + Σ_{i<n} c_i Z^{n-(i+1)}` -/

section FramePoly

open Polynomial

variable {S : Type*} [CommRing S]

/-- The polynomial `Zⁿ + c₀Zⁿ⁻¹ + ⋯ + c_{n-1}` (the shape `z^n + Σ_{i<n} c_i z^{n-(i+1)}` of
`RegularFrame.coeff_mem_comap_pow_of_mem_pow`). -/
def framePoly (n : ℕ) (c : Fin n → S) : S[X] :=
  X ^ n + ∑ i : Fin n, C (c i) * X ^ (n - ((i : ℕ) + 1))

theorem framePoly_eval₂ {B : Type*} [CommRing B] (φ : S →+* B) (n : ℕ) (c : Fin n → S) (z : B) :
    (framePoly n c).eval₂ φ z = z ^ n + ∑ i : Fin n, φ (c i) * z ^ (n - ((i : ℕ) + 1)) := by
  simp [framePoly, eval₂_finsetSum]

theorem framePoly_map {B : Type*} [CommRing B] (φ : S →+* B) (n : ℕ) (c : Fin n → S) :
    (framePoly n c).map φ = framePoly n (fun i => φ (c i)) := by
  simp [framePoly, Polynomial.map_sum]

theorem coeff_framePoly_sub (n : ℕ) (c : Fin n → S) (i : Fin n) :
    (framePoly n c).coeff (n - ((i : ℕ) + 1)) = c i := by
  classical
  have hi := i.2
  simp only [framePoly, coeff_add, coeff_X_pow, finsetSum_coeff, coeff_C_mul_X_pow]
  rw [ite_eq_right (by omega), zero_add]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hji
    rw [ite_eq_right]
    intro h
    apply hji
    ext
    have := j.2
    omega
  · simp

theorem coeff_framePoly_self (n : ℕ) (c : Fin n → S) : (framePoly n c).coeff n = 1 := by
  classical
  simp only [framePoly, coeff_add, coeff_X_pow, finsetSum_coeff, coeff_C_mul_X_pow]
  rw [Finset.sum_eq_zero fun i _ => by rw [ite_eq_right (by have := i.2; omega)]]
  simp

theorem degree_sum_framePoly_lt (n : ℕ) (c : Fin n → S) :
    (∑ i : Fin n, C (c i) * X ^ (n - ((i : ℕ) + 1))).degree < (n : WithBot ℕ) := by
  refine lt_of_le_of_lt (degree_sum_le _ _) ?_
  refine (Finset.sup_lt_iff (WithBot.bot_lt_coe n)).mpr fun i _ => ?_
  refine lt_of_le_of_lt (degree_C_mul_X_pow_le _ _) ?_
  have := i.2
  exact Nat.cast_lt.mpr (by omega)

theorem framePoly_monic [Nontrivial S] (n : ℕ) (c : Fin n → S) : (framePoly n c).Monic := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [framePoly]
  exact monic_X_pow_add (degree_sum_framePoly_lt n c)

theorem natDegree_framePoly [Nontrivial S] (n : ℕ) (c : Fin n → S) :
    (framePoly n c).natDegree = n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [framePoly]
  rw [framePoly, natDegree_add_eq_left_of_degree_lt, natDegree_X_pow]
  rw [degree_X_pow]
  exact degree_sum_framePoly_lt n c

/-- A monic polynomial of degree `n` is `framePoly n` of its coefficients. -/
theorem eq_framePoly_of_monic [Nontrivial S] {q : S[X]} (hq : q.Monic) {n : ℕ}
    (hd : q.natDegree = n) :
    q = framePoly n (fun i => q.coeff (n - ((i : ℕ) + 1))) := by
  ext k
  rcases lt_trichotomy k n with hk | rfl | hk
  · have := coeff_framePoly_sub n (fun i => q.coeff (n - ((i : ℕ) + 1))) ⟨n - (k + 1), by omega⟩
    simp only at this
    rw [show n - (n - (k + 1) + 1) = k by omega] at this
    rw [this]
  · rw [coeff_framePoly_self, ← hd]
    exact hq
  · rw [coeff_eq_zero_of_natDegree_lt (by omega), coeff_eq_zero_of_natDegree_lt]
    rw [natDegree_framePoly]
    exact hk

/-- The `(n-1)`-st Hasse derivative of `Zⁿ + c₀Zⁿ⁻¹ + ⋯` is `nZ + c₀`. -/
theorem hasseDeriv_pred_framePoly (n : ℕ) (hn : 0 < n) (c : Fin n → S) :
    hasseDeriv (n - 1) (framePoly n c) = C (n : S) * X + C (c ⟨0, hn⟩) := by
  classical
  have h1 : hasseDeriv (n - 1) (X ^ n : S[X]) = C (n : S) * X := by
    rw [← monomial_one_right_eq_X_pow, hasseDeriv_monomial, show n - (n - 1) = 1 by omega,
      Nat.choose_symm_of_eq_add (by omega : n = (n - 1) + 1), Nat.choose_one_right, mul_one,
      ← C_mul_X_pow_eq_monomial, pow_one]
  have hsum : ∀ i : Fin n, hasseDeriv (n - 1) (C (c i) * X ^ (n - ((i : ℕ) + 1))) =
      if i = ⟨0, hn⟩ then C (c i) else 0 := by
    intro i
    rw [C_mul_X_pow_eq_monomial, hasseDeriv_monomial]
    split_ifs with h0
    · subst h0
      simp only
      rw [show n - (0 + 1) = n - 1 by omega, Nat.choose_self, Nat.sub_self, Nat.cast_one,
        one_mul, monomial_zero_left]
    · have : (i : ℕ) ≠ 0 := fun h => h0 (Fin.ext h)
      rw [Nat.choose_eq_zero_of_lt (by omega), Nat.cast_zero, zero_mul, monomial_zero_right]
  simp only [framePoly, map_add, map_sum, h1, hsum]
  rw [Finset.sum_ite_eq' Finset.univ, ite_eq_left (Finset.mem_univ _)]

/-- The substitution `x = z + d` (proof of Lemma 22, p. 265: "We write `f` in the form
`f = z^ν + g'_1 z^{ν-1} + ⋯ + g'_ν` with `g'_j ∈ S`. Then `g'_1 = νh`"): the coefficients
`c'` of `Zⁿ + Σ c_i Zⁿ⁻⁽ⁱ⁺¹⁾` in `Z - d` satisfy `c'₀ = nd + c₀`. -/
theorem exists_framePoly_shift [Nontrivial S] (n : ℕ) (hn : 0 < n) (c : Fin n → S) (d : S) :
    ∃ c' : Fin n → S, c' ⟨0, hn⟩ = n * d + c ⟨0, hn⟩ ∧
      ∀ {B : Type*} [CommRing B] (φ : S →+* B) (x : B),
        x ^ n + ∑ i : Fin n, φ (c i) * x ^ (n - ((i : ℕ) + 1)) =
          (x - φ d) ^ n + ∑ i : Fin n, φ (c' i) * (x - φ d) ^ (n - ((i : ℕ) + 1)) := by
  set q := taylor d (framePoly n c) with hq
  have hqm : q.Monic := by
    rw [Monic, hq, leadingCoeff_taylor]; exact framePoly_monic n c
  have hqd : q.natDegree = n := by rw [hq, natDegree_taylor, natDegree_framePoly]
  refine ⟨fun i => q.coeff (n - ((i : ℕ) + 1)), ?_, fun φ x => ?_⟩
  · simp only [hq, taylor_coeff, show n - (0 + 1) = n - 1 by omega,
      hasseDeriv_pred_framePoly n hn c, eval_add, eval_mul, eval_C, eval_X]
  · rw [← framePoly_eval₂, ← framePoly_eval₂, ← eq_framePoly_of_monic hqm hqd,
      eval₂_eq_eval_map, eval₂_eq_eval_map, hq, map_taylor, taylor_eval, sub_add_cancel]

end FramePoly

end

end Hironaka
