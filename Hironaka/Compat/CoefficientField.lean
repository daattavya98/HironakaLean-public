/-
Copyright (c) 2026 Daattavya Aggarwal, Minhyong Kim, Oisin Kim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daattavya Aggarwal, Minhyong Kim, Oisin Kim
-/
module

public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
public import Mathlib.RingTheory.MvPowerSeries.Rename
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Architect
public import Hironaka.Ch3.Frames
public import Hironaka.Compat.MvPowerSeriesRegular
public import Hironaka.Statements

/-!
# Compatibility layer: coefficient fields and the power series expansion of a complete regular
# local ring (Ch. III §9; Ch. IV §3, p. 297)

The ring-theoretic facts behind "By Cohen's structure theorem of a complete regular local ring, we
have a subfield `k` of `Ŝ` and a regular system of parameters `(z, y₁, …, y_{N-1})` of `Ŝ` such
that `Ŝ = k{z, y₁, …, y_{N-1}}`" (Ch. IV, p. 297), and "`R = k{z₁, …, z_r, x₁, …, x_s}` by the
structure theorem of a complete regular local ring (equi-characteristic)" (Ch. III, Lemma 25,
p. 269):

* the power series expansion of a regular frame is an isomorphism for a complete ring, and it
  transforms `ν_M` into the order of power series (`RegularFrame.bijective_of_isExpansion`,
  `RegularFrame.order_eq_ordElem_of_isExpansion`);
* the cited leaf `exists_residue_comp_eq_id_of_isAdicComplete_of_ringChar_eq` (Cohen's coefficient field) and its
  consequence `exists_residue_comp_eq_id_of_isAdicComplete` (`thm:cohen-coefficient-field`);
* `RegularFrame.ofCoefficientField` and `exists_ringEquiv_mvPowerSeries_of_coefficientField`;
* the frame `(S; z₁, …, z_r)` with `S = k{y₁, …, y_m}` of such a ring, for any injective system
  `(z₁, …, z_r)` which extends to a regular system of parameters
  (`exists_regularFrame_of_extendsToRSOP`).

These declarations are kept in this file, upstream of `Hironaka/Ch3/JStability.lean`, where Lemma 25
and Theorem 9 need them.
-/

@[expose] public section

open IsLocalRing

namespace Hironaka

universe u

/-- An element of `(Z₁, …, Z_r)ⁿ` in `S{Z₁, …, Z_r}` has order at least `n` (the argument of the
private lemma `le_order_of_mem_pow_span_X_aux` of `Hironaka/Ch3/Frames.lean`). -/
theorem _root_.MvPowerSeries.le_order_of_mem_pow_span_range_X {S : Type u} [CommRing S] {r : ℕ}
    (n : ℕ) {f : MvPowerSeries (Fin r) S}
    (hf : f ∈ (Ideal.span (Set.range (MvPowerSeries.X : Fin r → MvPowerSeries (Fin r) S))) ^ n) :
    (n : ℕ∞) ≤ f.order := by
  induction n generalizing f with
  | zero => simp
  | succ n ih =>
    rw [pow_succ] at hf
    refine Submodule.mul_induction_on (C := fun f => ((n + 1 : ℕ) : ℕ∞) ≤ f.order) hf ?_ ?_
    · intro a ha b hb
      have h2 : (1 : ℕ∞) ≤ b.order := by
        refine Submodule.span_induction (p := fun b _ => (1 : ℕ∞) ≤ b.order) ?_ ?_ ?_ ?_ hb
        · rintro _ ⟨j, rfl⟩
          rw [MvPowerSeries.one_le_order_iff_constCoeff_eq_zero]
          exact MvPowerSeries.constantCoeff_X j
        · simp
        · intro x y _ _ hx hy
          exact (le_min hx hy).trans MvPowerSeries.min_order_le_add
        · intro c x _ hx
          rw [smul_eq_mul]
          exact (hx.trans le_add_self).trans MvPowerSeries.le_order_mul
      calc ((n + 1 : ℕ) : ℕ∞) = (n : ℕ∞) + 1 := by push_cast; rfl
        _ ≤ a.order + b.order := add_le_add (ih ha) h2
        _ ≤ (a * b).order := MvPowerSeries.le_order_mul
    · intro x y hx hy
      exact (le_min hx hy).trans MvPowerSeries.min_order_le_add

namespace RegularFrame

variable {R : Type u} [CommRing R] [IsRegularLocalRing R] (F : RegularFrame R)

/-- A power series expansion map sends `p(z₁, …, z_r)` to `p` for every polynomial `p` over
`S`. -/
theorem IsExpansion.map_aeval {e : R →+* MvPowerSeries (Fin F.r) F.S} (he : F.IsExpansion e)
    (p : MvPolynomial (Fin F.r) F.S) : e (MvPolynomial.aeval F.z p) = (p : MvPowerSeries _ _) := by
  induction p using MvPolynomial.induction_on with
  | C s =>
    rw [MvPolynomial.aeval_C, he.map_algebraMap, MvPolynomial.coe_C]
  | add p q hp hq => rw [map_add, map_add, hp, hq, MvPolynomial.coe_add]
  | mul_X p j hp =>
    rw [map_mul, map_mul, hp, MvPolynomial.aeval_X, he.map_z, MvPolynomial.coe_mul,
      MvPolynomial.coe_X]

/-- `p(z₁, …, z_r) ∈ Pⁿ` if all monomials of `p` have degree at least `n`. -/
theorem aeval_mem_pow (n : ℕ) (p : MvPolynomial (Fin F.r) F.S)
    (hp : ∀ A ∈ p.support, n ≤ A.degree) : MvPolynomial.aeval F.z p ∈ F.idealZ ^ n := by
  classical
  rw [p.as_sum, map_sum]
  refine Ideal.sum_mem _ fun A hA => ?_
  rw [MvPolynomial.aeval_monomial]
  refine Ideal.mul_mem_left _ _ (Ideal.pow_le_pow_right (hp A hA) ?_)
  have hz : ∀ i, F.z i ∈ F.idealZ := fun i => Ideal.subset_span ⟨i, rfl⟩
  have : ∏ i ∈ A.support, F.z i ^ A i ∈ ∏ i ∈ A.support, F.idealZ ^ A i :=
    Ideal.prod_mem_prod fun i _ => Ideal.pow_mem_pow (hz i) _
  rw [Finset.prod_pow_eq_pow_sum] at this
  exact this

/-- Every element of `Pⁿ` is, modulo `Pⁿ⁺¹`, a homogeneous polynomial of degree `n` over `S` in
`z₁, …, z_r` (`R = S + P`). -/
theorem exists_isHomogeneous_sub_mem_pow (n : ℕ) (a : R) (ha : a ∈ F.idealZ ^ n) :
    ∃ p : MvPolynomial (Fin F.r) F.S, p.IsHomogeneous n ∧
      a - MvPolynomial.aeval F.z p ∈ F.idealZ ^ (n + 1) := by
  classical
  have hR : ∀ r : R, ∃ s : F.S, r - algebraMap F.S R s ∈ F.idealZ := fun r => by
    obtain ⟨s, hs⟩ := F.quot_bijective.2 (Ideal.Quotient.mk _ r)
    refine ⟨s, ?_⟩
    rw [RingHom.comp_apply, Ideal.Quotient.eq] at hs
    rw [← neg_sub]
    exact neg_mem hs
  have hhom : ∀ (m : ℕ) (p : MvPolynomial (Fin F.r) F.S), p.IsHomogeneous m →
      MvPolynomial.aeval F.z p ∈ F.idealZ ^ m := fun m p hp =>
    F.aeval_mem_pow m p fun A hA => by
      have := hp (MvPolynomial.mem_support_iff.mp hA)
      rw [← this, Finsupp.degree_eq_weight_one]
      exact le_rfl
  -- the case `n = 1`
  have h1 : ∀ y ∈ F.idealZ, ∃ q : MvPolynomial (Fin F.r) F.S, q.IsHomogeneous 1 ∧
      y - MvPolynomial.aeval F.z q ∈ F.idealZ ^ 2 := by
    intro y hy
    obtain ⟨c, rfl⟩ := (Ideal.mem_span_range_iff_exists_fun).mp hy
    choose s hs using fun j => hR (c j)
    refine ⟨∑ j, MvPolynomial.C (s j) * MvPolynomial.X j,
      MvPolynomial.IsHomogeneous.sum _ _ _ fun j _ =>
        (MvPolynomial.isHomogeneous_X _ j).C_mul _, ?_⟩
    rw [map_sum, ← Finset.sum_sub_distrib, pow_two]
    refine Ideal.sum_mem _ fun j _ => ?_
    rw [map_mul, MvPolynomial.aeval_C, MvPolynomial.aeval_X, ← sub_mul]
    exact Ideal.mul_mem_mul (hs j) (Ideal.subset_span ⟨j, rfl⟩)
  induction n generalizing a with
  | zero =>
    obtain ⟨s, hs⟩ := hR a
    exact ⟨MvPolynomial.C s, MvPolynomial.isHomogeneous_C _ _, by
      rw [MvPolynomial.aeval_C, zero_add, pow_one]; exact hs⟩
  | succ n ih =>
    rw [pow_succ] at ha
    refine Submodule.mul_induction_on (C := fun a => ∃ p : MvPolynomial (Fin F.r) F.S,
      p.IsHomogeneous (n + 1) ∧ a - MvPolynomial.aeval F.z p ∈ F.idealZ ^ (n + 1 + 1)) ha ?_ ?_
    · intro x hx y hy
      obtain ⟨p, hp, hxp⟩ := ih x hx
      obtain ⟨q, hq, hyq⟩ := h1 y hy
      refine ⟨p * q, hp.mul hq, ?_⟩
      have e : x * y - MvPolynomial.aeval F.z (p * q) =
          (x - MvPolynomial.aeval F.z p) * y +
            MvPolynomial.aeval F.z p * (y - MvPolynomial.aeval F.z q) := by
        rw [map_mul]; ring
      rw [e]
      refine add_mem ?_ ?_
      · rw [pow_succ]; exact Ideal.mul_mem_mul hxp hy
      · rw [show n + 1 + 1 = n + 2 by omega, pow_add]
        exact Ideal.mul_mem_mul (hhom n p hp) hyq
    · rintro x y ⟨p, hp, hxp⟩ ⟨q, hq, hyq⟩
      refine ⟨p + q, hp.add hq, ?_⟩
      rw [map_add, show x + y - (MvPolynomial.aeval F.z p + MvPolynomial.aeval F.z q) =
        (x - MvPolynomial.aeval F.z p) + (y - MvPolynomial.aeval F.z q) by ring]
      exact add_mem hxp hyq

/-- For a regular frame `(S; z₁, …, z_r)` of `R`, with `R` complete for `P = (z₁, …, z_r)R`, the
power series expansion `R → S{z₁, …, z_r}` (`lem:III.9-frame-completion`) is a ring isomorphism:
an element of the kernel lies in every `Pⁿ` (`Pⁿ/Pⁿ⁺¹` is spanned by the monomials of degree `n`
in the `z_i` over `S`, `exists_isHomogeneous_sub_mem_pow`), hence is `0` (Krull); a power series
`Q` is the image of the limit of the `Q_{≤n}(z)`.  (Used for "`Ŝ = k{z, y₁, …, y_{N-1}}`",
p. 297.) -/
theorem bijective_of_isExpansion [IsAdicComplete F.idealZ R]
    {e : R →+* MvPowerSeries (Fin F.r) F.S} (he : F.IsExpansion e) : Function.Bijective e := by
  classical
  have hcoeff : ∀ (n : ℕ) (f : MvPowerSeries (Fin F.r) F.S),
      f ∈ (Ideal.span (Set.range (MvPowerSeries.X : Fin F.r → _))) ^ n →
      ∀ A : Fin F.r →₀ ℕ, A.degree < n → MvPowerSeries.coeff A f = 0 := fun n f hf A hA =>
    MvPowerSeries.coeff_of_lt_order ((Nat.cast_lt.mpr hA).trans_le
      (MvPowerSeries.le_order_of_mem_pow_span_range_X n hf))
  refine ⟨(injective_iff_map_eq_zero e).mpr fun a ha => ?_, fun Q => ?_⟩
  · have hmem : ∀ n, a ∈ F.idealZ ^ n := by
      intro n
      induction n with
      | zero => simp
      | succ n ih =>
        obtain ⟨p, hp, hap⟩ := F.exists_isHomogeneous_sub_mem_pow n a ih
        have h1 := he.map_pow (n + 1) _ hap
        rw [map_sub, ha, zero_sub, he.map_aeval, neg_mem_iff] at h1
        have hp0 : p = 0 := by
          ext A
          by_cases hA : A.degree = n
          · have := hcoeff (n + 1) _ h1 A (by omega)
            rwa [MvPolynomial.coeff_coe] at this
          · by_contra hne
            exact hA (by rw [Finsupp.degree_eq_weight_one]; exact hp hne)
        rw [hp0, map_zero, sub_zero] at hap
        exact hap
    refine IsHausdorff.haus (I := F.idealZ) inferInstance a fun n => ?_
    rw [SModEq.zero, smul_eq_mul, Ideal.mul_top]
    exact hmem n
  · let a : ℕ → R := fun n => MvPolynomial.aeval F.z (MvPowerSeries.truncTotal n Q)
    have hcauchy : ∀ {m n : ℕ}, m ≤ n → a m ≡ a n [SMOD (F.idealZ ^ m • ⊤ : Submodule R R)] := by
      intro m n hmn
      rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, ← map_sub]
      refine F.aeval_mem_pow m _ fun A hA => ?_
      by_contra hlt
      push Not at hlt
      apply MvPolynomial.mem_support_iff.mp hA
      rw [MvPolynomial.coeff_sub, MvPowerSeries.coeff_truncTotal _ hlt,
        MvPowerSeries.coeff_truncTotal _ (hlt.trans_le hmn), sub_self]
    obtain ⟨L, hL⟩ := IsPrecomplete.prec' (I := F.idealZ) a hcauchy
    refine ⟨L, MvPowerSeries.ext fun A => ?_⟩
    have h := hL (A.degree + 1)
    rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top] at h
    have h2 := hcoeff _ _ (he.map_pow _ _ h) A (by omega)
    rw [map_sub, he.map_aeval, map_sub, MvPolynomial.coeff_coe,
      MvPowerSeries.coeff_truncTotal _ (by omega), sub_eq_zero] at h2
    exact h2.symm

/-- The power series expansion preserves orders: `ord(e(x)) = ν_P(x)` for `P = (z₁, …, z_r)R`
(`exists_isHomogeneous_sub_mem_pow`: the leading form of `x` is a non-zero homogeneous
polynomial of degree `ν_P(x)` in the `z_i`). -/
theorem order_eq_ordElem_of_isExpansion {e : R →+* MvPowerSeries (Fin F.r) F.S}
    (he : F.IsExpansion e) (x : R) : (e x).order = Ideal.ordElem F.idealZ x := by
  classical
  refine le_antisymm ?_ (Ideal.ordElem_le fun ν hν =>
    MvPowerSeries.le_order_of_mem_pow_span_range_X ν (he.map_pow ν x hν))
  rcases eq_or_ne (Ideal.ordElem F.idealZ x) ⊤ with h | h
  · rw [h]; exact le_top
  obtain ⟨d, hd⟩ := ENat.ne_top_iff_exists.mp h
  rw [← hd]
  have hxd : x ∈ F.idealZ ^ d := Ideal.mem_pow_of_ordElem hd.symm
  have hxd1 : x ∉ F.idealZ ^ (d + 1) := fun h1 => by
    have := Ideal.le_ordElem h1
    rw [← hd, Nat.cast_le] at this
    omega
  obtain ⟨p, hp, hxp⟩ := F.exists_isHomogeneous_sub_mem_pow d x hxd
  have hp0 : p ≠ 0 := by
    rintro rfl
    rw [map_zero, sub_zero] at hxp
    exact hxd1 hxp
  obtain ⟨A, hA⟩ : p.support.Nonempty :=
    Finset.nonempty_iff_ne_empty.mpr (mt MvPolynomial.support_eq_empty.mp hp0)
  have hAdeg : A.degree = d := by
    rw [Finsupp.degree_eq_weight_one]
    exact hp (MvPolynomial.mem_support_iff.mp hA)
  have hcoeff : MvPowerSeries.coeff A (e x) ≠ 0 := by
    have h1 := he.map_pow (d + 1) _ hxp
    have h2 : MvPowerSeries.coeff A (e (x - MvPolynomial.aeval F.z p)) = 0 :=
      MvPowerSeries.coeff_of_lt_order ((show ((A.degree : ℕ) : ℕ∞) < ((d + 1 : ℕ) : ℕ∞) by
        exact_mod_cast (show A.degree < d + 1 by omega)).trans_le
          (MvPowerSeries.le_order_of_mem_pow_span_range_X _ h1))
    rw [map_sub, he.map_aeval, map_sub, MvPolynomial.coeff_coe, sub_eq_zero] at h2
    rw [h2]
    exact MvPolynomial.mem_support_iff.mp hA
  calc (e x).order ≤ (A.degree : ℕ∞) := MvPowerSeries.order_le hcoeff
    _ = d := by rw [hAdeg]

/-- For a regular frame `(S; z₁, …, z_r)` of `R`, an element `s` of `S` lies in `Nᵈ` as soon as
it lies in `Mᵈ` in `R` (`N`, `M` the maximal ideals): `R → R/P ≅ S` maps `M` into `N`. -/
theorem mem_maximalIdeal_pow_of_algebraMap_mem_pow {s : F.S} {d : ℕ}
    (hs : algebraMap F.S R s ∈ maximalIdeal R ^ d) : s ∈ maximalIdeal F.S ^ d := by
  classical
  let e := RingEquiv.ofBijective _ F.quot_bijective
  let π : R →+* F.S :=
    e.symm.toRingHom.comp (Ideal.Quotient.mk (Ideal.span (Set.range F.z)))
  have hπ : ∀ t, π (algebraMap F.S R t) = t := fun t => e.symm_apply_apply t
  have hP : Ideal.span (Set.range F.z) ≤ maximalIdeal R := by
    obtain ⟨s₀, hsub, hs₀⟩ := F.extends_rsop
    refine Ideal.span_le.mpr ?_
    rintro _ ⟨i, rfl⟩
    rw [← hs₀.1]
    exact Ideal.subset_span (hsub (Finset.mem_image_of_mem _ (Finset.mem_univ i)))
  have hM : (maximalIdeal R).map π ≤ maximalIdeal F.S := by
    rw [Ideal.map_le_iff_le_comap]
    intro y hy
    rw [Ideal.mem_comap]
    have hsub : y - algebraMap F.S R (π y) ∈ Ideal.span (Set.range F.z) := by
      rw [← Ideal.Quotient.eq]
      exact (e.apply_symm_apply (Ideal.Quotient.mk _ y)).symm
    have h2 : algebraMap F.S R (π y) ∈ maximalIdeal R := by
      have := sub_mem hy (hP hsub)
      rwa [sub_sub_cancel] at this
    rw [mem_maximalIdeal, mem_nonunits_iff] at h2 ⊢
    exact fun hu => h2 (hu.map (algebraMap F.S R))
  have := Ideal.mem_map_of_mem π hs
  rw [Ideal.map_pow, hπ] at this
  exact Ideal.pow_right_mono hM d this

end RegularFrame

/-! ### Coefficient fields (Cohen) -/


/-- Cited (p. 258: "Then `R` is a formal power series ring over a field, by Cohen's structure
theorem."; p. 297: "By Cohen's structure theorem of a complete regular local ring, we have a
subfield `k` of `Ŝ` …"): a complete noetherian local ring `R` of equal characteristic (`ringChar R`
equals the characteristic of the residue field) has a coefficient field, i.e. the residue map
`R → R/M` has a ring section `σ` (`k = σ(R/M)`).  Not proved in the paper: I. S. Cohen, *On the
structure and ideal theory of complete local rings*, Trans. Amer. Math. Soc. 59 (1946), 54–106;
Matsumura, *Commutative Ring Theory*, §28.  This is the only coefficient-field leaf of the
project: the case of residue characteristic zero, used in Ch. IV, is
`exists_residue_comp_eq_id_of_isAdicComplete`.

Encoding: "a subfield `k` of `R` which the residue map sends isomorphically onto `R/M`" is a ring
homomorphism `σ : R/M → R` with `residue ∘ σ = id`.  The project's other Cohen leaf,
`exists_surjective_of_isRegularLocalRing_of_isAdicComplete` (p. 200), is the other half of
Cohen's theorem (a complete local ring is a quotient of a complete regular local ring) and does
not provide a coefficient field. -/
@[blueprint "thm:cohen-coefficient-field-equal-characteristic"
  (statement := /-- (Cohen; coefficient fields in equal characteristic.) Let $R$ be a complete
    noetherian local ring with maximal ideal $M$ which has the same characteristic as its residue
    field $R/M$. Then $R$ has a coefficient field: a subfield $k$ of $R$ which the residue map
    $R\to R/M$ maps isomorphically onto $R/M$. (Cited in the proof of \cref{prop:III.8-2},
    p.~258: ``Then $R$ is a formal power series ring over a field, by Cohen's structure
    theorem'', and in the proof of \cref{lem:IV.3-setup-exists}, p.~297: ``By Cohen's structure
    theorem of a complete regular local ring, we have a subfield $k$ of $\hat S$ \dots''.) -/)
  (proof := /-- Cited: I.~S.~Cohen, On the structure and ideal theory of complete local
    rings, Trans.\ Amer.\ Math.\ Soc.\ 59 (1946); Matsumura, \emph{Commutative Ring Theory},
    \S28. -/)
  (latexEnv := "theorem")]
theorem exists_residue_comp_eq_id_of_isAdicComplete_of_ringChar_eq [Hironaka.Cited.ExistsResidueCompEqIdOfIsAdicCompleteOfRingCharEq.{u}] :
    ∀ (R : Type u) [CommRing R]
    [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R]
    (hchar : ringChar R = ringChar (ResidueField R)),
    ∃ σ : ResidueField R →+* R, (IsLocalRing.residue R).comp σ = RingHom.id _ :=
  @Hironaka.Cited.ExistsResidueCompEqIdOfIsAdicCompleteOfRingCharEq.exists_residue_comp_eq_id_of_isAdicComplete_of_ringChar_eq _

/-- Cohen's coefficient field (p. 297: "By Cohen's structure theorem of a complete regular local
ring, we have a subfield `k` of `Ŝ` …"): a complete noetherian local ring whose residue field has
characteristic zero has a coefficient field.  This is the special case of the cited leaf
`exists_residue_comp_eq_id_of_isAdicComplete_of_ringChar_eq`: if the residue field has
characteristic zero, so has `R` (a positive integer which is zero in `R` is zero in the residue
field). -/
@[blueprint "thm:cohen-coefficient-field"
  (statement := /-- (Cohen; coefficient fields.) Let $R$ be a complete noetherian local ring
    with maximal ideal $M$ whose residue field $R/M$ has characteristic zero. Then $R$ has a
    coefficient field: a subfield $k$ of $R$ which the residue map $R\to R/M$ maps
    isomorphically onto $R/M$. (Cited in the proof of \cref{lem:IV.3-setup-exists}, p.~297:
    ``By Cohen's structure theorem of a complete regular local ring, we have a subfield $k$ of
    $\hat S$ \dots''.) -/)
  (proof := /-- The special case of
    \cref{thm:cohen-coefficient-field-equal-characteristic}: if $R/M$ has characteristic zero, so
    has $R$, since $\mathbb Z\to R\to R/M$ is injective. -/)
  (latexEnv := "theorem")]
theorem exists_residue_comp_eq_id_of_isAdicComplete [Hironaka.Cited.ExistsResidueCompEqIdOfIsAdicCompleteOfRingCharEq.{u}] (R : Type u) [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R] [CharZero (ResidueField R)] :
    ∃ σ : ResidueField R →+* R, (IsLocalRing.residue R).comp σ = RingHom.id _ := by
  have _ : CharZero R := (IsLocalRing.residue R).charZero
  exact exists_residue_comp_eq_id_of_isAdicComplete_of_ringChar_eq R
    ((ringChar.eq R 0).trans (ringChar.eq (ResidueField R) 0).symm)

open Classical in
/-- The regular frame `(k; x₁, …, x_n)` of `R` given by a coefficient field `k = σ(R/M)` and a
regular system of parameters `(x₁, …, x_n)` (p. 297). -/
noncomputable def RegularFrame.ofCoefficientField {R : Type u} [CommRing R] [IsRegularLocalRing R]
    (σ : ResidueField R →+* R) (hσ : (IsLocalRing.residue R).comp σ = RingHom.id _) {n : ℕ}
    (x : Fin n → R) (hx : Function.Injective x)
    (hxs : IsRegularSystemOfParameters R (Finset.univ.image x)) : RegularFrame R where
  S := ResidueField R
  algebra := σ.toAlgebra
  isLocalHom := inferInstance
  r := n
  z := x
  z_injective := hx
  extends_rsop := ⟨_, subset_rfl, hxs⟩
  quot_bijective := by
    have hspan : Ideal.span (Set.range x) = maximalIdeal R := by
      rw [← hxs.1, Finset.coe_image, Finset.coe_univ, Set.image_univ]
    rw [hspan]
    have : (Ideal.Quotient.mk (maximalIdeal R)).comp σ = RingHom.id _ := hσ
    exact this ▸ Function.bijective_id

open Classical in
/-- p. 297, Cohen's structure theorem in the form `R = k{x₁, …, x_n}`: for a coefficient field
`k = σ(R/M)` of a complete regular local ring `R` and a regular system of parameters
`(x₁, …, x_n)` of `R`, the power series expansion of Ch. III, §9 with respect to the regular frame
`(k; x₁, …, x_n)` is a ring isomorphism `R ≃ k{X₁, …, X_n}` with `x_i ↦ X_i`, `σ(t) ↦ t`; it
transforms the order `ν_M` into the order of power series. -/
theorem exists_ringEquiv_mvPowerSeries_of_coefficientField {R : Type u} [CommRing R]
    [IsRegularLocalRing R] [IsAdicComplete (maximalIdeal R) R] (σ : ResidueField R →+* R)
    (hσ : (IsLocalRing.residue R).comp σ = RingHom.id _) {n : ℕ} (x : Fin n → R)
    (hx : Function.Injective x) (hxs : IsRegularSystemOfParameters R (Finset.univ.image x)) :
    ∃ Φ : R ≃+* MvPowerSeries (Fin n) (ResidueField R),
      (∀ i, Φ (x i) = MvPowerSeries.X i) ∧ (∀ t, Φ (σ t) = MvPowerSeries.C t) ∧
      ∀ a, (Φ a).order = Ideal.ordElem (maximalIdeal R) a := by
  classical
  let F := RegularFrame.ofCoefficientField σ hσ x hx hxs
  have hspan : F.idealZ = maximalIdeal R := by
    show Ideal.span (Set.range x) = maximalIdeal R
    rw [← hxs.1, Finset.coe_image, Finset.coe_univ, Set.image_univ]
  have : IsAdicComplete F.idealZ R := by rw [hspan]; infer_instance
  obtain ⟨-, -, e, he, -⟩ := F.idealZ_isPrime_and_completion
  let e' : R →+* MvPowerSeries (Fin n) (ResidueField R) := e
  refine ⟨RingEquiv.ofBijective e' (F.bijective_of_isExpansion he), fun i => he.map_z i,
    fun t => he.map_algebraMap t, fun a => ?_⟩
  have h := F.order_eq_ordElem_of_isExpansion he a
  rw [hspan] at h
  exact h

section SubVariables

open _root_.MvPowerSeries

variable {K : Type u} [CommRing K] {r m : ℕ}

/-- A power series in `Z₁, …, Z_r, Y₁, …, Y_m` all of whose monomials without a `Z` have
coefficient zero lies in the ideal generated by `Z₁, …, Z_r`: `P = Σ Z_i Q_i` with
`Q_i(d) = P(d + e_i)` if `d_j = 0` for all `j < i`, and `0` otherwise. -/
theorem mem_span_X_castAdd_of_coeff_eq_zero {P : MvPowerSeries (Fin (r + m)) K}
    (hP : ∀ d : Fin (r + m) →₀ ℕ, (∀ j : Fin r, d (Fin.castAdd m j) = 0) → coeff d P = 0) :
    P ∈ Ideal.span (Set.range fun j : Fin r =>
      (X (Fin.castAdd m j) : MvPowerSeries (Fin (r + m)) K)) := by
  classical
  let g : Fin r → MvPowerSeries (Fin (r + m)) K := fun i d =>
    if ∀ j : Fin r, j < i → d (Fin.castAdd m j) = 0 then
      coeff (d + Finsupp.single (Fin.castAdd m i) 1) P else 0
  have hg : ∀ (i : Fin r) (d : Fin (r + m) →₀ ℕ), coeff d (g i) =
      if ∀ j : Fin r, j < i → d (Fin.castAdd m j) = 0 then
        coeff (d + Finsupp.single (Fin.castAdd m i) 1) P else 0 := fun _ _ => rfl
  have key : P = ∑ i, X (Fin.castAdd m i) * g i := by
    ext d
    rw [map_sum]
    simp only [X, coeff_monomial_mul]
    by_cases hd0 : ∀ j : Fin r, d (Fin.castAdd m j) = 0
    · rw [hP d hd0]
      symm
      refine Finset.sum_eq_zero fun x _ => ?_
      have hx : ¬ (Finsupp.single (Fin.castAdd m x) 1 ≤ d) := by
        intro hx
        have := Finsupp.single_le_iff.mp hx
        have := hd0 x
        omega
      simp [hx]
    · push Not at hd0
      obtain ⟨i₀, hi₀, hmin⟩ : ∃ i₀ : Fin r, 1 ≤ d (Fin.castAdd m i₀) ∧
          ∀ j : Fin r, j < i₀ → d (Fin.castAdd m j) = 0 := by
        have hne : (Finset.univ.filter fun i : Fin r => 1 ≤ d (Fin.castAdd m i)).Nonempty := by
          obtain ⟨j, hj⟩ := hd0
          exact ⟨j, by simp; omega⟩
        obtain ⟨i₀, hi₀mem, hi₀min⟩ := Finset.exists_min_image _ id hne
        refine ⟨i₀, (Finset.mem_filter.mp hi₀mem).2, fun j hj => ?_⟩
        by_contra hjm
        have : j ∈ Finset.univ.filter fun i : Fin r => 1 ≤ d (Fin.castAdd m i) := by
          simp; omega
        exact absurd (hi₀min j this) (not_le.mpr hj)
      rw [Finset.sum_eq_single i₀]
      · have hle : Finsupp.single (Fin.castAdd m i₀) 1 ≤ d := Finsupp.single_le_iff.mpr hi₀
        have hcond : ∀ j : Fin r, j < i₀ →
            (d - Finsupp.single (Fin.castAdd m i₀) 1 : Fin (r + m) →₀ ℕ) (Fin.castAdd m j) = 0 := by
          intro j hj
          have hne : Fin.castAdd m j ≠ Fin.castAdd m i₀ :=
            fun h => hj.ne (Fin.castAdd_injective _ _ h)
          simp [hne, hmin j hj]
        simp only [hle, ↓reduceIte, one_mul]
        rw [hg]
        rw [tsub_add_cancel_of_le hle]
        split_ifs
        rfl
      · intro i _ hne
        by_cases hle : Finsupp.single (Fin.castAdd m i) 1 ≤ d
        · have hnot : ¬ ∀ j : Fin r, j < i →
              (d - Finsupp.single (Fin.castAdd m i) 1 : Fin (r + m) →₀ ℕ)
                (Fin.castAdd m j) = 0 := by
            intro hall
            rcases lt_or_gt_of_ne hne with hlt | hlt
            · have := hmin i hlt
              have h1 := Finsupp.single_le_iff.mp hle
              omega
            · have := hall i₀ hlt
              have hne' : Fin.castAdd m i₀ ≠ Fin.castAdd m i :=
                fun h => hlt.ne (Fin.castAdd_injective _ _ h)
              simp [hne'] at this
              omega
          simp only [hle, ↓reduceIte, one_mul]
          rw [hg]
          split_ifs
          rfl
        · simp [hle]
      · intro h; exact absurd (Finset.mem_univ _) h
  rw [key]
  exact Ideal.sum_mem _ fun i _ => Ideal.mul_mem_right _ _ (Ideal.subset_span ⟨i, rfl⟩)

/-- The embedding `Y_i ↦ Y_i` of the last `m` variables into `Z₁, …, Z_r, Y₁, …, Y_m`. -/
def natAddEmbedding (r m : ℕ) : Fin m ↪ Fin (r + m) := ⟨Fin.natAdd r, Fin.natAdd_injective m r⟩

/-- A monomial without a `Z` is the image of a monomial in the `Y_i`. -/
theorem exists_embDomain_eq_of_forall_castAdd_eq_zero {d : Fin (r + m) →₀ ℕ}
    (hd : ∀ j : Fin r, d (Fin.castAdd m j) = 0) :
    ∃ x : Fin m →₀ ℕ, Finsupp.embDomain (natAddEmbedding r m) x = d := by
  classical
  refine ⟨Finsupp.comapDomain (Fin.natAdd r) d (Fin.natAdd_injective m r).injOn, ?_⟩
  ext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · rw [hd j]
    exact Finsupp.embDomain_of_notMem_range _ _ _ (by
      rintro ⟨y, hy⟩
      have := congrArg Fin.val hy
      simp [natAddEmbedding] at this
      omega)
  · rw [show Fin.natAdd r j = natAddEmbedding r m j from rfl, Finsupp.embDomain_apply_self]
    rfl

/-- The kernel of "set `Z = 0`" is the ideal generated by `Z₁, …, Z_r`. -/
theorem mem_span_X_castAdd_of_killCompl_eq_zero {P : MvPowerSeries (Fin (r + m)) K}
    (hP : MvPowerSeries.killCompl (R := K) (natAddEmbedding r m) P = 0) :
    P ∈ Ideal.span (Set.range fun j : Fin r =>
      (X (Fin.castAdd m j) : MvPowerSeries (Fin (r + m)) K)) := by
  refine mem_span_X_castAdd_of_coeff_eq_zero fun d hd => ?_
  obtain ⟨x, rfl⟩ := exists_embDomain_eq_of_forall_castAdd_eq_zero hd
  rw [← coeff_killCompl, hP]
  simp

end SubVariables


section FrameExistence

open _root_.MvPowerSeries

variable {R : Type u} [CommRing R] [IsRegularLocalRing R] {K : Type u} [Field K] {r m : ℕ}

open Classical in
/-- p. 269: "We have a subfield `k` of `R` such that `R = k{z₁, …, z_r, x₁, …, x_s}`", and
`S = k{x₁, …, x_s}`: if `Φ : R ≃ K{Z₁, …, Z_r, Y₁, …, Y_m}` sends `z_j` to `Z_j`, then
`S = Φ⁻¹(K{Y₁, …, Y_m})` gives a regular frame `(S; z₁, …, z_r)` of `R` (generalizing the case
`r = 1` of p. 297, `exists_regularFrame_one_of_ringEquiv_mvPowerSeries`); the coefficient ring is
`K{Y}` itself, mapped into `R` by `Y_i ↦ Φ⁻¹(Y_i)`. -/
theorem exists_regularFrame_of_ringEquiv_mvPowerSeries
    (Φ : R ≃+* MvPowerSeries (Fin (r + m)) K) {z : Fin r → R} (hinj : Function.Injective z)
    (hz : ExtendsToRSOP R (Finset.image z Finset.univ))
    (hΦz : ∀ j, Φ (z j) = X (Fin.castAdd m j)) :
    ∃ (F : RegularFrame R) (h : F.r = r), (∀ j, F.z (Fin.cast h.symm j) = z j) ∧
      ∃ ET : F.S ≃+* MvPowerSeries (Fin m) K, ∀ s,
        Φ (algebraMap F.S R s) = MvPowerSeries.rename (Fin.natAdd r) (ET s) := by
  classical
  let e : Fin m ↪ Fin (r + m) := natAddEmbedding r m
  let ι : MvPowerSeries (Fin m) K →+* R :=
    Φ.symm.toRingHom.comp (MvPowerSeries.rename (R := K) (Fin.natAdd r)).toRingHom
  let ρ : MvPowerSeries (Fin (r + m)) K →+* MvPowerSeries (Fin m) K :=
    (MvPowerSeries.killCompl (R := K) e).toRingHom
  have hρι : ∀ g, ρ (MvPowerSeries.rename (R := K) (Fin.natAdd r) g) = g := fun g =>
    MvPowerSeries.killCompl_rename_app g
  have hρX : ∀ j : Fin r, ρ (X (Fin.castAdd m j)) = 0 := fun j =>
    MvPowerSeries.killCompl_X_eq_zero (by
      rintro ⟨i, hi⟩
      have := congrArg Fin.val hi
      simp [e, natAddEmbedding] at this
      omega)
  have hker : Ideal.span (Set.range fun j : Fin r =>
      (X (Fin.castAdd m j) : MvPowerSeries (Fin (r + m)) K)) ≤ RingHom.ker ρ := by
    refine Ideal.span_le.mpr ?_
    rintro _ ⟨j, rfl⟩
    exact hρX j
  set P : Ideal R := Ideal.span (Set.range z) with hP
  have hmapP : Ideal.map Φ P = Ideal.span (Set.range fun j : Fin r =>
      (X (Fin.castAdd m j) : MvPowerSeries (Fin (r + m)) K)) := by
    rw [hP, Ideal.map_span, ← Set.range_comp]
    congr 1
    ext x
    simp [hΦz]
  have hmem : ∀ x, x ∈ P ↔ Φ x ∈ Ideal.span (Set.range fun j : Fin r =>
      (X (Fin.castAdd m j) : MvPowerSeries (Fin (r + m)) K)) := by
    intro x
    rw [← hmapP]
    constructor
    · exact fun h => Ideal.mem_map_of_mem Φ h
    · intro h
      obtain ⟨x', hx', hx'e⟩ := (Ideal.mem_map_of_equiv Φ _).mp h
      rwa [← Φ.injective hx'e]
  let φ : MvPowerSeries (Fin m) K →+* R ⧸ P := (Ideal.Quotient.mk P).comp ι
  have hφ : Function.Bijective φ := by
    refine ⟨(injective_iff_map_eq_zero φ).mpr fun g hg => ?_, fun w => ?_⟩
    · rw [RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem, hmem] at hg
      have h1 : Φ (ι g) = MvPowerSeries.rename (R := K) (Fin.natAdd r) g :=
        Φ.apply_symm_apply _
      rw [h1] at hg
      have := hker hg
      rwa [RingHom.mem_ker, hρι] at this
    · obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective w
      refine ⟨ρ (Φ a), ?_⟩
      rw [RingHom.comp_apply, Ideal.Quotient.eq, ← Ideal.neg_mem_iff, neg_sub, hmem, map_sub]
      have h1 : Φ (ι (ρ (Φ a))) = MvPowerSeries.rename (R := K) (Fin.natAdd r) (ρ (Φ a)) :=
        Φ.apply_symm_apply _
      rw [h1]
      refine mem_span_X_castAdd_of_killCompl_eq_zero ?_
      show ρ _ = 0
      rw [map_sub, hρι, sub_self]
  have hreg : IsRegularLocalRing (MvPowerSeries (Fin m) K) := isRegularLocalRing_mvPowerSeries K m
  let eφ := RingEquiv.ofBijective φ hφ
  have hloc : IsLocalHom ι := ⟨fun t ht => by
    have h1 : IsUnit (φ t) := ht.map (Ideal.Quotient.mk P)
    have h2 : IsUnit (eφ.symm (φ t)) := h1.map eφ.symm
    rwa [show eφ.symm (φ t) = t from eφ.symm_apply_apply t] at h2⟩
  let F : RegularFrame R :=
    { S := MvPowerSeries (Fin m) K
      algebra := ι.toAlgebra
      isRegular := hreg
      isLocalHom := hloc
      r := r
      z := z
      z_injective := hinj
      extends_rsop := hz
      quot_bijective := hφ }
  refine ⟨F, rfl, fun j => rfl, RingEquiv.refl _, fun s => ?_⟩
  show Φ (Φ.symm _) = _
  rw [Φ.apply_symm_apply]
  rfl

end FrameExistence


section Enumeration

open _root_.MvPowerSeries

/-- The members of an injective system `z` contained in a finite set `s` can be put first in an
enumeration of `s`. -/
theorem exists_injective_append_enumeration {A : Type u} [DecidableEq A] {r : ℕ}
    {z : Fin r → A} (hinj : Function.Injective z) {s : Finset A}
    (hts : Finset.image z Finset.univ ⊆ s) :
    ∃ (m : ℕ) (x : Fin (r + m) → A), Function.Injective x ∧
      (∀ j, x (Fin.castAdd m j) = z j) ∧ Finset.univ.image x = s ∧ r + m = s.card := by
  set t : Finset A := s \ Finset.image z Finset.univ with htdef
  let u : Fin t.card → A := fun i => (t.equivFin.symm i : A)
  have huinj : Function.Injective u := Subtype.val_injective.comp t.equivFin.symm.injective
  have hzmem : ∀ i, z i ∈ Finset.image z Finset.univ := fun i =>
    Finset.mem_image_of_mem z (Finset.mem_univ i)
  have hunot : ∀ j, u j ∉ Finset.image z Finset.univ := fun j =>
    (Finset.mem_sdiff.mp (t.equivFin.symm j).2).2
  set y : Fin (r + t.card) → A := Fin.append z u with hydef
  have hyinj : Function.Injective y := by
    intro a b hab
    induction a using Fin.addCases with
    | left i =>
      induction b using Fin.addCases with
      | left j => rw [hydef, Fin.append_left, Fin.append_left] at hab; rw [hinj hab]
      | right j =>
        rw [hydef, Fin.append_left, Fin.append_right] at hab
        exact absurd (hab ▸ hzmem i) (hunot j)
    | right i =>
      induction b using Fin.addCases with
      | left j =>
        rw [hydef, Fin.append_left, Fin.append_right] at hab
        exact absurd (hab ▸ hzmem j) (hunot i)
      | right j => rw [hydef, Fin.append_right, Fin.append_right] at hab; rw [huinj hab]
  have hyimage : Finset.univ.image y = s := by
    ext x
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨a, rfl⟩
      induction a using Fin.addCases with
      | left i =>
        rw [hydef, Fin.append_left]
        exact hts (hzmem i)
      | right i =>
        rw [hydef, Fin.append_right]
        exact (Finset.mem_sdiff.mp (t.equivFin.symm i).2).1
    · intro hx
      by_cases hxz : x ∈ Finset.image z Finset.univ
      · obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hxz
        exact ⟨Fin.castAdd _ i, by rw [hydef, Fin.append_left]⟩
      · have hxt : x ∈ t := Finset.mem_sdiff.mpr ⟨hx, hxz⟩
        refine ⟨Fin.natAdd r (t.equivFin ⟨x, hxt⟩), ?_⟩
        rw [hydef, Fin.append_right]
        simp [u]
  refine ⟨t.card, y, hyinj, fun j => by rw [hydef, Fin.append_left], hyimage, ?_⟩
  have h1 : t.card + (Finset.image z Finset.univ).card = s.card :=
    Finset.card_sdiff_add_card_eq_card hts
  rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin] at h1
  omega

end Enumeration

section FrameOfSystem

open _root_.MvPowerSeries

variable {R : Type u} [CommRing R] [IsRegularLocalRing R] [IsAdicComplete (maximalIdeal R) R]
  [CharZero (ResidueField R)] {r : ℕ}

open Classical in
/-- p. 269 (Lemma 25): "We have a subfield `k` of `R` such that
`R = k{z₁, …, z_r, x₁, …, x_s}` by the structure theorem of a complete regular local ring
(equi-characteristic)", `S = k{x₁, …, x_s}`: for a complete regular local ring `R` whose residue
field has characteristic zero and an injective system `(z₁, …, z_r)` which can be extended to a
regular system of parameters, there are a coefficient field `σ`, a regular system of parameters
`(z, x)`, an isomorphism `Φ : R ≃ k{Z, X}` with `z_j ↦ Z_j`, `σ(t) ↦ t`, transforming `ν_M` into the
order of power series, and the regular frame `(S; z₁, …, z_r)` of `R` with `S = k{X}`, `S` mapped to
`R` by `Φ⁻¹`.  The only cited result is Cohen's coefficient field
(`exists_residue_comp_eq_id_of_isAdicComplete`). -/
theorem exists_regularFrame_of_extendsToRSOP [Hironaka.Cited.ExistsResidueCompEqIdOfIsAdicCompleteOfRingCharEq.{u}] {z : Fin r → R} (hinj : Function.Injective z)
    (hz : ExtendsToRSOP R (Finset.image z Finset.univ)) :
    ∃ (m : ℕ) (σ : ResidueField R →+* R) (_ : (IsLocalRing.residue R).comp σ = RingHom.id _)
      (Φ : R ≃+* MvPowerSeries (Fin (r + m)) (ResidueField R)),
      (∀ j, Φ (z j) = X (Fin.castAdd m j)) ∧ (∀ t, Φ (σ t) = MvPowerSeries.C t) ∧
      (∀ a, (Φ a).order = Ideal.ordElem (maximalIdeal R) a) ∧
      ∃ (F : RegularFrame R) (h : F.r = r), (∀ j, F.z (Fin.cast h.symm j) = z j) ∧
        ∃ ET : F.S ≃+* MvPowerSeries (Fin m) (ResidueField R), ∀ s,
          Φ (algebraMap F.S R s) = MvPowerSeries.rename (Fin.natAdd r) (ET s) := by
  obtain ⟨σ, hσ⟩ := exists_residue_comp_eq_id_of_isAdicComplete R
  obtain ⟨s, hts, hs⟩ := hz
  obtain ⟨m, x, hx, hxz, himg, -⟩ := exists_injective_append_enumeration hinj hts
  have hxs : IsRegularSystemOfParameters R (Finset.univ.image x) := by rw [himg]; exact hs
  obtain ⟨Φ, hΦx, hΦσ, hΦord⟩ := exists_ringEquiv_mvPowerSeries_of_coefficientField σ hσ x hx hxs
  have hΦz : ∀ j, Φ (z j) = X (Fin.castAdd m j) := fun j => by
    rw [← hxz j, hΦx]
  obtain ⟨F, h, hFz, ET, hET⟩ := exists_regularFrame_of_ringEquiv_mvPowerSeries Φ hinj
    ⟨s, hts, hs⟩ hΦz
  exact ⟨m, σ, hσ, Φ, hΦz, hΦσ, hΦord, F, h, hFz, ET, hET⟩

end FrameOfSystem


end Hironaka
