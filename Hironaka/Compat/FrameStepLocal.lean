/-
Copyright (c) 2026 Daattavya Aggarwal, Minhyong Kim, Oisin Kim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daattavya Aggarwal, Minhyong Kim, Oisin Kim
-/
module

public import Mathlib.FieldTheory.Separable
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Architect
public import Hironaka.Ch3.Stability
public import Hironaka.Ch3.StabilityCor3c
public import Hironaka.Ch3.SemiContinuity
public import Hironaka.Ch3.Frames
public import Hironaka.Compat.FrameCore
public import Hironaka.Compat.FrameLocalization
public import Hironaka.Compat.StableOrder
public import Hironaka.Statements

/-!
# The ring-level core of the frame step at a non-closed point (Ch. IV §3, Lemma (AB.5), p. 305)

In the step `t → t+1` of the proof of Lemma (AB.5) the paper says (p. 305): "Finally (a) of (2)
follows (b) of (2) for `g_{jk}(t + 1)` (`0 ≦ j β` [sic], `1 ≦ k ≦ m_j`) by Corollary 3 of Theorem 5,
§ 6, Ch. III, and by Theorem 5, § 6, Ch. III, applied to a monoidal transform of `Ŝ_t` with center
`Q̂_t` which is residually algebraic over `S_t` and such that `S_{t+1}` is a localization of the
transform."

Deviation from the paper (gap filled, incomplete citation): Corollary 3 (b) (p. 242) needs a prime
`Q_1` of the transform with `Q_1 ∩ R = Q ⊊ P`; here `Q_1 ∩ R = M` is the maximal ideal, so it is
not an instance of (b).  The true route, proved here, is Theorem 5 for the standard base `h_k`
(its hypothesis `ν_{M_1}(h_k) = ν_k`: the bound `≥` is Theorem 1 of §3 in the localization, the
bound `≤` is Lemma 8 of §3, which needs no prime `Q`), followed by Corollary 3 (c) for
`(R_1, M_1, Q_1, J_1, h)`.  The finiteness of the integral closures of footnote 10 needed in (c)
for the non-complete ring `R_1` is not verified in the paper; here it is the hypothesis `hfin`.
-/

@[expose] public section

open IsLocalRing

namespace Hironaka

universe u

noncomputable section

namespace RegularFrame

/-- **(S3a), coefficients**: analogue of `mem_pow_of_pow_mem_pow_sup` with a prime `Q ∋ z`,
`R/Q` regular, in place of `M`: if `a ∈ S` and `a^k ∈ Q^{ks} + (z)` in `R`, then
`a ∈ (Q ∩ S)^s`.  This is the ring-level content of p. 305: "(4) for `J̄(t)_{x̂'_t}` implies that
`g_{jki}(t)^{b/i}` is contained in the `b`th power of `Q̄_t`", with the consequence
`c_i ∈ (Q ∩ S)^i` (the paper's "it follows" is not argued; `ν_Q` is a valuation as `R/Q` is
regular). -/
@[blueprint "lem:IV.AB-5-frame-step-coeff"
  (statement := /-- Let $(S;z)$ be a regular frame of the regular local ring $R$ with $r=1$ and
    $Q\ni z$ a prime of $R$ with $R/Q$ regular. If $a\in S$ and $a^k\in Q^{ks}+(z)R$ ($k>0$),
    then $a\in(Q\cap S)^s$. (The step ``(4) for $\bar J(t)_{\hat x'_t}$ implies that
    $g_{jki}(t)^{b/i}$ is contained in the $b$th power of $\bar Q_t$'', p.~305.) -/)
  (proof := /-- $S\cap(Q^m+(z))=(Q\cap S)^m$ since $R/(z)\cong S$; $S/(Q\cap S)\cong R/Q$ is
    regular, so $\nu_{Q\cap S}$ is additive and $\nu_{Q\cap S}(a^k)=k\,\nu_{Q\cap S}(a)\ge ks$.
    \textbf{Deviation from the paper (gap filled).} The paper's ``it follows'' (that the coefficients lie in the powers of $Q\cap S$) is not argued. -/)
  (latexEnv := "lemma")]
theorem mem_comap_pow_of_pow_mem_pow_sup_prime {R : Type u} [CommRing R] [IsRegularLocalRing R]
    (F : RegularFrame R) (z : R) (hr : F.r = 1) (hz : ∀ i, F.z i = z) (Q : Ideal R) [Q.IsPrime]
    (hQ : IsRegularLocalRing (R ⧸ Q)) (hzQ : z ∈ Q) (a : F.S) {k s : ℕ} (hk : 0 < k)
    (h : algebraMap F.S R a ^ k ∈ Q ^ (k * s) ⊔ Ideal.span {z}) :
    a ∈ (Q.comap (algebraMap F.S R)) ^ s := by
  classical
  have h1 := mem_comap_pow_of_mem_pow_sup F z hz hr Q hzQ (k * s) (a ^ k)
    (by rwa [map_pow])
  -- `S/(Q ∩ S) ≅ R/Q` is regular
  have hq := F.quot_bijective
  have hzrange : Set.range F.z = {z} := by
    ext b
    simp only [Set.mem_range, Set.mem_singleton_iff]
    constructor
    · rintro ⟨j, rfl⟩; exact hz j
    · rintro rfl
      exact ⟨⟨0, by rw [hr]; exact Nat.one_pos⟩, hz _⟩
  rw [hzrange] at hq
  have hspan : Ideal.span {z} ≤ Q := (Ideal.span_singleton_le_iff_mem _).mpr hzQ
  let φ : F.S →+* R ⧸ Q := (Ideal.Quotient.mk Q).comp (algebraMap F.S R)
  have hφs : Function.Surjective φ := by
    intro y
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective y
    obtain ⟨b, hb⟩ := hq.2 (Ideal.Quotient.mk _ r)
    refine ⟨b, ?_⟩
    have : algebraMap F.S R b - r ∈ Ideal.span {z} := Ideal.Quotient.eq.mp hb
    exact Ideal.Quotient.eq.mpr (hspan this)
  have hker : RingHom.ker φ = Q.comap (algebraMap F.S R) := by
    ext b
    rw [RingHom.mem_ker, Ideal.mem_comap]
    exact Ideal.Quotient.eq_zero_iff_mem
  have hP'reg : IsRegularLocalRing (F.S ⧸ Q.comap (algebraMap F.S R)) := by
    have e := (Ideal.quotEquivOfEq hker.symm).trans (RingHom.quotientKerEquivOfSurjective hφs)
    exact IsRegularLocalRing.of_ringEquiv e.symm
  have hP'prime : (Q.comap (algebraMap F.S R)).IsPrime := Ideal.comap_isPrime _ _
  have h2 : ((k * s : ℕ) : ℕ∞) ≤ Ideal.ordElem (Q.comap (algebraMap F.S R)) (a ^ k) :=
    Ideal.le_ordElem h1
  have hpow : ∀ n : ℕ, Ideal.ordElem (Q.comap (algebraMap F.S R)) (a ^ n) =
      n * Ideal.ordElem (Q.comap (algebraMap F.S R)) a := by
    intro n
    induction n with
    | zero =>
      rw [pow_zero, Nat.cast_zero, zero_mul]
      refine le_antisymm (Ideal.ordElem_le_of_notMem (m := 0) ?_ |>.trans (by norm_num)) bot_le
      rw [zero_add, pow_one]
      exact fun h => hP'prime.ne_top ((Ideal.eq_top_iff_one _).mpr h)
    | succ n ih =>
      rw [pow_succ, ordElem_mul_of_isRegularLocalRing _ hP'reg, ih]
      push_cast
      ring
  rw [hpow] at h2
  refine Ideal.mem_pow_of_le_ordElem ?_
  rcases eq_or_ne (Ideal.ordElem (Q.comap (algebraMap F.S R)) a) ⊤ with h3 | h3
  · rw [h3]; exact le_top
  · obtain ⟨t, ht⟩ := ENat.ne_top_iff_exists.mp h3
    rw [← ht] at h2 ⊢
    have : k * s ≤ k * t := by exact_mod_cast h2
    exact_mod_cast Nat.le_of_mul_le_mul_left this hk

/-- **(S3a), shape**: if `z ∈ Q` and the coefficients `c_i` of `g = z^ν + Σ c_i z^{ν-(i+1)}` lie in
`(Q ∩ S)^{i+1}`, then `g ∈ Q^ν`; if moreover `ν_M(g) = ν`, then `ν_Q(g) = ν_M(g)` (for `Q` prime).
This is hypothesis (ii) `ν_P(g) = ν_M(g)` of Theorem 5 in the step of p. 305. -/
@[blueprint "lem:IV.AB-5-frame-step-order"
  (statement := /-- In the situation of \cref{lem:IV.AB-5-frame-step-coeff}, if the coefficients
    $c_i$ of $g=z^\nu+\sum_ic_iz^{\nu-i}$ lie in $(Q\cap S)^i$ and $\nu_M(g)=\nu$, then
    $\nu_Q(g)=\nu_M(g)$. -/)
  (proof := /-- Each term lies in $Q^\nu$, so $\nu\le\nu_Q(g)\le\nu_M(g)=\nu$ as $Q\subseteq M$.
    \textbf{Deviation from the paper (gap filled).} The paper does not argue this step; it is hypothesis (ii) $\nu_P(g)=\nu_M(g)$ of Theorem~5 in the step of p.~305. -/)
  (latexEnv := "lemma")]
theorem ordElem_eq_of_coeff_mem_pow {R : Type u} [CommRing R] [IsRegularLocalRing R]
    (F : RegularFrame R) (z : R) (Q : Ideal R) [Q.IsPrime] (hzQ : z ∈ Q) (ν : ℕ) (co : Fin ν → F.S)
    (hco : ∀ i : Fin ν, co i ∈ (Q.comap (algebraMap F.S R)) ^ ((i : ℕ) + 1))
    (hord : Ideal.ordElem (maximalIdeal R)
      (z ^ ν + ∑ i : Fin ν, algebraMap F.S R (co i) * z ^ (ν - ((i : ℕ) + 1))) = ν) :
    Ideal.ordElem Q (z ^ ν + ∑ i : Fin ν, algebraMap F.S R (co i) * z ^ (ν - ((i : ℕ) + 1))) =
      ν := by
  have hmem : z ^ ν + ∑ i : Fin ν, algebraMap F.S R (co i) * z ^ (ν - ((i : ℕ) + 1)) ∈ Q ^ ν := by
    refine Ideal.add_mem _ (Ideal.pow_mem_pow hzQ ν) (Ideal.sum_mem _ fun i _ => ?_)
    have h1 : algebraMap F.S R (co i) ∈ Q ^ ((i : ℕ) + 1) := by
      have h := Ideal.mem_map_of_mem (algebraMap F.S R) (hco i)
      rw [Ideal.map_pow] at h
      exact Ideal.pow_right_mono Ideal.map_comap_le _ h
    have h2 := Ideal.mul_mem_mul h1 (Ideal.pow_mem_pow hzQ (ν - ((i : ℕ) + 1)))
    rw [← pow_add, show (i : ℕ) + 1 + (ν - ((i : ℕ) + 1)) = ν by have := i.2; omega] at h2
    exact h2
  refine le_antisymm ?_ (by exact_mod_cast Ideal.le_ordElem hmem)
  rw [← hord]
  exact Ideal.ordElem_mono (IsLocalRing.le_maximalIdeal (Ideal.IsPrime.ne_top ‹_›)) _

end RegularFrame

namespace FrameStepLocal

/-- The initial form of a unit `u` of a local ring is the image of its class in `A/M`. -/
theorem initialForm_unit {A : Type u} [CommRing A] [IsLocalRing A] (u : Aˣ) :
    initialForm (maximalIdeal A) (u : A) =
      algebraMap (A ⧸ maximalIdeal A) (AssocGraded (maximalIdeal A))
        (Ideal.Quotient.mk (maximalIdeal A) u) := by
  have h0 : Ideal.ordElem (maximalIdeal A) (u : A) = ((0 : ℕ) : ℕ∞) := by
    refine le_antisymm (Ideal.ordElem_le_of_notMem ?_) (by simp)
    rw [zero_add, pow_one]
    exact fun h => (maximalIdeal.isMaximal A).ne_top (Ideal.eq_top_of_isUnit_mem _ h u.isUnit)
  rw [initialForm_eq_mk _ h0]
  show AssocGraded.mk _ 0 _ _ = AssocGraded.algebraMapQuot _ (Ideal.Quotient.mk _ _)
  rw [AssocGraded.algebraMapQuot, Ideal.Quotient.lift_mk, AssocGraded.algebraMap_apply,
    AssocGraded.mk]
  congr 1

/-- `gr(⊤) = ⊤` is generated by the initial form of any unit (in any local ring). -/
theorem grIdeal_top_eq_span_of_isUnit {A : Type u} [CommRing A] [IsLocalRing A] {m : ℕ}
    (g : Fin m → A) (k : Fin m) (hk : IsUnit (g k)) :
    grIdeal (maximalIdeal A) (⊤ : Ideal A) =
      Ideal.span (Set.range fun j => initialForm (maximalIdeal A) (g j)) := by
  obtain ⟨u, hu⟩ := hk
  have hunit : IsUnit (initialForm (maximalIdeal A) (g k)) := by
    rw [← hu, initialForm_unit]
    exact (Ideal.Quotient.mk (maximalIdeal A) |>.isUnit_map u.isUnit).map _
  have h1 : initialForm (maximalIdeal A) (g k) ∈ grIdeal (maximalIdeal A) (⊤ : Ideal A) :=
    Ideal.subset_span ⟨g k, Submodule.mem_top, rfl⟩
  have h2 : initialForm (maximalIdeal A) (g k) ∈
      Ideal.span (Set.range fun j => initialForm (maximalIdeal A) (g j)) :=
    Ideal.subset_span ⟨k, rfl⟩
  exact (Ideal.eq_top_of_isUnit_mem _ h1 hunit).trans (Ideal.eq_top_of_isUnit_mem _ h2 hunit).symm

variable {R : Type u} [CommRing R] [IsRegularLocalRing R] [IsDomain R]

/-- **Lemma 8 of §3 without a prime `Q`** (the step (1) of the proof of Corollary 3 (b)): if
`ν_P(f) = ν_M(f) = ν` and `x^ν h = f` in a residually algebraic monoidal transform `R_1` of `R`
with center `P`, then `ν_{M_1}(h) ≤ ν_M(f)`.

Deviation from the paper (gap filled): the "`≤`" half of hypothesis (iii) `ν_{M_1}(h_k) = ν_k` of
Theorem 5 in the step of p. 305 is Lemma 8 of §3 (p. 217) applied to the principal ideal `(f)`; the
existing chain for Corollary 3 (b) assumes a prime `Q ⊊ P` with `Q_1 ∩ R = Q`, which is absent
here, but the step does not use `Q`. -/
@[blueprint "lem:IV.AB-5-frame-step-lemma8"
  (statement := /-- Let $R$ be a regular local ring, $P$ a prime with $R/P$ regular, $R_1$ a
    monoidal transform of $R$ with center $P$ which is residually separable algebraic, $x$ with
    $PR_1=(x)R_1$, and $f\in R$ with $\nu_P(f)=\nu_M(f)=\nu$, $x^\nu h=f$. Then
    $\nu_{M_1}(h)\le\nu_M(f)$. -/)
  (proof := /-- Lemma~8 (\cref{lem:III.8}) for the principal ideal $(f)$, whose weak transform is
    $(h)$. \textbf{Deviation from the paper (gap filled).} The ``$\le$'' half of hypothesis (iii) of Theorem~5 in the step of p.~305 is Lemma~8 of \S3 (p.~217) applied to the principal ideal $(f)$; the existing chain for Corollary~3 (b) assumes a prime $Q\subsetneq P$ with $Q_1\cap R=Q$, which is absent here, but the step does not use $Q$. -/)
  (proofUses := ["lem:III.8"])
  (latexEnv := "lemma")]
theorem ordElem_maximalIdeal_le_of_strictTransform (P : Ideal R) [P.IsPrime]
    [IsRegularLocalRing (R ⧸ P)] (t : MonoidalTransform R P) [IsLocalHom t.toRing]
    [IsRegularLocalRing t.ring]
    (hsep : RingHom.IsResiduallySeparableAlgebraic (R := R) (R' := t.ring) t.toRing)
    (x : R) (hx : P.map t.toRing = Ideal.span {t.toRing x}) (f : R) (ν : ℕ)
    (hν : (ν : ℕ∞) = Ideal.ordElem P f) (hMP : Ideal.ordElem (maximalIdeal R) f = Ideal.ordElem P f)
    (hf0 : f ≠ 0) (h : t.ring) (hh : t.toRing x ^ ν * h = t.toRing f) :
    Ideal.ordElem (maximalIdeal t.ring) h ≤ Ideal.ordElem (maximalIdeal R) f := by
  classical
  have hinj := MonoidalTransform.toRing_injective t
  rcases Nat.eq_zero_or_pos ν with hν0 | hνpos
  · -- `ν = 0`: `h = f` is a unit
    subst hν0
    rw [pow_zero, one_mul] at hh
    have hM0 : Ideal.ordElem (maximalIdeal R) f = 0 := by rw [hMP, ← hν]; rfl
    have hfM : f ∉ maximalIdeal R := fun hfM => by
      have := Ideal.le_ordElem (I := maximalIdeal R) (f := f) (ν := 1) (by simpa using hfM)
      rw [hM0] at this
      exact absurd this (by decide)
    have hu : IsUnit (t.toRing f) := (IsLocalRing.notMem_maximalIdeal.mp hfM).map _
    rw [hM0, hh]
    refine Ideal.ordElem_le_of_notMem (m := 0) ?_ |>.trans (by norm_num)
    rw [zero_add, pow_one]
    exact fun hmem => (IsLocalRing.mem_maximalIdeal _).mp hmem hu
  have hx0 : t.toRing x ≠ 0 := by
    intro h0
    apply hf0
    apply hinj
    rw [← hh, h0, zero_pow hνpos.ne', zero_mul, map_zero]
  have hJ0 : Ideal.span {f} ≠ ⊥ := by rw [ne_eq, Ideal.span_singleton_eq_bot]; exact hf0
  have hPJ : Ideal.ord P (Ideal.span {f}) = Ideal.nu (Ideal.span {f}) := by
    simp only [Ideal.nu, Ideal.ord_span_singleton, hMP]
  have halg : RingHom.IsResiduallyAlgebraic (R := R) (R' := t.ring) t.toRing := by
    let _ : Algebra (ResidueField R) (ResidueField t.ring) :=
      (ResidueField.map t.toRing).toAlgebra
    have _ : Algebra.IsSeparable (ResidueField R) (ResidueField t.ring) := hsep
    exact Algebra.IsSeparable.isAlgebraic _ _
  have h8 := nu_weakTransform_le R (Ideal.span {f}) hJ0 P hPJ t halg
  obtain ⟨-, -, -, -, h5⟩ := t.divIdeal_monotone_and_strictTransformIdeal_eq_iSup inferInstance
    inferInstance (Ideal.span {f}) (t.toRing x) hx.symm
  obtain ⟨ν', hν', -, hweak⟩ := h5 hJ0 (Ideal.IsPrime.ne_top inferInstance)
  have hνν' : ν' = ν := by
    have : (ν' : ℕ∞) = ν := by rw [← hν', Ideal.ord_span_singleton, hν]
    exact_mod_cast this
  have hdiv : t.divIdeal (t.toRing x) ν' (Ideal.span {f}) = Ideal.span {h} := by
    rw [hνν']
    apply le_antisymm
    · rw [MonoidalTransform.divIdeal, Ideal.span_le]
      rintro y ⟨f', hf', hy⟩
      obtain ⟨r, rfl⟩ := Ideal.mem_span_singleton'.mp hf'
      rw [SetLike.mem_coe, Ideal.mem_span_singleton']
      refine ⟨t.toRing r, mul_left_cancel₀ (pow_ne_zero ν hx0) ?_⟩
      rw [hy, map_mul, ← hh]
      ring
    · rw [Ideal.span_le, Set.singleton_subset_iff]
      exact Ideal.subset_span ⟨f, Ideal.mem_span_singleton_self _, hh⟩
  rw [hweak, hdiv] at h8
  simpa only [Ideal.nu, Ideal.ord_span_singleton] using h8

/-- **(S5) and (S6)** (p. 305): Theorem 5 and Corollary 3 (c) at a prime `Q₁` of the transform
`R_1` with `ν_{Q_1}(h_k) = ν_k` (hypothesis `hloc`, "(b) of (2) for `g_{jk}(t+1)`").  The finiteness
of the integral closures of footnote 10 for `R_1` (`hfin`) is a hypothesis: the paper does not
verify it for the non-complete `R_1`.  No relation between `Q₁ ∩ R` and `P` is needed.

The paper (p. 305): "Finally (a) of (2) follows (b) of (2) for `g_{jk}(t+1)` ... by Corollary 3 of
Theorem 5, § 6, Ch. III, and by Theorem 5, § 6, Ch. III, applied to a monoidal transform of `Ŝ_t`
with center `Q̂_t` which is residually algebraic over `S_t` and such that `S_{t+1}` is a
localization of the transform."

Deviation from the paper (gap filled, incomplete citation): Corollary 3 (b) is not an instance
(it needs `Q_1 ∩ R = Q ⊊ P`, here `Q_1 ∩ R = M`); Theorem 5 plus Corollary 3 (c), with Lemma 8 for
the bound `ν_{M_1}(h_k) ≤ ν_k`, is the route that is true; the finiteness of footnote 10 for the
non-complete `R_1` is not verified in the paper. -/
@[blueprint "lem:IV.AB-5-frame-step-local"
  (statement := /-- Let $R$ be a regular local ring whose residue field has characteristic zero,
    $J\subseteq P$ with $P$ a prime, $R/P$ regular, $R_1$ a monoidal transform of $R$ with
    center $P$ which is residually separable algebraic, $x\in P$ with $PR_1=(x)R_1$,
    $(f_j)$ a standard base of $J$ with $\nu_P(f_j)=\nu_M(f_j)=\nu_j$ and $g_j=x^{-\nu_j}f_j$,
    and $Q_1$ a prime of $R_1$ with $\nu_{Q_1R_{1,Q_1}}(g_j)=\nu_j$. Assume the finiteness of
    the integral closures of footnote~10 for $R_1$. Then $(g_j)$ is a standard base of the strict
    transform $J_1$, $\nu_{M_1}(g_j)=\nu_j$, $\nu^*(J_1)=\nu^*(J)$, and the initial forms of
    the $g_j$ generate $\operatorname{gr}(J_1R_{1,Q_1})$. (Theorem~5 and Corollary~3~(c), as used
    on p.~305.) -/)
  (proof := /-- (iii) of Theorem~5: $\nu_{M_1}(g_j)\ge\nu_{Q_1}(g_j)=\nu_j$ by Theorem~1 of
    \S3, and $\le\nu_j$ by \cref{lem:IV.AB-5-frame-step-lemma8}; Theorem~5 (\cref{thm:III.5})
    gives the standard base; Corollary~3~(c) (\cref{cor:III.thm5-3c}) for $(R_1,M_1,Q_1,J_1,g)$
    gives the initial forms (if $J_1\not\subseteq Q_1$ then $J_1R_{1,Q_1}=(1)$ and a member of
    the system is a unit). \textbf{Deviation from the paper (gap filled, incomplete
    citation).} Corollary~3~(b) is not an instance. -/)
  (proofUses := ["thm:III.5", "cor:III.thm5-3c", "lem:IV.AB-5-frame-step-lemma8"])
  (latexEnv := "lemma")]
theorem isStandardBase_and_grIdeal_localization_of_strictTransform [Hironaka.HironakaCitedResults.{u}] [CharZero (ResidueField R)]
    (J P : Ideal R) [P.IsPrime] [IsRegularLocalRing (R ⧸ P)] (hJP : J ≤ P)
    (t : MonoidalTransform R P) [IsLocalHom t.toRing] [IsRegularLocalRing t.ring]
    (hsep : RingHom.IsResiduallySeparableAlgebraic (R := R) (R' := t.ring) t.toRing)
    (x : R) (hxP : x ∈ P) (hx : P.map t.toRing = Ideal.span {t.toRing x})
    {m : ℕ} (f : Fin m → R) (ν : Fin m → ℕ) (g : Fin m → t.ring)
    (hν : ∀ j, (ν j : ℕ∞) = Ideal.ordElem (maximalIdeal R) (f j))
    (hg : ∀ j, t.toRing x ^ ν j * g j = t.toRing (f j))
    (hi : IsStandardBase R J f)
    (hii : ∀ j, Ideal.ordElem P (f j) = Ideal.ordElem (maximalIdeal R) (f j))
    (Q₁ : Ideal t.ring) [Q₁.IsPrime]
    (hloc : ∀ j, Ideal.ordElem (maximalIdeal (Localization.AtPrime Q₁))
      (algebraMap t.ring (Localization.AtPrime Q₁) (g j)) = ν j)
    (hfin : ∀ (Q' Q'' : Ideal t.ring) [Q'.IsPrime] [Q''.IsPrime], Q'' ≤ Q' →
      Module.Finite (Localization.AtPrime Q' ⧸
        Q''.map (algebraMap t.ring (Localization.AtPrime Q')))
        (integralClosure (Localization.AtPrime Q' ⧸
          Q''.map (algebraMap t.ring (Localization.AtPrime Q')))
          (FractionRing (Localization.AtPrime Q' ⧸
            Q''.map (algebraMap t.ring (Localization.AtPrime Q')))))) :
    IsStandardBase t.ring (strictTransformIdeal t J) g ∧
      (∀ j, Ideal.ordElem (maximalIdeal t.ring) (g j) = ν j) ∧
      nuStar t.ring (strictTransformIdeal t J) = nuStar R J ∧
      grIdeal (maximalIdeal (Localization.AtPrime Q₁))
          ((strictTransformIdeal t J).map (algebraMap t.ring (Localization.AtPrime Q₁))) =
        Ideal.span (Set.range fun j => initialForm (maximalIdeal (Localization.AtPrime Q₁))
          (algebraMap t.ring (Localization.AtPrime Q₁) (g j))) := by
  classical
  have hdom : IsDomain t.ring := Transforms.isDomain_of_isRegularLocalRing t.ring
  have hf0 : ∀ j, f j ≠ 0 := fun j h0 => by
    have := hν j
    rw [h0, Ideal.ordElem_eq_top_iff.mpr fun n => zero_mem _] at this
    exact ENat.natCast_ne_top _ this
  have hνP : ∀ j, (ν j : ℕ∞) = Ideal.ordElem P (f j) := fun j => (hν j).trans (hii j).symm
  have hf0' : ∀ j, t.toRing (f j) ≠ 0 := fun j h0 =>
    hf0 j (MonoidalTransform.toRing_injective t (h0.trans (map_zero _).symm))
  -- (iii) of Theorem 5: `ν_{M₁}(g_j) = ν_j`
  have hiii : ∀ j, Ideal.ordElem (maximalIdeal t.ring) (g j) = (ν j : ℕ∞) := fun j => by
    refine le_antisymm ?_ ?_
    · exact (ordElem_maximalIdeal_le_of_strictTransform P t hsep x hx (f j) (ν j) (hνP j)
        (hii j).symm (hf0 j) (g j) (hg j)).trans (hν j).ge
    · have hg0 : g j ≠ 0 := fun h0 => hf0' j (by rw [← hg j, h0, mul_zero])
      have h1 := Ideal.ordElem_localization_le_ordElem_maximalIdeal (R := t.ring) Q₁ (g j)
      rw [Localization.AtPrime.map_eq_maximalIdeal, hloc j] at h1
      exact h1
  -- Theorem 5
  obtain ⟨hstd, hnu⟩ :=
    isStandardBase_strictTransform J P hJP t hsep x hxP hx f ν g hν hg hi hii hiii
  refine ⟨hstd, hiii, hnu, ?_⟩
  -- Corollary 3 (c)
  have hchar : CharZero (ResidueField t.ring) := by
    refine (RingHom.charZero_iff (ResidueField.map t.toRing).injective).mp ?_
    exact inferInstance
  by_cases hJ₁ : strictTransformIdeal t J ≤ Q₁
  · have hadapt : IsLocallyAdaptedSystem t.ring Q₁ (strictTransformIdeal t J) g := by
      refine ⟨hstd.1, hstd.2.2.2.1, fun k => ?_⟩
      rw [hiii k, Localization.AtPrime.map_eq_maximalIdeal, hloc k]
    have h := grIdeal_localization_eq_span_initialForm_of_finite hfin Q₁ _ hJ₁ g hadapt
    rwa [Localization.AtPrime.map_eq_maximalIdeal] at h
  · have hspan := span_eq_of_isStandardBase t.ring (strictTransformIdeal t J) g hstd
    obtain ⟨k, hkQ⟩ : ∃ k, g k ∉ Q₁ := by
      by_contra hcon
      push Not at hcon
      exact hJ₁ (by rw [← hspan, Ideal.span_le]; rintro _ ⟨k, rfl⟩; exact hcon k)
    have htop : (strictTransformIdeal t J).map (algebraMap t.ring (Localization.AtPrime Q₁)) =
        ⊤ :=
      Ideal.eq_top_of_isUnit_mem _ (Ideal.mem_map_of_mem _ (hstd.1 k))
        (RegularFrame.isUnit_algebraMap_of_notMem hkQ)
    rw [htop]
    exact grIdeal_top_eq_span_of_isUnit
      (fun k => algebraMap t.ring (Localization.AtPrime Q₁) (g k)) k
      (RegularFrame.isUnit_algebraMap_of_notMem hkQ)

end FrameStepLocal

end

end Hironaka
