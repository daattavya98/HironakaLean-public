/-
Copyright (c) 2026 Daattavya Aggarwal, Minhyong Kim, Oisin Kim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daattavya Aggarwal, Minhyong Kim, Oisin Kim
-/
module

public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.KrullDimension.NonZeroDivisors
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Architect
public import Hironaka.Ch3.Basic
public import Hironaka.Ch3.Frames
public import Hironaka.Ch3.FrameTransforms
public import Hironaka.Ch3.Transforms
public import Hironaka.Compat.RegularQuotient
public import Hironaka.Compat.RSOPProducts
public import Hironaka.Compat.FrameShift

/-!
# Ch. IV §4 (p. 318): the maximal-contact step of Lemma (CD.4), unrestricted case

> Clearly `z_{t+1}` is a non-unit for the case in which `ℜ = (ℜ^N_II, F)`, because
> `x'_{t+1} ∈ S_ν(h*_{t+1}(ℜ)) = S_ν(h*_{t+1}(ℜ^N_II)) ∩ F(t + 1)`. For the other case, we
> apply Lemma 22, §10, Ch. III, to
> `g_1(t)/v_t = z_{t+1}^ν + (g_{12}(t)/v_t²) z_{t+1}^{ν-2} + ⋯ + (g_{1ν}(t)/v_t^ν)`
> which is contained in the `ν`th power of the maximal ideal of `Ŝ'_{t+1}`. (p. 318; the left
> side should read `g_1(t)/v_t^ν`, a misprint.)

The paper's `g_{11}(t) = 0` is condition (c)_t of the induction (p. 317), not part of this
sentence.

The citation of Lemma 22 (p. 265) is circular: it is a statement about a regular frame
`(T'; z)`, and by Definition 9 (p. 248) a regular frame requires `z` to be part of a regular
system of parameters, hence a non-unit, which is the conclusion sought.  This file proves the
ring-level claim that the paper intends, `z/w ∈ M₁`, by the argument *of the proof of Lemma 22*
(pp. 265–266), run on the fibre `R₁/wR₁` of the monoidal transform:

* The first stage of Lemma 22's proof writes `x = z + h`, expands `f = z^ν + g'_1 z^{ν-1} + ⋯ + g'_ν`
  with `g'_1 = νh` (`g_{11} = 0`), and concludes from the uniqueness of the expansion in `z` and the
  `g'_j` that `νh ∈ P'`, so (`char = 0`) `h ∈ P` and `x ∈ P`.  Here the same two inputs (no
  `Z^{ν-1}` term, `ν!` a unit) are used in the same way in the polynomial ring `A[X] ≅ ` fibre of
  the blow-up, with `h` the residue of `X` in `A[X]/q` (`X_mem_of_monic_mem_pow_localization`).
* The polynomial structure of the fibre (`R₁/wR₁ ≅ (R/Q)[T_S][X]_q`, `X = z/x`) is the
  "well known" structure of a monoidal transform of p. 209–210
  (`MonoidalTransform.exists_quotient_equiv_localization`), taken in the chart given by an
  element `x₀ ∈ Q ∩ S` (`exists_fiber_polynomial_model`, proved).
-/

@[expose] public section

open IsLocalRing Polynomial

namespace Hironaka

universe u v

section CharZeroCore

variable {A : Type u} [CommRing A]

/-- An element of a ring whose image in the localization at a prime `q` lies in `m^n` is
multiplied into `q^n` by an element outside `q`. -/
theorem exists_mul_mem_pow_of_algebraMap_mem_pow {B : Type u} [CommRing B] (q : Ideal B)
    [q.IsPrime] (n : ℕ) (G : B)
    (hG : algebraMap B (Localization.AtPrime q) G ∈
      IsLocalRing.maximalIdeal (Localization.AtPrime q) ^ n) :
    ∃ s ∉ q, s * G ∈ q ^ n := by
  rw [← IsLocalization.AtPrime.map_eq_maximalIdeal q (Localization.AtPrime q), ← Ideal.map_pow,
    IsLocalization.mem_map_algebraMap_iff q.primeCompl] at hG
  obtain ⟨⟨x1, x2⟩, h⟩ := hG
  rw [← map_mul, IsLocalization.eq_iff_exists q.primeCompl] at h
  obtain ⟨c, hc⟩ := h
  refine ⟨c * x2, q.primeCompl.mul_mem c.2 x2.2, ?_⟩
  have : (c : B) * x2 * G = c * x1 := by
    simp only at hc; rw [← hc]; ring
  rw [this]
  exact Ideal.mul_mem_left _ _ x1.2

/-- The step "The assumption that `ν_{PR_P}(f) ≥ ν` implies that `f ∈ (z, Q')^νR'`" of the first
stage of Lemma 22 (p. 266), for a ring map `μ : B → E` that sends the ideal `q` into the principal
ideal `(y)` (here `y = z` and `Q'` is sent to `0`): `μ` sends `q^k` into `(y^k)`. -/
theorem pow_dvd_map_of_mem_pow {B E : Type*} [CommRing B] [CommRing E] (μ : B →+* E)
    (q : Ideal B) (y : E) (hy : ∀ f ∈ q, y ∣ μ f) (k : ℕ) (f : B) (hf : f ∈ q ^ k) :
    y ^ k ∣ μ f := by
  have h1 : μ f ∈ (q.map μ) ^ k := by
    rw [← Ideal.map_pow]; exact Ideal.mem_map_of_mem _ hf
  have h2 : q.map μ ≤ Ideal.span {y} := by
    rw [Ideal.map_le_iff_le_comap]
    intro f hf
    rw [Ideal.mem_comap, Ideal.mem_span_singleton]
    exact hy f hf
  have h3 := Ideal.pow_right_mono h2 k h1
  rwa [Ideal.span_singleton_pow, Ideal.mem_span_singleton] at h3

/-- **The characteristic-zero step of Lemma 22 (pp. 265--266), in the polynomial fibre** used on
p. 318: a polynomial `G = X^ν + a_0 X^(ν-1) + a_1 X^(ν-2) + ⋯ + a_{ν-1}` (`ν = n + 1`) over a ring
`A` in which `ν!` is a unit, lying in the `ν`-th power of the maximal ideal of `A[X]_q` and with
`a_0 ∈ q`, forces `X ∈ q`.

The proof is the first stage of the proof of Lemma 22 (p. 265, bottom, and p. 266, top):
"... let `z = x - h`. We write `f` in the form `f = z^ν + g'_1z^{ν-1} + ⋯ + g'_ν` with `g'_j ∈ S`
`(1 ≤ j ≤ ν)`. Then `g'_1 = νh`. Let `R' = R_P` and `S' = S_{P∩S}`. [...] The assumption that
`ν_{PR_P}(f) ≥ ν` implies that `f ∈ (z, Q')^νR'`. Hence, by the uniqueness of the above expression
of `f` in terms of `z` and `g'_j ∈ S`, we have `ν_{Q'}(g'_j) ≥ j` for `1 ≤ j ≤ ν`. In particular,
`νh = g'_1 ∈ P'`, hence `h ∈ P' ∩ R = P`. Hence `x = z + h ∈ P`."

The dictionary: `R = A[X]`, `P = q`, `S = A`, `x = X`, `f = G`; `ν_{PR_P}(f) ≥ ν` is the hypothesis
`hG`; the absence of the term `g_1 x^{ν-1}` is `a_0 ∈ q` (the image of `a_0` is `0` in `A[X]/q`).
The first stage assumes "a non-unit element `h` of `S` such that `x - h ∈ P`" (and `R` complete);
in the fibre no such `h ∈ A` is given.  Gap filled: `h` is taken to be the residue of `X` in the
domain `D = A[X]/q = R/P`, and the expansion `x = z + h` is the ring map `μ : A[X] → D[Y]`,
`X ↦ Y + h`, `a ↦ ā`, so that `z = Y`.  The coefficients `g'_j` of the expansion therefore lie in
`D` and not in `S`, and `Q' = 0` (the ideal `q` is sent into `(Y)`), so that `P' = (z, Q') = (Y)`;
no completeness and no regular frame `(S'; z)` is used.  The expansion of `x^ν + ⋯` in `z` with
`g'_1 = νh` (plus the image of `a_0`) is `exists_framePoly_shift`, and "the uniqueness of the above
expression" is the uniqueness of the coefficients of a polynomial in `Y`.  This is the analogue of
the choice of `u` on p. 267 ("there exists a unit element `u` in `S` such that `x/y - u ∈ M₁`").

Deviation from the paper (the citation of Lemma 22 on p. 318 is circular, gap filled): Lemma 22 is
a statement about a regular frame `(S'; z)`, hence about a non-unit `z`. -/
@[blueprint "lem:IV.CD-4-derivative-core"
  (statement := /-- Let $A$ be a ring in which $\nu!$ is a unit, $q$ a prime ideal of the
    polynomial ring $A[X]$, and $G=X^\nu+\sum_{i=0}^{\nu-1}a_iX^{\nu-1-i}$ with $a_i\in A$ and
    $a_0\in q$. If $G$ lies in the $\nu$-th power of the maximal ideal of $A[X]_q$, then
    $X\in q$. -/)
  (proof := /-- This is the first stage of the proof of Lemma~22 (pp.~265--266): ``let $z=x-h$.
    We write $f$ in the form $f=z^\nu+g'_1z^{\nu-1}+\dots+g'_\nu$ with $g'_j\in S$. Then
    $g'_1=\nu h$. [\dots] The assumption that $\nu_{PR_P}(f)\ge\nu$ implies that
    $f\in(z,Q')^\nu R'$. Hence, by the uniqueness of the above expression of $f$ in terms of $z$
    and $g'_j\in S$, we have $\nu_{Q'}(g'_j)\ge j$ for $1\le j\le\nu$. In particular, $\nu
    h=g'_1\in P'$, hence $h\in P'\cap R=P$. Hence $x=z+h\in P$.'' Here $R=A[X]$, $P=q$, $S=A$,
    $x=X$, $f=G$. Since $G$ lies in the $\nu$-th power of the maximal ideal, $sG\in q^\nu$ for
    some $s\notin q$. Let $D=A[X]/q$ (a domain), $h\in D$ the residue of $X$, and
    $\mu\colon A[X]\to D[Y]$ the ring map with $\mu(X)=Y+h$ and $\mu|_A$ the residue map, so that
    $z=Y=x-h$; $\mu$ sends $q$ into $(Y)$. Hence $Y^\nu$ divides $\mu(s)\mu(G)$, and $Y\nmid\mu(s)$,
    so $Y^\nu\mid\mu(G)$, i.e.\ $\mu(G)\in(z,Q')^\nu$ with $Q'=0$. By the expansion of $(z+h)^\nu$,
    $\mu(G)=Y^\nu+g'_1Y^{\nu-1}+\dots+g'_\nu$ with $g'_1=\nu h+\mu(a_0)=\nu h$ (as $a_0\in q$).
    By the uniqueness of this expression, $g'_j=0$ for all $j$; in particular $\nu h=0$, so $h=0$
    ($\nu$ a unit), i.e.\ $X\in q$.

    \textbf{Deviation from the paper (gap filled).} Lemma~22 is stated for a regular frame
    $(S';z)$, hence for a non-unit $z$; its application on p.~318 is circular. The first stage
    assumes ``a non-unit element $h$ of $S$ such that $x-h\in P$''; here $h$ is produced by the
    substitution $X\mapsto Y+h$ over the residue domain $D$, the device of p.~267 (``there exists
    a unit element $u$ in $S$ such that $x/y-u\in M_1$''). -/)
  (latexEnv := "lemma")]
theorem X_mem_of_monic_mem_pow_localization (n : ℕ) (hu : IsUnit (((n + 1).factorial : ℕ) : A))
    (a : Fin (n + 1) → A) (q : Ideal A[X]) [q.IsPrime] (h0 : C (a 0) ∈ q)
    (hG : algebraMap A[X] (Localization.AtPrime q)
      (X ^ (n + 1) + ∑ i : Fin (n + 1), C (a i) * X ^ ((n + 1) - ((i : ℕ) + 1))) ∈
      IsLocalRing.maximalIdeal (Localization.AtPrime q) ^ (n + 1)) :
    (X : A[X]) ∈ q := by
  classical
  set G : A[X] := X ^ (n + 1) + ∑ i : Fin (n + 1), C (a i) * X ^ ((n + 1) - ((i : ℕ) + 1))
    with hGdef
  -- "The assumption that `ν_{PR_P}(f) ≥ ν`": `s f ∈ q^ν` for some `s ∉ q`
  obtain ⟨s, hs, hsG⟩ := exists_mul_mem_pow_of_algebraMap_mem_pow q (n + 1) G hG
  -- gap filled (the element `h`): `D = A[X]/q`, `h` the residue of `x = X`, and the substitution
  -- `x = z + h`, `μ : A[X] → D[Y]`, `X ↦ Y + h`, `z = Y`
  let D := A[X] ⧸ q
  have : IsDomain D := Ideal.Quotient.isDomain q
  let res : A[X] →+* D := Ideal.Quotient.mk q
  let resA : A →+* D := res.comp C
  let h : D := res X
  let μ : A[X] →+* D[X] := eval₂RingHom (C.comp resA) (X + C h)
  have hμC : ∀ b : A, μ (C b) = C (resA b) := fun b => by simp [μ]
  have hμX : μ X = X + C h := by simp [μ]
  have hres : ∀ f : A[X], res f = 0 ↔ f ∈ q := fun f => Ideal.Quotient.eq_zero_iff_mem
  have hcoeff0 : ∀ f : A[X], (μ f).coeff 0 = res f := by
    intro f
    have : (evalRingHom (0 : D)).comp μ = res := by
      refine Polynomial.ringHom_ext (fun b => ?_) ?_
      · simp [hμC, resA]
      · simp [hμX, h]
    have h2 := congrArg (fun F : A[X] →+* D => F f) this
    simpa [coeff_zero_eq_eval_zero] using h2
  -- "`f ∈ (z, Q')^νR'`", with `Q' = 0` and `z = Y`: `μ` sends `q` into `(Y)`, hence `sG` into `(Y^ν)`
  have hdvd_q : ∀ (k : ℕ) (f : A[X]), f ∈ q ^ k → (X : D[X]) ^ k ∣ μ f :=
    fun k f hf => pow_dvd_map_of_mem_pow (B := A[X]) (E := D[X]) μ q X
      (fun f hf => X_dvd_iff.mpr ((hcoeff0 f).trans ((hres f).mpr hf))) k f hf
  have hdvd : (X : D[X]) ^ (n + 1) ∣ μ s * μ G := by
    rw [← map_mul]; exact hdvd_q _ _ hsG
  have hXs : ¬ (X : D[X]) ∣ μ s := by
    intro hd
    exact hs ((hres s).mp ((hcoeff0 s).symm.trans (X_dvd_iff.mp hd)))
  have hμG : (X : D[X]) ^ (n + 1) ∣ μ G :=
    (prime_X).pow_dvd_of_dvd_mul_left (n + 1) hXs hdvd
  -- "We write `f` in the form `f = z^ν + g'_1z^{ν-1} + ⋯ + g'_ν` … Then `g'_1 = νh`"
  obtain ⟨c', hc'0, hc'⟩ := exists_framePoly_shift (S := D) (n + 1) (Nat.succ_pos n)
    (fun i => resA (a i)) h
  have hμG' : μ G = framePoly (n + 1) c' := by
    have h1 := hc' (C : D →+* D[X]) (X + C h)
    rw [add_sub_cancel_right] at h1
    rw [framePoly, ← h1]
    simp only [hGdef, map_add, map_pow, map_sum, map_mul, hμC, hμX]
  -- "by the uniqueness of the above expression of `f` in terms of `z` and `g'_j ∈ S`, we have
  -- `ν_{Q'}(g'_j) ≥ j`": here `Q' = 0`, so all coefficients `g'_j` of `Y^{ν-j}` vanish
  have hc'zero : ∀ i : Fin (n + 1), c' i = 0 := by
    intro i
    have h1 := (X_pow_dvd_iff.mp hμG) ((n + 1) - ((i : ℕ) + 1)) (by have := i.2; omega)
    rwa [hμG', coeff_framePoly_sub] at h1
  -- `g_1 = 0` (here `a_0 ∈ q`, so `a_0` has image `0` in `D`) and `ν` is a unit
  have hψ0 : resA (a 0) = 0 := (hres _).mpr h0
  have hνu : IsUnit (((n + 1 : ℕ) : A)) := by
    rw [Nat.factorial_succ, Nat.cast_mul] at hu
    exact isUnit_of_mul_isUnit_left hu
  have hνD : IsUnit (((n + 1 : ℕ) : D)) := by
    have := hνu.map resA
    rwa [map_natCast] at this
  -- "In particular, `νh = g'_1 ∈ P'`": `νh = g'_1 = 0`, hence `h = 0`
  have hh0 : h = 0 := by
    have h1 := hc'zero ⟨0, Nat.succ_pos n⟩
    rw [hc'0] at h1
    have h2 : resA (a ⟨0, Nat.succ_pos n⟩) = 0 := hψ0
    rw [h2, add_zero] at h1
    exact (hνD.mul_right_eq_zero).mp h1
  -- "Hence `x = z + h ∈ P`": `h = 0` is `X ∈ q`
  exact (hres X).mp hh0

end CharZeroCore

section ChartChange

variable {R : Type u} [CommRing R] [IsRegularLocalRing R] [IsDomain R]

/-- A local ring map `α : R → B` into a local domain, injective and with `α x ∣ α p` for all
`p ∈ P`, is induced by a monoidal transform with center `P` and `x` as its first datum
(`R[x⁻¹P]` maps to `B` by `p/x ↦ α p / α x`, localized at the preimage of the maximal ideal). -/
theorem MonoidalTransform.exists_of_dvd_ringHom {B : Type v} [CommRing B] [IsDomain B]
    [IsLocalRing B] (P : Ideal R) (x : R) (hxP : x ∈ P) (hx0 : x ≠ 0) (α : R →+* B)
    [IsLocalHom α] (hα : Function.Injective α) (hdiv : ∀ p ∈ P, ∃ u, α p = α x * u) :
    ∃ (t : MonoidalTransform R P) (φ : t.ring →+* B), t.x = x ∧ IsLocalHom φ ∧
      φ.comp t.toRing = α ∧ Function.Injective φ ∧
      ∀ p ∈ P, ∀ u, α p = α x * u → ∃ y, t.toRing x * y = t.toRing p ∧ φ y = u := by
  classical
  let K := FractionRing R
  let L := FractionRing B
  have hinj : Function.Injective ((algebraMap B L).comp α) :=
    (IsFractionRing.injective B L).comp hα
  let ι : K →+* L := IsFractionRing.lift hinj
  have hι : ∀ r : R, ι (algebraMap R K r) = algebraMap B L (α r) := fun r =>
    IsFractionRing.lift_algebraMap hinj r
  have hαx : algebraMap B L (α x) ≠ 0 := fun h => by
    have h1 : α x = 0 := (IsFractionRing.injective B L) (by rw [h, map_zero])
    exact hx0 (hα (by rw [h1, map_zero]))
  have hxK : algebraMap R K x ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective R K)).mpr hx0
  have hgen : ∀ p ∈ P, ∀ u, α p = α x * u →
      ι (algebraMap R K p / algebraMap R K x) = algebraMap B L u := by
    intro p _ u hu
    rw [map_div₀, hι, hι, hu, map_mul]
    exact mul_div_cancel_left₀ _ hαx
  have key : ∀ k ∈ Algebra.adjoin R ((fun p => algebraMap R K p / algebraMap R K x) ''
      (P : Set R)), ∃ b : B, algebraMap B L b = ι k := by
    intro k hk
    induction hk using Algebra.adjoin_induction with
    | mem k hk =>
      obtain ⟨p, hp, rfl⟩ := hk
      obtain ⟨u, hu⟩ := hdiv p hp
      exact ⟨u, (hgen p hp u hu).symm⟩
    | algebraMap r => exact ⟨α r, (hι r).symm⟩
    | add a b _ _ ha hb =>
      obtain ⟨b1, hb1⟩ := ha
      obtain ⟨b2, hb2⟩ := hb
      exact ⟨b1 + b2, by rw [map_add, map_add, hb1, hb2]⟩
    | mul a b _ _ ha hb =>
      obtain ⟨b1, hb1⟩ := ha
      obtain ⟨b2, hb2⟩ := hb
      exact ⟨b1 * b2, by rw [map_mul, map_mul, hb1, hb2]⟩
  have hrange : ∀ a : blowupAlgebra R P x, ∃ b : B, algebraMap B L b = ι (a : K) :=
    fun a => key a a.2
  -- the ring map `ρ : R[x⁻¹P] → B`
  choose ρ0 hρ0 using hrange
  have hρ0inj : ∀ a b : blowupAlgebra R P x, ρ0 a = ρ0 b → ι (a : K) = ι (b : K) := by
    intro a b h; rw [← hρ0, ← hρ0, h]
  let ρ : blowupAlgebra R P x →+* B :=
    { toFun := ρ0
      map_one' := by
        apply IsFractionRing.injective B L
        rw [hρ0]; simp
      map_mul' := fun a b => by
        apply IsFractionRing.injective B L
        rw [hρ0]; simp only [MulMemClass.coe_mul, map_mul, hρ0]
      map_zero' := by
        apply IsFractionRing.injective B L
        rw [hρ0]; simp
      map_add' := fun a b => by
        apply IsFractionRing.injective B L
        rw [hρ0]; simp only [AddMemClass.coe_add, map_add, hρ0] }
  have hρ : ∀ a, algebraMap B L (ρ a) = ι (a : K) := hρ0
  have hρinj : Function.Injective ρ := by
    intro a b h
    have : ι (a : K) = ι (b : K) := by rw [← hρ, ← hρ]; exact congrArg _ h
    exact Subtype.ext (ι.injective this)
  have hρr : ∀ r, ρ (algebraMap R (blowupAlgebra R P x) r) = α r := by
    intro r
    apply IsFractionRing.injective B L
    rw [hρ, Subalgebra.coe_algebraMap, hι]
  have hMle : (maximalIdeal R).map (algebraMap R (blowupAlgebra R P x)) ≤
      (maximalIdeal B).comap ρ := by
    rw [Ideal.map_le_iff_le_comap]
    intro r hr
    show ρ (algebraMap R (blowupAlgebra R P x) r) ∈ maximalIdeal B
    rw [hρr]
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hr ⊢
    exact fun h => hr (IsLocalHom.map_nonunit r h)
  obtain ⟨M, hMprime, hMiff, hMle'⟩ : ∃ M : Ideal (blowupAlgebra R P x), M.IsPrime ∧
      (∀ a, a ∈ M ↔ ρ a ∈ maximalIdeal B) ∧
      (maximalIdeal R).map (algebraMap R (blowupAlgebra R P x)) ≤ M :=
    ⟨(maximalIdeal B).comap ρ, Ideal.comap_isPrime _ _, fun a => Iff.rfl, hMle⟩
  have hunit : ∀ y : M.primeCompl, IsUnit (ρ y) := fun y =>
    IsLocalRing.notMem_maximalIdeal.mp (fun h => y.2 ((hMiff y).mpr h))
  let φ0 : Localization.AtPrime M →+* B := IsLocalization.lift (M := M.primeCompl) hunit
  have hφ : ∀ a, φ0 (algebraMap (blowupAlgebra R P x) (Localization.AtPrime M) a) = ρ a :=
    fun a => IsLocalization.lift_eq hunit a
  have hloc : IsLocalHom φ0 := by
    refine ⟨fun y hy => ?_⟩
    obtain ⟨⟨a, s⟩, hs⟩ := IsLocalization.surj M.primeCompl y
    have h1 : φ0 y * ρ s = ρ a := by
      have := congrArg φ0 hs
      rwa [map_mul, hφ, hφ] at this
    have h2 : IsUnit (ρ a) := by rw [← h1]; exact hy.mul (hunit s)
    have h3 : a ∈ M.primeCompl := fun h => (IsLocalRing.notMem_maximalIdeal.mpr h2) ((hMiff a).mp h)
    have h4 := IsLocalization.map_units (Localization.AtPrime M) (⟨a, h3⟩ : M.primeCompl)
    rw [← hs] at h4
    exact isUnit_of_mul_isUnit_left h4
  have hφinj : Function.Injective φ0 := by
    rw [injective_iff_map_eq_zero]
    intro y hy
    obtain ⟨⟨a, s⟩, hs⟩ := IsLocalization.surj M.primeCompl y
    have h1 : φ0 y * ρ s = ρ a := by
      have := congrArg φ0 hs
      rwa [map_mul, hφ, hφ] at this
    rw [hy, zero_mul] at h1
    have h2 : a = 0 := hρinj (by rw [← h1, map_zero])
    rw [h2, map_zero] at hs
    have h4 := IsLocalization.map_units (Localization.AtPrime M) s
    exact (h4.mul_left_eq_zero).mp hs
  have hprop : ∀ p ∈ P, ∀ u, α p = α x * u → ∃ y : Localization.AtPrime M,
      algebraMap (blowupAlgebra R P x) (Localization.AtPrime M) (algebraMap R _ x) * y =
        algebraMap (blowupAlgebra R P x) (Localization.AtPrime M) (algebraMap R _ p) ∧
        φ0 y = u := by
    intro p hp u hu
    have hmem : algebraMap R K p / algebraMap R K x ∈ blowupAlgebra R P x :=
      Algebra.subset_adjoin ⟨p, hp, rfl⟩
    refine ⟨algebraMap (blowupAlgebra R P x) (Localization.AtPrime M) ⟨_, hmem⟩, ?_, ?_⟩
    · rw [← map_mul]
      congr 1
      apply Subtype.ext
      simp only [MulMemClass.coe_mul, Subalgebra.coe_algebraMap]
      field_simp
      rfl
    · rw [hφ]
      apply IsFractionRing.injective B L
      rw [hρ]
      exact hgen p hp u hu
  refine ⟨⟨x, hxP, hx0, M, hMprime, hMle'⟩, φ0, rfl, hloc, ?_, hφinj, hprop⟩
  ext r
  show φ0 (algebraMap _ (Localization.AtPrime M) (algebraMap R (blowupAlgebra R P x) r)) = α r
  rw [hφ]
  exact hρr r

/-- Change of chart (p. 209): a monoidal transform `T` with center `P` may be presented with any
`x' ∈ P` such that `T(x') R' = P R'`. -/
theorem MonoidalTransform.exists_ringEquiv_of_span_eq {P : Ideal R} (T : MonoidalTransform R P)
    [IsLocalHom T.toRing] (x' : R) (hx'P : x' ∈ P) (hx'0 : x' ≠ 0)
    (hspan : Ideal.span {T.toRing x'} = P.map T.toRing) :
    ∃ (T' : MonoidalTransform R P) (φ : T'.ring ≃+* T.ring), T'.x = x' ∧
      ∀ r, φ (T'.toRing r) = T.toRing r := by
  classical
  have hdiv : ∀ p ∈ P, ∃ u, T.toRing p = T.toRing x' * u := by
    intro p hp
    have : T.toRing p ∈ Ideal.span {T.toRing x'} := by
      rw [hspan]; exact Ideal.mem_map_of_mem _ hp
    obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.mp this
    exact ⟨a, by rw [← ha, mul_comm]⟩
  obtain ⟨T', φ, hx, hloc, hcomp, hinj, hprop⟩ := MonoidalTransform.exists_of_dvd_ringHom P x'
    hx'P hx'0 T.toRing T.toRing_injective hdiv
  have hxR0 : T.xR ≠ 0 := fun h =>
    T.x_ne_zero (T.toRing_injective (h.trans (map_zero _).symm))
  -- the range of `φ` is saturated
  have hsat : ∀ c ∈ φ.range, IsUnit c → ∃ d ∈ φ.range, d * c = 1 := by
    rintro c ⟨w, rfl⟩ hc
    have hw : IsUnit w := hloc.map_nonunit w hc
    obtain ⟨v, rfl⟩ := hw
    exact ⟨φ (↑v⁻¹), ⟨_, rfl⟩, by rw [← map_mul, Units.inv_mul, map_one]⟩
  obtain ⟨d, hd⟩ := hdiv T.x T.x_mem
  obtain ⟨y1, hy1, hy1'⟩ := hprop T.x T.x_mem d hd
  have hdR : d ∈ φ.range := ⟨y1, hy1'⟩
  obtain ⟨c, hc⟩ : ∃ c, T.toRing x' = T.xR * c := by
    have : T.toRing x' ∈ Ideal.span {T.xR} := by
      rw [T.span_xR_eq_map]; exact Ideal.mem_map_of_mem _ hx'P
    obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.mp this
    exact ⟨a, by rw [← ha, mul_comm]⟩
  have hcd : c * d = 1 := by
    apply mul_left_cancel₀ hxR0
    show T.xR * (c * d) = T.xR * 1
    have : T.toRing T.x = T.toRing x' * d := hd
    rw [mul_one, ← mul_assoc, ← hc]
    exact this.symm
  have hcR : c ∈ φ.range := by
    obtain ⟨d', hd'R, hd'⟩ := hsat d hdR (Units.mk d c (by rw [mul_comm]; exact hcd) hcd).isUnit
    have : d' = c := by
      calc d' = d' * (c * d) := by rw [hcd, mul_one]
        _ = (d' * d) * c := by ring
        _ = c := by rw [hd', one_mul]
    rw [← this]; exact hd'R
  -- every element of the blow-up algebra of `T` is in the range
  have key : ∀ k ∈ Algebra.adjoin R ((fun p => algebraMap R (FractionRing R) p /
      algebraMap R (FractionRing R) T.x) '' (P : Set R)),
      ∀ hk : k ∈ blowupAlgebra R P T.x, algebraMap (blowupAlgebra R P T.x) T.ring ⟨k, hk⟩ ∈
        φ.range := by
    intro k hk
    induction hk using Algebra.adjoin_induction with
    | mem k hk =>
      obtain ⟨p, hp, rfl⟩ := hk
      intro hk'
      obtain ⟨u'', hu''⟩ := hdiv p hp
      obtain ⟨y2, -, hy2'⟩ := hprop p hp u'' hu''
      have hy : T.xR * algebraMap (blowupAlgebra R P T.x) T.ring ⟨_, hk'⟩ = T.toRing p := by
        show algebraMap _ T.ring (algebraMap R (blowupAlgebra R P T.x) T.x) * _ =
          algebraMap _ T.ring (algebraMap R (blowupAlgebra R P T.x) p)
        rw [← map_mul]
        congr 1
        apply Subtype.ext
        simp only [MulMemClass.coe_mul, Subalgebra.coe_algebraMap]
        have hxK : algebraMap R (FractionRing R) T.x ≠ 0 :=
          (map_ne_zero_iff _ (IsFractionRing.injective R (FractionRing R))).mpr T.x_ne_zero
        field_simp
      have : algebraMap (blowupAlgebra R P T.x) T.ring ⟨_, hk'⟩ = c * u'' := by
        apply mul_left_cancel₀ hxR0
        rw [hy, hu'', hc]; ring
      rw [this]
      exact Subring.mul_mem _ hcR ⟨y2, hy2'⟩
    | algebraMap r =>
      intro hk'
      have : algebraMap (blowupAlgebra R P T.x) T.ring ⟨_, hk'⟩ = T.toRing r := rfl
      rw [this, ← hcomp]
      exact ⟨T'.toRing r, rfl⟩
    | add a b ha hb pa pb =>
      intro hk'
      have e : algebraMap (blowupAlgebra R P T.x) T.ring ⟨a + b, hk'⟩ =
          algebraMap (blowupAlgebra R P T.x) T.ring ⟨a, ha⟩ +
            algebraMap (blowupAlgebra R P T.x) T.ring ⟨b, hb⟩ := by
        rw [← map_add]; rfl
      rw [e]
      exact Subring.add_mem _ (pa ha) (pb hb)
    | mul a b ha hb pa pb =>
      intro hk'
      have e : algebraMap (blowupAlgebra R P T.x) T.ring ⟨a * b, hk'⟩ =
          algebraMap (blowupAlgebra R P T.x) T.ring ⟨a, ha⟩ *
            algebraMap (blowupAlgebra R P T.x) T.ring ⟨b, hb⟩ := by
        rw [← map_mul]; rfl
      rw [e]
      exact Subring.mul_mem _ (pa ha) (pb hb)
  have hsurj : Function.Surjective φ := by
    intro y
    obtain ⟨⟨a, s⟩, hs⟩ := IsLocalization.surj T.M'.primeCompl y
    have ha : algebraMap (blowupAlgebra R P T.x) T.ring a ∈ φ.range := key a a.2 a.2
    have hs' : algebraMap (blowupAlgebra R P T.x) T.ring (s : blowupAlgebra R P T.x) ∈ φ.range :=
      key s s.1.2 s.1.2
    obtain ⟨d', hd'R, hd'⟩ := hsat _ hs' (IsLocalization.map_units T.ring s)
    have : y = algebraMap (blowupAlgebra R P T.x) T.ring a * d' := by
      calc y = y * (d' * algebraMap (blowupAlgebra R P T.x) T.ring (s : blowupAlgebra R P T.x)) := by
            rw [hd', mul_one]
        _ = _ := by simp only at hs; rw [← hs]; ring
    rw [this]
    exact Subring.mul_mem _ ha hd'R
  exact ⟨T', RingEquiv.ofBijective φ ⟨hinj, hsurj⟩, hx, fun r => RingHom.congr_fun hcomp r⟩


end ChartChange

section FrameGenerators

variable {R : Type u} [CommRing R] [IsRegularLocalRing R]

/-- For a regular frame with `r = 1`, every `r ∈ R` is `≡ s (mod z)` for some `s ∈ S`. -/
theorem RegularFrame.exists_sub_mem_span_singleton (F : RegularFrame R) (z : R)
    (hzF : ∀ j, F.z j = z) (hr : F.r = 1) (r : R) :
    ∃ s : F.S, r - algebraMap F.S R s ∈ Ideal.span {z} := by
  have hrange : Set.range F.z = {z} := by
    ext y
    constructor
    · rintro ⟨j, rfl⟩; exact hzF j
    · rintro rfl; exact ⟨⟨0, by rw [hr]; exact Nat.one_pos⟩, hzF _⟩
  obtain ⟨s, hs⟩ := F.quot_bijective.2 (Ideal.Quotient.mk (Ideal.span (Set.range F.z)) r)
  refine ⟨s, ?_⟩
  have h1 := Ideal.Quotient.eq.mp hs
  rw [hrange] at h1
  have := Ideal.neg_mem_iff _ |>.mpr h1
  simpa using this

/-- `S/(Q ∩ S) ≅ R/Q` when `z ∈ Q`. -/
theorem RegularFrame.quotient_regular (F : RegularFrame R) (z : R)
    (hzF : ∀ j, F.z j = z) (hr : F.r = 1) (Q : Ideal R) [Q.IsPrime]
    [IsRegularLocalRing (R ⧸ Q)] (hzQ : z ∈ Q) :
    IsRegularLocalRing (F.S ⧸ Q.comap (algebraMap F.S R)) := by
  let ψ : F.S →+* R ⧸ Q := (Ideal.Quotient.mk Q).comp (algebraMap F.S R)
  have hψ : Function.Surjective ψ := by
    intro y
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective y
    obtain ⟨s, hs⟩ := F.exists_sub_mem_span_singleton z hzF hr r
    refine ⟨s, ?_⟩
    show Ideal.Quotient.mk Q (algebraMap F.S R s) = Ideal.Quotient.mk Q r
    rw [Ideal.Quotient.eq]
    have : algebraMap F.S R s - r ∈ Ideal.span {z} := by
      have := Ideal.neg_mem_iff _ |>.mpr hs
      simpa using this
    exact (Ideal.span_singleton_le_iff_mem _ |>.mpr hzQ) this
  have hker : RingHom.ker ψ = Q.comap (algebraMap F.S R) := by
    ext s
    rw [RingHom.mem_ker, Ideal.mem_comap]
    exact Ideal.Quotient.eq_zero_iff_mem
  have e2 : F.S ⧸ Q.comap (algebraMap F.S R) ≃+* R ⧸ Q :=
    (Ideal.quotEquivOfEq hker.symm).trans (RingHom.quotientKerEquivOfSurjective hψ)
  exact IsRegularLocalRing.of_ringEquiv e2.symm


section FrameGeneratorsDomain

variable [IsDomain R]

/-- Minimal generators of `M_S` with `Q ∩ S = (zS)` give minimal generators of `M` and of `Q`
by adjoining `z`. -/
theorem RegularFrame.exists_generators_append (F : RegularFrame R) (z : R)
    (hzF : ∀ j, F.z j = z) (hr : F.r = 1) (Q : Ideal R) [Q.IsPrime] (hzQ : z ∈ Q)
    (SS : Finset F.S) (hSSspan : Ideal.span (SS : Set F.S) = maximalIdeal F.S)
    (hSScard : SS.card = (maximalIdeal F.S).spanFinrank) {rs : ℕ} (zS : Fin (rs + 1) → F.S)
    (hzSinj : Function.Injective zS) (hzSmem : ∀ i, zS i ∈ SS)
    (hzSspan : Ideal.span (Set.range zS) = Q.comap (algebraMap F.S R)) :
    ∃ (SR : Finset R) (Z : Fin (rs + 1 + 1) → R),
      Ideal.span (SR : Set R) = maximalIdeal R ∧ SR.card = (maximalIdeal R).spanFinrank ∧
      Function.Injective Z ∧ (∀ i, Z i ∈ SR) ∧ Z 0 = algebraMap F.S R (zS 0) ∧ Z 1 = z ∧
      (∀ j : Fin rs, Z j.succ.succ = algebraMap F.S R (zS j.succ)) ∧
      Ideal.span (Set.range Z) = Q := by
  classical
  have hzne : z ≠ 0 := by
    have hmem : z ∈ Finset.image F.z Finset.univ :=
      Finset.mem_image.mpr ⟨⟨0, by rw [hr]; exact Nat.one_pos⟩, Finset.mem_univ _, hzF _⟩
    exact F.extends_rsop.ne_zero hmem
  have hzM : z ∈ maximalIdeal R := by
    have hmem : z ∈ Finset.image F.z Finset.univ :=
      Finset.mem_image.mpr ⟨⟨0, by rw [hr]; exact Nat.one_pos⟩, Finset.mem_univ _, hzF _⟩
    exact F.extends_rsop.mem_maximalIdeal hmem
  have hinjS : Function.Injective (algebraMap F.S R) := fun a b hab =>
    F.quot_bijective.1 (by simp only [RingHom.comp_apply]; rw [hab])
  have halg : ∀ s : F.S, algebraMap F.S R s ∈ maximalIdeal R ↔ s ∈ maximalIdeal F.S := by
    intro s
    simp only [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    exact ⟨fun h hs => h (hs.map _), fun h hu => h (IsLocalHom.map_nonunit s hu)⟩
  have hrange : Set.range F.z = {z} := by
    ext y
    constructor
    · rintro ⟨j, rfl⟩; exact hzF j
    · rintro rfl; exact ⟨⟨0, by rw [hr]; exact Nat.one_pos⟩, hzF _⟩
  have hznot : ∀ s : F.S, algebraMap F.S R s ≠ z := by
    intro s hs
    have h1 : (Ideal.Quotient.mk (Ideal.span (Set.range F.z))).comp (algebraMap F.S R) s =
        (Ideal.Quotient.mk (Ideal.span (Set.range F.z))).comp (algebraMap F.S R) 0 := by
      simp only [RingHom.comp_apply, map_zero]
      rw [hs, Ideal.Quotient.eq_zero_iff_mem, hrange]
      exact Ideal.subset_span rfl
    have := F.quot_bijective.1 h1
    rw [this, map_zero] at hs
    exact hzne hs.symm
  -- the generating set
  let SR : Finset R := SS.image (algebraMap F.S R) ∪ {z}
  have hSRspan : Ideal.span (SR : Set R) = maximalIdeal R := by
    apply le_antisymm
    · rw [Ideal.span_le]
      intro a ha
      simp only [SR, Finset.coe_union, Finset.coe_image, Finset.coe_singleton, Set.mem_union,
        Set.mem_image, Finset.mem_coe, Set.mem_singleton_iff] at ha
      rcases ha with ⟨s, hs, rfl⟩ | rfl
      · exact (halg s).mpr (hSSspan ▸ Ideal.subset_span hs)
      · exact hzM
    · intro r hr'
      obtain ⟨s, hs⟩ := F.exists_sub_mem_span_singleton z hzF hr r
      have hzspan : Ideal.span {z} ≤ Ideal.span (SR : Set R) :=
        Ideal.span_mono (by simp [SR])
      have hsM : algebraMap F.S R s ∈ maximalIdeal R := by
        have : algebraMap F.S R s = r - (r - algebraMap F.S R s) := by ring
        rw [this]
        exact sub_mem hr' ((Ideal.span_singleton_le_iff_mem _).mpr hzM hs)
      have hsN : s ∈ Ideal.span (SS : Set F.S) := hSSspan ▸ (halg s).mp hsM
      have h1 : algebraMap F.S R s ∈ Ideal.span (SR : Set R) := by
        have := Ideal.mem_map_of_mem (algebraMap F.S R) hsN
        rw [Ideal.map_span] at this
        refine Ideal.span_mono ?_ this
        intro a ha
        obtain ⟨b, hb, rfl⟩ := ha
        simp only [SR, Finset.coe_union, Finset.coe_image]
        exact Or.inl ⟨b, hb, rfl⟩
      have : r = algebraMap F.S R s + (r - algebraMap F.S R s) := by ring
      rw [this]
      exact add_mem h1 (hzspan hs)
  have hdisj : Disjoint (SS.image (algebraMap F.S R)) {z} := by
    rw [Finset.disjoint_singleton_right]
    intro h
    obtain ⟨s, -, hs⟩ := Finset.mem_image.mp h
    exact hznot s hs
  have hSRcard : SR.card = SS.card + 1 := by
    simp only [SR]
    rw [Finset.card_union_of_disjoint hdisj, Finset.card_image_of_injective _ hinjS,
      Finset.card_singleton]
  have hcardle : (maximalIdeal R).spanFinrank ≤ SR.card := by
    have h := Submodule.spanFinrank_span_le_ncard_of_finite (R := R) (Finset.finite_toSet SR)
    rw [Set.ncard_coe_finset] at h
    have h' : (Ideal.span (SR : Set R)).spanFinrank ≤ SR.card := h
    rwa [hSRspan] at h'
  have hsp : Ideal.span (Set.range F.z) = Ideal.span {z} := by rw [hrange]
  have hbij : Function.Bijective ((Ideal.quotEquivOfEq hsp).toRingHom.comp
      ((Ideal.Quotient.mk (Ideal.span (Set.range F.z))).comp (algebraMap F.S R))) :=
    (Ideal.quotEquivOfEq hsp).bijective.comp F.quot_bijective
  have hdim : ringKrullDim F.S + 1 ≤ ringKrullDim R := by
    have h1 := ringKrullDim_quotient_succ_le_of_nonZeroDivisor (mem_nonZeroDivisors_of_ne_zero hzne)
    rwa [← ringKrullDim_eq_of_ringEquiv (RingEquiv.ofBijective _ hbij)] at h1
  have hgecard : SS.card + 1 ≤ (maximalIdeal R).spanFinrank := by
    have h1 := IsRegularLocalRing.spanFinrank_maximalIdeal (R := R)
    have h2 := IsRegularLocalRing.spanFinrank_maximalIdeal (R := F.S)
    rw [← h1, ← h2] at hdim
    rw [hSScard]
    exact_mod_cast hdim
  have hSRcard' : SR.card = (maximalIdeal R).spanFinrank := le_antisymm (by omega) hcardle
  -- the generators `Z`
  let Z : Fin (rs + 1 + 1) → R := Fin.cons (algebraMap F.S R (zS 0))
    (Fin.cons z (fun j : Fin rs => algebraMap F.S R (zS j.succ)))
  have hZ0 : Z 0 = algebraMap F.S R (zS 0) := by simp [Z]
  have hZ1' : Z ((0 : Fin (rs + 1)).succ) = z := by simp [Z]
  have hZ1 : Z 1 = z := by
    have : (1 : Fin (rs + 1 + 1)) = (0 : Fin (rs + 1)).succ := by simp
    rw [this]; exact hZ1'
  have hZ2 : ∀ j : Fin rs, Z j.succ.succ = algebraMap F.S R (zS j.succ) := by
    intro j; simp [Z]
  have hZinj : Function.Injective Z := by
    refine Fin.cons_injective_iff.mpr ⟨?_, ?_⟩
    · rintro ⟨i, hi⟩
      revert hi
      refine Fin.cases ?_ (fun j => ?_) i
      · intro hi
        simp only [Fin.cons_zero] at hi
        exact hznot (zS 0) hi.symm
      · intro hi
        simp only [Fin.cons_succ] at hi
        exact Fin.succ_ne_zero j (hzSinj (hinjS hi))
    · refine Fin.cons_injective_iff.mpr ⟨?_, ?_⟩
      · rintro ⟨j, hj⟩
        exact hznot (zS j.succ) (by simpa using hj)
      · intro a b hab
        exact Fin.succ_injective _ (hzSinj (hinjS hab))
  have hS : ∀ k : Fin (rs + 1), algebraMap F.S R (zS k) ∈ Q := fun k =>
    Ideal.mem_comap.mp (hzSspan ▸ Ideal.subset_span ⟨k, rfl⟩)
  refine ⟨SR, Z, hSRspan, hSRcard', hZinj, ?_, hZ0, hZ1, hZ2, ?_⟩
  · intro i
    refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun k => ?_) j) i
    · rw [hZ0]
      exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨zS 0, hzSmem 0, rfl⟩)
    · rw [hZ1']
      exact Finset.mem_union_right _ (Finset.mem_singleton_self z)
    · rw [hZ2]
      exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨zS k.succ, hzSmem _, rfl⟩)
  · apply le_antisymm
    · rw [Ideal.span_le]
      rintro _ ⟨i, rfl⟩
      refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun k => ?_) j) i
      · rw [hZ0]; exact hS 0
      · rw [hZ1']; exact hzQ
      · rw [hZ2]; exact hS _
    · intro q hq
      obtain ⟨s, hs⟩ := F.exists_sub_mem_span_singleton z hzF hr q
      have hzspan : Ideal.span {z} ≤ Ideal.span (Set.range Z) :=
        Ideal.span_mono (by rintro _ rfl; exact ⟨1, hZ1⟩)
      have hsQ : algebraMap F.S R s ∈ Q := by
        have : algebraMap F.S R s = q - (q - algebraMap F.S R s) := by ring
        rw [this]
        exact sub_mem hq ((Ideal.span_singleton_le_iff_mem _).mpr hzQ hs)
      have hsP : s ∈ Ideal.span (Set.range zS) := hzSspan ▸ Ideal.mem_comap.mpr hsQ
      have h1 : algebraMap F.S R s ∈ Ideal.span (Set.range Z) := by
        have := Ideal.mem_map_of_mem (algebraMap F.S R) hsP
        rw [Ideal.map_span] at this
        refine Ideal.span_mono ?_ this
        rintro _ ⟨_, ⟨k, rfl⟩, rfl⟩
        refine Fin.cases ?_ (fun j => ?_) k
        · exact ⟨0, hZ0⟩
        · exact ⟨j.succ.succ, hZ2 j⟩
      have : q = algebraMap F.S R s + (q - algebraMap F.S R s) := by ring
      rw [this]
      exact add_mem h1 (hzspan hs)

end FrameGeneratorsDomain

end FrameGenerators

section FiberModel

variable {R : Type u} [CommRing R] [IsRegularLocalRing R]

/-- p. 209--210 ("well known"), in the form needed for p. 318: for a monoidal transform
`T` of `R` with centre `Q` (`R/Q` regular), a frame `(S; z)` with `r = 1` and `z ∈ Q`, and an
element `x₀ ∈ Q ∩ S` with `x₀ R₁ = Q R₁`, the fibre `R₁/x₀R₁` is the localization of a
polynomial ring `A[X]`, `A = (R/Q)[T_S]`, at a prime `q`, with `X ↦ z/x₀` and
`A` containing the images `c/x₀^n` of all elements `c ∈ (Q ∩ S)^n`.

Proof: (1) change of chart `x ↦ x₀`
(`x₀/T.x` is a unit of `R₁` since both generate `Q R₁`), identifying `R₁` with
`R[Q/x₀]_{M''}`; (2) `Q∩S = (x₀, y₂, …, y_s)` with `x₀` part of a minimal base of `Q∩S`
(otherwise `x₀ ∈ N·(Q∩S)` and `ξ ∈ w·M₁`), extended by `z` to a minimal base of `M` (as
`M = N R + z R`); (3) `MonoidalTransform.exists_quotient_equiv_localization` for the generators
`(x₀, y₂, …, y_s, z)`, giving `R₁/x₀R₁ ≅ (R/Q)[T₂, …, T_s, X]_q`, `A = (R/Q)[T₂, …, T_s]`;
(4) `c ∈ (Q∩S)^n` is a polynomial of degree `n` in `x₀, y₂, …, y_s` with `S`-coefficients, so
`c/x₀^n ≡` a polynomial in the `T_k` with coefficients in `R/Q`; (5) `k` is a unit in `R/Q`
since the residue field of `R/Q` is that of `S` (frame), of characteristic `0`.
Deviation from the paper (gap filled): the paper uses the fibre structure without comment
(p. 318 "we apply Lemma 22").  Its p. 209 remark "If `(x₁, …, x_r)` is a minimal base of the prime
ideal `P` and `R'` is a monoidal transform of `R` with center `P`, then there exist an index `i` and
a prime ideal `M'` in `R[x₁/x_i, …, x_r/x_i]` such that `R' = R[x₁/x_i, …, x_r/x_i]_{M'}`" is
used tacitly for the minimal base `(x₀, y₂, …, y_s, z)` of `Q`; Lean proves the chart change it
needs (`MonoidalTransform.exists_ringEquiv_of_span_eq`), and obtains the minimal base of `Q ∩ S`
through `x₀` by building a monoidal transform of `S` with `x = x₀` from `T`
(`MonoidalTransform.exists_of_dvd_ringHom`) and applying `exists_minimal_generators` to it. -/
@[blueprint "lem:IV.CD-4-fiber-model"
  (statement := /-- Let $R$ be a regular local ring with a regular frame $(S;z)$, $r=1$, $Q$ a
    prime ideal with $R/Q$ regular and $z\in Q$, $R_1=R[x^{-1}Q]_{M'}$ a monoidal transform,
    and $x_0\in Q\cap S$ with $x_0R_1=QR_1$. Then there are a ring $A$ in which every
    positive integer is a unit, a prime $q$ of $A[X]$ and an isomorphism
    $A[X]_q\cong R_1/x_0R_1$ mapping $X$ to the class of $z/x_0$, mapping $A$ onto classes
    containing all $c/x_0^n$ with $c\in(Q\cap S)^n$, and carrying the maximal ideal to the
    maximal ideal. -/)
  (proof := /-- Change the chart of the monoidal transform to $x_0$, take
    a minimal base $(x_0,y_2,\dots,y_s)$ of $Q\cap S$ extended by $z$ to a minimal base of $M$,
    and apply the local structure of $R_1/xR_1$ (\cref{lem:III.2-monoidal-transform-regular},
    pp.~209--210) with $A=(R/Q)[T_2,\dots,T_s]$ and $X=z/x_0$; an element of $(Q\cap S)^n$ is
    a polynomial of degree $n$ in $x_0,y_2,\dots,y_s$ with coefficients in $S$.

    \textbf{Deviation from the paper (gap filled).} The paper uses this structure without
    comment (p.~318, ``we apply Lemma~22''); its remark on p.~209 that a monoidal transform with
    center $P$ is a localization of $R[x_1/x_i,\dots,x_r/x_i]$ for some index $i$ of a minimal
    base is used tacitly, and the chart change to $x_0$ (any generator of $QR_1$) is proved. -/)
  (latexEnv := "lemma")]
theorem exists_fiber_polynomial_model [IsDomain R] (F : RegularFrame R) (z : R)
    (hzF : ∀ j, F.z j = z) (hr : F.r = 1) [CharZero (ResidueField F.S)]
    (Q : Ideal R) [Q.IsPrime] [IsRegularLocalRing (R ⧸ Q)] (hzQ : z ∈ Q)
    (T : MonoidalTransform R Q) [IsLocalHom T.toRing] [IsRegularLocalRing T.ring]
    (x₀ : F.S) (hx₀Q : algebraMap F.S R x₀ ∈ Q)
    (hx₀T : Ideal.span {T.toRing (algebraMap F.S R x₀)} = Q.map T.toRing) :
    ∃ (A : Type u) (_ : CommRing A) (q : Ideal A[X]) (_ : q.IsPrime)
      (e : Localization.AtPrime q ≃+*
        (T.ring ⧸ Ideal.span {T.toRing (algebraMap F.S R x₀)})),
      (∀ k : ℕ, k ≠ 0 → IsUnit (k : A)) ∧
      (∀ η : T.ring, T.toRing (algebraMap F.S R x₀) * η = T.toRing z →
        e (algebraMap A[X] (Localization.AtPrime q) X) = Ideal.Quotient.mk _ η) ∧
      (∀ (n : ℕ) (c : F.S), c ∈ (Q.comap (algebraMap F.S R)) ^ n → ∀ c' : T.ring,
        T.toRing (algebraMap F.S R c) = T.toRing (algebraMap F.S R x₀) ^ n * c' →
        ∃ a : A, e (algebraMap A[X] (Localization.AtPrime q) (C a)) = Ideal.Quotient.mk _ c') ∧
      (∀ y : T.ring, y ∈ maximalIdeal T.ring ↔
        e.symm (Ideal.Quotient.mk _ y) ∈ maximalIdeal (Localization.AtPrime q)) := by
  classical
  have := F.isDomain_S
  have hdomT := isDomain_of_isRegularLocalRing T.ring
  have hzne : z ≠ 0 := by
    have hmem : z ∈ Finset.image F.z Finset.univ :=
      Finset.mem_image.mpr ⟨⟨0, by rw [hr]; exact Nat.one_pos⟩, Finset.mem_univ _, hzF _⟩
    exact F.extends_rsop.ne_zero hmem
  have hinjS : Function.Injective (algebraMap F.S R) := fun a b hab =>
    F.quot_bijective.1 (by simp only [RingHom.comp_apply]; rw [hab])
  set ξ : T.ring := T.toRing (algebraMap F.S R x₀) with hξ
  have hξ0 : ξ ≠ 0 := by
    intro h0
    have : T.toRing z ∈ Ideal.span {ξ} := by
      rw [hx₀T]; exact Ideal.mem_map_of_mem _ hzQ
    rw [h0, Ideal.span_singleton_eq_bot.mpr rfl, Ideal.mem_bot] at this
    exact hzne (T.toRing_injective (by rw [this, map_zero]))
  have hx₀0 : x₀ ≠ 0 := fun h => hξ0 (by rw [hξ, h, map_zero, map_zero])
  have hPSprime : (Q.comap (algebraMap F.S R)).IsPrime := Ideal.comap_isPrime _ _
  have hSreg := F.quotient_regular z hzF hr Q hzQ
  have hdivT : ∀ r ∈ Q, ∃ v, T.toRing r = ξ * v := by
    intro r hr'
    have : T.toRing r ∈ Ideal.span {ξ} := by
      rw [hx₀T]; exact Ideal.mem_map_of_mem _ hr'
    obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.mp this
    exact ⟨a, by rw [← ha, mul_comm]⟩
  -- a monoidal transform of `S` with centre `Q ∩ S` and `x = x₀`
  have : IsLocalHom (T.toRing.comp (algebraMap F.S R)) := inferInstance
  obtain ⟨TS, -, hTSx, -, -, -, -⟩ := MonoidalTransform.exists_of_dvd_ringHom
    (R := F.S) (Q.comap (algebraMap F.S R)) x₀ (Ideal.mem_comap.mpr hx₀Q) hx₀0
    (T.toRing.comp (algebraMap F.S R)) (T.toRing_injective.comp hinjS)
    (fun p hp => hdivT _ (Ideal.mem_comap.mp hp))
  obtain ⟨SS, rs, zS, hSSspan, hSScard, hzSinj, hzSmem, hzS0, hzSspan⟩ :=
    TS.exists_minimal_generators hSreg
  have hzS0' : zS 0 = x₀ := hzS0.trans hTSx
  obtain ⟨SR, Z, hSRspan, hSRcard, hZinj, hZmem, hZ0, hZ1, hZ2, hZspan⟩ :=
    F.exists_generators_append z hzF hr Q hzQ SS hSSspan hSScard zS hzSinj hzSmem hzSspan
  -- change of chart
  have hx₀R0 : algebraMap F.S R x₀ ≠ 0 := fun h => hx₀0 (hinjS (by rw [h, map_zero]))
  obtain ⟨T', φ, hT'x, hφcomp⟩ := T.exists_ringEquiv_of_span_eq (algebraMap F.S R x₀) hx₀Q hx₀R0
    hx₀T
  have hZ0' : Z 0 = T'.x := by rw [hZ0, hzS0', hT'x]
  obtain ⟨q₀, hq₀, e₀, -, -, hc, hu⟩ := T'.exists_quotient_equiv_localization inferInstance
    hSRspan hSRcard hZinj hZmem hZ0' hZspan
  have := hq₀
  have hZQ : ∀ i, Z i ∈ Q := fun i => hZspan ▸ Ideal.subset_span ⟨i, rfl⟩
  -- the polynomial ring `A[X]`, `A = (R/Q)[T_S]`
  let g : MvPolynomial (Fin (rs + 1)) (R ⧸ Q) ≃+* (MvPolynomial (Fin rs) (R ⧸ Q))[X] :=
    (MvPolynomial.finSuccEquiv (R ⧸ Q) rs).toRingEquiv
  let q : Ideal (MvPolynomial (Fin rs) (R ⧸ Q))[X] := q₀.comap g.symm
  have hqprime : q.IsPrime := Ideal.comap_isPrime _ _
  have H : q₀.primeCompl.map g.toMonoidHom = q.primeCompl := by
    ext y
    constructor
    · rintro ⟨a, ha, rfl⟩
      show g.symm (g a) ∉ q₀
      rw [g.symm_apply_apply]; exact ha
    · intro hy
      exact ⟨g.symm y, hy, g.apply_symm_apply y⟩
  let Eloc : Localization.AtPrime q₀ ≃+* Localization.AtPrime q :=
    IsLocalization.ringEquivOfRingEquiv (Localization.AtPrime q₀) (Localization.AtPrime q) g H
  have hEloc : ∀ y, Eloc (algebraMap _ (Localization.AtPrime q₀) y) =
      algebraMap _ (Localization.AtPrime q) (g y) := fun y =>
    IsLocalization.ringEquivOfRingEquiv_eq H y
  have hxR : φ T'.xR = ξ := by
    show φ (T'.toRing T'.x) = ξ
    rw [hφcomp, hT'x]
  let ψ : T'.ring ⧸ Ideal.span {T'.xR} ≃+* T.ring ⧸ Ideal.span {ξ} :=
    Ideal.quotientEquiv (Ideal.span {T'.xR}) (Ideal.span {ξ}) φ (by
      rw [Ideal.map_span, Set.image_singleton]
      show _ = Ideal.span {φ T'.xR}
      rw [hxR])
  let e : Localization.AtPrime q ≃+* T.ring ⧸ Ideal.span {ξ} := Eloc.symm.trans (e₀.trans ψ)
  have he : ∀ y, e (algebraMap _ (Localization.AtPrime q) (g y)) =
      ψ (e₀ (algebraMap _ (Localization.AtPrime q₀) y)) := by
    intro y
    show ψ (e₀ (Eloc.symm _)) = _
    rw [← hEloc y, Eloc.symm_apply_apply]
  -- the elements `v i = Z (i+1) / ξ`
  choose v hv using fun i : Fin (rs + 1) => hdivT (Z i.succ) (hZQ i.succ)
  have hh : ∀ i, T'.toRing T'.x * φ.symm (v i) = T'.toRing (Z i.succ) := by
    intro i
    apply φ.injective
    rw [map_mul, hφcomp, hφcomp, hT'x, φ.apply_symm_apply, hv i]
  have hu' := hu (fun i => φ.symm (v i)) hh
  have hψX : ∀ i, ψ (e₀ (algebraMap _ (Localization.AtPrime q₀)
      (MvPolynomial.X i : MvPolynomial (Fin (rs + 1)) (R ⧸ Q)))) =
      Ideal.Quotient.mk _ (v i) := by
    intro i
    rw [(hu' i).2]
    show Ideal.Quotient.mk _ (φ (φ.symm (v i))) = _
    rw [φ.apply_symm_apply]
  have hψC : ∀ c : R, ψ (e₀ (algebraMap _ (Localization.AtPrime q₀)
      (MvPolynomial.C (Ideal.Quotient.mk Q c) : MvPolynomial (Fin (rs + 1)) (R ⧸ Q)))) =
      Ideal.Quotient.mk _ (T.toRing c) := by
    intro c
    rw [hc c]
    show Ideal.Quotient.mk _ (φ (T'.toRing c)) = _
    rw [hφcomp]
  have hgX0 : g (MvPolynomial.X 0 : MvPolynomial (Fin (rs + 1)) (R ⧸ Q)) = Polynomial.X := MvPolynomial.finSuccEquiv_X_zero
  have hgXs : ∀ j : Fin rs, g (MvPolynomial.X j.succ : MvPolynomial (Fin (rs + 1)) (R ⧸ Q)) = Polynomial.C (MvPolynomial.X j : MvPolynomial (Fin rs) (R ⧸ Q)) :=
    fun j => MvPolynomial.finSuccEquiv_X_succ
  have hgC : ∀ c : R ⧸ Q, g (MvPolynomial.C c) = Polynomial.C (MvPolynomial.C c : MvPolynomial (Fin rs) (R ⧸ Q)) := by
    intro c
    simp [g, MvPolynomial.finSuccEquiv_apply]
  have hXe : e (algebraMap _ (Localization.AtPrime q) (Polynomial.X : (MvPolynomial (Fin rs) (R ⧸ Q))[X])) = Ideal.Quotient.mk _ (v 0) := by
    rw [← hgX0, he, hψX]
  have hCXe : ∀ j : Fin rs, e (algebraMap _ (Localization.AtPrime q) (Polynomial.C
      (MvPolynomial.X j : MvPolynomial (Fin rs) (R ⧸ Q)))) = Ideal.Quotient.mk _ (v j.succ) := by
    intro j
    rw [← hgXs, he, hψX]
  have hCCe : ∀ c : R, e (algebraMap _ (Localization.AtPrime q) (Polynomial.C
      (MvPolynomial.C (Ideal.Quotient.mk Q c) : MvPolynomial (Fin rs) (R ⧸ Q)))) = Ideal.Quotient.mk _ (T.toRing c) := by
    intro c
    rw [← hgC, he, hψC]
  -- the image of `A` in the fibre
  let Λ : MvPolynomial (Fin rs) (R ⧸ Q) →+* T.ring ⧸ Ideal.span {ξ} :=
    ((e : _ →+* _).comp (algebraMap _ (Localization.AtPrime q))).comp Polynomial.C
  let Good : T.ring → Prop := fun y => Ideal.Quotient.mk _ y ∈ Λ.range
  have good_add : ∀ {a b}, Good a → Good b → Good (a + b) := by
    intro a b ha hb
    show Ideal.Quotient.mk _ (a + b) ∈ Λ.range
    rw [map_add]; exact Subring.add_mem _ ha hb
  have good_mul : ∀ {a b}, Good a → Good b → Good (a * b) := by
    intro a b ha hb
    show Ideal.Quotient.mk _ (a * b) ∈ Λ.range
    rw [map_mul]; exact Subring.mul_mem _ ha hb
  have good_zero : Good 0 := by
    show Ideal.Quotient.mk _ 0 ∈ Λ.range
    rw [map_zero]; exact Subring.zero_mem _
  have good_one : Good 1 := by
    show Ideal.Quotient.mk _ 1 ∈ Λ.range
    rw [map_one]; exact Subring.one_mem _
  have good_T : ∀ c : R, Good (T.toRing c) := fun c =>
    ⟨MvPolynomial.C (Ideal.Quotient.mk Q c), hCCe c⟩
  have good_v : ∀ j : Fin rs, Good (v j.succ) := fun j => ⟨MvPolynomial.X j, hCXe j⟩
  have hbase : ∀ k : Fin (rs + 1), ∃ b', T.toRing (algebraMap F.S R (zS k)) = ξ * b' ∧
      Good b' := by
    intro k
    refine Fin.cases ?_ (fun j => ?_) k
    · exact ⟨1, by simp only [mul_one, hzS0', hξ], good_one⟩
    · refine ⟨v j.succ, ?_, good_v j⟩
      rw [← hZ2 j]
      exact hv j.succ
  have hdivPS : ∀ b ∈ Q.comap (algebraMap F.S R), ∃ b', T.toRing (algebraMap F.S R b) =
      ξ * b' ∧ Good b' := by
    intro b hb
    rw [← hzSspan] at hb
    induction hb using Submodule.span_induction with
    | mem x hx => obtain ⟨k, rfl⟩ := hx; exact hbase k
    | zero => exact ⟨0, by simp, good_zero⟩
    | add x y _ _ hx hy =>
      obtain ⟨b1, h1, g1⟩ := hx
      obtain ⟨b2, h2, g2⟩ := hy
      exact ⟨b1 + b2, by rw [map_add, map_add, h1, h2, mul_add], good_add g1 g2⟩
    | smul s x _ hx =>
      obtain ⟨b1, h1, g1⟩ := hx
      exact ⟨T.toRing (algebraMap F.S R s) * b1, by
        rw [smul_eq_mul, map_mul, map_mul, h1]; ring, good_mul (good_T _) g1⟩
  have hpow : ∀ n : ℕ, ∀ c ∈ (Q.comap (algebraMap F.S R)) ^ n,
      ∃ c', T.toRing (algebraMap F.S R c) = ξ ^ n * c' ∧ Good c' := by
    intro n
    induction n with
    | zero => intro c _; exact ⟨T.toRing (algebraMap F.S R c), by simp, good_T _⟩
    | succ n ih =>
      intro c hc
      rw [pow_succ] at hc
      refine Submodule.mul_induction_on hc ?_ (fun x y hx hy => ?_)
      · intro a ha b hb
        obtain ⟨a', h1, g1⟩ := ih a ha
        obtain ⟨b', h2, g2⟩ := hdivPS b hb
        exact ⟨a' * b', by rw [map_mul, map_mul, h1, h2, pow_succ]; ring, good_mul g1 g2⟩
      · obtain ⟨b1, h1, g1⟩ := hx
        obtain ⟨b2, h2, g2⟩ := hy
        exact ⟨b1 + b2, by rw [map_add, map_add, h1, h2, mul_add], good_add g1 g2⟩
  -- units
  have hunit : ∀ k : ℕ, k ≠ 0 → IsUnit (k : MvPolynomial (Fin rs) (R ⧸ Q)) := by
    intro k hk
    have h1 : IsUnit (k : F.S) := by
      rw [← IsLocalRing.residue_ne_zero_iff_isUnit, map_natCast]
      exact Nat.cast_ne_zero.mpr hk
    have h2 := h1.map ((Ideal.Quotient.mk Q).comp (algebraMap F.S R))
    rw [map_natCast] at h2
    have h3 := h2.map (MvPolynomial.C : (R ⧸ Q) →+* MvPolynomial (Fin rs) (R ⧸ Q))
    rwa [map_natCast] at h3
  -- the local structure
  have hnt : Nontrivial (T.ring ⧸ Ideal.span {ξ}) := by
    apply Ideal.Quotient.nontrivial_iff.mpr
    rw [Ne, Ideal.span_singleton_eq_top]
    have hxM : algebraMap F.S R x₀ ∈ maximalIdeal R :=
      IsLocalRing.le_maximalIdeal (Ideal.IsPrime.ne_top ‹_›) hx₀Q
    exact map_nonunit T.toRing _ hxM
  have : IsLocalHom (Ideal.Quotient.mk (Ideal.span {ξ})) :=
    IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective
  refine ⟨MvPolynomial (Fin rs) (R ⧸ Q), inferInstance, q, hqprime, e, hunit, ?_, ?_, ?_⟩
  · intro η hη
    have : η = v 0 := by
      apply mul_left_cancel₀ hξ0
      rw [hη, ← hv 0]
      simp only [Fin.succ_zero_eq_one, hZ1]
    rw [this]; exact hXe
  · intro n c hc c' hc'
    obtain ⟨c'', hc'', hg⟩ := hpow n c hc
    have : c' = c'' := mul_left_cancel₀ (pow_ne_zero n hξ0) (hc'.symm.trans hc'')
    rw [this]
    exact hg
  · intro y
    rw [IsLocalRing.mem_maximalIdeal, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
      mem_nonunits_iff]
    rw [isUnit_map_iff e.symm]
    constructor
    · intro hy hu
      exact hy (IsLocalHom.map_nonunit _ hu)
    · intro hy hu
      exact hy (hu.map _)

end FiberModel

section Main

variable {R : Type u} [CommRing R] [IsRegularLocalRing R]

/-- p. 318 (unrestricted case), ring level: with `Q R₁ = (w)`, `z = wζ`, `g_j = z^ν + ∑ g_{ji}
z^{ν-i-1}` with coefficients `g_{ji} ∈ (Q ∩ S)^{i+1}` in the coefficient ring `S` of a regular
frame with `r = 1`, `g_{j,0} = 0` in characteristic `0`, `h_j = g_j/w^ν ∈ M₁^ν`, and some
`x₀ ∈ Q ∩ S` with `T(x₀) = w ε` (`ε` a unit; the paper's `v_t`): `ζ ∈ M₁`.

This is the conclusion that the paper obtains by "applying Lemma 22" (p. 318), a citation which
is circular (Lemma 22 needs a regular frame `(T'; z_{t+1})`, i.e. already `z_{t+1}` a
non-unit).  The route here follows the proof of Lemma 22 (pp. 265--266): after dividing by
`w^ν` one has `h = ε^ν (η^ν + ∑ c'_i η^{ν-i-1})`, `η = ζ/ε`, `c'_i = g_{ji}/x₀^{i+1}`;
in the polynomial fibre `R₁/x₀R₁ ≅ A[X]_q` (`exists_fiber_polynomial_model`) the `c'_i` come
from `A` and `η = X`, and the first stage of the proof of Lemma 22 (`z = x - h`, `g'_1 = νh`,
uniqueness of the expansion; `g_{11} = 0` and characteristic `0`) is run on this fibre
(`X_mem_of_monic_mem_pow_localization`).  The fibre structure is `exists_fiber_polynomial_model`
(proved from the local structure of monoidal transforms, pp. 209--210).

Deviation from the paper (gap filled): the paper's citation of Lemma 22 presupposes the
conclusion (Definition 9 requires `z_{t+1}` to be a non-unit).  Hypotheses `hcoef` (`g_{ji} ∈
(Q ∩ S)^{i+1}`, `CD.frame_coeff_mem_pow`) and the existence of `x₀` (`CD.exists_mem_comap_assoc_w`,
the paper's "indirect argument") are taken as hypotheses. -/
@[blueprint "lem:IV.CD-4-maximal-contact"
  (statement := /-- Let $R$ be a regular local ring and $(S;z)$ a regular frame of $R$ with
    $r=1$, the residue field of $S$ of characteristic $0$. Let $g_j=z^\nu+\sum_{i<\nu}c_{ji}
    z^{\nu-1-i}$ with $c_{ji}\in(Q\cap S)^{i+1}$ and $c_{j0}=0$ for $j=1$, where $Q$ is a prime
    ideal of $R$ with $R/Q$ regular and $z\in Q$. Let $R_1=R[x^{-1}Q]_{M'}$ be a monoidal
    transform with centre $Q$, $QR_1=wR_1$, $x_0\in Q\cap S$ with $x_0=w\varepsilon$ in $R_1$,
    $\varepsilon$ a unit, and $h$ with $w^\nu h=g_1$, $h\in M_1^\nu$. If $z=w\zeta$ in $R_1$
    then $\zeta\in M_1$. -/)
  (proof := /-- Put $\eta=\zeta/\varepsilon$ and $c'_i=c_{1i}/x_0^{i+1}\in R_1$. Dividing by
    $w^\nu$, $h=\varepsilon^\nu(\eta^\nu+\sum_ic'_i\eta^{\nu-1-i})$ with $c'_0=0$. By
    \cref{lem:IV.CD-4-fiber-model}, the fibre $R_1/x_0R_1$ is $A[X]_q$ with $\eta=X$ and
    $c'_i\in A$; the image of $h$ lies in the $\nu$-th power of the maximal ideal. By
    \cref{lem:IV.CD-4-derivative-core} (characteristic $0$, no term $X^{\nu-1}$), $X\in q$,
    i.e.\ $\eta\in M_1$ and $\zeta=\varepsilon\eta\in M_1$.

    \textbf{Deviation from the paper (gap filled).} The paper concludes ``we apply Lemma 22,
    \S10, Ch.~III'' (p.~318), but Lemma 22 is a statement about a regular frame $(T';z_{t+1})$
    and Definition~9 requires $z_{t+1}$ to be part of a regular system of parameters, hence a
    non-unit, which is the conclusion sought. The proof above follows that of Lemma 22
    (pp.~265--266: $z=x-h$, $g'_1=\nu h$, uniqueness of the expansion) on the fibre
    $R_1/x_0R_1$. -/)
  (latexEnv := "lemma")]
theorem RegularFrame.zeta_mem_maximalIdeal_of_maximal_contact [IsDomain R] (F : RegularFrame R)
    (z : R) (hzF : ∀ j, F.z j = z) (hr : F.r = 1) (ν : ℕ) (hν : 0 < ν) (m : ℕ) (g : Fin m → R)
    (co : Fin m → Fin ν → F.S)
    (hshape : ∀ j, g j = z ^ ν + ∑ i : Fin ν,
      algebraMap F.S R (co j i) * z ^ (ν - ((i : ℕ) + 1)))
    [CharZero (ResidueField F.S)] (hm : 0 < m) (h0 : co ⟨0, hm⟩ ⟨0, hν⟩ = 0)
    (Q : Ideal R) [Q.IsPrime] [IsRegularLocalRing (R ⧸ Q)]
    (hcoef : ∀ (j : Fin m) (i : Fin ν), co j i ∈ (Q.comap (algebraMap F.S R)) ^ ((i : ℕ) + 1))
    (hzQ : z ∈ Q) (T : MonoidalTransform R Q) [IsLocalHom T.toRing] [IsRegularLocalRing T.ring]
    (w : T.ring) (hw : Ideal.span {w} = Q.map T.toRing) (x₀ : F.S)
    (hx₀Q : algebraMap F.S R x₀ ∈ Q) (ε : T.ringˣ)
    (hε : T.toRing (algebraMap F.S R x₀) = w * ε)
    (h : Fin m → T.ring) (hh : ∀ j, h j ∈ maximalIdeal T.ring ^ ν)
    (hwh : ∀ j, w ^ ν * h j = T.toRing (g j)) :
    ∀ ζ : T.ring, T.toRing z = w * ζ → ζ ∈ maximalIdeal T.ring := by
  classical
  intro ζ hζ
  obtain ⟨n, rfl⟩ : ∃ n, ν = n + 1 := ⟨ν - 1, by omega⟩
  have hdomT := isDomain_of_isRegularLocalRing T.ring
  have hzne : z ≠ 0 := by
    have hmem : z ∈ Finset.image F.z Finset.univ :=
      Finset.mem_image.mpr ⟨⟨0, by rw [hr]; exact Nat.one_pos⟩, Finset.mem_univ _, hzF _⟩
    exact F.extends_rsop.ne_zero hmem
  have hw0 : w ≠ 0 := by
    intro h0'
    have hz0 : T.toRing z = 0 := by rw [hζ, h0', zero_mul]
    exact hzne (T.toRing_injective (by rw [hz0, map_zero]))
  set ξ : T.ring := T.toRing (algebraMap F.S R x₀) with hξ
  have hξ0 : ξ ≠ 0 := by rw [hε]; exact mul_ne_zero hw0 ε.ne_zero
  have hξspan : Ideal.span {ξ} = Q.map T.toRing := by
    rw [hε, ← hw, Ideal.span_singleton_mul_right_unit ε.isUnit]
  obtain ⟨A, _, q, _, e, hunit, hX, hcA, hloc⟩ :=
    exists_fiber_polynomial_model F z hzF hr Q hzQ T x₀ hx₀Q hξspan
  let f : T.ring →+* Localization.AtPrime q :=
    (e.symm : _ →+* _).comp (Ideal.Quotient.mk (Ideal.span {ξ}))
  have hfloc : ∀ y : T.ring, f y ∈ maximalIdeal (Localization.AtPrime q) ↔
      y ∈ maximalIdeal T.ring := fun y => (hloc y).symm
  set η : T.ring := ((ε⁻¹ : T.ringˣ) : T.ring) * ζ with hη
  have hξη : ξ * η = T.toRing z := by
    rw [hζ, hε, hη]
    calc w * ↑ε * (↑ε⁻¹ * ζ) = w * (↑ε * ↑ε⁻¹) * ζ := by ring
      _ = w * ζ := by rw [Units.mul_inv, mul_one]
  have hfη : f η = algebraMap A[X] (Localization.AtPrime q) X := by
    show e.symm (Ideal.Quotient.mk _ η) = _
    rw [← hX η hξη, e.symm_apply_apply]
  -- the coefficients: `T(c_i) = ξ^{i+1} c'_i`
  let j0 : Fin m := ⟨0, hm⟩
  have hle : (Q.comap (algebraMap F.S R)).map (T.toRing.comp (algebraMap F.S R)) ≤
      Ideal.span {ξ} := by
    rw [Ideal.map_le_iff_le_comap]
    intro p hp
    rw [Ideal.mem_comap, hξspan]
    exact Ideal.mem_map_of_mem _ (Ideal.mem_comap.mp hp)
  have hex : ∀ i : Fin (n + 1), ∃ c' : T.ring,
      T.toRing (algebraMap F.S R (co j0 i)) = ξ ^ ((i : ℕ) + 1) * c' := by
    intro i
    have h1 := Ideal.mem_map_of_mem (T.toRing.comp (algebraMap F.S R)) (hcoef j0 i)
    rw [Ideal.map_pow] at h1
    have h2 := Ideal.pow_right_mono hle ((i : ℕ) + 1) h1
    rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton'] at h2
    obtain ⟨c', hc'⟩ := h2
    exact ⟨c', by
      have h3 : T.toRing (algebraMap F.S R (co j0 i)) = c' * ξ ^ ((i : ℕ) + 1) := hc'.symm
      rw [h3, mul_comm]⟩
  choose c' hc' using hex
  have hAex : ∀ i : Fin (n + 1), ∃ a : A, e (algebraMap A[X] (Localization.AtPrime q) (C a)) =
      Ideal.Quotient.mk _ (c' i) := fun i => hcA _ _ (hcoef j0 i) _ (hc' i)
  choose a ha using hAex
  have hfc : ∀ i, f (c' i) = algebraMap A[X] (Localization.AtPrime q) (C (a i)) := by
    intro i
    show e.symm (Ideal.Quotient.mk _ (c' i)) = _
    rw [← ha i, e.symm_apply_apply]
  -- `h = ε^ν (η^ν + ∑ c'_i η^{ν-i-1})`
  have hTg : T.toRing (g j0) = ξ ^ (n + 1) * (η ^ (n + 1) + ∑ i : Fin (n + 1),
      c' i * η ^ ((n + 1) - ((i : ℕ) + 1))) := by
    rw [hshape j0, map_add, map_pow, map_sum, ← hξη, mul_pow, mul_add, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, map_pow, ← hξη, hc' i, mul_pow]
    have hi : (i : ℕ) + 1 ≤ n + 1 := i.2
    have : ξ ^ (n + 1) = ξ ^ ((i : ℕ) + 1) * ξ ^ ((n + 1) - ((i : ℕ) + 1)) := by
      rw [← pow_add]; congr 1; omega
    rw [this]
    ring
  have hhη : h j0 = (ε : T.ring) ^ (n + 1) * (η ^ (n + 1) + ∑ i : Fin (n + 1),
      c' i * η ^ ((n + 1) - ((i : ℕ) + 1))) := by
    apply mul_left_cancel₀ (pow_ne_zero (n + 1) hw0)
    rw [hwh j0, hTg, hε, mul_pow]
    ring
  -- transport to the fibre
  have hfh : f (h j0) = f (ε : T.ring) ^ (n + 1) * algebraMap A[X] (Localization.AtPrime q)
      (X ^ (n + 1) + ∑ i : Fin (n + 1), C (a i) * X ^ ((n + 1) - ((i : ℕ) + 1))) := by
    rw [hhη, map_mul, map_pow, map_add, map_pow, map_sum, hfη]
    simp only [map_mul, map_pow, hfc, hfη, map_add, map_sum]
  have hfhm : f (h j0) ∈ maximalIdeal (Localization.AtPrime q) ^ (n + 1) := by
    have h1 : Ideal.map f (maximalIdeal T.ring ^ (n + 1)) ≤
        maximalIdeal (Localization.AtPrime q) ^ (n + 1) := by
      rw [Ideal.map_pow]
      refine Ideal.pow_right_mono ?_ _
      rw [Ideal.map_le_iff_le_comap]
      intro y hy
      exact (hfloc y).mpr hy
    exact h1 (Ideal.mem_map_of_mem f (hh j0))
  have hG : algebraMap A[X] (Localization.AtPrime q)
      (X ^ (n + 1) + ∑ i : Fin (n + 1), C (a i) * X ^ ((n + 1) - ((i : ℕ) + 1))) ∈
      maximalIdeal (Localization.AtPrime q) ^ (n + 1) := by
    obtain ⟨v, hv⟩ := ((ε.isUnit.map f).pow (n + 1)).exists_left_inv
    have : algebraMap A[X] (Localization.AtPrime q)
        (X ^ (n + 1) + ∑ i : Fin (n + 1), C (a i) * X ^ ((n + 1) - ((i : ℕ) + 1))) =
        v * f (h j0) := by
      rw [hfh, ← mul_assoc, hv, one_mul]
    rw [this]
    exact Ideal.mul_mem_left _ _ hfhm
  -- `a 0` vanishes
  have hc0 : c' 0 = 0 := by
    have h1 := hc' 0
    have h2 : co j0 0 = 0 := by simpa using h0
    rw [h2, map_zero, map_zero] at h1
    rcases mul_eq_zero.mp h1.symm with h3 | h3
    · exact absurd (pow_eq_zero_iff (by norm_num) |>.mp h3) hξ0
    · exact h3
  have ha0 : C (a 0) ∈ q := by
    have h1 : algebraMap A[X] (Localization.AtPrime q) (C (a 0)) = 0 := by
      apply e.injective
      rw [ha 0, hc0, map_zero, map_zero]
    exact (IsLocalization.AtPrime.to_map_mem_maximal_iff (Localization.AtPrime q) q _).mp
      (by rw [h1]; exact zero_mem _)
  have hfact : IsUnit (((n + 1).factorial : ℕ) : A) := by
    have : ∀ k : ℕ, IsUnit ((k.factorial : ℕ) : A) := by
      intro k
      induction k with
      | zero => simp
      | succ k ih =>
        rw [Nat.factorial_succ, Nat.cast_mul]
        exact (hunit (k + 1) (by omega)).mul ih
    exact this _
  have hXq := X_mem_of_monic_mem_pow_localization n hfact a q ha0 hG
  have hηm : η ∈ maximalIdeal T.ring := by
    rw [← hfloc, hfη]
    exact (IsLocalization.AtPrime.to_map_mem_maximal_iff (Localization.AtPrime q) q _).mpr hXq
  have : ζ = (ε : T.ring) * η := by
    rw [hη, ← mul_assoc, Units.mul_inv, one_mul]
  rw [this]
  exact Ideal.mul_mem_left _ _ hηm

end Main

end Hironaka
