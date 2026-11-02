/-
Copyright (c) 2026 Daattavya Aggarwal, Minhyong Kim, Oisin Kim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daattavya Aggarwal, Minhyong Kim, Oisin Kim
-/
module

public import Mathlib.Algebra.Order.Star.Basic
public import Mathlib.AlgebraicGeometry.IdealSheaf.Basic
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.Data.Fin.Tuple.Sort
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.AdicCompletion.LocalRing
public import Mathlib.RingTheory.Coalgebra.IsFrobenius
public import Mathlib.RingTheory.Etale.Weakly
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.HopfAlgebra.Basic
public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
public import Mathlib.RingTheory.Nullstellensatz
public import Mathlib.RingTheory.RegularLocalRing.Polynomial
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.TotallySplit
public import Architect
public import Hironaka.Ch3.Basic
public import Hironaka.Compat.RegularQuotient
public import Hironaka.Ch2.GradedIdeal
public import Hironaka.Ch0.NormalFlatness
public import Hironaka.Ch3.Transforms
public import Hironaka.Ch3.NuStar
public import Hironaka.Compat.CurveResolution
public import Hironaka.Compat.AdicCompletionRegular
public import Hironaka.Compat.RegularLocalization

/-!
# Ch. III §3: The upper semi-continuity of ν(J) of local ideals J (pp. 217–221)

> Let R be a regular local ring, M the maximal ideal of R, P a prime ideal in R, and J a
> non-zero ideal in R. Then ν_P(J) is the maximal integer ν (≥ 0) such that P^ν contains J.
> We write ν(J) for ν_M(J). It is clear that ν_P(J) ≤ ν(J) and ν_P(J) ≤ ν(JR_P). If R/P is
> regular, then we have P^ν = P^ν R_P ∩ R for all non-negative integer ν. Therefore we have
> ν_P(J) = ν(JR_P).  (p. 217)

Contents, in the paper's order: the opening facts of p. 217 (`order_facts`), Lemma 7, Lemma 8,
Theorem 1 (Zariski–Nagata), Lemma 9, Theorem 2 and its two corollaries, and the Remark with the
example of pp. 220–221.

Conventions.  `ν_P(J)` is `Ideal.ord P J` and `ν(J)` is `Ideal.nu J`
(`Hironaka/Compat/RegularLocalRing.lean`); `ν_P(f)` for an element is `Ideal.ordElem P f`, the
initial form is `initialForm`, and `gr_P(J, R)` is `grIdeal P J` (`Hironaka/Compat/Graded.lean`);
`R_P` is `Localization.AtPrime P` and `JR_P` is `J.map (algebraMap R (Localization.AtPrime P))`;
`ν*(J)` and standard bases are `nuStar` and `IsStandardBase` (`Hironaka/Ch3/Basic.lean`);
"`gr_P̄(O)` is flat over `O/P̄`" for `O = R/J` is `IsNormallyFlatAlongIdeal (P.map (Ideal.Quotient.mk J))`
(Definition 1 of Ch. 0, as in Ch. II).  Monoidal transforms and weak transforms are those of
`Hironaka/Ch3/Basic.lean` (p. 209 and Definition 5, p. 213).

Two facts about regular local rings are used tacitly.  That a regular local ring is a domain is
proved in `Hironaka/Compat/RegularQuotient.lean` (`isDomain_of_isRegularLocalRing`); statements
that form `MonoidalTransform R P` still take `[IsDomain R]` as an instance hypothesis, as
everywhere in Ch. III.  That the localization `R_P` of a regular local ring at a prime is regular
(Serre; cited by the paper in footnote 9, p. 243) is not in Mathlib; it is the cited leaf
`isRegularLocalRing_localization_of_isRegularLocalRing` (`Hironaka/Compat/RegularLocalization.lean`),
used in the proof of Theorem 1, while statements that speak of a standard base of `JR_P` keep it
as an instance hypothesis `[IsRegularLocalRing (Localization.AtPrime P)]`, flagged in the
docstring.
-/

@[expose] public section

open IsLocalRing AlgebraicGeometry

namespace Hironaka

universe u

/-! ### The opening facts (p. 217) -/

section OrderFacts

variable (R : Type u) [CommRing R] [IsRegularLocalRing R] (J P : Ideal R) [P.IsPrime]

/-- p. 217: "Let `R` be a regular local ring, `M` the maximal ideal of `R`, `P` a prime ideal in
`R`, and `J` a non-zero ideal in `R`. Then `ν_P(J)` is the maximal integer `ν (≥ 0)` such that
`Pᵛ` contains `J`. We write `ν(J)` for `ν_M(J)`. It is clear that `ν_P(J) ≤ ν(J)` and
`ν_P(J) ≤ ν(JR_P)`. If `R/P` is regular, then we have `Pᵛ = PᵛR_P ∩ R` for all non-negative
integer `ν`. Therefore we have `ν_P(J) = ν(JR_P)`."

`ν_P(J)` is `Ideal.ord P J` (p. 165); `ν(JR_P)` is the order of `JR_P` with respect to the
maximal ideal `PR_P` of `R_P`; "`PᵛR_P ∩ R`" is the contraction `comap` of the extension
`(Pᵛ).map` to `R_P`.  The statements under "`R/P` regular" rest on the fact that `Pᵛ` is then
`P`-primary (`mem_pow_of_mul_mem_pow_of_isRegularLocalRing_quotient`,
`Hironaka/Compat/RegularQuotient.lean`).  The paper's hypothesis `J ≠ 0` is kept but not
needed.

Deviation from the paper (gap filled): the paper asserts `Pᵛ = PᵛR_P ∩ R` (for `R/P` regular)
without argument; it is proved here from the `P`-primarity of `Pᵛ`, which rests on
`gr_P(R)` being a polynomial ring over the domain `R/P`. -/
@[blueprint "lem:III.3-order-facts"
  (statement := /-- Let $R$ be a regular local ring, $M$ the maximal ideal of $R$, $P$ a prime
    ideal in $R$, and $J$ a non-zero ideal in $R$. Then $\nu_P(J)$ is the maximal integer
    $\nu\ (\ge0)$ such that $P^\nu$ contains $J$ (\cref{def:order-nu}); we write $\nu(J)$ for
    $\nu_M(J)$. It is clear that $\nu_P(J)\le\nu(J)$ and $\nu_P(J)\le\nu(JR_P)$. If $R/P$ is
    regular, then $P^\nu=P^\nu R_P\cap R$ for all non-negative integers $\nu$; therefore
    $\nu_P(J)=\nu(JR_P)$. (p.~217.) -/)
  (proof := /-- [The paper gives no argument (``It is clear that'', ``we have''); the following
    is supplied by the formalization.] Since $P\subseteq M$, $J\subseteq P^\nu$ implies
    $J\subseteq M^\nu$, whence $\nu_P(J)\le\nu(J)$; and $J\subseteq P^\nu$ implies
    $JR_P\subseteq P^\nu R_P=(PR_P)^\nu$, whence $\nu_P(J)\le\nu(JR_P)$. If $R/P$ is
    regular, $P$ is generated by part of a regular system of parameters of $R$
    (\cref{lem:regular-quotient-rsop}) and $\operatorname{gr}_P(R)$ is a polynomial ring over
    the domain $R/P$ (Ch.~II, footnote 41), so that every $P^\nu$ is $P$-primary
    (\cref{lem:regular-quotient-primary-powers}) and $P^\nu R_P\cap R=P^\nu$; hence
    $J\subseteq P^\nu$ if and only if $JR_P\subseteq(PR_P)^\nu$, i.e.\
    $\nu_P(J)=\nu(JR_P)$.

    \textbf{Gap in the paper filled.} The equality $P^\nu=P^\nu R_P\cap R$ for $R/P$ regular
    is asserted in the paper without argument; the formalization proves it through the
    $P$-primarity of the powers $P^\nu$. -/)
  (latexEnv := "lemma")]
theorem order_facts (_hJ : J ≠ ⊥) :
    Ideal.ord P J ≤ Ideal.nu J ∧
    Ideal.ord P J ≤ Ideal.nu (J.map (algebraMap R (Localization.AtPrime P))) ∧
    (IsRegularLocalRing (R ⧸ P) →
      (∀ ν : ℕ, ((P ^ ν).map (algebraMap R (Localization.AtPrime P))).comap
          (algebraMap R (Localization.AtPrime P)) = P ^ ν) ∧
      Ideal.ord P J = Ideal.nu (J.map (algebraMap R (Localization.AtPrime P)))) := by
  refine ⟨?_, ?_, fun hreg => ?_⟩
  · -- `J ⊆ Pᵛ ⊆ Mᵛ`.
    exact Ideal.ord_le fun ν hν =>
      Ideal.le_ord (hν.trans (Ideal.pow_right_mono (le_maximalIdeal_of_isPrime P) ν))
  · -- `J ⊆ Pᵛ` gives `JR_P ⊆ PᵛR_P = (PR_P)ᵛ`, and `PR_P` is the maximal ideal of `R_P`.
    exact Ideal.ord_le fun ν hν => Ideal.le_ord (by
      rw [← Localization.AtPrime.map_eq_maximalIdeal, ← Ideal.map_pow]
      exact Ideal.map_mono hν)
  · -- `R/P` regular: every `Pᵛ` is `P`-primary, so `PᵛR_P ∩ R = Pᵛ`
    have hsymb : ∀ ν : ℕ, ((P ^ ν).map (algebraMap R (Localization.AtPrime P))).comap
        (algebraMap R (Localization.AtPrime P)) = P ^ ν := by
      intro ν
      refine le_antisymm (fun b hb => ?_) Ideal.le_comap_map
      rw [Ideal.mem_comap, IsLocalization.mem_map_algebraMap_iff P.primeCompl] at hb
      obtain ⟨⟨a, s⟩, hs⟩ := hb
      rw [← map_mul, IsLocalization.eq_iff_exists P.primeCompl] at hs
      obtain ⟨c, hc⟩ := hs
      refine mem_pow_of_mul_mem_pow_of_isRegularLocalRing_quotient P hreg ν ((c : R) * s) b
        (P.primeCompl.mul_mem c.2 s.2) ?_
      have : (c : R) * s * b = c * a := by rw [← hc]; ring
      rw [this]
      exact Ideal.mul_mem_left _ _ a.2
    refine ⟨hsymb, le_antisymm ?_ ?_⟩
    · exact Ideal.ord_le fun ν hν => Ideal.le_ord (by
        rw [← Localization.AtPrime.map_eq_maximalIdeal, ← Ideal.map_pow]
        exact Ideal.map_mono hν)
    · -- `JR_P ⊆ (PR_P)ᵛ = PᵛR_P` gives `J ⊆ PᵛR_P ∩ R = Pᵛ`
      exact Ideal.ord_le fun ν hν => Ideal.le_ord (by
        rw [← hsymb ν, ← Ideal.map_le_iff_le_comap, Ideal.map_pow,
          Localization.AtPrime.map_eq_maximalIdeal]
        exact hν)

end OrderFacts

/-! ### Lemma 7 (p. 217) -/

/-- Lemma 7, p. 217: "Let `R`, `J` and `P` be as above. If `R/P` is regular, then we have
`ν(JR_P) ≤ ν(J)`." -/
@[blueprint "lem:III.7"
  (statement := /-- Let $R$, $J$ and $P$ be as in \cref{lem:III.3-order-facts} ($R$ a regular
    local ring, $P$ a prime ideal, $J$ a non-zero ideal). If $R/P$ is regular, then
    $\nu(JR_P)\le\nu(J)$. (Lemma 7, p.~217.) -/)
  (proof := /-- $\nu(JR_P)=\nu_P(J)\le\nu(J)$ by \cref{lem:III.3-order-facts}. -/)
  (latexEnv := "lemma")]
theorem nu_localization_le_of_quotient_regular (R : Type u) [CommRing R] [IsRegularLocalRing R]
    (J P : Ideal R) [P.IsPrime] (hJ : J ≠ ⊥) [IsRegularLocalRing (R ⧸ P)] :
    Ideal.nu (J.map (algebraMap R (Localization.AtPrime P))) ≤ Ideal.nu J := by
  obtain ⟨h₁, -, h₃⟩ := order_facts R J P hJ
  rw [← (h₃ inferInstance).2]
  exact h₁

/-! ### Lemma 8 (pp. 217–218) -/

open MvPolynomial in
/-- Substituting polynomials of degree `≤ 1` for the variables does not increase the degree. -/
private theorem totalDegree_eval₂_le_of_le_one {A B : Type*} [CommRing A] [CommRing B] {σ τ : Type*}
    (f : A →+* MvPolynomial τ B) (hf : ∀ c, (f c).totalDegree = 0) (g : σ → MvPolynomial τ B)
    (hg : ∀ i, (g i).totalDegree ≤ 1) (p : MvPolynomial σ A) :
    (eval₂ f g p).totalDegree ≤ p.totalDegree := by
  rw [eval₂_eq]
  refine totalDegree_finsetSum_le fun m hm => ?_
  refine (totalDegree_mul _ _).trans ?_
  rw [hf, zero_add]
  refine (totalDegree_finsetProd _ _).trans ?_
  refine le_trans ?_ (le_totalDegree hm)
  refine (Finset.sum_le_sum fun i _ => (totalDegree_pow (g i) (m i)).trans
    (Nat.mul_le_mul_left _ (hg i))).trans ?_
  simp [Finsupp.sum]

open MvPolynomial in
/-- The translation argument of p. 218: for a ring homomorphism `π : k[T₁, …, T_r] → L` (`k` a
field), a non-zero polynomial of degree `≤ ν` does not lie in `(ker π)^(ν+1)`: after the
substitution `Tᵢ ↦ Tᵢ + π(Tᵢ)` over `L`, `ker π` goes into the ideal of the variables. -/
private theorem not_mem_ker_pow_of_totalDegree_le {k L : Type*} [Field k] [CommRing L]
    [Nontrivial L] {r : ℕ}
    (π : MvPolynomial (Fin r) k →+* L) {H : MvPolynomial (Fin r) k} (hH : H ≠ 0) {ν : ℕ}
    (hdeg : H.totalDegree ≤ ν) : H ∉ RingHom.ker π ^ (ν + 1) := by
  intro hmem
  let a : Fin r → L := fun i => π (X i)
  let σ : MvPolynomial (Fin r) L →ₐ[L] MvPolynomial (Fin r) L := aeval fun i => X i + C (a i)
  let σ' : MvPolynomial (Fin r) L →ₐ[L] MvPolynomial (Fin r) L := aeval fun i => X i - C (a i)
  have hσ : Function.Injective σ := by
    have : σ'.comp σ = AlgHom.id L _ := by
      apply MvPolynomial.algHom_ext
      intro i
      simp [σ, σ']
    exact Function.LeftInverse.injective (g := σ') fun p => by
      simpa using DFunLike.congr_fun this p
  let τ : MvPolynomial (Fin r) k →+* MvPolynomial (Fin r) L :=
    eval₂Hom (C.comp (π.comp C)) fun i => X i + C (a i)
  have hτσ : τ = (σ : MvPolynomial (Fin r) L →+* MvPolynomial (Fin r) L).comp
      (map (π.comp C)) := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [τ, σ]
    · intro i
      simp [τ, σ]
  have hτ : Function.Injective τ := by
    rw [hτσ]
    exact hσ.comp (MvPolynomial.map_injective _ (π.comp C).injective)
  -- `τ(ker π)` lies in the ideal of the variables
  have hc : (constantCoeff : MvPolynomial (Fin r) L →+* L).comp τ = π := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [τ]
    · intro i
      simp [τ, a]
  have h1 : (RingHom.ker π).map τ ≤ idealOfVars (Fin r) L ^ 1 := by
    rw [Ideal.map_le_iff_le_comap]
    intro F hF
    rw [Ideal.mem_comap, mem_pow_idealOfVars_iff']
    intro x hx
    have hx0 : x = 0 := by
      rw [Nat.lt_one_iff] at hx
      exact (Finsupp.degree_eq_zero_iff x).mp hx
    subst hx0
    rw [← constantCoeff_eq, ← RingHom.comp_apply, hc]
    exact hF
  have h2 : τ H ∈ idealOfVars (Fin r) L ^ (ν + 1) := by
    have := Ideal.mem_map_of_mem τ hmem
    rw [Ideal.map_pow] at this
    have h3 := Ideal.pow_right_mono h1 (ν + 1)
    rw [← pow_mul, one_mul] at h3
    exact h3 this
  -- but `τ H ≠ 0` has degree `≤ ν`
  have hτH : τ H ≠ 0 := fun h => hH (hτ (h.trans (map_zero τ).symm))
  have hdeg' : (τ H).totalDegree ≤ ν := by
    refine le_trans ?_ hdeg
    have hg : ∀ i, (X i + C (a i) : MvPolynomial (Fin r) L).totalDegree ≤ 1 := fun i =>
      (totalDegree_add _ _).trans (max_le (totalDegree_X i).le (by rw [totalDegree_C]; omega))
    exact totalDegree_eval₂_le_of_le_one (C.comp (π.comp C)) (fun c => totalDegree_C _)
      (fun i => X i + C (a i)) hg H
  obtain ⟨m, hm⟩ := MvPolynomial.ne_zero_iff.mp hτH
  have hmdeg : m.degree ≤ ν := (le_totalDegree (mem_support_iff.mpr hm)).trans hdeg'
  exact hm ((mem_pow_idealOfVars_iff' (ν + 1) _).mp h2 m (by omega))

open MvPolynomial in
/-- Dehomogenization with respect to the first variable keeps the coefficients of a form. -/
private theorem coeff_aeval_cons_one_X {B : Type*} [CommRing B] {r ν : ℕ}
    {F : MvPolynomial (Fin (r + 1)) B}
    (hF : F.IsHomogeneous ν) (n : Fin (r + 1) →₀ ℕ) (hn : F.coeff n ≠ 0) :
    (aeval (Fin.cons (1 : MvPolynomial (Fin r) B) X : Fin (r + 1) → MvPolynomial (Fin r) B)
      F).coeff (Finsupp.tail n) = F.coeff n := by
  have hev : ∀ G : MvPolynomial (Fin (r + 1)) B,
      aeval (Fin.cons (1 : MvPolynomial (Fin r) B) X : Fin (r + 1) → MvPolynomial (Fin r) B) G =
        Polynomial.eval 1 (finSuccEquiv B r G) := by
    intro G
    induction G using MvPolynomial.induction_on with
    | C c => simp [finSuccEquiv_apply]
    | add p q hp hq => rw [map_add, map_add, Polynomial.eval_add, hp, hq]
    | mul_X p i hp =>
      rw [map_mul, map_mul, Polynomial.eval_mul, hp, aeval_X]
      refine Fin.cases ?_ (fun j => ?_) i
      · simp [finSuccEquiv_X_zero]
      · simp [finSuccEquiv_X_succ]
  have hdeg : ∀ (j : ℕ) (m : Fin r →₀ ℕ), (Finsupp.cons j m).degree = j + m.degree := by
    intro j m
    rw [Finsupp.degree_eq_sum, Finsupp.degree_eq_sum, Fin.sum_univ_succ]
    simp
  have hdegF : ∀ d, F.coeff d ≠ 0 → d.degree = ν := fun d hd =>
    ((hF.degree_eq_sum_deg_support (mem_support_iff.mpr hd)).trans rfl).symm
  rw [hev, Polynomial.eval_eq_sum, Polynomial.sum_def, coeff_sum]
  simp only [one_pow, mul_one]
  rw [Finset.sum_eq_single (n 0)]
  · rw [finSuccEquiv_coeff_coeff, Finsupp.cons_tail]
  · intro j _ hj
    rw [finSuccEquiv_coeff_coeff]
    by_contra hc
    have h1 := hdegF _ hc
    have h2 := hdegF _ hn
    rw [hdeg] at h1
    rw [← Finsupp.cons_tail n, hdeg] at h2
    exact hj (by omega)
  · intro h
    rw [Polynomial.notMem_support_iff.mp h]
    simp

open MvPolynomial in
/-- `totalDegree` does not increase under a change of coefficients. -/
private theorem totalDegree_map_le {A B σ : Type*} [CommSemiring A] [CommSemiring B]
    (f : A →+* B) (p : MvPolynomial σ A) : (map f p).totalDegree ≤ p.totalDegree :=
  Finset.sup_mono (support_map_subset f p)

open MvPolynomial in
/-- p. 218, "(This is easily shown if `k` is algebraically closed, …)": for an algebraically closed
field `k`, a non-zero polynomial of degree `≤ ν` does not lie in the `(ν+1)`-th power of a maximal
ideal `N` of `k[Z₁, …, Z_r]`.  By the Nullstellensatz `N = (Z₁ - a₁, …, Z_r - a_r)`, the kernel of
the evaluation at a point `a`; after the translation `Zᵢ ↦ Zᵢ + aᵢ` the ideal `N` goes into the
ideal `(Z₁, …, Z_r)`, whose `(ν+1)`-th power consists of polynomials without terms of degree `≤ ν`
(`not_mem_ker_pow_of_totalDegree_le`). -/
private theorem not_mem_pow_of_totalDegree_le_of_isAlgClosed {k : Type*} [Field k] [IsAlgClosed k]
    {r : ℕ} (N : Ideal (MvPolynomial (Fin r) k)) [hN : N.IsMaximal] {H : MvPolynomial (Fin r) k}
    (hH : H ≠ 0) {ν : ℕ} (hdeg : H.totalDegree ≤ ν) : H ∉ N ^ (ν + 1) := by
  obtain ⟨a, ha⟩ :=
    (MvPolynomial.isMaximal_iff_eq_vanishingIdeal_singleton (K := k) (σ := Fin r)).mp hN
  have hker : N = RingHom.ker (aeval a : MvPolynomial (Fin r) k →ₐ[k] k).toRingHom := by
    ext p
    rw [ha, RingHom.mem_ker, MvPolynomial.mem_vanishingIdeal_singleton_iff]
    rfl
  rw [hker]
  exact not_mem_ker_pow_of_totalDegree_le _ hH hdeg

open MvPolynomial in
/-- p. 218, "… and the assertion for an arbitrary `k` follows immediately": a non-zero polynomial of
degree `≤ ν` over any field `k` does not lie in the `(ν+1)`-th power of a maximal ideal `N` of
`k[Z₁, …, Z_r]`.  Extend the scalars to an algebraic closure `K` of `k`: `H` goes to a non-zero
polynomial of degree `≤ ν` of `K[Z]`, and `N·K[Z]` is contained in a maximal ideal `m` of `K[Z]`
(the ideal of a point `a ∈ K^r`, which exists since `k[Z]/N` is a finite extension of `k`), so
`H ∈ N^(ν+1)` would give `H ∈ m^(ν+1)`, contradicting the algebraically closed case. -/
private theorem not_mem_pow_of_totalDegree_le {k : Type*} [Field k] {r : ℕ}
    (N : Ideal (MvPolynomial (Fin r) k)) [hN : N.IsMaximal] {H : MvPolynomial (Fin r) k}
    (hH : H ≠ 0) {ν : ℕ} (hdeg : H.totalDegree ≤ ν) : H ∉ N ^ (ν + 1) := by
  intro hmem
  let K := AlgebraicClosure k
  obtain ⟨a, ha⟩ := MvPolynomial.eq_vanishingIdeal_singleton_of_isMaximal (σ := Fin r) K hN
  let m : Ideal (MvPolynomial (Fin r) K) := vanishingIdeal K {a}
  have hm : m.IsMaximal :=
    MvPolynomial.isMaximal_iff_eq_vanishingIdeal_singleton.mpr ⟨a, rfl⟩
  have hle : N.map (map (algebraMap k K)) ≤ m := by
    rw [Ideal.map_le_iff_le_comap]
    intro p hp
    rw [Ideal.mem_comap, MvPolynomial.mem_vanishingIdeal_singleton_iff, aeval_map_algebraMap]
    rw [ha] at hp
    exact (MvPolynomial.mem_vanishingIdeal_singleton_iff a p).mp hp
  have hmem' : map (algebraMap k K) H ∈ m ^ (ν + 1) := by
    have := Ideal.mem_map_of_mem (map (algebraMap k K)) hmem
    rw [Ideal.map_pow] at this
    exact Ideal.pow_right_mono hle _ this
  exact not_mem_pow_of_totalDegree_le_of_isAlgClosed m
    (fun h => hH ((map_injective _ (algebraMap k K).injective) (h.trans (map_zero _).symm)))
    ((totalDegree_map_le _ H).trans hdeg) hmem'

open MvPolynomial in
/-- p. 217: "We have seen in §2 that `A'/MA'` is isomorphic to a polynomial ring `k[Z₁, …, Z_r]` of
`r`-variables corresponding to the `zᵢ/x` (`1 ≤ i ≤ r`) over the field `k = R/M`."  In §2 (p. 210):
"`S[X₂, …, X_r]/M̄S[X₂, …, X_r]` can be identified with the polynomial ring `k[X₂, …, X_r]` …" and
"We can identify `A'/(x₁, y₁, …, y_s)A'` with `k[X₂, …, X_r]` as above", `(x₁, y₁, …, y_s)` being a
regular system of parameters of `R`, so that the ideal is `MA'`.  The isomorphism is given as a
surjective ring homomorphism `π : A' → k[Z₁, …, Z_r]` with kernel `MA'`, which extends the residue
map `R → k` and sends `zᵢ/x` to `Zᵢ`.

Obtained from the chart `χ : A' → (R/P)[Z]` of `MonoidalTransform.exists_chart` (the identification
`A'/(x)A' ≅ S[X₂, …, X_r]`) by reducing the coefficients from `S = R/P` to `k = S/M̄`
(`chartResidue`); `(x) ⊆ M`, so the kernel is `MA'`. -/
@[blueprint "lem:III.8-chart-residue"
  (statement := /-- Let $R$ be a regular local ring with maximal ideal $M$ and residue field $k$,
    $P$ a prime ideal of $R$ with $R/P$ regular, $(x,z_1,\dots,z_r)$ a minimal base of $P$ with
    $x$ the element defining the monoidal transform, which is part of a minimal base of $M$, and
    $A'=R[z_1/x,\dots,z_r/x]$. Then $A'/MA'$ is isomorphic to a polynomial ring
    $k[Z_1,\dots,Z_r]$ of $r$ variables corresponding to the $z_i/x$ over the field $k=R/M$.
    (pp.~210 and~217.) (Formalization note (encoding): the isomorphism is a surjective ring
    homomorphism $\pi\colon A'\to k[Z_1,\dots,Z_r]$ with kernel $MA'$ which extends the residue
    map $R\to k$ and sends $z_i/x$ to $Z_i$.) -/)
  (proof := /-- By \cref{lem:III.2-chart} there is a chart $\chi\colon A'\to S[Z_1,\dots,Z_r]$,
    $S=R/P$, which is onto with kernel $(x)A'$. Reducing the coefficients modulo the maximal
    ideal of $S$ gives a surjection $\pi\colon A'\to k[Z_1,\dots,Z_r]$. Its kernel is
    contained in $MA'$ (an element of $A'$ whose image modulo $x$ has coefficients in $\bar M$
    is a sum of elements of $M$ times elements of $A'$, plus a multiple of $x\in M$), and
    contains $MA'$ since $\pi$ extends $R\to k$. \textbf{Gap in the paper filled.} The paper
    identifies $A'/(x_1,y_1,\dots,y_s)A'$ with $k[X_2,\dots,X_r]$ (p.~210) without further
    argument. -/)
  (latexEnv := "lemma")]
theorem MonoidalTransform.exists_chart_mod_maximalIdeal {R : Type u} [CommRing R]
    [IsRegularLocalRing R] [IsDomain R] {P : Ideal R} (t : MonoidalTransform R P) [P.IsPrime]
    {S : Finset R} {r : ℕ} {z : Fin (r + 1) → R}
    (hSM : Ideal.span (S : Set R) = maximalIdeal R)
    (hScard : S.card = (maximalIdeal R).spanFinrank) (hinj : Function.Injective z)
    (hzS : ∀ i, z i ∈ S) (hz0 : z 0 = t.x) (hzP : Ideal.span (Set.range z) = P) :
    ∃ π : blowupAlgebra R P t.x →+* MvPolynomial (Fin r) (ResidueField R),
      Function.Surjective π ∧
      RingHom.ker π = (maximalIdeal R).map (algebraMap R (blowupAlgebra R P t.x)) ∧
      (∀ c : R, π (algebraMap R (blowupAlgebra R P t.x) c) = C (residue R c)) ∧
      ∀ (i : Fin r) (a : blowupAlgebra R P t.x),
        (a : FractionRing R) = algebraMap R (FractionRing R) (z i.succ) /
          algebraMap R (FractionRing R) t.x → π a = X i := by
  obtain ⟨χ, hχ, hχx, hχC, hχX⟩ := t.exists_chart hSM hScard hinj hzS hz0 hzP
  have hPM : P ≤ maximalIdeal R := IsLocalRing.le_maximalIdeal (Ideal.IsPrime.ne_top ‹_›)
  refine ⟨chartResidue hPM χ, chartResidue_surjective hPM hχ, le_antisymm ?_ ?_, ?_, ?_⟩
  · refine ker_chartResidue_le hPM _ hχ hχC ?_
    rw [hχx, Ideal.span_le, Set.singleton_subset_iff]
    exact Ideal.mem_map_of_mem _ (hPM t.x_mem)
  · rw [Ideal.map_le_iff_le_comap]
    intro c hc
    rw [Ideal.mem_comap, RingHom.mem_ker]
    simp [chartResidue, hχC, residueQuotientHom_mk, (IsLocalRing.residue_eq_zero_iff c).mpr hc]
  · intro c
    simp [chartResidue, hχC, residueQuotientHom_mk]
  · intro i a ha
    simp [chartResidue, hχX i a ha]

open MvPolynomial in
/-- The proof of Lemma 8 (p. 217–218), following the printed proof in `A' = R[z₁/x, …, z_r/x]`;
see `nu_weakTransform_le`. -/
private theorem nu_weakTransform_le_of_isDomain (R : Type u) [CommRing R] [IsRegularLocalRing R]
    [IsDomain R] (J : Ideal R) (hJ : J ≠ ⊥) (P : Ideal R) [P.IsPrime]
    [IsRegularLocalRing (R ⧸ P)] (hP : Ideal.ord P J = Ideal.nu J) (t : MonoidalTransform R P)
    (halg : RingHom.IsResiduallyAlgebraic (R := R) (R' := t.ring) t.toRing) :
    Ideal.nu (S := t.ring) (weakTransformIdeal t J) ≤ Ideal.nu J := by
  classical
  -- "Let us take an element `f` of `J` such that `ν_M(f) = ν(J)`."
  have hfin : Ideal.nu J ≠ ⊤ := by
    obtain ⟨g, hgJ, hg0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hJ
    intro htop
    exact hg0 ((Ideal.ordElem_eq_top_iff_eq_zero (maximalIdeal.isMaximal R).ne_top).mp
      (Ideal.ordElem_eq_top_iff.mpr fun n => Ideal.le_pow_of_le_ord
        (le_of_le_of_eq le_top (show Ideal.ord (maximalIdeal R) J = ⊤ from htop).symm) hgJ))
  obtain ⟨ν, hν⟩ := ENat.ne_top_iff_exists.mp hfin
  change (ν : ℕ∞) = Ideal.ord (maximalIdeal R) J at hν
  have hJP : J ≤ P ^ ν := Ideal.le_pow_of_le_ord (le_of_eq (hν.trans hP.symm))
  have hnot : ¬ J ≤ maximalIdeal R ^ (ν + 1) := fun h => by
    have := Ideal.le_ord h
    rw [← hν] at this
    norm_cast at this
    omega
  obtain ⟨f, hfJ, hfM⟩ := Set.not_subset.mp hnot
  -- "Then we have `ν_M(f) = ν_P(f)`": `f ∈ P^ν` since `J ⊆ P^ν`.
  -- "Let `x` be the element with `PR' = (x)R'`": the defining element `t.x` of `R'`.
  -- "`N` the maximal ideal in `A'` such that `R' = A'_N`": `N = M'` is maximal since `R'` is
  -- residually algebraic over `R`, i.e. `dim R' = dim R` ("Then we see that `dim R = dim R'` iff the
  -- residue field of `R'` is algebraic over that of `R`"), iff `M'` is a maximal ideal in `A'`
  -- ("It follows that `dim R' = dim R` iff `M'` is a maximal ideal in `A'`", p. 210).
  have hSreg : IsRegularLocalRing (R ⧸ P) := inferInstance
  have hP0 : P ≠ ⊥ := fun h => t.x_ne_zero (Ideal.mem_bot.mp (h ▸ t.x_mem))
  have hNmax : t.M'.IsMaximal :=
    (t.isMaximal_iff_isResiduallyAlgebraic_of_isRegular inferInstance hP0 hSreg).mpr halg
  -- "We have a minimal base of `P` including the element `x`, say `(x, z₁, …, z_r)`."
  obtain ⟨S, r, z, hSM, hScard, hinj, hzS, hz0, hzP⟩ := t.exists_minimal_generators hSreg
  -- "We have seen in §2 that `A'/MA'` is isomorphic to a polynomial ring `k[Z₁, …, Z_r]`."
  obtain ⟨π, hπsurj, hπker, hπC, hπX⟩ :=
    t.exists_chart_mod_maximalIdeal hSM hScard hinj hzS hz0 hzP
  -- "We can write the element `f` in the form `∑ a_(i) x^{i₀} z₁^{i₁} ⋯ z_r^{i_r}` where
  -- `i₀ + i₁ + ⋯ + i_r = ν` and `a_(i) ∈ R`.  Then some of the `a_(i)` must be units in `R`
  -- because `ν_M(f) = ν`."
  have hfP : f ∈ Ideal.span (Set.range z) ^ ν := by rw [hzP]; exact hJP hfJ
  obtain ⟨F, hFhom, hFf⟩ := (Ideal.mem_span_pow_iff_exists_isHomogeneous z f).mp hfP
  have hunit : ∃ n, F.coeff n ∉ maximalIdeal R := by
    by_contra h
    push Not at h
    apply hfM
    have := eval_mem_mul_span_pow_of_coeff_mem (y := z) hFhom h
    rw [hFf, hzP] at this
    rw [pow_succ']
    exact Ideal.mul_mono_right (Ideal.pow_right_mono (le_maximalIdeal_of_isPrime P) ν) this
  obtain ⟨n, hn⟩ := hunit
  -- "Then `x^{-ν} f` can be written in the form `∑ a_(i) (z₁/x)^{i₁} ⋯ (z_r/x)^{i_r}`", an
  -- element `vA` of `A' = R[z₁/x, …, z_r/x]`.
  let g : Fin r → FractionRing R := fun i => algebraMap R (FractionRing R) (z i.succ) /
    algebraMap R (FractionRing R) t.x
  have hgA : ∀ i, g i ∈ blowupAlgebra R P t.x := fun i =>
    Algebra.subset_adjoin ⟨z i.succ, hzP ▸ Ideal.subset_span ⟨i.succ, rfl⟩, rfl⟩
  let w : Fin (r + 1) → blowupAlgebra R P t.x := Fin.cons 1 fun i => ⟨g i, hgA i⟩
  have hw : ∀ j, algebraMap R (blowupAlgebra R P t.x) (z j) =
      w j * algebraMap R (blowupAlgebra R P t.x) t.x := by
    intro j
    refine Fin.cases ?_ (fun i => ?_) j
    · simp [w, hz0]
    · have hxK : algebraMap R (FractionRing R) t.x ≠ 0 :=
        (map_ne_zero_iff _ (IsFractionRing.injective R (FractionRing R))).mpr t.x_ne_zero
      apply Subtype.ext
      simp only [MulMemClass.coe_mul, Subalgebra.coe_algebraMap, w, Fin.cons_succ, g]
      field_simp
  let vA : blowupAlgebra R P t.x := eval₂ (algebraMap R (blowupAlgebra R P t.x)) w F
  have hvA : algebraMap R (blowupAlgebra R P t.x) t.x ^ ν * vA =
      algebraMap R (blowupAlgebra R P t.x) f := by
    have h1 := MvPolynomial.IsHomogeneous.aeval_mul_const (K := blowupAlgebra R P t.x) hFhom w
      (algebraMap R (blowupAlgebra R P t.x) t.x)
    have h2 : algebraMap R (blowupAlgebra R P t.x) f =
        eval₂ (algebraMap R (blowupAlgebra R P t.x)) (algebraMap R (blowupAlgebra R P t.x) ∘ z) F := by
      rw [← hFf]
      exact eval₂_comp_left (algebraMap R (blowupAlgebra R P t.x)) (RingHom.id R) z F
    rw [h2, show (algebraMap R (blowupAlgebra R P t.x) ∘ z) =
      fun j => w j * algebraMap R (blowupAlgebra R P t.x) t.x from funext hw]
    exact h1.symm
  -- "Then `x^{-ν} f ∈ J'` where `ν = ν_P(f) = ν_M(f)`": the image `v` of `vA` in `R' = A'_N`.
  let v : t.ring := algebraMap (blowupAlgebra R P t.x) t.ring vA
  have hv : t.toRing t.x ^ ν * v = t.toRing f := by
    have := congrArg (algebraMap (blowupAlgebra R P t.x) t.ring) hvA
    rw [map_mul, map_pow] at this
    exact this
  have hvJ' : v ∈ weakTransformIdeal t J :=
    Ideal.subset_span ⟨t.xR, t.span_xR_eq_map, f, hfJ, ν, le_of_eq (hν.trans hP.symm), hv⟩
  -- "Therefore it suffices to show that `ν_{M'}(x^{-ν} f) ≤ ν`."
  suffices hsuff : Ideal.ordElem (maximalIdeal t.ring) v ≤ ν by
    change Ideal.ord (maximalIdeal t.ring) (weakTransformIdeal t J) ≤ Ideal.ord (maximalIdeal R) J
    refine le_trans (Ideal.ord_le fun m hm => ?_) (hsuff.trans (le_of_eq hν))
    exact Ideal.le_ordElem (hm hvJ')
  -- "Let `F` be the class of `x^{-ν} f` in `k[Z₁, …, Z_r]`, which is of the form
  -- `∑ ā_(i) Z₁^{i₁} ⋯ Z_r^{i_r}`, where `ā_(i)` is the residue class of `a_(i)` in `k`."
  let ρ : R →+* ResidueField R := residue R
  let gk : Fin (r + 1) → MvPolynomial (Fin r) (ResidueField R) := Fin.cons 1 X
  let Fb : MvPolynomial (Fin r) (ResidueField R) := aeval gk (map ρ F)
  have hπvA : π vA = Fb := by
    have h1 : π.comp (algebraMap R (blowupAlgebra R P t.x)) =
        (C : ResidueField R →+* MvPolynomial (Fin r) (ResidueField R)).comp ρ :=
      RingHom.ext fun c => hπC c
    have h2 : π ∘ w = gk := by
      funext j
      refine Fin.cases ?_ (fun i => ?_) j
      · simp [w, gk]
      · simp only [Function.comp_apply, w, gk, Fin.cons_succ]
        exact hπX i _ rfl
    show π (eval₂ (algebraMap R (blowupAlgebra R P t.x)) w F) = aeval gk (map ρ F)
    rw [eval₂_comp_left, h1, h2, aeval_def, eval₂_map, MvPolynomial.algebraMap_eq]
  -- "Since some of the `a_(i)` are units in `R`, hence in `R'`, some of the `ā_(i)` are not zero.
  -- In view of the above expression of `F`, we see that `F` is a non-zero polynomial in the
  -- `Z_j`'s of degree at most `ν`."
  have hρn : (map ρ F).coeff n ≠ 0 := by
    rw [coeff_map]
    exact fun h0 => hn ((IsLocalRing.residue_eq_zero_iff _).mp h0)
  have hFb0 : Fb ≠ 0 := by
    intro h0
    apply hρn
    rw [← coeff_aeval_cons_one_X (hFhom.map ρ) n hρn]
    change Fb.coeff (Finsupp.tail n) = 0
    rw [h0]
    simp
  have hdeg : Fb.totalDegree ≤ ν := by
    refine le_trans ?_ (hFhom.map ρ).totalDegree_le
    have hg : ∀ j, (gk j).totalDegree ≤ 1 := by
      intro j
      refine Fin.cases ?_ (fun i => ?_) j
      · simp [gk]
      · simp only [gk, Fin.cons_succ]
        exact (totalDegree_monomial_le _ _).trans (by simp)
    exact totalDegree_eval₂_le_of_le_one (algebraMap (ResidueField R)
      (MvPolynomial (Fin r) (ResidueField R))) (fun c => totalDegree_C c) gk hg (map ρ F)
  -- "If `ν' = ν_{M'}(x^{-ν} f)", we have to exclude `ν' ≥ ν + 1`, i.e. `x^{-ν} f ∈ M'^(ν+1)`.
  apply Ideal.ordElem_le_of_notMem
  intro hvM
  -- "then `x^{-ν} f ∈ N^{ν'}`": `R' = A'_N` with `N` maximal, so `N^(ν+1)` is `N`-primary and
  -- `M'^(ν+1) ∩ A' = N^(ν+1)`.
  have hvN : vA ∈ t.M' ^ (ν + 1) := by
    have h1 : v ∈ Ideal.map (algebraMap (blowupAlgebra R P t.x) t.ring) (t.M' ^ (ν + 1)) := by
      rw [Ideal.map_pow, IsLocalization.AtPrime.map_eq_maximalIdeal t.M' t.ring]
      exact hvM
    have hrad : (t.M' ^ (ν + 1)).radical = t.M' := by
      apply le_antisymm
      · intro a ha
        obtain ⟨m, hm⟩ := ha
        exact hNmax.isPrime.mem_of_pow_mem m (Ideal.pow_le_self (by omega : ν + 1 ≠ 0) hm)
      · intro a ha
        exact ⟨ν + 1, Ideal.pow_mem_pow ha _⟩
    have hprim : (t.M' ^ (ν + 1)).IsPrimary :=
      Ideal.isPrimary_of_isMaximal_radical (by rw [hrad]; exact hNmax)
    have hdisj : Disjoint (t.M'.primeCompl : Set (blowupAlgebra R P t.x))
        (t.M' ^ (ν + 1) : Ideal _) := Set.disjoint_left.mpr fun a ha ha' =>
      ha (Ideal.pow_le_self (by omega : ν + 1 ≠ 0) ha')
    have := IsLocalization.under_map_of_isPrimary_disjoint t.M'.primeCompl t.ring hprim hdisj
    rw [← this]
    exact h1
  -- "and hence `F ∈ N̄^{ν'}`", `N̄ = N/MA'` a maximal ideal of `k[Z₁, …, Z_r]`.
  have hker : RingHom.ker π ≤ t.M' := by rw [hπker]; exact t.le
  have hNbar : (t.M'.map π).IsMaximal :=
    Ideal.IsMaximal.map_of_surjective_of_ker_le hπsurj hker
  have hFbN : Fb ∈ (t.M'.map π) ^ (ν + 1) := by
    rw [← hπvA, ← Ideal.map_pow]
    exact Ideal.mem_map_of_mem π hvN
  -- "Hence `F` is not contained in the `(ν+1)`-th power of any maximal ideal in `k[Z₁, …, Z_r]`."
  exact not_mem_pow_of_totalDegree_le (t.M'.map π) hFb0 hdeg hFbN

/-- Lemma 8, p. 217: "Let `R` be a regular local ring, `J` a non-zero ideal in `R`, and `P` a
prime ideal in `R`. Assume that `R/P` is regular and that `ν_P(J) = ν(J)`. Let `R'` be a monoidal
transform of `R` with center `P` which is residually algebraic over `R`. If `J'` is the weak
transform of `J` in `R'` then we have `ν(J') ≤ ν(J)`."

Formalization note (encoding): `R'` is `t.ring` for `t : MonoidalTransform R P` (p. 209), with its canonical
homomorphism `t.toRing : R → R'`, and `J'` is `weakTransformIdeal t J` (Definition 5, p. 213).

Deviation from the paper (statement modified): two redundant hypotheses.  (1)
`MonoidalTransform R P` requires `[IsDomain R]` (regular local rings are domains,
`isDomain_of_isRegularLocalRing`, but there is no such instance, so it is a hypothesis).  (2)
"residually algebraic" (`RingHom.IsResiduallyAlgebraic`) presupposes that `t.toRing` is a local
homomorphism, which always holds (the instance `MonoidalTransform.isLocalHom_toRing` of
`Hironaka/Ch3/Transforms.lean`); `[IsLocalHom t.toRing]` is nevertheless taken as an instance
hypothesis (redundant).

The proof follows the printed proof (pp. 217–218) step by step, in `A' = R[z₁/x, …, z_r/x]`
(`blowupAlgebra R P x`) and `A'/MA' ≅ k[Z₁, …, Z_r]`
(`MonoidalTransform.exists_chart_mod_maximalIdeal`), `k = R/M`.  The element `x` is the defining
element `t.x` of `R'`, `N` is `t.M'`, and `x⁻ᵛ f` is the element `vA` of `A'` (and its image `v` in
`R' = A'_N`).  Gaps in the paper filled: that `N` is maximal in `A'` (`R'` residually algebraic,
p. 210); that `x⁻ᵛ f ∈ M'^{ν'}` gives `x⁻ᵛ f ∈ N^{ν'}` (`N^{ν'}` is `N`-primary, so `M'^{ν'}R' ∩ A' =
N^{ν'}`); and the parenthetical "(This is easily shown if `k` is algebraically closed, and the
assertion for an arbitrary `k` follows immediately.)", proved as printed: first for algebraically
closed `k` (`not_mem_pow_of_totalDegree_le_of_isAlgClosed`, Nullstellensatz and translation), then
for arbitrary `k` by extension of scalars to an algebraic closure
(`not_mem_pow_of_totalDegree_le`). -/
@[blueprint "lem:III.8"
  (statement := /-- Let $R$ be a regular local ring, $J$ a non-zero ideal in $R$, and $P$ a
    prime ideal in $R$. Assume that $R/P$ is regular and that $\nu_P(J)=\nu(J)$. Let $R'$ be a
    monoidal transform of $R$ with center $P$ (\cref{def:III.2-monoidal-transform}) which is
    residually algebraic over $R$ (\cref{def:III.2-residually}). If $J'$ is the weak transform
    of $J$ in $R'$ (\cref{def:III.5-weak}) then we have $\nu(J')\le\nu(J)$.
    (Lemma 8, p.~217.)

    \textbf{Deviation from the paper (statement modified).} The formal statement also assumes
    that $R$ is a domain and that $R\to R'$ is a local homomorphism; both hold automatically
    (regular local rings are domains, and $R\to R'$ is local), so these hypotheses are
    redundant. -/)
  (proof := /-- Let $M$ (resp.\ $M'$) denote the maximal ideal of $R$ (resp.\ $R'$). Let us
    take an element $f$ of $J$ such that $\nu_M(f)=\nu(J)$. Then we have $\nu_M(f)=\nu_P(f)$.
    Let us choose $x\in P$ such that $PR'=(x)R'$. Then $x^{-\nu}f\in J'$ where
    $\nu=\nu_P(f)=\nu_M(f)$. Therefore it suffices to show that $\nu_{M'}(x^{-\nu}f)\le\nu$. We
    have a minimal base of $P$ including the element $x$, say $(x,z_1,\dots,z_r)$ where
    $r+1=\dim R_P$. We can write the element $f$ in the form
    $\sum a_{(i)}x^{i_0}z_1^{i_1}z_2^{i_2}\cdots z_r^{i_r}$ where the summation is for all
    distinct systems $(i_0,i_1,\dots,i_r)$ such that $i_0+i_1+\dots+i_r=\nu$, and
    $a_{(i)}\in R$. Then some of the $a_{(i)}$ must be units in $R$ because $\nu_M(f)=\nu$.
    Then $x^{-\nu}f$ can be written in the form
    $\sum a_{(i)}(z_1/x)^{i_1}(z_2/x)^{i_2}\cdots(z_r/x)^{i_r}$. Let
    $A'=R[z_1/x,\dots,z_r/x]$ and $N$ the maximal ideal in $A'$ such that $R'=A'_N$. Then $N$
    contains $MA'$. We have seen in \S2 that $A'/MA'$ is isomorphic to a polynomial ring
    $k[Z_1,\dots,Z_r]$ of $r$-variables corresponding to the $z_i/x$ ($1\le i\le r$) over the
    field $k=R/M$. Let $F$ be the class of $x^{-\nu}f$ in $k[Z_1,\dots,Z_r]$, which is of the
    form $\sum\bar a_{(i)}Z_1^{i_1}Z_2^{i_2}\cdots Z_r^{i_r}$, where $\bar a_{(i)}$ is the
    residue class of $a_{(i)}$ in $k$. Let $\bar N=N/MA'$, which is a maximal ideal in
    $k[Z_1,\dots,Z_r]$. If $\nu'=\nu_{M'}(x^{-\nu}f)$, then $x^{-\nu}f\in N^{\nu'}$ and hence
    $F\in\bar N^{\nu'}$. Since some of the $a_{(i)}$ are units in $R$, hence in $R'$, some of
    the $\bar a_{(i)}$ are not zero. In view of the above expression of $F$, we see that $F$
    is a non-zero polynomial in the $Z_j$'s of degree at most $\nu$. Hence $F$ is not
    contained in the $(\nu+1)$-th power of any maximal ideal in $k[Z_1,\dots,Z_r]$. (This is
    easily shown if $k$ is algebraically closed, and the assertion for an arbitrary $k$
    follows immediately.) Thus we have $\nu_{M'}(x^{-\nu}f)=\nu'\le\nu$.

    \textbf{Formal proof.} The formal proof follows this proof step by step. The element $x$ is
    the defining element of $R'$, $A'$ is $R[x^{-1}P]$ and $N$ is the prime $M'$ of $A'$
    (maximal because $R'$ is residually algebraic, \cref{def:III.2-residually}, by the two printed
    facts of p.~210 \cref{lem:III.2-dim} and \cref{lem:III.2-dim-maximal}); $x^{-\nu}f$ is
    the element $F(1,z_1/x,\dots,z_r/x)$ of $A'$, and $A'/MA'\cong k[Z_1,\dots,Z_r]$ is the
    surjection of \cref{lem:III.8-chart-residue}. One shows $x^{-\nu}f\notin M'^{\nu+1}$, which
    is $\nu_{M'}(x^{-\nu}f)\le\nu$.

    \textbf{Gaps in the paper filled.} (1) That $N$ is maximal in $A'$ is deduced from the
    residual algebraicity of $R'$ as on p.~210: $R'$ is residually algebraic iff $\dim R'=\dim R$
    iff $M'$ is a maximal ideal in $A'$. (2) ``Then $x^{-\nu}f\in N^{\nu'}$'': since $N$ is
    maximal, $N^{n}$ is $N$-primary, so $M'^{n}R'\cap A'=N^{n}$. (3) The parenthetical claim
    is proved as printed. If $k$ is algebraically closed, a maximal ideal of $k[Z_1,\dots,Z_r]$
    is $(Z_1-a_1,\dots,Z_r-a_r)$ (Nullstellensatz); the translation $Z_i\mapsto Z_i+a_i$ maps
    it into $(Z_1,\dots,Z_r)$, so a non-zero polynomial of degree $\le\nu$ is not in its
    $(\nu+1)$-th power. For an arbitrary $k$, extend the scalars to an algebraic closure
    $K$: the image of $F$ is a non-zero polynomial of degree $\le\nu$, and $\bar NK[Z]$ lies
    in a maximal ideal of $K[Z]$. -/)
  (latexEnv := "lemma")]
theorem nu_weakTransform_le (R : Type u) [CommRing R] [IsRegularLocalRing R] [IsDomain R]
    (J : Ideal R) (hJ : J ≠ ⊥) (P : Ideal R) [P.IsPrime] [IsRegularLocalRing (R ⧸ P)]
    (hP : Ideal.ord P J = Ideal.nu J) (t : MonoidalTransform R P)
    (halg : RingHom.IsResiduallyAlgebraic (R := R) (R' := t.ring) t.toRing) :
    Ideal.nu (S := t.ring) (weakTransformIdeal t J) ≤ Ideal.nu J := by
  exact nu_weakTransform_le_of_isDomain R J hJ P hP t halg

/-! ### Theorem 1, Zariski–Nagata (p. 218) -/

/-- `ν` does not decrease along a local homomorphism of local rings. -/
private theorem nu_le_nu_map {A B : Type*} [CommRing A] [CommRing B] [IsLocalRing A]
    [IsLocalRing B] (φ : A →+* B) [IsLocalHom φ] (I : Ideal A) :
    Ideal.nu I ≤ Ideal.nu (I.map φ) :=
  Ideal.ord_le fun ν hν => Ideal.le_ord <| by
    calc I.map φ ≤ ((maximalIdeal A) ^ ν).map φ := Ideal.map_mono hν
      _ = ((maximalIdeal A).map φ) ^ ν := Ideal.map_pow _ _ _
      _ ≤ (maximalIdeal B) ^ ν :=
        Ideal.pow_right_mono (((IsLocalRing.local_hom_TFAE φ).out 1 3).mp ‹IsLocalHom φ›) ν

/-- `ν` is invariant under ring isomorphisms of local rings. -/
private theorem nu_map_ringEquiv {A B : Type*} [CommRing A] [CommRing B]
    [IsLocalRing A] [IsLocalRing B] (e : A ≃+* B) (I : Ideal A) :
    Ideal.nu (I.map (e : A →+* B)) = Ideal.nu I := by
  have h1 : IsLocalHom (e : A →+* B) := IsLocalHom.of_surjective _ e.surjective
  have h2 : IsLocalHom (e.symm : B →+* A) := IsLocalHom.of_surjective _ e.symm.surjective
  refine le_antisymm ?_ (nu_le_nu_map (e : A →+* B) I)
  have := nu_le_nu_map (e.symm : B →+* A) (I.map (e : A →+* B))
  rwa [Ideal.map_of_equiv] at this

/-- `ν` is invariant under bijective ring homomorphisms of local rings. -/
private theorem nu_map_of_bijective {A B : Type*} [CommRing A] [CommRing B]
    [IsLocalRing A] [IsLocalRing B] (φ : A →+* B) (hφ : Function.Bijective φ) (I : Ideal A) :
    Ideal.nu (I.map φ) = Ideal.nu I :=
  nu_map_ringEquiv (RingEquiv.ofBijective φ hφ) I

/-- The residue field `R/M` of a local ring is a regular local ring (a field). -/
private theorem isRegularLocalRing_residue (R : Type u) [CommRing R] [IsLocalRing R] :
    IsRegularLocalRing (R ⧸ maximalIdeal R) := by
  let := Ideal.Quotient.field (maximalIdeal R)
  infer_instance

/-- Theorem 1 for `P = M`: Lemma 7, `R/M` being a field. -/
private theorem nu_localization_maximalIdeal_le (R : Type u) [CommRing R]
    [IsRegularLocalRing R] (J : Ideal R) (hJ : J ≠ ⊥) :
    Ideal.nu (J.map (algebraMap R (Localization.AtPrime (maximalIdeal R)))) ≤ Ideal.nu J := by
  have := isRegularLocalRing_residue R
  exact nu_localization_le_of_quotient_regular R J (maximalIdeal R) hJ

/-- Proof of Theorem 1, p. 218, given the sequence (i)–(iii) of monoidal transforms: "Let `J_i`
be the ideals in `R_i` (`0 ≤ i ≤ s`) such that `J = J_0`, and that `J_i` is the weak transform
of `J_{i-1}` in `R_i` (`1 ≤ i ≤ s`). Then by Lemma 8, we have `ν(J) ≥ ν(J_1) ≥ ⋯ ≥ ν(J_s)`;
and, by Lemma 7, we have `ν(J_s) ≥ ν(J_s(R_s)_{P_s}) = ν(JR_P)`."

By induction on the sequence of monoidal transforms (`CurveResolvable`, (i)–(iii) of p. 218).

Gap filled: the paper's equality `ν(J_s(R_s)_{P_s}) = ν(JR_P)` is not explained.  It is proved one
transform at a time: under `R_P = R'_{P'}` one has `JR'_{P'} = J'R'_{P'}`: `⊇` because every
generator `x^{-ν}f` of `J'` has `x` a unit in `R'_{P'}` (`x ∈ P'` would give `M ⊆ P' ∩ R = P`,
i.e. `P = M`, which is Lemma 7), and `⊆` because `JR' ⊆ J'`. -/
private theorem nu_localization_le_of_curveResolvable {R : Type u} [CommRing R]
    [IsRegularLocalRing R] [IsDomain R] {P : Ideal R} (h : CurveResolvable R P) :
    ∀ [P.IsPrime] (J : Ideal R), J ≠ ⊥ →
      Ideal.nu (J.map (algebraMap R (Localization.AtPrime P))) ≤ Ideal.nu J := by
  induction h with
  | regular P hreg =>
    intro _ J hJ
    have := hreg
    exact nu_localization_le_of_quotient_regular _ J P hJ
  | @step R _ _ _ P _ t halg P' _ hP' hloc hreg _ ih =>
    intro _ J hJ
    by_cases hPM : P = maximalIdeal R
    · subst hPM
      exact nu_localization_maximalIdeal_le R J hJ
    have := isRegularLocalRing_residue R
    -- Lemma 8 with center `M`: `ν(J') ≤ ν(J)` for the weak transform `J'`.
    set J' := weakTransformIdeal t J with hJ'
    have h8 : Ideal.nu J' ≤ Ideal.nu J :=
      nu_weakTransform_le R J hJ (maximalIdeal R) rfl t halg
    -- `J' ⊇ JR' ≠ 0`
    have hJR' : J.map t.toRing ≤ J' := by
      rw [Ideal.map_le_iff_le_comap]
      intro f hf
      exact Ideal.subset_span
        ⟨t.xR, t.span_xR_eq_map, f, hf, 0, zero_le, by rw [pow_zero, one_mul]⟩
    have hJ'0 : J' ≠ ⊥ := by
      obtain ⟨f, hf, hf0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hJ
      intro h0
      have : t.toRing f ∈ J' := hJR' (Ideal.mem_map_of_mem _ hf)
      rw [h0, Ideal.mem_bot] at this
      exact hf0 (MonoidalTransform.toRing_injective t (this.trans (map_zero _).symm))
    have hih := ih J' hJ'0
    -- `R_P ≅ R'_{P'}`, and `J'R'_{P'} = JR'_{P'}` since `x` is a unit in `R'_{P'}`
    let φ := Localization.localRingHom P P' t.toRing hP'
    have hφ : (J.map (algebraMap R (Localization.AtPrime P))).map φ =
        J.map ((algebraMap t.ring (Localization.AtPrime P')).comp t.toRing) := by
      rw [Ideal.map_map]
      congr 1
      exact RingHom.ext fun a => Localization.localRingHom_to_map P P' t.toRing hP' a
    have hle : J'.map (algebraMap t.ring (Localization.AtPrime P')) ≤
        J.map ((algebraMap t.ring (Localization.AtPrime P')).comp t.toRing) := by
      rw [Ideal.map_le_iff_le_comap, hJ', weakTransformIdeal, Ideal.span_le]
      rintro y ⟨x, hx, f, hf, ν, -, hxy⟩
      have hxP' : x ∉ P' := by
        intro hxP
        apply hPM
        refine le_antisymm (le_maximalIdeal (Ideal.IsPrime.ne_top ‹_›)) ?_
        rw [hP', ← Ideal.map_le_iff_le_comap, ← hx, Ideal.span_le, Set.singleton_subset_iff]
        exact hxP
      have hu : IsUnit (algebraMap t.ring (Localization.AtPrime P') x ^ ν) :=
        (IsLocalization.map_units (Localization.AtPrime P') (⟨x, hxP'⟩ : P'.primeCompl)).pow ν
      rw [SetLike.mem_coe, Ideal.mem_comap, ← Ideal.unit_mul_mem_iff_mem _ hu, ← map_pow,
        ← map_mul, hxy]
      exact Ideal.mem_map_of_mem _ hf
    -- the other inclusion, from `JR' ⊆ J'`: so `JR'_{P'} = J'R'_{P'}`
    have hge : J.map ((algebraMap t.ring (Localization.AtPrime P')).comp t.toRing) ≤
        J'.map (algebraMap t.ring (Localization.AtPrime P')) := by
      rw [← Ideal.map_map]
      exact Ideal.map_mono hJR'
    calc Ideal.nu (J.map (algebraMap R (Localization.AtPrime P)))
        = Ideal.nu ((J.map (algebraMap R (Localization.AtPrime P))).map φ) :=
          (nu_map_of_bijective φ hloc _).symm
      _ = Ideal.nu (J.map ((algebraMap t.ring (Localization.AtPrime P')).comp t.toRing)) := by
          rw [hφ]
      _ = Ideal.nu (J'.map (algebraMap t.ring (Localization.AtPrime P'))) := by
          rw [le_antisymm hge hle]
      _ ≤ Ideal.nu J' := hih
      _ ≤ Ideal.nu J := h8

/-- Proof of Theorem 1, p. 218, the reduction to the complete case: "let `R̂` be the completion of
`R`, `P̂` any minimal prime ideal associated with `PR̂`, and `Ĵ = JR̂`. Then we have a canonical
local homomorphism `R_P → R̂_{P̂}`. Hence `ν(JR_P) ≤ ν(ĴR̂_{P̂})`, while `ν(J) = ν(Ĵ)` as is easily
seen. Therefore, it suffices to show `ν(Ĵ) ≥ ν(ĴR̂_{P̂})`."

Stated in the case, produced by the paper's chain of primes, that the maximal ideal `M` is a
minimal prime of `P + aR` for some `a` (so that `dim(R/P) ≤ 1`).

As printed: `P̂` is a minimal prime of `PR̂` (chosen below a prime of `R̂` over `P`, which exists as
`R̂` is faithfully flat over `R`; then `P̂ ∩ R = P`, so that there is the canonical local
homomorphism `R_P → R̂_{P̂}`), and `ν(Ĵ) = ν(J)` (`M̂ᵛ = MᵛR̂` and `MᵛR̂ ∩ R = Mᵛ` give `≤`, and
`≥` holds for any local homomorphism).  The completion is a complete regular local ring
(`Hironaka/Compat/AdicCompletionRegular.lean`).

Gap filled: the paper continues "Thus we shall assume that `R` is complete and `dim(R/P) = 1`",
i.e. it asserts `dim(R̂/P̂) = 1` without argument.  Here `dim(R̂/P̂) ≤ 1` is proved: `Mᵏ ⊆ P + aR`
for some `k`, so `M̂ᵏ ⊆ P̂ + aR̂` and `M̂/P̂` is minimal over the principal ideal `(a)` of `R̂/P̂`
(Krull's principal ideal theorem). -/
private theorem nu_localization_le_of_minimal [Hironaka.Cited.CurveFiniteIntegralClosure.{u}] {R : Type u} [CommRing R]
    [IsRegularLocalRing R] (J : Ideal R) (hJ : J ≠ ⊥) (P : Ideal R) [P.IsPrime] (a : R)
    (ha : maximalIdeal R ∈ (P ⊔ Ideal.span {a}).minimalPrimes) :
    Ideal.nu (J.map (algebraMap R (Localization.AtPrime P))) ≤ Ideal.nu J := by
  let Rh := AdicCompletion (maximalIdeal R) R
  have hRreg : IsRegularLocalRing Rh := isRegularLocalRing_adicCompletion_of_isRegularLocalRing R
  have hRdom : IsDomain Rh := isDomain_of_isRegularLocalRing Rh
  let ι := algebraMap R Rh
  obtain ⟨Ph₀, hPh₀, hcomap₀⟩ := exists_isPrime_comap_adicCompletion_eq P
  -- "`P̂` any minimal prime ideal associated with `PR̂`": a minimal prime of `PR̂` inside `P̂₀`
  obtain ⟨Ph, hPhmin, hPhle⟩ := Ideal.exists_minimalPrimes_le
    (show P.map ι ≤ Ph₀ from Ideal.map_le_iff_le_comap.mpr hcomap₀.ge)
  have hPh : Ph.IsPrime := hPhmin.1.1
  have hcomap : Ph.comap ι = P :=
    le_antisymm ((Ideal.comap_mono hPhle).trans hcomap₀.le)
      (Ideal.map_le_iff_le_comap.mp hPhmin.1.2)
  have hMh : maximalIdeal Rh = (maximalIdeal R).map ι := AdicCompletion.maximalIdeal_eq_map
  have hιloc : IsLocalHom ι := ((IsLocalRing.local_hom_TFAE ι).out 1 3).mpr hMh.ge
  -- `ν(Ĵ) ≤ ν(J)`: `M̂ᵛ ∩ R = Mᵛ`
  have h1 : Ideal.nu (J.map ι) ≤ Ideal.nu J := Ideal.ord_le fun ν hν => Ideal.le_ord <| by
    rw [hMh, ← Ideal.map_pow] at hν
    rw [← comap_map_adicCompletion_maximalIdeal ((maximalIdeal R) ^ ν)]
    exact Ideal.map_le_iff_le_comap.mp hν
  -- "`ν(Ĵ) = ν(J)` as is easily seen": the other inequality, `ν(J) ≤ ν(Ĵ)`, holds for any
  -- local homomorphism
  have hν : Ideal.nu (J.map ι) = Ideal.nu J := le_antisymm h1 (nu_le_nu_map ι J)
  -- `Ĵ ≠ 0`
  have hJh : J.map ι ≠ ⊥ := by
    intro h0
    have h := comap_map_adicCompletion_maximalIdeal J
    have h' := comap_map_adicCompletion_maximalIdeal (⊥ : Ideal R)
    change (J.map ι).comap ι = J at h
    rw [h0] at h
    rw [Ideal.map_bot] at h'
    exact hJ (h.symm.trans h')
  -- `dim(R̂/P̂) ≤ 1`
  have hdim : ringKrullDim (Rh ⧸ Ph) ≤ 1 := by
    have hrad : maximalIdeal R ≤ (P ⊔ Ideal.span {a}).radical := by
      rw [Ideal.radical_eq_sInf]
      exact le_sInf fun q ⟨hIq, hq⟩ => ha.2 ⟨hq, hIq⟩ (le_maximalIdeal hq.ne_top)
    obtain ⟨k, hk⟩ := Ideal.exists_pow_le_of_le_radical_of_fg hrad (IsNoetherian.noetherian _)
    have hmin : maximalIdeal Rh ∈ (Ph ⊔ Ideal.span {ι a}).minimalPrimes := by
      refine ⟨⟨inferInstance, sup_le (le_maximalIdeal hPh.ne_top) ?_⟩,
        fun q ⟨hq, hqle⟩ _ => ?_⟩
      · rw [Ideal.span_le, Set.singleton_subset_iff, hMh]
        exact Ideal.mem_map_of_mem _
          (ha.1.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self a)))
      · have := hq
        refine Ideal.IsPrime.le_of_pow_le (n := k) ?_
        rw [hMh, ← Ideal.map_pow]
        refine (Ideal.map_mono hk).trans ?_
        rw [Ideal.map_sup, Ideal.map_span, Set.image_singleton]
        refine le_trans (sup_le_sup_right ?_ _) hqle
        rw [Ideal.map_le_iff_le_comap, hcomap]
    rw [ringKrullDim_le_iff_isMaximal_height_le]
    intro m hm
    have hm' : m = (maximalIdeal Rh).map (Ideal.Quotient.mk Ph) := by
      have : (m.comap (Ideal.Quotient.mk Ph)).IsMaximal :=
        Ideal.comap_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective
      rw [← IsLocalRing.eq_maximalIdeal this,
        Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective]
    rw [hm']
    exact_mod_cast Ideal.map_height_le_one_of_mem_minimalPrimes hmin
  have h2 := nu_localization_le_of_curveResolvable
    (curveResolvable_of_isAdicComplete Ph hdim) (J.map ι) hJh
  -- `R_P → R̂_{P̂}` is a local homomorphism
  let φ := Localization.localRingHom P Ph ι hcomap.symm
  have hφ : (J.map (algebraMap R (Localization.AtPrime P))).map φ =
      (J.map ι).map (algebraMap Rh (Localization.AtPrime Ph)) := by
    rw [Ideal.map_map, Ideal.map_map]
    congr 1
    exact RingHom.ext fun x => Localization.localRingHom_to_map P Ph ι hcomap.symm x
  calc Ideal.nu (J.map (algebraMap R (Localization.AtPrime P)))
      ≤ Ideal.nu ((J.map (algebraMap R (Localization.AtPrime P))).map φ) :=
        nu_le_nu_map φ _
    _ = Ideal.nu ((J.map ι).map (algebraMap Rh (Localization.AtPrime Ph))) := by rw [hφ]
    _ ≤ Ideal.nu (J.map ι) := h2
    _ = Ideal.nu J := hν

/-- A noetherian local ring `S` with a prime `p` such that the maximal ideal is minimal over `p + aS`
has `dim(S/p) ≤ 1` (Krull's principal ideal theorem). -/
private theorem ringKrullDim_quotient_le_one_of_mem_minimalPrimes {S : Type u} [CommRing S]
    [IsLocalRing S] [IsNoetherianRing S] (p : Ideal S) [p.IsPrime] (a : S)
    (hmin : maximalIdeal S ∈ (p ⊔ Ideal.span {a}).minimalPrimes) : ringKrullDim (S ⧸ p) ≤ 1 := by
  rw [ringKrullDim_le_iff_isMaximal_height_le]
  intro m hm
  have hm' : m = (maximalIdeal S).map (Ideal.Quotient.mk p) := by
    have : (m.comap (Ideal.Quotient.mk p)).IsMaximal :=
      Ideal.comap_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective
    rw [← IsLocalRing.eq_maximalIdeal this,
      Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective]
  rw [hm']
  exact_mod_cast Ideal.map_height_le_one_of_mem_minimalPrimes hmin

/-- Theorem 1 in the case `dim(R/P) ≤ 1` (the case `dim(R/P) = 1` of p. 218; for `P = M` the
claim is Lemma 7): the maximal ideal `M` is minimal over `P + aR` for any `a ∈ M \ P`, which is
the form in which `nu_localization_le_of_minimal` takes the hypothesis. -/
private theorem nu_localization_le_of_dim_le_one [Hironaka.Cited.CurveFiniteIntegralClosure.{u}] (R : Type u) [CommRing R] [IsRegularLocalRing R]
    (J : Ideal R) (hJ : J ≠ ⊥) (P : Ideal R) [P.IsPrime] (hdim : ringKrullDim (R ⧸ P) ≤ 1) :
    Ideal.nu (J.map (algebraMap R (Localization.AtPrime P))) ≤ Ideal.nu J := by
  by_cases hPM : P = maximalIdeal R
  · subst hPM
    exact nu_localization_maximalIdeal_le R J hJ
  obtain ⟨a, haM, haP⟩ :=
    IsConcreteLE.exists_of_lt (lt_of_le_of_ne (le_maximalIdeal Ideal.IsPrime.ne_top') hPM)
  have hK : Ring.KrullDimLE 1 (R ⧸ P) := Ring.krullDimLE_iff.mpr hdim
  refine nu_localization_le_of_minimal J hJ P a ⟨⟨inferInstance, sup_le
    (le_maximalIdeal Ideal.IsPrime.ne_top')
    (by rwa [Ideal.span_le, Set.singleton_subset_iff])⟩, fun q ⟨hq, hqle⟩ _ => ?_⟩
  -- a prime `q ⊋ P` is maximal, since `R/P` is a domain of dimension `≤ 1`
  have hPq : P ≤ q := le_sup_left.trans hqle
  have haq : a ∈ q := hqle (Ideal.mem_sup_right (Ideal.mem_span_singleton_self a))
  have hqmap : (q.map (Ideal.Quotient.mk P)).IsPrime :=
    Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by rwa [Ideal.mk_ker])
  have hne : q.map (Ideal.Quotient.mk P) ≠ ⊥ := by
    intro h0
    have : Ideal.Quotient.mk P a ∈ q.map (Ideal.Quotient.mk P) := Ideal.mem_map_of_mem _ haq
    rw [h0, Ideal.mem_bot, Ideal.Quotient.eq_zero_iff_mem] at this
    exact haP this
  have hmax := Ideal.IsPrime.isMaximal_of_ne_bot hqmap hne
  have hqmax : q.IsMaximal := by
    have := hmax
    have := Ideal.comap_isMaximal_of_surjective (K := q.map (Ideal.Quotient.mk P))
      (Ideal.Quotient.mk P) Ideal.Quotient.mk_surjective
    rwa [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective, ← RingHom.ker_eq_comap_bot,
      Ideal.mk_ker, sup_eq_left.mpr hPq] at this
  exact (IsLocalRing.eq_maximalIdeal hqmax).ge

/-- p. 218: "We have a chain of prime ideals `P = P₀ ⊂ P₁ ⊂ ⋯ ⊂ P_s = M` where `M` is the maximal
ideal of `R` and `dim(R_{P_i}/P_{i-1}R_{P_i})` for `i = 1, 2, …, s` are all equal to one", as an
inductive predicate on `P₀` (the chain read from `P_s = M` downwards).  For a strict inclusion
`P ⊂ Q` the dimension of `R_Q/PR_Q` is at least one, so the condition `≤ 1` below is `= 1`. -/
private inductive DimOneChain (R : Type u) [CommRing R] [IsLocalRing R] : Ideal R → Prop
  /-- `s = 0`: `P = M`. -/
  | top : DimOneChain R (maximalIdeal R)
  /-- `P_{i-1} ⊂ P_i` with `dim(R_{P_i}/P_{i-1}R_{P_i}) = 1`. -/
  | step (P Q : Ideal R) [P.IsPrime] [Q.IsPrime] (hPQ : P < Q)
      (hdim : ringKrullDim (Localization.AtPrime Q ⧸
        P.map (algebraMap R (Localization.AtPrime Q))) ≤ 1)
      (h : DimOneChain R Q) : DimOneChain R P

/-- The chain of p. 218 exists (the paper says "We have a chain"): induction on `P` from the top
(`R` is noetherian); for `P ≠ M` pick `a ∈ M \ P` and a minimal prime `Q` of `P + aR`; then
`P ⊂ Q` and `dim(R_Q/PR_Q) ≤ 1` by Krull's principal ideal theorem. -/
private theorem exists_dimOneChain [Hironaka.Cited.IsRegularLocalRingLocalizationOfIsRegularLocalRing.{u}] (R : Type u) [CommRing R] [IsRegularLocalRing R]
    (P : Ideal R) [P.IsPrime] : DimOneChain R P := by
  refine WellFoundedGT.induction (motive := fun P : Ideal R => ∀ _ : P.IsPrime,
    DimOneChain R P) P ?_ inferInstance
  intro P ih hP
  by_cases hPM : P = maximalIdeal R
  · subst hPM
    exact DimOneChain.top
  obtain ⟨a, haM, haP⟩ :=
    IsConcreteLE.exists_of_lt (lt_of_le_of_ne (le_maximalIdeal hP.ne_top) hPM)
  have hIM : P ⊔ Ideal.span {a} ≤ maximalIdeal R :=
    sup_le (le_maximalIdeal hP.ne_top) (by rwa [Ideal.span_le, Set.singleton_subset_iff])
  obtain ⟨Q, hQ, -⟩ := Ideal.exists_minimalPrimes_le hIM
  have hQp : Q.IsPrime := hQ.1.1
  have haQ : a ∈ Q := hQ.1.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self a))
  have hPQ : P < Q := lt_of_le_of_ne (le_sup_left.trans hQ.1.2) fun h => haP (h ▸ haQ)
  have hRQ : IsRegularLocalRing (Localization.AtPrime Q) :=
    isRegularLocalRing_localization_of_isRegularLocalRing R Q
  let RQ := Localization.AtPrime Q
  have hdisj : Disjoint (Q.primeCompl : Set R) P :=
    Set.disjoint_left.mpr fun b hb hbP => hb (hPQ.le hbP)
  have hp : (P.map (algebraMap R RQ)).IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint Q.primeCompl RQ P hP hdisj
  have hmin : maximalIdeal RQ ∈
      (P.map (algebraMap R RQ) ⊔ Ideal.span {algebraMap R RQ a}).minimalPrimes := by
    have : P.map (algebraMap R RQ) ⊔ Ideal.span {algebraMap R RQ a} =
        (P ⊔ Ideal.span {a}).map (algebraMap R RQ) := by
      rw [Ideal.map_sup, Ideal.map_span, Set.image_singleton]
    rw [this, IsLocalization.minimalPrimes_map Q.primeCompl RQ, Set.mem_preimage,
      Localization.AtPrime.under_maximalIdeal]
    exact hQ
  exact DimOneChain.step P Q hPQ
    (ringKrullDim_quotient_le_one_of_mem_minimalPrimes _ _ hmin) (ih Q hPQ hQp)

/-- Proof of Theorem 1, p. 218, the first reduction: "Therefore it suffices to prove the
inequality for the case in which `dim(R/P) = 1`".  Given the chain `P = P₀ ⊂ ⋯ ⊂ P_s = M`, the
case `dim ≤ 1` for the regular local rings `R_{P_i}` and their primes `P_{i-1}R_{P_i}` gives
`ν(JR_{P_{i-1}}) ≤ ν(JR_{P_i})` for `i = 1, …, s`, and `ν(JR_{P_s}) = ν(JR_M) ≤ ν(J)` (Lemma 7). -/
private theorem nu_localization_le_of_dimOneChain [Hironaka.Cited.IsRegularLocalRingLocalizationOfIsRegularLocalRing.{u}] {R : Type u} [CommRing R]
    [IsRegularLocalRing R]
    (hdim1 : ∀ (S : Type u) [CommRing S] [IsRegularLocalRing S] (I : Ideal S), I ≠ ⊥ →
      ∀ (p : Ideal S) [p.IsPrime], ringKrullDim (S ⧸ p) ≤ 1 →
        Ideal.nu (I.map (algebraMap S (Localization.AtPrime p))) ≤ Ideal.nu I)
    (J : Ideal R) (hJ : J ≠ ⊥) {P : Ideal R} (h : DimOneChain R P) :
    ∀ [P.IsPrime], Ideal.nu (J.map (algebraMap R (Localization.AtPrime P))) ≤ Ideal.nu J := by
  induction h with
  | top =>
    intro _
    exact nu_localization_maximalIdeal_le R J hJ
  | step P Q hPQ hdim hQ ih =>
    intro hP
    have : IsDomain R := isDomain_of_isRegularLocalRing R
    have ihQ := ih
    -- `R_Q` is regular (Serre), with the prime `PR_Q` and `(R_Q)_{PR_Q} = R_P`
    have hRQ : IsRegularLocalRing (Localization.AtPrime Q) :=
      isRegularLocalRing_localization_of_isRegularLocalRing R Q
    let RQ := Localization.AtPrime Q
    let p : Ideal RQ := P.map (algebraMap R RQ)
    have hdisj : Disjoint (Q.primeCompl : Set R) P :=
      Set.disjoint_left.mpr fun b hb hbP => hb (hPQ.le hbP)
    have hp : p.IsPrime := IsLocalization.isPrime_of_isPrime_disjoint Q.primeCompl RQ P hP hdisj
    have hcomap : p.comap (algebraMap R RQ) = P :=
      IsLocalization.under_map_of_isPrime_disjoint Q.primeCompl RQ hP hdisj
    have hJQ : J.map (algebraMap R RQ) ≠ ⊥ := by
      rw [Ne, Ideal.map_eq_bot_iff_of_injective
        (IsLocalization.injective RQ (Ideal.primeCompl_le_nonZeroDivisors Q))]
      exact hJ
    have hstep := hdim1 RQ (J.map (algebraMap R RQ)) hJQ p hdim
    let T := Localization.AtPrime p
    have hT : IsLocalization.AtPrime T (p.comap (algebraMap R RQ)) :=
      IsLocalization.isLocalization_isLocalization_atPrime_isLocalization Q.primeCompl T p
    have hM : (p.comap (algebraMap R RQ)).primeCompl = P.primeCompl := by
      ext b
      rw [Ideal.mem_primeCompl_iff, Ideal.mem_primeCompl_iff, hcomap]
    have hT' : IsLocalization P.primeCompl T := by
      rw [← hM]
      exact hT
    let e : Localization.AtPrime P ≃ₐ[R] T :=
      IsLocalization.algEquiv P.primeCompl (Localization.AtPrime P) T
    have h1 : (J.map (algebraMap R (Localization.AtPrime P))).map
        (e.toRingEquiv : Localization.AtPrime P →+* T) =
        (J.map (algebraMap R RQ)).map (algebraMap RQ T) := by
      rw [Ideal.map_map, Ideal.map_map, ← IsScalarTower.algebraMap_eq]
      congr 1
      exact RingHom.ext fun b => e.commutes b
    calc Ideal.nu (J.map (algebraMap R (Localization.AtPrime P)))
        = Ideal.nu ((J.map (algebraMap R (Localization.AtPrime P))).map
            (e.toRingEquiv : Localization.AtPrime P →+* T)) :=
          (nu_map_of_bijective _ e.bijective _).symm
      _ = Ideal.nu ((J.map (algebraMap R RQ)).map (algebraMap RQ T)) := by rw [h1]
      _ ≤ Ideal.nu (J.map (algebraMap R RQ)) := hstep
      _ ≤ Ideal.nu J := ihQ

/-- Theorem 1 (Zariski–Nagata), p. 218: "Let `R` be a regular local ring and `J` a non-zero ideal
in `R`. Let `P` be any prime ideal in `R`. Then we have `ν(J) ≥ ν(JR_P)`."

Footnote 3: "This theorem and the proof are O. Zariski's. It was pointed out by A. Grothendieck
that the theorem has also been given a proof by M. Nagata."

The proof is that of the paper: the chain `P = P_0 ⊂ ⋯ ⊂ P_s = M` with `dim(R_{P_i}/P_{i-1}R_{P_i}) = 1`
(`DimOneChain`, `exists_dimOneChain`) reduces the inequality to the case `dim(R/P) ≤ 1`
(`nu_localization_le_of_dimOneChain`); in that case one passes to the completion `R̂` with `P̂` a
minimal prime of `PR̂` (`nu_localization_le_of_minimal`), where the sequence of monoidal transforms
(i)–(iii) (`curveResolvable_of_isAdicComplete`) and Lemmas 7 and 8 conclude
(`nu_localization_le_of_curveResolvable`).

Applying the one-dimensional case to `R_{P_i}` uses that `R_{P_i}` is regular, which the paper
uses tacitly and cites in footnote 9, p. 243 (Serre): the cited leaf
`isRegularLocalRing_localization_of_isRegularLocalRing`
(`Hironaka/Compat/RegularLocalization.lean`).  Gaps filled: the existence of the chain ("We have a
chain"), `dim(R̂/P̂) ≤ 1`, and the equalities `ν(Ĵ) = ν(J)` and `ν(J_s(R_s)_{P_s}) = ν(JR_P)`. -/
@[blueprint "thm:III.1"
  (statement := /-- (Zariski--Nagata.) Let $R$ be a regular local ring and $J$ a non-zero
    ideal in $R$. Let $P$ be any prime ideal in $R$. Then we have $\nu(J)\ge\nu(JR_P)$.
    (Theorem 1, p.~218.) Footnote 3: ``This theorem and the proof are O.~Zariski's. It was
    pointed out by A.~Grothendieck that the theorem has also been given a proof by
    M.~Nagata.'' -/)
  (proof := /-- We have a chain of prime ideals $P=P_0\subset P_1\subset\dots\subset P_s=M$
    where $M$ is the maximal ideal of $R$ and $\dim(R_{P_i}/P_{i-1}R_{P_i})$ for
    $i=1,2,\dots,s$ are all equal to one. Therefore it suffices to prove the inequality for
    the case in which $\dim(R/P)=1$. On the other hand, let $\hat R$ be the completion of $R$,
    $\hat P$ any minimal prime ideal associated with $P\hat R$, and $\hat J=J\hat R$. Then we
    have a canonical local homomorphism $R_P\to\hat R_{\hat P}$. Hence
    $\nu(JR_P)\le\nu(\hat J\hat R_{\hat P})$, while $\nu(J)=\nu(\hat J)$ as is easily seen.
    Therefore, it suffices to show $\nu(\hat J)\ge\nu(\hat J\hat R_{\hat P})$. In other words,
    we may assume that $R$ is complete. Thus we shall assume that $R$ is complete and
    $\dim(R/P)=1$. Let $S=R/P$. Then we know that the derived normal ring of $S$ in its field
    of quotients is an $S$-module of finite type and that every localization of the derived
    normal ring is regular. In view of these facts, it is not difficult to show that there exists
    a finite sequence of successive monoidal transforms with center the maximal ideals,
    $R=R_0\to R_1\to\dots\to R_s$, such that: (i) $R_i$ is residually algebraic over
    $R_{i-1}$ for $i=1,2,\dots,s$; (ii) for each $i\ge1$, there exists a prime ideal $P_i$ in
    $R_i$ such that $R_P=(R_i)_{P_i}$; and (iii) $R_s/P_s$ is regular. Let $J_i$ be the
    ideals in $R_i$ ($0\le i\le s$) such that $J=J_0$, and that $J_i$ is the weak transform of
    $J_{i-1}$ in $R_i$ ($1\le i\le s$). Then by \cref{lem:III.8}, we have
    $\nu(J)\ge\nu(J_1)\ge\dots\ge\nu(J_s)$; and, by \cref{lem:III.7}, we have
    $\nu(J_s)\ge\nu(J_s(R_s)_{P_s})=\nu(JR_P)$. Hence $\nu(J)\ge\nu(JR_P)$.

    [Formalization: the first ``known'' fact is the cited leaf
    \cref{lem:III.1-derived-normal-ring-finite}; the second is proved (the derived normal ring
    is a discrete valuation ring or a field). The sequence of monoidal transforms is
    \cref{lem:III.1-curve-resolution}.]

    \textbf{Gaps in the paper filled.} (1) ``We have a chain'' is proved: for $P\ne M$ pick
    $a\in M\setminus P$ and a minimal prime $Q$ of $P+aR$; then $P\subset Q$ and
    $\dim(R_Q/PR_Q)\le1$ by Krull's principal ideal theorem. (2) $\dim(\hat R/\hat P)\le1$
    for a minimal prime $\hat P$ of $P\hat R$ (the paper silently takes it to be one) is proved
    by Krull's principal ideal theorem. (3) $\nu(\hat J)=\nu(J)$: $M^\nu\hat R\cap R=M^\nu$
    gives $\le$, and $\ge$ holds for any local homomorphism. (4) The equality
    $\nu(J_s(R_s)_{P_s})=\nu(JR_P)$ is proved one transform at a time: under $R_P=(R_i)_{P_i}$,
    $J_i(R_i)_{P_i}=J_{i-1}(R_i)_{P_i}$, because every generator $x^{-\nu}f$ of the weak
    transform has $x$ a unit in $(R_i)_{P_i}$ (otherwise $P=M$). The sequence of monoidal
    transforms is used through an inductive predicate. -/)
  (latexEnv := "theorem")]
theorem nu_localization_le [Hironaka.Cited.CurveFiniteIntegralClosure.{u}] [Hironaka.Cited.IsRegularLocalRingLocalizationOfIsRegularLocalRing.{u}] (R : Type u) [CommRing R] [IsRegularLocalRing R] (J : Ideal R)
    (hJ : J ≠ ⊥) (P : Ideal R) [P.IsPrime] :
    Ideal.nu (J.map (algebraMap R (Localization.AtPrime P))) ≤ Ideal.nu J :=
  -- "We have a chain of prime ideals `P = P_0 ⊂ ⋯ ⊂ P_s = M` …  Therefore it suffices to prove
  -- the inequality for the case in which `dim (R/P) = 1`."
  nu_localization_le_of_dimOneChain
    (fun S _ _ I hI p _ hdim => nu_localization_le_of_dim_le_one S I hI p hdim) J hJ
    (exists_dimOneChain R P)

/-! ### Lemma 9 (pp. 218–220) -/

open Polynomial in
/-- The graded step (Lemma 6 of Ch. II, Lemma 9 of Ch. III): if the class of `a ∈ Iⁿ` in
`gr_I(A)` lies in the ideal generated by classes `[b_j] ∈ gr^{d_j}_I(A)`, then
`a − Σ c_j b_j ∈ Iⁿ⁺¹` for some `c_j ∈ I^{n − d_j}` (`c_j = 0` if `d_j > n`). -/
private theorem exists_sub_mem_pow_of_mk_mem_span {A : Type*} [CommRing A] (I : Ideal A) {m n : ℕ}
    (b : Fin m → A) (d : Fin m → ℕ) (hb : ∀ j, b j ∈ I ^ d j) {a : A} (ha : a ∈ I ^ n)
    (h : AssocGraded.mk I n a ha ∈
      Ideal.span (Set.range fun j => AssocGraded.mk I (d j) (b j) (hb j))) :
    ∃ c : Fin m → A, (∀ j, d j ≤ n → c j ∈ I ^ (n - d j)) ∧ (∀ j, n < d j → c j = 0) ∧
      a - ∑ j, c j * b j ∈ I ^ (n + 1) := by
  classical
  obtain ⟨cg, hc⟩ := Ideal.mem_span_range_iff_exists_fun.mp h
  choose p hp using fun j => Ideal.Quotient.mk_surjective (cg j)
  have hmono : ∀ j, (monomial (d j) (b j) : A[X]) ∈ reesAlgebra I :=
    fun j => reesAlgebra.monomial_mem.mpr (hb j)
  have hq : (∑ j, p j * ⟨monomial (d j) (b j), hmono j⟩ -
      ⟨monomial n a, reesAlgebra.monomial_mem.mpr ha⟩ : reesAlgebra I) ∈
      I.map (algebraMap A (reesAlgebra I)) := by
    rw [← Ideal.Quotient.eq]
    refine (map_sum (Ideal.Quotient.mk (I.map (algebraMap A (reesAlgebra I)))).toAddMonoidHom
      _ _).trans ((Finset.sum_congr rfl fun j _ => ?_).trans hc)
    rw [← hp j]
    exact (Ideal.Quotient.mk (I.map (algebraMap A (reesAlgebra I)))).toMonoidHom.map_mul _ _
  have hcoeff := (mem_map_algebraMap_reesAlgebra_iff _).mp hq n
  have hco : ∀ j, ((p j : A[X]) * monomial (d j) (b j)).coeff n =
      if d j ≤ n then (p j : A[X]).coeff (n - d j) * b j else 0 := by
    intro j
    rw [← C_mul_X_pow_eq_monomial, ← mul_assoc, coeff_mul_X_pow', coeff_mul_C]
  simp only [AddSubgroupClass.coe_sub, AddSubmonoidClass.coe_finsetSum, MulMemClass.coe_mul,
    coeff_sub, finsetSum_coeff, hco, coeff_monomial_same] at hcoeff
  refine ⟨fun j => if d j ≤ n then (p j : A[X]).coeff (n - d j) else 0, fun j hj => ?_,
    fun j hj => ?_, ?_⟩
  · simp only [ite_eq_left hj]
    exact (mem_reesAlgebra_iff I _).mp (p j).2 _
  · simp [not_le.mpr hj]
  · have hsum : ∑ j, (if d j ≤ n then (p j : A[X]).coeff (n - d j) else 0) * b j =
        ∑ j, (if d j ≤ n then (p j : A[X]).coeff (n - d j) * b j else 0) :=
      Finset.sum_congr rfl fun j _ => by split_ifs <;> simp
    rw [hsum, ← neg_sub]
    exact neg_mem hcoeff

/-- `[a] ∈ grᵏ_I(A)` only depends on `a` and `k`. -/
private theorem mk_congr' {A : Type*} [CommRing A] (I : Ideal A) {k k' : ℕ} (hk : k = k') {a a' : A}
    (haa : a = a') (h : a ∈ I ^ k) (h' : a' ∈ I ^ k') :
    AssocGraded.mk I k a h = AssocGraded.mk I k' a' h' := by
  subst hk haa
  rfl

/-- Converse of the graded step: if `a − Σ_{j ∈ S} c_j b_j ∈ Iⁿ⁺¹` with `c_j ∈ I^{n − d_j}`, then
the class of `a` in `grⁿ_I(A)` lies in the ideal generated by the classes of the `b_j`, `j ∈ S`. -/
private theorem mk_mem_span_of_sub_mem_pow {A : Type*} [CommRing A] (I : Ideal A) {m n : ℕ}
    (b : Fin m → A) (d : Fin m → ℕ) (hb : ∀ j, b j ∈ I ^ d j) {a : A} (ha : a ∈ I ^ n)
    (S : Finset (Fin m)) (c : Fin m → A) (hc : ∀ j ∈ S, d j ≤ n ∧ c j ∈ I ^ (n - d j))
    (h : a - ∑ j ∈ S, c j * b j ∈ I ^ (n + 1)) :
    AssocGraded.mk I n a ha ∈
      Ideal.span ((fun j => AssocGraded.mk I (d j) (b j) (hb j)) '' (S : Set (Fin m))) := by
  classical
  have hterm : ∀ j ∈ S, c j * b j ∈ I ^ n := by
    intro j hj
    have := Ideal.mul_mem_mul (hc j hj).2 (hb j)
    rwa [← pow_add, Nat.sub_add_cancel (hc j hj).1] at this
  have hprod : ∀ j (hj : j ∈ S), AssocGraded.mk I n (c j * b j) (hterm j hj) =
      AssocGraded.mk I (n - d j) (c j) (hc j hj).2 * AssocGraded.mk I (d j) (b j) (hb j) := by
    intro j hj
    rw [AssocGraded.mk_mul_mk]
    exact mk_congr' I (Nat.sub_add_cancel (hc j hj).1).symm rfl _ _
  have hS : ∑ j ∈ S, c j * b j ∈ I ^ n := sum_mem hterm
  -- `a ↦ [a]` is additive on `Iⁿ`
  have hlin : AssocGraded.mk I n (∑ j ∈ S, c j * b j) hS =
      ∑ j ∈ S.attach, AssocGraded.mk I n (c j.1 * b j.1) (hterm j.1 j.2) := by
    have h1 : (⟨∑ j ∈ S, c j * b j, hS⟩ : ↥(I ^ n)) =
        ∑ j ∈ S.attach, (⟨c j.1 * b j.1, hterm j.1 j.2⟩ : ↥(I ^ n)) := by
      apply Subtype.ext
      rw [AddSubmonoidClass.coe_finsetSum]
      exact (Finset.sum_attach S (fun j => c j * b j)).symm
    have h2 := congrArg (AssocGraded.mkLinear I n) h1
    rw [map_sum] at h2
    exact h2
  have hmem : AssocGraded.mk I n (∑ j ∈ S, c j * b j) hS ∈
      Ideal.span ((fun j => AssocGraded.mk I (d j) (b j) (hb j)) '' (S : Set (Fin m))) := by
    rw [hlin]
    refine sum_mem fun j _ => ?_
    rw [hprod j.1 j.2]
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨j.1, j.2, rfl⟩)
  have hsplit : a = (a - ∑ j ∈ S, c j * b j) + ∑ j ∈ S, c j * b j := by ring
  rw [mk_congr' I rfl hsplit ha (add_mem (Ideal.pow_le_pow_right (Nat.le_succ n) h) hS),
    AssocGraded.mk_add I n _ _ (Ideal.pow_le_pow_right (Nat.le_succ n) h) hS,
    (AssocGraded.mk_eq_zero_iff I _).mpr h, zero_add]
  exact hmem

/-- The residue-field argument closing Lemma 9: for a system `F_j ∈ m^{ν_j}` (`ν` monotone) of a
local ring whose classes `[F_j] ∈ gr^{ν_j}_m` satisfy (iii) of Lemma 1, no relation
`F_i ≡ Σ_{j ≠ i} D_j F_j (mod m^{ν_i+1})` with `D_j ∈ m^{ν_i − ν_j}` exists. -/
private theorem false_of_sub_mem_pow {L : Type*} [CommRing L] [IsLocalRing L] {m : ℕ}
    (F : Fin m → L)
    (ν : Fin m → ℕ) (hν : Monotone ν) (hF : ∀ j, F j ∈ maximalIdeal L ^ ν j)
    (hirr : ∀ k : Fin m, AssocGraded.mk (maximalIdeal L) (ν k) (F k) (hF k) ∉
      Ideal.span (Set.range fun j : Fin k =>
        AssocGraded.mk (maximalIdeal L) (ν (Fin.castLE k.2.le j)) (F (Fin.castLE k.2.le j))
          (hF _)))
    (i : Fin m) (D : Fin m → L) (hDi : D i = 0)
    (hD : ∀ j, ν j ≤ ν i → D j ∈ maximalIdeal L ^ (ν i - ν j)) (hD0 : ∀ j, ν i < ν j → D j = 0)
    (h : F i - ∑ j, D j * F j ∈ maximalIdeal L ^ (ν i + 1)) : False := by
  classical
  set M := maximalIdeal L
  -- the ideal generated by the classes with index `< k`
  have hW : ∀ k : Fin m, Ideal.span ((fun j => AssocGraded.mk M (ν j) (F j) (hF j)) ''
      ((Finset.univ.filter (· < k) : Finset (Fin m)) : Set (Fin m))) =
      Ideal.span (Set.range fun j : Fin k =>
        AssocGraded.mk M (ν (Fin.castLE k.2.le j)) (F (Fin.castLE k.2.le j)) (hF _)) := by
    intro k
    congr 1
    ext y
    constructor
    · rintro ⟨j, hj, rfl⟩
      have hjk : (j : ℕ) < k := by simpa using hj
      exact ⟨⟨j, hjk⟩, rfl⟩
    · rintro ⟨j, rfl⟩
      refine ⟨Fin.castLE k.2.le j, ?_, rfl⟩
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq]
      exact j.2
  -- a relation `F_k ≡ Σ_{j < k} D'_j F_j` contradicts (iii) at `k`
  have key : ∀ (k : Fin m) (D' : Fin m → L), (∀ j, j < k → D' j ∈ M ^ (ν k - ν j)) →
      (∀ j, ¬ j < k → D' j = 0) → F k - ∑ j, D' j * F j ∈ M ^ (ν k + 1) → False := by
    intro k D' hD' hD'0 hk
    apply hirr k
    rw [← hW k]
    refine mk_mem_span_of_sub_mem_pow M F ν hF (hF k) _ D' (fun j hj => ?_) ?_
    · have hjk : j < k := by simpa using hj
      exact ⟨hν hjk.le, hD' j hjk⟩
    · have hsum : ∑ j ∈ Finset.univ.filter (· < k), D' j * F j = ∑ j, D' j * F j := by
        rw [Finset.sum_filter]
        refine Finset.sum_congr rfl fun j _ => ?_
        split_ifs with hj
        · rfl
        · rw [hD'0 j hj, zero_mul]
      rw [hsum]
      exact hk
  -- terms `D_j F_j` with `D_j ∈ M` and `ν_j ≥ ν_i` are negligible
  have hsmall : ∀ j, ν i ≤ ν j → D j ∈ M → D j * F j ∈ M ^ (ν i + 1) := by
    intro j hij hDj
    have := Ideal.mul_mem_mul hDj (hF j)
    rw [← pow_succ'] at this
    exact Ideal.pow_le_pow_right (by omega) this
  by_cases hT : ∃ j, i < j ∧ D j ∉ M
  · -- `k` the largest index `> i` with `D_k` a unit
    let T := Finset.univ.filter fun j => i < j ∧ D j ∉ M
    have hTne : T.Nonempty := by
      obtain ⟨j, hj⟩ := hT
      exact ⟨j, by simpa [T] using hj⟩
    set k := T.max' hTne with hkdef
    have hkT : k ∈ T := T.max'_mem hTne
    simp only [T, Finset.mem_filter, Finset.mem_univ, true_and] at hkT
    obtain ⟨hik, hDk⟩ := hkT
    have hνk : ν k = ν i := by
      by_contra hne
      have : ν i < ν k := lt_of_le_of_ne (hν hik.le) (Ne.symm hne)
      exact hDk (hD0 k this ▸ zero_mem _)
    have hu : IsUnit (D k) := (IsLocalRing.mem_maximalIdeal _).not.mp hDk |> not_not.mp
    obtain ⟨u, hu'⟩ := hu.exists_left_inv
    refine key k (fun j => if j < k then u * (if j = i then 1 else -D j) else 0)
      (fun j hj => ?_) (fun j hj => by simp [hj]) ?_
    · simp only [ite_eq_left hj]
      by_cases hji : j = i
      · subst hji
        rw [hνk, Nat.sub_self, pow_zero, Ideal.one_eq_top]
        exact Submodule.mem_top
      · simp only [ite_eq_right hji, mul_neg]
        have hνj : ν j ≤ ν i := hνk ▸ hν hj.le
        rw [hνk]
        exact neg_mem (Ideal.mul_mem_left _ _ (hD j hνj))
    · -- `F_k − Σ_{j<k} D'_j F_j = u·(D_k F_k − F_i + Σ_{j<k} D_j F_j)`
      have hlarge : ∑ j ∈ Finset.univ.filter (fun j => k < j), D j * F j ∈ M ^ (ν i + 1) := by
        refine sum_mem fun j hj => ?_
        have hkj : k < j := by simpa using hj
        refine hsmall j (hν (hik.trans hkj).le) ?_
        by_contra hDj
        have : j ∈ T := by simp [T, hik.trans hkj, hDj]
        exact absurd (T.le_max' j this) (not_le.mpr hkj)
      have hsplit : ∑ j, D j * F j = ∑ j ∈ Finset.univ.filter (· < k), D j * F j + D k * F k +
          ∑ j ∈ Finset.univ.filter (fun j => k < j), D j * F j := by
        rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (· < k), add_assoc]
        congr 1
        have hins : Finset.univ.filter (fun j => ¬ j < k) =
            insert k (Finset.univ.filter (fun j => k < j)) := by
          ext j
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, not_lt]
          constructor
          · intro hj
            rcases hj.lt_or_eq with h' | h'
            · exact Or.inr h'
            · exact Or.inl h'.symm
          · rintro (rfl | hj)
            · exact le_rfl
            · exact hj.le
        rw [hins, Finset.sum_insert (by simp)]
      have hsum' : ∑ j, (if j < k then u * (if j = i then 1 else -D j) else 0) * F j =
          u * F i - u * ∑ j ∈ Finset.univ.filter (· < k), D j * F j := by
        have hterm : ∀ j, (if j < k then u * (if j = i then 1 else -D j) else 0) * F j =
            (if j = i then u * F j else 0) - (if j < k then u * (D j * F j) else 0) := by
          intro j
          by_cases hji : j = i
          · subst hji
            simp [hik, hDi]
          · by_cases hjk : j < k
            · simp [hji, hjk]
              ring
            · simp [hji, hjk]
        rw [Finset.sum_congr rfl fun j _ => hterm j, Finset.sum_sub_distrib,
          Finset.sum_ite_eq' Finset.univ i, ite_eq_left (Finset.mem_univ i), Finset.mul_sum,
          Finset.sum_filter]
      have heq : F k - ∑ j, (if j < k then u * (if j = i then 1 else -D j) else 0) * F j =
          -u * (F i - ∑ j, D j * F j) - u * ∑ j ∈ Finset.univ.filter (fun j => k < j),
            D j * F j := by
        rw [hsum', hsplit]
        linear_combination (-F k) * hu'
      rw [heq, hνk]
      exact sub_mem (Ideal.mul_mem_left _ _ h) (Ideal.mul_mem_left _ _ hlarge)
  · -- all `D_j`, `j > i`, lie in `M`: then `F_i ≡ Σ_{j<i} D_j F_j`
    push Not at hT
    refine key i (fun j => if j < i then D j else 0) (fun j hj => ?_)
      (fun j hj => by simp [hj]) ?_
    · simp only [ite_eq_left hj]
      exact hD j (hν hj.le)
    · have heq : F i - ∑ j, (if j < i then D j else 0) * F j =
          (F i - ∑ j, D j * F j) + ∑ j, (if j < i then 0 else D j * F j) := by
        have hs : ∑ j, D j * F j = ∑ j, (if j < i then D j else 0) * F j +
            ∑ j, (if j < i then 0 else D j * F j) := by
          rw [← Finset.sum_add_distrib]
          exact Finset.sum_congr rfl fun j _ => by split_ifs <;> simp
        rw [hs]
        ring
      rw [heq]
      refine add_mem h (sum_mem fun j _ => ?_)
      split_ifs with hji
      · exact zero_mem _
      · rcases (not_lt.mp hji).lt_or_eq with hij | hij
        · exact hsmall j (hν hij.le) (hT j hij)
        · rw [← hij, hDi, zero_mul]
          exact zero_mem _

/-- A non-zero homogeneous element of `gr_I(A)` has a unique degree. -/
private theorem eq_of_mem_homogeneous {A : Type*} [CommRing A] (I : Ideal A) {a b : ℕ}
    {x : AssocGraded I} (ha : x ∈ AssocGraded.homogeneous I a)
    (hb : x ∈ AssocGraded.homogeneous I b) (hx : x ≠ 0) : a = b := by
  by_contra hne
  obtain ⟨y, rfl⟩ := LinearMap.mem_range.mp ha
  obtain ⟨y', hy'⟩ := LinearMap.mem_range.mp hb
  have h1 : grProj I a (AssocGraded.ofGrPiece I a y) = y := grProj_ofGrPiece_same I a y
  rw [← hy', grProj_ofGrPiece_ne I (Ne.symm hne)] at h1
  apply hx
  rw [← h1, map_zero]

section Lemma9Aux

/-- Membership in a finite sum of ideals. -/
private theorem exists_eq_sum_of_mem_finset_sum {A : Type*} [CommRing A]
    {ι : Type*} (s : Finset ι) (I : ι → Ideal A) {g : A}
    (hg : g ∈ ∑ a ∈ s, I a) : ∃ u : ι → A, (∀ a ∈ s, u a ∈ I a) ∧ ∑ a ∈ s, u a = g := by
  classical
  induction s using Finset.induction_on generalizing g with
  | empty =>
    rw [Finset.sum_empty, Submodule.zero_eq_bot, Submodule.mem_bot] at hg
    exact ⟨0, by simp, by simp [hg]⟩
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Submodule.add_eq_sup, Submodule.mem_sup] at hg
    obtain ⟨y, hy, z, hz, rfl⟩ := hg
    obtain ⟨u, hu, rfl⟩ := ih hz
    refine ⟨Function.update u a y, fun b hb => ?_, ?_⟩
    · rcases Finset.mem_insert.mp hb with rfl | hb
      · simpa using hy
      · rw [Function.update_of_ne (ne_of_mem_of_not_mem hb ha)]
        exact hu b hb
    · rw [Finset.sum_insert ha, Function.update_self]
      congr 1
      exact Finset.sum_congr rfl fun b hb =>
        Function.update_of_ne (ne_of_mem_of_not_mem hb ha) _ _

private theorem sum_le_of_forall_le {A : Type*} [CommRing A]
    {ι : Type*} (s : Finset ι) (I : ι → Ideal A) {K : Ideal A}
    (h : ∀ a ∈ s, I a ≤ K) : ∑ a ∈ s, I a ≤ K :=
  Finset.sum_induction I (· ≤ K) (fun _ _ h₁ h₂ => by
    rw [Submodule.add_eq_sup]; exact sup_le h₁ h₂) bot_le h

private theorem le_sum_of_mem_finset {A : Type*} [CommRing A]
    {ι : Type*} {s : Finset ι} (I : ι → Ideal A) {a : ι}
    (ha : a ∈ s) : I a ≤ ∑ b ∈ s, I b := by
  classical
  rw [← Finset.add_sum_erase s I ha, Submodule.add_eq_sup]
  exact le_sup_left

/-- `(P ⊔ Y)ᵏ ⊆ Σ_{a ≤ k} Pᵃ Yᵏ⁻ᵃ`. -/
private theorem sup_pow_le_sum_pow_mul {A : Type*} [CommRing A] (P Y : Ideal A) (k : ℕ) :
    (P ⊔ Y) ^ k ≤ ∑ a ∈ Finset.Icc 0 k, P ^ a * Y ^ (k - a) := by
  rw [← Submodule.add_eq_sup, add_pow]
  refine sum_le_of_forall_le _ _ fun a ha =>
    Ideal.mul_le_left.trans (le_sum_of_mem_finset (fun a => P ^ a * Y ^ (k - a)) ?_)
  simp only [Finset.mem_range] at ha
  simp only [Finset.mem_Icc]
  omega

private theorem mul_pow_le_pow_of_le {A : Type*} [CommRing A]
    {P Y Q : Ideal A} (hP : P ≤ Q) (hY : Y ≤ Q) (a b : ℕ) :
    P ^ a * Y ^ b ≤ Q ^ (a + b) := by
  rw [pow_add]
  exact Ideal.mul_mono (Ideal.pow_right_mono hP a) (Ideal.pow_right_mono hY b)

/-- **The bidegree argument behind "we must have `h_j ∈ P^{ν_i-ν_j}`"** (Lemma 9, p. 219; the paper
does not argue it). -/
private theorem exists_mem_pow_of_sub_mem_pow_succ {A : Type*} [CommRing A] (P Y Q : Ideal A)
    (hQ : Q = P ⊔ Y)
    (hind : ∀ (m : ℕ) (s : Finset ℕ), (∀ a ∈ s, a ≤ m) → ∀ u : ℕ → A,
      (∀ a ∈ s, u a ∈ P ^ a * Y ^ (m - a)) → ∑ a ∈ s, u a ∈ Q ^ (m + 1) →
      ∀ a ∈ s, u a ∈ Q * (P ^ a * Y ^ (m - a)))
    {ι : Type*} [Fintype ι] (f : ι → A) (d : ι → ℕ) (hf : ∀ j, f j ∈ P ^ d j)
    {n : ℕ} {g : A} (hg : g ∈ P ^ n) (c : ι → A) (hc : ∀ j, d j ≤ n → c j ∈ Q ^ (n - d j))
    (hc0 : ∀ j, n < d j → c j = 0) (hgc : g - ∑ j, c j * f j ∈ Q ^ (n + 1)) :
    ∃ h : ι → A, (∀ j, d j ≤ n → h j ∈ P ^ (n - d j)) ∧
      g - ∑ j, h j * f j ∈ Q ^ (n + 1) := by
  classical
  have hPQ : P ≤ Q := hQ ▸ le_sup_left
  have hYQ : Y ≤ Q := hQ ▸ le_sup_right
  -- the bidegree decomposition `c_j = Σ_a w_{j,a}`, `w_{j,a} ∈ P^a Y^{n-d_j-a}`
  have hw : ∀ j, ∃ w : ℕ → A, d j ≤ n →
      (∀ a ∈ Finset.Icc 0 (n - d j), w a ∈ P ^ a * Y ^ (n - d j - a)) ∧
        ∑ a ∈ Finset.Icc 0 (n - d j), w a = c j := by
    intro j
    by_cases hj : d j ≤ n
    · obtain ⟨w, hw, hwc⟩ := exists_eq_sum_of_mem_finset_sum _ _
        (sup_pow_le_sum_pow_mul P Y _ (hQ ▸ hc j hj))
      exact ⟨w, fun _ => ⟨hw, hwc⟩⟩
    · exact ⟨0, fun h => absurd h hj⟩
  choose w hw using hw
  -- the part of bidegree `(b, n - b)` of `Σ_j c_j f_j`
  set U : ℕ → A := fun b => ∑ j, if d j ≤ b then w j (b - d j) * f j else 0 with hU
  have hUmem : ∀ b ≤ n, U b ∈ P ^ b * Y ^ (n - b) := by
    intro b hb
    refine Ideal.sum_mem _ fun j _ => ?_
    by_cases hjb : d j ≤ b
    · simp only [hjb, ↓reduceIte]
      have hjn : d j ≤ n := hjb.trans hb
      have h1 := (hw j hjn).1 (b - d j) (Finset.mem_Icc.mpr ⟨Nat.zero_le _, by omega⟩)
      have h2 := Ideal.mul_mem_mul h1 (hf j)
      have e : P ^ (b - d j) * Y ^ (n - d j - (b - d j)) * P ^ d j = P ^ b * Y ^ (n - b) := by
        rw [show n - d j - (b - d j) = n - b by omega]
        rw [mul_right_comm, ← pow_add, Nat.sub_add_cancel hjb]
      rwa [e] at h2
    · simp only [hjb, ↓reduceIte]
      exact zero_mem _
  have hUsum : ∑ b ∈ Finset.range (n + 1), U b = ∑ j, c j * f j := by
    simp only [hU]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    by_cases hj : d j ≤ n
    · rw [← (hw j hj).2, Finset.sum_mul, ← Finset.sum_filter]
      have : (Finset.range (n + 1)).filter (fun b => d j ≤ b) = Finset.Ico (d j) (n + 1) := by
        ext b
        simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
        omega
      rw [this, Finset.sum_Ico_eq_sum_range]
      have h2 : Finset.Icc 0 (n - d j) = Finset.range (n + 1 - d j) := by
        ext a
        simp only [Finset.mem_Icc, Finset.mem_range]
        omega
      rw [h2]
      exact Finset.sum_congr rfl fun a _ => by rw [Nat.add_sub_cancel_left]
    · have hjn : n < d j := not_le.mp hj
      rw [hc0 j hjn, zero_mul]
      refine Finset.sum_eq_zero fun b hb => ?_
      have : b < n + 1 := Finset.mem_range.mp hb
      simp only [show ¬ d j ≤ b by omega, ↓reduceIte]
  refine ⟨fun j => if d j ≤ n then w j (n - d j) else 0, fun j hj => ?_, ?_⟩
  · simp only [hj, ↓reduceIte]
    have := (hw j hj).1 (n - d j) (Finset.mem_Icc.mpr ⟨Nat.zero_le _, le_rfl⟩)
    rw [Nat.sub_self, pow_zero, Ideal.one_eq_top, Ideal.mul_top] at this
    exact this
  · have hUn : U n = ∑ j, (if d j ≤ n then w j (n - d j) else 0) * f j := by
      simp only [hU]
      refine Finset.sum_congr rfl fun j _ => ?_
      split_ifs <;> simp
    set u : ℕ → A := fun b => if b = n then g - U n else - U b with hu
    have hunmem : u n ∈ Q * (P ^ n * Y ^ (n - n)) := by
      refine hind n (Finset.range (n + 1)) (fun a ha => Nat.le_of_lt_succ (Finset.mem_range.mp ha))
        u (fun b hb => ?_) ?_ n (Finset.mem_range.mpr n.lt_succ_self)
      · have hbn : b ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hb)
        by_cases hbe : b = n
        · subst hbe
          simp only [hu, ↓reduceIte]
          refine sub_mem ?_ (hUmem b le_rfl)
          rw [Nat.sub_self, pow_zero, Ideal.one_eq_top, Ideal.mul_top]
          exact hg
        · simp only [hu, hbe, ↓reduceIte]
          exact neg_mem (hUmem b hbn)
      · have hsum : ∑ b ∈ Finset.range (n + 1), u b =
            g - ∑ b ∈ Finset.range (n + 1), U b := by
          rw [Finset.sum_range_succ, Finset.sum_range_succ,
            Finset.sum_congr rfl (g := fun b => - U b) (fun b hb => by
              simp only [hu, ne_of_lt (Finset.mem_range.mp hb), ↓reduceIte]),
            Finset.sum_neg_distrib]
          simp only [hu, ↓reduceIte]
          ring
        rw [hsum, hUsum]
        exact hgc
    have hle : Q * (P ^ n * Y ^ (n - n)) ≤ Q ^ (n + 1) := by
      rw [pow_succ']
      refine Ideal.mul_mono_right ?_
      exact (mul_pow_le_pow_of_le hPQ hYQ n (n - n)).trans
        (le_of_eq (by rw [Nat.sub_self, add_zero]))
    have := hle hunmem
    simp only [hu, ↓reduceIte] at this
    rwa [hUn] at this

/-- `x ∈ Pᵐ/Pᵐ⁺¹` is the class of an element of `D m ∩ Pᵐ`. -/
private def InFamily {A : Type u} [CommRing A] (P : Ideal A) (D : ℕ → Ideal A) (m : ℕ)
    (x : GrPiece P m) : Prop :=
  ∃ a ∈ D m, ∃ ha : a ∈ P ^ m, Submodule.Quotient.mk ⟨a, ha⟩ = x

section GrBound

variable {A : Type u} [CommRing A] (P : Ideal A) (D : ℕ → Ideal A)

private theorem inFamily_zero (m : ℕ) : InFamily P D m 0 :=
  ⟨0, zero_mem _, zero_mem _, (Submodule.Quotient.mk_eq_zero _).mpr (zero_mem _)⟩

private theorem inFamily_add {m : ℕ} {x y : GrPiece P m} (hx : InFamily P D m x)
    (hy : InFamily P D m y) : InFamily P D m (x + y) := by
  obtain ⟨a, haD, ha, rfl⟩ := hx
  obtain ⟨b, hbD, hb, rfl⟩ := hy
  exact ⟨a + b, add_mem haD hbD, add_mem ha hb, by rw [← Submodule.Quotient.mk_add]; rfl⟩

private theorem inFamily_sum {m : ℕ} {ι : Type*} (s : Finset ι) (f : ι → GrPiece P m)
    (h : ∀ i ∈ s, InFamily P D m (f i)) : InFamily P D m (∑ i ∈ s, f i) :=
  Finset.sum_induction f (InFamily P D m) (fun _ _ => inFamily_add P D) (inFamily_zero P D m) h

open Polynomial in
/-- The key computation of `inJ_grProj_mk_mul` (`Hironaka/Compat/Graded.lean`) with the ideal `J`
replaced by a family `D` of ideals with `Pⁱ D_k ⊆ D_{i+k}`. -/
private theorem inFamily_grProj_mk_mul (hD : ∀ i k, P ^ i * D k ≤ D (i + k)) {i : ℕ} (b : A)
    (hb : b ∈ P ^ i) (ψ : AssocGraded P) (hψ : ∀ m, InFamily P D m (grProj P m ψ)) (m : ℕ) :
    InFamily P D m (grProj P m (AssocGraded.mk P i b hb * ψ)) := by
  obtain ⟨p, hp⟩ := Ideal.Quotient.mk_surjective ψ
  have key : grProj P m (AssocGraded.mk P i b hb * ψ) = Submodule.Quotient.mk
      (reesCoeff P m (⟨monomial i b, reesAlgebra.monomial_mem.mpr hb⟩ * p)) := by
    rw [← hp]
    rfl
  rw [key]
  by_cases him : i ≤ m
  · obtain ⟨a, haD, ha, hmk⟩ := hψ (m - i)
    rw [← hp, grProj_mk, Submodule.Quotient.eq] at hmk
    have hmk' : a - (p : A[X]).coeff (m - i) ∈ P ^ (m - i + 1) := hmk
    refine ⟨b * a, ?_, ?_, ?_⟩
    · have := hD i (m - i) (Ideal.mul_mem_mul hb haD)
      rwa [Nat.add_sub_cancel' him] at this
    · have : P ^ i * P ^ (m - i) = P ^ m := by rw [← pow_add, Nat.add_sub_cancel' him]
      rw [← this]
      exact Ideal.mul_mem_mul hb ha
    · rw [Submodule.Quotient.eq]
      show b * a - (monomial i b * (p : A[X])).coeff m ∈ P ^ (m + 1)
      rw [← C_mul_X_pow_eq_monomial, mul_assoc, coeff_C_mul, coeff_X_pow_mul', ite_eq_left him,
        ← mul_sub]
      have : P ^ i * P ^ (m - i + 1) = P ^ (m + 1) := by
        rw [← pow_add]
        congr 1
        omega
      rw [← this]
      exact Ideal.mul_mem_mul hb hmk'
  · refine ⟨0, zero_mem _, zero_mem _, ?_⟩
    rw [Submodule.Quotient.eq]
    show 0 - (monomial i b * (p : A[X])).coeff m ∈ P ^ (m + 1)
    rw [← C_mul_X_pow_eq_monomial, mul_assoc, coeff_C_mul, coeff_X_pow_mul', ite_eq_right him]
    simp

/-- The ideal of `gr_P(A)` of those elements all of whose homogeneous components of degree `m`
are classes of elements of `D_m` (`D_m ⊆ A` an ideal with `Pⁱ D_k ⊆ D_{i+k}`); for
`D_m = J ∩ Pᵐ` it is `grIdealBound P J`. -/
private def grBound (hD : ∀ i k, P ^ i * D k ≤ D (i + k)) : Ideal (AssocGraded P) where
  carrier := {ψ | ∀ m, InFamily P D m (grProj P m ψ)}
  zero_mem' := fun m => by rw [map_zero]; exact inFamily_zero P D m
  add_mem' := fun {x y} hx hy m => by rw [map_add]; exact inFamily_add P D (hx m) (hy m)
  smul_mem' := fun c ψ hψ m => by
    rw [smul_eq_mul]
    obtain ⟨p, hp⟩ := Ideal.Quotient.mk_surjective c
    rw [← hp, mk_eq_sum_mk, Finset.sum_mul, map_sum]
    exact inFamily_sum P D _ _ fun i _ => inFamily_grProj_mk_mul P D hD _ _ ψ hψ m

variable (hD : ∀ i k, P ^ i * D k ≤ D (i + k))

private theorem mk_mem_grBound {d : ℕ} {b : A} (hb : b ∈ P ^ d) (hbD : b ∈ D d) :
    AssocGraded.mk P d b hb ∈ grBound P D hD := by
  intro m
  by_cases hdm : d = m
  · subst hdm
    rw [grProj_mk_same]
    exact ⟨b, hbD, hb, rfl⟩
  · rw [grProj_mk_ne P hdm]
    exact inFamily_zero P D m

/-- If the class of `a ∈ Pᵖ` lies in `grBound P D`, then `a ∈ D_p + Pᵖ⁺¹`. -/
private theorem mem_sup_of_mk_mem_grBound {p : ℕ} {a : A} (ha : a ∈ P ^ p)
    (h : AssocGraded.mk P p a ha ∈ grBound P D hD) : a ∈ D p ⊔ P ^ (p + 1) := by
  obtain ⟨a', ha'D, ha', hclass⟩ := h p
  rw [grProj_mk_same, Submodule.Quotient.eq] at hclass
  have h1 : a' - a ∈ P ^ (p + 1) := hclass
  have : a = a' - (a' - a) := by ring
  rw [this]
  exact sub_mem (Ideal.mem_sup_left ha'D) (Ideal.mem_sup_right h1)

/-- `(Mⁿ gr_P(R)) · gr_P(J, R) ⊆ grBound` for `D_m ⊇ Mⁿ (J ∩ Pᵐ)`: the degree-`m` component of
`r · ψ` (`r ∈ Mⁿ`, `ψ ∈ gr_P(J, R)`) is the class of `r a` with `a ∈ J ∩ Pᵐ`. -/
private theorem map_pow_mul_grIdeal_le_grBound (J M : Ideal A) (n : ℕ)
    (hDM : ∀ m, M ^ n * (J ⊓ P ^ m) ≤ D m) :
    (M ^ n).map (algebraMap A (AssocGraded P)) * grIdeal P J ≤ grBound P D hD := by
  rw [Ideal.mul_le]
  intro r hr s hs
  have hsb := grIdeal_le_bound P J hs
  induction hr using Submodule.span_induction with
  | mem r hr =>
    obtain ⟨x, hx, rfl⟩ := hr
    intro m
    have h1 : grProj P m (algebraMap A (AssocGraded P) x * s) = x • grProj P m s := by
      rw [← Algebra.smul_def]
      exact map_smul (grProjA P m) x s
    rw [h1]
    obtain ⟨a, haJ, ha, hmk⟩ := hsb m
    rw [← hmk, ← Submodule.Quotient.mk_smul]
    exact ⟨x * a, hDM m (Ideal.mul_mem_mul hx ⟨haJ, ha⟩), Ideal.mul_mem_left _ _ ha, rfl⟩
  | zero => simp
  | add x y _ _ hx hy => rw [add_mul]; exact add_mem hx hy
  | smul a x _ hx => rw [smul_eq_mul, mul_assoc]; exact Ideal.mul_mem_left _ _ hx

end GrBound

/-- Krull's intersection theorem in the form used for Nakayama's lemma. -/
private theorem mem_of_forall_mem_sup_pow {R : Type u} [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] (E : Ideal R) {a : R}
    (h : ∀ n : ℕ, a ∈ E ⊔ maximalIdeal R ^ n) : a ∈ E := by
  have hK := Ideal.iInf_pow_smul_eq_bot_of_isLocalRing (maximalIdeal R) (M := R ⧸ E)
    (maximalIdeal.isMaximal R).ne_top
  have hmem : Ideal.Quotient.mk E a ∈ (⨅ i : ℕ, maximalIdeal R ^ i • ⊤ :
      Submodule R (R ⧸ E)) := by
    refine (Submodule.mem_iInf _).mpr fun k => ?_
    obtain ⟨e, he, q, hq, hgeq⟩ := Submodule.mem_sup.mp (h k)
    have h₁ : Ideal.Quotient.mk E a = Ideal.Quotient.mk E q :=
      Ideal.Quotient.eq.mpr (by rw [← hgeq, add_sub_cancel_right]; exact he)
    have h₂ : Ideal.Quotient.mk E q = q • (1 : R ⧸ E) := Algebra.algebraMap_eq_smul_one q
    rw [h₁, h₂]
    exact Submodule.smul_mem_smul hq Submodule.mem_top
  rw [hK] at hmem
  exact Ideal.Quotient.eq_zero_iff_mem.mp ((Submodule.mem_bot R).mp hmem)

open Polynomial in
/-- **Nakayama's lemma for `gr_P(J, R)`** (Lemma 9, p. 219: "`gr_P(J, R) = I + (M')ⁿ gr_P(J, R)` for
all positive integers `n`. Since each homogeneous part of `gr_P(J, R)` is an `R'`-module of finite
type, Nakayama's lemma gives us `gr_P(J, R) = I`"): if `I` is the ideal of `gr_P(R)` generated by
the classes `Φ_j`, `j ∈ T`, and `gr_P(J, R) ⊆ I + (M')ⁿ gr_P(J, R)` for all `n`, then
`gr_P(J, R) ⊆ I`.  Degree by degree, the hypothesis says that a class of `a ∈ J ∩ Pᵖ` lies in
`E_p + Mⁿ(J ∩ Pᵖ) + Pᵖ⁺¹` for all `n` (`E_p` the degree-`p` part of `I`, in `R`), and Krull's
intersection theorem for the finite `R`-module `R/(E_p + Pᵖ⁺¹)` gives that it lies in `E_p + Pᵖ⁺¹`,
i.e. its class lies in `I`. -/
private theorem grIdeal_le_span_of_forall_le {R : Type u} [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] (J P : Ideal R) {m : ℕ} (f : Fin m → R) (ν : Fin m → ℕ)
    (hfP : ∀ j, f j ∈ P ^ ν j) (T : Finset (Fin m))
    (hG : ∀ n : ℕ, grIdeal P J ≤
      Ideal.span ((fun j => AssocGraded.mk P (ν j) (f j) (hfP j)) '' (T : Set (Fin m))) ⊔
        (Ideal.map (algebraMap R (AssocGraded P)) (maximalIdeal R)) ^ n * grIdeal P J) :
    grIdeal P J ≤
      Ideal.span ((fun j => AssocGraded.mk P (ν j) (f j) (hfP j)) '' (T : Set (Fin m))) := by
  classical
  set I := Ideal.span ((fun j => AssocGraded.mk P (ν j) (f j) (hfP j)) '' (T : Set (Fin m)))
    with hI
  set M := maximalIdeal R with hM
  -- `E_p`: the degree-`p` part of `I`, in `R`
  let E : ℕ → Ideal R := fun p =>
    ∑ j ∈ T.filter (fun j => ν j ≤ p), P ^ (p - ν j) * Ideal.span {f j}
  let D : ℕ → ℕ → Ideal R := fun n p => E p ⊔ M ^ n * (J ⊓ P ^ p)
  have hD : ∀ n i k, P ^ i * D n k ≤ D n (i + k) := by
    intro n i k
    simp only [D]
    rw [Ideal.mul_sup]
    refine sup_le_sup ?_ ?_
    · simp only [E]
      rw [Finset.mul_sum]
      refine sum_le_of_forall_le _ _ fun j hj => ?_
      have hjk := (Finset.mem_filter.mp hj)
      refine le_trans ?_ (le_sum_of_mem_finset (fun j => P ^ (i + k - ν j) * Ideal.span {f j})
        (s := T.filter (fun j => ν j ≤ i + k)) (a := j)
        (Finset.mem_filter.mpr ⟨hjk.1, by omega⟩))
      rw [← mul_assoc, ← pow_add, show i + (k - ν j) = i + k - ν j by omega]
    · rw [mul_left_comm]
      refine Ideal.mul_mono_right (le_inf (Ideal.mul_le_right.trans inf_le_left) ?_)
      rw [pow_add]
      exact Ideal.mul_mono_right inf_le_right
  -- the classes of elements of `J ∩ Pᵖ` lie in `I`
  have hhom : ∀ (p : ℕ) (a : R) (ha : a ∈ P ^ p), a ∈ J → AssocGraded.mk P p a ha ∈ I := by
    intro p a ha haJ
    have hmem : ∀ n, a ∈ (E p ⊔ P ^ (p + 1)) ⊔ M ^ n := by
      intro n
      have h2 : I ⊔ (Ideal.map (algebraMap R (AssocGraded P)) M) ^ n * grIdeal P J ≤
          grBound P (D n) (hD n) := by
        refine sup_le ?_ ?_
        · rw [hI, Ideal.span_le]
          rintro _ ⟨j, hj, rfl⟩
          refine mk_mem_grBound P (D n) (hD n) (hfP j) (Ideal.mem_sup_left ?_)
          refine le_sum_of_mem_finset (fun j' => P ^ (ν j - ν j') * Ideal.span {f j'})
            (s := T.filter (fun j' => ν j' ≤ ν j)) (a := j)
            (Finset.mem_filter.mpr ⟨hj, le_rfl⟩) ?_
          rw [Nat.sub_self, pow_zero, Ideal.one_eq_top]
          have := Ideal.mul_mem_mul (show (1 : R) ∈ (⊤ : Ideal R) from Submodule.mem_top)
            (Ideal.mem_span_singleton_self (f j))
          rwa [one_mul] at this
        · rw [← Ideal.map_pow]
          exact map_pow_mul_grIdeal_le_grBound P (D n) (hD n) J M n (fun m => le_sup_right)
      have h3 := mem_sup_of_mk_mem_grBound P (D n) (hD n) ha (h2 (hG n (mk_mem_grIdeal P haJ ha)))
      have hle : D n p ⊔ P ^ (p + 1) ≤ (E p ⊔ P ^ (p + 1)) ⊔ M ^ n := by
        refine sup_le (sup_le (le_sup_of_le_left le_sup_left) ?_) (le_sup_of_le_left le_sup_right)
        exact Ideal.mul_le_left.trans le_sup_right
      exact hle h3
    have h4 := mem_of_forall_mem_sup_pow (E p ⊔ P ^ (p + 1)) hmem
    obtain ⟨e, he, b, hb, hab⟩ := Submodule.mem_sup.mp h4
    obtain ⟨u, hu, rfl⟩ := exists_eq_sum_of_mem_finset_sum _ _ he
    have hc : ∀ j ∈ T.filter (fun j => ν j ≤ p), ∃ c ∈ P ^ (p - ν j), c * f j = u j := fun j hj =>
      Ideal.mem_mul_span_singleton.mp (hu j hj)
    choose! c hcP hcu using hc
    have hsum : a - ∑ j ∈ T.filter (fun j => ν j ≤ p), c j * f j ∈ P ^ (p + 1) := by
      rw [Finset.sum_congr rfl hcu, ← hab]
      simpa using hb
    refine Ideal.span_mono (Set.image_mono ?_)
      (mk_mem_span_of_sub_mem_pow P f ν hfP ha (T.filter (fun j => ν j ≤ p)) c
        (fun j hj => ⟨(Finset.mem_filter.mp hj).2, hcP j hj⟩) hsum)
    intro j hj
    exact (Finset.mem_filter.mp hj).1
  -- the homogeneous components of an element of `gr_P(J, R)` are classes of elements of `J`
  intro Ψ hΨ
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective Ψ
  rw [mk_eq_sum_mk]
  refine Ideal.sum_mem _ fun i _ => ?_
  have hci : (p : Polynomial R).coeff i ∈ P ^ i := (mem_reesAlgebra_iff P p).mp p.2 i
  have hproj : grProj P i (Ideal.Quotient.mk _ p) =
      Submodule.Quotient.mk ⟨(p : Polynomial R).coeff i, hci⟩ := grProj_mk P i p
  obtain ⟨a, haJ, haP, ha⟩ := grIdeal_le_bound P J hΨ i
  rw [hproj, Submodule.Quotient.eq] at ha
  have ha₁ : a - (p : Polynomial R).coeff i ∈ P ^ (i + 1) := ha
  have heq : AssocGraded.mk P i ((p : Polynomial R).coeff i) hci = AssocGraded.mk P i a haP := by
    refine mk_eq_mk_of_sub_mem_pow_succ P hci haP ?_
    rw [show (p : Polynomial R).coeff i - a = -(a - (p : Polynomial R).coeff i) by ring]
    exact neg_mem ha₁
  rw [heq]
  exact hhom i a haP haJ

/-- The class in `grᵈ_P(A)` of an element of `I Pᵈ` lies in `I gr_P(A)` (copy of a private lemma of
`Hironaka/Ch2/GradedIdeal.lean`). -/
private theorem mk_mem_map_of_mem_mul {A : Type u} [CommRing A]
    (P I : Ideal A) {d : ℕ} {c : A} (hc : c ∈ I * P ^ d)
    (hcd : c ∈ P ^ d) : AssocGraded.mk P d c hcd ∈ I.map (algebraMap A (AssocGraded P)) := by
  suffices H : c ∈ P ^ d ∧ ∀ hcd : c ∈ P ^ d,
      AssocGraded.mk P d c hcd ∈ I.map (algebraMap A (AssocGraded P)) from H.2 hcd
  refine Submodule.mul_induction_on hc (fun r hr p hp => ⟨Ideal.mul_mem_left _ r hp, fun h => ?_⟩)
    (fun x y hx hy => ⟨add_mem hx.1 hy.1, fun h => ?_⟩)
  · have : AssocGraded.mk P d (r * p) h =
        algebraMap A (AssocGraded P) r * AssocGraded.mk P d p hp := by
      rw [← Algebra.smul_def]
      show AssocGraded.mkLinear P d ⟨r * p, h⟩ = r • AssocGraded.mkLinear P d ⟨p, hp⟩
      rw [← map_smul]
      rfl
    rw [this]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ hr)
  · rw [AssocGraded.mk_add P d x y hx.1 hy.1]
    exact add_mem (hx.2 hx.1) (hy.2 hy.1)

end Lemma9Aux

/-- Lemma 9 with `R_P` replaced by any regular local ring `S` receiving `R` by a homomorphism `ι`
with `ι⁻¹(M_Sⁿ) = Pⁿ` for all `n` (for `S = R_P` this is `PⁿR_P ∩ R = Pⁿ`, the opening facts of
p. 217).  The proof is that of Lemma 9, which only uses this property of `R → R_P`. -/
private theorem isStandardBase_of_map (R : Type u) [CommRing R] [IsRegularLocalRing R]
    (J P : Ideal R) [P.IsPrime] (hJP : J ≤ P) [IsRegularLocalRing (R ⧸ P)]
    {S : Type u} [CommRing S] [IsRegularLocalRing S] (ι : R →+* S)
    (hι : ∀ (n : ℕ) (x : R), ι x ∈ maximalIdeal S ^ n ↔ x ∈ P ^ n)
    (hflat : IsNormallyFlatAlongIdeal (P.map (Ideal.Quotient.mk J)))
    {m : ℕ} (f : Fin m → R) (hf : ∀ j, f j ∈ J)
    (h₁ : IsStandardBase S (J.map ι) fun j => ι (f j))
    (h₂ : Ideal.span (Set.range fun j => initialForm P (f j)) = grIdeal P J) :
    IsStandardBase R J f ∧ ∀ j, Ideal.ordElem (maximalIdeal R) (f j) = Ideal.ordElem P (f j) := by
  classical
  set F : Fin m → S := fun j => ι (f j)
    with hFdef
  -- orders are preserved by `ι`
  have hord : ∀ g : R, Ideal.ordElem (maximalIdeal (S))
      (ι g) = Ideal.ordElem P g := by
    intro g
    have hmem : ∀ n : ℕ, ι g ∈
        maximalIdeal (S) ^ n ↔ g ∈ P ^ n := fun n => hι n g
    simp only [Ideal.ordElem, hmem]
  obtain ⟨-, hgrL, ⟨dL, hdL, hmonoL⟩, -, hirrL⟩ := h₁
  -- the local initial forms are non-zero, so the `ν_j = ν_P(f_j)` are finite
  have hne : ∀ j, initialForm (maximalIdeal (S)) (F j) ≠ 0 := by
    intro j h0
    apply hirrL j
    dsimp only
    rw [h0]
    exact zero_mem _
  have hfin : ∀ j, Ideal.ordElem P (f j) ≠ ⊤ := by
    intro j htop
    apply hne j
    rw [initialForm, dite_eq_left (by rw [hFdef, hord]; exact htop)]
  let ν : Fin m → ℕ := fun j => (Ideal.ordElem P (f j)).toNat
  have hν : ∀ j, Ideal.ordElem P (f j) = ν j := fun j => (ENat.natCast_toNat (hfin j)).symm
  have hfP : ∀ j, f j ∈ P ^ ν j := fun j => Ideal.mem_pow_of_ordElem (hν j)
  have hFm : ∀ j, F j ∈ maximalIdeal (S) ^ ν j := fun j =>
    Ideal.mem_pow_of_ordElem ((hord _).trans (hν j))
  have hφL : ∀ j, initialForm (maximalIdeal (S)) (F j) =
      AssocGraded.mk (maximalIdeal (S)) (ν j) (F j) (hFm j) := fun j =>
    initialForm_eq_mk _ ((hord _).trans (hν j))
  have hdν : ∀ j, dL j = ν j := fun j =>
    eq_of_mem_homogeneous _ (hdL j) (by
      dsimp only
      rw [hφL j]
      exact AssocGraded.mk_mem_homogeneous _ (hFm j)) (hne j)
  have hmono : Monotone ν := fun i j hij => by
    have := hmonoL hij
    rwa [hdν, hdν] at this
  -- the classes `φ_j` of the `f_j` in `gr^{ν_j}_M(R)`
  set M := maximalIdeal R with hMdef
  have hPM : P ≤ M := le_maximalIdeal_of_isPrime P
  have hfM : ∀ j, f j ∈ M ^ ν j := fun j => Ideal.pow_right_mono hPM _ (hfP j)
  let φ : Fin m → AssocGraded M := fun j => AssocGraded.mk M (ν j) (f j) (hfM j)
  have hgrP : grIdeal P J =
      Ideal.span (Set.range fun j => AssocGraded.mk P (ν j) (f j) (hfP j)) := by
    rw [← h₂]
    congr 1
    ext y
    simp only [Set.mem_range]
    exact exists_congr fun j => by rw [initialForm_eq_mk P (hν j)]
  have hRM : IsRegularLocalRing (R ⧸ M) := by
    let _ := Ideal.Quotient.field M
    infer_instance
  -- (a) `gr_M(J, R) = (φ₁, …, φ_m)`, by Theorem 2 of Ch. II and the graded step
  have ha : grIdeal M J = Ideal.span (Set.range φ) := by
    apply le_antisymm
    · obtain ⟨n', g, hgJ, hgord, hgspan⟩ :=
        ((isNormallyFlatAlongIdeal_tfae_of_eq_maximalIdeal J P M hJP rfl).out 1 2).mp hflat
      rw [← hgspan, Ideal.span_le]
      rintro _ ⟨k, rfl⟩
      show initialForm M (g k) ∈ Ideal.span (Set.range φ)
      by_cases htop : Ideal.ordElem M (g k) = ⊤
      · rw [initialForm, dite_eq_left htop]
        exact zero_mem _
      obtain ⟨e, he⟩ := ENat.ne_top_iff_exists.mp htop
      have hgP : g k ∈ P ^ e := Ideal.mem_pow_of_ordElem ((hgord k).symm.trans he.symm)
      have hgM : g k ∈ M ^ e := Ideal.mem_pow_of_ordElem he.symm
      rw [initialForm_eq_mk M he.symm]
      have hmemP : AssocGraded.mk P e (g k) hgP ∈
          Ideal.span (Set.range fun j => AssocGraded.mk P (ν j) (f j) (hfP j)) := by
        rw [← hgrP]
        exact mk_mem_grIdeal P (hgJ k) hgP
      obtain ⟨c, hc, hc0, hcg⟩ := exists_sub_mem_pow_of_mk_mem_span P f ν hfP hgP hmemP
      refine Ideal.span_mono (Set.image_subset_range _ _)
        (mk_mem_span_of_sub_mem_pow M f ν hfM hgM (Finset.univ.filter fun j => ν j ≤ e) c
          (fun j hj => ?_) ?_)
      · have hje : ν j ≤ e := by simpa using hj
        exact ⟨hje, Ideal.pow_right_mono hPM _ (hc j hje)⟩
      · have hs : ∑ j ∈ Finset.univ.filter (fun j => ν j ≤ e), c j * f j = ∑ j, c j * f j := by
          rw [Finset.sum_filter]
          refine Finset.sum_congr rfl fun j _ => ?_
          split_ifs with hj
          · rfl
          · rw [hc0 j (not_le.mp hj), zero_mul]
        rw [hs]
        exact Ideal.pow_right_mono hPM _ hcg
    · rw [Ideal.span_le]
      rintro _ ⟨j, rfl⟩
      exact mk_mem_grIdeal M (hf j) (hfM j)
  -- `φ_j = 0` unless `ν_M(f_j) = ν_j`, and then `φ_j` is the initial form of `f_j`
  have hφ0 : ∀ j, Ideal.ordElem M (f j) ≠ ν j → φ j = 0 := by
    intro j hj
    apply (AssocGraded.mk_eq_zero_iff M (hfM j)).mpr
    have h1 : (ν j : ℕ∞) ≤ Ideal.ordElem M (f j) := Ideal.le_ordElem (hfM j)
    have h2 : ((ν j + 1 : ℕ) : ℕ∞) ≤ Ideal.ordElem M (f j) := by
      rw [Nat.cast_add, Nat.cast_one]
      exact Order.add_one_le_of_lt (lt_of_le_of_ne h1 (Ne.symm hj))
    exact Ideal.mem_pow_of_le_ordElem h2
  have hirr' : ∀ k : Fin m, AssocGraded.mk (maximalIdeal (S)) (ν k) (F k)
      (hFm k) ∉ Ideal.span (Set.range fun j : Fin k =>
        AssocGraded.mk (maximalIdeal (S)) (ν (Fin.castLE k.2.le j))
          (F (Fin.castLE k.2.le j)) (hFm _)) := by
    intro k
    have h1 := hirrL k
    simp only [hφL] at h1
    exact h1
  -- (b) `φ_i ∉ (φ_1, …, φ_{i-1})` for `1 ≤ i ≤ m` (p. 219)
  have hb : ∀ i : Fin m, φ i ∉ Ideal.span (Set.range fun j : Fin i => φ (Fin.castLE i.2.le j)) := by
    by_contra hbad
    push Not at hbad
    -- "Suppose we have `i ≥ 1` such that `φ_i ∈ (φ_1, …, φ_{i-1}) gr_M(R)`.  Let `i` be the
    -- smallest one which has this property"
    obtain ⟨i, hi, hmin⟩ := wellFounded_lt.has_min
      {i : Fin m | φ i ∈ Ideal.span (Set.range fun j : Fin i => φ (Fin.castLE i.2.le j))} hbad
    -- "so that we have `ν_M(f_j) = ν_P(f_j)` for `1 ≤ j ≤ i - 1`"
    have _hjmin : ∀ j : Fin m, j < i → Ideal.ordElem M (f j) = ν j := fun j hj => by
      by_contra h
      refine hmin j ?_ hj
      show φ j ∈ Ideal.span (Set.range fun j' : Fin j => φ (Fin.castLE j.2.le j'))
      rw [hφ0 j h]
      exact zero_mem _
    have hlt : ∀ j : Fin i, (Fin.castLE i.2.le j : Fin m) < i := fun j => by
      rw [Fin.lt_def, Fin.val_castLE]
      exact j.2
    have hνle : ∀ j : Fin i, ν (Fin.castLE i.2.le j) ≤ ν i := fun j => hmono (hlt j).le
    -- the relation `φ_i = Σ_{j<i} λ_j φ_j` of `gr_M(R)` is a congruence `f_i ≡ Σ_{j<i} c_j f_j`
    -- modulo `M^{ν_i+1}`, `c_j ∈ M^{ν_i-ν_j}`
    obtain ⟨c, hc, hc0, hcg⟩ := exists_sub_mem_pow_of_mk_mem_span M
      (fun j : Fin i => f (Fin.castLE i.2.le j)) (fun j : Fin i => ν (Fin.castLE i.2.le j))
      (fun j => hfM _) (hfM i) hi
    -- "In view of this, we must have `h_j ∈ P^{ν_i-ν_j}` (`1 ≤ j ≤ i-1`) such that
    -- `f_i − Σ f_j h_j ∈ M^{ν_i+1}`" (the bidegree argument)
    obtain ⟨κ, ι₀, -, -, y, z, -, hMy, hPz, hind⟩ :=
      exists_sumElim_isQuasiRegular P M hPM inferInstance hRM
    set Y := Ideal.span (Set.range y) with hY
    have hMPY : M = P ⊔ Y := by
      rw [← hMy, Set.Sum.elim_range, Ideal.span_union, hPz, sup_comm]
    obtain ⟨h, hh, hhg⟩ := exists_mem_pow_of_sub_mem_pow_succ P Y M hMPY hind
      (fun j : Fin i => f (Fin.castLE i.2.le j)) (fun j : Fin i => ν (Fin.castLE i.2.le j))
      (fun j => hfP _) (hfP i) c hc hc0 hcg
    have hhP : ∀ j : Fin i, h j ∈ P ^ (ν i - ν (Fin.castLE i.2.le j)) := fun j => hh j (hνle j)
    set x : R := f i - ∑ j : Fin i, h j * f (Fin.castLE i.2.le j) with hx
    have hterm : ∀ j : Fin i, h j * f (Fin.castLE i.2.le j) ∈ P ^ ν i := fun j => by
      have := Ideal.mul_mem_mul (hhP j) (hfP (Fin.castLE i.2.le j))
      rwa [← pow_add, Nat.sub_add_cancel (hνle j)] at this
    have hxP : x ∈ P ^ ν i := sub_mem (hfP i) (sum_mem fun j _ => hterm j)
    have hxJ : x ∈ J := sub_mem (hf i) (sum_mem fun j _ => Ideal.mul_mem_left J _ (hf _))
    -- "This means that, if `Λ_j` is the image of `h_j` in `gr_P^{ν_i-ν_j}(R)`, then
    -- `Φ_i − Σ Λ_j Φ_j ∈ M' gr_P(R)`": the class of `x` is `Φ_i − Σ Λ_j Φ_j`, and
    -- `x ∈ P^{ν_i} ∩ M^{ν_i+1} ⊆ M P^{ν_i}`
    have hΦ : AssocGraded.mk P (ν i) (f i) (hfP i) = AssocGraded.mk P (ν i) x hxP +
        ∑ j : Fin i, AssocGraded.mk P (ν i - ν (Fin.castLE i.2.le j)) (h j) (hhP j) *
          AssocGraded.mk P (ν (Fin.castLE i.2.le j)) (f (Fin.castLE i.2.le j)) (hfP _) := by
      have e1 : ∑ j : Fin i, AssocGraded.mk P (ν i - ν (Fin.castLE i.2.le j)) (h j) (hhP j) *
          AssocGraded.mk P (ν (Fin.castLE i.2.le j)) (f (Fin.castLE i.2.le j)) (hfP _) =
          AssocGraded.mk P (ν i) (∑ j : Fin i, h j * f (Fin.castLE i.2.le j))
            (sum_mem fun j _ => hterm j) := by
        rw [mk_finset_sum P (ν i) Finset.univ (fun j : Fin i => h j * f (Fin.castLE i.2.le j))
          hterm]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [AssocGraded.mk_mul_mk]
        exact mk_congr_of_eq P (Nat.sub_add_cancel (hνle j)) rfl _ _
      rw [e1, ← AssocGraded.mk_add P (ν i) x _ hxP (sum_mem fun j _ => hterm j)]
      exact mk_congr_of_eq P rfl (by rw [hx]; ring) _ _
    have hxM : x ∈ M ^ (ν i + 1) := hhg
    have hxMP : x ∈ M * P ^ ν i := by
      have := inf_pow_add_le_mul P M Y hMPY hind (ν i) 1 ⟨hxP, hxM⟩
      rwa [pow_one, mul_comm] at this
    have hxmem : AssocGraded.mk P (ν i) x hxP ∈ M.map (algebraMap R (AssocGraded P)) :=
      mk_mem_map_of_mem_mul P M hxMP hxP
    -- "Since we have `M' gr_P(R) ∩ gr_P(J, R) = M' gr_P(J, R)` by the flatness of `gr_P(O)` over
    -- `O/P`" (Lemma 7 of Ch. II, with `Q = M` and `g_j = f_j` if `ν_M(f_j) = ν_j`, `0` otherwise)
    let cond : Fin m → Prop := fun j => Ideal.ordElem M (f j) = ν j
    let g : Fin m → R := fun j => if cond j then f j else 0
    have hgJ : ∀ j, g j ∈ J := fun j => by
      by_cases h : cond j
      · simp only [g, ite_eq_left h]; exact hf j
      · simp only [g, ite_eq_right h]; exact zero_mem _
    have htop0 : ∀ I : Ideal R, Ideal.ordElem I 0 = ⊤ := fun I =>
      Ideal.ordElem_eq_top_iff.mpr fun n => zero_mem _
    have hgord : ∀ j, Ideal.ordElem M (g j) = Ideal.ordElem P (g j) := fun j => by
      by_cases h : cond j
      · simp only [g, ite_eq_left h]; rw [h, hν]
      · simp only [g, ite_eq_right h]; rw [htop0, htop0]
    have hinitg : ∀ j, cond j → initialForm M (g j) = φ j := fun j h => by
      simp only [g, ite_eq_left h]
      exact initialForm_eq_mk M h
    have hφmem : ∀ j, φ j ∈ Ideal.span (Set.range fun j => initialForm M (g j)) := by
      intro j
      by_cases h : cond j
      · rw [← hinitg j h]
        exact Ideal.subset_span ⟨j, rfl⟩
      · rw [hφ0 j h]
        exact zero_mem _
    have hspanM : Ideal.span (Set.range fun j => initialForm M (g j)) = grIdeal M J := by
      apply le_antisymm
      · rw [Ideal.span_le]
        rintro _ ⟨j, rfl⟩
        exact Ideal.subset_span ⟨g j, hgJ j, rfl⟩
      · rw [ha, Ideal.span_le]
        rintro _ ⟨j, rfl⟩
        exact hφmem j
    have h7 := inf_grIdeal_eq_mul_span_initialForm J P M hJP hPM g hgJ hgord hspanM
    have hB4 : (M.map (algebraMap R (AssocGraded P))) ⊓ grIdeal P J =
        (M.map (algebraMap R (AssocGraded P))) * grIdeal P J := by
      have h1 := h7.1 1
      simp only [pow_one] at h1
      rw [h1, ← h7.2]
    have hxmem' : AssocGraded.mk P (ν i) x hxP ∈
        (M.map (algebraMap R (AssocGraded P))) * grIdeal P J := by
      rw [← hB4]
      exact ⟨hxmem, mk_mem_grIdeal P hxJ hxP⟩
    -- "Hence, if `I` denotes the ideal `(Φ_1, …, Φ_{i-1}, Φ_{i+1}, …, Φ_m) gr_P(R)`, then
    -- `gr_P(J, R) = I + M' gr_P(J, R)`"
    set T : Finset (Fin m) := Finset.univ.filter (· ≠ i) with hT
    set I' : Ideal (AssocGraded P) := Ideal.span
      ((fun j => AssocGraded.mk P (ν j) (f j) (hfP j)) '' (T : Set (Fin m))) with hI'
    have hB5 : grIdeal P J = I' ⊔ (M.map (algebraMap R (AssocGraded P))) * grIdeal P J := by
      apply le_antisymm
      · conv_lhs => rw [hgrP]
        rw [Ideal.span_le]
        rintro _ ⟨j, rfl⟩
        by_cases hji : j = i
        · have hjΦ : AssocGraded.mk P (ν j) (f j) (hfP j) =
              AssocGraded.mk P (ν i) (f i) (hfP i) := by
            subst hji
            rfl
          show AssocGraded.mk P (ν j) (f j) (hfP j) ∈ _
          rw [hjΦ, hΦ]
          refine add_mem (Ideal.mem_sup_right hxmem') (Ideal.mem_sup_left (sum_mem fun j' _ => ?_))
          refine Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨Fin.castLE i.2.le j', ?_, rfl⟩)
          simp [hT, (hlt j').ne]
        · refine Ideal.mem_sup_left (Ideal.subset_span ⟨j, ?_, rfl⟩)
          simp [hT, hji]
      · refine sup_le (Ideal.span_le.mpr ?_) Ideal.mul_le_right
        rintro _ ⟨j, -, rfl⟩
        exact mk_mem_grIdeal P (hf j) (hfP j)
    -- "It follows immediately that `gr_P(J, R) = I + (M')ⁿ gr_P(J, R)` for all positive integers
    -- `n`"
    have hB6 : ∀ n : ℕ, grIdeal P J ≤
        I' ⊔ (M.map (algebraMap R (AssocGraded P))) ^ n * grIdeal P J := by
      intro n
      induction n with
      | zero => simp
      | succ n ih =>
        calc grIdeal P J ≤ I' ⊔ (M.map (algebraMap R (AssocGraded P))) * grIdeal P J := hB5.le
          _ ≤ I' ⊔ (M.map (algebraMap R (AssocGraded P))) * (I' ⊔
              (M.map (algebraMap R (AssocGraded P))) ^ n * grIdeal P J) :=
            sup_le_sup_left (Ideal.mul_mono_right ih) _
          _ ≤ I' ⊔ (M.map (algebraMap R (AssocGraded P))) ^ (n + 1) * grIdeal P J := by
            rw [Ideal.mul_sup, ← mul_assoc, ← pow_succ']
            exact sup_le le_sup_left (sup_le (Ideal.mul_le_right.trans le_sup_left) le_sup_right)
    -- "Since each homogeneous part of `gr_P(J, R)` is an `R'`-module of finite type, Nakayama's
    -- lemma gives us `gr_P(J, R) = I`."
    have hB7 : grIdeal P J ≤ I' :=
      grIdeal_le_span_of_forall_le J P f ν hfP T hB6
    -- "However, this contradicts the assumption (i)": `Φ_i ∈ (Φ_j : j ≠ i)`
    have hΦi : AssocGraded.mk P (ν i) (f i) (hfP i) ∈ I' := hB7 (mk_mem_grIdeal P (hf i) (hfP i))
    let g' : Fin m → R := fun j => if j = i then 0 else f j
    have hg'P : ∀ j, g' j ∈ P ^ ν j := fun j => by
      by_cases hji : j = i
      · simp only [g', ite_eq_left hji]; exact zero_mem _
      · simp only [g', ite_eq_right hji]; exact hfP j
    have hΦi' : AssocGraded.mk P (ν i) (f i) (hfP i) ∈
        Ideal.span (Set.range fun j => AssocGraded.mk P (ν j) (g' j) (hg'P j)) := by
      refine (Ideal.span_le.mpr ?_) hΦi
      rintro _ ⟨j, hj, rfl⟩
      have hji : j ≠ i := by simpa [hT] using hj
      refine Ideal.subset_span ⟨j, ?_⟩
      exact mk_congr_of_eq P rfl (by simp [g', hji]) _ _
    obtain ⟨c', hc', hc0', hcg'⟩ := exists_sub_mem_pow_of_mk_mem_span P g' ν hg'P (hfP i) hΦi'
    -- pass to `R_P`
    have hmapP : ∀ n (x : R), x ∈ P ^ n → ι x ∈ maximalIdeal (S) ^ n := fun n x hx => (hι n x).mpr hx
    refine false_of_sub_mem_pow F ν hmono hFm hirr' i (fun j => if j = i then 0 else ι (c' j))
      (by simp) (fun j hj => ?_) (fun j hj => ?_) ?_
    · by_cases hji : j = i
      · simp only [ite_eq_left hji]
        exact zero_mem _
      · simp only [ite_eq_right hji]
        exact hmapP _ _ (hc' j hj)
    · by_cases hji : j = i
      · simp only [ite_eq_left hji]
      · simp only [ite_eq_right hji, hc0' j hj, map_zero]
    · have hsum : ∑ j, (if j = i then 0 else ι (c' j)) * F j = ι (∑ j, c' j * g' j) := by
        rw [map_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        by_cases hji : j = i
        · simp only [ite_eq_left hji, g', zero_mul, mul_zero, map_zero]
        · simp only [ite_eq_right hji, g', map_mul, hFdef]
      rw [hsum, hFdef, ← map_sub]
      exact hmapP _ _ hcg'
  -- conclusion
  have hne' : ∀ j, φ j ≠ 0 := fun j h0 => hb j (h0 ▸ zero_mem _)
  have hordM : ∀ j, Ideal.ordElem M (f j) = ν j := fun j => by
    by_contra h
    exact hne' j (hφ0 j h)
  have hinit : (fun j => initialForm M (f j)) = φ := funext fun j => initialForm_eq_mk M (hordM j)
  refine ⟨⟨hf, ?_⟩, fun j => (hordM j).trans (hν j).symm⟩
  rw [hinit]
  refine ⟨fun j => mk_mem_grIdeal M (hf j) (hfM j), ⟨ν, fun j => AssocGraded.mk_mem_homogeneous _ _,
    hmono⟩, ha, hb⟩

/-- Lemma 9, pp. 218–219: "Let `R` be a regular local ring, `J` an ideal in `R`, and `P` a prime
ideal in `R` such that `P ⊇ J` and `R/P` is regular. Let `O = R/J` and `P̄ = P/J`. Assume that
`gr_P̄(O)` is flat over `O/P̄`. If `(f₁, …, f_m)` is a system of elements of `J` such that
(i) `(f₁, …, f_m)` is a standard base of `JR_P`, and
(ii) the initial forms `Φ_j` of `f_j` in `gr_P(R)` (`1 ≤ j ≤ m`) generate the ideal `gr_P(J, R)`,
then `(f₁, …, f_m)` is a standard base of `J`, and if `M` = the maximal ideal of `R`, we have
`ν_M(f_j) = ν_P(f_j)` for `1 ≤ j ≤ m`."

Formalization note (encoding): "`gr_P̄(O)` is flat over `O/P̄`" is `IsNormallyFlatAlongIdeal (P.map (Ideal.Quotient.mk J))`
(`O = R ⧸ J` is a noetherian local ring since `J ⊆ P`, and Definition 1 of Ch. 0 is equivalent to
flatness of `gr_P̄(O)`, `isNormallyFlatAlongIdeal_iff_isGrFlat`); (i) is `IsStandardBase` for the
regular local ring `R_P`, the ideal `JR_P` and the images of the `f_j`; (ii) is
`Ideal.span (range (initialForm P ∘ f)) = grIdeal P J`.

Formalization note (encoding): to speak of a standard base of `JR_P` one needs `R_P` regular
(Serre's theorem on localizations of regular local rings, the cited leaf
`isRegularLocalRing_localization_of_isRegularLocalRing`); here it is the instance hypothesis
`[IsRegularLocalRing (Localization.AtPrime P)]`.  The form without this hypothesis, the declaration
of the blueprint node `lem:III.9`, is `isStandardBase_of_isStandardBase_localization`.

Proof as printed (p. 219): (a) and (b) follow the paper step by step
(`isStandardBase_of_map`, comments quote the text).  Let `i` be the smallest index with
`φ_i ∈ (φ_1, …, φ_{i-1})`; the relation gives `c_j ∈ M^{ν_i-ν_j}` with `f_i − Σ c_j f_j ∈
M^{ν_i+1}`, then `h_j ∈ P^{ν_i-ν_j}` with `f_i − Σ f_j h_j ∈ M^{ν_i+1}`
(`exists_mem_pow_of_sub_mem_pow_succ`), hence `Φ_i − Σ Λ_j Φ_j ∈ M' gr_P(R)`, hence (Lemma 7 of
Ch. II) `∈ M' gr_P(J, R)`, hence `gr_P(J, R) = I + M' gr_P(J, R) = I + (M')ⁿ gr_P(J, R)`, and
Nakayama's lemma (degree by degree, as Krull's intersection theorem:
`grIdeal_le_span_of_forall_le`) gives `gr_P(J, R) = I`, which contradicts (i) (made explicit in
`R_P`, `false_of_sub_mem_pow`).

Gaps in the paper filled: (1) "we must have `h_j ∈ P^{ν_i−ν_j}`" (needs a bidegree argument in
`gr_M(R) = K[Z, Y]`: the independence of the bidegree components of `M^n`);
(2) `Φ_i − Σ Λ_j Φ_j ∈ M' gr_P(R)` (from `P^ν ∩ M^{ν+1} = M P^ν`); (3) the hypotheses of
Lemma 7 for `g_j = f_j` (if `ν_M(f_j) = ν_j`, else `0`), which follow from (a) and "`φ_j ≠ 0` iff
`ν_M(f_j) = ν_j = ν_P(f_j)`"; (4) Nakayama's lemma on the homogeneous parts of `gr_P(J, R)`;
(5) "this contradicts the assumption (i)". -/
theorem isStandardBase_of_localization (R : Type u) [CommRing R] [IsRegularLocalRing R]
    (J P : Ideal R) [P.IsPrime] (hJP : J ≤ P) [IsRegularLocalRing (R ⧸ P)]
    [IsRegularLocalRing (Localization.AtPrime P)]
    (hflat : IsNormallyFlatAlongIdeal (P.map (Ideal.Quotient.mk J)))
    {m : ℕ} (f : Fin m → R) (hf : ∀ j, f j ∈ J)
    (h₁ : IsStandardBase (Localization.AtPrime P) (J.map (algebraMap R (Localization.AtPrime P)))
      fun j => algebraMap R (Localization.AtPrime P) (f j))
    (h₂ : Ideal.span (Set.range fun j => initialForm P (f j)) = grIdeal P J) :
    IsStandardBase R J f ∧ ∀ j, Ideal.ordElem (maximalIdeal R) (f j) = Ideal.ordElem P (f j) := by
  have hsymb := ((order_facts R ⊤ P top_ne_bot).2.2 inferInstance).1
  refine isStandardBase_of_map R J P hJP (algebraMap R (Localization.AtPrime P)) (fun n x => ?_)
    hflat f hf h₁ h₂
  rw [← Localization.AtPrime.map_eq_maximalIdeal, ← Ideal.map_pow, ← Ideal.mem_comap, hsymb]

/-- Lemma 9, pp. 218-219, in the form of the paper (without an instance hypothesis on `R_P`): "(i)
`(f₁, …, f_m)` is a standard base of `JR_P`".  That `R_P` is a regular local ring, which one needs
to speak of a standard base of `JR_P` and which the paper uses tacitly, is Serre's theorem, the cited
leaf `isRegularLocalRing_localization_of_isRegularLocalRing`; it is supplied inside the statement
(`letI`).  The proof is `isStandardBase_of_localization`, the same statement with the instance
hypothesis `[IsRegularLocalRing (Localization.AtPrime P)]`; it is the declaration of the blueprint
node `lem:III.9`. -/
@[blueprint "lem:III.9"
  (statement := /-- Let $R$ be a regular local ring, $J$ an ideal in $R$, and $P$ a prime
    ideal in $R$ such that $P\supseteq J$ and $R/P$ is regular. Let $O=R/J$ and $\bar P=P/J$.
    Assume that $\operatorname{gr}_{\bar P}(O)$ is flat over $O/\bar P$
    (\cref{def:normally-flat-ideal}). If $(f_1,\dots,f_m)$ is a system of elements of $J$
    such that (i) $(f_1,\dots,f_m)$ is a standard base of $JR_P$ (\cref{def:III.3}), and
    (ii) the initial forms $\Phi_j$ of $f_j$ in $\operatorname{gr}_P(R)$ ($1\le j\le m$)
    generate the ideal $\operatorname{gr}_P(J,R)$, then $(f_1,\dots,f_m)$ is a standard base
    of $J$, and if $M$ is the maximal ideal of $R$, we have $\nu_M(f_j)=\nu_P(f_j)$ for
    $1\le j\le m$. (Lemma 9, pp.~218--219.)

    \textbf{Formalization note (encoding).} That $R_P$ is a regular local ring, needed to speak
    of a standard base of $JR_P$ and used tacitly by the paper, is Serre's theorem (the cited
    leaf \texttt{isRegularLocalRing\_localization\_of\_isRegularLocalRing}); it is supplied
    inside the formal statement. -/)
  (proof := /-- Let $R'=R/P=O/\bar P$ and $M'=M/P$. Since $\operatorname{gr}_{\bar P}(O)$ is
    flat over $O/\bar P$, $\operatorname{gr}_M(J,R)$ is generated by the initial forms of
    those $g\in J$ which have the property that $\nu_P(g)=\nu_M(g)$ (\cref{cor:II.2-thm2-1}).
    Take any $g\in J$ with this property. Let $\Psi$ be the initial form of $g$ in
    $\operatorname{gr}_P(R)$. Let $\nu=\deg\Psi=\nu_P(g)=\nu_M(g)$. Then by (ii), if
    $\nu_j=\deg\Phi_j$ ($1\le j\le m$), we have $\Lambda_j\in\operatorname{gr}^{\nu-\nu_j}_P(R)$
    such that $\Psi=\sum_j\Lambda_j\Phi_j$. Let us take $h_j\in P^{\nu-\nu_j}$ such that
    $\Lambda_j$ is the initial form of $h_j$ in $\operatorname{gr}_P(R)$. Then we have
    $g-\sum_jh_jf_j\in P^{\nu+1}$, hence $\in M^{\nu+1}$. Therefore the initial form of $g$
    in $\operatorname{gr}_M(R)$ is equal to that of $\sum_jh_jf_j$ in $\operatorname{gr}_M(R)$,
    which can be written as $\sum_j\lambda_j\varphi_j$ where $\lambda_j$ is the class of $h_j$
    in $\operatorname{gr}^{\nu-\nu_j}_M(R)$ and $\varphi_j$ the class of $f_j$ in
    $\operatorname{gr}^{\nu_j}_M(R)$. Thus we have seen that if $\varphi_j$ is the class of
    $f_j$ in $\operatorname{gr}^{\nu_j}_M(R)$ ($1\le j\le m$) then
    (a) $\operatorname{gr}_M(J,R)=(\varphi_1,\dots,\varphi_m)\operatorname{gr}_M(R)$.
    We note that $\varphi_j\ne0$ if and only if $\nu_M(f_j)=\nu_j=\nu_P(f_j)$. Now we claim
    that: (b) $\varphi_i\notin(\varphi_1,\dots,\varphi_{i-1})\operatorname{gr}_M(R)$ for
    $1\le i\le m$. Suppose we have $i\ge1$ such that
    $\varphi_i\in(\varphi_1,\dots,\varphi_{i-1})\operatorname{gr}_M(R)$. Let $i$ be the
    smallest one which has this property, so that we have $\nu_M(f_j)=\nu_P(f_j)$ for
    $1\le j\le i-1$. In view of this, we must have $h_j\in P^{\nu_i-\nu_j}$ ($1\le j\le i-1$)
    such that $f_i-\sum_jf_jh_j\in M^{\nu_i+1}$. This means that, if $\Lambda_j$ is the image
    of $h_j$ in $\operatorname{gr}^{\nu_i-\nu_j}_P(R)$ ($1\le j\le i-1$), then
    $\Phi_i-\sum_j\Lambda_j\Phi_j\in M'\operatorname{gr}_P(R)$. Since we have
    $M'\operatorname{gr}_P(R)\cap\operatorname{gr}_P(J,R)=M'\operatorname{gr}_P(J,R)$ by the
    flatness of $\operatorname{gr}_{\bar P}(O)$ over $O/\bar P$, we get
    $\Phi_i-\sum_j\Lambda_j\Phi_j\in M'\operatorname{gr}_P(J,R)$ (see, for instance,
    \cref{lem:II.2-7}). Hence, if $I$ denotes the ideal
    $(\Phi_1,\dots,\Phi_{i-1},\Phi_{i+1},\dots,\Phi_m)\operatorname{gr}_P(R)$, then
    $\operatorname{gr}_P(J,R)=I+M'\operatorname{gr}_P(J,R)$. It follows immediately that
    $\operatorname{gr}_P(J,R)=I+(M')^n\operatorname{gr}_P(J,R)$ for all positive integers
    $n$. Since each homogeneous part of $\operatorname{gr}_P(J,R)$ is an $R'$-module of finite
    type, Nakayama's lemma gives us $\operatorname{gr}_P(J,R)=I$. However, this contradicts
    the assumption (i). Thus (b) is established. In particular, $\nu_M(f_j)=\nu_P(f_j)$ for
    all $j$ ($1\le j\le m$), and therefore $\varphi_j$ is the initial form of $f_j$ in
    $\operatorname{gr}_M(R)$. It is clear that $\deg\varphi_j\le\deg\varphi_{j+1}$ for all
    $j$ ($1\le j\le m-1$). By (a) and (b), $(f_1,\dots,f_m)$ is a standard base of $J$.

    \textbf{Gaps in the paper filled.} (1) ``We must have $h_j\in P^{\nu_i-\nu_j}$'' is
    proved by a bidegree argument in $\operatorname{gr}_M(R)=K[Z,Y]$ (independence of the bidegree
    components of $M^n$): the relation $f_i-\sum c_jf_j\in M^{\nu_i+1}$ with
    $c_j\in M^{\nu_i-\nu_j}$ is turned into one with $h_j\in P^{\nu_i-\nu_j}$. (2)
    $\Phi_i-\sum\Lambda_j\Phi_j\in M'\operatorname{gr}_P(R)$ because an element of
    $P^{\nu_i}\cap M^{\nu_i+1}$ lies in $MP^{\nu_i}$. (3) The equality $M'\operatorname{gr}_P(R)\cap
    \operatorname{gr}_P(J,R)=M'\operatorname{gr}_P(J,R)$ is Lemma~7 of Ch.~II applied to
    $g_j=f_j$ if $\nu_M(f_j)=\nu_j$ and $g_j=0$ otherwise: its hypotheses follow from (a) and the
    note that $\varphi_j\ne0$ iff $\nu_M(f_j)=\nu_j$. (4) Nakayama's lemma is applied degree by
    degree, in the form of Krull's intersection theorem for $R/(E_p+P^{p+1})$, $E_p$ the
    degree-$p$ part of $I$. (5) ``This contradicts (i)'' is made explicit: lifting the relation
    to $R_P$ and choosing the largest index with a unit coefficient contradicts property (iii) of
    the standard base of $JR_P$. -/)
  (latexEnv := "lemma")]
theorem isStandardBase_of_isStandardBase_localization [Hironaka.Cited.IsRegularLocalRingLocalizationOfIsRegularLocalRing.{u}] (R : Type u) [CommRing R]
    [IsRegularLocalRing R] (J P : Ideal R) [P.IsPrime] (hJP : J ≤ P) [IsRegularLocalRing (R ⧸ P)]
    (hflat : IsNormallyFlatAlongIdeal (P.map (Ideal.Quotient.mk J)))
    {m : ℕ} (f : Fin m → R) (hf : ∀ j, f j ∈ J)
    (h₁ : letI := isRegularLocalRing_localization_of_isRegularLocalRing R P
      IsStandardBase (Localization.AtPrime P) (J.map (algebraMap R (Localization.AtPrime P)))
        fun j => algebraMap R (Localization.AtPrime P) (f j))
    (h₂ : Ideal.span (Set.range fun j => initialForm P (f j)) = grIdeal P J) :
    IsStandardBase R J f ∧ ∀ j, Ideal.ordElem (maximalIdeal R) (f j) = Ideal.ordElem P (f j) :=
  haveI := isRegularLocalRing_localization_of_isRegularLocalRing R P
  isStandardBase_of_localization R J P hJP hflat f hf h₁ h₂

/-! ### Standard bases: auxiliary facts (copies of private lemmas of Stability/JStability) -/

section StdBase

/-- A non-zero initial form which is homogeneous of degree `d` has `ν_I(a) = d`. -/
private theorem ordElem_eq_of_initialForm_mem_homogeneous {A : Type*} [CommRing A]
    (I : Ideal A) {a : A} {d : ℕ} (hd : initialForm I a ∈ AssocGraded.homogeneous I d)
    (h0 : initialForm I a ≠ 0) : Ideal.ordElem I a = d := by
  by_cases htop : Ideal.ordElem I a = ⊤
  · exact absurd (by rw [initialForm, dite_eq_left htop]) h0
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp htop
  rw [← hn]
  by_contra hnd
  have hnd' : n ≠ d := fun h => hnd (by rw [h])
  apply h0
  obtain ⟨y, hy⟩ := LinearMap.mem_range.mp hd
  have h1 : grProj I d (initialForm I a) = y := by rw [← hy, grProj_ofGrPiece_same]
  have h2 : grProj I d (initialForm I a) = 0 := by
    rw [initialForm_eq_mk I hn.symm, grProj_mk_ne I hnd']
  rw [← hy, ← h1, h2, map_zero]

variable (R : Type u) [CommRing R] [IsRegularLocalRing R]

/-- A system of elements of `J` whose initial forms generate `gr_M(J, R)` contains a standard
base of `J` (with at most as many elements): sort the elements by order and discard those whose
initial form lies in the ideal generated by the initial forms of the preceding ones. -/
private theorem exists_isStandardBase_comp (J : Ideal R) {n : ℕ} (f : Fin n → R)
    (hfJ : ∀ i, f i ∈ J)
    (hgen : Ideal.span (Set.range fun i => initialForm (maximalIdeal R) (f i)) =
      grIdeal (maximalIdeal R) J) :
    ∃ (m : ℕ) (σ : Fin m → Fin n), m ≤ n ∧ IsStandardBase R J (f ∘ σ) := by
  classical
  let e : Fin n → ℕ := fun i => (Ideal.ordElem (maximalIdeal R) (f i)).toNat
  let φ : Fin n → AssocGraded (maximalIdeal R) := fun i => initialForm (maximalIdeal R) (f i)
  let g' := φ ∘ Tuple.sort e
  let e' := e ∘ Tuple.sort e
  have he' : Monotone e' := Tuple.monotone_sort e
  have hspan' : grIdeal (maximalIdeal R) J = Ideal.span (Set.range g') := by
    rw [← hgen, Set.range_comp, (Tuple.sort e).surjective.range_eq, Set.image_univ]
  let S : Finset (Fin n) := Finset.univ.filter fun i =>
    g' i ∉ Ideal.span (Set.range fun j : Fin i => g' (Fin.castLE i.2.le j))
  let emb := S.orderEmbOfFin rfl
  have hS : S.card ≤ n := (Finset.card_le_univ S).trans (Fintype.card_fin n).le
  refine ⟨S.card, fun k => Tuple.sort e (emb k), hS, fun k => hfJ _,
    fun k => Ideal.subset_span ⟨_, hfJ _, rfl⟩,
    ⟨fun k => e' (emb k), fun k => ?_, he'.comp emb.monotone⟩, ?_, ?_⟩
  · show initialForm (maximalIdeal R) (f (Tuple.sort e (emb k))) ∈
      AssocGraded.homogeneous (maximalIdeal R) (e (Tuple.sort e (emb k)))
    by_cases htop : Ideal.ordElem (maximalIdeal R) (f (Tuple.sort e (emb k))) = ⊤
    · rw [initialForm, dite_eq_left htop]
      exact zero_mem _
    · rw [initialForm_eq_mk _ (ENat.natCast_toNat htop).symm]
      exact AssocGraded.mk_mem_homogeneous _ _
  · rw [hspan']
    refine le_antisymm ?_ (Ideal.span_le.mpr ?_)
    · have key : ∀ N : ℕ, ∀ i : Fin n, (i : ℕ) < N →
          g' i ∈ Ideal.span (Set.range fun k => g' (emb k)) := by
        intro N
        induction N with
        | zero => intro i hi; omega
        | succ N ih =>
          intro i hi
          by_cases hiS : i ∈ S
          · have : i ∈ Set.range emb := by rw [Finset.range_orderEmbOfFin]; exact hiS
            obtain ⟨k, rfl⟩ := this
            exact Ideal.subset_span ⟨k, rfl⟩
          · have hmem : g' i ∈
                Ideal.span (Set.range fun j : Fin i => g' (Fin.castLE i.2.le j)) := by
              simpa [S] using hiS
            refine (Ideal.span_le.mpr ?_) hmem
            rintro _ ⟨j, rfl⟩
            exact ih _ (by simp only [Fin.val_castLE]; omega)
      refine Ideal.span_le.mpr ?_
      rintro _ ⟨i, rfl⟩
      exact key n i i.2
    · rintro _ ⟨k, rfl⟩
      exact Ideal.subset_span ⟨_, rfl⟩
  · intro k hk
    have hkS : emb k ∈ S := S.orderEmbOfFin_mem rfl k
    rw [Finset.mem_filter] at hkS
    apply hkS.2
    refine (Ideal.span_mono ?_) hk
    rintro _ ⟨j, rfl⟩
    have hlt : emb (Fin.castLE k.2.le j) < emb k :=
      emb.strictMono (show Fin.castLE k.2.le j < k from Fin.lt_def.mpr (by simp))
    exact ⟨⟨(emb (Fin.castLE k.2.le j) : ℕ), hlt⟩, by simp [g', φ]⟩

/-- For a standard base `(f₁, …, f_m)` of `J`: `ν^{(j)}(J) = ν_M(f_j)` for `1 ≤ j ≤ m`, and
`ν^{(i)}(J) = ∞` for `i > m` (Lemma 1). -/
private theorem nuI_of_isStandardBase (J : Ideal R) {m : ℕ} (f : Fin m → R)
    (hf : IsStandardBase R J f) :
    (∀ j : Fin m, nuI R J ⟨(j : ℕ) + 1, Nat.succ_pos _⟩ =
      Ideal.ordElem (maximalIdeal R) (f j)) ∧
    ∀ i : ℕ+, m < (i : ℕ) → nuI R J i = ⊤ := by
  obtain ⟨-, hJφ, ⟨d, hd, hmono⟩, hspan, hnot⟩ := hf
  obtain ⟨h, h'⟩ := nuI_eq_of_lemma1_properties R J _ hJφ d hd hspan hmono hnot
  refine ⟨fun j => ?_, h'⟩
  have h0 : initialForm (maximalIdeal R) (f j) ≠ 0 := fun h0 => hnot j (by
    dsimp only; rw [h0]; exact zero_mem _)
  rw [h j, ordElem_eq_of_initialForm_mem_homogeneous _ (hd j) h0]

/-- Every ideal of a regular local ring has a standard base (finitely many initial forms generate
`gr_M(J, R)`, since `gr_M(R)` is noetherian). -/
private theorem exists_isStandardBase (J : Ideal R) :
    ∃ (m : ℕ) (f : Fin m → R), IsStandardBase R J f := by
  classical
  have : IsNoetherianRing (AssocGraded (maximalIdeal R)) :=
    inferInstanceAs (IsNoetherianRing (reesAlgebra (maximalIdeal R) ⧸ _))
  obtain ⟨s, hs, hspan⟩ := (Submodule.fg_span_iff_fg_span_finset_subset
    (initialForm (maximalIdeal R) '' (J : Set R))).mp
      (IsNoetherian.noetherian (grIdeal (maximalIdeal R) J))
  choose g hgJ hg using fun x : s => hs x.2
  have hr : (Set.range fun j : Fin s.card =>
      initialForm (maximalIdeal R) (g (s.equivFin.symm j))) = (s : Set _) := by
    ext x
    constructor
    · rintro ⟨j, rfl⟩
      show initialForm (maximalIdeal R) (g (s.equivFin.symm j)) ∈ (s : Set _)
      rw [hg]
      exact (s.equivFin.symm j).2
    · intro hx
      exact ⟨s.equivFin ⟨x, hx⟩, by simp [hg]⟩
  have hgen : Ideal.span (Set.range fun j : Fin s.card =>
      initialForm (maximalIdeal R) (g (s.equivFin.symm j))) = grIdeal (maximalIdeal R) J := by
    rw [hr]
    exact hspan.symm
  obtain ⟨m, σ, -, hσ⟩ := exists_isStandardBase_comp R J
    (fun j : Fin s.card => g (s.equivFin.symm j)) (fun j => hgJ _) hgen
  exact ⟨m, _, hσ⟩

end StdBase

section StdBaseUnit

/-- The initial form of a unit `u` is the image of its class `ū ∈ k = A/M` in `gr_M(A)`. -/
private theorem initialForm_unit {A : Type u} [CommRing A] [IsRegularLocalRing A]
    (u : Aˣ) :
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

/-- Multiplying the members of a standard base by units gives a standard base (the initial
forms change by non-zero constants of `k`). -/
private theorem isStandardBase_of_unit_mul {A : Type u} [CommRing A] [IsRegularLocalRing A]
    (J : Ideal A) {m : ℕ} {f f' : Fin m → A} (hf : IsStandardBase A J f) (u : Fin m → Aˣ)
    (hu : ∀ j, f' j = u j * f j) : IsStandardBase A J f' := by
  have hfwd : ∀ j, initialForm (maximalIdeal A) (f' j) =
      Ideal.Quotient.mk (maximalIdeal A) (u j : A) • initialForm (maximalIdeal A) (f j) :=
    fun j => by
      rw [hu j, initialForm_mul_maximalIdeal, Algebra.smul_def, ← initialForm_unit]
  have hbwd : ∀ j, initialForm (maximalIdeal A) (f j) =
      initialForm (maximalIdeal A) (((u j)⁻¹ : Aˣ) : A) * initialForm (maximalIdeal A) (f' j) :=
    fun j => by
      rw [← initialForm_mul_maximalIdeal, hu j, ← mul_assoc, ← Units.val_mul, inv_mul_cancel,
        Units.val_one, one_mul]
  have hle : ∀ {n : ℕ} (ψ χ : Fin n → AssocGraded (maximalIdeal A)),
      (∀ j, ∃ a, ψ j = a * χ j) → Ideal.span (Set.range ψ) ≤ Ideal.span (Set.range χ) := by
    intro n ψ χ h
    rw [Ideal.span_le]
    rintro _ ⟨j, rfl⟩
    obtain ⟨a, ha⟩ := h j
    rw [SetLike.mem_coe, ha]
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨j, rfl⟩)
  have hfwd' : ∀ j, ∃ a, initialForm (maximalIdeal A) (f' j) =
      a * initialForm (maximalIdeal A) (f j) := fun j =>
    ⟨_, (hfwd j).trans (Algebra.smul_def _ _)⟩
  have hbwd' : ∀ j, ∃ a, initialForm (maximalIdeal A) (f j) =
      a * initialForm (maximalIdeal A) (f' j) := fun j => ⟨_, hbwd j⟩
  obtain ⟨hJ, hin, ⟨d, hd, hmono⟩, hspan, hiii⟩ := hf
  refine ⟨fun j => (hu j) ▸ J.mul_mem_left _ (hJ j), fun j => ?_, ⟨d, fun j => ?_, hmono⟩,
    hspan.trans (le_antisymm (hle _ _ hbwd') (hle _ _ hfwd')), fun i h => hiii i ?_⟩
  · beta_reduce
    rw [hfwd j]
    exact Submodule.smul_of_tower_mem _ _ (hin j)
  · beta_reduce
    rw [hfwd j]
    exact Submodule.smul_mem _ _ (hd j)
  · have h' := hle (fun j : Fin i => initialForm (maximalIdeal A) (f' (Fin.castLE i.2.le j)))
      (fun j : Fin i => initialForm (maximalIdeal A) (f (Fin.castLE i.2.le j)))
      (fun j => hfwd' _) h
    beta_reduce
    rw [hbwd i]
    exact Ideal.mul_mem_left _ _ h'

/-- Two systems which are standard bases, with the same orders, give the same `ν*` (Lemma 1). -/
private theorem nuStar_eq_of_isStandardBase {R R' : Type u} [CommRing R]
    [IsRegularLocalRing R] [CommRing R'] [IsRegularLocalRing R'] (J : Ideal R) (J' : Ideal R')
    {m : ℕ} (f : Fin m → R) (f' : Fin m → R') (hf : IsStandardBase R J f)
    (hf' : IsStandardBase R' J' f')
    (h : ∀ j, Ideal.ordElem (maximalIdeal R) (f j) = Ideal.ordElem (maximalIdeal R') (f' j)) :
    nuStar R J = nuStar R' J' := by
  obtain ⟨hA, hB⟩ := nuI_of_isStandardBase R J f hf
  obtain ⟨hA', hB'⟩ := nuI_of_isStandardBase R' J' f' hf'
  unfold nuStar
  congr 1
  funext i
  by_cases hi : (i : ℕ) ≤ m
  · have hpos := i.pos
    have hij : (⟨((⟨(i : ℕ) - 1, by omega⟩ : Fin m) : ℕ) + 1, Nat.succ_pos _⟩ : ℕ+) = i :=
      PNat.eq (by simp; omega)
    rw [← hij, hA, hA', h]
  · rw [hB i (by omega), hB' i (by omega)]

end StdBaseUnit

/-! Transport of `gr` and of `ν*` along a ring isomorphism `e : A ≅ B`: the canonical map
`gr_N(A) → gr_{NB}(B)` is bijective, preserves degrees, and carries `gr_N(J, A)` onto
`gr_{NB}(JB, B)`; hence `ν*` is invariant.  (The Corollary to Lemma 2,
`nuStar_map_eq_of_mapsRSOP`, would also give this, but through the flatness leaf
`RingHom.MapsRSOP.flat`, which is needless for an isomorphism.) -/

section GrTransport

variable {A B : Type u} [CommRing A] [CommRing B] (e : A ≃+* B) (N : Ideal A)

private theorem mem_map_pow_iff (n : ℕ) (a : A) :
    e a ∈ N.map (e : A →+* B) ^ n ↔ a ∈ N ^ n := by
  rw [← Ideal.map_pow, Ideal.map_comap_of_equiv, Ideal.mem_comap]
  simp

private theorem ordElem_map (a : A) :
    Ideal.ordElem (N.map (e : A →+* B)) (e a) = Ideal.ordElem N a := by
  simp only [Ideal.ordElem, mem_map_pow_iff]

private theorem grMap_initialForm (a : A) :
    AssocGraded.map (e : A →+* B) N (initialForm N a) =
      initialForm (N.map (e : A →+* B)) (e a) := by
  have hord := ordElem_map e N a
  by_cases h : Ideal.ordElem N a = ⊤
  · rw [initialForm, dite_eq_left h, map_zero, initialForm, dite_eq_left (hord.trans h)]
  · obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp h
    rw [initialForm_eq_mk N hn.symm, AssocGraded.map_mk,
      initialForm_eq_mk _ (hord.trans hn.symm)]
    rfl

private theorem grMap_bijective : Function.Bijective (AssocGraded.map (e : A →+* B) N) := by
  constructor
  · refine Ideal.quotientMap_injective' ?_
    intro p hp
    rw [Ideal.mem_comap, mem_map_algebraMap_reesAlgebra_iff] at hp
    rw [mem_map_algebraMap_reesAlgebra_iff]
    intro n
    have := hp n
    rw [reesMap_apply_coe, Polynomial.coeff_map] at this
    exact (mem_map_pow_iff e N (n + 1) _).mp this
  · refine Ideal.quotientMap_surjective ?_
    intro q
    refine ⟨⟨(q : Polynomial B).map (e.symm : B →+* A), (mem_reesAlgebra_iff _ _).mpr fun i => ?_⟩, ?_⟩
    · rw [Polynomial.coeff_map, ← mem_map_pow_iff e N]
      simpa using (mem_reesAlgebra_iff _ _).mp q.2 i
    · apply Subtype.ext
      rw [reesMap_apply_coe, Polynomial.map_map]
      simp

private theorem grMap_mem_homogeneous_iff (n : ℕ) (χ : AssocGraded (N.map (e : A →+* B))) :
    χ ∈ AssocGraded.homogeneous (N.map (e : A →+* B)) n ↔
      ∃ χ₀ ∈ AssocGraded.homogeneous N n, AssocGraded.map (e : A →+* B) N χ₀ = χ := by
  constructor
  · intro hχ
    rw [AssocGraded.homogeneous, LinearMap.mem_range] at hχ
    obtain ⟨y, rfl⟩ := hχ
    induction y using Submodule.Quotient.induction_on with
    | H b =>
      have hb : e.symm b ∈ N ^ n := by
        rw [← mem_map_pow_iff e N]
        simp only [RingEquiv.apply_symm_apply]
        exact b.2
      refine ⟨AssocGraded.mk N n (e.symm b) hb, AssocGraded.mk_mem_homogeneous N hb, ?_⟩
      rw [AssocGraded.map_mk, AssocGraded.ofGrPiece_mk]
      congr 1
      simp
  · rintro ⟨χ₀, hχ₀, rfl⟩
    rw [AssocGraded.homogeneous, LinearMap.mem_range] at hχ₀
    obtain ⟨y, rfl⟩ := hχ₀
    induction y using Submodule.Quotient.induction_on with
    | H a =>
      rw [AssocGraded.ofGrPiece_mk, AssocGraded.map_mk]
      exact AssocGraded.mk_mem_homogeneous _ _

private theorem grMap_grIdeal (I : Ideal A) :
    (grIdeal N I).map (AssocGraded.map (e : A →+* B) N) =
      grIdeal (N.map (e : A →+* B)) (I.map (e : A →+* B)) := by
  rw [grIdeal, grIdeal, Ideal.map_span]
  congr 1
  ext χ
  simp only [Set.mem_image, SetLike.mem_coe]
  constructor
  · rintro ⟨_, ⟨a, ha, rfl⟩, rfl⟩
    exact ⟨e a, Ideal.mem_map_of_mem _ ha, (grMap_initialForm e N a).symm⟩
  · rintro ⟨b, hb, rfl⟩
    rw [Ideal.map_comap_of_equiv, Ideal.mem_comap] at hb
    refine ⟨initialForm N (e.symm b), ⟨e.symm b, hb, rfl⟩, ?_⟩
    rw [grMap_initialForm]
    simp

private theorem exists_nuSystem_map (N' : Ideal B) (hN : N.map (e : A →+* B) = N')
    (I : Ideal A) (ν k : ℕ) (φ : Fin k → AssocGraded N)
    (hφ : (∀ j, φ j ∈ grIdeal N I ∧ ∃ d : ℕ, φ j ∈ AssocGraded.homogeneous N d) ∧
      ∀ μ < ν, ∀ ψ ∈ AssocGraded.homogeneous N μ,
        (ψ ∈ Ideal.span (Set.range φ) ↔ ψ ∈ grIdeal N I)) :
    ∃ φ' : Fin k → AssocGraded N',
      (∀ j, φ' j ∈ grIdeal N' (I.map (e : A →+* B)) ∧
        ∃ d : ℕ, φ' j ∈ AssocGraded.homogeneous N' d) ∧
      ∀ μ < ν, ∀ ψ ∈ AssocGraded.homogeneous N' μ,
        (ψ ∈ Ideal.span (Set.range φ') ↔ ψ ∈ grIdeal N' (I.map (e : A →+* B))) := by
  subst hN
  set σ := AssocGraded.map (e : A →+* B) N
  have hbij := grMap_bijective e N
  have hmem : ∀ (K : Ideal (AssocGraded N)) χ₀, σ χ₀ ∈ K.map σ ↔ χ₀ ∈ K := fun K χ₀ => by
    rw [Ideal.mem_map_iff_of_surjective σ hbij.2]
    exact ⟨fun ⟨x, hx, hxe⟩ => hbij.1 hxe ▸ hx, fun h => ⟨χ₀, h, rfl⟩⟩
  have hspan : Ideal.span (Set.range (σ ∘ φ)) = (Ideal.span (Set.range φ)).map σ := by
    rw [Ideal.map_span, Set.range_comp]
  refine ⟨σ ∘ φ, fun j => ⟨?_, ?_⟩, fun μ hμ χ hχ => ?_⟩
  · rw [← grMap_grIdeal]
    exact Ideal.mem_map_of_mem σ (hφ.1 j).1
  · obtain ⟨d, hd⟩ := (hφ.1 j).2
    exact ⟨d, (grMap_mem_homogeneous_iff e N d _).mpr ⟨φ j, hd, rfl⟩⟩
  · obtain ⟨χ₀, hχ₀, rfl⟩ := (grMap_mem_homogeneous_iff e N μ χ).mp hχ
    rw [hspan, ← grMap_grIdeal, hmem, hmem]
    exact hφ.2 μ hμ χ₀ hχ₀

end GrTransport

private theorem nuI_le_map {A B : Type u} [CommRing A] [IsRegularLocalRing A] [CommRing B]
    [IsRegularLocalRing B] (e : A ≃+* B) (I : Ideal A) (i : ℕ+) :
    nuI A I i ≤ nuI B (I.map (e : A →+* B)) i := by
  have hM : (maximalIdeal A).map (e : A →+* B) = maximalIdeal B :=
    map_maximalIdeal_of_surjective _ e.surjective
  refine iSup₂_le fun ν ⟨φ, hφ⟩ => ?_
  obtain ⟨φ', hφ'⟩ := exists_nuSystem_map e _ _ hM I ν _ φ hφ
  exact le_iSup₂_of_le (f := fun (ν : ℕ) (_ : ∃ φ : Fin ((i : ℕ) - 1) → AssocGraded
    (maximalIdeal B), IsNuSystem B (I.map (e : A →+* B)) ν ((i : ℕ) - 1) φ) => (ν : ℕ∞))
    ν ⟨φ', hφ'⟩ le_rfl

/-- `ν*` is invariant under ring isomorphisms. -/
private theorem nuStar_ringEquiv {A B : Type u} [CommRing A] [IsRegularLocalRing A]
    [CommRing B] [IsRegularLocalRing B] (e : A ≃+* B) (I : Ideal A) :
    nuStar B (I.map (e : A →+* B)) = nuStar A I := by
  unfold nuStar
  congr 1
  funext i
  refine le_antisymm ?_ (nuI_le_map e I i)
  have := nuI_le_map e.symm (I.map (e : A →+* B)) i
  rwa [Ideal.map_of_equiv] at this

/-! ### Theorem 2: localization helpers -/

section Thm2Aux

/-- For a localization `S` of `A` at `M`: if `x/1 ∈ IS` then `t x ∈ I` for some `t ∈ M`. -/
private theorem exists_mul_mem_of_algebraMap_mem {A S : Type*} [CommRing A] [CommRing S]
    [Algebra A S] (M : Submonoid A) [IsLocalization M S] {I : Ideal A} {x : A}
    (hx : algebraMap A S x ∈ I.map (algebraMap A S)) : ∃ t ∈ M, t * x ∈ I := by
  rw [IsLocalization.mem_map_algebraMap_iff M S] at hx
  obtain ⟨⟨a, s⟩, hs⟩ := hx
  simp only at hs
  rw [← map_mul, IsLocalization.eq_iff_exists M S] at hs
  obtain ⟨c, hc⟩ := hs
  refine ⟨c * s, M.mul_mem c.2 s.2, ?_⟩
  have : (c : A) * s * x = c * a := by rw [← hc]; ring
  rw [this]
  exact I.mul_mem_left _ a.2

/-- The canonical homomorphism `A_P → A_Q` for primes `Q ⊆ P`. -/
private noncomputable def locMap {A : Type u} [CommRing A] (Q P : Ideal A) [Q.IsPrime]
    [P.IsPrime] (hQP : Q ≤ P) : Localization.AtPrime P →+* Localization.AtPrime Q :=
  IsLocalization.lift (M := P.primeCompl) (S := Localization.AtPrime P)
    (g := algebraMap A (Localization.AtPrime Q))
    fun y => IsLocalization.map_units (Localization.AtPrime Q)
      (⟨y, fun h => y.2 (hQP h)⟩ : Q.primeCompl)

private theorem locMap_algebraMap {A : Type u} [CommRing A] (Q P : Ideal A) [Q.IsPrime]
    [P.IsPrime] (hQP : Q ≤ P) (a : A) :
    locMap Q P hQP (algebraMap A (Localization.AtPrime P) a) =
      algebraMap A (Localization.AtPrime Q) a :=
  IsLocalization.lift_eq _ _

private theorem locMap_comp {A : Type u} [CommRing A] (Q P : Ideal A) [Q.IsPrime]
    [P.IsPrime] (hQP : Q ≤ P) :
    (locMap Q P hQP).comp (algebraMap A (Localization.AtPrime P)) =
      algebraMap A (Localization.AtPrime Q) :=
  RingHom.ext fun a => locMap_algebraMap Q P hQP a

/-- `QA_P` is a prime of `A_P` lying over `Q`, for primes `Q ⊆ P`. -/
private theorem map_isPrime {A : Type u} [CommRing A] (Q P : Ideal A) [hQ : Q.IsPrime]
    [P.IsPrime] (hQP : Q ≤ P) :
    (Q.map (algebraMap A (Localization.AtPrime P))).IsPrime ∧
      (Q.map (algebraMap A (Localization.AtPrime P))).comap
        (algebraMap A (Localization.AtPrime P)) = Q := by
  have hd : Disjoint (P.primeCompl : Set A) Q :=
    Set.disjoint_left.mpr fun a ha haQ => ha (hQP haQ)
  exact ⟨IsLocalization.isPrime_of_isPrime_disjoint P.primeCompl _ Q hQ hd,
    IsLocalization.under_map_of_isPrime_disjoint P.primeCompl _ hQ hd⟩

/-- For primes `Q ⊆ P` with `A_P` and `A_P/QA_P` regular, `(QA_P)ⁿ` is the contraction of
`(QA_Q)ⁿ` along `A_P → A_Q` (the powers of `QA_P` are `QA_P`-primary, p. 217). -/
private theorem mem_pow_iff {A : Type u} [CommRing A] (Q P : Ideal A) [Q.IsPrime]
    [P.IsPrime] (hQP : Q ≤ P) [IsRegularLocalRing (Localization.AtPrime P)]
    (hreg : IsRegularLocalRing
      (Localization.AtPrime P ⧸ Q.map (algebraMap A (Localization.AtPrime P))))
    (n : ℕ) (x : Localization.AtPrime P) :
    locMap Q P hQP x ∈ maximalIdeal (Localization.AtPrime Q) ^ n ↔
      x ∈ Q.map (algebraMap A (Localization.AtPrime P)) ^ n := by
  set ιP := algebraMap A (Localization.AtPrime P) with hιP
  set ιQ := algebraMap A (Localization.AtPrime Q) with hιQ
  obtain ⟨hprime, hcomap⟩ := map_isPrime Q P hQP
  obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective P.primeCompl x
  have hx : IsLocalization.mk' (Localization.AtPrime P) a s * ιP s = ιP a :=
    IsLocalization.mk'_spec _ a s
  have hMQ : ∀ k : ℕ, maximalIdeal (Localization.AtPrime Q) ^ k = (Q ^ k).map ιQ := fun k => by
    rw [Ideal.map_pow, Localization.AtPrime.map_eq_maximalIdeal]
  constructor
  · intro h
    have e1 : locMap Q P hQP (IsLocalization.mk' (Localization.AtPrime P) a s) * ιQ s =
        ιQ a := by
      have := congrArg (locMap Q P hQP) hx
      rwa [map_mul, locMap_algebraMap, locMap_algebraMap] at this
    have h' : ιQ a ∈ (Q ^ n).map ιQ := by
      rw [← hMQ, ← e1]
      exact Ideal.mul_mem_right _ _ h
    obtain ⟨t, ht, hta⟩ := exists_mul_mem_of_algebraMap_mem Q.primeCompl h'
    have h1 : (ιP t * ιP s) * IsLocalization.mk' (Localization.AtPrime P) a s ∈
        Q.map ιP ^ n := by
      have : ιP (t * a) ∈ Q.map ιP ^ n := by
        rw [← Ideal.map_pow]
        exact Ideal.mem_map_of_mem _ hta
      rw [map_mul, ← hx] at this
      convert this using 1
      ring
    refine mem_pow_of_mul_mem_pow_of_isRegularLocalRing_quotient (Q.map ιP) hreg n _ _ ?_ h1
    intro hmem
    rcases hprime.mem_or_mem hmem with h2 | h2
    · rw [← Ideal.mem_comap, hcomap] at h2
      exact ht h2
    · rw [← Ideal.mem_comap, hcomap] at h2
      exact s.2 (hQP h2)
  · intro h
    have : locMap Q P hQP (IsLocalization.mk' (Localization.AtPrime P) a s) ∈
        (Q.map ιP ^ n).map (locMap Q P hQP) := Ideal.mem_map_of_mem _ h
    rwa [Ideal.map_pow, Ideal.map_map, locMap_comp, Localization.AtPrime.map_eq_maximalIdeal]
      at this

/-- `(A/I)_{p̄} ≅ A_p/IA_p` for a prime `p ⊇ I` with image `p̄` in `A/I`. -/
private theorem exists_quotient_localization_equiv {A : Type u} [CommRing A] (I p : Ideal A)
    [p.IsPrime] (pb : Ideal (A ⧸ I)) [pb.IsPrime] (hpb : pb.comap (Ideal.Quotient.mk I) = p) :
    ∃ e : Localization.AtPrime pb ≃+*
        (Localization.AtPrime p ⧸ I.map (algebraMap A (Localization.AtPrime p))),
      ∀ a : A, e (algebraMap (A ⧸ I) _ (Ideal.Quotient.mk I a)) =
        Ideal.Quotient.mk _ (algebraMap A (Localization.AtPrime p) a) := by
  let Ap := Localization.AtPrime p
  let R' := Ap ⧸ I.map (algebraMap A Ap)
  let T := pb.primeCompl
  have hT : Algebra.algebraMapSubmonoid (A ⧸ I) p.primeCompl = T := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      show Ideal.Quotient.mk I y ∉ pb
      rw [← Ideal.mem_comap, hpb]
      exact hy
    · intro hx
      obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
      refine ⟨y, ?_, rfl⟩
      show y ∉ p
      rw [← hpb, Ideal.mem_comap]
      exact hx
  have hloc : IsLocalization T R' := by
    rw [← hT]
    infer_instance
  let e := IsLocalization.algEquiv T (Localization.AtPrime pb) R'
  refine ⟨e.toRingEquiv, fun a => ?_⟩
  show e (algebraMap _ _ _) = _
  rw [e.commutes]
  rfl

/-- The quotient `A_P/QA_P` is a regular local ring for primes `Q ⊆ P` of a ring `A` with `A/Q`
regular (it is `(A/Q)_{P/Q}`, p. 220: "`A_P/QA_P = (A/Q)_{P/Q}`"). -/
private theorem isRegularLocalRing_localization_quotient {A : Type u} [CommRing A] (Q P : Ideal A)
    [Q.IsPrime] [P.IsPrime] (hQP : Q ≤ P) [IsRegularRing (A ⧸ Q)] :
    IsRegularLocalRing
      (Localization.AtPrime P ⧸ Q.map (algebraMap A (Localization.AtPrime P))) := by
  have hker : RingHom.ker (Ideal.Quotient.mk Q) ≤ P := by rwa [Ideal.mk_ker]
  have hpb : (P.map (Ideal.Quotient.mk Q)).IsPrime :=
    Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective hker
  have hpbc : (P.map (Ideal.Quotient.mk Q)).comap (Ideal.Quotient.mk Q) = P := by
    rw [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective, ← RingHom.ker_eq_comap_bot,
      sup_eq_left.mpr hker]
  obtain ⟨e, -⟩ := exists_quotient_localization_equiv Q P (P.map (Ideal.Quotient.mk Q)) hpbc
  exact IsRegularLocalRing.of_ringEquiv e

/-- **`Qⁿ A_Q ∩ A = Qⁿ`** for a regular ring `A` and a prime `Q` with `A/Q` regular.  Used tacitly
on p. 220, where `gr_Q(A)_Q` is identified with `gr_{QA_Q}(A_Q)` and the initial form `Φ_j` of `f_j`
in `gr_Q(A)` with the initial form of the image of `f_j` in `gr_{QA_Q}(A_Q)`; the paper proves the
local case (p. 217: "If `R/P` is regular, then we have `P^ν = P^νR_P ∩ R`") and not this global
one.  The proof reduces to the local case at every maximal ideal of `A`. -/
private theorem mem_pow_of_algebraMap_mem_pow {A : Type u} [CommRing A] [IsRegularRing A]
    (Q : Ideal A) [Q.IsPrime] [IsRegularRing (A ⧸ Q)] (n : ℕ) {a : A}
    (h : algebraMap A (Localization.AtPrime Q) a ∈ maximalIdeal (Localization.AtPrime Q) ^ n) :
    a ∈ Q ^ n := by
  refine Ideal.mem_of_localization_maximal fun P hP => ?_
  have : P.IsPrime := hP.isPrime
  by_cases hQP : Q ≤ P
  · have hreg := isRegularLocalRing_localization_quotient Q P hQP
    have h1 := (mem_pow_iff Q P hQP hreg n (algebraMap A (Localization.AtPrime P) a)).mp
      (by rwa [locMap_algebraMap])
    rwa [← Ideal.map_pow] at h1
  · obtain ⟨q, hqQ, hqP⟩ := IsConcreteLE.not_le_iff_exists.mp hQP
    have hu : IsUnit (algebraMap A (Localization.AtPrime P) q) :=
      IsLocalization.map_units (Localization.AtPrime P) (⟨q, hqP⟩ : P.primeCompl)
    have htop : Q.map (algebraMap A (Localization.AtPrime P)) = ⊤ :=
      Ideal.eq_top_of_isUnit_mem _ (Ideal.mem_map_of_mem _ hqQ) hu
    have : (Q ^ n).map (algebraMap A (Localization.AtPrime P)) = ⊤ := by
      rw [Ideal.map_pow, htop, Ideal.top_pow]
    rw [this]
    exact Submodule.mem_top

/-- `Qⁿ B ∩ A = Qⁿ` for every localization `B` of `A` at a submonoid `M` of `A ∖ Q`
(`B = A_f` with `f ∉ Q`, or `B = A_P` with `P ⊇ Q`). -/
private theorem mem_pow_of_map_mem_pow {A : Type u} [CommRing A] [IsRegularRing A]
    (Q : Ideal A) [Q.IsPrime] [IsRegularRing (A ⧸ Q)] (M : Submonoid A) {B : Type u}
    [CommRing B] [Algebra A B] [IsLocalization M B] (hM : M ≤ Q.primeCompl) (n : ℕ) {a : A}
    (h : algebraMap A B a ∈ Q.map (algebraMap A B) ^ n) : a ∈ Q ^ n := by
  let ℓ : B →+* Localization.AtPrime Q := IsLocalization.lift (M := M) (S := B)
    (g := algebraMap A (Localization.AtPrime Q)) fun y =>
      IsLocalization.map_units (Localization.AtPrime Q) (⟨y, hM y.2⟩ : Q.primeCompl)
  have hℓ : ℓ.comp (algebraMap A B) = algebraMap A (Localization.AtPrime Q) :=
    RingHom.ext fun x => IsLocalization.lift_eq _ _
  have h1 := Ideal.mem_map_of_mem ℓ h
  rw [Ideal.map_pow, Ideal.map_map, hℓ, Localization.AtPrime.map_eq_maximalIdeal] at h1
  refine mem_pow_of_algebraMap_mem_pow Q n ?_
  rwa [← RingHom.comp_apply, hℓ] at h1

end Thm2Aux

section Thm2Core

variable {A : Type u} [CommRing A]

/-- The orders `ν_j = ν_{QA_Q}(f_j)` of the members of a standard base of `JA_Q`. -/
private noncomputable def nuAt (Q : Ideal A) [Q.IsPrime] {m : ℕ} (F : Fin m → A) (j : Fin m) :
    ℕ :=
  (Ideal.ordElem (maximalIdeal (Localization.AtPrime Q))
    (algebraMap A (Localization.AtPrime Q) (F j))).toNat

/-- The relation `t g ≡ Σ_{ν_j ≤ d} c_j f_j (mod Q^{d+1})` with `c_j ∈ Q^{d − ν_j}`. -/
private def Rel (Q : Ideal A) [Q.IsPrime] {m : ℕ} (F : Fin m → A) (g t : A) (d : ℕ) : Prop :=
  ∃ c : Fin m → A, (∀ j, nuAt Q F j ≤ d → c j ∈ Q ^ (d - nuAt Q F j)) ∧
    t * g - ∑ j ∈ Finset.univ.filter (fun j => nuAt Q F j ≤ d), c j * F j ∈ Q ^ (d + 1)

private theorem ordElem_eq_nuAt (J Q : Ideal A) [Q.IsPrime]
    [IsRegularLocalRing (Localization.AtPrime Q)] {m : ℕ} (F : Fin m → A)
    (hSB : IsStandardBase (Localization.AtPrime Q) (J.map (algebraMap A _))
      fun j => algebraMap A (Localization.AtPrime Q) (F j)) (j : Fin m) :
    Ideal.ordElem (maximalIdeal (Localization.AtPrime Q))
      (algebraMap A (Localization.AtPrime Q) (F j)) = nuAt Q F j := by
  have h0 : initialForm (maximalIdeal (Localization.AtPrime Q))
      (algebraMap A (Localization.AtPrime Q) (F j)) ≠ 0 := fun h0 => hSB.2.2.2.2 j (by
    dsimp only; rw [h0]; exact zero_mem _)
  have htop : Ideal.ordElem (maximalIdeal (Localization.AtPrime Q))
      (algebraMap A (Localization.AtPrime Q) (F j)) ≠ ⊤ := fun h => h0 (by
    rw [initialForm, dite_eq_left h])
  exact (ENat.natCast_toNat htop).symm

/-- The relation for one element `g ∈ J` with `ν_Q(g) = d`, obtained from the standard base of
`JA_Q` by clearing denominators. -/
private theorem exists_rel [IsNoetherianRing A] (J Q : Ideal A) [Q.IsPrime]
    [IsRegularLocalRing (Localization.AtPrime Q)] {m : ℕ} (F : Fin m → A)
    (hSB : IsStandardBase (Localization.AtPrime Q) (J.map (algebraMap A _))
      fun j => algebraMap A (Localization.AtPrime Q) (F j))
    {g : A} (hgJ : g ∈ J) {d : ℕ} (hd : Ideal.ordElem Q g = d) :
    ∃ t ∉ Q, Rel Q F g t d := by
  classical
  set ιQ := algebraMap A (Localization.AtPrime Q) with hιQ
  set MQ := maximalIdeal (Localization.AtPrime Q) with hMQdef
  have hMQ : ∀ k : ℕ, MQ ^ k = (Q ^ k).map ιQ := fun k => by
    rw [Ideal.map_pow, hMQdef, Localization.AtPrime.map_eq_maximalIdeal]
  have hgQ : g ∈ Q ^ d := Ideal.mem_pow_of_ordElem hd
  have hgM : ιQ g ∈ MQ ^ d := by rw [hMQ]; exact Ideal.mem_map_of_mem _ hgQ
  by_cases hdeg : Ideal.ordElem MQ (ιQ g) = d
  · -- the initial form of `g` in `gr(A_Q)` has degree `d`
    set ν := nuAt Q F with hνdef
    have hFM : ∀ j, ιQ (F j) ∈ MQ ^ ν j := fun j =>
      Ideal.mem_pow_of_ordElem (ordElem_eq_nuAt J Q F hSB j)
    have hinit : ∀ j, initialForm MQ (ιQ (F j)) = AssocGraded.mk MQ (ν j) (ιQ (F j)) (hFM j) :=
      fun j => initialForm_eq_mk MQ (ordElem_eq_nuAt J Q F hSB j)
    have hmem : AssocGraded.mk MQ d (ιQ g) hgM ∈
        Ideal.span (Set.range fun j => AssocGraded.mk MQ (ν j) (ιQ (F j)) (hFM j)) := by
      have h1 : initialForm MQ (ιQ g) ∈ grIdeal MQ (J.map ιQ) :=
        Ideal.subset_span ⟨ιQ g, Ideal.mem_map_of_mem _ hgJ, rfl⟩
      rw [hSB.2.2.2.1, initialForm_eq_mk MQ hdeg] at h1
      convert h1 using 3
      funext j
      exact (hinit j).symm
    obtain ⟨C, hC, hC0, hCg⟩ := exists_sub_mem_pow_of_mk_mem_span MQ (fun j => ιQ (F j)) ν hFM
      hgM hmem
    obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples Q.primeCompl Finset.univ C
    choose a ha using fun j => hb j (Finset.mem_univ j)
    -- the relation `b g − Σ a_j F_j ∈ Q^{d+1}` after multiplying by some `t₀ ∉ Q`
    have hrel : ιQ ((b : A) * g - ∑ j, a j * F j) ∈ (Q ^ (d + 1)).map ιQ := by
      rw [← hMQ]
      have : ιQ ((b : A) * g - ∑ j, a j * F j) =
          ιQ b * (ιQ g - ∑ j, C j * ιQ (F j)) := by
        rw [map_sub, map_mul, map_sum, mul_sub, Finset.mul_sum]
        congr 1
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [map_mul, ha j, Algebra.smul_def, mul_assoc]
      rw [this]
      exact Ideal.mul_mem_left _ _ hCg
    obtain ⟨t₀, ht₀, ht₀rel⟩ := exists_mul_mem_of_algebraMap_mem Q.primeCompl hrel
    -- the coefficients, after multiplying by some `t_j ∉ Q`
    let K : Fin m → Ideal A := fun j => if ν j ≤ d then Q ^ (d - ν j) else ⊥
    have hK : ∀ j, ιQ (a j) ∈ (K j).map ιQ := by
      intro j
      by_cases hj : ν j ≤ d
      · simp only [K, ite_eq_left hj]
        rw [← hMQ, ha j]
        exact Submodule.smul_of_tower_mem _ _ (hC j hj)
      · simp only [K, ite_eq_right hj, Ideal.map_bot]
        rw [ha j, hC0 j (not_le.mp hj), smul_zero]
        exact zero_mem _
    choose t ht htK using fun j => exists_mul_mem_of_algebraMap_mem Q.primeCompl (hK j)
    set T := t₀ * ∏ k, t k with hTdef
    have hT : T ∈ Q.primeCompl := Q.primeCompl.mul_mem ht₀ (prod_mem fun k _ => ht k)
    have hTj : ∀ j, ∃ r, T = r * t j := fun j =>
      ⟨t₀ * ∏ k ∈ Finset.univ.erase j, t k, by
        rw [hTdef, mul_assoc, Finset.prod_erase_mul _ _ (Finset.mem_univ j)]⟩
    refine ⟨T * b, Q.primeCompl.mul_mem hT b.2, fun j => T * a j, fun j hj => ?_, ?_⟩
    · obtain ⟨r, hr⟩ := hTj j
      have := htK j
      have hj' : ν j ≤ d := hj
      simp only [K] at this
      rw [ite_eq_left hj'] at this
      show T * a j ∈ _
      rw [hr, mul_assoc]
      exact Ideal.mul_mem_left _ _ this
    · have hsplit := Finset.sum_filter_add_sum_filter_not Finset.univ (fun j => ν j ≤ d)
        (fun j => T * a j * F j)
      have hzero : ∑ j ∈ Finset.univ.filter (fun j => ¬ ν j ≤ d), T * a j * F j = 0 := by
        refine Finset.sum_eq_zero fun j hj => ?_
        have hj' : ¬ ν j ≤ d := (Finset.mem_filter.mp hj).2
        obtain ⟨r, hr⟩ := hTj j
        have := htK j
        simp only [K, ite_eq_right hj', Ideal.mem_bot] at this
        rw [hr, mul_assoc r, this, mul_zero, zero_mul]
      rw [hzero, add_zero] at hsplit
      have heq : T * b * g - ∑ j ∈ Finset.univ.filter (fun j => ν j ≤ d), T * a j * F j =
          (∏ k, t k) * (t₀ * ((b : A) * g - ∑ j, a j * F j)) := by
        rw [hsplit, mul_sub, mul_sub, Finset.mul_sum, Finset.mul_sum, hTdef]
        congr 1
        · ring
        · refine Finset.sum_congr rfl fun j _ => ?_
          ring
      show T * b * g - ∑ j ∈ Finset.univ.filter (fun j => ν j ≤ d), T * a j * F j ∈ Q ^ (d + 1)
      rw [heq]
      exact Ideal.mul_mem_left _ _ ht₀rel
  · -- otherwise `g/1 ∈ (QA_Q)^{d+1}`, and `t g ∈ Q^{d+1}` for some `t ∉ Q`
    have h1 : (d : ℕ∞) ≤ Ideal.ordElem MQ (ιQ g) := Ideal.le_ordElem hgM
    have h2 : ((d + 1 : ℕ) : ℕ∞) ≤ Ideal.ordElem MQ (ιQ g) := by
      rw [Nat.cast_add, Nat.cast_one]
      exact Order.add_one_le_of_lt (lt_of_le_of_ne h1 (Ne.symm hdeg))
    have h3 : ιQ g ∈ (Q ^ (d + 1)).map ιQ := by
      rw [← hMQ]
      exact Ideal.mem_pow_of_le_ordElem h2
    obtain ⟨t, ht, htg⟩ := exists_mul_mem_of_algebraMap_mem Q.primeCompl h3
    refine ⟨t, ht, fun _ => 0, fun j _ => zero_mem _, ?_⟩
    simpa using htg

/-- `a ↦ [a X⁰]` is the `A`-algebra structure map of `gr_I(A)`. -/
private theorem algebraMap_eq_mk_zero {A : Type u} [CommRing A] (I : Ideal A) (a : A) :
    algebraMap A (AssocGraded I) a = AssocGraded.mk I 0 a (by simp) := by
  rw [AssocGraded.algebraMap_apply, AssocGraded.mk]
  congr 1

/-- `Qⁿ B ∩ A = Qⁿ` in the form of an equivalence, for a localization `B` of `A` at a submonoid
`M ⊆ A ∖ Q`. -/
private theorem mem_pow_map_iff {A : Type u} [CommRing A] [IsRegularRing A] (Q : Ideal A)
    [Q.IsPrime] [IsRegularRing (A ⧸ Q)] (M : Submonoid A) {B : Type u} [CommRing B]
    [Algebra A B] [IsLocalization M B] (hM : M ≤ Q.primeCompl) (n : ℕ) (a : A) :
    algebraMap A B a ∈ Q.map (algebraMap A B) ^ n ↔ a ∈ Q ^ n :=
  ⟨mem_pow_of_map_mem_pow Q M hM n, fun h => by
    rw [← Ideal.map_pow]
    exact Ideal.mem_map_of_mem _ h⟩

/-- The initial form of `a` is carried by `gr_Q(A) → gr_{QB}(B)` to that of its image when the
orders agree. -/
private theorem map_initialForm_of_ordElem_eq {A B : Type u} [CommRing A] [CommRing B]
    (φ : A →+* B) (I : Ideal A) (a : A)
    (hord : Ideal.ordElem (I.map φ) (φ a) = Ideal.ordElem I a) :
    AssocGraded.map φ I (initialForm I a) = initialForm (I.map φ) (φ a) := by
  by_cases h : Ideal.ordElem I a = ⊤
  · rw [initialForm, dite_eq_left h, map_zero, initialForm, dite_eq_left (hord.trans h)]
  · obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp h
    rw [initialForm_eq_mk I hn.symm, AssocGraded.map_mk,
      initialForm_eq_mk _ (hord.trans hn.symm)]

/-- **`gr_{QB}(JB, B) ⊆ σ̄(gr_Q(J, A))·gr_{QB}(B)`** for a localization `B` of `A` (the isomorphism
`gr_I(A)_P ≅ gr_{IA_P}(A_P)` of p. 181 and the identification
`gr_{IA_P}(JA_P, A_P) = gr_I(J, A)_P`): an initial form `[b Xⁿ]` of `b ∈ JB` with
`b ∈ (QB)ⁿ` becomes, after clearing denominators, the class of an element of `J ∩ Qⁿ`
up to a unit of `B`. -/
private theorem grIdeal_map_le_map_grIdeal {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    (M : Submonoid A) [IsLocalization M B] (I J : Ideal A) :
    grIdeal (I.map (algebraMap A B)) (J.map (algebraMap A B)) ≤
      Ideal.map (AssocGraded.map (algebraMap A B) I) (grIdeal I J) := by
  classical
  rw [grIdeal, Ideal.span_le]
  rintro _ ⟨b, hb, rfl⟩
  rw [SetLike.mem_coe]
  by_cases htop : Ideal.ordElem (I.map (algebraMap A B)) b = ⊤
  · rw [initialForm, dite_eq_left htop]
    exact zero_mem _
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp htop
  have hbn : b ∈ I.map (algebraMap A B) ^ n := Ideal.mem_pow_of_ordElem hn.symm
  rw [initialForm_eq_mk _ hn.symm]
  have hbn' := hbn
  rw [← Ideal.map_pow, IsLocalization.mem_map_algebraMap_iff M B] at hbn'
  have hb' := (SetLike.mem_coe.mp hb : b ∈ J.map (algebraMap A B))
  rw [IsLocalization.mem_map_algebraMap_iff M B] at hb'
  obtain ⟨⟨c, s⟩, hcs⟩ := hbn'
  obtain ⟨⟨j, t⟩, hjt⟩ := hb'
  simp only at hcs hjt
  have h1 : algebraMap A B ((c : A) * t) = algebraMap A B ((j : A) * s) := by
    rw [map_mul, map_mul, ← hcs, ← hjt]
    ring
  obtain ⟨r, hr⟩ := (IsLocalization.eq_iff_exists M B).mp h1
  set e : A := (r : A) * ((c : A) * t) with he
  have heI : e ∈ I ^ n := Ideal.mul_mem_left _ _ (Ideal.mul_mem_right _ _ c.2)
  have heJ : e ∈ J := by
    rw [hr]
    exact J.mul_mem_left _ (J.mul_mem_right _ j.2)
  set w : M := s * t * r with hw
  have hwb : algebraMap A B (w : A) * b = algebraMap A B e := by
    rw [hw, he]
    simp only [Submonoid.coe_mul, map_mul]
    rw [← hcs]
    ring
  have heB : algebraMap A B e ∈ I.map (algebraMap A B) ^ n := by
    rw [← Ideal.map_pow]
    exact Ideal.mem_map_of_mem _ heI
  have hmk : AssocGraded.mk (I.map (algebraMap A B)) 0 (algebraMap A B (w : A)) (by simp) *
      AssocGraded.mk (I.map (algebraMap A B)) n b hbn =
      AssocGraded.map (algebraMap A B) I (AssocGraded.mk I n e heI) := by
    rw [AssocGraded.mk_mul_mk, AssocGraded.map_mk]
    exact mk_congr' _ (zero_add n) hwb _ _
  have hunit : IsUnit (algebraMap B (AssocGraded (I.map (algebraMap A B)))
      (algebraMap A B (w : A))) :=
    (IsLocalization.map_units B w).map _
  rw [← algebraMap_eq_mk_zero] at hmk
  have hmem : AssocGraded.map (algebraMap A B) I (AssocGraded.mk I n e heI) ∈
      Ideal.map (AssocGraded.map (algebraMap A B) I) (grIdeal I J) :=
    Ideal.mem_map_of_mem _ (mk_mem_grIdeal I heJ heI)
  rw [← hmk] at hmem
  exact (Ideal.unit_mul_mem_iff_mem _ hunit).mp hmem

/-- `ν_{QA_Q}(a/1) = ν_Q(a)`: the order of an element of `A` along `Q` is its order in `A_Q`
(`Qⁿ A_Q ∩ A = Qⁿ`, `mem_pow_of_algebraMap_mem_pow`). -/
private theorem ordElem_atPrime_eq {A : Type u} [CommRing A] [IsRegularRing A] (Q : Ideal A)
    [Q.IsPrime] [IsRegularRing (A ⧸ Q)] (a : A) :
    Ideal.ordElem (maximalIdeal (Localization.AtPrime Q))
      (algebraMap A (Localization.AtPrime Q) a) = Ideal.ordElem Q a := by
  rw [← Localization.AtPrime.map_eq_maximalIdeal]
  simp only [Ideal.ordElem, mem_pow_map_iff Q Q.primeCompl le_rfl]

/-- p. 220: "We have `gr_Q(J, A)_Q = gr_{QA_Q}(JA_Q, A_Q) = (Φ₁, …, Φ_m) gr_Q(A)_Q`", in the form:
the initial form of every `g ∈ J` becomes, after multiplication by (the class in degree `0` of) some
`t ∈ A − Q`, an element of the ideal `(Φ₁, …, Φ_m)` of `gr_Q(A)`, where `Φ_j` is the initial form
of `f_j` in `gr_Q(A)`.  (The relation `t g ≡ Σ c_j f_j (mod Q^{d+1})` is obtained from the standard
base of `JA_Q` by clearing denominators, `exists_rel`; the orders of `f_j` in `A` and in `A_Q` agree
by `ordElem_atPrime_eq`.) -/
private theorem exists_mul_initialForm_mem_span {A : Type u} [CommRing A] [IsRegularRing A]
    (J Q : Ideal A) [Q.IsPrime] [IsRegularRing (A ⧸ Q)] {m : ℕ} (F : Fin m → A)
    (hSB : IsStandardBase (Localization.AtPrime Q) (J.map (algebraMap A _))
      fun j => algebraMap A (Localization.AtPrime Q) (F j))
    {g : A} (hgJ : g ∈ J) :
    ∃ t ∉ Q, algebraMap A (AssocGraded Q) t * initialForm Q g ∈
      Ideal.span (Set.range fun j => initialForm Q (F j)) := by
  classical
  by_cases htop : Ideal.ordElem Q g = ⊤
  · refine ⟨1, fun h => (Ideal.IsPrime.ne_top ‹_›) ((Ideal.eq_top_iff_one _).mpr h), ?_⟩
    rw [initialForm, dite_eq_left htop, mul_zero]
    exact zero_mem _
  obtain ⟨d, hd⟩ := ENat.ne_top_iff_exists.mp htop
  obtain ⟨t, ht, c, hc, hcg⟩ := exists_rel J Q F hSB hgJ hd.symm
  refine ⟨t, ht, ?_⟩
  set ν := nuAt Q F with hν
  have hordF : ∀ j, Ideal.ordElem Q (F j) = ν j := fun j =>
    (ordElem_atPrime_eq Q (F j)).symm.trans (ordElem_eq_nuAt J Q F hSB j)
  have hFQ : ∀ j, F j ∈ Q ^ ν j := fun j => Ideal.mem_pow_of_ordElem (hordF j)
  have hinit : ∀ j, initialForm Q (F j) = AssocGraded.mk Q (ν j) (F j) (hFQ j) := fun j =>
    initialForm_eq_mk Q (hordF j)
  have hgQ : g ∈ Q ^ d := Ideal.mem_pow_of_ordElem hd.symm
  have htg : t * g ∈ Q ^ d := Ideal.mul_mem_left _ _ hgQ
  have hmk := mk_mem_span_of_sub_mem_pow Q F ν hFQ htg (Finset.univ.filter fun j => ν j ≤ d) c
    (fun j hj => ⟨(Finset.mem_filter.mp hj).2, hc j (Finset.mem_filter.mp hj).2⟩) hcg
  have hsub : Ideal.span ((fun j => AssocGraded.mk Q (ν j) (F j) (hFQ j)) ''
      ((Finset.univ.filter fun j => ν j ≤ d : Finset (Fin m)) : Set (Fin m))) ≤
      Ideal.span (Set.range fun j => initialForm Q (F j)) := by
    refine Ideal.span_mono ?_
    rintro _ ⟨j, -, rfl⟩
    exact ⟨j, hinit j⟩
  rw [initialForm_eq_mk Q hd.symm, algebraMap_eq_mk_zero, AssocGraded.mk_mul_mk]
  rw [mk_congr' Q (zero_add d) rfl _ htg]
  exact hsub hmk

/-- p. 220: "Since `gr_Q(A)` is an `A/Q`-algebra of finite type and hence noetherian, the ideal
`gr_Q(J, A)` in `gr_Q(A)` has a finite system of generators.  Therefore, we can find an element
`f ∈ A − Q` such that `gr_Q(J, A)_f` (= the localization of `gr_Q(J, A)` with respect to the
multiplicatively closed set of the powers of `f`) is equal to `(Φ₁, …, Φ_m) gr_Q(A)_f`."  Here
`gr_Q(J, A)_f ⊆ (Φ₁, …, Φ_m) gr_Q(A)_f` is the statement that `f · gr_Q(J, A) ⊆ (Φ₁, …, Φ_m)`
(the generators are finitely many, so one `f` serves for all of them); the reverse inclusion holds
as the `Φ_j` are initial forms of elements of `J`. -/
private theorem exists_mul_mem_span_initialForm {A : Type u} [CommRing A] [IsRegularRing A]
    (J Q : Ideal A) [Q.IsPrime] [IsRegularRing (A ⧸ Q)] {m : ℕ} (F : Fin m → A)
    (hSB : IsStandardBase (Localization.AtPrime Q) (J.map (algebraMap A _))
      fun j => algebraMap A (Localization.AtPrime Q) (F j)) :
    ∃ f ∉ Q, ∀ x ∈ grIdeal Q J, algebraMap A (AssocGraded Q) f * x ∈
      Ideal.span (Set.range fun j => initialForm Q (F j)) := by
  classical
  have : IsNoetherianRing (AssocGraded Q) :=
    inferInstanceAs (IsNoetherianRing (reesAlgebra Q ⧸ _))
  obtain ⟨T, hTsub, hTspan⟩ := (Submodule.fg_span_iff_fg_span_finset_subset
    (initialForm Q '' (J : Set A))).mp (IsNoetherian.noetherian (grIdeal Q J))
  choose g hgJ hg using fun x : T => hTsub x.2
  choose t ht hrel using fun x : T => exists_mul_initialForm_mem_span J Q F hSB (hgJ x)
  refine ⟨∏ x, t x, fun h => ?_, fun x hx => ?_⟩
  · have : (∏ x, t x) ∈ Q.primeCompl := prod_mem fun x _ => ht x
    exact this h
  · let K : Submodule (AssocGraded Q) (AssocGraded Q) :=
      Submodule.comap (LinearMap.mulLeft (AssocGraded Q) (algebraMap A (AssocGraded Q) (∏ x, t x)))
        (Ideal.span (Set.range fun j => initialForm Q (F j)))
    have hle : Ideal.span (T : Set (AssocGraded Q)) ≤ K := by
      rw [Ideal.span_le]
      intro y hy
      show algebraMap A (AssocGraded Q) (∏ x, t x) * y ∈
        Ideal.span (Set.range fun j => initialForm Q (F j))
      have hyg : initialForm Q (g ⟨y, hy⟩) = y := hg ⟨y, hy⟩
      rw [← hyg, ← Finset.mul_prod_erase Finset.univ t (Finset.mem_univ (⟨y, hy⟩ : T)),
        map_mul, mul_comm (algebraMap A (AssocGraded Q) (t ⟨y, hy⟩)), mul_assoc]
      exact Ideal.mul_mem_left _ _ (hrel ⟨y, hy⟩)
    exact hle (hTspan.le hx)

/-- `ν_{QB}(a/1) = ν_Q(a)` for a localization `B` of `A` at a submonoid `M ⊆ A ∖ Q`. -/
private theorem ordElem_map_eq_of_le {A : Type u} [CommRing A] [IsRegularRing A] (Q : Ideal A)
    [Q.IsPrime] [IsRegularRing (A ⧸ Q)] (M : Submonoid A) {B : Type u} [CommRing B]
    [Algebra A B] [IsLocalization M B] (hM : M ≤ Q.primeCompl) (a : A) :
    Ideal.ordElem (Q.map (algebraMap A B)) (algebraMap A B a) = Ideal.ordElem Q a := by
  simp only [Ideal.ordElem, mem_pow_map_iff Q M hM]

/-- (ii) of Lemma 9 at a prime `P ⊇ Q`, from `gr_Q(J, A) = (Φ₁, …, Φ_m) gr_Q(A)` (the situation
after the replacement of `A` by `A[f⁻¹]`, p. 220): the initial forms of the `f_j` in `gr_{QA_P}(A_P)`
generate `gr_{QA_P}(JA_P, A_P)` (the flat base change `A → A_P`, as in Lemma 2 of §1). -/
private theorem span_eq_grIdeal_of_eq {A : Type u} [CommRing A] [IsRegularRing A] (J Q P : Ideal A)
    [Q.IsPrime] [P.IsPrime] (hQP : Q ≤ P) [IsRegularRing (A ⧸ Q)] {m : ℕ} (F : Fin m → A)
    (hFJ : ∀ j, F j ∈ J)
    (hH : grIdeal Q J = Ideal.span (Set.range fun j => initialForm Q (F j))) :
    Ideal.span (Set.range fun j => initialForm (Q.map (algebraMap A (Localization.AtPrime P)))
        (algebraMap A (Localization.AtPrime P) (F j))) =
      grIdeal (Q.map (algebraMap A (Localization.AtPrime P)))
        (J.map (algebraMap A (Localization.AtPrime P))) := by
  set ι := algebraMap A (Localization.AtPrime P) with hι
  apply le_antisymm
  · rw [Ideal.span_le]
    rintro _ ⟨j, rfl⟩
    exact Ideal.subset_span ⟨ι (F j), Ideal.mem_map_of_mem _ (hFJ j), rfl⟩
  · refine (grIdeal_map_le_map_grIdeal P.primeCompl Q J).trans ?_
    rw [hH, Ideal.map_span, ← Set.range_comp, Ideal.span_le]
    rintro _ ⟨j, rfl⟩
    refine Ideal.subset_span ⟨j, ?_⟩
    exact (map_initialForm_of_ordElem_eq ι Q (F j)
      (ordElem_map_eq_of_le Q P.primeCompl (fun x hx hxQ => hx (hQP hxQ)) (F j))).symm

end Thm2Core

section Thm2Final

variable {A : Type u} [CommRing A]

/-- Standard bases are carried along ring isomorphisms of regular local rings. -/
private theorem isStandardBase_ringEquiv {A B : Type u} [CommRing A] [IsRegularLocalRing A]
    [CommRing B] [IsRegularLocalRing B] (e : A ≃+* B) (I : Ideal A) {m : ℕ} (f : Fin m → A)
    (h : IsStandardBase A I f) :
    IsStandardBase B (I.map (e : A →+* B)) fun j => e (f j) := by
  have hM : (maximalIdeal A).map (e : A →+* B) = maximalIdeal B :=
    map_maximalIdeal_of_surjective _ e.surjective
  obtain ⟨hfJ, hgr, ⟨d, hd, hmono⟩, hspan, hnot⟩ := h
  refine ⟨fun j => Ideal.mem_map_of_mem _ (hfJ j), ?_⟩
  suffices key : ∀ N' : Ideal B, (maximalIdeal A).map (e : A →+* B) = N' →
      (∀ j, initialForm N' (e (f j)) ∈ grIdeal N' (I.map (e : A →+* B))) ∧
      (∃ d : Fin m → ℕ, (∀ j, initialForm N' (e (f j)) ∈ AssocGraded.homogeneous N' (d j)) ∧
        Monotone d) ∧
      grIdeal N' (I.map (e : A →+* B)) =
        Ideal.span (Set.range fun j => initialForm N' (e (f j))) ∧
      ∀ i : Fin m, initialForm N' (e (f i)) ∉
        Ideal.span (Set.range fun j : Fin i => initialForm N' (e (f (Fin.castLE i.2.le j)))) from
    key (maximalIdeal B) hM
  intro N' hN
  subst hN
  set N := maximalIdeal A
  set σ := AssocGraded.map (e : A →+* B) N
  have hbij := grMap_bijective e N
  have hmem : ∀ (K : Ideal (AssocGraded N)) χ₀, σ χ₀ ∈ K.map σ ↔ χ₀ ∈ K := fun K χ₀ => by
    rw [Ideal.mem_map_iff_of_surjective σ hbij.2]
    exact ⟨fun ⟨x, hx, hxe⟩ => hbij.1 hxe ▸ hx, fun h => ⟨χ₀, h, rfl⟩⟩
  have hinit : ∀ a, σ (initialForm N a) = initialForm (N.map (e : A →+* B)) (e a) :=
    grMap_initialForm e N
  have hspan' : Ideal.span (Set.range fun j => initialForm (N.map (e : A →+* B)) (e (f j))) =
      (Ideal.span (Set.range fun j => initialForm N (f j))).map σ := by
    rw [Ideal.map_span, ← Set.range_comp]
    congr 2
    funext j
    exact (hinit (f j)).symm
  refine ⟨fun j => ?_, ⟨d, fun j => ?_, hmono⟩, ?_, fun i hi => ?_⟩
  · rw [← hinit, ← grMap_grIdeal]
    exact Ideal.mem_map_of_mem σ (hgr j)
  · exact (grMap_mem_homogeneous_iff e N (d j) _).mpr ⟨_, hd j, hinit (f j)⟩
  · rw [hspan', ← hspan, grMap_grIdeal]
  · refine hnot i ?_
    have hi' : σ (initialForm N (f i)) ∈ (Ideal.span (Set.range fun j : Fin i =>
        initialForm N (f (Fin.castLE i.2.le j)))).map σ := by
      rw [hinit, Ideal.map_span, ← Set.range_comp]
      convert hi using 3
      funext j
      exact hinit _
    exact (hmem _ _).mp hi'

/-- The identification `(A_f)_{QA_f} = A_Q` and `(A_P)_{QA_P} = A_Q` of the paper, for a
localization `M⁻¹A` and a prime `q` of it lying over `Q`. -/
private noncomputable def atPrimeEquivOfEq {A : Type u} [CommRing A] {P P' : Ideal A}
    [P.IsPrime] [P'.IsPrime] (h : P = P') : Localization.AtPrime P ≃+* Localization.AtPrime P' := by
  subst h
  exact RingEquiv.refl _

private theorem atPrimeEquivOfEq_algebraMap {A : Type u} [CommRing A] {P P' : Ideal A}
    [P.IsPrime] [P'.IsPrime] (h : P = P') (a : A) :
    atPrimeEquivOfEq h (algebraMap A (Localization.AtPrime P) a) =
      algebraMap A (Localization.AtPrime P') a := by
  subst h
  rfl

private noncomputable def locLocEquiv {A : Type u} [CommRing A] (M : Submonoid A)
    (q : Ideal (Localization M)) [q.IsPrime] (P : Ideal A) [P.IsPrime]
    (hq : q.comap (algebraMap A (Localization M)) = P) :
    Localization.AtPrime P ≃+* Localization.AtPrime q :=
  (atPrimeEquivOfEq hq.symm).trans
    (IsLocalization.localizationLocalizationAtPrimeIsoLocalization M q).toRingEquiv

private theorem locLocEquiv_algebraMap {A : Type u} [CommRing A] (M : Submonoid A)
    (q : Ideal (Localization M)) [q.IsPrime] (P : Ideal A) [P.IsPrime]
    (hq : q.comap (algebraMap A (Localization M)) = P) (a : A) :
    locLocEquiv M q P hq (algebraMap A (Localization.AtPrime P) a) =
      algebraMap (Localization M) (Localization.AtPrime q) (algebraMap A (Localization M) a) := by
  rw [locLocEquiv, RingEquiv.trans_apply, atPrimeEquivOfEq_algebraMap]
  rw [← IsScalarTower.algebraMap_apply]
  exact (IsLocalization.localizationLocalizationAtPrimeIsoLocalization M q).commutes a

/-- The last step of the proof of Theorem 2 at one prime `P ⊇ Q`: "By applying Lemma 9 to `R = A_P`,
`JR`, `QR`, and `(f₁, …, f_m)`, we see immediately that [`ν*(JA_P) = ν*(JA_Q)`]".  Hypothesis (i) of
Lemma 9 for `R = A_P` is that `(f₁, …, f_m)` is a standard base of `JR_{QR}`, `R_{QR} = (A_P)_{QA_P}`;
it is the standard base of `JA_Q` transported along the canonical isomorphism `A_Q ≅ (A_P)_{QA_P}`
(`locLocEquiv`).  Lemma 9 gives that `(f₁, …, f_m)` is a standard base of `JA_P` with
`ν_{M_P}(f_j) = ν_{QA_P}(f_j) = ν_{QA_Q}(f_j)`, hence (Lemma 1, p. 208) `ν*(JA_P) = ν*(JA_Q)`. -/
private theorem nuStar_eq_at [IsRegularRing A] (J Q P : Ideal A) [Q.IsPrime] [P.IsPrime]
    (hJQ : J ≤ Q) (hQP : Q ≤ P) [IsRegularRing (A ⧸ Q)] {m : ℕ} (F : Fin m → A)
    (hFJ : ∀ j, F j ∈ J)
    (hSB : IsStandardBase (Localization.AtPrime Q) (J.map (algebraMap A _))
      fun j => algebraMap A (Localization.AtPrime Q) (F j))
    (hflat : IsNormallyFlatAlongIdeal ((Q.map (algebraMap A (Localization.AtPrime P))).map
      (Ideal.Quotient.mk (J.map (algebraMap A (Localization.AtPrime P))))))
    (h₂ : Ideal.span (Set.range fun j => initialForm (Q.map (algebraMap A
        (Localization.AtPrime P))) (algebraMap A (Localization.AtPrime P) (F j))) =
      grIdeal (Q.map (algebraMap A (Localization.AtPrime P)))
        (J.map (algebraMap A (Localization.AtPrime P)))) :
    nuStar (Localization.AtPrime P) (J.map (algebraMap A (Localization.AtPrime P))) =
      nuStar (Localization.AtPrime Q) (J.map (algebraMap A (Localization.AtPrime Q))) := by
  set ιP := algebraMap A (Localization.AtPrime P) with hιP
  have hqP : (Q.map ιP).IsPrime := (map_isPrime Q P hQP).1
  have hq : (Q.map ιP).comap ιP = Q := (map_isPrime Q P hQP).2
  have hreg := isRegularLocalRing_localization_quotient Q P hQP
  let e := locLocEquiv P.primeCompl (Q.map ιP) Q hq
  have : IsRegularLocalRing (Localization.AtPrime (Q.map ιP)) := IsRegularLocalRing.of_ringEquiv e
  -- (i): `(f₁, …, f_m)` is a standard base of `JR_{QR}`, `R_{QR} = (A_P)_{QA_P} ≅ A_Q`
  have h₁ : IsStandardBase (Localization.AtPrime (Q.map ιP))
      ((J.map ιP).map (algebraMap (Localization.AtPrime P) (Localization.AtPrime (Q.map ιP))))
      fun j => algebraMap (Localization.AtPrime P) (Localization.AtPrime (Q.map ιP)) (ιP (F j)) := by
    have key := isStandardBase_ringEquiv e (J.map (algebraMap A (Localization.AtPrime Q)))
      (fun j => algebraMap A _ (F j)) hSB
    have hfun : (fun j => e (algebraMap A (Localization.AtPrime Q) (F j))) =
        fun j => algebraMap (Localization.AtPrime P) (Localization.AtPrime (Q.map ιP))
          (ιP (F j)) := funext fun j => locLocEquiv_algebraMap _ _ _ hq _
    have hid : (J.map (algebraMap A (Localization.AtPrime Q))).map (e : _ →+* _) =
        (J.map ιP).map (algebraMap (Localization.AtPrime P) (Localization.AtPrime (Q.map ιP))) := by
      rw [Ideal.map_map, Ideal.map_map]
      congr 1
      exact RingHom.ext fun a => locLocEquiv_algebraMap _ _ _ hq a
    rw [hid] at key
    exact hfun ▸ key
  obtain ⟨hSBP, hord⟩ := isStandardBase_of_localization (Localization.AtPrime P) (J.map ιP)
    (Q.map ιP) (Ideal.map_mono hJQ) hflat (fun j => ιP (F j))
    (fun j => Ideal.mem_map_of_mem _ (hFJ j)) h₁ h₂
  refine nuStar_eq_of_isStandardBase _ _ _ _ hSBP hSB fun j => ?_
  rw [hord j, ordElem_map_eq_of_le Q P.primeCompl (fun x hx hxQ => hx (hQP hxQ)) (F j),
    ← ordElem_atPrime_eq Q (F j)]

/-- A standard base of `JA_Q` consisting of images of elements of `J` (clear the denominators of
any standard base; this multiplies its members by units). -/
private theorem exists_isStandardBase_of_elements (J Q : Ideal A) [Q.IsPrime]
    [IsRegularLocalRing (Localization.AtPrime Q)] :
    ∃ (m : ℕ) (F : Fin m → A), (∀ j, F j ∈ J) ∧
      IsStandardBase (Localization.AtPrime Q) (J.map (algebraMap A _))
        fun j => algebraMap A (Localization.AtPrime Q) (F j) := by
  obtain ⟨m, G, hG⟩ := exists_isStandardBase (Localization.AtPrime Q)
    (J.map (algebraMap A (Localization.AtPrime Q)))
  have hmem : ∀ j, ∃ x : J × Q.primeCompl, G j * algebraMap A (Localization.AtPrime Q) x.2 =
      algebraMap A (Localization.AtPrime Q) x.1 := fun j =>
    (IsLocalization.mem_map_algebraMap_iff Q.primeCompl _).mp (hG.1 j)
  choose x hx using hmem
  refine ⟨m, fun j => (x j).1, fun j => (x j).1.2, ?_⟩
  refine isStandardBase_of_unit_mul _ hG
    (fun j => (IsLocalization.map_units (Localization.AtPrime Q) (x j).2).unit) fun j => ?_
  rw [IsUnit.unit_spec, ← hx j, mul_comm]

end Thm2Final

/-- A localization `M⁻¹A` of a noetherian ring is regular as soon as the local rings of `A` at the
primes disjoint from `M` are (its local rings are those local rings of `A`). -/
private theorem isRegularRing_of_isLocalization_of_forall {A S : Type u} [CommRing A]
    [IsNoetherianRing A] [CommRing S] [Algebra A S] (M : Submonoid A) [IsLocalization M S]
    (h : ∀ (q : Ideal A) [q.IsPrime], Disjoint (M : Set A) q →
      IsRegularLocalRing (Localization.AtPrime q)) : IsRegularRing S := by
  have : IsNoetherianRing S := IsLocalization.isNoetherianRing M S inferInstance
  refine isRegularRing_iff.mpr fun p hp => ?_
  have hdisj : Disjoint (M : Set A) (p.comap (algebraMap A S)) :=
    Set.disjoint_left.mpr fun x hxM hxp => (hp.ne_top
      (Ideal.eq_top_of_isUnit_mem p hxp (IsLocalization.map_units S ⟨x, hxM⟩)))
  have := h (p.comap (algebraMap A S)) hdisj
  have h' : IsLocalization.AtPrime (Localization.AtPrime p) (p.comap (algebraMap A S)) :=
    IsLocalization.isLocalization_isLocalization_atPrime_isLocalization M (Localization.AtPrime p) p
  exact IsRegularLocalRing.of_ringEquiv
    (IsLocalization.algEquiv (p.comap (algebraMap A S)).primeCompl
      (Localization.AtPrime (p.comap (algebraMap A S))) (Localization.AtPrime p)).toRingEquiv

/-- A localization `M⁻¹A` of a regular ring is regular. -/
private theorem isRegularRing_of_isLocalization {A S : Type u} [CommRing A] [CommRing S]
    [Algebra A S] [IsRegularRing A] (M : Submonoid A) [IsLocalization M S] : IsRegularRing S :=
  isRegularRing_of_isLocalization_of_forall M fun _ _ _ => inferInstance

/-- `ν*` of an ideal of a localization `B = M⁻¹A` at a prime `q` over `P`: `ν*((JB)B_q) =
ν*(JA_P)` (the canonical isomorphism `A_P ≅ B_q`). -/
private theorem nuStar_localization_eq {A : Type u} [CommRing A] [IsRegularRing A]
    (M : Submonoid A) [IsRegularRing (Localization M)] (J : Ideal A)
    (q : Ideal (Localization M)) [q.IsPrime] (P : Ideal A) [P.IsPrime]
    (hq : q.comap (algebraMap A (Localization M)) = P) :
    nuStar (Localization.AtPrime q)
        ((J.map (algebraMap A (Localization M))).map
          (algebraMap (Localization M) (Localization.AtPrime q))) =
      nuStar (Localization.AtPrime P) (J.map (algebraMap A (Localization.AtPrime P))) := by
  have := nuStar_ringEquiv (locLocEquiv M q P hq) (J.map (algebraMap A (Localization.AtPrime P)))
  rw [← this, Ideal.map_map, Ideal.map_map]
  congr 2
  exact RingHom.ext fun a => (locLocEquiv_algebraMap M q P hq a).symm

/-- The conclusion of Theorem 2 for `(A, J, Q)`. -/
private def Thm2Conclusion (A : Type u) [CommRing A] [IsRegularRing A] (J Q : Ideal A)
    [Q.IsPrime] : Prop :=
  ∃ U : Set (PrimeSpectrum (A ⧸ Q)), IsOpen U ∧ U.Nonempty ∧
    ∀ P' ∈ U,
      nuStar (Localization.AtPrime (PrimeSpectrum.comap (Ideal.Quotient.mk Q) P').asIdeal)
          (J.map (algebraMap A _)) =
        nuStar (Localization.AtPrime Q) (J.map (algebraMap A _))

/-- "By replacing `A` by `A[f⁻¹]` and `J` by `JA[f⁻¹]`" (p. 220): the conclusion of Theorem 2 for
`(A[f⁻¹], JA[f⁻¹], QA[f⁻¹])` gives it for `(A, J, Q)` when `f ∉ Q`.  The open set of `Spec(A/Q)` is the
image of the open set of `Spec(A[f⁻¹]/QA[f⁻¹]) = D(f̄) ⊆ Spec(A/Q)`, and `A_P = (A[f⁻¹])_{PA[f⁻¹]}`
for `f ∉ P`. -/
private theorem thm2Conclusion_of_away {A : Type u} [CommRing A] [IsRegularRing A]
    (J Q : Ideal A) [Q.IsPrime] (f : A) (hf : f ∉ Q) [IsRegularRing (Localization.Away f)]
    [(Q.map (algebraMap A (Localization.Away f))).IsPrime]
    (h : Thm2Conclusion (Localization.Away f) (J.map (algebraMap A (Localization.Away f)))
      (Q.map (algebraMap A (Localization.Away f)))) :
    Thm2Conclusion A J Q := by
  classical
  obtain ⟨UB, hUBo, hUBne, hUB⟩ := h
  have hdisj : Disjoint ((Submonoid.powers f : Submonoid A) : Set A) (Q : Set A) :=
    Set.disjoint_left.mpr fun x ⟨n, hn⟩ hxQ => hf (‹Q.IsPrime›.mem_of_pow_mem n (by rw [show f ^ n = x from hn]; exact hxQ))
  have hQB : (Q.map (algebraMap A (Localization.Away f))).comap
      (algebraMap A (Localization.Away f)) = Q :=
    IsLocalization.under_map_of_isPrime_disjoint (Submonoid.powers f) _ ‹Q.IsPrime› hdisj
  -- `A[f⁻¹]/QA[f⁻¹]` is the localization of `A/Q` at `f̄`
  have hloc : IsLocalization.Away (Ideal.Quotient.mk Q f)
      (Localization.Away f ⧸ Q.map (algebraMap A (Localization.Away f))) := by
    have h0 : IsLocalization (Algebra.algebraMapSubmonoid (A ⧸ Q) (Submonoid.powers f))
        (Localization.Away f ⧸ Q.map (algebraMap A (Localization.Away f))) := inferInstance
    rwa [Algebra.algebraMapSubmonoid, Submonoid.map_powers] at h0
  refine ⟨PrimeSpectrum.comap (algebraMap (A ⧸ Q)
    (Localization.Away f ⧸ Q.map (algebraMap A (Localization.Away f)))) '' UB, ?_,
    hUBne.image _, ?_⟩
  · exact (PrimeSpectrum.localization_away_isOpenEmbedding _ (Ideal.Quotient.mk Q f)).isOpenMap
      _ hUBo
  · rintro _ ⟨P'B, hP'B, rfl⟩
    have hpB : ((PrimeSpectrum.comap (Ideal.Quotient.mk (Q.map (algebraMap A
        (Localization.Away f)))) P'B).asIdeal).comap (algebraMap A (Localization.Away f)) =
        (PrimeSpectrum.comap (Ideal.Quotient.mk Q) (PrimeSpectrum.comap (algebraMap (A ⧸ Q)
          (Localization.Away f ⧸ Q.map (algebraMap A (Localization.Away f)))) P'B)).asIdeal := by
      ext a
      rfl
    have h1 := hUB P'B hP'B
    rw [nuStar_localization_eq (Submonoid.powers f) J _ _ hpB,
      nuStar_localization_eq (Submonoid.powers f) J _ _ hQB] at h1
    exact h1

/-- The proof of Theorem 2 once `gr_Q(J, A) = (Φ₁, …, Φ_m) gr_Q(A)` (p. 220: "we may assume that
`gr_Q(J, A) = (Φ₁, …, Φ_m) gr_Q(A)`"): "Let `A' = A/J` and `Q' = Q/J`. Then `gr_{Q'}(A')` is a graded
`A'/Q'` (`= A/Q`)-algebra of finite type and, by Theorem 1, §1, Ch. II, we have an open subset `U`
of `Spec(A/Q)` such that, if `P` is a prime ideal in `A` containing `Q`, we have: `P/Q ∈ U ⇔
gr_{Q'}(A')_P` is flat over `A'_P/Q'A'_P = A_P/QA_P`.  If `P = Q`, then `A_P/QA_P` is a field, and
hence it is clear that `gr_{Q'}(A')_P` is flat over `A_P/QA_P`; i.e., `P/Q ∈ U`.  Thus `U` is a
non-empty open subset of `Spec(A/Q)`.  By applying Lemma 9 to `R = A_P`, `JR`, `QR`, and
`(f₁, …, f_m)`, we see immediately that this non-empty open subset `U` of `Spec(A/Q)` has the
property stated in Theorem 2." -/
private theorem exists_open_nuStar_localization_eq_of_gr_eq (A : Type u) [CommRing A]
    [IsRegularRing A] (J Q : Ideal A) [Q.IsPrime] (hJQ : J ≤ Q) [IsRegularRing (A ⧸ Q)] {m : ℕ}
    (F : Fin m → A) (hFJ : ∀ j, F j ∈ J)
    (hSB : IsStandardBase (Localization.AtPrime Q) (J.map (algebraMap A _))
      fun j => algebraMap A (Localization.AtPrime Q) (F j))
    (hH : grIdeal Q J = Ideal.span (Set.range fun j => initialForm Q (F j))) :
    ∃ U : Set (PrimeSpectrum (A ⧸ Q)), IsOpen U ∧ U.Nonempty ∧
      ∀ P' ∈ U,
        nuStar (Localization.AtPrime (PrimeSpectrum.comap (Ideal.Quotient.mk Q) P').asIdeal)
            (J.map (algebraMap A _)) =
          nuStar (Localization.AtPrime Q) (J.map (algebraMap A _)) := by
  classical
  -- Theorem 1 of Ch. II for `A' = A/J`, `Q' = Q/J`: the normally flat locus
  obtain ⟨O, hO, hOiff⟩ :=
    exists_isOpen_primes_isNormallyFlatAlongIdeal (Q.map (Ideal.Quotient.mk J))
  have hpbQ : ∀ pb : PrimeSpectrum (A ⧸ J), Q ≤ pb.asIdeal.comap (Ideal.Quotient.mk J) →
      Q.map (Ideal.Quotient.mk J) ≤ pb.asIdeal := fun pb h => Ideal.map_le_iff_le_comap.mpr h
  let φ : A ⧸ J →+* A ⧸ Q := Ideal.Quotient.factor hJQ
  have hφmk : ∀ a, φ (Ideal.Quotient.mk J a) = Ideal.Quotient.mk Q a := fun a =>
    Ideal.Quotient.factor_mk hJQ a
  have hcomap : ∀ P' : PrimeSpectrum (A ⧸ Q),
      (PrimeSpectrum.comap φ P').asIdeal.comap (Ideal.Quotient.mk J) =
        P'.asIdeal.comap (Ideal.Quotient.mk Q) := fun P' => by
    ext a
    show φ (Ideal.Quotient.mk J a) ∈ P'.asIdeal ↔ Ideal.Quotient.mk Q a ∈ P'.asIdeal
    rw [hφmk]
  refine ⟨PrimeSpectrum.comap φ ⁻¹' O,
    (PrimeSpectrum.continuous_comap φ).isOpen_preimage O hO, ?_, ?_⟩
  · -- "If `P = Q`, then `A_P/QA_P` is a field, and hence it is clear that `gr_{Q'}(A')_P` is flat
    -- over `A_P/QA_P`; i.e., `P/Q ∈ U`"
    have : IsDomain (A ⧸ Q) := Ideal.Quotient.isDomain Q
    let P₀ : PrimeSpectrum (A ⧸ Q) := ⟨⊥, Ideal.isPrime_bot⟩
    refine ⟨P₀, ?_⟩
    have hpb : (PrimeSpectrum.comap φ P₀).asIdeal.comap (Ideal.Quotient.mk J) = Q := by
      rw [hcomap]
      ext a
      show Ideal.Quotient.mk Q a ∈ (⊥ : Ideal (A ⧸ Q)) ↔ a ∈ Q
      rw [Ideal.mem_bot, Ideal.Quotient.eq_zero_iff_mem]
    have hker : ∀ pb : PrimeSpectrum (A ⧸ J), pb.asIdeal.comap (Ideal.Quotient.mk J) = Q →
        pb.asIdeal = Q.map (Ideal.Quotient.mk J) := fun pb hpb => by
      rw [← hpb, Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective]
    show PrimeSpectrum.comap φ P₀ ∈ O
    rw [hOiff _ (hpbQ _ hpb.ge), ← hker _ hpb, Localization.AtPrime.map_eq_maximalIdeal]
    intro n
    let _ := Ideal.Quotient.field (maximalIdeal (Localization.AtPrime
      (PrimeSpectrum.comap φ P₀).asIdeal))
    exact Module.Free.of_divisionRing _ _
  · intro P' hPO
    set P : Ideal A := (PrimeSpectrum.comap (Ideal.Quotient.mk Q) P').asIdeal with hPdef
    have hPeq : P = P'.asIdeal.comap (Ideal.Quotient.mk Q) := rfl
    have hQP : Q ≤ P := fun q hq => by
      rw [hPeq, Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.mpr hq]
      exact zero_mem _
    -- normal flatness at `P`, transported from `(A/J)_{P/J}` to `A_P/JA_P`
    have hflat : IsNormallyFlatAlongIdeal ((Q.map (algebraMap A (Localization.AtPrime P))).map
        (Ideal.Quotient.mk (J.map (algebraMap A (Localization.AtPrime P))))) := by
      have h1 := (hOiff (PrimeSpectrum.comap φ P')
        (hpbQ _ ((hcomap P').symm ▸ hPeq ▸ hQP))).mp hPO
      obtain ⟨e, he⟩ := exists_quotient_localization_equiv J P (PrimeSpectrum.comap φ P').asIdeal
        ((hcomap P').trans hPeq.symm)
      refine isNormallyFlatAlongIdeal_transport e _ _ ?_ h1
      rw [Ideal.map_map, Ideal.map_map, Ideal.map_map]
      congr 1
      exact RingHom.ext fun a => he a
    -- (ii) of Lemma 9 at `P`
    have h₂ := span_eq_grIdeal_of_eq J Q P hQP F hFJ hH
    exact nuStar_eq_at J Q P hJQ hQP F hFJ hSB hflat h₂

/-! ### Theorem 2 (p. 220) -/

/-- Theorem 2, p. 220: "Let `A` be a noetherian regular ring, `J` an ideal in `A`, and `Q` a
prime ideal in `A` which contains `J`. Suppose `A/Q` is also a regular ring. Then there exists a
non-empty open subset `U` of `Spec(A/Q)` such that we have `ν*(JA_P) = ν*(JA_Q)` for every prime
ideal `P` in `A` such that `P ⊇ Q` and `P/Q ∈ U`."

Formalization note (encoding): "noetherian regular ring" is Mathlib's `IsRegularRing`
(noetherian, with all localizations at primes regular local rings), which also provides the
regularity of `A_P` and `A_Q` needed to form `ν*`.  The primes `P ⊇ Q` of `A` correspond
bijectively to the points `P' = P/Q` of `Spec(A/Q)`, `P` being the preimage
`PrimeSpectrum.comap (Ideal.Quotient.mk Q) P'`; the conclusion is quantified over `P' ∈ U` with
`P` recovered as this preimage (this avoids carrying the primality of `P/Q` in the statement).

Proof as printed: the proof of p. 220 is followed sentence by sentence.
(1) "Let us take a system of elements `f₁, …, f_m` of `A` such that `(f₁, …, f_m)` (or, the system
of the canonical images of the `f_j` in `A_Q`) is a standard base of `JA_Q`":
`exists_isStandardBase_of_elements`.
(2) "Let `Φ_j` be the initial form of `f_j` in `gr_Q(A)`.  We have `gr_Q(J, A)_Q = gr_{QA_Q}(JA_Q, A_Q)
= (Φ₁, …, Φ_m) gr_Q(A)_Q`": `exists_mul_initialForm_mem_span`.
(3) "Since `gr_Q(A)` is an `A/Q`-algebra of finite type and hence noetherian, the ideal `gr_Q(J, A)`
has a finite system of generators.  Therefore, we can find an element `f ∈ A − Q` such that
`gr_Q(J, A)_f = (Φ₁, …, Φ_m) gr_Q(A)_f`": `exists_mul_mem_span_initialForm`.
(4) "By replacing `A` by `A[f⁻¹]` and `J` by `JA[f⁻¹]`, we may assume that `gr_Q(J, A) = (Φ₁, …, Φ_m)
gr_Q(A)`": the theorem for `(A[f⁻¹], JA[f⁻¹], QA[f⁻¹])` and the `f_j/1` implies it for `(A, J, Q)`
(`thm2Conclusion_of_away`), and the hypotheses pass to `A[f⁻¹]` (`isRegularRing_of_isLocalization`
for `A[f⁻¹]` and `A[f⁻¹]/QA[f⁻¹] = (A/Q)[f̄⁻¹]`, `isStandardBase_ringEquiv` for the standard base
along `(A[f⁻¹])_{QA[f⁻¹]} ≅ A_Q`, `grIdeal_map_le_map_grIdeal` for `gr`).
(5) "Let `A' = A/J` and `Q' = Q/J` … by Theorem 1, § 1, Ch. II, we have an open subset `U` of
`Spec(A/Q)` … If `P = Q`, then `A_P/QA_P` is a field, and hence it is clear that `gr_{Q'}(A')_P` is flat
over `A_P/QA_P`; i.e., `P/Q ∈ U`": `exists_open_nuStar_localization_eq_of_gr_eq`.
(6) "By applying Lemma 9 to `R = A_P`, `JR`, `QR`, and `(f₁, …, f_m)`, we see immediately …":
`nuStar_eq_at` (Lemma 9 itself, `isStandardBase_of_localization`, then Lemma 1 for `ν*`).

Gaps in the paper filled: (a) the paper says the `f_j` are "of `A`"; Lemma 9 needs them in `J`
(`f_j/1 ∈ JA_P`), and a lift to `A` of a standard base of `JA_Q` need not lie in `J`; they are taken
in `J` (clearing denominators; no effect on the rest of the proof).  (b) `Qⁿ A_Q ∩ A = Qⁿ`
(`mem_pow_of_algebraMap_mem_pow`), used tacitly to identify the initial form of `f_j` in `gr_Q(A)`
with that of its image in `gr_{QA_Q}(A_Q)` (the paper proves it for local `R` only, p. 217).
(c) "we may assume" in (4): the regularity of `A[f⁻¹]` and of `A[f⁻¹]/QA[f⁻¹]`, the passage of the
standard base and of `gr_Q(J, A) = (Φ_j)` to `A[f⁻¹]`, and that the open set of `Spec(A[f⁻¹]/QA[f⁻¹])`
is open in `Spec(A/Q)` and the `ν*` agree (`A_P = (A[f⁻¹])_{PA[f⁻¹]}` for `f ∉ P`).  (d) The
identification `(A_P)_{QA_P} = A_Q` in the application of Lemma 9 and the use of Lemma 1 to compare `ν*`.
(e) Hypothesis (ii) of Lemma 9 at `R = A_P`: the initial forms of the `f_j` in `gr_{QA_P}(A_P)`
generate `gr_{QA_P}(JA_P, A_P)` (`span_eq_grIdeal_of_eq`, from `gr_Q(J, A) = (Φ_j)` by the base change
`A → A_P` as in Lemma 2 of § 1).

Remaining difference: Theorem 1 of Ch. II § 1 is used through the public form
`exists_isOpen_primes_isNormallyFlatAlongIdeal` (Theorem 1 for `A/Q'` and `gr_{Q'}(A')`, with the
isomorphism of p. 181), which gives an open set `O` of `Spec(A/J)`; `U` is its preimage in
`Spec(A/Q)` under `Spec(A/Q) → Spec(A/J)`, which is the open set of the paper. -/
@[blueprint "thm:III.2"
  (statement := /-- Let $A$ be a noetherian regular ring, $J$ an ideal in $A$, and $Q$ a prime
    ideal in $A$ which contains $J$. Suppose $A/Q$ is also a regular ring. Then there exists a
    non-empty open subset $U$ of $\operatorname{Spec}(A/Q)$ such that we have
    $\nu^*(JA_P)=\nu^*(JA_Q)$ (\cref{def:III.2}) for every prime ideal $P$ in $A$ such that
    $P\supseteq Q$ and $P/Q\in U$. (Theorem 2, p.~220.) Formalization note (encoding): the
    condition is quantified over the points $P'=P/Q$ of $U$, $P$ being the preimage of $P'$ in
    $A$. -/)
  (proof := /-- Let us take a system of elements $f_1,\dots,f_m$ of $A$ such that
    $(f_1,\dots,f_m)$ (or, the system of the canonical images of the $f_j$ in $A_Q$) is a
    standard base of $JA_Q$. Let $\Phi_j$ be the initial form of $f_j$ in
    $\operatorname{gr}_Q(A)$. We have $\operatorname{gr}_Q(J,A)_Q=
    \operatorname{gr}_{QA_Q}(JA_Q,A_Q)=(\Phi_1,\dots,\Phi_m)\operatorname{gr}_Q(A)_Q$. Since
    $\operatorname{gr}_Q(A)$ is an $A/Q$-algebra of finite type and hence noetherian, the
    ideal $\operatorname{gr}_Q(J,A)$ in $\operatorname{gr}_Q(A)$ has a finite system of
    generators. Therefore, we can find an element $f\in A-Q$ such that
    $\operatorname{gr}_Q(J,A)_f$ (the localization of $\operatorname{gr}_Q(J,A)$ with respect
    to the multiplicatively closed set of the powers of $f$) is equal to
    $(\Phi_1,\dots,\Phi_m)\operatorname{gr}_Q(A)_f$. By replacing $A$ by $A[f^{-1}]$ and $J$
    by $JA[f^{-1}]$, we may assume that
    $\operatorname{gr}_Q(J,A)=(\Phi_1,\dots,\Phi_m)\operatorname{gr}_Q(A)$. Let $A'=A/J$ and
    $Q'=Q/J$. Then $\operatorname{gr}_{Q'}(A')$ is a graded $A'/Q'\ (=A/Q)$-algebra of finite
    type and, by \cref{thm:II.1-1}, we have an open subset $U$ of $\operatorname{Spec}(A/Q)$
    such that, if $P$ is a prime ideal in $A$ containing $Q$, we have: $P/Q\in U$ if and only
    if $\operatorname{gr}_{Q'}(A')_P$ is flat over $A'_P/Q'A'_P=A_P/QA_P$. If $P=Q$, then
    $A_P/QA_P$ is a field, and hence it is clear that $\operatorname{gr}_{Q'}(A')_P$ is flat
    over $A_P/QA_P$; i.e., $P/Q\in U$. Thus $U$ is a non-empty open subset of
    $\operatorname{Spec}(A/Q)$. By applying \cref{lem:III.9} to $R=A_P$, $JR$, $QR$, and
    $(f_1,\dots,f_m)$, we see immediately that this non-empty open subset $U$ of
    $\operatorname{Spec}(A/Q)$ has the property stated in Theorem 2.

    \textbf{Formal proof.} The formal proof follows this proof sentence by sentence. The $f_j$
    are taken in $J$ and $\Phi_j$ is the initial form of $f_j$ in $\operatorname{gr}_Q(A)$;
    $\operatorname{gr}_Q(J,A)_Q=(\Phi_1,\dots,\Phi_m)\operatorname{gr}_Q(A)_Q$ is proved by clearing
    denominators in property (ii) of the standard base of $JA_Q$, and the element $f$ is the
    product of the denominators needed for finitely many generators of
    $\operatorname{gr}_Q(J,A)$. The replacement of $A$ by $A[f^{-1}]$ is carried out: the theorem
    for $A[f^{-1}]$, $JA[f^{-1}]$, $QA[f^{-1}]$ implies the theorem for $A$, $J$, $Q$, since
    $A[f^{-1}]$ and $A[f^{-1}]/QA[f^{-1}]=(A/Q)[\bar f^{-1}]$ are regular, $D(\bar f)$ is open in
    $\operatorname{Spec}(A/Q)$, $A_P=A[f^{-1}]_{PA[f^{-1}]}$ for $f\notin P$, and
    $(A[f^{-1}])_{QA[f^{-1}]}=A_Q$ carries the standard base of $JA_Q$ to one of the localization of
    $JA[f^{-1}]$. Lemma~9 is applied to $R=A_P$ itself, the standard base of
    $JR_{QR}$ ($R_{QR}=(A_P)_{QA_P}\cong A_Q$) being transported along this isomorphism;
    $\nu^*(JA_P)=\nu^*(JA_Q)$ then follows from the standard bases and Lemma~1.

    \textbf{Gaps in the paper filled.} (a) The $f_j$ are said to be ``of $A$'' but Lemma~9 needs
    them in $J$; they are chosen in $J$. (b) $Q^nA_Q\cap A=Q^n$ (for $A$ and $A/Q$ regular) is used
    tacitly to identify the initial form of $f_j$ in $\operatorname{gr}_Q(A)$ with that in
    $\operatorname{gr}_{QA_Q}(A_Q)$; it is proved at every maximal ideal by the local case of
    p.~217. (c) The passage to $A[f^{-1}]$ ($\operatorname{gr}$ of a localization, regularity,
    descent of $U$ and of $\nu^*$) is proved. (d) The identification
    $(A_P)_{QA_P}=A_Q$ and the comparison of $\nu^*$ through Lemma~1. (e) Hypothesis (ii) of
    Lemma~9 at $A_P$ follows from $\operatorname{gr}_Q(J,A)=(\Phi_1,\dots,\Phi_m)\operatorname{gr}_Q(A)$
    by the base change $A\to A_P$.

    \textbf{Remaining difference.} \cref{thm:II.1-1} is used in its public form for $A/J$ and
    $Q/J$ (with the isomorphism of p.~181), which gives an open set of $\operatorname{Spec}(A/J)$;
    $U$ is its preimage in $\operatorname{Spec}(A/Q)$. -/)
  (latexEnv := "theorem")]
theorem exists_open_nuStar_localization_eq (A : Type u) [CommRing A] [IsRegularRing A]
    (J Q : Ideal A) [Q.IsPrime] (hJQ : J ≤ Q) [IsRegularRing (A ⧸ Q)] :
    ∃ U : Set (PrimeSpectrum (A ⧸ Q)), IsOpen U ∧ U.Nonempty ∧
      ∀ P' ∈ U,
        nuStar (Localization.AtPrime (PrimeSpectrum.comap (Ideal.Quotient.mk Q) P').asIdeal)
            (J.map (algebraMap A _)) =
          nuStar (Localization.AtPrime Q) (J.map (algebraMap A _)) := by
  classical
  -- "Let us take a system of elements `f₁, …, f_m` of `A` such that `(f₁, …, f_m)` (or, the system
  -- of the canonical images of the `f_j` in `A_Q`) is a standard base of `JA_Q`."
  obtain ⟨m, F, hFJ, hSB⟩ := exists_isStandardBase_of_elements J Q
  -- "Let `Φ_j` be the initial form of `f_j` in `gr_Q(A)`.  We have `gr_Q(J, A)_Q = gr_{QA_Q}(JA_Q, A_Q)
  -- = (Φ₁, …, Φ_m) gr_Q(A)_Q`.  Since `gr_Q(A)` is noetherian, `gr_Q(J, A)` has a finite system of
  -- generators.  Therefore we can find an element `f ∈ A − Q` such that `gr_Q(J, A)_f = (Φ₁, …, Φ_m)
  -- gr_Q(A)_f`."
  obtain ⟨f, hfQ, hf⟩ := exists_mul_mem_span_initialForm J Q F hSB
  -- "By replacing `A` by `A[f⁻¹]` and `J` by `JA[f⁻¹]`, we may assume that `gr_Q(J, A) = (Φ₁, …, Φ_m)
  -- gr_Q(A)`."
  have hdisj : Disjoint ((Submonoid.powers f : Submonoid A) : Set A) (Q : Set A) :=
    Set.disjoint_left.mpr fun x ⟨n, hn⟩ hxQ => hfQ (‹Q.IsPrime›.mem_of_pow_mem n
      (by rw [show f ^ n = x from hn]; exact hxQ))
  let B := Localization.Away f
  let ιB : A →+* B := algebraMap A B
  have : IsRegularRing B := isRegularRing_of_isLocalization (Submonoid.powers f)
  have : (Q.map ιB).IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint (Submonoid.powers f) B Q ‹Q.IsPrime› hdisj
  have hQB : (Q.map ιB).comap ιB = Q :=
    IsLocalization.under_map_of_isPrime_disjoint (Submonoid.powers f) B ‹Q.IsPrime› hdisj
  have : IsRegularRing (B ⧸ Q.map ιB) :=
    isRegularRing_of_isLocalization (Algebra.algebraMapSubmonoid (A ⧸ Q)
      (Submonoid.powers f))
  refine thm2Conclusion_of_away J Q f hfQ ?_
  -- the standard base `(f_j)` of `JA_Q` is one of `(JA[f⁻¹])(A[f⁻¹])_{QA[f⁻¹]}` (`(A_f)_{Q_f} = A_Q`)
  have hSBB : IsStandardBase (Localization.AtPrime (Q.map ιB))
      ((J.map ιB).map (algebraMap B (Localization.AtPrime (Q.map ιB))))
      fun j => algebraMap B (Localization.AtPrime (Q.map ιB)) (ιB (F j)) := by
    have key := isStandardBase_ringEquiv (locLocEquiv (Submonoid.powers f) (Q.map ιB) Q hQB)
      (J.map (algebraMap A (Localization.AtPrime Q))) (fun j => algebraMap A _ (F j)) hSB
    have hfun : (fun j => locLocEquiv (Submonoid.powers f) (Q.map ιB) Q hQB
        (algebraMap A (Localization.AtPrime Q) (F j))) =
        fun j => algebraMap B (Localization.AtPrime (Q.map ιB)) (ιB (F j)) :=
      funext fun j => locLocEquiv_algebraMap _ _ _ hQB _
    have hid : (J.map (algebraMap A (Localization.AtPrime Q))).map
        (locLocEquiv (Submonoid.powers f) (Q.map ιB) Q hQB : _ →+* _) =
        (J.map ιB).map (algebraMap B (Localization.AtPrime (Q.map ιB))) := by
      rw [Ideal.map_map, Ideal.map_map]
      congr 1
      exact RingHom.ext fun a => locLocEquiv_algebraMap _ _ _ hQB a
    rw [hid] at key
    exact hfun ▸ key
  -- `gr_{QA[f⁻¹]}(JA[f⁻¹]) = (Φ₁, …, Φ_m) gr_{QA[f⁻¹]}(A[f⁻¹])`
  have hHB : grIdeal (Q.map ιB) (J.map ιB) =
      Ideal.span (Set.range fun j => initialForm (Q.map ιB) (ιB (F j))) := by
    have hM : Submonoid.powers f ≤ Q.primeCompl := fun x ⟨n, hn⟩ hxQ =>
      hfQ (‹Q.IsPrime›.mem_of_pow_mem n (by rw [show f ^ n = x from hn]; exact hxQ))
    apply le_antisymm
    · refine (grIdeal_map_le_map_grIdeal (Submonoid.powers f) Q J).trans ?_
      rw [Ideal.map_le_iff_le_comap]
      intro x hx
      rw [Ideal.mem_comap]
      set σ := AssocGraded.map ιB Q
      have h1 := Ideal.mem_map_of_mem σ (hf x hx)
      have hσf : σ (algebraMap A (AssocGraded Q) f) =
          algebraMap B (AssocGraded (Q.map ιB)) (ιB f) := by
        rw [algebraMap_eq_mk_zero, algebraMap_eq_mk_zero, AssocGraded.map_mk]
      rw [map_mul, hσf, Ideal.map_span, ← Set.range_comp] at h1
      have hunit : IsUnit (algebraMap B (AssocGraded (Q.map ιB)) (ιB f)) :=
        (IsLocalization.map_units B (⟨f, Submonoid.mem_powers f⟩ : Submonoid.powers f)).map _
      have hspan : Set.range (σ ∘ fun j => initialForm Q (F j)) =
          Set.range fun j => initialForm (Q.map ιB) (ιB (F j)) := by
        congr 1
        funext j
        exact map_initialForm_of_ordElem_eq ιB Q (F j) (ordElem_map_eq_of_le Q _ hM (F j))
      rw [hspan] at h1
      exact (Ideal.unit_mul_mem_iff_mem _ hunit).mp h1
    · rw [Ideal.span_le]
      rintro _ ⟨j, rfl⟩
      exact Ideal.subset_span ⟨ιB (F j), Ideal.mem_map_of_mem _ (hFJ j), rfl⟩
  exact exists_open_nuStar_localization_eq_of_gr_eq B (J.map ιB) (Q.map ιB) (Ideal.map_mono hJQ)
    (fun j => ιB (F j)) (fun j => Ideal.mem_map_of_mem _ (hFJ j)) hSBB hHB

/-! ### Proofs of Corollaries 1 and 2: generic constancy of `ν*` and noetherian induction

Neither corollary is proved in the paper.  The argument is the standard one: by Theorem 2, on
the closure of every point `η` the function `x ↦ ν*(J_x)` is constant on a neighbourhood of `η`
(Theorem 2 needs `A/Q` regular; by (iii) of p. 161, `prop:class-A-iii`, the regular locus of
`A/Q` is open, and it contains the generic point, so we may shrink to it), and noetherian
induction on the closed subsets of `X` then gives constructibility; for Corollary 1, Theorem 1
(`ν(J_x)` does not increase under generization) upgrades this to openness. -/

section Corollaries

open Topology

/-! ### `ν*` of the unit ideal, and invariance of `ν*` under isomorphisms -/

section NuStarTop

variable (R : Type u) [CommRing R] [IsRegularLocalRing R]

private theorem ordElem_one : Ideal.ordElem (maximalIdeal R) (1 : R) = 0 :=
  le_antisymm (Ideal.ordElem_le_of_notMem (m := 0) (by simp)) (by simp)

private theorem initialForm_one : initialForm (maximalIdeal R) (1 : R) = 1 := by
  have h0 := ordElem_one R
  unfold initialForm
  split_ifs with h
  · rw [h0] at h; exact absurd h ENat.zero_ne_top
  · simp only [h0, ENat.toNat_zero]
    rfl

private theorem grIdeal_top : grIdeal (maximalIdeal R) (⊤ : Ideal R) = ⊤ :=
  (Ideal.eq_top_iff_one _).mpr
    (Ideal.subset_span ⟨1, Submodule.mem_top, initialForm_one R⟩)

private theorem one_mem_homogeneous_zero :
    (1 : AssocGraded (maximalIdeal R)) ∈ AssocGraded.homogeneous (maximalIdeal R) 0 := by
  have : (1 : AssocGraded (maximalIdeal R)) = AssocGraded.mk _ 0 1 (by simp) := rfl
  rw [this]
  exact AssocGraded.mk_mem_homogeneous _ _

private theorem nuI_top_one : nuI R (⊤ : Ideal R) 1 = 0 := by
  rw [(nuI_one_eq_nu_and_nuI_two_and_nuI_le_nuParen R ⊤).1.1]
  exact le_antisymm ((iInf₂_le 1 Submodule.mem_top).trans (ordElem_one R).le) (by simp)

private theorem nuI_top_of_ne_one {i : ℕ+} (hi : i ≠ 1) : nuI R (⊤ : Ideal R) i = ⊤ := by
  have hi' : 1 ≤ (i : ℕ) - 1 := by
    have h2 : ((1 : ℕ+) : ℕ) < i :=
      PNat.coe_lt_coe _ _ |>.mpr (lt_of_le_of_ne (one_le (a := i)) (Ne.symm hi))
    rw [PNat.one_coe] at h2
    omega
  have hsys : ∀ ν : ℕ, IsNuSystem R ⊤ ν ((i : ℕ) - 1) fun _ => 1 := by
    intro ν
    refine ⟨fun _ => ⟨by rw [grIdeal_top]; exact Submodule.mem_top,
      0, one_mem_homogeneous_zero R⟩, fun μ _ ψ _ => ?_⟩
    have hspan : Ideal.span (Set.range fun _ : Fin ((i : ℕ) - 1) =>
        (1 : AssocGraded (maximalIdeal R))) = ⊤ :=
      (Ideal.eq_top_iff_one _).mpr (Ideal.subset_span ⟨⟨0, hi'⟩, rfl⟩)
    rw [hspan, grIdeal_top]
  refine ENat.eq_top_iff_forall_ge.mpr fun m => ?_
  exact le_iSup₂_of_le (f := fun (ν : ℕ) (_ : ∃ φ : Fin ((i : ℕ) - 1) → AssocGraded
    (maximalIdeal R), IsNuSystem R ⊤ ν ((i : ℕ) - 1) φ) => (ν : ℕ∞)) m ⟨_, hsys m⟩ le_rfl

/-- `ν*(R) = (0, ∞, ∞, …)` for the unit ideal, independently of `R`. -/
private theorem nuStar_top :
    nuStar R (⊤ : Ideal R) = toLex (fun i : ℕ+ => if i = 1 then (0 : ℕ∞) else ⊤) := by
  refine congrArg toLex (funext fun i => ?_)
  split_ifs with hi
  · rw [hi]; exact nuI_top_one R
  · exact nuI_top_of_ne_one R hi

end NuStarTop

/-- The localization of a domain at its zero ideal is a field, hence a regular local ring. -/
private theorem isRegularLocalRing_atBot {B : Type u} [CommRing B] [IsDomain B] :
    IsRegularLocalRing (Localization.AtPrime (⊥ : Ideal B)) := by
  let : Field (Localization.AtPrime (⊥ : Ideal B)) := IsField.toField <| by
    simp [isField_iff_maximalIdeal_eq, ← Localization.AtPrime.map_eq_maximalIdeal]
  infer_instance

/-- The local form of the generic constancy of `ν*` along an irreducible closed set (Theorem 2
with the regularity of `A/Q` imposed only on an open set): for a noetherian ring `A` all of whose
local rings are regular, an ideal `J` and a prime `Q` such that the regular locus of `A/Q` is
open, there is an open neighbourhood `T` of `Q` in `Spec A` such that `ν*(JA_P) = ν*(JA_Q)` for
every `P ∈ T` with `P ⊇ Q`.  (Neither corollary is proved in the paper.  Shrink to a basic open set
`D(ā)` of `Spec(A/Q)` inside the regular locus and containing `Q`, apply Theorem 2 to `A[a⁻¹]` and
descend, as in the proof of Theorem 2 itself.) -/
private theorem generic_nuStar_local {A : Type u} [CommRing A] [IsNoetherianRing A]
    (hreg : ∀ P : PrimeSpectrum A, IsRegularLocalRing (Localization.AtPrime P.asIdeal))
    (J : Ideal A) (Q : PrimeSpectrum A) (hopen : IsOpen (regularLocus (A ⧸ Q.asIdeal))) :
    ∃ T : Set (PrimeSpectrum A), IsOpen T ∧ Q ∈ T ∧ ∀ P ∈ T, Q ≤ P →
      @nuStar _ _ (hreg P) (J.map (algebraMap A (Localization.AtPrime P.asIdeal))) =
        @nuStar _ _ (hreg Q) (J.map (algebraMap A (Localization.AtPrime Q.asIdeal))) := by
  classical
  by_cases hJQ : J ≤ Q.asIdeal
  · have := hreg Q
    have : IsRegularRing A := ⟨fun p hp => hreg ⟨p, hp⟩⟩
    have hQdom : IsDomain (A ⧸ Q.asIdeal) := Ideal.Quotient.isDomain _
    -- "Theorem 2 needs `A/Q` regular": shrink to a basic open set `D(ā) ∋ Q` of `Spec(A/Q)` inside
    -- the regular locus, and replace `A` by `A[a⁻¹]`, as in the proof of Theorem 2 (p. 220)
    let P₀ : PrimeSpectrum (A ⧸ Q.asIdeal) := ⟨⊥, Ideal.isPrime_bot⟩
    have hreg0 : P₀ ∈ regularLocus (A ⧸ Q.asIdeal) := isRegularLocalRing_atBot
    obtain ⟨_, ⟨ā, rfl⟩, hP₀ā, hāreg⟩ :=
      PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open hreg0 hopen
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective ā
    have haQ : a ∉ Q.asIdeal := fun h => by
      have : Ideal.Quotient.mk Q.asIdeal a ∈ P₀.asIdeal := by
        rw [Ideal.mem_bot]
        exact Ideal.Quotient.eq_zero_iff_mem.mpr h
      exact hP₀ā this
    have hdisj : Disjoint ((Submonoid.powers a : Submonoid A) : Set A) (Q.asIdeal : Set A) :=
      Set.disjoint_left.mpr fun x ⟨n, hn⟩ hxQ => haQ (Q.isPrime.mem_of_pow_mem n
        (by rw [show a ^ n = x from hn]; exact hxQ))
    let B := Localization.Away a
    let ιB : A →+* B := algebraMap A B
    have : IsRegularRing B := isRegularRing_of_isLocalization (Submonoid.powers a)
    have : (Q.asIdeal.map ιB).IsPrime :=
      IsLocalization.isPrime_of_isPrime_disjoint (Submonoid.powers a) B Q.asIdeal Q.isPrime hdisj
    have : IsRegularRing (B ⧸ Q.asIdeal.map ιB) :=
      isRegularRing_of_isLocalization_of_forall (A := A ⧸ Q.asIdeal)
        (Algebra.algebraMapSubmonoid (A ⧸ Q.asIdeal) (Submonoid.powers a)) fun q hq hqd =>
        hāreg (show (⟨q, hq⟩ : PrimeSpectrum (A ⧸ Q.asIdeal)) ∈
          (PrimeSpectrum.basicOpen (Ideal.Quotient.mk Q.asIdeal a) : Set _) from
          fun hmem => Set.disjoint_left.mp hqd ⟨a, Submonoid.mem_powers a, rfl⟩ hmem)
    -- Theorem 2 for `(A[a⁻¹], JA[a⁻¹], QA[a⁻¹])`, hence for `(A, J, Q)` on a non-empty open set
    obtain ⟨U, hUo, hUne, hU⟩ := thm2Conclusion_of_away J Q.asIdeal a haQ
      (exists_open_nuStar_localization_eq B (J.map ιB) (Q.asIdeal.map ιB) (Ideal.map_mono hJQ))
    -- `Spec(A/Q)` is a closed subspace of `Spec A`; the generic point lies in every non-empty open
    obtain ⟨T, hT, hTeq⟩ := (PrimeSpectrum.isClosedEmbedding_comap_of_surjective _ _
      (Ideal.Quotient.mk_surjective (I := Q.asIdeal))).isInducing.isOpen_iff.mp hUo
    have hP₀U : P₀ ∈ U := by
      obtain ⟨x, hx⟩ := hUne
      exact ((PrimeSpectrum.le_iff_specializes P₀ x).mp bot_le).mem_open hUo hx
    have hP₀Q : PrimeSpectrum.comap (Ideal.Quotient.mk Q.asIdeal) P₀ = Q := by
      ext a
      show Ideal.Quotient.mk Q.asIdeal a ∈ (⊥ : Ideal _) ↔ a ∈ Q.asIdeal
      rw [Ideal.mem_bot, Ideal.Quotient.eq_zero_iff_mem]
    refine ⟨T, hT, ?_, ?_⟩
    · have h0 : PrimeSpectrum.comap (Ideal.Quotient.mk Q.asIdeal) P₀ ∈ T := by
        rw [← Set.mem_preimage, hTeq]
        exact hP₀U
      rwa [hP₀Q] at h0
    · rintro P hPT hQP
      have := hreg P
      have hlift : ∃ pb : PrimeSpectrum (A ⧸ Q.asIdeal),
          PrimeSpectrum.comap (Ideal.Quotient.mk Q.asIdeal) pb = P := by
        have : P ∈ Set.range (PrimeSpectrum.comap (Ideal.Quotient.mk Q.asIdeal)) := by
          rw [_root_.range_comap_of_surjective (f := Ideal.Quotient.mk Q.asIdeal)
            (hf := Ideal.Quotient.mk_surjective), Ideal.mk_ker]
          exact hQP
        exact this
      obtain ⟨pb, hpb⟩ := hlift
      have hpbU : pb ∈ U := by
        rw [← hTeq, Set.mem_preimage, hpb]
        exact hPT
      subst hpb
      exact hU pb hpbU
  · -- `J ⊄ Q`: near `Q` the ideal `J` generates the unit ideal
    obtain ⟨a, haJ, haQ⟩ := Set.not_subset.mp hJQ
    have htop : ∀ P : PrimeSpectrum A, a ∉ P.asIdeal →
        J.map (algebraMap A (Localization.AtPrime P.asIdeal)) = ⊤ := by
      intro P haP
      refine Ideal.eq_top_of_isUnit_mem _ (Ideal.mem_map_of_mem _ haJ) ?_
      exact IsLocalization.map_units (Localization.AtPrime P.asIdeal)
        (⟨a, haP⟩ : P.asIdeal.primeCompl)
    refine ⟨PrimeSpectrum.basicOpen a, (PrimeSpectrum.basicOpen a).isOpen, haQ, ?_⟩
    intro P hP _
    rw [htop P hP, htop Q haQ, @nuStar_top _ _ (hreg P), @nuStar_top _ _ (hreg Q)]

/-- `ν` is invariant under ring isomorphisms of regular local rings. -/
private theorem nu_ringEquiv {A B : Type u} [CommRing A] [IsRegularLocalRing A]
    [CommRing B] [IsRegularLocalRing B] (e : A ≃+* B) (I : Ideal A) :
    Ideal.nu (I.map (e : A →+* B)) = Ideal.nu I := by
  rw [← (nuI_one_eq_nu_and_nuI_two_and_nuI_le_nuParen B _).1.2,
    ← (nuI_one_eq_nu_and_nuI_two_and_nuI_le_nuParen A I).1.2]
  exact congrArg (fun f : Lex (ℕ+ → ℕ∞) => ofLex f 1) (nuStar_ringEquiv e I)

/-- Theorem 1 in the form used for Corollary 1: for primes `P' ⊆ P` of a ring all of whose local
rings are regular, `ν(IA_{P'}) ≤ ν(IA_P)`. -/
private theorem nu_localization_mono [Hironaka.Cited.CurveFiniteIntegralClosure.{u}] [Hironaka.Cited.IsRegularLocalRingLocalizationOfIsRegularLocalRing.{u}] {A : Type u} [CommRing A]
    (hreg : ∀ P : PrimeSpectrum A, IsRegularLocalRing (Localization.AtPrime P.asIdeal))
    (I : Ideal A) {P' P : PrimeSpectrum A} (hle : P' ≤ P) :
    Ideal.nu (I.map (algebraMap A (Localization.AtPrime P'.asIdeal))) ≤
      Ideal.nu (I.map (algebraMap A (Localization.AtPrime P.asIdeal))) := by
  classical
  have := hreg P
  have := hreg P'
  let R := Localization.AtPrime P.asIdeal
  let IR := I.map (algebraMap A R)
  by_cases hI : IR = ⊥
  · have : Ideal.nu IR = ⊤ := by
      rw [hI]
      exact ((Ideal.ord_basic _ _ ⊥ ⊥).1).mpr fun _ => bot_le
    exact this ▸ le_top
  -- the prime `P'R` of `R`, and `R_{P'R} ≅ A_{P'}`
  let p : Ideal R := P'.asIdeal.map (algebraMap A R)
  have hdisj : Disjoint (P.asIdeal.primeCompl : Set A) P'.asIdeal := by
    rw [Set.disjoint_left]
    intro a ha haP'
    exact ha (hle haP')
  have hp : p.IsPrime := IsLocalization.isPrime_of_isPrime_disjoint P.asIdeal.primeCompl R
    P'.asIdeal P'.isPrime hdisj
  have hcomap : p.comap (algebraMap A R) = P'.asIdeal :=
    IsLocalization.under_map_of_isPrime_disjoint P.asIdeal.primeCompl R P'.isPrime hdisj
  let T := Localization.AtPrime p
  have hT : IsLocalization.AtPrime T (p.comap (algebraMap A R)) :=
    IsLocalization.isLocalization_isLocalization_atPrime_isLocalization P.asIdeal.primeCompl T p
  have hM : (p.comap (algebraMap A R)).primeCompl = P'.asIdeal.primeCompl := by
    ext a
    rw [Ideal.mem_primeCompl_iff, Ideal.mem_primeCompl_iff, hcomap]
  have hT' : IsLocalization P'.asIdeal.primeCompl T := by
    rw [← hM]; exact hT
  let e : Localization.AtPrime P'.asIdeal ≃ₐ[A] T :=
    IsLocalization.algEquiv P'.asIdeal.primeCompl (Localization.AtPrime P'.asIdeal) T
  have : IsRegularLocalRing T := IsRegularLocalRing.of_ringEquiv e.toRingEquiv
  have h1 : (I.map (algebraMap A (Localization.AtPrime P'.asIdeal))).map
      (e.toRingEquiv : Localization.AtPrime P'.asIdeal →+* T) =
      IR.map (algebraMap R T) := by
    rw [Ideal.map_map, Ideal.map_map, ← IsScalarTower.algebraMap_eq]
    congr 1
    exact RingHom.ext fun a => e.commutes a
  rw [← nu_ringEquiv e.toRingEquiv, h1]
  exact nu_localization_le R IR hI p

/-- The stalk of `O_X` at the point `P` of an affine open `W` is `Γ(X, W)_P`, and the stalk of
`J` corresponds to `J(W)_P`: hence `ν*(J_x) = ν*(J(W)Γ(X, W)_P)`. -/
private theorem nuStar_stalk_eq {X : Scheme.{u}} (hX : X.IsNonsingular) (J : Subscheme X)
    (W : X.affineOpens)
    (hreg : ∀ P : PrimeSpectrum Γ(X, W), IsRegularLocalRing (Localization.AtPrime P.asIdeal))
    (P : PrimeSpectrum Γ(X, W)) :
    @nuStar _ _ (hX (W.2.fromSpec P)) (J.stalkIdeal (W.2.fromSpec P)) =
      @nuStar _ _ (hreg P)
        ((J.ideal W).map (algebraMap Γ(X, W) (Localization.AtPrime P.asIdeal))) := by
  have hy : W.2.fromSpec P ∈ (W : X.Opens) := by
    rw [← SetLike.mem_coe, ← W.2.range_fromSpec]; exact ⟨P, rfl⟩
  let := TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨W.2.fromSpec P, hy⟩
  have hloc : IsLocalization P.asIdeal.primeCompl (X.presheaf.stalk (W.2.fromSpec P)) :=
    W.2.isLocalization_stalk' P hy
  let e := IsLocalization.algEquiv (R := Γ(X, W)) P.asIdeal.primeCompl
    (Localization.AtPrime P.asIdeal) (X.presheaf.stalk (W.2.fromSpec P))
  have := hreg P
  have : IsRegularLocalRing (X.presheaf.stalk (W.2.fromSpec P)) := hX (W.2.fromSpec P)
  have h1 : ((J.ideal W).map (algebraMap Γ(X, W) (Localization.AtPrime P.asIdeal))).map
      (e.toRingEquiv : Localization.AtPrime P.asIdeal →+* X.presheaf.stalk (W.2.fromSpec P)) =
        J.stalkIdeal (W.2.fromSpec P) := by
    rw [Ideal.map_map, Subscheme.stalkIdeal_eq_map_germ_affine J W hy]
    congr 1
    exact RingHom.ext fun a => e.commutes a
  rw [← h1]
  exact nuStar_ringEquiv e.toRingEquiv _

/-- `ν(J_x) = ν^{(1)}(J_x)`, the first term of `ν*(J_x)`. -/
private theorem nu_eq_nuStar_one {X : Scheme.{u}} (hX : X.IsNonsingular) (J : Subscheme X)
    (x : X) : Ideal.nu (J.stalkIdeal x) = ofLex (@nuStar _ _ (hX x) (J.stalkIdeal x)) 1 := by
  have : IsRegularLocalRing (X.presheaf.stalk x) := hX x
  exact ((nuI_one_eq_nu_and_nuI_two_and_nuI_le_nuParen _ (J.stalkIdeal x)).1.2).symm

/-- The affine charts of an algebraic scheme: the ring of sections is noetherian, all its local
rings are regular (if `X` is non-singular), and the regular locus of each of its quotients is
open (by (iii), p. 161). -/
private theorem affine_chart [Hironaka.Cited.IsHironakaBaseIsClosedSingularLocus.{u}] {X : Scheme.{u}} [IsAlgebraicScheme X] (hX : X.IsNonsingular)
    (W : X.affineOpens) :
    IsNoetherianRing Γ(X, W) ∧
      (∀ P : PrimeSpectrum Γ(X, W), IsRegularLocalRing (Localization.AtPrime P.asIdeal)) ∧
      ∀ I : Ideal Γ(X, W), IsOpen (regularLocus (Γ(X, W) ⧸ I)) := by
  have := IsAlgebraicScheme.isNoetherian X
  refine ⟨IsLocallyNoetherian.component_noetherian W,
    fun P => (isSimpleAt_fromSpec_iff W.2 P).mp (hX _), fun I => ?_⟩
  obtain ⟨S, i1, i2, i3, p, hp, -⟩ := IsAlgebraicScheme.exists_base (X := X)
  let φ : S →+* Γ(X, W) :=
    (p.appLE ⊤ W le_top).hom.comp (Scheme.ΓSpecIso (CommRingCat.of S)).inv.hom
  let : Algebra S Γ(X, W) := φ.toAlgebra
  have hφ : φ.FiniteType := by
    refine RingHom.FiniteType.comp ?_ (RingHom.FiniteType.of_surjective _ ?_)
    · exact HasRingHomProperty.appLE @LocallyOfFiniteType p hp
        ⟨⊤, isAffineOpen_top _⟩ W le_top
    · exact (Scheme.ΓSpecIso (CommRingCat.of S)).commRingCatIsoToRingEquiv.symm.surjective
  have : Algebra.FiniteType S Γ(X, W) := hφ
  have : Algebra.FiniteType S (Γ(X, W) ⧸ I) :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ S I)
      (Ideal.Quotient.mkₐ_surjective S I)
  exact isClosed_compl_iff.mp (IsHironakaBase.isClosed_singularLocus S (Γ(X, W) ⧸ I))

/-- Generic constancy of `ν*(J_x)` along the closure of a point (Theorem 2, globalized): every
point `η` has an open neighbourhood `V` such that `ν*(J_x) = ν*(J_η)` for all specializations
`x ∈ V` of `η`. -/
private theorem generic_nuStar [Hironaka.Cited.IsHironakaBaseIsClosedSingularLocus.{u}] {X : Scheme.{u}} [IsAlgebraicScheme X] (hX : X.IsNonsingular)
    (J : Subscheme X) (η : X) :
    ∃ V : Set X, IsOpen V ∧ η ∈ V ∧ ∀ x ∈ V, η ⤳ x →
      @nuStar _ _ (hX x) (J.stalkIdeal x) = @nuStar _ _ (hX η) (J.stalkIdeal η) := by
  obtain ⟨W, hηW⟩ := Subscheme.exists_affineOpen_mem η
  obtain ⟨Q, rfl⟩ : ∃ Q, W.2.fromSpec Q = η := ⟨_, W.2.fromSpec_primeIdealOf ⟨η, hηW⟩⟩
  obtain ⟨hnoeth, hreg, hopen⟩ := affine_chart hX W
  have := W.2.isOpenImmersion_fromSpec
  obtain ⟨T, hT, hQT, hTeq⟩ := generic_nuStar_local hreg (J.ideal W) Q (hopen Q.asIdeal)
  refine ⟨W.2.fromSpec '' T, W.2.fromSpec.isOpenEmbedding.isOpenMap _ hT, ⟨Q, hQT, rfl⟩, ?_⟩
  rintro x ⟨P, hPT, rfl⟩ hsp
  have hQP : @LE.le (PrimeSpectrum Γ(X, W)) _ Q P :=
    (PrimeSpectrum.le_iff_specializes (Q : PrimeSpectrum Γ(X, W)) P).mpr
      (W.2.fromSpec.isOpenEmbedding.isInducing.specializes_iff.mp hsp)
  rw [nuStar_stalk_eq hX J W hreg P, nuStar_stalk_eq hX J W hreg Q]
  exact hTeq P hPT hQP

/-- Theorem 1 globalized: `ν(J_y) ≤ ν(J_x)` whenever `y` is a generization of `x`. -/
private theorem nu_stalk_generization [Hironaka.Cited.IsHironakaBaseIsClosedSingularLocus.{u}] [Hironaka.Cited.CurveFiniteIntegralClosure.{u}] [Hironaka.Cited.IsRegularLocalRingLocalizationOfIsRegularLocalRing.{u}] {X : Scheme.{u}} [IsAlgebraicScheme X]
    (hX : X.IsNonsingular) (J : Subscheme X) {x y : X} (hyx : y ⤳ x) :
    Ideal.nu (J.stalkIdeal y) ≤ Ideal.nu (J.stalkIdeal x) := by
  obtain ⟨W, hxW⟩ := Subscheme.exists_affineOpen_mem x
  have hyW : y ∈ (W : X.Opens) := hyx.mem_open (W : X.Opens).isOpen hxW
  obtain ⟨P, rfl⟩ : ∃ P, W.2.fromSpec P = x := ⟨_, W.2.fromSpec_primeIdealOf ⟨x, hxW⟩⟩
  obtain ⟨P', rfl⟩ : ∃ P', W.2.fromSpec P' = y := ⟨_, W.2.fromSpec_primeIdealOf ⟨y, hyW⟩⟩
  obtain ⟨-, hreg, -⟩ := affine_chart hX W
  have := W.2.isOpenImmersion_fromSpec
  have hle : @LE.le (PrimeSpectrum Γ(X, W)) _ P' P :=
    (PrimeSpectrum.le_iff_specializes (P' : PrimeSpectrum Γ(X, W)) P).mpr
      (W.2.fromSpec.isOpenEmbedding.isInducing.specializes_iff.mp hyx)
  rw [nu_eq_nuStar_one hX J, nu_eq_nuStar_one hX J, nuStar_stalk_eq hX J W hreg P,
    nuStar_stalk_eq hX J W hreg P']
  have h := nu_localization_mono hreg (J.ideal W) hle
  have := hreg P
  have := hreg P'
  rwa [← (nuI_one_eq_nu_and_nuI_two_and_nuI_le_nuParen _ _).1.2,
    ← (nuI_one_eq_nu_and_nuI_two_and_nuI_le_nuParen _ _).1.2] at h

/-- Noetherian induction on the closed subsets of a noetherian space. -/
private theorem closed_induction {X : Type*} [TopologicalSpace X] [TopologicalSpace.NoetherianSpace X]
    (p : Set X → Prop)
    (h : ∀ Z : Set X, IsClosed Z → (∀ Z' : Set X, IsClosed Z' → Z' ⊂ Z → p Z') → p Z)
    (Z : Set X) (hZ : IsClosed Z) : p Z := by
  let q : TopologicalSpace.Closeds X → Prop := fun C => p C
  have : ∀ C : TopologicalSpace.Closeds X, q C := by
    intro C
    induction C using WellFoundedLT.induction with
    | _ C ih =>
      refine h C C.isClosed fun Z' hZ' hlt => ?_
      exact ih ⟨Z', hZ'⟩ (by
        show (⟨Z', hZ'⟩ : TopologicalSpace.Closeds X) < C
        rw [← SetLike.coe_ssubset_coe]
        exact hlt)
  exact this ⟨Z, hZ⟩

/-- The inductive step for a closed set which is not irreducible: it is the union of two proper
closed subsets. -/
private theorem exists_proper_cover {X : Type*} [TopologicalSpace X] {Z : Set X} (hZ : IsClosed Z)
    (hne : Z.Nonempty) (hirr : ¬ IsIrreducible Z) :
    ∃ Z₁ Z₂ : Set X, IsClosed Z₁ ∧ IsClosed Z₂ ∧ Z₁ ⊂ Z ∧ Z₂ ⊂ Z ∧ Z = Z₁ ∪ Z₂ := by
  have hpre : ¬ IsPreirreducible Z := fun h => hirr ⟨hne, h⟩
  rw [isPreirreducible_iff_isClosed_union_isClosed] at hpre
  push Not at hpre
  obtain ⟨z₁, z₂, h₁, h₂, hsub, hn₁, hn₂⟩ := hpre
  refine ⟨Z ∩ z₁, Z ∩ z₂, hZ.inter h₁, hZ.inter h₂, ?_, ?_, ?_⟩
  · exact Set.ssubset_iff_subset_ne.mpr ⟨Set.inter_subset_left,
      fun h => hn₁ (by rw [← h]; exact Set.inter_subset_right)⟩
  · exact Set.ssubset_iff_subset_ne.mpr ⟨Set.inter_subset_left,
      fun h => hn₂ (by rw [← h]; exact Set.inter_subset_right)⟩
  · rw [← Set.inter_union_distrib_left, Set.inter_eq_left.mpr hsub]

/-- A set `S` in a noetherian quasi-sober space is open as soon as it is stable under
generization and, for every point `η ∈ S`, contains all specializations of `η` in some open
neighbourhood of `η`. -/
private theorem isOpen_of_generic {X : Type*} [TopologicalSpace X] [TopologicalSpace.NoetherianSpace X]
    [QuasiSober X] (S : Set X) (hgen : ∀ x y : X, y ⤳ x → x ∈ S → y ∈ S)
    (hloc : ∀ η ∈ S, ∃ V : Set X, IsOpen V ∧ η ∈ V ∧ ∀ x ∈ V, η ⤳ x → x ∈ S) : IsOpen S := by
  suffices h : IsClosed (Set.univ \ S) by
    rw [← Set.compl_eq_univ_sdiff] at h
    exact isClosed_compl_iff.mp h
  refine closed_induction (fun Z => IsClosed (Z \ S)) (fun Z hZ ih => ?_) _ isClosed_univ
  rcases Z.eq_empty_or_nonempty with hZe | hne
  · rw [hZe, Set.empty_sdiff]; exact isClosed_empty
  by_cases hirr : IsIrreducible Z
  · obtain ⟨η, hη⟩ := QuasiSober.sober hirr hZ
    by_cases hηS : η ∈ S
    · obtain ⟨V, hV, hηV, hVS⟩ := hloc η hηS
      have hsub : Z ∩ Vᶜ ⊂ Z := Set.ssubset_iff_subset_ne.mpr ⟨Set.inter_subset_left,
        fun h => (h.ge hη.mem).2 hηV⟩
      have := ih _ (hZ.inter hV.isClosed_compl) hsub
      convert this using 1
      ext z
      simp only [Set.mem_sdiff, Set.mem_inter_iff, Set.mem_compl_iff]
      constructor
      · rintro ⟨hz, hzS⟩
        refine ⟨⟨hz, fun hzV => hzS (hVS z hzV ?_)⟩, hzS⟩
        exact hη.specializes hz
      · rintro ⟨⟨hz, -⟩, hzS⟩
        exact ⟨hz, hzS⟩
    · convert hZ using 1
      exact Set.ext fun z => ⟨fun h => h.1,
        fun hz => ⟨hz, fun hzS => hηS (hgen z η (hη.specializes hz) hzS)⟩⟩
  · obtain ⟨Z₁, Z₂, h₁, h₂, hs₁, hs₂, rfl⟩ := exists_proper_cover hZ hne hirr
    rw [Set.union_sdiff_distrib]
    exact (ih _ h₁ hs₁).union (ih _ h₂ hs₂)

/-- A set `S` in a noetherian quasi-sober space is constructible as soon as, for every point
`η`, membership in `S` is constant on the specializations of `η` in some open neighbourhood of
`η`. -/
private theorem isConstructible_of_generic {X : Type*} [TopologicalSpace X]
    [TopologicalSpace.NoetherianSpace X] [QuasiSober X] [QuasiSeparatedSpace X] (S : Set X)
    (hloc : ∀ η : X, ∃ V : Set X, IsOpen V ∧ η ∈ V ∧ ∀ x ∈ V, η ⤳ x → (x ∈ S ↔ η ∈ S)) :
    Topology.IsConstructible S := by
  have hopen : ∀ V : Set X, IsOpen V → Topology.IsConstructible V := fun V hV =>
    (TopologicalSpace.NoetherianSpace.isCompact V).isConstructible hV
  have hclosed : ∀ Z : Set X, IsClosed Z → Topology.IsConstructible Z := fun Z hZ => by
    rw [← compl_compl Z, isConstructible_compl]
    exact hopen _ hZ.isOpen_compl
  suffices h : Topology.IsConstructible (Set.univ ∩ S) by rwa [Set.univ_inter] at h
  refine closed_induction (fun Z => Topology.IsConstructible (Z ∩ S)) (fun Z hZ ih => ?_) _
    isClosed_univ
  rcases Z.eq_empty_or_nonempty with hZe | hne
  · rw [hZe, Set.empty_inter]; exact Topology.IsConstructible.empty
  by_cases hirr : IsIrreducible Z
  · obtain ⟨η, hη⟩ := QuasiSober.sober hirr hZ
    obtain ⟨V, hV, hηV, hVS⟩ := hloc η
    have hsub : Z ∩ Vᶜ ⊂ Z := Set.ssubset_iff_subset_ne.mpr ⟨Set.inter_subset_left,
      fun h => (h.ge hη.mem).2 hηV⟩
    have h1 := ih _ (hZ.inter hV.isClosed_compl) hsub
    have hsplit : Z ∩ S = (Z ∩ V ∩ {_z | η ∈ S}) ∪ (Z ∩ Vᶜ ∩ S) := by
      ext z
      simp only [Set.mem_inter_iff, Set.mem_union, Set.mem_compl_iff, Set.mem_ofPred_eq]
      by_cases hzV : z ∈ V
      · have := hVS z hzV
        constructor
        · rintro ⟨hz, hzS⟩
          exact Or.inl ⟨⟨hz, hzV⟩, (this (hη.specializes hz)).mp hzS⟩
        · rintro (⟨⟨hz, -⟩, hS⟩ | ⟨⟨-, h⟩, -⟩)
          · exact ⟨hz, (this (hη.specializes hz)).mpr hS⟩
          · exact absurd hzV h
      · constructor
        · rintro ⟨hz, hzS⟩
          exact Or.inr ⟨⟨hz, hzV⟩, hzS⟩
        · rintro (⟨⟨-, h⟩, -⟩ | ⟨⟨hz, -⟩, hS⟩)
          · exact absurd h hzV
          · exact ⟨hz, hS⟩
    rw [hsplit]
    refine Topology.IsConstructible.union ?_ h1
    by_cases hηS : η ∈ S
    · have : {_z : X | η ∈ S} = Set.univ := Set.eq_univ_of_forall fun _ => hηS
      rw [this, Set.inter_univ]
      exact (hclosed Z hZ).inter (hopen V hV)
    · have : {_z : X | η ∈ S} = ∅ := Set.eq_empty_of_forall_notMem fun _ => hηS
      rw [this, Set.inter_empty]
      exact Topology.IsConstructible.empty
  · obtain ⟨Z₁, Z₂, h₁, h₂, hs₁, hs₂, rfl⟩ := exists_proper_cover hZ hne hirr
    rw [Set.union_inter_distrib_right]
    exact (ih _ h₁ hs₁).union (ih _ h₂ hs₂)

end Corollaries

/-! ### Corollaries 1 and 2 of Theorem 2 (p. 220) -/

/-- Corollary 1 of Theorem 2, p. 220: "Let `X` be a non-singular algebraic scheme and `J` a
coherent sheaf of ideals of `X`. Then, for every non-negative integer `ν`, there exists an open
subset `U_ν` of `X` such that a point `x` of `X` belongs to `U_ν` if and only if `ν(J_x) ≤ ν`."

`J_x` is the stalk ideal `J.stalkIdeal x` of the local ring `O_{X,x}` (regular, by
non-singularity) and `ν(J_x)` its order `Ideal.nu` with respect to the maximal ideal.  The
corollary expresses the upper semi-continuity of `ν(J_x)` announced in the title of the
section: the set `{x | ν(J_x) ≥ ν + 1}` is closed.

Deviation from the paper (gap filled): the paper gives no proof.  The proof below combines
Theorem 1 (`ν(J_x)` does not increase under generization), Theorem 2 (generic constancy along
each irreducible closed set, after shrinking to the regular locus of `A/Q`, which is open by the
cited property (iii) of p. 161, `IsHironakaBase.isClosed_singularLocus`) and noetherian induction. -/
@[blueprint "cor:III.thm2-1"
  (statement := /-- Let $X$ be a non-singular algebraic scheme and $J$ a coherent sheaf of
    ideals of $X$. Then, for every non-negative integer $\nu$, there exists an open subset
    $U_\nu$ of $X$ such that a point $x$ of $X$ belongs to $U_\nu$ if and only if
    $\nu(J_x)\le\nu$. (Corollary 1, p.~220.) -/)
  (proof := /-- (The paper gives no proof.) By \cref{thm:III.1}, if $x'$ is a specialization
    of $x$ then $\nu(J_x)\le\nu(J_{x'})$, so the set $U_\nu=\{x\mid\nu(J_x)\le\nu\}$ is stable
    under generization; and by \cref{thm:III.2} (with $\nu^*$ replaced by its first term
    $\nu^{(1)}=\nu$), for every irreducible closed subset $Z$ of $X$ with generic point
    $\eta$ there is a non-empty open subset of $Z$ on which $\nu(J_x)=\nu(J_\eta)$. Since $X$
    is noetherian, noetherian induction on the closed subsets of $X$ shows that $U_\nu$ is
    open.

    \textbf{Gap in the paper filled.} The argument above is supplied by the formalization.
    Theorem~2 requires $A/Q$ to be regular; to apply it along an arbitrary irreducible closed
    set one shrinks to the regular locus of $A/Q$, which contains the generic point and is
    open by property (iii) of p.~161 (\cref{prop:class-A-iii}, a cited leaf). -/)
  (latexEnv := "corollary")]
theorem exists_isOpen_nu_stalk_le [Hironaka.Cited.IsHironakaBaseIsClosedSingularLocus.{u}] [Hironaka.Cited.CurveFiniteIntegralClosure.{u}] [Hironaka.Cited.IsRegularLocalRingLocalizationOfIsRegularLocalRing.{u}] (X : Scheme.{u}) [IsAlgebraicScheme X] (hX : X.IsNonsingular)
    (J : Subscheme X) (ν : ℕ) :
    ∃ U : Set X, IsOpen U ∧ ∀ x : X, x ∈ U ↔ Ideal.nu (J.stalkIdeal x) ≤ ν := by
  have := IsAlgebraicScheme.noetherianSpace X
  refine ⟨{x | Ideal.nu (J.stalkIdeal x) ≤ ν}, ?_, fun x => Iff.rfl⟩
  -- stable under generization by Theorem 1, and generically constant by Theorem 2
  refine isOpen_of_generic _ (fun x y hyx hx => (nu_stalk_generization hX J hyx).trans hx)
    fun η hη => ?_
  obtain ⟨V, hV, hηV, hVeq⟩ := generic_nuStar hX J η
  refine ⟨V, hV, hηV, fun x hxV hηx => ?_⟩
  show Ideal.nu _ ≤ _
  rw [nu_eq_nuStar_one hX J x, hVeq x hxV hηx, ← nu_eq_nuStar_one hX J η]
  exact hη

/-- Corollary 2 of Theorem 2, p. 220: "Let `X` and `J` be as above. Then, given a sequence `ν*`
of non-negative integers, or `∞`, the set of those points `x ∈ X` with `ν*(J_x) = ν*` is a
constructible set, i.e., it is a finite union of locally closed subsets of `X`."

`ν*(J_x)` is `nuStar` of the stalk ideal in the regular local ring `O_{X,x}` (the regularity
instance being supplied by `hX x`).  Formalization note (encoding): "constructible" is Mathlib's
`Topology.IsConstructible` (the Boolean algebra generated by the retrocompact open sets); on the
noetherian underlying space of an algebraic scheme every open set is retrocompact, and this is
exactly the paper's "finite union of locally closed subsets".

Deviation from the paper (gap filled): the paper gives no proof; the proof below uses Theorem 2
(after shrinking to the regular locus of `A/Q`, open by the cited property (iii) of p. 161) and
noetherian induction. -/
@[blueprint "cor:III.thm2-2"
  (statement := /-- Let $X$ and $J$ be as in \cref{cor:III.thm2-1}. Then, given a sequence
    $\nu^*$ of non-negative integers, or $\infty$, the set of those points $x\in X$ with
    $\nu^*(J_x)=\nu^*$ is a constructible set, i.e., it is a finite union of locally closed
    subsets of $X$. (Corollary 2, p.~220.) Formalization note (encoding): ``constructible'' is
    taken in the sense of Mathlib, the Boolean algebra generated by the retrocompact open
    sets, which on the noetherian space $X$ coincides with the paper's ``finite union of
    locally closed subsets''. -/)
  (proof := /-- (The paper gives no proof.) By \cref{thm:III.2}, for every irreducible closed
    subset $Z$ of $X$ with generic point $\eta$ there is a non-empty open subset $U_Z$ of $Z$
    on which $\nu^*(J_x)=\nu^*(J_\eta)$. Since $X$ is noetherian, noetherian induction on the
    closed subsets of $X$ gives a finite partition of $X$ into locally closed subsets on each
    of which $\nu^*(J_x)$ is constant; the set $\{x\mid\nu^*(J_x)=\nu^*\}$ is the union of
    those pieces on which the constant value is $\nu^*$.

    \textbf{Gap in the paper filled.} The argument above is supplied by the formalization; as
    for Corollary~1, applying Theorem~2 along an arbitrary irreducible closed set uses the
    openness of the regular locus of $A/Q$ (property (iii) of p.~161, \cref{prop:class-A-iii},
    a cited leaf). -/)
  (latexEnv := "corollary")]
theorem isConstructible_nuStar_stalk_eq [Hironaka.Cited.IsHironakaBaseIsClosedSingularLocus.{u}] (X : Scheme.{u}) [IsAlgebraicScheme X]
    (hX : X.IsNonsingular) (J : Subscheme X) (ν : Lex (ℕ+ → ℕ∞)) :
    Topology.IsConstructible {x : X | @nuStar _ _ (hX x) (J.stalkIdeal x) = ν} := by
  have := IsAlgebraicScheme.noetherianSpace X
  -- a noetherian space is quasi-separated (every subset is compact)
  have : QuasiSeparatedSpace X :=
    ⟨fun U V _ _ _ _ => TopologicalSpace.NoetherianSpace.isCompact _⟩
  refine isConstructible_of_generic _ fun η => ?_
  obtain ⟨V, hV, hηV, hVeq⟩ := generic_nuStar hX J η
  refine ⟨V, hV, hηV, fun x hxV hηx => ?_⟩
  show _ = ν ↔ _ = ν
  rw [hVeq x hxV hηx]

/-! ### The Remark after Corollary 2 (pp. 220–221) -/

section Remark

open MvPolynomial

variable (k : Type u) [Field k]

/-! The example of pp. 220–221: `X = Spec(k[z₁, z₂, x, y])`, `k` any field.  We use the ring
`MvPolynomial (Fin 4) k` with `z₁ = X 0`, `z₂ = X 1`, `x = X 2`, `y = X 3`. -/

/-- `f₁ = z₁z₂ + (z₁ + y)²x` (p. 221). -/
noncomputable def exampleF₁ : MvPolynomial (Fin 4) k := X 0 * X 1 + (X 0 + X 3) ^ 2 * X 2

/-- `f₂ = z₁(z₁ + z₂) + (z₂ + y)²x` (p. 221). -/
noncomputable def exampleF₂ : MvPolynomial (Fin 4) k :=
  X 0 * (X 0 + X 1) + (X 1 + X 3) ^ 2 * X 2

/-- `f₃ = (z₁ + y)²(z₁ + z₂) − (z₂ + y)²z₂` (p. 221). -/
noncomputable def exampleF₃ : MvPolynomial (Fin 4) k :=
  (X 0 + X 3) ^ 2 * (X 0 + X 1) - (X 1 + X 3) ^ 2 * X 1

/-- The ideal `J = (f₁, f₂, f₃)` of `k[z₁, z₂, x, y]` (p. 221). -/
noncomputable def exampleJ : Ideal (MvPolynomial (Fin 4) k) :=
  Ideal.span {exampleF₁ k, exampleF₂ k, exampleF₃ k}

/-- The prime ideal `(z₁, z₂, y) k[z₁, z₂, x, y]` of the point `x` (p. 221). -/
noncomputable def examplePx : Ideal (MvPolynomial (Fin 4) k) := Ideal.span {X 0, X 1, X 3}

/-- The prime ideal `(z₁, z₂, y, x) k[z₁, z₂, x, y]` of the point `x'` (p. 221). -/
noncomputable def examplePx' : Ideal (MvPolynomial (Fin 4) k) :=
  Ideal.span {X 0, X 1, X 2, X 3}

/-- An ideal of a polynomial ring over a domain generated by a set `s` of variables is prime: it
is the kernel of the substitution `X i ↦ 0` (`i ∈ s`), `X i ↦ X i` (`i ∉ s`), whose target is a
domain. -/
theorem isPrime_span_X_image {σ A : Type*} [CommRing A] [IsDomain A] (s : Set σ) :
    (Ideal.span ((X : σ → MvPolynomial σ A) '' s)).IsPrime := by
  classical
  let φ : MvPolynomial σ A →ₐ[A] MvPolynomial σ A := aeval fun i => if i ∈ s then 0 else X i
  -- `p - φ p` lies in the ideal, by induction on `p`
  have key : ∀ p, p - φ p ∈ Ideal.span ((X : σ → MvPolynomial σ A) '' s) := by
    intro p
    induction p using MvPolynomial.induction_on with
    | C a => simp [φ]
    | add p q hp hq => rw [map_add, add_sub_add_comm]; exact add_mem hp hq
    | mul_X p i hp =>
      rw [map_mul, show p * X i - φ p * φ (X i) = (p - φ p) * X i + φ p * (X i - φ (X i)) by
        ring]
      refine add_mem (Ideal.mul_mem_right _ _ hp) (Ideal.mul_mem_left _ _ ?_)
      simp only [φ, aeval_X]
      split_ifs with h
      · simpa using Ideal.subset_span (Set.mem_image_of_mem X h)
      · simp
  have h : Ideal.span ((X : σ → MvPolynomial σ A) '' s) = RingHom.ker φ := by
    refine le_antisymm ?_ fun p hp => by simpa [RingHom.mem_ker.mp hp] using key p
    rw [Ideal.span_le]
    rintro _ ⟨i, hi, rfl⟩
    simp [φ, hi]
  rw [h]
  exact RingHom.ker_isPrime _

/-- `(z₁, z₂, y)` is a prime ideal of `k[z₁, z₂, x, y]` (the quotient is `k[x]`). -/
instance isPrime_examplePx : (examplePx k).IsPrime := by
  have h : examplePx k = Ideal.span ((X : Fin 4 → MvPolynomial (Fin 4) k) '' {0, 1, 3}) := by
    simp [examplePx, Set.image_insert_eq]
  rw [h]
  exact isPrime_span_X_image _

/-- `(z₁, z₂, y, x)` is a prime (indeed maximal) ideal of `k[z₁, z₂, x, y]` (the quotient is
`k`). -/
instance isPrime_examplePx' : (examplePx' k).IsPrime := by
  have h : examplePx' k = Ideal.span ((X : Fin 4 → MvPolynomial (Fin 4) k) '' {0, 1, 2, 3}) := by
    simp [examplePx', Set.image_insert_eq]
  rw [h]
  exact isPrime_span_X_image _

/-- The point `x` of `X = Spec(k[z₁, z₂, x, y])`. -/
noncomputable def examplePt : PrimeSpectrum (MvPolynomial (Fin 4) k) := ⟨examplePx k, inferInstance⟩

/-- The point `x'` of `X = Spec(k[z₁, z₂, x, y])`. -/
noncomputable def examplePt' : PrimeSpectrum (MvPolynomial (Fin 4) k) :=
  ⟨examplePx' k, inferInstance⟩

/-! #### Weighted homogeneous components and `gr` of a localized polynomial ring

The paper gives no computation for the Remark.  We compute `ν*` through Lemma 1
(`nuI_eq_of_lemma1_properties`): for a prime `P` of `S = K[X_σ]` generated by the variables of
weight `1` for a weight `w ≤ 1`, `Pᵈ` consists of the polynomials all of whose monomials have
weight `≥ d`, so the class in `gr(S_P)` of an element of `S` is read off from its weighted
homogeneous components.  (At `x` the weights are `(1, 1, 0, 1)` on `(z₁, z₂, x, y)`, at `x'` they
are `(1, 1, 1, 1)`.) -/

/-- The powers of the ideal generated by the variables of weight one, for a weight `w ≤ 1`:
`p ∈ Pᵈ` iff every monomial of `p` has weight `≥ d`. -/
private theorem mem_pow_span_X_iff {σ K : Type*} [Field K] (w : σ → ℕ) (hw : ∀ i, w i ≤ 1)
    (d : ℕ) (p : MvPolynomial σ K) :
    p ∈ (Ideal.span ((X : σ → MvPolynomial σ K) '' {i | w i = 1})) ^ d ↔
      ∀ m ∈ p.support, d ≤ Finsupp.weight w m := by
  classical
  set P := Ideal.span ((X : σ → MvPolynomial σ K) '' {i | w i = 1}) with hPdef
  -- the ideal of polynomials all of whose monomials have weight `≥ e`
  let Kd : ℕ → Ideal (MvPolynomial σ K) := fun e =>
    { carrier := {p | ∀ m ∈ p.support, e ≤ Finsupp.weight w m}
      add_mem' := fun {p q} hp hq m hm => by
        rcases Finset.mem_union.mp (support_add hm) with h | h
        · exact hp m h
        · exact hq m h
      zero_mem' := fun m hm => by simp at hm
      smul_mem' := fun c p hp m hm => by
        obtain ⟨m₁, -, m₂, hm₂, rfl⟩ := Finset.mem_add.mp (support_mul c p hm)
        rw [map_add]
        exact le_add_left (hp m₂ hm₂) }
  have hKmul : ∀ a b, Kd a * Kd b ≤ Kd (a + b) := by
    intro a b
    refine Ideal.mul_le.mpr fun p hp q hq m hm => ?_
    obtain ⟨m₁, hm₁, m₂, hm₂, rfl⟩ := Finset.mem_add.mp (support_mul p q hm)
    rw [map_add]
    exact add_le_add (hp m₁ hm₁) (hq m₂ hm₂)
  have hP1 : P ≤ Kd 1 := by
    rw [hPdef, Ideal.span_le]
    rintro _ ⟨i, hi, rfl⟩ m hm
    rw [support_X, Finset.mem_singleton] at hm
    subst hm
    rw [Finsupp.weight_single, one_smul]
    exact le_of_eq hi.symm
  constructor
  · intro hp
    have hle : ∀ e, P ^ e ≤ Kd e := by
      intro e
      induction e with
      | zero => intro p _ m _; exact Nat.zero_le _
      | succ e ih => rw [pow_succ]; exact (Ideal.mul_mono ih hP1).trans (hKmul e 1)
    exact hle d hp
  · intro hp
    -- every monomial of weight `e` lies in `Pᵉ`
    have hmono : ∀ m : σ →₀ ℕ, monomial m (1 : K) ∈ P ^ Finsupp.weight w m := by
      intro m
      induction m using Finsupp.induction with
      | zero => simp
      | single_add i e m' _ _ ih =>
        rw [← mul_one (1 : K), ← monomial_mul_monomial, map_add, pow_add]
        refine Ideal.mul_mem_mul ?_ ih
        rw [← X_pow_eq_monomial, Finsupp.weight_single, smul_eq_mul]
        rcases Nat.le_one_iff_eq_zero_or_eq_one.mp (hw i) with h0 | h1
        · rw [h0, mul_zero, pow_zero, Ideal.one_eq_top]
          exact Submodule.mem_top
        · rw [h1, mul_one]
          exact Ideal.pow_mem_pow (Ideal.subset_span (Set.mem_image_of_mem X
            (show i ∈ {i | w i = 1} from h1))) e
    rw [p.as_sum]
    refine sum_mem fun m hm => ?_
    rw [show monomial m (p.coeff m) = C (p.coeff m) * monomial m 1 by
      rw [C_mul_monomial, mul_one]]
    exact Ideal.mul_mem_left _ _ (Ideal.pow_le_pow_right (hp m hm) (hmono m))

section WeightedPowers

variable {σ K : Type*} [Field K] (w : σ → ℕ) (P : Ideal (MvPolynomial σ K))
  (hPd : ∀ (d : ℕ) (p : MvPolynomial σ K), p ∈ P ^ d ↔ ∀ m ∈ p.support, d ≤ Finsupp.weight w m)
include hPd

private theorem wc_eq_zero_of_mem_pow {d : ℕ} {p : MvPolynomial σ K}
    (hp : p ∈ P ^ (d + 1)) :
    weightedHomogeneousComponent w d p = 0 := by
  classical
  ext m
  rw [coeff_weightedHomogeneousComponent]
  split_ifs with hm
  · by_contra hne
    have := (hPd _ p).mp hp m (mem_support_iff.mpr (by simpa using hne))
    omega
  · simp

private theorem mem_pow_succ_of_wc_eq_zero {d : ℕ} {p : MvPolynomial σ K} (hp : p ∈ P ^ d)
    (h0 : weightedHomogeneousComponent w d p = 0) : p ∈ P ^ (d + 1) := by
  classical
  refine (hPd _ p).mpr fun m hm => ?_
  have hle := (hPd _ p).mp hp m hm
  refine lt_of_le_of_ne hle fun heq => ?_
  have := congrArg (fun q : MvPolynomial σ K => q.coeff m) h0
  simp only [coeff_weightedHomogeneousComponent, heq.symm, ite_true] at this
  exact mem_support_iff.mp hm (by simpa using this)

private theorem wc_mem_pow (d : ℕ) (p : MvPolynomial σ K) :
    weightedHomogeneousComponent w d p ∈ P ^ d := by
  classical
  refine (hPd _ _).mpr fun m hm => ?_
  rw [support_weightedHomogeneousComponent, Finset.mem_filter] at hm
  exact hm.2.ge

private theorem sub_wc_mem_pow {d : ℕ} {p : MvPolynomial σ K} (hp : p ∈ P ^ d) :
    p - weightedHomogeneousComponent w d p ∈ P ^ (d + 1) := by
  refine mem_pow_succ_of_wc_eq_zero w P hPd (sub_mem hp (wc_mem_pow w P hPd d p)) ?_
  rw [map_sub, weightedHomogeneousComponent_eq_self
    (weightedHomogeneousComponent_isWeightedHomogeneous d p), sub_self]

private theorem wc_mul {a b : ℕ} {p q : MvPolynomial σ K} (hp : p ∈ P ^ a)
    (hq : q ∈ P ^ b) :
    weightedHomogeneousComponent w (a + b) (p * q) =
      weightedHomogeneousComponent w a p * weightedHomogeneousComponent w b q := by
  set pa := weightedHomogeneousComponent w a p
  set qb := weightedHomogeneousComponent w b q
  have h1 := sub_wc_mem_pow w P hPd hp
  have h2 := sub_wc_mem_pow w P hPd hq
  have hrest : p * q - pa * qb ∈ P ^ (a + b + 1) := by
    have : p * q - pa * qb = pa * (q - qb) + (p - pa) * q := by ring
    rw [this]
    refine add_mem ?_ ?_
    · have := Ideal.mul_mem_mul (wc_mem_pow w P hPd a p) h2
      rwa [← pow_add, ← add_assoc] at this
    · have := Ideal.mul_mem_mul h1 hq
      rwa [← pow_add, add_right_comm] at this
  have := wc_eq_zero_of_mem_pow w P hPd hrest
  rw [map_sub, sub_eq_zero] at this
  rw [this, weightedHomogeneousComponent_eq_self
    ((weightedHomogeneousComponent_isWeightedHomogeneous a p).mul
      (weightedHomogeneousComponent_isWeightedHomogeneous b q))]

private theorem mem_pow_of_mul_mem_pow {a d : ℕ} {u p : MvPolynomial σ K} (hu : u ∈ P ^ a)
    (hu0 : weightedHomogeneousComponent w a u ≠ 0) (h : u * p ∈ P ^ (a + d)) : p ∈ P ^ d := by
  have key : ∀ e ≤ d, p ∈ P ^ e := by
    intro e
    induction e with
    | zero => intro _; simp
    | succ e ih =>
      intro he
      have hpe := ih (by omega)
      refine mem_pow_succ_of_wc_eq_zero w P hPd hpe ?_
      by_contra hne
      have hmul := wc_mul w P hPd hu hpe
      have h0 : weightedHomogeneousComponent w (a + e) (u * p) = 0 :=
        wc_eq_zero_of_mem_pow w P hPd (Ideal.pow_le_pow_right (by omega) h)
      rw [h0] at hmul
      exact mul_ne_zero hu0 hne hmul.symm
  exact key d le_rfl

private theorem exists_wc_ne_zero {p : MvPolynomial σ K} (hp : p ≠ 0) :
    ∃ d, p ∈ P ^ d ∧ weightedHomogeneousComponent w d p ≠ 0 := by
  classical
  have hne : p.support.Nonempty := support_nonempty.mpr hp
  set d := (p.support.image (Finsupp.weight w)).min' (hne.image _) with hd
  obtain ⟨m, hm, hmd⟩ := Finset.mem_image.mp ((p.support.image (Finsupp.weight w)).min'_mem
    (hne.image _))
  refine ⟨d, (hPd _ p).mpr fun m' hm' => Finset.min'_le _ _ (Finset.mem_image_of_mem _ hm'),
    fun h0 => ?_⟩
  rw [← hd] at hmd
  have := congrArg (fun q : MvPolynomial σ K => q.coeff m) h0
  simp only [coeff_weightedHomogeneousComponent, hmd, ite_true] at this
  exact mem_support_iff.mp hm (by simpa using this)

end WeightedPowers

attribute [local instance] MvPolynomial.weightedGradedAlgebra in
/-- The weighted homogeneous component of `c g` for `g` weighted homogeneous. -/
private theorem wc_mul_homogeneous {σ K : Type*} [Field K] (w : σ → ℕ)
    {g : MvPolynomial σ K} {e : ℕ} (hg : IsWeightedHomogeneous w g e) (c : MvPolynomial σ K)
    (d : ℕ) :
    weightedHomogeneousComponent w d (c * g) =
      if e ≤ d then weightedHomogeneousComponent w (d - e) c * g else 0 := by
  classical
  have h := DirectSum.coe_decompose_mul_of_right_mem
    (𝒜 := weightedHomogeneousSubmodule K w) (a := c) d (show g ∈ _ from hg)
  rw [← weightedDecomposition.decompose'_apply K w, ← weightedDecomposition.decompose'_apply K w]
  exact h

/-- The class of `a X⁰` is the image of `a mod I` under `A/I → gr_I(A)`. -/
private theorem mk_zero_eq_algebraMap {A : Type*} [CommRing A] (I : Ideal A) (a : A)
    (ha : a ∈ I ^ 0) :
    AssocGraded.mk I 0 a ha = algebraMap (A ⧸ I) (AssocGraded I) (Ideal.Quotient.mk I a) := by
  show Ideal.Quotient.mk _ _ = Ideal.Quotient.mk _ (algebraMap A (reesAlgebra I) a)
  refine congrArg _ (Subtype.ext ?_)
  show Polynomial.monomial 0 a = Polynomial.C a
  rfl

/-- Two elements of `Iᵈ` congruent modulo `Iᵈ⁺¹` have the same class in `grᵈ_I(A)`. -/
private theorem mk_eq_mk {A : Type*} [CommRing A] (I : Ideal A) {d : ℕ} {a b : A}
    (ha : a ∈ I ^ d) (hb : b ∈ I ^ d) (h : a - b ∈ I ^ (d + 1)) :
    AssocGraded.mk I d a ha = AssocGraded.mk I d b hb := by
  rw [← sub_eq_zero]
  have hsub : AssocGraded.mk I d (a - b) (sub_mem ha hb) =
      AssocGraded.mk I d a ha - AssocGraded.mk I d b hb :=
    map_sub (AssocGraded.mkLinear I d) ⟨a, ha⟩ ⟨b, hb⟩
  rw [← hsub, AssocGraded.mk_eq_zero_iff]
  exact h

section WeightedLocalization

variable {σ K : Type*} [Field K] (w : σ → ℕ) (P : Ideal (MvPolynomial σ K)) [P.IsPrime]
  (hPd : ∀ (d : ℕ) (p : MvPolynomial σ K), p ∈ P ^ d ↔ ∀ m ∈ p.support, d ≤ Finsupp.weight w m)
include hPd

omit [P.IsPrime] in
private theorem wc_zero_ne_zero {s : MvPolynomial σ K} (hs : s ∉ P) :
    weightedHomogeneousComponent w 0 s ≠ 0 := fun h0 =>
  hs (by simpa using mem_pow_succ_of_wc_eq_zero w P hPd (by simp : s ∈ P ^ 0) h0)

/-- `PᵈR_P ∩ S = Pᵈ` (the powers of `P` are `P`-primary). -/
private theorem algebraMap_mem_pow_iff (d : ℕ) (p : MvPolynomial σ K) :
    algebraMap _ (Localization.AtPrime P) p ∈ maximalIdeal (Localization.AtPrime P) ^ d ↔
      p ∈ P ^ d := by
  constructor
  · intro h
    rw [← Localization.AtPrime.map_eq_maximalIdeal, ← Ideal.map_pow,
      IsLocalization.mem_map_algebraMap_iff P.primeCompl] at h
    obtain ⟨⟨⟨a, ha⟩, s⟩, hs⟩ := h
    simp only at hs
    rw [← map_mul, IsLocalization.eq_iff_exists P.primeCompl] at hs
    obtain ⟨c, hc⟩ := hs
    have hu : ((c : MvPolynomial σ K) * s) ∉ P := P.primeCompl.mul_mem c.2 s.2
    refine mem_pow_of_mul_mem_pow w P hPd (a := 0) (by simp)
      (wc_zero_ne_zero w P hPd hu) ?_
    rw [zero_add, show (c : MvPolynomial σ K) * s * p = c * a by rw [← hc]; ring]
    exact Ideal.mul_mem_left _ _ ha
  · intro h
    rw [← Localization.AtPrime.map_eq_maximalIdeal, ← Ideal.map_pow]
    exact Ideal.mem_map_of_mem _ h

/-- The initial form of the image of `p ∈ Pᵈ` with `(p)_d ≠ 0` is the class of `(p)_d`. -/
private theorem initialForm_localization_eq_mk_weightedHomogeneousComponent {d : ℕ} {p : MvPolynomial σ K} (hp : p ∈ P ^ d)
    (hp0 : weightedHomogeneousComponent w d p ≠ 0) :
    initialForm (maximalIdeal (Localization.AtPrime P)) (algebraMap _ _ p) =
      AssocGraded.mk _ d
        (algebraMap _ (Localization.AtPrime P) (weightedHomogeneousComponent w d p))
        ((algebraMap_mem_pow_iff w P hPd _ _).mpr (wc_mem_pow w P hPd d p)) := by
  have hnot : algebraMap _ (Localization.AtPrime P) p ∉
      maximalIdeal (Localization.AtPrime P) ^ (d + 1) := fun h =>
    hp0 (wc_eq_zero_of_mem_pow w P hPd ((algebraMap_mem_pow_iff w P hPd _ _).mp h))
  have hord : Ideal.ordElem (maximalIdeal (Localization.AtPrime P)) (algebraMap _ _ p) = d :=
    le_antisymm (Ideal.ordElem_le_of_notMem hnot)
      (Ideal.le_ordElem ((algebraMap_mem_pow_iff w P hPd _ _).mpr hp))
  rw [initialForm_eq_mk _ hord]
  refine mk_eq_mk _ _ _ ?_
  rw [← map_sub]
  exact (algebraMap_mem_pow_iff w P hPd _ _).mpr (sub_wc_mem_pow w P hPd hp)

/-- Forward transfer: a relation between weighted forms in `S` gives one in `gr(R_P)`. -/
private theorem mk_mem_span {m : ℕ} (g : Fin m → MvPolynomial σ K) (dg : Fin m → ℕ)
    (hg : ∀ j, IsWeightedHomogeneous w (g j) (dg j)) {D : ℕ} {h : MvPolynomial σ K}
    (hh : IsWeightedHomogeneous w h D) (hmem : h ∈ Ideal.span (Set.range g)) :
    AssocGraded.mk _ D (algebraMap _ (Localization.AtPrime P) h)
        ((algebraMap_mem_pow_iff w P hPd _ _).mpr
          (weightedHomogeneousComponent_eq_self hh ▸ wc_mem_pow w P hPd D h)) ∈
      Ideal.span (Set.range fun j => AssocGraded.mk _ (dg j)
        (algebraMap _ (Localization.AtPrime P) (g j))
        ((algebraMap_mem_pow_iff w P hPd _ _).mpr
          (weightedHomogeneousComponent_eq_self (hg j) ▸ wc_mem_pow w P hPd _ (g j)))) := by
  classical
  obtain ⟨c, hc⟩ := Ideal.mem_span_range_iff_exists_fun.mp hmem
  have hsum : ∑ j ∈ Finset.univ.filter (fun j => dg j ≤ D),
      weightedHomogeneousComponent w (D - dg j) (c j) * g j = h := by
    rw [Finset.sum_filter]
    conv_rhs => rw [← weightedHomogeneousComponent_eq_self hh, ← hc, map_sum]
    exact Finset.sum_congr rfl fun j _ => (wc_mul_homogeneous w (hg j) (c j) D).symm
  refine Ideal.span_mono (Set.image_subset_range _ _) (mk_mem_span_of_sub_mem_pow _ _ dg _ _
    (Finset.univ.filter fun j => dg j ≤ D)
    (fun j => algebraMap _ _ (weightedHomogeneousComponent w (D - dg j) (c j))) (fun j hj => ⟨?_,
      (algebraMap_mem_pow_iff w P hPd _ _).mpr (wc_mem_pow w P hPd _ _)⟩) ?_)
  · exact (Finset.mem_filter.mp hj).2
  · simp only [← map_mul, ← map_sum, hsum, sub_self]
    exact zero_mem _

/-- Backward transfer: a relation in `gr(R_P)` between classes of weighted forms comes, after
clearing denominators, from a relation `s₀ h = Σ c_j g_j` in `S` with `s₀` of weight `0`. -/
private theorem exists_of_mk_mem_span {m : ℕ} (g : Fin m → MvPolynomial σ K)
    (dg : Fin m → ℕ) (hg : ∀ j, g j ∈ P ^ dg j) (hgh : ∀ j, IsWeightedHomogeneous w (g j) (dg j))
    {D : ℕ} {h : MvPolynomial σ K}
    (hh : IsWeightedHomogeneous w h D) (hhP : h ∈ P ^ D)
    (hmem : AssocGraded.mk _ D (algebraMap _ (Localization.AtPrime P) h)
        ((algebraMap_mem_pow_iff w P hPd _ _).mpr hhP) ∈
      Ideal.span (Set.range fun j => AssocGraded.mk _ (dg j)
        (algebraMap _ (Localization.AtPrime P) (g j))
        ((algebraMap_mem_pow_iff w P hPd _ _).mpr (hg j)))) :
    ∃ s₀ : MvPolynomial σ K, IsWeightedHomogeneous w s₀ 0 ∧ s₀ ≠ 0 ∧
      ∃ c : Fin m → MvPolynomial σ K, (∀ j, IsWeightedHomogeneous w (c j) (D - dg j)) ∧
        s₀ * h = ∑ j, (if dg j ≤ D then c j else 0) * g j := by
  classical
  obtain ⟨c', -, -, hc'⟩ := exists_sub_mem_pow_of_mk_mem_span _ _ dg _ _ hmem
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples P.primeCompl Finset.univ c'
  choose a ha using fun j => hb j (Finset.mem_univ j)
  have hrel : algebraMap _ (Localization.AtPrime P) (b * h - ∑ j, a j * g j) ∈
      maximalIdeal (Localization.AtPrime P) ^ (D + 1) := by
    have : algebraMap _ (Localization.AtPrime P) (b * h - ∑ j, a j * g j) =
        algebraMap _ _ (b : MvPolynomial σ K) * (algebraMap _ _ h -
          ∑ j, c' j * algebraMap _ _ (g j)) := by
      simp only [map_sub, map_mul, map_sum, ha, Algebra.smul_def, Finset.mul_sum, mul_sub,
        mul_assoc]
    rw [this]
    exact Ideal.mul_mem_left _ _ hc'
  have h0 := wc_eq_zero_of_mem_pow w P hPd
    ((algebraMap_mem_pow_iff w P hPd _ _).mp hrel)
  rw [map_sub, map_sum, sub_eq_zero, wc_mul_homogeneous w hh, ite_eq_left (le_refl D),
    Nat.sub_self] at h0
  refine ⟨weightedHomogeneousComponent w 0 b,
    weightedHomogeneousComponent_isWeightedHomogeneous _ _,
    wc_zero_ne_zero w P hPd b.2, fun j => weightedHomogeneousComponent w (D - dg j) (a j),
    fun j => weightedHomogeneousComponent_isWeightedHomogeneous _ _, ?_⟩
  rw [h0]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [wc_mul_homogeneous w (hgh j)]
  split_ifs <;> simp

/-- `gr(J R_P)` lies in the ideal generated by the classes of weighted forms `g_j` as soon as every
weighted component of every element of `J` lies in `(g_j)`. -/
private theorem grIdeal_le [IsRegularLocalRing (Localization.AtPrime P)] {m : ℕ}
    (g : Fin m → MvPolynomial σ K) (dg : Fin m → ℕ)
    (hgh : ∀ j, IsWeightedHomogeneous w (g j) (dg j)) (J : Ideal (MvPolynomial σ K))
    (hJ : ∀ p ∈ J, ∀ d, p ∈ P ^ d → weightedHomogeneousComponent w d p ∈ Ideal.span (Set.range g)) :
    grIdeal (maximalIdeal (Localization.AtPrime P)) (J.map (algebraMap _ _)) ≤
      Ideal.span (Set.range fun j => AssocGraded.mk _ (dg j)
        (algebraMap _ (Localization.AtPrime P) (g j))
        ((algebraMap_mem_pow_iff w P hPd _ _).mpr
          (weightedHomogeneousComponent_eq_self (hgh j) ▸
            wc_mem_pow w P hPd _ (g j)))) := by
  classical
  rw [grIdeal, Ideal.span_le]
  rintro _ ⟨y, hy, rfl⟩
  rw [SetLike.mem_coe, IsLocalization.mem_map_algebraMap_iff P.primeCompl] at hy
  obtain ⟨⟨⟨a, ha⟩, s⟩, hs⟩ := hy
  simp only at hs
  have hu : IsUnit (algebraMap _ (Localization.AtPrime P) (s : MvPolynomial σ K)) :=
    IsLocalization.map_units _ s
  have hunit : IsUnit (initialForm (maximalIdeal (Localization.AtPrime P))
      (algebraMap _ (Localization.AtPrime P) (s : MvPolynomial σ K))) := by
    have hnot : algebraMap _ (Localization.AtPrime P) (s : MvPolynomial σ K) ∉
        maximalIdeal (Localization.AtPrime P) ^ (0 + 1) := by
      rw [zero_add, pow_one]
      exact fun h => (IsLocalRing.mem_maximalIdeal _).mp h hu
    have hord : Ideal.ordElem (maximalIdeal (Localization.AtPrime P))
        (algebraMap _ (Localization.AtPrime P) (s : MvPolynomial σ K)) = (0 : ℕ) :=
      le_antisymm (Ideal.ordElem_le_of_notMem hnot) (by simp)
    rw [initialForm_eq_mk _ hord, mk_zero_eq_algebraMap]
    exact (hu.map (Ideal.Quotient.mk _)).map (algebraMap _ _)
  have hmul := initialForm_mul_maximalIdeal y (algebraMap _ (Localization.AtPrime P)
    (s : MvPolynomial σ K))
  rw [hs] at hmul
  rw [SetLike.mem_coe, ← Ideal.mul_unit_mem_iff_mem _ hunit, ← hmul]
  by_cases ha0 : a = 0
  · rw [ha0, map_zero, initialForm, dite_eq_left (Ideal.ordElem_eq_top_iff.mpr fun _ => zero_mem _)]
    exact zero_mem _
  obtain ⟨d, hd, hd0⟩ := exists_wc_ne_zero w P hPd ha0
  rw [initialForm_localization_eq_mk_weightedHomogeneousComponent w P hPd hd hd0]
  exact mk_mem_span w P hPd g dg hgh
    (weightedHomogeneousComponent_isWeightedHomogeneous d a) (hJ a ha d hd)

end WeightedLocalization

section RemarkComputation

/-! The two computations of `ν*` in the Remark. -/

/-- A polynomial which is weighted homogeneous of weight `0` for the weight `1` is constant. -/
private theorem eq_C_of_deg_zero {σ : Type*} {u : MvPolynomial σ k}
    (hu : IsWeightedHomogeneous (fun _ : σ => (1 : ℕ)) u 0) : u = C (u.coeff 0) := by
  classical
  ext m
  rw [coeff_C]
  split_ifs with hm
  · rw [hm]
  · by_contra hne
    have := hu hne
    rw [← Finsupp.degree_eq_weight_one (R := ℕ)] at this
    exact hm ((Finsupp.degree_eq_zero_iff m).mp this).symm

/-- `q − q(X_j = 0) ∈ (X_j)`: the kernel of the substitution `X_j ↦ 0` is `(X_j)`. -/
private theorem sub_subst_mem_span (j : Fin 4) (q : MvPolynomial (Fin 4) k) :
    q - aeval (fun i => if i = j then (0 : MvPolynomial (Fin 4) k) else X i) q ∈
      Ideal.span {(X j : MvPolynomial (Fin 4) k)} := by
  induction q using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => rw [map_add, add_sub_add_comm]; exact add_mem hp hq
  | mul_X p i hp =>
    rw [map_mul, show p * X i - (aeval fun i => if i = j then (0 : MvPolynomial (Fin 4) k)
        else X i) p * (aeval fun i => if i = j then (0 : MvPolynomial (Fin 4) k) else X i) (X i) =
        (p - (aeval fun i => if i = j then (0 : MvPolynomial (Fin 4) k) else X i) p) * X i +
          (aeval fun i => if i = j then (0 : MvPolynomial (Fin 4) k) else X i) p *
            (X i - (aeval fun i => if i = j then (0 : MvPolynomial (Fin 4) k) else X i) (X i))
      by ring]
    refine add_mem (Ideal.mul_mem_right _ _ hp) (Ideal.mul_mem_left _ _ ?_)
    rw [aeval_X]
    split_ifs with h
    · rw [h, sub_zero]
      exact Ideal.mem_span_singleton_self _
    · simp

private theorem exists_mul_X_of_subst_eq_zero (j : Fin 4) {q : MvPolynomial (Fin 4) k}
    (hq : aeval (fun i => if i = j then (0 : MvPolynomial (Fin 4) k) else X i) q = 0) :
    ∃ r, r * X j = q := by
  have := sub_subst_mem_span k j q
  rw [hq, sub_zero] at this
  exact Ideal.mem_span_singleton'.mp this

/-- `(z₁, z₂, y, x)` is the ideal of the variables of weight `1`. -/
private theorem hPd' (d : ℕ) (p : MvPolynomial (Fin 4) k) :
    p ∈ examplePx' k ^ d ↔ ∀ m ∈ p.support, d ≤ Finsupp.weight (fun _ : Fin 4 => (1 : ℕ)) m := by
  have h : examplePx' k = Ideal.span ((X : Fin 4 → MvPolynomial (Fin 4) k) ''
      {i | (fun _ : Fin 4 => (1 : ℕ)) i = 1}) := by
    rw [examplePx']
    congr 1
    ext q
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.ofPred_true, Set.image_univ,
      Set.mem_range]
    constructor
    · rintro (rfl | rfl | rfl | rfl)
      exacts [⟨0, rfl⟩, ⟨1, rfl⟩, ⟨2, rfl⟩, ⟨3, rfl⟩]
    · rintro ⟨i, rfl⟩
      fin_cases i <;> simp
  rw [h]
  exact mem_pow_span_X_iff _ (fun _ => le_rfl) d p

/-- The standard base computation at the origin: every weighted component `(p)_d` of an element
`p ∈ Pᵈ` of `J = (f₁, f₂, f₃)` lies in the ideal of the initial forms `z₁z₂`, `z₁(z₁ + z₂)`, `f₃`.
(The syzygies of these forms are generated by `(z₁ + z₂, −z₂, 0)` and
`(−(z₂ + y)², (z₁ + y)², −z₁)`, which lift to the syzygies `(z₁ + z₂, −z₂, −x)` and
`(−(z₂ + y)², (z₁ + y)², −z₁)` of `(f₁, f₂, f₃)`; a representation `p = Σ a_j f_j` is improved
degree by degree until its leading part does not cancel.) -/
private theorem origin_sb (p : MvPolynomial (Fin 4) k) (hpJ : p ∈ exampleJ k) (d : ℕ)
    (hpd : p ∈ examplePx' k ^ d) :
    weightedHomogeneousComponent (fun _ : Fin 4 => (1 : ℕ)) d p ∈
      Ideal.span (Set.range ![X 0 * X 1, X 0 * (X 0 + X 1), exampleF₃ k]) := by
  classical
  set w : Fin 4 → ℕ := fun _ => 1 with hw
  set P := examplePx' k with hP
  have hPd := hPd' k
  have hX : ∀ i, IsWeightedHomogeneous w (X i : MvPolynomial (Fin 4) k) 1 := fun i =>
    isWeightedHomogeneous_X k w i
  have hg1 : IsWeightedHomogeneous w (X 0 * X 1 : MvPolynomial (Fin 4) k) 2 := (hX 0).mul (hX 1)
  have hg2 : IsWeightedHomogeneous w (X 0 * (X 0 + X 1) : MvPolynomial (Fin 4) k) 2 :=
    (hX 0).mul ((hX 0).add (hX 1))
  have hh1 : IsWeightedHomogeneous w ((X 0 + X 3) ^ 2 * X 2 : MvPolynomial (Fin 4) k) 3 :=
    (((hX 0).add (hX 3)).pow 2).mul (hX 2)
  have hh2 : IsWeightedHomogeneous w ((X 1 + X 3) ^ 2 * X 2 : MvPolynomial (Fin 4) k) 3 :=
    (((hX 1).add (hX 3)).pow 2).mul (hX 2)
  have hf3 : IsWeightedHomogeneous w (exampleF₃ k) 3 :=
    ((((hX 0).add (hX 3)).pow 2).mul ((hX 0).add (hX 1))).sub
      ((((hX 1).add (hX 3)).pow 2).mul (hX 1))
  have hmemP : ∀ {e : ℕ} {q : MvPolynomial (Fin 4) k}, IsWeightedHomogeneous w q e → q ∈ P ^ e :=
    fun {e q} hq => weightedHomogeneousComponent_eq_self hq ▸ wc_mem_pow w P hPd e q
  set G := Ideal.span (Set.range ![X 0 * X 1, X 0 * (X 0 + X 1), exampleF₃ k]) with hGdef
  have hG1 : (X 0 * X 1 : MvPolynomial (Fin 4) k) ∈ G := Ideal.subset_span ⟨0, rfl⟩
  have hG2 : (X 0 * (X 0 + X 1) : MvPolynomial (Fin 4) k) ∈ G := Ideal.subset_span ⟨1, rfl⟩
  have hG3 : exampleF₃ k ∈ G := Ideal.subset_span ⟨2, rfl⟩
  -- representations of level `L`
  let lev : ℕ → Prop := fun L => ∃ a b c : MvPolynomial (Fin 4) k,
    p = a * exampleF₁ k + b * exampleF₂ k + c * exampleF₃ k ∧ a ∈ P ^ (L - 2) ∧ b ∈ P ^ (L - 2) ∧
      c ∈ P ^ (L - 3)
  have hF₁ : exampleF₁ k = X 0 * X 1 + (X 0 + X 3) ^ 2 * X 2 := rfl
  have hF₂ : exampleF₂ k = X 0 * (X 0 + X 1) + (X 1 + X 3) ^ 2 * X 2 := rfl
  -- the component of degree `L` of a level-`L` representation
  have hcomp : ∀ L (a b c : MvPolynomial (Fin 4) k), a ∈ P ^ (L - 2) → b ∈ P ^ (L - 2) →
      weightedHomogeneousComponent w L (a * exampleF₁ k + b * exampleF₂ k + c * exampleF₃ k) =
        (if 2 ≤ L then weightedHomogeneousComponent w (L - 2) a * (X 0 * X 1) else 0) +
        (if 2 ≤ L then weightedHomogeneousComponent w (L - 2) b * (X 0 * (X 0 + X 1)) else 0) +
        (if 3 ≤ L then weightedHomogeneousComponent w (L - 3) c * exampleF₃ k else 0) := by
    intro L a b c ha hb
    have hz : ∀ (u : MvPolynomial (Fin 4) k) (h : MvPolynomial (Fin 4) k), u ∈ P ^ (L - 2) →
        IsWeightedHomogeneous w h 3 → weightedHomogeneousComponent w L (u * h) = 0 := by
      intro u h hu hh
      refine wc_eq_zero_of_mem_pow w P hPd
        (Ideal.pow_le_pow_right (show L + 1 ≤ L - 2 + 3 by omega) ?_)
      have := Ideal.mul_mem_mul hu (hmemP hh)
      rwa [← pow_add] at this
    rw [hF₁, hF₂, mul_add, mul_add, map_add, map_add, map_add, map_add, hz a _ ha hh1,
      hz b _ hb hh2, wc_mul_homogeneous w hg1, wc_mul_homogeneous w hg2,
      wc_mul_homogeneous w hf3, add_zero, add_zero]
  -- (A) a level-`L` representation gives the component of degree `L`
  have hA : ∀ L, lev L → weightedHomogeneousComponent w L p ∈ G := by
    rintro L ⟨a, b, c, hp, ha, hb, -⟩
    rw [hp, hcomp L a b c ha hb]
    refine add_mem (add_mem ?_ ?_) ?_ <;> split_ifs
    all_goals first | exact zero_mem _ | exact Ideal.mul_mem_left _ _ ‹_›
  have hX1P : ∀ i, (X i : MvPolynomial (Fin 4) k) ∈ P ^ 1 := fun i => hmemP (hX i)
  have hXP : ∀ i, (X i : MvPolynomial (Fin 4) k) ∈ P := fun i => by simpa using hX1P i
  have hF₃ : exampleF₃ k = (X 0 + X 3) ^ 2 * (X 0 + X 1) - (X 1 + X 3) ^ 2 * X 1 := rfl
  have hwcX : ∀ i, weightedHomogeneousComponent w 1 (X i : MvPolynomial (Fin 4) k) ≠ 0 := by
    intro i
    rw [weightedHomogeneousComponent_eq_self (hX i)]
    exact X_ne_zero i
  -- division by a variable lowers the order by one
  have hdiv : ∀ (i : Fin 4) (e : ℕ) (r : MvPolynomial (Fin 4) k), r * X i ∈ P ^ (e + 1) →
      r ∈ P ^ e := by
    intro i e r h
    refine mem_pow_of_mul_mem_pow w P hPd (hX1P i) (hwcX i) ?_
    rwa [mul_comm, add_comm]
  -- (B) raising the level of a representation
  have hB : ∀ L, 3 ≤ L → lev L → p ∈ P ^ (L + 1) → lev (L + 1) := by
    rintro L hL ⟨a, b, c, hp, ha, hb, hc⟩ hpL
    set A := weightedHomogeneousComponent w (L - 2) a with hAdef
    set B := weightedHomogeneousComponent w (L - 2) b with hBdef
    set C := weightedHomogeneousComponent w (L - 3) c with hCdef
    have hsyz : A * (X 0 * X 1) + B * (X 0 * (X 0 + X 1)) + C * exampleF₃ k = 0 := by
      have h0 := wc_eq_zero_of_mem_pow w P hPd hpL
      rw [hp, hcomp L a b c ha hb, ite_eq_left (by omega : 2 ≤ L),
        ite_eq_left (by omega : 2 ≤ L), ite_eq_left (by omega : 3 ≤ L)] at h0
      exact h0
    -- `C` is divisible by `z₁`
    set ev0 := aeval (R := k)
      (fun i => if i = (0 : Fin 4) then (0 : MvPolynomial (Fin 4) k) else X i) with hev0
    have hG : ev0 (exampleF₃ k) = X 3 ^ 2 * X 1 - (X 1 + X 3) ^ 2 * X 1 := by
      simp [hev0, exampleF₃]
    have hG0 : (X 3 ^ 2 * X 1 - (X 1 + X 3) ^ 2 * X 1 : MvPolynomial (Fin 4) k) ≠ 0 := by
      intro h
      have := congrArg (MvPolynomial.eval ![0, 1, 0, 0]) h
      simp at this
    have e00 : ev0 (X 0) = 0 := by simp [hev0]
    have hC0 : ev0 C = 0 := by
      have := congrArg ev0 hsyz
      simp only [map_add, map_mul, map_zero, hG, e00, zero_mul, mul_zero, zero_add] at this
      rcases mul_eq_zero.mp this with h | h
      · exact h
      · exact absurd h hG0
    obtain ⟨r0, hr0⟩ := exists_mul_X_of_subst_eq_zero k 0 hC0
    have hr0P : r0 ∈ P ^ (L - 4) := by
      rcases Nat.lt_or_ge L 4 with h4 | h4
      · rw [show L - 4 = 0 by omega, pow_zero, Ideal.one_eq_top]
        exact Submodule.mem_top
      · refine hdiv 0 _ r0 ?_
        rw [hr0, show L - 4 + 1 = L - 3 by omega]
        exact wc_mem_pow w P hPd _ c
    -- then `B + r₀(z₁ + y)²` is divisible by `z₂`
    have h5 : X 0 * (X 1 * (A - r0 * (X 1 + X 3) ^ 2) +
        (X 0 + X 1) * (B + r0 * (X 0 + X 3) ^ 2)) = 0 := by
      rw [← hsyz, ← hr0, exampleF₃]
      ring
    have h6 : X 1 * (A - r0 * (X 1 + X 3) ^ 2) + (X 0 + X 1) * (B + r0 * (X 0 + X 3) ^ 2) = 0 :=
      (mul_eq_zero.mp h5).resolve_left (X_ne_zero 0)
    set ev1 := aeval (R := k)
      (fun i => if i = (1 : Fin 4) then (0 : MvPolynomial (Fin 4) k) else X i) with hev1
    have e10 : ev1 (X 0) = X 0 := by simp [hev1]
    have e11 : ev1 (X 1) = 0 := by simp [hev1]
    set Z := B + r0 * (X 0 + X 3) ^ 2 with hZ
    have hB0 : ev1 Z = 0 := by
      have := congrArg ev1 h6
      simp only [map_add, map_mul, map_zero, e10, e11, zero_mul, zero_add, add_zero] at this
      exact (mul_eq_zero.mp this).resolve_left (X_ne_zero 0)
    obtain ⟨r1, hr1⟩ := exists_mul_X_of_subst_eq_zero k 1 hB0
    have hAe : A = r0 * (X 1 + X 3) ^ 2 - r1 * (X 0 + X 1) := by
      have h7 : X 1 * (A - r0 * (X 1 + X 3) ^ 2 + r1 * (X 0 + X 1)) = 0 := by
        rw [← h6, ← hr1]
        ring
      have := (mul_eq_zero.mp h7).resolve_left (X_ne_zero 1)
      linear_combination this
    have hBe : B = r1 * X 1 - r0 * (X 0 + X 3) ^ 2 := by
      linear_combination hr1.symm
    have hr1P : r1 ∈ P ^ (L - 3) := by
      refine hdiv 1 _ r1 ?_
      rw [hr1, show L - 3 + 1 = L - 2 by omega]
      refine add_mem (wc_mem_pow w P hPd _ b) ?_
      refine Ideal.pow_le_pow_right (show L - 2 ≤ L - 4 + 2 by omega) ?_
      rw [pow_add]
      exact Ideal.mul_mem_mul hr0P (Ideal.pow_mem_pow (add_mem (hXP 0) (hXP 3)) 2)
    refine ⟨a - A, b - B, c - C - r1 * X 2, ?_, ?_, ?_, ?_⟩
    · rw [hp, hF₁, hF₂, hF₃]
      linear_combination (X 0 * X 1 + (X 0 + X 3) ^ 2 * X 2) * hAe +
        (X 0 * (X 0 + X 1) + (X 1 + X 3) ^ 2 * X 2) * hBe +
        ((X 0 + X 3) ^ 2 * (X 0 + X 1) - (X 1 + X 3) ^ 2 * X 1) * hr0.symm
    · rw [show L + 1 - 2 = L - 2 + 1 by omega]
      exact sub_wc_mem_pow w P hPd ha
    · rw [show L + 1 - 2 = L - 2 + 1 by omega]
      exact sub_wc_mem_pow w P hPd hb
    · rw [show L + 1 - 3 = L - 3 + 1 by omega]
      refine sub_mem (sub_wc_mem_pow w P hPd hc) ?_
      rw [pow_add, pow_one]
      exact Ideal.mul_mem_mul hr1P (hXP 2)
  -- (C) a representation of level `2`, and of level `3` if `p ∈ P³`
  obtain ⟨a, b, c, hp⟩ : ∃ a b c : MvPolynomial (Fin 4) k,
      p = a * exampleF₁ k + b * exampleF₂ k + c * exampleF₃ k := by
    rw [exampleJ, Ideal.mem_span_insert] at hpJ
    obtain ⟨a, z, hz, rfl⟩ := hpJ
    rw [Ideal.mem_span_insert] at hz
    obtain ⟨b, z', hz', rfl⟩ := hz
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hz'
    exact ⟨a, b, c, by ring⟩
  have htop : ∀ (e : ℕ) (q : MvPolynomial (Fin 4) k), e = 0 → q ∈ P ^ e := by
    rintro e q rfl
    rw [pow_zero, Ideal.one_eq_top]
    exact Submodule.mem_top
  have hlev2 : ∀ L ≤ 2, lev L := fun L hL =>
    ⟨a, b, c, hp, htop _ _ (by omega), htop _ _ (by omega), htop _ _ (by omega)⟩
  have hlev3 : p ∈ P ^ 3 → lev 3 := by
    intro hp3
    have h0 := wc_eq_zero_of_mem_pow w P hPd (show p ∈ P ^ (2 + 1) from hp3)
    rw [hp, hcomp 2 a b c (htop _ _ rfl) (htop _ _ rfl), ite_eq_left le_rfl, ite_eq_left le_rfl,
      ite_eq_right (by omega : ¬ 3 ≤ 2), add_zero] at h0
    have hAc := eq_C_of_deg_zero k
      (weightedHomogeneousComponent_isWeightedHomogeneous (w := w) (2 - 2) a)
    have hBc := eq_C_of_deg_zero k
      (weightedHomogeneousComponent_isWeightedHomogeneous (w := w) (2 - 2) b)
    rw [hAc, hBc] at h0
    have hβ := congrArg (MvPolynomial.eval ![1, 0, 0, 0]) h0
    have hα := congrArg (MvPolynomial.eval ![1, 1, 0, 0]) h0
    simp at hβ hα
    have hβ0 : b.coeff 0 = 0 := by simpa using hβ
    have hα0 : a.coeff 0 = 0 := by simpa [hβ0] using hα
    refine ⟨a, b, c, hp, ?_, ?_, htop _ _ rfl⟩
    · refine mem_pow_succ_of_wc_eq_zero w P hPd (d := 0) (htop _ _ rfl) ?_
      rw [show (2 : ℕ) - 2 = 0 from rfl] at hAc
      rw [hAc]
      simp [hα0]
    · refine mem_pow_succ_of_wc_eq_zero w P hPd (d := 0) (htop _ _ rfl) ?_
      rw [show (2 : ℕ) - 2 = 0 from rfl] at hBc
      rw [hBc]
      simp [hβ0]
  rcases Nat.lt_or_ge d 3 with hd | hd
  · exact hA d (hlev2 d (by omega))
  · have hp3 : p ∈ P ^ 3 := Ideal.pow_le_pow_right hd hpd
    have key : ∀ L, 3 ≤ L → L ≤ d → lev L := by
      intro L hL hLd
      induction L, hL using Nat.le_induction with
      | base => exact hlev3 hp3
      | succ L hL ih =>
        exact hB L hL (ih (by omega)) (Ideal.pow_le_pow_right (by omega) hpd)
    exact hA d (key d hd le_rfl)

/-- `ν*(J_{x'}) = (2, 2, 3, ∞, ∞, …)` at the origin `x'`: the initial forms `z₁z₂`,
`z₁(z₁ + z₂)`, `f₃` form a standard base (Lemma 1). -/
private theorem nuStar_origin :
    nuStar (Localization.AtPrime (examplePx' k)) ((exampleJ k).map (algebraMap _ _)) =
      toLex (fun i : ℕ+ => if (i : ℕ) ≤ 2 then (2 : ℕ∞) else if (i : ℕ) = 3 then 3 else ⊤) := by
  classical
  set w : Fin 4 → ℕ := fun _ => 1 with hw
  set P := examplePx' k with hP
  have hPd := hPd' k
  have hX : ∀ i, IsWeightedHomogeneous w (X i : MvPolynomial (Fin 4) k) 1 := fun i =>
    isWeightedHomogeneous_X k w i
  have hf3 : IsWeightedHomogeneous w (exampleF₃ k) 3 :=
    ((((hX 0).add (hX 3)).pow 2).mul ((hX 0).add (hX 1))).sub
      ((((hX 1).add (hX 3)).pow 2).mul (hX 1))
  set g : Fin 3 → MvPolynomial (Fin 4) k := ![X 0 * X 1, X 0 * (X 0 + X 1), exampleF₃ k] with hg
  set dg : Fin 3 → ℕ := ![2, 2, 3] with hdg
  have hgh : ∀ j, IsWeightedHomogeneous w (g j) (dg j) := by
    intro j
    fin_cases j
    · exact (hX 0).mul (hX 1)
    · exact (hX 0).mul ((hX 0).add (hX 1))
    · exact hf3
  have hgP : ∀ j, g j ∈ P ^ dg j := fun j =>
    weightedHomogeneousComponent_eq_self (hgh j) ▸ wc_mem_pow w P hPd _ (g j)
  set f : Fin 3 → MvPolynomial (Fin 4) k := ![exampleF₁ k, exampleF₂ k, exampleF₃ k] with hf
  have hfJ : ∀ j, f j ∈ exampleJ k := by
    intro j
    fin_cases j <;> exact Ideal.subset_span (by simp [hf])
  have hfg : ∀ j, f j - g j ∈ P ^ (dg j + 1) := by
    intro j
    fin_cases j
    · show exampleF₁ k - X 0 * X 1 ∈ P ^ (2 + 1)
      rw [show exampleF₁ k - X 0 * X 1 = (X 0 + X 3) ^ 2 * X 2 by rw [exampleF₁]; ring]
      exact weightedHomogeneousComponent_eq_self ((((hX 0).add (hX 3)).pow 2).mul (hX 2)) ▸
        wc_mem_pow w P hPd _ _
    · show exampleF₂ k - X 0 * (X 0 + X 1) ∈ P ^ (2 + 1)
      rw [show exampleF₂ k - X 0 * (X 0 + X 1) = (X 1 + X 3) ^ 2 * X 2 by rw [exampleF₂]; ring]
      exact weightedHomogeneousComponent_eq_self ((((hX 1).add (hX 3)).pow 2).mul (hX 2)) ▸
        wc_mem_pow w P hPd _ _
    · simp [hf, hg]
  let φ : Fin 3 → AssocGraded (maximalIdeal (Localization.AtPrime P)) := fun j =>
    AssocGraded.mk _ (dg j) (algebraMap _ (Localization.AtPrime P) (g j))
      ((algebraMap_mem_pow_iff w P hPd _ _).mpr
        (weightedHomogeneousComponent_eq_self (hgh j) ▸ wc_mem_pow w P hPd _ (g j)))
  have hJ : ∀ j, φ j ∈ grIdeal (maximalIdeal (Localization.AtPrime P))
      ((exampleJ k).map (algebraMap _ _)) := by
    intro j
    have hfP : algebraMap _ (Localization.AtPrime P) (f j) ∈
        maximalIdeal (Localization.AtPrime P) ^ dg j := by
      rw [algebraMap_mem_pow_iff w P hPd]
      have := add_mem (hgP j) (Ideal.pow_le_pow_right (Nat.le_succ _) (hfg j))
      rwa [add_sub_cancel] at this
    have heq : φ j = AssocGraded.mk _ (dg j) (algebraMap _ (Localization.AtPrime P) (f j)) hfP := by
      refine mk_eq_mk _ _ _ ?_
      rw [← map_sub, ← neg_sub, map_neg]
      exact neg_mem ((algebraMap_mem_pow_iff w P hPd _ _).mpr (hfg j))
    rw [heq]
    exact mk_mem_grIdeal _ (Ideal.mem_map_of_mem _ (hfJ j)) _
  have hd : ∀ j, φ j ∈ AssocGraded.homogeneous (maximalIdeal (Localization.AtPrime P)) (dg j) :=
    fun j => AssocGraded.mk_mem_homogeneous _ _
  have h₁ : grIdeal (maximalIdeal (Localization.AtPrime P)) ((exampleJ k).map (algebraMap _ _)) =
      Ideal.span (Set.range φ) :=
    le_antisymm (grIdeal_le w P hPd g dg hgh (exampleJ k)
      (fun p hp d hpd => origin_sb k p hp d hpd))
      (Ideal.span_le.mpr (by rintro _ ⟨j, rfl⟩; exact hJ j))
  have h₂ : Monotone dg := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all
  have h₃ : ∀ i : Fin 3, φ i ∉ Ideal.span (Set.range fun j : Fin i =>
      φ (Fin.castLE i.2.le j)) := by
    intro i hmem
    obtain ⟨s₀, hs₀, hs₀0, c, -, hrel⟩ := exists_of_mk_mem_span w P hPd
      (fun j : Fin i => g (Fin.castLE i.2.le j)) (fun j => dg (Fin.castLE i.2.le j))
      (fun j => hgP _) (fun j => hgh _) (hgh i) (hgP i) hmem
    have hs₀C := eq_C_of_deg_zero k hs₀
    have hσ : s₀.coeff 0 ≠ 0 := fun h => hs₀0 (by rw [hs₀C, h, map_zero])
    rw [hs₀C] at hrel
    fin_cases i
    · have := congrArg (MvPolynomial.eval ![1, 1, 0, 0]) hrel
      simp [hg, hdg] at this
      exact hσ this
    · have := congrArg (MvPolynomial.eval ![1, 0, 0, 0]) hrel
      simp [hg, hdg] at this
      exact hσ this
    · have := congrArg (MvPolynomial.eval ![0, 1, 0, 0]) hrel
      simp [hg, hdg, exampleF₃] at this
      exact hσ this
  obtain ⟨hA, hB⟩ := nuI_eq_of_lemma1_properties (Localization.AtPrime P)
    ((exampleJ k).map (algebraMap _ _)) φ hJ dg hd h₁ h₂ h₃
  unfold nuStar
  congr 1
  funext i
  have hi := i.pos
  rcases (show (i : ℕ) = 1 ∨ (i : ℕ) = 2 ∨ (i : ℕ) = 3 ∨ 3 < (i : ℕ) by omega) with
    h | h | h | h
  · have := hA 0
    rw [show (⟨((0 : Fin 3) : ℕ) + 1, Nat.succ_pos _⟩ : ℕ+) = i from PNat.eq (by simp [h])]
      at this
    rw [this]
    simp [h, hdg]
  · have := hA 1
    rw [show (⟨((1 : Fin 3) : ℕ) + 1, Nat.succ_pos _⟩ : ℕ+) = i from PNat.eq (by simp [h])]
      at this
    rw [this]
    simp [h, hdg]
  · have := hA 2
    rw [show (⟨((2 : Fin 3) : ℕ) + 1, Nat.succ_pos _⟩ : ℕ+) = i from PNat.eq (by simp [h])]
      at this
    rw [this]
    simp [h, hdg]
  · rw [hB i h]
    simp [show ¬ (i : ℕ) ≤ 2 by omega, show (i : ℕ) ≠ 3 by omega]

/-- A substitution fixing the variables of weight `0` fixes every polynomial of weight `0`. -/
private theorem aeval_eq_self {σ : Type*} (w : σ → ℕ) (τ : σ → MvPolynomial σ k)
    (hτ : ∀ i, w i = 0 → τ i = X i) {s : MvPolynomial σ k} (hs : IsWeightedHomogeneous w s 0) :
    aeval τ s = s := by
  classical
  conv_rhs => rw [s.as_sum]
  conv_lhs => rw [s.as_sum]
  rw [map_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  rw [aeval_monomial, monomial_eq, MvPolynomial.algebraMap_eq]
  congr 1
  refine Finsupp.prod_congr fun i hi => ?_
  have hw0 : Finsupp.weight w m = 0 := hs (mem_support_iff.mp hm)
  rw [Finsupp.weight_apply, Finsupp.sum, Finset.sum_eq_zero_iff] at hw0
  have := hw0 i hi
  rw [smul_eq_mul, mul_eq_zero] at this
  rw [hτ i (this.resolve_left (Finsupp.mem_support_iff.mp hi))]

/-- `(z₁, z₂, y)` is the ideal of the variables of weight `1` for the weights `(1, 1, 0, 1)` on
`(z₁, z₂, x, y)`. -/
private theorem hPd (d : ℕ) (p : MvPolynomial (Fin 4) k) :
    p ∈ examplePx k ^ d ↔ ∀ m ∈ p.support, d ≤ Finsupp.weight (![1, 1, 0, 1] : Fin 4 → ℕ) m := by
  have h : examplePx k = Ideal.span ((X : Fin 4 → MvPolynomial (Fin 4) k) ''
      {i | (![1, 1, 0, 1] : Fin 4 → ℕ) i = 1}) := by
    rw [examplePx]
    congr 1
    ext q
    constructor
    · rintro (rfl | rfl | rfl)
      exacts [⟨0, rfl, rfl⟩, ⟨1, rfl, rfl⟩, ⟨3, rfl, rfl⟩]
    · rintro ⟨i, hi, rfl⟩
      fin_cases i <;> simp_all
  rw [h]
  exact mem_pow_span_X_iff _ (fun i => by fin_cases i <;> simp) d p

/-- The independence step at `x`: a relation `s₀ f₂ = c₀ f₁` with `s₀, c₀ ∈ k[x]` (weight `0`)
forces `s₀ = 0`.  (Substituting `(z₁, z₂, y) = (1, 0, 0)` gives `s₀ = c₀x`, and
`(z₁, z₂, y) = (1, −1, 0)` gives `s₀x = c₀(x − 1)`, whence `c₀(x² − x + 1) = 0`.) -/
private theorem generic_indep {s₀ c₀ : MvPolynomial (Fin 4) k}
    (hs : IsWeightedHomogeneous (![1, 1, 0, 1] : Fin 4 → ℕ) s₀ 0)
    (hc : IsWeightedHomogeneous (![1, 1, 0, 1] : Fin 4 → ℕ) c₀ 0)
    (h : s₀ * exampleF₂ k = c₀ * exampleF₁ k) : s₀ = 0 := by
  have hfix : ∀ (τ : Fin 4 → MvPolynomial (Fin 4) k), τ 2 = X 2 → ∀ q,
      IsWeightedHomogeneous (![1, 1, 0, 1] : Fin 4 → ℕ) q 0 → aeval τ q = q := by
    intro τ hτ q hq
    refine aeval_eq_self k _ τ (fun i hi => ?_) hq
    fin_cases i
    · simp at hi
    · simp at hi
    · exact hτ
    · simp at hi
  have e1 := congrArg (aeval (R := k) (![1, 0, X 2, 0] : Fin 4 → MvPolynomial (Fin 4) k)) h
  have e2 := congrArg (aeval (R := k) (![1, -1, X 2, 0] : Fin 4 → MvPolynomial (Fin 4) k)) h
  rw [map_mul, map_mul, hfix ![1, 0, X 2, 0] rfl _ hs, hfix ![1, 0, X 2, 0] rfl _ hc] at e1
  rw [map_mul, map_mul, hfix ![1, -1, X 2, 0] rfl _ hs, hfix ![1, -1, X 2, 0] rfl _ hc] at e2
  simp [exampleF₁, exampleF₂] at e1 e2
  have hq : c₀ * (X 2 ^ 2 - X 2 + 1) = 0 := by linear_combination (-(X 2)) * e1 + e2
  rcases mul_eq_zero.mp hq with h0 | h0
  · linear_combination e1 + X 2 * h0
  · have := congrArg (MvPolynomial.eval (fun _ => (0 : k))) h0
    simp at this

/-- `ν*(J_x) = (2, 2, ∞, ∞, …)` at the point `x` of `(z₁, z₂, y)`: since
`x f₃ = (z₁ + z₂) f₁ − z₂ f₂` and `x` is a unit at `x`, `J_x = (f₁, f₂)`; `f₁`, `f₂` are
homogeneous of degree `2` for the weights `(1, 1, 0, 1)`, so their initial forms generate
`gr(J_x)` and are independent. -/
private theorem nuStar_generic :
    nuStar (Localization.AtPrime (examplePx k)) ((exampleJ k).map (algebraMap _ _)) =
      toLex (fun i : ℕ+ => if (i : ℕ) ≤ 2 then (2 : ℕ∞) else ⊤) := by
  classical
  set w : Fin 4 → ℕ := ![1, 1, 0, 1] with hw
  set P := examplePx k with hP
  have hPd := hPd k
  have hX0 : IsWeightedHomogeneous w (X 0 : MvPolynomial (Fin 4) k) 1 :=
    isWeightedHomogeneous_X k w 0
  have hX1 : IsWeightedHomogeneous w (X 1 : MvPolynomial (Fin 4) k) 1 :=
    isWeightedHomogeneous_X k w 1
  have hX2 : IsWeightedHomogeneous w (X 2 : MvPolynomial (Fin 4) k) 0 :=
    isWeightedHomogeneous_X k w 2
  have hX3 : IsWeightedHomogeneous w (X 3 : MvPolynomial (Fin 4) k) 1 :=
    isWeightedHomogeneous_X k w 3
  have hf1 : IsWeightedHomogeneous w (exampleF₁ k) 2 :=
    (hX0.mul hX1).add (((hX0.add hX3).pow 2).mul hX2)
  have hf2 : IsWeightedHomogeneous w (exampleF₂ k) 2 :=
    (hX0.mul (hX0.add hX1)).add (((hX1.add hX3).pow 2).mul hX2)
  set g : Fin 2 → MvPolynomial (Fin 4) k := ![exampleF₁ k, exampleF₂ k] with hg
  set dg : Fin 2 → ℕ := ![2, 2] with hdg
  have hdg2 : ∀ j, dg j = 2 := by intro j; fin_cases j <;> rfl
  have hgh : ∀ j, IsWeightedHomogeneous w (g j) (dg j) := by
    intro j
    fin_cases j
    · exact hf1
    · exact hf2
  have hgP : ∀ j, g j ∈ P ^ dg j := fun j =>
    weightedHomogeneousComponent_eq_self (hgh j) ▸ wc_mem_pow w P hPd _ (g j)
  -- `J_x = (f₁, f₂)`, since `x f₃ = (z₁ + z₂) f₁ − z₂ f₂` and `x ∉ (z₁, z₂, y)`
  have hX2P : (X 2 : MvPolynomial (Fin 4) k) ∉ P := by
    intro h
    have := (hPd 1 (X 2)).mp (by rwa [pow_one]) (Finsupp.single 2 1) (by simp [support_X])
    simp [Finsupp.weight_single] at this
  have hJeq : (exampleJ k).map (algebraMap _ (Localization.AtPrime P)) =
      (Ideal.span {exampleF₁ k, exampleF₂ k}).map (algebraMap _ (Localization.AtPrime P)) := by
    refine le_antisymm ?_ (Ideal.map_mono (Ideal.span_mono ?_))
    · rw [exampleJ, Ideal.map_span, Ideal.span_le]
      rintro _ ⟨q, hq, rfl⟩
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hq
      rcases hq with rfl | rfl | rfl
      · exact Ideal.mem_map_of_mem _ (Ideal.subset_span (by simp))
      · exact Ideal.mem_map_of_mem _ (Ideal.subset_span (by simp))
      · have hu : IsUnit (algebraMap _ (Localization.AtPrime P)
            (X 2 : MvPolynomial (Fin 4) k)) :=
          IsLocalization.map_units _ (⟨X 2, hX2P⟩ : P.primeCompl)
        rw [SetLike.mem_coe, ← Ideal.unit_mul_mem_iff_mem _ hu, ← map_mul,
          show X 2 * exampleF₃ k = (X 0 + X 1) * exampleF₁ k - X 1 * exampleF₂ k by
            simp only [exampleF₁, exampleF₂, exampleF₃]; ring]
        exact Ideal.mem_map_of_mem _ (sub_mem
          (Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp)))
          (Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp))))
    · intro q hq
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hq ⊢
      tauto
  rw [hJeq]
  set J' : Ideal (MvPolynomial (Fin 4) k) := Ideal.span {exampleF₁ k, exampleF₂ k} with hJ'
  have hgJ : ∀ j, g j ∈ J' := by
    intro j
    fin_cases j <;> exact Ideal.subset_span (by simp [hg])
  let φ : Fin 2 → AssocGraded (maximalIdeal (Localization.AtPrime P)) := fun j =>
    AssocGraded.mk _ (dg j) (algebraMap _ (Localization.AtPrime P) (g j))
      ((algebraMap_mem_pow_iff w P hPd _ _).mpr
        (weightedHomogeneousComponent_eq_self (hgh j) ▸ wc_mem_pow w P hPd _ (g j)))
  have hJ : ∀ j, φ j ∈ grIdeal (maximalIdeal (Localization.AtPrime P))
      (J'.map (algebraMap _ _)) :=
    fun j => mk_mem_grIdeal _ (Ideal.mem_map_of_mem _ (hgJ j)) _
  have hd : ∀ j, φ j ∈ AssocGraded.homogeneous (maximalIdeal (Localization.AtPrime P)) (dg j) :=
    fun j => AssocGraded.mk_mem_homogeneous _ _
  -- standard base: `f₁`, `f₂` are weighted homogeneous
  have hsb : ∀ p ∈ J', ∀ d, p ∈ P ^ d →
      weightedHomogeneousComponent w d p ∈ Ideal.span (Set.range g) := by
    intro p hp d _
    obtain ⟨a, b, rfl⟩ := Ideal.mem_span_pair.mp hp
    rw [map_add, wc_mul_homogeneous w hf1, wc_mul_homogeneous w hf2]
    refine add_mem ?_ ?_
    · split_ifs
      · exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨0, rfl⟩)
      · exact zero_mem _
    · split_ifs
      · exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨1, rfl⟩)
      · exact zero_mem _
  have h₁ : grIdeal (maximalIdeal (Localization.AtPrime P)) (J'.map (algebraMap _ _)) =
      Ideal.span (Set.range φ) :=
    le_antisymm (grIdeal_le w P hPd g dg hgh J' hsb)
      (Ideal.span_le.mpr (by rintro _ ⟨j, rfl⟩; exact hJ j))
  have h₂ : Monotone dg := fun i j _ => by rw [hdg2 i, hdg2 j]
  have hne : exampleF₁ k ≠ 0 := fun h => by
    have := congrArg (MvPolynomial.eval ![1, 1, 0, 0]) h
    simp [exampleF₁] at this
  have h₃ : ∀ i : Fin 2, φ i ∉ Ideal.span (Set.range fun j : Fin i =>
      φ (Fin.castLE i.2.le j)) := by
    intro i hmem
    obtain ⟨s₀, hs₀, hs₀0, c, hc, hrel⟩ := exists_of_mk_mem_span w P hPd
      (fun j : Fin i => g (Fin.castLE i.2.le j)) (fun j => dg (Fin.castLE i.2.le j))
      (fun j => hgP _) (fun j => hgh _) (hgh i) (hgP i) hmem
    have hc0 : ∀ j, IsWeightedHomogeneous w (c j) 0 := fun j => by simpa [hdg2] using hc j
    fin_cases i
    · simp [hg, hs₀0, hne] at hrel
    · simp [hg, hdg2] at hrel
      exact hs₀0 (generic_indep k hs₀ (hc0 _) hrel)
  obtain ⟨hA, hB⟩ := nuI_eq_of_lemma1_properties (Localization.AtPrime P)
    (J'.map (algebraMap _ _)) φ hJ dg hd h₁ h₂ h₃
  unfold nuStar
  congr 1
  funext i
  have hi := i.pos
  rcases (show (i : ℕ) = 1 ∨ (i : ℕ) = 2 ∨ 2 < (i : ℕ) by omega) with h | h | h
  · have := hA 0
    rw [show (⟨((0 : Fin 2) : ℕ) + 1, Nat.succ_pos _⟩ : ℕ+) = i from PNat.eq (by simp [h])]
      at this
    rw [this]
    simp [h, hdg]
  · have := hA 1
    rw [show (⟨((1 : Fin 2) : ℕ) + 1, Nat.succ_pos _⟩ : ℕ+) = i from PNat.eq (by simp [h])]
      at this
    rw [this]
    simp [h, hdg]
  · rw [hB i h]
    simp [show ¬ (i : ℕ) ≤ 2 by omega]

end RemarkComputation

/-- The Remark, pp. 220–221: "It is not true in general that, if `x' ∈ X` is a specialization of
`x ∈ X`, then `ν*(J_{x'}) ≥ ν*(J_x)`. For example, let `X = Spec(k[z₁, z₂, x, y])` where
`(z₁, z₂, x, y)` is a system of four independent variables over any field `k`, and let `J` be the
sheaf of ideals on `X` which is generated by `f₁ = z₁z₂ + (z₁ + y)²x`,
`f₂ = z₁(z₁ + z₂) + (z₂ + y)²x` and `f₃ = (z₁ + y)²(z₁ + z₂) − (z₂ + y)²z₂`. Let `x` (resp. `x'`)
be the point of `X` which corresponds to the prime ideal `(z₁, z₂, y) k[z₁, z₂, x, y]` (resp. to
`(z₁, z₂, y, x) k[z₁, z₂, y, x]`). Then `x'` is a specialization of `x` on `X`, and
`ν*(J_x) = (2, 2, ∞, ∞, …)` while `ν*(J_{x'}) = (2, 2, 3, ∞, ∞, …)`, so that `ν*(J_x) > ν*(J_{x'})`."

The first conjunct is the general claim for this `X` and `J` (the negation of the monotonicity
statement over all pairs of points `x ⤳ x'` of `Spec(k[z₁, z₂, x, y])`); the remaining conjuncts
are the example as printed.  `X = Spec(k[z₁, z₂, x, y])` is `PrimeSpectrum (MvPolynomial (Fin 4) k)`,
the local rings of `X` are the localizations at primes (regular local rings, `MvPolynomial` over
a field being a regular ring in Mathlib), and `J_x` is `JA_x`.

Deviation from the paper (statement modified): the first conjunct (the general claim for this
`X` and `J`) is added to the example as printed; it follows from the other conjuncts.

Deviation from the paper (gap filled): the paper gives no computation.  The two values of `ν*`
are obtained from Lemma 1 (`nuI_eq_of_lemma1_properties`): at `x`, `J_x = (f₁, f₂)` (as
`x f₃ = (z₁ + z₂) f₁ − z₂ f₂`) with `f₁`, `f₂` homogeneous of degree `2` for the weights
`(1, 1, 0, 1)` on `(z₁, z₂, x, y)` (`nuStar_generic`); at `x'`, the initial forms `z₁z₂`,
`z₁(z₁ + z₂)`, `f₃` of `f₁`, `f₂`, `f₃` form a standard base, checked by lifting the syzygies of
the initial forms (`origin_sb`, `nuStar_origin`). -/
@[blueprint "rem:III.3-specialization"
  (statement := /-- It is not true in general that, if $x'\in X$ is a specialization of
    $x\in X$, then $\nu^*(J_{x'})\ge\nu^*(J_x)$. For example, let
    $X=\operatorname{Spec}(k[z_1,z_2,x,y])$ where $(z_1,z_2,x,y)$ is a system of four
    independent variables over any field $k$, and let $J$ be the sheaf of ideals on $X$ which
    is generated by $f_1=z_1z_2+(z_1+y)^2x$, $f_2=z_1(z_1+z_2)+(z_2+y)^2x$ and
    $f_3=(z_1+y)^2(z_1+z_2)-(z_2+y)^2z_2$. Let $x$ (resp.\ $x'$) be the point of $X$ which
    corresponds to the prime ideal $(z_1,z_2,y)k[z_1,z_2,x,y]$ (resp.\ to
    $(z_1,z_2,y,x)k[z_1,z_2,y,x]$). Then $x'$ is a specialization of $x$ on $X$, and
    $\nu^*(J_x)=(2,2,\infty,\infty,\dots)$ while $\nu^*(J_{x'})=(2,2,3,\infty,\infty,\dots)$,
    so that $\nu^*(J_x)>\nu^*(J_{x'})$. (Remark, pp.~220--221.) -/)
  (proof := /-- (The paper gives no computation.) Since $xf_3=(z_1+z_2)f_1-z_2f_2$ and $x$
    is a unit at $x$, $J_x=(f_1,f_2)$, whose initial forms $Z_1Z_2+x(Z_1+Y)^2$ and
    $Z_1^2+Z_1Z_2+x(Z_2+Y)^2$ in $\operatorname{gr}(\mathcal O_{X,x})=k(x)[Z_1,Z_2,Y]$ form a
    standard base, so $\nu^*(J_x)=(2,2,\infty,\dots)$. At $x'$ the initial forms of
    $f_1,f_2,f_3$ in $k[Z_1,Z_2,X,Y]$ are $Z_1Z_2$, $Z_1^2+Z_1Z_2$ and
    $(Z_1+Y)^2(Z_1+Z_2)-(Z_2+Y)^2Z_2$, the last of degree $3$ and not in $(Z_1Z_2,Z_1^2)$, so
    $\nu^*(J_{x'})=(2,2,3,\infty,\dots)$. Finally $(z_1,z_2,y)\subseteq(z_1,z_2,y,x)$ gives
    the specialization, and $(2,2,3,\infty,\dots)<(2,2,\infty,\dots)$ lexicographically.

    \textbf{Gap in the paper filled.} The paper gives no computation of the two sequences
    $\nu^*$; the computation above (the second one by lifting the syzygies of the initial
    forms at $x'$) is supplied by the formalization. The formal statement also records the
    general claim for this $X$ and $J$ (that $\nu^*$ is not monotone under specialization),
    which follows from the example. -/)
  (latexEnv := "remark")]
theorem not_forall_specializes_nuStar_le :
    (¬ ∀ x x' : PrimeSpectrum (MvPolynomial (Fin 4) k), x ⤳ x' →
        nuStar (Localization.AtPrime x.asIdeal) ((exampleJ k).map (algebraMap _ _)) ≤
          nuStar (Localization.AtPrime x'.asIdeal) ((exampleJ k).map (algebraMap _ _))) ∧
    examplePt k ⤳ examplePt' k ∧
    nuStar (Localization.AtPrime (examplePx k)) ((exampleJ k).map (algebraMap _ _)) =
      toLex (fun i : ℕ+ => if (i : ℕ) ≤ 2 then (2 : ℕ∞) else ⊤) ∧
    nuStar (Localization.AtPrime (examplePx' k)) ((exampleJ k).map (algebraMap _ _)) =
      toLex (fun i : ℕ+ => if (i : ℕ) ≤ 2 then (2 : ℕ∞) else if (i : ℕ) = 3 then 3 else ⊤) ∧
    nuStar (Localization.AtPrime (examplePx' k)) ((exampleJ k).map (algebraMap _ _)) <
      nuStar (Localization.AtPrime (examplePx k)) ((exampleJ k).map (algebraMap _ _)) := by
  -- the two computations of `ν*`
  have h₂ : nuStar (Localization.AtPrime (examplePx k)) ((exampleJ k).map (algebraMap _ _)) =
      toLex (fun i : ℕ+ => if (i : ℕ) ≤ 2 then (2 : ℕ∞) else ⊤) :=
    nuStar_generic k
  have h₃ : nuStar (Localization.AtPrime (examplePx' k)) ((exampleJ k).map (algebraMap _ _)) =
      toLex (fun i : ℕ+ => if (i : ℕ) ≤ 2 then (2 : ℕ∞) else if (i : ℕ) = 3 then 3 else ⊤) :=
    nuStar_origin k
  -- `x'` is a specialization of `x`: `(z₁, z₂, y) ⊆ (z₁, z₂, y, x)`.
  have hspec : examplePt k ⤳ examplePt' k :=
    (PrimeSpectrum.le_iff_specializes _ _).mp (Ideal.span_mono
      (Set.insert_subset_insert (Set.insert_subset_insert (Set.subset_insert _ _))))
  -- `(2, 2, 3, ∞, …) < (2, 2, ∞, …)` in the lexicographic order: the sequences agree below
  -- the third term, where `3 < ∞`.
  have hlt : nuStar (Localization.AtPrime (examplePx' k)) ((exampleJ k).map (algebraMap _ _)) <
      nuStar (Localization.AtPrime (examplePx k)) ((exampleJ k).map (algebraMap _ _)) := by
    rw [h₂, h₃]
    refine ⟨3, fun j hj => ?_, ?_⟩
    · have hj' : (j : ℕ) ≤ 2 := by
        have := (PNat.coe_lt_coe j 3).mpr hj
        simp only [PNat.val_ofNat] at this
        omega
      simp [hj']
    · show (if ((3 : ℕ+) : ℕ) ≤ 2 then (2 : ℕ∞) else if ((3 : ℕ+) : ℕ) = 3 then 3 else ⊤) <
        (if ((3 : ℕ+) : ℕ) ≤ 2 then (2 : ℕ∞) else ⊤)
      decide
  exact ⟨fun h => absurd (h _ _ hspec) (not_le.mpr hlt), hspec, h₂, h₃, hlt⟩

end Remark

end Hironaka

