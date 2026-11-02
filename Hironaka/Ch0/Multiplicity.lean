/-
Copyright (c) 2026 Daattavya Aggarwal, Minhyong Kim, Oisin Kim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daattavya Aggarwal, Minhyong Kim, Oisin Kim
-/
module

public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Architect
public import Hironaka.Compat.Graded
public import Hironaka.Ch0.AlgebraicScheme
public import Hironaka.Compat.HypersurfaceMultiplicity
public import Hironaka.Statements

/-!
# Hilbert–Samuel functions and multiplicity

Hironaka uses the multiplicity `e(O_{X,x})` of the local rings of an algebraic scheme in the
sense of Samuel (Ch. 0 §4 (I) "equi-multiple", Ch. II) without redefining it; his reference is
Zariski–Samuel, *Commutative Algebra* Vol. II, Ch. VIII.  Ch. 0 §4, p. 133:

> If A is a noetherian local ring and m is the maximal ideal of A, then we have a polynomial
> H(p) with rational coefficients such that for all sufficiently large integers p the value H(p)
> of the polynomial is equal to the sum of ranks of the (A/m)-modules gr^i_m(A) with 0 ≤ i ≤ p.
> The degree of the polynomial is equal to the Krull dimension of A, say d, and the coefficient
> of the term of degree d of H(p) is of the form e(A)/d! where e(A) is a positive integer. This
> integer e(A) is called the multiplicity of the local ring A. … Let X be a local-ringed space.
> If O_{X,x} is noetherian, then e(O_{X,x}) will be called the multiplicity of X at the point x. …

We define `e(R)` from that polynomial and record its existence as a cited leaf (cited through
footnote 3 of the Introduction, p. 116, which refers the theory of local rings to Ch. VII and VIII
of Zariski–Samuel).
-/

@[expose] public section

open IsLocalRing Polynomial Filter TopologicalSpace AlgebraicGeometry

universe u

namespace Hironaka

section LocalRing




/-- Samuel's theorem: for a noetherian local ring the Hilbert–Samuel function is eventually a
polynomial of degree `dim R`, and `(dim R)!` times its leading coefficient is a positive
integer.  Cited, not proved in the paper: p. 133 states it without a proof or a local
reference, and footnote 3 of the Introduction (p. 116) cites the theory of local rings as a
whole: "The two chapters, VII and VIII, of Samuel-Zariski, [18], should cover all that we need
from the theory of local rings.  A complete reference to the theory may be obtained from
M. Nagata [15]."  The fact is in Zariski–Samuel, Vol. II, Ch. VIII.

Classified as cited, through footnote 3. -/
@[blueprint "thm:hilbert-samuel"
  (statement := /-- Let $R$ be a noetherian local ring of dimension $d$. There is a polynomial
    $P_R\in\mathbb Q[T]$ of degree $d$ with $H_R(n)=P_R(n)$ for all large $n$, and $d!$ times
    the leading coefficient of $P_R$ is a positive integer, the \emph{multiplicity} $e(R)$. -/)
  (proof := /-- Cited, not proved in the paper. P.~133 states the fact (``we have a
    polynomial $H(p)$ \dots'') without a proof or a local reference; footnote~3 of the
    Introduction (p.~116) cites the theory of local rings as a whole: ``The two chapters, VII
    and VIII, of Samuel-Zariski, [18], should cover all that we need from the theory of local
    rings. A complete reference to the theory may be obtained from M. Nagata [15].'' The
    Hilbert--Samuel theorem is in Zariski--Samuel, Vol.~II, Ch.~VIII (see also
    Atiyah--Macdonald, Prop.~11.4 and Th.~11.14).
    The fact is thus cited through footnote~3. -/)
  (latexEnv := "theorem")]
theorem exists_hilbertSamuelPoly [Hironaka.Cited.ExistsHilbertSamuelPoly.{u}] :
    ∀ (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R],
    ∃ p : ℚ[X], (∀ᶠ n : ℕ in atTop, p.eval (n : ℚ) = (hilbertSamuel R n : ℚ)) ∧
      p.natDegree = dimNat R ∧
      ∃ e : ℕ, 0 < e ∧ ((dimNat R).factorial : ℚ) * p.leadingCoeff = e :=
  @Hironaka.Cited.ExistsHilbertSamuelPoly.exists_hilbertSamuelPoly _

open scoped Classical in
/-- The Hilbert–Samuel polynomial of `R`: the polynomial agreeing with `H_R` for large `n`
(unique when it exists, `hilbertSamuelPoly_unique`; `0` otherwise). -/
noncomputable def hilbertSamuelPoly (R : Type u) [CommRing R] [IsLocalRing R] : ℚ[X] :=
  if h : ∃ p : ℚ[X], ∀ᶠ n : ℕ in atTop, p.eval (n : ℚ) = (hilbertSamuel R n : ℚ) then
    Classical.choose h
  else 0

/-- Two polynomials over `ℚ` agreeing with `H_R` for all large `n` are equal. -/
theorem hilbertSamuelPoly_unique (R : Type u) [CommRing R] [IsLocalRing R] {p q : ℚ[X]}
    (hp : ∀ᶠ n : ℕ in atTop, p.eval (n : ℚ) = (hilbertSamuel R n : ℚ))
    (hq : ∀ᶠ n : ℕ in atTop, q.eval (n : ℚ) = (hilbertSamuel R n : ℚ)) : p = q := by
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp (hp.and hq)
  refine Polynomial.eq_of_infinite_eval_eq p q
    (Set.infinite_of_injective_forall_mem (f := fun n : ℕ => ((n + N : ℕ) : ℚ)) ?_ ?_)
  · intro a b hab
    have : a + N = b + N := Nat.cast_injective hab
    omega
  · intro n
    obtain ⟨h1, h2⟩ := hN (n + N) (by omega)
    exact h1.trans h2.symm

/-- The defining property of the Hilbert–Samuel polynomial, for noetherian `R`. -/
theorem hilbertSamuelPoly_spec [Hironaka.Cited.ExistsHilbertSamuelPoly.{u}] (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] :
    ∀ᶠ n : ℕ in atTop, (hilbertSamuelPoly R).eval (n : ℚ) = (hilbertSamuel R n : ℚ) := by
  have h : ∃ p : ℚ[X], ∀ᶠ n : ℕ in atTop, p.eval (n : ℚ) = (hilbertSamuel R n : ℚ) :=
    let ⟨p, hp, _⟩ := exists_hilbertSamuelPoly R
    ⟨p, hp⟩
  rw [hilbertSamuelPoly, dite_eq_left h]
  exact Classical.choose_spec h

/-- The multiplicity `e(R)`: `(dim R)!` times the coefficient of `T^{dim R}` in the
Hilbert–Samuel polynomial. -/
@[blueprint "def:multiplicity"
  (statement := /-- The \emph{multiplicity} of a noetherian local ring $R$ of dimension $d$ is
    $e(R)=d!\cdot(\text{coefficient of }T^d\text{ in }P_R)$, a positive integer by
    \cref{thm:hilbert-samuel}.
    Formalization note (encoding): $e(R)$ is defined for every local ring as
    $\lfloor d!\cdot c_d\rfloor$, $c_d$ the coefficient of $T^d$ in the polynomial agreeing with
    $H_R$ for large $n$ (zero if none exists); for noetherian $R$ it is the multiplicity. -/)
  (latexEnv := "definition")]
noncomputable def samuelMultiplicity (R : Type u) [CommRing R] [IsLocalRing R] : ℕ :=
  ⌊((dimNat R).factorial : ℚ) * (hilbertSamuelPoly R).coeff (dimNat R)⌋₊

/-! ### Invariance under ring isomorphisms

(Public form of the lemmas that `Hironaka/Ch2/Flatness.lean`, `Hironaka/Ch2/GradedIdeal.lean` and
`Hironaka/Compat/LocallyPrincipalConverse.lean` each carried as a private copy.) -/

/-- A ring isomorphism carrying `I` to `J` identifies `grᵖ_I` with `grᵖ_J` (semilinearly). -/
theorem finrank_grPiece_eq_of_ringEquiv {A B : Type u} [CommRing A] [CommRing B]
    (e : A ≃+* B) (I : Ideal A) (J : Ideal B) (hIJ : I.map (e : A →+* B) = J) (n : ℕ) :
    Module.finrank (A ⧸ I) (GrPiece I n) = Module.finrank (B ⧸ J) (GrPiece J n) := by
  have := RingHomInvPair.of_ringEquiv e
  have := RingHomInvPair.symm (e : A →+* B) (e.symm : B →+* A)
  let f₀ : A ≃ₛₗ[(e : A →+* B)] B := e.toSemilinearEquiv
  have hpow : ∀ k, J ^ k = (I ^ k).comap (e.symm : B →+* A) := by
    intro k
    rw [← hIJ, ← Ideal.map_pow, Ideal.map_comap_of_equiv]
    rfl
  have hmap : ∀ k, Submodule.map (f₀ : A →ₛₗ[(e : A →+* B)] B) (I ^ k) = J ^ k := by
    intro k
    ext x
    rw [Submodule.mem_map, hpow k, Ideal.mem_comap]
    constructor
    · rintro ⟨y, hy, rfl⟩
      simpa [f₀] using hy
    · intro hx
      exact ⟨e.symm x, hx, by simp [f₀]⟩
  let g₀ : ↥(I ^ n) ≃ₛₗ[(e : A →+* B)] ↥(J ^ n) :=
    (f₀.submoduleMap (I ^ n)).trans (LinearEquiv.ofEq _ _ (hmap n))
  have hq : (Submodule.comap (I ^ n).subtype (I ^ (n + 1))).map
      (g₀ : ↥(I ^ n) →ₛₗ[(e : A →+* B)] ↥(J ^ n)) =
      Submodule.comap (J ^ n).subtype (J ^ (n + 1)) := by
    rw [Submodule.map_equiv_eq_comap_symm]
    ext ⟨x, hx⟩
    show ((g₀.symm ⟨x, hx⟩ : ↥(I ^ n)) : A) ∈ I ^ (n + 1) ↔ x ∈ J ^ (n + 1)
    rw [hpow (n + 1), Ideal.mem_comap]
    rfl
  let j : GrPiece I n ≃ₛₗ[(e : A →+* B)] GrPiece J n := Submodule.Quotient.equiv _ _ g₀ hq
  let i : A ⧸ I ≃+* B ⧸ J := Ideal.quotientEquiv I J e hIJ.symm
  unfold Module.finrank
  rw [rank_eq_of_equiv_equiv i j.toAddEquiv i.bijective]
  intro r m
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective r
  have h1 : (Ideal.Quotient.mk I a) • m = a • m := algebraMap_smul (A ⧸ I) a m
  have h2 : i (Ideal.Quotient.mk I a) = Ideal.Quotient.mk J (e a) := rfl
  have h3 : (Ideal.Quotient.mk J (e a)) • j m = e a • j m := algebraMap_smul (B ⧸ J) (e a) (j m)
  rw [h1, h2]
  change j (a • m) = Ideal.Quotient.mk J (e a) • j m
  rw [h3]
  exact j.map_smulₛₗ a m

/-- `H_R` is invariant under ring isomorphisms. -/
theorem hilbertSamuel_eq_of_ringEquiv {A B : Type u} [CommRing A] [CommRing B]
    [IsLocalRing A] [IsLocalRing B] (e : A ≃+* B) (n : ℕ) :
    hilbertSamuel A n = hilbertSamuel B n := by
  have hm : (IsLocalRing.maximalIdeal A).map (e : A →+* B) = IsLocalRing.maximalIdeal B :=
    IsLocalRing.map_ringEquiv_maximalIdeal e
  unfold hilbertSamuel
  exact Finset.sum_congr rfl fun i _ => finrank_grPiece_eq_of_ringEquiv e _ _ hm i

/-- The multiplicity `e(R)` is invariant under ring isomorphisms. -/
theorem samuelMultiplicity_eq_of_ringEquiv {A B : Type u} [CommRing A] [CommRing B]
    [IsLocalRing A] [IsLocalRing B] (e : A ≃+* B) :
    samuelMultiplicity A = samuelMultiplicity B := by
  have hf : hilbertSamuel A = hilbertSamuel B := funext (hilbertSamuel_eq_of_ringEquiv e)
  have hd : dimNat A = dimNat B := by
    unfold dimNat
    rw [ringKrullDim_eq_of_ringEquiv e]
  have hp : hilbertSamuelPoly A = hilbertSamuelPoly B := by
    unfold hilbertSamuelPoly
    rw [hf]
  unfold samuelMultiplicity
  rw [hd, hp]

/-- `(1/e!) ∏_{i<e} (T + a + i + 1)`, the polynomial `T ↦ C(T + a + e, e)`. -/
noncomputable def binomPoly (e : ℕ) (a : ℚ) : ℚ[X] :=
  C (1 / (e.factorial : ℚ)) * ∏ i ∈ Finset.range e, (X + C (a + i + 1))

theorem prod_range_cast_add_eq (m e : ℕ) :
    ∏ i ∈ Finset.range e, ((m : ℚ) + i + 1) = (e.factorial : ℚ) * ((m + e).choose e : ℕ) := by
  induction e with
  | zero => simp
  | succ e ih =>
    rw [Finset.prod_range_succ, ih]
    have h := Nat.add_one_mul_choose_eq (m + e) e
    have h' : ((m + e + 1 : ℕ) : ℚ) * ((m + e).choose e : ℕ) =
        ((m + e + 1).choose (e + 1) : ℕ) * ((e + 1 : ℕ) : ℚ) := by exact_mod_cast h
    rw [show m + (e + 1) = m + e + 1 by ring, Nat.factorial_succ]
    push_cast at h' ⊢
    calc (e.factorial : ℚ) * ((m + e).choose e : ℕ) * ((m : ℚ) + e + 1)
        = (e.factorial : ℚ) * (((m : ℚ) + e + 1) * ((m + e).choose e : ℕ)) := by ring
      _ = (e.factorial : ℚ) * (((m + e + 1).choose (e + 1) : ℕ) * ((e : ℚ) + 1)) := by rw [h']
      _ = ((e : ℚ) + 1) * e.factorial * ((m + e + 1).choose (e + 1) : ℕ) := by ring

theorem eval_binomPoly (e m n : ℕ) (a : ℚ) (h : (n : ℚ) + a = m) :
    (binomPoly e a).eval (n : ℚ) = ((m + e).choose e : ℕ) := by
  unfold binomPoly
  rw [eval_mul, eval_C, eval_prod]
  have : ∀ i ∈ Finset.range e, ((X + C (a + i + 1) : ℚ[X]).eval (n : ℚ)) = (m : ℚ) + i + 1 := by
    intro i _
    rw [eval_add, eval_X, eval_C, ← h]
    ring
  rw [Finset.prod_congr rfl this, prod_range_cast_add_eq]
  have : (e.factorial : ℚ) ≠ 0 := by positivity
  field_simp

theorem coeff_binomPoly (e : ℕ) (a : ℚ) : (binomPoly e a).coeff e = 1 / (e.factorial : ℚ) := by
  unfold binomPoly
  rw [coeff_C_mul]
  have hm : (∏ i ∈ Finset.range e, (X + C (a + i + 1) : ℚ[X])).Monic :=
    monic_prod_of_monic _ _ fun i _ => monic_X_add_C _
  have hd : (∏ i ∈ Finset.range e, (X + C (a + i + 1) : ℚ[X])).natDegree = e := by
    rw [natDegree_prod_of_monic _ _ fun i _ => monic_X_add_C _]
    simp only [natDegree_X_add_C]
    simp
  have h1 := hm.coeff_natDegree
  rw [hd] at h1
  rw [h1, mul_one]

/-- `Σ_{j<ν} C(n - j + e, e) + C(n + 1 - ν + e, e + 1) = C(n + 1 + e, e + 1)` for `ν ≤ n + 1`. -/
theorem sum_choose_add_eq (e n : ℕ) : ∀ ν, ν ≤ n + 1 →
    ∑ j ∈ Finset.range ν, (n - j + e).choose e + (n + 1 - ν + e).choose (e + 1) =
      (n + 1 + e).choose (e + 1) := by
  intro ν
  induction ν with
  | zero => intro _; simp
  | succ ν ih =>
    intro hν
    have h1 := ih (by omega)
    rw [Finset.sum_range_succ]
    have h2 : n + 1 - ν + e = (n - ν) + e + 1 := by omega
    have h3 : n + 1 - (ν + 1) + e = n - ν + e := by omega
    rw [h3]
    rw [h2, Nat.choose_succ_succ'] at h1
    omega


/-- The multiplicity of `R/(f)` for a regular local ring `R` and a non-zero `f` in its maximal
ideal is `ν(f)`: the Hilbert–Samuel function of `R/(f)` is explicit
(`sum_finrank_grPiece_quotient_span_singleton`), hence eventually the polynomial
`Σ_{j<ν} C(T - j + e, e)` of degree `e = dim R/(f)` and leading coefficient `ν/e!`. -/
theorem samuelMultiplicity_quotient_span_singleton_aux (R : Type u) [CommRing R]
    [IsRegularLocalRing R] (f : R) (hf : f ≠ 0) (hfm : f ∈ maximalIdeal R)
    [IsLocalRing (R ⧸ Ideal.span {f})] :
    ∃ ν : ℕ, Ideal.ordElem (maximalIdeal R) f = ν ∧
      samuelMultiplicity (R ⧸ Ideal.span {f}) = ν := by
  classical
  have hM : maximalIdeal R ≠ ⊥ := fun h => hf (by simpa [h] using hfm)
  obtain ⟨e, hdim, hgr⟩ := exists_finrank_grPiece_maximalIdeal_eq_choose R hM
  obtain ⟨ν, hν⟩ : ∃ ν : ℕ, Ideal.ordElem (maximalIdeal R) f = ν := by
    obtain ⟨ν, hν⟩ := ENat.ne_top_iff_exists.mp
      (fun h => hf ((Ideal.ordElem_eq_top_iff_eq_zero
        (IsLocalRing.maximalIdeal.isMaximal R).ne_top).mp h))
    exact ⟨ν, hν.symm⟩
  refine ⟨ν, hν, ?_⟩
  have hH : ∀ n, hilbertSamuel (R ⧸ Ideal.span {f}) n =
      (n + 1 + e).choose (e + 1) - (n + 1 - ν + e).choose (e + 1) := fun n =>
    sum_finrank_grPiece_quotient_span_singleton f hν hgr n
  have hdimA : dimNat (R ⧸ Ideal.span {f}) = e := by
    unfold dimNat
    rw [ringKrullDim_quotient_span_singleton_eq hf hfm hdim]
    rfl
  let p : ℚ[X] := ∑ j ∈ Finset.range ν, binomPoly e (-(j : ℚ))
  have hp : ∀ᶠ n : ℕ in atTop,
      p.eval (n : ℚ) = (hilbertSamuel (R ⧸ Ideal.span {f}) n : ℚ) := by
    filter_upwards [eventually_ge_atTop ν] with n hn
    have h1 := sum_choose_add_eq e n ν (by omega)
    rw [hH n]
    have h2 : (n + 1 + e).choose (e + 1) - (n + 1 - ν + e).choose (e + 1) =
        ∑ j ∈ Finset.range ν, (n - j + e).choose e := by omega
    rw [h2, eval_finsetSum]
    push_cast
    refine Finset.sum_congr rfl fun j hj => ?_
    have hj' : j ≤ n := by
      have := Finset.mem_range.mp hj
      omega
    exact eval_binomPoly e (n - j) n (-(j : ℚ)) (by rw [Nat.cast_sub hj']; ring)
  have hcoeff : p.coeff e = ν / (e.factorial : ℚ) := by
    simp only [p, finsetSum_coeff, coeff_binomPoly, Finset.sum_const, Finset.card_range,
      nsmul_eq_mul]
    ring
  have hpoly : hilbertSamuelPoly (R ⧸ Ideal.span {f}) = p := by
    have hex : ∃ q : ℚ[X], ∀ᶠ n : ℕ in atTop,
        q.eval (n : ℚ) = (hilbertSamuel (R ⧸ Ideal.span {f}) n : ℚ) := ⟨p, hp⟩
    rw [hilbertSamuelPoly, dite_eq_left hex]
    exact hilbertSamuelPoly_unique _ (Classical.choose_spec hex) hp
  unfold samuelMultiplicity
  rw [hdimA, hpoly, hcoeff]
  have h3 : (e.factorial : ℚ) * (ν / (e.factorial : ℚ)) = ν := by
    have : (e.factorial : ℚ) ≠ 0 := by positivity
    field_simp
  rw [h3, Nat.floor_natCast]

/-- p. 133: "If R is a regular local ring and J is a non-zero principal ideal in R, then we can
prove that e(R/J) = ν(J)."  Stated for proper `J = (f)`, `f ≠ 0`, so that `R/J` is local.

The paper gives no proof and no reference ("we can prove").  Proved here: the Hilbert–Samuel
function of `R/(f)` is computed from that of `R`.  Since `gr_M(R)` is a polynomial ring in
`d = dim R` variables, `dim_k Mⁱ/Mⁱ⁺¹ = C(i + d - 1, d - 1)`, so `length(R/Mᵐ) = C(m + d - 1, d)`;
since `gr_M(R)` is a domain, `(Mᵐ : f) = Mᵐ⁻ᵛ` for `ν = ν(f)`, so
`length(R/(Mᵐ + (f))) = length(R/Mᵐ) - length(R/Mᵐ⁻ᵛ)` (the exact sequence
`0 → R/(Mᵐ : f) → R/Mᵐ → R/(Mᵐ + (f)) → 0`), whence
`H_{R/(f)}(n) = C(n + d, d) - C(n + d - ν, d)` for `n ≥ ν`.  This is the polynomial
`Σ_{j<ν} C(T - j + d - 1, d - 1)` of degree `d - 1 = dim R/(f)` (`dim R/(f) = dim R - 1`,
`f` being a non-zero-divisor in the maximal ideal) and leading coefficient `ν/(d-1)!`, so
`e(R/(f)) = ν`.  Only uniqueness of the Hilbert–Samuel polynomial is used, not Samuel's theorem
`exists_hilbertSamuelPoly`.

Deviation from the paper (statement modified): the hypothesis `f ∈ m` (`J` proper), implicit in
the paper, is explicit.  Deviation from the paper (gap filled): the paper says "we can prove"
without proof; proved here as above (`Hironaka/Compat/HypersurfaceMultiplicity.lean` and
`samuelMultiplicity_quotient_span_singleton_aux`). -/
@[blueprint "lem:0.4-multiplicity-hypersurface"
  (statement := /-- If $R$ is a regular local ring and $J=(f)$ is a non-zero proper principal
    ideal in $R$, then $e(R/J)=\nu(J)$. (p.~133.)
    \textbf{Deviation from the paper (statement modified).} ``Proper'' ($f$ in the maximal
    ideal), implicit in the paper, is made explicit, so that $R/J$ is a local ring. -/)
  (proof := /-- The paper says ``we can prove'' and gives no proof. Let $d=\dim R$, $M$ the
    maximal ideal, $\nu=\nu(f)$. Since $\operatorname{gr}_M(R)$ is a polynomial ring in $d$
    variables, $\dim_k M^i/M^{i+1}=\binom{i+d-1}{d-1}$ and $\ell(R/M^m)=\binom{m+d-1}{d}$.
    Since $\operatorname{gr}_M(R)$ is a domain, $\nu(gf)=\nu(g)+\nu$ and so $(M^m:f)=M^{m-\nu}$;
    the exact sequence $0\to R/(M^m:f)\xrightarrow{f}R/M^m\to R/(M^m+(f))\to0$ gives
    $\ell(R/(M^m+(f)))=\ell(R/M^m)-\ell(R/M^{m-\nu})$, hence the Hilbert--Samuel function of
    $R/(f)$ is $H(n)=\binom{n+d}{d}-\binom{n+d-\nu}{d}=\sum_{j<\nu}\binom{n-j+d-1}{d-1}$ for
    $n\ge\nu$. This is a polynomial of degree $d-1$ with leading coefficient $\nu/(d-1)!$, and
    $\dim R/(f)=d-1$ because $f$ is a non-zero-divisor in the maximal ideal. By uniqueness of
    the Hilbert--Samuel polynomial, $e(R/(f))=\nu$.

    \textbf{Deviation from the paper (gap filled).} The paper asserts this (``we can prove'')
    without proof or reference; it is proved here as above, using only the uniqueness of the
    Hilbert--Samuel polynomial and not \cref{thm:hilbert-samuel}. -/)
  (latexEnv := "lemma")]
theorem samuelMultiplicity_quotient_span_singleton (R : Type u) [CommRing R]
    [IsRegularLocalRing R] (f : R) (hf : f ≠ 0) (hfm : f ∈ maximalIdeal R) :
    haveI : Nontrivial (R ⧸ Ideal.span {f}) := Ideal.Quotient.nontrivial_iff.mpr
      (fun h => (IsLocalRing.mem_maximalIdeal f).mp hfm (Ideal.span_singleton_eq_top.mp h))
    haveI : IsLocalRing (R ⧸ Ideal.span {f}) :=
      IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective
    (samuelMultiplicity (R ⧸ Ideal.span {f}) : ℕ∞) = Ideal.nu (Ideal.span {f}) := by
  have : Nontrivial (R ⧸ Ideal.span {f}) := Ideal.Quotient.nontrivial_iff.mpr
    (fun h => (IsLocalRing.mem_maximalIdeal f).mp hfm (Ideal.span_singleton_eq_top.mp h))
  have : IsLocalRing (R ⧸ Ideal.span {f}) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective
  obtain ⟨ν, hν, hmult⟩ := samuelMultiplicity_quotient_span_singleton_aux R f hf hfm
  have hnu : Ideal.nu (Ideal.span {f}) = ν := by
    rw [← hν]
    unfold Ideal.nu Ideal.ord Ideal.ordElem
    simp only [Ideal.span_singleton_le_iff_mem]
  exact (congrArg (fun k : ℕ => (k : ℕ∞)) hmult).trans hnu.symm

end LocalRing

end Hironaka

namespace AlgebraicGeometry.Scheme

variable (X : Scheme.{u})

/-- p. 133: "If `O_{X,x}` is noetherian, then `e(O_{X,x})` will be called the multiplicity of
`X` at the point `x`." -/
@[blueprint "def:0.4-multiplicity-at"
  (statement := /-- The \emph{multiplicity of $X$ at a point $x$} is $e(\mathcal O_{X,x})$
    (\cref{def:multiplicity}), for $\mathcal O_{X,x}$ noetherian. (p.~133.) -/)
  (latexEnv := "definition")]
noncomputable def multAt (x : X) : ℕ := Hironaka.samuelMultiplicity (X.presheaf.stalk x)

end AlgebraicGeometry.Scheme

namespace Hironaka

namespace Subscheme

variable {X : Scheme.{u}}

/-- p. 133: "We say that X is equi-multiple along Y if X has the same multiplicity at the
points of Y." -/
@[blueprint "def:equimultiple-along"
  (statement := /-- Let $Y\subseteq X$ be a subscheme (with $\mathcal O_{X,x}$ noetherian
    for $x\in Y$). $X$ is \emph{equi-multiple along $Y$} if $X$ has the same multiplicity at
    the points of $Y$, i.e.\ $e_x(X)=e_y(X)$ for all $x,y\in Y$. (Ch.~0 \S4, p.~133.)
    Formalization note (encoding): $Y$ is a subscheme (the paper allows a local-ringed
    subspace), and the noetherian requirement is not built into the predicate. -/)
  (latexEnv := "definition")]
def IsEquimultipleAlong (D : Subscheme X) : Prop :=
  ∀ x ∈ D.pts, ∀ y ∈ D.pts, X.multAt x = X.multAt y

end Subscheme

end Hironaka
