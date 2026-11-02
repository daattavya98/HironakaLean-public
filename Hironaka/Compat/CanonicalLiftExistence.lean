/-
Copyright (c) 2026 Daattavya Aggarwal, Minhyong Kim, Oisin Kim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daattavya Aggarwal, Minhyong Kim, Oisin Kim
-/
module

public import Architect
public import Hironaka.Ch3.Transforms

/-!
# Existence of the canonical monoidal transforms (Lemma 4, pp. 210-212), along the printed route

> It is easily seen that if `M̃'` is an associated prime ideal of `M'Ã'`, then we have a canonical
> local homomorphism of `R' = A'_{M'}` into `R̃' = Ã'_{M̃'}`, and that if either `k̃` or `R'/M'R'` is
> algebraic over `k`, then every monoidal transform `R̃'` of `R` with center `P̃`, which admits a
> canonical local homomorphism `R' → R̃'`, can be obtained in this manner.  (p. 211)

The existence of a canonical monoidal transform `R̃'` over a given `R'` is the existence of an
associated prime of `M'Ã'`, i.e. `M'Ã' ≠ Ã'`: through the chart `Ã' → k̃[X₂,…,X_r]` of p. 211 the
ideal `M'Ã'` maps onto `m̄'k̃[X₂,…,X_r]`, which is proper since `k̃[X]` is a free `k[X]`-module and
`m̄'` is a proper ideal of `k[X]`.  (`Hironaka.exists_isCanonicalLift` constructs the same object
for an arbitrary ideal `P` by faithful flatness of `R → R̃`; it is kept for the callers that have no
prime center with regular quotient.)
-/

@[expose] public section

open IsLocalRing TensorProduct

namespace Hironaka

universe u

section CanonicalLiftExistence

/-- `m k̃[X] ≠ k̃[X]` for a proper prime ideal `m` of `k[X]` and a field extension `κ : k → k̃`
(`k̃[X]` is a free `k[X]`-module; here through `k̃[X]/m k̃[X] ⊆ K ⊗_k k̃`, `K = Frac(k[X]/m)`, which is
non-trivial, `exists_ringHom_tensor_fractionRing`). -/
theorem map_mvPolynomial_ne_top {k k' : Type u} [Field k] [Field k'] (κ : k →+* k') {σ : Type}
    (m : Ideal (MvPolynomial σ k)) [m.IsPrime] :
    m.map (MvPolynomial.map κ) ≠ ⊤ := by
  let := κ.toAlgebra
  obtain ⟨Ψ, -, -, hker⟩ := exists_ringHom_tensor_fractionRing κ m
  intro h
  have h1 : (1 : MvPolynomial σ k') ∈ RingHom.ker Ψ := by
    rw [hker, h]
    exact Submodule.mem_top
  rw [RingHom.mem_ker, map_one] at h1
  have : Nontrivial (FractionRing (MvPolynomial σ k ⧸ m) ⊗[k] k') :=
    Algebra.TensorProduct.nontrivial_of_algebraMap_injective_of_flat_left k
      (FractionRing (MvPolynomial σ k ⧸ m)) k' κ.injective
  exact one_ne_zero h1

variable {R Rb : Type u} [CommRing R] [IsRegularLocalRing R] [IsDomain R]
  [CommRing Rb] [IsRegularLocalRing Rb] [IsDomain Rb] {P : Ideal R}

/-- p. 211: `M'Ã' ≠ Ã'`.  Under the chart `π̃ : Ã' → k̃[X₂,…,X_r]` the ideal `M'Ã'` maps onto
`m̄'k̃[X₂,…,X_r]` (`MonoidalTransform.map_map_blowupMap_eq`), a proper ideal
(`map_mvPolynomial_ne_top`), while the image of the unit ideal is the unit ideal. -/
theorem MonoidalTransform.map_blowupMap_ne_top (α : R →+* Rb) [IsLocalHom α]
    (hα : RingHom.MapsRSOP α) (hP : P.IsPrime) (hS : IsRegularLocalRing (R ⧸ P))
    (t : MonoidalTransform R P) :
    t.M'.map (blowupMap α (RingHom.MapsRSOP.injective α hα) P t.x) ≠ ⊤ := by
  obtain ⟨r, π, π', hπ, hkπ, -, -, hcomm, -, -⟩ := t.exists_residue_charts α hα hP hS
  have hm : (t.M'.map π).IsPrime := Ideal.map_isPrime_of_surjective hπ (hkπ.trans t.le)
  intro h
  have h1 := congrArg (Ideal.map π') h
  rw [t.map_map_blowupMap_eq α hα π π' hcomm, Ideal.map_top] at h1
  exact map_mvPolynomial_ne_top (ResidueField.map α) (t.M'.map π) h1

/-- p. 211: there is an associated prime ideal `M̃'` of `M'Ã'`, and it lies over `M'`
(`MonoidalTransform.mem_liftPrimes_of_mem_associatedPrimes`): `M'Ã'` is a proper ideal of the
noetherian ring `Ã'` (`MonoidalTransform.map_blowupMap_ne_top`), so `Ã'/M'Ã' ≠ 0` has an associated
prime. -/
theorem MonoidalTransform.exists_mem_liftPrimes (α : R →+* Rb) [IsLocalHom α]
    (hα : RingHom.MapsRSOP α) (hP : P.IsPrime) (hS : IsRegularLocalRing (R ⧸ P))
    (t : MonoidalTransform R P) :
    ∃ N, N ∈ LiftPrimes α (RingHom.MapsRSOP.injective α hα) t := by
  have := isNoetherianRing_blowupAlgebra (R := Rb) (P := P.map α) (α t.x)
  have : Nontrivial (blowupAlgebra Rb (P.map α) (α t.x) ⧸
      t.M'.map (blowupMap α (RingHom.MapsRSOP.injective α hα) P t.x)) :=
    Ideal.Quotient.nontrivial_iff.mpr (t.map_blowupMap_ne_top α hα hP hS)
  obtain ⟨N, hN⟩ := associatedPrimes.nonempty (blowupAlgebra Rb (P.map α) (α t.x))
    (blowupAlgebra Rb (P.map α) (α t.x) ⧸
      t.M'.map (blowupMap α (RingHom.MapsRSOP.injective α hα) P t.x))
  exact ⟨N, t.mem_liftPrimes_of_mem_associatedPrimes α hα hP hS N hN⟩

/-- **Existence of the canonical monoidal transform** (Lemma 4, pp. 210-212, the existence half, as
printed on p. 211): for `α : R → R̃` transforming a regular system of parameters into one, `P` a
prime ideal of `R` with `R/P` regular and `R'` a monoidal transform of `R` with center `P`, there
are a monoidal transform `R̃'` of `R̃` with center `PR̃` and a canonical local homomorphism
`R' → R̃'`.  The prime `M̃'` of `Ã'` is an associated prime of `M'Ã'`, which exists since
`M'Ã' ≠ Ã'` (`MonoidalTransform.exists_mem_liftPrimes`); then `R̃' = Ã'_{M̃'}`
(`MonoidalTransform.ofLift`).  Compare `Hironaka.exists_isCanonicalLift`, the same statement
without the hypotheses on `P`, proved by faithful flatness of `R → R̃`. -/
@[blueprint "lem:III.4-existence"
  (statement := /-- Let $\alpha\colon R\to\tilde R$ be as in \cref{lem:III.4}, $P$ a prime ideal of
    $R$ with $R/P$ regular and $R'$ a monoidal transform of $R$ with center $P$. Then there exist
    a monoidal transform $\tilde R'$ of $\tilde R$ with center $P\tilde R$ and a canonical local
    homomorphism $R'\to\tilde R'$ (\cref{def:III.2-canonical}). (Lemma 4, p.~211: ``if $\tilde M'$
    is an associated prime ideal of $M'\tilde A'$, then we have a canonical local homomorphism of
    $R'=A'_{M'}$ into $\tilde R'=\tilde A'_{\tilde M'}$''.) -/)
  (proof := /-- Through the chart $\tilde A'\to\tilde k[X_2,\dots,X_r]$ of p.~211 the ideal
    $M'\tilde A'$ maps onto $\bar m'\tilde k[X_2,\dots,X_r]$, which is a proper ideal because
    $\tilde k[X]$ is a free $k[X]$-module and $\bar m'$ is proper. Hence $M'\tilde A'\ne\tilde A'$,
    so $M'\tilde A'$ has an associated prime ideal $\tilde M'$ in the noetherian ring $\tilde A'$,
    which lies over $M'$ by the correspondence of the associated primes of $M'\tilde A'$ and of
    $\bar m'\tilde k[X_2,\dots,X_r]$ (\cref{lem:III.4-associated-primes}). Put
    $\tilde R'=\tilde A'_{\tilde M'}$.

    \textbf{Gap in the paper filled.} The paper does not say that the set of associated primes is
    non-empty. -/)
  (latexEnv := "lemma")]
theorem MonoidalTransform.exists_isCanonicalLift_of_isRegular (α : R →+* Rb) [IsLocalHom α]
    (hα : RingHom.MapsRSOP α) (hP : P.IsPrime) (hS : IsRegularLocalRing (R ⧸ P))
    (t : MonoidalTransform R P) :
    ∃ (T' : MonoidalTransform Rb (P.map α)) (β : t.ring →+* T'.ring), IsCanonicalLift α t T' β := by
  obtain ⟨N, hN⟩ := t.exists_mem_liftPrimes α hα hP hS
  exact ⟨_, _, MonoidalTransform.isCanonicalLift_ofLiftHom α hα t N hN⟩

end CanonicalLiftExistence

end Hironaka
