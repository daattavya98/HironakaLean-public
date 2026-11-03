/-
Copyright (c) 2026 Daattavya Aggarwal, Minhyong Kim, Oisin Kim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daattavya Aggarwal, Minhyong Kim, Oisin Kim
-/
module

public import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
public import Mathlib.RingTheory.MvPowerSeries.Basic
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Architect
public import Hironaka.Compat.ClassBCompleteCore
public import Hironaka.Compat.ClassBCompleteKernel
public import Hironaka.Compat.RegularLocusFlatDescent
public import Hironaka.Compat.QuotientCompletion
public import Hironaka.Compat.PowerSeriesPresentation
public import Hironaka.Compat.JacobianCriterion

/-!
# Compatibility layer: the complete case of property (c) of the class 𝔅 (p. 161)

Footnote 31 (p. 161): "Reduce the proof to the case in which S is complete, and then apply the
jacobian criterion."  For `S` complete, `S = k⟦t⟧/J` (footnote 30, Cohen), `A` is a quotient of
`T = k⟦t⟧[x]` and `R = A_p` is a quotient of the regular local ring `Λ = T_P`.  This file proves
condition (ii) for such an `R`:

* `hasCompletionRegularLocus_of_surjective_localization`: for `T = k⟦t⟧[x]` (`k` of characteristic
  zero), a prime `P` of `T` and a surjection `φ : T_P → R` onto a noetherian local ring,
  condition (ii) holds for `R`.  The direction "`q` regular implies `comap q` regular" is descent
  along the flat map `B → B ⊗_R R̂` (`comap_mem_regularLocus_of_mem_regularLocus_of_flat`); the
  converse is `isRegularLocalRing_localization_quotient_completion_of_quotient`, the jacobian
  criterion in the completion, after identifying the local rings of `B` and of `B ⊗_R R̂` with
  `T₁_{Q₁}/K₁` and `Λ̂[y]_𝔔/K₁` (`exists_localRingEquivs`).
* `hasCompletionRegularLocus_localization_atPrime_of_complete`: the statement of
  `ClassBLocalization.lean`, from Cohen (footnote 30) and the presentation `A = T/K`.
-/

@[expose] public section

open IsLocalRing
open scoped TensorProduct

noncomputable section

namespace Hironaka

universe u

section General

open PowerSeriesPolynomialRing

variable {k : Type u} [Field k] [CharZero k] {n m : ℕ}
  (P : Ideal (PowerSeriesPolynomialRing k n m)) [P.IsPrime]
  (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
  (φ : Localization.AtPrime P →+* R)

/-- Transport of a `Localization.AtPrime`-quotient identification along an equality of primes. -/
theorem nonempty_ringEquiv_localization_quotient_of_eq {A X : Type u} [CommRing A] [CommRing X]
    {I J : Ideal A} [I.IsPrime] [J.IsPrime] (h : I = J) (K : Ideal A)
    (e : X ≃+* (Localization.AtPrime I ⧸ K.map (algebraMap A (Localization.AtPrime I)))) :
    Nonempty (X ≃+* (Localization.AtPrime J ⧸ K.map (algebraMap A (Localization.AtPrime J)))) := by
  subst h
  exact ⟨e⟩

omit [CharZero k] [IsNoetherianRing R] in
/-- **Identification of the local rings.**  For a finite type `R`-algebra `B` and a prime `q` of
`B ⊗_R R̂`, there are `l`, an ideal `K₁` of `T₁ = k⟦t⟧[x, y₁..y_l]` and a prime `𝔔` of
`Λ̂[y]` such that the local ring of `B` at `q ∩ B` is `T₁_{Q₁}/K₁` (`Q₁ = ρ⁻¹ 𝔔`) and the local
ring of `B ⊗_R R̂` at `q` is `Λ̂[y]_𝔔/K₁Λ̂[y]_𝔔`.  (`B` is a quotient `T₁/K₁` after inverting
elements of `T ∖ P`, `exists_unit_denominators_presentationHom`; `B ⊗_R R̂ ≅ Λ̂[y]/K₁Λ̂[y]`,
`ker_completionTensorHom`, since `R̂ ≅ Λ̂/(ker φ)Λ̂`, `exists_ringEquiv_adicCompletion_quotient`.)

Deviation from the paper (gap filled): footnote 31 (p. 161) only says "apply the jacobian
criterion" in the complete case; the identification of the local rings of `B` and `B ⊗_R R̂` with
the local rings of `T₁/K₁` and `Λ̂[y]/K₁Λ̂[y]` is the omitted bookkeeping. -/
@[blueprint "lem:class-A-c-local-ring-equivs"
  (statement := /-- With the notation of \cref{lem:class-A-c-core}, let $R$ be a quotient of
    $T_{\mathfrak P}$, $B$ a finite type $R$-algebra and $q$ a prime of $B\otimes_R\hat R$. Then
    there are $l$, an ideal $K_1\subseteq T_1$ and a prime $\mathfrak Q$ of $\hat\Lambda[y]$ such
    that $B_{q\cap B}\cong(T_1)_{Q_1}/K_1(T_1)_{Q_1}$ and $(B\otimes_R\hat R)_q\cong
    \hat\Lambda[y]_{\mathfrak Q}/K_1\hat\Lambda[y]_{\mathfrak Q}$, where $Q_1=\rho^{-1}\mathfrak
    Q$. -/)
  (proof := /-- Present $B$ as $R[y_1,\dots,y_l]/I$, let $K_1$ be the kernel of $T_1\to B$ and
    $\mathfrak Q$ the preimage of $q$ in $\hat\Lambda[y]$. By
    \cref{lem:localization-quotient-unit-denominators} applied to $T_1\to B$ (every element
    of $B$ has a denominator from $T\setminus P$ which is a unit in $B$) we get the first
    isomorphism (the preimage of $q\cap B$ in $T_1$ is $Q_1$); applied to the surjection
    $\hat\Lambda[y]\to B\otimes_R\hat R$ with kernel $K_1\hat\Lambda[y]$
    (\cref{lem:ker-completion-tensor-hom}) we get the second.
    \textbf{Deviation from the paper (gap filled).} Footnote~31 does not say this. -/)
  (proofUses := ["lem:localization-quotient-unit-denominators",
    "lem:ker-completion-tensor-hom"])
  (latexEnv := "lemma")]
theorem exists_localRingEquivs (hφ : Function.Surjective φ) (B : Type u) [CommRing B]
    [Algebra R B] [Algebra.FiniteType R B]
    (q : PrimeSpectrum (B ⊗[R] AdicCompletion (maximalIdeal R) R)) :
    ∃ (l : ℕ) (K₁ : Ideal (PowerSeriesPolynomialRing k n (m + l)))
      (𝔔 : Ideal (MvPolynomial (Fin l) (completionAtPrime P))) (_ : 𝔔.IsPrime),
      Nonempty (Localization.AtPrime
          (PrimeSpectrum.comap (algebraMap B (B ⊗[R] AdicCompletion (maximalIdeal R) R))
            q).asIdeal ≃+*
        (Localization.AtPrime (𝔔.comap (completionExtensionHom P l)) ⧸
          K₁.map (algebraMap (PowerSeriesPolynomialRing k n (m + l))
            (Localization.AtPrime (𝔔.comap (completionExtensionHom P l)))))) ∧
      Nonempty (Localization.AtPrime q.asIdeal ≃+*
        (Localization.AtPrime 𝔔 ⧸
          K₁.map ((algebraMap (MvPolynomial (Fin l) (completionAtPrime P))
            (Localization.AtPrime 𝔔)).comp (completionExtensionHom P l)))) := by
  obtain ⟨l, ψ, hψ⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.mp
    (inferInstance : Algebra.FiniteType R B)
  refine ⟨l, presentationKernel P φ ψ, q.asIdeal.comap (completionTensorHom P φ hφ ψ),
    inferInstance, ?_, ?_⟩
  · have hI : (q.asIdeal.comap (algebraMap B (B ⊗[R] AdicCompletion (maximalIdeal R) R))).comap
        (presentationHom P φ ψ) =
        (q.asIdeal.comap (completionTensorHom P φ hφ ψ)).comap (completionExtensionHom P l) := by
      rw [Ideal.comap_comap, Ideal.comap_comap]
      congr 1
      ext x
      exact (completionTensorHom_completionExtensionHom P φ hφ ψ x).symm
    obtain ⟨e, -⟩ := exists_ringEquiv_localization_quotient_of_unit_denominators
      (presentationHom P φ ψ) (exists_unit_denominators_presentationHom P φ hφ ψ hψ)
      (q.asIdeal.comap (algebraMap B (B ⊗[R] AdicCompletion (maximalIdeal R) R)))
    exact nonempty_ringEquiv_localization_quotient_of_eq hI _ e
  · obtain ⟨e, -⟩ := exists_ringEquiv_localization_quotient_of_unit_denominators
      (completionTensorHom P φ hφ ψ)
      (fun b => by
        obtain ⟨x, rfl⟩ := completionTensorHom_surjective P φ hφ ψ hψ b
        exact ⟨1, x, by simp, by simp⟩) q.asIdeal
    refine ⟨e.trans (Ideal.quotEquivOfEq ?_)⟩
    rw [ker_completionTensorHom P φ hφ ψ hψ, Ideal.map_map]

/-- **Condition (ii) for a quotient of `T_P`.**  Let `T = k⟦t⟧[x]` with `k` of characteristic zero,
`P` a prime of `T` and `φ : T_P → R` a surjection onto a noetherian local ring.  Then for every
finite type `R`-algebra `B`, the singular locus of `Spec (B ⊗_R R̂)` is the preimage of that of
`Spec B`.

Deviation from the paper (gap filled): footnote 31 (p. 161): "Reduce the proof to the case in which
S is complete, and then apply the jacobian criterion." -/
@[blueprint "lem:class-A-c-surjective-localization"
  (statement := /-- Let $k$ be a field of characteristic zero, $T=k[[t]][x]$, $\mathfrak P$ a prime
    of $T$ and $\varphi\colon T_{\mathfrak P}\to R$ a surjection onto a noetherian local ring $R$.
    Then $R$ satisfies condition (ii) of the class $\mathfrak B$. -/)
  (proof := /-- Let $B$ be a finite type $R$-algebra and $q$ a prime of $B\otimes_R\hat R$. If
    $q$ is regular, then so is $q\cap B$ by flat descent along $B\to B\otimes_R\hat R$
    (\cref{lem:regular-locus-flat-descent}). Conversely, if $q\cap B$ is regular, the local rings
    are identified with $(T_1)_{Q_1}/K_1$ and $\hat\Lambda[y]_{\mathfrak Q}/K_1$
    (\cref{lem:class-A-c-local-ring-equivs}), and \cref{lem:class-A-c-core} gives regularity of
    the latter. \textbf{Deviation from the paper (gap filled).} Footnote~31: ``apply the
    jacobian criterion''. -/)
  (proofUses := ["lem:regular-locus-flat-descent", "lem:class-A-c-local-ring-equivs",
    "lem:class-A-c-core"])
  (latexEnv := "lemma")]
theorem hasCompletionRegularLocus_of_surjective_localization [Hironaka.Cited.IsRegularLocalRingLocalizationIffRankJacobianEqHeight.{u}] [Hironaka.Cited.IsRegularLocalRingLocalizationOfIsRegularLocalRing.{u}] [Hironaka.Cited.IsRegularLocalRingOfFlatOfIsRegularLocalRing.{u}] (hφ : Function.Surjective φ) :
    HasCompletionRegularLocus R := by
  intro B _ _ _ q
  have hBnoeth : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing R B
  constructor
  · intro hq
    exact comap_mem_regularLocus_of_mem_regularLocus_of_flat B _ q hq
  · intro hq₀
    obtain ⟨l, K₁, 𝔔, h𝔔, ⟨e₁⟩, ⟨e₂⟩⟩ := exists_localRingEquivs P R φ hφ B q
    have h1 : IsRegularLocalRing (Localization.AtPrime
        (PrimeSpectrum.comap (algebraMap B (B ⊗[R] AdicCompletion (maximalIdeal R) R))
          q).asIdeal) := hq₀
    have h2 := IsRegularLocalRing.of_ringEquiv e₁ (R := Localization.AtPrime
        (PrimeSpectrum.comap (algebraMap B (B ⊗[R] AdicCompletion (maximalIdeal R) R))
          q).asIdeal)
    have h3 := isRegularLocalRing_localization_quotient_completion_of_quotient P l K₁ 𝔔 h2
    exact IsRegularLocalRing.of_ringEquiv e₂.symm
      (R := Localization.AtPrime 𝔔 ⧸
        K₁.map ((algebraMap (MvPolynomial (Fin l) (completionAtPrime P))
          (Localization.AtPrime 𝔔)).comp (completionExtensionHom P l)))

end General

/-- **The complete case of property (c)** (footnote 31): for `S` a noetherian local ring with
residue field of characteristic zero that is complete for its maximal ideal, `A` an `S`-algebra of
finite type and `p` a prime of `A`, the local ring `A_p` satisfies condition (ii) of the class 𝔅.
By Cohen (footnote 30) `S` is an image of `k⟦t⟧`; hence `A` is an image of `T = k⟦t⟧[x]`
(`exists_surjective_powerSeriesPolynomialRing`) and `A_p` an image of the regular local ring `T_P`
(`exists_ringEquiv_localization_quotient`); apply
`hasCompletionRegularLocus_of_surjective_localization`. -/
theorem hasCompletionRegularLocus_localization_atPrime_of_complete [Hironaka.Cited.ExistsSurjectiveMvPowerSeriesOfIsAdicComplete.{u}] [Hironaka.Cited.IsRegularLocalRingLocalizationIffRankJacobianEqHeight.{u}] [Hironaka.Cited.IsRegularLocalRingLocalizationOfIsRegularLocalRing.{u}] [Hironaka.Cited.IsRegularLocalRingOfFlatOfIsRegularLocalRing.{u}] (S : Type u) [CommRing S]
    [IsLocalRing S] [IsNoetherianRing S] [CharZero (ResidueField S)]
    [IsAdicComplete (maximalIdeal S) S] (A : Type u) [CommRing A] [Algebra S A]
    [Algebra.FiniteType S A] (p : PrimeSpectrum A) :
    HasCompletionRegularLocus (Localization.AtPrime p.asIdeal) := by
  obtain ⟨n, k, _, _, f, hf⟩ := exists_surjective_mvPowerSeries_of_isAdicComplete S
  obtain ⟨m, Φ, hΦ, -⟩ := exists_surjective_powerSeriesPolynomialRing (A := A) f hf
  obtain ⟨e, -⟩ := exists_ringEquiv_localization_quotient Φ hΦ p.asIdeal
  have hAn : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing S A
  have hRn : IsNoetherianRing (Localization.AtPrime p.asIdeal) :=
    IsLocalization.isNoetherianRing p.asIdeal.primeCompl _ inferInstance
  let φ : Localization.AtPrime (p.asIdeal.comap Φ) →+* Localization.AtPrime p.asIdeal :=
    e.symm.toRingHom.comp (Ideal.Quotient.mk _)
  have hφ : Function.Surjective φ :=
    e.symm.surjective.comp Ideal.Quotient.mk_surjective
  exact hasCompletionRegularLocus_of_surjective_localization (k := k) (n := n) (m := m)
    (p.asIdeal.comap Φ) (Localization.AtPrime p.asIdeal) φ hφ

end Hironaka
