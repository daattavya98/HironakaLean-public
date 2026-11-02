/-
Copyright (c) 2026 Daattavya Aggarwal, Minhyong Kim, Oisin Kim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daattavya Aggarwal, Minhyong Kim, Oisin Kim
-/
module

public import Mathlib.Algebra.CharP.Algebra
public import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
public import Mathlib.RingTheory.AdicCompletion.LocalRing
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.RingHom.FaithfullyFlat
public import Mathlib.RingTheory.SimpleRing.Principal
public import Architect
public import Hironaka.Compat.HironakaBaseStability
public import Hironaka.Compat.AdicCompletionRegular
public import Hironaka.Compat.FlatLocalRegularity
public import Hironaka.Compat.JacobianCriterion
public import Hironaka.Compat.RegularLocalization
public import Hironaka.Compat.ClassBCompleteCase
public import Hironaka.Compat.RegularLocusFlatDescent
public import Hironaka.Compat.RingPushoutSquares
public import Hironaka.Compat.ClassBReductionDescent
public import Hironaka.Compat.ClassBReductionFibre

/-!
# Compatibility layer: property (c) of the class 𝔅 (Ch. I, p. 161), without the class

> (c) if A is an algebra of finite type over S ∈ 𝔅, then every local ring of Spec(A) belongs to
> 𝔅.³¹        ³¹ Reduce the proof to the case in which S is complete, and then apply the jacobian
> criterion.

The proof lives here, stated without the class `IsHironakaBase` (which is defined in
`Hironaka/Ch0/AlgebraicScheme.lean`, importing this file) through `HasCompletionRegularLocus`
(condition (ii)) together with `IsNoetherianRing` and `CharZero (ResidueField _)` (condition (i)).
The plan is as follows:

* `isNoetherianRing_localization_atPrime_of_finiteType`,
  `charZero_residueField_localization_atPrime`: condition (i) for `A_p`;
* the complete case (`hasCompletionRegularLocus_localization_atPrime_of_isAdicComplete`):
  Cohen's theorem, the presentation `A_p = Λ/I₁Λ` with `Λ = T_P` regular, `T = k⟦t⟧[x]`, the
  completion of the quotient, and the jacobian criterion;
* the reduction to the complete case (`hasCompletionRegularLocus_localization_atPrime`), by
  condition (ii) of `S` and descent of regularity along flat local homomorphisms.
-/

@[expose] public section

open IsLocalRing
open scoped TensorProduct

noncomputable section

universe u

namespace Hironaka

/-! ### Condition (i) for the local rings of a finite-type algebra -/

/-- A local ring whose residue field has characteristic zero is a `ℚ`-algebra in the weak sense
that every nonzero natural number is a unit. -/
theorem isUnit_natCast_of_charZero_residueField (S : Type u) [CommRing S] [IsLocalRing S]
    [CharZero (ResidueField S)] {n : ℕ} (hn : n ≠ 0) : IsUnit (n : S) := by
  rw [← notMem_maximalIdeal, ← residue_eq_zero_iff]
  intro h
  have : ((n : ResidueField S)) = 0 := by simpa using h
  exact hn (by exact_mod_cast this)

/-- If every nonzero natural number is a unit in a local ring `R`, its residue field has
characteristic zero. -/
theorem charZero_residueField_of_isUnit_natCast (R : Type u) [CommRing R] [IsLocalRing R]
    (h : ∀ n : ℕ, n ≠ 0 → IsUnit (n : R)) : CharZero (ResidueField R) := by
  rw [CharZero.charZero_iff_forall_prime_ne_zero]
  intro p hp hzero
  have h1 : residue R (p : R) = 0 := by simpa using hzero
  rw [residue_eq_zero_iff] at h1
  exact (notMem_maximalIdeal.mpr (h p hp.ne_zero)) h1

/-- Condition (i) for the local rings of a finite-type algebra over a noetherian ring: `A_p` is
noetherian (Hilbert's basis theorem and localization). -/
theorem isNoetherianRing_localization_atPrime_of_finiteType (S : Type u) [CommRing S]
    [IsNoetherianRing S] (A : Type u) [CommRing A] [Algebra S A] [Algebra.FiniteType S A]
    (p : PrimeSpectrum A) : IsNoetherianRing (Localization.AtPrime p.asIdeal) := by
  have : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing S A
  exact IsLocalization.isNoetherianRing p.asIdeal.primeCompl _ inferInstance

/-- Condition (i) for the local rings of a finite-type algebra over a local ring `S` with residue
characteristic zero: every nonzero natural number is a unit in `S`, hence in `A_p`, so the residue
field of `A_p` has characteristic zero. -/
theorem charZero_residueField_localization_atPrime (S : Type u) [CommRing S] [IsLocalRing S]
    [CharZero (ResidueField S)] (A : Type u) [CommRing A] [Algebra S A] (p : PrimeSpectrum A) :
    CharZero (ResidueField (Localization.AtPrime p.asIdeal)) := by
  refine charZero_residueField_of_isUnit_natCast _ fun n hn => ?_
  have h := (isUnit_natCast_of_charZero_residueField S hn).map
    ((algebraMap A (Localization.AtPrime p.asIdeal)).comp (algebraMap S A))
  simpa using h

/-! ### The complete case and the reduction to it -/

/-- **The complete case of (c)** (footnote 31: "apply the jacobian criterion").  If `S` is a
noetherian local ring with residue field of characteristic zero that is complete for its maximal
ideal, `A` is an `S`-algebra of finite type and `p` a prime of `A`, then `A_p` satisfies
condition (ii) (it is in 𝔅, together with `isNoetherianRing_localization_atPrime_of_finiteType`
and `charZero_residueField_localization_atPrime`).

Plan: Cohen (`exists_surjective_mvPowerSeries_of_isAdicComplete`)
gives `S = k⟦t⟧/J`; `A_p = Λ/I₁Λ` with `Λ = T_P` regular, `T = k⟦t⟧[x]`; `R̂ = Λ̂/I₁Λ̂`; for a
finite-type `B = Λ[y]/I₃` over `R = A_p` the regularity of `(Λ̂[y]/I₃)_Q` follows from that of
`(Λ[y]/I₃)_{Q₀}` by the jacobian criterion applied twice with the same partial derivations
(necessity in `T[y]` at `Q₀ ∩ T[y]`, sufficiency in the completion after extending the partials)
and flatness of `Λ[y]_{Q₀} → Λ̂[y]_Q`; the converse is descent of regularity along a flat local
homomorphism.

Proved in `Hironaka/Compat/ClassBCompleteCase.lean` (the identification of the local rings of `B`
and `B ⊗_R R̂` is `exists_localRingEquivs`); the only unproved inputs are the cited leaves (Cohen,
the jacobian criterion, flat descent, footnote 3, the Serre localization leaf). -/
@[blueprint "lem:class-A-c-complete"
  (statement := /-- Let $S$ be a noetherian local ring with residue field of characteristic zero,
    complete for its maximal ideal, $A$ an $S$-algebra of finite type and $\mathfrak p$ a prime
    of $A$. Then $A_{\mathfrak p}$ satisfies condition (ii) of the class $\mathfrak B$. -/)
  (proof := /-- Footnote~31: ``Reduce the proof to the case in which S is complete, and then
    apply the jacobian criterion.'' By \cref{lem:cohen-power-series-image},
    $S=k[[t]]/J$; $A_{\mathfrak p}=\Lambda/I_1\Lambda$ with $\Lambda=T_P$ regular
    ($T=k[[t]][x]$); the completion of the quotient is $\hat\Lambda/I_1\hat\Lambda$. For $B$ of
    finite type over $A_{\mathfrak p}$, regularity of $B_{Q_0}$ gives, by the jacobian criterion
    (\cref{lem:jacobian-criterion}), generators $f_i$ of the ideal and partial derivations with
    invertible minor; the derivations extend to the completion, where the same minor shows the
    $f_i$ are part of a regular system of parameters, so the completed local ring is regular.
    The converse is descent of regularity along flat local homomorphisms
    (\cref{lem:regular-descent-flat-local}). \textbf{Deviation from the paper (gap filled).}
    The paper only sketches this (footnote~31). -/)
  (proofUses := ["lem:cohen-power-series-image", "lem:jacobian-criterion",
    "lem:regular-descent-flat-local", "lem:regular-localization-serre",
    "lem:class-A-c-surjective-localization"])
  (latexEnv := "lemma")]
theorem hasCompletionRegularLocus_localization_atPrime_of_isAdicComplete [Hironaka.Cited.ExistsSurjectiveMvPowerSeriesOfIsAdicComplete.{u}] [Hironaka.Cited.IsRegularLocalRingLocalizationIffRankJacobianEqHeight.{u}] [Hironaka.Cited.IsRegularLocalRingLocalizationOfIsRegularLocalRing.{u}] [Hironaka.Cited.IsRegularLocalRingOfFlatOfIsRegularLocalRing.{u}] (S : Type u)
    [CommRing S] [IsLocalRing S] [IsNoetherianRing S] [CharZero (ResidueField S)]
    [IsAdicComplete (maximalIdeal S) S] (A : Type u) [CommRing A] [Algebra S A]
    [Algebra.FiniteType S A] (p : PrimeSpectrum A) :
    HasCompletionRegularLocus (Localization.AtPrime p.asIdeal) :=
  hasCompletionRegularLocus_localization_atPrime_of_complete S A p

/-- **The reduction of (c) to the complete case** ("by virtue of (ii)").  Let `S` satisfy (i) and
(ii), `A` be an `S`-algebra of finite type and `p` a prime of `A`.  Then `A_p` satisfies (ii).

Proof: `Ŝ` is faithfully flat over `S`, hence so is `A → A' =
A ⊗_S Ŝ` and there is a prime `p'` of `A'` over `p`.  The map `R = A_p → R' = A'_{p'}` is flat and
local, and `R'` satisfies (ii) by the complete case (`Ŝ` is complete, `A'` is of finite type over
`Ŝ`).  For `C` of finite type over `R` and a prime `q` of `C ⊗_R R̂`, the implication "regular
implies regular below" is flat descent along `C → C ⊗_R R̂`
(`comap_mem_regularLocus_of_mem_regularLocus_of_flat`).  Conversely, if `q` lies over a regular
prime of `C`, then every prime of `R' ⊗_R C` over a regular prime of `C` is regular by (ii) for `S`
applied to a finite type `A`-algebra `C₀` with `C = C₀ ⊗_A R`
(`mem_regularLocus_tensor_of_hasCompletionRegularLocus`), so `q` is regular by
`mem_regularLocus_tensor_adicCompletion_of_fibre`, which uses (ii) for `R'` and the flat local
map `R̂ → R̂'` (footnote 3, p. 116).

Deviation from the paper (gap filled): footnote 31 only says "Reduce the proof to the case in which
S is complete". -/
@[blueprint "lem:class-A-c-reduction"
  (statement := /-- Let $S$ be a noetherian local ring with residue field of characteristic zero
    satisfying condition (ii) of the class $\mathfrak B$, $A$ an $S$-algebra of finite type and
    $\mathfrak p$ a prime of $A$. Then $A_{\mathfrak p}$ satisfies condition (ii). -/)
  (proof := /-- Footnote~31: ``Reduce the proof to the case in which S is complete.'' Let $\hat S$
    be the completion; $A'=A\otimes_S\hat S$ is faithfully flat over $A$, so it has a prime
    $\mathfrak p'$ over $\mathfrak p$. The map $R=A_{\mathfrak p}\to R'=A'_{\mathfrak p'}$ is flat
    and local, and $R'$ satisfies (ii) by \cref{lem:class-A-c-complete}. Let $C$ be of finite type
    over $R$ and $q$ a prime of $C\otimes_R\hat R$. If $q$ is regular, so is the prime below it in
    $C$, by descent of regularity along the flat map $C\to C\otimes_R\hat R$
    (\cref{lem:regular-locus-flat-descent}). Conversely suppose the prime below $q$ is regular.
    Then every prime of $R'\otimes_RC$ over a regular prime of $C$ is regular, by condition (ii)
    for $S$ (\cref{lem:class-A-c-fibre-regular}), and \cref{lem:class-A-c-descent-completion}
    (which uses (ii) for $R'$ and \cref{lem:completion-flat-local}) shows that $q$ is regular.
    \textbf{Deviation from the paper (gap filled).} The paper only says ``reduce'' (footnote~31). -/)
  (proofUses := ["lem:class-A-c-complete", "lem:regular-locus-flat-descent",
    "lem:class-A-c-fibre-regular", "lem:class-A-c-descent-completion",
    "lem:completion-flat-local"])
  (latexEnv := "lemma")]
theorem hasCompletionRegularLocus_localization_atPrime [Hironaka.Cited.ExistsFlatIsLocalHomAdicCompletionOfFlat.{u}] [Hironaka.Cited.ExistsSurjectiveMvPowerSeriesOfIsAdicComplete.{u}] [Hironaka.Cited.IsRegularLocalRingLocalizationIffRankJacobianEqHeight.{u}] [Hironaka.Cited.IsRegularLocalRingLocalizationOfIsRegularLocalRing.{u}] [Hironaka.Cited.IsRegularLocalRingOfFlatOfIsRegularLocalRing.{u}] (S : Type u) [CommRing S] [IsLocalRing S]
    [IsNoetherianRing S] [CharZero (ResidueField S)] (hS : HasCompletionRegularLocus S)
    (A : Type u) [CommRing A] [Algebra S A] [Algebra.FiniteType S A] (p : PrimeSpectrum A) :
    HasCompletionRegularLocus (Localization.AtPrime p.asIdeal) := by
  classical
  -- the base change `A' = A ⊗_S Ŝ` and a prime over `p`
  have hA' := IsRingPushout.tensorProduct S A (AdicCompletion (maximalIdeal S) S)
  have hSff : (algebraMap S (AdicCompletion (maximalIdeal S) S)).FaithfullyFlat :=
    RingHom.faithfullyFlat_algebraMap_iff.mpr (faithfullyFlat_adicCompletion_maximalIdeal S)
  have hαff := hA'.flip.faithfullyFlat hSff
  obtain ⟨p', hp'⟩ := (RingHom.FaithfullyFlat.iff_flat_and_comap_surjective.mp hαff).2 p
  have hpα : p.asIdeal = p'.asIdeal.comap Algebra.TensorProduct.includeLeftRingHom :=
    congrArg PrimeSpectrum.asIdeal hp'.symm
  let _ : Algebra (Localization.AtPrime p.asIdeal) (Localization.AtPrime p'.asIdeal) :=
    (Localization.localRingHom p.asIdeal p'.asIdeal Algebra.TensorProduct.includeLeftRingHom
      hpα).toAlgebra
  have hRR' : (algebraMap (Localization.AtPrime p.asIdeal) (Localization.AtPrime p'.asIdeal)).comp
      (algebraMap A (Localization.AtPrime p.asIdeal)) =
      (algebraMap (A ⊗[S] AdicCompletion (maximalIdeal S) S)
        (Localization.AtPrime p'.asIdeal)).comp Algebra.TensorProduct.includeLeftRingHom :=
    RingHom.ext fun a => Localization.localRingHom_to_map p.asIdeal p'.asIdeal
      Algebra.TensorProduct.includeLeftRingHom hpα a
  have hflat : (algebraMap (Localization.AtPrime p.asIdeal)
      (Localization.AtPrime p'.asIdeal)).Flat :=
    hαff.flat.localRingHom p'.asIdeal p.asIdeal hpα
  have : Module.Flat (Localization.AtPrime p.asIdeal) (Localization.AtPrime p'.asIdeal) :=
    RingHom.flat_algebraMap_iff.mp hflat
  have : IsLocalHom (algebraMap (Localization.AtPrime p.asIdeal)
      (Localization.AtPrime p'.asIdeal)) :=
    Localization.isLocalHom_localRingHom p.asIdeal p'.asIdeal
      Algebra.TensorProduct.includeLeftRingHom hpα
  have hAn : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing S A
  have hRn : IsNoetherianRing (Localization.AtPrime p.asIdeal) :=
    IsLocalization.isNoetherianRing p.asIdeal.primeCompl _ inferInstance
  have hβfin : (Algebra.TensorProduct.includeRight (R := S) (A := A)
      (B := AdicCompletion (maximalIdeal S) S)).toRingHom.FiniteType :=
    hA'.finiteType (RingHom.finiteType_algebraMap.mpr inferInstance)
  have hA'n : IsNoetherianRing (A ⊗[S] AdicCompletion (maximalIdeal S) S) := by
    algebraize [(Algebra.TensorProduct.includeRight (R := S) (A := A)
      (B := AdicCompletion (maximalIdeal S) S)).toRingHom]
    have := isNoetherianRing_adicCompletion_of_isNoetherianRing (maximalIdeal S)
    exact Algebra.FiniteType.isNoetherianRing (AdicCompletion (maximalIdeal S) S) _
  have hR'n : IsNoetherianRing (Localization.AtPrime p'.asIdeal) :=
    IsLocalization.isNoetherianRing p'.asIdeal.primeCompl _ inferInstance
  -- the complete case for `R' = A'_{p'}`
  have hR' : HasCompletionRegularLocus (Localization.AtPrime p'.asIdeal) := by
    have : IsNoetherianRing (AdicCompletion (maximalIdeal S) S) :=
      isNoetherianRing_adicCompletion_of_isNoetherianRing (maximalIdeal S)
    have : CharZero (ResidueField (AdicCompletion (maximalIdeal S) S)) :=
      charZero_of_injective_ringHom
        (f := ResidueField.map (algebraMap S (AdicCompletion (maximalIdeal S) S)))
        (RingHom.injective _)
    let _ : Algebra (AdicCompletion (maximalIdeal S) S)
        (A ⊗[S] AdicCompletion (maximalIdeal S) S) :=
      (Algebra.TensorProduct.includeRight (R := S) (A := A)
        (B := AdicCompletion (maximalIdeal S) S)).toRingHom.toAlgebra
    have : Algebra.FiniteType (AdicCompletion (maximalIdeal S) S)
        (A ⊗[S] AdicCompletion (maximalIdeal S) S) :=
      RingHom.finiteType_algebraMap.mp hβfin
    exact hasCompletionRegularLocus_localization_atPrime_of_complete
      (AdicCompletion (maximalIdeal S) S) (A ⊗[S] AdicCompletion (maximalIdeal S) S) p'
  intro C _ _ _ q
  have hCn : IsNoetherianRing C :=
    Algebra.FiniteType.isNoetherianRing (Localization.AtPrime p.asIdeal) C
  constructor
  · intro hq
    exact comap_mem_regularLocus_of_mem_regularLocus_of_flat C _ q hq
  · intro hq
    exact mem_regularLocus_tensor_adicCompletion_of_fibre hR'
      (fun Q hQ => mem_regularLocus_tensor_of_hasCompletionRegularLocus hS p.asIdeal.primeCompl
        Algebra.TensorProduct.includeLeftRingHom
        (Algebra.TensorProduct.includeRight (R := S) (A := A)
          (B := AdicCompletion (maximalIdeal S) S)).toRingHom hA' p'.asIdeal.primeCompl hRR' Q hQ)
      q hq

end Hironaka
