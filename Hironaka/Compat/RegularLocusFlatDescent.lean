/-
Copyright (c) 2026 Daattavya Aggarwal, Minhyong Kim, Oisin Kim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daattavya Aggarwal, Minhyong Kim, Oisin Kim
-/
module

public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Architect
public import Hironaka.Compat.HironakaBaseStability
public import Hironaka.Compat.FlatLocalRegularity

/-!
# Compatibility layer: descent of the regular locus along flat ring homomorphisms

If `A → B` is a flat homomorphism with `A` noetherian, a prime `q` of `B` whose local ring `B_q`
is regular has regular contraction `A_{q∩A}` (descent of regularity along the flat local
homomorphism `A_{q∩A} → B_q`, `lem:regular-descent-flat-local`).  This is the direction
"`q ∈ Reg(A ⊗ Ŝ)` implies `comap q ∈ Reg(A)`" of condition (ii) of the class 𝔅 (p. 161) for a
flat base change `S → Ŝ`, used for property (c).
-/

@[expose] public section

open IsLocalRing

namespace Hironaka

universe u

/-- **Descent of the regular locus along a flat homomorphism.**  If `A → B` is flat, `A` is
noetherian and `q` is a regular point of `Spec B`, then its image in `Spec A` is regular. -/
@[blueprint "lem:regular-locus-flat-descent"
  (statement := /-- Let $A\to B$ be a flat homomorphism with $A$ noetherian and $q$ a prime of
    $B$ with $B_q$ regular. Then $A_{q\cap A}$ is regular. -/)
  (proof := /-- The induced map $A_{q\cap A}\to B_q$ is a flat local homomorphism (flatness of
    $B$ over $A$ passes to the localization), so $A_{q\cap A}$ is regular by descent of
    regularity along flat local homomorphisms (\cref{lem:regular-descent-flat-local}). This is
    the direction ``$q$ regular in $\operatorname{Spec}(A\otimes\hat S)$ implies $q\cap A$
    regular'' of condition (ii) in the proof of property (c) (footnote~31). -/)
  (proofUses := ["lem:regular-descent-flat-local"])
  (latexEnv := "lemma")]
theorem comap_mem_regularLocus_of_mem_regularLocus_of_flat [Hironaka.Cited.IsRegularLocalRingOfFlatOfIsRegularLocalRing.{u}] (A B : Type u) [CommRing A]
    [CommRing B] [Algebra A B] [IsNoetherianRing A] [Module.Flat A B] (q : PrimeSpectrum B)
    (hq : q ∈ regularLocus B) :
    PrimeSpectrum.comap (algebraMap A B) q ∈ regularLocus A := by
  let p := PrimeSpectrum.comap (algebraMap A B) q
  have hq' : IsRegularLocalRing (Localization.AtPrime q.asIdeal) := hq
  let f : Localization.AtPrime p.asIdeal →+* Localization.AtPrime q.asIdeal :=
    Localization.localRingHom p.asIdeal q.asIdeal (algebraMap A B) rfl
  let _ : Algebra (Localization.AtPrime p.asIdeal) (Localization.AtPrime q.asIdeal) := f.toAlgebra
  have : IsScalarTower A (Localization.AtPrime p.asIdeal) (Localization.AtPrime q.asIdeal) :=
    IsScalarTower.of_algebraMap_eq fun x => by
      rw [RingHom.algebraMap_toAlgebra]
      rw [IsScalarTower.algebraMap_apply A B (Localization.AtPrime q.asIdeal)]
      exact (Localization.localRingHom_to_map p.asIdeal q.asIdeal (algebraMap A B) rfl x).symm
  have : IsLocalHom
      (algebraMap (Localization.AtPrime p.asIdeal) (Localization.AtPrime q.asIdeal)) :=
    Localization.isLocalHom_localRingHom p.asIdeal q.asIdeal (algebraMap A B) rfl
  have : IsNoetherianRing (Localization.AtPrime p.asIdeal) :=
    IsLocalization.isNoetherianRing p.asIdeal.primeCompl _ inferInstance
  exact isRegularLocalRing_of_flat_of_isRegularLocalRing (R := Localization.AtPrime p.asIdeal)
    (R' := Localization.AtPrime q.asIdeal)

end Hironaka
