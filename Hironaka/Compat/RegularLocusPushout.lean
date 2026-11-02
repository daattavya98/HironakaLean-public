/-
Copyright (c) 2026 Daattavya Aggarwal, Minhyong Kim, Oisin Kim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daattavya Aggarwal, Minhyong Kim, Oisin Kim
-/
module

public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Architect
public import Hironaka.Compat.HironakaBaseStability

/-!
# Compatibility layer: the regular locus along a localization

The regular locus along a localization, used in the reduction of property (c) of the class 𝔅 to
the complete case (p. 161, footnote 31: "Reduce the proof to the case in which S is complete"):

* `mem_regularLocus_iff_comap_of_isLocalization`: if `E` is a localization of `D`, a prime `Q` of
  `E` is regular iff its contraction to `D` is (the local rings agree).
-/

@[expose] public section

open IsLocalRing
open scoped TensorProduct

noncomputable section

namespace Hironaka

universe u

section Localization

variable {D E : Type u} [CommRing D] [CommRing E] [Algebra D E]

/-- If `E` is a localization of `D`, a prime of `E` is regular iff its contraction to `D` is: the
local rings are isomorphic.

Deviation from the paper (gap filled): used in the reduction of (c), p. 161 (footnote 31: "Reduce
the proof to the case in which S is complete"); the paper does not state it. -/
@[blueprint "lem:regular-locus-localization"
  (statement := /-- Let $E$ be a localization of a ring $D$ and $Q$ a prime of $E$. Then $E_Q$ is
    regular if and only if $D_{Q\cap D}$ is regular. -/)
  (proof := /-- The local ring $E_Q$ is the localization of $D$ at the prime $Q\cap D$ (a
    localization of a localization at a prime), so the two local rings are isomorphic.
    \textbf{Deviation from the paper (gap filled).} Used in the reduction of (c), footnote~31. -/)
  (latexEnv := "lemma")]
theorem mem_regularLocus_iff_comap_of_isLocalization (N : Submonoid D) [IsLocalization N E]
    (Q : PrimeSpectrum E) :
    Q ∈ regularLocus E ↔ PrimeSpectrum.comap (algebraMap D E) Q ∈ regularLocus D := by
  set p : Ideal D := Q.asIdeal.comap (algebraMap D E) with hp
  have hpp : p.IsPrime := Ideal.comap_isPrime _ _
  have hloc : IsLocalization.AtPrime (Localization.AtPrime Q.asIdeal) p :=
    IsLocalization.isLocalization_isLocalization_atPrime_isLocalization N
      (Localization.AtPrime Q.asIdeal) Q.asIdeal
  let e : Localization.AtPrime p ≃+* Localization.AtPrime Q.asIdeal :=
    (IsLocalization.algEquiv p.primeCompl (Localization.AtPrime p)
      (Localization.AtPrime Q.asIdeal)).toRingEquiv
  constructor
  · intro h
    have h' : IsRegularLocalRing (Localization.AtPrime Q.asIdeal) := h
    exact IsRegularLocalRing.of_ringEquiv e.symm
  · intro h
    have h' : IsRegularLocalRing (Localization.AtPrime p) := h
    exact IsRegularLocalRing.of_ringEquiv e

end Localization


end Hironaka
