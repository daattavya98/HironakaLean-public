/-
Copyright (c) 2026 Daattavya Aggarwal, Minhyong Kim, Oisin Kim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daattavya Aggarwal, Minhyong Kim, Oisin Kim
-/
module

public import Mathlib.RingTheory.MvPowerSeries.Equiv
public import Mathlib.RingTheory.RegularLocalRing.Polynomial
public import Mathlib.RingTheory.SimpleRing.Principal
public import Architect
public import Hironaka.Compat.MvPowerSeriesRegular
public import Hironaka.Compat.PowerSeriesPolynomialRing
public import Hironaka.Compat.RegularLocalization

/-!
# Compatibility layer: `k⟦t₁,…,t_n⟧[x₁,…,x_m]` is a regular ring

Footnote 30 (p. 161) reduces property (c) of the class 𝔅 to `A` a homomorphic image of a polynomial
ring over a formal power series ring over a field.  The ring `T = k⟦t⟧[x]`
(`PowerSeriesPolynomialRing`) is regular, so every localization `T_P` at a prime is a regular
local ring:

* `isRegularRing_mvPowerSeries`: `k⟦t⟧` is a regular ring (it is a regular local ring,
  `isRegularLocalRing_mvPowerSeries`, whose localizations are regular by Serre's theorem, cited by
  footnote 9, p. 243: `lem:regular-localization-serre`);
* `PowerSeriesPolynomialRing.isRegularRing`: so is `k⟦t⟧[x]`
  (`MvPolynomial.isRegularRing_of_isRegularRing`).
-/

@[expose] public section

namespace Hironaka

universe u

/-- The formal power series ring `k⟦t₁,…,t_n⟧` over a field is a regular ring: all its
localizations at primes are regular local rings (Serre's localization theorem, footnote 9). -/
@[blueprint "lem:mv-power-series-regular-ring"
  (statement := /-- The ring $k[[t_1,\dots,t_n]]$ is a regular ring: its localizations at primes
    are regular local rings. -/)
  (proof := /-- It is a regular local ring (\cref{lem:mv-power-series-regular}) and a localization
    of a regular local ring at a prime is regular (\cref{lem:regular-localization-serre}).
    \textbf{Deviation from the paper (gap filled).} Used tacitly in footnote~30 (p.~161). -/)
  (proofUses := ["lem:mv-power-series-regular", "lem:regular-localization-serre"])
  (latexEnv := "lemma")]
theorem isRegularRing_mvPowerSeries [Hironaka.Cited.IsRegularLocalRingLocalizationOfIsRegularLocalRing.{u}] (k : Type u) [Field k] (n : ℕ) :
    IsRegularRing (MvPowerSeries (Fin n) k) := by
  have := isRegularLocalRing_mvPowerSeries k n
  exact { isRegularLocalRing_localization := fun P _ =>
    isRegularLocalRing_localization_of_isRegularLocalRing _ P }

/-- The ring `k⟦t₁,…,t_n⟧[x₁,…,x_m]` is a regular ring; hence its localizations at primes are
regular local rings. -/
instance PowerSeriesPolynomialRing.isRegularRing [Hironaka.Cited.IsRegularLocalRingLocalizationOfIsRegularLocalRing.{u}] (k : Type u) [Field k] (n m : ℕ) :
    IsRegularRing (PowerSeriesPolynomialRing k n m) := by
  have := isRegularRing_mvPowerSeries k n
  exact inferInstanceAs (IsRegularRing (MvPolynomial (Fin m) (MvPowerSeries (Fin n) k)))

/-- Every localization of `k⟦t⟧[x]` at a prime is a regular local ring. -/
theorem PowerSeriesPolynomialRing.isRegularLocalRing_localization [Hironaka.Cited.IsRegularLocalRingLocalizationOfIsRegularLocalRing.{u}] (k : Type u) [Field k]
    (n m : ℕ) (P : Ideal (PowerSeriesPolynomialRing k n m)) [P.IsPrime] :
    IsRegularLocalRing (Localization.AtPrime P) :=
  inferInstance

end Hironaka
