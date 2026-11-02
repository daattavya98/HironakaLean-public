/-
Copyright (c) 2026 Daattavya Aggarwal, Minhyong Kim, Oisin Kim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daattavya Aggarwal, Minhyong Kim, Oisin Kim
-/
module

public import Mathlib.RingTheory.MvPowerSeries.Derivative
public import Mathlib.RingTheory.MvPowerSeries.Equiv
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Architect
public import Hironaka.Statements

/-!
# Compatibility layer: the ring `k⟦t₁,…,t_n⟧[x₁,…,x_m]` and its partial derivations

Footnote 30 (p. 161) reduces property (c) of the class 𝔅 to the case "in which A is a homomorphic
image of a polynomial ring over such a formal power series ring" (a formal power series ring over a
field of characteristic zero).  This file defines that ring, `PowerSeriesPolynomialRing k n m`
(`n` power series variables `t`, `m` polynomial variables `x`), its `n + m` partial derivations
(`PowerSeriesPolynomialRing.pderiv`: `∂/∂t_j` differentiates the coefficients, `∂/∂x_l` is the
formal derivative in the polynomial variable), the jacobian matrix of `r` elements and the
reduction modulo a prime, used to state Nagata's jacobian criterion
(`Hironaka/Compat/JacobianCriterion.lean`).

`mapCoeffsDerivation` (coefficientwise application of a derivation of `R` to `R[σ]`) is proved
here since Mathlib only has it for one variable (`Derivation.mapCoeffs`).
-/

@[expose] public section

open IsLocalRing

noncomputable section

namespace Hironaka

universe u

/-! ### Coefficientwise derivations of polynomial rings -/



section MapCoeffs

variable {k R σ : Type*} [CommRing k] [CommRing R] [Algebra k R]





end MapCoeffs





namespace PowerSeriesPolynomialRing

variable (k : Type u) [Field k] (n m : ℕ)



/-- `k⟦t⟧[x]` is noetherian (Hilbert's basis theorem for `k⟦t⟧`, a power series ring in finitely
many variables over a field, and for polynomials over it). -/
instance : IsNoetherianRing (PowerSeriesPolynomialRing k n m) :=
  inferInstanceAs (IsNoetherianRing (MvPolynomial (Fin m) (MvPowerSeries (Fin n) k)))




variable {k n m}

/-- The inclusion of the power series ring `k⟦t⟧` into `k⟦t⟧[x]`. -/
def C : MvPowerSeries (Fin n) k →+* PowerSeriesPolynomialRing k n m :=
  (MvPolynomial.C : MvPowerSeries (Fin n) k →+* MvPolynomial (Fin m) (MvPowerSeries (Fin n) k))

/-- The polynomial variable `x_l`. -/
def X (l : Fin m) : PowerSeriesPolynomialRing k n m :=
  (MvPolynomial.X l : MvPolynomial (Fin m) (MvPowerSeries (Fin n) k))

/-- Evaluation of `k⟦t⟧[x]` in a ring `A`: a ring homomorphism `g` on the power series and values
`a_l` of the polynomial variables. -/
def eval₂ {A : Type*} [CommRing A] (g : MvPowerSeries (Fin n) k →+* A) (a : Fin m → A) :
    PowerSeriesPolynomialRing k n m →+* A :=
  (MvPolynomial.eval₂Hom g a : MvPolynomial (Fin m) (MvPowerSeries (Fin n) k) →+* A)

@[simp]
theorem eval₂_C {A : Type*} [CommRing A] (g : MvPowerSeries (Fin n) k →+* A) (a : Fin m → A)
    (c : MvPowerSeries (Fin n) k) : eval₂ g a (C c) = g c :=
  MvPolynomial.eval₂_C g a c

@[simp]
theorem eval₂_X {A : Type*} [CommRing A] (g : MvPowerSeries (Fin n) k →+* A) (a : Fin m → A)
    (l : Fin m) : eval₂ g a (X l) = a l :=
  MvPolynomial.eval₂_X g a l



end PowerSeriesPolynomialRing


end Hironaka
