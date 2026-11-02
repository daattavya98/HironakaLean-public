/-
Copyright (c) 2026 Daattavya Aggarwal, Minhyong Kim, Oisin Kim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daattavya Aggarwal, Minhyong Kim, Oisin Kim
-/
module

public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Hironaka.Compat.WeierstrassFrameTransform
public import Hironaka.Compat.TauZCoreGraded

/-!
# Lemma 25, (ii) of (c) (p. 272): polynomial models of `gr` adapted to a Weierstrass datum

In the proof of (ii) of (c) of Lemma 25 the paper chooses "a regular system of parameters
`(y₁, …, y_b, y, x₁, …, x_a)` of `S₀`.  Then `(z₁, …, z_r, w, y₁, …, y_b, y, x₁, …, x_a)` is a
regular system of parameters of `R`, and `(z̄₁, …, z̄_r, w̄, ȳ₁, …, ȳ_b, y, x₁, …, x_a)` is a regular
system of parameters of `R₁`.  Then `gr_M(R) = k[Z₁, …, Z_r, W, Y₁, …, Y_b, Y, X₁, …, X_a]` [...]
and `gr_{M₁}(R₁) = k[Z̄₁, …, Z̄_r, W̄, Ȳ₁, …, Ȳ_b, Y, X₁, …, X_a]`" (p. 272).

`WeierstrassDatum.IsAdaptedModel` records such an identification `k[X₁, …, X_n] ≅ gr_M(A)` for a
Weierstrass datum `(S; z)`, `(S₀; w)` of a regular local ring `A`: a graded (semilinear) ring
isomorphism sending the variables `zI j` to the initial forms `Z_j` of `z_j`, the variable `wI` to
the initial form `W` of `w`, and every other variable to the initial form of an element `s i` of
`S₀`, these elements generating the maximal ideal of `S₀`.

This file also contains `WeierstrassDatum.transform`, the datum `(S₁; z̄)`, `(S₀₁; w̄)` of the
monoidal transform `R₁`.
-/

@[expose] public section

open IsLocalRing MvPolynomial

namespace Hironaka

universe u

section Step

attribute [local instance] RegularFrame.isDomain_S

/-- The `WeierstrassDatum` of the monoidal transform `R₁` obtained from frame transforms `FT` of
`(S; z)` and `FT0` of `(S₀; w)` (in `S₁`, the monoidal transform of `S` of `FT`). -/
noncomputable def WeierstrassDatum.transform {R : Type u} [CommRing R] [IsRegularLocalRing R]
    [IsDomain R] (D : WeierstrassDatum R) {P : Ideal R} [P.IsPrime] {T : MonoidalTransform R P}
    [IsRegularLocalRing T.ring] (FT : D.F.FrameTransform T) (FT0 : D.F0.FrameTransform FT.TS) :
    WeierstrassDatum T.ring :=
  haveI : IsRegularLocalRing FT.TS.ring := FT.isRegular
  { F := FT.toRegularFrame
    F0 := FT0.toRegularFrame
    rank_eq_one := D.rank_eq_one }

end Step

section AdaptedModel

attribute [local instance] Ideal.Quotient.field

variable {A : Type u} [CommRing A] [IsRegularLocalRing A]

/-- **A polynomial model of `gr_M(A)` adapted to a Weierstrass datum** (p. 272: "`gr_M(R) =
k[Z₁, …, Z_r, W, Y₁, …, Y_b, Y, X₁, …, X_a]` where `Z_j` (resp. `W`, resp. `Y_j`, resp. `Y`, resp.
`X_j`) denotes the initial form of `z_j` (resp. `w`, resp. `y_j`, resp. `y`, resp. `x_j`)"): the
semilinear graded isomorphism `M.Φ : K[X₁, …, X_n] ≅ gr_M(A)` sends `X_{zI j}` to `Z_j`, `X_{wI}`
to `W`, and every other variable `X_i` to the initial form of `s i ∈ S₀`; the elements `s i` of the
other indices generate the maximal ideal of `S₀` (they form the regular system of parameters
`(y₁, …, y_b, y, x₁, …, x_a)` of `S₀`). -/
structure WeierstrassDatum.IsAdaptedModel (D : WeierstrassDatum A) {K : Type u} [Field K]
    {n : ℕ} (M : SemiModel K (A ⧸ maximalIdeal A) (AssocGraded (maximalIdeal A)) n)
    (zI : Fin D.F.r → Fin n) (wI : Fin n) (s : Fin n → D.F0.S) : Prop where
  /-- `M.Φ` is graded. -/
  graded : ∀ (d : ℕ) (p : MvPolynomial (Fin n) K),
    p ∈ homogeneousSubmodule (Fin n) K d ↔ M.Φ p ∈ AssocGraded.homogeneous (maximalIdeal A) d
  zI_injective : Function.Injective zI
  wI_notMem : wI ∉ Set.range zI
  /-- `X_{zI j} ↦ Z_j`. -/
  Φ_X_zI : ∀ j, M.Φ (X (zI j)) = frameForm D.F.z j
  /-- `X_{wI} ↦ W`. -/
  Φ_X_wI : M.Φ (X wI) = initialForm (maximalIdeal A) D.wR
  /-- The other variables go to initial forms of elements of `S₀`. -/
  Φ_X_other : ∀ i, i ∉ Set.range zI → i ≠ wI →
    M.Φ (X i) = initialForm (maximalIdeal A) (algebraMap D.F.S A (algebraMap D.F0.S D.F.S (s i)))
  /-- These elements generate the maximal ideal of `S₀`. -/
  span_other : Ideal.span (s '' {i | i ∉ Set.range zI ∧ i ≠ wI}) = maximalIdeal D.F0.S

end AdaptedModel

end Hironaka
