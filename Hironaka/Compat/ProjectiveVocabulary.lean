/-
Copyright (c) 2026 Daattavya Aggarwal, Minhyong Kim, Oisin Kim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daattavya Aggarwal, Minhyong Kim, Oisin Kim
-/
module

public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Ideal
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Architect
public import Hironaka.Statements

/-!
# Projective schemes over a field (Ch. 0 §3, p. 132)

> An algebraic `B`-scheme is said to be projective if it is of the form `Proj(H)` with a quotient ring `H`, graded in a
> natural way, of a polynomial ring with coefficients in `B`.  (p. 132)

This file is the vocabulary of the Corollary of Main Theorem I (`Hironaka/Ch4/ProjectiveModel.lean`):
* `quotientGrading 𝔞`: the natural grading of `B[T₀, …, T_{n-1}] ⧸ 𝔞` for a homogeneous ideal `𝔞`, with the instance
  `GradedAlgebra (quotientGrading 𝔞)` (Mathlib has no grading on a quotient);
* `projStructure 𝔞 : Proj H ⟶ Spec B`, the structure morphism `Proj H → Spec H₀ → Spec B`;
* `IsProjectiveOver X p`: "`X` is of the form `Proj(H)`" as a `B`-scheme;
* a projective `B`-scheme is of finite type, separated and proper over `B` (Mathlib's properness of `Proj`).

Formalization notes (encoding): "a quotient ring graded in a natural way of a polynomial ring" is a bundled
`HomogeneousIdeal` of `B[T₀, …, T_{n-1}]` with the induced grading; the isomorphism `X ≅ Proj H` is an isomorphism of
`B`-schemes for the structure morphism `Proj H → Spec H₀ → Spec B` (`B → H₀` is the algebra structure; it is
surjective).  The first definition of "projective" of pp. 126–127 (via blowing-up of modules) is not formalized: the
Corollary uses this one, and the paper does not show that the two agree.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory MvPolynomial DirectSum

namespace Hironaka

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

section QuotientGrading

variable {B : Type u} [Field B] {n : ℕ}


theorem mk_mem_quotientGrading (𝔞 : HomogeneousIdeal (homogeneousSubmodule (Fin n) B))
    {d : ℕ} {a : MvPolynomial (Fin n) B} (ha : a ∈ homogeneousSubmodule (Fin n) B d) :
    Ideal.Quotient.mk 𝔞.toIdeal a ∈ quotientGrading 𝔞 d :=
  ⟨a, ha, rfl⟩

theorem mem_quotientGrading_iff (𝔞 : HomogeneousIdeal (homogeneousSubmodule (Fin n) B))
    {d : ℕ} {x : MvPolynomial (Fin n) B ⧸ 𝔞.toIdeal} :
    x ∈ quotientGrading 𝔞 d ↔
      ∃ a ∈ homogeneousSubmodule (Fin n) B d, Ideal.Quotient.mk 𝔞.toIdeal a = x :=
  Iff.rfl











end QuotientGrading

section ProjStructure

variable {B : Type u} [Field B] {n : ℕ} (𝔞 : HomogeneousIdeal (homogeneousSubmodule (Fin n) B))


theorem isHomogeneous_zero_eq_C {p : MvPolynomial (Fin n) B} (hp : p.IsHomogeneous 0) :
    p = C (p.coeff 0) := by
  by_cases h0 : p = 0
  · subst h0; simp
  · exact totalDegree_eq_zero_iff_eq_C.mp (hp.totalDegree h0)

theorem algebraMap_quotientGrading_zero_surjective :
    Function.Surjective (algebraMap B (quotientGrading 𝔞 0)) := by
  rintro ⟨x, a, ha, rfl⟩
  refine ⟨a.coeff 0, Subtype.ext ?_⟩
  show algebraMap B (MvPolynomial (Fin n) B ⧸ 𝔞.toIdeal) (a.coeff 0) =
    Ideal.Quotient.mk 𝔞.toIdeal a
  conv_rhs => rw [isHomogeneous_zero_eq_C ha]
  rfl


end ProjStructure

end Hironaka
