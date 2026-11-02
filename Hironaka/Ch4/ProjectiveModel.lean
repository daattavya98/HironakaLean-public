/-
Copyright (c) 2026 Daattavya Aggarwal, Minhyong Kim, Oisin Kim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daattavya Aggarwal, Minhyong Kim, Oisin Kim
-/
module

public import Mathlib.FieldTheory.IntermediateField.Adjoin.Defs
public import Architect
public import Hironaka.Compat.ResolutionBookkeeping
public import Hironaka.Ch4.MainTheoremIZero
public import Hironaka.Compat.ProjectiveVocabularyProper
public import Hironaka.Compat.ProjectiveModelChart
public import Hironaka.Compat.ProjectiveModelResolution
public import Hironaka.Statements

/-!
# The Corollary of Main Theorem I: a non-singular projective model (Ch. 0 §3, p. 132)

> We note that the following existence theorem is an immediate consequence of our main theorem I (or, even, of the same
> theorem in the weak form).  COROLLARY. If `L` is a finitely generated field over a field of characteristic zero, say
> `B`, then there exists an irreducible non-singular projective algebraic `B`-scheme whose function field is
> `B`-isomorphic to `L`.  An algebraic `B`-scheme is said to be projective if it is of the form `Proj(H)` with a quotient
> ring `H`, graded in a natural way, of a polynomial ring with coefficients in `B`.  If `B = C`, the assertion is
> equivalent to saying that there exists a complex projective manifold (i.e., a non-singular analytic subspace of a
> complex projective space) of which the field of meromorphic functions is `C`-isomorphic to the given `L`.  (p. 132)

The proof ("an immediate consequence") is not printed.  It is: take the projective model `X₀ = Proj H` of
`L = B(x₁, …, xₙ)` (`H = B[T₀, …, Tₙ] ⧸ 𝔞`, `𝔞` the kernel of `Tᵢ ↦ yᵢ t`; `Compat/ProjectiveModelChart.lean`), resolve
it by Main Theorem I in the strong form (`MainTheorem.Ch0.I_strong_of_isAlgebraicScheme`), and check that the centers,
which avoid the simple points, miss the generic point, so that the function field and integrality are preserved, and
that each monoidal transformation of a projective scheme is projective (`Compat/ProjectiveModelResolution.lean`,
`MonoidalTransformation.isProjectiveOver`).  The last sentence (`B = C`, analytic spaces) is not formalized.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

namespace Hironaka

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

namespace MainTheorem.Ch0

/-- **Corollary of Main Theorem I** (p. 132): a finitely generated field `L` over a field `B` of characteristic zero is
the function field (`B`-isomorphically) of an irreducible non-singular projective algebraic `B`-scheme.

Formalization notes (encoding): "algebraic `B`-scheme" (pp. 118–119) is a scheme `X` with a morphism
`p : X ⟶ Spec B` locally of finite type, quasi-compact and separated; "irreducible" is `IrreducibleSpace X`;
"non-singular" is `Scheme.IsNonsingular` (all local rings regular); "projective" is the p. 132 definition,
`IsProjectiveOver X p` (`X ≅ Proj H` over `Spec B`, `H` a graded quotient of a polynomial ring over `B`; the first
definition of pp. 126–127 is not formalized); "finitely generated field" is `IntermediateField.FG ⊤`; the function field
(p. 130) is a `B`-algebra through `functionFieldAlgebraMap p`.  The last sentence ("If `B = C`, … complex projective
manifold") is about analytic spaces and is asserted without proof; it is not formalized.

Deviation from the paper (gap filled): the paper calls the Corollary "an immediate consequence of our main theorem I"
and gives no argument.  Three steps are unproved and uncited there: a projective integral model of `L` exists
(`ProjectiveModel.exists_functionField_equiv`); a monoidal transformation of a projective scheme is projective
(`MonoidalTransformation.isProjectiveOver`); the function field is unchanged along the resolution, whose centers avoid
the simple points (`MonoidalSuccession.exists_functionField_equiv_of_isStrongResolution`). -/
@[blueprint "cor:0.projective-model"
  (statement := /-- If $L$ is a finitely generated field over a field of characteristic zero, say $B$, then there exists
    an irreducible non-singular projective algebraic $B$-scheme whose function field is $B$-isomorphic to $L$.
    (Corollary, p.~132; ``projective'' in the sense of p.~132, \cref{def:0-projective-scheme}.)
    Formalization note (encoding): an algebraic $B$-scheme is a scheme with a morphism to $\operatorname{Spec}B$ that is
    locally of finite type, quasi-compact and separated; the function field is a $B$-algebra through the structure
    morphism. The sentence ``If $B=C$, the assertion is equivalent to saying that there exists a complex projective
    manifold \dots'' (analytic spaces, asserted without proof) is not formalized. -/)
  (proof := /-- Write $L=B(x_1,\dots,x_n)$ and let $H=B[T_0,\dots,T_n]/\mathfrak a$, $\mathfrak a$ the kernel of
    $T_0\mapsto t$, $T_i\mapsto x_it$ into $L[t]$: $\mathfrak a$ is a homogeneous prime ideal, $X_0=\operatorname{Proj}H$ is
    an integral projective $B$-scheme, and its chart $D_+(T_0)=\operatorname{Spec}B[x_1,\dots,x_n]$ shows that its
    function field is $B$-isomorphic to $L$. By Main Theorem I in the strong form (\cref{thm:0.3-main-I-strong}) there is
    a succession of monoidal transformations $X_r\to\dots\to X_0$ with $X_r$ non-singular whose centers contain no simple
    point. The generic point of an integral scheme is simple, so it is never on a center; hence each $X_{i+1}$ is
    integral (the strict transform of $X_i$ is $X_{i+1}$), $X_{i+1}\to X_i$ is an isomorphism near the generic point
    (\cref{compat:blowup-local-iso-open}), so the function field does not change, and $X_{i+1}$ is projective
    (\cref{lem:0-blowup-projective}).
    \textbf{Gap in the paper filled.} The paper calls the Corollary ``an immediate consequence of our main theorem I''
    and proves none of the three steps (projective integral model, projectivity of monoidal transforms, birational
    invariance of the function field). -/)
  (proofUses := ["thm:0.3-main-I-strong", "lem:0-blowup-projective", "def:0-projective-scheme",
    "compat:blowup-local-iso-open"])
  (latexEnv := "corollary")]
theorem exists_projective_model [Hironaka.HironakaCitedResults.{u}] {B : Type u} [Field B] [CharZero B] (L : Type u) [Field L] [Algebra B L]
    (hL : (⊤ : IntermediateField B L).FG) :
    ∃ (X : Scheme.{u}) (p : X ⟶ Spec (CommRingCat.of B)) (_ : IrreducibleSpace X),
      LocallyOfFiniteType p ∧ QuasiCompact p ∧ IsSeparated p ∧ X.IsNonsingular ∧ IsProjectiveOver X p ∧
      ∃ e : X.functionField ≃+* L, ∀ b : B, e (functionFieldAlgebraMap p b) = algebraMap B L b := by
  obtain ⟨S, hS⟩ := hL
  let x : Fin S.card → L := fun i => (S.equivFin.symm i : L)
  have hx : IntermediateField.adjoin B (Set.range x) = ⊤ := by
    have hr : Set.range x = (S : Set L) := by
      ext z
      constructor
      · rintro ⟨i, rfl⟩
        exact (S.equivFin.symm i).2
      · intro hz
        exact ⟨S.equivFin ⟨z, hz⟩, by simp [x]⟩
    rw [hr, hS]
  let 𝔞 := ProjectiveModel.coneIdeal B x
  have : IsAlgebraicScheme (Proj (quotientGrading 𝔞)) := IsAlgebraicScheme.of_field (projStructure 𝔞)
  obtain ⟨Y, s, hs⟩ := I_strong_of_isAlgebraicScheme (Proj (quotientGrading 𝔞))
  have : IsIntegral Y := s.isIntegral_of_isStrongResolution hs
  have hproj := s.isProjectiveOver_of_isStrongResolution hs _ (IsProjectiveOver.projStructure 𝔞)
  obtain ⟨e₁, he₁⟩ := s.exists_functionField_equiv_of_isStrongResolution hs (projStructure 𝔞)
  obtain ⟨e₀, he₀⟩ := ProjectiveModel.exists_functionField_equiv x hx
  refine ⟨Y, s.composite ≫ projStructure 𝔞, inferInstance, hproj.locallyOfFiniteType, hproj.quasiCompact,
    hproj.isSeparated, s.isNonsingular_of_isStrongResolution hs, hproj, e₁.trans e₀, fun b => ?_⟩
  rw [RingEquiv.trans_apply, he₁, he₀]

end MainTheorem.Ch0

end Hironaka
