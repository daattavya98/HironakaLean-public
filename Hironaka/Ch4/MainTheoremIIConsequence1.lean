/-
Copyright (c) 2026 Daattavya Aggarwal, Minhyong Kim, Oisin Kim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daattavya Aggarwal, Minhyong Kim, Oisin Kim
-/
module

public import Architect
public import Hironaka.Ch0.QuestionE
public import Hironaka.Ch4.MainTheoremIZero
public import Hironaka.Compat.FunctionFieldPair
public import Hironaka.Compat.FunctionFieldPairProper
public import Hironaka.Statements

/-!
# Ch. 0 §5 (p. 144): consequence (1) of Corollary 1 of Main Theorem II

> (1) Let `(X₁, θ₁)` and `(X₂, θ₂)` belong to `𝔐(L/B)`.  Then we can obtain `(X'₁, θ'₁) ∈ 𝔐(L/B)` from `(X₁, θ₁)` by means
> of a finite succession of monoidal transformations with non-singular centers, such that `(X'₁, θ'₁)` domiates
> `(X₂, θ₂)`.  If `X₁` is non-singular, so is `X'₁`.  (See also main theorem I in the strong form.)  (p. 144)

> As consequences of Corollary 1, we can prove: …  (p. 144)

No argument is printed.  The route follows the two indications of the paper: "As consequences of Corollary 1" (Corollary 1
is what answers Question (E), p. 143: "In order to see that the main theorem II implies the affirmative answer to the
question (E) for the case in which `X` and `Y` are algebraic `B`-schemes with a field `B` of characteristic zero, the
following corollary of main theorem II is sufficient"), and "(See also main theorem I in the strong form)".
* Resolve `X₁` by the strong form of Main Theorem I (`MainTheorem.Ch0.I_strong_of_isAlgebraicScheme`): a succession with
  non-singular centers, nowhere dense because the generic point is simple, ending in a non-singular `X₁'`, with `(X₁', θ₁')`
  in `𝔐(L/B)` (`Compat/PairSuccession.lean`, `Compat/FunctionFieldPair.lean`).
* Apply Question (E) with `S₀ = X₁'` (`RationalApplication.question_E_integral`, `Ch0/QuestionE.lean`) to the rational application of
  `(X₁', θ₁')` to `(X₂, θ₂)`, which is proper (`isProperApplication_ratApp`,
  `Compat/FunctionFieldPairProper.lean`; used tacitly by the paper, proved here):
  a succession with non-singular irreducible nowhere dense centers after which the rational application is a morphism.
  Besides the cited results of the main theorems and the unique factorization of regular local rings, Question (E) rests
  on one cited statement, fact (*) of p. 141 as printed.  The two facts it uses tacitly, the existence of the primitive
  part of a sheaf of ideals and "the weak transform of a primitive ideal is primitive", are proved
  (`Compat/PrimitiveIdeal.lean`, `Compat/PrimitiveWeakTransform.lean`).
* Concatenate the two successions.  The non-singular addendum is the stability of non-singularity under monoidal
  transformations with non-singular centers (p. 142).

Deviation from the paper (gap filled): the derivation from Question (E) and the strong form, the nowhere density of the
centers, the integrality of the stages, the pair structure on the target and the concatenation are not argued in the paper.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

namespace Hironaka

universe u

namespace FunctionFieldPair

variable {B L : Type u} [Field B] [Field L] [Algebra B L]

/-- The elimination step of (1) for a non-singular proper pair: Question (E) applied to the (proper) rational application of
`(X₁, θ₁)` to `(X₂, θ₂)`. -/
theorem exists_isObtainedBy_dominates_of_isNonsingular [Hironaka.HironakaCitedResultsCh0.{u}] [CharZero B] (P₁ P₂ : FunctionFieldPair B L)
    (h₁ : P₁.IsProper) (h₂ : P₂.IsProper) (hns : P₁.X.IsNonsingular) :
    ∃ (P' : FunctionFieldPair B L) (s : MonoidalSuccession P₁.X P'.X),
      P₁.IsObtainedBy P' s ∧ P'.IsProper ∧ P'.Dominates P₂ := by
  obtain ⟨Xr, s, -, hint, hcent, hnd, hr, φ, -, hφ⟩ :=
    RationalApplication.question_E_integral P₁.p P₂.p hns (P₁.ratApp P₂) (isProperApplication_ratApp P₁ P₂ h₁ h₂)
  have hη : s.composite (genericPoint Xr) = genericPoint P₁.X := s.composite_genericPoint hnd
  have hobt : P₁.IsObtainedBy (P₁.ofSuccession s hnd) s :=
    P₁.ofSuccession_isObtainedBy s hnd hcent.hasNonsingularCenters
  refine ⟨P₁.ofSuccession s hnd, s, hobt, hobt.isProper h₁, ?_⟩
  -- `φ` induces `θ'∘θ₂⁻¹`, so `X'` dominates `X₂`
  refine dominates_of_fromSpecStalk_comp_eq _ P₂ φ ?_
  have h1 := congrArg Scheme.RationalMap.fromFunctionField hφ
  rw [fromFunctionField_toRationalMap_hom,
    Scheme.RationalMap.fromFunctionField_precomp (P₁.ratApp P₂) s.composite hr hη,
    fromFunctionField_ratApp] at h1
  have hθ : (P₁.ofSuccession s hnd).thetaHom P₂ =
      P₁.thetaHom P₂ ≫ functionFieldMap s.composite hη := by
    rw [← thetaHom_ofSuccession P₁ s hnd hη]
    ext x
    exact (congrArg (P₁.ofSuccession s hnd).θ (P₁.θ.symm_apply_apply (P₂.θ.symm x))).symm
  have e : (P₁.ofSuccession s hnd).ratFn P₂ =
      Spec.map ((P₁.ofSuccession s hnd).thetaHom P₂) ≫ P₂.X.fromSpecStalk (genericPoint P₂.X) := rfl
  have e0 : P₁.ratFn P₂ = Spec.map (P₁.thetaHom P₂) ≫ P₂.X.fromSpecStalk (genericPoint P₂.X) := rfl
  change Xr.fromSpecStalk (genericPoint Xr) ≫ φ = (P₁.ofSuccession s hnd).ratFn P₂
  rw [h1, e, e0, hθ, ← Category.assoc, ← Spec.map_comp]
  rfl

/-- **Consequence (1) of Corollary 1 of Main Theorem II** (p. 144), with its non-singular addendum: for two pairs of
`𝔐(L/B)` there is a pair `(X', θ') ∈ 𝔐(L/B)` obtained from `(X₁, θ₁)` by a finite succession of monoidal transformations
with non-singular (nowhere dense) centers, which dominates `(X₂, θ₂)`; if `X₁` is non-singular, so is `X'`.

Formalization notes (encoding): see `FunctionFieldPair`, `IsObtainedBy`, `Dominates`, `IsProper`; "domiates" is the printed
misprint of "dominates".  The addendum is the last conjunct.

Deviation from the paper (gap filled): the paper prints no argument; the proof is described in the header of this file.  It
uses the cited leaves of Question (E); the properness of the rational application (`isProperApplication_ratApp`) is used
tacitly by the paper and proved. -/
@[blueprint "cor:0.5-consequence-1"
  (statement := /-- Let $(X_1,\theta_1)$ and $(X_2,\theta_2)$ belong to $\mathfrak M(\mathbf L/\mathbf B)$. Then we can obtain
    $(X_1',\theta_1')\in\mathfrak M(\mathbf L/\mathbf B)$ from $(X_1,\theta_1)$ by means of a finite succession of monoidal
    transformations with non-singular centers, such that $(X_1',\theta_1')$ dominates $(X_2,\theta_2)$. If $X_1$ is
    non-singular, so is $X_1'$. (See also main theorem I in the strong form.) (p.~144.) Formalization note (encoding): the
    centers of the succession are nowhere dense, so that $\theta_1'$ exists. -/)
  (proof := /-- As consequences of Corollary~1 (no argument is printed). Resolve $X_1$ by the strong form of Main Theorem~I
    (\cref{thm:0.3-main-I-strong}); the centers do not contain the generic point, which is simple, and the end $X_1''$ is
    non-singular. Apply Question~(E) (\cref{cor:0.5-question-E-integral}) with $S_0=X_1''$ to the rational application of
    $(X_1'',\theta_1'')$ to $(X_2,\theta_2)$, which is proper (\cref{lem:0.5-ratapp-is-proper}): a succession of monoidal
    transformations with non-singular irreducible nowhere dense centers after which it is a morphism, i.e.\ $X_1'$ dominates
    $(X_2,\theta_2)$. Concatenate; non-singularity is preserved by monoidal transformations with non-singular centers.
    \textbf{Gap in the paper filled.} No argument is printed. -/)
  (proofUses := ["thm:0.3-main-I-strong", "cor:0.5-question-E-integral", "lem:0.5-ratapp-is-proper", "def:0.5-pair"])
  (latexEnv := "corollary")]
theorem exists_isObtainedBy_dominates [Hironaka.HironakaCitedResultsCh0.{u}] [CharZero B] (P₁ P₂ : FunctionFieldPair B L) (h₁ : P₁.IsProper)
    (h₂ : P₂.IsProper) :
    ∃ (P' : FunctionFieldPair B L) (s : MonoidalSuccession P₁.X P'.X),
      P₁.IsObtainedBy P' s ∧ P'.IsProper ∧ P'.Dominates P₂ ∧ (P₁.X.IsNonsingular → P'.X.IsNonsingular) := by
  -- resolve `X₁` (the printed hint "See also main theorem I in the strong form")
  have : IsAlgebraicScheme P₁.X := IsAlgebraicScheme.of_field P₁.p
  obtain ⟨Y₀, s₀, hs₀⟩ := MainTheorem.Ch0.I_strong_of_isAlgebraicScheme P₁.X
  have hnd₀ := s₀.nowhereDenseCenters_of_isStrongResolution hs₀
  have hobt₀ : P₁.IsObtainedBy (P₁.ofSuccession s₀ hnd₀) s₀ :=
    P₁.ofSuccession_isObtainedBy s₀ hnd₀ (s₀.hasNonsingularCenters_of_isStrongResolution hs₀)
  obtain ⟨P', s, hobt, hP', hdom⟩ := exists_isObtainedBy_dominates_of_isNonsingular
    (P₁.ofSuccession s₀ hnd₀) P₂ (isProper_ofSuccession h₁ s₀ hnd₀)
    h₂ (s₀.isNonsingular_of_isStrongResolution hs₀)
  exact ⟨P', s₀.append s, hobt₀.append hobt, hP', hdom, fun h => (hobt₀.append hobt).isNonsingular h⟩

end FunctionFieldPair

end Hironaka
