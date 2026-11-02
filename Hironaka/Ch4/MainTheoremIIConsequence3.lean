/-
Copyright (c) 2026 Daattavya Aggarwal, Minhyong Kim, Oisin Kim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daattavya Aggarwal, Minhyong Kim, Oisin Kim
-/
module

public import Architect
public import Hironaka.Ch4.MainTheoremIIConsequence1
public import Hironaka.Compat.FunctionFieldPairCited
public import Hironaka.Statements

/-!
# Ch. 0 §5 (p. 145): consequence (3) of Corollary 1 of Main Theorem II

> (3) Let `(X₁, θ₁) ∈ 𝔐(L/B)`.  Then we can obtain `(X', θ')` from it by means of a finite succession of monoidal
> transformations with non-singular centers, such that `X'` is non-singular and projective.  (We may assume that `X₁` is
> non-singular by main theorem I in the strong form.  Then we apply (1) to `(X₂, θ₂)` which dominates `(X₁, θ₁)` and of
> which `X₂` is projective.  The existence of such `(X₂, θ₂)` is obvious.  Note that the algebraic `B`-scheme `X'₁`
> obtained in (1) is then necessarily projective.)  (p. 145)

The proof follows the printed sketch.
* "We may assume that `X₁` is non-singular by main theorem I in the strong form": a strong resolution of `X₁`
  (`MainTheorem.Ch0.I_strong_of_isAlgebraicScheme`) gives a pair `(X₁', θ₁')` in `𝔐(L/B)` with `X₁'` non-singular, obtained
  from `(X₁, θ₁)` by a succession with non-singular nowhere dense centers.
* "The existence of such `(X₂, θ₂)` is obvious": used without proof or citation in the paper; assumed
  (`FunctionFieldPair.exists_projective_dominating`, cited leaf, `Compat/FunctionFieldPairCited.lean`).
* "Then we apply (1)": `FunctionFieldPair.exists_isObtainedBy_dominates` to `(X₁', θ₁')` and `(X₂, θ₂)`, giving
  `(X'₁, θ'₁)` which dominates `(X₂, θ₂)` and is non-singular (the addendum of (1)).
* "Note that `X'₁` … is then necessarily projective": used without proof or citation in the paper; assumed
  (`FunctionFieldPair.isProjectiveOver_of_isObtainedBy_dominates`, cited leaf).
* The two successions are concatenated (`FunctionFieldPair.IsObtainedBy.append`).

(1) rests on Question (E) (`Ch0/QuestionE.lean`), whose one cited statement beyond those of the main theorems and the unique
factorization of regular local rings is fact (*) of p. 141 as printed; the existence of the primitive part and "the weak
transform of a primitive ideal is primitive", which it uses tacitly, are proved.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

namespace Hironaka

universe u

namespace FunctionFieldPair

variable {B L : Type u} [Field B] [Field L] [Algebra B L]

/-- **Consequence (3) of Corollary 1 of Main Theorem II** (p. 145): from a pair `(X₁, θ₁) ∈ 𝔐(L/B)` one obtains a pair
`(X', θ')` by a finite succession of monoidal transformations with non-singular centers such that `X'` is non-singular and
projective (`IsProjectiveOver`, the definition of p. 132).

Deviation from the paper (gap filled): the reduction to non-singular `X₁` is carried out by the strong form of Main Theorem I
with the bookkeeping of nowhere dense centers and of the pair structure, and the successions are concatenated; the two
statements "The existence of such `(X₂, θ₂)` is obvious" and "necessarily projective" are used without proof or citation in
the paper and are assumed (cited leaves). -/
@[blueprint "cor:0.5-consequence-3"
  (statement := /-- Let $(X_1,\theta_1)\in\mathfrak M(\mathbf L/\mathbf B)$. Then we can obtain $(X',\theta')$ from it by means
    of a finite succession of monoidal transformations with non-singular centers, such that $X'$ is non-singular and
    projective. (p.~145; ``projective'' as on p.~132, \cref{def:0-projective-scheme}.) -/)
  (proof := /-- As printed (p.~145). By the strong form of Main Theorem~I (\cref{thm:0.3-main-I-strong}) we may assume that $X_1$
    is non-singular. Choose $(X_2,\theta_2)\in\mathfrak M(\mathbf L/\mathbf B)$ with $X_2$ projective which dominates
    $(X_1,\theta_1)$ (``The existence of such $(X_2,\theta_2)$ is obvious'', \cref{lem:0.5-projective-dominating}, assumed in
    the paper). Apply (1) (\cref{cor:0.5-consequence-1}) to $(X_1,\theta_1)$ and $(X_2,\theta_2)$: the scheme $X_1'$ obtained
    is non-singular and dominates $(X_2,\theta_2)$; it is projective (``necessarily projective'',
    \cref{lem:0.5-necessarily-projective}, assumed in the paper). Concatenate the successions.
    \textbf{Gaps in the paper filled.} The bookkeeping of the reduction and the concatenation; the two assumed statements are
    cited leaves. -/)
  (proofUses := ["thm:0.3-main-I-strong", "cor:0.5-consequence-1", "lem:0.5-projective-dominating",
    "lem:0.5-necessarily-projective", "def:0-projective-scheme"])
  (latexEnv := "corollary")]
theorem exists_isObtainedBy_nonsingular_projective [Hironaka.HironakaCitedResultsCh0.{u}] [CharZero B] (P₁ : FunctionFieldPair B L) (h₁ : P₁.IsProper) :
    ∃ (P' : FunctionFieldPair B L) (s : MonoidalSuccession P₁.X P'.X),
      P₁.IsObtainedBy P' s ∧ P'.X.IsNonsingular ∧ IsProjectiveOver P'.X P'.p := by
  -- "We may assume that `X₁` is non-singular by main theorem I in the strong form."
  have : IsAlgebraicScheme P₁.X := IsAlgebraicScheme.of_field P₁.p
  obtain ⟨Y₀, s₀, hs₀⟩ := MainTheorem.Ch0.I_strong_of_isAlgebraicScheme P₁.X
  have hnd₀ := s₀.nowhereDenseCenters_of_isStrongResolution hs₀
  have hobt₀ : P₁.IsObtainedBy (P₁.ofSuccession s₀ hnd₀) s₀ :=
    P₁.ofSuccession_isObtainedBy s₀ hnd₀ (s₀.hasNonsingularCenters_of_isStrongResolution hs₀)
  have hP₁' : (P₁.ofSuccession s₀ hnd₀).IsProper := isProper_ofSuccession h₁ s₀ hnd₀
  have hns : (P₁.ofSuccession s₀ hnd₀).X.IsNonsingular := s₀.isNonsingular_of_isStrongResolution hs₀
  -- "The existence of such `(X₂, θ₂)` is obvious."
  obtain ⟨P₂, hP₂, hproj, hdom⟩ := exists_projective_dominating (P₁.ofSuccession s₀ hnd₀) hP₁' hns
  -- "Then we apply (1) to `(X₂, θ₂)`"
  obtain ⟨P', s₁, hobt₁, hP', hdom', hnsg⟩ :=
    exists_isObtainedBy_dominates (P₁.ofSuccession s₀ hnd₀) P₂ hP₁' hP₂
  -- "Note that `X'₁` obtained in (1) is then necessarily projective."
  exact ⟨P', s₀.append s₁, hobt₀.append hobt₁, hnsg hns,
    isProjectiveOver_of_isObtainedBy_dominates hP₁' hns hobt₁ hproj hdom hdom'⟩

end FunctionFieldPair

end Hironaka
