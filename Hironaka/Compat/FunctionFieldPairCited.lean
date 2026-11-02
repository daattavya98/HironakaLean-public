/-
Copyright (c) 2026 Daattavya Aggarwal, Minhyong Kim, Oisin Kim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daattavya Aggarwal, Minhyong Kim, Oisin Kim
-/
module

public import Architect
public import Hironaka.Compat.FunctionFieldPair
public import Hironaka.Compat.ProjectiveVocabularyProper
public import Hironaka.Statements

/-!
# Consequence (3) of Corollary 1 (Ch. 0 §5, p. 145): the two statements used without proof

> (3) Let `(X₁, θ₁) ∈ 𝔐(L/B)`.  Then we can obtain `(X', θ')` from it by means of a finite succession of monoidal
> transformations with non-singular centers, such that `X'` is non-singular and projective.  (We may assume that `X₁`
> is non-singular by main theorem I in the strong form.  Then we apply (1) to `(X₂, θ₂)` which dominates `(X₁, θ₁)`
> and of which `X₂` is projective.  The existence of such `(X₂, θ₂)` is obvious.  Note that the algebraic `B`-scheme
> `X'₁` obtained in (1) is then necessarily projective.)  (p. 145)

The paper uses two statements here with neither proof nor citation: the existence of a projective `(X₂, θ₂)` dominating
`(X₁, θ₁)` ("obvious"), and the projectivity of `X'₁` ("necessarily").  Both are assumed, as in the paper: each is a
hypothesis (a cited leaf), stated exactly as it is used there, after the reduction to a non-singular `X₁` by the strong form of
Main Theorem I.  Both are true: the first is Chow's lemma (EGA II 5.6.1) applied to `X₁` (with `X₂ → X₁` birational), the
second follows from the projectivity of `X'₁ → X₁` (a composite of monoidal transformations), the separatedness of
`X₂ → X₁` and the projectivity of `X₂` over `B` (EGA II 5.5.5).
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

namespace Hironaka

universe u

namespace FunctionFieldPair

variable {B L : Type u} [Field B] [Field L] [Algebra B L]


/-- **Used without proof or citation; assumed, as in the paper** (cited leaf): for a pair `(X₁, θ₁) ∈ 𝔐(L/B)` with `X₁`
non-singular there is a pair `(X₂, θ₂) ∈ 𝔐(L/B)` with `X₂` projective which dominates `(X₁, θ₁)`.

> We may assume that `X₁` is non-singular by main theorem I in the strong form.  Then we apply (1) to `(X₂, θ₂)` which
> dominates `(X₁, θ₁)` and of which `X₂` is projective.  The existence of such `(X₂, θ₂)` is obvious.  (p. 145)

Encoding: "projective" is the definition of p. 132, `IsProjectiveOver` (`X₂ = Proj H`, `H` a graded quotient of a
polynomial ring over `B`); the non-singularity of `X₁` is the context in which the paper uses the statement (it is not
needed for the truth of the statement, which is Chow's lemma for the proper integral `B`-scheme `X₁`). -/
@[blueprint "lem:0.5-projective-dominating"
  (statement := /-- Let $(X_1,\theta_1)\in\mathfrak M(\mathbf L/\mathbf B)$ with $X_1$ non-singular. Then there is a pair
    $(X_2,\theta_2)\in\mathfrak M(\mathbf L/\mathbf B)$ which dominates $(X_1,\theta_1)$ and of which $X_2$ is projective.
    (p.~145, ``The existence of such $(X_2,\theta_2)$ is obvious.'') -/)
  (proof := /-- Used without proof or citation in the paper (assumed, as in the paper). It is Chow's lemma (EGA~II
    5.6.1) for the proper integral scheme $X_1$: there is a projective integral $X_2$ with a birational morphism
    $X_2\to X_1$. -/)
  (latexEnv := "lemma")]
theorem exists_projective_dominating [Hironaka.Cited.FunctionFieldPairExistsProjectiveDominating.{u}] :
    ∀ (P₁ : FunctionFieldPair B L) (_hP₁ : P₁.IsProper)
    (_hns : P₁.X.IsNonsingular),
    ∃ P₂ : FunctionFieldPair B L, P₂.IsProper ∧ IsProjectiveOver P₂.X P₂.p ∧ P₂.Dominates P₁ :=
  @Hironaka.Cited.FunctionFieldPairExistsProjectiveDominating.exists_projective_dominating _ B L _ _ _


/-- **Used without proof or citation; assumed, as in the paper** (cited leaf): let `(X₁, θ₁) ∈ 𝔐(L/B)` with `X₁`
non-singular, let `(X₂, θ₂)` with `X₂` projective dominate `(X₁, θ₁)`, and let `(X'₁, θ'₁)` be obtained from `(X₁, θ₁)` by
a finite succession of monoidal transformations with non-singular centers and dominate `(X₂, θ₂)`.  Then `X'₁` is
projective.

> Note that the algebraic `B`-scheme `X'₁` obtained in (1) is then necessarily projective.  (p. 145)

Encoding: "projective" is `IsProjectiveOver` (p. 132); "obtained in (1)" is `IsObtainedBy` together with `Dominates`; the
hypotheses on `(X₁, θ₁)` are the context of the paper's use (after the reduction to non-singular `X₁`). -/
@[blueprint "lem:0.5-necessarily-projective"
  (statement := /-- Let $(X_1,\theta_1)\in\mathfrak M(\mathbf L/\mathbf B)$ with $X_1$ non-singular, let $(X_2,\theta_2)$ with
    $X_2$ projective dominate $(X_1,\theta_1)$, and let $(X_1',\theta_1')$ be obtained from $(X_1,\theta_1)$ by a finite
    succession of monoidal transformations with non-singular centers such that $(X_1',\theta_1')$ dominates
    $(X_2,\theta_2)$. Then $X_1'$ is projective. (p.~145, ``Note that the algebraic $\mathbf B$-scheme $X_1'$ obtained in
    (1) is then necessarily projective.'') -/)
  (proof := /-- Used without proof or citation in the paper (assumed, as in the paper). The morphism $X_1'\to X_1$ is a
    composite of monoidal transformations, hence projective, and $X_2\to X_1$ is separated, so $X_1'\to X_2$ is projective
    (EGA~II 5.5.5); composing with the projective $X_2\to\operatorname{Spec}\mathbf B$ shows that $X_1'$ is projective. -/)
  (latexEnv := "lemma")]
theorem isProjectiveOver_of_isObtainedBy_dominates [Hironaka.Cited.FunctionFieldPairIsProjectiveOverOfIsObtainedByDominates.{u}] :
    ∀ {P₁ P₂ P' : FunctionFieldPair B L}
    {s : MonoidalSuccession P₁.X P'.X} (_hP₁ : P₁.IsProper) (_hns : P₁.X.IsNonsingular)
    (_hs : P₁.IsObtainedBy P' s) (_hP₂ : IsProjectiveOver P₂.X P₂.p) (_h₂₁ : P₂.Dominates P₁)
    (_h'₂ : P'.Dominates P₂),
    IsProjectiveOver P'.X P'.p :=
  @Hironaka.Cited.FunctionFieldPairIsProjectiveOverOfIsObtainedByDominates.isProjectiveOver_of_isObtainedBy_dominates _ B L _ _ _

end FunctionFieldPair

end Hironaka
