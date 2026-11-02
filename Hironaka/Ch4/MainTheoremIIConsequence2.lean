/-
Copyright (c) 2026 Daattavya Aggarwal, Minhyong Kim, Oisin Kim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daattavya Aggarwal, Minhyong Kim, Oisin Kim
-/
module

public import Architect
public import Hironaka.Compat.FunctionFieldPair
public import Hironaka.Ch4.MainTheoremIIConsequence1
public import Hironaka.Compat.HigherDirectImageStructureSheaf
public import Hironaka.Statements

/-!
# Ch. 0 §5 (p. 145): consequence (2) of Corollary 1 of Main Theorem II

> (2) Let us suppose that `(X₁, θ₁)` dominates `(X₂, θ₂)` and that both `X₁` and `X₂` are non-singular.  Let `f` be the
> rational application of `(X₁, θ₁)` to `(X₂, θ₂)`, which is a morphism of `X₁` to `X₂`.  Then the direct images
> `Rⁱf(O_{X₁})` of `O_{X₁}` by `f` are zero sheaves on `X₂` except `R⁰f(O_{X₁})` which is `O_{X₂}`.  (In fact, it follows
> from the same result for a monoidal transformation of a non-singular algebraic `B`-scheme with non-singular center,
> and from (1) applied twice.)  (p. 145)

The proof is the printed one: the single blow-up case (a cited leaf of `Hironaka/Compat/HigherDirectImageStructureSheaf.lean`),
its extension to successions, the Leray edge maps (`exists_lerayEdge`, used tacitly by the paper and proved), and the
retract argument `higherDirectImage_structureSheaf_of_dominating`, applied to the two successions given by (1).  This module
supplies the translation between the pairs `(X, θ)` of p. 144 (`Hironaka/Compat/FunctionFieldPair.lean`) and the morphisms
in that argument: a morphism inducing `θ₁ ∘ θ₂⁻¹` on the function fields is determined by it (two morphisms from an integral scheme
to a separated one agree if they agree on the generic point), hence the composites `h ≫ f`, `h' ≫ h` of the two dominations
are the composites of the two successions.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace Hironaka

universe u

namespace FunctionFieldPair

variable {B L : Type u} [Field B] [Field L] [Algebra B L]

/-- Two morphisms of pairs inducing `θ₁ ∘ θ₂⁻¹` on the function fields compose to a morphism inducing the composite
isomorphism: `Spec K(X₁) → X₁ → X₂ → X₃` is the rational application of `(X₁, θ₁)` to `(X₃, θ₃)`. -/
theorem fromSpecStalk_comp_comp_eq (P Q R : FunctionFieldPair B L) (g : P.X ⟶ Q.X) (g' : Q.X ⟶ R.X)
    (h : P.X.fromSpecStalk (genericPoint P.X) ≫ g = P.ratFn Q)
    (h' : Q.X.fromSpecStalk (genericPoint Q.X) ≫ g' = Q.ratFn R) :
    P.X.fromSpecStalk (genericPoint P.X) ≫ (g ≫ g') = P.ratFn R := by
  have hθ : Q.thetaHom R ≫ P.thetaHom Q = P.thetaHom R := by
    ext x
    simp [thetaHom_apply]
  have e1 : P.ratFn Q = Spec.map (P.thetaHom Q) ≫ Q.X.fromSpecStalk (genericPoint Q.X) := rfl
  have e2 : Q.ratFn R = Spec.map (Q.thetaHom R) ≫ R.X.fromSpecStalk (genericPoint R.X) := rfl
  have e3 : P.ratFn R = Spec.map (P.thetaHom R) ≫ R.X.fromSpecStalk (genericPoint R.X) := rfl
  rw [← Category.assoc, h, e1, Category.assoc, h', e2, e3, ← Category.assoc, ← Spec.map_comp, hθ]

/-- A morphism of pairs is determined by the map of function fields it induces. -/
theorem eq_of_fromSpecStalk_comp_eq (P Q : FunctionFieldPair B L) {g g' : P.X ⟶ Q.X}
    (h : P.X.fromSpecStalk (genericPoint P.X) ≫ g = P.ratFn Q)
    (h' : P.X.fromSpecStalk (genericPoint P.X) ≫ g' = P.ratFn Q) : g = g' :=
  Scheme.RationalMap.eq_of_toRationalMap_eq (((P.ratApp_eq_toRationalMap_iff Q g).mpr h).symm.trans
    ((P.ratApp_eq_toRationalMap_iff Q g').mpr h'))

/-- **Consequence (2) of Corollary 1 of Main Theorem II (p. 145).**  Let `(X₁, θ₁)` and `(X₂, θ₂)` be pairs of `𝔐(L/B)`
with `(X₁, θ₁)` dominating `(X₂, θ₂)` and `X₁`, `X₂` non-singular, and let `f : X₁ ⟶ X₂` be the rational application of
`(X₁, θ₁)` to `(X₂, θ₂)`, which is a morphism.  Then `Rⁱf_*O_{X₁} = 0` for `i > 0` and `R⁰f_*O_{X₁}` is `O_{X₂}`: the
comorphism `O_{X₂} → f_*O_{X₁}` is an isomorphism, and so is its composite `O_{X₂} → f_*O_{X₁} → R⁰f_*O_{X₁}`.

Proof, as printed: "it follows from the same result for a monoidal transformation of a non-singular algebraic `B`-scheme
with non-singular center, and from (1) applied twice": `higherDirectImage_structureSheaf_of_dominating`, with the two
successions given by (1) applied to `((X₂, θ₂), (X₁, θ₁))` and then to `((X₁, θ₁), (X', θ'))`.

Deviation from the paper (gap filled): the passage from the blow-up case and (1) to (2) is the retract argument of
`higherDirectImage_structureSheaf_of_dominating`; the identifications `h ≫ f = s.composite`, `h' ≫ h = s'.composite` of the
composites of the two dominations with those of the successions (both induce the same isomorphism of function fields)
are ours.

Deviation from the paper (hypothesis added): the printed (2) speaks of arbitrary pairs `(X, θ)` of p. 144 and does not
require them to be proper.  Lean requires `(X₁, θ₁), (X₂, θ₂) ∈ 𝔐(L/B)` (`hP₁`, `hP₂`), the hypothesis under which (1) is
stated, since the printed proof applies (1) twice.  Without it the statement is false: for `X₂ = 𝔸¹_B`, `X₁ = 𝔸¹_B ∖ {0}`
and `f` the inclusion, `f_*O_{X₁} = B[t, t⁻¹] ≠ B[t] = O_{X₂}`. -/
@[blueprint "cor:0.5-consequence-2"
  (statement := /-- Let $(X_1,\theta_1)$ and $(X_2,\theta_2)$ be pairs of $\mathfrak M(\mathbf L/\mathbf B)$ such that
    $(X_1,\theta_1)$ dominates $(X_2,\theta_2)$ and both $X_1$ and $X_2$ are non-singular, and let $f\colon X_1\to X_2$ be
    the rational application of $(X_1,\theta_1)$ to $(X_2,\theta_2)$, which is a morphism. Then the direct images
    $R^if_*(\mathcal O_{X_1})$ are zero sheaves on $X_2$ except $R^0f_*(\mathcal O_{X_1})$ which is $\mathcal O_{X_2}$.
    (p.~145.) Formalization note (hypothesis added): the printed (2) does not require the pairs to lie in
    $\mathfrak M(\mathbf L/\mathbf B)$, i.e.\ to be proper; its proof applies (1), which is stated for
    $\mathfrak M(\mathbf L/\mathbf B)$, and without properness the statement is false ($X_2=\mathbb A^1_B$,
    $X_1=\mathbb A^1_B\setminus\{0\}$, $f$ the inclusion: $f_*\mathcal O_{X_1}=B[t,t^{-1}]\ne\mathcal O_{X_2}$). -/)
  (proof := /-- ``(In fact, it follows from the same result for a monoidal transformation of a non-singular algebraic
    $B$-scheme with non-singular center, and from (1) applied twice.)'' Apply (1) to $((X_2,\theta_2),(X_1,\theta_1))$ and
    then to $((X_1,\theta_1),(X',\theta'))$, and argue by retract
    (\cref{thm:0.5-direct-image-dominating}), using the blow-up case
    (\cref{thm:0.5-direct-image-monoidal-transformation}). Gap filled: the paper only says ``(1) applied twice''. -/)
  (proofUses := ["thm:0.5-direct-image-dominating"])
  (latexEnv := "corollary")]
theorem exists_higherDirectImage_structureSheaf [Hironaka.HironakaCitedResultsCh0.{u}] [CharZero B] (P₁ P₂ : FunctionFieldPair B L)
    (hP₁ : P₁.IsProper) (hP₂ : P₂.IsProper) (_hdom : P₁.Dominates P₂)
    (hn₁ : P₁.X.IsNonsingular) (hn₂ : P₂.X.IsNonsingular) (f : P₁.X ⟶ P₂.X)
    (hf : f.toRationalMap = P₁.ratApp P₂) :
    (∀ i, 0 < i → IsZero (higherDirectImageStructure f i)) ∧ IsIso f.structureUnit ∧
      IsIso (structureUnitR0 f) := by
  have hfc : P₁.X.fromSpecStalk (genericPoint P₁.X) ≫ f = P₁.ratFn P₂ :=
    (P₁.ratApp_eq_toRationalMap_iff P₂ f).mp hf.symm
  -- first application of (1): `P'`, obtained from `P₂`, dominates `P₁`
  obtain ⟨P', s, hs, hP', hdom', hn'⟩ := exists_isObtainedBy_dominates P₂ P₁ hP₂ hP₁
  obtain ⟨h, -, -, hhc⟩ := hdom'.exists_hom
  -- second application of (1): `P''`, obtained from `P₁`, dominates `P'`
  obtain ⟨P'', s', hs', hP'', hdom'', hn''⟩ := exists_isObtainedBy_dominates P₁ P' hP₁ hP'
  obtain ⟨h', -, -, hh'c⟩ := hdom''.exists_hom
  have hη : h (genericPoint P'.X) = genericPoint P₁.X :=
    map_genericPoint_of_fromSpecStalk_comp_eq P' P₁ h hhc
  have hfh : h ≫ f = s.composite := by
    refine eq_of_fromSpecStalk_comp_eq P' P₂ (fromSpecStalk_comp_comp_eq P' P₁ P₂ h f hhc hfc) ?_
    exact (P'.ratApp_eq_toRationalMap_iff P₂ s.composite).mp hs.2.2.2
  have hk : h' ≫ h = s'.composite := by
    refine eq_of_fromSpecStalk_comp_eq P'' P₁ (fromSpecStalk_comp_comp_eq P'' P' P₁ h' h hh'c hhc) ?_
    exact (P''.ratApp_eq_toRationalMap_iff P₁ s'.composite).mp hs'.2.2.2
  obtain ⟨hz, hu⟩ := higherDirectImage_structureSheaf_of_dominating P₁.p P₂.p f h h' s s' hn₁ hn₂
    hs.2.1 hs.1 hs'.2.1 hs'.1 hfh hk hη
  exact ⟨hz, hu, (isIso_structureUnitR0_iff f).mpr hu⟩

end FunctionFieldPair

end Hironaka
