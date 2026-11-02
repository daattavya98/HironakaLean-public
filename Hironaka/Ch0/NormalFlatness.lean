/-
Copyright (c) 2026 Daattavya Aggarwal, Minhyong Kim, Oisin Kim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daattavya Aggarwal, Minhyong Kim, Oisin Kim
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.RingTheory.LocalRing.Module
public import Architect
public import Hironaka.Compat.Graded
public import Hironaka.Ch0.AlgebraicScheme
public import Hironaka.Ch0.Blowup
public import Hironaka.Ch0.Multiplicity
public import Hironaka.Statements

/-!
# Ch. 0 §4, Definition 1 (pp. 135–136): normal flatness

> Let X be a local-ringed space. Let D be a local-ringed subspace of X defined by a sheaf of
> ideals J. We denote by gr^p_D(X) the sheaf of modules on D obtained as the restriction of
> the quotient sheaf J^p/J^{p+1} to D. For a point x of D, we say that X is normally flat
> along D at the point x, if the stalk of gr^p_D(X) at x is a free O_{D,x}-module for all
> non-negative integers p. We say that X is normally flat along D if it is so at every point
> of D.  … The normal flatness of X along D is equivalent to saying that gr_D(X) is O_D-flat,
> if the local rings O_{X,x} (hence O_{D,x}) are all noetherian.

We formalize the stalk condition ring-theoretically: with `O = O_{X,x}` and `P = J_x`,
the stalk of gr^p_D(X) is `P^p / P^{p+1}`, an `O/P`-module (`GrPiece`, in
`Hironaka/Compat/Graded.lean`).

-/

@[expose] public section

open AlgebraicGeometry

namespace Hironaka

universe u

section RingLevel

variable {O : Type u} [CommRing O]


/-- p. 136: for noetherian `O`, freeness of all graded pieces is equivalent to flatness of
`gr_P(O)` over `O/P` (finitely generated flat modules over a local ring are free). -/
@[blueprint "lem:normally-flat-iff-flat"
  (statement := /-- If $O$ is a noetherian local ring, $O$ is normally flat along $P$ iff
    every $P^p/P^{p+1}$ is a flat $O/P$-module. -/)
  (proof := /-- Finitely generated flat modules over a local ring are free. -/)
  (latexEnv := "lemma")]
theorem isNormallyFlatAlongIdeal_iff_flat [IsLocalRing O] [IsNoetherianRing O] (P : Ideal O) :
    IsNormallyFlatAlongIdeal P ↔ ∀ p : ℕ, Module.Flat (O ⧸ P) (GrPiece P p) := by
  refine ⟨fun h p => ?_, fun h p => ?_⟩
  · -- free ⇒ flat
    have := h p
    infer_instance
  · -- flat ⇒ free: `Pᵖ/Pᵖ⁺¹` is finitely generated over `O/P`, and finitely generated flat
    -- modules over a local ring are free. If `P = ⊤` then `O/P = 0` and every module is free.
    by_cases hP : P = ⊤
    · have : Subsingleton (O ⧸ P) := Ideal.Quotient.subsingleton_iff.mpr hP
      have : Subsingleton (GrPiece P p) := Module.subsingleton (O ⧸ P) (GrPiece P p)
      infer_instance
    · have : Nontrivial (O ⧸ P) := Ideal.Quotient.nontrivial_iff.mpr hP
      have : IsLocalRing (O ⧸ P) :=
        IsLocalRing.of_surjective' (Ideal.Quotient.mk P) Ideal.Quotient.mk_surjective
      have := h p
      exact Module.free_of_flat_of_isLocalRing

/-- p. 136: "The normal flatness of X along D is equivalent to saying that gr_D(X) is O_D-flat,
if the local rings O_{X,x} (hence O_{D,x}) are all noetherian."  On the stalk at `x` this is the
equivalence between Definition 1 (freeness of the pieces) and flatness of the graded algebra
`gr_P(O)` over `O/P`. -/
@[blueprint "lem:0.1-normally-flat-iff-gr-flat"
  (statement := /-- Let $O$ be a noetherian local ring and $P$ an ideal. Then $O$ is normally
    flat along $P$ (\cref{def:normally-flat-ideal}) if and only if $\operatorname{gr}_P(O)$ is
    a flat $O/P$-module (p.~136). -/)
  (proof := /-- A direct sum is flat iff each summand is (\cref{lem:normally-flat-iff-flat}). -/)
  (latexEnv := "lemma")]
theorem isNormallyFlatAlongIdeal_iff_isGrFlat [IsLocalRing O] [IsNoetherianRing O] (P : Ideal O) :
    IsNormallyFlatAlongIdeal P ↔ IsGrFlat P := by
  rw [isNormallyFlatAlongIdeal_iff_flat, isGrFlat_iff_forall_flat_piece]

end RingLevel

/-! ### Scheme level -/

namespace Subscheme

variable {X : Scheme.{u}}


/-- Definition 1: `X` is normally flat along `D` (at every point of `D`). -/
@[blueprint "def:0.1-normally-flat"
  (statement := /-- $X$ is \emph{normally flat along $D$} if it is so at every point of $D$. -/)
  (latexEnv := "definition")]
def IsNormallyFlatAlong (D : Subscheme X) : Prop :=
  ∀ x ∈ D.pts, D.IsNormallyFlatAlongAt x


/-- Normal flatness of a subscheme `V ⊆ X` along a subscheme `W ⊆ V` at every point of `W`
("V is normally flat along W", as in Ch. II Cor. 2 of Th. 2 and Cor. of Th. 3). -/
def IsNormallyFlatAlong' (V W : Subscheme X) : Prop := ∀ x ∈ W.pts, IsNormallyFlatAlongAt' V W x

end Subscheme

end Hironaka
