/-
Copyright (c) 2026 Daattavya Aggarwal, Minhyong Kim, Oisin Kim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daattavya Aggarwal, Minhyong Kim, Oisin Kim
-/
module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Basic
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Architect
public import Hironaka.Ch2.PointwiseFlatness
public import Hironaka.Compat.LocalizeSuccession

/-!
# Remark 1 (Ch. I §1, p. 169): the case `X = B` and the dimension of `W'`

> Then we have dim(X') = dim(X) = N, unless X = B. If X = B, then X' is the empty algebraic scheme.
> This can happen only if ℜ = ℜ_I^{N,n} (as in Definition 3) and X = V_i = W for all i, in which
> case the datum ℜ_I^{N,n} is clearly resolved everywhere. We exclude once for always this
> uninteresting case in which X = W. Let W' be as in Definition 7. Then we have
> dim(W') = dim(W) = n, unless B contains an irreducible component of W. Note that B can not
> contain any irreducible component of W if ℜ has restriction either closed or open.

This file completes the formalization of these sentences:

* "clearly resolved everywhere": a type I datum with `W = V_j = X` (`B = X` forces this,
  `DatumI.Raw.eq_bot_of_isPermissible_of_pts_eq_univ`) is resolved at every point
  (`DatumI.Raw.resolvedEverywhere_of_eq_bot`);
* the remark that `B` contains no irreducible component of `W` for a closed or open restriction, and the
  resulting equality `dim(W') = dim(W)` (`DatumI.Raw.dim_transform_W_eq_of_restriction`).  The first
  half is `DatumI.Raw.IsPermissibleClosed.not_pts_subset_of_mem_irreducibleComponents` and its open
  analogue (`Hironaka/Compat/LocalizeSuccession.lean`), the second is `DatumI.Raw.dim_transform_W`.

The remaining statements of the passage are in `Hironaka/Ch1/ResolutionData.lean`
(`MonoidalTransformation.transform_isAmbient`, `MonoidalTransformation.isEmpty_of_pts_eq_univ`,
`DatumII.Raw.pts_ne_univ_of_isPermissible`).
-/

@[expose] public section

open AlgebraicGeometry

namespace Hironaka

universe u

namespace DatumI.Raw

variable {X : Scheme.{u}}

/-- Remark 1 (p. 169): "in which case the datum `ℜ_I^{N,n}` is clearly resolved everywhere": if `W = V_j = X`
for all `j`, the datum is resolved at every point of `W`.  `W = X` is simple at every point (`X` is
non-singular), `V_j = X` is normally flat along `W = X` (a regular local ring is normally flat along the zero
ideal), and `E` has only normal crossings with `W = X` since it has them at every point.

Deviation from the paper (gap filled): the paper says "clearly". -/
@[blueprint "rem:I.1-dim-resolved"
  (statement := /-- Let $\mathfrak R=(E;V_1,\dots,V_\beta;W)$ be a resolution datum of type
    $\mathfrak R^{N,n}_{\mathrm I}$ on a non-singular algebraic scheme $X$ with $W=V_j=X$ for all $j$. Then
    $\mathfrak R$ is resolved everywhere. (Remark~1, p.~169: ``clearly resolved everywhere''.)
    \textbf{Gap in the paper filled.} The paper says only ``clearly''; the verification is in the proof below. -/)
  (proof := /-- $W=X$ is simple at every point as $X$ is non-singular; $V_j=X$ is normally flat along
    $W=X$ (a regular local ring is normally flat along the zero ideal); $E$ has only normal crossings at
    every point. -/)
  (latexEnv := "lemma")]
theorem resolvedEverywhere_of_eq_bot [IsAlgebraicScheme X] (hX : X.IsNonsingular) (ℜ : Raw X)
    (hℜ : ℜ.IsDatum) (hW : ℜ.W = ⊥) (hV : ∀ j, ℜ.V j = ⊥) : ℜ.ResolvedEverywhere := by
  intro x _
  have hsimple : (⊥ : Subscheme X).IsSimpleAt x := by
    have : IsRegularLocalRing (X.presheaf.stalk x) := hX x
    refine ⟨Subscheme.mem_pts_iff_stalkIdeal_ne_top.mpr ?_, ?_⟩
    · rw [Subscheme.stalkIdeal_bot_eq]
      exact bot_ne_top
    · rw [Subscheme.stalkIdeal_bot_eq]
      exact IsRegularLocalRing.of_ringEquiv (RingEquiv.quotientBot (X.presheaf.stalk x)).symm
  refine ⟨by rw [hW]; exact hsimple, fun j => ?_, by rw [hW]; exact hℜ.2.2.1 x⟩
  rw [hW, hV j]
  exact Subscheme.isNormallyFlatAlongAt'_of_isSimpleAt (fun U => le_rfl) hsimple hsimple

/-- Remark 1 (p. 169): "Then we have `dim(W') = dim(W) = n`, unless `B` contains an irreducible component of
`W`. Note that `B` can not contain any irreducible component of `W` if `ℜ` has restriction either closed or
open."  For a permissible `B` and a closed restriction `F` (resp. an open restriction `U`) of `ℜ`: no
irreducible component of `W` lies in `B`, hence `dim(W') = dim(W)`.

Deviation from the paper (gap filled): the paper gives no argument.  The first half: `W − W ∩ F` (resp. `U`)
is dense in `W`, so every irreducible component of `W` has a point off `F` (resp. in `U`), while
`B ⊆ W ∩ F` (resp. `B ⊆ W − U`) (`DatumI.Raw.IsPermissibleClosed.not_pts_subset_of_mem_irreducibleComponents`
and the open analogue, `Hironaka/Compat/LocalizeSuccession.lean`); the second half is
`DatumI.Raw.dim_transform_W`. -/
@[blueprint "rem:I.1-dim-W-restriction"
  (statement := /-- Let $\mathfrak R=(E;V;W)$ be a resolution datum of type $\mathfrak R^{N,n}_{\mathrm I}$ on a
    non-singular algebraic scheme $X$ and $f\colon X'\to X$ the monoidal transformation with a center $B$
    permissible for $\mathfrak R$. If $\mathfrak R$ has a closed restriction $F$ and $B\subseteq W\cap F$, or an
    open restriction $U$ and $B\subseteq W-U$, then $B$ contains no irreducible component of $W$ and
    $\dim(W')=\dim(W)$. (Remark~1, p.~169.)
    \textbf{Gap in the paper filled.} The paper states the remark without proof. -/)
  (proof := /-- $W-W\cap F$ (resp.\ $U$) is dense in $W$, hence meets every irreducible component of $W$,
    while $B\subseteq W\cap F$ (resp.\ $B\subseteq W-U$) does not meet it. So $B$ contains no component
    and the dimension statement of \cref{rem:I.1-dim-W} applies. -/)
  (latexEnv := "remark")]
theorem dim_transform_W_eq_of_restriction [Hironaka.Cited.MonoidalTransformationExistsIsProper.{u}] [IsAlgebraicScheme X] (hX : X.IsNonsingular) (ℜ : Raw X)
    (hℜ : ℜ.IsDatum) {B : Subscheme X} (t : MonoidalTransformation X B) :
    (∀ F, ℜ.IsClosedRestriction F → ℜ.IsPermissibleClosed F B →
      (∀ C ∈ ℜ.W.irreducibleComponents, ¬ C.pts ⊆ B.pts) ∧ (ℜ.transform t).W.dim = ℜ.W.dim) ∧
    (∀ U, ℜ.IsOpenRestriction U → ℜ.IsPermissibleOpen U B →
      (∀ C ∈ ℜ.W.irreducibleComponents, ¬ C.pts ⊆ B.pts) ∧ (ℜ.transform t).W.dim = ℜ.W.dim) := by
  refine ⟨fun F hF hB => ?_, fun U hU hB => ?_⟩
  · have h := IsPermissibleClosed.not_pts_subset_of_mem_irreducibleComponents hF hB
    exact ⟨h, (dim_transform_W hX ℜ hℜ t hB.1).2 h⟩
  · have h := IsPermissibleOpen.not_pts_subset_of_mem_irreducibleComponents hU hB
    exact ⟨h, (dim_transform_W hX ℜ hℜ t hB.1).2 h⟩

end DatumI.Raw

end Hironaka
