/-
Copyright (c) 2026 Daattavya Aggarwal, Minhyong Kim, Oisin Kim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daattavya Aggarwal, Minhyong Kim, Oisin Kim
-/
module

public import Architect
public import Hironaka.Compat.ProjectiveModelResolution
public import Hironaka.Statements

/-!
# Successions of monoidal transformations with nowhere dense centers (Ch. 0 §5, p. 144)

> If `(X, θ)` is as above, and if `f : X' → X` is a monoidal transformation with center nowhere dense in `X`, we have a
> unique `B`-isomorphism `θ'` of `L` to the function field of `X'` such that `θ ∘ θ'⁻¹` is induced by `f`.  (p. 144)

The predicate `MonoidalSuccession.NowhereDenseCenters` says that every center of a succession is nowhere dense in its
stage.  For an integral scheme this means that the center misses the generic point; along such a succession of an
integral scheme every stage is integral and the composite maps the generic point to the generic point.  None of these
facts is stated in the paper (bookkeeping of the encoding).
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace Hironaka

universe u

/-- A center is nowhere dense iff it misses the generic point of an integral scheme: the center is closed, and the
generic point lies in every non-empty open set.
Encoding: "nowhere dense" (p. 144) is `interior D.pts = ∅`. -/
theorem Subscheme.interior_pts_eq_empty_iff {X : Scheme.{u}} [IsIntegral X] (D : Subscheme X) :
    interior D.pts = ∅ ↔ genericPoint X ∉ D.pts := by
  constructor
  · intro h hη
    have hcl : IsClosed D.pts := D.support.isClosed
    have hsub : closure {genericPoint X} ⊆ D.pts := hcl.closure_subset_iff.mpr (by simpa using hη)
    rw [(genericPoint_spec X).def] at hsub
    have : D.pts = Set.univ := Set.eq_univ_of_univ_subset hsub
    rw [this, interior_univ] at h
    exact (Set.univ_nonempty (α := X)).ne_empty h
  · intro h
    by_contra hne
    obtain ⟨x, hx⟩ := Set.nonempty_iff_ne_empty.mpr hne
    have hηmem : genericPoint X ∈ interior D.pts :=
      ((genericPoint_spec X).mem_open_set_iff isOpen_interior).mpr ⟨x, trivial, hx⟩
    exact h (interior_subset hηmem)

namespace MonoidalSuccession


variable {X Y : Scheme.{u}}

/-- Along a succession of an integral scheme with nowhere dense centers, every scheme is integral. -/
theorem isIntegral_of_nowhereDenseCenters (s : MonoidalSuccession X Y) [IsIntegral X]
    (hs : s.NowhereDenseCenters) : IsIntegral Y := by
  revert ‹IsIntegral X›
  induction s with
  | nil X => intro _; assumption
  | cons D t rest ih =>
    intro _
    have := t.isIntegral_of_genericPoint_notMem ((Subscheme.interior_pts_eq_empty_iff D).mp hs.1)
    exact ih hs.2

/-- The composite of a succession of an integral scheme with nowhere dense centers maps the generic point to the generic
point. -/
theorem composite_genericPoint (s : MonoidalSuccession X Y) [IsIntegral X] [IsIntegral Y]
    (hs : s.NowhereDenseCenters) : s.composite (genericPoint Y) = genericPoint X := by
  revert ‹IsIntegral X› ‹IsIntegral Y›
  induction s with
  | nil X => intro _ _; rfl
  | cons D t rest ih =>
    intro _ _
    have hD := (Subscheme.interior_pts_eq_empty_iff D).mp hs.1
    have := t.isIntegral_of_genericPoint_notMem hD
    rw [composite_cons, Scheme.Hom.comp_apply, ih hs.2, t.map_genericPoint hD]

end MonoidalSuccession

end Hironaka
