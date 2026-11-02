/-
Copyright (c) 2026 Daattavya Aggarwal, Minhyong Kim, Oisin Kim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daattavya Aggarwal, Minhyong Kim, Oisin Kim
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Architect
public import Hironaka.Compat.BlowupBaseChange
public import Hironaka.Compat.BlowupLocalIso
public import Hironaka.Compat.RationalMapPrecomp

/-!
# Ch. 0 §5 (p. 139): the composition `f ∘ h` with a monoidal transformation of nowhere dense center

> Let `D` be an algebraic subscheme (resp. an analytic subspace) of `X`, and `h : X' → X` the monoidal transformation of
> `X` with center `D`.  If the set of points of `D` is nowhere dense in the underlying topological space of `X`, then we
> get a unique rational application `f'` of `X'` to `Y` which is the composition `f ∘ h` (i.e., the composition of `f`
> and the rational application of `X'` to `X` to which `h` belongs.).  We shall only consider the case in which `X` is
> reduced, so that `X'` is necessarily reduced for every monoidal transformation `h` as above.  (p. 139)

The composition of a rational application with a morphism is `Scheme.RationalMap.precomp`
(`Hironaka/Compat/RationalMapPrecomp.lean`); it needs the hypothesis `Scheme.Hom.PreimageDense` of p. 139 on the
morphism.  This file proves that a monoidal transformation of an algebraic scheme satisfies it (the paper says that `f ∘ h` exists, without argument).  The ingredients exist: the exceptional subscheme is nowhere
dense (`MonoidalTransformation.interior_pts_exceptional`) and off the center `f` is an isomorphism
(`MonoidalTransformation.isIso_morphismRestrict_complOpens`, p. 167).

None of this is printed in the paper (bookkeeping of the encoding).
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace

universe u

namespace Hironaka

namespace MonoidalTransformation

variable {X : Scheme.{u}} {B : Subscheme X}

/-- **The monoidal transformation of an algebraic scheme has dense preimages**: the composition `f ∘ h` of p. 139
exists.  The proof: `f` is an isomorphism off the center, so an open dense set `V` of `X` has the dense preimage
`f⁻¹(V − B)` in the complement of the exceptional subscheme, which is nowhere dense, hence dense in `X'`.  (No
hypothesis on the center is needed: a component of `X` contained in the center has no counterpart in `X'`.)

Deviation from the paper (gap filled): "If the set of points of `D` is nowhere dense …, then we get a unique rational
application `f'` of `X'` to `Y` which is the composition `f ∘ h`" is stated without argument (p. 139). -/
@[blueprint "lem:0.5-blowup-preimage-dense"
  (statement := /-- Let $f\colon X'\to X$ be the monoidal transformation of an algebraic scheme $X$ with center $D$.
    Then the inverse image under $f$ of every open dense subset of $X$ is
    dense in $X'$; hence the composition $g\circ f$ of a rational application $g$ of $X$ with the rational application
    to which $f$ belongs is defined (p.~139). \textbf{Gap in the paper filled.} The paper states the existence of the
    composition without argument. -/)
  (proof := /-- $f$ is an isomorphism off $D$ (\cref{compat:blowup-local-iso-open}), so the image of a non-empty open
    subset of $X'-f^{-1}(D)$ is a non-empty open subset of $X-D$ and meets the open dense set $V$; and $X'-f^{-1}(D)$
    is dense because the exceptional subscheme is defined by an invertible sheaf of ideals, hence nowhere dense. -/)
  (latexEnv := "lemma")]
theorem preimageDense_f (t : MonoidalTransformation X B) [IsAlgebraicScheme t.X'] :
    t.f.PreimageDense := by
  intro V hV
  rw [dense_iff_inter_open]
  intro W hW hWne
  let U := complOpens B
  have hOI : IsOpenImmersion ((t.f ⁻¹ᵁ U).ι ≫ t.f) := by
    have h1 : (t.f ⁻¹ᵁ U).ι ≫ t.f = (t.f ∣_ U) ≫ U.ι := (morphismRestrict_ι t.f U).symm
    have := t.isIso_morphismRestrict_complOpens
    rw [h1]
    infer_instance
  -- the open set `W` is not contained in the exceptional subscheme
  have hE : interior (t.f.base ⁻¹' B.pts) = ∅ := by
    rw [← pts_exceptional]
    exact interior_pts_exceptional t
  obtain ⟨w, hwW, hwB⟩ : ∃ w ∈ W, t.f.base w ∉ B.pts := by
    by_contra hcon
    push Not at hcon
    have hsub : (W : Set t.X') ⊆ interior (t.f.base ⁻¹' B.pts) := interior_maximal hcon hW
    rw [hE] at hsub
    obtain ⟨y, hy⟩ := hWne
    exact hsub hy
  have hwU : w ∈ t.f ⁻¹ᵁ U := hwB
  -- the image of `W ∩ f⁻¹(U)` under the open immersion `f⁻¹(U) → X` is open and non-empty
  let S : Set ↥(t.f ⁻¹ᵁ U) := Subtype.val ⁻¹' W
  have hSopen : IsOpen S := hW.preimage continuous_subtype_val
  have himg : IsOpen (((t.f ⁻¹ᵁ U).ι ≫ t.f).base '' S) :=
    ((t.f ⁻¹ᵁ U).ι ≫ t.f).isOpenEmbedding.isOpenMap S hSopen
  obtain ⟨z, ⟨s, hsS, rfl⟩, hzV⟩ :=
    (dense_iff_inter_open.mp hV) _ himg ⟨_, ⟨⟨w, hwU⟩, hwW, rfl⟩⟩
  exact ⟨s.1, hsS, hzV⟩

end MonoidalTransformation

end Hironaka
