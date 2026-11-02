/-
Copyright (c) 2026 Daattavya Aggarwal, Minhyong Kim, Oisin Kim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daattavya Aggarwal, Minhyong Kim, Oisin Kim
-/
module

public import Mathlib.AlgebraicGeometry.Restrict
public import Architect
public import Hironaka.Compat.BlowupBaseChange
public import Hironaka.Statements

/-!
# The monoidal transformation is an isomorphism off the center (Ch. I §1, p. 167)

> Let `g : X' → X` be the monoidal transformation with center `B` … (the morphism `g` (which induces an
> isomorphism of `X' − g⁻¹(B)` to `X − B`)).  (p. 167)

The printed claim is stated and proved here for every scheme `X` and every subscheme `B`, with no
regularity hypothesis, and beyond stalks: the restriction `f⁻¹(X − B) → X − B` of `f` is an isomorphism of
schemes, and hence the stalk maps of `f` at the points off `f⁻¹(B)` are bijective.  (The earlier node
`MonoidalTransformation.bijective_stalkMap_of_notMem` in `Hironaka/Compat/BlowupCharts.lean` assumes
`O_{X,f(y)}` regular, an artefact of its proof through monoidal transforms of regular local rings.)

Deviation from the paper (gap filled): the paper gives no proof.  Proof: the base change of `f` to the open
`U = X − B` is a monoidal transformation of `U` with center `B ∩ U = ∅`, hence an isomorphism
(`MonoidalTransformation.isIso_of_eq_empty`, `compat:blowup-flat-base-change`).
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace Hironaka

universe u

namespace MonoidalTransformation

variable {X : Scheme.{u}} {B : Subscheme X}


/-- p. 167: "the morphism `g` (which induces an isomorphism of `X' − g⁻¹(B)` to `X − B`)": the restriction of
a monoidal transformation `f : X' → X` to `f⁻¹(X − B) = X' − f⁻¹(B)` is an isomorphism onto `X − B`. -/
@[blueprint "compat:blowup-local-iso-open"
  (statement := /-- Let $X$ be a scheme, $B$ a subscheme and $f\colon X'\to X$ the monoidal transformation
    with center $B$. Then $f$ induces an isomorphism of $X'-f^{-1}(B)$ onto $X-B$. (p.~167.)
    \textbf{Deviation from the paper (statement modified).} None; the earlier node
    \cref{compat:blowup-local-iso} proves the bijectivity of the stalk maps of $f$ off $f^{-1}(B)$ under an
    extra regularity hypothesis, which is not needed here. \textbf{Gap in the paper filled.} The paper gives
    no proof. -/)
  (proof := /-- The base change of $f$ to $U=X-B$ is a monoidal transformation of $U$ whose center
    $B\cap U$ is empty, hence an isomorphism (\cref{lem:monoidal-transformation-empty-center},
    \cref{compat:blowup-flat-base-change}); it is $f$ restricted over $U$. -/)
  (latexEnv := "lemma")]
theorem isIso_morphismRestrict_complOpens (t : MonoidalTransformation X B) :
    IsIso (t.f ∣_ complOpens B) := by
  have hBU : Subscheme.totalTransform (complOpens B).ι B = Subscheme.empty := by
    refine Subscheme.eq_empty_of_pts_eq_empty ?_
    rw [FlatPreimm.pts_totalTransform]
    ext z
    simp only [Set.mem_preimage, Set.mem_empty_iff_false, iff_false]
    exact ((complOpens B).ι_apply z ▸ z.2 : _)
  have hiso : IsIso (pullback.snd t.f (complOpens B).ι) :=
    isIso_of_eq_empty (t.baseChange (complOpens B).ι) hBU
  show IsIso ((pullbackRestrictIsoRestrict t.f (complOpens B)).inv ≫ pullback.snd _ _)
  infer_instance

/-- p. 167, on stalks and without regularity: for every point `y` of `X'` with `f(y) ∉ B`, the stalk map
`O_{X,f(y)} → O_{X',y}` is bijective (the stalk form of `isIso_morphismRestrict_complOpens`; the earlier
`bijective_stalkMap_of_notMem` needs `O_{X,f(y)}` regular).

Deviation from the paper (gap filled): the paper gives no proof. -/
@[blueprint "compat:blowup-local-iso-stalk"
  (statement := /-- Let $f\colon X'\to X$ be the monoidal transformation with center $B$ and $y\in X'$
    with $f(y)\notin B$. Then $\mathcal O_{X,f(y)}\to\mathcal O_{X',y}$ is an isomorphism, for every scheme
    $X$ (no regularity). (p.~167, on stalks.) -/)
  (proof := /-- $f^{-1}(X-B)\to X-B$ is an isomorphism (\cref{compat:blowup-local-iso-open}), and
    $f^{-1}(X-B)\to X'$, $X-B\to X$ are open immersions, which induce isomorphisms on stalks. -/)
  (latexEnv := "lemma")]
theorem bijective_stalkMap_of_notMem_pts (t : MonoidalTransformation X B) (y : t.X') (hy : t.f y ∉ B.pts) :
    Function.Bijective (t.f.stalkMap y) := by
  have hiso := t.isIso_morphismRestrict_complOpens
  have hopen : IsOpenImmersion ((t.f ⁻¹ᵁ complOpens B).ι ≫ t.f) := by
    rw [← morphismRestrict_ι t.f (complOpens B)]
    infer_instance
  let z : ((t.f ⁻¹ᵁ complOpens B : t.X'.Opens) : Scheme.{u}) := ⟨y, hy⟩
  have h1 : IsIso (((t.f ⁻¹ᵁ complOpens B).ι ≫ t.f).stalkMap z) := inferInstance
  rw [Scheme.Hom.stalkMap_comp] at h1
  have h2 : IsIso (t.f.stalkMap y) :=
    @IsIso.of_isIso_comp_right _ _ _ _ _ (t.f.stalkMap ((t.f ⁻¹ᵁ complOpens B).ι z))
      ((t.f ⁻¹ᵁ complOpens B).ι.stalkMap z) inferInstance h1
  exact ConcreteCategory.bijective_of_isIso (t.f.stalkMap y)

end MonoidalTransformation

end Hironaka
