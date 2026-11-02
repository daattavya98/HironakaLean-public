/-
Copyright (c) 2026 Daattavya Aggarwal, Minhyong Kim, Oisin Kim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daattavya Aggarwal, Minhyong Kim, Oisin Kim
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Restrict
public import Architect
public import Hironaka.Ch0.RationalApplication
public import Hironaka.Compat.FunctionFieldPair

/-!
# The rational application of two proper pairs is proper (Ch. 0 §5, pp. 139, 144)

> We say that a rational application `f` of `X` to `Y` is *proper*, if there exists an algebraic subscheme (or analytic
> subspace) `T` of the product `X × Y` (either in `Al/B` or in `An/K`) and also a morphism `f : X | U → Y` belonging to the
> class `f` such that the projections `p₁` and `p₂` of `X × Y` to `X` and `Y` induce proper morphisms of `T`, and that `p₁`
> induces an isomorphism of `T | p₁⁻¹(U)` to `X | U` while `p₂` induces the composition of this isomorphism and the
> morphism `f : X | U → Y`.  (pp. 138–139)

> The assumption that `f` is proper may be replaced by the weaker one that the projection of `X × Y` to `X` induces a
> proper morphism of the graph of `f` to `X`.  For instance, the latter is satisfied (but not in general the former) by an
> arbitrary rational application of `X` into a proper `B`-scheme (resp. a compact analytic `K`-space) `Y`.  (p. 140)

Consequence (1) (p. 144) applies Question (E) to the rational application of two pairs of `𝔐(L/B)` without saying that it is
proper; the paper asserts (p. 140) only the weaker statement for `Y` proper.  Here the properness in the sense of p. 139 is
proved for two proper pairs: `T` is the scheme-theoretic image of the graph of a `B`-morphism representing the rational
application on its domain `U` (a closed subscheme of `X ×_B Y`; the graph map `U → X ×_B Y` is an immersion, a closed
immersion into `fst⁻¹(U)` since `Y` is separated over `B`).  Both projections of `T` are proper because `T` is a closed
subscheme of `X ×_B Y` and `X`, `Y` are proper over `B`; over `U`, `T` is the graph: the graph map is an open immersion
onto `T ∩ fst⁻¹(U)`.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace Scheme

universe u

namespace Hironaka

section GraphClosure

variable {S X Y : Scheme.{u}} (pX : X ⟶ S) (pY : Y ⟶ S) (U : X.Opens) (h : U.toScheme ⟶ Y)
  (hh : U.ι ≫ pX = h ≫ pY)

/-- The graph morphism `U ⟶ X ×_S Y` of a morphism `h : U ⟶ Y` over `S`. -/
noncomputable def graphMap : U.toScheme ⟶ pullback pX pY := pullback.lift U.ι h hh

/-- The graph morphism followed by the first projection is the inclusion of `U`. -/
@[simp, reassoc] theorem graphMap_fst : graphMap pX pY U h hh ≫ pullback.fst pX pY = U.ι :=
  pullback.lift_fst _ _ _

/-- The graph morphism followed by the second projection is `h`. -/
@[simp, reassoc] theorem graphMap_snd : graphMap pX pY U h hh ≫ pullback.snd pX pY = h :=
  pullback.lift_snd _ _ _

/-- The open set `fst⁻¹(U)` of `X ×_S Y`. -/
noncomputable abbrev graphOpen : (pullback pX pY).Opens := pullback.fst pX pY ⁻¹ᵁ U

theorem graphMap_mem (u : U.toScheme) : graphMap pX pY U h hh u ∈ graphOpen pX pY U := by
  show (pullback.fst pX pY) (graphMap pX pY U h hh u) ∈ (U : Set X)
  rw [← Scheme.Hom.comp_apply, graphMap_fst]
  exact u.2

variable [IsSeparated pY] [QuasiCompact U.ι]

/-- The graph morphism, with target the open set `fst⁻¹(U)`. -/
noncomputable def graphMapOpen : U.toScheme ⟶ (graphOpen pX pY U).toScheme :=
  IsOpenImmersion.lift (graphOpen pX pY U).ι (graphMap pX pY U h hh) (by
    rintro _ ⟨u, rfl⟩; simpa using graphMap_mem pX pY U h hh u)

omit [IsSeparated pY] [QuasiCompact U.ι] in
@[simp, reassoc] theorem graphMapOpen_ι :
    graphMapOpen pX pY U h hh ≫ (graphOpen pX pY U).ι = graphMap pX pY U h hh :=
  IsOpenImmersion.lift_fac _ _ _

/-- The graph morphism into `fst⁻¹(U)` is a closed immersion (a section of a separated morphism). -/
instance : IsClosedImmersion (graphMapOpen pX pY U h hh) := by
  have h1 : graphMapOpen pX pY U h hh ≫ (pullback.fst pX pY ∣_ U) = 𝟙 _ := by
    rw [← cancel_mono U.ι, Category.assoc, morphismRestrict_ι, graphMapOpen_ι_assoc, graphMap_fst,
      Category.id_comp]
  have : IsClosedImmersion (graphMapOpen pX pY U h hh ≫ (pullback.fst pX pY ∣_ U)) := by
    rw [h1]; infer_instance
  exact IsClosedImmersion.of_comp _ (pullback.fst pX pY ∣_ U)

/-- The graph morphism is an immersion (it is a section of `fst` over the open immersion `U.ι`). -/
instance : IsImmersion (graphMap pX pY U h hh) := by
  have : IsImmersion (graphMap pX pY U h hh ≫ pullback.fst pX pY) := by
    rw [graphMap_fst]; infer_instance
  exact IsImmersion.of_comp _ (pullback.fst pX pY)

/-- The graph morphism is quasi-compact. -/
instance : QuasiCompact (graphMap pX pY U h hh) := by
  have : QuasiCompact (graphMap pX pY U h hh ≫ pullback.fst pX pY) := by
    rw [graphMap_fst]; infer_instance
  exact QuasiCompact.of_comp _ (pullback.fst pX pY)

omit [QuasiCompact U.ι] in
/-- The graph is closed in `fst⁻¹(U)`: a point of `fst⁻¹(U)` in the closure of the range of the graph is in the range
(`fst⁻¹(U) ⊆ coborder (range Γ)`, as `X ×_S Y → X` is separated). -/
theorem mem_range_graphMap_of_mem_closure {x : ↥(pullback pX pY)} (hx : x ∈ graphOpen pX pY U)
    (hcl : x ∈ closure (Set.range (graphMap pX pY U h hh))) : x ∈ Set.range (graphMap pX pY U h hh) := by
  have hemb := (graphOpen pX pY U).ι.isOpenEmbedding.isEmbedding
  have hrange : Set.range (graphMap pX pY U h hh) =
      (graphOpen pX pY U).ι '' Set.range (graphMapOpen pX pY U h hh) := by
    rw [← Set.range_comp, ← TopCat.coe_comp, ← Scheme.Hom.comp_base, graphMapOpen_ι]
  have hx' : (⟨x, hx⟩ : (graphOpen pX pY U).toScheme) ∈ closure (Set.range (graphMapOpen pX pY U h hh)) := by
    rw [hemb.closure_eq_preimage_closure_image, ← hrange]
    exact hcl
  rw [(graphMapOpen pX pY U h hh).isClosedEmbedding.isClosed_range.closure_eq] at hx'
  obtain ⟨u, hu⟩ := hx'
  exact ⟨u, by rw [← graphMapOpen_ι, Scheme.Hom.comp_apply, hu]; rfl⟩

/-- The scheme-theoretic image of the graph, restricted over `U`, is an isomorphism onto `U`. -/
theorem isIso_restrict_graphImage :
    IsIso (((graphMap pX pY U h hh).imageι ≫ pullback.fst pX pY) ∣_ U) ∧
      (((graphMap pX pY U h hh).imageι ≫ pullback.fst pX pY) ∣_ U) ≫ h =
        (((graphMap pX pY U h hh).imageι ≫ pullback.fst pX pY) ⁻¹ᵁ U).ι ≫
          (graphMap pX pY U h hh).imageι ≫ pullback.snd pX pY := by
  set Γ := graphMap pX pY U h hh with hΓ
  set TV := (Γ.imageι ≫ pullback.fst pX pY) ⁻¹ᵁ U with hTV
  have hsub : Set.range Γ.toImage ⊆ (TV : Set Γ.image) := by
    rintro _ ⟨u, rfl⟩
    show (Γ.imageι ≫ pullback.fst pX pY) (Γ.toImage u) ∈ (U : Set X)
    rw [← Scheme.Hom.comp_apply, Scheme.Hom.toImage_imageι_assoc, hΓ, graphMap_fst]
    exact u.2
  let a : U.toScheme ⟶ TV.toScheme := IsOpenImmersion.lift TV.ι Γ.toImage (by simpa using hsub)
  have ha : a ≫ TV.ι = Γ.toImage := IsOpenImmersion.lift_fac _ _ _
  have : IsOpenImmersion a := by
    have : IsOpenImmersion (a ≫ TV.ι) := by rw [ha]; infer_instance
    exact IsOpenImmersion.of_comp a TV.ι
  have hrange : a.opensRange = ⊤ := by
    refine top_le_iff.mp fun t _ => ?_
    have hz : Γ.imageι (TV.ι t) ∈ closure (Set.range Γ) := by
      rw [← Scheme.Hom.support_ker, ← Scheme.IdealSheafData.range_subschemeι]
      exact ⟨_, rfl⟩
    have hV : Γ.imageι (TV.ι t) ∈ graphOpen pX pY U := t.2
    obtain ⟨u, hu⟩ := mem_range_graphMap_of_mem_closure pX pY U h hh hV hz
    have h1 : Γ.imageι (Γ.toImage u) = Γ.imageι (TV.ι t) := by
      rw [← Scheme.Hom.comp_apply, Scheme.Hom.toImage_imageι]; exact hu
    have h2 : Γ.toImage u = TV.ι t := Γ.imageι.isEmbedding.injective h1
    refine ⟨u, ?_⟩
    apply TV.ι.isOpenEmbedding.isEmbedding.injective
    rw [← Scheme.Hom.comp_apply, ha]; exact h2
  have := isIso_of_isOpenImmersion_of_opensRange_eq_top a hrange
  have h3 : a ≫ ((Γ.imageι ≫ pullback.fst pX pY) ∣_ U) = 𝟙 _ := by
    rw [← cancel_mono U.ι, Category.assoc, morphismRestrict_ι, reassoc_of% ha,
      Scheme.Hom.toImage_imageι_assoc, hΓ, graphMap_fst, Category.id_comp]
  rw [← IsIso.inv_eq_of_hom_inv_id h3]
  refine ⟨inferInstance, ?_⟩
  rw [IsIso.inv_comp_eq, ← Category.assoc, ← Category.assoc, ha, Scheme.Hom.toImage_imageι, hΓ, graphMap_snd]

end GraphClosure

namespace FunctionFieldPair

variable {B L : Type u} [Field B] [Field L] [Algebra B L]

/-- **The rational application of two pairs of `𝔐(L/B)` is proper in the sense of p. 139.**

Deviation from the paper (gap filled): used tacitly by the paper, which applies Question (E) to this rational application
in (1) (p. 144) and asserts (p. 140) only the weaker statement (the graph is proper over `X`) for `Y` proper; proved here.
The subscheme `T` is the scheme-theoretic image `Γ.ker` of the graph `Γ : U → X ×_B Y` of a `B`-morphism representing the
rational application on its domain `U`. -/
@[blueprint "lem:0.5-ratapp-is-proper"
  (statement := /-- Let $(X_1,\theta_1)$, $(X_2,\theta_2)\in\mathfrak M(\mathbf L/\mathbf B)$. Then the rational
    application of $(X_1,\theta_1)$ to $(X_2,\theta_2)$ is proper in the sense of p.~139. (Used tacitly in (1), p.~144;
    compare p.~140: the projection of the graph of a rational application of $X$ into a proper $\mathbf B$-scheme to $X$ is
    proper.) -/)
  (proof := /-- Represent the rational application by a $\mathbf B$-morphism $g\colon U\to X_2$ on a dense open set $U$ and
    let $T$ be the scheme-theoretic image of its graph $\Gamma\colon U\to X_1\times_{\mathbf B}X_2$, a closed subscheme.
    Both projections of $T$ are proper, being closed immersions followed by the projections of $X_1\times_{\mathbf B}X_2$
    (base changes of the proper structure morphisms). The graph is an immersion, a closed immersion into
    $p_1^{-1}(U)$ ($X_2$ is separated over $\mathbf B$), so the scheme-theoretic image $T$ meets $p_1^{-1}(U)$ in the graph:
    $\Gamma$ factors through an open immersion $U\to T$ whose image is $T\cap p_1^{-1}(U)$. Hence $p_1$ induces an
    isomorphism $T|p_1^{-1}(U)\to U$ whose inverse followed by $p_2$ is $g$.
    \textbf{Gap in the paper filled.} Used tacitly. -/)
  (latexEnv := "lemma")]
theorem isProperApplication_ratApp (P₁ P₂ : FunctionFieldPair B L) (hP₁ : P₁.IsProper) (hP₂ : P₂.IsProper) :
    (P₁.ratApp P₂).IsProperApplication P₁.p P₂.p := by
  have : AlgebraicGeometry.IsProper P₁.p := hP₁
  have : AlgebraicGeometry.IsProper P₂.p := hP₂
  have : IsLocallyNoetherian P₁.X := LocallyOfFiniteType.isLocallyNoetherian P₁.p
  have : CompactSpace P₁.X := QuasiCompact.compactSpace_of_compactSpace P₁.p
  have : IsNoetherian P₁.X := ⟨⟩
  have hnoeth : NoetherianSpace P₁.X := IsNoetherian.noetherianSpace
  -- a `B`-morphism representing the rational application on its domain
  let _ : P₁.X.Over (Spec (CommRingCat.of B)) := ⟨P₁.p⟩
  let _ : P₂.X.Over (Spec (CommRingCat.of B)) := ⟨P₂.p⟩
  have hover : (P₁.ratApp P₂).IsOver (Spec (CommRingCat.of B)) :=
    RationalMap.isOver_iff.mpr (P₁.ratApp_compHom P₂)
  obtain ⟨g, hg, hgr⟩ := RationalMap.exists_partialMap_over (Spec (CommRingCat.of B)) (P₁.ratApp P₂)
  have hgh : g.domain.ι ≫ P₁.p = g.hom ≫ P₂.p := (PartialMap.isOver_iff.mp hg).symm
  have : QuasiCompact g.domain.ι := by
    have : NoetherianSpace (g.domain : Set P₁.X) := inferInstance
    exact ⟨fun _ _ _ => @NoetherianSpace.isCompact _ _ (by exact this) _⟩
  obtain ⟨hiso, hsnd⟩ := isIso_restrict_graphImage P₁.p P₂.p g.domain g.hom hgh
  refine ⟨g, (graphMap P₁.p P₂.p g.domain g.hom hgh).ker, hgr, ?_, ?_, hiso, hsnd⟩
  · exact inferInstanceAs (AlgebraicGeometry.IsProper
      ((graphMap P₁.p P₂.p g.domain g.hom hgh).imageι ≫ pullback.fst P₁.p P₂.p))
  · exact inferInstanceAs (AlgebraicGeometry.IsProper
      ((graphMap P₁.p P₂.p g.domain g.hom hgh).imageι ≫ pullback.snd P₁.p P₂.p))

end FunctionFieldPair

end Hironaka
