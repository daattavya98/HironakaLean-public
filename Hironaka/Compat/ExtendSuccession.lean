/-
Copyright (c) 2026 Daattavya Aggarwal, Minhyong Kim, Oisin Kim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daattavya Aggarwal, Minhyong Kim, Oisin Kim
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Architect
public import Hironaka.Compat.LocalizeSuccession

/-!
# Extension of successions from an open subscheme (Ch. IV §2, p. 291, step 7)

> Therefore the center of any permissible monoidal transformation for `(ℜ^{N*,n*}_I, E_1 − F)` is
> contained in `W_* − Ū` and closed not only in `W_* − F` but also in `W_*`. It follows that any
> permissible monoidal transformation for `(ℜ^{N*,n*}_I, E_1 − F)` is canonically induced by a
> permissible monoidal transformation for `(ℜ, U)`, and that this does not affect the properties
> (1), (2), (3)** and (4). (p. 291)

General machinery, for an arbitrary flat preimmersion `j : Z → Y` (in particular the open
immersion `X − F → X`), not mentioning the preparation setting:

* `isAlgebraicScheme_of_isOpenImmersion`, `exists_isAmbient_of_isOpenImmersion`: the restriction
  of an ambient scheme to a non-empty open subscheme is ambient of dimension `N* ≤ N`; the
  restriction of a datum is `DatumI.Raw.pullback` (a datum: `isDatum_pullback`; dimensions:
  `LocSucc.dim_totalTransform_le`, `LocSucc.dim_add_one_le_of_pts_ne_univ`).
* `MonoidalTransformation.exists_extend_step`: one monoidal transformation of `Z` with reduced
  center with closed image is induced by the monoidal transformation of `Y` whose center is the
  closure of the image (`FlatPreimm.closureLift`), via `MonoidalTransformation.exists_lift`.
* `DatumI.Raw.isPermissible_of_isPermissible_pullback`: the center is permissible for `ℜ` as soon
  as it is permissible for the restriction `ℜ_Z`.
* `MonoidalSuccession.exists_extension`: the whole succession, with the compatibilities with
  strict transforms, the transform of data and (closed/open) permissibility.
* `MonoidalSuccession.centersClosedIn_of_isPermissibleIClosed`: its hypothesis from
  permissibility for `(ℜ, F)`.

Deviation from the paper (gap filled): the paper says that a permissible monoidal transformation
for the restricted datum "is canonically induced" by one for `(ℜ, U)` and "does not affect"
the properties; Lean constructs the extension (center: reduced closure of the image;
`exists_lift`), proves that the transforms of data and strict transforms restrict to the given
ones, and that permissibility transfers.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

namespace Hironaka

universe u

namespace MonoidalSuccession

variable {Z Z' Y : Scheme.{u}}

/-- The centers of the succession `s` are reduced and their images under `q`, composed with the
earlier monoidal transformations, lie in `C`. -/
def CentersClosedIn : {Z Z' : Scheme.{u}} → MonoidalSuccession Z Z' → (Z ⟶ Y) → Set Y → Prop
  | _, _, nil _, _, _ => True
  | _, _, cons B t rest, q, C => B.IsReduced ∧ q.base '' B.pts ⊆ C ∧ rest.CentersClosedIn (t.f ≫ q) C

end MonoidalSuccession

namespace MonoidalTransformation

variable {Z Y : Scheme.{u}}

/-- One step of the extension of a succession from `Z` to `Y` along a flat preimmersion
`j : Z → Y`: a monoidal transformation `ts` of `Z` whose reduced center `B` has closed image in
`Y` is induced by a monoidal transformation of `Y` with center the closure of `j(B)`. -/
theorem exists_extend_step [Hironaka.Cited.MonoidalTransformationExistsIsProper.{u}] (j : Z ⟶ Y) [Flat j] [IsPreimmersion j] {B : Subscheme Z}
    (hB : B.IsReduced) (hcl : IsClosed (j.base '' B.pts)) (ts : MonoidalTransformation Z B) :
    ∃ (BY : Subscheme Y) (tY : MonoidalTransformation Y BY) (j' : ts.X' ⟶ tY.X'),
      Flat j' ∧ IsPreimmersion j' ∧ BY.IsReduced ∧ BY.pts = j.base '' B.pts ∧
      Subscheme.totalTransform j BY = B ∧ j' ≫ tY.f = ts.f ≫ j ∧
      Set.range j'.base = tY.f.base ⁻¹' Set.range j.base ∧
      Subscheme.totalTransform j' tY.exceptional = ts.exceptional ∧
      ∀ V, Subscheme.totalTransform j' (Subscheme.strictTransform tY V) =
        Subscheme.strictTransform ts (Subscheme.totalTransform j V) := by
  obtain ⟨tY, -⟩ := MonoidalTransformation.exists_isProper Y (FlatPreimm.closureLift j B)
  obtain ⟨j', h1, h2, h3, h4, h5, h6⟩ := MonoidalTransformation.exists_lift tY j
    (FlatPreimm.totalTransform_closureLift j B hB) ts
  exact ⟨_, tY, j', h1, h2, FlatPreimm.closureLift_isReduced j B,
    by rw [FlatPreimm.pts_closureLift, hcl.closure_eq], FlatPreimm.totalTransform_closureLift j B hB,
    h3, h4, h5, h6⟩

end MonoidalTransformation

namespace DatumI.Raw

variable {Z Y : Scheme.{u}}

/-- A reduced subscheme `BY` of `Y` lying in the range of a flat preimmersion `j : Z → Y` and
whose total transform is a center `B` of `Z` is a center. -/
theorem isCenter_of_totalTransform_eq (j : Z ⟶ Y) [Flat j] [IsPreimmersion j]
    {BY : Subscheme Y} {B : Subscheme Z} (htt : Subscheme.totalTransform j BY = B)
    (hpts : BY.pts ⊆ Set.range j.base) (hB : B.IsCenter) : BY.IsCenter := by
  have hBYpts : BY.pts = j.base '' B.pts := by
    rw [← htt, FlatPreimm.pts_totalTransform, Set.image_preimage_eq_of_subset hpts]
  rcases hB with hB | ⟨hns, hirr⟩
  · left
    refine Subscheme.eq_empty_of_pts_eq_empty ?_
    rw [hBYpts, hB, Subscheme.pts_empty, Set.image_empty]
  · right
    refine ⟨fun y => ?_, ?_⟩
    · obtain ⟨z, hz⟩ := hpts (Subscheme.mem_pts_ι BY y)
      have hzB : z ∈ B.pts := by
        rw [← htt, FlatPreimm.pts_totalTransform]
        show j.base z ∈ BY.pts
        rw [hz]; exact Subscheme.mem_pts_ι BY y
      have hS : B.IsSimpleAt z := ⟨hzB, Subscheme.isRegular_stalk_quot B hns hzB⟩
      rw [← htt] at hS
      have h2 := (FlatPreimm.isSimpleAt_totalTransform_iff j BY z).mp hS
      rw [hz] at h2
      obtain ⟨e⟩ := nonempty_stalk_quot_equiv BY y
      have : IsRegularLocalRing (Y.presheaf.stalk (BY.ι y) ⧸ BY.stalkIdeal (BY.ι y)) := h2.2
      exact IsRegularLocalRing.of_ringEquiv e
    · refine Subscheme.isIrreducible_of_pts _ ?_
      rw [hBYpts]
      exact (Subscheme.isIrreducible_pts B hirr).image _ j.base.hom.continuous.continuousOn

/-- Permissibility descends from the restriction to an open piece to the whole scheme (p. 291,
step 7: the center of a permissible monoidal transformation of the datum on `X − F`, closed in
`X`, is the center of a permissible monoidal transformation of the datum on `X`).

Deviation from the paper (gap filled): the paper asserts this ("canonically induced by a
permissible monoidal transformation", p. 291) without argument. -/
@[blueprint "prop:IV.2-5-permissible"
  (statement := /-- Let $j\colon Z\to Y$ be a flat preimmersion, $\mathfrak R$ a resolution
    datum on $Y$, $B_Y$ a reduced subscheme of $Y$ contained in $j(Z)$ whose pull-back $B$ is a
    permissible center for the restriction $\mathfrak R_Z$. Then $B_Y$ is a permissible center
    for $\mathfrak R$. -/)
  (proof := /-- $B_Y=\overline{j(B)}\subseteq j(Z)$ is irreducible and non-singular because $j$
    induces isomorphisms of local rings; $\mathfrak R\cdot B_Y$ is a datum since $B_Y$ is a reduced
    subscheme of $W$; and it is resolved at $j(z)$, $z\in B$, because $\mathfrak R_Z\cdot B$ is
    resolved at $z$ and resolvedness is local (\texttt{resolvedAt\_pullback\_iff}).

    \textbf{Deviation from the paper (gap filled).} The paper asserts that the permissible
    monoidal transformation is ``canonically induced'' (p.~291) without these verifications. -/)
  (latexEnv := "lemma")]
theorem isPermissible_of_isPermissible_pullback (j : Z ⟶ Y) [Flat j] [IsPreimmersion j]
    {ℜ : Raw Y} (hℜ : ℜ.IsDatum) {BY : Subscheme Y} {B : Subscheme Z} (hBY : BY.IsReduced)
    (htt : Subscheme.totalTransform j BY = B) (hpts : BY.pts ⊆ Set.range j.base)
    (hperm : (ℜ.pullback j).IsPermissible B) : ℜ.IsPermissible BY := by
  have hBYpts : BY.pts = j.base '' B.pts := by
    rw [← htt, FlatPreimm.pts_totalTransform, Set.image_preimage_eq_of_subset hpts]
  have hBW : BY.pts ⊆ ℜ.W.pts := by
    rw [hBYpts]
    rintro _ ⟨z, hz, rfl⟩
    have := hperm.pts_subset_W hz
    rwa [pullback_W, FlatPreimm.pts_totalTransform] at this
  have hD := isDatum_extendBy hℜ hBY hBW
  refine ⟨isCenter_of_totalTransform_eq j htt hpts hperm.1, hD, fun y hy => ?_⟩
  have hy' : y ∈ BY.pts := hy
  obtain ⟨z, hz, rfl⟩ : y ∈ j.base '' B.pts := hBYpts ▸ hy'
  rw [← resolvedAt_pullback_iff j _ hD.2.2.2.2, pullback_extendBy, htt]
  exact hperm.2.2 z hz

end DatumI.Raw

namespace MonoidalSuccession

variable {Z Z' Y Y₁ : Scheme.{u}}

theorem centersClosedIn_comp (s : MonoidalSuccession Z Z') :
    ∀ (q : Z ⟶ Y₁) (g : Y₁ ⟶ Y) (C : Set Y),
      s.CentersClosedIn (q ≫ g) C ↔ s.CentersClosedIn q (g.base ⁻¹' C) := by
  induction s with
  | nil Z => intro q g C; exact Iff.rfl
  | cons B t rest ih =>
    intro q g C
    show (B.IsReduced ∧ (q ≫ g).base '' B.pts ⊆ C ∧ rest.CentersClosedIn (t.f ≫ q ≫ g) C) ↔
      (B.IsReduced ∧ q.base '' B.pts ⊆ g.base ⁻¹' C ∧ rest.CentersClosedIn (t.f ≫ q) (g.base ⁻¹' C))
    rw [← Category.assoc, ih (t.f ≫ q) g C, Scheme.Hom.comp_base, TopCat.coe_comp,
      Set.image_comp, Set.image_subset_iff]

/-- **Extension of a succession** (p. 291, step 7, "canonically induced"): a succession of `Z`
whose centers are reduced and have images in a closed subset `C` of `Y` contained in the range of
a flat preimmersion `j : Z → Y` is induced by a succession of `Y` (with the closures of the images
of the centers as centers), compatibly with `j`, composites, strict transforms and transforms of
type I data; and it is permissible for a datum `ℜ` of `Y` (with closed restriction `F`, resp. open
restriction `U`) as soon as the given succession is permissible for the restriction `ℜ_Z` (with
`F_Z`, resp. `j⁻¹(U)`) (pp. 169, 276, 291).

Deviation from the paper (gap filled): "any permissible monoidal transformation for
`(ℜ^{N*,n*}_I, E_1 − F)` is canonically induced by a permissible monoidal transformation for
`(ℜ, U)`, and … this does not affect the properties" (p. 291) is proved by this construction. -/
@[blueprint "prop:IV.2-5-extension"
  (statement := /-- Let $j\colon Z\to Y$ be a flat preimmersion, $C\subseteq Y$ a closed subset
    contained in $j(Z)$, and $s$ a finite succession of monoidal transformations of $Z$ with
    reduced centers whose images in $Y$ lie in $C$. Then $s$ is induced by a succession $s_Y$ of
    $Y$ (centers: the closures of the images of the centers of $s$) and a flat preimmersion
    $j'\colon Z'\to Y'$ over $j$ with $j'(Z')=g^{-1}(j(Z))$, such that $j'^{-1}$ of strict
    transforms and of transforms of data are the strict transforms and transforms of the
    restrictions. If $s$ is permissible for the restriction $\mathfrak R_Z$ of a datum
    $\mathfrak R$ of $Y$ (with closed restriction $F_Z=j^{-1}F$, resp.\ open restriction
    $j^{-1}U$), then $s_Y$ is permissible for $\mathfrak R$ (with $F$, resp.\ $U$).
    (Used on p.~291, step 7.) -/)
  (proof := /-- Induction on the length of $s$. For one step, let $B$ be the (reduced) center of the
    first monoidal transformation $t_s$; $j(B)$ is closed in $Y$, being contained in the closed
    set $C\subseteq j(Z)$ (its closure meets $j(Z)$ exactly in $j(B)$). Let $B_Y$ be the reduced
    subscheme on $j(B)$, so $j^{-1}(B_Y)=B$, and $t_Y$ a monoidal transformation of $Y$ with
    center $B_Y$. By \cref{compat:blowup-flat-base-change} (\texttt{exists\_lift}) $j$ lifts to a
    flat preimmersion $j'\colon Z_1\to Y_1$ compatible with exceptional subschemes and strict
    transforms; $j'(Z_1)=f^{-1}(j(Z))$ contains $f^{-1}(C)$, which is closed, and one concludes
    by induction. For the permissibility, $B_Y$ is a center (non-singular and irreducible since
    $j$ preserves the local rings and $B_Y=\overline{j(B)}$), the datum $\mathfrak R\cdot B_Y$ is a
    datum (\texttt{isDatum\_extendBy}) and is resolved along $B_Y\subseteq j(Z)$ because it is so
    at the points of $B$ for the restriction (\texttt{resolvedAt\_pullback\_iff});
    the transform of $\mathfrak R$ is a datum (Remark~1, p.~169) and its restriction is the
    transform of $\mathfrak R_Z$.

    \textbf{Deviation from the paper (gap filled).} The paper says only that a permissible
    monoidal transformation for the restricted datum ``is canonically induced by a permissible
    monoidal transformation for $(\mathfrak R,U)$, and that this does not affect the properties''
    (p.~291). Lean constructs the induced succession and proves the compatibilities and the
    transfer of permissibility. -/)
  (proofUses := ["thm:monoidal-transformation-exists", "prop:IV.2-5-permissible"])
  (latexEnv := "proposition")]
theorem exists_extension [Hironaka.Cited.MonoidalTransformationExistsIsProper.{u}] (s : MonoidalSuccession Z Z') :
    ∀ {Y : Scheme.{u}} (j : Z ⟶ Y) [Flat j] [IsPreimmersion j] (C : Set Y), IsClosed C →
      C ⊆ Set.range j.base → s.CentersClosedIn j C →
      ∃ (Y' : Scheme.{u}) (sY : MonoidalSuccession Y Y') (j' : Z' ⟶ Y'), Flat j' ∧
        IsPreimmersion j' ∧ sY.length = s.length ∧ j' ≫ sY.composite = s.composite ≫ j ∧
        Set.range j'.base = sY.composite.base ⁻¹' Set.range j.base ∧
        (∀ V, Subscheme.totalTransform j' (sY.strictTransform V) =
          s.strictTransform (Subscheme.totalTransform j V)) ∧
        (∀ ℜ : DatumI.Raw Y, (sY.transformI ℜ).pullback j' = s.transformI (ℜ.pullback j)) ∧
        (IsAlgebraicScheme Y → Y.IsNonsingular → ∀ ℜ : DatumI.Raw Y, ℜ.IsDatum →
          (s.IsPermissibleI (ℜ.pullback j) → sY.IsPermissibleI ℜ) ∧
          (∀ F : Subscheme Y, s.IsPermissibleIClosed (ℜ.pullback j)
              (Subscheme.totalTransform j F) → sY.IsPermissibleIClosed ℜ F) ∧
          (∀ U : Set Y, s.IsPermissibleIOpen (ℜ.pullback j) (j.base ⁻¹' U) →
              sY.IsPermissibleIOpen ℜ U)) := by
  induction s with
  | nil Z =>
    intro Y j _ _ C _ _ _
    exact ⟨Y, nil Y, j, inferInstance, inferInstance, rfl, by simp, by simp, fun V => rfl,
      fun ℜ => rfl, fun _ _ ℜ _ => ⟨fun _ => trivial, fun _ _ => trivial, fun _ _ => trivial⟩⟩
  | cons B ts rest ih =>
    intro Y j _ _ C hC hCj hs
    obtain ⟨hBred, hBC, hrest⟩ := hs
    have hcl : IsClosed (j.base '' B.pts) := by
      have h1 : closure (j.base '' B.pts) ⊆ C := closure_minimal hBC hC
      have h2 := FlatPreimm.pts_closureLift_inter_range j B
      rw [FlatPreimm.pts_closureLift] at h2
      rw [← h2, Set.inter_eq_left.mpr (h1.trans hCj)]
      exact isClosed_closure
    obtain ⟨BY, tY, j', hfl, hpre, hBY, hpts, htt, hsq, hrange, hexc, hst⟩ :=
      MonoidalTransformation.exists_extend_step j hBred hcl ts
    obtain ⟨Y', sY, j'', hfl', hpre', hlen, hcomp, hrange', hst', htr, hperm⟩ :=
      ih j' (tY.f.base ⁻¹' C) (hC.preimage tY.f.continuous)
        (fun y hy => by rw [hrange]; exact hCj hy)
        ((centersClosedIn_comp rest j' tY.f C).mp (by rw [hsq]; exact hrest))
    refine ⟨Y', cons BY tY sY, j'', hfl', hpre', ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [length_cons, hlen]
    · rw [composite_cons, composite_cons, ← Category.assoc, hcomp, Category.assoc, hsq,
        Category.assoc]
    · rw [hrange', composite_cons, hrange]
      rfl
    · intro V
      rw [strictTransform_cons, strictTransform_cons, hst', hst]
    · intro ℜ
      rw [transformI_cons, transformI_cons, htr,
        DatumI.Raw.pullback_transform_of_lift tY j ts j' hexc hst]
    · intro hYa hYns ℜ hℜ
      have hrng : BY.pts ⊆ Set.range j.base := by
        rw [hpts]; rintro _ ⟨z, -, rfl⟩; exact ⟨z, rfl⟩
      have htr1 : (ℜ.transform tY).pullback j' = (ℜ.pullback j).transform ts :=
        DatumI.Raw.pullback_transform_of_lift tY j ts j' hexc hst ℜ
      -- the datum and ambient hypotheses for the next step, given permissibility of `BY`
      have key : ℜ.IsPermissible BY → IsAlgebraicScheme tY.X' ∧ tY.X'.IsNonsingular ∧
          (ℜ.transform tY).IsDatum := fun hp => by
        have := hYa
        exact ⟨tY.isAlgebraicScheme,
          (tY.isNonsingular_and_isNonsingular_exceptional hYns hp.1.isNonsingular).1,
          (DatumI.Raw.transform_isDatum hYns ℜ hℜ tY hp).1⟩
      refine ⟨fun hs => ?_, fun F hs => ?_, fun U hs => ?_⟩
      · have hp := DatumI.Raw.isPermissible_of_isPermissible_pullback j hℜ hBY htt hrng hs.1
        obtain ⟨h1, h2, h3⟩ := key hp
        refine ⟨hp, (hperm h1 h2 _ h3).1 ?_⟩
        rw [htr1]; exact hs.2
      · have hp := DatumI.Raw.isPermissible_of_isPermissible_pullback j hℜ hBY htt hrng hs.1.1
        obtain ⟨h1, h2, h3⟩ := key hp
        refine ⟨⟨hp, ?_⟩, (hperm h1 h2 _ h3).2.1 (Subscheme.strictTransform tY F) ?_⟩
        · rw [hpts]
          rintro _ ⟨z, hz, rfl⟩
          have := hs.1.2 hz
          rw [DatumI.Raw.pullback_W, FlatPreimm.pts_totalTransform,
            FlatPreimm.pts_totalTransform] at this
          exact this
        · rw [htr1, hst]; exact hs.2
      · have hp := DatumI.Raw.isPermissible_of_isPermissible_pullback j hℜ hBY htt hrng hs.1.1
        obtain ⟨h1, h2, h3⟩ := key hp
        refine ⟨⟨hp, ?_⟩, (hperm h1 h2 _ h3).2.2 (DatumI.Raw.transformOpen tY U) ?_⟩
        · rw [hpts]
          rintro _ ⟨z, hz, rfl⟩
          have := hs.1.2 hz
          rw [DatumI.Raw.pullback_W, FlatPreimm.pts_totalTransform] at this
          exact this
        · rw [htr1]
          have e : j'.base ⁻¹' DatumI.Raw.transformOpen tY U = DatumI.Raw.transformOpen ts
              (j.base ⁻¹' U) := by
            show j'.base ⁻¹' (tY.f.base ⁻¹' U) = ts.f.base ⁻¹' (j.base ⁻¹' U)
            have := congrArg (fun g : ts.X' ⟶ Y => g.base ⁻¹' U) hsq
            simpa [Scheme.Hom.comp_base, Set.preimage_comp] using this
          rw [e]; exact hs.2

end MonoidalSuccession

namespace MonoidalSuccession

variable {Z Z' Y : Scheme.{u}}

/-- The hypothesis of `exists_extension` for a succession permissible for `(ℜ, F)` (closed
restriction), in the form used on p. 291: "the center … is contained in `W_* − Ū` and closed
not only in `W_* − F` but also in `W_*`".  Every center of the succession is contained in
`W ∩ F` (transformed), so if `q(W ∩ F) ⊆ C` then the images of all the centers lie in `C`; the
centers are non-singular, hence reduced. -/
theorem centersClosedIn_of_isPermissibleIClosed {s : MonoidalSuccession Z Z'} :
    ∀ {ℜ : DatumI.Raw Z} {F : Subscheme Z} (_ : s.IsPermissibleIClosed ℜ F) (q : Z ⟶ Y)
      (C : Set Y), q.base '' (ℜ.W.pts ∩ F.pts) ⊆ C → s.CentersClosedIn q C := by
  induction s with
  | nil Z => intros; trivial
  | cons B t rest ih =>
    intro ℜ F hs q C hC
    obtain ⟨⟨hp, hBWF⟩, hrest⟩ := hs
    refine ⟨?_, (Set.image_mono hBWF).trans hC, ih hrest (t.f ≫ q) C ?_⟩
    · exact hp.1.isReduced
    · rintro _ ⟨z, ⟨hzW, hzF⟩, rfl⟩
      refine hC ⟨t.f.base z, ⟨?_, ?_⟩, rfl⟩
      · exact MonoidalTransformation.pts_strictTransform_subset t _ hzW
      · exact MonoidalTransformation.pts_strictTransform_subset t _ hzF

end MonoidalSuccession

section OpenRestriction

variable {V X : Scheme.{u}}

/-- An open subscheme of an algebraic scheme is algebraic (a noetherian space is
quasi-compact on every open subset). -/
theorem isAlgebraicScheme_of_isOpenImmersion (j : V ⟶ X) [IsOpenImmersion j] [IsAlgebraicScheme X] :
    IsAlgebraicScheme V := by
  obtain ⟨S, i1, i2, i3, p, hp1, hp2⟩ := IsAlgebraicScheme.exists_base (X := X)
  have := IsAlgebraicScheme.noetherianSpace X
  have : NoetherianSpace V := j.isOpenEmbedding.isInducing.noetherianSpace
  have : CompactSpace V := inferInstance
  have : QuasiCompact (j ≫ p) := inferInstance
  exact ⟨⟨S, i1, i2, i3, j ≫ p, inferInstance, this⟩⟩

/-- The restriction of an ambient scheme to a non-empty open subscheme is an ambient scheme of
dimension at most that of the original (p. 291, step 7: `X − F` is a non-singular irreducible
algebraic scheme with `N* = dim (X − F) ≤ N`). -/
theorem exists_isAmbient_of_isOpenImmersion {N : ℕ} (hX : IsAmbient X N) (j : V ⟶ X)
    [IsOpenImmersion j] [Nonempty V] : ∃ N' ≤ N, IsAmbient V N' := by
  obtain ⟨hXa, hXns, hXirr, hXdim⟩ := hX
  have := hXirr
  obtain ⟨z⟩ := ‹Nonempty V›
  have hdimle : V.dim ≤ (N : WithBot ℕ∞) := by
    rw [← hXdim]
    exact LocSucc.dim_le_of_forall j fun z => LocSucc.dimAt_le_dim _
  have hne : V.dim ≠ ⊥ := by
    intro hb
    have h1 : V.dimAt z ≤ V.dim := LocSucc.dimAt_le_dim z
    have h2 : (0 : WithBot ℕ∞) ≤ V.dimAt z := ringKrullDim_nonneg_of_nontrivial
    rw [hb] at h1
    exact absurd (h2.trans h1) (by simp)
  obtain ⟨m, hm, hmN⟩ := LocSucc.exists_nat_of_le hne hdimle
  have := hXa
  exact ⟨m, hmN, isAlgebraicScheme_of_isOpenImmersion j, LocSucc.isNonsingular j hXns,
    irreducibleSpace_of_flat_preimmersion j, hm⟩

end OpenRestriction

end Hironaka
