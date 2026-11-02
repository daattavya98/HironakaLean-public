/-
Copyright (c) 2026 Daattavya Aggarwal, Minhyong Kim, Oisin Kim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daattavya Aggarwal, Minhyong Kim, Oisin Kim
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Architect
public import Hironaka.Compat.BlowupExceptional
public import Hironaka.Compat.ExtendSuccession

/-!
# The strict transform meets the exceptional divisor in an irreducible set (Ch. IV §2, p. 290)

> We can prove that `W' ∩ E'_j` for `α < j ≤ α'` are non-singular irreducible subschemes of `X'`
> and contained in `Ũ'`. (p. 290)

One blow-up step, in general form: let `X` be an algebraic scheme, `B` a non-singular irreducible
center, `W` a subscheme containing `B` (as a set) which is simple at every point of `B`, and `t` the
monoidal transformation with center `B`. Then `W' ∩ E'` (`W'` the strict transform of `W`, `E' =
f⁻¹(B)`) is irreducible when non-empty.

The proof follows the geometric picture: `W'` is the blow-up of `W` along `B ∩ W`
(`Subscheme.nonempty_monoidalTransformation_strictTransform`, (a), (b) of p. 167), and `W'` over the
open subscheme `U` of simple points of `W` (which contains `B`) is the blow-up of the non-singular
`U` along `B`, whose exceptional divisor is irreducible (`MonoidalTransformation.isIrreducible_exceptional`).
The lift from `U` to `W` is `MonoidalTransformation.exists_lift`. The openness of the simple locus of
the algebraic scheme `W` is `isOpen_setOf_isSimpleAt` (Ch. 0 (iii), p. 161; it rests on the
cited fact `IsHironakaBase.isClosed_singularLocus`).

Deviation from the paper (gap filled): the paper writes "we can prove" (p. 290); this module
proves the irreducibility for one monoidal transformation.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry IsLocalRing

namespace Hironaka

universe u

namespace Subscheme

variable {X : Scheme.{u}}

/-- If `W_x ⊆ B_x` and `O_x/B_x` is regular, the local ring at `w` of the total transform to `W`
of `B` has regular quotient: it is `O_x/B_x` again. -/
theorem isRegularLocalRing_quotient_totalTransform_subschemeι {W B : Subscheme X}
    (w : W.toScheme) (hle : W.stalkIdeal (W.ι w) ≤ B.stalkIdeal (W.ι w))
    (hreg : IsRegularLocalRing (X.presheaf.stalk (W.ι w) ⧸ B.stalkIdeal (W.ι w))) :
    IsRegularLocalRing (W.toScheme.presheaf.stalk w ⧸ (totalTransform W.ι B).stalkIdeal w) := by
  set φ := (W.ι.stalkMap w).hom with hφ
  have hsurj : Function.Surjective φ := W.ι.stalkMap_surjective w
  have hker : RingHom.ker φ = W.stalkIdeal (W.ι w) := (stalkIdeal_eq_ker_stalkMap W w).symm
  have hT : (totalTransform W.ι B).stalkIdeal w = (B.stalkIdeal (W.ι w)).map φ :=
    stalkIdeal_totalTransform W.ι B w
  rw [hT]
  let ψ := (Ideal.Quotient.mk ((B.stalkIdeal (W.ι w)).map φ)).comp φ
  have hψ : Function.Surjective ψ := Ideal.Quotient.mk_surjective.comp hsurj
  have hkerψ : RingHom.ker ψ = B.stalkIdeal (W.ι w) := by
    ext a
    have h1 : a ∈ RingHom.ker ψ ↔ φ a ∈ (B.stalkIdeal (W.ι w)).map φ := by
      simp [ψ, RingHom.mem_ker, Ideal.Quotient.eq_zero_iff_mem]
    rw [h1, ← Ideal.mem_comap, Ideal.comap_map_of_surjective φ hsurj, ← RingHom.ker_eq_comap_bot,
      hker, sup_eq_left.mpr hle]
  let e := (Ideal.quotEquivOfEq hkerψ.symm).trans (RingHom.quotientKerEquivOfSurjective hψ)
  exact IsRegularLocalRing.of_ringEquiv e


/-- The points of the total transform are the points over `D`. -/
theorem pts_totalTransform_eq_preimage {Y : Scheme.{u}} (g : Y ⟶ X) (D : Subscheme X) :
    (totalTransform g D).pts = g.base ⁻¹' D.pts := by
  ext y
  change y ∈ ((D.comap g).support : Set Y) ↔ _
  rw [Scheme.IdealSheafData.support_comap]
  rfl

/-- Irreducibility passes to the preimage of an irreducible set contained in the range of an
inducing map. -/
theorem isIrreducible_preimage_of_subset_range {Y Z : Type*} [TopologicalSpace Y]
    [TopologicalSpace Z] {g : Y → Z} (hg : Topology.IsInducing g) {A : Set Z}
    (hA : _root_.IsIrreducible A) (hAg : A ⊆ Set.range g) : _root_.IsIrreducible (g ⁻¹' A) := by
  obtain ⟨a₀, ha₀⟩ := hA.nonempty
  obtain ⟨y₀, rfl⟩ := hAg ha₀
  refine ⟨⟨y₀, ha₀⟩, ?_⟩
  intro u v hu hv ⟨a, haA, hau⟩ ⟨b, hbA, hbv⟩
  obtain ⟨u', hu', rfl⟩ := hg.isOpen_iff.mp hu
  obtain ⟨v', hv', rfl⟩ := hg.isOpen_iff.mp hv
  obtain ⟨z, hzA, hzuv⟩ := hA.2 u' v' hu' hv' ⟨g a, haA, hau⟩ ⟨g b, hbA, hbv⟩
  obtain ⟨c, rfl⟩ := hAg hzA
  exact ⟨c, hzA, hzuv⟩

end Subscheme


namespace MonoidalTransformation

variable {X : Scheme.{u}}

/-- **One blow-up step of p. 290**: the strict transform `W'` of `W` meets the exceptional
subscheme `E' = f⁻¹(B)` of the monoidal transformation with non-singular irreducible center
`B ⊆ W` in an irreducible set, provided `W` is simple at the points of `B` (and the intersection is
non-empty).  `W' ∩ E'` is the exceptional divisor of the blow-up of `W` along `B`.

Deviation from the paper (gap filled): "We can prove that `W' ∩ E'_j` for `α < j ≤ α'` are
non-singular irreducible subschemes of `X'` and contained in `Ũ'`" (p. 290) has no proof in the
paper; the irreducibility for the exceptional divisor of one step is proved here (the non-singularity
and the containment are not part of this lemma). -/
@[blueprint "lem:IV.2-5-one-step-irreducible"
  (statement := /-- Let $X$ be an algebraic scheme, $B$ a non-singular irreducible subscheme,
    $W$ a subscheme with $B\subseteq W$ which is simple at every point of $B$, $f\colon X'\to X$
    the monoidal transformation with center $B$, $E'=f^{-1}(B)$ and $W'$ the strict transform of
    $W$. If $W'\cap E'$ is non-empty, it is irreducible. (Used on p.~290.) -/)
  (proof := /-- $W'$ is the blow-up of $W$ along $B\cap W=B$ (\cref{lem:strict-transform-is-blowup}),
    and $W'\cap E'$ is its exceptional subscheme. The simple locus $U$ of $W$ is open and contains
    $B$; the blow-up of $W$ lifts over $U$ (\cref{compat:blowup-flat-base-change}) to the blow-up of
    the non-singular scheme $U$ along $B$, whose exceptional subscheme is irreducible
    (\cref{compat:blowup-exceptional-irreducible}); $W'\cap E'$ is its image.

    \textbf{Deviation from the paper (gap filled).} The paper writes ``We can prove that
    $W'\cap E'_j$ for $\alpha<j\le\alpha'$ are non-singular irreducible subschemes of $X'$ and
    contained in $\tilde U'$'' (p.~290)
    without proof; the irreducibility of the exceptional divisor of one step is proved here, using
    the openness of the simple locus (Ch.~0 (iii), p.~161). -/)
  (proofUses := ["lem:strict-transform-is-blowup", "compat:blowup-exceptional-irreducible",
    "compat:blowup-flat-base-change"])
  (latexEnv := "lemma")]
theorem isIrreducible_pts_strictTransform_inter_exceptional_of_isSimpleAt [Hironaka.Cited.IsHironakaBaseIsClosedSingularLocus.{u}] [Hironaka.Cited.MonoidalTransformationExistsIsProper.{u}] [IsAlgebraicScheme X]
    {B W : Subscheme X} (t : MonoidalTransformation X B)
    (hBns : B.IsNonsingular) (hBirr : B.IsIrreducible) (hBW : B.pts ⊆ W.pts)
    (hW : ∀ x ∈ B.pts, W.IsSimpleAt x)
    (hne : ((Subscheme.strictTransform t W).pts ∩ t.exceptional.pts).Nonempty) :
    _root_.IsIrreducible ((Subscheme.strictTransform t W).pts ∩ t.exceptional.pts) := by
  classical
  have : IsAlgebraicScheme W.toScheme := isAlgebraicScheme_toScheme W
  let U : W.toScheme.Opens := ⟨{w | W.toScheme.IsSimpleAt w}, isOpen_setOf_isSimpleAt W.toScheme⟩
  have : IsAlgebraicScheme (U : W.toScheme.Opens).toScheme := isAlgebraicScheme_of_isOpenImmersion U.ι
  let BW : Subscheme W.toScheme := Subscheme.totalTransform W.ι B
  let BU : Subscheme U.toScheme := Subscheme.totalTransform U.ι BW
  have hBred : B.IsReduced := DatumTransform.isReduced_of_isNonsingular hBns
  have hWB : W ≤ B :=
    Scheme.IdealSheafData.le_def.mpr (Subscheme.isContainedIn_of_pts_subset hBred hBW)
  have hUns : U.toScheme.IsNonsingular := by
    intro u
    have h : W.toScheme.IsSimpleAt (U.ι u) := u.2
    have : IsRegularLocalRing (W.toScheme.presheaf.stalk (U.ι u)) := h
    exact IsRegularLocalRing.of_ringEquiv (FlatPreimm.stalkEquiv U.ι u)
  have hBUns : BU.IsNonsingular := by
    intro y
    obtain ⟨e1⟩ := nonempty_stalk_quot_equiv BU y
    have hu : BU.ι y ∈ BU.pts := Subscheme.mem_pts_ι BU y
    have hw : U.ι (BU.ι y) ∈ BW.pts := by
      have := hu
      rwa [Subscheme.pts_totalTransform_eq_preimage] at this
    have hx : W.ι (U.ι (BU.ι y)) ∈ B.pts := by
      have := hw
      rwa [Subscheme.pts_totalTransform_eq_preimage] at this
    have hreg := Subscheme.isRegularLocalRing_quotient_totalTransform_subschemeι
      (U.ι (BU.ι y)) (Subscheme.stalkIdeal_mono hWB _)
      (Subscheme.isRegular_stalk_quot B hBns hx)
    have hstalk : BU.stalkIdeal (BU.ι y) = (BW.stalkIdeal (U.ι (BU.ι y))).map
        (FlatPreimm.stalkEquiv U.ι (BU.ι y)) := FlatPreimm.stalkIdeal_totalTransform U.ι BW _
    let e2 := Ideal.quotientEquiv (BW.stalkIdeal (U.ι (BU.ι y))) (BU.stalkIdeal (BU.ι y))
      (FlatPreimm.stalkEquiv U.ι (BU.ι y)) hstalk
    have : IsRegularLocalRing (U.toScheme.presheaf.stalk (BU.ι y) ⧸ BU.stalkIdeal (BU.ι y)) :=
      IsRegularLocalRing.of_ringEquiv e2
    exact IsRegularLocalRing.of_ringEquiv e1
  have hBUirr : BU.IsIrreducible := by
    refine Subscheme.isIrreducible_of_pts BU ?_
    have hg : Topology.IsInducing (U.ι ≫ W.ι).base := (U.ι ≫ W.ι).isEmbedding.isInducing
    have hpts : BU.pts = (U.ι ≫ W.ι).base ⁻¹' B.pts := by
      rw [Subscheme.pts_totalTransform_eq_preimage, Subscheme.pts_totalTransform_eq_preimage]
      rfl
    rw [hpts]
    refine Subscheme.isIrreducible_preimage_of_subset_range hg (Subscheme.isIrreducible_pts B hBirr) ?_
    intro b hb
    obtain ⟨w, rfl⟩ := Subscheme.exists_ι_eq_of_mem_pts W (hBW hb)
    have hws : w ∈ (U : Set W.toScheme) := by
      obtain ⟨e⟩ := nonempty_stalk_quot_equiv W w
      have : IsRegularLocalRing (X.presheaf.stalk (W.ι w) ⧸ W.stalkIdeal (W.ι w)) := (hW _ hb).2
      exact IsRegularLocalRing.of_ringEquiv e
    obtain ⟨u, rfl⟩ : w ∈ Set.range U.ι := by rw [Scheme.Opens.range_ι]; exact hws
    exact ⟨u, rfl⟩
  obtain ⟨⟨s0⟩, hs0⟩ := Subscheme.nonempty_monoidalTransformation_strictTransform t W
  obtain ⟨e, he⟩ := hs0 s0
  obtain ⟨ts⟩ : Nonempty (MonoidalTransformation U.toScheme BU) :=
    ⟨(MonoidalTransformation.exists_isProper _ _).choose⟩
  obtain ⟨j', hfl, hpre, hsq, hrange, hexc, hst⟩ := MonoidalTransformation.exists_lift s0 U.ι rfl ts
  have hrangeU : ∀ w : W.toScheme, W.ι w ∈ B.pts → w ∈ Set.range U.ι.base := by
    intro w hb
    have hws : w ∈ (U : Set W.toScheme) := by
      obtain ⟨e⟩ := nonempty_stalk_quot_equiv W w
      have : IsRegularLocalRing (X.presheaf.stalk (W.ι w) ⧸ W.stalkIdeal (W.ι w)) := (hW _ hb).2
      exact IsRegularLocalRing.of_ringEquiv e
    rw [Scheme.Opens.range_ι]; exact hws
  let W' := Subscheme.strictTransform t W
  have hsq' : ∀ u, s0.f.base (j'.base u) = U.ι.base (ts.f.base u) := fun u =>
    congrArg (fun g => g.base u) hsq
  have he' : ∀ q, t.f.base (W'.ι.base (e.hom.base q)) = W.ι.base (s0.f.base q) := fun q =>
    congrArg (fun g => g.base q) he
  have hS : W'.pts ∩ t.exceptional.pts =
      (j' ≫ e.hom ≫ W'.ι).base '' ts.exceptional.pts := by
    ext p
    constructor
    · rintro ⟨hpW, hpE⟩
      have hpr : p ∈ Set.range W'.ι.base := by
        rw [Scheme.IdealSheafData.range_subschemeι]; exact hpW
      obtain ⟨q, rfl⟩ := hpr
      obtain ⟨q', rfl⟩ : ∃ q', e.hom.base q' = q := ⟨e.inv.base q, by
        rw [← Scheme.Hom.comp_apply, Iso.inv_hom_id]; rfl⟩
      have hB' : W.ι.base (s0.f.base q') ∈ B.pts := by
        rw [← he']; rwa [MonoidalTransformation.pts_exceptional] at hpE
      obtain ⟨u, hu⟩ : q' ∈ Set.range j'.base := by
        rw [hrange]; exact hrangeU _ hB'
      subst hu
      refine ⟨u, ?_, rfl⟩
      rw [MonoidalTransformation.pts_exceptional, Set.mem_preimage,
        Subscheme.pts_totalTransform_eq_preimage, Set.mem_preimage,
        Subscheme.pts_totalTransform_eq_preimage, Set.mem_preimage, ← hsq']
      exact hB'
    · rintro ⟨u, hu, rfl⟩
      refine ⟨?_, ?_⟩
      · exact Subscheme.mem_pts_ι W' (e.hom.base (j'.base u))
      · rw [MonoidalTransformation.pts_exceptional, Set.mem_preimage]
        change t.f.base (W'.ι.base (e.hom.base (j'.base u))) ∈ B.pts
        rw [he', hsq']
        rw [MonoidalTransformation.pts_exceptional, Set.mem_preimage,
          Subscheme.pts_totalTransform_eq_preimage, Set.mem_preimage,
          Subscheme.pts_totalTransform_eq_preimage, Set.mem_preimage] at hu
        exact hu
  have hneU : ts.exceptional.pts.Nonempty := by
    obtain ⟨p, hp⟩ := hne
    rw [hS] at hp
    obtain ⟨u, hu, -⟩ := hp
    exact ⟨u, hu⟩
  have hirr := isIrreducible_exceptional hUns hBUns hBUirr ts hneU
  rw [hS]
  exact (Subscheme.isIrreducible_pts _ hirr).image _
    (j' ≫ e.hom ≫ W'.ι).base.hom.continuous.continuousOn

end MonoidalTransformation

end Hironaka
