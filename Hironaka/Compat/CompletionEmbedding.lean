/-
Copyright (c) 2026 Daattavya Aggarwal, Minhyong Kim, Oisin Kim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daattavya Aggarwal, Minhyong Kim, Oisin Kim
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Architect
public import Hironaka.Compat.MainISystem
public import Hironaka.Compat.MonoidalSuccessionBaseChange
public import Hironaka.Compat.CompletionResolved
public import Hironaka.Compat.JacobianCriterion
public import Hironaka.Compat.CompleteRationalBaseChange
public import Hironaka.Compat.GenericWeierstrass
public import Hironaka.Compat.MvPowerSeriesRegular
public import Hironaka.Compat.CompletionStalk
public import Hironaka.Ch4.ImplicationsAB
public import Hironaka.Statements

/-!
# Main Theorem I(n), p. 175 and footnote 37: embedding `V̂₀` in a non-singular scheme

> Since `V̂₀` can be imbedded in a non-singular algebraic scheme,³⁷ we can apply the previous result to `V̂_j(r)`
> (0 ≤ j ≤ β) and `Ŵ(r)` so that there exists a prolongation of `{f̂_i}` satisfying (4), in addition to (1), (2)
> and (3).  (p. 175)
>
> ³⁷ Every complete local ring in the class 𝔅 is a homomorphic image of a formal power series ring over a field of
> characteristic zero.  Hence, `V̂₀` can be embedded in a prime spectrum of such a formal power series ring, which is
> non-singular.  (p. 175)

Contents:
* E1 `exists_closedImmersion_isAmbient`: `Spec(Ô_{X,x})` is a closed subscheme of an ambient scheme
  `Z = Spec(k⟦t₁,…,t_N⟧)` (`IsAmbient Z N`, `N` as large as wanted: add variables mapping to `0`).  Cited input: Cohen's
  structure theorem in the form of footnote 37 (`exists_surjective_mvPowerSeries_of_isAdicComplete`, Compat/JacobianCriterion).
* The closed subscheme `D ⊆ Z` and the data pulled back to it (`Subscheme.isSimpleAt_totalTransform_ι_iff`, the same for
  normal flatness, non-singularity, irreducibility, centers), the images `Subscheme.pushforward`, the monoidal
  transformation `t.induced D` induced by `t` on `D` ("the induced monoidal transformations", p. 173: "See the
  paragraphs preceding Definition 6, § 1") and the compatibility `strictTransform_induced` of the strict transforms.
* E2 `exists_isAmbient_closedImmersion_of_succession`: a succession of `Ŷ` with non-singular (not necessarily
  irreducible!) centers: its end is a closed subscheme of an ambient scheme `Z'` of the same dimension `N`, by blowing up
  the images of the centers (`MonoidalTransformation.irreducibleSpace_and_dim_eq` needs only a non-singular center
  `≠ Z`, which `N > dim Ŷ` ensures).  The paper does not say how the ambient scheme is obtained: "the previous
  result" is applied to the subschemes `V̂_j(r)` of `Z'`.
* E3/E4 `MonoidalSuccession.reach4_of_isMainI`: the succession of `Z'` given by "the previous result" (hypothesis `hAmb`)
  satisfies (1)–(4) for the system `(Z', V̂_0, …, V̂_β; Ŵ)`; its centers lie in the strict transforms of `Ŷ` and induce a
  succession of `Ŷ(r)` reaching (4) (`Reach4`), stage by stage.
* the export `exists_reach4_of_hat`: the data at the end of `{f̂_i}` reach (4) by a prolongation of some length `ℓ`
  (`Reach4`, Compat/MainISystem); one `Reach4.of_iso` passes from `D.toScheme` to the end of `{f̂_i}`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace IsLocalRing

namespace Hironaka

universe u

/-- The closed subscheme of `Z` which is the image of `V ⊆ Ŷ` under a morphism `i : Ŷ ⟶ Z` (for a closed immersion
`i`, `V` seen inside `Z`): the kernel of `V.ι ≫ i`. -/
noncomputable def Subscheme.pushforward {Ŷ Z : Scheme.{u}} (i : Ŷ ⟶ Z) (V : Subscheme Ŷ) : Subscheme Z :=
  (V.ι ≫ i).ker


/-! ### E1: the embedding in `Spec k⟦t₁,…,t_N⟧` (footnote 37) -/

section E1

variable (k : Type u) [Field k]

/-- The Krull dimension of `k⟦t₁,…,t_n⟧` is `n` (at least `n` by `le_ringKrullDim_mvPowerSeries`; at most the number
of generators `t₁,…,t_n` of its maximal ideal). -/
theorem ringKrullDim_mvPowerSeries_eq (n : ℕ) :
    ringKrullDim (MvPowerSeries (Fin n) k) = n := by
  classical
  refine le_antisymm ?_ (le_ringKrullDim_mvPowerSeries k n)
  have h1 := ringKrullDim_le_spanFinrank_maximalIdeal (MvPowerSeries (Fin n) k)
  refine h1.trans ?_
  rw [maximalIdeal_mvPowerSeries_eq_span_X]
  have hle := Submodule.spanFinrank_span_le_ncard_of_finite
    (R := MvPowerSeries (Fin n) k) (Set.finite_range (MvPowerSeries.X : Fin n → MvPowerSeries (Fin n) k))
  have hcard : (Set.range (MvPowerSeries.X : Fin n → MvPowerSeries (Fin n) k)).ncard ≤ n := by
    calc (Set.range (MvPowerSeries.X : Fin n → MvPowerSeries (Fin n) k)).ncard
        ≤ (Finset.univ : Finset (Fin n)).card := by
          rw [← Set.image_univ, ← Finset.coe_univ, ← Finset.coe_image, Set.ncard_coe_finset]
          exact Finset.card_image_le
      _ = n := by simp
  exact_mod_cast hle.trans hcard

/-- The dimension of `Spec R` (p. 163: the supremum of the local dimensions) is the Krull dimension of `R`. -/
theorem dim_Spec_eq (R : Type u) [CommRing R] :
    (Spec (CommRingCat.of R)).dim = ringKrullDim R := by
  rw [Scheme.dim_eq_topologicalKrullDim]
  exact PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim R


variable [CharZero k]

/-- `k⟦t₁,…,t_N⟧`, `k` a field of characteristic zero, belongs to the class 𝔅 (it is complete, noetherian, with
residue field `k`; `IsHironakaBase.of_isAdicComplete`). -/
theorem isHironakaBase_mvPowerSeries (N : ℕ) : IsHironakaBase (MvPowerSeries (Fin N) k) := by
  have := isRegularLocalRing_mvPowerSeries (k := k) N
  have : CharZero (ResidueField (MvPowerSeries (Fin N) k)) :=
    charZero_of_injective_ringHom (f := (algebraMap (MvPowerSeries (Fin N) k)
      (ResidueField (MvPowerSeries (Fin N) k))).comp (algebraMap k (MvPowerSeries (Fin N) k)))
      (RingHom.injective _)
  exact IsHironakaBase.of_isAdicComplete _

/-- Footnote 37, p. 175: `Spec k⟦t₁,…,t_N⟧` is "a prime spectrum of such a formal power series ring, which is
non-singular": it is an algebraic scheme (of the class 𝔅, by `isHironakaBase_mvPowerSeries`), non-singular (Serre's
theorem, footnote 3, on the localizations of the regular local ring), irreducible (a domain) and of dimension `N`. -/
theorem isAmbient_spec_mvPowerSeries [Hironaka.HironakaCitedResults.{u}] (N : ℕ) :
    IsAmbient (Spec (CommRingCat.of (MvPowerSeries (Fin N) k))) N := by
  have := isRegularLocalRing_mvPowerSeries (k := k) N
  have : IsDomain (MvPowerSeries (Fin N) k) := Transforms.isDomain_of_isRegularLocalRing _
  refine ⟨⟨⟨MvPowerSeries (Fin N) k, inferInstance, inferInstance, isHironakaBase_mvPowerSeries k N,
    𝟙 _, inferInstance, inferInstance⟩⟩, fun z => ?_, inferInstance, ?_⟩
  · have : IsRegularLocalRing (Localization.AtPrime (PrimeSpectrum.asIdeal (show PrimeSpectrum (MvPowerSeries (Fin N) k) from z))) :=
      isRegularLocalRing_localization_of_isRegularLocalRing _ _
    exact IsRegularLocalRing.of_ringEquiv
      (Spec.stalkIso (CommRingCat.of (MvPowerSeries (Fin N) k)) z).symm.commRingCatIsoToRingEquiv
  · rw [dim_Spec_eq, ringKrullDim_mvPowerSeries_eq]


omit [CharZero k] in
/-- Adding variables: if `A` is an image of `k⟦t₁,…,t_n⟧` it is an image of `k⟦t₁,…,t_{n+m}⟧` (the new variables
go to `0`). -/
theorem exists_surjective_mvPowerSeries_add {A : Type u} [CommRing A] {n : ℕ}
    (f : MvPowerSeries (Fin n) k →+* A) (hf : Function.Surjective f) (m : ℕ) :
    ∃ g : MvPowerSeries (Fin (n + m)) k →+* A, Function.Surjective g := by
  induction m with
  | zero => exact ⟨f, hf⟩
  | succ m ih =>
    obtain ⟨g, hg⟩ := ih
    let e := (MvPowerSeries.finSuccEquiv (R := k) (n + m)).toRingEquiv
    have hs : Function.Surjective ((PowerSeries.constantCoeff (R := MvPowerSeries (Fin (n + m)) k)).comp
        e.toRingHom) := by
      intro a
      exact ⟨e.symm (PowerSeries.C a), by simp⟩
    exact ⟨g.comp ((PowerSeries.constantCoeff (R := MvPowerSeries (Fin (n + m)) k)).comp e.toRingHom),
      hg.comp hs⟩


end E1

/-- E1 (footnote 37, p. 175): "`V̂₀` can be embedded in a prime spectrum of such a formal power series ring, which
is non-singular": for every point `x` of an algebraic scheme and every `n` there is an ambient scheme
`Z = Spec(k⟦t₁,…,t_N⟧)` of dimension `N > n` and a closed immersion `Spec(Ô_{X,x}) → Z`.  Cited: Cohen's theorem
in the form of footnote 37 (`exists_surjective_mvPowerSeries_of_isAdicComplete`); `Ô_{X,x}` is a complete noetherian
local ring of the class 𝔅 (`isHironakaBase_stalk`, `IsHironakaBase.adicCompletion_maximalIdeal`). -/
theorem exists_closedImmersion_isAmbient [Hironaka.HironakaCitedResults.{u}] (X : Scheme.{u}) [IsAlgebraicScheme X] (x : X) (n : ℕ) :
    ∃ (N : ℕ) (Z : Scheme.{u}) (i : AB.xHat0 X x ⟶ Z), n < N ∧ IsAmbient Z N ∧ IsClosedImmersion i := by
  have := isHironakaBase_stalk X x
  have : IsHironakaBase (AB.Shat X x) := IsHironakaBase.adicCompletion_maximalIdeal _
  obtain ⟨n₀, k, _, _, f, hf⟩ := exists_surjective_mvPowerSeries_of_isAdicComplete (AB.Shat X x)
  obtain ⟨g, hg⟩ := exists_surjective_mvPowerSeries_add k f hf (n + 1)
  exact ⟨n₀ + (n + 1), Spec (CommRingCat.of (MvPowerSeries (Fin (n₀ + (n + 1))) k)),
    Spec.map (CommRingCat.ofHom g), by omega, isAmbient_spec_mvPowerSeries k _,
    IsClosedImmersion.spec_of_surjective _ hg⟩

/-! ### Closed subschemes: transport of the data of Main Theorem I(n) -/

section RingLevel

variable {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S)

/-- `R/J ≃ S/φ(J)` for a surjection `φ` whose kernel lies in `J`. -/
noncomputable def quotEquivMapOfSurjective (hφ : Function.Surjective φ) (J : Ideal R)
    (hJ : RingHom.ker φ ≤ J) : (R ⧸ J) ≃+* (S ⧸ J.map φ) :=
  have hψ : Function.Surjective ((Ideal.Quotient.mk (J.map φ)).comp φ) :=
    Ideal.Quotient.mk_surjective.comp hφ
  have hker : RingHom.ker ((Ideal.Quotient.mk (J.map φ)).comp φ) = J := by
    rw [← RingHom.comap_ker, Ideal.mk_ker, Ideal.comap_map_of_surjective φ hφ, ← RingHom.ker_eq_comap_bot]
    exact sup_eq_left.mpr hJ
  (Ideal.quotEquivOfEq hker).symm.trans (RingHom.quotientKerEquivOfSurjective hψ)

/-- The explicit form of `quotEquivMapOfSurjective`. -/
theorem quotEquivMapOfSurjective_mk (hφ : Function.Surjective φ) (J : Ideal R)
    (hJ : RingHom.ker φ ≤ J) (a : R) :
    quotEquivMapOfSurjective φ hφ J hJ (Ideal.Quotient.mk J a) = Ideal.Quotient.mk (J.map φ) (φ a) := by
  simp [quotEquivMapOfSurjective]

end RingLevel

section RingLevelNF

variable {R S : Type u} [CommRing R] [CommRing S] (φ : R →+* S)

/-- Normal flatness of `W` in `R/V` is the same as that of `φ(W)` in `S/φ(V)`, for a surjection `φ` whose kernel
lies in `V`. -/
theorem isNormallyFlatAlongIdeal_map_quot_iff (hφ : Function.Surjective φ) (V W : Ideal R)
    (hV : RingHom.ker φ ≤ V) :
    IsNormallyFlatAlongIdeal (W.map (Ideal.Quotient.mk V)) ↔
      IsNormallyFlatAlongIdeal ((W.map φ).map (Ideal.Quotient.mk (V.map φ))) := by
  let e := quotEquivMapOfSurjective φ hφ V hV
  have hcomp : (e : R ⧸ V →+* S ⧸ V.map φ).comp (Ideal.Quotient.mk V) =
      (Ideal.Quotient.mk (V.map φ)).comp φ :=
    RingHom.ext fun a => quotEquivMapOfSurjective_mk φ hφ V hV a
  have hmap : (W.map (Ideal.Quotient.mk V)).map (e : R ⧸ V →+* S ⧸ V.map φ) =
      (W.map φ).map (Ideal.Quotient.mk (V.map φ)) := by
    rw [Ideal.map_map, hcomp, ← Ideal.map_map]
  constructor
  · intro h
    exact Hironaka.isNormallyFlatAlongIdeal_of_ringEquiv e _ _ hmap h
  · intro h
    refine Hironaka.isNormallyFlatAlongIdeal_of_ringEquiv e.symm _ _ ?_ h
    rw [← hmap, Ideal.map_map]
    convert Ideal.map_id _ using 2
    ext a
    simp

end RingLevelNF

section ClosedSubscheme

variable {Z : Scheme.{u}}

/-- The kernel of the stalk map of `D.ι` lies in the stalk of every subscheme `W ⊆ D`. -/
theorem Subscheme.ker_stalkMap_ι_le {D W : Subscheme Z} (hDW : D ≤ W) (y : D.toScheme) :
    RingHom.ker (D.ι.stalkMap y).hom ≤ W.stalkIdeal (D.ι y) := by
  rw [← stalkIdeal_eq_ker_stalkMap D y]
  exact Subscheme.stalkIdeal_mono hDW _

/-- Simple points of a subscheme `W ⊆ D` of the closed subscheme `D` of `Z`: `W ∩ D = W` is simple at `D.ι y`
iff its pull-back to `D` is simple at `y`. -/
theorem Subscheme.isSimpleAt_totalTransform_ι_iff {D W : Subscheme Z} (hDW : D ≤ W) (y : D.toScheme) :
    (Subscheme.totalTransform D.ι W).IsSimpleAt y ↔ W.IsSimpleAt (D.ι y) := by
  have hmem : y ∈ (Subscheme.totalTransform D.ι W).pts ↔ D.ι y ∈ W.pts := by
    rw [Subscheme.pts_totalTransform_eq_preimage]; rfl
  have hφ : Function.Surjective (D.ι.stalkMap y).hom := D.ι.stalkMap_surjective y
  let e := quotEquivMapOfSurjective (D.ι.stalkMap y).hom hφ (W.stalkIdeal (D.ι y))
    (Subscheme.ker_stalkMap_ι_le hDW y)
  have hs : (Subscheme.totalTransform D.ι W).stalkIdeal y = (W.stalkIdeal (D.ι y)).map (D.ι.stalkMap y).hom :=
    Hironaka.stalkIdeal_totalTransform D.ι W y
  constructor
  · rintro ⟨hy, hreg⟩
    refine ⟨hmem.mp hy, ?_⟩
    rw [hs] at hreg
    exact IsRegularLocalRing.of_ringEquiv e.symm
  · rintro ⟨hy, hreg⟩
    refine ⟨hmem.mpr hy, ?_⟩
    rw [hs]
    exact IsRegularLocalRing.of_ringEquiv e

/-- Normal flatness along the closed subscheme `D`: for `W ⊆ V ⊆ D` the pull-backs to `D` are normally flat at
`y` iff `V` is normally flat along `W` at `D.ι y`. -/
theorem Subscheme.isNormallyFlatAlongAt'_totalTransform_ι_iff {D V W : Subscheme Z} (hDV : D ≤ V)
    (hWV : W.IsContainedIn V) (y : D.toScheme) :
    Subscheme.IsNormallyFlatAlongAt' (Subscheme.totalTransform D.ι V) (Subscheme.totalTransform D.ι W) y ↔
      Subscheme.IsNormallyFlatAlongAt' V W (D.ι y) := by
  have hWV' : (Subscheme.totalTransform D.ι W).IsContainedIn (Subscheme.totalTransform D.ι V) :=
    fun U => Scheme.IdealSheafData.comap_mono _ (show V ≤ W from fun U => hWV U) U
  rw [Subscheme.isNormallyFlatAlongAt'_iff _ _ hWV', Subscheme.isNormallyFlatAlongAt'_iff _ _ hWV,
    Subscheme.pts_totalTransform_eq_preimage]
  have hφ : Function.Surjective (D.ι.stalkMap y).hom := D.ι.stalkMap_surjective y
  rw [Hironaka.stalkIdeal_totalTransform D.ι V y, Hironaka.stalkIdeal_totalTransform D.ι W y,
    ← isNormallyFlatAlongIdeal_map_quot_iff _ hφ _ _ (Subscheme.ker_stalkMap_ι_le hDV y)]
  rfl


/-- A non-singular subscheme is simple at each of its points. -/
theorem Subscheme.isSimpleAt_of_isNonsingular {B : Subscheme Z} (hB : B.IsNonsingular) {x : Z}
    (hx : x ∈ B.pts) : B.IsSimpleAt x := by
  obtain ⟨b, rfl⟩ := Subscheme.exists_ι_eq_of_mem_pts B hx
  obtain ⟨e⟩ := nonempty_stalk_quot_equiv B b
  have : IsRegularLocalRing (B.toScheme.presheaf.stalk b) := hB b
  exact ⟨hx, IsRegularLocalRing.of_ringEquiv e.symm⟩

/-- Non-singularity of `B ⊆ D` is the same as that of its pull-back to `D`. -/
theorem Subscheme.isNonsingular_totalTransform_ι_iff {D B : Subscheme Z} (hDB : D ≤ B) :
    (Subscheme.totalTransform D.ι B).IsNonsingular ↔ B.IsNonsingular := by
  constructor
  · intro h
    refine Subscheme.isNonsingular_of_forall_isSimpleAt fun x hx => ?_
    obtain ⟨y, rfl⟩ := Subscheme.exists_ι_eq_of_mem_pts D (pts_subset_of_isContainedIn
      (show B.IsContainedIn D from fun U => hDB U) hx)
    have hy : y ∈ (Subscheme.totalTransform D.ι B).pts := by
      rw [Subscheme.pts_totalTransform_eq_preimage]; exact hx
    exact (Subscheme.isSimpleAt_totalTransform_ι_iff hDB y).mp
      (Subscheme.isSimpleAt_of_isNonsingular h hy)
  · intro h
    refine Subscheme.isNonsingular_of_forall_isSimpleAt fun y hy => ?_
    rw [Subscheme.pts_totalTransform_eq_preimage] at hy
    exact (Subscheme.isSimpleAt_totalTransform_ι_iff hDB y).mpr (Subscheme.isSimpleAt_of_isNonsingular h hy)

/-- Irreducibility of `B ⊆ D` is the same as that of its pull-back to `D`. -/
theorem Subscheme.isIrreducible_totalTransform_ι_iff {D B : Subscheme Z} (hDB : D ≤ B) :
    (Subscheme.totalTransform D.ι B).IsIrreducible ↔ B.IsIrreducible := by
  have hsub : B.pts ⊆ Set.range D.ι := by
    rw [Scheme.IdealSheafData.range_subschemeι]
    exact pts_subset_of_isContainedIn (show B.IsContainedIn D from fun U => hDB U)
  constructor
  · intro h
    have h1 := (Subscheme.isIrreducible_pts _ h).image D.ι D.ι.continuous.continuousOn
    rw [Subscheme.pts_totalTransform_eq_preimage, Set.image_preimage_eq_of_subset hsub] at h1
    exact Subscheme.isIrreducible_of_pts B h1
  · intro h
    refine Subscheme.isIrreducible_of_pts _ ?_
    rw [Subscheme.pts_totalTransform_eq_preimage]
    exact Subscheme.isIrreducible_preimage_of_subset_range D.ι.isEmbedding.isInducing
      (Subscheme.isIrreducible_pts B h) hsub

/-- A center contained in `D` pulls back to a center of `D`. -/
theorem Subscheme.IsCenter.totalTransform_ι {D B : Subscheme Z} (hDB : D ≤ B) (hB : B.IsCenter) :
    (Subscheme.totalTransform D.ι B).IsCenter := by
  rcases hB with rfl | ⟨hns, hirr⟩
  · left
    exact Subscheme.totalTransform_empty D.ι
  · right
    exact ⟨(Subscheme.isNonsingular_totalTransform_ι_iff hDB).mpr hns,
      (Subscheme.isIrreducible_totalTransform_ι_iff hDB).mpr hirr⟩

end ClosedSubscheme

/-! ### The monoidal transformation induced on a closed subscheme -/

namespace MonoidalTransformation

variable {Z : Scheme.{u}} {B : Subscheme Z}

/-- Transport of a monoidal transformation along an isomorphism of its total space. -/
noncomputable def congrX (s : MonoidalTransformation Z B) {X'' : Scheme.{u}} (a : s.X' ≅ X'') :
    MonoidalTransformation Z B where
  X' := X''
  f := a.inv ≫ s.f
  invertible := by
    rw [Subscheme.totalTransform_comp]
    exact isInvertibleIdeal_totalTransform_of_flat a.inv s.invertible
  universal := fun X0 f' hf' => by
    obtain ⟨h, hh, huniq⟩ := s.universal X0 f' hf'
    refine ⟨h ≫ a.hom, ?_, fun h' hh' => ?_⟩
    · show (h ≫ a.hom) ≫ a.inv ≫ s.f = f'
      rw [Category.assoc, ← Category.assoc a.hom, a.hom_inv_id, Category.id_comp, hh]
    · have h1 : (h' ≫ a.inv) ≫ s.f = f' := by rw [Category.assoc]; exact hh'
      have := huniq _ h1
      rw [← this, Category.assoc, a.inv_hom_id, Category.comp_id]

@[simp] theorem congrX_X' (s : MonoidalTransformation Z B) {X'' : Scheme.{u}} (a : s.X' ≅ X'') :
    (s.congrX a).X' = X'' := rfl

@[simp] theorem congrX_f (s : MonoidalTransformation Z B) {X'' : Scheme.{u}} (a : s.X' ≅ X'') :
    (s.congrX a).f = a.inv ≫ s.f := rfl

/-- p. 173 ("See the paragraphs preceding Definition 6, § 1"): the monoidal transformation of the closed subscheme
`D` with center `B ∩ D` *induced* by `t`; its total space is the strict transform of `D`
(`Subscheme.nonempty_monoidalTransformation_strictTransform`). -/
@[reducible] noncomputable def induced [Hironaka.HironakaCitedResults.{u}] (t : MonoidalTransformation Z B) (D : Subscheme Z) :
    MonoidalTransformation D.toScheme (Subscheme.totalTransform D.ι B) :=
  let s := Classical.choice (Subscheme.nonempty_monoidalTransformation_strictTransform t D).1
  let e := Classical.choose ((Subscheme.nonempty_monoidalTransformation_strictTransform t D).2 s)
  { X' := (Subscheme.strictTransform t D).toScheme
    f := (s.congrX e).f
    invertible := (s.congrX e).invertible
    universal := (s.congrX e).universal }

@[simp] theorem induced_X' [Hironaka.HironakaCitedResults.{u}] (t : MonoidalTransformation Z B) (D : Subscheme Z) :
    (t.induced D).X' = (Subscheme.strictTransform t D).toScheme := rfl

/-- The structure morphism of `s.congrX a` followed by `D.ι` is `g` if `a` is compatible with `g` and `s.f ≫ D.ι`. -/
theorem congrX_f_comp_ι {D : Subscheme Z} {B' : Subscheme D.toScheme}
    (s : MonoidalTransformation D.toScheme B') {X'' : Scheme.{u}} (a : s.X' ≅ X'') (g : X'' ⟶ Z)
    (h : a.hom ≫ g = s.f ≫ D.ι) : (s.congrX a).f ≫ D.ι = g := by
  show (a.inv ≫ s.f) ≫ D.ι = g
  rw [Category.assoc, ← h, ← Category.assoc, a.inv_hom_id, Category.id_comp]

/-- The induced transformation of `D` commutes with `t` over the closed immersions: `f_D ≫ D.ι = D'.ι ≫ t.f`, where
`D' = strictTransform t D`. -/
theorem induced_f_comp [Hironaka.HironakaCitedResults.{u}] (t : MonoidalTransformation Z B) (D : Subscheme Z) :
    (t.induced D).f ≫ D.ι = (Subscheme.strictTransform t D).ι ≫ t.f :=
  congrX_f_comp_ι _ _ _ (Classical.choose_spec ((Subscheme.nonempty_monoidalTransformation_strictTransform t D).2
      (Classical.choice (Subscheme.nonempty_monoidalTransformation_strictTransform t D).1)))

end MonoidalTransformation


section K2

variable {Z : Scheme.{u}} {B : Subscheme Z}

/-- **The strict transform commutes with the induction on a closed subscheme.**  Let `t` be a monoidal transformation
of `Z`, `D ⊆ Z` a closed subscheme and `V ⊆ D`.  Then the strict transform, by the transformation `t.induced D` of `D`,
of the pull-back `V ∩ D` is the pull-back to `D' = strictTransform t D` of the strict transform of `V`.  (p. 173, "the
monoidal transformations `V_j(i+1) → V_j(i)` induced by `f_i`"; the paper does not prove that the induced
transformation of `V` inside `D` is the one induced by `t`.)  Proved on stalks: by `strictTransform_stalkIdeal` both
sides are the saturation of the total transform by the exceptional ideal `(σ)`, and the kernel `D'_z ⊆ V'_z` of the
surjective stalk map is absorbed because the saturation is already `σ`-saturated. -/
theorem MonoidalTransformation.strictTransform_induced [Hironaka.HironakaCitedResults.{u}] (t : MonoidalTransformation Z B) {D V : Subscheme Z}
    (hDV : D ≤ V) :
    Subscheme.strictTransform (t.induced D) (Subscheme.totalTransform D.ι V) =
      Subscheme.totalTransform (Subscheme.strictTransform t D).ι (Subscheme.strictTransform t V) := by
  refine Subscheme.ext_stalkIdeal fun y => ?_
  have hcomm := MonoidalTransformation.induced_f_comp t D
  have hφ : Function.Surjective ((Subscheme.strictTransform t D).ι.stalkMap y).hom :=
    (Subscheme.strictTransform t D).ι.stalkMap_surjective y
  obtain ⟨σ, hσ, -⟩ := t.invertible.exists_stalkIdeal_eq_span ((Subscheme.strictTransform t D).ι y)
  have hσ' : t.exceptional.stalkIdeal ((Subscheme.strictTransform t D).ι y) = Ideal.span {σ} := hσ
  have h1 : Subscheme.totalTransform (t.induced D).f (Subscheme.totalTransform D.ι V) =
      Subscheme.totalTransform (Subscheme.strictTransform t D).ι (Subscheme.totalTransform t.f V) := by
    rw [← Subscheme.totalTransform_comp, hcomm, Subscheme.totalTransform_comp]
  have h2 : (t.induced D).exceptional =
      Subscheme.totalTransform (Subscheme.strictTransform t D).ι t.exceptional := by
    unfold MonoidalTransformation.exceptional
    rw [← Subscheme.totalTransform_comp, hcomm, Subscheme.totalTransform_comp]
  have e1 : (Subscheme.totalTransform (Subscheme.strictTransform t D).ι
      (Subscheme.totalTransform t.f V)).stalkIdeal y =
      ((Subscheme.totalTransform t.f V).stalkIdeal ((Subscheme.strictTransform t D).ι y)).map
        ((Subscheme.strictTransform t D).ι.stalkMap y).hom := Hironaka.stalkIdeal_totalTransform _ _ _
  have e2 : (Subscheme.totalTransform (Subscheme.strictTransform t D).ι t.exceptional).stalkIdeal y =
      (t.exceptional.stalkIdeal ((Subscheme.strictTransform t D).ι y)).map
        ((Subscheme.strictTransform t D).ι.stalkMap y).hom := Hironaka.stalkIdeal_totalTransform _ _ _
  have e3 : (Subscheme.totalTransform (Subscheme.strictTransform t D).ι
      (Subscheme.strictTransform t V)).stalkIdeal y =
      ((Subscheme.strictTransform t V).stalkIdeal ((Subscheme.strictTransform t D).ι y)).map
        ((Subscheme.strictTransform t D).ι.stalkMap y).hom := Hironaka.stalkIdeal_totalTransform _ _ _
  have e4 := Subscheme.strictTransform_stalkIdeal t V ((Subscheme.strictTransform t D).ι y)
  have hker : RingHom.ker ((Subscheme.strictTransform t D).ι.stalkMap y).hom ≤
      (Subscheme.strictTransform t V).stalkIdeal ((Subscheme.strictTransform t D).ι y) := by
    rw [← stalkIdeal_eq_ker_stalkMap]
    exact Subscheme.stalkIdeal_mono (Subscheme.strictTransform_mono t hDV) _
  rw [Subscheme.strictTransform_stalkIdeal, h1, h2, e1, e2, e3, hσ', Ideal.map_span, Set.image_singleton]
  set φ := ((Subscheme.strictTransform t D).ι.stalkMap y).hom with hφdef
  set T := (Subscheme.totalTransform t.f V).stalkIdeal ((Subscheme.strictTransform t D).ι y) with hT
  rw [e4, hσ'] at hker ⊢
  ext r'
  obtain ⟨r, rfl⟩ := hφ r'
  rw [Hironaka.Ideal.mem_iSup_colon_pow_span]
  constructor
  · rintro ⟨n, hn⟩
    have hn' : φ (r * σ ^ n) ∈ Ideal.map φ T := by simpa [map_mul, map_pow] using hn
    obtain ⟨a, haT, hφa⟩ := (Ideal.mem_map_iff_of_surjective φ hφ).mp hn'
    have hk : r * σ ^ n - a ∈ RingHom.ker φ := by rw [RingHom.mem_ker, map_sub, hφa, sub_self]
    have hkS := hker hk
    rw [Hironaka.Ideal.mem_iSup_colon_pow_span] at hkS
    obtain ⟨m, hm⟩ := hkS
    refine Ideal.mem_map_of_mem φ ((Hironaka.Ideal.mem_iSup_colon_pow_span T σ r).mpr ⟨n + m, ?_⟩)
    have : r * σ ^ (n + m) = (r * σ ^ n - a) * σ ^ m + a * σ ^ m := by ring
    rw [this]
    exact T.add_mem hm (T.mul_mem_right _ haT)
  · intro h
    obtain ⟨x, hxS, hx⟩ := (Ideal.mem_map_iff_of_surjective φ hφ).mp h
    obtain ⟨n, hn⟩ := (Hironaka.Ideal.mem_iSup_colon_pow_span T σ x).mp hxS
    refine ⟨n, ?_⟩
    rw [← hx, ← map_pow, ← map_mul]
    exact Ideal.mem_map_of_mem φ hn

end K2

section Push

variable {Y Z : Scheme.{u}} (i : Y ⟶ Z) [IsClosedImmersion i]

omit [IsClosedImmersion i] in
theorem Subscheme.pushforward_eq_map (V : Subscheme Y) :
    Subscheme.pushforward i V = Scheme.IdealSheafData.map V i := rfl

omit [IsClosedImmersion i] in
/-- The ideal of `i(Ŷ)` is contained in the ideal of `i(V)`. -/
theorem Subscheme.ker_le_pushforward (V : Subscheme Y) : i.ker ≤ Subscheme.pushforward i V := by
  rw [Subscheme.pushforward_eq_map, ← Scheme.IdealSheafData.map_bot]
  exact Scheme.IdealSheafData.map_mono i bot_le

omit [IsClosedImmersion i] in
theorem Subscheme.pushforward_mono {V V' : Subscheme Y} (h : V ≤ V') :
    Subscheme.pushforward i V ≤ Subscheme.pushforward i V' :=
  Scheme.IdealSheafData.map_mono i h

/-- The points of the image subscheme `i(V)` are the images of the points of `V`. -/
theorem Subscheme.pts_pushforward (V : Subscheme Y) :
    (Subscheme.pushforward i V).pts = i.base '' V.pts := by
  have h1 : (Subscheme.pushforward i V).pts = closure (Set.range (V.ι ≫ i)) :=
    Scheme.Hom.support_ker (V.ι ≫ i)
  have h2 : IsClosed (Set.range (V.ι ≫ i)) :=
    (IsClosedImmersion.isClosedEmbedding (V.ι ≫ i)).isClosed_range
  rw [h1, h2.closure_eq]
  ext z
  constructor
  · rintro ⟨b, rfl⟩
    exact ⟨V.ι.base b, Subscheme.mem_pts_ι V b, rfl⟩
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨b, rfl⟩ := Subscheme.exists_ι_eq_of_mem_pts V hy
    exact ⟨b, rfl⟩

/-- The stalk ideal of the image subscheme at `i(y)` is the preimage of the stalk ideal of `V` at `y` (the stalk map of
a closed immersion is surjective). -/
theorem Subscheme.stalkIdeal_pushforward (V : Subscheme Y) (y : Y) :
    (Subscheme.pushforward i V).stalkIdeal (i.base y) = (V.stalkIdeal y).comap (i.stalkMap y).hom := by
  by_cases hy : y ∈ V.pts
  · obtain ⟨b, rfl⟩ := Subscheme.exists_ι_eq_of_mem_pts V hy
    obtain ⟨e₀, he₀⟩ := Subscheme.exists_iso_ker (V.ι ≫ i)
    have hf : V.ι ≫ i = e₀.symm.hom ≫ Subscheme.ι ((V.ι ≫ i).ker) := by
      show V.ι ≫ i = e₀.symm.hom ≫ (V.ι ≫ i).ker.subschemeι
      rw [Iso.symm_hom, ← he₀]
      simp
    have h := (Subscheme.ker_stalkMap_eq_and_surjective_of_eq_iso_comp (V.ι ≫ i) _ e₀.symm hf b).1
    show Subscheme.stalkIdeal (V.ι ≫ i).ker ((V.ι ≫ i).base b) = _
    rw [← h, Scheme.Hom.stalkMap_comp]
    change RingHom.ker (CommRingCat.Hom.hom (i.stalkMap (V.ι.base b) ≫ V.ι.stalkMap b)) = _
    rw [CommRingCat.hom_comp, stalkIdeal_eq_ker_stalkMap V b]
    ext a
    simp [RingHom.mem_ker, Ideal.mem_comap]
  · have h1 : i.base y ∉ (Subscheme.pushforward i V).pts := by
      rw [Subscheme.pts_pushforward]
      rintro ⟨y', hy', hyy⟩
      exact hy (i.isClosedEmbedding.injective hyy ▸ hy')
    rw [Subscheme.stalkIdeal_eq_top_of_notMem_pts h1, Subscheme.stalkIdeal_eq_top_of_notMem_pts hy,
      Ideal.comap_top]

/-- Pulling back the image of `V` along the closed immersion `i` gives back `V`. -/
theorem Subscheme.totalTransform_pushforward (V : Subscheme Y) :
    Subscheme.totalTransform i (Subscheme.pushforward i V) = V := by
  refine Subscheme.ext_stalkIdeal fun y => ?_
  rw [Hironaka.stalkIdeal_totalTransform, Subscheme.stalkIdeal_pushforward]
  exact Ideal.map_comap_of_surjective _ (i.stalkMap_surjective y) _

end Push

section Successions

/-- The blow-up does not raise the dimension of an algebraic scheme. -/
theorem MonoidalTransformation.dim_X'_le [Hironaka.HironakaCitedResults.{u}] {X : Scheme.{u}} [IsAlgebraicScheme X] {B : Subscheme X}
    (t : MonoidalTransformation X B) : t.X'.dim ≤ X.dim := by
  refine iSup_le fun y => ?_
  have := MonoidalSuccession.dimAt_le_composite_of_isAlgebraicScheme
    (MonoidalSuccession.cons B t (MonoidalSuccession.nil t.X')) y
  exact this.trans (le_iSup (fun x => X.dimAt x) _)

/-- A succession of monoidal transformations of an algebraic scheme does not raise the dimension. -/
theorem MonoidalSuccession.dim_le [Hironaka.HironakaCitedResults.{u}] {X Y : Scheme.{u}} [IsAlgebraicScheme X] (s : MonoidalSuccession X Y) :
    Y.dim ≤ X.dim :=
  iSup_le fun y => (MonoidalSuccession.dimAt_le_composite_of_isAlgebraicScheme s y).trans
    (le_iSup (fun x => X.dimAt x) _)

/-- The centers of a succession satisfying (1̂) are non-singular. -/
theorem MonoidalSuccession.IsMain123Hat.hasNonsingularCenters {X Y : Scheme.{u}} {s : MonoidalSuccession X Y}
    {β : ℕ} {V : Fin (β + 1) → Subscheme X} {W : Subscheme X} (h : s.IsMain123Hat V W) :
    s.HasNonsingularCenters := by
  induction s generalizing β with
  | nil => trivial
  | cons B t rest ih => exact ⟨h.1.1.1, ih h.2⟩

end Successions

section LiftUp

/-- A closed immersion that is onto an irreducible scheme of dimension `N` has source of dimension `N`:
a surjective closed immersion is a homeomorphism. -/
theorem dim_eq_of_surjective_closedImmersion {Y Z : Scheme.{u}} (i : Y ⟶ Z) [IsClosedImmersion i]
    (h : Function.Surjective i.base) : Y.dim = Z.dim := by
  rw [Scheme.dim_eq_topologicalKrullDim, Scheme.dim_eq_topologicalKrullDim]
  exact IsHomeomorph.topologicalKrullDim_eq _
    (isHomeomorph_iff_isEmbedding_surjective.mpr ⟨i.isEmbedding, h⟩)

/-- E2 (p. 175, the lift to the ambient scheme, a gap of the paper): if `Ŷ` is a closed subscheme of the ambient
scheme `Z` of dimension `N > dim Ŷ`, then the end `Y'` of a succession `ŝ` of `Ŷ` with non-singular (not
necessarily irreducible) centers is a closed subscheme of an ambient scheme `Z'` of the same dimension `N`: blow up
`Z` along the image of the first center, which is non-singular and not all of `Z` (`N > dim Ŷ`), and induce. -/
theorem exists_isAmbient_closedImmersion_of_succession [Hironaka.HironakaCitedResults.{u}] {Ŷ Z : Scheme.{u}} {N : ℕ} (hZ : IsAmbient Z N)
    (hŶ : IsAlgebraicScheme Ŷ) (i : Ŷ ⟶ Z) [IsClosedImmersion i] (hdim : Ŷ.dim < N) {Y' : Scheme.{u}}
    (ŝ : MonoidalSuccession Ŷ Y') (hŝ : ŝ.HasNonsingularCenters) :
    ∃ (Z' : Scheme.{u}) (i' : Y' ⟶ Z'), IsClosedImmersion i' ∧ IsAmbient Z' N := by
  induction ŝ generalizing Z with
  | nil Ŷ => exact ⟨Z, i, inferInstance, hZ⟩
  | @cons Ŷ Bh th Y' rest ih =>
    have := hŶ
    obtain ⟨hBh, hrest⟩ := hŝ
    obtain ⟨hZalg, hZns, hZirr, hZdim⟩ := hZ
    -- the image of the center
    have hBns : (Subscheme.pushforward i Bh).IsNonsingular := by
      obtain ⟨e, -⟩ := Subscheme.exists_iso_ker (Bh.ι ≫ i)
      exact Hironaka.CD.isNonsingular_of_iso e hBh
    have hBX : (Subscheme.pushforward i Bh).pts ≠ Set.univ := by
      intro h
      rw [Subscheme.pts_pushforward] at h
      have hsurj : Function.Surjective i.base := by
        intro z
        have : z ∈ i.base '' Bh.pts := h ▸ Set.mem_univ z
        obtain ⟨y, -, rfl⟩ := this
        exact ⟨y, rfl⟩
      have := dim_eq_of_surjective_closedImmersion i hsurj
      rw [hZdim] at this
      rw [this] at hdim
      exact lt_irrefl _ hdim
    obtain ⟨t⟩ : Nonempty (MonoidalTransformation Z (Subscheme.pushforward i Bh)) :=
      ⟨(MonoidalTransformation.exists_isProper Z _).choose⟩
    have := hZalg
    have := hZirr
    obtain ⟨hirr, hdim'⟩ := MonoidalTransformation.irreducibleSpace_and_dim_eq hZns hBns t hBX
    have hZ' : IsAmbient t.X' N :=
      ⟨t.isAlgebraicScheme, (t.isNonsingular_and_isNonsingular_exceptional hZns hBns).1, hirr,
        hdim'.trans hZdim⟩
    -- the closed immersion of the blow-up of `Ŷ`
    obtain ⟨e, he⟩ := Subscheme.exists_iso_ker i
    have hcen : Subscheme.totalTransform e.hom Bh =
        Subscheme.totalTransform i.ker.subschemeι (Subscheme.pushforward i Bh) := by
      rw [← he, Subscheme.totalTransform_comp, Subscheme.totalTransform_pushforward]
    obtain ⟨a, -⟩ := (Subscheme.nonempty_monoidalTransformation_strictTransform t i.ker).2
      ((th.ofIso e).congrCenter hcen)
    have hdim₁ : th.X'.dim < N := lt_of_le_of_lt th.dim_X'_le hdim
    have := th.isAlgebraicScheme
    have hia : IsClosedImmersion a.hom := by
      have : IsIso a.hom := inferInstance
      infer_instance
    have hi₁ : IsClosedImmersion (a.hom ≫ (Subscheme.strictTransform t i.ker).ι) := inferInstance
    exact @ih _ hZ' th.isAlgebraicScheme (a.hom ≫ (Subscheme.strictTransform t i.ker).ι) hi₁ hdim₁ hrest

end LiftUp

section E4c

/-- A non-singular scheme is simple at every point, as a subscheme of itself. -/
theorem Subscheme.isSimpleAt_bot {Z : Scheme.{u}} (hZ : Z.IsNonsingular) (x : Z) :
    (⊥ : Subscheme Z).IsSimpleAt x := by
  have hreg : IsRegularLocalRing (Z.presheaf.stalk x) := hZ x
  refine ⟨?_, ?_⟩
  · rw [Subscheme.mem_pts_iff_stalkIdeal_ne_top, Subscheme.stalkIdeal_bot_eq]
    exact bot_ne_top
  · rw [Subscheme.stalkIdeal_bot_eq]
    exact IsRegularLocalRing.of_ringEquiv (RingEquiv.quotientBot _).symm

/-- The strict transform of the system `(V_0 = ⊥, V_1, …, V_β)` is the system of the strict transforms (the strict
transform of the scheme itself is the scheme, `MonoidalTransformation.strictTransform_bot`). -/
theorem MonoidalTransformation.strictTransform_mainSystem {X : Scheme.{u}} {B : Subscheme X} (t : MonoidalTransformation X B)
    {β : ℕ} (V : Fin β → Subscheme X) :
    (fun j => Subscheme.strictTransform t (mainSystem V j)) =
      mainSystem (fun j => Subscheme.strictTransform t (V j)) := by
  funext j
  refine Fin.cases ?_ (fun j => ?_) j
  · exact MonoidalTransformation.strictTransform_bot t
  · rfl

/-- E4 (p. 173, 175; stagewise): the data on the closed subscheme `D` of the ambient scheme `Z` (`V̂_j = V_j ∩ D`,
`Ŵ = W ∩ D`, with `D ⊆ V_j`, `W ⊆ V_j`) reach (4) by a prolongation of length `r` if the system `(Z, V_0, …, V_β; W)`
does by a succession of `Z` of length `r` satisfying (1)–(4): the monoidal transformations of `Z` induce those of
`D` (`MonoidalTransformation.induced`) with the same centers `B_i ∩ D = B_i` (as `B_i ⊆ W(i) ⊆ D(i)`), and
(1), (2), (3), (4) are transported by the pull-back to `D`. -/
theorem MonoidalSuccession.reach4_of_isMainI [Hironaka.HironakaCitedResults.{u}] {Z Z'' : Scheme.{u}} (sZ : MonoidalSuccession Z Z'')
    (hA : IsAlgebraicScheme Z) (hZ : Z.IsNonsingular) {β : ℕ} (D : Subscheme Z) (V : Fin (β + 1) → Subscheme Z)
    (W : Subscheme Z) (hDV : ∀ j, D ≤ V j) (hWV : ∀ j, W.IsContainedIn (V j))
    (h : sZ.IsMainI (mainSystem V) W) :
    Reach4 sZ.length D.toScheme (fun j => Subscheme.totalTransform D.ι (V j))
      (Subscheme.totalTransform D.ι W) := by
  induction sZ with
  | nil Z =>
    have hDW : D ≤ W := (hDV 0).trans (show V 0 ≤ W from fun U => hWV 0 U)
    obtain ⟨hns, hnf⟩ := h.2
    refine ⟨(Subscheme.isNonsingular_totalTransform_ι_iff hDW).mpr hns, fun j y hy => ?_⟩
    rw [Subscheme.pts_totalTransform_eq_preimage] at hy
    exact (Subscheme.isNormallyFlatAlongAt'_totalTransform_ι_iff (hDV j) (hWV j) y).mpr
      (hnf j.succ _ hy)
  | @cons X B t Y rest ih =>
    have := hA
    obtain ⟨⟨⟨⟨hBc, hBW⟩, h2, h3⟩, h123⟩, h4⟩ := h
    have hDW : D ≤ W := (hDV 0).trans (show V 0 ≤ W from fun U => hWV 0 U)
    have hDB : D ≤ B := hDW.trans (show W ≤ B from fun U => hBW U)
    have hBV : ∀ j, B.IsContainedIn (V j) := fun j U => (hWV j U).trans (hBW U)
    have hsys := MonoidalTransformation.strictTransform_mainSystem t V
    refine ⟨Subscheme.totalTransform D.ι B, t.induced D, ⟨⟨Subscheme.IsCenter.totalTransform_ι hDB hBc, ?_⟩, ?_, ?_⟩, ?_⟩
    · exact fun U => Scheme.IdealSheafData.comap_mono _ (show W ≤ B from fun U => hBW U) U
    · intro y hy hres
      rw [Subscheme.pts_totalTransform_eq_preimage] at hy
      refine h2 (D.ι y) hy ⟨(Subscheme.isSimpleAt_totalTransform_ι_iff hDW y).mp hres.1, fun j => ?_⟩
      refine Fin.cases ?_ (fun j => ?_) j
      · exact Subscheme.isNormallyFlatAlongAt'_of_isSimpleAt (V := (⊥ : Subscheme X)) (D := W)
          (fun U => bot_le) (Subscheme.isSimpleAt_bot hZ _)
          ((Subscheme.isSimpleAt_totalTransform_ι_iff hDW y).mp hres.1)
      · exact (Subscheme.isNormallyFlatAlongAt'_totalTransform_ι_iff (hDV j) (hWV j) y).mp (hres.2 j)
    · intro y hy
      rw [Subscheme.pts_totalTransform_eq_preimage] at hy
      exact ⟨fun j => (Subscheme.isNormallyFlatAlongAt'_totalTransform_ι_iff (hDV j) (hBV j) y).mpr
        ((h3 _ hy).1 j.succ),
        (Subscheme.isNormallyFlatAlongAt'_totalTransform_ι_iff hDW (show B.IsContainedIn W from hBW) y).mpr
          (h3 _ hy).2⟩
    · have hBns : B.IsNonsingular := hBc.isNonsingular
      have h123' : rest.IsMain123 (mainSystem fun j => Subscheme.strictTransform t (V j))
          (Subscheme.strictTransform t W) := by
        rw [← hsys]; exact h123
      have h4' : rest.IsMain4 (mainSystem fun j => Subscheme.strictTransform t (V j))
          (Subscheme.strictTransform t W) := by
        rw [← hsys]; exact h4
      have ih' := ih t.isAlgebraicScheme
        (t.isNonsingular_and_isNonsingular_exceptional hZ hBns).1
        (Subscheme.strictTransform t D) (fun j => Subscheme.strictTransform t (V j))
        (Subscheme.strictTransform t W)
        (fun j => Subscheme.strictTransform_mono t (hDV j))
        (fun j => MonoidalTransformation.isContainedIn_strictTransform t (hWV j))
        ⟨h123', h4'⟩
      have e1 : (fun j => Subscheme.strictTransform (t.induced D) (Subscheme.totalTransform D.ι (V j))) =
          fun j => Subscheme.totalTransform (Subscheme.strictTransform t D).ι
            (Subscheme.strictTransform t (V j)) :=
        funext fun j => MonoidalTransformation.strictTransform_induced t (hDV j)
      have e2 := MonoidalTransformation.strictTransform_induced t hDW
      show Reach4 rest.length (Subscheme.strictTransform t D).toScheme
        (fun j => Subscheme.strictTransform (t.induced D) (Subscheme.totalTransform D.ι (V j)))
        (Subscheme.strictTransform (t.induced D) (Subscheme.totalTransform D.ι W))
      rw [e1, e2]
      exact ih'

end E4c

/-! ### The export -/

theorem dim_eq_of_iso {A B : Scheme.{u}} (e : A ≅ B) : A.dim = B.dim :=
  dim_eq_of_surjective_closedImmersion e.hom (by
    intro b
    exact ⟨e.inv.base b, by rw [← Scheme.Hom.comp_apply, e.inv_hom_id]; rfl⟩)

/-- A subscheme has at most the dimension of the ambient scheme. -/
theorem Subscheme.dim_le_scheme_dim {Y : Scheme.{u}} (D : Subscheme Y) : D.dim ≤ Y.dim := by
  unfold Subscheme.dim
  rw [Scheme.dim_eq_topologicalKrullDim, Scheme.dim_eq_topologicalKrullDim]
  exact D.ι.isEmbedding.isInducing.topologicalKrullDim_le

/-- The image subscheme `i(V)` is isomorphic to `V` (`i` a closed immersion). -/
theorem Subscheme.nonempty_iso_pushforward {Y Z : Scheme.{u}} (i : Y ⟶ Z) [IsClosedImmersion i]
    (V : Subscheme Y) : Nonempty ((Subscheme.pushforward i V).toScheme ≅ V.toScheme) :=
  ⟨(Subscheme.exists_iso_ker (V.ι ≫ i)).choose⟩

/-- The image subscheme has the dimension of `V`. -/
theorem Subscheme.dim_pushforward {Y Z : Scheme.{u}} (i : Y ⟶ Z) [IsClosedImmersion i] (V : Subscheme Y) :
    (Subscheme.pushforward i V).dim = V.dim := by
  obtain ⟨e⟩ := Subscheme.nonempty_iso_pushforward i V
  exact dim_eq_of_iso e

/-- The image of a reduced subscheme is reduced. -/
theorem Subscheme.isReduced_pushforward {Y Z : Scheme.{u}} (i : Y ⟶ Z) [IsClosedImmersion i]
    {V : Subscheme Y} (hV : V.IsReduced) : (Subscheme.pushforward i V).IsReduced := by
  obtain ⟨e⟩ := Subscheme.nonempty_iso_pushforward i V
  have : AlgebraicGeometry.IsReduced V.toScheme := hV
  exact AlgebraicGeometry.isReduced_of_isOpenImmersion e.hom


/-- **The export of this file** (p. 175): "Since `V̂₀` can be imbedded in a non-singular algebraic scheme, we can
apply the previous result to `V̂_j(r)` (`0 ≤ j ≤ β`) and `Ŵ(r)` so that there exists a prolongation of `{f̂_i}`
satisfying (4), in addition to (1), (2) and (3)."  The data `(V; W)` are those of `V̂₀ = Spec(Ô_{X,x})` at the start of
`{f̂_i}` (in the application `V 0 = ⊥`, the scheme itself; the proof does not need this); the data at the end of `{f̂_i}` reach (4) by a prolongation of some length.
`hAmb` is the previous result (Main Theorem I for a non-singular irreducible ambient scheme, `n < N`). -/
theorem exists_reach4_of_hat [Hironaka.HironakaCitedResults.{u}] (hAmb : ∀ N n : ℕ, n < N → MainTheorem.IAmbient.{u} N n)
    {X : Scheme.{u}} [IsAlgebraicScheme X] (x : X) {Y : Scheme.{u}}
    (ŝ : MonoidalSuccession (AB.xHat0 X x) Y) {β : ℕ} (V : Fin (β + 1) → Subscheme (AB.xHat0 X x))
    (W : Subscheme (AB.xHat0 X x)) (hW : W.IsReduced) (hWV : ∀ j, W.IsContainedIn (V j))
    (hŝ : ŝ.IsMain123Hat V W) :
    ∃ ℓ : ℕ, Reach4 ℓ Y (fun j => ŝ.strictTransform (V j)) (ŝ.strictTransform W) := by
  have hŶ : IsAlgebraicScheme (AB.xHat0 X x) := AB.isAlgebraicScheme_xHat0 X x
  have := isHironakaBase_stalk X x
  have : IsHironakaBase (AB.Shat X x) := IsHironakaBase.adicCompletion_maximalIdeal _
  obtain ⟨n, hn⟩ := exists_natCast_eq_ringKrullDim (AB.Shat X x)
  have hdimŶ : (AB.xHat0 X x).dim = n := (dim_Spec_eq _).trans hn
  obtain ⟨N, Z, i, hnN, hZ, hi⟩ := exists_closedImmersion_isAmbient X x n
  have hdim : (AB.xHat0 X x).dim < N := by rw [hdimŶ]; exact_mod_cast hnN
  obtain ⟨Z', i', hi', hZ'⟩ :=
    exists_isAmbient_closedImmersion_of_succession hZ hŶ i hdim ŝ hŝ.hasNonsingularCenters
  have hdimY : Y.dim ≤ n := ŝ.dim_le.trans hdimŶ.le
  set Wh := ŝ.strictTransform W with hWh
  set Vh : Fin (β + 1) → Subscheme Y := fun j => ŝ.strictTransform (V j) with hVh
  by_cases hemp : Wh.pts = ∅
  · refine ⟨0, ?_, fun j y hy => ?_⟩
    · exact Subscheme.isNonsingular_of_forall_isSimpleAt fun y hy => by rw [hemp] at hy; exact hy.elim
    · rw [hemp] at hy; exact hy.elim
  · have hne : Wh.dim ≠ ⊥ := fun h => hemp ((Subscheme.dim_eq_bot_iff _).mp h)
    have hle : Wh.dim ≤ (n : WithBot ℕ∞) := (Subscheme.dim_le_scheme_dim Wh).trans hdimY
    obtain ⟨n', hn'eq, hn'le⟩ := LocSucc.exists_nat_of_le hne hle
    have hn'N : n' < N := lt_of_le_of_lt hn'le hnN
    have hred : Wh.IsReduced := ŝ.isReduced_strictTransform_of_isReduced _ hW
    -- the data on the ambient scheme `Z'`
    have hcont : ∀ j, (Subscheme.pushforward i' Wh).IsContainedIn (Subscheme.pushforward i' (Vh j)) :=
      fun j U => Subscheme.pushforward_mono i'
        (show Vh j ≤ Wh from fun U => ŝ.isContainedIn_strictTransform (hWV j) U) U
    obtain ⟨Y'', sZ, hsZ⟩ := hAmb N n' hn'N Z' hZ' (β + 1) (fun j => Subscheme.pushforward i' (Vh j))
      (Subscheme.pushforward i' Wh) (Subscheme.isReduced_pushforward i' hred)
      ((Subscheme.dim_pushforward i' Wh).trans hn'eq) hcont
    obtain ⟨e, he⟩ := Subscheme.exists_iso_ker i'
    have hR := sZ.reach4_of_isMainI hZ'.1 hZ'.2.1 (i'.ker) (fun j => Subscheme.pushforward i' (Vh j))
      (Subscheme.pushforward i' Wh) (fun j => Subscheme.ker_le_pushforward i' _) hcont hsZ
    have hcomp : e.symm.hom ≫ (Subscheme.ι i'.ker) = i' := by
      rw [Iso.symm_hom]
      show e.inv ≫ i'.ker.subschemeι = i'
      rw [← he, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]
    refine ⟨sZ.length, Reach4.of_iso sZ.length e.symm Vh
      (fun j => Subscheme.totalTransform (Subscheme.ι i'.ker) (Subscheme.pushforward i' (Vh j))) Wh
      (Subscheme.totalTransform (Subscheme.ι i'.ker) (Subscheme.pushforward i' Wh)) (fun j U => ?_) (fun j => ?_) ?_ hR⟩
    · exact Scheme.IdealSheafData.comap_mono _ (show Subscheme.pushforward i' (Vh j) ≤ Subscheme.pushforward i' Wh
        from fun U => hcont j U) U
    · rw [← Subscheme.totalTransform_comp, hcomp, Subscheme.totalTransform_pushforward]
    · rw [← Subscheme.totalTransform_comp, hcomp, Subscheme.totalTransform_pushforward]


end Hironaka
