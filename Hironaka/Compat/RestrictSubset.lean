/-
Copyright (c) 2026 Daattavya Aggarwal, Minhyong Kim, Oisin Kim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daattavya Aggarwal, Minhyong Kim, Oisin Kim
-/
module

public import Mathlib.Geometry.RingedSpace.LocallyRingedSpace
public import Mathlib.Geometry.RingedSpace.OpenImmersion
public import Mathlib.Geometry.RingedSpace.Stalks
public import Mathlib.Topology.Sheaves.Functors
public import Mathlib.Topology.Sheaves.Sheafify

/-!
# Compatibility layer: restriction of a (locally) ringed space to an arbitrary subset

Ch. 0 (pp. 117–131) restricts local-ringed spaces to subsets that are not open: the image of the set `X(Ω)` of
geometric points in `X_Ω` (p. 130, "the restriction of `X_Ω` to the image of `f`"), and the support of `O_P/H`
(p. 127, "`O_{P'}` the restriction of `O_P/H` to `P'`").  Mathlib restricts (locally) ringed spaces to open
subsets only (`LocallyRingedSpace.restrict`, along an open embedding).

For a sheafed space `Y` of commutative rings and a subset `T` of its points this file builds the restriction
`Y|T`: the subspace `T` carries the inverse image of the structure sheaf (the sheafification of the presheaf
inverse image `TopCat.Presheaf.pullback`), a morphism `Y|T ⟶ Y` over the inclusion, and an isomorphism of the stalk
of `Y|T` at `t` with the stalk of `Y` at `t`.  For a locally ringed space `X` the stalks of `X|T` are local
(they are isomorphic to those of `X`), so `X|T` is a locally ringed space and `X|T ⟶ X` a morphism of locally
ringed spaces (each stalk map is an isomorphism, hence local).  For an open subset `T` the inclusion is an open
immersion, so `X|T` is isomorphic to Mathlib's restriction of `X` to `T`, compatibly with the inclusions.

## Main definitions

* `AlgebraicGeometry.SheafedSpace.restrictSubset Y T`: the sheafed space `Y|T`;
  `restrictSubsetHom : Y|T ⟶ Y` and `restrictSubsetStalkIso` (the stalk of `Y|T` at `t` is the stalk of `Y`).
* `AlgebraicGeometry.SheafedSpace.restrictSubsetLocallyRingedSpace`: `Y|T` as a locally ringed space when the
  stalks of `Y` at the points of `T` are local rings.
* `AlgebraicGeometry.LocallyRingedSpace.restrictSubset X T` and `ofRestrictSubset X T : X|T ⟶ X`.
* `AlgebraicGeometry.LocallyRingedSpace.restrictSubsetIsoRestrict`: for an open embedding with range `T`,
  `X|T ≅ X.restrict h`.

None of this is a claim of the paper; it is the infrastructure needed to state the paper's restrictions.
-/

@[expose] public section

open CategoryTheory TopologicalSpace Opposite AlgebraicGeometry TopCat

noncomputable section

universe u

namespace AlgebraicGeometry.SheafedSpace

variable (Y : SheafedSpace CommRingCat.{u}) (T : Set Y)

/-- The subset `T` of the points of `Y`, with the subspace topology. -/
abbrev subspace : TopCat.{u} := TopCat.of T

/-- The inclusion of the subspace `T` into the space of `Y`. -/
def subspaceIncl : subspace Y T ⟶ Y.carrier := TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩

/-- The presheaf inverse image of the structure presheaf of `Y` to the subspace `T`
(before sheafification). -/
abbrev restrictSubsetPresheaf : (subspace Y T).Presheaf CommRingCat.{u} :=
  (Presheaf.pullback CommRingCat (subspaceIncl Y T)).obj Y.presheaf

/-- The sheaf of rings on `T` obtained by sheafifying the presheaf inverse image. -/
abbrev restrictSubsetSheaf : (subspace Y T).Sheaf CommRingCat.{u} :=
  (presheafToSheaf (Opens.grothendieckTopology (subspace Y T)) CommRingCat.{u}).obj
    (restrictSubsetPresheaf Y T)

/-- The restriction `Y|T` of a sheafed space of commutative rings to an arbitrary subset `T` of its points: the
subspace `T` with the inverse image of the structure sheaf of `Y`. -/
def restrictSubset : SheafedSpace CommRingCat.{u} where
  carrier := subspace Y T
  presheaf := (restrictSubsetSheaf Y T).obj
  IsSheaf := (restrictSubsetSheaf Y T).property

/-- The canonical map from the stalk of the presheaf inverse image to the stalk of its sheafification is an
isomorphism (sheafification does not change stalks). -/
instance restrictSubset_isIso_stalk_toSheafify (t : subspace Y T) :
    IsIso ((Presheaf.stalkFunctor CommRingCat.{u} t).map
      (CategoryTheory.toSheafify (Opens.grothendieckTopology (subspace Y T))
        (restrictSubsetPresheaf Y T))) :=
  Presheaf.stalkFunctor_map_unit_toSheafify_isIso t (CommRingCat.{u}) (restrictSubsetPresheaf Y T)

/-- The stalk of `Y|T` at a point `t` of `T` is isomorphic to the stalk of `Y` at `t`.  Used to see that the
restriction of a locally ringed space is locally ringed and that the inclusion has invertible stalk maps. -/
def restrictSubsetStalkIso (t : subspace Y T) :
    (restrictSubset Y T).presheaf.stalk t ≅ Y.presheaf.stalk ((subspaceIncl Y T) t) :=
  (asIso ((Presheaf.stalkFunctor CommRingCat.{u} t).map
    (CategoryTheory.toSheafify (Opens.grothendieckTopology (subspace Y T))
      (restrictSubsetPresheaf Y T)))).symm ≪≫
    (Presheaf.stalkPullbackIso CommRingCat.{u} (subspaceIncl Y T) Y.presheaf t).symm

/-- The morphism of presheafed spaces `Y|T ⟶ Y` over the inclusion of `T`: on structure sheaves, the unit
`O_Y ⟶ i_* i⁻¹ O_Y` followed by the pushforward of the sheafification map. -/
def restrictSubsetHom :
    (restrictSubset Y T).toPresheafedSpace ⟶ Y.toPresheafedSpace where
  base := subspaceIncl Y T
  c := (Presheaf.pullbackPushforwardAdjunction CommRingCat.{u} (subspaceIncl Y T)).unit.app
      Y.presheaf ≫
    (Presheaf.pushforward CommRingCat.{u} (subspaceIncl Y T)).map
      (CategoryTheory.toSheafify (Opens.grothendieckTopology (subspace Y T))
        (restrictSubsetPresheaf Y T))

lemma restrictSubsetStalkIso_inv (t : subspace Y T) :
    (restrictSubsetStalkIso Y T t).inv =
      Presheaf.stalkPullbackHom CommRingCat.{u} (subspaceIncl Y T) Y.presheaf t ≫
        (Presheaf.stalkFunctor CommRingCat.{u} t).map
          (CategoryTheory.toSheafify (Opens.grothendieckTopology (subspace Y T))
            (restrictSubsetPresheaf Y T)) := rfl

/-- The stalk map of `Y|T ⟶ Y` at `t` is the inverse of `restrictSubsetStalkIso`. -/
lemma restrictSubsetHom_stalkMap (t : subspace Y T) :
    (restrictSubsetHom Y T).stalkMap t = (restrictSubsetStalkIso Y T t).inv := by
  refine Presheaf.stalk_hom_ext _ fun U hU => ?_
  refine (PresheafedSpace.stalkMap_germ (restrictSubsetHom Y T) U t hU).trans ?_
  rw [restrictSubsetStalkIso_inv]
  erw [Presheaf.germ_stalkPullbackHom_assoc, Presheaf.stalkFunctor_map_germ]
  simp [restrictSubsetHom]
  rfl

/-- Every stalk map of `Y|T ⟶ Y` is an isomorphism: the stalks of the restriction are those of `Y`. -/
instance restrictSubsetHom_isIso_stalkMap (t : subspace Y T) :
    IsIso ((restrictSubsetHom Y T).stalkMap t) := by
  rw [restrictSubsetHom_stalkMap]; exact Iso.isIso_inv _

/-- `Y|T` is a locally ringed space as soon as the stalks of `Y` at the points of `T` are local rings (they are
the stalks of `Y|T`, see `restrictSubsetStalkIso`).  Used for the restrictions of ringed spaces that are
not locally ringed everywhere. -/
def restrictSubsetLocallyRingedSpace (h : ∀ t : T, IsLocalRing (Y.presheaf.stalk (t : Y))) :
    LocallyRingedSpace.{u} where
  toSheafedSpace := restrictSubset Y T
  isLocalRing t := by
    apply @RingEquiv.isLocalRing _ _ _ (h t)
    exact (restrictSubsetStalkIso Y T t).symm.commRingCatIsoToRingEquiv

end AlgebraicGeometry.SheafedSpace

namespace AlgebraicGeometry.LocallyRingedSpace

variable (X : LocallyRingedSpace.{u}) (T : Set X)

/-- The restriction `X|T` of a locally ringed space to an arbitrary subset `T` of its points: the subspace `T`
with the inverse image of the structure sheaf (p. 130: "the restriction of `X_Ω` to the image of `f`").  Its
stalks are local, being isomorphic to those of `X` (`SheafedSpace.restrictSubsetStalkIso`). -/
def restrictSubset : LocallyRingedSpace.{u} :=
  X.toSheafedSpace.restrictSubsetLocallyRingedSpace T fun t => X.isLocalRing t

/-- The canonical morphism `X|T ⟶ X` of locally ringed spaces over the inclusion of `T`. -/
def ofRestrictSubset : X.restrictSubset T ⟶ X :=
  ⟨X.toSheafedSpace.restrictSubsetHom T, fun t => by
    have := X.toSheafedSpace.restrictSubsetHom_isIso_stalkMap T t
    exact isLocalHom_of_isIso ((X.toSheafedSpace.restrictSubsetHom T).stalkMap t)⟩

/-- The underlying map of `ofRestrictSubset` is the inclusion of `T`. -/
@[simp]
lemma ofRestrictSubset_base_apply (t : X.restrictSubset T) :
    (X.ofRestrictSubset T).base t = X.toSheafedSpace.subspaceIncl T t := rfl

/-- Every stalk map of `ofRestrictSubset` is an isomorphism: the stalk of `X|T` at `t` is the stalk of `X`
at `t`. -/
instance (t : X.restrictSubset T) : IsIso ((X.ofRestrictSubset T).stalkMap t) :=
  X.toSheafedSpace.restrictSubsetHom_isIso_stalkMap T t

/-- The stalk of `X|T` at `t ∈ T` is isomorphic to the stalk of `X` at `t`. -/
def restrictSubsetStalkIso (t : X.restrictSubset T) :
    (X.restrictSubset T).presheaf.stalk t ≅ X.presheaf.stalk ((X.ofRestrictSubset T).base t) :=
  X.toSheafedSpace.restrictSubsetStalkIso T t

/-- `ofRestrictSubset` is an embedding of topological spaces. -/
lemma isEmbedding_ofRestrictSubset : Topology.IsEmbedding (X.ofRestrictSubset T).base :=
  Topology.IsEmbedding.subtypeVal

/-- For an open subset `T` the canonical morphism `X|T ⟶ X` is an open immersion. -/
theorem isOpenImmersion_ofRestrictSubset (hT : IsOpen T) :
    LocallyRingedSpace.IsOpenImmersion (X.ofRestrictSubset T) :=
  LocallyRingedSpace.IsOpenImmersion.of_stalk_iso _
    ⟨isEmbedding_ofRestrictSubset X T, by
      change IsOpen (Set.range (Subtype.val : T → X))
      rwa [Subtype.range_coe]⟩

/-- The range of `ofRestrictSubset` is `T`. -/
lemma range_ofRestrictSubset_base : Set.range (X.ofRestrictSubset T).base = T :=
  Subtype.range_coe

lemma range_ofRestrictSubset_eq {U : TopCat.{u}} {f : U ⟶ X.toTopCat} (h : Topology.IsOpenEmbedding f)
    (hT : Set.range f = T) :
    Set.range (X.ofRestrictSubset T).base = Set.range (X.ofRestrict h).base :=
  (range_ofRestrictSubset_base X T).trans hT.symm

/-- For an open embedding `f : U ⟶ X` with range `T`, the restriction `X|T` to the subset is isomorphic to
Mathlib's restriction of `X` along `f`, compatibly with the two inclusions into `X` (`restrictSubsetIsoRestrict_hom_ofRestrict`):
the restriction to an arbitrary subset agrees with Mathlib's on open subsets. -/
def restrictSubsetIsoRestrict {U : TopCat.{u}} {f : U ⟶ X.toTopCat} (h : Topology.IsOpenEmbedding f)
    (hT : Set.range f = T) : X.restrictSubset T ≅ X.restrict h :=
  have := isOpenImmersion_ofRestrictSubset X T (hT ▸ h.isOpen_range)
  have e := range_ofRestrictSubset_eq X T h hT
  { hom := LocallyRingedSpace.IsOpenImmersion.lift (X.ofRestrict h) (X.ofRestrictSubset T) (le_of_eq e)
    inv := LocallyRingedSpace.IsOpenImmersion.lift (X.ofRestrictSubset T) (X.ofRestrict h)
      (le_of_eq e.symm)
    hom_inv_id := by rw [← cancel_mono (X.ofRestrictSubset T)]; simp
    inv_hom_id := by rw [← cancel_mono (X.ofRestrict h)]; simp }

@[reassoc (attr := simp)]
lemma restrictSubsetIsoRestrict_hom_ofRestrict {U : TopCat.{u}} {f : U ⟶ X.toTopCat}
    (h : Topology.IsOpenEmbedding f) (hT : Set.range f = T) :
    (X.restrictSubsetIsoRestrict T h hT).hom ≫ X.ofRestrict h = X.ofRestrictSubset T := by
  have := isOpenImmersion_ofRestrictSubset X T (hT ▸ h.isOpen_range)
  exact LocallyRingedSpace.IsOpenImmersion.lift_fac (X.ofRestrict h) (X.ofRestrictSubset T)
    (le_of_eq (range_ofRestrictSubset_eq X T h hT))

end AlgebraicGeometry.LocallyRingedSpace

end
