/-
Copyright (c) 2026 Daattavya Aggarwal, Minhyong Kim, Oisin Kim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daattavya Aggarwal, Minhyong Kim, Oisin Kim
-/
module

public import Hironaka.Ch0.BlowingUpModules
public import Mathlib.CategoryTheory.Limits.Shapes.FiniteLimits
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
public import Mathlib.Geometry.RingedSpace.OpenImmersion
public import Mathlib.Topology.Category.TopCat.Opens
public import Mathlib.Topology.Sheaves.SheafCondition.Sites

/-!
# Restriction of sheaves of modules along open immersions of locally ringed spaces

Infrastructure used in the derivation of assertions (a) and (b) of p. 124 of the paper; it proves no claim of the paper.

Mathlib has the restriction functor of sheaves of modules along an open immersion only for schemes
(`AlgebraicGeometry.Scheme.Modules.restrictFunctor`).  The paper's category `ℛ` consists of locally ringed spaces, and
`OModules X` is the category of sheaves of modules on a locally ringed space (`Hironaka/Ch0/BlowingUpModules.lean`), so
the construction is repeated here for `LocallyRingedSpace`, in the same way.

* `Hironaka.OModules.restrictFunctor g`: restriction `OModules X ⥤ OModules Y` along an open immersion `g : Y ⟶ X`,
  a pushforward along the functor `g.opensFunctor`, whose sections over `U` are those over `g '' U`;
* `Hironaka.OModules.restrictFunctorIsoPullback g`: it is isomorphic to the inverse image `OModules.pullback g`
  (the right adjoint `OModules.pushforward g` has an invertible counit, so that adjoint uniqueness applies);
* `isQuasicoherent_pullback_of_isOpenImmersion`, `isCoherent_pullback_of_isOpenImmersion` (finite presentation) and
  `isInvertible_pullback_of_isOpenImmersion`: these properties of `ℛ`-modules are preserved by the inverse image along
  an open immersion.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite

noncomputable section

universe u

namespace Hironaka

universe v₁ v₂ u₁ u₂

open SheafOfModules in
set_option backward.isDefEq.respectTransparency false in
/-- A finitely presented sheaf of modules stays finitely presented under the direct image along a left adjoint
continuous and cocontinuous functor `G` with an invertible comparison of the structure sheaves (the analogue of
Mathlib's `SheafOfModules.isQuasicoherent_pushforward_of_isLeftAdjoint`, whose proof it follows: the local
presentations are carried along and their numbers of generators and relations are unchanged). -/
lemma isFinitePresentation_pushforward_of_isLeftAdjoint
    {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}
    {D : Type u₂} [Category.{v₂, u₂} D] {K : GrothendieckTopology D}
    {S : Sheaf K RingCat.{u}} [∀ (X : D), (K.over X).WEqualsLocallyBijective AddCommGrpCat]
    [∀ X, HasWeakSheafify (J.over X) AddCommGrpCat.{u}]
    [∀ X, (J.over X).WEqualsLocallyBijective AddCommGrpCat.{u}]
    [∀ (X : C), HasSheafify (J.over X) AddCommGrpCat.{u}]
    [∀ (X : D), HasSheafify (K.over X) AddCommGrpCat.{u}]
    (G : D ⥤ C) [G.IsContinuous K J] [G.IsCocontinuous K J]
    (φ : S ⟶ (G.sheafPushforwardContinuous RingCat.{u} K J).obj R)
    (η : (SheafOfModules.pushforward φ).obj (SheafOfModules.unit R) ≅ SheafOfModules.unit S)
    [G.IsLeftAdjoint] [IsIso φ]
    [∀ X, Functor.IsContinuous (Over.post (X := X) G) (K.over _) (J.over _)]
    [Limits.HasPullbacks C] [Limits.HasPullbacks D]
    {M : SheafOfModules.{u} R} [SheafOfModules.IsFinitePresentation M] :
    SheafOfModules.IsFinitePresentation ((SheafOfModules.pushforward φ).obj M) := by
  have h : ∀ (X : D) (Y : C) (f : G.obj X ⟶ Y),
      Limits.PreservesColimitsOfSize.{u, u} <|
      SheafOfModules.pushforward.{u} (R := (R.over Y)) (F := Over.post (X := X) G ⋙ Over.map f)
        (((Over.forget X).sheafPushforwardContinuous RingCat.{u} (K.over X) K).map φ) := by
    intro X Y f
    let G' := Over.post (X := X) G ⋙ Over.map f
    have : G'.IsContinuous (K.over X) (J.over Y) := Functor.isContinuous_comp _ _ _ (J.over _) _
    have : G'.IsCocontinuous (K.over X) (J.over Y) := isCocontinuous_comp _ _ _ (J.over _)
    let a : S.over X ⟶
        (G'.sheafPushforwardContinuous RingCat.{u} (K.over X) (J.over Y)).obj (R.over Y) :=
      ((Over.forget X).sheafPushforwardContinuous RingCat.{u} (K.over X) K).map φ
    have : (SheafOfModules.pushforward.{u} a).IsLeftAdjoint := isLeftAdjoint_pushforward_of_isIso a
    infer_instance
  obtain ⟨σ, hσ⟩ := IsFinitePresentation.exists_quasicoherentData M
  refine ⟨⟨(σ.pushforward G φ η h).shrink, ⟨fun i => ?_⟩⟩⟩
  show ((σ.pushforward G φ η h).presentation i.2.choose).IsFinite
  generalize i.2.choose = j
  obtain ⟨X', i', f'⟩ := j
  have := hσ.isFinite_presentation i'
  refine ⟨⟨?_⟩, ⟨?_⟩⟩
  · exact (inferInstance : Finite (σ.presentation i').generators.I)
  · exact (inferInstance : Finite (σ.presentation i').relations.I)

end Hironaka

namespace Hironaka.OModules

variable {X Y : LocallyRingedSpace.{u}}

section OpensFunctor

variable (g : Y ⟶ X) [LocallyRingedSpace.IsOpenImmersion g]

/-- The underlying map of an open immersion of locally ringed spaces is an open embedding. -/
lemma isOpenEmbedding_base : Topology.IsOpenEmbedding g.base :=
  PresheafedSpace.IsOpenImmersion.base_open (f := g.toHom)

/-- The functor `Opens Y ⥤ Opens X` taking an open set to its image under an open immersion `g : Y ⟶ X`. -/
abbrev opensFunctor : Opens ↑↑Y.toPresheafedSpace ⥤ Opens ↑↑X.toPresheafedSpace :=
  SheafedSpace.IsOpenImmersion.opensFunctor g.toShHom

/-- The image-preimage adjunction of an open immersion of locally ringed spaces. -/
def opensFunctorAdjunction : opensFunctor g ⊣ Opens.map g.base :=
  IsOpenMap.adjunction (isOpenEmbedding_base g).isOpenMap

/-- `g '' (-)` is a left adjoint. -/
instance : (opensFunctor g).IsLeftAdjoint :=
  (opensFunctorAdjunction g).isLeftAdjoint

/-- `g '' (-)` is cocontinuous for the open-cover topologies. -/
instance : (opensFunctor g).IsCocontinuous (Opens.grothendieckTopology ↑↑Y.toPresheafedSpace)
    (Opens.grothendieckTopology ↑↑X.toPresheafedSpace) := by
  rw [(opensFunctorAdjunction g).isCocontinuous_iff_coverPreserving]
  exact coverPreserving_opens_map g.base

/-- `g '' (-)` is continuous for the open-cover topologies. -/
instance : (opensFunctor g).IsContinuous (Opens.grothendieckTopology ↑↑Y.toPresheafedSpace)
    (Opens.grothendieckTopology ↑↑X.toPresheafedSpace) :=
  (isOpenEmbedding_base g).functor_isContinuous

/-- The continuity of `Opens.map g.base`, in the form in which it is used by `pushforwardPushforwardAdj`. -/
instance : (Opens.map (X := Y.toTopCat) (Y := X.toTopCat) g.base).IsContinuous
    (Opens.grothendieckTopology ↑↑X.toPresheafedSpace)
    (Opens.grothendieckTopology ↑↑Y.toPresheafedSpace) :=
  instIsContinuousOpensCarrierMapGrothendieckTopology g.base

/-- `g '' (-)` preserves pullbacks (intersections). -/
instance : Limits.PreservesLimitsOfShape Limits.WalkingCospan (opensFunctor g) :=
  inferInstanceAs (Limits.PreservesLimitsOfShape Limits.WalkingCospan
    (isOpenEmbedding_base g).functor)

/-- `g '' (-)` preserves `1`-hypercovers. -/
instance : (opensFunctor g).PreservesOneHypercovers (Opens.grothendieckTopology ↑↑Y.toPresheafedSpace)
    (Opens.grothendieckTopology ↑↑X.toPresheafedSpace) :=
  Functor.PreservesOneHypercovers.of_coverPreserving (F := opensFunctor g) (isOpenEmbedding_base g).isOpenMap.coverPreserving

end OpensFunctor

/-- The comparison `O_Y ⟶ (g.opensFunctor)^* O_X` of presheaves of rings along an open immersion `g : Y ⟶ X`,
given by the inverses of the isomorphisms `X(g '' U) ≅ Y(U)`. -/
def restrictPresheafHom (g : Y ⟶ X) [LocallyRingedSpace.IsOpenImmersion g] :
    Y.presheaf ⟶ (opensFunctor g).op ⋙ X.presheaf where
  app U := SheafedSpace.IsOpenImmersion.invApp g.toShHom U.unop
  naturality _ _ i := SheafedSpace.IsOpenImmersion.inv_naturality g.toShHom i

variable (g : Y ⟶ X) [LocallyRingedSpace.IsOpenImmersion g]

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- Restriction of an `O_X`-module along an open immersion `g : Y ⟶ X`: its sections over `U` are those of the
module over `g '' U`.  It is isomorphic to the inverse image (`restrictFunctorIsoPullback`). -/
def restrictFunctor : OModules X ⥤ OModules Y :=
  SheafOfModules.pushforward (F := opensFunctor g)
    ⟨Functor.whiskerRight (restrictPresheafHom g) (forget₂ CommRingCat RingCat)⟩

/-- Restriction is left adjoint to direct image along an open immersion. -/
def restrictAdjunction : restrictFunctor g ⊣ pushforward g := by
  refine SheafOfModules.pushforwardPushforwardAdj (opensFunctorAdjunction g) _ (ringCatSheafHom g) ?_ ?_
  · ext U x
    exact congr($((SheafedSpace.IsOpenImmersion.app_invApp g.toShHom U.unop).symm).hom x)
  · ext U x
    have : SheafedSpace.IsOpenImmersion.invApp g.toShHom U.unop ≫ (InducedCategory.Hom.hom g.toShHom).c.app _ ≫
        Y.presheaf.map (eqToHom (by simp [Opens.map_def,
          Set.preimage_image_eq _ (isOpenEmbedding_base g).injective])).op = 𝟙 _ := by
      rw [SheafedSpace.IsOpenImmersion.invApp_app_assoc, ← Functor.map_comp, ← Y.presheaf.map_id]
      rfl
    exact congr($(this).hom x)

/-- The preimage of the image of an open set under an open immersion is that open set. -/
lemma preimage_image_eq (U : Opens Y) : (Opens.map g.base).obj ((opensFunctor g).obj U) = U :=
  Opens.ext (Set.preimage_image_eq _ (isOpenEmbedding_base g).injective)

/-- The counit of `restrictAdjunction g` is invertible: restricting a direct image gives back the module. -/
instance (M : OModules Y) : IsIso ((restrictAdjunction g).counit.app M) := by
  have h : IsIso ((SheafOfModules.forget (ringCatSheaf Y)).map
      ((restrictAdjunction g).counit.app M)) := by
    refine (isIso_iff_of_reflects_iso _ (PresheafOfModules.toPresheaf _)).mp ?_
    have : ∀ U, IsIso (((PresheafOfModules.toPresheaf _).map
      ((SheafOfModules.forget (ringCatSheaf Y)).map ((restrictAdjunction g).counit.app M))).app U) := by
      intro U
      change IsIso (M.val.presheaf.map ((opensFunctorAdjunction g).unit.app U.unop).op)
      have e : (opensFunctorAdjunction g).unit.app U.unop =
          eqToHom (preimage_image_eq g U.unop).symm := Subsingleton.elim _ _
      rw [e]
      exact (M.val.presheaf.mapIso (eqToIso (preimage_image_eq g U.unop).symm).op).isIso_hom
    exact NatIso.isIso_of_isIso_app _
  exact (SheafOfModules.fullyFaithfulForget _).reflectsIsomorphisms.reflects _

/-- Restriction is isomorphic to the inverse image (adjoint uniqueness). -/
def restrictFunctorIsoPullback : restrictFunctor g ≅ pullback g :=
  (restrictAdjunction g).leftAdjointUniq (pullbackPushforwardAdjunction g)

/-- Restriction along an open immersion is a left adjoint (of the direct image). -/
instance : (restrictFunctor g).IsLeftAdjoint := (restrictAdjunction g).isLeftAdjoint

/-- The isomorphism `X(g '' U) ≅ Y(U)` of an open immersion `g : Y ⟶ X`. -/
def appIso (U : Opens Y) :
    X.presheaf.obj (op ((opensFunctor g).obj U)) ≅ Y.presheaf.obj (op U) :=
  (asIso (SheafedSpace.IsOpenImmersion.invApp g.toShHom U)).symm

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- Restriction along an open immersion `g : Y ⟶ X` sends `O_X` to `O_Y`. -/
def restrictUnitIso : (restrictFunctor g).obj (unit X) ≅ unit Y := by
  refine (SheafOfModules.fullyFaithfulForget _).preimageIso <| PresheafOfModules.isoMk (fun U ↦ ?_) ?_
  · refine ModuleCat.isoMk
      ((forget₂ CommRingCat RingCat ⋙ forget₂ _ AddCommGrpCat).mapIso (appIso g U.unop)) ?_
    intro (r : Y.presheaf.obj U)
    ext (x : X.presheaf.obj (op ((opensFunctor g).obj U.unop)))
    change r * (appIso g U.unop).hom.hom x =
      (appIso g U.unop).hom.hom ((appIso g U.unop).inv.hom r * x)
    simp
  · intro U V i
    have : X.presheaf.map ((opensFunctor g).op.map i) ≫ (appIso g V.unop).hom =
        (appIso g U.unop).hom ≫ Y.presheaf.map i := by
      simp [← cancel_mono (appIso g V.unop).inv, appIso]
    ext x
    exact congr($(this).hom x)

/-- The comparison `O_Y ⟶ (g.opensFunctor)^* O_X` of sheaves of rings, as a morphism of sheaves of rings. -/
def restrictRingCatSheafHom : ringCatSheaf Y ⟶
    ((opensFunctor g).sheafPushforwardContinuous _ _ _).obj (ringCatSheaf X) :=
  ⟨Functor.whiskerRight (restrictPresheafHom g) (forget₂ CommRingCat RingCat)⟩

set_option backward.isDefEq.respectTransparency false in
/-- The comparison of sheaves of rings along an open immersion is an isomorphism. -/
instance : IsIso (restrictRingCatSheafHom g) := by
  have : ∀ U, IsIso ((restrictPresheafHom g).app U) := fun U =>
    inferInstanceAs (IsIso (SheafedSpace.IsOpenImmersion.invApp g.toShHom U.unop))
  have : IsIso (restrictPresheafHom g) := NatIso.isIso_of_isIso_app _
  rw [← isIso_iff_of_reflects_iso _ (ObjectProperty.ι _)]
  dsimp [restrictRingCatSheafHom]
  infer_instance

set_option backward.isDefEq.respectTransparency false in
/-- Restriction along an open immersion preserves quasi-coherence (as for schemes, by the pushforward along the
left adjoint `g '' (-)`). -/
theorem isQuasicoherent_restrictFunctor (M : OModules X)
    [SheafOfModules.IsQuasicoherent.{u, u, u} (R := ringCatSheaf X) M] :
    SheafOfModules.IsQuasicoherent.{u, u, u} (R := ringCatSheaf Y) ((restrictFunctor g).obj M) :=
  haveI : IsIso (C := Sheaf (Opens.grothendieckTopology ↑↑Y.toPresheafedSpace) RingCat.{u})
    (restrictRingCatSheafHom g) := inferInstanceAs (IsIso (restrictRingCatSheafHom g))
  haveI : ∀ U : Opens ↑↑Y.toPresheafedSpace,
      (Over.post (opensFunctor g)).IsContinuous
        ((Opens.grothendieckTopology ↑↑Y.toPresheafedSpace).over U)
        ((Opens.grothendieckTopology ↑↑X.toPresheafedSpace).over ((opensFunctor g).obj U)) :=
    fun _ => inferInstance
  SheafOfModules.isQuasicoherent_pushforward_of_isLeftAdjoint.{u} (opensFunctor g)
    (restrictRingCatSheafHom g) (restrictUnitIso g)

set_option backward.isDefEq.respectTransparency false in
/-- Restriction along an open immersion preserves finite presentation. -/
theorem isFinitePresentation_restrictFunctor (M : OModules X)
    [SheafOfModules.IsFinitePresentation.{u, u, u} (R := ringCatSheaf X) M] :
    SheafOfModules.IsFinitePresentation.{u, u, u} (R := ringCatSheaf Y) ((restrictFunctor g).obj M) :=
  haveI : IsIso (C := Sheaf (Opens.grothendieckTopology ↑↑Y.toPresheafedSpace) RingCat.{u})
    (restrictRingCatSheafHom g) := inferInstanceAs (IsIso (restrictRingCatSheafHom g))
  Hironaka.isFinitePresentation_pushforward_of_isLeftAdjoint (opensFunctor g)
    (restrictRingCatSheafHom g) (restrictUnitIso g)

set_option backward.isDefEq.respectTransparency false in
/-- The inverse image of a quasi-coherent module along an open immersion is quasi-coherent (it is the restriction,
up to isomorphism). -/
theorem isQuasicoherent_pullback_of_isOpenImmersion (g : Y ⟶ X)
    [LocallyRingedSpace.IsOpenImmersion g] (J : OModules X)
    (h : (RModule.mk X J).IsQuasicoherent) : (RModule.mk Y ((pullback g).obj J)).IsQuasicoherent := by
  have h' : SheafOfModules.IsQuasicoherent.{u, u, u} (R := ringCatSheaf X) J := h
  have := isQuasicoherent_restrictFunctor g J
  exact (SheafOfModules.isQuasicoherent (ringCatSheaf Y)).prop_of_iso
    ((restrictFunctorIsoPullback g).app J) this

set_option backward.isDefEq.respectTransparency false in
/-- The inverse image of a coherent module (a module of finite presentation) along an open immersion is coherent. -/
theorem isCoherent_pullback_of_isOpenImmersion (g : Y ⟶ X)
    [LocallyRingedSpace.IsOpenImmersion g] (J : OModules X)
    (h : (RModule.mk X J).IsCoherent) : (RModule.mk Y ((pullback g).obj J)).IsCoherent := by
  have h' : SheafOfModules.IsFinitePresentation.{u, u, u} (R := ringCatSheaf X) J := h
  have := isFinitePresentation_restrictFunctor g J
  exact (SheafOfModules.isFinitePresentation (ringCatSheaf Y)).prop_of_iso
    ((restrictFunctorIsoPullback g).app J) this

/-- The condition of the definition of `RModule.IsInvertibleAt` on a section `s` of `N` over `U`: for every open
`V ⊆ U`, `a ↦ a • s|_V` is a bijection `O(V) → N(V)`. -/
def IsInvertibleSection (N : OModules Y) (U : Opens Y) (s : N.val.obj (op U)) : Prop :=
  ∀ (V : Opens Y) (hV : V ≤ U),
    Function.Bijective (fun a : (ringCatSheaf Y).obj.obj (op V) =>
      a • ((N.val.map (homOfLE hV).op).hom s))

/-- The invertibility condition on a section is transported along an isomorphism of modules. -/
theorem IsInvertibleSection.of_iso {N N' : OModules Y} (e : N ≅ N') {U : Opens Y}
    {s : N.val.obj (op U)} (h : IsInvertibleSection N U s) :
    IsInvertibleSection N' U ((e.hom.val.app (op U)).hom s) := by
  intro V hV
  have key : (fun a : (ringCatSheaf Y).obj.obj (op V) =>
      a • ((N'.val.map (homOfLE hV).op).hom ((e.hom.val.app (op U)).hom s))) =
      (e.hom.val.app (op V)).hom ∘ (fun a : (ringCatSheaf Y).obj.obj (op V) =>
        a • ((N.val.map (homOfLE hV).op).hom s)) := by
    funext a
    have h1 := PresheafOfModules.naturality_apply e.hom.val (homOfLE hV).op s
    have h2 := (e.hom.val.app (op V)).hom.map_smul a ((N.val.map (homOfLE hV).op).hom s)
    exact (congrArg (fun m => a • m) h1.symm).trans h2.symm
  rw [key]
  refine Function.Bijective.comp ?_ (h V hV)
  have : IsIso (e.hom.val.app (op V)) :=
    inferInstanceAs (IsIso (((PresheafOfModules.evaluation _ (op V)).mapIso
      ((SheafOfModules.forget _).mapIso e)).hom))
  exact ConcreteCategory.bijective_of_isIso (e.hom.val.app (op V))

/-- The image of the preimage of an open set under an open immersion is contained in that open set. -/
lemma image_preimage_le (U' : Opens X) :
    (opensFunctor g).obj ((Opens.map g.base).obj U') ≤ U' :=
  fun _ ⟨_, hy, e⟩ => e ▸ hy

set_option backward.isDefEq.respectTransparency false in
/-- The invertibility condition on a section of `J` over `U'` gives the one on the restriction of that section to
`g⁻¹(U')`, as a section of the restriction of `J` (the isomorphisms `Y(V) ≅ X(g '' V)` are bijective). -/
theorem IsInvertibleSection.restrict (J : OModules X) {U' : Opens X} {s' : J.val.obj (op U')}
    (h : IsInvertibleSection J U' s') :
    IsInvertibleSection ((restrictFunctor g).obj J) ((Opens.map g.base).obj U')
      ((J.val.map (homOfLE (image_preimage_le g U')).op).hom s') := by
  intro V hV
  have hV' : (opensFunctor g).obj V ≤ U' :=
    ((opensFunctor g).map (homOfLE hV)).le.trans (image_preimage_le g U')
  have key : (fun a : (ringCatSheaf Y).obj.obj (op V) =>
      a • (((restrictFunctor g).obj J).val.map (homOfLE hV).op).hom
        ((J.val.map (homOfLE (image_preimage_le g U')).op).hom s')) =
      (fun b : (ringCatSheaf X).obj.obj (op ((opensFunctor g).obj V)) =>
        b • ((J.val.map (homOfLE hV').op).hom s')) ∘
      (fun a => (SheafedSpace.IsOpenImmersion.invApp g.toShHom V).hom a) := by
    funext a
    change (show (ringCatSheaf X).obj.obj (op ((opensFunctor g).obj V)) from
      (SheafedSpace.IsOpenImmersion.invApp g.toShHom V).hom a) •
      (J.val.map ((opensFunctor g).map (homOfLE hV)).op).hom
        ((J.val.map (homOfLE (image_preimage_le g U')).op).hom s') = _
    have := PresheafOfModules.map_comp_apply J.val (homOfLE (image_preimage_le g U')).op
      ((opensFunctor g).map (homOfLE hV)).op s'
    have e : (homOfLE (image_preimage_le g U')).op ≫ ((opensFunctor g).map (homOfLE hV)).op =
        (homOfLE hV').op := Subsingleton.elim _ _
    rw [e] at this
    exact congrArg _ this.symm
  rw [key]
  refine Function.Bijective.comp (h _ hV') ?_
  exact ConcreteCategory.bijective_of_isIso (SheafedSpace.IsOpenImmersion.invApp g.toShHom V)

set_option backward.isDefEq.respectTransparency false in
/-- The inverse image of an invertible module along an open immersion is invertible: a generating section `s` over
`U'` restricts to `g⁻¹(U')`, where `a ↦ a • s` is bijective because `Y(V) ≅ X(g '' V)`. -/
theorem isInvertible_pullback_of_isOpenImmersion (g : Y ⟶ X)
    [LocallyRingedSpace.IsOpenImmersion g] (J : OModules X)
    (h : (RModule.mk X J).IsInvertible) : (RModule.mk Y ((pullback g).obj J)).IsInvertible := by
  intro y
  obtain ⟨U', hx, s', hs⟩ := h (g.base y)
  have hs' : IsInvertibleSection J U' s' := hs
  exact ⟨(Opens.map g.base).obj U', hx, _,
    (hs'.restrict g J).of_iso ((restrictFunctorIsoPullback g).app J)⟩

end Hironaka.OModules
