/-
Copyright (c) 2026 Daattavya Aggarwal, Minhyong Kim, Oisin Kim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daattavya Aggarwal, Minhyong Kim, Oisin Kim
-/
module

public import Mathlib.Geometry.RingedSpace.OpenImmersion
public import Hironaka.Ch0.BlowingUpModules

/-!
# Restriction of `ℛ`-modules to an open set

Infrastructure for the derivation of assertions (a) and (b) of p. 124 of the paper; it proves no claim of
the paper.  For a locally ringed space `X` and an open `V ⊆ X`, `X|V` is Mathlib's `LocallyRingedSpace.restrict`
along the inclusion of `V`; for an `ℛ`-module `M = (X, J)` the restriction `M|V` is `(X|V, ι^* J)` for the
inclusion `ι : X|V ⟶ X` (`RModule.restrict`).  This file proves what is needed to work with `M|V`:

* the isomorphism `restrictIsoOfIso` of the restrictions of two isomorphic locally ringed spaces, and the
  induced morphism `restrictHom g V : g⁻¹(V) ⟶ V` of a morphism `g`;
* the open inclusion `M|V ⟶ M` (`RModule.restrictIncl`), through which a morphism into `M` factors uniquely if
  it lands in `V` (`RModule.restrictLift`), and the induced morphism `N|Φ⁻¹(U) ⟶ M|U` of a morphism
  `Φ : N ⟶ M` (`RModule.restrictMap`);
* transport of a module along an isomorphism of the underlying space (`RModule.transport`,
  `RModule.transportIso`), and the isomorphism of `ℛ`-modules given by an isomorphism of sheaves of modules on
  the same space (`RModule.ofModuleIso`);
* a blowing-up composed with an isomorphism of its target is a blowing-up (`isBlowingUp_comp_iso`).

The composition of `ℛ`-modules is the one given by the isomorphisms `f^* g^* ≅ (f ≫ g)^*`; all identities
below are checked with the coherence lemmas of `OModules` (`pseudofunctor_associativity`, unitality).
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite

noncomputable section

universe u

namespace Hironaka

namespace LocallyRingedSpace

/-- The range of the inclusion `X|V ⟶ X` is `V`. -/
lemma range_ofRestrict_base {X : LocallyRingedSpace.{u}} (V : Opens X) :
    Set.range (X.ofRestrict V.isOpenEmbedding).base = (V : Set X) := by
  ext x
  constructor
  · rintro ⟨⟨y, hy⟩, rfl⟩
    exact hy
  · intro hx
    exact ⟨⟨x, hx⟩, rfl⟩

/-- On points, `e.inv` is a left inverse of `e.hom`. -/
lemma base_hom_inv_apply {X X' : LocallyRingedSpace.{u}} (e : X ≅ X') (x : X) :
    e.inv.base (e.hom.base x) = x := by
  simp

/-- On points, `e.inv` is a right inverse of `e.hom`. -/
lemma base_inv_hom_apply {X X' : LocallyRingedSpace.{u}} (e : X ≅ X') (x : X') :
    e.hom.base (e.inv.base x) = x := by
  simp

/-- The image of `g⁻¹(V)` under `g` lies in `V`. -/
lemma range_ofRestrict_comp_subset {P X : LocallyRingedSpace.{u}} (g : P ⟶ X) (V : Opens X) :
    Set.range (P.ofRestrict ((Opens.map g.base).obj V).isOpenEmbedding ≫ g).base ⊆
      Set.range (X.ofRestrict V.isOpenEmbedding).base := by
  rintro _ ⟨⟨p, hp⟩, rfl⟩
  exact ⟨⟨g.base p, hp⟩, rfl⟩

/-- Restriction along an isomorphism `e : X ≅ X'`: the restriction of `X` to `e⁻¹(U)` is isomorphic to the
restriction of `X'` to `U`.  It is compatible with the inclusions (`restrictIsoOfIso_hom_ofRestrict`). -/
def restrictIsoOfIso {X X' : LocallyRingedSpace.{u}} (e : X ≅ X') (U : Opens X') :
    X.restrict ((Opens.map e.hom.base).obj U).isOpenEmbedding ≅ X'.restrict U.isOpenEmbedding where
  hom := LocallyRingedSpace.IsOpenImmersion.lift (X'.ofRestrict U.isOpenEmbedding)
    (X.ofRestrict ((Opens.map e.hom.base).obj U).isOpenEmbedding ≫ e.hom)
    (range_ofRestrict_comp_subset e.hom U)
  inv := LocallyRingedSpace.IsOpenImmersion.lift
    (X.ofRestrict ((Opens.map e.hom.base).obj U).isOpenEmbedding)
    (X'.ofRestrict U.isOpenEmbedding ≫ e.inv) (by
      rintro _ ⟨⟨x, hx⟩, rfl⟩
      refine ⟨⟨e.inv.base x, ?_⟩, rfl⟩
      change e.hom.base (e.inv.base x) ∈ U
      rw [base_inv_hom_apply]
      exact hx)
  hom_inv_id := by
    rw [← cancel_mono (X.ofRestrict ((Opens.map e.hom.base).obj U).isOpenEmbedding),
      Category.assoc, LocallyRingedSpace.IsOpenImmersion.lift_fac, ← Category.assoc,
      LocallyRingedSpace.IsOpenImmersion.lift_fac]
    simp
  inv_hom_id := by
    rw [← cancel_mono (X'.ofRestrict U.isOpenEmbedding), Category.assoc,
      LocallyRingedSpace.IsOpenImmersion.lift_fac, ← Category.assoc,
      LocallyRingedSpace.IsOpenImmersion.lift_fac]
    simp

/-- The isomorphism `restrictIsoOfIso e U` commutes with the inclusions of the restrictions. -/
@[reassoc (attr := simp)]
theorem restrictIsoOfIso_hom_ofRestrict {X X' : LocallyRingedSpace.{u}} (e : X ≅ X') (U : Opens X') :
    (restrictIsoOfIso e U).hom ≫ X'.ofRestrict U.isOpenEmbedding =
      X.ofRestrict ((Opens.map e.hom.base).obj U).isOpenEmbedding ≫ e.hom :=
  LocallyRingedSpace.IsOpenImmersion.lift_fac _ _ (range_ofRestrict_comp_subset e.hom U)

/-- The morphism `g⁻¹(V) ⟶ V` induced by `g : P ⟶ X`, between the restrictions to `V` and to its inverse
image. -/
def restrictHom {P X : LocallyRingedSpace.{u}} (g : P ⟶ X) (V : Opens X) :
    P.restrict ((Opens.map g.base).obj V).isOpenEmbedding ⟶ X.restrict V.isOpenEmbedding :=
  LocallyRingedSpace.IsOpenImmersion.lift (X.ofRestrict V.isOpenEmbedding)
    (P.ofRestrict ((Opens.map g.base).obj V).isOpenEmbedding ≫ g)
    (range_ofRestrict_comp_subset g V)

/-- The morphism `restrictHom g V` commutes with the inclusions of the restrictions. -/
@[reassoc (attr := simp)]
theorem restrictHom_ofRestrict {P X : LocallyRingedSpace.{u}} (g : P ⟶ X) (V : Opens X) :
    restrictHom g V ≫ X.ofRestrict V.isOpenEmbedding =
      P.ofRestrict ((Opens.map g.base).obj V).isOpenEmbedding ≫ g :=
  LocallyRingedSpace.IsOpenImmersion.lift_fac _ _ (range_ofRestrict_comp_subset g V)

end LocallyRingedSpace

namespace RModule

open OModules

/-- The restriction `M|V` of an `ℛ`-module `M = (X, J)` to an open set `V` of `X`: the restriction `X|V` of the
underlying space, with the inverse image of `J` under the inclusion `X|V ⟶ X`. -/
abbrev restrict (M : RModule.{u}) (V : Opens M.X) : RModule.{u} :=
  ⟨M.X.restrict V.isOpenEmbedding, (OModules.pullback (M.X.ofRestrict V.isOpenEmbedding)).obj M.J⟩

/-- The open inclusion `M|V ⟶ M` of `ℛ`-modules: the inclusion of `X|V` in `X`, with `φ = 𝟙`. -/
def restrictIncl (M : RModule.{u}) (V : Opens M.X) : M.restrict V ⟶ M :=
  ⟨M.X.ofRestrict V.isOpenEmbedding, 𝟙 _, inferInstance⟩

/-- Equal morphisms of `ℛ`-modules have equal `φ`-components, up to the identification of inverse images along
equal morphisms of spaces. -/
lemma φ_eq_of_eq {M N : RModule.{u}} {a b : M ⟶ N} (h : a = b) :
    a.φ = (pullbackCongr (congrArg (fun c : M ⟶ N => c.f) h)).hom.app N.J ≫ b.φ := by
  subst h
  simp [pullbackCongr]

/-- The underlying morphism of spaces of `restrictLift`: the lift of `g.f` through the inclusion `X|V ⟶ X`. -/
def restrictLiftF {M Q : RModule.{u}} (V : Opens M.X) (g : Q ⟶ M) (hg : ∀ q, g.f.base q ∈ V) :
    Q.X ⟶ M.X.restrict V.isOpenEmbedding :=
  LocallyRingedSpace.IsOpenImmersion.lift (M.X.ofRestrict V.isOpenEmbedding) g.f (by
    rintro _ ⟨q, rfl⟩
    exact ⟨⟨g.f.base q, hg q⟩, rfl⟩)

/-- The factorization of `g.f` through the inclusion `X|V ⟶ X`. -/
@[reassoc (attr := simp)]
lemma restrictLiftF_ofRestrict {M Q : RModule.{u}} (V : Opens M.X) (g : Q ⟶ M)
    (hg : ∀ q, g.f.base q ∈ V) :
    restrictLiftF V g hg ≫ M.X.ofRestrict V.isOpenEmbedding = g.f :=
  LocallyRingedSpace.IsOpenImmersion.lift_fac _ _ _

/-- A morphism `g : Q ⟶ M` of `ℛ`-modules whose underlying map lands in `V` factors through the open inclusion
`M|V ⟶ M` (`restrictLift_incl`), and uniquely so (`restrictLift_unique`). -/
def restrictLift {M Q : RModule.{u}} (V : Opens M.X) (g : Q ⟶ M) (hg : ∀ q, g.f.base q ∈ V) :
    Q ⟶ M.restrict V :=
  ⟨restrictLiftF V g hg,
    (pullbackComp (restrictLiftF V g hg) (M.X.ofRestrict V.isOpenEmbedding)).hom.app M.J ≫
      (pullbackCongr (restrictLiftF_ofRestrict V g hg)).hom.app M.J ≫ g.φ,
    inferInstance⟩

/-- The underlying morphism of spaces of `restrictLift` is `restrictLiftF`. -/
lemma restrictLift_f {M Q : RModule.{u}} (V : Opens M.X) (g : Q ⟶ M) (hg : ∀ q, g.f.base q ∈ V) :
    (restrictLift V g hg).f = restrictLiftF V g hg := rfl

/-- The underlying morphism of spaces of `restrictIncl M V` is the inclusion `X|V ⟶ X`. -/
@[simp]
lemma restrictIncl_f (M : RModule.{u}) (V : Opens M.X) :
    (restrictIncl M V).f = M.X.ofRestrict V.isOpenEmbedding := rfl

/-- The factorization `restrictLift V g hg ≫ restrictIncl M V = g`. -/
theorem restrictLift_incl {M Q : RModule.{u}} (V : Opens M.X) (g : Q ⟶ M) (hg : ∀ q, g.f.base q ∈ V) :
    restrictLift V g hg ≫ restrictIncl M V = g := by
  refine Hom.ext' (restrictLiftF_ofRestrict V g hg) ?_
  have key : (pullbackComp (restrictLiftF V g hg) (M.X.ofRestrict V.isOpenEmbedding)).inv.app M.J ≫
      (pullback (restrictLiftF V g hg)).map (𝟙 _) ≫
      (pullbackComp (restrictLiftF V g hg) (M.X.ofRestrict V.isOpenEmbedding)).hom.app M.J ≫
        (pullbackCongr (restrictLiftF_ofRestrict V g hg)).hom.app M.J ≫ g.φ =
      (pullbackCongr (restrictLiftF_ofRestrict V g hg)).hom.app M.J ≫ g.φ := by
    simp
  exact key

/-- Two morphisms into `M|V` that agree after the open inclusion are equal. -/
lemma restrictIncl_cancel {M Q : RModule.{u}} (V : Opens M.X) {a b : Q ⟶ M.restrict V}
    (h : a ≫ restrictIncl M V = b ≫ restrictIncl M V) : a = b := by
  have hf : a.f = b.f := by
    have := congrArg (fun c : Q ⟶ M => c.f) h
    exact (cancel_mono (M.X.ofRestrict V.isOpenEmbedding)).1 this
  have hφ := φ_eq_of_eq h
  obtain ⟨f, φ, _⟩ := a
  obtain ⟨f', φ', _⟩ := b
  change f = f' at hf
  subst hf
  refine Hom.ext' rfl ?_
  change (pullbackComp f (M.X.ofRestrict V.isOpenEmbedding)).inv.app M.J ≫ (pullback f).map (𝟙 _) ≫ φ =
    (pullbackCongr _).hom.app M.J ≫ (pullbackComp f (M.X.ofRestrict V.isOpenEmbedding)).inv.app M.J ≫
      (pullback f).map (𝟙 _) ≫ φ' at hφ
  simp [pullbackCongr] at hφ
  simpa [pullbackCongr] using hφ

/-- Uniqueness of the factorization through `M|V`. -/
theorem restrictLift_unique {M Q : RModule.{u}} (V : Opens M.X) (g : Q ⟶ M) (hg : ∀ q, g.f.base q ∈ V)
    (g' : Q ⟶ M.restrict V) (h : g' ≫ restrictIncl M V = g) : g' = restrictLift V g hg :=
  restrictIncl_cancel V (h.trans (restrictLift_incl V g hg).symm)

/-- The induced morphism `N|Φ⁻¹(U) ⟶ M|U` of `ℛ`-modules of a morphism `Φ : N ⟶ M` and an open `U` of `M.X`. -/
def restrictMap {N M : RModule.{u}} (Φ : N ⟶ M) (U : Opens M.X) :
    N.restrict ((Opens.map Φ.f.base).obj U) ⟶ M.restrict U :=
  restrictLift U (restrictIncl N ((Opens.map Φ.f.base).obj U) ≫ Φ) fun q => q.2

/-- The morphism `restrictMap Φ U` commutes with the open inclusions. -/
theorem restrictMap_incl {N M : RModule.{u}} (Φ : N ⟶ M) (U : Opens M.X) :
    restrictMap Φ U ≫ restrictIncl M U = restrictIncl N _ ≫ Φ :=
  restrictLift_incl _ _ _

/-- The underlying morphism of spaces of `restrictMap Φ U` is `restrictHom Φ.f U`. -/
theorem restrictMap_f {N M : RModule.{u}} (Φ : N ⟶ M) (U : Opens M.X) :
    (restrictMap Φ U).f = LocallyRingedSpace.restrictHom Φ.f U := rfl

/-- The module `M` transported along an isomorphism `e : X' ≅ M.X` of the underlying space: the space `X'` with the
inverse image of `M.J` under `e.hom`. -/
def transport (M : RModule.{u}) {X' : LocallyRingedSpace.{u}} (e : X' ≅ M.X) : RModule.{u} :=
  ⟨X', (OModules.pullback e.hom).obj M.J⟩

/-- The morphism `M.transport e ⟶ M` of `ℛ`-modules over `e.hom`, with `φ = 𝟙`. -/
def transportHom (M : RModule.{u}) {X' : LocallyRingedSpace.{u}} (e : X' ≅ M.X) :
    M.transport e ⟶ M :=
  ⟨e.hom, 𝟙 ((OModules.pullback e.hom).obj M.J),
    by exact inferInstanceAs (Epi (𝟙 ((OModules.pullback e.hom).obj M.J)))⟩

/-- The component `φ` of `transportInv`: the canonical isomorphism
`(e.inv)^* (e.hom)^* J ≅ (e.inv ≫ e.hom)^* J = J`. -/
def transportInvφ (M : RModule.{u}) {X' : LocallyRingedSpace.{u}} (e : X' ≅ M.X) :
    (OModules.pullback e.inv).obj ((OModules.pullback e.hom).obj M.J) ⟶ M.J :=
  (pullbackComp e.inv e.hom).hom.app M.J ≫ (pullbackCongr e.inv_hom_id).hom.app M.J ≫
    (pullbackId M.X).hom.app M.J

/-- `transportInvφ` is an isomorphism. -/
instance (M : RModule.{u}) {X' : LocallyRingedSpace.{u}} (e : X' ≅ M.X) :
    IsIso (transportInvφ M e) := by
  unfold transportInvφ
  infer_instance

/-- The morphism `M ⟶ M.transport e` of `ℛ`-modules over `e.inv`. -/
def transportInv (M : RModule.{u}) {X' : LocallyRingedSpace.{u}} (e : X' ≅ M.X) :
    M ⟶ M.transport e :=
  ⟨e.inv, transportInvφ M e, by exact inferInstanceAs (Epi (transportInvφ M e))⟩

/-- `transportInv` followed by `transportHom` is the identity. -/
lemma transportInv_transportHom (M : RModule.{u}) {X' : LocallyRingedSpace.{u}} (e : X' ≅ M.X) :
    M.transportInv e ≫ M.transportHom e = 𝟙 M := by
  refine Hom.ext' e.inv_hom_id ?_
  have key : (pullbackComp e.inv e.hom).inv.app M.J ≫ (pullback e.inv).map (𝟙 _) ≫
      transportInvφ M e =
      (pullbackCongr e.inv_hom_id).hom.app M.J ≫ (pullbackId M.X).hom.app M.J := by
    simp [transportInvφ]
  exact key

/-- A morphism of `ℛ`-modules `h` with `h.f` and `h.φ` invertible can be cancelled on the right. -/
lemma cancel_of_isIso {A B Q : RModule.{u}} (h : A ⟶ B) [IsIso h.f] [IsIso h.φ] {a b : Q ⟶ A}
    (hab : a ≫ h = b ≫ h) : a = b := by
  have hf : a.f = b.f := (cancel_mono h.f).1 (congrArg (fun c : Q ⟶ B => c.f) hab)
  have hφ := φ_eq_of_eq hab
  obtain ⟨f, φ, _⟩ := a
  obtain ⟨f', φ', _⟩ := b
  change f = f' at hf
  subst hf
  refine Hom.ext' rfl ?_
  change (pullbackComp f h.f).inv.app B.J ≫ (pullback f).map h.φ ≫ φ =
    (pullbackCongr _).hom.app B.J ≫ (pullbackComp f h.f).inv.app B.J ≫ (pullback f).map h.φ ≫ φ'
    at hφ
  simp only [pullbackCongr, eqToIso_refl, Iso.refl_hom, NatTrans.id_app, Category.id_comp] at hφ
  have h1 := (cancel_epi _).1 hφ
  have h2 := (cancel_epi _).1 h1
  simpa [pullbackCongr] using h2

/-- The isomorphism `M.transport e ≅ M` of `ℛ`-modules, over `e.hom` (`transportIso_hom_f`). -/
def transportIso (M : RModule.{u}) {X' : LocallyRingedSpace.{u}} (e : X' ≅ M.X) :
    M.transport e ≅ M where
  hom := M.transportHom e
  inv := M.transportInv e
  hom_inv_id := by
    have : IsIso (M.transportHom e).f := inferInstanceAs (IsIso e.hom)
    have : IsIso (M.transportHom e).φ :=
      inferInstanceAs (IsIso (𝟙 ((OModules.pullback e.hom).obj M.J)))
    apply cancel_of_isIso (M.transportHom e)
    rw [Category.assoc, transportInv_transportHom, Category.comp_id, Category.id_comp]
  inv_hom_id := transportInv_transportHom M e

/-- The underlying morphism of spaces of `transportIso M e` is `e.hom`. -/
theorem transportIso_hom_f (M : RModule.{u}) {X' : LocallyRingedSpace.{u}} (e : X' ≅ M.X) :
    (M.transportIso e).hom.f = e.hom := rfl

/-- The component `φ` of the morphism `RModule.mk X J ⟶ RModule.mk X J'` given by `α : J ≅ J'`. -/
def ofModuleIsoφ {X : LocallyRingedSpace.{u}} {J J' : OModules X} (α : J ≅ J') :
    (OModules.pullback (𝟙 X)).obj J' ⟶ J :=
  (pullbackId X).hom.app J' ≫ α.inv

/-- `ofModuleIsoφ α` is an isomorphism. -/
instance {X : LocallyRingedSpace.{u}} {J J' : OModules X} (α : J ≅ J') : IsIso (ofModuleIsoφ α) := by
  unfold ofModuleIsoφ
  infer_instance

/-- The composite of the `φ`-components of `ofModuleIso α` and `ofModuleIso α.symm` (the cocycle condition
for the composition of `ℛ`-modules over the identity of `X`). -/
lemma ofModuleIsoφ_comp {X : LocallyRingedSpace.{u}} {J J' : OModules X} (α : J ≅ J') :
    (pullbackComp (𝟙 X) (𝟙 X)).inv.app J ≫ (pullback (𝟙 X)).map (ofModuleIsoφ α.symm) ≫
      ofModuleIsoφ α = (pullbackCongr (Category.id_comp (𝟙 X))).hom.app J ≫
        (pullbackId X).hom.app J := by
  have h1 := congr_app (pseudofunctor_left_unitality (𝟙 X)) J
  simp at h1
  have nat := (pullbackId X).hom.naturality α.hom
  simp only [Functor.id_map] at nat
  simp only [ofModuleIsoφ, Iso.symm_inv, Functor.map_comp, Category.assoc]
  rw [reassoc_of% nat, Iso.hom_inv_id, reassoc_of% h1]
  simp [pullbackCongr]

/-- The isomorphism of `ℛ`-modules `(X, J) ≅ (X, J')` given by an isomorphism `α : J ≅ J'` of sheaves of modules
on the same space `X`; it is the identity on `X` (`ofModuleIso_hom_f`). -/
def ofModuleIso {X : LocallyRingedSpace.{u}} {J J' : OModules X} (α : J ≅ J') :
    RModule.mk X J ≅ RModule.mk X J' where
  hom := ⟨𝟙 X, ofModuleIsoφ α, inferInstance⟩
  inv := ⟨𝟙 X, ofModuleIsoφ α.symm, inferInstance⟩
  hom_inv_id := Hom.ext' (Category.id_comp _) (ofModuleIsoφ_comp α)
  inv_hom_id := Hom.ext' (Category.id_comp _) (ofModuleIsoφ_comp α.symm)

/-- The underlying morphism of spaces of `ofModuleIso α` is the identity. -/
theorem ofModuleIso_hom_f {X : LocallyRingedSpace.{u}} {J J' : OModules X} (α : J ≅ J') :
    (ofModuleIso α).hom.f = 𝟙 X := rfl

end RModule

/-- A blowing-up composed with an isomorphism of its target is a blowing-up. -/
theorem isBlowingUp_comp_iso {C : Type*} [Category C] (T : C ⥤ RModule.{u}) {P M M' : C}
    (Φ : P ⟶ M) (e : M ≅ M') (h : IsBlowingUp T Φ) : IsBlowingUp T (Φ ≫ e.hom) where
  invertible := h.invertible
  universal P' Φ' hP' := by
    obtain ⟨Ψ, hΨ, huniq⟩ := h.universal P' (Φ' ≫ e.inv) hP'
    refine ⟨Ψ, ?_, fun Ψ' hΨ' => huniq Ψ' ?_⟩
    · show Ψ ≫ Φ ≫ e.hom = Φ'
      rw [← Category.assoc, hΨ]
      simp
    · change Ψ' ≫ Φ ≫ e.hom = Φ' at hΨ'
      show Ψ' ≫ Φ = Φ' ≫ e.inv
      rw [← hΨ']
      simp

end Hironaka
