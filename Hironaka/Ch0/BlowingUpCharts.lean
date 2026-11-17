/-
Copyright (c) 2026 Daattavya Aggarwal, Minhyong Kim, Oisin Kim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daattavya Aggarwal, Minhyong Kim, Oisin Kim
-/
module

public import Hironaka.Compat.RModuleRestrict
public import Hironaka.Compat.ProjStructureMorphism
public import Hironaka.Compat.InvertibleModules
public import Hironaka.Ch0.BlowingUpProj
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Morphisms.Separated

/-!
# Ch. 0 §2 (pp. 124-125): charts of a blowing-up, schemes and separatedness

> We see that `N = (P, I)` with `P = (𝐏, O_P)` is an `ℛ`-module and that there exists a natural morphism
> `Φ : N → M` ... It is not difficult to prove that `(P, Φ)` is a blowing-up of `M` in the category `𝓜(ℛ)`.
> The basic existence theorem of blowing-up can be thus proved. The assertions of (a) and (b) follow from this
> fact and the result stated in the preceding paragraph. (p. 125)

The paper does not say why the blown-up space is a prescheme, why the structure morphism is separated, or why it
is of finite type when the module is coherent.  The lemmas of this file are gaps filled for that derivation:
they pass from the local description of a morphism `g : P ⟶ X` of locally ringed spaces as
`Proj S_A(J) ⟶ Spec A` over the members of an open cover of `X` (`IsSymmetricProjOver`) to global facts:

* `isPrescheme_of_charts`: `P` is a prescheme (locally affine);
* `property_of_charts`, with its instances `isSeparated_of_charts`, `locallyOfFiniteType_of_charts` and
  `quasiCompact_of_charts`: a property of morphisms of schemes that is local on the target and holds for the
  structure morphisms of `Proj` of symmetric algebras holds for `g`;
* `isScheme_of_blowingUp`, `isAlgebraicSchemeOver_of_blowingUp`, `isAlgebraicPreschemeOver_of_blowingUp`:
  the conclusions of (a) and (b) for the blown-up space, from the previous facts.

These lemmas are used in the derivation of assertions (a) and (b) of p. 124 of the paper; none of them is a
claim of the paper.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
open Hironaka ProjDegreeOne

noncomputable section

universe u

namespace Hironaka.BlowingUpClosed

/-- Over `V ⊆ X`, the morphism `g : P ⟶ X` looks like `Proj(S_A(J)) ⟶ Spec A`: the restriction of `X` to `V` is
isomorphic to `Spec A`, the restriction of `P` to `g⁻¹(V)` is isomorphic to `Proj(S_A(J))`, for a module `J`
satisfying `K A J`, and the two isomorphisms are compatible with `g` and the structure morphism.

Gap filled: the derivation of p. 125 compares a blowing-up, over an affine chart, with Grothendieck's
`P(A, J) ⟶ S(A, J)` (p. 124) without writing the comparison down; this is the statement of locally ringed spaces
that it needs. -/
def IsSymmetricProjOver (K : ∀ A : CommRingCat.{u}, ModuleCat.{u} A → Prop) {P X : LocallyRingedSpace.{u}}
    (g : P ⟶ X) (V : Opens X) : Prop :=
  ∃ (A : CommRingCat.{u}) (J : ModuleCat.{u} A) (_ : K A J)
    (a : X.restrict V.isOpenEmbedding ≅ (Spec A).toLocallyRingedSpace)
    (b : P.restrict ((Opens.map g.base).obj V).isOpenEmbedding ≅
      (Proj (symmetricGrading A J)).toLocallyRingedSpace),
    LocallyRingedSpace.restrictHom g V ≫ a.hom = b.hom ≫ structureLRS (symmetricGrading A J)

/-- Gap filled: a weaker condition on the module `J` gives a weaker `IsSymmetricProjOver`. -/
theorem IsSymmetricProjOver.mono {K K' : ∀ A : CommRingCat.{u}, ModuleCat.{u} A → Prop}
    (hK : ∀ A J, K A J → K' A J) {P X : LocallyRingedSpace.{u}} {g : P ⟶ X} {V : Opens X}
    (h : IsSymmetricProjOver K g V) : IsSymmetricProjOver K' g V := by
  obtain ⟨A, J, hJ, a, b, hab⟩ := h
  exact ⟨A, J, hK A J hJ, a, b, hab⟩

/-- Gap filled: an open immersion into a locally ringed space `X` from a scheme `Z` gives, at the image of any
point of `Z`, an open immersion into `X` from an affine scheme whose range contains that point. -/
lemma exists_spec_openImmersion {X : LocallyRingedSpace.{u}} {Z : Scheme.{u}}
    (f : Z.toLocallyRingedSpace ⟶ X) [LocallyRingedSpace.IsOpenImmersion f] (z : Z) :
    ∃ (R : CommRingCat.{u}) (h : (Spec R).toLocallyRingedSpace ⟶ X),
      f.base z ∈ Set.range h.base ∧ LocallyRingedSpace.IsOpenImmersion h := by
  let 𝒰 := Z.affineOpenCover
  obtain ⟨s, hs⟩ := 𝒰.covers z
  refine ⟨𝒰.X (𝒰.idx z), (𝒰.f (𝒰.idx z)).toLRSHom ≫ f, ⟨s, ?_⟩, inferInstance⟩
  have : (𝒰.f (𝒰.idx z)).base s = z := hs
  simp [this]

/-- Gap filled: a locally ringed space isomorphic to (the underlying space of) a scheme `Y` is itself the
underlying space of a scheme, by transport of the affine charts. -/
def schemeOfIso {Y : Scheme.{u}} {X : LocallyRingedSpace.{u}} (e : Y.toLocallyRingedSpace ≅ X) :
    Scheme.{u} :=
  LocallyRingedSpace.IsOpenImmersion.scheme X fun x => by
    obtain ⟨R, h, hx, hh⟩ := exists_spec_openImmersion e.hom (e.inv.base x)
    refine ⟨R, h, ?_, hh⟩
    rwa [Hironaka.LocallyRingedSpace.base_inv_hom_apply] at hx

/-- Gap filled: the underlying locally ringed space of `schemeOfIso e` is `X`. -/
theorem schemeOfIso_toLocallyRingedSpace {Y : Scheme.{u}} {X : LocallyRingedSpace.{u}}
    (e : Y.toLocallyRingedSpace ≅ X) : (schemeOfIso e).toLocallyRingedSpace = X := rfl

/-- Gap filled: the isomorphism of schemes `Y ≅ schemeOfIso e` with underlying morphism `e.hom`. -/
def schemeIsoOfIso {Y : Scheme.{u}} {X : LocallyRingedSpace.{u}} (e : Y.toLocallyRingedSpace ≅ X) :
    Y ≅ schemeOfIso e :=
  Scheme.fullyFaithfulForgetToLocallyRingedSpace.preimageIso e

/-- Step 7, first half.  Gap filled: `P` is a prescheme (locally affine).  The paper does not say why the blown-up
space is a prescheme; here, over each chart `V` of `X`, `P` restricted to `g⁻¹(V)` is `Proj S_A(J)`, a scheme, so
it is covered by open immersions of spectra. -/
theorem isPrescheme_of_charts {P X : LocallyRingedSpace.{u}} (g : P ⟶ X)
    (h : ∀ x : X, ∃ V : Opens X, x ∈ V ∧ IsSymmetricProjOver (fun _ _ => True) g V) :
    IsPrescheme P := by
  refine ⟨LocallyRingedSpace.IsOpenImmersion.scheme P fun x => ?_, ⟨Iso.refl _⟩⟩
  obtain ⟨V, hxV, A, J, -, a, b, -⟩ := h (g.base x)
  have hx : x ∈ ((Opens.map g.base).obj V) := hxV
  obtain ⟨R, h, hx', hh⟩ := exists_spec_openImmersion
    (b.inv ≫ P.ofRestrict ((Opens.map g.base).obj V).isOpenEmbedding)
    (b.hom.base ⟨x, hx⟩)
  have e : (b.inv ≫ P.ofRestrict ((Opens.map g.base).obj V).isOpenEmbedding).base
      (b.hom.base ⟨x, hx⟩) = x := by
    rw [LocallyRingedSpace.comp_base]
    change (P.ofRestrict _).base (b.inv.base (b.hom.base ⟨x, hx⟩)) = x
    exact congrArg (P.ofRestrict ((Opens.map g.base).obj V).isOpenEmbedding).base
      (Hironaka.LocallyRingedSpace.base_hom_inv_apply b ⟨x, hx⟩)
  rw [e] at hx'
  exact ⟨R, h, hx', hh⟩

/-- Step 7, second half, for a morphism of schemes.  Gap filled: a property of morphisms of schemes that is local
on the target (`IsZariskiLocalAtTarget`) and holds for the structure morphisms of `Proj` of the symmetric algebras
`S_A(J)` (with `K A J`) holds for a morphism `g` that is locally of this form over the members of an open cover of
the target. -/
theorem property_of_charts_scheme (P : MorphismProperty Scheme.{u}) [IsZariskiLocalAtTarget P]
    (K : ∀ A : CommRingCat.{u}, ModuleCat.{u} A → Prop)
    (hP : ∀ (A : CommRingCat.{u}) (J : ModuleCat.{u} A), K A J →
      P (structureMorphism (symmetricGrading A J)))
    {Q X : Scheme.{u}} (g : Q ⟶ X)
    (h : ∀ x : X, ∃ V : X.Opens, x ∈ V ∧ IsSymmetricProjOver K g.toLRSHom V) : P g := by
  choose V hxV hV using h
  rw [IsZariskiLocalAtTarget.iff_of_iSup_eq_top (P := P) V ?_]
  · intro x
    obtain ⟨A, J, hK, a, b, sq⟩ := hV x
    let α : (g ⁻¹ᵁ V x).toScheme ≅ Proj (symmetricGrading A J) :=
      Scheme.fullyFaithfulForgetToLocallyRingedSpace.preimageIso b
    let β : (V x).toScheme ≅ Spec A :=
      Scheme.fullyFaithfulForgetToLocallyRingedSpace.preimageIso a
    have hsq : α.hom ≫ structureMorphism (symmetricGrading A J) = (g ∣_ V x) ≫ β.hom := by
      apply Scheme.Hom.ext'
      have h1 : (g ∣_ V x).toLRSHom = LocallyRingedSpace.restrictHom g.toLRSHom (V x) := by
        refine (cancel_mono (X.toLocallyRingedSpace.ofRestrict (V x).isOpenEmbedding)).1 ?_
        have := congrArg Scheme.Hom.toLRSHom (morphismRestrict_ι g (V x))
        exact this.trans (LocallyRingedSpace.restrictHom_ofRestrict _ _).symm
      simp only [Scheme.Hom.comp_toLRSHom, h1]
      exact (sq).symm
    exact (P.arrow_mk_iso_iff (Arrow.isoMk α β hsq)).mpr (hP A J hK)
  · rw [eq_top_iff]
    intro x _
    simp only [Opens.mem_iSup]
    exact ⟨x, hxV x⟩

/-- Step 7, second half (generic).  Gap filled: the statement of `property_of_charts_scheme` for a morphism `g` of
locally ringed spaces, read as a morphism of schemes through isomorphisms `e`, `e'` with schemes `Y`, `Y'`. -/
theorem property_of_charts (P : MorphismProperty Scheme.{u}) [IsZariskiLocalAtTarget P]
    (K : ∀ A : CommRingCat.{u}, ModuleCat.{u} A → Prop)
    (hP : ∀ (A : CommRingCat.{u}) (J : ModuleCat.{u} A), K A J →
      P (structureMorphism (symmetricGrading A J)))
    {Q X : LocallyRingedSpace.{u}} (g : Q ⟶ X) (Y : Scheme.{u}) (e : Y.toLocallyRingedSpace ≅ X)
    (Y' : Scheme.{u}) (e' : Y'.toLocallyRingedSpace ≅ Q)
    (h : ∀ x : X, ∃ V : Opens X, x ∈ V ∧ IsSymmetricProjOver K g V) :
    P (Scheme.Hom.mk (e'.hom ≫ g ≫ e.inv) : Y' ⟶ Y) := by
  let g' : (schemeOfIso e').toLocallyRingedSpace ⟶ (schemeOfIso e).toLocallyRingedSpace := g
  have key : P (Scheme.Hom.mk g' : schemeOfIso e' ⟶ schemeOfIso e) :=
    property_of_charts_scheme P K hP _ h
  have hmk : (Scheme.Hom.mk (e'.hom ≫ g ≫ e.inv) : Y' ⟶ Y) =
      (schemeIsoOfIso e').hom ≫ Scheme.Hom.mk g' ≫ (schemeIsoOfIso e).inv := by
    apply Scheme.Hom.ext'
    rfl
  rw [hmk, P.cancel_left_of_respectsIso, P.cancel_right_of_respectsIso]
  exact key

/-- Gap filled: `IsZariskiLocalAtTarget` for `LocallyOfFiniteType` (Mathlib proves it through
`HasRingHomProperty`, but the instance is not found by search for this form of the property). -/
instance isZariskiLocalAtTarget_locallyOfFiniteType :
    IsZariskiLocalAtTarget (@LocallyOfFiniteType : MorphismProperty Scheme.{u}) :=
  HasRingHomProperty.instIsZariskiLocalAtTarget @LocallyOfFiniteType (Q := RingHom.FiniteType)

/-- Gap filled: `IsZariskiLocalAtTarget` for `QuasiCompact` (Mathlib proves it through `HasAffineProperty`, but the
instance is not found by search for this form of the property). -/
instance isZariskiLocalAtTarget_quasiCompact :
    IsZariskiLocalAtTarget (@QuasiCompact : MorphismProperty Scheme.{u}) :=
  @HasAffineProperty.instIsZariskiLocalAtTarget _ _
    instHasAffinePropertyQuasiCompactCompactSpaceCarrierCarrierCommRingCat

/-- Gap filled: separatedness of the morphism, from the charts (every `Proj` of a symmetric algebra is separated
over `Spec A`, `isSeparated_structureMorphism`). -/
theorem isSeparated_of_charts {Q X : LocallyRingedSpace.{u}} (g : Q ⟶ X) (Y : Scheme.{u})
    (e : Y.toLocallyRingedSpace ≅ X) (Y' : Scheme.{u}) (e' : Y'.toLocallyRingedSpace ≅ Q)
    (h : ∀ x : X, ∃ V : Opens X, x ∈ V ∧ IsSymmetricProjOver (fun _ _ => True) g V) :
    IsSeparated (Scheme.Hom.mk (e'.hom ≫ g ≫ e.inv) : Y' ⟶ Y) :=
  property_of_charts (P := @IsSeparated) (fun _ _ => True)
    (fun A J _ => isSeparated_structureMorphism (symmetricGrading A J)) g Y e Y' e' h

/-- Gap filled: the morphism is locally of finite type, from the charts, when the modules of the charts are
finitely generated (`locallyOfFiniteType_structureMorphism_symmetric`). -/
theorem locallyOfFiniteType_of_charts {Q X : LocallyRingedSpace.{u}} (g : Q ⟶ X) (Y : Scheme.{u})
    (e : Y.toLocallyRingedSpace ≅ X) (Y' : Scheme.{u}) (e' : Y'.toLocallyRingedSpace ≅ Q)
    (h : ∀ x : X, ∃ V : Opens X, x ∈ V ∧
      IsSymmetricProjOver (fun A J => Module.Finite A J) g V) :
    LocallyOfFiniteType (Scheme.Hom.mk (e'.hom ≫ g ≫ e.inv) : Y' ⟶ Y) :=
  property_of_charts (P := @LocallyOfFiniteType) (fun A J => Module.Finite A J)
    (fun A J _ => locallyOfFiniteType_structureMorphism_symmetric A J) g Y e Y' e' h

/-- Gap filled: the morphism is quasi-compact, from the charts, when the modules of the charts are finitely
generated (`quasiCompact_structureMorphism_symmetric`). -/
theorem quasiCompact_of_charts {Q X : LocallyRingedSpace.{u}} (g : Q ⟶ X) (Y : Scheme.{u})
    (e : Y.toLocallyRingedSpace ≅ X) (Y' : Scheme.{u}) (e' : Y'.toLocallyRingedSpace ≅ Q)
    (h : ∀ x : X, ∃ V : Opens X, x ∈ V ∧
      IsSymmetricProjOver (fun A J => Module.Finite A J) g V) :
    QuasiCompact (Scheme.Hom.mk (e'.hom ≫ g ≫ e.inv) : Y' ⟶ Y) :=
  property_of_charts (P := @QuasiCompact) (fun A J => Module.Finite A J)
    (fun A J _ => quasiCompact_structureMorphism_symmetric A J) g Y e Y' e' h

/-- (a), schemes.  Gap filled: if `M` is a scheme, `N` a prescheme and the comparison morphism
`N.X ⟶ M.X` (read as a morphism of schemes) is separated, then `N` is a scheme in the paper's sense
(separated over `Spec ℤ`), since separated morphisms compose. -/
theorem isScheme_of_blowingUp {M N : RModule.{u}} (Φ : N ⟶ M) (hM : IsScheme M.X) (hN : IsPrescheme N.X)
    (hsep : ∀ (Y : Scheme.{u}) (e : Y.toLocallyRingedSpace ≅ M.X) (Y' : Scheme.{u})
        (e' : Y'.toLocallyRingedSpace ≅ N.X),
        IsSeparated (Scheme.Hom.mk (e'.hom ≫ Φ.f ≫ e.inv) : Y' ⟶ Y)) : IsScheme N.X := by
  obtain ⟨Y, ⟨e⟩, hY⟩ := hM
  obtain ⟨Y', ⟨e'⟩⟩ := hN
  refine ⟨Y', ⟨e'⟩, ?_⟩
  have h1 := hsep Y e Y' e'
  have : Limits.terminal.from Y' =
      (Scheme.Hom.mk (e'.hom ≫ Φ.f ≫ e.inv) : Y' ⟶ Y) ≫ Limits.terminal.from Y :=
    Limits.terminal.hom_ext _ _
  rw [this]
  infer_instance

/-- (b).  Gap filled: if `(M, p)` is an algebraic scheme over `B`, `N` a prescheme, and the comparison morphism
`N.X ⟶ M.X` is separated, locally of finite type and quasi-compact, then `(N, Φ ≫ p)` is an algebraic scheme
over `B`: these properties are stable under composition. -/
theorem isAlgebraicSchemeOver_of_blowingUp (B : Type u) [CommRing B] {M N : RModule.{u}}
    (p : M.X ⟶ specLRS B) (Φ : N ⟶ M) (hM : LocallyRingedSpace.IsAlgebraicSchemeOver B M.X p)
    (hN : IsPrescheme N.X)
    (h : ∀ (Y : Scheme.{u}) (e : Y.toLocallyRingedSpace ≅ M.X) (Y' : Scheme.{u})
        (e' : Y'.toLocallyRingedSpace ≅ N.X),
        IsSeparated (Scheme.Hom.mk (e'.hom ≫ Φ.f ≫ e.inv) : Y' ⟶ Y) ∧
        LocallyOfFiniteType (Scheme.Hom.mk (e'.hom ≫ Φ.f ≫ e.inv) : Y' ⟶ Y) ∧
        QuasiCompact (Scheme.Hom.mk (e'.hom ≫ Φ.f ≫ e.inv) : Y' ⟶ Y)) :
    LocallyRingedSpace.IsAlgebraicSchemeOver B N.X (Φ.f ≫ p) := by
  obtain ⟨hB, Y, e, hL, hQ, hS⟩ := hM
  obtain ⟨Y', ⟨e'⟩⟩ := hN
  obtain ⟨s, l, q⟩ := h Y e Y' e'
  let f1 : Y' ⟶ Y := Scheme.Hom.mk (e'.hom ≫ Φ.f ≫ e.inv)
  let f2 : Y ⟶ Spec (CommRingCat.of B) := Scheme.Hom.mk (e.hom ≫ p)
  have heq : (Scheme.Hom.mk (e'.hom ≫ Φ.f ≫ p) : Y' ⟶ Spec (CommRingCat.of B)) = f1 ≫ f2 := by
    apply Scheme.Hom.ext'
    change e'.hom ≫ Φ.f ≫ p = (e'.hom ≫ Φ.f ≫ e.inv) ≫ e.hom ≫ p
    simp
  refine ⟨hB, Y', e', ?_, ?_, ?_⟩ <;> rw [heq] <;> infer_instance

/-- (b), preschemes.  Gap filled: as `isAlgebraicSchemeOver_of_blowingUp`, without separatedness. -/
theorem isAlgebraicPreschemeOver_of_blowingUp (B : Type u) [CommRing B] {M N : RModule.{u}}
    (p : M.X ⟶ specLRS B) (Φ : N ⟶ M) (hM : LocallyRingedSpace.IsAlgebraicPreschemeOver B M.X p)
    (hN : IsPrescheme N.X)
    (h : ∀ (Y : Scheme.{u}) (e : Y.toLocallyRingedSpace ≅ M.X) (Y' : Scheme.{u})
        (e' : Y'.toLocallyRingedSpace ≅ N.X),
        LocallyOfFiniteType (Scheme.Hom.mk (e'.hom ≫ Φ.f ≫ e.inv) : Y' ⟶ Y) ∧
        QuasiCompact (Scheme.Hom.mk (e'.hom ≫ Φ.f ≫ e.inv) : Y' ⟶ Y)) :
    LocallyRingedSpace.IsAlgebraicPreschemeOver B N.X (Φ.f ≫ p) := by
  obtain ⟨hB, Y, e, hL, hQ⟩ := hM
  obtain ⟨Y', ⟨e'⟩⟩ := hN
  obtain ⟨l, q⟩ := h Y e Y' e'
  let f1 : Y' ⟶ Y := Scheme.Hom.mk (e'.hom ≫ Φ.f ≫ e.inv)
  let f2 : Y ⟶ Spec (CommRingCat.of B) := Scheme.Hom.mk (e.hom ≫ p)
  have heq : (Scheme.Hom.mk (e'.hom ≫ Φ.f ≫ p) : Y' ⟶ Spec (CommRingCat.of B)) = f1 ≫ f2 := by
    apply Scheme.Hom.ext'
    change e'.hom ≫ Φ.f ≫ p = (e'.hom ≫ Φ.f ≫ e.inv) ≫ e.hom ≫ p
    simp
  refine ⟨hB, Y', e', ?_, ?_⟩ <;> rw [heq] <;> infer_instance

end Hironaka.BlowingUpClosed

end
