/-
Copyright (c) 2026 Daattavya Aggarwal, Minhyong Kim, Oisin Kim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daattavya Aggarwal, Minhyong Kim, Oisin Kim
-/
module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Basic
public import Architect

/-!
# Ch. 0 §2 (pp. 123–129): generalities on blowing-up, `(ℛ/S)`-modules and `(ℛ/S)`-ideals

The algebraic part of §2.  The paper's claims are stated as `def … : Prop`; those with a printed derivation are proved in later files (see below), the others are not proved here.  The analytic material (analytic
K-covers and the category `𝔄(K/k)`, assertion (c), the analytic blowing-up in `𝓜*(𝔄n/K)`, `𝒥*(𝔄n/K)`, Chow's
theorem) is not formalized.

> Let S be a local-ringed space or a commutative ring with unity, and ℛ/S the category of S-local-ringed spaces.
> Then by an (ℛ/S)-module, we shall mean a pair (X, J) of an S-local-ringed space X and a sheaf of modules J on X.
> A morphism of (ℛ/S)-modules, say (X₁, J₁) → (X₂, J₂), is by definition a pair (f, φ) of an S-morphism f: X₁ → X₂
> and an f-epimorphism of sheaves of modules φ: J₂ → J₁, i.e., a surjective homomorphism of sheaves of modules on
> X₁ from f*(J₂) to J₁. (p. 123)

> (**) If (P′, Φ′) is any pair of the same type, then there exists a unique morphism Ψ: P′ → P in 𝓜′ such that
> Φ′ = Φ∘Ψ. (p. 123)

## What is formalized

* `(ℛ/S)`-modules and their morphisms (`RModule`, `RModule.Hom`, with the category structure, `RModuleOver`),
  invertible, quasi-coherent and coherent modules, blowing-up by the universal property (**)
  (`IsBlowingUp`, `HasBlowingUp`, `IsClosedUnderBlowingUp`), `(ℛ/S)`-ideals, their morphisms, `f⁻¹(J)`
  (`RIdeal`, `RIdealOver`, `RIdeal.pullbackIdeal`), blowing-up in a subcategory by (1), (2) of p. 129
  (`IsMonoidalBlowingUp`), and the first definition of "projective" (p. 126, `IsProjectiveFirst`).
* The claims of §2 as `def … : Prop`, each with its classification in its docstring: uniqueness of a blowing-up,
  the basic existence theorem, the existence for `𝓜(ℛ/S)`, assertions (a) and (b), the existence in `𝓜*(𝔄l/B)`,
  `𝒥(ℛ/S)` not closed in `𝓜(ℛ)`, the existence for `(ℛ/S)`-ideals and in `𝒥*(𝔄l/B)`, its closedness in
  `𝒥(ℛ/B)`, the uniqueness of `f⁻¹(J₂)`, the reduction "only `T = X`" for projective morphisms, "projective implies
  proper", and the cited coherence of direct images under proper morphisms (footnote 14′).

## Formalization notes (encodings)

* `ℛ` is Mathlib's `LocallyRingedSpace`.  Mathlib's sheaves of modules `Scheme.Modules` are for schemes only, and
  restricting `ℛ` to schemes would change the meaning of the universal property (**), which is tested against all
  local-ringed spaces; so the functoriality of sheaves of modules (`f^*`, `f_*`, `(f ≫ g)^* ≅ f^* g^*`, the
  coherence laws) is repeated for locally ringed spaces (`OModules`), using Mathlib's generic `SheafOfModules` API.
* `ℛ/ℤ = ℛ` (`Spec ℤ` is terminal), so `ℛ`-modules and `ℛ`-ideals carry no structure morphism; `(ℛ/S)`-modules and
  `(ℛ/S)`-ideals are those with a morphism to `S` (`CostructuredArrow`); a ring as base is its spectrum.  The
  subcategories `ℛ′` of `ℛ/S` are taken full, given by a property of the objects (all those of the paper are full).
* The paper's "prescheme" is Mathlib's `Scheme`; its "scheme" is a separated one (`IsPrescheme`, `IsScheme`,
  `LocallyRingedSpace.IsAlgebraicPreschemeOver`, `LocallyRingedSpace.IsAlgebraicSchemeOver`, for locally ringed spaces isomorphic to Mathlib schemes).
* "invertible" is that `O_X|U ≅ J|U` is given by a section `s` with `a ↦ a s` bijective on every open `V ⊆ U`;
  "coherent" is finite presentation (coherence on the locally noetherian schemes where the paper uses it).
* `Φ′ = Φ∘Ψ` is `Ψ ≫ Φ = Φ'` in the category notation; the composition of `(ℛ/S)`-modules is the one given by the
  isomorphisms `f^* g^* ≅ (f ≫ g)^*` (not printed; the category axioms are proved).  For ideals, the
  compatibility with the monomorphisms is the commutativity of the square with the canonical map
  `f^*(O_{X₂}) → O_{X₁}`, which is shown to be compatible with composition and identities.
* Restrictions of local-ringed spaces to non-open subsets, needed in the first definition of "projective", are
  encoded stalkwise (`RestrictsToIso`).

## Correspondence with the project

`Hironaka.MonoidalTransformation X B` (`Hironaka/Statements.lean`, p. 129 and p. 166) is the universal property (1),
(2) of p. 129 (`IsMonoidalBlowingUp`) for `ℛ′` the category of schemes and the ideal sheaf of the center `B`; the
strict transform and its facts of p. 130 are `Hironaka/Ch0/Blowup.lean`.  The correspondence of p. 129 between coherent sheaves of ideals on `X` and the algebraic subschemes (local-ringed subspaces) `D` of `X`, with "the sheaf of ideals of `D` on `X`", is built into the project's encoding `Subscheme X := X.IdealSheafData` (`Hironaka/Statements.lean`); it is not restated here.  The second definition of "projective"
(p. 132) is `IsProjectiveOver`; the paper does not show that the two definitions agree, and this is not proved here.

## Where the related material is

* Grothendieck's observation (p. 124, footnote 13: `(Proj(S_A(J)), J₁)` is a blowing-up of `(Spec A, J)`), the
  claims of p. 128 about `(Proj(S*_A(J)), I₁*)` (the degree-one sheaf is an ideal, and it is a blowing-up of `S(A, J)` in
  `𝒥(ℛ)`) are stated in `Hironaka/Ch0/BlowingUpProj.lean` (`GrothendieckObservation`, `ReesDegreeOneIsIdeal`,
  `ReesProjIsBlowingUp`), on the infrastructure `Hironaka/Compat/SymmetricAlgebraGrading.lean`, `ReesAlgebraGrading.lean`,
  `ProjDegreeOne.lean`.
* The annihilator construction of p. 127 and its claim are in `Hironaka/Ch0/BlowingUpIdeals.lean`
  (`AnnihilatorConstructionIsBlowingUp`); the deduction of p. 128 for `𝒥*(𝔄l/B)` is in
  `Hironaka/Ch0/BlowingUpIdealsCoherent.lean` (the membership of the constructed object in `𝒥*(𝔄l/B)`, which the deduction
  does not print, is the paper's own next sentence of p. 128, `CoherentIdealsClosedInIdeals`, an explicit hypothesis).
* The three deductions of pp. 123–124 are proved in `Hironaka/Ch0/BlowingUpDeductions.lean`
  (`existenceOfBlowingUpOver_of_basic`, `modulesOverClosedUnderBlowingUp_of_basic`,
  `existenceOfBlowingUpCoherent_of_closed`).

* The construction of `(P, I)` on pp. 124–125 (the sets `𝐏^x`, the topology on `𝐏`, the sections of `O_P` and `I`,
  the morphism `Φ`) is in `Hironaka/Ch0/BlowingUpConstruction.lean`, characterized by the printed conditions
  (`IsConstruction`); its claims "We see that N … is an ℛ-module" (`ConstructionIsRModule`) and "It is not difficult
  to prove that (P, Φ) is a blowing-up" (`ConstructionIsBlowingUp`) are stated, not proved.
* Assertions (a) and (b) of p. 124 are proved along the printed derivation of p. 125 ("The assertions of (a) and (b)
  follow from this fact and the result stated in the preceding paragraph") in `Hironaka/Ch0/BlowingUpClosed.lean`
  (`quasicoherentClosedUnderBlowingUp_of_construction`, `coherentClosedUnderBlowingUp_of_construction`), from the
  statements the paper makes: the construction's two claims, Grothendieck's observation and the uniqueness of
  blowing-ups; the steps the paper does not print are gaps filled and proved.

## Misprints of the source

Quotations reproduce the page, with [sic] where a misprint is quoted.  p. 119 (not quoted here): `p₁ = f∘p₂` for `p₁ = p₂∘f`; p. 123 "subcatgory"; p. 126 `X | h⁻¹(T)` for
`X̃ | h⁻¹(T)`; p. 127 "dlowing-up", "exitence"; p. 128 "subcategry".
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite

noncomputable section

namespace Hironaka

universe u

/-- The underlying sheaf of rings (valued in `RingCat`) of a locally ringed space.

Formalization note (encoding): Mathlib's sheaves of modules `Scheme.Modules` are defined for schemes
only (`Scheme.ringCatSheaf`).  The paper's category `ℛ` is that of all local-ringed spaces (p. 117), and the
universal property (**) of p. 123 quantifies over all of them, so the construction is repeated here for
`LocallyRingedSpace`, with the same definitions (the functoriality statements are Mathlib's generic
`SheafOfModules` ones). -/
noncomputable abbrev ringCatSheaf (X : LocallyRingedSpace.{u}) : TopCat.Sheaf RingCat.{u} X.carrier :=
  (sheafCompose _ (forget₂ CommRingCat RingCat.{u})).obj X.sheaf

variable {X Y : LocallyRingedSpace.{u}} in
/-- The morphism of sheaves of rings `θ : O_Y → f_*(O_X)` of a morphism `f : X ⟶ Y` of locally ringed spaces
(encoding, as for `ringCatSheaf`). -/
noncomputable def ringCatSheafHom (f : X ⟶ Y) :
    ringCatSheaf Y ⟶ ((TopologicalSpace.Opens.map f.base).sheafPushforwardContinuous
      _ _ _).obj (ringCatSheaf X) where
  hom := Functor.whiskerRight f.c _

/-- The category of sheaves of `O_X`-modules on a locally ringed space `X` (encoding, as for `ringCatSheaf`). -/
def OModules (X : LocallyRingedSpace.{u}) := SheafOfModules.{u} (ringCatSheaf X)

namespace OModules

variable {X Y Z T : LocallyRingedSpace.{u}}

/-- Morphisms of sheaves of `O_X`-modules (encoding). -/
def Hom (M N : OModules X) : Type u := SheafOfModules.Hom M N

noncomputable instance : Category (OModules X) where
  Hom := Hom
  __ := (inferInstance : Category (SheafOfModules.{u} (ringCatSheaf X)))

noncomputable instance : Abelian (OModules X) :=
  inferInstanceAs <| Abelian (SheafOfModules.{u} (ringCatSheaf X))

variable (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ T)

set_option backward.isDefEq.respectTransparency.types false in
/-- The direct image `f_*` of sheaves of modules (encoding). -/
noncomputable def pushforward : OModules X ⥤ OModules Y :=
  SheafOfModules.pushforward (ringCatSheafHom f)

set_option backward.isDefEq.respectTransparency.types false in
/-- The inverse image `f^*` of sheaves of modules, left adjoint to `f_*` (encoding). -/
noncomputable def pullback : OModules Y ⥤ OModules X :=
  SheafOfModules.pullback (ringCatSheafHom f)

set_option backward.isDefEq.respectTransparency.types false in
/-- The adjunction `f^* ⊣ f_*` (encoding). -/
noncomputable def pullbackPushforwardAdjunction : pullback f ⊣ pushforward f :=
  SheafOfModules.pullbackPushforwardAdjunction _

instance : (pullback f).IsLeftAdjoint := (pullbackPushforwardAdjunction f).isLeftAdjoint

/-- Inverse images along equal morphisms are isomorphic. -/
def pullbackCongr {f g : X ⟶ Y} (hf : f = g) : pullback f ≅ pullback g :=
  eqToIso (hf ▸ rfl)

variable (X) in
set_option backward.isDefEq.respectTransparency.types false in
/-- `(𝟙 X)^* ≅ 𝟭` (encoding). -/
noncomputable def pullbackId : pullback (𝟙 X) ≅ 𝟭 _ :=
  SheafOfModules.pullbackId _

set_option backward.isDefEq.respectTransparency.types false in
/-- `f^* g^* ≅ (f ≫ g)^*` (encoding). -/
noncomputable def pullbackComp : pullback g ⋙ pullback f ≅ pullback (f ≫ g) :=
  SheafOfModules.pullbackComp _ _

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
lemma pseudofunctor_associativity :
    (pullbackComp f (g ≫ h)).inv ≫
      Functor.whiskerRight (pullbackComp g h).inv _ ≫ (Functor.associator _ _ _).hom ≫
        Functor.whiskerLeft _ (pullbackComp f g).hom ≫ (pullbackComp (f ≫ g) h).hom =
    eqToHom (by simp) := by
  let e₁ := pullbackComp f (g ≫ h)
  let e₂ := Functor.isoWhiskerRight (pullbackComp g h) (pullback f)
  let e₃ := Functor.isoWhiskerLeft (pullback h) (pullbackComp f g)
  let e₄ := pullbackComp (f ≫ g) h
  change e₁.inv ≫ e₂.inv ≫ (Functor.associator _ _ _).hom ≫ e₃.hom ≫ e₄.hom = _
  have : e₃.hom ≫ e₄.hom = (Functor.associator _ _ _).inv ≫ e₂.hom ≫ e₁.hom :=
    congr_arg Iso.hom (SheafOfModules.pullback_assoc.{u}
      (ringCatSheafHom h) (ringCatSheafHom g) (ringCatSheafHom f))
  simp [this]

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
lemma pseudofunctor_left_unitality :
    (pullbackComp f (𝟙 Y)).inv ≫
      Functor.whiskerRight (pullbackId Y).hom (pullback f) ≫ (Functor.leftUnitor _).hom =
        eqToHom (by simp) := by
  let e₁ := pullbackComp f (𝟙 _)
  let e₂ := Functor.isoWhiskerRight (pullbackId Y) (pullback f)
  let e₃ := (pullback f).leftUnitor
  change e₁.inv ≫ e₂.hom ≫ e₃.hom = _
  have : e₁.hom = e₂.hom ≫ e₃.hom :=
    congr_arg Iso.hom (SheafOfModules.pullback_id_comp.{u} (ringCatSheafHom f))
  simp [← this]

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
lemma pseudofunctor_right_unitality :
    (pullbackComp (𝟙 X) f).inv ≫
      Functor.whiskerLeft (pullback f) (pullbackId X).hom ≫ (Functor.rightUnitor _).hom =
        eqToHom (by simp) := by
  let e₁ := pullbackComp (𝟙 _) f
  let e₂ := Functor.isoWhiskerLeft (pullback f) (pullbackId _)
  let e₃ := (pullback f).rightUnitor
  change e₁.inv ≫ e₂.hom ≫ e₃.hom = _
  have : e₁.hom = e₂.hom ≫ e₃.hom :=
    congr_arg Iso.hom (SheafOfModules.pullback_comp_id.{u} (ringCatSheafHom f))
  simp [← this]

set_option backward.isDefEq.respectTransparency.types false in
/-- The structure sheaf `O_X` as a sheaf of modules over itself (encoding). -/
noncomputable def unit (X : LocallyRingedSpace.{u}) : OModules X := SheafOfModules.unit (ringCatSheaf X)

set_option backward.isDefEq.respectTransparency.types false in
/-- The module map `O_Y → f_*(O_X)` given by the ring map `θ` (encoding). -/
noncomputable def unitToPushforward : unit Y ⟶ (pushforward f).obj (unit X) :=
  SheafOfModules.unitToPushforwardObjUnit (ringCatSheafHom f)

set_option backward.isDefEq.respectTransparency.types false in
/-- The canonical map `f^*(O_Y) → O_X`, adjoint to `unitToPushforward`; it is the map `θ(·)O_X` of the paper (encoding). -/
noncomputable def pullbackUnitToUnit : (pullback f).obj (unit Y) ⟶ unit X :=
  SheafOfModules.pullbackObjUnitToUnit (ringCatSheafHom f)

set_option backward.isDefEq.respectTransparency.types false in
/-- `f_* g_* ≅ (f ≫ g)_*` (encoding). -/
noncomputable def pushforwardComp : pushforward f ⋙ pushforward g ≅ pushforward (f ≫ g) :=
  SheafOfModules.pushforwardComp _ _

set_option backward.isDefEq.respectTransparency.types false in
lemma pullbackConj :
    conjugateEquiv ((pullbackPushforwardAdjunction g).comp (pullbackPushforwardAdjunction f))
      (pullbackPushforwardAdjunction (f ≫ g)) (pullbackComp f g).inv = (pushforwardComp f g).hom :=
  SheafOfModules.conjugateEquiv_pullbackComp_inv _ _

set_option backward.isDefEq.respectTransparency.types false in
lemma pullbackUnitToUnit_comp :
    pullbackUnitToUnit (f ≫ g) = (pullbackComp f g).inv.app (unit Z) ≫
      (pullback f).map (pullbackUnitToUnit g) ≫ pullbackUnitToUnit f := by
  apply ((pullbackPushforwardAdjunction (f ≫ g)).homEquiv _ _).injective
  have := unit_conjugateEquiv ((pullbackPushforwardAdjunction g).comp
      (pullbackPushforwardAdjunction f)) (pullbackPushforwardAdjunction (f ≫ g))
      (pullbackComp f g).inv (unit Z)
  rw [pullbackConj] at this
  simp only [Functor.comp_obj] at this
  have hu : (pullbackPushforwardAdjunction (f ≫ g)).homEquiv _ _ (pullbackUnitToUnit (f ≫ g)) =
      unitToPushforward (f ≫ g) := by
    exact Equiv.apply_symm_apply _ _
  rw [hu, Adjunction.homEquiv_unit, Functor.map_comp, ← Category.assoc, ← this,
    Adjunction.comp_unit_app]
  have nat := (pushforwardComp f g).hom.naturality
    ((pullback f).map (pullbackUnitToUnit g) ≫ pullbackUnitToUnit f)
  simp only [Functor.comp_map] at nat
  rw [Category.assoc, ← nat]
  have hf : (pullbackPushforwardAdjunction f).homEquiv _ _ (pullbackUnitToUnit f) =
      unitToPushforward f :=
    Equiv.apply_symm_apply _ _
  have hg : (pullbackPushforwardAdjunction g).homEquiv _ _ (pullbackUnitToUnit g) =
      unitToPushforward g :=
    Equiv.apply_symm_apply _ _
  have h1 : (pullbackPushforwardAdjunction f).unit.app ((pullback g).obj (unit Z)) ≫
      (pushforward f).map ((pullback f).map (pullbackUnitToUnit g) ≫ pullbackUnitToUnit f) =
      pullbackUnitToUnit g ≫ unitToPushforward f := by
    have e := (pullbackPushforwardAdjunction f).homEquiv_unit
      (X := (pullback g).obj (unit Z)) (f := (pullback f).map (pullbackUnitToUnit g) ≫
        pullbackUnitToUnit f)
    rw [← e, Adjunction.homEquiv_naturality_left, hf]
  have h2 : (pullbackPushforwardAdjunction g).unit.app (unit Z) ≫
      (pushforward g).map (pullbackUnitToUnit g) =
      unitToPushforward g := by
    rw [← hg, Adjunction.homEquiv_unit]
  rw [Category.assoc, ← Functor.map_comp_assoc, h1]
  simp only [Functor.map_comp, Category.assoc]
  rw [reassoc_of% h2]
  apply SheafOfModules.hom_ext
  ext U
  show _ = _
  rfl

variable (X) in
set_option backward.isDefEq.respectTransparency.types false in
/-- `(𝟙 X)_* ≅ 𝟭` (encoding). -/
noncomputable def pushforwardId : pushforward (𝟙 X) ≅ 𝟭 _ :=
  SheafOfModules.pushforwardId _

set_option backward.isDefEq.respectTransparency.types false in
lemma pullbackIdConj :
    conjugateEquiv .id (pullbackPushforwardAdjunction (𝟙 X)) (pullbackId X).hom =
      (pushforwardId X).inv :=
  SheafOfModules.conjugateEquiv_pullbackId_hom _

set_option backward.isDefEq.respectTransparency.types false in
lemma pullbackUnitToUnit_id :
    pullbackUnitToUnit (𝟙 X) = (pullbackId X).hom.app (unit X) := by
  apply ((pullbackPushforwardAdjunction (𝟙 X)).homEquiv _ _).injective
  have hu : (pullbackPushforwardAdjunction (𝟙 X)).homEquiv _ _ (pullbackUnitToUnit (𝟙 X)) =
      unitToPushforward (𝟙 X) :=
    Equiv.apply_symm_apply _ _
  rw [hu, Adjunction.homEquiv_unit]
  have := unit_conjugateEquiv Adjunction.id (pullbackPushforwardAdjunction (𝟙 X))
    (pullbackId X).hom (unit X)
  rw [pullbackIdConj] at this
  simp at this
  rw [← this]
  rfl

end OModules

/-- An `ℛ`-module, i.e. an `(ℛ/ℤ)`-module: a pair `(X, J)` of a locally ringed space and a sheaf of modules on it.

> Let S be a local-ringed space or a commutative ring with unity, and ℛ/S the category of S-local-ringed spaces.
> Then by an (ℛ/S)-module, we shall mean a pair (X, J) of an S-local-ringed space X and a sheaf of modules J on X.
> (p. 123)

Definition (p. 123).  Formalization notes (encoding): `ℛ` is Mathlib's `LocallyRingedSpace` (no restriction to
schemes: the universal property (**) is tested against all local-ringed spaces).  Since `Spec ℤ` is terminal in
`ℛ`, `ℛ/ℤ = ℛ` (the paper identifies them, p. 123), so an `ℛ`-module needs no structure morphism; an
`(ℛ/S)`-module is an `ℛ`-module with a morphism `X ⟶ S` (`RModuleOver`), and a ring `A` as base is `Spec A`. -/
@[blueprint "def:0.S2-module"
  (statement := /-- Let $S$ be a local-ringed space or a commutative ring with unity, and $\mathcal R/S$ the category of
    $S$-local-ringed spaces. Then by an \emph{$(\mathcal R/S)$-module} we shall mean a pair $(X,J)$ of an
    $S$-local-ringed space $X$ and a sheaf of modules $J$ on $X$. (p.~123.) Formalization note (encoding):
    $\mathcal R$ is the category of locally ringed spaces; since $\operatorname{Spec}\mathbb Z$ is terminal in it,
    $\mathcal R/\mathbb Z=\mathcal R$ (as the paper identifies them), so an $\mathcal R$-module is a pair $(X,J)$
    (this declaration) and an $(\mathcal R/S)$-module is such a pair with a morphism $X\to S$; a ring as base
    means its spectrum. -/)
  (latexEnv := "definition")]
structure RModule where
  /-- The local-ringed space `X`. -/
  X : LocallyRingedSpace.{u}
  /-- The sheaf of modules `J` on `X`. -/
  J : OModules X

namespace RModule

/-- A morphism of `ℛ`-modules `(X₁, J₁) → (X₂, J₂)`: a morphism `f : X₁ ⟶ X₂` together with an `f`-epimorphism
`φ : J₂ → J₁`, i.e. a surjective homomorphism `f^*(J₂) ⟶ J₁` of sheaves of modules on `X₁`.

> A morphism of (ℛ/S)-modules, say (X₁, J₁) → (X₂, J₂), is by definition a pair (f, φ) of an S-morphism
> f: X₁ → X₂ and an f-epimorphism of sheaves of modules φ: J₂ → J₁, i.e., a surjective homomorphism of sheaves of
> modules on X₁ from f*(J₂) to J₁. (p. 123)

Definition (p. 123).  Formalization notes (encoding): the field `φ` is the homomorphism `f^*(J₂) → J₁`, and
"surjective" is `Epi` in the abelian category of sheaves of modules (surjective on stalks).  The paper does not
print the composition of such morphisms (it speaks of "the category of (ℛ/S)-modules"); it is the one forced by
the pseudofunctoriality of `f^*` (`φ` of the composite is `(f ≫ g)^* J₃ ≅ f^* g^* J₃ → f^* J₂ → J₁`); the category
axioms are proved (a tacit step, recorded). -/
@[blueprint "def:0.S2-module-morphism"
  (statement := /-- A \emph{morphism of $(\mathcal R/S)$-modules}, say $(X_1,J_1)\to(X_2,J_2)$, is by definition a pair $(f,\varphi)$
    of an $S$-morphism $f\colon X_1\to X_2$ and an $f$-epimorphism of sheaves of modules $\varphi\colon J_2\to J_1$,
    i.e., a surjective homomorphism of sheaves of modules on $X_1$ from $f^*(J_2)$ to $J_1$. (p.~123.)
    Formalization note (encoding): $\varphi$ is the homomorphism $f^*(J_2)\to J_1$, which is required to be an
    epimorphism; the composition (not printed in the paper) is the one given by the isomorphisms
    $f^*g^*\cong(fg)^*$, and the category axioms are verified. -/)
  (latexEnv := "definition")]
structure Hom (M N : RModule.{u}) where
  /-- The morphism of local-ringed spaces `f`. -/
  f : M.X ⟶ N.X
  /-- The homomorphism `φ : f^*(J₂) ⟶ J₁`. -/
  φ : (OModules.pullback f).obj N.J ⟶ M.J
  /-- `φ` is surjective (an epimorphism of sheaves of modules). -/
  epi_φ : Epi φ

attribute [instance] Hom.epi_φ

noncomputable instance : CategoryStruct RModule.{u} where
  Hom := Hom
  id M := ⟨𝟙 M.X, (OModules.pullbackId M.X).hom.app M.J, inferInstance⟩
  comp {A B C} g h := ⟨g.f ≫ h.f,
    (OModules.pullbackComp g.f h.f).inv.app C.J ≫ (OModules.pullback g.f).map h.φ ≫ g.φ,
    by
      have : Epi ((OModules.pullback g.f).map h.φ) := inferInstance
      infer_instance⟩

lemma Hom.ext' {M N : RModule.{u}} {a b : M ⟶ N} (h : a.f = b.f)
    (h2 : a.φ = (OModules.pullbackCongr h).hom.app N.J ≫ b.φ) : a = b := by
  obtain ⟨f, φ, _⟩ := a
  obtain ⟨g, ψ, _⟩ := b
  change f = g at h
  subst h
  simp [OModules.pullbackCongr] at h2
  subst h2
  rfl

open OModules in
lemma id_comp' {A B : RModule.{u}} (f : A ⟶ B) : 𝟙 A ≫ f = f := by
  refine Hom.ext' (by change 𝟙 A.X ≫ f.f = f.f; exact Category.id_comp _) ?_
  have := congr_app (pseudofunctor_right_unitality f.f) B.J
  simp at this
  change (pullbackComp (𝟙 A.X) f.f).inv.app B.J ≫ (pullback (𝟙 A.X)).map f.φ ≫
    (pullbackId A.X).hom.app A.J = _
  rw [(pullbackId A.X).hom.naturality f.φ]
  simp only [Functor.id_map]
  rw [← Category.assoc, this]
  simp [pullbackCongr]

open OModules in
lemma comp_id' {A B : RModule.{u}} (f : A ⟶ B) : f ≫ 𝟙 B = f := by
  refine Hom.ext' (by change f.f ≫ 𝟙 B.X = f.f; exact Category.comp_id _) ?_
  have := congr_app (pseudofunctor_left_unitality f.f) B.J
  simp at this
  change (pullbackComp f.f (𝟙 B.X)).inv.app B.J ≫ (pullback f.f).map ((pullbackId B.X).hom.app B.J) ≫
    f.φ = _
  rw [← Category.assoc, this]
  simp [pullbackCongr]

open OModules in
lemma assoc' {A B C D : RModule.{u}} (f : A ⟶ B) (g : B ⟶ C) (h : C ⟶ D) :
    (f ≫ g) ≫ h = f ≫ g ≫ h := by
  refine Hom.ext' (by change (f.f ≫ g.f) ≫ h.f = f.f ≫ g.f ≫ h.f; exact Category.assoc _ _ _) ?_
  have := congr_app (pseudofunctor_associativity f.f g.f h.f) D.J
  simp at this
  have e1 : (pullbackComp (f.f ≫ g.f) h.f).inv.app D.J =
      (pullbackCongr (Category.assoc f.f g.f h.f)).hom.app D.J ≫
        (pullbackComp f.f (g.f ≫ h.f)).inv.app D.J ≫
        (pullback f.f).map ((pullbackComp g.f h.f).inv.app D.J) ≫
        (pullbackComp f.f g.f).hom.app ((pullback h.f).obj D.J) := by
    apply (cancel_mono ((pullbackComp (f.f ≫ g.f) h.f).hom.app D.J)).1
    simp only [Iso.inv_hom_id_app, Category.assoc]
    rw [this]
    simp [pullbackCongr]
  change (pullbackComp (f.f ≫ g.f) h.f).inv.app D.J ≫ (pullback (f.f ≫ g.f)).map h.φ ≫
    (pullbackComp f.f g.f).inv.app C.J ≫ (pullback f.f).map g.φ ≫ f.φ = _ ≫
    (pullbackComp f.f (g.f ≫ h.f)).inv.app D.J ≫ (pullback f.f).map
      ((pullbackComp g.f h.f).inv.app D.J ≫ (pullback g.f).map h.φ ≫ g.φ) ≫ f.φ
  rw [e1]
  have nat := (pullbackComp f.f g.f).hom.naturality h.φ
  simp only [Functor.comp_map] at nat
  simp only [Category.assoc, Functor.map_comp]
  rw [← reassoc_of% nat]
  simp

instance : Category RModule.{u} where
  id_comp := id_comp'
  comp_id := comp_id'
  assoc := assoc'

/-- The module `(X, J)` is invertible at the point `x`: some open neighbourhood `U` of `x` carries a section `s` of
`J` such that, for every open `V ⊆ U`, `a ↦ a • s|_V` is a bijection `O_X(V) → J(V)` (that is, `O_X|U ≅ J|U` as
sheaves of `O_X|U`-modules, the isomorphism being `1 ↦ s`).  Formalization note (encoding): an isomorphism of sheaves of
modules `O_X|U ≅ J|U` is the same as a section `s` of `J` over `U` for which these maps are all bijective. -/
def IsInvertibleAt (M : RModule.{u}) (x : M.X) : Prop :=
  ∃ (U : Opens M.X) (_ : x ∈ U) (s : M.J.val.obj (op U)),
    ∀ (V : Opens M.X) (hV : V ≤ U),
      Function.Bijective (fun a : (ringCatSheaf M.X).obj.obj (op V) =>
        a • ((M.J.val.map (homOfLE hV).op).hom s))

/-- An `ℛ`-module `(X, J)` is invertible.

> An (ℛ/S)-module (X, J) with X = (X, O_X) will be said to be invertible if every point of X has a neighborhood U
> in X such that the restrictions O_X | U and J | U are isomorphic to each other as sheaves of (O_X | U)-modules.
> (p. 123)

Definition (p. 123).  Formalization note (encoding): see `IsInvertibleAt`. -/
@[blueprint "def:0.S2-invertible"
  (statement := /-- An $(\mathcal R/S)$-module $(X,J)$ with $X=(\mathbf X,O_X)$ will be said to be \emph{invertible} if every point of
    $\mathbf X$ has a neighborhood $U$ in $\mathbf X$ such that the restrictions $O_X|U$ and $J|U$ are isomorphic to
    each other as sheaves of $(O_X|U)$-modules. (p.~123.) Formalization note (encoding): an isomorphism
    $O_X|U\cong J|U$ of sheaves of modules is a section $s$ of $J$ over $U$ such that
    $a\mapsto a\,s|_V$ is bijective $O_X(V)\to J(V)$ for every open $V\subseteq U$. -/)
  (latexEnv := "definition")]
def IsInvertible (M : RModule.{u}) : Prop := ∀ x : M.X, M.IsInvertibleAt x

/-- The `ℛ`-module `(X, J)` is quasi-coherent: `J` is quasi-coherent (Mathlib's `SheafOfModules.IsQuasicoherent`).

> We shall say an (ℛ/S)-module (or ℛ-module) (X, J) is coherent (resp. quasi-coherent) if J is coherent
> (resp. quasi-coherent). (p. 124)

Definition (p. 124). -/
@[blueprint "def:0.S2-quasicoherent"
  (statement := /-- An $(\mathcal R/S)$-module (or $\mathcal R$-module) $(X,J)$ is \emph{quasi-coherent} if $J$ is quasi-coherent.
    (p.~124.) Formalization note (encoding): Mathlib's quasi-coherence of sheaves of modules (locally a cokernel of a
    map of free modules). -/)
  (latexEnv := "definition")]
def IsQuasicoherent (M : RModule.{u}) : Prop :=
  SheafOfModules.IsQuasicoherent (R := ringCatSheaf M.X) M.J

/-- The `ℛ`-module `(X, J)` is coherent: `J` is of finite presentation (Mathlib's `SheafOfModules.IsFinitePresentation`).

Definition (p. 124, see `IsQuasicoherent`).  Formalization note (encoding): the paper does not define "coherent"
for sheaves of modules (it refers to Serre and Cartan).  Finite presentation coincides with coherence (Serre) when
the structure sheaf is coherent, in particular on locally noetherian schemes, which are the only spaces on which
the paper uses the word for modules (algebraic `B`-schemes with `B` noetherian, p. 124); recorded as an encoding. -/
@[blueprint "def:0.S2-coherent"
  (statement := /-- An $(\mathcal R/S)$-module (or $\mathcal R$-module) $(X,J)$ is \emph{coherent} if $J$ is coherent. (p.~124.)
    Formalization note (encoding): for modules over locally noetherian schemes, the only case in which the paper
    uses the word, coherent means of finite presentation; this is the definition taken, for all modules. -/)
  (latexEnv := "definition")]
def IsCoherent (M : RModule.{u}) : Prop :=
  SheafOfModules.IsFinitePresentation (R := ringCatSheaf M.X) M.J

/-- The underlying local-ringed space, as a functor `𝓜(ℛ) ⥤ ℛ` (encoding). -/
def base : RModule.{u} ⥤ LocallyRingedSpace.{u} where
  obj M := M.X
  map f := f.f

end RModule

/-- An `ℛ`-ideal, i.e. an `(ℛ/ℤ)`-ideal: a pair `(X, J)` of a local-ringed space and a sheaf of ideals, namely a
sheaf of `O_X`-modules with a specific monomorphism `J → O_X`.

> ... we define an (ℛ/S)-ideal as a pair (X, J) of an S-local-ringed space X = (X, O_X) and a sheaf of ideals J on
> X, i.e., a sheaf of O_X-modules with a specific monomorphism J → O_X. (p. 127)

Definition (p. 127).  Formalization notes (encoding): the monomorphism is part of the data; `ℛ/ℤ = ℛ` as for
`RModule`; the structure morphism of an `(ℛ/S)`-ideal is `RIdealOver`. -/
@[blueprint "def:0.S2-ideal"
  (statement := /-- To be precise, $S$ being a local-ringed space or a commutative ring with unity, we define an
    \emph{$(\mathcal R/S)$-ideal} as a pair $(X,J)$ of an $S$-local-ringed space $X=(\mathbf X,O_X)$ and a sheaf of ideals
    $J$ on $X$, i.e., a sheaf of $O_X$-modules with a specific monomorphism $J\to O_X$. (p.~127.) Formalization note
    (encoding): the monomorphism is part of the data; as for modules, $\mathcal R/\mathbb Z=\mathcal R$. -/)
  (latexEnv := "definition")]
structure RIdeal where
  /-- The local-ringed space `X`. -/
  X : LocallyRingedSpace.{u}
  /-- The sheaf of modules `J` on `X`. -/
  J : OModules X
  /-- The monomorphism `J → O_X`. -/
  ι : J ⟶ OModules.unit X
  /-- `ι` is a monomorphism. -/
  mono_ι : Mono ι

attribute [instance] RIdeal.mono_ι

namespace RIdeal

/-- The `ℛ`-module underlying an `ℛ`-ideal (encoding). -/
abbrev toRModule (I : RIdeal.{u}) : RModule.{u} := ⟨I.X, I.J⟩

/-- A morphism of `ℛ`-ideals `(X₁, J₁) → (X₂, J₂)`: a morphism `(f, φ)` of the underlying `ℛ`-modules such that `φ`
and `θ` are compatible with the monomorphisms `J₂ → O_{X₂}` and `J₁ → O_{X₁}`.

> A morphism of (ℛ/S)-ideals, (X₁, J₁) → (X₂, J₂), is a morphism of (ℛ/S)-modules (the (ℛ/S)-ideals are viewed as
> (ℛ/S)-modules in a natural way), say (f, φ) with f = (f, θ): X₁ → X₂ and with an f-epimorphism φ: J₂ → J₁,
> which is subject to the additional condition that φ and θ are compatible with the monomorphisms J₂ → O_{X₂}
> and J₁ → O_{X₁}. (p. 127)

Definition (p. 127).  Formalization note (encoding): the compatibility is the commutativity of
`f^*(J₂) → f^*(O_{X₂}) → O_{X₁}` with `f^*(J₂) → J₁ → O_{X₁}`, where `f^*(O_{X₂}) → O_{X₁}` is the canonical map
(`OModules.pullbackUnitToUnit`); the closure of this condition under composition and identities is proved. -/
@[blueprint "def:0.S2-ideal-morphism"
  (statement := /-- A \emph{morphism of $(\mathcal R/S)$-ideals}, $(X_1,J_1)\to(X_2,J_2)$, is a morphism of $(\mathcal R/S)$-modules
    (the $(\mathcal R/S)$-ideals are viewed as $(\mathcal R/S)$-modules in a natural way), say $(f,\varphi)$ with
    $f=(\mathbf f,\theta)\colon X_1\to X_2$ and with an $f$-epimorphism $\varphi\colon J_2\to J_1$, which is subject
    to the additional condition that $\varphi$ and $\theta$ are compatible with the monomorphisms
    $J_2\to O_{X_2}$ and $J_1\to O_{X_1}$. (p.~127.) Formalization note (encoding): compatibility means that
    $f^*(J_2)\to f^*(O_{X_2})\to O_{X_1}$ equals $f^*(J_2)\to J_1\to O_{X_1}$. -/)
  (latexEnv := "definition")]
structure Hom (I₁ I₂ : RIdeal.{u}) where
  /-- The underlying morphism of `ℛ`-modules. -/
  toHom : I₁.toRModule ⟶ I₂.toRModule
  /-- The compatibility of `φ` and `θ` with the monomorphisms. -/
  compat : (OModules.pullback toHom.f).map I₂.ι ≫ OModules.pullbackUnitToUnit toHom.f =
    toHom.φ ≫ I₁.ι

attribute [ext] Hom

open OModules in
instance : Category RIdeal.{u} where
  Hom := Hom
  id I := ⟨𝟙 I.toRModule, by
    change (pullback (𝟙 I.X)).map I.ι ≫ pullbackUnitToUnit (𝟙 I.X) =
      (pullbackId I.X).hom.app I.J ≫ I.ι
    rw [pullbackUnitToUnit_id]
    exact (pullbackId I.X).hom.naturality I.ι⟩
  comp {I₁ I₂ I₃} a b := ⟨a.toHom ≫ b.toHom, by
    change (pullback (a.toHom.f ≫ b.toHom.f)).map I₃.ι ≫ pullbackUnitToUnit (a.toHom.f ≫ b.toHom.f) =
      ((pullbackComp a.toHom.f b.toHom.f).inv.app I₃.J ≫ (pullback a.toHom.f).map b.toHom.φ ≫
        a.toHom.φ) ≫ I₁.ι
    rw [pullbackUnitToUnit_comp]
    have nat := (pullbackComp a.toHom.f b.toHom.f).inv.naturality I₃.ι
    simp only [Functor.comp_map] at nat
    rw [← Category.assoc, nat]
    simp only [Category.assoc]
    rw [← Functor.map_comp_assoc, b.compat, Functor.map_comp_assoc, a.compat]⟩
  id_comp a := Hom.ext (Category.id_comp a.toHom)
  comp_id a := Hom.ext (Category.comp_id a.toHom)
  assoc a b c := Hom.ext (Category.assoc a.toHom b.toHom c.toHom)

end RIdeal

/-- The category `𝓜(ℛ/S)` of `(ℛ/S)`-modules: `ℛ`-modules `(X, J)` with a morphism `p : X ⟶ S`, the morphisms being
those of `ℛ`-modules over `S`.

> Let us denote by 𝓜(ℛ/S) the category of (ℛ/S)-modules. We write 𝓜(ℛ) for 𝓜(ℛ/Z). ... We have then a canonical
> covariant functor from 𝓜(ℛ′) to 𝓜(ℛ), induced by that from 𝓜(ℛ/S) to 𝓜(ℛ), which is obtained by neglecting the
> structural morphisms of S-local-ringed spaces. (p. 123)

Formalization notes (encoding): realized as `CostructuredArrow RModule.base S`; the "canonical covariant functor
to `𝓜(ℛ)`" is `RModuleOver.forget`.  The subcategories `𝓜(ℛ′)` for a subcategory `ℛ′` of `ℛ/S` are taken to be
full subcategories given by a property of the objects (`ObjectProperty.FullSubcategory`): all the subcategories
used in the paper (`𝔖`, `pre-𝔖`, `𝔄l/B`, `pre-𝔄l/B`) are full (pp. 117–119); this restriction of the printed
definition (arbitrary subcategories) is recorded. -/
@[blueprint "def:0.S2-module-over"
  (statement := /-- Let us denote by $\mathcal M(\mathcal R/S)$ the category of $(\mathcal R/S)$-modules. We write
    $\mathcal M(\mathcal R)$ for $\mathcal M(\mathcal R/\mathbb Z)$. (p.~123.) Formalization note (encoding): an
    $(\mathcal R/S)$-module is an $\mathcal R$-module with a morphism $X\to S$, and the canonical covariant functor
    $\mathcal M(\mathcal R/S)\to\mathcal M(\mathcal R)$ neglects the structural morphisms; for a subcategory $\mathcal R'$
    of $\mathcal R/S$ the category $\mathcal M(\mathcal R')$ is encoded only for \emph{full} subcategories $\mathcal R'$
    (all those used in the paper), as a full subcategory given by a property of the objects. -/)
  (latexEnv := "definition")]
abbrev RModuleOver (S : LocallyRingedSpace.{u}) := CostructuredArrow RModule.base S

/-- The canonical covariant functor `𝓜(ℛ/S) ⥤ 𝓜(ℛ)` neglecting the structural morphisms (p. 123, see `RModuleOver`). -/
def RModuleOver.forget (S : LocallyRingedSpace.{u}) : RModuleOver S ⥤ RModule.{u} :=
  CostructuredArrow.proj _ _

namespace RIdeal

/-- The underlying local-ringed space of an `ℛ`-ideal, as a functor `𝒥(ℛ) ⥤ ℛ` (encoding). -/
def base : RIdeal.{u} ⥤ LocallyRingedSpace.{u} where
  obj I := I.X
  map a := a.toHom.f

/-- The functor viewing `ℛ`-ideals as `ℛ`-modules ("in a natural way", p. 127). -/
def toRModuleFunctor : RIdeal.{u} ⥤ RModule.{u} where
  obj I := I.toRModule
  map a := a.toHom

/-- The inverse image `f⁻¹(J₂)` of an `ℛ`-ideal `(X₂, J₂)` under `f : X₁ ⟶ X₂`: the sheaf of ideals of `X₁` generated by
`J₂`, i.e. the image of `f^*(J₂) → f^*(O_{X₂}) → O_{X₁}`.

> We shall write f⁻¹(J₂) for θ(J₂)O_{X₁}. (p. 128)

Definition (p. 128).  Formalization note (encoding): `θ(J₂)O_{X₁}` is the image sheaf of the canonical map
`f^*(J₂) → O_{X₁}` (the abelian category of sheaves of modules has images). -/
@[blueprint "def:0.S2-inverse-image-ideal"
  (statement := /-- We shall write $f^{-1}(J_2)$ for $\theta(J_2)O_{X_1}$. (p.~128.) Formalization note (encoding): the sheaf of
    ideals generated by $J_2$ with reference to $f$ is the image of $f^*(J_2)\to f^*(O_{X_2})\to O_{X_1}$. -/)
  (latexEnv := "definition")]
def pullbackIdeal (I : RIdeal.{u}) {X' : LocallyRingedSpace.{u}} (f : X' ⟶ I.X) : RIdeal.{u} where
  X := X'
  J := Abelian.image ((OModules.pullback f).map I.ι ≫ OModules.pullbackUnitToUnit f)
  ι := Abelian.image.ι _
  mono_ι := inferInstance

end RIdeal

/-- The category `𝒥(ℛ/S)` of `(ℛ/S)`-ideals: `ℛ`-ideals with a morphism `X ⟶ S`, the morphisms being those of
`ℛ`-ideals over `S` (p. 127; realized as for `RModuleOver`). -/
abbrev RIdealOver (S : LocallyRingedSpace.{u}) := CostructuredArrow RIdeal.base S

/-- The canonical functor `𝒥(ℛ/S) ⥤ 𝓜(ℛ)` viewing `(ℛ/S)`-ideals as `ℛ`-modules and neglecting the structural morphisms (the "obvious functor" of p. 127). -/
def RIdealOver.toRModule (S : LocallyRingedSpace.{u}) : RIdealOver S ⥤ RModule.{u} :=
  CostructuredArrow.proj _ _ ⋙ RIdeal.toRModuleFunctor

/-- `Φ : P ⟶ M` is a blowing-up of `M` in the category `C` with respect to the functor `T : C ⥤ 𝓜(ℛ)`.

> Let T be a covariant functor from a category 𝓜′ to 𝓜(ℛ). Then, given an object M in 𝓜′, we ask if there exists a
> pair (P, Φ) of an object P in 𝓜′ such that T(P) is invertible and of a morphism Φ: P → M in 𝓜′ which has the
> following universal mapping property:
> (**) If (P′, Φ′) is any pair of the same type, then there exists a unique morphism Ψ: P′ → P in 𝓜′ such that
> Φ′ = Φ∘Ψ. ... will be called a blowing-up of M in the category 𝓜′ with respect to T. (p. 123)

Definition (p. 123).  Formalization note (encoding): `C` is any category (the paper's `𝓜′`); `Φ′ = Φ∘Ψ` is
`Ψ ≫ Φ = Φ'`.  "Blowing-up in `𝓜′` without mentioning `T`" is `T` the canonical functor to `𝓜(ℛ)`. -/
@[blueprint "def:0.S2-blowing-up"
  (statement := /-- Let $T$ be a covariant functor from a category $\mathcal M'$ to $\mathcal M(\mathcal R)$. Then, given an object $M$
    in $\mathcal M'$, we ask if there exists a pair $(P,\Phi)$ of an object $P$ in $\mathcal M'$ such that $T(P)$ is
    invertible and of a morphism $\Phi\colon P\to M$ in $\mathcal M'$ which has the following universal mapping
    property: $(**)$ if $(P',\Phi')$ is any pair of the same type, then there exists a unique morphism
    $\Psi\colon P'\to P$ in $\mathcal M'$ such that $\Phi'=\Phi\circ\Psi$. Such a pair $(P,\Phi)$ \dots{} will be called
    a \emph{blowing-up of $M$ in the category $\mathcal M'$ with respect to $T$}. (p.~123.) Formalization note
    (encoding): $\mathcal M'$ is an arbitrary category. -/)
  (latexEnv := "definition")]
structure IsBlowingUp {C : Type*} [Category C] (T : C ⥤ RModule.{u}) {M P : C} (Φ : P ⟶ M) :
    Prop where
  /-- `T(P)` is invertible. -/
  invertible : (T.obj P).IsInvertible
  /-- The universal property (**). -/
  universal : ∀ (P' : C) (Φ' : P' ⟶ M), (T.obj P').IsInvertible →
    ∃! Ψ : P' ⟶ P, Ψ ≫ Φ = Φ'

/-- The object `M` of `C` admits a blowing-up in `C` with respect to `T` ("`M` admits a blowing-up", p. 123). -/
@[blueprint "def:0.S2-admits-blowing-up"
  (statement := /-- An object $M$ of $\mathcal M'$ \emph{admits a blowing-up} in $\mathcal M'$ with respect to $T$ if there is a pair
    $(P,\Phi)$ as in the definition of a blowing-up. (p.~123.) -/)
  (latexEnv := "definition")]
def HasBlowingUp {C : Type*} [Category C] (T : C ⥤ RModule.{u}) (M : C) : Prop :=
  ∃ (P : C) (Φ : P ⟶ M), IsBlowingUp T Φ

/-- `T : C ⥤ 𝓜(ℛ)` makes `C` closed under blowing-up in `𝓜(ℛ)`.

> We shall say that 𝓜′ is closed under blowing-up in the category 𝓜(ℛ), if every object M in 𝓜′ admits a
> blowing-up (P, Φ) in 𝓜′ (with respect to T) such that (T(P), T(Φ)) is a blowing-up of T(M) in 𝓜(ℛ). (pp. 123–124)

Definition (pp. 123–124). -/
@[blueprint "def:0.S2-closed-under-blowing-up"
  (statement := /-- In general, let $\mathcal M'$ be a category with an obvious functor $T\colon\mathcal M'\to\mathcal M(\mathcal R)$.
    We shall say that $\mathcal M'$ is \emph{closed under blowing-up in the category $\mathcal M(\mathcal R)$}, if every
    object $M$ in $\mathcal M'$ admits a blowing-up $(P,\Phi)$ in $\mathcal M'$ (with respect to $T$) such that
    $(T(P),T(\Phi))$ is a blowing-up of $T(M)$ in $\mathcal M(\mathcal R)$. (pp.~123--124.) -/)
  (latexEnv := "definition")]
def IsClosedUnderBlowingUp {C : Type*} [Category C] (T : C ⥤ RModule.{u}) : Prop :=
  ∀ M : C, ∃ (P : C) (Φ : P ⟶ M), IsBlowingUp T Φ ∧ IsBlowingUp (𝟭 RModule.{u}) (T.map Φ)

/-- A blowing-up is unique up to an isomorphism.

> Such a pair (P, Φ) is unique up to an isomorphism of P in 𝓜′, if it exists, and will be called a blowing-up of M
> in the category 𝓜′ with respect to T. (p. 123)

Stated without proof (p. 123); not proved here.  Formalization note: the isomorphism is compatible with the
two morphisms to `M` (`e.hom ≫ Φ₂ = Φ₁`), as the universal property gives. -/
@[blueprint "prop:0.S2-blowing-up-unique"
  (statement := /-- Such a pair $(P,\Phi)$ is unique up to an isomorphism of $P$ in $\mathcal M'$, if it exists. (p.~123.)
    Formalization note: the isomorphism $P_1\cong P_2$ commutes with the morphisms to $M$. Not proved here: stated
    without argument. -/)
  (latexEnv := "proposition")]
def BlowingUpUnique.{v, w} : Prop :=
  ∀ (C : Type v) [Category.{w} C] (T : C ⥤ RModule.{u}) (M P₁ P₂ : C) (Φ₁ : P₁ ⟶ M)
    (Φ₂ : P₂ ⟶ M), IsBlowingUp T Φ₁ → IsBlowingUp T Φ₂ → ∃ e : P₁ ≅ P₂, e.hom ≫ Φ₂ = Φ₁

/-- The local-ringed space `X` is a prescheme.

> A prescheme is by definition a local-ringed space X = (X, O_X) such that, for each point x of X, there exists an
> open neighborhood X_i of x in X such that the restriction X_i = (X_i, O_X | X_i) of X to X_i is isomorphic to an
> affine scheme, i.e., Spec(A) with a commutative ring A with unity. (p. 117)

Definition (p. 117).  Formalization note (encoding): Mathlib's `Scheme` is exactly this notion (a locally ringed
space locally isomorphic to a `Spec`); "`X` is a prescheme" is "`X` is isomorphic, as a locally ringed space, to
the underlying space of a Mathlib scheme".  Mathlib's `Scheme` is thus the paper's *prescheme*. -/
@[blueprint "def:0.S1-prescheme-lrs"
  (statement := /-- A \emph{prescheme} is by definition a local-ringed space $X=(\mathbf X,O_X)$ such that, for each point $x$ of $X$,
    there exists an open neighborhood $\mathbf X_i$ of $x$ in $\mathbf X$ such that the restriction of $X$ to
    $\mathbf X_i$ is isomorphic to an affine scheme, i.e.\ $\operatorname{Spec}(A)$ with a commutative ring $A$ with
    unity. (p.~117.) Formalization note (encoding): Mathlib's schemes are exactly the paper's preschemes; the
    predicate says that the local-ringed space is isomorphic to a Mathlib scheme. -/)
  (latexEnv := "definition")]
def IsPrescheme (X : LocallyRingedSpace.{u}) : Prop :=
  ∃ Y : Scheme.{u}, Nonempty (Y.toLocallyRingedSpace ≅ X)

/-- The local-ringed space `X` is a scheme in the sense of the paper: a prescheme whose diagonal over `Spec ℤ` is a
closed subscheme, i.e. a separated one.

> If the diagonal of X ×_S X is a closed subscheme, then the S-prescheme (X, p) is called an S-scheme. ... We say
> that X is a scheme, if (X, p_Z) is an Spec(Z)-scheme. (p. 118)

Definition (p. 118).  Formalization note (encoding): "the diagonal is a closed subscheme" is Mathlib's
`IsSeparated`; `X` is a scheme if it is isomorphic to a Mathlib scheme `Y` with `Y ⟶ ⊤_ Scheme` (`= Spec ℤ`)
separated.  A Mathlib scheme is *not* required to be separated, so Mathlib's `Scheme` is the paper's prescheme. -/
@[blueprint "def:0.S1-scheme-lrs"
  (statement := /-- If the diagonal of $X\times_SX$ is a closed subscheme, then the $S$-prescheme $(X,p)$ is called an
    \emph{$S$-scheme}. \dots{} We say that $X$ is a \emph{scheme}, if $(X,p_{\mathbb Z})$ is a
    $\operatorname{Spec}(\mathbb Z)$-scheme. (p.~118.) Formalization note (encoding): a scheme in the paper's sense is a
    separated Mathlib scheme (Mathlib's \texttt{Scheme} is the paper's prescheme). -/)
  (latexEnv := "definition")]
def IsScheme (X : LocallyRingedSpace.{u}) : Prop :=
  ∃ Y : Scheme.{u}, Nonempty (Y.toLocallyRingedSpace ≅ X) ∧
    IsSeparated (CategoryTheory.Limits.terminal.from Y)

/-- `Spec B` as a locally ringed space (encoding). -/
abbrev specLRS (B : Type u) [CommRing B] : LocallyRingedSpace.{u} :=
  (Spec (CommRingCat.of B)).toLocallyRingedSpace

/-- `(X, p)` is an algebraic `B`-prescheme (`B` noetherian): `p : X ⟶ Spec B` is of finite type.

> We shall be particularly interested in B-schemes where B is a noetherian ring. Assuming this, a B-prescheme (or,
> B-scheme) is said to be algebraic if it is of finite type over Spec(B) (i.e., the structural morphism of the
> B-prescheme to Spec(B) is of finite type). (pp. 118–119)

Definition (pp. 118–119).  Formalization note (encoding): "of finite type" is `LocallyOfFiniteType` and
`QuasiCompact` (as in `IsAlgebraicScheme`); `X` is transported to a Mathlib scheme by an isomorphism. -/
@[blueprint "def:0.S1-algebraic-b-prescheme-lrs"
  (statement := /-- We shall be particularly interested in $\mathbf B$-schemes where $\mathbf B$ is a noetherian ring. Assuming this,
    a $\mathbf B$-prescheme (or $\mathbf B$-scheme) is said to be \emph{algebraic} if it is of finite type over
    $\operatorname{Spec}(\mathbf B)$. (pp.~118--119.) Formalization note (encoding): ``of finite type'' is
    ``locally of finite type and quasi-compact''. -/)
  (latexEnv := "definition")]
def LocallyRingedSpace.IsAlgebraicPreschemeOver (B : Type u) [CommRing B] (X : LocallyRingedSpace.{u})
    (p : X ⟶ specLRS B) : Prop :=
  IsNoetherianRing B ∧ ∃ (Y : Scheme.{u}) (e : Y.toLocallyRingedSpace ≅ X),
    LocallyOfFiniteType (Scheme.Hom.mk (e.hom ≫ p) : Y ⟶ Spec (CommRingCat.of B)) ∧
    QuasiCompact (Scheme.Hom.mk (e.hom ≫ p) : Y ⟶ Spec (CommRingCat.of B))

/-- `(X, p)` is an algebraic `B`-scheme: an algebraic `B`-prescheme (`B` noetherian) with `p` separated (the diagonal
over `Spec B` is closed).  Definition (pp. 118–119), see `LocallyRingedSpace.IsAlgebraicPreschemeOver` and `IsScheme`. -/
@[blueprint "def:0.S1-algebraic-b-scheme-lrs"
  (statement := /-- An algebraic $\mathbf B$-scheme is a $\mathbf B$-scheme (the diagonal over $\operatorname{Spec}(\mathbf B)$ is a
    closed subscheme) that is of finite type over $\operatorname{Spec}(\mathbf B)$, $\mathbf B$ noetherian.
    (pp.~118--119.) Formalization note (encoding): separated, locally of finite type and quasi-compact. -/)
  (latexEnv := "definition")]
def LocallyRingedSpace.IsAlgebraicSchemeOver (B : Type u) [CommRing B] (X : LocallyRingedSpace.{u})
    (p : X ⟶ specLRS B) : Prop :=
  IsNoetherianRing B ∧ ∃ (Y : Scheme.{u}) (e : Y.toLocallyRingedSpace ≅ X),
    LocallyOfFiniteType (Scheme.Hom.mk (e.hom ≫ p) : Y ⟶ Spec (CommRingCat.of B)) ∧
    QuasiCompact (Scheme.Hom.mk (e.hom ≫ p) : Y ⟶ Spec (CommRingCat.of B)) ∧
    IsSeparated (Scheme.Hom.mk (e.hom ≫ p) : Y ⟶ Spec (CommRingCat.of B))

/-- The category `𝓜*(𝔄l/B)`: the full subcategory of `𝓜(𝔄l/B)` of coherent modules.

> Let us denote by 𝓜*(𝔄l/B) the full subcategory of 𝓜(𝔄l/B) of those which are coherent. (p. 124)

Definition (p. 124).  This is the property of objects of `𝓜(ℛ/B)`; the functor to `𝓜(ℛ)` is `ι ⋙ RModuleOver.forget`. -/
@[blueprint "def:0.S2-coherent-algebraic-modules"
  (statement := /-- Let us denote by $\mathcal M^*(\mathcal{A}l/\mathbf B)$ the full subcategory of $\mathcal M(\mathcal{A}l/\mathbf B)$
    of those which are coherent. (p.~124.) Formalization note (encoding): the object property ``algebraic
    $\mathbf B$-scheme and coherent'' on $\mathcal M(\mathcal R/\mathbf B)$. -/)
  (latexEnv := "definition")]
def algebraicCoherentModules (B : Type u) [CommRing B] : ObjectProperty (RModuleOver (specLRS B)) :=
  fun N => LocallyRingedSpace.IsAlgebraicSchemeOver B N.left.X N.hom ∧ N.left.IsCoherent

/-- The category `𝒥*(𝔄l/B)`: the full subcategory of `𝒥(𝔄l/B)` of coherent ideals.

> Let us denote by 𝒥*(𝔄l/B) the full subcategry [sic] of 𝒥(𝔄l/B) of those which are coherent ... (p. 128)

Definition (p. 128).  The misprint "subcategry" is kept in the quotation. -/
@[blueprint "def:0.S2-coherent-algebraic-ideals"
  (statement := /-- Let us denote by $\mathcal J^*(\mathcal{A}l/\mathbf B)$ the full subcategory of $\mathcal J(\mathcal{A}l/\mathbf B)$
    of those which are coherent. (p.~128.) Formalization note (encoding): the object property ``algebraic
    $\mathbf B$-scheme and coherent'' on $\mathcal J(\mathcal R/\mathbf B)$. -/)
  (latexEnv := "definition")]
def algebraicCoherentIdeals (B : Type u) [CommRing B] : ObjectProperty (RIdealOver (specLRS B)) :=
  fun N => LocallyRingedSpace.IsAlgebraicSchemeOver B N.left.X N.hom ∧ N.left.toRModule.IsCoherent

/-- `g : P ⟶ Q` induces an isomorphism of the restriction of `P` to `A` onto the restriction of `Q` to `A'`.

Formalization note (encoding): the restriction of a local-ringed space to a subset that is not open (here the
preimages of a quasi-compact subset `T`) is not available in Mathlib.  An isomorphism between the restrictions
`(A, O_P|A)` and `(A', O_Q|A')` induced by `g` is a homeomorphism `A → A'` (for the subspace topologies) such that
the maps of structure sheaves are isomorphisms; the stalks of `O_P|A` at `x ∈ A` are the stalks `O_{P,x}`, and a
morphism of sheaves is an isomorphism iff it is so on all stalks, so this is: `g` maps `A` homeomorphically onto
`A'` and `g_x : O_{Q,g x} → O_{P,x}` is an isomorphism for every `x ∈ A`. -/
def RestrictsToIso {P Q : LocallyRingedSpace.{u}} (g : P ⟶ Q) (A : Set P) (A' : Set Q) : Prop :=
  ∃ h : Set.MapsTo g.base A A',
    IsHomeomorph (h.restrict g.base A A') ∧ ∀ x ∈ A, IsIso (g.stalkMap x)

/-- The object `(X, J)` (with its structure morphism `p`) of `𝓜*(𝔄l/B)`, for `J` coherent (encoding). -/
def algebraicCoherentModule (B : Type u) [CommRing B] {X : LocallyRingedSpace.{u}}
    (p : X ⟶ specLRS B) (hX : LocallyRingedSpace.IsAlgebraicSchemeOver B X p) (J : OModules X)
    (hJ : (RModule.mk X J).IsCoherent) : (algebraicCoherentModules B).FullSubcategory :=
  ⟨CostructuredArrow.mk (Y := RModule.mk X J) p, hX, hJ⟩

/-- The canonical morphism `(f, φ) : (X', J') → (X, f_*(J'))` of `𝓜*(𝔄l/B)`, where `φ : f^*(f_*(J')) → J'` is the
canonical `f`-epimorphism (assumed epi) (p. 126, encoding). -/
def algebraicCoherentModuleMap (B : Type u) [CommRing B] {X' X : LocallyRingedSpace.{u}}
    (p' : X' ⟶ specLRS B) (p : X ⟶ specLRS B) (hX' : LocallyRingedSpace.IsAlgebraicSchemeOver B X' p')
    (hX : LocallyRingedSpace.IsAlgebraicSchemeOver B X p) (f : X' ⟶ X) (hf : f ≫ p = p') (J' : OModules X')
    (hJ' : (RModule.mk X' J').IsCoherent)
    (hfJ' : (RModule.mk X ((OModules.pushforward f).obj J')).IsCoherent)
    (hε : Epi ((OModules.pullbackPushforwardAdjunction f).counit.app J')) :
    algebraicCoherentModule B p' hX' J' hJ' ⟶
      algebraicCoherentModule B p hX ((OModules.pushforward f).obj J') hfJ' :=
  ObjectProperty.homMk (CostructuredArrow.homMk
    (⟨f, (OModules.pullbackPushforwardAdjunction f).counit.app J', hε⟩ :
      RModule.Hom (RModule.mk X' J') (RModule.mk X ((OModules.pushforward f).obj J')))
    hf)

/-- The morphism `f : X' → X` of algebraic `B`-schemes is projective, in the first definition (p. 126).

> Let f: X′ → X be a morphism of algebraic B-schemes. Suppose we have a coherent sheaf of O_{X′}-modules J′ on X′ such
> that the canonical homomorphism of f_*(J′) to J′ is an f-epimorphism. Suppose that f_*(J′) is coherent. Let (N′, Φ′)
> and (N, Φ) be the blowings-up of (X′, J′) and (X, f_*(J′)), respectively, in the category 𝓜*(𝔄l/B) ... We then have a
> canonical morphism (f̃, φ̃): N′ → N such that Φ∘(f̃, φ̃) = (f, φ)∘Φ′ ... (p. 126)

> We say that f is projective if for every quasi-compact (resp. compact) subset T of the underlying topological space
> of X, we can find a coherent sheaf J′ on X′, as above, such that J′ | f⁻¹(T) is invertible on X′ | f⁻¹(T) and that
> f̃ induces an isomorphism of X̃′ | (f∘h′)⁻¹(T) to X | h⁻¹(T). (p. 126)

Definition (p. 126), the *first* definition of "projective" (the second is `IsProjectiveOver`, p. 132; the
paper does not show that they agree, and this is not proved here).  Formalization notes (encoding and
deviations):
* misprint: the paper writes `X | h⁻¹(T)` for the target; since `h : X̃ → X`, `h⁻¹(T)` is a subset of `X̃`, so the
  faithful reading (used here) is `X̃ | h⁻¹(T)` (a tilde is missing).
* "we can find `J′` ... such that" and the blowings-up are existential: `J′`, the two blowings-up and the
  canonical morphism `ψ = (f̃, φ̃)` (determined by (**), so that "some" and "any" blowing-up agree when they exist)
  are existentially quantified; `ψ` is required to satisfy `ψ ≫ Φ = Φ′ ≫ (f, φ)`.
* the restrictions to `f⁻¹(T)` and to `(f∘h′)⁻¹(T)`, `h⁻¹(T)` of non-open subsets are encoded stalkwise
  (`RestrictsToIso`); "`J′|f⁻¹(T)` is invertible on `X′|f⁻¹(T)`" is encoded as invertibility at every point of
  `f⁻¹(T)` in a neighbourhood in `X′` (equivalent for the coherent `J′`, by coherence).
* "quasi-compact subset" is `IsCompact`. -/
@[blueprint "def:0.S2-projective-first"
  (statement := /-- Let $f\colon X'\to X$ be a morphism of algebraic $\mathbf B$-schemes, $J'$ a coherent sheaf on $X'$ such that the canonical homomorphism of $f_*(J')$ to $J'$ is an $f$-epimorphism and $f_*(J')$ is coherent, and let $(N',\Phi')$, $(N,\Phi)$ be the blowings-up of $(X',J')$, $(X,f_*(J'))$ in $\mathcal M^*(\mathcal{A}l/\mathbf B)$, with canonical morphism $(\tilde f,\tilde\varphi)\colon N'\to N$ such that $\Phi\circ(\tilde f,\tilde\varphi)=(f,\varphi)\circ\Phi'$ (p.~126; summary). We say that $f$ is \emph{projective} if for every quasi-compact subset $\mathbf T$ of the underlying topological
    space of $X$, we can find a coherent sheaf $J'$ on $X'$, as above, such that $J'|f^{-1}(\mathbf T)$ is invertible on
    $X'|f^{-1}(\mathbf T)$ and that $\tilde f$ induces an isomorphism of $\tilde X'|(f\circ h')^{-1}(\mathbf T)$ to
    $\tilde X|h^{-1}(\mathbf T)$. (p.~126.) Formalization notes: the printed target $X|h^{-1}(\mathbf T)$ is read
    $\tilde X|h^{-1}(\mathbf T)$ (misprint: a tilde is missing); restrictions to non-open subsets are encoded stalkwise
    (homeomorphism of the subspaces and isomorphisms of stalks); the blowings-up and $J'$ are existentially quantified;
    ``quasi-compact'' is \texttt{IsCompact}. -/)
  (latexEnv := "definition")]
def IsProjectiveFirst (B : Type u) [CommRing B] {X' X : LocallyRingedSpace.{u}}
    (p' : X' ⟶ specLRS B) (p : X ⟶ specLRS B) (hX' : LocallyRingedSpace.IsAlgebraicSchemeOver B X' p')
    (hX : LocallyRingedSpace.IsAlgebraicSchemeOver B X p) (f : X' ⟶ X) (hf : f ≫ p = p') : Prop :=
  ∀ T : Set X, IsCompact T →
    ∃ (J' : OModules X') (hJ' : (RModule.mk X' J').IsCoherent)
      (hfJ' : (RModule.mk X ((OModules.pushforward f).obj J')).IsCoherent)
      (hε : Epi ((OModules.pullbackPushforwardAdjunction f).counit.app J')),
      (∀ x ∈ f.base ⁻¹' T, (RModule.mk X' J').IsInvertibleAt x) ∧
      ∃ (N' N : (algebraicCoherentModules B).FullSubcategory)
        (Φ' : N' ⟶ algebraicCoherentModule B p' hX' J' hJ')
        (Φ : N ⟶ algebraicCoherentModule B p hX ((OModules.pushforward f).obj J') hfJ')
        (ψ : N' ⟶ N),
        IsBlowingUp ((algebraicCoherentModules B).ι ⋙ RModuleOver.forget _) Φ' ∧
        IsBlowingUp ((algebraicCoherentModules B).ι ⋙ RModuleOver.forget _) Φ ∧
        ψ ≫ Φ = Φ' ≫ algebraicCoherentModuleMap B p' p hX' hX f hf J' hJ' hfJ' hε ∧
        RestrictsToIso ψ.hom.left.f ((Φ'.hom.left.f ≫ f).base ⁻¹' T) (Φ.hom.left.f.base ⁻¹' T)

/-- The category `𝓜(pre-𝔄l/B)` restricted to coherent modules: the full subcategory of `𝓜(ℛ/B)` of coherent modules
over algebraic `B`-preschemes (the second alternative of assertion (b), p. 124). -/
@[blueprint "def:0.S2-coherent-algebraic-premodules"
  (statement := /-- The full subcategory of $\mathcal M(\mathcal{A}l/\mathbf B)$ (or, of $\mathcal M(\mathrm{pre}\text{-}\mathcal{A}l/\mathbf B)$)
    of those which are coherent, where $\mathbf B$ is a noetherian ring. (p.~124, assertion (b).) Formalization note
    (encoding): the object property ``algebraic $\mathbf B$-prescheme and coherent''. -/)
  (latexEnv := "definition")]
def algebraicCoherentPreModules (B : Type u) [CommRing B] :
    ObjectProperty (RModuleOver (specLRS B)) :=
  fun N => LocallyRingedSpace.IsAlgebraicPreschemeOver B N.left.X N.hom ∧ N.left.IsCoherent

/-- The case `T = X` of `IsProjectiveFirst`, as printed: `J′` is invertible and `f̃` (and `h′`) is an isomorphism.

> As is easily seen, if f is a morphism of algebraic B-schemes, then we have only to consider the case in which T is
> the underlying topological space of X so that J′ is required to be invertible and that f̃ (and h′) is required to
> be an isomorphism. (p. 126)

Formalization note (encoding): "(and `h′`)" is read as the additional requirement that `h′` is an isomorphism. -/
@[blueprint "def:0.S2-projective-first-reduced"
  (statement := /-- \dots{} we have only to consider the case in which $\mathbf T$ is the underlying topological space of $X$ so that
    $J'$ is required to be invertible and that $\tilde f$ (and $h'$) is required to be an isomorphism. (p.~126.)
    Formalization note (encoding): the existence of $J'$, of the blowings-up and of the canonical morphism as in the
    definition of projective, with $J'$ invertible and $\tilde f$ and $h'$ isomorphisms. -/)
  (latexEnv := "definition")]
def IsProjectiveFirstReduced (B : Type u) [CommRing B] {X' X : LocallyRingedSpace.{u}}
    (p' : X' ⟶ specLRS B) (p : X ⟶ specLRS B) (hX' : LocallyRingedSpace.IsAlgebraicSchemeOver B X' p')
    (hX : LocallyRingedSpace.IsAlgebraicSchemeOver B X p) (f : X' ⟶ X) (hf : f ≫ p = p') : Prop :=
  ∃ (J' : OModules X') (hJ' : (RModule.mk X' J').IsCoherent)
    (hfJ' : (RModule.mk X ((OModules.pushforward f).obj J')).IsCoherent)
    (hε : Epi ((OModules.pullbackPushforwardAdjunction f).counit.app J')),
    (RModule.mk X' J').IsInvertible ∧
    ∃ (N' N : (algebraicCoherentModules B).FullSubcategory)
      (Φ' : N' ⟶ algebraicCoherentModule B p' hX' J' hJ')
      (Φ : N ⟶ algebraicCoherentModule B p hX ((OModules.pushforward f).obj J') hfJ')
      (ψ : N' ⟶ N),
      IsBlowingUp ((algebraicCoherentModules B).ι ⋙ RModuleOver.forget _) Φ' ∧
      IsBlowingUp ((algebraicCoherentModules B).ι ⋙ RModuleOver.forget _) Φ ∧
      ψ ≫ Φ = Φ' ≫ algebraicCoherentModuleMap B p' p hX' hX f hf J' hJ' hfJ' hε ∧
      IsIso ψ.hom.left.f ∧ IsIso Φ'.hom.left.f

/-- For morphisms of algebraic `B`-schemes it suffices to consider `T = X`.

> As is easily seen, if f is a morphism of algebraic B-schemes, then we have only to consider the case in which T is
> the underlying topological space of X so that J′ is required to be invertible and that f̃ (and h′) is required to
> be an isomorphism. (p. 126)

Stated without argument (p. 126, "As is easily seen"); not proved here. -/
@[blueprint "prop:0.S2-projective-first-reduction"
  (statement := /-- As is easily seen, if $f$ is a morphism of algebraic $\mathbf B$-schemes, then we have only to consider the case in
    which $\mathbf T$ is the underlying topological space of $X$ so that $J'$ is required to be invertible and that
    $\tilde f$ (and $h'$) is required to be an isomorphism. (p.~126.) Formalization note: stated as the equivalence of
    the definition of projective with its case $\mathbf T=X$. Not proved here: stated without argument. -/)
  (latexEnv := "proposition")]
def ProjectiveFirstReduction : Prop :=
  ∀ (B : Type u) [CommRing B] (X' X : LocallyRingedSpace.{u}) (p' : X' ⟶ specLRS B)
    (p : X ⟶ specLRS B) (hX' : LocallyRingedSpace.IsAlgebraicSchemeOver B X' p') (hX : LocallyRingedSpace.IsAlgebraicSchemeOver B X p)
    (f : X' ⟶ X) (hf : f ≫ p = p'),
    IsProjectiveFirst B p' p hX' hX f hf ↔ IsProjectiveFirstReduced B p' p hX' hX f hf

/-- The algebraic `B`-scheme `(X, p)` is projective (first definition): its structural morphism `p : X ⟶ Spec B` is
projective.

> We say that an algebraic B-scheme (resp. an analytic C-space) X is projective if the structural morphism of X to
> Spec(B) (resp. to Spec(C)) is projective. (p. 126)

Definition (p. 126).  Formalization note (encoding): `Spec B` is an algebraic `B`-scheme (`B` noetherian), with the
identity as structure morphism. -/
@[blueprint "def:0.S2-projective-scheme-first"
  (statement := /-- We say that an algebraic $\mathbf B$-scheme $X$ is \emph{projective} if the structural morphism of $X$ to
    $\operatorname{Spec}(\mathbf B)$ is projective. (p.~126.) Formalization note (encoding): projectivity of morphisms
    is the first definition (p.~126). -/)
  (latexEnv := "definition")]
def IsProjectiveSchemeFirst (B : Type u) [CommRing B] {X : LocallyRingedSpace.{u}}
    (p : X ⟶ specLRS B) (hX : LocallyRingedSpace.IsAlgebraicSchemeOver B X p) : Prop :=
  ∃ hB : LocallyRingedSpace.IsAlgebraicSchemeOver B (specLRS B) (𝟙 _),
    IsProjectiveFirst B p (𝟙 _) hX hB p (Category.comp_id p)

/-- A projective morphism of algebraic `B`-schemes is proper in the sense of Grothendieck.

> A projective morphism of algebraic B-schemes ... f: X′ → X is proper in the sense of Grothendieck ... (pp. 126–127)

Stated without proof (pp. 126–127: "A projective morphism ... is proper in the sense of Grothendieck", no
argument or citation); not proved here.  Formalization note: stated for morphisms of Mathlib schemes (algebraic
`B`-schemes are schemes) and Mathlib's `IsProper`. -/
@[blueprint "prop:0.S2-projective-first-proper"
  (statement := /-- A projective morphism of algebraic $\mathbf B$-schemes $f\colon X'\to X$ is \emph{proper} in the sense of Grothendieck.
    (pp.~126--127.) Formalization note: for the first definition of projective morphism. Not proved here: stated
    without argument or citation. -/)
  (latexEnv := "proposition")]
def ProjectiveFirstIsProper : Prop :=
  ∀ (B : Type u) [CommRing B] (X' X : Scheme.{u}) (p' : X' ⟶ Spec (CommRingCat.of B))
    (p : X ⟶ Spec (CommRingCat.of B))
    (hX' : LocallyRingedSpace.IsAlgebraicSchemeOver B X'.toLocallyRingedSpace p'.toLRSHom)
    (hX : LocallyRingedSpace.IsAlgebraicSchemeOver B X.toLocallyRingedSpace p.toLRSHom) (f : X' ⟶ X) (hf : f ≫ p = p'),
    IsProjectiveFirst B p'.toLRSHom p.toLRSHom hX' hX f.toLRSHom
      (by exact congrArg Scheme.Hom.toLRSHom hf) → IsProper f

/-- The direct image of a coherent sheaf under a proper morphism of algebraic `B`-schemes is coherent.

> (The coherency of f_*(J′) follows that of J′ if f is proper.)^{14′} (p. 126)

Cited (footnote 14′, p. 126: Grauert, *Ein Theorem der analytischen Garbentheorie und die Modulräume komplexer
Strukturen*, Publ. Math. IHES 5); not proved here.  Formalization note: the cited reference is the analytic
(proper direct image) theorem; the statement used here for algebraic `B`-schemes is Grothendieck's finiteness
theorem for proper morphisms (EGA III 3.2.1), which the paper does not cite. -/
@[blueprint "prop:0.S2-coherent-direct-image"
  (statement := /-- (The coherency of $f_*(J')$ follows that of $J'$ if $f$ is proper.) (p.~126, footnote $14'$.) Formalization note: for
    morphisms of algebraic $\mathbf B$-schemes; the paper's reference is Grauert's analytic theorem. Not proved here:
    cited (footnote $14'$). -/)
  (latexEnv := "proposition")]
def CoherentDirectImageOfProper : Prop :=
  ∀ (B : Type u) [CommRing B] (X' X : Scheme.{u}) (p' : X' ⟶ Spec (CommRingCat.of B))
    (p : X ⟶ Spec (CommRingCat.of B))
    (_ : LocallyRingedSpace.IsAlgebraicSchemeOver B X'.toLocallyRingedSpace p'.toLRSHom)
    (_ : LocallyRingedSpace.IsAlgebraicSchemeOver B X.toLocallyRingedSpace p.toLRSHom) (f : X' ⟶ X) (_ : f ≫ p = p'),
    IsProper f → ∀ J' : OModules X'.toLocallyRingedSpace,
      (RModule.mk X'.toLocallyRingedSpace J').IsCoherent →
      (RModule.mk X.toLocallyRingedSpace ((OModules.pushforward f.toLRSHom).obj J')).IsCoherent

/-- The basic existence theorem of blowing-up: every `ℛ`-module admits a blowing-up in `𝓜(ℛ)` (identity functor).

> The basic existence theorem of blowing-up is that for the category 𝓜(ℛ) with the identity functor to itself.
> Namely, we can prove that every ℛ-module admits a blowing-up in the category of ℛ-modules 𝓜(ℛ). (p. 123)

Argued: "The basic existence theorem of blowing-up can be thus proved" (p. 125), after the printed construction of
`(P, Φ)` (pp. 124–125) and its two claims, both stated without proof on p. 125: "We see that N = (P, I) … is an
ℛ-module and that there exists a natural morphism Φ: N → M …" (`ConstructionIsRModule`) and "It is not difficult to
prove that (P, Φ) is a blowing-up of M in the category 𝓜(ℛ)" (`ConstructionIsBlowingUp`).  Proved from these two claims,
which enter as explicit hypotheses (assumed, as in the paper): `basicExistenceOfBlowingUp_of_construction`
(`Hironaka/Ch0/BlowingUpConstruction.lean`).  Grothendieck's observation (footnotes 13 and 14, cited) is stated in
`Hironaka/Ch0/BlowingUpProj.lean` (`GrothendieckObservation`); the construction itself is `IsConstruction`. -/
@[blueprint "thm:0.S2-basic-existence"
  (statement := /-- \textbf{The basic existence theorem of blowing-up} is that for the category $\mathcal M(\mathcal R)$ with the
    identity functor to itself. Namely, we can prove that every $\mathcal R$-module admits a blowing-up in the
    category of $\mathcal R$-modules $\mathcal M(\mathcal R)$. (p.~123.) Proved from the two claims of p.~125, which the paper
    states without proof and which enter as hypotheses. -/)
  (proof := /-- The paper prints the construction of $(P,\Phi)$ (pp.~124--125) and states that $N=(P,I)$ is an
    $\mathcal R$-module with a natural morphism $\Phi\colon N\to M$ (\cref{prop:0.S2-construction-is-rmodule}, stated without
    argument, assumed) and that $(P,\Phi)$ is a blowing-up of $M$ in $\mathcal M(\mathcal R)$
    (\cref{thm:0.S2-construction-blowing-up}, stated without proof, assumed). ``The basic existence theorem of blowing-up can
    be thus proved'': every $M$ admits a blowing-up (\cref{def:0.S2-admits-blowing-up}). (Lean:
    \texttt{basicExistenceOfBlowingUp\_of\_construction}.) -/)
  (proofUses := ["prop:0.S2-construction-is-rmodule", "thm:0.S2-construction-blowing-up",
    "def:0.S2-admits-blowing-up"])
  (latexEnv := "theorem")]
def BasicExistenceOfBlowingUp : Prop := ∀ M : RModule.{u}, HasBlowingUp (𝟭 RModule.{u}) M

/-- Existence of blowing-up for `𝓜(ℛ/S)` (with respect to the canonical functor to `𝓜(ℛ)`).

> An immediate consequence is the existence theorem of blowing-up for the category 𝓜(ℛ/S). (p. 123)

Argued by reference to the basic existence theorem ("an immediate consequence").  Proved from `BasicExistenceOfBlowingUp` as
`existenceOfBlowingUpOver_of_basic` (`Hironaka/Ch0/BlowingUpDeductions.lean`). -/
@[blueprint "prop:0.S2-existence-over-base"
  (statement := /-- An immediate consequence is the existence theorem of blowing-up for the category $\mathcal M(\mathcal R/S)$.
    (p.~123.) -/)
  (proof := /-- Let $M=(X,J)$ with $p\colon X\to S$. By the basic existence theorem the $\mathcal R$-module $T(M)$ has a
    blowing-up $(P,\Phi)$ in $\mathcal M(\mathcal R)$, $\Phi=(f,\varphi)$. Give $P$ the structural morphism $f\circ p$;
    then $\Phi$ is a morphism of $(\mathcal R/S)$-modules, and the unique $\Psi$ in $\mathcal M(\mathcal R)$ with
    $\Phi'=\Phi\circ\Psi$ for a pair $(P',\Phi')$ over $S$ lies over $S$; it is unique among morphisms of
    $(\mathcal R/S)$-modules because these are determined by their underlying morphism. \textbf{Gap filled:} the structural
    morphism of $P$ and the verification that $\Psi$ lies over $S$ (not printed). (Lean:
    \texttt{existenceOfBlowingUpOver\_of\_basic}.) -/)
  (proofUses := ["thm:0.S2-basic-existence", "def:0.S2-blowing-up", "def:0.S2-module-over"])
  (latexEnv := "proposition")]
def ExistenceOfBlowingUpOver : Prop :=
  ∀ (S : LocallyRingedSpace.{u}) (M : RModuleOver S), HasBlowingUp (RModuleOver.forget S) M

/-- `𝓜(ℛ/S)` is closed under blowing-up in `𝓜(ℛ)`.

> In this sense, 𝓜(ℛ/S) is closed under blowing-up in 𝓜(ℛ). (p. 124)

Argued by reference to the preceding paragraph (the existence theorem for `𝓜(ℛ/S)`).  Proved from `BasicExistenceOfBlowingUp`
as `modulesOverClosedUnderBlowingUp_of_basic` (`Hironaka/Ch0/BlowingUpDeductions.lean`).  The statement is repeated on p. 127: "whereas 𝓜(ℛ/S) is". -/
@[blueprint "prop:0.S2-modules-over-closed"
  (statement := /-- In this sense, $\mathcal M(\mathcal R/S)$ is closed under blowing-up in $\mathcal M(\mathcal R)$. (p.~124; again
    p.~127, ``whereas $\mathcal M(\mathcal R/S)$ is''.) -/)
  (proof := /-- Apply the basic existence theorem to $T(M)$ and give the blowing-up $(P,\Phi)$ the structural morphism
    $f\circ p$, as in the proof of the existence theorem for $\mathcal M(\mathcal R/S)$; then $(T(P),T(\Phi))=(P,\Phi)$
    is a blowing-up of $T(M)$ in $\mathcal M(\mathcal R)$ by construction. \textbf{Gap filled:} the lifting of the
    universal property to $\mathcal M(\mathcal R/S)$ (not printed). (Lean:
    \texttt{modulesOverClosedUnderBlowingUp\_of\_basic}.) -/)
  (proofUses := ["thm:0.S2-basic-existence", "prop:0.S2-existence-over-base", "def:0.S2-closed-under-blowing-up"])
  (latexEnv := "proposition")]
def ModulesOverClosedUnderBlowingUp : Prop :=
  ∀ S : LocallyRingedSpace.{u}, IsClosedUnderBlowingUp (RModuleOver.forget S)

/-- Assertion (a): the quasi-coherent modules over schemes (resp. preschemes) are closed under blowing-up in `𝓜(ℛ)`.

> It can be proved that the following categories (with obvious functors to 𝓜(ℛ)) are closed under blowing-up in
> 𝓜(ℛ): (a) The full subcategory of 𝓜(𝔖) (or, of 𝓜(pre-𝔖)) of those which are quasi-coherent. (p. 124)

Stated with a sketch: "The assertions of (a) and (b) follow from this fact [that (P, Φ) is a blowing-up of M in 𝓜(ℛ)] and
the result stated in the preceding paragraph [Grothendieck's observation, p. 124]" (p. 125).  Proved here along that
derivation, as `quasicoherentClosedUnderBlowingUp_of_construction` (`Hironaka/Ch0/BlowingUpClosed.lean`), from four
statements the paper makes and does not prove: this fact (`Construction.ConstructionIsRModule`,
`Construction.ConstructionIsBlowingUp`, p. 125), Grothendieck's observation (`GrothendieckObservation`, cited,
footnote 13, p. 124) and the uniqueness of blowing-ups (`BlowingUpUnique`, p. 123); the unprinted steps are gaps filled
and proved.  Formalization note (encoding): both alternatives (schemes and preschemes) are asserted. -/
@[blueprint "thm:0.S2-closed-quasicoherent"
  (statement := /-- It can be proved that the following categories (with obvious functors to $\mathcal M(\mathcal R)$) are closed
    under blowing-up in $\mathcal M(\mathcal R)$: (a) The full subcategory of $\mathcal M(\mathfrak S)$ (or, of
    $\mathcal M(\mathrm{pre}\text{-}\mathfrak S)$) of those which are quasi-coherent. (p.~124.) The paper derives (a) and (b)
    from the fact that $(P,\Phi)$ is a blowing-up of $M$ in $\mathcal M(\mathcal R)$ and from Grothendieck's observation
    (p.~125); proved here from these and from the uniqueness of blowing-ups, which the paper states without proof. -/)
  (proof := /-- Let $M$ be quasi-coherent on a scheme (resp.\ prescheme). By the construction, $M$ has a blowing-up
    $(N,\Phi)$ in $\mathcal M(\mathcal R)$ (the basic existence theorem, p.~125). \textbf{Gap filled:} $N$ is invertible,
    hence quasi-coherent; the part of $N$ over an open set is a blowing-up of the restriction of $M$; over an affine open
    set $M\cong S(A,J)$, and by Grothendieck's observation and the uniqueness of blowing-ups $N\to M$ is there
    $P(A,J)\to S(A,J)$, i.e.\ $\operatorname{Proj}S_A(J)\to\operatorname{Spec}A$. So the space of $N$ is a prescheme and
    $N\to M$ is separated (the separatedness of $\operatorname{Proj}$ is Mathlib's), hence the space of $N$ is a scheme if
    that of $M$ is. A blowing-up in $\mathcal M(\mathcal R)$ of an object of the full subcategory, lying in it, is a
    blowing-up in the subcategory. (Lean: \texttt{quasicoherentClosedUnderBlowingUp\_of\_construction}.) -/)
  (proofUses := ["thm:0.S2-construction-blowing-up", "prop:0.S2-construction-is-rmodule",
    "thm:0.S2-grothendieck-observation", "prop:0.S2-blowing-up-unique", "def:0.S2-closed-under-blowing-up"])
  (latexEnv := "theorem")]
def QuasicoherentClosedUnderBlowingUp : Prop :=
  IsClosedUnderBlowingUp (ObjectProperty.ι (fun M : RModule.{u} => IsScheme M.X ∧ M.IsQuasicoherent)) ∧
  IsClosedUnderBlowingUp (ObjectProperty.ι (fun M : RModule.{u} => IsPrescheme M.X ∧ M.IsQuasicoherent))

/-- Assertion (b): the coherent modules over algebraic `B`-schemes (resp. `B`-preschemes), `B` noetherian, are closed
under blowing-up in `𝓜(ℛ)`.

> (b) The full subcategory of 𝓜(𝔄l/B) (or, of 𝓜(pre-𝔄l/B)) of those which are coherent, where B is a noetherian
> ring. (p. 124)

Stated with a sketch, as for (a) (p. 125).  Proved here along that derivation, as
`coherentClosedUnderBlowingUp_of_construction` (`Hironaka/Ch0/BlowingUpClosed.lean`), from the same four statements
that the paper makes and does not prove (see `QuasicoherentClosedUnderBlowingUp`); the unprinted steps are gaps filled
and proved. -/
@[blueprint "thm:0.S2-closed-coherent"
  (statement := /-- (b) The full subcategory of $\mathcal M(\mathcal{A}l/\mathbf B)$ (or, of $\mathcal M(\mathrm{pre}\text{-}\mathcal{A}l/\mathbf B)$)
    of those which are coherent, where $\mathbf B$ is a noetherian ring. (p.~124.) The paper derives it from the fact that
    $(P,\Phi)$ is a blowing-up of $M$ in $\mathcal M(\mathcal R)$ and from Grothendieck's observation (p.~125); proved here
    from these and from the uniqueness of blowing-ups, which the paper states without proof. -/)
  (proof := /-- As for (a). Let $M$ be coherent over an algebraic $\mathbf B$-scheme (resp.\ prescheme), with structure
    morphism $p$, and $(N,\Phi)$ its blowing-up in $\mathcal M(\mathcal R)$ given by the construction (p.~125).
    \textbf{Gap filled:} $N$ is invertible, hence coherent; locally $M\cong S(A,J)$ with $J$ finitely generated, and $N\to M$ is
    $P(A,J)\to S(A,J)$ by Grothendieck's observation and the uniqueness of blowing-ups, so it is separated, locally of
    finite type and quasi-compact ($\operatorname{Proj}$ of the symmetric algebra of a finitely generated module is
    Mathlib's). Composing with $p$, the space of $N$ with the structure morphism $\Phi\circ p$ is an algebraic
    $\mathbf B$-scheme (resp.\ prescheme), and $(N,\Phi)$ is a blowing-up in the full subcategory. (Lean:
    \texttt{coherentClosedUnderBlowingUp\_of\_construction}.) -/)
  (proofUses := ["thm:0.S2-construction-blowing-up", "prop:0.S2-construction-is-rmodule",
    "thm:0.S2-grothendieck-observation", "prop:0.S2-blowing-up-unique", "def:0.S2-closed-under-blowing-up"])
  (latexEnv := "theorem")]
def CoherentClosedUnderBlowingUp : Prop :=
  ∀ (B : Type u) [CommRing B], IsNoetherianRing B →
    IsClosedUnderBlowingUp ((algebraicCoherentModules B).ι ⋙ RModuleOver.forget _) ∧
    IsClosedUnderBlowingUp ((algebraicCoherentPreModules B).ι ⋙ RModuleOver.forget _)

/-- The existence theorem of blowing-up in `𝓜*(𝔄l/B)`.

> Then, by the assertion (b), we have the existence theorem of blowing-up in the category 𝓜*(𝔄l/B). (p. 124)

Argued by reference to (b).  Proved from `CoherentClosedUnderBlowingUp` as `existenceOfBlowingUpCoherent_of_closed`
(`Hironaka/Ch0/BlowingUpDeductions.lean`). -/
@[blueprint "prop:0.S2-existence-coherent"
  (statement := /-- Then, by the assertion (b), we have the existence theorem of blowing-up in the category
    $\mathcal M^*(\mathcal{A}l/\mathbf B)$. (p.~124.) -/)
  (proof := /-- $\mathcal M^*(\mathcal{A}l/\mathbf B)$ is the category of the first alternative of (b). That it is closed
    under blowing-up in $\mathcal M(\mathcal R)$ means that every object admits a blowing-up in it (with
    $(T(P),T(\Phi))$ a blowing-up of $T(M)$ in $\mathcal M(\mathcal R)$); forgetting the second requirement gives the
    existence theorem. (Lean: \texttt{existenceOfBlowingUpCoherent\_of\_closed}.) -/)
  (proofUses := ["thm:0.S2-closed-coherent", "def:0.S2-closed-under-blowing-up",
    "def:0.S2-coherent-algebraic-modules"])
  (latexEnv := "proposition")]
def ExistenceOfBlowingUpCoherent : Prop :=
  ∀ (B : Type u) [CommRing B], IsNoetherianRing B → ∀ M : (algebraicCoherentModules B).FullSubcategory,
    HasBlowingUp ((algebraicCoherentModules B).ι ⋙ RModuleOver.forget _) M

/-- A morphism of `ℛ`-ideals is determined by `f`, and exists iff `J₁ = θ(J₂)O_{X₁}`.

> In other words, a morphism of (ℛ/S)-ideals as above is uniquely determined by the morphism f = (f, θ): X₁ → X₂ with
> θ: O_{X₂} → O_{X₁}, in such a way that J₁ = θ(J₂)O_{X₁} and φ is the natural homomorphism of f*(J₂) onto
> θ(J₂)O_{X₁}. (p. 127)

Stated without argument (p. 127, "In other words"); not proved here.  Formalization note: "uniquely determined by
`f`" is that two morphisms with the same `f` are equal, and "`J₁ = θ(J₂)O_{X₁}`" is the equality of the subobjects
`J₁ ⊆ O_{X₁}` and `f⁻¹(J₂) ⊆ O_{X₁}` (`pullbackIdeal`). -/
@[blueprint "prop:0.S2-ideal-morphism-determined"
  (statement := /-- In other words, a morphism of $(\mathcal R/S)$-ideals as above is uniquely determined by the morphism
    $f=(\mathbf f,\theta)\colon X_1\to X_2$ with $\theta\colon O_{X_2}\to O_{X_1}$, in such a way that
    $J_1=\theta(J_2)O_{X_1}$ and $\varphi$ is the natural homomorphism of $f^*(J_2)$ onto $\theta(J_2)O_{X_1}$.
    (p.~127.) Not proved here: stated without argument. -/)
  (latexEnv := "proposition")]
def IdealMorphismDeterminedByUnderlying : Prop :=
  (∀ (I₁ I₂ : RIdeal.{u}) (a b : I₁ ⟶ I₂), a.toHom.f = b.toHom.f → a = b) ∧
  ∀ (I₁ I₂ : RIdeal.{u}) (f : I₁.X ⟶ I₂.X),
    (∃ a : I₁ ⟶ I₂, a.toHom.f = f) ↔ Subobject.mk I₁.ι = Subobject.mk (I₂.pullbackIdeal f).ι

/-- For `f : X₁ ⟶ X₂` and a sheaf of ideals `J₂` on `X₂` there is a unique sheaf of ideals `J₁` on `X₁` and a unique
morphism of ideals `(X₁, J₁) → (X₂, J₂)` over `f`.

> Let f = (f, θ): X₁ → X₂ be a morphism of local-ringed spaces, where X_i = (X_i, O_{X_i}) for i = 1, 2. Let J₂ be a
> sheaf of ideals on X₂. Then, as was remarked above, there exists a unique sheaf of ideals J₁ on X₁ and a unique
> morphism of ℛ-ideals from (X₁, J₁) to (X₂, J₂), such that f undergoes this morphism. (p. 128)

Stated by reference to the remark of p. 127 ("as was remarked above", itself without argument); not proved here.
Formalization note (encoding): the sheaf of ideals `J₁` is a subobject of `O_{X₁}`; the morphism is the epimorphism
`φ` compatible with the monomorphisms, and is unique. -/
@[blueprint "prop:0.S2-inverse-image-unique"
  (statement := /-- Let $f=(\mathbf f,\theta)\colon X_1\to X_2$ be a morphism of local-ringed spaces, where
    $X_i=(\mathbf X_i,O_{X_i})$ for $i=1,2$. Let $J_2$ be a sheaf of ideals on $X_2$. Then, as was remarked above, there
    exists a unique sheaf of ideals $J_1$ on $X_1$ and a unique morphism of $\mathcal R$-ideals from $(X_1,J_1)$ to
    $(X_2,J_2)$, such that $f$ undergoes this morphism. (p.~128.) Not proved here: by reference to an earlier remark
    without argument. -/)
  (latexEnv := "proposition")]
def InverseImageIdealUnique : Prop :=
  ∀ (I₂ : RIdeal.{u}) (X₁ : LocallyRingedSpace.{u}) (f : X₁ ⟶ I₂.X),
    ∃! J₁ : Subobject (OModules.unit X₁),
      ∃ φ : (OModules.pullback f).obj I₂.J ⟶ (J₁ : OModules X₁),
        Epi φ ∧ (OModules.pullback f).map I₂.ι ≫ OModules.pullbackUnitToUnit f = φ ≫ J₁.arrow ∧
        ∀ φ' : (OModules.pullback f).obj I₂.J ⟶ (J₁ : OModules X₁),
          Epi φ' → (OModules.pullback f).map I₂.ι ≫ OModules.pullbackUnitToUnit f = φ' ≫ J₁.arrow →
          φ' = φ

/-- For `𝒥*(𝔄l/B)` the pullback `f⁻¹(J)` of a coherent ideal under a morphism of algebraic `B`-schemes is again
coherent (the property of `𝒥′` assumed on p. 129).

> Suppose we have a subcategory ℛ′ of ℛ (or of ℛ/S) such that every (X, J) ∈ 𝒥′ has X ∈ ℛ′ and that, if f: X′ → X
> belongs to ℛ′, then the canonical morphism (f, φ): (X′, f⁻¹(J)) → (X, J) belongs to 𝒥′. For instance, the
> categories 𝒥*(𝔄l/B) and 𝒥*(𝔄n/K) have this property. (p. 129)

Stated without argument (p. 129, "For instance"); not proved here.  Only the algebraic case `𝒥*(𝔄l/B)` is stated. -/
@[blueprint "prop:0.S2-coherent-ideals-inverse-image"
  (statement := /-- Suppose we have a subcategory $\mathcal R'$ of $\mathcal R$ (or of $\mathcal R/S$) such that every
    $(X,J)\in\mathcal J'$ has $X\in\mathcal R'$ and that, if $f\colon X'\to X$ belongs to $\mathcal R'$, then the canonical
    morphism $(f,\varphi)\colon(X',f^{-1}(J))\to(X,J)$ belongs to $\mathcal J'$. For instance, the categories
    $\mathcal J^*(\mathcal{A}l/\mathbf B)$ and $\mathcal J^*(\mathcal{A}n/\mathbf K)$ have this property. (p.~129.)
    Formalization note: only $\mathcal J^*(\mathcal{A}l/\mathbf B)$: the inverse image of a coherent ideal under a morphism of
    algebraic $\mathbf B$-schemes is coherent. Not proved here: stated without argument. -/)
  (latexEnv := "proposition")]
def CoherentIdealInverseImageCoherent : Prop :=
  ∀ (B : Type u) [CommRing B], IsNoetherianRing B →
    ∀ (I : RIdeal.{u}) (pI : I.X ⟶ specLRS B), LocallyRingedSpace.IsAlgebraicSchemeOver B I.X pI →
      I.toRModule.IsCoherent →
      ∀ (X' : LocallyRingedSpace.{u}) (pX' : X' ⟶ specLRS B), LocallyRingedSpace.IsAlgebraicSchemeOver B X' pX' →
        ∀ f : X' ⟶ I.X, f ≫ pI = pX' → (I.pullbackIdeal f).toRModule.IsCoherent

/-- `𝒥(ℛ)` is not closed under blowing-up in `𝓜(ℛ)`.

> The category 𝒥(ℛ/S) is not closed under blowing-up in 𝓜(ℛ), whereas 𝓜(ℛ/S) is. (p. 127)

Stated without argument (p. 127); not proved here.  Formalization note (encoding, degenerate-case slip): read for
`S = Spec ℤ`, i.e. for `𝒥(ℛ/ℤ) = 𝒥(ℛ)`; for an empty `S` the category `𝒥(ℛ/S)` has only empty spaces and is trivially
closed under blowing-up, so the printed sentence cannot hold for every `S` (recorded as a slip).

Truth checked by hand (it stays a statement, not proved here), assuming Grothendieck's observation (footnote 13, p. 124)
and the uniqueness of blowing-ups (`BlowingUpUnique`), both stated by the paper.  Take `A = k[x, y]/(xy)`, `J = (x, y)`,
`M = (Spec A, J)`, an `ℛ`-ideal.  The syzygies of `(x, y)` over `A` are generated by `(y, 0)` and `(0, x)` (write
`a = a₀ + a₁(x)x + a₂(y)y`, `b` likewise: `ax + by = 0` forces `a ∈ (y)`, `b ∈ (x)`), so
`Sym_A(J) = A[T₁, T₂]/(yT₁, xT₂)`, while the Rees algebra also kills `T₁T₂`.  The blowing-up of `T(M)` in `𝓜(ℛ)` is
`(Proj Sym_A(J), J₁)`; over the origin its fibre is all of `ℙ¹_k`, an irreducible component `C`; on the chart `T₁ = 1` it is
`Spec k[x, t]/(xt)` with `y = 0` and `C = {x = 0}`, and at the generic point `η` of `C` the element `t` is a unit, so
`x = y = 0` in `O_η = k(t)`.  If a blowing-up `(P, Φ)` of `M` in `𝒥(ℛ)` had `(T(P), T(Φ))` a blowing-up of `T(M)` in `𝓜(ℛ)`,
then by uniqueness `T(P) ≅ (Proj Sym_A(J), J₁)` over `T(M)`, and the ideal of `P` is `f⁻¹(J) = J·O_P`; at (the point
corresponding to) `η`, `(J₁)_η ≅ O_η ≠ 0` but `(J·O_P)_η = 0`, a contradiction.  So `𝒥(ℛ)` is not closed under
blowing-up in `𝓜(ℛ)`. -/
@[blueprint "prop:0.S2-ideals-not-closed"
  (statement := /-- The category $\mathcal J(\mathcal R/S)$ is not closed under blowing-up in $\mathcal M(\mathcal R)$, whereas
    $\mathcal M(\mathcal R/S)$ is. (p.~127.) Formalization note: read for $S=\operatorname{Spec}\mathbb Z$, i.e.\ for
    $\mathcal J(\mathcal R)$ (for an empty $S$ the printed sentence fails trivially). Not proved here: stated without
    argument. -/)
  (latexEnv := "proposition")]
def IdealsNotClosedUnderBlowingUp : Prop := ¬ IsClosedUnderBlowingUp RIdeal.toRModuleFunctor.{u}

/-- The existence of blowing-up in `𝓜(ℛ/S)` implies the same in `𝒥(ℛ/S)`, for any `S`.

> However, the existence of blowing-up in the category 𝓜(ℛ/S) implies the same in the category 𝒥(ℛ/S). In fact, let
> M = (X, J) be an (ℛ/S)-ideal ... Let H be the union of the annihilators of θ(J)ⁿ in O_P for all positive integers
> n. ... It can be easily seen that (N′, Φ′) with N′ = (P′, I′) is a blowing-up of M in the category 𝒥(ℛ/S).
> (p. 127; the misprint "exitence" in the next sentence is not reproduced)

The construction (annihilators of the powers of the ideal, the support `P′` of `O_P/H`, the sheaf of ideals `I′`
generated by the image of `θ(J)`) is printed, and its decisive step is stated without argument ("It can be easily
seen").  The construction is formalized in `Hironaka/Ch0/BlowingUpIdeals.lean`, where its claim is
`AnnihilatorConstructionIsBlowingUp`; the deduction is proved from that claim (assumed, as in the paper) as
`idealExistenceFromModules_of_annihilator` (same file). -/
@[blueprint "prop:0.S2-ideal-existence"
  (statement := /-- However, the existence of blowing-up in the category $\mathcal M(\mathcal R/S)$ implies the same in the category
    $\mathcal J(\mathcal R/S)$. In fact, let $M=(X,J)$ be an $(\mathcal R/S)$-ideal \dots{} Let $H$ be the union of the
    annihilators of $\theta(J)^n$ in $O_P$ for all positive integers $n$. \dots{} It can be easily seen that $(N',\Phi')$
    with $N'=(P',I')$ is a blowing-up of $M$ in the category $\mathcal J(\mathcal R/S)$. (p.~127.) The construction is
    printed; its verification is stated as ``easily seen'' and enters as a hypothesis. -/)
  (proof := /-- Let $I$ be an $(\mathcal R/S)$-ideal. Viewed as an $(\mathcal R/S)$-module it has, by hypothesis, a
    blowing-up $(N,\Phi)$ in $\mathcal M(\mathcal R/S)$. The construction of the annihilators of $\theta(J)^n$ gives
    $(N',\Phi')$, which is a blowing-up of $I$ in $\mathcal J(\mathcal R/S)$ by the claim ``It can be easily seen''
    (\cref{prop:0.S2-annihilator-construction-blowing-up}, stated without proof, assumed as in the paper). (Lean:
    \texttt{idealExistenceFromModules\_of\_annihilator}.) -/)
  (proofUses := ["prop:0.S2-annihilator-construction-blowing-up", "def:0.S2-annihilator-hom"])
  (latexEnv := "proposition")]
def IdealExistenceFromModules : Prop :=
  ∀ S : LocallyRingedSpace.{u},
    (∀ M : RModuleOver S, HasBlowingUp (RModuleOver.forget S) M) →
    ∀ I : RIdealOver S, HasBlowingUp (RIdealOver.toRModule S) I

/-- The existence theorem of blowing-up in `𝒥*(𝔄l/B)`.

> We can easily deduce the existence theorem of blowing-up in the category 𝒥*(𝔄l/B) (resp. 𝒥*(𝔄n/K)) from that in
> 𝓜*(𝔄l/B) (resp. 𝓜*(𝔄n/K)). (See the preceding paragraph where we deduce the existence theorem for 𝒥(ℛ/S) from
> that for 𝓜(ℛ/S).) (p. 128)

Argued by reference to the preceding paragraph.  Proved, from (b), the claim of p. 127, and the paper's own next
sentence of p. 128 (`CoherentIdealsClosedInIdeals`, stated without argument; assumed, as in the paper, it supplies the
membership of the constructed object in `𝒥*(𝔄l/B)`): `existenceOfBlowingUpCoherentIdeals_of_annihilator`
(`Hironaka/Ch0/BlowingUpIdealsCoherent.lean`).  Only the algebraic case is
stated (the analytic case is out of scope). -/
@[blueprint "prop:0.S2-existence-coherent-ideals"
  (statement := /-- We can easily deduce the existence theorem of blowing-up in the category $\mathcal J^*(\mathcal{A}l/\mathbf B)$ from
    that in $\mathcal M^*(\mathcal{A}l/\mathbf B)$. (See the preceding paragraph where we deduce the existence theorem
    for $\mathcal J(\mathcal R/S)$ from that for $\mathcal M(\mathcal R/S)$.) (p.~128.) -/)
  (proof := /-- A coherent ideal $I$ is an object of $\mathcal M^*(\mathcal{A}l/\mathbf B)$. By (b)
    (\cref{thm:0.S2-closed-coherent}) it has a blowing-up $(N,\Phi)$ there that is also a blowing-up in
    $\mathcal M(\mathcal R)$, hence in $\mathcal M(\mathcal R/\mathbf B)$ (\textbf{gap filled}: the lifting of the universal
    property over $\mathbf B$). The construction of p.~127 gives a blowing-up $(N',\Phi')$ of $I$ in
    $\mathcal J(\mathcal R/\mathbf B)$ (\cref{prop:0.S2-annihilator-construction-blowing-up}, stated, not proved). That $N'$
    lies in $\mathcal J^*(\mathcal{A}l/\mathbf B)$ is not printed in the deduction; it is the paper's own next sentence
    (\cref{prop:0.S2-ideals-star-closed}, stated without argument, assumed). As the subcategory is full, $\Phi'$ is a blowing-up there (\textbf{gap filled}). Lean:
    \texttt{existenceOfBlowingUpCoherentIdeals\_of\_annihilator}. -/)
  (proofUses := ["thm:0.S2-closed-coherent", "prop:0.S2-annihilator-construction-blowing-up",
    "prop:0.S2-ideals-star-closed", "def:0.S2-annihilator-hom", "def:0.S2-coherent-algebraic-ideals"])
  (latexEnv := "proposition")]
def ExistenceOfBlowingUpCoherentIdeals : Prop :=
  ∀ (B : Type u) [CommRing B], IsNoetherianRing B →
    ∀ I : (algebraicCoherentIdeals B).FullSubcategory,
      HasBlowingUp ((algebraicCoherentIdeals B).ι ⋙ RIdealOver.toRModule _) I

/-- `𝒥*(𝔄l/B)` is closed under blowing-up in `𝒥(ℛ/B)`, in the sense of p. 128.

> We can also see that 𝒥*(𝔄l/B) is closed under blowing-up in 𝒥(ℛ/B) in the sense that a blowing-up of an object of
> the first category in the second category is necessarily a blowing-up of the same object in the first category.
> (p. 128)

Stated without argument (p. 128); not proved here.  It enters as an explicit hypothesis of
`existenceOfBlowingUpCoherentIdeals_of_annihilator` (`Hironaka/Ch0/BlowingUpIdealsCoherent.lean`), where it supplies the
membership step of the deduction of p. 128 (assumed, as in the paper). -/
@[blueprint "prop:0.S2-ideals-star-closed"
  (statement := /-- We can also see that $\mathcal J^*(\mathcal{A}l/\mathbf B)$ is closed under blowing-up in $\mathcal J(\mathcal R/\mathbf B)$
    in the sense that a blowing-up of an object of the first category in the second category is necessarily a
    blowing-up of the same object in the first category. (p.~128.) Not proved here: stated without argument; it enters as
    a hypothesis of the deduction of the existence theorem in $\mathcal J^*(\mathcal{A}l/\mathbf B)$. -/)
  (latexEnv := "proposition")]
def CoherentIdealsClosedInIdeals : Prop :=
  ∀ (B : Type u) [CommRing B], IsNoetherianRing B →
    ∀ (I : (algebraicCoherentIdeals B).FullSubcategory) (P : RIdealOver (specLRS B))
      (Φ : P ⟶ I.obj), IsBlowingUp (RIdealOver.toRModule _) Φ →
      ∃ hP : algebraicCoherentIdeals B P,
        IsBlowingUp ((algebraicCoherentIdeals B).ι ⋙ RIdealOver.toRModule _)
          (ObjectProperty.homMk (X := ⟨P, hP⟩) (Y := I) Φ)

/-- `(P, f)` is a blowing-up of the `ℛ`-ideal `(X, J)` in a category `𝒥′` over the subcategory `ℛ′`, by (1), (2) of p. 129.

> Suppose we have a subcategory ℛ′ of ℛ (or of ℛ/S) such that every (X, J) ∈ 𝒥′ has X ∈ ℛ′ and that, if f: X′ → X
> belongs to ℛ′, then the canonical morphism (f, φ): (X′, f⁻¹(J)) → (X, J) belongs to 𝒥′. ... we can define a
> blowing-up (N, Φ) of (X, J) ∈ 𝒥′ in the category 𝒥′, where N = (P, I) and Φ = (f, φ), by the following universal
> mapping property:
> (1) P and f: P → X belong to ℛ′, and f⁻¹(J) is invertible, and
> (2) for every pair (P′, f′) of P′ and f′: P′ → X both belonging to ℛ′, if f′⁻¹(J) is invertible, there exists a
> unique g: P′ → P in ℛ′ such that f′ = f∘g.
> Here (N, Φ) is determined by (P, f). (p. 129)

Definition (p. 129).  Formalization notes (encoding): `ℛ′` is a full subcategory of `ℛ/S` given by the property `R'`
of an `S`-space (`R' X pX`); `𝒥′` enters only through the hypothesis that it contains the canonical morphisms
`(P, f⁻¹(J)) → (X, J)`, so `(N, Φ)` is `((P, f⁻¹(J)), (f, φ))` and the data is `(P, f)`.  Correspondence with the
project: `Hironaka.MonoidalTransformation X B` (`Hironaka/Statements.lean`) is this universal property for `ℛ′` the
category of all schemes (the paper remarks on p. 166 that the two agree), with the center `B` and its ideal sheaf; it
is not duplicated here.  The correspondence of p. 129 between coherent sheaves of ideals and algebraic subschemes `D` ("`D` is defined by `J`", "the monoidal transformation of `X` with center `D`") is the project's encoding `Subscheme X := X.IdealSheafData`. -/
@[blueprint "def:0.S2-blowing-up-ideals"
  (statement := /-- Suppose we have a subcategory $\mathcal R'$ of $\mathcal R$ (or of $\mathcal R/S$) such that every $(X,J)\in\mathcal J'$
    has $X\in\mathcal R'$ and that, if $f\colon X'\to X$ belongs to $\mathcal R'$, then the canonical morphism
    $(f,\varphi)\colon(X',f^{-1}(J))\to(X,J)$ belongs to $\mathcal J'$. We can define a \emph{blowing-up} $(N,\Phi)$ of
    $(X,J)\in\mathcal J'$ in the category $\mathcal J'$, where $N=(P,I)$ and $\Phi=(f,\varphi)$, by the following
    universal mapping property: (1) $P$ and $f\colon P\to X$ belong to $\mathcal R'$, and $f^{-1}(J)$ is invertible, and
    (2) for every pair $(P',f')$ of $P'$ and $f'\colon P'\to X$ both belonging to $\mathcal R'$, if $f'^{-1}(J)$ is
    invertible, there exists a unique $g\colon P'\to P$ in $\mathcal R'$ such that $f'=f\circ g$. (p.~129.)
    Formalization note (encoding): $\mathcal R'$ is a full subcategory given by a property of $S$-spaces; the
    correspondence with the monoidal transformation of the project (\texttt{MonoidalTransformation}) is that
    one is this property for $\mathcal R'$ the schemes. -/)
  (latexEnv := "definition")]
structure IsMonoidalBlowingUp {S : LocallyRingedSpace.{u}}
    (R' : ∀ X : LocallyRingedSpace.{u}, (X ⟶ S) → Prop) (I : RIdeal.{u}) (pI : I.X ⟶ S)
    {P : LocallyRingedSpace.{u}} (pP : P ⟶ S) (f : P ⟶ I.X) : Prop where
  /-- `P` and `f` belong to `ℛ′`. -/
  mem : R' P pP
  /-- `f` is a morphism over `S`. -/
  comm : f ≫ pI = pP
  /-- (1): `f⁻¹(J)` is invertible. -/
  invertible : (I.pullbackIdeal f).toRModule.IsInvertible
  /-- (2): the universal property. -/
  universal : ∀ (P' : LocallyRingedSpace.{u}) (pP' : P' ⟶ S) (f' : P' ⟶ I.X), R' P' pP' →
    f' ≫ pI = pP' → (I.pullbackIdeal f').toRModule.IsInvertible →
    ∃! g : P' ⟶ P, g ≫ pP = pP' ∧ g ≫ f = f'

end Hironaka

end
