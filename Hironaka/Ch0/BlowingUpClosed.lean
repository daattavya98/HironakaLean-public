/-
Copyright (c) 2026 Daattavya Aggarwal, Minhyong Kim, Oisin Kim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daattavya Aggarwal, Minhyong Kim, Oisin Kim
-/
module

public import Hironaka.Ch0.BlowingUpCharts
public import Hironaka.Ch0.BlowingUpLocality
public import Hironaka.Ch0.BlowingUpConstruction
public import Hironaka.Ch0.BlowingUpDeductions
public import Hironaka.Ch0.BlowingUpIdealsCoherent
public import Hironaka.Compat.AffineCharts
public import Hironaka.Compat.InvertibleModules
public import Hironaka.Compat.OModulesRestrict
public import Hironaka.Compat.RModuleRestrict

/-!
# Ch. 0 §2 (pp. 124-125): assertions (a) and (b) of p. 124

> It can be proved that the following categories (with obvious functors to 𝓜(ℛ)) are closed under blowing-up in
> 𝓜(ℛ): (a) The full subcategory of 𝓜(𝔖) (or, of 𝓜(pre-𝔖)) of those which are quasi-coherent. (b) The full
> subcategory of 𝓜(𝔄l/B) (or, of 𝓜(pre-𝔄l/B)) of those which are coherent, where B is a noetherian ring. (p. 124)

> The basic existence theorem of blowing-up can be thus proved. The assertions of (a) and (b) follow from this fact
> and the result stated in the preceding paragraph. (p. 125)

This file proves the two assertions along the printed derivation.  "This fact" is that the construction of
pp. 124-125 gives a blowing-up `(N, Φ)` of any `ℛ`-module `M` in `𝓜(ℛ)` (`Construction.ConstructionIsRModule`,
`Construction.ConstructionIsBlowingUp`, stated without proof on p. 125; hypotheses `hR`, `hB`); "the result stated in
the preceding paragraph" is Grothendieck's observation (`GrothendieckObservation`, cited, footnote 13, p. 124;
hypothesis `hG`); the uniqueness of blowing-ups (`BlowingUpUnique`, stated without proof, p. 123; hypothesis `hU`)
identifies the part of `N` over a chart with the blowing-up of Grothendieck's observation.  No other hypothesis is
used.

The steps the paper does not print are gaps filled and are proved: the blown-up module is quasi-coherent and coherent
when `M` is (an invertible module is; `Hironaka/Compat/InvertibleModules.lean`); the part of a blowing-up over an open
set is a blowing-up of the restriction (`Hironaka.isBlowingUp_restrictMap`); a quasi-coherent module on a prescheme is
locally `S(A, J)` (`Hironaka.RModule.exists_affine_chart`); hence `N` is locally `P(A, J)` over `S(A, J)`
(`exists_isSymmetricProjOver`); hence `N` is a prescheme and `N → M` is separated, and, for coherent `M`, of finite type
(`blowingUp_over_prescheme`, with `Hironaka/Ch0/BlowingUpCharts.lean`); and the blowing-up in `𝓜(ℛ)` is one in the
full subcategories (`isClosedUnderBlowingUp_of_prop`, `isClosedUnderBlowingUp_of_prop_over`).

* `exists_isSymmetricProjOver`: over a chart, the blowing-up is `P(A, J) ⟶ S(A, J)`;
* `blowingUp_over_prescheme`: the conclusion of the steps about the blown-up module and space;
* `isClosedUnderBlowingUp_of_prop`, `isClosedUnderBlowingUp_of_prop_over`: closure of a full subcategory;
* `Hironaka.quasicoherentClosedUnderBlowingUp_of_construction`, `Hironaka.coherentClosedUnderBlowingUp_of_construction`:
  assertions (a) and (b) of p. 124.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
open Hironaka ProjDegreeOne

noncomputable section

universe u

namespace Hironaka.BlowingUpClosed

/-- Steps (3)-(5).  Gap filled: the part of a blowing-up over a chart is `P(A, J) ⟶ S(A, J)`.

The paper does not print this step: over a chart where `M` is `S(A, J)`, a blowing-up of `M` is compared with
Grothendieck's `P(A, J) → S(A, J)` (p. 124) through the uniqueness of blowing-ups (p. 123).  Let
`Φ : N ⟶ M` be a blowing-up in `𝓜(ℛ)` of a quasi-coherent module `M` on a prescheme.  Around `x`, `M|V ≅ S(A, J)` with
`J` finitely generated if `M` is coherent (`RModule.exists_affine_chart`).  The part `N|Φ⁻¹(V) ⟶ M|V` is a blowing-up
(`isBlowingUp_restrictMap`), hence so is its composite with `M|V ≅ S(A, J)` (`isBlowingUp_comp_iso`); Grothendieck's
observation `hG` says that `P(A, J) ⟶ S(A, J)` is one too, so by the uniqueness `hU` the two are isomorphic over
`S(A, J)`.  The underlying morphisms of locally ringed spaces give `IsSymmetricProjOver`. -/
theorem exists_isSymmetricProjOver (hG : GrothendieckObservation.{u}) (hU : BlowingUpUnique.{u, u + 1, u})
    {M N : RModule.{u}} (Φ : N ⟶ M) (hΦ : IsBlowingUp (𝟭 RModule.{u}) Φ)
    (hP : IsPrescheme M.X) (hq : M.IsQuasicoherent) (x : M.X) :
    ∃ V : Opens M.X, x ∈ V ∧ IsSymmetricProjOver (fun A J => M.IsCoherent → Module.Finite A J) Φ.f V := by
  obtain ⟨V, hxV, A, J, ⟨δ⟩, hfin⟩ := RModule.exists_affine_chart M hP hq x
  obtain ⟨hepi, hGA⟩ := hG A J
  have h1 : IsBlowingUp (𝟭 RModule.{u}) (RModule.restrictMap Φ V ≫ δ.hom) :=
    isBlowingUp_comp_iso _ _ δ (isBlowingUp_restrictMap Φ hΦ V)
  obtain ⟨e, he⟩ := hU RModule.{u} (𝟭 _) (symmetricAffine A J) _ (symmetricProj A J) _
    (symmetricMorphism A J hepi) h1 hGA
  refine ⟨V, hxV, A, J, hfin, RModule.base.mapIso δ, RModule.base.mapIso e, ?_⟩
  have hf : e.hom.f ≫ structureLRS (symmetricGrading A J) =
      (RModule.restrictMap Φ V).f ≫ δ.hom.f := congrArg RModule.Hom.f he
  rw [RModule.restrictMap_f] at hf
  exact hf.symm

/-- Steps (2)-(7).  Gap filled: the blown-up module is quasi-coherent (coherent if `M` is), its space is a prescheme,
and the comparison morphism `N → M` of schemes is separated (and locally of finite type and quasi-compact if `M` is
coherent).

The paper states none of this.  Let `Φ : N ⟶ M` be a blowing-up in `𝓜(ℛ)`, with `M` quasi-coherent on a prescheme.
`N` is invertible by the definition of a blowing-up, hence quasi-coherent and coherent
(`RModule.isQuasicoherent_of_isInvertible`, `RModule.isCoherent_of_isInvertible`).  Over each chart `Φ` is
`Proj S_A(J) → Spec A` (`exists_isSymmetricProjOver`), so `N` is a prescheme (`isPrescheme_of_charts`), and the
properties that are local on the target and hold for these morphisms (separated; for finitely generated `J`, locally of
finite type and quasi-compact) hold for `Φ` (`isSeparated_of_charts`, `locallyOfFiniteType_of_charts`,
`quasiCompact_of_charts`). -/
theorem blowingUp_over_prescheme (hG : GrothendieckObservation.{u}) (hU : BlowingUpUnique.{u, u + 1, u})
    {M N : RModule.{u}} (Φ : N ⟶ M) (hΦ : IsBlowingUp (𝟭 RModule.{u}) Φ)
    (hP : IsPrescheme M.X) (hq : M.IsQuasicoherent) :
    N.IsQuasicoherent ∧ (M.IsCoherent → N.IsCoherent) ∧ IsPrescheme N.X ∧
      ∀ (Y : Scheme.{u}) (e : Y.toLocallyRingedSpace ≅ M.X) (Y' : Scheme.{u})
        (e' : Y'.toLocallyRingedSpace ≅ N.X),
        IsSeparated (Scheme.Hom.mk (e'.hom ≫ Φ.f ≫ e.inv) : Y' ⟶ Y) ∧
        (M.IsCoherent → LocallyOfFiniteType (Scheme.Hom.mk (e'.hom ≫ Φ.f ≫ e.inv) : Y' ⟶ Y) ∧
          QuasiCompact (Scheme.Hom.mk (e'.hom ≫ Φ.f ≫ e.inv) : Y' ⟶ Y)) := by
  have hch := exists_isSymmetricProjOver hG hU Φ hΦ hP hq
  have hch' : ∀ x : M.X, ∃ V : Opens M.X, x ∈ V ∧ IsSymmetricProjOver (fun _ _ => True) Φ.f V :=
    fun x => let ⟨V, hx, h⟩ := hch x; ⟨V, hx, h.mono fun _ _ _ => trivial⟩
  refine ⟨RModule.isQuasicoherent_of_isInvertible hΦ.invertible,
    fun _ => RModule.isCoherent_of_isInvertible hΦ.invertible, isPrescheme_of_charts Φ.f hch',
    fun Y e Y' e' => ⟨isSeparated_of_charts Φ.f Y e Y' e' hch', fun hc => ?_⟩⟩
  have hfin : ∀ x : M.X, ∃ V : Opens M.X, x ∈ V ∧
      IsSymmetricProjOver (fun A J => Module.Finite A J) Φ.f V :=
    fun x => let ⟨V, hx, h⟩ := hch x; ⟨V, hx, h.mono fun _ _ hJ => hJ hc⟩
  exact ⟨locallyOfFiniteType_of_charts Φ.f Y e Y' e' hfin, quasiCompact_of_charts Φ.f Y e Y' e' hfin⟩

/-- Step (8).  Gap filled: a property of `ℛ`-modules that is preserved by blowing-up in `𝓜(ℛ)` makes the full
subcategory it defines closed under blowing-up in `𝓜(ℛ)`.

By the basic existence theorem (`hbasic`) every `M` in the subcategory has a blowing-up `(N, Φ)` in `𝓜(ℛ)`; `N` is in
the subcategory by hypothesis, and a blowing-up in `𝓜(ℛ)` between objects of a full subcategory is a blowing-up in the
subcategory (`isBlowingUp_fullSubcategory`). -/
theorem isClosedUnderBlowingUp_of_prop (hbasic : BasicExistenceOfBlowingUp.{u})
    (Pr : ObjectProperty RModule.{u})
    (hcl : ∀ (M N : RModule.{u}) (Φ : N ⟶ M), Pr M → IsBlowingUp (𝟭 RModule.{u}) Φ → Pr N) :
    IsClosedUnderBlowingUp (ObjectProperty.ι Pr) := by
  intro M
  obtain ⟨N, Φ, hΦ⟩ := hbasic M.obj
  exact ⟨⟨N, hcl M.obj N Φ M.property hΦ⟩, ObjectProperty.homMk Φ,
    isBlowingUp_fullSubcategory Pr (𝟭 RModule.{u}) (hcl M.obj N Φ M.property hΦ) Φ hΦ, hΦ⟩

/-- Step (8), over `S`.  Gap filled: as `isClosedUnderBlowingUp_of_prop`, for a full subcategory of `(ℛ/S)`-modules
with the forgetful functor to `𝓜(ℛ)`; the blown-up module is given the structure morphism `Φ.f ≫ p`
(`BlowingUpDeductions.overObject`, `BlowingUpDeductions.overHom`). -/
theorem isClosedUnderBlowingUp_of_prop_over (hbasic : BasicExistenceOfBlowingUp.{u})
    {S : LocallyRingedSpace.{u}} (Pr : ObjectProperty (RModuleOver S))
    (hcl : ∀ (M : RModuleOver S) (N : RModule.{u}) (Φ : N ⟶ M.left), Pr M →
      IsBlowingUp (𝟭 RModule.{u}) Φ → Pr (BlowingUpDeductions.overObject M Φ)) :
    IsClosedUnderBlowingUp (ObjectProperty.ι Pr ⋙ RModuleOver.forget S) := by
  intro M
  obtain ⟨N, Φ, hΦ⟩ := hbasic ((RModuleOver.forget S).obj M.obj)
  exact ⟨⟨BlowingUpDeductions.overObject M.obj Φ, hcl M.obj N Φ M.property hΦ⟩,
    ObjectProperty.homMk (BlowingUpDeductions.overHom M.obj Φ),
    isBlowingUp_fullSubcategory Pr (RModuleOver.forget S) (hcl M.obj N Φ M.property hΦ)
      (BlowingUpDeductions.overHom M.obj Φ) (BlowingUpDeductions.isBlowingUp_overHom M.obj Φ hΦ), hΦ⟩

end Hironaka.BlowingUpClosed

namespace Hironaka
open BlowingUpClosed

/-- Assertion (a) of p. 124, proved along the printed derivation of p. 125.

> It can be proved that the following categories (with obvious functors to 𝓜(ℛ)) are closed under blowing-up in
> 𝓜(ℛ): (a) The full subcategory of 𝓜(𝔖) (or, of 𝓜(pre-𝔖)) of those which are quasi-coherent. (p. 124)

> The basic existence theorem of blowing-up can be thus proved. The assertions of (a) and (b) follow from this fact and
> the result stated in the preceding paragraph. (p. 125)

Steps.  (1) "This fact": the construction gives a blowing-up `(N, Φ)` of any `ℛ`-module `M` in `𝓜(ℛ)` (`hR`, `hB`:
`ConstructionIsRModule`, `ConstructionIsBlowingUp`, stated without proof, p. 125; assumed, as in the paper;
`basicExistenceOfBlowingUp_of_construction`).  (2) Gap filled: `N` is invertible, hence quasi-coherent
(`RModule.isQuasicoherent_of_isInvertible`).  (3) Gap filled: the part of `N` over an open set is a blowing-up of the
restriction of `M` (`isBlowingUp_restrictMap`).  (4) Gap filled: a quasi-coherent module on a prescheme is locally
`S(A, J)` (`RModule.exists_affine_chart`).  (5) "The result stated in the preceding paragraph": Grothendieck's
observation that `P(A, J)` is a blowing-up of `S(A, J)` (`hG`: `GrothendieckObservation`, cited, footnote 13, p. 124;
assumed, as in the paper), and the uniqueness of blowing-ups (`hU`: `BlowingUpUnique`, stated without proof, p. 123;
assumed, as in the paper), give that over a chart `N → M` is `P(A, J) → S(A, J)` (`exists_isSymmetricProjOver`).
(6) Gap filled: `Proj S_A(J) → Spec A` is separated (`isSeparated_structureMorphism`).  (7) Gap filled: hence `N` is a
prescheme and `N → M` is separated, so `N` is a scheme if `M` is (`isPrescheme_of_charts`, `isSeparated_of_charts`,
`isScheme_of_blowingUp`; `blowingUp_over_prescheme`).  (8) Gap filled: a blowing-up in `𝓜(ℛ)` of an object of the full
subcategory, which lies in it, is a blowing-up there (`isClosedUnderBlowingUp_of_prop`).

No hypothesis other than the four statements the paper prints is used. -/
theorem quasicoherentClosedUnderBlowingUp_of_construction
    (hR : Construction.ConstructionIsRModule.{u}) (hB : Construction.ConstructionIsBlowingUp.{u})
    (hG : GrothendieckObservation.{u}) (hU : BlowingUpUnique.{u, u + 1, u}) :
    QuasicoherentClosedUnderBlowingUp.{u} := by
  have hbasic := basicExistenceOfBlowingUp_of_construction hR hB
  refine ⟨isClosedUnderBlowingUp_of_prop hbasic _ ?_, isClosedUnderBlowingUp_of_prop hbasic _ ?_⟩
  · rintro M N Φ ⟨hM, hq⟩ hΦ
    obtain ⟨hNq, -, hNp, hsep⟩ := blowingUp_over_prescheme hG hU Φ hΦ
      (let ⟨Y, e, _⟩ := hM; ⟨Y, e⟩) hq
    exact ⟨isScheme_of_blowingUp Φ hM hNp fun Y e Y' e' => (hsep Y e Y' e').1, hNq⟩
  · rintro M N Φ ⟨hM, hq⟩ hΦ
    obtain ⟨hNq, -, hNp, -⟩ := blowingUp_over_prescheme hG hU Φ hΦ hM hq
    exact ⟨hNp, hNq⟩

/-- Assertion (b) of p. 124, proved along the printed derivation of p. 125.

> (b) The full subcategory of 𝓜(𝔄l/B) (or, of 𝓜(pre-𝔄l/B)) of those which are coherent, where B is a noetherian ring.
> (p. 124)

> The basic existence theorem of blowing-up can be thus proved. The assertions of (a) and (b) follow from this fact and
> the result stated in the preceding paragraph. (p. 125)

Steps, as for (a) (`quasicoherentClosedUnderBlowingUp_of_construction`).  (1) "This fact": the construction gives a
blowing-up `(N, Φ)` of any `ℛ`-module in `𝓜(ℛ)` (`hR`, `hB`: stated without proof, p. 125; assumed, as in the paper).
(2) Gap filled: `N` is invertible, hence coherent (`RModule.isCoherent_of_isInvertible`), and a coherent module is
quasi-coherent (`RModule.isQuasicoherent_of_isCoherent`).  (3) Gap filled: locality of blowing-up
(`isBlowingUp_restrictMap`).  (4) Gap filled: local form `S(A, J)` with `J` finitely generated
(`RModule.exists_affine_chart`).  (5) Grothendieck's observation (`hG`, cited, footnote 13, p. 124; assumed, as in the
paper) and the uniqueness of blowing-ups (`hU`, stated without proof, p. 123; assumed, as in the paper)
(`exists_isSymmetricProjOver`).  (6) Gap filled: `Proj S_A(J) → Spec A` is separated, and locally of finite type and
quasi-compact for finitely generated `J`.  (7) Gap filled: hence `N` is a prescheme and `N → M` is separated, locally of
finite type and quasi-compact; composed with the structure morphism of `M` over `Spec B` it makes `N` an algebraic
`B`-scheme (resp. `B`-prescheme) (`blowingUp_over_prescheme`, `isAlgebraicSchemeOver_of_blowingUp`,
`isAlgebraicPreschemeOver_of_blowingUp`).  (8) Gap filled: the blowing-up in `𝓜(ℛ)` is one in the full subcategory of
`(ℛ/B)`-modules, with structure morphism `Φ.f ≫ p` (`isClosedUnderBlowingUp_of_prop_over`).

No hypothesis other than the four statements the paper prints is used. -/
theorem coherentClosedUnderBlowingUp_of_construction
    (hR : Construction.ConstructionIsRModule.{u}) (hB : Construction.ConstructionIsBlowingUp.{u})
    (hG : GrothendieckObservation.{u}) (hU : BlowingUpUnique.{u, u + 1, u}) :
    CoherentClosedUnderBlowingUp.{u} := by
  have hbasic := basicExistenceOfBlowingUp_of_construction hR hB
  intro B _ hBn
  refine ⟨isClosedUnderBlowingUp_of_prop_over hbasic _ ?_, isClosedUnderBlowingUp_of_prop_over hbasic _ ?_⟩
  · rintro M N Φ ⟨hM, hco⟩ hΦ
    obtain ⟨-, hc, hNp, h⟩ := blowingUp_over_prescheme hG hU Φ hΦ
      (let ⟨_, Y, e, _⟩ := hM; ⟨Y, ⟨e⟩⟩) (RModule.isQuasicoherent_of_isCoherent hco)
    exact ⟨isAlgebraicSchemeOver_of_blowingUp B M.hom Φ hM hNp fun Y e Y' e' =>
      ⟨(h Y e Y' e').1, (h Y e Y' e').2 hco⟩, hc hco⟩
  · rintro M N Φ ⟨hM, hco⟩ hΦ
    obtain ⟨-, hc, hNp, h⟩ := blowingUp_over_prescheme hG hU Φ hΦ
      (let ⟨_, Y, e, _⟩ := hM; ⟨Y, ⟨e⟩⟩) (RModule.isQuasicoherent_of_isCoherent hco)
    exact ⟨isAlgebraicPreschemeOver_of_blowingUp B M.hom Φ hM hNp fun Y e Y' e' =>
      (h Y e Y' e').2 hco, hc hco⟩

end Hironaka

end
