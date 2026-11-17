/-
Copyright (c) 2026 Daattavya Aggarwal, Minhyong Kim, Oisin Kim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daattavya Aggarwal, Minhyong Kim, Oisin Kim
-/
module

public import Mathlib.CategoryTheory.Comma.StructuredArrow.Basic
public import Hironaka.Ch0.BlowingUpModules

/-!
# Ch. 0 §2 (pp. 123–124): three deductions

The paper derives three statements from others, in single sentences.  Each is proved here from the statement it names,
which enters as an explicit hypothesis (a `Prop` stated in `Hironaka/Ch0/BlowingUpModules.lean`); nothing else is assumed.

> The basic existence theorem of blowing-up is that for the category 𝓜(ℛ) with the identity functor to itself.
> Namely, we can prove that every ℛ-module admits a blowing-up in the category of ℛ-modules 𝓜(ℛ). An immediate
> consequence is the existence theorem of blowing-up for the category 𝓜(ℛ/S). In general, let 𝓜′ be a category with an
> obvious functor T: 𝓜′ → 𝓜(ℛ). We shall say that 𝓜′ is closed under blowing-up in the category 𝓜(ℛ), if every object M
> in 𝓜′ admits a blowing-up (P, Φ) in 𝓜′ (with respect to T) such that (T(P), T(Φ)) is a blowing-up of T(M) in 𝓜(ℛ).
> In this sense, 𝓜(ℛ/S) is closed under blowing-up in 𝓜(ℛ). (pp. 123–124)

> Then, by the assertion (b), we have the existence theorem of blowing-up in the category 𝓜*(𝔄l/B). (p. 124)

* `existenceOfBlowingUpOver_of_basic`: `BasicExistenceOfBlowingUp → ExistenceOfBlowingUpOver` ("an immediate consequence").
* `modulesOverClosedUnderBlowingUp_of_basic`: `BasicExistenceOfBlowingUp → ModulesOverClosedUnderBlowingUp` ("In this
  sense, 𝓜(ℛ/S) is closed under blowing-up in 𝓜(ℛ)").
* `existenceOfBlowingUpCoherent_of_closed`: `CoherentClosedUnderBlowingUp → ExistenceOfBlowingUpCoherent` ("by the
  assertion (b)").

The proofs hang on the blueprint nodes of the deduced statements (`prop:0.S2-existence-over-base`, `prop:0.S2-modules-over-closed`,
`prop:0.S2-existence-coherent`), in the pattern of `MainTheorem.II`.  The paper gives no more than these sentences.  Gaps filled (steps the text does not print) are recorded in the docstrings
of the helper declarations.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace Hironaka

universe u

namespace BlowingUpDeductions

variable {S : LocallyRingedSpace.{u}}

/-- Gap filled: the structure morphism of the blowing-up.  A blowing-up `(P, Φ)` of the `ℛ`-module `T(M)` carries no
structure morphism to `S`; it is given the one forced by `Φ`, namely `f ≫ p` where `Φ = (f, φ)` and `p : X ⟶ S` is that of
`M = (X, J)`.  This is the object `P` of `𝓜(ℛ/S)` of the deduction (p. 123, "an immediate consequence"). -/
def overObject (M : RModuleOver S) {P : RModule.{u}} (Φ : P ⟶ M.left) : RModuleOver S :=
  CostructuredArrow.mk (Y := P) (Φ.f ≫ M.hom)

/-- Gap filled: `Φ` is a morphism of `(ℛ/S)`-modules from `P` with the structure morphism `f ≫ p` (the compatibility
`f ≫ p = f ≫ p` is trivial). -/
def overHom (M : RModuleOver S) {P : RModule.{u}} (Φ : P ⟶ M.left) : overObject M Φ ⟶ M :=
  CostructuredArrow.homMk Φ rfl

/-- Gap filled: a morphism `Ψ : T(Q) ⟶ P` of `ℛ`-modules with `Ψ ≫ Φ = T(Ψ₀)` for a morphism `Ψ₀ : Q ⟶ M` of
`(ℛ/S)`-modules is itself a morphism of `(ℛ/S)`-modules `Q ⟶ P` (with the structure morphism `f ≫ p`): the structure
morphism of `Q` is `q = Ψ₀.f ≫ p = Ψ.f ≫ f ≫ p`. -/
def liftHom (M : RModuleOver S) {P : RModule.{u}} (Φ : P ⟶ M.left) {Q : RModuleOver S}
    (Ψ₀ : Q ⟶ M) (Ψ : Q.left ⟶ P) (h : Ψ ≫ Φ = Ψ₀.left) : Q ⟶ overObject M Φ :=
  CostructuredArrow.homMk Ψ (by
    have h1 : Ψ.f ≫ Φ.f = Ψ₀.left.f := congrArg RModule.Hom.f h
    have h2 : Ψ₀.left.f ≫ M.hom = Q.hom := CostructuredArrow.w Ψ₀
    have h3 : (Ψ.f ≫ Φ.f) ≫ M.hom = Q.hom := by rw [h1]; exact h2
    exact (Category.assoc _ _ _).symm.trans h3)

/-- The deduction of p. 123: if `(P, Φ)` is a blowing-up of `T(M)` in `𝓜(ℛ)`, then `Φ`, viewed as a morphism of
`(ℛ/S)`-modules from `(P, f ≫ p)`, is a blowing-up of `M` in `𝓜(ℛ/S)` with respect to the functor neglecting the structure
morphisms, and `(T(P), T(Φ)) = (P, Φ)` is a blowing-up of `T(M)` in `𝓜(ℛ)`.

Printed: "An immediate consequence is the existence theorem of blowing-up for the category 𝓜(ℛ/S)" and the definition of
"closed under blowing-up" (pp. 123–124).  Gap filled: the universal property in `𝓜(ℛ/S)` follows from that in `𝓜(ℛ)`:
existence of `Ψ` is `liftHom`, uniqueness is that a morphism of `(ℛ/S)`-modules is determined by its underlying
morphism of `ℛ`-modules (the forgetful functor is faithful). -/
theorem isBlowingUp_overHom (M : RModuleOver S) {P : RModule.{u}} (Φ : P ⟶ M.left)
    (hΦ : IsBlowingUp (𝟭 RModule.{u}) Φ) :
    IsBlowingUp (RModuleOver.forget S) (overHom M Φ) := by
  refine ⟨hΦ.invertible, fun Q Ψ₀ hQ => ?_⟩
  obtain ⟨Ψ, hΨ, huniq⟩ := hΦ.universal Q.left Ψ₀.left hQ
  refine ⟨liftHom M Φ Ψ₀ Ψ hΨ, ?_, fun Ξ hΞ => ?_⟩
  · apply CostructuredArrow.hom_ext
    exact hΨ
  · apply CostructuredArrow.hom_ext
    exact huniq Ξ.left (congrArg CommaMorphism.left hΞ)

/-- The deduction of p. 123 for `HasBlowingUp`, and of p. 124 for `IsClosedUnderBlowingUp`: given the basic existence
theorem, every `(ℛ/S)`-module `M` has a blowing-up `(P, Φ)` in `𝓜(ℛ/S)` such that `(T(P), T(Φ))` is a blowing-up of `T(M)`
in `𝓜(ℛ)`.  Printed steps: apply the basic existence theorem to the `ℛ`-module `T(M)` (p. 123), take as `P` that blowing-up
with the structure morphism forced by `Φ` and as `Φ` the same morphism (`isBlowingUp_overHom`; gaps filled there). -/
theorem exists_blowingUp_over (hbasic : BasicExistenceOfBlowingUp.{u}) (M : RModuleOver S) :
    ∃ (P : RModuleOver S) (Φ : P ⟶ M), IsBlowingUp (RModuleOver.forget S) Φ ∧
      IsBlowingUp (𝟭 RModule.{u}) ((RModuleOver.forget S).map Φ) := by
  obtain ⟨P, Φ, hΦ⟩ := hbasic ((RModuleOver.forget S).obj M)
  exact ⟨overObject M Φ, overHom M Φ, isBlowingUp_overHom M Φ hΦ, hΦ⟩

end BlowingUpDeductions

/-- "An immediate consequence is the existence theorem of blowing-up for the category 𝓜(ℛ/S)." (p. 123)

> The basic existence theorem of blowing-up is that for the category 𝓜(ℛ) with the identity functor to itself. ... An
> immediate consequence is the existence theorem of blowing-up for the category 𝓜(ℛ/S).

The hypothesis is the basic existence theorem (`BasicExistenceOfBlowingUp`, stated on p. 123; it is proved from the two
claims of p. 125, which are stated without proof, as `basicExistenceOfBlowingUp_of_construction`).  Proof: see
`BlowingUpDeductions.exists_blowingUp_over`.
Gap filled: the structure morphism of the blowing-up and the lifting of the universal property to `𝓜(ℛ/S)`. -/
theorem existenceOfBlowingUpOver_of_basic (hbasic : BasicExistenceOfBlowingUp.{u}) :
    ExistenceOfBlowingUpOver.{u} := fun _ M =>
  let ⟨P, Φ, h, _⟩ := BlowingUpDeductions.exists_blowingUp_over hbasic M
  ⟨P, Φ, h⟩

/-- "In this sense, 𝓜(ℛ/S) is closed under blowing-up in 𝓜(ℛ)." (p. 124)

> We shall say that 𝓜′ is closed under blowing-up in the category 𝓜(ℛ), if every object M in 𝓜′ admits a blowing-up
> (P, Φ) in 𝓜′ (with respect to T) such that (T(P), T(Φ)) is a blowing-up of T(M) in 𝓜(ℛ). In this sense, 𝓜(ℛ/S) is
> closed under blowing-up in 𝓜(ℛ).

The hypothesis is the basic existence theorem (as for `existenceOfBlowingUpOver_of_basic`).  Proof: the blowing-up of
`T(M)` in `𝓜(ℛ)` provided by the basic existence theorem, with the structure morphism forced by `Φ`, is the required
`(P, Φ)` (`BlowingUpDeductions.exists_blowingUp_over`); gap filled as there. -/
theorem modulesOverClosedUnderBlowingUp_of_basic (hbasic : BasicExistenceOfBlowingUp.{u}) :
    ModulesOverClosedUnderBlowingUp.{u} := fun _ M =>
  BlowingUpDeductions.exists_blowingUp_over hbasic M

/-- "Then, by the assertion (b), we have the existence theorem of blowing-up in the category 𝓜*(𝔄l/B)." (p. 124)

> Let us denote by 𝓜*(𝔄l/B) the full subcategory of 𝓜(𝔄l/B) of those which are coherent. Then, by the assertion (b), we
> have the existence theorem of blowing-up in the category 𝓜*(𝔄l/B).

The hypothesis is assertion (b) (`CoherentClosedUnderBlowingUp`: "It can be proved …", stated with a sketch; it is
proved from the construction of p. 125 in `Hironaka/Ch0/BlowingUpClosed.lean`, which builds on this file, so it enters
here as a hypothesis, as in the paper).  Proof: 𝓜*(𝔄l/B) is the category of the first alternative of (b); "closed under
blowing-up" includes that every object admits a blowing-up in that category (the definition, p. 123–124), which is the
existence theorem.  No gap: the deduction is the definition unfolded. -/
theorem existenceOfBlowingUpCoherent_of_closed (hb : CoherentClosedUnderBlowingUp.{u}) :
    ExistenceOfBlowingUpCoherent.{u} := fun B _ hB M =>
  let ⟨P, Φ, h, _⟩ := (hb B hB).1 M
  ⟨P, Φ, h⟩

end Hironaka

end
