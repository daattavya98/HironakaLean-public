/-
Copyright (c) 2026 Daattavya Aggarwal, Minhyong Kim, Oisin Kim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daattavya Aggarwal, Minhyong Kim, Oisin Kim
-/
module

public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Architect
public import Hironaka.Ch0.BlowingUpIdeals

/-!
# Ch. 0 §2 (p. 128): the existence of blowing-up in `𝒥*(𝔄l/B)`

> We can easily deduce the existence theorem of blowing-up in the category 𝒥*(𝔄l/B) (resp. 𝒥*(𝔄n/K)) from that in
> 𝓜*(𝔄l/B) (resp. 𝓜*(𝔄n/K)). (See the preceding paragraph where we deduce the existence theorem for 𝒥(ℛ/S) from that
> for 𝓜(ℛ/S).) (p. 128)

The deduction follows the construction of p. 127 (`Hironaka/Ch0/BlowingUpIdeals.lean`): take a blowing-up `(N, Φ)` of the
coherent ideal `I`, viewed as a module, in `𝓜*(𝔄l/B)` (which, by assertion (b), is also a blowing-up in `𝓜(ℛ)`, hence
in `𝓜(ℛ/B)`), and form `(N′, Φ′)`.  The paper does not print, in the deduction, that `N′ = (P′, I′)` is again an object
of `𝒥*(𝔄l/B)` (`P′` an algebraic `B`-scheme, `I′` coherent).  It states it, without argument, in the next sentence of
p. 128:

> We can also see that 𝒥*(𝔄l/B) is closed under blowing-up in 𝒥(ℛ/B) in the sense that a blowing-up of an object of the
> first category in the second category is necessarily a blowing-up of the same object in the first category. (p. 128)

This is `CoherentIdealsClosedInIdeals` (`Hironaka/Ch0/BlowingUpModules.lean`); it enters as an explicit hypothesis of the
theorem below (stated without argument, p. 128; assumed, as in the paper) and supplies the membership step (4).  Everything
else is proved: the theorem has the hypotheses (b), the claim of p. 127, and that sentence.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace Hironaka

/-- Gap filled: a blowing-up of `M` in a category `C` with respect to `T`, whose source `P` lies in a full subcategory
`Pr` containing `M`, is a blowing-up of `M` in the full subcategory (the factorization of a morphism of the
subcategory is a morphism of the subcategory, the subcategory being full).  This is the "universal property in the full
subcategory" used for `𝒥*(𝔄l/B) ⊆ 𝒥(ℛ/B)`. -/
theorem isBlowingUp_fullSubcategory {C : Type*} [Category C] (Pr : ObjectProperty C) (T : C ⥤ RModule.{u})
    {M : Pr.FullSubcategory} {P : C} (hP : Pr P) (Φ : P ⟶ M.obj) (h : IsBlowingUp T Φ) :
    IsBlowingUp (Pr.ι ⋙ T) (ObjectProperty.homMk (X := ⟨P, hP⟩) (Y := M) Φ) := by
  refine ⟨h.invertible, fun Q Ψ hQ => ?_⟩
  obtain ⟨χ, hχ, huniq⟩ := h.universal Q.obj Ψ.hom hQ
  refine ⟨ObjectProperty.homMk (X := Q) (Y := ⟨P, hP⟩) χ, ?_, fun ξ hξ => ?_⟩
  · apply ObjectProperty.hom_ext
    exact hχ
  · apply ObjectProperty.hom_ext
    exact huniq ξ.hom (congrArg (fun g => g.hom) hξ)

/-- The existence theorem of blowing-up in `𝒥*(𝔄l/B)`, deduced from the construction of p. 127.

> We can easily deduce the existence theorem of blowing-up in the category 𝒥*(𝔄l/B) (resp. 𝒥*(𝔄n/K)) from that in
> 𝓜*(𝔄l/B) (resp. 𝓜*(𝔄n/K)). (See the preceding paragraph where we deduce the existence theorem for 𝒥(ℛ/S) from that
> for 𝓜(ℛ/S).) (p. 128)

Only the algebraic case is treated.  Printed steps, in the printed order: (1) a coherent ideal `I` is an object of
`𝓜*(𝔄l/B)`; (2) it has a blowing-up `(N, Φ)` there, which by assertion (b) (`CoherentClosedUnderBlowingUp`, the input
of "Then, by the assertion (b), we have the existence theorem of blowing-up in the category 𝓜*(𝔄l/B)", p. 124) is also a blowing-up in `𝓜(ℛ)`, hence in
`𝓜(ℛ/B)` (`AnnihilatorConstruction.isBlowingUp_forget`, gap filled); (3) the construction of the preceding paragraph gives
`(N′, Φ′)`, a blowing-up of `I` in `𝒥(ℛ/B)` (`AnnihilatorConstructionIsBlowingUp`, stated by the paper without proof, "it can be
easily seen", assumed as in the paper); (4) `N′` lies in `𝒥*(𝔄l/B)`: assumed, as in the paper.  The paper does not print this step in the deduction; it
states it, without argument, in its next sentence

> We can also see that 𝒥*(𝔄l/B) is closed under blowing-up in 𝒥(ℛ/B) in the sense that a blowing-up of an object of the
> first category in the second category is necessarily a blowing-up of the same object in the first category. (p. 128)

which enters as the hypothesis `CoherentIdealsClosedInIdeals`, applied to `I` and to `(N′, Φ′)` of step (3) to give the
membership `N′ ∈ 𝒥*(𝔄l/B)`; then `Φ′` is a blowing-up in the full subcategory (`isBlowingUp_fullSubcategory`, gap
filled).

The existence in `𝓜*(𝔄l/B)` alone (`ExistenceOfBlowingUpCoherent`) does not suffice for step (2): it gives a blowing-up in
`𝓜*(𝔄l/B)` only, while the construction of p. 127 needs one in `𝓜(ℛ/B)`; the paper's own input for the existence in
`𝓜*(𝔄l/B)` is (b), which also gives the stronger property. -/
theorem existenceOfBlowingUpCoherentIdeals_of_annihilator (hb : CoherentClosedUnderBlowingUp.{u})
    (hann : AnnihilatorConstructionIsBlowingUp.{u}) (hclosed : CoherentIdealsClosedInIdeals.{u}) :
    ExistenceOfBlowingUpCoherentIdeals.{u} := by
  intro B _ hB I
  -- (1) `I` is an object of `𝓜*(𝔄l/B)`.
  let M : (algebraicCoherentModules B).FullSubcategory := ⟨I.obj.asModuleOver, I.property⟩
  -- (2) a blowing-up `(N, Φ)` of `M` in `𝓜*(𝔄l/B)` that is also one in `𝓜(ℛ)` (assertion (b)).
  obtain ⟨N, Φ, -, hΦ'⟩ := (hb B hB).1 M
  have hΦ : IsBlowingUp (RModuleOver.forget (specLRS B)) Φ.hom :=
    AnnihilatorConstruction.isBlowingUp_forget Φ.hom hΦ'
  -- (3) the construction of p. 127.
  have h3 := hann (specLRS B) I.obj N.obj Φ.hom hΦ
  -- (4) membership in `𝒥*(𝔄l/B)`: "We can also see that 𝒥*(𝔄l/B) is closed under blowing-up in 𝒥(ℛ/B) …" (p. 128),
  -- assumed as `hclosed`; then the universal property in the full subcategory.
  obtain ⟨hP, -⟩ := hclosed B hB I (AnnihilatorConstruction.object I.obj N.obj Φ.hom)
    (AnnihilatorConstruction.hom I.obj N.obj Φ.hom) h3
  exact ⟨⟨_, hP⟩, _, isBlowingUp_fullSubcategory _ _ hP _ h3⟩

end Hironaka

end
