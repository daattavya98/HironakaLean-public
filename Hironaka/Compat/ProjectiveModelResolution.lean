/-
Copyright (c) 2026 Daattavya Aggarwal, Minhyong Kim, Oisin Kim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daattavya Aggarwal, Minhyong Kim, Oisin Kim
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import Hironaka.Ch4.MainTheoremIZero
public import Hironaka.Compat.BlowupProjective
public import Hironaka.Compat.BlowupLocalIso
public import Hironaka.Compat.DatumRefinement
public import Hironaka.Compat.MonoidalSuccessionBaseChange
public import Hironaka.Compat.FunctionFieldMap

/-!
# Resolving a projective integral model (for the Corollary of Main Theorem I, p. 132)

> We note that the following existence theorem is an immediate consequence of our main theorem I (or, even, of the same
> theorem in the weak form).  (p. 132)

The "immediate consequence" uses, without proof, that along a succession of monoidal transformations whose centers
avoid the simple points (Main Theorem I in the strong form, p. 132):
* every scheme stays integral (the generic point is simple, hence never on a center; the strict transform of the whole
  scheme is the whole scheme);
* the function field does not change, as a `B`-algebra (each step is an isomorphism off its center, which misses the
  generic point);
* the schemes stay projective (`MonoidalTransformation.isProjectiveOver`, `Compat/BlowupProjective.lean`).
These are proved here (gap filled).
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace Hironaka

universe u

/-! ### The subscheme `⊥ = X` -/

section Bot

variable {X : Scheme.{u}}

/-- The image of an irreducible space by a surjective morphism is irreducible. -/
theorem irreducibleSpace_of_surjective {Y : Scheme.{u}} (f : X ⟶ Y) [IrreducibleSpace X]
    (hf : Function.Surjective f) : IrreducibleSpace Y := by
  rw [irreducibleSpace_def]
  have := (IrreducibleSpace.isIrreducible_univ X).image f f.continuous.continuousOn
  rwa [Set.image_univ, hf.range_eq] at this

/-- The subscheme `⊥` of an irreducible scheme is irreducible. -/
theorem Subscheme.isIrreducible_bot [IrreducibleSpace X] : (⊥ : Subscheme X).IsIrreducible :=
  irreducibleSpace_of_surjective (inv (⊥ : Subscheme X).ι) (Surjective.surj (f := inv (⊥ : Subscheme X).ι))

/-- `X` is irreducible as soon as the subscheme `⊥` is. -/
theorem Subscheme.irreducibleSpace_of_isIrreducible_bot (h : (⊥ : Subscheme X).IsIrreducible) :
    IrreducibleSpace X :=
  have : IrreducibleSpace (⊥ : Subscheme X).toScheme := h
  irreducibleSpace_of_surjective (⊥ : Subscheme X).ι (Surjective.surj (f := (⊥ : Subscheme X).ι))

/-- `X` is reduced as soon as the subscheme `⊥` is. -/
theorem Subscheme.isReduced_of_isReduced_bot (h : (⊥ : Subscheme X).IsReduced) :
    AlgebraicGeometry.IsReduced X :=
  have : AlgebraicGeometry.IsReduced (⊥ : Subscheme X).toScheme := h
  isReduced_of_isOpenImmersion (inv (⊥ : Subscheme X).ι)

/-- The generic point of an integral scheme is a simple point (its local ring is a field). -/
theorem isSimpleAt_genericPoint [IsIntegral X] : X.IsSimpleAt (genericPoint X) :=
  show IsRegularLocalRing X.functionField from inferInstance

end Bot

/-! ### One monoidal transformation whose center misses the generic point -/

namespace MonoidalTransformation

variable {X : Scheme.{u}} {D : Subscheme X}

/-- A monoidal transformation of an integral scheme whose center does not contain the generic point has an integral
total space: the strict transform of the whole scheme is the whole scheme, and it is reduced and irreducible. -/
theorem isIntegral_of_genericPoint_notMem [IsIntegral X] (t : MonoidalTransformation X D)
    (h : genericPoint X ∉ D.pts) : IsIntegral t.X' := by
  have hred := t.isReduced_strictTransform_of_isReduced ⊥ Subscheme.isReduced_bot_of_isReduced
  have hirr := t.strictTransform_isIrreducible ⊥ Subscheme.isIrreducible_bot
    (fun hsub => h (hsub (Subscheme.mem_pts_bot _)))
  rw [t.strictTransform_bot] at hred hirr
  have := Subscheme.isReduced_of_isReduced_bot hred
  have := Subscheme.irreducibleSpace_of_isIrreducible_bot hirr
  exact isIntegral_of_irreducibleSpace_of_isReduced _

/-- Off the center, `f` is surjective onto `X − D`. -/
theorem complOpens_subset_range (t : MonoidalTransformation X D) :
    (complOpens D : Set X) ⊆ Set.range t.f := by
  intro z hz
  have := t.isIso_morphismRestrict_complOpens
  obtain ⟨y, hy⟩ := Surjective.surj (f := t.f ∣_ complOpens D) ⟨z, hz⟩
  refine ⟨(t.f ⁻¹ᵁ complOpens D).ι y, ?_⟩
  have e := congrArg (fun φ => φ y) (morphismRestrict_ι t.f (complOpens D))
  simp only [Scheme.Hom.comp_apply] at e
  rw [← e, hy]
  rfl

/-- If the center misses the generic point, `f` maps the generic point to the generic point. -/
theorem map_genericPoint [IrreducibleSpace X] (t : MonoidalTransformation X D) [IrreducibleSpace t.X']
    (h : genericPoint X ∉ D.pts) : t.f (genericPoint t.X') = genericPoint X := by
  refine map_genericPoint_eq_of_denseRange t.f ?_
  have hd : Dense (complOpens D : Set X) := (complOpens D).isOpen.dense ⟨genericPoint X, h⟩
  exact hd.mono t.complOpens_subset_range

/-- If the center misses the generic point, `f` induces a `B`-isomorphism of function fields. -/
theorem exists_functionField_equiv {B : Type u} [CommRing B] [IrreducibleSpace X]
    (t : MonoidalTransformation X D) [IrreducibleSpace t.X'] (h : genericPoint X ∉ D.pts) (p : X ⟶ Spec (CommRingCat.of B)) :
    ∃ e : t.X'.functionField ≃+* X.functionField,
      ∀ b, e (functionFieldAlgebraMap (t.f ≫ p) b) = functionFieldAlgebraMap p b := by
  have hg := t.map_genericPoint h
  have hbij := bijective_functionFieldMap t.f hg
    (t.bijective_stalkMap_of_notMem_pts _ (by rw [hg]; exact h))
  refine ⟨(RingEquiv.ofBijective _ hbij).symm, fun b => ?_⟩
  rw [RingEquiv.symm_apply_eq, functionFieldAlgebraMap_comp t.f hg p]
  rfl

end MonoidalTransformation

/-! ### Along a strong resolution -/

namespace MonoidalSuccession

/-- The last scheme of a strong resolution is non-singular. -/
theorem isNonsingular_of_isStrongResolution {X Y : Scheme.{u}} (s : MonoidalSuccession X Y)
    (hs : s.IsStrongResolution) : Y.IsNonsingular := by
  induction s with
  | nil X => exact hs
  | cons D t rest ih => exact ih hs.2.2.2

/-- The first center of a strong resolution of an integral scheme misses the generic point. -/
theorem genericPoint_notMem_of_isStrongResolution {X Y : Scheme.{u}} [IsIntegral X] {D : Subscheme X}
    {t : MonoidalTransformation X D} {rest : MonoidalSuccession t.X' Y}
    (hs : (cons D t rest).IsStrongResolution) : genericPoint X ∉ D.pts :=
  fun hη => hs.2.1 _ hη isSimpleAt_genericPoint

/-- Along a strong resolution of an integral scheme, every scheme is integral. -/
theorem isIntegral_of_isStrongResolution {X Y : Scheme.{u}} (s : MonoidalSuccession X Y) [IsIntegral X]
    (hs : s.IsStrongResolution) : IsIntegral Y := by
  revert ‹IsIntegral X›
  induction s with
  | nil X => intro _; assumption
  | cons D t rest ih =>
    intro _
    have := t.isIntegral_of_genericPoint_notMem (genericPoint_notMem_of_isStrongResolution hs)
    exact ih hs.2.2.2

/-- Along a strong resolution of an integral projective `B`-scheme, every scheme is projective (by
`MonoidalTransformation.isProjectiveOver` at each step). -/
theorem isProjectiveOver_of_isStrongResolution {B : Type u} [Field B] {X Y : Scheme.{u}}
    (s : MonoidalSuccession X Y) [IsIntegral X] (hs : s.IsStrongResolution)
    (p : X ⟶ Spec (CommRingCat.of B)) (hp : IsProjectiveOver X p) :
    IsProjectiveOver Y (s.composite ≫ p) := by
  revert ‹IsIntegral X›
  induction s with
  | nil X => intro _; simpa using hp
  | cons D t rest ih =>
    intro _
    have := t.isIntegral_of_genericPoint_notMem (genericPoint_notMem_of_isStrongResolution hs)
    rw [composite_cons, Category.assoc]
    exact ih hs.2.2.2 _ (t.isProjectiveOver p hp)

/-- Along a strong resolution of an integral `B`-scheme, the function field does not change, as a `B`-algebra. -/
theorem exists_functionField_equiv_of_isStrongResolution {B : Type u} [CommRing B] {X Y : Scheme.{u}}
    (s : MonoidalSuccession X Y) [IsIntegral X] [IsIntegral Y] (hs : s.IsStrongResolution)
    (p : X ⟶ Spec (CommRingCat.of B)) :
    ∃ e : Y.functionField ≃+* X.functionField,
      ∀ b, e (functionFieldAlgebraMap (s.composite ≫ p) b) = functionFieldAlgebraMap p b := by
  revert ‹IsIntegral X› ‹IsIntegral Y›
  induction s with
  | nil X => intro _ _; exact ⟨RingEquiv.refl _, fun b => by simp⟩
  | cons D t rest ih =>
    intro _ _
    have hD := genericPoint_notMem_of_isStrongResolution hs
    have := t.isIntegral_of_genericPoint_notMem hD
    obtain ⟨e₁, he₁⟩ := ih hs.2.2.2 (t.f ≫ p)
    obtain ⟨e₂, he₂⟩ := t.exists_functionField_equiv hD p
    refine ⟨e₁.trans e₂, fun b => ?_⟩
    have hc : (cons D t rest).composite ≫ p = rest.composite ≫ t.f ≫ p := by
      rw [composite_cons, Category.assoc]
    rw [hc, RingEquiv.trans_apply, he₁, he₂]

end MonoidalSuccession

end Hironaka
