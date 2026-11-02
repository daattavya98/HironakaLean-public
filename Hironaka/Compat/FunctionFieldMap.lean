/-
Copyright (c) 2026 Daattavya Aggarwal, Minhyong Kim, Oisin Kim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daattavya Aggarwal, Minhyong Kim, Oisin Kim
-/
module

public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.Stalk
public import Hironaka.Ch0.AlgebraicScheme
public import Hironaka.Statements

/-!
# Function fields of `B`-schemes and the maps between them (for the Corollary of Main Theorem I, p. 132)

> If `X` is reduced and irreducible, then the local ring of `X` at the generic point is a field, which is called the
> function field of `X`.  (p. 130)

For the Corollary of p. 132 ("whose function field is `B`-isomorphic to `L`"):
* `functionFieldAlgebraMap p : B →+* X.functionField`, the `B`-algebra structure of the function field of an
  irreducible `B`-scheme `p : X ⟶ Spec B` (`B → Γ(X, O_X) → O_{X,η}`);
* `functionFieldMap f h : Y.functionField ⟶ X.functionField` for a morphism `f : X ⟶ Y` of irreducible schemes sending
  the generic point to the generic point (the stalk map at the generic point), compatible with the `B`-structures
  (`functionFieldAlgebraMap_comp`), and bijective when the stalk map at the generic point is (open immersions,
  monoidal transformations whose center avoids the generic point);
* the function field of `Spec R`, `R` a domain, as a `B`-algebra (`functionFieldAlgebraMap_specMap`).

Nothing here is printed: it is the bookkeeping behind "B-isomorphic" and "function field".
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace Hironaka

universe u

section FunctionFieldAlgebraMap

variable {B : Type u} [CommRing B]


/-- Equal points specialize to each other. -/
theorem specializes_of_eq {X : Type*} [TopologicalSpace X] {x y : X} (h : x = y) : x ⤳ y :=
  h ▸ specializes_rfl

variable {X Y : Scheme.{u}} [IrreducibleSpace X] [IrreducibleSpace Y]

/-- The map of function fields `K(Y) → K(X)` induced by a morphism `f : X ⟶ Y` sending the generic point of `X` to
the generic point of `Y`: the stalk map of `f` at the generic point. -/
noncomputable def functionFieldMap (f : X ⟶ Y) (h : f (genericPoint X) = genericPoint Y) :
    Y.functionField ⟶ X.functionField :=
  Y.presheaf.stalkSpecializes (specializes_of_eq h) ≫ f.stalkMap (genericPoint X)

/-- The map of function fields on germs: `germ_U ≫ f^♯ = f.app U ≫ germ_{f⁻¹U}`. -/
theorem germ_functionFieldMap (f : X ⟶ Y) (h : f (genericPoint X) = genericPoint Y) (U : Y.Opens)
    (hU : genericPoint Y ∈ U) :
    Y.presheaf.germ U (genericPoint Y) hU ≫ functionFieldMap f h =
      f.app U ≫ X.presheaf.germ (f ⁻¹ᵁ U) (genericPoint X) (show f (genericPoint X) ∈ U from h ▸ hU) := by
  rw [functionFieldMap, TopCat.Presheaf.germ_stalkSpecializes_assoc, Scheme.Hom.germ_stalkMap]

/-- The map of function fields is compatible with the `B`-structures. -/
theorem functionFieldAlgebraMap_comp (f : X ⟶ Y) (h : f (genericPoint X) = genericPoint Y)
    (p : Y ⟶ Spec (CommRingCat.of B)) :
    functionFieldAlgebraMap (f ≫ p) = (functionFieldMap f h).hom.comp (functionFieldAlgebraMap p) := by
  ext b
  have hU : genericPoint Y ∈ (⊤ : Y.Opens) := trivial
  have e := congrArg (fun φ => φ.hom (p.appTop ((Scheme.ΓSpecIso (CommRingCat.of B)).inv b)))
    (germ_functionFieldMap f h ⊤ hU)
  simp only [CommRingCat.comp_apply] at e
  simp only [functionFieldAlgebraMap, RingHom.comp_apply, Scheme.germToFunctionField, e]
  rfl

omit [IrreducibleSpace X] [IrreducibleSpace Y] in
/-- The specialization map between the stalks at equal points is bijective. -/
theorem bijective_stalkSpecializes_of_eq {x y : Y} (h : x = y) :
    Function.Bijective (Y.presheaf.stalkSpecializes (specializes_of_eq h)) := by
  subst h
  rw [show specializes_of_eq (rfl : x = x) = specializes_refl x from rfl,
    TopCat.Presheaf.stalkSpecializes_refl]
  exact Function.bijective_id

/-- The map of function fields is bijective when the stalk map at the generic point is. -/
theorem bijective_functionFieldMap (f : X ⟶ Y) (h : f (genericPoint X) = genericPoint Y)
    (hf : Function.Bijective (f.stalkMap (genericPoint X))) :
    Function.Bijective (functionFieldMap f h) :=
  hf.comp (bijective_stalkSpecializes_of_eq h)

/-- An open immersion of irreducible schemes induces an isomorphism of function fields. -/
theorem bijective_functionFieldMap_of_isOpenImmersion (f : X ⟶ Y) [IsOpenImmersion f] :
    Function.Bijective (functionFieldMap f (genericPoint_eq_of_isOpenImmersion f)) :=
  bijective_functionFieldMap f _ (ConcreteCategory.bijective_of_isIso (f.stalkMap (genericPoint X)))

/-- A morphism of irreducible schemes whose image is dense sends the generic point to the generic point. -/
theorem map_genericPoint_eq_of_denseRange (f : X ⟶ Y) (hf : DenseRange f) :
    f (genericPoint X) = genericPoint Y := by
  refine ((genericPoint_spec Y).eq ?_).symm
  rw [isGenericPoint_def]
  refine Set.eq_univ_of_univ_subset ?_
  have h1 : Set.range f ⊆ closure {f (genericPoint X)} := by
    rintro _ ⟨y, rfl⟩
    have : genericPoint X ⤳ y := (genericPoint_spec X).specializes trivial
    exact specializes_iff_mem_closure.mp (this.map f.continuous)
  have := closure_mono h1
  rw [closure_closure, hf.closure_range] at this
  exact this

end FunctionFieldAlgebraMap

section Spec

variable {B : Type u} [CommRing B] (R : CommRingCat.{u}) [IsDomain R]

/-- The function field of `Spec R`, `R` a domain, as a `B`-algebra for `Spec R → Spec B` given by `g : B → R`:
`b ↦ g(b)/1`. -/
theorem functionFieldAlgebraMap_specMap (g : B →+* R) :
    functionFieldAlgebraMap (Spec.map (CommRingCat.ofHom g)) =
      (algebraMap R (Spec R).functionField).comp g := by
  ext b
  have e := congrArg (fun φ => φ.hom b) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom g))
  simp only at e
  simp only [functionFieldAlgebraMap, RingHom.comp_apply, Scheme.Hom.appTop]
  erw [← e]
  rfl

/-- If `ψ : R → L` makes the field `L` a fraction field of the domain `R` and `ψ ∘ g` is the algebra map of `L`, then
the function field of `Spec R` (a `B`-scheme via `g : B → R`) is `B`-isomorphic to `L`. -/
theorem exists_functionField_spec_equiv {L : Type u} [Field L] [Algebra B L] (g : B →+* R) (ψ : R →+* L)
    (hinj : Function.Injective ψ) (hsurj : ∀ z : L, ∃ a b, z = ψ a / ψ b)
    (hg : ∀ b, ψ (g b) = algebraMap B L b) :
    ∃ e : (Spec R).functionField ≃+* L,
      ∀ b, e (functionFieldAlgebraMap (Spec.map (CommRingCat.ofHom g)) b) = algebraMap B L b := by
  let _ : Algebra R L := ψ.toAlgebra
  have : FaithfulSMul R L := (faithfulSMul_iff_algebraMap_injective R L).mpr hinj
  have : IsFractionRing R L := IsFractionRing.of_field R L hsurj
  let e := IsLocalization.algEquiv (nonZeroDivisors R) (Spec R).functionField L
  refine ⟨e.toRingEquiv, fun b => ?_⟩
  rw [functionFieldAlgebraMap_specMap, RingHom.comp_apply]
  exact (e.commutes (g b)).trans (hg b)

/-- The function field of an irreducible `B`-scheme `X` with an open immersion `Spec R → X` over `B` (`R` a domain with
fraction field `L`, compatibly with `B`) is `B`-isomorphic to `L`. -/
theorem exists_functionField_equiv_of_isOpenImmersion {L : Type u} [Field L] [Algebra B L]
    {X : Scheme.{u}} [IrreducibleSpace X] (p : X ⟶ Spec (CommRingCat.of B)) (ι : Spec R ⟶ X)
    [IsOpenImmersion ι] (g : B →+* R) (hι : ι ≫ p = Spec.map (CommRingCat.ofHom g)) (ψ : R →+* L)
    (hinj : Function.Injective ψ) (hsurj : ∀ z : L, ∃ a b, z = ψ a / ψ b)
    (hg : ∀ b, ψ (g b) = algebraMap B L b) :
    ∃ e : X.functionField ≃+* L, ∀ b, e (functionFieldAlgebraMap p b) = algebraMap B L b := by
  obtain ⟨e, he⟩ := exists_functionField_spec_equiv R g ψ hinj hsurj hg
  have h := genericPoint_eq_of_isOpenImmersion ι
  let e₁ := RingEquiv.ofBijective (functionFieldMap ι h).hom
    (bijective_functionFieldMap_of_isOpenImmersion ι)
  refine ⟨e₁.trans e, fun b => ?_⟩
  have h1 := congrArg (fun φ => φ b) (functionFieldAlgebraMap_comp ι h p)
  simp only [RingHom.comp_apply] at h1
  rw [hι] at h1
  simp only [RingEquiv.trans_apply, RingEquiv.ofBijective_apply, e₁]
  rw [← h1, he]

end Spec

end Hironaka
