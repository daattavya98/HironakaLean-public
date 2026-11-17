/-
Copyright (c) 2026 Daattavya Aggarwal, Minhyong Kim, Oisin Kim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daattavya Aggarwal, Minhyong Kim, Oisin Kim
-/
module

public import Hironaka.Ch0.BlowingUpModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree

/-!
# Invertible `ℛ`-modules are locally free of rank one, hence quasi-coherent and coherent

Infrastructure used in the derivation of assertions (a) and (b) of p. 124 of the paper; proves no claim of the
paper.

The project's `RModule.IsInvertible` (Ch. 0 §2, p. 123) is the sections-level encoding of "`O_X | U ≅ J | U` near every
point": a section `s` of `J` over `U` with `a ↦ a • s|_V` bijective `O_X(V) → J(V)` for all open `V ⊆ U`.  Here this is
turned into Mathlib's `SheafOfModules.IsLocallyFree` (the generating section `s` of `J.over U` gives an isomorphism
`free PUnit ⟶ J.over U`), from which quasi-coherence follows by Mathlib, and coherence (finite presentation) because the
presentations obtained have no relations and one generator.  Also: a coherent (finitely presented) `ℛ`-module is
quasi-coherent.
-/

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite

noncomputable section

namespace Hironaka.RModule

universe u

variable {M : RModule.{u}}

/-- The section of `J.over U` induced by a section `s` of `J` over `U`: over `V ⟶ U` it is `s|_V`. -/
def overSection (U : Opens M.X) (s : M.J.val.obj (op U)) : (M.J.over U).sections :=
  PresheafOfModules.sectionsMk (fun V => M.J.val.map V.unop.hom.op s)
    (fun V W f => by
      change M.J.val.map f.unop.left.op (M.J.val.map V.unop.hom.op s) = _
      rw [← PresheafOfModules.map_comp_apply]
      rfl)

/-- The morphism `O_X | U ⟶ J | U`, `1 ↦ s`, is an isomorphism when `a ↦ a • s|_V` is bijective for all open
`V ⊆ U`. -/
theorem isIso_unitHomEquiv_symm_overSection (U : Opens M.X) (s : M.J.val.obj (op U))
    (hs : ∀ (V : Opens M.X) (hV : V ≤ U),
      Function.Bijective (fun a : (ringCatSheaf M.X).obj.obj (op V) =>
        a • ((M.J.val.map (homOfLE hV).op).hom s))) :
    IsIso ((M.J.over U).unitHomEquiv.symm (overSection U s)) := by
  set f := (M.J.over U).unitHomEquiv.symm (overSection U s) with hf
  rw [← isIso_iff_of_reflects_iso f (SheafOfModules.forget _)]
  have key : ∀ V, IsIso (f.val.app V) := fun V => by
    rw [ConcreteCategory.isIso_iff_bijective]
    have h : ⇑(ConcreteCategory.hom (f.val.app V)) =
        fun a : (ringCatSheaf M.X).obj.obj (op V.unop.left) =>
          a • ((M.J.val.map (homOfLE (leOfHom V.unop.hom)).op).hom s) := by
      funext a
      rfl
    rw [h]
    exact hs _ _
  let e := PresheafOfModules.isoMk (fun V => asIso (f.val.app V)) (fun V W g => f.val.naturality g)
  exact inferInstanceAs (IsIso e.hom)

/-- The inclusion `unit R ⟶ free PUnit` of the unique summand is an isomorphism. -/
instance isIso_ιFree_punit {C : Type*} [Category C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}
    [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}] :
    IsIso (SheafOfModules.ιFree (R := R) (I := PUnit.{u + 1}) PUnit.unit) := by
  let d : SheafOfModules.free (R := R) PUnit.{u + 1} ⟶ SheafOfModules.unit R :=
    Cofan.IsColimit.desc (SheafOfModules.isColimitFreeCofan (R := R) PUnit.{u + 1}) (fun _ => 𝟙 _)
  have h1 : SheafOfModules.ιFree (R := R) (I := PUnit.{u + 1}) PUnit.unit ≫ d = 𝟙 _ :=
    Cofan.IsColimit.fac (SheafOfModules.isColimitFreeCofan (R := R) PUnit.{u + 1})
      (fun _ => 𝟙 (SheafOfModules.unit R)) PUnit.unit
  refine ⟨d, h1, ?_⟩
  refine Cofan.IsColimit.hom_ext (SheafOfModules.isColimitFreeCofan (R := R) PUnit.{u + 1}) _ _ ?_
  intro i
  cases i
  change SheafOfModules.ιFree PUnit.unit ≫ d ≫ SheafOfModules.ιFree PUnit.unit =
    SheafOfModules.ιFree PUnit.unit ≫ 𝟙 _
  rw [← Category.assoc]
  change (SheafOfModules.ιFree PUnit.unit ≫ d) ≫ _ = _
  rw [h1, Category.id_comp, Category.comp_id]

/-- Over `U`, the generating section `s` gives an isomorphism `free PUnit ⟶ J.over U`. -/
theorem isIso_freeHomEquiv_symm_overSection (U : Opens M.X) (s : M.J.val.obj (op U))
    (hs : ∀ (V : Opens M.X) (hV : V ≤ U),
      Function.Bijective (fun a : (ringCatSheaf M.X).obj.obj (op V) =>
        a • ((M.J.val.map (homOfLE hV).op).hom s))) :
    IsIso ((M.J.over U).freeHomEquiv.symm (fun _ : PUnit.{u + 1} => overSection U s)) := by
  have h1 := isIso_unitHomEquiv_symm_overSection U s hs
  have h2 : SheafOfModules.ιFree (R := (ringCatSheaf M.X).over U) (I := PUnit.{u + 1}) PUnit.unit ≫
      (M.J.over U).freeHomEquiv.symm (fun _ : PUnit.{u + 1} => overSection U s) =
      (M.J.over U).unitHomEquiv.symm (overSection U s) := by
    rw [← SheafOfModules.unitHomEquiv_symm_freeHomEquiv_apply, Equiv.apply_symm_apply]
  rw [← h2] at h1
  exact IsIso.of_isIso_comp_left (SheafOfModules.ιFree (R := (ringCatSheaf M.X).over U)
    (I := PUnit.{u + 1}) PUnit.unit) _

/-- Local generators of an invertible `ℛ`-module: around each point `x`, the single section `s` of the definition of
`IsInvertibleAt`, generating `J | U`. -/
def localGeneratorsDataOfIsInvertible (h : M.IsInvertible) : M.J.LocalGeneratorsData :=
  let U := fun x => (h x).choose
  have hxU : ∀ x, x ∈ U x := fun x => (h x).choose_spec.choose
  let s := fun x => (h x).choose_spec.choose_spec.choose
  have hs := fun x => (h x).choose_spec.choose_spec.choose_spec
  { I := M.X
    X := U
    coversTop := (Opens.coversTop_iff M.X U).2 (IsOpenCover.mk (by
      rw [eq_top_iff]
      intro x _
      exact Opens.mem_iSup.2 ⟨x, hxU x⟩))
    generators := fun x =>
      { I := PUnit.{u + 1}
        s := fun _ => overSection (U x) (s x)
        epi := by
          have := isIso_freeHomEquiv_symm_overSection (U x) (s x) (hs x)
          infer_instance } }

/-- The local generators of an invertible module are locally free data (`free PUnit ≅ J | U`). -/
instance (h : M.IsInvertible) : (localGeneratorsDataOfIsInvertible h).IsLocallyFreeData :=
  SheafOfModules.LocalGeneratorsData.IsLocallyFreeData.mk (q := localGeneratorsDataOfIsInvertible h)
    (fun x => isIso_freeHomEquiv_symm_overSection _ _ (h x).choose_spec.choose_spec.choose_spec)

/-- An invertible `ℛ`-module is locally free (of rank one): near each point `x`, the section `s` of the definition
of `IsInvertibleAt` generates `J | U` freely.

Gap filled (p. 123 / p. 124): the paper does not print that an invertible module is quasi-coherent; this is
the first half of the proof. -/
theorem isLocallyFree_of_isInvertible {M : RModule.{u}} (h : M.IsInvertible) :
    SheafOfModules.IsLocallyFree (R := ringCatSheaf M.X) M.J :=
  (localGeneratorsDataOfIsInvertible h).isLocallyFree

/-- An invertible `ℛ`-module is quasi-coherent (locally free sheaves of modules are quasi-coherent).

Gap filled (p. 124): the derivation of assertions (a) and (b) does not print that an invertible module is
quasi-coherent. -/
theorem isQuasicoherent_of_isInvertible {M : RModule.{u}} (h : M.IsInvertible) : M.IsQuasicoherent :=
  (localGeneratorsDataOfIsInvertible h).quasiCoherentData.isQuasicoherent

/-- An invertible `ℛ`-module is coherent in the sense of the project (finitely presented): the presentations coming
from local freeness have one generator and no relation. -/
theorem isCoherent_of_isInvertible {M : RModule.{u}} (h : M.IsInvertible) : M.IsCoherent := by
  have hfp : (localGeneratorsDataOfIsInvertible h).quasiCoherentData.IsFinitePresentation := by
    constructor
    intro i
    constructor
    · constructor
      exact inferInstanceAs (Finite PUnit.{u + 1})
    · constructor
      exact inferInstanceAs (Finite (ULift.{u} Empty))
  constructor
  exact ⟨(localGeneratorsDataOfIsInvertible h).quasiCoherentData, hfp⟩

set_option backward.isDefEq.respectTransparency false in
/-- A coherent (finitely presented) `ℛ`-module is quasi-coherent. -/
theorem isQuasicoherent_of_isCoherent {M : RModule.{u}} (h : M.IsCoherent) : M.IsQuasicoherent := by
  have h' : SheafOfModules.IsFinitePresentation.{u, u, u} (R := ringCatSheaf M.X) M.J := h
  exact (inferInstance : SheafOfModules.IsQuasicoherent.{u, u, u} (R := ringCatSheaf M.X) M.J)

end Hironaka.RModule
