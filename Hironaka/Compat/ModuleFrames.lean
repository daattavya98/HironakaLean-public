/-
Copyright (c) 2026 Daattavya Aggarwal, Minhyong Kim, Oisin Kim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daattavya Aggarwal, Minhyong Kim, Oisin Kim
-/
module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
public import Mathlib.LinearAlgebra.InvariantBasisNumber
public import Hironaka.Statements

/-!
# Frames of sheaves of modules (Compat API for Corollary 2 of Main Theorem II)

Hironaka, Ch. 0, Corollary 2 of Main Theorem II (p. 145) works with free bases
`(c_1, ..., c_r)` of a locally free coherent sheaf `F` near a point.  Mathlib encodes local
freeness abstractly (`SheafOfModules.IsLocallyFree`: charts `free I ≅ M.over U`) and has no
description of the sections of a finite free sheaf.  This module supplies the missing
section-level API:

* `Hironaka.SheafOfModules.coordMap`, `bijective_coordMap_free`: the sections of `free I`
  (`I` finite) over any object are uniquely the combinations `∑ aᵢ • eᵢ`;
* `Hironaka.SheafOfModules.isIso_freeHomEquiv_symm_iff`: a morphism out of a finite free
  sheaf is an isomorphism iff its coordinate maps are bijective;
* `Hironaka.SheafOfModules.card_le_of_epi`, `finite_of_epi`: an epimorphism `free κ ⟶ free ι`
  (`κ` finite) over a site with a terminal object `T` forces `card ι ≤ card κ` (so `ι` is
  finite) as soon as `R(T)ᵐᵒᵖ` has the strong rank condition (e.g. `R(T)` commutative and
  nonzero); proof: `Hom(-, unit R)` turns the epimorphism into an injective linear map;
* `Hironaka.Scheme.Modules.IsFrame`: a *frame* of an `𝒪_X`-module `M` over an open `U` (a
  finite family of sections over `U` restricting to a basis over every smaller open);
* the translations between frames and Mathlib's charts (`isFrame_of_isIso`,
  `frameGeneratingSections`, `isIso_frameGeneratingSections_π`) and the restrictions
  `M.restrict U.ι` (`isFrame_iff_isIso_restrict`);
* `isFrame_iff_bijective_frameHomMap`: the Yoneda form of the frame condition, through the
  adjunction `restrictFunctor U.ι ⊣ pushforward U.ι`; it is the tool for pulling frames back
  (`Hironaka/Compat/PullbackFrames.lean`).

This is infrastructure (no statement of the paper); it is not a deviation.
-/

@[expose] public section

open CategoryTheory Limits Opposite

universe v₁ u₁ u

namespace Hironaka

namespace SheafOfModules

open _root_.SheafOfModules

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}
  [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]

omit [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- Applying a morphism out of `unit R` to a section `a • 1`. -/
theorem unitHom_app_apply {M : SheafOfModules.{u} R} (f : unit R ⟶ M) (X : Cᵒᵖ)
    (a : R.obj.obj X) :
    f.val.app X a = a • PresheafOfModules.sections.eval (M.unitHomEquiv f) X := by
  have h : (a : (unit R).val.obj X) =
      a • (show (unit R).val.obj X from (1 : R.obj.obj X)) := by
    change a = a * 1
    simp
  calc (f.val.app X).hom (a : (unit R).val.obj X)
      = (f.val.app X).hom (a • (show (unit R).val.obj X from (1 : R.obj.obj X))) :=
        congrArg _ h
    _ = a • (f.val.app X).hom (show (unit R).val.obj X from (1 : R.obj.obj X)) := map_smul _ _ _
    _ = _ := rfl

/-- The combination `∑ aᵢ • sᵢ` of finitely many sections at the object `X`. -/
noncomputable def coordMap (M : SheafOfModules.{u} R) {I : Type u} [Fintype I]
    (s : I → M.sections) (X : Cᵒᵖ) (a : I → R.obj.obj X) : M.val.obj X :=
  ∑ i, a i • PresheafOfModules.sections.eval (s i) X

/-- The element `1` of `(unit R)(X) = R(X)`. -/
abbrev unitOne (R : Sheaf J RingCat.{u}) (X : Cᵒᵖ) : (unit R).val.obj X := (1 : R.obj.obj X)

/-- The tautological section `eᵢ` of `free I` at `X` is the image of `1` under `ιFree i`. -/
theorem freeSection_eval {I : Type u} (i : I) (X : Cᵒᵖ) :
    PresheafOfModules.sections.eval (freeSection (R := R) i) X =
      (ιFree i).val.app X (unitOne R X) :=
  rfl

/-- The projection `free I ⟶ unit R` onto the `i`-th coordinate. -/
noncomputable def freeProj {I : Type u} [DecidableEq I] (i : I) : free (R := R) I ⟶ unit R :=
  Cofan.IsColimit.desc (isColimitFreeCofan I) (fun j => if j = i then 𝟙 _ else 0)

/-- `ιFree j ≫ freeProj i` is `𝟙` if `j = i` and `0` otherwise. -/
theorem ιFree_comp_freeProj {I : Type u} [DecidableEq I] (j i : I) :
    ιFree (R := R) j ≫ freeProj i = if j = i then 𝟙 _ else 0 :=
  Cofan.IsColimit.fac (isColimitFreeCofan I) _ j

/-- The `i`-th coordinate of the tautological section `eⱼ` is `δⱼᵢ`. -/
theorem freeProj_app_freeSection {I : Type u} [DecidableEq I] (i j : I) (X : Cᵒᵖ) :
    (freeProj (R := R) i).val.app X (PresheafOfModules.sections.eval (freeSection j) X) =
      if j = i then unitOne R X else 0 := by
  rw [freeSection_eval]
  have h := congrArg (fun φ : unit R ⟶ unit R => φ.val.app X (unitOne R X))
    (ιFree_comp_freeProj (R := R) j i)
  dsimp only at h
  split_ifs at h ⊢ with hji
  · exact h
  · exact h

/-- The `i`-th coordinate of `∑ aⱼ • eⱼ` is `aᵢ`. -/
theorem freeProj_app_coordMap {I : Type u} [Fintype I] [DecidableEq I] (i : I) (X : Cᵒᵖ)
    (a : I → R.obj.obj X) :
    (freeProj (R := R) i).val.app X (coordMap (free I) freeSection X a) =
      (a i : (unit R).val.obj X) := by
  unfold coordMap
  rw [map_sum]
  simp_rw [map_smul, freeProj_app_freeSection]
  simp only [smul_ite, smul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  change a i * 1 = a i
  simp

/-- The coordinate projections and inclusions of a finite free sheaf add up to the identity. -/
theorem sum_freeProj_comp_ιFree {I : Type u} [Fintype I] [DecidableEq I] :
    ∑ i, freeProj (R := R) i ≫ ιFree i = 𝟙 (free I) := by
  refine Cofan.IsColimit.hom_ext (isColimitFreeCofan I) _ _ fun j => ?_
  change ιFree j ≫ ∑ i, freeProj (R := R) i ≫ ιFree i = ιFree j ≫ 𝟙 (free I)
  rw [Preadditive.comp_sum, Category.comp_id]
  rw [Finset.sum_eq_single j]
  · rw [← Category.assoc, ιFree_comp_freeProj]
    simp
  · intro b _ hb
    rw [← Category.assoc, ιFree_comp_freeProj]
    simp [Ne.symm hb]
  · simp

/-- `ιFree i` sends `c` to `c • eᵢ`. -/
theorem ιFree_app_apply {I : Type u} (i : I) (X : Cᵒᵖ) (c : R.obj.obj X) :
    (ιFree (R := R) i).val.app X c = c • PresheafOfModules.sections.eval (freeSection i) X := by
  have := unitHom_app_apply (ιFree (R := R) i) X c
  rw [this]
  rfl

omit [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- Evaluation of sheaves of modules at an object is additive. -/
instance (X : Cᵒᵖ) : (evaluation R X).Additive :=
  inferInstanceAs ((forget R ⋙ PresheafOfModules.evaluation _ X).Additive)

omit [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- A finite sum of morphisms of sheaves of modules acts on sections as the sum of the actions. -/
theorem hom_sum_app {M N : SheafOfModules.{u} R} {ι : Type*} (t : Finset ι) (f : ι → (M ⟶ N))
    (X : Cᵒᵖ) (m : M.val.obj X) :
    (∑ i ∈ t, f i).val.app X m = ∑ i ∈ t, (f i).val.app X m := by
  have h := (evaluation R X).map_sum f t
  change (∑ i ∈ t, f i).val.app X = ∑ i ∈ t, (f i).val.app X at h
  rw [h]
  have h2 := ModuleCat.hom_sum (fun i => (f i).val.app X) t
  have h3 := congrArg (fun φ => φ m) h2
  simp only [LinearMap.sum_apply] at h3
  exact h3

/-- **Sections of a finite free sheaf**: for finite `I` the sections of `free I` over `X` are
uniquely the combinations `∑ aᵢ • eᵢ` of the tautological sections. -/
theorem bijective_coordMap_free {I : Type u} [Fintype I] (X : Cᵒᵖ) :
    Function.Bijective (coordMap (free (R := R) I) freeSection X) := by
  classical
  constructor
  · intro a b hab
    funext i
    have := congrArg ((freeProj (R := R) i).val.app X) hab
    rw [freeProj_app_coordMap, freeProj_app_coordMap] at this
    exact this
  · intro m
    refine ⟨fun i => (freeProj (R := R) i).val.app X m, ?_⟩
    have h := congrArg (fun φ : free (R := R) I ⟶ free I => φ.val.app X m)
      (sum_freeProj_comp_ιFree (R := R) (I := I))
    dsimp only at h
    rw [hom_sum_app] at h
    unfold coordMap
    calc ∑ i, (show R.obj.obj X from (freeProj (R := R) i).val.app X m) •
          PresheafOfModules.sections.eval (freeSection i) X
        = ∑ i, (freeProj (R := R) i ≫ ιFree i).val.app X m :=
          Finset.sum_congr rfl fun i _ => (ιFree_app_apply i X _).symm
      _ = m := h

/-- The morphism `free I ⟶ M` attached to sections `s` sends `∑ aᵢ • eᵢ` to `∑ aᵢ • sᵢ`. -/
theorem freeHomEquiv_symm_app_coordMap {M : SheafOfModules.{u} R} {I : Type u} [Fintype I]
    (s : I → M.sections) (X : Cᵒᵖ) (a : I → R.obj.obj X) :
    (M.freeHomEquiv.symm s).val.app X (coordMap (free I) freeSection X a) = coordMap M s X a := by
  unfold coordMap
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul]
  congr 1
  have := freeHomEquiv_apply (M := M) (M.freeHomEquiv.symm s) i
  rw [Equiv.apply_symm_apply] at this
  rw [this]
  rfl

/-- A morphism out of a finite free sheaf is an isomorphism iff its coordinate maps are
bijective at every object. -/
theorem isIso_freeHomEquiv_symm_iff {M : SheafOfModules.{u} R} {I : Type u} [Fintype I]
    (s : I → M.sections) :
    IsIso (M.freeHomEquiv.symm s) ↔ ∀ X, Function.Bijective (coordMap M s X) := by
  have key : ∀ X, Function.Bijective ((M.freeHomEquiv.symm s).val.app X) ↔
      Function.Bijective (coordMap M s X) := by
    intro X
    have h := (bijective_coordMap_free (R := R) (I := I) X)
    have h2 : coordMap M s X =
        (M.freeHomEquiv.symm s).val.app X ∘ coordMap (free I) freeSection X := by
      funext a
      exact (freeHomEquiv_symm_app_coordMap s X a).symm
    rw [h2]
    exact (Function.Bijective.of_comp_iff _ h).symm
  have : ∀ φ : free (R := R) I ⟶ M, IsIso φ ↔ ∀ X, IsIso (φ.val.app X) := by
    intro φ
    rw [← isIso_iff_of_reflects_iso φ (forget R),
      ← isIso_iff_of_reflects_iso _ (PresheafOfModules.toPresheaf R.obj),
      NatTrans.isIso_iff_isIso_app]
    exact forall_congr' fun X => isIso_iff_of_reflects_iso (φ.val.app X)
      (forget₂ (ModuleCat (R.obj.obj X)) AddCommGrpCat)
  rw [this]
  have hb : ∀ X, IsIso ((M.freeHomEquiv.symm s).val.app X) ↔
      Function.Bijective ((M.freeHomEquiv.symm s).val.app X) := fun X =>
    ConcreteCategory.isIso_iff_bijective _
  simp_rw [hb, key]

/-- The global section of `unit R` determined by an element over a terminal object. -/
noncomputable def unitSectionOfTerminal {T : C} (hT : IsTerminal T) (a : R.obj.obj (op T)) :
    (unit R).sections :=
  PresheafOfModules.sectionsMk (fun X => (show (unit R).val.obj X from
      R.obj.map (hT.from X.unop).op a)) (by
    intro X Y g
    show R.obj.map g (R.obj.map (hT.from X.unop).op a) = R.obj.map (hT.from Y.unop).op a
    rw [← ConcreteCategory.comp_apply, ← R.obj.map_comp,
      show (hT.from X.unop).op ≫ g = (hT.from Y.unop).op from
        Quiver.Hom.unop_inj (hT.hom_ext _ _)])

omit [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- The section `unitSectionOfTerminal hT a` has value `a` at the terminal object. -/
theorem unitSectionOfTerminal_eval {T : C} (hT : IsTerminal T) (a : R.obj.obj (op T)) :
    PresheafOfModules.sections.eval (unitSectionOfTerminal hT a) (op T) = a := by
  show R.obj.map (hT.from T).op a = a
  rw [show hT.from T = 𝟙 T from hT.hom_ext _ _, op_id, R.obj.map_id]
  rfl

omit [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- Global sections agreeing at a terminal object are equal. -/
theorem sections_ext_of_terminal {M : SheafOfModules.{u} R} {T : C} (hT : IsTerminal T)
    {s t : M.sections}
    (h : PresheafOfModules.sections.eval s (op T) = PresheafOfModules.sections.eval t (op T)) :
    s = t := by
  refine PresheafOfModules.sections_ext _ _ fun X => ?_
  exact (PresheafOfModules.sections_property s (hT.from X.unop).op).symm.trans
    ((congrArg (M.val.map (hT.from X.unop).op) h).trans
      (PresheafOfModules.sections_property t _))

/-- **Rank inequality.** On a site with a terminal object `T` whose ring of sections is
(opposite-)strong-rank, an epimorphism `free κ ⟶ free ι` of finite free sheaves forces
`card ι ≤ card κ`. -/
theorem card_le_of_epi {T : C} (hT : IsTerminal T) [StrongRankCondition (R.obj.obj (op T))ᵐᵒᵖ]
    {κ ι : Type u} [Fintype κ] [Fintype ι] (p : free (R := R) κ ⟶ free ι) [Epi p] :
    Fintype.card ι ≤ Fintype.card κ := by
  classical
  let A := R.obj.obj (op T)
  -- coordinates of the images of the basis vectors
  have hQ := fun j : κ => (bijective_coordMap_free (R := R) (I := ι) (op T)).2
    (PresheafOfModules.sections.eval (sectionsMap p (freeSection j)) (op T))
  choose Q hQ using hQ
  let φ : (ι → A) → (free (R := R) ι ⟶ unit R) := fun a =>
    (unit R).freeHomEquiv.symm fun k => unitSectionOfTerminal hT (a k)
  have hφ : ∀ (a : ι → A) (j : κ),
      PresheafOfModules.sections.eval ((unit R).freeHomEquiv (p ≫ φ a) j) (op T) =
        ∑ k, Q j k * a k := by
    intro a j
    rw [freeHomEquiv_comp_apply]
    show (φ a).val.app (op T) (PresheafOfModules.sections.eval (sectionsMap p (freeSection j))
      (op T)) = _
    rw [← hQ j, freeHomEquiv_symm_app_coordMap]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [unitSectionOfTerminal_eval]
    rfl
  let L : (ι → Aᵐᵒᵖ) →ₗ[Aᵐᵒᵖ] (κ → Aᵐᵒᵖ) :=
    { toFun := fun b j => ∑ k, b k * MulOpposite.op (Q j k)
      map_add' := fun b b' => by
        funext j
        simp [add_mul, Finset.sum_add_distrib]
      map_smul' := fun c b => by
        funext j
        simp [Finset.mul_sum, mul_assoc] }
  refine card_le_of_injective Aᵐᵒᵖ L fun b b' hbb' => ?_
  have hL : ∀ b : ι → Aᵐᵒᵖ, ∀ j, MulOpposite.unop (L b j) = ∑ k, Q j k * (b k).unop := by
    intro b j
    simp [L]
  have h1 : p ≫ φ (fun k => (b k).unop) = p ≫ φ (fun k => (b' k).unop) := by
    refine (unit R).freeHomEquiv.injective (funext fun j => sections_ext_of_terminal hT ?_)
    rw [hφ, hφ, ← hL, ← hL, hbb']
  funext k
  have h2 := congrArg (fun ψ => PresheafOfModules.sections.eval
    ((unit R).freeHomEquiv ψ k) (op T)) ((cancel_epi p).mp h1)
  simp only [φ, Equiv.apply_symm_apply, unitSectionOfTerminal_eval] at h2
  exact MulOpposite.unop_injective h2


/-- If a finite free sheaf maps epimorphically onto `free I` (over a site with a terminal object
whose ring of sections is opposite-strong-rank), then `I` is finite. -/
theorem finite_of_epi {T : C} (hT : IsTerminal T) [StrongRankCondition (R.obj.obj (op T))ᵐᵒᵖ]
    {κ I : Type u} [Finite κ] (p : free (R := R) κ ⟶ free I) [Epi p] : Finite I := by
  classical
  have := Fintype.ofFinite κ
  by_contra hI
  rw [not_finite_iff_infinite] at hI
  obtain ⟨s, hs⟩ := Infinite.exists_subset_card_eq I (Fintype.card κ + 1)
  let r : free (R := R) I ⟶ free s := Cofan.IsColimit.desc (isColimitFreeCofan I)
    fun i => if h : i ∈ s then ιFree (⟨i, h⟩ : s) else 0
  have hr : freeMap (R := R) (Subtype.val : s → I) ≫ r = 𝟙 _ := by
    refine Cofan.IsColimit.hom_ext (isColimitFreeCofan s) _ _ fun k => ?_
    change ιFree k ≫ freeMap (R := R) (Subtype.val : s → I) ≫ r = ιFree k ≫ 𝟙 _
    rw [ιFree_freeMap_assoc, Category.comp_id]
    have := Cofan.IsColimit.fac (isColimitFreeCofan (R := R) I)
      (fun i => if h : i ∈ s then ιFree (⟨i, h⟩ : s) else 0) k.1
    simp only [k.2, ↓reduceDIte] at this
    exact this
  have : IsSplitEpi r := IsSplitEpi.mk' (⟨freeMap (R := R) Subtype.val, hr⟩ : SplitEpi r)
  have := card_le_of_epi hT (p ≫ r)
  simp [hs] at this

end SheafOfModules

open AlgebraicGeometry

namespace Scheme.Modules

open AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}


/-- Frames from a finite free chart: if `π : free I ⟶ M.over U` is an isomorphism, the images of
the tautological sections form a frame over `U`. -/
theorem isFrame_of_isIso {M : X.Modules} {U : X.Opens} (σ : (M.over U).GeneratingSections)
    [Fintype σ.I] [IsIso σ.π] :
    ∃ c : σ.I → Γ(M, U), IsFrame M U c := by
  classical
  refine ⟨fun i => PresheafOfModules.sections.eval (σ.s i) (op (Over.mk (𝟙 U))), ⟨fun V h => ?_⟩⟩
  have hb := (SheafOfModules.isIso_freeHomEquiv_symm_iff (M := M.over U) σ.s).mp
    inferInstance
    (op (Over.mk (homOfLE h)))
  have e : (fun a : σ.I → Γ(X, V) => ∑ i, a i •
      M.presheaf.map (homOfLE h).op
        (PresheafOfModules.sections.eval (σ.s i) (op (Over.mk (𝟙 U))))) =
      SheafOfModules.coordMap (M.over U) σ.s (op (Over.mk (homOfLE h))) := by
    funext a
    refine Finset.sum_congr rfl fun i _ => ?_
    congr 1
    exact PresheafOfModules.sections_property (σ.s i)
      (f := (Over.homMk (homOfLE h) (by simp) :
        Over.mk (homOfLE h) ⟶ Over.mk (𝟙 U)).op)
  rw [e]
  exact hb

/-- The section of `M.over U` over all of `Over U` given by a section of `M` over `U`. -/
noncomputable def overSection (M : X.Modules) (U : X.Opens) (m : Γ(M, U)) :
    (M.over U).sections :=
  PresheafOfModules.sectionsMk (fun Y => M.presheaf.map Y.unop.hom.op m) (by
    intro Y Y' f
    show M.presheaf.map f.unop.left.op (M.presheaf.map Y.unop.hom.op m) = _
    rw [← ConcreteCategory.comp_apply, ← M.presheaf.map_comp]
    congr 2)

/-- A frame over `U` gives bijective coordinate maps of `M.over U` at every object. -/
theorem bijective_coordMap_overSection {M : X.Modules} {U : X.Opens} {ι : Type u}
    [Fintype ι] {c : ι → Γ(M, U)} (hc : IsFrame M U c) (Y : (Over U)ᵒᵖ) :
    Function.Bijective
      (SheafOfModules.coordMap (M.over U) (fun i => overSection M U (c i)) Y) := by
  have h : Y.unop.left ≤ U := leOfHom Y.unop.hom
  exact hc.bijective Y.unop.left h

/-- The finite free generating sections of `M.over U` attached to a frame. -/
noncomputable def frameGeneratingSections {M : X.Modules} {U : X.Opens} {ι : Type u}
    [Fintype ι] {c : ι → Γ(M, U)} (hc : IsFrame M U c) : (M.over U).GeneratingSections where
  I := ι
  s i := overSection M U (c i)
  epi := by
    have : IsIso ((M.over U).freeHomEquiv.symm fun i => overSection M U (c i)) :=
      (SheafOfModules.isIso_freeHomEquiv_symm_iff _).mpr (bijective_coordMap_overSection hc)
    infer_instance

/-- The chart `free ι ⟶ M.over U` attached to a frame is an isomorphism. -/
theorem isIso_frameGeneratingSections_π {M : X.Modules} {U : X.Opens} {ι : Type u}
    [Fintype ι] {c : ι → Γ(M, U)} (hc : IsFrame M U c) :
    IsIso (frameGeneratingSections hc).π :=
  (SheafOfModules.isIso_freeHomEquiv_symm_iff (M := M.over U) (I := ι) _).mpr
    (bijective_coordMap_overSection hc)

/-- The sections of `M.restrict U.ι` over all opens of `U` induced by a section of `M` over `U`. -/
noncomputable def restrictSection (M : X.Modules) (U : X.Opens) (m : Γ(M, U)) :
    (M.restrict U.ι).sections :=
  PresheafOfModules.sectionsMk
    (fun V => M.presheaf.map (homOfLE (Scheme.Opens.ι_image_le U V.unop)).op m) (by
    intro V W g
    show M.presheaf.map (U.ι.opensFunctor.map g.unop).op
      (M.presheaf.map (homOfLE (Scheme.Opens.ι_image_le U V.unop)).op m) = _
    rw [← ConcreteCategory.comp_apply, ← M.presheaf.map_comp]
    rfl)

/-- A frame over `U` trivializes the restriction: `free ι ⟶ M.restrict U.ι` is an isomorphism. -/
theorem isIso_restrict_frame {M : X.Modules} {U : X.Opens} {ι : Type u} [Fintype ι]
    {c : ι → Γ(M, U)} (hc : IsFrame M U c) :
    IsIso ((M.restrict U.ι).freeHomEquiv.symm fun i => restrictSection M U (c i)) := by
  refine (SheafOfModules.isIso_freeHomEquiv_symm_iff (M := M.restrict U.ι) _).mpr fun V => ?_
  have hb := hc.bijective (U.ι ''ᵁ V.unop) (Scheme.Opens.ι_image_le U V.unop)
  have e : SheafOfModules.coordMap (M.restrict U.ι) (fun i => restrictSection M U (c i)) V =
      (fun a : ι → Γ(X, U.ι ''ᵁ V.unop) => ∑ i, a i •
        M.presheaf.map (homOfLE (Scheme.Opens.ι_image_le U V.unop)).op (c i)) ∘
      (fun (a : ι → Γ(U.toScheme, V.unop)) i => (U.ι.appIso V.unop).inv (a i)) := by
    funext a
    refine Finset.sum_congr rfl fun i _ => ?_
    rfl
  rw [e]
  refine hb.comp ?_
  exact (Equiv.piCongrRight fun _ =>
    (U.ι.appIso V.unop).symm.commRingCatIsoToRingEquiv.toEquiv).bijective


/-- Conversely, if `free ι ⟶ M.restrict U.ι` (built from `c`) is an isomorphism, then `c` is a
frame over `U`. -/
theorem isFrame_iff_isIso_restrict {M : X.Modules} {U : X.Opens} {ι : Type u} [Fintype ι]
    (c : ι → Γ(M, U)) :
    IsFrame M U c ↔
      IsIso ((M.restrict U.ι).freeHomEquiv.symm fun i => restrictSection M U (c i)) := by
  refine ⟨isIso_restrict_frame, fun h => ⟨fun V hV => ?_⟩⟩
  obtain ⟨W, rfl⟩ : ∃ W : U.toScheme.Opens, U.ι ''ᵁ W = V :=
    ⟨U.ι ⁻¹ᵁ V, by simpa [Scheme.Hom.image_preimage_eq_opensRange_inf] using hV⟩
  have hb := (SheafOfModules.isIso_freeHomEquiv_symm_iff
    (M := M.restrict U.ι) _).mp h (op W)
  have e : SheafOfModules.coordMap (M.restrict U.ι)
      (fun i => restrictSection M U (c i)) (op W) =
      (fun a : ι → Γ(X, U.ι ''ᵁ W) => ∑ i, a i • M.presheaf.map (homOfLE hV).op (c i)) ∘
      (fun (a : ι → Γ(U.toScheme, W)) i => (U.ι.appIso W).inv (a i)) := by
    funext a
    refine Finset.sum_congr rfl fun i _ => ?_
    rfl
  rw [e] at hb
  exact (Function.Bijective.of_comp_iff _
    (Equiv.piCongrRight fun _ =>
      (U.ι.appIso W).symm.commRingCatIsoToRingEquiv.toEquiv).bijective).mp hb

/-- The global sections of an `𝒪`-module, read as compatible families of sections
(`SheafOfModules.sections`), are the sections over `⊤`. -/
noncomputable def sectionsEquivTop {Z : Scheme.{u}} (S : Z.Modules) : S.sections ≃ Γ(S, ⊤) where
  toFun s := PresheafOfModules.sections.eval s (op ⊤)
  invFun m := PresheafOfModules.sectionsMk (fun V => S.presheaf.map (homOfLE le_top).op m) (by
    intro V W g
    show S.presheaf.map g (S.presheaf.map (homOfLE le_top).op m) = _
    rw [← ConcreteCategory.comp_apply, ← S.presheaf.map_comp]
    rfl)
  left_inv s := by
    refine PresheafOfModules.sections_ext _ _ fun V => ?_
    exact PresheafOfModules.sections_property s (homOfLE (le_top : V.unop ≤ ⊤)).op
  right_inv m := by
    show S.presheaf.map (homOfLE le_top).op m = m
    rw [show (homOfLE (le_top : (⊤ : Z.Opens) ≤ ⊤)).op = 𝟙 _ from rfl, S.presheaf.map_id]
    rfl

/-- The Yoneda form of a frame: for `χ : M ⟶ U.ι_* S`, the values `χ(cᵢ)`, read as global
sections of `S` (through `U.ι ⁻¹ᵁ U = ⊤`). -/
noncomputable def frameHomMap (M : X.Modules) (U : X.Opens) {ι : Type u} (c : ι → Γ(M, U))
    (S : U.toScheme.Modules) (χ : M ⟶ (pushforward U.ι).obj S) (i : ι) : Γ(S, ⊤) :=
  S.presheaf.map (homOfLE (Scheme.Opens.ι_preimage_self U).ge).op (χ.app U (c i))

/-- Naturality of a morphism of `𝒪`-modules on sections: restricting `φ(y)` is applying `φ` to
the restriction of `y`. -/
theorem map_hom_app_apply {Z : Scheme.{u}} {M N : Z.Modules} (φ : M ⟶ N) {V W : Z.Opens}
    (h : V ⟶ W) (y : Γ(M, W)) :
    N.presheaf.map h.op (φ.app W y) = φ.app V (M.presheaf.map h.op y) := by
  rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply, ← mapPresheaf_app,
    ← mapPresheaf_app, φ.mapPresheaf.naturality]

/-- Two successive restrictions are one restriction (along any morphism of opens). -/
theorem map_map_apply_eq {Z : Scheme.{u}} (M : Z.Modules) {V W T : Z.Opens} (g : V ⟶ W)
    (g' : W ⟶ T) (g'' : V ⟶ T) (x : Γ(M, T)) :
    M.presheaf.map g.op (M.presheaf.map g'.op x) = M.presheaf.map g''.op x := by
  rw [← ConcreteCategory.comp_apply, ← M.presheaf.map_comp]
  rfl

/-- Two successive restrictions are the restriction along the composite. -/
theorem map_map_apply {Z : Scheme.{u}} (M : Z.Modules) {V W T : Z.Opens} (g : V ⟶ W)
    (g' : W ⟶ T) (x : Γ(M, T)) :
    M.presheaf.map g.op (M.presheaf.map g'.op x) = M.presheaf.map (g ≫ g').op x := by
  rw [← ConcreteCategory.comp_apply, ← M.presheaf.map_comp]
  rfl

/-- Restrictions along two morphisms between the same opens agree. -/
theorem map_apply_congr {Z : Scheme.{u}} (M : Z.Modules) {V W : Z.Opens} (g g' : V ⟶ W)
    (x : Γ(M, W)) : M.presheaf.map g.op x = M.presheaf.map g'.op x := by
  rw [Subsingleton.elim g g']

/-- The restriction map between equal opens (`V ≤ W ≤ V`) is bijective. -/
theorem bijective_map_of_le {Z : Scheme.{u}} (M : Z.Modules) {V W : Z.Opens} (h : V ≤ W)
    (h' : W ≤ V) : Function.Bijective (M.presheaf.map (homOfLE h).op) := by
  obtain rfl := le_antisymm h h'
  rw [show (homOfLE h).op = 𝟙 (op V) from rfl, M.presheaf.map_id]
  exact ⟨fun a b hab => hab, fun b => ⟨b, rfl⟩⟩

/-- `frameHomMap` after the adjunction `restrictFunctor U.ι ⊣ pushforward U.ι` is the map
`φ ↦ (φ(cᵢ|_U))ᵢ` on morphisms out of `M.restrict U.ι`. -/
theorem frameHomMap_homEquiv (M : X.Modules) (U : X.Opens) {ι : Type u} (c : ι → Γ(M, U))
    (S : U.toScheme.Modules) (φ : M.restrict U.ι ⟶ S) (i : ι) :
    frameHomMap M U c S ((restrictAdjunction U.ι).homEquiv M S φ) i =
      sectionsEquivTop S (_root_.SheafOfModules.sectionsMap φ (restrictSection M U (c i))) := by
  rw [Adjunction.homEquiv_unit]
  unfold frameHomMap
  change S.presheaf.map (homOfLE (Scheme.Opens.ι_preimage_self U).ge).op
      (φ.app (U.ι ⁻¹ᵁ U) (M.presheaf.map (homOfLE (U.ι.image_preimage_le U)).op (c i))) =
    φ.app ⊤ (M.presheaf.map (homOfLE (Scheme.Opens.ι_image_le U ⊤)).op (c i))
  refine (map_hom_app_apply φ _ _).trans (congrArg (φ.app ⊤) ?_)
  exact map_map_apply_eq M
    (U.ι.opensFunctor.map (homOfLE (Scheme.Opens.ι_preimage_self U).ge)) _ _ _

/-- **Yoneda criterion for frames.** `c` is a frame of `M` over `U` iff for every `𝒪_U`-module
`S` the map `frameHomMap : (M ⟶ U.ι_* S) → (ι → Γ(S, ⊤))` is bijective. -/
theorem isFrame_iff_bijective_frameHomMap {M : X.Modules} {U : X.Opens} {ι : Type u}
    [Fintype ι] (c : ι → Γ(M, U)) :
    IsFrame M U c ↔ ∀ S : U.toScheme.Modules, Function.Bijective (frameHomMap M U c S) := by
  refine (isFrame_iff_isIso_restrict c).trans ((isIso_iff_coyoneda_map_bijective _).trans ?_)
  refine forall_congr' fun S => ?_
  let E := (M.restrict U.ι).freeHomEquiv.symm fun i => restrictSection M U (c i)
  have key : frameHomMap M U c S ∘ (restrictAdjunction U.ι).homEquiv M S =
      (Equiv.piCongrRight fun _ => sectionsEquivTop S) ∘ S.freeHomEquiv ∘
        (fun φ : M.restrict U.ι ⟶ S => E ≫ φ) := by
    funext φ i
    refine (frameHomMap_homEquiv M U c S φ i).trans ?_
    show _ = sectionsEquivTop S (_root_.SheafOfModules.sectionsMap φ
      ((M.restrict U.ι).freeHomEquiv E i))
    simp only [E, Equiv.apply_symm_apply]
  have b1 := Function.Bijective.of_comp_iff' S.freeHomEquiv.bijective
    (fun φ : M.restrict U.ι ⟶ S => E ≫ φ)
  have b2 := Function.Bijective.of_comp_iff'
    (Equiv.piCongrRight fun _ => sectionsEquivTop S).bijective
    (S.freeHomEquiv ∘ fun φ : M.restrict U.ι ⟶ S => E ≫ φ)
  have b3 := Function.Bijective.of_comp_iff (frameHomMap M U c S)
    ((restrictAdjunction U.ι).homEquiv M S).bijective
  exact b1.symm.trans (b2.symm.trans
    (Eq.subst (motive := fun g => Function.Bijective g ↔ _) key b3))

end Scheme.Modules

end Hironaka
