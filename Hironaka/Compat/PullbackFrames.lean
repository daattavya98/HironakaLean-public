/-
Copyright (c) 2026 Daattavya Aggarwal, Minhyong Kim, Oisin Kim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daattavya Aggarwal, Minhyong Kim, Oisin Kim
-/
module

public import Hironaka.Compat.ModuleFrames
public import Mathlib.AlgebraicGeometry.Properties

/-!
# Pulling back frames; frames versus Mathlib's local freeness (Compat API for Corollary 2)

Hironaka, Ch. 0, Corollary 2 of Main Theorem II (p. 145) pulls a locally free coherent sheaf
`F` back along a succession of monoidal transformations `f : X' → X` and works with the
pulled-back bases `f*(c_1), ..., f*(c_r)` of `f*(F)`.  Mathlib knows that `f*` of a free sheaf
is free (`SheafOfModules.pullbackObjFreeIso`) but not which sections of `f*(F)` form a basis,
nor how to pass between frames and `SheafOfModules.IsLocallyFree`.  This module proves:

* `Hironaka.Scheme.Modules.pullbackSection`: the pulled-back section `f*(m)` of `f*(F)` over
  `f ⁻¹ᵁ U` (the unit of `pullback f ⊣ pushforward f`), with semilinearity
  (`pullbackSection_smul`), naturality (`pullback_map_app_pullbackSection`) and compatibility
  with restriction (`map_pullbackSection`);
* `isFrame_pullback`: **the pulled-back sections of a frame of `F` over `U` form a frame of
  `f*(F)` over `f ⁻¹ᵁ U`** (proof by the Yoneda criterion
  `isFrame_iff_bijective_frameHomMap` of `Hironaka/Compat/ModuleFrames.lean`);
* `HasLocalFrames` (every point has a neighbourhood with a finite frame) and its equivalence with
  Mathlib's pair `IsLocallyFree` + `IsFiniteType` (`isLocallyFree_of_hasLocalFrames`,
  `isFiniteType_of_hasLocalFrames`, `hasLocalFrames_of_isLocallyFree`); the converse direction
  rests on the rank inequality `Hironaka.SheafOfModules.finite_of_epi` for epimorphisms between
  free sheaves (`Hironaka/Compat/ModuleFrames.lean`);
* consequently `hasLocalFrames_pullback`: the pullback of a locally free sheaf of finite type is
  locally free of finite type.

This is infrastructure (no statement of the paper); it is not a deviation.
-/

@[expose] public section

open CategoryTheory Limits Opposite AlgebraicGeometry

universe u

namespace Hironaka

namespace Scheme.Modules

open AlgebraicGeometry.Scheme.Modules

variable {X Y : Scheme.{u}}

/-! ### Pulled-back sections -/

/-- The pulled-back section `f*(m)` of `f*(F)` over `f ⁻¹ᵁ U` of a section `m` of `F` over `U`:
the image of `m` under the unit `F ⟶ f_* f^* F` of the adjunction `pullback f ⊣ pushforward f`. -/
noncomputable def pullbackSection (f : Y ⟶ X) (F : X.Modules) {U : X.Opens} (m : Γ(F, U)) :
    Γ((Scheme.Modules.pullback f).obj F, f ⁻¹ᵁ U) :=
  ((pullbackPushforwardAdjunction f).unit.app F).app U m

/-- Pulling back sections is additive. -/
theorem pullbackSection_add (f : Y ⟶ X) (F : X.Modules) {U : X.Opens} (m m' : Γ(F, U)) :
    pullbackSection f F (m + m') = pullbackSection f F m + pullbackSection f F m' :=
  map_add _ _ _

/-- Pulling back sections is semilinear along `f^♯ : Γ(X, U) ⟶ Γ(Y, f ⁻¹ᵁ U)`. -/
theorem pullbackSection_smul (f : Y ⟶ X) (F : X.Modules) {U : X.Opens} (a : Γ(X, U))
    (m : Γ(F, U)) :
    pullbackSection f F (a • m) = f.app U a • pullbackSection f F m :=
  Hom.app_smul _ a m

/-- Naturality of pulled-back sections: `(f^* α)(f*(m)) = f*(α(m))`. -/
theorem pullback_map_app_pullbackSection (f : Y ⟶ X) {F F' : X.Modules} (α : F ⟶ F')
    {U : X.Opens} (m : Γ(F, U)) :
    ((Scheme.Modules.pullback f).map α).app (f ⁻¹ᵁ U) (pullbackSection f F m) =
      pullbackSection f F' (α.app U m) := by
  have h := congrArg (fun φ : F ⟶ (pushforward f).obj ((Scheme.Modules.pullback f).obj F') =>
    φ.app U m) ((pullbackPushforwardAdjunction f).unit.naturality α)
  exact h.symm

/-- Pulled-back sections are compatible with restriction. -/
theorem map_pullbackSection (f : Y ⟶ X) (F : X.Modules) {U V : X.Opens} (i : V ⟶ U)
    (m : Γ(F, U)) :
    ((Scheme.Modules.pullback f).obj F).presheaf.map
        ((TopologicalSpace.Opens.map f.base).map i).op (pullbackSection f F m) =
      pullbackSection f F (F.presheaf.map i.op m) :=
  map_hom_app_apply ((pullbackPushforwardAdjunction f).unit.app F) i m

/-! ### Pulling back a frame -/

/-- The comparison `f_* (U'.ι)_* T ⟶ U.ι_* (f ∣_ U)_* T` (`U' = f ⁻¹ᵁ U`), from
`f ∣_ U ≫ U.ι = U'.ι ≫ f`. -/
noncomputable def pushforwardRestrictHom (f : Y ⟶ X) (U : X.Opens)
    (T : (f ⁻¹ᵁ U).toScheme.Modules) :
    (pushforward f).obj ((pushforward (f ⁻¹ᵁ U).ι).obj T) ⟶
      (pushforward U.ι).obj ((pushforward (f ∣_ U)).obj T) :=
  (pushforwardComp (f ⁻¹ᵁ U).ι f).hom.app T ≫
    (pushforwardCongr (morphismRestrict_ι f U).symm).hom.app T ≫
      (pushforwardComp (f ∣_ U) U.ι).inv.app T

/-- The comparison `pushforwardRestrictHom` is an isomorphism. -/
instance (f : Y ⟶ X) (U : X.Opens) (T : (f ⁻¹ᵁ U).toScheme.Modules) :
    IsIso (pushforwardRestrictHom f U T) := by
  unfold pushforwardRestrictHom
  infer_instance

/-- On sections over `U`, `pushforwardRestrictHom` is a restriction map of `T` (between two
opens which are both `⊤`). -/
theorem pushforwardRestrictHom_app (f : Y ⟶ X) (U : X.Opens) (T : (f ⁻¹ᵁ U).toScheme.Modules) :
    (pushforwardRestrictHom f U T).app U = T.presheaf.map (homOfLE (by simp) :
      (f ∣_ U) ⁻¹ᵁ U.ι ⁻¹ᵁ U ⟶ (f ⁻¹ᵁ U).ι ⁻¹ᵁ f ⁻¹ᵁ U).op := by
  simp only [pushforwardRestrictHom, Hom.comp_app, pushforwardComp_hom_app_app,
    pushforwardCongr_hom_app_app, pushforwardComp_inv_app_app]
  rfl

/-- **Pulled-back frames.** If `c` is a frame of `F` over `U`, the pulled-back sections
`f*(cᵢ)` form a frame of `f^* F` over `f ⁻¹ᵁ U`. -/
theorem isFrame_pullback (f : Y ⟶ X) {F : X.Modules} {U : X.Opens} {ι : Type u} [Fintype ι]
    {c : ι → Γ(F, U)} (hc : IsFrame F U c) :
    IsFrame ((Scheme.Modules.pullback f).obj F) (f ⁻¹ᵁ U) (fun i => pullbackSection f F (c i)) := by
  refine (isFrame_iff_bijective_frameHomMap _).mpr fun T => ?_
  let S := (pushforward (f ∣_ U)).obj T
  have hS := (isFrame_iff_bijective_frameHomMap c).mp hc S
  let adj := pullbackPushforwardAdjunction f
  let eh := pushforwardRestrictHom f U T
  have htop : (⊤ : (f ⁻¹ᵁ U).toScheme.Opens) ≤ (f ∣_ U) ⁻¹ᵁ ⊤ := by simp
  have key : frameHomMap ((Scheme.Modules.pullback f).obj F) (f ⁻¹ᵁ U)
      (fun i => pullbackSection f F (c i)) T =
      (fun a i => T.presheaf.map (homOfLE htop).op (a i)) ∘ frameHomMap F U c S ∘
        (fun χ => χ ≫ eh) ∘ adj.homEquiv F ((pushforward (f ⁻¹ᵁ U).ι).obj T) := by
    funext ψ i
    have h1 : (adj.homEquiv F _ ψ ≫ eh).app U (c i) =
        T.presheaf.map (homOfLE (by simp) :
          (f ∣_ U) ⁻¹ᵁ U.ι ⁻¹ᵁ U ⟶ (f ⁻¹ᵁ U).ι ⁻¹ᵁ f ⁻¹ᵁ U).op
          (ψ.app (f ⁻¹ᵁ U) (pullbackSection f F (c i))) := by
      rw [Hom.comp_app, ConcreteCategory.comp_apply, pushforwardRestrictHom_app,
        Adjunction.homEquiv_unit]
      rfl
    show T.presheaf.map (homOfLE (Scheme.Opens.ι_preimage_self (f ⁻¹ᵁ U)).ge).op
        (ψ.app (f ⁻¹ᵁ U) (pullbackSection f F (c i))) =
      T.presheaf.map (homOfLE htop).op (T.presheaf.map ((TopologicalSpace.Opens.map
        (f ∣_ U).base).map (homOfLE (Scheme.Opens.ι_preimage_self U).ge)).op
          ((adj.homEquiv F _ ψ ≫ eh).app U (c i)))
    rw [h1, map_map_apply]
    exact (map_apply_congr T _ _ _).trans (map_map_apply T _ _ _).symm
  have hiso : Function.Bijective (fun χ : F ⟶ (pushforward f).obj
      ((pushforward (f ⁻¹ᵁ U).ι).obj T) => χ ≫ eh) :=
    ⟨fun a b h => (cancel_mono eh).mp h, fun b => ⟨b ≫ inv eh, by simp⟩⟩
  have htr := bijective_map_of_le T htop (by simp)
  rw [key]
  exact (Function.Bijective.piMap fun _ => htr).comp (hS.comp (hiso.comp
    (adj.homEquiv _ _).bijective))

/-! ### Frames versus `IsLocallyFree` + `IsFiniteType` -/

/-- `M` has local frames: every point has an open neighbourhood over which `M` has a finite
frame (the reading of "locally free of finite rank" used for Corollary 2, p. 145). -/
def HasLocalFrames (M : X.Modules) : Prop :=
  ∀ x : X, ∃ (U : X.Opens) (_ : x ∈ U) (ι : Type u) (_ : Fintype ι) (c : ι → Γ(M, U)),
    IsFrame M U c

/-- A family of opens `U x ∋ x` indexed by the points covers `X` (Grothendieck topology). -/
theorem coversTop_of_forall_mem {U : X → X.Opens} (h : ∀ x, x ∈ U x) :
    (_root_.Opens.grothendieckTopology X).CoversTop U := by
  rw [_root_.Opens.coversTop_iff]
  exact TopologicalSpace.IsOpenCover.mk (top_le_iff.mp fun x _ =>
    TopologicalSpace.Opens.mem_iSup.mpr ⟨x, h x⟩)

set_option backward.isDefEq.respectTransparency false in
/-- The local generators data of a family of frames covering `X`. -/
noncomputable def localGeneratorsDataOfFrames {M : X.Modules} {U : X → X.Opens}
    (hxU : ∀ x, x ∈ U x) {ι : X → Type u} [∀ x, Fintype (ι x)] {c : ∀ x, ι x → Γ(M, U x)}
    (hc : ∀ x, IsFrame M (U x) (c x)) :
    M.LocalGeneratorsData where
  I := X
  X := U
  coversTop := coversTop_of_forall_mem hxU
  generators x := frameGeneratingSections (hc x)

set_option backward.isDefEq.respectTransparency false in
/-- The local generators data of a covering family of frames is locally free data. -/
theorem isLocallyFreeData_localGeneratorsDataOfFrames {M : X.Modules} {U : X → X.Opens}
    (hxU : ∀ x, x ∈ U x) {ι : X → Type u} [∀ x, Fintype (ι x)] {c : ∀ x, ι x → Γ(M, U x)}
    (hc : ∀ x, IsFrame M (U x) (c x)) :
    (localGeneratorsDataOfFrames hxU hc).IsLocallyFreeData where
  isIso x := by
    dsimp [localGeneratorsDataOfFrames]
    exact isIso_frameGeneratingSections_π (hc x)

set_option backward.isDefEq.respectTransparency false in
/-- The local generators data of a covering family of frames is of finite type. -/
theorem isFiniteType_localGeneratorsDataOfFrames {M : X.Modules} {U : X → X.Opens}
    (hxU : ∀ x, x ∈ U x) {ι : X → Type u} [∀ x, Fintype (ι x)] {c : ∀ x, ι x → Γ(M, U x)}
    (hc : ∀ x, IsFrame M (U x) (c x)) :
    (localGeneratorsDataOfFrames hxU hc).IsFiniteType where
  isFiniteType x := ⟨inferInstanceAs (Finite (ι x))⟩

/-- Local frames give Mathlib's local freeness. -/
theorem isLocallyFree_of_hasLocalFrames {M : X.Modules} (h : HasLocalFrames M) :
    M.IsLocallyFree := by
  choose U hxU ι hι c hc using h
  have := isLocallyFreeData_localGeneratorsDataOfFrames hxU hc
  exact (localGeneratorsDataOfFrames hxU hc).isLocallyFree

/-- Local frames give Mathlib's finite type. -/
theorem isFiniteType_of_hasLocalFrames {M : X.Modules} (h : HasLocalFrames M) :
    M.IsFiniteType := by
  choose U hxU ι hι c hc using h
  constructor
  exact ⟨localGeneratorsDataOfFrames hxU hc, isFiniteType_localGeneratorsDataOfFrames hxU hc⟩

set_option backward.isDefEq.respectTransparency false in
/-- **Finite-rank charts.** A locally free `𝒪_X`-module of finite type (Mathlib's
`IsLocallyFree` + `IsFiniteType`) has local frames: the chart indices of `IsLocallyFree` are
finite near every point (`Hironaka.SheafOfModules.finite_of_epi` on the Over-site of a common
neighbourhood, whose ring of sections is a nonzero commutative ring). -/
theorem hasLocalFrames_of_isLocallyFree (M : X.Modules) [M.IsLocallyFree] [M.IsFiniteType] :
    HasLocalFrames M := by
  intro x
  obtain ⟨q, hq⟩ := _root_.SheafOfModules.IsLocallyFree.exists_isLocallyFreeData
    (R := X.ringCatSheaf) (M := M)
  obtain ⟨σ, hσ⟩ := _root_.SheafOfModules.IsFiniteType.exists_localGeneratorsData
    (R := X.ringCatSheaf) M
  obtain ⟨i, hi⟩ := ((_root_.Opens.coversTop_iff _ q.X).mp q.coversTop).exists_mem x
  obtain ⟨j, hj⟩ := ((_root_.Opens.coversTop_iff _ σ.X).mp σ.coversTop).exists_mem x
  let W := q.X i ⊓ σ.X j
  have hW : x ∈ W := ⟨hi, hj⟩
  let f1 : W ⟶ q.X i := homOfLE inf_le_left
  let f2 : W ⟶ σ.X j := homOfLE inf_le_right
  let g1 := (q.generators i).map (_root_.SheafOfModules.overMap X.ringCatSheaf f1)
    (_root_.SheafOfModules.overMapUnitIso f1).symm
  let g2 := (σ.generators j).map (_root_.SheafOfModules.overMap X.ringCatSheaf f2)
    (_root_.SheafOfModules.overMapUnitIso f2).symm
  let e1 := (_root_.SheafOfModules.overFunctorMap X.ringCatSheaf f1).app M
  let e2 := (_root_.SheafOfModules.overFunctorMap X.ringCatSheaf f2).app M
  have hq1 : IsIso (q.generators i).π := hq.isIso i
  have : IsIso g1.π := inferInstanceAs (IsIso ((q.generators i).map _ _).π)
  have : Epi g2.π := g2.epi
  let p := g2.π ≫ e2.hom ≫ e1.inv ≫ inv g1.π
  have : Nonempty W := ⟨⟨x, hW⟩⟩
  have : Nontrivial Γ(X, W) := Scheme.component_nontrivial X W
  have : StrongRankCondition ((X.ringCatSheaf.over W).obj.obj (op (Over.mk (𝟙 W))))ᵐᵒᵖ :=
    inferInstanceAs (StrongRankCondition (Γ(X, W))ᵐᵒᵖ)
  have : Finite (σ.generators j).I := (hσ.isFiniteType j).finite
  have hfin : Finite (q.generators i).I :=
    Hironaka.SheafOfModules.finite_of_epi (κ := (σ.generators j).I) Over.mkIdTerminal p
  have := Fintype.ofFinite (q.generators i).I
  obtain ⟨c, hc⟩ := isFrame_of_isIso (q.generators i)
  exact ⟨q.X i, hi, _, _, c, hc⟩

/-- Local frames are exactly Mathlib's pair `IsLocallyFree` + `IsFiniteType`. -/
theorem hasLocalFrames_iff (M : X.Modules) :
    HasLocalFrames M ↔ M.IsLocallyFree ∧ M.IsFiniteType := by
  refine ⟨fun h => ⟨isLocallyFree_of_hasLocalFrames h, isFiniteType_of_hasLocalFrames h⟩,
    fun ⟨h₁, h₂⟩ => hasLocalFrames_of_isLocallyFree M⟩

/-! ### Pullbacks of locally free sheaves of finite type -/

/-- The pullback of a sheaf with local frames has local frames (the pulled-back ones). -/
theorem hasLocalFrames_pullback (f : Y ⟶ X) {F : X.Modules} (h : HasLocalFrames F) :
    HasLocalFrames ((Scheme.Modules.pullback f).obj F) := by
  intro y
  obtain ⟨U, hU, ι, _, c, hc⟩ := h (f y)
  exact ⟨f ⁻¹ᵁ U, hU, ι, _, _, isFrame_pullback f hc⟩

/-- The pullback of a locally free sheaf of finite type is locally free. -/
theorem isLocallyFree_pullback (f : Y ⟶ X) (F : X.Modules) [F.IsLocallyFree]
    [F.IsFiniteType] : ((Scheme.Modules.pullback f).obj F).IsLocallyFree :=
  isLocallyFree_of_hasLocalFrames (hasLocalFrames_pullback f (hasLocalFrames_of_isLocallyFree F))

/-- The pullback of a locally free sheaf of finite type is of finite type. -/
theorem isFiniteType_pullback (f : Y ⟶ X) (F : X.Modules) [F.IsLocallyFree]
    [F.IsFiniteType] : ((Scheme.Modules.pullback f).obj F).IsFiniteType :=
  isFiniteType_of_hasLocalFrames (hasLocalFrames_pullback f (hasLocalFrames_of_isLocallyFree F))

end Scheme.Modules

end Hironaka
