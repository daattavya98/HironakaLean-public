/-
Copyright (c) 2026 Daattavya Aggarwal, Minhyong Kim, Oisin Kim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daattavya Aggarwal, Minhyong Kim, Oisin Kim
-/
module

public import Hironaka.Compat.PullbackDatum
public import Hironaka.Compat.FrameModifications

/-!
# The subsheaf `L` of `f*(F)` (proof of Corollary 2 of Main Theorem II, pp. 145–146)

The coordinates of a pulled-back section in a pulled-back frame, the injectivity of `f*(M) → f*(F)` on
sections (`pullback_map_app_injective`), the subsheaf `L` of the sections which lie in the image of an
injective morphism over a dense open set (`localImage`, `localImageModule`) and its local structure, and the
open set where `J` is trivial (`trivialLocus`) with its preimage under `f`.
-/

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry AlgebraicGeometry.Scheme TopologicalSpace Opposite
open Hironaka.Scheme.Modules AlgebraicGeometry.Scheme.Modules

namespace Hironaka

universe u

variable {X Y : Scheme.{u}}

/-- Pulling back sections commutes with finite sums. -/
theorem pullbackSection_sum (f : Y ⟶ X) (F : X.Modules) {U : X.Opens} {κ : Type*} (t : Finset κ)
    (m : κ → Γ(F, U)) :
    pullbackSection f F (∑ k ∈ t, m k) = ∑ k ∈ t, pullbackSection f F (m k) := by
  unfold pullbackSection
  exact map_sum _ _ _

/-- **Coordinates of a pulled-back section.**  The coordinates of `f*(m)|_T` in the pulled-back frame `f*(c)` are
the pull-backs `f^♯` of the coordinates of `m` in the frame `c`. -/
theorem coord_pullbackSection (f : Y ⟶ X) {F : X.Modules} {U : X.Opens} {ι : Type u} [Fintype ι]
    {c : ι → Γ(F, U)} (hc : IsFrame F U c) {W : X.Opens} (hWU : W ≤ U) (m : Γ(F, W)) (j : ι)
    {T : Y.Opens} (hT : T ≤ f ⁻¹ᵁ W) :
    (isFrame_pullback f hc).coord (hT.trans (show f ⁻¹ᵁ W ≤ f ⁻¹ᵁ U from fun _ hz => hWU hz))
      (((Scheme.Modules.pullback f).obj F).sectionRes hT (pullbackSection f F m)) j =
      resO Y hT (f.app W (hc.coord hWU m j)) := by
  refine (isFrame_pullback f hc).coord_eq _ _ (fun j => resO Y hT (f.app W (hc.coord hWU m j))) ?_ j
  conv_rhs => rw [← hc.sum_coord_smul hWU m]
  rw [pullbackSection_sum]
  rw [sectionRes_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [pullbackSection_smul, sectionRes_smul]
  congr 1
  have e : pullbackSection f F (F.sectionRes hWU (c k)) =
      ((Scheme.Modules.pullback f).obj F).sectionRes (show f ⁻¹ᵁ W ≤ f ⁻¹ᵁ U from fun _ hz => hWU hz)
        (pullbackSection f F (c k)) :=
    (map_pullbackSection f F (homOfLE hWU) (c k)).symm
  rw [e, sectionRes_res]

variable {M F : X.Modules} {f : Y ⟶ X} {i : M ⟶ F} {y : Y}

namespace PullbackDatum

variable (δ : PullbackDatum f i y)

/-- `V' ≤ f⁻¹ U`. -/
theorem le_U : δ.V' ≤ f ⁻¹ᵁ δ.U := fun _ hz => δ.hWU (δ.hV'W hz)

/-- `V' ≤ f⁻¹ V`. -/
theorem le_V : δ.V' ≤ f ⁻¹ᵁ δ.V := fun _ hz => δ.hWV (δ.hV'W hz)

/-- The coordinates of `(f*i)(f*d)|_T` in the pulled-back frame `f*(c)` are `g h'_j|_T` (the pull-back of the
coordinates `h_j` of `i(d)`: `f^♯ h_j = g h'_j`). -/
theorem coord_sigma {T : Y.Opens} (hT : T ≤ δ.V') (j : δ.ι) :
    (isFrame_pullback f δ.hc).coord (hT.trans δ.le_U)
      (((Scheme.Modules.pullback f).obj F).sectionRes (hT.trans δ.le_V)
        (((Scheme.Modules.pullback f).map i).app (f ⁻¹ᵁ δ.V) (pullbackSection f M δ.d))) j =
      resO Y hT (δ.g * δ.h' j) := by
  have e1 := pullback_map_app_pullbackSection f i (U := δ.V) δ.d
  rw [e1]
  have hTW : T ≤ f ⁻¹ᵁ δ.W := hT.trans δ.hV'W
  have e2 : ((Scheme.Modules.pullback f).obj F).sectionRes (hT.trans δ.le_V)
      (pullbackSection f F (i.app δ.V δ.d)) =
      ((Scheme.Modules.pullback f).obj F).sectionRes hTW
        (pullbackSection f F (i.app δ.W (M.sectionRes δ.hWV δ.d))) := by
    rw [app_sectionRes]
    have := map_pullbackSection f F (homOfLE δ.hWV) (i.app δ.V δ.d)
    change ((Scheme.Modules.pullback f).obj F).presheaf.map _ _ = _ at this
    rw [← sectionRes_res _ hTW (show f ⁻¹ᵁ δ.W ≤ f ⁻¹ᵁ δ.V from fun _ hz => δ.hWV hz)]
    congr 1
  rw [e2, coord_pullbackSection f δ.hc δ.hWU _ j hTW]
  have := congrArg (resO Y hT) (δ.hg j)
  rw [resO_resO] at this
  exact this

/-- On an integral scheme, `g` is non-zero in the function field on every non-empty open subset of `V'`. -/
theorem germToFunctionField_g_ne_zero [IsIntegral Y] {T : Y.Opens} [Nonempty T] (hT : T ≤ δ.V') :
    Y.germToFunctionField T (resO Y hT δ.g) ≠ 0 := by
  obtain ⟨⟨z, hzT⟩⟩ := ‹Nonempty T›
  have hzV : z ∈ δ.V' := hT hzT
  have e1 := Scheme.algebraMap_germ_eq_germToFunctionField Y hzT (resO Y hT δ.g)
  have e2 : (Y.presheaf.germ T z hzT).hom (resO Y hT δ.g) = (Y.presheaf.germ δ.V' z hzV).hom δ.g :=
    TopCat.Presheaf.germ_res_apply Y.presheaf (homOfLE hT) z hzT _
  rw [← e1, e2]
  exact fun h0 => δ.hg0 z hzV ((IsFractionRing.injective (Y.presheaf.stalk z) Y.functionField)
    (by rw [h0, map_zero]))

/-- The vector `e = ∑ h'_j f*(c_j)|_{V'}`, the local generator of `L` (p. 145: "`f^*(M) = f^{-1}(J) L`"). -/
noncomputable def e : Γ((Scheme.Modules.pullback f).obj F, δ.V') :=
  ∑ j, δ.h' j • ((Scheme.Modules.pullback f).obj F).sectionRes δ.le_U (pullbackSection f F (δ.c j))

/-- The coordinates of `e` are the `h'_j`. -/
theorem coord_e (j : δ.ι) :
    (isFrame_pullback f δ.hc).coord δ.le_U δ.e j = δ.h' j :=
  (isFrame_pullback f δ.hc).coord_eq δ.le_U _ δ.h' rfl j

/-- **`f*(i(d)) = g · e`** on `V'`: the image of the pulled-back generator is the product of the generator `g` of
`f⁻¹(J)` and the vector `e` with coordinates `h'_j`. -/
theorem sigma_eq :
    ((Scheme.Modules.pullback f).obj F).sectionRes δ.le_V
      (((Scheme.Modules.pullback f).map i).app (f ⁻¹ᵁ δ.V) (pullbackSection f M δ.d)) = δ.g • δ.e := by
  refine (isFrame_pullback f δ.hc).ext_coord δ.le_U fun j => ?_
  have := δ.coord_sigma (le_refl δ.V') j
  rw [resO_self] at this
  rw [IsFrame.coord_smul, δ.coord_e]
  exact this

/-- If `a` kills all `g h'_j` on an open subset of `V'`, then `a = 0` (the coordinates `h'_j` are unimodular and
`g` is non-zero on an integral scheme). -/
theorem eq_zero_of_mul_g [IsIntegral Y] {T : Y.Opens} (hT : T ≤ δ.V') (a : Γ(Y, T))
    (h : ∀ j, a * resO Y hT (δ.g * δ.h' j) = 0) : a = 0 := by
  by_cases hne : Nonempty T
  · have hag : a * resO Y hT δ.g = 0 := by
      have h1 : resO Y hT (∑ j, δ.a j * δ.h' j) = 1 := by
        rw [δ.ha, resO_one]
      rw [resO_sum] at h1
      calc a * resO Y hT δ.g = a * resO Y hT δ.g * ∑ j, resO Y hT (δ.a j * δ.h' j) := by rw [h1, mul_one]
        _ = ∑ j, resO Y hT (δ.a j) * (a * resO Y hT (δ.g * δ.h' j)) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun j _ => ?_
          simp only [resO_mul]
          ring
        _ = 0 := by simp [h]
    have hε := congrArg (Y.germToFunctionField T) hag
    rw [map_mul, map_zero] at hε
    have hg := δ.germToFunctionField_g_ne_zero hT
    exact Scheme.germToFunctionField_injective Y T (by
      rw [map_zero]; exact (mul_eq_zero.mp hε).resolve_right hg)
  · have := subsingleton_sections_of_not_nonempty T hne
    exact Subsingleton.elim _ _

end PullbackDatum


/-- **`f*(M) → f*(F)` is injective on sections** (the paper: "`f*(M)` is viewed as a subsheaf of `f*(F)` in a natural
manner", p. 145-146; `f*` is not exact).  Locally `(f*i)(a f*d) = a g e` and the coordinates `a g h'_j` vanish only
for `a = 0`. -/
theorem pullback_map_app_injective [IsIntegral Y] (hδ : ∀ y, Nonempty (PullbackDatum f i y))
    (T : Y.Opens) : Function.Injective (((Scheme.Modules.pullback f).map i).app T) := by
  rw [injective_iff_map_eq_zero]
  intro s hs
  let δ : ∀ y, PullbackDatum f i y := fun y => (hδ y).some
  refine Modules.eq_of_locally_eq _ (fun y : T => T ⊓ (δ y).V') (fun y => inf_le_left)
    (fun z hz => TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨z, hz⟩, hz, (δ z).hyV'⟩) fun y => ?_
  rw [sectionRes_zero]
  have hT' : T ⊓ (δ y).V' ≤ (δ y).V' := inf_le_right
  have hTV : T ⊓ (δ y).V' ≤ f ⁻¹ᵁ (δ y).V := hT'.trans (δ y).le_V
  obtain ⟨a, ha⟩ := ((isFrame_pullback f (δ y).hd).bijective (T ⊓ (δ y).V') hTV).2
    (((Scheme.Modules.pullback f).obj M).sectionRes inf_le_left s)
  simp only [Finset.univ_unique, Finset.sum_singleton] at ha
  have hφs : ((Scheme.Modules.pullback f).map i).app (T ⊓ (δ y).V')
      (((Scheme.Modules.pullback f).obj M).sectionRes inf_le_left s) = 0 := by
    rw [app_sectionRes, hs, sectionRes_zero]
  rw [← ha] at hφs
  have hφs' : a PUnit.unit • ((Scheme.Modules.pullback f).obj F).sectionRes hTV
      (((Scheme.Modules.pullback f).map i).app (f ⁻¹ᵁ (δ y).V) (pullbackSection f M (δ y).d)) = 0 := by
    rw [← hφs, Hom.app_smul]
    congr 1
    exact (app_sectionRes ((Scheme.Modules.pullback f).map i) hTV _).symm
  have ha0 : a PUnit.unit = 0 := (δ y).eq_zero_of_mul_g hT' _ fun j => by
    have := congrArg ((isFrame_pullback f (δ y).hc).coord (hT'.trans (δ y).le_U) · j) hφs'
    simp only [IsFrame.coord_smul, (δ y).coord_sigma hT' j, IsFrame.coord_zero] at this
    exact this
  rw [← ha]
  show a PUnit.unit • _ = 0
  rw [ha0, zero_smul]


/-! ### The subsheaf `L`: sections which lie in the image of an injective morphism over a dense open set -/

section LocalImage

variable {N G : Y.Modules} (φ : N ⟶ G) (U0 : Y.Opens)

/-- The sections `s` of `G` over `V` whose restriction to `V ⊓ U0` lies in the image of `φ`. -/
noncomputable def localImage (V : Y.Opens) : Submodule Γ(Y, V) Γ(G, V) where
  carrier := {s | ∃ m : Γ(N, V ⊓ U0), φ.app (V ⊓ U0) m = G.sectionRes inf_le_left s}
  zero_mem' := ⟨0, by simp⟩
  add_mem' := by
    rintro s t ⟨m, hm⟩ ⟨m', hm'⟩
    exact ⟨m + m', by rw [map_add, hm, hm', sectionRes_add]⟩
  smul_mem' := by
    rintro a s ⟨m, hm⟩
    exact ⟨resO Y inf_le_left a • m, by rw [Hom.app_smul, hm, sectionRes_smul]⟩

/-- The image submodule is stable under restriction. -/
theorem sectionRes_mem_localImage {V W : Y.Opens} (h : V ≤ W) {s : Γ(G, W)}
    (hs : s ∈ localImage φ U0 W) : G.sectionRes h s ∈ localImage φ U0 V := by
  obtain ⟨m, hm⟩ := hs
  refine ⟨N.sectionRes (inf_le_inf_right U0 h) m, ?_⟩
  rw [app_sectionRes, hm, sectionRes_res, sectionRes_res]

/-- Locality of membership in the image submodule, when `φ` is injective on all sections. -/
theorem mem_localImage_of_local (hinj : ∀ T : Y.Opens, Function.Injective (φ.app T)) {V : Y.Opens}
    (s : Γ(G, V))
    (hs : ∀ x ∈ V, ∃ (V' : Y.Opens) (h : V' ≤ V), x ∈ V' ∧ G.sectionRes h s ∈ localImage φ U0 V') :
    s ∈ localImage φ U0 V := by
  have hs' : ∀ x : V, ∃ (V' : Y.Opens) (h : V' ≤ V), (x : Y) ∈ V' ∧
      G.sectionRes h s ∈ localImage φ U0 V' := fun x => hs x x.2
  choose V' hV' hxV' hl using hs'
  choose m hm using hl
  let U : V → Y.Opens := fun x => V' x ⊓ U0
  have hUle : ∀ x, U x ≤ V ⊓ U0 := fun x => inf_le_inf_right U0 (hV' x)
  have hcomp : ∀ a b, N.sectionRes (inf_le_left : U a ⊓ U b ≤ U a) (m a) =
      N.sectionRes (inf_le_right : U a ⊓ U b ≤ U b) (m b) := by
    intro a b
    refine hinj _ ?_
    rw [app_sectionRes, app_sectionRes]
    change G.sectionRes _ (φ.app (V' a ⊓ U0) (m a)) = G.sectionRes _ (φ.app (V' b ⊓ U0) (m b))
    rw [hm a, hm b, sectionRes_res, sectionRes_res, sectionRes_res, sectionRes_res]
  have hcov : V ⊓ U0 ≤ ⨆ x, U x := by
    intro z hz
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨z, hz.1⟩, hxV' ⟨z, hz.1⟩, hz.2⟩
  obtain ⟨m0, hm0⟩ := Modules.exists_section_of_compatible N U hUle hcov m hcomp
  refine ⟨m0, Modules.eq_of_locally_eq G U hUle hcov fun x => ?_⟩
  rw [← app_sectionRes, hm0, hm x, sectionRes_res, sectionRes_res]

/-- The sub-`𝒪_Y`-module of `G` of the sections lying in the image of `φ` over `U0`. -/
noncomputable def localImageModule (hinj : ∀ T : Y.Opens, Function.Injective (φ.app T)) : Y.Modules :=
  Modules.ofSubmodule G (localImage φ U0) (fun h _ hs => sectionRes_mem_localImage φ U0 h hs)
    (fun _ s hs => mem_localImage_of_local φ U0 hinj s hs)

/-- The inclusion of `localImageModule` in `G` (a monomorphism). -/
noncomputable def localImageι (hinj : ∀ T : Y.Opens, Function.Injective (φ.app T)) :
    localImageModule φ U0 hinj ⟶ G :=
  Modules.ofSubmoduleι G (localImage φ U0) (fun h _ hs => sectionRes_mem_localImage φ U0 h hs)
    (fun _ s hs => mem_localImage_of_local φ U0 hinj s hs)

end LocalImage


/-! ### The local structure of `L` at a point -/

namespace PullbackDatum

variable (δ : PullbackDatum f i y) (U0 : Y.Opens)

/-- `e` is a section of `L` over `V'`: `e|_{V' ⊓ U0} = (f*i)((g|)⁻¹ f*d)` since `g` is a unit on `U0`. -/
theorem e_mem_localImage
    (hgU : ∀ (z : Y) (hz : z ∈ δ.V'), z ∈ U0 → IsUnit ((Y.presheaf.germ δ.V' z hz).hom δ.g)) :
    δ.e ∈ localImage ((Scheme.Modules.pullback f).map i) U0 δ.V' := by
  have hunit : IsUnit (resO Y (inf_le_left : δ.V' ⊓ U0 ≤ δ.V') δ.g) := by
    refine Y.toRingedSpace.isUnit_of_isUnit_germ _ _ fun z hz => ?_
    have := hgU z hz.1 hz.2
    rwa [← TopCat.Presheaf.germ_res_apply Y.presheaf (homOfLE (inf_le_left : δ.V' ⊓ U0 ≤ δ.V')) z hz] at this
  obtain ⟨β, hβ⟩ := hunit.exists_left_inv
  have hTV : δ.V' ⊓ U0 ≤ f ⁻¹ᵁ δ.V := inf_le_left.trans δ.le_V
  refine ⟨β • ((Scheme.Modules.pullback f).obj M).sectionRes hTV (pullbackSection f M δ.d), ?_⟩
  rw [Hom.app_smul, app_sectionRes]
  have h1 : ((Scheme.Modules.pullback f).obj F).sectionRes hTV
      (((Scheme.Modules.pullback f).map i).app (f ⁻¹ᵁ δ.V) (pullbackSection f M δ.d)) =
      ((Scheme.Modules.pullback f).obj F).sectionRes (inf_le_left : δ.V' ⊓ U0 ≤ δ.V')
        (((Scheme.Modules.pullback f).obj F).sectionRes δ.le_V
          (((Scheme.Modules.pullback f).map i).app (f ⁻¹ᵁ δ.V) (pullbackSection f M δ.d))) :=
    (sectionRes_res _ _ _ _).symm
  rw [h1, δ.sigma_eq, sectionRes_smul, ← mul_smul, hβ, one_smul]

/-- Every section of `L` over `T ≤ V'` is a multiple of `e`: the coordinates `h'_j` are unimodular, so the
multiplier is `∑ a_j s_j` where `s_j` are the coordinates of the section ("easily seen"). -/
theorem exists_smul_e_of_mem_localImage [IsIntegral Y]
    (hne : ∀ T : Y.Opens, Nonempty T → Nonempty (T ⊓ U0 : Y.Opens)) {T : Y.Opens} (hT : T ≤ δ.V')
    (s : Γ((Scheme.Modules.pullback f).obj F, T))
    (hs : s ∈ localImage ((Scheme.Modules.pullback f).map i) U0 T) :
    ∃ a : Γ(Y, T), a • ((Scheme.Modules.pullback f).obj F).sectionRes hT δ.e = s := by
  have hTU : T ≤ f ⁻¹ᵁ δ.U := hT.trans δ.le_U
  by_cases hTne : Nonempty T
  swap
  · have := subsingleton_sections_of_not_nonempty T hTne
    exact ⟨0, (isFrame_pullback f δ.hc).ext_coord hTU fun j => Subsingleton.elim _ _⟩
  obtain ⟨m, hm⟩ := hs
  have hT₂ne : Nonempty (T ⊓ U0 : Y.Opens) := hne T hTne
  have hT₂V' : T ⊓ U0 ≤ δ.V' := inf_le_left.trans hT
  have hT₂V : T ⊓ U0 ≤ f ⁻¹ᵁ δ.V := hT₂V'.trans δ.le_V
  obtain ⟨b, hb⟩ := ((isFrame_pullback f δ.hd).bijective (T ⊓ U0) hT₂V).2 m
  simp only [Finset.univ_unique, Finset.sum_singleton] at hb
  let B : Γ(Y, T ⊓ U0) := b PUnit.unit * resO Y hT₂V' δ.g
  -- the section on `T ⊓ U0`
  have hsB : ((Scheme.Modules.pullback f).obj F).sectionRes (inf_le_left : T ⊓ U0 ≤ T) s =
      B • ((Scheme.Modules.pullback f).obj F).sectionRes hT₂V' δ.e := by
    rw [← hm, ← hb, Hom.app_smul]
    have h0 : ((Scheme.Modules.pullback f).map i).app (T ⊓ U0)
        (((Scheme.Modules.pullback f).obj M).sectionRes hT₂V (pullbackSection f M δ.d)) =
        ((Scheme.Modules.pullback f).obj F).sectionRes hT₂V
          (((Scheme.Modules.pullback f).map i).app (f ⁻¹ᵁ δ.V) (pullbackSection f M δ.d)) :=
      app_sectionRes _ hT₂V _
    change b PUnit.unit • ((Scheme.Modules.pullback f).map i).app (T ⊓ U0)
      (((Scheme.Modules.pullback f).obj M).sectionRes hT₂V (pullbackSection f M δ.d)) = _
    rw [h0]
    have h1 : ((Scheme.Modules.pullback f).obj F).sectionRes hT₂V
        (((Scheme.Modules.pullback f).map i).app (f ⁻¹ᵁ δ.V) (pullbackSection f M δ.d)) =
        ((Scheme.Modules.pullback f).obj F).sectionRes hT₂V'
          (((Scheme.Modules.pullback f).obj F).sectionRes δ.le_V
            (((Scheme.Modules.pullback f).map i).app (f ⁻¹ᵁ δ.V) (pullbackSection f M δ.d))) :=
      (sectionRes_res _ _ _ _).symm
    rw [h1, δ.sigma_eq, sectionRes_smul, mul_smul]
  -- the coordinates
  let sc : δ.ι → Γ(Y, T) := fun j => (isFrame_pullback f δ.hc).coord hTU s j
  have hsc : ∀ j, resO Y (inf_le_left : T ⊓ U0 ≤ T) (sc j) = B * resO Y hT₂V' (δ.h' j) := by
    intro j
    have h1 := (isFrame_pullback f δ.hc).coord_sectionRes (inf_le_left : T ⊓ U0 ≤ T) hTU s j
    have h2 := congrArg (fun t => (isFrame_pullback f δ.hc).coord (hT₂V'.trans δ.le_U) t j) hsB
    rw [IsFrame.coord_smul, (isFrame_pullback f δ.hc).coord_sectionRes hT₂V' δ.le_U δ.e j, δ.coord_e] at h2
    exact h1.symm.trans h2
  -- the multiplier
  refine ⟨∑ j, resO Y hT (δ.a j) * sc j, ?_⟩
  refine (isFrame_pullback f δ.hc).ext_coord hTU fun k => ?_
  rw [IsFrame.coord_smul, (isFrame_pullback f δ.hc).coord_sectionRes hT δ.le_U δ.e k, δ.coord_e]
  refine (Scheme.germToFunctionField_injective Y T ?_).symm
  have hV'ne : Nonempty δ.V' := ⟨⟨y, δ.hyV'⟩⟩
  let κ : Y.functionField := Y.germToFunctionField (T ⊓ U0) B
  have hK1 : ∀ j, Y.germToFunctionField T (sc j) = κ * Y.germToFunctionField δ.V' (δ.h' j) := by
    intro j
    rw [← germToFunctionField_resO (inf_le_left : T ⊓ U0 ≤ T) (sc j), hsc j, map_mul,
      germToFunctionField_resO hT₂V' (δ.h' j)]
  have hsum : ∑ j, Y.germToFunctionField δ.V' (δ.a j) * Y.germToFunctionField δ.V' (δ.h' j) = 1 := by
    have := congrArg (Y.germToFunctionField δ.V') δ.ha
    rw [map_sum, map_one] at this
    simpa only [map_mul] using this
  rw [map_mul, map_sum, germToFunctionField_resO hT (δ.h' k)]
  simp only [map_mul, germToFunctionField_resO hT (δ.a _), hK1]
  have : ∑ j, Y.germToFunctionField δ.V' (δ.a j) * (κ * Y.germToFunctionField δ.V' (δ.h' j)) =
      κ := by
    calc _ = κ * ∑ j, Y.germToFunctionField δ.V' (δ.a j) * Y.germToFunctionField δ.V' (δ.h' j) := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun j _ => by ring
      _ = κ := by rw [hsum, mul_one]
  rw [this, hK1 k]

/-- `e` is not a zero divisor: its coordinates `h'_j` are unimodular. -/
theorem eq_zero_of_smul_e {T : Y.Opens} (hT : T ≤ δ.V') (a : Γ(Y, T))
    (h : a • ((Scheme.Modules.pullback f).obj F).sectionRes hT δ.e = 0) : a = 0 := by
  have hTU : T ≤ f ⁻¹ᵁ δ.U := hT.trans δ.le_U
  have hco : ∀ j, a * resO Y hT (δ.h' j) = 0 := fun j => by
    have := congrArg (fun t => (isFrame_pullback f δ.hc).coord hTU t j) h
    simp only [IsFrame.coord_smul, IsFrame.coord_zero] at this
    rwa [(isFrame_pullback f δ.hc).coord_sectionRes hT δ.le_U δ.e j, δ.coord_e] at this
  calc a = a * resO Y hT (∑ j, δ.a j * δ.h' j) := by rw [δ.ha, resO_one, mul_one]
    _ = ∑ j, resO Y hT (δ.a j) * (a * resO Y hT (δ.h' j)) := by
      rw [resO_sum, Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by rw [resO_mul]; ring
    _ = 0 := by simp [hco]

/-- Where `J` is the unit ideal at `f z`, the generator `g` is a unit at `z` (the ideal `f⁻¹(J)_z` is generated by the
`g h'_j`). -/
theorem isUnit_germ_g [IsLocallyNoetherian X] (hF : HasLocalFrames F) (hM : IsInvertible M) {z : Y}
    (hz : z ∈ δ.V') (hJ : (coordSubscheme i hF hM).stalkIdeal (f z) = ⊤) :
    IsUnit ((Y.presheaf.germ δ.V' z hz).hom δ.g) := by
  have hzW : f z ∈ δ.W := δ.hV'W hz
  rw [stalkIdeal_coordSubscheme_eq_span i hF hM δ.hc δ.hd δ.hWV δ.hWU hzW] at hJ
  have h1 := congrArg (Ideal.map (f.stalkMap z).hom) hJ
  rw [Ideal.map_top, Ideal.map_span, ← Set.range_comp] at h1
  have h2 : Ideal.span (Set.range ((f.stalkMap z).hom ∘ fun j =>
      (X.presheaf.germ δ.W (f z) hzW).hom (δ.hc.coord δ.hWU (i.app δ.W (M.sectionRes δ.hWV δ.d)) j))) ≤
      Ideal.span {(Y.presheaf.germ δ.V' z hz).hom δ.g} := by
    refine Ideal.span_le.mpr ?_
    rintro _ ⟨j, rfl⟩
    have e1 : ((f.stalkMap z).hom ∘ fun j =>
        (X.presheaf.germ δ.W (f z) hzW).hom (δ.hc.coord δ.hWU (i.app δ.W (M.sectionRes δ.hWV δ.d)) j)) j =
        (Y.presheaf.germ δ.V' z hz).hom (δ.g * δ.h' j) := by
      rw [← δ.hg j]
      exact (Scheme.Hom.germ_stalkMap_apply f δ.W z hzW _).trans
        (TopCat.Presheaf.germ_res_apply Y.presheaf (homOfLE δ.hV'W) z hz _).symm
    rw [e1, map_mul]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)
  rw [h1] at h2
  exact Ideal.span_singleton_eq_top.mp (top_le_iff.mp h2)

/-- **The local frames at `y`**: near `y` the pull-back `f*F` has a frame whose `j₀`-th vector is the
generator `e` of `L`, and `L` has the one-element frame `e`. -/
theorem exists_frames [IsIntegral Y]
    (hne : ∀ T : Y.Opens, Nonempty T → Nonempty (T ⊓ U0 : Y.Opens))
    (hgU : ∀ (z : Y) (hz : z ∈ δ.V'), z ∈ U0 → IsUnit ((Y.presheaf.germ δ.V' z hz).hom δ.g))
    (hinj : ∀ T : Y.Opens, Function.Injective (((Scheme.Modules.pullback f).map i).app T)) :
    ∃ (V₀ : Y.Opens) (_ : y ∈ V₀) (c' : δ.ι → Γ((Scheme.Modules.pullback f).obj F, V₀)) (j₀ : δ.ι)
      (ε : Γ(localImageModule ((Scheme.Modules.pullback f).map i) U0 hinj, V₀)),
      IsFrame ((Scheme.Modules.pullback f).obj F) V₀ c' ∧
      IsFrame (localImageModule ((Scheme.Modules.pullback f).map i) U0 hinj) V₀
        (fun _ : PUnit.{u + 1} => ε) ∧
      (localImageι ((Scheme.Modules.pullback f).map i) U0 hinj).app V₀ ε = c' j₀ := by
  classical
  -- some `h'_{j₀}` is a unit at `y`
  obtain ⟨j₀, hj₀⟩ : ∃ j₀, IsUnit ((Y.presheaf.germ δ.V' y δ.hyV').hom (δ.h' j₀)) := by
    by_contra hcon
    push Not at hcon
    have h1 := congrArg (Y.presheaf.germ δ.V' y δ.hyV').hom δ.ha
    rw [map_sum, map_one] at h1
    have h2 : (1 : Y.presheaf.stalk y) ∈ IsLocalRing.maximalIdeal (Y.presheaf.stalk y) := by
      rw [← h1]
      refine Ideal.sum_mem _ fun j _ => ?_
      rw [map_mul]
      exact Ideal.mul_mem_left _ _ (hcon j)
    exact (IsLocalRing.maximalIdeal.isMaximal _).ne_top ((Ideal.eq_top_iff_one _).mpr h2)
  let V₀ : Y.Opens := Y.basicOpen (δ.h' j₀)
  have hV₀V' : V₀ ≤ δ.V' := Y.basicOpen_le _
  have hyV₀ : y ∈ V₀ := (Y.mem_basicOpen _ y δ.hyV').mpr hj₀
  have hV₀U : V₀ ≤ f ⁻¹ᵁ δ.U := hV₀V'.trans δ.le_U
  have hunit : IsUnit (resO Y hV₀V' (δ.h' j₀)) := Y.toRingedSpace.isUnit_res_basicOpen _
  have hrep := (isFrame_pullback f δ.hc).replace hV₀U (fun k => resO Y hV₀V' (δ.h' k)) j₀ hunit
  have hed : ((Scheme.Modules.pullback f).obj F).sectionRes hV₀V' δ.e =
      ∑ k, resO Y hV₀V' (δ.h' k) • ((Scheme.Modules.pullback f).obj F).sectionRes hV₀U
        (pullbackSection f F (δ.c k)) := by
    unfold e
    rw [sectionRes_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [sectionRes_smul, sectionRes_res]
  have hemem : ((Scheme.Modules.pullback f).obj F).sectionRes hV₀V' δ.e ∈
      localImage ((Scheme.Modules.pullback f).map i) U0 V₀ :=
    sectionRes_mem_localImage _ U0 hV₀V' (δ.e_mem_localImage U0 hgU)
  refine ⟨V₀, hyV₀, _, j₀,
    (⟨_, hemem⟩ : Γ(localImageModule ((Scheme.Modules.pullback f).map i) U0 hinj, V₀)), hrep,
    Modules.isFrame_ofSubmodule_singleton _ _ _ _ _ hemem
      (fun T hT a ha => δ.eq_zero_of_smul_e (hT.trans hV₀V') a (by
        rw [sectionRes_res] at ha
        exact ha))
      (fun T hT s hs => ?_), ?_⟩
  · obtain ⟨a, ha⟩ := δ.exists_smul_e_of_mem_localImage U0 hne (hT.trans hV₀V') s hs
    exact ⟨a, by rwa [sectionRes_res]⟩
  · show _ = if j₀ = j₀ then _ else _
    rw [show (j₀ = j₀) = True from eq_self j₀, ite_true, ← hed]
    rfl

end PullbackDatum


/-! ### The open set where `J` is trivial, and `f⁻¹` of it -/

/-- The open set of the points where the sheaf of ideals `D` is trivial (the complement of its support). -/
def trivialLocus (D : Subscheme X) : X.Opens :=
  ⟨(D.pts)ᶜ, D.support.isClosed.isOpen_compl⟩

/-- A point lies in the trivial locus iff the stalk of the ideal sheaf is the unit ideal. -/
theorem mem_trivialLocus_iff (D : Subscheme X) (x : X) : x ∈ trivialLocus D ↔ D.stalkIdeal x = ⊤ := by
  show x ∈ (D.pts)ᶜ ↔ _
  rw [Set.mem_compl_iff, Subscheme.mem_pts_iff_stalkIdeal_ne_top, not_not]

/-- The generic point of an integral `Y` maps into the trivial locus of `J` when `f⁻¹(J)` is invertible (a
principal ideal generated by a non-zero-divisor of a field is the unit ideal, and `J_{f η}` is proper only if its
image in `𝒪_{Y,η}` is). -/
theorem genericPoint_mem_preimage_trivialLocus [IsIntegral Y] (J : Subscheme X) (f : Y ⟶ X)
    (hinv : (Subscheme.totalTransform f J).IsInvertibleIdeal) :
    genericPoint Y ∈ f ⁻¹ᵁ trivialLocus J := by
  show f (genericPoint Y) ∈ trivialLocus J
  rw [mem_trivialLocus_iff]
  obtain ⟨g0, hg0, hnzd⟩ := hinv.exists_stalkIdeal_eq_span (genericPoint Y)
  have hfield : IsField (Y.presheaf.stalk (genericPoint Y)) := Field.toIsField _
  have hg00 : g0 ≠ 0 := nonZeroDivisors.ne_zero hnzd
  obtain ⟨b, hb⟩ := hfield.mul_inv_cancel hg00
  have htop : (Subscheme.totalTransform f J).stalkIdeal (genericPoint Y) = ⊤ := by
    rw [hg0]
    exact Ideal.span_singleton_eq_top.mpr (IsUnit.of_mul_eq_one b hb)
  change Subscheme.stalkIdeal (J.comap f) (genericPoint Y) = ⊤ at htop
  rw [Subscheme.stalkIdeal_comap] at htop
  by_contra hne
  have hle : J.stalkIdeal (f (genericPoint Y)) ≤ IsLocalRing.maximalIdeal _ :=
    IsLocalRing.le_maximalIdeal hne
  have : Ideal.map (f.stalkMap (genericPoint Y)).hom (J.stalkIdeal (f (genericPoint Y))) ≤
      IsLocalRing.maximalIdeal _ := by
    rw [Ideal.map_le_iff_le_comap]
    intro a ha
    rw [Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    exact (IsLocalRing.mem_maximalIdeal _).mp (hle ha) (IsLocalHom.map_nonunit a hu)
  rw [htop] at this
  exact (IsLocalRing.maximalIdeal.isMaximal _).ne_top (top_le_iff.mp this)

end Hironaka
