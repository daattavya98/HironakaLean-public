/-
Copyright (c) 2026 Daattavya Aggarwal, Minhyong Kim, Oisin Kim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daattavya Aggarwal, Minhyong Kim, Oisin Kim
-/
module

public import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing
public import Hironaka.Compat.PullbackFrames

/-!
# Coordinates in a frame (Compat API for Corollary 2 of Main Theorem II)

Hironaka, Ch. 0, Corollary 2 of Main Theorem II (p. 145) works with "a free base `(c_1, …, c_r)` of the
`O_{X,x}`-module `F_x`" and writes sections as combinations `d = ∑ h_j c_j`.  For a frame `c` of an
`𝒪_X`-module `M` over an open `U` (`Hironaka.Scheme.Modules.IsFrame`, `Hironaka/Compat/ModuleFrames.lean`)
this module defines the restriction maps and the coordinates:

* `Hironaka.Scheme.Modules.res`: the restriction `Γ(M, W) → Γ(M, V)` along `V ≤ W`, with its simp lemmas;
* `Hironaka.Scheme.Modules.IsFrame.linearEquiv`, `IsFrame.coord`: for `V ≤ U` the coordinate map
  `Γ(M, V) → (ι → Γ(X, V))` is a linear isomorphism, inverse to `a ↦ ∑ aᵢ • cᵢ|_V`, compatible with restriction
  (`IsFrame.coord_res`);
* `Hironaka.Scheme.Modules.eq_of_locally_eq`, `exists_section_of_compatible`: separation of the sheaf `M`
  and gluing of sections of `𝒪_X`.

This is infrastructure (no statement of the paper); it is not a deviation.
-/

@[expose] public section

open CategoryTheory Limits Opposite AlgebraicGeometry TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme

variable {X : Scheme.{u}}

/-- The restriction `Γ(M, W) → Γ(M, V)` of a section of an `𝒪_X`-module along `V ≤ W`. -/
noncomputable def Modules.sectionRes (M : X.Modules) {V W : X.Opens} (h : V ≤ W) (s : Γ(M, W)) : Γ(M, V) :=
  M.presheaf.map (homOfLE h).op s

/-- The restriction `Γ(X, W) → Γ(X, V)` of a function along `V ≤ W`. -/
noncomputable def resO (X : Scheme.{u}) {V W : X.Opens} (h : V ≤ W) (a : Γ(X, W)) : Γ(X, V) :=
  X.presheaf.map (homOfLE h).op a

/-- Restriction of sections is additive. -/
@[simp] theorem Modules.sectionRes_add (M : X.Modules) {V W : X.Opens} (h : V ≤ W) (s t : Γ(M, W)) :
    M.sectionRes h (s + t) = M.sectionRes h s + M.sectionRes h t := map_add _ _ _

/-- Restriction of sections preserves zero. -/
@[simp] theorem Modules.sectionRes_zero (M : X.Modules) {V W : X.Opens} (h : V ≤ W) :
    M.sectionRes h (0 : Γ(M, W)) = 0 := map_zero _

/-- Restriction of sections is semilinear over the restriction of functions. -/
@[simp] theorem Modules.sectionRes_smul (M : X.Modules) {V W : X.Opens} (h : V ≤ W) (a : Γ(X, W)) (s : Γ(M, W)) :
    M.sectionRes h (a • s) = resO X h a • M.sectionRes h s :=
  Modules.map_smul M (homOfLE h) a s

/-- Restriction of sections commutes with finite sums. -/
theorem Modules.sectionRes_sum (M : X.Modules) {V W : X.Opens} (h : V ≤ W) {ι : Type*} (t : Finset ι)
    (s : ι → Γ(M, W)) : M.sectionRes h (∑ i ∈ t, s i) = ∑ i ∈ t, M.sectionRes h (s i) := map_sum _ _ _

/-- Two successive restrictions of sections are one restriction. -/
theorem Modules.sectionRes_res (M : X.Modules) {V W T : X.Opens} (h : V ≤ W) (h' : W ≤ T) (s : Γ(M, T)) :
    M.sectionRes h (M.sectionRes h' s) = M.sectionRes (h.trans h') s :=
  Hironaka.Scheme.Modules.map_map_apply M (homOfLE h) (homOfLE h') s

/-- Restriction along `V ≤ V` is the identity. -/
@[simp] theorem Modules.sectionRes_self (M : X.Modules) {V : X.Opens} (s : Γ(M, V)) : M.sectionRes le_rfl s = s := by
  have : M.presheaf.map (homOfLE (le_refl V)).op s = M.presheaf.map (𝟙 (op V)) s := rfl
  exact this.trans (by rw [M.presheaf.map_id]; rfl)

/-- Restriction of functions along `V ≤ V` is the identity. -/
@[simp] theorem resO_self (X : Scheme.{u}) {V : X.Opens} (a : Γ(X, V)) : resO X le_rfl a = a := by
  have : X.presheaf.map (homOfLE (le_refl V)).op a = X.presheaf.map (𝟙 (op V)) a := rfl
  exact this.trans (by rw [X.presheaf.map_id]; rfl)

/-- Restriction of functions is multiplicative. -/
theorem resO_mul (X : Scheme.{u}) {V W : X.Opens} (h : V ≤ W) (a b : Γ(X, W)) :
    resO X h (a * b) = resO X h a * resO X h b := map_mul _ _ _

/-- Restriction of functions is additive. -/
theorem resO_add (X : Scheme.{u}) {V W : X.Opens} (h : V ≤ W) (a b : Γ(X, W)) :
    resO X h (a + b) = resO X h a + resO X h b := map_add _ _ _

/-- Restriction of functions preserves `1`. -/
@[simp] theorem resO_one (X : Scheme.{u}) {V W : X.Opens} (h : V ≤ W) : resO X h (1 : Γ(X, W)) = 1 :=
  map_one _

/-- Two successive restrictions of functions are one restriction. -/
theorem resO_resO (X : Scheme.{u}) {V W T : X.Opens} (h : V ≤ W) (h' : W ≤ T) (a : Γ(X, T)) :
    resO X h (resO X h' a) = resO X (h.trans h') a := by
  unfold resO
  rw [← ConcreteCategory.comp_apply, ← X.presheaf.map_comp]
  rfl

/-- Separation: two sections of an `𝒪_X`-module which agree on an open cover are equal. -/
theorem Modules.eq_of_locally_eq (M : X.Modules) {V : X.Opens} {ι : Type*} (U : ι → X.Opens)
    (hU : ∀ i, U i ≤ V) (hcov : V ≤ ⨆ i, U i) {s t : Γ(M, V)}
    (h : ∀ i, M.sectionRes (hU i) s = M.sectionRes (hU i) t) : s = t :=
  TopCat.Sheaf.eq_of_locally_eq' (F := ⟨M.presheaf, M.isSheaf⟩) U V (fun i => homOfLE (hU i)) hcov
    s t h

/-- Gluing of sections of an `𝒪_X`-module: a compatible family of sections over an open cover of `V` comes from
a section over `V`. -/
theorem Modules.exists_section_of_compatible (M : X.Modules) {V : X.Opens} {ι : Type*}
    (U : ι → X.Opens) (hU : ∀ i, U i ≤ V) (hcov : V ≤ ⨆ i, U i) (t : ∀ i, Γ(M, U i))
    (hcomp : ∀ i j, M.sectionRes (inf_le_left : U i ⊓ U j ≤ U i) (t i) =
      M.sectionRes (inf_le_right : U i ⊓ U j ≤ U j) (t j)) :
    ∃ a : Γ(M, V), ∀ i, M.sectionRes (hU i) a = t i := by
  obtain ⟨a, ha, -⟩ := TopCat.Sheaf.existsUnique_gluing' (⟨M.presheaf, M.isSheaf⟩ : TopCat.Sheaf Ab X) U V
    (fun i => homOfLE (hU i)) hcov t hcomp
  exact ⟨a, ha⟩

/-- Gluing of functions: a compatible family of sections of `𝒪_X` over an open cover of `V` comes from a
section over `V`. -/
theorem exists_section_of_compatible (X : Scheme.{u}) {V : X.Opens} {ι : Type*} (U : ι → X.Opens)
    (hU : ∀ i, U i ≤ V) (hcov : V ≤ ⨆ i, U i) (t : ∀ i, Γ(X, U i))
    (hcomp : ∀ i j, resO X (inf_le_left : U i ⊓ U j ≤ U i) (t i) =
      resO X (inf_le_right : U i ⊓ U j ≤ U j) (t j)) :
    ∃ a : Γ(X, V), ∀ i, resO X (hU i) a = t i := by
  obtain ⟨a, ha, -⟩ := TopCat.Sheaf.existsUnique_gluing' X.sheaf U V (fun i => homOfLE (hU i)) hcov t
    hcomp
  exact ⟨a, ha⟩

end AlgebraicGeometry.Scheme

namespace Hironaka

namespace Scheme.Modules

open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}} {M : X.Modules} {U : X.Opens} {ι : Type u} [Fintype ι]

/-- The linear combination map `(aᵢ) ↦ ∑ aᵢ • cᵢ|_V` of a family of sections over `U`, for `V ≤ U`. -/
noncomputable def frameCombo (c : ι → Γ(M, U)) {V : X.Opens} (h : V ≤ U) :
    (ι → Γ(X, V)) →ₗ[Γ(X, V)] Γ(M, V) where
  toFun a := ∑ i, a i • M.sectionRes h (c i)
  map_add' a b := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' r a := by simp [Finset.smul_sum, mul_smul]

/-- The value of `frameCombo` on a coefficient vector. -/
theorem frameCombo_apply (c : ι → Γ(M, U)) {V : X.Opens} (h : V ≤ U) (a : ι → Γ(X, V)) :
    frameCombo c h a = ∑ i, a i • M.sectionRes h (c i) := rfl

variable {c : ι → Γ(M, U)}

/-- For a frame, the combination map over `V ≤ U` is a linear isomorphism. -/
noncomputable def IsFrame.linearEquiv (hc : IsFrame M U c) {V : X.Opens} (h : V ≤ U) :
    (ι → Γ(X, V)) ≃ₗ[Γ(X, V)] Γ(M, V) :=
  LinearEquiv.ofBijective (frameCombo c h) (hc.bijective V h)

/-- The `i`-th coordinate in the frame `c` of a section over `V ≤ U`. -/
noncomputable def IsFrame.coord (hc : IsFrame M U c) {V : X.Opens} (h : V ≤ U) (s : Γ(M, V))
    (i : ι) : Γ(X, V) :=
  (hc.linearEquiv h).symm s i

/-- A section is the combination of its coordinates. -/
theorem IsFrame.sum_coord_smul (hc : IsFrame M U c) {V : X.Opens} (h : V ≤ U) (s : Γ(M, V)) :
    ∑ i, hc.coord h s i • M.sectionRes h (c i) = s :=
  (hc.linearEquiv h).apply_symm_apply s

/-- The coordinates of a combination are its coefficients. -/
theorem IsFrame.coord_eq (hc : IsFrame M U c) {V : X.Opens} (h : V ≤ U) (s : Γ(M, V))
    (a : ι → Γ(X, V)) (hs : ∑ i, a i • M.sectionRes h (c i) = s) (i : ι) :
    hc.coord h s i = a i := by
  have : (hc.linearEquiv h).symm s = a := by
    rw [LinearEquiv.symm_apply_eq]
    exact hs.symm
  exact congrFun this i

/-- Two sections with the same coordinates are equal. -/
theorem IsFrame.ext_coord (hc : IsFrame M U c) {V : X.Opens} (h : V ≤ U) {s t : Γ(M, V)}
    (hst : ∀ i, hc.coord h s i = hc.coord h t i) : s = t := by
  rw [← hc.sum_coord_smul h s, ← hc.sum_coord_smul h t]
  exact Finset.sum_congr rfl fun i _ => by rw [hst i]

/-- Coordinates are additive. -/
theorem IsFrame.coord_add (hc : IsFrame M U c) {V : X.Opens} (h : V ≤ U) (s t : Γ(M, V)) (i : ι) :
    hc.coord h (s + t) i = hc.coord h s i + hc.coord h t i :=
  congrFun (map_add (hc.linearEquiv h).symm s t) i

/-- Coordinates are linear over `Γ(X, V)`. -/
theorem IsFrame.coord_smul (hc : IsFrame M U c) {V : X.Opens} (h : V ≤ U) (a : Γ(X, V))
    (s : Γ(M, V)) (i : ι) : hc.coord h (a • s) i = a * hc.coord h s i :=
  congrFun (map_smul (hc.linearEquiv h).symm a s) i

/-- Coordinates commute with finite sums. -/
theorem IsFrame.coord_sum (hc : IsFrame M U c) {V : X.Opens} (h : V ≤ U) {κ : Type*} (t : Finset κ)
    (s : κ → Γ(M, V)) (i : ι) : hc.coord h (∑ k ∈ t, s k) i = ∑ k ∈ t, hc.coord h (s k) i := by
  have := congrFun (map_sum (hc.linearEquiv h).symm s t) i
  refine this.trans ?_
  simp [IsFrame.coord]

/-- The coordinates of `0` vanish. -/
theorem IsFrame.coord_zero (hc : IsFrame M U c) {V : X.Opens} (h : V ≤ U) (i : ι) :
    hc.coord h 0 i = 0 :=
  congrFun (map_zero (hc.linearEquiv h).symm) i

/-- The coordinates are compatible with restriction. -/
theorem IsFrame.coord_sectionRes (hc : IsFrame M U c) {V V' : X.Opens} (h' : V' ≤ V) (h : V ≤ U)
    (s : Γ(M, V)) (i : ι) :
    hc.coord (h'.trans h) (M.sectionRes h' s) i = resO X h' (hc.coord h s i) := by
  refine hc.coord_eq (h'.trans h) _ (fun j => resO X h' (hc.coord h s j)) ?_ i
  conv_rhs => rw [← hc.sum_coord_smul h s]
  rw [Modules.sectionRes_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Modules.sectionRes_smul, Modules.sectionRes_res]

/-- The coordinates of a frame vector. -/
theorem IsFrame.coord_sectionRes_self [DecidableEq ι] (hc : IsFrame M U c) {V : X.Opens}
    (h : V ≤ U) (j i : ι) :
    hc.coord h (M.sectionRes h (c j)) i = if i = j then 1 else 0 := by
  have := hc.coord_eq h (M.sectionRes h (c j)) (Pi.single j 1) ?_ i
  · rw [this, Pi.single_apply]
  · rw [Finset.sum_eq_single j]
    · simp
    · intro b _ hb
      simp [hb]
    · simp

end Scheme.Modules

end Hironaka
