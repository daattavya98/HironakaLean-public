/-
Copyright (c) 2026 Daattavya Aggarwal, Minhyong Kim, Oisin Kim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daattavya Aggarwal, Minhyong Kim, Oisin Kim
-/
module

public import Mathlib.RingTheory.MvPowerSeries.Inverse
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Hironaka.Compat.WeierstrassDatum
public import Hironaka.Compat.TauZSystem
public import Hironaka.Compat.TauZSingleton
public import Hironaka.Compat.TauZBaseChange
public import Hironaka.Compat.CompleteRationalFrameBaseChange
public import Hironaka.Statements

/-!
# Base change of the data of the reformulation of Lemma 25 (pp. 270--271)

The proof of Lemma 25 reduces (ii) of (c) "as in the proof of Lemma 22" to the case in which the
residue field `k` of `S₀` is algebraically closed, "so that `R₁` is residually rational over `R`"
(p. 271), and, "as in Lemma 20", to `S` and `R` complete.  The paper does not carry this reduction
out.  This file contains the transfers of the data along the base changes `S₀ → S̃₀`,
`S → S̃ = S̃₀⟦w⟧`, `R → R̃ = S̃⟦z⟧` that it needs:

* `WeierstrassDatum.baseChange`: the datum `(S̃; z)`, `(S̃₀; w)` of `R̃`;
* `WeierstrassDatum.hasShape_baseChange`: the shape (4) of `f` passes to `α(f)`;
* `WeierstrassDatum.inTauStar_baseChange`: the condition (3) passes to `α(f)`
  (`grMapMax_mem_tauZSubmoduleStar`: `ᾱ` maps `T*` into `T*`);
* `tauZ_congr_of_associated`: `τ_{(z)}(f)` only depends on the `z_j` and `f` up to units (the
  frame transform of the hypothesis and the one with denominator `y` differ by a unit);
* `WeierstrassDatum.one_le_tauZ`: `τ_{(z)}(f) ≥ 1` when `w` lies in `T*`.
-/

@[expose] public section

open IsLocalRing

namespace Hironaka

universe u

section GrStar

variable {A B : Type u} [CommRing A] [IsRegularLocalRing A] [CommRing B] [IsRegularLocalRing B]

/-- `ᾱ` maps `T*` for `(z; f)` into `T*` for `(α z; α f)`. -/
theorem grMapMax_mem_tauZSubmoduleStar [Hironaka.HironakaCitedResults.{u}] (α : A →+* B) [IsLocalHom α] (hα : RingHom.MapsRSOP α)
    (hsep : RingHom.IsResiduallySeparable α) {r i : ℕ} (z : Fin r → A) (f : Fin i → A)
    {x : AssocGraded (maximalIdeal A)} (hx : x ∈ tauZSubmoduleStar A z f) :
    grMapMax α hα x ∈ tauZSubmoduleStar B (fun j => α (z j)) (fun j => α (f j)) := by
  classical
  obtain ⟨t, ht, w, hw, rfl⟩ := Submodule.mem_sup.mp hx
  rw [map_add]
  refine Submodule.add_mem_sup ?_ ?_
  · rw [tauZSubmodule_map α hα hsep f]
    exact Submodule.subset_span ⟨t, ht, rfl⟩
  · have := grMapMax_mem_span_image α hα _ hw
    refine (Submodule.span_le.mpr ?_) this
    rintro _ ⟨_, ⟨j, rfl⟩, rfl⟩
    exact Submodule.subset_span ⟨j, initialForm_map_of_mapsRSOP α hα (z j)⟩


end GrStar

section Helpers

variable {A : Type u} [CommRing A] [IsRegularLocalRing A]

omit [IsRegularLocalRing A] in
/-- `x · [u] = ū • x` for the class `[u]` of a unit (a degree-`0` element) of `gr_M(A)`. -/
theorem mul_algebraMap_eq_smul (I : Ideal A) (x : AssocGraded I) (a : A) :
    x * algebraMap A (AssocGraded I) a = Ideal.Quotient.mk I a • x := by
  rw [IsScalarTower.algebraMap_apply A (A ⧸ I) (AssocGraded I), Algebra.smul_def, mul_comm]
  rfl

open Classical in
/-- `T` of Definition 10* for a single element does not change when the element is multiplied
by a unit. -/
theorem isTauZSubmodule_mul_unit (f : A) (u : Aˣ)
    (T : Submodule (A ⧸ maximalIdeal A) (AssocGraded (maximalIdeal A))) :
    IsTauZSubmodule A (fun _ : Fin 1 => f * u) T ↔ IsTauZSubmodule A (fun _ : Fin 1 => f) T := by
  rw [isTauZSubmodule_singleton_iff, isTauZSubmodule_singleton_iff, initialForm_mul_unit,
    mul_algebraMap_eq_smul]
  refine and_congr_right fun _ => ⟨fun h => ?_, fun h => Subalgebra.smul_mem _ h _⟩
  have := Subalgebra.smul_mem _ h (Ideal.Quotient.mk (maximalIdeal A) ((u⁻¹ : Aˣ) : A))
  rwa [smul_smul, ← map_mul, Units.inv_mul, map_one, one_smul] at this

/-- `T` is unchanged under multiplication of the element by a unit. -/
theorem tauZSubmodule_mul_unit (f : A) (u : Aˣ) :
    tauZSubmodule A (fun _ : Fin 1 => f * u) = tauZSubmodule A (fun _ : Fin 1 => f) := by
  unfold tauZSubmodule
  congr 1
  ext T
  exact isTauZSubmodule_mul_unit f u T

/-- The span of the `Z_j` does not change when the `z_j` are multiplied by units. -/
theorem span_frameForm_mul_unit_le {r : ℕ} (z : Fin r → A) (u : Fin r → Aˣ) :
    Submodule.span (A ⧸ maximalIdeal A) (Set.range (frameForm fun j => z j * u j)) ≤
      Submodule.span (A ⧸ maximalIdeal A) (Set.range (frameForm z)) := by
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨j, rfl⟩
  show initialForm (maximalIdeal A) (z j * u j) ∈ _
  rw [initialForm_mul_unit, mul_algebraMap_eq_smul]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)

/-- **`τ_{(z)}(f)` only depends on the `z_j` and on `f` up to units.** -/
theorem tauZ_congr_of_associated {r : ℕ} (z z' : Fin r → A) (f f' : A)
    (hz : ∀ j, Associated (z j) (z' j)) (hf : Associated f f') :
    tauZ A z (fun _ : Fin 1 => f) = tauZ A z' (fun _ : Fin 1 => f') := by
  choose u hu using hz
  obtain ⟨v, hv⟩ := hf
  have hz' : z' = fun j => z j * u j := funext fun j => (hu j).symm
  have hspan : Submodule.span (A ⧸ maximalIdeal A) (Set.range (frameForm z')) =
      Submodule.span (A ⧸ maximalIdeal A) (Set.range (frameForm z)) := by
    refine le_antisymm ?_ ?_
    · rw [hz']
      exact span_frameForm_mul_unit_le z u
    · have := span_frameForm_mul_unit_le z' (fun j => (u j)⁻¹)
      have hzz : (fun j => z' j * ((u j)⁻¹ : Aˣ)) = z := funext fun j => by
        rw [← hu j, mul_assoc, Units.mul_inv, mul_one]
      rw [hzz] at this
      exact this
  unfold tauZ tauZSubmoduleStar
  rw [hspan, ← hv, tauZSubmodule_mul_unit]


end Helpers

section DatumBaseChange

variable {R : Type u} [CommRing R] [IsRegularLocalRing R] (D : WeierstrassDatum R)
  (S0 : Type u) [CommRing S0] [IsRegularLocalRing S0]

/-- The datum of the reformulation of Lemma 25 after the base changes `S₀ → S̃₀`, `S → S̃ = S̃₀⟦w⟧`,
`R → R̃ = S̃⟦z⟧` (p. 271: "the proof of (ii) of (c) can be reduced to the case in which the residue
field `k` of `S₀` is algebraically closed"; pp. 254, 266: `R̃ = S̃{z₁, …, z_r}`). -/
noncomputable def WeierstrassDatum.baseChange :
    WeierstrassDatum (MvPowerSeries (Fin D.F.r) (MvPowerSeries (Fin D.F0.r) S0)) where
  F := D.F.baseChange (MvPowerSeries (Fin D.F0.r) S0)
  F0 := D.F0.baseChange S0
  rank_eq_one := D.rank_eq_one

variable {S0}
variable (a₀ : D.F0.S →+* S0) [IsLocalHom a₀]

omit [IsLocalHom a₀] in
/-- The image of `w` in `R̃` is the `w` of the base changed datum. -/
theorem WeierstrassDatum.baseChangeHom_wR :
    D.F.baseChangeHom (D.F0.baseChangeHom a₀) D.wR = (D.baseChange S0).wR := by
  show D.F.baseChangeHom (D.F0.baseChangeHom a₀) (algebraMap D.F.S R D.w) = _
  have hw : D.F0.baseChangeHom a₀ D.w = (D.baseChange S0).w := D.F0.baseChangeHom_z a₀ _
  rw [D.F.baseChangeHom_algebraMap, hw]
  rfl

open Classical in
/-- **The shape (4) is preserved by the base change** (p. 271: the reduction to an algebraically
closed residue field "as in the proof of Lemma 22"; the paper does not check it): the expansion
coefficients of `f` over `S` map to those of `α(f)` over `S̃` (`expCoeff_baseChangeHom`), `u ↦ ã u`,
`w ↦ w`, `p_j ↦ a₀ p_j`, and the order is unchanged (`ordElem_map_of_mapsRSOP`). -/
theorem WeierstrassDatum.hasShape_baseChange (ha₀ : RingHom.MapsRSOP a₀) {f : R}
    (h : D.HasShape f) :
    (D.baseChange S0).HasShape (D.F.baseChangeHom (D.F0.baseChangeHom a₀) f) := by
  obtain ⟨A, e, u, p, hu, he, hdeg, hcoef⟩ := h
  have hα := D.F.mapsRSOP_baseChangeHom (D.F0.baseChangeHom a₀)
    (D.F0.mapsRSOP_baseChangeHom a₀ ha₀)
  have hw : D.F0.baseChangeHom a₀ D.w = (D.baseChange S0).w := D.F0.baseChangeHom_z a₀ _
  refine ⟨A, e, D.F0.baseChangeHom a₀ u, fun j => a₀ (p j), hu.map _, he, ?_, ?_⟩
  · rw [ordElem_map_of_mapsRSOP (D.F.baseChangeHom (D.F0.baseChangeHom a₀)) hα]
    exact hdeg
  · show (RegularFrame.mvPowerSeries _ D.F.r).expCoeff
      (D.F.baseChangeHom (D.F0.baseChangeHom a₀) f) A = _
    rw [D.F.expCoeff_baseChangeHom, hcoef, map_mul, map_add, map_pow, map_sum, hw]
    congr 2
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_mul, map_pow, hw, D.F0.baseChangeHom_algebraMap a₀ (p j)]
    rfl

/-- **Condition (3) is preserved by the base change**: `ᾱ` maps `T*` for `(z; f)` into `T*` for
`(α z; α f)` (`tauZSubmodule_map`, `grMapMax_mem_tauZSubmoduleStar`) and the initial form of `w`
to that of `α(w)` (`initialForm_map_of_mapsRSOP`). -/
theorem WeierstrassDatum.inTauStar_baseChange [Hironaka.HironakaCitedResults.{u}] (ha₀ : RingHom.MapsRSOP a₀)
    (hsep : RingHom.IsResiduallySeparableAlgebraic a₀) {f : R} (h : D.InTauStar f) :
    (D.baseChange S0).InTauStar (D.F.baseChangeHom (D.F0.baseChangeHom a₀) f) := by
  have hα := D.F.mapsRSOP_baseChangeHom (D.F0.baseChangeHom a₀)
    (D.F0.mapsRSOP_baseChangeHom a₀ ha₀)
  have hsepα := (D.F.isResiduallySeparableAlgebraic_baseChangeHom (D.F0.baseChangeHom a₀)
    (D.F0.isResiduallySeparableAlgebraic_baseChangeHom a₀ hsep)).isResiduallySeparable
  have key := grMapMax_mem_tauZSubmoduleStar (D.F.baseChangeHom (D.F0.baseChangeHom a₀)) hα hsepα
    D.F.z (fun _ : Fin 1 => f) h
  have hzeq : (fun j : Fin D.F.r => D.F.baseChangeHom (D.F0.baseChangeHom a₀) (D.F.z j)) =
      (D.baseChange S0).F.z := funext fun j => D.F.baseChangeHom_z' (D.F0.baseChangeHom a₀) j
  show initialForm _ (D.baseChange S0).wR ∈ _
  rw [← D.baseChangeHom_wR a₀, initialForm_map_of_mapsRSOP _ hα]
  rw [hzeq] at key
  exact key

/-- `τ_{(z)}(f) ≥ 1` as soon as `w ∈ T*` (`w` is independent of `Z₁, …, Z_r`). -/
theorem WeierstrassDatum.one_le_tauZ {R : Type u} [CommRing R] [IsRegularLocalRing R]
    (D : WeierstrassDatum R) {f : R} (h : D.InTauStar f) :
    1 ≤ tauZ R D.F.z (fun _ : Fin 1 => f) := by
  classical
  have h1 := finrank_tauZSubmoduleStar_eq D.F.z_injective D.F.extends_rsop (fun _ : Fin 1 => f)
  have h2 := finrank_tauZSubmoduleStar_eq D.injective_snoc D.extendsToRSOP_snoc
    (fun _ : Fin 1 => f)
  rw [tauZSubmoduleStar_snoc_eq_of_mem D.F.z (fun _ : Fin 1 => f) D.wR h] at h2
  omega

end DatumBaseChange

end Hironaka
