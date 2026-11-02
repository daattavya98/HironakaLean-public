/-
Copyright (c) 2026 Daattavya Aggarwal, Minhyong Kim, Oisin Kim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daattavya Aggarwal, Minhyong Kim, Oisin Kim
-/
module

public import Mathlib.RingTheory.Localization.BaseChange
public import Mathlib.RingTheory.TensorProduct.Maps
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.Algebra.Module.LocalizedModule.Submodule

/-!
# Compatibility layer: `Tor₁` commutes with localization, on the kernel model (Ch. II §1, p. 188)

The proof of Lemma 4 (p. 188) passes from "`Tor₁^{A_P}(M_P, A_P/PA_P) = 0`" (the corollary to
Lemma 2 over the local ring `A_P`) to "`Tor₁^A(M, A/P)_P = 0`", using tacitly that `Tor`
commutes with localization.  Mathlib's `Tor` has no localization API, but the project identifies
`Tor₁^A(M, A/J)` with `ker (M ⊗_A J → M)` (`Hironaka/Compat/TorOne.lean`), so this file proves
the localization statement on that model:

* `tensorEquivMapAtPrime`: `A_Q ⊗_A J ≅ J A_Q`, `r ⊗ p ↦ r p`;
* `tensorIdealLocalization`: `N ⊗_A J → (A_Q ⊗_A N) ⊗_{A_Q} J A_Q`, `n ⊗ p ↦ (1 ⊗ n) ⊗ p`, which is
  the localization of the `A`-module `N ⊗_A J` at `Q` (`isLocalizedModule_tensorIdealLocalization`)
  and is compatible with the multiplication maps (`rid_lTensor_tensorIdealLocalization`);
* `exists_smul_eq_zero_of_mul_injective_localization`: if the localized multiplication map is
  injective (i.e. `Tor₁^{A_Q}(N_Q, A_Q/J A_Q) = 0`), every element of `ker (N ⊗_A J → N)` is
  killed by some `s ∉ Q` (i.e. `Tor₁^A(N, A/J)_Q = 0`).
-/

@[expose] public section

open TensorProduct

namespace Hironaka

universe u

section LocalizationTensor

variable {A : Type u} [CommRing A] (Q : Ideal A) [Q.IsPrime]

/-- The localization of an ideal: `A_Q ⊗_A J ≅ J A_Q`, `r ⊗ p ↦ r p`. -/
noncomputable def tensorEquivMapAtPrime (J : Ideal A) :
    Localization.AtPrime Q ⊗[A] J ≃ₗ[Localization.AtPrime Q]
      J.map (algebraMap A (Localization.AtPrime Q)) :=
  (((isLocalizedModule_iff_isBaseChange Q.primeCompl (Localization.AtPrime Q)
    (Submodule.toLocalized' (Localization.AtPrime Q) Q.primeCompl
      (Algebra.linearMap A (Localization.AtPrime Q)) J)).mp inferInstance).equiv).trans
    (LinearEquiv.ofEq _ _ (by
      rw [Submodule.localized'_eq_span]
      rfl))

/-- `A_Q ⊗_A J ≅ J A_Q` sends `r ⊗ p` to `r p`. -/
theorem coe_tensorEquivMapAtPrime_tmul (J : Ideal A) (r : Localization.AtPrime Q) (p : J) :
    (tensorEquivMapAtPrime Q J (r ⊗ₜ[A] p) : Localization.AtPrime Q) =
      r * algebraMap A (Localization.AtPrime Q) p := by
  simp only [tensorEquivMapAtPrime, LinearEquiv.trans_apply, LinearEquiv.coe_ofEq_apply]
  rw [IsBaseChange.equiv_tmul]
  rfl

section TensorIdeal

variable (N : Type u) [AddCommGroup N] [Module A N] (J : Ideal A)

/-- The localization of `N ⊗_A J` at `Q`, written as `(A_Q ⊗_A N) ⊗_{A_Q} J A_Q`: the map
`n ⊗ p ↦ (1 ⊗ n) ⊗ p`. -/
noncomputable def tensorIdealLocalization :
    N ⊗[A] J →ₗ[A] (Localization.AtPrime Q ⊗[A] N) ⊗[Localization.AtPrime Q]
      (J.map (algebraMap A (Localization.AtPrime Q))) :=
  (((TensorProduct.AlgebraTensorModule.distribBaseChange A (Localization.AtPrime Q) N J).trans
    (TensorProduct.AlgebraTensorModule.congr
      (LinearEquiv.refl (Localization.AtPrime Q) (Localization.AtPrime Q ⊗[A] N))
      (tensorEquivMapAtPrime Q J))).restrictScalars A).toLinearMap ∘ₗ
    TensorProduct.mk A (Localization.AtPrime Q) (N ⊗[A] J) 1

/-- `n ⊗ p ↦ (1 ⊗ n) ⊗ (1 ⊗ p)` under the identification of `A_Q ⊗_A J` with `J A_Q`. -/
theorem tensorIdealLocalization_tmul (n : N) (p : J) :
    tensorIdealLocalization Q N J (n ⊗ₜ[A] p) =
      ((1 : Localization.AtPrime Q) ⊗ₜ[A] n) ⊗ₜ[Localization.AtPrime Q]
        tensorEquivMapAtPrime Q J ((1 : Localization.AtPrime Q) ⊗ₜ[A] p) := by
  simp [tensorIdealLocalization]

/-- `N ⊗_A J → (A_Q ⊗_A N) ⊗_{A_Q} J A_Q` is the localization at `Q` (the passage from `Tor` to
`Tor` of the localized modules, on the kernel model). -/
instance isLocalizedModule_tensorIdealLocalization :
    IsLocalizedModule Q.primeCompl (tensorIdealLocalization Q N J) := by
  have h : IsLocalizedModule Q.primeCompl
      (TensorProduct.mk A (Localization.AtPrime Q) (N ⊗[A] J) 1) :=
    (isLocalizedModule_iff_isBaseChange Q.primeCompl (Localization.AtPrime Q) _).mpr
      (TensorProduct.isBaseChange A (N ⊗[A] J) (Localization.AtPrime Q))
  exact IsLocalizedModule.of_linearEquiv Q.primeCompl
    (TensorProduct.mk A (Localization.AtPrime Q) (N ⊗[A] J) 1) _

/-- The multiplication map of the localized kernel model commutes with `tensorIdealLocalization`. -/
theorem rid_lTensor_tensorIdealLocalization (x : N ⊗[A] J) :
    TensorProduct.rid (Localization.AtPrime Q) _ (LinearMap.lTensor _
      (J.map (algebraMap A (Localization.AtPrime Q))).subtype (tensorIdealLocalization Q N J x)) =
      (1 : Localization.AtPrime Q) ⊗ₜ[A]
        (TensorProduct.rid A N (LinearMap.lTensor N J.subtype x)) := by
  induction x using TensorProduct.inductionOn with
  | tmul n p =>
    rw [tensorIdealLocalization_tmul]
    have h1 : (tensorEquivMapAtPrime Q J ((1 : Localization.AtPrime Q) ⊗ₜ[A] p)) =
        (algebraMap A (Localization.AtPrime Q) p : Localization.AtPrime Q) := by
      rw [coe_tensorEquivMapAtPrime_tmul, one_mul]
    simp only [LinearMap.lTensor_tmul, Submodule.subtype_apply, TensorProduct.rid_tmul, h1]
    rw [algebraMap_smul]
    exact (TensorProduct.tmul_smul _ _ _).symm
  | add x y hx hy =>
    rw [map_add, map_add, map_add, hx, hy, map_add, map_add, TensorProduct.tmul_add]

/-- If the multiplication map `(A_Q ⊗_A N) ⊗_{A_Q} J A_Q → A_Q ⊗_A N` is injective, then every
element of `ker (N ⊗_A J → N)` is killed by some `s ∉ Q`. -/
theorem exists_smul_eq_zero_of_mul_injective_localization
    (hinj : Function.Injective (fun y : (Localization.AtPrime Q ⊗[A] N) ⊗[Localization.AtPrime Q]
        (J.map (algebraMap A (Localization.AtPrime Q))) =>
      TensorProduct.rid (Localization.AtPrime Q) _ (LinearMap.lTensor _
        (J.map (algebraMap A (Localization.AtPrime Q))).subtype y)))
    (x : N ⊗[A] J) (hx : TensorProduct.rid A N (LinearMap.lTensor N J.subtype x) = 0) :
    ∃ s ∉ Q, s • x = 0 := by
  have h0 : tensorIdealLocalization Q N J x = tensorIdealLocalization Q N J 0 := by
    rw [map_zero]
    apply hinj
    simp only
    rw [rid_lTensor_tensorIdealLocalization, hx, map_zero, map_zero, TensorProduct.tmul_zero]
  obtain ⟨c, hc⟩ := IsLocalizedModule.exists_of_eq (S := Q.primeCompl) h0
  exact ⟨c, c.2, by rw [smul_zero] at hc; exact hc⟩

/-- Converse of `exists_smul_eq_zero_of_mul_injective_localization`: if every element of
`ker (N ⊗_A J → N)` is killed by some `s ∉ Q` (`Tor₁^A(N, A/J)_Q = 0`), the multiplication map
`(A_Q ⊗_A N) ⊗_{A_Q} J A_Q → A_Q ⊗_A N` is injective (`Tor₁^{A_Q}(N_Q, A_Q/J A_Q) = 0`). -/
theorem mul_injective_localization_of_forall_exists_smul_eq_zero
    (hb : ∀ x : N ⊗[A] J, TensorProduct.rid A N (LinearMap.lTensor N J.subtype x) = 0 →
      ∃ s ∉ Q, s • x = 0) :
    Function.Injective (fun y : (Localization.AtPrime Q ⊗[A] N) ⊗[Localization.AtPrime Q]
        (J.map (algebraMap A (Localization.AtPrime Q))) =>
      TensorProduct.rid (Localization.AtPrime Q) _ (LinearMap.lTensor _
        (J.map (algebraMap A (Localization.AtPrime Q))).subtype y)) := by
  let S := Q.primeCompl
  let μ' : ((Localization.AtPrime Q ⊗[A] N) ⊗[Localization.AtPrime Q]
      (J.map (algebraMap A (Localization.AtPrime Q)))) →ₗ[Localization.AtPrime Q]
      (Localization.AtPrime Q ⊗[A] N) :=
    (TensorProduct.rid (Localization.AtPrime Q) _).toLinearMap ∘ₗ LinearMap.lTensor _
      (J.map (algebraMap A (Localization.AtPrime Q))).subtype
  have hN : IsLocalizedModule S (TensorProduct.mk A (Localization.AtPrime Q) N 1) :=
    (isLocalizedModule_iff_isBaseChange S (Localization.AtPrime Q) _).mpr
      (TensorProduct.isBaseChange A N (Localization.AtPrime Q))
  have key : ∀ y, μ' y = 0 → y = 0 := by
    intro y hy
    obtain ⟨⟨x, s⟩, hs⟩ := IsLocalizedModule.surj S (tensorIdealLocalization Q N J) y
    simp only [Submonoid.smul_def] at hs
    -- `1 ⊗ μ x = μ' (σ x) = μ' (s • y) = 0`, so `t μ x = 0` for some `t ∈ S`
    have h0 : μ' (tensorIdealLocalization Q N J x) = 0 := by
      rw [← hs, LinearMap.map_smul_of_tower, hy, smul_zero]
    have h1 : (1 : Localization.AtPrime Q) ⊗ₜ[A] (TensorProduct.rid A N
        (LinearMap.lTensor N J.subtype x)) = 0 := by
      rw [← rid_lTensor_tensorIdealLocalization]
      exact h0
    obtain ⟨t, ht⟩ := IsLocalizedModule.exists_of_eq (S := S) (f := TensorProduct.mk A
      (Localization.AtPrime Q) N 1) (h1.trans (TensorProduct.tmul_zero _ _).symm)
    rw [smul_zero, Submonoid.smul_def] at ht
    obtain ⟨s', hs'Q, hs'⟩ := hb ((t : A) • x) (by
      rw [map_smul, map_smul]
      exact ht)
    have hunit := IsLocalization.map_units (Localization.AtPrime Q)
      (⟨s' * t * s, S.mul_mem (S.mul_mem hs'Q t.2) s.2⟩ : S)
    have h3 : algebraMap A (Localization.AtPrime Q) (s' * t * s) • y = 0 := by
      rw [algebraMap_smul, mul_smul, mul_smul, hs, ← map_smul, ← map_smul, hs', map_zero]
    exact hunit.smul_eq_zero.mp h3
  intro y z hyz
  exact sub_eq_zero.mp (key _ (by rw [map_sub]; exact sub_eq_zero.mpr hyz))

end TensorIdeal

end LocalizationTensor

end Hironaka
