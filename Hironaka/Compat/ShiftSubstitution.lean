/-
Copyright (c) 2026 Daattavya Aggarwal, Minhyong Kim, Oisin Kim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daattavya Aggarwal, Minhyong Kim, Oisin Kim
-/
module

public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.Etale.Weakly
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.TotallySplit

/-!
# Compatibility layer: shifts of linear forms in a polynomial ring (Ch. III, Lemma 25, p. 272)

In the proof of Lemma 25 the paper writes, in the polynomial ring `gr_{M₁}(R₁)`:
"By the assumption (2), we can find a system of linear forms `(L, L_1, …, L_τ)` in `Y, X_1, …, X_a`
with coefficients in `k` such that
`φ̄ = φ(Z̄_1, …, Z̄_r, W̄ + L, Ȳ_1 + L_1, …, Ȳ_τ + L_τ)`" and then,
comparing the `Z̄^Ā`-components of the two expressions of `φ̄`, "It follows that `eL = 0`, hence
`L = 0`" (pp. 272–273).  The same argument ends the proof of Lemma 21 (p. 258).  This file proves
the polynomial-ring content, for a field `K` and an arbitrary set `σ` of variables:

* `killVars K U`: the retraction killing the variables of `U` (the `Y, X_1, …, X_a`);
* `exists_shift_of_finrank_le`: if `T` is a space of linear forms on which the retraction does not
  lower the dimension, the inverse of `π|_T` is the restriction of a substitution
  `θ : X_v ↦ X_v + ℓ_v`, `ℓ_v ∈ span(U)` (the paper's `L, L_1, …, L_τ`), `θ ∘ π = id` on `T`;
* `X_mem_of_shape`: if `φ̄ ∈ K[T]` and the `Z̄^Ā`-components of `φ̄` and `π φ̄` have the shape
  `c W̄^e + (terms of `W̄`-degree ≤ e - 2)`, then `W̄ ∈ T` (`L = 0`).  The `Z̄^Ā`-component is
  encoded by iterated partial derivatives `Λ = ev_{Z = 0} ∘ ∂_D` (`derivList`), which commute with
  the substitution `θ`.
-/

@[expose] public section

open MvPolynomial

namespace Hironaka

section PolyShift

variable (K : Type*) {σ : Type*} [Field K]

open Classical in
/-- The retraction `K[X_v] → K[X_v : v ∉ U]` killing the variables in `U`. -/
noncomputable def killVars (U : Set σ) : MvPolynomial σ K →ₐ[K] MvPolynomial σ K :=
  aeval fun v => if v ∈ U then 0 else X v

variable {K}

open Classical in
theorem killVars_X (U : Set σ) (v : σ) :
    killVars K U (X v) = if v ∈ U then 0 else X v := by
  simp [killVars]

theorem killVars_killVars (U : Set σ) (P : MvPolynomial σ K) :
    killVars K U (killVars K U P) = killVars K U P := by
  have : (killVars K U).comp (killVars K U) = killVars K U := by
    refine MvPolynomial.algHom_ext fun v => ?_
    by_cases hv : v ∈ U <;> simp [killVars_X, hv]
  exact congrArg (fun f => f P) this

/-- The span of the variables in `U`. -/
noncomputable def varSpan (K : Type*) {σ : Type*} [Field K] (U : Set σ) :
    Submodule K (MvPolynomial σ K) :=
  Submodule.span K (X '' U)

theorem killVars_linearForm (U : Set σ) {x : MvPolynomial σ K}
    (hx : x ∈ homogeneousSubmodule σ K 1) :
    killVars K U x ∈ homogeneousSubmodule σ K 1 ∧ x - killVars K U x ∈ varSpan K U := by
  rw [homogeneousSubmodule_one_eq_span_X] at hx ⊢
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨v, rfl⟩ := hy
    by_cases hv : v ∈ U
    · refine ⟨?_, ?_⟩
      · simp [killVars_X, hv]
      · simp only [killVars_X, hv, ite_true, sub_zero]
        exact Submodule.subset_span ⟨v, hv, rfl⟩
    · simp [killVars_X, hv, zero_mem]
      exact Submodule.subset_span ⟨v, rfl⟩
  | zero => simp
  | add x y _ _ hx hy =>
    refine ⟨by rw [map_add]; exact add_mem hx.1 hy.1, ?_⟩
    have := add_mem hx.2 hy.2
    simpa [map_add, sub_add_sub_comm] using this
  | smul c x _ hx =>
    refine ⟨by rw [map_smul]; exact Submodule.smul_mem _ _ hx.1, ?_⟩
    have := Submodule.smul_mem _ c hx.2
    simpa [map_smul, smul_sub] using this

/-- **Shifting lemma** (the "linear forms `L, L_1, …, L_τ`" of Lemma 25, p. 272, and of the proof
of Lemma 21, p. 258): if `φ̄ ∈ K[T]` where `T` is a `K`-space of linear forms whose image under
the retraction `π` killing the variables of `U` has no smaller dimension, then `π` is injective on
`T`, and the inverse of `π|_T` is the restriction of a substitution `θ : X_v ↦ X_v + ℓ_v`,
`ℓ_v ∈ span(U)`, with `θ ∘ π = id` on `T`. -/
theorem exists_shift_of_finrank_le (U : Set σ) (T : Submodule K (MvPolynomial σ K))
    [FiniteDimensional K T] (hT : T ≤ homogeneousSubmodule σ K 1)
    (hrank : Module.finrank K T ≤ Module.finrank K (T.map (killVars K U).toLinearMap)) :
    ∃ θ : MvPolynomial σ K →ₐ[K] MvPolynomial σ K,
      (∀ v, θ (X v) - X v ∈ varSpan K U) ∧ ∀ t ∈ T, θ (killVars K U t) = t := by
  classical
  set π : MvPolynomial σ K →ₗ[K] MvPolynomial σ K := (killVars K U).toLinearMap with hπ
  have hπapp : ∀ x, π x = killVars K U x := fun x => rfl
  -- `π` is injective on `T`
  have hrange : LinearMap.range (π.domRestrict T) = T.map π := LinearMap.range_domRestrict _ _
  have hinj : Function.Injective (π.domRestrict T) := by
    rw [← LinearMap.ker_eq_bot]
    have h1 := LinearMap.finrank_range_add_finrank_ker (π.domRestrict T)
    rw [hrange] at h1
    have h2 : Module.finrank K (LinearMap.ker (π.domRestrict T)) = 0 := by omega
    exact Submodule.finrank_eq_zero.mp h2
  let e : T ≃ₗ[K] LinearMap.range (π.domRestrict T) := LinearEquiv.ofInjective _ hinj
  have he : ∀ t : T, (e t : MvPolynomial σ K) = π t := fun t => rfl
  -- the displacement `y ↦ π⁻¹ y - y`, with values in `span(U)`
  have hmem : ∀ y : LinearMap.range (π.domRestrict T),
      ((e.symm y : T) : MvPolynomial σ K) - y ∈ varSpan K U := by
    intro y
    obtain ⟨t, rfl⟩ := e.surjective y
    rw [LinearEquiv.symm_apply_apply, he]
    exact (killVars_linearForm U (hT t.2)).2
  let ℓ : LinearMap.range (π.domRestrict T) →ₗ[K] varSpan K U :=
    LinearMap.codRestrict (varSpan K U)
      ((T.subtype ∘ₗ e.symm.toLinearMap) - (LinearMap.range (π.domRestrict T)).subtype) hmem
  obtain ⟨g, hg⟩ := LinearMap.exists_extend ℓ
  let θ : MvPolynomial σ K →ₐ[K] MvPolynomial σ K :=
    aeval fun v => X v + ((g (π (X v)) : varSpan K U) : MvPolynomial σ K)
  have hθX : ∀ v, θ (X v) = X v + ((g (π (X v)) : varSpan K U) : MvPolynomial σ K) :=
    fun v => aeval_X _ v
  have hθlin : ∀ x ∈ homogeneousSubmodule σ K 1,
      θ x = x + ((g (π x) : varSpan K U) : MvPolynomial σ K) := by
    intro x hx
    rw [homogeneousSubmodule_one_eq_span_X] at hx
    induction hx using Submodule.span_induction with
    | mem y hy => obtain ⟨v, rfl⟩ := hy; exact hθX v
    | zero => simp
    | add x y _ _ hx hy =>
      simp only [map_add, hx, hy, Submodule.coe_add]; abel
    | smul c x _ hx =>
      simp only [map_smul, hx, smul_add, Submodule.coe_smul]
  refine ⟨θ, fun v => ?_, fun t ht => ?_⟩
  · rw [hθX, add_sub_cancel_left]
    exact (g (π (X v))).2
  · have h1 : π t ∈ homogeneousSubmodule σ K 1 := (killVars_linearForm U (hT ht)).1
    have hmemT : π t ∈ LinearMap.range (π.domRestrict T) := ⟨⟨t, ht⟩, rfl⟩
    have h2 : g (π (π t)) = ℓ ⟨π t, hmemT⟩ := by
      have := congrArg (fun F => F ⟨π t, hmemT⟩) hg
      rw [show π (π t) = π t from killVars_killVars U t]
      exact this
    show θ (π t) = t
    have h3 : e.symm ⟨π t, hmemT⟩ = ⟨t, ht⟩ := by
      rw [LinearEquiv.symm_apply_eq]
      exact Subtype.ext rfl
    have hℓ : ((ℓ ⟨π t, hmemT⟩ : varSpan K U) : MvPolynomial σ K) = t - π t := by
      show ((e.symm ⟨π t, hmemT⟩ : T) : MvPolynomial σ K) - π t = t - π t
      rw [h3]
    rw [hθlin _ h1, h2, hℓ]
    abel

section Shape

variable [DecidableEq σ]

/-- Iterated partial derivatives `∂_{x_1} ⋯ ∂_{x_n}` along a list of variables. -/
noncomputable def derivList : List σ → MvPolynomial σ K → MvPolynomial σ K
  | [], P => P
  | x :: l, P => pderiv x (derivList l P)

omit [DecidableEq σ] in
theorem pderiv_eq_zero_of_mem_varSpan {U : Set σ} {x : σ} (hx : x ∉ U)
    {ℓ : MvPolynomial σ K} (hℓ : ℓ ∈ varSpan K U) : pderiv x ℓ = 0 := by
  induction hℓ using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨u, hu, rfl⟩ := hy
    exact pderiv_X_of_ne (fun h => hx (h ▸ hu))
  | zero => simp
  | add a b _ _ ha hb => simp [ha, hb]
  | smul c a _ ha => simp [ha]

/-- A substitution `X_v ↦ X_v + ℓ_v`, `ℓ_v ∈ span(U)`, commutes with `∂_x` for `x ∉ U`. -/
theorem pderiv_comp_substitution {U : Set σ} {x : σ} (hx : x ∉ U)
    (θ : MvPolynomial σ K →ₐ[K] MvPolynomial σ K)
    (hθ : ∀ v, θ (X v) - X v ∈ varSpan K U)
    (P : MvPolynomial σ K) : pderiv x (θ P) = θ (pderiv x P) := by
  have hℓ : ∀ v, pderiv x (θ (X v)) = pderiv x (X v) := fun v => by
    have := pderiv_eq_zero_of_mem_varSpan hx (hθ v)
    rw [map_sub] at this
    exact sub_eq_zero.mp this
  induction P using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p v hp =>
    have h1 : θ (pderiv x (X v)) = pderiv x (X v) := by
      by_cases hv : v = x
      · subst hv; simp
      · rw [pderiv_X_of_ne hv, map_zero]
    rw [map_mul, pderiv_mul, hp, hℓ, pderiv_mul, map_add, map_mul, map_mul, h1]

theorem derivList_comp_substitution {U : Set σ} {D : List σ} (hD : ∀ x ∈ D, x ∉ U)
    (θ : MvPolynomial σ K →ₐ[K] MvPolynomial σ K)
    (hθ : ∀ v, θ (X v) - X v ∈ varSpan K U)
    (P : MvPolynomial σ K) : derivList D (θ P) = θ (derivList D P) := by
  induction D with
  | nil => rfl
  | cons x l ih =>
    simp only [derivList]
    rw [ih (fun y hy => hD y (List.mem_cons_of_mem _ hy)),
      pderiv_comp_substitution (hD x List.mem_cons_self) θ hθ]

omit [DecidableEq σ] in
theorem killVars_of_mem_varSpan {U Zs : Set σ} (hUZ : Disjoint U Zs) {ℓ : MvPolynomial σ K}
    (hℓ : ℓ ∈ varSpan K U) : killVars K Zs ℓ = ℓ := by
  classical
  induction hℓ using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨u, hu, rfl⟩ := hy
    have : u ∉ Zs := Set.disjoint_left.mp hUZ hu
    simp [killVars_X, this]
  | zero => simp
  | add a b _ _ ha hb => simp [ha, hb]
  | smul c a _ ha => simp [ha]

omit [DecidableEq σ] in
/-- A substitution `X_v ↦ X_v + ℓ_v`, `ℓ_v ∈ span(U)`, fixing the variables of `Zs`, commutes
with the evaluation at `Zs = 0`. -/
theorem killVars_comp_substitution {U Zs : Set σ} (hUZ : Disjoint U Zs)
    (θ : MvPolynomial σ K →ₐ[K] MvPolynomial σ K)
    (hθ : ∀ v, θ (X v) - X v ∈ varSpan K U)
    (hθZ : ∀ z ∈ Zs, θ (X z) = X z) (P : MvPolynomial σ K) :
    killVars K Zs (θ P) = θ (killVars K Zs P) := by
  classical
  have : (killVars K Zs).comp θ = θ.comp (killVars K Zs) := by
    refine MvPolynomial.algHom_ext fun v => ?_
    by_cases hv : v ∈ Zs
    · simp [killVars_X, hv, hθZ v hv]
    · have h1 : θ (X v) = X v + (θ (X v) - X v) := by ring
      simp only [AlgHom.comp_apply, killVars_X, hv, ite_false]
      conv_lhs => rw [h1]
      rw [map_add, killVars_of_mem_varSpan hUZ (hθ v), killVars_X]
      simp [hv]
  exact congrArg (fun f => f P) this

omit [DecidableEq σ] in
theorem X_notMem_varSpan {U : Set σ} {w : σ} (hw : w ∉ U) :
    (X w : MvPolynomial σ K) ∉ varSpan K U :=
  (linearIndependent_X σ K).notMem_span_image hw

/-- **Lemma 25, step `eL = 0`** (pp. 272–273), in the polynomial ring `gr_{M₁}(R₁) = K[X_v]`:
let `φ̄ ∈ K[T]`, `T` a `K`-space of linear forms containing the variables of `Zs` such that the
retraction `π` killing the variables of `U` (the `Y, X_1, …, X_a`) does not lower the dimension of
`T`, and `X_w ∈ π(T)`.  Suppose that the "`Z̄^Ā`-component" `Λ = ev_{Zs=0} ∘ ∂_D` of `φ̄` (resp. of
`π φ̄`) is `c'' X_w` (resp. `c X_w` with `c ≠ 0`): this is the shape
`Z̄^Ā(W̄^e + λ_2 W̄^{e-2} + ⋯)` of the paper (`D` consists of the exponents `Ā` of `Zs` and of
`e - 1` copies of `w`; then `Λ(c W^e + ⋯ + c_{e-2} W^{e-2}) = c e! W`).  Then `X_w ∈ T`, i.e.
`L = 0`. -/
theorem X_mem_of_shape {U Zs : Set σ} (hUZ : Disjoint U Zs) {w : σ} (hwU : w ∉ U)
    {D : List σ} (hD : ∀ x ∈ D, x ∉ U)
    (T : Submodule K (MvPolynomial σ K)) [FiniteDimensional K T]
    (hT : T ≤ homogeneousSubmodule σ K 1)
    (hrank : Module.finrank K T ≤ Module.finrank K (T.map (killVars K U).toLinearMap))
    (hZ : ∀ z ∈ Zs, X z ∈ T) (hwT : X w ∈ T.map (killVars K U).toLinearMap)
    {φ : MvPolynomial σ K} (hφ : φ ∈ Algebra.adjoin K (T : Set (MvPolynomial σ K)))
    {c c'' : K} (hc : c ≠ 0)
    (hφ' : killVars K Zs (derivList D (killVars K U φ)) = C c * X w)
    (hφ'' : killVars K Zs (derivList D φ) = C c'' * X w) : X w ∈ T := by
  obtain ⟨θ, hθ, hθT⟩ := exists_shift_of_finrank_le U T hT hrank
  -- `θ` fixes the variables of `Zs`
  have hθZ : ∀ z ∈ Zs, θ (X z) = X z := fun z hz => by
    have hzU : z ∉ U := fun h => Set.disjoint_left.mp hUZ h hz
    have := hθT (X z) (hZ z hz)
    simpa [killVars_X, hzU] using this
  -- `φ = θ (π φ)`
  have hφθ : φ = θ (killVars K U φ) := by
    have hle : Algebra.adjoin K (T : Set (MvPolynomial σ K)) ≤
        AlgHom.equalizer ((θ.comp (killVars K U))) (AlgHom.id K _) :=
      Algebra.adjoin_le fun t ht => hθT t ht
    exact ((hle hφ) : _).symm
  -- `Λ φ = θ (Λ π φ) = c (X_w + ℓ_w)`
  have hΛ : killVars K Zs (derivList D φ) = C c * θ (X w) := by
    conv_lhs => rw [hφθ]
    rw [derivList_comp_substitution hD θ hθ, killVars_comp_substitution hUZ θ hθ hθZ, hφ',
      map_mul]
    congr 1
    exact θ.commutes c
  -- hence `ℓ_w = θ X_w - X_w = 0`
  have hℓ0 : θ (X w) = X w := by
    set ℓ := θ (X w) - X w with hℓdef
    have hℓ : ℓ ∈ varSpan K U := hθ w
    have h1 : C c * (X w + ℓ) = C c'' * X w := by
      rw [← hφ'', hΛ, hℓdef]; ring_nf
    have h2 : c • ℓ = (c'' - c) • (X w : MvPolynomial σ K) := by
      have : C c * ℓ = C (c'' - c) * X w := by
        have := h1
        rw [C_sub]
        linear_combination this
      rw [C_mul', C_mul'] at this
      exact this
    have hcc : c'' - c = 0 := by
      by_contra hne
      apply X_notMem_varSpan (K := K) hwU
      have : (X w : MvPolynomial σ K) = ((c'' - c)⁻¹ : K) • (c • ℓ) := by
        rw [h2, smul_smul, inv_mul_cancel₀ hne, one_smul]
      rw [this]
      exact Submodule.smul_mem _ _ (Submodule.smul_mem _ _ hℓ)
    rw [hcc, zero_smul] at h2
    have : ℓ = 0 := by
      rcases smul_eq_zero.mp h2 with h | h
      · exact absurd h hc
      · exact h
    rw [hℓdef] at this
    exact sub_eq_zero.mp this
  obtain ⟨t, ht, htw⟩ := Submodule.mem_map.mp hwT
  have := hθT t ht
  rw [show killVars K U t = X w from htw, hℓ0] at this
  rw [this]; exact ht

end Shape

end PolyShift

end Hironaka
