/-
Copyright (c) 2026 Daattavya Aggarwal, Minhyong Kim, Oisin Kim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daattavya Aggarwal, Minhyong Kim, Oisin Kim
-/
module

public import Mathlib.RingTheory.AdicCompletion.LocalRing
public import Mathlib.RingTheory.Ideal.Quotient.Noetherian
public import Architect
public import Hironaka.Compat.AdicCompletionRegular

/-!
# Compatibility layer: the completion of a quotient of a noetherian local ring

A step in the proof of property (c) of the class 𝔅 (p. 161): if `R` is a
quotient `Λ/K` of a noetherian local ring `Λ`, the completion of `R` is the quotient of the
completion of `Λ`: `R̂ ≅ Λ̂/KΛ̂`.  This is a standard fact of the theory of local rings (the
completion of a noetherian local ring is exact on finitely generated modules); the project's
`AdicCompletionRegular` uses it tacitly.  Here it is proved directly:

* `completionMap φ hφ : Λ̂ →+* R̂`, induced by a surjection `φ : Λ → R` of local rings, levelwise
  `Λ/𝔫ⁿ → R/𝔪ⁿ`;
* it is surjective (a recursive choice of lifts, as in `AdicCompletion.map_surjective`);
* its kernel is `(ker φ)Λ̂` (`x ∈ ker` gives `x ∈ algebraMap K + 𝔫ⁿΛ̂` for all `n`, and Krull's
  intersection theorem in the noetherian local ring `Λ̂/KΛ̂`).
-/

@[expose] public section

open IsLocalRing

noncomputable section

namespace Hironaka

universe u

section LevelMaps

variable {Λ R : Type u} [CommRing Λ] [IsLocalRing Λ] [CommRing R] [IsLocalRing R]
  (φ : Λ →+* R) (hφ : Function.Surjective φ)

include hφ in
/-- A surjection of local rings maps `𝔫ⁿ` onto `𝔪ⁿ`. -/
theorem map_maximalIdeal_pow_of_surjective (n : ℕ) :
    (maximalIdeal Λ ^ n).map φ = maximalIdeal R ^ n := by
  rw [Ideal.map_pow, map_maximalIdeal_of_surjective φ hφ]

include hφ in
theorem maximalIdeal_pow_le_comap_of_surjective (n : ℕ) :
    maximalIdeal Λ ^ n ≤ (maximalIdeal R ^ n).comap φ := by
  rw [← map_maximalIdeal_pow_of_surjective φ hφ n]
  exact Ideal.le_comap_map

/-- The map `Λ/𝔫ⁿ → R/𝔪ⁿ` induced by a surjection `φ : Λ → R` of local rings. -/
def quotientPowMap (n : ℕ) : Λ ⧸ maximalIdeal Λ ^ n →+* R ⧸ maximalIdeal R ^ n :=
  Ideal.quotientMap (maximalIdeal R ^ n) φ (maximalIdeal_pow_le_comap_of_surjective φ hφ n)

theorem quotientPowMap_mk (n : ℕ) (a : Λ) :
    quotientPowMap φ hφ n (Ideal.Quotient.mk _ a) = Ideal.Quotient.mk _ (φ a) := rfl

theorem factorPow_quotientPowMap {m n : ℕ} (h : m ≤ n) (y : Λ ⧸ maximalIdeal Λ ^ n) :
    Ideal.Quotient.factorPow (maximalIdeal R) h (quotientPowMap φ hφ n y) =
      quotientPowMap φ hφ m (Ideal.Quotient.factorPow (maximalIdeal Λ) h y) := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective y
  simp [quotientPowMap_mk, Ideal.Quotient.factorPow]

private theorem factorPow_evalₐ {S : Type u} [CommRing S] (I : Ideal S) {m n : ℕ} (h : m ≤ n)
    (x : AdicCompletion I S) :
    Ideal.Quotient.factorPow I h (AdicCompletion.evalₐ I n x) = AdicCompletion.evalₐ I m x := by
  obtain ⟨c, rfl⟩ := AdicCompletion.mk_surjective I S x
  rw [AdicCompletion.evalₐ_mk, AdicCompletion.evalₐ_mk, Ideal.Quotient.factorPow,
    Ideal.Quotient.factor_mk, Ideal.Quotient.eq]
  have := AdicCompletion.AdicCauchySequence.mk_eq_mk h c
  rw [Submodule.Quotient.eq, smul_eq_mul, Ideal.mul_top] at this
  simpa using this

theorem completionMap_compat {m n : ℕ} (h : m ≤ n) :
    (Ideal.Quotient.factorPow (maximalIdeal R) h).comp ((quotientPowMap φ hφ n).comp
      (AdicCompletion.evalₐ (maximalIdeal Λ) n : AdicCompletion (maximalIdeal Λ) Λ →+*
        Λ ⧸ maximalIdeal Λ ^ n)) =
    (quotientPowMap φ hφ m).comp
      (AdicCompletion.evalₐ (maximalIdeal Λ) m : AdicCompletion (maximalIdeal Λ) Λ →+*
        Λ ⧸ maximalIdeal Λ ^ m) := by
  refine RingHom.ext fun x => ?_
  simp only [RingHom.comp_apply, RingHom.coe_coe]
  rw [factorPow_quotientPowMap φ hφ h, factorPow_evalₐ]

/-- The ring homomorphism `Λ̂ → R̂` between the completions induced by a surjection `φ : Λ → R` of
local rings. -/
def completionMap : AdicCompletion (maximalIdeal Λ) Λ →+* AdicCompletion (maximalIdeal R) R :=
  AdicCompletion.liftRingHom (maximalIdeal R)
    (fun n => (quotientPowMap φ hφ n).comp
      (AdicCompletion.evalₐ (maximalIdeal Λ) n : AdicCompletion (maximalIdeal Λ) Λ →+*
        Λ ⧸ maximalIdeal Λ ^ n))
    (fun h => completionMap_compat φ hφ h)

theorem evalₐ_completionMap (n : ℕ) (x : AdicCompletion (maximalIdeal Λ) Λ) :
    AdicCompletion.evalₐ (maximalIdeal R) n (completionMap φ hφ x) =
      quotientPowMap φ hφ n (AdicCompletion.evalₐ (maximalIdeal Λ) n x) :=
  AdicCompletion.evalₐ_liftRingHom (maximalIdeal R) _ (fun h => completionMap_compat φ hφ h) n x

theorem completionMap_algebraMap (x : Λ) :
    completionMap φ hφ (algebraMap Λ (AdicCompletion (maximalIdeal Λ) Λ) x) =
      algebraMap R (AdicCompletion (maximalIdeal R) R) (φ x) := by
  refine AdicCompletion.ext_evalₐ fun n => ?_
  rw [evalₐ_completionMap]
  show _ = AdicCompletion.evalₐ _ n (AdicCompletion.of _ R (φ x))
  rw [AdicCompletion.evalₐ_of]
  show quotientPowMap φ hφ n (AdicCompletion.evalₐ _ n (AdicCompletion.of _ Λ x)) = _
  rw [AdicCompletion.evalₐ_of, quotientPowMap_mk]

include hφ in
/-- `Λ̂ → R̂` is surjective: lift the compatible family `(y_n)` of `R/𝔪ⁿ` recursively to an
`𝔫`-adic Cauchy sequence in `Λ` (as in `AdicCompletion.map_surjective`). -/
theorem completionMap_surjective : Function.Surjective (completionMap φ hφ) := by
  intro y
  -- representatives `r n` of the levels of `y`
  choose r hr using fun n =>
    Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ (maximalIdeal R) n y)
  have hcompat : ∀ n, r (n + 1) - r n ∈ maximalIdeal R ^ n := by
    intro n
    have h1 := factorPow_evalₐ (maximalIdeal R) (Nat.le_succ n) y
    rw [← hr (n + 1), ← hr n] at h1
    rw [Ideal.Quotient.factorPow, Ideal.Quotient.factor_mk, Ideal.Quotient.eq] at h1
    exact h1
  -- the recursion
  have step : ∀ n (c : Λ), φ c - r n ∈ maximalIdeal R ^ n →
      ∃ c' : Λ, φ c' - r (n + 1) ∈ maximalIdeal R ^ (n + 1) ∧ c' - c ∈ maximalIdeal Λ ^ n := by
    intro n c hc
    have h2 : r (n + 1) - φ c ∈ maximalIdeal R ^ n := by
      have := Ideal.add_mem _ (hcompat n) ((Ideal.neg_mem_iff _).mpr hc)
      convert this using 1
      ring
    rw [← map_maximalIdeal_pow_of_surjective φ hφ n] at h2
    obtain ⟨d, hd, hdφ⟩ := (Ideal.mem_map_iff_of_surjective φ hφ).mp h2
    refine ⟨c + d, ?_, by simpa using hd⟩
    rw [map_add, hdφ]
    simp
  let a : (n : ℕ) → {c : Λ // φ c - r n ∈ maximalIdeal R ^ n} := fun n =>
    Nat.rec ⟨0, by rw [pow_zero, Ideal.one_eq_top]; trivial⟩
      (fun n cn => ⟨(step n cn.1 cn.2).choose, (step n cn.1 cn.2).choose_spec.1⟩) n
  have ha : ∀ n, (a (n + 1)).1 - (a n).1 ∈ maximalIdeal Λ ^ n := fun n =>
    (step n (a n).1 (a n).2).choose_spec.2
  let x : AdicCompletion (maximalIdeal Λ) Λ :=
    AdicCompletion.mk (maximalIdeal Λ) Λ
      (AdicCompletion.AdicCauchySequence.mk (maximalIdeal Λ) Λ (fun n => (a n).1) (fun n => by
        refine SModEq.symm ?_
        rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top]
        exact ha n))
  refine ⟨x, AdicCompletion.ext_evalₐ fun n => ?_⟩
  rw [evalₐ_completionMap, AdicCompletion.evalₐ_mk, ← hr n, quotientPowMap_mk,
    Ideal.Quotient.eq]
  exact (a n).2

end LevelMaps

section Kernel

variable {Λ : Type u} [CommRing Λ] [IsLocalRing Λ] [IsNoetherianRing Λ]

/-- The kernel of `Λ̂ → Λ/𝔫ⁿ` is `𝔫ⁿΛ̂`. -/
theorem ker_evalₐ_eq_map (n : ℕ) :
    RingHom.ker (AdicCompletion.evalₐ (maximalIdeal Λ) n :
        AdicCompletion (maximalIdeal Λ) Λ →+* Λ ⧸ maximalIdeal Λ ^ n) =
      (maximalIdeal Λ ^ n).map (algebraMap Λ (AdicCompletion (maximalIdeal Λ) Λ)) := by
  ext x
  have hfg : (maximalIdeal Λ).FG := (maximalIdeal Λ).fg_of_isNoetherianRing
  have h1 : (maximalIdeal Λ ^ n • ⊤ : Submodule Λ (AdicCompletion (maximalIdeal Λ) Λ)) =
      (AdicCompletion.eval (maximalIdeal Λ) Λ n).ker :=
    AdicCompletion.pow_smul_top_eq_ker_eval hfg
  rw [RingHom.mem_ker, ← Submodule.restrictScalars_mem Λ, ← Ideal.smul_top_eq_map, h1,
    LinearMap.mem_ker]
  have hle : maximalIdeal Λ ^ n ≤ (maximalIdeal Λ ^ n • ⊤ : Ideal Λ) := by
    rw [smul_eq_mul, Ideal.mul_top]
  have hle' : (maximalIdeal Λ ^ n • ⊤ : Ideal Λ) ≤ maximalIdeal Λ ^ n := by
    rw [smul_eq_mul, Ideal.mul_top]
  constructor
  · intro h
    have h' : AdicCompletion.evalₐ (maximalIdeal Λ) n x = 0 := h
    rw [← AdicCompletion.factor_evalₐ_eq_eval (maximalIdeal Λ) x hle, h', map_zero]
  · intro h
    show AdicCompletion.evalₐ (maximalIdeal Λ) n x = 0
    rw [← AdicCompletion.factor_eval_eq_evalₐ (maximalIdeal Λ) x hle', h, map_zero]

variable {R : Type u} [CommRing R] [IsLocalRing R] (φ : Λ →+* R) (hφ : Function.Surjective φ)

include hφ in
omit [IsNoetherianRing Λ] in
/-- `(ker φ)Λ̂ ⊆ ker (Λ̂ → R̂)`. -/
theorem map_ker_le_ker_completionMap :
    (RingHom.ker φ).map (algebraMap Λ (AdicCompletion (maximalIdeal Λ) Λ)) ≤
      RingHom.ker (completionMap φ hφ) := by
  rw [Ideal.map_le_iff_le_comap]
  intro κ hκ
  rw [Ideal.mem_comap, RingHom.mem_ker, completionMap_algebraMap, RingHom.mem_ker.mp hκ,
    map_zero]

include hφ in
/-- If `x ∈ ker (Λ̂ → R̂)`, then `x ∈ (ker φ)Λ̂ + 𝔫ⁿΛ̂` for every `n`. -/
theorem mem_sup_of_mem_ker_completionMap {x : AdicCompletion (maximalIdeal Λ) Λ}
    (hx : x ∈ RingHom.ker (completionMap φ hφ)) (n : ℕ) :
    x ∈ (RingHom.ker φ).map (algebraMap Λ (AdicCompletion (maximalIdeal Λ) Λ)) ⊔
      (maximalIdeal Λ ^ n).map (algebraMap Λ (AdicCompletion (maximalIdeal Λ) Λ)) := by
  have h0 := congrArg (AdicCompletion.evalₐ (maximalIdeal R) n) (RingHom.mem_ker.mp hx)
  rw [evalₐ_completionMap, map_zero] at h0
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ (maximalIdeal Λ) n x)
  rw [← ha, quotientPowMap_mk, Ideal.Quotient.eq_zero_iff_mem,
    ← map_maximalIdeal_pow_of_surjective φ hφ n] at h0
  obtain ⟨b, hb, hba⟩ := (Ideal.mem_map_iff_of_surjective φ hφ).mp h0
  have hκ : a - b ∈ RingHom.ker φ := by
    rw [RingHom.mem_ker, map_sub, hba, sub_self]
  have hmem : x - algebraMap Λ (AdicCompletion (maximalIdeal Λ) Λ) (a - b) ∈
      (maximalIdeal Λ ^ n).map (algebraMap Λ (AdicCompletion (maximalIdeal Λ) Λ)) := by
    rw [← ker_evalₐ_eq_map, RingHom.mem_ker, map_sub]
    have : (AdicCompletion.evalₐ (maximalIdeal Λ) n)
        (algebraMap Λ (AdicCompletion (maximalIdeal Λ) Λ) (a - b)) =
        Ideal.Quotient.mk _ (a - b) :=
      AdicCompletion.evalₐ_of (maximalIdeal Λ) n (a - b)
    change AdicCompletion.evalₐ (maximalIdeal Λ) n x -
      AdicCompletion.evalₐ (maximalIdeal Λ) n
        (algebraMap Λ (AdicCompletion (maximalIdeal Λ) Λ) (a - b)) = 0
    rw [this, ← ha, ← map_sub, Ideal.Quotient.eq_zero_iff_mem]
    simpa using hb
  have : x = algebraMap Λ (AdicCompletion (maximalIdeal Λ) Λ) (a - b) +
      (x - algebraMap Λ (AdicCompletion (maximalIdeal Λ) Λ) (a - b)) := by ring
  rw [this]
  exact Submodule.add_mem_sup (Ideal.mem_map_of_mem _ hκ) hmem

include hφ in
/-- The kernel of `Λ̂ → R̂` is `(ker φ)Λ̂`: by `mem_sup_of_mem_ker_completionMap` the image of an
element of the kernel lies in every power of the maximal ideal of the noetherian local ring
`Λ̂/(ker φ)Λ̂`, hence is zero (Krull's intersection theorem). -/
theorem ker_completionMap :
    RingHom.ker (completionMap φ hφ) =
      (RingHom.ker φ).map (algebraMap Λ (AdicCompletion (maximalIdeal Λ) Λ)) := by
  refine le_antisymm (fun x hx => ?_) (map_ker_le_ker_completionMap φ hφ)
  have hN : IsNoetherianRing (AdicCompletion (maximalIdeal Λ) Λ) :=
    isNoetherianRing_adicCompletion_of_isNoetherianRing _
  set J := (RingHom.ker φ).map (algebraMap Λ (AdicCompletion (maximalIdeal Λ) Λ)) with hJdef
  have hRn : IsNoetherianRing R := isNoetherianRing_of_surjective Λ R φ hφ
  have hJ : J ≠ ⊤ := by
    intro h
    have h1 : (1 : AdicCompletion (maximalIdeal Λ) Λ) ∈ RingHom.ker (completionMap φ hφ) :=
      map_ker_le_ker_completionMap φ hφ (show (1 : AdicCompletion (maximalIdeal Λ) Λ) ∈ J by
        rw [h]; exact Submodule.mem_top)
    rw [RingHom.mem_ker, map_one] at h1
    exact one_ne_zero h1
  have : Nontrivial (AdicCompletion (maximalIdeal Λ) Λ ⧸ J) :=
    Ideal.Quotient.nontrivial_iff.mpr hJ
  have : IsLocalRing (AdicCompletion (maximalIdeal Λ) Λ ⧸ J) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective
  have hmax : maximalIdeal (AdicCompletion (maximalIdeal Λ) Λ ⧸ J) =
      (maximalIdeal (AdicCompletion (maximalIdeal Λ) Λ)).map (Ideal.Quotient.mk J) :=
    (map_maximalIdeal_of_surjective _ Ideal.Quotient.mk_surjective).symm
  have hk : Ideal.Quotient.mk J x ∈
      ⨅ n, maximalIdeal (AdicCompletion (maximalIdeal Λ) Λ ⧸ J) ^ n := by
    rw [Submodule.mem_iInf]
    intro n
    rw [hmax, ← Ideal.map_pow, AdicCompletion.maximalIdeal_eq_map, ← Ideal.map_pow]
    obtain ⟨j, hj, y, hy, hxy⟩ := Submodule.mem_sup.mp (mem_sup_of_mem_ker_completionMap φ hφ hx n)
    rw [← hxy, map_add, Ideal.Quotient.eq_zero_iff_mem.mpr hj, zero_add]
    exact Ideal.mem_map_of_mem _ hy
  rw [Ideal.iInf_pow_eq_bot_of_isLocalRing _ (maximalIdeal.isMaximal _).ne_top,
    Ideal.mem_bot] at hk
  exact Ideal.Quotient.eq_zero_iff_mem.mp hk

include hφ in
/-- **The completion of a quotient** (`R = Λ/K`): `R̂ ≅ Λ̂/KΛ̂`, the isomorphism being the inverse
of the map induced by `completionMap`: `ε (completionMap φ hφ x) = mk x` for `x ∈ Λ̂`. -/
@[blueprint "lem:completion-quotient"
  (statement := /-- Let $\varphi\colon\Lambda\to R$ be a surjection of noetherian local rings.
    Then $\hat\varphi\colon\hat\Lambda\to\hat R$ is surjective with kernel
    $(\ker\varphi)\hat\Lambda$,
    so $\hat R\cong\hat\Lambda/(\ker\varphi)\hat\Lambda$. -/)
  (proof := /-- Surjectivity: lift a compatible family in $R/\mathfrak m^n$ recursively to
    $\Lambda/\mathfrak n^n$. Kernel: if $x\in\ker\hat\varphi$ then, for every $n$, writing its
    image in $\Lambda/\mathfrak n^n$ as $a$ with $\varphi(a)\in\mathfrak m^n$ and
    $\varphi(\mathfrak n^n)=\mathfrak m^n$, we get $x\in(\ker\varphi)\hat\Lambda+\mathfrak
    n^n\hat\Lambda$. Hence the image of $x$ in the noetherian local ring
    $\hat\Lambda/(\ker\varphi)\hat\Lambda$ lies in every power of its maximal ideal, so it is zero
    by Krull's intersection theorem. This is step 3.2 of the proof of property (c)
    (footnote~31). -/)
  (latexEnv := "lemma")]
theorem exists_ringEquiv_adicCompletion_quotient_comp :
    ∃ ε : AdicCompletion (maximalIdeal R) R ≃+*
        (AdicCompletion (maximalIdeal Λ) Λ ⧸
          (RingHom.ker φ).map (algebraMap Λ (AdicCompletion (maximalIdeal Λ) Λ))),
      ∀ x : AdicCompletion (maximalIdeal Λ) Λ,
        ε (completionMap φ hφ x) = Ideal.Quotient.mk _ x := by
  let e₁ := RingHom.quotientKerEquivOfSurjective (completionMap_surjective φ hφ)
  let e₂ := Ideal.quotEquivOfEq (ker_completionMap φ hφ)
  refine ⟨e₁.symm.trans e₂, fun x => ?_⟩
  have h1 : e₁.symm (completionMap φ hφ x) =
      Ideal.Quotient.mk (RingHom.ker (completionMap φ hφ)) x := by
    rw [RingEquiv.symm_apply_eq]
    rfl
  rw [RingEquiv.trans_apply, h1]
  rfl

include hφ in
/-- **The completion of a quotient** (`R = Λ/K`): `R̂ ≅ Λ̂/KΛ̂`, compatibly with the canonical maps
from `Λ`.  Used in step 3.2 of the proof of (c), p. 161. -/
theorem exists_ringEquiv_adicCompletion_quotient :
    ∃ ε : AdicCompletion (maximalIdeal R) R ≃+*
        (AdicCompletion (maximalIdeal Λ) Λ ⧸
          (RingHom.ker φ).map (algebraMap Λ (AdicCompletion (maximalIdeal Λ) Λ))),
      ∀ x : Λ, ε (algebraMap R (AdicCompletion (maximalIdeal R) R) (φ x)) =
        Ideal.Quotient.mk _ (algebraMap Λ (AdicCompletion (maximalIdeal Λ) Λ) x) := by
  obtain ⟨ε, hε⟩ := exists_ringEquiv_adicCompletion_quotient_comp φ hφ
  exact ⟨ε, fun x => by rw [← completionMap_algebraMap φ hφ x, hε]⟩

end Kernel

end Hironaka
