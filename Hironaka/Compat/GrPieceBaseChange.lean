/-
Copyright (c) 2026 Daattavya Aggarwal, Minhyong Kim, Oisin Kim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daattavya Aggarwal, Minhyong Kim, Oisin Kim
-/
module

public import Mathlib.RingTheory.TensorProduct.IsBaseChangeRightExact
public import Hironaka.Compat.GradedModule

/-!
# Ch. II §1, p. 181: base change of the graded pieces `grⁿ_I(M)`

The first half of the proof of Lemma 9 (p. 181) and its consequence on the graded pieces.  For a
flat ring homomorphism `A → A'` and `I' = IA'`:

> "`gr_I(A)_P ≅ gr_{IA_P}(A_P)`": the canonical map `grⁿ_I(M) ⊗_A A' → grⁿ_{I'}(M')` is bijective
> when `M'` is a base change of `M` (the maps `λ : (IᵏM) ⊗_A A' → I'ᵏM'` are bijective because
> `A'` is flat over `A`, and `⊗` is right exact).

* `GrModPiece.nonempty_baseChange_equiv`: `grⁿ_I(M) ⊗_{A/I} A'/I' ≅ grⁿ_{I'}(M')`,
  `A'/I'`-linearly, for `M'` a base change of `M` and `A'` flat over `A`;
* `GrPiece.nonempty_baseChange_equiv`: the case `M = A`, `M' = A'`, i.e. the degreewise form of
  "the localization `gr_P(O)_P` of `gr_P(O)` with respect to `P` is canonically isomorphic to
  `gr_{PO_P}(O_P)`" (p. 186, Corollary 2), `grⁿ_{IA'}(A') ≅ (A'/IA') ⊗_{A/I} grⁿ_I(A)`.

The proof of Corollary 2 (i) in `Hironaka/Ch2/Flatness.lean` uses `GrPiece.nonempty_baseChange_equiv`.
-/

@[expose] public section

open TensorProduct

namespace Hironaka

universe u

namespace GrModPiece

/-- For an `A`-linear map `f : M → M'` into an `A'`-module and `JA' ⊆ J'`, `f(JM) ⊆ J'M'`. -/
theorem map_mem_smul_top_of_map_le {A A' : Type u} [CommRing A] [CommRing A']
    [Algebra A A'] {M : Type u} [AddCommGroup M] [Module A M] {M' : Type u} [AddCommGroup M']
    [Module A' M'] [Module A M'] [IsScalarTower A A' M'] (f : M →ₗ[A] M') {J : Ideal A}
    {J' : Ideal A'} (hJ : J.map (algebraMap A A') ≤ J') {x : M}
    (hx : x ∈ J • (⊤ : Submodule A M)) : f x ∈ J' • (⊤ : Submodule A' M') := by
  refine Submodule.smul_induction_on hx (fun a ha m _ => ?_) (fun x y hx hy => ?_)
  · rw [map_smul, ← algebraMap_smul A' a]
    exact Submodule.smul_mem_smul (hJ (Ideal.mem_map_of_mem _ ha)) Submodule.mem_top
  · rw [map_add]; exact add_mem hx hy

/-- The restriction `JM → J'M'` of an `A`-linear map `f : M → M'` (the map `λ` of the proof of
Lemma 9 when `M' = M ⊗_A A'` and `J' = JA'`). -/
def smulTopRestrict {A A' : Type u} [CommRing A] [CommRing A'] [Algebra A A']
    {M : Type u} [AddCommGroup M] [Module A M] {M' : Type u} [AddCommGroup M'] [Module A' M']
    [Module A M'] [IsScalarTower A A' M'] (f : M →ₗ[A] M') (J : Ideal A) (J' : Ideal A')
    (hJ : J.map (algebraMap A A') ≤ J') :
    ↥(J • (⊤ : Submodule A M)) →ₗ[A] ↥(J' • (⊤ : Submodule A' M')) where
  toFun x := ⟨f x, map_mem_smul_top_of_map_le f hJ x.2⟩
  map_add' _ _ := Subtype.ext (map_add f _ _)
  map_smul' _ _ := Subtype.ext (map_smul f _ _)

/-- Proof of Lemma 9, first step: if `A'` is flat over `A` and `M'` is the base change of `M`,
then `J'M'` (`J' = JA'`) is the base change of `JM`, i.e. `λ : (JM) ⊗_A A' → J'M'` is
bijective. -/
theorem isBaseChange_smulTopRestrict {A A' : Type u} [CommRing A] [CommRing A']
    [Algebra A A'] [Module.Flat A A'] {M : Type u} [AddCommGroup M] [Module A M] {M' : Type u}
    [AddCommGroup M'] [Module A' M'] [Module A M'] [IsScalarTower A A' M'] {f : M →ₗ[A] M'}
    (hf : IsBaseChange A' f) (J : Ideal A) (J' : Ideal A')
    (hJ : J.map (algebraMap A A') = J') :
    IsBaseChange A' (smulTopRestrict f J J' hJ.le) := by
  let g : A' ⊗[A] ↥(J • (⊤ : Submodule A M)) →ₗ[A'] M' :=
    hf.equiv.toLinearMap ∘ₗ (J • (⊤ : Submodule A M)).subtype.baseChange A'
  have hg : ∀ (a : A') (x : ↥(J • (⊤ : Submodule A M))), g (a ⊗ₜ x) = a • f x := fun a x => by
    simp [g, IsBaseChange.equiv_tmul]
  -- `(JM) ⊗_A A' → M ⊗_A A'` is injective since `A'` is flat over `A`.
  have hinj : Function.Injective g := by
    refine hf.equiv.injective.comp ?_
    rw [LinearMap.baseChange_eq_ltensor]
    exact Module.Flat.lTensor_preserves_injective_linearMap _ (Submodule.injective_subtype _)
  -- Its image is `J'M'`.
  have hrange : LinearMap.range g = J' • (⊤ : Submodule A' M') := by
    apply le_antisymm
    · rintro _ ⟨y, rfl⟩
      induction y using TensorProduct.inductionOn with
      | tmul a x =>
        rw [hg]
        exact Submodule.smul_mem _ a (map_mem_smul_top_of_map_le f hJ.le x.2)
      | add y z hy hz => rw [map_add]; exact add_mem hy hz
    · rw [Submodule.smul_le]
      intro r hr n _
      rw [← hJ] at hr
      have hr' : r ∈ Submodule.span A' (algebraMap A A' '' J) := hr
      clear hr
      induction hr' using Submodule.span_induction with
      | mem r hmem =>
        obtain ⟨a, ha, rfl⟩ := hmem
        induction n using hf.inductionOn with
        | tmul m =>
          rw [algebraMap_smul, ← map_smul]
          exact ⟨1 ⊗ₜ ⟨a • m, Submodule.smul_mem_smul ha Submodule.mem_top⟩, by
            rw [hg, one_smul]⟩
        | smul s n hn => rw [smul_comm]; exact Submodule.smul_mem _ s (hn trivial)
        | add x y hx hy => rw [smul_add]; exact add_mem (hx trivial) (hy trivial)
      | zero => simp
      | add r s _ _ hr hs => rw [add_smul]; exact add_mem hr hs
      | smul c r _ hr => rw [smul_eq_mul, mul_smul]; exact Submodule.smul_mem _ c hr
  refine IsBaseChange.of_equiv ((LinearEquiv.ofInjective g hinj).trans
    (LinearEquiv.ofEq _ _ hrange)) fun x => Subtype.ext ?_
  simp [hg]
  rfl

/-- A module `N` killed by `I` is its own base change to `R ⧸ I`. -/
theorem isBaseChange_quotient_id {R : Type u} [CommRing R] (I : Ideal R) (N : Type u)
    [AddCommGroup N] [Module R N] [Module (R ⧸ I) N] [IsScalarTower R (R ⧸ I) N] :
    IsBaseChange (R ⧸ I) (LinearMap.id : N →ₗ[R] N) := by
  have hbot : I • (⊤ : Submodule R N) = ⊥ := by
    rw [eq_bot_iff, Submodule.smul_le]
    intro r hr x _
    rw [Submodule.mem_bot, ← algebraMap_smul (R ⧸ I) r x, Ideal.Quotient.algebraMap_eq,
      Ideal.Quotient.eq_zero_iff_mem.mpr hr, zero_smul]
  refine IsBaseChange.of_equiv
    ((TensorProduct.quotTensorEquivQuotSMul N I ≪≫ₗ
      Submodule.quotEquivOfEqBot _ hbot).extendScalarsOfSurjective
      Ideal.Quotient.mk_surjective) fun x => ?_
  simp

/-- Proof of Lemma 9, second step: if `A'` is flat over `A` and `M'` is the base change of `M`
(e.g. `M' = M ⊗_A A'`), then `ε_n : grⁿ_I(M) ⊗_A A' → grⁿ_{I'}(M')` is bijective, which gives
an `A'/I'`-linear isomorphism `grⁿ_I(M) ⊗_{A/I} A'/I' ≅ grⁿ_{I'}(M')` (`I' = IA'`). -/
theorem nonempty_baseChange_equiv {A A' : Type u} [CommRing A]
    [CommRing A'] [Algebra A A'] [Module.Flat A A'] {M : Type u} [AddCommGroup M] [Module A M]
    {M' : Type u} [AddCommGroup M'] [Module A' M'] [Module A M'] [IsScalarTower A A' M']
    {f : M →ₗ[A] M'} (hf : IsBaseChange A' f) (I : Ideal A) (n : ℕ) :
    Nonempty ((A' ⧸ I.map (algebraMap A A')) ⊗[A ⧸ I] GrModPiece I M n ≃ₗ[A' ⧸ I.map
      (algebraMap A A')] GrModPiece (I.map (algebraMap A A')) M' n) := by
  have hpow : ∀ k, (I ^ k).map (algebraMap A A') = I.map (algebraMap A A') ^ k :=
    fun k => Ideal.map_pow _ _ _
  have hle : I ^ (n + 1) • (⊤ : Submodule A M) ≤ I ^ n • ⊤ :=
    Submodule.smul_mono_left (Ideal.pow_le_pow_right n.le_succ)
  have hle' : I.map (algebraMap A A') ^ (n + 1) • (⊤ : Submodule A' M') ≤
      I.map (algebraMap A A') ^ n • ⊤ :=
    Submodule.smul_mono_left (Ideal.pow_le_pow_right n.le_succ)
  let K := Submodule.comap (I ^ n • ⊤ : Submodule A M).subtype (I ^ (n + 1) • ⊤)
  let K' := Submodule.comap (I.map (algebraMap A A') ^ n • ⊤ : Submodule A' M').subtype
    (I.map (algebraMap A A') ^ (n + 1) • ⊤)
  -- The maps `λ_{n+1}`, `λ_n` and `ε_n` of the paper's diagram.
  let l₀ := smulTopRestrict f (I ^ (n + 1)) (I.map (algebraMap A A') ^ (n + 1)) (hpow _).le
  let l₁ := smulTopRestrict f (I ^ n) (I.map (algebraMap A A') ^ n) (hpow _).le
  let ε : GrModPiece I M n →ₗ[A] GrModPiece (I.map (algebraMap A A')) M' n :=
    K.liftQ ((K'.mkQ.restrictScalars A) ∘ₗ l₁) (by
      intro x hx
      rw [LinearMap.mem_ker, LinearMap.comp_apply, LinearMap.restrictScalars_apply,
        Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      exact map_mem_smul_top_of_map_le f (hpow _).le hx)
  -- `λ_{n+1}`, `λ_n` are bijective (flatness), hence so is `ε_n` (right exactness of `⊗`).
  have hε : IsBaseChange A' ε := by
    refine IsBaseChange.of_right_exact A' l₀ l₁ ε (f := Submodule.inclusion hle) (g := K.mkQ)
      (f' := Submodule.inclusion hle') (g' := K'.mkQ) ?_ ?_
      (isBaseChange_smulTopRestrict hf _ _ (hpow _))
      (isBaseChange_smulTopRestrict hf _ _ (hpow _))
      ?_ (Submodule.mkQ_surjective _) ?_ (Submodule.mkQ_surjective _)
    · ext x; rfl
    · ext x; rfl
    · rw [LinearMap.exact_iff, Submodule.ker_mkQ, Submodule.range_inclusion]
    · rw [LinearMap.exact_iff, Submodule.ker_mkQ, Submodule.range_inclusion]
  -- `grⁿ_{I'}(M') ≅ grⁿ_I(M) ⊗_A A' = grⁿ_I(M) ⊗_A A'/I' = grⁿ_I(M) ⊗_{A/I} A'/I'`.
  have hT := hε.comp (isBaseChange_quotient_id (I.map (algebraMap A A'))
    (GrModPiece (I.map (algebraMap A A')) M' n))
  exact ⟨LinearEquiv.baseChange (A ⧸ I) (A' ⧸ I.map (algebraMap A A')) _ _
      (isBaseChange_quotient_id I (GrModPiece I M n)).equiv.symm ≪≫ₗ
    AlgebraTensorModule.cancelBaseChange A (A ⧸ I) (A' ⧸ I.map (algebraMap A A'))
      (A' ⧸ I.map (algebraMap A A')) (GrModPiece I M n) ≪≫ₗ hT.equiv⟩

end GrModPiece

namespace GrPiece

/-- `Pⁿ/Pⁿ⁺¹ = PⁿO/Pⁿ⁺¹O` (`GrPiece` versus `GrModPiece` for the module `O`). -/
theorem nonempty_equiv_grModPiece {R : Type u} [CommRing R] (P : Ideal R)
    (n : ℕ) : Nonempty (GrPiece P n ≃ₗ[R ⧸ P] GrModPiece P R n) := by
  have h : ∀ k : ℕ, (P ^ k : Submodule R R) = P ^ k • (⊤ : Submodule R R) := fun k => by
    rw [smul_eq_mul, Ideal.mul_top]
  have key : ∀ a b c d : Submodule R R, a = c → b = d →
      Nonempty ((↥a ⧸ Submodule.comap a.subtype b) ≃ₗ[R] (↥c ⧸ Submodule.comap c.subtype d)) := by
    rintro a b c d rfl rfl
    exact ⟨LinearEquiv.refl _ _⟩
  obtain ⟨e⟩ := key _ _ _ _ (h n) (h (n + 1))
  exact ⟨e.extendScalarsOfSurjective Ideal.Quotient.mk_surjective⟩

/-- `grⁿ_{IA'}(A') ≅ (A'/IA') ⊗_{A/I} grⁿ_I(A)` for a flat `A → A'` (p. 181, proof of Lemma 9,
applied to `M = A`, `M' = A'`; the degreewise form of "the localization `gr_P(O)_P` of `gr_P(O)` with
respect to `P` is canonically isomorphic to `gr_{PO_P}(O_P)`", p. 186). -/
theorem nonempty_baseChange_equiv {A A' : Type u} [CommRing A] [CommRing A'] [Algebra A A']
    [Module.Flat A A'] (I : Ideal A) (n : ℕ) :
    Nonempty ((A' ⧸ I.map (algebraMap A A')) ⊗[A ⧸ I] GrPiece I n ≃ₗ[A' ⧸ I.map
      (algebraMap A A')] GrPiece (I.map (algebraMap A A')) n) := by
  obtain ⟨e₀⟩ := GrModPiece.nonempty_baseChange_equiv (IsBaseChange.linearMap A A') I n
  obtain ⟨f₁⟩ := nonempty_equiv_grModPiece I n
  obtain ⟨f₂⟩ := nonempty_equiv_grModPiece (I.map (algebraMap A A')) n
  exact ⟨TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl _ _) f₁ ≪≫ₗ e₀ ≪≫ₗ
    f₂.symm⟩

end GrPiece

end Hironaka
