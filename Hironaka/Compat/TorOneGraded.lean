/-
Copyright (c) 2026 Daattavya Aggarwal, Minhyong Kim, Oisin Kim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daattavya Aggarwal, Minhyong Kim, Oisin Kim
-/
module

public import Mathlib.Algebra.Module.GradedModule
public import Mathlib.RingTheory.Ideal.Defs
public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.Noetherian.Basic
public import Mathlib.RingTheory.TensorProduct.Finite
public import Mathlib.LinearAlgebra.TensorProduct.Pi
public import Mathlib.LinearAlgebra.TensorProduct.RightExactness
public import Mathlib.LinearAlgebra.TensorProduct.Decomposition
public import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Submodule

/-!
# Compatibility layer: `Tor₁^A(M, A/P)` as a graded `B`-module of finite type (Ch. II §1, p. 188)

The proof of Lemma 4 (p. 188) says: "Since `M` is a graded `B`-module of finite type,
`Tor₁^A(M, A/P)` is also a graded `B`-module of finite type.  Therefore it is clear that (b')
implies (b)."  Mathlib's `Tor` carries no `B`-module structure, so (as allowed by
`Hironaka/Compat/TorOne.lean`, which identifies `Tor₁^A(M, A/P)` with `ker (M ⊗_A P → M)`) the
statement is proved on the kernel model:

* `torOneKernel B M P = ker (M ⊗_A P → M)` as a `B`-submodule of `M ⊗_A P` (`mulIdealB` is the
  `B`-linear multiplication map `m ⊗ p ↦ p m`);
* `finite_torOneKernel`: it is of finite type over `B`;
* `isHomogeneous_torOneKernel`: it is a graded submodule for the grading
  `(M ⊗_A P)_n = ℳ n ⊗_A P` of `M ⊗_A P` (`DirectSum.tensorDecomposition`), which is compatible
  with the grading of `B` (the `SetLike.GradedSMul` instance below).
-/

@[expose] public section

open TensorProduct DirectSum

namespace Hironaka

universe u

section TorOneGraded

variable {A : Type u} [CommRing A] {B : Type u} [CommRing B] [Algebra A B]
  {M : Type u} [AddCommGroup M] [Module B M] [Module A M] [IsScalarTower A B M]
  (P : Ideal A)

/-- `μ : M ⊗_A P → M`, `m ⊗ p ↦ p m`, as a `B`-linear map. -/
noncomputable def mulIdealB : M ⊗[A] P →ₗ[B] M :=
  (TensorProduct.AlgebraTensorModule.rid A B M).toLinearMap ∘ₗ
    TensorProduct.AlgebraTensorModule.lTensor B M P.subtype

/-- `μ (m ⊗ p) = p m`. -/
theorem mulIdealB_tmul (m : M) (p : P) : mulIdealB (B := B) P (m ⊗ₜ[A] p) = (p : A) • m := by
  simp [mulIdealB]

/-- `μ` is the multiplication map `rid ∘ (M ⊗ P.subtype)` used in `Hironaka/Compat/TorOne.lean`. -/
theorem mulIdealB_apply (x : M ⊗[A] P) :
    mulIdealB (B := B) P x = TensorProduct.rid A M (LinearMap.lTensor M P.subtype x) := by
  induction x using TensorProduct.inductionOn with
  | tmul m p => rw [mulIdealB_tmul]; simp
  | add x y hx hy => rw [map_add, hx, hy, map_add, map_add]

/-- `μ` commutes with `f ⊗ P` for every `A`-linear endomorphism `f` of `M`. -/
theorem mulIdealB_rTensor (f : M →ₗ[A] M) (x : M ⊗[A] P) :
    mulIdealB (B := B) P (LinearMap.rTensor P f x) = f (mulIdealB (B := B) P x) := by
  induction x using TensorProduct.inductionOn with
  | tmul m p => rw [LinearMap.rTensor_tmul, mulIdealB_tmul, mulIdealB_tmul, map_smul]
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]

variable (B) (M)

/-- The kernel model of `Tor₁^A(M, A/P)`: `ker (M ⊗_A P → M)`, a `B`-submodule of `M ⊗_A P`. -/
noncomputable def torOneKernel : Submodule B (M ⊗[A] P) := LinearMap.ker (mulIdealB (B := B) P)

variable {B} {M}

variable (ℳ : ℕ → Submodule A M) [Decomposition ℳ]

/-- The projection of `M` onto its homogeneous part of degree `i` (as an endomorphism of `M`). -/
noncomputable def projHomogeneous (i : ℕ) : M →ₗ[A] M :=
  (ℳ i).subtype ∘ₗ (DirectSum.component A ℕ (fun j => ℳ j) i) ∘ₗ
    (DirectSum.decomposeLinearEquiv ℳ).toLinearMap

theorem projHomogeneous_apply (i : ℕ) (m : M) :
    projHomogeneous ℳ i m = (decompose ℳ m i : M) := rfl

attribute [local instance] DirectSum.tensorDecomposition

/-- The homogeneous components of `M ⊗_A P` (for the decomposition `⨁ (ℳ n ⊗ P)`) of `m ⊗ p`. -/
theorem coe_decompose_tensor_tmul (m : M) (p : P) (i : ℕ) :
    ((decompose (decomposeTensor ℳ P) (m ⊗ₜ[A] p) i : decomposeTensor ℳ P i) : M ⊗[A] P) =
      (decompose ℳ m i : M) ⊗ₜ[A] p := by
  have hy : DirectSum.coeAddMonoidHom (decomposeTensor ℳ P)
      (DirectSum.congrLinearEquiv (decomposeTensorEquiv ℳ P)
        (TensorProduct.directSumLeft A A (fun i => ℳ i) P
          ((DirectSum.decomposeLinearEquiv ℳ).rTensor P (m ⊗ₜ[A] p)))) = m ⊗ₜ[A] p := by
    rw [DirectSum.coe_decomposeTensor_apply]
    simp
  rw [← hy, ← Decomposition.decompose'_eq, Decomposition.right_inv]
  rw [DirectSum.coe_congrLinearEquiv, DirectSum.lmap_apply, LinearEquiv.rTensor_tmul,
    TensorProduct.directSumLeft_tmul]
  simp [DirectSum.decomposeLinearEquiv_apply]

/-- The homogeneous component of degree `i` of `x ∈ M ⊗_A P` is `(proj_i ⊗ P) x`. -/
theorem coe_decompose_tensor (x : M ⊗[A] P) (i : ℕ) :
    ((decompose (decomposeTensor ℳ P) x i : decomposeTensor ℳ P i) : M ⊗[A] P) =
      LinearMap.rTensor P (projHomogeneous ℳ i) x := by
  induction x using TensorProduct.inductionOn with
  | tmul m p => rw [coe_decompose_tensor_tmul, LinearMap.rTensor_tmul, projHomogeneous_apply]
  | add x y hx hy =>
    rw [decompose_add, DirectSum.add_apply, Submodule.coe_add, hx, hy, map_add]

/-- The grading `ℳ n ⊗_A P` of `M ⊗_A P` is compatible with the grading of `B`: so `M ⊗_A P` is a
graded `B`-module. -/
instance (𝒜 : ℕ → Submodule A B) (ℳ : ℕ → Submodule A M) [SetLike.GradedSMul 𝒜 ℳ] :
    SetLike.GradedSMul 𝒜 (decomposeTensor ℳ P) where
  smul_mem := by
    intro i j b x hb hx
    rw [decomposeTensor_apply] at hx ⊢
    obtain ⟨y, rfl⟩ := hx
    induction y using TensorProduct.inductionOn with
    | tmul m p =>
      refine ⟨⟨b • (m : M), SetLike.GradedSMul.smul_mem hb m.2⟩ ⊗ₜ[A] p, ?_⟩
      simp [TensorProduct.smul_tmul']
    | add y z hy hz =>
      rw [map_add, smul_add]
      exact add_mem hy hz

variable (B) in
/-- "`Tor₁^A(M, A/P)` is a graded `B`-module": the kernel `ker (M ⊗_A P → M)` of the
multiplication map is a homogeneous `B`-submodule of `M ⊗_A P` (graded by `decomposeTensor ℳ P`,
the pieces `ℳ n ⊗_A P`), i.e. the homogeneous components of its elements lie in it. -/
theorem isHomogeneous_torOneKernel :
    (torOneKernel B M P).IsHomogeneous (decomposeTensor ℳ P) := by
  intro i x hx
  rw [coe_decompose_tensor]
  show mulIdealB (B := B) P _ = 0
  rw [mulIdealB_rTensor, show mulIdealB (B := B) P x = 0 from hx, map_zero]

/-- `M ⊗_A N` is a finite `B`-module for a finite `B`-module `M` and a finite `A`-module `N`. -/
theorem finite_tensorProduct_left {N : Type u} [AddCommGroup N] [Module A N] [Module.Finite B M]
    [Module.Finite A N] : Module.Finite B (M ⊗[A] N) := by
  obtain ⟨n, f, hf⟩ := Module.Finite.exists_fin' A N
  have hs : Function.Surjective (TensorProduct.AlgebraTensorModule.lTensor B M f) :=
    LinearMap.lTensor_surjective M hf
  have : Module.Finite B (M ⊗[A] (Fin n → A)) :=
    Module.Finite.equiv (TensorProduct.piScalarRight A B M (Fin n)).symm
  exact Module.Finite.of_surjective _ hs

/-- "`Tor₁^A(M, A/P)` is a $B$-module of finite type": the kernel `ker (M ⊗_A P → M)` is a finite
`B`-module (`B` is noetherian and `M ⊗_A P` is finite over `B`). -/
theorem finite_torOneKernel [IsNoetherianRing A] [Algebra.FiniteType A B] [Module.Finite B M] :
    Module.Finite B (torOneKernel B M P) := by
  have : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing A B
  have : Module.Finite A P := Module.Finite.iff_fg.mpr (IsNoetherian.noetherian P)
  have : Module.Finite B (M ⊗[A] P) := finite_tensorProduct_left
  have : IsNoetherian B (M ⊗[A] P) := isNoetherian_of_isNoetherianRing_of_finite B _
  exact Module.Finite.iff_fg.mpr (IsNoetherian.noetherian _)

end TorOneGraded

end Hironaka
