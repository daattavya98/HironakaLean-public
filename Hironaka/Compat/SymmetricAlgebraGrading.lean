/-
Copyright (c) 2026 Daattavya Aggarwal, Minhyong Kim, Oisin Kim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daattavya Aggarwal, Minhyong Kim, Oisin Kim
-/
module

public import Mathlib.LinearAlgebra.SymmetricAlgebra.Basic
public import Mathlib.LinearAlgebra.TensorAlgebra.Grading

/-!
# The grading of the symmetric algebra

Mathlib has the grading of the tensor algebra (`TensorAlgebra.gradedAlgebra`) but none for the
symmetric algebra.  This file gives the symmetric algebra `SymmetricAlgebra R M` of an `R`-module `M`
the structure of a graded `R`-algebra, the piece of degree `n` being the `n`-th power of the range of
`SymmetricAlgebra.ι`, in the same way as for the tensor algebra.  It is infrastructure for Proj of the
symmetric algebra (Ch. 0 §2, p. 124 of the paper).
-/

@[expose] public section

namespace SymmetricAlgebra

open scoped DirectSum

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

variable (R M) in
/-- A version of `SymmetricAlgebra.ι` that maps directly into the graded structure; an auxiliary
construction for `SymmetricAlgebra.gradedAlgebra`. -/
def gradedι : M →ₗ[R] ⨁ i : ℕ, ↥(LinearMap.range (ι R M : M →ₗ[R] _) ^ i) :=
  DirectSum.lof R ℕ (fun i => ↥(LinearMap.range (ι R M : M →ₗ[R] _) ^ i)) 1 ∘ₗ
    (ι R M).codRestrict _ fun m => by simpa only [pow_one] using LinearMap.mem_range_self _ m

theorem gradedι_apply (m : M) :
    gradedι R M m =
      DirectSum.of (fun (i : ℕ) => ↥(LinearMap.range (ι R M : M →ₗ[R] _) ^ i)) 1
        ⟨ι R M m, by simpa only [pow_one] using LinearMap.mem_range_self _ m⟩ :=
  rfl

/-- The symmetric algebra is graded by the powers of the submodule `(SymmetricAlgebra.ι R M).range`:
the homogeneous part of degree `n` is the `n`-th symmetric power of `M` (Ch. 0 §2, p. 124). -/
instance gradedAlgebra :
    GradedAlgebra
      ((LinearMap.range (ι R M : M →ₗ[R] SymmetricAlgebra R M) ^ ·) : ℕ → Submodule R _) :=
  fast_instance% GradedAlgebra.ofAlgHom _ (lift (gradedι R M))
    (by
      ext m
      simp [gradedι_apply, DirectSum.coeAlgHom_of])
    fun i x => by
    obtain ⟨x, hx⟩ := x
    dsimp only [Subtype.coe_mk, DirectSum.lof_eq_of]
    induction hx using Submodule.pow_induction_on_left' with
    | algebraMap r =>
      rw [AlgHom.commutes, DirectSum.algebraMap_apply]; rfl
    | add x y i hx hy ihx ihy =>
      rw [map_add, ihx, ihy, ← map_add]
      rfl
    | mem_mul m hm i x hx ih =>
      obtain ⟨_, rfl⟩ := hm
      rw [map_mul, ih, lift_ι_apply, gradedι_apply, DirectSum.of_mul_of]
      exact DirectSum.of_eq_of_gradedMonoid_eq (Sigma.subtype_ext (add_comm _ _) rfl)

end SymmetricAlgebra
