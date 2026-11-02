/-
Copyright (c) 2026 Daattavya Aggarwal, Minhyong Kim, Oisin Kim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daattavya Aggarwal, Minhyong Kim, Oisin Kim
-/
module

public import Mathlib.Algebra.Module.GradedModule
public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.Algebra.Polynomial.Module.Basic
public import Mathlib.LinearAlgebra.DirectSum.TensorProduct
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Architect
public import Hironaka.Compat.Graded

/-!
# The graded module `gr_I(M)` (Ch. II §1, pp. 180-182)

> If M is an A-module, then we associate the following graded gr_I(A)-module:
> gr_I(M) = Σ_{m=0}^∞ I^m M / I^{m+1} M. If M is an A-module of finite type, then gr_I(M) is a
> gr_I(A)-module of finite type. The homogeneous part of degree m of gr_I(M), that is
> I^m M / I^{m+1} M, will be denoted by gr^m_I(M). If M is an A-module of finite type, then
> gr^m_I(M) is an A/I-module of finite type.  (p. 180)

> Let A be a noetherian ring and I an ideal in A. If M is an A-module, then we have the
> canonical homomorphisms M ⊗_A I^m/I^{m+1} → I^m M/I^{m+1} M for all non-negative integers m
> \dots\ The above canonical homomorphisms give us a canonical homomorphism of graded
> gr_I(A)-modules: φ: gr^0_I(M) ⊗_{A/I} gr_I(A) → gr_I(M).  (pp. 181-182)

This file holds:

* the homogeneous parts `grᵐ_I(M) = GrModPiece I M m` and the canonical maps
  `M ⊗_A grᵐ_I(A) → grᵐ_I(M)` (`grModMap`) of pp. 181-182;
* the graded `gr_I(A)`-module `gr_I(M)` itself, `AssocGradedModule I M`, as the quotient
  `Rees(M)/(I · Rees(A)) · Rees(M)` of the Rees module `Rees(M) = ⊕_m IᵐM Xᵐ ⊆ M[X]` (a module over
  the Rees algebra `Rees(A)`), a module over `gr_I(A) = Rees(A)/I · Rees(A)` (`AssocGraded I`);
  its grading is the internal direct sum `gr_I(M) = ⨁_m grᵐ_I(M)` (`DirectSum.Decomposition`,
  compatible with the grading of `gr_I(A)` through `SetLike.GradedSMul`), and
  `finite_of_finite` proves "if `M` is of finite type, `gr_I(M)` is a `gr_I(A)`-module of finite
  type";
* the canonical homomorphism `φ` as one map `grModPhi : gr⁰_I(M) ⊗_{A/I} gr_I(A) → gr_I(M)`,
  `gr_I(A)`-linear (`grModPhi_tmul_mul`) and degree preserving (`grModPhi_tmul_mem_homogeneous`),
  and its link with the degree-wise maps: `φ` is the direct sum of the `φₘ`
  (`grModPhi_bijective_iff`), and `φₘ` is `grModMap` under the identification
  `gr⁰_I(M) ⊗_{A/I} grᵐ_I(A) = M ⊗_A grᵐ_I(A)` (`zeroPieceTensorGrPieceEquiv`), so that
  "`φ` is an isomorphism" is equivalent to "every `grModMap I M m` is bijective"
  (`grModPhi_bijective_iff_forall_grModMap_bijective`).
-/

@[expose] public section

open TensorProduct Polynomial
open scoped DirectSum

namespace Hironaka

universe u

/-! ### The graded module `gr_I(M)` (p. 180) -/

section GradedModule

variable {A : Type u} [CommRing A]

/-- p. 180: the homogeneous part of degree `m` of the graded `gr_I(A)`-module
`gr_I(M) = ⊕_{m≥0} IᵐM/Iᵐ⁺¹M`, i.e. `grᵐ_I(M) = IᵐM/Iᵐ⁺¹M`, encoded like `GrPiece` as the
submodule `IᵐM ⊆ M` modulo the preimage of `Iᵐ⁺¹M`.

The graded `gr_I(A)`-module `gr_I(M)` itself is `AssocGradedModule I M` (below), and the sentence of
p. 180 "If `M` is an `A`-module of finite type, then `gr_I(M)` is a `gr_I(A)`-module of finite
type" is `AssocGradedModule.finite_of_finite`. -/
@[blueprint "def:II.1-graded-module"
  (statement := /-- Let $A$ be a noetherian ring, $I$ an ideal in $A$ and $M$ an $A$-module.
    We associate with $I$ the graded $\operatorname{gr}_I(A)$-module
    $\operatorname{gr}_I(M)=\bigoplus_{m\ge0}I^mM/I^{m+1}M$; its homogeneous part of degree
    $m$, that is $I^mM/I^{m+1}M$, is denoted by $\operatorname{gr}^m_I(M)$. If $M$ is an
    $A$-module of finite type, then $\operatorname{gr}^m_I(M)$ is an $A/I$-module of finite
    type. (p.~180.)

    \textbf{Formalization.} This declaration is the homogeneous part
    $\operatorname{gr}^m_I(M)$; the graded $\operatorname{gr}_I(A)$-module
    $\operatorname{gr}_I(M)$ is \cref{def:II.1-gr-module}, and the assertion of p.~180 that it is
    of finite type over $\operatorname{gr}_I(A)$ when $M$ is of finite type is
    \cref{lem:II.1-gr-module-finite}. -/)
  (latexEnv := "definition")]
abbrev GrModPiece (I : Ideal A) (M : Type u) [AddCommGroup M] [Module A M] (m : ℕ) : Type u :=
  ↥(I ^ m • (⊤ : Submodule A M)) ⧸
    Submodule.comap (I ^ m • (⊤ : Submodule A M)).subtype (I ^ (m + 1) • (⊤ : Submodule A M))

/-- `I` annihilates `IᵐM/Iᵐ⁺¹M`, so it is an `A/I`-module. -/
theorem grModPiece_isTorsionBySet (I : Ideal A) (M : Type u) [AddCommGroup M] [Module A M]
    (m : ℕ) : Module.IsTorsionBySet A (GrModPiece I M m) (I : Set A) := by
  intro x a
  induction x using Submodule.Quotient.induction_on with
  | H x =>
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap,
      Submodule.subtype_apply, Submodule.coe_smul, pow_succ', Submodule.mul_smul]
    exact Submodule.smul_mem_smul a.2 x.2

noncomputable instance GrModPiece.module (I : Ideal A) (M : Type u) [AddCommGroup M]
    [Module A M] (m : ℕ) : Module (A ⧸ I) (GrModPiece I M m) :=
  (grModPiece_isTorsionBySet I M m).module

/-- The `A/I`-module structure on `IᵐM/Iᵐ⁺¹M` is compatible with the `A`-module structure. -/
instance GrModPiece.isScalarTower (I : Ideal A) (M : Type u) [AddCommGroup M] [Module A M]
    (m : ℕ) : IsScalarTower A (A ⧸ I) (GrModPiece I M m) :=
  IsScalarTower.of_algebraMap_smul fun _ _ => rfl

/-- For noetherian `A` and `M` of finite type, `IᵐM/Iᵐ⁺¹M` is a finitely generated
`A`-module. -/
instance GrModPiece.finite [IsNoetherianRing A] (I : Ideal A) (M : Type u) [AddCommGroup M]
    [Module A M] [Module.Finite A M] (m : ℕ) : Module.Finite A (GrModPiece I M m) :=
  inferInstance

/-- p. 180: "If `M` is an `A`-module of finite type, then `grᵐ_I(M)` is an `A/I`-module of
finite type." -/
instance GrModPiece.finite_quotient [IsNoetherianRing A] (I : Ideal A) (M : Type u)
    [AddCommGroup M] [Module A M] [Module.Finite A M] (m : ℕ) :
    Module.Finite (A ⧸ I) (GrModPiece I M m) :=
  Module.Finite.of_restrictScalars_finite A (A ⧸ I) (GrModPiece I M m)

/-! ### The canonical homomorphisms `M ⊗_A Iᵐ/Iᵐ⁺¹ → IᵐM/Iᵐ⁺¹M` (pp. 181–182) -/

/-- The bilinear map `(a, x) ↦ [a • x]` for `a ∈ Iᵐ`, `x ∈ M`, "induced by the operation of
`A` on the `A`-module `M`" (p. 182), with values in `IᵐM/Iᵐ⁺¹M`. -/
noncomputable def grModMapAux (I : Ideal A) (M : Type u) [AddCommGroup M] [Module A M] (m : ℕ) :
    ↥(I ^ m) →ₗ[A] M →ₗ[A] GrModPiece I M m :=
  (LinearMap.mk₂ A (fun (a : ↥(I ^ m)) (x : M) =>
      (⟨a.1 • x, Submodule.smul_mem_smul a.2 Submodule.mem_top⟩ :
        ↥(I ^ m • (⊤ : Submodule A M))))
    (fun a₁ a₂ x => Subtype.ext (add_smul a₁.1 a₂.1 x))
    (fun c a x => Subtype.ext (by simp [mul_smul]))
    (fun a x₁ x₂ => Subtype.ext (smul_add a.1 x₁ x₂))
    (fun c a x => Subtype.ext (smul_comm a.1 c x))).compr₂
    (Submodule.comap (I ^ m • (⊤ : Submodule A M)).subtype
      (I ^ (m + 1) • (⊤ : Submodule A M))).mkQ

/-- The bilinear map `grModMapAux` kills `Iᵐ⁺¹` in its first argument, so it descends to
`Iᵐ/Iᵐ⁺¹`. -/
theorem grModMapAux_ker (I : Ideal A) (M : Type u) [AddCommGroup M] [Module A M] (m : ℕ) :
    Submodule.comap (I ^ m).subtype (I ^ (m + 1)) ≤ LinearMap.ker (grModMapAux I M m) := by
  intro a ha
  rw [Submodule.mem_comap, Submodule.subtype_apply] at ha
  rw [LinearMap.mem_ker]
  ext x
  simp only [grModMapAux, LinearMap.compr₂_apply, LinearMap.mk₂_apply, Submodule.mkQ_apply,
    LinearMap.zero_apply, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap,
    Submodule.subtype_apply]
  exact Submodule.smul_mem_smul ha Submodule.mem_top

/-- p. 181: "If `M` is an `A`-module, then we have the canonical homomorphisms
`M ⊗_A Iᵐ/Iᵐ⁺¹ → IᵐM/Iᵐ⁺¹M` for all non-negative integers `m`", `x ⊗ [a] ↦ [a • x]`, obtained
from the commutative diagram with exact rows `M ⊗_A Iᵐ⁺¹ → M ⊗_A Iᵐ → M ⊗_A Iᵐ/Iᵐ⁺¹ → 0`
and `0 → Iᵐ⁺¹M → IᵐM → IᵐM/Iᵐ⁺¹M → 0`, "where the first two vertical arrows are induced by
the operation of `A` on the `A`-module `M`".

p. 182: "The above canonical homomorphisms give us a canonical homomorphism of graded
`gr_I(A)`-modules `φ: gr⁰_I(M) ⊗_{A/I} gr_I(A) → gr_I(M)`."  Since `Iᵐ/Iᵐ⁺¹` is killed by
`I`, `gr⁰_I(M) ⊗_{A/I} grᵐ_I(A) = (M/IM) ⊗_{A/I} Iᵐ/Iᵐ⁺¹` is canonically `M ⊗_A Iᵐ/Iᵐ⁺¹`, and
`φ` is the direct sum over `m` of the maps `grModMap I M m`.  (Formalization note: `φ` as one map
of graded modules is `AssocGradedModule.grModPhi`; "φ is an isomorphism" is transcribed
throughout as `∀ m, Function.Bijective (grModMap I M m)`, which is equivalent by
`AssocGradedModule.grModPhi_bijective_iff_forall_grModMap_bijective`.) -/
@[blueprint "def:II.1-canonical-phi"
  (statement := /-- Let $A$ be a noetherian ring, $I$ an ideal in $A$ and $M$ an $A$-module.
    The operation of $A$ on $M$ induces canonical homomorphisms
    $M\otimes_A I^m/I^{m+1}\to I^mM/I^{m+1}M$, $x\otimes\bar a\mapsto\overline{ax}$, for all
    $m\ge0$, and hence a canonical homomorphism of graded $\operatorname{gr}_I(A)$-modules
    $\varphi\colon\operatorname{gr}^0_I(M)\otimes_{A/I}\operatorname{gr}_I(A)\to
    \operatorname{gr}_I(M)$. (pp.~181--182.) (Formalization note (encoding): $\varphi$ is the
    direct sum of its homogeneous components $\varphi_m\colon M\otimes_A\operatorname{gr}^m_I(A)
    \to\operatorname{gr}^m_I(M)$, which are the maps formalized
    ($\operatorname{gr}^0_I(M)\otimes_{A/I}\operatorname{gr}^m_I(A)=M\otimes_A
    \operatorname{gr}^m_I(A)$ canonically); ``$\varphi$ is an isomorphism'' is transcribed as
    ``every $\varphi_m$ is bijective'', which is equivalent to $\varphi$ being bijective
    (\cref{lem:II.1-phi-bijective}); $\varphi$ as one map is \cref{def:II.1-phi}.) -/)
  (latexEnv := "definition")]
noncomputable def grModMap (I : Ideal A) (M : Type u) [AddCommGroup M] [Module A M] (m : ℕ) :
    M ⊗[A] GrPiece I m →ₗ[A] GrModPiece I M m :=
  TensorProduct.lift ((Submodule.liftQ _ (grModMapAux I M m) (grModMapAux_ker I M m)).flip)

/-- `grModMap` sends `x ⊗ [a]` to `[a • x]`. -/
theorem grModMap_tmul (I : Ideal A) (M : Type u) [AddCommGroup M] [Module A M] (m : ℕ)
    (x : M) (a : ↥(I ^ m)) :
    grModMap I M m (x ⊗ₜ Submodule.Quotient.mk a) =
      Submodule.Quotient.mk ⟨a.1 • x, Submodule.smul_mem_smul a.2 Submodule.mem_top⟩ := by
  rw [grModMap, TensorProduct.lift.tmul]
  rfl

end GradedModule


/-! ### The graded `gr_I(A)`-module `gr_I(M)` and the canonical map `φ` (pp. 180–182) -/

section ReesModule

variable {A : Type u} [CommRing A] (I : Ideal A) (M : Type u) [AddCommGroup M] [Module A M]

/-- `I^p • ⊤` times `I^q • ⊤`: a product of an element of `I^p` and an element of `I^q M` lies in
`I^(p+q) M`. -/
theorem smul_mem_pow_smul_top {a : A} {y : M} {p q : ℕ} (ha : a ∈ I ^ p)
    (hy : y ∈ I ^ q • (⊤ : Submodule A M)) : a • y ∈ I ^ (p + q) • (⊤ : Submodule A M) := by
  rw [pow_add, Submodule.mul_smul]
  exact Submodule.smul_mem_smul ha hy

/-- The Rees algebra `⊕_m Iᵐ Xᵐ ⊆ A[X]` as a type synonym, so that its quotients and its modules do
not run into the instance diamonds of `Subalgebra` (a ring `ReesAlg I` with the instances of
`reesAlgebra I`). -/
def ReesAlg : Type u := ↥(reesAlgebra I)

noncomputable instance : CommRing (ReesAlg I) := inferInstanceAs (CommRing ↥(reesAlgebra I))

/-- An element of the Rees algebra, as an element of the type synonym. -/
def ReesAlg.mk {I : Ideal A} (q : ↥(reesAlgebra I)) : ReesAlg I := q

/-- The underlying element of the Rees algebra. -/
def ReesAlg.val {I : Ideal A} (q : ReesAlg I) : ↥(reesAlgebra I) := q

noncomputable instance : Algebra A (ReesAlg I) := inferInstanceAs (Algebra A ↥(reesAlgebra I))

noncomputable instance : Module (ReesAlg I) (PolynomialModule A M) :=
  inferInstanceAs (Module ↥(reesAlgebra I) (PolynomialModule A M))

noncomputable instance : IsScalarTower A (ReesAlg I) (PolynomialModule A M) :=
  inferInstanceAs (IsScalarTower A ↥(reesAlgebra I) (PolynomialModule A M))

/-- The Rees module `⊕_m Iᵐ M Xᵐ ⊆ M[X]` of `M` with respect to `I`, a module over the Rees algebra
`⊕_m Iᵐ Xᵐ ⊆ A[X]`. -/
noncomputable def reesModule : Submodule (ReesAlg I) (PolynomialModule A M) where
  carrier := {p | ∀ m, p.coeff m ∈ I ^ m • (⊤ : Submodule A M)}
  add_mem' := fun {p q} hp hq m => by
    show p.coeff m + q.coeff m ∈ _
    exact add_mem (hp m) (hq m)
  zero_mem' := fun m => by
    show (0 : M) ∈ _
    exact zero_mem _
  smul_mem' := fun q p hp m => by
    show (((ReesAlg.val q : reesAlgebra I) : A[X]) • p).coeff m ∈ _
    rw [PolynomialModule.smul_apply]
    refine Submodule.sum_mem _ fun x hx => ?_
    have hx' : x.1 + x.2 = m := Finset.mem_antidiagonal.mp hx
    rw [← hx']
    exact smul_mem_pow_smul_top I M
      ((mem_reesAlgebra_iff I (ReesAlg.val q)).mp (ReesAlg.val q).2 x.1) (hp x.2)

theorem mem_reesModule_iff (p : PolynomialModule A M) :
    p ∈ reesModule I M ↔ ∀ m, p.coeff m ∈ I ^ m • (⊤ : Submodule A M) := Iff.rfl

/-- `y ↦ y Xᵐ` as an `A`-linear map `Iᵐ M → reesModule I M`. -/
noncomputable def reesSingle (m : ℕ) : ↥(I ^ m • (⊤ : Submodule A M)) →ₗ[A] ↥(reesModule I M) where
  toFun y := ⟨PolynomialModule.single A m (y : M), fun n => by
    show (Finsupp.single m (y : M) n) ∈ _
    rw [Finsupp.single_apply]
    split_ifs with h
    · subst h; exact y.2
    · exact zero_mem _⟩
  map_add' x y := Subtype.ext (by simp)
  map_smul' r x := Subtype.ext (by simp [PolynomialModule.single_smul])

theorem coe_reesSingle (m : ℕ) (y : ↥(I ^ m • (⊤ : Submodule A M))) :
    ((reesSingle I M m y : reesModule I M) : PolynomialModule A M) =
      PolynomialModule.single A m (y : M) := rfl

/-- The ideal `I · Rees(A) = ⊕ Iᵐ⁺¹ Xᵐ` of the Rees algebra, with quotient `gr_I(A)`. -/
noncomputable abbrev reesIdeal : Ideal (ReesAlg I) := Ideal.map (algebraMap A (ReesAlg I)) I

theorem reesSingle_smul_algebraMap (m : ℕ) {a : A} (y : ↥(I ^ m • (⊤ : Submodule A M))) :
    reesSingle I M m (a • y) = algebraMap A (ReesAlg I) a • reesSingle I M m y := by
  apply Subtype.ext
  rw [coe_reesSingle]
  show PolynomialModule.single A m (a • (y : M)) =
    (Polynomial.C a) • PolynomialModule.single A m (y : M)
  rw [← Polynomial.monomial_zero_left, PolynomialModule.monomial_smul_single, zero_add]

/-- The elements `y Xᵐ` with `y ∈ Iᵐ⁺¹ M` lie in `(I · Rees(A)) · Rees(M)`. -/
theorem reesSingle_mem_smul_top {m : ℕ} {y : M} (hy : y ∈ I ^ (m + 1) • (⊤ : Submodule A M))
    (hy0 : y ∈ I ^ m • (⊤ : Submodule A M)) :
    reesSingle I M m ⟨y, hy0⟩ ∈
      reesIdeal I • (⊤ : Submodule (ReesAlg I) (reesModule I M)) := by
  rw [pow_succ', Submodule.mul_smul] at hy
  have key : ∃ h : y ∈ I ^ m • (⊤ : Submodule A M), reesSingle I M m ⟨y, h⟩ ∈
      reesIdeal I • (⊤ : Submodule (ReesAlg I) (reesModule I M)) := by
    refine Submodule.smul_induction_on hy (fun a ha y' hy' => ?_)
      (fun x y ⟨hx0, hx⟩ ⟨hy0, hy⟩ => ?_)
    · refine ⟨Submodule.smul_mem _ a hy', ?_⟩
      have h1 : (⟨a • y', Submodule.smul_mem _ a hy'⟩ : ↥(I ^ m • (⊤ : Submodule A M))) =
          a • (⟨y', hy'⟩ : ↥(I ^ m • (⊤ : Submodule A M))) := rfl
      rw [h1, reesSingle_smul_algebraMap I M m]
      exact Submodule.smul_mem_smul (Ideal.mem_map_of_mem _ ha) Submodule.mem_top
    · refine ⟨add_mem hx0 hy0, ?_⟩
      have h1 : (⟨x + y, add_mem hx0 hy0⟩ : ↥(I ^ m • (⊤ : Submodule A M))) =
          ⟨x, hx0⟩ + ⟨y, hy0⟩ := rfl
      rw [h1, map_add]
      exact add_mem hx hy
  obtain ⟨h, hmem⟩ := key
  exact hmem

/-- Every element of the Rees module is the finite sum of its homogeneous components
`[coeff · Xⁱ]`. -/
theorem reesModule_eq_sum (z : reesModule I M) :
    z = ∑ i ∈ (z : PolynomialModule A M).coeff.support,
      reesSingle I M i ⟨(z : PolynomialModule A M).coeff i, z.2 i⟩ := by
  apply Subtype.ext
  rw [AddSubmonoidClass.coe_finsetSum]
  simp only [coe_reesSingle]
  apply PolynomialModule.coeff_injective
  rw [PolynomialModule.coeff_sum]
  simp only [PolynomialModule.coeff_single]
  exact (Finsupp.sum_single (z : PolynomialModule A M).coeff).symm

/-- The submodule `(I · Rees(A)) · Rees(M)` of the Rees module is `⊕ Iᵐ⁺¹ M Xᵐ`: an element of the
Rees module lies in it iff its `m`-th coefficient lies in `Iᵐ⁺¹ M` for every `m`. -/
theorem mem_smul_top_reesModule_iff (z : reesModule I M) :
    z ∈ reesIdeal I • (⊤ : Submodule (ReesAlg I) (reesModule I M)) ↔
      ∀ m, (z : PolynomialModule A M).coeff m ∈ I ^ (m + 1) • (⊤ : Submodule A M) := by
  constructor
  · intro hz
    refine Submodule.smul_induction_on hz (fun j hj w _ m => ?_) (fun x y hx hy m => ?_)
    · rw [Submodule.coe_smul]
      show (((ReesAlg.val j : reesAlgebra I) : A[X]) • (w : PolynomialModule A M)).coeff m ∈ _
      rw [PolynomialModule.smul_apply]
      refine Submodule.sum_mem _ fun x hx => ?_
      have hx' : x.1 + x.2 = m := Finset.mem_antidiagonal.mp hx
      have hj' := (mem_map_algebraMap_reesAlgebra_iff (I := I) (ReesAlg.val j)).mp hj x.1
      have := smul_mem_pow_smul_top I M hj' (w.2 x.2)
      rwa [show x.1 + 1 + x.2 = m + 1 by omega] at this
    · rw [Submodule.coe_add]
      exact add_mem (hx m) (hy m)
  · intro hz
    rw [reesModule_eq_sum I M z]
    exact Submodule.sum_mem _ fun i _ => reesSingle_mem_smul_top I M (hz i) (z.2 i)

end ReesModule

/-! ### `gr_I(M)` -/

section GrModule

variable {A : Type u} [CommRing A] (I : Ideal A) (M : Type u) [AddCommGroup M] [Module A M]

/-- p. 180: "If `M` is an `A`-module, then we associate the following graded `gr_I(A)`-module:
`gr_I(M) = Σ_{m=0}^∞ IᵐM/Iᵐ⁺¹M`."  Encoding: the quotient `Rees(M) / (I · Rees(A)) · Rees(M)` of the
Rees module `Rees(M) = ⊕_m IᵐM Xᵐ ⊆ M[X]` (`reesModule`), which is `⊕_m IᵐM/Iᵐ⁺¹M`, as a module
over `gr_I(A) = Rees(A) / I · Rees(A)` (`AssocGraded I`, the same encoding of `gr_I(A)`).  Its
grading (`homogeneous`, `instDecomposition`, `instGradedSMul`) is the internal direct sum of the
`ofGrModPiece I M m`-images of `grᵐ_I(M)`. -/
@[blueprint "def:II.1-gr-module"
  (statement := /-- If $M$ is an $A$-module, then we associate with $I$ the following graded
    $\operatorname{gr}_I(A)$-module: $\operatorname{gr}_I(M)=\sum_{m=0}^\infty
    I^mM/I^{m+1}M$ (p.~180); its homogeneous part of degree $m$ is
    $\operatorname{gr}^m_I(M)=I^mM/I^{m+1}M$ (\cref{def:II.1-graded-module}). Formalized as the
    quotient $\operatorname{Rees}(M)/(I\cdot\operatorname{Rees}(A))\operatorname{Rees}(M)$ of the
    Rees module $\operatorname{Rees}(M)=\bigoplus_mI^mMX^m\subseteq M[X]$, a module over
    $\operatorname{gr}_I(A)=\operatorname{Rees}(A)/I\cdot\operatorname{Rees}(A)$
    (\cref{def:II.1-associated-graded-algebra}); it is the internal direct sum of its homogeneous
    parts, and $[a]\cdot[y]=[ay]$ for $a\in I^i$, $y\in I^jM$ maps the parts compatibly with the
    grading of $\operatorname{gr}_I(A)$. -/)
  (latexEnv := "definition")]
noncomputable abbrev AssocGradedModule : Type u :=
  ↥(reesModule I M) ⧸ (reesIdeal I • (⊤ : Submodule (ReesAlg I) ↥(reesModule I M)))

namespace AssocGradedModule

/-- `gr_I(M)` is a module over `gr_I(A)` (p. 180: "the following graded `gr_I(A)`-module"). -/
noncomputable instance instModule : Module (AssocGraded I) (AssocGradedModule I M) :=
  inferInstanceAs (Module (ReesAlg I ⧸ reesIdeal I) (↥(reesModule I M) ⧸
    (reesIdeal I • (⊤ : Submodule (ReesAlg I) ↥(reesModule I M)))))

/-- The class in `gr_I(M)` of an element of the Rees module. -/
noncomputable def mk : ↥(reesModule I M) →ₗ[ReesAlg I] AssocGradedModule I M :=
  Submodule.mkQ _

noncomputable instance instIsScalarTower :
    IsScalarTower A (AssocGraded I) (AssocGradedModule I M) :=
  inferInstanceAs (IsScalarTower A (ReesAlg I ⧸ reesIdeal I) (AssocGradedModule I M))

/-- `gr_I(M)` is an `A/I`-module (through `A/I → gr_I(A)`); its homogeneous parts are the
`A/I`-modules `grᵐ_I(M)`. -/
noncomputable instance instModuleQuotient : Module (A ⧸ I) (AssocGradedModule I M) :=
  Module.compHom _ (algebraMap (A ⧸ I) (AssocGraded I))

theorem quotient_smul_def (r : A ⧸ I) (x : AssocGradedModule I M) :
    r • x = algebraMap (A ⧸ I) (AssocGraded I) r • x := rfl

instance instIsScalarTowerQuotient :
    IsScalarTower (A ⧸ I) (AssocGraded I) (AssocGradedModule I M) :=
  ⟨fun r s x => by rw [Algebra.smul_def, mul_smul]; rfl⟩

instance instIsScalarTowerQuotient' : IsScalarTower A (A ⧸ I) (AssocGradedModule I M) :=
  ⟨fun a r x => by
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective r
    rw [quotient_smul_def, quotient_smul_def, Algebra.smul_def a (Ideal.Quotient.mk I r), map_mul,
      mul_smul, ← algebraMap_smul (AssocGraded I) a (_ • x),
      ← IsScalarTower.algebraMap_apply A (A ⧸ I) (AssocGraded I)]⟩

/-- `y ↦ [y Xᵐ]` as an `A`-linear map `Iᵐ M → gr_I(M)`. -/
noncomputable def ofGrModPieceA (m : ℕ) :
    ↥(I ^ m • (⊤ : Submodule A M)) →ₗ[A] AssocGradedModule I M :=
  (Submodule.mkQ (reesIdeal I • (⊤ : Submodule (ReesAlg I) ↥(reesModule I M)))).restrictScalars A ∘ₗ
    reesSingle I M m

/-- The canonical `A/I`-linear map `grᵐ_I(M) = IᵐM/Iᵐ⁺¹M → gr_I(M)`, `[y] ↦ [y Xᵐ]`. -/
noncomputable def ofGrModPiece (m : ℕ) : GrModPiece I M m →ₗ[A ⧸ I] AssocGradedModule I M :=
  LinearMap.extendScalarsOfSurjective (Ideal.Quotient.mk_surjective (I := I))
    (Submodule.liftQ _ (ofGrModPieceA I M m) fun y hy => by
      rw [LinearMap.mem_ker]
      exact (Submodule.Quotient.mk_eq_zero _).mpr (reesSingle_mem_smul_top I M
        (Submodule.mem_comap.mp hy) y.2))

theorem ofGrModPiece_mk (m : ℕ) (y : ↥(I ^ m • (⊤ : Submodule A M))) :
    ofGrModPiece I M m (Submodule.Quotient.mk y) =
      Submodule.Quotient.mk (reesSingle I M m y) := rfl

/-- The `n`-th coefficient `z ↦ (coeff z n : Iⁿ M)` of an element of the Rees module,
`A`-linearly. -/
noncomputable def reesModuleCoeff (n : ℕ) :
    ↥(reesModule I M) →ₗ[A] ↥(I ^ n • (⊤ : Submodule A M)) where
  toFun z := ⟨(z : PolynomialModule A M).coeff n, z.2 n⟩
  map_add' x y := Subtype.ext (by simp)
  map_smul' r x := Subtype.ext rfl

/-- The `A`-linear degree-`n` projection `gr_I(M) → IⁿM/Iⁿ⁺¹M`, `[z] ↦ [coeff z n]`. -/
noncomputable def grModProjA (n : ℕ) : AssocGradedModule I M →ₗ[A] GrModPiece I M n :=
  (Submodule.liftQ ((reesIdeal I • (⊤ : Submodule (ReesAlg I) ↥(reesModule I M))).restrictScalars A)
      ((Submodule.mkQ _).comp (reesModuleCoeff I M n)) (fun z hz => by
        rw [LinearMap.mem_ker, LinearMap.comp_apply, Submodule.mkQ_apply,
          Submodule.Quotient.mk_eq_zero]
        exact (mem_smul_top_reesModule_iff I M z).mp hz n)).comp
    (Submodule.Quotient.restrictScalarsEquiv A _).symm.toLinearMap

/-- The `A/I`-linear degree-`n` projection `gr_I(M) → grⁿ_I(M)`. -/
noncomputable def grModProj (n : ℕ) : AssocGradedModule I M →ₗ[A ⧸ I] GrModPiece I M n :=
  LinearMap.extendScalarsOfSurjective (Ideal.Quotient.mk_surjective (I := I)) (grModProjA I M n)

theorem grModProj_mk (n : ℕ) (z : ↥(reesModule I M)) :
    grModProj I M n (Submodule.Quotient.mk z) = Submodule.Quotient.mk (reesModuleCoeff I M n z) :=
  rfl

theorem grModProj_ofGrModPiece_same (n : ℕ) (y : GrModPiece I M n) :
    grModProj I M n (ofGrModPiece I M n y) = y := by
  induction y using Submodule.Quotient.induction_on with
  | H x =>
    rw [ofGrModPiece_mk, grModProj_mk]
    congr 1
    exact Subtype.ext (by simp [reesModuleCoeff, coe_reesSingle])

theorem grModProj_ofGrModPiece_ne {n i : ℕ} (h : i ≠ n) (y : GrModPiece I M i) :
    grModProj I M n (ofGrModPiece I M i y) = 0 := by
  induction y using Submodule.Quotient.induction_on with
  | H x =>
    rw [ofGrModPiece_mk, grModProj_mk, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap,
      Submodule.subtype_apply]
    simp [reesModuleCoeff, coe_reesSingle, h]

/-- `⨁ₙ grⁿ_I(M) → gr_I(M)`, `A/I`-linearly, assembling the `ofGrModPiece I M n`. -/
noncomputable def toGrMod : DirectSum ℕ (fun n => GrModPiece I M n) →ₗ[A ⧸ I]
    AssocGradedModule I M :=
  DirectSum.toModule (A ⧸ I) ℕ (AssocGradedModule I M) (ofGrModPiece I M)

theorem grModProj_toGrMod (n : ℕ) (x : DirectSum ℕ (fun n => GrModPiece I M n)) :
    grModProj I M n (toGrMod I M x) = x n := by
  have : (grModProj I M n).comp (toGrMod I M) =
      DirectSum.component (A ⧸ I) ℕ (fun n => GrModPiece I M n) n := by
    refine DirectSum.linearMap_ext _ fun i => LinearMap.ext fun y => ?_
    simp only [LinearMap.comp_apply, toGrMod, DirectSum.toModule_lof, DirectSum.component.of]
    split_ifs with h
    · subst h
      exact grModProj_ofGrModPiece_same I M i y
    · exact grModProj_ofGrModPiece_ne I M h y
  exact LinearMap.congr_fun this x

/-- `gr_I(M) = ⊕ₙ grⁿ_I(M)`: the canonical map `⨁ₙ IⁿM/Iⁿ⁺¹M → gr_I(M)` is bijective. -/
theorem toGrMod_bijective : Function.Bijective (toGrMod I M) := by
  constructor
  · intro x y hxy
    refine DirectSum.ext fun n => ?_
    rw [← grModProj_toGrMod I M n x, ← grModProj_toGrMod I M n y, hxy]
  · intro z
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ z
    refine ⟨∑ i ∈ (z : PolynomialModule A M).coeff.support, DirectSum.lof (A ⧸ I) ℕ
      (fun n => GrModPiece I M n) i (Submodule.Quotient.mk (reesModuleCoeff I M i z)), ?_⟩
    rw [map_sum]
    conv_rhs => rw [reesModule_eq_sum I M z, ← Submodule.mkQ_apply, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [toGrMod, DirectSum.toModule_lof, ofGrModPiece_mk]
    rfl

/-- The homogeneous part of degree `n` of `gr_I(M)` (p. 180: "The homogeneous part of degree m of
gr_I(M), that is IᵐM/Iᵐ⁺¹M, will be denoted by grᵐ_I(M)"): the `A/I`-submodule of `gr_I(M)`
consisting of the classes of the elements `y Xⁿ`, `y ∈ IⁿM`. -/
noncomputable def homogeneous (n : ℕ) : Submodule (A ⧸ I) (AssocGradedModule I M) :=
  LinearMap.range (ofGrModPiece I M n)

theorem ofGrModPiece_injective (n : ℕ) : Function.Injective (ofGrModPiece I M n) := by
  intro x y hxy
  rw [← grModProj_ofGrModPiece_same I M n x, ← grModProj_ofGrModPiece_same I M n y, hxy]

/-- `grⁿ_I(M) ≅` the degree-`n` part of `gr_I(M)`. -/
noncomputable def grModPieceEquiv (n : ℕ) : GrModPiece I M n ≃ₗ[A ⧸ I] homogeneous I M n :=
  LinearEquiv.ofInjective _ (ofGrModPiece_injective I M n)

theorem reesAlg_smul_reesSingle (i j : ℕ) (a : A) (ha : a ∈ I ^ i)
    (y : ↥(I ^ j • (⊤ : Submodule A M))) :
    ReesAlg.mk (⟨Polynomial.monomial i a, reesAlgebra.monomial_mem.mpr ha⟩ : ↥(reesAlgebra I)) •
        reesSingle I M j y =
      reesSingle I M (i + j) ⟨a • (y : M), smul_mem_pow_smul_top I M ha y.2⟩ := by
  apply Subtype.ext
  rw [coe_reesSingle]
  show (Polynomial.monomial i a) • PolynomialModule.single A j (y : M) =
    PolynomialModule.single A (i + j) (a • (y : M))
  rw [PolynomialModule.monomial_smul_single]

/-- The action of `gr_I(A)` on `gr_I(M)` in terms of the pieces: `[a Xⁱ] · [y Xʲ] = [a y Xⁱ⁺ʲ]`
(`a ∈ Iⁱ`, `y ∈ IʲM`). -/
theorem mk_smul_ofGrModPiece (i j : ℕ) (a : A) (ha : a ∈ I ^ i)
    (y : ↥(I ^ j • (⊤ : Submodule A M))) :
    AssocGraded.mk I i a ha • ofGrModPiece I M j (Submodule.Quotient.mk y) =
      ofGrModPiece I M (i + j) (Submodule.Quotient.mk
        ⟨a • (y : M), smul_mem_pow_smul_top I M ha y.2⟩) := by
  rw [ofGrModPiece_mk, ofGrModPiece_mk, ← reesAlg_smul_reesSingle I M i j a ha y]
  rfl

theorem ofGrModPiece_mem_homogeneous (n : ℕ) (y : GrModPiece I M n) :
    ofGrModPiece I M n y ∈ homogeneous I M n := LinearMap.mem_range_self _ y

/-- `gr_I(M) = ⨁ₙ grⁿ_I(M)` as an internal direct sum of the homogeneous parts. -/
theorem isInternal_homogeneous : DirectSum.IsInternal (homogeneous I M) := by
  classical
  let E : (DirectSum ℕ fun n => GrModPiece I M n) ≃ₗ[A ⧸ I]
      DirectSum ℕ fun n => homogeneous I M n :=
    DFinsupp.mapRange.linearEquiv (grModPieceEquiv I M)
  have key' : (DirectSum.coeLinearMap (homogeneous I M)) ∘ₗ E.toLinearMap = toGrMod I M := by
    refine DirectSum.linearMap_ext _ fun n => LinearMap.ext fun u => ?_
    change DirectSum.coeLinearMap (homogeneous I M) (DFinsupp.mapRange.linearEquiv
      (grModPieceEquiv I M) (DirectSum.lof (A ⧸ I) ℕ (fun n => GrModPiece I M n) n u)) =
      toGrMod I M (DirectSum.lof (A ⧸ I) ℕ (fun n => GrModPiece I M n) n u)
    rw [toGrMod, DirectSum.toModule_lof, DFinsupp.mapRange.linearEquiv_apply]
    erw [DFinsupp.mapRange_single]
    exact (DirectSum.coeLinearMap_of (homogeneous I M) n (grModPieceEquiv I M n u)).trans rfl
  have key : (DirectSum.coeLinearMap (homogeneous I M)) ∘ E = toGrMod I M :=
    congrArg DFunLike.coe key'
  have h : Function.Bijective ((DirectSum.coeLinearMap (homogeneous I M)) ∘ E) := by
    rw [key]; exact toGrMod_bijective I M
  exact (Function.Bijective.of_comp_iff _ E.bijective).mp h

/-- The grading of the module `gr_I(M)`: the decomposition into the homogeneous parts. -/
noncomputable instance instDecomposition : DirectSum.Decomposition (homogeneous I M) :=
  (isInternal_homogeneous I M).chooseDecomposition

/-- The grading of `gr_I(M)` is compatible with the grading of `gr_I(A)`: `gr_I(M)` is a graded
`gr_I(A)`-module (p. 180). -/
instance instGradedSMul : SetLike.GradedSMul (AssocGraded.homogeneous I) (homogeneous I M) where
  smul_mem := by
    rintro i j _ _ ⟨u, rfl⟩ ⟨v, rfl⟩
    induction u using Submodule.Quotient.induction_on with
    | H a =>
      induction v using Submodule.Quotient.induction_on with
      | H y =>
        rw [AssocGraded.ofGrPiece_mk, mk_smul_ofGrModPiece I M i j a.1 a.2 y, vadd_eq_add]
        exact ofGrModPiece_mem_homogeneous I M (i + j) _

theorem mem_ideal_pow_zero_smul_top (x : M) : x ∈ I ^ 0 • (⊤ : Submodule A M) := by
  rw [pow_zero, Ideal.one_eq_top, Submodule.top_smul]
  exact Submodule.mem_top

/-- The class of `x ∈ M` in `gr⁰_I(M) = M/IM`. -/
noncomputable def grModZeroMk (x : M) : GrModPiece I M 0 :=
  Submodule.Quotient.mk ⟨x, mem_ideal_pow_zero_smul_top I M x⟩

theorem grModZeroMk_surjective : Function.Surjective (grModZeroMk I M) := by
  intro w
  induction w using Submodule.Quotient.induction_on with
  | H x => exact ⟨x.1, rfl⟩

/-- The `A/I`-bilinear map `(w, α) ↦ α · ι₀(w)` of the definition of `φ`, `ι₀ : gr⁰_I(M) → gr_I(M)`
the inclusion of the degree-`0` part. -/
noncomputable def grModPhiBilin :
    GrModPiece I M 0 →ₗ[A ⧸ I] AssocGraded I →ₗ[A ⧸ I] AssocGradedModule I M :=
  LinearMap.mk₂ (A ⧸ I) (fun w α => α • ofGrModPiece I M 0 w)
    (fun w w' α => by rw [map_add, smul_add])
    (fun c w α => by
      rw [map_smul, smul_comm])
    (fun w α α' => by rw [add_smul])
    (fun c w α => by rw [smul_assoc])

/-- p. 182: "The above canonical homomorphisms give us a canonical homomorphism of graded
`gr_I(A)`-modules: `φ: gr⁰_I(M) ⊗_{A/I} gr_I(A) → gr_I(M)`", as one map: `w ⊗ α ↦ α · w` (the
`gr_I(A)`-linear extension of the inclusion `gr⁰_I(M) → gr_I(M)` of the degree-`0` part; the module
structure on the source is by multiplication on the factor `gr_I(A)`: `grModPhi_tmul_mul`).  It
preserves the grading (`grModPhi_tmul_mem_homogeneous`). -/
@[blueprint "def:II.1-phi"
  (statement := /-- The canonical homomorphism of graded $\operatorname{gr}_I(A)$-modules
    $\varphi\colon\operatorname{gr}^0_I(M)\otimes_{A/I}\operatorname{gr}_I(A)\to
    \operatorname{gr}_I(M)$ (p.~182), as one map: $\varphi(w\otimes\alpha)=\alpha\cdot w$, where
    $\operatorname{gr}^0_I(M)=M/IM\subseteq\operatorname{gr}_I(M)$ is the degree-$0$ part. It is
    $\operatorname{gr}_I(A)$-linear for the multiplication on the second factor and maps
    $\operatorname{gr}^0_I(M)\otimes\operatorname{gr}^m_I(A)$ into $\operatorname{gr}^m_I(M)$. -/)
  (latexEnv := "definition")]
noncomputable def grModPhi :
    GrModPiece I M 0 ⊗[A ⧸ I] AssocGraded I →ₗ[A ⧸ I] AssocGradedModule I M :=
  TensorProduct.lift (grModPhiBilin I M)

theorem grModPhi_tmul (w : GrModPiece I M 0) (α : AssocGraded I) :
    grModPhi I M (w ⊗ₜ α) = α • ofGrModPiece I M 0 w := by
  rw [grModPhi, TensorProduct.lift.tmul]
  rfl

/-- `φ` is a homomorphism of `gr_I(A)`-modules: `φ (w ⊗ βα) = β · φ (w ⊗ α)`. -/
theorem grModPhi_tmul_mul (w : GrModPiece I M 0) (β α : AssocGraded I) :
    grModPhi I M (w ⊗ₜ (β * α)) = β • grModPhi I M (w ⊗ₜ α) := by
  rw [grModPhi_tmul, grModPhi_tmul, mul_smul]

/-- `φ` preserves degrees: it maps `gr⁰_I(M) ⊗ grᵐ_I(A)` into `grᵐ_I(M)`. -/
theorem grModPhi_tmul_mem_homogeneous (m : ℕ) (w : GrModPiece I M 0) {α : AssocGraded I}
    (hα : α ∈ AssocGraded.homogeneous I m) : grModPhi I M (w ⊗ₜ α) ∈ homogeneous I M m := by
  rw [grModPhi_tmul]
  have h := SetLike.GradedSMul.smul_mem (A := AssocGraded.homogeneous I) (B := homogeneous I M)
    (i := m) (j := 0) hα (ofGrModPiece_mem_homogeneous I M 0 w)
  rwa [vadd_eq_add, Nat.add_zero] at h

/-- The degree-`m` component of `φ`: `φₘ : gr⁰_I(M) ⊗_{A/I} grᵐ_I(A) → grᵐ_I(M)`,
`w ⊗ [a] ↦ [a w]`. -/
noncomputable def grModPhiPiece (m : ℕ) :
    GrModPiece I M 0 ⊗[A ⧸ I] GrPiece I m →ₗ[A ⧸ I] GrModPiece I M m :=
  TensorProduct.lift (LinearMap.mk₂ (A ⧸ I)
    (fun w u => grModProj I M m (AssocGraded.ofGrPiece I m u • ofGrModPiece I M 0 w))
    (fun w w' u => by rw [map_add, smul_add, map_add])
    (fun c w u => by rw [map_smul (ofGrModPiece I M 0), smul_comm, map_smul (grModProj I M m)])
    (fun w u u' => by rw [map_add, add_smul, map_add])
    (fun c w u => by
      rw [map_smul (AssocGraded.ofGrPiece I m), smul_assoc, map_smul (grModProj I M m)]))

theorem grModPhiPiece_tmul (m : ℕ) (w : GrModPiece I M 0) (u : GrPiece I m) :
    grModPhiPiece I M m (w ⊗ₜ u) =
      grModProj I M m (AssocGraded.ofGrPiece I m u • ofGrModPiece I M 0 w) := by
  rw [grModPhiPiece, TensorProduct.lift.tmul]
  rfl

theorem ofGrModPiece_grModProj_of_mem_homogeneous (m : ℕ) {z : AssocGradedModule I M}
    (hz : z ∈ homogeneous I M m) : ofGrModPiece I M m (grModProj I M m z) = z := by
  obtain ⟨y, rfl⟩ := hz
  rw [grModProj_ofGrModPiece_same]

/-- `φ` on `gr⁰_I(M) ⊗ grᵐ_I(A)` is `φₘ`, followed by `grᵐ_I(M) ⊆ gr_I(M)`. -/
theorem grModPhi_tmul_ofGrPiece (m : ℕ) (w : GrModPiece I M 0) (u : GrPiece I m) :
    grModPhi I M (w ⊗ₜ AssocGraded.ofGrPiece I m u) =
      ofGrModPiece I M m (grModPhiPiece I M m (w ⊗ₜ u)) := by
  have hmem : AssocGraded.ofGrPiece I m u • ofGrModPiece I M 0 w ∈ homogeneous I M m := by
    rw [← grModPhi_tmul]
    exact grModPhi_tmul_mem_homogeneous I M m w ⟨u, rfl⟩
  rw [grModPhiPiece_tmul, ofGrModPiece_grModProj_of_mem_homogeneous I M m hmem, grModPhi_tmul]

/-- "`φ` is the direct sum of the canonical homomorphisms `φₘ`": `φ` is bijective if and only if
every `φₘ` is. -/
theorem grModPhi_bijective_iff :
    Function.Bijective (grModPhi I M) ↔ ∀ m, Function.Bijective (grModPhiPiece I M m) := by
  classical
  let eSrc : (⨁ m, GrModPiece I M 0 ⊗[A ⧸ I] GrPiece I m) ≃ₗ[A ⧸ I]
      GrModPiece I M 0 ⊗[A ⧸ I] AssocGraded I :=
    (TensorProduct.directSumRight (A ⧸ I) (A ⧸ I) (GrModPiece I M 0)
      (fun m => GrPiece I m)).symm ≪≫ₗ
    LinearEquiv.lTensor (GrModPiece I M 0) (LinearEquiv.ofBijective (toGr I) (toGr_bijective I))
  let eTgt := LinearEquiv.ofBijective (toGrMod I M) (toGrMod_bijective I M)
  let F : (⨁ m, GrModPiece I M 0 ⊗[A ⧸ I] GrPiece I m) →ₗ[A ⧸ I] ⨁ m, GrModPiece I M m :=
    DirectSum.lmap fun m => grModPhiPiece I M m
  have key : ∀ x, grModPhi I M (eSrc x) = eTgt (F x) := by
    intro x
    have : (grModPhi I M).comp eSrc.toLinearMap = (eTgt.toLinearMap).comp F := by
      refine DirectSum.linearMap_ext _ fun m => ?_
      refine TensorProduct.ext' fun w u => ?_
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, eTgt, F, eSrc,
        LinearEquiv.trans_apply, TensorProduct.directSumRight_symm_lof_tmul,
        LinearEquiv.lTensor_tmul, LinearEquiv.ofBijective_apply, DirectSum.lmap_lof, toGr,
        toGrMod, DirectSum.toModule_lof]
      exact grModPhi_tmul_ofGrPiece I M m w u
    exact LinearMap.congr_fun this x
  have hcomp : (⇑(grModPhi I M) ∘ ⇑eSrc) = ⇑eTgt ∘ ⇑F := funext key
  rw [← Function.Bijective.of_comp_iff _ eSrc.bijective, hcomp,
    Function.Bijective.of_comp_iff' eTgt.bijective]
  exact ⟨fun h m => ⟨(DirectSum.lmap_injective _).mp h.1 m, (DirectSum.lmap_surjective _).mp h.2 m⟩,
    fun h => ⟨(DirectSum.lmap_injective _).mpr fun m => (h m).1,
      (DirectSum.lmap_surjective _).mpr fun m => (h m).2⟩⟩

/-- `x ↦ [x]`, `A`-linearly `M → gr⁰_I(M) = M/IM`. -/
noncomputable def grModZeroMkLinear : M →ₗ[A] GrModPiece I M 0 where
  toFun := grModZeroMk I M
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem ker_grModZeroMkLinear :
    LinearMap.ker (grModZeroMkLinear I M) = I • (⊤ : Submodule A M) := by
  ext x
  rw [LinearMap.mem_ker]
  show Submodule.Quotient.mk (⟨x, mem_ideal_pow_zero_smul_top I M x⟩ :
      ↥(I ^ 0 • (⊤ : Submodule A M))) = 0 ↔ _
  rw [Submodule.Quotient.mk_eq_zero, Submodule.mem_comap, Submodule.subtype_apply, pow_one]

/-- `gr⁰_I(M) = M/IM`, `(A/I) ⊗_A M ≅ gr⁰_I(M)`, `s ⊗ x ↦ s · [x]`, `A/I`-linearly. -/
noncomputable def zeroPieceTensorEquiv : (A ⧸ I) ⊗[A] M ≃ₗ[A ⧸ I] GrModPiece I M 0 :=
  LinearEquiv.extendScalarsOfSurjective (Ideal.Quotient.mk_surjective (I := I))
    ((TensorProduct.quotTensorEquivQuotSMul M I).trans
      ((Submodule.quotEquivOfEq _ _ (ker_grModZeroMkLinear I M).symm).trans
        (LinearMap.quotKerEquivOfSurjective _ (grModZeroMk_surjective I M))))

theorem zeroPieceTensorEquiv_one_tmul (x : M) :
    zeroPieceTensorEquiv I M ((1 : A ⧸ I) ⊗ₜ[A] x) = grModZeroMk I M x := by
  show (LinearMap.quotKerEquivOfSurjective _ (grModZeroMk_surjective I M))
    (Submodule.quotEquivOfEq _ _ (ker_grModZeroMkLinear I M).symm
      (TensorProduct.quotTensorEquivQuotSMul M I ((1 : A ⧸ I) ⊗ₜ[A] x))) = _
  rw [TensorProduct.quotTensorEquivQuotSMul_mk_one_tmul]
  rfl

/-- `M ⊗_A grᵐ_I(A) ≅ gr⁰_I(M) ⊗_{A/I} grᵐ_I(A)`: for an `A/I`-module `Q`,
`(M/IM) ⊗_{A/I} Q = M ⊗_A Q` (the identification used tacitly on p. 182: "`φ` is the direct sum of
the canonical homomorphisms" built from `M ⊗_A grᵐ_I(A) → grᵐ_I(M)`). -/
noncomputable def zeroPieceTensorGrPieceEquiv (m : ℕ) :
    GrModPiece I M 0 ⊗[A ⧸ I] GrPiece I m ≃ₗ[A] M ⊗[A] GrPiece I m :=
  (((TensorProduct.comm (A ⧸ I) (GrModPiece I M 0) (GrPiece I m)) ≪≫ₗ
    (TensorProduct.congr (LinearEquiv.refl (A ⧸ I) (GrPiece I m))
      (zeroPieceTensorEquiv I M).symm) ≪≫ₗ
    TensorProduct.AlgebraTensorModule.cancelBaseChange A (A ⧸ I) (A ⧸ I) (GrPiece I m) M
      ).restrictScalars A) ≪≫ₗ
    TensorProduct.comm A (GrPiece I m) M

theorem zeroPieceTensorGrPieceEquiv_tmul (m : ℕ) (x : M) (u : GrPiece I m) :
    zeroPieceTensorGrPieceEquiv I M m (grModZeroMk I M x ⊗ₜ[A ⧸ I] u) = x ⊗ₜ[A] u := by
  have h : (zeroPieceTensorEquiv I M).symm (grModZeroMk I M x) = (1 : A ⧸ I) ⊗ₜ[A] x :=
    (LinearEquiv.symm_apply_eq _).mpr (zeroPieceTensorEquiv_one_tmul I M x).symm
  simp only [zeroPieceTensorGrPieceEquiv, LinearEquiv.trans_apply,
    LinearEquiv.restrictScalars_apply,
    TensorProduct.comm_tmul, TensorProduct.congr_tmul, LinearEquiv.refl_apply, h,
    TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul, one_smul]

theorem zeroPieceTensorGrPieceEquiv_symm_tmul (m : ℕ) (x : M) (u : GrPiece I m) :
    (zeroPieceTensorGrPieceEquiv I M m).symm (x ⊗ₜ[A] u) = grModZeroMk I M x ⊗ₜ[A ⧸ I] u :=
  (LinearEquiv.symm_apply_eq _).mpr (zeroPieceTensorGrPieceEquiv_tmul I M m x u).symm

/-- `φₘ` and the canonical map `M ⊗_A grᵐ_I(A) → grᵐ_I(M)` of p. 181 correspond under
`gr⁰_I(M) ⊗_{A/I} grᵐ_I(A) = M ⊗_A grᵐ_I(A)`: `x ⊗ [a] ↦ [a x]`. -/
theorem grModPhiPiece_zeroPieceTensorGrPieceEquiv_symm (m : ℕ) (x : M) (a : ↥(I ^ m)) :
    grModPhiPiece I M m ((zeroPieceTensorGrPieceEquiv I M m).symm
      (x ⊗ₜ[A] (Submodule.Quotient.mk a : GrPiece I m))) =
      Submodule.Quotient.mk (⟨a.1 • x, Submodule.smul_mem_smul a.2 Submodule.mem_top⟩ :
        ↥(I ^ m • (⊤ : Submodule A M))) := by
  rw [zeroPieceTensorGrPieceEquiv_symm_tmul, grModPhiPiece_tmul, AssocGraded.ofGrPiece_mk]
  have h0 : ofGrModPiece I M 0 (grModZeroMk I M x) = ofGrModPiece I M 0
      (Submodule.Quotient.mk ⟨x, mem_ideal_pow_zero_smul_top I M x⟩) := rfl
  rw [h0, mk_smul_ofGrModPiece I M m 0 a.1 a.2]
  exact grModProj_ofGrModPiece_same I M m _

/-- The canonical map `grModMap` (`M ⊗_A grᵐ_I(A) → grᵐ_I(M)`) is `φₘ` composed with the
identification `M ⊗_A grᵐ_I(A) = gr⁰_I(M) ⊗_{A/I} grᵐ_I(A)`. -/
theorem grModMap_eq_grModPhiPiece_comp (m : ℕ) :
    ⇑(grModMap I M m) = ⇑(grModPhiPiece I M m) ∘ ⇑(zeroPieceTensorGrPieceEquiv I M m).symm := by
  funext z
  induction z using TensorProduct.inductionOn with
  | tmul x u =>
    induction u using Submodule.Quotient.induction_on with
    | H a =>
      rw [Function.comp_apply, grModPhiPiece_zeroPieceTensorGrPieceEquiv_symm, grModMap_tmul]
  | add z z' hz hz' =>
    rw [map_add, hz, hz', Function.comp_apply, Function.comp_apply, Function.comp_apply, map_add,
      map_add]

theorem grModMap_bijective_iff_grModPhiPiece_bijective (m : ℕ) :
    Function.Bijective (grModMap I M m) ↔ Function.Bijective (grModPhiPiece I M m) := by
  rw [grModMap_eq_grModPhiPiece_comp]
  exact Function.Bijective.of_comp_iff _ (zeroPieceTensorGrPieceEquiv I M m).symm.bijective

/-- "`φ` is an isomorphism" (condition (iii) of Lemma 2, p. 182) is equivalent to the
degree-wise statement used throughout the formalization: every canonical map
`M ⊗_A grᵐ_I(A) → grᵐ_I(M)` (`grModMap`) is bijective.  Gap filled: the paper passes tacitly from
`φ` to its homogeneous components ("`φ` is the direct sum of the canonical homomorphisms `φₙ`",
p. 182) and uses `gr⁰_I(M) ⊗_{A/I} grᵐ_I(A) = M ⊗_A grᵐ_I(A)`. -/
@[blueprint "lem:II.1-phi-bijective"
  (statement := /-- The homomorphism $\varphi\colon\operatorname{gr}^0_I(M)\otimes_{A/I}
    \operatorname{gr}_I(A)\to\operatorname{gr}_I(M)$ is bijective if and only if each of the
    canonical maps $M\otimes_A\operatorname{gr}^m_I(A)\to\operatorname{gr}^m_I(M)$ is bijective. -/)
  (proof := /-- $\varphi$ is the direct sum over $m$ of its homogeneous components
    $\varphi_m\colon\operatorname{gr}^0_I(M)\otimes_{A/I}\operatorname{gr}^m_I(A)\to
    \operatorname{gr}^m_I(M)$ (the source is $\bigoplus_m$ of these tensor products since
    $\operatorname{gr}_I(A)=\bigoplus_m\operatorname{gr}^m_I(A)$, the target is
    $\bigoplus_m\operatorname{gr}^m_I(M)$), and a direct sum of maps is bijective if and only if
    each is. For an $A/I$-module $Q$, $(M/IM)\otimes_{A/I}Q=M\otimes_AQ$, and under this
    identification $\varphi_m$ is the canonical map $x\otimes[a]\mapsto[ax]$. -/)
  (latexEnv := "lemma")]
theorem grModPhi_bijective_iff_forall_grModMap_bijective :
    Function.Bijective (grModPhi I M) ↔ ∀ m, Function.Bijective (grModMap I M m) :=
  (grModPhi_bijective_iff I M).trans
    (forall_congr' fun m => (grModMap_bijective_iff_grModPhiPiece_bijective I M m).symm)

/-- Every homogeneous element `[y Xᵐ]` of `gr_I(M)` is in the image of `φ`: for `y = a x` with
`a ∈ Iᵐ`, it is `φ ([x] ⊗ [a Xᵐ])`. -/
theorem ofGrModPiece_mem_range_grModPhi (m : ℕ) (y : GrModPiece I M m) :
    ofGrModPiece I M m y ∈ LinearMap.range (grModPhi I M) := by
  induction y using Submodule.Quotient.induction_on with
  | H v =>
    obtain ⟨v, hv⟩ := v
    have key : ∃ hv0 : v ∈ I ^ m • (⊤ : Submodule A M),
        ofGrModPiece I M m (Submodule.Quotient.mk ⟨v, hv0⟩) ∈ LinearMap.range (grModPhi I M) := by
      refine Submodule.smul_induction_on hv (fun a ha x _ => ?_) (fun x y ⟨hx0, hx⟩ ⟨hy0, hy⟩ => ?_)
      · refine ⟨Submodule.smul_mem_smul ha Submodule.mem_top, ⟨grModZeroMk I M x ⊗ₜ
          AssocGraded.ofGrPiece I m (Submodule.Quotient.mk ⟨a, ha⟩), ?_⟩⟩
        rw [grModPhi_tmul, AssocGraded.ofGrPiece_mk]
        exact (mk_smul_ofGrModPiece I M m 0 a ha ⟨x, mem_ideal_pow_zero_smul_top I M x⟩)
      · refine ⟨add_mem hx0 hy0, ?_⟩
        have h1 : (⟨x + y, add_mem hx0 hy0⟩ : ↥(I ^ m • (⊤ : Submodule A M))) =
            ⟨x, hx0⟩ + ⟨y, hy0⟩ := rfl
        rw [h1, Submodule.Quotient.mk_add, map_add]
        exact add_mem hx hy
    obtain ⟨hv0, h⟩ := key
    exact h

/-- `φ : gr⁰_I(M) ⊗_{A/I} gr_I(A) → gr_I(M)` is surjective ("`gr_I(M)` is generated over `gr_I(A)`
by `gr⁰_I(M)`"). -/
theorem grModPhi_surjective : Function.Surjective (grModPhi I M) := by
  intro z
  obtain ⟨x, rfl⟩ := (toGrMod_bijective I M).2 z
  have : ∀ x : DirectSum ℕ (fun n => GrModPiece I M n),
      toGrMod I M x ∈ LinearMap.range (grModPhi I M) := by
    intro x
    induction x using DirectSum.induction_on with
    | zero => rw [map_zero]; exact zero_mem _
    | of i y =>
      have : toGrMod I M (DirectSum.of (fun n => GrModPiece I M n) i y) =
          ofGrModPiece I M i y := by
        rw [← DirectSum.lof_eq_of (A ⧸ I), toGrMod, DirectSum.toModule_lof]
      rw [this]
      exact ofGrModPiece_mem_range_grModPhi I M i y
    | add x y hx hy => rw [map_add]; exact add_mem hx hy
  exact this x

/-- p. 180: "If `M` is an `A`-module of finite type, then `gr_I(M)` is a `gr_I(A)`-module of finite
type" (stated without proof in the paper): `gr_I(M)` is generated over `gr_I(A)` by (the image of)
a finite set of generators of `gr⁰_I(M) = M/IM` over `A/I`, by the surjectivity of `φ`.  Gap
filled. -/
@[blueprint "lem:II.1-gr-module-finite"
  (statement := /-- Let $A$ be a noetherian ring, $I$ an ideal in $A$ and $M$ an $A$-module of
    finite type. Then $\operatorname{gr}_I(M)$ is a $\operatorname{gr}_I(A)$-module of finite
    type. (p.~180.) -/)
  (proof := /-- The paper states this without proof. The homomorphism $\varphi$ is surjective
    (an element of $I^mM$ is a sum of elements $ax$ with $a\in I^m$, and $[ax]=[a]\cdot[x]$), so
    $\operatorname{gr}_I(M)$ is generated over $\operatorname{gr}_I(A)$ by the image of
    $\operatorname{gr}^0_I(M)=M/IM$, which is of finite type over $A/I$. -/)
  (latexEnv := "lemma")]
theorem finite_of_finite [IsNoetherianRing A] [Module.Finite A M] :
    Module.Finite (AssocGraded I) (AssocGradedModule I M) := by
  classical
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := A ⧸ I) (M := GrModPiece I M 0)
  refine Module.finite_def.mpr ⟨s.image (ofGrModPiece I M 0), ?_⟩
  rw [eq_top_iff]
  intro z _
  obtain ⟨t, rfl⟩ := grModPhi_surjective I M z
  have hι : ∀ w : GrModPiece I M 0, ofGrModPiece I M 0 w ∈
      Submodule.span (AssocGraded I)
        (↑(s.image (ofGrModPiece I M 0)) : Set (AssocGradedModule I M)) := by
    intro w
    have hw : w ∈ Submodule.span (A ⧸ I) (s : Set (GrModPiece I M 0)) := hs ▸ Submodule.mem_top
    induction hw using Submodule.span_induction with
    | mem x hx => exact Submodule.subset_span (Finset.mem_image_of_mem _ hx)
    | zero => rw [map_zero]; exact zero_mem _
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | smul c x _ hx =>
      rw [map_smul, quotient_smul_def]
      exact Submodule.smul_mem _ _ hx
  induction t using TensorProduct.inductionOn with
  | tmul w α =>
    rw [grModPhi_tmul]
    exact Submodule.smul_mem _ _ (hι w)
  | add x y hx hy => rw [map_add]; exact add_mem (hx trivial) (hy trivial)

end AssocGradedModule

end GrModule

end Hironaka
