/-
Copyright (c) 2026 Daattavya Aggarwal, Minhyong Kim, Oisin Kim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daattavya Aggarwal, Minhyong Kim, Oisin Kim
-/
module

public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.Algebra.GradedMonoid
public import Mathlib.Algebra.DirectSum.Decomposition
public import Mathlib.Logic.Equiv.Fin.Basic
public import Architect
public import Hironaka.Compat.ProjectiveIdealForms

/-!
# The graded ring `H' = ⊕ₙ (Iⁿ)_{n(e+1)}` of a blow-up of `Proj H` (step L1b of the p. 132 lemma)

Step L1b of the proof of `MonoidalTransformation.isProjectiveOver` (`Hironaka/Compat/BlowupProjective.lean`, the
unproved, uncited step "a monoidal transformation of a projective scheme is projective" of the Corollary on p. 132;
the paper cites only `Proj(S(I))` over `V`, p. 166).  Let `H = B[T₀, …, T_{n-1}] ⧸ 𝔭` with its natural grading,
`uᵢ` the images of the variables, and `g₁, …, g_N ∈ H_e` forms of one degree (step L1a,
`quotientGrading.exists_forms_generating`).  Put `y_{(a,i)} = g_a uᵢ ∈ H_{e+1}`.

* `BlowupRing.eval` : the `B`-algebra map `B[V_k : k < N n] → H`, `V_{(a,i)} ↦ g_a uᵢ`;
* `BlowupRing.kerIdeal` : its kernel, a *homogeneous* ideal (`eval` sends forms of degree `d` to `H_{d(e+1)}`, and
  these are independent);
* `BlowupRing.incl` : the injection `H' := B[V] ⧸ 𝔟 ↪ H` of the graded ring `H'` (graded as a quotient of a polynomial
  ring, `quotientGrading`, so `Proj H'` is a projective `B`-scheme in the sense of p. 132) onto the subring
  `⊕ₙ (Iⁿ)_{n(e+1)}` of `H`, sending degree `d` into degree `d(e+1)`;
* `H'` is a domain if `H` is.

Nothing here is printed: it is part of the proof of a gap filled.
-/

@[expose] public section

open MvPolynomial DirectSum

namespace Hironaka

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

namespace BlowupRing

variable {B : Type u} [Field B] {n N : ℕ} (𝔭 : HomogeneousIdeal (homogeneousSubmodule (Fin n) B))
  (g : Fin N → MvPolynomial (Fin n) B ⧸ 𝔭.toIdeal)

/-- The generators `y_{(a,i)} = g_a uᵢ` of the ring `H'`, indexed by `Fin (N * n)` through `finProdFinEquiv`. -/
noncomputable def gen (k : Fin (N * n)) : MvPolynomial (Fin n) B ⧸ 𝔭.toIdeal :=
  g (finProdFinEquiv.symm k).1 * quotientGrading.var 𝔭 (finProdFinEquiv.symm k).2

/-- The `B`-algebra map `B[V_k : k < N n] → H`, `V_k ↦ y_k = g_a uᵢ`. -/
noncomputable def eval : MvPolynomial (Fin (N * n)) B →ₐ[B] MvPolynomial (Fin n) B ⧸ 𝔭.toIdeal :=
  aeval (gen 𝔭 g)

/-- `eval` sends the variable `V_k` to the generator `y_k`. -/
theorem eval_X (k : Fin (N * n)) : eval 𝔭 g (X k) = gen 𝔭 g k := aeval_X _ _

variable {e : ℕ} (hg : ∀ a, g a ∈ quotientGrading 𝔭 e)
include hg

/-- Each generator `y_k = g_a uᵢ` has degree `e + 1`. -/
theorem gen_mem (k : Fin (N * n)) : gen 𝔭 g k ∈ quotientGrading 𝔭 (e + 1) := by
  rw [gen]
  exact SetLike.mul_mem_graded (hg _) (quotientGrading.var_mem 𝔭 _)

/-- `eval` sends a form of degree `d` to an element of `H_{d(e+1)}`. -/
theorem eval_mem {d : ℕ} {p : MvPolynomial (Fin (N * n)) B} (hp : p.IsHomogeneous d) :
    eval 𝔭 g p ∈ quotientGrading 𝔭 (d * (e + 1)) := by
  classical
  rw [p.as_sum, map_sum]
  refine Submodule.sum_mem _ fun m hm => ?_
  rw [eval, aeval_monomial, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul]
  refine Submodule.smul_mem _ _ ?_
  have hmd : ∑ k ∈ m.support, m k = d := by
    have := hp (mem_support_iff.mp hm)
    simpa [Finsupp.weight_apply, Finsupp.sum] using this
  have h1 := SetLike.prod_pow_mem_graded (quotientGrading 𝔭) (fun _ : Fin (N * n) => e + 1)
    (gen 𝔭 g) (F := m.support) (fun k => m k) (fun k _ => gen_mem 𝔭 g hg k)
  rw [Finsupp.prod]
  convert h1 using 2
  simp only [smul_eq_mul]
  rw [← Finset.sum_mul, hmd]

/-- The kernel of `eval` is a homogeneous ideal of `B[V]`: `eval` is compatible with the gradings
(`d ↦ d (e + 1)`), and the graded pieces of `H` are independent. -/
theorem isHomogeneous_ker :
    (RingHom.ker (eval 𝔭 g)).IsHomogeneous (homogeneousSubmodule (Fin (N * n)) B) := by
  classical
  intro i r hr
  rw [RingHom.mem_ker] at hr ⊢
  set Q := quotientGrading 𝔭
  set M := homogeneousSubmodule (Fin (N * n)) B
  have hdec : eval 𝔭 g r =
      ∑ j ∈ (DirectSum.decompose M r).support, eval 𝔭 g (DirectSum.decompose M r j : _) := by
    conv_lhs => rw [← DirectSum.sum_support_decompose M r]
    rw [map_sum]
  have hmem : ∀ j, eval 𝔭 g (DirectSum.decompose M r j : _) ∈ Q (j * (e + 1)) := fun j =>
    eval_mem 𝔭 g hg (DirectSum.decompose M r j).2
  have h0 : ((DirectSum.decompose Q (eval 𝔭 g r) (i * (e + 1)) : Q (i * (e + 1))) :
      MvPolynomial (Fin n) B ⧸ 𝔭.toIdeal) = 0 := by
    rw [hr]; simp
  by_cases hi : i ∈ (DirectSum.decompose M r).support
  · rw [hdec, DirectSum.decompose_sum, DFinsupp.finsetSum_apply, AddSubmonoidClass.coe_finsetSum]
      at h0
    rw [Finset.sum_eq_single_of_mem i hi] at h0
    · rwa [DirectSum.decompose_of_mem_same Q (hmem i)] at h0
    · intro j _ hji
      exact DirectSum.decompose_of_mem_ne Q (hmem j) (i := j * (e + 1)) (j := i * (e + 1))
        (fun hh => hji (Nat.eq_of_mul_eq_mul_right (Nat.succ_pos e) hh))
  · have : ((DirectSum.decompose M r i : M i) : MvPolynomial (Fin (N * n)) B) = 0 := by
      rw [DFinsupp.notMem_support_iff.mp hi]; rfl
    rw [this, map_zero]

/-- The homogeneous ideal `𝔟 = ker (eval)` of `B[V_k : k < N n]`; the graded ring `H' = B[V] ⧸ 𝔟` is the ring
`⊕ₙ (Iⁿ)_{n(e+1)}` of the blow-up of `Proj H` with center `I = (g₁, …, g_N)`. -/
noncomputable def kerIdeal : HomogeneousIdeal (homogeneousSubmodule (Fin (N * n)) B) :=
  ⟨RingHom.ker (eval 𝔭 g), isHomogeneous_ker 𝔭 g hg⟩

/-- Membership in `𝔟 = ker (eval)`. -/
theorem mem_kerIdeal_iff {p : MvPolynomial (Fin (N * n)) B} :
    p ∈ (kerIdeal 𝔭 g hg).toIdeal ↔ eval 𝔭 g p = 0 := RingHom.mem_ker

/-- The inclusion `H' = B[V] ⧸ 𝔟 ↪ H` of the graded ring `H'` into `H`. -/
noncomputable def incl : (MvPolynomial (Fin (N * n)) B ⧸ (kerIdeal 𝔭 g hg).toIdeal) →ₐ[B]
    MvPolynomial (Fin n) B ⧸ 𝔭.toIdeal :=
  Ideal.Quotient.liftₐ (kerIdeal 𝔭 g hg).toIdeal (eval 𝔭 g) fun _ ha => (mem_kerIdeal_iff 𝔭 g hg).mp ha

/-- `incl` on a class `mk p` is `eval p`. -/
theorem incl_mk (p : MvPolynomial (Fin (N * n)) B) :
    incl 𝔭 g hg (Ideal.Quotient.mk _ p) = eval 𝔭 g p := rfl

/-- `H' → H` is injective. -/
theorem incl_injective : Function.Injective (incl 𝔭 g hg) := by
  rintro x y hxy
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective y
  rw [incl_mk, incl_mk] at hxy
  rw [Ideal.Quotient.eq, mem_kerIdeal_iff, map_sub, hxy, sub_self]

/-- `H' → H` sends the degree `d` part of `H'` into the degree `d (e + 1)` part of `H`. -/
theorem incl_mem_grading {d : ℕ} {x : MvPolynomial (Fin (N * n)) B ⧸ (kerIdeal 𝔭 g hg).toIdeal}
    (hx : x ∈ quotientGrading (kerIdeal 𝔭 g hg) d) :
    incl 𝔭 g hg x ∈ quotientGrading 𝔭 (d * (e + 1)) := by
  obtain ⟨a, ha, rfl⟩ := hx
  exact eval_mem 𝔭 g hg ha

/-- `H'` is a domain if `H` is. -/
theorem isDomain_quotient [IsDomain (MvPolynomial (Fin n) B ⧸ 𝔭.toIdeal)] :
    IsDomain (MvPolynomial (Fin (N * n)) B ⧸ (kerIdeal 𝔭 g hg).toIdeal) :=
  Function.Injective.isDomain (incl 𝔭 g hg).toRingHom (incl_injective 𝔭 g hg)

end BlowupRing

end Hironaka
