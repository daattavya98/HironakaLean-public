/-
Copyright (c) 2026 Daattavya Aggarwal, Minhyong Kim, Oisin Kim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daattavya Aggarwal, Minhyong Kim, Oisin Kim
-/
module

public import Mathlib.Algebra.MvPolynomial.Supported
public import Mathlib.Data.Nat.Nth
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Hironaka.Ch3.Basic
public import Hironaka.Ch3.NuStar
public import Hironaka.Ch3.TauStar
public import Hironaka.Ch3.Transforms
public import Hironaka.Ch3.Frames
public import Hironaka.Compat.FrameGraded
public import Hironaka.Compat.NormalizedStandardBase
public import Hironaka.Ch3.PermissibleEffects
public import Hironaka.Compat.TauZSystem
public import Hironaka.Compat.TauZBaseChange
public import Hironaka.Compat.TauZPolyCore

/-!
# Compatibility layer: the graded core of Lemma 21 (Ch. III §8, pp. 256--258)

The proof of Lemma 21 (p. 256--258) compares the initial forms of `f_{i+j}` in `gr_M(R)` and of
`g_{i+j} = x^{-ν} f_{i+j}` in `gr_{M₁}(R₁)` through the identifications `gr_M(R) = k[Z, X, Y]`,
`gr_{M₁}(R₁) = k[W, U, X, Y]` and concludes by a rank count for the spaces `T*` of Definition 10*
and Definition 6.  This file contains the parts of that argument which do not mention frame
transforms (the coordinates of the proof and the final assembly are in
`Hironaka/Ch3/FrameTransforms.lean`):

* the polynomial pictures of `gr_M(A)`: `gradedModel` (for a regular system of parameters) and the
  `ρ`-semilinear `SemiModel`/`gradedSemiModel` (the residue fields `k = R/M`, `k₁ = R₁/M₁` are
  identified through the residual rationality of `R₁`), with the transport of the property of
  Definitions 6 and 10* (`SemiModel.isTauZSubmodule_iff`);
* the comparison of initial forms along a chart `forms_correspond` (p. 256: "the initial forms of
  `f_{i+j}` are contained in `k[Z₁, …, Z_r, X₁, …, X_t]`", p. 257: "`ψ = φ(W, U) + χ`,
  `χ ∈ (X, Y) gr`"), and the lowest-degree claim it uses;
* replacement in a standard base (`isStandardBase_replace`) and the group `f_{i+1}, …, f_{i+p}` of
  Lemma 17 (`RegularFrame.exists_normalized_group`, p. 256);
* copies of the lemmas of `Ch3/JStability.lean` (`mem_adjoin_of_isTauSubmoduleMv_aux`, ...) and
  `Compat/TauZStandardBase.lean` (`proj_mem_span_prefix`, ...) which are needed here, upstream of
  `Ch3/FrameTransforms.lean` (those two files are downstream of it): a principal ideal and
  initial segments of a standard base (`homogeneousComponent_mul_form`,
  `mem_adjoin_of_isTauSubmoduleMv_span_singleton`, `proj_mem_span_initialSegment`,
  `isTauSubmodule_iff_isTauZSubmodule_initialSegment`, `exists_initialSegment_length`);
* the monotonicity of `T` of Definition 10* along initial segments of a standard base
  (`isTauZSubmodule_prefix_of_isTauSubmodule`; p. 257: "`T*` contains `W₁, …, W_r` by (8) and (b)");
* Lemma 19 for `T*_a = T_a ⊔ ⟨Z⟩` (`RegularFrame.initialForm_mem_adjoin_tauSubmodule_sup`);
* `μ^{(a)}` and `t` for an ideal whose characters agree with those of `J` up to `ν^{(i+1)}`
  (`mu_eq_of_nuI_eq_prefix`);
* the final rank count of p. 257--258 in the polynomial picture (the choice of the coordinates adapted
  to `T_a`, the forms `L_k`, `ψ = φ(W, U + L)`) is in `Compat/TauZAdapted.lean`, from the
  polynomial core of `Compat/TauZPolyCore.lean`.
-/

@[expose] public section

open IsLocalRing

namespace Hironaka

universe u

section FrameDim

variable {R : Type u} [CommRing R] [IsRegularLocalRing R] (F : RegularFrame R)

/-- `dim R = r + dim S` for a regular frame `(S; z₁, …, z_r)` of `R` (Definition 9(1): `R/(z)R ≅ S`
and `(z)` is part of a regular system of parameters). -/
theorem RegularFrame.ringKrullDim_eq_add :
    ringKrullDim R = (F.r : WithBot ℕ∞) + ringKrullDim F.S := by
  classical
  obtain ⟨s, w, hwN, hNle, hspan, hdim⟩ := exists_rsop_append F
  have hS : (Submodule.spanFinrank (maximalIdeal F.S) : WithBot ℕ∞) = ringKrullDim F.S :=
    IsRegularLocalRing.spanFinrank_maximalIdeal
  have hNspan : Ideal.span (Set.range w) = maximalIdeal F.S :=
    le_antisymm (Ideal.span_le.mpr (by rintro _ ⟨j, rfl⟩; exact hwN j)) hNle
  have hsr : Submodule.spanFinrank (maximalIdeal F.S) ≤ s := by
    have := Submodule.spanFinrank_span_le_ncard_of_finite (R := F.S) (Set.finite_range w)
    rw [show Submodule.span F.S (Set.range w) = maximalIdeal F.S from hNspan] at this
    refine this.trans ?_
    calc (Set.range w).ncard ≤ (Set.univ : Set (Fin s)).ncard := by
          rw [← Set.image_univ]; exact Set.ncard_image_le Set.finite_univ
      _ = s := by simp [Set.ncard_univ]
  apply le_antisymm
  · -- `dim R ≤ dim R/(z) + r`
    have hI : F.idealZ ≤ Ring.jacobson R := by
      rw [ringJacobson_eq_maximalIdeal R]
      rw [F.maximalIdeal_eq_idealZ_sup_map]
      exact le_sup_left
    have h1 := ringKrullDim_le_ringKrullDim_quotient_add_spanFinrank F.idealZ hI
    have hIs : F.idealZ.spanFinrank ≤ F.r := by
      have := Submodule.spanFinrank_span_le_ncard_of_finite (R := R)
        (Set.finite_range F.z)
      refine this.trans ?_
      calc (Set.range F.z).ncard ≤ (Set.univ : Set (Fin F.r)).ncard := by
            rw [← Set.image_univ]; exact Set.ncard_image_le Set.finite_univ
        _ = F.r := by simp [Set.ncard_univ]
    have hq : ringKrullDim (R ⧸ F.idealZ) = ringKrullDim F.S :=
      ringKrullDim_eq_of_ringEquiv (RingEquiv.ofBijective _ F.quot_bijective).symm
    calc ringKrullDim R ≤ ringKrullDim (R ⧸ F.idealZ) + (F.idealZ.spanFinrank : WithBot ℕ∞) := h1
      _ ≤ ringKrullDim F.S + (F.r : WithBot ℕ∞) := by
        rw [hq]; gcongr
      _ = (F.r : WithBot ℕ∞) + ringKrullDim F.S := add_comm _ _
  · rw [← hdim, ← hS, Nat.cast_add]
    gcongr

end FrameDim

section ResidueHelpers

/-- The ideal generated by the range of `Fin.append f g` is the sum of the two spans. -/
theorem span_range_append {A : Type*} [CommRing A] {m n : ℕ} (f : Fin m → A) (g : Fin n → A) :
    Ideal.span (Set.range (Fin.append f g)) =
      Ideal.span (Set.range f) ⊔ Ideal.span (Set.range g) := by
  rw [← Ideal.span_union]
  congr 1
  ext y
  constructor
  · rintro ⟨i, rfl⟩
    refine Fin.addCases (fun i => ?_) (fun i => ?_) i
    · left; exact ⟨i, by simp⟩
    · right; exact ⟨i, by simp⟩
  · rintro (⟨i, rfl⟩ | ⟨i, rfl⟩)
    · exact ⟨Fin.castAdd n i, by simp⟩
    · exact ⟨Fin.natAdd m i, by simp⟩

theorem span_range_cons {A : Type*} [CommRing A] {n : ℕ} (a : A) (g : Fin n → A) :
    Ideal.span (Set.range (Fin.cons a g : Fin (n + 1) → A)) =
      Ideal.span {a} ⊔ Ideal.span (Set.range g) := by
  rw [← Ideal.span_union]
  congr 1
  ext y
  constructor
  · rintro ⟨i, rfl⟩
    refine Fin.cases ?_ (fun i => ?_) i
    · left; simp
    · right; exact ⟨i, by simp⟩
  · rintro (rfl | ⟨i, rfl⟩)
    · exact ⟨0, by simp⟩
    · exact ⟨i.succ, by simp⟩

theorem RingHom.isResiduallyAlgebraic_of_isResiduallyRational {A B : Type u} [CommRing A]
    [CommRing B] [IsLocalRing A] [IsLocalRing B] (φ : A →+* B) [IsLocalHom φ]
    (h : RingHom.IsResiduallyRational φ) : RingHom.IsResiduallyAlgebraic φ := by
  let _ : Algebra (ResidueField A) (ResidueField B) := (ResidueField.map φ).toAlgebra
  refine ⟨fun b => ?_⟩
  obtain ⟨a, rfl⟩ := h b
  exact isAlgebraic_algebraMap a

end ResidueHelpers

section PowerHomogeneous

open MvPolynomial

variable {A : Type u} [CommRing A] {ι : Type*}

/-- Elements of `J^m`, `J` generated by `p_i` (`i ∈ S`), are values at `p` of homogeneous
polynomials of degree `m` in the variables `X_i`, `i ∈ S`. -/
theorem exists_isHomogeneous_aeval_eq_of_mem_pow (p : ι → A) (S : Set ι) (m : ℕ) {f : A}
    (hf : f ∈ (Ideal.span (p '' S)) ^ m) :
    ∃ H : MvPolynomial ι A, H.IsHomogeneous m ∧ H ∈ supported A S ∧ aeval p H = f := by
  induction m generalizing f with
  | zero =>
    exact ⟨C f, isHomogeneous_C _ _, Subalgebra.algebraMap_mem _ f, by simp⟩
  | succ m ih =>
    rw [pow_succ] at hf
    refine Submodule.mul_induction_on hf ?_ ?_
    · intro a ha b hb
      obtain ⟨H, hH, hHS, rfl⟩ := ih ha
      -- `b ∈ span (p '' S)`
      induction hb using Submodule.span_induction with
      | mem y hy =>
        obtain ⟨i, hi, rfl⟩ := hy
        refine ⟨H * X i, ?_, mul_mem hHS ?_, by simp⟩
        · simpa using hH.mul (isHomogeneous_X A i)
        · rw [supported_eq_adjoin_X]; exact Algebra.subset_adjoin ⟨i, hi, rfl⟩
      | zero => exact ⟨0, isHomogeneous_zero _ _ _, zero_mem _, by simp⟩
      | add y z _ _ hy hz =>
        obtain ⟨H₁, h₁, hS₁, e₁⟩ := hy
        obtain ⟨H₂, h₂, hS₂, e₂⟩ := hz
        exact ⟨H₁ + H₂, h₁.add h₂, add_mem hS₁ hS₂, by rw [map_add, mul_add, e₁, e₂]⟩
      | smul c y _ hy =>
        obtain ⟨H₁, h₁, hS₁, e₁⟩ := hy
        refine ⟨C c * H₁, ?_, mul_mem (Subalgebra.algebraMap_mem _ c) hS₁, ?_⟩
        · simpa using (isHomogeneous_C _ c).mul h₁
        · rw [map_mul, aeval_C, smul_eq_mul, e₁]
          simp only [Algebra.algebraMap_self, RingHom.id_apply]
          ring
    · rintro x y ⟨H₁, h₁, hS₁, e₁⟩ ⟨H₂, h₂, hS₂, e₂⟩
      exact ⟨H₁ + H₂, h₁.add h₂, add_mem hS₁ hS₂, by rw [map_add, e₁, e₂]⟩

end PowerHomogeneous

section SemiModelDef

open MvPolynomial

/-- A `ρ`-semilinear ring isomorphism from `k[X₁, …, X_n]` onto a `k₁`-algebra `G`
(`ρ : k ≃ k₁`): the polynomial pictures `gr_M(R) ≅ k[X]`, `gr_{M₁}(R₁) ≅ k₁[X] ≅_ρ k[X]`. -/
structure SemiModel (k k₁ G : Type u) [Field k] [Field k₁] [CommRing G] [Algebra k₁ G] (n : ℕ) where
  ρ : k ≃+* k₁
  Φ : MvPolynomial (Fin n) k ≃+* G
  map_C : ∀ c : k, Φ (C c) = algebraMap k₁ G (ρ c)

namespace SemiModel

section Basic

variable {k k₁ G : Type u} [Field k] [Field k₁] [CommRing G] [Algebra k₁ G] {n : ℕ}
  (M : SemiModel k k₁ G n)

theorem map_smul' (c : k) (p : MvPolynomial (Fin n) k) : M.Φ (c • p) = M.ρ c • M.Φ p := by
  rw [Algebra.smul_def, map_mul, show algebraMap k (MvPolynomial (Fin n) k) c = C c from rfl,
    M.map_C, Algebra.smul_def]

/-- The `k`-submodule of `k[X₁, …, X_n]` of the elements whose image lies in `T`. -/
def pull (T : Submodule k₁ G) : Submodule k (MvPolynomial (Fin n) k) where
  carrier := {p | M.Φ p ∈ T}
  add_mem' := fun {a b} ha hb => by
    simp only [Set.mem_ofPred_eq, map_add] at *
    exact add_mem ha hb
  zero_mem' := by simp
  smul_mem' := fun c p hp => by
    simp only [Set.mem_ofPred_eq] at *
    rw [M.map_smul']
    exact T.smul_mem _ hp

theorem mem_pull {T : Submodule k₁ G} {p : MvPolynomial (Fin n) k} :
    p ∈ M.pull T ↔ M.Φ p ∈ T := Iff.rfl

theorem pull_mono {T T' : Submodule k₁ G} (h : T ≤ T') : M.pull T ≤ M.pull T' := fun _ hp => h hp

theorem finrank_pull (T : Submodule k₁ G) :
    Module.finrank k (M.pull T) = Module.finrank k₁ T := by
  unfold Module.finrank
  congr 1
  refine rank_eq_of_equiv_equiv M.ρ
    { toFun := fun p => ⟨M.Φ p, p.2⟩
      invFun := fun t => ⟨M.Φ.symm t, by
        show M.Φ (M.Φ.symm t) ∈ T
        rw [RingEquiv.apply_symm_apply]; exact t.2⟩
      left_inv := fun p => by ext; simp
      right_inv := fun t => by ext; simp
      map_add' := fun a b => by ext; simp } M.ρ.bijective ?_
  intro c p
  ext
  simp [M.map_smul']

theorem mem_adjoin_pull_iff (T : Submodule k₁ G) (p : MvPolynomial (Fin n) k) :
    p ∈ Algebra.adjoin k (M.pull T : Set (MvPolynomial (Fin n) k)) ↔
      M.Φ p ∈ Algebra.adjoin k₁ (T : Set G) := by
  constructor
  · intro hp
    induction hp using Algebra.adjoin_induction with
    | mem x hx => exact Algebra.subset_adjoin hx
    | algebraMap c =>
      have : M.Φ (algebraMap k (MvPolynomial (Fin n) k) c) = algebraMap k₁ G (M.ρ c) :=
        M.map_C c
      rw [this]
      exact Subalgebra.algebraMap_mem _ _
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | mul x y _ _ hx hy => rw [map_mul]; exact mul_mem hx hy
  · intro hp
    have h : M.Φ.symm (M.Φ p) = p := by simp
    rw [← h]
    generalize M.Φ p = y at hp
    induction hp using Algebra.adjoin_induction with
    | mem x hx =>
      refine Algebra.subset_adjoin ?_
      show M.Φ (M.Φ.symm x) ∈ T
      rw [RingEquiv.apply_symm_apply]; exact hx
    | algebraMap c =>
      have : M.Φ.symm (algebraMap k₁ G c) = algebraMap k (MvPolynomial (Fin n) k) (M.ρ.symm c) := by
        apply M.Φ.injective
        rw [RingEquiv.apply_symm_apply]
        show _ = M.Φ (C _)
        rw [M.map_C]; simp
      rw [this]
      exact Subalgebra.algebraMap_mem _ _
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | mul x y _ _ hx hy => rw [map_mul]; exact mul_mem hx hy

theorem pull_sup (T T' : Submodule k₁ G) : M.pull (T ⊔ T') = M.pull T ⊔ M.pull T' := by
  apply le_antisymm
  · intro p hp
    obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp hp
    refine Submodule.mem_sup.mpr ⟨M.Φ.symm a, ?_, M.Φ.symm b, ?_, ?_⟩
    · show M.Φ (M.Φ.symm a) ∈ T; rw [RingEquiv.apply_symm_apply]; exact ha
    · show M.Φ (M.Φ.symm b) ∈ T'; rw [RingEquiv.apply_symm_apply]; exact hb
    · apply M.Φ.injective
      rw [map_add, RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply]; exact hab
  · exact sup_le (M.pull_mono le_sup_left) (M.pull_mono le_sup_right)

end Basic

end SemiModel

end SemiModelDef

section GradedModel

open MvPolynomial

attribute [local instance] Ideal.Quotient.field

variable {A : Type u} [CommRing A] [IsRegularLocalRing A]

theorem mem_pow_one_of_span_eq {n : ℕ} {v : Fin n → A}
    (hspan : Ideal.span (Set.range v) = maximalIdeal A) (i : Fin n) :
    v i ∈ maximalIdeal A ^ 1 := by
  rw [pow_one, ← hspan]; exact Ideal.subset_span ⟨i, rfl⟩

/-- **The polynomial picture** `k[X₁, …, X_n] ≅ gr_M(A)`, `X_i ↦ [v_i]`, for a regular system of
parameters `v` (given as a family of `n = dim A` generators of `M`; p. 225). -/
noncomputable def gradedModel {n : ℕ} (v : Fin n → A)
    (hspan : Ideal.span (Set.range v) = maximalIdeal A)
    (hdim : (n : WithBot ℕ∞) = ringKrullDim A) :
    MvPolynomial (Fin n) (A ⧸ maximalIdeal A) ≃ₐ[A ⧸ maximalIdeal A]
      AssocGraded (maximalIdeal A) :=
  AlgEquiv.ofBijective (aeval fun i => AssocGraded.mk (maximalIdeal A) 1 (v i)
    (mem_pow_one_of_span_eq hspan i)) (assocGraded_maximalIdeal_aeval_bijective hspan hdim
      (mem_pow_one_of_span_eq hspan))

theorem gradedModel_X {n : ℕ} (v : Fin n → A) (hspan : Ideal.span (Set.range v) = maximalIdeal A)
    (hdim : (n : WithBot ℕ∞) = ringKrullDim A) (i : Fin n) :
    gradedModel v hspan hdim (X i) = AssocGraded.mk (maximalIdeal A) 1 (v i)
      (mem_pow_one_of_span_eq hspan i) := by
  simp [gradedModel]

theorem gradedModel_apply {n : ℕ} (v : Fin n → A)
    (hspan : Ideal.span (Set.range v) = maximalIdeal A)
    (hdim : (n : WithBot ℕ∞) = ringKrullDim A) (p : MvPolynomial (Fin n) (A ⧸ maximalIdeal A)) :
    gradedModel v hspan hdim p = aeval (fun i => AssocGraded.mk (maximalIdeal A) 1 (v i)
      (mem_pow_one_of_span_eq hspan i)) p := rfl

theorem gradedModel_mem_homogeneous_iff {n : ℕ} (v : Fin n → A)
    (hspan : Ideal.span (Set.range v) = maximalIdeal A)
    (hdim : (n : WithBot ℕ∞) = ringKrullDim A) (d : ℕ)
    (p : MvPolynomial (Fin n) (A ⧸ maximalIdeal A)) :
    p ∈ homogeneousSubmodule (Fin n) (A ⧸ maximalIdeal A) d ↔
      gradedModel v hspan hdim p ∈ AssocGraded.homogeneous (maximalIdeal A) d :=
  (aeval_mk_graded_aux' v (mem_pow_one_of_span_eq hspan)
    (assocGraded_maximalIdeal_aeval_bijective hspan hdim (mem_pow_one_of_span_eq hspan))).1 d p

/-- **Class of a value**: for a homogeneous polynomial `H` of degree `d` over `A` the class of
`H(v)` in `gr^d_M(A)` is the image of the reduction of `H` mod `M`. -/
theorem gradedModel_map_eq_mk {n : ℕ} (v : Fin n → A)
    (hspan : Ideal.span (Set.range v) = maximalIdeal A)
    (hdim : (n : WithBot ℕ∞) = ringKrullDim A) {d : ℕ} {H : MvPolynomial (Fin n) A}
    (hH : H.IsHomogeneous d) (h : aeval v H ∈ maximalIdeal A ^ d) :
    gradedModel v hspan hdim (H.map (Ideal.Quotient.mk (maximalIdeal A))) =
      AssocGraded.mk (maximalIdeal A) d (aeval v H) h := by
  rw [gradedModel_apply]
  have := aeval_mk_map_of_isHomogeneous (maximalIdeal A) v (mem_pow_one_of_span_eq hspan) hH
  rw [this]
  rfl

end GradedModel

section LowestDegree

open MvPolynomial
open scoped Classical

attribute [local instance] Ideal.Quotient.field

variable {B : Type u} [CommRing B] [IsRegularLocalRing B]

theorem mem_supported_of_support {K : Type*} [CommSemiring K] {n : ℕ} (U : Set (Fin n))
    {p : MvPolynomial (Fin n) K} (h : ∀ d ∈ p.support, ∀ i, d i ≠ 0 → i ∈ U) :
    p ∈ supported K U := by
  rw [mem_supported]
  intro i hi
  obtain ⟨d, hd, hid⟩ := (mem_vars_iff_mem_support i).mp (Finset.mem_coe.mp hi)
  exact h d hd i (Finsupp.mem_support_iff.mp hid)

theorem support_of_mem_supported {K : Type*} [CommSemiring K] {n : ℕ} (U : Set (Fin n))
    {p : MvPolynomial (Fin n) K} (hp : p ∈ supported K U) :
    ∀ d ∈ p.support, ∀ i, d i ≠ 0 → i ∈ U := by
  intro d hd i hi
  rw [mem_supported] at hp
  exact hp (Finset.mem_coe.mpr
    ((mem_vars_iff_mem_support i).mpr ⟨d, hd, Finsupp.mem_support_iff.mpr hi⟩))

/-- The class in `gr^e` of an element of `(v_i)_{i∉U} · M^{e-1}` is, in the polynomial picture, in
the ideal `(X_i)_{i ∉ U}`. -/
theorem gradedModel_symm_mk_mem_outIdeal {n : ℕ} (v : Fin n → B)
    (hspan : Ideal.span (Set.range v) = maximalIdeal B)
    (hdim : (n : WithBot ℕ∞) = ringKrullDim B) (U : Set (Fin n)) [DecidablePred (· ∈ U)]
    (e : ℕ) (a : B)
    (ha : a ∈ maximalIdeal B ^ e) (d : Fin n → B) (hd : ∀ i, d i ∈ maximalIdeal B ^ (e - 1))
    (hav : a = ∑ i, if i ∈ U then 0 else v i * d i) :
    (gradedModel v hspan hdim).symm (AssocGraded.mk (maximalIdeal B) e a ha) ∈
      outIdeal (K := B ⧸ maximalIdeal B) U := by
  have hv : ∀ i, v i ∈ maximalIdeal B ^ 1 := mem_pow_one_of_span_eq hspan
  rcases e with _ | e
  · have h1 : a ∈ maximalIdeal B ^ (0 + 1) := by
      rw [hav]
      refine Ideal.sum_mem _ fun i _ => ?_
      split_ifs
      · exact zero_mem _
      · rw [zero_add, pow_one]
        exact Ideal.mul_mem_right _ _ (by simpa using hv i)
    rw [(AssocGraded.mk_eq_zero_iff _ ha).mpr h1]
    simp
  · have hterm : ∀ i, (if i ∈ U then 0 else v i * d i) ∈ maximalIdeal B ^ (e + 1) := fun i => by
      split_ifs
      · exact zero_mem _
      · have := Ideal.mul_mem_mul (hv i) (hd i)
        rw [← pow_add] at this
        simpa [Nat.add_comm] using this
    have hmk : ∀ i, AssocGraded.mk (maximalIdeal B) (e + 1) (if i ∈ U then 0 else v i * d i)
        (hterm i) = if i ∈ U then 0 else
          gradedModel v hspan hdim (X i * (gradedModel v hspan hdim).symm
            (AssocGraded.mk (maximalIdeal B) e (d i) (by simpa using hd i))) := by
      intro i
      split_ifs with hi
      · exact (AssocGraded.mk_eq_zero_iff _ _).mpr (zero_mem _)
      · rw [map_mul, AlgEquiv.apply_symm_apply, gradedModel_X, AssocGraded.mk_mul_mk]
        exact AssocGraded.mk_congr_exponent _ (by omega) _ _
    have hsum : AssocGraded.mk (maximalIdeal B) (e + 1) a ha =
        ∑ i, AssocGraded.mk (maximalIdeal B) (e + 1) (if i ∈ U then 0 else v i * d i)
          (hterm i) := by
      rw [← AssocGraded.mk_sum _ _ _ _ hterm]
      exact AssocGraded.mk_congr _ _ hav
    simp only [hmk] at hsum
    rw [hsum, map_sum]
    refine Ideal.sum_mem _ fun i _ => ?_
    split_ifs with hi
    · simp
    · rw [AlgEquiv.symm_apply_apply]
      exact Ideal.mul_mem_right _ _ (Ideal.subset_span ⟨i, hi, rfl⟩)

/-- **The lowest degree term** (used on p. 257, "the form `φ''` …"): if a polynomial `𝒬` over `B`
supported on the variables in `U`, all of whose coefficients are units or `0`, has value at the
regular system of parameters `v` in `M^m + (v_i)_{i ∉ U}B`, then it has no term of degree `< m`.
(Lemma K for the ideal `(v_i)_{i∉U}` is the hypothesis `hK`.) -/
theorem homogeneousComponent_eq_zero_of_aeval_mem {n : ℕ} (v : Fin n → B)
    (hspan : Ideal.span (Set.range v) = maximalIdeal B)
    (hdim : (n : WithBot ℕ∞) = ringKrullDim B) (U : Set (Fin n)) [DecidablePred (· ∈ U)]
    (hK : ∀ a ∈ Ideal.span (v '' Uᶜ), ∀ m : ℕ, a ∈ maximalIdeal B ^ m →
      ∃ d : Fin n → B, (∀ i, d i ∈ maximalIdeal B ^ (m - 1)) ∧
        a = ∑ i, (if i ∈ U then 0 else v i * d i))
    (Q : MvPolynomial (Fin n) B) (hQU : ∀ d ∈ Q.support, ∀ i, d i ≠ 0 → i ∈ U)
    (hQc : ∀ d ∈ Q.support, Q.coeff d ∉ maximalIdeal B) {m : ℕ}
    (hm : aeval v Q ∈ maximalIdeal B ^ m ⊔ Ideal.span (v '' Uᶜ)) :
    ∀ d < m, homogeneousComponent d Q = 0 := by
  have hv : ∀ i, v i ∈ maximalIdeal B ^ 1 := mem_pow_one_of_span_eq hspan
  by_contra hcon
  push Not at hcon
  have hex : ∃ d, d < m ∧ homogeneousComponent d Q ≠ 0 := hcon
  set d₀ := Nat.find hex with hd₀def
  obtain ⟨hd₀m, hd₀ne⟩ := Nat.find_spec hex
  have hmin : ∀ d < d₀, homogeneousComponent d Q = 0 := fun d hd => by
    by_contra h
    exact Nat.find_min hex hd ⟨hd.trans hd₀m, h⟩
  -- decomposition of `aeval v Q`
  have hd₀deg : d₀ ∈ Finset.range (Q.totalDegree + 1) := by
    rw [Finset.mem_range, Nat.lt_succ_iff]
    by_contra hlt
    exact hd₀ne (homogeneousComponent_eq_zero _ _ (by omega))
  have hsum := sum_homogeneousComponent Q
  have hcomp : ∀ d, aeval v (homogeneousComponent d Q) ∈ maximalIdeal B ^ d := fun d => by
    have := eval_mem_pow_of_isHomogeneous (maximalIdeal B) v hv
      (homogeneousComponent_isHomogeneous d Q)
    exact this
  set c := aeval v (homogeneousComponent d₀ Q) with hcdef
  set R' := ∑ i ∈ (Finset.range (Q.totalDegree + 1)).erase d₀, aeval v (homogeneousComponent i Q)
    with hR'
  have hQsplit : aeval v Q = c + R' := by
    conv_lhs => rw [← hsum]
    rw [map_sum, ← Finset.add_sum_erase _ _ hd₀deg]
  have hR'mem : R' ∈ maximalIdeal B ^ (d₀ + 1) := by
    refine Ideal.sum_mem _ fun i hi => ?_
    obtain ⟨hid, -⟩ := Finset.mem_erase.mp hi
    rcases lt_or_gt_of_ne hid with hlt | hgt
    · rw [hmin i hlt, map_zero]; exact zero_mem _
    · exact Ideal.pow_le_pow_right hgt (hcomp i)
  obtain ⟨x, hx, a₁, ha₁, hxa⟩ := Submodule.mem_sup.mp hm
  have hy' : x - R' ∈ maximalIdeal B ^ (d₀ + 1) :=
    sub_mem (Ideal.pow_le_pow_right hd₀m hx) hR'mem
  have hca : c = a₁ + (x - R') := by
    have : c + R' = x + a₁ := by rw [← hQsplit, hxa]
    linear_combination this
  have ha₁M : a₁ ∈ maximalIdeal B ^ d₀ := by
    have : a₁ = c - (x - R') := by rw [hca]; ring
    rw [this]
    exact sub_mem (hcomp d₀) (Ideal.pow_le_pow_right (Nat.le_succ d₀) hy')
  obtain ⟨d, hd, had⟩ := hK a₁ ha₁ d₀ ha₁M
  -- the class in `gr^{d₀}`
  have hcls : gradedModel v hspan hdim ((homogeneousComponent d₀ Q).map
      (Ideal.Quotient.mk (maximalIdeal B))) =
        AssocGraded.mk (maximalIdeal B) d₀ a₁ ha₁M := by
    rw [gradedModel_map_eq_mk v hspan hdim (homogeneousComponent_isHomogeneous d₀ Q) (hcomp d₀)]
    have h1 : AssocGraded.mk (maximalIdeal B) d₀ c (hcomp d₀) =
        AssocGraded.mk (maximalIdeal B) d₀ (a₁ + (x - R')) (by rw [← hca]; exact hcomp d₀) :=
      AssocGraded.mk_congr _ _ hca
    rw [h1, AssocGraded.mk_add _ _ _ _ ha₁M (Ideal.pow_le_pow_right (Nat.le_succ d₀) hy')]
    rw [(AssocGraded.mk_eq_zero_iff _ _).mpr hy', add_zero]
  set Qb := (homogeneousComponent d₀ Q).map (Ideal.Quotient.mk (maximalIdeal B)) with hQb
  have hQbBid : Qb ∈ outIdeal (K := B ⧸ maximalIdeal B) U := by
    have h1 : Qb = (gradedModel v hspan hdim).symm
        (AssocGraded.mk (maximalIdeal B) d₀ a₁ ha₁M) := by
      rw [← hcls]; simp
    rw [h1]
    exact gradedModel_symm_mk_mem_outIdeal v hspan hdim U d₀ a₁ ha₁M d hd had
  have hQbU : Qb ∈ supported (B ⧸ maximalIdeal B) U := by
    refine mem_supported_of_support U fun e he i hi => ?_
    have h1 := support_map_subset _ _ he
    have h2 : e ∈ Q.support := by
      rw [mem_support_iff, coeff_homogeneousComponent] at h1
      rw [mem_support_iff]
      split_ifs at h1 with h
      · exact h1
      · exact absurd rfl h1
    exact hQU e h2 i hi
  have hQb0 : Qb = 0 := by
    have h1 := (projOut_eq_zero_iff U Qb).mpr hQbBid
    rwa [projOut_of_mem_supported U hQbU] at h1
  -- the coefficients of the component are units or `0`, so it vanishes
  have hz0 : homogeneousComponent d₀ Q = 0 := by
    refine MvPolynomial.ext _ _ fun e => ?_
    have key : (homogeneousComponent d₀ Q).coeff e =
        if e.degree = d₀ then Q.coeff e else 0 := by
      rw [coeff_homogeneousComponent]
    have hmap : Ideal.Quotient.mk (maximalIdeal B) ((homogeneousComponent d₀ Q).coeff e) = 0 := by
      have := congrArg (fun p => p.coeff e) hQb0
      simpa [hQb, coeff_map] using this
    by_cases h : e.degree = d₀
    · have hk : (homogeneousComponent d₀ Q).coeff e = Q.coeff e := by simp [key, h]
      by_cases hz : Q.coeff e = 0
      · simp [hk, hz]
      · exfalso
        have hmem : e ∈ Q.support := mem_support_iff.mpr hz
        refine hQc e hmem ?_
        rw [hk] at hmap
        exact Ideal.Quotient.eq_zero_iff_mem.mp hmap
    · simp [key, h]
  exact hd₀ne hz0

end LowestDegree

section FormsCorrespond

open MvPolynomial
open scoped Classical

attribute [local instance] Ideal.Quotient.field

variable {A A₁ : Type u} [CommRing A] [IsRegularLocalRing A] [CommRing A₁]
  [IsRegularLocalRing A₁] [IsDomain A₁]

/-- **The comparison of initial forms along a chart** (p. 257: "by (10) and (b), `ψ = φ(W₁, …, W_r,
U₁, …, U_t) + λ`, where `λ ∈ (X, Y₁, …, Y_s) gr_{M₁}(R₁)`", and p. 256: "This shows that the
initial forms of `f_{i+j}` are contained in `k[Z₁, …, Z_r, X₁, …, X_t]`").  `α : A → A₁`, regular
systems of parameters `v = (z, x_1, …, x_t, x, y)` of `A` and `v₁ = (w, u, x, y)` of `A₁`
(first `m` entries: the variables `Z, X_1, …, X_t`; the entry `m`: `x`; the rest: `y`), with
`α(z_j) = x w_j`, `α(x_k) = x u_k`, `α(x) = x`, `α(y_l) = y_l`.  If `f ∈ P^μ`
(`P = (z, x_1, …, x_t, x)`)
and `g = f/x^μ` lies in `M₁^μ`, then the initial form of `f` involves only `Z, X_1, …, X_t` and
the initial form of `g` is its image mod `(x, y)`. -/
theorem forms_correspond (α : A →+* A₁) [IsLocalHom α] {m s : ℕ}
    (v : Fin (m + (s + 1)) → A) (v₁ : Fin (m + (s + 1)) → A₁)
    (hspan : Ideal.span (Set.range v) = maximalIdeal A)
    (hdim : ((m + (s + 1) : ℕ) : WithBot ℕ∞) = ringKrullDim A)
    (hspan₁ : Ideal.span (Set.range v₁) = maximalIdeal A₁)
    (hdim₁ : ((m + (s + 1) : ℕ) : WithBot ℕ∞) = ringKrullDim A₁)
    (xx : A₁) (hxx0 : xx ≠ 0) (hxx : v₁ ⟨m, by omega⟩ = xx)
    (hrelU : ∀ i : Fin (m + (s + 1)), i.val < m → α (v i) = xx * v₁ i)
    (hrelx : α (v ⟨m, by omega⟩) = xx)
    (hrely : ∀ i : Fin (m + (s + 1)), m < i.val → α (v i) = v₁ i)
    (hK : ∀ a ∈ Ideal.span (v₁ '' {i : Fin (m + (s + 1)) | ¬ i.val < m}), ∀ k : ℕ,
      a ∈ maximalIdeal A₁ ^ k →
      ∃ d : Fin (m + (s + 1)) → A₁, (∀ i, d i ∈ maximalIdeal A₁ ^ (k - 1)) ∧
        a = ∑ i, (if i ∈ {i : Fin (m + (s + 1)) | i.val < m} then 0 else v₁ i * d i))
    {μ : ℕ} {f : A} (hfP : f ∈ Ideal.span (v '' {i : Fin (m + (s + 1)) | i.val ≤ m}) ^ μ)
    (hfM : f ∈ maximalIdeal A ^ μ) {g : A₁} (hg : xx ^ μ * g = α f)
    (hgM : g ∈ maximalIdeal A₁ ^ μ) :
    (gradedModel v hspan hdim).symm (AssocGraded.mk (maximalIdeal A) μ f hfM) ∈
        supported (A ⧸ maximalIdeal A) {i : Fin (m + (s + 1)) | i.val < m} ∧
      (gradedModel v₁ hspan₁ hdim₁).symm (AssocGraded.mk (maximalIdeal A₁) μ g hgM) -
        MvPolynomial.map (Ideal.quotientMap (maximalIdeal A₁) α
          (fun a ha => map_nonunit α a ha))
          ((gradedModel v hspan hdim).symm (AssocGraded.mk (maximalIdeal A) μ f hfM)) ∈
        outIdeal (K := A₁ ⧸ maximalIdeal A₁) {i : Fin (m + (s + 1)) | i.val < m} := by
  set ι : Fin (m + (s + 1)) := ⟨m, by omega⟩ with hι
  set U : Set (Fin (m + (s + 1))) := {i | i.val < m} with hU
  have hv : ∀ i, v i ∈ maximalIdeal A ^ 1 := mem_pow_one_of_span_eq hspan
  have hv₁ : ∀ i, v₁ i ∈ maximalIdeal A₁ ^ 1 := mem_pow_one_of_span_eq hspan₁
  -- a homogeneous polynomial with `f = H(v)`
  obtain ⟨H, hHh, hHS, hHv⟩ := exists_isHomogeneous_aeval_eq_of_mem_pow v
    {i | i.val ≤ m} μ hfP
  have hHsupp : ∀ d ∈ H.support, ∀ i, d i ≠ 0 → i.val ≤ m :=
    support_of_mem_supported _ hHS
  have hHdeg : ∀ d ∈ H.support, ∑ i, d i = μ := by
    intro d hd
    have h1 := hHh (mem_support_iff.mp hd)
    have h2 : d.degree = μ := by
      rw [Finsupp.degree_eq_weight_one]; exact h1
    rw [← h2, Finsupp.degree_eq_sum]
  have hfH : aeval v H ∈ maximalIdeal A ^ μ := hHv ▸ hfM
  have hφ : (gradedModel v hspan hdim).symm (AssocGraded.mk (maximalIdeal A) μ f hfM) =
      H.map (Ideal.Quotient.mk (maximalIdeal A)) := by
    rw [AlgEquiv.symm_apply_eq, gradedModel_map_eq_mk v hspan hdim hHh hfH]
    exact AssocGraded.mk_congr _ _ hHv.symm
  -- `g = Σ_d α(c_d) W^d`
  set W : Fin (m + (s + 1)) → A₁ := fun i => if i = ι then 1 else v₁ i with hW
  have hrel : ∀ d ∈ H.support, ∏ i, (α (v i)) ^ d i = xx ^ μ * ∏ i, W i ^ d i := by
    intro d hd
    have h1 : ∀ i, (α (v i)) ^ d i = (xx ^ d i) * W i ^ d i := by
      intro i
      by_cases hdi : d i = 0
      · simp [hdi]
      · have hle := hHsupp d hd i hdi
        have : α (v i) = xx * W i := by
          rcases lt_or_eq_of_le hle with hlt | heq
          · have hne : i ≠ ι := fun h => by simp [hι, h] at hlt
            rw [hrelU i hlt]
            simp [hW, hne]
          · have hieq : i = ι := Fin.ext heq
            rw [hieq, hrelx]
            simp [hW]
        rw [this, mul_pow]
    rw [Finset.prod_congr rfl fun i _ => h1 i, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum,
      hHdeg d hd]
  have hgsum : g = ∑ d ∈ H.support, α (H.coeff d) * ∏ i, W i ^ d i := by
    apply mul_left_cancel₀ (pow_ne_zero μ hxx0)
    rw [hg, ← hHv]
    show α (eval v H) = _
    rw [eval_eq', map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun d hd => ?_
    rw [map_mul, map_prod]
    simp only [map_pow]
    rw [hrel d hd]
    ring
  -- lifting of residues, and `α(M) ⊆ (x, y)`
  let σc : A → A := fun c => if IsUnit c then c else 0
  have hσc : ∀ c, c - σc c ∈ maximalIdeal A := fun c => by
    by_cases hc : IsUnit c
    · simp [σc, hc]
    · simp [σc, hc]
  set 𝔞 : Ideal A₁ := Ideal.span (v₁ '' {i : Fin (m + (s + 1)) | ¬ i.val < m}) with h𝔞
  have hxxa : xx ∈ 𝔞 := by
    rw [← hxx]
    exact Ideal.subset_span ⟨ι, by simp [hι], rfl⟩
  have hαM : ∀ c ∈ maximalIdeal A, α c ∈ 𝔞 := by
    intro c hc
    rw [← hspan] at hc
    induction hc using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨i, rfl⟩ := hy
      rcases lt_trichotomy i.val m with hlt | heq | hgt
      · rw [hrelU i hlt]; exact Ideal.mul_mem_right _ _ hxxa
      · have : i = ι := Fin.ext heq
        rw [this, hrelx]; exact hxxa
      · rw [hrely i hgt]
        exact Ideal.subset_span ⟨i, by simpa using not_lt.mpr hgt.le, rfl⟩
    | zero => simp
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | smul a x _ hx => rw [smul_eq_mul, map_mul]; exact Ideal.mul_mem_left _ _ hx
  -- the polynomial `Q` of the units among the coefficients, dehomogenized at `x`
  set Q : MvPolynomial (Fin (m + (s + 1))) A₁ :=
    ∑ d ∈ H.support, monomial (d.erase ι) (α (σc (H.coeff d))) with hQ
  have hWprod : ∀ d : Fin (m + (s + 1)) →₀ ℕ,
      (d.erase ι).prod (fun i k => v₁ i ^ k) = ∏ i, W i ^ d i := by
    intro d
    rw [Finsupp.prod_fintype _ _ (fun i => pow_zero _)]
    refine Finset.prod_congr rfl fun i _ => ?_
    by_cases hi : i = ι
    · subst hi; simp [hW]
    · simp [hW, hi, Finsupp.erase_ne hi]
  have hQeval : aeval v₁ Q = ∑ d ∈ H.support, α (σc (H.coeff d)) * ∏ i, W i ^ d i := by
    show eval v₁ Q = _
    rw [hQ, map_sum]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [eval_monomial, hWprod]
  have hinj : ∀ d ∈ H.support, ∀ d' ∈ H.support, d.erase ι = d'.erase ι → d = d' := by
    intro d hd d' hd' hdd
    have hsum : ∀ e : Fin (m + (s + 1)) →₀ ℕ, ∑ i, e i = e ι + ∑ i ∈ Finset.univ.erase ι, e i :=
      fun e => (Finset.add_sum_erase _ _ (Finset.mem_univ ι)).symm
    have hrest : ∑ i ∈ Finset.univ.erase ι, d i = ∑ i ∈ Finset.univ.erase ι, d' i := by
      refine Finset.sum_congr rfl fun i hi => ?_
      have hne : i ≠ ι := (Finset.mem_erase.mp hi).1
      have := congrArg (fun e => e i) hdd
      simpa [Finsupp.erase_ne hne] using this
    have h1 := hHdeg d hd
    have h2 := hHdeg d' hd'
    rw [hsum d] at h1
    rw [hsum d'] at h2
    ext i
    by_cases hi : i = ι
    · subst hi; omega
    · have := congrArg (fun e => e i) hdd
      simpa [Finsupp.erase_ne hi] using this
  have hQcoeff : ∀ d ∈ H.support, Q.coeff (d.erase ι) = α (σc (H.coeff d)) := by
    intro d hd
    rw [hQ, coeff_sum, Finset.sum_eq_single d]
    · simp [coeff_monomial]
    · intro d' hd' hne
      rw [coeff_monomial]
      split_ifs with h
      · exact absurd (hinj d' hd' d hd h) hne
      · rfl
    · intro h; exact absurd hd h
  have hQsupp : ∀ e ∈ Q.support, ∃ d ∈ H.support, e = d.erase ι := by
    intro e he
    have hne : Q.coeff e ≠ 0 := mem_support_iff.mp he
    rw [hQ, coeff_sum] at hne
    obtain ⟨d, hd, hdne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
    refine ⟨d, hd, ?_⟩
    by_contra hed
    refine hdne ?_
    rw [coeff_monomial]
    split_ifs with h
    · exact absurd h.symm hed
    · rfl
  have hQU : ∀ e ∈ Q.support, ∀ i, e i ≠ 0 → i ∈ U := by
    intro e he i hi
    obtain ⟨d, hd, rfl⟩ := hQsupp e he
    have hiι : i ≠ ι := fun h => by subst h; simp at hi
    have hdi : d i ≠ 0 := by simpa [Finsupp.erase_ne hiι] using hi
    have hle := hHsupp d hd i hdi
    have hne : i.val ≠ m := fun h => hiι (Fin.ext h)
    show i.val < m
    omega
  have hQc : ∀ e ∈ Q.support, Q.coeff e ∉ maximalIdeal A₁ := by
    intro e he
    obtain ⟨d, hd, rfl⟩ := hQsupp e he
    have hne : Q.coeff (d.erase ι) ≠ 0 := mem_support_iff.mp he
    rw [hQcoeff d hd] at hne ⊢
    have hunit : IsUnit (H.coeff d) := by
      by_contra hnu
      exact hne (by simp [σc, hnu])
    have : σc (H.coeff d) = H.coeff d := by simp [σc, hunit]
    rw [this, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, not_not]
    exact hunit.map α
  have hdiff : g - aeval v₁ Q ∈ 𝔞 := by
    rw [hgsum, hQeval, ← Finset.sum_sub_distrib]
    refine Ideal.sum_mem _ fun d _ => ?_
    rw [← sub_mul, ← map_sub]
    exact Ideal.mul_mem_right _ _ (hαM _ (hσc _))
  have hm : aeval v₁ Q ∈ maximalIdeal A₁ ^ μ ⊔ 𝔞 :=
    Submodule.mem_sup.mpr ⟨g, hgM, aeval v₁ Q - g, by
      rw [← neg_sub]; exact neg_mem hdiff, by ring⟩
  have hK' : ∀ a ∈ Ideal.span (v₁ '' Uᶜ), ∀ k : ℕ, a ∈ maximalIdeal A₁ ^ k →
      ∃ d : Fin (m + (s + 1)) → A₁, (∀ i, d i ∈ maximalIdeal A₁ ^ (k - 1)) ∧
        a = ∑ i, (if i ∈ U then 0 else v₁ i * d i) := by
    exact hK
  have hLD := homogeneousComponent_eq_zero_of_aeval_mem v₁ hspan₁ hdim₁ U hK' Q hQU hQc hm
  -- no `X` in the initial form of `f`
  have hnoX : ∀ d ∈ H.support, d ι ≠ 0 → H.coeff d ∈ maximalIdeal A := by
    intro d hd hdι
    by_contra hcm
    have hunit : IsUnit (H.coeff d) := by
      by_contra hnu
      exact hcm ((IsLocalRing.mem_maximalIdeal _).mpr hnu)
    have hco : Q.coeff (d.erase ι) = α (H.coeff d) := by
      rw [hQcoeff d hd]; simp [σc, hunit]
    have hα0 : α (H.coeff d) ≠ 0 := (hunit.map α).ne_zero
    have hdeg : (d.erase ι).degree < μ := by
      have hsum : ∀ e : Fin (m + (s + 1)) →₀ ℕ,
          ∑ i, e i = e ι + ∑ i ∈ Finset.univ.erase ι, e i :=
        fun e => (Finset.add_sum_erase _ _ (Finset.mem_univ ι)).symm
      rw [Finsupp.degree_eq_sum]
      have h1 := hHdeg d hd
      rw [hsum d] at h1
      have h2 : ∑ i, (d.erase ι) i = ∑ i ∈ Finset.univ.erase ι, d i := by
        rw [hsum (d.erase ι), Finsupp.erase_same, zero_add]
        refine Finset.sum_congr rfl fun i hi => ?_
        exact Finsupp.erase_ne (Finset.mem_erase.mp hi).1
      rw [h2]
      have : 0 < d ι := Nat.pos_of_ne_zero hdι
      omega
    have h3 : (homogeneousComponent (d.erase ι).degree Q).coeff (d.erase ι) =
        Q.coeff (d.erase ι) := by
      rw [coeff_homogeneousComponent]; simp
    rw [hLD _ hdeg, hco] at h3
    exact hα0 (by simpa using h3.symm)
  -- (a) the initial form of `f` involves only `Z, X_1, …, X_t`
  have hφsupp : H.map (Ideal.Quotient.mk (maximalIdeal A)) ∈
      supported (A ⧸ maximalIdeal A) U := by
    refine mem_supported_of_support U fun e he i hi => ?_
    have heH : e ∈ H.support := support_map_subset _ _ he
    have hne : (Ideal.Quotient.mk (maximalIdeal A)) (H.coeff e) ≠ 0 := by
      rwa [mem_support_iff, coeff_map] at he
    have heι : e ι = 0 := by
      by_contra h
      exact hne (Ideal.Quotient.eq_zero_iff_mem.mpr (hnoX e heH h))
    have hiι : i ≠ ι := fun h => by subst h; exact hi heι
    have hle := hHsupp e heH i hi
    have hne' : i.val ≠ m := fun h => hiι (Fin.ext h)
    show i.val < m
    omega
  refine ⟨hφ ▸ hφsupp, ?_⟩
  rw [hφ]
  -- (b) splitting `g = g₀ + gP`
  set H₀ : MvPolynomial (Fin (m + (s + 1))) A :=
    ∑ d ∈ H.support.filter (fun d => d ι = 0), monomial d (H.coeff d) with hH₀
  have hH₀h : H₀.IsHomogeneous μ := by
    refine IsHomogeneous.sum _ _ _ fun d hd => ?_
    have := hHdeg d (Finset.mem_filter.mp hd).1
    refine isHomogeneous_monomial _ ?_
    rw [Finsupp.degree_eq_sum]
    exact this
  set g₀ : A₁ := ∑ d ∈ H.support.filter (fun d => d ι = 0),
    α (H.coeff d) * ∏ i, v₁ i ^ d i with hg₀
  have hg₀eval : aeval v₁ (H₀.map α) = g₀ := by
    show eval v₁ (H₀.map α) = _
    rw [hH₀, map_sum, map_sum]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [map_monomial, eval_monomial, Finsupp.prod_fintype _ _ (fun i => pow_zero _)]
  have hg₀M : g₀ ∈ maximalIdeal A₁ ^ μ := by
    rw [← hg₀eval]
    exact eval_mem_pow_of_isHomogeneous (maximalIdeal A₁) v₁ hv₁ (hH₀h.map α)
  have hgsplit : g = g₀ + ∑ d ∈ H.support.filter (fun d => ¬ d ι = 0),
      α (H.coeff d) * ∏ i, W i ^ d i := by
    rw [hgsum, ← Finset.sum_filter_add_sum_filter_not H.support (fun d => d ι = 0)]
    congr 1
    refine Finset.sum_congr rfl fun d hd => ?_
    have hdι := (Finset.mem_filter.mp hd).2
    congr 1
    refine Finset.prod_congr rfl fun i _ => ?_
    by_cases hi : i = ι
    · subst hi; simp [hdι]
    · simp [hW, hi]
  set gP : A₁ := ∑ d ∈ H.support.filter (fun d => ¬ d ι = 0),
    α (H.coeff d) * ∏ i, W i ^ d i with hgP
  have hgPa : gP ∈ 𝔞 := by
    refine Ideal.sum_mem _ fun d hd => ?_
    obtain ⟨hdH, hdι⟩ := Finset.mem_filter.mp hd
    exact Ideal.mul_mem_right _ _ (hαM _ (hnoX d hdH hdι))
  have hgPM : gP ∈ maximalIdeal A₁ ^ μ := by
    have : gP = g - g₀ := by rw [hgsplit]; ring
    rw [this]; exact sub_mem hgM hg₀M
  -- classes
  have hclass : (gradedModel v₁ hspan₁ hdim₁).symm (AssocGraded.mk (maximalIdeal A₁) μ g hgM) =
      (gradedModel v₁ hspan₁ hdim₁).symm (AssocGraded.mk (maximalIdeal A₁) μ g₀ hg₀M) +
      (gradedModel v₁ hspan₁ hdim₁).symm (AssocGraded.mk (maximalIdeal A₁) μ gP hgPM) := by
    rw [← map_add, ← AssocGraded.mk_add _ _ _ _ hg₀M hgPM]
    congr 1
    exact AssocGraded.mk_congr _ _ (by rw [hgsplit])
  have hPP : (gradedModel v₁ hspan₁ hdim₁).symm (AssocGraded.mk (maximalIdeal A₁) μ gP hgPM) ∈
      outIdeal (K := A₁ ⧸ maximalIdeal A₁) U := by
    obtain ⟨d, hd, had⟩ := hK' gP hgPa μ hgPM
    exact gradedModel_symm_mk_mem_outIdeal v₁ hspan₁ hdim₁ U μ gP hgPM d hd had
  have h₀ : (gradedModel v₁ hspan₁ hdim₁).symm (AssocGraded.mk (maximalIdeal A₁) μ g₀ hg₀M) =
      MvPolynomial.map (Ideal.quotientMap (maximalIdeal A₁) α
        (fun a ha => map_nonunit α a ha)) (H.map (Ideal.Quotient.mk (maximalIdeal A))) := by
    rw [AlgEquiv.symm_apply_eq]
    have h1 := gradedModel_map_eq_mk v₁ hspan₁ hdim₁ (hH₀h.map α) (hg₀eval ▸ hg₀M)
    have h2 : (H₀.map α).map (Ideal.Quotient.mk (maximalIdeal A₁)) =
        MvPolynomial.map (Ideal.quotientMap (maximalIdeal A₁) α
          (fun a ha => map_nonunit α a ha)) (H.map (Ideal.Quotient.mk (maximalIdeal A))) := by
      ext d
      rw [coeff_map, coeff_map, coeff_map, coeff_map]
      have hρ : ∀ c : A, Ideal.quotientMap (maximalIdeal A₁) α
          (fun a ha => map_nonunit α a ha) (Ideal.Quotient.mk (maximalIdeal A) c) =
            Ideal.Quotient.mk (maximalIdeal A₁) (α c) := fun c => Ideal.quotientMap_mk
      rw [hρ]
      by_cases hd : d ∈ H.support ∧ d ι = 0
      · have : H₀.coeff d = H.coeff d := by
          rw [hH₀, coeff_sum, Finset.sum_eq_single d]
          · simp [coeff_monomial]
          · intro d' _ hne
            rw [coeff_monomial]
            split_ifs with h
            · exact absurd h hne
            · rfl
          · intro h
            exact absurd (Finset.mem_filter.mpr hd) h
        rw [this]
      · have h0 : H₀.coeff d = 0 := by
          rw [hH₀, coeff_sum]
          refine Finset.sum_eq_zero fun d' hd' => ?_
          rw [coeff_monomial]
          split_ifs with h
          · exact absurd (h ▸ Finset.mem_filter.mp hd') hd
          · rfl
        rw [h0, map_zero, map_zero]
        symm
        by_cases hdH : d ∈ H.support
        · have hdι : d ι ≠ 0 := fun h => hd ⟨hdH, h⟩
          refine Ideal.Quotient.eq_zero_iff_mem.mpr ?_
          rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
          intro hu
          exact ((IsLocalRing.mem_maximalIdeal _).mp (hnoX d hdH hdι))
            (isUnit_of_map_unit α _ hu)
        · rw [notMem_support_iff.mp hdH]; simp
    rw [← h2, h1]
    exact AssocGraded.mk_congr _ _ hg₀eval.symm
  rw [hclass, h₀]
  simpa using hPP

end FormsCorrespond

section StandardBaseReplace

variable {R : Type u} [CommRing R] [IsRegularLocalRing R]

/-- **One replacement step in a standard base** (p. 256: "we can choose elements `f_{i+j}` … such
that each is normalized by `(f₁, …, f_i)`"; footnote 11, p. 259): if `G` is a standard base of
`J`, `k ≥ i` and `h_l` (`l < i`) satisfy `ν_M(h_l) ≥ ν_M(G_k) - ν_M(G_l)`, then `G_k - Σ h_l G_l`
has the same order as `G_k` and its initial form is `φ_k - Σ β_l φ_l` for some `β_l ∈ gr_M(R)`. -/
theorem exists_initialForm_sub_sum (J : Ideal R) {m : ℕ} (G : Fin m → R)
    (hG : IsStandardBase R J G) {i : ℕ} (hi : i ≤ m) (k : Fin m) (hik : i ≤ (k : ℕ))
    (h : Fin i → R)
    (hh : ∀ l : Fin i, Ideal.ordElem (maximalIdeal R) (G k) -
      Ideal.ordElem (maximalIdeal R) (G (Fin.castLE hi l)) ≤ Ideal.ordElem (maximalIdeal R) (h l)) :
    ∃ β : Fin i → AssocGraded (maximalIdeal R),
      Ideal.ordElem (maximalIdeal R) (G k - ∑ l, h l * G (Fin.castLE hi l)) =
          Ideal.ordElem (maximalIdeal R) (G k) ∧
        initialForm (maximalIdeal R) (G k - ∑ l, h l * G (Fin.castLE hi l)) =
          initialForm (maximalIdeal R) (G k) -
            ∑ l, β l * initialForm (maximalIdeal R) (G (Fin.castLE hi l)) := by
  classical
  obtain ⟨hGJ, hφJ, ⟨d, hd, hmono⟩, hspan, hirr⟩ := hG
  have hgM : ∀ j, Ideal.ordElem (maximalIdeal R) (G j) = d j := fun j =>
    ordElem_eq_of_isStandardBase_of_initialForm_mem_homogeneous J G
      ⟨hGJ, hφJ, ⟨d, hd, hmono⟩, hspan, hirr⟩ d hd j
  have hνle : ∀ l : Fin i, d (Fin.castLE hi l) ≤ d k := fun l =>
    hmono (Fin.le_def.mpr (by show (l : ℕ) ≤ (k : ℕ); have := l.2; omega))
  have hhmem : ∀ l : Fin i, h l ∈ maximalIdeal R ^ (d k - d (Fin.castLE hi l)) := by
    intro l
    refine Ideal.mem_pow_of_le_ordElem ?_
    refine le_trans ?_ (hh l)
    rw [hgM, hgM]
    exact (ENat.natCast_sub (d k) (d (Fin.castLE hi l))).symm.le
  have hGj : ∀ l : Fin i, G (Fin.castLE hi l) ∈ maximalIdeal R ^ d (Fin.castLE hi l) :=
    fun l => Ideal.mem_pow_of_ordElem (hgM _)
  have hGk : G k ∈ maximalIdeal R ^ d k := Ideal.mem_pow_of_ordElem (hgM k)
  have hprod : ∀ l : Fin i, h l * G (Fin.castLE hi l) ∈ maximalIdeal R ^ d k := fun l => by
    have := Ideal.mul_mem_mul (hhmem l) (hGj l)
    rwa [← pow_add, Nat.sub_add_cancel (hνle l)] at this
  set β : Fin i → AssocGraded (maximalIdeal R) := fun l =>
    AssocGraded.mk (maximalIdeal R) _ (h l) (hhmem l) with hβ
  have hmk : AssocGraded.mk (maximalIdeal R) (d k) (G k - ∑ l, h l * G (Fin.castLE hi l))
      (sub_mem hGk (sum_mem fun l _ => hprod l)) =
      initialForm (maximalIdeal R) (G k) -
        ∑ l : Fin i, β l * initialForm (maximalIdeal R) (G (Fin.castLE hi l)) := by
    rw [AssocGraded.mk_sub _ _ _ _ hGk (sum_mem fun l _ => hprod l),
      AssocGraded.mk_sum _ _ _ _ hprod, initialForm_eq_mk _ (hgM k)]
    congr 1
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [initialForm_eq_mk _ (hgM _), hβ, AssocGraded.mk_mul_mk]
    have := hνle l
    congr 1
    omega
  have hirrk : initialForm (maximalIdeal R) (G k) ∉
      Ideal.span (Set.range fun l : Fin i =>
        initialForm (maximalIdeal R) (G (Fin.castLE hi l))) := by
    intro hmem
    refine hirr k (Ideal.span_mono ?_ hmem)
    rintro _ ⟨l, rfl⟩
    exact ⟨Fin.castLE hik l, rfl⟩
  have hsum_mem : ∑ l : Fin i, β l * initialForm (maximalIdeal R) (G (Fin.castLE hi l)) ∈
      Ideal.span (Set.range fun l : Fin i => initialForm (maximalIdeal R)
        (G (Fin.castLE hi l))) :=
    Ideal.sum_mem _ fun l _ => Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨l, rfl⟩)
  have hne : AssocGraded.mk (maximalIdeal R) (d k) (G k - ∑ l, h l * G (Fin.castLE hi l))
      (sub_mem hGk (sum_mem fun l _ => hprod l)) ≠ 0 := by
    rw [hmk]
    intro h0
    apply hirrk
    have := sub_eq_zero.mp h0
    rw [this]
    exact hsum_mem
  obtain ⟨hord, hin⟩ := Ideal.ordElem_eq_of_mk_ne_zero _ _ hne
  exact ⟨β, by rw [hord, hgM], by rw [hin, hmk]⟩

/-- **Replacing the members `G_j`, `j ≥ i`, of a standard base** by `G_j - Σ_{l<i} h_{jl} G_l` with
`ν_M(h_{jl}) ≥ ν_M(G_j) - ν_M(G_l)` gives again a standard base of `J`, of the same orders (the
passage from `f` to `f - Σ h_p f_p` of footnote 11, p. 259, applied to the members of the group
`f_{i+1}, …, f_{i+p}` in the proof of Lemma 21, p. 256). -/
theorem isStandardBase_replace (J : Ideal R) {m : ℕ} (G : Fin m → R) (hG : IsStandardBase R J G)
    {i : ℕ} (hi : i ≤ m) (h : Fin m → Fin i → R)
    (hh : ∀ (j : Fin m) (l : Fin i), i ≤ (j : ℕ) →
      Ideal.ordElem (maximalIdeal R) (G j) - Ideal.ordElem (maximalIdeal R) (G (Fin.castLE hi l)) ≤
        Ideal.ordElem (maximalIdeal R) (h j l)) :
    IsStandardBase R J (fun j : Fin m =>
      if i ≤ (j : ℕ) then G j - ∑ l : Fin i, h j l * G (Fin.castLE hi l) else G j) ∧
    ∀ j : Fin m, Ideal.ordElem (maximalIdeal R)
      (if i ≤ (j : ℕ) then G j - ∑ l : Fin i, h j l * G (Fin.castLE hi l) else G j) =
        Ideal.ordElem (maximalIdeal R) (G j) := by
  classical
  have hG' := hG
  obtain ⟨hGJ, hφJ, ⟨d, hd, hmono⟩, hspan, hirr⟩ := hG
  have hgM : ∀ j, Ideal.ordElem (maximalIdeal R) (G j) = d j := fun j =>
    ordElem_eq_of_isStandardBase_of_initialForm_mem_homogeneous J G hG' d hd j
  choose! β hβord hβform using fun (j : Fin m) (hj : i ≤ (j : ℕ)) =>
    exists_initialForm_sub_sum J G hG' hi j hj (h j) (hh j · hj)
  set G' : Fin m → R := fun j =>
    if i ≤ (j : ℕ) then G j - ∑ l : Fin i, h j l * G (Fin.castLE hi l) else G j with hG'def
  have hG'lt : ∀ j : Fin m, (j : ℕ) < i → G' j = G j := fun j hj => by
    simp [hG'def, not_le.mpr hj]
  have hG'ge : ∀ j : Fin m, i ≤ (j : ℕ) → G' j = G j - ∑ l : Fin i, h j l * G (Fin.castLE hi l) :=
    fun j hj => by simp [hG'def, hj]
  have hord : ∀ j, Ideal.ordElem (maximalIdeal R) (G' j) = d j := by
    intro j
    by_cases hj : i ≤ (j : ℕ)
    · rw [hG'ge j hj, hβord j hj, hgM]
    · rw [hG'lt j (not_le.mp hj), hgM]
  have hform : ∀ j : Fin m, i ≤ (j : ℕ) → initialForm (maximalIdeal R) (G' j) =
      initialForm (maximalIdeal R) (G j) -
        ∑ l : Fin i, β j l * initialForm (maximalIdeal R) (G (Fin.castLE hi l)) := by
    intro j hj
    rw [hG'ge j hj, hβform j hj]
  have hformlt : ∀ j : Fin m, (j : ℕ) < i →
      initialForm (maximalIdeal R) (G' j) = initialForm (maximalIdeal R) (G j) := fun j hj => by
    rw [hG'lt j hj]
  refine ⟨⟨fun j => ?_, ?_, ?_, ?_, ?_⟩, fun j => (hord j).trans (hgM j).symm⟩
  · -- `G'_j ∈ J`
    by_cases hj : i ≤ (j : ℕ)
    · rw [hG'ge j hj]
      exact sub_mem (hGJ j) (Ideal.sum_mem _ fun l _ => J.mul_mem_left _ (hGJ _))
    · rw [hG'lt j (not_le.mp hj)]
      exact hGJ j
  · -- the initial forms lie in `gr(J)`
    intro j
    exact Ideal.subset_span ⟨_, by
      by_cases hj : i ≤ (j : ℕ)
      · rw [hG'ge j hj]
        exact sub_mem (hGJ j) (Ideal.sum_mem _ fun l _ => J.mul_mem_left _ (hGJ _))
      · rw [hG'lt j (not_le.mp hj)]
        exact hGJ j, rfl⟩
  · -- degrees
    refine ⟨d, fun j => ?_, hmono⟩
    show initialForm (maximalIdeal R) (G' j) ∈ _
    rw [initialForm_eq_mk _ (hord j)]
    exact AssocGraded.mk_mem_homogeneous _ _
  · -- generation
    refine le_antisymm ?_ (Ideal.span_le.mpr ?_)
    · rw [hspan]
      refine Ideal.span_le.mpr ?_
      rintro _ ⟨j, rfl⟩
      by_cases hj : i ≤ (j : ℕ)
      · have h1 : initialForm (maximalIdeal R) (G j) = initialForm (maximalIdeal R) (G' j) +
            ∑ l : Fin i, β j l * initialForm (maximalIdeal R) (G (Fin.castLE hi l)) := by
          rw [hform j hj]; ring
        show initialForm (maximalIdeal R) (G j) ∈ _
        rw [h1]
        refine add_mem (Ideal.subset_span ⟨j, rfl⟩) (Ideal.sum_mem _ fun l _ =>
          Ideal.mul_mem_left _ _ ?_)
        refine Ideal.subset_span ⟨Fin.castLE hi l, ?_⟩
        exact hformlt _ l.2
      · refine Ideal.subset_span ⟨j, ?_⟩
        exact hformlt j (not_le.mp hj)
    · rintro _ ⟨j, rfl⟩
      by_cases hj : i ≤ (j : ℕ)
      · exact Ideal.subset_span ⟨_, by
          rw [hG'ge j hj]
          exact sub_mem (hGJ j) (Ideal.sum_mem _ fun l _ => J.mul_mem_left _ (hGJ _)), rfl⟩
      · exact Ideal.subset_span ⟨_, by rw [hG'lt j (not_le.mp hj)]; exact hGJ j, rfl⟩
  · -- irreducibility
    intro j hjmem
    -- every `φ'_l`, `l < j`, lies in `(φ_l : l < j)`
    have hle : Ideal.span (Set.range fun l : Fin j =>
        initialForm (maximalIdeal R) (G' (Fin.castLE j.2.le l))) ≤
        Ideal.span (Set.range fun l : Fin j =>
          initialForm (maximalIdeal R) (G (Fin.castLE j.2.le l))) := by
      refine Ideal.span_le.mpr ?_
      rintro _ ⟨l, rfl⟩
      by_cases hl : i ≤ ((Fin.castLE j.2.le l : Fin m) : ℕ)
      · show initialForm (maximalIdeal R) (G' (Fin.castLE j.2.le l)) ∈ _
        rw [hform _ hl]
        refine sub_mem (Ideal.subset_span ⟨l, rfl⟩) (Ideal.sum_mem _ fun l' _ =>
          Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨⟨l', ?_⟩, rfl⟩))
        have h1 := l'.2
        have h2 : ((Fin.castLE j.2.le l : Fin m) : ℕ) < j := l.2
        show (l' : ℕ) < (j : ℕ)
        have h3 : ((Fin.castLE j.2.le l : Fin m) : ℕ) = (l : ℕ) := rfl
        omega
      · refine Ideal.subset_span ⟨l, ?_⟩
        exact (hformlt _ (not_le.mp hl)).symm
    have h1 := hle hjmem
    by_cases hj : i ≤ (j : ℕ)
    · refine hirr j ?_
      have h2 : initialForm (maximalIdeal R) (G j) = initialForm (maximalIdeal R) (G' j) +
          ∑ l : Fin i, β j l * initialForm (maximalIdeal R) (G (Fin.castLE hi l)) := by
        rw [hform j hj]; ring
      show initialForm (maximalIdeal R) (G j) ∈ _
      rw [h2]
      refine add_mem h1 (Ideal.sum_mem _ fun l _ => Ideal.mul_mem_left _ _ ?_)
      refine Ideal.subset_span ⟨⟨l, ?_⟩, rfl⟩
      have := l.2
      show (l : ℕ) < (j : ℕ)
      omega
    · refine hirr j ?_
      have : initialForm (maximalIdeal R) (G' j) = initialForm (maximalIdeal R) (G j) :=
        hformlt j (not_le.mp hj)
      have h3 : initialForm (maximalIdeal R) (G' j) ∈ Ideal.span (Set.range fun l : Fin j =>
          initialForm (maximalIdeal R) (G' (Fin.castLE j.2.le l))) := hjmem
      rw [this] at h3
      exact hle h3

end StandardBaseReplace

section GroupExistence

variable {R : Type u} [CommRing R] [IsRegularLocalRing R] (F : RegularFrame R)

/-- **The group `f_{i+1}, …, f_{i+p}` of the proof of Lemma 21** (p. 256: "By means of Lemma 17 of
§7, we can choose elements `f_{i+j}` (`1 ≤ j ≤ p`) of `J` such that each of the `f_{i+j}` is
normalized by `(f₁, …, f_i)` with respect to `(S; z₁, …, z_r)` and that `(f₁, …, f_i, f_{i+1}, …,
f_{i+p})` can be extended to a standard base of `J`").  Here `f_{i+1} = f'` is the given element,
which is normalized by hypothesis; a standard base `G` of `J` beginning with `(f₁, …, f_i, f')` is
changed, in the places `j > i`, by Lemma 17, into a standard base whose members `G_j`, `j ≥ i`,
are all normalized by `(f₁, …, f_i)`. -/
theorem RegularFrame.exists_normalized_group [IsAdicComplete (maximalIdeal R) R] (J : Ideal R)
    {i : ℕ} (f : Fin i → R) (f' : R)
    (h1 : ExtendsToStandardBase J (Fin.snoc f f' : Fin (i + 1) → R))
    (hf : ∀ j, initialForm (maximalIdeal R) (f j) ∈ F.assocSubalgebra)
    (h3 : F.IsNormalizedBy f f') :
    ∃ (m : ℕ) (hi : i < m) (G : Fin m → R), IsStandardBase R J G ∧
      (∀ j : Fin i, G ⟨j, by omega⟩ = f j) ∧ G ⟨i, hi⟩ = f' ∧
      ∀ j : Fin m, i ≤ (j : ℕ) → F.IsNormalizedBy f (G j) := by
  classical
  obtain ⟨m, G0, hle, hG0, hGf⟩ := h1
  have hi : i ≤ m := by omega
  have hGfl : ∀ l : Fin i, G0 (Fin.castLE hi l) = f l := fun l => by
    have := hGf (Fin.castSucc l)
    rw [Fin.snoc_castSucc] at this
    exact this
  have hGfi : G0 ⟨i, by omega⟩ = f' := by
    have := hGf (Fin.last i)
    rw [Fin.snoc_last] at this
    exact this
  have hex : ∀ j : Fin m, i ≤ (j : ℕ) → ∃ h : Fin i → R,
      (∀ l : Fin i, Ideal.ordElem (maximalIdeal R) (G0 j) -
        Ideal.ordElem (maximalIdeal R) (G0 (Fin.castLE hi l)) ≤
          Ideal.ordElem (maximalIdeal R) (h l)) ∧
      F.IsNormalizedBy f (G0 j - ∑ l, h l * G0 (Fin.castLE hi l)) ∧
      ((j : ℕ) = i → h = 0) := by
    intro j hj
    by_cases hji : (j : ℕ) = i
    · refine ⟨0, fun l => ?_, ?_, fun _ => rfl⟩
      · have htop : Ideal.ordElem (maximalIdeal R) ((0 : Fin i → R) l) = ⊤ :=
          Ideal.ordElem_eq_top_iff.mpr fun n => zero_mem _
        rw [htop]
        exact le_top
      · have hj' : G0 j = f' := by
          have : j = ⟨i, by omega⟩ := Fin.ext hji
          rw [this, hGfi]
        simpa [hj'] using h3
    · obtain ⟨h, hh1, hh2⟩ := F.exists_isNormalizedBy_sub_sum f hf (G0 j)
      refine ⟨h, fun l => ?_, ?_, fun hh => absurd hh hji⟩
      · rw [hGfl l]; exact hh1 l
      · have : ∑ l, h l * G0 (Fin.castLE hi l) = ∑ l, h l * f l :=
          Finset.sum_congr rfl fun l _ => by rw [hGfl l]
        rw [this]
        exact hh2
  choose! h hh hnorm hzero using hex
  obtain ⟨hG', -⟩ := isStandardBase_replace J G0 hG0 hi h (fun j l hj => hh j hj l)
  refine ⟨m, by omega, _, hG', fun j => ?_, ?_, fun j hj => ?_⟩
  · show (if i ≤ ((⟨j, by omega⟩ : Fin m) : ℕ) then _ else G0 ⟨j, by omega⟩) = f j
    have hnl : ¬ i ≤ ((⟨j, by omega⟩ : Fin m) : ℕ) := not_le.mpr j.2
    simp only [hnl, ↓reduceIte]
    exact hGfl j
  · show (if i ≤ i then G0 ⟨i, by omega⟩ - ∑ l : Fin i, h ⟨i, by omega⟩ l * G0 (Fin.castLE hi l)
      else G0 ⟨i, by omega⟩) = f'
    simp only [le_refl, ↓reduceIte]
    rw [hzero ⟨i, by omega⟩ le_rfl rfl, hGfi]
    simp
  · show F.IsNormalizedBy f (if i ≤ (j : ℕ) then G0 j - ∑ l : Fin i, h j l * G0 (Fin.castLE hi l)
      else G0 j)
    simp only [hj, ↓reduceIte]
    exact hnorm j hj

end GroupExistence

section PolyAux

open MvPolynomial

/-- The homogeneous component of degree `μ ≤ ν` of `g F`, for a form `F` of degree `ν`: it is
`0` for `μ < ν` and `g(0) F` for `μ = ν`. -/
theorem homogeneousComponent_mul_form {σ E : Type*} [CommRing E]
    {F : MvPolynomial σ E} {ν : ℕ} (hF : F ∈ homogeneousSubmodule σ E ν)
    (g : MvPolynomial σ E) (μ : ℕ) (hμ : μ ≤ ν) :
    homogeneousComponent μ (g * F) = if μ = ν then C (g.coeff 0) * F else 0 := by
  classical
  conv_lhs => rw [← sum_homogeneousComponent g]
  rw [Finset.sum_mul, map_sum]
  have h : ∀ i, homogeneousComponent μ (homogeneousComponent i g * F) =
      if μ = i + ν then homogeneousComponent i g * F else 0 := fun i =>
    homogeneousComponent_of_mem ((homogeneousComponent_isHomogeneous i g).mul hF)
  simp_rw [h]
  split_ifs with hμν
  · subst hμν
    rw [Finset.sum_eq_single 0]
    · simp [homogeneousComponent_zero]
    · intro i _ hi
      rw [ite_eq_right (by omega)]
    · intro h0
      exact absurd (Finset.mem_range.mpr (Nat.succ_pos _)) h0
  · exact Finset.sum_eq_zero fun i _ => ite_eq_right (by omega)

/-- The homogeneous components of an element of `E[T]`, `T` a set of linear forms, lie in `E[T]`. -/
theorem homogeneousComponent_mem_adjoin_of_linear {σ E : Type*} [CommRing E]
    {T : Set (MvPolynomial σ E)} (hT : T ⊆ homogeneousSubmodule σ E 1)
    {h : MvPolynomial σ E} (hh : h ∈ Algebra.adjoin E T) (μ : ℕ) :
    homogeneousComponent μ h ∈ Algebra.adjoin E T := by
  classical
  induction hh using Algebra.adjoin_induction generalizing μ with
  | mem x hx =>
    rw [homogeneousComponent_of_mem (hT hx)]
    split_ifs
    · exact Algebra.subset_adjoin hx
    · exact zero_mem _
  | algebraMap r =>
    rw [MvPolynomial.algebraMap_eq, homogeneousComponent_of_mem (isHomogeneous_C σ r)]
    split_ifs
    · exact Subalgebra.algebraMap_mem _ r
    · exact zero_mem _
  | add x y _ _ hx hy =>
    rw [map_add]
    exact add_mem (hx μ) (hy μ)
  | mul x y _ _ hx hy =>
    rw [← sum_homogeneousComponent x, ← sum_homogeneousComponent y, Finset.sum_mul_sum, map_sum]
    refine sum_mem fun i _ => ?_
    rw [map_sum]
    refine sum_mem fun j _ => ?_
    rw [homogeneousComponent_of_mem ((homogeneousComponent_isHomogeneous i x).mul
      (homogeneousComponent_isHomogeneous j y))]
    split_ifs
    · exact mul_mem (hx i) (hy j)
    · exact zero_mem _


/-- If a form `F` of degree `ν` lies in `E[T]` (`T` a module of linear forms), then `T` has the
property of Lemma 10 for the principal ideal `(F)` up to degree `ν`. -/
theorem isTauSubmoduleMv_span_singleton {E : Type u} [Field E] {m : ℕ}
    {F : MvPolynomial (Fin m) E} {ν : ℕ} (hF : F ∈ homogeneousSubmodule (Fin m) E ν)
    {T : Submodule E (MvPolynomial (Fin m) E)} (hT : T ≤ homogeneousSubmodule (Fin m) E 1)
    (hFT : F ∈ Algebra.adjoin E (T : Set (MvPolynomial (Fin m) E))) :
    IsTauSubmoduleMv E m (Ideal.span {F}) T ν := by
  refine ⟨hT, fun μ hμ ψ hψ => ⟨fun hψF => ?_, fun h => ?_⟩⟩
  · obtain ⟨g, rfl⟩ := Ideal.mem_span_singleton'.mp hψF
    have hgF : g * F = homogeneousComponent μ (g * F) := by
      rw [homogeneousComponent_of_mem hψ, ite_eq_left rfl]
    rw [hgF, homogeneousComponent_mul_form hF g μ hμ]
    split_ifs
    · exact Ideal.mul_mem_left _ _
        (Ideal.subset_span ⟨Ideal.mem_span_singleton_self F, hFT⟩)
    · exact zero_mem _
  · refine (Ideal.span_le.mpr ?_) h
    exact fun x hx => hx.1

/-- Conversely, if `L` has the property of Lemma 10 for `(F)` up to the degree `ν` of the form
`F`, then `F ∈ k[L]`. -/
theorem mem_adjoin_of_isTauSubmoduleMv_span_singleton {E : Type u} [Field E] {m : ℕ}
    {F : MvPolynomial (Fin m) E} {ν : ℕ} (hF : F ∈ homogeneousSubmodule (Fin m) E ν)
    {L : Submodule E (MvPolynomial (Fin m) E)}
    (hL : IsTauSubmoduleMv E m (Ideal.span {F}) L ν) :
    F ∈ Algebra.adjoin E (L : Set (MvPolynomial (Fin m) E)) := by
  have hmem := (hL.2 ν le_rfl F hF).mp (Ideal.mem_span_singleton_self F)
  -- the degree-`ν` component maps `span((F) ∩ E[L])` into `E[L]`
  have key : ∀ x ∈ Ideal.span ((Ideal.span {F} : Set (MvPolynomial (Fin m) E)) ∩
      (Algebra.adjoin E (L : Set (MvPolynomial (Fin m) E)) : Set (MvPolynomial (Fin m) E))),
      x ∈ Ideal.span {F} ∧
        homogeneousComponent ν x ∈ Algebra.adjoin E (L : Set (MvPolynomial (Fin m) E)) := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      exact ⟨hx.1, homogeneousComponent_mem_adjoin_of_linear (fun y hy => hL.1 hy) hx.2 ν⟩
    | zero => exact ⟨zero_mem _, by rw [map_zero]; exact zero_mem _⟩
    | add x y _ _ hx hy =>
      exact ⟨add_mem hx.1 hy.1, by rw [map_add]; exact add_mem hx.2 hy.2⟩
    | smul a x _ hx =>
      refine ⟨Ideal.mul_mem_left _ a hx.1, ?_⟩
      obtain ⟨g, rfl⟩ := Ideal.mem_span_singleton'.mp hx.1
      have h2 := hx.2
      rw [homogeneousComponent_mul_form hF g ν le_rfl, ite_eq_left rfl] at h2
      rw [smul_eq_mul, ← mul_assoc, homogeneousComponent_mul_form hF (a * g) ν le_rfl,
        ite_eq_left rfl, ← constantCoeff_eq, map_mul, constantCoeff_eq, constantCoeff_eq,
        map_mul, mul_assoc]
      exact mul_mem (by rw [← MvPolynomial.algebraMap_eq]; exact Subalgebra.algebraMap_mem _ _) h2
  have := (key F hmem).2
  rwa [homogeneousComponent_of_mem hF, ite_eq_left rfl] at this

end PolyAux

section StandardBase

variable {R : Type u} [CommRing R] [IsRegularLocalRing R] (J : Ideal R) {m : ℕ} (f : Fin m → R)

/-- The low-degree components of an element of `gr_M(J, R)` lie in the ideal generated by the
initial forms of the first members of a standard base: those `f_j` with `ν_M(f_j) ≤ μ₀`. -/
theorem proj_mem_span_initialSegment (hf : IsStandardBase R J f) {m' : ℕ} (hm' : m' ≤ m) {μ₀ : ℕ}
    (hhigh : ∀ j : Fin m, m' ≤ (j : ℕ) → (μ₀ : ℕ∞) < Ideal.ordElem (maximalIdeal R) (f j))
    {x : AssocGraded (maximalIdeal R)} (hx : x ∈ grIdeal (maximalIdeal R) J) {k : ℕ}
    (hk : k ≤ μ₀) :
    AssocGraded.proj (maximalIdeal R) k x ∈ Ideal.span (Set.range fun j : Fin m' =>
      initialForm (maximalIdeal R) (f (Fin.castLE hm' j))) := by
  classical
  obtain ⟨-, ⟨d, hd, -⟩, hspan, -⟩ := hf.2
  rw [hspan] at hx
  obtain ⟨c, rfl⟩ := Ideal.mem_span_range_iff_exists_fun.mp hx
  rw [map_sum]
  refine Ideal.sum_mem _ fun t _ => ?_
  rw [AssocGraded.proj_mul_of_mem_homogeneous _ _ _ (hd t)]
  split_ifs with hdt
  · refine Ideal.mul_mem_left _ _ ?_
    have hlt : (t : ℕ) < m' := by
      by_contra hge
      have := hhigh t (not_lt.mp hge)
      rw [ordElem_eq_of_isStandardBase_of_initialForm_mem_homogeneous J f hf d hd t] at this
      have h2 : (d t : ℕ∞) ≤ μ₀ := by exact_mod_cast hdt.trans hk
      exact absurd this (not_lt.mpr h2)
    exact Ideal.subset_span ⟨⟨t, hlt⟩, rfl⟩
  · exact zero_mem _

/-- **Definition 6/7 versus Definition 10* for a standard base** (p. 251, "the `T` of Definition 10*
for a standard base is the `T_a` of Definition 7"): if `f` is a standard base of `J` and the first
`m'` members are exactly those with `ν_M(f_j) ≤ μ₀`, a `k`-submodule `T` of `gr¹_M(R)` has the
property of Definition 6 up to degree `μ₀` for `J` iff it has the property of Definition 10* for
`(f₁, …, f_{m'})`. -/
theorem isTauSubmodule_iff_isTauZSubmodule_initialSegment (hf : IsStandardBase R J f) {m' : ℕ}
    (hm' : m' ≤ m) {μ₀ : ℕ}
    (hlow : ∀ j : Fin m, (j : ℕ) < m' → Ideal.ordElem (maximalIdeal R) (f j) ≤ μ₀)
    (hhigh : ∀ j : Fin m, m' ≤ (j : ℕ) → (μ₀ : ℕ∞) < Ideal.ordElem (maximalIdeal R) (f j))
    (T : Submodule (R ⧸ maximalIdeal R) (AssocGraded (maximalIdeal R))) :
    IsTauSubmodule R J T μ₀ ↔
      IsTauZSubmodule R (fun j : Fin m' => f (Fin.castLE hm' j)) T := by
  classical
  obtain ⟨hφJ, ⟨d, hd, -⟩, -, -⟩ := hf.2
  set B : Ideal (AssocGraded (maximalIdeal R)) := Ideal.span (Set.range fun j : Fin m' =>
    initialForm (maximalIdeal R) (f (Fin.castLE hm' j))) with hB
  set A := Algebra.adjoin (R ⧸ maximalIdeal R) (T : Set (AssocGraded (maximalIdeal R))) with hA
  have hBJ : B ≤ grIdeal (maximalIdeal R) J := Ideal.span_le.mpr (by
    rintro _ ⟨j, rfl⟩
    exact hφJ _)
  unfold IsTauSubmodule IsTauZSubmodule
  constructor
  · rintro ⟨hT, h⟩
    refine ⟨hT, le_antisymm (Ideal.span_le.mpr fun x hx => hx.1) ?_⟩
    rw [Ideal.span_le]
    rintro _ ⟨j, rfl⟩
    set j' : Fin m := Fin.castLE hm' j
    have hdj : (d j' : ℕ) ≤ μ₀ := by
      have := hlow j' (by simp [j'])
      rwa [ordElem_eq_of_isStandardBase_of_initialForm_mem_homogeneous J f hf d hd j',
        Nat.cast_le] at this
    have hmem : initialForm (maximalIdeal R) (f j') ∈ Ideal.span
        ((grIdeal (maximalIdeal R) J : Set (AssocGraded (maximalIdeal R))) ∩ (A : Set _)) :=
      (h (d j') hdj _ (hd j')).mp (hφJ j')
    -- every low-degree component of an element of `span (gr(J) ∩ k[T])` is in `span (B ∩ k[T])`
    have key : ∀ x ∈ Ideal.span
        ((grIdeal (maximalIdeal R) J : Set (AssocGraded (maximalIdeal R))) ∩ (A : Set _)),
        ∀ k ≤ μ₀, AssocGraded.proj (maximalIdeal R) k x ∈
          Ideal.span ((B : Set (AssocGraded (maximalIdeal R))) ∩ (A : Set _)) := by
      intro x hx
      induction hx using Submodule.span_induction with
      | mem a ha =>
        intro k hk
        exact Ideal.subset_span ⟨proj_mem_span_initialSegment J f hf hm' hhigh ha.1 hk,
          AssocGraded.proj_mem_adjoin _ (fun s hs => hT hs) ha.2 k⟩
      | zero => intro k _; rw [map_zero]; exact zero_mem _
      | add x y _ _ hx hy => intro k hk; rw [map_add]; exact add_mem (hx k hk) (hy k hk)
      | smul c x _ hx =>
        intro k hk
        obtain ⟨N, hN⟩ := AssocGraded.exists_eq_sum_proj (maximalIdeal R) x
        have hx' := hN (max N (k + 1)) (le_max_left _ _)
        rw [smul_eq_mul]
        have hsum : c * x = ∑ i ∈ Finset.range (max N (k + 1)),
            c * AssocGraded.proj (maximalIdeal R) i x := by
          rw [← Finset.mul_sum, ← hx']
        rw [hsum, map_sum]
        refine Ideal.sum_mem _ fun i hi => ?_
        rw [AssocGraded.proj_mul_of_mem_homogeneous _ _ _
          (AssocGraded.proj_mem_homogeneous (maximalIdeal R) i x)]
        split_ifs with hik
        · exact Ideal.mul_mem_left _ _ (hx i (hik.trans hk))
        · exact zero_mem _
    have := key _ hmem (d j') hdj
    rwa [AssocGraded.proj_of_mem_homogeneous _ (hd j')] at this
  · rintro ⟨hT, h⟩
    refine ⟨hT, fun μ hμ ψ hψ => ⟨fun hψJ => ?_, fun hψ => ?_⟩⟩
    · have h1 := proj_mem_span_initialSegment J f hf hm' hhigh hψJ hμ
      rw [AssocGraded.proj_of_mem_homogeneous _ hψ] at h1
      rw [← h] at h1
      refine Ideal.span_mono (fun x hx => ?_) h1
      exact ⟨hBJ hx.1, hx.2⟩
    · exact (Ideal.span_le.mpr fun x hx => hx.1) hψ

/-- The members of a standard base with `ν_M ≤ μ₀` form an initial segment. -/
theorem exists_initialSegment_length (hf : IsStandardBase R J f) (μ₀ : ℕ) :
    ∃ (m' : ℕ) (_ : m' ≤ m),
      (∀ j : Fin m, (j : ℕ) < m' → Ideal.ordElem (maximalIdeal R) (f j) ≤ μ₀) ∧
      (∀ j : Fin m, m' ≤ (j : ℕ) → (μ₀ : ℕ∞) < Ideal.ordElem (maximalIdeal R) (f j)) := by
  classical
  obtain ⟨-, ⟨d, hd, hmono⟩, -, -⟩ := hf.2
  have hord := ordElem_eq_of_isStandardBase_of_initialForm_mem_homogeneous J f hf d hd
  by_cases h : ∃ j : Fin m, μ₀ < d j
  · have hex : ∃ n, ∃ hn : n < m, μ₀ < d ⟨n, hn⟩ := by
      obtain ⟨j, hj⟩ := h
      exact ⟨j, j.2, hj⟩
    have hj₀ := Nat.find_spec hex
    refine ⟨Nat.find hex, hj₀.1.le, fun j hj => ?_, fun j hj => ?_⟩
    · have hnot := Nat.find_min hex hj
      rw [hord j]
      have : ¬ μ₀ < d j := fun hlt => hnot ⟨j.2, hlt⟩
      exact_mod_cast not_lt.mp this
    · rw [hord j]
      have h1 : d ⟨Nat.find hex, hj₀.1⟩ ≤ d j := hmono (Fin.mk_le_of_le_val hj)
      exact_mod_cast hj₀.2.trans_le h1
  · push Not at h
    refine ⟨m, le_rfl, fun j _ => ?_, fun j hj => absurd j.2 (by omega)⟩
    rw [hord j]
    exact_mod_cast h j

end StandardBase

section PrefixMonotone

variable {R : Type u} [CommRing R] [IsRegularLocalRing R]

/-- **The property of Definition 6 gives the property of Definition 10* for every initial segment
of a standard base** (p. 257: "`T*` must contain `W₁, …, W_r` … by (8) and (b)"; the ideal
generated by the initial forms of the first `m'` members of a standard base of `J` is the part of
`gr_M(J, R)` in the degrees below `ν_M(f_{m'})`, up to the generators of the same degree).  If
`T` has the property of Definition 6 up to degree `μ₀` and `ν_M(f_j) ≤ μ₀` for `j < m'`, then
`T` has the property of Definition 10* for `(f₁, …, f_{m'})`.  (Only the degree-`ν_M(f_j)`
component of an element of `gr_M(J, R) ∩ k[T]`-combinations can involve generators of the same
degree not in the segment; Lemma 15's decomposition
`AssocGraded.exists_proj_eq_add_of_mem_span` shows that this part is again in `gr_M(J, R) ∩ k[T]`,
and it lies in the ideal of the segment since the initial form `φ_j` does.) -/
theorem isTauZSubmodule_prefix_of_isTauSubmodule (J : Ideal R) {m : ℕ} (f : Fin m → R)
    (hf : IsStandardBase R J f) {m' : ℕ} (hm' : m' ≤ m) {μ₀ : ℕ}
    (hlow : ∀ j : Fin m, (j : ℕ) < m' → Ideal.ordElem (maximalIdeal R) (f j) ≤ μ₀)
    {T : Submodule (R ⧸ maximalIdeal R) (AssocGraded (maximalIdeal R))}
    (hT : IsTauSubmodule R J T μ₀) :
    IsTauZSubmodule R (fun j : Fin m' => f (Fin.castLE hm' j)) T := by
  classical
  obtain ⟨hφJ, ⟨d, hd, hmono⟩, hspan, hirr⟩ := hf.2
  have hord : ∀ j, Ideal.ordElem (maximalIdeal R) (f j) = d j := fun j =>
    ordElem_eq_of_isStandardBase_of_initialForm_mem_homogeneous J f hf d hd j
  set A := Algebra.adjoin (R ⧸ maximalIdeal R) (T : Set (AssocGraded (maximalIdeal R))) with hA
  set Bi : Ideal (AssocGraded (maximalIdeal R)) := Ideal.span (Set.range fun j : Fin m' =>
    initialForm (maximalIdeal R) (f (Fin.castLE hm' j))) with hBi
  set W : Set (AssocGraded (maximalIdeal R)) :=
    {w | w ∈ grIdeal (maximalIdeal R) J ∧ w ∈ A} with hW
  -- the homogeneous components of `gr_M(J, R)` lie in `gr_M(J, R)`
  have hproj_gr : ∀ w ∈ grIdeal (maximalIdeal R) J, ∀ k : ℕ,
      AssocGraded.proj (maximalIdeal R) k w ∈ grIdeal (maximalIdeal R) J := by
    intro w hw k
    have h1 := proj_mem_span_initialSegment J f hf le_rfl (μ₀ := k)
      (fun j hj => absurd j.2 (by omega)) hw le_rfl
    refine (Ideal.span_le.mpr ?_ : Ideal.span (Set.range fun j : Fin m =>
      initialForm (maximalIdeal R) (f (Fin.castLE le_rfl j))) ≤ _) h1
    rintro _ ⟨j, rfl⟩
    exact hφJ _
  have hWp : ∀ w ∈ W, ∀ k, AssocGraded.proj (maximalIdeal R) k w ∈ W := fun w hw k =>
    ⟨hproj_gr w hw.1 k, AssocGraded.proj_mem_adjoin (maximalIdeal R)
      (fun s hs => hT.1 hs) hw.2 k⟩
  have hWs : ∀ c ∈ AssocGraded.homogeneous (maximalIdeal R) 0, ∀ w ∈ W, c * w ∈ W := by
    intro c hc w hw
    obtain ⟨c₀, rfl⟩ := AssocGraded.exists_eq_algebraMap_of_mem_homogeneous_zero _ hc
    exact ⟨Ideal.mul_mem_left _ _ hw.1, mul_mem (Subalgebra.algebraMap_mem _ c₀) hw.2⟩
  refine ⟨hT.1, le_antisymm (Ideal.span_le.mpr fun x hx => hx.1) ?_⟩
  refine Ideal.span_le.mpr ?_
  rintro _ ⟨l, rfl⟩
  set j : Fin m := Fin.castLE hm' l with hj
  have hjm' : (j : ℕ) < m' := l.2
  have hφj : initialForm (maximalIdeal R) (f j) ∈ Bi := Ideal.subset_span ⟨l, rfl⟩
  have hDμ : d j ≤ μ₀ := by
    have := hlow j hjm'
    rwa [hord j, Nat.cast_le] at this
  have hmem : initialForm (maximalIdeal R) (f j) ∈ Ideal.span W :=
    (hT.2 (d j) hDμ _ (hd j)).mp (hφJ j)
  obtain ⟨B, w', hB, hw'W, hw'hom, hproj⟩ :=
    AssocGraded.exists_proj_eq_add_of_mem_span (maximalIdeal R) W hWp (zero_mem _ |> fun h =>
      ⟨h, zero_mem _⟩) (fun w hw w' hw' => ⟨add_mem hw.1 hw'.1, add_mem hw.2 hw'.2⟩) hWs hmem
      (d j)
  rw [AssocGraded.proj_of_mem_homogeneous _ (hd j)] at hproj
  have hproj' : initialForm (maximalIdeal R) (f j) = B + w' := hproj
  -- the generators of `B` lie in `Bi ∩ A`
  have hgen : ∀ w ∈ {w | w ∈ W ∧ ∃ d' < d j, w ∈ AssocGraded.homogeneous (maximalIdeal R) d'},
      w ∈ Bi ∧ w ∈ A := by
    rintro w ⟨hwW, d', hd'j, hwd'⟩
    obtain ⟨N₀, hN₀m, hN₀low, hN₀high⟩ := exists_initialSegment_length J f hf (d j - 1)
    have hk : d' ≤ d j - 1 := by omega
    have h1 := proj_mem_span_initialSegment J f hf hN₀m hN₀high hwW.1 hk
    rw [AssocGraded.proj_of_mem_homogeneous _ hwd'] at h1
    refine ⟨?_, hwW.2⟩
    refine (Ideal.span_le.mpr ?_ : Ideal.span (Set.range fun l' : Fin N₀ =>
      initialForm (maximalIdeal R) (f (Fin.castLE hN₀m l'))) ≤ Bi) h1
    rintro _ ⟨l', rfl⟩
    have hl'j : ((Fin.castLE hN₀m l' : Fin m) : ℕ) < (j : ℕ) := by
      by_contra hcon
      have h2 := hmono (show j ≤ Fin.castLE hN₀m l' from not_lt.mp hcon)
      have h3 := hN₀low (Fin.castLE hN₀m l') l'.2
      rw [hord, Nat.cast_le] at h3
      omega
    exact Ideal.subset_span ⟨⟨(Fin.castLE hN₀m l' : Fin m), by omega⟩, rfl⟩
  have hBBi : B ∈ Ideal.span (Bi ∩ A : Set (AssocGraded (maximalIdeal R))) :=
    (Ideal.span_mono fun w hw => hgen w hw) hB
  have hw'Bi : w' ∈ Bi := by
    have hB' : B ∈ Bi := by
      refine (Ideal.span_le.mpr ?_ : Ideal.span {w | w ∈ W ∧ ∃ d' < d j,
        w ∈ AssocGraded.homogeneous (maximalIdeal R) d'} ≤ Bi) hB
      exact fun w hw => (hgen w hw).1
    have : w' = initialForm (maximalIdeal R) (f j) - B := by rw [hproj']; ring
    rw [this]
    exact sub_mem hφj hB'
  show initialForm (maximalIdeal R) (f j) ∈ _
  rw [hproj']
  exact add_mem hBBi (Ideal.subset_span ⟨hw'Bi, hw'W.2⟩)

end PrefixMonotone

section SemiModelPush

open MvPolynomial

namespace SemiModel

variable {k k₁ G : Type u} [Field k] [Field k₁] [CommRing G] [Algebra k₁ G] {n : ℕ}
  (M : SemiModel k k₁ G n)

theorem symm_smul (c : k₁) (y : G) : M.Φ.symm (c • y) = M.ρ.symm c • M.Φ.symm y := by
  apply M.Φ.injective
  rw [RingEquiv.apply_symm_apply, M.map_smul', RingEquiv.apply_symm_apply,
    RingEquiv.apply_symm_apply]

/-- The `k₁`-submodule of `G` of the images of the elements of a `k`-submodule of `k[X]`. -/
def push (T : Submodule k (MvPolynomial (Fin n) k)) : Submodule k₁ G where
  carrier := {y | M.Φ.symm y ∈ T}
  add_mem' := fun {a b} ha hb => by
    simp only [Set.mem_ofPred_eq, map_add] at *
    exact add_mem ha hb
  zero_mem' := by simp
  smul_mem' := fun c y hy => by
    simp only [Set.mem_ofPred_eq] at *
    rw [M.symm_smul]
    exact T.smul_mem _ hy

theorem mem_push {T : Submodule k (MvPolynomial (Fin n) k)} {y : G} :
    y ∈ M.push T ↔ M.Φ.symm y ∈ T := Iff.rfl

theorem pull_push (T : Submodule k (MvPolynomial (Fin n) k)) : M.pull (M.push T) = T := by
  ext p
  rw [mem_pull, mem_push, RingEquiv.symm_apply_apply]

theorem pull_le_iff (T : Submodule k₁ G) (T' : Submodule k (MvPolynomial (Fin n) k)) :
    M.pull T ≤ T' ↔ T ≤ M.push T' := by
  constructor
  · intro h y hy
    rw [mem_push]
    apply h
    rw [mem_pull, RingEquiv.apply_symm_apply]
    exact hy
  · intro h p hp
    have := h hp
    rwa [mem_push, RingEquiv.symm_apply_apply] at this

end SemiModel

end SemiModelPush

section SpanPullback

variable {P G : Type*} [CommRing P] [CommRing G]

theorem mem_span_preimage_iff (e : P ≃+* G) (S : Set G) (p : P) :
    p ∈ Ideal.span (e ⁻¹' S) ↔ e p ∈ Ideal.span S := by
  have h1 : Ideal.span (e ⁻¹' S) = (Ideal.span S).comap e := by
    rw [← Ideal.map_symm, Ideal.map_span]
    congr 1
    ext y
    simp only [Set.mem_image, Set.mem_preimage]
    constructor
    · intro hy
      exact ⟨e y, hy, by simp⟩
    · rintro ⟨s, hs, rfl⟩
      simpa using hs
  rw [h1, Ideal.mem_comap]

end SpanPullback

namespace SemiModel

variable {k k₁ G : Type u} [Field k] [Field k₁] [CommRing G] [Algebra k₁ G] {n : ℕ}
  (M : SemiModel k k₁ G n)

/-- **Transport of the property `((φ) ∩ k[T]) gr = (φ) gr`** along the semilinear isomorphism
`k[X] ≃ G`. -/
theorem span_inter_eq_iff {ι : Type*} (φ : ι → G) (T : Submodule k₁ G) :
    Ideal.span ((Ideal.span (Set.range φ) : Set G) ∩
        (Algebra.adjoin k₁ (T : Set G) : Set G)) = Ideal.span (Set.range φ) ↔
      Ideal.span ((Ideal.span (Set.range fun j => M.Φ.symm (φ j)) :
          Set (MvPolynomial (Fin n) k)) ∩
        (Algebra.adjoin k (M.pull T : Set (MvPolynomial (Fin n) k)) :
          Set (MvPolynomial (Fin n) k))) =
        Ideal.span (Set.range fun j => M.Φ.symm (φ j)) := by
  have hrange : (Set.range fun j => M.Φ.symm (φ j)) = M.Φ ⁻¹' (Set.range φ) := by
    ext p
    constructor
    · rintro ⟨j, rfl⟩
      exact ⟨j, by simp⟩
    · rintro ⟨j, hj⟩
      exact ⟨j, by show M.Φ.symm (φ j) = p; rw [hj]; simp⟩
  have hI : ∀ p, p ∈ Ideal.span (Set.range fun j => M.Φ.symm (φ j)) ↔
      M.Φ p ∈ Ideal.span (Set.range φ) := fun p => by
    rw [hrange]
    exact mem_span_preimage_iff M.Φ _ p
  have hinter : (Ideal.span (Set.range fun j => M.Φ.symm (φ j)) :
      Set (MvPolynomial (Fin n) k)) ∩
        (Algebra.adjoin k (M.pull T : Set (MvPolynomial (Fin n) k)) :
          Set (MvPolynomial (Fin n) k)) =
      M.Φ ⁻¹' ((Ideal.span (Set.range φ) : Set G) ∩
        (Algebra.adjoin k₁ (T : Set G) : Set G)) := by
    ext p
    exact and_congr (hI p) (M.mem_adjoin_pull_iff T p)
  rw [hinter]
  constructor
  · intro h
    ext p
    rw [mem_span_preimage_iff M.Φ _ p, hI p]
    show M.Φ p ∈ Ideal.span _ ↔ _
    rw [h]
  · intro h
    ext y
    obtain ⟨p, rfl⟩ := M.Φ.surjective y
    have := congrArg (fun I : Ideal (MvPolynomial (Fin n) k) => p ∈ I) h
    simp only [eq_iff_iff] at this
    rw [mem_span_preimage_iff M.Φ _ p, hI p] at this
    exact this

end SemiModel

section MvIff

open MvPolynomial

variable (K : Type u) [Field K] (n : ℕ)

/-- For an ideal generated by homogeneous polynomials of degrees `≤ μb`, the property of
Definition 6 up to `μb` is `((q) ∩ K[T]) G = (q)`. -/
theorem isTauSubmoduleMv_iff_span_eq {ι : Type*} (q : ι → MvPolynomial (Fin n) K) (μb : ℕ)
    (hq : ∀ j, ∃ d ≤ μb, q j ∈ homogeneousSubmodule (Fin n) K d)
    (T : Submodule K (MvPolynomial (Fin n) K)) :
    IsTauSubmoduleMv K n (Ideal.span (Set.range q)) T μb ↔
      T ≤ homogeneousSubmodule (Fin n) K 1 ∧
        Ideal.span ((Ideal.span (Set.range q) : Set (MvPolynomial (Fin n) K)) ∩
          (Algebra.adjoin K (T : Set (MvPolynomial (Fin n) K)) :
            Set (MvPolynomial (Fin n) K))) = Ideal.span (Set.range q) := by
  constructor
  · rintro ⟨hT, h⟩
    refine ⟨hT, le_antisymm (Ideal.span_le.mpr fun x hx => hx.1) ?_⟩
    refine Ideal.span_le.mpr ?_
    rintro _ ⟨j, rfl⟩
    obtain ⟨d, hd, hqd⟩ := hq j
    exact (h d hd (q j) hqd).mp (Ideal.subset_span ⟨j, rfl⟩)
  · rintro ⟨hT, h⟩
    refine ⟨hT, fun μ _ ψ _ => ?_⟩
    rw [h]

end MvIff

section TauZTranslation

open MvPolynomial

attribute [local instance] Ideal.Quotient.field

variable {K : Type u} [Field K] {A : Type u} [CommRing A] [IsRegularLocalRing A] {n : ℕ}

/-- **Definition 10* in the polynomial picture**: for a `ρ`-semilinear model `k[X] ≃ gr_M(A)`
compatible with the gradings and a system `f` whose initial forms have degrees `≤ μb`, a
`k`-submodule `T` of `gr_M(A)` has the property of Definition 10* iff its pull-back has the
property of Definition 6 up to `μb` for the ideal generated by the polynomials of the initial
forms. -/
theorem SemiModel.isTauZSubmodule_iff
    (M : SemiModel K (A ⧸ maximalIdeal A) (AssocGraded (maximalIdeal A)) n)
    (hhom : ∀ (d : ℕ) (p : MvPolynomial (Fin n) K), p ∈ homogeneousSubmodule (Fin n) K d ↔
      M.Φ p ∈ AssocGraded.homogeneous (maximalIdeal A) d)
    {m : ℕ} (f : Fin m → A) (μb : ℕ)
    (hdeg : ∀ j, ∃ d ≤ μb, initialForm (maximalIdeal A) (f j) ∈
      AssocGraded.homogeneous (maximalIdeal A) d)
    (T : Submodule (A ⧸ maximalIdeal A) (AssocGraded (maximalIdeal A))) :
    IsTauZSubmodule A f T ↔
      IsTauSubmoduleMv K n (Ideal.span (Set.range fun j =>
        M.Φ.symm (initialForm (maximalIdeal A) (f j)))) (M.pull T) μb := by
  rw [isTauSubmoduleMv_iff_span_eq K n _ μb (fun j => by
    obtain ⟨d, hd, h⟩ := hdeg j
    refine ⟨d, hd, (hhom d _).mpr ?_⟩
    rwa [RingEquiv.apply_symm_apply])]
  unfold IsTauZSubmodule
  rw [M.span_inter_eq_iff (fun j => initialForm (maximalIdeal A) (f j)) T]
  refine and_congr ?_ Iff.rfl
  constructor
  · intro h p hp
    exact (hhom 1 p).mpr (h hp)
  · intro h y hy
    have hp : M.Φ.symm y ∈ M.pull T := by
      rw [SemiModel.mem_pull, RingEquiv.apply_symm_apply]
      exact hy
    have := (hhom 1 _).mp (h hp)
    rwa [RingEquiv.apply_symm_apply] at this

end TauZTranslation

section CoreAssembly

open MvPolynomial
open scoped Classical

attribute [local instance] Ideal.Quotient.field

variable {K : Type u} [Field K] {A A₁ : Type u} [CommRing A] [IsRegularLocalRing A] [CommRing A₁]
  [IsRegularLocalRing A₁] {n : ℕ}

/-- The pull-back of `T` of Definition 10* for a single element, with its characterization
(`φ ∈ k[T]` and minimality, p. 251). -/
theorem SemiModel.singleton_minimal
    (M : SemiModel K (A ⧸ maximalIdeal A) (AssocGraded (maximalIdeal A)) n)
    (hhom : ∀ (d : ℕ) (p : MvPolynomial (Fin n) K), p ∈ homogeneousSubmodule (Fin n) K d ↔
      M.Φ p ∈ AssocGraded.homogeneous (maximalIdeal A) d) (f : A) :
    M.pull (tauZSubmodule A (fun _ : Fin 1 => f)) ≤ homogeneousSubmodule (Fin n) K 1 ∧
    M.Φ.symm (initialForm (maximalIdeal A) f) ∈
      Algebra.adjoin K (M.pull (tauZSubmodule A (fun _ : Fin 1 => f)) :
        Set (MvPolynomial (Fin n) K)) ∧
    ∀ T : Submodule K (MvPolynomial (Fin n) K), T ≤ homogeneousSubmodule (Fin n) K 1 →
      M.Φ.symm (initialForm (maximalIdeal A) f) ∈
          Algebra.adjoin K (T : Set (MvPolynomial (Fin n) K)) →
        M.pull (tauZSubmodule A (fun _ : Fin 1 => f)) ≤ T := by
  have hspec := tauZSubmodule_spec A (fun _ : Fin 1 => f)
  have hφd : initialForm (maximalIdeal A) f ∈
      AssocGraded.homogeneous (maximalIdeal A) (Ideal.ordElem (maximalIdeal A) f).toNat :=
    initialForm_mem_homogeneous_toNat f
  set d := (Ideal.ordElem (maximalIdeal A) f).toNat with hd
  have hdeg : ∀ j : Fin 1, ∃ d' ≤ d, initialForm (maximalIdeal A) ((fun _ : Fin 1 => f) j) ∈
      AssocGraded.homogeneous (maximalIdeal A) d' := fun _ => ⟨d, le_rfl, hφd⟩
  have hq : M.Φ.symm (initialForm (maximalIdeal A) f) ∈ homogeneousSubmodule (Fin n) K d :=
    (hhom d _).mpr (by rw [RingEquiv.apply_symm_apply]; exact hφd)
  have hMv := (M.isTauZSubmodule_iff hhom (fun _ : Fin 1 => f) d hdeg _).mp hspec
  rw [Set.range_const] at hMv
  refine ⟨hMv.1, ?_, ?_⟩
  · exact mem_adjoin_of_isTauSubmoduleMv_span_singleton hq hMv
  · intro T hT hφ
    rw [M.pull_le_iff]
    refine sInf_le (show IsTauZSubmodule A (fun _ : Fin 1 => f) (M.push T) from ?_)
    rw [M.isTauZSubmodule_iff hhom (fun _ : Fin 1 => f) d hdeg, M.pull_push, Set.range_const]
    exact isTauSubmoduleMv_span_singleton hq hT hφ

end CoreAssembly

section GradedSemiModel

open MvPolynomial

attribute [local instance] Ideal.Quotient.field

variable {A : Type u} [CommRing A] [IsRegularLocalRing A] {K : Type u} [Field K]

/-- **The semilinear polynomial picture of `gr_M(A)`** for a regular system of parameters `v`
and a field isomorphism `ρ : K ≃ A/M`: `K[X] → (A/M)[X] ≅ gr_M(A)`, `X_i ↦ [v_i]`. -/
noncomputable def gradedSemiModel (ρ : K ≃+* A ⧸ maximalIdeal A) {n : ℕ} (v : Fin n → A)
    (hspan : Ideal.span (Set.range v) = maximalIdeal A)
    (hdim : (n : WithBot ℕ∞) = ringKrullDim A) :
    SemiModel K (A ⧸ maximalIdeal A) (AssocGraded (maximalIdeal A)) n where
  ρ := ρ
  Φ := (MvPolynomial.mapEquiv (Fin n) ρ).trans (gradedModel v hspan hdim).toRingEquiv
  map_C := fun c => by
    show gradedModel v hspan hdim (MvPolynomial.map (ρ : K →+* _) (C c)) = _
    rw [MvPolynomial.map_C]
    have := (gradedModel v hspan hdim).commutes (ρ c)
    rwa [MvPolynomial.algebraMap_eq] at this

theorem gradedSemiModel_apply (ρ : K ≃+* A ⧸ maximalIdeal A) {n : ℕ} (v : Fin n → A)
    (hspan : Ideal.span (Set.range v) = maximalIdeal A)
    (hdim : (n : WithBot ℕ∞) = ringKrullDim A) (p : MvPolynomial (Fin n) K) :
    (gradedSemiModel ρ v hspan hdim).Φ p =
      gradedModel v hspan hdim (MvPolynomial.map (ρ : K →+* _) p) := rfl

theorem gradedSemiModel_X (ρ : K ≃+* A ⧸ maximalIdeal A) {n : ℕ} (v : Fin n → A)
    (hspan : Ideal.span (Set.range v) = maximalIdeal A)
    (hdim : (n : WithBot ℕ∞) = ringKrullDim A) (i : Fin n) :
    (gradedSemiModel ρ v hspan hdim).Φ (X i) =
      AssocGraded.mk (maximalIdeal A) 1 (v i) (mem_pow_one_of_span_eq hspan i) := by
  rw [gradedSemiModel_apply, MvPolynomial.map_X, gradedModel_X]

theorem gradedSemiModel_symm (ρ : K ≃+* A ⧸ maximalIdeal A) {n : ℕ} (v : Fin n → A)
    (hspan : Ideal.span (Set.range v) = maximalIdeal A)
    (hdim : (n : WithBot ℕ∞) = ringKrullDim A) (y : AssocGraded (maximalIdeal A)) :
    (gradedSemiModel ρ v hspan hdim).Φ.symm y =
      MvPolynomial.map (ρ.symm : A ⧸ maximalIdeal A →+* K)
        ((gradedModel v hspan hdim).symm y) := by
  apply (gradedSemiModel ρ v hspan hdim).Φ.injective
  rw [RingEquiv.apply_symm_apply, gradedSemiModel_apply, MvPolynomial.map_map]
  have : (ρ : K →+* A ⧸ maximalIdeal A).comp (ρ.symm : A ⧸ maximalIdeal A →+* K) =
      RingHom.id _ := by
    ext c
    simp
  rw [this, MvPolynomial.map_id]
  exact ((gradedModel v hspan hdim).apply_symm_apply y).symm

theorem gradedSemiModel_hhom (ρ : K ≃+* A ⧸ maximalIdeal A) {n : ℕ} (v : Fin n → A)
    (hspan : Ideal.span (Set.range v) = maximalIdeal A)
    (hdim : (n : WithBot ℕ∞) = ringKrullDim A) (d : ℕ) (p : MvPolynomial (Fin n) K) :
    p ∈ homogeneousSubmodule (Fin n) K d ↔
      (gradedSemiModel ρ v hspan hdim).Φ p ∈ AssocGraded.homogeneous (maximalIdeal A) d := by
  rw [gradedSemiModel_apply, ← gradedModel_mem_homogeneous_iff, mem_homogeneousSubmodule,
    mem_homogeneousSubmodule]
  constructor
  · intro h
    exact h.map _
  · intro h
    exact IsHomogeneous.of_map ρ.injective h

theorem map_mem_supported_of_mem {R S : Type*} [CommSemiring R] [CommSemiring S] {σ : Type*}
    (f : R →+* S) {p : MvPolynomial σ R} {s : Set σ} (hp : p ∈ supported R s) :
    MvPolynomial.map f p ∈ supported S s := by
  rw [mem_supported] at hp ⊢
  exact (Finset.coe_subset.mpr (vars_map (f := f) (p := p))).trans hp

end GradedSemiModel

section PullSpanRange

open MvPolynomial

namespace SemiModel

variable {k k₁ G : Type u} [Field k] [Field k₁] [CommRing G] [Algebra k₁ G] {n : ℕ}
  (M : SemiModel k k₁ G n)

/-- The pull-back of the span of the images of the variables `X_{idx l}` is the span of these
variables. -/
theorem pull_span_range {r : ℕ} (w : Fin r → G) (idx : Fin r → Fin n)
    (hw : ∀ l, M.Φ (X (idx l)) = w l) :
    M.pull (Submodule.span k₁ (Set.range w)) =
      Submodule.span k (X '' Set.range idx : Set (MvPolynomial (Fin n) k)) := by
  apply le_antisymm
  · rw [M.pull_le_iff, Submodule.span_le]
    rintro _ ⟨l, rfl⟩
    rw [SetLike.mem_coe, M.mem_push, ← hw l, RingEquiv.symm_apply_apply]
    exact Submodule.subset_span ⟨idx l, ⟨l, rfl⟩, rfl⟩
  · rw [Submodule.span_le]
    rintro _ ⟨_, ⟨l, rfl⟩, rfl⟩
    rw [SetLike.mem_coe, M.mem_pull, hw l]
    exact Submodule.subset_span ⟨l, rfl⟩

end SemiModel

end PullSpanRange

section SameModelRank

open MvPolynomial

attribute [local instance] Ideal.Quotient.field

variable {K : Type u} [Field K] {A A₁ : Type u} [CommRing A] [IsRegularLocalRing A] [CommRing A₁]
  [IsRegularLocalRing A₁] {n : ℕ}

/-- **Same polynomials, same `T`** (p. 257: "(11) implies that `τ(g₁, …, g_i) = r`" from
`ψ_j = φ_j(W)`): if two systems have the same initial-form polynomials in the polynomial pictures,
their spaces `T` of Definition 10* have the same rank. -/
theorem tauZSubmodule_finrank_eq_of_models
    (M : SemiModel K (A ⧸ maximalIdeal A) (AssocGraded (maximalIdeal A)) n)
    (M₁ : SemiModel K (A₁ ⧸ maximalIdeal A₁) (AssocGraded (maximalIdeal A₁)) n)
    (hhom : ∀ (d : ℕ) (p : MvPolynomial (Fin n) K), p ∈ homogeneousSubmodule (Fin n) K d ↔
      M.Φ p ∈ AssocGraded.homogeneous (maximalIdeal A) d)
    (hhom₁ : ∀ (d : ℕ) (p : MvPolynomial (Fin n) K), p ∈ homogeneousSubmodule (Fin n) K d ↔
      M₁.Φ p ∈ AssocGraded.homogeneous (maximalIdeal A₁) d)
    {m : ℕ} (f : Fin m → A) (g : Fin m → A₁) (μb : ℕ)
    (hdeg : ∀ j, ∃ d ≤ μb, initialForm (maximalIdeal A) (f j) ∈
      AssocGraded.homogeneous (maximalIdeal A) d)
    (hq : ∀ j, M₁.Φ.symm (initialForm (maximalIdeal A₁) (g j)) =
      M.Φ.symm (initialForm (maximalIdeal A) (f j))) :
    Module.finrank (A₁ ⧸ maximalIdeal A₁) (tauZSubmodule A₁ g) =
      Module.finrank (A ⧸ maximalIdeal A) (tauZSubmodule A f) := by
  have hdeg₁ : ∀ j, ∃ d ≤ μb, initialForm (maximalIdeal A₁) (g j) ∈
      AssocGraded.homogeneous (maximalIdeal A₁) d := fun j => by
    obtain ⟨d, hd, h⟩ := hdeg j
    refine ⟨d, hd, ?_⟩
    have h1 : M.Φ.symm (initialForm (maximalIdeal A) (f j)) ∈ homogeneousSubmodule (Fin n) K d :=
      (hhom d _).mpr (by rwa [RingEquiv.apply_symm_apply])
    have h2 := (hhom₁ d _).mp (hq j ▸ h1)
    rwa [RingEquiv.apply_symm_apply] at h2
  have hI : (Set.range fun j => M₁.Φ.symm (initialForm (maximalIdeal A₁) (g j))) =
      Set.range fun j => M.Φ.symm (initialForm (maximalIdeal A) (f j)) := by
    congr 1; funext j; exact hq j
  have hMv_f : IsTauSubmoduleMv K n (Ideal.span (Set.range fun j =>
      M.Φ.symm (initialForm (maximalIdeal A) (f j)))) (M.pull (tauZSubmodule A f)) μb :=
    (M.isTauZSubmodule_iff hhom f μb hdeg _).mp (tauZSubmodule_spec A f)
  have hMv_g : IsTauSubmoduleMv K n (Ideal.span (Set.range fun j =>
      M.Φ.symm (initialForm (maximalIdeal A) (f j)))) (M₁.pull (tauZSubmodule A₁ g)) μb := by
    rw [← hI]
    exact (M₁.isTauZSubmodule_iff hhom₁ g μb hdeg₁ _).mp (tauZSubmodule_spec A₁ g)
  have hmin_f : ∀ T, IsTauSubmoduleMv K n (Ideal.span (Set.range fun j =>
      M.Φ.symm (initialForm (maximalIdeal A) (f j)))) T μb →
        M.pull (tauZSubmodule A f) ≤ T := by
    intro T hT
    have h1 : IsTauZSubmodule A f (M.push T) := by
      rw [M.isTauZSubmodule_iff hhom f μb hdeg, M.pull_push]; exact hT
    exact (M.pull_le_iff _ _).mpr (sInf_le h1)
  have hmin_g : ∀ T, IsTauSubmoduleMv K n (Ideal.span (Set.range fun j =>
      M.Φ.symm (initialForm (maximalIdeal A) (f j)))) T μb →
        M₁.pull (tauZSubmodule A₁ g) ≤ T := by
    intro T hT
    have h1 : IsTauZSubmodule A₁ g (M₁.push T) := by
      rw [M₁.isTauZSubmodule_iff hhom₁ g μb hdeg₁, M₁.pull_push, hI]; exact hT
    exact (M₁.pull_le_iff _ _).mpr (sInf_le h1)
  have heq : M₁.pull (tauZSubmodule A₁ g) = M.pull (tauZSubmodule A f) :=
    le_antisymm (hmin_g _ hMv_f) (hmin_f _ hMv_g)
  rw [← M₁.finrank_pull, ← M.finrank_pull, heq]

end SameModelRank

section Lemma19Tau

variable {R : Type u} [CommRing R] [IsRegularLocalRing R]

/-- A regular system of `t`-th `τ`-parameters restricts to a regular system of `a`-th
`τ`-parameters (Definition 7, p. 222: the conditions are those for `b ≤ a`). -/
theorem IsRegularSystemOfTauParameters.restrict (J : Ideal R) {a : ℕ} (ha : 1 ≤ a)
    (hat : a ≤ t R J) (z : Fin (tau R J (t R J)) → maximalIdeal R)
    (hz : IsRegularSystemOfTauParameters R J (t R J) z) :
    IsRegularSystemOfTauParameters R J a (fun i => z ⟨i, lt_of_lt_of_le i.2
      (tau_le_tau_of_le J ha hat le_rfl)⟩) := by
  intro b hb1 hba
  have h1 := hz b hb1 (hba.trans hat)
  have hset : (Set.range fun i : {i : Fin (tau R J a) // (i : ℕ) < tau R J b} =>
      AssocGraded.mk (maximalIdeal R) 1 (z ⟨i.1, lt_of_lt_of_le i.1.2
        (tau_le_tau_of_le J ha hat le_rfl)⟩ : R)
        (by rw [pow_one]; exact (z _).2)) =
      Set.range fun i : {i : Fin (tau R J (t R J)) // (i : ℕ) < tau R J b} =>
        AssocGraded.mk (maximalIdeal R) 1 (z i.1) (by rw [pow_one]; exact (z i.1).2) := by
    ext y
    constructor
    · rintro ⟨⟨i, hi⟩, rfl⟩
      exact ⟨⟨⟨i, lt_of_lt_of_le i.2 (tau_le_tau_of_le J ha hat le_rfl)⟩, hi⟩, rfl⟩
    · rintro ⟨⟨i, hi⟩, rfl⟩
      have hi' : (i : ℕ) < tau R J a := lt_of_lt_of_le hi (tau_le_tau_of_le J hb1 hba hat)
      exact ⟨⟨⟨i, hi'⟩, hi⟩, rfl⟩
  show IsTauSubmodule R J (Submodule.span (R ⧸ maximalIdeal R) _) (mu R J b)
  rw [hset]
  exact h1

end Lemma19Tau

section Lemma19Sup

variable {R : Type u} [CommRing R] [IsRegularLocalRing R]

/-- **Lemma 19 with `T*_a = T_a ⊔ ⟨Z⟩`** (p. 251, as used on p. 257: "by Lemma 19 of §7, we must
have `ψ_{i+j} ∈ k[T*]`"): the initial form of a member `g` normalized by `(f₁, …, f_i)` lies in the
algebra generated by `T_a(J)` and `Z₁, …, Z_r`.  The regular system of `a`-th `τ`-parameters
which Lemma 19 asks for exists (Lemma 11 for `P = M`, restricted from the `t`-th to the `a`-th
system) and generates `T_a` (Corollary to Lemma 10). -/
theorem RegularFrame.initialForm_mem_adjoin_tauSubmodule_sup (F : RegularFrame R) (J : Ideal R)
    (hJ : J ≤ maximalIdeal R) {i : ℕ} (f : Fin i → R) (hfJ : ∀ j, f j ∈ J)
    (hτ : ∀ j : Fin i, tauZ R F.z (fun _ : Fin 1 => f j) = 0) (g : R) (hgJ : g ∈ J)
    (a : ℕ) (ha : 1 ≤ a) (hat : a ≤ t R J) (hmu : (mu R J a : ℕ∞) = nuI R J i.succPNat)
    (h1 : ExtendsToStandardBase J (Fin.snoc f g : Fin (i + 1) → R)) (h2 : F.IsNormalizedBy f g) :
    initialForm (maximalIdeal R) g ∈ Algebra.adjoin (R ⧸ maximalIdeal R)
      ((tauSubmodule R J a ⊔ Submodule.span (R ⧸ maximalIdeal R) (Set.range (frameForm F.z)) :
        Submodule (R ⧸ maximalIdeal R) (AssocGraded (maximalIdeal R))) :
          Set (AssocGraded (maximalIdeal R))) := by
  classical
  obtain ⟨m, G, hG⟩ := exists_isStandardBase J
  have hPprime : (maximalIdeal R).IsPrime := (maximalIdeal.isMaximal R).isPrime
  have hreg : IsRegularLocalRing (R ⧸ maximalIdeal R) := by
    let _ := Ideal.Quotient.field (maximalIdeal R)
    infer_instance
  obtain ⟨z, hz, -⟩ := exists_regularSystemOfTauParameters_mem_prime R J (maximalIdeal R) hJ hreg
    G hG.1 (fun _ => rfl) hG.2.2.2.1.symm
  have hx := IsRegularSystemOfTauParameters.restrict J ha hat z hz
  set x : Fin (tau R J a) → maximalIdeal R := fun i => z ⟨i, lt_of_lt_of_le i.2
    (tau_le_tau_of_le J ha hat le_rfl)⟩ with hxdef
  have h19 := initialForm_mem_adjoin_of_isNormalizedBy F J f hfJ hτ g hgJ a ha hmu h1 h2 x hx
  have hspan : Submodule.span (R ⧸ maximalIdeal R) (Set.range (linearForms R x)) =
      tauSubmodule R J a := by
    refine (tauSubmodule_spec R J a ha hat).2.2 (linearForms R x) (fun i => ?_) ?_
    · exact AssocGraded.mk_mem_homogeneous _ _
    · have h3 := hx a ha le_rfl
      have hset : (Set.range fun i : {i : Fin (tau R J a) // (i : ℕ) < tau R J a} =>
          AssocGraded.mk (maximalIdeal R) 1 (x i.1 : R) (by rw [pow_one]; exact (x i.1).2)) =
          Set.range (linearForms R x) := by
        ext y
        constructor
        · rintro ⟨⟨i, hi⟩, rfl⟩
          exact ⟨i, rfl⟩
        · rintro ⟨i, rfl⟩
          exact ⟨⟨i, i.2⟩, rfl⟩
      rw [hset] at h3
      exact h3
  have hstar : tauParamsSubmoduleStar J a x F.z =
      tauSubmodule R J a ⊔ Submodule.span (R ⧸ maximalIdeal R) (Set.range (frameForm F.z)) := by
    rw [tauParamsSubmoduleStar, Submodule.span_union, hspan]
  rw [← hstar]
  exact h19

end Lemma19Sup

section MuPrefix

variable {R : Type u} [CommRing R] [IsRegularLocalRing R]

/-- If the characters `ν^{(k)}` of `J'` and `J` agree for `k ≤ i + 1`, and `μ^{(a)}(J) =
ν^{(i+1)}(J)`, then `a ≤ t(J')` and `μ^{(a)}(J') = ν^{(i+1)}(J')` (the distinct values below
`ν^{(i+1)}` are attained at indices `≤ i`; used for `J₁` in the proof of Lemma 21, where (10)
gives the agreement). -/
theorem mu_eq_of_nuI_eq_prefix {R' : Type u} [CommRing R'] [IsRegularLocalRing R']
    (J : Ideal R) (J' : Ideal R') {i : ℕ}
    (h : ∀ k : ℕ+, (k : ℕ) ≤ i + 1 → nuI R' J' k = nuI R J k) {a : ℕ} (ha : 1 ≤ a)
    (hat : a ≤ t R J) (hμ : (mu R J a : ℕ∞) = nuI R J i.succPNat) :
    a ≤ t R' J' ∧ (mu R' J' a : ℕ∞) = nuI R' J' i.succPNat := by
  classical
  set μ := mu R J a with hμdef
  have hfin : (muSet R J).Finite := (muSet_finite R J).1
  have hfin' : (muSet R' J').Finite := (muSet_finite R' J').1
  have hi1 : nuI R' J' i.succPNat = nuI R J i.succPNat := h _ (by simp)
  have hmemJ' : μ ∈ muSet R' J' := ⟨i.succPNat, by rw [hi1, hμ]⟩
  have hiff : ∀ k < μ, k ∈ muSet R J ↔ k ∈ muSet R' J' := by
    intro k hk
    have hlt : (k : ℕ∞) < nuI R J i.succPNat := by rw [← hμ]; exact_mod_cast hk
    constructor
    · rintro ⟨l, hl⟩
      have hli : (l : ℕ) ≤ i := by
        by_contra hcon
        have hle : i.succPNat ≤ l := by
          rw [← PNat.coe_le_coe]; simp; omega
        have := nuI_mono J hle
        rw [hl] at this
        exact absurd hlt (not_lt.mpr this)
      exact ⟨l, by rw [h l (by omega), hl]⟩
    · rintro ⟨l, hl⟩
      have hlt' : (k : ℕ∞) < nuI R' J' i.succPNat := by rw [hi1]; exact hlt
      have hli : (l : ℕ) ≤ i := by
        by_contra hcon
        have hle : i.succPNat ≤ l := by
          rw [← PNat.coe_le_coe]; simp; omega
        have := nuI_mono J' hle
        rw [hl] at this
        exact absurd hlt' (not_lt.mpr this)
      exact ⟨l, by rw [← h l (by omega), hl]⟩
  have hcount : Nat.count (· ∈ muSet R J) μ = Nat.count (· ∈ muSet R' J') μ := by
    rw [Nat.count_eq_card_filter_range, Nat.count_eq_card_filter_range]
    congr 1
    ext k
    simp only [Finset.mem_filter, Finset.mem_range]
    exact and_congr_right fun hk => hiff k hk
  have hcard : hfin.toFinset.card = t R J := (Set.ncard_eq_toFinset_card _ hfin).symm
  have hacount : Nat.count (· ∈ muSet R J) μ = a - 1 := by
    rw [hμdef, mu]
    exact Nat.count_nth_of_lt_card_finite hfin (by rw [hcard]; omega)
  have hlt' : Nat.count (· ∈ muSet R' J') μ < hfin'.toFinset.card := Nat.count_lt_card hfin' hmemJ'
  have hcard' : hfin'.toFinset.card = t R' J' := (Set.ncard_eq_toFinset_card _ hfin').symm
  refine ⟨by rw [hcard'] at hlt'; omega, ?_⟩
  have hmu' : mu R' J' a = μ := by
    rw [mu, show a - 1 = Nat.count (· ∈ muSet R' J') μ by rw [← hcount, hacount]]
    exact Nat.nth_count hmemJ'
  rw [hmu', hi1, hμ]

end MuPrefix

end Hironaka
