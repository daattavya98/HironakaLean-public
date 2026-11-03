/-
Copyright (c) 2026 Daattavya Aggarwal, Minhyong Kim, Oisin Kim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daattavya Aggarwal, Minhyong Kim, Oisin Kim
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.Algebra.Module.LocalizedModule.Away
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.CategoryTheory.Monoidal.Tor
public import Mathlib.Data.Sym.Card
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.DirectSum.Basis
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.Coalgebra.IsFrobenius
public import Mathlib.RingTheory.Etale.Weakly
public import Mathlib.RingTheory.Flat.CategoryTheory
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.HopfAlgebra.Basic
public import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.TensorProduct.IsBaseChangeRightExact
public import Mathlib.RingTheory.TotallySplit
public import Architect
public import Hironaka.Compat.Graded
public import Hironaka.Compat.GradedModule
public import Hironaka.Ch0.NormalFlatness
public import Hironaka.Ch0.Multiplicity
public import Hironaka.Compat.RegularGraded
public import Hironaka.Compat.SubschemeStalk
public import Hironaka.Compat.GradedBaseChange
public import Hironaka.Compat.GradedPolynomialPresentation
public import Hironaka.Compat.GrPieceBaseChange
public import Hironaka.Compat.TorOne
public import Hironaka.Compat.TorOneGraded
public import Hironaka.Compat.TorOneLocalization
public import Hironaka.Compat.LocalFlatness
public import Hironaka.Compat.GenericFreeness

/-!
# Ch. II §1: Flatness of the associated graded algebra (pp. 180–189)

> Let A be a noetherian ring and I an ideal in A. Then we associate with I the following graded
> A/I-algebra of finite type: gr_I(A) = ⊕_{m≥0} Iᵐ/Iᵐ⁺¹. The homogeneous part of degree m of
> gr_I(A) is the A/I-module of finite type Iᵐ/Iᵐ⁺¹ and will be denoted by grᵐ_I(A). If M is an
> A-module, then we associate the following graded gr_I(A)-module:
> gr_I(M) = ⊕_{m≥0} IᵐM/Iᵐ⁺¹M. … The homogeneous part of degree m of gr_I(M), that is
> IᵐM/Iᵐ⁺¹M, will be denoted by grᵐ_I(M). … (p. 180)
>
> … If O is the local ring of V at a
> point of W and if P is the ideal in O which defines the subscheme W, then gr_P(O) … is the
> stalk of the sheaf gr_W(V) on W at the point. … Throughout this paper all the
> local rings with which we are concerned will be assumed to be noetherian.  (p. 181)

The homogeneous pieces `grᵐ_I(A) = GrPiece I m` live in `Hironaka/Compat/Graded.lean`; this
file adds `grᵐ_I(M) = GrModPiece I M m`, the canonical maps of p. 181 and the results of §1:
Lemmas 1–4, Proposition 1 with its four corollaries, the Remark of p. 187, Theorem 1
(Krull–Seidenberg–Grothendieck) and its corollary.

Conventions.  "gr_P(O) is flat over O/P" for a noetherian local ring `O` is
`IsNormallyFlatAlongIdeal P` (Definition 1 of Ch. 0 and Lemma 1).  "Tor₁^A(M, N) = 0" is
`IsZero` of Mathlib's categorical `Tor (ModuleCat A) 1`.  Graded algebras and graded modules
are Mathlib's internal gradings `GradedAlgebra 𝒜`, `SetLike.GradedSMul 𝒜 ℳ` with
`DirectSum.Decomposition ℳ`.  Representation choices are flagged as "Formalization note
(encoding)"; every place where a statement or proof departs from the paper is flagged as
"Deviation from the paper (<category>)" in the docstrings and blueprint texts.
-/

@[expose] public section

open TensorProduct AlgebraicGeometry
open scoped DirectSum

namespace Hironaka

universe u

/-! ### Lemmas 1 and 2 and the corollary to Lemma 2 (pp. 181–182) -/

section FlatnessLemmas

/-- Lemma 1, p. 181: "Let `O` be a local ring and `M` an `O`-module of finite type. Then the
following conditions are equivalent to each other: (i) `M` is a free `O`-module, (ii) `M` is a
projective `O`-module, (iii) `M` is a flat `O`-module."  (Local rings are noetherian
throughout the paper, p. 181; Mathlib's proof of (iii) ⇒ (i) does not need it.) -/
@[blueprint "lem:II.1-1"
  (statement := /-- Let $O$ be a (noetherian) local ring and $M$ an $O$-module of finite type.
    Then the following conditions are equivalent to each other: (i) $M$ is a free $O$-module;
    (ii) $M$ is a projective $O$-module; (iii) $M$ is a flat $O$-module. (p.~181.) -/)
  (proof := /-- Cited: ``Corollaire 4.3 to Proposition 4.1'' of the seminar note by
    A.~Grothendieck, \emph{S\'eminaire de G\'eom\'etrie Alg\'ebrique de l'Institut des Hautes
    \'Etudes Scientifiques}, No.~IV (1960) (p.~181). In Mathlib:
    free $\Rightarrow$ projective $\Rightarrow$ flat in general, and finitely generated flat
    modules over a local ring are free (\texttt{Module.free\_of\_flat\_of\_isLocalRing}). -/)
  (latexEnv := "lemma")]
theorem free_projective_flat_tfae (O : Type u) [CommRing O] [IsLocalRing O]
    [IsNoetherianRing O] (M : Type u) [AddCommGroup M] [Module O M] [Module.Finite O M] :
    [Module.Free O M, Module.Projective O M, Module.Flat O M].TFAE := by
  tfae_have 1 → 2 := fun _ => Module.Projective.of_free
  tfae_have 2 → 3 := fun _ => Module.Flat.of_projective
  tfae_have 3 → 1 := fun _ => Module.free_of_flat_of_isLocalRing
  tfae_finish

/-- A finite part of the generating set suffices for an element of `Algebra.adjoin`. -/
private theorem exists_finset_subset_adjoin {A B : Type u} [CommRing A] [CommRing B]
    [Algebra A B] {s : Set B} {x : B} (hx : x ∈ Algebra.adjoin A s) :
    ∃ t : Finset B, (t : Set B) ⊆ s ∧ x ∈ Algebra.adjoin A (t : Set B) := by
  classical
  induction hx using Algebra.adjoin_induction with
  | mem x hx => exact ⟨{x}, by simpa using hx, Algebra.subset_adjoin (by simp)⟩
  | algebraMap r => exact ⟨∅, by simp, Subalgebra.algebraMap_mem _ r⟩
  | add x y _ _ hx hy =>
    obtain ⟨t₁, h₁, hx⟩ := hx
    obtain ⟨t₂, h₂, hy⟩ := hy
    refine ⟨t₁ ∪ t₂, by simpa using ⟨h₁, h₂⟩, add_mem ?_ ?_⟩
    · exact Algebra.adjoin_mono (by simp) hx
    · exact Algebra.adjoin_mono (by simp) hy
  | mul x y _ _ hx hy =>
    obtain ⟨t₁, h₁, hx⟩ := hx
    obtain ⟨t₂, h₂, hy⟩ := hy
    refine ⟨t₁ ∪ t₂, by simpa using ⟨h₁, h₂⟩, mul_mem ?_ ?_⟩
    · exact Algebra.adjoin_mono (by simp) hx
    · exact Algebra.adjoin_mono (by simp) hy

/-- A graded `A`-algebra of finite type generated by homogeneous elements of positive degrees
is generated by finitely many of them. -/
private theorem exists_positive_degree_generators {A B : Type u} [CommRing A] [CommRing B]
    [Algebra A B] (𝒜 : ℕ → Submodule A B) [Algebra.FiniteType A B]
    (hgen : Algebra.adjoin A (⋃ n : ℕ, (𝒜 (n + 1) : Set B)) = ⊤) :
    ∃ (κ : Type u) (_ : Fintype κ) (t : κ → B) (e : κ → ℕ), (∀ j, 0 < e j) ∧
      (∀ j, t j ∈ 𝒜 (e j)) ∧ Algebra.adjoin A (Set.range t) = ⊤ := by
  classical
  obtain ⟨s, hs⟩ := Algebra.FiniteType.out (R := A) (A := B)
  have h : ∀ x : s, ∃ T : Finset B, (T : Set B) ⊆ ⋃ n : ℕ, (𝒜 (n + 1) : Set B) ∧
      (x : B) ∈ Algebra.adjoin A (T : Set B) := fun x =>
    exists_finset_subset_adjoin (hgen ▸ Algebra.mem_top)
  choose T hT hxT using h
  let U : Finset B := Finset.univ.biUnion T
  have hU : ∀ y : U, ∃ n : ℕ, (y : B) ∈ 𝒜 (n + 1) := by
    rintro ⟨y, hy⟩
    obtain ⟨x, -, hx⟩ := Finset.mem_biUnion.mp hy
    simpa using hT x hx
  choose e he using hU
  refine ⟨U, inferInstance, Subtype.val, fun j => e j + 1, fun j => Nat.succ_pos _, he, ?_⟩
  rw [eq_top_iff, ← hs, Algebra.adjoin_le_iff]
  intro x hx
  refine Algebra.adjoin_mono ?_ (hxT ⟨x, hx⟩)
  intro y hy
  exact ⟨⟨y, Finset.mem_biUnion.mpr ⟨⟨x, hx⟩, Finset.mem_univ _, hy⟩⟩, rfl⟩

/-- Every element of `A[t₁, …, tₖ]` is of the form `a + Σ cⱼ tⱼ`. -/
private theorem exists_eq_algebraMap_add_sum {A B : Type u} [CommRing A] [CommRing B]
    [Algebra A B] {κ : Type*} [Fintype κ] (t : κ → B) {x : B}
    (hx : x ∈ Algebra.adjoin A (Set.range t)) :
    ∃ (a : A) (c : κ → B), x = algebraMap A B a + ∑ j, c j * t j := by
  classical
  induction hx using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨j, rfl⟩ := hx
    exact ⟨0, fun j' => if j' = j then 1 else 0, by simp⟩
  | algebraMap r => exact ⟨r, 0, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨a₁, c₁, rfl⟩ := hx
    obtain ⟨a₂, c₂, rfl⟩ := hy
    refine ⟨a₁ + a₂, c₁ + c₂, ?_⟩
    simp only [map_add, Pi.add_apply, add_mul, Finset.sum_add_distrib]
    ring
  | mul x y _ _ hx hy =>
    obtain ⟨a₁, c₁, rfl⟩ := hx
    obtain ⟨a₂, c₂, rfl⟩ := hy
    refine ⟨a₁ * a₂, fun j => algebraMap A B a₁ * c₂ j +
      c₁ j * (algebraMap A B a₂ + ∑ j, c₂ j * t j), ?_⟩
    simp only [map_mul, add_mul, Finset.sum_add_distrib, Finset.sum_mul]
    have : ∀ j, c₁ j * t j * (algebraMap A B a₂ + ∑ i, c₂ i * t i) =
        c₁ j * (algebraMap A B a₂ + ∑ i, c₂ i * t i) * t j := fun j => by ring
    simp only [mul_add, Finset.mul_sum] at this ⊢
    rw [Finset.sum_congr rfl (fun j _ => this j)]
    simp only [mul_assoc]
    ring_nf

/-- The homogeneous parts of a graded algebra generated over a noetherian ring `A` by
finitely many homogeneous elements of positive degrees are `A`-modules of finite type. -/
private theorem fg_grade_of_adjoin_eq_top {A B : Type u} [CommRing A] [IsNoetherianRing A] [CommRing B]
    [Algebra A B] (𝒜 : ℕ → Submodule A B) [GradedAlgebra 𝒜] {κ : Type*} [Fintype κ]
    (t : κ → B) (e : κ → ℕ) (he : ∀ j, 0 < e j) (ht : ∀ j, t j ∈ 𝒜 (e j))
    (hgen : Algebra.adjoin A (Set.range t) = ⊤) (k : ℕ) : (𝒜 k).FG := by
  classical
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  refine Submodule.FG.of_le (T := Submodule.span A {1} ⊔
    ⨆ j, ⨆ (_ : e j ≤ k), (𝒜 (k - e j)).map (LinearMap.mulRight A (t j))) ?_ ?_
  · refine (Submodule.fg_span_singleton 1).sup (Submodule.fg_iSup _ fun j => ?_)
    refine Submodule.fg_iSup _ fun h => (ih _ ?_).map _
    have := he j
    omega
  · intro x hx
    obtain ⟨a, c, hxc⟩ := exists_eq_algebraMap_add_sum (A := A) t
      (hgen ▸ Algebra.mem_top : x ∈ Algebra.adjoin A (Set.range t))
    have hx' : x = (DirectSum.decompose 𝒜 x k : B) :=
      (DirectSum.decompose_of_mem_same 𝒜 hx).symm
    rw [hx', hxc, DirectSum.decompose_add, DirectSum.add_apply, Submodule.coe_add,
      DirectSum.decompose_sum, DFinsupp.finsetSum_apply, Submodule.coe_sum]
    refine Submodule.add_mem_sup ?_ (Submodule.sum_mem _ fun j _ => ?_)
    · have h0 : algebraMap A B a ∈ 𝒜 0 := SetLike.algebraMap_mem_graded 𝒜 a
      by_cases hk : k = 0
      · subst hk
        rw [DirectSum.decompose_of_mem_same 𝒜 h0, Algebra.algebraMap_eq_smul_one]
        exact Submodule.smul_mem _ a (Submodule.mem_span_singleton_self 1)
      · rw [DirectSum.decompose_of_mem_ne 𝒜 h0 (Ne.symm hk)]
        exact zero_mem _
    · by_cases hjk : e j ≤ k
      · rw [DirectSum.coe_decompose_mul_of_right_mem_of_le 𝒜 (ht j) hjk]
        refine Submodule.mem_iSup_of_mem j (Submodule.mem_iSup_of_mem hjk ?_)
        exact ⟨_, SetLike.coe_mem _, rfl⟩
      · rw [DirectSum.coe_decompose_mul_of_right_mem_of_not_le 𝒜 (ht j) hjk]
        exact zero_mem _

/-- The degree-`n` part of `b • m`, for `m` homogeneous of degree `d`, is `b_{n-d} • m`. -/
private theorem decompose_smul_mem_map_toSpanSingleton {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    (𝒜 : ℕ → Submodule A B) [GradedAlgebra 𝒜] {M : Type u} [AddCommGroup M] [Module B M]
    [Module A M] [IsScalarTower A B M] (ℳ : ℕ → Submodule A M) [SetLike.GradedSMul 𝒜 ℳ]
    [DirectSum.Decomposition ℳ] (b : B) {m : M} {d : ℕ} (hm : m ∈ ℳ d) (n : ℕ) :
    (DirectSum.decompose ℳ (b • m) n : M) ∈
      (𝒜 (n - d)).map ((LinearMap.toSpanSingleton B M m).restrictScalars A) := by
  classical
  rw [← DirectSum.sum_support_decompose 𝒜 b, Finset.sum_smul, DirectSum.decompose_sum,
    DFinsupp.finsetSum_apply, Submodule.coe_sum]
  refine Submodule.sum_mem _ fun i _ => ?_
  have hmem : ((DirectSum.decompose 𝒜 b i : B)) • m ∈ ℳ (i + d) :=
    SetLike.GradedSMul.smul_mem (A := 𝒜) (SetLike.coe_mem (DirectSum.decompose 𝒜 b i)) hm
  by_cases hi : i + d = n
  · rw [DirectSum.decompose_of_mem_same ℳ (hi ▸ hmem)]
    have : i = n - d := by omega
    subst this
    exact ⟨_, SetLike.coe_mem _, rfl⟩
  · rw [DirectSum.decompose_of_mem_ne ℳ hmem hi]
    exact zero_mem _

/-- A graded module of finite type is generated by finitely many homogeneous elements. -/
private theorem exists_homogeneous_generators {B : Type u} [CommRing B] {A : Type u}
    [CommRing A] {M : Type u} [AddCommGroup M] [Module B M] [Module A M]
    (ℳ : ℕ → Submodule A M) [DirectSum.Decomposition ℳ] [Module.Finite B M] :
    ∃ (ι : Type u) (_ : Fintype ι) (g : ι → M) (d : ι → ℕ), (∀ i, g i ∈ ℳ (d i)) ∧
      Submodule.span B (Set.range g) = ⊤ := by
  classical
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := B) (M := M)
  let ι := Σ x : s, (DirectSum.decompose ℳ (x : M)).support
  refine ⟨ULift ι, inferInstance, fun i => (DirectSum.decompose ℳ (i.down.1 : M) i.down.2 : M),
    fun i => i.down.2, fun i => SetLike.coe_mem _, ?_⟩
  rw [eq_top_iff, ← hs, Submodule.span_le]
  intro x hx
  rw [← DirectSum.sum_support_decompose ℳ x]
  exact Submodule.sum_mem _ fun i hi => Submodule.subset_span ⟨ULift.up ⟨⟨x, hx⟩, ⟨i, hi⟩⟩, rfl⟩

/-- Proof of the corollary to Lemma 2, first step: "all homogeneous parts `Mₙ` of `M` are
`A`-modules of finite type". -/
private theorem finite_piece_of_adjoin_eq_top {A : Type u} [CommRing A] [IsNoetherianRing A]
    (B : Type u) [CommRing B] [Algebra A B] (𝒜 : ℕ → Submodule A B) [GradedAlgebra 𝒜]
    [Algebra.FiniteType A B] (hgen : Algebra.adjoin A (⋃ n : ℕ, (𝒜 (n + 1) : Set B)) = ⊤)
    (M : Type u) [AddCommGroup M] [Module B M] [Module A M] [IsScalarTower A B M]
    [Module.Finite B M] (ℳ : ℕ → Submodule A M) [SetLike.GradedSMul 𝒜 ℳ]
    [DirectSum.Decomposition ℳ] (n : ℕ) : Module.Finite A (ℳ n) := by
  classical
  obtain ⟨κ, _, t, e, he, ht, htgen⟩ := exists_positive_degree_generators 𝒜 hgen
  have h𝒜 := fg_grade_of_adjoin_eq_top 𝒜 t e he ht htgen
  obtain ⟨ι, _, g, d, hg, hspan⟩ := exists_homogeneous_generators (B := B) ℳ
  refine Module.Finite.iff_fg.mpr (Submodule.FG.of_le (T := ⨆ i, (𝒜 (n - d i)).map
    ((LinearMap.toSpanSingleton B M (g i)).restrictScalars A)) ?_ ?_)
  · exact Submodule.fg_iSup _ fun i => (h𝒜 _).map _
  · intro x hx
    have hx' : x ∈ Submodule.span B (Set.range g) := hspan ▸ Submodule.mem_top
    obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun B).mp hx'
    rw [← DirectSum.decompose_of_mem_same ℳ hx, DirectSum.decompose_sum,
      DFinsupp.finsetSum_apply, Submodule.coe_sum]
    exact Submodule.sum_mem _ fun i _ => Submodule.mem_iSup_of_mem i
      (decompose_smul_mem_map_toSpanSingleton 𝒜 ℳ (c i) (hg i) n)

/-- The multiplication map `M ⊗_A Iᵏ → M`, `x ⊗ a ↦ a • x`. -/
private noncomputable abbrev tensorPowMul {A : Type u} [CommRing A] (I : Ideal A)
    (M : Type u) [AddCommGroup M] [Module A M] (k : ℕ) : M ⊗[A] ↥(I ^ k) →ₗ[A] M :=
  (TensorProduct.rid A M).toLinearMap ∘ₗ LinearMap.lTensor M (I ^ k).subtype

private theorem tensorPowMul_tmul {A : Type u} [CommRing A] (I : Ideal A) (M : Type u)
    [AddCommGroup M] [Module A M] (k : ℕ) (x : M) (a : ↥(I ^ k)) :
    tensorPowMul I M k (x ⊗ₜ a) = (a : A) • x := by
  simp [tensorPowMul]

private theorem tensorPowMul_mem {A : Type u} [CommRing A] (I : Ideal A) (M : Type u)
    [AddCommGroup M] [Module A M] (k : ℕ) (s : M ⊗[A] ↥(I ^ k)) :
    tensorPowMul I M k s ∈ I ^ k • (⊤ : Submodule A M) := by
  induction s with
  | tmul x a =>
    rw [tensorPowMul_tmul]
    exact Submodule.smul_mem_smul a.2 Submodule.mem_top
  | add s₁ s₂ h₁ h₂ => rw [map_add]; exact add_mem h₁ h₂

private theorem exists_tensorPowMul_eq {A : Type u} [CommRing A] (I : Ideal A) (M : Type u)
    [AddCommGroup M] [Module A M] (k : ℕ) {y : M} (hy : y ∈ I ^ k • (⊤ : Submodule A M)) :
    ∃ s, tensorPowMul I M k s = y := by
  refine Submodule.smul_induction_on hy (fun a ha x _ => ?_) (fun x y hx hy => ?_)
  · exact ⟨x ⊗ₜ ⟨a, ha⟩, tensorPowMul_tmul I M k x ⟨a, ha⟩⟩
  · obtain ⟨s₁, rfl⟩ := hx
    obtain ⟨s₂, rfl⟩ := hy
    exact ⟨s₁ + s₂, map_add _ _ _⟩

/-- `φ(x ⊗ [a]) = [a • x]`, for `s ∈ M ⊗_A Iᵐ` mapped to `M ⊗_A Iᵐ/Iᵐ⁺¹`. -/
private theorem grModMap_lTensor_mkQ {A : Type u} [CommRing A] (I : Ideal A) (M : Type u)
    [AddCommGroup M] [Module A M] (m : ℕ) (s : M ⊗[A] ↥(I ^ m)) :
    grModMap I M m (LinearMap.lTensor M (Submodule.mkQ _) s) =
      Submodule.Quotient.mk ⟨tensorPowMul I M m s, tensorPowMul_mem I M m s⟩ := by
  induction s with
  | tmul x a =>
    rw [LinearMap.lTensor_tmul, Submodule.mkQ_apply, grModMap_tmul]
    congr 2
  | add s₁ s₂ h₁ h₂ =>
    rw [map_add, map_add, h₁, h₂, ← Submodule.Quotient.mk_add]
    congr 1
    exact Subtype.ext (map_add _ _ _).symm

/-- The canonical homomorphism `M ⊗_A Iᵐ/Iᵐ⁺¹ → IᵐM/Iᵐ⁺¹M` is always surjective. -/
theorem grModMap_surjective {A : Type u} [CommRing A] (I : Ideal A) (M : Type u)
    [AddCommGroup M] [Module A M] (m : ℕ) : Function.Surjective (grModMap I M m) := by
  intro z
  induction z using Submodule.Quotient.induction_on with
  | H y =>
    obtain ⟨s, hs⟩ := exists_tensorPowMul_eq I M m y.2
    refine ⟨LinearMap.lTensor M (Submodule.mkQ _) s, ?_⟩
    rw [grModMap_lTensor_mkQ]
    congr 1
    exact Subtype.ext hs

/-- For a flat `A`-module `M`, `M ⊗_A Iᵐ/Iᵐ⁺¹ → IᵐM/Iᵐ⁺¹M` is injective. -/
theorem grModMap_injective_of_flat {A : Type u} [CommRing A] (I : Ideal A)
    (M : Type u) [AddCommGroup M] [Module A M] [Module.Flat A M] (m : ℕ) :
    Function.Injective (grModMap I M m) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro t ht
  obtain ⟨s, rfl⟩ := LinearMap.lTensor_surjective M (Submodule.mkQ_surjective
    (Submodule.comap (I ^ m).subtype (I ^ (m + 1)))) t
  rw [grModMap_lTensor_mkQ, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap,
    Submodule.subtype_apply] at ht
  obtain ⟨s', hs'⟩ := exists_tensorPowMul_eq I M (m + 1) ht
  have hle : I ^ (m + 1) ≤ I ^ m := Ideal.pow_le_pow_right (Nat.le_succ m)
  let incl : ↥(I ^ (m + 1)) →ₗ[A] ↥(I ^ m) := Submodule.inclusion hle
  have hinj : Function.Injective (tensorPowMul I M m) :=
    (TensorProduct.rid A M).injective.comp
      (Module.Flat.lTensor_preserves_injective_linearMap _ Subtype.val_injective)
  have hs : s = LinearMap.lTensor M incl s' := by
    apply hinj
    have e : tensorPowMul I M m s = tensorPowMul I M (m + 1) s' := hs'.symm
    rw [e]
    simp only [tensorPowMul, LinearMap.comp_apply, ← LinearMap.lTensor_comp_apply]
    rfl
  rw [hs, ← LinearMap.lTensor_comp_apply]
  have h0 : (Submodule.mkQ (Submodule.comap (I ^ m).subtype (I ^ (m + 1)))) ∘ₗ incl = 0 := by
    ext a
    simp only [LinearMap.comp_apply, Submodule.mkQ_apply, LinearMap.zero_apply,
      Submodule.Quotient.mk_eq_zero, Submodule.mem_comap, Submodule.subtype_apply]
    exact a.2
  rw [h0, LinearMap.lTensor_zero, LinearMap.zero_apply]

/-- `Tor_{n+1}^A(M, N) = 0` for a flat `A`-module `M`: `Tor(M, -)` is the left derived functor
of the exact functor `M ⊗_A -`. -/
private theorem isZero_tor_of_flat {A : Type u} [CommRing A] (M N : ModuleCat.{u} A)
    [Module.Flat A M] (n : ℕ) :
    CategoryTheory.Limits.IsZero
      (((CategoryTheory.Tor (ModuleCat.{u} A) (n + 1)).obj M).obj N) := by
  let P := CategoryTheory.projectiveResolution N
  refine CategoryTheory.Limits.IsZero.of_iso ?_ (P.isoLeftDerivedObj
    ((CategoryTheory.MonoidalCategory.tensoringLeft (ModuleCat.{u} A)).obj M) (n + 1))
  erw [← HomologicalComplex.exactAt_iff_isZero_homology]
  have h := P.complex_exactAt_succ n
  rw [HomologicalComplex.exactAt_iff] at h ⊢
  exact h.map (CategoryTheory.MonoidalCategory.tensorLeft M)

/-- Lemma 2, p. 182: "Let `A → B` be a homomorphism of noetherian rings, `I` an ideal in `A`
such that `IB` is contained in the Jacobson radical of `B` (i.e., in the intersection of all
the maximal ideals of `B`), and `M` a `B`-module of finite type. Then the following conditions
are equivalent to each other: (i) `M` is a flat `A`-module, (ii) `M ⊗_A A/I` is a flat
`A/I`-module and `Tor₁^A(M, A/I) = 0`, (iii) `M ⊗_A A/I` is a flat `A/I`-module, and the
canonical homomorphism `φ: gr⁰_I(M) ⊗_{A/I} gr_I(A) → gr_I(M)` is an isomorphism."

Encoding: the homomorphism `A → B` is `[Algebra A B]`; `M ⊗_A A/I` is written
`(A ⧸ I) ⊗[A] M` (Mathlib puts the `A/I`-module structure on the left factor);
`Tor₁^A(M, A/I)` is the categorical `Tor (ModuleCat A) 1`; "`φ` is an isomorphism" is
`∀ m, Function.Bijective (grModMap I M m)` (see `grModMap`).

The paper cites this from Grothendieck; Mathlib has neither the local criterion of flatness nor
a long exact sequence for `Tor`, so it is proved here from `Hironaka/Compat/TorOne.lean` and
`Hironaka/Compat/LocalFlatness.lean`.  (It is stated after the auxiliary lemmas on `grModMap`
and `Tor` that its proof uses.) -/
@[blueprint "lem:II.1-2"
  (statement := /-- Let $A\to B$ be a homomorphism of noetherian rings, $I$ an ideal in $A$
    such that $IB$ is contained in the Jacobson radical of $B$ (i.e., in the intersection of
    all the maximal ideals of $B$), and $M$ a $B$-module of finite type. Then the following
    conditions are equivalent to each other: (i) $M$ is a flat $A$-module; (ii)
    $M\otimes_AA/I$ is a flat $A/I$-module and $\operatorname{Tor}_1^A(M,A/I)=0$; (iii)
    $M\otimes_AA/I$ is a flat $A/I$-module, and the canonical homomorphism
    $\varphi\colon\operatorname{gr}^0_I(M)\otimes_{A/I}\operatorname{gr}_I(A)\to
    \operatorname{gr}_I(M)$ of \cref{def:II.1-canonical-phi} is an isomorphism. (p.~182.) -/)
  (proof := /-- Cited: ``Th\'eor\`eme 5.6 of the above cited seminar note by Grothendieck''
    (S\'eminaire de G\'eom\'etrie Alg\'ebrique de l'IHES, No.~IV (1960); p.~182); the paper
    gives no proof. (Formalization note: proved in Lean, by the following self-contained
    argument.) (i)$\Rightarrow$(ii): flatness is preserved by base change, and
    $\operatorname{Tor}_1^A(M,-)$ vanishes for flat $M$. (i)$\Rightarrow$(iii): for flat $M$,
    $M\otimes_AI^{m+1}\to M\otimes_AI^m$ is identified with $I^{m+1}M\subseteq I^mM$, so
    $\varphi$ is injective; it is always surjective. (iii)$\Rightarrow$(ii): by
    \cref{compat:gr-injective-mul-injective}, $M\otimes_AI\to M$ is injective, which is
    $\operatorname{Tor}_1^A(M,A/I)=0$ by \cref{compat:tor-one-quotient}.
    (ii)$\Rightarrow$(i): \cref{compat:tor-one-quotient} and
    \cref{compat:local-flatness-criterion}. -/)
  (latexEnv := "lemma")]
theorem flat_tfae_of_map_le_jacobson (A : Type u) [CommRing A] [IsNoetherianRing A]
    (B : Type u) [CommRing B] [IsNoetherianRing B] [Algebra A B] (I : Ideal A)
    (hI : I.map (algebraMap A B) ≤ Ring.jacobson B)
    (M : Type u) [AddCommGroup M] [Module B M] [Module A M] [IsScalarTower A B M]
    [Module.Finite B M] :
    [Module.Flat A M,
      Module.Flat (A ⧸ I) ((A ⧸ I) ⊗[A] M) ∧
        CategoryTheory.Limits.IsZero (((CategoryTheory.Tor (ModuleCat.{u} A) 1).obj
          (ModuleCat.of A M)).obj (ModuleCat.of A (A ⧸ I))),
      Module.Flat (A ⧸ I) ((A ⧸ I) ⊗[A] M) ∧
        ∀ m : ℕ, Function.Bijective (grModMap I M m)].TFAE := by
  classical
  -- (iii) ⇒ "`M ⊗_A I → M` is injective": the injectivity of `φ` in each degree, read through
  -- `M ⊗_A Iᵐ ↠ M ⊗_A Iᵐ/Iᵐ⁺¹`, is the hypothesis of `mul_injective_of_forall_gr`
  have hμ : (∀ m : ℕ, Function.Injective (grModMap I M m)) →
      Function.Injective (fun x : M ⊗[A] I =>
        TensorProduct.rid A M (LinearMap.lTensor M I.subtype x)) := fun h =>
    mul_injective_of_forall_gr A B I hI M fun n s hs => by
      refine h n ?_
      rw [grModMap_lTensor_mkQ, map_zero, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap,
        Submodule.subtype_apply]
      exact hs
  tfae_have 1 → 2 := fun _ => ⟨inferInstance, isZero_tor_of_flat _ _ 0⟩
  tfae_have 1 → 3 := fun _ => ⟨inferInstance, fun m =>
    ⟨grModMap_injective_of_flat I M m, grModMap_surjective I M m⟩⟩
  tfae_have 3 → 2 := fun ⟨h₁, h₂⟩ =>
    ⟨h₁, (isZero_torOne_quotient_iff I M).mpr (hμ fun m => (h₂ m).1)⟩
  tfae_have 2 → 1 := fun ⟨h₁, h₂⟩ =>
    flat_of_flat_quotient_of_mul_injective A B I hI M h₁ ((isZero_torOne_quotient_iff I M).mp h₂)
  tfae_finish

/-! #### Graded pieces: each condition for `M` against the same condition for all `Mₙ` (p. 182)

In the proof of the corollary to Lemma 2 the paper argues: "In fact, first of all by the
definition of flatness, the `A`-module `M` is flat if and only if all the direct summands `Mₙ` of
`M` are flat `A`-modules.  Secondly, the functor `Tor₁^A` commutes with direct summation of
modules, and finally `gr⁰_I(M)` (resp. `gr_I(M)`) is a direct sum of the modules `gr⁰_I(Mₙ)`
(resp. `gr_I(Mₙ)`) for all integers `n`, so that the homomorphism `φ` is the direct sum of the
canonical homomorphisms `φₙ: gr⁰_I(Mₙ) ⊗_{A/I} gr_I(A) → gr_I(Mₙ)` for all integers `n`."
Each of the three sentences is a lemma below, for a decomposition `M = ⊕ Mₙ` into `A`-submodules
`ℳ n`. -/

section GradedPieces

variable {A : Type u} [CommRing A] {M : Type u} [AddCommGroup M] [Module A M]
  (ℳ : ℕ → Submodule A M) [DirectSum.Decomposition ℳ]

/-- The projection `M → Mₙ` onto the `n`th direct summand of `M = ⊕ Mₙ`. -/
private noncomputable def projPiece (n : ℕ) : M →ₗ[A] ℳ n :=
  DirectSum.component A ℕ (fun i => ℳ i) n ∘ₗ (DirectSum.decomposeLinearEquiv ℳ).toLinearMap

private theorem projPiece_apply (n : ℕ) (x : M) : projPiece ℳ n x = DirectSum.decompose ℳ x n :=
  rfl

private theorem projPiece_comp_subtype_self (n : ℕ) :
    projPiece ℳ n ∘ₗ (ℳ n).subtype = LinearMap.id := by
  ext x
  simp only [projPiece, LinearMap.comp_apply, LinearEquiv.coe_coe,
    DirectSum.decomposeLinearEquiv_apply, Submodule.subtype_apply, DirectSum.decompose_coe,
    LinearMap.id_apply]
  exact congrArg Subtype.val (DirectSum.component.lof_self (R := A) (M := fun i => ℳ i) n x)

private theorem projPiece_comp_subtype_ne {n k : ℕ} (h : n ≠ k) :
    projPiece ℳ k ∘ₗ (ℳ n).subtype = 0 := by
  ext x
  simp only [LinearMap.comp_apply, Submodule.subtype_apply, projPiece_apply,
    LinearMap.zero_apply]
  rw [ZeroMemClass.coe_zero]
  exact DirectSum.decompose_of_mem_ne ℳ x.2 h

/-- Corollary to Lemma 2, p. 182, first printed sentence: "first of all by the definition of
flatness, the `A`-module `M` is flat if and only if all the direct summands `Mₙ` of `M` are flat
`A`-modules". -/
private theorem flat_iff_forall_flat_graded :
    Module.Flat A M ↔ ∀ n, Module.Flat A (ℳ n) := by
  classical
  rw [← Module.Flat.directSum_iff (R := A) (M := fun n => ℳ n)]
  exact ⟨fun _ => Module.Flat.of_linearEquiv (DirectSum.decomposeLinearEquiv ℳ).symm,
    fun _ => Module.Flat.of_linearEquiv (DirectSum.decomposeLinearEquiv ℳ)⟩

/-- Tensor products commute with the direct sum `M = ⊕ Mₙ`: `⊕ₙ (Mₙ ⊗_A Q) ≅ M ⊗_A Q`. -/
private noncomputable def tensorDecompEquiv (Q : Type u) [AddCommGroup Q] [Module A Q] :
    (⨁ n, ℳ n ⊗[A] Q) ≃ₗ[A] M ⊗[A] Q :=
  (TensorProduct.directSumLeft A A (fun n => ℳ n) Q).symm ≪≫ₗ
    LinearEquiv.rTensor Q (DirectSum.decomposeLinearEquiv ℳ).symm

private theorem tensorDecompEquiv_lof (Q : Type u) [AddCommGroup Q] [Module A Q] (n : ℕ)
    (z : ℳ n ⊗[A] Q) :
    tensorDecompEquiv ℳ Q (DirectSum.lof A ℕ (fun n => ℳ n ⊗[A] Q) n z) =
      LinearMap.rTensor Q (ℳ n).subtype z := by
  classical
  induction z with
  | tmul x q =>
    simp [tensorDecompEquiv]
  | add z₁ z₂ h₁ h₂ => simp only [map_add, h₁, h₂]

/-- The base change `(A/I) ⊗_A M` is the direct sum of the `(A/I) ⊗_A Mₙ`; so it is flat over
`A/I` if and only if all the `(A/I) ⊗_A Mₙ` are (second condition of (ii) and (iii) of Lemma 2,
the sentence of p. 182 quoted above applied to `A/I`). -/
private theorem flat_baseChange_iff_forall_graded (I : Ideal A) :
    Module.Flat (A ⧸ I) ((A ⧸ I) ⊗[A] M) ↔ ∀ n, Module.Flat (A ⧸ I) ((A ⧸ I) ⊗[A] ℳ n) := by
  classical
  let e : (A ⧸ I) ⊗[A] M ≃ₗ[A ⧸ I] ⨁ n, (A ⧸ I) ⊗[A] ℳ n :=
    TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl (A ⧸ I) (A ⧸ I))
        (DirectSum.decomposeLinearEquiv ℳ) ≪≫ₗ
      TensorProduct.directSumRight A (A ⧸ I) (A ⧸ I) (fun n => ℳ n)
  rw [← Module.Flat.directSum_iff (R := A ⧸ I) (M := fun n => (A ⧸ I) ⊗[A] ℳ n)]
  exact ⟨fun _ => Module.Flat.of_linearEquiv e.symm, fun _ => Module.Flat.of_linearEquiv e⟩

/-- The multiplication map `N ⊗_A I → N`, `x ⊗ a ↦ a • x`, of `compat:tor-one-quotient`. -/
private noncomputable abbrev mulIdealMap (I : Ideal A) (N : Type u) [AddCommGroup N]
    [Module A N] : N ⊗[A] I →ₗ[A] N :=
  (TensorProduct.rid A N).toLinearMap ∘ₗ LinearMap.lTensor N I.subtype

/-- If `F ∘ a = b ∘ F'` for linear equivalences `a`, `b`, then `F` is injective (bijective) if
and only if `F'` is. -/
private theorem injective_bijective_iff_of_comp_eq {X Y X' Y' : Type*} [AddCommMonoid X]
    [AddCommMonoid Y] [AddCommMonoid X'] [AddCommMonoid Y'] [Module A X] [Module A Y]
    [Module A X'] [Module A Y'] (F : X →ₗ[A] Y) (F' : X' →ₗ[A] Y') (a : X' ≃ₗ[A] X)
    (b : Y' ≃ₗ[A] Y) (h : ∀ x', F (a x') = b (F' x')) :
    (Function.Injective F ↔ Function.Injective F') ∧
      (Function.Bijective F ↔ Function.Bijective F') := by
  have hF : (F : X → Y) ∘ a = b ∘ F' := funext h
  constructor
  · rw [← EquivLike.injective_comp a (F : X → Y), hF, EquivLike.comp_injective _ b]
  · rw [← EquivLike.bijective_comp a (F : X → Y), hF, EquivLike.comp_bijective _ b]

/-- The multiplication map `M ⊗_A I → M` is the direct sum of the maps `Mₙ ⊗_A I → Mₙ`. -/
private theorem mulIdealMap_tensorDecompEquiv (I : Ideal A) (w : ⨁ n, ℳ n ⊗[A] ↥I) :
    mulIdealMap I M (tensorDecompEquiv ℳ I w) =
      (DirectSum.decomposeLinearEquiv ℳ).symm
        (DirectSum.lmap (fun n => mulIdealMap I (ℳ n)) w) := by
  classical
  have h : mulIdealMap I M ∘ₗ (tensorDecompEquiv ℳ I).toLinearMap =
      (DirectSum.decomposeLinearEquiv ℳ).symm.toLinearMap ∘ₗ
        DirectSum.lmap (fun n => mulIdealMap I (ℳ n)) := by
    refine DirectSum.linearMap_ext A fun n => TensorProduct.ext' fun x a => ?_
    simp [tensorDecompEquiv_lof]
  exact LinearMap.congr_fun h w

/-- Corollary to Lemma 2, p. 182, second printed sentence: "the functor `Tor₁^A` commutes with
direct summation of modules".  It is only used for the vanishing of `Tor₁^A(-, A/I)` in the
condition (ii) of Lemma 2.  By `compat:tor-one-quotient`, `Tor₁^A(N, A/I) = 0` if and only if
`N ⊗_A I → N` is injective; for `N = M = ⊕ Mₙ` the multiplication map `M ⊗_A I → M` is the direct
sum of the maps `Mₙ ⊗_A I → Mₙ` (`mulIdealMap_tensorDecompEquiv`), which is injective if and
only if each one is. -/
private theorem isZero_tor_iff_forall_graded (I : Ideal A) :
    CategoryTheory.Limits.IsZero (((CategoryTheory.Tor (ModuleCat.{u} A) 1).obj
        (ModuleCat.of A M)).obj (ModuleCat.of A (A ⧸ I))) ↔
      ∀ n, CategoryTheory.Limits.IsZero (((CategoryTheory.Tor (ModuleCat.{u} A) 1).obj
        (ModuleCat.of A (ℳ n))).obj (ModuleCat.of A (A ⧸ I))) := by
  classical
  simp only [isZero_torOne_quotient_iff]
  change Function.Injective (mulIdealMap I M) ↔ ∀ n, Function.Injective (mulIdealMap I (ℳ n))
  rw [(injective_bijective_iff_of_comp_eq (mulIdealMap I M)
    (DirectSum.lmap fun n => mulIdealMap I (ℳ n)) (tensorDecompEquiv ℳ I)
    (DirectSum.decomposeLinearEquiv ℳ).symm (mulIdealMap_tensorDecompEquiv ℳ I)).1,
    DirectSum.lmap_injective]

/-- The map `grᵐ_I(N) → grᵐ_I(P)` induced by an `A`-linear map `f : N → P` (`f` maps `IᵐN` into
`IᵐP` and `Iᵐ⁺¹N` into `Iᵐ⁺¹P`). -/
private noncomputable def grModPieceMap (I : Ideal A) (m : ℕ) {N P : Type u} [AddCommGroup N]
    [Module A N] [AddCommGroup P] [Module A P] (f : N →ₗ[A] P) :
    GrModPiece I N m →ₗ[A] GrModPiece I P m :=
  Submodule.mapQ _ _ (f.restrict fun _ hx => Submodule.smul_top_le_comap_smul_top (I ^ m) f hx)
    (fun _ hx => Submodule.smul_top_le_comap_smul_top (I ^ (m + 1)) f hx)

private theorem grModPieceMap_mk (I : Ideal A) (m : ℕ) {N P : Type u} [AddCommGroup N]
    [Module A N] [AddCommGroup P] [Module A P] (f : N →ₗ[A] P)
    (x : ↥(I ^ m • (⊤ : Submodule A N))) :
    grModPieceMap I m f (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk ⟨f x, Submodule.smul_top_le_comap_smul_top (I ^ m) f x.2⟩ :=
  rfl

private theorem grModPieceMap_comp (I : Ideal A) (m : ℕ) {N P Q : Type u} [AddCommGroup N]
    [Module A N] [AddCommGroup P] [Module A P] [AddCommGroup Q] [Module A Q] (f : N →ₗ[A] P)
    (g : P →ₗ[A] Q) :
    grModPieceMap I m (g ∘ₗ f) = grModPieceMap I m g ∘ₗ grModPieceMap I m f := by
  refine LinearMap.ext fun z => ?_
  induction z using Submodule.Quotient.induction_on with
  | H x => rfl

private theorem grModPieceMap_id (I : Ideal A) (m : ℕ) {N : Type u} [AddCommGroup N]
    [Module A N] : grModPieceMap I m (LinearMap.id : N →ₗ[A] N) = LinearMap.id := by
  refine LinearMap.ext fun z => ?_
  induction z using Submodule.Quotient.induction_on with
  | H x => rfl

private theorem grModPieceMap_zero (I : Ideal A) (m : ℕ) {N P : Type u} [AddCommGroup N]
    [Module A N] [AddCommGroup P] [Module A P] :
    grModPieceMap I m (0 : N →ₗ[A] P) = 0 := by
  refine LinearMap.ext fun z => ?_
  induction z using Submodule.Quotient.induction_on with
  | H x => rfl

/-- The canonical homomorphisms are natural in `M`: `φ_P ∘ (f ⊗ 1) = gr(f) ∘ φ_N`. -/
private theorem grModMap_comp_rTensor (I : Ideal A) (m : ℕ) {N P : Type u} [AddCommGroup N]
    [Module A N] [AddCommGroup P] [Module A P] (f : N →ₗ[A] P) :
    grModMap I P m ∘ₗ LinearMap.rTensor (GrPiece I m) f =
      grModPieceMap I m f ∘ₗ grModMap I N m := by
  refine TensorProduct.ext' fun x a => ?_
  induction a using Submodule.Quotient.induction_on with
  | H a =>
    simp only [LinearMap.comp_apply, LinearMap.rTensor_tmul, grModMap_tmul, grModPieceMap_mk]
    exact congrArg Submodule.Quotient.mk (Subtype.ext (map_smul f a.1 x).symm)

variable (I : Ideal A) (m : ℕ)

/-- The map `⊕ₙ grᵐ_I(Mₙ) → grᵐ_I(M)` induced by the inclusions `Mₙ → M`. -/
private noncomputable def grModPieceDecomp :
    (⨁ n, GrModPiece I (ℳ n) m) →ₗ[A] GrModPiece I M m :=
  DirectSum.toModule A ℕ _ fun n => grModPieceMap I m (ℳ n).subtype

omit [DirectSum.Decomposition ℳ] in
private theorem grModPieceDecomp_lof (n : ℕ) (z : GrModPiece I (ℳ n) m) :
    grModPieceDecomp ℳ I m (DirectSum.lof A ℕ (fun n => GrModPiece I (ℳ n) m) n z) =
      grModPieceMap I m (ℳ n).subtype z := by
  classical
  simp [grModPieceDecomp]

/-- Corollary to Lemma 2, p. 182, third printed sentence, first half: "`gr_I(M)` is a direct sum of
the modules `gr_I(Mₙ)`", degree by degree: `⊕ₙ grᵐ_I(Mₙ) → grᵐ_I(M)` is bijective. -/
private theorem grModPieceDecomp_bijective : Function.Bijective (grModPieceDecomp ℳ I m) := by
  classical
  constructor
  · -- the `k`th component of the image is `grᵐ_I(projPiece k)`
    have key : ∀ k, grModPieceMap I m (projPiece ℳ k) ∘ₗ grModPieceDecomp ℳ I m =
        DirectSum.component A ℕ (fun n => GrModPiece I (ℳ n) m) k := fun k => by
      refine DirectSum.linearMap_ext A fun n => ?_
      by_cases h : n = k
      · subst h
        ext z
        simp only [LinearMap.comp_apply, grModPieceDecomp_lof, DirectSum.component.lof_self]
        rw [← LinearMap.comp_apply, ← grModPieceMap_comp, projPiece_comp_subtype_self,
          grModPieceMap_id, LinearMap.id_apply]
      · ext z
        simp only [LinearMap.comp_apply, grModPieceDecomp_lof, DirectSum.component.of,
          h, ↓reduceDIte]
        rw [← LinearMap.comp_apply, ← grModPieceMap_comp, projPiece_comp_subtype_ne ℳ h,
          grModPieceMap_zero, LinearMap.zero_apply]
    refine (injective_iff_map_eq_zero _).mpr fun z hz => ?_
    refine DirectSum.ext_component A fun k => ?_
    have hk := LinearMap.congr_fun (key k) z
    rw [LinearMap.comp_apply, hz, map_zero] at hk
    rw [map_zero]
    exact hk.symm
  · intro z
    induction z using Submodule.Quotient.induction_on with
    | H y =>
      let q := Submodule.comap (I ^ m • (⊤ : Submodule A M)).subtype
        (I ^ (m + 1) • (⊤ : Submodule A M))
      -- `y = Σₙ ιₙ (πₙ y)`, and `πₙ y ∈ Iᵐ Mₙ`
      let w : ℕ → ↥(I ^ m • (⊤ : Submodule A M)) := fun n =>
        ⟨(ℳ n).subtype (projPiece ℳ n y), Submodule.smul_top_le_comap_smul_top (I ^ m)
          ((ℳ n).subtype ∘ₗ projPiece ℳ n) y.2⟩
      have hw : ∑ n ∈ (DirectSum.decompose ℳ (y : M)).support, w n = y := Subtype.ext (by
        rw [Submodule.coe_sum]
        exact DirectSum.sum_support_decompose ℳ (y : M))
      refine ⟨∑ n ∈ (DirectSum.decompose ℳ (y : M)).support, DirectSum.lof A ℕ
        (fun n => GrModPiece I (ℳ n) m) n (Submodule.Quotient.mk ⟨projPiece ℳ n y,
          Submodule.smul_top_le_comap_smul_top (I ^ m) (projPiece ℳ n) y.2⟩), ?_⟩
      rw [map_sum]
      calc _ = ∑ n ∈ (DirectSum.decompose ℳ (y : M)).support, q.mkQ (w n) :=
            Finset.sum_congr rfl fun n _ => by rw [grModPieceDecomp_lof, grModPieceMap_mk]; rfl
        _ = q.mkQ (∑ n ∈ (DirectSum.decompose ℳ (y : M)).support, w n) := (map_sum _ _ _).symm
        _ = Submodule.Quotient.mk y := by rw [hw]; rfl

/-- Corollary to Lemma 2, p. 182, third printed sentence, second half: "so that the homomorphism
`φ` is the direct sum of the canonical homomorphisms `φₙ`", in degree `m`: under the isomorphisms
`⊕ₙ (Mₙ ⊗_A grᵐ_I(A)) ≅ M ⊗_A grᵐ_I(A)` and `⊕ₙ grᵐ_I(Mₙ) ≅ grᵐ_I(M)`, the map `φ` is
`⊕ₙ φₙ`. -/
private theorem grModMap_tensorDecompEquiv (w : ⨁ n, ℳ n ⊗[A] GrPiece I m) :
    grModMap I M m (tensorDecompEquiv ℳ (GrPiece I m) w) =
      grModPieceDecomp ℳ I m (DirectSum.lmap (fun n => grModMap I (ℳ n) m) w) := by
  classical
  have h : grModMap I M m ∘ₗ (tensorDecompEquiv ℳ (GrPiece I m)).toLinearMap =
      grModPieceDecomp ℳ I m ∘ₗ DirectSum.lmap (fun n => grModMap I (ℳ n) m) := by
    refine DirectSum.linearMap_ext A fun n => LinearMap.ext fun z => ?_
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, tensorDecompEquiv_lof,
      DirectSum.lmap_lof, grModPieceDecomp_lof]
    exact LinearMap.congr_fun (grModMap_comp_rTensor I m (ℳ n).subtype) z
  exact LinearMap.congr_fun h w

/-- Corollary to Lemma 2, p. 182, third printed sentence: since `φ` is the direct sum of the
`φₙ`, it is an isomorphism (in each degree `m`) if and only if every `φₙ` is. -/
private theorem bijective_grModMap_iff_forall_graded :
    Function.Bijective (grModMap I M m) ↔ ∀ n, Function.Bijective (grModMap I (ℳ n) m) := by
  classical
  let e := LinearEquiv.ofBijective (grModPieceDecomp ℳ I m) (grModPieceDecomp_bijective ℳ I m)
  let F' : (⨁ n, ℳ n ⊗[A] GrPiece I m) →ₗ[A] ⨁ n, GrModPiece I (ℳ n) m :=
    DirectSum.lmap fun n => grModMap I (ℳ n) m
  have h : ∀ w, grModMap I M m (tensorDecompEquiv ℳ (GrPiece I m) w) = e (F' w) := fun w =>
    grModMap_tensorDecompEquiv ℳ I m w
  rw [(injective_bijective_iff_of_comp_eq (grModMap I M m) F' (tensorDecompEquiv ℳ (GrPiece I m))
    e h).2]
  exact ⟨fun h n => ⟨(DirectSum.lmap_injective _).mp h.1 n, (DirectSum.lmap_surjective _).mp h.2 n⟩,
    fun h => ⟨(DirectSum.lmap_injective _).mpr fun n => (h n).1,
      (DirectSum.lmap_surjective _).mpr fun n => (h n).2⟩⟩

end GradedPieces

/-- Corollary to Lemma 2, p. 182: "The three conditions of the above lemma remain equivalent to
each other if we replace the assumptions on `IB` and `M` by the following ones: `B` is a graded
`A`-algebra of finite type which is generated by homogeneous elements of positive degrees as an
`A`-algebra, `I` is contained in the Jacobson radical of `A`, and `M` is a graded `B`-module of
finite type."

Encoding: the grading of `B` is `𝒜 : ℕ → Submodule A B` with `[GradedAlgebra 𝒜]`; "generated
by homogeneous elements of positive degrees" is `Algebra.adjoin A (⋃ n, 𝒜 (n+1)) = ⊤`; the
graded `B`-module `M` is `ℳ : ℕ → Submodule A M` with `[SetLike.GradedSMul 𝒜 ℳ]` and
`[DirectSum.Decomposition ℳ]`.  (`B` is noetherian, being of finite type over the noetherian
ring `A`, so that hypothesis of Lemma 2 is not repeated.)  The gradings are by `ℕ`; the paper's
"for every integer `n`" may allow `ℤ`-graded `M`, which (being finitely generated over the
`ℕ`-graded `B`) is bounded below and becomes `ℕ`-graded after a shift.

Proof, as printed (p. 182): "Then the assertion of
the corollary can be verified by applying Lemma 2 to `(A =) A`, `(B =) A`, and `(M =) Mₙ` for every
integer `n`" (`finite_piece_of_adjoin_eq_top` gives that `Mₙ` is of finite type, as the paper
shows just before).  "In fact, first of all by the definition of flatness, the `A`-module `M` is
flat if and only if all the direct summands `Mₙ` of `M` are flat `A`-modules"
(`flat_iff_forall_flat_graded`, and `flat_baseChange_iff_forall_graded` for `M ⊗_A A/I`).
"Secondly, the functor `Tor₁^A` commutes with direct summation of modules"
(`isZero_tor_iff_forall_graded`).  "And finally `gr⁰_I(M)` (resp. `gr_I(M)`) is a direct sum of
the modules `gr⁰_I(Mₙ)` (resp. `gr_I(Mₙ)`) for all integers `n`, so that the homomorphism `φ` is
the direct sum of the canonical homomorphisms `φₙ`" (`grModPieceDecomp_bijective`,
`grModMap_tensorDecompEquiv`, `bijective_grModMap_iff_forall_graded`).  Hence each of the three
conditions for `M` is equivalent to the same condition for all `Mₙ`, and the equivalence of the
three conditions for `M` follows from that for every `Mₙ`, which is Lemma 2.

Gaps filled (the paper states these without argument): the finiteness of the `Bₙ` and of the
`Mₙ`; that `Tor₁^A` commutes with direct sums, which Lean proves only in the case used,
`Tor₁^A(-, A/I)` (through `compat:tor-one-quotient`, because Mathlib's `Tor` has no direct-sum
API); that `gr_I(M)` is the direct sum of the `gr_I(Mₙ)` and `φ` the direct sum of the `φₙ`,
degree by degree. -/
@[blueprint "cor:II.1-lem2"
  (statement := /-- The three conditions of \cref{lem:II.1-2} remain equivalent to each other
    if we replace the assumptions on $IB$ and $M$ by the following ones: $B$ is a graded
    $A$-algebra of finite type which is generated by homogeneous elements of positive degrees
    as an $A$-algebra, $I$ is contained in the Jacobson radical of $A$, and $M$ is a graded
    $B$-module of finite type. (p.~182.) (Formalization note (encoding): gradings are
    $\mathbb N$-gradings; a finitely generated $\mathbb Z$-graded $M$ is bounded below and
    becomes $\mathbb N$-graded after a shift, which changes none of the conditions.) -/)
  (proof := /-- (The paper's proof, p.~182.) The $A$-algebra $B$ is a direct sum of its homogeneous parts $B_n$, $n\ge0$,
    each an $A$-module of finite type. Since $M$ is a graded $B$-module of finite type, it is
    a homomorphic image of a direct sum of finitely many copies of $B$ (with shifted
    gradings), so all homogeneous parts $M_n$ of $M$ are $A$-modules of finite type. Apply
    \cref{lem:II.1-2} to $A$, $B:=A$ and $M_n$ for every $n$ (here $I$ lies in the Jacobson
    radical of $A$). ``In fact, first of all by the definition of flatness, the $A$-module $M$
    is flat if and only if all the direct summands $M_n$ of $M$ are flat $A$-modules.
    Secondly, the functor $\operatorname{Tor}^A_1$ commutes with direct summation of modules,
    and finally $\operatorname{gr}^0_I(M)$ (resp.\ $\operatorname{gr}_I(M)$) is a direct sum of
    the modules $\operatorname{gr}^0_I(M_n)$ (resp.\ $\operatorname{gr}_I(M_n)$) for all
    integers $n$, so that the homomorphism $\varphi$ is the direct sum of the canonical
    homomorphisms $\varphi_n\colon\operatorname{gr}^0_I(M_n)\otimes_{A/I}\operatorname{gr}_I(A)
    \to\operatorname{gr}_I(M_n)$ for all integers $n$.'' Hence each of the conditions (i),
    (ii), (iii) for $M$ is equivalent to the same condition for all the $M_n$, and the
    equivalence of (i), (ii), (iii) for $M$ follows from \cref{lem:II.1-2} for every $M_n$.

    \textbf{Formalization note.} The three printed sentences are three lemmas in Lean. The
    functor $\operatorname{Tor}^A_1$ is only used through the vanishing of
    $\operatorname{Tor}^A_1(-,A/I)$; Lean proves that $\operatorname{Tor}^A_1(M,A/I)=0$ if and
    only if $\operatorname{Tor}^A_1(M_n,A/I)=0$ for all $n$ by means of
    \cref{compat:tor-one-quotient} ($\operatorname{Tor}^A_1(N,A/I)=0$ if and only if
    $N\otimes_AI\to N$ is injective) and the decomposition of $M\otimes_AI\to M$ as the direct
    sum of the $M_n\otimes_AI\to M_n$, since Mathlib's $\operatorname{Tor}$ has no direct-sum
    API. -/)
  (latexEnv := "corollary")]
theorem flat_tfae_of_graded (A : Type u) [CommRing A] [IsNoetherianRing A]
    (B : Type u) [CommRing B] [Algebra A B] (𝒜 : ℕ → Submodule A B) [GradedAlgebra 𝒜]
    [Algebra.FiniteType A B] (hgen : Algebra.adjoin A (⋃ n : ℕ, (𝒜 (n + 1) : Set B)) = ⊤)
    (I : Ideal A) (hI : I ≤ Ring.jacobson A)
    (M : Type u) [AddCommGroup M] [Module B M] [Module A M] [IsScalarTower A B M]
    [Module.Finite B M] (ℳ : ℕ → Submodule A M) [SetLike.GradedSMul 𝒜 ℳ]
    [DirectSum.Decomposition ℳ] :
    [Module.Flat A M,
      Module.Flat (A ⧸ I) ((A ⧸ I) ⊗[A] M) ∧
        CategoryTheory.Limits.IsZero (((CategoryTheory.Tor (ModuleCat.{u} A) 1).obj
          (ModuleCat.of A M)).obj (ModuleCat.of A (A ⧸ I))),
      Module.Flat (A ⧸ I) ((A ⧸ I) ⊗[A] M) ∧
        ∀ m : ℕ, Function.Bijective (grModMap I M m)].TFAE := by
  classical
  -- "applying Lemma 2 to `(A =) A`, `(B =) A`, and `(M =) Mₙ` for every integer `n`"
  have hI' : I.map (algebraMap A A) ≤ Ring.jacobson A := by
    rw [Algebra.algebraMap_self, Ideal.map_id]
    exact hI
  have hL2 : ∀ n, [Module.Flat A (ℳ n),
      Module.Flat (A ⧸ I) ((A ⧸ I) ⊗[A] ℳ n) ∧
        CategoryTheory.Limits.IsZero (((CategoryTheory.Tor (ModuleCat.{u} A) 1).obj
          (ModuleCat.of A (ℳ n))).obj (ModuleCat.of A (A ⧸ I))),
      Module.Flat (A ⧸ I) ((A ⧸ I) ⊗[A] ℳ n) ∧
        ∀ m : ℕ, Function.Bijective (grModMap I (ℳ n) m)].TFAE := fun n => by
    have := finite_piece_of_adjoin_eq_top B 𝒜 hgen M ℳ n
    exact flat_tfae_of_map_le_jacobson A A I hI' (ℳ n)
  -- "first of all by the definition of flatness, the `A`-module `M` is flat if and only if all
  -- the direct summands `Mₙ` of `M` are flat `A`-modules"
  have h1 : Module.Flat A M ↔ ∀ n, Module.Flat A (ℳ n) := flat_iff_forall_flat_graded ℳ
  -- "Secondly, the functor `Tor₁^A` commutes with direct summation of modules" (and `M ⊗_A A/I`
  -- is the direct sum of the `Mₙ ⊗_A A/I`)
  have h2 : (Module.Flat (A ⧸ I) ((A ⧸ I) ⊗[A] M) ∧
        CategoryTheory.Limits.IsZero (((CategoryTheory.Tor (ModuleCat.{u} A) 1).obj
          (ModuleCat.of A M)).obj (ModuleCat.of A (A ⧸ I)))) ↔
      ∀ n, Module.Flat (A ⧸ I) ((A ⧸ I) ⊗[A] ℳ n) ∧
        CategoryTheory.Limits.IsZero (((CategoryTheory.Tor (ModuleCat.{u} A) 1).obj
          (ModuleCat.of A (ℳ n))).obj (ModuleCat.of A (A ⧸ I))) := by
    rw [flat_baseChange_iff_forall_graded ℳ I, isZero_tor_iff_forall_graded ℳ I, ← forall_and]
  -- "and finally `gr_I(M)` is a direct sum of the `gr_I(Mₙ)`, so that `φ` is the direct sum of
  -- the `φₙ`"
  have h3 : (Module.Flat (A ⧸ I) ((A ⧸ I) ⊗[A] M) ∧
        ∀ m : ℕ, Function.Bijective (grModMap I M m)) ↔
      ∀ n, Module.Flat (A ⧸ I) ((A ⧸ I) ⊗[A] ℳ n) ∧
        ∀ m : ℕ, Function.Bijective (grModMap I (ℳ n) m) :=
    ⟨fun ⟨hf, hb⟩ n => ⟨(flat_baseChange_iff_forall_graded ℳ I).mp hf n, fun m =>
        (bijective_grModMap_iff_forall_graded ℳ I m).mp (hb m) n⟩,
      fun h => ⟨(flat_baseChange_iff_forall_graded ℳ I).mpr fun n => (h n).1, fun m =>
        (bijective_grModMap_iff_forall_graded ℳ I m).mpr fun n => (h n).2 m⟩⟩
  -- each condition for `M` is equivalent to the same condition for all `Mₙ`, and Lemma 2 applies
  -- to every `Mₙ`
  tfae_have 1 ↔ 2 := by
    rw [h1, h2]
    exact forall_congr' fun n => (hL2 n).out 1 2
  tfae_have 1 ↔ 3 := by
    rw [h1, h3]
    exact forall_congr' fun n => (hL2 n).out 1 3
  tfae_finish

end FlatnessLemmas

/-! ### Proposition 1 and its corollaries (pp. 183–188) -/

section Prop1

variable {O : Type u} [CommRing O]

/-- Membership in a finite sum of ideals. -/
private theorem exists_eq_sum_of_mem_sum {A : Type*} [CommRing A] {ι : Type*} (s : Finset ι)
    (I : ι → Ideal A) {g : A} (hg : g ∈ ∑ a ∈ s, I a) :
    ∃ u : ι → A, (∀ a ∈ s, u a ∈ I a) ∧ ∑ a ∈ s, u a = g := by
  classical
  induction s using Finset.induction_on generalizing g with
  | empty =>
    rw [Finset.sum_empty, Submodule.zero_eq_bot, Submodule.mem_bot] at hg
    exact ⟨0, by simp, by simp [hg]⟩
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Submodule.add_eq_sup, Submodule.mem_sup] at hg
    obtain ⟨y, hy, z, hz, rfl⟩ := hg
    obtain ⟨u, hu, rfl⟩ := ih hz
    refine ⟨Function.update u a y, fun b hb => ?_, ?_⟩
    · rcases Finset.mem_insert.mp hb with rfl | hb
      · simpa using hy
      · rw [Function.update_of_ne (ne_of_mem_of_not_mem hb ha)]
        exact hu b hb
    · rw [Finset.sum_insert ha, Function.update_self]
      congr 1
      exact Finset.sum_congr rfl fun b hb =>
        Function.update_of_ne (ne_of_mem_of_not_mem hb ha) _ _

private theorem le_sum_of_mem {A : Type*} [CommRing A] {ι : Type*} {s : Finset ι}
    (I : ι → Ideal A) {a : ι} (ha : a ∈ s) : I a ≤ ∑ b ∈ s, I b := by
  classical
  rw [← Finset.add_sum_erase s I ha, Submodule.add_eq_sup]
  exact le_sup_left

private theorem sum_le_of_forall {A : Type*} [CommRing A] {ι : Type*} (s : Finset ι)
    (I : ι → Ideal A) {K : Ideal A} (h : ∀ a ∈ s, I a ≤ K) : ∑ a ∈ s, I a ≤ K :=
  Finset.sum_induction I (· ≤ K) (fun _ _ h₁ h₂ => by
    rw [Submodule.add_eq_sup]; exact sup_le h₁ h₂) bot_le h

/-- `(P ⊔ Y)ᵏ ⊆ Σ_{a ≤ k} Pᵃ Yᵏ⁻ᵃ`. -/
private theorem sup_pow_le_sum {A : Type*} [CommRing A] (P Y : Ideal A) (k : ℕ) :
    (P ⊔ Y) ^ k ≤ ∑ a ∈ Finset.range (k + 1), P ^ a * Y ^ (k - a) := by
  rw [← Submodule.add_eq_sup, add_pow]
  exact sum_le_of_forall _ _ fun a ha =>
    Ideal.mul_le_left.trans (le_sum_of_mem (fun a => P ^ a * Y ^ (k - a)) ha)

open MvPolynomial in
/-- Elements of `I · (y)^q` are combinations `Σ_{|α| = q} g_α y^α` with `g_α ∈ I`. -/
theorem exists_eq_sum_mono_of_mem {A : Type*} [CommRing A] {s : ℕ} (y : Fin s → A)
    (D : ℕ → Finset (Fin s →₀ ℕ)) (hD : ∀ q α, α ∈ D q ↔ α.degree = q) (I : Ideal A) (q : ℕ)
    {x : A} (hx : x ∈ I * Ideal.span (Set.range y) ^ q) :
    ∃ g : (Fin s →₀ ℕ) → A, (∀ α, g α ∈ I) ∧
      x = ∑ α ∈ D q, g α * α.prod fun j e => y j ^ e := by
  classical
  refine Submodule.mul_induction_on hx (fun a ha b hb => ?_) (fun x₁ x₂ h₁ h₂ => ?_)
  · obtain ⟨K, hK, rfl⟩ := (Ideal.mem_span_pow_iff_exists_isHomogeneous y b).mp hb
    refine ⟨fun α => a * K.coeff α, fun α => Ideal.mul_mem_right _ _ ha, ?_⟩
    rw [eval_eq, Finset.mul_sum]
    refine Finset.sum_subset (fun α hα => (hD q α).mpr ?_) (fun α _ hα => ?_) |>.trans ?_
    · have := hK (mem_support_iff.mp hα)
      rw [Finsupp.weight_eq_sum] at this
      rw [Finsupp.degree_eq_sum, ← this]
      simp
    · rw [notMem_support_iff.mp hα, zero_mul, mul_zero]
    · refine Finset.sum_congr rfl fun α _ => ?_
      rw [mul_assoc]
      rfl
  · obtain ⟨g₁, hg₁, rfl⟩ := h₁
    obtain ⟨g₂, hg₂, rfl⟩ := h₂
    refine ⟨g₁ + g₂, fun α => add_mem (hg₁ α) (hg₂ α), ?_⟩
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun α _ => by rw [Pi.add_apply, add_mul]

open MvPolynomial in
/-- The value `y^α` of a monomial of degree `q` lies in `(y)^q`. -/
theorem mono_mem_span_pow {A : Type*} [CommRing A] {s : ℕ} (y : Fin s → A)
    (α : Fin s →₀ ℕ) : (α.prod fun j e => y j ^ e) ∈ Ideal.span (Set.range y) ^ α.degree := by
  refine (Ideal.mem_span_pow_iff_exists_isHomogeneous y _).mpr
    ⟨monomial α 1, isHomogeneous_monomial 1 rfl, ?_⟩
  rw [eval_monomial, one_mul]

open MvPolynomial in
/-- Quasi-regularity in coordinates: if `Σ_{|α| = q} c_α y^α ∈ (y)^(q+1)`, all `c_α ∈ (y)`. -/
theorem coeff_mem_of_sum_mono_mem {A : Type*} [CommRing A] {s : ℕ} {y : Fin s → A}
    (hqr : IsQuasiRegular y) (D : ℕ → Finset (Fin s →₀ ℕ))
    (hD : ∀ q α, α ∈ D q ↔ α.degree = q) (q : ℕ) (c : (Fin s →₀ ℕ) → A)
    (h : ∑ α ∈ D q, c α * (α.prod fun j e => y j ^ e) ∈ Ideal.span (Set.range y) ^ (q + 1)) :
    ∀ α ∈ D q, c α ∈ Ideal.span (Set.range y) := by
  classical
  let F : MvPolynomial (Fin s) A := ∑ α ∈ D q, monomial α (c α)
  have hF : F.IsHomogeneous q :=
    IsHomogeneous.sum _ _ _ fun α hα => isHomogeneous_monomial _ ((hD q α).mp hα)
  have hFe : eval y F = ∑ α ∈ D q, c α * (α.prod fun j e => y j ^ e) := by
    simp only [F, map_sum, eval_monomial]
  intro α hα
  have := hqr q F hF (hFe ▸ h) α
  rwa [show F.coeff α = c α by
    simp only [F, coeff_sum, coeff_monomial]
    rw [Finset.sum_eq_single α (fun β _ hβ => by simp [hβ]) (fun h' => absurd hα h')]
    simp]
    at this

/-- The class in `Pᵖ/Pᵖ⁺¹` of an element of `I Pᵖ` lies in `I • grᵖ_P(O)`. -/
theorem mk_mem_smul_top_of_mem_mul_pow {O : Type u} [CommRing O] (P I : Ideal O) (p : ℕ)
    {a : O} (ha : a ∈ I * P ^ p) (haP : a ∈ P ^ p) :
    (Submodule.Quotient.mk ⟨a, haP⟩ : GrPiece P p) ∈ (I • ⊤ : Submodule O (GrPiece P p)) := by
  suffices H : a ∈ P ^ p ∧ ∀ h : a ∈ P ^ p,
      (Submodule.Quotient.mk ⟨a, h⟩ : GrPiece P p) ∈ (I • ⊤ : Submodule O (GrPiece P p)) from
    H.2 haP
  refine Submodule.mul_induction_on ha (fun i hi b hb => ⟨Ideal.mul_mem_left _ i hb, fun h => ?_⟩)
    (fun x y hx hy => ⟨add_mem hx.1 hy.1, fun h => ?_⟩)
  · have : (Submodule.Quotient.mk ⟨i * b, h⟩ : GrPiece P p) =
        i • Submodule.Quotient.mk ⟨b, hb⟩ := by
      rw [← Submodule.Quotient.mk_smul]
      rfl
    rw [this]
    exact Submodule.smul_mem_smul hi Submodule.mem_top
  · have : (Submodule.Quotient.mk ⟨x + y, h⟩ : GrPiece P p) =
        Submodule.Quotient.mk ⟨x, hx.1⟩ + Submodule.Quotient.mk ⟨y, hy.1⟩ := by
      rw [← Submodule.Quotient.mk_add]
      rfl
    rw [this]
    exact add_mem (hx.2 hx.1) (hy.2 hy.1)

/-- An element of `I • grᵖ_P(O)` is the class of an element of `I Pᵖ`. -/
theorem exists_mem_mul_of_mem_smul_top {O : Type u} [CommRing O] (P I : Ideal O) (p : ℕ)
    {v : GrPiece P p} (hv : v ∈ (I • ⊤ : Submodule O (GrPiece P p))) :
    ∃ a ∈ I * P ^ p, ∃ ha : a ∈ P ^ p, Submodule.Quotient.mk ⟨a, ha⟩ = v := by
  refine Submodule.smul_induction_on hv (fun i hi w _ => ?_) (fun v₁ v₂ h₁ h₂ => ?_)
  · induction w using Submodule.Quotient.induction_on with
    | H w =>
      refine ⟨i * w.1, Ideal.mul_mem_mul hi w.2, Ideal.mul_mem_left _ i w.2, ?_⟩
      rw [← Submodule.Quotient.mk_smul]
      rfl
  · obtain ⟨a₁, h₁, h₁P, rfl⟩ := h₁
    obtain ⟨a₂, h₂, h₂P, rfl⟩ := h₂
    exact ⟨a₁ + a₂, add_mem h₁ h₂, add_mem h₁P h₂P, by rw [← Submodule.Quotient.mk_add]; rfl⟩

/-- Sums of classes in a quotient module. -/
theorem quotient_mk_sum {R M : Type*} [Ring R] [AddCommGroup M] [Module R M]
    (N : Submodule R M) {ι : Type*} (s : Finset ι) (x : ι → M) :
    ∑ i ∈ s, (Submodule.Quotient.mk (x i) : M ⧸ N) = Submodule.Quotient.mk (∑ i ∈ s, x i) :=
  (map_sum N.mkQ x s).symm

/-- `gr^q_{m̄}(Ō)` is a free `O/𝔪`-module with basis the classes of the monomials of degree `q`
in a part `ȳ` of a regular system of parameters of `Ō` generating `m̄` (footnote 39). -/
noncomputable def grPieceMapBasis {O : Type u} [CommRing O] (P m : Ideal O)
    (hPm : P ≤ m) {s : ℕ} (z : Fin s → O ⧸ P) (hqr : IsQuasiRegular z)
    (hz : Ideal.span (Set.range z) = m.map (Ideal.Quotient.mk P))
    (D : ℕ → Finset (Fin s →₀ ℕ)) (hD : ∀ q α, α ∈ D q ↔ α.degree = q) (q : ℕ) :
    Module.Basis ↥(D q) (O ⧸ m) (GrPiece (m.map (Ideal.Quotient.mk P)) q) := by
  classical
  have hmem : ∀ α : ↥(D q), (α.1.prod fun j e => z j ^ e) ∈
      (m.map (Ideal.Quotient.mk P)) ^ q := fun α => by
    have := mono_mem_span_pow z α.1
    rwa [(hD q α.1).mp α.2, hz] at this
  let v : ↥(D q) → GrPiece (m.map (Ideal.Quotient.mk P)) q :=
    fun α => Submodule.Quotient.mk ⟨_, hmem α⟩
  have hsmul : ∀ (c : O) (w : GrPiece (m.map (Ideal.Quotient.mk P)) q),
      (Ideal.Quotient.mk m c) • w = (Ideal.Quotient.mk P c) • w := fun c w => rfl
  refine Module.Basis.mk (v := v) ?_ ?_
  · rw [Fintype.linearIndependent_iff]
    intro g hg α
    obtain ⟨g', hg'⟩ : ∃ g' : ↥(D q) → O, ∀ β, Ideal.Quotient.mk m (g' β) = g β :=
      ⟨fun β => Function.surjInv Ideal.Quotient.mk_surjective (g β),
        fun β => Function.surjInv_eq _ _⟩
    simp_rw [← hg', hsmul] at hg
    have h1 : ∑ β : ↥(D q), (Ideal.Quotient.mk P (g' β)) • v β =
        Submodule.Quotient.mk ⟨∑ β : ↥(D q), Ideal.Quotient.mk P (g' β) *
          (β.1.prod fun j e => z j ^ e), sum_mem fun β _ => Ideal.mul_mem_left _ _ (hmem β)⟩ := by
      simp only [v, ← Submodule.Quotient.mk_smul]
      rw [quotient_mk_sum]
      congr 1
      apply Subtype.ext
      simp [smul_eq_mul]
    rw [h1, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap, Submodule.subtype_apply] at hg
    let c : (Fin s →₀ ℕ) → O ⧸ P := fun β =>
      if h : β ∈ D q then Ideal.Quotient.mk P (g' ⟨β, h⟩) else 0
    have hc : ∑ β ∈ D q, c β * (β.prod fun j e => z j ^ e) ∈
        Ideal.span (Set.range z) ^ (q + 1) := by
      rw [hz, ← Finset.sum_coe_sort]
      convert hg using 2 with β
      simp [c, β.2]
    have := coeff_mem_of_sum_mono_mem hqr D hD q c hc α.1 α.2
    simp only [c, dite_eq_left α.2, Subtype.coe_eta] at this
    rw [hz, Ideal.mem_quotient_iff_mem hPm] at this
    rw [← hg', Ideal.Quotient.eq_zero_iff_mem]
    exact this
  · rintro w -
    induction w using Submodule.Quotient.induction_on with
    | H w =>
      obtain ⟨x, hx⟩ := w
      have hx' : x ∈ (⊤ : Ideal (O ⧸ P)) * Ideal.span (Set.range z) ^ q := by
        rw [Ideal.top_mul, hz]
        exact hx
      obtain ⟨g, -, rfl⟩ := exists_eq_sum_mono_of_mem z D hD ⊤ q hx'
      have h2 : (Submodule.Quotient.mk ⟨_, hx⟩ :
          GrPiece (m.map (Ideal.Quotient.mk P)) q) =
          ∑ β : ↥(D q), (Ideal.Quotient.mk m (Function.surjInv Ideal.Quotient.mk_surjective
            (g β.1))) • v β := by
        simp_rw [hsmul, Function.surjInv_eq]
        simp only [v, ← Submodule.Quotient.mk_smul]
        rw [quotient_mk_sum]
        congr 1
        apply Subtype.ext
        simp only [Submodule.coe_sum, Submodule.coe_smul, smul_eq_mul]
        exact (Finset.sum_coe_sort (D q) fun β => g β * (β.prod fun j e => z j ^ e)).symm
      rw [h2]
      exact Submodule.sum_mem _ fun β _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨β, rfl⟩)

theorem grPieceMapBasis_apply {O : Type u} [CommRing O] (P m : Ideal O)
    (hPm : P ≤ m) {s : ℕ} (z : Fin s → O ⧸ P) (hqr : IsQuasiRegular z)
    (hz : Ideal.span (Set.range z) = m.map (Ideal.Quotient.mk P))
    (D : ℕ → Finset (Fin s →₀ ℕ)) (hD : ∀ q α, α ∈ D q ↔ α.degree = q) (q : ℕ) (α : ↥(D q))
    (h : (α.1.prod fun j e => z j ^ e) ∈ (m.map (Ideal.Quotient.mk P)) ^ q) :
    grPieceMapBasis P m hPm z hqr hz D hD q α = Submodule.Quotient.mk ⟨_, h⟩ := by
  simp [grPieceMapBasis, Module.Basis.mk_apply]

private theorem nonempty_basis_grPiece_map {O : Type u} [CommRing O] (P m : Ideal O)
    (hPm : P ≤ m) {s : ℕ} (z : Fin s → O ⧸ P) (hqr : IsQuasiRegular z)
    (hz : Ideal.span (Set.range z) = m.map (Ideal.Quotient.mk P))
    (D : ℕ → Finset (Fin s →₀ ℕ)) (hD : ∀ q α, α ∈ D q ↔ α.degree = q) (q : ℕ) :
    Nonempty (Module.Basis ↥(D q) (O ⧸ m) (GrPiece (m.map (Ideal.Quotient.mk P)) q)) :=
  ⟨grPieceMapBasis P m hPm z hqr hz D hD q⟩

/-- `gr⁰_{m̄}(grᵖ_P(O)) = grᵖ_P(O)/𝔪 grᵖ_P(O)` is free over `O/𝔪` on the image of a basis of the
free `Ō`-module `grᵖ_P(O)`. -/
private theorem nonempty_basis_grModPiece_zero {O : Type u} [CommRing O] (P m : Ideal O)
    (hPm : P ≤ m) (p : ℕ) {ι : Type*} [Fintype ι] (e : Module.Basis ι (O ⧸ P) (GrPiece P p)) :
    Nonempty (Module.Basis ι (O ⧸ m) (GrModPiece m (GrPiece P p) 0)) := by
  classical
  have htop : m ^ 0 • (⊤ : Submodule O (GrPiece P p)) = ⊤ := by
    rw [pow_zero, Ideal.one_eq_top, Submodule.top_smul]
  have hmem : ∀ x : GrPiece P p, x ∈ m ^ 0 • (⊤ : Submodule O (GrPiece P p)) := fun x => by
    rw [htop]
    trivial
  let v : ι → GrModPiece m (GrPiece P p) 0 := fun i => Submodule.Quotient.mk ⟨e i, hmem _⟩
  have hsmul : ∀ (c : O) (w : GrModPiece m (GrPiece P p) 0),
      (Ideal.Quotient.mk m c) • w = c • w := fun c w => rfl
  have hsmul' : ∀ (c : O) (x : GrPiece P p), (Ideal.Quotient.mk P c) • x = c • x :=
    fun c x => rfl
  refine ⟨Module.Basis.mk (v := v) ?_ ?_⟩
  · rw [Fintype.linearIndependent_iff]
    intro g hg i
    obtain ⟨g', hg'⟩ : ∃ g' : ι → O, ∀ j, Ideal.Quotient.mk m (g' j) = g j :=
      ⟨fun j => Function.surjInv Ideal.Quotient.mk_surjective (g j),
        fun j => Function.surjInv_eq _ _⟩
    simp_rw [← hg', hsmul] at hg
    have h1 : ∑ j, g' j • v j =
        Submodule.Quotient.mk ⟨∑ j, g' j • e j, hmem _⟩ := by
      simp only [v, ← Submodule.Quotient.mk_smul]
      rw [quotient_mk_sum]
      congr 1
      apply Subtype.ext
      simp
    rw [h1, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap, Submodule.subtype_apply,
      zero_add, pow_one] at hg
    let φ : GrPiece P p →ₗ[O] O ⧸ P :=
      ((Finsupp.lapply i).comp e.repr.toLinearMap).restrictScalars O
    have h2 := Submodule.mem_map_of_mem (f := φ) hg
    rw [Submodule.map_smul'', Submodule.map_top] at h2
    have h3 : φ (∑ j, g' j • e j) = Ideal.Quotient.mk P (g' i) := by
      rw [map_sum]
      simp_rw [map_smul]
      simp [φ, e.repr_self, Finsupp.single_apply, Algebra.smul_def]
    have h4 : (m • LinearMap.range φ : Submodule O (O ⧸ P)) ≤ (m • ⊤ : Submodule O (O ⧸ P)) :=
      Submodule.smul_mono le_rfl le_top
    have h5 := h4 h2
    rw [Ideal.smul_top_eq_map, h3] at h5
    have : g' i ∈ m := (Ideal.mem_quotient_iff_mem hPm).mp h5
    rw [← hg', Ideal.Quotient.eq_zero_iff_mem]
    exact this
  · rintro w -
    induction w using Submodule.Quotient.induction_on with
    | H w =>
      obtain ⟨x, hx⟩ := w
      let c : ι → O := fun i => Function.surjInv Ideal.Quotient.mk_surjective (e.repr x i)
      have hc : ∀ i, Ideal.Quotient.mk P (c i) = e.repr x i := fun i => Function.surjInv_eq _ _
      have h2 : (Submodule.Quotient.mk ⟨x, hx⟩ : GrModPiece m (GrPiece P p) 0) =
          ∑ i, (Ideal.Quotient.mk m (c i)) • v i := by
        simp_rw [hsmul]
        simp only [v, ← Submodule.Quotient.mk_smul]
        rw [quotient_mk_sum]
        congr 1
        apply Subtype.ext
        simp only [Submodule.coe_sum, Submodule.coe_smul]
        conv_lhs => rw [← e.sum_repr x]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [← hc, hsmul']
      rw [h2]
      exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

section Psi

/-- The product `Iᵖ/Iᵖ⁺¹ × I^q/I^(q+1) → I^(p+q)/I^(p+q+1)`, `([a], [b]) ↦ [ab]`, the
multiplication of the graded ring `gr_I(A)` restricted to homogeneous parts (used for the map `ψ`
of p. 183, which is a homomorphism of graded algebras and is given here by its homogeneous
components). -/
noncomputable def GrPiece.mulPiece (I : Ideal O) (p q : ℕ) :
    GrPiece I p →ₗ[O] GrPiece I q →ₗ[O] GrPiece I (p + q) := by
  let T := GrPiece I (p + q)
  let f : ↥(I ^ p) →ₗ[O] ↥(I ^ q) →ₗ[O] T :=
    LinearMap.mk₂ O (fun a b => (Submodule.Quotient.mk
      (⟨a.1 * b.1, by rw [pow_add]; exact Ideal.mul_mem_mul a.2 b.2⟩ : ↥(I ^ (p + q))) : T))
      (fun a₁ a₂ b => by
        rw [← Submodule.Quotient.mk_add]
        exact congrArg _ (Subtype.ext (add_mul _ _ _)))
      (fun c a b => by
        rw [← Submodule.Quotient.mk_smul]
        exact congrArg _ (Subtype.ext (by simp [mul_assoc])))
      (fun a b₁ b₂ => by
        rw [← Submodule.Quotient.mk_add]
        exact congrArg _ (Subtype.ext (mul_add _ _ _)))
      (fun c a b => by
        rw [← Submodule.Quotient.mk_smul]
        exact congrArg _ (Subtype.ext (by simp [mul_left_comm])))
  have h2 : Submodule.comap (I ^ q).subtype (I ^ (q + 1)) ≤ LinearMap.ker f.flip := by
    intro b hb
    rw [LinearMap.mem_ker]
    refine LinearMap.ext fun a => ?_
    show (Submodule.Quotient.mk _ : T) = 0
    rw [Submodule.Quotient.mk_eq_zero, Submodule.mem_comap, Submodule.subtype_apply]
    show a.1 * b.1 ∈ I ^ (p + q + 1)
    have hb' : b.1 ∈ I ^ (q + 1) := hb
    have := Ideal.mul_mem_mul a.2 hb'
    rwa [← pow_add, show p + (q + 1) = p + q + 1 by omega] at this
  let g : GrPiece I q →ₗ[O] ↥(I ^ p) →ₗ[O] T :=
    (Submodule.comap (I ^ q).subtype (I ^ (q + 1))).liftQ f.flip h2
  have h1 : Submodule.comap (I ^ p).subtype (I ^ (p + 1)) ≤ LinearMap.ker g.flip := by
    intro a ha
    rw [LinearMap.mem_ker]
    refine LinearMap.ext fun b => ?_
    induction b using Submodule.Quotient.induction_on with
    | H b =>
      show (Submodule.Quotient.mk _ : T) = 0
      rw [Submodule.Quotient.mk_eq_zero, Submodule.mem_comap, Submodule.subtype_apply]
      show a.1 * b.1 ∈ I ^ (p + q + 1)
      have ha' : a.1 ∈ I ^ (p + 1) := ha
      have := Ideal.mul_mem_mul ha' b.2
      rwa [← pow_add, show p + 1 + q = p + q + 1 by omega] at this
  exact (Submodule.comap (I ^ p).subtype (I ^ (p + 1))).liftQ g.flip h1

theorem GrPiece.mulPiece_mk (I : Ideal O) (p q : ℕ) (a : ↥(I ^ p)) (b : ↥(I ^ q)) :
    GrPiece.mulPiece I p q (Submodule.Quotient.mk a) (Submodule.Quotient.mk b) =
      Submodule.Quotient.mk ⟨a.1 * b.1, by rw [pow_add]; exact Ideal.mul_mem_mul a.2 b.2⟩ := rfl

/-- `mulPiece` is `O/I`-bilinear. -/
noncomputable def GrPiece.mulPieceQuot (I : Ideal O) (p q : ℕ) :
    GrPiece I p →ₗ[O ⧸ I] GrPiece I q →ₗ[O ⧸ I] GrPiece I (p + q) :=
  LinearMap.mk₂ (O ⧸ I) (fun a b => GrPiece.mulPiece I p q a b)
    (fun a₁ a₂ b => by rw [map_add, LinearMap.add_apply])
    (fun c a b => by
      obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective c
      exact (by rw [show (Ideal.Quotient.mk I c) • a = c • a from rfl, map_smul,
        LinearMap.smul_apply]; rfl))
    (fun a b₁ b₂ => by rw [map_add])
    (fun c a b => by
      obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective c
      exact (by rw [show (Ideal.Quotient.mk I c) • b = c • b from rfl, map_smul]; rfl))

variable (P m : Ideal O) (hPm : P ≤ m)

/-- `grᵖ_P(O) → grᵖ_m(O)`, `[a] ↦ [a]`, induced by the inclusion `Pᵖ ⊆ mᵖ` (the map `α` of
p. 183 in degree `p`, before dividing by `m̄ grᵖ_P(O)`). -/
noncomputable def grPieceInclusion (p : ℕ) : GrPiece P p →ₗ[O] GrPiece m p :=
  Submodule.mapQ _ _ (Submodule.inclusion (Ideal.pow_right_mono hPm p) :
    ↥(P ^ p) →ₗ[O] ↥(m ^ p)) (fun x hx => by
      rw [Submodule.mem_comap] at hx ⊢
      exact Ideal.pow_right_mono hPm (p + 1) hx)

theorem grPieceInclusion_mk (p : ℕ) (a : ↥(P ^ p)) :
    grPieceInclusion P m hPm p (Submodule.Quotient.mk a) =
      Submodule.Quotient.mk ⟨a.1, Ideal.pow_right_mono hPm p a.2⟩ := rfl

/-- The map `α` of p. 183 in degree `p`: `gr⁰_{m̄}(grᵖ_P(O)) = grᵖ_P(O)/m grᵖ_P(O) → grᵖ_m(O)`,
induced by `Pᵖ ⊆ mᵖ` (the kernel of `grᵖ_P(O) → grᵖ_m(O)` contains `m grᵖ_P(O)`, since `m`
annihilates `grᵖ_m(O)`). -/
noncomputable def alphaPiece (p : ℕ) :
    GrModPiece m (GrPiece P p) 0 →ₗ[O ⧸ m] GrPiece m p :=
  LinearMap.extendScalarsOfSurjective (Ideal.Quotient.mk_surjective (I := m))
    ((Submodule.comap ((m ^ 0 • (⊤ : Submodule O (GrPiece P p))).subtype)
      (m ^ (0 + 1) • (⊤ : Submodule O (GrPiece P p)))).liftQ
      ((grPieceInclusion P m hPm p).comp (Submodule.subtype _)) (by
        intro x hx
        rw [LinearMap.mem_ker]
        rw [Submodule.mem_comap, Submodule.subtype_apply] at hx
        show grPieceInclusion P m hPm p x.1 = 0
        refine Submodule.smul_induction_on hx (fun r hr n _ => ?_) (fun a b ha hb => ?_)
        · rw [map_smul]
          rw [← IsScalarTower.algebraMap_smul (O ⧸ m) r (grPieceInclusion P m hPm p n),
            show algebraMap O (O ⧸ m) r = 0 from
              Ideal.Quotient.eq_zero_iff_mem.mpr (by simpa using hr),
            zero_smul]
        · rw [map_add, ha, hb, add_zero]))

theorem mem_pow_zero_smul_top (m : Ideal O) {M : Type*} [AddCommGroup M] [Module O M] (x : M) :
    x ∈ m ^ 0 • (⊤ : Submodule O M) := by
  rw [pow_zero, Ideal.one_eq_top, Submodule.top_smul]
  trivial

theorem alphaPiece_mk (p : ℕ) (x : GrPiece P p) :
    alphaPiece P m hPm p (Submodule.Quotient.mk ⟨x, mem_pow_zero_smul_top m x⟩) =
      grPieceInclusion P m hPm p x := rfl

/-- The monomials of degree `q` in `s` variables. -/
noncomputable def degreeFinset (s q : ℕ) : Finset (Fin s →₀ ℕ) :=
  (Finsupp.finite_of_degree_eq q).toFinset

theorem mem_degreeFinset {s q : ℕ} {α : Fin s →₀ ℕ} : α ∈ degreeFinset s q ↔ α.degree = q := by
  simp [degreeFinset]

section PsiMaps

variable {s : ℕ} (y : Fin s → O)
  (hqr : IsQuasiRegular fun j => Ideal.Quotient.mk P (y j))
  (hz : Ideal.span (Set.range fun j => Ideal.Quotient.mk P (y j)) =
    m.map (Ideal.Quotient.mk P))

include hPm hz in
theorem span_range_le_of_span_map_eq :
    Ideal.span (Set.range y) ≤ m := by
  rw [Ideal.span_le]
  rintro _ ⟨j, rfl⟩
  rw [SetLike.mem_coe, ← Ideal.mem_quotient_iff_mem hPm, ← hz]
  exact Ideal.subset_span ⟨j, rfl⟩

theorem prod_pow_mem_pow_of_span_le (hy : Ideal.span (Set.range y) ≤ m) (q : ℕ)
    (α : Fin s →₀ ℕ) (hα : α.degree = q) : (α.prod fun j e => y j ^ e) ∈ m ^ q := by
  have := mono_mem_span_pow y α
  rw [hα] at this
  exact Ideal.pow_right_mono hy q this

include hPm hqr hz in
/-- The map `β*` of p. 183 in degree `q`: `gr^q_{m̄}(Ō) → gr^q_m(O)`, which sends the class of a
monomial `x̄^α` of degree `q` in the generators `x̄_i = ȳ_i` of `m̄` (a regular system of
parameters of `Ō` generating `m̄`, so that these classes form a basis of `gr^q_{m̄}(Ō)`) to the
class of `y^α` in `gr^q_m(O)`. -/
noncomputable def betaStarPiece (q : ℕ) :
    GrPiece (m.map (Ideal.Quotient.mk P)) q →ₗ[O ⧸ m] GrPiece m q :=
  (grPieceMapBasis P m hPm _ hqr hz (degreeFinset s) (fun _ _ => mem_degreeFinset) q).constr
    (O ⧸ m) (fun α => Submodule.Quotient.mk ⟨_, prod_pow_mem_pow_of_span_le m y
      (span_range_le_of_span_map_eq P m hPm y hz) q α.1 (mem_degreeFinset.mp α.2)⟩)

/-- Transport along an equality of degrees `a = b` (used to read the component `ψ_{p,q}` in total
degree `n = p + q`). -/
noncomputable def GrPiece.castDeg (I : Ideal O) {a b : ℕ} (h : a = b) :
    GrPiece I a →ₗ[O ⧸ I] GrPiece I b := by
  subst h
  exact LinearMap.id

include hPm hqr hz in
/-- The component `ψ_{p,q}: gr⁰_{m̄}(grᵖ_P(O)) ⊗_K gr^q_{m̄}(Ō) → gr^{p+q}_m(O)` of the map
`ψ = α ⊗ β*` of p. 183, `a ⊗ b ↦ α(a) · β*(b)`. -/
noncomputable def psiPiece (p q : ℕ) :
    GrModPiece m (GrPiece P p) 0 ⊗[O ⧸ m] GrPiece (m.map (Ideal.Quotient.mk P)) q →ₗ[O ⧸ m]
      GrPiece m (p + q) :=
  TensorProduct.lift ((GrPiece.mulPieceQuot m p q).compl₁₂ (alphaPiece P m hPm p)
    (betaStarPiece P m hPm y hqr hz q))

/-- The summands `gr⁰_{m̄}(grᵖ_P(O)) ⊗_K gr^q_{m̄}(Ō)`, `p + q = n`, of the source of `ψ` in total
degree `n`. -/
abbrev PsiSummand (P m : Ideal O) (n : ℕ) : {pq : ℕ × ℕ // pq.1 + pq.2 = n} → Type u := fun pq =>
  GrModPiece m (GrPiece P pq.1.1) 0 ⊗[O ⧸ m] GrPiece (m.map (Ideal.Quotient.mk P)) pq.1.2

include hPm hqr hz in
/-- The component `ψ_{p,q}` read in total degree `n = p + q`. -/
noncomputable def psiSummandMap (n : ℕ) (pq : {pq : ℕ × ℕ // pq.1 + pq.2 = n}) :
    PsiSummand P m n pq →ₗ[O ⧸ m] GrPiece m n :=
  (GrPiece.castDeg m pq.2).comp (psiPiece P m hPm y hqr hz pq.1.1 pq.1.2)

include hPm hqr hz in
/-- The homogeneous part of total degree `n` of `ψ = α ⊗ β*` (p. 183):
`⊕_{p+q=n} gr⁰_{m̄}(grᵖ_P(O)) ⊗_K gr^q_{m̄}(Ō) → grⁿ_m(O)`. -/
noncomputable def psiDeg (n : ℕ) :
    (⨁ pq : {pq : ℕ × ℕ // pq.1 + pq.2 = n}, PsiSummand P m n pq) →ₗ[O ⧸ m] GrPiece m n :=
  DirectSum.toModule (O ⧸ m) {pq : ℕ × ℕ // pq.1 + pq.2 = n} (GrPiece m n)
    (psiSummandMap P m hPm y hqr hz n)

include hPm hqr hz in
theorem psiDeg_lof (n : ℕ) (pq : {pq : ℕ × ℕ // pq.1 + pq.2 = n}) (v : PsiSummand P m n pq) :
    psiDeg P m hPm y hqr hz n
        (DirectSum.lof (O ⧸ m) {pq : ℕ × ℕ // pq.1 + pq.2 = n} (PsiSummand P m n) pq v) =
      psiSummandMap P m hPm y hqr hz n pq v :=
  DirectSum.toModule_lof (O ⧸ m) pq v

include hPm hqr hz in
theorem psiPiece_tmul_basis (p q : ℕ) (b : O) (hb : b ∈ P ^ p) (α : ↥(degreeFinset s q))
    (h : b * (α.1.prod fun j e => y j ^ e) ∈ m ^ (p + q)) :
    psiPiece P m hPm y hqr hz p q (Submodule.Quotient.mk ⟨Submodule.Quotient.mk ⟨b, hb⟩,
      mem_pow_zero_smul_top m _⟩ ⊗ₜ[O ⧸ m]
      grPieceMapBasis P m hPm _ hqr hz (degreeFinset s) (fun _ _ => mem_degreeFinset) q α) =
      Submodule.Quotient.mk ⟨b * (α.1.prod fun j e => y j ^ e), h⟩ := by
  unfold psiPiece betaStarPiece
  rw [TensorProduct.lift.tmul, LinearMap.compl₁₂_apply, alphaPiece_mk, grPieceInclusion_mk,
    Module.Basis.constr_basis]
  rfl

/-- The index set of the coefficients of an element of the source of `ψ` in total degree `n`:
a pair `(p, q)` with `p + q = n` and a monomial of degree `q`. -/
abbrev PsiIndex (s n : ℕ) : Type :=
  Σ pq : {pq : ℕ × ℕ // pq.1 + pq.2 = n}, ↥(degreeFinset s pq.1.2)

instance (n : ℕ) : Finite {pq : ℕ × ℕ // pq.1 + pq.2 = n} :=
  Finite.of_injective
    (fun pq => (⟨pq.1.1, Nat.lt_succ_of_le (by have := pq.2; omega)⟩ : Fin (n + 1)))
    (fun a b h => by
      have h1 : a.1.1 = b.1.1 := Fin.mk.inj h
      have ha := a.2
      have hb := b.2
      exact Subtype.ext (Prod.ext h1 (by omega)))

noncomputable instance (n : ℕ) : Fintype {pq : ℕ × ℕ // pq.1 + pq.2 = n} :=
  Fintype.ofFinite _

include hPm hqr hz in
/-- The basis of `gr^q_{m̄}(Ō)` by the monomials `x̄^α` of degree `q`. -/
noncomputable abbrev psiBasis (q : ℕ) :
    Module.Basis ↥(degreeFinset s q) (O ⧸ m) (GrPiece (m.map (Ideal.Quotient.mk P)) q) :=
  grPieceMapBasis P m hPm _ hqr hz (degreeFinset s) (fun _ _ => mem_degreeFinset) q

include hPm hqr hz in
/-- The map `a ↦ ψ_{p,q}(a ⊗ x̄^α)` for a monomial `x̄^α` of degree `q = n - p`. -/
noncomputable def psiMono (n : ℕ) (i : PsiIndex s n) :
    GrModPiece m (GrPiece P i.1.1.1) 0 →ₗ[O ⧸ m] GrPiece m n :=
  (GrPiece.castDeg m i.1.2).comp ((psiPiece P m hPm y hqr hz i.1.1.1 i.1.1.2).comp
    ((TensorProduct.mk (O ⧸ m) _ _).flip
      (psiBasis P m hPm y hqr hz
        i.1.1.2 i.2)))

include hPm hqr hz in
/-- The coefficient of the monomial `x̄^α` in the component `(p, q)` of an element of the source of
`ψ` in total degree `n` (`K`-linear in the element). -/
noncomputable def psiCoeff (n : ℕ) (i : PsiIndex s n) :
    (⨁ pq : {pq : ℕ × ℕ // pq.1 + pq.2 = n},
      GrModPiece m (GrPiece P pq.1.1) 0 ⊗[O ⧸ m] GrPiece (m.map (Ideal.Quotient.mk P)) pq.1.2)
      →ₗ[O ⧸ m] GrModPiece m (GrPiece P i.1.1.1) 0 :=
  (Finsupp.lapply i.2).comp ((TensorProduct.equivFinsuppOfBasisRight
    (psiBasis P m hPm y hqr hz
      i.1.1.2)).toLinearMap.comp (DirectSum.component (O ⧸ m) _ _ i.1))

theorem tmul_eq_sum_repr {K M N κ : Type*} [CommRing K] [AddCommGroup M] [Module K M]
    [AddCommGroup N] [Module K N] [Fintype κ] (B : Module.Basis κ K N) (a : M) (b : N) :
    a ⊗ₜ[K] b = ∑ α, (B.repr b α • a) ⊗ₜ[K] B α := by
  conv_lhs => rw [← B.sum_repr b]
  rw [TensorProduct.tmul_sum]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [TensorProduct.tmul_smul, TensorProduct.smul_tmul']

include hPm hqr hz in
theorem psiDeg_eq_sum_comp (n : ℕ) :
    psiDeg P m hPm y hqr hz n = ∑ i : PsiIndex s n, (psiMono P m hPm y hqr hz n i).comp
      (psiCoeff P m hPm y hqr hz n i) := by
  refine DirectSum.linearMap_ext (O ⧸ m) fun pq => TensorProduct.ext' fun a b => ?_
  simp only [LinearMap.comp_apply, LinearMap.sum_apply]
  set v : PsiSummand P m n pq := a ⊗ₜ[O ⧸ m] b with hv
  have hs : (DirectSum.lof (O ⧸ m) _ (PsiSummand P m n) pq v) pq = v := DirectSum.of_eq_same _ _
  have hn : ∀ pq', pq' ≠ pq → (DirectSum.lof (O ⧸ m) _ (PsiSummand P m n) pq v) pq' = 0 :=
    fun pq' h => DirectSum.of_eq_of_ne _ _ _ h
  rw [Fintype.sum_sigma, Finset.sum_eq_single pq]
  · have key : ∀ α, psiCoeff P m hPm y hqr hz n ⟨pq, α⟩
        (DirectSum.lof (O ⧸ m) _ (PsiSummand P m n) pq v) =
        ((psiBasis P m hPm y hqr hz
          pq.1.2).repr b α) • a := by
      intro α
      have h3 : (DirectSum.component (O ⧸ m) _ (PsiSummand P m n) pq)
          (DirectSum.lof (O ⧸ m) _ (PsiSummand P m n) pq v) = a ⊗ₜ[O ⧸ m] b := hs
      exact (congrArg (fun w => (TensorProduct.equivFinsuppOfBasisRight
        (psiBasis P m hPm y hqr hz pq.1.2)) w α) h3).trans
        (TensorProduct.equivFinsuppOfBasisRight_apply_tmul_apply
          (psiBasis P m hPm y hqr hz pq.1.2) a b α)
    simp only [key]
    have h4 : psiDeg P m hPm y hqr hz n (DirectSum.lof (O ⧸ m) _ (PsiSummand P m n) pq v) =
        (GrPiece.castDeg m pq.2) (psiPiece P m hPm y hqr hz pq.1.1 pq.1.2 v) :=
      psiDeg_lof P m hPm y hqr hz n pq v
    rw [h4, hv, tmul_eq_sum_repr (psiBasis P m hPm y hqr hz pq.1.2) a b, map_sum, map_sum]
    rfl
  · intro pq' _ hne
    refine Finset.sum_eq_zero fun α _ => ?_
    have : psiCoeff P m hPm y hqr hz n ⟨pq', α⟩
        (DirectSum.lof (O ⧸ m) _ (PsiSummand P m n) pq v) = 0 := by
      simp only [psiCoeff, LinearMap.comp_apply, LinearEquiv.coe_coe, Finsupp.lapply_apply]
      have h5 : (DirectSum.component (O ⧸ m) _ (PsiSummand P m n) pq')
          (DirectSum.lof (O ⧸ m) _ (PsiSummand P m n) pq v) = 0 := hn pq' hne
      exact (congrArg (fun w => (TensorProduct.equivFinsuppOfBasisRight
        (psiBasis P m hPm y hqr hz pq'.1.2)) w α) h5).trans (by rw [LinearEquiv.map_zero]; rfl)
    rw [this, map_zero]
  · intro h
    exact absurd (Finset.mem_univ pq) h

include hPm hqr hz in
theorem psiCoeff_ext (n : ℕ)
    (x x' : ⨁ pq : {pq : ℕ × ℕ // pq.1 + pq.2 = n},
      GrModPiece m (GrPiece P pq.1.1) 0 ⊗[O ⧸ m] GrPiece (m.map (Ideal.Quotient.mk P)) pq.1.2) :
    x = x' ↔ ∀ i : PsiIndex s n,
      psiCoeff P m hPm y hqr hz n i x = psiCoeff P m hPm y hqr hz n i x' := by
  refine ⟨fun h _ => by rw [h], fun h => ?_⟩
  refine DFinsupp.ext fun pq => ?_
  apply (TensorProduct.equivFinsuppOfBasisRight
    (psiBasis P m hPm y hqr hz
      pq.1.2)).injective
  refine Finsupp.ext fun α => ?_
  exact h ⟨pq, α⟩

include hPm hqr hz in
theorem exists_psiCoeff_eq (n : ℕ) (c : (i : PsiIndex s n) → GrModPiece m (GrPiece P i.1.1.1) 0) :
    ∃ x : (⨁ pq : {pq : ℕ × ℕ // pq.1 + pq.2 = n},
      GrModPiece m (GrPiece P pq.1.1) 0 ⊗[O ⧸ m] GrPiece (m.map (Ideal.Quotient.mk P)) pq.1.2),
      ∀ i, psiCoeff P m hPm y hqr hz n i x = c i := by
  set F : (pq : ↥(Finset.univ : Finset {pq : ℕ × ℕ // pq.1 + pq.2 = n})) →
      GrModPiece m (GrPiece P pq.1.1.1) 0 ⊗[O ⧸ m]
        GrPiece (m.map (Ideal.Quotient.mk P)) pq.1.1.2 := fun pq =>
    (TensorProduct.equivFinsuppOfBasisRight
      (psiBasis P m hPm y hqr hz
        pq.1.1.2)).symm (Finsupp.equivFunOnFinite.symm fun α => c ⟨pq.1, α⟩) with hF
  refine ⟨DirectSum.mk (PsiSummand P m n) Finset.univ F, fun i => ?_⟩
  obtain ⟨pq, α⟩ := i
  have h1 : (DirectSum.mk (PsiSummand P m n) Finset.univ F) pq = F ⟨pq, Finset.mem_univ pq⟩ :=
    DirectSum.mk_apply_of_mem (Finset.mem_univ pq)
  have h2 : (DirectSum.component (O ⧸ m) _ _ pq) (DirectSum.mk (PsiSummand P m n) Finset.univ F) =
      (DirectSum.mk (PsiSummand P m n) Finset.univ F) pq := rfl
  simp only [psiCoeff, LinearMap.comp_apply, LinearEquiv.coe_coe, Finsupp.lapply_apply]
  refine (congrArg (fun v => (TensorProduct.equivFinsuppOfBasisRight
    (psiBasis P m hPm y hqr hz
      pq.1.2)) v α) (h2.trans h1)).trans ?_
  simp only [hF, LinearEquiv.apply_symm_apply]
  rfl

include hPm hqr hz in
/-- `ψ` is injective in total degree `n` iff its monomial components have no linear relation. -/
theorem psiDeg_injective_iff (n : ℕ) :
    Function.Injective (psiDeg P m hPm y hqr hz n) ↔
      ∀ c d : (i : PsiIndex s n) → GrModPiece m (GrPiece P i.1.1.1) 0,
        ∑ i, psiMono P m hPm y hqr hz n i (c i) = ∑ i, psiMono P m hPm y hqr hz n i (d i) →
          ∀ i, c i = d i := by
  refine ⟨fun h c d hcd i => ?_, fun h x z hxz => ?_⟩
  · obtain ⟨x, hx⟩ := exists_psiCoeff_eq P m hPm y hqr hz n c
    obtain ⟨z, hz'⟩ := exists_psiCoeff_eq P m hPm y hqr hz n d
    have h0 : psiDeg P m hPm y hqr hz n x = psiDeg P m hPm y hqr hz n z := by
      rw [psiDeg_eq_sum_comp, LinearMap.sum_apply, LinearMap.sum_apply]
      simp only [LinearMap.comp_apply, hx, hz']
      exact hcd
    have := (psiCoeff_ext P m hPm y hqr hz n x z).mp (h h0) i
    rw [hx i, hz' i] at this
    exact this
  · rw [psiCoeff_ext P m hPm y hqr hz n]
    refine h _ _ ?_
    rw [psiDeg_eq_sum_comp, LinearMap.sum_apply, LinearMap.sum_apply] at hxz
    simpa only [LinearMap.comp_apply] using hxz

end PsiMaps

section ZeroPiece

variable (P m : Ideal O)

/-- The class in `gr⁰_{m}(grᵖ_P(O)) = grᵖ_P(O)/m grᵖ_P(O)` of an element `a ∈ Pᵖ`. -/
def zeroPieceMk (p : ℕ) (a : O) (ha : a ∈ P ^ p) : GrModPiece m (GrPiece P p) 0 :=
  Submodule.Quotient.mk ⟨Submodule.Quotient.mk ⟨a, ha⟩, mem_pow_zero_smul_top m _⟩

theorem zeroPieceMk_add (p : ℕ) (a b : O) (ha : a ∈ P ^ p) (hb : b ∈ P ^ p) :
    zeroPieceMk P m p (a + b) (add_mem ha hb) = zeroPieceMk P m p a ha + zeroPieceMk P m p b hb :=
  rfl

theorem zeroPieceMk_congr (p : ℕ) {a a' : O} (h : a = a') (ha : a ∈ P ^ p) (ha' : a' ∈ P ^ p) :
    zeroPieceMk P m p a ha = zeroPieceMk P m p a' ha' := by
  subst h
  rfl

theorem zeroPieceMk_eq_zero_iff (p : ℕ) (a : O) (ha : a ∈ P ^ p) :
    zeroPieceMk P m p a ha = 0 ↔ a ∈ m * P ^ p ⊔ P ^ (p + 1) := by
  unfold zeroPieceMk
  rw [Submodule.Quotient.mk_eq_zero, Submodule.mem_comap, Submodule.subtype_apply]
  constructor
  · intro h
    have h' : (Submodule.Quotient.mk ⟨a, ha⟩ : GrPiece P p) ∈
        (m ^ (0 + 1) • (⊤ : Submodule O (GrPiece P p))) := h
    rw [zero_add, pow_one] at h'
    obtain ⟨a', ha'm, ha'P, hmk⟩ := exists_mem_mul_of_mem_smul_top P m p h'
    rw [Submodule.Quotient.eq, Submodule.mem_comap] at hmk
    have hr : a' - a ∈ P ^ (p + 1) := hmk
    have : a = a' + (a - a') := by ring
    rw [this]
    exact add_mem (Ideal.mem_sup_left ha'm) (Ideal.mem_sup_right (by
      have := (P ^ (p + 1)).neg_mem hr
      simpa using this))
  · intro h
    rw [zero_add, pow_one]
    obtain ⟨q, hq, r, hr, rfl⟩ := Submodule.mem_sup.mp h
    have hqP : q ∈ P ^ p := (Ideal.mul_le_right : m * P ^ p ≤ P ^ p) hq
    have h1 : (Submodule.Quotient.mk ⟨q + r, ha⟩ : GrPiece P p) =
        Submodule.Quotient.mk ⟨q, hqP⟩ := by
      rw [Submodule.Quotient.eq, Submodule.mem_comap]
      show q + r - q ∈ P ^ (p + 1)
      simpa using hr
    have key : (Submodule.Quotient.mk ⟨q + r, ha⟩ : GrPiece P p) ∈
        (m • ⊤ : Submodule O (GrPiece P p)) := by
      rw [h1]
      exact mk_mem_smul_top_of_mem_mul_pow P m p hq hqP
    exact key

theorem exists_zeroPieceMk_eq (p : ℕ) (x : GrModPiece m (GrPiece P p) 0) :
    ∃ (a : O) (ha : a ∈ P ^ p), x = zeroPieceMk P m p a ha := by
  induction x using Submodule.Quotient.induction_on with
  | H x =>
    obtain ⟨x, hx⟩ := x
    induction x using Submodule.Quotient.induction_on with
    | H x =>
      obtain ⟨a, ha⟩ := x
      exact ⟨a, ha, rfl⟩

end ZeroPiece

section PsiMonoZero

variable {s : ℕ} (y : Fin s → O)
  (hqr : IsQuasiRegular fun j => Ideal.Quotient.mk P (y j))
  (hz : Ideal.span (Set.range fun j => Ideal.Quotient.mk P (y j)) =
    m.map (Ideal.Quotient.mk P))

theorem GrPiece.castDeg_mk (I : Ideal O) {a b : ℕ} (h : a = b) (x : O) (hx : x ∈ I ^ a)
    (hx' : x ∈ I ^ b) :
    GrPiece.castDeg I h (Submodule.Quotient.mk ⟨x, hx⟩) = Submodule.Quotient.mk ⟨x, hx'⟩ := by
  subst h
  rfl

include hPm hqr hz in
/-- `psiMono` on the class of `b ∈ Pᵖ` is the class of `b y^α` in `grⁿ_m(O)`. -/
theorem psiMono_zeroPieceMk (n : ℕ) (i : PsiIndex s n) (b : O) (hb : b ∈ P ^ i.1.1.1)
    (h : b * (i.2.1.prod fun j e => y j ^ e) ∈ m ^ n) :
    psiMono P m hPm y hqr hz n i (zeroPieceMk P m i.1.1.1 b hb) =
      Submodule.Quotient.mk ⟨b * (i.2.1.prod fun j e => y j ^ e), h⟩ := by
  obtain ⟨⟨⟨p, q⟩, hpq⟩, α⟩ := i
  have h1 := psiPiece_tmul_basis P m hPm y hqr hz p q b hb α
    (by have := h; subst hpq; exact this)
  unfold psiMono
  show GrPiece.castDeg m hpq (psiPiece P m hPm y hqr hz p q (Submodule.Quotient.mk
    ⟨Submodule.Quotient.mk ⟨b, hb⟩, mem_pow_zero_smul_top m _⟩ ⊗ₜ[O ⧸ m]
      psiBasis P m hPm y hqr hz q α)) = _
  rw [h1]
  exact GrPiece.castDeg_mk m hpq _ _ h

include hPm hz in
theorem mono_mul_mem_pow (n : ℕ) (i : PsiIndex s n) (b : O) (hb : b ∈ P ^ i.1.1.1) :
    b * (i.2.1.prod fun j e => y j ^ e) ∈ m ^ n := by
  obtain ⟨⟨⟨p, q⟩, hpq⟩, α⟩ := i
  have hy : Ideal.span (Set.range y) ≤ m := span_range_le_of_span_map_eq P m hPm y hz
  have h1 := Ideal.mul_mem_mul (Ideal.pow_right_mono hPm p hb)
    (prod_pow_mem_pow_of_span_le m y hy q α.1 (mem_degreeFinset.mp α.2))
  rw [← pow_add] at h1
  have : p + q = n := hpq
  rwa [this] at h1

include hPm hqr hz in
/-- The sum over all monomial components of the classes of `b_i y^α` is the class of the sum. -/
theorem sum_psiMono_zeroPieceMk (n : ℕ) (b : PsiIndex s n → O)
    (hb : ∀ i, b i ∈ P ^ i.1.1.1) (h : ∑ i, b i * (i.2.1.prod fun j e => y j ^ e) ∈ m ^ n) :
    ∑ i, psiMono P m hPm y hqr hz n i (zeroPieceMk P m i.1.1.1 (b i) (hb i)) =
      Submodule.Quotient.mk ⟨∑ i, b i * (i.2.1.prod fun j e => y j ^ e), h⟩ := by
  classical
  have hmem := fun i => mono_mul_mem_pow P m hPm y hz n i (b i) (hb i)
  have key : ∀ S : Finset (PsiIndex s n), ∑ i ∈ S, psiMono P m hPm y hqr hz n i
      (zeroPieceMk P m i.1.1.1 (b i) (hb i)) =
      Submodule.Quotient.mk ⟨∑ i ∈ S, b i * (i.2.1.prod fun j e => y j ^ e),
        Ideal.sum_mem _ fun i _ => hmem i⟩ := by
    intro S
    induction S using Finset.induction_on with
    | empty => rfl
    | insert a S ha ih =>
      rw [Finset.sum_insert ha, ih,
        psiMono_zeroPieceMk P m hPm y hqr hz n a (b a) (hb a) (hmem a)]
      have : (Submodule.Quotient.mk ⟨∑ i ∈ insert a S, b i * (i.2.1.prod fun j e => y j ^ e),
          Ideal.sum_mem _ fun i _ => hmem i⟩ : GrPiece m n) =
          Submodule.Quotient.mk ⟨b a * (a.2.1.prod fun j e => y j ^ e), hmem a⟩ +
            Submodule.Quotient.mk ⟨∑ i ∈ S, b i * (i.2.1.prod fun j e => y j ^ e),
              Ideal.sum_mem _ fun i _ => hmem i⟩ := by
        rw [← Submodule.Quotient.mk_add]
        exact congrArg _ (Subtype.ext (Finset.sum_insert ha))
      exact this.symm
  exact key Finset.univ

end PsiMonoZero
end Psi
section Prop1Core

/-- The ideal `Σ_{s>0, s+t=q} Pˢ Fᵗ` of p. 185. -/
private def mixedIdeal (P F : Ideal O) (q : ℕ) : Ideal O :=
  ∑ s ∈ Finset.Icc 1 q, P ^ s * F ^ (q - s)

private theorem mixedIdeal_le (P F : Ideal O) (q : ℕ) : mixedIdeal P F q ≤ P :=
  sum_le_of_forall _ _ fun s hs => by
    have h1 : s ≠ 0 := by have := Finset.mem_Icc.mp hs; omega
    exact Ideal.mul_le_left.trans (Ideal.pow_le_self h1)

/-- An element of `span (f) · J` is `Σ f_i c_i` with `c_i ∈ J` (`Pᵖ = (f_i^{(p)})_i`, p. 185). -/
private theorem exists_eq_sum_mul_of_mem_mul {ι : Type*} [Fintype ι] (f : ι → O) (J : Ideal O)
    {u : O} (hu : u ∈ Ideal.span (Set.range f) * J) :
    ∃ c : ι → O, (∀ i, c i ∈ J) ∧ u = ∑ i, f i * c i := by
  refine Submodule.mul_induction_on hu (fun a ha b hb => ?_) (fun x y hx hy => ?_)
  · obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun O).mp ha
    refine ⟨fun i => c i * b, fun i => J.mul_mem_left _ hb, ?_⟩
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ => by rw [smul_eq_mul]; ring
  · obtain ⟨c, hc, rfl⟩ := hx
    obtain ⟨d, hd, rfl⟩ := hy
    exact ⟨c + d, fun i => add_mem (hc i) (hd i), by
      simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]⟩

/-- p. 185: "`λ ∈ 𝔪^{q+1}` ... It then follows that `λ ∈ Σ_{(q+1=u+v, u≥0)} PᵘFᵛ ⊂
Σ_{(q=s+t, s>0)} PˢFᵗ + F^{q+1}`" (for `q ≥ 1`, and in the form `𝔪^{r+1} ⊆ ... + F^{r+1}` for
`r ≥ q`, as needed for the iteration). -/
private theorem pow_succ_le_mixedIdeal_sup (P F : Ideal O) {q r : ℕ} (hq : 1 ≤ q)
    (hqr : q ≤ r) : (P ⊔ F) ^ (r + 1) ≤ mixedIdeal P F q ⊔ F ^ (r + 1) := by
  refine (sup_pow_le_sum P F (r + 1)).trans (sum_le_of_forall _ _ fun u hu => ?_)
  have hu' := Finset.mem_range.mp hu
  rcases Nat.eq_zero_or_pos u with rfl | hu0
  · simp only [pow_zero, Ideal.one_eq_top, Ideal.top_mul, Nat.sub_zero]
    exact le_sup_right
  · refine le_sup_of_le_left ?_
    refine le_trans ?_ (le_sum_of_mem (fun s => P ^ s * F ^ (q - s))
      (s := Finset.Icc 1 q) (a := min u q) ?_)
    · exact Ideal.mul_mono (Ideal.pow_le_pow_right (min_le_left _ _))
        (Ideal.pow_le_pow_right (by omega))
    · simp only [Finset.mem_Icc]
      omega

/-- p. 185, the claim: "if `λ ∈ P` then we must have `λ ∈ 𝔪^{q+1}` because the generators
`x₁, …, x_r` of `F` form a regular system of parameters of `Ō_{m̄}`. ... By the same reason, we
must have `λ ∈ Σ PˢFᵗ + F^{q+2}`. Repeating this argument, we have `λ ∈ Σ_{(q=s+t, s>0)} PˢFᵗ +
F^{q+m}` for all positive integer `m`. Hence `λ ∈ Σ_{(q=s+t, s>0)} PˢFᵗ`": the hypothesis `hFP`
is "`λ ∈ F^q ∩ P` implies `λ ∈ 𝔪^{q+1}`", and the last step is Krull's intersection theorem
(implicit in the paper). -/
private theorem mem_mixedIdeal_of_mem_inf [IsLocalRing O] [IsNoetherianRing O] (P F : Ideal O)
    (hF : F ≠ ⊤) (hFP : ∀ q, F ^ q ⊓ P ≤ (P ⊔ F) ^ (q + 1)) {q : ℕ} (hq : 1 ≤ q) {l : O}
    (hl : l ∈ F ^ q ⊓ P) : l ∈ mixedIdeal P F q := by
  set N := mixedIdeal P F q with hN
  have iter : ∀ k, l ∈ N ⊔ F ^ (q + k) := by
    intro k
    induction k with
    | zero => exact Ideal.mem_sup_right hl.1
    | succ k ih =>
      obtain ⟨a, ha, w, hw, rfl⟩ := Submodule.mem_sup.mp ih
      have hwP : w ∈ P := by
        have := sub_mem hl.2 (mixedIdeal_le P F q ha)
        rwa [add_sub_cancel_left] at this
      have h1 := pow_succ_le_mixedIdeal_sup P F hq (Nat.le_add_right q k)
        (hFP (q + k) ⟨hw, hwP⟩)
      obtain ⟨a', ha', w', hw', rfl⟩ := Submodule.mem_sup.mp h1
      exact Submodule.mem_sup.mpr ⟨a + a', add_mem ha ha', w', hw', by ring⟩
  have hK := Ideal.iInf_pow_smul_eq_bot_of_isLocalRing F (M := O ⧸ N) hF
  have hmem : Ideal.Quotient.mk N l ∈ (⨅ i : ℕ, F ^ i • ⊤ : Submodule O (O ⧸ N)) := by
    refine (Submodule.mem_iInf _).mpr fun k => ?_
    obtain ⟨a, ha, c, hc, hbeq⟩ := Submodule.mem_sup.mp (iter k)
    have hc' : c ∈ F ^ k := Ideal.pow_le_pow_right (Nat.le_add_left k q) hc
    have h₁ : Ideal.Quotient.mk N l = Ideal.Quotient.mk N c :=
      Ideal.Quotient.eq.mpr (by rw [← hbeq, add_sub_cancel_right]; exact ha)
    have h₂ : Ideal.Quotient.mk N c = c • (1 : O ⧸ N) := Algebra.algebraMap_eq_smul_one c
    rw [h₁, h₂]
    exact Submodule.smul_mem_smul hc' Submodule.mem_top
  rw [hK] at hmem
  exact Ideal.Quotient.eq_zero_iff_mem.mp ((Submodule.mem_bot O).mp hmem)

end Prop1Core
section Prop1CoreMain

/-- **The kernel step of the proof of Proposition 1 (pp. 184--185)**, in ring-theoretic terms:
`Σ_{p+q=n} Σ_i f_i^{(p)} ⊗ g_i^{(q)}` is an element `h` of the kernel of `ν` (`h̃ = Σ f g ∈ 𝔪^{n+1}`)
whose coefficients satisfy "for every `(q, i)` either `g_i^{(q)} = 0` or `g_i^{(q)} ∉ 𝔪^{q+1}`";
the conclusion is that all `g_i^{(q)} = 0` (so that `μ(h) = 0`).  The proof is the printed one:
the maximal integer `p₁` with `h̃ ∈ Σ_{(p+q'=n+1, p≥p₁)} Pᵖ F^{q'}` (`p₁`), the representation
`h̃ = Σ f_i^{(p)} λ_i^{(q')}` with `λ ∈ F^{q'}`, the claim that some `λ_i^{(q'₁)} ∉ P`
(`mem_mixedIdeal_of_mem_inf`), and the smallest integer `δ` such that one of the `λ_i^{(n-δ+1)}`
and `g_i^{(n-δ)}` is not zero.

Hypotheses: `m = P + F`; `(f_i^{(p)})_i` generate `Pᵖ` and their classes are linearly independent
in `Pᵖ/Pᵖ⁺¹` over `Ō` (`hfind`: a relation `Σ c_i f_i ∈ Pᵖ⁺¹` has all `c_i ∈ P`); `hFP` is
"if `λ ∈ F^q` and `λ ∈ P` then `λ ∈ 𝔪^{q+1}`" (the generators of `F` form a regular system of
parameters of `Ō_{m̄}`). -/
theorem coeff_eq_zero_of_sum_mem_pow_succ [IsLocalRing O] [IsNoetherianRing O] (P F m : Ideal O)
    (hm : m = P ⊔ F) (hF : F ≠ ⊤) (hFP : ∀ q, F ^ q ⊓ P ≤ m ^ (q + 1))
    {ι : ℕ → Type*} [∀ p, Fintype (ι p)] (f : ∀ p, ι p → O) (hfP : ∀ p i, f p i ∈ P ^ p)
    (hfspan : ∀ p, P ^ p = Ideal.span (Set.range (f p)))
    (hfind : ∀ p (c : ι p → O), ∑ i, c i * f p i ∈ P ^ (p + 1) → ∀ i, c i ∈ P)
    (n : ℕ) (g : ∀ p, ι p → O) (hgF : ∀ p, p ≤ n → ∀ i, g p i ∈ F ^ (n - p))
    (hgm : ∀ p, p ≤ n → ∀ i, g p i = 0 ∨ g p i ∉ m ^ (n - p + 1))
    (hsum : ∑ p ∈ Finset.range (n + 1), ∑ i, f p i * g p i ∈ m ^ (n + 1)) :
    ∀ p, p ≤ n → ∀ i, g p i = 0 := by
  classical
  subst hm
  by_contra hcon
  push Not at hcon
  obtain ⟨p₀, hp₀, i₀, hgi₀⟩ := hcon
  -- `h̃ = Σ_{p+q=n} Σ_i f_i^{(p)} g_i^{(q)}` lies in `𝔪^{n+1} = (P, F)^{n+1}`
  set hs := ∑ p ∈ Finset.range (n + 1), ∑ i, f p i * g p i with hhs
  let S : ℕ → Ideal O := fun j => ∑ p ∈ Finset.Ico j (n + 2), P ^ p * F ^ (n + 1 - p)
  have hS0 : hs ∈ S 0 := by
    have := sup_pow_le_sum P F (n + 1) hsum
    rwa [Finset.range_eq_Ico] at this
  -- "Let us take the maximal integer `p₁` such that `h̃ ∈ Σ_{(p+q'=n+1, p≥p₁)} Pᵖ F^{q'}`"
  let p₁ := Nat.findGreatest (fun j => hs ∈ S j) (n + 1)
  have hp₁S : hs ∈ S p₁ :=
    Nat.findGreatest_spec (P := fun j => hs ∈ S j) (Nat.zero_le (n + 1)) hS0
  have hp₁le : p₁ ≤ n + 1 := Nat.findGreatest_le _
  have hmax : ∀ k, p₁ < k → k ≤ n + 1 → hs ∉ S k := fun k h1 h2 =>
    Nat.findGreatest_is_greatest h1 h2
  -- "and write `h̃ = Σ_{(p+q'=n+1, p≥p₁)} (Σ_i f_i^{(p)} λ_i^{(q')})` with `λ_i^{(q')} ∈ F^{q'}`"
  have rep : ∀ (j : ℕ) (x : O), x ∈ S j → ∃ l : ∀ p, ι p → O,
      (∀ p i, l p i ∈ F ^ (n + 1 - p)) ∧ (∀ p, p < j → ∀ i, l p i = 0) ∧
        x = ∑ p ∈ Finset.Ico j (n + 2), ∑ i, f p i * l p i := by
    intro j x hx
    obtain ⟨u, hu, rfl⟩ := exists_eq_sum_of_mem_sum _ _ hx
    have hl : ∀ p, ∃ c : ι p → O, p ∈ Finset.Ico j (n + 2) →
        (∀ i, c i ∈ F ^ (n + 1 - p)) ∧ u p = ∑ i, f p i * c i := by
      intro p
      by_cases hp : p ∈ Finset.Ico j (n + 2)
      · obtain ⟨c, hc, hu'⟩ := exists_eq_sum_mul_of_mem_mul (f p) (F ^ (n + 1 - p))
          (by rw [← hfspan p]; exact hu p hp)
        exact ⟨c, fun _ => ⟨hc, hu'⟩⟩
      · exact ⟨0, fun h => absurd h hp⟩
    choose c hc using hl
    refine ⟨fun p i => if p ∈ Finset.Ico j (n + 2) then c p i else 0, fun p i => ?_,
      fun p hp i => ?_, ?_⟩
    · by_cases hpm : p ∈ Finset.Ico j (n + 2)
      · simpa only [hpm, ↓reduceIte] using (hc p hpm).1 i
      · simp only [hpm, ↓reduceIte]
        exact zero_mem _
    · have : p ∉ Finset.Ico j (n + 2) := fun h => absurd (Finset.mem_Ico.mp h).1 (by omega)
      simp only [this, ↓reduceIte]
    · refine Finset.sum_congr rfl fun p hp => ?_
      simp only [hp, ↓reduceIte]
      exact (hc p hp).2
  obtain ⟨l, hlF, hl0, hhs_eq⟩ := rep p₁ hs hp₁S
  -- "We claim that there exists at least one `i` such that `λ_i^{(q'₁)} ∉ P`, where
  -- `q'₁ = n - p₁ + 1`, unless `p₁ = n + 1`."
  have claim : p₁ ≤ n → ∃ i, l p₁ i ∉ P := by
    intro hp₁n
    by_contra hall
    push Not at hall
    refine hmax (p₁ + 1) (Nat.lt_succ_self _) (by omega) ?_
    rw [hhs_eq, Finset.sum_eq_sum_Ico_succ_bot (by omega : p₁ < n + 2)]
    refine add_mem (Ideal.sum_mem _ fun i _ => ?_) (Ideal.sum_mem _ fun p hp =>
      Ideal.sum_mem _ fun i _ => ?_)
    · -- "Hence `λ ∈ Σ_{(q'₁=s+t, s>0)} PˢFᵗ`, and `f_i^{(p₁)} λ_i^{(q'₁)} ∈ Σ_{p≥p₁+1} Pᵖ F^{q'}`"
      have hN := mem_mixedIdeal_of_mem_inf P F hF hFP (q := n + 1 - p₁) (by omega)
        ⟨hlF p₁ i, hall i⟩
      obtain ⟨v, hv, hvsum⟩ := exists_eq_sum_of_mem_sum _ _ hN
      rw [← hvsum, Finset.mul_sum]
      refine Ideal.sum_mem _ fun s hs' => ?_
      have hs'' := Finset.mem_Icc.mp hs'
      have hmem : f p₁ i * v s ∈ P ^ (p₁ + s) * F ^ (n + 1 - (p₁ + s)) := by
        have h1 := Ideal.mul_mem_mul (hfP p₁ i) (hv s hs')
        rw [← mul_assoc, ← pow_add] at h1
        rwa [show n + 1 - (p₁ + s) = n + 1 - p₁ - s by omega]
      exact le_sum_of_mem (fun p => P ^ p * F ^ (n + 1 - p))
        (s := Finset.Ico (p₁ + 1) (n + 2)) (a := p₁ + s)
        (by simp only [Finset.mem_Ico]; omega) hmem
    · exact le_sum_of_mem (fun p => P ^ p * F ^ (n + 1 - p))
        (s := Finset.Ico (p₁ + 1) (n + 2)) (a := p) hp
        (Ideal.mul_mem_mul (hfP p i) (hlF p i))
  -- "Now let `δ` be the smallest integer such that one of the `λ_i^{(n-δ+1)}` and
  -- `g_i^{(n-δ)}` is not zero."
  let D : ℕ → Prop := fun p => (∃ i, l p i ≠ 0) ∨ (p ≤ n ∧ ∃ i, g p i ≠ 0)
  have hD₀ : D p₀ := Or.inr ⟨hp₀, i₀, hgi₀⟩
  let δ := Nat.find (⟨p₀, hD₀⟩ : ∃ p, D p)
  have hδD : D δ := Nat.find_spec (⟨p₀, hD₀⟩ : ∃ p, D p)
  have hδmin : ∀ p, p < δ → ¬ D p := fun p hp => Nat.find_min (⟨p₀, hD₀⟩ : ∃ p, D p) hp
  have hδle : δ ≤ p₀ := Nat.find_min' (⟨p₀, hD₀⟩ : ∃ p, D p) hD₀
  have hδn : δ ≤ n := hδle.trans hp₀
  -- "Then we should have `Σ_i f^{(δ)} g_i^{(n-δ)} ≡ Σ_i f_i^{(δ)} λ_i^{(n-δ+1)} mod P^{δ+1}`"
  let T : ℕ → O := fun p => ∑ i, f p i * ((if p ≤ n then g p i else 0) - l p i)
  have hTP : ∀ p, T p ∈ P ^ p := fun p =>
    Ideal.sum_mem _ fun i _ => Ideal.mul_mem_right _ _ (hfP p i)
  have hT0 : ∀ p, p < δ → T p = 0 := by
    intro p hp
    have hnD := hδmin p hp
    simp only [D, not_or, not_exists, not_not, not_and] at hnD
    refine Finset.sum_eq_zero fun i _ => ?_
    have h1 : l p i = 0 := hnD.1 i
    by_cases hpn : p ≤ n
    · simp [hpn, h1, hnD.2 hpn i]
    · simp [hpn, h1]
  have hTsum : ∑ p ∈ Finset.range (n + 2), T p = 0 := by
    have hA : ∑ p ∈ Finset.range (n + 2), ∑ i, f p i * (if p ≤ n then g p i else 0) = hs := by
      rw [Finset.sum_range_succ, hhs]
      simp only [show ¬ (n + 1 ≤ n) by omega, ↓reduceIte, mul_zero, Finset.sum_const_zero,
        add_zero]
      refine Finset.sum_congr rfl fun p hp => ?_
      have : p ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hp)
      simp only [this, ↓reduceIte]
    have hB : ∑ p ∈ Finset.range (n + 2), ∑ i, f p i * l p i = hs := by
      rw [Finset.range_eq_Ico, ← Finset.sum_Ico_consecutive _ (Nat.zero_le p₁) (by omega : p₁ ≤ n + 2),
        Finset.sum_eq_zero (s := Finset.Ico 0 p₁) (fun p hp => Finset.sum_eq_zero fun i _ => by
          rw [hl0 p (Finset.mem_Ico.mp hp).2 i, mul_zero]), zero_add, ← hhs_eq]
    simp only [T, mul_sub, Finset.sum_sub_distrib]
    rw [hA, hB, sub_self]
  have hTδ : T δ ∈ P ^ (δ + 1) := by
    have h1 := Finset.add_sum_erase (Finset.range (n + 2)) T
      (Finset.mem_range.mpr (by omega : δ < n + 2))
    rw [hTsum] at h1
    have h2 : T δ = -∑ p ∈ (Finset.range (n + 2)).erase δ, T p := eq_neg_of_add_eq_zero_left h1
    rw [h2]
    refine neg_mem (Ideal.sum_mem _ fun p hp => ?_)
    have hpδ : p ≠ δ := (Finset.mem_erase.mp hp).1
    rcases lt_or_gt_of_ne hpδ with hlt | hgt
    · rw [hT0 p hlt]
      exact zero_mem _
    · exact Ideal.pow_le_pow_right (Nat.succ_le_of_lt hgt) (hTP p)
  -- "Since `(f_i^{(δ)})` form a free base of the `Ō`-module `Pδ/Pδ+1`, `g_i^{(n-δ)} ≡ λ_i^{(n-δ+1)}
  -- mod P`, for all `i`."
  have hcP : ∀ i, g δ i - l δ i ∈ P := by
    refine hfind δ (fun i => g δ i - l δ i) ?_
    have : ∑ i, (g δ i - l δ i) * f δ i = T δ := by
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [hδn, ↓reduceIte]
      ring
    rw [this]
    exact hTδ
  -- "Since `g_i^{(n-δ)} ∈ F^{n-δ}` and `λ_i^{(n-δ+1)} ∈ F^{n-δ+1}`, the assumption on the
  -- `g_i^{(q)}` implies that `g_i^{(n-δ)} = 0` for all `i`"
  have hgδ : ∀ i, g δ i = 0 := by
    intro i
    have hl' : l δ i ∈ F ^ (n - δ + 1) := by
      have := hlF δ i
      rwa [show n + 1 - δ = n - δ + 1 by omega] at this
    have hc : g δ i - l δ i ∈ (P ⊔ F) ^ (n - δ + 1) :=
      hFP (n - δ) ⟨sub_mem (hgF δ hδn i) (Ideal.pow_le_pow_right (by omega) hl'), hcP i⟩
    have hmem : g δ i ∈ (P ⊔ F) ^ (n - δ + 1) := by
      have := add_mem hc (Ideal.pow_right_mono le_sup_right (n - δ + 1) hl')
      rwa [sub_add_cancel] at this
    exact (hgm δ hδn i).resolve_right (fun h => h hmem)
  -- "so that `δ = p₁` and `λ_i^{(n-δ+1)} ∈ P` for all `i`."
  have hlP : ∀ i, l δ i ∈ P := fun i => by
    have := neg_mem (hcP i)
    rwa [hgδ i, zero_sub, neg_neg] at this
  have hlδ : ∃ i, l δ i ≠ 0 := by
    rcases hδD with h | ⟨-, i, hi⟩
    · exact h
    · exact absurd (hgδ i) hi
  have hp₁δ : p₁ ≤ δ := by
    by_contra hlt
    obtain ⟨i, hi⟩ := hlδ
    exact hi (hl0 δ (not_le.mp hlt) i)
  obtain ⟨i₁, hi₁⟩ := claim (hp₁δ.trans hδn)
  have hD₁ : D p₁ := Or.inl ⟨i₁, fun h => hi₁ (h ▸ zero_mem _)⟩
  have hδp₁ : δ ≤ p₁ := Nat.find_min' (⟨p₀, hD₀⟩ : ∃ p, D p) hD₁
  have hδeq : δ = p₁ := le_antisymm hδp₁ hp₁δ
  exact hi₁ ((fun k (hk : k = p₁) => by subst hk; exact id :
    ∀ k, k = p₁ → (∀ i : ι k, l k i ∈ P) → ∀ i : ι p₁, l p₁ i ∈ P) δ hδeq hlP i₁)

end Prop1CoreMain
section Prop1Bridge

variable (P m : Ideal O) (hPm : P ≤ m) {s : ℕ} (y : Fin s → O)
  (hqr : IsQuasiRegular fun j => Ideal.Quotient.mk P (y j))
  (hz : Ideal.span (Set.range fun j => Ideal.Quotient.mk P (y j)) =
    m.map (Ideal.Quotient.mk P))

include hPm hz in
/-- The map `F^q → gr^q_{m̄}(Ō)` of the commutative diagram of p. 184 (the right-hand column):
`F^q ⊆ 𝔪^q → (F^q + P)/P = m̄^q → gr^q_{m̄}(Ō)`, `b ↦` the class of `b̄`. -/
noncomputable def toGrBar (q : ℕ) (b : ↥(Ideal.span (Set.range y) ^ q)) :
    GrPiece (m.map (Ideal.Quotient.mk P)) q :=
  Submodule.Quotient.mk ⟨Ideal.Quotient.mk P b.1, by
    have := Ideal.pow_right_mono (span_range_le_of_span_map_eq P m hPm y hz) q b.2
    rw [← Ideal.map_pow]
    exact Ideal.mem_map_of_mem _ this⟩

include hPm hz in
theorem toGrBar_add (q : ℕ) (b b' : ↥(Ideal.span (Set.range y) ^ q)) :
    toGrBar P m hPm y hz q (b + b') = toGrBar P m hPm y hz q b + toGrBar P m hPm y hz q b' :=
  rfl

include hPm hz in
theorem toGrBar_zero_of_mem (q : ℕ) (b : ↥(Ideal.span (Set.range y) ^ q))
    (hb : b.1 ∈ m ^ (q + 1)) : toGrBar P m hPm y hz q b = 0 := by
  unfold toGrBar
  rw [Submodule.Quotient.mk_eq_zero, Submodule.mem_comap, Submodule.subtype_apply]
  show Ideal.Quotient.mk P b.1 ∈ (m.map (Ideal.Quotient.mk P)) ^ (q + 1)
  rw [← Ideal.map_pow]
  exact Ideal.mem_map_of_mem _ hb

include hPm hqr hz in
/-- The commutative diagram of p. 184 (the square `F^q → m̄^q → gr^q_{m̄}(Ō) → gr^q_𝔪(O)`):
`β*` maps the class of `b̄` in `gr^q_{m̄}(Ō)` to the class of `b ∈ F^q ⊆ 𝔪^q` in `gr^q_𝔪(O)`. -/
theorem betaStarPiece_toGrBar (q : ℕ) (b : ↥(Ideal.span (Set.range y) ^ q))
    (hbm : b.1 ∈ m ^ q) :
    betaStarPiece P m hPm y hqr hz q (toGrBar P m hPm y hz q b) =
      Submodule.Quotient.mk ⟨b.1, hbm⟩ := by
  classical
  have hD : ∀ q α, α ∈ degreeFinset s q ↔ α.degree = q := fun _ _ => mem_degreeFinset
  obtain ⟨c, -, hc⟩ := exists_eq_sum_mono_of_mem y (degreeFinset s) hD ⊤ q
    (by rw [Ideal.top_mul]; exact b.2 : b.1 ∈ ⊤ * Ideal.span (Set.range y) ^ q)
  have hsm : ∀ (r : O) (x : GrPiece (m.map (Ideal.Quotient.mk P)) q),
      (Ideal.Quotient.mk m r) • x = (Ideal.Quotient.mk P r) • x := fun _ _ => rfl
  have hmem : ∀ α : ↥(degreeFinset s q),
      (α.1.prod fun j e => (Ideal.Quotient.mk P (y j)) ^ e) ∈
        (m.map (Ideal.Quotient.mk P)) ^ q := fun α => by
    have := mono_mem_span_pow (fun j => Ideal.Quotient.mk P (y j)) α.1
    rwa [(hD q α.1).mp α.2, hz] at this
  have hbα : ∀ α : ↥(degreeFinset s q), psiBasis P m hPm y hqr hz q α =
      Submodule.Quotient.mk ⟨α.1.prod fun j e => (Ideal.Quotient.mk P (y j)) ^ e, hmem α⟩ :=
    fun α => grPieceMapBasis_apply P m hPm _ hqr hz (degreeFinset s) (fun _ _ => mem_degreeFinset)
      q α (hmem α)
  -- `b̄ = Σ_α c̄_α x̄^α`, i.e. the class of `b̄` is `Σ_α c̄_α • [x̄^α]`
  have h2 : toGrBar P m hPm y hz q b = ∑ α : ↥(degreeFinset s q), (Ideal.Quotient.mk m (c α.1)) •
      psiBasis P m hPm y hqr hz q α := by
    simp only [hbα, hsm, ← Submodule.Quotient.mk_smul]
    unfold toGrBar
    rw [quotient_mk_sum]
    congr 1
    apply Subtype.ext
    simp only [Submodule.coe_sum, Submodule.coe_smul, smul_eq_mul]
    rw [hc, map_sum, ← Finset.sum_coe_sort (degreeFinset s q)]
    refine Finset.sum_congr rfl fun α _ => ?_
    rw [map_mul, map_finsuppProd]
    simp only [map_pow]
  rw [h2, map_sum]
  simp only [map_smul]
  have hβ : ∀ α : ↥(degreeFinset s q), betaStarPiece P m hPm y hqr hz q
      (psiBasis P m hPm y hqr hz q α) = Submodule.Quotient.mk ⟨_, prod_pow_mem_pow_of_span_le m y
        (span_range_le_of_span_map_eq P m hPm y hz) q α.1 (mem_degreeFinset.mp α.2)⟩ := fun α => by
    unfold betaStarPiece
    rw [Module.Basis.constr_basis]
  have hsm' : ∀ (r : O) (x : GrPiece m q), (Ideal.Quotient.mk m r) • x = r • x := fun _ _ => rfl
  simp only [hβ, hsm', ← Submodule.Quotient.mk_smul]
  rw [quotient_mk_sum]
  congr 1
  apply Subtype.ext
  simp only [Submodule.coe_sum, Submodule.coe_smul, smul_eq_mul]
  rw [hc, ← Finset.sum_coe_sort (degreeFinset s q)]

/-- The summands `Pᵖ ⊗_O F^q`, `p + q = n`, of the source of the maps `ν` and `μ` of p. 184. -/
abbrev NuSummand (P F : Ideal O) (n : ℕ) : {pq : ℕ × ℕ // pq.1 + pq.2 = n} → Type u :=
  fun pq => ↥(P ^ pq.1.1) ⊗[O] ↥(F ^ pq.1.2)

include hPm hz in
theorem mul_mem_pow_of_mem_pow (n : ℕ) (pq : {pq : ℕ × ℕ // pq.1 + pq.2 = n})
    (a : ↥(P ^ pq.1.1)) (b : ↥(Ideal.span (Set.range y) ^ pq.1.2)) : a.1 * b.1 ∈ m ^ n := by
  have h := Ideal.mul_mem_mul (Ideal.pow_right_mono hPm _ a.2)
    (Ideal.pow_right_mono (span_range_le_of_span_map_eq P m hPm y hz) _ b.2)
  rw [← pow_add, pq.2] at h
  exact h

include hPm hz in
/-- The bi-additive map `(a, b) ↦ [a b]`, `Pᵖ × F^q → grⁿ_𝔪(O)`, `p + q = n`, behind `ν`. -/
noncomputable def nuBilin (n : ℕ) (pq : {pq : ℕ × ℕ // pq.1 + pq.2 = n}) :
    ↥(P ^ pq.1.1) →+ ↥(Ideal.span (Set.range y) ^ pq.1.2) →+ GrPiece m n :=
  AddMonoidHom.mk' (fun a => AddMonoidHom.mk'
    (fun b => Submodule.Quotient.mk ⟨a.1 * b.1, mul_mem_pow_of_mem_pow P m hPm y hz n pq a b⟩)
    (fun b b' => by
      rw [← Submodule.Quotient.mk_add]
      exact congrArg _ (Subtype.ext (mul_add _ _ _))))
    (fun a a' => AddMonoidHom.ext fun b => by
      show (Submodule.Quotient.mk _ : GrPiece m n) = Submodule.Quotient.mk _ + Submodule.Quotient.mk _
      rw [← Submodule.Quotient.mk_add]
      exact congrArg _ (Subtype.ext (add_mul _ _ _)))

include hPm hz in
/-- The map `ν` of p. 184 in degree `p + q = n`: `Pᵖ ⊗_O F^q → grⁿ_𝔪(O)`, `a ⊗ b ↦ [a b]`. -/
noncomputable def nuPiece (n : ℕ) (pq : {pq : ℕ × ℕ // pq.1 + pq.2 = n}) :
    NuSummand P (Ideal.span (Set.range y)) n pq →+ GrPiece m n :=
  TensorProduct.liftAddHom (nuBilin P m hPm y hz n pq) (fun r a b => by
    show (Submodule.Quotient.mk _ : GrPiece m n) = Submodule.Quotient.mk _
    exact congrArg _ (Subtype.ext (by simp only [Submodule.coe_smul, smul_eq_mul]; ring)))

include hPm hz in
/-- The map `ν` of p. 184, "obtained by first sending `Σ_{p+q=n} Pᵖ ⊗_O F^q` into `𝔪ⁿ`":
`⊕_{p+q=n} Pᵖ ⊗_O F^q → grⁿ_𝔪(O)`. -/
noncomputable def nuDeg (n : ℕ) :
    (⨁ pq : {pq : ℕ × ℕ // pq.1 + pq.2 = n}, NuSummand P (Ideal.span (Set.range y)) n pq) →+
      GrPiece m n :=
  DirectSum.toAddMonoid (nuPiece P m hPm y hz n)

include hPm hz in
/-- The additive map `b ↦ [a] ⊗ [b̄]`, `F^q → gr⁰_{m̄}(grᵖ_P(O)) ⊗_K gr^q_{m̄}(Ō)`, for fixed `a`. -/
noncomputable def muBilinFun (n : ℕ) (pq : {pq : ℕ × ℕ // pq.1 + pq.2 = n})
    (a : ↥(P ^ pq.1.1)) : ↥(Ideal.span (Set.range y) ^ pq.1.2) →+ PsiSummand P m n pq :=
  AddMonoidHom.mk'
    (fun b => zeroPieceMk P m pq.1.1 a.1 a.2 ⊗ₜ[O ⧸ m] toGrBar P m hPm y hz pq.1.2 b)
    (fun b b' => by rw [toGrBar_add, TensorProduct.tmul_add])

include hPm hz in
/-- The bi-additive map `(a, b) ↦ [a] ⊗ [b̄]`, `Pᵖ × F^q → gr⁰_{m̄}(grᵖ_P(O)) ⊗_K gr^q_{m̄}(Ō)`. -/
noncomputable def muBilin (n : ℕ) (pq : {pq : ℕ × ℕ // pq.1 + pq.2 = n}) :
    ↥(P ^ pq.1.1) →+ ↥(Ideal.span (Set.range y) ^ pq.1.2) →+ PsiSummand P m n pq :=
  AddMonoidHom.mk' (muBilinFun P m hPm y hz n pq) (fun a a' => AddMonoidHom.ext fun b => by
    refine (congrArg (fun t => t ⊗ₜ[O ⧸ m] toGrBar P m hPm y hz pq.1.2 b)
      (zeroPieceMk_add P m pq.1.1 a.1 a'.1 a.2 a'.2)).trans (TensorProduct.add_tmul _ _ _))

include hPm hz in
/-- The map `μ` of p. 184 in degree `p + q = n`:
`Pᵖ ⊗_O F^q → gr⁰_{m̄}(grᵖ_P(O)) ⊗_K gr^q_{m̄}(Ō)`, `a ⊗ b ↦ [a] ⊗ [b̄]`. -/
noncomputable def muPiece (n : ℕ) (pq : {pq : ℕ × ℕ // pq.1 + pq.2 = n}) :
    NuSummand P (Ideal.span (Set.range y)) n pq →+ PsiSummand P m n pq :=
  TensorProduct.liftAddHom (muBilin P m hPm y hz n pq) (fun r a b => by
    show zeroPieceMk P m pq.1.1 (r • a).1 _ ⊗ₜ[O ⧸ m] toGrBar P m hPm y hz pq.1.2 b =
      zeroPieceMk P m pq.1.1 a.1 a.2 ⊗ₜ[O ⧸ m] toGrBar P m hPm y hz pq.1.2 (r • b)
    have h1 : zeroPieceMk P m pq.1.1 (r • a).1 (r • a).2 =
        (Ideal.Quotient.mk m r) • zeroPieceMk P m pq.1.1 a.1 a.2 := rfl
    have h2 : toGrBar P m hPm y hz pq.1.2 (r • b) =
        (Ideal.Quotient.mk m r) • toGrBar P m hPm y hz pq.1.2 b := rfl
    rw [h1, h2, TensorProduct.smul_tmul])

include hPm hz in
/-- The map `μ` of p. 184: `⊕_{p+q=n} Pᵖ ⊗_O F^q → ⊕_{p+q=n} gr⁰_{m̄}(grᵖ_P(O)) ⊗_K gr^q_{m̄}(Ō)`. -/
noncomputable def muDeg (n : ℕ) :
    (⨁ pq : {pq : ℕ × ℕ // pq.1 + pq.2 = n}, NuSummand P (Ideal.span (Set.range y)) n pq) →+
      ⨁ pq : {pq : ℕ × ℕ // pq.1 + pq.2 = n}, PsiSummand P m n pq :=
  DirectSum.map (muPiece P m hPm y hz n)

include hPm hz in
theorem nuPiece_tmul (n : ℕ) (pq : {pq : ℕ × ℕ // pq.1 + pq.2 = n}) (a : ↥(P ^ pq.1.1))
    (b : ↥(Ideal.span (Set.range y) ^ pq.1.2)) :
    nuPiece P m hPm y hz n pq (a ⊗ₜ[O] b) =
      Submodule.Quotient.mk ⟨a.1 * b.1, mul_mem_pow_of_mem_pow P m hPm y hz n pq a b⟩ :=
  rfl

include hPm hz in
theorem nuDeg_of (n : ℕ) (pq : {pq : ℕ × ℕ // pq.1 + pq.2 = n})
    (x : NuSummand P (Ideal.span (Set.range y)) n pq) :
    nuDeg P m hPm y hz n (DirectSum.of (NuSummand P (Ideal.span (Set.range y)) n) pq x) =
      nuPiece P m hPm y hz n pq x :=
  DirectSum.toAddMonoid_of _ _ _

include hPm hz in
theorem muPiece_tmul (n : ℕ) (pq : {pq : ℕ × ℕ // pq.1 + pq.2 = n}) (a : ↥(P ^ pq.1.1))
    (b : ↥(Ideal.span (Set.range y) ^ pq.1.2)) :
    muPiece P m hPm y hz n pq (a ⊗ₜ[O] b) =
      zeroPieceMk P m pq.1.1 a.1 a.2 ⊗ₜ[O ⧸ m] toGrBar P m hPm y hz pq.1.2 b :=
  rfl

include hPm hz in
theorem muDeg_of (n : ℕ) (pq : {pq : ℕ × ℕ // pq.1 + pq.2 = n})
    (x : NuSummand P (Ideal.span (Set.range y)) n pq) :
    muDeg P m hPm y hz n (DirectSum.of (NuSummand P (Ideal.span (Set.range y)) n) pq x) =
      DirectSum.of (PsiSummand P m n) pq (muPiece P m hPm y hz n pq x) :=
  DirectSum.map_of _ _ _

include hPm hqr hz in
/-- The commutative triangle `ψ ∘ μ = ν` of p. 184, on the component `Pᵖ ⊗_O F^q`. -/
theorem psiSummandMap_muPiece (n : ℕ) (pq : {pq : ℕ × ℕ // pq.1 + pq.2 = n})
    (x : NuSummand P (Ideal.span (Set.range y)) n pq) :
    psiSummandMap P m hPm y hqr hz n pq (muPiece P m hPm y hz n pq x) =
      nuPiece P m hPm y hz n pq x := by
  induction x using TensorProduct.inductionOn with
  | tmul a b =>
    have hbm : b.1 ∈ m ^ pq.1.2 :=
      Ideal.pow_right_mono (span_range_le_of_span_map_eq P m hPm y hz) _ b.2
    have h1 : psiPiece P m hPm y hqr hz pq.1.1 pq.1.2 (zeroPieceMk P m pq.1.1 a.1 a.2 ⊗ₜ[O ⧸ m]
        toGrBar P m hPm y hz pq.1.2 b) =
        Submodule.Quotient.mk ⟨a.1 * b.1, by
          rw [pow_add]; exact Ideal.mul_mem_mul (Ideal.pow_right_mono hPm _ a.2) hbm⟩ := by
      unfold psiPiece
      rw [TensorProduct.lift.tmul, LinearMap.compl₁₂_apply, zeroPieceMk, alphaPiece_mk,
        grPieceInclusion_mk, betaStarPiece_toGrBar P m hPm y hqr hz _ b hbm]
      rfl
    show GrPiece.castDeg m pq.2 (psiPiece P m hPm y hqr hz pq.1.1 pq.1.2
      (zeroPieceMk P m pq.1.1 a.1 a.2 ⊗ₜ[O ⧸ m] toGrBar P m hPm y hz pq.1.2 b)) =
        Submodule.Quotient.mk ⟨a.1 * b.1, mul_mem_pow_of_mem_pow P m hPm y hz n pq a b⟩
    rw [h1]
    exact GrPiece.castDeg_mk m pq.2 _ _ _
  | add x x' hx hx' => simp only [map_add, hx, hx']

include hPm hqr hz in
/-- `ψ ∘ μ = ν` (p. 184), in total degree `n`. -/
theorem psiDeg_muDeg (n : ℕ)
    (x : ⨁ pq : {pq : ℕ × ℕ // pq.1 + pq.2 = n}, NuSummand P (Ideal.span (Set.range y)) n pq) :
    psiDeg P m hPm y hqr hz n (muDeg P m hPm y hz n x) = nuDeg P m hPm y hz n x := by
  induction x using DirectSum.induction_on with
  | zero => simp only [map_zero]
  | of pq a =>
    rw [muDeg_of, nuDeg_of, ← DirectSum.lof_eq_of (O ⧸ m), psiDeg_lof]
    exact psiSummandMap_muPiece P m hPm y hqr hz n pq a
  | add x x' hx hx' => simp only [map_add, hx, hx']

include hz in
theorem map_span_range_eq : (Ideal.span (Set.range y)).map (Ideal.Quotient.mk P) =
    m.map (Ideal.Quotient.mk P) := by
  rw [Ideal.map_span, ← Set.range_comp, ← hz]
  rfl

include hPm hz in
/-- "As is easily seen, `μ` is surjective" (p. 184), on each component `Pᵖ ⊗_O F^q`: the module
`gr⁰_{m̄}(grᵖ_P(O)) ⊗_K gr^q_{m̄}(Ō)` is generated by the elements `[a] ⊗ [b̄]`, `a ∈ Pᵖ`,
`b ∈ F^q` (as `m̄^q = (F^q + P)/P`). -/
theorem muPiece_surjective (n : ℕ) (pq : {pq : ℕ × ℕ // pq.1 + pq.2 = n}) :
    Function.Surjective (muPiece P m hPm y hz n pq) := by
  intro v
  induction v using TensorProduct.inductionOn with
  | tmul x w =>
    obtain ⟨a, ha, rfl⟩ := exists_zeroPieceMk_eq P m pq.1.1 x
    induction w using Submodule.Quotient.induction_on with
    | H w =>
      obtain ⟨w₀, hw₀⟩ := w
      have hw₀' : w₀ ∈ (Ideal.span (Set.range y) ^ pq.1.2).map (Ideal.Quotient.mk P) := by
        rw [Ideal.map_pow, map_span_range_eq P m y hz]
        exact hw₀
      obtain ⟨b, hb, rfl⟩ := (Ideal.mem_map_iff_of_surjective _
        Ideal.Quotient.mk_surjective).mp hw₀'
      exact ⟨⟨a, ha⟩ ⊗ₜ[O] ⟨b, hb⟩, muPiece_tmul P m hPm y hz n pq ⟨a, ha⟩ ⟨b, hb⟩⟩
  | add v v' hv hv' =>
    obtain ⟨u, rfl⟩ := hv
    obtain ⟨u', rfl⟩ := hv'
    exact ⟨u + u', map_add _ _ _⟩

include hPm hz in
/-- "As is easily seen, `μ` is surjective" (p. 184). -/
theorem muDeg_surjective (n : ℕ) : Function.Surjective (muDeg P m hPm y hz n) :=
  (DirectSum.map_surjective _).mpr (muPiece_surjective P m hPm y hz n)

include hPm hz in
/-- "As is easily seen, `ν` and `μ` are both surjective" (p. 184), for `ν`: since
`𝔪ⁿ = (P, F)ⁿ = Σ_{p+q=n} Pᵖ F^q` (`m = P + F`), every class of `grⁿ_𝔪(O)` is a sum of classes
`[a b]`, `a ∈ Pᵖ`, `b ∈ F^q`, which are the images of the elements `a ⊗ b`. -/
theorem nuDeg_surjective (hmPY : m = P ⊔ Ideal.span (Set.range y)) (n : ℕ) :
    Function.Surjective (nuDeg P m hPm y hz n) := by
  classical
  let R : AddSubgroup (GrPiece m n) := (nuDeg P m hPm y hz n).range
  let T : AddSubgroup O :=
    { carrier := {x | x ∈ m ^ n ∧ ∀ hx : x ∈ m ^ n, (Submodule.Quotient.mk ⟨x, hx⟩ : GrPiece m n) ∈ R}
      add_mem' := fun {a b} ha hb => ⟨add_mem ha.1 hb.1, fun h => by
        have : (Submodule.Quotient.mk ⟨a + b, h⟩ : GrPiece m n) =
            Submodule.Quotient.mk ⟨a, ha.1⟩ + Submodule.Quotient.mk ⟨b, hb.1⟩ := by
          rw [← Submodule.Quotient.mk_add]
          rfl
        rw [this]
        exact add_mem (ha.2 _) (hb.2 _)⟩
      zero_mem' := ⟨zero_mem _, fun h => by
        have : (Submodule.Quotient.mk ⟨0, h⟩ : GrPiece m n) = 0 := by
          rw [Submodule.Quotient.mk_eq_zero]
          exact zero_mem _
        rw [this]
        exact zero_mem _⟩
      neg_mem' := fun {a} ha => ⟨neg_mem ha.1, fun h => by
        have : (Submodule.Quotient.mk ⟨-a, h⟩ : GrPiece m n) = -Submodule.Quotient.mk ⟨a, ha.1⟩ := by
          rw [← Submodule.Quotient.mk_neg]
          rfl
        rw [this]
        exact neg_mem (ha.2 _)⟩ }
  -- the products `a b ∈ Pᵖ F^q` are in `T`
  have hprod : ∀ p ∈ Finset.range (n + 1), ∀ x ∈ P ^ p * Ideal.span (Set.range y) ^ (n - p),
      x ∈ T := by
    intro p hp x hx
    have hpn : p + (n - p) = n := by have := Finset.mem_range.mp hp; omega
    refine Submodule.mul_induction_on hx (fun a ha b hb => ?_) (fun u v hu hv => add_mem hu hv)
    refine ⟨mul_mem_pow_of_mem_pow P m hPm y hz n ⟨(p, n - p), hpn⟩ ⟨a, ha⟩ ⟨b, hb⟩, fun h => ?_⟩
    exact ⟨DirectSum.of (NuSummand P (Ideal.span (Set.range y)) n) ⟨(p, n - p), hpn⟩
      (⟨a, ha⟩ ⊗ₜ[O] ⟨b, hb⟩), by rw [nuDeg_of]; rfl⟩
  intro w
  induction w using Submodule.Quotient.induction_on with
  | H w =>
    obtain ⟨x, hx⟩ := w
    have hx' := sup_pow_le_sum P (Ideal.span (Set.range y)) n (hmPY ▸ hx)
    obtain ⟨u, hu, rfl⟩ := exists_eq_sum_of_mem_sum _ _ hx'
    exact (AddSubgroup.sum_mem T fun p hp => hprod p hp (u p) (hu p hp)).2 hx

include hPm hqr hz in
/-- `ψ` is surjective in each total degree: since `ψ ∘ μ = ν` (p. 184) and `ν` is surjective
("as is easily seen, `ν` and `μ` are both surjective"). -/
theorem psiDeg_surjective (hmPY : m = P ⊔ Ideal.span (Set.range y)) (n : ℕ) :
    Function.Surjective (psiDeg P m hPm y hqr hz n) := by
  have h : ⇑(psiDeg P m hPm y hqr hz n) ∘ ⇑(muDeg P m hPm y hz n) = ⇑(nuDeg P m hPm y hz n) :=
    funext (psiDeg_muDeg P m hPm y hqr hz n)
  exact Function.Surjective.of_comp (h ▸ nuDeg_surjective P m hPm y hz hmPY n)

/-- "Let us choose a system of elements `(f_i^{(p)})` of `Pᵖ` whose residue classes mod `Pᵖ⁺¹`
form a free base of `Pᵖ/Pᵖ⁺¹` as `Ō`-module. Then it is easy to show that
`Pᵖ = (f₁^{(p)}, f₂^{(p)}, …)O`" (p. 184--185).  (The easy step is Nakayama's lemma, `P ⊆ 𝔪`
for the maximal ideal `𝔪` of the local ring `O`.) -/
theorem pow_eq_span_of_basis [IsLocalRing O] [IsNoetherianRing O] (P : Ideal O) (hP : P ≠ ⊤)
    (p : ℕ) {ι : Type*} [Fintype ι] (e : Module.Basis ι (O ⧸ P) (GrPiece P p))
    (f : ι → ↥(P ^ p)) (hf : ∀ i, Submodule.Quotient.mk (f i) = e i) :
    P ^ p = Ideal.span (Set.range fun i => (f i).1) := by
  classical
  refine le_antisymm ?_ (Ideal.span_le.mpr (by rintro _ ⟨i, rfl⟩; exact (f i).2))
  have hfg : (P ^ p).FG := IsNoetherian.noetherian _
  refine Submodule.le_of_le_smul_of_le_jacobson_bot (I := P) hfg ?_ ?_
  · rw [IsLocalRing.jacobson_eq_maximalIdeal _ bot_ne_top]
    exact IsLocalRing.le_maximalIdeal hP
  · intro a ha
    obtain ⟨c, hc⟩ : ∃ c : ι → O, ∀ i, Ideal.Quotient.mk P (c i) =
        e.repr (Submodule.Quotient.mk ⟨a, ha⟩) i :=
      ⟨fun i => Function.surjInv Ideal.Quotient.mk_surjective _,
        fun i => Function.surjInv_eq Ideal.Quotient.mk_surjective _⟩
    have hv : (Submodule.Quotient.mk ⟨a, ha⟩ : GrPiece P p) =
        ∑ i, (Ideal.Quotient.mk P (c i)) • e i := by
      simp_rw [hc]
      exact (e.sum_repr _).symm
    have hdiff : a - ∑ i, c i * (f i).1 ∈ P ^ (p + 1) := by
      have h1 : (∑ i, (Ideal.Quotient.mk P (c i)) • e i : GrPiece P p) =
          Submodule.Quotient.mk (∑ i, c i • f i) := by
        simp_rw [← hf]
        rw [← quotient_mk_sum]
        exact Finset.sum_congr rfl fun i _ => (Submodule.Quotient.mk_smul _ _ _).symm
      rw [h1, Submodule.Quotient.eq, Submodule.mem_comap] at hv
      have h2 : (⟨a, ha⟩ - ∑ i, c i • f i : ↥(P ^ p)).1 = a - ∑ i, c i * (f i).1 := by
        simp only [Submodule.coe_sub, Submodule.coe_sum, Submodule.coe_smul, smul_eq_mul]
      rw [Submodule.subtype_apply, h2] at hv
      exact hv
    rw [show a = ∑ i, c i * (f i).1 + (a - ∑ i, c i * (f i).1) by ring]
    refine Submodule.add_mem_sup (Ideal.sum_mem _ fun i _ =>
      Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨i, rfl⟩)) ?_
    rw [smul_eq_mul, ← pow_succ']
    exact hdiff

/-- "if `Σ_i c_i f_i^{(δ)} ≡ 0 mod P^{δ+1}`, since the classes of the `f_i^{(δ)}` form a free base of
the `Ō`-module `Pδ/Pδ+1`, all `c_i ∈ P`" (p. 185). -/
theorem coeff_mem_of_sum_mem_pow_succ (P : Ideal O) (p : ℕ) {ι : Type*} [Fintype ι]
    (e : Module.Basis ι (O ⧸ P) (GrPiece P p)) (f : ι → ↥(P ^ p))
    (hf : ∀ i, Submodule.Quotient.mk (f i) = e i) (c : ι → O)
    (h : ∑ i, c i * (f i).1 ∈ P ^ (p + 1)) : ∀ i, c i ∈ P := by
  classical
  have h0 : ∑ i, (Ideal.Quotient.mk P (c i)) • e i = 0 := by
    simp_rw [← hf]
    have h1 : (∑ i, (Ideal.Quotient.mk P (c i)) • (Submodule.Quotient.mk (f i) : GrPiece P p)) =
        Submodule.Quotient.mk (∑ i, c i • f i) := by
      rw [← quotient_mk_sum]
      exact Finset.sum_congr rfl fun i _ => (Submodule.Quotient.mk_smul _ _ _).symm
    rw [h1, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap, Submodule.subtype_apply]
    simpa only [Submodule.coe_sum, Submodule.coe_smul, smul_eq_mul] using h
  have := Fintype.linearIndependent_iff.mp e.linearIndependent _ h0
  exact fun i => Ideal.Quotient.eq_zero_iff_mem.mp (this i)

include hPm hqr hz in
/-- p. 185: "if `λ ∈ F^q` and `λ ∈ P` then we must have `λ ∈ 𝔪^{q+1}` because the generators
`x₁, …, x_r` of `F` form a regular system of parameters of `Ō_{m̄}`": writing
`λ = Σ_{|α|=q} c_α x^α`, the relation `Σ c̄_α x̄^α = 0` forces all `c̄_α ∈ m̄`
(quasi-regularity of `x̄`), so `c_α ∈ 𝔪` and `λ ∈ 𝔪 F^q ⊆ 𝔪^{q+1}`. -/
theorem span_pow_inf_le_pow_succ (q : ℕ) : Ideal.span (Set.range y) ^ q ⊓ P ≤ m ^ (q + 1) := by
  classical
  intro l hl
  have hD : ∀ q α, α ∈ degreeFinset s q ↔ α.degree = q := fun _ _ => mem_degreeFinset
  obtain ⟨c, -, hc⟩ := exists_eq_sum_mono_of_mem y (degreeFinset s) hD ⊤ q
    (by rw [Ideal.top_mul]; exact hl.1 : l ∈ ⊤ * Ideal.span (Set.range y) ^ q)
  have hcm : ∀ α ∈ degreeFinset s q, c α ∈ m := by
    have h0 : ∑ α ∈ degreeFinset s q, Ideal.Quotient.mk P (c α) *
        (α.prod fun j e => (Ideal.Quotient.mk P (y j)) ^ e) ∈
        Ideal.span (Set.range fun j => Ideal.Quotient.mk P (y j)) ^ (q + 1) := by
      have : ∑ α ∈ degreeFinset s q, Ideal.Quotient.mk P (c α) *
          (α.prod fun j e => (Ideal.Quotient.mk P (y j)) ^ e) = Ideal.Quotient.mk P l := by
        rw [hc, map_sum]
        refine Finset.sum_congr rfl fun α _ => ?_
        rw [map_mul, map_finsuppProd]
        simp only [map_pow]
      rw [this, Ideal.Quotient.eq_zero_iff_mem.mpr hl.2]
      exact zero_mem _
    intro α hα
    have := coeff_mem_of_sum_mono_mem hqr (degreeFinset s) hD q
      (fun α => Ideal.Quotient.mk P (c α)) h0 α hα
    rw [hz] at this
    exact (Ideal.mem_quotient_iff_mem hPm).mp this
  rw [hc, pow_succ']
  exact Ideal.sum_mem _ fun α hα => Ideal.mul_mem_mul (hcm α hα)
    (prod_pow_mem_pow_of_span_le m y (span_range_le_of_span_map_eq P m hPm y hz) q α
      ((hD q α).mp hα))

/-- The sum over `{(p, q) : p + q = n}` as a sum over `p ≤ n`. -/
theorem sum_antidiagonal_subtype_eq {M : Type*} [AddCommMonoid M] (n : ℕ)
    (F : {pq : ℕ × ℕ // pq.1 + pq.2 = n} → M) :
    ∑ pq, F pq = ∑ p ∈ Finset.range (n + 1), if h : p ≤ n then F ⟨(p, n - p), by omega⟩ else 0 := by
  classical
  let eqv : Fin (n + 1) ≃ {pq : ℕ × ℕ // pq.1 + pq.2 = n} :=
    { toFun := fun p => ⟨((p : ℕ), n - p), by simp only; omega⟩
      invFun := fun pq => ⟨pq.1.1, by have := pq.2; omega⟩
      left_inv := fun p => by ext; rfl
      right_inv := fun pq => by
        ext
        · rfl
        · simp only
          have := pq.2
          omega }
  rw [← Fintype.sum_equiv eqv (fun p => F (eqv p)) F fun _ => rfl,
    ← Fin.sum_univ_eq_sum_range (fun p => if h : p ≤ n then F ⟨(p, n - p), by omega⟩ else 0)
      (n + 1)]
  exact Finset.sum_congr rfl fun p _ => by
    simp only [Nat.lt_succ_iff.mp p.2, ↓reduceDIte]
    rfl

include hPm hqr hz in
/-- **`ker ν ⊆ ker μ`** (pp. 184--185), the heart of the proof of Proposition 1 (1).  The proof is
the printed one: "Let `h` be an arbitrary element of the kernel of `ν`. We shall prove that
`μ(h) = 0`. Let us choose a system of elements `(f_i^{(p)})` of `Pᵖ` whose residue classes mod
`Pᵖ⁺¹` form a free base of `Pᵖ/Pᵖ⁺¹` as `Ō`-module. Then it is easy to show that
`Pᵖ = (f₁^{(p)}, f₂^{(p)}, …)O`. Therefore we can write `h = Σ_{p+q=n} (Σ_i f_i^{(p)} ⊗ g_i^{(q)})`
where `g_i^{(q)} ∈ F^q`. If `g_i^{(q)} ∈ 𝔪^{q+1}`, then `ν(f_i^{(p)} ⊗ g_i^{(q)}) =
μ(f_i^{(p)} ⊗ g_i^{(q)}) = 0`. Therefore, to prove `μ(h) = 0`, we may omit all those terms ... Thus
we assume that for every `(q, i)` either `g_i^{(q)} = 0` or `g_i^{(q)} ∉ 𝔪^{q+1}`", and the rest is
`coeff_eq_zero_of_sum_mem_pow_succ`, which shows that then all `g_i^{(q)} = 0`, "hence `μ(h) = 0` is clear". -/
theorem muDeg_eq_zero_of_nuDeg_eq_zero [IsLocalRing O] [IsNoetherianRing O] [P.IsPrime]
    [m.IsPrime] (hP : IsNormallyFlatAlongIdeal P) (hmPY : m = P ⊔ Ideal.span (Set.range y))
    (n : ℕ) (h : ⨁ pq : {pq : ℕ × ℕ // pq.1 + pq.2 = n},
      NuSummand P (Ideal.span (Set.range y)) n pq)
    (hν : nuDeg P m hPm y hz n h = 0) : muDeg P m hPm y hz n h = 0 := by
  classical
  have hmtop : m ≠ ⊤ := Ideal.IsPrime.ne_top'
  have hYm : (Ideal.span (Set.range y)) ≤ m := span_range_le_of_span_map_eq P m hPm y hz
  have hYtop : (Ideal.span (Set.range y)) ≠ ⊤ := ne_top_of_le_ne_top hmtop hYm
  have hPtop : P ≠ ⊤ := Ideal.IsPrime.ne_top'
  -- "Let us choose a system of elements `(f_i^{(p)})` of `Pᵖ` whose residue classes mod `Pᵖ⁺¹`
  -- form a free base of `Pᵖ/Pᵖ⁺¹` as `Ō`-module."
  have : ∀ p, Module.Free (O ⧸ P) (GrPiece P p) := hP
  let e := fun p => Module.Free.chooseBasis (O ⧸ P) (GrPiece P p)
  let ι : ℕ → Type u := fun p => Module.Free.ChooseBasisIndex (O ⧸ P) (GrPiece P p)
  obtain ⟨f, hf⟩ : ∃ f : ∀ p, ι p → ↥(P ^ p), ∀ p i, Submodule.Quotient.mk (f p i) = e p i := by
    choose f hf using fun p i => Submodule.Quotient.mk_surjective _ (e p i)
    exact ⟨f, hf⟩
  -- "Then it is easy to show that `Pᵖ = (f₁^{(p)}, f₂^{(p)}, …)O`."
  have hfspan : ∀ p, P ^ p = Ideal.span (Set.range fun i => (f p i).1) := fun p =>
    pow_eq_span_of_basis P hPtop p (e p) (f p) (hf p)
  -- "Therefore we can write `h = Σ_{p+q=n} (Σ_i f_i^{(p)} ⊗ g_i^{(q)})` where `g_i^{(q)} ∈ F^q`."
  let E : (∀ pq : {pq : ℕ × ℕ // pq.1 + pq.2 = n}, ι pq.1.1 → ↥((Ideal.span (Set.range y)) ^ pq.1.2)) →
      ⨁ pq : {pq : ℕ × ℕ // pq.1 + pq.2 = n}, NuSummand P (Ideal.span (Set.range y)) n pq := fun G =>
    ∑ pq, ∑ i, DirectSum.of (NuSummand P (Ideal.span (Set.range y)) n) pq (f pq.1.1 i ⊗ₜ[O] G pq i)
  have hrep : ∀ h, ∃ G, h = E G := by
    intro h
    induction h using DirectSum.induction_on with
    | zero => exact ⟨0, by simp [E]⟩
    | of pq a =>
      induction a using TensorProduct.inductionOn with
      | tmul a b =>
        obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun O).mp
          ((hfspan pq.1.1) ▸ a.2 : a.1 ∈ Ideal.span (Set.range fun i => (f pq.1.1 i).1))
        refine ⟨Pi.single pq fun i => c i • b, ?_⟩
        have ha : a = ∑ i, c i • f pq.1.1 i := Subtype.ext (by
          rw [Submodule.coe_sum]
          simpa only [Submodule.coe_smul] using hc.symm)
        simp only [E]
        rw [Finset.sum_eq_single pq (fun pq' _ hne => by
          simp only [Pi.single_eq_of_ne hne, Pi.zero_apply, TensorProduct.tmul_zero, map_zero,
            Finset.sum_const_zero]) (fun hn => absurd (Finset.mem_univ pq) hn)]
        simp only [Pi.single_eq_same]
        rw [← map_sum, ha, TensorProduct.sum_tmul]
        refine congrArg _ (Finset.sum_congr rfl fun i _ => ?_)
        rw [← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
      | add a a' ha ha' =>
        obtain ⟨G, hG⟩ := ha
        obtain ⟨G', hG'⟩ := ha'
        refine ⟨G + G', ?_⟩
        rw [map_add, hG, hG']
        simp only [E, Pi.add_apply, TensorProduct.tmul_add, map_add, Finset.sum_add_distrib]
    | add h h' hh hh' =>
      obtain ⟨G, hG⟩ := hh
      obtain ⟨G', hG'⟩ := hh'
      refine ⟨G + G', ?_⟩
      rw [hG, hG']
      simp only [E, Pi.add_apply, TensorProduct.tmul_add, map_add, Finset.sum_add_distrib]
  obtain ⟨G, rfl⟩ := hrep h
  -- the maps `ν` and `μ` on `Σ f_i^{(p)} ⊗ g_i^{(q)}`
  have hνE : nuDeg P m hPm y hz n (E G) = Submodule.Quotient.mk (∑ pq, ∑ i,
      (⟨(f pq.1.1 i).1 * (G pq i).1, mul_mem_pow_of_mem_pow P m hPm y hz n pq (f pq.1.1 i)
        (G pq i)⟩ : ↥(m ^ n))) := by
    simp only [E, map_sum, nuDeg_of, nuPiece_tmul]
    rw [← quotient_mk_sum]
    refine Finset.sum_congr rfl fun pq _ => ?_
    rw [← quotient_mk_sum]
  have hμE : muDeg P m hPm y hz n (E G) = ∑ pq, ∑ i, DirectSum.of (PsiSummand P m n) pq
      (zeroPieceMk P m pq.1.1 (f pq.1.1 i).1 (f pq.1.1 i).2 ⊗ₜ[O ⧸ m]
        toGrBar P m hPm y hz pq.1.2 (G pq i)) := by
    simp only [E, map_sum, muDeg_of, muPiece_tmul]
  -- "Since `ν(h) = 0`, the image `h̃` of `h` in `𝔪ⁿ` must be in `𝔪ⁿ⁺¹`"
  rw [hνE, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap, Submodule.subtype_apply,
    Submodule.coe_sum] at hν
  simp only [Submodule.coe_sum] at hν
  -- coefficients indexed by `p ∈ ℕ`
  let g : ∀ p, ι p → O := fun p i =>
    if hp : p ≤ n then ((G ⟨(p, n - p), by omega⟩ i : ↥((Ideal.span (Set.range y)) ^ (n - p))) : O) else 0
  have hsum0 : ∑ p ∈ Finset.range (n + 1), ∑ i, (f p i).1 * g p i ∈ m ^ (n + 1) := by
    rw [sum_antidiagonal_subtype_eq] at hν
    convert hν using 1
    refine Finset.sum_congr rfl fun p hp => ?_
    have hpn : p ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hp)
    simp only [hpn, ↓reduceDIte, g]
  -- "Thus we assume that for every `(q, i)` either `g_i^{(q)} = 0` or `g_i^{(q)} ∉ 𝔪^{q+1}`."
  let g' : ∀ p, ι p → O := fun p i => if g p i ∈ m ^ (n - p + 1) then 0 else g p i
  have hgG : ∀ p (hp : p ≤ n) i, g p i =
      ((G ⟨(p, n - p), by omega⟩ i : ↥((Ideal.span (Set.range y)) ^ (n - p))) : O) :=
    fun p hp i => by simp only [g, hp, ↓reduceDIte]
  have hgY' : ∀ p, p ≤ n → ∀ i, g' p i ∈ (Ideal.span (Set.range y)) ^ (n - p) := by
    intro p hp i
    by_cases hm : g p i ∈ m ^ (n - p + 1)
    · rw [show g' p i = 0 by simp only [g', hm, ↓reduceIte]]
      exact zero_mem _
    · rw [show g' p i = g p i by simp only [g', hm, ↓reduceIte], hgG p hp i]
      exact (G ⟨(p, n - p), by omega⟩ i).2
  have hgm' : ∀ p, p ≤ n → ∀ i, g' p i = 0 ∨ g' p i ∉ m ^ (n - p + 1) := by
    intro p hp i
    by_cases hm : g p i ∈ m ^ (n - p + 1)
    · exact Or.inl (by simp only [g', hm, ↓reduceIte])
    · exact Or.inr (by rw [show g' p i = g p i by simp only [g', hm, ↓reduceIte]]; exact hm)
  have hsum' : ∑ p ∈ Finset.range (n + 1), ∑ i, (f p i).1 * g' p i ∈ m ^ (n + 1) := by
    have hdiff : ∀ p ∈ Finset.range (n + 1), ∀ i, (f p i).1 * (g p i - g' p i) ∈ m ^ (n + 1) := by
      intro p hp i
      have hpn : p ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hp)
      by_cases hm : g p i ∈ m ^ (n - p + 1)
      · rw [show g' p i = 0 by simp only [g', hm, ↓reduceIte], sub_zero]
        have := Ideal.mul_mem_mul (Ideal.pow_right_mono hPm p (f p i).2) hm
        rwa [← pow_add, show p + (n - p + 1) = n + 1 by omega] at this
      · rw [show g' p i = g p i by simp only [g', hm, ↓reduceIte], sub_self, mul_zero]
        exact zero_mem _
    have h1 : ∑ p ∈ Finset.range (n + 1), ∑ i, (f p i).1 * g' p i =
        ∑ p ∈ Finset.range (n + 1), ∑ i, (f p i).1 * g p i -
          ∑ p ∈ Finset.range (n + 1), ∑ i, (f p i).1 * (g p i - g' p i) := by
      simp only [mul_sub, Finset.sum_sub_distrib, sub_sub_cancel]
    rw [h1]
    exact sub_mem hsum0 (Ideal.sum_mem _ fun p hp => Ideal.sum_mem _ fun i _ => hdiff p hp i)
  -- the claim of the printed proof
  have hfind : ∀ p (c : ι p → O), ∑ i, c i * (f p i).1 ∈ P ^ (p + 1) → ∀ i, c i ∈ P :=
    fun p c hc => coeff_mem_of_sum_mem_pow_succ P p (e p) (f p) (hf p) c hc
  have hall := coeff_eq_zero_of_sum_mem_pow_succ P (Ideal.span (Set.range y)) m hmPY hYtop (span_pow_inf_le_pow_succ P m hPm y hqr hz)
    (fun p i => (f p i).1) (fun p i => (f p i).2) hfspan hfind n g' hgY' hgm' hsum'
  -- "so `μ(h) = 0` is clear"
  rw [hμE]
  refine Finset.sum_eq_zero fun pq _ => Finset.sum_eq_zero fun i _ => ?_
  obtain ⟨⟨p, q⟩, hpq⟩ := pq
  have hpn : p ≤ n := by have : p + q = n := hpq; omega
  obtain rfl : q = n - p := by have : p + q = n := hpq; omega
  have h0 := hall p hpn i
  have hmem : g p i ∈ m ^ (n - p + 1) := by
    by_contra hm
    rw [show g' p i = g p i by simp only [g', hm, ↓reduceIte]] at h0
    exact hm (h0 ▸ zero_mem _)
  have hmem' : (G ⟨(p, n - p), hpq⟩ i).1 ∈ m ^ (n - p + 1) := by
    rw [← hgG p hpn i]
    exact hmem
  rw [toGrBar_zero_of_mem P m hPm y hz (n - p) _ hmem', TensorProduct.tmul_zero, map_zero]

include hPm hqr hz in
/-- **Proposition 1 (1), p. 184**, the injectivity half: "Therefore, to prove that `ψ` is an
isomorphism, it suffices that the kernel of `ν` is equal to that of `μ`": since `ν = ψ ∘ μ` and
`μ` is surjective, `ψ x = 0` gives `x = μ(h)` with `ν(h) = 0`, so `μ(h) = 0` by
`muDeg_eq_zero_of_nuDeg_eq_zero`. -/
theorem psiDeg_injective_of_isNormallyFlatAlongIdeal [IsLocalRing O] [IsNoetherianRing O]
    [P.IsPrime] [m.IsPrime] (hP : IsNormallyFlatAlongIdeal P)
    (hmPY : m = P ⊔ Ideal.span (Set.range y)) (n : ℕ) :
    Function.Injective (psiDeg P m hPm y hqr hz n) := by
  let _ : ∀ pq : {pq : ℕ × ℕ // pq.1 + pq.2 = n}, AddCommGroup (PsiSummand P m n pq) :=
    fun pq => TensorProduct.addCommGroup
  refine (injective_iff_map_eq_zero (psiDeg P m hPm y hqr hz n)).mpr fun x hx => ?_
  obtain ⟨h, rfl⟩ := muDeg_surjective P m hPm y hz n x
  have hν : nuDeg P m hPm y hz n h = 0 := by
    rw [← psiDeg_muDeg P m hPm y hqr hz n h]
    exact hx
  rw [muDeg_eq_zero_of_nuDeg_eq_zero P m hPm y hqr hz hP hmPY n h hν]

include hqr hz in
/-- **Proposition 1 (1), p. 184**: "If `gr_P(O)` is flat over `Ō`, then (1) the homomorphism of
graded `K`-algebras, obtained as above, `ψ : gr⁰_{m̄}(gr_P(O)) ⊗_K gr_{m̄}(Ō) → gr_m(O)` is an
isomorphism."

Here `ψ = α ⊗ β*` is the map of p. 183, given by its homogeneous components `psiPiece` (`psiDeg n`
is the part of total degree `n`), where `y₁, …, y_s ∈ O` are the paper's `x₁, …, x_r ∈ 𝔪`: their classes in `Ō` generate
`m̄` and form a quasi-regular family (a part of a regular system of parameters of `Ō`, "since
`K` and `Ō` are both regular, `(x̄₁, …, x̄_r)` can be extended to a regular system of
parameters", footnote 39; every minimal base `ȳ` of `m̄` has this property).  The hypothesis
`hmPY` is `𝔪 = P + (y)`.

The proof is the printed one (pp. 184–185): with `ν = ψ ∘ μ` (`psiDeg_muDeg`) and `μ` surjective
(`muDeg_surjective`) "to prove that `ψ` is an isomorphism, it suffices that the kernel of `ν` is
equal to that of `μ`"; `ker ν ⊆ ker μ` is `muDeg_eq_zero_of_nuDeg_eq_zero` (the `p₁`/`δ`
argument, `coeff_eq_zero_of_sum_mem_pow_succ`), so `ψ` is injective
(`psiDeg_injective_of_isNormallyFlatAlongIdeal`); surjectivity of `ψ` is `psiDeg_surjective`
(`𝔪ⁿ = Σ_{p+q=n} Pᵖ (y)^q`, and the surjectivity of `ν`). -/
@[blueprint "prop:II.1-1-psi"
  (statement := /-- Let $O$ be a local ring and $P\subseteq\mathfrak m$ prime ideals with $O/P$
    and $O/\mathfrak m$ regular; $\bar O=O/P$, $\bar{\mathfrak m}=\mathfrak m/P$,
    $K=O/\mathfrak m$. Let $y_1,\dots,y_s\in O$ (the paper's $x_1,\dots,x_r$) be such that
    their classes in $\bar O$ form a quasi-regular system generating $\bar{\mathfrak m}$, and let
    $\psi=\alpha\otimes\beta^*\colon\operatorname{gr}^0_{\bar{\mathfrak m}}
    (\operatorname{gr}_P(O))\otimes_K\operatorname{gr}_{\bar{\mathfrak m}}(\bar O)\to
    \operatorname{gr}_{\mathfrak m}(O)$ be the map of p.~183, with $\beta^*$ sending the class
    of $\bar y_j$ to the class of $y_j$. If $\operatorname{gr}_P(O)$ is flat over $\bar O$,
    then $\psi$ is an isomorphism (in every total degree). (Proposition 1 (1), p.~184.)

    \textbf{Formalization note (encoding).} $\psi$ is given by its homogeneous components
    $\psi_{p,q}\colon\operatorname{gr}^0_{\bar{\mathfrak m}}(\operatorname{gr}^p_P(O))
    \otimes_K\operatorname{gr}^q_{\bar{\mathfrak m}}(\bar O)\to
    \operatorname{gr}^{p+q}_{\mathfrak m}(O)$; ``isomorphism'' means that the induced map on
    each total degree $n$ is bijective. -/)
  (proof := /-- (The paper's proof, pp.~184--185, in the notation of \cref{prop:II.1-1}.)
    With $F=(y_1,\dots,y_s)$ one has $\psi\circ\mu=\nu$ on
    $\bigoplus_{p+q=n}P^p\otimes_OF^q$, and $\mu,\nu$ are surjective (``as is easily seen'');
    hence ``it suffices that the kernel of $\nu$ is equal to that of $\mu$''. The inclusion
    $\ker\nu\subseteq\ker\mu$ is the $p_1$/$\delta$ argument of p.~185, given in the proof of
    \cref{prop:II.1-1}; it shows that $\psi_n$ is injective. Surjectivity of $\psi_n$ is the
    surjectivity of $\nu$ (since $\mathfrak m^n=\sum_{p+q=n}P^pF^q$).

    \textbf{Gap filled.} ``As is easily seen, $\nu$ and $\mu$ are both surjective'' (p.~184) is
    argued in Lean: $\nu$ is surjective because $\mathfrak m^n=\sum P^pF^q$, and $\mu$ because
    $\bar{\mathfrak m}^q=(F^q+P)/P$ and $\operatorname{gr}^0_{\bar{\mathfrak m}}
    (\operatorname{gr}^p_P(O))$ is generated by the classes of the elements of $P^p$. -/)
  (latexEnv := "proposition")]
theorem psiDeg_bijective_of_isNormallyFlatAlongIdeal [IsLocalRing O] [IsNoetherianRing O]
    [P.IsPrime] [m.IsPrime] [IsRegularLocalRing (O ⧸ P)] [IsRegularLocalRing (O ⧸ m)]
    (hP : IsNormallyFlatAlongIdeal P) (hmPY : m = P ⊔ Ideal.span (Set.range y)) (n : ℕ) :
    Function.Bijective (psiDeg P m hPm y hqr hz n) :=
  ⟨psiDeg_injective_of_isNormallyFlatAlongIdeal P m hPm y hqr hz hP hmPY n,
    psiDeg_surjective P m hPm y hqr hz hmPY n⟩

end Prop1Bridge

/-- Proposition 1, p. 184: "Let `O` be a local ring and `P`, `m` prime ideals in `O` such that
`m` contains `P` and `O/P`, `O/m` are regular. Let `Ō = O/P` and `m̄ = m/P`. Let
`K = O/m = Ō/m̄`. If `gr_P(O)` is flat over `Ō`, then (1) the homomorphism of graded
`K`-algebras, obtained as above, `ψ: gr⁰_{m̄}(gr_P(O)) ⊗_K gr_{m̄}(Ō) → gr_m(O)` is an
isomorphism; (2) `gr_m(O)` is flat over `K`."

Deviation from the paper (statement modified): the paper's `ψ = α ⊗ β*` (p. 183) "is not
canonical and depends upon the choice of the system `(x₁, …, x_r)`" of elements of `m` lifting
a minimal base of `m̄`.  Assertion (1) is stated here only in the weak form that, for every
total degree `n`, there exists *some* `K`-linear isomorphism
`⊕_{p+q=n} gr⁰_{m̄}(gr^p_P(O)) ⊗_K gr^q_{m̄}(Ō) ≃ gr^n_m(O)` of the homogeneous parts of degree
`n` (it is what Corollary 2 uses); the statement about the specific map `ψ` (`psiDeg`, for every
choice of the system) is `psiDeg_bijective_of_isNormallyFlatAlongIdeal` (node
`prop:II.1-1-psi`); `ψ` as one isomorphism of graded `K`-algebras is `psiAlgHom_bijective` (node
`prop:II.1-1-algebra`).

The proof is the printed one (pp. 184–185).  (1) is proved, for a system `ȳ` lifting a minimal
base of `m̄` (a part of a regular system of parameters of `Ō`, footnote 39), by showing that `ψ`
is bijective in every total degree (`psiDeg_bijective_of_isNormallyFlatAlongIdeal`: `ψ ∘ μ = ν`,
`μ` and `ν` surjective, `ker ν ⊆ ker μ` by the `p₁`/`δ` argument,
`muDeg_eq_zero_of_nuDeg_eq_zero`).  (2) "follows from (1). In fact, `gr⁰_{m̄}(gr_P(O))` is
obviously flat over `K` and so is `gr_{m̄}(Ō)` because `Ō` and `Ō/m̄` are assumed to be
regular": the two tensor factors are free over `K`
(`nonempty_basis_grModPiece_zero`, `grPieceMapBasis`), hence so is the source of `ψ`, hence so
is `gr_m(O)`.

Formalization note (encoding): `gr⁰_{m̄}(gr^p_P(O))` is
`GrModPiece m (GrPiece P p) 0 = gr^p_P(O)/m·gr^p_P(O)` and `gr^q_{m̄}(Ō)` is
`GrPiece (m/P) q`, both as `K = O/m`-modules.  Assertion (2), "`gr_m(O)` is flat over `K`", is
`IsNormallyFlatAlongIdeal m` (Lemma 1). -/
@[blueprint "prop:II.1-1"
  (statement := /-- Let $O$ be a local ring and $P$, $\mathfrak m$ prime ideals in $O$ such
    that $\mathfrak m$ contains $P$ and $O/P$, $O/\mathfrak m$ are regular. Let $\bar O=O/P$
    and $\bar{\mathfrak m}=\mathfrak m/P$. Let $K=O/\mathfrak m=\bar O/\bar{\mathfrak m}$. If
    $\operatorname{gr}_P(O)$ is flat over $\bar O$ (\cref{def:normally-flat-ideal}), then
    (1) the homomorphism of graded $K$-algebras, obtained as above,
    $\psi\colon\operatorname{gr}^0_{\bar{\mathfrak m}}(\operatorname{gr}_P(O))\otimes_K
    \operatorname{gr}_{\bar{\mathfrak m}}(\bar O)\to\operatorname{gr}_{\mathfrak m}(O)$ is an
    isomorphism; (2) $\operatorname{gr}_{\mathfrak m}(O)$ is flat over $K$. (p.~184.)

    \textbf{Deviation from the paper (statement modified).} The map $\psi=\alpha\otimes\beta^*$
    of p.~183 depends on the choice of a system $(x_1,\dots,x_r)$; here (1) is stated only in the
    weaker form that for every $n$ there is \emph{some} $K$-linear isomorphism
    $\bigoplus_{p+q=n}\operatorname{gr}^0_{\bar{\mathfrak m}}
    (\operatorname{gr}^p_P(O))\otimes_K\operatorname{gr}^q_{\bar{\mathfrak m}}(\bar O)\cong
    \operatorname{gr}^n_{\mathfrak m}(O)$. That the specific $\psi$ (for every choice of the
    system) is an isomorphism is \cref{prop:II.1-1-psi}, and as one isomorphism of graded
    $K$-algebras \cref{prop:II.1-1-algebra}. -/)
  (proof := /-- (The paper's proof, pp.~184--185.) Let $F=(x_1,\dots,x_r)\subseteq\mathfrak m$
    be the chosen system, so that $\mathfrak m=P+F$ and $(P^p\otimes_O F^q)\to\mathfrak m^n$,
    $p+q=n$, is surjective. ``For every non-negative integer $q$'' there is a commutative
    diagram $\mathfrak m^q\supset F^q\to(F^q+P)/P=\bar{\mathfrak m}^q$,
    $F^q\to\operatorname{gr}^q_{\bar{\mathfrak m}}(\bar O)\rightleftarrows
    \operatorname{gr}^q_{\mathfrak m}(O)$ (with $\beta^*$ and $\beta$), and for every $p$ one for
    $P^p\to\operatorname{gr}^p_{\mathfrak m}(O)\leftarrow\operatorname{gr}^0_{\bar{\mathfrak m}}
    (\operatorname{gr}^p_P(O))$ ($\alpha$). They produce, for each $n$, a commutative triangle
    $\psi\circ\mu=\nu$ on $\bigoplus_{p+q=n}P^p\otimes_OF^q$, where $\nu$ is obtained by first
    sending $\bigoplus P^p\otimes_OF^q$ into $\mathfrak m^n$. ``As is easily seen, $\nu$ and
    $\mu$ are both surjective. Therefore, to prove that $\psi$ is an isomorphism, it suffices
    that the kernel of $\nu$ is equal to that of $\mu$.'' Let $h\in\ker\nu$; ``we shall prove
    that $\mu(h)=0$''. Choose $f^{(p)}_i\in P^p$ whose classes mod $P^{p+1}$ form a free base of
    $P^p/P^{p+1}$ over $\bar O$ (flatness); then ``it is easy to show that
    $P^p=(f^{(p)}_1,f^{(p)}_2,\dots)O$'' and so $h=\sum_{p+q=n}(\sum_if^{(p)}_i\otimes
    g^{(q)}_i)$ with $g^{(q)}_i\in F^q$. If $g^{(q)}_i\in\mathfrak m^{q+1}$ then
    $\nu(f^{(p)}_i\otimes g^{(q)}_i)=\mu(f^{(p)}_i\otimes g^{(q)}_i)=0$, so these terms may be
    omitted: ``for every $(q,i)$ either $g^{(q)}_i=0$ or $g^{(q)}_i\notin\mathfrak m^{q+1}$''.
    Since $\nu(h)=0$, the image $\tilde h$ of $h$ in $\mathfrak m^n$ lies in
    $\mathfrak m^{n+1}=(P,F)^{n+1}$, so $\tilde h\in\sum_{p+q'=n+1}P^pF^{q'}$. Take the maximal
    $p_1$ with $\tilde h\in\sum_{p+q'=n+1,\,p\ge p_1}P^pF^{q'}$ and write
    $\tilde h=\sum(\sum_if^{(p)}_i\lambda^{(q')}_i)$ with $\lambda^{(q')}_i\in F^{q'}$. Claim:
    unless $p_1=n+1$, some $\lambda^{(q'_1)}_i\notin P$, $q'_1=n-p_1+1$. Indeed, ``if
    $\lambda^{(q'_1)}_i\in P$ then we must have $\lambda^{(q'_1)}_i\in\mathfrak m^{q'_1+1}$
    because the generators $x_1,\dots,x_r$ of $F$ form a regular system of parameters of
    $\bar O_{\bar{\mathfrak m}}$'', hence $\lambda^{(q'_1)}_i\in\sum_{q'_1=s+t,\,s>0}P^sF^t+
    F^{q'_1+1}$, ``by the same reason'' $+F^{q'_1+2}$, and repeating, $+F^{q'_1+m}$ for all
    $m$; ``hence $\lambda^{(q'_1)}_i\in\sum_{s>0}P^sF^t$'', and if this held for all $i$, $p_1$
    would not be maximal. Now let $\delta$ be the smallest integer such that one of the
    $\lambda^{(n-\delta+1)}_i$ and $g^{(n-\delta)}_i$ is not zero. If $\delta=n+1$ all
    $g^{(q)}_i=0$ and $\mu(h)=0$ ``is clear''. If $\delta\le n$ then
    $\sum_if^{(\delta)}_ig^{(n-\delta)}_i\equiv\sum_if^{(\delta)}_i\lambda^{(n-\delta+1)}_i
    \bmod P^{\delta+1}$ and, the $f^{(\delta)}_i$ forming a free base of $P^\delta/P^{\delta+1}$,
    $g^{(n-\delta)}_i\equiv\lambda^{(n-\delta+1)}_i\bmod P$ for all $i$; as
    $g^{(n-\delta)}_i\in F^{n-\delta}$, $\lambda^{(n-\delta+1)}_i\in F^{n-\delta+1}$, the
    assumption on the $g$'s gives $g^{(n-\delta)}_i=0$, so $\delta=p_1$ and all
    $\lambda^{(n-\delta+1)}_i\in P$, contradicting the claim. This proves (1). ``The second
    assertion (2) follows from (1). In fact, $\operatorname{gr}^0_{\bar{\mathfrak m}}
    (\operatorname{gr}_P(O))$ is obviously flat over $K$ and so is $\operatorname{gr}_{\bar
    {\mathfrak m}}(\bar O)$ because $\bar O$ and $\bar O/\bar{\mathfrak m}$ are assumed to be
    regular.''

    \textbf{Gaps filled (Lean).} (a) ``As is easily seen, $\nu$ and $\mu$ are both
    surjective'': argued in Lean (\texttt{nuDeg\_surjective}, \texttt{muDeg\_surjective}).
    (b) ``It is easy to show that $P^p=(f^{(p)}_1,\dots)O$'': Nakayama's lemma
    (\texttt{pow\_eq\_span\_of\_basis}). (c) ``If $\lambda\in P$ then $\lambda\in\mathfrak
    m^{q+1}$'' is the quasi-regularity of $\bar x$ (\texttt{span\_pow\_inf\_le\_pow\_succ}), and
    the passage from ``$+F^{q'_1+m}$ for all $m$'' to ``hence $\lambda\in\sum P^sF^t$'' is
    Krull's intersection theorem, which the paper leaves implicit
    (\texttt{mem\_mixedIdeal\_of\_mem\_inf}). (d) ``$\operatorname{gr}^0_{\bar{\mathfrak m}}
    (\operatorname{gr}_P(O))$ is obviously flat over $K$ and so is $\operatorname{gr}_{\bar
    {\mathfrak m}}(\bar O)$'': both are free over $K$ (bases \texttt{nonempty\_basis\_grModPiece\_zero},
    \texttt{grPieceMapBasis}), and ``(2) follows from (1)'' is the transport of freeness along
    the isomorphism $\psi_n$. -/)
  (latexEnv := "proposition")]
theorem isNormallyFlatAlongIdeal_of_le [IsLocalRing O] [IsNoetherianRing O]
    (P m : Ideal O) [P.IsPrime] [m.IsPrime] (hPm : P ≤ m)
    [IsRegularLocalRing (O ⧸ P)] [IsRegularLocalRing (O ⧸ m)]
    (hP : IsNormallyFlatAlongIdeal P) :
    (∀ n : ℕ, Nonempty ((⨁ pq : {pq : ℕ × ℕ // pq.1 + pq.2 = n},
        GrModPiece m (GrPiece P pq.1.1) 0 ⊗[O ⧸ m]
          GrPiece (m.map (Ideal.Quotient.mk P)) pq.1.2) ≃ₗ[O ⧸ m] GrPiece m n)) ∧
      IsNormallyFlatAlongIdeal m := by
  classical
  -- a part `ȳ` of a regular system of parameters of `Ō` generating `m̄` (p. 183), lifted to `O`
  have hmb : (m.map (Ideal.Quotient.mk P)).IsPrime :=
    Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by rw [Ideal.mk_ker]; exact hPm)
  have hreg : IsRegularLocalRing ((O ⧸ P) ⧸ m.map (Ideal.Quotient.mk P)) :=
    IsRegularLocalRing.of_ringEquiv (DoubleQuot.quotQuotEquivQuotOfLE hPm).symm
  obtain ⟨S, T, hS, hScard, hTS, hT⟩ :=
    exists_finset_span_eq_prime (O ⧸ P) (m.map (Ideal.Quotient.mk P)) hreg
  let z : Fin T.card → O ⧸ P := fun i => (T.equivFin.symm i : O ⧸ P)
  have hinj : Function.Injective z := Subtype.val_injective.comp T.equivFin.symm.injective
  have hrange : Set.range z = (T : Set (O ⧸ P)) := by
    ext w
    constructor
    · rintro ⟨i, rfl⟩
      exact (T.equivFin.symm i).2
    · intro hw
      exact ⟨T.equivFin ⟨w, hw⟩, by simp [z]⟩
  have hqrz : IsQuasiRegular z :=
    isQuasiRegular_of_minimal hS hScard hinj (fun i => hTS (T.equivFin.symm i).2)
  have hzspan : Ideal.span (Set.range z) = m.map (Ideal.Quotient.mk P) := by rw [hrange, hT]
  let y : Fin T.card → O := fun i => Function.surjInv Ideal.Quotient.mk_surjective (z i)
  have hyz : (fun j => Ideal.Quotient.mk P (y j)) = z := funext fun i => Function.surjInv_eq _ _
  have hqr : IsQuasiRegular (fun j => Ideal.Quotient.mk P (y j)) := by rw [hyz]; exact hqrz
  have hYmap : (Ideal.span (Set.range y)).map (Ideal.Quotient.mk P) =
      m.map (Ideal.Quotient.mk P) := by
    rw [Ideal.map_span, ← Set.range_comp, ← hzspan]
    exact congrArg _ (congrArg Set.range hyz)
  have hmPY : m = P ⊔ Ideal.span (Set.range y) := by
    apply le_antisymm
    · intro a ha
      have : Ideal.Quotient.mk P a ∈ (Ideal.span (Set.range y)).map (Ideal.Quotient.mk P) := by
        rw [hYmap]
        exact Ideal.mem_map_of_mem _ ha
      rw [Ideal.mem_quotient_iff_mem_sup] at this
      rwa [sup_comm]
    · refine sup_le hPm ?_
      rw [Ideal.span_le]
      rintro _ ⟨j, rfl⟩
      rw [SetLike.mem_coe, ← Ideal.mem_quotient_iff_mem hPm, ← hYmap]
      exact Ideal.mem_map_of_mem _ (Ideal.subset_span ⟨j, rfl⟩)
  have hmtop : m ≠ ⊤ := Ideal.IsPrime.ne_top'
  let D : ℕ → Finset (Fin T.card →₀ ℕ) := fun q => (Finsupp.finite_of_degree_eq q).toFinset
  have hD : ∀ q α, α ∈ D q ↔ α.degree = q := fun q α => by simp [D]
  have hz : Ideal.span (Set.range fun j => Ideal.Quotient.mk P (y j)) =
      m.map (Ideal.Quotient.mk P) := by rw [hyz]; exact hzspan
  -- (1): "to prove that `ψ` is an isomorphism" - `ψ` is bijective in every total degree
  have hψ := fun n => psiDeg_bijective_of_isNormallyFlatAlongIdeal P m hPm y hqr hz hP hmPY n
  -- "`gr⁰_{m̄}(gr_P(O))` is obviously flat over `K` and so is `gr_{m̄}(Ō)`": both are free
  have : ∀ p, Module.Free (O ⧸ P) (GrPiece P p) := hP
  have hA : ∀ p, Module.Free (O ⧸ m) (GrModPiece m (GrPiece P p) 0) := fun p =>
    Module.Free.of_basis (nonempty_basis_grModPiece_zero P m hPm p
      (Module.Free.chooseBasis (O ⧸ P) (GrPiece P p))).some
  have hBq : ∀ q, Module.Free (O ⧸ m) (GrPiece (m.map (Ideal.Quotient.mk P)) q) := fun q =>
    Module.Free.of_basis (nonempty_basis_grPiece_map P m hPm z hqrz hzspan D hD q).some
  refine ⟨fun n => ⟨LinearEquiv.ofBijective (psiDeg P m hPm y hqr hz n) (hψ n)⟩, fun n => ?_⟩
  -- "(2) follows from (1)": the source of `ψ` is free over `K`
  have hfreeL : Module.Free (O ⧸ m) (⨁ pq : {pq : ℕ × ℕ // pq.1 + pq.2 = n},
      GrModPiece m (GrPiece P pq.1.1) 0 ⊗[O ⧸ m] GrPiece (m.map (Ideal.Quotient.mk P)) pq.1.2) :=
    inferInstance
  exact Module.Free.of_equiv (LinearEquiv.ofBijective (psiDeg P m hPm y hqr hz n) (hψ n))

/-- A part `ȳ` of a regular system of parameters of `Ō = O/P` generating `m̄ = 𝔪/P` (p. 183),
lifted to `O`, so that `𝔪 = P + (y)`. -/
theorem exists_adapted_lift {O : Type u} [CommRing O] (P m : Ideal O) [P.IsPrime]
    [m.IsPrime] (hPm : P ≤ m) [IsRegularLocalRing (O ⧸ P)] [IsRegularLocalRing (O ⧸ m)] :
    ∃ (s : ℕ) (y : Fin s → O), IsQuasiRegular (fun j => Ideal.Quotient.mk P (y j)) ∧
      Ideal.span (Set.range fun j => Ideal.Quotient.mk P (y j)) =
        m.map (Ideal.Quotient.mk P) ∧
      m = P ⊔ Ideal.span (Set.range y) ∧
      s ≤ (IsLocalRing.maximalIdeal (O ⧸ P)).spanFinrank := by
  classical
  have hmb : (m.map (Ideal.Quotient.mk P)).IsPrime :=
    Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by rw [Ideal.mk_ker]; exact hPm)
  have hreg : IsRegularLocalRing ((O ⧸ P) ⧸ m.map (Ideal.Quotient.mk P)) :=
    IsRegularLocalRing.of_ringEquiv (DoubleQuot.quotQuotEquivQuotOfLE hPm).symm
  obtain ⟨S, T, hS, hScard, hTS, hT⟩ :=
    exists_finset_span_eq_prime (O ⧸ P) (m.map (Ideal.Quotient.mk P)) hreg
  let z : Fin T.card → O ⧸ P := fun i => (T.equivFin.symm i : O ⧸ P)
  have hinj : Function.Injective z := Subtype.val_injective.comp T.equivFin.symm.injective
  have hrange : Set.range z = (T : Set (O ⧸ P)) := by
    ext w
    constructor
    · rintro ⟨i, rfl⟩
      exact (T.equivFin.symm i).2
    · intro hw
      exact ⟨T.equivFin ⟨w, hw⟩, by simp [z]⟩
  have hqrz : IsQuasiRegular z :=
    isQuasiRegular_of_minimal hS hScard hinj (fun i => hTS (T.equivFin.symm i).2)
  have hzspan : Ideal.span (Set.range z) = m.map (Ideal.Quotient.mk P) := by rw [hrange, hT]
  let y : Fin T.card → O := fun i => Function.surjInv Ideal.Quotient.mk_surjective (z i)
  have hyz : (fun j => Ideal.Quotient.mk P (y j)) = z := funext fun i => Function.surjInv_eq _ _
  have hYmap : (Ideal.span (Set.range y)).map (Ideal.Quotient.mk P) =
      m.map (Ideal.Quotient.mk P) := by
    rw [Ideal.map_span, ← Set.range_comp, ← hzspan]
    exact congrArg _ (congrArg Set.range hyz)
  refine ⟨T.card, y, by rw [hyz]; exact hqrz, by rw [hyz]; exact hzspan, ?_, ?_⟩
  · apply le_antisymm
    · intro a ha
      have : Ideal.Quotient.mk P a ∈ (Ideal.span (Set.range y)).map (Ideal.Quotient.mk P) := by
        rw [hYmap]
        exact Ideal.mem_map_of_mem _ ha
      rw [Ideal.mem_quotient_iff_mem_sup] at this
      rwa [sup_comm]
    · refine sup_le hPm ?_
      rw [Ideal.span_le]
      rintro _ ⟨j, rfl⟩
      rw [SetLike.mem_coe, ← Ideal.mem_quotient_iff_mem hPm, ← hYmap]
      exact Ideal.mem_map_of_mem _ (Ideal.subset_span ⟨j, rfl⟩)
  · rw [← hScard]
    exact Finset.card_le_card hTS

/-- The number of monomials of degree `q` in `s` variables, with the convention of Corollary 2
for `s = 0`. -/
private theorem card_monomials (s q : ℕ) (D : Finset (Fin s →₀ ℕ))
    (hD : ∀ α, α ∈ D ↔ α.degree = q) :
    D.card = if s = 0 then (if q = 0 then 1 else 0) else Nat.choose (q + s - 1) (s - 1) := by
  classical
  have e : ↥D ≃ Sym (Fin s) q :=
    (Equiv.subtypeEquivRight fun α => by
      rw [hD, Finsupp.degree_apply]
      rfl).trans (Sym.equivNatSum (Fin s) q).symm
  rw [← Fintype.card_coe D, Fintype.card_congr e, Sym.card_sym_eq_multichoose, Fintype.card_fin,
    Nat.multichoose_eq]
  split_ifs with hs hq
  · subst hs hq
    simp
  · subst hs
    exact Nat.choose_eq_zero_of_lt (by omega)
  · have : s + q - 1 = q + (s - 1) := by omega
    rw [this, Nat.choose_symm_add, show q + (s - 1) = q + s - 1 by omega]

/-- `Σ_{p+q=n} (Σ_{i≤p} r_i) b_q = Σ_{j≤n} Σ_{p≤j} r_p b_{j-p}` (summation of the
isomorphisms of Proposition 1 over the degrees `i ≤ n`, p. 186). -/
private theorem sum_antidiagonal_sum_range_eq (r b : ℕ → ℕ) (n : ℕ) :
    ∑ pq ∈ Finset.HasAntidiagonal.antidiagonal n, (∑ i ∈ Finset.range (pq.1 + 1), r i) * b pq.2 =
      ∑ j ∈ Finset.range (n + 1), ∑ p ∈ Finset.range (j + 1), r p * b (j - p) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.Nat.sum_antidiagonal_succ, Finset.sum_range_succ _ (n + 1), ← ih]
    have h1 : ∑ pq ∈ Finset.HasAntidiagonal.antidiagonal n,
        (∑ i ∈ Finset.range (pq.1 + 1 + 1), r i) * b pq.2 =
        ∑ pq ∈ Finset.HasAntidiagonal.antidiagonal n,
          (∑ i ∈ Finset.range (pq.1 + 1), r i) * b pq.2 +
          ∑ pq ∈ Finset.HasAntidiagonal.antidiagonal n, r (pq.1 + 1) * b pq.2 := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun pq _ => by rw [Finset.sum_range_succ, add_mul]
    have h2 : ∑ p ∈ Finset.range (n + 1 + 1), r p * b (n + 1 - p) =
        r 0 * b (n + 1) + ∑ pq ∈ Finset.HasAntidiagonal.antidiagonal n, r (pq.1 + 1) * b pq.2 := by
      rw [← Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk (fun pq => r pq.1 * b pq.2) (n + 1),
        Finset.Nat.sum_antidiagonal_succ]
    rw [h1, h2]
    simp only [Finset.sum_range_one, zero_add]
    ring

/-- Corollary 2 (i), first printed step (p. 186): "In general, the localization `gr_P(O)_P` of
`gr_P(O)` with respect to `P` is canonically isomorphic to `gr_{PO_P}(O_P)`. Since `grᵖ_P(O)` is a
free `Ō`-module for every non-negative integer `p`, we have
`dim_{O_P/PO_P}(grᵖ_{PO_P}(O_P)) = dim_K(gr⁰_{m̄}(grᵖ_P(O)))` where `m̄ = m/P`."  The canonical
isomorphism is the one of p. 181 (flat base change `O → O_P`, `GrPiece.nonempty_baseChange_equiv`),
in degree `p`: `O_P/PO_P ⊗_Ō grᵖ_P(O) ≅ grᵖ_{PO_P}(O_P)`.  So the left-hand side is the rank of
the free `Ō`-module `grᵖ_P(O)` (`Module.finrank_baseChange`), and so is the right-hand side
(`nonempty_basis_grModPiece_zero`, the reduction `gr⁰_{m̄}`).  The isomorphism is the justification
of the printed "in general". -/
private theorem finrank_grPiece_localization_eq [IsLocalRing O] [IsNoetherianRing O]
    (P m : Ideal O) [P.IsPrime] [m.IsPrime] (hPm : P ≤ m) (hP : IsNormallyFlatAlongIdeal P) (p : ℕ) :
    Module.finrank (Localization.AtPrime P ⧸ IsLocalRing.maximalIdeal (Localization.AtPrime P))
        (GrPiece (IsLocalRing.maximalIdeal (Localization.AtPrime P)) p) =
      Module.finrank (O ⧸ m) (GrModPiece m (GrPiece P p) 0) := by
  classical
  have : Module.Free (O ⧸ P) (GrPiece P p) := hP p
  let e := Module.Free.chooseBasis (O ⧸ P) (GrPiece P p)
  have hM : P.map (algebraMap O (Localization.AtPrime P)) =
      IsLocalRing.maximalIdeal (Localization.AtPrime P) :=
    Localization.AtPrime.map_eq_maximalIdeal
  -- "`gr_P(O)_P` is canonically isomorphic to `gr_{PO_P}(O_P)`" (p. 181, in degree `p`)
  have key : ∀ M : Ideal (Localization.AtPrime P), P.map (algebraMap O (Localization.AtPrime P)) =
      M → Module.finrank (Localization.AtPrime P ⧸ M) (GrPiece M p) =
        Module.finrank (O ⧸ P) (GrPiece P p) := by
    rintro M rfl
    obtain ⟨e₂⟩ := GrPiece.nonempty_baseChange_equiv (A' := Localization.AtPrime P) P p
    rw [← e₂.finrank_eq, Module.finrank_baseChange]
  rw [key _ hM, Module.finrank_eq_card_basis e,
    Module.finrank_eq_card_basis (nonempty_basis_grModPiece_zero P m hPm p e).some]

/-- Corollary 2 (i), third printed step (p. 186): "We know that `gr_{m̄}(Ō)` is a polynomial ring
of `r` variables, and hence `dim_K(gr^q_{m̄}(Ō)) = C(q+r-1, r-1)` for all non-negative integer
`q`", with `r = dim Ō`.  The polynomial ring is the isomorphism of `K`-algebras
`τ : K[X₁, …, X_r] → gr_{m̄}(Ō)`, `X_j ↦ [ȳ_j]` (`psiTau_bijective`), for a regular system of
parameters `ȳ` of `Ō` generating `m̄` (footnote 39); it maps the homogeneous polynomials of degree
`q` onto `gr^q_{m̄}(Ō)`, so that `dim_K gr^q_{m̄}(Ō)` is the number of monomials of degree `q`
(`finrank_grPiece_eq_natCard_of_psiTau`), and the number `r` of variables is `dim Ō` because `Ō` is
regular (the number of generators of `m̄` is `dim Ō`).  For `r = 0` the binomial coefficient is
read as in the statement of Corollary 2. -/
private theorem finrank_grPiece_map_eq_choose [IsLocalRing O] [IsNoetherianRing O]
    (P : Ideal O) [P.IsPrime] [IsRegularLocalRing (O ⧸ P)]
    [IsRegularLocalRing (O ⧸ IsLocalRing.maximalIdeal O)] (q : ℕ) :
    Module.finrank (O ⧸ IsLocalRing.maximalIdeal O)
        (GrPiece ((IsLocalRing.maximalIdeal O).map (Ideal.Quotient.mk P)) q) =
      if dimNat (O ⧸ P) = 0 then (if q = 0 then 1 else 0)
        else Nat.choose (q + dimNat (O ⧸ P) - 1) (dimNat (O ⧸ P) - 1) := by
  classical
  set m := IsLocalRing.maximalIdeal O with hm
  have hPm : P ≤ m := IsLocalRing.le_maximalIdeal Ideal.IsPrime.ne_top'
  obtain ⟨s, y, hqr, hzspan, -, hsle⟩ := exists_adapted_lift P m hPm
  -- `s = dim Ō`
  have hs : s = dimNat (O ⧸ P) := by
    have hmb : m.map (Ideal.Quotient.mk P) = IsLocalRing.maximalIdeal (O ⧸ P) :=
      IsLocalRing.map_maximalIdeal_of_surjective _ Ideal.Quotient.mk_surjective
    have h1 : (IsLocalRing.maximalIdeal (O ⧸ P)).spanFinrank ≤ s := by
      rw [← hmb, ← hzspan]
      refine (Submodule.spanFinrank_span_le_ncard_of_finite (Set.finite_range _)).trans ?_
      rw [← Set.image_univ]
      refine (Set.ncard_image_le Set.finite_univ).trans ?_
      rw [Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fin]
    have h2 := IsRegularLocalRing.spanFinrank_maximalIdeal (R := O ⧸ P)
    have h3 : s = (IsLocalRing.maximalIdeal (O ⧸ P)).spanFinrank := le_antisymm hsle h1
    rw [dimNat, ← h2, h3]
    rfl
  let D : ℕ → Finset (Fin s →₀ ℕ) := fun q => (Finsupp.finite_of_degree_eq q).toFinset
  have hD : ∀ q α, α ∈ D q ↔ α.degree = q := fun q α => by simp [D]
  -- "`gr_{m̄}(Ō)` is a polynomial ring of `r` variables": `τ` maps the homogeneous polynomials of
  -- degree `q` onto `gr^q_{m̄}(Ō)`, so `dim_K gr^q_{m̄}(Ō)` is the number of monomials of degree `q`
  rw [finrank_grPiece_eq_natCard_of_psiTau hPm y hqr hzspan Ideal.IsPrime.ne_top' q, ← hs]
  have hcard : Nat.card {α : Fin s →₀ ℕ // α.degree = q} = (D q).card := by
    rw [← Nat.card_eq_finsetCard]
    exact Nat.card_congr (Equiv.subtypeEquivRight fun α => (hD q α).symm)
  rw [hcard]
  exact card_monomials s q (D q) (hD q)

/-- Corollary 2 (i), second printed step (p. 186): "By Proposition 1, we have an isomorphism of
`K`-modules `Σ_{p+q=i} gr⁰_{m̄}(grᵖ_P(O)) ⊗_K gr^q_{m̄}(Ō) → grⁱ_m(O)` for every non-negative
integer `i`", hence `dim_K grⁿ_m(O) = Σ_{p+q=n} dim_K gr⁰_{m̄}(grᵖ_P(O)) · dim_K gr^q_{m̄}(Ō)`.
Only the existence of a `K`-isomorphism in each degree is used, which is the form of
Proposition 1 that `isNormallyFlatAlongIdeal_of_le` states. -/
private theorem finrank_grPiece_eq_sum_antidiagonal [IsLocalRing O] [IsNoetherianRing O]
    (P m : Ideal O) [P.IsPrime] [m.IsPrime] (hPm : P ≤ m) [IsRegularLocalRing (O ⧸ P)]
    [IsRegularLocalRing (O ⧸ m)] (hP : IsNormallyFlatAlongIdeal P) (n : ℕ) :
    Module.finrank (O ⧸ m) (GrPiece m n) =
      ∑ pq ∈ Finset.HasAntidiagonal.antidiagonal n,
        Module.finrank (O ⧸ m) (GrModPiece m (GrPiece P pq.1) 0) *
          Module.finrank (O ⧸ m) (GrPiece (m.map (Ideal.Quotient.mk P)) pq.2) := by
  classical
  obtain ⟨e⟩ := (isNormallyFlatAlongIdeal_of_le P m hPm hP).1 n
  obtain ⟨s, y, hqr, hzspan, -, -⟩ := exists_adapted_lift P m hPm
  let D : ℕ → Finset (Fin s →₀ ℕ) := fun q => (Finsupp.finite_of_degree_eq q).toFinset
  have hD : ∀ q α, α ∈ D q ↔ α.degree = q := fun q α => by simp [D]
  have : ∀ p, Module.Free (O ⧸ P) (GrPiece P p) := hP
  let b := fun p => Module.Free.chooseBasis (O ⧸ P) (GrPiece P p)
  have hA := fun p => nonempty_basis_grModPiece_zero P m hPm p (b p)
  have hBq := fun q =>
    nonempty_basis_grPiece_map P m hPm (fun j => Ideal.Quotient.mk P (y j)) hqr hzspan D hD q
  have : ∀ p, Module.Free (O ⧸ m) (GrModPiece m (GrPiece P p) 0) :=
    fun p => Module.Free.of_basis (hA p).some
  have : ∀ p, Module.Finite (O ⧸ m) (GrModPiece m (GrPiece P p) 0) :=
    fun p => Module.Finite.of_basis (hA p).some
  have : ∀ q, Module.Free (O ⧸ m) (GrPiece (m.map (Ideal.Quotient.mk P)) q) :=
    fun q => Module.Free.of_basis (hBq q).some
  have : ∀ q, Module.Finite (O ⧸ m) (GrPiece (m.map (Ideal.Quotient.mk P)) q) :=
    fun q => Module.Finite.of_basis (hBq q).some
  rw [← e.finrank_eq, Module.finrank_directSum]
  simp only [Module.finrank_tensorProduct]
  exact (Finset.sum_subtype (Finset.HasAntidiagonal.antidiagonal n)
    (fun x => by simp)
    (fun pq => Module.finrank (O ⧸ m) (GrModPiece m (GrPiece P pq.1) 0) *
      Module.finrank (O ⧸ m) (GrPiece (m.map (Ideal.Quotient.mk P)) pq.2))).symm

section PolynomialConvolution

open Polynomial

/-- The number `C(q+r-1, r-1)` of monomials of degree `q` in `r` variables (`= dim_K gr^q_{m̄}(Ō)`
for `r = dim Ō`, p. 186), with the reading `C(q-1, -1) = 1` if `q = 0` and `0` if `q > 0` for
`r = 0` made in the statement of Corollary 2. -/
private def monomialCount (r q : ℕ) : ℕ :=
  if r = 0 then (if q = 0 then 1 else 0) else Nat.choose (q + r - 1) (r - 1)

private theorem monomialCount_zero_right (r : ℕ) : monomialCount r 0 = 1 := by
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · simp [monomialCount]
  · simp [monomialCount, show r ≠ 0 by omega]

/-- Pascal's rule for the numbers `C(q+r-1, r-1)`: `C(q+r, r) = C(q+r-1, r) + C(q+r-1, r-1)`. -/
private theorem monomialCount_succ_succ (r q : ℕ) :
    monomialCount (r + 1) (q + 1) = monomialCount (r + 1) q + monomialCount r (q + 1) := by
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · simp [monomialCount]
  · simp only [monomialCount, show r + 1 ≠ 0 by omega, show r ≠ 0 by omega, ↓reduceIte,
      Nat.add_sub_cancel]
    rw [show q + 1 + (r + 1) - 1 = (q + r) + 1 by omega, show q + (r + 1) - 1 = q + r by omega,
      show q + 1 + r - 1 = q + r by omega, show r = (r - 1) + 1 by omega, Nat.choose_succ_succ']
    simp only [Nat.add_sub_cancel]
    rw [show q + (r - 1 + 1) = q + r by omega]
    omega

/-- The identity of p. 187: "`Σ_{p+q=n} C(p+s, s) C(q+r-1, r-1) = C(n+s+r, s+r)`". -/
private theorem sum_antidiagonal_choose_mul_monomialCount (s r : ℕ) : ∀ n : ℕ,
    ∑ pq ∈ Finset.HasAntidiagonal.antidiagonal n, (pq.1 + s).choose s * monomialCount r pq.2 =
      (n + s + r).choose (s + r) := by
  induction r with
  | zero =>
    intro n
    rw [Finset.sum_eq_single (n, 0)]
    · simp [monomialCount]
    · rintro ⟨p, q⟩ hpq hne
      have : q ≠ 0 := by
        intro hq
        subst hq
        rw [Finset.HasAntidiagonal.mem_antidiagonal] at hpq
        simp at hpq
        exact hne (by rw [hpq])
      simp [monomialCount, this]
    · intro h
      exact absurd (Finset.HasAntidiagonal.mem_antidiagonal.mpr (by simp)) h
  | succ r ih =>
    intro n
    induction n with
    | zero => simp [monomialCount]
    | succ n ihn =>
      have h1 := Finset.Nat.sum_antidiagonal_succ' (n := n)
        (f := fun pq => (pq.1 + s).choose s * monomialCount (r + 1) pq.2)
      have h2 := Finset.Nat.sum_antidiagonal_succ' (n := n)
        (f := fun pq => (pq.1 + s).choose s * monomialCount r pq.2)
      have h3 := ih (n + 1)
      dsimp only at h1 h2
      simp only [monomialCount_succ_succ, mul_add, Finset.sum_add_distrib,
        monomialCount_zero_right, mul_one] at h1 h2
      have hP : (n + 1 + s + (r + 1)).choose (s + (r + 1)) =
          (n + s + r + 1).choose (s + r) + (n + s + r + 1).choose (s + r + 1) := by
        rw [show n + 1 + s + (r + 1) = (n + s + r + 1) + 1 by omega,
          show s + (r + 1) = (s + r) + 1 by omega]
        exact Nat.choose_succ_succ' (n + s + r + 1) (s + r)
      have e1 : (n + s + (r + 1)).choose (s + (r + 1)) = (n + s + r + 1).choose (s + r + 1) := rfl
      have e2 : (n + 1 + s + r).choose (s + r) = (n + s + r + 1).choose (s + r) := by
        rw [show n + 1 + s + r = n + s + r + 1 by omega]
      have h4 := h2.symm.trans (h3.trans e2)
      have h5 := ihn.trans e1
      rw [h1, hP]
      omega

/-- `deg binomPoly e a ≤ e`. -/
private theorem natDegree_binomPoly_le (e : ℕ) (a : ℚ) : (binomPoly e a).natDegree ≤ e := by
  unfold binomPoly
  refine (natDegree_C_mul_le _ _).trans ?_
  rw [natDegree_prod_of_monic _ _ fun i _ => monic_X_add_C _]
  simp only [natDegree_X_add_C]
  simp

/-- "We can write `F⁰(n) = a₀ C(n+s, n) + a₁ C(n+s-1, s-1) + ⋯ + a_s`" (p. 186): a polynomial of
degree `≤ s` is a combination of the polynomials `n ↦ C(n+s-k, s-k)`, with `a₀ = s!` times the
coefficient of `Tˢ`. -/
private theorem exists_eq_sum_binomPoly (s : ℕ) : ∀ f : ℚ[X], f.natDegree ≤ s →
    ∃ a : ℕ → ℚ, a 0 = (s.factorial : ℚ) * f.coeff s ∧
      f = ∑ k ∈ Finset.range (s + 1), C (a k) * binomPoly (s - k) 0 := by
  induction s with
  | zero =>
    intro f hf
    refine ⟨fun _ => f.coeff 0, by simp, ?_⟩
    rw [Polynomial.eq_C_of_natDegree_le_zero hf]
    simp [binomPoly]
  | succ s ih =>
    intro f hf
    set a₀ : ℚ := ((s + 1).factorial : ℚ) * f.coeff (s + 1) with ha₀
    set g : ℚ[X] := f - C a₀ * binomPoly (s + 1) 0 with hg
    have hgdeg : g.natDegree ≤ s := by
      rw [natDegree_le_iff_coeff_eq_zero]
      intro N hN
      rw [hg, coeff_sub, coeff_C_mul]
      rcases Nat.lt_or_ge (s + 1) N with h | h
      · have h1 : f.coeff N = 0 := coeff_eq_zero_of_natDegree_lt (by omega)
        have h2 : (binomPoly (s + 1) 0).coeff N = 0 :=
          coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt (natDegree_binomPoly_le _ _) h)
        rw [h1, h2]; ring
      · have : N = s + 1 := by omega
        subst this
        rw [coeff_binomPoly, ha₀]
        have : ((s + 1).factorial : ℚ) ≠ 0 := by positivity
        field_simp
        ring
    obtain ⟨b, hb0, hb⟩ := ih g hgdeg
    refine ⟨fun k => if k = 0 then a₀ else b (k - 1), by simp [ha₀], ?_⟩
    rw [Finset.sum_range_succ']
    simp only [↓reduceIte, Nat.sub_zero, Nat.add_sub_cancel, add_eq_zero, one_ne_zero, and_false,
      Nat.add_sub_add_right]
    have : f = g + C a₀ * binomPoly (s + 1) 0 := by rw [hg]; ring
    conv_lhs => rw [this, hb]

/-- The correction term of p. 187: `Σ_{p<N} (F(p) - F⁰(p)) C(n-p+r-1, r-1)`, as a polynomial in
`n` of degree `≤ r - 1` ("the constant zero if `r = 0`"). -/
private noncomputable def convCorrection (r N : ℕ) (F : ℕ → ℚ) (pF : ℚ[X]) : ℚ[X] :=
  ∑ p ∈ Finset.range N, C (F p - pF.eval (p : ℚ)) *
    (if r = 0 then 0 else binomPoly (r - 1) (-(p : ℚ)))

private theorem natDegree_convCorrection_le (r N : ℕ) (F : ℕ → ℚ) (pF : ℚ[X]) :
    (convCorrection r N F pF).natDegree ≤ r := by
  refine natDegree_sum_le_of_forall_le _ _ fun p _ => (natDegree_C_mul_le _ _).trans ?_
  split_ifs
  · simp
  · exact (natDegree_binomPoly_le _ _).trans (by omega)

private theorem coeff_convCorrection (r N : ℕ) (F : ℕ → ℚ) (pF : ℚ[X]) (j : ℕ) (hj : r ≤ j) :
    (convCorrection r N F pF).coeff j = 0 ∧ (r = 0 → convCorrection r N F pF = 0) := by
  refine ⟨?_, fun h => by simp [convCorrection, h]⟩
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · simp [convCorrection]
  · refine coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt ?_ (show r - 1 < j by omega))
    refine natDegree_sum_le_of_forall_le _ _ fun p _ => (natDegree_C_mul_le _ _).trans ?_
    simp only [show r ≠ 0 by omega, ↓reduceIte]
    exact natDegree_binomPoly_le _ _

private theorem eval_convCorrection (r N : ℕ) (F : ℕ → ℚ) (pF : ℚ[X]) (n : ℕ) (hn : N ≤ n) :
    (convCorrection r N F pF).eval (n : ℚ) =
      ∑ p ∈ Finset.range N, (F p - pF.eval (p : ℚ)) * (monomialCount r (n - p) : ℚ) := by
  unfold convCorrection
  rw [eval_finsetSum]
  refine Finset.sum_congr rfl fun p hp => ?_
  have hpn : p ≤ n := by have := Finset.mem_range.mp hp; omega
  rw [eval_mul, eval_C]
  congr 1
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · have : n - p ≠ 0 := by have := Finset.mem_range.mp hp; omega
    simp [monomialCount, this]
  · simp only [show r ≠ 0 by omega, ↓reduceIte, monomialCount]
    rw [eval_binomPoly (r - 1) (n - p) n (-(p : ℚ)) (by rw [Nat.cast_sub hpn]; ring)]
    rw [show n - p + (r - 1) = n - p + r - 1 by omega]

/-- Corollary 2 (ii), the printed argument (pp. 186–187), as a statement on polynomials.
`F⁰ = pF` is a polynomial with `F⁰(n) = F(n)` for large `n` and degree `≤ s`; write
`F⁰(n) = a₀ C(n+s, n) + a₁ C(n+s-1, s-1) + ⋯ + a_s`.  Let `G(n) = Σ_{p+q=n} F(p) C(q+r-1, r-1)`.
Then `G⁰(n) - Σ_{p+q=n} F⁰(p) C(q+r-1, r-1)` "is equal to a polynomial of degree `≤ r - 1` and to
the constant zero if `r = 0`" (as is easily seen: a gap that Lean fills, it is
`convCorrection`), and by `Σ_{p+q=n} C(p+s, s) C(q+r-1, r-1) = C(n+s+r, s+r)` one gets
`G⁰(n) = a₀ C(n+s+r, s+r) + a₁ C(n+s+r-1, s+r-1) + ⋯`; hence `G⁰` has degree `≤ s + r` and the
coefficient of `T^{s+r}` is `a₀/(s+r)!` with `a₀ = s! ·` (coefficient of `Tˢ` in `F⁰`). -/
private theorem exists_poly_convolution (r s N : ℕ) (F : ℕ → ℚ) (pF : ℚ[X])
    (hdeg : pF.natDegree ≤ s) (hF : ∀ n, N ≤ n → pF.eval (n : ℚ) = F n) (G : ℕ → ℚ)
    (hG : ∀ n, G n = ∑ pq ∈ Finset.HasAntidiagonal.antidiagonal n,
      F pq.1 * (monomialCount r pq.2 : ℚ)) :
    ∃ pG : ℚ[X], (∀ n, N ≤ n → pG.eval (n : ℚ) = G n) ∧ pG.natDegree ≤ s + r ∧
      pG.coeff (s + r) = (s.factorial : ℚ) * pF.coeff s / ((s + r).factorial : ℚ) := by
  classical
  -- "We can write `F⁰(n) = a₀ C(n+s, n) + a₁ C(n+s-1, s-1) + ⋯ + a_s`"
  obtain ⟨a, ha0, hpF⟩ := exists_eq_sum_binomPoly s pF hdeg
  let M : ℚ[X] := ∑ k ∈ Finset.range (s + 1), C (a k) * binomPoly (s + r - k) 0
  refine ⟨M + convCorrection r N F pF, ?_, ?_, ?_⟩
  · intro n hn
    -- `F⁰(p) = Σ_k a_k C(p+s-k, s-k)`
    have h1 : ∀ p : ℕ, pF.eval (p : ℚ) =
        ∑ k ∈ Finset.range (s + 1), a k * (((p + (s - k)).choose (s - k) : ℕ) : ℚ) := by
      intro p
      conv_lhs => rw [hpF]
      rw [eval_finsetSum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [eval_mul, eval_C, eval_binomPoly (s - k) p p 0 (by simp)]
    -- "`Σ_{p+q=n} C(p+s, s) C(q+r-1, r-1) = C(n+s+r, s+r)`" applied termwise
    have h2 : ∑ pq ∈ Finset.HasAntidiagonal.antidiagonal n,
        pF.eval (pq.1 : ℚ) * (monomialCount r pq.2 : ℚ) = M.eval (n : ℚ) := by
      simp only [h1, Finset.sum_mul]
      rw [Finset.sum_comm]
      simp only [M, eval_finsetSum, eval_mul, eval_C]
      refine Finset.sum_congr rfl fun k hk => ?_
      have hk' : k ≤ s := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
      rw [eval_binomPoly (s + r - k) n n 0 (by simp)]
      have hV := sum_antidiagonal_choose_mul_monomialCount (s - k) r n
      have hV' : ∑ pq ∈ Finset.HasAntidiagonal.antidiagonal n,
          ((((pq.1 + (s - k)).choose (s - k) : ℕ) : ℚ) * (monomialCount r pq.2 : ℚ)) =
          (((n + (s - k) + r).choose ((s - k) + r) : ℕ) : ℚ) := by exact_mod_cast hV
      rw [show s + r - k = (s - k) + r by omega]
      simp only [mul_assoc, ← Finset.mul_sum]
      rw [hV', show n + (s - k + r) = n + (s - k) + r by omega]
    -- the difference `Σ (F(p) - F⁰(p)) C(n-p+r-1, r-1)` only involves `p < N`
    have h3 : ∑ pq ∈ Finset.HasAntidiagonal.antidiagonal n,
        (F pq.1 - pF.eval (pq.1 : ℚ)) * (monomialCount r pq.2 : ℚ) =
        (convCorrection r N F pF).eval (n : ℚ) := by
      rw [eval_convCorrection r N F pF n hn,
        Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk
          (fun pq => (F pq.1 - pF.eval (pq.1 : ℚ)) * (monomialCount r pq.2 : ℚ)) n]
      refine (Finset.sum_subset (fun p hp => ?_) (fun p hp hpN => ?_)).symm
      · exact Finset.mem_range.mpr (by have := Finset.mem_range.mp hp; omega)
      · have : N ≤ p := by simpa using hpN
        simp [hF p this]
    rw [eval_add, ← h2, ← h3, hG n, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun pq _ => by ring
  · refine (natDegree_add_le _ _).trans (max_le ?_ ?_)
    · refine natDegree_sum_le_of_forall_le _ _ fun k hk => (natDegree_C_mul_le _ _).trans ?_
      exact (natDegree_binomPoly_le _ _).trans (by omega)
    · exact (natDegree_convCorrection_le r N F pF).trans (by omega)
  · rw [coeff_add, (coeff_convCorrection r N F pF (s + r) (by omega)).1, add_zero]
    simp only [M, finsetSum_coeff, coeff_C_mul]
    rw [Finset.sum_eq_single 0]
    · rw [Nat.sub_zero, coeff_binomPoly, ha0]
      field_simp
    · intro k hk hk0
      have hks : k ≤ s := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
      rw [coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt (natDegree_binomPoly_le _ _)
        (show s + r - k < s + r by omega)), mul_zero]
    · intro h
      exact absurd (Finset.mem_range.mpr (Nat.succ_pos s)) h

end PolynomialConvolution

/-- Corollary 2 of Proposition 1, p. 186: "Let `O` be a local ring with the maximal ideal `m`.
Let `P` be a prime ideal in `O` such that `Ō = O/P` is regular and that `gr_P(O)` is flat over
`Ō`. Let `r = dim Ō`. Then the following are true: (i) Let `F(n)` be the function of
non-negative integers `n` defined by `F(n) = Σ_{i≤n} dim_{O_P/PO_P}(grⁱ_{PO_P}(O_P))`. Then we
have `Σ_{p+q=n} F(p)·C(q+r−1, r−1) = Σ_{i≤n} dim_K(grⁱ_m(O))` where `K = O/m`. (ii) The local
rings `O` and `O_P` have the same multiplicity."

Encoding: `F = hilbertSamuel (Localization.AtPrime P)` and the right-hand side of (i) is
`hilbertSamuel O n` (p. 133); `r = dimNat (O ⧸ P)`; multiplicities are `samuelMultiplicity`.
The binomial coefficient `C(q+r−1, r−1)` is `dim_K gr^q_{m̄}(Ō)`, the number of monomials of
degree `q` in `r` variables (p. 186).

Deviation from the paper (statement modified): for `r = 0` the paper's `C(q−1, −1)` is read
with the convention `C(q−1, −1) = 1` if `q = 0` and `= 0` if `q > 0` (then `Ō = K`,
`gr_{m̄}(Ō) = K` and (i) reads `F(n) = Σ_{i≤n} dim_K grⁱ_m(O)`, in accordance with the proof
on p. 187, where the correction term is "the constant zero if `r = 0`"); with the convention
`C(n, −1) = 0` the printed (i) would be false for `r = 0`, and natural-number subtraction would
give `C(q−1, 0) = 1`, so this case is written out explicitly.

Proof of (i), as printed (the first and the third step use the printed isomorphisms): `dim_{O_P/PO_P} grᵖ_{PO_P}(O_P) =
dim_K gr⁰_{m̄}(grᵖ_P(O))` (`finrank_grPiece_localization_eq`: "the localization `gr_P(O)_P` of
`gr_P(O)` with respect to `P` is canonically isomorphic to `gr_{PO_P}(O_P)`" is the isomorphism of
p. 181, in degree `p` `GrPiece.nonempty_baseChange_equiv`, and `grᵖ_P(O)` is a free `Ō`-module),
the `K`-isomorphism of Proposition 1 in each degree `i`, which gives
`dim_K grⁱ_m(O) = Σ_{p+q=i} dim_K gr⁰_{m̄}(grᵖ_P(O)) · dim_K gr^q_{m̄}(Ō)`
(`finrank_grPiece_eq_sum_antidiagonal`), `dim_K gr^q_{m̄}(Ō) = C(q+r−1, r−1)`
(`finrank_grPiece_map_eq_choose`: "`gr_{m̄}(Ō)` is a polynomial ring of `r` variables" is the ring
isomorphism `psiTau_bijective`, `K[X̄₁, …, X̄_r] ≅ gr_{m̄}(Ō)`, which maps the homogeneous polynomials
of degree `q` onto `gr^q_{m̄}(Ō)`, `finrank_grPiece_eq_natCard_of_psiTau`), and summation over
`i ≤ n`.  Only the existence of a `K`-isomorphism in each degree is used, as printed.

Proof of (ii), as printed:
`F⁰` is the polynomial with `F⁰(n) = F(n)` for large `n`, of degree `s = dim O_P` (Samuel's theorem,
`exists_hilbertSamuelPoly`, cited), and "We can write `F⁰(n) = a₀ C(n+s, n) + a₁ C(n+s-1, s-1) +
⋯ + a_s`" (`exists_eq_sum_binomPoly`); "as is easily seen, `G⁰(n) - Σ_{p+q=n} F⁰(p) C(q+r-1, r-1)` is
equal to a polynomial of degree `≤ r - 1` and to the constant zero if `r = 0`" (`convCorrection`:
a gap that Lean fills); "by using the formula `Σ_{p+q=n} C(p+s, s) C(q+r-1, r-1) = C(n+s+r, s+r)`"
(`sum_antidiagonal_choose_mul_monomialCount`) "we get `G⁰(n) = a₀ C(n+s+r, s+r) + ⋯`"
(`exists_poly_convolution`); "Therefore the multiplicity of `O` is equal to `a₀`": by (i) `G = H_O`,
so `G⁰` is the Hilbert–Samuel polynomial of `O`, of degree `dim O` (Samuel again), hence
`dim O = s + r` (a gap that Lean fills: the paper uses `deg G⁰ = dim O` tacitly) and
`e(O) = (s+r)! · a₀/(s+r)! = a₀ = e(O_P)`.

Paper misprint (p. 187, in the proof of (ii)): the paper prints
`Σ_{p+q=n} F⁰(p) C(p+q−1, r−1)`; `C(q+r−1, r−1)` is meant. -/
@[blueprint "cor:II.1-prop1-2"
  (statement := /-- Let $O$ be a local ring with the maximal ideal $\mathfrak m$. Let $P$ be a
    prime ideal in $O$ such that $\bar O=O/P$ is regular and that $\operatorname{gr}_P(O)$ is
    flat over $\bar O$. Let $r=\dim\bar O$. Then the following are true: (i) Let $F(n)$ be
    the function of non-negative integers $n$ defined by
    $F(n)=\sum_{i=0}^n\dim_{O_P/PO_P}(\operatorname{gr}^i_{PO_P}(O_P))$
    (\cref{def:hilbert-samuel-function}). Then we have
    $\sum_{p+q=n}F(p)\binom{q+r-1}{r-1}=\sum_{i=0}^n\dim_K(\operatorname{gr}^i_{\mathfrak m}(O))$
    where $K=O/\mathfrak m$. (ii) The local rings $O$ and $O_P$ have the same multiplicity
    (\cref{def:multiplicity}). (p.~186.)

    \textbf{Deviation from the paper (statement modified).} For $r=0$ the printed coefficient
    $\binom{q-1}{-1}$ is read as $1$ if $q=0$ and $0$ if $q>0$, i.e.\ as
    $\dim_K\operatorname{gr}^q_{\bar{\mathfrak m}}(\bar O)$ for $\bar O=K$ (as the paper's proof
    requires; with the convention $\binom{n}{-1}=0$ statement (i) would be false for $r=0$). -/)
  (proof := /-- (The paper's proof, pp.~186--187.) The localization $\operatorname{gr}_P(O)_P$ is canonically
    $\operatorname{gr}_{PO_P}(O_P)$; since $\operatorname{gr}^p_P(O)$ is a free
    $\bar O$-module, $\dim_{O_P/PO_P}\operatorname{gr}^p_{PO_P}(O_P)=\dim_K
    \operatorname{gr}^0_{\bar{\mathfrak m}}(\operatorname{gr}^p_P(O))$. By
    \cref{prop:II.1-1} there is an isomorphism of $K$-modules
    $\bigoplus_{p+q=i}\operatorname{gr}^0_{\bar{\mathfrak m}}(\operatorname{gr}^p_P(O))
    \otimes_K\operatorname{gr}^q_{\bar{\mathfrak m}}(\bar O)\cong\operatorname{gr}^i_{\mathfrak
    m}(O)$ for every $i$, and $\operatorname{gr}_{\bar{\mathfrak m}}(\bar O)$ is a polynomial
    ring in $r$ variables, so $\dim_K\operatorname{gr}^q_{\bar{\mathfrak m}}(\bar O)=
    \binom{q+r-1}{r-1}$; summing over $i\le n$ gives (i). For (ii), let $G(n)$ be the left
    side of (i), $F^0$ the polynomial equal to $F$ for large $n$, written
    $F^0(n)=a_0\binom{n+s}{s}+a_1\binom{n+s-1}{s-1}+\dots+a_s$ with $s=\dim O_P$, so that
    $e(O_P)=a_0$. The polynomial $G^0$ agreeing with $G$ for large $n$ differs from
    $\sum_{p+q=n}F^0(p)\binom{q+r-1}{r-1}$ by a polynomial of degree $\le r-1$ (the constant
    zero if $r=0$), and $\sum_{p+q=n}\binom{p+s}{s}\binom{q+r-1}{r-1}=\binom{n+s+r}{s+r}$
    gives $G^0(n)=a_0\binom{n+s+r}{s+r}+a_1\binom{n+s+r-1}{s+r-1}+\dots$; hence
    $e(O)=a_0=e(O_P)$.

    \textbf{Paper misprint.} On p.~187 the paper prints
    $\sum_{p+q=n}F^0(p)\binom{p+q-1}{r-1}$; $\binom{q+r-1}{r-1}$ is meant (as above).

    \textbf{Proof of (i) in Lean (as printed).} The Lean proof of (i) follows the paper: the
    dimensions $\dim_{O_P/PO_P}\operatorname{gr}^p_{PO_P}(O_P)$ and
    $\dim_K\operatorname{gr}^0_{\bar{\mathfrak m}}(\operatorname{gr}^p_P(O))$ agree (the
    canonical isomorphism $\operatorname{gr}_P(O)_P\cong\operatorname{gr}_{PO_P}(O_P)$ of
    p.~181, in each degree, and the freeness of $\operatorname{gr}^p_P(O)$ over $\bar O$), the
    isomorphism of $K$-modules of \cref{prop:II.1-1} in each degree $i$ gives
    $\dim_K\operatorname{gr}^i_{\mathfrak m}(O)=\sum_{p+q=i}\dim_K
    \operatorname{gr}^0_{\bar{\mathfrak m}}(\operatorname{gr}^p_P(O))\cdot\dim_K
    \operatorname{gr}^q_{\bar{\mathfrak m}}(\bar O)$, and $\dim_K\operatorname{gr}^q_{\bar{\mathfrak
    m}}(\bar O)=\binom{q+r-1}{r-1}$ (the polynomial ring $K[\bar X_1,\dots,\bar X_r]\cong
    \operatorname{gr}_{\bar{\mathfrak m}}(\bar O)$ of p.~183, as a ring isomorphism, maps the
    homogeneous polynomials of degree $q$ onto $\operatorname{gr}^q_{\bar{\mathfrak m}}(\bar
    O)$); only the existence of a $K$-isomorphism in each degree is used.

    \textbf{Proof of (ii) in Lean (as printed).} The Lean proof of (ii) follows the paper: $F^0$
    (degree $s=\dim O_P$, Samuel's theorem, cited) is expanded as
    $F^0(n)=a_0\binom{n+s}{n}+a_1\binom{n+s-1}{s-1}+\dots+a_s$; the difference
    $G^0(n)-\sum_{p+q=n}F^0(p)\binom{q+r-1}{r-1}$ is a polynomial of degree $\le r-1$ (the constant
    zero if $r=0$); the formula $\sum_{p+q=n}\binom{p+s}{s}\binom{q+r-1}{r-1}=\binom{n+s+r}{s+r}$ gives
    $G^0(n)=a_0\binom{n+s+r}{s+r}+\dots$; and since $G=H_O$ by (i), $G^0$ is the Hilbert--Samuel
    polynomial of $O$, so $\dim O=s+r$ and $e(O)=a_0=e(O_P)$.

    \textbf{Gaps filled.} (a) ``as is easily seen'' (p.~187), that $G^0(n)-\sum_{p+q=n}F^0(p)
    \binom{q+r-1}{r-1}$ is a polynomial of degree $\le r-1$ and the constant zero if $r=0$: it
    equals $\sum_{p<N}(F(p)-F^0(p))\binom{n-p+r-1}{r-1}$ for $n\ge N$, where $F=F^0$ from $N$ on.
    (b) The expansion of $F^0$ in the polynomials $\binom{n+s-k}{s-k}$ and the formula
    $\sum_{p+q=n}\binom{p+s}{s}\binom{q+r-1}{r-1}=\binom{n+s+r}{s+r}$, stated without proof, are
    proved (induction on the degree, resp.\ on $r$ and $n$ with Pascal's rule). (c) That
    $\deg G^0=\dim O$, i.e.\ $\dim O=\dim O_P+r$, used tacitly to conclude ``the multiplicity of $O$
    is equal to $a_0$'', follows from Samuel's theorem for $O$. (d) ``We know that
    $\operatorname{gr}_{\bar{\mathfrak m}}(\bar O)$ is a polynomial ring of $r$ variables, and
    hence $\dim_K(\operatorname{gr}^q_{\bar{\mathfrak m}}(\bar O))=\binom{q+r-1}{r-1}$'' tacitly
    uses that the identification with the polynomial ring is graded: Lean proves that
    $K[\bar X]\to\operatorname{gr}_{\bar{\mathfrak m}}(\bar O)$ maps the homogeneous polynomials
    of degree $q$ onto $\operatorname{gr}^q_{\bar{\mathfrak m}}(\bar O)$. (e) The isomorphism
    $\operatorname{gr}_P(O)_P\cong\operatorname{gr}_{PO_P}(O_P)$ (``in general'', p.~186) is the
    one of p.~181, which the paper asserts without proof; Lean proves it by flat base change. -/)
  (latexEnv := "corollary")]
theorem hilbertSamuel_formula_and_samuelMultiplicity_eq_localization [Hironaka.Cited.ExistsHilbertSamuelPoly.{u}] [IsLocalRing O]
    [IsNoetherianRing O] (P : Ideal O) [P.IsPrime] [IsRegularLocalRing (O ⧸ P)]
    (hP : IsNormallyFlatAlongIdeal P) :
    (∀ n : ℕ, ∑ pq ∈ Finset.HasAntidiagonal.antidiagonal n,
        hilbertSamuel (Localization.AtPrime P) pq.1 *
          (if dimNat (O ⧸ P) = 0 then (if pq.2 = 0 then 1 else 0)
            else Nat.choose (pq.2 + dimNat (O ⧸ P) - 1) (dimNat (O ⧸ P) - 1)) =
      hilbertSamuel O n) ∧
    samuelMultiplicity O = samuelMultiplicity (Localization.AtPrime P) := by
  classical
  set m := IsLocalRing.maximalIdeal O with hm
  have hPm : P ≤ m := IsLocalRing.le_maximalIdeal Ideal.IsPrime.ne_top'
  let _ : Field (O ⧸ m) := Ideal.Quotient.field m
  have : IsRegularLocalRing (O ⧸ m) := inferInstance
  -- (i), p. 186: `dim_K gr⁰_{m̄}(grᵖ_P(O))` and `dim_K gr^q_{m̄}(Ō)`
  let r : ℕ → ℕ := fun p => Module.finrank (O ⧸ m) (GrModPiece m (GrPiece P p) 0)
  let b : ℕ → ℕ := fun q => Module.finrank (O ⧸ m) (GrPiece (m.map (Ideal.Quotient.mk P)) q)
  -- "`dim_K(gr^q_{m̄}(Ō)) = C(q+r-1, r-1)`"
  have hb : ∀ q, b q = if dimNat (O ⧸ P) = 0 then (if q = 0 then 1 else 0)
      else Nat.choose (q + dimNat (O ⧸ P) - 1) (dimNat (O ⧸ P) - 1) :=
    finrank_grPiece_map_eq_choose P
  -- "By Proposition 1 ... `H_O(n) = Σ_{i ≤ n} Σ_{p+q=i} r_p b_q`"
  have hHO : ∀ n, hilbertSamuel O n =
      ∑ j ∈ Finset.range (n + 1), ∑ p ∈ Finset.range (j + 1), r p * b (j - p) := by
    intro n
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [finrank_grPiece_eq_sum_antidiagonal P m hPm hP j,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun p q => r p * b q) j]
  -- "`dim_{O_P/PO_P}(grᵖ_{PO_P}(O_P)) = dim_K(gr⁰_{m̄}(grᵖ_P(O)))`", so `F(p) = Σ_{i ≤ p} r_i`
  have hHL : ∀ p, hilbertSamuel (Localization.AtPrime P) p = ∑ i ∈ Finset.range (p + 1), r i := by
    intro p
    refine Finset.sum_congr rfl fun i _ => ?_
    exact finrank_grPiece_localization_eq P m hPm hP i
  have hi : ∀ n : ℕ, ∑ pq ∈ Finset.HasAntidiagonal.antidiagonal n,
      hilbertSamuel (Localization.AtPrime P) pq.1 *
        (if dimNat (O ⧸ P) = 0 then (if pq.2 = 0 then 1 else 0)
          else Nat.choose (pq.2 + dimNat (O ⧸ P) - 1) (dimNat (O ⧸ P) - 1)) =
      hilbertSamuel O n := by
    intro n
    rw [hHO, ← sum_antidiagonal_sum_range_eq r b n]
    refine Finset.sum_congr rfl fun pq _ => ?_
    rw [hHL, hb]
  refine ⟨hi, ?_⟩
  -- (ii), pp. 186-187: "Let `F⁰(n)` be the polynomial such that `F⁰(n) = F(n)` for all
  -- sufficiently large integer `n`", of degree `s = dim O_P` (Samuel's theorem, cited)
  obtain ⟨pL, hpL, hdegL, eL, heL, hlcL⟩ := exists_hilbertSamuelPoly (Localization.AtPrime P)
  obtain ⟨pO, hpO, hdegO, eO, heO, hlcO⟩ := exists_hilbertSamuelPoly O
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hpL
  -- "`G(n) = Σ_{p+q=n} F(p) C(q+r-1, r-1)`", which is `H_O(n)` by (i)
  have hi' : ∀ n : ℕ, (hilbertSamuel O n : ℚ) =
      ∑ pq ∈ Finset.HasAntidiagonal.antidiagonal n,
        (hilbertSamuel (Localization.AtPrime P) pq.1 : ℚ) *
          (monomialCount (dimNat (O ⧸ P)) pq.2 : ℚ) := by
    intro n
    have h := congrArg (Nat.cast : ℕ → ℚ) (hi n)
    rw [Nat.cast_sum] at h
    simp only [Nat.cast_mul] at h
    exact h.symm
  -- "`G⁰(n) - Σ F⁰(p) C(q+r-1, r-1)` is a polynomial of degree `≤ r - 1`", the identity
  -- `Σ_{p+q=n} C(p+s, s) C(q+r-1, r-1) = C(n+s+r, s+r)`, and the expansion of `F⁰`
  obtain ⟨pG, hpG, hdegG, hcoefG⟩ := exists_poly_convolution (dimNat (O ⧸ P))
    (dimNat (Localization.AtPrime P)) N (fun p => (hilbertSamuel (Localization.AtPrime P) p : ℚ))
    pL hdegL.le hN (fun n => (hilbertSamuel O n : ℚ)) hi'
  have hevL : pL = hilbertSamuelPoly (Localization.AtPrime P) :=
    hilbertSamuelPoly_unique _ hpL (hilbertSamuelPoly_spec _)
  have hevG : pG = hilbertSamuelPoly O :=
    hilbertSamuelPoly_unique O (Filter.eventually_atTop.mpr ⟨N, hpG⟩) (hilbertSamuelPoly_spec O)
  have hevO : pO = pG := hilbertSamuelPoly_unique O hpO (Filter.eventually_atTop.mpr ⟨N, hpG⟩)
  -- `a₀ = s! · (leading coefficient of F⁰) = e(O_P) ≠ 0`
  have hcL : pL.coeff (dimNat (Localization.AtPrime P)) = pL.leadingCoeff := by
    rw [← hdegL]
    rfl
  have hcoefG' : pG.coeff (dimNat (Localization.AtPrime P) + dimNat (O ⧸ P)) =
      (eL : ℚ) / ((dimNat (Localization.AtPrime P) + dimNat (O ⧸ P)).factorial : ℚ) := by
    rw [hcoefG, hcL, ← hlcL]
  have hne : pG.coeff (dimNat (Localization.AtPrime P) + dimNat (O ⧸ P)) ≠ 0 := by
    rw [hcoefG']
    have : (0 : ℚ) < eL := by exact_mod_cast heL
    positivity
  -- "Therefore the multiplicity of `O` is equal to `a₀`": `G⁰` has degree `s + r = dim O`
  have hdimO : dimNat O = dimNat (Localization.AtPrime P) + dimNat (O ⧸ P) := by
    rw [← hdegO, hevO]
    exact le_antisymm hdegG (Polynomial.le_natDegree_of_ne_zero hne)
  have hO : ((dimNat O).factorial : ℚ) * pG.coeff (dimNat O) = eL := by
    rw [hdimO, hcoefG']
    have : ((dimNat (Localization.AtPrime P) + dimNat (O ⧸ P)).factorial : ℚ) ≠ 0 := by positivity
    field_simp
  have hL : ((dimNat (Localization.AtPrime P)).factorial : ℚ) *
      pL.coeff (dimNat (Localization.AtPrime P)) = eL := by
    rw [hcL]
    exact hlcL
  unfold samuelMultiplicity
  rw [← hevG, ← hevL, hO, hL]

end Prop1

/-! ### The scheme-theoretic corollaries of Proposition 1 (pp. 185–188) -/

namespace Subscheme

variable {X : Scheme.{u}} [IsAlgebraicScheme X]

/-- At a point `x` of a non-singular subscheme `W`, `O_{X,x}/W_x ≅ O_{W,x}` is regular. -/
private theorem isRegularLocalRing_stalk_quot {X : Scheme.{u}} (W : Subscheme X)
    (hW : W.IsNonsingular) {x : X} (hx : x ∈ W.pts) :
    IsRegularLocalRing (X.presheaf.stalk x ⧸ W.stalkIdeal x) := by
  have hx' : x ∈ Set.range W.ι := by
    rw [Scheme.IdealSheafData.range_subschemeι]
    exact hx
  obtain ⟨y, rfl⟩ := hx'
  obtain ⟨e⟩ := nonempty_stalk_quot_equiv W y
  have : IsRegularLocalRing (W.toScheme.presheaf.stalk y) := hW y
  exact IsRegularLocalRing.of_ringEquiv e.symm

/-- At a point `x` of a non-singular subscheme `W`, the stalk `W_x` is a prime ideal. -/
private theorem isPrime_stalkIdeal {X : Scheme.{u}} (W : Subscheme X) (hW : W.IsNonsingular)
    {x : X} (hx : x ∈ W.pts) : (W.stalkIdeal x).IsPrime := by
  have := isRegularLocalRing_stalk_quot W hW hx
  have := isDomain_of_isRegularLocalRing (X.presheaf.stalk x ⧸ W.stalkIdeal x)
  exact (Ideal.Quotient.isDomain_iff_prime _).mp this

/-- Containment of subschemes gives the reverse inclusion of the stalks of the ideal
sheaves. -/
private theorem stalkIdeal_le_of_isContainedIn {X : Scheme.{u}} {W W₁ : Subscheme X}
    (h : W₁.IsContainedIn W) (x : X) : W.stalkIdeal x ≤ W₁.stalkIdeal x :=
  Ideal.span_mono fun _ ⟨U, hxU, s, hs, hsa⟩ => ⟨U, hxU, s, h U hs, hsa⟩

/-- Corollary 1 of Proposition 1, p. 185: "Let `V` be an algebraic scheme and `W` a non-singular
subscheme of `V`. Suppose `V` be normally flat along `W`. Then, for every non-singular
subscheme `W₁` of `W`, `V` is normally flat along `W₁`." -/
@[blueprint "cor:II.1-prop1-1"
  (statement := /-- Let $V$ be an algebraic scheme and $W$ a non-singular subscheme of $V$.
    Suppose $V$ be normally flat along $W$ (\cref{def:0.1-normally-flat}). Then, for every
    non-singular subscheme $W_1$ of $W$, $V$ is normally flat along $W_1$. (p.~185.) -/)
  (proof := /-- Let $x$ be any point of $W_1$. Let $O$ be the local ring of $V$ at $x$, $P$
    the prime ideal in $O$ defining the subscheme $W$, and $\mathfrak m$ the prime ideal in
    $O$ defining the subscheme $W_1$. Then by assumption, $\operatorname{gr}_P(O)$ is flat
    over $\bar O=O/P$. Hence by \cref{prop:II.1-1}, $\operatorname{gr}_{\mathfrak m}(O)$ is
    flat over $K=O/\mathfrak m$. Thus $V$ is normally flat along $W_1$. -/)
  (latexEnv := "corollary")]
theorem isNormallyFlatAlong_of_isContainedIn (W : Subscheme X) (hW : W.IsNonsingular)
    (h : W.IsNormallyFlatAlong) (W₁ : Subscheme X) (hW₁ : W₁.IsContainedIn W)
    (hW₁' : W₁.IsNonsingular) : W₁.IsNormallyFlatAlong := by
  intro x hx
  have hxW : x ∈ W.pts := pts_subset_of_isContainedIn hW₁ hx
  refine ⟨hx, ?_⟩
  have := IsAlgebraicScheme.isNoetherian X
  have := isRegularLocalRing_stalk_quot W hW hxW
  have := isRegularLocalRing_stalk_quot W₁ hW₁' hx
  have := isPrime_stalkIdeal W hW hxW
  have := isPrime_stalkIdeal W₁ hW₁' hx
  exact (isNormallyFlatAlongIdeal_of_le _ _ (stalkIdeal_le_of_isContainedIn hW₁ x)
    (h x hxW).2).2

/-- The local ring of `X` at the generic point `ξ` of `W` is `(O_{X,x})_{W_x}` for every `x ∈ W`
(when `W_x` is prime). -/
private theorem nonempty_stalk_equiv_localization {X : Scheme.{u}} (W : Subscheme X)
    {ξ : X} (hξ : IsGenericPoint ξ W.pts) {x : X} (hx : x ∈ W.pts)
    [hq : (W.stalkIdeal x).IsPrime] :
    Nonempty (X.presheaf.stalk ξ ≃+* Localization.AtPrime (W.stalkIdeal x)) := by
  have hspec : ξ ⤳ x := by
    rw [specializes_iff_mem_closure, hξ.def]
    exact hx
  obtain ⟨_, ⟨U, hU₀, rfl⟩, hxU, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  have hU : IsAffineOpen U := hU₀
  have hξU : ξ ∈ U := hspec.mem_open U.isOpen hxU
  have hxr : x ∈ Set.range hU.fromSpec := by rw [hU.range_fromSpec]; exact hxU
  have hξr : ξ ∈ Set.range hU.fromSpec := by rw [hU.range_fromSpec]; exact hξU
  obtain ⟨px, rfl⟩ := hxr
  obtain ⟨pξ, rfl⟩ := hξr
  have hle : pξ.asIdeal ≤ px.asIdeal :=
    (PrimeSpectrum.le_iff_specializes (x := pξ) (y := px)).mpr
      ((hU.fromSpec.isOpenEmbedding.isInducing.specializes_iff).mp hspec)
  let _ : Algebra Γ(X, U) (X.presheaf.stalk (hU.fromSpec px)) :=
    TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨hU.fromSpec px, hxU⟩
  have hpx : px.asIdeal.IsPrime := PrimeSpectrum.isPrime px
  have hpξ : pξ.asIdeal.IsPrime := PrimeSpectrum.isPrime pξ
  have hlocx : IsLocalization.AtPrime (X.presheaf.stalk (hU.fromSpec px)) px.asIdeal :=
    hU.isLocalization_stalk' px hxU
  set I := W.ideal ⟨U, hU₀⟩ with hI
  -- the stalk `W_x` is generated by `W(U)`
  have hW : W.stalkIdeal (hU.fromSpec px) =
      I.map (algebraMap Γ(X, U) (X.presheaf.stalk (hU.fromSpec px))) := by
    apply le_antisymm
    · rw [Subscheme.stalkIdeal, Ideal.span_le]
      rintro _ ⟨V, hxV, s, hs, rfl⟩
      obtain ⟨_, ⟨D, hD, rfl⟩, hxD, hDUV⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open
        (show hU.fromSpec px ∈ (U ⊓ V.1 : TopologicalSpace.Opens X) from ⟨hxU, hxV⟩)
        (U ⊓ V.1).isOpen
      have hDV : (⟨D, hD⟩ : X.affineOpens) ≤ V := hDUV.trans inf_le_right
      have hDU : (⟨D, hD⟩ : X.affineOpens) ≤ ⟨U, hU₀⟩ := hDUV.trans inf_le_left
      have h1 := W.ideal_le_comap_ideal hDV hs
      rw [Ideal.mem_comap, ← W.map_ideal hDU] at h1
      have h2 := Ideal.mem_map_of_mem (X.presheaf.germ D _ hxD).hom h1
      rw [Ideal.map_map] at h2
      have e1 : (X.presheaf.germ D _ hxD).hom.comp
          (X.presheaf.map (CategoryTheory.homOfLE hDU).op).hom =
          algebraMap Γ(X, U) (X.presheaf.stalk (hU.fromSpec px)) := by
        ext t
        exact X.presheaf.germ_res_apply (CategoryTheory.homOfLE hDU) _ hxD t
      have e2 : (X.presheaf.germ D _ hxD).hom
          ((X.presheaf.map (CategoryTheory.homOfLE hDV).op).hom s) =
          (X.presheaf.germ V.1 _ hxV).hom s := X.presheaf.germ_res_apply _ _ _ _
      rw [e1, e2] at h2
      exact h2
    · rw [Ideal.map_le_iff_le_comap]
      intro t ht
      exact Ideal.subset_span ⟨⟨U, hU₀⟩, hxU, t, ht, rfl⟩
  -- `√W(U) = P_ξ`: `V(W(U)) = W ∩ U = closure {ξ} ∩ U`
  have hzero : PrimeSpectrum.zeroLocus (I : Set Γ(X, U)) =
      PrimeSpectrum.zeroLocus (pξ.asIdeal : Set Γ(X, U)) := by
    ext p
    have h1 : hU.fromSpec '' PrimeSpectrum.zeroLocus (I : Set Γ(X, U)) =
        (W.support : Set X) ∩ U := by
      rw [hU.fromSpec_image_zeroLocus, W.coe_support_inter ⟨U, hU₀⟩]
    have h2 : p ∈ PrimeSpectrum.zeroLocus (I : Set Γ(X, U)) ↔ hU.fromSpec p ∈ W.pts := by
      constructor
      · intro hp
        have : hU.fromSpec p ∈ hU.fromSpec '' PrimeSpectrum.zeroLocus (I : Set Γ(X, U)) :=
          ⟨p, hp, rfl⟩
        rw [h1] at this
        exact this.1
      · intro hp
        have : hU.fromSpec p ∈ (W.support : Set X) ∩ U :=
          ⟨hp, by rw [← hU.range_fromSpec]; exact ⟨p, rfl⟩⟩
        rw [← h1] at this
        obtain ⟨p', hp', he⟩ := this
        rwa [← hU.fromSpec.isOpenEmbedding.injective he]
    have h3 : hU.fromSpec p ∈ W.pts ↔ pξ.asIdeal ≤ p.asIdeal := by
      rw [← hξ.def, ← specializes_iff_mem_closure]
      refine hU.fromSpec.isOpenEmbedding.isInducing.specializes_iff.trans ?_
      exact (PrimeSpectrum.le_iff_specializes (x := pξ) (y := p)).symm
    rw [h2, h3, PrimeSpectrum.mem_zeroLocus]
    exact SetLike.coe_subset_coe.symm
  have hrad : I.radical = pξ.asIdeal := by
    rw [← PrimeSpectrum.vanishingIdeal_zeroLocus_eq_radical, hzero,
      PrimeSpectrum.vanishingIdeal_zeroLocus_eq_radical, hpξ.radical]
  -- `W_x = P_ξ O_{X,x}`
  have hq' : W.stalkIdeal (hU.fromSpec px) =
      pξ.asIdeal.map (algebraMap Γ(X, U) (X.presheaf.stalk (hU.fromSpec px))) := by
    apply le_antisymm
    · rw [hW]
      exact Ideal.map_mono (hrad ▸ Ideal.le_radical)
    · rw [Ideal.map_le_iff_le_comap]
      intro a ha
      rw [← hrad] at ha
      obtain ⟨n, hn⟩ := ha
      have := Ideal.mem_map_of_mem (algebraMap Γ(X, U) (X.presheaf.stalk (hU.fromSpec px))) hn
      rw [← hW, map_pow] at this
      exact hq.mem_of_pow_mem n this
  have hcomap : (W.stalkIdeal (hU.fromSpec px)).comap
      (algebraMap Γ(X, U) (X.presheaf.stalk (hU.fromSpec px))) = pξ.asIdeal := by
    rw [hq']
    exact IsLocalization.under_map_of_isPrime_disjoint px.asIdeal.primeCompl _ hpξ
      (by
        rw [Set.disjoint_left]
        intro a ha ha'
        exact ha (hle ha'))
  have hlocq : IsLocalization.AtPrime (Localization.AtPrime (W.stalkIdeal (hU.fromSpec px)))
      pξ.asIdeal := by
    have := IsLocalization.isLocalization_isLocalization_atPrime_isLocalization
      px.asIdeal.primeCompl
      (S := X.presheaf.stalk (hU.fromSpec px))
      (Localization.AtPrime (W.stalkIdeal (hU.fromSpec px))) (W.stalkIdeal (hU.fromSpec px))
    convert this using 2
    exact hcomap.symm
  let _ : Algebra Γ(X, U) (X.presheaf.stalk (hU.fromSpec pξ)) :=
    TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨hU.fromSpec pξ, hξU⟩
  have hlocξ : IsLocalization.AtPrime (X.presheaf.stalk (hU.fromSpec pξ)) pξ.asIdeal :=
    hU.isLocalization_stalk' pξ hξU
  exact ⟨(IsLocalization.algEquiv pξ.asIdeal.primeCompl (X.presheaf.stalk (hU.fromSpec pξ))
    (Localization.AtPrime (W.stalkIdeal (hU.fromSpec px)))).toRingEquiv⟩

/-- An irreducible subscheme has a generic point (schemes are quasi-sober). -/
theorem exists_isGenericPoint_pts {X : Scheme.{u}} (W : Subscheme X)
    (hirr : W.IsIrreducible) : ∃ ξ : X, IsGenericPoint ξ W.pts := by
  have : IrreducibleSpace W.toScheme := hirr
  have h1 : _root_.IsIrreducible (Set.range W.ι) := by
    rw [← Set.image_univ]
    exact (IrreducibleSpace.isIrreducible_univ W.toScheme).image W.ι
      W.ι.continuous.continuousOn
  rw [Scheme.IdealSheafData.range_subschemeι] at h1
  exact QuasiSober.sober h1 W.support.isClosed

/-- Corollary 3 of Proposition 1, p. 187: "Let `V` be an algebraic scheme and `W` a
non-singular irreducible subscheme of `V`. Suppose `V` is normally flat along `W`. Then `V` has
the same multiplicity at every point of `W`."

Deviation from the paper (gap filled): the paper states this corollary without proof (after
Corollary 2).  The Lean proof applies Corollary 2 (ii) at every point `x` of `W` and proves that
`O_P` (`P` the ideal of `W` in `O_{V,x}`) is the local ring of `V` at the generic point of `W`
(`nonempty_stalk_equiv_localization`). -/
@[blueprint "cor:II.1-prop1-3"
  (statement := /-- Let $V$ be an algebraic scheme and $W$ a non-singular irreducible
    subscheme of $V$. Suppose $V$ is normally flat along $W$. Then $V$ has the same
    multiplicity at every point of $W$ (\cref{def:equimultiple-along}). (p.~187.) -/)
  (proof := /-- The paper states this without proof, after \cref{cor:II.1-prop1-2}.

    \textbf{Gap in the paper filled.} For a point $x$ of $W$ let $O=\mathcal O_{V,x}$ and
    $P$ the prime ideal of $W$ in $O$ ($W$ non-singular, so $O/P$ is regular); then $O_P$ is
    the local ring of $V$ at the generic point $\xi$ of $W$ (proved in Lean), and
    \cref{cor:II.1-prop1-2}(ii) gives $e(\mathcal O_{V,x})=e(\mathcal O_{V,\xi})$ for every
    $x\in W$. -/)
  (latexEnv := "corollary")]
theorem isEquimultipleAlong_of_isNormallyFlatAlong [Hironaka.Cited.ExistsHilbertSamuelPoly.{u}] (W : Subscheme X) (hW : W.IsNonsingular)
    (hirr : W.IsIrreducible) (h : W.IsNormallyFlatAlong) : W.IsEquimultipleAlong := by
  have := IsAlgebraicScheme.isNoetherian X
  obtain ⟨ξ, hξ⟩ := exists_isGenericPoint_pts W hirr
  have key : ∀ x ∈ W.pts, X.multAt x = X.multAt ξ := by
    intro x hx
    have := isRegularLocalRing_stalk_quot W hW hx
    have := isPrime_stalkIdeal W hW hx
    obtain ⟨e⟩ := nonempty_stalk_equiv_localization W hξ hx
    unfold Scheme.multAt
    rw [(hilbertSamuel_formula_and_samuelMultiplicity_eq_localization (W.stalkIdeal x)
      (h x hx).2).2]
    exact (samuelMultiplicity_eq_of_ringEquiv e).symm
  intro x hx y hy
  rw [key x hx, key y hy]

omit [IsAlgebraicScheme X] in
/-- Remark, p. 187: "Let us write `F_W` for `F_x̄` with the generic point `x̄` of `W`.  `F_W` is then
uniquely determined by the pair `(W, V)`."  An irreducible subscheme `W` of the algebraic scheme
`V = X` has a unique generic point (it exists since `X` is quasi-sober, and it is unique since `X`
is `T₀`), so `F_W = F_ξ` does not depend on any choice. -/
theorem existsUnique_isGenericPoint_pts (W : Subscheme X) (hirr : W.IsIrreducible) :
    ∃! ξ : X, IsGenericPoint ξ W.pts := by
  obtain ⟨ξ, hξ⟩ := exists_isGenericPoint_pts W hirr
  exact ⟨ξ, hξ, fun _ hξ' => hξ'.eq hξ⟩

/-- Remark, p. 187: `F_W`, the Samuel characteristic function of `V` at the generic point of the
irreducible subscheme `W` (`F_x = hilbertSamuel (X.presheaf.stalk x)`, the function
`n ↦ Σ_{i≤n} dim_{O/m}(mⁱ/mⁱ⁺¹)` of the local ring `O` of `V` at `x`). -/
@[blueprint "rem:II.1-samuel-function-unique"
  (statement := /-- Let $V$ be an algebraic scheme and $W$ an irreducible subscheme of $V$. Let
    $F_x$ denote the Samuel characteristic function of $V$ at the point $x$
    (\cref{def:hilbert-samuel-function}) and write $F_W$ for $F_x$ with the generic point $x$ of
    $W$. Then $F_W$ is uniquely determined by the pair $(W,V)$. (p.~187.) -/)
  (proof := /-- $W$ is irreducible, so it has a generic point, which is unique since the scheme
    $V$ is a $T_0$-space (and exists since $V$ is quasi-sober); hence $F_x$ for the generic point
    $x$ of $W$ does not depend on any choice. (The paper states the uniqueness without
    argument.) -/)
  (latexEnv := "remark")]
noncomputable def samuelFunction (W : Subscheme X) (hirr : W.IsIrreducible) : ℕ → ℕ :=
  hilbertSamuel (X.presheaf.stalk (Classical.choose (exists_isGenericPoint_pts W hirr)))

omit [IsAlgebraicScheme X] in
/-- `F_W = F_ξ` for every generic point `ξ` of `W`: "`F_W` is then uniquely determined by the pair
`(W, V)`" (p. 187). -/
theorem samuelFunction_eq_hilbertSamuel (W : Subscheme X) (hirr : W.IsIrreducible) {ξ : X}
    (hξ : IsGenericPoint ξ W.pts) :
    W.samuelFunction hirr = hilbertSamuel (X.presheaf.stalk ξ) := by
  have h := (Classical.choose_spec (exists_isGenericPoint_pts W hirr)).eq hξ
  have key : ∀ a b : X, a = b →
      hilbertSamuel (X.presheaf.stalk a) = hilbertSamuel (X.presheaf.stalk b) :=
    fun a b hab => by subst hab; rfl
  exact key _ _ h

omit [IsAlgebraicScheme X] in
/-- The Samuel characteristic functions at two generic points of `W` agree. -/
theorem hilbertSamuel_stalk_eq_of_isGenericPoint (W : Subscheme X) (hirr : W.IsIrreducible)
    {ξ ξ' : X} (hξ : IsGenericPoint ξ W.pts) (hξ' : IsGenericPoint ξ' W.pts) :
    hilbertSamuel (X.presheaf.stalk ξ) = hilbertSamuel (X.presheaf.stalk ξ') :=
  (W.samuelFunction_eq_hilbertSamuel hirr hξ).symm.trans
    (W.samuelFunction_eq_hilbertSamuel hirr hξ')

/-- Remark, p. 187: "Let `V` and `W` be the same as in Corollary 3. Let `x` be a point of `W`,
`O` the local ring of `V` at `x` and `m` the maximal ideal of `O`. Let `F_x(n)` denote the
function of non-negative integers `n` defined by `F_x(n) = Σ_{i≤n} dim_{O/m}(mⁱ/mⁱ⁺¹)`. Let us
call this function `F_x` the Samuel characteristic function of `V` at `x`. Let us write `F_W`
for `F_x̄` with the generic point `x̄` of `W`. `F_W` is then uniquely determined by the pair
`(W, V)`. Now, Corollary 2 implies that for every point `x` of `W`, we have
`F_x(n) = Σ_{p+q=n} F_W(p)·C(q+r−1, r−1)` for all non-negative integers `n`, where `r` denotes
the dimension of `W` at `x`. This fact is certainly stronger than the equi-multiplicity of `V`
along `W` as is asserted in Corollary 3."

Encoding: `F_x = hilbertSamuel (X.presheaf.stalk x)`, `F_W = hilbertSamuel (X.presheaf.stalk ξ)`
for the generic point `ξ` of `W`, and `r = dim O_{W,x} = dimNat (O_{V,x} ⧸ P_x)` (p. 163).

Deviation from the paper (statement modified): the binomial coefficient is read for `r = 0`
with the convention of Corollary 2.  The sentence "`F_W` is then uniquely determined by the
pair `(W, V)`" is `existsUnique_isGenericPoint_pts`, `samuelFunction` and
`samuelFunction_eq_hilbertSamuel`; the statement below keeps the generic
point `ξ` as a hypothesis, and `samuelFunction_formula_samuelFunction` is the form with `F_W`
itself.  The identification
`O_{V,ξ} ≅ (O_{V,x})_P` left implicit in "Corollary 2 implies" is proved
(`nonempty_stalk_equiv_localization`). -/
@[blueprint "rem:II.1-samuel-function"
  (statement := /-- Let $V$ and $W$ be the same as in \cref{cor:II.1-prop1-3}. For a point
    $x$ of $W$ with local ring $O=\mathcal O_{V,x}$ and maximal ideal $\mathfrak m$, let
    $F_x(n)=\sum_{i=0}^n\dim_{O/\mathfrak m}(\mathfrak m^i/\mathfrak m^{i+1})$ be the
    \emph{Samuel characteristic function} of $V$ at $x$
    (\cref{def:hilbert-samuel-function}), and let $F_W=F_\xi$ for the generic point $\xi$ of
    $W$. Then for every point $x$ of $W$, $F_x(n)=\sum_{p+q=n}F_W(p)\binom{q+r-1}{r-1}$ for all
    $n\ge0$, where $r$ denotes the dimension of $W$ at $x$. (p.~187.)

    \textbf{Deviation from the paper (statement modified).} For $r=0$ the binomial
    coefficient is read with the convention of \cref{cor:II.1-prop1-2}. -/)
  (proof := /-- \cref{cor:II.1-prop1-2}(i) applied to $O=\mathcal O_{V,x}$ and the prime
    ideal $P$ of $W$ in $O$: $O_P=\mathcal O_{V,\xi}$, $O/P=\mathcal O_{W,x}$ is regular of
    dimension $r$, and $\operatorname{gr}_P(O)$ is flat over $O/P$ by normal flatness. -/)
  (latexEnv := "remark")]
theorem samuelFunction_formula [Hironaka.Cited.ExistsHilbertSamuelPoly.{u}] (W : Subscheme X) (hW : W.IsNonsingular)
    (hirr : W.IsIrreducible) (h : W.IsNormallyFlatAlong) (ξ : X) (hξ : IsGenericPoint ξ W.pts)
    (x : X) (hx : x ∈ W.pts) (n : ℕ) :
    hilbertSamuel (X.presheaf.stalk x) n =
      ∑ pq ∈ Finset.HasAntidiagonal.antidiagonal n,
        hilbertSamuel (X.presheaf.stalk ξ) pq.1 *
          (if dimNat (X.presheaf.stalk x ⧸ W.stalkIdeal x) = 0 then
              (if pq.2 = 0 then 1 else 0)
            else Nat.choose (pq.2 + dimNat (X.presheaf.stalk x ⧸ W.stalkIdeal x) - 1)
              (dimNat (X.presheaf.stalk x ⧸ W.stalkIdeal x) - 1)) := by
  -- the irreducibility of `W` is already encoded in its generic point `ξ`
  have _ : IrreducibleSpace W.toScheme := hirr
  have := IsAlgebraicScheme.isNoetherian X
  have := isRegularLocalRing_stalk_quot W hW hx
  have := isPrime_stalkIdeal W hW hx
  obtain ⟨e⟩ := nonempty_stalk_equiv_localization W hξ hx
  rw [← (hilbertSamuel_formula_and_samuelMultiplicity_eq_localization (W.stalkIdeal x)
    (h x hx).2).1 n]
  refine Finset.sum_congr rfl fun pq _ => ?_
  rw [hilbertSamuel_eq_of_ringEquiv e]

/-- Remark, p. 187, with `F_W` itself (no generic point as a hypothesis): for every point `x` of
`W`, `F_x(n) = Σ_{p+q=n} F_W(p)·C(q+r−1, r−1)`, `F_W = W.samuelFunction` being uniquely determined
by `(W, V)` (`samuelFunction_eq_hilbertSamuel`). -/
theorem samuelFunction_formula_samuelFunction [Hironaka.Cited.ExistsHilbertSamuelPoly.{u}] (W : Subscheme X) (hW : W.IsNonsingular)
    (hirr : W.IsIrreducible) (h : W.IsNormallyFlatAlong) (x : X) (hx : x ∈ W.pts) (n : ℕ) :
    hilbertSamuel (X.presheaf.stalk x) n =
      ∑ pq ∈ Finset.HasAntidiagonal.antidiagonal n,
        W.samuelFunction hirr pq.1 *
          (if dimNat (X.presheaf.stalk x ⧸ W.stalkIdeal x) = 0 then
              (if pq.2 = 0 then 1 else 0)
            else Nat.choose (pq.2 + dimNat (X.presheaf.stalk x ⧸ W.stalkIdeal x) - 1)
              (dimNat (X.presheaf.stalk x ⧸ W.stalkIdeal x) - 1)) := by
  obtain ⟨ξ, hξ⟩ := exists_isGenericPoint_pts W hirr
  rw [samuelFunction_formula W hW hirr h ξ hξ x hx n, W.samuelFunction_eq_hilbertSamuel hirr hξ]

/-- `gr⁰_m(R) = R/m` is one-dimensional over `R/m`. -/
private theorem finrank_grPiece_maximalIdeal_zero (R : Type u) [CommRing R] [IsLocalRing R] :
    Module.finrank (R ⧸ IsLocalRing.maximalIdeal R) (GrPiece (IsLocalRing.maximalIdeal R) 0) =
      1 := by
  set m := IsLocalRing.maximalIdeal R with hm
  let f : ↥(m ^ 0) ≃ₗ[R] R :=
    (LinearEquiv.ofEq _ _ (by rw [pow_zero, Ideal.one_eq_top])).trans Submodule.topEquiv
  have hf : (Submodule.comap (m ^ 0).subtype (m ^ (0 + 1))).map (f : ↥(m ^ 0) →ₗ[R] R) =
      (m : Submodule R R) := by
    rw [Submodule.map_equiv_eq_comap_symm]
    ext x
    rw [Submodule.mem_comap, Submodule.mem_comap, zero_add, pow_one]
    rfl
  let j : GrPiece m 0 ≃ₗ[R] R ⧸ m := Submodule.Quotient.equiv _ _ f hf
  refine Eq.trans ?_ (Module.finrank_self (R ⧸ m))
  unfold Module.finrank
  rw [rank_eq_of_equiv_equiv (id : R ⧸ m → R ⧸ m) j.toAddEquiv Function.bijective_id]
  intro r y
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective r
  have h1 : (Ideal.Quotient.mk m a) • y = a • y := algebraMap_smul (R ⧸ m) a y
  have h3 : (Ideal.Quotient.mk m a) • j y = a • j y := algebraMap_smul (R ⧸ m) a (j y)
  rw [h1]
  change j (a • y) = Ideal.Quotient.mk m a • j y
  rw [h3]
  exact j.map_smul a y

/-- `gr¹_m(R) = m/m²` has dimension `emb dim R`. -/
private theorem finrank_grPiece_maximalIdeal_one (R : Type u) [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] :
    Module.finrank (R ⧸ IsLocalRing.maximalIdeal R) (GrPiece (IsLocalRing.maximalIdeal R) 1) =
      (IsLocalRing.maximalIdeal R).spanFinrank := by
  set m := IsLocalRing.maximalIdeal R with hm
  let f : ↥(m ^ 1) ≃ₗ[R] ↥m := LinearEquiv.ofEq _ _ (pow_one m)
  have hf : (Submodule.comap (m ^ 1).subtype (m ^ (1 + 1))).map (f : ↥(m ^ 1) →ₗ[R] ↥m) =
      LinearMap.ker m.toCotangent := by
    rw [Submodule.map_equiv_eq_comap_symm]
    ext x
    rw [Submodule.mem_comap, Submodule.mem_comap, Ideal.mem_toCotangent_ker]
    rfl
  let j₀ : GrPiece m 1 ≃ₗ[R] ↥m ⧸ LinearMap.ker m.toCotangent :=
    Submodule.Quotient.equiv _ _ f hf
  let j₁ : (↥m ⧸ LinearMap.ker m.toCotangent) ≃ₗ[R] m.Cotangent :=
    m.toCotangent.quotKerEquivOfSurjective m.toCotangent_surjective
  let j := j₀.trans j₁
  refine Eq.trans ?_ (IsLocalRing.spanFinrank_maximalIdeal_eq_finrank_cotangentSpace R).symm
  unfold Module.finrank
  rw [rank_eq_of_equiv_equiv (show R ⧸ m → IsLocalRing.ResidueField R from fun a => a)
    j.toAddEquiv Function.bijective_id]
  intro r y
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective r
  have h1 : (Ideal.Quotient.mk m a) • y = a • y := algebraMap_smul (R ⧸ m) a y
  have h3 : (IsLocalRing.residue R a) • j y = a • j y :=
    algebraMap_smul (IsLocalRing.ResidueField R) a (j y)
  rw [h1]
  change j (a • y) = IsLocalRing.residue R a • j y
  rw [h3]
  exact j.map_smul a y

/-- `H_R(1) = 1 + emb dim R`. -/
private theorem hilbertSamuel_one (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] :
    hilbertSamuel R 1 = 1 + (IsLocalRing.maximalIdeal R).spanFinrank := by
  unfold hilbertSamuel
  rw [Finset.sum_range_succ, Finset.sum_range_one, finrank_grPiece_maximalIdeal_zero,
    finrank_grPiece_maximalIdeal_one]

/-- A local ring with `𝔪ⁱ = 0` has `gr^i_𝔪 = 0`. -/
private theorem finrank_grPiece_eq_zero_of_pow_eq_bot {R : Type u} [CommRing R] [IsLocalRing R]
    {i : ℕ} (h : IsLocalRing.maximalIdeal R ^ i = ⊥) :
    Module.finrank (R ⧸ IsLocalRing.maximalIdeal R) (GrPiece (IsLocalRing.maximalIdeal R) i) =
      0 := by
  have : Subsingleton (GrPiece (IsLocalRing.maximalIdeal R) i) := by
    refine ⟨fun a b => ?_⟩
    induction a using Submodule.Quotient.induction_on with
    | H x =>
    induction b using Submodule.Quotient.induction_on with
    | H y =>
      have hx : (x : R) = 0 := Ideal.mem_bot.mp (h ▸ x.2)
      have hy : (y : R) = 0 := Ideal.mem_bot.mp (h ▸ y.2)
      rw [Subtype.ext (hx.trans hy.symm : (x : R) = y)]
  exact Module.finrank_zero_of_subsingleton

/-- Corollary 4, p. 188: "by the assumption on the generic point of `W`, we have
`F_W(p) = C(p+s, s)` where `s` denotes the codimension of `W` in `V`, i.e., the dimension of `V` at
the generic point of `W`."  This is the Samuel characteristic function of a regular local ring `R`
of dimension `s`: `gr_𝔪(R)` is a polynomial ring in `s` variables (`dim_k grⁱ = C(i+s-1, s-1)`,
`exists_finrank_grPiece_maximalIdeal_eq_choose`), so `F(p) = Σ_{i≤p} C(i+s-1, s-1) = C(p+s, s)`
(`sum_range_choose_eq`); for `s = 0` (`R` a field) `F = 1`.  The paper's only reason is "by the
assumption on the generic point of `W`"; the computation is a gap filled. -/
private theorem hilbertSamuel_eq_choose_of_isRegularLocalRing (R : Type u) [CommRing R]
    [IsRegularLocalRing R] (p : ℕ) :
    hilbertSamuel R p = (p + dimNat R).choose (dimNat R) := by
  by_cases hM : IsLocalRing.maximalIdeal R = ⊥
  · have hd : dimNat R = 0 := by
      rw [dimNat, ← IsRegularLocalRing.spanFinrank_maximalIdeal (R := R), hM]
      simp
      rfl
    rw [hd, Nat.choose_zero_right]
    unfold hilbertSamuel
    rw [Finset.sum_eq_single 0, finrank_grPiece_maximalIdeal_zero]
    · intro i _ hi
      exact finrank_grPiece_eq_zero_of_pow_eq_bot (by rw [hM]; exact zero_pow hi)
    · intro h
      exact absurd (Finset.mem_range.mpr (Nat.succ_pos p)) h
  · obtain ⟨e, hdim, hgr⟩ := exists_finrank_grPiece_maximalIdeal_eq_choose R hM
    have hd : dimNat R = e + 1 := by
      rw [dimNat, hdim]
      rfl
    rw [hd]
    unfold hilbertSamuel
    simp_rw [hgr]
    rw [sum_range_choose_eq, show p + 1 + e = p + (e + 1) by ring]

/-- `dim R` of a noetherian local ring, as an element of `WithBot ℕ∞` (it is finite). -/
private theorem ringKrullDim_eq_dimNat (R : Type u) [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] : ringKrullDim R = (dimNat R : WithBot ℕ∞) := by
  have h1 : ringKrullDim R ≠ ⊥ := ringKrullDim_ne_bot
  have h2 : ringKrullDim R ≠ ⊤ := ringKrullDim_ne_top
  obtain ⟨a, ha⟩ := WithBot.ne_bot_iff_exists.mp h1
  have ha' : a ≠ ⊤ := fun h => h2 (by rw [← ha, h]; rfl)
  obtain ⟨n, rfl⟩ := ENat.ne_top_iff_exists.mp ha'
  rw [← ha, dimNat, ← ha]
  rfl

/-- `T ↦ C(T + a + e, e)` is a polynomial of degree `e`. -/
private theorem natDegree_binomPoly_eq (e : ℕ) (a : ℚ) : (binomPoly e a).natDegree = e := by
  unfold binomPoly
  rw [Polynomial.natDegree_C_mul (one_div_ne_zero (Nat.cast_ne_zero.mpr e.factorial_ne_zero)),
    Polynomial.natDegree_prod_of_monic _ _ fun i _ => Polynomial.monic_X_add_C _]
  simp only [Polynomial.natDegree_X_add_C, Finset.sum_const, Finset.card_range, smul_eq_mul,
    mul_one]

/-- Corollary 4, p. 188: "`F_x(n) = C(n+s+r, s+r)` ... This implies immediately that the local ring
of `V` at `x` is regular".  The step is not printed; the argument of this lemma: if
`F(n) = C(n+d, d)` for all `n`, then `F` is the polynomial `binomPoly d 0` of degree `d`, so by
Samuel's theorem (`exists_hilbertSamuelPoly`, cited through footnote 3, p. 116, and
`hilbertSamuelPoly_unique`) `dim R = d`, and `F(1) = d + 1` says that the embedding dimension is
`d` (`F(1) = 1 + emb dim R`), so `R` is regular. -/
private theorem isRegularLocalRing_of_hilbertSamuel_eq_choose [Hironaka.Cited.ExistsHilbertSamuelPoly.{u}] (R : Type u) [CommRing R]
    [IsLocalRing R] [IsNoetherianRing R] (d : ℕ)
    (h : ∀ n, hilbertSamuel R n = (n + d).choose d) : IsRegularLocalRing R := by
  -- `dim R = d`: the degree of the Hilbert-Samuel polynomial (Samuel's theorem)
  have hdim : dimNat R = d := by
    obtain ⟨p, hp, hdeg, -⟩ := exists_hilbertSamuelPoly R
    have hq : ∀ᶠ n : ℕ in Filter.atTop,
        (binomPoly d 0).eval (n : ℚ) = (hilbertSamuel R n : ℚ) :=
      Filter.Eventually.of_forall fun n => by
        rw [h n]
        exact eval_binomPoly d n n 0 (by simp)
    rw [← hdeg, hilbertSamuelPoly_unique R hp hq]
    exact natDegree_binomPoly_eq d 0
  -- `emb dim R = d`: `F(1) = 1 + emb dim R` and `F(1) = C(1+d, d) = d + 1`
  have hemb : (IsLocalRing.maximalIdeal R).spanFinrank = d := by
    have h1 := hilbertSamuel_one R
    rw [h 1, add_comm 1 d, Nat.choose_succ_self_right] at h1
    omega
  refine IsRegularLocalRing.of_spanFinrank_maximalIdeal_le R ?_
  rw [hemb, ringKrullDim_eq_dimNat, hdim]

/-- Corollary 4 of Proposition 1, p. 188: "Let `V` and `W` be the same as in Corollary 3. If `V`
is normally flat along `W`, and `W` contains at least one simple point of `V`, then every point
of `W` is a simple point of `V`."

Proof as printed (Remark, pp. 187-188): "In fact, by the assumption on the generic point of `W`, we
have `F_W(p) = C(p+s, s)` where `s` denotes the codimension of `W` in `V`, i.e., the dimension of `V`
at the generic point of `W`.  Therefore, by the normal flatness, we have `F_x(n) = C(n+s+r, s+r)`
for every point of `W`, where `r` denotes the dimension of `W` at `x`.  This implies immediately that
the local ring of `V` at `x` is regular, i.e., `x` is a simple point of `V`."  The three steps are
`hilbertSamuel_eq_choose_of_isRegularLocalRing`, the Remark `samuelFunction_formula` together
with the identity of p. 187 `sum_antidiagonal_choose_mul_monomialCount`, and
`isRegularLocalRing_of_hilbertSamuel_eq_choose` (Samuel's theorem, cited through footnote 3,
p. 116).

Deviation from the paper (gap filled): the paper's argument assumes that the *generic point* of `W`
is a simple point of `V` ("let us suppose that the generic point of `W` is a simple point of `V`");
the passage from "`W` contains at least one simple point" to this is not stated.  Lean obtains it
from the openness of the simple locus (`isOpen_setOf_isSimpleAt`, i.e. the cited (iii) of p. 161).

Gaps filled: `F_W(p) = C(p+s, s)` (stated without proof) is the Samuel function of a regular local
ring of dimension `s`, and "This implies immediately" (no argument is printed) is proved by Samuel's
theorem: `F_x` is the polynomial `C(n+s+r, s+r)` of degree `s+r`, so `dim O_x = s+r`, and
`F_x(1) = s+r+1` gives `emb dim O_x = s+r`. -/
@[blueprint "cor:II.1-prop1-4"
  (statement := /-- Let $V$ and $W$ be the same as in \cref{cor:II.1-prop1-3}. If $V$ is
    normally flat along $W$, and $W$ contains at least one simple point of $V$, then every
    point of $W$ is a simple point of $V$. (p.~188.) -/)
  (proof := /-- (The paper's argument, Remark, pp.~187--188.) Suppose that the generic point
    of $W$ is a simple point of $V$. Then $F_W(p)=\binom{p+s}{s}$ where $s$ is the codimension
    of $W$ in $V$, i.e.\ the dimension of $V$ at the generic point of $W$. Therefore, by the
    normal flatness (\cref{rem:II.1-samuel-function}), $F_x(n)=\binom{n+s+r}{s+r}$ for every
    point $x$ of $W$, where $r$ denotes the dimension of $W$ at $x$. ``This implies immediately
    that the local ring of $V$ at $x$ is regular, i.e., $x$ is a simple point of $V$.''

    \textbf{Gap in the paper filled.} The corollary assumes only that $W$ contains some simple
    point $x_0$ of $V$; that the generic point of $W$ is then simple is not stated in the paper.
    Lean deduces it from the openness of the set of simple points, (iii) of p.~161 (a cited
    leaf), since $x_0$ is a specialization of the generic point.

    \textbf{Gaps in the paper filled.} $F_W(p)=\binom{p+s}{s}$ is stated without proof: it is the
    Samuel function of a regular local ring of dimension $s$ ($\operatorname{gr}$ is a polynomial
    ring in $s$ variables). ``This implies immediately'' is proved with Samuel's theorem (cited,
    footnote~3, p.~116): $F_x(n)=\binom{n+s+r}{s+r}$ is a polynomial of degree $s+r$, so
    $\dim\mathcal O_{V,x}=s+r$, and $F_x(1)=s+r+1$ gives $\operatorname{emb\,dim}\mathcal O_{V,x}
    =s+r$, so $\mathcal O_{V,x}$ is regular. -/)
  (latexEnv := "corollary")]
theorem forall_isSimpleAt_of_isNormallyFlatAlong [Hironaka.Cited.IsHironakaBaseIsClosedSingularLocus.{u}] [Hironaka.Cited.ExistsHilbertSamuelPoly.{u}] (W : Subscheme X) (hW : W.IsNonsingular)
    (hirr : W.IsIrreducible) (h : W.IsNormallyFlatAlong) (hx : ∃ x ∈ W.pts, X.IsSimpleAt x) :
    ∀ x ∈ W.pts, X.IsSimpleAt x := by
  have := IsAlgebraicScheme.isNoetherian X
  obtain ⟨ξ, hξ⟩ := exists_isGenericPoint_pts W hirr
  obtain ⟨x₀, hx₀, hs₀⟩ := hx
  -- the generic point `ξ` of `W` is simple: the simple points form an open set containing `x₀`
  have hξs : X.IsSimpleAt ξ := by
    have hspec : ξ ⤳ x₀ := by
      rw [specializes_iff_mem_closure, hξ.def]
      exact hx₀
    exact hspec.mem_open (isOpen_setOf_isSimpleAt X) hs₀
  intro x hx
  have : IsRegularLocalRing (X.presheaf.stalk ξ) := hξs
  -- "by the assumption on the generic point of `W`, we have `F_W(p) = C(p+s, s)`", `s = dim O_ξ`
  have hFW : ∀ p, hilbertSamuel (X.presheaf.stalk ξ) p =
      (p + dimNat (X.presheaf.stalk ξ)).choose (dimNat (X.presheaf.stalk ξ)) :=
    hilbertSamuel_eq_choose_of_isRegularLocalRing _
  -- "Therefore, by the normal flatness, we have `F_x(n) = C(n+s+r, s+r)` for every point of `W`,
  -- where `r` denotes the dimension of `W` at `x`": the Remark and the identity of p. 187
  have hFx : ∀ n, hilbertSamuel (X.presheaf.stalk x) n =
      (n + (dimNat (X.presheaf.stalk ξ) + dimNat (X.presheaf.stalk x ⧸ W.stalkIdeal x))).choose
        (dimNat (X.presheaf.stalk ξ) + dimNat (X.presheaf.stalk x ⧸ W.stalkIdeal x)) := by
    intro n
    rw [samuelFunction_formula W hW hirr h ξ hξ x hx n]
    simp_rw [hFW]
    rw [← add_assoc]
    exact sum_antidiagonal_choose_mul_monomialCount _ _ n
  -- "This implies immediately that the local ring of `V` at `x` is regular"
  exact isRegularLocalRing_of_hilbertSamuel_eq_choose _ _ hFx

end Subscheme

/-! ### Lemmas 3, 4 and Theorem 1 (Krull–Seidenberg–Grothendieck), pp. 188–189 -/

section OpennessOfFlatness

/-- Lemma 3, p. 188: "Let `A` be a noetherian integral domain, `S` an `A`-algebra of finite
type and `M` an `S`-module of finite type. Then there exists a non-zero element `f` of `A` such
that `M_f` is a free `A_f`-module, where `M_f` and `A_f` denote the localizations of `M` and
`A` respectively with respect to the multiplicatively closed subset of `A` consisting of the
powers of `f`." -/
@[blueprint "lem:II.1-3"
  (statement := /-- Let $A$ be a noetherian integral domain, $S$ an $A$-algebra of finite type
    and $M$ an $S$-module of finite type. Then there exists a non-zero element $f$ of $A$ such
    that $M_f$ is a free $A_f$-module, where $M_f$ and $A_f$ denote the localizations of $M$
    and $A$ with respect to the powers of $f$. (p.~188.) -/)
  (proof := /-- Cited: ``Lemma 6.7 of the above cited seminar note by Grothendieck''
    (S\'eminaire de G\'eom\'etrie Alg\'ebrique de l'IHES, No.~IV (1960); p.~188); the paper
    gives no proof. (Formalization note: proved in Lean as \cref{compat:generic-freeness}, by
    induction on the number of generators of $S$.) -/)
  (latexEnv := "lemma")]
theorem exists_free_localization_away (A : Type u) [CommRing A] [IsDomain A]
    [IsNoetherianRing A] (S : Type u) [CommRing S] [Algebra A S] [Algebra.FiniteType A S]
    (M : Type u) [AddCommGroup M] [Module S M] [Module A M] [IsScalarTower A S M]
    [Module.Finite S M] :
    ∃ f : A, f ≠ 0 ∧
      Module.Free (Localization.Away f) (LocalizedModule (Submonoid.powers f) M) :=
  exists_free_localizedModule_of_finiteType A S M

/-- Flatness of `X_f` over `R_f` passes to `X_{fg}` over `R_{fg}`. -/
private theorem flat_localization_away_mul {R X : Type u} [CommRing R] [AddCommGroup X] [Module R X]
    (f g : R)
    [hX : Module.Flat (Localization.Away f) (LocalizedModule (Submonoid.powers f) X)] :
    Module.Flat (Localization.Away (f * g)) (LocalizedModule (Submonoid.powers (f * g)) X) := by
  let mf := LocalizedModule.mkLinearMap (Submonoid.powers f) X
  let mh := LocalizedModule.mkLinearMap (Submonoid.powers (f * g)) X
  have hflat : Module.Flat R (LocalizedModule (Submonoid.powers f) X) :=
    (Module.flat_iff_of_isLocalization (Localization.Away f) (Submonoid.powers f) _).mp hX
  have hhu : IsUnit (algebraMap R (Module.End R (LocalizedModule (Submonoid.powers (f * g)) X))
      (f * g)) := IsLocalizedModule.Away.isUnit_algebraMap mh (f * g)
  have hfu : ∀ y : Submonoid.powers f, IsUnit (algebraMap R
      (Module.End R (LocalizedModule (Submonoid.powers (f * g)) X)) y) := by
    rintro ⟨_, n, rfl⟩
    rw [map_mul, ((Commute.all f g).map (algebraMap R
      (Module.End R (LocalizedModule (Submonoid.powers (f * g)) X)))).isUnit_mul_iff] at hhu
    simpa using hhu.1.pow n
  let φ := IsLocalizedModule.lift (Submonoid.powers f) mf mh hfu
  have hφ : ∀ x, φ (mf x) = mh x := fun x => IsLocalizedModule.lift_apply _ _ _ _ x
  have hfu' : IsUnit (algebraMap R (Module.End R (LocalizedModule (Submonoid.powers f) X)) f) :=
    IsLocalizedModule.Away.isUnit_algebraMap mf f
  have : IsLocalizedModule.Away (f * g) φ := by
    refine IsLocalizedModule.Away.mk_of_addCommGroup hhu (fun y => ?_) (fun x hx => ?_)
    · obtain ⟨n, x, hx⟩ := IsLocalizedModule.Away.surj mh (f * g) y
      exact ⟨n, mf x, by rw [hφ, hx]⟩
    · obtain ⟨k, x', hx'⟩ := IsLocalizedModule.Away.surj mf f x
      have h0 : mh x' = 0 := by rw [← hφ, ← hx', map_smul, hx, smul_zero]
      obtain ⟨m, hm⟩ := IsLocalizedModule.Away.exists_of_eq (f * g) (f := mh)
        (h0.trans (map_zero mh).symm)
      rw [smul_zero] at hm
      refine ⟨m, ?_⟩
      have h1 : f ^ k • ((f * g) ^ m • x) = 0 := by
        rw [smul_comm, hx', ← map_smul, hm, map_zero]
      have hinj : Function.Injective (algebraMap R
          (Module.End R (LocalizedModule (Submonoid.powers f) X)) (f ^ k)) :=
        (Module.End.isUnit_iff _).mp (by rw [map_pow]; exact hfu'.pow k) |>.1
      apply hinj
      rw [map_zero]
      exact h1
  exact Module.Flat.of_isLocalizedModule (Localization.Away (f * g))
    (Submonoid.powers (f * g)) φ

/-- `P M = (P B) M` for a `B`-module `M`. -/
private theorem restrictScalars_map_smul_top {A B M : Type u} [CommRing A] [CommRing B]
    [Algebra A B] [AddCommGroup M]
    [Module B M] [Module A M] [IsScalarTower A B M] (P : Ideal A) :
    ((P.map (algebraMap A B)) • (⊤ : Submodule B M)).restrictScalars A =
      (P • ⊤ : Submodule A M) := by
  have hstab : ∀ (b : B) (x : M), x ∈ (P • ⊤ : Submodule A M) →
      b • x ∈ (P • ⊤ : Submodule A M) := by
    intro b x hx
    refine Submodule.smul_induction_on hx (fun p hp m _ => ?_) (fun x y hx hy => ?_)
    · rw [smul_comm b p m]
      exact Submodule.smul_mem_smul hp Submodule.mem_top
    · rw [smul_add]
      exact add_mem hx hy
  apply le_antisymm
  · intro x hx
    rw [Submodule.restrictScalars_mem] at hx
    refine Submodule.smul_induction_on hx (fun j hj m _ => ?_) (fun x y hx hy => add_mem hx hy)
    have hj' : j ∈ Submodule.span B (algebraMap A B '' P) := hj
    clear hj
    induction hj' using Submodule.span_induction with
    | mem j hj =>
      obtain ⟨p, hp, rfl⟩ := hj
      rw [algebraMap_smul]
      exact Submodule.smul_mem_smul hp Submodule.mem_top
    | zero => rw [zero_smul]; exact zero_mem _
    | add j k _ _ hj hk => rw [add_smul]; exact add_mem hj hk
    | smul b j _ hj =>
      rw [smul_eq_mul, mul_smul]
      exact hstab b _ hj
  · rw [Submodule.smul_le]
    intro p hp m _
    rw [Submodule.restrictScalars_mem, ← algebraMap_smul B p m]
    exact Submodule.smul_mem_smul (Ideal.mem_map_of_mem _ hp) Submodule.mem_top

/-- Lemma 3 (generic freeness) applied to `M/PM` over the domain `A/P`: some `f ∉ P` makes
`(M/PM)_{fg}` flat over `(A/P)_{fg}` for every `g`. -/
private theorem exists_flat_localization_quotient (A : Type u) [CommRing A] [IsNoetherianRing A]
    (B : Type u) [CommRing B] [Algebra A B] [Algebra.FiniteType A B]
    (M : Type u) [AddCommGroup M] [Module B M] [Module A M] [IsScalarTower A B M]
    [Module.Finite B M] (P : Ideal A) [P.IsPrime] :
    ∃ f : A, f ∉ P ∧ ∀ g : A, Module.Flat (Localization.Away (Ideal.Quotient.mk P (f * g)))
      (LocalizedModule (Submonoid.powers (Ideal.Quotient.mk P (f * g)))
        (M ⧸ (P • ⊤ : Submodule A M))) := by
  let J : Ideal B := P.map (algebraMap A B)
  -- `P M = (P B) M`
  have hN : (J • (⊤ : Submodule B M)).restrictScalars A = (P • ⊤ : Submodule A M) :=
    restrictScalars_map_smul_top P
  let e₀ : (M ⧸ (P • ⊤ : Submodule A M)) ≃ₗ[A] M ⧸ J • (⊤ : Submodule B M) :=
    (Submodule.quotEquivOfEq _ _ hN.symm).trans (Submodule.Quotient.restrictScalarsEquiv A _)
  let _ : Module (B ⧸ J) (M ⧸ (P • ⊤ : Submodule A M)) := e₀.toAddEquiv.module (B ⧸ J)
  let e₁ : (M ⧸ (P • ⊤ : Submodule A M)) ≃ₗ[B ⧸ J] M ⧸ J • (⊤ : Submodule B M) :=
    e₀.toAddEquiv.linearEquiv (B ⧸ J)
  have : IsScalarTower (A ⧸ P) (B ⧸ J) (M ⧸ (P • ⊤ : Submodule A M)) := by
    constructor
    intro a' b' x
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a'
    apply e₁.injective
    have h1 : ∀ y : M ⧸ (P • ⊤ : Submodule A M), e₁ (Ideal.Quotient.mk P a • y) = a • e₁ y :=
      fun y => by
        have : Ideal.Quotient.mk P a • y = a • y := algebraMap_smul (A ⧸ P) a y
        rw [this]
        exact e₀.map_smul a y
    have h2 : ∀ w : M ⧸ J • (⊤ : Submodule B M),
        algebraMap (A ⧸ P) (B ⧸ J) (Ideal.Quotient.mk P a) • w = a • w := fun w => by
      rw [Ideal.Quotient.algebraMap_quotient_map_quotient]
      have : Ideal.Quotient.mk J (algebraMap A B a) • w = algebraMap A B a • w :=
        algebraMap_smul (B ⧸ J) (algebraMap A B a) w
      rw [this, algebraMap_smul]
    rw [e₁.map_smul, Algebra.smul_def, mul_smul, h1, e₁.map_smul, h2]
  have : Module.Finite B (M ⧸ J • (⊤ : Submodule B M)) := inferInstance
  have : Module.Finite (B ⧸ J) (M ⧸ J • (⊤ : Submodule B M)) :=
    Module.Finite.of_restrictScalars_finite B (B ⧸ J) _
  have : Module.Finite (B ⧸ J) (M ⧸ (P • ⊤ : Submodule A M)) := Module.Finite.equiv e₁.symm
  have : Algebra.FiniteType A (B ⧸ J) :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ A J)
      Ideal.Quotient.mk_surjective
  have : Algebra.FiniteType (A ⧸ P) (B ⧸ J) :=
    Algebra.FiniteType.of_restrictScalars_finiteType A (A ⧸ P) (B ⧸ J)
  obtain ⟨f', hf', hfree⟩ := exists_free_localization_away (A ⧸ P) (B ⧸ J)
    (M ⧸ (P • ⊤ : Submodule A M))
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective f'
  refine ⟨f, fun hf => hf' (Ideal.Quotient.eq_zero_iff_mem.mpr hf), fun g => ?_⟩
  rw [map_mul]
  have : Module.Flat (Localization.Away (Ideal.Quotient.mk P f))
      (LocalizedModule (Submonoid.powers (Ideal.Quotient.mk P f))
        (M ⧸ (P • ⊤ : Submodule A M))) := Module.Flat.of_free
  exact flat_localization_away_mul _ _

/-- Proof of Lemma 4, p. 188: "Therefore it is clear that (b′) implies (b)".  A `B`-module `K` of
finite type each of whose elements is killed by some element outside the prime `P` (the
vanishing of `K_P`) is killed by one element `g ∉ P`: take the product of elements outside `P`
killing a finite set of `B`-generators of `K`. -/
private theorem exists_smul_eq_zero_of_finite_of_forall {A : Type u} [CommRing A] (B : Type u)
    [CommRing B] [Algebra A B] {K : Type u} [AddCommGroup K] [Module B K] [Module A K]
    [IsScalarTower A B K] [Module.Finite B K] (P : Ideal A) [P.IsPrime]
    (h : ∀ k : K, ∃ s ∉ P, s • k = 0) : ∃ g : A, g ∉ P ∧ ∀ k : K, g • k = 0 := by
  classical
  obtain ⟨gen, hgen⟩ := Module.Finite.fg_top (R := B) (M := K)
  choose! s hsP hs using h
  refine ⟨∏ x ∈ gen, s x, fun hf => ?_, fun k => ?_⟩
  · have : ∏ x ∈ gen, s x ∈ P.primeCompl := Submonoid.prod_mem _ fun x _ => hsP x
    exact this hf
  · have hk : k ∈ Submodule.span B (gen : Set K) := hgen ▸ Submodule.mem_top
    induction hk using Submodule.span_induction with
    | mem y hy =>
      rw [← Finset.mul_prod_erase gen s hy, mul_smul, smul_comm, hs y, smul_zero]
    | zero => exact smul_zero _
    | add y z _ _ hy hz => rw [smul_add, hy, hz, add_zero]
    | smul b y _ hy => rw [smul_comm, hy, smul_zero]

/-- Proof of Lemma 4, (b): if the `A`-module `T = Tor₁^A(M, A/P)` is killed by `g`, then
`T_g = 0`. -/
private theorem subsingleton_localizedModule_powers_of_smul_eq_zero {A : Type u} [CommRing A]
    {T : Type u} [AddCommGroup T] [Module A T] (g : A) (h : ∀ t : T, g • t = 0) :
    Subsingleton (LocalizedModule (Submonoid.powers g) T) := by
  have hzero : ∀ a : LocalizedModule (Submonoid.powers g) T, a = 0 := by
    intro a
    induction a using LocalizedModule.induction_on with
    | h t s =>
      rw [← LocalizedModule.zero_mk s, LocalizedModule.mk_eq]
      refine ⟨⟨g, 1, pow_one _⟩, ?_⟩
      rw [smul_zero, smul_zero, Submonoid.smul_def, Submonoid.smul_def, smul_comm, h,
        smul_zero]
  exact ⟨fun a b => (hzero a).trans (hzero b).symm⟩

/-- Proof of Lemma 4, the element `f` of the statement (gap filled): (b) for `g` implies (b) for
`f * g`, since `T_g = 0` means that each `t ∈ T` is killed by a power of `g`, hence by the same
power of `f * g`. -/
private theorem subsingleton_localizedModule_powers_mul {A : Type u} [CommRing A]
    {T : Type u} [AddCommGroup T] [Module A T] (f g : A)
    (h : Subsingleton (LocalizedModule (Submonoid.powers g) T)) :
    Subsingleton (LocalizedModule (Submonoid.powers (f * g)) T) := by
  have hzero : ∀ a : LocalizedModule (Submonoid.powers (f * g)) T, a = 0 := by
    intro a
    induction a using LocalizedModule.induction_on with
    | h t s =>
      have h0 : LocalizedModule.mk t (1 : Submonoid.powers g) = LocalizedModule.mk 0 1 :=
        Subsingleton.elim _ _
      obtain ⟨⟨_, m, rfl⟩, hm⟩ := LocalizedModule.mk_eq.mp h0
      rw [← LocalizedModule.zero_mk s, LocalizedModule.mk_eq]
      refine ⟨⟨(f * g) ^ m, m, rfl⟩, ?_⟩
      simp only [one_smul, smul_zero, Submonoid.smul_def] at hm ⊢
      rw [smul_comm, mul_pow, mul_smul, hm, smul_zero, smul_zero]
  exact ⟨fun a b => (hzero a).trans (hzero b).symm⟩

/-- Proof of Lemma 4, (a′): "`(M/PM)_P` is a flat `(A/P)_P`-module (which is trivial because
`(A/P)_P` is a field)".  Here `(A/P)_P = A_P/PA_P` (a field, the residue field of `A_P`) and
`(M/PM)_P = (A_P/PA_P) ⊗_{A_P} (A_P ⊗_A M)`. -/
private theorem flat_quotient_tensor_localization_atPrime {A : Type u} [CommRing A]
    (P : Ideal A) [P.IsPrime] (M : Type u) [AddCommGroup M] [Module A M] :
    Module.Flat (Localization.AtPrime P ⧸ P.map (algebraMap A (Localization.AtPrime P)))
      ((Localization.AtPrime P ⧸ P.map (algebraMap A (Localization.AtPrime P))) ⊗[
        Localization.AtPrime P] (Localization.AtPrime P ⊗[A] M)) := by
  have hmax : (P.map (algebraMap A (Localization.AtPrime P))).IsMaximal := by
    rw [IsLocalization.AtPrime.map_eq_maximalIdeal P (Localization.AtPrime P)]
    infer_instance
  let _ := Ideal.Quotient.field (P.map (algebraMap A (Localization.AtPrime P)))
  have : Module.Free (Localization.AtPrime P ⧸ P.map (algebraMap A (Localization.AtPrime P)))
      ((Localization.AtPrime P ⧸ P.map (algebraMap A (Localization.AtPrime P))) ⊗[
        Localization.AtPrime P] (Localization.AtPrime P ⊗[A] M)) :=
    Module.Free.of_divisionRing _ _
  exact Module.Flat.of_free

/-- Proof of Lemma 4, first sentence ("We may assume that `B` is a polynomial ring over `A`,
suitably graded"): the monomial `∏ tⱼ^{αⱼ}` lies in the degree `∑ αⱼ eⱼ`, so the homomorphism
`A[X_j] → B`, `X_j ↦ t_j`, from the polynomial ring graded by the weights `e_j` to `B` preserves
degrees. -/
private theorem aeval_mem_graded {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    (𝒜 : ℕ → Submodule A B) [GradedAlgebra 𝒜] {κ : Type u} (t : κ → B) (e : κ → ℕ)
    (ht : ∀ j, t j ∈ 𝒜 (e j)) (i : ℕ) {p : MvPolynomial κ A}
    (hp : p ∈ MvPolynomial.weightedHomogeneousSubmodule A e i) : MvPolynomial.aeval t p ∈ 𝒜 i := by
  classical
  rw [MvPolynomial.mem_weightedHomogeneousSubmodule] at hp
  rw [p.as_sum, map_sum]
  refine Submodule.sum_mem _ fun α hα => ?_
  rw [MvPolynomial.aeval_monomial]
  have hw : Finsupp.weight e α = i := hp (MvPolynomial.mem_support_iff.mp hα)
  have hprod : (α.prod fun j k => t j ^ k) ∈ 𝒜 (∑ j ∈ α.support, α j • e j) :=
    SetLike.prod_mem_graded _ _ _ fun j _ => SetLike.pow_mem_graded _ (ht j)
  have h1 : (algebraMap A B (p.coeff α) * α.prod fun i k => t i ^ k) =
      p.coeff α • (α.prod fun i k => t i ^ k) := (Algebra.smul_def _ _).symm
  rw [h1]
  refine Submodule.smul_mem _ _ ?_
  have hw' : ∑ j ∈ α.support, α j • e j = i := by rw [← hw, Finsupp.weight_apply]; rfl
  rwa [hw'] at hprod

section Lemma4

attribute [local instance] baseChangeModule DirectSum.tensorDecomposition

/-- Lemma 4, p. 188, for `B` a polynomial ring over `A`, graded by the positive weights `w`
(the printed proof after its first sentence): "Since `M_P` is a flat `A_P`-module, we have (a′)
`(M/PM)_P` is a flat `(A/P)_P`-module (which is trivial because `(A/P)_P` is a field), and (b′)
`Tor₁^A(M, A/P)_P = 0`.  (See corollary to Lemma 2.)  By Lemma 3, (a′) implies (a).  Since `M` is
a graded `B`-module of finite type, `Tor₁^A(M, A/P)` is also a graded `B`-module of finite type.
Therefore it is clear that (b′) implies (b)."

(a′) is `flat_quotient_tensor_localization_atPrime`.  For (b′), the corollary to Lemma 2
(`flat_tfae_of_graded`, (i) ⇒ (ii)) is applied over the local ring `A_P`, to the graded
`A_P`-algebra `B_P = A_P ⊗_A B` (generated by homogeneous elements of positive degrees) and the
graded `B_P`-module `M_P = A_P ⊗_A M` of finite type (`Hironaka/Compat/GradedBaseChange.lean`),
with `I = P A_P`, which lies in the Jacobson radical of `A_P`: it gives
`Tor₁^{A_P}(M_P, A_P/PA_P) = 0`.  The passage to `Tor₁^A(M, A/P)_P = 0` ("`Tor` commutes with
localization", tacit in the paper) is made on the kernel model `ker (M ⊗_A P → M)` of `Tor₁`
(`compat:tor-one-quotient`; `Hironaka/Compat/TorOneLocalization.lean`).  `Tor₁^A(M, A/P)` as a
graded `B`-module of finite type is `torOneKernel` (`Hironaka/Compat/TorOneGraded.lean`).  By
`exists_smul_eq_zero_of_finite_of_forall` one `g ∉ P` kills it, which is (b) for `g`; Lemma 3
applied to `M/PM` gives `f₀ ∉ P` for (a); (a) and (b) both hold for `f₀ · g` (gap filled: the
paper leaves implicit that they combine). -/
private theorem exists_flat_localization_away_and_tor_eq_zero_mvPolynomial (A : Type u)
    [CommRing A] [IsNoetherianRing A] (κ : Type u) [Fintype κ] (w : κ → ℕ) (hw : ∀ j, 0 < w j)
    (M : Type u) [AddCommGroup M] [Module (MvPolynomial κ A) M] [Module A M]
    [IsScalarTower A (MvPolynomial κ A) M] [Module.Finite (MvPolynomial κ A) M]
    (ℳ : ℕ → Submodule A M)
    [SetLike.GradedSMul (MvPolynomial.weightedHomogeneousSubmodule A w) ℳ]
    [DirectSum.Decomposition ℳ] (P : Ideal A) [P.IsPrime]
    (hP : Module.Flat (Localization.AtPrime P) (LocalizedModule.AtPrime P M)) :
    ∃ f : A, f ∉ P ∧
      Module.Flat (Localization.Away (Ideal.Quotient.mk P f))
        (LocalizedModule (Submonoid.powers (Ideal.Quotient.mk P f))
          (M ⧸ (P • ⊤ : Submodule A M))) ∧
      Subsingleton (LocalizedModule (Submonoid.powers f)
        ↑(((CategoryTheory.Tor (ModuleCat.{u} A) 1).obj (ModuleCat.of A M)).obj
          (ModuleCat.of A (A ⧸ P)))) := by
  classical
  let B := MvPolynomial κ A
  let 𝒜 := MvPolynomial.weightedHomogeneousSubmodule A w
  let _ : GradedAlgebra 𝒜 := MvPolynomial.weightedGradedAlgebra A w
  -- `B` is generated by the homogeneous elements `X_j` of the positive degrees `w j`
  have hgen : Algebra.adjoin A (⋃ n : ℕ, (𝒜 (n + 1) : Set B)) = ⊤ := by
    rw [eq_top_iff, ← MvPolynomial.adjoin_range_X]
    refine Algebra.adjoin_mono ?_
    rintro _ ⟨j, rfl⟩
    refine Set.mem_iUnion.mpr ⟨w j - 1, ?_⟩
    rw [SetLike.mem_coe, Nat.sub_add_cancel (hw j), MvPolynomial.mem_weightedHomogeneousSubmodule]
    exact MvPolynomial.isWeightedHomogeneous_X A w j
  -- the localization `A_P`, the graded `A_P`-algebra `B_P = A_P ⊗_A B` and the graded
  -- `B_P`-module `M_P = A_P ⊗_A M`
  let AP := Localization.AtPrime P
  let I' : Ideal AP := P.map (algebraMap A AP)
  have hflatP : Module.Flat AP (AP ⊗[A] M) :=
    Module.Flat.of_linearEquiv (LocalizedModule.isBaseChange P.primeCompl M).equiv
  -- (a′) `(M/PM)_P` is a flat `(A/P)_P`-module (which is trivial because `(A/P)_P` is a field)
  have _ha' := flat_quotient_tensor_localization_atPrime P M
  -- (b′) `Tor₁^A(M, A/P)_P = 0`.  "(See corollary to Lemma 2.)": over the local ring `A_P`, the
  -- ideal `I = P A_P` lies in the Jacobson radical, and the flat module `M_P` has
  -- `Tor₁^{A_P}(M_P, A_P/PA_P) = 0`
  have hI : I' ≤ Ring.jacobson AP := by
    rw [← Ideal.jacobson_bot, IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top,
      ← IsLocalization.AtPrime.map_eq_maximalIdeal P AP]
  have _ : Module.Finite (AP ⊗[A] B) (AP ⊗[A] M) := baseChange_moduleFinite AP
  have hcor := flat_tfae_of_graded AP (AP ⊗[A] B) (fun n => (𝒜 n).baseChange AP)
    (baseChange_adjoin_eq_top AP 𝒜 hgen) I' hI (AP ⊗[A] M) (fun n => (ℳ n).baseChange AP)
  obtain ⟨-, htorP⟩ := (hcor.out 1 2).mp hflatP
  -- "`Tor` commutes with localization", on the kernel model `ker (M ⊗_A P → M)` of `Tor₁`
  have hinj := (isZero_torOne_quotient_iff I' (AP ⊗[A] M)).mp htorP
  have hb' : ∀ x : M ⊗[A] P, TensorProduct.rid A M (LinearMap.lTensor M P.subtype x) = 0 →
      ∃ s ∉ P, s • x = 0 := fun x hx =>
    exists_smul_eq_zero_of_mul_injective_localization P M P hinj x hx
  -- "Since `M` is a graded `B`-module of finite type, `Tor₁^A(M, A/P)` is also a graded
  -- `B`-module of finite type" (on the kernel model)
  have hKfin : Module.Finite B (torOneKernel B M P) := finite_torOneKernel P
  have _hKgr : (torOneKernel B M P).IsHomogeneous (DirectSum.decomposeTensor ℳ P) :=
    isHomogeneous_torOneKernel B P ℳ
  -- "Therefore it is clear that (b′) implies (b)"
  have hmem : ∀ x : M ⊗[A] P, x ∈ torOneKernel B M P →
      TensorProduct.rid A M (LinearMap.lTensor M P.subtype x) = 0 := fun x hx => by
    rw [← mulIdealB_apply (B := B)]
    exact hx
  obtain ⟨g, hgP, hg⟩ := exists_smul_eq_zero_of_finite_of_forall B P (K := torOneKernel B M P)
    fun k => by
      obtain ⟨s, hs, h⟩ := hb' k.1 (hmem k.1 k.2)
      exact ⟨s, hs, Subtype.ext h⟩
  obtain ⟨Φ, hΦ, hΦμ⟩ := exists_torOne_quotient_injective P M
  have hTor : Subsingleton (LocalizedModule (Submonoid.powers g)
      ↑(((CategoryTheory.Tor (ModuleCat.{u} A) 1).obj (ModuleCat.of A M)).obj
        (ModuleCat.of A (A ⧸ P)))) :=
    subsingleton_localizedModule_powers_of_smul_eq_zero g fun t => by
      apply hΦ
      rw [map_smul, map_zero]
      exact congrArg Subtype.val
        (hg ⟨Φ t, by rw [torOneKernel, LinearMap.mem_ker, mulIdealB_apply]; exact hΦμ t⟩)
  -- (a): "By Lemma 3, (a′) implies (a)": Lemma 3 applied to `M/PM` over the domain `A/P`
  obtain ⟨f, hfP, hflat⟩ := exists_flat_localization_quotient A B M P
  -- gap filled: the elements obtained for (a) and (b) combine to `f * g`
  exact ⟨f * g, fun h => ((inferInstance : P.IsPrime).mem_or_mem h).elim hfP hgP, hflat g,
    subsingleton_localizedModule_powers_mul f g hTor⟩

end Lemma4

/-- Lemma 4, p. 188: "Let `A` be a noetherian ring, `B` a graded `A`-algebra of finite type and
`M` a graded `B`-module of finite type. Assume that `B` is generated by homogeneous elements of
positive degrees as an `A`-algebra. Let `P` be a prime ideal in `A` such that `M_P` is a flat
`A_P`-module. Then there exists an element `f ∈ A − P` such that (a) `(M/PM)_f` is a flat
`(A/P)_f`-module, (b) `Tor₁^A(M, A/P)_f = 0`."  (See Lemma 6.8 of Grothendieck's seminar
note.)

Encoding: gradings as in the corollary to Lemma 2; `(M/PM)_f` is the localization of the
`A/P`-module `M ⧸ P•M` at the powers of the image of `f` in `A/P`; `Tor₁^A(M, A/P)_f` is the
localization at the powers of `f` of the categorical `Tor (ModuleCat A) 1`, and "`= 0`" is
`Subsingleton`.  Mathlib's `Tor` has no `B`-module structure and no localization, so the paper's
`Tor₁^A(M, A/P)` as a graded `B`-module of finite type is realized by its identification with
`ker (M ⊗_A P → M)` (`compat:tor-one-quotient`, `exists_torOne_quotient_injective`), a graded
`B`-submodule of `M ⊗_A P` (`torOneKernel`).

Proof, as printed (p. 188): "We may assume that `B` is a polynomial ring over `A`, suitably graded": `B` is the quotient of
the polynomial ring `A[X_j]`, graded by the degrees `e_j > 0` of homogeneous generators `t_j` of
`B`, by `X_j ↦ t_j`, a surjective homomorphism of graded algebras (`aeval_mem_graded`); `M` is a
graded module of finite type over `A[X_j]` through it, and neither `M_P`, nor (a), nor (b)
involves `B`.  The polynomial case is
`exists_flat_localization_away_and_tor_eq_zero_mvPolynomial`, where the rest of the printed proof
is carried out step by step: (a′) is trivial since `(A/P)_P` is a field; (b′) is the corollary to
Lemma 2 applied over `A_P`; "By Lemma 3, (a′) implies (a)" is Lemma 3 for `M/PM` over the domain
`A/P`; "`Tor₁^A(M, A/P)` is also a graded `B`-module of finite type" and "it is clear that (b′)
implies (b)" are `torOneKernel` (finite type, graded) and
`exists_smul_eq_zero_of_finite_of_forall`.

Gaps filled (the paper states these without argument): `Tor₁^A(M, A/P)_P ≅ Tor₁^{A_P}(M_P,
A_P/PA_P)` ("`Tor` commutes with localization"), proved on the kernel model
(`exists_smul_eq_zero_of_mul_injective_localization`); that `B_P = A_P ⊗_A B` and `M_P = A_P ⊗_A M`
are again a graded algebra generated by homogeneous elements of positive degrees and a graded
module of finite type (`Hironaka/Compat/GradedBaseChange.lean`), which the corollary to Lemma 2
needs; that the element `f` obtained for (a) by Lemma 3 and the element `g` obtained for (b)
combine to the single element `f g` of the statement (`subsingleton_localizedModule_powers_mul`,
`flat_localization_away_mul`).  Remark: Lemma 3 gives (a) outright, so (a′) is not used for it. -/
@[blueprint "lem:II.1-4"
  (statement := /-- Let $A$ be a noetherian ring, $B$ a graded $A$-algebra of finite type and
    $M$ a graded $B$-module of finite type. Assume that $B$ is generated by homogeneous
    elements of positive degrees as an $A$-algebra. Let $P$ be a prime ideal in $A$ such that
    $M_P$ is a flat $A_P$-module. Then there exists an element $f\in A-P$ such that (a)
    $(M/PM)_f$ is a flat $(A/P)_f$-module, (b) $\operatorname{Tor}_1^A(M,A/P)_f=0$.
    (p.~188.) -/)
  (proof := /-- (The paper's proof, p.~188; the lemma itself is cited as ``Lemma 6.8 of the
    above cited seminar note by Grothendieck'', S\'eminaire de G\'eom\'etrie Alg\'ebrique de
    l'IHES, No.~IV (1960).) We may assume that $B$ is a polynomial ring
    over $A$, suitably graded. Since $M_P$ is a flat $A_P$-module, we have (a$'$) $(M/PM)_P$
    is a flat $(A/P)_P$-module (which is trivial because $(A/P)_P$ is a field), and (b$'$)
    $\operatorname{Tor}_1^A(M,A/P)_P=0$ (see \cref{cor:II.1-lem2}). By \cref{lem:II.1-3},
    (a$'$) implies (a). Since $M$ is a graded $B$-module of finite type,
    $\operatorname{Tor}_1^A(M,A/P)$ is also a graded $B$-module of finite type. Therefore it
    is clear that (b$'$) implies (b).

    \textbf{Formalization.} The Lean proof follows the printed one. The reduction to a
    polynomial ring is made through the surjection $A[X_j]\to B$, $X_j\mapsto t_j$, where the
    $t_j$ are homogeneous generators of $B$ of positive degrees $e_j$ and $A[X_j]$ is graded by
    the weights $e_j$. In the polynomial case, \cref{cor:II.1-lem2} is applied over the local
    ring $A_P$ to the graded $A_P$-algebra $B_P=A_P\otimes_AB$ and the graded $B_P$-module
    $M_P=A_P\otimes_AM$ of finite type, with $I=PA_P$ (contained in the Jacobson radical of
    $A_P$); it gives $\operatorname{Tor}_1^{A_P}(M_P,A_P/PA_P)=0$. Since Mathlib's
    $\operatorname{Tor}$ has neither a $B$-module structure nor a localization,
    $\operatorname{Tor}_1^A(M,A/P)$ is realized as $\ker(M\otimes_AP\to M)$
    (\cref{compat:tor-one-quotient}), a graded $B$-submodule of $M\otimes_AP$ of finite type,
    and $\operatorname{Tor}_1^A(M,A/P)_P=0$ is proved on this model: the kernel commutes with
    localization at $P$ (the localization of $M\otimes_AP$ at $P$ is
    $M_P\otimes_{A_P}PA_P$). A $B$-module of finite type each of whose elements is killed by
    an element outside $P$ is killed by one such element $g$ (the product over a finite set of
    generators); this is (b) with $f=g$. \cref{lem:II.1-3} applied to $M/PM$ over $A/P$ gives
    $f_0$ for (a). The paper leaves implicit that (a) and (b) can be obtained for the same $f$:
    both persist when $f$ is multiplied by an element outside $P$, and $f_0g$ serves. -/)
  (latexEnv := "lemma")]
theorem exists_flat_localization_away_and_tor_eq_zero (A : Type u) [CommRing A]
    [IsNoetherianRing A] (B : Type u) [CommRing B] [Algebra A B] (𝒜 : ℕ → Submodule A B)
    [GradedAlgebra 𝒜] [Algebra.FiniteType A B]
    (hgen : Algebra.adjoin A (⋃ n : ℕ, (𝒜 (n + 1) : Set B)) = ⊤)
    (M : Type u) [AddCommGroup M] [Module B M] [Module A M] [IsScalarTower A B M]
    [Module.Finite B M] (ℳ : ℕ → Submodule A M) [SetLike.GradedSMul 𝒜 ℳ]
    [DirectSum.Decomposition ℳ] (P : Ideal A) [P.IsPrime]
    (hP : Module.Flat (Localization.AtPrime P) (LocalizedModule.AtPrime P M)) :
    ∃ f : A, f ∉ P ∧
      Module.Flat (Localization.Away (Ideal.Quotient.mk P f))
        (LocalizedModule (Submonoid.powers (Ideal.Quotient.mk P f))
          (M ⧸ (P • ⊤ : Submodule A M))) ∧
      Subsingleton (LocalizedModule (Submonoid.powers f)
        ↑(((CategoryTheory.Tor (ModuleCat.{u} A) 1).obj (ModuleCat.of A M)).obj
          (ModuleCat.of A (A ⧸ P)))) := by
  classical
  -- "We may assume that `B` is a polynomial ring over `A`, suitably graded."
  obtain ⟨κ, _, t, e, he, ht, htgen⟩ := exists_positive_degree_generators 𝒜 hgen
  -- `π : A[X_j] → B`, `X_j ↦ t_j`, is a surjective homomorphism of graded algebras
  let π : MvPolynomial κ A →ₐ[A] B := MvPolynomial.aeval t
  have hπ : Function.Surjective π := fun b => by
    have : b ∈ Algebra.adjoin A (Set.range t) := htgen ▸ Algebra.mem_top
    rwa [Algebra.adjoin_range_eq_range_aeval] at this
  -- `M` is a graded module of finite type over the polynomial ring, via `π`
  let _ : Module (MvPolynomial κ A) M := Module.compHom M π.toRingHom
  have hsmul : ∀ (q : MvPolynomial κ A) (m : M), q • m = π q • m := fun _ _ => rfl
  have : IsScalarTower A (MvPolynomial κ A) M :=
    ⟨fun a q m => by rw [hsmul, hsmul, map_smul, smul_assoc]⟩
  have : Module.Finite (MvPolynomial κ A) M := by
    obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := B) (M := M)
    refine Module.finite_def.mpr ⟨s, ?_⟩
    rw [eq_top_iff]
    intro m _
    clear ‹m ∈ ⊤›
    have hm : m ∈ Submodule.span B (s : Set M) := hs ▸ Submodule.mem_top
    induction hm using Submodule.span_induction with
    | mem x hx => exact Submodule.subset_span hx
    | zero => exact zero_mem _
    | add x y _ _ hx hy => exact add_mem hx hy
    | smul b y _ hy =>
      obtain ⟨q, rfl⟩ := hπ b
      exact Submodule.smul_mem _ q hy
  have : SetLike.GradedSMul (MvPolynomial.weightedHomogeneousSubmodule A e) ℳ :=
    ⟨fun {i j q m} hq hm => by
      rw [hsmul]
      exact SetLike.GradedSMul.smul_mem (aeval_mem_graded 𝒜 t e ht i hq) hm⟩
  exact exists_flat_localization_away_and_tor_eq_zero_mvPolynomial A κ e he M ℳ P hP

/-- `M_Q` is flat over `A_Q` iff every element of `ker (M ⊗_A J → M)` (`J` an ideal) is killed
by an element outside `Q`. -/
private theorem flat_localization_iff_ker {A : Type u} [CommRing A] (M : Type u) [AddCommGroup M]
    [Module A M] (Q : Ideal A) [Q.IsPrime] :
    Module.Flat (Localization.AtPrime Q) (LocalizedModule.AtPrime Q M) ↔
      ∀ (J : Ideal A) (x : M ⊗[A] J), TensorProduct.rid A M (LinearMap.lTensor M J.subtype x) = 0 →
        ∃ s ∉ Q, s • x = 0 := by
  let S := Q.primeCompl
  let ℓ := LocalizedModule.mkLinearMap S M
  rw [Module.flat_iff_of_isLocalization (Localization.AtPrime Q) S]
  have hnat : ∀ (J : Ideal A) (y : M ⊗[A] J), TensorProduct.rid A _ (LinearMap.lTensor _ J.subtype
      (TensorProduct.AlgebraTensorModule.rTensor A J ℓ y)) =
      ℓ (TensorProduct.rid A M (LinearMap.lTensor M J.subtype y)) := by
    intro J y
    induction y using TensorProduct.inductionOn with
    | tmul m p => simp [ℓ]
    | add y z hy hz => rw [map_add, map_add, map_add, hy, hz, map_add, map_add, map_add]
  constructor
  · intro hflat J x hx
    have hinj : Function.Injective (fun y : LocalizedModule S M ⊗[A] J =>
        TensorProduct.rid A _ (LinearMap.lTensor _ J.subtype y)) :=
      (TensorProduct.rid A _).injective.comp
        (Module.Flat.lTensor_preserves_injective_linearMap _ Subtype.val_injective)
    have h0 : TensorProduct.AlgebraTensorModule.rTensor A J ℓ x =
        TensorProduct.AlgebraTensorModule.rTensor A J ℓ 0 := by
      rw [map_zero]
      apply hinj
      simp only
      rw [hnat, hx, map_zero, map_zero, map_zero]
    obtain ⟨c, hc⟩ := IsLocalizedModule.exists_of_eq (S := S) h0
    exact ⟨c, c.2, by rw [smul_zero] at hc; exact hc⟩
  · intro h
    rw [Module.Flat.iff_lTensor_injective']
    intro J
    let ρ := TensorProduct.AlgebraTensorModule.rTensor A J ℓ
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro y hy
    obtain ⟨⟨x, s⟩, hs⟩ := IsLocalizedModule.surj S ρ y
    simp only [Submonoid.smul_def] at hs
    -- `s • y = ρ x`
    have hx0 : ℓ (TensorProduct.rid A M (LinearMap.lTensor M J.subtype x)) = 0 := by
      rw [← hnat]
      change TensorProduct.rid A _ (LinearMap.lTensor _ J.subtype (ρ x)) = 0
      rw [← hs, map_smul, map_smul]
      have hy' : LinearMap.lTensor _ J.subtype y = 0 := hy
      rw [hy', map_zero, smul_zero]
    obtain ⟨t, ht⟩ := IsLocalizedModule.exists_of_eq (S := S) (hx0.trans (map_zero ℓ).symm)
    rw [smul_zero, Submonoid.smul_def, ← map_smul, ← map_smul] at ht
    obtain ⟨s', hs'Q, hs'⟩ := h J _ ht
    have hunit : IsUnit (algebraMap A (Module.End A (LocalizedModule S M ⊗[A] J))
        (s' * t * s)) := IsLocalizedModule.map_units ρ ⟨s' * t * s, by
          exact S.mul_mem (S.mul_mem hs'Q t.2) s.2⟩
    have : (s' * t * s) • y = 0 := by
      rw [mul_smul, hs, mul_smul, ← map_smul, ← map_smul, hs', map_zero]
    exact (Module.End.isUnit_iff _).mp hunit |>.1 (by rw [map_zero]; exact this)

/-- The kernel condition `[*]_Q` for a graded module follows from that of its homogeneous parts. -/
private theorem ker_cond_of_pieces {A : Type u} [CommRing A] {M : Type u} [AddCommGroup M]
    [Module A M]
    (ℳ : ℕ → Submodule A M) [DirectSum.Decomposition ℳ] (Q : Ideal A) [Q.IsPrime]
    (h : ∀ (n : ℕ) (J : Ideal A) (x : ℳ n ⊗[A] J),
      TensorProduct.rid A (ℳ n) (LinearMap.lTensor (ℳ n) J.subtype x) = 0 → ∃ s ∉ Q, s • x = 0)
    (J : Ideal A) (x : M ⊗[A] J)
    (hx : TensorProduct.rid A M (LinearMap.lTensor M J.subtype x) = 0) :
    ∃ s ∉ Q, s • x = 0 := by
  classical
  let ι : ∀ n, ℳ n →ₗ[A] M := fun n => (ℳ n).subtype
  let π : ∀ n, M →ₗ[A] ℳ n := fun n =>
    DirectSum.component A ℕ (fun i => ℳ i) n ∘ₗ (DirectSum.decomposeLinearEquiv ℳ).toLinearMap
  have hπ : ∀ n m, (π n m : M) = DirectSum.decompose ℳ m n := fun n m => rfl
  -- every `m` is the sum of its homogeneous components over any superset of its support
  have hdec : ∀ (m : M) (N : Finset ℕ), (DirectSum.decompose ℳ m).support ⊆ N →
      ∑ n ∈ N, ι n (π n m) = m := by
    intro m N hN
    conv_rhs => rw [← DirectSum.sum_support_decompose ℳ m]
    symm
    refine Finset.sum_subset hN fun n _ hn => ?_
    show (π n m : M) = 0
    rw [hπ, DFinsupp.notMem_support_iff.mp hn]
    rfl
  have hsplit : ∀ y : M ⊗[A] J, ∃ N : Finset ℕ, ∀ N' : Finset ℕ, N ⊆ N' →
      ∑ n ∈ N', LinearMap.rTensor J (ι n ∘ₗ π n) y = y := by
    intro y
    induction y using TensorProduct.inductionOn with
    | tmul m j =>
      refine ⟨(DirectSum.decompose ℳ m).support, fun N' hN' => ?_⟩
      simp only [LinearMap.rTensor_tmul, LinearMap.comp_apply]
      rw [← TensorProduct.sum_tmul, hdec m N' hN']
    | add y z hy hz =>
      obtain ⟨N₁, h₁⟩ := hy
      obtain ⟨N₂, h₂⟩ := hz
      refine ⟨N₁ ∪ N₂, fun N' hN' => ?_⟩
      simp only [map_add, Finset.sum_add_distrib]
      rw [h₁ N' (Finset.union_subset_left hN'), h₂ N' (Finset.union_subset_right hN')]
  -- the components of `x` lie in the kernels for the `Mₙ`
  have hcomp : ∀ n (y : M ⊗[A] J), TensorProduct.rid A (ℳ n) (LinearMap.lTensor (ℳ n) J.subtype
      (LinearMap.rTensor J (π n) y)) = π n (TensorProduct.rid A M
        (LinearMap.lTensor M J.subtype y)) := by
    intro n y
    induction y using TensorProduct.inductionOn with
    | tmul m j => simp
    | add y z hy hz => simp only [map_add, hy, hz]
  choose s hsQ hs using fun n => h n J (LinearMap.rTensor J (π n) x) (by rw [hcomp, hx, map_zero])
  obtain ⟨N, hN⟩ := hsplit x
  refine ⟨∏ n ∈ N, s n, fun hmem => ?_, ?_⟩
  · have : ∏ n ∈ N, s n ∈ Q.primeCompl := Submonoid.prod_mem _ fun n _ => hsQ n
    exact this hmem
  · rw [← hN N subset_rfl, Finset.smul_sum]
    refine Finset.sum_eq_zero fun n hn => ?_
    rw [LinearMap.rTensor_comp_apply, ← map_smul, ← Finset.mul_prod_erase N s hn, mul_comm,
      mul_smul, hs n, smul_zero, map_zero]

/-- The openness criterion of the proof of Theorem 1 (p. 189): in a noetherian quasi-sober space,
a set `U` stable under generization which contains, with each point `x`, a non-empty open subset
of `closure {x}` around `x`, is open. -/
private theorem isOpen_of_generalization_of_exists_open {X : Type*} [TopologicalSpace X]
    [TopologicalSpace.NoetherianSpace X] [QuasiSober X] (U : Set X)
    (h1 : ∀ x y : X, x ⤳ y → y ∈ U → x ∈ U)
    (h2 : ∀ x ∈ U, ∃ O : Set X, IsOpen O ∧ x ∈ O ∧ O ∩ closure {x} ⊆ U) : IsOpen U := by
  classical
  rw [← isClosed_compl_iff]
  set Z := Uᶜ with hZdef
  have hZ : ∀ x y : X, x ⤳ y → x ∈ Z → y ∈ Z := fun x y hxy hx hy => hx (h1 x y hxy hy)
  have hex : ∃ n : ℕ, ∃ S : Finset (Set X), S.card = n ∧ (∀ t ∈ S, IsClosed t) ∧
      (∀ t ∈ S, IsIrreducible t) ∧ closure Z = ⋃ t ∈ S, t := by
    obtain ⟨S, hSfin, hScl, hSirr, hSeq⟩ :=
      TopologicalSpace.NoetherianSpace.exists_finite_set_isClosed_irreducible
        (isClosed_closure (s := Z))
    refine ⟨hSfin.toFinset.card, hSfin.toFinset, rfl, fun t ht => hScl t (by simpa using ht),
      fun t ht => hSirr t (by simpa using ht), ?_⟩
    rw [hSeq, Set.sUnion_eq_biUnion]
    simp
  obtain ⟨S, hScard, hScl, hSirr, hSeq⟩ := Nat.find_spec hex
  have hmin : ∀ S' : Finset (Set X), S'.card < S.card → (∀ t ∈ S', IsClosed t) →
      (∀ t ∈ S', IsIrreducible t) → closure Z ≠ ⋃ t ∈ S', t := by
    intro S' hlt hcl hirr heq
    rw [hScard] at hlt
    exact Nat.find_min hex hlt ⟨S', rfl, hcl, hirr, heq⟩
  refine closure_subset_iff_isClosed.mp fun y hy => ?_
  rw [hSeq, Set.mem_iUnion₂] at hy
  obtain ⟨t, ht, hyt⟩ := hy
  obtain ⟨η, hη⟩ := QuasiSober.sober (hSirr t ht) (hScl t ht)
  suffices hηZ : η ∈ Z by
    have : η ⤳ y := by
      rw [specializes_iff_mem_closure, hη.def]
      exact hyt
    exact hZ η y this hηZ
  by_contra hηZ
  have hηU : η ∈ U := by simpa [hZdef] using hηZ
  obtain ⟨O, hO, hηO, hOU⟩ := h2 η hηU
  -- `η` lies in no other member of `S`
  have hηt' : ∀ t' ∈ S.erase t, η ∉ t' := by
    intro t' ht' hηt'
    have htt' : t ⊆ t' := by
      rw [← hη.def]
      exact (hScl t' (Finset.mem_of_mem_erase ht')).closure_subset_iff.mpr
        (Set.singleton_subset_iff.mpr hηt')
    apply hmin (S.erase t) (Finset.card_erase_lt_of_mem ht)
      (fun s hs => hScl s (Finset.mem_of_mem_erase hs))
      (fun s hs => hSirr s (Finset.mem_of_mem_erase hs))
    rw [hSeq]
    apply le_antisymm
    · intro z hz
      rw [Set.mem_iUnion₂] at hz ⊢
      obtain ⟨s, hs, hzs⟩ := hz
      by_cases hst : s = t
      · subst hst
        exact ⟨t', ht', htt' hzs⟩
      · exact ⟨s, Finset.mem_erase.mpr ⟨hst, hs⟩, hzs⟩
    · intro z hz
      rw [Set.mem_iUnion₂] at hz ⊢
      obtain ⟨s, hs, hzs⟩ := hz
      exact ⟨s, Finset.mem_of_mem_erase hs, hzs⟩
  set O' := O ∩ ⋂ t' ∈ S.erase t, t'ᶜ with hO'
  have hO'open : IsOpen O' :=
    hO.inter (isOpen_biInter_finset fun t' ht' =>
      (hScl t' (Finset.mem_of_mem_erase ht')).isOpen_compl)
  have hηO' : η ∈ O' := ⟨hηO, Set.mem_iInter₂.mpr fun t' ht' => hηt' t' ht'⟩
  have hZO' : Z ⊆ O'ᶜ := by
    intro z hzZ hzO'
    have hzC : z ∈ closure Z := subset_closure hzZ
    rw [hSeq, Set.mem_iUnion₂] at hzC
    obtain ⟨s, hs, hzs⟩ := hzC
    by_cases hst : s = t
    · subst hst
      have : z ∈ U := hOU ⟨hzO'.1, by rw [hη.def]; exact hzs⟩
      exact hzZ this
    · exact (Set.mem_iInter₂.mp hzO'.2 s (Finset.mem_erase.mpr ⟨hst, hs⟩)) hzs
  have hcl : closure Z ⊆ O'ᶜ := closure_minimal hZO' hO'open.isClosed_compl
  have hηC : η ∈ closure Z := by
    rw [hSeq, Set.mem_iUnion₂]
    exact ⟨t, ht, hη.mem⟩
  exact hcl hηC hηO'

/-- Flatness of `(N/PN)_f` over `(A/P)_f` gives flatness of `(A_Q/PA_Q) ⊗_{A_Q} (A_Q ⊗_A N)` over
`A_Q/PA_Q` for every prime `Q ∌ f`. -/
private theorem flat_quot_tensor_localization {A : Type u} [CommRing A] (N : Type u)
    [AddCommGroup N]
    [Module A N] (P Q : Ideal A) [P.IsPrime] [Q.IsPrime] (f : A) (hfQ : f ∉ Q)
    (ha : Module.Flat (Localization.Away (Ideal.Quotient.mk P f))
      (LocalizedModule (Submonoid.powers (Ideal.Quotient.mk P f)) (N ⧸ (P • ⊤ : Submodule A N)))) :
    Module.Flat (Localization.AtPrime Q ⧸ P.map (algebraMap A (Localization.AtPrime Q)))
      ((Localization.AtPrime Q ⧸ P.map (algebraMap A (Localization.AtPrime Q))) ⊗[
        Localization.AtPrime Q] (Localization.AtPrime Q ⊗[A] N)) := by
  let AQ := Localization.AtPrime Q
  let R' := AQ ⧸ P.map (algebraMap A AQ)
  let fb : A ⧸ P := Ideal.Quotient.mk P f
  let Af := Localization.Away fb
  -- `f` becomes a unit in `R'`
  have hunit : IsUnit (algebraMap (A ⧸ P) R' fb) := by
    rw [Ideal.Quotient.algebraMap_quotient_map_quotient]
    exact (IsLocalization.map_units AQ (⟨f, hfQ⟩ : Q.primeCompl)).map _
  let φ : Af →+* R' := IsLocalization.Away.lift fb hunit
  let _ : Algebra Af R' := φ.toAlgebra
  have : IsScalarTower (A ⧸ P) Af R' := IsScalarTower.of_algebraMap_eq fun a =>
    (IsLocalization.Away.lift_eq fb hunit a).symm
  -- `X_f = A_f ⊗ X`, flat over `A_f`; base change to `R'`
  let eX : Af ⊗[A ⧸ P] (N ⧸ (P • ⊤ : Submodule A N)) ≃ₗ[Af]
      LocalizedModule (Submonoid.powers fb) (N ⧸ (P • ⊤ : Submodule A N)) :=
    (IsLocalizedModule.isBaseChange (Submonoid.powers fb) Af
      (LocalizedModule.mkLinearMap _ _)).equiv
  have h1 : Module.Flat Af (Af ⊗[A ⧸ P] (N ⧸ (P • ⊤ : Submodule A N))) :=
    Module.Flat.of_linearEquiv eX
  have h2 : Module.Flat R' (R' ⊗[Af] (Af ⊗[A ⧸ P] (N ⧸ (P • ⊤ : Submodule A N)))) :=
    inferInstance
  have h3 : Module.Flat R' (R' ⊗[A ⧸ P] (N ⧸ (P • ⊤ : Submodule A N))) :=
    Module.Flat.of_linearEquiv
      (TensorProduct.AlgebraTensorModule.cancelBaseChange (A ⧸ P) Af R' R' _).symm
  -- `N/PN = (A/P) ⊗_A N`
  let e3 : (A ⧸ P) ⊗[A] N ≃ₗ[A ⧸ P] N ⧸ (P • ⊤ : Submodule A N) :=
    (TensorProduct.quotTensorEquivQuotSMul N P).extendScalarsOfSurjective
      Ideal.Quotient.mk_surjective
  have h4 : Module.Flat R' (R' ⊗[A ⧸ P] ((A ⧸ P) ⊗[A] N)) :=
    Module.Flat.of_linearEquiv
      (TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl R' R') e3)
  have h5 : Module.Flat R' (R' ⊗[A] N) :=
    Module.Flat.of_linearEquiv
      (TensorProduct.AlgebraTensorModule.cancelBaseChange A (A ⧸ P) R' R' N).symm
  exact Module.Flat.of_linearEquiv
    (TensorProduct.AlgebraTensorModule.cancelBaseChange A AQ R' R' N)

/-- Proof of Theorem 1, p. 189: the base change `R ⊗_A M` of `M = ⊕ Mₙ` is flat over `R` if and
only if all the `R ⊗_A Mₙ` are ("the direct summands of a flat module are flat", as in the proof of
the corollary to Lemma 2 (p. 182), applied to the `R`-module `R ⊗_A M`, whose homogeneous parts
are the base changes of the `Mₙ`). -/
private theorem flat_tensor_iff_forall_flat_graded {A : Type u} [CommRing A] (R : Type u)
    [CommRing R] [Algebra A R] {M : Type u} [AddCommGroup M] [Module A M]
    (ℳ : ℕ → Submodule A M) [DirectSum.Decomposition ℳ] :
    Module.Flat R (R ⊗[A] M) ↔ ∀ n, Module.Flat R (R ⊗[A] ℳ n) := by
  classical
  have e : ∀ n, (R ⊗[A] ℳ n) ≃ₗ[R] ((ℳ n).baseChange R) := fun n =>
    LinearEquiv.ofBijective ((ℳ n).toBaseChange R) (DirectSum.toBaseChange_bijective ℳ n)
  rw [flat_iff_forall_flat_graded (A := R) (M := R ⊗[A] M) (fun n => (ℳ n).baseChange R)]
  exact forall_congr' fun n => ⟨fun h => Module.Flat.of_linearEquiv (e n),
    fun h => Module.Flat.of_linearEquiv (e n).symm⟩

/-- Proof of Theorem 1, (ii) (via Lemma 4 (b)): if the localization of `T` at the powers of `f`
vanishes, each `t ∈ T` is killed by a power of `f`. -/
private theorem exists_pow_smul_eq_zero_of_subsingleton_localizedModule_powers {A : Type u}
    [CommRing A] {T : Type u} [AddCommGroup T] [Module A T] {f : A}
    (h : Subsingleton (LocalizedModule (Submonoid.powers f) T)) (t : T) :
    ∃ n : ℕ, f ^ n • t = 0 := by
  have h0 : LocalizedModule.mk t (1 : Submonoid.powers f) = LocalizedModule.mk 0 1 :=
    Subsingleton.elim _ _
  obtain ⟨⟨_, n, rfl⟩, hn⟩ := LocalizedModule.mk_eq.mp h0
  exact ⟨n, by simpa [Submonoid.smul_def] using hn⟩

/-- Theorem 1, proof of (i), p. 189: "First of all, (i) is clear.  In fact, for each non-negative
integer `n`, if `(Mₙ)_P` is a free `A_P`-module, then `(Mₙ)_F` is a free `A_F`-module where `Mₙ`
denotes the homogeneous part of degree `n` of `M`."  Here `M_P` is flat if and only if all the
`(Mₙ)_P` are free (the `Mₙ` are of finite type, as in the proof of the corollary to Lemma 2; Lemma
1 for the local ring `A_P`; `M_P = ⊕ (Mₙ)_P`), and `(Mₙ)_F = A_F ⊗_{A_P} (Mₙ)_P` is free if
`(Mₙ)_P` is. -/
private theorem flat_localization_of_le {A : Type u} [CommRing A] [IsNoetherianRing A]
    (B : Type u) [CommRing B] [Algebra A B] (𝒜 : ℕ → Submodule A B) [GradedAlgebra 𝒜]
    [Algebra.FiniteType A B] (hgen : Algebra.adjoin A (⋃ n : ℕ, (𝒜 (n + 1) : Set B)) = ⊤)
    (M : Type u) [AddCommGroup M] [Module B M] [Module A M] [IsScalarTower A B M]
    [Module.Finite B M] (ℳ : ℕ → Submodule A M) [SetLike.GradedSMul 𝒜 ℳ]
    [DirectSum.Decomposition ℳ] {F P : Ideal A} [F.IsPrime] [P.IsPrime] (hFP : F ≤ P)
    (hP : Module.Flat (Localization.AtPrime P) (LocalizedModule.AtPrime P M)) :
    Module.Flat (Localization.AtPrime F) (LocalizedModule.AtPrime F M) := by
  classical
  let AP := Localization.AtPrime P
  let AF := Localization.AtPrime F
  have hle : P.primeCompl ≤ F.primeCompl := fun a ha haF => ha (hFP haF)
  let _ : Algebra AP AF :=
    IsLocalization.localizationAlgebraOfSubmonoidLe AP AF P.primeCompl F.primeCompl hle
  have : IsScalarTower A AP AF :=
    IsLocalization.localization_isScalarTower_of_submonoid_le AP AF P.primeCompl F.primeCompl hle
  -- `A_P ⊗_A M = M_P` is flat, so each `(Mₙ)_P` is flat; it is of finite type, hence free (Lemma 1)
  have hPM : Module.Flat AP (AP ⊗[A] M) :=
    Module.Flat.of_linearEquiv (LocalizedModule.isBaseChange P.primeCompl M).equiv
  have hfree : ∀ n, Module.Free AP (AP ⊗[A] ℳ n) := fun n => by
    have := finite_piece_of_adjoin_eq_top B 𝒜 hgen M ℳ n
    exact ((free_projective_flat_tfae AP (AP ⊗[A] ℳ n)).out 1 3).mpr
      ((flat_tensor_iff_forall_flat_graded AP ℳ).mp hPM n)
  -- "if `(Mₙ)_P` is a free `A_P`-module, then `(Mₙ)_F` is a free `A_F`-module": `A_F ⊗_{A_P} -`
  have hfreeF : ∀ n, Module.Flat AF (AF ⊗[A] ℳ n) := fun n => by
    have := hfree n
    have : Module.Free AF (AF ⊗[A] ℳ n) :=
      Module.Free.of_equiv (TensorProduct.AlgebraTensorModule.cancelBaseChange A AP AF AF (ℳ n))
    exact Module.Flat.of_free
  -- `A_F ⊗_A M = ⊕ A_F ⊗_A Mₙ` is flat, and so is `M_F`
  have hFM : Module.Flat AF (AF ⊗[A] M) := (flat_tensor_iff_forall_flat_graded AF ℳ).mpr hfreeF
  exact Module.Flat.of_linearEquiv (LocalizedModule.isBaseChange F.primeCompl M).equiv.symm

section Theorem1

attribute [local instance] baseChangeModule

/-- Theorem 1, proof of (ii), p. 189: "Then (ii) follows Lemma 4 and corollary to Lemma 2."  Let
`f ∈ A − P` be as in Lemma 4, so that (a) `(M/PM)_f` is a flat `(A/P)_f`-module and (b)
`Tor₁^A(M, A/P)_f = 0`, and let `Q` be a prime ideal containing `P` with `f ∉ Q` (the points of
the non-empty open subset `D(f)` of `Spec(A/P) = V(P)`).  The corollary to Lemma 2 is applied to
the local ring `A_Q`, the graded `A_Q`-algebra `B_Q = A_Q ⊗_A B`, the graded `B_Q`-module
`M_Q = A_Q ⊗_A M` of finite type (`Hironaka/Compat/GradedBaseChange.lean`) and `I = PA_Q`, which
lies in the Jacobson radical of `A_Q` since `P ⊆ Q`: by (ii) ⇒ (i), `M_Q` is flat over `A_Q`
once `M_Q ⊗_{A_Q} A_Q/PA_Q` is flat over `A_Q/PA_Q` (this is (a), localized at `Q`) and
`Tor₁^{A_Q}(M_Q, A_Q/PA_Q) = 0` (this is (b), localized at `Q`: "`Tor` commutes with
localization", tacit in the paper, proved on the kernel model `ker (M ⊗_A P → M)` of `Tor₁`,
`Hironaka/Compat/TorOneLocalization.lean`). -/
private theorem flat_localization_of_flat_quotient_of_tor_eq_zero {A : Type u} [CommRing A]
    [IsNoetherianRing A] (B : Type u) [CommRing B] [Algebra A B] (𝒜 : ℕ → Submodule A B)
    [GradedAlgebra 𝒜] [Algebra.FiniteType A B]
    (hgen : Algebra.adjoin A (⋃ n : ℕ, (𝒜 (n + 1) : Set B)) = ⊤)
    (M : Type u) [AddCommGroup M] [Module B M] [Module A M] [IsScalarTower A B M]
    [Module.Finite B M] (ℳ : ℕ → Submodule A M) [SetLike.GradedSMul 𝒜 ℳ]
    [DirectSum.Decomposition ℳ] (P Q : Ideal A) [P.IsPrime] [Q.IsPrime] (hPQ : P ≤ Q) (f : A)
    (hfQ : f ∉ Q)
    (hflat : Module.Flat (Localization.Away (Ideal.Quotient.mk P f))
      (LocalizedModule (Submonoid.powers (Ideal.Quotient.mk P f))
        (M ⧸ (P • ⊤ : Submodule A M))))
    (hTor : Subsingleton (LocalizedModule (Submonoid.powers f)
      ↑(((CategoryTheory.Tor (ModuleCat.{u} A) 1).obj (ModuleCat.of A M)).obj
        (ModuleCat.of A (A ⧸ P))))) :
    Module.Flat (Localization.AtPrime Q) (LocalizedModule.AtPrime Q M) := by
  classical
  let AQ := Localization.AtPrime Q
  let I' : Ideal AQ := P.map (algebraMap A AQ)
  -- (a) localized at `Q`
  have ha := flat_quot_tensor_localization M P Q f hfQ hflat
  -- (b) localized at `Q`: `Tor₁^A(M, A/P)_f = 0` says that every element of the kernel model
  -- `ker (M ⊗_A P → M)` is killed by a power of `f`, which lies outside `Q`
  obtain ⟨Φ, -, -, hΦsurj⟩ := exists_torOne_quotient_injective_onto_ker P M
  have hb : ∀ x : M ⊗[A] P, TensorProduct.rid A M (LinearMap.lTensor M P.subtype x) = 0 →
      ∃ s ∉ Q, s • x = 0 := by
    intro x hx
    obtain ⟨t, rfl⟩ := hΦsurj x hx
    obtain ⟨n, hn⟩ := exists_pow_smul_eq_zero_of_subsingleton_localizedModule_powers hTor t
    exact ⟨f ^ n, fun h => hfQ ((inferInstance : Q.IsPrime).mem_of_pow_mem n h),
      by rw [← map_smul, hn, map_zero]⟩
  have htor := (isZero_torOne_quotient_iff I' (AQ ⊗[A] M)).mpr
    (mul_injective_localization_of_forall_exists_smul_eq_zero Q M P hb)
  -- the corollary to Lemma 2 over `A_Q`, (ii) ⇒ (i)
  have hI : I' ≤ Ring.jacobson AQ := by
    rw [← Ideal.jacobson_bot, IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top,
      ← IsLocalization.AtPrime.map_eq_maximalIdeal Q AQ]
    exact Ideal.map_mono hPQ
  have _ : Module.Finite (AQ ⊗[A] B) (AQ ⊗[A] M) := baseChange_moduleFinite AQ
  have hcor := flat_tfae_of_graded AQ (AQ ⊗[A] B) (fun n => (𝒜 n).baseChange AQ)
    (baseChange_adjoin_eq_top AQ 𝒜 hgen) I' hI (AQ ⊗[A] M) (fun n => (ℳ n).baseChange AQ)
  have hflatQ : Module.Flat AQ (AQ ⊗[A] M) := (hcor.out 1 2).mpr (And.intro ha htor)
  exact Module.Flat.of_linearEquiv (LocalizedModule.isBaseChange Q.primeCompl M).equiv.symm

end Theorem1

/-- Theorem 1 (Krull–Seidenberg–Grothendieck), p. 188: "Let `A` be a noetherian ring, `B` a
graded `A`-algebra of finite type, and `M` a graded `B`-module of finite type. We assume that
`B` is generated by homogeneous elements of positive degrees as an `A`-algebra. Then the set of
those prime ideals `P` in `A` such that `M_P` is a flat `A_P`-module is an open subset of
`Spec(A)`."

Footnote 40: "This is a special case of a more general theorem of Grothendieck, [7], which says
that if `B` is an `A`-algebra of finite type (without gradation) and `M` is a `B`-module of
finite type, then the set of those points `x` of `Spec(B)` for which `M_x` is flat over the
local ring of `Spec(A)` at the point corresponding to `x` is an open subset of `Spec(B)`."
(The general theorem of footnote 40 is not formalized; it is not used.)

Proof, as printed (pp. 188–189): "Let `U` be the set of those prime ideals `P` in `A` such that `M_P` is a flat
`A_P`-module.  In order to prove that `U` is open in `Spec(A)`, it is necessary and sufficient
that (i) if `P ∈ U` and `F` is a prime ideal contained in `P`, then `F ∈ U`, and (ii) if
`P ∈ U`, then there exists a non-empty open subset of `Spec(A/P)` whose image in `Spec(A)` is
contained in `U`.  First of all, (i) is clear.  In fact, for each non-negative integer `n`, if
`(Mₙ)_P` is a free `A_P`-module, then `(Mₙ)_F` is a free `A_F`-module where `Mₙ` denotes the
homogeneous part of degree `n` of `M`.  Then (ii) follows Lemma 4 and corollary to Lemma 2."
* The criterion is `isOpen_of_generalization_of_exists_open` (gap filled, see below); a non-empty
  open subset of `Spec(A/P) = V(P)` contains the generic point `P`, so (ii) is stated as
  "`P` has an open neighbourhood `O` in `Spec A` with `O ∩ V(P) ⊆ U`".
* (i) is `flat_localization_of_le`.
* (ii): Lemma 4 (`exists_flat_localization_away_and_tor_eq_zero`) gives `f ∈ A − P` with (a) and
  (b); `O = D(f)`; at each prime `Q ⊇ P` with `f ∉ Q` the corollary to Lemma 2 over `A_Q` gives
  that `M_Q` is flat (`flat_localization_of_flat_quotient_of_tor_eq_zero`).

Gaps filled (the paper states these without argument): the "necessary and sufficient" openness
criterion (its sufficiency is proved here for noetherian quasi-sober spaces); that `M_P` is
flat if and only if all `(Mₙ)_P` are free, which (i) uses (`flat_tensor_iff_forall_flat_graded`,
Lemma 1 and the finiteness of the `Mₙ`); the passage from (a) and (b) at `f` to the hypotheses of
the corollary to Lemma 2 over `A_Q` (localization of `(M/PM)_f` at `Q`
(`flat_quot_tensor_localization`), compatibility of `Tor` with localization (on the kernel
model, `exists_torOne_quotient_injective_onto_ker` and
`mul_injective_localization_of_forall_exists_smul_eq_zero`), and the gradings on `B_Q` and `M_Q`
(`Hironaka/Compat/GradedBaseChange.lean`)). -/
@[blueprint "thm:II.1-1"
  (statement := /-- (Krull--Seidenberg--Grothendieck.) Let $A$ be a noetherian ring, $B$ a
    graded $A$-algebra of finite type, and $M$ a graded $B$-module of finite type. We assume
    that $B$ is generated by homogeneous elements of positive degrees as an $A$-algebra. Then
    the set of those prime ideals $P$ in $A$ such that $M_P$ is a flat $A_P$-module is an open
    subset of $\operatorname{Spec}(A)$. (p.~188.) -/)
  (proof := /-- Let $U$ be the set of those prime ideals $P$ in $A$ such that $M_P$ is a flat
    $A_P$-module. In order to prove that $U$ is open in $\operatorname{Spec}(A)$, it is
    necessary and sufficient that (i) if $P\in U$ and $F$ is a prime ideal contained in $P$,
    then $F\in U$, and (ii) if $P\in U$, then there exists a non-empty open subset of
    $\operatorname{Spec}(A/P)$ whose image in $\operatorname{Spec}(A)$ is contained in $U$.
    First of all, (i) is clear: for each $n\ge0$, if $(M_n)_P$ is a free $A_P$-module, then
    $(M_n)_F$ is a free $A_F$-module, where $M_n$ denotes the homogeneous part of degree $n$
    of $M$. Then (ii) follows from \cref{lem:II.1-4} and \cref{cor:II.1-lem2}. (This is the
    paper's proof, p.~189.)

    \textbf{Formalization.} The Lean proof follows the printed one. (i): $M_P$ is flat if and
    only if all $(M_n)_P$ are free ($M_P=\bigoplus(M_n)_P$, the $M_n$ are of finite type, and
    \cref{lem:II.1-1} over $A_P$); then $(M_n)_F=A_F\otimes_{A_P}(M_n)_P$ is free, so
    $M_F=\bigoplus(M_n)_F$ is flat. (ii): \cref{lem:II.1-4} gives $f\in A-P$ with
    (a) and (b); a non-empty open subset of $\operatorname{Spec}(A/P)=V(P)$ contains $P$, and
    the image of $D(\bar f)$ is $V(P)\cap D(f)$. For every prime $Q\supseteq P$ with $f\notin Q$,
    \cref{cor:II.1-lem2} is applied over the local ring $A_Q$ to $B_Q=A_Q\otimes_AB$,
    $M_Q=A_Q\otimes_AM$ and $I=PA_Q$ (contained in the Jacobson radical of $A_Q$): (a)
    localized at $Q$ says that $M_Q\otimes_{A_Q}A_Q/PA_Q$ is flat over $A_Q/PA_Q$, and (b)
    localized at $Q$ says that $\operatorname{Tor}_1^{A_Q}(M_Q,A_Q/PA_Q)=0$ (the kernel model
    $\ker(M\otimes_AP\to M)$ of \cref{compat:tor-one-quotient} commutes with localization), so
    $M_Q$ is flat over $A_Q$.

    \textbf{Gap in the paper filled.} The sufficiency of the openness criterion (i)+(ii),
    asserted in the paper, is proved for noetherian quasi-sober spaces; the localization of
    $(M/PM)_f$ and of $\operatorname{Tor}_1^A(M,A/P)_f$ at $Q$ and the gradings of $B_Q$ and
    $M_Q$, which the paper uses tacitly, are constructed. -/)
  (latexEnv := "theorem")]
theorem isOpen_flatLocus_of_graded (A : Type u) [CommRing A] [IsNoetherianRing A]
    (B : Type u) [CommRing B] [Algebra A B] (𝒜 : ℕ → Submodule A B) [GradedAlgebra 𝒜]
    [Algebra.FiniteType A B] (hgen : Algebra.adjoin A (⋃ n : ℕ, (𝒜 (n + 1) : Set B)) = ⊤)
    (M : Type u) [AddCommGroup M] [Module B M] [Module A M] [IsScalarTower A B M]
    [Module.Finite B M] (ℳ : ℕ → Submodule A M) [SetLike.GradedSMul 𝒜 ℳ]
    [DirectSum.Decomposition ℳ] :
    IsOpen {P : PrimeSpectrum A |
      Module.Flat (Localization.AtPrime P.asIdeal) (LocalizedModule.AtPrime P.asIdeal M)} := by
  classical
  -- `U` is open iff (i) it is stable under generization and (ii) each `P ∈ U` has a neighbourhood
  -- `O` with `O ∩ V(P) ⊆ U`
  apply isOpen_of_generalization_of_exists_open
  · -- (i): "First of all, (i) is clear."
    intro x y hxy hy
    have hle : x.asIdeal ≤ y.asIdeal := (PrimeSpectrum.le_iff_specializes x y).mpr hxy
    exact flat_localization_of_le B 𝒜 hgen M ℳ hle hy
  · -- (ii): "Then (ii) follows Lemma 4 and corollary to Lemma 2."
    intro x hx
    obtain ⟨f, hfx, hflat, hTor⟩ :=
      exists_flat_localization_away_and_tor_eq_zero A B 𝒜 hgen M ℳ x.asIdeal hx
    refine ⟨PrimeSpectrum.basicOpen f, (PrimeSpectrum.basicOpen f).isOpen, ?_, ?_⟩
    · exact (PrimeSpectrum.mem_basicOpen f x).mpr hfx
    · rintro Q ⟨hQf, hQx⟩
      have hPQ : x.asIdeal ≤ Q.asIdeal :=
        (PrimeSpectrum.le_iff_specializes x Q).mpr (specializes_iff_mem_closure.mpr hQx)
      exact flat_localization_of_flat_quotient_of_tor_eq_zero B 𝒜 hgen M ℳ x.asIdeal Q.asIdeal hPQ
        f hQf hflat hTor

end OpennessOfFlatness

namespace Subscheme

variable {X : Scheme.{u}} [IsAlgebraicScheme X]

open AssocGraded in
/-- `gr_I(A)` is a graded `A/I`-algebra, graded by its homogeneous parts. -/
private theorem nonempty_gradedAlgebra_assocGraded {A : Type u} [CommRing A] (I : Ideal A) :
    Nonempty (GradedAlgebra (homogeneous I)) := by
  classical
  have h1 : (1 : AssocGraded I) = mk I 0 1 (by simp) := by
    show Ideal.Quotient.mk _ 1 = Ideal.Quotient.mk _ _
    congr 1
  have gm : SetLike.GradedMonoid (homogeneous I) :=
    { one_mem := by rw [h1]; exact mk_mem_homogeneous I _
      mul_mem := by
        rintro i j x y ⟨u, rfl⟩ ⟨v, rfl⟩
        induction u using Submodule.Quotient.induction_on with
        | H a =>
          induction v using Submodule.Quotient.induction_on with
          | H b =>
            rw [ofGrPiece_mk, ofGrPiece_mk, mk_mul_mk]
            exact mk_mem_homogeneous I _ }
  let e : ∀ n, GrPiece I n ≃ₗ[A ⧸ I] homogeneous I n := fun n =>
    LinearEquiv.ofInjective _ (ofGrPiece_injective I n)
  let E : (DirectSum ℕ fun n => GrPiece I n) ≃ₗ[A ⧸ I] DirectSum ℕ fun n => homogeneous I n :=
    DFinsupp.mapRange.linearEquiv e
  let T : (DirectSum ℕ fun n => GrPiece I n) ≃ₗ[A ⧸ I] AssocGraded I :=
    LinearEquiv.ofBijective (toGr I) (toGr_bijective I)
  have key : DirectSum.coeLinearMap (homogeneous I) ∘ₗ E.toLinearMap = T.toLinearMap := by
    refine DirectSum.linearMap_ext _ fun n => LinearMap.ext fun u => ?_
    change DirectSum.coeLinearMap (homogeneous I) (DFinsupp.mapRange.linearEquiv e
      (DirectSum.lof (A ⧸ I) ℕ (fun n => GrPiece I n) n u)) =
      toGr I (DirectSum.lof (A ⧸ I) ℕ (fun n => GrPiece I n) n u)
    rw [toGr, DirectSum.toModule_lof, DFinsupp.mapRange.linearEquiv_apply]
    erw [DFinsupp.mapRange_single]
    exact (DirectSum.coeLinearMap_of (homogeneous I) n (e n u)).trans rfl
  let dec : DirectSum.Decomposition (homogeneous I) :=
    DirectSum.Decomposition.ofLinearMap _ (E.toLinearMap ∘ₗ T.symm.toLinearMap)
      (by rw [← LinearMap.comp_assoc, key]; ext x; simp)
      (by
        have : DirectSum.coeLinearMap (homogeneous I) = T.toLinearMap ∘ₗ E.symm.toLinearMap := by
          rw [← key]; ext x; simp
        rw [this]; ext x; simp)
  exact ⟨{ gm, dec with }⟩

open AssocGraded in
/-- `gr_I(A)` is generated over `A/I` by its homogeneous parts of positive degree. -/
private theorem adjoin_homogeneous_succ_eq_top {A : Type u} [CommRing A] (I : Ideal A) :
    Algebra.adjoin (A ⧸ I) (⋃ n : ℕ, (homogeneous I (n + 1) : Set (AssocGraded I))) = ⊤ := by
  rw [eq_top_iff]
  rintro x -
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [mk_eq_sum_mk]
  refine Subalgebra.sum_mem _ fun i _ => ?_
  rcases i with _ | k
  · have : mk I 0 ((p : Polynomial A).coeff 0) ((mem_reesAlgebra_iff I p).mp p.2 0) =
        algebraMap (A ⧸ I) (AssocGraded I) (Ideal.Quotient.mk I ((p : Polynomial A).coeff 0)) := by
      show Ideal.Quotient.mk _ _ = Ideal.Quotient.mk _ _
      congr 1
    rw [this]
    exact Subalgebra.algebraMap_mem _ _
  · exact Algebra.subset_adjoin (Set.mem_iUnion.mpr ⟨k, mk_mem_homogeneous I _⟩)

open AssocGraded in
/-- `gr_I(A)` is an `A/I`-algebra of finite type for noetherian `A`. -/
private theorem finiteType_assocGraded {A : Type u} [CommRing A] [IsNoetherianRing A]
    (I : Ideal A) :
    Algebra.FiniteType (A ⧸ I) (AssocGraded I) := by
  have : Algebra.FiniteType A (AssocGraded I) :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ A _) Ideal.Quotient.mk_surjective
  exact Algebra.FiniteType.of_restrictScalars_finiteType A (A ⧸ I) (AssocGraded I)

/-- For `p ⊇ I` with image `p̄` in `A/I`: `(grⁿ_I A)_{p̄}` is flat over `(A/I)_{p̄}` iff
`grⁿ_{IA_p}(A_p)` is flat over `A_p/IA_p`. -/
private theorem flat_localized_grPiece_iff {A : Type u} [CommRing A] (I p : Ideal A) [p.IsPrime]
    (pb : Ideal (A ⧸ I)) [pb.IsPrime] (hpb : pb.comap (Ideal.Quotient.mk I) = p) (n : ℕ) :
    Module.Flat (Localization.AtPrime pb) (LocalizedModule.AtPrime pb (GrPiece I n)) ↔
      Module.Flat (Localization.AtPrime p ⧸ I.map (algebraMap A (Localization.AtPrime p)))
        (GrPiece (I.map (algebraMap A (Localization.AtPrime p))) n) := by
  let Ap := Localization.AtPrime p
  let R' := Ap ⧸ I.map (algebraMap A Ap)
  let T := pb.primeCompl
  have hT : Algebra.algebraMapSubmonoid (A ⧸ I) p.primeCompl = T := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      show Ideal.Quotient.mk I y ∉ pb
      rw [← Ideal.mem_comap, hpb]
      exact hy
    · intro hx
      obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
      refine ⟨y, ?_, rfl⟩
      show y ∉ p
      rw [← hpb, Ideal.mem_comap]
      exact hx
  have hloc : IsLocalization T R' := by
    rw [← hT]
    infer_instance
  have hbc : IsLocalizedModule T (TensorProduct.mk (A ⧸ I) R' (GrPiece I n) 1) :=
    (isLocalizedModule_iff_isBaseChange T R' _).mpr
      (TensorProduct.isBaseChange (A ⧸ I) (GrPiece I n) R')
  let e₁ : LocalizedModule T (GrPiece I n) ≃ₗ[A ⧸ I] R' ⊗[A ⧸ I] GrPiece I n :=
    IsLocalizedModule.linearEquiv T (LocalizedModule.mkLinearMap T _)
      (TensorProduct.mk (A ⧸ I) R' (GrPiece I n) 1)
  obtain ⟨e₂⟩ := GrPiece.nonempty_baseChange_equiv (A' := Ap) I n
  rw [Module.flat_iff_of_isLocalization (Localization.AtPrime pb) T, Module.Flat.equiv_iff e₁,
    ← Module.flat_iff_of_isLocalization R' T, Module.Flat.equiv_iff e₂]

/-- The kernel condition passes to direct summands. -/
private theorem ker_cond_of_retract {A : Type u} [CommRing A] {M N : Type u} [AddCommGroup M]
    [Module A M] [AddCommGroup N] [Module A N] (ι : N →ₗ[A] M) (π : M →ₗ[A] N)
    (hπι : π ∘ₗ ι = LinearMap.id) (Q : Ideal A)
    (h : ∀ (J : Ideal A) (x : M ⊗[A] J),
      TensorProduct.rid A M (LinearMap.lTensor M J.subtype x) = 0 → ∃ s ∉ Q, s • x = 0)
    (J : Ideal A) (x : N ⊗[A] J)
    (hx : TensorProduct.rid A N (LinearMap.lTensor N J.subtype x) = 0) :
    ∃ s ∉ Q, s • x = 0 := by
  have hnat : ∀ w : N ⊗[A] J, TensorProduct.rid A M (LinearMap.lTensor M J.subtype
      (LinearMap.rTensor _ ι w)) = ι (TensorProduct.rid A N (LinearMap.lTensor N J.subtype w)) := by
    intro w
    induction w using TensorProduct.inductionOn with
    | tmul a p => simp
    | add w₁ w₂ h₁ h₂ => rw [map_add, map_add, map_add, h₁, h₂, map_add, map_add, map_add]
  obtain ⟨s, hs, hsx⟩ := h J _ (by rw [hnat, hx, map_zero])
  refine ⟨s, hs, ?_⟩
  have := congrArg (LinearMap.rTensor _ π) hsx
  rwa [map_smul, ← LinearMap.rTensor_comp_apply, hπι, LinearMap.rTensor_id,
    LinearMap.id_apply, map_zero] at this

/-- Step 1 of the corollary to Theorem 1 (affine case): the primes `p ⊇ I` at which `A_p` is
normally flat along `IA_p` are those of an open subset of `Spec A` (Theorem 1 applied to
`A/I` and `gr_I(A)`). -/
private theorem exists_isOpen_normallyFlat_primes {A : Type u} [CommRing A] [IsNoetherianRing A]
    (I : Ideal A) :
    ∃ O : Set (PrimeSpectrum A), IsOpen O ∧ ∀ p : PrimeSpectrum A, I ≤ p.asIdeal →
      (p ∈ O ↔ IsNormallyFlatAlongIdeal
        (I.map (algebraMap A (Localization.AtPrime p.asIdeal)))) := by
  classical
  obtain ⟨gr⟩ := nonempty_gradedAlgebra_assocGraded I
  let _ := gr
  have := finiteType_assocGraded I
  have hU := isOpen_flatLocus_of_graded (A ⧸ I) (AssocGraded I) (AssocGraded.homogeneous I)
    (adjoin_homogeneous_succ_eq_top I) (AssocGraded I) (AssocGraded.homogeneous I)
  obtain ⟨O, hO, hOU⟩ := (PrimeSpectrum.isClosedEmbedding_comap_of_surjective _ _
    (Ideal.Quotient.mk_surjective (I := I))).isInducing.isOpen_iff.mp hU
  refine ⟨O, hO, fun p hIp => ?_⟩
  have hker : RingHom.ker (Ideal.Quotient.mk I) ≤ p.asIdeal := by rwa [Ideal.mk_ker]
  let pb : PrimeSpectrum (A ⧸ I) := ⟨p.asIdeal.map (Ideal.Quotient.mk I),
    Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective hker⟩
  have hpb : pb.asIdeal.comap (Ideal.Quotient.mk I) = p.asIdeal := by
    show (p.asIdeal.map _).comap _ = _
    rw [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective, ← RingHom.ker_eq_comap_bot,
      sup_eq_left.mpr hker]
  have : pb.asIdeal.IsPrime := pb.isPrime
  have hc : PrimeSpectrum.comap (Ideal.Quotient.mk I) pb = p := PrimeSpectrum.ext hpb
  have hmem : p ∈ O ↔ pb ∈ {P : PrimeSpectrum (A ⧸ I) | Module.Flat (Localization.AtPrime
      P.asIdeal) (LocalizedModule.AtPrime P.asIdeal (AssocGraded I))} := by
    rw [← hOU, Set.mem_preimage, hc]
  rw [hmem, Set.mem_ofPred_eq, flat_localization_iff_ker, isNormallyFlatAlongIdeal_iff_flat]
  -- the homogeneous pieces
  let ι : ∀ n, AssocGraded.homogeneous I n →ₗ[A ⧸ I] AssocGraded I := fun n =>
    (AssocGraded.homogeneous I n).subtype
  let π : ∀ n, AssocGraded I →ₗ[A ⧸ I] AssocGraded.homogeneous I n := fun n =>
    DirectSum.component (A ⧸ I) ℕ (fun i => AssocGraded.homogeneous I i) n ∘ₗ
      (DirectSum.decomposeLinearEquiv (AssocGraded.homogeneous I)).toLinearMap
  have hπι : ∀ n, π n ∘ₗ ι n = LinearMap.id := fun n => by
    ext z
    simp only [π, ι, LinearMap.comp_apply, LinearEquiv.coe_coe,
      DirectSum.decomposeLinearEquiv_apply, Submodule.subtype_apply, DirectSum.decompose_coe,
      LinearMap.id_apply]
    exact congrArg Subtype.val (DirectSum.component.lof_self (R := A ⧸ I)
      (M := fun i => AssocGraded.homogeneous I i) n z)
  have hpiece : ∀ n, (∀ (J : Ideal (A ⧸ I)) (x : AssocGraded.homogeneous I n ⊗[A ⧸ I] J),
      TensorProduct.rid _ _ (LinearMap.lTensor _ J.subtype x) = 0 → ∃ s ∉ pb.asIdeal,
        s • x = 0) ↔ Module.Flat (Localization.AtPrime p.asIdeal ⧸
          I.map (algebraMap A (Localization.AtPrime p.asIdeal)))
          (GrPiece (I.map (algebraMap A (Localization.AtPrime p.asIdeal))) n) := by
    intro n
    obtain ⟨en⟩ := AssocGraded.homogeneous_equiv_grPiece I n
    rw [← flat_localized_grPiece_iff I p.asIdeal pb.asIdeal hpb n,
      flat_localization_iff_ker]
    constructor
    · exact ker_cond_of_retract en.toLinearMap en.symm.toLinearMap
        (LinearMap.ext fun z => en.symm_apply_apply z) _
    · exact ker_cond_of_retract en.symm.toLinearMap en.toLinearMap
        (LinearMap.ext fun z => en.apply_symm_apply z) _
  constructor
  · intro h n
    exact (hpiece n).mp (ker_cond_of_retract (ι n) (π n) (hπι n) _ h)
  · intro h
    exact ker_cond_of_pieces (AssocGraded.homogeneous I) pb.asIdeal fun n => (hpiece n).mpr (h n)

/-- A ring isomorphism `A ≅ B` carrying `I` to `J` identifies `grⁿ_I(A)` with `grⁿ_J(B)`,
semilinearly over `A/I ≅ B/J`. -/
private theorem exists_grPiece_addEquiv {A B : Type u} [CommRing A] [CommRing B]
    (e : A ≃+* B) (I : Ideal A) (J : Ideal B) (hIJ : I.map (e : A →+* B) = J) (n : ℕ) :
    ∃ j : GrPiece I n ≃+ GrPiece J n, ∀ (r : A ⧸ I) (m : GrPiece I n),
      j (r • m) = Ideal.quotientEquiv I J e hIJ.symm r • j m := by
  have := RingHomInvPair.of_ringEquiv e
  have := RingHomInvPair.symm (e : A →+* B) (e.symm : B →+* A)
  let f₀ : A ≃ₛₗ[(e : A →+* B)] B := e.toSemilinearEquiv
  have hpow : ∀ k, J ^ k = (I ^ k).comap (e.symm : B →+* A) := by
    intro k
    rw [← hIJ, ← Ideal.map_pow, Ideal.map_comap_of_equiv]
    rfl
  have hmap : ∀ k, Submodule.map (f₀ : A →ₛₗ[(e : A →+* B)] B) (I ^ k) = J ^ k := by
    intro k
    ext x
    rw [Submodule.mem_map, hpow k, Ideal.mem_comap]
    constructor
    · rintro ⟨y, hy, rfl⟩
      simpa [f₀] using hy
    · intro hx
      exact ⟨e.symm x, hx, by simp [f₀]⟩
  let g₀ : ↥(I ^ n) ≃ₛₗ[(e : A →+* B)] ↥(J ^ n) :=
    (f₀.submoduleMap (I ^ n)).trans (LinearEquiv.ofEq _ _ (hmap n))
  have hq : (Submodule.comap (I ^ n).subtype (I ^ (n + 1))).map
      (g₀ : ↥(I ^ n) →ₛₗ[(e : A →+* B)] ↥(J ^ n)) =
      Submodule.comap (J ^ n).subtype (J ^ (n + 1)) := by
    rw [Submodule.map_equiv_eq_comap_symm]
    ext ⟨x, hx⟩
    show ((g₀.symm ⟨x, hx⟩ : ↥(I ^ n)) : A) ∈ I ^ (n + 1) ↔ x ∈ J ^ (n + 1)
    rw [hpow (n + 1), Ideal.mem_comap]
    rfl
  let j : GrPiece I n ≃ₛₗ[(e : A →+* B)] GrPiece J n := Submodule.Quotient.equiv _ _ g₀ hq
  refine ⟨j.toAddEquiv, fun r m => ?_⟩
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective r
  have h1 : (Ideal.Quotient.mk I a) • m = a • m := algebraMap_smul (A ⧸ I) a m
  have h2 : Ideal.quotientEquiv I J e hIJ.symm (Ideal.Quotient.mk I a) =
      Ideal.Quotient.mk J (e a) := rfl
  have h3 : (Ideal.Quotient.mk J (e a)) • j m = e a • j m := algebraMap_smul (B ⧸ J) (e a) (j m)
  rw [h1, h2]
  change j (a • m) = Ideal.Quotient.mk J (e a) • j m
  rw [h3]
  exact j.map_smulₛₗ a m

/-- Freeness is transported along a semilinear additive isomorphism. -/
private theorem free_of_equiv_equiv {K L M N : Type u} [CommRing K] [CommRing L]
    [AddCommGroup M] [AddCommGroup N] [Module K M] [Module L N] (i : K ≃+* L) (j : M ≃+ N)
    (hc : ∀ (r : K) (m : M), j (r • m) = i r • j m) [Module.Free K M] : Module.Free L N := by
  let : Module K N := Module.compHom N (i : K →+* L)
  let j' : M ≃ₗ[K] N := { j with map_smul' := hc }
  exact Module.Free.of_basis (((Module.Free.chooseBasis K M).map j').mapCoeffs i fun _ _ => rfl)

/-- Normal flatness is invariant under ring isomorphisms. -/
private theorem isNormallyFlatAlongIdeal_of_ringEquiv {A B : Type u} [CommRing A] [CommRing B]
    (e : A ≃+* B) (I : Ideal A) (J : Ideal B) (hIJ : I.map (e : A →+* B) = J)
    (h : IsNormallyFlatAlongIdeal I) : IsNormallyFlatAlongIdeal J := fun n => by
  obtain ⟨j, hj⟩ := exists_grPiece_addEquiv e I J hIJ n
  have := h n
  exact free_of_equiv_equiv _ j hj

/-- On an affine open `V ∋ y`, the stalk `D_y` is generated by the germs of `D(V)`. -/
private theorem stalkIdeal_eq_map_germ' {Y : Scheme.{u}} (D : Subscheme Y) (V : Y.affineOpens)
    {y : Y} (hy : y ∈ (V : Y.Opens)) :
    D.stalkIdeal y = (D.ideal V).map (Y.presheaf.germ (V : Y.Opens) y hy).hom := by
  apply le_antisymm
  · refine Ideal.span_le.mpr ?_
    rintro _ ⟨U, hyU, s, hs, rfl⟩
    obtain ⟨_, ⟨U', hU', rfl⟩, hyU', hU'le⟩ :=
      Y.isBasis_affineOpens.exists_subset_of_mem_open (show y ∈ (U : Y.Opens) ⊓ V from ⟨hyU, hy⟩)
        ((U : Y.Opens) ⊓ V).isOpen
    let U'' : Y.affineOpens := ⟨U', hU'⟩
    have h1 : U'' ≤ U := fun z hz => (hU'le hz).1
    have h2 : U'' ≤ V := fun z hz => (hU'le hz).2
    have hs' : Y.presheaf.map (CategoryTheory.homOfLE h1).op s ∈ (D.ideal V).map (Y.presheaf.map
        (CategoryTheory.homOfLE h2).op).hom := by
      rw [D.map_ideal h2]
      exact D.ideal_le_comap_ideal h1 hs
    have hle : (D.ideal V).map (Y.presheaf.map (CategoryTheory.homOfLE h2).op).hom ≤
        ((D.ideal V).map (Y.presheaf.germ (V : Y.Opens) y hy).hom).comap
          (Y.presheaf.germ (U'' : Y.Opens) y hyU').hom := by
      rw [Ideal.map_le_iff_le_comap]
      intro t ht
      have e : (Y.presheaf.germ (U'' : Y.Opens) y hyU').hom
          ((Y.presheaf.map (CategoryTheory.homOfLE h2).op).hom t) =
          (Y.presheaf.germ (V : Y.Opens) y hy).hom t := Y.presheaf.germ_res_apply _ _ _ _
      rw [Ideal.mem_comap, Ideal.mem_comap, e]
      exact Ideal.mem_map_of_mem _ ht
    have e : (Y.presheaf.germ (U'' : Y.Opens) y hyU').hom
        ((Y.presheaf.map (CategoryTheory.homOfLE h1).op).hom s) =
        (Y.presheaf.germ (U : Y.Opens) y hyU).hom s := Y.presheaf.germ_res_apply _ _ _ _
    show (Y.presheaf.germ (U : Y.Opens) y hyU).hom s ∈ _
    rw [← e]
    exact hle hs'
  · rw [Ideal.map_le_iff_le_comap]
    intro s hs
    exact Ideal.subset_span ⟨V, hy, s, hs, rfl⟩

/-- The normally flat locus of a subscheme `D` of an algebraic scheme is the trace on `D` of an
open subset of `X` (Theorem 1 of Ch. II §1 on affine charts). -/
theorem exists_isOpen_isNormallyFlatAlongAt (D : Subscheme X) :
    ∃ U₀ : Set X, IsOpen U₀ ∧ ∀ x ∈ D.pts, (x ∈ U₀ ↔ D.IsNormallyFlatAlongAt x) := by
  classical
  have := IsAlgebraicScheme.isNoetherian X
  have hVa : ∀ V : X.affineOpens, IsAffineOpen (V : X.Opens) := fun V => V.2
  choose O hO hOp using fun V : X.affineOpens =>
    have := IsLocallyNoetherian.component_noetherian V
    exists_isOpen_normallyFlat_primes (D.ideal V)
  refine ⟨⋃ V : X.affineOpens, (hVa V).fromSpec '' O V,
    isOpen_iUnion fun V => (hVa V).fromSpec.isOpenEmbedding.isOpenMap _ (hO V), ?_⟩
  -- the local comparison at `x = fromSpec p`
  have key : ∀ (V : X.affineOpens) (p : PrimeSpectrum Γ(X, V)),
      (hVa V).fromSpec p ∈ D.pts → D.ideal V ≤ p.asIdeal ∧
        (IsNormallyFlatAlongIdeal (D.stalkIdeal ((hVa V).fromSpec p)) ↔
          IsNormallyFlatAlongIdeal ((D.ideal V).map
            (algebraMap Γ(X, V) (Localization.AtPrime p.asIdeal)))) := by
    intro V p hp
    have hpV : (hVa V).fromSpec p ∈ (V : X.Opens) := by
      rw [← SetLike.mem_coe, ← (hVa V).range_fromSpec]
      exact ⟨p, rfl⟩
    refine ⟨?_, ?_⟩
    · have h1 : (hVa V).fromSpec '' PrimeSpectrum.zeroLocus (D.ideal V : Set Γ(X, V)) =
          (D.support : Set X) ∩ V := by
        rw [(hVa V).fromSpec_image_zeroLocus, D.coe_support_inter V]
      have : (hVa V).fromSpec p ∈ (D.support : Set X) ∩ V := ⟨hp, hpV⟩
      rw [← h1] at this
      obtain ⟨p', hp', he⟩ := this
      rw [← (hVa V).fromSpec.isOpenEmbedding.injective he]
      exact hp'
    · let _ : Algebra Γ(X, V) (X.presheaf.stalk ((hVa V).fromSpec p)) :=
        TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨(hVa V).fromSpec p, hpV⟩
      have hloc : IsLocalization.AtPrime (X.presheaf.stalk ((hVa V).fromSpec p)) p.asIdeal :=
        (hVa V).isLocalization_stalk' p hpV
      let e := IsLocalization.algEquiv p.asIdeal.primeCompl
        (Localization.AtPrime p.asIdeal) (X.presheaf.stalk ((hVa V).fromSpec p))
      have hmap : ((D.ideal V).map (algebraMap Γ(X, V) (Localization.AtPrime p.asIdeal))).map
          (e.toRingEquiv : Localization.AtPrime p.asIdeal →+* _) =
          D.stalkIdeal ((hVa V).fromSpec p) := by
        rw [Ideal.map_map, stalkIdeal_eq_map_germ' D V hpV]
        congr 1
        exact RingHom.ext fun a => e.commutes a
      constructor
      · intro h
        refine isNormallyFlatAlongIdeal_of_ringEquiv e.toRingEquiv.symm _ _ ?_ h
        rw [← hmap, Ideal.map_map]
        convert Ideal.map_id _
        exact RingHom.ext fun a => e.toRingEquiv.symm_apply_apply a
      · exact fun h => isNormallyFlatAlongIdeal_of_ringEquiv e.toRingEquiv _ _ hmap h
  intro x hx
  constructor
  · intro hxU
    obtain ⟨V, p, hpO, rfl⟩ := Set.mem_iUnion.mp hxU
    obtain ⟨hIp, hiff⟩ := key V p hx
    exact ⟨hx, hiff.mpr ((hOp V p hIp).mp hpO)⟩
  · rintro ⟨-, hnf⟩
    obtain ⟨_, ⟨V, hV, rfl⟩, hxV, -⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
    have hxr : x ∈ Set.range (hVa ⟨V, hV⟩).fromSpec := by
      rw [(hVa ⟨V, hV⟩).range_fromSpec]; exact hxV
    obtain ⟨p, rfl⟩ := hxr
    obtain ⟨hIp, hiff⟩ := key ⟨V, hV⟩ p hx
    exact Set.mem_iUnion.mpr ⟨⟨V, hV⟩, p, (hOp ⟨V, hV⟩ p hIp).mpr (hiff.mp hnf), rfl⟩

/-- Corollary to Theorem 1, p. 189: "Let `V` be an algebraic scheme and `W` a reduced subscheme
of `V`. Then there exists an open dense subset `U` of `W` such that `x ∈ U` if and only if `V`
is normally flat along `W` at `x`."

"Open dense subset of `W`" is encoded as a subset `U` of the points of `W` which is open in
`W` (the trace `U₀ ∩ W` of an open `U₀` of `V`) and whose closure contains `W`.

Deviation from the paper (gap filled): the reduction to the affine case ("of local nature"),
the comparison of flatness of `gr_I(A)_p` over `(A/I)_p` with normal flatness at `p` (via the
p. 181 isomorphism `gr_I(A)_P ≅ gr_{IA_P}(A_P)`, proved by flat base change of `gr`), and the
density ("It is easy to see that `U` contains all the generic points of `W`": at the generic
point of an irreducible component of the reduced `W` the ideal of `W` is the maximal ideal, so
the graded pieces are vector spaces) are proved.

The Remark on p. 189 (the openness of the set of simple points of `W` at which `V` is normally
flat along `W`) is `isOpen_setOf_isSimpleAt_and_isNormallyFlatAlongAt`. -/
@[blueprint "cor:II.1-thm1"
  (statement := /-- Let $V$ be an algebraic scheme and $W$ a reduced subscheme of $V$. Then
    there exists an open dense subset $U$ of $W$ such that $x\in U$ if and only if $V$ is
    normally flat along $W$ at $x$ (\cref{def:0.1-normally-flat-at}). (p.~189.) -/)
  (proof := /-- The assertion is of local nature. Hence we may assume that $V$ is an affine
    scheme, say $V=\operatorname{Spec}(A)$ with a noetherian ring $A$. Let $I$ be the ideal of
    $W$ in $A$. Let $\bar A=A/I$ and $B=\operatorname{gr}_I(A)$. Applying \cref{thm:II.1-1}
    to these $\bar A$ and $B$ ($M=B$), we obtain an open subset $U$ of $W$ which has the
    property that $x\in U$ if and only if $V$ is normally flat along $W$ at $x$. It is easy to
    see that $U$ is dense in $W$, i.e., that $U$ contains all the generic points of $W$. (This
    is the paper's proof, p.~189.) (Formalization note (encoding): ``open dense subset of $W$''
    is the trace on $W$ of an open subset of $V$ whose closure contains $W$.)

    \textbf{Gap in the paper filled.} Lean glues the affine pieces, proves the p.~181
    isomorphism $\operatorname{gr}_I(A)_{\mathfrak p}\cong\operatorname{gr}_{IA_{\mathfrak p}}
    (A_{\mathfrak p})$ (flat base change) to translate the flat locus of Theorem 1 into normal
    flatness, and proves the density: at the generic point of an irreducible component of the
    reduced $W$ the ideal of $W$ is the maximal ideal, so the graded pieces are free. -/)
  (latexEnv := "corollary")]
theorem exists_isOpen_dense_isNormallyFlatAlong (W : Subscheme X) (hW : W.IsReduced) :
    ∃ U : Set X, (∃ U₀ : Set X, IsOpen U₀ ∧ U = U₀ ∩ W.pts) ∧ W.pts ⊆ closure U ∧
      ∀ x ∈ W.pts, (x ∈ U ↔ W.IsNormallyFlatAlongAt x) := by
  -- Theorem 1 on affine charts: the normally flat locus is open in `W`
  obtain ⟨U₀, hU₀, hiff⟩ := exists_isOpen_isNormallyFlatAlongAt W
  refine ⟨U₀ ∩ W.pts, ⟨U₀, hU₀, rfl⟩, ?_, fun x hx =>
    ⟨fun h => (hiff x hx).mp h.1, fun h => ⟨(hiff x hx).mpr h, hx⟩⟩⟩
  -- it is dense: it contains the generic points of the irreducible components of `W`
  intro x hx
  have hx' : x ∈ Set.range W.ι := by
    rw [Scheme.IdealSheafData.range_subschemeι]
    exact hx
  obtain ⟨y, rfl⟩ := hx'
  have := IsAlgebraicScheme.isNoetherian X
  have := isAlgebraicScheme_toScheme W
  have := IsAlgebraicScheme.isNoetherian W.toScheme
  obtain ⟨η, hη⟩ := QuasiSober.sober (isIrreducible_irreducibleComponent (x := y))
    isClosed_irreducibleComponent
  have hηc : closure {η} ∈ _root_.irreducibleComponents W.toScheme := by
    rw [hη.def]
    exact irreducibleComponent_mem_irreducibleComponents y
  have hηW : W.ι η ∈ W.pts := by
    show W.ι η ∈ (W.support : Set X)
    rw [← Scheme.IdealSheafData.range_subschemeι]
    exact ⟨η, rfl⟩
  have hnf : W.IsNormallyFlatAlongAt (W.ι η) := by
    refine ⟨hηW, ?_⟩
    rw [stalkIdeal_eq_maximalIdeal_of_isReduced W hW η hηc]
    intro n
    let _ : Field (X.presheaf.stalk (W.ι η) ⧸
        IsLocalRing.maximalIdeal (X.presheaf.stalk (W.ι η))) := Ideal.Quotient.field _
    exact Module.Free.of_divisionRing _ _
  have hsp : W.ι η ⤳ W.ι y := by
    have : η ⤳ y := by
      rw [specializes_iff_mem_closure, hη.def]
      exact mem_irreducibleComponent
    exact this.map W.ι.continuous
  have hmem : W.ι η ∈ U₀ ∩ W.pts := ⟨(hiff _ hηW).mpr hnf, hηW⟩
  exact closure_mono (Set.singleton_subset_iff.mpr hmem) (specializes_iff_mem_closure.mp hsp)

/-- Remark, p. 189: "In the later applications of the corollary, we shall be interested only in
the subset of `W` of those simple points of `W` at which `V` is normally flat along `W`.  The
openness of this subset of `W` is all that will be needed later.  This openness can also be proved
by means of the generalized theorem of Krull–Seidenberg, Hironaka [8]."

Here `V = X`, `W` is a reduced subscheme as in the Corollary, and the subset is encoded as the set
of points `y` of the scheme `W` at which `W` is simple (`W.toScheme.IsSimpleAt y`) and `V` is
normally flat along `W` at `W.ι y`; it is open in `W`.  Proof: it is the intersection of the open
set `U` of the Corollary (`exists_isOpen_dense_isNormallyFlatAlong`) with the set of simple points
of `W`, which is open by `isOpen_setOf_isSimpleAt` (the cited (iii) of p. 161).  The alternative
proof by the generalized Krull–Seidenberg theorem [8], the paper's own second proof, is not
formalized. -/
@[blueprint "rem:II.1-thm1-simple-locus"
  (statement := /-- Let $V$ be an algebraic scheme and $W$ a reduced subscheme of $V$. The subset
    of $W$ of those simple points of $W$ at which $V$ is normally flat along $W$ is open in $W$.
    (Remark, p.~189: ``In the later applications of the corollary, we shall be interested only in
    the subset of $W$ of those simple points of $W$ at which $V$ is normally flat along $W$. The
    openness of this subset of $W$ is all that will be needed later.'') -/)
  (proof := /-- By \cref{cor:II.1-thm1} the set of points of $W$ at which $V$ is normally flat
    along $W$ is open in $W$ (it is the open subset $U$ of the corollary), and the set of simple
    points of $W$ is open by (iii) of p.~161 (a cited leaf); the set in question is the
    intersection of the two. (The paper adds that the openness can also be proved by means of the
    generalized theorem of Krull--Seidenberg [8]; that second proof is not formalized.) -/)
  (latexEnv := "remark")]
theorem isOpen_setOf_isSimpleAt_and_isNormallyFlatAlongAt [Hironaka.Cited.IsHironakaBaseIsClosedSingularLocus.{u}] (W : Subscheme X) (hW : W.IsReduced) :
    IsOpen {y : W.toScheme | W.toScheme.IsSimpleAt y ∧ W.IsNormallyFlatAlongAt (W.ι y)} := by
  obtain ⟨U, ⟨U₀, hU₀, rfl⟩, -, hU⟩ := exists_isOpen_dense_isNormallyFlatAlong W hW
  have := isAlgebraicScheme_toScheme W
  have h1 : IsOpen (W.ι ⁻¹' U₀) := hU₀.preimage W.ι.continuous
  convert (isOpen_setOf_isSimpleAt W.toScheme).inter h1 using 1
  ext y
  have hy : W.ι y ∈ W.pts := by
    show W.ι y ∈ (W.support : Set X)
    rw [← Scheme.IdealSheafData.range_subschemeι]
    exact ⟨y, rfl⟩
  have := hU (W.ι y) hy
  simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_preimage, this.symm, hy, and_true]

end Subscheme

/-! ### Public forms of helpers used in Ch. III §3 (Theorem 2 and its corollaries)

These restate private lemmas of this file under distinct public names (the private names also
occur, as private copies, in other files). -/

/-- The primes `p ⊇ I` at which `A_p` is normally flat along `IA_p` are those of an open subset
of `Spec A` (Theorem 1 applied to `A/I` and `gr_I(A)`; public form of
`Subscheme.exists_isOpen_normallyFlat_primes`). -/
theorem exists_isOpen_primes_isNormallyFlatAlongIdeal {A : Type u} [CommRing A]
    [IsNoetherianRing A] (I : Ideal A) :
    ∃ O : Set (PrimeSpectrum A), IsOpen O ∧ ∀ p : PrimeSpectrum A, I ≤ p.asIdeal →
      (p ∈ O ↔ IsNormallyFlatAlongIdeal
        (I.map (algebraMap A (Localization.AtPrime p.asIdeal)))) :=
  Subscheme.exists_isOpen_normallyFlat_primes I

/-- Normal flatness is invariant under ring isomorphisms (public form of
`Subscheme.isNormallyFlatAlongIdeal_of_ringEquiv`). -/
theorem isNormallyFlatAlongIdeal_transport {A B : Type u} [CommRing A] [CommRing B]
    (e : A ≃+* B) (I : Ideal A) (J : Ideal B) (hIJ : I.map (e : A →+* B) = J)
    (h : IsNormallyFlatAlongIdeal I) : IsNormallyFlatAlongIdeal J :=
  Subscheme.isNormallyFlatAlongIdeal_of_ringEquiv e I J hIJ h

end Hironaka

