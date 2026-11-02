/-
Copyright (c) 2026 Daattavya Aggarwal, Minhyong Kim, Oisin Kim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daattavya Aggarwal, Minhyong Kim, Oisin Kim
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.CategoryTheory.Monoidal.Tor
public import Mathlib.Data.Fin.Tuple.Sort
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.Coalgebra.IsFrobenius
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.HopfAlgebra.Basic
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Architect
public import Hironaka.Ch3.Basic
public import Hironaka.Compat.RegularGraded
public import Hironaka.Compat.MapsRSOPOrder
public import Hironaka.Ch2.Flatness
public import Hironaka.Ch2.GradedIdeal
public import Hironaka.Ch0.AlgebraicScheme

/-!
# Ch. III §1: The numerical characters ν*(J) and ν(J) of a local ideal J, and a standard
base of J (pp. 205–209)

> Let R be a regular local ring and J an ideal in R. Let M be the maximal ideal of R. We have
> defined the homogeneous ideal gr_M(J, R) in the graded R/M-algebra gr_M(R).  (p. 205)

Definitions 1–3 of this section (`nuI` = ν^{(i)}(J), `nuStar` = ν*(J), `IsStandardBase`) and
the notion of a local homomorphism which "transforms a regular system of parameters of R into
such a system of parameters of R'" (`RingHom.MapsRSOP`) live in `Hironaka/Ch3/Basic.lean`.
This file contains the rest of §1 in the paper's order:

* Lemma 1 (p. 205): ν^{(i)}(J) = deg φ_i for a system (φ₁, …, φ_m) with the properties
  (i)–(iii), and ν^{(i)}(J) = ∞ for i > m;
* p. 206: the canonical homomorphism of graded algebras `gr_I(A) → gr_{I'}(A')` induced by a
  ring homomorphism `α : A → A'`, `I' = IA'` (`AssocGraded.map`);
* Lemma 2 (p. 206) and its Corollary (p. 207): invariance of ν* under flat / regular-parameter
  preserving local homomorphisms;
* Lemma 3 (p. 207) and its Corollary (p. 208): ν* is strictly decreasing in the ideal, and a
  standard base generates the ideal;
* the Remark of pp. 208–209 (ν^{(1)}(J) = ν(J), the description of ν^{(2)}(J), the characters
  ν_{(i)}(J) = `nuParen`, and the example of p. 209);
* Definition 4 (p. 209): ν*(V/X) for a subscheme V of a non-singular scheme X
  (`Subscheme.nuStarAt`).

Conventions.  `gr_M(R)` is `AssocGraded (maximalIdeal R)`, `gr^μ_M(R)` is
`AssocGraded.homogeneous _ μ` and `gr_M(J, R)` is `grIdeal (maximalIdeal R) J`
(`Hironaka/Compat/Graded.lean`).  Sequences ν* are elements of `Lex (ℕ+ → ℕ∞)` with the
lexicographic order of Definition 2.  For `α : A → A'` and an ideal `J` of `A`, "`J' = JA'`" is
`J.map α`.  "`A'` is flat over `A`" is `Module.Flat A A'` for `[Algebra A A']`.
-/

@[expose] public section

open IsLocalRing

namespace Hironaka

universe u v

/-! ### Lemma 1 (pp. 205–206) -/

section Lemma1

variable (R : Type u) [CommRing R] [IsRegularLocalRing R] (J : Ideal R)

/-- `[a Xᵐ] · [b Xⁿ] = [ab Xᵐ⁺ⁿ]` in `gr_I(A)`. -/
private theorem mk_mul_mk_eq_mk_add {A : Type*} [CommRing A] (I : Ideal A) {m n : ℕ} {a b : A}
    (ha : a ∈ I ^ m) (hb : b ∈ I ^ n) :
    AssocGraded.mk I m a ha * AssocGraded.mk I n b hb =
      AssocGraded.mk I (m + n) (a * b) (by rw [pow_add]; exact Ideal.mul_mem_mul ha hb) := by
  refine (map_mul (Ideal.Quotient.mk (Ideal.map (algebraMap A (reesAlgebra I)) I)) _ _).symm.trans
    (congrArg _ (Subtype.ext ?_))
  exact Polynomial.monomial_mul_monomial m n a b

/-- The class of `a X⁰` is the image of `a mod I` under `A/I → gr_I(A)`. -/
private theorem mk_zero_eq_algebraMap_mk {A : Type*} [CommRing A] (I : Ideal A) (a : A)
    (ha : a ∈ I ^ 0) :
    AssocGraded.mk I 0 a ha = algebraMap (A ⧸ I) (AssocGraded I) (Ideal.Quotient.mk I a) := by
  show Ideal.Quotient.mk _ _ = Ideal.Quotient.mk _ (algebraMap A (reesAlgebra I) a)
  refine congrArg _ (Subtype.ext ?_)
  show Polynomial.monomial 0 a = Polynomial.C a
  rfl

/-- Every element of `grⁿ_I(A)` is the class `[y Xⁿ]` of some `y ∈ Iⁿ`. -/
private theorem exists_mk_eq_of_mem_homogeneous {A : Type*} [CommRing A] (I : Ideal A)
    {n : ℕ} {x : AssocGraded I} (hx : x ∈ AssocGraded.homogeneous I n) :
    ∃ y : A, ∃ hy : y ∈ I ^ n, AssocGraded.mk I n y hy = x := by
  obtain ⟨q, rfl⟩ := LinearMap.mem_range.mp hx
  induction q using Submodule.Quotient.induction_on with
  | H y => exact ⟨y, y.2, rfl⟩

/-- `grᵃ_I(A) · grᵇ_I(A) ⊆ grᵃ⁺ᵇ_I(A)`. -/
private theorem mul_mem_homogeneous_add {A : Type*} [CommRing A] (I : Ideal A) {a b : ℕ}
    {x y : AssocGraded I} (hx : x ∈ AssocGraded.homogeneous I a)
    (hy : y ∈ AssocGraded.homogeneous I b) : x * y ∈ AssocGraded.homogeneous I (a + b) := by
  obtain ⟨x, hx, rfl⟩ := exists_mk_eq_of_mem_homogeneous I hx
  obtain ⟨y, hy, rfl⟩ := exists_mk_eq_of_mem_homogeneous I hy
  rw [mk_mul_mk_eq_mk_add]
  exact AssocGraded.mk_mem_homogeneous I _

/-- `gr⁰_I(A)` is the image of `A/I`. -/
private theorem exists_algebraMap_eq_of_mem_homogeneous_zero {A : Type*} [CommRing A]
    (I : Ideal A) {x : AssocGraded I} (hx : x ∈ AssocGraded.homogeneous I 0) :
    ∃ k : A ⧸ I, algebraMap (A ⧸ I) _ k = x := by
  obtain ⟨y, hy, rfl⟩ := exists_mk_eq_of_mem_homogeneous I hx
  exact ⟨_, (mk_zero_eq_algebraMap_mk I y hy).symm⟩

/-- The degree-`n` component of a homogeneous element of degree `n` is itself. -/
private theorem ofGrPiece_grProj_of_mem_homogeneous {A : Type*} [CommRing A] (I : Ideal A) {n : ℕ}
    {x : AssocGraded I} (hx : x ∈ AssocGraded.homogeneous I n) :
    AssocGraded.ofGrPiece I n (grProj I n x) = x := by
  obtain ⟨y, rfl⟩ := LinearMap.mem_range.mp hx
  rw [grProj_ofGrPiece_same]

/-- The degree-`n` component of a homogeneous element of degree `m ≠ n` vanishes. -/
private theorem ofGrPiece_grProj_eq_zero_of_mem_homogeneous_of_ne {A : Type*} [CommRing A] (I : Ideal A) {m n : ℕ}
    (h : m ≠ n) {x : AssocGraded I} (hx : x ∈ AssocGraded.homogeneous I m) :
    AssocGraded.ofGrPiece I n (grProj I n x) = 0 := by
  obtain ⟨y, rfl⟩ := LinearMap.mem_range.mp hx
  rw [grProj_ofGrPiece_ne I h, map_zero]

/-- The degree-`n` component lies in degree `n`. -/
private theorem ofGrPiece_grProj_mem_homogeneous {A : Type*} [CommRing A] (I : Ideal A) (n : ℕ) (x : AssocGraded I) :
    AssocGraded.ofGrPiece I n (grProj I n x) ∈ AssocGraded.homogeneous I n :=
  LinearMap.mem_range_self _ _

/-- `ofGrPiece_grProj_mul` for `c = [a Xⁱ]`. -/
private theorem ofGrPiece_grProj_mk_mul {A : Type*} [CommRing A] (I : Ideal A) {e μ i : ℕ}
    {s : AssocGraded I} (hs : s ∈ AssocGraded.homogeneous I e) (a : A) (ha : a ∈ I ^ i) :
    AssocGraded.ofGrPiece I μ (grProj I μ (AssocGraded.mk I i a ha * s)) =
      if e ≤ μ then
        AssocGraded.ofGrPiece I (μ - e) (grProj I (μ - e) (AssocGraded.mk I i a ha)) * s
      else 0 := by
  have hmul : AssocGraded.mk I i a ha * s ∈ AssocGraded.homogeneous I (i + e) :=
    mul_mem_homogeneous_add I (AssocGraded.mk_mem_homogeneous I ha) hs
  by_cases hie : i + e = μ
  · have heμ : e ≤ μ := by omega
    rw [ite_eq_left heμ, ofGrPiece_grProj_of_mem_homogeneous I (hie ▸ hmul),
      ofGrPiece_grProj_of_mem_homogeneous I (show AssocGraded.mk I i a ha ∈ AssocGraded.homogeneous I (μ - e) from
        (show i = μ - e by omega) ▸ AssocGraded.mk_mem_homogeneous I ha)]
  · rw [ofGrPiece_grProj_eq_zero_of_mem_homogeneous_of_ne I hie hmul]
    split_ifs with heμ
    · rw [ofGrPiece_grProj_eq_zero_of_mem_homogeneous_of_ne I (show i ≠ μ - e by omega) (AssocGraded.mk_mem_homogeneous I ha),
        zero_mul]
    · rfl

/-- The degree-`μ` component of `c · s`, for `s` homogeneous of degree `e`, is `c_{μ-e} · s`
(and `0` if `e > μ`). -/
private theorem ofGrPiece_grProj_mul {A : Type*} [CommRing A] (I : Ideal A) {e μ : ℕ}
    {s : AssocGraded I} (hs : s ∈ AssocGraded.homogeneous I e) (c : AssocGraded I) :
    AssocGraded.ofGrPiece I μ (grProj I μ (c * s)) =
      if e ≤ μ then AssocGraded.ofGrPiece I (μ - e) (grProj I (μ - e) c) * s else 0 := by
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective c
  rw [mk_eq_sum_mk, Finset.sum_mul, map_sum, map_sum]
  split_ifs with h
  · rw [map_sum, map_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [ofGrPiece_grProj_mk_mul I hs, ite_eq_left h]
  · refine Finset.sum_eq_zero fun i _ => ?_
    rw [ofGrPiece_grProj_mk_mul I hs, ite_eq_right h]

/-- Graded ideal membership: a homogeneous element of degree `μ` of the ideal generated by
homogeneous elements `f t` of degrees `e t` lies in the ideal generated by the `f t` with
`e t < μ` plus the `A/I`-span of the `f t` with `e t = μ`. -/
private theorem mem_sup_of_mem_span_homogeneous {A : Type*} [CommRing A] (I : Ideal A) {n : ℕ}
    (f : Fin n → AssocGraded I) (e : Fin n → ℕ)
    (hf : ∀ t, f t ∈ AssocGraded.homogeneous I (e t)) {μ : ℕ} {χ : AssocGraded I}
    (hχ : χ ∈ AssocGraded.homogeneous I μ) (hχs : χ ∈ Ideal.span (Set.range f)) :
    χ ∈ (Ideal.span (Set.range fun t : {t // e t < μ} => f t)).restrictScalars (A ⧸ I) ⊔
      Submodule.span (A ⧸ I) (Set.range fun t : {t // e t = μ} => f t) := by
  obtain ⟨c, rfl⟩ := Ideal.mem_span_range_iff_exists_fun.mp hχs
  rw [← ofGrPiece_grProj_of_mem_homogeneous I hχ, map_sum, map_sum]
  refine Submodule.sum_mem _ fun t _ => ?_
  rw [ofGrPiece_grProj_mul I (hf t)]
  split_ifs with h
  · rcases h.lt_or_eq with hlt | heq
    · exact Submodule.mem_sup_left (Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨⟨t, hlt⟩, rfl⟩))
    · refine Submodule.mem_sup_right ?_
      have h0 : μ - e t = 0 := by omega
      generalize hx : AssocGraded.ofGrPiece I (μ - e t) (grProj I (μ - e t) (c t)) = x
      have hmem : x ∈ AssocGraded.homogeneous I (μ - e t) := hx ▸ ofGrPiece_grProj_mem_homogeneous I _ _
      rw [h0] at hmem
      obtain ⟨k, rfl⟩ := exists_algebraMap_eq_of_mem_homogeneous_zero I hmem
      rw [← Algebra.smul_def]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨t, heq⟩, rfl⟩)
  · exact zero_mem _

/-- A homogeneous element of degree `μ` of the ideal generated by homogeneous elements `f t`
(degrees `e t`) lies in the ideal generated by the `f t` with `e t ≤ μ`. -/
private theorem mem_span_le_of_mem_span_homogeneous {A : Type*} [CommRing A] (I : Ideal A) {n : ℕ}
    (f : Fin n → AssocGraded I) (e : Fin n → ℕ)
    (hf : ∀ t, f t ∈ AssocGraded.homogeneous I (e t)) {μ : ℕ} {χ : AssocGraded I}
    (hχ : χ ∈ AssocGraded.homogeneous I μ) (hχs : χ ∈ Ideal.span (Set.range f)) :
    χ ∈ Ideal.span (Set.range fun t : {t // e t ≤ μ} => f t) := by
  have h := mem_sup_of_mem_span_homogeneous I f e hf hχ hχs
  refine (sup_le ?_ ?_ : _ ≤ (Ideal.span (Set.range fun t : {t // e t ≤ μ} =>
    f t)).restrictScalars (A ⧸ I)) h
  · intro x hx
    refine (Ideal.span_mono ?_) hx
    rintro _ ⟨t, rfl⟩
    exact ⟨⟨t, t.2.le⟩, rfl⟩
  · refine Submodule.span_le.mpr ?_
    rintro _ ⟨t, rfl⟩
    exact Ideal.subset_span ⟨⟨t, t.2.le⟩, rfl⟩

/-- Lemma 1, p. 206: the last step of the printed proof, "some non-zero linear combination of
`φ_s, φ_{s+1}, …, φ_k` with coefficients in `R/M` must be in the ideal `(φ₁, …, φ_{s-1}) gr_M(R)`.
Hence, there exists `j` (`s ≤ j ≤ k`) such that `φ_j ∈ (φ₁, …, φ_{j-1}) gr_M(R)`.  This
contradicts (iii)", in the contrapositive form: for a system `φ` with non-decreasing degrees `d`
and `φ_i ∉ (φ₁, …, φ_{i-1})`, the classes of the `φ_j` of degree `μ` (those with `s ≤ j ≤ k`
when `μ = ν_i`) are `K`-linearly independent modulo the ideal generated by the `φ_j` of degree
`< μ` (those with `j < s`).  The proof takes the largest `j` with a non-zero coefficient in a
relation, so that all other terms lie in `(φ₁, …, φ_{j-1})`. -/
private theorem linearIndependent_mkQ_of_irredundant {m : ℕ} (φ : Fin m → AssocGraded (maximalIdeal R))
    (d : Fin m → ℕ) (h₂ : Monotone d)
    (h₃ : ∀ i : Fin m, φ i ∉ Ideal.span (Set.range fun j : Fin i => φ (Fin.castLE i.2.le j)))
    (μ : ℕ) :
    LinearIndependent (R ⧸ maximalIdeal R) (fun j : {j // d j = μ} =>
      ((Ideal.span (Set.range fun k : {k // d k < μ} => φ k)).restrictScalars
        (R ⧸ maximalIdeal R)).mkQ (φ j)) := by
  classical
  let _ : Field (R ⧸ maximalIdeal R) := Ideal.Quotient.field _
  rw [linearIndependent_iff']
  intro s g hg j hj
  by_contra hgj
  have hne : (s.filter fun i => g i ≠ 0).Nonempty := ⟨j, Finset.mem_filter.mpr ⟨hj, hgj⟩⟩
  set j₀ := (s.filter fun i => g i ≠ 0).max' hne with hj₀def
  obtain ⟨hj₀s, hgj₀⟩ := Finset.mem_filter.mp ((s.filter fun i => g i ≠ 0).max'_mem hne)
  have hmax : ∀ i ∈ s, g i ≠ 0 → i ≤ j₀ := fun i hi hgi =>
    (s.filter fun i => g i ≠ 0).le_max' i (Finset.mem_filter.mpr ⟨hi, hgi⟩)
  -- the ideal generated by the `φ k`, `k < j₀`
  set P : Ideal (AssocGraded (maximalIdeal R)) :=
    Ideal.span (Set.range fun k : Fin j₀.1 => φ (Fin.castLE j₀.1.2.le k)) with hP
  have hmemP : ∀ k : Fin m, k < j₀.1 → φ k ∈ P := fun k hk =>
    Ideal.subset_span ⟨⟨k, hk⟩, rfl⟩
  have hsum : ∑ i ∈ s, g i • φ i.1 ∈ (Ideal.span (Set.range fun k : {k // d k < μ} =>
      φ k)).restrictScalars (R ⧸ maximalIdeal R) := by
    have h0 : ((Ideal.span (Set.range fun k : {k // d k < μ} => φ k)).restrictScalars
        (R ⧸ maximalIdeal R)).mkQ (∑ i ∈ s, g i • φ i.1) = 0 := by
      rw [map_sum]
      simpa only [map_smul] using hg
    rwa [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at h0
  have hUP : Ideal.span (Set.range fun k : {k // d k < μ} => φ k) ≤ P := by
    refine Ideal.span_le.mpr ?_
    rintro _ ⟨k, rfl⟩
    refine hmemP k ?_
    by_contra hk
    have := h₂ (not_lt.mp hk)
    have h1 := k.2
    have h2 := j₀.2
    omega
  have hrest : ∑ i ∈ s.erase j₀, g i • φ i.1 ∈ P.restrictScalars (R ⧸ maximalIdeal R) := by
    refine Submodule.sum_mem _ fun i hi => ?_
    obtain ⟨hij, his⟩ := Finset.mem_erase.mp hi
    by_cases hgi : g i = 0
    · rw [hgi, zero_smul]
      exact zero_mem _
    · refine Submodule.smul_mem _ _ (hmemP i.1 ?_)
      exact lt_of_le_of_ne (hmax i his hgi) (fun h => hij (Subtype.ext h))
  have hj₀P : g j₀ • φ j₀.1 ∈ P.restrictScalars (R ⧸ maximalIdeal R) := by
    have := sub_mem (hUP hsum) hrest
    rwa [← Finset.add_sum_erase s _ hj₀s, add_sub_cancel_right] at this
  apply h₃ j₀.1
  have := Submodule.smul_mem (P.restrictScalars (R ⧸ maximalIdeal R)) (g j₀)⁻¹ hj₀P
  rwa [smul_smul, inv_mul_cancel₀ hgj₀, one_smul] at this

/-- Lemma 1, p. 206: "Let `{ψ_t}` be those which have `deg ψ_t = ν_i`. Then for each `j` with
`s ≤ j ≤ k`, there exists a linear combination `L_j` of those `ψ_t` with coefficients in `R/M`
such that `φ_j - L_j` is contained in the ideal in `gr_M(R)` generated by those `ψ_n` with
`deg ψ_n < ν_i`. Hence by the above equality for `μ < ν_i = ν_k`, `φ_j - L_j` is contained in
`(φ₁, …, φ_{s-1}) gr_M(R)`."  Here `U` is the ideal generated by the `φ_j` of degree `< μ`
(`(φ₁, …, φ_{s-1})` for `μ = ν_i`).  The classes modulo `U` of the elements `χ` of degree `μ` of
the ideal generated by homogeneous elements `ψ t` (degrees `e t`) lie in the `K`-span of the
classes of the `ψ t` of degree `μ`, provided the `ψ t` of degree `< μ` lie in `U`.  (The printed
text states the existence of `L_j` without proof; it is the splitting of a homogeneous element of
`(ψ) gr_M(R)` of degree `μ` into the part with coefficients of positive degree, which lies in the
ideal of the `ψ_t` of degree `< μ`, and the part with coefficients in `gr⁰_M(R) = R/M`, i.e.
`mem_sup_of_mem_span_homogeneous`.) -/
private theorem mkQ_mem_span_of_lt {m k : ℕ} (φ : Fin m → AssocGraded (maximalIdeal R))
    (d : Fin m → ℕ) (ψ : Fin k → AssocGraded (maximalIdeal R)) (e : Fin k → ℕ)
    (he : ∀ t, ψ t ∈ AssocGraded.homogeneous (maximalIdeal R) (e t)) (μ : ℕ)
    (H2 : ∀ t, e t < μ → ψ t ∈ Ideal.span (Set.range fun j : {j // d j < μ} => φ j))
    {χ : AssocGraded (maximalIdeal R)} (hχ : χ ∈ AssocGraded.homogeneous (maximalIdeal R) μ)
    (hχs : χ ∈ Ideal.span (Set.range ψ)) :
    ((Ideal.span (Set.range fun j : {j // d j < μ} => φ j)).restrictScalars
        (R ⧸ maximalIdeal R)).mkQ χ ∈ Submodule.span (R ⧸ maximalIdeal R)
      (Set.range fun t : {t // e t = μ} => ((Ideal.span (Set.range fun j : {j // d j < μ} =>
        φ j)).restrictScalars (R ⧸ maximalIdeal R)).mkQ (ψ t)) := by
  set U := (Ideal.span (Set.range fun j : {j // d j < μ} => φ j)).restrictScalars
    (R ⧸ maximalIdeal R) with hU
  have h := mem_sup_of_mem_span_homogeneous (maximalIdeal R) ψ e he hχ hχs
  have hle : (Ideal.span (Set.range fun t : {t // e t < μ} => ψ t)).restrictScalars
      (R ⧸ maximalIdeal R) ≤ U := by
    intro x hx
    refine (Ideal.span_le.mpr ?_) hx
    rintro _ ⟨t, rfl⟩
    exact H2 t t.2
  obtain ⟨u, hu, y, hy, rfl⟩ := Submodule.mem_sup.mp (sup_le_sup_right hle _ h)
  rw [map_add, show U.mkQ u = 0 from (Submodule.Quotient.mk_eq_zero U).mpr hu, zero_add]
  have hr : (Set.range fun t : {t // e t = μ} => U.mkQ (ψ t)) =
      U.mkQ '' Set.range fun t : {t // e t = μ} => ψ t := by
    rw [← Set.range_comp]
    rfl
  rw [hr, ← Submodule.map_span]
  exact Submodule.mem_map_of_mem hy

/-- Lemma 1, p. 206: "Since we have `deg ψ_j ≤ ν_j` for all `j`, the number of elements in `{ψ_t}`
is less than `k - s + 1`.  Therefore, some non-zero linear combination of `φ_s, φ_{s+1}, …, φ_k`
with coefficients in `R/M` must be in the ideal `(φ₁, …, φ_{s-1}) gr_M(R)`. Hence, there exists
`j` (`s ≤ j ≤ k`) such that `φ_j ∈ (φ₁, …, φ_{j-1}) gr_M(R)`.  This contradicts (iii)."  This is
the comparison of the number `k - s + 1` of the `φ_j` of degree `μ` (`μ = ν_i`) with the number
of the `ψ_t` of degree `μ`: if `φ` has non-decreasing degrees `d` and
`φ_i ∉ (φ₁, …, φ_{i-1})`, and `ψ` is a system of homogeneous elements (degrees `e`) such that
the `φ_j` of degree `μ` lie in `(ψ) gr_M(R)` and the `ψ_t` of degree `< μ` lie in the ideal
generated by the `φ_j` of degree `< μ`, then there are at least as many `ψ_t` of degree `μ` as
there are `φ_j` of degree `μ`.  The `L_j` of the printed proof are `mkQ_mem_span_of_lt`; the
`R/M`-linear algebra (`k - s + 1` vectors `L_j` in a space spanned by fewer vectors, hence a
non-trivial relation, hence a `j` contradicting (iii)) is `linearIndependent_mkQ_of_irredundant`
together with `linearIndependent_le_span_aux'`. -/
private theorem card_filter_le_le {m k : ℕ} (φ : Fin m → AssocGraded (maximalIdeal R))
    (d : Fin m → ℕ) (hd : ∀ j, φ j ∈ AssocGraded.homogeneous (maximalIdeal R) (d j))
    (h₂ : Monotone d)
    (h₃ : ∀ i : Fin m, φ i ∉ Ideal.span (Set.range fun j : Fin i => φ (Fin.castLE i.2.le j)))
    (ψ : Fin k → AssocGraded (maximalIdeal R)) (e : Fin k → ℕ)
    (he : ∀ t, ψ t ∈ AssocGraded.homogeneous (maximalIdeal R) (e t)) (μ : ℕ)
    (H1 : ∀ j, d j = μ → φ j ∈ Ideal.span (Set.range ψ))
    (H2 : ∀ t, e t < μ → ψ t ∈ Ideal.span (Set.range fun j : {j // d j < μ} => φ j)) :
    (Finset.univ.filter fun j => d j = μ).card ≤ (Finset.univ.filter fun t => e t = μ).card := by
  classical
  have hli := linearIndependent_mkQ_of_irredundant R φ d h₂ h₃ μ
  have hsub := fun j : {j // d j = μ} => mkQ_mem_span_of_lt R φ d ψ e he μ H2
    (show φ j ∈ AssocGraded.homogeneous (maximalIdeal R) μ by have := hd j.1; rwa [j.2] at this)
    (H1 j j.2)
  have h := linearIndependent_le_span_aux' _ hli _ (by rintro _ ⟨j, rfl⟩; exact hsub j)
  rw [Fintype.card_subtype] at h
  refine h.trans ((Fintype.card_range_le _).trans ?_)
  rw [Fintype.card_subtype]

/-- Definition 1 (p. 205): a system `(φ₁, …, φ_n)` of homogeneous elements of `gr_M(J, R)` with
`(φ₁, …, φ_n) gr_M(R) ∩ gr^μ_M(R) = gr^μ_M(J, R)` for all `μ < ν` shows `ν ≤ ν^{(n+1)}(J)`
("`ν^{(i)}(J)` is the maximal integer `ν` ... such that there exists a system ... `(φ₁, …, φ_{i-1})`
..."). -/
private theorem le_nuI_of_isNuSystem {ν n : ℕ} {φ : Fin n → AssocGraded (maximalIdeal R)}
    (h : IsNuSystem R J ν n φ) : (ν : ℕ∞) ≤ nuI R J ⟨n + 1, Nat.succ_pos n⟩ :=
  le_iSup₂ (f := fun (ν : ℕ) (_ : ∃ φ : Fin (((⟨n + 1, Nat.succ_pos n⟩ : ℕ+) : ℕ) - 1) →
    AssocGraded (maximalIdeal R), IsNuSystem R J ν (((⟨n + 1, Nat.succ_pos n⟩ : ℕ+) : ℕ) - 1) φ) =>
    (ν : ℕ∞)) ν ⟨φ, h⟩

/-- Definition 1 (p. 205), the other direction: if `a < ν^{(n+1)}(J)`, then ("by Definition 1")
there is a system `(ψ₁, …, ψ_n)` of homogeneous elements of `gr_M(J, R)` with the property
`(ψ₁, …, ψ_n) gr_M(R) ∩ gr^μ_M(R) = gr^μ_M(J, R)` for all `μ < ν`, for some `ν > a`.  (If
`ν^{(n+1)}(J)` is finite one can take `ν = ν^{(n+1)}(J)`; if it is `∞` the definition provides such
a system for every finite `ν`, not obviously one system for all `μ`.) -/
private theorem exists_isNuSystem_of_lt_nuI {a n : ℕ}
    (h : (a : ℕ∞) < nuI R J ⟨n + 1, Nat.succ_pos n⟩) :
    ∃ ν : ℕ, a < ν ∧ ∃ φ : Fin n → AssocGraded (maximalIdeal R), IsNuSystem R J ν n φ := by
  unfold nuI at h
  obtain ⟨ν, hν⟩ := lt_iSup_iff.mp h
  obtain ⟨⟨φ, hφ⟩, hlt⟩ := lt_iSup_iff.mp hν
  exact ⟨ν, Nat.cast_lt.mp hlt, φ, hφ⟩

/-- Lemma 1, p. 205, "In view of (i) and (ii), it is clear from Definition 1 that `ν_i ≤ μ_i`":
for a system `φ` with (i) and homogeneous elements of degrees `d`, the first `n` members
`(φ₁, …, φ_n)` satisfy `(φ₁, …, φ_n) gr_M(R) ∩ gr^μ_M(R) = gr^μ_M(J, R)` for all `μ < ν`,
as soon as `ν ≤ deg φ_j` for all `j > n`: a homogeneous element of `gr_M(J, R)` of degree `μ`
lies in `(φ₁, …, φ_m) gr_M(R)` by (i), hence in the ideal generated by the `φ_j` of degree
`≤ μ < ν`, all of which come among `φ₁, …, φ_n`.  (Used for `n = i` (here `ν = ν_i` by (ii))
and for `n = k` (here `ν = ν_k + 1`) in the proof of Lemma 1.) -/
private theorem isNuSystem_prefix {m : ℕ} (φ : Fin m → AssocGraded (maximalIdeal R))
    (hJ : ∀ j, φ j ∈ grIdeal (maximalIdeal R) J) (d : Fin m → ℕ)
    (hd : ∀ j, φ j ∈ AssocGraded.homogeneous (maximalIdeal R) (d j))
    (h₁ : grIdeal (maximalIdeal R) J = Ideal.span (Set.range φ)) {n : ℕ} (hn : n ≤ m) {ν : ℕ}
    (hν : ∀ j : Fin m, n ≤ (j : ℕ) → ν ≤ d j) :
    IsNuSystem R J ν n (fun j : Fin n => φ (Fin.castLE hn j)) := by
  refine ⟨fun j => ⟨hJ _, d _, hd _⟩, fun μ hμ χ hχ => ⟨fun h => ?_, fun h => ?_⟩⟩
  · refine (Ideal.span_le.mpr ?_) h
    rintro _ ⟨j, rfl⟩
    exact hJ _
  · rw [h₁] at h
    refine (Ideal.span_mono ?_) (mem_span_le_of_mem_span_homogeneous _ φ d hd hχ h)
    rintro _ ⟨j, rfl⟩
    have hjn : (j.1 : ℕ) < n := by
      by_contra hc
      have h1 := hν j.1 (not_lt.mp hc)
      have h2 := j.2
      omega
    exact ⟨⟨j.1, hjn⟩, rfl⟩

/-- Lemma 1, p. 206: "Let `k` be the largest integer such that `ν_i = ν_k`. We have `k ≥ i`", and
"Let `s` be the smallest positive integer such that `ν_s = ν_i` (`= ν_k`). Then `s ≤ i`."  For a
non-decreasing sequence `d` (property (ii)), with `0`-based indices: the indices `j < s` are
those with `ν_j < ν_i`, and the indices `j > k` are those with `ν_j > ν_i`. -/
private theorem exists_first_last {m : ℕ} (d : Fin m → ℕ) (hd : Monotone d) (i : Fin m) :
    ∃ s k : Fin m, s ≤ i ∧ i ≤ k ∧ (∀ j, j < s ↔ d j < d i) ∧ (∀ j, k < j ↔ d i < d j) := by
  classical
  set F : Finset (Fin m) := Finset.univ.filter fun j => d j = d i with hF
  have hmem : ∀ j, j ∈ F ↔ d j = d i := fun j => by simp [hF]
  have hne : F.Nonempty := ⟨i, (hmem i).mpr rfl⟩
  have hs := (hmem _).mp (F.min'_mem hne)
  have hk := (hmem _).mp (F.max'_mem hne)
  refine ⟨F.min' hne, F.max' hne, F.min'_le i ((hmem i).mpr rfl),
    F.le_max' i ((hmem i).mpr rfl), fun j => ?_, fun j => ?_⟩
  · constructor
    · intro hj
      have h1 := hd hj.le
      refine lt_of_le_of_ne (by omega) fun h => ?_
      exact absurd (F.min'_le j ((hmem j).mpr h)) (not_le.mpr hj)
    · intro hj
      by_contra hc
      have h1 := hd (not_lt.mp hc)
      omega
  · constructor
    · intro hj
      have h1 := hd hj.le
      refine lt_of_le_of_ne (by omega) fun h => ?_
      exact absurd (F.le_max' j ((hmem j).mpr h.symm)) (not_le.mpr hj)
    · intro hj
      by_contra hc
      have h1 := hd (not_lt.mp hc)
      omega

/-- Lemma 1, p. 205: "We may assume that `deg ψ₁ ≤ ⋯ ≤ deg ψ_{i-1}`."  A system of homogeneous
elements with the property of Definition 1 up to `ν` can be reordered (by a permutation sorting
the degrees) so that the degrees `e t` (any chosen degrees `ψ t ∈ gr^{e t}_M(R)`) are
non-decreasing; the ideal `(ψ₁, …, ψ_n) gr_M(R)` does not change. -/
private theorem exists_sorted_isNuSystem {ν k : ℕ} {ψ : Fin k → AssocGraded (maximalIdeal R)}
    (hψ : IsNuSystem R J ν k ψ) :
    ∃ (ψ' : Fin k → AssocGraded (maximalIdeal R)) (e : Fin k → ℕ),
      IsNuSystem R J ν k ψ' ∧ (∀ t, ψ' t ∈ AssocGraded.homogeneous (maximalIdeal R) (e t)) ∧
        Monotone e := by
  choose e he using fun t => (hψ.1 t).2
  refine ⟨ψ ∘ Tuple.sort e, e ∘ Tuple.sort e, ⟨fun t => hψ.1 _, fun μ hμ χ hχ => ?_⟩,
    fun t => he _, Tuple.monotone_sort e⟩
  rw [(Tuple.sort e).surjective.range_comp]
  exact hψ.2 μ hμ χ hχ

/-- Lemma 1, p. 205: "Then, for every `j < i`, we have
`(ψ₁, …, ψ_{j-1}) gr_M(R) ∩ gr^μ_M(R) = gr^μ_M(J, R)` for all `μ < deg ψ_j`."  For `ψ` with
non-decreasing degrees `e` and the property of Definition 1 up to `ν`, the printed claim holds
for `μ < min (deg ψ_j) ν` (the paper's `μ < deg ψ_j` tacitly stays below the bound `ν ≤ μ_i` up
to which `ψ` was chosen).  A homogeneous element of degree `μ` of `(ψ₁, …, ψ_i) gr_M(R)` lies in
the ideal generated by the `ψ_t` of degree `≤ μ < deg ψ_j`, which come before `ψ_j`. -/
private theorem isNuSystem_castLE_of_monotone {ν k : ℕ} {ψ : Fin k → AssocGraded (maximalIdeal R)}
    {e : Fin k → ℕ} (he : ∀ t, ψ t ∈ AssocGraded.homogeneous (maximalIdeal R) (e t))
    (hmono : Monotone e) (hψ : IsNuSystem R J ν k ψ) (j : Fin k) :
    IsNuSystem R J (min (e j) ν) j (fun t : Fin j => ψ (Fin.castLE j.2.le t)) := by
  refine ⟨fun t => ⟨(hψ.1 _).1, e _, he _⟩, fun μ hμ χ hχ => ⟨fun h => ?_, fun h => ?_⟩⟩
  · refine (Ideal.span_le.mpr ?_) h
    rintro _ ⟨t, rfl⟩
    exact (hψ.1 _).1
  · have hμ' := lt_min_iff.mp hμ
    have h' : χ ∈ Ideal.span (Set.range ψ) := (hψ.2 μ hμ'.2 χ hχ).mpr h
    refine (Ideal.span_mono ?_) (mem_span_le_of_mem_span_homogeneous _ ψ e he hχ h')
    rintro _ ⟨t, rfl⟩
    have htj : (t.1 : ℕ) < j := by
      by_contra hc
      have h1 := hmono (show j ≤ t.1 from not_lt.mp hc)
      have h2 := t.2
      omega
    exact ⟨⟨t.1, htj⟩, rfl⟩

/-- Lemma 1, p. 205–206, the minimal counterexample: if `ν^{(j)}(J) = ν_j` for all `j < i`, then
`ν^{(i)}(J) ≤ ν_i`.  This is the printed proof from "Suppose we have `i` ... such that
`μ_i > ν_i`.  Let `i` be the smallest integer with this property" (the minimality of `i` is the
hypothesis `ih`) to "This contradicts (iii)"; the comments mark the printed steps.  Indices are
`0`-based: the paper's `ψ_j`, `φ_j`, `ν_j` are `ψ (j-1)`, `φ (j-1)`, `d (j-1)`, the paper's index
`i ∈ {1, …, m}` is `(i : ℕ) + 1`, and `(φ₁, …, φ_{j-1})` is the `j`-th prefix. -/
private theorem nuI_le_of_lemma1_properties {m : ℕ} (φ : Fin m → AssocGraded (maximalIdeal R))
    (hJ : ∀ j, φ j ∈ grIdeal (maximalIdeal R) J) (d : Fin m → ℕ)
    (hd : ∀ j, φ j ∈ AssocGraded.homogeneous (maximalIdeal R) (d j))
    (h₁ : grIdeal (maximalIdeal R) J = Ideal.span (Set.range φ)) (h₂ : Monotone d)
    (h₃ : ∀ i : Fin m, φ i ∉ Ideal.span (Set.range fun j : Fin i => φ (Fin.castLE i.2.le j)))
    (i : Fin m)
    (ih : ∀ j : Fin m, j < i → nuI R J ⟨(j : ℕ) + 1, Nat.succ_pos _⟩ = d j) :
    nuI R J ⟨(i : ℕ) + 1, Nat.succ_pos _⟩ ≤ d i := by
  classical
  by_contra hlt
  rw [not_le] at hlt
  -- "By Definition 1, we have homogeneous elements `ψ₁, …, ψ_{i-1}` such that
  -- `(ψ₁, …, ψ_{i-1}) gr_M(R) ∩ gr^μ_M(R) = gr^μ_M(J, R)` for all `μ < μ_i`": here for all
  -- `μ < ν`, where `ν_i < ν ≤ μ_i`
  obtain ⟨ν, hν, ψ₀, hψ₀⟩ := exists_isNuSystem_of_lt_nuI R J hlt
  -- "We may assume that `deg ψ₁ ≤ ⋯ ≤ deg ψ_{i-1}`."
  obtain ⟨ψ, e, hψ, he, hmono⟩ := exists_sorted_isNuSystem R J hψ₀
  -- "Then, for every `j < i`, we have `(ψ₁, …, ψ_{j-1}) gr_M(R) ∩ gr^μ_M(R) = gr^μ_M(J, R)` for
  -- all `μ < deg ψ_j`. Hence, by Definition 1, we have `deg ψ_j ≤ μ_j = ν_j`.
  -- Thus `deg ψ_j ≤ ν_j` for all `j < i`."
  have hdeg : ∀ j : Fin i, e j ≤ d ⟨j, lt_trans j.2 i.2⟩ := by
    intro j
    have hji : (⟨j, lt_trans j.2 i.2⟩ : Fin m) < i := j.2
    have h1 := (le_nuI_of_isNuSystem R J (isNuSystem_castLE_of_monotone R J he hmono hψ j)).trans
      (ih _ hji).le
    have h2 : d ⟨j, lt_trans j.2 i.2⟩ ≤ d i := h₂ hji.le
    have h3 := Nat.cast_le.mp h1
    omega
  -- "Let `k` be the largest integer such that `ν_i = ν_k`. We have `k ≥ i`", "Let `s` be the
  -- smallest positive integer such that `ν_s = ν_i` (`= ν_k`). Then `s ≤ i`."
  obtain ⟨s, k, hsi, hik, hs, hk⟩ := exists_first_last d h₂ i
  have hkm : (k : ℕ) + 1 ≤ m := k.2
  -- "`(φ₁, …, φ_k) gr_M(R) ∩ gr^μ_M(R) = gr^μ_M(J, R)` for all `μ ≤ ν_i = ν_k`"
  have hφk := isNuSystem_prefix R J φ hJ d hd h₁ hkm (ν := d i + 1) fun j hj =>
    Nat.succ_le_of_lt ((hk j).mp hj)
  -- "Hence we have `(ψ₁, …, ψ_{i-1}) gr_M(R) ∩ gr^μ_M(R) = (φ₁, …, φ_k) gr_M(R) ∩ gr^μ_M(R)`
  -- for all `μ ≤ ν_k`."
  have h4 : ∀ μ ≤ d i, ∀ χ ∈ AssocGraded.homogeneous (maximalIdeal R) μ,
      (χ ∈ Ideal.span (Set.range ψ) ↔
        χ ∈ Ideal.span (Set.range fun j : Fin (k + 1) => φ (Fin.castLE hkm j))) :=
    fun μ hμ χ hχ => (hψ.2 μ (by omega) χ hχ).trans (hφk.2 μ (by omega) χ hχ).symm
  -- "Let `{ψ_t}` be those which have `deg ψ_t = ν_i`. Then for each `j` with `s ≤ j ≤ k`, there
  -- exists a linear combination `L_j` of those `ψ_t` with coefficients in `R/M` such that
  -- `φ_j - L_j` is contained in the ideal in `gr_M(R)` generated by those `ψ_n` with
  -- `deg ψ_n < ν_i`": `φ_j ∈ (ψ) gr_M(R)` is `H1`; the decomposition is made in `card_filter_le_le`
  have H1 : ∀ j, d j = d i → φ j ∈ Ideal.span (Set.range ψ) := fun j hj =>
    (hψ.2 (d i) hν (φ j) (by rw [← hj]; exact hd j)).mpr (hJ j)
  -- "Hence by the above equality for `μ < ν_i = ν_k`, `φ_j - L_j` is contained in
  -- `(φ₁, …, φ_{s-1}) gr_M(R)`": each `ψ_n` with `deg ψ_n < ν_i` lies in the ideal generated
  -- by the `φ_j` of degree `< ν_i`, i.e. (by `hs`) by `φ₁, …, φ_{s-1}`
  have H2 : ∀ t : Fin i, e t < d i →
      ψ t ∈ Ideal.span (Set.range fun j : {j // d j < d i} => φ j) := by
    intro t ht
    have h1 : ψ t ∈ Ideal.span (Set.range fun j : Fin (k + 1) => φ (Fin.castLE hkm j)) :=
      (h4 (e t) ht.le (ψ t) (he t)).mp (Ideal.subset_span ⟨t, rfl⟩)
    have h2 := mem_span_le_of_mem_span_homogeneous (maximalIdeal R)
      (fun j : Fin (k + 1) => φ (Fin.castLE hkm j)) (fun j => d (Fin.castLE hkm j))
      (fun j => hd _) (he t) h1
    refine (Ideal.span_mono ?_) h2
    rintro _ ⟨j, rfl⟩
    exact ⟨⟨Fin.castLE hkm j.1, lt_of_le_of_lt j.2 ht⟩, rfl⟩
  -- "Since we have `deg ψ_j ≤ ν_j` for all `j`, the number of elements in `{ψ_t}` is less than
  -- `k - s + 1`": the `ψ_t` of degree `ν_i` have `ν_t ≥ ν_i`, i.e. `s ≤ t < i`
  have hcardψ : (Finset.univ.filter fun t : Fin i => e t = d i).card ≤ i - s := by
    have hsub : (Finset.univ.filter fun t : Fin i => e t = d i).map Fin.valEmbedding ⊆
        Finset.Ico (s : ℕ) i := by
      intro x hx
      simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
        Fin.valEmbedding_apply] at hx
      obtain ⟨t, ht, rfl⟩ := hx
      rw [Finset.mem_Ico]
      refine ⟨?_, t.2⟩
      by_contra hc
      have hts : (⟨t, lt_trans t.2 i.2⟩ : Fin m) < s := not_le.mp hc
      have h1 := (hs _).mp hts
      have h2 := hdeg t
      omega
    have := Finset.card_le_card hsub
    rwa [Finset.card_map, Nat.card_Ico] at this
  -- the `φ_j` with `s ≤ j ≤ k` are those of degree `ν_i`; there are `k - s + 1` of them
  have hcardφ : (Finset.univ.filter fun j : Fin m => d j = d i).card = k + 1 - s := by
    rw [← Fin.card_Icc]
    congr 1
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_Icc]
    have h1 := hs j
    have h2 := hk j
    have h3 : d j = d i ↔ ¬ d j < d i ∧ ¬ d i < d j := by omega
    rw [h3, ← h1, ← h2, not_lt, not_lt]
  -- "Therefore, some non-zero linear combination of `φ_s, φ_{s+1}, …, φ_k` with coefficients in
  -- `R/M` must be in the ideal `(φ₁, …, φ_{s-1}) gr_M(R)`. Hence, there exists `j` (`s ≤ j ≤ k`)
  -- such that `φ_j ∈ (φ₁, …, φ_{j-1}) gr_M(R)`. This contradicts (iii)": `card_filter_le_le`
  -- shows `k - s + 1 ≤ #{ψ_t}` (the classes of `φ_s, …, φ_k` modulo `(φ₁, …, φ_{s-1})` are
  -- `R/M`-linearly independent by (iii), and lie in the span of those of `{ψ_t}`)
  have hcount := card_filter_le_le R φ d hd h₂ h₃ ψ e he (d i) H1 H2
  rw [hcardφ] at hcount
  have h5 : (s : ℕ) ≤ i := hsi
  have h6 : (i : ℕ) ≤ k := hik
  omega

/-- Lemma 1, p. 205: "Let `(φ₁, …, φ_m)` be a system of homogeneous elements of `gr_M(J, R)`
such that (i) `gr_M(J, R) = (φ₁, …, φ_m) gr_M(R)`, (ii) if `ν_i = deg φ_i` (`1 ≤ i ≤ m`), then
`ν₁ ≤ ν₂ ≤ … ≤ ν_m`, and (iii) for every `i ≥ 1`, `φ_i ∉ (φ₁, …, φ_{i-1}) gr_M(R)` (where the
empty system of elements generates the zero ideal). Then we have `ν^{(i)}(J) = ν_i` for
`1 ≤ i ≤ m` and `ν^{(i)}(J) = ∞` for all `i > m`."

Bookkeeping: the system is `φ : Fin m → gr_M(R)`, its degrees are given by an explicit
function `d : Fin m → ℕ` with `φ_i ∈ gr^{d i}_M(R)` (so `d` is the degree function `ν_i`, and
the hypotheses `hJ`, `hd`, `h₁`, `h₂`, `h₃` are exactly the properties packaged existentially
in `IsMinimalGradedGenerators`; see `nuI_eq_of_hasLemma1Properties` for that form); the paper's
index `i ∈ {1, …, m}` is `⟨(i : ℕ) + 1, _⟩ : ℕ+` for `i : Fin m`.

The proof is the printed one (pp. 205–206): "In view of (i) and (ii), it is clear from
Definition 1 that `ν_i ≤ μ_i` ... and also that `μ_i = ∞` for all `i > m`", and, for
`μ_i > ν_i` with `i` minimal (strong induction on `i`, `nuI_le_of_lemma1_properties`), the
competing system `ψ`, its reordering by degree, `deg ψ_j ≤ ν_j`, the indices `k` and `s`, the
linear combinations `L_j` and the count of the `ψ_t` of degree `ν_i` against `k - s + 1`.  Two
points the paper leaves implicit are filled in: the printed
"for all `μ < deg ψ_j`" holds for `μ < min (deg ψ_j) ν`, which suffices; and, if `μ_i = ∞`, the
system `ψ` is taken for all `μ < ν` with a finite `ν > ν_i`. -/
@[blueprint "lem:III.1"
  (statement := /-- Let $R$ be a regular local ring with maximal ideal $M$ and $J$ an ideal in
    $R$. Let $(\varphi_1,\dots,\varphi_m)$ be a system of homogeneous elements of
    $\operatorname{gr}_M(J,R)$ such that (i)
    $\operatorname{gr}_M(J,R)=(\varphi_1,\dots,\varphi_m)\operatorname{gr}_M(R)$; (ii) if
    $\nu_i=\deg\varphi_i$ ($1\le i\le m$), then $\nu_1\le\nu_2\le\dots\le\nu_m$; and (iii)
    for every $i\ge1$, $\varphi_i\notin(\varphi_1,\dots,\varphi_{i-1})\operatorname{gr}_M(R)$
    (where the empty system of elements generates the zero ideal). Then we have
    $\nu^{(i)}(J)=\nu_i$ for $1\le i\le m$ and $\nu^{(i)}(J)=\infty$ for all $i>m$
    (\cref{def:III.1}). (Lemma 1, p.~205.) Formalization note (encoding): the degrees
    $\nu_i$ are recorded by an explicit function $d$ with
    $\varphi_i\in\operatorname{gr}^{d(i)}_M(R)$. -/)
  (proof := /-- Let $\mu_i=\nu^{(i)}(J)$. In view of (i) and (ii), it is clear from
    Definition~1 that $\nu_i\le\mu_i$ for all $i$ ($1\le i\le m$), and also that
    $\mu_i=\infty$ for all $i>m$. Suppose we have $i$ ($1\le i\le m$) such that
    $\mu_i>\nu_i$. Let $i$ be the smallest integer with this property. By Definition~1, we
    have homogeneous elements $\psi_1,\dots,\psi_{i-1}$ such that
    $(\psi_1,\dots,\psi_{i-1})\operatorname{gr}_M(R)\cap\operatorname{gr}^\mu_M(R)
    =\operatorname{gr}^\mu_M(J,R)$ for all $\mu<\mu_i$. We may assume that
    $\deg\psi_1\le\dots\le\deg\psi_{i-1}$. Then, for every $j<i$, we have
    $(\psi_1,\dots,\psi_{j-1})\operatorname{gr}_M(R)\cap\operatorname{gr}^\mu_M(R)
    =\operatorname{gr}^\mu_M(J,R)$ for all $\mu<\deg\psi_j$. Hence, by Definition~1, we have
    $\deg\psi_j\le\mu_j=\nu_j$. Thus $\deg\psi_j\le\nu_j$ for all $j<i$. Let $k$ be the
    largest integer such that $\nu_i=\nu_k$. We have $k\ge i$ and
    $(\varphi_1,\dots,\varphi_k)\operatorname{gr}_M(R)\cap\operatorname{gr}^\mu_M(R)
    =\operatorname{gr}^\mu_M(J,R)$ for all $\mu\le\nu_i=\nu_k<\mu_i$. Hence we have
    $(\psi_1,\dots,\psi_{i-1})\operatorname{gr}_M(R)\cap\operatorname{gr}^\mu_M(R)
    =(\varphi_1,\dots,\varphi_k)\operatorname{gr}_M(R)\cap\operatorname{gr}^\mu_M(R)$ for all
    $\mu\le\nu_k$. Let $s$ be the smallest positive integer such that $\nu_s=\nu_i$
    ($=\nu_k$). Then $s\le i$. Let $\{\psi_t\}$ be those which have $\deg\psi_t=\nu_i$. Then
    for each $j$ with $s\le j\le k$, there exists a linear combination $L_j$ of those $\psi_t$
    with coefficients in $R/M$ such that $\varphi_j-L_j$ is contained in the ideal in
    $\operatorname{gr}_M(R)$ generated by those $\psi_n$ with $\deg\psi_n<\nu_i$. Hence by
    the above equality for $\mu<\nu_i=\nu_k$, $\varphi_j-L_j$ is contained in
    $(\varphi_1,\dots,\varphi_{s-1})\operatorname{gr}_M(R)$. (Here, any linear combination of
    the empty set of elements means to be zero.) Since we have $\deg\psi_j\le\nu_j$ for all
    $j$, the number of elements in $\{\psi_t\}$ is less than $k-s+1$. Therefore, some
    non-zero linear combination of $\varphi_s,\dots,\varphi_k$ with coefficients in $R/M$ must
    be in the ideal $(\varphi_1,\dots,\varphi_{s-1})\operatorname{gr}_M(R)$. Hence, there
    exists $j$ ($s\le j\le k$) such that
    $\varphi_j\in(\varphi_1,\dots,\varphi_{j-1})\operatorname{gr}_M(R)$. This contradicts
    (iii).

    \textbf{Formalization.} The proof is the printed one: strong induction on $i$ supplies the
    smallest counterexample; $\psi$ is reordered by a sorting permutation; $\deg\psi_j\le\nu_j$,
    the indices $k$ and $s$, the equality of the two intersections and the count of the $\psi_t$
    of degree $\nu_i$ are separate steps. Two points are filled in. First, the printed ``for all
    $\mu<\deg\psi_j$'' holds for $\mu<\min(\deg\psi_j,\nu)$, where $\nu>\nu_i$ is the bound up
    to which $\psi$ was chosen; this suffices, since $\nu_j<\nu$. Second, when $\mu_i=\infty$
    Definition~1 gives such a $\psi$ for every finite $\nu$ but not obviously one $\psi$ for all
    $\mu$; the proof takes a finite $\nu>\nu_i$, which is all the printed argument uses. The
    final step (some non-zero combination of $\varphi_s,\dots,\varphi_k$ in
    $(\varphi_1,\dots,\varphi_{s-1})$ gives $j$ with $\varphi_j\in(\varphi_1,\dots,\varphi_{j-1})$)
    takes the largest $j$ with non-zero coefficient. -/)
  (latexEnv := "lemma")]
theorem nuI_eq_of_lemma1_properties {m : ℕ} (φ : Fin m → AssocGraded (maximalIdeal R))
    (hJ : ∀ j, φ j ∈ grIdeal (maximalIdeal R) J) (d : Fin m → ℕ)
    (hd : ∀ j, φ j ∈ AssocGraded.homogeneous (maximalIdeal R) (d j))
    (h₁ : grIdeal (maximalIdeal R) J = Ideal.span (Set.range φ)) (h₂ : Monotone d)
    (h₃ : ∀ i : Fin m, φ i ∉ Ideal.span (Set.range fun j : Fin i => φ (Fin.castLE i.2.le j))) :
    (∀ i : Fin m, nuI R J ⟨(i : ℕ) + 1, Nat.succ_pos _⟩ = d i) ∧
    ∀ i : ℕ+, m < (i : ℕ) → nuI R J i = ⊤ := by
  refine ⟨?_, ?_⟩
  · intro i
    induction i using WellFoundedLT.induction with
    | _ i ih =>
      apply le_antisymm
      · -- "Suppose we have `i` such that `μ_i > ν_i`. Let `i` be the smallest integer with this
        -- property": `ih` says `μ_j = ν_j` for `j < i`
        exact nuI_le_of_lemma1_properties R J φ hJ d hd h₁ h₂ h₃ i ih
      · -- "In view of (i) and (ii), it is clear from Definition 1 that `ν_i ≤ μ_i`": `(φ₁, …, φ_{i-1})`
        -- has the property of Definition 1 up to `ν_i`
        exact le_nuI_of_isNuSystem R J (isNuSystem_prefix R J φ hJ d hd h₁ i.2.le
          (fun j hj => h₂ (show i ≤ j from hj)))
  · -- "... and also that `μ_i = ∞` for all `i > m`": pad `φ` by zeros to a system of
    -- `i - 1 ≥ m` homogeneous elements of `gr_M(J, R)`; it still generates `gr_M(J, R)` (by (i)),
    -- hence has the property of Definition 1 for every `ν`.
    intro i hi
    let ψ : Fin ((i : ℕ) - 1) → AssocGraded (maximalIdeal R) := fun j =>
      if h : (j : ℕ) < m then φ ⟨j, h⟩ else 0
    have hspan : Ideal.span (Set.range ψ) = Ideal.span (Set.range φ) := by
      refine le_antisymm (Ideal.span_le.mpr ?_) (Ideal.span_le.mpr ?_)
      · rintro _ ⟨j, rfl⟩
        simp only [ψ]
        split_ifs with h
        · exact Ideal.subset_span ⟨_, rfl⟩
        · exact zero_mem _
      · rintro _ ⟨j, rfl⟩
        refine Ideal.subset_span ⟨⟨j, by omega⟩, ?_⟩
        simp [ψ, j.2]
    have hsys : ∀ ν : ℕ, ∃ ψ' : Fin ((i : ℕ) - 1) → AssocGraded (maximalIdeal R),
        IsNuSystem R J ν ((i : ℕ) - 1) ψ' := by
      intro ν
      refine ⟨ψ, fun j => ?_, fun μ _ χ _ => by rw [hspan, h₁]⟩
      simp only [ψ]
      split_ifs with h
      · exact ⟨hJ _, d _, hd _⟩
      · exact ⟨zero_mem _, 0, zero_mem _⟩
    unfold nuI
    refine le_antisymm le_top ?_
    rw [← ENat.iSup_natCast]
    exact iSup_le fun ν => le_iSup₂ (f := fun (ν : ℕ) (_ : ∃ ψ' : Fin ((i : ℕ) - 1) →
      AssocGraded (maximalIdeal R), IsNuSystem R J ν ((i : ℕ) - 1) ψ') => (ν : ℕ∞)) ν (hsys ν)

/-- Lemma 1 for a system `φ` satisfying `HasLemma1Properties R J φ` (which packages the degree
function existentially): `ν^{(i)}(J)` is the degree of `φ_i` for `1 ≤ i ≤ m` and `∞` for
`i > m`. -/
theorem nuI_eq_of_hasLemma1Properties {m : ℕ} (φ : Fin m → AssocGraded (maximalIdeal R))
    (hφ : IsMinimalGradedGenerators R J φ) :
    (∃ d : Fin m → ℕ, (∀ j, φ j ∈ AssocGraded.homogeneous (maximalIdeal R) (d j)) ∧
      ∀ i : Fin m, nuI R J ⟨(i : ℕ) + 1, Nat.succ_pos _⟩ = d i) ∧
    ∀ i : ℕ+, m < (i : ℕ) → nuI R J i = ⊤ := by
  obtain ⟨hJ, ⟨d, hd, h₂⟩, h₁, h₃⟩ := hφ
  obtain ⟨h, h'⟩ := nuI_eq_of_lemma1_properties R J φ hJ d hd h₁ h₂ h₃
  exact ⟨⟨d, hd, h⟩, h'⟩

end Lemma1

/-! ### The canonical homomorphism `gr_I(A) → gr_{I'}(A')` induced by `α : A → A'` (p. 206) -/

noncomputable section GradedMap

open Polynomial

variable {A : Type u} {A' : Type v} [CommRing A] [CommRing A']

/-- The map of Rees algebras `⊕ Iⁿ Xⁿ → ⊕ I'ⁿ Xⁿ` induced by a ring homomorphism `α : A → A'`,
`I' = IA'` (coefficientwise `α`; cf. `reesMapQuot` for `α = A → A/J`). -/
def reesMap (α : A →+* A') (I : Ideal A) : reesAlgebra I →+* reesAlgebra (I.map α) where
  toFun p := ⟨(p : A[X]).map α, (mem_reesAlgebra_iff _ _).mpr fun i => by
    rw [coeff_map, ← Ideal.map_pow]
    exact Ideal.mem_map_of_mem _ ((mem_reesAlgebra_iff I _).mp p.2 i)⟩
  map_one' := Subtype.ext (by simp)
  map_mul' x y := Subtype.ext (by simp)
  map_zero' := Subtype.ext (by simp)
  map_add' x y := Subtype.ext (by simp)

theorem reesMap_apply_coe (α : A →+* A') (I : Ideal A) (p : reesAlgebra I) :
    (reesMap α I p : A'[X]) = (p : A[X]).map α := rfl

/-- p. 206: "Let `σ̄` be the canonical homomorphism of graded algebras `gr_I(A) → gr_{I'}(A')`
which is induced by `α`", for a ring homomorphism `α : A → A'` and `I' = IA'`.  On the
Rees-algebra model it is `Polynomial.map α` coefficientwise (`reesMap`), which sends
`I · reesAlgebra I = ⊕ Iⁿ⁺¹ Xⁿ` into `I' · reesAlgebra I' = ⊕ I'ⁿ⁺¹ Xⁿ`; on homogeneous
elements it is the class of `a ∈ Iⁿ` ↦ the class of `α(a) ∈ I'ⁿ` (`AssocGraded.map_mk`). -/
@[blueprint "def:III.1-graded-map"
  (statement := /-- Let $\alpha\colon A\to A'$ be a homomorphism of rings, $I$ an ideal in $A$
    and $I'=IA'$. The \emph{canonical homomorphism of graded algebras}
    $\bar\sigma\colon\operatorname{gr}_I(A)\to\operatorname{gr}_{I'}(A')$ induced by
    $\alpha$ (\cref{def:II.1-associated-graded-algebra}) sends the class of $a\in I^n$ in
    $I^n/I^{n+1}$ to the class of $\alpha(a)\in I'^n$ in $I'^n/I'^{n+1}$. (p.~206.) -/)
  (latexEnv := "definition")]
def AssocGraded.map (α : A →+* A') (I : Ideal A) : AssocGraded I →+* AssocGraded (I.map α) :=
  Ideal.quotientMap (I := Ideal.map (algebraMap A (reesAlgebra I)) I) _ (reesMap α I) (by
    intro x hx
    rw [Ideal.mem_comap, mem_map_algebraMap_reesAlgebra_iff]
    rw [mem_map_algebraMap_reesAlgebra_iff] at hx
    intro n
    rw [reesMap_apply_coe, coeff_map, ← Ideal.map_pow]
    exact Ideal.mem_map_of_mem _ (hx n))

/-- `σ̄` sends the class of `a Xⁿ` (`a ∈ Iⁿ`) to the class of `α(a) Xⁿ`. -/
theorem AssocGraded.map_mk (α : A →+* A') (I : Ideal A) (n : ℕ) (a : A) (ha : a ∈ I ^ n) :
    AssocGraded.map α I (AssocGraded.mk I n a ha) =
      AssocGraded.mk (I.map α) n (α a)
        (by rw [← Ideal.map_pow]; exact Ideal.mem_map_of_mem α ha) := by
  show Ideal.Quotient.mk _ (reesMap α I ⟨monomial n a, _⟩) = Ideal.Quotient.mk _ _
  congr 1
  exact Subtype.ext (Polynomial.map_monomial α)

end GradedMap

/-! ### Lemma 2 (pp. 206–207) -/

section Lemma2Diagram

open scoped TensorProduct

/-! The commutative diagram of p. 206, in each degree `n`.

The three horizontal maps `φ`, `φ'`, `φ''` of the diagram are graded, i.e. direct sums over `n`
of their degree-`n` components.  As in Ch. II §1 (`grModMap`), `gr⁰_{I'}(A') ⊗_{A/I} grⁿ_I(A)` is
`A' ⊗_A grⁿ_I(A)`, the component `φₙ : A' ⊗_A grⁿ_I(A) → grⁿ_{I'}(A')` is `x ⊗ [a] ↦ [a x]`
(`grModMap I A' n`, followed by `grModPieceToAssocGraded` for the identification
`IⁿA'/Iⁿ⁺¹A' = grⁿ_{I'}(A')`), and "`φ` is an isomorphism" is "every `φₙ` is bijective". -/

section ModuleToGraded

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]

/-- The identification `IⁿB/Iⁿ⁺¹B = grⁿ_{I''}(B)`, `[c] ↦ [c Xⁿ]`, for an ideal `I''` of `B` with
`I''ᵏ = IᵏB` for all `k` (e.g. `I'' = IB`): it identifies the target `IⁿA'/Iⁿ⁺¹A'` of `φₙ` in
Lemma 2 of Ch. II §1 with the degree-`n` part of `gr_{I'}(A')`, `I' = IA'`. -/
private noncomputable def grModPieceToAssocGraded (I : Ideal A) (I'' : Ideal B)
    (h : ∀ (k : ℕ) (x : B), x ∈ I'' ^ k ↔ x ∈ I ^ k • (⊤ : Submodule A B)) (n : ℕ) :
    GrModPiece I B n →ₗ[A] AssocGraded I'' :=
  Submodule.liftQ _
    { toFun := fun v => AssocGraded.mk I'' n v.1 ((h n v.1).mpr v.2)
      map_add' := fun v w => AssocGraded.mk_add I'' n v.1 w.1 _ _
      map_smul' := fun a v => by
        have := map_smul (AssocGraded.mkLinear I'' n) (algebraMap A B a)
          (⟨v.1, (h n v.1).mpr v.2⟩ : ↥(I'' ^ n))
        rw [AssocGraded.mkLinear_apply, AssocGraded.mkLinear_apply] at this
        rw [RingHom.id_apply, ← algebraMap_smul B a (AssocGraded.mk I'' n v.1 _)]
        convert this using 2
        simp [Algebra.smul_def] }
    (fun v hv => by
      rw [LinearMap.mem_ker]
      refine (AssocGraded.mk_eq_zero_iff I'' ((h n v.1).mpr v.2)).mpr ((h (n + 1) v.1).mpr ?_)
      simpa using hv)

private theorem grModPieceToAssocGraded_mk (I : Ideal A) (I'' : Ideal B)
    (h : ∀ (k : ℕ) (x : B), x ∈ I'' ^ k ↔ x ∈ I ^ k • (⊤ : Submodule A B)) (n : ℕ) (c : B)
    (hc : c ∈ I ^ n • (⊤ : Submodule A B)) :
    grModPieceToAssocGraded I I'' h n (Submodule.Quotient.mk ⟨c, hc⟩) =
      AssocGraded.mk I'' n c ((h n c).mpr hc) := rfl

private theorem grModPieceToAssocGraded_injective (I : Ideal A) (I'' : Ideal B)
    (h : ∀ (k : ℕ) (x : B), x ∈ I'' ^ k ↔ x ∈ I ^ k • (⊤ : Submodule A B)) (n : ℕ) :
    Function.Injective (grModPieceToAssocGraded I I'' h n) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro m hm
  induction m using Submodule.Quotient.induction_on with
  | H x =>
    rw [Submodule.Quotient.mk_eq_zero, Submodule.mem_comap, Submodule.subtype_apply]
    exact (h (n + 1) x.1).mp ((AssocGraded.mk_eq_zero_iff I'' ((h n x.1).mpr x.2)).mp hm)

end ModuleToGraded

section LeftColumn

variable {A : Type u} [CommRing A]

/-- The degree-`n` part `grⁿ_I(A) → grⁿ_Ī(Ā)` of the canonical homomorphism
`gr_I(A) → gr_Ī(Ā)` (`Ā = A/J`, `Ī = IĀ`), the middle map of the left column of the diagram of
p. 206 (before tensoring with `gr⁰_{I'}(A')`). -/
private noncomputable def grPieceMapQuot (I J : Ideal A) (n : ℕ) :
    GrPiece I n →ₗ[A] GrPiece (I.map (Ideal.Quotient.mk J)) n :=
  Submodule.liftQ _
    { toFun := fun v => Submodule.Quotient.mk
        (⟨Ideal.Quotient.mk J v.1, by rw [← Ideal.map_pow]; exact Ideal.mem_map_of_mem _ v.2⟩ :
          ↥(I.map (Ideal.Quotient.mk J) ^ n))
      map_add' := fun v w => rfl
      map_smul' := fun a v => rfl }
    (fun v hv => by
      rw [LinearMap.mem_ker]
      refine (Submodule.Quotient.mk_eq_zero _).mpr ?_
      rw [Submodule.mem_comap, Submodule.subtype_apply]
      show Ideal.Quotient.mk J v.1 ∈ I.map (Ideal.Quotient.mk J) ^ (n + 1)
      rw [← Ideal.map_pow]
      exact Ideal.mem_map_of_mem _ hv)

private theorem ofGrPiece_grPieceMapQuot (I J : Ideal A) (n : ℕ) (z : GrPiece I n) :
    AssocGraded.ofGrPiece (I.map (Ideal.Quotient.mk J)) n (grPieceMapQuot I J n z) =
      grMapQuot I J (AssocGraded.ofGrPiece I n z) := by
  induction z using Submodule.Quotient.induction_on with
  | H v => exact (grMapQuot_mk I J n v.1 v.2).symm

private theorem grPieceMapQuot_surjective (I J : Ideal A) (n : ℕ) :
    Function.Surjective (grPieceMapQuot I J n) := by
  intro w
  induction w using Submodule.Quotient.induction_on with
  | H v =>
    have hv : v.1 ∈ (I ^ n).map (Ideal.Quotient.mk J) := by
      rw [Ideal.map_pow]; exact v.2
    obtain ⟨c, hc, hcv⟩ := (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).mp hv
    exact ⟨Submodule.Quotient.mk ⟨c, hc⟩, by
      show Submodule.Quotient.mk _ = _
      congr 1
      exact Subtype.ext hcv⟩

end LeftColumn

section TensorKernel

variable {A A' : Type u} [CommRing A] [CommRing A'] [Algebra A A']

/-- If `J` kills `N`, then `j ⊗ x = 0` in `A' ⊗_A N` for `j ∈ JA'`. -/
private theorem tmul_eq_zero_of_mem_map {N : Type*} [AddCommGroup N] [Module A N] (J : Ideal A)
    (hN : ∀ a ∈ J, ∀ x : N, a • x = 0) {j : A'} (hj : j ∈ J.map (algebraMap A A')) (x : N) :
    j ⊗ₜ[A] x = 0 := by
  induction hj using Submodule.span_induction with
  | mem j hj =>
    obtain ⟨a, ha, rfl⟩ := hj
    rw [Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul, hN a ha x, TensorProduct.tmul_zero]
  | zero => exact TensorProduct.zero_tmul _ _
  | add j₁ j₂ _ _ h₁ h₂ => rw [TensorProduct.add_tmul, h₁, h₂, add_zero]
  | smul c j _ h => rw [← TensorProduct.smul_tmul', h, smul_zero]

/-- The left vertical sequence of the diagram of p. 206, in degree `n`: "the left vertical
sequence is also exact because `gr⁰_{I'}(A') = A'/I'` is flat over `A/I`" (p. 207).  Here
`ker π → N → N'` is a short exact sequence of `A`-modules (`gr^n_I(J, A) → grⁿ_I(A) → grⁿ_Ī(Ā)`,
exact by Lemma 5, §2, Ch. II) with `J` killing `N'`, and `A'` is flat over `A`: then
`0 → A' ⊗_A ker π → A' ⊗_A N → A'/JA' ⊗_A N' → 0` is exact. -/
private theorem exact_leftColumn [Module.Flat A A'] {N N' : Type*} [AddCommGroup N] [Module A N]
    [AddCommGroup N'] [Module A N'] (J : Ideal A) (hN' : ∀ a ∈ J, ∀ x : N', a • x = 0)
    (π : N →ₗ[A] N') (hπ : Function.Surjective π) :
    Function.Injective (LinearMap.lTensor A' (LinearMap.ker π).subtype) ∧
      (∀ y : A' ⊗[A] N,
        LinearMap.rTensor N' (Ideal.Quotient.mkₐ A (J.map (algebraMap A A'))).toLinearMap
          (LinearMap.lTensor A' π y) = 0 ↔
        y ∈ LinearMap.range (LinearMap.lTensor A' (LinearMap.ker π).subtype)) ∧
      Function.Surjective (fun y : A' ⊗[A] N =>
        LinearMap.rTensor N' (Ideal.Quotient.mkₐ A (J.map (algebraMap A A'))).toLinearMap
          (LinearMap.lTensor A' π y)) := by
  set g : A' →ₗ[A] A' ⧸ J.map (algebraMap A A') :=
    (Ideal.Quotient.mkₐ A (J.map (algebraMap A A'))).toLinearMap with hg
  have hgs : Function.Surjective g := Ideal.Quotient.mk_surjective
  refine ⟨Module.Flat.lTensor_preserves_injective_linearMap _ Subtype.val_injective,
    fun y => ⟨fun hy => ?_, ?_⟩,
    (LinearMap.rTensor_surjective N' hgs).comp (LinearMap.lTensor_surjective A' hπ)⟩
  · -- the kernel of `A' ⊗ N → A'/JA' ⊗ N'`: `JA' ⊗ N'` dies in `A' ⊗ N'` since `J` kills `N'`
    have hex := _root_.rTensor_exact N' (LinearMap.exact_subtype_ker_map g) hgs
    obtain ⟨w, hw⟩ := (hex _).mp hy
    have hw0 : ∀ w : ↥(LinearMap.ker g) ⊗[A] N',
        LinearMap.rTensor N' (LinearMap.ker g).subtype w = 0 := by
      intro w
      induction w with
      | tmul j x =>
        rw [LinearMap.rTensor_tmul, Submodule.subtype_apply]
        refine tmul_eq_zero_of_mem_map J hN' ?_ x
        have := j.2
        rw [LinearMap.mem_ker] at this
        exact Ideal.Quotient.eq_zero_iff_mem.mp this
      | add w₁ w₂ h₁ h₂ => rw [map_add, h₁, h₂, add_zero]
    have h0 : LinearMap.lTensor A' π y = 0 := by rw [← hw, hw0 w]
    exact ((_root_.lTensor_exact A' (LinearMap.exact_subtype_ker_map π) hπ) y).mp h0
  · rintro ⟨w, rfl⟩
    rw [← LinearMap.comp_apply (LinearMap.lTensor A' π), ← LinearMap.lTensor_comp,
      LinearMap.comp_ker_subtype, LinearMap.lTensor_zero, LinearMap.zero_apply, map_zero]

end TensorKernel

section Diagram

variable {A A' : Type u} [CommRing A] [IsNoetherianRing A] [CommRing A'] [IsNoetherianRing A']
  [Algebra A A']

omit [IsNoetherianRing A] in
/-- Tensor over `A` and over `A/J` agree for `A/J`-modules: the scalars of `A/J` move across
`⊗_A`. -/
private theorem compatibleSMul_quotient (J : Ideal A) (M N : Type*) [AddCommGroup M] [Module A M]
    [Module (A ⧸ J) M] [IsScalarTower A (A ⧸ J) M] [AddCommGroup N] [Module A N]
    [Module (A ⧸ J) N] [IsScalarTower A (A ⧸ J) N] :
    TensorProduct.CompatibleSMul A (A ⧸ J) M N :=
  ⟨fun r m n => by
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective r
    show (algebraMap A (A ⧸ J) a • m) ⊗ₜ[A] n = m ⊗ₜ[A] (algebraMap A (A ⧸ J) a • n)
    rw [algebraMap_smul, algebraMap_smul, TensorProduct.smul_tmul]⟩

omit [IsNoetherianRing A] [IsNoetherianRing A'] in
private theorem map_map_quotient_eq (I J : Ideal A) :
    (I.map (Ideal.Quotient.mk J)).map (algebraMap (A ⧸ J) (A' ⧸ J.map (algebraMap A A'))) =
      (I.map (algebraMap A A')).map (Ideal.Quotient.mk (J.map (algebraMap A A'))) := by
  rw [Ideal.map_map, Ideal.map_map]
  congr 1

omit [IsNoetherianRing A] [IsNoetherianRing A'] in
/-- The hypothesis of Lemma 2 of Ch. II §1 for `A/J → A'/J'` ("by the same reason applied to
`A/J → A'/J'`", p. 207): the image of `I(A/J)` lies in the Jacobson radical of `A'/J'` if `IA'`
lies in that of `A'`. -/
private theorem map_map_le_jacobson_quotient (I J : Ideal A)
    (hI : I.map (algebraMap A A') ≤ Ring.jacobson A') :
    ((I.map (Ideal.Quotient.mk J)).map (algebraMap (A ⧸ J) (A' ⧸ J.map (algebraMap A A')))) ≤
      Ring.jacobson (A' ⧸ J.map (algebraMap A A')) := by
  rw [map_map_quotient_eq]
  have h2 : (Ring.jacobson A').map (Ideal.Quotient.mk (J.map (algebraMap A A'))) ≤
      Ring.jacobson (A' ⧸ J.map (algebraMap A A')) := by
    have h3 := Ideal.map_jacobson_of_surjective
      (f := Ideal.Quotient.mk (J.map (algebraMap A A'))) Ideal.Quotient.mk_surjective
      (I := J.map (algebraMap A A')) (by rw [Ideal.mk_ker])
    calc _ ≤ (Ideal.jacobson (J.map (algebraMap A A'))).map
          (Ideal.Quotient.mk (J.map (algebraMap A A'))) :=
          Ideal.map_mono (by rw [← Ideal.jacobson_bot]; exact Ideal.jacobson_mono bot_le)
      _ = Ideal.jacobson ((J.map (algebraMap A A')).map
          (Ideal.Quotient.mk (J.map (algebraMap A A')))) := h3
      _ = Ring.jacobson (A' ⧸ J.map (algebraMap A A')) := by
          rw [Ideal.map_quotient_self, Ideal.jacobson_bot]
  exact (Ideal.map_mono hI).trans h2

/-- Proof of Lemma 2, p. 206–207, the diagram in degree `n`: for `b ∈ J' = JA'` of `I'`-order
`≥ n` (`I' = IA'`), the class `[b Xⁿ]` of `b` in `grⁿ_{I'}(A')` lies in the ideal generated by
`σ̄(gr_I(J, A))`.  In the notation of the diagram (all maps in degree `n`):
`φ : A' ⊗_A grⁿ_I(A) → grⁿ_{I'}(A')`, `φ' : A'/J' ⊗_{A/J} grⁿ_Ī(Ā) → grⁿ_{Ī'}(Ā')`, with `Ā' = A'/J'`,
and `φ''` is the restriction of `φ` to `A' ⊗_A gr^n_I(J, A)`.

The steps are those of the printed proof (p. 207): "By Lemma 2, § 1, Ch. II, `φ` is an
isomorphism, because `A'` is flat over `A` and `α(I)` is contained in the Jacobson radical of
`A'`" (`hφ`); "By the same reason applied to `A/J → A'/J'` (induced by `α`), `φ'` must be an
isomorphism" (`hφ'`); "the left vertical sequence is also exact" (`exact_leftColumn`) and "the
right vertical sequence is exact" (Lemma 5, `ker_grMapQuot`); "Therefore the mapping `φ''` must be
surjective" is the diagram chase `hℓ`, `exact_leftColumn`: `[b Xⁿ] = φ(y)` for some `y` by the
surjectivity of `φ`; the image of `y` in the top left corner is killed by `φ'` (it maps to
`σ̄([b Xⁿ]) = 0`, `b ∈ J'`), hence is `0` since `φ'` is injective; so `y` comes from the left
column's kernel term `A' ⊗_A gr^n_I(J, A)`, i.e. `[b Xⁿ] = φ''(y')`. -/
private theorem mk_mem_map_grIdeal_of_flat [Module.Flat A A'] (I J : Ideal A)
    (hI : I.map (algebraMap A A') ≤ Ring.jacobson A') (n : ℕ) (b : A')
    (hbJ : b ∈ J.map (algebraMap A A')) (hbn : b ∈ I.map (algebraMap A A') ^ n) :
    AssocGraded.mk (I.map (algebraMap A A')) n b hbn ∈
      Ideal.map (AssocGraded.map (algebraMap A A') I) (grIdeal I J) := by
  classical
  have hmem : ∀ (k : ℕ) (x : A'),
      x ∈ I.map (algebraMap A A') ^ k ↔ x ∈ I ^ k • (⊤ : Submodule A A') := by
    intro k x
    rw [Ideal.smul_top_eq_map, Submodule.restrictScalars_mem, Ideal.map_pow]
  have hmem' : ∀ (k : ℕ) (x : A' ⧸ J.map (algebraMap A A')),
      x ∈ (I.map (algebraMap A A')).map (Ideal.Quotient.mk (J.map (algebraMap A A'))) ^ k ↔
        x ∈ (I.map (Ideal.Quotient.mk J)) ^ k •
          (⊤ : Submodule (A ⧸ J) (A' ⧸ J.map (algebraMap A A'))) := by
    intro k x
    rw [Ideal.smul_top_eq_map, Submodule.restrictScalars_mem, Ideal.map_pow,
      map_map_quotient_eq]
  -- "By Lemma 2, § 1, Ch. II, φ is an isomorphism, because A' is flat over A and α(I) is
  -- contained in the Jacobson radical of A'"
  have hφ : ∀ m, Function.Bijective (grModMap I A' m) := by
    have h13 := (flat_tfae_of_map_le_jacobson A A' I hI A').out 1 3
    exact (h13.mp inferInstance).2
  -- "By the same reason applied to A/J → A'/J' (induced by α), φ' must be an isomorphism"
  -- (`A'/J'` is flat over `A/J` by base change, `IA'/J'` is in the Jacobson radical of `A'/J'`)
  have hflat : Module.Flat (A ⧸ J) (A' ⧸ J.map (algebraMap A A')) :=
    Module.Flat.of_linearEquiv (Algebra.TensorProduct.quotIdealMapEquivQuotTensor A' J).toLinearEquiv
  have hφ' : ∀ m, Function.Bijective (grModMap (I.map (Ideal.Quotient.mk J))
      (A' ⧸ J.map (algebraMap A A')) m) := by
    have h13 := (flat_tfae_of_map_le_jacobson (A ⧸ J) (A' ⧸ J.map (algebraMap A A')) _
      (map_map_le_jacobson_quotient I J hI) (A' ⧸ J.map (algebraMap A A'))).out 1 3
    exact (h13.mp hflat).2
  -- the maps of the diagram in degree `n`
  let π := grPieceMapQuot I J n
  let g : A' →ₗ[A] A' ⧸ J.map (algebraMap A A') :=
    (Ideal.Quotient.mkₐ A (J.map (algebraMap A A'))).toLinearMap
  have := compatibleSMul_quotient J (A' ⧸ J.map (algebraMap A A'))
    (GrPiece (I.map (Ideal.Quotient.mk J)) n)
  -- the top left corner is `A'/J' ⊗_{A/J} grⁿ_Ī(Ā)` (`= A'/I' ⊗_{A/I} gr_I(A/J)` of the diagram)
  let ℓ₂ : (A' ⧸ J.map (algebraMap A A')) ⊗[A] GrPiece (I.map (Ideal.Quotient.mk J)) n ≃ₗ[A]
      (A' ⧸ J.map (algebraMap A A')) ⊗[A ⧸ J] GrPiece (I.map (Ideal.Quotient.mk J)) n :=
    (TensorProduct.equivOfCompatibleSMul A (A ⧸ J) A (A' ⧸ J.map (algebraMap A A'))
      (GrPiece (I.map (Ideal.Quotient.mk J)) n)).symm
  have mk_congr : ∀ {B : Type u} [CommRing B] (K : Ideal B) (n : ℕ) (x y : B) (hx : x ∈ K ^ n)
      (hy : y ∈ K ^ n), x = y → AssocGraded.mk K n x hx = AssocGraded.mk K n y hy := by
    rintro B _ K n x y hx hy rfl
    rfl
  -- the right square of the diagram commutes: `φ'` of the image of `y` in the top left corner is
  -- `σ̄(φ(y))` (here both are read in `gr_{Ī'}(Ā') = gr_{I'}(A'/J')`)
  have hcomm : ∀ y : A' ⊗[A] GrPiece I n,
      grModPieceToAssocGraded (I.map (Ideal.Quotient.mk J)) _ hmem' n
        (grModMap (I.map (Ideal.Quotient.mk J)) (A' ⧸ J.map (algebraMap A A')) n
          (ℓ₂ (LinearMap.rTensor _ g (LinearMap.lTensor A' π y)))) =
      grMapQuot (I.map (algebraMap A A')) (J.map (algebraMap A A'))
        (grModPieceToAssocGraded I _ hmem n (grModMap I A' n y)) := by
    intro y
    induction y with
    | tmul a' z =>
      induction z using Submodule.Quotient.induction_on with
      | H v =>
        rw [LinearMap.lTensor_tmul, LinearMap.rTensor_tmul]
        have h1 : ℓ₂ (g a' ⊗ₜ[A] π (Submodule.Quotient.mk v)) =
            (Ideal.Quotient.mk (J.map (algebraMap A A')) a') ⊗ₜ[A ⧸ J]
              (π (Submodule.Quotient.mk v)) := rfl
        have h2 : π (Submodule.Quotient.mk v) = Submodule.Quotient.mk
            (⟨Ideal.Quotient.mk J v.1, by rw [← Ideal.map_pow]; exact Ideal.mem_map_of_mem _ v.2⟩ :
              ↥(I.map (Ideal.Quotient.mk J) ^ n)) := rfl
        rw [h1, h2, grModMap_tmul, grModMap_tmul, grModPieceToAssocGraded_mk,
          grModPieceToAssocGraded_mk, grMapQuot_mk]
        refine mk_congr _ _ _ _ _ _ ?_
        show (algebraMap A (A ⧸ J) v.1) • Ideal.Quotient.mk (J.map (algebraMap A A')) a' = _
        rw [algebraMap_smul]
        exact (map_smul g v.1 a').symm
    | add y₁ y₂ h₁ h₂ => simp only [map_add, h₁, h₂]
  -- `φ` is surjective: `[b Xⁿ] = φ(y)`
  obtain ⟨y, hy⟩ := (hφ n).2 (Submodule.Quotient.mk ⟨b, (hmem n b).mp hbn⟩)
  -- "the right vertical sequence is exact" (Lemma 5): `σ̄([b Xⁿ]) = 0` because `b ∈ J'`; hence
  -- `φ'` kills the image of `y` in the top left corner, and `φ'` is injective
  have hℓ : LinearMap.rTensor _ g (LinearMap.lTensor A' π y) = 0 := by
    have h0 : grModMap (I.map (Ideal.Quotient.mk J)) (A' ⧸ J.map (algebraMap A A')) n
        (ℓ₂ (LinearMap.rTensor _ g (LinearMap.lTensor A' π y))) = 0 := by
      refine grModPieceToAssocGraded_injective (I.map (Ideal.Quotient.mk J)) _ hmem' n ?_
      rw [hcomm y, hy, map_zero, grModPieceToAssocGraded_mk]
      exact RingHom.mem_ker.mp ((ker_grMapQuot (I.map (algebraMap A A'))
        (J.map (algebraMap A A'))).ge (mk_mem_grIdeal _ hbJ hbn))
    exact ℓ₂.injective (((hφ' n).1 (h0.trans (map_zero _).symm)).trans (map_zero _).symm)
  -- "the left vertical sequence is also exact": `y` comes from `A' ⊗_A gr^n_I(J, A)`
  have hJ0 : ∀ a ∈ J, ∀ x : GrPiece (I.map (Ideal.Quotient.mk J)) n, a • x = 0 := by
    intro a ha x
    rw [← algebraMap_smul (A ⧸ J) a x, Ideal.Quotient.algebraMap_eq,
      Ideal.Quotient.eq_zero_iff_mem.mpr ha, zero_smul]
  obtain ⟨w, hw⟩ := ((exact_leftColumn (A' := A') J hJ0 π (grPieceMapQuot_surjective I J n)).2.1
    y).mp hℓ
  -- `φ'' = φ ∘ (1 ⊗ ι)`: its values lie in the ideal generated by `σ̄(gr_I(J, A))`
  have hx : AssocGraded.mk (I.map (algebraMap A A')) n b hbn =
      grModPieceToAssocGraded I _ hmem n (grModMap I A' n y) := by
    rw [hy, grModPieceToAssocGraded_mk]
  rw [hx, ← hw]
  clear hx hw hℓ hy
  induction w with
  | tmul a' z =>
    obtain ⟨z, hz⟩ := z
    induction z using Submodule.Quotient.induction_on with
    | H v =>
      rw [LinearMap.lTensor_tmul, Submodule.subtype_apply]
      show grModPieceToAssocGraded I _ hmem n (grModMap I A' n (a' ⊗ₜ Submodule.Quotient.mk v)) ∈ _
      rw [grModMap_tmul, grModPieceToAssocGraded_mk]
      -- Lemma 5 (p. 190): the class of `v` in `ker π` lies in `gr_I(J, A)`
      have hv : AssocGraded.mk I n v.1 v.2 ∈ grIdeal I J := by
        rw [← ker_grMapQuot I J, RingHom.mem_ker]
        have h := ofGrPiece_grPieceMapQuot I J n (Submodule.Quotient.mk v)
        rw [LinearMap.mem_ker.mp hz, map_zero, AssocGraded.ofGrPiece_mk] at h
        exact h.symm
      have hσ := Ideal.mem_map_of_mem (AssocGraded.map (algebraMap A A') I) hv
      rw [AssocGraded.map_mk] at hσ
      -- the class of `v • a'` is `a' · σ̄([v])`
      have h := map_smul (AssocGraded.mkLinear (I.map (algebraMap A A')) n) a'
        (⟨algebraMap A A' v.1, by rw [← Ideal.map_pow]; exact Ideal.mem_map_of_mem _ v.2⟩ :
          ↥(I.map (algebraMap A A') ^ n))
      rw [AssocGraded.mkLinear_apply, AssocGraded.mkLinear_apply, Algebra.smul_def] at h
      have h' := Ideal.mul_mem_left (Ideal.map (AssocGraded.map (algebraMap A A') I) (grIdeal I J))
        (algebraMap A' (AssocGraded (I.map (algebraMap A A'))) a') hσ
      rw [← h] at h'
      convert h' using 2
      simp [Algebra.smul_def, mul_comm]
  | add w₁ w₂ h₁ h₂ =>
    rw [map_add, map_add, map_add]
    exact add_mem h₁ h₂

end Diagram

end Lemma2Diagram

section Lemma2

variable (A A' : Type u) [CommRing A] [IsNoetherianRing A] [CommRing A'] [IsNoetherianRing A']
  [Algebra A A']

/-- Lemma 2, p. 206: "Let `A` be a noetherian ring, `J` and `I` ideals in `A`. Let
`α : A → A'` be a homomorphism of noetherian rings such that `α(I)` is contained in the
Jacobson radical of `A'`. Let `J' = JA'` and `I' = IA'`. Let `σ̄` be the canonical homomorphism
of graded algebras `gr_I(A) → gr_{I'}(A')` which is induced by `α`. If `A'` is flat over `A`,
then `σ̄(gr_I(J, A))` generates the ideal `gr_{I'}(J', A')`."

Formalization note (encoding): `α = algebraMap A A'` for `[Algebra A A']`; "`σ̄(gr_I(J, A))`
generates `gr_{I'}(J', A')`" is `Ideal.map σ̄ (gr_I(J, A)) = gr_{I'}(J', A')`.

The proof is the printed one (pp. 206–207): the commutative diagram of canonical homomorphisms
with the exact vertical sequences (Lemma 5, §2, Ch. II, `ker_grMapQuot`, and the flatness of
`gr⁰_{I'}(A') = A'/I'` over `A/I`), the isomorphisms `φ` and `φ'` by Lemma 2, §1, Ch. II
(`flat_tfae_of_map_le_jacobson`), and the surjectivity of `φ''` (`mk_mem_map_grIdeal_of_flat`,
degree by degree, as `φ`, `φ'`, `φ''` are graded).  Points the paper leaves implicit are
filled in: the maps of the diagram are the degree-`n`
components, `σ̄` maps `gr_I(J, A)` into `gr_{I'}(J', A')` (so that `φ''` exists), the
hypotheses of Lemma 2, §1, Ch. II for `A/J → A'/J'` are verified, and the tensor products over
`A/I` with `A'/I'` are identified with tensor products over `A`. -/
@[blueprint "lem:III.2"
  (statement := /-- Let $A$ be a noetherian ring, $J$ and $I$ ideals in $A$. Let
    $\alpha\colon A\to A'$ be a homomorphism of noetherian rings such that $\alpha(I)$ is
    contained in the Jacobson radical of $A'$. Let $J'=JA'$ and $I'=IA'$. Let $\bar\sigma$ be
    the canonical homomorphism of graded algebras
    $\operatorname{gr}_I(A)\to\operatorname{gr}_{I'}(A')$ which is induced by $\alpha$
    (\cref{def:III.1-graded-map}). If $A'$ is flat over $A$, then
    $\bar\sigma(\operatorname{gr}_I(J,A))$ generates the ideal $\operatorname{gr}_{I'}(J',A')$
    (\cref{def:II.2-graded-ideal}). (Lemma 2, p.~206.) -/)
  (proof := /-- We have the following commutative diagram of canonical homomorphisms
    \[\begin{array}{ccc}
    \operatorname{gr}_{\bar I}(A/J)\otimes_{A/I}\operatorname{gr}^0_{I'}(A') &
      \xrightarrow{\ \varphi'\ } & \operatorname{gr}_{\bar I'}(A'/J') \\
    \uparrow && \uparrow \\
    \operatorname{gr}_I(A)\otimes_{A/I}\operatorname{gr}^0_{I'}(A') &
      \xrightarrow{\ \varphi\ } & \operatorname{gr}_{I'}(A') \\
    \uparrow && \uparrow \\
    \operatorname{gr}_I(J,A)\otimes_{A/I}\operatorname{gr}^0_{I'}(A') &
      \xrightarrow{\ \varphi''\ } & \operatorname{gr}_{I'}(J',A') \\
    \uparrow && \uparrow \\
    0 && 0
    \end{array}\]
    (where $\bar I=I(A/J)$ and $\bar I'=I'(A'/J')$), where the right vertical sequence is
    exact while the left vertical sequence is also exact because
    $\operatorname{gr}^0_{I'}(A')=A'/I'$ is flat over $A/I$. (See Lemma~5, \S2, Ch.~II,
    \cref{lem:II.2-5}.) By Lemma~2, \S1, Ch.~II (\cref{lem:II.1-2}), $\varphi$ is an
    isomorphism, because $A'$ is flat over $A$ and $\alpha(I)$ is contained in the Jacobson
    radical of $A'$. By the same reason applied to $A/J\to A'/J'$ (induced by $\alpha$),
    $\varphi'$ must be an isomorphism. Therefore the mapping $\varphi''$ must be surjective.
    This means that the image of $\operatorname{gr}_I(J,A)$ by the canonical homomorphism
    $\bar\sigma\colon\operatorname{gr}_I(A)\to\operatorname{gr}_{I'}(A')$ generates the ideal
    $\operatorname{gr}_{I'}(J',A')$.

    \textbf{Formalization.} The proof is the printed one. The three horizontal maps are graded,
    and the diagram chase is done in each degree $n$: $\varphi_n$ is surjective (and
    bijective, by Lemma~2 of Ch.~II \S1, \cref{lem:II.1-2}, for $A\to A'$), $\varphi'_n$ is
    injective (Lemma~2 of Ch.~II \S1 for $A/J\to A'/J'$, whose hypotheses are verified: flatness
    by base change, $I(A'/J')$ in the Jacobson radical), the left vertical sequence is exact
    (flatness of $A'$; Lemma~5, \S2, Ch.~II for the identification of its kernel term with
    $\operatorname{gr}^n_I(J,A)$), and the right column is exact (Lemma~5). Several identifications
    that the paper does not state are proved: $\operatorname{gr}^0_{I'}(A')\otimes_{A/I}
    \operatorname{gr}^n_I(A)=A'\otimes_A\operatorname{gr}^n_I(A)$ and
    $A'/J'\otimes_{A/J}\operatorname{gr}^n_{\bar I}(\bar A)=A'/J'\otimes_A
    \operatorname{gr}^n_{\bar I}(\bar A)$, the identification of $I^nA'/I^{n+1}A'$ with
    $\operatorname{gr}^n_{I'}(A')$, the commutativity of the right square, and the fact that
    $\bar\sigma$ maps $\operatorname{gr}_I(J,A)$ into $\operatorname{gr}_{I'}(J',A')$ (so that
    $\varphi''$ exists). -/)
  (latexEnv := "lemma")]
theorem map_grIdeal_eq_grIdeal_map_of_flat (I J : Ideal A)
    (hI : I.map (algebraMap A A') ≤ Ring.jacobson A') [Module.Flat A A'] :
    Ideal.map (AssocGraded.map (algebraMap A A') I) (grIdeal I J) =
      grIdeal (I.map (algebraMap A A')) (J.map (algebraMap A A')) := by
  apply le_antisymm
  · -- the canonical homomorphisms of the diagram exist: `σ̄` maps the initial form of `g ∈ J` to
    -- the class of `α(g) ∈ J'`, so `σ̄(gr_I(J, A)) ⊆ gr_{I'}(J', A')` (the map `φ''`)
    rw [Ideal.map_le_iff_le_comap, grIdeal, Ideal.span_le]
    rintro _ ⟨g, hg, rfl⟩
    rw [SetLike.mem_coe, Ideal.mem_comap]
    by_cases htop : Ideal.ordElem I g = ⊤
    · rw [initialForm, dite_eq_left htop, map_zero]
      exact zero_mem _
    · obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp htop
      rw [initialForm_eq_mk I hn.symm, AssocGraded.map_mk]
      exact mk_mem_grIdeal _ (Ideal.mem_map_of_mem _ hg) _
  · -- "Therefore the mapping φ'' must be surjective": `gr_{I'}(J', A')` is generated by the
    -- initial forms of the elements `b ∈ J'`, each of which is homogeneous
    rw [grIdeal, Ideal.span_le]
    rintro _ ⟨b, hb, rfl⟩
    rw [SetLike.mem_coe]
    by_cases htop : Ideal.ordElem (I.map (algebraMap A A')) b = ⊤
    · rw [initialForm, dite_eq_left htop]
      exact zero_mem _
    obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp htop
    rw [initialForm_eq_mk _ hn.symm]
    exact mk_mem_map_grIdeal_of_flat I J hI n b hb (Ideal.mem_pow_of_ordElem hn.symm)

end Lemma2

/-! ### Corollary to Lemma 2 (p. 207) -/

/-! ### The initial form of `α(a)` (p. 207): "we can easily see that `σ̄(φ_j)` is the initial form of `α(f_j)`" -/

section GrMapMax

/-- The initial form is carried to the initial form by a homomorphism `σ` of graded algebras with
`σ[a] = [α a]` as soon as the order of `a` is preserved by `α`. -/
theorem initialForm_map_of_ordElem_eq {A : Type u} {A' : Type v} [CommRing A] [CommRing A']
    (α : A →+* A') (I : Ideal A) (I' : Ideal A') (σ : AssocGraded I →+* AssocGraded I')
    (hσ : ∀ (n : ℕ) (a : A) (ha : a ∈ I ^ n) (ha' : α a ∈ I' ^ n),
      σ (AssocGraded.mk I n a ha) = AssocGraded.mk I' n (α a) ha') (a : A)
    (h : Ideal.ordElem I' (α a) = Ideal.ordElem I a) :
    σ (initialForm I a) = initialForm I' (α a) := by
  by_cases htop : Ideal.ordElem I a = ⊤
  · have htop' : Ideal.ordElem I' (α a) = ⊤ := h.trans htop
    rw [initialForm, dite_eq_left htop, initialForm, dite_eq_left htop', map_zero]
  · obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp htop
    have hn' : Ideal.ordElem I' (α a) = n := h.trans hn.symm
    rw [initialForm_eq_mk _ hn.symm, initialForm_eq_mk _ hn',
      hσ n a (Ideal.mem_pow_of_ordElem hn.symm) (Ideal.mem_pow_of_ordElem hn')]

variable {R R' : Type u} [CommRing R] [CommRing R'] [IsRegularLocalRing R]
  [IsRegularLocalRing R'] (α : R →+* R') [IsLocalHom α]

omit [IsRegularLocalRing R'] [IsLocalHom α] in
theorem exists_grMapMax_aux (P' : Ideal R') (hM : (maximalIdeal R).map α = P') :
    ∃ σ : AssocGraded (maximalIdeal R) →+* AssocGraded P',
      ∀ (n : ℕ) (a : R) (ha : a ∈ maximalIdeal R ^ n) (ha' : α a ∈ P' ^ n),
        σ (AssocGraded.mk _ n a ha) = AssocGraded.mk P' n (α a) ha' := by
  subst hM
  exact ⟨AssocGraded.map α _, fun n a ha ha' => AssocGraded.map_mk α _ n a ha⟩

/-- The homomorphism `gr_M(R) → gr_{M'}(R')` of graded algebras induced by `α` when `MR' = M'`
(p. 206: "Let `σ̄` be the canonical homomorphism of graded algebras `gr_I(A) → gr_{I'}(A')`
which is induced by `α`"). -/
noncomputable def grMapMax (hα : RingHom.MapsRSOP α) :
    AssocGraded (maximalIdeal R) →+* AssocGraded (maximalIdeal R') :=
  (exists_grMapMax_aux α _ hα.map_maximalIdeal).choose

omit [IsLocalHom α] in
theorem grMapMax_mk (hα : RingHom.MapsRSOP α) (n : ℕ) (a : R) (ha : a ∈ maximalIdeal R ^ n)
    (ha' : α a ∈ maximalIdeal R' ^ n) :
    grMapMax α hα (AssocGraded.mk _ n a ha) = AssocGraded.mk _ n (α a) ha' :=
  (exists_grMapMax_aux α _ hα.map_maximalIdeal).choose_spec n a ha ha'

/-- `ν_{M'}(α a) = ν_M(a)` for `α` transforming a regular system of parameters into one: `a ∈ Mᵏ`
iff `α a ∈ M'ᵏ` (`RingHom.MapsRSOP.comap_maximalIdeal_pow`, which uses the quasi-regularity of the
regular system of parameters and no flatness). -/
theorem ordElem_map_of_mapsRSOP (hα : RingHom.MapsRSOP α) (a : R) :
    Ideal.ordElem (maximalIdeal R') (α a) = Ideal.ordElem (maximalIdeal R) a := by
  refine le_antisymm (Ideal.ordElem_le fun ν hν => Ideal.le_ordElem ?_)
    (Ideal.ordElem_le fun ν hν => Ideal.le_ordElem ?_)
  · rw [← hα.comap_maximalIdeal_pow ν, Ideal.mem_comap]
    exact hν
  · have h : a ∈ ((maximalIdeal R') ^ ν).comap α := by
      rw [hα.comap_maximalIdeal_pow ν]
      exact hν
    exact Ideal.mem_comap.mp h

/-- Corollary to Lemma 2, p. 207: "We can easily see that `σ̄(φ_j)` is the initial form of `α(f_j)` in
`gr_{M'}(R')`": the initial form of `α a` is the image under `σ̄` of the initial form of `a`
(the order is preserved, `ordElem_map_of_mapsRSOP`). -/
theorem initialForm_map_of_mapsRSOP (hα : RingHom.MapsRSOP α) (a : R) :
    initialForm (maximalIdeal R') (α a) = grMapMax α hα (initialForm (maximalIdeal R) a) :=
  (initialForm_map_of_ordElem_eq α (maximalIdeal R) (maximalIdeal R') (grMapMax α hα)
    (fun n b hb hb' => grMapMax_mk α hα n b hb hb') a (ordElem_map_of_mapsRSOP α hα a)).symm

end GrMapMax

section CorLemma2

variable {R R' : Type u} [CommRing R] [IsRegularLocalRing R] [CommRing R']
  [IsRegularLocalRing R']

/-- The initial form of an element is homogeneous (of degree `ν_I(f)`, or `0` if it vanishes). -/
private theorem exists_initialForm_mem_homogeneous {A : Type*} [CommRing A] (I : Ideal A) (f : A) :
    ∃ d, initialForm I f ∈ AssocGraded.homogeneous I d := by
  by_cases htop : Ideal.ordElem I f = ⊤
  · exact ⟨0, by rw [initialForm, dite_eq_left htop]; exact zero_mem _⟩
  · obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp htop
    exact ⟨n, by rw [initialForm_eq_mk I hn.symm]; exact AssocGraded.mk_mem_homogeneous I _⟩

/-- `gr_M(J, R)` is generated by finitely many homogeneous elements of `gr_M(J, R)`. -/
private theorem exists_fin_homogeneous_generators (J : Ideal R) :
    ∃ (m : ℕ) (φ : Fin m → AssocGraded (maximalIdeal R)),
      (∀ j, φ j ∈ grIdeal (maximalIdeal R) J ∧
        ∃ d, φ j ∈ AssocGraded.homogeneous (maximalIdeal R) d) ∧
      grIdeal (maximalIdeal R) J = Ideal.span (Set.range φ) := by
  have : IsNoetherianRing (AssocGraded (maximalIdeal R)) :=
    inferInstanceAs (IsNoetherianRing (reesAlgebra (maximalIdeal R) ⧸ _))
  obtain ⟨s, hs, hspan⟩ := (Submodule.fg_span_iff_fg_span_finset_subset
    (initialForm (maximalIdeal R) '' (J : Set R))).mp
      (IsNoetherian.noetherian (grIdeal (maximalIdeal R) J))
  refine ⟨s.card, fun j => (s.equivFin.symm j : AssocGraded (maximalIdeal R)), fun j => ?_, ?_⟩
  · obtain ⟨f, -, hf⟩ := hs (s.equivFin.symm j).2
    refine ⟨Ideal.subset_span (hs (s.equivFin.symm j).2), ?_⟩
    show ∃ d, (s.equivFin.symm j : AssocGraded (maximalIdeal R)) ∈ _
    rw [← hf]
    exact exists_initialForm_mem_homogeneous _ f
  · refine hspan.trans (congrArg (Submodule.span _) ?_)
    ext x
    refine ⟨fun hx => ⟨s.equivFin ⟨x, hx⟩, by simp⟩, ?_⟩
    rintro ⟨j, rfl⟩
    exact (s.equivFin.symm j).2

/-- Every ideal `J` has a system of homogeneous elements of `gr_M(J, R)` with the properties
(i), (ii), (iii) of Lemma 1: sort finitely many homogeneous generators by degree and discard
those lying in the ideal generated by the preceding ones. -/
private theorem exists_isMinimalGradedGenerators (J : Ideal R) :
    ∃ (m : ℕ) (φ : Fin m → AssocGraded (maximalIdeal R)) (d : Fin m → ℕ),
      (∀ j, φ j ∈ grIdeal (maximalIdeal R) J) ∧
      (∀ j, φ j ∈ AssocGraded.homogeneous (maximalIdeal R) (d j)) ∧
      grIdeal (maximalIdeal R) J = Ideal.span (Set.range φ) ∧ Monotone d ∧
      ∀ i : Fin m, φ i ∉ Ideal.span (Set.range fun j : Fin i => φ (Fin.castLE i.2.le j)) := by
  classical
  obtain ⟨n, g, hg, hspan⟩ := exists_fin_homogeneous_generators J
  choose e he using fun t => (hg t).2
  -- sort the generators by degree
  let g' := g ∘ Tuple.sort e
  let e' := e ∘ Tuple.sort e
  have he' : Monotone e' := Tuple.monotone_sort e
  have hspan' : grIdeal (maximalIdeal R) J = Ideal.span (Set.range g') := by
    rw [hspan, Set.range_comp, (Tuple.sort e).surjective.range_eq, Set.image_univ]
  -- keep the generators not in the ideal generated by the preceding ones
  let S : Finset (Fin n) := Finset.univ.filter fun i =>
    g' i ∉ Ideal.span (Set.range fun j : Fin i => g' (Fin.castLE i.2.le j))
  let emb := S.orderEmbOfFin rfl
  refine ⟨S.card, fun k => g' (emb k), fun k => e' (emb k), fun k => (hg _).1, fun k => he _,
    ?_, he'.comp emb.monotone, ?_⟩
  · rw [hspan']
    refine le_antisymm ?_ (Ideal.span_le.mpr ?_)
    · have key : ∀ N : ℕ, ∀ i : Fin n, (i : ℕ) < N →
          g' i ∈ Ideal.span (Set.range fun k => g' (emb k)) := by
        intro N
        induction N with
        | zero => intro i hi; omega
        | succ N ih =>
          intro i hi
          by_cases hiS : i ∈ S
          · have : i ∈ Set.range emb := by rw [Finset.range_orderEmbOfFin]; exact hiS
            obtain ⟨k, rfl⟩ := this
            exact Ideal.subset_span ⟨k, rfl⟩
          · have hmem : g' i ∈
                Ideal.span (Set.range fun j : Fin i => g' (Fin.castLE i.2.le j)) := by
              simpa [S] using hiS
            refine (Ideal.span_le.mpr ?_) hmem
            rintro _ ⟨j, rfl⟩
            exact ih _ (by simp only [Fin.val_castLE]; omega)
      refine Ideal.span_le.mpr ?_
      rintro _ ⟨i, rfl⟩
      exact key (n) i i.2
    · rintro _ ⟨k, rfl⟩
      exact Ideal.subset_span ⟨_, rfl⟩
  · intro k hk
    have hkS : emb k ∈ S := S.orderEmbOfFin_mem rfl k
    rw [Finset.mem_filter] at hkS
    apply hkS.2
    refine (Ideal.span_mono ?_) hk
    rintro _ ⟨j, rfl⟩
    have hlt : emb (Fin.castLE k.2.le j) < emb k :=
      emb.strictMono (show Fin.castLE k.2.le j < k from Fin.lt_def.mpr (by simp))
    exact ⟨⟨(emb (Fin.castLE k.2.le j) : ℕ), hlt⟩, by simp⟩


/-- Remark (c), p. 209: "we take a standard base `(f₁, …, f_m)` of `J`" (also the Corollary to Lemma 2,
p. 207: "We have a system of elements `(f₁, …, f_m)` of `J` such that: if `φ_j` is the initial form of
`f_j` in `gr_M(R)`, then the system `(φ₁, …, φ_m)` possesses the properties (i), (ii), and (iii) of
Lemma 1").  A standard base exists (the paper does not say so): lift the homogeneous system of Lemma 1 (`exists_isMinimalGradedGenerators`,
sorting and pruning finitely many generators of `gr_M(J, R)`) to elements of `J`; a non-zero
homogeneous element of degree `d` of `gr_M(J, R)` is the initial form of an element of `J` of
order `d`. -/
private theorem exists_isStandardBase_lift (J : Ideal R) :
    ∃ (m : ℕ) (f : Fin m → R), IsStandardBase R J f := by
  obtain ⟨m, φ, d, hJφ, hd, h₁, h₂, h₃⟩ := exists_isMinimalGradedGenerators (R := R) J
  have hlift : ∀ t, ∃ a ∈ J, initialForm (maximalIdeal R) a = φ t := by
    intro t
    obtain ⟨a, ⟨haJ, -⟩, ha, hmk⟩ :=
      (grIdeal_homogeneous_eq (maximalIdeal R) J (d t) (φ t) (hd t)).mp (hJφ t)
    refine ⟨a, haJ, ?_⟩
    have hord : Ideal.ordElem (maximalIdeal R) a = d t := by
      refine le_antisymm (Ideal.ordElem_le_of_notMem fun ha1 => h₃ t ?_) (Ideal.le_ordElem ha)
      rw [← hmk, (AssocGraded.mk_eq_zero_iff _ ha).mpr ha1]
      exact zero_mem _
    rw [initialForm_eq_mk _ hord, hmk]
  choose f hfJ hf using hlift
  have hφ : (fun j => initialForm (maximalIdeal R) (f j)) = φ := funext hf
  exact ⟨m, f, hfJ, by rw [hφ]; exact ⟨hJφ, ⟨d, hd, h₂⟩, h₁, h₃⟩⟩

/-- Descent of ideal membership along a coefficient extension `k[X] → k'[X]` for a homomorphism
`ρ : k → k'` from a field: `(𝔟 k'[X]) ∩ k[X] = 𝔟` (coefficientwise application of a
`k`-linear retraction `k' → k` of `ρ` is `k[X]`-linear). -/
private theorem mem_of_map_mem_map {k k' : Type*} [Field k] [CommRing k'] [Nontrivial k']
    {n : ℕ} (ρ : k →+* k') (𝔟 : Ideal (MvPolynomial (Fin n) k)) {p : MvPolynomial (Fin n) k}
    (hp : MvPolynomial.map ρ p ∈ Ideal.map (MvPolynomial.map ρ) 𝔟) : p ∈ 𝔟 := by
  let _ := ρ.toAlgebra
  obtain ⟨π, hπ⟩ := LinearMap.exists_leftInverse_of_injective (Algebra.linearMap k k')
    (LinearMap.ker_eq_bot.mpr ρ.injective)
  have hπρ : ∀ a, π (ρ a) = a := fun a => LinearMap.congr_fun hπ a
  have hπmul : ∀ a y, π (ρ a * y) = a * π y := fun a y => by
    have h : ρ a * y = a • y := by rw [Algebra.smul_def]; rfl
    rw [h, map_smul, smul_eq_mul]
  obtain ⟨Pr, hPr⟩ : ∃ Pr : MvPolynomial (Fin n) k' → MvPolynomial (Fin n) k,
      ∀ q m, (Pr q).coeff m = π (q.coeff m) :=
    ⟨fun q => AddMonoidAlgebra.ofCoeff (Finsupp.mapRange π (map_zero π) q.coeff),
      fun q m => rfl⟩
  have hadd : ∀ q₁ q₂, Pr (q₁ + q₂) = Pr q₁ + Pr q₂ := fun q₁ q₂ => by
    ext m
    simp only [hPr, AddMonoidAlgebra.coeff_add, Finsupp.coe_add, Pi.add_apply, map_add]
  have hzero : Pr 0 = 0 := by
    ext m
    simp only [hPr, AddMonoidAlgebra.coeff_zero, Finsupp.coe_zero, Pi.zero_apply, map_zero]
  have hmul : ∀ b c, Pr (MvPolynomial.map ρ b * c) = b * Pr c := fun b c => by
    ext m
    rw [hPr, MvPolynomial.coeff_mul, MvPolynomial.coeff_mul, map_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [MvPolynomial.coeff_map, hπmul, hPr]
  have hmap : ∀ b, Pr (MvPolynomial.map ρ b) = b := fun b => by
    ext m
    rw [hPr, MvPolynomial.coeff_map, hπρ]
  have key : ∀ y ∈ Ideal.map (MvPolynomial.map ρ) 𝔟, ∀ c, Pr (c * y) ∈ 𝔟 := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨b, hb, rfl⟩ := hy
      intro c
      rw [mul_comm, hmul]
      exact 𝔟.mul_mem_right _ hb
    | zero => intro c; rw [mul_zero, hzero]; exact zero_mem _
    | add x y _ _ hx hy => intro c; rw [mul_add, hadd]; exact add_mem (hx c) (hy c)
    | smul d x _ hx => intro c; rw [smul_eq_mul, ← mul_assoc]; exact hx (c * d)
  simpa [hmap] using key _ hp 1

open Classical in
/-- The homomorphism `σ : gr_M(R) → gr_{M'}(R')` sending the class of `a` to the class of `α(a)`, for `α`
transforming a regular system of parameters of `R` into one of `R'`, is *pure* (it is faithfully flat): in
the polynomial pictures `gr_M(R) = k[X]`, `gr_{M'}(R') = k'[X]` given by `α`-corresponding regular
systems of parameters, `σ` is the coefficient extension `k[X] → k'[X]` along the field homomorphism
`k = R/M → k' = R'/M'`, so `σ(x) ∈ σ(𝔞) gr_{M'}(R')` implies `x ∈ 𝔞` for every ideal `𝔞` of `gr_M(R)`
("faithfully flat, so non-membership descends", the Remark of p. 238). -/
theorem mem_of_map_mem_map_of_gradedMap (α : R →+* R') [IsLocalHom α] (s : Finset R)
    (hs : IsRegularSystemOfParameters R s) (hs' : IsRegularSystemOfParameters R' (s.image α))
    (hinj : Set.InjOn α s)
    (σ : AssocGraded (maximalIdeal R) →+* AssocGraded (maximalIdeal R'))
    (hσ : ∀ (n : ℕ) (a : R) (ha : a ∈ maximalIdeal R ^ n) (ha' : α a ∈ maximalIdeal R' ^ n),
      σ (AssocGraded.mk _ n a ha) = AssocGraded.mk (maximalIdeal R') n (α a) ha')
    (𝔞 : Ideal (AssocGraded (maximalIdeal R))) (x : AssocGraded (maximalIdeal R))
    (hx : σ x ∈ Ideal.map σ 𝔞) : x ∈ 𝔞 := by
  classical
  let _ : Field (R ⧸ maximalIdeal R) := Ideal.Quotient.field _
  let _ : Field (R' ⧸ maximalIdeal R') := Ideal.Quotient.field _
  have hMM : ∀ a ∈ maximalIdeal R, α a ∈ maximalIdeal R' := fun a ha => map_nonunit α a ha
  have hαn : ∀ (n : ℕ) (a : R), a ∈ maximalIdeal R ^ n → α a ∈ maximalIdeal R' ^ n := by
    intro n a ha
    have h1 : α a ∈ ((maximalIdeal R) ^ n).map α := Ideal.mem_map_of_mem α ha
    rw [Ideal.map_pow] at h1
    exact Ideal.pow_right_mono (Ideal.map_le_iff_le_comap.mpr hMM) n h1
  -- the polynomial pictures of `gr_M(R)` and `gr_{M'}(R')`
  let z : Fin s.card → R := fun i => ((s.equivFin.symm i : s) : R)
  have hz : ∀ i, z i ∈ maximalIdeal R ^ 1 := fun i => by
    rw [pow_one, ← hs.1]
    exact Ideal.subset_span (s.equivFin.symm i).2
  have hz' : ∀ i, α (z i) ∈ maximalIdeal R' ^ 1 := fun i => hαn 1 _ (hz i)
  let e := MvPolynomial.aeval (R := R ⧸ maximalIdeal R)
    fun i => AssocGraded.mk (maximalIdeal R) 1 (z i) (hz i)
  have he : Function.Bijective e := assocGraded_maximalIdeal_aeval_bijective_of_rsop hs hz
  have hspan' : Ideal.span (Set.range fun i => α (z i)) = maximalIdeal R' := by
    have h := hs'.1
    rw [Finset.coe_image] at h
    rw [← h]
    congr 1
    ext y
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨_, (s.equivFin.symm i).2, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨s.equivFin ⟨x, hx⟩, by simp [z]⟩
  have hn' : (s.card : WithBot ℕ∞) = ringKrullDim R' := by
    rw [← hs'.2, Finset.card_image_of_injOn hinj]
  let e' := MvPolynomial.aeval (R := R' ⧸ maximalIdeal R')
    fun i => AssocGraded.mk (maximalIdeal R') 1 (α (z i)) (hz' i)
  have he' : Function.Bijective e' := assocGraded_maximalIdeal_aeval_bijective hspan' hn' hz'
  let ρ : R ⧸ maximalIdeal R →+* R' ⧸ maximalIdeal R' :=
    Ideal.quotientMap (maximalIdeal R') α fun a ha => hMM a ha
  -- `σ` is the coefficient extension along `ρ`
  have hcomm : σ.comp (e : MvPolynomial (Fin s.card) (R ⧸ maximalIdeal R) →+*
      AssocGraded (maximalIdeal R)) =
      (e' : MvPolynomial (Fin s.card) (R' ⧸ maximalIdeal R') →+*
        AssocGraded (maximalIdeal R')).comp (MvPolynomial.map ρ) := by
    refine MvPolynomial.ringHom_ext (fun c => ?_) (fun i => ?_)
    · obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective c
      simp only [RingHom.coe_comp, Function.comp_apply, RingHom.coe_coe, MvPolynomial.map_C,
        MvPolynomial.aeval_C, e, e']
      rw [← mk_zero_eq_algebraMap_mk _ r (by simp), hσ 0 r _ (by simp),
        show ρ (Ideal.Quotient.mk _ r) = Ideal.Quotient.mk _ (α r) from Ideal.quotientMap_mk,
        ← mk_zero_eq_algebraMap_mk]
    · simp only [RingHom.coe_comp, Function.comp_apply, RingHom.coe_coe, MvPolynomial.map_X,
        MvPolynomial.aeval_X, e, e']
      exact hσ 1 _ (hz i) (hz' i)

  let eR : MvPolynomial (Fin s.card) (R ⧸ maximalIdeal R) →+* AssocGraded (maximalIdeal R) := e
  let eR' : MvPolynomial (Fin s.card) (R' ⧸ maximalIdeal R') →+*
    AssocGraded (maximalIdeal R') := e'
  obtain ⟨p, rfl⟩ := he.2 x
  have h𝔞 : 𝔞 = Ideal.map eR (Ideal.comap eR 𝔞) :=
    (Ideal.map_comap_of_surjective eR he.2 𝔞).symm
  rw [h𝔞, Ideal.map_map] at hx
  have hx' : eR' (MvPolynomial.map ρ p) ∈
      Ideal.map eR' (Ideal.map (MvPolynomial.map ρ) (Ideal.comap eR 𝔞)) := by
    rw [Ideal.map_map, ← hcomm,
      show eR' (MvPolynomial.map ρ p) = σ (e p) from (RingHom.congr_fun hcomm p).symm]
    exact hx
  rw [← Ideal.mem_comap, Ideal.comap_map_of_bijective eR' he'] at hx'
  exact mem_of_map_mem_map ρ _ hx'


/-- `mem_of_map_mem_map_of_gradedMap` for the canonical homomorphism `grMapMax`: `gr_M(R) → gr_{M'}(R')` is
pure, i.e. `grMapMax x ∈ 𝔞 · gr_{M'}(R')` implies `x ∈ 𝔞`. -/
theorem mem_of_map_mem_map_grMapMax (α : R →+* R') [IsLocalHom α] (hα : RingHom.MapsRSOP α)
    (𝔞 : Ideal (AssocGraded (maximalIdeal R))) (x : AssocGraded (maximalIdeal R))
    (hx : grMapMax α hα x ∈ Ideal.map (grMapMax α hα) 𝔞) : x ∈ 𝔞 := by
  obtain ⟨s, hs, hs', hinj⟩ := id hα
  exact mem_of_map_mem_map_of_gradedMap α s hs hs' hinj (grMapMax α hα)
    (fun n a ha ha' => grMapMax_mk α hα n a ha ha') 𝔞 x hx

open Classical in
/-- The Corollary to Lemma 2 for a homomorphism `σ : gr_M(R) → gr_{M'}(R')` sending the class
of `a` to the class of `α(a)` and `gr_M(J, R)` onto generators of `gr_{M'}(J', R')`: the initial
forms `φ_j` of a standard base `(f_j)` of `J` are carried to the initial forms `σ(φ_j)` of the
`α(f_j)` ("we can easily see", `initialForm_map_of_ordElem_eq`), a system with the properties
(i)–(iii) of Lemma 1 for `J'`. (Property (iii) is preserved because, in the polynomial pictures
`gr_M(R) = k[X]`, `gr_{M'}(R') = k'[X]` given by `α`-corresponding regular systems of parameters,
`σ` is the coefficient extension `k[X] → k'[X]`.) -/
private theorem nuI_eq_of_gradedMap (α : R →+* R') [IsLocalHom α] (s : Finset R)
    (hs : IsRegularSystemOfParameters R s) (hs' : IsRegularSystemOfParameters R' (s.image α))
    (hinj : Set.InjOn α s) (J : Ideal R) (P' : Ideal R') (hP' : P' = maximalIdeal R')
    (σ : AssocGraded (maximalIdeal R) →+* AssocGraded P')
    (hσ : ∀ (n : ℕ) (a : R) (ha : a ∈ maximalIdeal R ^ n) (ha' : α a ∈ P' ^ n),
      σ (AssocGraded.mk _ n a ha) = AssocGraded.mk P' n (α a) ha')
    (hord : ∀ a : R, Ideal.ordElem (maximalIdeal R') (α a) = Ideal.ordElem (maximalIdeal R) a)
    (hσJ : Ideal.map σ (grIdeal (maximalIdeal R) J) = grIdeal P' (J.map α)) (i : ℕ+) :
    nuI R J i = nuI R' (J.map α) i := by
  subst hP'
  classical
  let _ : Field (R ⧸ maximalIdeal R) := Ideal.Quotient.field _
  let _ : Field (R' ⧸ maximalIdeal R') := Ideal.Quotient.field _
  have hMM : ∀ a ∈ maximalIdeal R, α a ∈ maximalIdeal R' := fun a ha => map_nonunit α a ha
  have hαn : ∀ (n : ℕ) (a : R), a ∈ maximalIdeal R ^ n → α a ∈ maximalIdeal R' ^ n := by
    intro n a ha
    have h1 : α a ∈ ((maximalIdeal R) ^ n).map α := Ideal.mem_map_of_mem α ha
    rw [Ideal.map_pow] at h1
    exact Ideal.pow_right_mono (Ideal.map_le_iff_le_comap.mpr hMM) n h1
  -- purity: `σ x ∈ σ(𝔞) gr_{M'}(R')` implies `x ∈ 𝔞` (the Remark of p. 238)
  have hpure : ∀ (𝔞 : Ideal (AssocGraded (maximalIdeal R))) (x : AssocGraded (maximalIdeal R)),
      σ x ∈ Ideal.map σ 𝔞 → x ∈ 𝔞 := fun 𝔞 x hx =>
    mem_of_map_mem_map_of_gradedMap α s hs hs' hinj σ hσ 𝔞 x hx
  -- "We have a system of elements `(f₁, …, f_m)` of `J` such that: if `φ_j` is the initial form of
  -- `f_j` in `gr_M(R)`, then the system `(φ₁, …, φ_m)` possesses the properties (i), (ii), (iii)
  -- of Lemma 1": a standard base of `J`
  obtain ⟨m, f, hfJ, hJφ, ⟨d, hd, h₂⟩, h₁, h₃⟩ := exists_isStandardBase_lift J
  let φ : Fin m → AssocGraded (maximalIdeal R) := fun j => initialForm (maximalIdeal R) (f j)
  have hJφ : ∀ j, φ j ∈ grIdeal (maximalIdeal R) J := hJφ
  have hd : ∀ j, φ j ∈ AssocGraded.homogeneous (maximalIdeal R) (d j) := hd
  have h₁ : grIdeal (maximalIdeal R) J = Ideal.span (Set.range φ) := h₁
  have h₃ : ∀ i : Fin m, φ i ∉ Ideal.span (Set.range fun j : Fin i => φ (Fin.castLE i.2.le j)) :=
    h₃
  -- "We can easily see that `σ̄(φ_j)` is the initial form of `α(f_j)` in `gr_{M'}(R')`"
  have hψinit : ∀ j, σ (φ j) = initialForm (maximalIdeal R') (α (f j)) := fun j =>
    initialForm_map_of_ordElem_eq α _ _ σ hσ (f j) (hord (f j))
  have hψJ : ∀ j, σ (φ j) ∈ grIdeal (maximalIdeal R') (J.map α) := fun j => by
    rw [hψinit j]
    exact Ideal.subset_span ⟨α (f j), Ideal.mem_map_of_mem α (hfJ j), rfl⟩
  have hψd : ∀ j, σ (φ j) ∈ AssocGraded.homogeneous (maximalIdeal R') (d j) := fun j => by
    obtain ⟨y, hy, hyφ⟩ := exists_mk_eq_of_mem_homogeneous _ (hd j)
    rw [← hyφ, hσ _ _ hy (hαn _ _ hy)]
    exact AssocGraded.mk_mem_homogeneous _ _
  have hψ₁ : grIdeal (maximalIdeal R') (J.map α) = Ideal.span (Set.range fun j => σ (φ j)) := by
    rw [← hσJ, h₁, Ideal.map_span, ← Set.range_comp]
    rfl
  have hψ₃ : ∀ i : Fin m, σ (φ i) ∉ Ideal.span (Set.range fun j : Fin i =>
      σ (φ (Fin.castLE i.2.le j))) := by
    intro i hmem
    refine h₃ i (hpure _ _ ?_)
    rw [Ideal.map_span, ← Set.range_comp]
    exact hmem
  obtain ⟨hA, hB⟩ := nuI_eq_of_lemma1_properties R J φ hJφ d hd h₁ h₂ h₃
  obtain ⟨hA', hB'⟩ := nuI_eq_of_lemma1_properties R' (J.map α) (fun j => σ (φ j)) hψJ d hψd
    hψ₁ h₂ hψ₃
  by_cases hi : (i : ℕ) ≤ m
  · have hk : (i : ℕ) - 1 < m := by have := i.pos; omega
    have hik : (⟨((⟨(i : ℕ) - 1, hk⟩ : Fin m) : ℕ) + 1, Nat.succ_pos _⟩ : ℕ+) = i :=
      PNat.eq (by simp only [PNat.mk_coe]; have := i.pos; omega)
    rw [← hik, hA, hA']
  · rw [hB i (by omega), hB' i (by omega)]

/-- Corollary to Lemma 2, p. 207: "Let `α : R → R'` be a local homomorphism of regular local
rings which transforms a regular system of parameters of `R` into such a system of parameters
of `R'`. Let `J` be an ideal in `R` and `J'` the ideal in `R'` generated by `α(J)`. Then we have
`ν^{(i)}(J) = ν^{(i)}(J')` for all `i`."

Deviation from the paper (proof corrected): the paper says "(i) and (ii) are clear from the
canonical isomorphism `φ : gr_M(R) ⊗_{R/M} R'/M' → gr_{M'}(R')`, and (iii) is clear from the
fact that `σ̄(gr_M(J, R))` generates `gr_{M'}(J', R')`"; the two justifications are
interchanged.  The proof below obtains (i) from Lemma 2 (generation) and (iii) from the purity of
the coefficient extension `k[X] → k'[X]` (the concrete form of `φ`, `nuI_eq_of_gradedMap`).
Otherwise it is the printed one: a standard base `(f_j)` of `J` (`exists_isStandardBase_lift`), the
`σ̄(φ_j)` are the initial forms of the `α(f_j)` ("we can easily see",
`initialForm_map_of_mapsRSOP`, proved in `nuI_eq_of_gradedMap`), and Lemma 1 is applied to `J` and
`J'`; the flatness of `R'` is `RingHom.MapsRSOP.flat`. -/
@[blueprint "cor:III.lem2"
  (statement := /-- Let $\alpha\colon R\to R'$ be a local homomorphism of regular local rings
    which transforms a regular system of parameters of $R$ into such a system of parameters
    of $R'$ (\cref{def:III.rsop-map}). Let $J$ be an ideal in $R$ and $J'$ the ideal in $R'$
    generated by $\alpha(J)$. Then we have $\nu^{(i)}(J)=\nu^{(i)}(J')$ for all $i$
    (\cref{def:III.1}). (Corollary to Lemma 2, p.~207.) -/)
  (proof := /-- Let $M$ (resp.\ $M'$) denote the maximal ideal of $R$ (resp.\ $R'$). The
    local homomorphism $\alpha$ induces a canonical homomorphism
    $\bar\sigma\colon\operatorname{gr}_M(R)\to\operatorname{gr}_{M'}(R')$
    (\cref{def:III.1-graded-map}). The assumption on $\alpha$ implies that $R'$ is flat over
    $R$. Therefore $\bar\sigma(\operatorname{gr}_M(J,R))$ generates the ideal
    $\operatorname{gr}_{M'}(J',R')$ (\cref{lem:III.2}). We have a system of elements
    $(f_1,\dots,f_m)$ of $J$ such that: if $\varphi_j$ is the initial form of $f_j$ in
    $\operatorname{gr}_M(R)$ for $1\le j\le m$, then the system
    $(\varphi_1,\varphi_2,\dots,\varphi_m)$ possesses the properties (i), (ii), and (iii) of
    Lemma~1 (\cref{lem:III.1}). We can easily see that $\bar\sigma(\varphi_j)$ is the initial
    form of $\alpha(f_j)$ in $\operatorname{gr}_{M'}(R')$ for $1\le j\le m$. Then we claim
    that the system $(\bar\sigma(\varphi_1),\dots,\bar\sigma(\varphi_m))$ possesses the
    properties (i), (ii), and (iii) of Lemma~1 for $\operatorname{gr}_{M'}(J',R')$, too. In
    fact, (i) and (ii) are clear from the canonical isomorphism
    $\varphi\colon\operatorname{gr}_M(R)\otimes_{R/M}R'/M'\to\operatorname{gr}_{M'}(R')$, and
    (iii) is clear from the fact that $\bar\sigma(\operatorname{gr}_M(J,R))$ generates
    $\operatorname{gr}_{M'}(J',R')$. [End of the paper's proof; the assertion then follows
    from Lemma~1 applied to $J$ and to $J'$.]

    \textbf{Correction of the paper (proof).} The two justifications are interchanged: (i)
    follows from the fact that $\bar\sigma(\operatorname{gr}_M(J,R))$ generates
    $\operatorname{gr}_{M'}(J',R')$ (Lemma~2), while (iii) needs the isomorphism $\varphi$
    (purity of the coefficient extension $k[X]\to k'[X]$, $k=R/M$, $k'=R'/M'$); generation
    alone does not exclude
    $\bar\sigma(\varphi_i)\in(\bar\sigma(\varphi_1),\dots,\bar\sigma(\varphi_{i-1}))$. The
    formal proof argues in this corrected way, with the initial forms of a standard base
    $(f_j)$ of $J$ as printed (``we can easily see'' that $\bar\sigma(\varphi_j)$ is the initial
    form of $\alpha(f_j)$ is proved: the order is preserved, $\alpha^{-1}(M'^k)=M^k$), and
    identifies $\operatorname{gr}_M(R)=k[X]$, $\operatorname{gr}_{M'}(R')=k'[X]$ by corresponding
    regular systems of parameters. -/)
  (latexEnv := "corollary")]
theorem nuI_map_eq_of_mapsRSOP (α : R →+* R') [IsLocalHom α] (hα : RingHom.MapsRSOP α)
    (J : Ideal R) (i : ℕ+) : nuI R J i = nuI R' (J.map α) i := by
  classical
  let _ := α.toAlgebra
  have hflat : Module.Flat R R' := RingHom.MapsRSOP.flat hα
  have hord := ordElem_map_of_mapsRSOP α hα
  obtain ⟨s, hs, hs', hinj⟩ := hα
  have hM : (maximalIdeal R).map α = maximalIdeal R' := by
    have h := hs'.1
    rw [Finset.coe_image] at h
    rw [← hs.1, Ideal.map_span, h]
  have hjac : (maximalIdeal R).map (algebraMap R R') ≤ Ring.jacobson R' := by
    rw [ringJacobson_eq_maximalIdeal]
    exact hM.le
  exact nuI_eq_of_gradedMap α s hs hs' hinj J _ hM (AssocGraded.map α (maximalIdeal R))
    (fun n a ha _ => AssocGraded.map_mk α _ n a ha) hord
    (map_grIdeal_eq_grIdeal_map_of_flat R R' (maximalIdeal R) J hjac) i

/-- The Corollary to Lemma 2 for the sequences: `ν*(J) = ν*(J')` (Definition 2). -/
theorem nuStar_map_eq_of_mapsRSOP (α : R →+* R') [IsLocalHom α] (hα : RingHom.MapsRSOP α)
    (J : Ideal R) : nuStar R J = nuStar R' (J.map α) := by
  simp only [nuStar]
  congr 1
  funext i
  exact nuI_map_eq_of_mapsRSOP α hα J i

end CorLemma2

/-! ### Lemma 3 and its Corollary (pp. 207–208) -/

section Lemma3

variable (R : Type u) [CommRing R] [IsRegularLocalRing R]

/-- Lemma 3, p. 208 (second half of the proof): "if `J₂ ⊆ J₁ + Mⁿ` for a certain `n`, then
`gr_M(J₁, R) = gr_M(J₂, R)` implies `J₂ ⊆ J₁ + Mⁿ⁺¹`", used degree by degree: if `J₁ ⊆ J₂` and
`gr^μ_M(J₂, R) ⊆ gr^μ_M(J₁, R)` for all `μ < ν`, then `J₂ ⊆ J₁ + Mᵛ`. -/
private theorem le_sup_pow_of_grIdeal_eq {J₁ J₂ : Ideal R} (h : J₁ ≤ J₂) {ν : ℕ}
    (hgr : ∀ μ < ν, ∀ χ ∈ AssocGraded.homogeneous (maximalIdeal R) μ,
      χ ∈ grIdeal (maximalIdeal R) J₂ → χ ∈ grIdeal (maximalIdeal R) J₁) :
    J₂ ≤ J₁ ⊔ maximalIdeal R ^ ν := by
  -- `J₂ ⊆ J₁ + Mⁿ` for all `n ≤ ν`
  have key : ∀ n ≤ ν, ∀ g ∈ J₂, g ∈ J₁ ⊔ maximalIdeal R ^ n := by
    intro n
    induction n with
    | zero => intro _ g _; simp
    | succ n ih =>
      intro hn g hg
      obtain ⟨f₁, hf₁, r, hr, rfl⟩ := Submodule.mem_sup.mp (ih (by omega) g hg)
      have hrJ : r ∈ J₂ := by simpa using sub_mem hg (h hf₁)
      have hmem : AssocGraded.mk (maximalIdeal R) n r hr ∈ grIdeal (maximalIdeal R) J₁ :=
        hgr n (by omega) _ (AssocGraded.mk_mem_homogeneous _ hr)
          (mk_mem_grIdeal (maximalIdeal R) hrJ hr)
      obtain ⟨a, ⟨haJ, -⟩, ha, hmk⟩ := (grIdeal_homogeneous_eq (maximalIdeal R) J₁ n _
        (AssocGraded.mk_mem_homogeneous _ hr)).mp hmem
      have hra : r - a ∈ maximalIdeal R ^ (n + 1) := by
        rw [← AssocGraded.mk_eq_zero_iff (maximalIdeal R) (sub_mem hr ha)]
        have : AssocGraded.mk (maximalIdeal R) n (r - a) (sub_mem hr ha) =
            AssocGraded.mk (maximalIdeal R) n r hr - AssocGraded.mk (maximalIdeal R) n a ha :=
          map_sub (AssocGraded.mkLinear (maximalIdeal R) n) ⟨r, hr⟩ ⟨a, ha⟩
        rw [this, hmk, sub_self]
      have : f₁ + r = (f₁ + a) + (r - a) := by ring
      rw [this]
      exact Submodule.add_mem_sup (add_mem hf₁ haJ) hra
  exact fun g hg => key ν le_rfl g hg

/-- Krull: if `J₁ ⊆ J₂` and `gr_M(J₁, R) = gr_M(J₂, R)` then `J₁ = J₂` (as in the second half
of the proof of Lemma 3). -/
private theorem eq_of_grIdeal_eq {J₁ J₂ : Ideal R} (h : J₁ ≤ J₂)
    (hgr : grIdeal (maximalIdeal R) J₁ = grIdeal (maximalIdeal R) J₂) : J₁ = J₂ := by
  refine le_antisymm h fun g hg => ?_
  -- `J₂ ⊆ J₁ + Mⁿ` for all `n`
  have key : ∀ n : ℕ, ∀ g ∈ J₂, g ∈ J₁ ⊔ maximalIdeal R ^ n := fun n =>
    le_sup_pow_of_grIdeal_eq R h fun μ _ χ _ hχ₂ => by rw [hgr]; exact hχ₂
  -- Krull's intersection theorem for the `R`-module `R/J₁`
  have hK := Ideal.iInf_pow_smul_eq_bot_of_isLocalRing (M := R ⧸ J₁) (maximalIdeal R)
    (maximalIdeal.isMaximal R).ne_top
  have hmem : Ideal.Quotient.mk J₁ g ∈
      (⨅ i : ℕ, maximalIdeal R ^ i • ⊤ : Submodule R (R ⧸ J₁)) := by
    rw [Submodule.mem_iInf]
    intro i
    obtain ⟨f₁, hf₁, r, hr, hfr⟩ := Submodule.mem_sup.mp (key i g hg)
    rw [← hfr, map_add, Ideal.Quotient.eq_zero_iff_mem.mpr hf₁, zero_add]
    have : Ideal.Quotient.mk J₁ r = r • (1 : R ⧸ J₁) := by
      rw [Algebra.smul_def, mul_one]
      rfl
    rw [this]
    exact Submodule.smul_mem_smul hr Submodule.mem_top
  rw [hK, Submodule.mem_bot, Ideal.Quotient.eq_zero_iff_mem] at hmem
  exact hmem

/-- For non-decreasing `d`, `d i < μ ↔ i < #{j | d j < μ}`. -/
private theorem lt_iff_lt_card {n : ℕ} (d : Fin n → ℕ) (hd : Monotone d) (i : Fin n)
    (μ : ℕ) : d i < μ ↔ (i : ℕ) < (Finset.univ.filter fun j => d j < μ).card := by
  constructor
  · intro h
    have hsub : Finset.Iic i ⊆ Finset.univ.filter fun j => d j < μ := fun j hj =>
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, lt_of_le_of_lt (hd (Finset.mem_Iic.mp hj)) h⟩
    have := Finset.card_le_card hsub
    rw [Fin.card_Iic] at this
    omega
  · intro h
    by_contra hc
    have hsub : (Finset.univ.filter fun j => d j < μ) ⊆ Finset.Iio i := fun j hj => by
      rw [Finset.mem_Iio]
      by_contra hji
      have := hd (not_lt.mp hji)
      rw [Finset.mem_filter] at hj
      omega
    have := Finset.card_le_card hsub
    rw [Fin.card_Iio] at this
    omega

/-- The system `(χ₁, …, χ_k, ξ)`: `χ` with `ξ` appended. -/
private def snocFun {α : Type*} {k : ℕ} (χ : Fin k → α) (ξ : α) : Fin (k + 1) → α :=
  fun i => if h : (i : ℕ) < k then χ ⟨i, h⟩ else ξ

private theorem snocFun_castLE {α : Type*} {k : ℕ} (χ : Fin k → α) (ξ : α) (i : Fin k) :
    snocFun χ ξ (Fin.castLE (Nat.le_succ k) i) = χ i := by
  simp [snocFun]

private theorem snocFun_last {α : Type*} {k : ℕ} (χ : Fin k → α) (ξ : α) :
    snocFun χ ξ ⟨k, Nat.lt_succ_self k⟩ = ξ := by
  simp [snocFun]

/-- A relation holding between the corresponding terms of two systems holds for the appended
systems if it holds for the appended terms. -/
private theorem snocFun_pair {α β : Type*} {k : ℕ} (Q : α → β → Prop) (χ : Fin k → α)
    (e : Fin k → β) (ξ : α) (μ : β) (hχ : ∀ i, Q (χ i) (e i)) (hξ : Q ξ μ) :
    ∀ i, Q (snocFun χ ξ i) (snocFun e μ i) := by
  intro i
  by_cases h : (i : ℕ) < k
  · simp only [snocFun, dite_eq_left h]
    exact hχ _
  · simp only [snocFun, dite_eq_right h]
    exact hξ

private theorem monotone_snocFun {k : ℕ} (e : Fin k → ℕ) (μ : ℕ) (he : Monotone e)
    (hes : ∀ i, e i ≤ μ) : Monotone (snocFun e μ) := by
  intro a b hab
  have hab' : (a : ℕ) ≤ b := hab
  by_cases hb : (b : ℕ) < k
  · have ha : (a : ℕ) < k := lt_of_le_of_lt hab' hb
    simp only [snocFun, dite_eq_left ha, dite_eq_left hb]
    exact he hab'
  · simp only [snocFun, dite_eq_right hb]
    by_cases ha : (a : ℕ) < k
    · simp only [dite_eq_left ha]
      exact hes _
    · simp only [dite_eq_right ha, le_refl]

/-- Property (iii) of Lemma 1 for the system `χ` with `ξ` appended, if `ξ` is not in the ideal
generated by `χ`. -/
private theorem irredundant_snocFun {k : ℕ} (χ : Fin k → AssocGraded (maximalIdeal R))
    (ξ : AssocGraded (maximalIdeal R))
    (hirr : ∀ i : Fin k, χ i ∉ Ideal.span (Set.range fun j : Fin i => χ (Fin.castLE i.2.le j)))
    (hξ : ξ ∉ Ideal.span (Set.range χ)) :
    ∀ i : Fin (k + 1), snocFun χ ξ i ∉
      Ideal.span (Set.range fun j : Fin i => snocFun χ ξ (Fin.castLE i.2.le j)) := by
  intro i hmem
  by_cases h : (i : ℕ) < k
  · rw [show snocFun χ ξ i = χ ⟨i, h⟩ by simp [snocFun, h]] at hmem
    refine hirr ⟨i, h⟩ ?_
    refine (Ideal.span_mono ?_) hmem
    rintro _ ⟨j, rfl⟩
    exact ⟨j, by simp [snocFun, lt_trans j.2 h]; rfl⟩
  · rw [show snocFun χ ξ i = ξ by simp [snocFun, h]] at hmem
    refine hξ ?_
    refine (Ideal.span_mono ?_) hmem
    rintro _ ⟨j, rfl⟩
    have hjk : (j : ℕ) < k := lt_of_lt_of_le j.2 (by omega)
    exact ⟨⟨j, hjk⟩, by simp [snocFun, hjk]⟩

/-- A homogeneous element of `gr_M(J, R)` outside a given ideal exists unless `gr_M(J, R)` is
contained in it (`gr_M(J, R)` is generated by the homogeneous initial forms of elements of `J`). -/
private theorem exists_homogeneous_mem_not_mem (J : Ideal R)
    {𝔟 : Ideal (AssocGraded (maximalIdeal R))} (h : ¬ grIdeal (maximalIdeal R) J ≤ 𝔟) :
    ∃ μ, ∃ ξ, ξ ∈ AssocGraded.homogeneous (maximalIdeal R) μ ∧
      ξ ∈ grIdeal (maximalIdeal R) J ∧ ξ ∉ 𝔟 := by
  by_contra hc
  push Not at hc
  apply h
  rw [grIdeal, Ideal.span_le]
  rintro _ ⟨f, hf, rfl⟩
  obtain ⟨d, hd⟩ := exists_initialForm_mem_homogeneous (maximalIdeal R) f
  exact hc d _ hd (Ideal.subset_span ⟨f, hf, rfl⟩)

/-- Lemma 3, p. 208: "`(φ₁, …, φ_j, ψ)` can be extended to a system of elements of
`gr_M(J₂, R)` which has the properties (i), (ii), and (iii) of Lemma 1."  The paper states the
extendability without argument.  Let `χ` be a system of homogeneous elements of `gr_M(J, R)`
with non-decreasing degrees `e ≤ s`, with (iii), and such that every homogeneous element of
`gr_M(J, R)` of degree `< s` lies in `(χ) gr_M(R)`.  Then `χ` is the beginning of a system
`χ'` of homogeneous elements of `gr_M(J, R)` with the properties (i), (ii), (iii): repeatedly
append a homogeneous element of `gr_M(J, R)` of smallest degree which is not in the ideal
generated by the system so far (its degree is `≥ s`, so (ii) is kept, and it keeps the
hypothesis on the degrees below it); the process stops since `gr_M(R)` is noetherian. -/
private theorem exists_extension_isMinimalGradedGenerators (J : Ideal R) :
    ∀ {k : ℕ} (χ : Fin k → AssocGraded (maximalIdeal R)) (e : Fin k → ℕ),
      (∀ i, χ i ∈ grIdeal (maximalIdeal R) J) →
      (∀ i, χ i ∈ AssocGraded.homogeneous (maximalIdeal R) (e i)) → Monotone e →
      (∀ i : Fin k, χ i ∉ Ideal.span (Set.range fun j : Fin i => χ (Fin.castLE i.2.le j))) →
      ∀ s : ℕ, (∀ i, e i ≤ s) →
      (∀ μ < s, ∀ ξ ∈ AssocGraded.homogeneous (maximalIdeal R) μ,
        ξ ∈ grIdeal (maximalIdeal R) J → ξ ∈ Ideal.span (Set.range χ)) →
      ∃ (k' : ℕ) (hk : k ≤ k') (χ' : Fin k' → AssocGraded (maximalIdeal R)) (e' : Fin k' → ℕ),
        (∀ i : Fin k, χ' (Fin.castLE hk i) = χ i) ∧ (∀ i : Fin k, e' (Fin.castLE hk i) = e i) ∧
        (∀ i, χ' i ∈ grIdeal (maximalIdeal R) J) ∧
        (∀ i, χ' i ∈ AssocGraded.homogeneous (maximalIdeal R) (e' i)) ∧ Monotone e' ∧
        grIdeal (maximalIdeal R) J = Ideal.span (Set.range χ') ∧
        ∀ i : Fin k', χ' i ∉
          Ideal.span (Set.range fun j : Fin i => χ' (Fin.castLE i.2.le j)) := by
  classical
  have : IsNoetherianRing (AssocGraded (maximalIdeal R)) :=
    inferInstanceAs (IsNoetherianRing (reesAlgebra (maximalIdeal R) ⧸ _))
  -- induction on the ideal generated by the system, which strictly increases at each step
  suffices h : ∀ 𝔟 : Ideal (AssocGraded (maximalIdeal R)), ∀ {k : ℕ}
      (χ : Fin k → AssocGraded (maximalIdeal R)) (e : Fin k → ℕ),
      (∀ i, χ i ∈ grIdeal (maximalIdeal R) J) →
      (∀ i, χ i ∈ AssocGraded.homogeneous (maximalIdeal R) (e i)) → Monotone e →
      (∀ i : Fin k, χ i ∉ Ideal.span (Set.range fun j : Fin i => χ (Fin.castLE i.2.le j))) →
      ∀ s : ℕ, (∀ i, e i ≤ s) →
      (∀ μ < s, ∀ ξ ∈ AssocGraded.homogeneous (maximalIdeal R) μ,
        ξ ∈ grIdeal (maximalIdeal R) J → ξ ∈ Ideal.span (Set.range χ)) →
      Ideal.span (Set.range χ) = 𝔟 →
      ∃ (k' : ℕ) (hk : k ≤ k') (χ' : Fin k' → AssocGraded (maximalIdeal R)) (e' : Fin k' → ℕ),
        (∀ i : Fin k, χ' (Fin.castLE hk i) = χ i) ∧ (∀ i : Fin k, e' (Fin.castLE hk i) = e i) ∧
        (∀ i, χ' i ∈ grIdeal (maximalIdeal R) J) ∧
        (∀ i, χ' i ∈ AssocGraded.homogeneous (maximalIdeal R) (e' i)) ∧ Monotone e' ∧
        grIdeal (maximalIdeal R) J = Ideal.span (Set.range χ') ∧
        ∀ i : Fin k', χ' i ∉
          Ideal.span (Set.range fun j : Fin i => χ' (Fin.castLE i.2.le j)) from
    fun {k} χ e hχJ hχe he hirr s hes H => h _ χ e hχJ hχe he hirr s hes H rfl
  intro 𝔟
  induction 𝔟 using WellFoundedGT.induction with
  | _ 𝔟 ih =>
    intro k χ e hχJ hχe he hirr s hes H hspan
    by_cases hle : grIdeal (maximalIdeal R) J ≤ Ideal.span (Set.range χ)
    · -- the system generates `gr_M(J, R)`: property (i)
      exact ⟨k, le_rfl, χ, e, fun i => rfl, fun i => rfl, hχJ, hχe, he,
        le_antisymm hle (Ideal.span_le.mpr (by rintro _ ⟨i, rfl⟩; exact hχJ i)), hirr⟩
    · -- append a homogeneous element of `gr_M(J, R)` of smallest degree not in `(χ)`
      have hex := exists_homogeneous_mem_not_mem R J hle
      obtain ⟨ξ, hξ, hξJ, hξn⟩ := Nat.find_spec hex
      set μ₀ := Nat.find hex with hμ₀
      have hμs : s ≤ μ₀ := by
        by_contra hlt
        exact hξn (H μ₀ (not_le.mp hlt) ξ hξ hξJ)
      have hmin : ∀ μ < μ₀, ∀ ξ' ∈ AssocGraded.homogeneous (maximalIdeal R) μ,
          ξ' ∈ grIdeal (maximalIdeal R) J → ξ' ∈ Ideal.span (Set.range χ) := by
        intro μ hμ ξ' h1 h2
        by_contra h3
        exact Nat.find_min hex hμ ⟨ξ', h1, h2, h3⟩
      have hle₁ : Ideal.span (Set.range χ) ≤ Ideal.span (Set.range (snocFun χ ξ)) :=
        Ideal.span_mono (by
          rintro _ ⟨i, rfl⟩
          exact ⟨Fin.castLE (Nat.le_succ k) i, snocFun_castLE χ ξ i⟩)
      have hξ₁ : ξ ∈ Ideal.span (Set.range (snocFun χ ξ)) :=
        Ideal.subset_span ⟨⟨k, Nat.lt_succ_self k⟩, snocFun_last χ ξ⟩
      have hlt : 𝔟 < Ideal.span (Set.range (snocFun χ ξ)) :=
        hspan ▸ lt_of_le_of_ne hle₁ fun heq => hξn (heq ▸ hξ₁)
      have hes₁ : ∀ i, snocFun e μ₀ i ≤ μ₀ := by
        intro i
        by_cases h : (i : ℕ) < k
        · simp only [snocFun, dite_eq_left h]
          exact (hes _).trans hμs
        · simp only [snocFun, dite_eq_right h, le_refl]
      obtain ⟨k', hk', χ', e', hpre, hepre, h1, h2, h3, h4, h5⟩ := ih _ hlt (snocFun χ ξ)
        (snocFun e μ₀)
        (snocFun_pair (fun x (_ : ℕ) => x ∈ grIdeal (maximalIdeal R) J) χ e ξ μ₀ hχJ hξJ)
        (snocFun_pair (fun x n => x ∈ AssocGraded.homogeneous (maximalIdeal R) n) χ e ξ μ₀ hχe hξ)
        (monotone_snocFun e μ₀ he fun i => (hes i).trans hμs)
        (irredundant_snocFun R χ ξ hirr hξn) μ₀ hes₁
        (fun μ hμ ξ' h1 h2 => hle₁ (hmin μ hμ ξ' h1 h2)) rfl
      exact ⟨k', (Nat.le_succ k).trans hk', χ', e',
        fun i => (hpre (Fin.castLE (Nat.le_succ k) i)).trans (snocFun_castLE χ ξ i),
        fun i => (hepre (Fin.castLE (Nat.le_succ k) i)).trans (snocFun_castLE e μ₀ i),
        h1, h2, h3, h4, h5⟩

/-- The main step of Lemma 3 (p. 208): if `J₁ ⊆ J₂` and `gr_M(J₁, R) ≠ gr_M(J₂, R)`, then
`ν*(J₂) < ν*(J₁)`.  The proof is the printed one:

"Let `(φ₁, …, φ_m)` be a system of elements of `gr_M(J₁, R)` which has the properties (i), (ii),
and (iii) of Lemma 1.  Let `ν_i = ν^{(i)}(J₁)` which is `deg φ_i` for `1 ≤ i ≤ m` and `∞` for
`i > m`.  Let `s` be the smallest integer such that `gr^s_M(J₁, R) ≠ gr^s_M(J₂, R)`.  Let `j` be
the largest integer such that `ν_j ≤ s`.  Then `gr^μ_M(J₂, R) = gr^μ_M(J₁, R) =
(φ₁, …, φ_j) gr_M(R) ∩ gr^μ_M(R)` for all `μ < s`, and `gr^s_M(J₂, R) ⊋ gr^s_M(J₁, R) =
(φ₁, …, φ_j) gr_M(R) ∩ gr^s_M(R)`.  Therefore, we have `ψ ∈ gr^s_M(J₂, R)` such that
`(φ₁, …, φ_j, ψ)` can be extended to a system of elements of `gr_M(J₂, R)` which has the
properties (i), (ii), and (iii) of Lemma 1.  Thus we have `ν^{(i)}(J₂) = ν^{(i)}(J₁)` for
`i ≤ j` and `ν^{(j+1)}(J₂) = s < ν^{(j+1)}(J₁)`, so that `ν₂* < ν₁*`."

(Indices are `0`-based: the paper's `φ_i` is `φ (i - 1)`, and `j = #{i | ν_i ≤ s}`.) -/
private theorem nuStar_lt {J₁ J₂ : Ideal R}
    (hI : grIdeal (maximalIdeal R) J₁ ≤ grIdeal (maximalIdeal R) J₂)
    (hne : grIdeal (maximalIdeal R) J₁ ≠ grIdeal (maximalIdeal R) J₂) :
    nuStar R J₂ < nuStar R J₁ := by
  classical
  -- "Let `(φ₁, …, φ_m)` be a system of elements of `gr_M(J₁, R)` which has the properties (i),
  -- (ii), and (iii) of Lemma 1."
  obtain ⟨m, φ, d, hJφ, hd, h₁, h₂, h₃⟩ := exists_isMinimalGradedGenerators (R := R) J₁
  -- "Let `ν_i = ν^{(i)}(J₁)` which is `deg φ_i` for `1 ≤ i ≤ m` and `∞` for `i > m`."  (Lemma 1)
  obtain ⟨hν, hν'⟩ := nuI_eq_of_lemma1_properties R J₁ φ hJφ d hd h₁ h₂ h₃
  -- "Let `s` be the smallest integer such that `gr^s_M(J₁, R) ≠ gr^s_M(J₂, R)`."
  have hex : ∃ μ, ∃ ξ, ξ ∈ AssocGraded.homogeneous (maximalIdeal R) μ ∧
      ξ ∈ grIdeal (maximalIdeal R) J₂ ∧ ξ ∉ grIdeal (maximalIdeal R) J₁ :=
    exists_homogeneous_mem_not_mem R J₂ fun h => hne (le_antisymm hI h)
  obtain ⟨ψ, hψ, hψ₂, hψ₁⟩ := Nat.find_spec hex
  set s := Nat.find hex with hs
  have hmin : ∀ μ < s, ∀ ξ ∈ AssocGraded.homogeneous (maximalIdeal R) μ,
      ξ ∈ grIdeal (maximalIdeal R) J₂ → ξ ∈ grIdeal (maximalIdeal R) J₁ := by
    intro μ hμ ξ hξ hξ₂
    by_contra hξ₁
    exact Nat.find_min hex hμ ⟨ξ, hξ, hξ₂, hξ₁⟩
  -- "Let `j` be the largest integer such that `ν_j ≤ s`": `φ₁, …, φ_j` are the `φ_i` of degree
  -- `≤ s`
  set j := (Finset.univ.filter fun i : Fin m => d i < s + 1).card with hj
  have hjm : j ≤ m :=
    (Finset.card_filter_le _ _).trans (by rw [Finset.card_univ, Fintype.card_fin])
  have hlow : ∀ i : Fin m, d i < s + 1 ↔ (i : ℕ) < j := fun i => lt_iff_lt_card d h₂ i (s + 1)
  -- "`gr^μ_M(J₁, R) = (φ₁, …, φ_j) gr_M(R) ∩ gr^μ_M(R)` for all `μ ≤ s`" (`(φ₁, …, φ_j)` has the
  -- property of Definition 1 up to `s + 1`)
  have hφj : IsNuSystem R J₁ (s + 1) j (fun i : Fin j => φ (Fin.castLE hjm i)) :=
    isNuSystem_prefix R J₁ φ hJφ d hd h₁ hjm fun i hi =>
      not_lt.mp fun h => absurd ((hlow i).mp h) (not_lt.mpr hi)
  -- "`gr^s_M(J₂, R) ⊋ gr^s_M(J₁, R)`": `ψ ∉ (φ₁, …, φ_j) gr_M(R)`
  have hψφ : ψ ∉ Ideal.span (Set.range fun i : Fin j => φ (Fin.castLE hjm i)) := fun hmem =>
    hψ₁ ((hφj.2 s (Nat.lt_succ_self s) ψ hψ).mp hmem)
  -- "Therefore, we have `ψ ∈ gr^s_M(J₂, R)` such that `(φ₁, …, φ_j, ψ)` can be extended to a
  -- system of elements of `gr_M(J₂, R)` which has the properties (i), (ii), and (iii)"
  have hdj : ∀ i : Fin j, d (Fin.castLE hjm i) ≤ s := fun i =>
    Nat.lt_succ_iff.mp ((hlow _).mpr i.2)
  let χ₀ : Fin j → AssocGraded (maximalIdeal R) := fun i => φ (Fin.castLE hjm i)
  let e₀ : Fin j → ℕ := fun i => d (Fin.castLE hjm i)
  obtain ⟨k', hk', χ', e', hpre, hepre, hχJ, hχe, hχm, hχspan, hχirr⟩ :=
    exists_extension_isMinimalGradedGenerators R J₂ (snocFun χ₀ ψ) (snocFun e₀ s)
      (snocFun_pair (fun x (_ : ℕ) => x ∈ grIdeal (maximalIdeal R) J₂) χ₀ e₀ ψ s
        (fun i => hI (hJφ _)) hψ₂)
      (snocFun_pair (fun x n => x ∈ AssocGraded.homogeneous (maximalIdeal R) n) χ₀ e₀ ψ s
        (fun i => hd _) hψ)
      (monotone_snocFun e₀ s (fun a b hab => h₂ hab) hdj)
      (irredundant_snocFun R χ₀ ψ (fun i => h₃ (Fin.castLE hjm i)) hψφ) s
      (fun i => by
        by_cases h : (i : ℕ) < j
        · simp only [snocFun, dite_eq_left h]
          exact hdj _
        · simp only [snocFun, dite_eq_right h, le_refl])
      (fun μ hμ ξ hξ hξ₂ => by
        refine (Ideal.span_mono ?_) ((hφj.2 μ (lt_trans hμ (Nat.lt_succ_self s)) ξ hξ).mpr
          (hmin μ hμ ξ hξ hξ₂))
        rintro _ ⟨i, rfl⟩
        exact ⟨Fin.castLE (Nat.le_succ j) i, snocFun_castLE χ₀ ψ i⟩)
  -- "Thus we have `ν^{(i)}(J₂) = ν^{(i)}(J₁)` for `i ≤ j` and `ν^{(j+1)}(J₂) = s < ν^{(j+1)}(J₁)`"
  obtain ⟨hν₂, -⟩ := nuI_eq_of_lemma1_properties R J₂ χ' hχJ e' hχe hχspan hχm hχirr
  have hjk : j < k' := lt_of_lt_of_le (Nat.lt_succ_self j) hk'
  have hj₂ : nuI R J₂ ⟨j + 1, Nat.succ_pos _⟩ = s := by
    rw [hν₂ ⟨j, hjk⟩]
    have := hepre ⟨j, Nat.lt_succ_self j⟩
    rw [show (⟨j, hjk⟩ : Fin k') = Fin.castLE hk' ⟨j, Nat.lt_succ_self j⟩ from rfl, this]
    simp [snocFun]
  have hj₁ : (s : ℕ∞) < nuI R J₁ ⟨j + 1, Nat.succ_pos _⟩ := by
    by_cases hjm' : j < m
    · rw [hν ⟨j, hjm'⟩]
      exact_mod_cast not_lt.mp (fun h => absurd ((hlow ⟨j, hjm'⟩).mp h) (lt_irrefl j))
    · rw [hν' ⟨j + 1, Nat.succ_pos _⟩ (by simp only [PNat.mk_coe]; omega)]
      exact ENat.natCast_lt_top _
  -- "so that `ν₂* < ν₁*`"
  refine ⟨⟨j + 1, Nat.succ_pos _⟩, fun p hp => ?_, ?_⟩
  · obtain ⟨i, hi⟩ : ∃ i : ℕ, (p : ℕ) = i + 1 := ⟨(p : ℕ) - 1, by have := p.pos; omega⟩
    have hij : i < j := by
      have : (p : ℕ) < j + 1 := hp
      omega
    have hpeq : p = ⟨i + 1, Nat.succ_pos _⟩ := PNat.eq hi
    subst hpeq
    show nuI R J₂ _ = nuI R J₁ _
    rw [hν ⟨i, lt_of_lt_of_le hij hjm⟩, hν₂ ⟨i, hij.trans hjk⟩]
    have := hepre ⟨i, hij.trans (Nat.lt_succ_self j)⟩
    rw [show (⟨i, hij.trans hjk⟩ : Fin k') =
      Fin.castLE hk' ⟨i, hij.trans (Nat.lt_succ_self j)⟩ from rfl, this]
    simp [snocFun, hij]
    rfl
  · show nuI R J₂ _ < nuI R J₁ _
    rw [hj₂]
    exact hj₁

/-- Lemma 3, p. 207: "Let `J₁` and `J₂` be two ideals in a regular local ring `R` such that
`J₁ ⊆ J₂`. Let `ν_i* = {ν^{(j)}(J_i)}_{j ∈ ℤ⁺}` for `i = 1, 2`. Then we have `ν₁* ≥ ν₂*`.
Moreover, `ν₁* = ν₂*` if and only if `J₁ = J₂`."  (The smaller ideal has the larger `ν*`: the
proof shows `gr_M(J₁, R) ⊆ gr_M(J₂, R)` and derives `ν₂* < ν₁*` when they differ.)

The proof is the printed one: `nuStar_lt` takes a Lemma-1 system `(φ_i)` of `J₁`, the smallest
degree `s` with `gr^s_M(J₁, R) ≠ gr^s_M(J₂, R)`, the largest `j` with `ν_j ≤ s`, an element
`ψ ∈ gr^s_M(J₂, R) ∖ gr^s_M(J₁, R)`, and extends `(φ₁, …, φ_j, ψ)` to a system with the
properties of Lemma 1 for `J₂` (`exists_extension_isMinimalGradedGenerators`, which the paper
asserts without proof: it is proved here by appending, one at a time, a homogeneous element of
smallest degree outside the ideal generated so far).  The second half (Krull) follows the paper
(`eq_of_grIdeal_eq`). -/
@[blueprint "lem:III.3"
  (statement := /-- Let $J_1$ and $J_2$ be two ideals in a regular local ring $R$ such that
    $J_1\subseteq J_2$. Let $\nu_i^*=\{\nu^{(j)}(J_i)\}_{j\in\mathbb Z^+}$ for $i=1,2$
    (\cref{def:III.2}). Then we have $\nu_1^*\ge\nu_2^*$. Moreover, $\nu_1^*=\nu_2^*$ if and
    only if $J_1=J_2$. (Lemma 3, p.~207.) -/)
  (proof := /-- It is clear that $\operatorname{gr}_M(J_1,R)\subseteq\operatorname{gr}_M(J_2,R)$.
    If $\operatorname{gr}_M(J_1,R)=\operatorname{gr}_M(J_2,R)$, then $\nu_1^*=\nu_2^*$.
    Suppose $\operatorname{gr}_M(J_1,R)\ne\operatorname{gr}_M(J_2,R)$. Let
    $(\varphi_1,\dots,\varphi_m)$ be a system of elements of $\operatorname{gr}_M(J_1,R)$
    which has the properties (i), (ii), and (iii) of Lemma~1 (\cref{lem:III.1}). Let
    $\nu_i=\nu^{(i)}(J_1)$, which is $\deg\varphi_i$ for $1\le i\le m$ and $\infty$ for
    $i>m$. Let $s$ be the smallest integer such that
    $\operatorname{gr}^s_M(J_1,R)\ne\operatorname{gr}^s_M(J_2,R)$. Let $j$ be the largest
    integer such that $\nu_j\le s$. Then
    $\operatorname{gr}^\mu_M(J_2,R)=\operatorname{gr}^\mu_M(J_1,R)
    =(\varphi_1,\dots,\varphi_j)\operatorname{gr}_M(R)\cap\operatorname{gr}^\mu_M(R)$ for
    all $\mu<s$, and
    $\operatorname{gr}^s_M(J_2,R)\supsetneq\operatorname{gr}^s_M(J_1,R)
    =(\varphi_1,\dots,\varphi_j)\operatorname{gr}_M(R)\cap\operatorname{gr}^s_M(R)$.
    Therefore, we have $\psi\in\operatorname{gr}^s_M(J_2,R)$ such that
    $(\varphi_1,\dots,\varphi_j,\psi)$ can be extended to a system of elements of
    $\operatorname{gr}_M(J_2,R)$ which has the properties (i), (ii), and (iii) of Lemma~1.
    Thus we have $\nu^{(i)}(J_2)=\nu^{(i)}(J_1)$ for $i\le j$ and
    $\nu^{(j+1)}(J_2)=s<\nu^{(j+1)}(J_1)$, so that $\nu_2^*<\nu_1^*$. In particular,
    $\nu_1^*=\nu_2^*$ implies $\operatorname{gr}_M(J_1,R)=\operatorname{gr}_M(J_2,R)$. We
    then claim $J_1=J_2$. It is sufficient to show that $J_2\subseteq J_1+M^n$ for all
    positive integers $n$ [by Krull's intersection theorem]. For this, we have only to prove
    that, if $J_2\subseteq J_1+M^n$ for a certain $n$, then
    $\operatorname{gr}_M(J_1,R)=\operatorname{gr}_M(J_2,R)$ implies
    $J_2\subseteq J_1+M^{n+1}$. Let $g$ be any element of $J_2$. Then we have $f_1\in J_1$
    such that $g-f_1\in M^n$. Therefore to prove that $g\in J_1+M^{n+1}$, we may assume that
    $\nu_M(g)=n$. Let $\psi$ be the initial form of $g$ in $\operatorname{gr}_M(R)$, which is
    of degree $n$. Then $\psi\in\operatorname{gr}^n_M(J_2,R)=\operatorname{gr}^n_M(J_1,R)$.
    Hence there exists $f\in J_1$ such that $\psi$ is the initial form of $f$ in
    $\operatorname{gr}_M(R)$. Clearly $g-f\in M^{n+1}$. Thus $J_2\subseteq J_1+M^{n+1}$.

    \textbf{Formalization.} The proof is the printed one. The extension of
    $(\varphi_1,\dots,\varphi_j,\psi)$ to a system with the properties (i), (ii), (iii) of
    Lemma~1 for $J_2$ is asserted without argument in the paper; it is proved here: the system
    has non-decreasing degrees $\le s$ and every homogeneous element of
    $\operatorname{gr}_M(J_2,R)$ of degree $<s$ lies in $(\varphi_1,\dots,\varphi_j)
    \operatorname{gr}_M(R)$, so one appends, one at a time, a homogeneous element of
    $\operatorname{gr}_M(J_2,R)$ of smallest degree outside the ideal generated so far (its
    degree is $\ge s$, which keeps (ii), and (iii) holds by choice); the ideals generated
    increase strictly, so the process stops since $\operatorname{gr}_M(R)$ is noetherian, and
    (i) holds at the end. Lemma~1 then gives $\nu^{(i)}(J_2)=\nu^{(i)}(J_1)$ for $i\le j$ and
    $\nu^{(j+1)}(J_2)=s<\nu^{(j+1)}(J_1)$. -/)
  (latexEnv := "lemma")]
theorem nuStar_ge_and_eq_iff_of_le (J₁ J₂ : Ideal R) (h : J₁ ≤ J₂) :
    nuStar R J₂ ≤ nuStar R J₁ ∧ (nuStar R J₁ = nuStar R J₂ ↔ J₁ = J₂) := by
  -- `gr_M(J₁, R) ⊆ gr_M(J₂, R)`; if they are equal then `J₁ = J₂` (Krull), otherwise
  -- `ν*(J₂) < ν*(J₁)` (`nuStar_lt`)
  have hI : grIdeal (maximalIdeal R) J₁ ≤ grIdeal (maximalIdeal R) J₂ :=
    Ideal.span_mono (Set.image_mono h)
  have key : J₁ = J₂ ∨ nuStar R J₂ < nuStar R J₁ := by
    by_cases heq : grIdeal (maximalIdeal R) J₁ = grIdeal (maximalIdeal R) J₂
    · exact Or.inl (eq_of_grIdeal_eq R h heq)
    · exact Or.inr (nuStar_lt R hI heq)
  refine ⟨?_, ?_, fun e => by rw [e]⟩
  · rcases key with h' | h'
    · rw [h']
    · exact h'.le
  · intro e
    rcases key with h' | h'
    · exact h'
    · exact absurd e (ne_of_gt h')

/-- Corollary to Lemma 3, p. 208: "If `(f₁, …, f_m)` is a system of elements of `J` such that
their initial forms `(φ₁, …, φ_m)` in `gr_M(R)` have the properties (i), (ii), and (iii) of
Lemma 1, then `J = (f₁, …, f_m)R`."  The hypothesis is `IsStandardBase R J f`
(Definition 3, which the paper states right after this Corollary).

Gap in the paper filled: the paper gives no proof.  The proof is the one the position of the
Corollary suggests, from Lemma 1 and Lemma 3: `J₀ = (f₁, …, f_m)R ⊆ J` has the same `gr_M` (the
`φ_j` are the initial forms of the `f_j ∈ J₀`), the same system has the properties of Lemma 1 for
`J₀` and `J`, so `ν*(J₀) = ν*(J)` and `J₀ = J` by Lemma 3. -/
@[blueprint "cor:III.lem3"
  (statement := /-- If $(f_1,\dots,f_m)$ is a system of elements of $J$ such that their
    initial forms $(\varphi_1,\dots,\varphi_m)$ in $\operatorname{gr}_M(R)$ have the
    properties (i), (ii), and (iii) of Lemma~1 (\cref{lem:III.1}), i.e.\ if $(f_1,\dots,f_m)$
    is a standard base of $J$ (\cref{def:III.3}), then $J=(f_1,\dots,f_m)R$.
    (Corollary to Lemma 3, p.~208.) -/)
  (proof := /-- Let $J_0=(f_1,\dots,f_m)R\subseteq J$. The initial forms $\varphi_j$ of the
    $f_j$ lie in $\operatorname{gr}_M(J_0,R)\subseteq\operatorname{gr}_M(J,R)
    =(\varphi_1,\dots,\varphi_m)\operatorname{gr}_M(R)$, so
    $\operatorname{gr}_M(J_0,R)=\operatorname{gr}_M(J,R)$ and $(\varphi_1,\dots,\varphi_m)$
    has the properties (i)--(iii) of Lemma~1 for $J_0$ as well. By Lemma~1,
    $\nu^*(J_0)=\nu^*(J)$, hence $J_0=J$ by Lemma~3 (\cref{lem:III.3}).

    \textbf{Gap in the paper filled.} The paper states this Corollary without proof; the
    argument above (from Lemma~1 and Lemma~3, the lemmas it follows) is supplied by the
    formalization, and the formal proof is this one. -/)
  (latexEnv := "corollary")]
theorem span_eq_of_isStandardBase (J : Ideal R) {m : ℕ} (f : Fin m → R)
    (hf : IsStandardBase R J f) : Ideal.span (Set.range f) = J := by
  obtain ⟨hfJ, hJφ, ⟨d, hd, h₂⟩, h₁, h₃⟩ := hf
  -- `J₀ = (f₁, …, f_m)R ⊆ J`
  let J₀ : Ideal R := Ideal.span (Set.range f)
  have hle : J₀ ≤ J := Ideal.span_le.mpr (by rintro _ ⟨j, rfl⟩; exact hfJ j)
  -- `gr_M(J₀, R) = gr_M(J, R)`: the `φ_j`, the initial forms of the `f_j ∈ J₀`, generate `gr_M(J, R)`
  have hJ₀φ : ∀ j, initialForm (maximalIdeal R) (f j) ∈ grIdeal (maximalIdeal R) J₀ := fun j =>
    Ideal.subset_span ⟨f j, Ideal.subset_span ⟨j, rfl⟩, rfl⟩
  have h₁' : grIdeal (maximalIdeal R) J₀ =
      Ideal.span (Set.range fun j => initialForm (maximalIdeal R) (f j)) :=
    le_antisymm (h₁ ▸ Ideal.span_mono (Set.image_mono hle))
      (Ideal.span_le.mpr (by rintro _ ⟨j, rfl⟩; exact hJ₀φ j))
  -- so `(φ₁, …, φ_m)` has the properties (i)–(iii) of Lemma 1 for `J₀` as well, whence
  -- `ν*(J₀) = ν*(J)` by Lemma 1
  obtain ⟨hA, hB⟩ := nuI_eq_of_lemma1_properties R J _ hJφ d hd h₁ h₂ h₃
  obtain ⟨hA₀, hB₀⟩ := nuI_eq_of_lemma1_properties R J₀ _ hJ₀φ d hd h₁' h₂ h₃
  have hν : nuStar R J₀ = nuStar R J := by
    unfold nuStar
    congr 1
    funext i
    by_cases hi : (i : ℕ) ≤ m
    · have hk : (i : ℕ) - 1 < m := by have := i.pos; omega
      have hik : (⟨((⟨(i : ℕ) - 1, hk⟩ : Fin m) : ℕ) + 1, Nat.succ_pos _⟩ : ℕ+) = i :=
        PNat.eq (by simp only [PNat.mk_coe]; have := i.pos; omega)
      rw [← hik, hA₀, hA]
    · rw [hB₀ i (by omega), hB i (by omega)]
  -- `J₀ = J` by Lemma 3
  exact ((nuStar_ge_and_eq_iff_of_le R J₀ J hle).2).1 hν

end Lemma3

/-! ### Remark (pp. 208–209): ν^{(1)}(J), ν^{(2)}(J) and the characters ν_{(i)}(J) -/

section Remark

variable (R : Type u) [CommRing R] [IsRegularLocalRing R]

/-- p. 209: "Given a positive integer `i`, … the maximum (or `∞`), `ν_{(i)}(J)` in symbol, of
those `ν` for which there exists a system of elements `(f₁, …, f_{i-1})` of `J` such that
`J ⊆ (f₁, …, f_{i-1})R + Mᵛ`."

Formalization note (encoding): the maximum is taken as the supremum in `ℕ∞`; the admissible `ν`
form a downward closed set containing `0`, so the supremum is the maximum when it is finite and
`∞` otherwise. -/
@[blueprint "def:III.1-nu-paren"
  (statement := /-- Let $J$ be an ideal in a regular local ring $R$ with maximal ideal $M$.
    For a positive integer $i$, $\nu_{(i)}(J)$ is the maximum (or $\infty$) of those $\nu$
    for which there exists a system of elements $(f_1,\dots,f_{i-1})$ of $J$ such that
    $J\subseteq(f_1,\dots,f_{i-1})R+M^\nu$. (p.~209.) Formalization note (encoding): the
    maximum is taken as a supremum in $\mathbb N\cup\{\infty\}$. -/)
  (latexEnv := "definition")]
noncomputable def nuParen (J : Ideal R) (i : ℕ+) : ℕ∞ :=
  ⨆ (ν : ℕ) (_ : ∃ f : Fin ((i : ℕ) - 1) → R, (∀ j, f j ∈ J) ∧
    J ≤ Ideal.span (Set.range f) + maximalIdeal R ^ ν), (ν : ℕ∞)

/-- Remark (a): `ν^{(1)}(J) = ν(J)`: the empty system has the property of Definition 1 for all
`μ < ν` iff `gr^μ_M(J, R) = 0` for all `μ < ν`, i.e. iff `J ⊆ Mᵛ`. -/
private theorem nuI_one_eq_nu (J : Ideal R) : nuI R J 1 = Ideal.nu J := by
  have key : ∀ ν : ℕ, (∃ φ : Fin (((1 : ℕ+) : ℕ) - 1) → AssocGraded (maximalIdeal R),
      IsNuSystem R J ν (((1 : ℕ+) : ℕ) - 1) φ) ↔ J ≤ maximalIdeal R ^ ν := by
    intro ν
    constructor
    · rintro ⟨φ, hφ⟩
      have hbot : Ideal.span (Set.range φ) = ⊥ := by
        rw [Ideal.span_eq_bot]
        rintro _ ⟨j, rfl⟩
        exact absurd j.2 (by simp)
      have : ∀ μ ≤ ν, J ≤ maximalIdeal R ^ μ := by
        intro μ
        induction μ with
        | zero => intro _; simp
        | succ μ ih =>
          intro hμ f hf
          have hfμ := ih (by omega) hf
          have := (hφ.2 μ (by omega) _ (AssocGraded.mk_mem_homogeneous _ hfμ)).mpr
            (mk_mem_grIdeal _ hf hfμ)
          rwa [hbot, Ideal.mem_bot, AssocGraded.mk_eq_zero_iff] at this
      exact this ν le_rfl
    · intro hJ
      refine ⟨fun j => absurd j.2 (by simp), fun j => absurd j.2 (by simp), fun μ hμ ψ hψ => ?_⟩
      have hbot : Ideal.span (Set.range (fun j : Fin (((1 : ℕ+) : ℕ) - 1) =>
          (absurd j.2 (by simp) : AssocGraded (maximalIdeal R)))) = ⊥ := by
        rw [Ideal.span_eq_bot]
        rintro _ ⟨j, rfl⟩
        exact absurd j.2 (by simp)
      rw [hbot, Ideal.mem_bot]
      constructor
      · rintro rfl; exact zero_mem _
      · intro h
        obtain ⟨a, ⟨haJ, -⟩, ha, rfl⟩ := (grIdeal_homogeneous_eq _ J μ ψ hψ).mp h
        exact (AssocGraded.mk_eq_zero_iff _ ha).mpr
          (Ideal.pow_le_pow_right (by omega : μ + 1 ≤ ν) (hJ haJ))
  simp only [nuI, Ideal.nu, Ideal.ord, key]

/-- Remark (c), p. 209: "Given a positive integer `i`, `ν^{(i)}(J)` is at most the maximum (or
`∞`), `ν_{(i)}(J)` in symbol, of those `ν` for which there exists a system of elements
`(f₁, …, f_{i-1})` of `J` such that `J ⊆ (f₁, …, f_{i-1})R + Mᵛ`.  In fact, we take a standard
base `(f₁, …, f_m)` of `J`, which necessarily has the property that
`(f₁, …, f_{i-1})R + M^{ν^{(i)}(J)} ⊇ J`.  (See the proof of Lemma 3.)  The assertion is clear."

For `i ≤ m`, `ν^{(i)}(J) = deg φ_i` (Lemma 1); the system `(φ₁, …, φ_{i-1})` has the property of
Definition 1 up to `ν^{(i)}(J)`, and the `φ_j` are initial forms of the `f_j` in
`J₀ = (f₁, …, f_{i-1})R`, so `gr^μ_M(J₀, R) = gr^μ_M(J, R)` for `μ < ν^{(i)}(J)`, whence
`J ⊆ J₀ + M^{ν^{(i)}(J)}` by the second half of the proof of Lemma 3
(`le_sup_pow_of_grIdeal_eq`).  For `i > m`, `ν^{(i)}(J) = ∞` (Lemma 1) and `J = (f₁, …, f_m)R`
(Corollary to Lemma 3). -/
private theorem nuI_le_nuParen (J : Ideal R) (i : ℕ+) : nuI R J i ≤ nuParen R J i := by
  classical
  -- "we take a standard base `(f₁, …, f_m)` of `J`"
  obtain ⟨m, f, hf⟩ := exists_isStandardBase_lift J
  have hstd := hf
  obtain ⟨hfJ, hJφ, ⟨d, hd, h₂⟩, h₁, h₃⟩ := hf
  -- Lemma 1: `ν^{(j)}(J) = deg φ_j` for `j ≤ m` and `∞` for `j > m`
  obtain ⟨hν, hν'⟩ := nuI_eq_of_lemma1_properties R J _ hJφ d hd h₁ h₂ h₃
  by_cases him : (i : ℕ) - 1 < m
  · have hiν : nuI R J i = d ⟨(i : ℕ) - 1, him⟩ := by
      have := hν ⟨(i : ℕ) - 1, him⟩
      rwa [show (⟨(i : ℕ) - 1 + 1, Nat.succ_pos _⟩ : ℕ+) = i from
        PNat.eq (Nat.sub_add_cancel i.pos)] at this
    -- `(f₁, …, f_{i-1})`
    let f' : Fin ((i : ℕ) - 1) → R := fun t => f (Fin.castLE him.le t)
    have hJ0 : Ideal.span (Set.range f') ≤ J :=
      Ideal.span_le.mpr (by rintro _ ⟨t, rfl⟩; exact hfJ _)
    -- `(φ₁, …, φ_{i-1})` has the property of Definition 1 up to `ν_i = ν^{(i)}(J)`
    have hφ' : IsNuSystem R J (d ⟨(i : ℕ) - 1, him⟩) ((i : ℕ) - 1)
        (fun t => initialForm (maximalIdeal R) (f' t)) :=
      isNuSystem_prefix R J (fun j => initialForm (maximalIdeal R) (f j)) hJφ d hd h₁ him.le
        (fun j hj => h₂ (show (⟨(i : ℕ) - 1, him⟩ : Fin m) ≤ j from hj))
    -- "`(f₁, …, f_{i-1})R + M^{ν^{(i)}(J)} ⊇ J`.  (See the proof of Lemma 3.)"
    have hkey : J ≤ Ideal.span (Set.range f') ⊔ maximalIdeal R ^ d ⟨(i : ℕ) - 1, him⟩ := by
      refine le_sup_pow_of_grIdeal_eq R hJ0 fun μ hμ χ hχ hχJ => ?_
      refine (Ideal.span_le.mpr ?_) ((hφ'.2 μ hμ χ hχ).mpr hχJ)
      rintro _ ⟨t, rfl⟩
      exact Ideal.subset_span ⟨f' t, Ideal.subset_span (Set.mem_range_self t), rfl⟩
    rw [hiν]
    exact le_iSup₂ (f := fun (ν : ℕ) (_ : ∃ f : Fin ((i : ℕ) - 1) → R, (∀ j, f j ∈ J) ∧
      J ≤ Ideal.span (Set.range f) + maximalIdeal R ^ ν) => (ν : ℕ∞)) _
      ⟨f', fun t => hfJ _, hkey⟩
  · -- `i > m`: `ν^{(i)}(J) = ∞` and `J = (f₁, …, f_m)R` (Corollary to Lemma 3)
    have hpos := i.pos
    rw [hν' i (by omega), ← ENat.iSup_natCast]
    refine iSup_le fun ν => ?_
    let f'' : Fin ((i : ℕ) - 1) → R := fun t => if h : (t : ℕ) < m then f ⟨t, h⟩ else 0
    have hf''J : ∀ t, f'' t ∈ J := fun t => by
      simp only [f'']
      split_ifs with h
      · exact hfJ _
      · exact zero_mem _
    have hspan : J ≤ Ideal.span (Set.range f'') := by
      rw [← span_eq_of_isStandardBase R J f hstd]
      refine Ideal.span_le.mpr ?_
      rintro _ ⟨j, rfl⟩
      refine Ideal.subset_span ⟨⟨j, by omega⟩, ?_⟩
      simp [f'']
    exact le_iSup₂ (f := fun (ν : ℕ) (_ : ∃ f : Fin ((i : ℕ) - 1) → R, (∀ j, f j ∈ J) ∧
      J ≤ Ideal.span (Set.range f) + maximalIdeal R ^ ν) => (ν : ℕ∞)) ν
      ⟨f'', hf''J, hspan.trans le_sup_left⟩

/-- `ν(J) = min_{f ∈ J} ν_M(f)`. -/
private theorem nu_eq_iInf_ordElem (J : Ideal R) :
    Ideal.nu J = ⨅ f ∈ J, Ideal.ordElem (maximalIdeal R) f := by
  refine le_antisymm (le_iInf₂ fun f hf => Ideal.ord_le fun ν hν => Ideal.le_ordElem (hν hf)) ?_
  refine ENat.forall_natCast_le_iff_le.mp fun ν hν => Ideal.le_ord fun f hf => ?_
  have hfν := hν.trans (iInf₂_le f hf)
  by_cases htop : Ideal.ordElem (maximalIdeal R) f = ⊤
  · exact Ideal.ordElem_eq_top_iff.mp htop ν
  · obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.mp htop
    rw [← hm, Nat.cast_le] at hfν
    exact Ideal.pow_le_pow_right hfν (Ideal.mem_pow_of_ordElem hm.symm)

/-- Remark (b), p. 208: "If `ν = ν₁`, then `ν^{(2)}(J) ≥ ν` is clear": `ν^{(1)}(J) ≤ ν^{(2)}(J)`
(a system with the property of Definition 1 up to `ν` stays one when an element `0` is added). -/
private theorem nuI_one_le_nuI_two (J : Ideal R) : nuI R J 1 ≤ nuI R J 2 := by
  refine iSup₂_le fun ν ⟨φ, hφ⟩ => ?_
  refine le_iSup₂ (f := fun (ν : ℕ) (_ : ∃ φ : Fin (((2 : ℕ+) : ℕ) - 1) →
    AssocGraded (maximalIdeal R), IsNuSystem R J ν _ φ) => (ν : ℕ∞)) ν ⟨fun _ => 0, ?_⟩
  refine ⟨fun _ => ⟨zero_mem _, 0, zero_mem _⟩, fun μ hμ ψ hψ => ?_⟩
  rw [← hφ.2 μ hμ ψ hψ]
  have h1 : Ideal.span (Set.range φ) = ⊥ := by
    rw [Ideal.span_eq_bot]
    rintro _ ⟨j, rfl⟩
    exact absurd j.2 (by simp)
  have h2 : Ideal.span (Set.range fun _ : Fin (((2 : ℕ+) : ℕ) - 1) =>
      (0 : AssocGraded (maximalIdeal R))) = ⊥ := by
    rw [Ideal.span_eq_bot]
    rintro _ ⟨j, rfl⟩
    rfl
  rw [h1, h2]

/-- Remark (b), p. 208: "We may assume that `ν > ν₁` and hence `ν_M(f₁) = ν₁`", where
`J ⊆ (f₁)R + Mᵛ`, `f₁ ∈ J` and `ν₁ = ν^{(1)}(J) = ν(J) = min_{f ∈ J} ν_M(f)`.  (If `f₁ ∈ Mᵛ¹⁺¹`
then `J ⊆ Mᵛ¹⁺¹`, against the definition of `ν₁`.) -/
private theorem ordElem_eq_of_le_span_add_pow (J : Ideal R) {ν ν₁ : ℕ} {f₁ : R} (hf₁ : f₁ ∈ J)
    (hJ : J ≤ Ideal.span {f₁} + maximalIdeal R ^ ν) (hν₁ : (ν₁ : ℕ∞) = nuI R J 1)
    (hlt : ν₁ < ν) : Ideal.ordElem (maximalIdeal R) f₁ = ν₁ := by
  refine le_antisymm (Ideal.ordElem_le_of_notMem fun hmem => ?_) ?_
  · have hJ1 : J ≤ maximalIdeal R ^ (ν₁ + 1) := by
      refine hJ.trans (sup_le (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hmem)) ?_)
      exact Ideal.pow_le_pow_right hlt
    have h1 : ((ν₁ + 1 : ℕ) : ℕ∞) ≤ nuI R J 1 := by
      rw [nuI_one_eq_nu]
      exact Ideal.le_ord hJ1
    rw [← hν₁] at h1
    exact absurd (Nat.cast_le.mp h1) (by omega)
  · rw [hν₁, nuI_one_eq_nu, nu_eq_iInf_ordElem]
    exact iInf₂_le f₁ hf₁

/-- Remark (b), p. 208: "We have `h ∈ R` such that `g - h f₁ ∈ Mᵛ`.  Hence the initial form of `g`
in `gr_M(R)` is equal to the product of the initial forms of `h` and `f₁` in `gr_M(R)`, provided
`ν_M(g) < ν`." -/
private theorem initialForm_eq_mul_of_sub_mem {g h f₁ : R} {ν : ℕ}
    (hg : g - h * f₁ ∈ maximalIdeal R ^ ν) (hgν : Ideal.ordElem (maximalIdeal R) g < ν) :
    initialForm (maximalIdeal R) g =
      initialForm (maximalIdeal R) h * initialForm (maximalIdeal R) f₁ := by
  obtain ⟨μ, hμ⟩ := ENat.ne_top_iff_exists.mp (ne_top_of_lt hgν)
  have hμν : μ < ν := by rw [← hμ] at hgν; exact_mod_cast hgν
  have hgμ : g ∈ maximalIdeal R ^ μ := Ideal.mem_pow_of_ordElem hμ.symm
  have hz1 : g - h * f₁ ∈ maximalIdeal R ^ (μ + 1) := Ideal.pow_le_pow_right hμν hg
  have hhfμ : h * f₁ ∈ maximalIdeal R ^ μ := by
    have : h * f₁ = g - (g - h * f₁) := by ring
    rw [this]
    exact sub_mem hgμ (Ideal.pow_le_pow_right (Nat.le_succ μ) hz1)
  have hord : Ideal.ordElem (maximalIdeal R) (h * f₁) = μ := by
    refine le_antisymm (Ideal.ordElem_le_of_notMem fun hmem => ?_) (Ideal.le_ordElem hhfμ)
    have hg1 : g ∈ maximalIdeal R ^ (μ + 1) := by
      have : g = h * f₁ + (g - h * f₁) := by ring
      rw [this]
      exact add_mem hmem hz1
    have h1 := Ideal.le_ordElem hg1
    rw [← hμ] at h1
    exact absurd (Nat.cast_le.mp h1) (by omega)
  rw [initialForm_eq_mk _ hμ.symm, ← initialForm_mul_maximalIdeal, initialForm_eq_mk _ hord]
  have hsub : AssocGraded.mk (maximalIdeal R) μ (g - h * f₁) (sub_mem hgμ hhfμ) =
      AssocGraded.mk (maximalIdeal R) μ g hgμ -
        AssocGraded.mk (maximalIdeal R) μ (h * f₁) hhfμ :=
    map_sub (AssocGraded.mkLinear (maximalIdeal R) μ) ⟨g, hgμ⟩ ⟨h * f₁, hhfμ⟩
  rw [← sub_eq_zero, ← hsub, AssocGraded.mk_eq_zero_iff]
  exact hz1

/-- The ≥ half of (b), as in the paper (p. 208): if `f₁ ∈ J` and `J ⊆ (f₁)R + Mᵛ`, then
`ν ≤ ν^{(2)}(J)`.  "It is trivial if `J = (0)`" (then `ν₁ = ν(J) = ∞`, and the case `ν ≤ ν₁`
below applies).  Let `ν₁ = ν^{(1)}(J) = ν(J)`.  If `ν ≤ ν₁`, then `ν^{(2)}(J) ≥ ν` is clear.  Else
`ν > ν₁` and hence `ν_M(f₁) = ν₁`; if `φ₁` is the initial form of `f₁` in `gr_M(R)`, then
`gr^μ_M(J, R) = (φ₁) gr_M(R) ∩ gr^μ_M(R)` for all `μ < ν`, i.e. `(φ₁)` has the property of
Definition 1 up to `ν`, so `ν ≤ ν^{(2)}(J)`. -/
private theorem le_nuI_two (J : Ideal R) {ν : ℕ} {f₁ : R} (hf₁ : f₁ ∈ J)
    (hJ : J ≤ Ideal.span {f₁} + maximalIdeal R ^ ν) : (ν : ℕ∞) ≤ nuI R J 2 := by
  -- "If `ν = ν₁`, then `ν^{(2)}(J) ≥ ν` is clear."
  by_cases hν1 : (ν : ℕ∞) ≤ nuI R J 1
  · exact hν1.trans (nuI_one_le_nuI_two R J)
  -- "We may assume that `ν > ν₁` and hence `ν_M(f₁) = ν₁`."
  rw [not_le] at hν1
  obtain ⟨ν₁, hν₁⟩ := ENat.ne_top_iff_exists.mp (ne_top_of_lt hν1)
  have hlt : ν₁ < ν := by rw [← hν₁] at hν1; exact_mod_cast hν1
  have hord := ordElem_eq_of_le_span_add_pow R J hf₁ hJ hν₁ hlt
  have hin : initialForm (maximalIdeal R) f₁ ∈ grIdeal (maximalIdeal R) J :=
    Ideal.subset_span ⟨f₁, hf₁, rfl⟩
  have hsys : IsNuSystem R J ν (((2 : ℕ+) : ℕ) - 1)
      (fun _ => initialForm (maximalIdeal R) f₁) := by
    refine ⟨fun _ => ⟨hin, ν₁, ?_⟩, fun μ hμ χ hχ => ⟨fun h => ?_, fun h => ?_⟩⟩
    · rw [initialForm_eq_mk _ hord]
      exact AssocGraded.mk_mem_homogeneous _ _
    · refine (Ideal.span_le.mpr ?_) h
      rintro _ ⟨j, rfl⟩
      exact hin
    · -- an element of `gr^μ_M(J, R)` is the class of some `g ∈ J ∩ Mᵘ`
      obtain ⟨g, ⟨hgJ, -⟩, hg, rfl⟩ :=
        (grIdeal_homogeneous_eq (maximalIdeal R) J μ χ hχ).mp h
      by_cases hg1 : g ∈ maximalIdeal R ^ (μ + 1)
      · rw [(AssocGraded.mk_eq_zero_iff _ hg).mpr hg1]
        exact zero_mem _
      have hordg : Ideal.ordElem (maximalIdeal R) g = μ :=
        le_antisymm (Ideal.ordElem_le_of_notMem hg1) (Ideal.le_ordElem hg)
      -- "We have `h ∈ R` such that `g - h f₁ ∈ Mᵛ`"
      obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.mp (hJ hgJ)
      obtain ⟨h', rfl⟩ := Ideal.mem_span_singleton'.mp hy
      have hgz : g - h' * f₁ ∈ maximalIdeal R ^ ν := by
        rw [← hyz]
        simpa using hz
      -- "Hence the initial form of `g` is the product of the initial forms of `h` and `f₁`"
      have hprod := initialForm_eq_mul_of_sub_mem R hgz (by rw [hordg]; exact_mod_cast hμ)
      rw [initialForm_eq_mk _ hordg] at hprod
      rw [hprod]
      exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨⟨0, by decide⟩, rfl⟩)
  exact le_iSup₂ (f := fun (ν : ℕ) (_ : ∃ φ : Fin (((2 : ℕ+) : ℕ) - 1) →
    AssocGraded (maximalIdeal R), IsNuSystem R J ν _ φ) => (ν : ℕ∞)) ν ⟨_, hsys⟩

/-- Remark, pp. 208–209: "As is easily seen, we have `ν^{(1)}(J) = min_{f ∈ J} {ν_M(f)}`, i.e.,
`ν^{(1)}(J) = ν(J)`. Moreover, we can see that `ν^{(2)}(J)` is the largest integer `ν` (or `∞`)
such that there exists `f₁ ∈ J` with the property: `J ⊆ (f₁)R + Mᵛ`. … Given a positive
integer `i`, `ν^{(i)}(J)` is at most the maximum (or `∞`), `ν_{(i)}(J)` in symbol, of those
`ν` for which there exists a system of elements `(f₁, …, f_{i-1})` of `J` such that
`J ⊆ (f₁, …, f_{i-1})R + Mᵛ`. … We remark that `ν^{(3)}(J)` can be smaller than `ν_{(3)}(J)`,
and the same for `ν^{(i)}(J)` and `ν_{(i)}(J)` if `i > 2`. For example, let
`R = k{x, y, z₁, z₂}` be a formal power series ring of four variables over a field `k`. Let
`J` be the ideal generated by `f₁ = z₁z₂ + x³` and `f₂ = z₁(z₁ + z₂) + y³`. Then we have
`h = (z₁ + z₂)f₁ − z₂f₂ = (z₁ + z₂)x³ − z₂y³ ∈ J`. We can prove that
`ν^{(1)}(J) = ν_{(1)}(J) = 2`, `ν^{(2)}(J) = ν_{(2)}(J) = 2` but `ν^{(3)}(J) = 4` while
`ν_{(3)}(J) = ∞`."

Here `ν(J) = Ideal.nu J = Ideal.ord (maximalIdeal R) J` is the largest `ν` with `J ⊆ Mᵛ`
(p. 165), which is `min_{f ∈ J} ν_M(f)` (`Ideal.ordElem`); (a) records both forms.  (b) is
stated literally, as the supremum of the `ν` admitting `f₁ ∈ J` with `J ⊆ (f₁)R + Mᵛ` (this is
`nuParen R J 2`).  (c) is `ν^{(i)}(J) ≤ ν_{(i)}(J)` for all `i`.

Deviation from the paper (not formalized): the example of p. 209 (the values of `ν^{(i)}` and
`ν_{(i)}` for `J = (z₁z₂ + x³, z₁(z₁ + z₂) + y³)` in `k{x, y, z₁, z₂}`, asserted by the paper
without proof) is not formalized.

Both (b) and (c) are proved as printed: (b) `≥` with the case distinction `ν ≤ ν₁` / `ν > ν₁`,
the equality `ν_M(f₁) = ν₁`, and the product of initial forms (`le_nuI_two`); (c) with a standard
base and the second half of the proof of Lemma 3 (`nuI_le_nuParen`).  (a) ("as is easily seen")
is proved. -/
@[blueprint "rem:III.1-nu"
  (statement := /-- Let $J$ be an ideal in a regular local ring $R$ with maximal ideal $M$.
    (a) $\nu^{(1)}(J)=\min_{f\in J}\{\nu_M(f)\}$, i.e.\ $\nu^{(1)}(J)=\nu(J)$
    (\cref{def:order-nu}). (b) $\nu^{(2)}(J)$ is the largest integer $\nu$ (or $\infty$) such
    that there exists $f_1\in J$ with the property $J\subseteq(f_1)R+M^\nu$. (c) For every
    positive integer $i$, $\nu^{(i)}(J)\le\nu_{(i)}(J)$ (\cref{def:III.1-nu-paren}).
    (Remark, pp.~208--209.)

    \textbf{Not formalized.} The example of p.~209 is not formalized: for the formal power
    series ring $R=k\{x,y,z_1,z_2\}$ and $J=(f_1,f_2)$, $f_1=z_1z_2+x^3$,
    $f_2=z_1(z_1+z_2)+y^3$, the paper asserts (``We can prove that'', without proof)
    $\nu^{(1)}(J)=\nu_{(1)}(J)=2$, $\nu^{(2)}(J)=\nu_{(2)}(J)=2$, but $\nu^{(3)}(J)=4$ while
    $\nu_{(3)}(J)=\infty$. -/)
  (proof := /-- (a) [The paper: ``As is easily seen''. Argument supplied by the
    formalization:] the empty system has the property of Definition~1 for all $\mu<\nu$ iff
    $\operatorname{gr}^\mu_M(J,R)=0$ for all $\mu<\nu$, i.e.\ iff $J\subseteq M^\nu$; hence
    $\nu^{(1)}(J)=\nu(J)=\min_{f\in J}\nu_M(f)$. (b) [The paper's argument:] It is trivial if
    $J=(0)$. So we assume that $J\ne(0)$. Let $\nu_1=\nu^{(1)}(J)=\nu(J)$. Suppose we have
    $f_1\in J$ such that $J\subseteq(f_1)R+M^{\nu}$ with $\nu\ge\nu_1$. We claim
    $\nu^{(2)}(J)\ge\nu$. If $\nu=\nu_1$, then $\nu^{(2)}(J)\ge\nu$ is clear. We may assume
    that $\nu>\nu_1$ and hence $\nu_M(f_1)=\nu_1$. Let $g$ be any element of $J$. We have
    $h\in R$ such that $g-hf_1\in M^{\nu}$. Hence the initial form of $g$ in
    $\operatorname{gr}_M(R)$ is equal to the product of the initial forms of $h$ and $f_1$ in
    $\operatorname{gr}_M(R)$, provided $\nu_M(g)<\nu$. Hence, if $\varphi_1$ is the initial
    form of $f_1$ in $\operatorname{gr}_M(R)$, then
    $\operatorname{gr}^\mu_M(J,R)=(\varphi_1)\operatorname{gr}_M(R)\cap
    \operatorname{gr}^\mu_M(R)$ for all $\mu<\nu$. Hence $\nu\le\nu^{(2)}(J)$. For the
    converse, (c) the following is
    true in general. Given a positive integer $i$, $\nu^{(i)}(J)$ is at most the maximum (or
    $\infty$), $\nu_{(i)}(J)$ in symbol, of those $\nu$ for which there exists a system of
    elements $(f_1,\dots,f_{i-1})$ of $J$ such that $J\subseteq(f_1,\dots,f_{i-1})R+M^\nu$.
    In fact, we take a standard base $(f_1,\dots,f_m)$ of $J$ (\cref{def:III.3}), which
    necessarily has the property that $(f_1,\dots,f_{i-1})R+M^{\nu^{(i)}(J)}\supseteq J$
    (see the proof of Lemma~3, \cref{lem:III.3}). The assertion is clear.

    \textbf{Formalization.} (b) and (c) are proved as printed. For (b), $\ge$: the case
    $\nu\le\nu_1$ uses $\nu^{(1)}(J)\le\nu^{(2)}(J)$ (``clear''); for $\nu>\nu_1$ the
    equality $\nu_M(f_1)=\nu_1$ is proved (if $f_1\in M^{\nu_1+1}$ then $J\subseteq
    M^{\nu_1+1}$), the initial form of $g\in J$ is the product of those of $h$ and $f_1$ when
    $g-hf_1\in M^\nu$ and $\nu_M(g)<\nu$, and this gives $\operatorname{gr}^\mu_M(J,R)=
    (\varphi_1)\operatorname{gr}_M(R)\cap\operatorname{gr}^\mu_M(R)$ for $\mu<\nu$. For (c),
    a standard base $(f_1,\dots,f_m)$ is obtained by lifting the system of Lemma~1 to elements
    of $J$; for $i\le m$, $J\subseteq(f_1,\dots,f_{i-1})R+M^{\nu^{(i)}(J)}$ by the second half
    of the proof of Lemma~3 (applied in degrees $<\nu^{(i)}(J)$), and for $i>m$,
    $\nu^{(i)}(J)=\infty$ and $J=(f_1,\dots,f_m)R$ (Corollary to Lemma~3). -/)
  (latexEnv := "remark")]
theorem nuI_one_eq_nu_and_nuI_two_and_nuI_le_nuParen (J : Ideal R) :
    (nuI R J 1 = ⨅ f ∈ J, Ideal.ordElem (maximalIdeal R) f ∧ nuI R J 1 = Ideal.nu J) ∧
    nuI R J 2 =
      ⨆ (ν : ℕ) (_ : ∃ f₁ ∈ J, J ≤ Ideal.span {f₁} + maximalIdeal R ^ ν), (ν : ℕ∞) ∧
    ∀ i : ℕ+, nuI R J i ≤ nuParen R J i := by
  have ha := nuI_one_eq_nu R J
  have hc := nuI_le_nuParen R J
  refine ⟨⟨ha.trans (nu_eq_iInf_ordElem R J), ha⟩, le_antisymm ?_ ?_, hc⟩
  · -- `≤`: this is (c) for `i = 2`
    refine (hc 2).trans (iSup₂_le fun ν ⟨f, hf, hJf⟩ => ?_)
    have hrange : Set.range f = {f ⟨0, by decide⟩} := by
      ext y
      refine ⟨?_, fun hy => ⟨_, (Set.mem_singleton_iff.mp hy).symm⟩⟩
      rintro ⟨j, rfl⟩
      refine congrArg f (Fin.ext ?_)
      have := j.2
      simp only [PNat.val_ofNat] at this
      simp only
      omega
    rw [hrange] at hJf
    exact le_iSup₂ (f := fun (ν : ℕ) (_ : ∃ f₁ ∈ J, J ≤ Ideal.span {f₁} +
      maximalIdeal R ^ ν) => (ν : ℕ∞)) ν ⟨_, hf _, hJf⟩
  · -- `≥`: the initial form of `f₁` has the property of Definition 1 up to `ν`
    exact iSup₂_le fun ν ⟨f₁, hf₁, hJ⟩ => le_nuI_two R J hf₁ hJ

end Remark

/-! ### Definition 4 (p. 209): ν*(V/X) -/

section Definition4

open AlgebraicGeometry

/-- Definition 4, p. 209: "Let `V` be a subscheme of a non-singular algebraic scheme `X`. Let
`x` be a point of `V`, `R_x` the local ring of `X` at `x` (which is regular) and `J_x` the
ideal of `V` in `R_x`. Then we shall denote `ν*(J_x)` by `ν*_x(V/X)`."

Formalization note (encoding): `R_x` is the stalk `X.presheaf.stalk x`, regular by the
hypothesis `hx : X.IsSimpleAt x` (which is `IsRegularLocalRing (X.presheaf.stalk x)`; for a
non-singular `X` it holds at every point), and `J_x` is `V.stalkIdeal x`.  The definition only
uses that `X` is simple at `x`, so it is stated for any such point of `X` rather than only for
points of `V` and non-singular `X`; at a point `x ∉ V` one has `J_x = R_x`.  The paper writes
`ν*_x(V/X)`; the point is the argument `x`. -/
@[blueprint "def:III.4"
  (statement := /-- Let $V$ be a subscheme of a non-singular algebraic scheme $X$. Let $x$ be
    a point of $V$, $R_x$ the local ring of $X$ at $x$ (which is regular) and $J_x$ the ideal
    of $V$ in $R_x$. Then we shall denote $\nu^*(J_x)$ (\cref{def:III.2}) by
    $\nu^*_x(V/X)$. (Definition 4, p.~209.) Formalization note (encoding): defined for any
    point $x$ of $X$ at which $X$ is simple (for $x\notin V$, $J_x=R_x$). -/)
  (latexEnv := "definition")]
noncomputable def Subscheme.nuStarAt {X : Scheme.{u}} (V : Subscheme X) (x : X)
    (hx : X.IsSimpleAt x) : Lex (ℕ+ → ℕ∞) :=
  @nuStar (X.presheaf.stalk x) _ hx (V.stalkIdeal x)

end Definition4

end Hironaka
