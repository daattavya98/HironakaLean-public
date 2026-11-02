/-
Copyright (c) 2026 Daattavya Aggarwal, Minhyong Kim, Oisin Kim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daattavya Aggarwal, Minhyong Kim, Oisin Kim
-/
module

public import Mathlib.Data.Sym.Card
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.KrullDimension.Regular
public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Architect
public import Hironaka.Compat.RegularLocalRing
public import Hironaka.Compat.Graded
public import Hironaka.Compat.RegularGraded

/-!
# Compatibility layer: lengths of `R/Mⁿ` and of a hypersurface section

Tools for the multiplicity of a hypersurface `R/(f)` of a regular local ring `R`
(Ch. 0 §4, p. 133: "If R is a regular local ring and J is a non-zero principal ideal in R, then
we can prove that e(R/J) = ν(J)"); see `Hironaka/Ch0/Multiplicity.lean`.  The Hilbert–Samuel
function is expressed through the `R`-length of `R/Mⁿ` (Mathlib's `Module.length`), which is
additive in exact sequences.
-/

@[expose] public section

open IsLocalRing

universe u

namespace Hironaka

section Length

variable {B : Type u} [CommRing B] (I : Ideal B)

/-- `length(B/Iᵐ⁺¹) = length(Iᵐ/Iᵐ⁺¹) + length(B/Iᵐ)`. -/
theorem length_quotient_pow_succ (m : ℕ) :
    Module.length B (B ⧸ I ^ (m + 1)) =
      Module.length B (GrPiece I m) + Module.length B (B ⧸ I ^ m) := by
  let f : GrPiece I m →ₗ[B] B ⧸ I ^ (m + 1) :=
    Submodule.liftQ _ ((Submodule.mkQ (I ^ (m + 1))).comp (I ^ m).subtype) (by
      intro x hx
      exact LinearMap.mem_ker.mpr (Ideal.Quotient.eq_zero_iff_mem.mpr hx))
  let g : B ⧸ I ^ (m + 1) →ₗ[B] B ⧸ I ^ m :=
    Submodule.factor (Ideal.pow_le_pow_right (Nat.le_succ m))
  refine Module.length_eq_add_of_exact f g ?_ ?_ ?_
  · intro x y hxy
    induction x using Submodule.Quotient.induction_on with
    | H x =>
      induction y using Submodule.Quotient.induction_on with
      | H y =>
        have : (Submodule.Quotient.mk (x : B) : B ⧸ I ^ (m + 1)) =
            Submodule.Quotient.mk (y : B) := hxy
        rw [Submodule.Quotient.eq] at this ⊢
        simpa using this
  · intro x
    induction x using Submodule.Quotient.induction_on with
    | H x => exact ⟨Submodule.Quotient.mk x, rfl⟩
  · intro y
    constructor
    · intro hy
      induction y using Submodule.Quotient.induction_on with
      | H y =>
        have h0 : (Submodule.Quotient.mk y : B ⧸ I ^ m) = 0 := hy
        rw [Submodule.Quotient.mk_eq_zero] at h0
        exact ⟨Submodule.Quotient.mk ⟨y, h0⟩, rfl⟩
    · rintro ⟨z, rfl⟩
      induction z using Submodule.Quotient.induction_on with
      | H z =>
        have : (Submodule.Quotient.mk (z : B) : B ⧸ I ^ m) = 0 :=
          (Submodule.Quotient.mk_eq_zero _).mpr z.2
        exact this

end Length

section LocalLength

variable (B : Type u) [CommRing B] [IsLocalRing B] [IsNoetherianRing B]

/-- The length of `mⁱ/mⁱ⁺¹` as a `B`-module is its dimension over the residue field. -/
theorem length_grPiece_maximalIdeal (i : ℕ) :
    Module.length B (GrPiece (maximalIdeal B) i) =
      (Module.finrank (B ⧸ maximalIdeal B) (GrPiece (maximalIdeal B) i) : ℕ∞) := by
  let _ : Field (B ⧸ maximalIdeal B) := Ideal.Quotient.field _
  have h1 : Module.length B (GrPiece (maximalIdeal B) i) =
      Module.length (B ⧸ maximalIdeal B) (GrPiece (maximalIdeal B) i) :=
    Module.length_eq_of_surjective (S := B) (R := B ⧸ maximalIdeal B)
      (M := GrPiece (maximalIdeal B) i) Ideal.Quotient.mk_surjective
  exact h1.trans (Module.length_eq_finrank _ _)

/-- `length(B/mⁿ) = Σ_{i<n} dim_k mⁱ/mⁱ⁺¹`. -/
theorem length_quotient_maximalIdeal_pow (n : ℕ) :
    Module.length B (B ⧸ maximalIdeal B ^ n) =
      ∑ i ∈ Finset.range n,
        (Module.finrank (B ⧸ maximalIdeal B) (GrPiece (maximalIdeal B) i) : ℕ∞) := by
  induction n with
  | zero =>
    have : Subsingleton (B ⧸ maximalIdeal B ^ 0) := by
      rw [pow_zero]
      exact Ideal.Quotient.subsingleton_iff.mpr Ideal.one_eq_top
    simp [Module.length_eq_zero]
  | succ n ih =>
    rw [length_quotient_pow_succ, ih, Finset.sum_range_succ, length_grPiece_maximalIdeal, add_comm]

end LocalLength

section Hypersurface

variable {R : Type u} [CommRing R] (M : Ideal R) (f : R) (ν : ℕ)

/-- For `f ∈ Mᵛ` with `(Mᵐ : f) = Mᵐ⁻ᵛ` and `A = R/(f)`:
`length_R(R/Mᵐ) = length_R(R/Mᵐ⁻ᵛ) + length_R(A/(M A)ᵐ)`. -/
theorem length_quotient_pow_eq_add (hf : f ∈ M ^ ν)
    (hcolon : ∀ (m : ℕ) (g : R), g * f ∈ M ^ m → g ∈ M ^ (m - ν)) (m : ℕ) :
    Module.length R (R ⧸ M ^ m) = Module.length R (R ⧸ M ^ (m - ν)) +
      Module.length R ((R ⧸ Ideal.span {f}) ⧸
        (M.map (Ideal.Quotient.mk (Ideal.span {f}))) ^ m) := by
  let q : R →ₗ[R] (R ⧸ Ideal.span {f}) := (Ideal.Quotient.mkₐ R (Ideal.span {f})).toLinearMap
  have hmap : (M.map (Ideal.Quotient.mk (Ideal.span {f}))) ^ m =
      (M ^ m).map (Ideal.Quotient.mk (Ideal.span {f})) := (Ideal.map_pow _ _ _).symm
  let f1 : (R ⧸ M ^ (m - ν)) →ₗ[R] (R ⧸ M ^ m) :=
    Submodule.liftQ _ ((Submodule.mkQ (M ^ m)).comp (LinearMap.mulLeft R f)) (by
      intro x hx
      refine LinearMap.mem_ker.mpr (Ideal.Quotient.eq_zero_iff_mem.mpr ?_)
      have h1 : f * x ∈ M ^ ν * M ^ (m - ν) := Ideal.mul_mem_mul hf hx
      rw [← pow_add] at h1
      exact Ideal.pow_le_pow_right (by omega) h1)
  let f2 : (R ⧸ M ^ m) →ₗ[R] ((R ⧸ Ideal.span {f}) ⧸
      (M.map (Ideal.Quotient.mk (Ideal.span {f}))) ^ m) :=
    Submodule.liftQ _ ((Ideal.Quotient.mkₐ R
      ((M.map (Ideal.Quotient.mk (Ideal.span {f}))) ^ m)).toLinearMap.comp q) (by
      intro x hx
      refine LinearMap.mem_ker.mpr (Ideal.Quotient.eq_zero_iff_mem.mpr ?_)
      rw [hmap]
      exact Ideal.mem_map_of_mem _ hx)
  refine Module.length_eq_add_of_exact f1 f2 ?_ ?_ ?_
  · intro x y hxy
    induction x using Submodule.Quotient.induction_on with
    | H x =>
      induction y using Submodule.Quotient.induction_on with
      | H y =>
        have h : (Submodule.Quotient.mk (f * x) : R ⧸ M ^ m) = Submodule.Quotient.mk (f * y) := hxy
        rw [Submodule.Quotient.eq] at h ⊢
        have h' : (x - y) * f ∈ M ^ m := by
          have : f * x - f * y = (x - y) * f := by ring
          rw [← this]
          exact h
        exact hcolon m _ h'
  · intro y
    induction y using Submodule.Quotient.induction_on with
    | H y =>
      obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
      exact ⟨Submodule.Quotient.mk x, rfl⟩
  · intro y
    constructor
    · intro hy
      induction y using Submodule.Quotient.induction_on with
      | H y =>
        have h0 : (Submodule.Quotient.mk (q y) : (R ⧸ Ideal.span {f}) ⧸
            (M.map (Ideal.Quotient.mk (Ideal.span {f}))) ^ m) = 0 := hy
        rw [Submodule.Quotient.mk_eq_zero, hmap] at h0
        obtain ⟨z, hz, hzy⟩ :=
          (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).mp h0
        have hyz : y - z ∈ Ideal.span {f} := by
          have : Ideal.Quotient.mk (Ideal.span {f}) (y - z) = 0 := by
            rw [map_sub, hzy]
            · exact sub_eq_zero.mpr rfl
          exact Ideal.Quotient.eq_zero_iff_mem.mp this
        obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp hyz
        refine ⟨Submodule.Quotient.mk c, ?_⟩
        show (Submodule.Quotient.mk (f * c) : R ⧸ M ^ m) = Submodule.Quotient.mk y
        rw [Submodule.Quotient.eq]
        have : f * c - y = -z := by rw [mul_comm, hc]; ring
        rw [this]
        exact neg_mem hz
    · rintro ⟨z, rfl⟩
      induction z using Submodule.Quotient.induction_on with
      | H z =>
        show (Submodule.Quotient.mk (q (f * z)) : (R ⧸ Ideal.span {f}) ⧸
            (M.map (Ideal.Quotient.mk (Ideal.span {f}))) ^ m) = 0
        have : q (f * z) = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr
          (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self f))
        rw [this]
        rfl

end Hypersurface

section PolynomialPieces

open MvPolynomial

variable {A : Type u} [CommRing A] (I : Ideal A) {n : ℕ} (x : Fin n → A) (hx : ∀ i, x i ∈ I ^ 1)

/-- `X_i ↦ [x_i]` sends a monomial of degree `d` into the homogeneous part of degree `d`. -/
theorem aeval_monomial_mem_homogeneous (m : Fin n →₀ ℕ) (c : A ⧸ I) :
    aeval (R := A ⧸ I) (fun i => AssocGraded.mk I 1 (x i) (hx i)) (monomial m c) ∈
      AssocGraded.homogeneous I m.degree := by
  have h1 : (monomial m (1 : A)).IsHomogeneous m.degree := isHomogeneous_monomial 1 rfl
  have h2 := aeval_mk_map_of_isHomogeneous I x hx h1
  rw [map_monomial, map_one] at h2
  have hc : (monomial m c : MvPolynomial (Fin n) (A ⧸ I)) = c • monomial m 1 := by
    rw [smul_monomial, smul_eq_mul, mul_one]
  rw [hc, map_smul, h2]
  exact Submodule.smul_mem _ _ (AssocGraded.mk_mem_homogeneous I _)

/-- `X_i ↦ [x_i]` sends a form of degree `d` into the homogeneous part of degree `d`. -/
theorem aeval_mem_homogeneous_of_isHomogeneous {K : MvPolynomial (Fin n) (A ⧸ I)} {d : ℕ}
    (hK : K.IsHomogeneous d) :
    aeval (R := A ⧸ I) (fun i => AssocGraded.mk I 1 (x i) (hx i)) K ∈
      AssocGraded.homogeneous I d := by
  rw [K.as_sum, map_sum]
  refine Submodule.sum_mem _ fun m hm => ?_
  have hdeg : m.degree = d := by
    by_contra h
    exact (mem_support_iff.mp hm) (hK.coeff_eq_zero h)
  have := aeval_monomial_mem_homogeneous I x hx m (K.coeff m)
  rwa [hdeg] at this

/-- If `X_i ↦ [x_i]` is bijective and the image of `K` is homogeneous of degree `d`, then `K` is a
form of degree `d`. -/
theorem isHomogeneous_of_aeval_mem_homogeneous
    (hbij : Function.Bijective (aeval (R := A ⧸ I) fun i => AssocGraded.mk I 1 (x i) (hx i)))
    {K : MvPolynomial (Fin n) (A ⧸ I)} {d : ℕ}
    (h : aeval (R := A ⧸ I) (fun i => AssocGraded.mk I 1 (x i) (hx i)) K ∈
      AssocGraded.homogeneous I d) : K.IsHomogeneous d := by
  classical
  set a := aeval (R := A ⧸ I) (fun i => AssocGraded.mk I 1 (x i) (hx i)) with ha
  have hcomp : ∀ j, a (homogeneousComponent j K) ∈ AssocGraded.homogeneous I j := fun j =>
    aeval_mem_homogeneous_of_isHomogeneous I x hx (homogeneousComponent_isHomogeneous j K)
  have hproj : ∀ j (z : AssocGraded I), z ∈ AssocGraded.homogeneous I j →
      ∀ j', j' ≠ j → grProj I j' z = 0 := by
    intro j z hz j' hj'
    obtain ⟨y, rfl⟩ := LinearMap.mem_range.mp hz
    exact grProj_ofGrPiece_ne I (Ne.symm hj') y
  have hzero : ∀ j, j ≠ d → homogeneousComponent j K = 0 := by
    intro j hjd
    have hsum : a K = ∑ j' ∈ Finset.range (K.totalDegree + 1), a (homogeneousComponent j' K) := by
      rw [← map_sum, sum_homogeneousComponent]
    have h1 : grProj I j (a K) = 0 := hproj d _ h j hjd
    by_cases hj : j ∈ Finset.range (K.totalDegree + 1)
    · rw [hsum, map_sum, Finset.sum_eq_single j] at h1
      · have hmem := hcomp j
        obtain ⟨y, hy⟩ := LinearMap.mem_range.mp hmem
        have : y = 0 := by
          rw [← grProj_ofGrPiece_same I j y, hy]
          exact h1
        rw [this, map_zero] at hy
        exact hbij.1 (hy.symm.trans (map_zero a).symm)
      · intro j' _ hj'
        exact hproj j' _ (hcomp j') j (Ne.symm hj')
      · intro hj'
        exact absurd hj hj'
    · refine homogeneousComponent_eq_zero j K ?_
      simp only [Finset.mem_range, not_lt] at hj
      omega
  intro m hm
  by_contra hmd
  refine hm ?_
  have hmd' : m.degree ≠ d := fun h' =>
    hmd (by simpa [Finsupp.degree_eq_weight_one, Pi.one_def] using h')
  have := hzero m.degree hmd'
  have h2 := coeff_homogeneousComponent (n := m.degree) (φ := K) m
  rw [this] at h2
  exact (by simpa using h2 : (0 : A ⧸ I) = K.coeff m).symm

/-- If `X_i ↦ [x_i]` is bijective, `grⁱ_I(A)` has the monomials of degree `i` as a basis, so its
dimension over `A/I` is the number of monomials of degree `i`. -/
theorem finrank_grPiece_eq_nat_card_degree (hI : I ≠ ⊤)
    (hbij : Function.Bijective (aeval (R := A ⧸ I) fun i => AssocGraded.mk I 1 (x i) (hx i)))
    (i : ℕ) :
    Module.finrank (A ⧸ I) (GrPiece I i) = Nat.card {m : Fin n →₀ ℕ // m.degree = i} := by
  classical
  set a := aeval (R := A ⧸ I) (fun i => AssocGraded.mk I 1 (x i) (hx i)) with ha
  let V := homogeneousSubmodule (Fin n) (A ⧸ I) i
  let F : V →ₗ[A ⧸ I] GrPiece I i := (grProj I i).comp (a.toLinearMap.comp V.subtype)
  have hF : Function.Bijective F := by
    constructor
    · intro K₁ K₂ h12
      have hmem : ∀ K : V, a K ∈ AssocGraded.homogeneous I i := fun K =>
        aeval_mem_homogeneous_of_isHomogeneous I x hx K.2
      have hrec : ∀ K : V, AssocGraded.ofGrPiece I i (F K) = a K := by
        intro K
        obtain ⟨y, hy⟩ := LinearMap.mem_range.mp (hmem K)
        show AssocGraded.ofGrPiece I i (grProj I i (a K)) = a K
        rw [← hy, grProj_ofGrPiece_same]
      apply Subtype.ext
      apply hbij.1
      rw [← hrec K₁, ← hrec K₂, h12]
    · intro y
      obtain ⟨K, hK⟩ := hbij.2 (AssocGraded.ofGrPiece I i y)
      have hKh : K.IsHomogeneous i := isHomogeneous_of_aeval_mem_homogeneous I x hx hbij
        (by rw [hK]; exact LinearMap.mem_range.mpr ⟨y, rfl⟩)
      refine ⟨⟨K, hKh⟩, ?_⟩
      show grProj I i (a K) = y
      rw [hK, grProj_ofGrPiece_same]
  rw [← LinearEquiv.finrank_eq (LinearEquiv.ofBijective F hF)]
  have hV := homogeneousSubmodule_eq_finsupp_supported (Fin n) (A ⧸ I) i
  have : Nontrivial (A ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr hI
  have : Fintype ↑{d : Fin n →₀ ℕ | d.degree = i} := (Finsupp.finite_of_degree_eq i).fintype
  show Module.finrank (A ⧸ I) (homogeneousSubmodule (Fin n) (A ⧸ I) i) = _
  rw [hV, LinearEquiv.finrank_eq (AddMonoidAlgebra.supportedEquivFinsupp
    (R := A ⧸ I) (S := A ⧸ I) {d : Fin n →₀ ℕ | d.degree = i}), Module.finrank_finsupp_self]
  exact (Nat.card_eq_fintype_card).symm

/-- The number of monomials of degree `i` in `e + 1` variables is `C(i + e, e)`. -/
theorem nat_card_degree_eq_choose (e i : ℕ) :
    Nat.card {m : Fin (e + 1) →₀ ℕ // m.degree = i} = (i + e).choose e := by
  classical
  have eq : {m : Fin (e + 1) →₀ ℕ // m.degree = i} ≃ Sym (Fin (e + 1)) i :=
    (Equiv.subtypeEquivRight fun α => by
      rw [Finsupp.degree_apply]
      rfl).trans (Sym.equivNatSum (Fin (e + 1)) i).symm
  rw [Nat.card_congr eq, Nat.card_eq_fintype_card, Sym.card_sym_eq_multichoose, Fintype.card_fin,
    Nat.multichoose_eq]
  have h : e + 1 + i - 1 = i + e := by omega
  rw [h, Nat.choose_symm_add]

/-- The number of monomials of degree `i` in `n ≥ 1` variables is `C(i + n - 1, n - 1)`. -/
theorem nat_card_degree_eq_choose_pred {n : ℕ} (hn : 0 < n) (i : ℕ) :
    Nat.card {m : Fin n →₀ ℕ // m.degree = i} = (i + (n - 1)).choose (n - 1) := by
  obtain ⟨e, rfl⟩ : ∃ e, n = e + 1 := ⟨n - 1, by omega⟩
  simpa using nat_card_degree_eq_choose e i

end PolynomialPieces

section RegularLocal

variable (R : Type u) [CommRing R] [IsRegularLocalRing R]

/-- For a regular local ring `R` of dimension `e + 1 ≥ 1`, `dim_k mⁱ/mⁱ⁺¹ = C(i + e, e)`. -/
theorem exists_finrank_grPiece_maximalIdeal_eq_choose (hM : maximalIdeal R ≠ ⊥) :
    ∃ e : ℕ, ringKrullDim R = ((e + 1 : ℕ) : WithBot ℕ∞) ∧
      ∀ i, Module.finrank (R ⧸ maximalIdeal R) (GrPiece (maximalIdeal R) i) =
        (i + e).choose e := by
  obtain ⟨-, s, hs⟩ := (isRegularLocalRing_iff_exists_rsop R).mp inferInstance
  have hcard : 0 < s.card := by
    rcases Nat.eq_zero_or_pos s.card with h0 | h0
    · exfalso
      apply hM
      rw [← hs.1, Finset.card_eq_zero.mp h0]
      simp
    · exact h0
  have hz : ∀ i : Fin s.card, ((s.equivFin.symm i : s) : R) ∈ maximalIdeal R ^ 1 := fun i => by
    rw [pow_one, ← hs.1]
    exact Ideal.subset_span (s.equivFin.symm i).2
  have hbij := assocGraded_maximalIdeal_aeval_bijective_of_rsop hs hz
  refine ⟨s.card - 1, ?_, fun i => ?_⟩
  · rw [← hs.2]
    have : s.card - 1 + 1 = s.card := by omega
    rw [this]
  · rw [finrank_grPiece_eq_nat_card_degree (maximalIdeal R) _ hz Ideal.IsPrime.ne_top' hbij i,
      nat_card_degree_eq_choose_pred hcard]

end RegularLocal

section Hypersurface'

variable {R : Type u} [CommRing R] [IsRegularLocalRing R]

/-- In a regular local ring, `ν(g f) = ν(g) + ν(f)` gives `(Mᵐ : f) = Mᵐ⁻ᵛ` for `ν = ν(f)`. -/
theorem mem_pow_sub_of_mul_mem_pow {f : R} {ν : ℕ} (hν : Ideal.ordElem (maximalIdeal R) f = ν)
    (m : ℕ) (g : R) (h : g * f ∈ maximalIdeal R ^ m) : g ∈ maximalIdeal R ^ (m - ν) := by
  by_cases hg : g = 0
  · rw [hg]
    exact zero_mem _
  have hgtop : Ideal.ordElem (maximalIdeal R) g ≠ ⊤ := fun h' =>
    hg ((Ideal.ordElem_eq_top_iff_eq_zero Ideal.IsPrime.ne_top').mp h')
  obtain ⟨a, ha⟩ := ENat.ne_top_iff_exists.mp hgtop
  have h1 := Ideal.le_ordElem h
  rw [ordElem_mul_maximalIdeal, ← ha, hν, ← Nat.cast_add, Nat.cast_le] at h1
  exact Ideal.pow_le_pow_right (by omega) (Ideal.mem_pow_of_ordElem ha.symm)

/-- `Σ_{i<m} C(i + e, e) = C(m + e, e + 1)`. -/
theorem sum_range_choose_eq (e m : ℕ) :
    ∑ i ∈ Finset.range m, (i + e).choose e = (m + e).choose (e + 1) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, ih, show m + 1 + e = (m + e) + 1 by ring, Nat.choose_succ_succ,
      add_comm]

/-- `R`-length of `R/Mᵐ` for a regular local ring of dimension `e + 1`. -/
theorem length_quotient_maximalIdeal_pow_regular {e : ℕ}
    (hgr : ∀ i, Module.finrank (R ⧸ maximalIdeal R) (GrPiece (maximalIdeal R) i) =
      (i + e).choose e) (m : ℕ) :
    Module.length R (R ⧸ maximalIdeal R ^ m) = ((m + e).choose (e + 1) : ℕ) := by
  rw [length_quotient_maximalIdeal_pow]
  simp_rw [hgr]
  rw [← Nat.cast_sum, sum_range_choose_eq]

/-- The Hilbert–Samuel function of `R/(f)` in terms of binomial coefficients. -/
theorem sum_finrank_grPiece_quotient_span_singleton (f : R) {ν e : ℕ}
    (hν : Ideal.ordElem (maximalIdeal R) f = ν)
    (hgr : ∀ i, Module.finrank (R ⧸ maximalIdeal R) (GrPiece (maximalIdeal R) i) =
      (i + e).choose e)
    [IsLocalRing (R ⧸ Ideal.span {f})] (n : ℕ) :
    ∑ i ∈ Finset.range (n + 1), Module.finrank ((R ⧸ Ideal.span {f}) ⧸
        maximalIdeal (R ⧸ Ideal.span {f})) (GrPiece (maximalIdeal (R ⧸ Ideal.span {f})) i) =
      (n + 1 + e).choose (e + 1) - (n + 1 - ν + e).choose (e + 1) := by
  have hmA : (maximalIdeal R).map (Ideal.Quotient.mk (Ideal.span {f})) =
      maximalIdeal (R ⧸ Ideal.span {f}) :=
    IsLocalRing.map_maximalIdeal_of_surjective _ Ideal.Quotient.mk_surjective
  have h1 := length_quotient_pow_eq_add (maximalIdeal R) f ν (Ideal.mem_pow_of_ordElem hν)
    (mem_pow_sub_of_mul_mem_pow hν) (n + 1)
  rw [hmA, length_quotient_maximalIdeal_pow_regular hgr,
    length_quotient_maximalIdeal_pow_regular hgr] at h1
  have h2 : Module.length R ((R ⧸ Ideal.span {f}) ⧸
        maximalIdeal (R ⧸ Ideal.span {f}) ^ (n + 1)) =
      Module.length (R ⧸ Ideal.span {f}) ((R ⧸ Ideal.span {f}) ⧸
        maximalIdeal (R ⧸ Ideal.span {f}) ^ (n + 1)) :=
    Module.length_eq_of_surjective (S := R) (R := R ⧸ Ideal.span {f})
      Ideal.Quotient.mk_surjective
  rw [h2, length_quotient_maximalIdeal_pow, ← Nat.cast_sum] at h1
  have h3 : (n + 1 + e).choose (e + 1) = (n + 1 - ν + e).choose (e + 1) +
      ∑ i ∈ Finset.range (n + 1), Module.finrank ((R ⧸ Ideal.span {f}) ⧸
        maximalIdeal (R ⧸ Ideal.span {f})) (GrPiece (maximalIdeal (R ⧸ Ideal.span {f})) i) := by
    exact_mod_cast h1
  omega

/-- `dim R/(f) = dim R - 1` for a non-zero `f` in the maximal ideal of a regular local ring. -/
theorem ringKrullDim_quotient_span_singleton_eq {f : R} (hf : f ≠ 0)
    (hfm : f ∈ maximalIdeal R) {e : ℕ} (hdim : ringKrullDim R = ((e + 1 : ℕ) : WithBot ℕ∞)) :
    ringKrullDim (R ⧸ Ideal.span {f}) = (e : WithBot ℕ∞) := by
  have : IsDomain R := isDomain_of_isRegularLocalRing R
  have h := ringKrullDim_quotient_span_singleton_succ_eq_ringKrullDim_of_mem_nonZeroDivisors
    (mem_nonZeroDivisors_of_ne_zero hf) hfm
  rw [hdim] at h
  have h' : ringKrullDim (R ⧸ Ideal.span {f}) + 1 = ((e + 1 : ℕ) : WithBot ℕ∞) := h
  generalize ringKrullDim (R ⧸ Ideal.span {f}) = d at h' ⊢
  induction d using WithBot.recBotCoe with
  | bot =>
    exfalso
    rw [WithBot.bot_add] at h'
    exact WithBot.coe_ne_bot (a := ((e : ℕ∞) + 1)) (by exact_mod_cast h'.symm)
  | coe d =>
    have h2 : d + 1 = ((e + 1 : ℕ) : ℕ∞) := by exact_mod_cast h'
    induction d using ENat.recTopCoe with
    | top =>
      exfalso
      exact ENat.top_ne_natCast (e + 1) (by simpa using h2.symm)
    | coe d =>
      have : d = e := by
        have : (d + 1 : ℕ) = e + 1 := by exact_mod_cast h2
        omega
      subst this
      rfl

end Hypersurface'

end Hironaka
