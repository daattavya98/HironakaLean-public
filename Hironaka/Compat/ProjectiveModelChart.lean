/-
Copyright (c) 2026 Daattavya Aggarwal, Minhyong Kim, Oisin Kim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daattavya Aggarwal, Minhyong Kim, Oisin Kim
-/
module

public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper
public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Defs
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Ideal
public import Hironaka.Compat.ProjectiveVocabularyProper
public import Hironaka.Compat.FunctionFieldMap

/-!
# A projective integral model of a finitely generated field (for the Corollary of Main Theorem I, p. 132)

> COROLLARY. If `L` is a finitely generated field over a field of characteristic zero, say `B`, then there exists an
> irreducible non-singular projective algebraic `B`-scheme whose function field is `B`-isomorphic to `L`.  (p. 132)

The paper calls the Corollary "an immediate consequence of our main theorem I" and does not say where the projective
model to be resolved comes from.  This file builds it (gap filled):
for `L = B(x₁, …, xₙ)`,
* `coneMap B x : B[T₀, …, Tₙ] → L[t]`, `T₀ ↦ t`, `Tᵢ ↦ xᵢ t`, maps a form of degree `d` to `c t^d`
  (`coneMap_of_isHomogeneous`), so its kernel `coneIdeal B x` is a homogeneous prime ideal;
* `H = B[T] ⧸ coneIdeal B x` (the homogeneous coordinate ring of the closure of `(x₁, …, xₙ)` in `P^n`) is a graded
  domain, embedded in `L[t]`, with dehomogenization `coneDehom B x : H → L`, `T₀ ↦ 1`, `Tᵢ ↦ xᵢ`;
* `Proj H` is integral (`zero` is its generic point, the stalks are subrings of localizations of the domain `H`);
* the chart `D₊(T₀) = Spec H_(T₀)` has `H_(T₀) ≅ B[x₁, …, xₙ] ⊂ L` (`chartMap x`), whose fraction field is `L`, so the
  function field of `Proj H` is `B`-isomorphic to `L` (`exists_functionField_equiv`).
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory MvPolynomial

namespace Hironaka

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

namespace ProjectiveModel

variable {B : Type u} [Field B] {L : Type u} [Field L] [Algebra B L] {n : ℕ} (x : Fin n → L)

/-! ### The cone map and its kernel -/

/-- The affine coordinates `(1, x₁, …, xₙ)`. -/
def coords : Fin (n + 1) → L := Fin.cons 1 x

variable (B) in
/-- `B[T₀, …, Tₙ] → L[t]`, `Tᵢ ↦ yᵢ t` with `y = (1, x₁, …, xₙ)`. -/
noncomputable def coneMap : MvPolynomial (Fin (n + 1)) B →ₐ[B] Polynomial L :=
  aeval fun i => Polynomial.C (coords x i) * Polynomial.X

/-- The cone map on a monomial: `c T^m ↦ c y^m t^{|m|}`. -/
theorem coneMap_monomial (m : Fin (n + 1) →₀ ℕ) (c : B) :
    coneMap B x (monomial m c) =
      Polynomial.C (aeval (coords x) (monomial m c)) * Polynomial.X ^ m.degree := by
  rw [coneMap, aeval_monomial, aeval_monomial, Polynomial.algebraMap_apply, Finsupp.prod, Finsupp.prod]
  simp only [mul_pow, Finset.prod_mul_distrib, ← Polynomial.C_pow, ← map_prod, map_mul,
    Finset.prod_pow_eq_pow_sum, Finsupp.degree_apply]
  ring

/-- A form of degree `d` is mapped to `c t^d`, `c` its value at `(1, x₁, …, xₙ)`. -/
theorem coneMap_of_isHomogeneous {p : MvPolynomial (Fin (n + 1)) B} {d : ℕ} (hp : p.IsHomogeneous d) :
    coneMap B x p = Polynomial.C (aeval (coords x) p) * Polynomial.X ^ d := by
  conv_lhs => rw [p.as_sum]
  conv_rhs => rw [p.as_sum]
  rw [map_sum, map_sum, map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun m hm => ?_
  rw [coneMap_monomial]
  congr 2
  have := hp (mem_support_iff.mp hm)
  rw [Finsupp.degree_eq_weight_one]
  exact this

/-- The graded decomposition of `B[T]` is by homogeneous components. -/
theorem decompose_eq_homogeneousComponent (p : MvPolynomial (Fin (n + 1)) B) (d : ℕ) :
    (DirectSum.decompose (homogeneousSubmodule (Fin (n + 1)) B) p d : MvPolynomial (Fin (n + 1)) B) =
      homogeneousComponent d p :=
  decomposition.decompose'_apply p d

/-- The kernel of the cone map is homogeneous. -/
theorem isHomogeneous_ker_coneMap :
    (RingHom.ker (coneMap B x)).IsHomogeneous (homogeneousSubmodule (Fin (n + 1)) B) := by
  intro d p hp
  rw [decompose_eq_homogeneousComponent]
  change coneMap B x _ = 0
  rw [coneMap_of_isHomogeneous x (homogeneousComponent_isHomogeneous d p)]
  by_cases hd : d ∈ Finset.range (p.totalDegree + 1)
  · have h0 : coneMap B x p = 0 := hp
    rw [← sum_homogeneousComponent p, map_sum] at h0
    have h1 := congrArg (fun q => Polynomial.coeff q d) h0
    simp only [Polynomial.finsetSum_coeff, Polynomial.coeff_zero] at h1
    rw [Finset.sum_eq_single d] at h1
    · rw [coneMap_of_isHomogeneous x (homogeneousComponent_isHomogeneous d p),
        Polynomial.coeff_C_mul_X_pow, ite_eq_left_iff.mpr (fun h => absurd rfl h)] at h1
      rw [h1, map_zero, zero_mul]
    · intro i _ hid
      rw [coneMap_of_isHomogeneous x (homogeneousComponent_isHomogeneous i p),
        Polynomial.coeff_C_mul_X_pow, ite_eq_right_iff.mpr (fun h => absurd h.symm hid)]
    · intro h; exact absurd hd h
  · rw [homogeneousComponent_eq_zero d p (by simpa [Nat.lt_succ_iff] using hd), map_zero,
      map_zero, zero_mul]

variable (B) in
/-- The homogeneous prime ideal of the cone over `(1 : x₁ : … : xₙ)`. -/
noncomputable def coneIdeal : HomogeneousIdeal (homogeneousSubmodule (Fin (n + 1)) B) where
  toSubmodule := RingHom.ker (coneMap B x)
  is_homogeneous' := isHomogeneous_ker_coneMap x

/-- Membership in the cone ideal. -/
theorem mem_coneIdeal {p : MvPolynomial (Fin (n + 1)) B} : p ∈ (coneIdeal B x).toIdeal ↔ coneMap B x p = 0 :=
  Iff.rfl

/-- The cone ideal is prime (the kernel of a map into the domain `L[t]`). -/
instance isPrime_coneIdeal : (coneIdeal B x).toIdeal.IsPrime :=
  RingHom.ker_isPrime (coneMap B x)

variable (B) in
/-- The homogeneous coordinate ring `H = B[T₀, …, Tₙ] ⧸ 𝔞`. -/
abbrev ConeRing := MvPolynomial (Fin (n + 1)) B ⧸ (coneIdeal B x).toIdeal

/-- `H` is a domain. -/
instance : IsDomain (ConeRing B x) := Ideal.Quotient.isDomain _

variable (B) in
/-- The embedding `H ↪ L[t]`. -/
noncomputable def coneLift : ConeRing B x →+* Polynomial L :=
  Ideal.Quotient.lift _ (coneMap B x).toRingHom fun _ ha => ha

/-- The embedding `H ↪ L[t]` on classes. -/
theorem coneLift_mk (p : MvPolynomial (Fin (n + 1)) B) :
    coneLift B x (Ideal.Quotient.mk _ p) = coneMap B x p := rfl

/-- `H → L[t]` is injective. -/
theorem coneLift_injective : Function.Injective (coneLift B x) := by
  rw [injective_iff_map_eq_zero]
  intro a ha
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective a
  exact Ideal.Quotient.eq_zero_iff_mem.mpr ha

variable (B) in
/-- The dehomogenization `H → L`, `T₀ ↦ 1`, `Tᵢ ↦ xᵢ`. -/
noncomputable def coneDehom : ConeRing B x →+* L :=
  (Polynomial.evalRingHom 1).comp (coneLift B x)

/-- The dehomogenization on classes: evaluation at `(1, x₁, …, xₙ)`. -/
theorem coneDehom_mk (p : MvPolynomial (Fin (n + 1)) B) :
    coneDehom B x (Ideal.Quotient.mk _ p) = aeval (coords x) p := by
  have h : (Polynomial.evalRingHom (1 : L)).comp (coneMap B x).toRingHom = (aeval (coords x)).toRingHom :=
    MvPolynomial.ringHom_ext (fun b => by simp [coneMap, Polynomial.algebraMap_apply])
      (fun i => by simp [coneMap])
  exact congrArg (fun f => f p) h

/-- The dehomogenization is a `B`-algebra map. -/
theorem coneDehom_algebraMap (b : B) : coneDehom B x (algebraMap B (ConeRing B x) b) = algebraMap B L b := by
  rw [IsScalarTower.algebraMap_apply B (MvPolynomial (Fin (n + 1)) B) (ConeRing B x),
    Ideal.Quotient.algebraMap_eq, coneDehom_mk, MvPolynomial.algebraMap_eq, aeval_C]

variable (B) in
/-- The homogeneous coordinate `Tᵢ` in `H`. -/
noncomputable def var (i : Fin (n + 1)) : ConeRing B x := Ideal.Quotient.mk _ (X i)

/-- The coordinates `Tᵢ` have degree one. -/
theorem var_mem (i : Fin (n + 1)) : var B x i ∈ quotientGrading (coneIdeal B x) 1 :=
  mk_mem_quotientGrading _ (isHomogeneous_X B i)

/-- `δ(T₀) = 1`. -/
theorem coneDehom_var_zero : coneDehom B x (var B x 0) = 1 := by
  rw [var, coneDehom_mk, aeval_X]; rfl

/-- `δ(Tᵢ) = xᵢ`. -/
theorem coneDehom_var_succ (i : Fin n) : coneDehom B x (var B x i.succ) = x i := by
  rw [var, coneDehom_mk, aeval_X]; rfl

/-- On `H_d`, the embedding into `L[t]` is `a ↦ δ(a) t^d`. -/
theorem coneLift_of_mem {a : ConeRing B x} {d : ℕ} (ha : a ∈ quotientGrading (coneIdeal B x) d) :
    coneLift B x a = Polynomial.C (coneDehom B x a) * Polynomial.X ^ d := by
  obtain ⟨p, hp, rfl⟩ := ha
  change coneLift B x (Ideal.Quotient.mk _ p) = Polynomial.C (coneDehom B x (Ideal.Quotient.mk _ p)) * _
  rw [coneDehom_mk, coneLift_mk, coneMap_of_isHomogeneous x hp]

/-- A homogeneous element with dehomogenization `0` is `0`. -/
theorem eq_zero_of_coneDehom_eq_zero {a : ConeRing B x} {d : ℕ} (ha : a ∈ quotientGrading (coneIdeal B x) d)
    (h : coneDehom B x a = 0) : a = 0 :=
  coneLift_injective (B := B) x (by rw [coneLift_of_mem x ha, h, map_zero, zero_mul, map_zero])

/-- `T₀ ≠ 0` in `H`. -/
theorem var_zero_ne_zero : var B x 0 ≠ 0 := fun h => by
  have := coneDehom_var_zero (B := B) x
  rw [h, map_zero] at this
  exact zero_ne_one this

/-! ### `Proj H` is integral -/

variable (B) in
/-- The zero ideal of the graded domain `H`, a point of `Proj H` (its generic point). -/
noncomputable def genericPt : ProjectiveSpectrum (quotientGrading (coneIdeal B x)) where
  asHomogeneousIdeal := ⊥
  isPrime := by rw [HomogeneousIdeal.toIdeal_bot]; exact Ideal.isPrime_bot
  not_irrelevant_le h := var_zero_ne_zero (B := B) x (by
    have h1 : var B x 0 ∈ (⊥ : HomogeneousIdeal (quotientGrading (coneIdeal B x))).toIdeal :=
      h (HomogeneousIdeal.mem_irrelevant_of_mem _ one_pos (var_mem x 0))
    rw [HomogeneousIdeal.toIdeal_bot] at h1
    exact (Submodule.mem_bot _).mp h1)

/-- `Proj H` is irreducible: the zero ideal is a generic point. -/
instance irreducibleSpace_proj : IrreducibleSpace (Proj (quotientGrading (coneIdeal B x))) := by
  have h : closure ({genericPt B x} : Set (ProjectiveSpectrum (quotientGrading (coneIdeal B x)))) =
      Set.univ := by
    refine Set.eq_univ_of_forall fun y => (ProjectiveSpectrum.le_iff_mem_closure _ _ y).mp ?_
    show (⊥ : HomogeneousIdeal _) ≤ y.asHomogeneousIdeal
    exact bot_le
  have h2 := (isIrreducible_singleton (x := genericPt B x)).closure
  rw [h] at h2
  exact (irreducibleSpace_def _).mpr h2

/-- The local rings of `Proj H` are reduced (subrings of localizations of the domain `H`). -/
instance isReduced_stalk_proj (y : Proj (quotientGrading (coneIdeal B x))) :
    _root_.IsReduced ((Proj (quotientGrading (coneIdeal B x))).presheaf.stalk y) := by
  have : y.asHomogeneousIdeal.toIdeal.IsPrime := y.isPrime
  have : _root_.IsReduced (HomogeneousLocalization.AtPrime (quotientGrading (coneIdeal B x))
      y.asHomogeneousIdeal.toIdeal) :=
    isReduced_of_injective (algebraMap _ (Localization.AtPrime y.asHomogeneousIdeal.toIdeal))
      (HomogeneousLocalization.val_injective _)
  exact isReduced_of_injective (Proj.stalkIso (quotientGrading (coneIdeal B x)) y).hom.hom
    (ConcreteCategory.bijective_of_isIso (Proj.stalkIso _ y).hom).1

/-- `Proj H` is reduced. -/
instance isReduced_proj : IsReduced (Proj (quotientGrading (coneIdeal B x))) :=
  isReduced_of_isReduced_stalk _

/-- `Proj H` is integral. -/
instance isIntegral_proj : IsIntegral (Proj (quotientGrading (coneIdeal B x))) :=
  isIntegral_of_irreducibleSpace_of_isReduced _

/-! ### The chart `D₊(T₀)` and the function field -/

/-- `T₀` has degree one. -/
theorem var_zero_mem : var B x 0 ∈ quotientGrading (coneIdeal B x) 1 := var_mem x 0

variable (B) in
/-- The chart ring `H_(T₀) → L`, `a/T₀^k ↦ δ(a)`; its image is `B[x₁, …, xₙ]`. -/
noncomputable def chartMap :
    HomogeneousLocalization.Away (quotientGrading (coneIdeal B x)) (var B x 0) →+* L :=
  (IsLocalization.Away.lift (var B x 0) (g := coneDehom B x)
    (by rw [coneDehom_var_zero]; exact isUnit_one)).comp
    (algebraMap _ (Localization.Away (var B x 0)))

/-- The chart map on `a/T₀^k` is `δ(a)`. -/
theorem chartMap_mk {k : ℕ} {a : ConeRing B x} (ha : a ∈ quotientGrading (coneIdeal B x) (k • 1)) :
    chartMap B x (HomogeneousLocalization.Away.mk _ (var_zero_mem x) k a ha) = coneDehom B x a := by
  rw [chartMap, RingHom.comp_apply, HomogeneousLocalization.algebraMap_apply,
    HomogeneousLocalization.Away.val_mk, Localization.mk_eq_mk', IsLocalization.Away.lift,
    IsLocalization.lift_mk'_spec]
  simp [map_pow, coneDehom_var_zero]

/-- The chart map on degree-zero elements `c/1` is `δ(c)`. -/
theorem chartMap_fromZero (c : quotientGrading (coneIdeal B x) 0) :
    chartMap B x (HomogeneousLocalization.fromZeroRingHom _ _ c) = coneDehom B x c := by
  rw [chartMap, RingHom.comp_apply, HomogeneousLocalization.algebraMap_apply]
  have : (HomogeneousLocalization.fromZeroRingHom _ (Submonoid.powers (var B x 0)) c).val =
      algebraMap _ (Localization.Away (var B x 0)) (c : ConeRing B x) := by
    rw [← Localization.mk_one_eq_algebraMap]
    rfl
  rw [this]
  exact IsLocalization.lift_eq _ _

/-- The chart map is compatible with `B`. -/
theorem chartMap_algebraMap (b : B) :
    chartMap B x (HomogeneousLocalization.fromZeroRingHom _ _
      (algebraMap B (quotientGrading (coneIdeal B x) 0) b)) = algebraMap B L b := by
  rw [chartMap_fromZero]
  exact coneDehom_algebraMap x b

/-- The chart map `H_(T₀) → L` is injective. -/
theorem chartMap_injective : Function.Injective (chartMap B x) := by
  rw [injective_iff_map_eq_zero]
  intro y hy
  obtain ⟨k, a, ha, rfl⟩ := HomogeneousLocalization.Away.mk_surjective _ (var_zero_mem x) y
  rw [chartMap_mk] at hy
  have h0 := eq_zero_of_coneDehom_eq_zero x ha hy
  subst h0
  apply HomogeneousLocalization.val_injective
  simp only [HomogeneousLocalization.Away.val_mk, HomogeneousLocalization.val_zero]
  exact Localization.mk_zero _

/-- The chart ring `H_(T₀)` is a domain. -/
instance : IsDomain (HomogeneousLocalization.Away (quotientGrading (coneIdeal B x)) (var B x 0)) :=
  (chartMap_injective x).isDomain

/-- The chart ring `H_(T₀)` is a domain (as a `CommRingCat`). -/
instance : IsDomain
    (CommRingCat.of (HomogeneousLocalization.Away (quotientGrading (coneIdeal B x)) (var B x 0))) :=
  (chartMap_injective x).isDomain

/-- The chart map sends `Tᵢ/T₀` to `xᵢ`. -/
theorem chartMap_var_succ (i : Fin n) :
    chartMap B x (HomogeneousLocalization.Away.mk _ (var_zero_mem x) 1 (var B x i.succ)
      (by rw [smul_eq_mul, one_mul]; exact var_mem x i.succ)) = x i := by
  rw [chartMap_mk, coneDehom_var_succ]

/-- `B[x₁, …, xₙ]` lies in the image of the chart ring. -/
theorem adjoin_le_range_chartMap :
    ∀ z ∈ Algebra.adjoin B (Set.range x), z ∈ (chartMap B x).range := by
  let S : Subalgebra B L :=
    { (chartMap B x).range with
      algebraMap_mem' := fun b => ⟨_, chartMap_algebraMap x b⟩ }
  have hS : Algebra.adjoin B (Set.range x) ≤ S := by
    rw [Algebra.adjoin_le_iff]
    rintro _ ⟨i, rfl⟩
    exact ⟨_, chartMap_var_succ x i⟩
  exact fun z hz => hS hz

/-- If `L = B(x₁, …, xₙ)`, every element of `L` is a quotient of two elements of the image of the chart ring. -/
theorem exists_eq_div_chartMap (hx : IntermediateField.adjoin B (Set.range x) = ⊤) (z : L) :
    ∃ a b, z = chartMap B x a / chartMap B x b := by
  have hz : z ∈ IntermediateField.adjoin B (Set.range x) := hx ▸ IntermediateField.mem_top
  obtain ⟨r, hr, s, hs, rfl⟩ := IntermediateField.mem_adjoin_iff_div.mp hz
  obtain ⟨r', rfl⟩ := adjoin_le_range_chartMap x r hr
  obtain ⟨s', rfl⟩ := adjoin_le_range_chartMap x s hs
  exact ⟨r', s', rfl⟩

/-- The chart `D₊(T₀) = Spec H_(T₀) → Proj H` over `B`. -/
theorem awayι_projStructure :
    Proj.awayι (quotientGrading (coneIdeal B x)) (var B x 0) (var_zero_mem x) one_pos ≫
        projStructure (coneIdeal B x) =
      Spec.map (CommRingCat.ofHom ((HomogeneousLocalization.fromZeroRingHom _ _).comp
        (algebraMap B (quotientGrading (coneIdeal B x) 0)))) := by
  rw [projStructure, Proj.awayι_toSpecZero_assoc, ← Spec.map_comp]
  rfl

/-- **The function field of `Proj H` is `B`-isomorphic to `L = B(x₁, …, xₙ)`.** -/
theorem exists_functionField_equiv (hx : IntermediateField.adjoin B (Set.range x) = ⊤) :
    ∃ e : (Proj (quotientGrading (coneIdeal B x))).functionField ≃+* L,
      ∀ b, e (functionFieldAlgebraMap (projStructure (coneIdeal B x)) b) = algebraMap B L b :=
  exists_functionField_equiv_of_isOpenImmersion
    (CommRingCat.of (HomogeneousLocalization.Away (quotientGrading (coneIdeal B x)) (var B x 0)))
    (projStructure (coneIdeal B x))
    (Proj.awayι (quotientGrading (coneIdeal B x)) (var B x 0) (var_zero_mem x) one_pos) _
    (awayι_projStructure x) (chartMap B x) (chartMap_injective x) (exists_eq_div_chartMap x hx)
    (chartMap_algebraMap x)

end ProjectiveModel

end Hironaka
