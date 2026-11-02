/-
Copyright (c) 2026 Daattavya Aggarwal, Minhyong Kim, Oisin Kim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daattavya Aggarwal, Minhyong Kim, Oisin Kim
-/
module

public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.RingTheory.TensorProduct.Maps
public import Hironaka.Compat.Graded
public import Hironaka.Compat.RegularGraded

/-!
# Ch. II §1, p. 183: `gr_{m̄}(Ō)` as the polynomial ring `K[X̄₁, …, X̄_r]`

> We know that gr_{m̄}(Ō) is a polynomial ring of r variables.  (p. 186)

Let `O` be a ring, `P ⊆ m` ideals with `Ō = O/P` and `m̄ = m/P`, `K = O/m = Ō/m̄`, and `ȳ` a
quasi-regular family generating `m̄` (a part of a regular system of parameters of `Ō`,
footnote 39).  This file records the presentation of `gr_{m̄}(Ō)` as a polynomial ring over `K`:

* `GrPiece.moduleQuotientMap`: the `K`-module structure on `gr^q_{m̄}(Ō)`;
* `AssocGraded.algebraQuotientMap`: `gr_{m̄}(Ō)` is a `K`-algebra (`m` acts by `0`);
* `psiTau : K[X₁, …, X_r] →ₐ[K] gr_{m̄}(Ō)`, `X_j ↦` the class of `ȳ_j` in `m̄/m̄²` (the map `τ`
  of p. 183), `psiTau_bijective`: it is an isomorphism of `K`-algebras (the polynomial ring
  `K[X̄₁, …, X̄_r]` of p. 183), `psiTau_monomial`: the image of a monomial;
* `ofGrPieceK`: `gr^q_{m̄}(Ō) → gr_{m̄}(Ō)` as a `K`-linear map;
* `finrank_grPiece_eq_natCard_of_psiTau`: "`gr_{m̄}(Ō)` is a polynomial ring of `r` variables, and
  hence `dim_K(gr^q_{m̄}(Ō))` is the number of monomials of degree `q`": `τ` maps the
  homogeneous polynomials of degree `q` onto `gr^q_{m̄}(Ō)` (`map_homogeneousSubmodule_psiTau`).

Moved here from `Hironaka/Ch2/PsiAlgebra.lean` (the first four items) so that
`Hironaka/Ch2/Flatness.lean`, which `PsiAlgebra` imports, can use them in the proof of
Corollary 2 (i).
-/

@[expose] public section

open TensorProduct

namespace Hironaka
universe u

section PsiTau

theorem AssocGraded.algebraMap_eq_zero_of_mem {A : Type u} [CommRing A] {I : Ideal A} {a : A}
    (ha : a ∈ I) : algebraMap A (AssocGraded I) a = 0 := by
  rw [AssocGraded.algebraMap_apply]
  exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_map_of_mem _ ha)

variable {O : Type u} [CommRing O] (P m : Ideal O)

/-- For ideals `P, m` of `O`, the ideal `m` of `O` annihilates `gr_{m̄}(Ō)`, `Ō = O/P`,
`m̄ = m/P` (it acts through `m̄`). -/
theorem grPiece_map_isTorsionBySet (P m : Ideal O) (q : ℕ) :
    Module.IsTorsionBySet O (GrPiece (m.map (Ideal.Quotient.mk P)) q) (m : Set O) := by
  intro x a
  rw [← IsScalarTower.algebraMap_smul (O ⧸ P) (a : O) x]
  exact @grPiece_isTorsionBySet (O ⧸ P) _ (m.map (Ideal.Quotient.mk P)) q x
    ⟨algebraMap O (O ⧸ P) a, Ideal.mem_map_of_mem _ a.2⟩

/-- The `K = O/m`-module structure on `gr^q_{m̄}(Ō)` used in Proposition 1 (p. 183: `Ō/m̄ = K`).
-/
noncomputable instance GrPiece.moduleQuotientMap (P m : Ideal O) (q : ℕ) :
    Module (O ⧸ m) (GrPiece (m.map (Ideal.Quotient.mk P)) q) :=
  (grPiece_map_isTorsionBySet P m q).module

/-- `gr_{m̄}(Ō)` is a `K = O/m`-algebra (`m` acts by `0` on `gr_{m̄}(Ō)`, `m̄ = m/P`). -/
noncomputable instance AssocGraded.algebraQuotientMap :
    Algebra (O ⧸ m) (AssocGraded (m.map (Ideal.Quotient.mk P))) :=
  (Ideal.Quotient.lift m (algebraMap O (AssocGraded (m.map (Ideal.Quotient.mk P)))) (fun a ha => by
    have h1 : algebraMap O (AssocGraded (m.map (Ideal.Quotient.mk P))) a =
        algebraMap (O ⧸ P) (AssocGraded (m.map (Ideal.Quotient.mk P))) (Ideal.Quotient.mk P a) :=
      IsScalarTower.algebraMap_apply O (O ⧸ P) _ a
    rw [h1]
    exact AssocGraded.algebraMap_eq_zero_of_mem (Ideal.mem_map_of_mem _ ha))).toAlgebra

variable {P m} (hPm : P ≤ m)

section OfGrPieceK

/-- `gr^q_{m̄}(Ō) → gr_{m̄}(Ō)`, as a `K = O/m`-linear map. -/
noncomputable def ofGrPieceK (q : ℕ) :
    GrPiece (m.map (Ideal.Quotient.mk P)) q →ₗ[O ⧸ m]
      AssocGraded (m.map (Ideal.Quotient.mk P)) where
  toFun := AssocGraded.ofGrPiece _ q
  map_add' := map_add _
  map_smul' c x := by
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective c
    induction x using Submodule.Quotient.induction_on with
    | H b =>
      rw [Algebra.smul_def, RingHom.id_apply, mul_comm]
      have h1 : algebraMap (O ⧸ m) (AssocGraded (m.map (Ideal.Quotient.mk P)))
          (Ideal.Quotient.mk m a) =
          AssocGraded.mk (m.map (Ideal.Quotient.mk P)) 0 (Ideal.Quotient.mk P a) (by simp) := by
        show algebraMap O (AssocGraded (m.map (Ideal.Quotient.mk P))) a = _
        rw [IsScalarTower.algebraMap_apply O (O ⧸ P)]
        rfl
      rw [h1]
      obtain ⟨b, hb⟩ := b
      have hs : (Ideal.Quotient.mk m a •
          (Submodule.Quotient.mk ⟨b, hb⟩ : GrPiece (m.map (Ideal.Quotient.mk P)) q)) =
          Submodule.Quotient.mk ⟨Ideal.Quotient.mk P a * b, Ideal.mul_mem_left _ _ hb⟩ := rfl
      rw [hs, AssocGraded.ofGrPiece_mk, AssocGraded.ofGrPiece_mk, AssocGraded.mk_mul_mk]
      congr 1
      exact mul_comm _ _

end OfGrPieceK

section Beta

variable {s : ℕ} (y : Fin s → O)
  (hqr : IsQuasiRegular fun j => Ideal.Quotient.mk P (y j))
  (hz : Ideal.span (Set.range fun j => Ideal.Quotient.mk P (y j)) =
    m.map (Ideal.Quotient.mk P))

include hz in
theorem mk_mem_pow_one (j : Fin s) :
    Ideal.Quotient.mk P (y j) ∈ (m.map (Ideal.Quotient.mk P)) ^ 1 := by
  rw [pow_one, ← hz]
  exact Ideal.subset_span ⟨j, rfl⟩

/-- `K[X₁, …, X_r] → gr_{m̄}(Ō)`, `X_j ↦` the class of `x̄_j = ȳ_j` in `m̄/m̄²`. -/
noncomputable def psiTau : MvPolynomial (Fin s) (O ⧸ m) →ₐ[O ⧸ m]
    AssocGraded (m.map (Ideal.Quotient.mk P)) :=
  MvPolynomial.aeval fun j => AssocGraded.mk (m.map (Ideal.Quotient.mk P)) 1
    (Ideal.Quotient.mk P (y j)) (mk_mem_pow_one y hz j)

include hPm hz in
/-- `psiTau` is `τ` over `Ō/m̄` composed with the coefficient isomorphism `K ≅ Ō/m̄`. -/
theorem psiTau_eq_comp :
    ⇑(psiTau y hz) =
      ⇑(MvPolynomial.aeval (R := (O ⧸ P) ⧸ m.map (Ideal.Quotient.mk P)) (fun j =>
        AssocGraded.mk (m.map (Ideal.Quotient.mk P)) 1 (Ideal.Quotient.mk P (y j))
          (mk_mem_pow_one y hz j))) ∘
      ⇑(MvPolynomial.map ((DoubleQuot.quotQuotEquivQuotOfLE hPm).symm : O ⧸ m →+* _)) := by
  set Q := m.map (Ideal.Quotient.mk P) with hQ
  let τ0 := MvPolynomial.aeval (R := (O ⧸ P) ⧸ Q) (fun j =>
    AssocGraded.mk Q 1 (Ideal.Quotient.mk P (y j)) (mk_mem_pow_one y hz j))
  let eK : O ⧸ m ≃+* (O ⧸ P) ⧸ Q := (DoubleQuot.quotQuotEquivQuotOfLE hPm).symm
  have h : (psiTau y hz).toRingHom = τ0.toRingHom.comp (MvPolynomial.map (eK : O ⧸ m →+* _)) := by
    refine MvPolynomial.ringHom_ext (fun c => ?_) (fun j => ?_)
    · obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective c
      simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, RingHom.coe_comp, Function.comp_apply,
        MvPolynomial.map_C, psiTau, τ0, MvPolynomial.aeval_C]
      show algebraMap (O ⧸ m) (AssocGraded Q) (Ideal.Quotient.mk m a) =
        algebraMap ((O ⧸ P) ⧸ Q) (AssocGraded Q) (eK (Ideal.Quotient.mk m a))
      rw [show eK (Ideal.Quotient.mk m a) = DoubleQuot.quotQuotMk P m a from
        DoubleQuot.quotQuotEquivQuotOfLE_symm_mk a hPm]
      show Ideal.Quotient.lift m _ _ (Ideal.Quotient.mk m a) =
        AssocGraded.algebraMapQuot Q (Ideal.Quotient.mk Q (Ideal.Quotient.mk P a))
      rw [Ideal.Quotient.lift_mk, AssocGraded.algebraMapQuot, Ideal.Quotient.lift_mk]
      exact IsScalarTower.algebraMap_apply O (O ⧸ P) _ a
    · simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, RingHom.coe_comp, Function.comp_apply,
        MvPolynomial.map_X, psiTau, τ0, MvPolynomial.aeval_X]
      rfl
  exact congrArg DFunLike.coe h

include hPm hqr hz in
/-- `K[X₁, …, X_r] → gr_{m̄}(Ō)` is an isomorphism: `gr_{m̄}(Ō)` is a polynomial ring in the
classes of the `x̄_j` (p. 183: "`gr_{m̄}(Ō)` can be identified with the polynomial ring
`K[X̄₁, …, X̄_r]`"; regular system of parameters, footnote 39). -/
theorem psiTau_bijective : Function.Bijective (psiTau y hz) := by
  have hτ0 : Function.Bijective (MvPolynomial.aeval
      (R := (O ⧸ P) ⧸ m.map (Ideal.Quotient.mk P)) (fun j =>
      AssocGraded.mk (m.map (Ideal.Quotient.mk P)) 1 (Ideal.Quotient.mk P (y j))
        (mk_mem_pow_one y hz j))) :=
    ⟨aeval_mk_injective_of_isQuasiRegular _ _ (mk_mem_pow_one y hz) hqr hz,
      aeval_mk_surjective _ _ (mk_mem_pow_one y hz) hz⟩
  rw [psiTau_eq_comp hPm y hz]
  exact hτ0.comp ⟨MvPolynomial.map_injective _
    (DoubleQuot.quotQuotEquivQuotOfLE hPm).symm.injective,
    MvPolynomial.map_surjective _ (DoubleQuot.quotQuotEquivQuotOfLE hPm).symm.surjective⟩

include hPm hz in
theorem psiTau_monomial (α : Fin s →₀ ℕ) {d : ℕ} (hd : α.degree = d)
    (h : (α.prod fun j e => Ideal.Quotient.mk P (y j) ^ e) ∈
      (m.map (Ideal.Quotient.mk P)) ^ d) :
    psiTau y hz (MvPolynomial.monomial α 1) =
      AssocGraded.mk (m.map (Ideal.Quotient.mk P)) d
        (α.prod fun j e => Ideal.Quotient.mk P (y j) ^ e) h := by
  subst hd
  have h1 := congrFun (psiTau_eq_comp hPm y hz) (MvPolynomial.monomial α 1)
  have he : ((DoubleQuot.quotQuotEquivQuotOfLE hPm).symm :
      O ⧸ m →+* (O ⧸ P) ⧸ m.map (Ideal.Quotient.mk P)) 1 = 1 := map_one _
  rw [Function.comp_apply, MvPolynomial.map_monomial, he] at h1
  rw [h1]
  have h2 := aeval_mk_map_of_isHomogeneous (m.map (Ideal.Quotient.mk P))
    (fun j => Ideal.Quotient.mk P (y j)) (mk_mem_pow_one y hz)
    (K := MvPolynomial.monomial α (1 : O ⧸ P)) (d := α.degree)
    (MvPolynomial.isHomogeneous_monomial _ rfl)
  have h3 : (Ideal.Quotient.mk (m.map (Ideal.Quotient.mk P)) :
      O ⧸ P →+* (O ⧸ P) ⧸ m.map (Ideal.Quotient.mk P)) 1 = 1 := map_one _
  rw [MvPolynomial.map_monomial] at h2
  rw [h3] at h2
  rw [h2]
  congr 1
  simp [MvPolynomial.eval_monomial]

include hPm hz in
/-- `τ` maps the homogeneous polynomials of degree `q` into `gr^q_{m̄}(Ō)`: the image of the
monomial `X^α`, `|α| = q`, is the class of `ȳ^α` in `m̄^q/m̄^{q+1}` (`psiTau_monomial`). -/
theorem psiTau_mem_range_ofGrPieceK (q : ℕ) {φ : MvPolynomial (Fin s) (O ⧸ m)}
    (hφ : φ.IsHomogeneous q) :
    psiTau y hz φ ∈ LinearMap.range (ofGrPieceK (P := P) (m := m) q) := by
  rw [← MvPolynomial.mem_homogeneousSubmodule,
    MvPolynomial.homogeneousSubmodule_eq_finsupp_supported,
    AddMonoidAlgebra.supported_eq_span_single] at hφ
  induction hφ using Submodule.span_induction with
  | mem φ hφ =>
    obtain ⟨α, hα, rfl⟩ := hφ
    have hα' : α.degree = q := hα
    have hmem : (α.prod fun j e => Ideal.Quotient.mk P (y j) ^ e) ∈
        (m.map (Ideal.Quotient.mk P)) ^ q := by
      rw [← hz, ← hα']
      refine (Ideal.mem_span_pow_iff_exists_isHomogeneous
        (fun j => Ideal.Quotient.mk P (y j)) _).mpr
        ⟨MvPolynomial.monomial α 1, MvPolynomial.isHomogeneous_monomial 1 rfl, ?_⟩
      rw [MvPolynomial.eval_monomial, one_mul]
    show psiTau y hz (MvPolynomial.monomial α 1) ∈ _
    rw [psiTau_monomial hPm y hz α hα' hmem]
    exact ⟨Submodule.Quotient.mk ⟨_, hmem⟩, rfl⟩
  | zero => rw [map_zero]; exact zero_mem _
  | add a b _ _ ha hb => rw [map_add]; exact add_mem ha hb
  | smul c a _ ha =>
    rw [map_smul]
    exact Submodule.smul_mem _ c ha

include hPm hz in
/-- Every element of `gr^q_{m̄}(Ō)` is the image under `τ` of a homogeneous polynomial of degree
`q` (the presentation of `gr_{m̄}(Ō)` by the classes of the generators `ȳ_j` of `m̄`; this is the
proof of `aeval_mk_surjective` kept track of degrees). -/
theorem exists_isHomogeneous_psiTau_eq_mk (q : ℕ) (a : O ⧸ P)
    (ha : a ∈ (m.map (Ideal.Quotient.mk P)) ^ q) :
    ∃ φ : MvPolynomial (Fin s) (O ⧸ m), φ.IsHomogeneous q ∧
      psiTau y hz φ = AssocGraded.mk (m.map (Ideal.Quotient.mk P)) q a ha := by
  set Q := m.map (Ideal.Quotient.mk P) with hQ
  obtain ⟨F, hF, rfl⟩ := (Ideal.mem_span_pow_iff_exists_isHomogeneous
    (fun j => Ideal.Quotient.mk P (y j)) a).mp (by rw [hz]; exact ha)
  let eK : O ⧸ m ≃+* (O ⧸ P) ⧸ Q := (DoubleQuot.quotQuotEquivQuotOfLE hPm).symm
  refine ⟨F.map ((eK.symm : (O ⧸ P) ⧸ Q →+* O ⧸ m).comp (Ideal.Quotient.mk Q)), hF.map _, ?_⟩
  have h1 := congrFun (psiTau_eq_comp hPm y hz)
    (F.map ((eK.symm : (O ⧸ P) ⧸ Q →+* O ⧸ m).comp (Ideal.Quotient.mk Q)))
  rw [Function.comp_apply, MvPolynomial.map_map] at h1
  have h2 : (eK : O ⧸ m →+* (O ⧸ P) ⧸ Q).comp
      ((eK.symm : (O ⧸ P) ⧸ Q →+* O ⧸ m).comp (Ideal.Quotient.mk Q)) = Ideal.Quotient.mk Q := by
    ext x
    simp
  rw [h1]
  have h3 : ((DoubleQuot.quotQuotEquivQuotOfLE hPm).symm : O ⧸ m →+* (O ⧸ P) ⧸ Q).comp
      ((eK.symm : (O ⧸ P) ⧸ Q →+* O ⧸ m).comp (Ideal.Quotient.mk Q)) =
      Ideal.Quotient.mk Q := h2
  rw [h3]
  exact aeval_mk_map_of_isHomogeneous Q (fun j => Ideal.Quotient.mk P (y j))
    (mk_mem_pow_one y hz) hF

include hPm hz in
/-- `τ` maps the `K`-module of homogeneous polynomials of degree `q` onto `gr^q_{m̄}(Ō)`
(inside `gr_{m̄}(Ō)`). -/
theorem map_homogeneousSubmodule_psiTau (q : ℕ) :
    (MvPolynomial.homogeneousSubmodule (Fin s) (O ⧸ m) q).map (psiTau y hz).toLinearMap =
      LinearMap.range (ofGrPieceK (P := P) (m := m) q) := by
  refine le_antisymm ?_ ?_
  · rintro _ ⟨φ, hφ, rfl⟩
    exact psiTau_mem_range_ofGrPieceK hPm y hz q hφ
  · rintro _ ⟨b, rfl⟩
    induction b using Submodule.Quotient.induction_on with
    | H b =>
      obtain ⟨a, ha⟩ := b
      obtain ⟨φ, hφ, hφa⟩ := exists_isHomogeneous_psiTau_eq_mk hPm y hz q a ha
      exact ⟨φ, hφ, hφa⟩

include hPm hqr hz in
/-- "`gr_{m̄}(Ō)` is a polynomial ring of `r` variables, and hence `dim_K(gr^q_{m̄}(Ō))` is the number
of monomials of degree `q`" (p. 186): `K[X̄] ≅ gr_{m̄}(Ō)` (`psiTau_bijective`) maps the homogeneous
polynomials of degree `q` onto `gr^q_{m̄}(Ō)` (`map_homogeneousSubmodule_psiTau`). -/
theorem finrank_grPiece_eq_natCard_of_psiTau (hm : m ≠ ⊤) (q : ℕ) :
    Module.finrank (O ⧸ m) (GrPiece (m.map (Ideal.Quotient.mk P)) q) =
      Nat.card {α : Fin s →₀ ℕ // α.degree = q} := by
  have : Nontrivial (O ⧸ m) := Ideal.Quotient.nontrivial_iff.mpr hm
  have hinj : Function.Injective (ofGrPieceK (P := P) (m := m) q) := fun a b h =>
    AssocGraded.ofGrPiece_injective _ q h
  have hτ : Function.Injective (psiTau y hz).toLinearMap :=
    (psiTau_bijective hPm y hqr hz).1
  rw [LinearEquiv.finrank_eq (LinearEquiv.ofInjective _ hinj),
    ← map_homogeneousSubmodule_psiTau hPm y hz q,
    ← LinearEquiv.finrank_eq (Submodule.equivMapOfInjective _ hτ _)]
  have : Fintype ↑{d : Fin s →₀ ℕ | d.degree = q} := (Finsupp.finite_of_degree_eq q).fintype
  rw [MvPolynomial.homogeneousSubmodule_eq_finsupp_supported,
    LinearEquiv.finrank_eq (AddMonoidAlgebra.supportedEquivFinsupp
      (R := O ⧸ m) (S := O ⧸ m) {d : Fin s →₀ ℕ | d.degree = q}), Module.finrank_finsupp_self]
  exact (Nat.card_eq_fintype_card).symm

end Beta

end PsiTau

end Hironaka
