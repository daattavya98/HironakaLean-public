/-
Copyright (c) 2026 Daattavya Aggarwal, Minhyong Kim, Oisin Kim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daattavya Aggarwal, Minhyong Kim, Oisin Kim
-/
module

public import Mathlib.RingTheory.TensorProduct.Maps
public import Architect
public import Hironaka.Compat.GradedLocalization
public import Hironaka.Compat.GradedPolynomialPresentation
public import Hironaka.Ch2.Flatness

/-!
# Ch. II §1, Proposition 1 (p. 184): `ψ` as one isomorphism of graded `K`-algebras

> Let O be a local ring and P, m prime ideals in O such that m contains P and O/P, O/m are regular
> local rings. Let Ō = O/P and m̄ = m/P. Let K = O/m = Ō/m̄. If gr_P(O) is flat over Ō, then
> (1) the homomorphism of graded K-algebras, obtained as above,
> ψ: gr⁰_{m̄}(gr_P(O)) ⊗_K gr_{m̄}(Ō) → gr_m(O)
> is an isomorphism.  (2) gr_m(O) is flat over K.  (p. 184)

The map `ψ = α ⊗ β*` is built on p. 183 from a system `x₁, …, x_r ∈ m` inducing a minimal base of
`m̄`: `α : gr⁰_{m̄}(gr_P(O)) → gr_m(O)` is induced by the injections `Pᵐ ⊆ mᵐ` (whose kernel
contains `m̄ gr_P(O)`), and `β* : gr_{m̄}(Ō) → gr_m(O)` is the inverse of the isomorphism of the
subalgebra `T = K[X₁, …, X_r] ⊆ gr_m(O)` onto `gr_{m̄}(Ō)` induced by `β : gr_m(O) → gr_{m̄}(Ō)`,
`X̄_j ↦ X_j`.  `Hironaka/Ch2/Flatness.lean` constructs `ψ` degree by degree (`psiDeg`, in each
total degree `n`, as the sum over `p + q = n` of the maps `ψ_{p,q}`) and proves that each `ψ_n` is
bijective (`psiDeg_bijective_of_isNormallyFlatAlongIdeal`).  This file builds `ψ` as one
homomorphism of `K`-algebras

  `psiAlgHom : gr⁰_{m̄}(gr_P(O)) ⊗_K gr_{m̄}(Ō) →ₐ[K] gr_m(O)`, `ψ = α ⊗ β*`,

where `gr⁰_{m̄}(gr_P(O)) = gr_P(O)/m gr_P(O)` is the ring `GrZeroAlg P m`, `α = psiAlpha` is
`Ideal.Quotient.lift` of the homomorphism `gr_P(O) → gr_m(O)` induced by the inclusions of the
powers (`grInclusion`, from `AssocGraded.mapLE`), and `β* = psiBeta` is `K[X̄] → gr_m(O)`,
`X̄_j ↦ [y_j]`, precomposed with the inverse of the polynomial presentation
`K[X̄] ≅ gr_{m̄}(Ō)` (`psiTau_bijective`, the classes of the regular system of parameters `ȳ` of `Ō`
generating `m̄`, footnote 39; `psiTau` and the `K`-algebra structure of `gr_{m̄}(Ō)` are in
`Hironaka/Compat/GradedPolynomialPresentation.lean`, so that `Flatness` can use them).  The statement is then

* `psiBetaProj` (`β`), `psiBetaProj_psiBeta`, `range_psiBeta`, `psiBeta_psiBetaProj`: `β*` is a
  section of `β` with image the subalgebra `T`, and the inverse of the isomorphism
  `β|_T : T → gr_{m̄}(Ō)`
  (the printed definition of `β*`);
* `psiAlgHom_tmul_grPiece`: `ψ` sends the bidegree `(p, q)` part to total degree `p + q`, by the
  component `ψ_{p,q}` (`psiPiece`) of `Hironaka/Ch2/Flatness.lean`;
* `psiAlgHom_bijective`: assertion (1), `ψ` is an isomorphism, from the bijectivity of the
  `ψ_n` (the diagram `psiAlgHom_comp_psiTotal`);
* `map_psiDegPart_eq_homogeneous`: `ψ` is graded, it maps the total degree `n` part of the source
  onto `grⁿ_m(O)`;
* `psiAlgEquiv`: the isomorphism of `K`-algebras, with the grading statement
  `comap_homogeneous_eq_psiDegPart`.
-/

@[expose] public section

open TensorProduct
open scoped DirectSum

namespace Hironaka
universe u

section PsiAlgebra

variable {O : Type u} [CommRing O] (P m : Ideal O)

/-- `gr⁰_{m̄}(gr_P(O)) = gr_P(O)/m·gr_P(O)`, the ring quotient of `gr_P(O)` by the ideal generated
by `m` (acting through `O → O/P → gr_P(O)`). -/
abbrev GrZeroAlg : Type u := AssocGraded P ⧸ Ideal.map (algebraMap O (AssocGraded P)) m

/-- `gr⁰_{m̄}(gr_P(O))` is a `K = O/m`-algebra. -/
noncomputable instance GrZeroAlg.algebra : Algebra (O ⧸ m) (GrZeroAlg P m) :=
  Ideal.Quotient.algebraQuotientOfLEComap (Ideal.le_comap_map)

theorem GrZeroAlg.algebraMap_apply (a : O) :
    algebraMap (O ⧸ m) (GrZeroAlg P m) (Ideal.Quotient.mk m a) =
      Ideal.Quotient.mk _ (algebraMap O (AssocGraded P) a) := rfl

variable {P m} (hPm : P ≤ m)

/-- The ring homomorphism `gr_P(O) → gr_m(O)` induced by the inclusions `Pᵖ ⊆ mᵖ` (p. 183). -/
noncomputable def grInclusion : AssocGraded P →+* AssocGraded m :=
  AssocGraded.mapLE (RingHom.id O) P m (by rw [Ideal.map_id]; exact hPm)

theorem grInclusion_mk (n : ℕ) (a : O) (ha : a ∈ P ^ n) :
    grInclusion hPm (AssocGraded.mk P n a ha) =
      AssocGraded.mk m n a (Ideal.pow_right_mono hPm n ha) :=
  AssocGraded.mapLE_mk (RingHom.id O) P m _ n a ha

theorem grInclusion_algebraMap (a : O) :
    grInclusion hPm (algebraMap O (AssocGraded P) a) = algebraMap O (AssocGraded m) a :=
  AssocGraded.mapLE_algebraMap (RingHom.id O) P m _ a

/-- The kernel of `gr_P(O) → gr_m(O)` contains `m gr_P(O)` (p. 183: "whose kernel contains
`m̄ gr_P(O)`"), since `m` acts by `0` on `gr_m(O)`. -/
theorem map_le_ker_grInclusion :
    Ideal.map (algebraMap O (AssocGraded P)) m ≤ RingHom.ker (grInclusion hPm) := by
  rw [Ideal.map_le_iff_le_comap]
  intro a ha
  rw [Ideal.mem_comap, RingHom.mem_ker, grInclusion_algebraMap]
  exact AssocGraded.algebraMap_eq_zero_of_mem ha

/-- The map `α : gr⁰_{m̄}(gr_P(O)) → gr_m(O)` of p. 183, a homomorphism of `K`-algebras: the
injections `Pᵖ ⊆ mᵖ` induce a homomorphism `gr_P(O) → gr_m(O)` whose kernel contains
`m̄ gr_P(O)`, hence `α` on `gr_P(O)/m̄ gr_P(O)`. -/
noncomputable def psiAlpha : GrZeroAlg P m →ₐ[O ⧸ m] AssocGraded m :=
  { Ideal.Quotient.lift _ (grInclusion hPm)
      (fun _ ha => RingHom.mem_ker.mp (map_le_ker_grInclusion hPm ha)) with
    commutes' := fun c => by
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective c
      show Ideal.Quotient.lift _ (grInclusion hPm) _
        (Ideal.Quotient.mk _ (algebraMap O (AssocGraded P) a)) = _
      rw [Ideal.Quotient.lift_mk, grInclusion_algebraMap]
      rfl }

/-- The class in `gr⁰_{m̄}(gr_P(O)) = gr_P(O)/m gr_P(O)` of the degree-`p` part:
`gr⁰_{m̄}(grᵖ_P(O)) = grᵖ_P(O)/m grᵖ_P(O) → gr_P(O)/m gr_P(O)`. -/
noncomputable def grZeroMk (p : ℕ) : GrModPiece m (GrPiece P p) 0 →ₗ[O ⧸ m] GrZeroAlg P m :=
  LinearMap.extendScalarsOfSurjective (Ideal.Quotient.mk_surjective (I := m))
    ((Submodule.comap ((m ^ 0 • (⊤ : Submodule O (GrPiece P p))).subtype)
      (m ^ (0 + 1) • (⊤ : Submodule O (GrPiece P p)))).liftQ
      ((Ideal.Quotient.mkₐ O (Ideal.map (algebraMap O (AssocGraded P)) m)).toLinearMap ∘ₗ
        (AssocGraded.ofGrPiece P p).restrictScalars O ∘ₗ Submodule.subtype _) (by
        intro x hx
        rw [LinearMap.mem_ker]
        rw [Submodule.mem_comap, Submodule.subtype_apply] at hx
        show Ideal.Quotient.mk _ (AssocGraded.ofGrPiece P p x.1) = 0
        refine Submodule.smul_induction_on hx (fun r hr w _ => ?_) (fun a b ha hb => ?_)
        · rw [Ideal.Quotient.eq_zero_iff_mem]
          have : AssocGraded.ofGrPiece P p (r • w) =
              algebraMap O (AssocGraded P) r * AssocGraded.ofGrPiece P p w := by
            rw [← IsScalarTower.algebraMap_smul (O ⧸ P) r w, map_smul, Algebra.smul_def]
            rfl
          rw [this]
          exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ (by simpa using hr))
        · rw [map_add, map_add, ha, hb, add_zero]))

theorem grZeroMk_mk (p : ℕ) (a : O) (ha : a ∈ P ^ p) :
    grZeroMk p (Submodule.Quotient.mk ⟨Submodule.Quotient.mk ⟨a, ha⟩,
      mem_pow_zero_smul_top m _⟩) =
      Ideal.Quotient.mk _ (AssocGraded.mk P p a ha) := rfl

theorem psiAlpha_grZeroMk (p : ℕ) (x : GrModPiece m (GrPiece P p) 0) :
    psiAlpha hPm (grZeroMk p x) = AssocGraded.ofGrPiece m p (alphaPiece P m hPm p x) := by
  induction x using Submodule.Quotient.induction_on with
  | H w =>
    obtain ⟨w, hw⟩ := w
    induction w using Submodule.Quotient.induction_on with
    | H a =>
      obtain ⟨a, ha⟩ := a
      rw [alphaPiece_mk P m hPm p]
      show grInclusion hPm (AssocGraded.mk P p a ha) = _
      rw [grInclusion_mk, grPieceInclusion_mk, AssocGraded.ofGrPiece_mk]

section Beta

variable {s : ℕ} (y : Fin s → O)
  (hqr : IsQuasiRegular fun j => Ideal.Quotient.mk P (y j))
  (hz : Ideal.span (Set.range fun j => Ideal.Quotient.mk P (y j)) =
    m.map (Ideal.Quotient.mk P))

include hPm hz in
theorem mem_pow_one (j : Fin s) : y j ∈ m ^ 1 := by
  rw [pow_one]
  exact span_range_le_of_span_map_eq P m hPm y hz (Ideal.subset_span ⟨j, rfl⟩)

include hPm hqr hz in
/-- The map `β* : gr_{m̄}(Ō) → gr_m(O)` of p. 183, a monomorphism of `K`-algebras (an isomorphism
onto the subalgebra `T` generated by the classes `X_j` of the `x_j` in `m/m²`): the inverse of
the isomorphism `T → gr_{m̄}(Ō) = K[X̄]` induced by `β`, i.e. `X̄_j ↦ X_j`.  It is defined as
`K[X̄] → gr_m(O)`, `X̄_j ↦ X_j`, precomposed with the inverse of the polynomial presentation
`psiTau`; `psiBetaProj_psiBeta`, `range_psiBeta` and `psiBeta_psiBetaProj` show that it is a section
of `β` (`psiBetaProj`) with image `T`, and the inverse of `β|_T`. -/
noncomputable def psiBeta : AssocGraded (m.map (Ideal.Quotient.mk P)) →ₐ[O ⧸ m] AssocGraded m :=
  (MvPolynomial.aeval (R := O ⧸ m) (fun j => AssocGraded.mk m 1 (y j)
    (mem_pow_one hPm y hz j))).comp
    (AlgEquiv.ofBijective (psiTau y hz) (psiTau_bijective hPm y hqr hz)).symm.toAlgHom

include hPm hqr hz in
theorem psiBeta_psiTau (f : MvPolynomial (Fin s) (O ⧸ m)) :
    psiBeta hPm y hqr hz (psiTau y hz f) =
      MvPolynomial.aeval (R := O ⧸ m) (fun j => AssocGraded.mk m 1 (y j)
        (mem_pow_one hPm y hz j)) f := by
  have := (AlgEquiv.ofBijective (psiTau y hz) (psiTau_bijective hPm y hqr hz)).symm_apply_apply f
  simp only [psiBeta, AlgHom.comp_apply, AlgEquiv.coe_toAlgHom]
  rw [show psiTau y hz f = (AlgEquiv.ofBijective (psiTau y hz)
    (psiTau_bijective hPm y hqr hz)) f from rfl, this]

include hPm hz in
theorem aeval_monomial_assocGraded (α : Fin s →₀ ℕ) {d : ℕ} (hd : α.degree = d)
    (h : (α.prod fun j e => y j ^ e) ∈ m ^ d) :
    MvPolynomial.aeval (R := O ⧸ m) (fun j => AssocGraded.mk m 1 (y j)
      (mem_pow_one hPm y hz j)) (MvPolynomial.monomial α 1) =
      AssocGraded.mk m d (α.prod fun j e => y j ^ e) h := by
  subst hd
  have h2 := aeval_mk_map_of_isHomogeneous m y (mem_pow_one hPm y hz)
    (K := MvPolynomial.monomial α (1 : O)) (d := α.degree)
    (MvPolynomial.isHomogeneous_monomial _ rfl)
  have h3 : (Ideal.Quotient.mk m : O →+* O ⧸ m) 1 = 1 := map_one _
  rw [MvPolynomial.map_monomial, h3] at h2
  rw [h2]
  congr 1
  simp [MvPolynomial.eval_monomial]

include hPm hqr hz in
/-- `β*` in degree `q` is the map `betaStarPiece`: `gr^q_{m̄}(Ō) → gr^q_m(O)`, `[x̄^α] ↦ [x^α]`. -/
theorem psiBeta_ofGrPiece (q : ℕ) (b : GrPiece (m.map (Ideal.Quotient.mk P)) q) :
    psiBeta hPm y hqr hz (AssocGraded.ofGrPiece _ q b) =
      AssocGraded.ofGrPiece m q (betaStarPiece P m hPm y hqr hz q b) := by
  have key : (psiBeta hPm y hqr hz).toLinearMap ∘ₗ ofGrPieceK q =
      (AssocGraded.ofGrPiece m q) ∘ₗ betaStarPiece P m hPm y hqr hz q := by
    refine (grPieceMapBasis P m hPm _ hqr hz (degreeFinset s)
      (fun _ _ => mem_degreeFinset) q).ext fun α => ?_
    have hdeg := mem_degreeFinset.mp α.2
    have hQ : (α.1.prod fun j e => Ideal.Quotient.mk P (y j) ^ e) ∈
        (m.map (Ideal.Quotient.mk P)) ^ q := by
      have := mono_mem_span_pow (fun j => Ideal.Quotient.mk P (y j)) α.1
      rwa [hdeg, hz] at this
    have hM : (α.1.prod fun j e => y j ^ e) ∈ m ^ q :=
      prod_pow_mem_pow_of_span_le m y (span_range_le_of_span_map_eq P m hPm y hz) q α.1 hdeg
    have hRHS : betaStarPiece P m hPm y hqr hz q (grPieceMapBasis P m hPm _ hqr hz
        (degreeFinset s) (fun _ _ => mem_degreeFinset) q α) =
        Submodule.Quotient.mk ⟨_, hM⟩ := by
      unfold betaStarPiece
      rw [Module.Basis.constr_basis]
    have hLHS : ofGrPieceK q (grPieceMapBasis P m hPm _ hqr hz
        (degreeFinset s) (fun _ _ => mem_degreeFinset) q α) =
        AssocGraded.mk (m.map (Ideal.Quotient.mk P)) q
          (α.1.prod fun j e => Ideal.Quotient.mk P (y j) ^ e) hQ := by
      show AssocGraded.ofGrPiece _ q _ = _
      rw [grPieceMapBasis_apply P m hPm _ hqr hz (degreeFinset s) (fun _ _ => mem_degreeFinset)
        q α hQ, AssocGraded.ofGrPiece_mk]
    simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply]
    rw [hLHS, hRHS, AssocGraded.ofGrPiece_mk, ← psiTau_monomial hPm y hz α.1 hdeg hQ,
      psiBeta_psiTau hPm y hqr hz, aeval_monomial_assocGraded hPm y hz α.1 hdeg hM]
  exact LinearMap.congr_fun key b

variable (P m)

/-- The homomorphism of graded `K`-algebras `β : gr_m(O) → gr_{m̄}(Ō)` of p. 183, induced by the
natural homomorphisms of `O`-modules `mᵐ → m̄ᵐ`. -/
noncomputable def psiBetaProj :
    AssocGraded m →ₐ[O ⧸ m] AssocGraded (m.map (Ideal.Quotient.mk P)) :=
  { AssocGraded.mapLE (Ideal.Quotient.mk P) m (m.map (Ideal.Quotient.mk P)) le_rfl with
    commutes' := fun c => by
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective c
      show AssocGraded.mapLE (Ideal.Quotient.mk P) m _ le_rfl (algebraMap O (AssocGraded m) a) =
        algebraMap O (AssocGraded (m.map (Ideal.Quotient.mk P))) a
      rw [AssocGraded.mapLE_algebraMap, IsScalarTower.algebraMap_apply O (O ⧸ P)]
      rfl }

variable {P m}

theorem psiBetaProj_mk (n : ℕ) (a : O) (ha : a ∈ m ^ n) :
    psiBetaProj P m (AssocGraded.mk m n a ha) =
      AssocGraded.mk (m.map (Ideal.Quotient.mk P)) n (Ideal.Quotient.mk P a)
        (Ideal.pow_right_mono le_rfl n
          (by rw [← Ideal.map_pow]; exact Ideal.mem_map_of_mem _ ha)) :=
  AssocGraded.mapLE_mk (Ideal.Quotient.mk P) m _ le_rfl n a ha

include hPm hqr hz in
/-- `β ∘ β* = id`: `β*` is a section of `β` (so a monomorphism of `K`-algebras, p. 183). -/
theorem psiBetaProj_psiBeta (u : AssocGraded (m.map (Ideal.Quotient.mk P))) :
    psiBetaProj P m (psiBeta hPm y hqr hz u) = u := by
  obtain ⟨f, rfl⟩ := (psiTau_bijective hPm y hqr hz).2 u
  rw [psiBeta_psiTau hPm y hqr hz]
  have : (psiBetaProj P m).comp (MvPolynomial.aeval (R := O ⧸ m) (fun j =>
      AssocGraded.mk m 1 (y j) (mem_pow_one hPm y hz j))) = psiTau y hz := by
    refine MvPolynomial.algHom_ext fun j => ?_
    simp only [AlgHom.comp_apply, MvPolynomial.aeval_X, psiTau]
    exact psiBetaProj_mk 1 (y j) _
  exact AlgHom.congr_fun this f

include hPm hqr hz in
/-- Image of `β*`: the `K`-subalgebra `T` of `gr_m(O)` generated by the classes `X_j` of the `x_j`
in `m/m²` (p. 183). -/
theorem range_psiBeta : (psiBeta hPm y hqr hz).range =
    Algebra.adjoin (O ⧸ m) (Set.range fun j => AssocGraded.mk m 1 (y j)
      (mem_pow_one hPm y hz j)) := by
  have h : (psiBeta hPm y hqr hz).range = (MvPolynomial.aeval (R := O ⧸ m) (fun j =>
      AssocGraded.mk m 1 (y j) (mem_pow_one hPm y hz j))).range := by
    ext t
    constructor
    · rintro ⟨u, rfl⟩
      obtain ⟨f, rfl⟩ := (psiTau_bijective hPm y hqr hz).2 u
      exact ⟨f, (psiBeta_psiTau hPm y hqr hz f).symm⟩
    · rintro ⟨f, rfl⟩
      exact ⟨psiTau y hz f, psiBeta_psiTau hPm y hqr hz f⟩
  rw [h, ← Algebra.adjoin_range_eq_range_aeval]

include hPm hqr hz in
/-- "`β` induces an isomorphism of `T` onto `gr_{m̄}(Ō) = K[X̄]`.  Hence taking the inverse of this
induced isomorphism, we obtain a monomorphism of `K`-algebras `β*`" (p. 183): `β*` is the inverse
of `β|_T`, i.e. `β*(β t) = t` for `t ∈ T`, together with `β(β* u) = u` and `β* u ∈ T`. -/
theorem psiBeta_psiBetaProj (t : AssocGraded m)
    (ht : t ∈ Algebra.adjoin (O ⧸ m) (Set.range fun j => AssocGraded.mk m 1 (y j)
      (mem_pow_one hPm y hz j))) :
    psiBeta hPm y hqr hz (psiBetaProj P m t) = t := by
  rw [← range_psiBeta hPm y hqr hz, AlgHom.mem_range] at ht
  obtain ⟨u, rfl⟩ := ht
  rw [psiBetaProj_psiBeta hPm y hqr hz]

end Beta

theorem ofGrPiece_mulPiece (I : Ideal O) (p q : ℕ) (u : GrPiece I p) (v : GrPiece I q) :
    AssocGraded.ofGrPiece I (p + q) (GrPiece.mulPiece I p q u v) =
      AssocGraded.ofGrPiece I p u * AssocGraded.ofGrPiece I q v := by
  induction u using Submodule.Quotient.induction_on with
  | H a =>
    induction v using Submodule.Quotient.induction_on with
    | H b =>
      rw [GrPiece.mulPiece_mk, AssocGraded.ofGrPiece_mk, AssocGraded.ofGrPiece_mk,
        AssocGraded.ofGrPiece_mk, AssocGraded.mk_mul_mk]

section PsiAlgHom

variable {s : ℕ} (y : Fin s → O)
  (hqr : IsQuasiRegular fun j => Ideal.Quotient.mk P (y j))
  (hz : Ideal.span (Set.range fun j => Ideal.Quotient.mk P (y j)) =
    m.map (Ideal.Quotient.mk P))

include hPm hqr hz in
/-- The homomorphism of graded `K`-algebras
`ψ = α ⊗ β* : gr⁰_{m̄}(gr_P(O)) ⊗_K gr_{m̄}(Ō) → gr_m(O)` of p. 183 ("Thus we obtain a
homomorphism of K-algebras: `ψ = α ⊗ β*`"), as one map, for the system `y` of elements of `m`
inducing a minimal base of `m̄`.  It is graded (p. 183: "In this manner, we easily see that `ψ` is a
homomorphism of graded K-algebras"): `psiAlgHom_tmul_grPiece`, `map_psiDegPart_eq_homogeneous`. -/
noncomputable def psiAlgHom :
    GrZeroAlg P m ⊗[O ⧸ m] AssocGraded (m.map (Ideal.Quotient.mk P)) →ₐ[O ⧸ m]
      AssocGraded m :=
  Algebra.TensorProduct.lift (psiAlpha hPm) (psiBeta hPm y hqr hz) (fun _ _ => Commute.all _ _)

include hPm hqr hz in
theorem psiAlgHom_tmul (a : GrZeroAlg P m) (b : AssocGraded (m.map (Ideal.Quotient.mk P))) :
    psiAlgHom hPm y hqr hz (a ⊗ₜ b) = psiAlpha hPm a * psiBeta hPm y hqr hz b :=
  Algebra.TensorProduct.lift_tmul _ _ _ _ _

include hPm hqr hz in
/-- `ψ` maps the bidegree `(p, q)` part to the total degree `p + q` part, as the component
`ψ_{p,q}` (`psiPiece`). -/
theorem psiAlgHom_tmul_grPiece (p q : ℕ) (x : GrModPiece m (GrPiece P p) 0)
    (b : GrPiece (m.map (Ideal.Quotient.mk P)) q) :
    psiAlgHom hPm y hqr hz (grZeroMk p x ⊗ₜ AssocGraded.ofGrPiece _ q b) =
      AssocGraded.ofGrPiece m (p + q) (psiPiece P m hPm y hqr hz p q (x ⊗ₜ b)) := by
  rw [psiAlgHom_tmul, psiAlpha_grZeroMk, psiBeta_ofGrPiece, ← ofGrPiece_mulPiece]
  rfl

end PsiAlgHom

section PsiBijective

variable (P m)

/-- `⨁_{p+q=n} gr⁰_{m̄}(grᵖ_P(O)) ⊗_K gr^q_{m̄}(Ō) → gr⁰_{m̄}(gr_P(O)) ⊗_K gr_{m̄}(Ō)`, the
inclusion of the total degree `n` part of the doubly graded algebra. -/
noncomputable def psiIota (n : ℕ) :
    (⨁ pq : {pq : ℕ × ℕ // pq.1 + pq.2 = n}, PsiSummand P m n pq) →ₗ[O ⧸ m]
      GrZeroAlg P m ⊗[O ⧸ m] AssocGraded (m.map (Ideal.Quotient.mk P)) :=
  DirectSum.toModule (O ⧸ m) _ _ fun pq =>
    TensorProduct.map (grZeroMk pq.1.1) (ofGrPieceK pq.1.2)

/-- The doubly graded algebra `gr⁰_{m̄}(gr_P(O)) ⊗_K gr_{m̄}(Ō)` is the sum of its total degree
parts: `⨁_n ⨁_{p+q=n} → gr⁰ ⊗ gr` (surjective: `psiTotal_surjective`). -/
noncomputable def psiTotal :
    (⨁ n : ℕ, ⨁ pq : {pq : ℕ × ℕ // pq.1 + pq.2 = n}, PsiSummand P m n pq) →ₗ[O ⧸ m]
      GrZeroAlg P m ⊗[O ⧸ m] AssocGraded (m.map (Ideal.Quotient.mk P)) :=
  DirectSum.toModule (O ⧸ m) ℕ _ (psiIota P m)

theorem psiTotal_lof (n : ℕ) (pq : {pq : ℕ × ℕ // pq.1 + pq.2 = n})
    (x : GrModPiece m (GrPiece P pq.1.1) 0)
    (b : GrPiece (m.map (Ideal.Quotient.mk P)) pq.1.2) :
    psiTotal P m (DirectSum.lof (O ⧸ m) ℕ (fun n => ⨁ pq : {pq : ℕ × ℕ // pq.1 + pq.2 = n},
      PsiSummand P m n pq) n (DirectSum.lof (O ⧸ m) _ (PsiSummand P m n) pq (x ⊗ₜ b))) =
      grZeroMk pq.1.1 x ⊗ₜ ofGrPieceK pq.1.2 b := by
  rw [psiTotal, DirectSum.toModule_lof, psiIota, DirectSum.toModule_lof, TensorProduct.map_tmul]

theorem grZeroMk_mk_zero (p : ℕ) (z : GrPiece P p) :
    grZeroMk p (Submodule.Quotient.mk ⟨z, mem_pow_zero_smul_top m z⟩ :
      GrModPiece m (GrPiece P p) 0) =
      Ideal.Quotient.mk _ (AssocGraded.ofGrPiece P p z) := by
  induction z using Submodule.Quotient.induction_on with
  | H a => exact grZeroMk_mk p a.1 a.2

theorem psiTotal_surjective : Function.Surjective (psiTotal P m) := by
  rw [← LinearMap.range_eq_top, eq_top_iff]
  intro t _
  induction t using TensorProduct.inductionOn with
  | tmul a b =>
    obtain ⟨g, rfl⟩ := Ideal.Quotient.mk_surjective a
    obtain ⟨S₁, hS₁⟩ := GrQuotDiagram.exists_eq_sum_ofGrPiece_grProj P g
    obtain ⟨S₂, hS₂⟩ := GrQuotDiagram.exists_eq_sum_ofGrPiece_grProj
      (m.map (Ideal.Quotient.mk P)) b
    rw [hS₁, hS₂, map_sum, TensorProduct.sum_tmul]
    refine Submodule.sum_mem _ fun p _ => ?_
    rw [TensorProduct.tmul_sum]
    refine Submodule.sum_mem _ fun q _ => ?_
    refine ⟨DirectSum.lof (O ⧸ m) ℕ (fun n => ⨁ pq : {pq : ℕ × ℕ // pq.1 + pq.2 = n},
      PsiSummand P m n pq) (p + q) (DirectSum.lof (O ⧸ m) _ (PsiSummand P m (p + q))
        ⟨(p, q), rfl⟩ (Submodule.Quotient.mk ⟨grProj P p g,
          mem_pow_zero_smul_top m _⟩ ⊗ₜ grProj _ q b)), ?_⟩
    rw [psiTotal_lof]
    exact congrArg (· ⊗ₜ[O ⧸ m] _) (grZeroMk_mk_zero P m p _)
  | add x y hx hy => exact add_mem (hx trivial) (hy trivial)

variable {P m} {s : ℕ} (y : Fin s → O)
  (hqr : IsQuasiRegular fun j => Ideal.Quotient.mk P (y j))
  (hz : Ideal.span (Set.range fun j => Ideal.Quotient.mk P (y j)) =
    m.map (Ideal.Quotient.mk P))

include hPm hz in
/-- The lifts `y` of the chosen system of generators of `m̄` generate `m` modulo `P`. -/
theorem eq_sup_span_of_span_map_eq : m = P ⊔ Ideal.span (Set.range y) := by
  have h1 : (Ideal.span (Set.range y)).map (Ideal.Quotient.mk P) = m.map (Ideal.Quotient.mk P) := by
    rw [← hz, Ideal.map_span, ← Set.range_comp]
    rfl
  have h2 := congrArg (Ideal.comap (Ideal.Quotient.mk P)) h1
  rw [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective,
    Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective, ← RingHom.ker_eq_comap_bot,
    Ideal.mk_ker] at h2
  rw [sup_comm, h2]
  exact (sup_eq_left.mpr hPm).symm

include hPm hqr hz in
theorem psiAlgHom_comp_psiTotal :
    ⇑(psiAlgHom hPm y hqr hz) ∘ ⇑(psiTotal P m) =
      ⇑(toGr m) ∘ ⇑(DirectSum.lmap fun n => psiDeg P m hPm y hqr hz n) := by
  have : (psiAlgHom hPm y hqr hz).toLinearMap ∘ₗ psiTotal P m =
      toGr m ∘ₗ DirectSum.lmap fun n => psiDeg P m hPm y hqr hz n := by
    refine DirectSum.linearMap_ext _ fun n => DirectSum.linearMap_ext _ fun pq => ?_
    refine TensorProduct.ext' fun x b => ?_
    simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply, DirectSum.lmap_lof, toGr,
      DirectSum.toModule_lof]
    obtain ⟨⟨p, q⟩, hpq⟩ := pq
    subst hpq
    rw [psiTotal_lof, psiDeg_lof]
    show psiAlgHom hPm y hqr hz (grZeroMk p x ⊗ₜ AssocGraded.ofGrPiece _ q b) = _
    rw [psiAlgHom_tmul_grPiece]
    rfl
  exact congrArg DFunLike.coe this

include hPm hqr hz in
theorem psiAlgHom_comp_psiIota (n : ℕ) (v : ⨁ pq : {pq : ℕ × ℕ // pq.1 + pq.2 = n},
    PsiSummand P m n pq) :
    psiAlgHom hPm y hqr hz (psiIota P m n v) =
      AssocGraded.ofGrPiece m n (psiDeg P m hPm y hqr hz n v) := by
  have := congrFun (psiAlgHom_comp_psiTotal hPm y hqr hz)
    (DirectSum.lof (O ⧸ m) ℕ (fun n => ⨁ pq : {pq : ℕ × ℕ // pq.1 + pq.2 = n},
      PsiSummand P m n pq) n v)
  simpa [psiTotal, DirectSum.toModule_lof, toGr] using this

include hPm hqr hz in
/-- The printed assertion (1) of Proposition 1 (p. 184): "If `gr_P(O)` is flat over `Ō`, then (1)
the homomorphism of graded `K`-algebras, obtained as above,
`ψ : gr⁰_{m̄}(gr_P(O)) ⊗_K gr_{m̄}(Ō) → gr_m(O)` is an isomorphism", for the specific `ψ = α ⊗ β*`
(`psiAlgHom`) attached to a system `y` of elements of `m` inducing a minimal base of `m̄` (the
choice on which, as the paper notes, `ψ` depends).  Proof: `ψ ∘ ι = toGr ∘ ⨁ ψₙ`
(`psiAlgHom_comp_psiTotal`), `ι : ⨁ₙ ⨁_{p+q=n} → gr⁰ ⊗ gr` is surjective (`psiTotal_surjective`),
and every `ψₙ` is bijective (`psiDeg_bijective_of_isNormallyFlatAlongIdeal`). -/
@[blueprint "prop:II.1-1-algebra"
  (statement := /-- Let $O$ be a local ring and $P\subseteq\mathfrak m$ prime ideals such that
    $O/P$ and $O/\mathfrak m$ are regular, $\bar O=O/P$, $\bar{\mathfrak m}=\mathfrak m/P$,
    $K=O/\mathfrak m$, and let $x_1,\dots,x_r\in\mathfrak m$ induce a minimal base of
    $\bar{\mathfrak m}$. If $\operatorname{gr}_P(O)$ is flat over $\bar O$, then the
    homomorphism of graded $K$-algebras
    $\psi=\alpha\otimes\beta^*\colon\operatorname{gr}^0_{\bar{\mathfrak m}}(\operatorname{gr}_P(O))
    \otimes_K\operatorname{gr}_{\bar{\mathfrak m}}(\bar O)\to\operatorname{gr}_{\mathfrak m}(O)$
    of p.~183 is an isomorphism (\cref{prop:II.1-1}(1), p.~184), $\psi$ taking the part of total
    degree $n$ onto $\operatorname{gr}^n_{\mathfrak m}(O)$. -/)
  (proof := /-- The map $\psi=\alpha\otimes\beta^*$ is one homomorphism of $K$-algebras
    ($\alpha$ induced by $P^m\subseteq\mathfrak m^m$, $\beta^*$ the inverse of
    $\beta|_T\colon T=K[X_1,\dots,X_r]\to\operatorname{gr}_{\bar{\mathfrak m}}(\bar O)$
    composed with $\bar X_j\mapsto X_j$). In each total degree $n$ it is the map $\psi_n$ of
    \cref{prop:II.1-1-psi}, which is bijective; $\psi$ restricted to the sum of the total degree
    parts of the doubly graded source is the direct sum of the $\psi_n$, and that sum is the
    whole source, so $\psi$ is bijective. -/)
  (latexEnv := "proposition")]
theorem psiAlgHom_bijective [IsLocalRing O] [IsNoetherianRing O] [P.IsPrime] [m.IsPrime]
    [IsRegularLocalRing (O ⧸ P)] [IsRegularLocalRing (O ⧸ m)] (hP : IsNormallyFlatAlongIdeal P) :
    Function.Bijective (psiAlgHom hPm y hqr hz) := by
  have hmPY := eq_sup_span_of_span_map_eq hPm y hz
  have hd : ∀ n, Function.Bijective (psiDeg P m hPm y hqr hz n) := fun n =>
    psiDeg_bijective_of_isNormallyFlatAlongIdeal P m hPm y hqr hz hP hmPY n
  have hF : Function.Bijective (DirectSum.lmap fun n => psiDeg P m hPm y hqr hz n) :=
    ⟨(DirectSum.lmap_injective _).mpr fun n => (hd n).1,
      (DirectSum.lmap_surjective _).mpr fun n => (hd n).2⟩
  have hcomp := psiAlgHom_comp_psiTotal hPm y hqr hz
  have hT := (toGr_bijective m).comp hF
  refine ⟨fun a a' haa' => ?_, ?_⟩
  · obtain ⟨w, rfl⟩ := psiTotal_surjective P m a
    obtain ⟨w', rfl⟩ := psiTotal_surjective P m a'
    have h : (⇑(toGr m) ∘ ⇑(DirectSum.lmap fun n => psiDeg P m hPm y hqr hz n)) w =
        (⇑(toGr m) ∘ ⇑(DirectSum.lmap fun n => psiDeg P m hPm y hqr hz n)) w' := by
      rw [← hcomp]
      exact haa'
    rw [hT.1 h]
  · rw [← hcomp] at hT
    exact Function.Surjective.of_comp hT.2

/-- The part of total degree `n` of the doubly graded algebra
`gr⁰_{m̄}(gr_P(O)) ⊗_K gr_{m̄}(Ō)`: the image of `⨁_{p+q=n} gr⁰_{m̄}(grᵖ_P(O)) ⊗_K gr^q_{m̄}(Ō)`. -/
noncomputable def psiDegPart (P m : Ideal O) (n : ℕ) :
    Submodule (O ⧸ m) (GrZeroAlg P m ⊗[O ⧸ m] AssocGraded (m.map (Ideal.Quotient.mk P))) :=
  LinearMap.range (psiIota P m n)

include hPm hqr hz in
/-- `ψ` is graded: it maps the total degree `n` part of the source onto the degree `n` part
`grⁿ_m(O)` of the target. -/
theorem map_psiDegPart_eq_homogeneous (n : ℕ) :
    (psiDegPart P m n).map (psiAlgHom hPm y hqr hz).toLinearMap = AssocGraded.homogeneous m n := by
  have hmPY := eq_sup_span_of_span_map_eq hPm y hz
  apply le_antisymm
  · rintro _ ⟨_, ⟨v, rfl⟩, rfl⟩
    rw [AlgHom.toLinearMap_apply, psiAlgHom_comp_psiIota]
    exact ⟨_, rfl⟩
  · rintro _ ⟨w, rfl⟩
    obtain ⟨v, rfl⟩ := psiDeg_surjective P m hPm y hqr hz hmPY n w
    exact ⟨psiIota P m n v, ⟨v, rfl⟩, by
      rw [AlgHom.toLinearMap_apply, psiAlgHom_comp_psiIota]⟩

include hPm hqr hz in
/-- The isomorphism of `K`-algebras `ψ`. -/
noncomputable def psiAlgEquiv [IsLocalRing O] [IsNoetherianRing O] [P.IsPrime] [m.IsPrime]
    [IsRegularLocalRing (O ⧸ P)] [IsRegularLocalRing (O ⧸ m)] (hP : IsNormallyFlatAlongIdeal P) :
    GrZeroAlg P m ⊗[O ⧸ m] AssocGraded (m.map (Ideal.Quotient.mk P)) ≃ₐ[O ⧸ m] AssocGraded m :=
  AlgEquiv.ofBijective (psiAlgHom hPm y hqr hz) (psiAlgHom_bijective hPm y hqr hz hP)

include hPm hqr hz in
/-- `ψ` is an isomorphism of graded algebras: the grading of the source is also recovered from that
of the target, `ψ⁻¹(grⁿ_m(O))` is the part of total degree `n`. -/
theorem comap_homogeneous_eq_psiDegPart [IsLocalRing O] [IsNoetherianRing O] [P.IsPrime]
    [m.IsPrime] [IsRegularLocalRing (O ⧸ P)] [IsRegularLocalRing (O ⧸ m)]
    (hP : IsNormallyFlatAlongIdeal P) (n : ℕ) :
    (AssocGraded.homogeneous m n).comap (psiAlgHom hPm y hqr hz).toLinearMap =
      psiDegPart P m n := by
  rw [← map_psiDegPart_eq_homogeneous hPm y hqr hz n]
  exact Submodule.comap_map_eq_of_injective (psiAlgHom_bijective hPm y hqr hz hP).1 _

variable (P m) in
/-- Proposition 1, p. 184, as printed: "If `gr_P(O)` is flat over `Ō`, then (1) the homomorphism of
graded `K`-algebras, obtained as above, `ψ : gr⁰_{m̄}(gr_P(O)) ⊗_K gr_{m̄}(Ō) → gr_m(O)` is an
isomorphism.  (2) `gr_m(O)` is flat over `K`."  Assertion (1) for every system `y` inducing a
minimal base of `m̄` (the choice on which `ψ` depends), together with (2)
(`isNormallyFlatAlongIdeal_of_le`). -/
theorem psiAlgHom_bijective_and_isNormallyFlatAlongIdeal [IsLocalRing O] [IsNoetherianRing O]
    [P.IsPrime] [m.IsPrime] (hPm : P ≤ m) [IsRegularLocalRing (O ⧸ P)]
    [IsRegularLocalRing (O ⧸ m)] (hP : IsNormallyFlatAlongIdeal P) :
    (∀ (s : ℕ) (y : Fin s → O) (hqr : IsQuasiRegular fun j => Ideal.Quotient.mk P (y j))
      (hz : Ideal.span (Set.range fun j => Ideal.Quotient.mk P (y j)) =
        m.map (Ideal.Quotient.mk P)), Function.Bijective (psiAlgHom hPm y hqr hz)) ∧
      IsNormallyFlatAlongIdeal m :=
  ⟨fun _ y hqr hz => psiAlgHom_bijective hPm y hqr hz hP,
    (isNormallyFlatAlongIdeal_of_le P m hPm hP).2⟩

end PsiBijective

end PsiAlgebra

end Hironaka
