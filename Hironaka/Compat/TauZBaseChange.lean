/-
Copyright (c) 2026 Daattavya Aggarwal, Minhyong Kim, Oisin Kim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daattavya Aggarwal, Minhyong Kim, Oisin Kim
-/
module

public import Hironaka.Ch3.TauStar
public import Hironaka.Ch3.Frames
public import Hironaka.Ch3.StabilityCor3c
public import Hironaka.Ch3.PermissibleEffects
public import Hironaka.Compat.RegularGraded

/-!
# Compatibility layer: the invariance of `T` and `τ_{(z)}` of Definition 10* under a base change
`α : R → R'` that transforms a regular system of parameters into one (Ch. III §4, §8)

The reductions "we may assume that `R` is complete and `R₁` residually rational over `R`"
(proof of Lemma 20, p. 254; Lemma 21, p. 256; Proposition 2, p. 258) replace `R` by `R' = S̃{z}`
(a local homomorphism `α` which transforms a regular system of parameters into one and induces a
separable residue field extension), and the conclusion `τ_{(z)}(f) = τ_{(w)}(g)` of Lemma 21 must be
transported back.  This file proves, for such an `α` (Lemma 12 of §4 for the `T` of Definition 10*;
cf. Lemma 13, p. 225, for the `T_a` of Definition 7, proved in `Ch3/TauStar.lean`), that

* `grMapMax α`: the canonical graded homomorphism `ᾱ : gr_M(R) → gr_{M'}(R')` (p. 206);
* `tauZSubmodule_map`: the smallest `k'`-submodule for `(α f₁, …, α f_i)` is the `k'`-span of the
  image under `ᾱ` of the smallest `k`-submodule for `(f₁, …, f_i)`;
* `tauZ_map`: `τ_{(α z)}(α f₁, …, α f_i) = τ_{(z)}(f₁, …, f_i)`.

The proof is that of Lemma 13: the polynomial pictures `gr_M(R) = k[X]`, `gr_{M'}(R') = k'[X]`
(`exists_polyModel`) and Lemma 12 (`isTauSubmoduleMv_map_iff`) for the homogeneous ideal generated
by the initial forms.  A few private auxiliary lemmas of `Ch3/TauStar.lean`
(`exists_coeffwise`, `linearIndependent_map`, `linearFormsOver_span_map`, `aeval_mk_graded`) are
reproved here under new names.
-/

@[expose] public section

open IsLocalRing

namespace Hironaka
universe u

section CopiedAux

/-- For `x ∈ grᵉ_I(A)`, `x` is recovered from its degree-`e` component. -/
theorem ofGrPiece_grProj_of_mem_aux' {A : Type*} [CommRing A] (I : Ideal A) {e : ℕ}
    {x : AssocGraded I} (hx : x ∈ AssocGraded.homogeneous I e) :
    AssocGraded.ofGrPiece I e (grProj I e x) = x := by
  obtain ⟨y, rfl⟩ := LinearMap.mem_range.mp hx
  rw [grProj_ofGrPiece_same]

/-- For `x ∈ gr^{e'}_I(A)` and `e ≠ e'`, the degree-`e` component of `x` vanishes. -/
theorem grProj_of_mem_ne_aux' {A : Type*} [CommRing A] (I : Ideal A) {e e' : ℕ}
    (h : e' ≠ e) {x : AssocGraded I} (hx : x ∈ AssocGraded.homogeneous I e') :
    grProj I e x = 0 := by
  obtain ⟨y, rfl⟩ := LinearMap.mem_range.mp hx
  exact grProj_ofGrPiece_ne I h y

variable {R R' : Type u} [CommRing R] [CommRing R'] [IsRegularLocalRing R] [IsRegularLocalRing R']

/-- The polynomial picture `k[Z₁, …, Z_n] → gr_M(R)`, `Z_i ↦ [z_i]`, of a regular system of
parameters `z` is graded: it maps `G_d` onto `gr^d_M(R)` and commutes with taking homogeneous
components. -/
theorem aeval_mk_graded_aux' {n : ℕ} (z : Fin n → R)
    (hz : ∀ i, z i ∈ maximalIdeal R ^ 1)
    (hbij : Function.Bijective (MvPolynomial.aeval (R := R ⧸ maximalIdeal R)
      fun i => AssocGraded.mk (maximalIdeal R) 1 (z i) (hz i))) :
    (∀ (d : ℕ) (p : MvPolynomial (Fin n) (R ⧸ maximalIdeal R)),
      p ∈ MvPolynomial.homogeneousSubmodule (Fin n) (R ⧸ maximalIdeal R) d ↔
        MvPolynomial.aeval (R := R ⧸ maximalIdeal R)
          (fun i => AssocGraded.mk (maximalIdeal R) 1 (z i) (hz i)) p ∈
            AssocGraded.homogeneous (maximalIdeal R) d) ∧
    ∀ (d : ℕ) (p : MvPolynomial (Fin n) (R ⧸ maximalIdeal R)),
      AssocGraded.ofGrPiece (maximalIdeal R) d (grProj (maximalIdeal R) d
        (MvPolynomial.aeval (R := R ⧸ maximalIdeal R)
          (fun i => AssocGraded.mk (maximalIdeal R) 1 (z i) (hz i)) p)) =
        MvPolynomial.aeval (R := R ⧸ maximalIdeal R)
          (fun i => AssocGraded.mk (maximalIdeal R) 1 (z i) (hz i))
          (MvPolynomial.homogeneousComponent d p) := by
  let e := MvPolynomial.aeval (R := R ⧸ maximalIdeal R)
    fun i => AssocGraded.mk (maximalIdeal R) 1 (z i) (hz i)
  -- `e` maps `G_d` into `gr^d_M(R)`: lift a form of degree `d` to a form over `R`
  have h1 : ∀ (d : ℕ) (p : MvPolynomial (Fin n) (R ⧸ maximalIdeal R)),
      p ∈ MvPolynomial.homogeneousSubmodule (Fin n) (R ⧸ maximalIdeal R) d →
        e p ∈ AssocGraded.homogeneous (maximalIdeal R) d := by
    intro d p hp
    obtain ⟨q, rfl⟩ := MvPolynomial.map_surjective _ Ideal.Quotient.mk_surjective p
    have hq : (MvPolynomial.homogeneousComponent d q).map (Ideal.Quotient.mk (maximalIdeal R)) =
        q.map (Ideal.Quotient.mk (maximalIdeal R)) := by
      rw [← MvPolynomial.homogeneousComponent_eq_self hp]
      ext m
      simp only [MvPolynomial.coeff_map, MvPolynomial.coeff_homogeneousComponent]
      split_ifs <;> simp
    rw [← hq]
    show MvPolynomial.aeval _ _ ∈ _
    rw [aeval_mk_map_of_isHomogeneous (maximalIdeal R) z hz
      (MvPolynomial.homogeneousComponent_isHomogeneous d q)]
    exact AssocGraded.mk_mem_homogeneous _ _
  -- taking homogeneous components commutes with `e`
  have h2 : ∀ (d : ℕ) (p : MvPolynomial (Fin n) (R ⧸ maximalIdeal R)),
      AssocGraded.ofGrPiece (maximalIdeal R) d (grProj (maximalIdeal R) d (e p)) =
        e (MvPolynomial.homogeneousComponent d p) := by
    intro d p
    conv_lhs => rw [← MvPolynomial.sum_homogeneousComponent p]
    rw [map_sum, map_sum, map_sum]
    rw [Finset.sum_eq_single d]
    · exact ofGrPiece_grProj_of_mem_aux' _
        (h1 d _ (MvPolynomial.homogeneousComponent_mem d p))
    · intro d' _ hd'
      rw [grProj_of_mem_ne_aux' _ hd' (h1 d' _ (MvPolynomial.homogeneousComponent_mem d' p)),
        map_zero]
    · intro hd
      rw [MvPolynomial.homogeneousComponent_eq_zero d p (by
        simp only [Finset.mem_range, not_lt] at hd; omega), map_zero, map_zero, map_zero]
  refine ⟨fun d p => ⟨h1 d p, fun hp => ?_⟩, h2⟩
  -- conversely, if `e p ∈ gr^d_M(R)` then all other homogeneous components of `p` vanish
  have hzero : ∀ d', d' ≠ d → MvPolynomial.homogeneousComponent d' p = 0 := by
    intro d' hd'
    apply hbij.1
    rw [← h2, grProj_of_mem_ne_aux' _ (Ne.symm hd') hp, map_zero, map_zero]
  have hpd : p = MvPolynomial.homogeneousComponent d p := by
    conv_lhs => rw [← MvPolynomial.sum_homogeneousComponent p]
    rw [Finset.sum_eq_single d (fun d' _ hd' => hzero d' hd')]
    intro hd
    rw [MvPolynomial.homogeneousComponent_eq_zero d p (by
      simp only [Finset.mem_range, not_lt] at hd; omega)]
  rw [hpd]
  exact MvPolynomial.homogeneousComponent_mem d p


/-- Coefficientwise application of a `k`-linear map `λ : k' → k` is an additive map
`k'[X] → k[X]` with `λ(c · b) = λ(c) b` for `b ∈ k[X]`, `c ∈ k'`. -/
theorem exists_coeffwise_aux' {k k' σ : Type*} [Field k] [CommRing k'] [Algebra k k']
    (lam : k' →ₗ[k] k) :
    ∃ Pr : MvPolynomial σ k' →+ MvPolynomial σ k,
      (∀ q m, (Pr q).coeff m = lam (q.coeff m)) ∧
      ∀ (c : k') (b : MvPolynomial σ k),
        Pr (c • MvPolynomial.map (algebraMap k k') b) = lam c • b := by
  let Pr : MvPolynomial σ k' →+ MvPolynomial σ k :=
    { toFun := fun q => AddMonoidAlgebra.ofCoeff (Finsupp.mapRange lam (map_zero lam) q.coeff)
      map_zero' := by
        ext m
        show lam _ = _
        simp
      map_add' := fun q₁ q₂ => by
        ext m
        show lam _ = lam _ + lam _
        simp }
  have hPr : ∀ q m, (Pr q).coeff m = lam (q.coeff m) := fun q m => rfl
  refine ⟨Pr, hPr, fun c b => ?_⟩
  ext m
  rw [hPr, MvPolynomial.coeff_smul, MvPolynomial.coeff_smul, MvPolynomial.coeff_map, smul_eq_mul,
    mul_comm, ← Algebra.smul_def, map_smul, smul_eq_mul, smul_eq_mul, mul_comm]

/-- Linear independence of forms with coefficients in `k` is preserved under extension of the
coefficient field `k → k'`. -/
theorem linearIndependent_map_aux' {k k' σ ι : Type*} [Field k] [Field k'] [Algebra k k']
    [Fintype ι] {v : ι → MvPolynomial σ k} (hv : LinearIndependent k v) :
    LinearIndependent k' fun i => MvPolynomial.map (algebraMap k k') (v i) := by
  rw [Fintype.linearIndependent_iff] at hv ⊢
  intro c hc i
  by_contra hci
  obtain ⟨φ, hφ⟩ : ∃ φ : Module.Dual k k', φ (c i) ≠ 0 := by
    by_contra hall
    push Not at hall
    exact hci ((Module.forall_dual_apply_eq_zero_iff k (c i)).mp hall)
  obtain ⟨Pr, -, hPr⟩ := exists_coeffwise_aux' (σ := σ) φ
  have h0 := congrArg Pr hc
  rw [map_sum, map_zero] at h0
  simp only [hPr] at h0
  exact hφ (hv _ h0 i)

/-- `L' ∩ k[X]₁ = L` for the `k'`-span `L'` of a `k`-submodule `L ⊆ k[X]₁` (a `k`-linear
retraction `k' → k` applied coefficientwise). -/
theorem linearFormsOver_span_map_aux' {k k' : Type u} [Field k] [Field k'] [Algebra k k']
    {n : ℕ} (L : Submodule k (MvPolynomial (Fin n) k))
    (hL : L ≤ MvPolynomial.homogeneousSubmodule (Fin n) k 1) :
    linearFormsOver k (Submodule.span k' (MvPolynomial.map (algebraMap k k') ''
      (L : Set (MvPolynomial (Fin n) k)))) = L := by
  refine le_antisymm (fun p hp => ?_) (fun l hl => ⟨?_, hL hl⟩)
  · obtain ⟨hp1, -⟩ := hp
    have hpm : MvPolynomial.map (algebraMap k k') p ∈ Submodule.span k'
        (MvPolynomial.map (algebraMap k k') '' (L : Set (MvPolynomial (Fin n) k))) := hp1
    obtain ⟨π, hπ⟩ := LinearMap.exists_leftInverse_of_injective (Algebra.linearMap k k')
      (LinearMap.ker_eq_bot.mpr (algebraMap k k').injective)
    have hπ1 : π 1 = 1 := by
      have := LinearMap.congr_fun hπ 1
      simpa using this
    obtain ⟨Pr, -, hPr⟩ := exists_coeffwise_aux' (σ := Fin n) π
    have key : ∀ y ∈ Submodule.span k' (MvPolynomial.map (algebraMap k k') ''
        (L : Set (MvPolynomial (Fin n) k))), ∀ c : k', Pr (c • y) ∈ L := by
      intro y hy
      induction hy using Submodule.span_induction with
      | mem y hy =>
        obtain ⟨l, hl, rfl⟩ := hy
        intro c
        rw [hPr]
        exact L.smul_mem _ hl
      | zero => intro c; rw [smul_zero, map_zero]; exact zero_mem _
      | add x y _ _ hx hy => intro c; rw [smul_add, map_add]; exact add_mem (hx c) (hy c)
      | smul d x _ hx => intro c; rw [smul_smul]; exact hx (c * d)
    have := key _ hpm 1
    rwa [hPr, hπ1, one_smul] at this
  · show MvPolynomial.map (algebraMap k k') l ∈ Submodule.span k'
      (MvPolynomial.map (algebraMap k k') '' (L : Set (MvPolynomial (Fin n) k)))
    exact Submodule.subset_span ⟨l, hl, rfl⟩


end CopiedAux

section GrMap

variable {R R' : Type u} [CommRing R] [CommRing R'] [IsRegularLocalRing R]
  [IsRegularLocalRing R'] (α : R →+* R') [IsLocalHom α]

-- `exists_grMapMax_aux`, `grMapMax`, `grMapMax_mk` are in `Ch3/NuStar.lean`, section `GrMapMax`.

/-- For an ideal `I` of `R`, the `I`-adic order is preserved by a faithfully flat map. -/
theorem ordElem_map_ideal_of_mapsRSOP (hα : RingHom.MapsRSOP α) (I : Ideal R) (a : R) :
    Ideal.ordElem (I.map α) (α a) = Ideal.ordElem I a := by
  let _ := α.toAlgebra
  have _ : IsLocalHom (algebraMap R R') := ‹IsLocalHom α›
  have _ : Module.Flat R R' := hα.flat
  have _ : Module.FaithfullyFlat R R' := Module.FaithfullyFlat.of_flat_of_isLocalHom
  exact Ideal.ordElem_map_of_faithfullyFlat (B := R') I a

-- `ordElem_map_of_mapsRSOP` and `initialForm_map_of_mapsRSOP` are in `Ch3/NuStar.lean`, section `GrMapMax`,
-- where the Corollary to Lemma 2 uses them.

/-- The residue field map `R/M → R'/M'` induced by a local homomorphism. -/
noncomputable def residueQuotMap : R ⧸ maximalIdeal R →+* R' ⧸ maximalIdeal R' :=
  Ideal.quotientMap (maximalIdeal R') α fun a ha => map_nonunit α a ha

theorem residueQuotMap_mk (a : R) :
    residueQuotMap α (Ideal.Quotient.mk _ a) = Ideal.Quotient.mk _ (α a) :=
  Ideal.quotientMap_mk

theorem residueQuotMap_injective :
    Function.Injective (residueQuotMap α) := by
  let _ : Field (R ⧸ maximalIdeal R) := Ideal.Quotient.field _
  exact (residueQuotMap α).injective

theorem grMapMax_smul (hα : RingHom.MapsRSOP α) (c : R ⧸ maximalIdeal R)
    (x : AssocGraded (maximalIdeal R)) :
    grMapMax α hα (c • x) = residueQuotMap α c • grMapMax α hα x := by
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective c
  rw [Algebra.smul_def, Algebra.smul_def, map_mul,
    ← AssocGraded.mk_zero_eq_algebraMap _ r (by simp),
    grMapMax_mk α hα 0 r _ (by simp), residueQuotMap_mk, ← AssocGraded.mk_zero_eq_algebraMap]

omit [IsLocalHom α] in
theorem grMapMax_mem_homogeneous (hα : RingHom.MapsRSOP α) {d : ℕ}
    {x : AssocGraded (maximalIdeal R)}
    (hx : x ∈ AssocGraded.homogeneous (maximalIdeal R) d) :
    grMapMax α hα x ∈ AssocGraded.homogeneous (maximalIdeal R') d := by
  obtain ⟨y, hy, rfl⟩ := AssocGraded.exists_mk_eq_of_mem_homogeneous _ hx
  have hy' : α y ∈ maximalIdeal R' ^ d := by
    have h1 : α y ∈ ((maximalIdeal R) ^ d).map α := Ideal.mem_map_of_mem α hy
    rw [Ideal.map_pow, hα.map_maximalIdeal] at h1
    exact h1
  rw [grMapMax_mk α hα d y hy hy']
  exact AssocGraded.mk_mem_homogeneous _ _


open MvPolynomial in
/-- **The polynomial pictures** of `gr_M(R)` and `gr_{M'}(R')` (p. 225, proof of Lemma 13):
`α`-corresponding regular systems of parameters identify `gr_M(R)` with `k[X₁, …, X_n]` and
`gr_{M'}(R')` with `k'[X₁, …, X_n]`, as graded algebras, and `ᾱ` becomes the coefficient extension
`k[X] → k'[X]`. -/
theorem exists_polyModel (hα : RingHom.MapsRSOP α) :
    ∃ (n : ℕ) (e : MvPolynomial (Fin n) (R ⧸ maximalIdeal R) ≃ₐ[R ⧸ maximalIdeal R]
        AssocGraded (maximalIdeal R))
      (e' : MvPolynomial (Fin n) (R' ⧸ maximalIdeal R') ≃ₐ[R' ⧸ maximalIdeal R']
        AssocGraded (maximalIdeal R')),
      (∀ (d : ℕ) (p : MvPolynomial (Fin n) (R ⧸ maximalIdeal R)),
        p ∈ homogeneousSubmodule (Fin n) (R ⧸ maximalIdeal R) d ↔
          e p ∈ AssocGraded.homogeneous (maximalIdeal R) d) ∧
      (∀ (d : ℕ) (p : MvPolynomial (Fin n) (R' ⧸ maximalIdeal R')),
        p ∈ homogeneousSubmodule (Fin n) (R' ⧸ maximalIdeal R') d ↔
          e' p ∈ AssocGraded.homogeneous (maximalIdeal R') d) ∧
      ∀ p, grMapMax α hα (e p) = e' (MvPolynomial.map (residueQuotMap α) p) := by
  classical
  obtain ⟨s, hs, hs', hinj⟩ := hα
  have hα0 : RingHom.MapsRSOP α := ⟨s, hs, hs', hinj⟩
  let z : Fin s.card → R := fun i => ((s.equivFin.symm i : s) : R)
  have hz : ∀ i, z i ∈ maximalIdeal R ^ 1 := fun i => by
    rw [pow_one, ← hs.1]
    exact Ideal.subset_span (s.equivFin.symm i).2
  have hαn : ∀ (n : ℕ) (a : R), a ∈ maximalIdeal R ^ n → α a ∈ maximalIdeal R' ^ n := by
    intro n a ha
    have h1 : α a ∈ ((maximalIdeal R) ^ n).map α := Ideal.mem_map_of_mem α ha
    rw [Ideal.map_pow, hα0.map_maximalIdeal] at h1
    exact h1
  have hz' : ∀ i, α (z i) ∈ maximalIdeal R' ^ 1 := fun i => hαn 1 _ (hz i)
  have hbij := assocGraded_maximalIdeal_aeval_bijective_of_rsop hs hz
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
  have hbij' := assocGraded_maximalIdeal_aeval_bijective hspan' hn' hz'
  let e := AlgEquiv.ofBijective _ hbij
  let e' := AlgEquiv.ofBijective _ hbij'
  obtain ⟨hE, -⟩ := aeval_mk_graded_aux' z hz hbij
  obtain ⟨hE', -⟩ := aeval_mk_graded_aux' (fun i => α (z i)) hz' hbij'
  refine ⟨s.card, e, e', hE, hE', fun p => ?_⟩
  have : (grMapMax α hα0).comp (e : MvPolynomial (Fin s.card) (R ⧸ maximalIdeal R) →+*
      AssocGraded (maximalIdeal R)) =
      (e' : MvPolynomial (Fin s.card) (R' ⧸ maximalIdeal R') →+*
        AssocGraded (maximalIdeal R')).comp (MvPolynomial.map (residueQuotMap α)) := by
    refine MvPolynomial.ringHom_ext (fun c => ?_) (fun i => ?_)
    · obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective c
      simp only [RingHom.coe_comp, Function.comp_apply, RingHom.coe_coe, MvPolynomial.map_C,
        e, e', AlgEquiv.ofBijective_apply, MvPolynomial.aeval_C]
      rw [← AssocGraded.mk_zero_eq_algebraMap _ r (by simp), grMapMax_mk α hα0 0 r _ (by simp),
        residueQuotMap_mk, ← AssocGraded.mk_zero_eq_algebraMap]
    · simp only [RingHom.coe_comp, Function.comp_apply, RingHom.coe_coe, MvPolynomial.map_X,
        e, e', AlgEquiv.ofBijective_apply, MvPolynomial.aeval_X]
      exact grMapMax_mk α hα0 1 _ (hz i) (hz' i)
  exact RingHom.congr_fun this p


section Translate

open MvPolynomial

variable {A : Type u} [CommRing A] [CommRing R]

/-- The property of a `k`-submodule `T` of `gr¹` for an ideal `K` of `gr_M(R) ≅ k[X]`
(`K = (φ₁, …, φ_i)`, Definition 10*, p. 251) is transported along a graded isomorphism
`e : k[X] ≅ gr_M(R)`: `T` has it iff `e⁻¹(T)` has the analogous property for `e⁻¹(K)` in `k[X]`. -/
theorem isTauZProp_iff_comap {n : ℕ} {k G : Type*} [Field k] [CommRing G] [Algebra k G]
    (e : MvPolynomial (Fin n) k ≃ₐ[k] G) (K : Ideal G) (T : Submodule k G) :
    Ideal.span ((K : Set G) ∩ (Algebra.adjoin k (T : Set G) : Set G)) = K ↔
      Ideal.span ((K.comap e : Set (MvPolynomial (Fin n) k)) ∩
        (Algebra.adjoin k ((T.comap e.toLinearMap : Submodule k _) :
          Set (MvPolynomial (Fin n) k)) : Set (MvPolynomial (Fin n) k))) = K.comap e := by
  have hadj : ∀ p, p ∈ Algebra.adjoin k ((T.comap e.toLinearMap : Submodule k _) :
      Set (MvPolynomial (Fin n) k)) ↔ e p ∈ Algebra.adjoin k (T : Set G) := by
    intro p
    have hmap : (Algebra.adjoin k ((T.comap e.toLinearMap : Submodule k _) :
        Set (MvPolynomial (Fin n) k))).map (e : _ →ₐ[k] _) = Algebra.adjoin k (T : Set G) := by
      rw [AlgHom.map_adjoin]
      congr 1
      ext y
      refine ⟨?_, fun hy => ⟨e.symm y, by simpa using hy, by simp⟩⟩
      rintro ⟨x, hx, rfl⟩
      simpa using hx
    rw [← hmap, Subalgebra.mem_map]
    refine ⟨fun h => ⟨p, h, rfl⟩, ?_⟩
    rintro ⟨q, hq, hqp⟩
    rwa [← e.injective hqp]
  have himg : (e : MvPolynomial (Fin n) k → G) '' ((K.comap e : Set (MvPolynomial (Fin n) k)) ∩
      (Algebra.adjoin k ((T.comap e.toLinearMap : Submodule k _) :
        Set (MvPolynomial (Fin n) k)) : Set (MvPolynomial (Fin n) k))) =
      (K : Set G) ∩ (Algebra.adjoin k (T : Set G) : Set G) := by
    ext y
    constructor
    · rintro ⟨x, ⟨hx1, hx2⟩, rfl⟩
      exact ⟨hx1, (hadj x).mp hx2⟩
    · rintro ⟨hy1, hy2⟩
      refine ⟨e.symm y, ⟨?_, (hadj _).mpr (by simpa using hy2)⟩, by simp⟩
      rw [SetLike.mem_coe, Ideal.mem_comap, AlgEquiv.apply_symm_apply]
      exact hy1
  have hspan : Ideal.span ((K : Set G) ∩ (Algebra.adjoin k (T : Set G) : Set G)) =
      (Ideal.span ((K.comap e : Set (MvPolynomial (Fin n) k)) ∩
        (Algebra.adjoin k ((T.comap e.toLinearMap : Submodule k _) :
          Set (MvPolynomial (Fin n) k)) : Set (MvPolynomial (Fin n) k)))).map
        (e : MvPolynomial (Fin n) k →+* G) := by
    rw [Ideal.map_span]
    exact congrArg Ideal.span himg.symm
  have hK : K = (K.comap e).map (e : MvPolynomial (Fin n) k →+* G) :=
    (Ideal.map_comap_of_surjective (e : MvPolynomial (Fin n) k →+* G) e.surjective K).symm
  constructor
  · intro h
    rw [hspan] at h
    have := congrArg (Ideal.comap (e : MvPolynomial (Fin n) k →+* G)) h
    rwa [Ideal.comap_map_of_bijective (e : MvPolynomial (Fin n) k →+* G) e.bijective] at this
  · intro h
    rw [hspan, h, ← hK]

end Translate



/-- `ᾱ` maps the `k`-span of a set into the `k'`-span of its image. -/
theorem grMapMax_mem_span_image (hα : RingHom.MapsRSOP α) (X : Set (AssocGraded (maximalIdeal R)))
    {y : AssocGraded (maximalIdeal R)}
    (hy : y ∈ Submodule.span (R ⧸ maximalIdeal R) X) :
    grMapMax α hα y ∈ Submodule.span (R' ⧸ maximalIdeal R') (grMapMax α hα '' X) := by
  induction hy using Submodule.span_induction with
  | mem y hy => exact Submodule.subset_span ⟨y, hy, rfl⟩
  | zero => rw [map_zero]; exact zero_mem _
  | add y z _ _ hy hz => rw [map_add]; exact add_mem hy hz
  | smul c y _ hy =>
    rw [grMapMax_smul α hα]
    exact Submodule.smul_mem _ _ hy

section TauZMap

open MvPolynomial

/-- For an ideal `I` of `k[X]` generated by forms of degree at most `μ̄`, the property of
Lemma 10 up to degree `μ̄` is the property `I ⊆ (I ∩ k[L]) k[X]`. -/
theorem isTauSubmoduleMv_iff_of_generators {k : Type u} [Field k] {n : ℕ}
    (I : Ideal (MvPolynomial (Fin n) k)) {ι : Type*} (q : ι → MvPolynomial (Fin n) k) (d : ι → ℕ)
    (hI : I = Ideal.span (Set.range q)) (hq : ∀ j, q j ∈ homogeneousSubmodule (Fin n) k (d j))
    (μbar : ℕ) (hd : ∀ j, d j ≤ μbar) (L : Submodule k (MvPolynomial (Fin n) k)) :
    IsTauSubmoduleMv k n I L μbar ↔
      L ≤ homogeneousSubmodule (Fin n) k 1 ∧
        I ≤ Ideal.span ((I : Set (MvPolynomial (Fin n) k)) ∩
          (Algebra.adjoin k (L : Set (MvPolynomial (Fin n) k)) :
            Set (MvPolynomial (Fin n) k))) := by
  subst hI
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨h1, ?_⟩
    rw [Ideal.span_le]
    rintro _ ⟨j, rfl⟩
    exact (h2 (d j) (hd j) _ (hq j)).mp (Ideal.subset_span ⟨j, rfl⟩)
  · rintro ⟨h1, h2⟩
    refine ⟨h1, fun μ _ ψ _ => ⟨fun hψ => h2 hψ, fun hψ => ?_⟩⟩
    exact (Ideal.span_le.mpr fun x hx => hx.1) hψ


/-- Definition 10*, p. 251, in the polynomial picture: for a graded isomorphism
`e : k[X] ≅ gr_M(R)`, a `k`-submodule `T` of `gr_M(R)` has the property of Definition 10* for
`(f₁, …, f_i)` iff `e⁻¹(T)` has the property of Lemma 10 (up to degree `μ̄`, bigger than the
degrees of the initial forms) for the ideal generated by the `e⁻¹(φ_j)`. -/
theorem isTauZSubmodule_iff_mv {n : ℕ}
    (e : MvPolynomial (Fin n) (R ⧸ maximalIdeal R) ≃ₐ[R ⧸ maximalIdeal R]
      AssocGraded (maximalIdeal R))
    (hE : ∀ (d : ℕ) (p : MvPolynomial (Fin n) (R ⧸ maximalIdeal R)),
      p ∈ homogeneousSubmodule (Fin n) (R ⧸ maximalIdeal R) d ↔
        e p ∈ AssocGraded.homogeneous (maximalIdeal R) d)
    {i : ℕ} (f : Fin i → R) (d : Fin i → ℕ)
    (hd : ∀ j, initialForm (maximalIdeal R) (f j) ∈ AssocGraded.homogeneous (maximalIdeal R) (d j))
    (μb : ℕ) (hμ : ∀ j, d j ≤ μb)
    (T : Submodule (R ⧸ maximalIdeal R) (AssocGraded (maximalIdeal R))) :
    let _ : Field (R ⧸ maximalIdeal R) := Ideal.Quotient.field _
    IsTauZSubmodule R f T ↔
      IsTauSubmoduleMv (R ⧸ maximalIdeal R) n
        (Ideal.span (Set.range fun j => e.symm (initialForm (maximalIdeal R) (f j))))
        (T.comap e.toLinearMap) μb := by
  intro _
  set K : Ideal (AssocGraded (maximalIdeal R)) :=
    Ideal.span (Set.range fun j => initialForm (maximalIdeal R) (f j)) with hK
  set q : Fin i → MvPolynomial (Fin n) (R ⧸ maximalIdeal R) :=
    fun j => e.symm (initialForm (maximalIdeal R) (f j)) with hq
  set I := Ideal.span (Set.range q) with hI
  have hKI : K = I.map (e : MvPolynomial (Fin n) (R ⧸ maximalIdeal R) →+* _) := by
    rw [hI, Ideal.map_span, ← Set.range_comp]
    show Ideal.span _ = Ideal.span _
    congr 2
    funext j
    simp [q]
  have hKc : K.comap e = I := by
    rw [hKI]
    exact Ideal.comap_map_of_bijective _ e.bijective
  have hqd : ∀ j, q j ∈ homogeneousSubmodule (Fin n) (R ⧸ maximalIdeal R) (d j) := fun j =>
    (hE _ _).mpr (by simpa [q] using hd j)
  have hmv := isTauSubmoduleMv_iff_of_generators I q d hI hqd μb hμ (T.comap e.toLinearMap)
  rw [hmv]
  have hT1 : T ≤ AssocGraded.homogeneous (maximalIdeal R) 1 ↔
      T.comap e.toLinearMap ≤ homogeneousSubmodule (Fin n) (R ⧸ maximalIdeal R) 1 := by
    constructor
    · intro h p hp
      exact (hE 1 p).mpr (h hp)
    · intro h t ht
      have hmem : e.symm t ∈ T.comap e.toLinearMap := by simpa using ht
      simpa using (hE 1 _).mp (h hmem)
  have hprop := isTauZProp_iff_comap e K T
  rw [hKc] at hprop
  unfold IsTauZSubmodule
  rw [← hK, hT1]
  refine and_congr Iff.rfl ?_
  rw [hprop]
  constructor
  · intro h
    exact h.ge
  · intro h
    exact le_antisymm (Ideal.span_le.mpr fun x hx => hx.1) h


attribute [local instance] MvPolynomial.gradedAlgebra in
/-- **Lemma 12 for the `T` of Definition 10*** (the case of systems of elements of the proof of
Lemma 13, p. 225): for `α : R → R'` transforming a regular system of parameters into one, with
residue field extension separable, the smallest `k'`-submodule `T'` of `gr¹_{M'}(R')` for the
system `(α(f₁), …, α(f_i))` is the `k'`-submodule generated by the image under
`ᾱ : gr_M(R) → gr_{M'}(R')` of the smallest `k`-submodule `T` for `(f₁, …, f_i)`. -/
theorem tauZSubmodule_map [Hironaka.Cited.IsSeparableFieldExtensionIff.{u}] (hα : RingHom.MapsRSOP α) (hsep : RingHom.IsResiduallySeparable α)
    {i : ℕ} (f : Fin i → R) :
    tauZSubmodule R' (fun j => α (f j)) =
      Submodule.span (R' ⧸ maximalIdeal R') (grMapMax α hα '' (tauZSubmodule R f :
        Set (AssocGraded (maximalIdeal R)))) := by
  classical
  let _ : Field (R ⧸ maximalIdeal R) := Ideal.Quotient.field _
  let _ : Field (R' ⧸ maximalIdeal R') := Ideal.Quotient.field _
  let _ : Algebra (R ⧸ maximalIdeal R) (R' ⧸ maximalIdeal R') := (residueQuotMap α).toAlgebra
  have hsep' : IsSeparableFieldExtension (R ⧸ maximalIdeal R) (R' ⧸ maximalIdeal R') := hsep
  obtain ⟨n, e, e', hE, hE', hcomm⟩ := exists_polyModel α hα
  have hdex : ∀ j, ∃ d, initialForm (maximalIdeal R) (f j) ∈
      AssocGraded.homogeneous (maximalIdeal R) d := fun j => initialForm_mem_homogeneous_aux' _ _
  choose d hd using hdex
  set μb := ∑ j, d j + 1 with hμb
  have hdμ : ∀ j, d j ≤ μb := fun j =>
    (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)).trans (Nat.le_succ _)
  have hμpos : 0 < μb := Nat.succ_pos _
  have hd' : ∀ j, initialForm (maximalIdeal R') (α (f j)) ∈
      AssocGraded.homogeneous (maximalIdeal R') (d j) := fun j => by
    rw [initialForm_map_of_mapsRSOP α hα]
    exact grMapMax_mem_homogeneous α hα (hd j)
  set q : Fin i → MvPolynomial (Fin n) (R ⧸ maximalIdeal R) :=
    fun j => e.symm (initialForm (maximalIdeal R) (f j)) with hq
  set I := Ideal.span (Set.range q) with hI
  have hqd : ∀ j, q j ∈ MvPolynomial.homogeneousSubmodule (Fin n) (R ⧸ maximalIdeal R) (d j) :=
    fun j => (hE _ _).mpr (by simpa [q] using hd j)
  have hIhom : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin n)
      (R ⧸ maximalIdeal R)) := by
    apply Ideal.homogeneous_span
    rintro _ ⟨j, rfl⟩
    exact ⟨d j, hqd j⟩
  -- the ideal for `R'` is the extension of `I`
  have hq' : ∀ j, e'.symm (initialForm (maximalIdeal R') (α (f j))) =
      MvPolynomial.map (residueQuotMap α) (q j) := by
    intro j
    rw [initialForm_map_of_mapsRSOP α hα,
      show initialForm (maximalIdeal R) (f j) = e (q j) by simp [q],
      hcomm, AlgEquiv.symm_apply_apply]
  have hI' : Ideal.span (Set.range fun j =>
      e'.symm (initialForm (maximalIdeal R') (α (f j)))) =
      I.map (MvPolynomial.map (algebraMap (R ⧸ maximalIdeal R) (R' ⧸ maximalIdeal R'))) := by
    rw [hI, Ideal.map_span, ← Set.range_comp]
    congr 2
    funext j
    exact hq' j
  have hμ : ∀ j, d j ≤ μb := hdμ
  -- forward direction
  have hfwd : ∀ T : Submodule (R ⧸ maximalIdeal R) (AssocGraded (maximalIdeal R)),
      IsTauZSubmodule R f T → IsTauZSubmodule R' (fun j => α (f j))
        (Submodule.span (R' ⧸ maximalIdeal R') (grMapMax α hα '' (T : Set _))) := by
    intro T hT
    have hmv := (isTauZSubmodule_iff_mv e hE f d hd μb hμ T).mp hT
    have hL1 := hmv.1
    set L := T.comap e.toLinearMap with hL
    set L' := Submodule.span (R' ⧸ maximalIdeal R') (MvPolynomial.map
      (algebraMap (R ⧸ maximalIdeal R) (R' ⧸ maximalIdeal R')) ''
        (L : Set (MvPolynomial (Fin n) (R ⧸ maximalIdeal R)))) with hL'
    have hL'1 : L' ≤ MvPolynomial.homogeneousSubmodule (Fin n) (R' ⧸ maximalIdeal R') 1 := by
      rw [hL', Submodule.span_le]
      rintro _ ⟨l, hl, rfl⟩
      exact (hL1 hl).map _
    have hmv' := (isTauSubmoduleMv_map_iff (R ⧸ maximalIdeal R) hsep' I hIhom L' hL'1 μb hμpos).mpr
      (by rw [hL', linearFormsOver_span_map_aux' L hL1]; exact hmv)
    rw [← hI'] at hmv'
    have hT'' : (Submodule.span (R' ⧸ maximalIdeal R') (grMapMax α hα '' (T : Set _))) =
        L'.map e'.toLinearMap := by
      rw [hL', Submodule.map_span, ← Set.image_comp]
      congr 1
      ext y
      constructor
      · rintro ⟨x, hx, rfl⟩
        refine ⟨e.symm x, ?_, ?_⟩
        · simpa [hL] using hx
        · have h := hcomm (e.symm x)
          rw [AlgEquiv.apply_symm_apply] at h
          exact h.symm
      · rintro ⟨p, hp, rfl⟩
        refine ⟨e p, by simpa [hL] using hp, ?_⟩
        exact hcomm p
    rw [hT'']
    refine (isTauZSubmodule_iff_mv e' hE' (fun j => α (f j)) d hd' μb hμ _).mpr ?_
    rw [Submodule.comap_map_eq_of_injective (f := e'.toLinearMap) e'.injective]
    exact hmv'
  -- backward direction
  have hbwd : ∀ T' : Submodule (R' ⧸ maximalIdeal R') (AssocGraded (maximalIdeal R')),
      IsTauZSubmodule R' (fun j => α (f j)) T' →
        ∃ T₀ : Submodule (R ⧸ maximalIdeal R) (AssocGraded (maximalIdeal R)),
          IsTauZSubmodule R f T₀ ∧ ∀ x ∈ T₀, grMapMax α hα x ∈ T' := by
    intro T' hT'
    have hmv := (isTauZSubmodule_iff_mv e' hE' (fun j => α (f j)) d hd' μb hμ T').mp hT'
    rw [hI'] at hmv
    have hL1 := hmv.1
    have hmv2 := (isTauSubmoduleMv_map_iff (R ⧸ maximalIdeal R) hsep' I hIhom _ hL1 μb hμpos).mp hmv
    refine ⟨(linearFormsOver (R ⧸ maximalIdeal R) (T'.comap e'.toLinearMap)).map e.toLinearMap,
      (isTauZSubmodule_iff_mv e hE f d hd μb hμ _).mpr ?_, ?_⟩
    · rw [Submodule.comap_map_eq_of_injective (f := e.toLinearMap) e.injective]
      exact hmv2
    · rintro x ⟨p, hp, rfl⟩
      have hp1 : MvPolynomial.map (algebraMap (R ⧸ maximalIdeal R) (R' ⧸ maximalIdeal R')) p ∈
          T'.comap e'.toLinearMap := hp.1
      have h := hcomm p
      have : e' (MvPolynomial.map (residueQuotMap α) p) ∈ T' := hp1
      exact h ▸ this
  -- conclusion
  refine le_antisymm ?_ ?_
  · refine sInf_le (hfwd _ (tauZSubmodule_spec R f))
  · rw [Submodule.span_le]
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨T₀, hT₀, hT₀'⟩ := hbwd _ (tauZSubmodule_spec R' (fun j => α (f j)))
    have hle : tauZSubmodule R f ≤ T₀ := sInf_le hT₀
    exact hT₀' x (hle hx)


/-- `ᾱ` preserves `k`-linear independence (as `k'`-linear independence of the images): the
`k'`-span of `ᾱ(V)` has the same dimension as `V` (p. 225, proof of Lemma 13: "the `k'`-submodule
generated by `T`"). -/
theorem finrank_span_grMapMax (hα : RingHom.MapsRSOP α)
    (V : Submodule (R ⧸ maximalIdeal R) (AssocGraded (maximalIdeal R)))
    [Module.Finite (R ⧸ maximalIdeal R) V] :
    Module.finrank (R' ⧸ maximalIdeal R')
        (Submodule.span (R' ⧸ maximalIdeal R') (grMapMax α hα '' (V : Set _))) =
      Module.finrank (R ⧸ maximalIdeal R) V := by
  classical
  let _ : Field (R ⧸ maximalIdeal R) := Ideal.Quotient.field _
  let _ : Field (R' ⧸ maximalIdeal R') := Ideal.Quotient.field _
  let _ : Algebra (R ⧸ maximalIdeal R) (R' ⧸ maximalIdeal R') := (residueQuotMap α).toAlgebra
  obtain ⟨n, e, e', hE, hE', hcomm⟩ := exists_polyModel α hα
  let b := Module.finBasis (R ⧸ maximalIdeal R) V
  have hvli : LinearIndependent (R ⧸ maximalIdeal R) fun j => e.symm (b j : AssocGraded _) :=
    (b.linearIndependent.map' V.subtype (Submodule.ker_subtype _)).map' e.symm.toLinearMap
      (LinearMap.ker_eq_bot.mpr e.symm.injective)
  have hwli := linearIndependent_map_aux' (k' := R' ⧸ maximalIdeal R') hvli
  have hli : LinearIndependent (R' ⧸ maximalIdeal R')
      fun j => grMapMax α hα (b j : AssocGraded _) := by
    have := hwli.map' e'.toLinearMap (LinearMap.ker_eq_bot.mpr e'.injective)
    convert this using 2 with j
    have h := hcomm (e.symm (b j : AssocGraded _))
    rw [AlgEquiv.apply_symm_apply] at h
    exact h
  have key : ∀ y ∈ Submodule.span (R ⧸ maximalIdeal R)
      (Set.range fun j => (b j : AssocGraded (maximalIdeal R))),
      grMapMax α hα y ∈ Submodule.span (R' ⧸ maximalIdeal R')
        (Set.range fun j => grMapMax α hα (b j : AssocGraded _)) := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨j, rfl⟩ := hy
      exact Submodule.subset_span ⟨j, rfl⟩
    | zero => rw [map_zero]; exact zero_mem _
    | add y z _ _ hy hz => rw [map_add]; exact add_mem hy hz
    | smul c y _ hy =>
      rw [grMapMax_smul α hα]
      exact Submodule.smul_mem _ _ hy
  have hspan : Submodule.span (R' ⧸ maximalIdeal R') (grMapMax α hα '' (V : Set _)) =
      Submodule.span (R' ⧸ maximalIdeal R')
        (Set.range fun j => grMapMax α hα (b j : AssocGraded _)) := by
    refine le_antisymm (Submodule.span_le.mpr ?_) (Submodule.span_mono ?_)
    · rintro _ ⟨x, hx, rfl⟩
      have hxs : (⟨x, hx⟩ : V) ∈ Submodule.span (R ⧸ maximalIdeal R) (Set.range b) := by
        rw [b.span_eq]; trivial
      have hx' : x ∈ Submodule.span (R ⧸ maximalIdeal R)
          (Set.range fun j => (b j : AssocGraded _)) := by
        have := Submodule.apply_mem_span_image_of_mem_span V.subtype hxs
        rwa [← Set.range_comp] at this
      exact key x hx'
    · rintro _ ⟨j, rfl⟩
      exact ⟨(b j : AssocGraded _), (b j).2, rfl⟩
  rw [hspan, finrank_span_eq_card hli]
  simp


/-- `T` is finite dimensional: it lies in `gr¹_M(R)`. -/
theorem finite_tauZSubmodule {i : ℕ} (f : Fin i → R) :
    Module.Finite (R ⧸ maximalIdeal R) (tauZSubmodule R f) := by
  let _ : Field (R ⧸ maximalIdeal R) := Ideal.Quotient.field _
  have : FiniteDimensional (R ⧸ maximalIdeal R) (AssocGraded.homogeneous (maximalIdeal R) 1) := by
    refine Module.Finite.iff_fg.mpr ?_
    rw [AssocGraded.homogeneous, LinearMap.range_eq_map]
    exact Module.Finite.fg_top.map _
  exact Submodule.finiteDimensional_of_le (tauZSubmodule_spec R f).1

/-- **`τ_{(z)}` is invariant under the base change `α`**: if `α : R → R'` transforms a regular
system of parameters into one, with separable residue field extension, then
`τ_{(α z)}(α f₁, …, α f_i) = τ_{(z)}(f₁, …, f_i)`.  (Lemma 12 of §4 for the `T` of
Definition 10*; used in the reductions "we may assume that `R` is complete and `R₁` residually
rational" of pp. 254, 256, 258.) -/
theorem tauZ_map [Hironaka.Cited.IsSeparableFieldExtensionIff.{u}] (hα : RingHom.MapsRSOP α) (hsep : RingHom.IsResiduallySeparable α) {r i : ℕ}
    (z : Fin r → R) (f : Fin i → R) :
    tauZ R' (fun j => α (z j)) (fun j => α (f j)) = tauZ R z f := by
  classical
  let _ : Field (R ⧸ maximalIdeal R) := Ideal.Quotient.field _
  let _ : Field (R' ⧸ maximalIdeal R') := Ideal.Quotient.field _
  unfold tauZ tauZSubmoduleStar
  have hfin := finite_tauZSubmodule f
  have hfr : Module.Finite (R ⧸ maximalIdeal R)
      (Submodule.span (R ⧸ maximalIdeal R) (Set.range (frameForm z))) :=
    Module.Finite.span_of_finite _ (Set.finite_range _)
  have hfinV : Module.Finite (R ⧸ maximalIdeal R) (tauZSubmodule R f ⊔
      Submodule.span (R ⧸ maximalIdeal R) (Set.range (frameForm z)) :
        Submodule (R ⧸ maximalIdeal R) (AssocGraded (maximalIdeal R))) := inferInstance
  have hT := tauZSubmodule_map α hα hsep f
  have hz : ∀ j, frameForm (fun j => α (z j)) j = grMapMax α hα (frameForm z j) := fun j =>
    initialForm_map_of_mapsRSOP α hα (z j)
  have hsup : tauZSubmodule R' (fun j => α (f j)) ⊔
      Submodule.span (R' ⧸ maximalIdeal R') (Set.range (frameForm fun j => α (z j))) =
      Submodule.span (R' ⧸ maximalIdeal R') (grMapMax α hα '' ((tauZSubmodule R f ⊔
        Submodule.span (R ⧸ maximalIdeal R) (Set.range (frameForm z)) :
          Submodule (R ⧸ maximalIdeal R) (AssocGraded (maximalIdeal R))) : Set _)) := by
    rw [hT]
    have hrange : Set.range (frameForm fun j => α (z j)) =
        grMapMax α hα '' Set.range (frameForm z) := by
      rw [← Set.range_comp]
      exact congrArg Set.range (funext hz)
    rw [hrange]
    refine le_antisymm (sup_le (Submodule.span_mono (Set.image_mono ?_))
      (Submodule.span_le.mpr ?_)) (Submodule.span_le.mpr ?_)
    · exact fun x hx => Submodule.mem_sup_left hx
    · rintro _ ⟨x, hx, rfl⟩
      exact Submodule.subset_span ⟨x, Submodule.mem_sup_right (Submodule.subset_span hx), rfl⟩
    · rintro _ ⟨y, hy, rfl⟩
      obtain ⟨t, ht, w, hw, rfl⟩ := Submodule.mem_sup.mp hy
      rw [map_add]
      exact add_mem (Submodule.mem_sup_left (Submodule.subset_span ⟨t, ht, rfl⟩))
        (Submodule.mem_sup_right (grMapMax_mem_span_image α hα _ hw))
  rw [hsup, finrank_span_grMapMax α hα]

end TauZMap

end GrMap

section FrameAlgHom

open MvPolynomial

variable {R R' : Type u} [CommRing R] [CommRing R'] [IsRegularLocalRing R]
  [IsRegularLocalRing R'] (α : R →+* R') [IsLocalHom α]

/-- `ᾱ` carries the polynomial map `k[Z] → gr_M(R)`, `Z_j ↦ [z_j]`, of a system `z` to that of
the system `α(z)` (coefficientwise extension `k → k'`). -/
theorem grMapMax_frameAlgHom (hα : RingHom.MapsRSOP α) {r : ℕ} (z : Fin r → R) (z' : Fin r → R')
    (hz : ∀ j, z' j = α (z j)) (p : MvPolynomial (Fin r) (R ⧸ maximalIdeal R)) :
    grMapMax α hα (frameAlgHom z p) =
      frameAlgHom z' (MvPolynomial.map (residueQuotMap α) p) := by
  have : (grMapMax α hα).comp (frameAlgHom z : MvPolynomial (Fin r) (R ⧸ maximalIdeal R) →+*
      AssocGraded (maximalIdeal R)) =
      (frameAlgHom z' : MvPolynomial (Fin r) (R' ⧸ maximalIdeal R') →+*
        AssocGraded (maximalIdeal R')).comp (MvPolynomial.map (residueQuotMap α)) := by
    refine MvPolynomial.ringHom_ext (fun c => ?_) (fun j => ?_)
    · obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective c
      simp only [RingHom.coe_comp, Function.comp_apply, RingHom.coe_coe, MvPolynomial.map_C,
        frameAlgHom, MvPolynomial.aeval_C]
      rw [← AssocGraded.mk_zero_eq_algebraMap _ a (by simp), grMapMax_mk α hα 0 a _ (by simp),
        residueQuotMap_mk, ← AssocGraded.mk_zero_eq_algebraMap]
    · simp only [RingHom.coe_comp, Function.comp_apply, RingHom.coe_coe, MvPolynomial.map_X,
        frameAlgHom, MvPolynomial.aeval_X, frameForm]
      rw [hz j]
      exact (initialForm_map_of_mapsRSOP α hα (z j)).symm
  exact RingHom.congr_fun this p

end FrameAlgHom


section MuTau

variable {R R' : Type u} [CommRing R] [CommRing R'] [IsRegularLocalRing R]
  [IsRegularLocalRing R'] (α : R →+* R') [IsLocalHom α]

/-- The set of integers `μ` appearing in `ν*(J)` is unchanged by the base change `α`
(Corollary to Lemma 2). -/
theorem muSet_map_of_mapsRSOP (hα : RingHom.MapsRSOP α) (J : Ideal R) :
    muSet R' (J.map α) = muSet R J := by
  ext μ
  simp only [muSet, Set.mem_ofPred_eq]
  simp only [← nuI_map_eq_of_mapsRSOP α hα J]

/-- `μ^{(a)}(J) = μ^{(a)}(J R')` (Corollary to Lemma 2). -/
theorem mu_map_of_mapsRSOP (hα : RingHom.MapsRSOP α) (J : Ideal R) (a : ℕ) :
    mu R' (J.map α) a = mu R J a := by
  unfold mu
  rw [muSet_map_of_mapsRSOP α hα]

omit [IsRegularLocalRing R'] [IsLocalHom α] in
/-- If `μ^{(a)}(J) = 0` (the junk value for `a > t(J)`, or `J = R`), then `τ^{(a)}(J) = 0`: the
empty system of linear forms has the property of Definition 6 up to degree `0`. -/
theorem tau_eq_zero_of_mu_eq_zero (J : Ideal R) (a : ℕ) (h : mu R J a = 0) : tau R J a = 0 := by
  let _ : Field (R ⧸ maximalIdeal R) := Ideal.Quotient.field _
  refine Nat.eq_zero_of_le_zero (tau_le R J (Fin.elim0 : Fin 0 → _) (fun i => i.elim0) ?_)
  rw [h]
  refine ⟨?_, fun μ hμ ψ hψ => ⟨fun hJ => ?_, fun hJ => ?_⟩⟩
  · rw [Submodule.span_le]
    rintro _ ⟨i, _⟩
    exact i.elim0
  · have hμ0 : μ = 0 := Nat.le_zero.mp hμ
    subst hμ0
    obtain ⟨y, hy, rfl⟩ := AssocGraded.exists_mk_eq_of_mem_homogeneous _ hψ
    refine Ideal.subset_span ⟨hJ, ?_⟩
    rw [AssocGraded.mk_zero_eq_algebraMap _ y (by simp)]
    exact Subalgebra.algebraMap_mem _ _
  · exact (Ideal.span_le.mpr fun x hx => hx.1) hJ

/-- `τ^{(a)}(J R') = τ^{(a)}(J)` for all `a ≥ 1`, also outside the range `a ≤ t(J)` (where both
sides are `0`; Lemma 13 for the range `a ≤ t(J)`). -/
theorem tau_map_of_mapsRSOP [Hironaka.Cited.IsSeparableFieldExtensionIff.{u}] (hα : RingHom.MapsRSOP α) (hsep : RingHom.IsResiduallySeparable α)
    (J : Ideal R) (a : ℕ) (ha : 1 ≤ a) : tau R' (J.map α) a = tau R J a := by
  by_cases hat : a ≤ t R J
  · exact (tauStar_map α hα hsep J).2.1 a ha hat
  · have hfin := (muSet_finite R J).1
    have h1 : mu R J a = 0 := by
      unfold mu
      refine Nat.nth_of_card_le hfin ?_
      have hc : (muSet R J).ncard ≤ a - 1 := by
        unfold t at hat
        omega
      rw [Set.ncard_eq_toFinset_card _ hfin] at hc
      exact hc
    rw [tau_eq_zero_of_mu_eq_zero J a h1,
      tau_eq_zero_of_mu_eq_zero (J.map α) a (by rw [mu_map_of_mapsRSOP α hα, h1])]

end MuTau

end Hironaka
