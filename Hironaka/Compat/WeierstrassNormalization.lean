/-
Copyright (c) 2026 Daattavya Aggarwal, Minhyong Kim, Oisin Kim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daattavya Aggarwal, Minhyong Kim, Oisin Kim
-/
module

public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Hironaka.Compat.WeierstrassAdaptedCoordinates
public import Hironaka.Compat.WeierstrassTauLift
public import Hironaka.Compat.TauZSystem
public import Hironaka.Ch3.JStability
public import Hironaka.Statements

/-!
# Lemma 25, (ii) of (c) (pp. 271--272): the two "we may assume" normalizations

> "Let us choose a minimal base `(y₁, ⋯, y_i)` of `Q₀` in such a way that `y = y_i` and
> `ȳ_j = y_j/y ∈ M₁` for `1 ≤ j ≤ i − 1`.  Lemma 24 shows that, if `τ = τ_{(z)}(f) − 1`
> (`= τ_{(z,w)}(f)`), there exist `τ` independent linear combinations of `y₁, ⋯, y_{i−1}` with
> coefficients in `S₀` which form a regular system of `τ_{(z,w)}`-parameters of `R` for `f`.
> Therefore, we may assume that `(w, y₁, ⋯, y_τ)` is a regular system of `τ_{(z)}`-parameters of
> `R` for `f` (`τ ≤ i − 1`)."  (pp. 271--272)

> "We can find linear combinations `v₁, ⋯, v_τ` of `y, x₁, ⋯, x_a` with coefficients in `S₀` such
> that `L_j` is the initial form of `v_j` in `gr_M(R)` (hence, in `gr_{M₁}(R₁)`) for `1 ≤ j ≤ τ`.
> We may replace `y_j` by `y_j + v_j y` for `1 ≤ j ≤ τ` without affecting any of the assumptions on
> `(y₁, ⋯, y_b)` in the above argument, so that we may assume that `L₁ = ⋯ = L_τ = 0`."  (p. 272)

Both normalizations are changes of the coordinates `(y₁, …, y_b)` of
`WeierstrassDatum.AdaptedCoords` (`AdaptedCoords.recoord`: `y_j ↦ ∑_l C_{jl} y_l + v_j y`).

* `AdaptedCoords.tauStar_le_sup` is the use of Lemma 24 (`mem_maximalIdeal_of_ordElem_eq`):
  every element of `T*` is a combination of `Z₁, …, Z_r, W, Y₁, …, Y_b` (no `Y`, `X_k`), because a
  regular system of `τ_{(z)}`-parameters through any element of `T*` may be taken in `P`, and its
  quotients by `y` lie in `M₁`;
* `AdaptedCoords.exists_tauNormalized` produces the `τ` independent combinations and the
  invertible matrix `C` over `S₀` ("we may assume that `(w, y₁, ⋯, y_τ)` is a regular system of
  `τ_{(z)}`-parameters");
* `AdaptedCoords.exists_shift` carries out "We may replace `y_j` by `y_j + v_j y`": the model of `gr_M(R)` is unchanged (the
  initial form of `y_j + v_j y` is `Y_j`) and the model of `gr_{M₁}(R₁)` is composed with the
  substitution `Ȳ_j ↦ Ȳ_j + L_j` (the initial form of `ȳ_j + v_j` is `Ȳ_j + L_j`).
-/

@[expose] public section

open IsLocalRing MvPolynomial Matrix

namespace Hironaka

universe u

section LinearAlgebra

variable {k V : Type*} [Field k] [AddCommGroup V] [Module k V]

/-- A linearly independent family of `τ` vectors in a space of dimension `t` extends to a linearly
independent family of `t` vectors. -/
theorem exists_linearIndependent_extend_fin [FiniteDimensional k V] {τ t : ℕ}
    (ht : Module.finrank k V = t) (hτt : τ ≤ t) (v : Fin τ → V) (hv : LinearIndependent k v) :
    ∃ w : Fin t → V, LinearIndependent k w ∧ ∀ j, w (Fin.castLE hτt j) = v j := by
  have key : ∀ d, τ + d ≤ t → ∃ w : Fin (τ + d) → V, LinearIndependent k w ∧
      ∀ j, w (Fin.castAdd d j) = v j := by
    intro d
    induction d with
    | zero =>
      intro _
      refine ⟨v ∘ Fin.cast (add_zero τ), hv.comp _ (Fin.cast_injective _), fun j => ?_⟩
      simp only [Function.comp_apply]
      congr 1
    | succ d ih =>
      intro hd
      obtain ⟨w, hw, hwv⟩ := ih (by omega)
      obtain ⟨x, hx⟩ := exists_linearIndependent_snoc_of_lt_finrank hw (by omega)
      refine ⟨Fin.snoc w x, hx, fun j => ?_⟩
      have : (Fin.castAdd (d + 1) j : Fin (τ + (d + 1))) = Fin.castSucc (Fin.castAdd d j) :=
        Fin.ext rfl
      rw [this, Fin.snoc_castSucc, hwv]
  obtain ⟨w, hw, hwv⟩ := key (t - τ) (by omega)
  refine ⟨w ∘ Fin.cast (by omega), hw.comp _ (Fin.cast_injective _), fun j => ?_⟩
  simp only [Function.comp_apply]
  rw [← hwv j]
  congr 1

/-- **The normalization by a change of basis** (the linear algebra of "we may assume that
`(w, y₁, ⋯, y_τ)` is a regular system of `τ_{(z)}`-parameters", p. 272): let `Z` and `Y` be families
of vectors, jointly linearly independent, and `T` a subspace containing the `Z`'s, contained in the
span of the `Z`'s and `Y`'s and of dimension `m + τ`.  Then there is an invertible matrix `C` such
that the `Z`'s and the first `τ` of the combinations `∑_l C_{jl} Y_l` span `T`. -/
theorem exists_isUnit_matrix_span_eq {m t τ : ℕ} (Z : Fin m → V) (Y : Fin t → V)
    (hli : LinearIndependent k (Sum.elim Z Y)) (Ts : Submodule k V)
    (hZT : Submodule.span k (Set.range Z) ≤ Ts)
    (hT : Ts ≤ Submodule.span k (Set.range Z) ⊔ Submodule.span k (Set.range Y))
    [FiniteDimensional k Ts] (hτ : Module.finrank k Ts = m + τ) :
    ∃ (hτt : τ ≤ t) (C : Matrix (Fin t) (Fin t) k), IsUnit C ∧
      Submodule.span k (Set.range Z ∪
        Set.range (fun j : Fin τ => ∑ l, C (Fin.castLE hτt j) l • Y l)) = Ts := by
  classical
  obtain ⟨hZ, hY, hdisj⟩ := linearIndependent_sum.mp hli
  have hZ' : LinearIndependent k Z := hZ
  have hY' : LinearIndependent k Y := hY
  have hdisj' : Disjoint (Submodule.span k (Set.range Z)) (Submodule.span k (Set.range Y)) := by
    simpa using hdisj
  set Λ : (Fin t → k) →ₗ[k] V := Fintype.linearCombination k Y with hΛ
  have hΛinj : Function.Injective Λ :=
    linearIndependent_iff_injective_fintypeLinearCombination.mp hY'
  have hΛrange : LinearMap.range Λ = Submodule.span k (Set.range Y) :=
    Fintype.range_linearCombination k Y
  set N := Submodule.span k (Set.range Z) with hN
  set W₀ : Submodule k (Fin t → k) := Ts.comap Λ with hW₀
  have hTs : Ts = N ⊔ W₀.map Λ := by
    apply le_antisymm
    · intro x hx
      obtain ⟨n, hn, e, he, rfl⟩ := Submodule.mem_sup.mp (hT hx)
      rw [← hΛrange] at he
      obtain ⟨a, rfl⟩ := he
      refine Submodule.mem_sup.mpr ⟨n, hn, Λ a, ⟨a, ?_, rfl⟩, rfl⟩
      show Λ a ∈ Ts
      have : Λ a = (n + Λ a) - n := by abel
      rw [this]
      exact sub_mem hx (hZT hn)
    · exact sup_le hZT (Submodule.map_comap_le _ _)
  have hdisjW : Disjoint N (W₀.map Λ) := by
    refine hdisj'.mono_right ?_
    rw [← hΛrange]
    exact LinearMap.map_le_range
  have hfinN : Module.finrank k N = m := by
    rw [hN, finrank_span_eq_card hZ', Fintype.card_fin]
  have hfinW : Module.finrank k (W₀.map Λ) = Module.finrank k W₀ :=
    (LinearEquiv.finrank_eq (Submodule.equivMapOfInjective Λ hΛinj W₀)).symm
  have : FiniteDimensional k N := FiniteDimensional.span_of_finite k (Set.finite_range Z)
  have : FiniteDimensional k (W₀.map Λ) :=
    LinearEquiv.finiteDimensional (Submodule.equivMapOfInjective Λ hΛinj W₀)
  have hsum : Module.finrank k (N ⊔ W₀.map Λ : Submodule k V) =
      Module.finrank k N + Module.finrank k (W₀.map Λ) := by
    have h := Submodule.finrank_sup_add_finrank_inf_eq N (W₀.map Λ)
    rw [disjoint_iff.mp hdisjW, finrank_bot, add_zero] at h
    exact h
  have hfinW₀ : Module.finrank k W₀ = τ := by
    have h1 : Module.finrank k Ts = Module.finrank k (N ⊔ W₀.map Λ : Submodule k V) := by
      rw [← hTs]
    rw [hτ, hsum, hfinN, hfinW] at h1
    omega
  have hτt : τ ≤ t := by
    have := Submodule.finrank_le W₀
    rw [hfinW₀, Module.finrank_fin_fun] at this
    exact this
  let b := Module.finBasisOfFinrankEq k W₀ hfinW₀
  have hbli : LinearIndependent k (fun j => (b j : Fin t → k)) :=
    b.linearIndependent.map' W₀.subtype (Submodule.ker_subtype W₀)
  obtain ⟨w, hw, hwb⟩ := exists_linearIndependent_extend_fin (Module.finrank_fin_fun k) hτt _ hbli
  refine ⟨hτt, Matrix.of w, ?_, ?_⟩
  · exact Matrix.linearIndependent_rows_iff_isUnit.mp hw
  · have hrange : Set.range (fun j : Fin τ => ∑ l, (Matrix.of w) (Fin.castLE hτt j) l • Y l) =
        Λ '' Set.range (fun j => (b j : Fin t → k)) := by
      rw [← Set.range_comp]
      refine congrArg Set.range (funext fun j => ?_)
      simp only [Function.comp_apply, hΛ, Fintype.linearCombination_apply, Matrix.of_apply, hwb]
    have hspanb : Submodule.span k (Set.range (fun j => (b j : Fin t → k))) = W₀ := by
      have h1 : Set.range (fun j => (b j : Fin t → k)) = W₀.subtype '' Set.range b := by
        rw [← Set.range_comp]; rfl
      rw [h1, Submodule.span_image, b.span_eq, Submodule.map_subtype_top]
    rw [Submodule.span_union, hrange, Submodule.span_image, hspanb, ← hTs]

end LinearAlgebra

section ModelComp

open scoped Classical

attribute [local instance] Ideal.Quotient.field

/-- Two polynomial pictures `X_i ↦ [v_i]` of `gr_M(A)` over the same field: if the class of each
`v₂ i` is the image under the first picture of a polynomial `σ i`, the second picture is the first
composed with the substitution `X_i ↦ σ i`. -/
theorem gradedSemiModel_apply_eq_aeval {A : Type u} [CommRing A] [IsRegularLocalRing A]
    {K : Type u} [Field K] (ρ : K ≃+* A ⧸ maximalIdeal A) {n : ℕ} (v₁ v₂ : Fin n → A)
    (h₁ : Ideal.span (Set.range v₁) = maximalIdeal A) (hd₁ : (n : WithBot ℕ∞) = ringKrullDim A)
    (h₂ : Ideal.span (Set.range v₂) = maximalIdeal A) (hd₂ : (n : WithBot ℕ∞) = ringKrullDim A)
    (σ : Fin n → MvPolynomial (Fin n) K)
    (h : ∀ i, AssocGraded.mk (maximalIdeal A) 1 (v₂ i) (mem_pow_one_of_span_eq h₂ i) =
      (gradedSemiModel ρ v₁ h₁ hd₁).Φ (σ i)) (p : MvPolynomial (Fin n) K) :
    (gradedSemiModel ρ v₂ h₂ hd₂).Φ p = (gradedSemiModel ρ v₁ h₁ hd₁).Φ (aeval σ p) := by
  have key : (gradedSemiModel ρ v₂ h₂ hd₂).Φ.toRingHom =
      (gradedSemiModel ρ v₁ h₁ hd₁).Φ.toRingHom.comp
        (aeval σ : MvPolynomial (Fin n) K →ₐ[K] MvPolynomial (Fin n) K).toRingHom := by
    refine MvPolynomial.ringHom_ext (fun r => ?_) (fun i => ?_)
    · simp only [RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, RingHom.comp_apply,
        AlgHom.toRingHom_eq_coe, aeval_C, (gradedSemiModel ρ v₂ h₂ hd₂).map_C]
      rw [MvPolynomial.algebraMap_eq, (gradedSemiModel ρ v₁ h₁ hd₁).map_C]
      rfl
    · simp only [RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, RingHom.comp_apply,
        AlgHom.toRingHom_eq_coe, aeval_X, gradedSemiModel_X]
      exact h i
  exact RingHom.congr_fun key p

/-- An element of the span of the variables of a set `S` is the combination of those variables
with its coefficients. -/
theorem eq_sum_coeff_smul_X_of_mem_linSpan {K : Type u} [Field K] {n : ℕ} (S : Set (Fin n))
    {t : MvPolynomial (Fin n) K} (ht : t ∈ linSpan (k := K) S) :
    t = ∑ i, (if i ∈ S then t.coeff (Finsupp.single i 1) else 0) •
      (X i : MvPolynomial (Fin n) K) := by
  have hlin : ∀ t : MvPolynomial (Fin n) K,
      (∑ i, (if i ∈ S then t.coeff (Finsupp.single i 1) else 0) • (X i : MvPolynomial (Fin n) K)) =
        ∑ i, (t.coeff (Finsupp.single i 1)) • (if i ∈ S then X i else 0) := by
    intro t
    refine Finset.sum_congr rfl fun i _ => ?_
    split_ifs <;> simp
  rw [hlin]
  refine Submodule.span_induction (p := fun t _ => t = ∑ i, (t.coeff (Finsupp.single i 1)) •
    (if i ∈ S then (X i : MvPolynomial (Fin n) K) else 0)) ?_ ?_ ?_ ?_ ht
  · rintro _ ⟨v, hv, rfl⟩
    rw [Finset.sum_eq_single v]
    · simp [hv]
    · intro i _ hiv
      rw [coeff_X, ite_eq_right]
      · simp
      · intro h
        exact hiv (Finsupp.single_left_injective one_ne_zero h).symm
    · simp
  · simp
  · intro a b _ _ ha hb
    have e : ∀ i, (a + b).coeff (Finsupp.single i 1) =
        a.coeff (Finsupp.single i 1) + b.coeff (Finsupp.single i 1) := fun i => by simp
    simp only [e, add_smul, Finset.sum_add_distrib]
    rw [← ha, ← hb]
  · intro r a _ ha
    simp only [coeff_smul, smul_eq_mul, mul_smul, ← Finset.smul_sum]
    rw [← ha]

/-- The pull-back of subspaces along a polynomial picture is injective. -/
theorem SemiModel.pull_injective {k k₁ G : Type u} [Field k] [Field k₁] [CommRing G] [Algebra k₁ G]
    {n : ℕ} (M : SemiModel k k₁ G n) {T T' : Submodule k₁ G} (h : M.pull T = M.pull T') :
    T = T' := by
  ext x
  have hx : x = M.Φ (M.Φ.symm x) := (RingEquiv.apply_symm_apply _ x).symm
  rw [hx, ← SemiModel.mem_pull, ← SemiModel.mem_pull, h]

/-- The pull-back only depends on the isomorphism of the picture. -/
theorem SemiModel.pull_eq_of_Φ_eq {k k₁ G : Type u} [Field k] [Field k₁] [CommRing G]
    [Algebra k₁ G] {n : ℕ} {M M' : SemiModel k k₁ G n} (h : M.Φ = M'.Φ) (T : Submodule k₁ G) :
    M.pull T = M'.pull T := by
  ext p
  rw [SemiModel.mem_pull, SemiModel.mem_pull, h]

end ModelComp

section Lemma24

attribute [local instance] RegularFrame.isDomain_S
attribute [local instance] Ideal.Quotient.field

variable {R : Type u} [CommRing R] [IsRegularLocalRing R] [IsDomain R] {D : WeierstrassDatum R}
  {P : Ideal R} [P.IsPrime] [IsRegularLocalRing (R ⧸ P)] {T : MonoidalTransform R P}
  [IsLocalHom T.toRing] [IsRegularLocalRing T.ring]
  {FT' : D.F.FrameTransform T} {FT0 : D.F0.FrameTransform FT'.TS} {y : D.F0.S}
  {hx : FT'.x = T.toRing (algebraMap D.F.S R (algebraMap D.F0.S D.F.S y))}
  {hx0 : FT0.x = FT'.TS.toRing (algebraMap D.F0.S D.F.S y)}

namespace WeierstrassDatum.AdaptedCoords

variable {t s : ℕ} (c : D.AdaptedCoords FT' FT0 y hx hx0 t s)

omit [IsRegularLocalRing (R ⧸ P)] [IsLocalHom T.toRing] in
theorem coordV_mem (i : Fin c.n) :
    coordV (F := D.compositeFrame) y c.xs c.ys i ∈ maximalIdeal R ^ 1 :=
  mem_pow_one_of_span_eq c.span_R i

omit [IsRegularLocalRing (R ⧸ P)] [IsLocalHom T.toRing] in
theorem algR_xs_mem (l : Fin t) : D.algR (c.xs l) ∈ maximalIdeal R ^ 1 :=
  c.coordV_yI l ▸ c.coordV_mem (c.yI l)

omit [IsRegularLocalRing (R ⧸ P)] [IsLocalHom T.toRing] in
include c in
theorem algR_y_mem : D.algR y ∈ maximalIdeal R := by
  have h := c.coordV_mem (Fin.natAdd (D.compositeFrame.r + t) 0)
  simp only [coordV, Fin.append_right, Fin.cons_zero, pow_one] at h
  exact h

omit [IsRegularLocalRing (R ⧸ P)] [IsLocalHom T.toRing] in
theorem coordV₁_mem (i : Fin c.n) :
    coordV₁ (D.compositeFrameTransform FT' FT0 y hx hx0) c.ys
      (fun k => (FT'.β.comp FT0.β) (c.u' k)) i ∈ maximalIdeal T.ring := by
  rw [← c.span_R₁]
  exact Ideal.subset_span ⟨i, rfl⟩

omit [IsLocalHom T.toRing] in
/-- **The use of Lemma 24 in (ii) of (c)** (p. 271: "Lemma 24 shows that […] there exist `τ`
independent linear combinations of `y₁, ⋯, y_{i−1}` with coefficients in `S₀` which form a regular
system of `τ_{(z,w)}`-parameters of `R` for `f`"): `T*` of `f` (for `(z)`) is contained in the span
of `Z₁, …, Z_r, W` and `Y₁, …, Y_b` (no component along `Y = in(y)` and the `X_k`).

Gap filled (the paper gives no argument).  Let `t ∈ T*` lie outside `⟨Z₁, …, Z_r⟩`.  `T*`
consists of classes of elements of `P` (`f ∈ P^ν` with `ν = ν_M(f)`,
`tauZSubmoduleStar_le_classSubmodule`), so `t` is the class of some `a ∈ P` which is a member of a
regular system `(x₁, …, x_τ)` of `τ_{(z)}`-parameters of `R` for `f` contained in `P`
(`exists_isRegularSystemOfTauZParameters_of_mem`).  Lemma 24 (`mem_maximalIdeal_of_ordElem_eq`,
with `ν_P(f) = ν_M(f)`, `z̄_j ∈ M₁` and `ν_{M₁}(f̄) = ν_M(f)`) gives `a/y ∈ M₁`.  Writing
`a = ∑ α_i g_i + δ y` with `g = (z, w, y₁, …, y_b)` (`P = (z, w, y₁, …, y_b, y)R`),
`a/y = ∑ α_i (g_i/y) + δ` with all `g_i/y ∈ M₁`, so `δ ∈ M` and the class of `a` is
`∑ ᾱ_i [g_i]`. -/
theorem tauStar_le_sup [Hironaka.HironakaCitedResults.{u}] [CharZero (ResidueField R)] {f : R} (hz : D.F.idealZ ≤ P)
    (hP : Ideal.ordElem P f = Ideal.ordElem (maximalIdeal R) f) {ν : ℕ}
    (hν : (ν : ℕ∞) = Ideal.ordElem (maximalIdeal R) f) {f₂ : T.ring}
    (hf₂ : FT'.x ^ ν * f₂ = T.toRing f) (hord₂ : Ideal.ordElem (maximalIdeal T.ring) f₂ = ν) :
    tauZSubmoduleStar R D.F.z (fun _ : Fin 1 => f) ≤
      Submodule.span (R ⧸ maximalIdeal R)
          (Set.range (frameForm (Fin.snoc D.F.z D.wR : Fin (D.F.r + 1) → R))) ⊔
        Submodule.span (R ⧸ maximalIdeal R) (Set.range (fun l =>
          AssocGraded.mk (maximalIdeal R) 1 (D.algR (c.xs l)) (c.algR_xs_mem l))) := by
  classical
  have hdom1 : IsDomain T.ring := Transforms.isDomain_of_isRegularLocalRing _
  set N := Submodule.span (R ⧸ maximalIdeal R)
    (Set.range (frameForm (Fin.snoc D.F.z D.wR : Fin (D.F.r + 1) → R))) with hN
  set E := Submodule.span (R ⧸ maximalIdeal R) (Set.range (fun l =>
    AssocGraded.mk (maximalIdeal R) 1 (D.algR (c.xs l)) (c.algR_xs_mem l))) with hE
  have hzM : ∀ j, D.F.z j ∈ maximalIdeal R := fun j =>
    D.F.extends_rsop.mem_maximalIdeal (Finset.mem_image_of_mem _ (Finset.mem_univ j))
  have hz1 := (linearIndependent_frameForm D.F.z_injective D.F.extends_rsop).2
  have hzw1 := (linearIndependent_frameForm D.injective_snoc D.extendsToRSOP_snoc).2
  have hPM : P ≤ maximalIdeal R := le_maximalIdeal (Ideal.IsPrime.ne_top ‹_›)
  have hzP : ∀ j, D.F.z j ∈ P := fun j => hz (Ideal.subset_span ⟨j, rfl⟩)
  have hfP : f ∈ P ^ ν := Ideal.mem_pow_of_ordElem (hP.trans hν.symm)
  have hU := tauZSubmoduleStar_le_classSubmodule hz1 P hPM hzP hν.symm hfP
  have hZN : Submodule.span (R ⧸ maximalIdeal R) (Set.range (frameForm D.F.z)) ≤ N := by
    refine Submodule.span_mono ?_
    rintro _ ⟨j, rfl⟩
    exact ⟨Fin.castSucc j, by simp [frameForm]⟩
  have hFTx0 : FT'.x ≠ 0 := by
    intro h0
    have h1 : P.map T.toRing = ⊥ := by rw [← FT'.span_x, h0, Ideal.span_singleton_eq_bot]
    exact T.x_ne_zero (T.toRing_injective ((Ideal.mem_bot.mp
      (h1 ▸ Ideal.mem_map_of_mem T.toRing T.x_mem)).trans (map_zero _).symm))
  have hxy : T.toRing (D.algR y) = FT'.x := hx.symm
  intro v hv
  by_cases hvZ : v ∈ Submodule.span (R ⧸ maximalIdeal R) (Set.range (frameForm D.F.z))
  · exact Submodule.mem_sup_left (hZN hvZ)
  obtain ⟨a, haM, haP, rfl⟩ := exists_lift_of_mem_classSubmodule (hU hv)
  obtain ⟨X, hX, hXP, i₀, hi₀⟩ := exists_isRegularSystemOfTauZParameters_of_mem
    D.F.z_injective D.F.extends_rsop hU haP haM hv hvZ
  -- Lemma 24: `a/y ∈ M₁`
  have hyP : D.algR y ∈ P := by
    have h : D.algR y ∈ Ideal.span (Set.range (Fin.append (Fin.snoc D.F.z D.wR :
        Fin (D.F.r + 1) → R) (fun k => D.algR (c.xs k))) ∪ {D.algR y}) :=
      Ideal.subset_span (Or.inr rfl)
    rwa [← c.P_eq] at h
  have hxspan : Ideal.span {T.toRing (D.algR y)} = P.map T.toRing := by
    rw [hxy, FT'.span_x]
  have hyb : ∀ j, ∃ b, T.toRing (D.algR y) * b = T.toRing (X j : R) := fun j => by
    have : T.toRing (X j : R) ∈ Ideal.span {T.toRing (D.algR y)} :=
      hxspan ▸ Ideal.mem_map_of_mem _ (hXP j)
    obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.mp this
    exact ⟨b, by rw [mul_comm]; exact hb⟩
  choose yb hyb using hyb
  have h24 := mem_maximalIdeal_of_ordElem_eq D.F.z hzM D.F.extends_rsop f X hX P
    (Ideal.span_le.mpr (by
      rintro _ (⟨j, rfl⟩ | ⟨j, rfl⟩)
      · exact hzP j
      · exact hXP j))
    hP T (D.algR y) hyP hxspan ν hν f₂ (by rw [hxy]; exact hf₂) FT'.w
    (fun j => by rw [hxy]; exact FT'.mul_w j) yb hyb
    (fun j => FT'.extends_rsop.mem_maximalIdeal (Finset.mem_image_of_mem _ (Finset.mem_univ j)))
    (hord₂.trans hν) i₀
  have hab : T.toRing (D.algR y) * yb i₀ = T.toRing a := by rw [hyb i₀, hi₀]
  -- `a = ∑ α_i g_i + δ y`
  rw [c.P_eq, Ideal.span_union] at haP
  obtain ⟨a₁, ha₁, a₂, ha₂, rfl⟩ := Submodule.mem_sup.mp haP
  obtain ⟨α, rfl⟩ := Ideal.mem_span_range_iff_exists_fun.mp ha₁
  obtain ⟨δ, rfl⟩ := Ideal.mem_span_singleton'.mp ha₂
  set g : Fin (D.F.r + 1 + t) → R := Fin.append (Fin.snoc D.F.z D.wR :
    Fin (D.F.r + 1) → R) (fun k => D.algR (c.xs k)) with hg
  set g₁ : Fin (D.F.r + 1 + t) → T.ring := Fin.append (Fin.snoc FT'.w
    (D.transform FT' FT0).wR : Fin (D.F.r + 1) → T.ring) (fun k => FT'.β (FT0.β (c.u' k)))
    with hg₁
  have hg₁M : ∀ i, g₁ i ∈ maximalIdeal T.ring := by
    intro i
    refine Fin.addCases (fun j => ?_) (fun l => ?_) i
    · simp only [hg₁, Fin.append_left]
      refine Fin.lastCases ?_ (fun j => ?_) j
      · rw [Fin.snoc_last]
        exact (D.transform FT' FT0).wR_mem
      · rw [Fin.snoc_castSucc]
        exact FT'.extends_rsop.mem_maximalIdeal (Finset.mem_image_of_mem _ (Finset.mem_univ j))
    · simp only [hg₁, Fin.append_right]
      exact c.coordV₁_yI l ▸ c.coordV₁_mem (c.yI l)
  have hTg : ∀ i, T.toRing (g i) = FT'.x * g₁ i := by
    intro i
    refine Fin.addCases (fun j => ?_) (fun l => ?_) i
    · simp only [hg, hg₁, Fin.append_left]
      exact ((D.compositeFrameTransform FT' FT0 y hx hx0).mul_w j).symm
    · simp only [hg, hg₁, Fin.append_right]
      exact c.mul_u l
  have hgM : ∀ i, g i ∈ maximalIdeal R ^ 1 := by
    intro i
    refine Fin.addCases (fun j => ?_) (fun l => ?_) i
    · simp only [hg, Fin.append_left]
      exact Ideal.mem_pow_of_ordElem (hzw1 j)
    · simp only [hg, Fin.append_right]
      exact c.algR_xs_mem l
  -- `δ ∈ M`
  have hδ : δ ∈ maximalIdeal R := by
    have h1 : FT'.x * yb i₀ = FT'.x * (∑ i, T.toRing (α i) * g₁ i + T.toRing δ) := by
      rw [← hxy, hab, map_add, map_sum, mul_add, Finset.mul_sum, map_mul T.toRing δ]
      congr 1
      · exact Finset.sum_congr rfl fun i _ => by rw [map_mul, hTg, hxy]; ring
      · ring
    have h2 := mul_left_cancel₀ hFTx0 h1
    have h3 : T.toRing δ ∈ maximalIdeal T.ring := by
      have : T.toRing δ = yb i₀ - ∑ i, T.toRing (α i) * g₁ i := by rw [h2]; ring
      rw [this]
      exact sub_mem h24 (Ideal.sum_mem _ fun i _ => Ideal.mul_mem_left _ _ (hg₁M i))
    by_contra hδM
    exact (IsLocalRing.mem_maximalIdeal _).mp h3
      ((IsLocalRing.notMem_maximalIdeal.mp hδM).map T.toRing)
  -- the class of `a` is that of `∑ α_i g_i`
  have ha₁M : ∑ i, α i * g i ∈ maximalIdeal R ^ 1 :=
    Ideal.sum_mem _ fun i _ => Ideal.mul_mem_left _ _ (hgM i)
  have hcls : AssocGraded.mk (maximalIdeal R) 1 (∑ i, α i * g i + δ * D.algR y) haM =
      AssocGraded.mk (maximalIdeal R) 1 (∑ i, α i * g i) ha₁M := by
    refine AssocGraded.mk_eq_mk_of_sub_mem_pow_succ _ 1 _ _ ?_
    rw [add_sub_cancel_left, pow_two]
    exact Ideal.mul_mem_mul hδ c.algR_y_mem
  rw [hcls, AssocGraded.mk_one_sum_mul (maximalIdeal R) Finset.univ α g hgM ha₁M]
  refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ ?_
  refine Fin.addCases (fun j => ?_) (fun l => ?_) i
  · refine Submodule.mem_sup_left (Submodule.subset_span ⟨j, ?_⟩)
    rw [AssocGraded.mk_congr _ (hgM _) (by simp only [hg, Fin.append_left] :
      g (Fin.castAdd t j) = (Fin.snoc D.F.z D.wR : Fin (D.F.r + 1) → R) j)]
    exact initialForm_eq_mk _ (hzw1 j)
  · refine Submodule.mem_sup_right (Submodule.subset_span ⟨l, ?_⟩)
    rw [AssocGraded.mk_congr _ (hgM _) (by simp only [hg, Fin.append_right] :
      g (Fin.natAdd (D.F.r + 1) l) = D.algR (c.xs l))]

omit [IsDomain R] in
/-- Every residue class of `R` is that of an element of `S₀` (`R/(z, w)R ≅ S₀`). -/
theorem exists_algR_eq (a : R ⧸ maximalIdeal R) :
    ∃ s₀ : D.F0.S, Ideal.Quotient.mk (maximalIdeal R) (D.algR s₀) = a := by
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective a
  obtain ⟨s₀, hs₀⟩ := D.quot_bijective_snoc.2 (Ideal.Quotient.mk _ r)
  refine ⟨s₀, Ideal.Quotient.eq.mpr ?_⟩
  have h : D.algR s₀ - r ∈ Ideal.span (Set.range (Fin.snoc D.F.z D.wR : Fin (D.F.r + 1) → R)) :=
    Ideal.Quotient.eq.mp hs₀
  refine (Ideal.span_le.mpr ?_) h
  rintro _ ⟨j, rfl⟩
  have := (linearIndependent_frameForm D.injective_snoc D.extendsToRSOP_snoc).2 j
  have h1 := Ideal.mem_pow_of_ordElem this
  rw [pow_one] at h1
  exact h1

omit [IsRegularLocalRing (R ⧸ P)] [IsLocalHom T.toRing] in
/-- The classes of `(z, w, y₁, …, y_b)` in `gr¹_M(R) = M/M²` are linearly independent (they are
part of the regular system of parameters `(z, w, y₁, …, y_b, y, x₁, …, x_a)` of `R`). -/
theorem linearIndependent_classes :
    LinearIndependent (R ⧸ maximalIdeal R)
      (Sum.elim (frameForm (Fin.snoc D.F.z D.wR : Fin (D.F.r + 1) → R))
        (fun l => AssocGraded.mk (maximalIdeal R) 1 (D.algR (c.xs l)) (c.algR_xs_mem l))) := by
  classical
  set v := coordV (F := D.compositeFrame) y c.xs c.ys with hv
  set G := gradedModel v c.span_R c.dim_R with hG
  have h1 : LinearIndependent (R ⧸ maximalIdeal R)
      (fun i => AssocGraded.mk (maximalIdeal R) 1 (v i) (mem_pow_one_of_span_eq c.span_R i)) := by
    have := (MvPolynomial.linearIndependent_X (R := R ⧸ maximalIdeal R) (σ := Fin c.n)).map'
      G.toLinearEquiv.toLinearMap G.toLinearEquiv.ker
    convert this using 1
    funext i
    simp [hG, gradedModel_X]
  let ι : Fin (D.F.r + 1) ⊕ Fin t → Fin c.n :=
    Sum.elim (fun j => Fin.castAdd (s + 1) (Fin.castAdd t j)) c.yI
  have hr : D.compositeFrame.r = D.F.r + 1 := rfl
  have hι : Function.Injective ι := by
    have e1 : ∀ a : Fin (D.F.r + 1), (ι (Sum.inl a)).val = a.val := fun a => rfl
    have e2 : ∀ b : Fin t, (ι (Sum.inr b)).val = D.F.r + 1 + b.val := fun b => rfl
    rintro (a | a) (b | b) h
    · have h' := congrArg Fin.val h
      rw [e1, e1] at h'
      exact congrArg Sum.inl (Fin.ext h')
    · have h' := congrArg Fin.val h
      rw [e1, e2] at h'
      have := a.2
      omega
    · have h' := congrArg Fin.val h
      rw [e1, e2] at h'
      have := b.2
      omega
    · exact congrArg Sum.inr (c.yI_injective h)
  have hzw1 := (linearIndependent_frameForm D.injective_snoc D.extendsToRSOP_snoc).2
  convert h1.comp ι hι using 1
  funext i
  rcases i with j | l
  · simp only [Sum.elim_inl, Function.comp_apply, ι]
    have hvj : v (Fin.castAdd (s + 1) (Fin.castAdd t j)) =
        (Fin.snoc D.F.z D.wR : Fin (D.F.r + 1) → R) j := by
      simp only [hv, coordV, Fin.append_left]
      exact Fin.append_left _ _ j
    rw [AssocGraded.mk_congr _ _ hvj]
    exact initialForm_eq_mk _ (hzw1 j)
  · simp only [Sum.elim_inr, Function.comp_apply, ι]
    rw [AssocGraded.mk_congr _ _ (c.coordV_yI l)]

omit [IsLocalHom T.toRing] in
/-- **"Therefore, we may assume that `(w, y₁, ⋯, y_τ)` is a regular system of
`τ_{(z)}`-parameters of `R` for `f` (`τ ≤ i − 1`)"** (pp. 271--272), with
`τ = τ_{(z,w)}(f) = τ_{(z)}(f) − 1`: there is an invertible matrix `C` over `S₀` such that after the
change of coordinates `y_j ↦ ∑_l C_{jl} y_l` (`AdaptedCoords.recoord`, `v = 0`) the classes of
`z₁, …, z_r, w, y₁, …, y_τ` span `T*` of `f` (for `(z)`).

Gap filled.  By Lemma 24 (`tauStar_le_sup`), `T*` lies in the span of `Z, W, Y₁, …, Y_b`; it
contains `Z, W` (condition (3)) and has dimension `r + 1 + τ`; so its intersection with
`⟨Y₁, …, Y_b⟩` modulo `⟨Z, W⟩` gives `τ` independent combinations of `Y₁, …, Y_b` ("`τ` independent
linear combinations of `y₁, ⋯, y_{i−1}`"), which are completed to a basis of `⟨Y₁, …, Y_b⟩`
(`exists_isUnit_matrix_span_eq`); the coefficients are lifted to `S₀` (`exists_algR_eq`), and the
lifted matrix is invertible (its determinant is a unit modulo `M`). -/
theorem exists_tauNormalized [Hironaka.HironakaCitedResults.{u}] [CharZero (ResidueField R)] {f : R} (hTau : D.InTauStar f)
    (hz : D.F.idealZ ≤ P) (hP : Ideal.ordElem P f = Ideal.ordElem (maximalIdeal R) f) {ν : ℕ}
    (hν : (ν : ℕ∞) = Ideal.ordElem (maximalIdeal R) f) {f₂ : T.ring}
    (hf₂ : FT'.x ^ ν * f₂ = T.toRing f) (hord₂ : Ideal.ordElem (maximalIdeal T.ring) f₂ = ν) :
    ∃ (C : Matrix (Fin t) (Fin t) D.F0.S) (hC : IsUnit C)
      (hτt : tauZ R (Fin.snoc D.F.z D.wR : Fin (D.F.r + 1) → R) (fun _ : Fin 1 => f) ≤ t),
      Submodule.span (R ⧸ maximalIdeal R)
          (Set.range (frameForm (Fin.snoc D.F.z D.wR : Fin (D.F.r + 1) → R)) ∪
            Set.range (fun j => AssocGraded.mk (maximalIdeal R) 1
              (D.algR ((c.recoord C hC 0 (fun _ => zero_mem _)).xs (Fin.castLE hτt j)))
              ((c.recoord C hC 0 (fun _ => zero_mem _)).algR_xs_mem (Fin.castLE hτt j)))) =
        tauZSubmoduleStar R D.F.z (fun _ : Fin 1 => f) := by
  classical
  set τ := tauZ R (Fin.snoc D.F.z D.wR : Fin (D.F.r + 1) → R) (fun _ : Fin 1 => f) with hτdef
  set Ts := tauZSubmoduleStar R D.F.z (fun _ : Fin 1 => f) with hTs
  have hW : initialForm (maximalIdeal R) D.wR ∈ Ts := hTau
  have hsnoc : tauZSubmoduleStar R (Fin.snoc D.F.z D.wR : Fin (D.F.r + 1) → R)
      (fun _ : Fin 1 => f) = Ts := tauZSubmoduleStar_snoc_eq_of_mem D.F.z _ D.wR hW
  have hZT : Submodule.span (R ⧸ maximalIdeal R)
      (Set.range (frameForm (Fin.snoc D.F.z D.wR : Fin (D.F.r + 1) → R))) ≤ Ts := by
    rw [← hsnoc]
    exact le_sup_right
  have hfin : FiniteDimensional (R ⧸ maximalIdeal R) Ts :=
    finite_tauZSubmoduleStar (linearIndependent_frameForm D.F.z_injective D.F.extends_rsop).2 _
  have hrank : Module.finrank (R ⧸ maximalIdeal R) Ts = (D.F.r + 1) + τ := by
    rw [← hsnoc, finrank_tauZSubmoduleStar_eq D.injective_snoc D.extendsToRSOP_snoc, add_comm]
  obtain ⟨hτt, Cb, hCb, hspan⟩ := exists_isUnit_matrix_span_eq _ _ c.linearIndependent_classes Ts
    hZT (c.tauStar_le_sup hz hP hν hf₂ hord₂) hrank
  choose lift hlift using fun a : R ⧸ maximalIdeal R => exists_algR_eq (D := D) a
  set C : Matrix (Fin t) (Fin t) D.F0.S := Matrix.of fun i j => lift (Cb i j) with hCdef
  have hCmap : RingHom.mapMatrix ((Ideal.Quotient.mk (maximalIdeal R)).comp D.algR) C = Cb := by
    ext i j
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, hCdef, Matrix.of_apply,
      RingHom.comp_apply]
    exact hlift _
  have hC : IsUnit C := by
    rw [Matrix.isUnit_iff_isUnit_det]
    have h1 : Ideal.Quotient.mk (maximalIdeal R) (D.algR C.det) = Cb.det := by
      rw [← RingHom.comp_apply, RingHom.map_det, hCmap]
    have h2 : Cb.det ≠ 0 := ((Matrix.isUnit_iff_isUnit_det Cb).mp hCb).ne_zero
    have h3 : D.algR C.det ∉ maximalIdeal R := by
      intro hm
      apply h2
      rw [← h1]
      exact Ideal.Quotient.eq_zero_iff_mem.mpr hm
    have h4 : IsUnit (D.algR C.det) := IsLocalRing.notMem_maximalIdeal.mp h3
    have : IsLocalHom D.algR :=
      (inferInstance : IsLocalHom ((algebraMap D.F.S R).comp (algebraMap D.F0.S D.F.S)))
    exact isUnit_of_map_unit D.algR _ h4
  refine ⟨C, hC, hτt, ?_⟩
  rw [← hspan]
  congr 2
  refine congrArg Set.range (funext fun j => ?_)
  have hxs : D.algR ((c.recoord C hC 0 (fun _ => zero_mem _)).xs (Fin.castLE hτt j)) =
      ∑ l, D.algR (C (Fin.castLE hτt j) l) * D.algR (c.xs l) := by
    show D.algR (c.newXs C 0 (Fin.castLE hτt j)) = _
    simp only [newXs, Pi.add_apply, Matrix.mulVec, dotProduct, Pi.zero_apply, zero_mul, add_zero,
      map_sum, map_mul]
  rw [AssocGraded.mk_congr _ _ hxs, AssocGraded.mk_one_sum_mul (maximalIdeal R) Finset.univ _ _
    c.algR_xs_mem]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [hCdef, Matrix.of_apply, hlift]

section ModelsX

attribute [local instance] Ideal.Quotient.field

/-- The index of the `j`-th member of `(z₁, …, z_r, w)`. -/
noncomputable abbrev zwI (_c : D.AdaptedCoords FT' FT0 y hx hx0 t s) (j : Fin (D.F.r + 1)) :
    Fin ((D.compositeFrame.r + t) + (s + 1)) := Fin.castAdd (s + 1) (Fin.castAdd t j)

omit [IsRegularLocalRing (R ⧸ P)] [IsLocalHom T.toRing] in
theorem zwI_castSucc (j : Fin D.F.r) : c.zwI (Fin.castSucc j) = c.zI j := rfl

omit [IsRegularLocalRing (R ⧸ P)] [IsLocalHom T.toRing] in
theorem zwI_last : c.zwI (Fin.last D.F.r) = c.wI := rfl

omit [IsRegularLocalRing (R ⧸ P)] [IsLocalHom T.toRing] in
theorem range_zwI : Set.range c.zwI = Set.range c.zI ∪ {c.wI} := by
  ext i
  constructor
  · rintro ⟨j, rfl⟩
    refine Fin.lastCases ?_ (fun j => ?_) j
    · exact Or.inr rfl
    · exact Or.inl ⟨j, rfl⟩
  · rintro (⟨j, rfl⟩ | h)
    · exact ⟨Fin.castSucc j, rfl⟩
    · rw [Set.mem_singleton_iff] at h
      exact ⟨Fin.last D.F.r, h.symm⟩

omit [IsRegularLocalRing (R ⧸ P)] [IsLocalHom T.toRing] in
theorem modelR_X_zwI (ρ : T.ring ⧸ maximalIdeal T.ring ≃+* R ⧸ maximalIdeal R)
    (j : Fin (D.F.r + 1)) :
    (c.modelR ρ).Φ (X (c.zwI j)) = frameForm (Fin.snoc D.F.z D.wR : Fin (D.F.r + 1) → R) j := by
  rw [D.frameForm_snoc_wR]
  refine Fin.lastCases ?_ (fun j => ?_) j
  · rw [Fin.snoc_last, zwI_last]
    exact (c.isAdaptedModel ρ).Φ_X_wI
  · rw [Fin.snoc_castSucc, zwI_castSucc]
    exact (c.isAdaptedModel ρ).Φ_X_zI j

omit [IsRegularLocalRing (R ⧸ P)] [IsLocalHom T.toRing] in
theorem modelT_X_zwI (j : Fin (D.F.r + 1)) :
    c.modelT.Φ (X (c.zwI j)) =
      frameForm (Fin.snoc FT'.w (D.transform FT' FT0).wR : Fin (D.F.r + 1) → T.ring) j := by
  have h := (D.transform FT' FT0).frameForm_snoc_wR
  change frameForm (Fin.snoc FT'.w (D.transform FT' FT0).wR : Fin (D.F.r + 1) → T.ring) =
    Fin.snoc (frameForm FT'.w) (initialForm (maximalIdeal T.ring) (D.transform FT' FT0).wR) at h
  rw [h]
  refine Fin.lastCases ?_ (fun j => ?_) j
  · rw [Fin.snoc_last, zwI_last]
    exact c.isAdaptedModel_transform.Φ_X_wI
  · rw [Fin.snoc_castSucc, zwI_castSucc]
    exact c.isAdaptedModel_transform.Φ_X_zI j

omit [IsRegularLocalRing (R ⧸ P)] [IsLocalHom T.toRing] in
theorem modelR_X_yI (ρ : T.ring ⧸ maximalIdeal T.ring ≃+* R ⧸ maximalIdeal R) (k : Fin t) :
    (c.modelR ρ).Φ (X (c.yI k)) =
      AssocGraded.mk (maximalIdeal R) 1 (D.algR (c.xs k)) (c.algR_xs_mem k) :=
  (gradedSemiModel_X _ _ c.span_R c.dim_R (c.yI k)).trans
    (AssocGraded.mk_congr _ _ (c.coordV_yI k))

omit [IsRegularLocalRing (R ⧸ P)] [IsLocalHom T.toRing] in
theorem uβ_mem (k : Fin t) : FT'.β (FT0.β (c.u' k)) ∈ maximalIdeal T.ring ^ 1 :=
  (c.coordV₁_yI k) ▸ mem_pow_one_of_span_eq c.span_R₁ (c.yI k)

omit [IsRegularLocalRing (R ⧸ P)] [IsLocalHom T.toRing] in
theorem modelT_X_yI (k : Fin t) :
    c.modelT.Φ (X (c.yI k)) =
      AssocGraded.mk (maximalIdeal T.ring) 1 (FT'.β (FT0.β (c.u' k))) (c.uβ_mem k) :=
  (gradedSemiModel_X _ _ c.span_R₁ c.dim_R₁ (c.yI k)).trans
    (AssocGraded.mk_congr _ _ (c.coordV₁_yI k))

omit [IsRegularLocalRing (R ⧸ P)] [IsLocalHom T.toRing] in
/-- In the picture of `gr_M(R)`: `(w, y₁, ⋯, y_τ)` is a regular system of `τ_{(z)}`-parameters of
`R` for `f` iff the pull-back of `T*` is the span of the variables `Z, W, Y₁, …, Y_τ`. -/
theorem modelR_pull_eq (ρ : T.ring ⧸ maximalIdeal T.ring ≃+* R ⧸ maximalIdeal R) {τ : ℕ}
    (hτt : τ ≤ t) (Ts : Submodule (R ⧸ maximalIdeal R) (AssocGraded (maximalIdeal R)))
    (h : Submodule.span (R ⧸ maximalIdeal R)
      (Set.range (frameForm (Fin.snoc D.F.z D.wR : Fin (D.F.r + 1) → R)) ∪
        Set.range (fun j => AssocGraded.mk (maximalIdeal R) 1 (D.algR (c.xs (Fin.castLE hτt j)))
          (c.algR_xs_mem (Fin.castLE hτt j)))) = Ts) :
    (c.modelR ρ).pull Ts = Submodule.span (T.ring ⧸ maximalIdeal T.ring)
      (X '' (Set.range c.zwI ∪ Set.range (fun j : Fin τ => c.yI (Fin.castLE hτt j)))) := by
  rw [← h, ← range_fin_append, ← range_fin_append]
  refine (c.modelR ρ).pull_span_range _ _ fun l => ?_
  refine Fin.addCases (fun j => ?_) (fun j => ?_) l
  · simp only [Fin.append_left]
    exact c.modelR_X_zwI ρ j
  · simp only [Fin.append_right]
    exact c.modelR_X_yI ρ _

omit [IsRegularLocalRing (R ⧸ P)] [IsLocalHom T.toRing] in
/-- In the picture of `gr_{M₁}(R₁)`: if the pull-back of `T*` of `f̄` (for `(z̄)`) is the span of
the variables `Z̄, W̄, Ȳ₁, …, Ȳ_τ`, then `(w̄, ȳ₁, ⋯, ȳ_τ)` is a regular system of
`τ_{(z̄)}`-parameters of `R₁` for `f̄` (the classes of `z̄, w̄, ȳ₁, …, ȳ_τ` span `T*`). -/
theorem span_eq_of_modelT_pull_eq {τ : ℕ} (hτt : τ ≤ t)
    (Ts : Submodule (T.ring ⧸ maximalIdeal T.ring) (AssocGraded (maximalIdeal T.ring)))
    (h : c.modelT.pull Ts = Submodule.span (T.ring ⧸ maximalIdeal T.ring)
      (X '' (Set.range c.zwI ∪ Set.range (fun j : Fin τ => c.yI (Fin.castLE hτt j))))) :
    Submodule.span (T.ring ⧸ maximalIdeal T.ring)
      (Set.range (frameForm (Fin.snoc FT'.w (D.transform FT' FT0).wR : Fin (D.F.r + 1) → T.ring)) ∪
        Set.range (fun j => AssocGraded.mk (maximalIdeal T.ring) 1
          (FT'.β (FT0.β (c.u' (Fin.castLE hτt j)))) (c.uβ_mem (Fin.castLE hτt j)))) = Ts := by
  refine c.modelT.pull_injective ?_
  rw [h, ← range_fin_append, ← range_fin_append]
  refine c.modelT.pull_span_range _ _ fun l => ?_
  refine Fin.addCases (fun j => ?_) (fun j => ?_) l
  · simp only [Fin.append_left]
    exact c.modelT_X_zwI j
  · simp only [Fin.append_right]
    exact c.modelT_X_yI _

end ModelsX

section Shift

open scoped Classical

omit [P.IsPrime] [IsRegularLocalRing (R ⧸ P)] [IsRegularLocalRing T.ring] in
/-- The image in `R₁` of an element of the maximal ideal of `S₀` lies in `M₁`. -/
theorem toRing_algR_mem {a : D.F0.S} (ha : a ∈ maximalIdeal D.F0.S) :
    T.toRing (D.algR a) ∈ maximalIdeal T.ring := by
  have : IsLocalHom D.algR :=
    (inferInstance : IsLocalHom ((algebraMap D.F.S R).comp (algebraMap D.F0.S D.F.S)))
  by_contra h
  have h1 := isUnit_of_map_unit D.algR _
    (isUnit_of_map_unit T.toRing _ (IsLocalRing.notMem_maximalIdeal.mp h))
  exact (IsLocalRing.mem_maximalIdeal _).mp ha h1

omit [IsRegularLocalRing (R ⧸ P)] [IsLocalHom T.toRing] in
theorem sF_mem (i : Fin c.n) : c.sF i ∈ maximalIdeal D.F0.S := by
  rw [← c.span_S]
  rcases fin_split_three i with ⟨j, rfl⟩ | ⟨k, rfl⟩ | rfl | ⟨l, rfl⟩
  · simp only [sF, Fin.append_left]
    exact zero_mem _
  · simp only [sF, Fin.append_left, Fin.append_right]
    exact Ideal.subset_span (Or.inl (Or.inr ⟨k, rfl⟩))
  · simp only [sF, Fin.append_right, Fin.cons_zero]
    exact Ideal.subset_span (Or.inl (Or.inl rfl))
  · simp only [sF, Fin.append_right, Fin.cons_succ]
    exact Ideal.subset_span (Or.inr ⟨l, rfl⟩)

omit [IsRegularLocalRing (R ⧸ P)] [IsLocalHom T.toRing] in
theorem sF_mem_span_of_notMem_U (i : Fin c.n) (hi : i ∉ c.U) :
    c.sF i ∈ Ideal.span ({y} ∪ Set.range c.ys) := by
  have hr : D.compositeFrame.r = D.F.r + 1 := rfl
  have hi' : D.F.r + 1 + t ≤ i.val := by
    have : ¬ i.val < D.F.r + 1 + t := hi
    omega
  rcases fin_split_three i with ⟨j, rfl⟩ | ⟨k, rfl⟩ | rfl | ⟨l, rfl⟩
  · have := j.2
    simp at hi'
    omega
  · have := k.2
    simp at hi'
    omega
  · simp only [sF, Fin.append_right, Fin.cons_zero]
    exact Ideal.subset_span (Or.inl rfl)
  · simp only [sF, Fin.append_right, Fin.cons_succ]
    exact Ideal.subset_span (Or.inr ⟨l, rfl⟩)

section RecoordCoords

variable (C : Matrix (Fin t) (Fin t) D.F0.S) (hC : IsUnit C) (v : Fin t → D.F0.S)
  (hv : ∀ k, v k ∈ Ideal.span ({y} ∪ Set.range c.ys))

omit [IsRegularLocalRing (R ⧸ P)] [IsLocalHom T.toRing] in
theorem recoord_coordV_yI (k : Fin t) :
    coordV (F := D.compositeFrame) y (c.recoord C hC v hv).xs (c.recoord C hC v hv).ys (c.yI k) =
      D.algR (c.newXs C v k) :=
  (c.recoord C hC v hv).coordV_yI k

omit [IsRegularLocalRing (R ⧸ P)] [IsLocalHom T.toRing] in
theorem recoord_coordV_of_notMem (i : Fin c.n) (hi : i ∉ Set.range c.yI) :
    coordV (F := D.compositeFrame) y (c.recoord C hC v hv).xs (c.recoord C hC v hv).ys i =
      coordV (F := D.compositeFrame) y c.xs c.ys i := by
  show coordV (F := D.compositeFrame) y (c.newXs C v) c.ys i = _
  rcases fin_split_three i with ⟨j, rfl⟩ | ⟨k, rfl⟩ | rfl | ⟨l, rfl⟩
  · simp only [coordV, Fin.append_left]
  · exact absurd ⟨k, rfl⟩ hi
  · simp only [coordV, Fin.append_right, Fin.cons_zero]
  · simp only [coordV, Fin.append_right, Fin.cons_succ]

omit [IsRegularLocalRing (R ⧸ P)] [IsLocalHom T.toRing] in
theorem recoord_coordV₁_yI (k : Fin t) :
    coordV₁ (D.compositeFrameTransform FT' FT0 y hx hx0) (c.recoord C hC v hv).ys
      (fun k => (FT'.β.comp FT0.β) ((c.recoord C hC v hv).u' k)) (c.yI k) =
      FT'.β (FT0.β (c.newU C v k)) :=
  (c.recoord C hC v hv).coordV₁_yI k

omit [IsRegularLocalRing (R ⧸ P)] [IsLocalHom T.toRing] in
theorem recoord_coordV₁_of_notMem (i : Fin c.n) (hi : i ∉ Set.range c.yI) :
    coordV₁ (D.compositeFrameTransform FT' FT0 y hx hx0) (c.recoord C hC v hv).ys
      (fun k => (FT'.β.comp FT0.β) ((c.recoord C hC v hv).u' k)) i =
      coordV₁ (D.compositeFrameTransform FT' FT0 y hx hx0) c.ys
        (fun k => (FT'.β.comp FT0.β) (c.u' k)) i := by
  show coordV₁ (D.compositeFrameTransform FT' FT0 y hx hx0) c.ys
    (fun k => (FT'.β.comp FT0.β) (c.newU C v k)) i = _
  rcases fin_split_three i with ⟨j, rfl⟩ | ⟨k, rfl⟩ | rfl | ⟨l, rfl⟩
  · simp only [coordV₁, Fin.append_left]
  · exact absurd ⟨k, rfl⟩ hi
  · simp only [coordV₁, Fin.append_right, Fin.cons_zero]
  · simp only [coordV₁, Fin.append_right, Fin.cons_succ]

end RecoordCoords

omit [IsRegularLocalRing (R ⧸ P)] in
/-- **"We can find linear combinations `v` of `y, x₁, ⋯, x_a` with coefficients in `S₀` such that
`L` is the initial form of `v` in `gr_M(R)` (hence, in `gr_{M₁}(R₁)`)"** (p. 272): for a linear
form `L` in the variables `Y, X₁, …, X_a` (outside `U`) and lifts to `S₀` of its coefficients, the
class of `v = ∑ c_i s_i` in `gr¹_{M₁}(R₁)` is the image of `L` under the model of `gr_{M₁}(R₁)`.
(`lift` is a section of `S₀ → R₁/M₁`, which exists since `R₁` is residually rational over `R`.) -/
theorem modelT_eq_mk_of_mem_linSpan (lift : (T.ring ⧸ maximalIdeal T.ring) → D.F0.S)
    (hlift : ∀ a, Ideal.Quotient.mk (maximalIdeal T.ring) (T.toRing (D.algR (lift a))) = a)
    {L : MvPolynomial (Fin c.n) (T.ring ⧸ maximalIdeal T.ring)}
    (hL : L ∈ linSpan (k := T.ring ⧸ maximalIdeal T.ring) {v | v ∉ c.U})
    (hmem : T.toRing (D.algR (∑ i, (if i ∈ {v | v ∉ c.U} then lift (L.coeff (Finsupp.single i 1))
      else 0) * c.sF i)) ∈ maximalIdeal T.ring ^ 1) :
    AssocGraded.mk (maximalIdeal T.ring) 1 (T.toRing (D.algR (∑ i, (if i ∈ {v | v ∉ c.U} then
      lift (L.coeff (Finsupp.single i 1)) else 0) * c.sF i))) hmem = c.modelT.Φ L := by
  have hq : ∀ i, T.toRing (D.algR (c.sF i)) ∈ maximalIdeal T.ring ^ 1 := fun i => by
    rw [pow_one]; exact toRing_algR_mem (c.sF_mem i)
  have hsum : T.toRing (D.algR (∑ i, (if i ∈ {v | v ∉ c.U} then
      lift (L.coeff (Finsupp.single i 1)) else 0) * c.sF i)) =
      ∑ i, T.toRing (D.algR (if i ∈ {v | v ∉ c.U} then lift (L.coeff (Finsupp.single i 1))
        else 0)) * T.toRing (D.algR (c.sF i)) := by
    simp only [map_sum, map_mul]
  rw [AssocGraded.mk_congr _ hmem hsum, AssocGraded.mk_one_sum_mul _ Finset.univ _ _ hq]
  conv_rhs => rw [eq_sum_coeff_smul_X_of_mem_linSpan _ hL]
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [SemiModel.map_smul']
  by_cases hi : i ∈ {v | v ∉ c.U}
  · rw [ite_eq_left hi, ite_eq_left hi, hlift]
    show _ = (RingEquiv.refl _) _ • _
    rw [RingEquiv.refl_apply]
    congr 1
    show _ = (gradedSemiModel _ _ c.span_R₁ c.dim_R₁).Φ (X i)
    rw [gradedSemiModel_X]
    refine AssocGraded.mk_congr _ _ ?_
    have hle : D.F.r + 1 ≤ i.val := by
      have hr : D.compositeFrame.r = D.F.r + 1 := rfl
      have : ¬ i.val < D.F.r + 1 + t := hi
      omega
    rw [c.coordV₁_eq_toRing_coordV i hi, c.coordV_other i hle]
  · rw [ite_eq_right hi, ite_eq_right hi]
    simp only [map_zero, zero_smul]

omit [IsRegularLocalRing (R ⧸ P)] in
/-- **"We may replace `y_j` by `y_j + v_j y` for `1 ≤ j ≤ τ` without affecting any of the
assumptions on `(y₁, ⋯, y_b)` in the above argument, so that we may assume that
`L₁ = ⋯ = L_τ = 0`"** (p. 272).  Given linear forms `ℓ` in `Y, X₁, …, X_a` (the `L_j` are the
`ℓ (yI j)`, `j < τ`; for `j ≥ τ` the form `L_j` is taken to be `0`), there are
`v_j ∈ (y, x₁, …, x_a)S₀` with initial form `L_j` in `gr_{M₁}(R₁)` such that for the new
coordinates `y_j + v_j y` (`AdaptedCoords.recoord` with `C = 1`): the model of `gr_M(R)` is
unchanged (the initial form of `y_j + v_j y` is `Y_j`), and the model of
`gr_{M₁}(R₁)` is the old one composed with `Ȳ_j ↦ Ȳ_j + L_j` (`j < τ`), the initial form of
`(y_j + v_j y)/y = ȳ_j + v_j` being `Ȳ_j + L_j`. -/
theorem exists_shift (ρ : T.ring ⧸ maximalIdeal T.ring ≃+* R ⧸ maximalIdeal R)
    (hρ : (ρ.symm : R ⧸ maximalIdeal R →+* T.ring ⧸ maximalIdeal T.ring) =
      quotientMaximalIdealMap T.toRing)
    {τ : ℕ} (hτt : τ ≤ t)
    (ℓ : Fin c.n → MvPolynomial (Fin c.n) (T.ring ⧸ maximalIdeal T.ring))
    (hℓB : ∀ v, ℓ v ∈ linSpan (k := T.ring ⧸ maximalIdeal T.ring) {v | v ∉ c.U}) :
    ∃ (v : Fin t → D.F0.S) (hv : ∀ k, v k ∈ Ideal.span ({y} ∪ Set.range c.ys)),
      ((c.recoord 1 isUnit_one v hv).modelR ρ).Φ = (c.modelR ρ).Φ ∧
      ∀ p, (c.recoord 1 isUnit_one v hv).modelT.Φ p = c.modelT.Φ (aeval (fun i => X i +
        if i ∈ Set.range (fun j : Fin τ => c.yI (Fin.castLE hτt j)) then ℓ i else 0) p) := by
  -- a section of `S₀ → R₁/M₁`
  have hlift : ∀ a : T.ring ⧸ maximalIdeal T.ring, ∃ s₀ : D.F0.S,
      Ideal.Quotient.mk (maximalIdeal T.ring) (T.toRing (D.algR s₀)) = a := by
    intro a
    obtain ⟨s₀, hs₀⟩ := exists_algR_eq (D := D) (ρ a)
    refine ⟨s₀, ?_⟩
    rw [← quotientMaximalIdealMap_mk, hs₀, ← hρ]
    exact ρ.symm_apply_apply a
  choose lift hlift using hlift
  set ℓ₂ : Fin c.n → MvPolynomial (Fin c.n) (T.ring ⧸ maximalIdeal T.ring) := fun i =>
    if i ∈ Set.range (fun j : Fin τ => c.yI (Fin.castLE hτt j)) then ℓ i else 0 with hℓ₂
  have hℓ₂B : ∀ i, ℓ₂ i ∈ linSpan (k := T.ring ⧸ maximalIdeal T.ring) {v | v ∉ c.U} := by
    intro i
    simp only [hℓ₂]
    split_ifs
    · exact hℓB i
    · exact zero_mem _
  set v : Fin t → D.F0.S := fun k => ∑ i, (if i ∈ {v | v ∉ c.U} then
    lift ((ℓ₂ (c.yI k)).coeff (Finsupp.single i 1)) else 0) * c.sF i with hvdef
  have hv : ∀ k, v k ∈ Ideal.span ({y} ∪ Set.range c.ys) := by
    intro k
    refine Ideal.sum_mem _ fun i _ => ?_
    by_cases hi : i ∈ {v | v ∉ c.U}
    · rw [ite_eq_left hi]
      exact Ideal.mul_mem_left _ _ (c.sF_mem_span_of_notMem_U i hi)
    · rw [ite_eq_right hi, zero_mul]
      exact zero_mem _
  have hvM : ∀ k, v k ∈ maximalIdeal D.F0.S := fun k => by
    rw [← c.span_S]
    exact Ideal.span_mono (by
      rintro _ (rfl | h)
      · exact Or.inl (Or.inl rfl)
      · exact Or.inr h) (hv k)
  refine ⟨v, hv, ?_, ?_⟩
  · -- the model of `gr_M(R)` is unchanged
    refine RingEquiv.ext fun p => ?_
    refine (gradedSemiModel_apply_eq_aeval ρ _ _ c.span_R c.dim_R _ _ X (fun i => ?_) p).trans ?_
    · rw [gradedSemiModel_X]
      by_cases hi : i ∈ Set.range c.yI
      · obtain ⟨k, rfl⟩ := hi
        refine AssocGraded.mk_eq_mk_of_sub_mem_pow_succ _ 1 _ _ ?_
        rw [c.recoord_coordV_yI 1 isUnit_one v hv k, c.coordV_yI k]
        simp only [newXs, Pi.add_apply, Matrix.one_mulVec, map_add, map_mul, add_sub_cancel_left]
        have h1 : D.algR (v k) ∈ maximalIdeal R := by
          have : IsLocalHom D.algR :=
            (inferInstance : IsLocalHom ((algebraMap D.F.S R).comp (algebraMap D.F0.S D.F.S)))
          by_contra h
          exact (IsLocalRing.mem_maximalIdeal _).mp (hvM k)
            (isUnit_of_map_unit D.algR _ (IsLocalRing.notMem_maximalIdeal.mp h))
        show _ ∈ maximalIdeal R ^ 2
        rw [pow_two]
        exact Ideal.mul_mem_mul h1 c.algR_y_mem
      · exact AssocGraded.mk_congr _ _ (c.recoord_coordV_of_notMem 1 isUnit_one v hv i hi)
    · exact congrArg _ (aeval_X_left_apply p)
  · -- the model of `gr_{M₁}(R₁)` is composed with `Ȳ_j ↦ Ȳ_j + L_j`
    intro p
    refine gradedSemiModel_apply_eq_aeval (RingEquiv.refl _) _ _ c.span_R₁ c.dim_R₁ _ _ _
      (fun i => ?_) p
    rw [map_add]
    by_cases hi : i ∈ Set.range c.yI
    · obtain ⟨k, rfl⟩ := hi
      have hmem := toRing_algR_mem (T := T) (hvM k)
      have hmem' : T.toRing (D.algR (v k)) ∈ maximalIdeal T.ring ^ 1 := by rwa [pow_one]
      have h1 := c.modelT_eq_mk_of_mem_linSpan lift hlift (hℓ₂B (c.yI k)) hmem'
      have hA : FT'.β (FT0.β (c.u' k)) ∈ maximalIdeal T.ring ^ 1 :=
        (c.coordV₁_yI k) ▸ mem_pow_one_of_span_eq c.span_R₁ (c.yI k)
      have heq := (c.recoord_coordV₁_yI 1 isUnit_one v hv k).trans
        (show FT'.β (FT0.β (c.newU 1 v k)) = FT'.β (FT0.β (c.u' k)) + T.toRing (D.algR (v k)) by
          simp only [newU, Pi.add_apply, Matrix.map_one _ (map_zero _) (map_one _),
            Matrix.one_mulVec, map_add, β_toRing]
          rfl)
      have hX : c.modelT.Φ (X (c.yI k)) =
          AssocGraded.mk (maximalIdeal T.ring) 1 (FT'.β (FT0.β (c.u' k))) hA :=
        (gradedSemiModel_X _ _ c.span_R₁ c.dim_R₁ (c.yI k)).trans
          (AssocGraded.mk_congr _ _ (c.coordV₁_yI k))
      exact ((AssocGraded.mk_congr _ _ heq).trans (AssocGraded.mk_add _ 1 _ _ hA hmem')).trans
        (congrArg₂ (· + ·) hX.symm h1)
    · have h0 : ℓ₂ i = 0 := by
        simp only [hℓ₂]
        refine ite_eq_right ?_
        rintro ⟨j, rfl⟩
        exact hi ⟨_, rfl⟩
      show _ = _ + c.modelT.Φ (ℓ₂ i)
      rw [h0, map_zero, add_zero]
      show _ = (gradedSemiModel _ _ c.span_R₁ c.dim_R₁).Φ (X i)
      rw [gradedSemiModel_X]
      exact AssocGraded.mk_congr _ _ (c.recoord_coordV₁_of_notMem 1 isUnit_one v hv i hi)

end Shift

end WeierstrassDatum.AdaptedCoords

end Lemma24

end Hironaka
