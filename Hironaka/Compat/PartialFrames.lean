/-
Copyright (c) 2026 Daattavya Aggarwal, Minhyong Kim, Oisin Kim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daattavya Aggarwal, Minhyong Kim, Oisin Kim
-/
module

public import Hironaka.Ch3.FrameTransforms
public import Hironaka.Ch3.JStability

/-!
# Compatibility layer: the partial frames `(S{z_{p+1}, …, z_r}; z₁, …, z_p)` of `S{z₁, …, z_r}`
(Ch. III pp. 253, 264)

The proofs of Theorem 7 (p. 253) and Theorem 8 (p. 264) use, for a complete `R = S{z₁, …, z_τ}`,
the partial frames

> Let `S^{(a)} = S{z_{τ_a+1}, …, z_τ}`. Let `(S^{(a)}₁; w₁, …, w_{τ_a})` be the frame transform of
> `(S^{(a)}; z₁, …, z_{τ_a})` in `R₁` with the denominator `x`. (Theorem 8, p. 264)
>
> By the completeness of `R`, if `S_a = S{z_{τ_a+1}, …, z_τ}`, then `(S_a; z₁, …, z_{τ_a})` is a
> regular frame of `R`. (Theorem 7, p. 253)

This file constructs them for `R = S⟦z₁, …, z_r⟧` (the `R̃ = S{z}` of the reductions of §8,
`RegularFrame.mvPowerSeries`):
* `sumSplitEquiv`: `S⟦X, Y⟧ ≅ S⟦Y⟧⟦X⟧` for variables indexed by `σ ⊕ τ`, and
  `finSplitEquiv`, its version `S⟦z₁, …, z_r⟧ ≅ S{z_{p+1}, …, z_r}⟦z₁, …, z_p⟧`;
* `RegularFrame.partialFrame`: the regular frame `(S{z_{p+1}, …, z_r}; z₁, …, z_p)` of `S⟦z⟧`, with
  its members (`RegularFrame.partialFrame_z`), the image of `S` in its coefficient ring and its
  expansion coefficients (`RegularFrame.partialFrame_expCoeff`);
* Remarks 1 and 2 of §7 for it (`RegularFrame.isNormalizedBy_partialFrame`): if the initial forms of
  `f₁, …, f_i` lie in `k[Z₁, …, Z_p]` and `g` is normalized by `(f₁, …, f_i)` with respect to
  `(S; z₁, …, z_r)`, then `g` is normalized by `(f₁, …, f_i)` with respect to
  `(S{z_{p+1}, …, z_r}; z₁, …, z_p)` (Theorem 7, p. 253: "in view of Remarks 1 and 2,
  `f_{m_a+j}` is normalized by `(f₁, …, f_{m_a})` with respect to `(S_a; z₁, …, z_{τ_a})`");
* the frame transform of the partial frame with a given denominator
  (`RegularFrame.exists_partialFrame_frameTransform`).
-/

@[expose] public section

open IsLocalRing

namespace Hironaka

universe u

/-! ### `S⟦X, Y⟧ ≅ S⟦Y⟧⟦X⟧` -/

section SumSplit

open MvPowerSeries Finsupp

variable {σ τ : Type*} {S : Type*} [CommRing S]

/-- The coefficients of `f ∈ S⟦X, Y⟧` (variables indexed by `σ ⊕ τ`), arranged as a power series
in `X` with coefficients in `S⟦Y⟧`. -/
noncomputable def sumSplitFun (f : MvPowerSeries (σ ⊕ τ) S) :
    MvPowerSeries σ (MvPowerSeries τ S) :=
  fun x => fun y => coeff (x.sumElim y) f

/-- The inverse of `sumSplitFun`. -/
noncomputable def sumJoinFun (g : MvPowerSeries σ (MvPowerSeries τ S)) :
    MvPowerSeries (σ ⊕ τ) S :=
  fun z => coeff (z.comapDomain Sum.inr Sum.inr_injective.injOn)
    (coeff (z.comapDomain Sum.inl Sum.inl_injective.injOn) g)

theorem coeff_coeff_sumSplitFun (f : MvPowerSeries (σ ⊕ τ) S) (x : σ →₀ ℕ)
    (y : τ →₀ ℕ) : coeff y (coeff x (sumSplitFun f)) = coeff (x.sumElim y) f := rfl

/-- **`S⟦X, Y⟧ ≅ S⟦Y⟧⟦X⟧`**: a power series in the variables `X_i` (`i ∈ σ`) and `Y_k` (`k ∈ τ`)
is a power series in the `X_i` whose coefficients are power series in the `Y_k`. -/
noncomputable def sumSplitEquiv (σ τ S : Type*) [CommRing S] :
    MvPowerSeries (σ ⊕ τ) S ≃+* MvPowerSeries σ (MvPowerSeries τ S) where
  toFun := sumSplitFun
  invFun := sumJoinFun
  left_inv f := by
    ext z
    show coeff ((z.comapDomain Sum.inl Sum.inl_injective.injOn).sumElim
      (z.comapDomain Sum.inr Sum.inr_injective.injOn)) f = coeff z f
    rw [comapDomain_sumElim_comapDomain]
  right_inv g := by
    ext x y
    show coeff ((x.sumElim y).comapDomain Sum.inr Sum.inr_injective.injOn)
      (coeff ((x.sumElim y).comapDomain Sum.inl Sum.inl_injective.injOn) g) = coeff y (coeff x g)
    rw [comapDomain_inl_sumElim, comapDomain_inr_sumElim]
  map_add' f g := by
    ext x y
    show coeff (x.sumElim y) (f + g) = coeff (x.sumElim y) f + coeff (x.sumElim y) g
    rw [map_add]
  map_mul' f g := by
    classical
    ext x y
    rw [coeff_coeff_sumSplitFun, coeff_mul, coeff_mul, map_sum]
    simp_rw [coeff_mul, coeff_coeff_sumSplitFun]
    rw [← image_sumElim_product_antidiagonal, Finset.sum_image, Finset.sum_product]
    rintro ⟨⟨a, b⟩, c, d⟩ - ⟨⟨a', b'⟩, c', d'⟩ - h
    simp only [Prod.mk.injEq] at h
    obtain ⟨h1, h2⟩ := h
    have e1 := congrArg (fun z => z.comapDomain Sum.inl Sum.inl_injective.injOn) h1
    have e2 := congrArg (fun z => z.comapDomain Sum.inr Sum.inr_injective.injOn) h1
    have e3 := congrArg (fun z => z.comapDomain Sum.inl Sum.inl_injective.injOn) h2
    have e4 := congrArg (fun z => z.comapDomain Sum.inr Sum.inr_injective.injOn) h2
    simp only [comapDomain_inl_sumElim, comapDomain_inr_sumElim] at e1 e2 e3 e4
    rw [e1, e2, e3, e4]

theorem coeff_coeff_sumSplitEquiv (f : MvPowerSeries (σ ⊕ τ) S) (x : σ →₀ ℕ)
    (y : τ →₀ ℕ) : coeff y (coeff x (sumSplitEquiv σ τ S f)) = coeff (x.sumElim y) f := rfl

theorem sumSplitEquiv_C (s : S) :
    sumSplitEquiv σ τ S (C s) = C (C s) := by
  classical
  ext x y
  rw [coeff_coeff_sumSplitEquiv, coeff_C, coeff_C]
  by_cases hx : x = 0
  · subst hx
    rw [ite_eq_left rfl, coeff_C]
    by_cases hy : y = 0
    · subst hy; simp
    · rw [ite_eq_right hy, ite_eq_right]
      intro h
      apply hy
      have := congrArg (fun z => z.comapDomain Sum.inr Sum.inr_injective.injOn) h
      simpa using this
  · rw [ite_eq_right hx, ite_eq_right, map_zero]
    intro h
    apply hx
    have := congrArg (fun z => z.comapDomain Sum.inl Sum.inl_injective.injOn) h
    simpa using this

theorem sumSplitEquiv_X_inl (i : σ) :
    sumSplitEquiv σ τ S (X (Sum.inl i)) = X i := by
  classical
  ext x y
  rw [coeff_coeff_sumSplitEquiv, coeff_X, coeff_X]
  by_cases hx : x = single i 1
  · subst hx
    rw [ite_eq_left rfl, coeff_one]
    by_cases hy : y = 0
    · subst hy; simp
    · rw [ite_eq_right hy, ite_eq_right]
      intro h
      apply hy
      have := congrArg (fun z => z.comapDomain Sum.inr Sum.inr_injective.injOn) h
      simpa using this
  · rw [ite_eq_right hx, ite_eq_right, map_zero]
    intro h
    apply hx
    have := congrArg (fun z => z.comapDomain Sum.inl Sum.inl_injective.injOn) h
    simpa using this

theorem sumSplitEquiv_X_inr (k : τ) :
    sumSplitEquiv σ τ S (X (Sum.inr k)) = C (X k) := by
  classical
  ext x y
  rw [coeff_coeff_sumSplitEquiv, coeff_X, coeff_C]
  by_cases hx : x = 0
  · subst hx
    rw [ite_eq_left rfl, coeff_X]
    by_cases hy : y = single k 1
    · subst hy; simp
    · rw [ite_eq_right hy, ite_eq_right]
      intro h
      apply hy
      have := congrArg (fun z => z.comapDomain Sum.inr Sum.inr_injective.injOn) h
      simpa using this
  · rw [ite_eq_right hx, ite_eq_right, map_zero]
    intro h
    apply hx
    have := congrArg (fun z => z.comapDomain Sum.inl Sum.inl_injective.injOn) h
    simpa using this

end SumSplit

/-! ### `S⟦z₁, …, z_r⟧ ≅ S{z_{p+1}, …, z_r}⟦z₁, …, z_p⟧` -/

section FinSplit

open MvPowerSeries Finsupp

/-- The bijection `Fin p ⊕ Fin q ≃ Fin r` (`p + q = r`): the variables `z₁, …, z_p` first, then
`z_{p+1}, …, z_r`. -/
def finSplit {p q r : ℕ} (h : p + q = r) : Fin p ⊕ Fin q ≃ Fin r :=
  finSumFinEquiv.trans (finCongr h)

theorem finSplit_inl {p q r : ℕ} (h : p + q = r) (l : Fin p) :
    finSplit h (Sum.inl l) = Fin.castLE (by omega) l := Fin.ext rfl

theorem finSplit_inr {p q r : ℕ} (h : p + q = r) (k : Fin q) :
    finSplit h (Sum.inr k) = ⟨p + k, by omega⟩ := Fin.ext rfl

variable (S : Type*) [CommRing S]

/-- `S⟦z₁, …, z_r⟧ ≅ S⟦z_{p+1}, …, z_r⟧⟦z₁, …, z_p⟧` (`p + q = r`). -/
noncomputable def finSplitEquiv {p q r : ℕ} (h : p + q = r) :
    MvPowerSeries (Fin r) S ≃+* MvPowerSeries (Fin p) (MvPowerSeries (Fin q) S) :=
  (renameEquiv S (finSplit h).symm).toRingEquiv.trans (sumSplitEquiv (Fin p) (Fin q) S)

variable {S}

theorem finSplitEquiv_apply {p q r : ℕ} (h : p + q = r) (g : MvPowerSeries (Fin r) S) :
    finSplitEquiv S h g = sumSplitEquiv (Fin p) (Fin q) S (rename (finSplit h).symm g) := rfl

theorem finSplitEquiv_X_inl {p q r : ℕ} (h : p + q = r) (l : Fin p) :
    finSplitEquiv S h (X (finSplit h (Sum.inl l))) = X l := by
  rw [finSplitEquiv_apply, rename_X, Equiv.symm_apply_apply, sumSplitEquiv_X_inl]

theorem finSplitEquiv_X_inr {p q r : ℕ} (h : p + q = r) (k : Fin q) :
    finSplitEquiv S h (X (finSplit h (Sum.inr k))) = C (X k) := by
  rw [finSplitEquiv_apply, rename_X, Equiv.symm_apply_apply, sumSplitEquiv_X_inr]

theorem finSplitEquiv_C {p q r : ℕ} (h : p + q = r) (s : S) :
    finSplitEquiv S h (C s) = C (C s) := by
  rw [finSplitEquiv_apply, rename_C, sumSplitEquiv_C]

/-- The coefficients of the image in `S⟦z_{p+1}, …, z_r⟧⟦z₁, …, z_p⟧`: the coefficient of
`z'^{A''}` in the coefficient of `z^{A'}` is the coefficient of `z^A`, `A = (A', A'')`. -/
theorem coeff_coeff_finSplitEquiv {p q r : ℕ} (h : p + q = r)
    (g : MvPowerSeries (Fin r) S) (A : Fin r → ℕ) :
    coeff (equivFunOnFinite.symm fun k : Fin q => A (finSplit h (Sum.inr k)))
        (coeff (equivFunOnFinite.symm fun l : Fin p => A (finSplit h (Sum.inl l)))
          (finSplitEquiv S h g)) = coeff (equivFunOnFinite.symm A) g := by
  rw [finSplitEquiv_apply, coeff_coeff_sumSplitEquiv]
  have hA : (equivFunOnFinite.symm fun l : Fin p => A (finSplit h (Sum.inl l))).sumElim
      (equivFunOnFinite.symm fun k : Fin q => A (finSplit h (Sum.inr k))) =
      embDomain (finSplit h).symm.toEmbedding (equivFunOnFinite.symm A) := by
    ext z
    have h1 := embDomain_apply_self (finSplit h).symm.toEmbedding (equivFunOnFinite.symm A)
      (finSplit h z)
    simp only [Equiv.toEmbedding_apply, Equiv.symm_apply_apply] at h1
    rw [h1]
    rcases z with l | k <;> simp
  rw [hA]
  exact coeff_embDomain_rename (finSplit h).symm.toEmbedding g (equivFunOnFinite.symm A)

end FinSplit

/-! ### The partial frames of `S{z₁, …, z_r}` -/

section PartialFrame

open MvPowerSeries Finsupp

variable (S : Type u) [CommRing S] [IsRegularLocalRing S]

/-- **The partial frame** `(S{z_{p+1}, …, z_r}; z₁, …, z_p)` of `S{z₁, …, z_r} = S⟦z₁, …, z_r⟧`
(p. 253: "By the completeness of `R`, if `S_a = S{z_{τ_a+1}, …, z_τ}`, then `(S_a; z₁, …, z_{τ_a})`
is a regular frame of `R`"; p. 264: "Let `S^{(a)} = S{z_{τ_a+1}, …, z_τ}`").  Its coefficient ring
is `S⟦z_{p+1}, …, z_r⟧`; it is the regular frame `(S⟦z_{p+1}, …, z_r⟧; z₁, …, z_p)` of
`S⟦z_{p+1}, …, z_r⟧⟦z₁, …, z_p⟧` (`RegularFrame.mvPowerSeries`) carried to `S⟦z₁, …, z_r⟧` by the
isomorphism `finSplitEquiv`. -/
noncomputable def RegularFrame.partialFrame (r p : ℕ) (hp : p ≤ r) :
    RegularFrame (MvPowerSeries (Fin r) S) where
  S := MvPowerSeries (Fin (r - p)) S
  commRing := inferInstance
  isRegular := instIsRegularLocalRingMvPowerSeries S (r - p)
  algebra := ((RegularFrame.mvPowerSeries (MvPowerSeries (Fin (r - p)) S) p).transport
    (finSplitEquiv S (Nat.add_sub_cancel' hp)).symm).algebra
  isLocalHom := ((RegularFrame.mvPowerSeries (MvPowerSeries (Fin (r - p)) S) p).transport
    (finSplitEquiv S (Nat.add_sub_cancel' hp)).symm).isLocalHom
  r := p
  z := ((RegularFrame.mvPowerSeries (MvPowerSeries (Fin (r - p)) S) p).transport
    (finSplitEquiv S (Nat.add_sub_cancel' hp)).symm).z
  z_injective := ((RegularFrame.mvPowerSeries (MvPowerSeries (Fin (r - p)) S) p).transport
    (finSplitEquiv S (Nat.add_sub_cancel' hp)).symm).z_injective
  extends_rsop := ((RegularFrame.mvPowerSeries (MvPowerSeries (Fin (r - p)) S) p).transport
    (finSplitEquiv S (Nat.add_sub_cancel' hp)).symm).extends_rsop
  quot_bijective := ((RegularFrame.mvPowerSeries (MvPowerSeries (Fin (r - p)) S) p).transport
    (finSplitEquiv S (Nat.add_sub_cancel' hp)).symm).quot_bijective

variable {S}

@[simp]
theorem RegularFrame.partialFrame_r (r p : ℕ) (hp : p ≤ r) :
    (RegularFrame.partialFrame S r p hp).r = p := rfl

theorem RegularFrame.partialFrame_r_le (r p : ℕ) (hp : p ≤ r) :
    (RegularFrame.partialFrame S r p hp).r ≤ (RegularFrame.mvPowerSeries S r).r := hp

/-- The members of the partial frame are `z₁, …, z_p`. -/
theorem RegularFrame.partialFrame_z (r p : ℕ) (hp : p ≤ r)
    (l : Fin (RegularFrame.partialFrame S r p hp).r) :
    (RegularFrame.partialFrame S r p hp).z l =
      (RegularFrame.mvPowerSeries S r).z (Fin.castLE (RegularFrame.partialFrame_r_le r p hp) l) := by
  show (finSplitEquiv S (Nat.add_sub_cancel' hp)).symm (X l) = X (Fin.castLE hp l)
  rw [RingEquiv.symm_apply_eq]
  have := finSplitEquiv_X_inl (S := S) (Nat.add_sub_cancel' hp) l
  exact this.symm.trans (congrArg (fun j => finSplitEquiv S (Nat.add_sub_cancel' hp) (X j))
    (Fin.ext rfl))

theorem RegularFrame.partialFrame_z_eq (r p : ℕ) (hp : p ≤ r) :
    (RegularFrame.partialFrame S r p hp).z =
      fun l => (RegularFrame.mvPowerSeries S r).z
        (Fin.castLE (RegularFrame.partialFrame_r_le r p hp) l) :=
  funext fun l => RegularFrame.partialFrame_z r p hp l

/-- The structure map of the partial frame. -/
theorem RegularFrame.partialFrame_algebraMap (r p : ℕ) (hp : p ≤ r)
    (s : MvPowerSeries (Fin (r - p)) S) :
    algebraMap (RegularFrame.partialFrame S r p hp).S (MvPowerSeries (Fin r) S) s =
      (finSplitEquiv S (Nat.add_sub_cancel' hp)).symm (C s) := by
  show (finSplitEquiv S (Nat.add_sub_cancel' hp)).symm
    (algebraMap (MvPowerSeries (Fin (r - p)) S) (MvPowerSeries (Fin p) _) s) = _
  rw [algebraMap_mvPowerSeries_eq_C]

/-- `S ⊆ S{z_{p+1}, …, z_r}`: the image of `s ∈ S` in `R` through the coefficient ring of the
partial frame is its image through `S`. -/
theorem RegularFrame.partialFrame_algebraMap_C (r p : ℕ) (hp : p ≤ r) (s : S) :
    algebraMap (RegularFrame.partialFrame S r p hp).S (MvPowerSeries (Fin r) S) (C s) =
      algebraMap (RegularFrame.mvPowerSeries S r).S (MvPowerSeries (Fin r) S) s := by
  rw [RegularFrame.partialFrame_algebraMap, RingEquiv.symm_apply_eq]
  show C (C s) = finSplitEquiv S _ (algebraMap S (MvPowerSeries (Fin r) S) s)
  rw [algebraMap_mvPowerSeries_eq_C, finSplitEquiv_C]

/-- The isomorphism `finSplitEquiv` is the expansion map of the partial frame. -/
theorem RegularFrame.isExpansion_partialFrame (r p : ℕ) (hp : p ≤ r) :
    (RegularFrame.partialFrame S r p hp).IsExpansion
      (finSplitEquiv S (Nat.add_sub_cancel' hp) :
        MvPowerSeries (Fin r) S →+* MvPowerSeries (Fin p) (MvPowerSeries (Fin (r - p)) S)) where
  map_algebraMap s := by
    change finSplitEquiv S (Nat.add_sub_cancel' hp) ((finSplitEquiv S (Nat.add_sub_cancel' hp)).symm
      (algebraMap (MvPowerSeries (Fin (r - p)) S)
        (MvPowerSeries (Fin p) (MvPowerSeries (Fin (r - p)) S)) s)) = C s
    rw [RingEquiv.apply_symm_apply]
    exact algebraMap_mvPowerSeries_eq_C _ _ s
  map_z j := RingEquiv.apply_symm_apply _ _
  map_pow n x hx := by
    have h1 : Ideal.map (finSplitEquiv S (Nat.add_sub_cancel' hp))
        ((RegularFrame.partialFrame S r p hp).idealZ ^ n) =
        (Ideal.span (Set.range (X : Fin p → MvPowerSeries (Fin p) _))) ^ n := by
      rw [Ideal.map_pow, RegularFrame.idealZ, Ideal.map_span, ← Set.range_comp]
      congr 3
      funext j
      exact RingEquiv.apply_symm_apply _ _
    have h2 := Ideal.mem_map_of_mem (finSplitEquiv S (Nat.add_sub_cancel' hp)) hx
    rw [h1] at h2
    exact h2

/-- The expansion coefficients with respect to the partial frame are the coefficients in
`S⟦z_{p+1}, …, z_r⟧⟦z₁, …, z_p⟧`. -/
theorem RegularFrame.partialFrame_expCoeff (r p : ℕ) (hp : p ≤ r) (g : MvPowerSeries (Fin r) S)
    (B : Fin (RegularFrame.partialFrame S r p hp).r →₀ ℕ) :
    (RegularFrame.partialFrame S r p hp).expCoeff g B =
      coeff B (finSplitEquiv S (Nat.add_sub_cancel' hp) g) := by
  have h := isExpansion_unique_aux (RegularFrame.partialFrame S r p hp)
    (isExpansion_expansion _) (RegularFrame.isExpansion_partialFrame r p hp)
  have h2 := coeff_expansion (RegularFrame.partialFrame S r p hp) g B
  rw [h] at h2
  exact h2.symm

end PartialFrame

/-! ### Remarks 1 and 2 of §7 for the partial frames -/

section PartialNormalized

open MvPowerSeries Finsupp

/-- The `E`-function of a non-zero constant is `0`. -/
theorem eFunction_C {K : Type*} [CommRing K] {r : ℕ} {c : K} (hc : c ≠ 0) :
    EFunction (MvPolynomial.C c : MvPolynomial (Fin r) K) = 0 := by
  classical
  have hs : (MvPolynomial.C c : MvPolynomial (Fin r) K).support = {0} := by
    rw [MvPolynomial.support_C, ite_eq_right hc]
  have hne : (MvPolynomial.C c : MvPolynomial (Fin r) K).support.Nonempty := by
    rw [hs]; exact Finset.singleton_nonempty _
  unfold EFunction
  rw [dite_eq_left hne]
  set M := ((MvPolynomial.C c : MvPolynomial (Fin r) K).support.image fun A => toLex A).max'
    (hne.image _) with hM
  have hm : M ∈ (MvPolynomial.C c : MvPolynomial (Fin r) K).support.image fun A => toLex A :=
    Finset.max'_mem _ _
  rw [hs, Finset.image_singleton, Finset.mem_singleton] at hm
  rw [hm]
  rfl

/-- `E`-sets are monotone in the ideal. -/
theorem eSet_mono {K : Type*} [CommRing K] {r : ℕ} {I I' : Ideal (MvPolynomial (Fin r) K)}
    (h : I ≤ I') : ESet I ⊆ ESet I' := by
  rintro A ⟨A₀, ⟨φ, hφ, hrest⟩, B, rfl⟩
  exact ⟨A₀, ⟨φ, h hφ, hrest⟩, B, rfl⟩

attribute [local instance] MvPolynomial.gradedAlgebra in
/-- **Remark 2 of §7** (pp. 245–246), the inclusion `q(E_t(I₀)) ⊆ E_r(I)` for `I = I₀ S[Z₁, …, Z_r]`,
in the form used for the partial frames: if `B ∈ E_p(I₀)` then `q(B) + D ∈ E_r(I)` for every
`D ∈ Z₀ʳ` (the `E`-set is an `E`-subset).  For `1 ≤ p < r` this is `eSet_isBound_qInj_image`; the
cases `p = 0` (then `I₀` contains a non-zero constant) and `p = r` are direct. -/
theorem qInj_add_mem_eSet_map {K : Type*} [CommRing K] [IsNoetherianRing K] {p r : ℕ}
    (hp : p ≤ r) (I₀ : Ideal (MvPolynomial (Fin p) K))
    (hI₀ : I₀.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin p) K)) {B : Fin p → ℕ}
    (hB : B ∈ ESet I₀) (D : Fin r → ℕ) :
    qInj p r B + D ∈ ESet (I₀.map (MvPolynomial.rename (R := K) (Fin.castLE hp))) := by
  classical
  rcases Nat.eq_zero_or_pos p with rfl | hp0
  · obtain ⟨φ, hφI, hφ0, -, -⟩ := (mem_eSet_iff I₀ hI₀ B).mp hB
    obtain ⟨c, hφC⟩ := MvPolynomial.C_surjective (R := K) (Fin 0) φ
    have hφC := hφC.symm
    have hc0 : c ≠ 0 := by
      intro h0
      apply hφ0
      rw [hφC, h0, map_zero]
    refine ⟨0, ⟨MvPolynomial.C c, ?_, ?_, ⟨0, ?_⟩, (eFunction_C hc0).symm⟩, qInj 0 r B + D,
      (zero_add _).symm⟩
    · rw [← MvPolynomial.rename_C (Fin.castLE hp), ← hφC]
      exact Ideal.mem_map_of_mem _ hφI
    · simpa using hc0
    · rw [MvPolynomial.mem_homogeneousSubmodule]
      exact MvPolynomial.isHomogeneous_C _ _
  rcases lt_or_eq_of_le hp with hlt | rfl
  · obtain ⟨h1, -⟩ := eSet_isBound_qInj_image hp0 hlt I₀ hI₀
    obtain ⟨A₀, hA₀, C', hC'⟩ := h1 ⟨B, hB, rfl⟩
    exact ⟨A₀, hA₀, C' + D, by rw [hC', add_assoc]⟩
  · have hid : (MvPolynomial.rename (R := K) (Fin.castLE hp)) = AlgHom.id K _ := by
      apply MvPolynomial.algHom_ext
      intro i
      rw [MvPolynomial.rename_X, AlgHom.id_apply]
      exact congrArg MvPolynomial.X (Fin.ext rfl)
    have hmap : I₀.map (MvPolynomial.rename (R := K) (Fin.castLE hp)) = I₀ := by
      rw [hid]
      exact Ideal.map_id I₀
    have hq : qInj p p B = B := funext fun i => by simp [qInj, i.2]
    rw [hmap, hq]
    obtain ⟨A₀, hA₀, C', rfl⟩ := hB
    exact ⟨A₀, hA₀, C' + D, by rw [add_assoc]⟩

variable {S : Type u} [CommRing S] [IsRegularLocalRing S]

/-- The `k`-algebra map `k[Z₁, …, Z_p] → gr_M(R)` of the partial frame is that of the frame
`(S; z₁, …, z_r)` restricted to the polynomials in `Z₁, …, Z_p`. -/
theorem RegularFrame.frameAlgHom_partialFrame (r p : ℕ) (hp : p ≤ r)
    (ψ : MvPolynomial (Fin (RegularFrame.partialFrame S r p hp).r)
      (MvPowerSeries (Fin r) S ⧸ maximalIdeal (MvPowerSeries (Fin r) S))) :
    frameAlgHom (RegularFrame.mvPowerSeries S r).z
        (MvPolynomial.rename (Fin.castLE (RegularFrame.partialFrame_r_le r p hp)) ψ) =
      frameAlgHom (RegularFrame.partialFrame S r p hp).z ψ := by
  rw [frameAlgHom, frameAlgHom, MvPolynomial.aeval_rename, RegularFrame.partialFrame_z_eq]
  rfl

attribute [local instance] MvPolynomial.gradedAlgebra in
/-- The ideal `I = (φ₁, …, φ_i) k[Z₁, …, Z_r]` is generated by the ideal
`I₀ = (φ₁, …, φ_i) k[Z₁, …, Z_p]` when the initial forms `φ_j` lie in `k[Z₁, …, Z_p]`; `I₀` is
homogeneous. -/
theorem RegularFrame.frameInitialIdeal_partialFrame (r p : ℕ) (hp : p ≤ r) {i : ℕ}
    (f : Fin i → MvPowerSeries (Fin r) S)
    (hf : ∀ j, initialForm (maximalIdeal _) (f j) ∈
      (RegularFrame.partialFrame S r p hp).assocSubalgebra) :
    frameInitialIdeal (RegularFrame.mvPowerSeries S r).z f =
        (frameInitialIdeal (RegularFrame.partialFrame S r p hp).z f).map
          (MvPolynomial.rename (Fin.castLE (RegularFrame.partialFrame_r_le r p hp))) ∧
      (frameInitialIdeal (RegularFrame.partialFrame S r p hp).z f).IsHomogeneous
        (MvPolynomial.homogeneousSubmodule (Fin (RegularFrame.partialFrame S r p hp).r)
          (MvPowerSeries (Fin r) S ⧸ maximalIdeal (MvPowerSeries (Fin r) S))) := by
  classical
  have hf' : ∀ j, initialForm (maximalIdeal _) (f j) ∈
      Set.range (frameAlgHom (RegularFrame.partialFrame S r p hp).z) := fun j => by
    have := hf j
    rw [RegularFrame.assocSubalgebra, Hironaka.assocSubalgebra,
      Algebra.adjoin_range_eq_range_aeval] at this
    exact this
  choose Pf hPf using hf'
  have hI0 : frameInitialIdeal (RegularFrame.partialFrame S r p hp).z f =
      Ideal.span (Set.range Pf) := by
    unfold frameInitialIdeal
    congr 1
    ext ψ
    constructor
    · rintro ⟨j, hj⟩
      exact ⟨j, (RegularFrame.partialFrame S r p hp).frameAlgHom_injective
        ((hPf j).trans hj.symm)⟩
    · rintro ⟨j, rfl⟩
      exact ⟨j, hPf j⟩
  have hI : frameInitialIdeal (RegularFrame.mvPowerSeries S r).z f =
      Ideal.span (Set.range fun j =>
        MvPolynomial.rename (Fin.castLE (RegularFrame.partialFrame_r_le r p hp)) (Pf j)) := by
    unfold frameInitialIdeal
    congr 1
    ext ψ
    constructor
    · rintro ⟨j, hj⟩
      refine ⟨j, (RegularFrame.mvPowerSeries S r).frameAlgHom_injective ?_⟩
      exact (RegularFrame.frameAlgHom_partialFrame r p hp (Pf j)).trans ((hPf j).trans hj.symm)
    · rintro ⟨j, rfl⟩
      exact ⟨j, (RegularFrame.frameAlgHom_partialFrame r p hp (Pf j)).trans (hPf j)⟩
  refine ⟨?_, ?_⟩
  · rw [hI, hI0, Ideal.map_span, ← Set.range_comp]
    rfl
  · rw [hI0]
    apply Ideal.homogeneous_span
    rintro _ ⟨j, rfl⟩
    obtain ⟨d, hd⟩ := initialForm_mem_homogeneous_aux' (maximalIdeal (MvPowerSeries (Fin r) S))
      (f j)
    exact ⟨d, (RegularFrame.partialFrame S r p hp).isHomogeneous_of_frameAlgHom_mem_homogeneous
      (by rw [hPf j]; exact hd)⟩

/-- **Remarks 1 and 2 of §7 for the partial frame** (Theorem 7, p. 253: "`f_{m_a+j}` is normalized
by `(f₁, …, f_{m_a})` with respect to `(S; z₁, …, z_τ)` and therefore, in view of Remarks 1 and 2,
`f_{m_a+j}` is normalized by `(f₁, …, f_{m_a})` with respect to `(S_a; z₁, …, z_{τ_a})`"): if the
initial forms of `f₁, …, f_i` lie in `k[Z₁, …, Z_p]` and `g` is normalized by `(f₁, …, f_i)` with
respect to `(S; z₁, …, z_r)`, then `g` is normalized by `(f₁, …, f_i)` with respect to
`(S{z_{p+1}, …, z_r}; z₁, …, z_p)`.  The coefficient of `z^B` in the expansion with respect to
the partial frame is `Σ_C c_{(B, C)} z'^C`, and `(B, C) = q(B) + (0, C)` lies in the `E`-set of
`(f₁, …, f_i)` with respect to `(k; Z₁, …, Z_r)` when `B` lies in that with respect to
`(k; Z₁, …, Z_p)` (Remark 2, `qInj_add_mem_eSet_map`). -/
theorem RegularFrame.isNormalizedBy_partialFrame (r p : ℕ) (hp : p ≤ r) {i : ℕ}
    (f : Fin i → MvPowerSeries (Fin r) S) (g : MvPowerSeries (Fin r) S)
    (hf : ∀ j, initialForm (maximalIdeal _) (f j) ∈
      (RegularFrame.partialFrame S r p hp).assocSubalgebra)
    (h : (RegularFrame.mvPowerSeries S r).IsNormalizedBy f g) :
    (RegularFrame.partialFrame S r p hp).IsNormalizedBy f g := by
  classical
  obtain ⟨hI, hhom⟩ := RegularFrame.frameInitialIdeal_partialFrame r p hp f hf
  rw [RegularFrame.isNormalizedBy_iff_expCoeff] at h ⊢
  intro B hB
  rw [RegularFrame.partialFrame_expCoeff]
  refine MvPowerSeries.ext fun C' => ?_
  refine Eq.trans ?_ (MvPowerSeries.coeff_zero C').symm
  set A : Fin (RegularFrame.mvPowerSeries S r).r → ℕ :=
    fun i => if hi : (i : ℕ) < p then B ⟨i, hi⟩ else C' ⟨i - p, by have : (i : ℕ) < r := i.2; omega⟩
    with hA
  have hAl : (fun l : Fin p => A (finSplit (Nat.add_sub_cancel' hp) (Sum.inl l))) = B := by
    funext l
    rw [finSplit_inl]
    simp [hA, l.2]
  have hAr : (fun k : Fin (r - p) => A (finSplit (Nat.add_sub_cancel' hp) (Sum.inr k))) = ⇑C' := by
    funext k
    rw [finSplit_inr]
    simp [hA]
  have key := coeff_coeff_finSplitEquiv (Nat.add_sub_cancel' hp) g A
  rw [hAl, hAr, Finsupp.equivFunOnFinite_symm_coe] at key
  refine key.trans ?_
  refine (RegularFrame.expCoeff_mvPowerSeries S r g _).symm.trans ?_
  refine h A ?_
  have hD := qInj_add_mem_eSet_map (RegularFrame.partialFrame_r_le r p hp) _ hhom hB
    (fun i => if hi : (i : ℕ) < p then 0 else C' ⟨i - p, by have : (i : ℕ) < r := i.2; omega⟩)
  rw [frameESet, hI]
  convert hD using 1
  funext i
  by_cases hi : (i : ℕ) < p
  · simp [hA, qInj, hi]
  · simp [hA, qInj, hi]

/-- Normalization by a system implies normalization by an initial segment of it (the `E`-set of an
initial segment is contained in that of the system, the ideal being smaller). -/
theorem RegularFrame.IsNormalizedBy.prefix {R : Type u} [CommRing R] [IsRegularLocalRing R]
    (F : RegularFrame R) {j : ℕ} (f : Fin j → R) {i : ℕ} (hij : i ≤ j) {g : R}
    (h : F.IsNormalizedBy f g) : F.IsNormalizedBy (fun l : Fin i => f (Fin.castLE hij l)) g := by
  intro e he A hA
  refine h e he A (eSet_mono ?_ hA)
  unfold frameInitialIdeal
  refine Ideal.span_mono ?_
  rintro ψ ⟨l, hl⟩
  exact ⟨Fin.castLE hij l, hl⟩

end PartialNormalized

/-! ### The frame transform of a partial frame -/

section PartialFrameTransform

variable {S : Type u} [CommRing S] [IsRegularLocalRing S]

/-- **The frame transform of the partial frame with the denominator `x`** (p. 264: "Let
`(S^{(a)}₁; w₁, …, w_{τ_a})` be the frame transform of `(S^{(a)}; z₁, …, z_{τ_a})` in `R₁` with the
denominator `x`"; its existence is not argued in the paper).  If `(S₁; w₁, …, w_r)` is a frame
transform of `(S; z₁, …, z_r)` in `R₁` with denominator `x ∈ P ∩ S`, then the partial frame
`(S{z_{p+1}, …, z_r}; z₁, …, z_p)` has a frame transform in `R₁` with the same denominator `x`
(`x ∈ S ⊆ S{z_{p+1}, …, z_r}`), whose members are `w₁, …, w_p`: the criterion
`exists_frameTransform_denominator_eq` (Lemma 13's construction of p. 253) needs only
`(x)R₁ = PR₁`, `x · w_j = z_j` and `w_j ∈ M₁`. -/
theorem RegularFrame.exists_partialFrame_frameTransform {r p : ℕ} (hp : p ≤ r)
    {P : Ideal (MvPowerSeries (Fin r) S)} [P.IsPrime]
    [IsRegularLocalRing (MvPowerSeries (Fin r) S ⧸ P)] {T : MonoidalTransform _ P}
    [IsRegularLocalRing T.ring] (x : (RegularFrame.mvPowerSeries S r).S)
    (hxP : algebraMap (RegularFrame.mvPowerSeries S r).S (MvPowerSeries (Fin r) S) x ∈ P)
    (hx : P.map T.toRing = Ideal.span {T.toRing (algebraMap _ (MvPowerSeries (Fin r) S) x)})
    (FT : (RegularFrame.mvPowerSeries S r).FrameTransform T)
    (hFTx : FT.x = T.toRing
      (algebraMap (RegularFrame.mvPowerSeries S r).S (MvPowerSeries (Fin r) S) x)) :
    ∃ FTp : (RegularFrame.partialFrame S r p hp).FrameTransform T,
      FTp.x = T.toRing
        (algebraMap (RegularFrame.mvPowerSeries S r).S (MvPowerSeries (Fin r) S) x) ∧
      ∀ l, FTp.w l = FT.w (Fin.castLE (RegularFrame.partialFrame_r_le r p hp) l) := by
  classical
  have := Transforms.isDomain_of_isRegularLocalRing T.ring
  have hC := RegularFrame.partialFrame_algebraMap_C (S := S) r p hp x
  have hw : ∀ l, T.toRing (algebraMap (RegularFrame.partialFrame S r p hp).S
      (MvPowerSeries (Fin r) S) (MvPowerSeries.C x)) *
        FT.w (Fin.castLE (RegularFrame.partialFrame_r_le r p hp) l) =
      T.toRing ((RegularFrame.partialFrame S r p hp).z l) := by
    intro l
    rw [hC, ← hFTx, FT.mul_w, RegularFrame.partialFrame_z]
  have hnu : ∀ l, ¬ IsUnit (FT.w (Fin.castLE (RegularFrame.partialFrame_r_le r p hp) l)) := by
    intro l hl
    obtain ⟨s, hsub, hs⟩ := FT.extends_rsop
    have hwM : FT.w (Fin.castLE (RegularFrame.partialFrame_r_le r p hp) l) ∈
        maximalIdeal T.ring := by
      rw [← hs.1]
      exact Ideal.subset_span (hsub (Finset.mem_image_of_mem _ (Finset.mem_univ _)))
    exact hwM hl
  obtain ⟨FTp, hFTp⟩ := RegularFrame.exists_frameTransform_denominator_eq
    (F := RegularFrame.partialFrame S r p hp) (P := P) (T := T) (MvPowerSeries.C x)
    (by rw [hC]; exact hxP) (by rw [hC]; exact hx) hw hnu
  rw [hC] at hFTp
  refine ⟨FTp, hFTp, fun l => ?_⟩
  have hx0 : FTp.x ≠ 0 := by
    intro h0
    have h1 : P.map T.toRing = ⊥ := by rw [← FTp.span_x, h0, Ideal.span_singleton_eq_bot]
    exact T.x_ne_zero (T.toRing_injective ((Ideal.mem_bot.mp
      (h1 ▸ Ideal.mem_map_of_mem T.toRing T.x_mem)).trans (map_zero _).symm))
  refine mul_left_cancel₀ hx0 ((FTp.mul_w l).trans ?_)
  rw [hFTp, ← hC]
  exact (hw l).symm

end PartialFrameTransform

end Hironaka
