/-
Copyright (c) 2026 Daattavya Aggarwal, Minhyong Kim, Oisin Kim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daattavya Aggarwal, Minhyong Kim, Oisin Kim
-/
module

public import Mathlib.Algebra.MvPolynomial.Supported
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Hironaka.Compat.WeierstrassAdaptedModel

/-!
# Lemma 25, (ii) of (c) (pp. 271--272): the coordinates and the two adapted models

> "Let us choose a minimal base `(y₁, …, y_i)` of `Q₀` in such a way that `y = y_i` and
> `ȳ_j = y_j/y ∈ M₁` for `1 ≤ j ≤ i - 1`."  (p. 271)
> "Let `b = i - 1`.  Let us choose a regular system of parameters `(y₁, …, y_b, y, x₁, …, x_a)` of
> `S₀`.  Then … `(z̄₁, …, z̄_r, w̄, ȳ₁, …, ȳ_b, y, x₁, …, x_a)` is a regular system of parameters of
> `R₁`.
> … Let `φ` (resp. `φ̄`) denote
> the initial form of `f` (resp. `f̄`) in `gr_M(R)` (resp. `gr_{M₁}(R₁)`).  Then
> `deg φ = deg φ̄ = ν`, `φ` is a form only in `Z₁, …, Z_r, W, Y₁, …, Y_τ`, and
> `φ̄ = φ(Z̄₁, …, Z̄_r, W̄, Ȳ₁, …, Ȳ_τ) + φ̄*` with
> `φ̄* ∈ (Y, X₁, …, X_a) gr_{M₁}(R₁)`."  (p. 272)

This file provides the coordinates and the polynomial pictures of this passage, for `R₁`
residually rational over `R` (the case to which the proof reduces: "the proof of (ii) of (c) can be
reduced to the case in which the residue field `k` of `S₀` is algebraically closed, so that `R₁` is
residually rational over `R`", p. 271):

* `WeierstrassDatum.AdaptedCoords` (with `t = b`, `s = a`): the elements `(y₁, …, y_b)`,
  `(x₁, …, x_a)` of `S₀`, the quotients `ȳ_j` in `S₀₁`, and the facts that `(y₁, …, y_b, y, x₁, …,
  x_a)`, `(ȳ₁, …, ȳ_b, y, x₁, …, x_a)` are regular systems of parameters of `S₀`, `S₀₁`, that
  `(z, w, y_j, y, x_k)`, `(z̄, w̄, ȳ_j, y, x_k)` are regular systems of parameters of `R`, `R₁`, and
  that `P = (z, w, y₁, …, y_b, y)R`; their existence is `WeierstrassDatum.exists_adaptedCoords`;
* `AdaptedCoords.recoord`: the change of coordinates `y_j ↦ ∑_l C_{jl} y_l + v_j y` (`C`
  invertible over `S₀`, `v_j ∈ (y, x₁, …, x_a)`), which keeps all these facts; the two "we may
  assume" normalizations of pp. 271--272 are of this form (`Compat/WeierstrassNormalization.lean`);
* `AdaptedCoords.modelR`, `AdaptedCoords.modelT`: the pictures
  `gr_M(R) = k[Z, W, Y₁, …, Y_b, Y, X₁, …, X_a]`, `gr_{M₁}(R₁) = k[Z̄, W̄, Ȳ₁, …, Ȳ_b, Y, X₁, …,
  X_a]`, adapted to the data (`AdaptedCoords.isAdaptedModel`, `isAdaptedModel_transform`), and the
  comparison of the initial forms (`AdaptedCoords.forms`: `φ` supported on the variables
  `Z, W, Y_j`,
  `φ̄ - φ ∈ (Y, X)`, from `forms_of_coordinates`, i.e. `forms_correspond`).

The route to the coordinates (a formalization choice) is the proof of
Lemma 21 for the two frames at once: the *composite regular frame* `(S₀; z₁, …, z_r, w)` of `R`
(`WeierstrassDatum.compositeFrame`; `R/(z, w)R ≅ S₀`) and its frame transform
`(S₀₁; z̄₁, …, z̄_r, w̄)` in `R₁` with denominator `y`
(`WeierstrassDatum.compositeFrameTransform`).  The coordinates of Lemma 21
(`RegularFrame.FrameTransform.exists_coordinates_spans`) for this pair have `(y₁, …, y_b)` in the
role of `(x₁, …, x_t)` there and `y` in the role of `x`; all of `y₁, …, y_b, y, x₁, …, x_a` lie in
`S₀`, and the `ȳ_j` are elements of `S₀₁`.
-/

@[expose] public section

open IsLocalRing MvPolynomial Matrix

namespace Hironaka

universe u

section CompositeFrame

variable {R : Type u} [CommRing R] [IsRegularLocalRing R]

namespace WeierstrassDatum

variable (D : WeierstrassDatum R)

/-- For `a ∈ S`: `a ∈ (z₁, …, z_r, w)R` iff `a ∈ (w)S` (`R/(z)R ≅ S`). -/
theorem algebraMap_mem_span_snoc_iff (a : D.F.S) :
    algebraMap D.F.S R a ∈ Ideal.span (Set.range (Fin.snoc D.F.z D.wR : Fin (D.F.r + 1) → R)) ↔
      a ∈ Ideal.span {D.w} := by
  classical
  have hJ : Ideal.span (Set.range (Fin.snoc D.F.z D.wR : Fin (D.F.r + 1) → R)) =
      D.F.idealZ ⊔ Ideal.span {D.wR} := by
    rw [RegularFrame.idealZ, ← Ideal.span_union]
    congr 1
    ext y
    constructor
    · rintro ⟨i, rfl⟩
      refine Fin.lastCases ?_ (fun j => ?_) i
      · right; simp
      · left; exact ⟨j, by simp⟩
    · rintro (⟨j, rfl⟩ | h)
      · exact ⟨j.castSucc, by simp⟩
      · rw [Set.mem_singleton_iff.mp h]; exact ⟨Fin.last _, by simp⟩
  rw [hJ]
  constructor
  · intro ha
    obtain ⟨i, hi, c, hc, hsum⟩ := Submodule.mem_sup.mp ha
    obtain ⟨c', rfl⟩ := Ideal.mem_span_singleton'.mp hc
    have h1 := congrArg D.F.retraction hsum
    rw [map_add, (D.F.retraction_eq_zero_iff i).mpr hi, zero_add, D.F.retraction_algebraMap,
      map_mul] at h1
    have h2 : D.F.retraction D.wR = D.w := D.F.retraction_algebraMap D.w
    rw [h2] at h1
    rw [← h1]
    exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)
  · intro ha
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp ha
    rw [map_mul]
    exact Ideal.mem_sup_right (Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _))

/-- "`R/(z₁, …, z_r, w)R` is canonically isomorphic to `S₀`": the composite
`S₀ → S → R → R/(z₁, …, z_r, w)R` is bijective (`R/(z)R ≅ S` and `S/(w)S ≅ S₀`). -/
theorem quot_bijective_snoc :
    Function.Bijective ((Ideal.Quotient.mk (Ideal.span (Set.range
      (Fin.snoc D.F.z D.wR : Fin (D.F.r + 1) → R)))).comp
        ((algebraMap D.F.S R).comp (algebraMap D.F0.S D.F.S))) := by
  classical
  set J := Ideal.span (Set.range (Fin.snoc D.F.z D.wR : Fin (D.F.r + 1) → R)) with hJ
  have hrange : Set.range D.F0.z = {D.w} := by
    ext y
    constructor
    · rintro ⟨j, rfl⟩
      exact D.z0_eq j
    · intro hy
      rw [Set.mem_singleton_iff] at hy
      exact ⟨Fin.cast D.rank_eq_one.symm 0, by rw [hy]; rfl⟩
  have hq0 := D.F0.quot_bijective
  rw [hrange] at hq0
  have hzJ : D.F.idealZ ≤ J := Ideal.span_mono (by
    rintro _ ⟨j, rfl⟩
    exact ⟨j.castSucc, by simp⟩)
  constructor
  · rw [injective_iff_map_eq_zero]
    intro a ha
    have h1 : algebraMap D.F.S R (algebraMap D.F0.S D.F.S a) ∈ J := by
      have := (Ideal.Quotient.eq_zero_iff_mem).mp ha
      exact this
    have h2 := (D.algebraMap_mem_span_snoc_iff _).mp h1
    have h3 : (Ideal.Quotient.mk (Ideal.span {D.w})).comp (algebraMap D.F0.S D.F.S) a = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr h2
    exact hq0.1 (h3.trans (map_zero _).symm)
  · intro y
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective y
    obtain ⟨s, hs⟩ := D.F.quot_bijective.2 (Ideal.Quotient.mk D.F.idealZ r)
    obtain ⟨s₀, hs₀⟩ := hq0.2 (Ideal.Quotient.mk (Ideal.span {D.w}) s)
    refine ⟨s₀, ?_⟩
    have h1 : algebraMap D.F.S R s - r ∈ D.F.idealZ := Ideal.Quotient.eq.mp hs
    have h2 : algebraMap D.F0.S D.F.S s₀ - s ∈ Ideal.span {D.w} := Ideal.Quotient.eq.mp hs₀
    have h3 : algebraMap D.F.S R (algebraMap D.F0.S D.F.S s₀ - s) ∈ J :=
      (D.algebraMap_mem_span_snoc_iff _).mpr h2
    show Ideal.Quotient.mk J (algebraMap D.F.S R (algebraMap D.F0.S D.F.S s₀)) =
      Ideal.Quotient.mk J r
    rw [Ideal.Quotient.eq]
    have : algebraMap D.F.S R (algebraMap D.F0.S D.F.S s₀) - r =
        algebraMap D.F.S R (algebraMap D.F0.S D.F.S s₀ - s) + (algebraMap D.F.S R s - r) := by
      rw [map_sub]; ring
    rw [this]
    exact add_mem h3 (hzJ h1)

/-- **The composite regular frame** `(S₀; z₁, …, z_r, w)` of `R`: `R/(z, w)R ≅ S₀` and
`(z₁, …, z_r, w)` extends to a regular system of parameters of `R`. -/
noncomputable def compositeFrame : RegularFrame R where
  S := D.F0.S
  algebra := ((algebraMap D.F.S R).comp (algebraMap D.F0.S D.F.S)).toAlgebra
  isLocalHom := by
    let : Algebra D.F0.S R := ((algebraMap D.F.S R).comp (algebraMap D.F0.S D.F.S)).toAlgebra
    exact (inferInstance : IsLocalHom ((algebraMap D.F.S R).comp (algebraMap D.F0.S D.F.S)))
  r := D.F.r + 1
  z := Fin.snoc D.F.z D.wR
  z_injective := D.injective_snoc
  extends_rsop := D.extendsToRSOP_snoc
  quot_bijective := D.quot_bijective_snoc

end WeierstrassDatum

end CompositeFrame

section CompositeTransform

attribute [local instance] RegularFrame.isDomain_S

variable {R : Type u} [CommRing R] [IsRegularLocalRing R] [IsDomain R] (D : WeierstrassDatum R)
  {P : Ideal R} [P.IsPrime] [IsRegularLocalRing (R ⧸ P)] {T : MonoidalTransform R P}
  [IsLocalHom T.toRing] [IsRegularLocalRing T.ring]

omit [IsRegularLocalRing (R ⧸ P)] [IsLocalHom T.toRing] in
/-- `z_j = y z̄_j` and `w = y w̄` (the relations of the composite frame transform). -/
theorem WeierstrassDatum.compositeFrameTransform_mul_w (FT' : D.F.FrameTransform T)
    (FT0 : D.F0.FrameTransform FT'.TS) (y : D.F0.S)
    (hx : FT'.x = T.toRing (algebraMap D.F.S R (algebraMap D.F0.S D.F.S y)))
    (hx0 : FT0.x = FT'.TS.toRing (algebraMap D.F0.S D.F.S y)) (j : Fin (D.F.r + 1)) :
    FT'.x * (Fin.snoc FT'.w (D.transform FT' FT0).wR : Fin (D.F.r + 1) → T.ring) j =
      T.toRing ((Fin.snoc D.F.z D.wR : Fin (D.F.r + 1) → R) j) := by
  refine Fin.lastCases ?_ (fun j => ?_) j
  · -- `y · w̄ = w`
    have h1 : FT0.x * FT0.w (Fin.cast D.rank_eq_one.symm 0) =
        FT'.TS.toRing (D.F0.z (Fin.cast D.rank_eq_one.symm 0)) :=
      FT0.mul_w (Fin.cast D.rank_eq_one.symm 0)
    have h2 := congrArg FT'.β h1
    rw [map_mul, hx0] at h2
    have h3 : FT'.β (FT'.TS.toRing (algebraMap D.F0.S D.F.S y)) = FT'.x := by
      rw [hx, ← RingHom.comp_apply FT'.β, FT'.canonical.comm]
      rfl
    rw [h3] at h2
    simp only [Fin.snoc_last]
    show FT'.x * FT'.β (FT0.w (Fin.cast D.rank_eq_one.symm 0)) = T.toRing D.wR
    rw [h2, ← RingHom.comp_apply FT'.β, FT'.canonical.comm]
    rfl
  · simp only [Fin.snoc_castSucc]
    exact FT'.mul_w j

/-- **The composite frame transform**: the frame transforms `FT'` of `(S; z)` (denominator `y`) and
`FT0` of `(S₀; w)` give the frame transform `(S₀₁; z̄₁, …, z̄_r, w̄)` of the composite frame
`(S₀; z₁, …, z_r, w)` in `R₁`, with the same denominator `y` (`z_j = y z̄_j`, `w = y w̄`). -/
noncomputable def WeierstrassDatum.compositeFrameTransform (FT' : D.F.FrameTransform T)
    (FT0 : D.F0.FrameTransform FT'.TS) (y : D.F0.S)
    (hx : FT'.x = T.toRing (algebraMap D.F.S R (algebraMap D.F0.S D.F.S y)))
    (hx0 : FT0.x = FT'.TS.toRing (algebraMap D.F0.S D.F.S y)) :
    D.compositeFrame.FrameTransform T where
  x := FT'.x
  span_x := FT'.span_x
  TS := FT0.TS
  β := FT'.β.comp FT0.β
  canonical :=
    { isLocalHom := by
        have := FT0.canonical.isLocalHom
        have := FT'.canonical.isLocalHom
        exact RingHom.isLocalHom_comp FT'.β FT0.β
      comm := by
        have h1 := FT0.canonical.comm
        have h2 := FT'.canonical.comm
        calc (FT'.β.comp FT0.β).comp FT0.TS.toRing
            = FT'.β.comp (FT0.β.comp FT0.TS.toRing) := RingHom.comp_assoc _ _ _
          _ = FT'.β.comp (FT'.TS.toRing.comp (algebraMap D.F0.S D.F.S)) := by rw [h1]
          _ = (FT'.β.comp FT'.TS.toRing).comp (algebraMap D.F0.S D.F.S) :=
            (RingHom.comp_assoc _ _ _).symm
          _ = (T.toRing.comp (algebraMap D.F.S R)).comp (algebraMap D.F0.S D.F.S) := by rw [h2]
          _ = T.toRing.comp ((algebraMap D.F.S R).comp (algebraMap D.F0.S D.F.S)) :=
            RingHom.comp_assoc _ _ _ }
  isRegular := FT0.isRegular
  w := Fin.snoc FT'.w (D.transform FT' FT0).wR
  mul_w := D.compositeFrameTransform_mul_w FT' FT0 y hx hx0
  extends_rsop := (D.transform FT' FT0).extendsToRSOP_snoc
  quot_bijective := (D.transform FT' FT0).quot_bijective_snoc

end CompositeTransform


section Main

attribute [local instance] RegularFrame.isDomain_S
attribute [local instance] Ideal.Quotient.field

/-- The three kinds of coordinates of the form `(z, w, x_k, y, ys)`: an index of
`Fin ((m + t) + (s + 1))` is a `z`/`w`-index, an `x`-index, the index of `y`, or a `ys`-index. -/
theorem fin_split_three {m t s : ℕ} (i : Fin ((m + t) + (s + 1))) :
    (∃ j : Fin m, i = Fin.castAdd (s + 1) (Fin.castAdd t j)) ∨
      (∃ k : Fin t, i = Fin.castAdd (s + 1) (Fin.natAdd m k)) ∨
        i = Fin.natAdd (m + t) 0 ∨ ∃ l : Fin s, i = Fin.natAdd (m + t) l.succ := by
  refine Fin.addCases (fun i₁ => ?_) (fun i₂ => ?_) i
  · refine Fin.addCases (fun j => ?_) (fun k => ?_) i₁
    · exact Or.inl ⟨j, rfl⟩
    · exact Or.inr (Or.inl ⟨k, rfl⟩)
  · refine Fin.cases ?_ (fun l => ?_) i₂
    · exact Or.inr (Or.inr (Or.inl rfl))
    · exact Or.inr (Or.inr (Or.inr ⟨l, rfl⟩))

/-- In the polynomial picture of a regular system of parameters, the variable `X_i` goes to the
initial form of the `i`-th parameter (which has order `1`, the system being a basis of `M/M²`). -/
theorem gradedSemiModel_X_eq_initialForm {A : Type u} [CommRing A] [IsRegularLocalRing A]
    {K : Type u} [Field K] (ρ : K ≃+* A ⧸ maximalIdeal A) {n : ℕ} (v : Fin n → A)
    (hspan : Ideal.span (Set.range v) = maximalIdeal A)
    (hdim : (n : WithBot ℕ∞) = ringKrullDim A) (i : Fin n) :
    (gradedSemiModel ρ v hspan hdim).Φ (X i) = initialForm (maximalIdeal A) (v i) := by
  have hmk := gradedSemiModel_X ρ v hspan hdim i
  have hne : AssocGraded.mk (maximalIdeal A) 1 (v i) (mem_pow_one_of_span_eq hspan i) ≠ 0 := by
    rw [← hmk]
    intro h0
    exact X_ne_zero i ((gradedSemiModel ρ v hspan hdim).Φ.injective (h0.trans (map_zero _).symm))
  rw [hmk]
  exact ((Ideal.ordElem_eq_of_mk_ne_zero _ (mem_pow_one_of_span_eq hspan i) hne).2).symm

/-- A change of a family `a` of generators by an invertible matrix `C`, corrected by a family `d`
of elements of the ideal generated by `X`, does not change the ideal generated by `X` and the
family. -/
theorem span_union_range_mulVec_add {A : Type*} [CommRing A] {t : ℕ} (X : Set A)
    (a d : Fin t → A) (C : Matrix (Fin t) (Fin t) A) (hC : IsUnit C)
    (hd : ∀ k, d k ∈ Ideal.span X) :
    Ideal.span (X ∪ Set.range (C *ᵥ a + d)) = Ideal.span (X ∪ Set.range a) := by
  have key : ∀ (B : Matrix (Fin t) (Fin t) A) (a' d' : Fin t → A), (∀ k, d' k ∈ Ideal.span X) →
      ∀ k, (B *ᵥ a' + d') k ∈ Ideal.span (X ∪ Set.range a') := by
    intro B a' d' hd' k
    rw [Pi.add_apply, Matrix.mulVec, dotProduct]
    exact add_mem (Ideal.sum_mem _ fun l _ =>
      Ideal.mul_mem_left _ _ (Ideal.subset_span (Or.inr ⟨l, rfl⟩)))
      ((Ideal.span_mono Set.subset_union_left) (hd' k))
  apply le_antisymm
  · rw [Ideal.span_le]
    rintro _ (h | ⟨k, rfl⟩)
    · exact Ideal.subset_span (Or.inl h)
    · exact key C a d hd k
  · obtain ⟨u, rfl⟩ := hC
    have ha : a = (↑u⁻¹ : Matrix (Fin t) (Fin t) A) *ᵥ ((↑u : Matrix (Fin t) (Fin t) A) *ᵥ a + d) +
        -((↑u⁻¹ : Matrix (Fin t) (Fin t) A) *ᵥ d) := by
      rw [Matrix.mulVec_add, Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]
      abel
    rw [Ideal.span_le]
    rintro _ (h | ⟨k, rfl⟩)
    · exact Ideal.subset_span (Or.inl h)
    · rw [congrFun ha k]
      refine key _ _ _ (fun k => neg_mem ?_) k
      rw [Matrix.mulVec, dotProduct]
      exact Ideal.sum_mem _ fun l _ => Ideal.mul_mem_left _ _ (hd l)

/-- `span_union_range_mulVec_add` for a family placed between two sets of generators. -/
theorem span_union_range_mulVec_add' {A : Type*} [CommRing A] {t : ℕ} (X Y : Set A)
    (a d : Fin t → A) (C : Matrix (Fin t) (Fin t) A) (hC : IsUnit C)
    (hd : ∀ k, d k ∈ Ideal.span (X ∪ Y)) :
    Ideal.span (X ∪ Set.range (C *ᵥ a + d) ∪ Y) = Ideal.span (X ∪ Set.range a ∪ Y) := by
  rw [Set.union_right_comm X (Set.range (C *ᵥ a + d)) Y, Set.union_right_comm X (Set.range a) Y]
  exact span_union_range_mulVec_add _ a d C hC hd

/-- The range of `Fin.append`. -/
theorem range_fin_append {α : Type*} {m n : ℕ} (a : Fin m → α) (b : Fin n → α) :
    Set.range (Fin.append a b) = Set.range a ∪ Set.range b := by
  ext x
  constructor
  · rintro ⟨i, rfl⟩
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · exact Or.inl ⟨j, by simp⟩
    · exact Or.inr ⟨j, by simp⟩
  · rintro (⟨j, rfl⟩ | ⟨j, rfl⟩)
    · exact ⟨Fin.castAdd n j, by simp⟩
    · exact ⟨Fin.natAdd m j, by simp⟩

section Coordinates

variable {R : Type u} [CommRing R] [IsRegularLocalRing R] [IsDomain R] (D : WeierstrassDatum R)
  {P : Ideal R} [P.IsPrime] [IsRegularLocalRing (R ⧸ P)] {T : MonoidalTransform R P}
  [IsLocalHom T.toRing] [IsRegularLocalRing T.ring]

/-- The composite `S₀ → S → R`. -/
noncomputable abbrev WeierstrassDatum.algR : D.F0.S →+* R :=
  (algebraMap D.F.S R).comp (algebraMap D.F0.S D.F.S)

omit [IsDomain R] in
theorem WeierstrassDatum.range_coordV_composite (a : D.F0.S) {t s : ℕ} (xs : Fin t → D.F0.S)
    (ys : Fin s → D.F0.S) : Set.range (coordV (F := D.compositeFrame) a xs ys) =
      Set.range (Fin.snoc D.F.z D.wR : Fin (D.F.r + 1) → R) ∪ Set.range (fun k => D.algR (xs k)) ∪
        ({D.algR a} ∪ Set.range (fun l => D.algR (ys l))) := by
  change Set.range (Fin.append (Fin.append (Fin.snoc D.F.z D.wR : Fin (D.F.r + 1) → R)
    (fun k => D.algR (xs k))) (Fin.cons (D.algR a) (fun l => D.algR (ys l)))) = _
  rw [range_fin_append, range_fin_append, Fin.range_cons, Set.insert_eq]

omit [IsRegularLocalRing (R ⧸ P)] [IsLocalHom T.toRing] in
theorem WeierstrassDatum.range_coordV₁_composite (FT' : D.F.FrameTransform T)
    (FT0 : D.F0.FrameTransform FT'.TS) (y : D.F0.S)
    (hx : FT'.x = T.toRing (algebraMap D.F.S R (algebraMap D.F0.S D.F.S y)))
    (hx0 : FT0.x = FT'.TS.toRing (algebraMap D.F0.S D.F.S y)) {t s : ℕ} (ys : Fin s → D.F0.S)
    (u : Fin t → T.ring) :
    Set.range (coordV₁ (D.compositeFrameTransform FT' FT0 y hx hx0) ys u) =
      Set.range (Fin.snoc FT'.w (D.transform FT' FT0).wR : Fin (D.F.r + 1) → T.ring) ∪
        Set.range u ∪ ({FT'.x} ∪ Set.range (fun l => T.toRing (D.algR (ys l)))) := by
  change Set.range (Fin.append (Fin.append
    (Fin.snoc FT'.w (D.transform FT' FT0).wR : Fin (D.F.r + 1) → T.ring) u)
    (Fin.cons FT'.x (fun l => T.toRing (D.algR (ys l))))) = _
  rw [range_fin_append, range_fin_append, Fin.range_cons, Set.insert_eq]

/-- **The coordinates of (ii) of (c) of Lemma 25** (pp. 271--272): "a minimal base
`(y₁, ⋯, y_i)` of `Q₀` in such a way that `y = y_i` and `ȳ_j = y_j/y ∈ M₁` for `1 ≤ j ≤ i − 1`
[…] Let `b = i − 1`.  Let us choose a regular system of parameters `(y₁, ⋯, y_b, y, x₁, ⋯, x_a)`
of `S₀`.  Then `(z₁, ⋯, z_r, w, y₁, ⋯, y_b, y, x₁, ⋯, x_a)` is a regular system of parameters of
`R`, and `(z̄₁, ⋯, z̄_r, w̄, ȳ₁, ⋯, ȳ_b, y, x₁, ⋯, x_a)` is a regular system of parameters of `R₁`."

The fields: `t = b` and the elements `xs = (y₁, …, y_b)` of `S₀` (the minimal base of `Q₀ = P ∩ S₀`
besides `y`), `s = a` and `ys = (x₁, …, x_a)`, the quotients `u' = (ȳ₁, …, ȳ_b)` in `S₀₁` (their
images in `R₁` are the `ȳ_j = y_j/y`: `mul_u`), the regular systems of parameters of `S₀`, `S₀₁`,
`R` (`coordV` of the composite frame `(S₀; z, w)`: `(z, w, y_j, y, x_k)`) and `R₁` (`coordV₁` of its
frame transform: `(z̄, w̄, ȳ_j, y, x_k)`), and `P = (z, w, y₁, …, y_b, y)R`.  (The names `xs`, `ys`
are those of Lemma 21, whose coordinates these are: `(w, y₁, …, y_b)` there play the role of
`(x₁, …, x_t)` and `y` that of `x`.) -/
structure WeierstrassDatum.AdaptedCoords (FT' : D.F.FrameTransform T)
    (FT0 : D.F0.FrameTransform FT'.TS) (y : D.F0.S)
    (hx : FT'.x = T.toRing (algebraMap D.F.S R (algebraMap D.F0.S D.F.S y)))
    (hx0 : FT0.x = FT'.TS.toRing (algebraMap D.F0.S D.F.S y)) (t s : ℕ) where
  /-- `(y₁, …, y_b)` (`b = t`; `a = s`). -/
  xs : Fin t → D.F0.S
  /-- `(x₁, …, x_a)`. -/
  ys : Fin s → D.F0.S
  /-- `(ȳ₁, …, ȳ_b)`, in `S₀₁`. -/
  u' : Fin t → FT0.TS.ring
  /-- `(y₁, …, y_b, y, x₁, …, x_a)` generates the maximal ideal of `S₀`. -/
  span_S : Ideal.span ({y} ∪ Set.range xs ∪ Set.range ys : Set D.F0.S) = maximalIdeal D.F0.S
  /-- `(ȳ₁, …, ȳ_b, y, x₁, …, x_a)` generates the maximal ideal of `S₀₁`. -/
  span_S₁ : Ideal.span ({FT0.TS.toRing y} ∪ Set.range u' ∪
      Set.range (fun l => FT0.TS.toRing (ys l)) : Set FT0.TS.ring) = maximalIdeal FT0.TS.ring
  /-- `y_j = y ȳ_j` in `R₁`. -/
  mul_u : ∀ k, T.toRing (algebraMap D.F.S R (algebraMap D.F0.S D.F.S (xs k))) =
    FT'.x * FT'.β (FT0.β (u' k))
  /-- `(z, w, y₁, …, y_b, y, x₁, …, x_a)` generates the maximal ideal of `R`. -/
  span_R : Ideal.span (Set.range (coordV (F := D.compositeFrame) y xs ys)) = maximalIdeal R
  dim_R : (((D.compositeFrame.r + t) + (s + 1) : ℕ) : WithBot ℕ∞) = ringKrullDim R
  /-- `(z̄, w̄, ȳ₁, …, ȳ_b, y, x₁, …, x_a)` generates the maximal ideal of `R₁`. -/
  span_R₁ : Ideal.span (Set.range (coordV₁ (D.compositeFrameTransform FT' FT0 y hx hx0) ys
    (fun k => (FT'.β.comp FT0.β) (u' k)))) = maximalIdeal T.ring
  dim_R₁ : (((D.compositeFrame.r + t) + (s + 1) : ℕ) : WithBot ℕ∞) = ringKrullDim T.ring
  /-- `P = (z, w, y₁, …, y_b, y)R`. -/
  P_eq : P = Ideal.span (Set.range (Fin.append (Fin.snoc D.F.z D.wR : Fin (D.F.r + 1) → R)
    (fun k => D.algR (xs k))) ∪ {D.algR y})

attribute [local instance] RegularFrame.isDomain_S

/-- **The coordinates of (ii) of (c) of Lemma 25 exist** (pp. 271--272: "Let us choose a minimal
base `(y₁, ⋯, y_i)` of `Q₀` in such a way that `y = y_i` and `ȳ_j = y_j/y ∈ M₁` […] Let us choose a
regular system of parameters `(y₁, ⋯, y_b, y, x₁, ⋯, x_a)` of `S₀`.  Then […] is a regular system of
parameters of `R`, and […] of `R₁`"), for `R₁` residually rational over `R`.

Gaps filled (the paper says "Then …"): the coordinates of Lemma 21
(`RegularFrame.FrameTransform.exists_coordinates_spans`) for the composite regular frame
`(S₀; z₁, …, z_r, w)` of `R` (`R/(z, w)R ≅ S₀`, `WeierstrassDatum.quot_bijective_snoc`) and its
frame transform `(S₀₁; z̄, w̄)` in `R₁` with denominator `y`
(`WeierstrassDatum.compositeFrameTransform`):
the minimal base `(x₀, y₁, …, y_b)` of `Q₀` with `y_j/x₀ ∈ M₁` exists for a residually rational
monoidal transform (`MonoidalTransform.exists_rsop_of_isResiduallyRational`) and `x₀` is replaced by
`y`, which generates `Q₀S₀₁` up to a unit. -/
theorem WeierstrassDatum.exists_adaptedCoords
    (hrat : RingHom.IsResiduallyRational (R := R) (R' := T.ring) T.toRing)
    (y : D.F0.S) (FT' : D.F.FrameTransform T) (FT0 : D.F0.FrameTransform FT'.TS)
    (hyP : algebraMap D.F.S R (algebraMap D.F0.S D.F.S y) ∈ P)
    (hx : FT'.x = T.toRing (algebraMap D.F.S R (algebraMap D.F0.S D.F.S y)))
    (hx0 : FT0.x = FT'.TS.toRing (algebraMap D.F0.S D.F.S y)) :
    ∃ t s : ℕ, Nonempty (D.AdaptedCoords FT' FT0 y hx hx0 t s) := by
  obtain ⟨t', s, xs, ys, u, u', hu, hS, hS₁, hxs, hspanR, hdimR, hspanR₁, hdimR₁, hPeq⟩ :=
    (D.compositeFrameTransform FT' FT0 y hx hx0).exists_coordinates_spans hrat y hyP hx
  have hu' : u = fun k => (FT'.β.comp FT0.β) (u' k) := funext hu
  subst hu'
  exact ⟨t', s, ⟨⟨xs, ys, u', hS, hS₁, hxs, hspanR, hdimR, hspanR₁, hdimR₁, hPeq⟩⟩⟩

namespace WeierstrassDatum.AdaptedCoords

variable {D} {FT' : D.F.FrameTransform T} {FT0 : D.F0.FrameTransform FT'.TS} {y : D.F0.S}
  {hx : FT'.x = T.toRing (algebraMap D.F.S R (algebraMap D.F0.S D.F.S y))}
  {hx0 : FT0.x = FT'.TS.toRing (algebraMap D.F0.S D.F.S y)}
  {t s : ℕ} (c : D.AdaptedCoords FT' FT0 y hx hx0 t s)

omit [P.IsPrime] [IsRegularLocalRing (R ⧸ P)] [IsLocalHom T.toRing] [IsRegularLocalRing T.ring] in
/-- `β ∘ (S₀ → S₀₁) = (R → R₁) ∘ (S₀ → R)`. -/
theorem β_toRing (a : D.F0.S) : FT'.β (FT0.β (FT0.TS.toRing a)) =
    T.toRing (algebraMap D.F.S R (algebraMap D.F0.S D.F.S a)) := by
  have h1 : FT0.β (FT0.TS.toRing a) = FT'.TS.toRing (algebraMap D.F0.S D.F.S a) :=
    RingHom.congr_fun FT0.canonical.comm a
  rw [h1]
  exact RingHom.congr_fun FT'.canonical.comm _

section Recoord

variable (C : Matrix (Fin t) (Fin t) D.F0.S) (hC : IsUnit C) (v : Fin t → D.F0.S)
  (hv : ∀ k, v k ∈ Ideal.span ({y} ∪ Set.range c.ys))

/-- The new `y_j`: `∑_l C_{jl} y_l + v_j y`. -/
noncomputable def newXs : Fin t → D.F0.S := C *ᵥ c.xs + fun k => v k * y

/-- The new `ȳ_j`: `∑_l C_{jl} ȳ_l + v_j`. -/
noncomputable def newU : Fin t → FT0.TS.ring :=
  (C.map FT0.TS.toRing) *ᵥ c.u' + fun k => FT0.TS.toRing (v k)

omit [IsRegularLocalRing (R ⧸ P)] [IsLocalHom T.toRing] in
include hC in
theorem recoord_span_S :
    Ideal.span ({y} ∪ Set.range (c.newXs C v) ∪ Set.range c.ys : Set D.F0.S) =
      maximalIdeal D.F0.S := by
  rw [← c.span_S]
  exact span_union_range_mulVec_add' _ _ c.xs _ C hC fun k =>
    Ideal.mul_mem_left _ _ (Ideal.subset_span (Or.inl rfl))

omit [IsRegularLocalRing (R ⧸ P)] [IsLocalHom T.toRing] in
include hC hv in
theorem recoord_span_S₁ :
    Ideal.span ({FT0.TS.toRing y} ∪ Set.range (c.newU C v) ∪
        Set.range (fun l => FT0.TS.toRing (c.ys l)) : Set FT0.TS.ring) =
      maximalIdeal FT0.TS.ring := by
  rw [← c.span_S₁]
  refine span_union_range_mulVec_add' _ _ c.u' _ _ (hC.map (RingHom.mapMatrix FT0.TS.toRing))
    fun k => ?_
  have h := Ideal.mem_map_of_mem FT0.TS.toRing (hv k)
  rw [Ideal.map_span] at h
  refine (Ideal.span_mono ?_) h
  rintro _ ⟨a, (rfl | ⟨l, rfl⟩), rfl⟩
  · exact Or.inl rfl
  · exact Or.inr ⟨l, rfl⟩

omit [IsRegularLocalRing (R ⧸ P)] [IsLocalHom T.toRing] in
theorem recoord_mul_u (k : Fin t) :
    T.toRing (algebraMap D.F.S R (algebraMap D.F0.S D.F.S (c.newXs C v k))) =
      FT'.x * FT'.β (FT0.β (c.newU C v k)) := by
  simp only [newXs, newU, Pi.add_apply, Matrix.mulVec, dotProduct, Matrix.map_apply, map_add,
    map_sum, map_mul, β_toRing]
  rw [mul_add, Finset.mul_sum]
  congr 1
  · refine Finset.sum_congr rfl fun l _ => ?_
    rw [c.mul_u l]
    ring
  · rw [← hx]
    ring

omit [IsRegularLocalRing (R ⧸ P)] [IsLocalHom T.toRing] in
theorem recoord_algR_xs :
    (fun k => D.algR (c.newXs C v k)) =
      (C.map D.algR) *ᵥ (fun k => D.algR (c.xs k)) + fun k => D.algR (v k) * D.algR y := by
  funext k
  simp only [newXs, Pi.add_apply, Matrix.mulVec, dotProduct, Matrix.map_apply, map_add, map_sum,
    map_mul]

omit [IsRegularLocalRing (R ⧸ P)] [IsLocalHom T.toRing] in
include hC in
theorem recoord_span_R :
    Ideal.span (Set.range (coordV (F := D.compositeFrame) y (c.newXs C v) c.ys)) =
      maximalIdeal R := by
  have h := c.span_R
  rw [D.range_coordV_composite] at h ⊢
  rw [← h, recoord_algR_xs]
  exact span_union_range_mulVec_add' _ _ (fun k => D.algR (c.xs k)) _ (C.map D.algR)
    (hC.map (RingHom.mapMatrix D.algR)) fun k =>
    Ideal.mul_mem_left _ _ (Ideal.subset_span (Or.inr (Or.inl rfl)))

omit [IsRegularLocalRing (R ⧸ P)] [IsLocalHom T.toRing] in
include hC hv in
theorem recoord_span_R₁ :
    Ideal.span (Set.range (coordV₁ (D.compositeFrameTransform FT' FT0 y hx hx0) c.ys
      (fun k => (FT'.β.comp FT0.β) (c.newU C v k)))) = maximalIdeal T.ring := by
  have h := c.span_R₁
  rw [D.range_coordV₁_composite] at h ⊢
  rw [← h]
  have hu' : (fun k => (FT'.β.comp FT0.β) (c.newU C v k)) =
      (C.map (T.toRing.comp D.algR)) *ᵥ (fun k => (FT'.β.comp FT0.β) (c.u' k)) +
        fun k => T.toRing (D.algR (v k)) := by
    funext k
    simp only [newU, Pi.add_apply, Matrix.mulVec, dotProduct, Matrix.map_apply, map_add, map_sum,
      map_mul, β_toRing, RingHom.comp_apply]
  rw [hu']
  refine span_union_range_mulVec_add' _ _ _ _ _
    (hC.map (RingHom.mapMatrix (T.toRing.comp D.algR))) fun k => ?_
  have h := Ideal.mem_map_of_mem (T.toRing.comp D.algR) (hv k)
  rw [Ideal.map_span] at h
  refine (Ideal.span_mono ?_) h
  rintro _ ⟨a, (rfl | ⟨l, rfl⟩), rfl⟩
  · exact Or.inr (Or.inl hx.symm)
  · exact Or.inr (Or.inr ⟨l, rfl⟩)

omit [IsRegularLocalRing (R ⧸ P)] [IsLocalHom T.toRing] in
include hC in
theorem recoord_P_eq :
    P = Ideal.span (Set.range (Fin.append (Fin.snoc D.F.z D.wR : Fin (D.F.r + 1) → R)
      (fun k => D.algR (c.newXs C v k))) ∪ {D.algR y}) := by
  refine c.P_eq.trans ?_
  rw [range_fin_append, range_fin_append, recoord_algR_xs]
  symm
  exact span_union_range_mulVec_add' (Set.range (Fin.snoc D.F.z D.wR : Fin (D.F.r + 1) → R))
    {D.algR y} (fun k => D.algR (c.xs k)) (fun k => D.algR (v k) * D.algR y) (C.map D.algR)
    (hC.map (RingHom.mapMatrix D.algR)) fun k =>
    Ideal.mul_mem_left _ _ (Ideal.subset_span (Or.inr rfl))

/-- **Change of coordinates** `y_j ↦ ∑_l C_{jl} y_l + v_j y` (`C` an invertible matrix over `S₀`,
`v_j` in the ideal `(y, x₁, …, x_a)` of `S₀`); the quotients become `ȳ_j ↦ ∑_l C_{jl} ȳ_l + v_j`.
This is the form of the two normalizations of (ii) of (c) (pp. 271--272): "we may assume that
`(w, y₁, ⋯, y_τ)` is a regular system of `τ_{(z)}`-parameters" (`v = 0`) and "We may replace `y_j`
by `y_j + v_j y` for `1 ≤ j ≤ τ` without affecting any of the assumptions on `(y₁, ⋯, y_b)`"
(`C = 1`). -/
noncomputable def recoord : D.AdaptedCoords FT' FT0 y hx hx0 t s :=
  ⟨c.newXs C v, c.ys, c.newU C v,
    c.recoord_span_S C hC v, c.recoord_span_S₁ C hC v hv, c.recoord_mul_u C v,
    c.recoord_span_R C hC v, c.dim_R, c.recoord_span_R₁ C hC v hv, c.dim_R₁,
    c.recoord_P_eq C hC v⟩

end Recoord

section Models

attribute [local instance] Ideal.Quotient.field

/-- The number `r + 1 + b + 1 + a` of variables. -/
noncomputable abbrev n (_c : D.AdaptedCoords FT' FT0 y hx hx0 t s) : ℕ :=
  (D.compositeFrame.r + t) + (s + 1)

/-- The index of `Z_j`. -/
noncomputable abbrev zI (_c : D.AdaptedCoords FT' FT0 y hx hx0 t s) (j : Fin D.F.r) :
    Fin ((D.compositeFrame.r + t) + (s + 1)) :=
  Fin.castAdd (s + 1) (Fin.castAdd t (Fin.castSucc j : Fin (D.F.r + 1)))

/-- The index of `W`. -/
noncomputable abbrev wI (_c : D.AdaptedCoords FT' FT0 y hx hx0 t s) :
    Fin ((D.compositeFrame.r + t) + (s + 1)) :=
  Fin.castAdd (s + 1) (Fin.castAdd t (Fin.last D.F.r : Fin (D.F.r + 1)))

/-- The index of `Y_j`. -/
noncomputable abbrev yI (_c : D.AdaptedCoords FT' FT0 y hx hx0 t s) (k : Fin t) :
    Fin ((D.compositeFrame.r + t) + (s + 1)) :=
  Fin.castAdd (s + 1) (Fin.natAdd D.compositeFrame.r k)

/-- The set `U` of the indices of `Z, W, Y₁, …, Y_b`. -/
noncomputable def U (_c : D.AdaptedCoords FT' FT0 y hx hx0 t s) :
    Set (Fin ((D.compositeFrame.r + t) + (s + 1))) := {i | i.val < D.compositeFrame.r + t}

/-- The elements `y_j`, `y`, `x_k` of `S₀` of the variables other than `Z`, `W`. -/
noncomputable def sF : Fin c.n → D.F0.S :=
  Fin.append (Fin.append (fun _ : Fin D.compositeFrame.r => (0 : D.F0.S)) c.xs) (Fin.cons y c.ys)

/-- The elements `ȳ_j`, `y`, `x_k` of `S₀₁` of the variables other than `Z̄`, `W̄`. -/
noncomputable def s₁F : Fin c.n → FT0.TS.ring :=
  Fin.append (Fin.append (fun _ : Fin D.compositeFrame.r => (0 : FT0.TS.ring)) c.u')
    (Fin.cons (FT0.TS.toRing y) (fun l => FT0.TS.toRing (c.ys l)))

/-- `gr_M(R) = k[Z, W, Y₁, …, Y_b, Y, X₁, …, X_a]` (p. 272), over `k = R₁/M₁` through `ρ`. -/
noncomputable def modelR (ρ : T.ring ⧸ maximalIdeal T.ring ≃+* R ⧸ maximalIdeal R) :
    SemiModel (T.ring ⧸ maximalIdeal T.ring) (R ⧸ maximalIdeal R) (AssocGraded (maximalIdeal R))
      c.n :=
  gradedSemiModel ρ (coordV (F := D.compositeFrame) y c.xs c.ys) c.span_R c.dim_R

/-- `gr_{M₁}(R₁) = k[Z̄, W̄, Ȳ₁, …, Ȳ_b, Y, X₁, …, X_a]` (p. 272). -/
noncomputable def modelT :
    SemiModel (T.ring ⧸ maximalIdeal T.ring) (T.ring ⧸ maximalIdeal T.ring)
      (AssocGraded (maximalIdeal T.ring)) c.n :=
  gradedSemiModel (RingEquiv.refl _) (coordV₁ (D.compositeFrameTransform FT' FT0 y hx hx0) c.ys
    (fun k => (FT'.β.comp FT0.β) (c.u' k))) c.span_R₁ c.dim_R₁

omit [IsRegularLocalRing (R ⧸ P)] [IsLocalHom T.toRing] in
theorem zI_val (j : Fin D.F.r) : (c.zI j).val = j.val := rfl

omit [IsRegularLocalRing (R ⧸ P)] [IsLocalHom T.toRing] in
theorem wI_val : c.wI.val = D.F.r := rfl

omit [IsRegularLocalRing (R ⧸ P)] [IsLocalHom T.toRing] in
theorem yI_val (k : Fin t) : (c.yI k).val = D.F.r + 1 + k.val := rfl

omit [IsRegularLocalRing (R ⧸ P)] [IsLocalHom T.toRing] in
theorem zI_injective : Function.Injective c.zI := fun a b h => by
  have h1 : (c.zI a).val = (c.zI b).val := congrArg Fin.val h
  rw [zI_val, zI_val] at h1
  exact Fin.ext h1

omit [IsRegularLocalRing (R ⧸ P)] [IsLocalHom T.toRing] in
theorem wI_notMem : c.wI ∉ Set.range c.zI := by
  rintro ⟨j, hj⟩
  have h1 := congrArg Fin.val hj
  rw [zI_val, wI_val] at h1
  have := j.2
  omega

omit [IsRegularLocalRing (R ⧸ P)] [IsLocalHom T.toRing] in
theorem yI_injective : Function.Injective c.yI := fun a b h => by
  have h1 : (c.yI a).val = (c.yI b).val := congrArg Fin.val h
  rw [yI_val, yI_val] at h1
  exact Fin.ext (by omega)

omit [IsRegularLocalRing (R ⧸ P)] [IsLocalHom T.toRing] in
theorem range_zI_subset_U : Set.range c.zI ⊆ c.U := by
  rintro _ ⟨j, rfl⟩
  show (c.zI j).val < D.compositeFrame.r + t
  rw [zI_val]
  have := j.2
  show j.val < D.F.r + 1 + t
  omega

omit [IsRegularLocalRing (R ⧸ P)] [IsLocalHom T.toRing] in
theorem wI_mem_U : c.wI ∈ c.U := by
  show c.wI.val < D.F.r + 1 + t
  rw [wI_val]
  omega

omit [IsRegularLocalRing (R ⧸ P)] [IsLocalHom T.toRing] in
theorem yI_mem_U (k : Fin t) : c.yI k ∈ c.U := by
  show (c.yI k).val < D.F.r + 1 + t
  rw [yI_val]
  omega

omit [IsRegularLocalRing (R ⧸ P)] [IsLocalHom T.toRing] in
/-- The indices of `U` are those of `Z`, `W` and the `Y_j`. -/
theorem mem_U_iff (i : Fin c.n) :
    i ∈ c.U ↔ i ∈ Set.range c.zI ∨ i = c.wI ∨ i ∈ Set.range c.yI := by
  have hr : D.compositeFrame.r = D.F.r + 1 := rfl
  constructor
  · intro hi
    have hi' : i.val < D.F.r + 1 + t := hi
    rcases fin_split_three i with ⟨j, rfl⟩ | ⟨k, rfl⟩ | rfl | ⟨l, rfl⟩
    · rcases Fin.eq_castSucc_or_eq_last (n := D.F.r) j with ⟨j'', hj⟩ | hj
      · exact Or.inl ⟨j'', by simp [zI, hj]⟩
      · exact Or.inr (Or.inl (by simp [wI, hj]))
    · exact Or.inr (Or.inr ⟨k, rfl⟩)
    · simp at hi'; omega
    · simp at hi'; omega
  · rintro (h | rfl | ⟨k, rfl⟩)
    · exact c.range_zI_subset_U h
    · exact c.wI_mem_U
    · exact c.yI_mem_U k

omit [IsRegularLocalRing (R ⧸ P)] [IsLocalHom T.toRing] in
theorem other_iff (i : Fin c.n) : (i ∉ Set.range c.zI ∧ i ≠ c.wI) ↔ D.F.r + 1 ≤ i.val := by
  have hr : D.compositeFrame.r = D.F.r + 1 := rfl
  constructor
  · rintro ⟨h1, h2⟩
    by_contra hlt
    rcases fin_split_three i with ⟨j, rfl⟩ | ⟨k, rfl⟩ | rfl | ⟨l, rfl⟩
    · rcases Fin.eq_castSucc_or_eq_last (n := D.F.r) j with ⟨j'', hj⟩ | hj
      · exact h1 ⟨j'', by simp [zI, hj]⟩
      · exact h2 (by simp [wI, hj])
    · simp at hlt; omega
    · simp at hlt; omega
    · simp at hlt; omega
  · intro h
    refine ⟨?_, ?_⟩
    · rintro ⟨j, rfl⟩
      rw [zI_val] at h
      have := j.2
      omega
    · rintro rfl
      rw [wI_val] at h
      omega

omit [IsRegularLocalRing (R ⧸ P)] [IsLocalHom T.toRing] in
theorem coordV_zI (j : Fin D.F.r) :
    coordV (F := D.compositeFrame) y c.xs c.ys (c.zI j) = D.F.z j := by
  simp [coordV, zI, WeierstrassDatum.compositeFrame]

omit [IsRegularLocalRing (R ⧸ P)] [IsLocalHom T.toRing] in
theorem coordV_wI : coordV (F := D.compositeFrame) y c.xs c.ys c.wI = D.wR := by
  simp [coordV, wI, WeierstrassDatum.compositeFrame]

omit [IsRegularLocalRing (R ⧸ P)] [IsLocalHom T.toRing] in
theorem coordV_yI (k : Fin t) :
    coordV (F := D.compositeFrame) y c.xs c.ys (c.yI k) = D.algR (c.xs k) := by
  simp only [coordV, yI, Fin.append_left, Fin.append_right]
  rfl

omit [IsRegularLocalRing (R ⧸ P)] [IsLocalHom T.toRing] in
theorem coordV_other (i : Fin c.n) (hi : D.F.r + 1 ≤ i.val) :
    coordV (F := D.compositeFrame) y c.xs c.ys i = D.algR (c.sF i) := by
  have hr : D.compositeFrame.r = D.F.r + 1 := rfl
  rcases fin_split_three i with ⟨j, rfl⟩ | ⟨k, rfl⟩ | rfl | ⟨l, rfl⟩
  · have := j.2
    simp at hi
    omega
  · simp only [coordV, sF, Fin.append_left, Fin.append_right]
    rfl
  · simp only [coordV, sF, Fin.append_right, Fin.cons_zero]
    rfl
  · simp only [coordV, sF, Fin.append_right, Fin.cons_succ]
    rfl

omit [IsRegularLocalRing (R ⧸ P)] [IsLocalHom T.toRing] in
theorem coordV₁_zI (j : Fin D.F.r) : coordV₁ (D.compositeFrameTransform FT' FT0 y hx hx0) c.ys
    (fun k => (FT'.β.comp FT0.β) (c.u' k)) (c.zI j) = FT'.w j := by
  simp [coordV₁, zI, WeierstrassDatum.compositeFrameTransform, WeierstrassDatum.compositeFrame]

omit [IsRegularLocalRing (R ⧸ P)] [IsLocalHom T.toRing] in
theorem coordV₁_wI : coordV₁ (D.compositeFrameTransform FT' FT0 y hx hx0) c.ys
    (fun k => (FT'.β.comp FT0.β) (c.u' k)) c.wI = (D.transform FT' FT0).wR := by
  simp [coordV₁, wI, WeierstrassDatum.compositeFrameTransform, WeierstrassDatum.compositeFrame]

omit [IsRegularLocalRing (R ⧸ P)] [IsLocalHom T.toRing] in
theorem coordV₁_yI (k : Fin t) : coordV₁ (D.compositeFrameTransform FT' FT0 y hx hx0) c.ys
    (fun k => (FT'.β.comp FT0.β) (c.u' k)) (c.yI k) = FT'.β (FT0.β (c.u' k)) := by
  simp only [coordV₁, yI, Fin.append_left, Fin.append_right]
  rfl

omit [IsRegularLocalRing (R ⧸ P)] [IsLocalHom T.toRing] in
theorem coordV₁_other (i : Fin c.n) (hi : D.F.r + 1 ≤ i.val) :
    coordV₁ (D.compositeFrameTransform FT' FT0 y hx hx0) c.ys
      (fun k => (FT'.β.comp FT0.β) (c.u' k)) i = FT'.β (FT0.β (c.s₁F i)) := by
  have hr : D.compositeFrame.r = D.F.r + 1 := rfl
  rcases fin_split_three i with ⟨j, rfl⟩ | ⟨k, rfl⟩ | rfl | ⟨l, rfl⟩
  · have := j.2
    simp at hi
    omega
  · simp only [coordV₁, s₁F, Fin.append_left, Fin.append_right]
    rfl
  · simp only [coordV₁, s₁F, Fin.append_right, Fin.cons_zero]
    rw [β_toRing, ← hx]
    rfl
  · simp only [coordV₁, s₁F, Fin.append_right, Fin.cons_succ]
    rw [β_toRing]
    rfl

omit [IsRegularLocalRing (R ⧸ P)] [IsLocalHom T.toRing] in
/-- For the variables outside `U` (`Y`, `X₁, …, X_a`), the two coordinates are the same element of
`S₀`: `s₁F i` is the image of `sF i` and the coordinates are `x ∈ S₀` in `R` and in `R₁`. -/
theorem coordV₁_eq_toRing_coordV (i : Fin c.n) (hi : i ∉ c.U) :
    coordV₁ (D.compositeFrameTransform FT' FT0 y hx hx0) c.ys
      (fun k => (FT'.β.comp FT0.β) (c.u' k)) i =
      T.toRing (coordV (F := D.compositeFrame) y c.xs c.ys i) := by
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
  · simp only [coordV₁, coordV, Fin.append_right, Fin.cons_zero]
    exact hx
  · simp only [coordV₁, coordV, Fin.append_right, Fin.cons_succ]

omit [IsRegularLocalRing (R ⧸ P)] [IsLocalHom T.toRing] in
theorem sF_image_other : c.sF '' {i | i ∉ Set.range c.zI ∧ i ≠ c.wI} =
    {y} ∪ Set.range c.xs ∪ Set.range c.ys := by
  have hr : D.compositeFrame.r = D.F.r + 1 := rfl
  ext z
  constructor
  · rintro ⟨i, hi, rfl⟩
    have hi' := (c.other_iff i).mp hi
    rcases fin_split_three i with ⟨j, rfl⟩ | ⟨k, rfl⟩ | rfl | ⟨l, rfl⟩
    · have := j.2
      simp at hi'
      omega
    · exact Or.inl (Or.inr ⟨k, by simp only [sF, Fin.append_left, Fin.append_right]⟩)
    · exact Or.inl (Or.inl (by simp only [sF, Fin.append_right, Fin.cons_zero]; rfl))
    · exact Or.inr ⟨l, by simp only [sF, Fin.append_right, Fin.cons_succ]⟩
  · rintro ((rfl | ⟨k, rfl⟩) | ⟨l, rfl⟩)
    · refine ⟨Fin.natAdd (D.compositeFrame.r + t) 0, ?_, ?_⟩
      · refine (c.other_iff _).mpr ?_
        show D.F.r + 1 ≤ D.compositeFrame.r + t + 0
        omega
      · simp only [sF, Fin.append_right, Fin.cons_zero]
    · refine ⟨Fin.castAdd (s + 1) (Fin.natAdd D.compositeFrame.r k), ?_, ?_⟩
      · refine (c.other_iff _).mpr ?_
        show D.F.r + 1 ≤ D.compositeFrame.r + k
        omega
      · simp only [sF, Fin.append_left, Fin.append_right]
    · refine ⟨Fin.natAdd (D.compositeFrame.r + t) l.succ, ?_, ?_⟩
      · refine (c.other_iff _).mpr ?_
        show D.F.r + 1 ≤ D.compositeFrame.r + t + (l + 1)
        omega
      · simp only [sF, Fin.append_right, Fin.cons_succ]

omit [IsRegularLocalRing (R ⧸ P)] [IsLocalHom T.toRing] in
theorem s₁F_image_other : c.s₁F '' {i | i ∉ Set.range c.zI ∧ i ≠ c.wI} =
    {FT0.TS.toRing y} ∪ Set.range c.u' ∪ Set.range (fun l => FT0.TS.toRing (c.ys l)) := by
  have hr : D.compositeFrame.r = D.F.r + 1 := rfl
  ext z
  constructor
  · rintro ⟨i, hi, rfl⟩
    have hi' := (c.other_iff i).mp hi
    rcases fin_split_three i with ⟨j, rfl⟩ | ⟨k, rfl⟩ | rfl | ⟨l, rfl⟩
    · have := j.2
      simp at hi'
      omega
    · exact Or.inl (Or.inr ⟨k, by simp only [s₁F, Fin.append_left, Fin.append_right]⟩)
    · exact Or.inl (Or.inl (by
        simp only [s₁F, Fin.append_right, Fin.cons_zero]; exact Set.mem_singleton _))
    · exact Or.inr ⟨l, by simp only [s₁F, Fin.append_right, Fin.cons_succ]⟩
  · rintro ((rfl | ⟨k, rfl⟩) | ⟨l, rfl⟩)
    · refine ⟨Fin.natAdd (D.compositeFrame.r + t) 0, ?_, ?_⟩
      · refine (c.other_iff _).mpr ?_
        show D.F.r + 1 ≤ D.compositeFrame.r + t + 0
        omega
      · simp only [s₁F, Fin.append_right, Fin.cons_zero]
    · refine ⟨Fin.castAdd (s + 1) (Fin.natAdd D.compositeFrame.r k), ?_, ?_⟩
      · refine (c.other_iff _).mpr ?_
        show D.F.r + 1 ≤ D.compositeFrame.r + k
        omega
      · simp only [s₁F, Fin.append_left, Fin.append_right]
    · refine ⟨Fin.natAdd (D.compositeFrame.r + t) l.succ, ?_, ?_⟩
      · refine (c.other_iff _).mpr ?_
        show D.F.r + 1 ≤ D.compositeFrame.r + t + (l + 1)
        omega
      · simp only [s₁F, Fin.append_right, Fin.cons_succ]

omit [IsRegularLocalRing (R ⧸ P)] [IsLocalHom T.toRing] in
/-- **The model `gr_M(R) = k[Z, W, Y₁, …, Y_b, Y, X₁, …, X_a]` is adapted to the datum** (p. 272:
"where `Z_j` (resp. `W`, resp. `Y_j`, resp. `Y`, resp. `X_j`) denotes the initial form of `z_j`
(resp. `w`, resp. `y_j`, resp. `y`, resp. `x_j`) in `gr_M(R)`"). -/
theorem isAdaptedModel (ρ : T.ring ⧸ maximalIdeal T.ring ≃+* R ⧸ maximalIdeal R) :
    D.IsAdaptedModel (c.modelR ρ) c.zI c.wI c.sF where
  graded := gradedSemiModel_hhom ρ (coordV (F := D.compositeFrame) y c.xs c.ys) c.span_R c.dim_R
  zI_injective := c.zI_injective
  wI_notMem := c.wI_notMem
  Φ_X_zI := fun j => by
    rw [modelR, gradedSemiModel_X_eq_initialForm, coordV_zI]; rfl
  Φ_X_wI := by
    rw [modelR, gradedSemiModel_X_eq_initialForm, coordV_wI]
  Φ_X_other := fun i hz hw => by
    rw [modelR, gradedSemiModel_X_eq_initialForm, c.coordV_other i ((c.other_iff i).mp ⟨hz, hw⟩)]
    rfl
  span_other := by
    rw [sF_image_other]
    exact c.span_S

omit [IsRegularLocalRing (R ⧸ P)] [IsLocalHom T.toRing] in
/-- **The model `gr_{M₁}(R₁) = k[Z̄, W̄, Ȳ₁, …, Ȳ_b, Y, X₁, …, X_a]` is adapted to the transformed
datum** (p. 272). -/
theorem isAdaptedModel_transform :
    (D.transform FT' FT0).IsAdaptedModel c.modelT c.zI c.wI c.s₁F where
  graded := gradedSemiModel_hhom (RingEquiv.refl (T.ring ⧸ maximalIdeal T.ring)) _ c.span_R₁
    c.dim_R₁
  zI_injective := c.zI_injective
  wI_notMem := c.wI_notMem
  Φ_X_zI := fun j =>
    (gradedSemiModel_X_eq_initialForm _ _ c.span_R₁ c.dim_R₁ (c.zI j)).trans
      (congrArg (initialForm (maximalIdeal T.ring)) (c.coordV₁_zI j))
  Φ_X_wI :=
    (gradedSemiModel_X_eq_initialForm _ _ c.span_R₁ c.dim_R₁ c.wI).trans
      (congrArg (initialForm (maximalIdeal T.ring)) c.coordV₁_wI)
  Φ_X_other := fun i hz hw =>
    (gradedSemiModel_X_eq_initialForm _ _ c.span_R₁ c.dim_R₁ i).trans
      (congrArg (initialForm (maximalIdeal T.ring))
        (c.coordV₁_other i ((c.other_iff i).mp ⟨hz, hw⟩)))
  span_other := (congrArg Ideal.span c.s₁F_image_other).trans c.span_S₁

/-- **The comparison of the initial forms** (p. 272): "`φ` is a form only in `Z₁, ⋯, Z_r, W,
Y₁, ⋯, Y_b`" (the variables of `U`), "and `φ̄ = φ(Z̄₁, ⋯, Z̄_r, W̄, Ȳ₁, ⋯) + φ̄*` with
`φ̄* ∈ (Y, X₁, ⋯, X_a) gr_{M₁}(R₁)`": for `f ∈ P^μ` of order `μ` and `g = y^{-μ} f` of order `μ`
(`forms_of_coordinates`, i.e. `forms_correspond`). -/
theorem forms (ρ : T.ring ⧸ maximalIdeal T.ring ≃+* R ⧸ maximalIdeal R)
    (hρ : (ρ.symm : R ⧸ maximalIdeal R →+* T.ring ⧸ maximalIdeal T.ring) =
      quotientMaximalIdealMap T.toRing)
    (μ : ℕ) (f : R) (g : T.ring) (hfP : f ∈ P ^ μ)
    (hford : Ideal.ordElem (maximalIdeal R) f = μ)
    (hgord : Ideal.ordElem (maximalIdeal T.ring) g = μ) (hgf : FT'.x ^ μ * g = T.toRing f) :
    (c.modelR ρ).Φ.symm (initialForm (maximalIdeal R) f) ∈
        MvPolynomial.supported (T.ring ⧸ maximalIdeal T.ring) c.U ∧
      c.modelT.Φ.symm (initialForm (maximalIdeal T.ring) g) -
          (c.modelR ρ).Φ.symm (initialForm (maximalIdeal R) f) ∈
        outIdeal (K := T.ring ⧸ maximalIdeal T.ring) c.U := by
  have hdom1 : IsDomain T.ring := Transforms.isDomain_of_isRegularLocalRing _
  have hFTx0 : FT'.x ≠ 0 := by
    intro h0
    have h1 : P.map T.toRing = ⊥ := by rw [← FT'.span_x, h0, Ideal.span_singleton_eq_bot]
    exact T.x_ne_zero (T.toRing_injective ((Ideal.mem_bot.mp
      (h1 ▸ Ideal.mem_map_of_mem T.toRing T.x_mem)).trans (map_zero _).symm))
  exact forms_of_coordinates (D.compositeFrameTransform FT' FT0 y hx hx0) y hx hFTx0 c.xs c.ys
    (fun k => (FT'.β.comp FT0.β) (c.u' k)) c.mul_u c.span_R c.dim_R c.span_R₁ c.dim_R₁ c.P_eq
    ρ hρ μ f g hfP hford hgord hgf

end Models

end WeierstrassDatum.AdaptedCoords

end Coordinates

end Main

end Hironaka
