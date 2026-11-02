/-
Copyright (c) 2026 Daattavya Aggarwal, Minhyong Kim, Oisin Kim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daattavya Aggarwal, Minhyong Kim, Oisin Kim
-/
module

public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Hironaka.Compat.TauParameterLift
public import Hironaka.Compat.FrameGraded
public import Hironaka.Compat.RSOPProducts

/-!
# The data of the reformulation of Lemma 25 (pp. 270--271)

The reformulation in the proof of Lemma 25 speaks of a regular local ring `R` with a regular frame
`(S; z₁, …, z_r)` and a regular frame `(S₀; w)` of `S`.  `WeierstrassDatum` packages these two
frames; `HasShape` is the condition (4) (the coefficient of `z^Ā` in the power series expansion of
`f` over `S` is `u (w^e + p₂ w^{e-2} + ⋯ + p_e)`), `TauParams` the condition (3) as printed ("`(w)`
can be extended to a regular system of `τ_{(z)}`-parameters of `R` for `f`") and `InTauStar` its
reading through the space `T*` of Definition 10* (`inTauStar_iff_tauParams`).

`WeierstrassDatum.rsopIndep_snoc`: `(z₁, …, z_r, w)` is independent modulo `M²`, so injective and
extendable to a regular system of parameters of `R` (`R/(z)R ≅ S` and `w` is part of a regular
system of parameters of `S`).
-/

@[expose] public section

open IsLocalRing

namespace Hironaka

universe u

section Datum

variable {R : Type u} [CommRing R] [IsRegularLocalRing R]

/-- The data of the reformulation of Lemma 25 (p. 270): a regular frame `(S; z₁, …, z_r)` of `R` and
a regular frame `(S₀; w)` of `S` (a regular frame with the single element `w`). -/
structure WeierstrassDatum (R : Type u) [CommRing R] [IsRegularLocalRing R] where
  /-- The regular frame `(S; z₁, …, z_r)` of `R`. -/
  F : RegularFrame R
  /-- The regular frame `(S₀; w)` of `S`. -/
  F0 : RegularFrame F.S
  /-- `(S₀; w)` has one element. -/
  rank_eq_one : F0.r = 1

namespace WeierstrassDatum

variable (D : WeierstrassDatum R)

/-- The element `w` of `S`. -/
def w : D.F.S := D.F0.z (Fin.cast D.rank_eq_one.symm 0)

/-- The image of `w` in `R`. -/
def wR : R := algebraMap D.F.S R D.w

section Independence

open Classical in
/-- `(z₁, …, z_r, w)` is independent modulo `M²`: `(S; z)` and `(S₀; w)` being regular frames,
`R/(z)R ≅ S` and `w` is part of a regular system of parameters of `S`. -/
theorem rsopIndep_snoc : RSOPIndep (Finset.univ : Finset (Fin (D.F.r + 1)))
    (Fin.snoc D.F.z D.wR : Fin (D.F.r + 1) → R) := by
  set v : Fin (D.F.r + 1) → R := Fin.snoc D.F.z D.wR with hv
  have hvc : ∀ j : Fin D.F.r, v j.castSucc = D.F.z j := fun j => by simp [hv]
  have hvl : v (Fin.last D.F.r) = D.wR := by simp [hv]
  set G : Finset (Fin (D.F.r + 1)) := Finset.univ.image Fin.castSucc with hG
  set Fs : Finset (Fin (D.F.r + 1)) := {Fin.last D.F.r} with hFs
  have hunion : G ∪ Fs = Finset.univ := by
    ext i
    simp only [hG, hFs, Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and,
      Finset.mem_singleton, iff_true]
    exact Fin.lastCases (Or.inr rfl) (fun j => Or.inl ⟨j, rfl⟩) i
  have hdisj : Disjoint G Fs := by
    rw [Finset.disjoint_left]
    intro i hi
    simp only [hG, Finset.mem_image] at hi
    obtain ⟨j, -, rfl⟩ := hi
    simp [hFs, Fin.castSucc_ne_last]
  have himg : G.image v = Finset.image D.F.z Finset.univ := by
    simp only [hG, Finset.image_image]
    exact congrArg (fun g => Finset.image g Finset.univ) (funext hvc)
  have hGind : RSOPIndep G v := by
    refine RSOPIndep.of_extends ?_ (by rw [himg]; exact D.F.extends_rsop)
    intro a ha b hb hab
    simp only [hG, Finset.coe_image, Set.mem_image, Finset.mem_coe, Finset.mem_univ,
      true_and] at ha hb
    obtain ⟨i, rfl⟩ := ha
    obtain ⟨j, rfl⟩ := hb
    rw [hvc, hvc] at hab
    rw [D.F.z_injective hab]
  have hJ : D.F.idealZ = Ideal.span (v '' (G : Set (Fin (D.F.r + 1)))) := by
    unfold RegularFrame.idealZ
    congr 1
    ext x
    simp only [hG, Finset.coe_image, Finset.coe_univ, Set.image_univ, Set.mem_range,
      Set.mem_image]
    constructor
    · rintro ⟨j, rfl⟩
      exact ⟨j.castSucc, ⟨j, rfl⟩, hvc j⟩
    · rintro ⟨_, ⟨j, rfl⟩, rfl⟩
      exact ⟨j, (hvc j).symm⟩
  have hreg : IsRegularLocalRing (R ⧸ D.F.idealZ) := by
    have := D.F.extends_rsop.isRegularLocalRing_quotient
    have h : D.F.idealZ = Ideal.span ((Finset.image D.F.z Finset.univ : Finset R) : Set R) := by
      unfold RegularFrame.idealZ
      congr 1
      simp
    rw [h]
    exact this
  let φ : D.F.S ≃+* R ⧸ D.F.idealZ :=
    RingEquiv.ofBijective ((Ideal.Quotient.mk D.F.idealZ).comp (algebraMap D.F.S R))
      D.F.quot_bijective
  have h0 : RSOPIndep ({Fin.last D.F.r} : Finset (Fin (D.F.r + 1))) (fun _ => D.w) := by
    refine RSOPIndep.of_extends (fun a ha b hb _ => ?_) ?_
    · rw [Finset.coe_singleton, Set.mem_singleton_iff] at ha hb
      rw [ha, hb]
    · refine ExtendsToRSOP.mono D.F0.extends_rsop ?_
      intro x hx
      simp only [Finset.image_singleton, Finset.mem_singleton] at hx
      subst hx
      exact Finset.mem_image.mpr ⟨Fin.cast D.rank_eq_one.symm 0, Finset.mem_univ _, rfl⟩
  have hF : RSOPIndep Fs (fun i => Ideal.Quotient.mk D.F.idealZ (v i)) := by
    intro i hi
    have hi' : i = Fin.last D.F.r := Finset.mem_singleton.mp hi
    subst hi'
    have h1 := RSOPIndep.map_ringEquiv φ h0 (Fin.last D.F.r) (Finset.mem_singleton_self _)
    have hφ : φ D.w = Ideal.Quotient.mk D.F.idealZ (v (Fin.last D.F.r)) := by
      rw [hvl]
      rfl
    simp only [hφ] at h1
    simpa [hFs] using h1
  have := RSOPIndep.union_of_quotient hdisj hGind (J := D.F.idealZ) hJ hF
  convert this using 2
  ext i
  simp only [hG, hFs, Finset.mem_univ, Finset.mem_union, Finset.mem_image, Finset.mem_singleton,
    true_iff]
  exact Fin.lastCases (Or.inr rfl) (fun j => Or.inl ⟨j, trivial, rfl⟩) i

/-- The members of `(z₁, …, z_r, w)` are distinct. -/
theorem injective_snoc : Function.Injective (Fin.snoc D.F.z D.wR : Fin (D.F.r + 1) → R) := by
  classical
  have := D.rsopIndep_snoc.injOn
  intro a b hab
  exact this (Finset.mem_coe.mpr (Finset.mem_univ a)) (Finset.mem_coe.mpr (Finset.mem_univ b)) hab

open Classical in
/-- `(z₁, …, z_r, w)` can be extended to a regular system of parameters of `R`. -/
theorem extendsToRSOP_snoc : ExtendsToRSOP R
    (Finset.image (Fin.snoc D.F.z D.wR : Fin (D.F.r + 1) → R) Finset.univ) :=
  D.rsopIndep_snoc.injOn_and_extends.2

/-- `w` has order one: it is part of a regular system of parameters. -/
theorem ordElem_wR : Ideal.ordElem (maximalIdeal R) D.wR = ((1 : ℕ) : ℕ∞) := by
  classical
  have h := D.rsopIndep_snoc (Fin.last D.F.r) (Finset.mem_univ _)
  have hv : (Fin.snoc D.F.z D.wR : Fin (D.F.r + 1) → R) (Fin.last D.F.r) = D.wR := by simp
  rw [hv] at h
  have hsq : D.wR ∉ maximalIdeal R ^ 2 := fun h2 => h.2 (Ideal.mem_sup_right h2)
  refine le_antisymm (Ideal.ordElem_le_of_notMem (m := 1) hsq) ?_
  exact Ideal.le_ordElem (by rw [pow_one]; exact h.1)

theorem wR_mem_pow_one : D.wR ∈ maximalIdeal R ^ 1 :=
  Ideal.mem_pow_of_ordElem D.ordElem_wR

theorem wR_mem : D.wR ∈ maximalIdeal R := by
  simpa using D.wR_mem_pow_one

/-- The initial form of `w` is its class in `gr¹_M(R) = M/M²`. -/
theorem initialForm_wR : initialForm (maximalIdeal R) D.wR =
    AssocGraded.mk (maximalIdeal R) 1 D.wR D.wR_mem_pow_one :=
  initialForm_eq_mk _ D.ordElem_wR

open Classical in
theorem frameForm_snoc_wR : frameForm (Fin.snoc D.F.z D.wR : Fin (D.F.r + 1) → R) =
    (Fin.snoc (frameForm D.F.z) (initialForm (maximalIdeal R) D.wR) :
      Fin (D.F.r + 1) → AssocGraded (maximalIdeal R)) := by
  funext j
  refine Fin.lastCases ?_ (fun j => ?_) j
  · simp [frameForm]
  · simp [frameForm]

open Classical in
/-- The initial form of `w` is independent of `Z_1, …, Z_r`. -/
theorem initialForm_wR_notMem_span : initialForm (maximalIdeal R) D.wR ∉
    Submodule.span (R ⧸ maximalIdeal R) (Set.range (frameForm D.F.z)) := by
  let _ : Field (R ⧸ maximalIdeal R) := Ideal.Quotient.field _
  obtain ⟨hli, -⟩ := linearIndependent_frameForm D.injective_snoc D.extendsToRSOP_snoc
  rw [D.frameForm_snoc_wR] at hli
  exact (linearIndependent_finSnoc.mp hli).2

end Independence

open Classical in
/-- Condition (4) of the reformulation (p. 270): "`f` can be written in the form
`f = g + u z^Ā (w^e + p₂ w^{e-2} + ⋯ + p_e)` where `g = ∑_{A ≠ Ā} h_A z^A` with `h_A ∈ S`, `u` a
unit in `S`, `e = ν_M(f) − |Ā| > 0`, and `p_j ∈ S₀` for `2 ≤ j ≤ e`": the coefficient `h_Ā` of
`z^Ā` in the (unique) power series expansion of `f` over `S` is `u (w^e + p₂ w^{e-2} + ⋯ + p_e)`.
(The other coefficients `h_A` are arbitrary, so that `g` plays no role in the statement; the
expansion is the canonical expansion `RegularFrame.expCoeff` of the frame, which exists although
`R` is not assumed to be complete.) -/
def HasShape (f : R) : Prop :=
  ∃ (A : Fin D.F.r →₀ ℕ) (e : ℕ) (u : D.F.S) (p : ℕ → D.F0.S), IsUnit u ∧ 0 < e ∧
    ((A.degree + e : ℕ) : ℕ∞) = Ideal.ordElem (maximalIdeal R) f ∧
    D.F.expCoeff f A = u * (D.w ^ e + ∑ j ∈ Finset.Icc 2 e,
      algebraMap D.F0.S D.F.S (p j) * D.w ^ (e - j))

open Classical in
/-- Condition (4) in the form printed on p. 270, read in the power series ring `S{z}` into which `R`
is embedded by the expansion of the frame (`RegularFrame.expansion`; `R` itself is not assumed
complete, so the infinite sum `g = ∑_{A ≠ Ā} h_A z^A` of the printed text lives there): "`f` can be
written in the form `f = g + u z^Ā (w^e + p₂ w^{e-2} + ⋯ + p_e)` where `g = ∑_{A ≠ Ā} h_A z^A` with
`h_A ∈ S`, `u` = a unit in `S`, `e = ν_M(f) − |Ā| > 0`, and `p_j ∈ S₀` for `2 ≤ j ≤ e`".  The series
`g` is any series without the monomial `z^Ā`.  This is `HasShape` (comparison of the coefficient of
`z^Ā`). -/
theorem hasShape_iff_expansion (f : R) :
    D.HasShape f ↔ ∃ (A : Fin D.F.r →₀ ℕ) (e : ℕ) (u : D.F.S) (p : ℕ → D.F0.S)
      (g : MvPowerSeries (Fin D.F.r) D.F.S), IsUnit u ∧ 0 < e ∧
      ((A.degree + e : ℕ) : ℕ∞) = Ideal.ordElem (maximalIdeal R) f ∧
      MvPowerSeries.coeff A g = 0 ∧
      D.F.expansion f = g + MvPowerSeries.monomial A (u * (D.w ^ e + ∑ j ∈ Finset.Icc 2 e,
        algebraMap D.F0.S D.F.S (p j) * D.w ^ (e - j))) := by
  constructor
  · rintro ⟨A, e, u, p, hu, he, hdeg, hcoeff⟩
    refine ⟨A, e, u, p, D.F.expansion f - MvPowerSeries.monomial A (u * (D.w ^ e +
      ∑ j ∈ Finset.Icc 2 e, algebraMap D.F0.S D.F.S (p j) * D.w ^ (e - j))),
      hu, he, hdeg, ?_, by abel⟩
    rw [map_sub, MvPowerSeries.coeff_monomial_same, RegularFrame.coeff_expansion, hcoeff,
      sub_self]
  · rintro ⟨A, e, u, p, g, hu, he, hdeg, hg, hf⟩
    refine ⟨A, e, u, p, hu, he, hdeg, ?_⟩
    rw [← RegularFrame.coeff_expansion, hf, map_add, hg, zero_add,
      MvPowerSeries.coeff_monomial_same]

/-- Condition (3) of the reformulation (p. 270): "`(w)` can be extended to a regular system of
`τ_{(z)}`-parameters of `R` for `f`", in the form: the initial form of `w` lies in the space `T*`
of Definition 10* (`w`, `z₁, …, z_r` are independent modulo `M²`, so the two are equivalent:
`inTauStar_iff_tauParams`). -/
def InTauStar (f : R) : Prop :=
  initialForm (maximalIdeal R) D.wR ∈ tauZSubmoduleStar R D.F.z (fun _ : Fin 1 => f)

open Classical in
/-- Condition (3) of the reformulation as printed (p. 270): "`(w)` can be extended to a regular
system of `τ_{(z)}`-parameters of `R` for `f`": some regular system `(x₁, …, x_τ)` of
`τ_{(z)}`-parameters of `R` for `f` (Definition 10*) has `w` as one of its members. -/
def TauParams (f : R) : Prop :=
  ∃ x : Fin (tauZ R D.F.z (fun _ : Fin 1 => f)) → maximalIdeal R,
    IsRegularSystemOfTauZParameters R D.F.z (fun _ : Fin 1 => f) x ∧ ∃ i, (x i : R) = D.wR

open Classical in
/-- The two readings of condition (3) agree: `(z, w)` can be extended to a regular system of
parameters (`w, z₁, …, z_r` are independent modulo `M²`), so `w` is a member of a regular system of
`τ_{(z)}`-parameters exactly when its initial form lies in `T*`. -/
theorem inTauStar_iff_tauParams (f : R) : D.InTauStar f ↔ D.TauParams f := by
  constructor
  · intro hT
    obtain ⟨-, hord⟩ := linearIndependent_frameForm D.F.z_injective D.F.extends_rsop
    have hU : tauZSubmoduleStar R D.F.z (fun _ : Fin 1 => f) ≤
        classSubmodule (maximalIdeal R) :=
      (tauZSubmoduleStar_le_homogeneous_one hord).trans
        homogeneous_one_le_classSubmodule_maximalIdeal
    have hT' : AssocGraded.mk (maximalIdeal R) 1 D.wR D.wR_mem_pow_one ∈
        tauZSubmoduleStar R D.F.z (fun _ : Fin 1 => f) := by
      rw [InTauStar, D.initialForm_wR] at hT
      exact hT
    have hWZ : AssocGraded.mk (maximalIdeal R) 1 D.wR D.wR_mem_pow_one ∉
        Submodule.span (R ⧸ maximalIdeal R) (Set.range (frameForm D.F.z)) := by
      rw [← D.initialForm_wR]
      exact D.initialForm_wR_notMem_span
    obtain ⟨x, hx, -, i, hi⟩ := exists_isRegularSystemOfTauZParameters_of_mem
      D.F.z_injective D.F.extends_rsop hU D.wR_mem D.wR_mem_pow_one hT' hWZ
    exact ⟨x, hx, i, hi⟩
  · rintro ⟨x, hx, i, hi⟩
    have hmk : linearForms R x i = AssocGraded.mk (maximalIdeal R) 1 D.wR D.wR_mem_pow_one := by
      have key : ∀ (a b : R) (h : a = b) (ha : a ∈ maximalIdeal R ^ 1)
          (hb : b ∈ maximalIdeal R ^ 1), AssocGraded.mk (maximalIdeal R) 1 a ha =
            AssocGraded.mk (maximalIdeal R) 1 b hb := fun a b h ha hb => by subst h; rfl
      exact key _ _ hi _ _
    show initialForm (maximalIdeal R) D.wR ∈ _
    rw [D.initialForm_wR, ← hmk]
    have hsp := hx
    unfold IsRegularSystemOfTauZParameters at hsp
    rw [← hsp]
    exact Submodule.subset_span (Or.inl ⟨i, rfl⟩)

end WeierstrassDatum

end Datum

end Hironaka
