/-
Copyright (c) 2026 Daattavya Aggarwal, Minhyong Kim, Oisin Kim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daattavya Aggarwal, Minhyong Kim, Oisin Kim
-/
module

public import Mathlib.Algebra.MvPolynomial.Supported
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Hironaka.Compat.WeierstrassAdaptedModel
public import Hironaka.Compat.TauZCoreGraded

/-!
# Lemma 25, (ii) of (c) (pp. 272--273): the coefficient of `Z^Ā` in the initial form of `f`

In the proof of (ii) of (c) of Lemma 25 the shape (4) of `f` is read off in the polynomial ring
`gr_M(R) = k[Z₁, …, Z_r, W, Y₁, …, Y_b, Y, X₁, …, X_a]`:

> "Hence `φ̄` is of the form `φ̄ = ψ̄ + cZ̄^Ā(W̄^e + λ̄₂W̄^{e-2} + ⋯ + λ̄_e)`, where
> `ψ̄ = Σ_{A≠Ā} δ̄_A Z̄^A` with `δ̄_A ∈ k[W̄, Ȳ₁, …, Ȳ_b, Y, X̄₁, …, X̄_a]`, `c ≠ 0` (a constant in
> `k`), `λ̄_j ∈ k[Ȳ₁, …, Ȳ_b, Y, X̄₁, …, X̄_a]`.  On the other hand, `φ` is of the form
> `φ = ψ + cZ^Ā(W^e + λ₂W^{e-2} + ⋯ + λ_e)` where `ψ = Σ_{A≠Ā} δ_A Z^A` with
> `δ_A ∈ k[W, Y₁, …, Y_b, Y, X₁, …, X_a]`, `c` = the same non-zero constant in `k` as above,
> `λ_j ∈ k[Y₁, …, Y_b, Y, X₁, …, X_a]`."  (pp. 272--273)

`WeierstrassDatum.IsAdaptedModel.initialForm_coeff` formalizes this for an adapted polynomial model
(`Compat/WeierstrassAdaptedModel.lean`) of one regular local ring `A` with a Weierstrass datum; it
does not use completeness, so it applies to `R` and to the monoidal transform `R₁` alike.

The proof expands `f` in the frame `(S; z)`: `f ≡ Σ_B c_B z^B (mod M^{ν+1})`, with
`c_B = RegularFrame.expCoeff f B ∈ M_S^{ν-|B|}` (`RegularFrame.expCoeff_mem_pow_comap`); the
`c_B ∈ M_S^{ν-|B|}` are values of forms of degree `ν-|B|` in the generators `w, s_i` of `M_S`
(`exists_isHomogeneous_aeval_eq_of_mem_pow`), and the shape (4) gives the explicit form of `c_Ā`.
This file also contains the two facts used for it that were stated in
`Compat/WeierstrassFrameStep.lean` (`WeierstrassDatum.weierstrassPoly_mem_pow`,
`WeierstrassDatum.expCoeff_weierstrassPoly`).
-/

@[expose] public section

open IsLocalRing MvPolynomial

namespace Hironaka

universe u

section ShapeAux

attribute [local instance] RegularFrame.isDomain_S

variable {R : Type u} [CommRing R] [IsRegularLocalRing R]

open Classical in
/-- **The polynomial `w^e + p₂w^{e-2} + ⋯ + p_e` lies in `Q^e`** (p. 271: "by (4) we have
`w^e + p₂w^{e-2} + ⋯ + p_e ∈ Q^e`, where `Q` is the prime ideal `P ∩ S` in `S`"), from the shape (4)
and `ν_P(f) = ν_M(f)` (`RegularFrame.expCoeff_mem_pow_comap`). -/
theorem WeierstrassDatum.weierstrassPoly_mem_pow (D : WeierstrassDatum R) {f : R}
    {A : Fin D.F.r →₀ ℕ} {e : ℕ} {u : D.F.S} (hu : IsUnit u) {p : ℕ → D.F0.S}
    (hdeg : ((A.degree + e : ℕ) : ℕ∞) = Ideal.ordElem (maximalIdeal R) f)
    (hcoef : D.F.expCoeff f A = u * (D.w ^ e + ∑ j ∈ Finset.Icc 2 e,
      algebraMap D.F0.S D.F.S (p j) * D.w ^ (e - j)))
    {P : Ideal R} [P.IsPrime] (hz : D.F.idealZ ≤ P)
    (hP : Ideal.ordElem P f = Ideal.ordElem (maximalIdeal R) f) :
    (D.w ^ e + ∑ j ∈ Finset.Icc 2 e, algebraMap D.F0.S D.F.S (p j) * D.w ^ (e - j)) ∈
      (P.comap (algebraMap D.F.S R)) ^ e := by
  obtain ⟨v, rfl⟩ := hu
  have hfP : f ∈ P ^ (A.degree + e) := Ideal.mem_pow_of_ordElem (hP.trans hdeg.symm)
  have hc := D.F.expCoeff_mem_pow_comap P hz hfP A
  rw [Nat.add_sub_cancel_left] at hc
  have h1 : D.w ^ e + ∑ j ∈ Finset.Icc 2 e, algebraMap D.F0.S D.F.S (p j) * D.w ^ (e - j) =
      ((v⁻¹ : D.F.Sˣ) : D.F.S) * D.F.expCoeff f A := by
    rw [hcoef, ← mul_assoc, Units.inv_mul, one_mul]
  rw [h1]
  exact Ideal.mul_mem_left _ _ hc

open Classical in
/-- The expansion coefficients of the polynomial `w^e + p₂w^{e-2} + ⋯ + p_e` in the frame
`(S₀; w)`: the coefficient of `w^{e-j}` is `p_j` (`2 ≤ j ≤ e`). -/
theorem WeierstrassDatum.expCoeff_weierstrassPoly (D : WeierstrassDatum R) (e : ℕ)
    (p : ℕ → D.F0.S) {j : ℕ} (hj : j ∈ Finset.Icc 2 e) :
    D.F0.expCoeff (D.w ^ e + ∑ j ∈ Finset.Icc 2 e,
      algebraMap D.F0.S D.F.S (p j) * D.w ^ (e - j))
      (Finsupp.single (Fin.cast D.rank_eq_one.symm 0) (e - j)) = p j := by
  set i0 : Fin D.F0.r := Fin.cast D.rank_eq_one.symm 0 with hi0
  have hz0 : D.F0.z i0 = D.w := D.z0_eq i0
  set G : MvPolynomial (Fin D.F0.r) D.F0.S := MvPolynomial.X i0 ^ e +
    ∑ j' ∈ Finset.Icc 2 e, MvPolynomial.C (p j') * MvPolynomial.X i0 ^ (e - j') with hG
  have hevZ : D.F0.evZ G = D.w ^ e + ∑ j' ∈ Finset.Icc 2 e,
      algebraMap D.F0.S D.F.S (p j') * D.w ^ (e - j') := by
    simp only [hG, map_add, map_pow, map_sum, map_mul, RegularFrame.evZ, MvPolynomial.aeval_X,
      MvPolynomial.aeval_C, hz0]
  have hjle : j ≤ e := (Finset.mem_Icc.mp hj).2
  have hj2 : 2 ≤ j := (Finset.mem_Icc.mp hj).1
  rw [RegularFrame.expCoeff_eq D.F0 (G := G) (n := (Finsupp.single i0 (e - j)).degree + 1)
    (by rw [← hevZ, sub_self]; exact zero_mem _) (Nat.lt_succ_self _)]
  have hsum : ∀ j' ∈ Finset.Icc 2 e, (MvPolynomial.C (p j') * MvPolynomial.X i0 ^ (e - j')).coeff
      (Finsupp.single i0 (e - j)) = if j' = j then p j' else 0 := by
    intro j' hj'
    rw [MvPolynomial.coeff_C_mul, MvPolynomial.coeff_X_pow]
    by_cases h : j' = j
    · subst h; simp
    · have hj'le : j' ≤ e := (Finset.mem_Icc.mp hj').2
      have hne : Finsupp.single i0 (e - j) ≠ Finsupp.single i0 (e - j') := fun h' =>
        h (by have := (Finsupp.single_injective i0) h'; omega)
      have hne2 : ¬ (Finsupp.single i0 (e - j') = Finsupp.single i0 (e - j)) := fun h' => hne h'.symm
      rw [ite_eq_right hne2, ite_eq_right h, mul_zero]
  have hfirst : (MvPolynomial.X i0 ^ e : MvPolynomial (Fin D.F0.r) D.F0.S).coeff
      (Finsupp.single i0 (e - j)) = 0 := by
    rw [MvPolynomial.coeff_X_pow, ite_eq_right]
    intro h
    have := (Finsupp.single_injective i0) h
    omega
  rw [hG, MvPolynomial.coeff_add, MvPolynomial.coeff_sum, hfirst, zero_add,
    Finset.sum_congr rfl hsum, Finset.sum_ite_eq' (Finset.Icc 2 e) j, ite_eq_left hj]

end ShapeAux

section SemiModelFormula

variable {k k₁ G : Type u} [Field k] [Field k₁] [CommRing G] [Algebra k₁ G] {n : ℕ}
  (M : SemiModel k k₁ G n)

/-- A semilinear polynomial model evaluates a polynomial on the images of the variables. -/
theorem SemiModel.apply_eq_aeval (p : MvPolynomial (Fin n) k) :
    M.Φ p = aeval (R := k₁) (fun i => M.Φ (X i)) (p.map (M.ρ : k →+* k₁)) := by
  induction p using MvPolynomial.induction_on with
  | C a =>
    rw [MvPolynomial.map_C, aeval_C]
    exact M.map_C a
  | add p q hp hq => rw [map_add, hp, hq, map_add, map_add]
  | mul_X p i hp => rw [map_mul, hp, map_mul, map_X, map_mul, aeval_X]

end SemiModelFormula

section ValueClass

attribute [local instance] Ideal.Quotient.field

variable {A : Type u} [CommRing A] [IsRegularLocalRing A] {K : Type u} [Field K] {n : ℕ}
  (M : SemiModel K (A ⧸ maximalIdeal A) (AssocGraded (maximalIdeal A)) n)

/-- **The class of a value in the polynomial model**: if the variables go to the classes of
elements `v_i ∈ M` of `A`, the image under `M.Φ` of the reduction of a form `H` of degree `d` over
`A` is the class of its value at `v` in `gr^d_M(A)` (cf. `gradedModel_map_eq_mk`). -/
theorem SemiModel.apply_map_symm_eq_mk (vA : Fin n → A) (hv : ∀ i, vA i ∈ maximalIdeal A ^ 1)
    (hX : ∀ i, M.Φ (X i) = AssocGraded.mk (maximalIdeal A) 1 (vA i) (hv i))
    {H : MvPolynomial (Fin n) A} {d : ℕ} (hH : H.IsHomogeneous d) :
    M.Φ ((H.map (Ideal.Quotient.mk (maximalIdeal A))).map
        (M.ρ.symm : A ⧸ maximalIdeal A →+* K)) =
      AssocGraded.mk (maximalIdeal A) d (eval vA H)
        (eval_mem_pow_of_isHomogeneous (maximalIdeal A) vA hv hH) := by
  rw [M.apply_eq_aeval, MvPolynomial.map_map]
  have hid : (M.ρ : K →+* A ⧸ maximalIdeal A).comp
      (M.ρ.symm : A ⧸ maximalIdeal A →+* K) = RingHom.id _ :=
    RingHom.ext fun x => M.ρ.apply_symm_apply x
  rw [hid, MvPolynomial.map_id]
  have hfun : (fun i => M.Φ (X i)) = fun i => AssocGraded.mk (maximalIdeal A) 1 (vA i) (hv i) :=
    funext hX
  rw [hfun]
  exact aeval_mk_map_of_isHomogeneous (maximalIdeal A) vA hv hH

end ValueClass

section Adapted

attribute [local instance] RegularFrame.isDomain_S
attribute [local instance] Ideal.Quotient.field

variable {A : Type u} [CommRing A] [IsRegularLocalRing A]

/-- A non-zero initial form which is homogeneous of degree `1` is the class in `M/M²`: `ν_M(a) = 1`. -/
theorem ordElem_eq_one_of_initialForm_mem_homogeneous_one {a : A}
    (h : initialForm (maximalIdeal A) a ∈ AssocGraded.homogeneous (maximalIdeal A) 1)
    (h0 : initialForm (maximalIdeal A) a ≠ 0) : Ideal.ordElem (maximalIdeal A) a = ((1 : ℕ) : ℕ∞) := by
  have hne : Ideal.ordElem (maximalIdeal A) a ≠ ⊤ := fun h' => h0 (by
    rw [initialForm, dite_eq_left h'])
  obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.mp hne
  have hmk : initialForm (maximalIdeal A) a ∈ AssocGraded.homogeneous (maximalIdeal A) m := by
    rw [initialForm_eq_mk _ hm.symm]
    exact AssocGraded.mk_mem_homogeneous _ _
  have := AssocGraded.degree_eq_of_mem_homogeneous_of_ne_zero (maximalIdeal A) hmk h h0
  rw [← hm, this]

variable {D : WeierstrassDatum A} {K : Type u} [Field K] {n : ℕ}
  {M : SemiModel K (A ⧸ maximalIdeal A) (AssocGraded (maximalIdeal A)) n}
  {zI : Fin D.F.r → Fin n} {wI : Fin n} {s : Fin n → D.F0.S}

open Classical in
/-- The elements of `A` whose classes are the images of the variables of an adapted model:
`z_j` at `zI j`, `w` at `wI`, the image of `s i` at the other indices. -/
noncomputable def WeierstrassDatum.adaptedFamily (D : WeierstrassDatum A) {n : ℕ}
    (zI : Fin D.F.r → Fin n) (wI : Fin n) (s : Fin n → D.F0.S) : Fin n → A := fun i =>
  if hz : ∃ j, zI j = i then D.F.z hz.choose
  else if i = wI then D.wR
  else algebraMap D.F.S A (algebraMap D.F0.S D.F.S (s i))

theorem WeierstrassDatum.adaptedFamily_zI (hinj : Function.Injective zI) (j : Fin D.F.r) :
    D.adaptedFamily zI wI s (zI j) = D.F.z j := by
  have hz : ∃ j', zI j' = zI j := ⟨j, rfl⟩
  rw [WeierstrassDatum.adaptedFamily, dite_eq_left_of_eq_true (eq_true hz)]
  exact congrArg D.F.z (hinj hz.choose_spec)

theorem WeierstrassDatum.adaptedFamily_wI (hw : wI ∉ Set.range zI) :
    D.adaptedFamily zI wI s wI = D.wR := by
  have hz : ¬ ∃ j', zI j' = wI := fun ⟨j, hj⟩ => hw ⟨j, hj⟩
  rw [WeierstrassDatum.adaptedFamily, dite_eq_right_of_eq_false (eq_false hz)]
  simp

theorem WeierstrassDatum.adaptedFamily_other {i : Fin n} (hi : i ∉ Set.range zI) (hiw : i ≠ wI) :
    D.adaptedFamily zI wI s i = algebraMap D.F.S A (algebraMap D.F0.S D.F.S (s i)) := by
  have hz : ¬ ∃ j', zI j' = i := fun ⟨j, hj⟩ => hi ⟨j, hj⟩
  rw [WeierstrassDatum.adaptedFamily, dite_eq_right_of_eq_false (eq_false hz)]
  simp [hiw]

/-- The variables of an adapted model go to the classes in `gr¹` of the family. -/
theorem WeierstrassDatum.IsAdaptedModel.apply_X (hM : D.IsAdaptedModel M zI wI s) (i : Fin n) :
    ∃ h : D.adaptedFamily zI wI s i ∈ maximalIdeal A ^ 1,
      M.Φ (X i) = AssocGraded.mk (maximalIdeal A) 1 (D.adaptedFamily zI wI s i) h := by
  classical
  by_cases hz : ∃ j, zI j = i
  · obtain ⟨j, rfl⟩ := hz
    obtain ⟨-, hord⟩ := linearIndependent_frameForm D.F.z_injective D.F.extends_rsop
    rw [D.adaptedFamily_zI hM.zI_injective]
    refine ⟨Ideal.mem_pow_of_ordElem (hord j), ?_⟩
    rw [hM.Φ_X_zI, frameForm, initialForm_eq_mk _ (hord j)]
  · by_cases hw : i = wI
    · subst hw
      rw [D.adaptedFamily_wI hM.wI_notMem]
      refine ⟨D.wR_mem_pow_one, ?_⟩
      rw [hM.Φ_X_wI]
      exact D.initialForm_wR
    · have hi : i ∉ Set.range zI := fun ⟨j, hj⟩ => hz ⟨j, hj⟩
      rw [D.adaptedFamily_other hi hw]
      have hΦ := hM.Φ_X_other i hi hw
      have hh : M.Φ (X i) ∈ AssocGraded.homogeneous (maximalIdeal A) 1 :=
        (hM.graded 1 _).mp (isHomogeneous_X K i)
      have h0 : M.Φ (X i) ≠ 0 := fun h0 => X_ne_zero i (M.Φ.injective (by rw [h0, map_zero]))
      rw [hΦ] at hh h0
      have hord := ordElem_eq_one_of_initialForm_mem_homogeneous_one hh h0
      refine ⟨Ideal.mem_pow_of_ordElem hord, ?_⟩
      rw [hΦ, initialForm_eq_mk _ hord]

end Adapted

section SIdeals

attribute [local instance] RegularFrame.isDomain_S
attribute [local instance] Ideal.Quotient.field

variable {A : Type u} [CommRing A] [IsRegularLocalRing A]
  {D : WeierstrassDatum A} {K : Type u} [Field K] {n : ℕ}
  {M : SemiModel K (A ⧸ maximalIdeal A) (AssocGraded (maximalIdeal A)) n}
  {zI : Fin D.F.r → Fin n} {wI : Fin n} {s : Fin n → D.F0.S}

open Classical in
/-- The elements of `S` whose images (at the indices that are not `zI j`) are the elements
`w`, `s i` of the adapted model. -/
noncomputable def WeierstrassDatum.adaptedFamilyS (D : WeierstrassDatum A) {n : ℕ}
    (wI : Fin n) (s : Fin n → D.F0.S) : Fin n → D.F.S := fun i =>
  if i = wI then D.w else algebraMap D.F0.S D.F.S (s i)

/-- `M_S` is generated by `w` and the `s i`: the classes in `gr¹` come from `M_S`. -/
theorem WeierstrassDatum.IsAdaptedModel.span_adaptedFamilyS (hM : D.IsAdaptedModel M zI wI s) :
    Ideal.span (D.adaptedFamilyS wI s '' {i | i ∉ Set.range zI}) = maximalIdeal D.F.S := by
  classical
  have hspan0 := hM.span_other
  have hS0 : ∀ i, i ∉ Set.range zI → i ≠ wI → s i ∈ maximalIdeal D.F0.S := fun i hi hw => by
    rw [← hspan0]
    exact Ideal.subset_span ⟨i, ⟨hi, hw⟩, rfl⟩
  have hwM : D.w ∈ maximalIdeal D.F.S := by
    rw [← D.z0_eq (Fin.cast D.rank_eq_one.symm 0)]
    exact RegularFrame.z_mem_maximalIdeal D.F0 _
  apply le_antisymm
  · rw [Ideal.span_le]
    rintro _ ⟨i, hi, rfl⟩
    unfold WeierstrassDatum.adaptedFamilyS
    split_ifs with hw
    · exact hwM
    · exact (mem_maximalIdeal _).mpr fun hu => (mem_maximalIdeal _).mp (hS0 i hi hw)
        (isUnit_of_map_unit _ _ hu)
  · rw [D.F0.maximalIdeal_eq_idealZ_sup_map]
    refine sup_le ?_ ?_
    · refine Ideal.span_le.mpr ?_
      rintro _ ⟨j, rfl⟩
      rw [D.z0_eq j]
      refine Ideal.subset_span ⟨wI, hM.wI_notMem, ?_⟩
      simp [WeierstrassDatum.adaptedFamilyS]
    · rw [← hspan0, Ideal.map_span, Set.image_image]
      refine Ideal.span_le.mpr ?_
      rintro _ ⟨i, ⟨hi, hw⟩, rfl⟩
      refine Ideal.subset_span ⟨i, hi, ?_⟩
      simp [WeierstrassDatum.adaptedFamilyS, hw]

/-- The elements of `M_S^d` are values at `(w, s_i)` of forms of degree `d` in the variables other
than the `X_{zI j}` (the elements of `S` do not involve `Z`). -/
theorem WeierstrassDatum.IsAdaptedModel.exists_form_of_mem_pow (hM : D.IsAdaptedModel M zI wI s)
    {d : ℕ} {c : D.F.S} (hc : c ∈ maximalIdeal D.F.S ^ d) :
    ∃ H : MvPolynomial (Fin n) D.F.S, H.IsHomogeneous d ∧
      H ∈ supported D.F.S {i | i ∉ Set.range zI} ∧ aeval (D.adaptedFamilyS wI s) H = c := by
  apply exists_isHomogeneous_aeval_eq_of_mem_pow (D.adaptedFamilyS wI s) {i | i ∉ Set.range zI} d
  rw [hM.span_adaptedFamilyS]
  exact hc

/-- The elements of `M_{S₀}^j` are values at `s` of forms of degree `j` in the variables other
than the `X_{zI j}` and `X_{wI}`. -/
theorem WeierstrassDatum.IsAdaptedModel.exists_form_of_mem_pow₀ (hM : D.IsAdaptedModel M zI wI s)
    {j : ℕ} {c : D.F0.S} (hc : c ∈ maximalIdeal D.F0.S ^ j) :
    ∃ H : MvPolynomial (Fin n) D.F0.S, H.IsHomogeneous j ∧
      H ∈ supported D.F0.S {i | i ∉ Set.range zI ∧ i ≠ wI} ∧ aeval s H = c := by
  apply exists_isHomogeneous_aeval_eq_of_mem_pow s {i | i ∉ Set.range zI ∧ i ≠ wI} j
  rw [hM.span_other]
  exact hc

/-- Two valuations that agree on the variables of the support give the same value. -/
theorem aeval_congr_of_supported {R' B : Type*} [CommSemiring R'] [CommSemiring B] [Algebra R' B]
    {σ : Type*} {U : Set σ} {f g : σ → B} {H : MvPolynomial σ R'} (hH : H ∈ supported R' U)
    (hfg : ∀ i ∈ U, f i = g i) : aeval f H = aeval g H := by
  rw [aeval_def f H, aeval_def g H, eval₂_eq (algebraMap R' B) f H, eval₂_eq (algebraMap R' B) g H]
  refine Finset.sum_congr rfl fun d hd => ?_
  have : ∀ i ∈ d.support, f i = g i := fun i hi =>
    hfg i ((mem_supported.mp hH) (Finset.mem_coe.mpr
      ((mem_vars_iff_mem_support i).mpr ⟨d, hd, hi⟩)))
  have hp : ∏ i ∈ d.support, f i ^ d i = ∏ i ∈ d.support, g i ^ d i :=
    Finset.prod_congr rfl fun i hi => by rw [this i hi]
  rw [hp]

end SIdeals

section CoeffAux

/-- The variables occurring in a monomial of the support of a polynomial in `supported R U`
lie in `U`. -/
theorem mem_of_mem_support_of_mem_supported {R' : Type*} [CommSemiring R'] {σ : Type*}
    {U : Set σ} {H : MvPolynomial σ R'} (hH : H ∈ supported R' U) {m : σ →₀ ℕ}
    (hm : m ∈ H.support) {i : σ} (hi : m i ≠ 0) : i ∈ U :=
  (mem_supported.mp hH) (Finset.mem_coe.mpr
    ((mem_vars_iff_mem_support i).mpr ⟨m, hm, Finsupp.mem_support_iff.mpr hi⟩))

variable {r n : ℕ} {S K : Type*} [CommRing S] [Field K]

/-- The coefficients of a sum `Σ_B Z^B · H_B` where `H_B` involves no `Z`: at a monomial whose
`Z`-part is `Ā` only the term `B = Ā` contributes. -/
theorem coeff_sum_monomial_mul_of_zPart (zI : Fin r → Fin n) (hzI : Function.Injective zI)
    (κ : S →+* K) (Bs : Finset (Fin r →₀ ℕ)) (Hc : (Fin r →₀ ℕ) → MvPolynomial (Fin n) S)
    (hHc : ∀ B ∈ Bs, ∀ m ∈ (Hc B).support, ∀ j, m (zI j) = 0)
    {Ā : Fin r →₀ ℕ} (hĀ : Ā ∈ Bs) {m : Fin n →₀ ℕ} (hm : ∀ j, m (zI j) = Ā j) :
    Finsupp.mapDomain zI Ā ≤ m ∧
    (∑ B ∈ Bs, monomial (Finsupp.mapDomain zI B) (1 : K) * (Hc B).map κ).coeff m =
      ((Hc Ā).map κ).coeff (m - Finsupp.mapDomain zI Ā) := by
  classical
  have hmd : ∀ (B : Fin r →₀ ℕ) (j : Fin r), (Finsupp.mapDomain zI B) (zI j) = B j := fun B j =>
    Finsupp.mapDomain_apply_of_injective hzI B j
  have hmd' : ∀ (B : Fin r →₀ ℕ) (i : Fin n), i ∉ Set.range zI →
      (Finsupp.mapDomain zI B) i = 0 := by
    intro B i hi
    rw [← Finsupp.notMem_support_iff]
    intro hmem
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp (Finsupp.mapDomain_support hmem)
    exact hi ⟨j, rfl⟩
  have hle : Finsupp.mapDomain zI Ā ≤ m := by
    intro i
    by_cases hi : i ∈ Set.range zI
    · obtain ⟨j, rfl⟩ := hi
      rw [hmd, hm]
    · rw [hmd' Ā i hi]; exact Nat.zero_le _
  refine ⟨hle, ?_⟩
  rw [MvPolynomial.coeff_sum]
  rw [Finset.sum_eq_single_of_mem Ā hĀ]
  · rw [coeff_monomial_mul']
    simp [hle]
  · intro B hB hBA
    rw [coeff_monomial_mul']
    split_ifs with hBm
    · have hzero : ((Hc B).map κ).coeff (m - Finsupp.mapDomain zI B) = 0 := by
        rw [← MvPolynomial.notMem_support_iff]
        intro hmem
        have hsub := MvPolynomial.support_map_subset κ (Hc B) hmem
        have hjz := hHc B hB _ hsub
        apply hBA
        ext j
        have h1 := hjz j
        have h2 : (m - Finsupp.mapDomain zI B) (zI j) = m (zI j) - B j := by
          rw [Finsupp.tsub_apply, hmd]
        rw [h2, hm] at h1
        have h3 : B j ≤ Ā j := by
          have := hBm (zI j)
          rwa [hmd, hm] at this
        omega
      rw [hzero, mul_zero]
    · rfl

end CoeffAux

section LeadingAux

variable {n : ℕ} {K : Type*} [Field K]

/-- The shape of `c · (W^e + Σ_{j=2}^e P_j W^{e-j})` for polynomials `P_j` not involving `W`. -/
theorem coeff_support_leading (wI : Fin n) (e : ℕ) (c : K)
    (P : ℕ → MvPolynomial (Fin n) K) (hP : ∀ j ∈ Finset.Icc 2 e, ∀ m ∈ (P j).support, m wI = 0) :
    (C c * (X wI ^ e + ∑ j ∈ Finset.Icc 2 e, P j * X wI ^ (e - j)) :
        MvPolynomial (Fin n) K).coeff (Finsupp.single wI e) = c ∧
    ∀ m ∈ (C c * (X wI ^ e + ∑ j ∈ Finset.Icc 2 e, P j * X wI ^ (e - j)) :
        MvPolynomial (Fin n) K).support, m = Finsupp.single wI e ∨ m wI + 2 ≤ e := by
  classical
  -- the coefficients of the tail
  have htail : ∀ m : Fin n →₀ ℕ, (∑ j ∈ Finset.Icc 2 e, P j * X wI ^ (e - j) :
      MvPolynomial (Fin n) K).coeff m ≠ 0 → m wI + 2 ≤ e := by
    intro m hm
    rw [MvPolynomial.coeff_sum] at hm
    obtain ⟨j, hj, hjm⟩ := Finset.exists_ne_zero_of_sum_ne_zero hm
    have hj2 := Finset.mem_Icc.mp hj
    rw [X_pow_eq_monomial, coeff_mul_monomial'] at hjm
    split_ifs at hjm with hle
    · have hmem : m - Finsupp.single wI (e - j) ∈ (P j).support := by
        rw [MvPolynomial.mem_support_iff]
        intro h0
        apply hjm
        rw [h0, zero_mul]
      have h0 := hP j hj _ hmem
      have h1 := hle wI
      rw [Finsupp.tsub_apply, Finsupp.single_eq_same] at h0
      rw [Finsupp.single_eq_same] at h1
      omega
    · exact absurd rfl hjm
  have hlead : ∀ m : Fin n →₀ ℕ, (X wI ^ e : MvPolynomial (Fin n) K).coeff m =
      if m = Finsupp.single wI e then 1 else 0 := by
    intro m
    rw [X_pow_eq_monomial, coeff_monomial]
    simp only [eq_comm]
  have hco : ∀ m : Fin n →₀ ℕ, (C c * (X wI ^ e + ∑ j ∈ Finset.Icc 2 e, P j * X wI ^ (e - j)) :
      MvPolynomial (Fin n) K).coeff m = c * ((if m = Finsupp.single wI e then 1 else 0) +
      (∑ j ∈ Finset.Icc 2 e, P j * X wI ^ (e - j) : MvPolynomial (Fin n) K).coeff m) := by
    intro m
    rw [coeff_C_mul]
    congr 1
    rw [← hlead]
    exact rfl
  refine ⟨?_, ?_⟩
  · rw [hco]
    have : (∑ j ∈ Finset.Icc 2 e, P j * X wI ^ (e - j) : MvPolynomial (Fin n) K).coeff
        (Finsupp.single wI e) = 0 := by
      by_contra hne
      have := htail _ hne
      rw [Finsupp.single_eq_same] at this
      omega
    rw [this]
    simp
  · intro m hm
    rw [MvPolynomial.mem_support_iff, hco] at hm
    by_cases hmw : m = Finsupp.single wI e
    · exact Or.inl hmw
    · right
      simp only [hmw, ↓reduceIte, zero_add] at hm
      exact htail m (right_ne_zero_of_mul hm)

end LeadingAux

section Main

attribute [local instance] RegularFrame.isDomain_S
attribute [local instance] Ideal.Quotient.field

variable {A : Type u} [CommRing A] [IsRegularLocalRing A] [IsDomain A]
  {D : WeierstrassDatum A} {K : Type u} [Field K] {n : ℕ}
  {M : SemiModel K (A ⧸ maximalIdeal A) (AssocGraded (maximalIdeal A)) n}
  {zI : Fin D.F.r → Fin n} {wI : Fin n} {s : Fin n → D.F0.S}

theorem comap_maximalIdeal_algebraMap {S T : Type*} [CommRing S] [CommRing T] [IsLocalRing S]
    [IsLocalRing T] [Algebra S T] [IsLocalHom (algebraMap S T)] :
    (maximalIdeal T).comap (algebraMap S T) = maximalIdeal S := by
  ext a
  simp only [Ideal.mem_comap, mem_maximalIdeal, mem_nonunits_iff, isUnit_map_iff]

open Classical in
omit [IsDomain A] in
/-- **The coefficient of `Z^Ā` in the initial form of `f`** (pp. 272--273: "`φ` is of the form
`φ = ψ + cZ^Ā(W^e + λ₂W^{e-2} + ⋯ + λ_e)` where `ψ = Σ_{A≠Ā} δ_A Z^A` [...], `c ≠ 0` [...],
`λ_j ∈ k[Y₁, …, Y_b, Y, X₁, …, X_a]`", and the same for `φ̄`).

Let `M` be an adapted polynomial model of `gr_M(A)` (the variables `zI j`, `wI`, and the others are
the `Z_j`, `W`, `Y_j, Y, X_j`), let `f ∈ A` have order `ν = |Ā| + e` and let the coefficient of `z^Ā`
in the expansion of `f` in the frame `(S; z)` have the shape (4) (p. 270):
`h_Ā = u(w^e + p₂w^{e-2} + ⋯ + p_e)`.  Then the coefficient of `Z^Ā W^e` in the initial form `φ` of
`f` is non-zero (it is `c`), and every other monomial of `φ` with `Z`-part `Z^Ā` has `W`-degree at
most `e - 2` (it comes from `cλ_j W^{e-j}` with `j ≥ 2` and `λ_j` involving neither `Z` nor `W`).

Gap filled (the paper only says "is of the form"): the shape of `φ` is derived from the shape (4) of
`f` by the expansion `f ≡ Σ_B h_B z^B (mod M^{ν+1})` (`RegularFrame.exists_evZ_sub_mem_pow`) with
`h_B ∈ M_S^{ν-|B|}` (`RegularFrame.expCoeff_mem_pow_comap`), each `h_B` being the value of a form
of degree `ν - |B|` in `w, s_i`, and `h_Ā` the value of `c(W^e + λ₂W^{e-2} + ⋯ + λ_e)` with
`λ_j` the form of degree `j` obtained from `p_j ∈ M_{S₀}^j` (`weierstrassPoly_mem_pow`,
`expCoeff_weierstrassPoly`).  Only the part of the printed shape needed in the comparison of `φ`
and `φ̄` is recorded (the constant `c` is not required to be the same for `φ` and `φ̄`). -/
theorem WeierstrassDatum.IsAdaptedModel.initialForm_coeff (hM : D.IsAdaptedModel M zI wI s)
    {f : A} {Ā : Fin D.F.r →₀ ℕ} {e : ℕ} {u : D.F.S} {p : ℕ → D.F0.S} (hu : IsUnit u)
    (he : 0 < e) (hdeg : ((Ā.degree + e : ℕ) : ℕ∞) = Ideal.ordElem (maximalIdeal A) f)
    (hcoef : D.F.expCoeff f Ā = u * (D.w ^ e + ∑ j ∈ Finset.Icc 2 e,
      algebraMap D.F0.S D.F.S (p j) * D.w ^ (e - j))) :
    (M.Φ.symm (initialForm (maximalIdeal A) f)).coeff
        (Finsupp.mapDomain zI Ā + Finsupp.single wI e) ≠ 0 ∧
      ∀ m ∈ (M.Φ.symm (initialForm (maximalIdeal A) f)).support, (∀ j, m (zI j) = Ā j) →
        m = Finsupp.mapDomain zI Ā + Finsupp.single wI e ∨ m wI + 2 ≤ e := by
  set ν : ℕ := Ā.degree + e with hν
  have hfM : f ∈ maximalIdeal A ^ ν := Ideal.mem_pow_of_ordElem hdeg.symm
  have hin : initialForm (maximalIdeal A) f = AssocGraded.mk (maximalIdeal A) ν f hfM :=
    initialForm_eq_mk _ hdeg.symm
  have hz : D.F.idealZ ≤ maximalIdeal A := by
    refine Ideal.span_le.mpr ?_
    rintro _ ⟨j, rfl⟩
    exact RegularFrame.z_mem_maximalIdeal D.F j
  have hcomap : (maximalIdeal A).comap (algebraMap D.F.S A) = maximalIdeal D.F.S :=
    comap_maximalIdeal_algebraMap
  have hcomap0 : (maximalIdeal D.F.S).comap (algebraMap D.F0.S D.F.S) = maximalIdeal D.F0.S :=
    comap_maximalIdeal_algebraMap
  -- the unit `u` and the polynomial `W`
  set Wp : D.F.S := D.w ^ e + ∑ j ∈ Finset.Icc 2 e,
    algebraMap D.F0.S D.F.S (p j) * D.w ^ (e - j) with hWp
  have hWmem : Wp ∈ maximalIdeal D.F.S ^ e := by
    have := D.weierstrassPoly_mem_pow hu hdeg hcoef hz rfl
    rwa [hcomap] at this
  have hpj : ∀ j ∈ Finset.Icc 2 e, p j ∈ maximalIdeal D.F0.S ^ j := by
    intro j hj
    have hz0 : D.F0.idealZ ≤ maximalIdeal D.F.S := by
      refine Ideal.span_le.mpr ?_
      rintro _ ⟨i, rfl⟩
      exact RegularFrame.z_mem_maximalIdeal D.F0 i
    have h1 := D.F0.expCoeff_mem_pow_comap (maximalIdeal D.F.S) hz0 hWmem
      (Finsupp.single (Fin.cast D.rank_eq_one.symm 0) (e - j))
    rw [D.expCoeff_weierstrassPoly e p hj, hcomap0, Finsupp.degree_single] at h1
    have hjle : j ≤ e := (Finset.mem_Icc.mp hj).2
    rwa [show e - (e - j) = j by omega] at h1
  -- the explicit form of `c_Ā`
  choose! Hbar hHbar using fun j (hj : j ∈ Finset.Icc 2 e) =>
    hM.exists_form_of_mem_pow₀ (hpj j hj)
  set HĀ : MvPolynomial (Fin n) D.F.S := C u * (X wI ^ e + ∑ j ∈ Finset.Icc 2 e,
    (Hbar j).map (algebraMap D.F0.S D.F.S) * X wI ^ (e - j)) with hHĀ
  have hwT : wI ∈ {i | i ∉ Set.range zI} := hM.wI_notMem
  have hHĀ_hom : HĀ.IsHomogeneous e := by
    have h1 : (X wI ^ e : MvPolynomial (Fin n) D.F.S).IsHomogeneous e := by
      simpa using (isHomogeneous_X D.F.S wI).pow e
    have h2 : (∑ j ∈ Finset.Icc 2 e, (Hbar j).map (algebraMap D.F0.S D.F.S) * X wI ^ (e - j) :
        MvPolynomial (Fin n) D.F.S).IsHomogeneous e := by
      refine IsHomogeneous.sum _ _ _ fun j hj => ?_
      have h3 := ((hHbar j hj).1.map (algebraMap D.F0.S D.F.S)).mul
        (((isHomogeneous_X D.F.S wI).pow (e - j)) : (X wI ^ (e - j) :
          MvPolynomial (Fin n) D.F.S).IsHomogeneous (1 * (e - j)))
      have hj2 : j + 1 * (e - j) = e := by have := (Finset.mem_Icc.mp hj).2; omega
      rwa [hj2] at h3
    have h4 := (isHomogeneous_C (Fin n) u).mul (h1.add h2)
    simpa using h4
  have hXw : (X wI : MvPolynomial (Fin n) D.F.S) ∈ supported D.F.S {i | i ∉ Set.range zI} := by
    rw [supported_eq_adjoin_X]
    exact Algebra.subset_adjoin ⟨wI, hwT, rfl⟩
  have hHĀ_supp : HĀ ∈ supported D.F.S {i | i ∉ Set.range zI} := by
    refine mul_mem (Subalgebra.algebraMap_mem _ u) (add_mem (pow_mem hXw e) (sum_mem fun j hj => ?_))
    exact mul_mem (supported_mono (fun i hi => hi.1)
      (map_mem_supported_of_mem _ (hHbar j hj).2.1)) (pow_mem hXw _)
  have hHĀ_val : aeval (D.adaptedFamilyS wI s) HĀ = u * Wp := by
    have hval : ∀ j ∈ Finset.Icc 2 e, aeval (D.adaptedFamilyS wI s)
        ((Hbar j).map (algebraMap D.F0.S D.F.S)) = algebraMap D.F0.S D.F.S (p j) := by
      intro j hj
      have hsupp := map_mem_supported_of_mem (algebraMap D.F0.S D.F.S) (hHbar j hj).2.1
      rw [aeval_congr_of_supported hsupp (g := fun i => algebraMap D.F0.S D.F.S (s i))
        (fun i hi => by simp [WeierstrassDatum.adaptedFamilyS, hi.2]), aeval_map_algebraMap,
        show (fun i => algebraMap D.F0.S D.F.S (s i)) = algebraMap D.F0.S D.F.S ∘ s from rfl,
        aeval_algebraMap_apply, (hHbar j hj).2.2]
    simp only [hHĀ, map_mul, aeval_C, map_add, map_pow, aeval_X, map_sum]
    rw [Finset.sum_congr rfl fun j hj => by rw [hval j hj]]
    simp [WeierstrassDatum.adaptedFamilyS, hWp, Algebra.algebraMap_self]
  -- the truncated expansion of `f`
  obtain ⟨G, hG⟩ := RegularFrame.exists_evZ_sub_mem_pow D.F (ν + 1) f
  set Bs : Finset (Fin D.F.r →₀ ℕ) := insert Ā (G.support.filter (fun B => B.degree ≤ ν)) with hBs
  have hĀBs : Ā ∈ Bs := Finset.mem_insert_self _ _
  have hĀν : Ā.degree ≤ ν := by omega
  have hGcoeff : ∀ B : Fin D.F.r →₀ ℕ, B.degree ≤ ν → G.coeff B = D.F.expCoeff f B := fun B hB =>
    (RegularFrame.expCoeff_eq D.F hG (by omega)).symm
  have hGmem : ∀ B : Fin D.F.r →₀ ℕ, B.degree ≤ ν →
      G.coeff B ∈ maximalIdeal D.F.S ^ (ν - B.degree) := by
    intro B hB
    rw [hGcoeff B hB]
    have := D.F.expCoeff_mem_pow_comap (maximalIdeal A) hz hfM B
    rwa [hcomap] at this
  choose! Hex hHex using fun (B : Fin D.F.r →₀ ℕ) (hB : B.degree ≤ ν) =>
    hM.exists_form_of_mem_pow (hGmem B hB)
  set Hc : (Fin D.F.r →₀ ℕ) → MvPolynomial (Fin n) D.F.S := fun B => if B = Ā then HĀ else Hex B
    with hHc
  have hprop : ∀ B ∈ Bs, B.degree ≤ ν ∧ (Hc B).IsHomogeneous (ν - B.degree) ∧
      Hc B ∈ supported D.F.S {i | i ∉ Set.range zI} ∧
      aeval (D.adaptedFamilyS wI s) (Hc B) = G.coeff B := by
    intro B hB
    by_cases hBA : B = Ā
    · subst hBA
      have hHc' : Hc B = HĀ := by rw [hHc]; simp
      rw [hHc']
      refine ⟨hĀν, ?_, hHĀ_supp, ?_⟩
      · rwa [show ν - B.degree = e by omega]
      · rw [hHĀ_val, hGcoeff B hĀν, hcoef]
    · have hB' : B.degree ≤ ν := by
        rcases Finset.mem_insert.mp hB with h | h
        · exact absurd h hBA
        · exact (Finset.mem_filter.mp h).2
      have hHc' : Hc B = Hex B := by rw [hHc]; simp [hBA]
      rw [hHc']
      obtain ⟨h1, h2, h3⟩ := hHex B hB'
      exact ⟨hB', h1, h2, by rw [h3]⟩
  -- the polynomial over `A`
  have hzinj := hM.zI_injective
  choose hv hX using hM.apply_X
  set vA := D.adaptedFamily zI wI s with hvA
  set ι : D.F.S →+* A := algebraMap D.F.S A with hι
  set term : (Fin D.F.r →₀ ℕ) → A := fun B =>
    ι (G.coeff B) * B.prod fun j k => D.F.z j ^ k with hterm
  set Hbig : MvPolynomial (Fin n) A := ∑ B ∈ Bs,
    monomial (Finsupp.mapDomain zI B) (1 : A) * (Hc B).map ι with hHbig
  have hHbig_hom : Hbig.IsHomogeneous ν := by
    refine IsHomogeneous.sum _ _ _ fun B hB => ?_
    obtain ⟨hBν, hh, -, -⟩ := hprop B hB
    have h1 := (isHomogeneous_monomial (1 : A) (Finsupp.degree_mapDomain zI B)).mul (hh.map ι)
    rwa [show B.degree + (ν - B.degree) = ν by omega] at h1
  have hHbig_eval : eval vA Hbig = ∑ B ∈ Bs, term B := by
    rw [hHbig, map_sum]
    refine Finset.sum_congr rfl fun B hB => ?_
    obtain ⟨hBν, hh, hsupp, hval⟩ := hprop B hB
    rw [map_mul, eval_monomial, one_mul, Finsupp.prod_mapDomain_index_inj hzinj]
    have h1 : (B.prod fun j k => vA (zI j) ^ k) = B.prod fun j k => D.F.z j ^ k :=
      Finsupp.prod_congr fun j _ => by rw [hvA, D.adaptedFamily_zI hzinj]
    have h2 : eval vA ((Hc B).map ι) = ι (G.coeff B) := by
      rw [eval_map, ← hval]
      change aeval (R := D.F.S) vA (Hc B) = _
      rw [aeval_congr_of_supported hsupp (g := ι ∘ D.adaptedFamilyS wI s), aeval_algebraMap_apply]
      intro i hi
      by_cases hiw : i = wI
      · subst hiw
        rw [hvA, D.adaptedFamily_wI hM.wI_notMem]
        simp [WeierstrassDatum.adaptedFamilyS, WeierstrassDatum.wR, hι]
      · rw [hvA, D.adaptedFamily_other hi hiw]
        simp [WeierstrassDatum.adaptedFamilyS, hiw, hι]
    rw [h1, h2, mul_comm]
  -- `f ≡ Σ_B c_B z^B` modulo `M^{ν+1}`
  have hzpow : ∀ B : Fin D.F.r →₀ ℕ, (B.prod fun j k => D.F.z j ^ k) ∈ maximalIdeal A ^ B.degree :=
    fun B => Ideal.pow_right_mono hz B.degree (RegularFrame.prod_z_pow_mem D.F B)
  have hcongr : f - eval vA Hbig ∈ maximalIdeal A ^ (ν + 1) := by
    have hev : D.F.evZ G = ∑ B ∈ G.support, term B := by
      conv_lhs => rw [G.as_sum]
      rw [map_sum]
      refine Finset.sum_congr rfl fun B _ => ?_
      rw [RegularFrame.evZ, aeval_monomial]
    have hsub : G.support.filter (fun B => B.degree ≤ ν) ⊆ Bs := Finset.subset_insert _ _
    have hsum : ∑ B ∈ G.support.filter (fun B => B.degree ≤ ν), term B = ∑ B ∈ Bs, term B := by
      refine Finset.sum_subset hsub fun B hB hBn => ?_
      have hBA : B = Ā := by
        rcases Finset.mem_insert.mp hB with h | h
        · exact h
        · exact absurd h hBn
      subst hBA
      have : G.coeff B = 0 := by
        by_contra hne
        exact hBn (Finset.mem_filter.mpr ⟨MvPolynomial.mem_support_iff.mpr hne, hĀν⟩)
      simp [hterm, this]
    have hhigh : ∑ B ∈ G.support.filter (fun B => ¬ B.degree ≤ ν), term B ∈
        maximalIdeal A ^ (ν + 1) := by
      refine Ideal.sum_mem _ fun B hB => ?_
      have hBν := (Finset.mem_filter.mp hB).2
      refine Ideal.mul_mem_left _ _ (Ideal.pow_le_pow_right (by omega) (hzpow B))
    have hG' : f - D.F.evZ G ∈ maximalIdeal A ^ (ν + 1) :=
      Ideal.pow_right_mono hz (ν + 1) hG
    have : f - eval vA Hbig = (f - D.F.evZ G) + ∑ B ∈ G.support.filter (fun B => ¬ B.degree ≤ ν), term B := by
      rw [hHbig_eval, ← hsum, hev, ← Finset.sum_filter_add_sum_filter_not G.support
        (fun B => B.degree ≤ ν) term]
      ring
    rw [this]
    exact add_mem hG' hhigh
  -- the class of `f`
  have hmk : AssocGraded.mk (maximalIdeal A) ν f hfM =
      AssocGraded.mk (maximalIdeal A) ν (eval vA Hbig)
        (eval_mem_pow_of_isHomogeneous (maximalIdeal A) vA hv hHbig_hom) :=
    mk_eq_mk_of_sub_mem_pow_succ _ _ _ hcongr
  set κ : D.F.S →+* K := (M.ρ.symm : A ⧸ maximalIdeal A →+* K).comp
    ((Ideal.Quotient.mk (maximalIdeal A)).comp ι) with hκ
  have hφ : M.Φ.symm (initialForm (maximalIdeal A) f) =
      ∑ B ∈ Bs, monomial (Finsupp.mapDomain zI B) (1 : K) * (Hc B).map κ := by
    rw [M.Φ.symm_apply_eq, hin, hmk, ← M.apply_map_symm_eq_mk vA hv hX hHbig_hom]
    congr 1
    rw [hHbig, map_sum, map_sum]
    refine Finset.sum_congr rfl fun B _ => ?_
    simp only [map_mul, map_monomial, map_one, MvPolynomial.map_map]
    rfl
  -- the coefficients
  have hHc_supp : ∀ B ∈ Bs, ∀ m ∈ (Hc B).support, ∀ j, m (zI j) = 0 := by
    intro B hB m hm j
    by_contra hne
    exact (mem_of_mem_support_of_mem_supported (hprop B hB).2.2.1 hm hne) ⟨j, rfl⟩
  have hHĀc : Hc Ā = HĀ := by rw [hHc]; simp
  set P : ℕ → MvPolynomial (Fin n) K :=
    fun j => ((Hbar j).map (algebraMap D.F0.S D.F.S)).map κ with hP
  have hmapĀ : HĀ.map κ = C (κ u) * (X wI ^ e + ∑ j ∈ Finset.Icc 2 e, P j * X wI ^ (e - j)) := by
    rw [hHĀ]
    simp only [map_mul, map_add, map_pow, map_sum, MvPolynomial.map_C, MvPolynomial.map_X, hP]
  have hPw : ∀ j ∈ Finset.Icc 2 e, ∀ m ∈ (P j).support, m wI = 0 := by
    intro j hj m hm
    have h1 := MvPolynomial.support_map_subset κ _ hm
    have h2 := MvPolynomial.support_map_subset _ _ h1
    by_contra hne
    exact (mem_of_mem_support_of_mem_supported (hHbar j hj).2.1 h2 hne).2 rfl
  obtain ⟨hlead1, hlead2⟩ := coeff_support_leading wI e (κ u) P hPw
  rw [← hmapĀ] at hlead1 hlead2
  have hκu : κ u ≠ 0 := (hu.map κ).ne_zero
  have hmd : ∀ j, (Finsupp.mapDomain zI Ā) (zI j) = Ā j := fun j =>
    Finsupp.mapDomain_apply_of_injective hzinj Ā j
  have hmdw : (Finsupp.mapDomain zI Ā) wI = 0 := by
    rw [← Finsupp.notMem_support_iff]
    intro hmem
    obtain ⟨j, _, hj⟩ := Finset.mem_image.mp (Finsupp.mapDomain_support hmem)
    exact hM.wI_notMem ⟨j, hj⟩
  have hsingle_z : ∀ j, (Finsupp.single wI e : Fin n →₀ ℕ) (zI j) = 0 := fun j =>
    Finsupp.single_eq_of_ne (fun h => hM.wI_notMem ⟨j, h⟩)
  rw [hφ]
  refine ⟨?_, ?_⟩
  · have hm0 : ∀ j, (Finsupp.mapDomain zI Ā + Finsupp.single wI e) (zI j) = Ā j := by
      intro j
      rw [Finsupp.add_apply, hmd, hsingle_z, add_zero]
    obtain ⟨-, hco⟩ := coeff_sum_monomial_mul_of_zPart zI hzinj κ Bs Hc hHc_supp hĀBs hm0
    rw [hco, add_tsub_cancel_left, hHĀc, hlead1]
    exact hκu
  · intro m hm hmz
    obtain ⟨hle, hco⟩ := coeff_sum_monomial_mul_of_zPart zI hzinj κ Bs Hc hHc_supp hĀBs hmz
    have hne := MvPolynomial.mem_support_iff.mp hm
    rw [hco, hHĀc] at hne
    have hmem : m - Finsupp.mapDomain zI Ā ∈ (HĀ.map κ).support := MvPolynomial.mem_support_iff.mpr hne
    rcases hlead2 _ hmem with h | h
    · left
      rw [← h, add_tsub_cancel_of_le hle]
    · right
      rw [Finsupp.tsub_apply, hmdw] at h
      omega

end Main

end Hironaka
