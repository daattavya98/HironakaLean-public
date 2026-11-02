/-
Copyright (c) 2026 Daattavya Aggarwal, Minhyong Kim, Oisin Kim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daattavya Aggarwal, Minhyong Kim, Oisin Kim
-/
module

public import Mathlib.FieldTheory.Perfect
public import Mathlib.RingTheory.MvPowerSeries.Basic
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Hironaka.Compat.WeierstrassDatum
public import Hironaka.Ch3.JStability
public import Hironaka.Ch3.JStabilityLemma22
public import Hironaka.Statements

/-!
# The frame transforms in the reformulation of Lemma 25 (pp. 270--271), part (a) and (c)(i)

* `WeierstrassDatum.wR_mem_of_hasShape`: (a), `P ⊇ (z₁, …, z_r, w)R`.  By Lemma 22 for the frame
  `(S₀; w)` of `S` and the prime `Q = P ∩ S`, after the estimate of the coefficients of the
  expansion of an element of `Pⁿ` (`RegularFrame.expCoeff_mem_pow_comap`).
* `WeierstrassDatum.exists_frameTransforms`: (c)(i), the existence of `y ∈ P ∩ S₀` with
  `PR₁ = (y)R₁`, of the frame transform of `(S; z)` in `R₁` with denominator `y` and of the frame
  transform of `(S₀; w)` in `S₁` with denominator `y`.  The system of `τ_{(z)}`-parameters through
  `w` lying in `P` (`exists_isRegularSystemOfTauZParameters_of_mem`) gives `w/x ∈ M₁` by Lemma 24,
  and Nakayama's lemma (`RegularFrame.exists_mem_span_eq_of_nonunit`, applied to `(S; z)` in `R₁`
  and to `(S₀; w)` in `S₁`) gives the denominators in `S` and in `S₀`.
-/

@[expose] public section

open IsLocalRing

namespace Hironaka

universe u

section Prelim

attribute [local instance] RegularFrame.isDomain_S

variable {R : Type u} [CommRing R] [IsRegularLocalRing R]

/-- `S / (P ∩ S) ≅ R / P` is regular when `R / P` is, for a prime `P ⊇ (z)R` of a regular frame. -/
theorem RegularFrame.isRegularLocalRing_quotient_comap' (F : RegularFrame R) (P : Ideal R)
    [P.IsPrime] (hzP : F.idealZ ≤ P) (hPreg : IsRegularLocalRing (R ⧸ P)) :
    IsRegularLocalRing (F.S ⧸ P.comap (algebraMap F.S R)) := by
  have := hPreg
  let φ : F.S →+* R ⧸ P := (Ideal.Quotient.mk P).comp (algebraMap F.S R)
  have hφ : Function.Surjective φ := by
    intro a
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective a
    obtain ⟨s, hs⟩ := F.quot_bijective.2 (Ideal.Quotient.mk (Ideal.span (Set.range F.z)) y)
    refine ⟨s, ?_⟩
    have h1 : algebraMap F.S R s - y ∈ F.idealZ := Ideal.Quotient.eq.mp hs
    show Ideal.Quotient.mk P (algebraMap F.S R s) = Ideal.Quotient.mk P y
    exact Ideal.Quotient.eq.mpr (hzP h1)
  have hker : P.comap (algebraMap F.S R) = RingHom.ker φ := by
    ext a
    rw [Ideal.mem_comap, RingHom.mem_ker]
    exact (Ideal.Quotient.eq_zero_iff_mem (I := P) (a := algebraMap F.S R a)).symm
  have e : (F.S ⧸ P.comap (algebraMap F.S R)) ≃+* R ⧸ P :=
    (Ideal.quotEquivOfEq hker).trans (RingHom.quotientKerEquivOfSurjective hφ)
  exact IsRegularLocalRing.of_ringEquiv e.symm

namespace WeierstrassDatum

variable (D : WeierstrassDatum R)

/-- The only member of the frame `(S₀; w)` is `w`. -/
theorem z0_eq (j : Fin D.F0.r) : D.F0.z j = D.w := by
  have h1 : j.val < 1 := D.rank_eq_one ▸ j.2
  have : j = Fin.cast D.rank_eq_one.symm 0 := Fin.ext (by simp; omega)
  rw [this]
  rfl

end WeierstrassDatum

end Prelim

section CoeffWeight

variable {R : Type u} [CommRing R] [IsRegularLocalRing R]

namespace RegularFrame

/-- The elements `x` of `R` whose coefficients `c_A(x) ∈ S` in the power series expansion over a
frame lie in `Q^{n − |A|}` (`Q` an ideal of `S`, truncated subtraction). -/
def coeffWeightIdeal (F : RegularFrame R) (Q : Ideal F.S) (n : ℕ) : Ideal R where
  carrier := {x | ∀ A : Fin F.r →₀ ℕ, F.expCoeff x A ∈ Q ^ (n - A.degree)}
  zero_mem' := fun A => by
    have : F.expCoeff 0 A = 0 := by
      rw [← coeff_expansion, map_zero]
      simp
    rw [this]
    exact zero_mem _
  add_mem' := fun {x y} hx hy A => by
    have : F.expCoeff (x + y) A = F.expCoeff x A + F.expCoeff y A := by
      rw [← coeff_expansion, map_add]
      simp [coeff_expansion]
    rw [this]
    exact add_mem (hx A) (hy A)
  smul_mem' := fun c x hx A => by
    rw [smul_eq_mul, ← coeff_expansion, map_mul, MvPowerSeries.coeff_mul]
    refine Ideal.sum_mem _ fun p hp => ?_
    have hsum := Finset.HasAntidiagonal.mem_antidiagonal.mp hp
    have hdeg : A.degree = p.1.degree + p.2.degree := by
      rw [← hsum]
      exact map_add Finsupp.degree p.1 p.2
    rw [coeff_expansion]
    refine Ideal.mul_mem_left _ _ ?_
    rw [coeff_expansion]
    exact Ideal.pow_le_pow_right (by omega) (hx p.2)

theorem mul_mem_coeffWeightIdeal (F : RegularFrame R) (Q : Ideal F.S) {m n : ℕ} {x y : R}
    (hx : x ∈ F.coeffWeightIdeal Q m) (hy : y ∈ F.coeffWeightIdeal Q n) :
    x * y ∈ F.coeffWeightIdeal Q (m + n) := by
  intro A
  rw [← coeff_expansion, map_mul, MvPowerSeries.coeff_mul]
  refine Ideal.sum_mem _ fun p hp => ?_
  have hsum := Finset.HasAntidiagonal.mem_antidiagonal.mp hp
  have hdeg : A.degree = p.1.degree + p.2.degree := by
    rw [← hsum]
    exact map_add Finsupp.degree p.1 p.2
  rw [coeff_expansion, coeff_expansion]
  have h1 := Ideal.mul_mem_mul (hx p.1) (hy p.2)
  rw [← pow_add] at h1
  exact Ideal.pow_le_pow_right (by omega) h1

/-- If `P ⊇ (z₁, …, z_r)R`, then `P ⊆ (z)R + (P ∩ S)R` (`R/(z) = S`). -/
theorem le_idealZ_sup_map_comap (F : RegularFrame R) (P : Ideal R) (hz : F.idealZ ≤ P) :
    P ≤ F.idealZ ⊔ (P.comap (algebraMap F.S R)).map (algebraMap F.S R) := by
  intro p hp
  obtain ⟨s, hs⟩ := F.quot_bijective.2 (Ideal.Quotient.mk (Ideal.span (Set.range F.z)) p)
  have h1 : algebraMap F.S R s - p ∈ F.idealZ := Ideal.Quotient.eq.mp hs
  have h2 : p - algebraMap F.S R s ∈ F.idealZ := by
    have := F.idealZ.neg_mem h1
    simpa using this
  have hsP : algebraMap F.S R s ∈ P := by
    have : algebraMap F.S R s = p - (p - algebraMap F.S R s) := by ring
    rw [this]
    exact P.sub_mem hp (hz h2)
  rw [Submodule.mem_sup]
  exact ⟨p - algebraMap F.S R s, h2, algebraMap F.S R s,
    Ideal.mem_map_of_mem _ (Ideal.mem_comap.mpr hsP), by ring⟩

/-- **Orders along the center**: if `P ⊇ (z)R` and `x ∈ Pⁿ`, the coefficient of `z^A` in the
expansion of `x` lies in `(P ∩ S)^{n − |A|}`. -/
theorem expCoeff_mem_pow_comap (F : RegularFrame R) (P : Ideal R) (hz : F.idealZ ≤ P) {n : ℕ}
    {x : R} (hx : x ∈ P ^ n) (A : Fin F.r →₀ ℕ) :
    F.expCoeff x A ∈ (P.comap (algebraMap F.S R)) ^ (n - A.degree) := by
  set Q := P.comap (algebraMap F.S R) with hQ
  have hP1 : P ≤ F.coeffWeightIdeal Q 1 := by
    refine (le_idealZ_sup_map_comap F P hz).trans (sup_le ?_ ?_)
    · refine Ideal.span_le.mpr ?_
      rintro _ ⟨j, rfl⟩ A
      rw [← coeff_expansion, (isExpansion_expansion F).map_z, MvPowerSeries.coeff_X]
      split_ifs with h
      · subst h
        simp
      · exact zero_mem _
    · refine Ideal.map_le_iff_le_comap.mpr fun s hs A => ?_
      rw [← coeff_expansion, (isExpansion_expansion F).map_algebraMap, MvPowerSeries.coeff_C]
      split_ifs with h
      · subst h
        simp only [map_zero, Nat.sub_zero, pow_one]
        exact hs
      · exact zero_mem _
  have hpow : ∀ n, P ^ n ≤ F.coeffWeightIdeal Q n := by
    intro n
    induction n with
    | zero =>
      intro y _ A
      simp
    | succ n ih =>
      rw [pow_succ]
      refine Ideal.mul_le.mpr fun a ha b hb => ?_
      exact mul_mem_coeffWeightIdeal F Q (ih ha) (hP1 hb)
  exact hpow n hx A

end RegularFrame

end CoeffWeight

section WMem

attribute [local instance] RegularFrame.isDomain_S

open Classical in
/-- **(a) of the reformulation of Lemma 25** (p. 271): "By (2), we have `ν_P(f) = ν`, i.e. (b),
and therefore by (4) we have `w^e + p₂w^{e-2} + ⋯ + p_e ∈ Q^e`, where `Q` is the prime ideal
`P ∩ S` in `S`. (Note that `S/Q` is regular.) By Lemma 22, we then have `w ∈ Q ⊆ P`.  Thus (a)."

Gap filled (not detailed in the paper): "`ν_P(f) = ν` and (4) give `w^e + ⋯ + p_e ∈ Q^e`" is the
estimate of the coefficients of the power series expansion of an element of `P^ν`
(`RegularFrame.expCoeff_mem_pow_comap`: the coefficient of `z^A` lies in `Q^{ν−|A|}`, because
`P = (z)R + QR`). -/
theorem WeierstrassDatum.wR_mem_of_hasShape [Hironaka.HironakaCitedResults.{u}] {R : Type u} [CommRing R] [IsRegularLocalRing R]
    [CharZero (ResidueField R)] (D : WeierstrassDatum R) {f : R} (hShape : D.HasShape f)
    {P : Ideal R} [P.IsPrime] (hz : D.F.idealZ ≤ P)
    (hP : Ideal.ordElem P f = Ideal.ordElem (maximalIdeal R) f) : D.wR ∈ P := by
  obtain ⟨A, e, u, p, ⟨v, rfl⟩, he, hdeg, hcoef⟩ := hShape
  have hQprime : (P.comap (algebraMap D.F.S R)).IsPrime := Ideal.comap_isPrime _ P
  set Q : Ideal D.F.S := P.comap (algebraMap D.F.S R) with hQ
  have hfP : f ∈ P ^ (A.degree + e) := Ideal.mem_pow_of_ordElem (hP.trans hdeg.symm)
  have hc := D.F.expCoeff_mem_pow_comap P hz hfP A
  rw [Nat.add_sub_cancel_left] at hc
  set Wp : D.F.S := D.w ^ e + ∑ j ∈ Finset.Icc 2 e,
    algebraMap D.F0.S D.F.S (p j) * D.w ^ (e - j) with hWp
  have hWpQ : Wp ∈ Q ^ e := by
    have h1 : Wp = ((v⁻¹ : D.F.Sˣ) : D.F.S) * D.F.expCoeff f A := by
      rw [hcoef, ← mul_assoc, Units.inv_mul, one_mul]
    rw [h1]
    exact Ideal.mul_mem_left _ _ hc
  have hchar : CharZero (ResidueField D.F0.S) :=
    RingHom.charZero (ResidueField.map ((algebraMap D.F.S R).comp (algebraMap D.F0.S D.F.S)))
  have hloc : ((e : ℕ) : ℕ∞) ≤ Ideal.ordElem (Q.map (algebraMap D.F.S (Localization.AtPrime Q)))
      (algebraMap D.F.S (Localization.AtPrime Q) Wp) := by
    apply Ideal.le_ordElem
    rw [← Ideal.map_pow]
    exact Ideal.mem_map_of_mem _ hWpQ
  have hwQ := mem_prime_of_ordElem_localization_ge D.F0 D.rank_eq_one D.w D.z0_eq Wp e he p hWp Q
    hloc
  exact Ideal.mem_comap.mp hwQ

end WMem

section FrameTransformI

attribute [local instance] RegularFrame.isDomain_S

variable {R : Type u} [CommRing R] [IsRegularLocalRing R]

open Classical in
/-- **(c)(i) of the reformulation of Lemma 25** (p. 271): ... -/
theorem WeierstrassDatum.exists_frameTransforms [Hironaka.HironakaCitedResults.{u}] [IsDomain R] [CharZero (ResidueField R)]
    (D : WeierstrassDatum R) {f : R} (hTau : D.InTauStar f) {P : Ideal R} [P.IsPrime]
    [IsRegularLocalRing (R ⧸ P)] (hz : D.F.idealZ ≤ P) (hwP : D.wR ∈ P)
    (hP : Ideal.ordElem P f = Ideal.ordElem (maximalIdeal R) f)
    (T : MonoidalTransform R P) [IsLocalHom T.toRing] [IsRegularLocalRing T.ring]
    (FT : D.F.FrameTransform T) {ν : ℕ} (hν : (ν : ℕ∞) = Ideal.ordElem (maximalIdeal R) f)
    {f₁ : T.ring} (hf₁ : FT.x ^ ν * f₁ = T.toRing f)
    (hord₁ : Ideal.ordElem (maximalIdeal T.ring) f₁ = ν) :
    ∃ (y : D.F0.S) (FT' : D.F.FrameTransform T) (FT0 : D.F0.FrameTransform FT'.TS),
      algebraMap D.F.S R (algebraMap D.F0.S D.F.S y) ∈ P ∧
      FT'.x = T.toRing (algebraMap D.F.S R (algebraMap D.F0.S D.F.S y)) ∧
      FT0.x = FT'.TS.toRing (algebraMap D.F0.S D.F.S y) := by
  have hPM : P ≤ maximalIdeal R := IsLocalRing.le_maximalIdeal (Ideal.IsPrime.ne_top ‹_›)
  have hzM : ∀ j, D.F.z j ∈ maximalIdeal R := fun j =>
    D.F.extends_rsop.mem_maximalIdeal (Finset.mem_image_of_mem _ (Finset.mem_univ j))
  have hz1 : ∀ j, Ideal.ordElem (maximalIdeal R) (D.F.z j) = ((1 : ℕ) : ℕ∞) := fun j =>
    ordElem_maximalIdeal_eq_one_of_mem_extendsToRSOP D.F.extends_rsop
      (Finset.mem_image_of_mem _ (Finset.mem_univ j))
  have hzP : ∀ j, D.F.z j ∈ P := fun j => hz (Ideal.subset_span ⟨j, rfl⟩)
  have hfP : f ∈ P ^ ν := Ideal.mem_pow_of_ordElem (hP.trans hν.symm)
  have hxspan : Ideal.span {T.toRing T.x} = P.map T.toRing := T.span_xR_eq_map
  have hx0 : T.toRing T.x ≠ 0 := fun h0 =>
    T.x_ne_zero (MonoidalTransform.toRing_injective T (h0.trans (map_zero _).symm))
  -- the denominator `x` of `FT` is a unit multiple of `T.xR`
  obtain ⟨u, hu⟩ : Associated (T.toRing T.x) FT.x :=
    Ideal.span_singleton_eq_span_singleton.mp (hxspan.trans FT.span_x.symm)
  have hzbM : ∀ j, (u : T.ring) * FT.w j ∈ maximalIdeal T.ring := fun j =>
    Ideal.mul_mem_left _ _ (FT.extends_rsop.mem_maximalIdeal
      (Finset.mem_image_of_mem _ (Finset.mem_univ j)))
  have hzb : ∀ j, T.toRing T.x * ((u : T.ring) * FT.w j) = T.toRing (D.F.z j) := fun j => by
    rw [← mul_assoc, hu, FT.mul_w]
  have hfb : T.toRing T.x ^ ν * ((u : T.ring) ^ ν * f₁) = T.toRing f := by
    rw [← mul_assoc, ← mul_pow, hu, hf₁]
  have hordfb : Ideal.ordElem (maximalIdeal T.ring) ((u : T.ring) ^ ν * f₁) =
      Ideal.ordElem (maximalIdeal R) f := by
    rw [Ideal.ordElem_isUnit_mul _ (u.isUnit.pow ν), hord₁, hν]
  -- the system of `τ_{(z)}`-parameters through `w`, all of whose members lie in `P`
  have hW : AssocGraded.mk (maximalIdeal R) 1 D.wR D.wR_mem_pow_one ∈
      tauZSubmoduleStar R D.F.z (fun _ : Fin 1 => f) := by
    have := hTau
    rw [WeierstrassDatum.InTauStar, D.initialForm_wR] at this
    exact this
  have hWZ : AssocGraded.mk (maximalIdeal R) 1 D.wR D.wR_mem_pow_one ∉
      Submodule.span (R ⧸ maximalIdeal R) (Set.range (frameForm D.F.z)) := by
    rw [← D.initialForm_wR]
    exact D.initialForm_wR_notMem_span
  have hU := tauZSubmoduleStar_le_classSubmodule hz1 P hPM hzP hν.symm hfP
  obtain ⟨y, hy, hyP, i₀, hi₀⟩ := exists_isRegularSystemOfTauZParameters_of_mem
    D.F.z_injective D.F.extends_rsop hU hwP D.wR_mem_pow_one hW hWZ
  have hyb : ∀ j, ∃ b, b * T.toRing T.x = T.toRing (y j : R) := fun j => by
    have : T.toRing (y j : R) ∈ Ideal.span {T.toRing T.x} :=
      hxspan ▸ Ideal.mem_map_of_mem _ (hyP j)
    exact Ideal.mem_span_singleton'.mp this
  choose yb hyb using hyb
  have hyb' : ∀ j, T.toRing T.x * yb j = T.toRing (y j : R) := fun j => by
    rw [mul_comm]; exact hyb j
  have h24 := mem_maximalIdeal_of_ordElem_eq D.F.z hzM D.F.extends_rsop f y hy P
    (Ideal.span_le.mpr (by
      rintro _ (⟨j, rfl⟩ | ⟨j, rfl⟩)
      · exact hzP j
      · exact hyP j))
    hP T T.x T.x_mem hxspan ν hν ((u : T.ring) ^ ν * f₁) hfb (fun j => (u : T.ring) * FT.w j) hzb
    yb hyb' hzbM hordfb i₀
  have hybw' : T.toRing T.x * yb i₀ = T.toRing D.wR := by rw [hyb' i₀, hi₀]
  -- Nakayama in `R₁` (level `F`): a denominator in `P ∩ S`
  obtain ⟨x₀, hx₀P, hx₀⟩ := RegularFrame.exists_mem_span_eq_of_nonunit D.F T hz hzb
    (fun j => hzbM j)
  have hTSreg : IsRegularLocalRing FT.TS.ring := FT.isRegular
  have hcomm : ∀ s : D.F.S, FT.β (FT.TS.toRing s) = T.toRing (algebraMap D.F.S R s) := fun s =>
    RingHom.congr_fun FT.canonical.comm s
  have hQS : (P.comap (algebraMap D.F.S R)).map FT.TS.toRing = Ideal.span {FT.TS.toRing FT.TS.x} :=
    FT.TS.span_xR_eq_map.symm
  have hβx : FT.β (FT.TS.toRing FT.TS.x) ∈ Ideal.span {T.toRing T.x} := by
    rw [hcomm, hxspan]
    exact Ideal.mem_map_of_mem _ (Ideal.mem_comap.mp FT.TS.x_mem)
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp hβx
  have hx₀Q : x₀ ∈ P.comap (algebraMap D.F.S R) := Ideal.mem_comap.mpr hx₀P
  obtain ⟨d, hd⟩ := Ideal.mem_span_singleton'.mp
    (hQS ▸ Ideal.mem_map_of_mem FT.TS.toRing hx₀Q)
  obtain ⟨η, hη⟩ : Associated (T.toRing T.x) (T.toRing (algebraMap D.F.S R x₀)) :=
    Ideal.span_singleton_eq_span_singleton.mp (hxspan.trans hx₀)
  have hcunit : IsUnit c := by
    have h1 : T.toRing (algebraMap D.F.S R x₀) = FT.β d * c * T.toRing T.x := by
      rw [← hcomm, ← hd, map_mul, ← hc]
      ring
    have h2 : (η : T.ring) = FT.β d * c := by
      apply mul_left_cancel₀ hx0
      rw [hη, h1]
      ring
    exact isUnit_of_mul_isUnit_right (h2 ▸ η.isUnit)
  -- `w` in `S`: `w = a · x_{S₁}`, and `a` is a non-unit
  have hwQ : D.w ∈ P.comap (algebraMap D.F.S R) := Ideal.mem_comap.mpr hwP
  obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.mp (hQS ▸ Ideal.mem_map_of_mem FT.TS.toRing hwQ)
  have hba : FT.β a * c = yb i₀ := by
    apply mul_left_cancel₀ hx0
    calc T.toRing T.x * (FT.β a * c) = FT.β a * (c * T.toRing T.x) := by ring
      _ = FT.β a * FT.β (FT.TS.toRing FT.TS.x) := by rw [hc]
      _ = FT.β (a * FT.TS.toRing FT.TS.x) := (map_mul FT.β _ _).symm
      _ = FT.β (FT.TS.toRing D.w) := by rw [ha]
      _ = T.toRing D.wR := hcomm D.w
      _ = T.toRing T.x * yb i₀ := hybw'.symm
  have hanu : ¬ IsUnit a := fun hau => by
    have : IsUnit (yb i₀) := hba ▸ (hau.map FT.β).mul hcunit
    exact (IsLocalRing.mem_maximalIdeal _).mp h24 this
  -- Nakayama in `S₁` (level `F₀`): the denominator `y ∈ S₀`
  have hzQ0 : D.F0.idealZ ≤ P.comap (algebraMap D.F.S R) := by
    unfold RegularFrame.idealZ
    rw [Ideal.span_le]
    rintro _ ⟨j, rfl⟩
    rw [D.z0_eq j]
    exact hwQ
  obtain ⟨y, hyQ, hyspan⟩ := RegularFrame.exists_mem_span_eq_of_nonunit D.F0 FT.TS hzQ0
    (w := fun _ => a) (fun j => by rw [D.z0_eq j, mul_comm]; exact ha) (fun _ => hanu)
  have hyR : algebraMap D.F.S R (algebraMap D.F0.S D.F.S y) ∈ P := Ideal.mem_comap.mp hyQ
  obtain ⟨e, he⟩ : Associated (FT.TS.toRing FT.TS.x)
      (FT.TS.toRing (algebraMap D.F0.S D.F.S y)) :=
    Ideal.span_singleton_eq_span_singleton.mp (hQS.symm.trans hyspan)
  -- `T(y)` generates `PR₁`
  have hTy : T.toRing (algebraMap D.F.S R (algebraMap D.F0.S D.F.S y)) =
      T.toRing T.x * (c * FT.β e) := by
    rw [← hcomm, ← he, map_mul, ← hc]
    ring
  have hyspanR : Ideal.span {T.toRing (algebraMap D.F.S R (algebraMap D.F0.S D.F.S y))} =
      P.map T.toRing := by
    rw [← hxspan, hTy]
    exact Ideal.span_singleton_mul_right_unit (hcunit.mul (e.isUnit.map FT.β)) _
  -- the frame transform with denominator `T(y)`
  obtain ⟨v, hv⟩ : Associated FT.x
      (T.toRing (algebraMap D.F.S R (algebraMap D.F0.S D.F.S y))) :=
    Ideal.span_singleton_eq_span_singleton.mp (FT.span_x.trans hyspanR.symm)
  have : IsRegularLocalRing (FT.rescale v).TS.ring := (FT.rescale v).isRegular
  have hQprime : (P.comap (algebraMap D.F.S R)).IsPrime := Ideal.comap_isPrime _ P
  have : IsRegularLocalRing (D.F.S ⧸ P.comap (algebraMap D.F.S R)) :=
    D.F.isRegularLocalRing_quotient_comap' P hz inferInstance
  have hw0 : ∀ j : Fin D.F0.r, FT.TS.toRing (algebraMap D.F0.S D.F.S y) *
      (((e⁻¹ : FT.TS.ringˣ) : FT.TS.ring) * a) = FT.TS.toRing (D.F0.z j) := fun j => by
    rw [← he, D.z0_eq j]
    have hee : (e : FT.TS.ring) * ((e⁻¹ : FT.TS.ringˣ) : FT.TS.ring) = 1 := Units.mul_inv e
    calc FT.TS.toRing FT.TS.x * (e : FT.TS.ring) * (((e⁻¹ : FT.TS.ringˣ) : FT.TS.ring) * a)
        = FT.TS.toRing FT.TS.x * ((e : FT.TS.ring) * ((e⁻¹ : FT.TS.ringˣ) : FT.TS.ring)) * a := by
          ring
      _ = a * FT.TS.toRing FT.TS.x := by rw [hee]; ring
      _ = FT.TS.toRing D.w := ha
  have hnu0 : ∀ j : Fin D.F0.r, ¬ IsUnit (((e⁻¹ : FT.TS.ringˣ) : FT.TS.ring) * a) := fun j h =>
    hanu (by
      have := e.isUnit.mul h
      rwa [← mul_assoc, Units.mul_inv, one_mul] at this)
  obtain ⟨FT0, hFT0⟩ := RegularFrame.exists_frameTransform_x_eq (F := D.F0)
    (T := (FT.rescale v).TS) y hyQ hyspan hw0 hnu0
  refine ⟨y, FT.rescale v, FT0, hyR, ?_, hFT0⟩
  rw [RegularFrame.FrameTransform.rescale_x]
  exact hv

end FrameTransformI

end Hironaka
