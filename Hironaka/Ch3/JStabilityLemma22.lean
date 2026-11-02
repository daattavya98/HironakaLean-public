/-
Copyright (c) 2026 Daattavya Aggarwal, Minhyong Kim, Oisin Kim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daattavya Aggarwal, Minhyong Kim, Oisin Kim
-/
module

public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.PowerSeries.WeierstrassPreparation
public import Mathlib.RingTheory.AdicCompletion.RingHom
public import Architect
public import Hironaka.Compat.FrameShift
public import Hironaka.Compat.CompleteRationalFrameBaseChange
public import Hironaka.Compat.NagataFinite
public import Hironaka.Compat.CurveCompletion
public import Hironaka.Statements

/-!
# Ch. III §10 (pp. 265–267): Lemma 22, along the printed proof

> LEMMA 22. Let `R` be a regular local ring, `M` the maximal ideal of `R` and `(S; x)` a regular
> frame of `R`. Let `f` be an element of `R` which can be written in the form
> `f = x^ν + g₂x^{ν-2} + ⋯ + g_ν` `(ν > 0)` where `g_j ∈ S` for `2 ≤ j ≤ ν`. If the residue field
> `k` of `S` is of characteristic zero, then `x` is contained in every prime ideal `P` in `R` such
> that `ν_{PR_P}(f) ≥ ν`, where `f` is viewed as an element of `R_P`.  (p. 265)

The statement (`mem_prime_of_ordElem_localization_ge`, `lem:III.22`) is in this
separate file, rather than in `Hironaka/Ch3/JStability.lean`, because its printed proof uses the base change of regular frames
(`Hironaka/Compat/CompleteRationalFrameBaseChange.lean`), the frame transforms of §8 in the form of
`Hironaka/Compat/FrameCore.lean`, the localization of frames (`Hironaka/Compat/FrameLocalization.lean`)
and the derived normal ring of a complete curve germ (`Hironaka/Compat/CurveResolution.lean`), all of
which import `JStability.lean`.

The proof is that of the paper, in its four stages (pp. 265–267):

1. `mem_prime_of_sub_mem_of_isAdicComplete`: `x - h ∈ P` for a non-unit `h ∈ S`, `R` complete
   ("let `z = x - h` … Then `g'_1 = νh`"), through `coeff_zero_mem_comap_of_ordElem_localization_ge`
   (the frame `(S'; z)` of `R' = R_P`);
2. `mem_prime_of_isRegularLocalRing_quotient`: `R/P` regular (`exists_mem_notMem_map_sup_sq`: the
   element `w₁`; `exists_X_sub_C_mem_span_of_isUnit_coeff`: "`R̂ = Ŝ{w₁}`. Hence we have `h ∈ Ŝ` such
   that `x - h ∈ (w₁)R̂`");
3. the reduction to `k` algebraically closed and `R` complete, in the proof of
   `mem_prime_of_ordElem_localization_ge`;
4. `mem_prime_of_isAdicComplete_of_isAlgClosed`: the induction on `dim R/P`, and for
   `dim R/P = 1` (`mem_prime_of_isAdicComplete_of_ringKrullDim_le_one`) the sequence of monoidal
   transforms `R ⊆ R₁ ⊆ ⋯ ⊆ R_P` with center the maximal ideals, ending by the finiteness of the
   integral closure of `R/P` (`mem_ker_of_curveImage_eq`, a well-founded induction on the measure
   `φ(R) ∩ V` of `Hironaka/Compat/CurveResolution.lean`); one step consists of the choice of `y`
   (`exists_extendsToRSOP_le_comap_span`, corrected), the transform `R₁`
   (`exists_monoidalTransform_of_le_comap_span`), the claim `x/y ∈ M₁`
   (`mem_maximalIdeal_of_toRing_eq_xR_mul`), the passage to `(R₁, S₁, x₁, f₁, P₁)`
   (`exists_frameTransform_of_mem_maximalIdeal_hypotheses`) and, to repeat the process, the
   completion `R̂₁ = Ŝ₁{x₁}` of `R₁` with a prime over `P₁` (`exists_ringHom_comp_baseChangeHom_eq`).

Inside the proofs, `f = x^ν + g₂x^{ν-2} + ⋯ + g_ν` is written `x^ν + Σ_{i<ν} c_i x^{ν-(i+1)}` with
`c_0 = 0` (`c_i = g_{i+1}`, `sum_Icc_two_eq_sum_fin`), the shape of
`RegularFrame.coeff_mem_comap_pow_of_mem_pow`.

Where these steps argue differently from the paper or fill unargued steps, this is recorded as
"Correction of the paper" or "Gap filled" in the docstrings and in the blueprint text of Lemma 22.
-/

@[expose] public section

open IsLocalRing

namespace Hironaka

universe u

noncomputable section

section Lemma22Stages

variable {R : Type u} [CommRing R] [IsRegularLocalRing R]

/-- The step "by the uniqueness of the above expression of `f` in terms of `z` and `g'_j ∈ S`, we
have `ν_{Q'}(g'_j) ≥ j`" of the first stage of Lemma 22 (p. 266), for `j = 1`: if
`f = z^ν + Σ_{i<ν} c_i z^{ν-(i+1)}` (`c_i ∈ S`) has `ν_{PR_P}(f) ≥ ν` for a prime `P ∋ z`, then
`c₀ ∈ P ∩ S`.  The localization `(S_{P∩S}; z)` of the frame is a regular frame of `R_P`
(`RegularFrame.localizeAtPrime`; `R_P` is regular, Serre), `f ∈ (PR_P)^ν`, and
`RegularFrame.coeff_mem_comap_pow_of_mem_pow` applies to the maximal ideal `PR_P` of `R_P`. -/
theorem coeff_zero_mem_comap_of_ordElem_localization_ge [Hironaka.HironakaCitedResults.{u}] (G : RegularFrame R) (hr : G.r = 1)
    (z : R) (hz : ∀ j, G.z j = z) (ν : ℕ) (hν : 0 < ν) (c : Fin ν → G.S) (P : Ideal R)
    [P.IsPrime] (hzP : z ∈ P)
    (hP : (ν : ℕ∞) ≤ Ideal.ordElem (P.map (algebraMap R (Localization.AtPrime P)))
      (algebraMap R (Localization.AtPrime P)
        (z ^ ν + ∑ i : Fin ν, algebraMap G.S R (c i) * z ^ (ν - ((i : ℕ) + 1))))) :
    c ⟨0, hν⟩ ∈ P.comap (algebraMap G.S R) := by
  classical
  have : IsRegularLocalRing (Localization.AtPrime P) :=
    isRegularLocalRing_localization_of_isRegularLocalRing R P
  set Rp := Localization.AtPrime P
  set φ := algebraMap R Rp with hφ
  set Sp := Localization.AtPrime (P.comap (algebraMap G.S R))
  let G' := G.localizeAtPrime z hr hz P hzP
  let ι : G.S →+* G'.S := algebraMap G.S Sp
  have hι : ∀ s : G.S, algebraMap G'.S Rp (ι s) = φ (algebraMap G.S R s) := fun s =>
    Localization.localRingHom_to_map _ _ _ _ s
  set Q := maximalIdeal Rp
  have hQreg : IsRegularLocalRing (Rp ⧸ Q) := by
    let _ : Field (Rp ⧸ Q) := Ideal.Quotient.field _
    infer_instance
  have hzQ : φ z ∈ Q := (IsLocalization.AtPrime.to_map_mem_maximal_iff Rp P z).mpr hzP
  have hmem : φ z ^ ν + ∑ i : Fin ν, algebraMap G'.S Rp (ι (c i)) * φ z ^ (ν - ((i : ℕ) + 1)) ∈
      Q ^ ν := by
    have h1 := Ideal.mem_pow_of_le_ordElem hP
    rw [Localization.AtPrime.map_eq_maximalIdeal] at h1
    have e : φ (z ^ ν + ∑ i : Fin ν, algebraMap G.S R (c i) * z ^ (ν - ((i : ℕ) + 1))) =
        φ z ^ ν + ∑ i : Fin ν, algebraMap G'.S Rp (ι (c i)) * φ z ^ (ν - ((i : ℕ) + 1)) := by
      rw [map_add, map_pow, map_sum]
      refine congrArg _ (Finset.sum_congr rfl fun i _ => ?_)
      rw [map_mul, map_pow, hι]
    rwa [e] at h1
  have hcoeff := RegularFrame.coeff_mem_comap_pow_of_mem_pow G' (φ z) (fun _ => rfl) rfl Q
    hQreg hzQ ν (fun i => ι (c i)) hmem ⟨0, hν⟩
  rw [zero_add, pow_one] at hcoeff
  have hloc : Q.comap (algebraMap G'.S Rp) = maximalIdeal G'.S := by
    ext s
    simp only [Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    exact not_congr ⟨fun hu => isUnit_of_map_unit _ _ hu, fun hu => hu.map _⟩
  rw [hloc] at hcoeff
  exact (IsLocalization.AtPrime.to_map_mem_maximal_iff Sp (P.comap (algebraMap G.S R))
    (c ⟨0, hν⟩)).mp hcoeff

/-- **Lemma 22, first stage** (p. 265): "We shall first prove the assertion under the additional
assumptions that there exists a non-unit element `h` of `S` such that `x - h ∈ P` and that `R` is
complete. In fact, let `z = x - h`. We write `f` in the form `f = z^ν + g'_1z^{ν-1} + ⋯ + g'_ν` with
`g'_j ∈ S` `(1 ≤ j ≤ ν)`. Then `g'_1 = νh`. Let `R' = R_P` and `S' = S_{P∩S}`. Obviously `(S'; z)` is
a regular frame of `R'`. Let `P' = PR'` and `Q' = (P ∩ S)S'`. We have `P' = (z, Q')R'`. The
assumption that `ν_{PR_P}(f) ≥ ν` implies that `f ∈ (z, Q')^νR'`. Hence, by the uniqueness of the
above expression of `f` in terms of `z` and `g'_j ∈ S`, we have `ν_{Q'}(g'_j) ≥ j` for
`1 ≤ j ≤ ν`. In particular, `νh = g'_1 ∈ P'`, hence `h ∈ P' ∩ R = P`. Hence `x = z + h ∈ P`."

Gap filled: "Obviously `(S'; z)` is a regular frame of `R'`": `(S; z)` is a regular frame of `R`
because `R` is complete (`RegularFrame.shift`), and its localization at `P ∋ z` is `(S'; z)`
(`RegularFrame.localizeAtPrime`, which uses that `R_P` is regular: Serre, footnote 9).  "By the
uniqueness of the above expression" is `RegularFrame.coeff_mem_comap_pow_of_mem_pow` for the
maximal ideal `P'` of `R'` (`coeff_zero_mem_comap_of_ordElem_localization_ge`). -/
theorem mem_prime_of_sub_mem_of_isAdicComplete [Hironaka.HironakaCitedResults.{u}] [IsAdicComplete (maximalIdeal R) R]
    (F : RegularFrame R) (hr : F.r = 1) (x : R) (hx : ∀ j, F.z j = x)
    [CharZero (ResidueField F.S)] (ν : ℕ) (hν : 0 < ν) (c : Fin ν → F.S)
    (hc0 : c ⟨0, hν⟩ = 0) (P : Ideal R) [P.IsPrime]
    (hP : (ν : ℕ∞) ≤ Ideal.ordElem (P.map (algebraMap R (Localization.AtPrime P)))
      (algebraMap R (Localization.AtPrime P)
        (x ^ ν + ∑ i : Fin ν, algebraMap F.S R (c i) * x ^ (ν - ((i : ℕ) + 1)))))
    (h : F.S) (hh : h ∈ maximalIdeal F.S) (hxh : x - algebraMap F.S R h ∈ P) : x ∈ P := by
  classical
  -- "let `z = x - h`": `(S; z)` is a regular frame of `R` (`R` complete)
  -- "`f = z^ν + g'_1z^{ν-1} + ⋯ + g'_ν` … Then `g'_1 = νh`"
  obtain ⟨c', hc'0, hc'⟩ := exists_framePoly_shift ν hν c h
  rw [hc0, add_zero] at hc'0
  rw [hc' (algebraMap F.S R) x] at hP
  -- "In particular, `νh = g'_1 ∈ P'`"
  have hνh := coeff_zero_mem_comap_of_ordElem_localization_ge (F.shift hr hx h hh) rfl
    (x - algebraMap F.S R h) (fun _ => rfl) ν hν c' P hxh hP
  rw [hc'0] at hνh
  -- "hence `h ∈ P' ∩ R = P`. Hence `x = z + h ∈ P`."
  have hνu : IsUnit (ν : R) := by
    have := (isUnit_natCast_of_charZero_residueField F.S hν.ne').map (algebraMap F.S R)
    rwa [map_natCast] at this
  have hhP : algebraMap F.S R h ∈ P := by
    have h2 : algebraMap F.S R (ν * h) ∈ P := hνh
    rw [map_mul, map_natCast] at h2
    exact (Ideal.unit_mul_mem_iff_mem P hνu).mp h2
  have : x = (x - algebraMap F.S R h) + algebraMap F.S R h := by ring
  rw [this]
  exact add_mem hxh hhP

/-- Weierstrass division by a power series of order one modulo the maximal ideal (the step "Then the
above result shows that `R̂ = Ŝ{w₁}`. Hence we have `h ∈ Ŝ` such that `x - h ∈ (w₁)R̂`" of the second
stage of Lemma 22, p. 266): over a complete local ring `A`, if `W ∈ A{X}` has constant term in
the maximal ideal and a unit as coefficient of `X`, then `X - h ∈ (W)` for some non-unit `h ∈ A`
(Weierstrass division of `X` by `W`, Mathlib's `PowerSeries.exists_isWeierstrassDivision`). -/
theorem exists_X_sub_C_mem_span_of_isUnit_coeff {A : Type*} [CommRing A] [IsLocalRing A]
    [IsAdicComplete (maximalIdeal A) A] {σ : Type*} [Unique σ] (a₀ a₁ : A)
    (h0 : a₀ ∈ maximalIdeal A) (h1 : IsUnit a₁) (W₂ : MvPowerSeries σ A) :
    ∃ h ∈ maximalIdeal A, MvPowerSeries.X default - MvPowerSeries.C h ∈
      Ideal.span {MvPowerSeries.C a₀ + MvPowerSeries.X default *
        (MvPowerSeries.C a₁ + MvPowerSeries.X default * W₂)} := by
  classical
  set W := MvPowerSeries.C a₀ + MvPowerSeries.X default *
    (MvPowerSeries.C a₁ + MvPowerSeries.X default * W₂) with hWdef
  let e : σ ≃ Unit := Equiv.ofUnique σ Unit
  let Φ := MvPowerSeries.renameEquiv A e
  let W' : PowerSeries A := Φ W
  have hX' : Φ (MvPowerSeries.X default) = PowerSeries.X := by
    show MvPowerSeries.rename e (MvPowerSeries.X default) = _
    rw [MvPowerSeries.rename_X]
    rfl
  have hC' : ∀ b : A, Φ (MvPowerSeries.C b) = PowerSeries.C b := fun b => by
    show MvPowerSeries.rename e (MvPowerSeries.C b) = _
    rw [MvPowerSeries.rename_C]
    rfl
  have hW'eq : W' = PowerSeries.C a₀ + PowerSeries.X * (PowerSeries.C a₁ + PowerSeries.X * Φ W₂) := by
    simp only [W', hWdef, map_add, map_mul, hX', hC']
  have hcoeff0 : PowerSeries.coeff 0 W' = a₀ := by
    rw [hW'eq]; simp
  have hcoeff1 : PowerSeries.coeff 1 W' = a₁ := by
    rw [hW'eq, map_add, PowerSeries.coeff_C, ite_eq_right one_ne_zero, zero_add,
      show (1 : ℕ) = 0 + 1 from rfl, PowerSeries.coeff_succ_X_mul]
    simp
  have hres1 : PowerSeries.coeff 1 (W'.map (residue A)) ≠ 0 := by
    rw [PowerSeries.coeff_map, hcoeff1, Ne, IsLocalRing.residue_eq_zero_iff]
    exact fun hm => (IsLocalRing.mem_maximalIdeal _).mp hm h1
  have hW' : W'.map (residue A) ≠ 0 := fun h => hres1 (by rw [h, map_zero])
  have hord : (W'.map (residue A)).order = 1 := by
    rw [← Nat.cast_one, PowerSeries.order_eq_nat]
    refine ⟨hres1, fun i hi => ?_⟩
    have hi0 : i = 0 := by omega
    rw [hi0, PowerSeries.coeff_map, hcoeff0, IsLocalRing.residue_eq_zero_iff]
    exact h0
  obtain ⟨q, r, hdiv⟩ := PowerSeries.exists_isWeierstrassDivision (f := PowerSeries.X) hW'
  have hdeg : r.degree < ((W'.map (residue A)).order.toNat : WithBot ℕ) := hdiv.degree_lt
  rw [hord] at hdeg
  have hr : r = Polynomial.C (r.coeff 0) :=
    Polynomial.eq_C_of_degree_le_zero (Nat.WithBot.lt_one_iff_le_zero.mp (by simpa using hdeg))
  have heq : PowerSeries.X - PowerSeries.C (r.coeff 0) = W' * q := by
    have := hdiv.eq_mul_add
    rw [hr, Polynomial.coe_C] at this
    rw [this]
    ring
  refine ⟨r.coeff 0, ?_, ?_⟩
  · -- `X - h ∈ (W)` and `X`, `W` have constant terms in `M`
    have hc := congrArg (PowerSeries.constantCoeff) heq
    rw [map_sub, map_mul, PowerSeries.constantCoeff_X, PowerSeries.constantCoeff_C, zero_sub] at hc
    have : PowerSeries.constantCoeff W' = a₀ := by
      rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, hcoeff0]
    rw [this] at hc
    have := Ideal.mul_mem_right (PowerSeries.constantCoeff q) _ h0
    rw [← hc, neg_mem_iff] at this
    exact this
  · have h2 := congrArg Φ.symm heq
    rw [map_sub, map_mul] at h2
    have hX : Φ.symm PowerSeries.X = MvPowerSeries.X default := by
      show MvPowerSeries.rename e.symm (MvPowerSeries.X ()) = _
      rw [MvPowerSeries.rename_X]
      rfl
    have hC : Φ.symm (PowerSeries.C (r.coeff 0)) = MvPowerSeries.C (r.coeff 0) := by
      show MvPowerSeries.rename e.symm (MvPowerSeries.C (r.coeff 0)) = _
      rw [MvPowerSeries.rename_C]
    have hW : Φ.symm W' = W := Φ.symm_apply_apply W
    rw [hX, hC, hW] at h2
    rw [h2, Ideal.mem_span_singleton']
    exact ⟨_, mul_comm _ _⟩

/-- The coefficients of `f = x^ν + Σ_{i<ν} c_i x^{ν-(i+1)}` with `ν_M(f) ≥ ν`: `c_i ∈ N^{i+1}`
(`RegularFrame.coeff_mem_comap_pow_of_mem_pow` for the maximal ideal `M`; the form
`φ = X^ν + λ₂X^{ν-2} + ⋯ + λ_ν`, `λ_j` of degree `j`, of p. 266). -/
theorem coeff_mem_maximalIdeal_pow_of_mem_pow (F : RegularFrame R) (hr : F.r = 1) (x : R)
    (hx : ∀ j, F.z j = x) (ν : ℕ) (c : Fin ν → F.S)
    (hf : x ^ ν + ∑ i : Fin ν, algebraMap F.S R (c i) * x ^ (ν - ((i : ℕ) + 1)) ∈
      maximalIdeal R ^ ν) (i : Fin ν) : c i ∈ maximalIdeal F.S ^ ((i : ℕ) + 1) := by
  have hreg : IsRegularLocalRing (R ⧸ maximalIdeal R) := by
    let _ : Field (R ⧸ maximalIdeal R) := Ideal.Quotient.field _
    infer_instance
  have h := RegularFrame.coeff_mem_comap_pow_of_mem_pow F x hx hr (maximalIdeal R) hreg
    (F.mem_maximalIdeal_and_ne_zero hr hx).1 ν c hf i
  have hc : (maximalIdeal R).comap (algebraMap F.S R) = maximalIdeal F.S := by
    ext s
    simp only [Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    exact not_congr ⟨fun hu => isUnit_of_map_unit _ _ hu, fun hu => hu.map _⟩
  rwa [hc] at h

/-- The comparison of the two expressions of the initial form `φ` of `f` in the second stage of
Lemma 22 (p. 266): "The assumption `f ∈ P^ν` implies that the initial form `φ` of `f` in `gr_M(R)` is
a form only in `W₁, …, W_r`. On the other hand, […] `φ = X^ν + λ₂X^{ν-2} + ⋯ + λ_ν`, where `λ_j` is
a form of degree `j` only in `Y₁, …, Y_s`. Comparing these two expressions of `φ`, we see that one
of the `W_j`, say `W₁`, can be written as `W₁ = bX + Σ_j a_jY_j` where […] `b ≠ 0`."  In other
words, `P ⊄ NR + M²`.  The comparison is made modulo `NR`: `R/NR` is a discrete valuation ring
with uniformizing parameter `x̄` (`M = (x) + NR`), the image of `f` is `x̄^ν` (the `c_i` lie in `N`),
while `(NR + M²)^ν` maps into `(x̄)^{2ν}`. -/
theorem exists_mem_notMem_map_sup_sq (F : RegularFrame R) (hr : F.r = 1) (x : R)
    (hx : ∀ j, F.z j = x) (ν : ℕ) (hν : 0 < ν) (c : Fin ν → F.S) (P : Ideal R) [P.IsPrime]
    (hfP : x ^ ν + ∑ i : Fin ν, algebraMap F.S R (c i) * x ^ (ν - ((i : ℕ) + 1)) ∈ P ^ ν) :
    ∃ w ∈ P, w ∉ (maximalIdeal F.S).map (algebraMap F.S R) ⊔ maximalIdeal R ^ 2 := by
  classical
  have hdom := isDomain_of_isRegularLocalRing R
  set a := algebraMap F.S R with ha
  set f := x ^ ν + ∑ i : Fin ν, a (c i) * x ^ (ν - ((i : ℕ) + 1)) with hfdef
  set J : Ideal R := (maximalIdeal F.S).map a with hJ
  by_contra hcon
  push Not at hcon
  have hPL : P ≤ J ⊔ maximalIdeal R ^ 2 := fun w hw => hcon w hw
  have hPM : P ≤ maximalIdeal R := le_maximalIdeal (Ideal.IsPrime.ne_top ‹_›)
  have hfM : f ∈ maximalIdeal R ^ ν := Ideal.pow_right_mono hPM ν hfP
  have hcN : ∀ i, c i ∈ maximalIdeal F.S := fun i =>
    Ideal.pow_le_self (by omega) (coeff_mem_maximalIdeal_pow_of_mem_pow F hr x hx ν c hfM i)
  -- `R/NR` is a regular local ring of dimension one with parameter `x̄`
  obtain ⟨V, hVspan, hxV, hV⟩ := RegularFrame.exists_extendsToRSOP_insert F x hr hx
  have hJV : J = Ideal.span (V : Set R) := hVspan.symm
  have hJprime : J.IsPrime := by
    rw [hJV]; exact (hV.mono (Finset.subset_insert _ _)).isPrime_span
  have hxJ : x ∉ J := by
    obtain ⟨Z, hZsub, hZ⟩ := hV
    rw [hJV]
    exact rsop_notMem_span hZ ((Finset.subset_insert _ _).trans hZsub)
      (hZsub (Finset.mem_insert_self _ _)) hxV
  set π := Ideal.Quotient.mk J
  have hxM := (F.mem_maximalIdeal_and_ne_zero hr hx).1
  have hMmap : (maximalIdeal R).map π = Ideal.span {π x} := by
    rw [RegularFrame.maximalIdeal_eq_span_sup_map F x hr hx hxM, Ideal.map_sup, Ideal.map_span,
      Set.image_singleton, ← hJ, Ideal.map_quotient_self, sup_bot_eq]
  have hπf : π f = π x ^ ν := by
    rw [hfdef, map_add, map_pow, map_sum, add_eq_left]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [map_mul, Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_map_of_mem a (hcN i)), zero_mul]
  -- `f ∈ (NR + M²)^ν` maps into `(x̄)^{2ν}`
  have hfL : f ∈ (J ⊔ maximalIdeal R ^ 2) ^ ν := Ideal.pow_right_mono hPL ν hfP
  have hmapL : (J ⊔ maximalIdeal R ^ 2).map π ≤ Ideal.span {π x} ^ 2 := by
    rw [Ideal.map_sup, Ideal.map_quotient_self, bot_sup_eq, Ideal.map_pow, hMmap]
  have hmem : π x ^ ν ∈ Ideal.span {π x ^ (2 * ν)} := by
    have h1 := Ideal.mem_map_of_mem π hfL
    rw [Ideal.map_pow, hπf] at h1
    have h2 := Ideal.pow_right_mono hmapL ν h1
    rwa [← pow_mul, Ideal.span_singleton_pow] at h2
  obtain ⟨t, ht⟩ := Ideal.mem_span_singleton'.mp hmem
  have hx0 : π x ≠ 0 := fun h => hxJ (Ideal.Quotient.eq_zero_iff_mem.mp h)
  have : IsDomain (R ⧸ J) := Ideal.Quotient.isDomain J
  have hunit : IsUnit (π x) := by
    have h3 : π x ^ ν * (t * π x ^ ν - 1) = 0 := by
      rw [two_mul, pow_add] at ht
      linear_combination ht
    have h4 := (mul_eq_zero.mp h3).resolve_left (pow_ne_zero _ hx0)
    have h5 : π x * (t * π x ^ (ν - 1)) = 1 := by
      rw [sub_eq_zero] at h4
      rw [← h4, show ν = (ν - 1) + 1 by omega]
      simp only [Nat.add_sub_cancel]
      ring
    exact IsUnit.of_mul_eq_one _ h5
  have hne : (maximalIdeal R).map π ≠ ⊤ := by
    intro htop
    have := congrArg (Ideal.comap π) htop
    rw [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective, Ideal.comap_top] at this
    have hle : Ideal.comap π ⊥ ≤ maximalIdeal R := by
      rw [← RingHom.ker_eq_comap_bot, Ideal.mk_ker]
      exact (hJ ▸ ((maximalIdeal F.S).map_le_iff_le_comap.mpr fun s hs =>
        (IsLocalRing.mem_maximalIdeal _).mpr fun hu =>
          (IsLocalRing.mem_maximalIdeal _).mp hs (isUnit_of_map_unit _ _ hu)))
    exact (maximalIdeal.isMaximal R).ne_top (by rw [← top_le_iff, ← this]; exact sup_le le_rfl hle)
  exact hne (by rw [hMmap]; exact Ideal.span_singleton_eq_top.mpr hunit)

/-- A local homomorphism `A → B` of local rings keeps the characteristic zero of the residue field
(the residue field of `B` is an extension of that of `A`): used for `S → Ŝ`. -/
theorem charZero_residueField_of_isLocalHom {A B : Type*} [CommRing A] [IsLocalRing A] [CommRing B]
    [IsLocalRing B] (φ : A →+* B) [IsLocalHom φ] [CharZero (ResidueField A)] :
    CharZero (ResidueField B) := by
  let _ : Algebra (ResidueField A) (ResidueField B) := (ResidueField.map φ).toAlgebra
  exact charZero_of_injective_algebraMap (ResidueField.map φ).injective

/-- **Lemma 22, second stage** (p. 266): "Next we shall prove the assertion for the case in which
`R/P` is regular. In this case, `ν_{PR_P}(f) ≥ ν` is equivalent to saying that `f ∈ P^ν`. Let
`(w₁, …, w_r)` be a minimal base of `P`, and `W_j` the initial form of `w_j` in `gr_M(R)` […].
Comparing these two expressions of `φ`, we see that one of the `W_j`, say `W₁`, can be written as
`W₁ = bX + Σ_j a_jY_j` where `b` and `a_j` are in `k` (`= R/M`) and `b ≠ 0`. Let `Ŝ` and `R̂` be the
completions of `S` and `R`. Then the above result shows that `R̂ = Ŝ{w₁}`. Hence we have `h ∈ Ŝ`
such that `x - h ∈ (w₁)R̂ ⊆ PR̂`. We know that `PR̂` is a prime ideal in `R̂` and that
`ν_{PR_P}(f) ≥ ν` implies that `ν_{P̂R̂_{P̂R̂}}(f) ≥ ν`. Hence, by the first result, we have
`x ∈ PR̂`. Hence `x ∈ PR̂ ∩ R = P`."

Formalization notes: the completion `R̂` is the power series ring `Ŝ{x} = Ŝ⟦X⟧`
(`RegularFrame.baseChange` along `S → Ŝ`; `R → Ŝ{x}` transforms a regular system of parameters into
one, hence is faithfully flat and `PŜ{x}` is prime by Lemma 4 of §2).  The element `w₁` is an
element of `P` outside `NR + M²` (`exists_mem_notMem_map_sup_sq`: the comparison of the two
expressions of `φ`), i.e. `w₁ = s₀ + s₁x + x²w'` with `s₀ ∈ N` and `s₁` a unit; "`R̂ = Ŝ{w₁}`" is
used only through its consequence "`x - h ∈ (w₁)R̂` for some `h ∈ Ŝ`", which is Weierstrass
division of `X` by `w₁` (`exists_X_sub_C_mem_span_of_isUnit_coeff`). -/
theorem mem_prime_of_isRegularLocalRing_quotient [Hironaka.HironakaCitedResults.{u}] (F : RegularFrame R) (hr : F.r = 1) (x : R)
    (hx : ∀ j, F.z j = x) [CharZero (ResidueField F.S)] (ν : ℕ) (hν : 0 < ν) (c : Fin ν → F.S)
    (hc0 : c ⟨0, hν⟩ = 0) (P : Ideal R) [P.IsPrime] (hreg : IsRegularLocalRing (R ⧸ P))
    (hP : (ν : ℕ∞) ≤ Ideal.ordElem (P.map (algebraMap R (Localization.AtPrime P)))
      (algebraMap R (Localization.AtPrime P)
        (x ^ ν + ∑ i : Fin ν, algebraMap F.S R (c i) * x ^ (ν - ((i : ℕ) + 1))))) : x ∈ P := by
  classical
  set a := algebraMap F.S R with ha
  set f := x ^ ν + ∑ i : Fin ν, a (c i) * x ^ (ν - ((i : ℕ) + 1)) with hfdef
  -- "In this case, `ν_{PR_P}(f) ≥ ν` is equivalent to saying that `f ∈ P^ν`."
  have hfP : f ∈ P ^ ν := by
    rw [ordElem_localization_eq_of_isRegularLocalRing_quotient P hreg] at hP
    exact Ideal.mem_pow_of_le_ordElem hP
  -- "one of the `W_j`, say `W₁`, can be written as `W₁ = bX + Σ_j a_jY_j` […] `b ≠ 0`"
  obtain ⟨w, hwP, hwL⟩ := exists_mem_notMem_map_sup_sq F hr x hx ν hν c P hfP
  obtain ⟨w₁, hw₁⟩ := F.exists_eq_algebraMap_retraction_add_mul hr hx w
  obtain ⟨w₂, hw₂⟩ := F.exists_eq_algebraMap_retraction_add_mul hr hx w₁
  set s₀ := F.retraction w with hs₀def
  set s₁ := F.retraction w₁ with hs₁def
  have hxM := (F.mem_maximalIdeal_and_ne_zero hr hx).1
  have hwM : w ∈ maximalIdeal R := le_maximalIdeal (Ideal.IsPrime.ne_top ‹_›) hwP
  have hs₀ : s₀ ∈ maximalIdeal F.S := by
    have h1 : a s₀ ∈ maximalIdeal R := by
      have : a s₀ = w - x * w₁ := by rw [hw₁]; ring
      rw [this]
      exact sub_mem hwM (Ideal.mul_mem_right _ _ hxM)
    exact (IsLocalRing.mem_maximalIdeal _).mpr fun hu =>
      (IsLocalRing.mem_maximalIdeal _).mp h1 (hu.map a)
  have hs₁ : IsUnit s₁ := by
    by_contra hnu
    have hs₁N : s₁ ∈ maximalIdeal F.S := hnu
    apply hwL
    have hw : w = a s₀ + x * a s₁ + x ^ 2 * w₂ := by
      rw [hw₁, hw₂]; ring
    rw [hw]
    refine add_mem (add_mem (Ideal.mem_sup_left (Ideal.mem_map_of_mem _ hs₀))
      (Ideal.mem_sup_left (Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _ hs₁N))))
      (Ideal.mem_sup_right (Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow hxM 2)))
  -- "Let `Ŝ` and `R̂` be the completions of `S` and `R`": `R̂ = Ŝ{x}`
  set Sh := AdicCompletion (maximalIdeal F.S) F.S
  have : IsRegularLocalRing Sh := isRegularLocalRing_adicCompletion_of_isRegularLocalRing F.S
  have : IsAdicComplete (maximalIdeal Sh) Sh := isAdicComplete_maximalIdeal_adicCompletion F.S
  set ι := algebraMap F.S Sh with hιdef
  have hι : RingHom.MapsRSOP ι := mapsRSOP_algebraMap_adicCompletion
  set B := MvPowerSeries (Fin F.r) Sh
  set β := F.baseChangeHom ι with hβdef
  have hβ : RingHom.MapsRSOP β := F.mapsRSOP_baseChangeHom ι hι
  have : IsAdicComplete (maximalIdeal B) B := F.isAdicComplete_baseChange
  -- "We know that `PR̂` is a prime ideal in `R̂`"
  obtain ⟨hPB, -⟩ := hβ.isPrime_map_and_isRegularLocalRing_quotient (inferInstance : P.IsPrime) hreg
  set PB := P.map β with hPBdef
  have : PB.IsPrime := hPB
  -- `PR̂ ∩ R = P`
  have hcomap : PB.comap β = P := by
    let _ := β.toAlgebra
    have : Module.Flat R B := hβ.flat
    have : IsLocalHom (algebraMap R B) := (inferInstance : IsLocalHom β)
    have : Module.FaithfullyFlat R B := Module.FaithfullyFlat.of_flat_of_isLocalHom
    exact Ideal.comap_map_eq_self_of_faithfullyFlat P
  have : Unique (Fin F.r) := Equiv.unique (finCongr hr)
  set j₀ : Fin F.r := default
  have hβx : β x = MvPowerSeries.X j₀ := by rw [← hx j₀]; exact F.baseChangeHom_z ι j₀
  have hβa : ∀ s, β (a s) = MvPowerSeries.C (ι s) := F.baseChangeHom_algebraMap ι
  -- "Hence we have `h ∈ Ŝ` such that `x - h ∈ (w₁)R̂ ⊆ PR̂`."
  have hιs₀ : ι s₀ ∈ maximalIdeal Sh := (IsLocalRing.mem_maximalIdeal _).mpr fun hu =>
    (IsLocalRing.mem_maximalIdeal _).mp hs₀ (isUnit_of_map_unit ι _ hu)
  obtain ⟨h, hh, hXh⟩ := exists_X_sub_C_mem_span_of_isUnit_coeff (σ := Fin F.r) (ι s₀) (ι s₁)
    hιs₀ (hs₁.map ι) (β w₂)
  have hβw : β w = MvPowerSeries.C (ι s₀) + MvPowerSeries.X j₀ *
      (MvPowerSeries.C (ι s₁) + MvPowerSeries.X j₀ * β w₂) := by
    rw [hw₁, hw₂, map_add, map_mul, map_add, map_mul, hβa, hβa, hβx]
  have hXhP : MvPowerSeries.X j₀ - MvPowerSeries.C h ∈ PB := by
    refine (Ideal.span_singleton_le_iff_mem _).mpr ?_ hXh
    rw [← hβw]
    exact Ideal.mem_map_of_mem β hwP
  -- "`ν_{PR_P}(f) ≥ ν` implies that `ν_{P̂R̂_{P̂}}(f) ≥ ν`"
  set G := F.baseChange Sh with hGdef
  have hGx : ∀ j, G.z j = MvPowerSeries.X j₀ := fun j =>
    show MvPowerSeries.X (σ := Fin F.r) (R := Sh) j = _ from
      congrArg _ (Subsingleton.elim (α := Fin F.r) j j₀)
  have : CharZero (ResidueField Sh) := charZero_residueField_of_isLocalHom ι
  have : CharZero (ResidueField G.S) := ‹CharZero (ResidueField Sh)›
  let c' : Fin ν → G.S := fun i => ι (c i)
  have hβf : β f = MvPowerSeries.X j₀ ^ ν + ∑ i : Fin ν, algebraMap G.S B (c' i) *
      MvPowerSeries.X j₀ ^ (ν - ((i : ℕ) + 1)) := by
    rw [hfdef, map_add, map_pow, hβx, map_sum]
    refine congrArg _ (Finset.sum_congr rfl fun i _ => ?_)
    rw [map_mul, map_pow, hβx, hβa]
    rfl
  have hP' : (ν : ℕ∞) ≤ Ideal.ordElem (PB.map (algebraMap B (Localization.AtPrime PB)))
      (algebraMap B (Localization.AtPrime PB) (MvPowerSeries.X j₀ ^ ν +
        ∑ i : Fin ν, algebraMap G.S B (c' i) * MvPowerSeries.X j₀ ^ (ν - ((i : ℕ) + 1)))) := by
    rw [← hβf]
    apply Ideal.le_ordElem
    have h1 := Ideal.mem_map_of_mem β hfP
    rw [Ideal.map_pow] at h1
    have h2 := Ideal.mem_map_of_mem (algebraMap B (Localization.AtPrime PB)) h1
    rwa [Ideal.map_pow] at h2
  -- "Hence, by the first result, we have `x ∈ PR̂`. Hence `x ∈ PR̂ ∩ R = P`."
  have hX := mem_prime_of_sub_mem_of_isAdicComplete G hr (MvPowerSeries.X j₀) hGx ν hν c'
    (show ι (c ⟨0, hν⟩) = 0 by rw [hc0, map_zero]) PB hP' h hh (by
      have : algebraMap G.S B h = MvPowerSeries.C h := algebraMap_mvPowerSeries_eq_C Sh F.r h
      rw [this]; exact hXhP)
  rw [← hcomap, Ideal.mem_comap, hβx]
  exact hX

end Lemma22Stages




/-! ### The last stage: the monoidal transform `R₁` (p. 267) -/

section Lemma22Transform

variable {R : Type u} [CommRing R] [IsRegularLocalRing R] [IsDomain R]

/-- The comparison `T(f) = c₀^ν f*` for a frame transform `(S₁; z')` with denominator `c₀`
(`z = c₀ z'`, `c_i = c'_i c₀^{i+1}`): "The element `y^{-ν}f` can be written as
`y^{-ν}f = (x*)^ν + g*_1(x*)^{ν-1} + ⋯ + g*_ν` where `g*_j ∈ S₁`" (p. 267). -/
theorem toRing_framePoly_eq {A B : Type*} [CommRing A] [CommRing B] (T : A →+* B) (ν : ℕ)
    (z : A) (cA : Fin ν → A) (z' c₀ : B) (cB : Fin ν → B) (hz : T z = c₀ * z')
    (hc : ∀ i : Fin ν, T (cA i) = cB i * c₀ ^ ((i : ℕ) + 1)) :
    T (z ^ ν + ∑ i : Fin ν, cA i * z ^ (ν - ((i : ℕ) + 1))) =
      c₀ ^ ν * (z' ^ ν + ∑ i : Fin ν, cB i * z' ^ (ν - ((i : ℕ) + 1))) := by
  rw [map_add, map_pow, map_sum, hz, mul_add, Finset.mul_sum, mul_pow]
  refine congrArg _ (Finset.sum_congr rfl fun i _ => ?_)
  rw [map_mul, map_pow, hc, hz, mul_pow]
  have h1 := pow_mul_pow_sub c₀ (show (i : ℕ) + 1 ≤ ν from i.2)
  calc cB i * c₀ ^ ((i : ℕ) + 1) * (c₀ ^ (ν - ((i : ℕ) + 1)) * z' ^ (ν - ((i : ℕ) + 1))) =
      (c₀ ^ ((i : ℕ) + 1) * c₀ ^ (ν - ((i : ℕ) + 1))) * (cB i * z' ^ (ν - ((i : ℕ) + 1))) := by
        ring
    _ = c₀ ^ ν * (cB i * z' ^ (ν - ((i : ℕ) + 1))) := by rw [h1]

/-- **`x/y ∈ M₁`** (p. 267): "We claim that `x/y ∈ M₁`. In fact, if otherwise, there exists a unit
element `u` in `S` such that `x/y - u ∈ M₁`. Let `x* = x/y - u`. Let `S₁` be the monoidal transform of
`S` with center `N` (= the maximal ideal of `S`) `= M ∩ S`, such that we have a local canonical
homomorphism `S₁ → R₁`. Then `(S₁; x*)` is a regular frame of `R₁`. The element `y^{-ν}f` can be
written as `y^{-ν}f = (x*)^ν + g*_1(x*)^{ν-1} + ⋯ + g*_ν` where `g*_j ∈ S₁` for `1 ≤ j ≤ ν`. We have
`g*_1 = νu`, which is a unit of `S₁`. On the other hand, we have `(R₁)_{P₁} = R_P`, hence
`ν_{P₁(R₁)_{P₁}}(y^{-ν}f) ≥ ν`. By Theorem 1 of §3, we then have `ν_{M₁}(y^{-ν}f) ≥ ν`. Since
`(S₁; x*)` is a regular frame of `R₁`, we must have `ν_{M₁}(g*_j) ≥ j` for `1 ≤ j ≤ ν`. This
inequality for `j = 1` contradicts the fact that `g*_1 = νu` which is a unit in `R₁`."

Here `ξ` is `x/y` (`x = yξ` in `R₁`).  Gap filled: "Then `(S₁; x*)` is a regular frame of `R₁`":
`R` is complete, so `(S; x - uy)` is a regular frame of `R` (`RegularFrame.shift`), and
`x* = (x - uy)/y ∈ M₁`; its frame transform in `R₁` (the criterion of p. 254,
`RegularFrame.exists_frameTransform_of_mem_maximalIdeal`) is `(S₁; x*)` up to a unit of `S₁` in
the denominator.  "`g*_j ∈ S₁`" uses `g'_j ∈ N^j` for the coefficients `g'_j` of `f` in `x - uy`
(Theorem 1 of §3 and the frame `(S; x - uy)`). -/
theorem mem_maximalIdeal_of_toRing_eq_xR_mul [Hironaka.HironakaCitedResults.{u}] [IsAdicComplete (maximalIdeal R) R]
    (F : RegularFrame R) (hr : F.r = 1) (x : R) (hx : ∀ j, F.z j = x)
    [CharZero (ResidueField F.S)] (ν : ℕ) (hν : 0 < ν) (c : Fin ν → F.S)
    (hc0 : c ⟨0, hν⟩ = 0) (P : Ideal R) [P.IsPrime]
    (hP : (ν : ℕ∞) ≤ Ideal.ordElem (P.map (algebraMap R (Localization.AtPrime P)))
      (algebraMap R (Localization.AtPrime P)
        (x ^ ν + ∑ i : Fin ν, algebraMap F.S R (c i) * x ^ (ν - ((i : ℕ) + 1)))))
    (T : MonoidalTransform R (maximalIdeal R)) [IsRegularLocalRing T.ring]
    (y : F.S) (hTy : T.x = algebraMap F.S R y)
    (hrat : Function.Surjective (ResidueField.map T.toRing))
    (P' : Ideal T.ring) [P'.IsPrime] (hP' : P = P'.comap T.toRing)
    (hloc : Function.Bijective (Localization.localRingHom P P' T.toRing hP'))
    (hMP' : ¬ (maximalIdeal R).map T.toRing ≤ P')
    (ξ : T.ring) (hξ : T.toRing x = T.xR * ξ) : ξ ∈ maximalIdeal T.ring := by
  classical
  set a := algebraMap F.S R with ha
  set f := x ^ ν + ∑ i : Fin ν, a (c i) * x ^ (ν - ((i : ℕ) + 1)) with hfdef
  have hxM := (F.mem_maximalIdeal_and_ne_zero hr hx).1
  have hyN : y ∈ maximalIdeal F.S := by
    have h1 : a y ∈ maximalIdeal R := hTy ▸ T.x_mem
    exact (IsLocalRing.mem_maximalIdeal _).mpr fun hu =>
      (IsLocalRing.mem_maximalIdeal _).mp h1 (hu.map a)
  have hTxR : T.xR = T.toRing (a y) := by rw [MonoidalTransform.xR, hTy]
  -- "there exists a unit element `u` in `S` such that `x/y - u ∈ M₁`"
  by_contra hξM
  obtain ⟨r₀, hr₀⟩ := hrat (residue T.ring ξ)
  obtain ⟨s₀, hs₀⟩ := F.residueField_map_algebraMap_bijective.2 r₀
  obtain ⟨u, rfl⟩ := IsLocalRing.residue_surjective s₀
  have hres : residue T.ring (T.toRing (a u)) = residue T.ring ξ := by
    rw [← hr₀, ← hs₀, ResidueField.map_residue, ResidueField.map_residue]
  have hu : IsUnit u := by
    by_contra hnu
    have huN : u ∈ maximalIdeal F.S := hnu
    apply hξM
    rw [← IsLocalRing.residue_eq_zero_iff, ← hres, IsLocalRing.residue_eq_zero_iff]
    exact (IsLocalRing.mem_maximalIdeal _).mpr fun hu' =>
      (IsLocalRing.mem_maximalIdeal _).mp huN (isUnit_of_map_unit _ _
        (isUnit_of_map_unit T.toRing _ hu'))
  set ζ := ξ - T.toRing (a u) with hζdef
  have hζM : ζ ∈ maximalIdeal T.ring := by
    rw [← IsLocalRing.residue_eq_zero_iff, hζdef, map_sub, hres, sub_self]
  -- "Let `x* = x/y - u`": `(S; x - uy)` is a regular frame of `R` (`R` complete)
  have huyN : u * y ∈ maximalIdeal F.S := Ideal.mul_mem_left _ _ hyN
  set G := F.shift hr hx (u * y) huyN with hG
  set z := x - a (u * y) with hz
  have hzM : z ∈ maximalIdeal R := by
    refine sub_mem hxM ?_
    exact (IsLocalRing.mem_maximalIdeal _).mpr fun h1 =>
      (IsLocalRing.mem_maximalIdeal _).mp huyN (isUnit_of_map_unit a _ h1)
  have hζ : T.toRing z = T.xR * ζ := by
    rw [hz, map_sub, hξ, hTxR, hζdef, map_mul, map_mul]
    ring
  have : IsRegularLocalRing (R ⧸ maximalIdeal R) := by
    let _ : Field (R ⧸ maximalIdeal R) := Ideal.Quotient.field _
    infer_instance
  -- "Then `(S₁; x*)` is a regular frame of `R₁`."
  obtain ⟨F', z', c₀, hF'r, hF'z, hspan, hTz, hc₀, hdivn⟩ :=
    RegularFrame.exists_frameTransform_of_mem_maximalIdeal G z (fun _ => rfl) rfl
      (maximalIdeal R) hzM T ζ hζ hζM
  -- "`y^{-ν}f = (x*)^ν + g*_1(x*)^{ν-1} + ⋯ + g*_ν` … We have `g*_1 = νu`"
  obtain ⟨c', hc'0, hshift⟩ := exists_framePoly_shift ν hν c (u * y)
  rw [hc0, add_zero] at hc'0
  have hfz := hshift a x
  rw [← hz] at hfz
  -- the coefficients `g'_j` of `f` in `z` lie in `N^j` (Theorem 1 of §3: `ν_M(f) ≥ ν`)
  have hfM : f ∈ maximalIdeal R ^ ν :=
    Ideal.mem_pow_of_le_ordElem (hP.trans (Ideal.ordElem_localization_le_ordElem_maximalIdeal P f))
  have hcN : ∀ i : Fin ν, c' i ∈ maximalIdeal F.S ^ ((i : ℕ) + 1) := by
    intro i
    have h1 : z ^ ν + ∑ i : Fin ν, algebraMap G.S R (c' i) * z ^ (ν - ((i : ℕ) + 1)) ∈
        maximalIdeal R ^ ν := by
      have := hfM
      rw [hfdef, hfz] at this
      exact this
    exact coeff_mem_maximalIdeal_pow_of_mem_pow G rfl z (fun _ => rfl) ν c' h1 i
  have hcomapN : (maximalIdeal R).comap a = maximalIdeal F.S := by
    ext s
    simp only [Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    exact not_congr ⟨fun hu => isUnit_of_map_unit _ _ hu, fun hu => hu.map _⟩
  have hdiv : ∀ i : Fin ν, ∃ d : F'.S, T.toRing (a (c' i)) =
      algebraMap F'.S T.ring d * (algebraMap F'.S T.ring c₀) ^ ((i : ℕ) + 1) := fun i =>
    hdivn _ (c' i) (by have := hcN i; rw [← hcomapN] at this; exact this)
  choose d hd using hdiv
  set f' := z' ^ ν + ∑ i : Fin ν, algebraMap F'.S T.ring (d i) * z' ^ (ν - ((i : ℕ) + 1))
    with hf'def
  have hTf : T.toRing f = (algebraMap F'.S T.ring c₀) ^ ν * f' := by
    rw [hfdef, hfz]
    exact toRing_framePoly_eq T.toRing ν z (fun i => a (c' i)) z' _ _ hTz hd
  -- "we have `(R₁)_{P₁} = R_P`, hence `ν_{P₁(R₁)_{P₁}}(y^{-ν}f) ≥ ν`"
  have hc₀P' : algebraMap F'.S T.ring c₀ ∉ P' := by
    intro h
    apply hMP'
    rw [← hspan, Ideal.span_le, Set.singleton_subset_iff]
    exact h
  have hP'f := le_ordElem_of_localRingHom_bijective P P' T.toRing hP' hloc f ν hP f' _ hc₀P' hTf
  -- "By Theorem 1 of §3, we then have `ν_{M₁}(y^{-ν}f) ≥ ν`."
  have hM₁ : f' ∈ maximalIdeal T.ring ^ ν :=
    Ideal.mem_pow_of_le_ordElem (hP'f.trans (Ideal.ordElem_localization_le_ordElem_maximalIdeal P' f'))
  -- "Since `(S₁; x*)` is a regular frame of `R₁`, we must have `ν_{M₁}(g*_j) ≥ j`"
  have hd0 := coeff_mem_maximalIdeal_pow_of_mem_pow F' hF'r z' hF'z ν d hM₁ ⟨0, hν⟩
  rw [zero_add, pow_one] at hd0
  -- "This inequality for `j = 1` contradicts the fact that `g*_1 = νu` which is a unit"
  have hassoc : Associated (algebraMap F'.S T.ring c₀) T.xR := by
    rw [← Ideal.span_singleton_eq_span_singleton, hspan, T.span_xR_eq_map]
  obtain ⟨ε, hε⟩ := hassoc
  have hc₀0 : algebraMap F'.S T.ring c₀ ≠ 0 := fun h0 =>
    hc₀ (F'.algebraMap_injective (h0.trans (map_zero _).symm))
  have hd0eq : algebraMap F'.S T.ring (d ⟨0, hν⟩) = (ν : T.ring) * T.toRing (a u) * ↑ε := by
    have h1 := hd ⟨0, hν⟩
    rw [hc'0, zero_add, pow_one] at h1
    simp only [map_mul, map_natCast] at h1
    rw [← hTxR, ← hε] at h1
    apply mul_right_cancel₀ hc₀0
    rw [← h1]
    ring
  have hνu : IsUnit (ν : T.ring) := by
    have := (isUnit_natCast_of_charZero_residueField F.S hν.ne').map (T.toRing.comp a)
    rwa [map_natCast] at this
  have hunit : IsUnit (algebraMap F'.S T.ring (d ⟨0, hν⟩)) := by
    rw [hd0eq]
    exact (hνu.mul ((hu.map a).map T.toRing)).mul ε.isUnit
  exact (IsLocalRing.mem_maximalIdeal _).mp hd0 (isUnit_of_map_unit _ _ hunit)


/-- p. 267: "Now that we have `x₁ = x/y ∈ M₁`, the assumptions of the lemma remain valid if we
replace `(R, S, x, f, P)` by `(R₁, S₁, x₁, f₁, P₁)` where `f₁ = y^{-ν}f`. Note that if we can prove
`x₁ ∈ P₁`, then it follows that `x ∈ P`, because `(R₁)_{P₁} = R_P`."

Gap filled ("the assumptions of the lemma remain valid", and the existence of `S₁` with a local
canonical homomorphism `S₁ → R₁` making `(S₁; x₁)` a regular frame): the frame transform of
`(S; x)` in `R₁` (the criterion of p. 254, `RegularFrame.exists_frameTransform_of_mem_maximalIdeal`)
is a regular frame `(S₁; x₁)` of `R₁` with a denominator `c₀ ∈ S₁` (`c₀R₁ = MR₁ = yR₁`, `x = c₀x₁`);
the coefficients `c_i ∈ N^{i+1}` of `f` are `c'_ic₀^{i+1}` with `c'_i ∈ S₁` (so `f = c₀^ν f₁` with
`f₁ = x₁^ν + Σ c'_i x₁^{ν-(i+1)}`, `c'_0 = 0`); `ν_{P₁(R₁)_{P₁}}(f₁) ≥ ν` since `(R₁)_{P₁} = R_P`;
and the residue field of `S₁` is that of `S` (`R₁` is residually rational over `R`). -/
theorem exists_frameTransform_of_mem_maximalIdeal_hypotheses
    (F : RegularFrame R) (hr : F.r = 1) (x : R) (hx : ∀ j, F.z j = x)
    (ν : ℕ) (hν : 0 < ν) (c : Fin ν → F.S) (hc0 : c ⟨0, hν⟩ = 0)
    (hcN : ∀ i : Fin ν, c i ∈ maximalIdeal F.S ^ ((i : ℕ) + 1)) (P : Ideal R) [P.IsPrime]
    (hP : (ν : ℕ∞) ≤ Ideal.ordElem (P.map (algebraMap R (Localization.AtPrime P)))
      (algebraMap R (Localization.AtPrime P)
        (x ^ ν + ∑ i : Fin ν, algebraMap F.S R (c i) * x ^ (ν - ((i : ℕ) + 1)))))
    (T : MonoidalTransform R (maximalIdeal R)) [IsRegularLocalRing T.ring]
    (hrat : Function.Surjective (ResidueField.map T.toRing))
    (P' : Ideal T.ring) [P'.IsPrime] (hP' : P = P'.comap T.toRing)
    (hloc : Function.Bijective (Localization.localRingHom P P' T.toRing hP'))
    (hMP' : ¬ (maximalIdeal R).map T.toRing ≤ P')
    (ξ : T.ring) (hξ : T.toRing x = T.xR * ξ) (hξM : ξ ∈ maximalIdeal T.ring) :
    ∃ (F₁ : RegularFrame T.ring) (x₁ : T.ring) (c₁ : Fin ν → F₁.S), F₁.r = 1 ∧
      (∀ j, F₁.z j = x₁) ∧ c₁ ⟨0, hν⟩ = 0 ∧
      (ν : ℕ∞) ≤ Ideal.ordElem (P'.map (algebraMap T.ring (Localization.AtPrime P')))
        (algebraMap T.ring (Localization.AtPrime P')
          (x₁ ^ ν + ∑ i : Fin ν, algebraMap F₁.S T.ring (c₁ i) * x₁ ^ (ν - ((i : ℕ) + 1)))) ∧
      (x₁ ∈ P' → x ∈ P) ∧ Nonempty (ResidueField F.S ≃+* ResidueField F₁.S) := by
  classical
  set a := algebraMap F.S R with ha
  set f := x ^ ν + ∑ i : Fin ν, a (c i) * x ^ (ν - ((i : ℕ) + 1)) with hfdef
  have hxM := (F.mem_maximalIdeal_and_ne_zero hr hx).1
  have : IsRegularLocalRing (R ⧸ maximalIdeal R) := by
    let _ : Field (R ⧸ maximalIdeal R) := Ideal.Quotient.field _
    infer_instance
  obtain ⟨F₁, x₁, c₀, hF₁r, hF₁z, hspan, hTx, hc₀, hdivn⟩ :=
    RegularFrame.exists_frameTransform_of_mem_maximalIdeal F x hx hr (maximalIdeal R) hxM T ξ hξ
      hξM
  have hcomapN : (maximalIdeal R).comap a = maximalIdeal F.S := by
    ext s
    simp only [Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    exact not_congr ⟨fun hu => isUnit_of_map_unit _ _ hu, fun hu => hu.map _⟩
  have hdiv : ∀ i : Fin ν, ∃ d : F₁.S, T.toRing (a (c i)) =
      algebraMap F₁.S T.ring d * (algebraMap F₁.S T.ring c₀) ^ ((i : ℕ) + 1) := fun i =>
    hdivn _ (c i) (by rw [hcomapN]; exact hcN i)
  choose c₁ hc₁ using hdiv
  have hc₀0 : algebraMap F₁.S T.ring c₀ ≠ 0 := fun h0 =>
    hc₀ (F₁.algebraMap_injective (h0.trans (map_zero _).symm))
  have hc₁0 : c₁ ⟨0, hν⟩ = 0 := by
    have h1 := hc₁ ⟨0, hν⟩
    rw [hc0, map_zero, map_zero, zero_add, pow_one] at h1
    have h2 := (mul_eq_zero.mp h1.symm).resolve_right hc₀0
    exact F₁.algebraMap_injective (h2.trans (map_zero _).symm)
  have hTf : T.toRing f = (algebraMap F₁.S T.ring c₀) ^ ν *
      (x₁ ^ ν + ∑ i : Fin ν, algebraMap F₁.S T.ring (c₁ i) * x₁ ^ (ν - ((i : ℕ) + 1))) :=
    toRing_framePoly_eq T.toRing ν x (fun i => a (c i)) x₁ _ _ hTx hc₁
  have hc₀P' : algebraMap F₁.S T.ring c₀ ∉ P' := by
    intro h
    apply hMP'
    rw [← hspan, Ideal.span_le, Set.singleton_subset_iff]
    exact h
  refine ⟨F₁, x₁, c₁, hF₁r, hF₁z, hc₁0,
    le_ordElem_of_localRingHom_bijective P P' T.toRing hP' hloc f ν hP _ _ hc₀P' hTf,
    fun hx₁ => ?_, ?_⟩
  · rw [hP', Ideal.mem_comap, hTx]
    exact Ideal.mul_mem_left _ _ hx₁
  · -- `k = R/M = R₁/M₁ = S₁/N₁`
    have hbijT : Function.Bijective (ResidueField.map T.toRing) :=
      ⟨(ResidueField.map T.toRing).injective, hrat⟩
    exact ⟨((RingEquiv.ofBijective _ F.residueField_map_algebraMap_bijective).trans
      (RingEquiv.ofBijective _ hbijT)).trans
      (RingEquiv.ofBijective _ F₁.residueField_map_algebraMap_bijective).symm⟩

end Lemma22Transform

/-- The order along a prime, through `β : R₁ → R̂₁` and a prime `P̂ = ker ψ` over `P₁ = ker φ₁`
(`ψ ∘ β = φ₁`): `ν_{P₁}(g) ≥ ν` implies `ν_{P̂}(β g) ≥ ν`. -/
theorem le_ordElem_ker_of_comp_eq {A B K : Type*} [CommRing A] [IsDomain A] [CommRing B] [Field K]
    (φ : A →+* K) (β : A →+* B) (ψ : B →+* K) (hψ : ∀ a, ψ (β a) = φ a) (g : A) (ν : ℕ)
    [(RingHom.ker φ).IsPrime] [(RingHom.ker ψ).IsPrime]
    (h : (ν : ℕ∞) ≤ Ideal.ordElem ((RingHom.ker φ).map (algebraMap A
      (Localization.AtPrime (RingHom.ker φ)))) (algebraMap A (Localization.AtPrime (RingHom.ker φ)) g)) :
    (ν : ℕ∞) ≤ Ideal.ordElem ((RingHom.ker ψ).map (algebraMap B
      (Localization.AtPrime (RingHom.ker ψ)))) (algebraMap B (Localization.AtPrime (RingHom.ker ψ)) (β g)) := by
  obtain ⟨s, hs, hsg⟩ := exists_notMem_mul_mem_pow_of_le_ordElem (RingHom.ker φ) g ν h
  have hle : (RingHom.ker φ).map β ≤ RingHom.ker ψ := by
    rw [Ideal.map_le_iff_le_comap]
    intro p hp
    rw [Ideal.mem_comap, RingHom.mem_ker, hψ]
    exact hp
  refine le_ordElem_of_notMem_mul_mem_pow (RingHom.ker ψ) (s := β s) ?_ ν ?_
  · rw [RingHom.mem_ker, hψ]
    exact hs
  · have h1 := Ideal.mem_map_of_mem β hsg
    rw [Ideal.map_pow, map_mul] at h1
    exact Ideal.pow_right_mono hle ν h1


/-! ### The last stage: the induction on `φ(R) ∩ V` (p. 267) -/

section Lemma22Curve

attribute [local instance] RingHom.ker_isPrime

variable {K : Type u} [Field K] {S₀ : Type u} [CommRing S₀] [Algebra S₀ K] (V : Subalgebra S₀ K)

-- the induction runs over rings carrying both `[IsRegularLocalRing R]` and the derived `IsDomain R`
set_option linter.overlappingInstances false in
/-- **The process of p. 267 and its termination** ("If `R₁/P₁` is regular, then the proof is done.
If `R₁/P₁` is not regular, we repeat the same process as above. Since `R/P` is of dimension 1, and
its integral closure in its field of quotients is a finite `R/P`-module (by the completeness of
`R/P`) the process cannot be repeated infinitely."): the assertion of Lemma 22 for complete `R`
with algebraically closed `k`, for every prime `P = ker φ` with `φ(R) ⊆ V`, by well-founded
induction on the `S₀`-submodule `φ(R) ∩ V` of the noetherian `S₀`-module `V` (`S₀ = R₀/P₀` for the
ring `R₀` one starts from, `V` its integral closure, a valuation ring).

One step: `R/P` regular is the second stage; otherwise choose `y`
(`exists_extendsToRSOP_le_comap_span`, the correction of the paper), the monoidal transform `R₁`
(`exists_monoidalTransform_of_le_comap_span`), which is residually rational (`k` is algebraically
closed), prove `x/y ∈ M₁` (`mem_maximalIdeal_of_toRing_eq_xR_mul`), pass to `(R₁, S₁, x₁, f₁, P₁)`
(`exists_frameTransform_of_mem_maximalIdeal_hypotheses`), and, to repeat the process, which assumed
`R` complete, to the completion `R̂₁ = Ŝ₁{x₁}` with the prime `P̂₁ = ker ψ` over `P₁`, `ψ : R̂₁ → V`
extending `φ₁` (`exists_ringHom_comp_baseChangeHom_eq`; `V` is complete).  The measure strictly
increases: `φ(R) ∩ V ⊊ φ₁(R₁) ∩ V ⊆ ψ(R̂₁) ∩ V`. -/
theorem mem_ker_of_curveImage_eq [Hironaka.HironakaCitedResults.{u}] [ValuationRing V] [Module.Finite S₀ V] [IsNoetherianRing S₀]
    [IsAdicComplete (maximalIdeal V) V] (N : Submodule S₀ V) :
    ∀ {R : Type u} [CommRing R] [IsRegularLocalRing R] [IsAdicComplete (maximalIdeal R) R]
      (F : RegularFrame R) (_hr : F.r = 1) (x : R) (_hx : ∀ j, F.z j = x)
      [IsAlgClosed (ResidueField F.S)] [CharZero (ResidueField F.S)] (ν : ℕ) (hν : 0 < ν)
      (c : Fin ν → F.S) (_hc0 : c ⟨0, hν⟩ = 0) (φ : R →+* K) (_hφV : ∀ r, φ r ∈ V)
      (hφS : ∀ s, algebraMap S₀ K s ∈ φ.range)
      (_hP : (ν : ℕ∞) ≤ Ideal.ordElem ((RingHom.ker φ).map
        (algebraMap R (Localization.AtPrime (RingHom.ker φ))))
        (algebraMap R (Localization.AtPrime (RingHom.ker φ))
          (x ^ ν + ∑ i : Fin ν, algebraMap F.S R (c i) * x ^ (ν - ((i : ℕ) + 1))))),
      curveImage V φ hφS = N → x ∈ RingHom.ker φ := by
  induction N using WellFoundedGT.induction with
  | _ N ih =>
  intro R _ _ _ F hr x hx _ _ ν hν c hc0 φ hφV hφS hP hN
  classical
  have : IsDomain R := isDomain_of_isRegularLocalRing R
  set P := RingHom.ker φ with hPdef
  set a := algebraMap F.S R with ha
  set f := x ^ ν + ∑ i : Fin ν, a (c i) * x ^ (ν - ((i : ℕ) + 1)) with hfdef
  -- "Hence, if `R₁/P₁` is regular, then the proof is done" (the second stage)
  by_cases hreg : IsRegularLocalRing (R ⧸ P)
  · exact mem_prime_of_isRegularLocalRing_quotient F hr x hx ν hν c hc0 P hreg hP
  by_cases hxP : x ∈ P
  · exact hxP
  have hxφ : φ x ≠ 0 := fun h => hxP (RingHom.mem_ker.mpr h)
  have hxM := (F.mem_maximalIdeal_and_ne_zero hr hx).1
  -- `f ∈ P`, and `c_i ∈ N^{i+1}` (Theorem 1 of §3: `ν_M(f) ≥ ν`)
  have hfP : φ f = 0 := by
    obtain ⟨s, hs, hsf⟩ := exists_notMem_mul_mem_pow_of_le_ordElem P f ν hP
    have h1 : s * f ∈ P := Ideal.pow_le_self hν.ne' hsf
    exact RingHom.mem_ker.mp (((inferInstance : P.IsPrime).mem_or_mem h1).resolve_left hs)
  have hfM : f ∈ maximalIdeal R ^ ν :=
    Ideal.mem_pow_of_le_ordElem (hP.trans (Ideal.ordElem_localization_le_ordElem_maximalIdeal P f))
  have hcN := coeff_mem_maximalIdeal_pow_of_mem_pow F hr x hx ν c hfM
  -- "So we take such an element `y` of `S`" (with the least value in `V`: correction)
  obtain ⟨y, hyrsop, hy0, hdiv⟩ :=
    exists_extendsToRSOP_le_comap_span V F hr hx φ hφV hxφ hreg ν c hcN hfP
  have hyM : a y ∈ maximalIdeal R := by
    have hyN := hyrsop.mem_maximalIdeal (Finset.mem_singleton_self y)
    exact (IsLocalRing.mem_maximalIdeal _).mpr fun hu =>
      (IsLocalRing.mem_maximalIdeal _).mp hyN (isUnit_of_map_unit a _ hu)
  -- "Let `R₁` be a monoidal transform of `R` with center `M` such that: `(y)R₁ = MR₁`,
  -- `R_P ⊇ R₁`, and `R₁` is residually algebraic (hence, rational) over `R`."
  obtain ⟨t, φ', hP', hty, hloc, halg, hreg1, hφ'V, hφ'S, hlt⟩ :=
    exists_monoidalTransform_of_le_comap_span V φ hφV hφS rfl hreg (a y) hyM hy0 hdiv
  have := hreg1
  have : IsAlgClosed (ResidueField R) := IsAlgClosed.of_ringEquiv _ _
    (RingEquiv.ofBijective _ F.residueField_map_algebraMap_bijective)
  have hrat : Function.Surjective (ResidueField.map t.toRing) := by
    let _ : Algebra (ResidueField R) (ResidueField t.ring) := (ResidueField.map t.toRing).toAlgebra
    have : Algebra.IsAlgebraic (ResidueField R) (ResidueField t.ring) := halg
    exact (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := ResidueField R)
      (K := ResidueField t.ring)).2
  have hMP' : ¬ (maximalIdeal R).map t.toRing ≤ RingHom.ker φ' := by
    intro h
    apply hreg
    have hMP : maximalIdeal R ≤ P := fun m hm => by
      have := Ideal.map_le_iff_le_comap.mp h hm
      rw [← hP'] at this
      exact this
    rw [le_antisymm (le_maximalIdeal (inferInstance : P.IsPrime).ne_top) hMP]
    let _ : Field (R ⧸ maximalIdeal R) := Ideal.Quotient.field _
    infer_instance
  obtain ⟨ξ, hξ⟩ : ∃ ξ, t.toRing x = t.xR * ξ := by
    have : t.toRing x ∈ Ideal.span {t.xR} := by
      rw [t.span_xR_eq_map]; exact Ideal.mem_map_of_mem _ hxM
    obtain ⟨ξ, hξ⟩ := Ideal.mem_span_singleton'.mp this
    exact ⟨ξ, by rw [← hξ, mul_comm]⟩
  -- "We claim that `x/y ∈ M₁`."
  have hξM := mem_maximalIdeal_of_toRing_eq_xR_mul F hr x hx ν hν c hc0 P hP t y hty hrat
    (RingHom.ker φ') hP' hloc hMP' ξ hξ
  -- "the assumptions of the lemma remain valid if we replace `(R, S, x, f, P)` by
  -- `(R₁, S₁, x₁, f₁, P₁)`"
  obtain ⟨F₁, x₁, c₁, hF₁r, hF₁z, hc₁0, hP₁, hx₁P, ⟨eres⟩⟩ :=
    exists_frameTransform_of_mem_maximalIdeal_hypotheses F hr x hx ν hν c hc0 hcN P hP t hrat
      (RingHom.ker φ') hP' hloc hMP' ξ hξ hξM
  have : IsAlgClosed (ResidueField F₁.S) := IsAlgClosed.of_ringEquiv _ _ eres
  have : CharZero (ResidueField F₁.S) := by
    let _ : Algebra (ResidueField F.S) (ResidueField F₁.S) := eres.toRingHom.toAlgebra
    exact charZero_of_injective_algebraMap eres.injective
  -- "we repeat the same process as above": the completion `R̂₁ = Ŝ₁{x₁}` and `P̂₁ = ker ψ`
  set Sh := AdicCompletion (maximalIdeal F₁.S) F₁.S
  have : IsRegularLocalRing Sh := isRegularLocalRing_adicCompletion_of_isRegularLocalRing F₁.S
  have : IsAdicComplete (maximalIdeal Sh) Sh := isAdicComplete_maximalIdeal_adicCompletion F₁.S
  set ι := algebraMap F₁.S Sh with hιdef
  set B := MvPowerSeries (Fin F₁.r) Sh
  set β := F₁.baseChangeHom ι with hβdef
  have hφ'loc : maximalIdeal t.ring ≤ (maximalIdeal V).comap (φ'.codRestrict V hφ'V) :=
    (comap_maximalIdeal_codRestrict V φ' hφ'V hφ'S).ge
  obtain ⟨ψV, hψV⟩ := exists_ringHom_comp_baseChangeHom_eq F₁ (φ'.codRestrict V hφ'V) hφ'loc
  set ψ : B →+* K := V.val.toRingHom.comp ψV with hψdef
  have hψ : ∀ r, ψ (β r) = φ' r := fun r => congrArg Subtype.val (hψV r)
  have hψV' : ∀ b, ψ b ∈ V := fun b => (ψV b).2
  have hψS : ∀ s, algebraMap S₀ K s ∈ ψ.range := fun s => by
    obtain ⟨r, hr'⟩ := hφ'S s
    exact ⟨β r, (hψ r).trans hr'⟩
  have hlt' : N < curveImage V ψ hψS := by
    refine lt_of_lt_of_le (hN ▸ hlt) fun v hv => ?_
    obtain ⟨r, hr'⟩ := hv
    exact ⟨β r, (hψ r).trans hr'⟩
  -- the assumptions for `(R̂₁, Ŝ₁, x₁, f₁, P̂₁)`
  have : IsAdicComplete (maximalIdeal B) B := F₁.isAdicComplete_baseChange
  set G := F₁.baseChange Sh with hGdef
  have : Unique (Fin F₁.r) := Equiv.unique (finCongr hF₁r)
  set j₀ : Fin F₁.r := default
  have hGx : ∀ j, G.z j = MvPowerSeries.X j₀ := fun j =>
    show MvPowerSeries.X (σ := Fin F₁.r) (R := Sh) j = _ from
      congrArg _ (Subsingleton.elim (α := Fin F₁.r) j j₀)
  have : IsAlgClosed (ResidueField Sh) := IsAlgClosed.of_ringEquiv _ _
    (RingEquiv.ofBijective _ (AdicCompletion.residueField_map_bijective F₁.S))
  have : CharZero (ResidueField Sh) := charZero_residueField_of_isLocalHom ι
  have : IsAlgClosed (ResidueField G.S) := ‹IsAlgClosed (ResidueField Sh)›
  have : CharZero (ResidueField G.S) := ‹CharZero (ResidueField Sh)›
  let c' : Fin ν → G.S := fun i => ι (c₁ i)
  have hβx₁ : β x₁ = MvPowerSeries.X j₀ := by rw [← hF₁z j₀]; exact F₁.baseChangeHom_z ι j₀
  have hβf : β (x₁ ^ ν + ∑ i : Fin ν, algebraMap F₁.S t.ring (c₁ i) * x₁ ^ (ν - ((i : ℕ) + 1))) =
      MvPowerSeries.X j₀ ^ ν + ∑ i : Fin ν, algebraMap G.S B (c' i) *
        MvPowerSeries.X j₀ ^ (ν - ((i : ℕ) + 1)) := by
    rw [map_add, map_pow, hβx₁, map_sum]
    refine congrArg _ (Finset.sum_congr rfl fun i _ => ?_)
    rw [map_mul, map_pow, hβx₁, F₁.baseChangeHom_algebraMap]
    rfl
  have hPh := le_ordElem_ker_of_comp_eq φ' β ψ hψ _ ν hP₁
  rw [hβf] at hPh
  -- the induction hypothesis
  have hX := ih _ hlt' G hF₁r (MvPowerSeries.X j₀) hGx ν hν c'
    (show ι (c₁ ⟨0, hν⟩) = 0 by rw [hc₁0, map_zero]) ψ hψV' hψS hPh rfl
  -- "Note that if we can prove `x₁ ∈ P₁`, then it follows that `x ∈ P`"
  apply hx₁P
  rw [RingHom.mem_ker, ← hψ, hβx₁]
  exact hX

set_option linter.overlappingInstances false in
/-- `mem_ker_of_curveImage_eq` for a prime `P` given with `ker φ = P`. -/
theorem mem_prime_of_ker_eq [Hironaka.HironakaCitedResults.{u}] [ValuationRing V] [Module.Finite S₀ V] [IsNoetherianRing S₀]
    [IsAdicComplete (maximalIdeal V) V] {R : Type u} [CommRing R] [IsRegularLocalRing R]
    [IsAdicComplete (maximalIdeal R) R] (F : RegularFrame R) (hr : F.r = 1) (x : R)
    (hx : ∀ j, F.z j = x) [IsAlgClosed (ResidueField F.S)] [CharZero (ResidueField F.S)]
    (ν : ℕ) (hν : 0 < ν) (c : Fin ν → F.S) (hc0 : c ⟨0, hν⟩ = 0) (φ : R →+* K)
    (hφV : ∀ r, φ r ∈ V) (hφS : ∀ s, algebraMap S₀ K s ∈ φ.range) (P : Ideal R) [P.IsPrime]
    (hker : RingHom.ker φ = P)
    (hP : (ν : ℕ∞) ≤ Ideal.ordElem (P.map (algebraMap R (Localization.AtPrime P)))
      (algebraMap R (Localization.AtPrime P)
        (x ^ ν + ∑ i : Fin ν, algebraMap F.S R (c i) * x ^ (ν - ((i : ℕ) + 1))))) : x ∈ P := by
  subst hker
  exact mem_ker_of_curveImage_eq V _ F hr x hx ν hν c hc0 φ hφV hφS hP rfl

end Lemma22Curve


/-! ### The last stage: complete `R`, `k` algebraically closed; the reduction (pp. 266–267) -/

section Lemma22Complete

variable {R : Type u} [CommRing R] [IsRegularLocalRing R]

set_option linter.overlappingInstances false in
/-- The last stage of Lemma 22 for `dim R/P ≤ 1` (p. 266–267: "So we shall assume this"): `R/P` is a
complete local domain of dimension `≤ 1`, its integral closure `V` in its field of quotients is a
finite `R/P`-module ("by the completeness of `R/P`": the cited leaf
`curve_finite_integralClosure`, Nagata), hence a valuation ring (`curve_valuationRing_integralClosure`),
complete; the process of p. 267 runs with the measure `φ(R) ∩ V` (`mem_ker_of_curveImage_eq`). -/
theorem mem_prime_of_isAdicComplete_of_ringKrullDim_le_one [Hironaka.HironakaCitedResults.{u}] [IsAdicComplete (maximalIdeal R) R]
    (F : RegularFrame R) (hr : F.r = 1) (x : R) (hx : ∀ j, F.z j = x)
    [IsAlgClosed (ResidueField F.S)] [CharZero (ResidueField F.S)] (ν : ℕ) (hν : 0 < ν)
    (c : Fin ν → F.S) (hc0 : c ⟨0, hν⟩ = 0) (P : Ideal R) [P.IsPrime]
    (hdim : ringKrullDim (R ⧸ P) ≤ 1)
    (hP : (ν : ℕ∞) ≤ Ideal.ordElem (P.map (algebraMap R (Localization.AtPrime P)))
      (algebraMap R (Localization.AtPrime P)
        (x ^ ν + ∑ i : Fin ν, algebraMap F.S R (c i) * x ^ (ν - ((i : ℕ) + 1))))) : x ∈ P := by
  have : IsLocalRing (R ⧸ P) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk P) Ideal.Quotient.mk_surjective
  have : IsAdicComplete (maximalIdeal (R ⧸ P)) (R ⧸ P) := by
    have : IsAdicComplete (maximalIdeal R) (R ⧸ P) := curve_isAdicComplete_of_finite _ _
    have h := curve_isAdicComplete_map (B := R ⧸ P) (maximalIdeal R)
    rwa [Ideal.Quotient.algebraMap_eq, IsLocalRing.map_maximalIdeal_of_surjective _
      Ideal.Quotient.mk_surjective] at h
  -- "its integral closure in its field of quotients is a finite `R/P`-module"
  set V := integralClosure (R ⧸ P) (FractionRing (R ⧸ P))
  have : Module.Finite (R ⧸ P) V := curve_finite_integralClosure _
  have : ValuationRing V := curve_valuationRing_integralClosure _ hdim
  have : IsAdicComplete (maximalIdeal V) V :=
    isAdicComplete_maximalIdeal_of_finite (S₀ := R ⧸ P) (V := V)
  let φ : R →+* FractionRing (R ⧸ P) :=
    (algebraMap (R ⧸ P) (FractionRing (R ⧸ P))).comp (Ideal.Quotient.mk P)
  have hφV : ∀ r, φ r ∈ V := fun r => V.algebraMap_mem _
  have hφS : ∀ s, algebraMap (R ⧸ P) (FractionRing (R ⧸ P)) s ∈ φ.range := by
    intro s
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective s
    exact ⟨r, rfl⟩
  have hker : RingHom.ker φ = P := by
    rw [RingHom.ker_comp_of_injective _ (IsFractionRing.injective _ _), Ideal.mk_ker]
  exact mem_prime_of_ker_eq V F hr x hx ν hν c hc0 φ hφV hφS P hker hP

set_option linter.overlappingInstances false in
/-- **Lemma 22, the case `k` algebraically closed and `R` complete** (pp. 266–267): "We shall assume
that `k` is algebraically closed and that `R` is complete. We shall reduce the proof in this case to
the case in which `R/P` is regular. First of all, by induction on `dim R/P`, we can reduce the proof
to the case in which `dim R/P = 1`."

Gap filled ("by induction on `dim R/P`"): induction on the primes of `R` from the top.  If
`dim R/P ≥ 2`, every prime `P' ⊋ P` satisfies `ν_{P'R_{P'}}(f) ≥ ν_{PR_P}(f) ≥ ν` (Theorem 1 of §3
for `R_{P'}`, `Ideal.ordElem_localization_mono`), hence contains `x` by induction, and the primes
`P' ⊋ P` intersect in `P` (`exists_isPrime_ne_bot_notMem`, Krull's principal ideal theorem); the
ring `R`, complete with residue field `k`, is not changed. -/
theorem mem_prime_of_isAdicComplete_of_isAlgClosed [Hironaka.HironakaCitedResults.{u}] [IsAdicComplete (maximalIdeal R) R]
    (F : RegularFrame R) (hr : F.r = 1) (x : R) (hx : ∀ j, F.z j = x)
    [IsAlgClosed (ResidueField F.S)] [CharZero (ResidueField F.S)] (ν : ℕ) (hν : 0 < ν)
    (c : Fin ν → F.S) (hc0 : c ⟨0, hν⟩ = 0) (P : Ideal R) :
    ∀ _ : P.IsPrime, (ν : ℕ∞) ≤ Ideal.ordElem (P.map (algebraMap R (Localization.AtPrime P)))
      (algebraMap R (Localization.AtPrime P)
        (x ^ ν + ∑ i : Fin ν, algebraMap F.S R (c i) * x ^ (ν - ((i : ℕ) + 1)))) → x ∈ P := by
  induction P using WellFoundedGT.induction with
  | _ P ih =>
  intro hPp hP
  by_cases hdim : ringKrullDim (R ⧸ P) ≤ 1
  · exact mem_prime_of_isAdicComplete_of_ringKrullDim_le_one F hr x hx ν hν c hc0 P hdim hP
  -- `dim R/P ≥ 2`: `x` lies in every prime `P' ⊋ P`, and these intersect in `P`
  by_contra hxP
  have : IsDomain (R ⧸ P) := Ideal.Quotient.isDomain P
  have : IsLocalRing (R ⧸ P) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk P) Ideal.Quotient.mk_surjective
  have hx0 : Ideal.Quotient.mk P x ≠ 0 := fun h => hxP (Ideal.Quotient.eq_zero_iff_mem.mp h)
  obtain ⟨q, hq, hq0, hxq⟩ := exists_isPrime_ne_bot_notMem hdim hx0
  set P' := q.comap (Ideal.Quotient.mk P) with hP'def
  have hP'p : P'.IsPrime := Ideal.comap_isPrime _ _
  have hPP' : P ≤ P' := fun p hp => by
    rw [hP'def, Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.mpr hp]
    exact zero_mem _
  have hlt : P < P' := by
    refine lt_of_le_of_ne hPP' fun heq => hq0 ?_
    have := Ideal.map_comap_of_surjective (Ideal.Quotient.mk P) Ideal.Quotient.mk_surjective q
    rw [← hP'def, ← heq, Ideal.map_quotient_self] at this
    exact this.symm
  have hP' := hP.trans (Ideal.ordElem_localization_mono P P' hPP' _)
  exact hxq (ih P' hlt hP'p hP')

end Lemma22Complete

/-! ### The theorem -/

section Lemma22

variable {R : Type u} [CommRing R] [IsRegularLocalRing R]

/-- `x^ν + Σ_{2 ≤ j ≤ ν} g_j x^{ν-j} = x^ν + Σ_{i<ν} c_i x^{ν-(i+1)}` with `c₀ = 0`, `c_i = g_{i+1}`. -/
theorem sum_Icc_two_eq_sum_fin {S B : Type*} [CommRing S] [CommRing B] (φ : S →+* B) (ν : ℕ)
    (hν : 0 < ν) (g : ℕ → S) (x : B) :
    ∑ j ∈ Finset.Icc 2 ν, φ (g j) * x ^ (ν - j) =
      ∑ i : Fin ν, φ (if (i : ℕ) = 0 then 0 else g ((i : ℕ) + 1)) * x ^ (ν - ((i : ℕ) + 1)) := by
  rw [Fin.sum_univ_eq_sum_range (fun i => φ (if i = 0 then 0 else g (i + 1)) *
    x ^ (ν - (i + 1))) ν, Finset.sum_range_eq_add_Ico _ hν]
  simp only [↓reduceIte, map_zero, zero_mul, zero_add]
  rw [← Finset.Ico_add_one_right_eq_Icc (2 : ℕ) ν,
    ← Finset.sum_Ico_add' (fun j : ℕ => φ (g j) * x ^ (ν - j)) 1 ν 1]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [ite_eq_right (by have := (Finset.mem_Ico.mp hi).1; omega)]


/-- Lemma 22, p. 265: "Let `R` be a regular local ring, `M` the maximal ideal of `R` and `(S; x)` a
regular frame of `R`. Let `f` be an element of `R` which can be written in the form
`f = x^ν + g₂x^{ν−2} + ⋯ + g_ν` (`ν > 0`) where `g_j ∈ S` for `2 ≤ j ≤ ν`. If the residue field `k`
of `S` is of characteristic zero, then `x` is contained in every prime ideal `P` in `R` such that
`ν_{PR_P}(f) ≥ ν`, where `f` is viewed as an element of `R_P`."

(Formalization notes: the regular frame `(S; x)` is a `RegularFrame` `F` with `r = 1` and
`z₁ = x`; the coefficients `g_j ∈ S` are elements of `F.S` (a family `g : ℕ → F.S` of which only
`g₂, …, g_ν` are used), mapped to `R` by the structure map; `ν_{PR_P}` is the order function of
the ideal `PR_P` of the localization `R_P`.)

The proof is the printed one (pp. 265–267), in its four stages:
`mem_prime_of_sub_mem_of_isAdicComplete` (`x - h ∈ P`, `R` complete),
`mem_prime_of_isRegularLocalRing_quotient` (`R/P` regular), the reduction below (to `k`
algebraically closed and `R` complete), and `mem_prime_of_isAdicComplete_of_isAlgClosed` (the
induction on `dim R/P` and the sequence of monoidal transforms, `mem_ker_of_curveImage_eq`).

The reduction (p. 266): "Next we shall reduce the proof to the case in which `k` is algebraically
closed and `R` is complete. We have a complete local ring `S̃` and a local monomorphism `S → S̃`
which transforms a regular system of parameters of `S` into such a system of `S̃`, and such that the
residue field of `S̃` is algebraically closed. Let `R̃ = S̃{x}`. We have a canonical local
monomorphism `R → R̃`. Let `P̃` be a prime ideal in `R̃` such that `P̃ ∩ R = P`. In fact, such `P̃`
exists because `R̃` is faithfully flat over `R`. As is easily seen, the assumptions of the lemma
remain valid if we replace `{R, (S; x), P}` by `{R̃, (S̃; x), P̃}`. Therefore, if the lemma was proved
for the case in which `k` is algebraically closed and `R` is complete, then `x ∈ P̃ ∩ R = P`."
`S̃` is `CompleteSepClosedExtension` (residue field separably closed, hence algebraically closed in
characteristic zero), `R̃ = S̃{x}` the base change of the frame (`RegularFrame.baseChange`), and
"the assumptions remain valid" is checked (gap filled): `R̃` complete, `(S̃; x)` a regular frame,
`f` of the same shape, `ν_{P̃R̃_{P̃}}(f) ≥ ν` (`sf ∈ P^ν`, `s ∉ P̃`).

Correction of the paper (p. 267, the choice of `y`): see `exists_extendsToRSOP_le_comap_span`; the
other unargued steps of the last stage are filled in `mem_prime_of_isAdicComplete_of_isAlgClosed`,
`mem_maximalIdeal_of_toRing_eq_xR_mul`, `exists_frameTransform_of_mem_maximalIdeal_hypotheses` and
`mem_ker_of_curveImage_eq`. -/
@[blueprint "lem:III.22"
  (statement := /-- Let $R$ be a regular local ring, $M$ the maximal ideal of $R$ and $(S;x)$ a
    regular frame of $R$ (\cref{def:III.9}). Let $f$ be an element of $R$ which can be written
    in the form $f=x^\nu+g_2x^{\nu-2}+\dots+g_\nu$ ($\nu>0$) where $g_j\in S$ for
    $2\le j\le\nu$. If the residue field $k$ of $S$ is of characteristic zero, then $x$ is
    contained in every prime ideal $P$ in $R$ such that $\nu_{PR_P}(f)\ge\nu$, where $f$ is
    viewed as an element of $R_P$. (Lemma 22, p.~265.) -/)
  (proof := /-- We shall first prove the assertion under the additional assumptions that there
    exists a non-unit element $h$ of $S$ such that $x-h\in P$ and that $R$ is complete. In
    fact, let $z=x-h$. We write $f$ in the form
    $$f=z^\nu+g'_1z^{\nu-1}+\dots+g'_\nu\qquad\text{with }g'_j\in S\ (1\le j\le\nu).$$
    Then $g'_1=\nu h$. Let $R'=R_P$ and $S'=S_{P\cap S}$. Obviously $(S';z)$ is a regular frame
    of $R'$. Let $P'=PR'$ and $Q'=(P\cap S)S'$. We have $P'=(z,Q')R'$. The assumption that
    $\nu_{PR_P}(f)\ge\nu$ implies that $f\in(z,Q')^\nu R'$. Hence, by the uniqueness of the
    above expression of $f$ in terms of $z$ and $g'_j\in S$, we have $\nu_{Q'}(g'_j)\ge j$ for
    $1\le j\le\nu$. In particular, $\nu h=g'_1\in P'$, hence $h\in P'\cap R=P$. Hence
    $x=z+h\in P$.

    Next we shall prove the assertion for the case in which $R/P$ is regular. In this case,
    $\nu_{PR_P}(f)\ge\nu$ is equivalent to saying that $f\in P^\nu$. Let $(w_1,\dots,w_r)$ be a
    minimal base of $P$, and $W_j$ the initial form of $w_j$ in $\operatorname{gr}_M(R)$, which
    is in $\operatorname{gr}^1_M(R)$, for $1\le j\le r$. The assumption $f\in P^\nu$ implies that
    the initial form $\varphi$ of $f$ in $\operatorname{gr}_M(R)$ is a form only in
    $W_1,\dots,W_r$. On the other hand, if $(y_1,\dots,y_s)$ is a regular system of parameters
    of $S$, and if $X$ (resp.\ $Y_j$) is the initial form of $x$ (resp.\ $y_j$) in
    $\operatorname{gr}_M(R)$, then $\varphi$ can be written as
    $$\varphi=X^\nu+\lambda_2X^{\nu-2}+\dots+\lambda_\nu,$$
    where $\lambda_j$ is a form of degree $j$ only in $Y_1,\dots,Y_s$. Comparing these two
    expressions of $\varphi$, we see that one of the $W_j$, say $W_1$, can be written as
    $$W_1=bX+\textstyle\sum_ja_jY_j$$
    where $b$ and $a_j$ are in $k$ ($=R/M$) and $b\ne0$. Let $\hat S$ and $\hat R$ be the
    completions of $S$ and $R$. Then the above result shows that $\hat R=\hat S\{w_1\}$. Hence
    we have $h\in\hat S$ such that $x-h\in(w_1)\hat R\subseteq P\hat R$. We know that $P\hat R$
    is a prime ideal in $\hat R$ and that $\nu_{PR_P}(f)\ge\nu$ implies that
    $\nu_{P\hat R_{P\hat R}}(f)\ge\nu$. Hence, by the first result, we have $x\in P\hat R$.
    Hence $x\in P\hat R\cap R=P$.

    Next we shall reduce the proof to the case in which $k$ is algebraically closed and $R$ is
    complete. We have a complete local ring $\tilde S$ and a local monomorphism $S\to\tilde S$
    which transforms a regular system of parameters of $S$ into such a system of $\tilde S$,
    and such that the residue field of $\tilde S$ is algebraically closed. Let
    $\tilde R=\tilde S\{x\}$. We have a canonical local monomorphism $R\to\tilde R$. Let
    $\tilde P$ be a prime ideal in $\tilde R$ such that $\tilde P\cap R=P$. In fact, such
    $\tilde P$ exists because $\tilde R$ is faithfully flat over $R$. As is easily seen, the
    assumptions of the lemma remain valid if we replace $\{R,(S;x),P\}$ by
    $\{\tilde R,(\tilde S;x),\tilde P\}$. Therefore, if the lemma was proved for the case in
    which $k$ is algebraically closed and $R$ is complete, then $x\in\tilde P\cap R=P$.

    We shall assume that $k$ is algebraically closed and that $R$ is complete. We shall reduce
    the proof in this case to the case in which $R/P$ is regular. First of all, by induction on
    $\dim R/P$, we can reduce the proof to the case in which $\dim R/P=1$. So we shall assume
    this. Suppose $R/P$ is not regular. Then we have $y\in S$ such that $y\notin P$, and that
    $(y)$ can be extended to a regular system of parameters of $S$. In fact, if otherwise, $P$
    should contain the maximal ideal $N$ of $S$. But $NR$ is a prime ideal, and $R/NR$ is a
    regular local ring of dimension $1$, so that $P=NR$ which is a contradiction. So we take
    such an element $y$ of $S$. Let $R_1$ be a monoidal transform of $R$ with center $M$ such
    that: $(y)R_1=MR_1$, $R_P\supseteq R_1$, and $R_1$ is residually algebraic (hence,
    rational) over $R$. Let $P_1$ be the prime ideal in $R_1$ with $R_P=(R_1)_{P_1}$ and $M_1$
    the maximal ideal of $R_1$. We claim that $x/y\in M_1$. In fact, if otherwise, there exists
    a unit element $u$ in $S$ such that $x/y-u\in M_1$. Let $x^*=x/y-u$. Let $S_1$ be the
    monoidal transform of $S$ with center $N$ ($=$ the maximal ideal of $S$) $=M\cap S$, such
    that we have a local canonical homomorphism $S_1\to R_1$. Then $(S_1;x^*)$ is a regular
    frame of $R_1$. The element $y^{-\nu}f$ can be written as
    $$y^{-\nu}f=(x^*)^\nu+g^*_1(x^*)^{\nu-1}+\dots+g^*_\nu$$
    where $g^*_j\in S_1$ for $1\le j\le\nu$. We have $g^*_1=\nu u$, which is a unit of $S_1$.
    On the other hand, we have $(R_1)_{P_1}=R_P$, hence
    $\nu_{P_1(R_1)_{P_1}}(y^{-\nu}f)\ge\nu$. By Theorem~1 of \S3 (\cref{thm:III.1}), we then
    have $\nu_{M_1}(y^{-\nu}f)\ge\nu$. Since $(S_1;x^*)$ is a regular frame of $R_1$, we must
    have $\nu_{M_1}(g^*_j)\ge j$ for $1\le j\le\nu$. This inequality for $j=1$ contradicts the
    fact that $g^*_1=\nu u$ which is a unit in $R_1$. Now that we have $x_1=x/y\in M_1$, the
    assumptions of the lemma remain valid if we replace $(R,S,x,f,P)$ by
    $(R_1,S_1,x_1,f_1,P_1)$ where $f_1=y^{-\nu}f$. Note that if we can prove $x_1\in P_1$, then
    it follows that $x\in P$, because $(R_1)_{P_1}=R_P$. Hence, if $R_1/P_1$ is regular, then
    the proof is done. If $R_1/P_1$ is not regular, we repeat the same process as above. Since
    $R/P$ is of dimension $1$, and its integral closure in its field of quotients is a finite
    $R/P$-module (by the completeness of $R/P$) the process cannot be repeated infinitely.
    \qed

    \textbf{Correction of the paper (the choice of $y$).} The text allows any $y\in S$ with $y\notin P$
    such that $(y)$ extends to a regular system of parameters of $S$; for such $y$ the monoidal
    transform $R_1$ with $(y)R_1=MR_1$ and $R_1\subseteq R_P$ need not exist. For $k=\mathbb C$, $S=k[[s,u]]$,
    $R=S\{x\}$, $f=x^2$ ($\nu=2$), $P=(x,u^2-s^3)$ (a prime, with $R/P\cong k[[s,u]]/(u^2-s^3)$ the cusp,
    and $\nu_{PR_P}(f)=2$) and $y=u$, which extends to the regular system of parameters $(u,s)$ of $S$
    (all hypotheses hold), one would need a prime
    $M_1\ni u$ of $R[M/u]$ containing $PR_P\cap R[M/u]$, but $u^2-s^3=u^2(1-(s/u)^3u)$ puts
    $1-(s/u)^3u$ there ($u$ is a unit of $R_P$), so $1\in M_1$. (For $y=s$ the transform exists.) The formalization takes $y$ among the members of a regular
    system of parameters of $S$ with $\bar y\ne0$ of least value for the valuation $v$ of the
    integral closure $V$ of $R/P$ (a discrete valuation ring); then $v(\bar x)\ge v(\bar y)$, since
    $f\in P$ and $g_j\in N^j$, so $\bar M V=\bar yV$, and the center of $V$ on $R[M/y]$ gives $R_1$
    (residually algebraic, regular, $R_P=(R_1)_{P_1}$).

    \textbf{Gaps in the paper filled.} (1) First stage: $(S;z)$ is a regular frame of $R$ because
    $R$ is complete ($R=S+(x-h)R$ by successive approximation, $S\cap(x-h)R=0$ by Krull's theorem),
    and its localization $(S';z)$ is a regular frame of $R'=R_P$ (\cref{def:IV.AB-5-frame-localization},
    using \cref{lem:regular-localization-serre}); ``by the uniqueness of the above expression'' is the
    comparison of coefficients modulo $z$ and the multiplicativity of $\nu_{P'}$. (2) Second stage:
    the element $w_1$ is an element of $P$ outside $NR+M^2$ (comparison of the two expressions of
    $\varphi$, made modulo $NR$, where $R/NR$ is a discrete valuation ring with parameter $\bar x$);
    $\hat R$ is $\hat S\{x\}$, $P\hat R$ is prime and $P\hat R\cap R=P$ (\cref{lem:III.4} and faithful
    flatness, \cref{lem:III.rsop-map-flat}); ``$\hat R=\hat S\{w_1\}$'' is used through $x-h\in(w_1)\hat R$, Weierstrass division of
    $x$ by $w_1$. (3) The reduction: $\tilde S$ has separably closed residue field
    (\cref{lem:III.5-maximal-local-extension}, then completion), algebraically closed in
    characteristic $0$; the assumptions for $\{\tilde R,(\tilde S;x),\tilde P\}$ are checked. (4) ``By
    induction on $\dim R/P$'': if $\dim R/P\ge2$, every prime $P'\supsetneq P$ has
    $\nu_{P'R_{P'}}(f)\ge\nu_{PR_P}(f)$ (\cref{thm:III.1} for $R_{P'}$), hence $x\in P'$, and these
    primes intersect in $P$ (Krull's principal ideal theorem); $R$ is not changed. (5) ``Then
    $(S_1;x^*)$ is a regular frame of $R_1$'': $(S;x-uy)$ is a regular frame of the complete ring $R$
    and $(S_1;x^*)$ is its frame transform in $R_1$ (\cref{lem:III.8-frame-transform-criterion}); the
    $g^*_j\in S_1$ because the coefficients of $f$ in $x-uy$ lie in $N^j$ (\cref{thm:III.1}). (6) ``The
    assumptions of the lemma remain valid'' for $(R_1,S_1,x_1,f_1,P_1)$: $(S_1;x_1)$ is the frame
    transform of $(S;x)$ (\cref{lem:III.8-frame-transform-criterion}), $R_1$ is regular
    (\cref{lem:III.2-monoidal-transform-regular}) and residually rational, $\nu_{P_1(R_1)_{P_1}}(f_1)\ge\nu$.
    (7) ``We repeat the same process as above'': the process assumed $R$ complete; $R_1$ is replaced by
    its completion $\hat S_1\{x_1\}$, with the prime $\hat P_1=\ker\psi$ over $P_1$, where
    $\psi\colon\hat S_1\{x_1\}\to V$ extends $R_1\to R_1/P_1\subseteq V$ ($V$ is complete). (8) ``The
    process cannot be repeated infinitely'': the $R/P$-submodule $\varphi(R_i)\cap V$ of the finite
    $R/P$-module $V$ (\cref{lem:III.1-derived-normal-ring-finite}) strictly increases, since otherwise
    $M_i\subseteq yR_i+P_i$ and $R_i/P_i$ would be regular.
 -/)
  (latexEnv := "lemma")]
theorem mem_prime_of_ordElem_localization_ge [Hironaka.HironakaCitedResults.{u}] (F : RegularFrame R) (hr : F.r = 1) (x : R)
    (hx : ∀ j, F.z j = x) [CharZero (ResidueField F.S)] (f : R) (ν : ℕ) (hν : 0 < ν)
    (g : ℕ → F.S) (hf : f = x ^ ν + ∑ j ∈ Finset.Icc 2 ν, algebraMap F.S R (g j) * x ^ (ν - j))
    (P : Ideal R) [P.IsPrime]
    (hP : (ν : ℕ∞) ≤ Ideal.ordElem (P.map (algebraMap R (Localization.AtPrime P)))
      (algebraMap R (Localization.AtPrime P) f)) :
    x ∈ P := by
  classical
  have : IsDomain R := isDomain_of_isRegularLocalRing R
  set a := algebraMap F.S R with ha
  let c : Fin ν → F.S := fun i => if (i : ℕ) = 0 then 0 else g ((i : ℕ) + 1)
  have hc0 : c ⟨0, hν⟩ = 0 := by simp [c]
  set f' := x ^ ν + ∑ i : Fin ν, a (c i) * x ^ (ν - ((i : ℕ) + 1)) with hf'def
  have hff' : f = f' := by rw [hf, sum_Icc_two_eq_sum_fin a ν hν g x]
  rw [hff'] at hP
  -- "We have a complete local ring `S̃` and a local monomorphism `S → S̃` …"
  obtain ⟨E⟩ := CompleteSepClosedExtension.nonempty F.S
  have : IsAdicComplete (maximalIdeal E.ring) E.ring := E.isAdicComplete
  -- "Let `R̃ = S̃{x}`. We have a canonical local monomorphism `R → R̃`."
  set B := MvPowerSeries (Fin F.r) E.ring
  set β := F.baseChangeHom E.hom with hβdef
  have hβ : RingHom.MapsRSOP β := F.mapsRSOP_baseChangeHom E.hom E.mapsRSOP
  -- "Let `P̃` be a prime ideal in `R̃` such that `P̃ ∩ R = P`. In fact, such `P̃` exists because `R̃`
  -- is faithfully flat over `R`."
  have hpure : (P.map β).comap β ≤ P := by
    let _ := β.toAlgebra
    have : Module.Flat R B := hβ.flat
    have : IsLocalHom (algebraMap R B) := (inferInstance : IsLocalHom β)
    have : Module.FaithfullyFlat R B := Module.FaithfullyFlat.of_flat_of_isLocalHom
    exact (Ideal.comap_map_eq_self_of_faithfullyFlat P).le
  obtain ⟨Pt, hPPt, hPt, hPtP⟩ := Ideal.exists_ideal_comap_le_prime P (P.map β) hpure
  have hcomap : Pt.comap β = P := le_antisymm hPtP (Ideal.map_le_iff_le_comap.mp hPPt)
  -- "As is easily seen, the assumptions of the lemma remain valid"
  have : CharZero (ResidueField E.ring) := E.charZero_residueField
  have : IsSepClosed (ResidueField E.ring) := E.isSepClosed
  have : IsAlgClosed (ResidueField E.ring) := inferInstance
  set G := F.baseChange E.ring with hGdef
  have : IsAdicComplete (maximalIdeal B) B := F.isAdicComplete_baseChange
  have : Unique (Fin F.r) := Equiv.unique (finCongr hr)
  set j₀ : Fin F.r := default
  have hGx : ∀ j, G.z j = MvPowerSeries.X j₀ := fun j =>
    show MvPowerSeries.X (σ := Fin F.r) (R := E.ring) j = _ from
      congrArg _ (Subsingleton.elim (α := Fin F.r) j j₀)
  have : IsAlgClosed (ResidueField G.S) := ‹IsAlgClosed (ResidueField E.ring)›
  have : CharZero (ResidueField G.S) := ‹CharZero (ResidueField E.ring)›
  let c' : Fin ν → G.S := fun i => E.hom (c i)
  have hβx : β x = MvPowerSeries.X j₀ := by rw [← hx j₀]; exact F.baseChangeHom_z E.hom j₀
  have hβf : β f' = MvPowerSeries.X j₀ ^ ν + ∑ i : Fin ν, algebraMap G.S B (c' i) *
      MvPowerSeries.X j₀ ^ (ν - ((i : ℕ) + 1)) := by
    rw [hf'def, map_add, map_pow, hβx, map_sum]
    refine congrArg _ (Finset.sum_congr rfl fun i _ => ?_)
    rw [map_mul, map_pow, hβx, F.baseChangeHom_algebraMap]
    rfl
  have hPt' : (ν : ℕ∞) ≤ Ideal.ordElem (Pt.map (algebraMap B (Localization.AtPrime Pt)))
      (algebraMap B (Localization.AtPrime Pt) (MvPowerSeries.X j₀ ^ ν +
        ∑ i : Fin ν, algebraMap G.S B (c' i) * MvPowerSeries.X j₀ ^ (ν - ((i : ℕ) + 1)))) := by
    rw [← hβf]
    obtain ⟨s, hs, hsf⟩ := exists_notMem_mul_mem_pow_of_le_ordElem P f' ν hP
    refine le_ordElem_of_notMem_mul_mem_pow Pt (s := β s) ?_ ν ?_
    · rw [← Ideal.mem_comap, hcomap]; exact hs
    · have h1 := Ideal.mem_map_of_mem β hsf
      rw [Ideal.map_pow, map_mul] at h1
      exact Ideal.pow_right_mono hPPt ν h1
  -- "Therefore, if the lemma was proved for the case in which `k` is algebraically closed and `R`
  -- is complete, then `x ∈ P̃ ∩ R = P`."
  have hX := mem_prime_of_isAdicComplete_of_isAlgClosed G hr (MvPowerSeries.X j₀) hGx ν hν c'
    (show E.hom (c ⟨0, hν⟩) = 0 by rw [hc0, map_zero]) Pt hPt hPt'
  rw [← hcomap, Ideal.mem_comap, hβx]
  exact hX

end Lemma22

end

end Hironaka
