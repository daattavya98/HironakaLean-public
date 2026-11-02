/-
Copyright (c) 2026 Daattavya Aggarwal, Minhyong Kim, Oisin Kim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daattavya Aggarwal, Minhyong Kim, Oisin Kim
-/
module

public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.AdicCompletion.RingHom
public import Architect
public import Hironaka.Compat.CompleteRationalFrameBaseChange
public import Hironaka.Compat.NagataFinite
public import Hironaka.Compat.FrameShift

/-!
# Compatibility layer: completions and valuation rings in the proof of Lemma 22 (Ch. III §10, p. 267)

The last stage of the proof of Lemma 22 (p. 267) runs through a sequence of monoidal transforms
`R ⊆ R₁ ⊆ ⋯ ⊆ R_P` with center the maximal ideals: "If `R₁/P₁` is not regular, we repeat the same
process as above. Since `R/P` is of dimension 1, and its integral closure in its field of quotients
is a finite `R/P`-module (by the completeness of `R/P`) the process cannot be repeated infinitely."
The process "as above" assumed `R` complete; the transforms `R₁` are not.  This file contains the
ring-level tools used to repeat it:

* `isAdicComplete_of_le_of_pow_le`, `isAdicComplete_maximalIdeal_of_finite`: the integral closure
  `V` of the complete one-dimensional local domain `R/P` (a valuation ring finite over `R/P`) is
  complete;
* `exists_ringHom_comp_baseChangeHom_eq`: a local homomorphism `φ : R₁ → V` extends to the completion
  `Ŝ₁{x₁}` of `R₁` (the base change of the frame `(S₁; x₁)` along `S₁ → Ŝ₁`), so that the prime
  `P₁` of `R₁` has a prime of `Ŝ₁{x₁}` over it with the same image in the field of quotients of
  `R/P`;
* `exists_notMem_mul_mem_pow_of_le_ordElem`, `le_ordElem_of_notMem_mul_mem_pow`,
  `le_ordElem_of_localRingHom_bijective`: orders `ν_{PR_P}` along primes and through the
  identifications `(R₁)_{P₁} = R_P`;
* `isIntegral_codRestrict`, `comap_maximalIdeal_codRestrict`: the center of `V` on the rings of the
  sequence.
-/

@[expose] public section

open IsLocalRing

namespace Hironaka

universe u

noncomputable section

/-! ### Completions (stage 4: "we repeat the same process as above") -/

section CompletionLift

/-- Adic completeness passes from `J` to `I` when `J ⊆ I` and `I^e ⊆ J`. -/
theorem isAdicComplete_of_le_of_pow_le {A : Type*} [CommRing A] {I J : Ideal A} (hJI : J ≤ I)
    (e : ℕ) (he : I ^ e ≤ J) [IsAdicComplete J A] : IsAdicComplete I A := by
  have he' : I ^ (e + 1) ≤ J := (Ideal.pow_le_pow_right (Nat.le_succ e)).trans he
  have hpow : ∀ n, I ^ ((e + 1) * n) ≤ J ^ n := fun n => by
    rw [pow_mul]; exact Ideal.pow_right_mono he' n
  have hJn : ∀ n, J ^ n ≤ I ^ n := fun n => Ideal.pow_right_mono hJI n
  refine { haus' := fun x hx => ?_, prec' := fun f hf => ?_ }
  · refine IsHausdorff.haus (I := J) inferInstance x fun n => ?_
    have := hx ((e + 1) * n)
    rw [sModEq_pow_iff] at this ⊢
    exact hpow n this
  · obtain ⟨L, hL⟩ := IsPrecomplete.prec' (I := J) (fun n => f ((e + 1) * n)) (by
      intro m n hmn
      have := hf (Nat.mul_le_mul_left (e + 1) hmn)
      rw [sModEq_pow_iff] at this ⊢
      exact hpow m this)
    refine ⟨L, fun n => ?_⟩
    have h1 := hf (show n ≤ (e + 1) * n by nlinarith)
    have h2 := hL n
    rw [sModEq_pow_iff] at h1 h2 ⊢
    have : f n - L = (f n - f ((e + 1) * n)) + (f ((e + 1) * n) - L) := by ring
    rw [this]
    exact add_mem h1 (hJn n h2)

/-- A local domain `V` finite over a complete noetherian local ring `S₀` is complete for its
maximal ideal (`V/M_{S₀}V` is artinian, so `M_V^e ⊆ M_{S₀}V ⊆ M_V`). -/
theorem isAdicComplete_maximalIdeal_of_finite {S₀ V : Type u} [CommRing S₀] [IsLocalRing S₀]
    [IsNoetherianRing S₀] [IsAdicComplete (maximalIdeal S₀) S₀] [CommRing V] [IsLocalRing V]
    [Algebra S₀ V] [Module.Finite S₀ V] : IsAdicComplete (maximalIdeal V) V := by
  set J := (maximalIdeal S₀).map (algebraMap S₀ V) with hJ
  have : IsAdicComplete (maximalIdeal S₀) V := curve_isAdicComplete_of_finite _ V
  have : IsAdicComplete J V := curve_isAdicComplete_map _
  have hint : Algebra.IsIntegral S₀ V := inferInstance
  have hcomap : (maximalIdeal V).comap (algebraMap S₀ V) = maximalIdeal S₀ :=
    IsLocalRing.eq_maximalIdeal (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal
      (algebraMap S₀ V) (fun v => Algebra.IsIntegral.isIntegral v) _)
  have hJV : J ≤ maximalIdeal V := by rw [hJ, Ideal.map_le_iff_le_comap, hcomap]
  have hJtop : J ≠ ⊤ := fun h => (maximalIdeal.isMaximal V).ne_top (top_le_iff.mp (h ▸ hJV))
  have : Nontrivial (V ⧸ J) := Ideal.Quotient.nontrivial_iff.mpr hJtop
  have : IsLocalRing (V ⧸ J) := IsLocalRing.of_surjective' _ Ideal.Quotient.mk_surjective
  have hart : IsArtinianRing (V ⧸ J) := by
    let _ : Field (S₀ ⧸ maximalIdeal S₀) := Ideal.Quotient.field _
    exact IsArtinianRing.of_finite (S₀ ⧸ maximalIdeal S₀) (V ⧸ J)
  obtain ⟨e, he⟩ := IsArtinianRing.isNilpotent_jacobson_bot (R := V ⧸ J)
  refine isAdicComplete_of_le_of_pow_le hJV e ?_
  have hjac : (⊥ : Ideal (V ⧸ J)).jacobson = (maximalIdeal V).map (Ideal.Quotient.mk J) := by
    rw [IsLocalRing.jacobson_eq_maximalIdeal _ bot_ne_top,
      IsLocalRing.map_maximalIdeal_of_surjective _ Ideal.Quotient.mk_surjective]
  rw [hjac, ← Ideal.map_pow] at he
  intro v hv
  have h1 := Ideal.mem_map_of_mem (Ideal.Quotient.mk J) hv
  rw [he] at h1
  have h2 : Ideal.Quotient.mk J v ∈ (⊥ : Ideal (V ⧸ J)) := h1
  exact Ideal.Quotient.eq_zero_iff_mem.mp ((Submodule.mem_bot _).mp h2)

/-- **The extension of a local homomorphism `R → V` to the completion `Ŝ{z}` of `R`**: for a
regular frame `(S; z)` of `R` and a local homomorphism `φ : R → V` into a complete local ring,
there is `ψ : Ŝ{z} → V` with `ψ ∘ β = φ`, `β : R → Ŝ{z}` the base change of the frame along
`S → Ŝ`.  (`β` induces `R/Mⁿ ≅ Ŝ{z}/M̂ⁿ` for all `n`: `M^nŜ{z} ∩ R = Mⁿ` by faithful flatness, and
`Ŝ{z} = β(R) + M̂ⁿ` as the residue fields agree; then `ψ` is the limit of the induced maps
`Ŝ{z}/M̂ⁿ → V/M_Vⁿ`.) -/
theorem exists_ringHom_comp_baseChangeHom_eq {R : Type u} [CommRing R] [IsRegularLocalRing R]
    (G : RegularFrame R) {V : Type*} [CommRing V] [IsLocalRing V]
    [IsAdicComplete (maximalIdeal V) V] (φ : R →+* V)
    (hφ : maximalIdeal R ≤ (maximalIdeal V).comap φ) :
    ∃ ψ : MvPowerSeries (Fin G.r) (AdicCompletion (maximalIdeal G.S) G.S) →+* V,
      ∀ r, ψ (G.baseChangeHom (algebraMap G.S (AdicCompletion (maximalIdeal G.S) G.S)) r) = φ r := by
  classical
  set Sh := AdicCompletion (maximalIdeal G.S) G.S
  have : IsRegularLocalRing Sh := isRegularLocalRing_adicCompletion_of_isRegularLocalRing G.S
  set ι := algebraMap G.S Sh with hιdef
  have hι : RingHom.MapsRSOP ι := mapsRSOP_algebraMap_adicCompletion
  set B := MvPowerSeries (Fin G.r) Sh
  set β := G.baseChangeHom ι with hβdef
  have hβ : RingHom.MapsRSOP β := G.mapsRSOP_baseChangeHom ι hι
  set MR := maximalIdeal R
  set MB := maximalIdeal B
  have hmap : MR.map β = MB := hβ.map_maximalIdeal
  have hc : ∀ n, (MB ^ n).comap β = MR ^ n := by
    intro n
    let _ := β.toAlgebra
    have : Module.Flat R B := hβ.flat
    have : IsLocalHom (algebraMap R B) := (inferInstance : IsLocalHom β)
    have : Module.FaithfullyFlat R B := Module.FaithfullyFlat.of_flat_of_isLocalHom
    rw [← hmap, ← Ideal.map_pow]
    exact Ideal.comap_map_eq_self_of_faithfullyFlat (MR ^ n)
  -- the residue fields agree: `B = β(R) + M̂`
  have hres : ∀ b : B, ∃ a, b - β a ∈ MB := by
    intro b
    have hbij : Function.Bijective (ResidueField.map (algebraMap Sh B)) :=
      (G.baseChange Sh).residueField_map_algebraMap_bijective
    obtain ⟨t, ht⟩ := hbij.2 (residue B b)
    obtain ⟨t', ht'⟩ := (AdicCompletion.residueField_map_bijective G.S).2 t
    obtain ⟨s, rfl⟩ := IsLocalRing.residue_surjective t'
    refine ⟨algebraMap G.S R s, ?_⟩
    rw [← IsLocalRing.residue_eq_zero_iff, map_sub, sub_eq_zero, ← ht, ← ht',
      ResidueField.map_residue, ResidueField.map_residue, G.baseChangeHom_algebraMap,
      algebraMap_mvPowerSeries_eq_C]
  have hs := exists_sub_mem_pow_of_map_eq β MR MB hmap hres
  -- `R/Mⁿ ≅ B/M̂ⁿ`
  let e : ∀ n, R ⧸ MR ^ n ≃+* B ⧸ MB ^ n := fun n =>
    RingEquiv.ofBijective (Ideal.quotientMap (MB ^ n) β (hc n).ge)
      ⟨Ideal.quotientMap_injective' (hc n).le, fun q => by
        obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective q
        obtain ⟨a, ha⟩ := hs n b
        exact ⟨Ideal.Quotient.mk _ a, by
          rw [Ideal.quotientMap_mk, Ideal.Quotient.eq, ← neg_sub]
          exact neg_mem ha⟩⟩
  have hφn : ∀ n, MR ^ n ≤ (maximalIdeal V ^ n).comap φ := fun n =>
    (Ideal.pow_right_mono hφ n).trans (Ideal.le_comap_pow φ n)
  let g : ∀ n, R ⧸ MR ^ n →+* V ⧸ maximalIdeal V ^ n := fun n =>
    Ideal.quotientMap (maximalIdeal V ^ n) φ (hφn n)
  let f : ∀ n, B →+* V ⧸ maximalIdeal V ^ n := fun n =>
    (g n).comp ((e n).symm.toRingHom.comp (Ideal.Quotient.mk (MB ^ n)))
  -- the values of `f n`: `f n b = [φ a]` for `b ≡ β a`
  have hf_val : ∀ n (b : B) (a : R), b - β a ∈ MB ^ n →
      f n b = Ideal.Quotient.mk _ (φ a) := by
    intro n b a hba
    have h1 : Ideal.Quotient.mk (MB ^ n) b = e n (Ideal.Quotient.mk _ a) := by
      show _ = Ideal.Quotient.mk (MB ^ n) (β a)
      rw [Ideal.Quotient.eq]
      exact hba
    simp only [f, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, h1,
      RingEquiv.symm_apply_apply]
    rfl
  have hf : ∀ {m n : ℕ} (hle : m ≤ n),
      (Ideal.Quotient.factorPow (maximalIdeal V) hle).comp (f n) = f m := by
    intro m n hle
    ext b
    obtain ⟨a, ha⟩ := hs n b
    rw [RingHom.comp_apply, hf_val n b a ha,
      hf_val m b a (Ideal.pow_le_pow_right hle ha)]
    rfl
  refine ⟨IsAdicComplete.liftRingHom (maximalIdeal V) f hf, fun r => ?_⟩
  refine (IsHausdorff.eq_iff_smodEq (I := maximalIdeal V)).mpr fun n => ?_
  rw [sModEq_pow_iff, ← Ideal.Quotient.eq, IsAdicComplete.mk_liftRingHom]
  exact hf_val n (β r) r (by rw [sub_self]; exact zero_mem _)

end CompletionLift

/-! ### Orders along primes, through localizations -/

section OrderLocalization

/-- `ν_{PR_P}(g) ≥ ν` gives `s g ∈ P^ν` for some `s ∉ P` (`R` a domain). -/
theorem exists_notMem_mul_mem_pow_of_le_ordElem {A : Type*} [CommRing A] [IsDomain A]
    (P : Ideal A) [P.IsPrime] (g : A) (ν : ℕ)
    (h : (ν : ℕ∞) ≤ Ideal.ordElem (P.map (algebraMap A (Localization.AtPrime P)))
      (algebraMap A (Localization.AtPrime P) g)) : ∃ s ∉ P, s * g ∈ P ^ ν := by
  have h1 := Ideal.mem_pow_of_le_ordElem h
  rw [← Ideal.map_pow, IsLocalization.mem_map_algebraMap_iff P.primeCompl] at h1
  obtain ⟨⟨⟨a, ha⟩, ⟨t, ht⟩⟩, hat⟩ := h1
  refine ⟨t, ht, ?_⟩
  have hinj := IsLocalization.injective (Localization.AtPrime P)
    (Ideal.primeCompl_le_nonZeroDivisors P)
  rw [← map_mul] at hat
  rw [mul_comm, hinj hat]
  exact ha

/-- Conversely, `s g ∈ P^ν` with `s ∉ P` gives `ν_{PR_P}(g) ≥ ν`. -/
theorem le_ordElem_of_notMem_mul_mem_pow {A : Type*} [CommRing A] (P : Ideal A) [P.IsPrime]
    {s g : A} (hs : s ∉ P) (ν : ℕ) (h : s * g ∈ P ^ ν) :
    (ν : ℕ∞) ≤ Ideal.ordElem (P.map (algebraMap A (Localization.AtPrime P)))
      (algebraMap A (Localization.AtPrime P) g) := by
  apply Ideal.le_ordElem
  have h1 := Ideal.mem_map_of_mem (algebraMap A (Localization.AtPrime P)) h
  rw [Ideal.map_pow, map_mul] at h1
  have hu : IsUnit (algebraMap A (Localization.AtPrime P) s) :=
    IsLocalization.map_units (Localization.AtPrime P) (⟨s, hs⟩ : P.primeCompl)
  exact (Ideal.unit_mul_mem_iff_mem _ hu).mp h1

/-- The order along `P` passes to `R'` and `P'` when `R_P → R'_{P'}` is bijective
("`(R₁)_{P₁} = R_P`, hence `ν_{P₁(R₁)_{P₁}}(y^{-ν}f) ≥ ν`", p. 267): if `φ(f) = dᵛg` with `d ∉ P'`,
then `ν_{P'R'_{P'}}(g) ≥ ν_{PR_P}(f)`. -/
theorem le_ordElem_of_localRingHom_bijective {A B : Type*} [CommRing A] [CommRing B]
    (P : Ideal A) [P.IsPrime] (Q : Ideal B) [Q.IsPrime] (φ : A →+* B) (hPQ : P = Q.comap φ)
    (hbij : Function.Bijective (Localization.localRingHom P Q φ hPQ)) (f : A) (ν : ℕ)
    (hf : (ν : ℕ∞) ≤ Ideal.ordElem (P.map (algebraMap A (Localization.AtPrime P)))
      (algebraMap A (Localization.AtPrime P) f))
    (g d : B) (hd : d ∉ Q) (hfg : φ f = d ^ ν * g) :
    (ν : ℕ∞) ≤ Ideal.ordElem (Q.map (algebraMap B (Localization.AtPrime Q)))
      (algebraMap B (Localization.AtPrime Q) g) := by
  set α := Localization.localRingHom P Q φ hPQ
  have hmax : (P.map (algebraMap A (Localization.AtPrime P))).map α =
      Q.map (algebraMap B (Localization.AtPrime Q)) := by
    rw [Localization.AtPrime.map_eq_maximalIdeal, Localization.AtPrime.map_eq_maximalIdeal]
    exact map_maximalIdeal_of_surjective α hbij.2
  have h1 := Ideal.ordElem_map_of_bijective α hbij (P.map (algebraMap A (Localization.AtPrime P)))
    (algebraMap A (Localization.AtPrime P) f)
  rw [hmax, Localization.localRingHom_to_map, hfg] at h1
  rw [← h1] at hf
  apply Ideal.le_ordElem
  have h2 := Ideal.mem_pow_of_le_ordElem hf
  rw [map_mul, map_pow] at h2
  have hu : IsUnit (algebraMap B (Localization.AtPrime Q) d) :=
    IsLocalization.map_units (Localization.AtPrime Q) (⟨d, hd⟩ : Q.primeCompl)
  exact (Ideal.unit_mul_mem_iff_mem _ (hu.pow ν)).mp h2

end OrderLocalization

/-! ### The valuation ring `V` and the maps into it -/

section ValuationTarget

variable {K : Type*} [Field K] {S₀ : Type*} [CommRing S₀] [Algebra S₀ K] (V : Subalgebra S₀ K)

/-- If `V` is finite over `S₀` and `S₀ ⊆ φ(A) ⊆ V`, then `V` is integral over `A` (through `φ`). -/
theorem isIntegral_codRestrict [Module.Finite S₀ V] {A : Type*} [CommRing A] (φ : A →+* K)
    (hφV : ∀ a, φ a ∈ V) (hφS : ∀ s, algebraMap S₀ K s ∈ φ.range) :
    (φ.codRestrict V hφV).IsIntegral := by
  intro v
  obtain ⟨q, hqm, hq⟩ := Algebra.IsIntegral.isIntegral (R := S₀) v
  have hlift : q.map (algebraMap S₀ V) ∈ Polynomial.lifts (φ.codRestrict V hφV) := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    intro n
    rw [Polynomial.coeff_map]
    obtain ⟨r, hr⟩ := hφS (q.coeff n)
    exact ⟨r, Subtype.ext hr⟩
  obtain ⟨p, hp, -, hpm⟩ := Polynomial.lifts_and_natDegree_eq_and_monic hlift (hqm.map _)
  refine ⟨p, hpm, ?_⟩
  rw [Polynomial.eval₂_eq_eval_map, hp, Polynomial.eval_map]
  exact hq

/-- The center of `V` on a local ring `A` with `S₀ ⊆ φ(A) ⊆ V` is the maximal ideal of `A`. -/
theorem comap_maximalIdeal_codRestrict [ValuationRing V] [Module.Finite S₀ V] {A : Type*}
    [CommRing A] [IsLocalRing A] (φ : A →+* K) (hφV : ∀ a, φ a ∈ V)
    (hφS : ∀ s, algebraMap S₀ K s ∈ φ.range) :
    (maximalIdeal V).comap (φ.codRestrict V hφV) = maximalIdeal A :=
  IsLocalRing.eq_maximalIdeal (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal _
    (isIntegral_codRestrict V φ hφV hφS) _)

end ValuationTarget


/-! ### The frame modulo `NR` -/

section FrameModN

variable {R : Type u} [CommRing R] [IsRegularLocalRing R]

/-- For a regular frame `(S; x)` (`r = 1`), `NR` is a prime with `R/NR` regular, `x ∉ NR`, and the
maximal ideal of `R/NR` is generated by the class of `x` (`M = (x) + NR`). -/
theorem RegularFrame.isPrime_map_and_notMem_and_map_eq_span (F : RegularFrame R) (hr : F.r = 1)
    {x : R} (hx : ∀ j, F.z j = x) :
    ((maximalIdeal F.S).map (algebraMap F.S R)).IsPrime ∧
      IsRegularLocalRing (R ⧸ (maximalIdeal F.S).map (algebraMap F.S R)) ∧
      x ∉ (maximalIdeal F.S).map (algebraMap F.S R) ∧
      (maximalIdeal R).map (Ideal.Quotient.mk ((maximalIdeal F.S).map (algebraMap F.S R))) =
        Ideal.span {Ideal.Quotient.mk ((maximalIdeal F.S).map (algebraMap F.S R)) x} := by
  classical
  set J := (maximalIdeal F.S).map (algebraMap F.S R) with hJ
  obtain ⟨V, hVspan, hxV, hV⟩ := RegularFrame.exists_extendsToRSOP_insert F x hr hx
  have hJV : J = Ideal.span (V : Set R) := hVspan.symm
  have hV' := hV.mono (Finset.subset_insert _ _)
  refine ⟨hJV ▸ hV'.isPrime_span, hJV ▸ hV'.isRegularLocalRing_quotient, ?_, ?_⟩
  · obtain ⟨Z, hZsub, hZ⟩ := hV
    rw [hJV]
    exact rsop_notMem_span hZ ((Finset.subset_insert _ _).trans hZsub)
      (hZsub (Finset.mem_insert_self _ _)) hxV
  · have hxM := (F.mem_maximalIdeal_and_ne_zero hr hx).1
    rw [RegularFrame.maximalIdeal_eq_span_sup_map F x hr hx hxM, Ideal.map_sup, Ideal.map_span,
      Set.image_singleton, ← hJ, Ideal.map_quotient_self, sup_bot_eq]

/-- p. 267: "In fact, if otherwise, `P` should contain the maximal ideal `N` of `S`. But `NR` is a
prime ideal, and `R/NR` is a regular local ring of dimension 1, so that `P = NR` which is a
contradiction": a prime `P ⊇ NR` has `R/P` regular (`P = NR` or `P = M`, `R/NR` being a discrete
valuation ring). -/
theorem RegularFrame.isRegularLocalRing_quotient_of_map_le (F : RegularFrame R) (hr : F.r = 1)
    {x : R} (hx : ∀ j, F.z j = x) (P : Ideal R) [P.IsPrime]
    (hNP : (maximalIdeal F.S).map (algebraMap F.S R) ≤ P) : IsRegularLocalRing (R ⧸ P) := by
  classical
  set J := (maximalIdeal F.S).map (algebraMap F.S R) with hJ
  obtain ⟨hJp, hJreg, hxJ, hJmax⟩ := F.isPrime_map_and_notMem_and_map_eq_span hr hx
  set π := Ideal.Quotient.mk J
  by_cases hPJ : P = J
  · rw [hPJ]; exact hJreg
  -- `P ≠ NR`: then `P = M`
  have : IsDomain (R ⧸ J) := Ideal.Quotient.isDomain J
  have : IsLocalRing (R ⧸ J) := IsLocalRing.of_surjective' π Ideal.Quotient.mk_surjective
  have hmaxD : maximalIdeal (R ⧸ J) = Ideal.span {π x} := by
    rw [← IsLocalRing.map_maximalIdeal_of_surjective π Ideal.Quotient.mk_surjective, hJmax]
  have hx0 : π x ≠ 0 := fun h => hxJ (Ideal.Quotient.eq_zero_iff_mem.mp h)
  have hnf : ¬ IsField (R ⧸ J) := by
    rw [IsLocalRing.isField_iff_maximalIdeal_eq, hmaxD]
    intro h
    exact hx0 (Ideal.span_singleton_eq_bot.mp h)
  have : IsDiscreteValuationRing (R ⧸ J) :=
    ((IsDiscreteValuationRing.TFAE (R ⧸ J) hnf).out 5 1).mp
      (⟨⟨_, hmaxD⟩⟩ : (maximalIdeal (R ⧸ J)).IsPrincipal)
  have hirr : Irreducible (π x) :=
    IsDiscreteValuationRing.irreducible_of_span_eq_maximalIdeal _ hx0 hmaxD
  -- some `p ∈ P \ NR`; its class is `u x̄ⁿ` with `n ≥ 1`, so `x ∈ P`
  obtain ⟨p, hpP, hpJ⟩ : ∃ p ∈ P, p ∉ J := by
    by_contra h
    push Not at h
    exact hPJ (le_antisymm h hNP)
  have hp0 : π p ≠ 0 := fun h => hpJ (Ideal.Quotient.eq_zero_iff_mem.mp h)
  obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hp0 hirr
  have hxP : x ∈ P := by
    have hP' : (P.map π).IsPrime :=
      Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by
        rw [Ideal.mk_ker]; exact hNP)
    have hmem : π p ∈ P.map π := Ideal.mem_map_of_mem π hpP
    rw [hu] at hmem
    have hn : n ≠ 0 := by
      rintro rfl
      rw [pow_zero, mul_one] at hmem
      exact hP'.ne_top (Ideal.eq_top_of_isUnit_mem _ hmem u.isUnit)
    have h1 : π x ^ n ∈ P.map π := (Ideal.unit_mul_mem_iff_mem _ u.isUnit).mp hmem
    have h2 := hP'.mem_of_pow_mem n h1
    have h3 := Ideal.mem_comap.mpr h2
    rw [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective] at h3
    rcases Submodule.mem_sup.mp h3 with ⟨a, ha, b, hb, hab⟩
    have hb' : b ∈ J := by
      have : b ∈ Ideal.comap π ⊥ := hb
      rwa [← RingHom.ker_eq_comap_bot, Ideal.mk_ker] at this
    rw [← hab]
    exact add_mem ha (hNP hb')
  have hPM : P = maximalIdeal R := by
    refine le_antisymm (le_maximalIdeal (Ideal.IsPrime.ne_top ‹_›)) ?_
    rw [RegularFrame.maximalIdeal_eq_span_sup_map F x hr hx
      (F.mem_maximalIdeal_and_ne_zero hr hx).1]
    exact sup_le ((Ideal.span_singleton_le_iff_mem _).mpr hxP) hNP
  rw [hPM]
  let _ : Field (R ⧸ maximalIdeal R) := Ideal.Quotient.field _
  infer_instance

end FrameModN

/-! ### The choice of `y` and the monoidal transform `R₁` (p. 267) -/

section CurveStepSupport

attribute [local instance] RingHom.ker_isPrime

variable {K : Type*} [Field K] {S₀ : Type*} [CommRing S₀] [Algebra S₀ K] (V : Subalgebra S₀ K)

open Classical in
/-- **The choice of `y`** (p. 266–267: "Then we have `y ∈ S` such that `y ∉ P`, and that `(y)` can be
extended to a regular system of parameters of `S`. […] So we take such an element `y` of `S`.",
corrected): among the members `y` of a regular system of parameters of `S` with `φ(y) ≠ 0`, choose one
of least value in the valuation ring `V` of the normalization of `R/P`.  Then `φ(M) ⊆ φ(y)V`:
every member of the system is divisible by `y`, and so is `x`, since `f ∈ P` with `c_i ∈ N^{i+1}`
(if `φ(y) = φ(x)w` with `w` a non-unit, then `φ(x)^ν = φ(x)^ν w (⋯)` in `V`).

Correction of the paper: the text allows any `y ∉ P` that extends to a regular system of parameters;
for such `y` the monoidal transform `R₁` with `(y)R₁ = MR₁`, `R₁ ⊆ R_P` need not exist.  Counterexample:
`k = ℂ`, `S = k[[s, u]]`, `R = S{x}`, `f = x²` (`ν = 2`), `P = (x, u² − s³)` (`R/P` the cusp), `y = u`:
a prime `M₁ ∋ u` of `R[M/u]` containing `PR_P ∩ R[M/u]` would contain `1 − (s/u)³u`, since
`u² − s³ = u²(1 − (s/u)³u)` and `u` is a unit of `R_P`; so `1 ∈ M₁`. -/
theorem exists_extendsToRSOP_le_comap_span [ValuationRing V] {R : Type*} [CommRing R]
    [IsRegularLocalRing R] (F : RegularFrame R) (hr : F.r = 1) {x : R} (hx : ∀ j, F.z j = x)
    (φ : R →+* K) (hφV : ∀ r, φ r ∈ V) (hxφ : φ x ≠ 0)
    (hnreg : ¬ IsRegularLocalRing (R ⧸ RingHom.ker φ)) (ν : ℕ) (c : Fin ν → F.S)
    (hcN : ∀ i : Fin ν, c i ∈ maximalIdeal F.S ^ ((i : ℕ) + 1))
    (hf : φ (x ^ ν + ∑ i : Fin ν, algebraMap F.S R (c i) * x ^ (ν - ((i : ℕ) + 1))) = 0) :
    ∃ y : F.S, ExtendsToRSOP F.S {y} ∧ φ (algebraMap F.S R y) ≠ 0 ∧
      maximalIdeal R ≤ (Ideal.span {φ.codRestrict V hφV (algebraMap F.S R y)}).comap
        (φ.codRestrict V hφV) := by
  set a := algebraMap F.S R with ha
  set φV := φ.codRestrict V hφV with hφVdef
  have hφVv : ∀ r, (φV r : K) = φ r := fun r => rfl
  obtain ⟨-, t, ht⟩ := (isRegularLocalRing_iff_exists_rsop (R := F.S)).mp inferInstance
  -- some member of `t` is not in `P`
  obtain ⟨y₀, hy₀t, hy₀⟩ : ∃ y ∈ t, φ (a y) ≠ 0 := by
    by_contra h
    push Not at h
    apply hnreg
    refine F.isRegularLocalRing_quotient_of_map_le hr hx _ ?_
    rw [← ht.1, Ideal.map_span, Ideal.span_le]
    rintro _ ⟨y, hy, rfl⟩
    exact RingHom.mem_ker.mpr (h y hy)
  -- a member of least value
  have key : ∀ T' : Finset F.S, T' ⊆ t → ∃ y ∈ t, φ (a y) ≠ 0 ∧ ∀ f ∈ T', φV (a y) ∣ φV (a f) := by
    intro T'
    induction T' using Finset.induction_on with
    | empty => exact fun _ => ⟨y₀, hy₀t, hy₀, by simp⟩
    | insert f T' hf ih =>
      intro hT'
      obtain ⟨y, hyt, hy0, hyd⟩ := ih ((Finset.subset_insert _ _).trans hT')
      rcases ValuationRing.dvd_total (φV (a y)) (φV (a f)) with hyf | hfy
      · refine ⟨y, hyt, hy0, fun g hg => ?_⟩
        rcases Finset.mem_insert.mp hg with rfl | hg
        · exact hyf
        · exact hyd g hg
      · refine ⟨f, hT' (Finset.mem_insert_self f T'), fun hf0 => hy0 ?_, fun g hg => ?_⟩
        · have : φV (a f) = 0 := Subtype.ext hf0
          rw [this, zero_dvd_iff] at hfy
          exact congrArg Subtype.val hfy
        · rcases Finset.mem_insert.mp hg with rfl | hg
          · exact dvd_rfl
          · exact hfy.trans (hyd g hg)
  obtain ⟨y, hyt, hy0, hyd⟩ := key t le_rfl
  set ϖ := φV (a y) with hϖ
  have hϖ0 : ϖ ≠ 0 := fun h => hy0 (congrArg Subtype.val h)
  -- `φ(N) ⊆ ϖV`, hence `φ(N^k) ⊆ ϖ^kV`
  have hN : maximalIdeal F.S ≤ (Ideal.span {ϖ}).comap (φV.comp a) := by
    rw [← ht.1, Ideal.span_le]
    intro f hf
    exact Ideal.mem_span_singleton.mpr (hyd f hf)
  have hNk : ∀ k, ∀ s ∈ maximalIdeal F.S ^ k, φV (a s) ∈ Ideal.span {ϖ ^ k} := by
    intro k s hs
    have := Ideal.mem_map_of_mem (φV.comp a) hs
    rw [Ideal.map_pow] at this
    have h2 := Ideal.pow_right_mono (Ideal.map_le_iff_le_comap.mpr hN) k this
    rwa [Ideal.span_singleton_pow] at h2
  -- `φ(x) ∈ ϖV`
  have hxdiv : φV x ∈ Ideal.span {ϖ} := by
    rw [Ideal.mem_span_singleton]
    by_contra hnd
    obtain ⟨w, hw⟩ := (ValuationRing.dvd_total ϖ (φV x)).resolve_left hnd
    have hξ0 : φV x ≠ 0 := fun h => hxφ (congrArg Subtype.val h)
    have hwu : ¬ IsUnit w := fun hu =>
      hnd ⟨↑hu.unit⁻¹, by rw [hw, mul_assoc, IsUnit.mul_val_inv, mul_one]⟩
    choose v hv using fun i : Fin ν => Ideal.mem_span_singleton'.mp (hNk _ _ (hcN i))
    have hterm : ∀ i : Fin ν, φV (a (c i) * x ^ (ν - ((i : ℕ) + 1))) =
        φV x ^ ν * (w * (v i * w ^ (i : ℕ))) := by
      intro i
      rw [map_mul, map_pow, ← hv i, hw, mul_pow]
      have h1 := pow_mul_pow_sub (φV x) (show (i : ℕ) + 1 ≤ ν from i.2)
      calc v i * (φV x ^ ((i : ℕ) + 1) * w ^ ((i : ℕ) + 1)) * φV x ^ (ν - ((i : ℕ) + 1)) =
            v i * w ^ ((i : ℕ) + 1) * (φV x ^ ((i : ℕ) + 1) * φV x ^ (ν - ((i : ℕ) + 1))) := by
              ring
        _ = φV x ^ ν * (w * (v i * w ^ (i : ℕ))) := by rw [h1]; ring
    have hfV : φV (x ^ ν + ∑ i : Fin ν, a (c i) * x ^ (ν - ((i : ℕ) + 1))) = 0 :=
      Subtype.ext (by rw [hφVv]; exact hf)
    rw [map_add, map_pow, map_sum, Finset.sum_congr rfl fun i _ => hterm i, ← Finset.mul_sum,
      ← Finset.mul_sum] at hfV
    have h2 : φV x ^ ν * (1 + w * ∑ i : Fin ν, v i * w ^ (i : ℕ)) = 0 := by
      rw [← hfV]; ring
    have h3 := (mul_eq_zero.mp h2).resolve_left (pow_ne_zero _ hξ0)
    exact hwu (IsUnit.of_mul_eq_one (-(∑ i : Fin ν, v i * w ^ (i : ℕ))) (by
      linear_combination -h3))
  refine ⟨y, (ExtendsToRSOP.of_isRegularSystemOfParameters ht).mono
    (Finset.singleton_subset_iff.mpr hyt), hy0, ?_⟩
  rw [RegularFrame.maximalIdeal_eq_span_sup_map F x hr hx (F.mem_maximalIdeal_and_ne_zero hr hx).1]
  refine sup_le ((Ideal.span_singleton_le_iff_mem _).mpr hxdiv) ?_
  rw [Ideal.map_le_iff_le_comap, Ideal.comap_comap]
  exact hN


/-- **The monoidal transform `R₁`** (p. 267: "Let `R₁` be a monoidal transform of `R` with center `M`
such that: `(y)R₁ = MR₁`, `R_P ⊇ R₁`, and `R₁` is residually algebraic (hence, rational) over `R`"),
for an element `m ∈ M` with `φ(M) ⊆ φ(m)V`: `φ` extends to `R[M/m] → V`, the center of `V` on
`R[M/m]` gives the transform `R₁` with `t.x = m`, residually algebraic, regular, with
`R_P = (R₁)_{P₁}`, and `φ₁(R₁) ∩ V ⊋ φ(R) ∩ V` when `R/P` is not regular.  (The construction of
`exists_monoidalTransform_of_not_isRegularLocalRing_quotient`, `Compat/CurveResolution.lean`, for a
given element `m`.) -/
theorem exists_monoidalTransform_of_le_comap_span [ValuationRing V] [Module.Finite S₀ V]
    {R : Type u} [CommRing R] [IsRegularLocalRing R] [IsDomain R] {P : Ideal R} [P.IsPrime]
    (φ : R →+* K) (hφV : ∀ r, φ r ∈ V) (hφS : ∀ s, algebraMap S₀ K s ∈ φ.range)
    (hker : RingHom.ker φ = P) (hS : ¬ IsRegularLocalRing (R ⧸ P)) (m : R)
    (hmM : m ∈ maximalIdeal R) (hm0 : φ m ≠ 0)
    (hdiv : maximalIdeal R ≤ (Ideal.span {φ.codRestrict V hφV m}).comap (φ.codRestrict V hφV)) :
    ∃ (t : MonoidalTransform R (maximalIdeal R)) (φ' : t.ring →+* K)
      (hP' : P = (RingHom.ker φ').comap t.toRing), t.x = m ∧
      Function.Bijective (Localization.localRingHom P (RingHom.ker φ') t.toRing hP') ∧
      RingHom.IsResiduallyAlgebraic (R := R) (R' := t.ring) t.toRing ∧
      IsRegularLocalRing t.ring ∧ (∀ r, φ' r ∈ V) ∧
      ∃ hφ'S : ∀ s, algebraMap S₀ K s ∈ φ'.range,
        curveImage V φ hφS < curveImage V φ' hφ'S := by
  classical
  set M := maximalIdeal R with hMdef
  let φV : R →+* V := φ.codRestrict V hφV
  have hint : φV.IsIntegral := isIntegral_codRestrict V φ hφV hφS
  have hMcomap : Ideal.comap φV (maximalIdeal V) = M :=
    comap_maximalIdeal_codRestrict V φ hφV hφS
  have hm0' : m ≠ 0 := fun h => hm0 (by rw [h, map_zero])
  -- the blow-up algebra `A = R[M/m]` lies in `R[1/m]`, on which `φ` extends to `ψ : A → V`
  set A := blowupAlgebra R M m with hAdef
  have hmS : Submonoid.powers m ≤ nonZeroDivisors R :=
    powers_le_nonZeroDivisors_of_noZeroDivisors hm0'
  let D := Localization.subalgebra.ofField (FractionRing R) (Submonoid.powers m) hmS
  have hunit : ∀ y : Submonoid.powers m, IsUnit (φ y) := by
    rintro ⟨_, n, rfl⟩
    exact isUnit_iff_ne_zero.mpr (by rw [map_pow]; exact pow_ne_zero n hm0)
  let ψD : D →+* K := IsLocalization.lift (M := Submonoid.powers m) (S := D) hunit
  have hψD : ∀ r, ψD (algebraMap R D r) = φ r := IsLocalization.lift_eq hunit
  have hAD : A ≤ D := by
    refine Algebra.adjoin_le ?_
    rintro _ ⟨n, -, rfl⟩
    exact ⟨n, m, Submonoid.mem_powers m, div_eq_mul_inv _ _⟩
  let ψA : A →+* K := ψD.comp (Subalgebra.inclusion hAD).toRingHom
  have hψA : ∀ (b : A) (k : ℕ) (g : R), (b : FractionRing R) * algebraMap R _ m ^ k =
      algebraMap R _ g → ψA b * φ m ^ k = φ g := by
    intro b k g h
    have h' : Subalgebra.inclusion hAD b * algebraMap R D (m ^ k) = algebraMap R D g :=
      Subtype.ext (by simpa [map_pow] using h)
    have := congrArg ψD h'
    rwa [map_mul, hψD, hψD, map_pow] at this
  have hψA_alg : ∀ r, ψA (algebraMap R A r) = φ r := by
    intro r
    simpa using hψA (algebraMap R A r) 0 r (by simp)
  have hMpow : ∀ k, M ^ k ≤ Ideal.comap φV (Ideal.span {φV m ^ k}) := by
    intro k
    rw [← Ideal.span_singleton_pow]
    exact (Ideal.pow_right_mono hdiv k).trans (Ideal.le_comap_pow _ k)
  have hψA_V : ∀ b, ψA b ∈ V := by
    intro b
    obtain ⟨k, g, hg, hbg⟩ :=
      MonoidalTransform.exists_mul_pow_eq_of_mem_blowupAlgebra hmM hm0' b.2
    obtain ⟨v, hv⟩ := Ideal.mem_span_singleton'.mp (Ideal.mem_comap.mp (hMpow k hg))
    have h2 : φ g = (v : K) * φ m ^ k := by
      have := congrArg Subtype.val hv
      push_cast at this
      exact this.symm
    have : ψA b = v := mul_right_cancel₀ (pow_ne_zero k hm0) ((hψA b k g hbg).trans h2)
    rw [this]
    exact v.2
  let ψV : A →+* V := ψA.codRestrict V hψA_V
  have hψV_comp : ψV.comp (algebraMap R A) = φV := RingHom.ext fun r => Subtype.ext (hψA_alg r)
  -- the center `N` of `V` on `A`: a maximal ideal containing `M A`
  set N : Ideal A := Ideal.comap ψV (maximalIdeal V) with hNdef
  have hNmax : N.IsMaximal :=
    Ideal.isMaximal_comap_of_isIntegral_of_isMaximal ψV
      (RingHom.IsIntegral.tower_top (algebraMap R A) ψV (hψV_comp ▸ hint)) _
  have hMN : M.map (algebraMap R A) ≤ N := by
    rw [Ideal.map_le_iff_le_comap, Ideal.comap_comap, hψV_comp, hMcomap]
  obtain ⟨φ', hP', h1, h2, h3, h4, h5⟩ := exists_curveImage_lt_of_lift V φ hφS hker hS
    ⟨m, hmM, hm0', N, hNmax.isPrime, hMN⟩ ψV hψA_alg hψA rfl hNmax hm0
  exact ⟨⟨m, hmM, hm0', N, hNmax.isPrime, hMN⟩, φ', hP', rfl, h1, h2, h3, h4, h5⟩

end CurveStepSupport


/-! ### Dimension at least two (the induction on `dim R/P`, p. 266) -/

section DimensionTwo

/-- In a noetherian local domain of dimension `≥ 2` (i.e. not `≤ 1`), a non-zero element lies outside some non-zero
prime ideal.  (Otherwise every height-one prime would be minimal over `(a)`, hence one of finitely
many; by prime avoidance some `b ∈ M` avoids them all, and a minimal prime of `(b)`, of height one by
Krull's principal ideal theorem, would contain `a`, hence be minimal over `(a)`.) This is the step
"by induction on `dim R/P`, we can reduce the proof to the case in which `dim R/P = 1`" of the proof
of Lemma 22 (p. 266): the primes `P' ⊋ P` satisfy the hypotheses for `P'` by Theorem 1 of §3, and
their intersection is `P` when `dim R/P ≥ 2`. -/
theorem exists_isPrime_ne_bot_notMem {A : Type*} [CommRing A] [IsNoetherianRing A]
    [IsLocalRing A] [IsDomain A] (hdim : ¬ ringKrullDim A ≤ 1) {a : A} (ha : a ≠ 0) :
    ∃ q : Ideal A, q.IsPrime ∧ q ≠ ⊥ ∧ a ∉ q := by
  classical
  by_contra hcon
  push Not at hcon
  have hm2 : (2 : ℕ∞) ≤ (maximalIdeal A).height := by
    have h := IsLocalRing.maximalIdeal_height_eq_ringKrullDim (R := A)
    rw [← h] at hdim
    have h1 : ¬ (maximalIdeal A).height ≤ 1 := fun h2 => hdim (WithBot.coe_le_coe.mpr h2)
    have h3 : (1 : ℕ∞) + 1 ≤ (maximalIdeal A).height := Order.add_one_le_of_lt (lt_of_not_ge h1)
    rwa [one_add_one_eq_two] at h3
  have hmbot : maximalIdeal A ≠ ⊥ := by
    intro h
    rw [h, Ideal.height_bot] at hm2
    exact absurd hm2 (by norm_num)
  have haM : a ∈ maximalIdeal A := hcon _ (maximalIdeal.isMaximal A).isPrime hmbot
  have hspan : Ideal.span {a} ≠ ⊤ := by
    rw [Ne, Ideal.span_singleton_eq_top]
    exact (IsLocalRing.mem_maximalIdeal _).mp haM
  set S := (Ideal.span {a}).minimalPrimes with hS
  have hSfin : S.Finite := Ideal.finite_minimalPrimes_of_isNoetherianRing _ _
  have hSprime : ∀ q ∈ S, q.IsPrime := fun q hq => hq.1.1
  have hSht : ∀ q ∈ S, q.height ≤ 1 := fun q hq =>
    Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes _ q hq
  -- the maximal ideal is not contained in a member of `S`
  have hmS : ∀ q ∈ S, ¬ maximalIdeal A ≤ q := by
    intro q hq hle
    have := hSprime q hq
    have heq : q = maximalIdeal A := le_antisymm (le_maximalIdeal this.ne_top) hle
    have := hSht q hq
    rw [heq] at this
    exact absurd (hm2.trans this) (by norm_num)
  -- prime avoidance
  obtain ⟨b, hbM, hbS⟩ : ∃ b ∈ maximalIdeal A, ∀ q ∈ S, b ∉ q := by
    by_contra h
    push Not at h
    have hsub : ((maximalIdeal A : Ideal A) : Set A) ⊆ ⋃ q ∈ (↑hSfin.toFinset : Set (Ideal A)), q := by
      intro b hb
      obtain ⟨q, hq, hbq⟩ := h b hb
      exact Set.mem_biUnion (by simpa using hq) hbq
    obtain ⟨q, hq, hle⟩ := (Ideal.subset_union_prime (f := id) ⊥ ⊥
      (fun q hq _ _ => hSprime q (by simpa using hq))).mp hsub
    exact hmS q (by simpa using hq) hle
  have hb0 : b ≠ 0 := by
    intro hb
    obtain ⟨q, hq⟩ := Ideal.nonempty_minimalPrimes hspan
    exact hbS q hq (by rw [hb]; exact zero_mem _)
  have hbspan : Ideal.span {b} ≠ ⊤ := by
    rw [Ne, Ideal.span_singleton_eq_top]
    exact (IsLocalRing.mem_maximalIdeal _).mp hbM
  obtain ⟨p, hp⟩ := Ideal.nonempty_minimalPrimes hbspan
  have hpprime : p.IsPrime := hp.1.1
  have hbp : b ∈ p := hp.1.2 (Ideal.mem_span_singleton_self b)
  have hp0 : p ≠ ⊥ := fun h => hb0 (by rw [h] at hbp; exact hbp)
  have hap : Ideal.span {a} ≤ p := (Ideal.span_singleton_le_iff_mem _).mpr (hcon p hpprime hp0)
  obtain ⟨q, hq, hqp⟩ := Ideal.exists_minimalPrimes_le hap
  have hqprime := hSprime q hq
  rcases eq_or_lt_of_le hqp with heq | hlt
  · exact hbS q hq (heq ▸ hbp)
  · -- `q ⊊ p` with `ht p ≤ 1` forces `ht q = 0`, i.e. `q = 0`, but `a ∈ q`
    have h1 := Ideal.height_strict_mono_of_isPrime hlt
    have h2 := Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes _ p hp
    have h3 : q.height = 0 := by
      have := lt_of_lt_of_le h1 h2
      exact Order.lt_one_iff.mp this
    rw [Ideal.height_eq_zero_iff] at h3
    have hq0 : q = ⊥ := le_antisymm (h3.2 ⟨Ideal.isPrime_bot, bot_le⟩ bot_le) bot_le
    have haq : a ∈ q := hq.1.2 (Ideal.mem_span_singleton_self a)
    rw [hq0] at haq
    exact ha haq

end DimensionTwo

end

end Hironaka
