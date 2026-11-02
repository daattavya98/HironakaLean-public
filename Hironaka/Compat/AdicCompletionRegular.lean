/-
Copyright (c) 2026 Daattavya Aggarwal, Minhyong Kim, Oisin Kim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daattavya Aggarwal, Minhyong Kim, Oisin Kim
-/
module

public import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
public import Mathlib.RingTheory.AdicCompletion.LocalRing
public import Mathlib.RingTheory.KrullDimension.Regular
public import Mathlib.RingTheory.Regular.Flat
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Architect
public import Hironaka.Compat.RegularGraded

/-!
# Compatibility layer: the completion of a regular local ring

Facts about the completion `R̂ = AdicCompletion (maximalIdeal R) R` of a noetherian local ring
that Hironaka uses without comment (Ch. III §3, proof of Theorem 1, p. 218: "let `R̂` be the
completion of `R` … we may assume that `R` is complete"):

* `R̂` is noetherian (it is a quotient of a power series ring `R⟦X₁, …, Xₙ⟧`);
* `R̂` is faithfully flat over `R`, so that `IR̂ ∩ R = I` for every ideal `I` of `R` and every
  prime of `R` is the contraction of a prime of `R̂`;
* if `R` is regular, so is `R̂`.

Mathlib provides the local ring structure of `R̂`, `M̂ = MR̂`, the completeness of `R̂` along
`M̂`, and the flatness of `R̂` over a noetherian `R`.  The proofs of the noetherianity and the
regularity of `R̂` are those of `Hironaka/Ch2/AscendingChain.lean` (where they are private),
repeated here with public names.
-/

@[expose] public section

open IsLocalRing

namespace Hironaka

universe u

/-- A polynomial all of whose monomials have total degree `≥ k`, evaluated at elements of an
ideal `m`, lies in `mᵏ`. -/
private theorem eval_mem_pow_of_forall_le_degree {S : Type u} [CommRing S] {n : ℕ} (m : Ideal S)
    (x : Fin n → S) (hx : ∀ i, x i ∈ m)
    (k : ℕ) (H : MvPolynomial (Fin n) S)
    (hH : ∀ α ∈ H.support, k ≤ α.degree) : MvPolynomial.eval x H ∈ m ^ k := by
  classical
  rw [MvPolynomial.eval_eq]
  refine Ideal.sum_mem _ fun α hα => ?_
  refine Ideal.mul_mem_left _ _ ?_
  refine Ideal.pow_le_pow_right (hH α hα) ?_
  have : ∏ i ∈ α.support, x i ^ α i ∈ ∏ i ∈ α.support, m ^ α i :=
    Ideal.prod_mem_prod fun i _ => Ideal.pow_mem_pow (hx i) _
  rwa [Finset.prod_pow_eq_pow_sum] at this

/-- Every element of `mᵏ` is the value at the generators `x` of a homogeneous polynomial of
degree `k`. -/
private theorem exists_isHomogeneous_eval_eq_of_span_eq {S : Type u} [CommRing S] {n : ℕ} (m : Ideal S)
    (x : Fin n → S)
    (hx : Ideal.span (Set.range x) = m) (k : ℕ) (d : S) (hd : d ∈ m ^ k) :
    ∃ P : MvPolynomial (Fin n) S, P.IsHomogeneous k ∧ MvPolynomial.eval x P = d := by
  induction k generalizing d with
  | zero => exact ⟨MvPolynomial.C d, MvPolynomial.isHomogeneous_C _ _, by simp⟩
  | succ k ih =>
    rw [pow_succ] at hd
    refine Submodule.mul_induction_on hd (fun a ha b hb => ?_) (fun a b ha hb => ?_)
    · obtain ⟨Pa, hPa, rfl⟩ := ih a ha
      rw [← hx] at hb
      obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun S).mp hb
      refine ⟨Pa * ∑ i, MvPolynomial.C (c i) * MvPolynomial.X i, hPa.mul ?_, ?_⟩
      · refine MvPolynomial.IsHomogeneous.sum _ _ _ fun i _ => ?_
        simpa using (MvPolynomial.isHomogeneous_C _ (c i)).mul (MvPolynomial.isHomogeneous_X _ i)
      · simp [smul_eq_mul]
    · obtain ⟨Pa, hPa, rfl⟩ := ha
      obtain ⟨Pb, hPb, rfl⟩ := hb
      exact ⟨Pa + Pb, hPa.add hPb, by simp⟩

open MvPowerSeries in
/-- The adic completion of a noetherian ring along an ideal is noetherian: it is a quotient of a
power series ring `S⟦X₁, …, Xₙ⟧` (`Xᵢ ↦ xᵢ`, the `xᵢ` generating the ideal). -/
theorem isNoetherianRing_adicCompletion_of_isNoetherianRing {S : Type u} [CommRing S]
    [IsNoetherianRing S] (m : Ideal S) :
    IsNoetherianRing (AdicCompletion m S) := by
  classical
  obtain ⟨n, x, hx⟩ := Submodule.fg_iff_exists_fin_generating_family.mp
    (IsNoetherian.noetherian m)
  have hxm : ∀ i, x i ∈ m := fun i => hx ▸ Ideal.subset_span ⟨i, rfl⟩
  have htop : ∀ a b : S ⧸ m ^ 0, a = b := fun a b => by
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
    rw [Ideal.Quotient.eq, pow_zero, Ideal.one_eq_top]
    trivial
  -- two truncations agreeing in degrees `< k` have the same value modulo `mᵏ`
  have hdiff : ∀ (k : ℕ) (H₁ H₂ : MvPolynomial (Fin n) S),
      (∀ α : Fin n →₀ ℕ, α.degree < k → H₁.coeff α = H₂.coeff α) →
      Ideal.Quotient.mk (m ^ k) (MvPolynomial.eval x H₁) =
        Ideal.Quotient.mk (m ^ k) (MvPolynomial.eval x H₂) := by
    intro k H₁ H₂ h
    rw [Ideal.Quotient.eq, ← map_sub]
    refine eval_mem_pow_of_forall_le_degree m x hxm k _ fun α hα => ?_
    by_contra hlt
    rw [MvPolynomial.mem_support_iff, MvPolynomial.coeff_sub, h α (not_le.mp hlt),
      sub_self] at hα
    exact hα rfl
  let f : ∀ k, MvPowerSeries (Fin n) S →+* S ⧸ m ^ k := fun k =>
    { toFun := fun F => Ideal.Quotient.mk (m ^ k) (MvPolynomial.eval x (truncTotal k F))
      map_one' := by
        rcases Nat.eq_zero_or_pos k with rfl | hk
        · exact htop _ _
        · rw [truncTotal_one hk.ne', map_one, map_one]
      map_mul' := fun F G => by
        rw [← map_mul, ← map_mul]
        exact hdiff k _ _ fun α hα => by
          rw [coeff_truncTotal _ hα, coeff_truncTotal_mul_truncTotal_eq_coeff_mul _ _ hα]
      map_zero' := by simp
      map_add' := fun F G => by simp }
  have hf : ∀ k F, f k F = Ideal.Quotient.mk (m ^ k) (MvPolynomial.eval x (truncTotal k F)) :=
    fun _ _ => rfl
  have hcompat : ∀ {k l : ℕ} (hkl : k ≤ l),
      (Ideal.Quotient.factorPow m hkl).comp (f l) = f k := by
    intro k l hkl
    ext F
    rw [RingHom.comp_apply, hf, hf, Ideal.Quotient.factorPow, Ideal.Quotient.factor_mk]
    exact hdiff k _ _ fun α hα => by
      rw [coeff_truncTotal _ hα, coeff_truncTotal _ (lt_of_lt_of_le hα hkl)]
  let Φ := AdicCompletion.liftRingHom m f hcompat
  have hΦ : Function.Surjective Φ := by
    intro a
    obtain ⟨c, rfl⟩ := AdicCompletion.mk_surjective m S a
    have hd : ∀ k, c.val (k + 1) - c.val k ∈ m ^ k := by
      intro k
      have := AdicCompletion.AdicCauchySequence.mk_eq_mk (Nat.le_succ k) c
      rw [Submodule.Quotient.eq, smul_eq_mul, Ideal.mul_top] at this
      exact this
    choose P hP hPe using fun k => exists_isHomogeneous_eval_eq_of_span_eq m x hx k _ (hd k)
    let F : MvPowerSeries (Fin n) S := fun α =>
      (P α.degree).coeff α + if α = 0 then c.val 0 else 0
    have hF : ∀ α, MvPowerSeries.coeff α F = (P α.degree).coeff α + if α = 0 then c.val 0 else 0 :=
      fun _ => rfl
    have htrunc : ∀ k, 0 < k → truncTotal k F =
        MvPolynomial.C (c.val 0) + ∑ j ∈ Finset.range k, P j := by
      intro k hk
      ext α
      rw [coeff_truncTotal_eq_ite, AddMonoidAlgebra.coeff_add, Finsupp.add_apply,
        MvPolynomial.coeff_C, MvPolynomial.coeff_sum]
      by_cases hα : α.degree < k
      · have hsum : ∑ j ∈ Finset.range k, (P j).coeff α = (P α.degree).coeff α := by
          refine Finset.sum_eq_single α.degree (fun j _ hj => ?_) (fun h => ?_)
          · exact (hP j).coeff_eq_zero (fun h => hj h.symm)
          · exact absurd (Finset.mem_range.mpr hα) h
        simp only [hα, ↓reduceIte, hsum, hF]
        by_cases h0 : α = 0
        · simp only [h0, ↓reduceIte]
          ring
        · have h0' : ¬ (0 = α) := fun h => h0 h.symm
          simp only [h0, h0', ↓reduceIte]
          ring
      · have hsum : ∑ j ∈ Finset.range k, (P j).coeff α = 0 := by
          refine Finset.sum_eq_zero fun j hj => ?_
          refine (hP j).coeff_eq_zero fun h => hα ?_
          rw [h]
          exact Finset.mem_range.mp hj
        have h0 : ¬ (0 = α) := fun h => hα (by rw [← h]; simpa using hk)
        simp only [hα, h0, ↓reduceIte, hsum, add_zero]
    refine ⟨F, AdicCompletion.ext_evalₐ fun k => ?_⟩
    rw [AdicCompletion.evalₐ_liftRingHom, AdicCompletion.evalₐ_mk, hf]
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · exact htop _ _
    · rw [htrunc k hk, map_add, map_sum, MvPolynomial.eval_C]
      simp only [hPe]
      rw [Finset.sum_range_sub (fun j => c.val j), add_sub_cancel]
  exact isNoetherianRing_of_surjective _ _ Φ hΦ

/-- The completion `R̂` of a noetherian local ring `R` is faithfully flat over `R` (flat by
Mathlib, and `R → R̂` is a local homomorphism of local rings). -/
theorem faithfullyFlat_adicCompletion_maximalIdeal (R : Type u) [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] :
    Module.FaithfullyFlat R (AdicCompletion (maximalIdeal R) R) :=
  Module.FaithfullyFlat.of_flat_of_isLocalHom

/-- `IR̂ ∩ R = I` for every ideal `I` of a noetherian local ring `R`. -/
theorem comap_map_adicCompletion_maximalIdeal {R : Type u} [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] (I : Ideal R) :
    (I.map (algebraMap R (AdicCompletion (maximalIdeal R) R))).comap
      (algebraMap R (AdicCompletion (maximalIdeal R) R)) = I := by
  have := faithfullyFlat_adicCompletion_maximalIdeal R
  exact Ideal.comap_map_eq_self_of_faithfullyFlat I

/-- Every prime `P` of a noetherian local ring `R` is the contraction of a prime of `R̂`. -/
theorem exists_isPrime_comap_adicCompletion_eq {R : Type u} [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] (P : Ideal R) [P.IsPrime] :
    ∃ P' : Ideal (AdicCompletion (maximalIdeal R) R), P'.IsPrime ∧
      P'.comap (algebraMap R (AdicCompletion (maximalIdeal R) R)) = P := by
  have := faithfullyFlat_adicCompletion_maximalIdeal R
  obtain ⟨P', hP', hlo⟩ :=
    Ideal.exists_isPrime_liesOver_of_faithfullyFlat (B := AdicCompletion (maximalIdeal R) R) P
  exact ⟨P', hP', hlo.over.symm⟩

/-- The completion of a regular local ring is a regular local ring: the images of a regular
system of parameters form a regular sequence in `R̂` (faithfully flat over `R`) generating its
maximal ideal. -/
theorem isRegularLocalRing_adicCompletion_of_isRegularLocalRing (S : Type u) [CommRing S]
    [IsRegularLocalRing S] :
    IsRegularLocalRing (AdicCompletion (IsLocalRing.maximalIdeal S) S) := by
  classical
  set m := IsLocalRing.maximalIdeal S
  have := isNoetherianRing_adicCompletion_of_isNoetherianRing m
  obtain ⟨S₀, hScard, hSspan⟩ := (IsNoetherian.noetherian m).exists_span_finset_card_eq_spanFinrank
  have hS : Ideal.span (S₀ : Set S) = m := hSspan
  let z : Fin S₀.card → S := fun i => (S₀.equivFin.symm i : S)
  have hinj : Function.Injective z := Subtype.val_injective.comp S₀.equivFin.symm.injective
  have hreg := isRegular_ofFn_of_minimal hS hScard hinj (fun i => (S₀.equivFin.symm i).2)
  have : Module.FaithfullyFlat S (AdicCompletion m S) := Module.FaithfullyFlat.of_flat_of_isLocalHom
  have hreg' := hreg.of_faithfullyFlat (S := AdicCompletion m S)
  have hdim := ringKrullDim_add_length_eq_ringKrullDim_of_isRegular _ hreg'
  have hz : Ideal.ofList (List.ofFn z) = m := by
    rw [← hS]
    show Ideal.span {r | r ∈ List.ofFn z} = Ideal.span (S₀ : Set S)
    congr 1
    ext y
    show y ∈ List.ofFn z ↔ y ∈ (S₀ : Set S)
    rw [List.mem_ofFn, Finset.mem_coe]
    constructor
    · rintro ⟨i, rfl⟩
      exact (S₀.equivFin.symm i).2
    · intro hy
      exact ⟨S₀.equivFin ⟨y, hy⟩, by simp [z]⟩
  have hof : Ideal.ofList ((List.ofFn z).map (algebraMap S (AdicCompletion m S))) =
      IsLocalRing.maximalIdeal (AdicCompletion m S) := by
    rw [← Ideal.map_ofList, hz, AdicCompletion.maximalIdeal_eq_map]
  rw [hof, List.length_map, List.length_ofFn] at hdim
  have h0 : ringKrullDim (AdicCompletion m S ⧸ IsLocalRing.maximalIdeal (AdicCompletion m S)) =
      0 := by
    let _ := Ideal.Quotient.field (IsLocalRing.maximalIdeal (AdicCompletion m S))
    exact ringKrullDim_eq_zero_of_field _
  rw [h0, zero_add] at hdim
  refine IsRegularLocalRing.of_spanFinrank_maximalIdeal_le _ ?_
  rw [AdicCompletion.spanFinrank_maximalIdeal_eq, ← hScard, hdim]

end Hironaka
