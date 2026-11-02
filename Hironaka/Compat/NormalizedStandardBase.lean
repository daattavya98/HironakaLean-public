/-
Copyright (c) 2026 Daattavya Aggarwal, Minhyong Kim, Oisin Kim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daattavya Aggarwal, Minhyong Kim, Oisin Kim
-/
module

public import Mathlib.Data.Nat.Nth
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
public import Mathlib.RingTheory.MvPowerSeries.Inverse
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Architect
public import Hironaka.Ch3.Frames
public import Hironaka.Ch3.TauStar
public import Hironaka.Ch3.Transforms
public import Hironaka.Ch3.PermissibleEffects
public import Hironaka.Compat.CoefficientField
public import Hironaka.Compat.FrameTransformCriterion

/-!
# Compatibility layer: existence of a normalized standard base (footnote 11, p. 259)

> "We can thus prove the existence of a normalized standard base of `J` with respect to any
> regular `τ`-frame of `R` for `J`, when `R` is complete."  (Footnote 11, p. 259)

The proof of footnote 11 is an induction using Lemma 17
(`exists_normalized_of_isAdicComplete`, stated for the power series ring `S{z₁, …, z_r}`) and
Lemma 19 (`initialForm_mem_adjoin_of_isNormalizedBy`).  This file contains the infrastructure:

* the power series expansion `R → S{z₁, …, z_r}` of a regular frame of a complete regular local
  ring `R` is an isomorphism (`RegularFrame.exists_isExpansion_bijective`, from
  `Hironaka/Compat/CoefficientField.lean` and `RegularFrame.isAdicComplete_idealZ`), and the
  coefficient ring `S` is complete (`RegularFrame.isAdicComplete_S`);
* its transport of Lemma 17 to `R` (`RegularFrame.exists_isNormalizedBy_sub_sum`): the isomorphism
  carries `ν_M`, the associated subalgebras `k[Z]` and the `E`-sets of a system (the latter through
  Remark 1, `eSet_subset_of_map_le`);
* the replacement step in a standard base (`ordElem_sub_sum_eq_and_initialForm_notMem`), the
  `τ`-parameters `τ_{(z)}(f) = 0` (`RegularFrame.tauZ_eq_zero_of_initialForm_mem`) and
  `a`-th `τ`-parameters taken from the frame
  (`RegularFrame.IsRegularTauFrame.exists_isRegularSystemOfTauParameters`);
* the induction (`RegularFrame.exists_snoc_isNormalizedSystem`,
  `RegularFrame.exists_isNormalizedStandardBase`).
-/

@[expose] public section

open IsLocalRing

namespace Hironaka

universe u

section FrameCompletionB1

variable {R : Type u} [CommRing R] [IsRegularLocalRing R] (F : RegularFrame R)

/-- Krull's intersection theorem in the form `⋂ₙ (I + Mⁿ) = I`, for a proper ideal `I` of a
noetherian local ring. -/
theorem Ideal.mem_of_forall_mem_sup_pow_maximalIdeal {I : Ideal R} (hI : I ≠ ⊤) {y : R}
    (hy : ∀ N : ℕ, y ∈ I ⊔ maximalIdeal R ^ N) : y ∈ I := by
  have hIM : I ≤ maximalIdeal R := IsLocalRing.le_maximalIdeal hI
  have : IsLocalRing (R ⧸ I) := isLocalRing_quotient_of_le hIM
  have hbot := Ideal.iInf_pow_eq_bot_of_isLocalRing (maximalIdeal (R ⧸ I))
    (Ideal.IsPrime.ne_top inferInstance)
  have : Ideal.Quotient.mk I y ∈ ⨅ N : ℕ, maximalIdeal (R ⧸ I) ^ N := by
    rw [Ideal.mem_iInf]
    intro N
    have h1 := hy N
    rw [← IsLocalRing.map_maximalIdeal_of_surjective (Ideal.Quotient.mk I)
      Ideal.Quotient.mk_surjective, ← Ideal.map_pow, Ideal.mem_quotient_iff_mem_sup]
    simpa [sup_comm] using h1
  rw [hbot, Ideal.mem_bot] at this
  exact Ideal.Quotient.eq_zero_iff_mem.mp this

/-- The ideal `(z₁, …, z_r)R` of a regular frame lies in the maximal ideal. -/
theorem RegularFrame.idealZ_le_maximalIdeal : F.idealZ ≤ maximalIdeal R := by
  classical
  refine Ideal.span_le.mpr ?_
  rintro _ ⟨j, rfl⟩
  exact F.extends_rsop.mem_maximalIdeal (Finset.mem_image_of_mem F.z (Finset.mem_univ j))

/-- If `R` is complete for the maximal ideal, it is complete for `P = (z₁, …, z_r)R`
(`P ⊆ M`, `R` noetherian). -/
theorem RegularFrame.isAdicComplete_idealZ [IsAdicComplete (maximalIdeal R) R] :
    IsAdicComplete F.idealZ R := by
  classical
  have hPM := F.idealZ_le_maximalIdeal
  have hPtop : F.idealZ ≠ ⊤ := ne_top_of_le_ne_top (Ideal.IsPrime.ne_top inferInstance) hPM
  have hhaus : IsHausdorff F.idealZ R := by
    refine ⟨fun x hx => ?_⟩
    have hbot := Ideal.iInf_pow_eq_bot_of_isLocalRing F.idealZ hPtop
    have : x ∈ ⨅ n : ℕ, F.idealZ ^ n := by
      rw [Ideal.mem_iInf]
      intro n
      have := hx n
      rwa [SModEq.sub_mem, sub_zero, smul_eq_mul, Ideal.mul_top] at this
    rwa [hbot, Ideal.mem_bot] at this
  have hprec : IsPrecomplete F.idealZ R := by
    refine ⟨fun u hu => ?_⟩
    have hprec := IsAdicComplete.toIsPrecomplete (I := maximalIdeal R) (M := R)
    obtain ⟨L, hL⟩ := IsPrecomplete.prec hprec (f := u) fun {m n} hmn => by
      have := hu hmn
      rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top] at this ⊢
      exact Ideal.pow_right_mono hPM m this
    refine ⟨L, fun n => ?_⟩
    rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top]
    by_cases hn : n = 0
    · subst hn; simp
    have hPn : F.idealZ ^ n ≠ ⊤ := fun h => hPtop (by
      rw [Ideal.eq_top_iff_one] at h ⊢
      exact (Ideal.pow_le_self hn) h)
    refine Ideal.mem_of_forall_mem_sup_pow_maximalIdeal hPn fun N => ?_
    have h1 : L - u (max n N) ∈ maximalIdeal R ^ N := by
      have := hL (max n N)
      rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top] at this
      rw [← neg_sub]
      exact neg_mem (Ideal.pow_le_pow_right (le_max_right n N) this)
    have h2 : u n - u (max n N) ∈ F.idealZ ^ n := by
      have := hu (le_max_left n N)
      rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top] at this
      exact this
    have : u n - L = (u n - u (max n N)) + (u (max n N) - L) := by ring
    have h3 : u (max n N) - L ∈ maximalIdeal R ^ N := by
      rw [← neg_sub]; exact neg_mem h1
    rw [this]
    exact add_mem (Ideal.mem_sup_left h2) (Ideal.mem_sup_right h3)
  exact { toIsHausdorff := hhaus, toIsPrecomplete := hprec }

end FrameCompletionB1

section FrameCompletion6

variable {R : Type u} [CommRing R] [IsRegularLocalRing R] (F : RegularFrame R)

/-- The expansion map of a regular frame of a complete local ring `R` is an isomorphism
`R ≃ S{z₁, …, z_r}`. -/
theorem RegularFrame.exists_isExpansion_bijective [IsAdicComplete (maximalIdeal R) R] :
    ∃ e : R →+* MvPowerSeries (Fin F.r) F.S, F.IsExpansion e ∧ Function.Bijective e ∧
      ∀ e' : R →+* MvPowerSeries (Fin F.r) F.S, F.IsExpansion e' → e' = e := by
  obtain ⟨-, -, e, he, huniq⟩ := F.idealZ_isPrime_and_completion
  have := F.isAdicComplete_idealZ
  exact ⟨e, he, RegularFrame.bijective_of_isExpansion F he, fun e' he' => huniq e' he'⟩

/-- If `R` is complete, so is the coefficient ring `S` of a regular frame of `R`
(`S ≅ R/(z)R`). -/
theorem RegularFrame.isAdicComplete_S [IsAdicComplete (maximalIdeal R) R] :
    IsAdicComplete (maximalIdeal F.S) F.S := by
  classical
  have hrt : ∀ s, F.retraction (algebraMap F.S R s) = s := F.retraction_algebraMap
  have hloc : ∀ s ∈ maximalIdeal F.S, algebraMap F.S R s ∈ maximalIdeal R := fun s hs =>
    (IsLocalRing.mem_maximalIdeal _).mpr fun hu =>
      ((IsLocalRing.mem_maximalIdeal s).mp hs) (isUnit_of_map_unit _ s hu)
  have hmap : ∀ n : ℕ, ∀ s ∈ maximalIdeal F.S ^ n, algebraMap F.S R s ∈ maximalIdeal R ^ n := by
    intro n s hs
    have : algebraMap F.S R s ∈ (maximalIdeal F.S ^ n).map (algebraMap F.S R) :=
      Ideal.mem_map_of_mem _ hs
    rw [Ideal.map_pow] at this
    exact Ideal.pow_right_mono (Ideal.map_le_iff_le_comap.mpr hloc) n this
  have hretr : ∀ n : ℕ, ∀ a ∈ maximalIdeal R ^ n, F.retraction a ∈ maximalIdeal F.S ^ n := by
    intro n a ha
    have hsurj : Function.Surjective F.retraction := fun s => ⟨algebraMap F.S R s, hrt s⟩
    have hlocr : IsLocalHom F.retraction := IsLocalHom.of_surjective _ hsurj
    have : F.retraction a ∈ (maximalIdeal R ^ n).map F.retraction := Ideal.mem_map_of_mem _ ha
    rw [Ideal.map_pow, IsLocalRing.map_maximalIdeal_of_surjective _ hsurj] at this
    exact this
  have hhaus : IsHausdorff (maximalIdeal F.S) F.S := by
    refine ⟨fun x hx => ?_⟩
    have hbot := Ideal.iInf_pow_eq_bot_of_isLocalRing (maximalIdeal F.S)
      (Ideal.IsPrime.ne_top inferInstance)
    have : x ∈ ⨅ n : ℕ, maximalIdeal F.S ^ n := by
      rw [Ideal.mem_iInf]
      intro n
      have := hx n
      rwa [SModEq.sub_mem, sub_zero, smul_eq_mul, Ideal.mul_top] at this
    rwa [hbot, Ideal.mem_bot] at this
  have hprec' : IsPrecomplete (maximalIdeal F.S) F.S := by
    refine ⟨fun u hu => ?_⟩
    have hprec := IsAdicComplete.toIsPrecomplete (I := maximalIdeal R) (M := R)
    obtain ⟨L, hL⟩ := IsPrecomplete.prec hprec (f := fun n => algebraMap F.S R (u n))
      fun {m n} hmn => by
        have := hu hmn
        rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top] at this ⊢
        rw [← map_sub]
        exact hmap m _ this
    refine ⟨F.retraction L, fun n => ?_⟩
    have := hL n
    rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top] at this ⊢
    have h2 := hretr n _ this
    rwa [map_sub, hrt] at h2
  exact { toIsHausdorff := hhaus, toIsPrecomplete := hprec' }

end FrameCompletion6

section TransportGraded

/-- The canonical homomorphism `gr_I(A) → gr_{I'}(B)` of a ring homomorphism `E : A → B` with
`E(I)B = I'` and `ν_{I'}(E a) = ν_I(a)` maps initial forms to initial forms, and is semilinear over
`A/I → B/I'`. -/
theorem exists_assocGraded_ringHom_of_map_eq {A B : Type u} [CommRing A] [CommRing B]
    (E : A →+* B) (I : Ideal A) (I' : Ideal B) (hI : I.map E = I')
    (hord : ∀ a, Ideal.ordElem I' (E a) = Ideal.ordElem I a) :
    ∃ (Γ : AssocGraded I →+* AssocGraded I') (Ē : A ⧸ I →+* B ⧸ I'),
      (∀ a, Γ (initialForm I a) = initialForm I' (E a)) ∧
      (∀ c, Γ (algebraMap (A ⧸ I) (AssocGraded I) c) =
        algebraMap (B ⧸ I') (AssocGraded I') (Ē c)) := by
  subst hI
  refine ⟨AssocGraded.map E I, Ideal.quotientMap (I.map E) E Ideal.le_comap_map, fun a => ?_, ?_⟩
  · by_cases htop : Ideal.ordElem I a = ⊤
    · have htop' : Ideal.ordElem (I.map E) (E a) = ⊤ := by rw [hord, htop]
      rw [initialForm, dite_eq_left htop, map_zero, initialForm, dite_eq_left htop']
    · obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp htop
      rw [initialForm_eq_mk I hn.symm, AssocGraded.map_mk,
        initialForm_eq_mk _ ((hord a).trans hn.symm)]
  · intro c
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective c
    have h1 : algebraMap (A ⧸ I) (AssocGraded I) (Ideal.Quotient.mk I a) =
        algebraMap A (AssocGraded I) a := rfl
    have h2 : algebraMap (B ⧸ I.map E) (AssocGraded (I.map E))
        (Ideal.quotientMap (I.map E) E Ideal.le_comap_map (Ideal.Quotient.mk I a)) =
        algebraMap B (AssocGraded (I.map E)) (E a) := rfl
    rw [h1, h2]
    show Ideal.Quotient.mk _ (reesMap E I (algebraMap A (reesAlgebra I) a)) = _
    exact congrArg (Ideal.Quotient.mk _) (Subtype.ext (by
      show Polynomial.map E (Polynomial.C a) = Polynomial.C (E a)
      exact Polynomial.map_C E))

end TransportGraded

section ESetMap

/-- The `E`-set of an ideal is contained in that of any ideal containing its image under an
injective change of coefficients. -/
theorem eSet_subset_of_map_le {S₀ S : Type u} [CommRing S₀] [CommRing S] (α : S₀ →+* S)
    (hα : Function.Injective α) {r : ℕ} (I₀ : Ideal (MvPolynomial (Fin r) S₀))
    (I : Ideal (MvPolynomial (Fin r) S)) (h : I₀.map (MvPolynomial.map α) ≤ I) :
    ESet I₀ ⊆ ESet I := by
  rintro A ⟨A₀, ⟨φ, hφI, hφ0, ⟨n, hn⟩, rfl⟩, B, rfl⟩
  refine ⟨EFunction (MvPolynomial.map α φ), ⟨MvPolynomial.map α φ, h (Ideal.mem_map_of_mem _ hφI),
    ?_, ⟨n, ?_⟩, rfl⟩, B, ?_⟩
  · intro h0
    exact hφ0 ((MvPolynomial.map_injective α hα) (by simpa using h0))
  · exact (MvPolynomial.mem_homogeneousSubmodule _ _ |>.mpr
      ((MvPolynomial.mem_homogeneousSubmodule _ _ |>.mp hn).map α))
  · congr 1
    simp only [EFunction, MvPolynomial.support_map_of_injective φ hα]

end ESetMap

section Lemma17Transport

variable {R : Type u} [CommRing R] [IsRegularLocalRing R] (F : RegularFrame R)

/-- An isomorphism `R ≃ S{z₁, …, z_r}` carries the associated subalgebra and the `E`-set of a
system of `R` into those of its image (the data of Lemma 17 for the power series ring). -/
theorem RegularFrame.IsExpansion.transport_of_bijective [IsAdicComplete (maximalIdeal R) R]
    {e : R →+* MvPowerSeries (Fin F.r) F.S} (he : F.IsExpansion e) (hbij : Function.Bijective e) :
    (∀ a, Ideal.ordElem (maximalIdeal (MvPowerSeries (Fin F.r) F.S)) (e a) =
      Ideal.ordElem (maximalIdeal R) a) ∧
    (∀ a, initialForm (maximalIdeal R) a ∈ F.assocSubalgebra →
      initialForm (maximalIdeal (MvPowerSeries (Fin F.r) F.S)) (e a) ∈
        Hironaka.assocSubalgebra (psVars F.S F.r)) ∧
    (∀ {i : ℕ} (f : Fin i → R), frameESet F.z f ⊆ frameESet (psVars F.S F.r) fun j => e (f j)) := by
  classical
  set B := MvPowerSeries (Fin F.r) F.S with hB
  let E : R ≃+* B := RingEquiv.ofBijective e hbij
  have hloc : IsLocalHom e := ⟨fun a ha => by
    have h1 := ha.map E.symm.toRingHom
    have h2 : E.symm (e a) = a := E.symm_apply_apply a
    rwa [RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, h2] at h1⟩
  have hM : (maximalIdeal R).map e = maximalIdeal B :=
    IsLocalRing.map_maximalIdeal_of_surjective e hbij.2
  have hmem : ∀ (ν : ℕ) (a : R), e a ∈ maximalIdeal B ^ ν ↔ a ∈ maximalIdeal R ^ ν := by
    intro ν a
    rw [← hM, ← Ideal.map_pow]
    refine ⟨fun h => ?_, Ideal.mem_map_of_mem e⟩
    rw [← Ideal.comap_map_of_bijective e hbij (I := maximalIdeal R ^ ν)]
    exact h
  have hord : ∀ a, Ideal.ordElem (maximalIdeal B) (e a) = Ideal.ordElem (maximalIdeal R) a := by
    intro a
    simp only [Ideal.ordElem, hmem]
  obtain ⟨Γ, Ē, hΓ1, hΓ2⟩ := exists_assocGraded_ringHom_of_map_eq e (maximalIdeal R)
    (maximalIdeal B) hM hord
  have hĒ : Function.Injective Ē := by
    let _ : Field (R ⧸ maximalIdeal R) := Ideal.Quotient.field _
    exact Ē.injective
  have key : ∀ ψ : MvPolynomial (Fin F.r) (R ⧸ maximalIdeal R),
      Γ (frameAlgHom F.z ψ) = frameAlgHom (psVars F.S F.r) (MvPolynomial.map Ē ψ) := by
    intro ψ
    induction ψ using MvPolynomial.induction_on with
    | C c =>
      simp only [frameAlgHom, MvPolynomial.aeval_C, MvPolynomial.map_C]
      exact hΓ2 c
    | add p q hp hq => simp only [map_add, hp, hq]
    | mul_X p j hp =>
      simp only [frameAlgHom, map_mul, MvPolynomial.map_X, MvPolynomial.aeval_X] at hp ⊢
      rw [hp]
      congr 1
      simp only [frameForm]
      rw [hΓ1, he.map_z]
      rfl
  refine ⟨hord, fun a ha => ?_, fun {i} f => ?_⟩
  · have ha' : initialForm (maximalIdeal R) a ∈ Hironaka.assocSubalgebra F.z := ha
    rw [Hironaka.assocSubalgebra, Algebra.adjoin_range_eq_range_aeval] at ha' ⊢
    obtain ⟨ψ, hψ⟩ := ha'
    refine ⟨MvPolynomial.map Ē ψ, ?_⟩
    have := key ψ
    simp only [frameAlgHom] at this
    have hψ' : MvPolynomial.aeval (frameForm F.z) ψ = initialForm (maximalIdeal R) a := hψ
    show MvPolynomial.aeval (frameForm (psVars F.S F.r)) (MvPolynomial.map Ē ψ) = _
    rw [← this, hψ', hΓ1]
  · refine eSet_subset_of_map_le Ē hĒ _ _ ?_
    rw [frameInitialIdeal, Ideal.map_span, Ideal.span_le]
    rintro _ ⟨ψ, ⟨j, hψ⟩, rfl⟩
    refine Ideal.subset_span ⟨j, ?_⟩
    rw [← key, hψ, hΓ1]

end Lemma17Transport

section Lemma17Frame

variable {R : Type u} [CommRing R] [IsRegularLocalRing R] (F : RegularFrame R)

/-- **Lemma 17 for a regular frame of a complete regular local ring** (pp. 246–248, in the form
used in footnote 11, p. 259): for `R = S{z₁, …, z_r}` complete, a system `(f_j)` whose initial
forms lie in the associated subalgebra `k[Z]` and an element `g`, there are `h_j` with
`ν_M(h_j) ≥ ν_M(g) - ν_M(f_j)` such that `g - Σ h_j f_j` is normalized by `(f_j)` with respect to
`(S; z₁, …, z_r)`. -/
theorem RegularFrame.exists_isNormalizedBy_sub_sum [IsAdicComplete (maximalIdeal R) R] {i : ℕ}
    (f : Fin i → R) (hf : ∀ j, initialForm (maximalIdeal R) (f j) ∈ F.assocSubalgebra) (g : R) :
    ∃ h : Fin i → R, (∀ j, Ideal.ordElem (maximalIdeal R) g -
        Ideal.ordElem (maximalIdeal R) (f j) ≤ Ideal.ordElem (maximalIdeal R) (h j)) ∧
      F.IsNormalizedBy f (g - ∑ j, h j * f j) := by
  classical
  obtain ⟨e, he, hbij, huniq⟩ := F.exists_isExpansion_bijective
  obtain ⟨hord, hsub, hE⟩ := he.transport_of_bijective F hbij
  have := F.isAdicComplete_S
  obtain ⟨ĥ, hĥ1, hĥ2⟩ := exists_normalized_of_isAdicComplete (S := F.S) (r := F.r)
    (fun j => e (f j)) (fun j => hsub _ (hf j)) (e g)
  choose h hh using fun j => hbij.2 (ĥ j)
  refine ⟨h, fun j => ?_, ?_⟩
  · have := hĥ1 j
    rwa [← hh j, hord, hord, hord] at this
  · intro e' he' A hA
    rw [huniq e' he']
    have : e (g - ∑ j, h j * f j) = e g - ∑ j, ĥ j * e (f j) := by
      simp only [map_sub, map_sum, map_mul, hh]
    rw [this]
    exact hĥ2 A (hE f hA)

end Lemma17Frame

section StandardBaseStep

variable {S : Type u} [CommRing S] [IsRegularLocalRing S]

/-- Let `(G₁, …, G_m)` be a standard base of `J`, `k < m`, and `h_j` (`j < k`) elements with
`ν_M(h_j) ≥ ν_M(G_k) - ν_M(G_j)`.  Then `a = G_k - Σ_{j<k} h_j G_j` has `ν_M(a) = ν_M(G_k)` and
its initial form is not in the ideal generated by the initial forms of `G_j`, `j < k`
(footnote 11, p. 259: "It is clear from the above properties of the `h_p` ..."). -/
theorem ordElem_sub_sum_eq_and_initialForm_notMem (J : Ideal S) {m : ℕ} (G : Fin m → S)
    (hG : IsStandardBase S J G) (k : Fin m) (h : Fin k → S)
    (hh : ∀ j : Fin k, Ideal.ordElem (maximalIdeal S) (G k) -
      Ideal.ordElem (maximalIdeal S) (G (Fin.castLE k.2.le j)) ≤
        Ideal.ordElem (maximalIdeal S) (h j)) :
    Ideal.ordElem (maximalIdeal S) (G k - ∑ j, h j * G (Fin.castLE k.2.le j)) =
        Ideal.ordElem (maximalIdeal S) (G k) ∧
      initialForm (maximalIdeal S) (G k - ∑ j, h j * G (Fin.castLE k.2.le j)) ∉
        Ideal.span (Set.range fun j : Fin k =>
          initialForm (maximalIdeal S) (G (Fin.castLE k.2.le j))) := by
  classical
  obtain ⟨hGJ, hφJ, ⟨d, hd, hmono⟩, hspan, hirr⟩ := hG
  have hgM : ∀ j, Ideal.ordElem (maximalIdeal S) (G j) = d j := fun j =>
    ordElem_eq_of_isStandardBase_of_initialForm_mem_homogeneous J G
      ⟨hGJ, hφJ, ⟨d, hd, hmono⟩, hspan, hirr⟩ d hd j
  have hνle : ∀ j : Fin k, d (Fin.castLE k.2.le j) ≤ d k := fun j =>
    hmono (by simp [Fin.le_def])
  have hhmem : ∀ j : Fin k, h j ∈ maximalIdeal S ^ (d k - d (Fin.castLE k.2.le j)) := by
    intro j
    refine Ideal.mem_pow_of_le_ordElem ?_
    refine le_trans ?_ (hh j)
    rw [hgM, hgM]
    exact (ENat.natCast_sub (d k) (d (Fin.castLE k.2.le j))).symm.le
  have hGj : ∀ j : Fin k, G (Fin.castLE k.2.le j) ∈ maximalIdeal S ^ d (Fin.castLE k.2.le j) :=
    fun j => Ideal.mem_pow_of_ordElem (hgM _)
  have hGk : G k ∈ maximalIdeal S ^ d k := Ideal.mem_pow_of_ordElem (hgM k)
  have hprod : ∀ j : Fin k, h j * G (Fin.castLE k.2.le j) ∈ maximalIdeal S ^ d k := fun j => by
    have := Ideal.mul_mem_mul (hhmem j) (hGj j)
    rwa [← pow_add, Nat.sub_add_cancel (hνle j)] at this
  set β : Fin k → AssocGraded (maximalIdeal S) := fun j =>
    AssocGraded.mk (maximalIdeal S) _ (h j) (hhmem j) with hβ
  have hmk : AssocGraded.mk (maximalIdeal S) (d k) (G k - ∑ j, h j * G (Fin.castLE k.2.le j))
      (sub_mem hGk (sum_mem fun j _ => hprod j)) =
      initialForm (maximalIdeal S) (G k) -
        ∑ j : Fin k, β j * initialForm (maximalIdeal S) (G (Fin.castLE k.2.le j)) := by
    rw [AssocGraded.mk_sub _ _ _ _ hGk (sum_mem fun j _ => hprod j),
      AssocGraded.mk_sum _ _ _ _ hprod, initialForm_eq_mk _ (hgM k)]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [initialForm_eq_mk _ (hgM _), hβ, AssocGraded.mk_mul_mk]
    have := hνle j
    congr 1
    omega
  have hirrk : initialForm (maximalIdeal S) (G k) ∉
      Ideal.span (Set.range fun j : Fin k =>
        initialForm (maximalIdeal S) (G (Fin.castLE k.2.le j))) :=
    hirr k
  have hsum_mem : ∑ j : Fin k, β j * initialForm (maximalIdeal S) (G (Fin.castLE k.2.le j)) ∈
      Ideal.span (Set.range fun j : Fin k => initialForm (maximalIdeal S)
        (G (Fin.castLE k.2.le j))) :=
    Ideal.sum_mem _ fun j _ => Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨j, rfl⟩)
  have hne : AssocGraded.mk (maximalIdeal S) (d k) (G k - ∑ j, h j * G (Fin.castLE k.2.le j))
      (sub_mem hGk (sum_mem fun j _ => hprod j)) ≠ 0 := by
    rw [hmk]
    intro h0
    apply hirrk
    have := sub_eq_zero.mp h0
    rw [this]
    exact hsum_mem
  obtain ⟨hord, hin⟩ := Ideal.ordElem_eq_of_mk_ne_zero _ _ hne
  refine ⟨by rw [hord, hgM], ?_⟩
  rw [hin, hmk]
  intro hmem
  apply hirrk
  have := add_mem hmem hsum_mem
  rwa [sub_add_cancel] at this

end StandardBaseStep

section TauHelpers

variable {R : Type u} [CommRing R] [IsRegularLocalRing R]

/-- The initial form of a member of a regular system of parameters has degree `1`. -/
theorem RegularFrame.frameForm_mem_homogeneous_one (F : RegularFrame R) (j : Fin F.r) :
    frameForm F.z j ∈ AssocGraded.homogeneous (maximalIdeal R) 1 := by
  classical
  have hmem : F.z j ∈ maximalIdeal R :=
    F.extends_rsop.mem_maximalIdeal (Finset.mem_image_of_mem F.z (Finset.mem_univ j))
  have hsq : F.z j ∉ maximalIdeal R ^ 2 :=
    F.extends_rsop.notMem_maximalIdeal_sq (Finset.mem_image_of_mem F.z (Finset.mem_univ j))
  have hord : Ideal.ordElem (maximalIdeal R) (F.z j) = ((1 : ℕ) : ℕ∞) := by
    refine le_antisymm (Ideal.ordElem_le_of_notMem (m := 1) hsq) ?_
    exact Ideal.le_ordElem (by rwa [pow_one])
  rw [frameForm, initialForm_eq_mk _ hord]
  exact AssocGraded.mk_mem_homogeneous _ _

/-- If the initial form of `f` lies in the associated subalgebra `k[Z]` of a regular frame, then
`τ_{(z)}(f) = 0`. -/
theorem RegularFrame.tauZ_eq_zero_of_initialForm_mem (F : RegularFrame R) (f : R)
    (hf : initialForm (maximalIdeal R) f ∈ F.assocSubalgebra) :
    tauZ R F.z (fun _ : Fin 1 => f) = 0 := by
  classical
  set W : Submodule (R ⧸ maximalIdeal R) (AssocGraded (maximalIdeal R)) :=
    Submodule.span (R ⧸ maximalIdeal R) (Set.range (frameForm F.z)) with hW
  have hWspec : IsTauZSubmodule R (fun _ : Fin 1 => f) W := by
    refine ⟨?_, ?_⟩
    · refine Submodule.span_le.mpr ?_
      rintro _ ⟨j, rfl⟩
      exact F.frameForm_mem_homogeneous_one j
    · apply le_antisymm
      · refine Ideal.span_le.mpr fun x hx => hx.1
      · refine Ideal.span_mono ?_
        intro x hx
        obtain ⟨j, rfl⟩ := hx
        refine ⟨Ideal.subset_span ⟨0, rfl⟩, ?_⟩
        have hf' : initialForm (maximalIdeal R) f ∈ Hironaka.assocSubalgebra F.z := hf
        have hle : Algebra.adjoin (R ⧸ maximalIdeal R) (Set.range (frameForm F.z)) ≤
            Algebra.adjoin (R ⧸ maximalIdeal R) (W : Set (AssocGraded (maximalIdeal R))) :=
          Algebra.adjoin_mono Submodule.subset_span
        exact hle hf'
  have hT : tauZSubmodule R (fun _ : Fin 1 => f) ≤ W := sInf_le hWspec
  have hstar : tauZSubmoduleStar R F.z (fun _ : Fin 1 => f) ≤ W := by
    unfold tauZSubmoduleStar
    exact sup_le hT le_rfl
  have hfin : Module.finrank (R ⧸ maximalIdeal R) (tauZSubmoduleStar R F.z (fun _ : Fin 1 => f)) ≤
      F.r := by
    have : Module.Finite (R ⧸ maximalIdeal R) W :=
      Module.Finite.span_of_finite _ (Set.finite_range _)
    refine (Submodule.finrank_mono hstar).trans ?_
    refine (finrank_range_le_card (frameForm F.z)).trans ?_
    simp
  unfold tauZ
  exact Nat.sub_eq_zero_of_le hfin

end TauHelpers

section TauHelpers2

variable {R : Type u} [CommRing R] [IsRegularLocalRing R] (J : Ideal R)

/-- `τ^{(b)}(J) ≤ τ^{(a)}(J)` for `1 ≤ b ≤ a ≤ t(J)`. -/
theorem tau_le_tau_of_le {b a : ℕ} (hb : 1 ≤ b) (hba : b ≤ a) (hat : a ≤ t R J) :
    tau R J b ≤ tau R J a := by
  induction a, hba using Nat.le_induction with
  | base => exact le_rfl
  | succ a hba ih =>
    exact (ih (by omega)).trans (tauSubmodule_mono R J (a + 1) (by omega) hat).2
      |> fun h => by simpa using h

/-- If `ν^{(k)}(J) = μ` is finite then `μ = μ^{(a)}(J)` for some `1 ≤ a ≤ t(J)`. -/
theorem exists_mu_eq_of_nuI_eq (k : ℕ+) (μ : ℕ) (hk : nuI R J k = (μ : ℕ∞)) :
    ∃ a : ℕ, 1 ≤ a ∧ a ≤ t R J ∧ mu R J a = μ := by
  have hmem : μ ∈ muSet R J := ⟨k, hk⟩
  have hfin : (muSet R J).Finite := (muSet_finite R J).1
  obtain ⟨n, hn, hnth⟩ := Nat.exists_lt_card_nth_eq hmem
  refine ⟨n + 1, by omega, ?_, by simpa [mu] using hnth⟩
  have := hn hfin
  rw [t, Set.ncard_eq_toFinset_card _ hfin]
  omega

/-- A standard base is not shorter than another. -/
theorem le_length_of_isStandardBase {m m' : ℕ} {g : Fin m → R} {g' : Fin m' → R}
    (hg : IsStandardBase R J g) (hg' : IsStandardBase R J g') : m' ≤ m := by
  obtain ⟨⟨d, hd, hnu⟩, hbig⟩ := nuI_eq_of_hasLemma1Properties R J _ hg.2
  obtain ⟨⟨d', hd', hnu'⟩, hbig'⟩ := nuI_eq_of_hasLemma1Properties R J _ hg'.2
  by_contra hlt
  push Not at hlt
  have h1 := hbig ⟨m + 1, Nat.succ_pos _⟩ (by simp)
  have h2 := hnu' ⟨m, hlt⟩
  rw [h1] at h2
  exact ENat.top_ne_natCast _ h2

/-- Two standard bases of the same ideal have the same length. -/
theorem length_eq_of_isStandardBase {m m' : ℕ} {g : Fin m → R} {g' : Fin m' → R}
    (hg : IsStandardBase R J g) (hg' : IsStandardBase R J g') : m = m' :=
  le_antisymm (le_length_of_isStandardBase J hg' hg) (le_length_of_isStandardBase J hg hg')

end TauHelpers2

section NormalizedSnoc

variable {R : Type u} [CommRing R] [IsRegularLocalRing R] (F : RegularFrame R)

/-- Appending to a normalized system an element which is normalized by it and whose initial form
lies in the associated subalgebra gives a normalized system. -/
theorem RegularFrame.isNormalizedSystem_snoc {i : ℕ} (f : Fin i → R) (f' : R)
    (hf : F.IsNormalizedSystem f) (hf'1 : initialForm (maximalIdeal R) f' ∈ F.assocSubalgebra)
    (hf'2 : F.IsNormalizedBy f f') :
    F.IsNormalizedSystem (Fin.snoc f f' : Fin (i + 1) → R) := by
  refine ⟨fun j => ?_, fun j => ?_⟩
  · induction j using Fin.lastCases with
    | last => simpa using hf'1
    | cast j => simpa using hf.1 j
  · induction j using Fin.lastCases with
    | last =>
      have hfun : (fun l : Fin (Fin.last i : ℕ) =>
          (Fin.snoc f f' : Fin (i + 1) → R) (Fin.castLE (Fin.last i).2.le l)) = f := by
        funext l
        have h1 : Fin.castLE (Fin.last i).2.le l = Fin.castSucc (n := i) l := Fin.ext rfl
        rw [h1, Fin.snoc_castSucc]
      have key : F.IsNormalizedBy (fun l : Fin (Fin.last i : ℕ) =>
          (Fin.snoc f f' : Fin (i + 1) → R) (Fin.castLE (Fin.last i).2.le l))
          ((Fin.snoc f f' : Fin (i + 1) → R) (Fin.last i)) := by
        rw [hfun, Fin.snoc_last]
        exact hf'2
      exact key
    | cast j =>
      have hfun : (fun l : Fin ((Fin.castSucc j : Fin (i + 1)) : ℕ) =>
          (Fin.snoc f f' : Fin (i + 1) → R) (Fin.castLE (Fin.castSucc j).2.le l)) =
          fun l : Fin (j : ℕ) => f (Fin.castLE j.2.le l) := by
        funext l
        have h1 : Fin.castLE (Fin.castSucc j).2.le l =
            Fin.castSucc (n := i) (Fin.castLE j.2.le l) := Fin.ext rfl
        rw [h1, Fin.snoc_castSucc]
      have key : F.IsNormalizedBy (fun l : Fin ((Fin.castSucc j : Fin (i + 1)) : ℕ) =>
          (Fin.snoc f f' : Fin (i + 1) → R) (Fin.castLE (Fin.castSucc j).2.le l))
          ((Fin.snoc f f' : Fin (i + 1) → R) (Fin.castSucc j)) := by
        rw [hfun, Fin.snoc_castSucc]
        exact hf.2 j
      exact key

end NormalizedSnoc

section TauFrame

variable {R : Type u} [CommRing R] [IsRegularLocalRing R] (F : RegularFrame R) (J : Ideal R)

/-- The members `z_j` of a regular frame lie in the maximal ideal. -/
theorem RegularFrame.mem_maximalIdeal_z (j : Fin F.r) : F.z j ∈ maximalIdeal R := by
  classical
  exact F.extends_rsop.mem_maximalIdeal (Finset.mem_image_of_mem F.z (Finset.mem_univ j))

/-- The initial form of `z_j` is the class `[z_j] ∈ M/M² = gr¹_M(R)`. -/
theorem RegularFrame.frameForm_eq_mk (j : Fin F.r) :
    frameForm F.z j = AssocGraded.mk (maximalIdeal R) 1 (F.z j)
      (by rw [pow_one]; exact F.mem_maximalIdeal_z j) := by
  classical
  have hsq : F.z j ∉ maximalIdeal R ^ 2 :=
    F.extends_rsop.notMem_maximalIdeal_sq (Finset.mem_image_of_mem F.z (Finset.mem_univ j))
  have hmem : F.z j ∈ maximalIdeal R :=
    F.extends_rsop.mem_maximalIdeal (Finset.mem_image_of_mem F.z (Finset.mem_univ j))
  have hord : Ideal.ordElem (maximalIdeal R) (F.z j) = ((1 : ℕ) : ℕ∞) := by
    refine le_antisymm (Ideal.ordElem_le_of_notMem (m := 1) hsq) ?_
    exact Ideal.le_ordElem (by rwa [pow_one])
  rw [frameForm, initialForm_eq_mk _ hord]

/-- A regular `τ`-frame `(S; z)` of `R` for `J` gives, for each `1 ≤ a ≤ t(J)`, a regular system
of `a`-th `τ`-parameters of `R` for `J` consisting of members of `z` (Definition 10). -/
theorem RegularFrame.IsRegularTauFrame.exists_isRegularSystemOfTauParameters
    (hF : F.IsRegularTauFrame J) {a : ℕ} (ha : 1 ≤ a) (hat : a ≤ t R J) :
    ∃ x : Fin (tau R J a) → maximalIdeal R, IsRegularSystemOfTauParameters R J a x ∧
      ∀ i, ∃ k, (x i : R) = F.z k := by
  obtain ⟨hτ, hz, hreg⟩ := hF
  have hale : tau R J a ≤ F.r := hτ ▸ tau_le_tau_of_le J ha hat le_rfl
  let x : Fin (tau R J a) → maximalIdeal R := fun i => ⟨F.z ⟨i, lt_of_lt_of_le i.2 hale⟩, hz _⟩
  refine ⟨x, fun b hb1 hba => ?_, fun i => ⟨⟨i, lt_of_lt_of_le i.2 hale⟩, rfl⟩⟩
  have hbt : b ≤ t R J := hba.trans hat
  have hbalt : tau R J b ≤ tau R J a := tau_le_tau_of_le J hb1 hba hat
  have h1 := hreg b hb1 hbt
  convert h1 using 2
  ext y
  simp only [Set.mem_range]
  constructor
  · rintro ⟨⟨i, hi⟩, rfl⟩
    refine ⟨⟨⟨i, hτ ▸ lt_of_lt_of_le i.2 hale⟩, hi⟩, ?_⟩
    rfl
  · rintro ⟨⟨i, hi⟩, rfl⟩
    refine ⟨⟨⟨i, lt_of_lt_of_le hi hbalt⟩, hi⟩, ?_⟩
    rfl

end TauFrame

section NormalizedBaseExistence

variable {R : Type u} [CommRing R] [IsRegularLocalRing R] (F : RegularFrame R) (J : Ideal R)

/-- **The inductive step of footnote 11** (p. 259): if `(f₁, …, f_i)` is a normalized system of
elements of `J` which can be extended to a standard base `G` of `J` with `i < #G`, then there is
`f' ∈ J` such that `(f₁, …, f_i, f')` is again a normalized system which can be extended to a
standard base of `J`. -/
theorem RegularFrame.exists_snoc_isNormalizedSystem [IsAdicComplete (maximalIdeal R) R]
    (hF : F.IsRegularTauFrame J) {i : ℕ} (f : Fin i → R) (hfJ : ∀ j, f j ∈ J)
    (hext : ExtendsToStandardBase J f) (hnorm : F.IsNormalizedSystem f) {m' : ℕ} (G : Fin m' → R)
    (hG : IsStandardBase R J G) (hi : i < m') (hGf : ∀ j : Fin i, G (Fin.castLE hi.le j) = f j) :
    ∃ f' : R, f' ∈ J ∧ ExtendsToStandardBase J (Fin.snoc f f' : Fin (i + 1) → R) ∧
      F.IsNormalizedSystem (Fin.snoc f f' : Fin (i + 1) → R) := by
  classical
  set k : Fin m' := ⟨i, hi⟩ with hk
  have hfsub : ∀ j, initialForm (maximalIdeal R) (f j) ∈ F.assocSubalgebra := hnorm.1
  obtain ⟨h, hh1, hh2⟩ := F.exists_isNormalizedBy_sub_sum f hfsub (G k)
  set f' := G k - ∑ j, h j * f j with hf'
  -- the data of the standard base
  obtain ⟨hGJ, hφJ, ⟨d, hd, hmono⟩, hspan, hirr⟩ := hG
  have hGstd : IsStandardBase R J G := ⟨hGJ, hφJ, ⟨d, hd, hmono⟩, hspan, hirr⟩
  have hgM : ∀ j, Ideal.ordElem (maximalIdeal R) (G j) = d j := fun j =>
    ordElem_eq_of_isStandardBase_of_initialForm_mem_homogeneous J G hGstd d hd j
  have hGf' : ∀ j : Fin (k : ℕ), G (Fin.castLE k.2.le j) = f j := hGf
  have hhh : ∀ j : Fin (k : ℕ), Ideal.ordElem (maximalIdeal R) (G k) -
      Ideal.ordElem (maximalIdeal R) (G (Fin.castLE k.2.le j)) ≤
        Ideal.ordElem (maximalIdeal R) (h j) := fun j => by
    rw [hGf' j]; exact hh1 j
  obtain ⟨hord, hirrf'⟩ := ordElem_sub_sum_eq_and_initialForm_notMem J G hGstd k h hhh
  have hsumeq : ∑ j : Fin (k : ℕ), h j * G (Fin.castLE k.2.le j) = ∑ j, h j * f j :=
    Finset.sum_congr rfl fun j _ => by rw [hGf' j]
  rw [hsumeq] at hord hirrf'
  have hrange : (Set.range fun j : Fin (k : ℕ) =>
      initialForm (maximalIdeal R) (G (Fin.castLE k.2.le j))) =
      Set.range fun j : Fin i => initialForm (maximalIdeal R) (f j) := by
    congr 1; funext j; rw [hGf' j]
  rw [hrange] at hirrf'
  have hf'J : f' ∈ J := sub_mem (hGJ k) (Ideal.sum_mem _ fun j _ => J.mul_mem_left _ (hfJ j))
  -- extension to a standard base
  have hlow : ∀ j : Fin i, Ideal.ordElem (maximalIdeal R) (f j) ≤ d k := fun j => by
    rw [← hGf j, hgM]
    exact_mod_cast hmono (by simp [Fin.le_def, k])
  have hup : ((d k : ℕ) : ℕ∞) ≤ nuI R J i.succPNat := by
    have := ordElem_eq_nuI_of_isStandardBase J G hGstd k
    rw [hgM] at this
    exact this.le
  have hext' : ExtendsToStandardBase J (Fin.snoc f f' : Fin (i + 1) → R) :=
    extendsToStandardBase_snoc J f f' hext hf'J (d k) (by rw [hord, hgM]) hlow hup hirrf'
  refine ⟨f', hf'J, hext', ?_⟩
  -- the initial form of `f'` lies in `k[Z]` (Lemma 19)
  obtain ⟨a, ha1, hat, hmua⟩ := exists_mu_eq_of_nuI_eq J i.succPNat (d k) (by
    have := ordElem_eq_nuI_of_isStandardBase J G hGstd k
    rw [hgM] at this
    exact this.symm)
  obtain ⟨x, hx, hxz⟩ :=
    RegularFrame.IsRegularTauFrame.exists_isRegularSystemOfTauParameters F J hF ha1 hat
  have hν : nuI R J i.succPNat = ((d k : ℕ) : ℕ∞) := by
    have := ordElem_eq_nuI_of_isStandardBase J G hGstd k
    rw [hgM] at this
    exact this.symm
  have hmu : (mu R J a : ℕ∞) = nuI R J i.succPNat := by rw [hmua, hν]
  have h19 := initialForm_mem_adjoin_of_isNormalizedBy F J f hfJ
    (fun j => F.tauZ_eq_zero_of_initialForm_mem (f j) (hfsub j)) f' hf'J a ha1 hmu hext' hh2 x hx
  have hstar : tauParamsSubmoduleStar J a x F.z ≤
      (Hironaka.assocSubalgebra F.z).toSubmodule := by
    unfold tauParamsSubmoduleStar
    refine Submodule.span_le.mpr ?_
    rintro _ (⟨i', rfl⟩ | ⟨j, rfl⟩)
    · obtain ⟨k', hk'⟩ := hxz i'
      have : linearForms R x i' = frameForm F.z k' := by
        rw [F.frameForm_eq_mk k']
        simp only [linearForms]
        congr 1
      rw [this]
      exact Algebra.subset_adjoin ⟨k', rfl⟩
    · exact Algebra.subset_adjoin ⟨j, rfl⟩
  have hsub : Algebra.adjoin (R ⧸ maximalIdeal R)
      ((tauParamsSubmoduleStar J a x F.z : Submodule (R ⧸ maximalIdeal R)
        (AssocGraded (maximalIdeal R))) : Set (AssocGraded (maximalIdeal R))) ≤
      Hironaka.assocSubalgebra F.z := Algebra.adjoin_le fun y hy => hstar hy
  exact F.isNormalizedSystem_snoc f f' hnorm (hsub h19) hh2

end NormalizedBaseExistence

section NormalizedBaseExistence2

variable {R : Type u} [CommRing R] [IsRegularLocalRing R] (F : RegularFrame R) (J : Ideal R)

/-- **Footnote 11, p. 259**: for a complete regular local ring `R` and a regular `τ`-frame
`(S; z)` of `R` for `J`, there exists a normalized standard base of `J` with respect to
`(S; z)`. -/
theorem RegularFrame.exists_isNormalizedStandardBase [IsAdicComplete (maximalIdeal R) R]
    (hF : F.IsRegularTauFrame J) : ∃ (m : ℕ) (f : Fin m → R), F.IsNormalizedStandardBase J f := by
  classical
  obtain ⟨m0, G0, hG0⟩ := exists_isStandardBase J
  have key : ∀ n i (f : Fin i → R), i + n = m0 → (∀ j, f j ∈ J) → ExtendsToStandardBase J f →
      F.IsNormalizedSystem f → ∃ (m : ℕ) (g : Fin m → R), F.IsNormalizedStandardBase J g := by
    intro n
    induction n with
    | zero =>
      intro i f hi hfJ hext hnorm
      obtain ⟨m', G, hle, hG, hGf⟩ := hext
      have hm' : m' = m0 := length_eq_of_isStandardBase J hG hG0
      have him : m' = i := by omega
      subst him
      have hfG : f = G := funext fun j => by rw [← hGf j]; rfl
      subst hfG
      exact ⟨m', f, hG, hnorm⟩
    | succ n ih =>
      intro i f hi hfJ hext hnorm
      obtain ⟨m', G, hle, hG, hGf⟩ := hext
      have hm' : m' = m0 := length_eq_of_isStandardBase J hG hG0
      have hlt : i < m' := by omega
      obtain ⟨f', hf'J, hext', hnorm'⟩ := F.exists_snoc_isNormalizedSystem J hF f hfJ
        ⟨m', G, hle, hG, hGf⟩ hnorm G hG hlt hGf
      refine ih (i + 1) (Fin.snoc f f') (by omega) ?_ hext' hnorm'
      intro j
      induction j using Fin.lastCases with
      | last => simpa using hf'J
      | cast j => simpa using hfJ j
  exact key m0 0 (fun j => j.elim0) (by omega) (fun j => j.elim0)
    ⟨m0, G0, Nat.zero_le _, hG0, fun j => j.elim0⟩ ⟨fun j => j.elim0, fun j => j.elim0⟩

end NormalizedBaseExistence2

end Hironaka
