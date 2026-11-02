/-
Copyright (c) 2026 Daattavya Aggarwal, Minhyong Kim, Oisin Kim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daattavya Aggarwal, Minhyong Kim, Oisin Kim
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.RingTheory.Ideal.AssociatedPrime.Basic
public import Mathlib.RingTheory.Ideal.MinimalPrime.Localization
public import Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian
public import Mathlib.RingTheory.KrullDimension.Zero
public import Mathlib.RingTheory.LocalProperties.Reduced
public import Mathlib.RingTheory.Nilpotent.Lemmas
public import Mathlib.RingTheory.RingHom.Flat
public import Architect
public import Hironaka.Compat.MainISystem
public import Hironaka.Compat.MonoidalSuccessionBaseChange
public import Hironaka.Compat.SingularStandardBase
public import Hironaka.Compat.CompletionStalk
public import Hironaka.Compat.FlatLocalRegularity
public import Hironaka.Compat.AdicCompletionRegular
public import Hironaka.Compat.BlowupBaseChange
public import Hironaka.Ch4.ImplicationsAB
public import Hironaka.Statements

/-!
# Main Theorem I(n), p. 175: the completed data and class 𝔅 (ii)

> We have a canonical morphism of `V̂₀` to `V₀`. … Hence, in view of the property (ii) of the class 𝔅 (in the
> beginning of this chapter), we have `Ŝ(r) = c_r⁻¹(S(r))` where `Ŝ(r)` denotes the complement in `Ŵ(r)` of the set
> of those simple points of `Ŵ(r)` at which all the `V̂_j(r)` for `0 ≤ j ≤ β` are normally flat along `Ŵ(r)`. …
> Obviously, `B̂_i`, `Ŵ(i)` and the `V̂_j(i)` for all `j` satisfy the conditions (1), (2) and (3).  (p. 175)

Contents:
* the transfer of simple points and of normal flatness along the flat completion square
  `Ŷ = Y ×_X Spec(Ô_{X,x})` in both directions: simple points ascend by class 𝔅 (ii)
  (`isRegularLocalRing_quotient_stalk_totalTransform_of_isPullback_completion`, Compat/SingularStandardBase) and
  descend by flat descent of regularity (`isRegularLocalRing_of_flat_of_isRegularLocalRing`, cited, footnote 3);
  normal flatness ascends by flat base change and descends by faithful flatness (`Module.FaithfullyFlat.of_flat_of_isLocalHom`,
  `isNormallyFlatAlongIdeal_iff_of_faithfullyFlat`; public wrappers of the private versions in Ch2/AscendingChain and
  Ch3/Stability are needed);
* `Ŝ(r) = c_r⁻¹(S(r))`;
* the base change of `Ŵ` is reduced and of a non-singular subscheme non-singular (class 𝔅 (ii) + flatness; the
  paper uses the reducedness of `Ŵ(r)` silently, when it applies "the previous result" to it);
* the hatted properties (1̂), (2), (3) of the base change of a succession satisfying (1), (2), (3).
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace IsLocalRing
open scoped TensorProduct

namespace Hironaka

universe u

/-- A flat homomorphism `φ : B → B'` of noetherian rings with `B` reduced and all localizations of `B'` at the primes lying
over minimal primes of `B` reduced has `B'` reduced: a nonzero nilpotent `n` has a nonzero nilpotent multiple `m` with
prime annihilator `P`; elements of `φ⁻¹(P)` are zero divisors of `B'`, hence (flatness) of `B`, so lie in a minimal prime
(`B` reduced, prime avoidance), and `φ⁻¹(P)` is itself minimal; then `m/1 = 0` in `B'_P` gives `t ∉ P` with `t m = 0`,
absurd. -/
theorem isReduced_of_flat_of_isReduced_localization_minimalPrimes {B B' : Type u} [CommRing B] [CommRing B']
    [IsNoetherianRing B] [IsNoetherianRing B'] [_root_.IsReduced B] {φ : B →+* B'} (hφ : φ.Flat)
    (h : ∀ (P : Ideal B') [P.IsPrime], P.comap φ ∈ minimalPrimes B → _root_.IsReduced (Localization.AtPrime P)) :
    _root_.IsReduced B' := by
  refine ⟨fun n hn => ?_⟩
  by_contra hne
  let M : Submodule B' B' := Ideal.span {n}
  have hMne : M ≠ ⊥ := by
    intro hM
    apply hne
    have : n ∈ M := Ideal.subset_span rfl
    rw [hM] at this
    simpa using this
  have : Nontrivial M := Submodule.nontrivial_iff_ne_bot.mpr hMne
  obtain ⟨P, hP⟩ := associatedPrimes.nonempty B' M
  obtain ⟨hPprime, m, hPm⟩ := isAssociatedPrime_iff.mp hP
  have hmP : ∀ r : B', r ∈ P ↔ r * (m : B') = 0 := by
    intro r
    rw [hPm, Submodule.mem_colon_singleton, Submodule.mem_bot]
    exact ⟨fun h => by simpa using congrArg Subtype.val h, fun h => Subtype.ext (by simpa using h)⟩
  have hm0 : (m : B') ≠ 0 := by
    intro h0
    apply hPprime.ne_top
    rw [Ideal.eq_top_iff_one, hmP, h0, mul_zero]
  have hmnil : IsNilpotent (m : B') := by
    obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.mp m.2
    obtain ⟨k, hk⟩ := hn
    refine ⟨k, ?_⟩
    rw [← ha, mul_pow, hk, mul_zero]
  -- `φ⁻¹(P)` is a minimal prime of `B`
  have hQ : P.comap φ ∈ minimalPrimes B := by
    have hQprime : (P.comap φ).IsPrime := Ideal.comap_isPrime φ P
    have hsub : ((P.comap φ : Ideal B) : Set B) ⊆ ⋃ η ∈ minimalPrimes B, (η : Set B) := by
      intro s hs
      have hs' : φ s * (m : B') = 0 := (hmP _).mp hs
      have hsnz : s ∉ nonZeroDivisors B := by
        intro hsn
        have := flat_map_mem_nonZeroDivisors hφ hsn
        exact hm0 (mem_nonZeroDivisors_iff_right.mp this _ (by rw [mul_comm]; exact hs'))
      obtain ⟨b, hbs, hb0⟩ : ∃ b, b * s = 0 ∧ b ≠ 0 := by
        by_contra hcon
        exact hsnz (mem_nonZeroDivisors_iff_right.mpr fun b hb =>
          by_contra fun hb0 => hcon ⟨b, hb, hb0⟩)
      obtain ⟨η, hη, hbη⟩ : ∃ η ∈ minimalPrimes B, b ∉ η := by
        by_contra hcon
        push Not at hcon
        apply hb0
        have hb : b ∈ sInf (minimalPrimes B) := Ideal.mem_sInf.mpr fun I hI => hcon I hI
        have : b ∈ (⊥ : Ideal B).radical := by
          rw [← Ideal.sInf_minimalPrimes]; exact hb
        obtain ⟨k, hk⟩ := this
        exact _root_.IsReduced.eq_zero b ⟨k, by simpa using hk⟩
      have hsη : s ∈ η := by
        have hprime : η.IsPrime := hη.1.1
        have : b * s ∈ η := by rw [hbs]; exact η.zero_mem
        exact (hprime.mem_or_mem this).resolve_left hbη
      exact Set.mem_biUnion hη hsη
    obtain ⟨η, hη, hQη⟩ := (Ideal.subset_union_prime_finite
      (minimalPrimes.finite_of_isNoetherianRing B) (⊥ : Ideal B) ⊥
      (fun i hi _ _ => hi.1.1)).mp hsub
    refine ⟨⟨hQprime, bot_le⟩, fun q hq hqQ => ?_⟩
    exact hQη.trans (hη.2 hq (hqQ.trans hQη))
  have := hPprime
  have hred := h P hQ
  have hz : algebraMap B' (Localization.AtPrime P) (m : B') = 0 :=
    _root_.IsReduced.eq_zero _ (hmnil.map (algebraMap B' (Localization.AtPrime P)))
  obtain ⟨t, ht⟩ := (IsLocalization.map_eq_zero_iff P.primeCompl (Localization.AtPrime P) _).mp hz
  exact t.2 ((hmP _).mpr ht)


/-- The localization of a reduced noetherian ring at a minimal prime is a regular local ring (it is a field). -/
theorem isRegularLocalRing_localization_of_mem_minimalPrimes {A : Type u} [CommRing A] [_root_.IsReduced A]
    [IsNoetherianRing A] (η : Ideal A) [η.IsPrime] (hη : η ∈ minimalPrimes A) :
    IsRegularLocalRing (Localization.AtPrime η) := by
  have : Ring.KrullDimLE 0 (Localization.AtPrime η) := Ring.KrullDimLE.of_isLocalization η hη _
  have hf : IsField (Localization.AtPrime η) := Ring.KrullDimLE.isField_of_isReduced
  let := hf.toField
  infer_instance

/-- Class 𝔅 (ii) and reducedness: for `S ∈ 𝔅` and a reduced `S`-algebra `A` of finite type, `A ⊗_S Ŝ` is reduced.
Its localizations over the minimal primes of `A` (fields) are regular by (ii), hence domains; flatness of `Ŝ` and
`isReduced_of_flat_of_isReduced_localization_minimalPrimes` do the rest. -/
theorem isReduced_tensor_adicCompletion {S : Type u} [CommRing S] [IsLocalRing S] [IsHironakaBase S]
    (A : Type u) [CommRing A] [Algebra S A] [Algebra.FiniteType S A] [_root_.IsReduced A] :
    _root_.IsReduced (A ⊗[S] AdicCompletion (maximalIdeal S) S) := by
  have : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing S A
  have : IsNoetherianRing (AdicCompletion (maximalIdeal S) S) :=
    isNoetherianRing_adicCompletion_of_isNoetherianRing (maximalIdeal S)
  have : IsNoetherianRing (AdicCompletion (maximalIdeal S) S ⊗[S] A) :=
    Algebra.FiniteType.isNoetherianRing (AdicCompletion (maximalIdeal S) S) _
  have : IsNoetherianRing (A ⊗[S] AdicCompletion (maximalIdeal S) S) :=
    isNoetherianRing_of_ringEquiv _ (Algebra.TensorProduct.comm S (AdicCompletion (maximalIdeal S) S) A).toRingEquiv
  have hfl : Module.Flat A (A ⊗[S] AdicCompletion (maximalIdeal S) S) := inferInstance
  refine isReduced_of_flat_of_isReduced_localization_minimalPrimes
    (φ := algebraMap A (A ⊗[S] AdicCompletion (maximalIdeal S) S)) ((RingHom.flat_algebraMap_iff).mpr hfl) ?_
  intro P hPprime hQ
  have hreg : (⟨P, hPprime⟩ : PrimeSpectrum (A ⊗[S] AdicCompletion (maximalIdeal S) S)) ∈
      regularLocus (A ⊗[S] AdicCompletion (maximalIdeal S) S) :=
    (IsHironakaBase.completion_singularLocus A ⟨P, hPprime⟩).mpr
      (isRegularLocalRing_localization_of_mem_minimalPrimes _ hQ)
  have hreg' : IsRegularLocalRing (Localization.AtPrime P) := hreg
  have hdom : IsDomain (Localization.AtPrime P) := Transforms.isDomain_of_isRegularLocalRing (Localization.AtPrime P)
  infer_instance



/-! ### Reducedness along the completion (class 𝔅 (ii)) -/

section ReducedPullback

/-- `Spec` form: for `A` reduced of finite type over `S ∈ 𝔅` and `W = Spec A ×_{Spec S} Spec Ŝ`, the scheme `W` is
reduced (`A ⊗_S Ŝ` is reduced, `isReduced_tensor_adicCompletion`). -/
theorem isReduced_of_isPullback_spec {S : Type u} [CommRing S] [IsLocalRing S] [IsHironakaBase S]
    {A : Type u} [CommRing A] [Algebra S A] [Algebra.FiniteType S A] [_root_.IsReduced A]
    {W : Scheme.{u}} (ψ : W ⟶ Spec (CommRingCat.of A))
    (ĝ : W ⟶ Spec (CommRingCat.of (AdicCompletion (IsLocalRing.maximalIdeal S) S)))
    (H : IsPullback ψ ĝ (Spec.map (CommRingCat.ofHom (algebraMap S A)))
      (Spec.map (CommRingCat.ofHom (algebraMap S (AdicCompletion (IsLocalRing.maximalIdeal S) S))))) :
    AlgebraicGeometry.IsReduced W := by
  let e : W ≅ Spec (CommRingCat.of (A ⊗[S] AdicCompletion (IsLocalRing.maximalIdeal S) S)) :=
    H.isoPullback ≪≫ pullbackSpecIso S A (AdicCompletion (IsLocalRing.maximalIdeal S) S)
  have : _root_.IsReduced (A ⊗[S] AdicCompletion (IsLocalRing.maximalIdeal S) S) :=
    isReduced_tensor_adicCompletion A
  have : AlgebraicGeometry.IsReduced
      (Spec (CommRingCat.of (A ⊗[S] AdicCompletion (IsLocalRing.maximalIdeal S) S))) := inferInstance
  exact isReduced_of_isOpenImmersion e.hom

/-- Chart form: the pull-back `cS : Y → P` of `Spec Ŝ → Spec S` along a morphism `gS : P → Spec S` which is locally of
finite type, `S ∈ 𝔅`, `P` reduced: `Y` is reduced (reduction to an affine chart of `P`, as in
`isRegularLocalRing_stalk_of_isPullback_of_locallyOfFiniteType`). -/
theorem isReduced_of_isPullback_of_locallyOfFiniteType {S : Type u} [CommRing S]
    [IsLocalRing S] [IsHironakaBase S] {P Y : Scheme.{u}} [AlgebraicGeometry.IsReduced P]
    (gS : P ⟶ Spec (CommRingCat.of S)) [LocallyOfFiniteType gS] (cS : Y ⟶ P)
    (ĝ : Y ⟶ Spec (CommRingCat.of (AdicCompletion (IsLocalRing.maximalIdeal S) S)))
    (H : IsPullback cS ĝ gS
      (Spec.map (CommRingCat.ofHom (algebraMap S (AdicCompletion (IsLocalRing.maximalIdeal S) S))))) :
    AlgebraicGeometry.IsReduced Y := by
  have hst : ∀ y : Y, _root_.IsReduced (Y.presheaf.stalk y) := by
    intro y
    obtain ⟨W, hW, hyW, -⟩ := exists_isAffineOpen_mem_and_subset
      (U := ⊤) (x := cS y) (by simp)
    have : IsAffine (W : Scheme) := hW
    let y' : ((cS ⁻¹ᵁ W : Y.Opens) : Scheme.{u}) := ⟨y, hyW⟩
    have hsq := (isPullback_morphismRestrict cS W)
    have Hpb : IsPullback (cS ∣_ W) ((cS ⁻¹ᵁ W).ι ≫ ĝ) (W.ι ≫ gS) _ :=
      (hsq.flip.paste_horiz H.flip).flip
    let ν : (W : Scheme) ≅ Spec Γ((W : Scheme), ⊤) := Scheme.isoSpec (W : Scheme)
    obtain ⟨φ, hφ⟩ := Spec.map_surjective (ν.inv ≫ W.ι ≫ gS)
    have HpbS : IsPullback (cS ∣_ W ≫ ν.hom) ((cS ⁻¹ᵁ W).ι ≫ ĝ) (Spec.map φ)
        (Spec.map (CommRingCat.ofHom
          (algebraMap S (AdicCompletion (IsLocalRing.maximalIdeal S) S)))) := by
      refine Hpb.of_iso (Iso.refl _) ν (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
      · simp
      · simp
      · simp [hφ]
      · simp
    let inst : Algebra S Γ((W : Scheme), ⊤) := φ.hom.toAlgebra
    have hft : Algebra.FiniteType S Γ((W : Scheme), ⊤) := by
      have : LocallyOfFiniteType (Spec.map φ) := by
        rw [hφ]; infer_instance
      exact (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mp this
    have hred : _root_.IsReduced Γ((W : Scheme), ⊤) := inferInstance
    have hU : AlgebraicGeometry.IsReduced ((cS ⁻¹ᵁ W : Y.Opens) : Scheme.{u}) :=
      @isReduced_of_isPullback_spec S _ _ _ Γ((W : Scheme), ⊤) _ inst hft hred
        _ (cS ∣_ W ≫ ν.hom) _ HpbS
    have hst' := isReduced_stalk_of_isReduced (X := ((cS ⁻¹ᵁ W : Y.Opens) : Scheme.{u})) y'
    exact isReduced_of_injective
      (asIso ((cS ⁻¹ᵁ W).ι.stalkMap y')).commRingCatIsoToRingEquiv.toRingHom
      (asIso ((cS ⁻¹ᵁ W).ι.stalkMap y')).commRingCatIsoToRingEquiv.injective
  exact @isReduced_of_isReduced_stalk Y hst

/-- **Reducedness along the completion (class 𝔅, (ii))**: let `S = O_{X,x₀} ∈ 𝔅`, `g : Y → X` locally of finite type
with `Y` reduced, and `c : Ŷ → Y`, `ĝ : Ŷ → Spec Ŝ` the pull-back of `g` along `Spec Ŝ → Spec S → X`.  Then `Ŷ` is
reduced.  (Companion of `isRegularLocalRing_stalk_of_isPullback_completion`.) -/
theorem isReduced_of_isPullback_completion {X Y Ŷ : Scheme.{u}} (x₀ : X)
    [IsHironakaBase (X.presheaf.stalk x₀)] (g : Y ⟶ X) [LocallyOfFiniteType g]
    [AlgebraicGeometry.IsReduced Y] (c : Ŷ ⟶ Y)
    (ĝ : Ŷ ⟶ Spec (CommRingCat.of (AdicCompletion (IsLocalRing.maximalIdeal (X.presheaf.stalk x₀))
      (X.presheaf.stalk x₀))))
    (H : IsPullback c ĝ g (Spec.map (CommRingCat.ofHom (algebraMap (X.presheaf.stalk x₀)
      (AdicCompletion (IsLocalRing.maximalIdeal (X.presheaf.stalk x₀))
        (X.presheaf.stalk x₀)))) ≫ X.fromSpecStalk x₀)) :
    AlgebraicGeometry.IsReduced Ŷ := by
  obtain ⟨P, π, gS, cS, H1, hc, H2⟩ := exists_factorization_isPullback x₀ g c ĝ _ H
  subst hc
  have hflat : Flat π := MorphismProperty.of_isPullback H1.flip (flat_fromSpecStalk X x₀)
  have hpre : IsPreimmersion π := MorphismProperty.of_isPullback (P := @IsPreimmersion) H1.flip
    inferInstance
  have hfin : LocallyOfFiniteType gS :=
    MorphismProperty.of_isPullback (P := @LocallyOfFiniteType) H1 inferInstance
  have hPred : AlgebraicGeometry.IsReduced P := by
    have : ∀ p : P, _root_.IsReduced (P.presheaf.stalk p) := by
      intro p
      have hiso := isIso_stalkMap_of_flat_of_isPreimmersion π p
      have := isReduced_stalk_of_isReduced (X := Y) (π p)
      exact isReduced_of_injective
        (asIso (π.stalkMap p)).commRingCatIsoToRingEquiv.symm.toRingHom
        (asIso (π.stalkMap p)).commRingCatIsoToRingEquiv.symm.injective
    exact @isReduced_of_isReduced_stalk P this
  have hloc : IsLocalRing (X.presheaf.stalk x₀) := inferInstance
  exact @isReduced_of_isPullback_of_locallyOfFiniteType
    (X.presheaf.stalk x₀) _ hloc _ P Ŷ hPred gS hfin cS ĝ H2

end ReducedPullback


section Completion

variable {X Y Ŷ : Scheme.{u}} [IsAlgebraicScheme X] (x : X) (g : Y ⟶ X) [LocallyOfFiniteType g]
  (c : Ŷ ⟶ Y) (ĝ : Ŷ ⟶ AB.xHat0 X x) (H : IsPullback c ĝ g (AB.c0 X x))

include H

omit [LocallyOfFiniteType g] in
/-- `c : Ŷ ⟶ Y` is flat: it is the base change of the flat `c_0 = AB.c0 X x`. -/
theorem flat_of_isPullback_completion : Flat c :=
  MorphismProperty.of_isPullback H.flip inferInstance

/-- `Y` and `Ŷ` are locally noetherian (`g` and `ĝ` are locally of finite type, `X` and `X̂_0` are algebraic). -/
theorem isLocallyNoetherian_of_isPullback_completion [Hironaka.HironakaCitedResults.{u}] :
    IsLocallyNoetherian Y ∧ IsLocallyNoetherian Ŷ := by
  have hX : IsLocallyNoetherian X := (IsAlgebraicScheme.isNoetherian X).toIsLocallyNoetherian
  have hX0 : IsLocallyNoetherian (AB.xHat0 X x) := by
    have := AB.isAlgebraicScheme_xHat0 X x
    exact (IsAlgebraicScheme.isNoetherian _).toIsLocallyNoetherian
  have hĝ : LocallyOfFiniteType ĝ := MorphismProperty.of_isPullback H ‹LocallyOfFiniteType g›
  exact ⟨LocallyOfFiniteType.isLocallyNoetherian g, LocallyOfFiniteType.isLocallyNoetherian ĝ⟩

/-- p. 175: "in view of the property (ii) of the class 𝔅": simple points of `Ŵ = c⁻¹(W)` lie exactly over the
simple points of `W`. -/
theorem Subscheme.isSimpleAt_totalTransform_iff_of_isPullback_completion [Hironaka.HironakaCitedResults.{u}] (W : Subscheme Y) (ŷ : Ŷ) :
    (Subscheme.totalTransform c W).IsSimpleAt ŷ ↔ W.IsSimpleAt (c.base ŷ) := by
  have hflat : Flat c := flat_of_isPullback_completion x g c ĝ H
  obtain ⟨hY, hŶ⟩ := isLocallyNoetherian_of_isPullback_completion x g c ĝ H
  have := isHironakaBase_stalk X x
  constructor
  · rintro ⟨hŷ, hreg⟩
    have hy : c ŷ ∈ W.pts := by rw [FlatPreimm.pts_totalTransform] at hŷ; exact hŷ
    refine ⟨hy, ?_⟩
    obtain ⟨w, hw⟩ := Subscheme.exists_ι_eq_of_mem_pts (Subscheme.totalTransform c W) hŷ
    let cW : (Subscheme.totalTransform c W).toScheme ⟶ W.toScheme :=
      Scheme.IdealSheafData.subschemeMap (W.comap c) W c (W.le_map_comap c)
    have hsq : (Subscheme.totalTransform c W).ι ≫ c = cW ≫ W.ι :=
      (Scheme.IdealSheafData.subschemeMap_subschemeι (W.comap c) W c (W.le_map_comap c)).symm
    have hP : IsPullback (Subscheme.totalTransform c W).ι cW c W.ι := by
      refine isPullback_of_isClosedImmersion _ _ _ _ hsq ?_
      show W.subschemeι.ker.comap c = (W.comap c).subschemeι.ker
      rw [Scheme.IdealSheafData.ker_subschemeι, Scheme.IdealSheafData.ker_subschemeι]
    have hcW : Flat cW := MorphismProperty.of_isPullback hP inferInstance
    have hy' : W.ι (cW w) = c ŷ := by
      rw [← hw, ← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, hsq]
    have hregŴ : IsRegularLocalRing ((Subscheme.totalTransform c W).toScheme.presheaf.stalk w) :=
      (isRegularLocalRing_quotient_stalk_iff _ w hw).mp hreg
    have hflatW : (cW.stalkMap w).hom.Flat := Flat.stalkMap cW w
    have : IsLocallyNoetherian W.toScheme := LocallyOfFiniteType.isLocallyNoetherian W.ι
    have : IsLocallyNoetherian (Subscheme.totalTransform c W).toScheme :=
      LocallyOfFiniteType.isLocallyNoetherian (Subscheme.totalTransform c W).ι
    let : Algebra (W.toScheme.presheaf.stalk (cW w))
        ((Subscheme.totalTransform c W).toScheme.presheaf.stalk w) := (cW.stalkMap w).hom.toAlgebra
    have : Module.Flat (W.toScheme.presheaf.stalk (cW w))
        ((Subscheme.totalTransform c W).toScheme.presheaf.stalk w) := hflatW
    have : IsLocalHom (algebraMap (W.toScheme.presheaf.stalk (cW w))
        ((Subscheme.totalTransform c W).toScheme.presheaf.stalk w)) := by
      show IsLocalHom (cW.stalkMap w).hom
      infer_instance
    have hregW := isRegularLocalRing_of_flat_of_isRegularLocalRing
      (R := W.toScheme.presheaf.stalk (cW w))
      (R' := (Subscheme.totalTransform c W).toScheme.presheaf.stalk w)
    exact (isRegularLocalRing_quotient_stalk_iff W (cW w) hy').mpr hregW
  · rintro ⟨hy, hreg⟩
    refine ⟨?_, isRegularLocalRing_quotient_stalk_totalTransform_of_isPullback_completion x g c ĝ
      H W ŷ hreg⟩
    rw [FlatPreimm.pts_totalTransform]
    exact hy

/-- Normal flatness along the completion square, both directions: `V̂ = c⁻¹(V)` is normally flat along `Ŵ = c⁻¹(W)` at
`ŷ` iff `V` is normally flat along `W` at `c ŷ` (flat base change one way, faithful flatness of the local maps the
other). -/
theorem Subscheme.isNormallyFlatAlongAt'_totalTransform_iff_of_isPullback_completion [Hironaka.HironakaCitedResults.{u}]
    (V W : Subscheme Y) (hWV : W.IsContainedIn V) (ŷ : Ŷ) :
    Subscheme.IsNormallyFlatAlongAt' (Subscheme.totalTransform c V) (Subscheme.totalTransform c W) ŷ ↔
      Subscheme.IsNormallyFlatAlongAt' V W (c.base ŷ) := by
  have hflat : Flat c := flat_of_isPullback_completion x g c ĝ H
  obtain ⟨hY, hŶ⟩ := isLocallyNoetherian_of_isPullback_completion x g c ĝ H
  have hWV' : (Subscheme.totalTransform c W).IsContainedIn (Subscheme.totalTransform c V) :=
    fun U => FlatPreimm.totalTransform_mono c (fun U => hWV U) U
  rw [Subscheme.isNormallyFlatAlongAt'_iff _ _ hWV, Subscheme.isNormallyFlatAlongAt'_iff _ _ hWV',
    FlatPreimm.pts_totalTransform]
  have hc : ∀ D : Subscheme Y, (Subscheme.totalTransform c D).stalkIdeal ŷ =
      (D.stalkIdeal (c.base ŷ)).map (c.stalkMap ŷ).hom := fun D => stalkIdeal_totalTransform c D ŷ
  rw [hc V, hc W]
  have hflat' : (c.stalkMap ŷ).hom.Flat := Flat.stalkMap c ŷ
  let : Algebra (Y.presheaf.stalk (c.base ŷ)) (Ŷ.presheaf.stalk ŷ) := (c.stalkMap ŷ).hom.toAlgebra
  have : Module.Flat (Y.presheaf.stalk (c.base ŷ)) (Ŷ.presheaf.stalk ŷ) := hflat'
  have : IsLocalHom (algebraMap (Y.presheaf.stalk (c.base ŷ)) (Ŷ.presheaf.stalk ŷ)) := by
    show IsLocalHom (c.stalkMap ŷ).hom
    infer_instance
  have : Module.FaithfullyFlat (Y.presheaf.stalk (c.base ŷ)) (Ŷ.presheaf.stalk ŷ) :=
    Module.FaithfullyFlat.of_flat_of_isLocalHom
  have hJP : V.stalkIdeal (c.base ŷ) ≤ W.stalkIdeal (c.base ŷ) :=
    Subscheme.stalkIdeal_mono (show V ≤ W from fun U => hWV U) (c.base ŷ)
  constructor
  · rintro ⟨hy, h⟩
    have hP : W.stalkIdeal (c.base ŷ) ≠ ⊤ := Subscheme.mem_pts_iff_stalkIdeal_ne_top.mp hy
    exact ⟨hy, (isNormallyFlatAlongIdeal_map_iff (R := Y.presheaf.stalk (c.base ŷ))
      (R' := Ŷ.presheaf.stalk ŷ) _ _ hJP hP).mpr h⟩
  · rintro ⟨hy, h⟩
    have hP : W.stalkIdeal (c.base ŷ) ≠ ⊤ := Subscheme.mem_pts_iff_stalkIdeal_ne_top.mp hy
    exact ⟨hy, (isNormallyFlatAlongIdeal_map_iff (R := Y.presheaf.stalk (c.base ŷ))
      (R' := Ŷ.presheaf.stalk ŷ) _ _ hJP hP).mp h⟩

/-- The resolved points (simple points of `W` at which all the `V_j` are normally flat along `W`) of the
pull-backs lie exactly over those of `V`, `W`. -/
theorem Subscheme.isMainResolvedAt_totalTransform_iff_of_isPullback_completion [Hironaka.HironakaCitedResults.{u}] {β : ℕ}
    (V : Fin (β + 1) → Subscheme Y) (W : Subscheme Y) (hWV : ∀ j, W.IsContainedIn (V j)) (ŷ : Ŷ) :
    Subscheme.IsMainResolvedAt (fun j => Subscheme.totalTransform c (V j))
        (Subscheme.totalTransform c W) ŷ ↔
      Subscheme.IsMainResolvedAt V W (c.base ŷ) := by
  unfold Subscheme.IsMainResolvedAt
  exact and_congr (Subscheme.isSimpleAt_totalTransform_iff_of_isPullback_completion x g c ĝ H W ŷ)
    (forall_congr' fun j => Subscheme.isNormallyFlatAlongAt'_totalTransform_iff_of_isPullback_completion
      x g c ĝ H (V j) W (hWV j) ŷ)

/-- p. 175: "`Ŝ(r) = c_r⁻¹(S(r))`".  `S(r)` is `mainUnresolved` of the strict transforms; the `V̂_j(r)` are the
total transforms `c_r⁻¹(V_j(r))`; `V̂_0(r) = ⊥` pulls back to `⊥`. -/
theorem Subscheme.mainUnresolved_totalTransform_of_isPullback_completion [Hironaka.HironakaCitedResults.{u}] {β : ℕ}
    (V : Fin (β + 1) → Subscheme Y) (W : Subscheme Y) (hWV : ∀ j, W.IsContainedIn (V j)) :
    Subscheme.mainUnresolved (fun j => Subscheme.totalTransform c (V j)) (Subscheme.totalTransform c W) =
      c.base ⁻¹' Subscheme.mainUnresolved V W := by
  ext ŷ
  have hpts : ŷ ∈ (Subscheme.totalTransform c W).pts ↔ c.base ŷ ∈ W.pts := by
    rw [FlatPreimm.pts_totalTransform]; rfl
  unfold Subscheme.mainUnresolved
  simp only [Set.mem_ofPred_eq, Set.mem_preimage]
  exact and_congr hpts (not_congr
    (Subscheme.isMainResolvedAt_totalTransform_iff_of_isPullback_completion x g c ĝ H V W hWV ŷ))

/-- The paper uses silently that `Ŵ(r)` is a reduced subscheme (it applies "the previous result", whose `W` is
reduced, to `Ŵ(r)`): the pull-back of a reduced subscheme along the completion square is reduced.  From class 𝔅
(ii) and flatness: the minimal primes of `A` embed `A ⊗ Ŝ ↪ ∏ (A/p_i) ⊗ Ŝ`; for a domain `A`, `A ⊗ Ŝ ↪ K ⊗ Ŝ`
whose local rings lie over the generic point, regular by (ii). -/
theorem Subscheme.isReduced_totalTransform_of_isPullback_completion [Hironaka.HironakaCitedResults.{u}] (W : Subscheme Y) (hW : W.IsReduced) :
    (Subscheme.totalTransform c W).IsReduced := by
  have := isHironakaBase_stalk X x
  have hW' : AlgebraicGeometry.IsReduced W.toScheme := hW
  let cW : (Subscheme.totalTransform c W).toScheme ⟶ W.toScheme :=
    Scheme.IdealSheafData.subschemeMap (W.comap c) W c (W.le_map_comap c)
  have hsq : (Subscheme.totalTransform c W).ι ≫ c = cW ≫ W.ι :=
    (Scheme.IdealSheafData.subschemeMap_subschemeι (W.comap c) W c (W.le_map_comap c)).symm
  have hP : IsPullback (Subscheme.totalTransform c W).ι cW c W.ι := by
    refine isPullback_of_isClosedImmersion _ _ _ _ hsq ?_
    show W.subschemeι.ker.comap c = (W.comap c).subschemeι.ker
    rw [Scheme.IdealSheafData.ker_subschemeι, Scheme.IdealSheafData.ker_subschemeι]
  have Hpb := (hP.paste_horiz H.flip).flip
  have : LocallyOfFiniteType (W.ι ≫ g) := inferInstance
  exact isReduced_of_isPullback_completion x (W.ι ≫ g) cW
    ((Subscheme.totalTransform c W).ι ≫ ĝ) Hpb

/-- The pull-back of a non-singular subscheme along the completion square is non-singular (class 𝔅 (ii),
`isRegularLocalRing_quotient_stalk_totalTransform_of_isPullback_completion`): (1̂) for `B̂ = c⁻¹(B)`. -/
theorem Subscheme.isNonsingular_totalTransform_of_isPullback_completion [Hironaka.HironakaCitedResults.{u}] (D : Subscheme Y)
    (hD : D.IsNonsingular) : (Subscheme.totalTransform c D).IsNonsingular := by
  have := isHironakaBase_stalk X x
  refine Subscheme.isNonsingular_of_stalk_quot _ fun ŷ hŷ => ?_
  have hy : c.base ŷ ∈ D.pts := by rw [FlatPreimm.pts_totalTransform] at hŷ; exact hŷ
  exact isRegularLocalRing_quotient_stalk_totalTransform_of_isPullback_completion x g c ĝ H D ŷ
    (Subscheme.isRegular_stalk_quot D hD hy)

end Completion

namespace MonoidalSuccession

/-- The strict transform of a reduced subscheme by a succession is reduced, for an arbitrary ambient scheme (no
algebraicity hypothesis): induction on the length via `MonoidalTransformation.isReduced_strictTransform_of_isReduced`. -/
theorem isReduced_strictTransform_of_isReduced {X Y : Scheme.{u}} (s : MonoidalSuccession X Y) :
    ∀ V : Subscheme X, V.IsReduced → (s.strictTransform V).IsReduced := by
  induction s with
  | nil X => intro V hV; exact hV
  | cons B t rest ih =>
    intro V hV
    exact ih _ (MonoidalTransformation.isReduced_strictTransform_of_isReduced t V hV)

/-- The conditions (1̂), (2), (3) for the base change of a succession along a flat morphism `c` which sits in a
completion square `Z = X ×_{X₀} Spec(Ô_{X₀,x})` over a morphism `g : X ⟶ X₀` locally of finite type: the square is
pasted along the pull-back square of each stage, so the induction runs over successions of an arbitrary algebraic
scheme over `X₀` (p. 175: "`c_i` is the base change of `c_0`"). -/
theorem isMain123Hat_baseChangeSucc_of_isPullback [Hironaka.HironakaCitedResults.{u}] {X₀ X Y Z : Scheme.{u}} [IsAlgebraicScheme X₀] (x : X₀)
    (s : MonoidalSuccession X Y) (g : X ⟶ X₀) [LocallyOfFiniteType g] (c : Z ⟶ X) [Flat c]
    (ĝ : Z ⟶ AB.xHat0 X₀ x) (H : IsPullback c ĝ g (AB.c0 X₀ x)) {β : ℕ}
    (V : Fin (β + 1) → Subscheme X) (W : Subscheme X) (hWV : ∀ j, W.IsContainedIn (V j))
    (hs : s.IsMain123 V W) :
    (s.baseChangeSucc c).IsMain123Hat (fun j => Subscheme.totalTransform c (V j))
      (Subscheme.totalTransform c W) := by
  induction s generalizing Z with
  | nil X => trivial
  | @cons X B t Y rest ih =>
    obtain ⟨⟨⟨hB, hBW⟩, h2, h3⟩, hrest⟩ := hs
    have hX₀ : IsLocallyNoetherian X₀ := (IsAlgebraicScheme.isNoetherian X₀).toIsLocallyNoetherian
    have hXn : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian g
    have : IsProper t.f := t.isProper
    have : LocallyOfFiniteType (t.f ≫ g) := inferInstance
    have hfl : Flat (pullback.fst t.f c) := inferInstance
    have hBns : B.IsNonsingular := by
      rcases hB with h | ⟨hns, -⟩
      · rw [h]; exact Subscheme.isNonsingular_empty
      · exact hns
    have hBV : ∀ j, B.IsContainedIn (V j) := fun j => hBW.trans (hWV j)
    have hWV' : ∀ j, (Subscheme.strictTransform t W).IsContainedIn
        (Subscheme.strictTransform t (V j)) := fun j =>
      MonoidalTransformation.isContainedIn_strictTransform t (hWV j)
    have H' := (IsPullback.of_hasPullback t.f c).paste_vert H
    have key := ih (t.f ≫ g) (pullback.fst t.f c) (pullback.snd t.f c ≫ ĝ) H' _ _ hWV' hrest
    have e1 : ∀ j, Subscheme.strictTransform (t.baseChange c) (Subscheme.totalTransform c (V j)) =
        Subscheme.totalTransform (pullback.fst t.f c) (Subscheme.strictTransform t (V j)) := fun j =>
      (@MonoidalTransformation.totalTransform_strictTransform_of_flat_square _ _ _ t _ (t.baseChange c) c
        (pullback.fst t.f c) hfl pullback.condition rfl (V j)).symm
    have e2 : Subscheme.strictTransform (t.baseChange c) (Subscheme.totalTransform c W) =
        Subscheme.totalTransform (pullback.fst t.f c) (Subscheme.strictTransform t W) :=
      (@MonoidalTransformation.totalTransform_strictTransform_of_flat_square _ _ _ t _ (t.baseChange c) c
        (pullback.fst t.f c) hfl pullback.condition rfl W).symm
    refine ⟨⟨⟨?_, ?_⟩, ?_, ?_⟩, ?_⟩
    · exact Subscheme.isNonsingular_totalTransform_of_isPullback_completion x g c ĝ H B hBns
    · exact fun U => FlatPreimm.totalTransform_mono c (fun U => hBW U) U
    · intro y hy hres
      rw [FlatPreimm.pts_totalTransform] at hy
      exact h2 (c.base y) hy
        ((Subscheme.isMainResolvedAt_totalTransform_iff_of_isPullback_completion x g c ĝ H V W hWV y).mp
          hres)
    · intro y hy
      rw [FlatPreimm.pts_totalTransform] at hy
      obtain ⟨h3a, h3b⟩ := h3 (c.base y) hy
      refine ⟨fun j => ?_, ?_⟩
      · exact (Subscheme.isNormallyFlatAlongAt'_totalTransform_iff_of_isPullback_completion x g c ĝ H
          (V j) B (hBV j) y).mpr (h3a j)
      · exact (Subscheme.isNormallyFlatAlongAt'_totalTransform_iff_of_isPullback_completion x g c ĝ H
          W B hBW y).mpr h3b
    · show (rest.baseChangeSucc (pullback.fst t.f c)).IsMain123Hat
        (fun j => Subscheme.strictTransform (t.baseChange c) (Subscheme.totalTransform c (V j)))
        (Subscheme.strictTransform (t.baseChange c) (Subscheme.totalTransform c W))
      simp only [e1, e2]
      exact key

variable {X Y : Scheme.{u}} [IsAlgebraicScheme X] (x : X) (s : MonoidalSuccession X Y)

/-- p. 175: "`Ŝ(r) = c_r⁻¹(S(r))`" for the base change of a succession: with `ĉ = baseChangeMap` and the data
`V̂_j = c⁻¹(V_j)`, `Ŵ = c⁻¹(W)` transformed by `{f̂_i}`. -/
theorem mainUnresolvedAt_baseChangeSucc [Hironaka.HironakaCitedResults.{u}] {β : ℕ} (V : Fin (β + 1) → Subscheme X) (W : Subscheme X)
    (hWV : ∀ j, W.IsContainedIn (V j)) :
    (s.baseChangeSucc (AB.c0 X x)).mainUnresolvedAt (fun j => Subscheme.totalTransform (AB.c0 X x) (V j))
        (Subscheme.totalTransform (AB.c0 X x) W) =
      (s.baseChangeMap (AB.c0 X x)).base ⁻¹' s.mainUnresolvedAt V W := by
  have hX : IsLocallyNoetherian X := (IsAlgebraicScheme.isNoetherian X).toIsLocallyNoetherian
  have : IsProper s.composite := s.isProper_composite
  have hWV' : ∀ j, (s.strictTransform W).IsContainedIn (s.strictTransform (V j)) := fun j =>
    s.isContainedIn_strictTransform (hWV j)
  unfold mainUnresolvedAt
  simp only [strictTransform_baseChangeSucc]
  exact Subscheme.mainUnresolved_totalTransform_of_isPullback_completion x s.composite
    (s.baseChangeMap (AB.c0 X x)) (s.baseChangeSucc (AB.c0 X x)).composite
    (isPullback_baseChange s (AB.c0 X x)) _ _ hWV'

/-- p. 175: "Obviously, `B̂_i`, `Ŵ(i)` and the `V̂_j(i)` for all `j` satisfy the conditions (1), (2) and (3)" — in the
form (1̂): the `B̂_i = c_i⁻¹(B_i)` are non-singular (they need not be irreducible), contained in `Ŵ(i)`; (2), (3) as
printed.  And "any prolongation of the succession `{f_i}` satisfying (1), (2) and (3) induces the same kind of
prolongation of `{f̂_i}`" (apply this to the prolongation). -/
theorem isMain123Hat_baseChangeSucc [Hironaka.HironakaCitedResults.{u}] {β : ℕ} (V : Fin (β + 1) → Subscheme X) (W : Subscheme X)
    (hWV : ∀ j, W.IsContainedIn (V j)) (hs : s.IsMain123 V W) :
    (s.baseChangeSucc (AB.c0 X x)).IsMain123Hat (fun j => Subscheme.totalTransform (AB.c0 X x) (V j))
      (Subscheme.totalTransform (AB.c0 X x) W) :=
  isMain123Hat_baseChangeSucc_of_isPullback x s (𝟙 X) (AB.c0 X x) (𝟙 _) (IsPullback.id_vert _) V W hWV hs

/-- The end of `{f̂_i}`: the strict transforms of `V̂_j`, `Ŵ` are `ĉ⁻¹` of the strict transforms of `V_j`, `W`
(`strictTransform_baseChangeSucc`), and `Ŵ(r)` is reduced if `W` is. -/
theorem isReduced_strictTransform_baseChangeSucc [Hironaka.HironakaCitedResults.{u}] (W : Subscheme X) (hW : W.IsReduced) :
    ((s.baseChangeSucc (AB.c0 X x)).strictTransform (Subscheme.totalTransform (AB.c0 X x) W)).IsReduced := by
  have hX : IsLocallyNoetherian X := (IsAlgebraicScheme.isNoetherian X).toIsLocallyNoetherian
  have : IsProper s.composite := s.isProper_composite
  rw [strictTransform_baseChangeSucc]
  exact Subscheme.isReduced_totalTransform_of_isPullback_completion x s.composite
    (s.baseChangeMap (AB.c0 X x)) (s.baseChangeSucc (AB.c0 X x)).composite
    (isPullback_baseChange s (AB.c0 X x)) _ (isReduced_strictTransform_of_isReduced s W hW)

end MonoidalSuccession

end Hironaka
