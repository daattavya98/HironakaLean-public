/-
Copyright (c) 2026 Daattavya Aggarwal, Minhyong Kim, Oisin Kim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daattavya Aggarwal, Minhyong Kim, Oisin Kim
-/
module

public import Mathlib.Algebra.CharP.Algebra
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Architect
public import Hironaka.Compat.CompletionOrder
public import Hironaka.Compat.BlowupBaseChange

/-!
# Stalks of a pull-back along the completion 

The scheme-level bridge for `CompletionOrder`:
* `OrderDescends φ` (the statement `J R' ⊆ M'^k ⇒ J ⊆ M^k`) and `OrderDescends.of_arrow_iso`
  (transport along isomorphisms of arrows);
* `exists_factorization_isPullback`: a pull-back square along `Spec Ŝ → Spec S → X` factors
  through `P = X' ×_X Spec S`, `c = c_S ≫ π`, with `c_S` the pull-back of `Spec Ŝ → Spec S`.

* `IsHironakaBase.of_ringEquiv`, `isHironakaBase_stalk`: the class 𝔅 is invariant under ring
  isomorphisms, so the local rings `O_{X,x₀}` of an algebraic scheme belong to 𝔅;
* `orderDescends_stalkMap_iff_of_square`: invariance under commuting squares of schemes whose
  comparison maps are isomorphisms on stalks;
* `orderDescends_stalkMap_of_isPullback_spec`: the `Spec` form (via `pullbackSpecIso` and
  `Scheme.localRingHom_comp_stalkIso`), using
  `le_pow_maximalIdeal_of_map_le_pow_of_isHironakaBase`;
* `orderDescends_stalkMap_of_isPullback_of_locallyOfFiniteType`: reduction to an affine chart;
* `orderDescends_stalkMap_of_isPullback_completion`: the scheme-level bridge for (CD.5), p. 320.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory IsLocalRing

namespace Hironaka

universe u

section Transport

/-- The order statement `J R' ⊆ M'^k ⇒ J ⊆ M^k` for a local homomorphism. -/
def OrderDescends {R R' : Type u} [CommRing R] [IsLocalRing R] [CommRing R'] [IsLocalRing R']
    (φ : R →+* R') : Prop :=
  ∀ (J : Ideal R) (k : ℕ), J.map φ ≤ maximalIdeal R' ^ k → J ≤ maximalIdeal R ^ k

variable {R R' R₁ R₁' : Type u} [CommRing R] [IsLocalRing R] [CommRing R'] [IsLocalRing R']
  [CommRing R₁] [IsLocalRing R₁] [CommRing R₁'] [IsLocalRing R₁']

/-- The order statement is transported along isomorphisms of arrows. -/
theorem OrderDescends.of_arrow_iso {φ : R →+* R'} {φ' : R₁ →+* R₁'} (a : R ≃+* R₁)
    (b : R' ≃+* R₁') (hab : ∀ x, b (φ x) = φ' (a x)) (h : OrderDescends φ') :
    OrderDescends φ := by
  intro J k hJ
  have h1 : (J.map (a : R →+* R₁)).map φ' ≤ maximalIdeal R₁' ^ k := by
    rw [Ideal.map_map]
    have : φ'.comp (a : R →+* R₁) = (b : R' →+* R₁').comp φ := RingHom.ext fun x => (hab x).symm
    rw [this, ← Ideal.map_map]
    calc (J.map φ).map (b : R' →+* R₁') ≤ (maximalIdeal R' ^ k).map (b : R' →+* R₁') :=
          Ideal.map_mono hJ
      _ = maximalIdeal R₁' ^ k := by
          rw [Ideal.map_pow]
          congr 1
          exact map_ringEquiv_maximalIdeal b
  have h2 := h _ k h1
  have h3 : (J.map (a : R →+* R₁)).map (a.symm : R₁ →+* R) ≤
      (maximalIdeal R₁ ^ k).map (a.symm : R₁ →+* R) := Ideal.map_mono h2
  rw [Ideal.map_map, Ideal.map_pow] at h3
  have e1 : (a.symm : R₁ →+* R).comp (a : R →+* R₁) = RingHom.id R := by ext x; simp
  have e2 : Ideal.map (a.symm : R₁ →+* R) (maximalIdeal R₁) = maximalIdeal R :=
    map_ringEquiv_maximalIdeal a.symm
  rw [e1, Ideal.map_id, e2] at h3
  exact h3

end Transport


section Pullback

open CategoryTheory.Limits

variable {X X' Y Z : Scheme.{u}}

/-- **Reduction of a pull-back along `Spec Ŝ → Spec S → X` to the base `Spec S`**, `S = O_{X,x₀}`:
the square factors through `P = X' ×_X Spec S`, with `c = c_S ≫ π` and `c_S` the pull-back of
`Spec Ŝ → Spec S` along `P → Spec S`. -/
theorem exists_factorization_isPullback (x₀ : X) (g : X' ⟶ X) (c : Y ⟶ X') (ĝ : Y ⟶ Z)
    (ι' : Z ⟶ Spec (X.presheaf.stalk x₀)) (H : IsPullback c ĝ g (ι' ≫ X.fromSpecStalk x₀)) :
    ∃ (P : Scheme.{u}) (π : P ⟶ X') (gS : P ⟶ Spec (X.presheaf.stalk x₀)) (cS : Y ⟶ P),
      IsPullback π gS g (X.fromSpecStalk x₀) ∧ cS ≫ π = c ∧ IsPullback cS ĝ gS ι' := by
  have H1 : IsPullback (pullback.fst g (X.fromSpecStalk x₀)) (pullback.snd g (X.fromSpecStalk x₀))
      g (X.fromSpecStalk x₀) := IsPullback.of_hasPullback _ _
  have hw : c ≫ g = (ĝ ≫ ι') ≫ X.fromSpecStalk x₀ := by rw [Category.assoc]; exact H.w
  refine ⟨_, _, _, H1.lift c (ĝ ≫ ι') hw, H1, H1.lift_fst _ _ _, ?_⟩
  refine IsPullback.of_right (h₁₂ := pullback.fst g (X.fromSpecStalk x₀)) ?_ ?_ H1
  · rw [H1.lift_fst]; exact H
  · rw [H1.lift_snd]

end Pullback



section ClassB

open scoped TensorProduct

private theorem factorPow_evalₐ' {S : Type u} [CommRing S] (I : Ideal S) {m n : ℕ} (h : m ≤ n)
    (x : AdicCompletion I S) :
    Ideal.Quotient.factorPow I h (AdicCompletion.evalₐ I n x) = AdicCompletion.evalₐ I m x := by
  obtain ⟨c, rfl⟩ := AdicCompletion.mk_surjective I S x
  rw [AdicCompletion.evalₐ_mk, AdicCompletion.evalₐ_mk, Ideal.Quotient.factorPow,
    Ideal.Quotient.factor_mk, Ideal.Quotient.eq]
  have := AdicCompletion.AdicCauchySequence.mk_eq_mk h c
  rw [Submodule.Quotient.eq, smul_eq_mul, Ideal.mul_top] at this
  simpa using this

/-- Functoriality of the adic completion along a ring isomorphism, compatible with the canonical
maps. -/
theorem exists_adicCompletion_ringEquiv {S S' : Type u} [CommRing S] [CommRing S'] (e : S ≃+* S')
    (I : Ideal S) (J : Ideal S') (hIJ : J = I.map (e : S →+* S')) :
    ∃ ε : AdicCompletion I S ≃+* AdicCompletion J S', ∀ x : S,
      ε (algebraMap S (AdicCompletion I S) x) = algebraMap S' (AdicCompletion J S') (e x) := by
  have hn : ∀ n, J ^ n = (I ^ n).map (e : S →+* S') := fun n => by rw [hIJ, Ideal.map_pow]
  let q : ∀ n, S ⧸ I ^ n ≃+* S' ⧸ J ^ n := fun n => Ideal.quotientEquiv (I ^ n) (J ^ n) e (hn n)
  have hq : ∀ n a, q n (Ideal.Quotient.mk _ a) = Ideal.Quotient.mk _ (e a) := fun n a => rfl
  have hcomp : ∀ {m n : ℕ} (hmn : m ≤ n) (y : S ⧸ I ^ n),
      Ideal.Quotient.factorPow J hmn (q n y) = q m (Ideal.Quotient.factorPow I hmn y) := by
    intro m n hmn y
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective y
    simp only [hq, Ideal.Quotient.factorPow, Ideal.Quotient.factor_mk]
  let F : AdicCompletion I S →+* AdicCompletion J S' :=
    AdicCompletion.liftRingHom J (fun n => ((q n : S ⧸ I ^ n →+* S' ⧸ J ^ n)).comp
      (AdicCompletion.evalₐ I n : AdicCompletion I S →+* S ⧸ I ^ n)) (by
        intro m n hmn
        ext x
        simp only [RingHom.comp_apply, RingHom.coe_coe]
        rw [hcomp, factorPow_evalₐ'])
  let G : AdicCompletion J S' →+* AdicCompletion I S :=
    AdicCompletion.liftRingHom I (fun n => (((q n).symm : S' ⧸ J ^ n ≃+* S ⧸ I ^ n) :
      S' ⧸ J ^ n →+* S ⧸ I ^ n).comp
      (AdicCompletion.evalₐ J n : AdicCompletion J S' →+* S' ⧸ J ^ n)) (by
        intro m n hmn
        ext x
        simp only [RingHom.comp_apply, RingHom.coe_coe]
        rw [eq_comm, RingEquiv.symm_apply_eq, ← hcomp, RingEquiv.apply_symm_apply,
          factorPow_evalₐ'])
  refine ⟨RingEquiv.ofRingHom F G ?_ ?_, ?_⟩
  · refine RingHom.ext fun y => ?_
    refine AdicCompletion.ext_evalₐ fun n => ?_
    simp [F, G]
  · refine RingHom.ext fun y => ?_
    refine AdicCompletion.ext_evalₐ fun n => ?_
    simp [F, G]
  · intro x
    refine AdicCompletion.ext_evalₐ fun n => ?_
    show (AdicCompletion.evalₐ J n) (F _) = _
    simp [F, hq]


/-- Change of the base ring along a ring isomorphism `e : S ≃+* S'`: the tensor products
`A ⊗[S] B` and `A ⊗[S'] B'` are isomorphic (compatibly with `A`) when `A` and `B ≃ B'` are
compatible with `e`. -/
theorem exists_tensor_ringEquiv {S S' A B B' : Type u} [CommRing S] [CommRing S'] [CommRing A]
    [CommRing B] [CommRing B'] (e : S ≃+* S') [Algebra S A] [Algebra S' A]
    (hA : ∀ s, algebraMap S' A (e s) = algebraMap S A s) [Algebra S B] [Algebra S' B']
    (ε : B ≃+* B') (hε : ∀ s, ε (algebraMap S B s) = algebraMap S' B' (e s)) :
    ∃ Ψ : A ⊗[S] B ≃+* A ⊗[S'] B', ∀ a : A,
      Ψ (algebraMap A (A ⊗[S] B) a) = algebraMap A (A ⊗[S'] B') a := by
  have hA' : ∀ s', algebraMap S' A s' = algebraMap S A (e.symm s') := fun s' => by
    rw [← hA, RingEquiv.apply_symm_apply]
  let φ₁ : A →ₐ[S] A ⊗[S'] B' :=
    { Algebra.TensorProduct.includeLeftRingHom with
      commutes' := fun s => by
        show (algebraMap S A s) ⊗ₜ[S'] (1 : B') = _
        rfl }
  let φ₂ : B →ₐ[S] A ⊗[S'] B' :=
    { ((Algebra.TensorProduct.includeRight : B' →ₐ[S'] A ⊗[S'] B') : B' →+* _).comp
        (ε : B →+* B') with
      commutes' := fun s => by
        show (1 : A) ⊗ₜ[S'] ε (algebraMap S B s) = _
        rw [hε, Algebra.algebraMap_eq_smul_one, TensorProduct.tmul_smul,
          TensorProduct.smul_tmul', ← Algebra.algebraMap_eq_smul_one, hA s]
        rfl }
  let ψ₁ : A →ₐ[S'] A ⊗[S] B :=
    { Algebra.TensorProduct.includeLeftRingHom with
      commutes' := fun s' => by
        show (algebraMap S' A s') ⊗ₜ[S] (1 : B) = _
        rfl }
  let ψ₂ : B' →ₐ[S'] A ⊗[S] B :=
    { ((Algebra.TensorProduct.includeRight : B →ₐ[S] A ⊗[S] B) : B →+* _).comp
        (ε.symm : B' →+* B) with
      commutes' := fun s' => by
        show (1 : A) ⊗ₜ[S] ε.symm (algebraMap S' B' s') = _
        have : ε.symm (algebraMap S' B' s') = algebraMap S B (e.symm s') := by
          rw [RingEquiv.symm_apply_eq, hε, RingEquiv.apply_symm_apply]
        rw [this, Algebra.algebraMap_eq_smul_one, TensorProduct.tmul_smul,
          TensorProduct.smul_tmul', ← Algebra.algebraMap_eq_smul_one, ← hA' s']
        rfl }
  let F : A ⊗[S] B →ₐ[S] A ⊗[S'] B' :=
    Algebra.TensorProduct.lift φ₁ φ₂ (fun _ _ => Commute.all _ _)
  let G : A ⊗[S'] B' →ₐ[S'] A ⊗[S] B :=
    Algebra.TensorProduct.lift ψ₁ ψ₂ (fun _ _ => Commute.all _ _)
  have hF : ∀ a b, F (a ⊗ₜ b) = a ⊗ₜ ε b := fun a b => by
    simp [F, φ₁, φ₂, Algebra.TensorProduct.tmul_mul_tmul]
  have hG : ∀ a b, G (a ⊗ₜ b) = a ⊗ₜ ε.symm b := fun a b => by
    simp [G, ψ₁, ψ₂, Algebra.TensorProduct.tmul_mul_tmul]
  refine ⟨RingEquiv.ofRingHom (F : A ⊗[S] B →+* A ⊗[S'] B') (G : A ⊗[S'] B' →+* A ⊗[S] B)
    ?_ ?_, fun a => ?_⟩
  · refine RingHom.ext fun x => ?_
    induction x using TensorProduct.inductionOn with
    | tmul a b => simp [hF, hG]
    | add x y hx hy => simp only [map_add] at hx hy ⊢; rw [hx, hy]
  · refine RingHom.ext fun x => ?_
    induction x using TensorProduct.inductionOn with
    | tmul a b => simp [hF, hG]
    | add x y hx hy => simp only [map_add] at hx hy ⊢; rw [hx, hy]
  · show F (algebraMap A _ a) = _
    rw [Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.algebraMap_apply, hF]
    simp


/-- The regular locus is transported along ring isomorphisms. -/
theorem mem_regularLocus_comap_symm_iff {T T' : Type u} [CommRing T] [CommRing T']
    (Ψ : T ≃+* T') (q : PrimeSpectrum T) :
    PrimeSpectrum.comap (Ψ.symm : T' →+* T) q ∈ regularLocus T' ↔ q ∈ regularLocus T := by
  have H : q.asIdeal.primeCompl.map Ψ.toMonoidHom =
      (PrimeSpectrum.comap (Ψ.symm : T' →+* T) q).asIdeal.primeCompl := by
    ext x
    simp only [Submonoid.mem_map, Ideal.mem_primeCompl_iff, PrimeSpectrum.comap_asIdeal,
      Ideal.mem_comap]
    constructor
    · rintro ⟨y, hy, rfl⟩
      simpa using hy
    · intro hx
      exact ⟨Ψ.symm x, hx, by simp⟩
  let E := IsLocalization.ringEquivOfRingEquiv (Localization.AtPrime q.asIdeal)
    (Localization.AtPrime (PrimeSpectrum.comap (Ψ.symm : T' →+* T) q).asIdeal) Ψ H
  constructor
  · intro h
    have h' : IsRegularLocalRing (Localization.AtPrime
      (PrimeSpectrum.comap (Ψ.symm : T' →+* T) q).asIdeal) := h
    exact IsRegularLocalRing.of_ringEquiv E.symm
  · intro h
    have h' : IsRegularLocalRing (Localization.AtPrime q.asIdeal) := h
    exact IsRegularLocalRing.of_ringEquiv E

/-- The class 𝔅 is invariant under isomorphism of local rings. -/
theorem IsHironakaBase.of_ringEquiv {S S' : Type u} [CommRing S] [IsLocalRing S] [CommRing S']
    [IsLocalRing S'] [IsHironakaBase S'] (e : S ≃+* S') : IsHironakaBase S := by
  have hnoeth : IsNoetherianRing S := isNoetherianRing_of_ringEquiv S' e.symm
  have hloc : IsLocalHom (e : S →+* S') := inferInstance
  refine @IsHironakaBase.mk S _ _ ⟨hnoeth.noetherian⟩ ?_ ?_
  · have := IsHironakaBase.charZero_residueField (S := S')
    exact charZero_of_injective_ringHom (f := IsLocalRing.ResidueField.map (e.symm : S' →+* S))
      (RingHom.injective _)
  · intro A _ _ hfin q
    let _ : Algebra S' A := ((algebraMap S A).comp (e.symm : S' →+* S)).toAlgebra
    have hA : ∀ s, algebraMap S' A (e s) = algebraMap S A s := fun s => by
      simp [RingHom.algebraMap_toAlgebra]
    have hfin' : Algebra.FiniteType S' A := by
      have : (algebraMap S' A).FiniteType :=
        RingHom.FiniteType.comp (g := algebraMap S A) (RingHom.finiteType_algebraMap.mpr hfin)
          (RingHom.FiniteType.of_surjective _ e.symm.surjective)
      exact this
    have hmax : maximalIdeal S' = (maximalIdeal S).map (e : S →+* S') := by
      exact (map_ringEquiv_maximalIdeal e).symm
    obtain ⟨ε, hε⟩ := exists_adicCompletion_ringEquiv e (maximalIdeal S) (maximalIdeal S') hmax
    obtain ⟨Ψ, hΨ⟩ := exists_tensor_ringEquiv (A := A) e hA ε hε
    have key := IsHironakaBase.completion_singularLocus (S := S') A
      (PrimeSpectrum.comap (Ψ.symm : _ →+* _) q)
    rw [mem_regularLocus_comap_symm_iff] at key
    rw [key]
    have hcomap : PrimeSpectrum.comap (algebraMap A (A ⊗[S'] AdicCompletion (maximalIdeal S') S'))
        (PrimeSpectrum.comap (Ψ.symm : _ →+* _) q) =
        PrimeSpectrum.comap (algebraMap A (A ⊗[S] AdicCompletion (maximalIdeal S) S)) q := by
      refine PrimeSpectrum.ext (Ideal.ext fun a => ?_)
      simp only [PrimeSpectrum.comap_asIdeal, Ideal.mem_comap]
      rw [← hΨ a]
      simp
    rw [hcomap]

/-- For an algebraic scheme `X` and a point `x₀`, the local ring `O_{X,x₀}` belongs to the class
𝔅 (p. 161, (c): every local ring of a finite-type algebra over `S ∈ 𝔅` is in 𝔅). -/
theorem isHironakaBase_stalk [Hironaka.Cited.ExistsFlatIsLocalHomAdicCompletionOfFlat.{u}] [Hironaka.Cited.ExistsSurjectiveMvPowerSeriesOfIsAdicComplete.{u}] [Hironaka.Cited.IsRegularLocalRingLocalizationIffRankJacobianEqHeight.{u}] [Hironaka.Cited.IsRegularLocalRingLocalizationOfIsRegularLocalRing.{u}] [Hironaka.Cited.IsRegularLocalRingOfFlatOfIsRegularLocalRing.{u}] (X : Scheme.{u}) [IsAlgebraicScheme X] (x₀ : X) :
    IsHironakaBase (X.presheaf.stalk x₀) := by
  obtain ⟨S, i1, i2, i3, p, hp, -⟩ := IsAlgebraicScheme.exists_base (X := X)
  obtain ⟨_, ⟨U, hU₀, rfl⟩, hxU, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x₀) isOpen_univ
  have hU : IsAffineOpen U := hU₀
  let φ : S →+* Γ(X, U) :=
    (p.appLE ⊤ U le_top).hom.comp (Scheme.ΓSpecIso (CommRingCat.of S)).inv.hom
  let _ : Algebra S Γ(X, U) := φ.toAlgebra
  have hφ : φ.FiniteType := by
    refine RingHom.FiniteType.comp ?_ (RingHom.FiniteType.of_surjective _ ?_)
    · exact HasRingHomProperty.appLE @LocallyOfFiniteType p hp ⟨⊤, isAffineOpen_top _⟩ ⟨U, hU⟩
        le_top
    · exact (Scheme.ΓSpecIso (CommRingCat.of S)).commRingCatIsoToRingEquiv.symm.surjective
  have : Algebra.FiniteType S Γ(X, U) := hφ
  set q := hU.primeIdealOf ⟨x₀, hxU⟩
  have hB : IsHironakaBase (Localization.AtPrime q.asIdeal) :=
    IsHironakaBase.localization_atPrime_of_finiteType S Γ(X, U) q
  let _ := TopCat.Presheaf.algebra_section_stalk X.presheaf (U := U) ⟨x₀, hxU⟩
  have : IsLocalization q.asIdeal.primeCompl (X.presheaf.stalk x₀) :=
    hU.isLocalization_stalk ⟨x₀, hxU⟩
  let e : Localization.AtPrime q.asIdeal ≃+* X.presheaf.stalk x₀ :=
    (IsLocalization.algEquiv q.asIdeal.primeCompl _ _).toRingEquiv
  exact IsHironakaBase.of_ringEquiv e.symm

end ClassB

section Bridge

open CategoryTheory.Limits
open scoped TensorProduct

/-- The ring isomorphism between the stalks of the targets of a commuting square, when the
vertical comparison map `b` is an isomorphism on stalks. -/
noncomputable def stalkEquivOfSquare {X₁ X₂ Y₁ Y₂ : Scheme.{u}} (a : X₁ ⟶ X₂)
    (χ : X₂ ⟶ Y₂) (ψ : X₁ ⟶ Y₁) (b : Y₁ ⟶ Y₂) (w : a ≫ χ = ψ ≫ b) (x : X₁)
    [IsIso (b.stalkMap (ψ x))] :
    Y₂.presheaf.stalk (χ (a x)) ≃+* Y₁.presheaf.stalk (ψ x) :=
  (Y₂.presheaf.stalkCongr (.of_eq (by
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, w]))).commRingCatIsoToRingEquiv.trans
    (asIso (b.stalkMap (ψ x))).commRingCatIsoToRingEquiv

/-- Compatibility of `stalkEquivOfSquare` with the stalk maps. -/
theorem stalkMap_comp_stalkEquivOfSquare {X₁ X₂ Y₁ Y₂ : Scheme.{u}} (a : X₁ ⟶ X₂)
    (χ : X₂ ⟶ Y₂) (ψ : X₁ ⟶ Y₁) (b : Y₁ ⟶ Y₂) (w : a ≫ χ = ψ ≫ b) (x : X₁)
    [IsIso (a.stalkMap x)] [IsIso (b.stalkMap (ψ x))] (y : Y₂.presheaf.stalk (χ (a x))) :
    (asIso (a.stalkMap x)).commRingCatIsoToRingEquiv ((χ.stalkMap (a x)).hom y) =
      (ψ.stalkMap x).hom (stalkEquivOfSquare a χ ψ b w x y) := by
  have h1 := Scheme.Hom.stalkMap_congr_hom (a ≫ χ) (ψ ≫ b) w x
  rw [Scheme.Hom.stalkMap_comp, Scheme.Hom.stalkMap_comp] at h1
  have h2 := congrArg (fun f => f.hom y) h1
  exact h2

/-- The order statement for stalk maps is invariant under a commuting square whose horizontal
comparison maps are isomorphisms on stalks. -/
theorem orderDescends_stalkMap_iff_of_square {X₁ X₂ Y₁ Y₂ : Scheme.{u}} (a : X₁ ⟶ X₂)
    (χ : X₂ ⟶ Y₂) (ψ : X₁ ⟶ Y₁) (b : Y₁ ⟶ Y₂) (w : a ≫ χ = ψ ≫ b) (x : X₁)
    [IsIso (a.stalkMap x)] [IsIso (b.stalkMap (ψ x))] :
    OrderDescends (ψ.stalkMap x).hom ↔ OrderDescends (χ.stalkMap (a x)).hom := by
  have key := stalkMap_comp_stalkEquivOfSquare a χ ψ b w x
  constructor
  · intro h
    exact OrderDescends.of_arrow_iso (stalkEquivOfSquare a χ ψ b w x)
      (asIso (a.stalkMap x)).commRingCatIsoToRingEquiv key h
  · intro h
    refine OrderDescends.of_arrow_iso (stalkEquivOfSquare a χ ψ b w x).symm
      (asIso (a.stalkMap x)).commRingCatIsoToRingEquiv.symm ?_ h
    intro z
    apply (asIso (a.stalkMap x)).commRingCatIsoToRingEquiv.injective
    rw [RingEquiv.apply_symm_apply]
    have := key ((stalkEquivOfSquare a χ ψ b w x).symm z)
    simpa using this.symm

/-- Regularity of the stalks of the targets of a commuting square. -/
theorem isRegularLocalRing_stalk_iff_of_square {X₁ X₂ Y₁ Y₂ : Scheme.{u}} (a : X₁ ⟶ X₂)
    (χ : X₂ ⟶ Y₂) (ψ : X₁ ⟶ Y₁) (b : Y₁ ⟶ Y₂) (w : a ≫ χ = ψ ≫ b) (x : X₁)
    [IsIso (b.stalkMap (ψ x))] :
    IsRegularLocalRing (Y₂.presheaf.stalk (χ (a x))) ↔
      IsRegularLocalRing (Y₁.presheaf.stalk (ψ x)) :=
  ⟨fun _ => IsRegularLocalRing.of_ringEquiv (stalkEquivOfSquare a χ ψ b w x),
   fun _ => IsRegularLocalRing.of_ringEquiv (stalkEquivOfSquare a χ ψ b w x).symm⟩

/-- The ring-level bridge in `Spec` form: for `A` of finite type over `S ∈ 𝔅`, a scheme `Ŵ`
which is the pull-back of `Spec A → Spec S ← Spec Ŝ`, and a point `w` of `Ŵ` over a regular point
of `Spec A`, the order statement holds for the stalk map `O_{Spec A, ψ w} → O_{Ŵ, w}`. -/
theorem orderDescends_stalkMap_of_isPullback_spec {S : Type u} [CommRing S] [IsLocalRing S]
    [IsHironakaBase S] {A : Type u} [CommRing A] [Algebra S A] [Algebra.FiniteType S A]
    {W : Scheme.{u}} (ψ : W ⟶ Spec (CommRingCat.of A))
    (ĝ : W ⟶ Spec (CommRingCat.of (AdicCompletion (IsLocalRing.maximalIdeal S) S)))
    (H : IsPullback ψ ĝ (Spec.map (CommRingCat.ofHom (algebraMap S A)))
      (Spec.map (CommRingCat.ofHom (algebraMap S (AdicCompletion (IsLocalRing.maximalIdeal S) S)))))
    (w : W) [IsRegularLocalRing ((Spec (CommRingCat.of A)).presheaf.stalk (ψ w))] :
    OrderDescends (ψ.stalkMap w).hom := by
  let e : W ≅ Spec (CommRingCat.of (A ⊗[S] AdicCompletion (IsLocalRing.maximalIdeal S) S)) :=
    H.isoPullback ≪≫ pullbackSpecIso S A (AdicCompletion (IsLocalRing.maximalIdeal S) S)
  let f : CommRingCat.of A ⟶
      CommRingCat.of (A ⊗[S] AdicCompletion (IsLocalRing.maximalIdeal S) S) :=
    CommRingCat.ofHom (algebraMap A _)
  have hw : e.hom ≫ Spec.map f = ψ ≫ 𝟙 _ := by
    rw [Category.comp_id]
    show (H.isoPullback.hom ≫ (pullbackSpecIso S A _).hom) ≫ Spec.map f = ψ
    rw [Category.assoc]
    simp only [f, pullbackSpecIso_hom_fst', IsPullback.isoPullback_hom_fst]
  have hpt : ψ.base w = (Spec.map f).base (e.hom.base w) := by
    have := congrArg (fun g : W ⟶ _ => g.base w) hw
    simpa using this.symm
  set q' : PrimeSpectrum (A ⊗[S] AdicCompletion (IsLocalRing.maximalIdeal S) S) := e.hom.base w
    with hq'
  rw [orderDescends_stalkMap_iff_of_square e.hom (Spec.map f) ψ (𝟙 _) hw w]
  have hreg0 : IsRegularLocalRing ((Spec (CommRingCat.of A)).presheaf.stalk
      ((Spec.map f).base q')) :=
    IsRegularLocalRing.of_ringEquiv
      ((Spec (CommRingCat.of A)).presheaf.stalkCongr (.of_eq hpt)).commRingCatIsoToRingEquiv
  have hreg1 : IsRegularLocalRing ((Spec (CommRingCat.of A)).presheaf.stalk
      (q'.comap f.hom)) := hreg0
  have hreg : IsRegularLocalRing (Localization.AtPrime (q'.asIdeal.comap (algebraMap A _))) :=
    IsRegularLocalRing.of_ringEquiv
      (Spec.stalkIso (CommRingCat.of A) (q'.comap f.hom)).commRingCatIsoToRingEquiv
  have key := Scheme.localRingHom_comp_stalkIso f q'
  refine OrderDescends.of_arrow_iso
    (φ' := Localization.localRingHom (q'.comap f.hom).asIdeal q'.asIdeal f.hom rfl)
    (Spec.stalkIso (CommRingCat.of A) (q'.comap f.hom)).commRingCatIsoToRingEquiv
    (Spec.stalkIso (CommRingCat.of (A ⊗[S] AdicCompletion (IsLocalRing.maximalIdeal S) S))
      q').commRingCatIsoToRingEquiv ?_ ?_
  · intro x
    rw [← key]
    exact (Spec.stalkIso (CommRingCat.of (A ⊗[S] AdicCompletion (IsLocalRing.maximalIdeal S) S))
      q').inv_hom_id_apply _
  · intro J k h
    exact le_pow_maximalIdeal_of_map_le_pow_of_isHironakaBase (S := S) (A := A) q'.asIdeal J k h


/-- The order statement for the pull-back `cS : Ŷ → P` of `Spec Ŝ → Spec S` along a morphism
`gS : P → Spec S` which is locally of finite type, `S ∈ 𝔅`: reduction to the affine chart. -/
theorem orderDescends_stalkMap_of_isPullback_of_locallyOfFiniteType {S : Type u} [CommRing S]
    [IsLocalRing S] [IsHironakaBase S] {P Y : Scheme.{u}} (gS : P ⟶ Spec (CommRingCat.of S))
    [LocallyOfFiniteType gS] (cS : Y ⟶ P)
    (ĝ : Y ⟶ Spec (CommRingCat.of (AdicCompletion (IsLocalRing.maximalIdeal S) S)))
    (H : IsPullback cS ĝ gS
      (Spec.map (CommRingCat.ofHom (algebraMap S (AdicCompletion (IsLocalRing.maximalIdeal S) S)))))
    (y : Y) [IsRegularLocalRing (P.presheaf.stalk (cS y))] :
    OrderDescends (cS.stalkMap y).hom := by
  obtain ⟨W, hW, hyW, -⟩ := exists_isAffineOpen_mem_and_subset
    (U := ⊤) (x := cS y) (by simp)
  have : IsAffine (W : Scheme) := hW
  let y' : ((cS ⁻¹ᵁ W : Y.Opens) : Scheme.{u}) := ⟨y, hyW⟩
  have hsq := (isPullback_morphismRestrict cS W)
  have hw1 : (cS ⁻¹ᵁ W).ι ≫ cS = (cS ∣_ W) ≫ W.ι := (morphismRestrict_ι cS W).symm
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
  have := hft
  have hid : IsIso (Scheme.Hom.stalkMap (𝟙 ((cS ⁻¹ᵁ W : Y.Opens) : Scheme.{u})) y') := by
    rw [Scheme.Hom.stalkMap_id]; exact CategoryTheory.IsIso.id _
  have hreg1 : IsRegularLocalRing (P.presheaf.stalk (cS y'.1)) := ‹_›
  have hreg2 : IsRegularLocalRing ((W : Scheme).presheaf.stalk ((cS ∣_ W) y')) :=
    (isRegularLocalRing_stalk_iff_of_square (cS ⁻¹ᵁ W).ι cS (cS ∣_ W) W.ι hw1 y').mp hreg1
  have hreg3 : IsRegularLocalRing ((Spec Γ((W : Scheme), ⊤)).presheaf.stalk
      ((cS ∣_ W ≫ ν.hom) y')) :=
    (isRegularLocalRing_stalk_iff_of_square (𝟙 ((cS ⁻¹ᵁ W : Y.Opens) : Scheme.{u}))
      (cS ∣_ W ≫ ν.hom) (cS ∣_ W) ν.hom (by simp) y').mpr hreg2
  have h3 := @orderDescends_stalkMap_of_isPullback_spec S _ _ _ Γ((W : Scheme), ⊤) _ inst hft
    _ (cS ∣_ W ≫ ν.hom) _ HpbS y' hreg3
  have h2 := (orderDescends_stalkMap_iff_of_square
    (𝟙 ((cS ⁻¹ᵁ W : Y.Opens) : Scheme.{u})) (cS ∣_ W ≫ ν.hom) (cS ∣_ W) ν.hom
    (by simp) y').mpr h3
  exact (orderDescends_stalkMap_iff_of_square (cS ⁻¹ᵁ W).ι cS (cS ∣_ W) W.ι hw1 y').mp h2



/-- A flat preimmersion is an isomorphism on stalks. -/
theorem isIso_stalkMap_of_flat_of_isPreimmersion {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f]
    [IsPreimmersion f] (x : X) : IsIso (f.stalkMap x) := by
  have hsurj := f.stalkMap_surjective x
  have hinj : Function.Injective (f.stalkMap x) := by
    algebraize [(f.stalkMap x).hom]
    have : Module.FaithfullyFlat (Y.presheaf.stalk (f x)) (X.presheaf.stalk x) :=
      @Module.FaithfullyFlat.of_flat_of_isLocalHom _ _ _ _ _ _ _
        (Flat.stalkMap f x) (f.toLRSHom.prop x)
    exact ‹RingHom.FaithfullyFlat _›.injective
  exact (ConcreteCategory.isIso_iff_bijective _).mpr ⟨hinj, hsurj⟩


/-- **The scheme-level bridge for Lemma (CD.5)** (p. 320).  Let `S = O_{X,x₀}` belong to the
class 𝔅, `g : Y → X` be locally of finite type and `c : Ŷ → Y`, `ĝ : Ŷ → Spec Ŝ` the pull-back
of `g` along `Spec Ŝ → Spec S → X`.  Then for every point `ŷ` of `Ŷ` such that `O_{Y,c ŷ}` is
regular, `J O_{Ŷ,ŷ} ⊆ M̂^k` implies `J ⊆ M^k` for ideals `J` of `O_{Y,c ŷ}`.

Deviation from the paper (gap filled): the paper says "This can be easily deduced from the fact
that `X̂_s = X_s ×_X Spec(Ŝ)` and that `S` belongs to the class 𝔅" (p. 320).  Lean first replaces
`Y` by `P = Y ×_X Spec S` (the stalks agree, since `P → Y` is flat and a preimmersion), then
passes to an affine chart `Spec A ⊆ P`, `A` of finite type over `S`, where
`Ŷ ⊇ Spec (A ⊗_S Ŝ)` and the ring statement
`le_pow_maximalIdeal_of_map_le_pow_of_isHironakaBase` applies. -/
theorem orderDescends_stalkMap_of_isPullback_completion {X Y Ŷ : Scheme.{u}} (x₀ : X)
    [IsHironakaBase (X.presheaf.stalk x₀)] (g : Y ⟶ X) [LocallyOfFiniteType g] (c : Ŷ ⟶ Y)
    (ĝ : Ŷ ⟶ Spec (CommRingCat.of (AdicCompletion (IsLocalRing.maximalIdeal (X.presheaf.stalk x₀))
      (X.presheaf.stalk x₀))))
    (H : IsPullback c ĝ g (Spec.map (CommRingCat.ofHom (algebraMap (X.presheaf.stalk x₀)
      (AdicCompletion (IsLocalRing.maximalIdeal (X.presheaf.stalk x₀))
        (X.presheaf.stalk x₀)))) ≫ X.fromSpecStalk x₀))
    (ŷ : Ŷ) [IsRegularLocalRing (Y.presheaf.stalk (c ŷ))] :
    OrderDescends (c.stalkMap ŷ).hom := by
  obtain ⟨P, π, gS, cS, H1, hc, H2⟩ := exists_factorization_isPullback x₀ g c ĝ _ H
  subst hc
  have hflat : Flat π := MorphismProperty.of_isPullback H1.flip (flat_fromSpecStalk X x₀)
  have hpre : IsPreimmersion π := MorphismProperty.of_isPullback (P := @IsPreimmersion) H1.flip
    inferInstance
  have hfin : LocallyOfFiniteType gS :=
    MorphismProperty.of_isPullback (P := @LocallyOfFiniteType) H1 inferInstance
  have hiso := isIso_stalkMap_of_flat_of_isPreimmersion π (cS ŷ)
  have hreg : IsRegularLocalRing (Y.presheaf.stalk (π (cS ŷ))) := ‹_›
  have hregP : IsRegularLocalRing (P.presheaf.stalk (cS ŷ)) :=
    IsRegularLocalRing.of_ringEquiv (asIso (π.stalkMap (cS ŷ))).commRingCatIsoToRingEquiv
  have hloc : IsLocalRing (X.presheaf.stalk x₀) := inferInstance
  have h1 := @orderDescends_stalkMap_of_isPullback_of_locallyOfFiniteType
    (X.presheaf.stalk x₀) _ hloc _ P Ŷ gS hfin cS ĝ H2 ŷ hregP
  have hid : IsIso (Scheme.Hom.stalkMap (𝟙 Ŷ) ŷ) := by
    rw [Scheme.Hom.stalkMap_id]; exact CategoryTheory.IsIso.id _
  exact (orderDescends_stalkMap_iff_of_square (𝟙 Ŷ) (cS ≫ π) cS π (by simp) ŷ).mp h1

end Bridge

end Hironaka
