/-
Copyright (c) 2026 Daattavya Aggarwal, Minhyong Kim, Oisin Kim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daattavya Aggarwal, Minhyong Kim, Oisin Kim
-/
module

public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.FieldTheory.PurelyInseparable.Basic
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.LocalProperties.Reduced
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Architect
public import Hironaka.Ch3.JStability
public import Hironaka.Compat.FieldTensor

/-!
# Canonical lifts whose closed fibre is a field (Lemma 4, Remark 1)

Remark 1 (pp. 262-263) lifts a sequence of monoidal transforms of `R` to one of `R'` along a local
homomorphism `R -> R'` which transforms a regular system of parameters into one and whose residue
field extension is separable.  At each stage the paper applies Lemma 4 of Ch. III §2
(pp. 210-212) to the new homomorphism `R_alpha -> R'_alpha`: "By Lemma 4, §2, `R_alpha -> R'_alpha`
has the same properties as `R -> R'` for every `alpha`" (p. 263).  This file proves these
properties (the paper does not argue them) for one stage:

* separable extensions are geometrically reduced
  (`isReduced_tensorProduct_of_isSeparableFieldExtension`, from Mac Lane's criterion as proved in
  `Hironaka/Compat/FieldTensor.lean`); the base change of a
  separable extension is separable at every prime of the tensor product
  (`isSeparableFieldExtension_of_algEquiv_localization`);
* if the closed fibre `R'_bar/M_{R'} R'_bar` of a canonical lift is a field, then `R' -> R'_bar`
  again transforms a regular system of parameters into one and is residually separable
  (`IsCanonicalLift.mapsRSOP_and_isResiduallySeparable_of_ringKrullDim_eq`, the closed fibre being a
  field as soon as `dim R'_bar = dim R'`, `IsCanonicalLift.map_maximalIdeal_eq_of_ringKrullDim_eq`).
-/

@[expose] public section

open IsLocalRing
open scoped TensorProduct

namespace Hironaka

universe u

section FieldRed

/-- A regular ring is reduced (its localizations at maximal ideals are regular local rings,
hence domains). -/
theorem isReduced_of_isRegularRing (A : Type u) [CommRing A] [IsRegularRing A] : IsReduced A := by
  refine isReduced_ofLocalizationMaximal A fun J hJ => ?_
  have : J.IsPrime := hJ.isPrime
  have : IsRegularLocalRing (Localization.AtPrime J) := inferInstance
  have : IsDomain (Localization.AtPrime J) := isDomain_of_isRegularLocalRing _
  infer_instance

variable {k : Type u} [Field k]

/-- A finitely generated field `K` over `k` which is separable in the sense of pp. 211-212 has
`E ⊗_k K` reduced for every finitely generated field extension `E` of `k`. -/
theorem isReduced_tensorProduct_of_isSeparable_of_fg (E K : Type u) [Field E] [Field K]
    [Algebra k E] [Algebra k K] [Algebra.EssFiniteType k K] (hE : (⊤ : IntermediateField k E).FG)
    (hK : IsSeparableFieldExtension k K) : IsReduced (E ⊗[k] K) := by
  obtain ⟨s, hs, hsep⟩ := exists_isTranscendenceBasis_isSeparable_of_forall_isReduced
    (k := k) (E := K) hK
  have : IsRegularRing (E ⊗[k] K) := isRegularRing_tensorProduct_of_isTranscendenceBasis hE s hs
  exact isReduced_of_isRegularRing _

/-- A subfield (intermediate field) of a separable extension is separable. -/
theorem IsSeparableFieldExtension.intermediateField {K : Type u} [Field K] [Algebra k K]
    (hK : IsSeparableFieldExtension k K) (F : IntermediateField k K) :
    IsSeparableFieldExtension k F := fun k' _ _ h =>
  have := hK k' h
  isReduced_of_injective (Algebra.TensorProduct.map F.val (AlgHom.id k k'))
    (Module.Flat.rTensor_preserves_injective_linearMap (M := k') F.val.toLinearMap
      F.val.injective)

/-- **Separable extensions are geometrically reduced** (consequence of Mac Lane's criterion, as
used on p. 212): if `K/k` is separable in the sense of pp. 211-212 (`K ⊗_k k''` reduced for every
purely inseparable `k''`), then `E ⊗_k K` is reduced for every field extension `E` of `k`. -/
theorem isReduced_tensorProduct_of_isSeparableFieldExtension (E K : Type u) [Field E] [Field K]
    [Algebra k E] [Algebra k K] (hK : IsSeparableFieldExtension k K) : IsReduced (E ⊗[k] K) := by
  -- reduce to finitely generated subalgebras `B` of `K`
  refine IsReduced.tensorProduct_of_flat_of_forall_fg fun B hB => ?_
  obtain ⟨s, hs⟩ := hB
  let F : IntermediateField k K := IntermediateField.adjoin k (s : Set K)
  have hBF : B ≤ F.toSubalgebra := hs ▸ IntermediateField.algebra_adjoin_le_adjoin k (s : Set K)
  have hFfg : Algebra.EssFiniteType k F :=
    IntermediateField.essFiniteType_iff.mpr ⟨s, rfl⟩
  have hFsep : IsSeparableFieldExtension k F := hK.intermediateField F
  have : Module.Flat k F := Module.Flat.of_free
  -- `E ⊗_k F` is reduced
  have hEF : IsReduced (E ⊗[k] F) := by
    have hcomm : IsReduced (F ⊗[k] E) := by
      refine IsReduced.tensorProduct_of_flat_of_forall_fg fun B' hB' => ?_
      obtain ⟨t, ht⟩ := hB'
      let E' : IntermediateField k E := IntermediateField.adjoin k (t : Set E)
      have hBE' : B' ≤ E'.toSubalgebra :=
        ht ▸ IntermediateField.algebra_adjoin_le_adjoin k (t : Set E)
      have hE'fg : Algebra.EssFiniteType k E' :=
        IntermediateField.essFiniteType_iff.mpr ⟨t, rfl⟩
      have hred : IsReduced (E' ⊗[k] F) :=
        isReduced_tensorProduct_of_isSeparable_of_fg E' F (IntermediateField.fg_top k E') hFsep
      have hred' : IsReduced (F ⊗[k] E') :=
        isReduced_of_injective (Algebra.TensorProduct.comm k F E').toAlgHom
          (Algebra.TensorProduct.comm k F E').injective
      exact isReduced_of_injective
        (Algebra.TensorProduct.map (AlgHom.id k F) (Subalgebra.inclusion hBE'))
        (Module.Flat.lTensor_preserves_injective_linearMap _ (Subalgebra.inclusion_injective hBE'))
    exact isReduced_of_injective (Algebra.TensorProduct.comm k E F).toAlgHom
      (Algebra.TensorProduct.comm k E F).injective
  exact isReduced_of_injective
    (Algebra.TensorProduct.map (AlgHom.id k E) (Subalgebra.inclusion hBF))
    (Module.Flat.lTensor_preserves_injective_linearMap _ (Subalgebra.inclusion_injective hBF))

end FieldRed

section LocalizationSeparable

attribute [local instance] Algebra.TensorProduct.rightAlgebra in
/-- The tensor product of a localization `A = M⁻¹R` with a reduced `R`-algebra is reduced
(it is a localization of that algebra). -/
theorem isReduced_tensorProduct_localization {R S : Type u} [CommRing R] [CommRing S]
    [Algebra R S] (M : Submonoid R) (A : Type u) [CommRing A] [Algebra R A] [IsLocalization M A]
    [IsReduced S] : IsReduced (A ⊗[R] S) := by
  have : IsLocalization (Algebra.algebraMapSubmonoid S M) (A ⊗[R] S) := inferInstance
  exact isReduced_localizationPreserves (Algebra.algebraMapSubmonoid S M) (A ⊗[R] S) inferInstance

/-- The base change of a separable extension to a field is, at every prime ideal of the tensor
product, again separable: if `kb/k` is separable (pp. 211-212) and `Q` is a field which is
`k'`-isomorphic to the localization of `k' ⊗_k kb` at a prime ideal `𝔭`, then `Q/k'` is separable.
(`Q = A_𝔭` is a localization of `A ⊗_{k'} L ≅ L ⊗_k kb` for every extension `L` of `k'`, which is
reduced by `isReduced_tensorProduct_of_isSeparableFieldExtension`.) -/
theorem isSeparableFieldExtension_of_algEquiv_localization {k k' kb Q : Type u} [Field k]
    [Field k'] [Field kb] [Field Q] [Algebra k k'] [Algebra k kb] [Algebra k' Q]
    (hsep : IsSeparableFieldExtension k kb) (𝔭 : Ideal (k' ⊗[k] kb)) [𝔭.IsPrime]
    (e : Localization.AtPrime 𝔭 ≃ₐ[k'] Q) : IsSeparableFieldExtension k' Q := by
  intro L _ _ _
  let _ : Algebra k L := ((algebraMap k' L).comp (algebraMap k k')).toAlgebra
  have : IsScalarTower k k' L := IsScalarTower.of_algebraMap_eq fun x => rfl
  -- `(k' ⊗_k kb) ⊗_{k'} L` is reduced
  have hA : IsReduced ((k' ⊗[k] kb) ⊗[k'] L) := by
    have h1 : IsReduced (L ⊗[k] kb) :=
      isReduced_tensorProduct_of_isSeparableFieldExtension L kb hsep
    have e1 : L ⊗[k'] (k' ⊗[k] kb) ≃ₐ[k'] L ⊗[k] kb :=
      Algebra.TensorProduct.cancelBaseChange k k' k' L kb
    have h2 : IsReduced (L ⊗[k'] (k' ⊗[k] kb)) :=
      isReduced_of_injective e1.toAlgHom e1.injective
    exact isReduced_of_injective (Algebra.TensorProduct.comm k' (k' ⊗[k] kb) L).toAlgHom
      (Algebra.TensorProduct.comm k' (k' ⊗[k] kb) L).injective
  -- tensoring the localization
  have hloc : IsReduced (Localization.AtPrime 𝔭 ⊗[k' ⊗[k] kb] ((k' ⊗[k] kb) ⊗[k'] L)) := by
    have := hA
    exact isReduced_tensorProduct_localization 𝔭.primeCompl (Localization.AtPrime 𝔭)
  have e2 : Localization.AtPrime 𝔭 ⊗[k' ⊗[k] kb] ((k' ⊗[k] kb) ⊗[k'] L) ≃ₐ[k' ⊗[k] kb]
      Localization.AtPrime 𝔭 ⊗[k'] L :=
    Algebra.TensorProduct.cancelBaseChange k' (k' ⊗[k] kb) (k' ⊗[k] kb) (Localization.AtPrime 𝔭) L
  have h3 : IsReduced (Localization.AtPrime 𝔭 ⊗[k'] L) :=
    isReduced_of_injective e2.symm.toRingEquiv.toRingHom e2.symm.toRingEquiv.injective
  exact isReduced_of_injective
    (Algebra.TensorProduct.congr e.symm (AlgEquiv.refl (R := k') (A₁ := L))).toAlgHom
    (AlgEquiv.injective _)

end LocalizationSeparable

section FibreSeparable

variable {R Rb : Type u} [CommRing R] [IsRegularLocalRing R] [IsDomain R] [CommRing Rb]
  [IsRegularLocalRing Rb] [IsDomain Rb]

/-- **The residue field of a canonical lift with a field as closed fibre** (p. 212): if `α : R → R̄`
transforms a regular system of parameters into one and is residually separable, and the canonical
lift `β : R' → R̄'` of a monoidal transform has `M_{R'}R̄' = M_{R̄'}` (the closed fibre
`R̄'/M_{R'}R̄'` is a field), then the residue field `k̄'` of `R̄'` is `k'`-isomorphic to the
localization of `k' ⊗_k k̄` at a prime ideal (`R̄'` is a localization of `R' ⊗_R R̄`, p. 211), and
is therefore separable over the residue field `k'` of `R'`. -/
theorem IsCanonicalLift.isResiduallySeparable_of_map_maximalIdeal_eq (α : R →+* Rb)
    [IsLocalHom α] (hα : RingHom.MapsRSOP α) (hsep : RingHom.IsResiduallySeparable α)
    {P : Ideal R} (t : MonoidalTransform R P) (tb : MonoidalTransform Rb (P.map α))
    (β : t.ring →+* tb.ring) (hβ : IsCanonicalLift α t tb β)
    (hfield : (maximalIdeal t.ring).map β = maximalIdeal tb.ring) :
    haveI := hβ.isLocalHom
    RingHom.IsResiduallySeparable β := by
  have := hβ.isLocalHom
  let _ : Algebra R Rb := α.toAlgebra
  let _ : Algebra R t.ring := t.toRing.toAlgebra
  have : IsLocalHom (algebraMap R Rb) := inferInstanceAs (IsLocalHom α)
  have : IsLocalHom (algebraMap R t.ring) := t.isLocalHom_toRing
  obtain ⟨Θ, hΘ, hΘinj, hfracΘ, 𝔭, h𝔭, h𝔭char, -⟩ :=
    IsCanonicalLift.exists_tensorHom_injective_and_isFraction_and_quotient_equiv α hα t tb β hβ
  let _ : Algebra (t.ring ⊗[R] Rb) tb.ring := Θ.toAlgebra
  have hloc : IsLocalization.AtPrime tb.ring ((maximalIdeal tb.ring).comap Θ) :=
    isLocalization_comap_maximalIdeal_of_injective Θ hΘinj hfracΘ
  let ρ : tb.ring →+* Localization.AtPrime 𝔭 :=
    IsLocalization.lift (M := ((maximalIdeal tb.ring).comap Θ).primeCompl)
      (S := tb.ring) (g := (algebraMap _ (Localization.AtPrime 𝔭)).comp (residueTensorHom α t))
      fun y => IsLocalization.map_units (M := 𝔭.primeCompl) (Localization.AtPrime 𝔭)
        ⟨residueTensorHom α t y, fun h => y.2 ((h𝔭char y).mpr h)⟩
  have hρ : ∀ z, ρ (Θ z) = algebraMap _ (Localization.AtPrime 𝔭) (residueTensorHom α t z) :=
    fun z => IsLocalization.lift_eq _ z
  have hρI : ∀ a ∈ (maximalIdeal t.ring).map β, ρ a = 0 := by
    intro a ha
    have hle : (maximalIdeal t.ring).map β ≤ RingHom.ker ρ := by
      refine (Ideal.map_le_iff_le_comap (f := β) (K := RingHom.ker ρ)).mpr ?_
      intro y hy
      rw [Ideal.mem_comap, RingHom.mem_ker]
      have : β y = Θ (y ⊗ₜ 1) := by rw [hΘ, map_one, mul_one]
      rw [this, hρ, residueTensorHom_tmul, (residue_eq_zero_iff y).mpr hy,
        TensorProduct.zero_tmul, map_zero]
    exact hle ha
  have hmax0 : ∀ a ∈ maximalIdeal tb.ring, ρ a = 0 := fun a ha => hρI a (hfield ▸ ha)
  let ρ' : ResidueField tb.ring →+* Localization.AtPrime 𝔭 :=
    Ideal.Quotient.lift (maximalIdeal tb.ring) ρ hmax0
  have hρ' : ∀ z, ρ' (residue tb.ring (Θ z)) =
      algebraMap _ (Localization.AtPrime 𝔭) (residueTensorHom α t z) := fun z => hρ z
  have hinj : Function.Injective ρ' := ρ'.injective
  have hsurj : Function.Surjective ρ' := by
    intro w
    obtain ⟨⟨x, y⟩, rfl⟩ := IsLocalization.mk'_surjective 𝔭.primeCompl w
    obtain ⟨a₀, rfl⟩ := residueTensorHom_surjective α t x
    obtain ⟨s₀, hs₀⟩ := residueTensorHom_surjective α t y.1
    have hu : Θ s₀ ∉ maximalIdeal tb.ring := fun h => y.2 (hs₀ ▸ (h𝔭char s₀).mp h)
    have hres : residue tb.ring (Θ s₀) ≠ 0 := fun h => hu ((residue_eq_zero_iff _).mp h)
    refine ⟨residue tb.ring (Θ a₀) * (residue tb.ring (Θ s₀))⁻¹, ?_⟩
    rw [eq_comm, IsLocalization.mk'_eq_iff_eq_mul]
    rw [map_mul, mul_assoc, ← hs₀, ← hρ' s₀, ← map_mul, inv_mul_cancel₀ hres, map_one, mul_one,
      hρ']
  have hcompat : ∀ c : ResidueField t.ring, ρ' (ResidueField.map β c) =
      algebraMap (ResidueField t.ring) (Localization.AtPrime 𝔭) c := by
    intro c
    obtain ⟨y, rfl⟩ := residue_surjective c
    rw [ResidueField.map_residue]
    have : β y = Θ (y ⊗ₜ 1) := by rw [hΘ, map_one, mul_one]
    rw [this, hρ', residueTensorHom_tmul, map_one,
      IsScalarTower.algebraMap_apply (ResidueField t.ring)
        (ResidueField t.ring ⊗[ResidueField R] ResidueField Rb) (Localization.AtPrime 𝔭)]
    rfl
  rw [isResiduallySeparable_iff]
  let _ : Algebra (ResidueField t.ring) (ResidueField tb.ring) := (ResidueField.map β).toAlgebra
  have hsep' : IsSeparableFieldExtension (ResidueField R) (ResidueField Rb) := by
    have heq : (ResidueField.map α).toAlgebra =
        (inferInstance : Algebra (ResidueField R) (ResidueField Rb)) := by
      ext c
      obtain ⟨r, rfl⟩ := residue_surjective c
      rfl
    unfold RingHom.IsResiduallySeparable at hsep
    rw [heq] at hsep
    exact hsep
  let e : Localization.AtPrime 𝔭 ≃ₐ[ResidueField t.ring] ResidueField tb.ring :=
    AlgEquiv.ofRingEquiv (f := (RingEquiv.ofBijective ρ' ⟨hinj, hsurj⟩).symm) fun c => by
      rw [RingEquiv.symm_apply_eq]
      exact (hcompat c).symm
  exact isSeparableFieldExtension_of_algEquiv_localization hsep' 𝔭 e

end FibreSeparable

section FibreField

variable {R Rb : Type u} [CommRing R] [IsRegularLocalRing R] [IsDomain R] [CommRing Rb]
  [IsRegularLocalRing Rb] [IsDomain Rb]

/-- **The closed fibre of a canonical lift of the same dimension is a field** (p. 212): for a
residually separable `α` which transforms a regular system of parameters into one, and a canonical
lift `β : R' → R̄'` of regular local rings with `dim R̄' = dim R'`, we have `M_{R'}R̄' = M_{R̄'}`.
(The closed fibre `R̄'/M_{R'}R̄'` is regular of dimension `dim R̄' - dim R' = 0`.) -/
theorem IsCanonicalLift.map_maximalIdeal_eq_of_ringKrullDim_eq (α : R →+* Rb) [IsLocalHom α]
    (hα : RingHom.MapsRSOP α) (hsep : RingHom.IsResiduallySeparable α) {P : Ideal R}
    (t : MonoidalTransform R P) (tb : MonoidalTransform Rb (P.map α)) [IsRegularLocalRing t.ring]
    [IsRegularLocalRing tb.ring] (β : t.ring →+* tb.ring) (hβ : IsCanonicalLift α t tb β)
    (hdim : ringKrullDim tb.ring = ringKrullDim t.ring) :
    (maximalIdeal t.ring).map β = maximalIdeal tb.ring := by
  have := hβ.isLocalHom
  set I := (maximalIdeal t.ring).map β with hIdef
  have hI : I ≤ maximalIdeal tb.ring :=
    Ideal.map_le_iff_le_comap.mpr fun a ha => map_nonunit β a ha
  have : IsLocalRing (tb.ring ⧸ I) := isLocalRing_quotient_of_le hI
  have hreg : IsRegularLocalRing (tb.ring ⧸ I) :=
    IsCanonicalLift.isRegularLocalRing_quotient_map_maximalIdeal α hα t tb β hβ hsep
  have hheight := IsCanonicalLift.height_maximalIdeal_eq_add α hα t tb β hβ
  have hmax : (maximalIdeal tb.ring).map (Ideal.Quotient.mk I) = maximalIdeal (tb.ring ⧸ I) :=
    map_maximalIdeal_of_surjective _ Ideal.Quotient.mk_surjective
  -- heights are dimensions, which are finite for regular local rings
  have hht : (maximalIdeal tb.ring).height = (maximalIdeal t.ring).height := by
    have h1 := IsLocalRing.maximalIdeal_height_eq_ringKrullDim (R := tb.ring)
    have h2 := IsLocalRing.maximalIdeal_height_eq_ringKrullDim (R := t.ring)
    rw [hdim, ← h2] at h1
    exact_mod_cast h1
  have hfin : (maximalIdeal t.ring).height ≠ ⊤ := by
    intro h
    have h1 := IsRegularLocalRing.spanFinrank_maximalIdeal (R := t.ring)
    rw [← IsLocalRing.maximalIdeal_height_eq_ringKrullDim, h] at h1
    exact absurd (WithBot.coe_injective h1) (by simp)
  rw [hht] at hheight
  have h0 : ((maximalIdeal tb.ring).map (Ideal.Quotient.mk I)).height = 0 := by
    obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp hfin
    rw [← hn] at hheight
    revert hheight
    induction ((maximalIdeal tb.ring).map (Ideal.Quotient.mk I)).height using ENat.recTopCoe with
    | top => intro h; simp at h
    | coe m =>
      intro h
      have : (n : ℕ∞) + 0 = n + m := by rw [add_zero]; exact h
      have : (m : ℕ∞) = 0 := by
        have h2 : n + 0 = n + m := by exact_mod_cast this
        exact_mod_cast (Nat.add_left_cancel h2).symm
      exact this
  rw [hmax] at h0
  have h1 := IsRegularLocalRing.spanFinrank_maximalIdeal (R := tb.ring ⧸ I)
  have h2 := IsLocalRing.maximalIdeal_height_eq_ringKrullDim (R := tb.ring ⧸ I)
  rw [h0] at h2
  rw [← h2] at h1
  have hbot : maximalIdeal (tb.ring ⧸ I) = ⊥ := by
    have h3 : (maximalIdeal (tb.ring ⧸ I)).spanFinrank = 0 := by
      have := WithBot.coe_injective h1
      exact_mod_cast this
    exact (Submodule.spanFinrank_eq_zero_iff_eq_bot (IsNoetherian.noetherian _)).mp h3
  refine le_antisymm hI ?_
  intro a ha
  have : Ideal.Quotient.mk I a ∈ maximalIdeal (tb.ring ⧸ I) := by
    rw [← hmax]; exact Ideal.mem_map_of_mem _ ha
  rw [hbot, Ideal.mem_bot, Ideal.Quotient.eq_zero_iff_mem] at this
  exact this

end FibreField

section StageLemma

variable {R Rb : Type u} [CommRing R] [IsRegularLocalRing R] [IsDomain R] [CommRing Rb]
  [IsRegularLocalRing Rb] [IsDomain Rb]

open Classical in
/-- If `M_{R'}R̄' = M_{R̄'}` for a canonical lift `β : R' → R̄'`, then the image of a regular system
of parameters of `R'` is one of `R̄'` (as in the separable algebraic case of Lemma 4 (3), p. 212,
with the equality of the maximal ideals as hypothesis). -/
theorem IsCanonicalLift.isRegularSystemOfParameters_image_of_map_maximalIdeal_eq
    (α : R →+* Rb) [IsLocalHom α] (hα : RingHom.MapsRSOP α) {P : Ideal R}
    (t : MonoidalTransform R P) (tb : MonoidalTransform Rb (P.map α)) (β : t.ring →+* tb.ring)
    (hβ : IsCanonicalLift α t tb β) (hfield : (maximalIdeal t.ring).map β = maximalIdeal tb.ring)
    (s : Finset t.ring) (hs : IsRegularSystemOfParameters t.ring s) :
    IsRegularSystemOfParameters tb.ring (s.image β) := by
  have : IsNoetherianRing tb.ring := MonoidalTransform.isNoetherianRing tb
  have hspan : Ideal.span ((s.image β : Finset tb.ring) : Set tb.ring) = maximalIdeal tb.ring := by
    rw [Finset.coe_image, ← Ideal.map_span, hs.1, hfield]
  have hle : ringKrullDim tb.ring ≤ (s.image β).card := by
    refine (ringKrullDim_le_spanFinrank_maximalIdeal tb.ring).trans ?_
    rw [← hspan]
    have := Submodule.spanFinrank_span_le_ncard_of_finite (R := tb.ring) (s.image β).finite_toSet
    rw [Set.ncard_coe_finset] at this
    exact_mod_cast this
  have hge := IsCanonicalLift.ringKrullDim_le α hα t tb β hβ
  rw [← hs.2] at hge
  have hcard : (s.image β).card = s.card := by
    have h1 : s.card ≤ (s.image β).card := by exact_mod_cast hge.trans hle
    have := Finset.card_image_le (s := s) (f := β)
    omega
  exact ⟨hspan, le_antisymm (by rw [hcard]; exact hge) hle⟩

/-- **One stage of the lifting of a sequence** (Lemma 4, p. 212, in the situation of Remark 1,
p. 263): if `α : R → R̄` transforms a regular system of parameters into one and is residually
separable, and the canonical lift `β : R' → R̄'` of a monoidal transform `R'` of `R` with a prime
center `P` with `R/P` regular has `dim R̄' = dim R'` (e.g. if `R'` is residually algebraic over
`R`),
then `β` has the same properties: it transforms a regular system of parameters into one, and is
residually separable. -/
theorem IsCanonicalLift.mapsRSOP_and_isResiduallySeparable_of_ringKrullDim_eq
    (α : R →+* Rb) [IsLocalHom α] (hα : RingHom.MapsRSOP α) (hsep : RingHom.IsResiduallySeparable α)
    {P : Ideal R} (t : MonoidalTransform R P) (tb : MonoidalTransform Rb (P.map α))
    [IsRegularLocalRing t.ring] [IsRegularLocalRing tb.ring] (β : t.ring →+* tb.ring)
    (hβ : IsCanonicalLift α t tb β) (hdim : ringKrullDim tb.ring = ringKrullDim t.ring) :
    haveI := hβ.isLocalHom
    RingHom.MapsRSOP β ∧ RingHom.IsResiduallySeparable β := by
  have hfield := IsCanonicalLift.map_maximalIdeal_eq_of_ringKrullDim_eq α hα hsep t tb β hβ hdim
  refine ⟨?_, IsCanonicalLift.isResiduallySeparable_of_map_maximalIdeal_eq α hα hsep t tb β hβ
    hfield⟩
  obtain ⟨-, s, hs⟩ := (isRegularLocalRing_iff_exists_rsop t.ring).mp inferInstance
  exact ⟨s, hs, IsCanonicalLift.isRegularSystemOfParameters_image_of_map_maximalIdeal_eq α hα t tb
    β hβ hfield s hs, (IsCanonicalLift.injective_of_mapsRSOP α hα t tb β hβ).injOn⟩

end StageLemma

end Hironaka
