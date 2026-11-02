/-
Copyright (c) 2026 Daattavya Aggarwal, Minhyong Kim, Oisin Kim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daattavya Aggarwal, Minhyong Kim, Oisin Kim
-/
module

public import Mathlib.FieldTheory.IsSepClosed
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.AdicCompletion.LocalRing
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Architect
public import Hironaka.Ch3.Basic
public import Hironaka.Ch3.Transforms
public import Hironaka.Ch3.NuStar
public import Hironaka.Ch3.TauStar
public import Hironaka.Ch3.PermissibleEffects
public import Hironaka.Ch3.TransformsCompletion
public import Hironaka.Compat.NagataFinite
public import Hironaka.Ch3.Frames
public import Hironaka.Compat.MvPowerSeriesRegular
public import Hironaka.Compat.FrameGraded
public import Hironaka.Compat.FrameTransformCriterion

/-!
# Compatibility layer: the reduction to a complete regular local ring with separably closed residue
field (and residually rational monoidal transforms), Ch. III pp. 234, 254, 256, 258

The proofs of Theorem 3 (p. 234), Lemma 20 and Lemma 21 (p. 254, 256), Proposition 2 (p. 258) and
Lemma 25 begin with the sentence "we may assume that `R` is complete and that `R₁` is residually
rational over `R`":

> Let `S → S̃` be any local homomorphism such that a regular system of parameters of `S` is
> transformed into such a system of parameters of `S̃` and that the residue field of `S̃` is
> separable algebraic over that of `S`. … If we replace `S` by `S̃`, `R` by `R̃ = S̃{z₁,…,z_r}`, and
> `P` and `J` by their extensions in `R̃`, and `R₁` by a monoidal transform `R̃₁` of `R̃` with centre
> `PR̃` which admits a canonical local homomorphism `R₁ → R̃₁`, all the assumptions … remain valid,
> and the conclusions … are replaced by equivalent ones. Therefore we may assume that `R` and `S`
> are complete and that `R₁` is residually rational over `R`. (Lemma 20, p. 254)
>
> We may assume that `R` is complete, and that `R₁` is residually rational over `R`.
> (Proposition 2, p. 258)

This file is the frame-free ("`R`-level") part of that reduction.  It is built from
* the maximal local extension `exists_maximal_local_extension` (`Ch3/PermissibleEffects.lean`:
  a regular local `R'`, `R → R'` transforming a regular system of parameters into one, residue
  field extension separable algebraic, residue field of `R'` separably closed) composed with the
  adic completion `R' → R̂'` (`Ch3/TransformsCompletion.lean`; the residue field does not change),
  see `CompleteSepClosedExtension`;
* the canonical lift `T̄` of a monoidal transform `T` of `R` to `R̄` (`exists_isCanonicalLift`) and
  Lemma 4 (`RingHom.MapsRSOP.canonicalLift_properties`), see `CompleteSepClosedExtension.Lift`;
* the invariance of `ν`, `ν*`, `τ`, of the strict transform and of permissibility under such base
  changes (`nuStar_map_eq_of_mapsRSOP`, `strictTransform_map_of_mapsRSOP`,
  `isPermissibleCenter_map_iff`, …).

The frame-level part (`S → S̃`, `R̃ = S̃{z}`, frame transforms) is in
`Hironaka/Compat/CompleteRationalFrameBaseChange.lean`.

Main results:
* `CompleteSepClosedExtension`, `CompleteSepClosedExtension.nonempty`: the extension `R → R̄`.
* `CompleteSepClosedExtension.Lift`: the canonical lift of a monoidal transform; it is residually
  rational over `R̄` when `T` is residually separable algebraic over `R`.
* `proposition2_of_complete_residuallyRational`: Proposition 2 follows from its special case for
  complete `R` and residually rational `R₁` (`Proposition2Complete`).
-/

@[expose] public section

open IsLocalRing

namespace Hironaka

universe u

/-! ### Auxiliary facts on homomorphisms of local rings -/

section Aux

variable {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]

/-- If `α` and `β` transform a regular system of parameters into one, so does `β ∘ α`. -/
theorem RingHom.mapsRSOP_comp [IsRegularLocalRing A] [IsRegularLocalRing B] [IsRegularLocalRing C]
    {α : A →+* B} {β : B →+* C} (hα : RingHom.MapsRSOP α) (hβ : RingHom.MapsRSOP β) :
    RingHom.MapsRSOP (β.comp α) := by
  classical
  obtain ⟨s, hs, hs', hinj⟩ := hα
  obtain ⟨h2, hcard2⟩ := hβ.isRegularSystemOfParameters_image hs'
  have himg : (s.image α).image β = s.image (β.comp α) := by
    rw [Finset.image_image, RingHom.coe_comp]
  refine ⟨s, hs, himg ▸ h2, Finset.injOn_of_card_image_eq ?_⟩
  rw [← himg, hcard2, Finset.card_image_of_injOn hinj]

/-- A local homomorphism `β` with bijective residue field map preserves residual separability:
if `α` is residually separable algebraic, so is `β ∘ α`. -/
theorem RingHom.isResiduallySeparableAlgebraic_comp_of_bijective [IsLocalRing A] [IsLocalRing B]
    [IsLocalRing C] {α : A →+* B} {β : B →+* C} [IsLocalHom α] [IsLocalHom β]
    (hα : RingHom.IsResiduallySeparableAlgebraic α)
    (hβ : Function.Bijective (ResidueField.map β)) :
    RingHom.IsResiduallySeparableAlgebraic (β.comp α) := by
  let _ : Algebra (ResidueField A) (ResidueField B) := (ResidueField.map α).toAlgebra
  have : Algebra.IsSeparable (ResidueField A) (ResidueField B) := hα
  let _ : Algebra (ResidueField A) (ResidueField C) :=
    (ResidueField.map (β.comp α)).toAlgebra
  show Algebra.IsSeparable (ResidueField A) (ResidueField C)
  refine Algebra.IsSeparable.of_equiv_equiv (RingEquiv.refl (ResidueField A))
    (RingEquiv.ofBijective (ResidueField.map β) hβ) (RingHom.ext fun x => ?_)
  exact RingHom.congr_fun (ResidueField.map_comp α β) x

/-- A local homomorphism with surjective residue field map (residually rational) is residually
separable algebraic: the residue field extension is trivial. -/
theorem RingHom.isResiduallySeparableAlgebraic_of_residueField_surjective [IsLocalRing A]
    [IsLocalRing B] {α : A →+* B} [IsLocalHom α]
    (h : Function.Surjective (ResidueField.map α)) : RingHom.IsResiduallySeparableAlgebraic α := by
  let _ : Algebra (ResidueField A) (ResidueField B) := (ResidueField.map α).toAlgebra
  refine ⟨fun x => ?_⟩
  obtain ⟨y, rfl⟩ := h x
  exact isSeparable_algebraMap y

/-- Separable closedness is invariant under ring isomorphisms of fields. -/
theorem isSepClosed_of_ringEquiv' {k k' : Type*} [Field k] [Field k'] [IsSepClosed k]
    (e : k ≃+* k') : IsSepClosed k' := by
  refine IsSepClosed.of_exists_root k' fun p _ hirr hsep => ?_
  let q := p.map (e.symm : k' →+* k)
  have hq : q.degree ≠ 0 := by
    rw [Polynomial.degree_map]
    exact (Polynomial.degree_pos_of_irreducible hirr).ne'
  obtain ⟨x, hx⟩ := IsSepClosed.exists_root q hq hsep.map
  refine ⟨e x, ?_⟩
  have hp : p = q.map (e : k →+* k') := by
    simp only [q, Polynomial.map_map]
    rw [show (e : k →+* k').comp (e.symm : k' →+* k) = RingHom.id k' from
      RingHom.ext fun y => e.apply_symm_apply y, Polynomial.map_id]
  rw [hp, Polynomial.eval_map]
  show Polynomial.eval₂ (e : k →+* k') ((e : k →+* k') x) q = 0
  rw [Polynomial.eval₂_at_apply, hx.eq_zero, map_zero]

end Aux

/-! ### The extension `R → R̄` (p. 234, p. 254, p. 258) -/

section Extension

/-- **The extension of the reduction** (p. 234: "a maximal local extension `R'` of `R` such that the
local homomorphism `R → R'` transforms a regular system of parameters of `R` into such a system of
parameters of `R'` and induces a separable algebraic extension of the residue fields"; p. 254,
p. 258: "we may assume that `R` is complete"): a *complete* regular local ring `R̄` with a local
homomorphism `α : R → R̄` that transforms a regular system of parameters into one, whose residue
field extension is separable algebraic and whose residue field is separably closed.  Then `α` is
faithfully flat, `MR̄ = M̄`, and every monoidal transform of `R` that is residually separable
algebraic has a canonical lift to `R̄` that is residually rational
(`CompleteSepClosedExtension.Lift`). -/
structure CompleteSepClosedExtension (R : Type u) [CommRing R] [IsRegularLocalRing R] where
  /-- The ring `R̄`. -/
  ring : Type u
  [commRing : CommRing ring]
  [isRegularLocalRing : IsRegularLocalRing ring]
  /-- The structure map `α : R → R̄`. -/
  hom : R →+* ring
  [isLocalHom : IsLocalHom hom]
  /-- `α` transforms a regular system of parameters of `R` into one of `R̄`. -/
  mapsRSOP : RingHom.MapsRSOP hom
  /-- The residue field of `R̄` is separable algebraic over that of `R`. -/
  isResiduallySeparableAlgebraic : RingHom.IsResiduallySeparableAlgebraic hom
  /-- The residue field of `R̄` is separably closed. -/
  isSepClosed : IsSepClosed (ResidueField ring)
  /-- `R̄` is complete for its maximal ideal. -/
  isAdicComplete : IsAdicComplete (maximalIdeal ring) ring

namespace CompleteSepClosedExtension

attribute [instance] commRing isRegularLocalRing isLocalHom

variable {R : Type u} [CommRing R] [IsRegularLocalRing R] (E : CompleteSepClosedExtension R)

/-- Existence of the extension: the completion of a maximal local extension. -/
theorem nonempty (R : Type u) [CommRing R] [IsRegularLocalRing R] :
    Nonempty (CompleteSepClosedExtension R) := by
  obtain ⟨R', _, _, α₁, _, hα₁, hsep₁, hsc₁⟩ := exists_maximal_local_extension R
  let R'' := AdicCompletion (maximalIdeal R') R'
  let β : R' →+* R'' := algebraMap R' R''
  have hβ : RingHom.MapsRSOP β := mapsRSOP_algebraMap_adicCompletion
  have : IsLocalHom β := inferInstance
  have hbij : Function.Bijective (ResidueField.map β) :=
    AdicCompletion.residueField_map_bijective R'
  have hsc : IsSepClosed (ResidueField R'') := by
    have := hsc₁
    exact isSepClosed_of_ringEquiv' (RingEquiv.ofBijective (ResidueField.map β) hbij)
  exact ⟨{
    ring := R''
    hom := β.comp α₁
    mapsRSOP := RingHom.mapsRSOP_comp hα₁ hβ
    isResiduallySeparableAlgebraic :=
      RingHom.isResiduallySeparableAlgebraic_comp_of_bijective hsep₁ hbij
    isSepClosed := hsc
    isAdicComplete := isAdicComplete_maximalIdeal_adicCompletion R' }⟩

/-- `R̄` is a domain (a regular local ring is a domain). -/
instance isDomain : IsDomain E.ring := Transforms.isDomain_of_isRegularLocalRing E.ring

/-- `α` is injective. -/
theorem hom_injective : Function.Injective E.hom :=
  RingHom.MapsRSOP.injective E.hom E.mapsRSOP

/-- `α` is flat. -/
theorem flat : letI := E.hom.toAlgebra; Module.Flat R E.ring :=
  RingHom.MapsRSOP.flat E.mapsRSOP

/-- `α` is faithfully flat. -/
theorem faithfullyFlat : letI := E.hom.toAlgebra; Module.FaithfullyFlat R E.ring := by
  let _ := E.hom.toAlgebra
  have _ : Module.Flat R E.ring := E.flat
  have _ : IsLocalHom (algebraMap R E.ring) := E.isLocalHom
  exact Module.FaithfullyFlat.of_flat_of_isLocalHom

/-- `MR̄ = M̄`. -/
theorem map_maximalIdeal : (maximalIdeal R).map E.hom = maximalIdeal E.ring :=
  RingHom.MapsRSOP.map_maximalIdeal E.mapsRSOP

/-- `ν*`, `ν^{(i)}` do not change: `ν*(J) = ν*(JR̄)` (the Corollary to Lemma 2). -/
theorem nuStar_map (J : Ideal R) : nuStar E.ring (J.map E.hom) = nuStar R J :=
  (nuStar_map_eq_of_mapsRSOP E.hom E.mapsRSOP J).symm

/-- The characteristic of `R̄` is that of its residue field when this holds for `R`. -/
theorem ringChar_eq (h : ringChar R = ringChar (ResidueField R)) :
    ringChar E.ring = ringChar (ResidueField E.ring) := by
  have h1 : CharP E.ring (ringChar R) :=
    (RingHom.charP_iff E.hom E.hom_injective _).mp (ringChar.charP R)
  have h2 : CharP (ResidueField E.ring) (ringChar (ResidueField R)) :=
    (RingHom.charP_iff (ResidueField.map E.hom) (ResidueField.map E.hom).injective _).mp
      (ringChar.charP _)
  rw [ringChar.eq E.ring (ringChar R), ringChar.eq (ResidueField E.ring)
    (ringChar (ResidueField R)), h]

/-- The residue field of `R̄` has characteristic zero when that of `R` does. -/
theorem charZero_residueField [CharZero (ResidueField R)] : CharZero (ResidueField E.ring) := by
  let _ : Algebra (ResidueField R) (ResidueField E.ring) := (ResidueField.map E.hom).toAlgebra
  exact charZero_of_injective_algebraMap (ResidueField.map E.hom).injective

/-- `J ⊆ P` and `P` permissible: `P` is a permissible centre for `J` iff `PR̄` is one for
`JR̄` (faithfully flat descent, Remark 1 of §5, `isPermissibleCenter_map_iff`). -/
theorem isPermissibleCenter_map_iff (J P : Ideal R) [P.IsPrime] (hJP : J ≤ P) :
    IsPermissibleCenter R J P ↔ IsPermissibleCenter E.ring (J.map E.hom) (P.map E.hom) :=
  (Hironaka.isPermissibleCenter_map_iff E.hom E.mapsRSOP J P hJP).2.2.2

/-- For a prime `P` with `R/P` regular, `PR̄` is prime and `R̄/PR̄` is regular (Lemma 4). -/
theorem isPrime_map (P : Ideal R) [P.IsPrime] [IsRegularLocalRing (R ⧸ P)] :
    (P.map E.hom).IsPrime ∧ IsRegularLocalRing (E.ring ⧸ P.map E.hom) :=
  RingHom.MapsRSOP.isPrime_map_and_isRegularLocalRing_quotient E.mapsRSOP inferInstance
    inferInstance

/-- `P ≠ Q` stays `P R̄ ≠ Q R̄`, and inclusions are preserved. -/
theorem map_injective_ideal : Function.Injective (Ideal.map E.hom : Ideal R → Ideal E.ring) := by
  let _ := E.hom.toAlgebra
  have _ := E.faithfullyFlat
  intro I I' h
  rw [← Ideal.comap_map_eq_self_of_faithfullyFlat (B := E.ring) I,
    ← Ideal.comap_map_eq_self_of_faithfullyFlat (B := E.ring) I']
  exact congrArg _ h

end CompleteSepClosedExtension

end Extension

/-! ### The power series ring over a regular local ring is a regular local ring -/

section PowerSeriesRegular

open MvPowerSeries

/-- A formal power series in `n` variables with zero constant term lies in the ideal generated by
the variables (over any commutative ring; the proof of
`mvPowerSeries_mem_span_X_of_constantCoeff_eq_zero` of `Compat/MvPowerSeriesRegular.lean` does not
use that the coefficient ring is a field). -/
theorem mvPowerSeries_mem_span_X_of_constantCoeff_eq_zero_of_commRing {k : Type u} [CommRing k] {n : ℕ}
    {f : MvPowerSeries (Fin n) k}
    (hf : constantCoeff f = 0) :
    f ∈ Ideal.span (Set.range (X : Fin n → MvPowerSeries (Fin n) k)) := by
  classical
  let g : Fin n → MvPowerSeries (Fin n) k := fun i m =>
    if ∀ j < i, m j = 0 then coeff (m + Finsupp.single i 1) f else 0
  have hg : ∀ (i : Fin n) (m' : Fin n →₀ ℕ), coeff m' (g i) =
      if ∀ j < i, m' j = 0 then coeff (m' + Finsupp.single i 1) f else 0 := fun _ _ => rfl
  have key : f = ∑ i, X i * g i := by
    ext m
    rw [map_sum]
    simp only [X, coeff_monomial_mul]
    by_cases hm0 : m = 0
    · subst hm0
      rw [coeff_zero_eq_constantCoeff_apply, hf]
      symm
      refine Finset.sum_eq_zero fun x _ => ?_
      have hx : ¬ (Finsupp.single x 1 ≤ (0 : Fin n →₀ ℕ)) := by
        intro hx
        have := Finsupp.single_le_iff.mp hx
        simp at this
      simp [hx]
    · obtain ⟨i₀, hi₀, hmin⟩ : ∃ i₀ : Fin n, 1 ≤ m i₀ ∧ ∀ j < i₀, m j = 0 := by
        have hne : (Finset.univ.filter fun i : Fin n => 1 ≤ m i).Nonempty := by
          by_contra hcon
          apply hm0
          ext i
          by_contra hi
          refine hcon ⟨i, ?_⟩
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          simp at hi
          omega
        obtain ⟨i₀, hi₀mem, hi₀min⟩ := Finset.exists_min_image _ id hne
        refine ⟨i₀, (Finset.mem_filter.mp hi₀mem).2, fun j hj => ?_⟩
        by_contra hjm
        have : j ∈ Finset.univ.filter fun i : Fin n => 1 ≤ m i := by simp; omega
        exact absurd (hi₀min j this) (not_le.mpr hj)
      rw [Finset.sum_eq_single i₀]
      · have hle : Finsupp.single i₀ 1 ≤ m := Finsupp.single_le_iff.mpr hi₀
        have hcond : ∀ j < i₀, ((m - Finsupp.single i₀ 1 : Fin n →₀ ℕ) j) = 0 := by
          intro j hj
          simp [hj.ne, hmin j hj]
        simp only [hle, ↓reduceIte, one_mul]
        rw [hg]
        split_ifs
        rw [tsub_add_cancel_of_le hle]
      · intro i _ hne
        by_cases hle : Finsupp.single i 1 ≤ m
        · have hnot : ¬ ∀ j < i, ((m - Finsupp.single i 1 : Fin n →₀ ℕ) j) = 0 := by
            intro hall
            rcases lt_or_gt_of_ne hne with hlt | hlt
            · have := hmin i hlt
              have h1 := Finsupp.single_le_iff.mp hle
              omega
            · have := hall i₀ hlt
              simp [hlt.ne] at this
              omega
          simp only [hle, ↓reduceIte, one_mul]
          rw [hg]
          split_ifs
          rfl
        · simp [hle]
      · intro h; exact absurd (Finset.mem_univ _) h
  rw [key]
  exact Ideal.sum_mem _ fun i _ => Ideal.mul_mem_right _ _ (Ideal.subset_span ⟨i, rfl⟩)

variable (S : Type u) [CommRing S]

/-- `S⟦X₁, …, X_n⟧` has Krull dimension at least `dim S + n`. -/
theorem ringKrullDim_mvPowerSeries_ge : ∀ n : ℕ,
    ringKrullDim S + n ≤ ringKrullDim (MvPowerSeries (Fin n) S)
  | 0 => by
    have hinj : Function.Injective (constantCoeff (σ := Fin 0) (R := S)) := by
      intro φ ψ h
      ext m
      have hm : m = 0 := Subsingleton.elim _ _
      rw [hm, coeff_zero_eq_constantCoeff_apply, coeff_zero_eq_constantCoeff_apply, h]
    let e : MvPowerSeries (Fin 0) S ≃+* S :=
      RingEquiv.ofBijective (constantCoeff (σ := Fin 0) (R := S)) ⟨hinj, fun s => ⟨C s, by simp⟩⟩
    rw [ringKrullDim_eq_of_ringEquiv e]
    simp
  | n + 1 => by
    rw [ringKrullDim_eq_of_ringEquiv (MvPowerSeries.finSuccEquiv (R := S) n).toRingEquiv]
    have h := ringKrullDim_powerSeries_ge (MvPowerSeries (Fin n) S)
    refine le_trans ?_ h
    push_cast
    rw [← add_assoc]
    exact add_le_add_left (ringKrullDim_mvPowerSeries_ge n) 1

variable [IsLocalRing S]

open Classical in
/-- The maximal ideal of `S⟦X₁, …, X_n⟧` is generated by the variables and the generators of the
maximal ideal of `S`. -/
theorem maximalIdeal_mvPowerSeries_eq (n : ℕ) {t : Finset S}
    (ht : Ideal.span (t : Set S) = maximalIdeal S) :
    maximalIdeal (MvPowerSeries (Fin n) S) =
      Ideal.span ((Finset.univ.image (X : Fin n → MvPowerSeries (Fin n) S) ∪
        t.image (C : S →+* MvPowerSeries (Fin n) S) : Finset _) : Set _) := by
  classical
  apply le_antisymm
  · intro f hf
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, MvPowerSeries.isUnit_iff_constantCoeff]
      at hf
    have hc : constantCoeff f ∈ maximalIdeal S := hf
    rw [← ht] at hc
    have h1 : f = C (constantCoeff f) + (f - C (constantCoeff f)) := by ring
    rw [h1]
    refine Ideal.add_mem _ ?_ ?_
    · have := Ideal.mem_map_of_mem (C : S →+* MvPowerSeries (Fin n) S) hc
      rw [Ideal.map_span] at this
      refine Ideal.span_mono ?_ this
      intro x hx
      obtain ⟨y, hy, rfl⟩ := hx
      simp only [Finset.coe_union, Finset.coe_image, Finset.coe_univ, Set.image_univ]
      exact Or.inr ⟨y, hy, rfl⟩
    · have h0 : constantCoeff (f - C (constantCoeff f)) = 0 := by simp
      refine Ideal.span_mono ?_
        (mvPowerSeries_mem_span_X_of_constantCoeff_eq_zero_of_commRing h0)
      intro x hx
      obtain ⟨y, rfl⟩ := hx
      simp only [Finset.coe_union, Finset.coe_image, Finset.coe_univ, Set.image_univ]
      exact Or.inl ⟨y, rfl⟩
  · rw [Ideal.span_le]
    intro x hx
    simp only [Finset.coe_union, Finset.coe_image, Finset.coe_univ, Set.image_univ,
      Set.mem_union, Set.mem_range, Set.mem_image, Finset.mem_coe] at hx
    rw [SetLike.mem_coe, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
      MvPowerSeries.isUnit_iff_constantCoeff]
    rcases hx with ⟨i, rfl⟩ | ⟨y, hy, rfl⟩
    · simp
    · rw [constantCoeff_C]
      have : y ∈ maximalIdeal S := ht ▸ Ideal.subset_span hy
      exact this

variable [IsNoetherianRing S]

open Classical in
/-- If `t` is a regular system of parameters of `S`, then `(X₁, …, X_n, t)` is a regular system of
parameters of `S⟦X₁, …, X_n⟧`. -/
theorem isRegularSystemOfParameters_mvPowerSeries (n : ℕ) {t : Finset S}
    (ht : IsRegularSystemOfParameters S t) :
    IsRegularSystemOfParameters (MvPowerSeries (Fin n) S)
      (Finset.univ.image (X : Fin n → MvPowerSeries (Fin n) S) ∪
        t.image (C : S →+* MvPowerSeries (Fin n) S)) := by
  refine ⟨(maximalIdeal_mvPowerSeries_eq S n ht.1).symm, ?_⟩
  set t' : Finset (MvPowerSeries (Fin n) S) := Finset.univ.image (X : Fin n → MvPowerSeries (Fin n) S) ∪
        t.image (C : S →+* MvPowerSeries (Fin n) S) with ht'
  have hcard : t'.card ≤ n + t.card := by
    calc t'.card ≤ (Finset.univ.image (X : Fin n → MvPowerSeries (Fin n) S)).card +
          (t.image (C : S →+* MvPowerSeries (Fin n) S)).card := Finset.card_union_le _ _
      _ ≤ n + t.card := by
        refine add_le_add ?_ Finset.card_image_le
        calc (Finset.univ.image (X : Fin n → MvPowerSeries (Fin n) S)).card
            ≤ (Finset.univ : Finset (Fin n)).card := Finset.card_image_le
          _ = n := by simp
  have hup : ringKrullDim (MvPowerSeries (Fin n) S) ≤ (t'.card : WithBot ℕ∞) := by
    have h1 := ringKrullDim_le_spanFinrank_maximalIdeal (MvPowerSeries (Fin n) S)
    have hmax : maximalIdeal (MvPowerSeries (Fin n) S) = Ideal.span (t' : Set _) :=
      maximalIdeal_mvPowerSeries_eq S n ht.1
    rw [hmax] at h1
    have h2 := Submodule.spanFinrank_span_le_ncard_of_finite (R := MvPowerSeries (Fin n) S)
      t'.finite_toSet
    rw [Set.ncard_coe_finset] at h2
    exact h1.trans (by exact_mod_cast h2)
  have hlow : ((n + t.card : ℕ) : WithBot ℕ∞) ≤ ringKrullDim (MvPowerSeries (Fin n) S) := by
    have := ringKrullDim_mvPowerSeries_ge S n
    rw [← ht.2] at this
    push_cast
    rw [add_comm]
    exact this
  exact le_antisymm (le_trans (by exact_mod_cast hcard) hlow) hup

variable {S}

/-- **The power series ring `S⟦X₁, …, X_n⟧` over a regular local ring `S` is a regular local ring**
(used tacitly for `R̃ = S̃{z₁, …, z_r}` on p. 254: "`R̃ = S̃{z₁,…,z_r}`" is the regular local ring of
which `(S̃; z₁, …, z_r)` is a regular frame). -/
theorem _root_.Hironaka.isRegularLocalRing_mvPowerSeries_of_isRegularLocalRing (S : Type u)
    [CommRing S] [IsRegularLocalRing S] (n : ℕ) :
    IsRegularLocalRing (MvPowerSeries (Fin n) S) := by
  classical
  obtain ⟨-, t, ht⟩ := (isRegularLocalRing_iff_exists_rsop S).mp inferInstance
  exact (isRegularLocalRing_iff_exists_rsop _).mpr
    ⟨inferInstance, _, isRegularSystemOfParameters_mvPowerSeries S n ht⟩

end PowerSeriesRegular

/-! ### Regular systems of parameters of a regular frame -/

section FrameRSOP

variable {R : Type u} [CommRing R] [IsRegularLocalRing R] (F : RegularFrame R)

open Classical in
/-- If `t` is a regular system of parameters of the coefficient ring `S` of a regular frame, then
`(z₁, …, z_r, t)` is a regular system of parameters of `R` (`R/(z) ≅ S`), and
`dim R = r + dim S`. -/
theorem RegularFrame.isRegularSystemOfParameters_append {t : Finset F.S}
    (ht : IsRegularSystemOfParameters F.S t) :
    IsRegularSystemOfParameters R (Finset.univ.image F.z ∪ t.image (algebraMap F.S R)) := by
  set T : Finset R := Finset.univ.image F.z ∪ t.image (algebraMap F.S R) with hT
  have hspan : Ideal.span (T : Set R) = maximalIdeal R := by
    rw [F.maximalIdeal_eq_idealZ_sup_map, hT, Finset.coe_union, Ideal.span_union,
      Finset.coe_image, Finset.coe_image, Finset.coe_univ, Set.image_univ, ← ht.1,
      Ideal.map_span]
    rfl
  refine ⟨hspan, le_antisymm ?_ ?_⟩
  · -- `card T ≤ dim R`
    have hcardT : T.card ≤ F.r + t.card := by
      calc T.card ≤ (Finset.univ.image F.z).card + (t.image (algebraMap F.S R)).card :=
            Finset.card_union_le _ _
        _ ≤ F.r + t.card := by
          refine add_le_add ?_ Finset.card_image_le
          calc (Finset.univ.image F.z).card ≤ (Finset.univ : Finset (Fin F.r)).card :=
                Finset.card_image_le
            _ = F.r := by simp
    obtain ⟨s, w, hwN, hNle, -, hdim⟩ := exists_rsop_append F
    have hNspan : Ideal.span (Set.range w) = maximalIdeal F.S :=
      le_antisymm (Ideal.span_le.mpr (by rintro _ ⟨j, rfl⟩; exact hwN j)) hNle
    have hS : (Submodule.spanFinrank (maximalIdeal F.S) : WithBot ℕ∞) = ringKrullDim F.S :=
      IsRegularLocalRing.spanFinrank_maximalIdeal
    have hsr : Submodule.spanFinrank (maximalIdeal F.S) ≤ s := by
      have := Submodule.spanFinrank_span_le_ncard_of_finite (R := F.S) (Set.finite_range w)
      rw [show Submodule.span F.S (Set.range w) = maximalIdeal F.S from hNspan] at this
      refine this.trans ?_
      calc (Set.range w).ncard ≤ (Set.univ : Set (Fin s)).ncard := by
            rw [← Set.image_univ]; exact Set.ncard_image_le Set.finite_univ
        _ = s := by simp [Set.ncard_univ]
    calc (T.card : WithBot ℕ∞) ≤ ((F.r + t.card : ℕ) : WithBot ℕ∞) := by exact_mod_cast hcardT
      _ = F.r + ringKrullDim F.S := by rw [Nat.cast_add, ht.2]
      _ = F.r + (Submodule.spanFinrank (maximalIdeal F.S) : WithBot ℕ∞) := by rw [hS]
      _ ≤ ((F.r + s : ℕ) : WithBot ℕ∞) := by exact_mod_cast Nat.add_le_add_left hsr _
      _ = ringKrullDim R := hdim
  · -- `dim R ≤ card T`
    have h1 := ringKrullDim_le_spanFinrank_maximalIdeal R
    rw [← hspan] at h1
    have h2 := Submodule.spanFinrank_span_le_ncard_of_finite (R := R) T.finite_toSet
    rw [Set.ncard_coe_finset] at h2
    exact h1.trans (by exact_mod_cast h2)

end FrameRSOP

/-! ### The frame `(S; X₁, …, X_r)` of `S⟦X₁, …, X_r⟧` -/

section PowerSeriesFrame

open MvPowerSeries

/-- `S⟦X₁, …, X_n⟧` is a regular local ring when `S` is (`R̃ = S̃{z₁, …, z_r}`, p. 254). -/
instance instIsRegularLocalRingMvPowerSeries (S : Type u) [CommRing S] [IsRegularLocalRing S]
    (n : ℕ) : IsRegularLocalRing (MvPowerSeries (Fin n) S) :=
  isRegularLocalRing_mvPowerSeries_of_isRegularLocalRing S n

variable (S : Type u) [CommRing S] [IsRegularLocalRing S] (r : ℕ)

omit [IsRegularLocalRing S] in
theorem algebraMap_mvPowerSeries_eq_C (a : S) :
    algebraMap S (MvPowerSeries (Fin r) S) a = C a := by
  rw [MvPowerSeries.algebraMap_apply]
  rfl

instance : IsLocalHom (algebraMap S (MvPowerSeries (Fin r) S)) where
  map_nonunit a ha := by
    rw [MvPowerSeries.isUnit_iff_constantCoeff, algebraMap_mvPowerSeries_eq_C] at ha
    simpa using ha

theorem X_injective_mvPowerSeries : Function.Injective (X : Fin r → MvPowerSeries (Fin r) S) := by
  classical
  intro a b h
  by_contra hab
  have h1 := congrArg (coeff (Finsupp.single a 1)) h
  rw [coeff_X, coeff_X] at h1
  simp [Finsupp.single_left_inj one_ne_zero, hab] at h1

open Classical in
/-- **The regular frame `(S; X₁, …, X_r)` of `S⟦X₁, …, X_r⟧`**: `R̃ = S̃{z₁, …, z_r}` of p. 254. -/
noncomputable def RegularFrame.mvPowerSeries : RegularFrame (MvPowerSeries (Fin r) S) where
  S := S
  r := r
  z := fun j => X j
  z_injective := X_injective_mvPowerSeries S r
  extends_rsop := by
    obtain ⟨-, t, ht⟩ := (isRegularLocalRing_iff_exists_rsop S).mp inferInstance
    exact ⟨_, Finset.subset_union_left, isRegularSystemOfParameters_mvPowerSeries S r ht⟩
  quot_bijective := by
    have hker : Ideal.span (Set.range (X : Fin r → MvPowerSeries (Fin r) S)) ≤
        RingHom.ker (constantCoeff (σ := Fin r) (R := S)) :=
      Ideal.span_le.mpr (by rintro _ ⟨i, rfl⟩; simp)
    refine ⟨fun a b hab => ?_, fun q => ?_⟩
    · have h : algebraMap S (MvPowerSeries (Fin r) S) a - algebraMap S (MvPowerSeries (Fin r) S) b ∈
          Ideal.span (Set.range (X : Fin r → MvPowerSeries (Fin r) S)) := by
        rw [← Ideal.Quotient.eq]
        exact hab
      have := RingHom.mem_ker.mp (hker h)
      rw [map_sub, algebraMap_mvPowerSeries_eq_C, algebraMap_mvPowerSeries_eq_C, constantCoeff_C,
        constantCoeff_C, sub_eq_zero] at this
      exact this
    · obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective q
      refine ⟨constantCoeff f, ?_⟩
      rw [RingHom.comp_apply, Ideal.Quotient.eq]
      have h0 : constantCoeff (f - C (constantCoeff f)) = 0 := by simp
      have := mvPowerSeries_mem_span_X_of_constantCoeff_eq_zero_of_commRing h0
      rw [algebraMap_mvPowerSeries_eq_C, ← neg_sub]
      exact Ideal.neg_mem_iff _ |>.mpr this

end PowerSeriesFrame

/-! ### Base change of a regular frame: `R → S̃{z₁, …, z_r}` (p. 254) -/

section FrameBaseChange

open MvPowerSeries

variable {R : Type u} [CommRing R] [IsRegularLocalRing R] (F : RegularFrame R)
  {S' : Type u} [CommRing S'] [IsRegularLocalRing S'] (a : F.S →+* S')

/-- **The canonical homomorphism `R → S̃{z₁, …, z_r}`** (p. 254: "Then `S → S̃` induces in a
canonical manner a local homomorphism `R → S̃{z₁,…,z_r}`"): the power series expansion of `R` in
`S{z₁, …, z_r}` followed by the coefficientwise map `S → S̃`. -/
noncomputable def RegularFrame.baseChangeHom : R →+* MvPowerSeries (Fin F.r) S' :=
  (MvPowerSeries.map a).comp F.expansion

omit [IsRegularLocalRing S'] in
theorem RegularFrame.baseChangeHom_algebraMap (s : F.S) :
    F.baseChangeHom a (algebraMap F.S R s) = C (a s) := by
  show MvPowerSeries.map a (F.expansion (algebraMap F.S R s)) = _
  rw [(isExpansion_expansion F).map_algebraMap, MvPowerSeries.map_C]

omit [IsRegularLocalRing S'] in
theorem RegularFrame.baseChangeHom_z (j : Fin F.r) : F.baseChangeHom a (F.z j) = X j := by
  show MvPowerSeries.map a (F.expansion (F.z j)) = _
  rw [(isExpansion_expansion F).map_z, MvPowerSeries.map_X]

omit [IsRegularLocalRing S'] in
theorem RegularFrame.coeff_baseChangeHom (g : R) (A : Fin F.r →₀ ℕ) :
    coeff A (F.baseChangeHom a g) = a (F.expCoeff g A) := by
  show coeff A (MvPowerSeries.map a (F.expansion g)) = _
  rw [MvPowerSeries.coeff_map]
  rfl

/-- The identity is the expansion map of the frame `(S; X₁, …, X_r)` of `S⟦X₁, …, X_r⟧`. -/
theorem RegularFrame.isExpansion_mvPowerSeries_id (S : Type u) [CommRing S] [IsRegularLocalRing S]
    (r : ℕ) : (RegularFrame.mvPowerSeries S r).IsExpansion (RingHom.id (MvPowerSeries (Fin r) S)) where
  map_algebraMap s := algebraMap_mvPowerSeries_eq_C S r s
  map_z _ := rfl
  map_pow _ _ hx := hx

/-- The expansion coefficients in `S⟦X₁, …, X_r⟧` are its coefficients. -/
theorem RegularFrame.expCoeff_mvPowerSeries (S : Type u) [CommRing S] [IsRegularLocalRing S]
    (r : ℕ) (g : MvPowerSeries (Fin r) S) (A : Fin r →₀ ℕ) :
    (RegularFrame.mvPowerSeries S r).expCoeff g A = coeff A g := by
  have h := isExpansion_unique_aux (RegularFrame.mvPowerSeries S r)
    (isExpansion_expansion (RegularFrame.mvPowerSeries S r))
    (RegularFrame.isExpansion_mvPowerSeries_id S r)
  have h2 := coeff_expansion (RegularFrame.mvPowerSeries S r) g A
  rw [h] at h2
  exact h2.symm

/-- The expansion coefficients of `ι(g)` in `S̃{z}` are the images of those of `g`. -/
theorem RegularFrame.expCoeff_baseChangeHom (g : R) (A : Fin F.r →₀ ℕ) :
    (RegularFrame.mvPowerSeries S' F.r).expCoeff (F.baseChangeHom a g) A =
      a (F.expCoeff g A) := by
  rw [RegularFrame.expCoeff_mvPowerSeries, F.coeff_baseChangeHom]

/-- The constant coefficient of the expansion is the retraction `R → S`. -/
theorem RegularFrame.constantCoeff_expansion (g : R) :
    MvPowerSeries.constantCoeff (F.expansion g) = F.retraction g := by
  have hker : F.idealZ ≤ RingHom.ker ((MvPowerSeries.constantCoeff (σ := Fin F.r) (R := F.S)).comp
      F.expansion) := by
    rw [RegularFrame.idealZ, Ideal.span_le]
    rintro _ ⟨j, rfl⟩
    rw [SetLike.mem_coe, RingHom.mem_ker, RingHom.comp_apply,
      (isExpansion_expansion F).map_z]
    simp
  have h1 := hker (F.sub_algebraMap_retraction_mem g)
  simp only [RingHom.mem_ker, RingHom.comp_apply, map_sub] at h1
  rw [sub_eq_zero] at h1
  rw [h1, (isExpansion_expansion F).map_algebraMap]
  simp

/-- `ι : R → S̃{z}` is a local homomorphism. -/
instance RegularFrame.isLocalHom_baseChangeHom [IsLocalHom a] :
    IsLocalHom (F.baseChangeHom a) where
  map_nonunit g hg := by
    rw [MvPowerSeries.isUnit_iff_constantCoeff] at hg
    have h1 : MvPowerSeries.constantCoeff (F.baseChangeHom a g) = a (F.retraction g) := by
      show MvPowerSeries.constantCoeff (MvPowerSeries.map a (F.expansion g)) = _
      rw [MvPowerSeries.constantCoeff_map, F.constantCoeff_expansion]
    rw [h1] at hg
    have h2 : IsUnit (F.retraction g) := isUnit_of_map_unit a _ hg
    by_contra hng
    have hgM : g ∈ maximalIdeal R := hng
    have hzM : F.idealZ ≤ maximalIdeal R := by
      rw [F.maximalIdeal_eq_idealZ_sup_map]
      exact le_sup_left
    have h3 := F.retraction_mem_comap hzM hgM
    have h4 : F.retraction g ∈ maximalIdeal F.S :=
      (algebraMap_mem_maximalIdeal_iff_aux F _).mp h3
    exact (IsLocalRing.mem_maximalIdeal _).mp h4 h2

open Classical in
/-- The regular system of parameters `(X₁, …, X_n, t)` of `S⟦X₁, …, X_n⟧` has `n + #t` elements. -/
theorem card_mvPowerSeries_rsop (S : Type u) [CommRing S] [IsRegularLocalRing S] (n : ℕ)
    {t : Finset S} (ht : IsRegularSystemOfParameters S t) :
    (Finset.univ.image (MvPowerSeries.X : Fin n → MvPowerSeries (Fin n) S) ∪
      t.image (MvPowerSeries.C : S →+* MvPowerSeries (Fin n) S)).card = n + t.card := by
  have h := (isRegularSystemOfParameters_mvPowerSeries S n ht).2
  have hlow := ringKrullDim_mvPowerSeries_ge S n
  rw [← ht.2] at hlow
  have hle : (Finset.univ.image (MvPowerSeries.X : Fin n → MvPowerSeries (Fin n) S) ∪
      t.image (MvPowerSeries.C : S →+* MvPowerSeries (Fin n) S)).card ≤ n + t.card := by
    calc _ ≤ (Finset.univ.image (MvPowerSeries.X : Fin n → MvPowerSeries (Fin n) S)).card +
          (t.image (MvPowerSeries.C : S →+* MvPowerSeries (Fin n) S)).card :=
            Finset.card_union_le _ _
      _ ≤ n + t.card := by
        refine add_le_add ?_ Finset.card_image_le
        calc _ ≤ (Finset.univ : Finset (Fin n)).card := Finset.card_image_le
          _ = n := by simp
  have hge : n + t.card ≤ (Finset.univ.image (MvPowerSeries.X : Fin n → MvPowerSeries (Fin n) S) ∪
      t.image (MvPowerSeries.C : S →+* MvPowerSeries (Fin n) S)).card := by
    have : ((n + t.card : ℕ) : WithBot ℕ∞) ≤ ringKrullDim (MvPowerSeries (Fin n) S) := by
      push_cast
      rw [add_comm]
      exact hlow
    rw [← h] at this
    exact_mod_cast this
  exact le_antisymm hle hge

open Classical in
/-- `R → S̃{z}` transforms a regular system of parameters of `R` into one of `S̃{z}` when
`S → S̃` does so for `S` (p. 254: "which also has the same properties as `S → S̃`"). -/
theorem RegularFrame.mapsRSOP_baseChangeHom [IsLocalHom a] (ha : RingHom.MapsRSOP a) :
    RingHom.MapsRSOP (F.baseChangeHom a) := by
  obtain ⟨t, ht, ht', hinj⟩ := ha
  set T : Finset R := Finset.univ.image F.z ∪ t.image (algebraMap F.S R) with hT
  have hTrsop : IsRegularSystemOfParameters R T := F.isRegularSystemOfParameters_append ht
  have himg : T.image (F.baseChangeHom a) =
      Finset.univ.image (MvPowerSeries.X : Fin F.r → MvPowerSeries (Fin F.r) S') ∪
        (t.image a).image (MvPowerSeries.C : S' →+* MvPowerSeries (Fin F.r) S') := by
    rw [hT, Finset.image_union, Finset.image_image, Finset.image_image, Finset.image_image]
    congr 1
    · exact Finset.image_congr fun j _ => F.baseChangeHom_z a j
    · exact Finset.image_congr fun s _ => F.baseChangeHom_algebraMap a s
  have hrsop' := isRegularSystemOfParameters_mvPowerSeries S' F.r ht'
  have hcard := card_mvPowerSeries_rsop S' F.r ht'
  have hcardt : (t.image a).card = t.card := Finset.card_image_of_injOn hinj
  have hTcard : T.card ≤ F.r + t.card := by
    calc T.card ≤ (Finset.univ.image F.z).card + (t.image (algebraMap F.S R)).card :=
          Finset.card_union_le _ _
      _ ≤ F.r + t.card := by
        refine add_le_add ?_ Finset.card_image_le
        calc _ ≤ (Finset.univ : Finset (Fin F.r)).card := Finset.card_image_le
          _ = F.r := by simp
  refine ⟨T, hTrsop, himg ▸ hrsop', Finset.injOn_of_card_image_eq ?_⟩
  have h1 := Finset.card_image_le (s := T) (f := F.baseChangeHom a)
  rw [himg, hcard, hcardt] at h1
  rw [himg, hcard, hcardt]
  omega

/-- `R/M = S/N` for a regular frame: the residue map of the structure map `S → R` is bijective
(Definition 9(1), p. 248: `R/(z)R ≅ S` and `(z) ⊆ M`). -/
theorem RegularFrame.residueField_map_algebraMap_bijective :
    Function.Bijective (ResidueField.map (algebraMap F.S R)) := by
  refine ⟨(ResidueField.map (algebraMap F.S R)).injective, fun y => ?_⟩
  obtain ⟨r, rfl⟩ := IsLocalRing.residue_surjective y
  refine ⟨IsLocalRing.residue F.S (F.retraction r), ?_⟩
  rw [ResidueField.map_residue, ← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff]
  have hzM : F.idealZ ≤ maximalIdeal R := by
    rw [F.maximalIdeal_eq_idealZ_sup_map]
    exact le_sup_left
  have h := neg_mem (hzM (F.sub_algebraMap_retraction_mem r))
  simpa using h

/-- `R → S̃{z}` is residually separable algebraic when `S → S̃` is (p. 254: "which also has the
same properties as `S → S̃`"). -/
theorem RegularFrame.isResiduallySeparableAlgebraic_baseChangeHom [IsLocalHom a]
    (hsep : RingHom.IsResiduallySeparableAlgebraic a) :
    RingHom.IsResiduallySeparableAlgebraic (F.baseChangeHom a) := by
  let _ : Algebra (ResidueField F.S) (ResidueField S') := (ResidueField.map a).toAlgebra
  have _ : Algebra.IsSeparable (ResidueField F.S) (ResidueField S') := hsep
  let G := RegularFrame.mvPowerSeries S' F.r
  let e₁ : ResidueField F.S ≃+* ResidueField R :=
    RingEquiv.ofBijective _ F.residueField_map_algebraMap_bijective
  let e₂ : ResidueField S' ≃+* ResidueField (MvPowerSeries (Fin F.r) S') :=
    RingEquiv.ofBijective (ResidueField.map (algebraMap S' (MvPowerSeries (Fin F.r) S')))
      G.residueField_map_algebraMap_bijective
  let _ : Algebra (ResidueField R) (ResidueField (MvPowerSeries (Fin F.r) S')) :=
    (ResidueField.map (F.baseChangeHom a)).toAlgebra
  show Algebra.IsSeparable (ResidueField R) (ResidueField (MvPowerSeries (Fin F.r) S'))
  refine Algebra.IsSeparable.of_equiv_equiv e₁ e₂ (RingHom.ext fun x => ?_)
  obtain ⟨s, rfl⟩ := IsLocalRing.residue_surjective x
  simp only [RingHom.coe_comp, Function.comp_apply, RingHom.algebraMap_toAlgebra,
    RingEquiv.coe_toRingHom, e₁, e₂, RingEquiv.ofBijective_apply, ResidueField.map_residue]
  rw [F.baseChangeHom_algebraMap a s]
  show _ = ResidueField.map (algebraMap S' (MvPowerSeries (Fin F.r) S')) (residue S' (a s))
  rw [ResidueField.map_residue, algebraMap_mvPowerSeries_eq_C]

end FrameBaseChange

section Complete

open MvPowerSeries

theorem sModEq_pow_iff {A : Type*} [CommRing A] (I : Ideal A) (n : ℕ) (x y : A) :
    x ≡ y [SMOD (I ^ n • ⊤ : Submodule A A)] ↔ x - y ∈ I ^ n := by
  rw [SModEq.sub_mem]
  simp [Ideal.mul_top]

/-- `S⟦X₁, …, X_n⟧` is adically complete for its maximal ideal when `S` is complete for its
maximal ideal (`R̃ = S̃{z₁, …, z_r}` is complete, p. 254). -/
theorem isAdicComplete_maximalIdeal_mvPowerSeries_of_isAdicComplete (S : Type u) [CommRing S]
    [IsRegularLocalRing S] [h : IsAdicComplete (maximalIdeal S) S] (n : ℕ) :
    IsAdicComplete (maximalIdeal (MvPowerSeries (Fin n) S)) (MvPowerSeries (Fin n) S) := by
  classical
  let G := RegularFrame.mvPowerSeries S n
  have hmem : ∀ (d : ℕ) (g : MvPowerSeries (Fin n) S),
      g ∈ maximalIdeal (MvPowerSeries (Fin n) S) ^ d ↔
        ∀ A : Fin n →₀ ℕ, A.degree ≤ d → coeff A g ∈ maximalIdeal S ^ (d - A.degree) := by
    intro d g
    exact G.mem_maximalIdeal_pow_iff_coeff_mem_pow (RegularFrame.isExpansion_mvPowerSeries_id S n)
      d g
  refine
    { haus' := fun x hx => ?_
      prec' := fun f hf => ?_ }
  · -- Hausdorff
    ext A
    have hA : ∀ k : ℕ, coeff A x ∈ maximalIdeal S ^ k := fun k => by
      have h1 := (sModEq_pow_iff _ (k + A.degree) x 0).mp (hx (k + A.degree))
      rw [sub_zero] at h1
      have := (hmem _ x).mp h1 A (by omega)
      rwa [show k + A.degree - A.degree = k by omega] at this
    have h2 := h.1.haus' (coeff A x) fun k => (sModEq_pow_iff _ k _ 0).mpr (by
      rw [sub_zero]; exact hA k)
    rw [h2]
    simp
  · -- precomplete: coefficientwise limits
    have hf' : ∀ {m k : ℕ}, m ≤ k → ∀ A : Fin n →₀ ℕ, A.degree ≤ m →
        coeff A (f m) - coeff A (f k) ∈ maximalIdeal S ^ (m - A.degree) := by
      intro m k hmk A hA
      have h1 := (sModEq_pow_iff _ m _ _).mp (hf hmk)
      have := (hmem m _).mp h1 A hA
      simpa using this
    have hlim : ∀ A : Fin n →₀ ℕ, ∃ L : S, ∀ j : ℕ,
        coeff A (f (j + A.degree)) - L ∈ maximalIdeal S ^ j := by
      intro A
      obtain ⟨L, hL⟩ := h.2.prec' (fun j => coeff A (f (j + A.degree))) (fun {m k} hmk => by
        refine (sModEq_pow_iff _ m _ _).mpr ?_
        have := hf' (m := m + A.degree) (k := k + A.degree) (by omega) A (by omega)
        simpa using this)
      exact ⟨L, fun j => (sModEq_pow_iff _ j _ _).mp (hL j)⟩
    choose L hL using hlim
    refine ⟨(L : MvPowerSeries (Fin n) S), fun N => ?_⟩
    refine (sModEq_pow_iff _ N _ _).mpr ((hmem N _).mpr fun A hA => ?_)
    have := hL A (N - A.degree)
    rw [show N - A.degree + A.degree = N by omega] at this
    exact this

end Complete

/-! ### Localization at a prime not containing the defining element -/

section LocalizationBijective

/-- For a monoidal transform `R'` of `R` (centre `Q`, element `x`) and a prime `P'` of `R'` over a prime
`P` of `R` with `x ∉ P`, the canonical map `R_P → R'_{P'}` is bijective: `R' ⊆ R[1/x] ⊆ R_P` inside
the field of quotients.  (The case `Q = M` is `MonoidalTransform.localRingHom_bijective_of_x_notMem`
of `Ch3/StabilityCor3c.lean`; the proof is the same for any centre.) -/
theorem MonoidalTransform.bijective_localRingHom_of_x_notMem {R : Type u} [CommRing R]
    [IsRegularLocalRing R] [IsDomain R] {Q : Ideal R} (t : MonoidalTransform R Q) (P : Ideal R)
    [P.IsPrime] (P' : Ideal t.ring)
    [P'.IsPrime] (hP' : P = P'.comap t.toRing) (hxP : t.x ∉ P) :
    Function.Bijective (Localization.localRingHom P P' t.toRing hP') := by
  have hxM : t.x ∈ Q := t.x_mem
  set f := Localization.localRingHom P P' t.toRing hP'
  set T := Localization.AtPrime P'
  let A := blowupAlgebra R Q t.x
  set α := algebraMap t.ring T
  let β : A →+* T := α.comp (algebraMap A t.ring)
  have hxpow : ∀ m, t.x ^ m ∈ P.primeCompl := fun m h =>
    hxP (Ideal.IsPrime.mem_of_pow_mem ‹_› m h)
  -- every `b = g/xᵐ ∈ A` comes from `R_P`
  have hβ : ∀ b : A, ∃ y, f y = β b := by
    intro b
    obtain ⟨m, g, -, hbg⟩ :=
      MonoidalTransform.exists_mul_pow_eq_of_mem_blowupAlgebra hxM t.x_ne_zero b.2
    refine ⟨IsLocalization.mk' _ g ⟨t.x ^ m, hxpow m⟩, ?_⟩
    rw [Localization.localRingHom_mk', IsLocalization.mk'_eq_iff_eq_mul]
    have hA : b * algebraMap R A (t.x ^ m) = algebraMap R A g :=
      Subtype.ext (by simpa [map_pow] using hbg)
    show α (algebraMap A t.ring (algebraMap R A g)) =
      β b * α (algebraMap A t.ring (algebraMap R A (t.x ^ m)))
    rw [← hA, map_mul, map_mul]
    rfl
  -- and so do the inverses of the units among them (`f` is local)
  have hβinv : ∀ b : A, IsUnit (β b) → ∃ y, f y * β b = 1 := by
    intro b hb
    obtain ⟨y, hy⟩ := hβ b
    have hyu : IsUnit y := isUnit_of_map_unit f y (hy ▸ hb)
    refine ⟨↑hyu.unit⁻¹, ?_⟩
    rw [← hy, ← map_mul, hyu.val_inv_mul, map_one]
  refine ⟨?_, ?_⟩
  · rw [injective_iff_map_eq_zero]
    intro z hz
    obtain ⟨r, s, rfl⟩ := IsLocalization.exists_mk'_eq P.primeCompl z
    rw [Localization.localRingHom_mk', IsLocalization.mk'_eq_zero_iff] at hz
    obtain ⟨c, hc⟩ := hz
    have hc0 : (c : t.ring) ≠ 0 := fun h0 => c.2 (by rw [h0]; exact zero_mem _)
    have hr : t.toRing r = 0 := (mul_eq_zero.mp hc).resolve_left hc0
    have : r = 0 := t.toRing_injective (by rw [hr, map_zero])
    rw [this, IsLocalization.mk'_zero]
  · intro z
    obtain ⟨a, s, rfl⟩ := IsLocalization.exists_mk'_eq P'.primeCompl z
    obtain ⟨b, u, rfl⟩ := IsLocalization.exists_mk'_eq t.M'.primeCompl a
    obtain ⟨c, w, hcw⟩ := IsLocalization.exists_mk'_eq t.M'.primeCompl (s : t.ring)
    have h1 : α (IsLocalization.mk' t.ring b u) * β u = β b := by
      show α _ * α (algebraMap A t.ring u) = α (algebraMap A t.ring b)
      rw [← map_mul, IsLocalization.mk'_spec]
    have h2 : α s * β w = β c := by
      show α _ * α (algebraMap A t.ring w) = α (algebraMap A t.ring c)
      rw [← hcw, ← map_mul, IsLocalization.mk'_spec]
    have hβu : IsUnit (β u) := (IsLocalization.map_units t.ring u).map α
    have hβc : IsUnit (β c) := by
      rw [← h2]
      exact (IsLocalization.map_units T s).mul ((IsLocalization.map_units t.ring w).map α)
    obtain ⟨yb, hyb⟩ := hβ b
    obtain ⟨yw, hyw⟩ := hβ w
    obtain ⟨yc, hyc⟩ := hβinv c hβc
    obtain ⟨yu, hyu⟩ := hβinv u hβu
    refine ⟨yb * yw * yc * yu, ?_⟩
    rw [map_mul, map_mul, map_mul, hyb, hyw, eq_comm, IsLocalization.mk'_eq_iff_eq_mul]
    linear_combination (-(α (IsLocalization.mk' t.ring b u))) * hyu + f yu * h1 -
      (β b * f yu) * hyc - (β b * f yu * f yc) * h2

end LocalizationBijective

/-! ### Transfer along a local homomorphism that transforms a regular system of parameters

Everything in this section is stated for an *arbitrary* local homomorphism `α : R → R̄` that
transforms a regular system of parameters of `R` into one of `R̄` and whose residue field extension
is separable algebraic, exactly as in the first sentence of the proof of Lemma 20 (p. 254): "Let
`S → S̃` be any local homomorphism such that a regular system of parameters of `S` is transformed
into such a system of parameters of `S̃` and that the residue field of `S̃` is separable algebraic
over that of `S`." -/

section Lift

variable {R R' : Type u} [CommRing R] [IsRegularLocalRing R] [IsDomain R] [CommRing R']
  [IsRegularLocalRing R'] [IsDomain R'] (α : R →+* R') [IsLocalHom α]

/-- **The canonical lift of a monoidal transform** (p. 254: "`R₁` by a monoidal transform `R̃₁` of
`R̃` with centre `PR̃` which admits a canonical local homomorphism `R₁ → R̃₁`"; p. 211, Lemma 4):
a monoidal transform `T'` of `R'` with centre `PR'` and a canonical local homomorphism
`β : T.ring → T'.ring`. -/
structure BaseChangeLift {P : Ideal R} (T : MonoidalTransform R P) where
  /-- The monoidal transform `R̃₁` of `R̃` with centre `PR̃`. -/
  T' : MonoidalTransform R' (P.map α)
  /-- The canonical homomorphism `R₁ → R̃₁`. -/
  β : T.ring →+* T'.ring
  /-- `β` is canonical (p. 211). -/
  isCanonicalLift : IsCanonicalLift α T T' β

namespace BaseChangeLift

variable {α} {P : Ideal R} {T : MonoidalTransform R P} (L : BaseChangeLift α T)

/-- The canonical homomorphism `β : R₁ → R̃₁` is local. -/
instance isLocalHom_β : IsLocalHom L.β := L.isCanonicalLift.isLocalHom

/-- Existence of the canonical lift (Lemma 4 (1), the existence half; `exists_isCanonicalLift`). -/
theorem nonempty (hα : RingHom.MapsRSOP α) (T : MonoidalTransform R P) :
    Nonempty (BaseChangeLift α T) := by
  obtain ⟨T', β, h⟩ := exists_isCanonicalLift α hα T
  exact ⟨⟨T', β, h⟩⟩

section Properties

variable [P.IsPrime] [IsRegularLocalRing (R ⧸ P)] (hα : RingHom.MapsRSOP α)
  [IsLocalHom T.toRing] [IsRegularLocalRing T.ring]

include hα

omit [IsLocalHom T.toRing] [IsRegularLocalRing T.ring] in
/-- `R̃₁` is a regular local ring. -/
theorem isRegularLocalRing : IsRegularLocalRing L.T'.ring := by
  obtain ⟨⟨hP', hS'⟩, -⟩ := RingHom.MapsRSOP.canonicalLift_properties α hα
    (inferInstance : P.IsPrime) inferInstance
  have hP'0 : P.map α ≠ ⊥ := fun h =>
    L.T'.x_ne_zero (Ideal.mem_bot.mp (h.le L.T'.x_mem))
  exact (MonoidalTransform.isRegularLocalRing_and_isLocalHom_and_span_xR_eq_map L.T' hP' hP'0
    hS').1

omit [IsLocalHom α] [P.IsPrime] [IsRegularLocalRing (R ⧸ P)] hα [IsLocalHom T.toRing] [IsRegularLocalRing T.ring] in
/-- `R̃ → R̃₁` is a local homomorphism. -/
theorem isLocalHom_toRing : IsLocalHom L.T'.toRing := inferInstance

omit [IsLocalHom T.toRing] [IsRegularLocalRing T.ring] in
/-- `β : R₁ → R̃₁` is injective. -/
theorem injective_β : Function.Injective L.β := by
  obtain ⟨-, -, h2, -⟩ := RingHom.MapsRSOP.canonicalLift_properties α hα
    (inferInstance : P.IsPrime) inferInstance
  exact (h2 T L.T' L.β L.isCanonicalLift).2.2.2.1

variable (hsep : RingHom.IsResiduallySeparableAlgebraic α)

include hsep

omit [IsLocalHom T.toRing] in
/-- Lemma 4 (3): if `α` is residually separable algebraic, `β : R₁ → R̃₁` transforms a regular
system of parameters of `R₁` into one of `R̃₁`; hence it is flat, and faithfully flat. -/
theorem mapsRSOP_β : RingHom.MapsRSOP L.β := by
  obtain ⟨-, -, h2, h3⟩ := RingHom.MapsRSOP.canonicalLift_properties α hα
    (inferInstance : P.IsPrime) inferInstance
  obtain ⟨-, s, hs⟩ := (isRegularLocalRing_iff_exists_rsop T.ring).mp inferInstance
  exact ⟨s, hs, (h3 T L.T' L.β L.isCanonicalLift).2 hsep s hs,
    (h2 T L.T' L.β L.isCanonicalLift).2.2.2.1.injOn⟩

omit [IsRegularLocalRing T.ring] in
/-- The residue field extension of `β` is separable algebraic. -/
theorem isResiduallySeparableAlgebraic_β : RingHom.IsResiduallySeparableAlgebraic L.β := by
  obtain ⟨-, -, h2, -⟩ := RingHom.MapsRSOP.canonicalLift_properties α hα
    (inferInstance : P.IsPrime) inferInstance
  exact isResiduallySeparableAlgebraic_of_closure_eq_top α T.toRing L.T'.toRing L.β
    L.isCanonicalLift.comm hsep (h2 T L.T' L.β L.isCanonicalLift).2.2.2.2

omit hsep in
/-- **Strict transform and base change** (Corollary to Lemma 5 of §2, Remark 3): `J₁R̃₁` is the
strict transform of `JR̃` in `R̃₁`. -/
theorem strictTransformIdeal_map [Hironaka.Cited.IsSeparableFieldExtensionIff.{u}] (J : Ideal R) (hJP : J ≤ P) :
    haveI := L.isRegularLocalRing hα
    strictTransformIdeal L.T' (J.map α) = (strictTransformIdeal T J).map L.β := by
  obtain ⟨⟨hP', hS'⟩, -⟩ := RingHom.MapsRSOP.canonicalLift_properties α hα
    (inferInstance : P.IsPrime) inferInstance
  have _ := hP'
  have _ := L.isRegularLocalRing hα
  have _ := L.isLocalHom_toRing
  exact (strictTransform_map_of_mapsRSOP α hα J P hJP T L.T' L.β
    L.isCanonicalLift.comm).1

/-- `ν*` of the strict transform does not change (Corollary to Lemma 2, applied to `β`). -/
theorem nuStar_strictTransformIdeal [Hironaka.Cited.IsSeparableFieldExtensionIff.{u}] (J : Ideal R) (hJP : J ≤ P) :
    haveI := L.isRegularLocalRing hα
    nuStar L.T'.ring (strictTransformIdeal L.T' (J.map α)) =
      nuStar T.ring (strictTransformIdeal T J) := by
  have _ := L.isRegularLocalRing hα
  rw [L.strictTransformIdeal_map hα J hJP]
  exact (nuStar_map_eq_of_mapsRSOP L.β (L.mapsRSOP_β hα hsep) _).symm

/-- `ν^{(i)}` of the strict transform does not change. -/
theorem nuI_strictTransformIdeal [Hironaka.Cited.IsSeparableFieldExtensionIff.{u}] (J : Ideal R) (hJP : J ≤ P) (i : ℕ+) :
    haveI := L.isRegularLocalRing hα
    nuI L.T'.ring (strictTransformIdeal L.T' (J.map α)) i =
      nuI T.ring (strictTransformIdeal T J) i := by
  have _ := L.isRegularLocalRing hα
  rw [L.strictTransformIdeal_map hα J hJP]
  exact (nuI_map_eq_of_mapsRSOP L.β (L.mapsRSOP_β hα hsep) _ i).symm

omit [IsLocalHom T.toRing] in
/-- `P₁` is a permissible centre for `J₁` iff `P₁R̃₁` is one for `J₁R̃₁` (faithfully flat descent
along `β`, `isPermissibleCenter_map_iff`). -/
theorem isPermissibleCenter_map_iff_β (J₁ P₁ : Ideal T.ring) [P₁.IsPrime] (hJP : J₁ ≤ P₁) :
    haveI := L.isRegularLocalRing hα
    IsPermissibleCenter T.ring J₁ P₁ ↔
      IsPermissibleCenter L.T'.ring (J₁.map L.β) (P₁.map L.β) := by
  have _ := L.isRegularLocalRing hα
  exact (Hironaka.isPermissibleCenter_map_iff L.β (L.mapsRSOP_β hα hsep) J₁ P₁ hJP).2.2.2

omit hsep in
omit [IsRegularLocalRing T.ring] in
/-- If `T` is residually separable algebraic over `R` and the residue field of `R̃` is separably
closed, then `T'` is residually rational over `R̃` (p. 254: "so that `R₁` is residually rational
over `R`"; the residue field of `R̃₁` is generated by those of `R₁` and `R̃`, Lemma 4 (2)). -/
theorem isResiduallyRational (hsc : IsSepClosed (ResidueField R'))
    (hsepT : RingHom.IsResiduallySeparableAlgebraic (R := R) (R' := T.ring) T.toRing) :
    haveI := L.isRegularLocalRing hα
    RingHom.IsResiduallyRational (R := R') (R' := L.T'.ring) L.T'.toRing := by
  have _ := L.isRegularLocalRing hα
  have _ := L.isLocalHom_toRing
  obtain ⟨-, -, h2, -⟩ := RingHom.MapsRSOP.canonicalLift_properties α hα
    (inferInstance : P.IsPrime) inferInstance
  have hsepT' := isResiduallySeparableAlgebraic_of_closure_eq_top T.toRing α L.β L.T'.toRing
    L.isCanonicalLift.comm.symm hsepT
    (by rw [Set.union_comm]; exact (h2 T L.T' L.β L.isCanonicalLift).2.2.2.2)
  let _ : Algebra (ResidueField R') (ResidueField L.T'.ring) :=
    (ResidueField.map L.T'.toRing).toAlgebra
  have _ : Algebra.IsSeparable (ResidueField R') (ResidueField L.T'.ring) := hsepT'
  have _ := hsc
  exact IsSepClosed.algebraMap_surjective (ResidueField R') (ResidueField L.T'.ring)

omit [IsLocalHom T.toRing] in
/-- **A prime of `R̃₁` over `P₁`** (the primes `P̃`, `P̃₁` of the reduction of Proposition 2, p. 258,
which the paper does not construct): for a prime `P₁` of `R₁` such that `x ∉ P₁` (`x` the defining
element of the monoidal transform `T`), `R/(P₁ ∩ R)` regular and `P₁R̃₁` prime, the contraction of
`P₁R̃₁` to `R̃` is `(P₁ ∩ R)R̃`.  (Both `R_{P₁ ∩ R} → (R₁)_{P₁}` and
`R̃_{p̄} → (R̃₁)_{P₁R̃₁}` are bijective, `x` being a unit, and the maximal ideal of the first is
extended from `R`.) -/
theorem comap_map_β_eq (P₁ : Ideal T.ring) [P₁.IsPrime] [(P₁.map L.β).IsPrime]
    [IsRegularLocalRing (R ⧸ P₁.comap T.toRing)] (hx : T.toRing T.x ∉ P₁) :
    (P₁.map L.β).comap L.T'.toRing = (P₁.comap T.toRing).map α := by
  classical
  have _ := L.isRegularLocalRing hα
  set p : Ideal R := P₁.comap T.toRing with hp
  set Pb : Ideal L.T'.ring := P₁.map L.β with hPb
  set pb : Ideal R' := Pb.comap L.T'.toRing with hpbdef
  -- `β` is faithfully flat
  have hβ := L.mapsRSOP_β hα hsep
  have hcomapβ : Pb.comap L.β = P₁ := by
    let _ : Algebra T.ring L.T'.ring := L.β.toAlgebra
    have _ : Module.Flat T.ring L.T'.ring := RingHom.MapsRSOP.flat hβ
    have _ : IsLocalHom (algebraMap T.ring L.T'.ring) := inferInstanceAs (IsLocalHom L.β)
    have _ : Module.FaithfullyFlat T.ring L.T'.ring := Module.FaithfullyFlat.of_flat_of_isLocalHom
    exact Ideal.comap_map_eq_self_of_faithfullyFlat (B := L.T'.ring) P₁
  have hcomm := L.isCanonicalLift.comm
  have hpb : pb.comap α = p := by
    rw [hpbdef, Ideal.comap_comap, ← hcomm, ← Ideal.comap_comap, hcomapβ]
  have hge : p.map α ≤ pb := by
    rw [Ideal.map_le_iff_le_comap, hpb]
  -- `(pR̃)` is prime
  have hpmap := RingHom.MapsRSOP.isPrime_map_and_isRegularLocalRing_quotient hα
    (inferInstance : p.IsPrime) inferInstance
  have _ := hpmap.1
  -- the element `x ∉ P₁` and its image
  have hxp : T.x ∉ p := hx
  have hxPb : L.T'.toRing L.T'.x ∉ Pb := by
    intro hxb
    have h1 : Ideal.span {L.T'.xR} = Ideal.span {L.β (T.xR)} := by
      calc Ideal.span {L.T'.xR} = (P.map α).map L.T'.toRing := L.T'.span_xR_eq_map
        _ = P.map (L.T'.toRing.comp α) := Ideal.map_map _ _
        _ = P.map (L.β.comp T.toRing) := by rw [hcomm]
        _ = (P.map T.toRing).map L.β := (Ideal.map_map _ _).symm
        _ = Ideal.span {L.β (T.xR)} := by
          rw [← T.span_xR_eq_map, Ideal.map_span, Set.image_singleton]
    have h2 : L.β T.xR ∈ Ideal.span {L.T'.xR} := by
      rw [h1]; exact Ideal.mem_span_singleton_self _
    obtain ⟨d, hd⟩ := Ideal.mem_span_singleton'.mp h2
    apply hx
    rw [← hcomapβ, Ideal.mem_comap]
    show L.β (T.toRing T.x) ∈ Pb
    rw [show L.β (T.toRing T.x) = L.β T.xR from rfl, ← hd]
    exact Ideal.mul_mem_left _ _ hxb
  have hxpb : L.T'.x ∉ pb := hxPb
  -- bijectivity of the two localizations
  have hf := T.bijective_localRingHom_of_x_notMem p P₁ hp hxp
  have hf' := L.T'.bijective_localRingHom_of_x_notMem pb Pb hpbdef hxpb
  -- the localizations and the canonical homomorphisms
  let Lp := Localization.AtPrime p
  let Lpb := Localization.AtPrime pb
  let TP := Localization.AtPrime P₁
  let TPb := Localization.AtPrime Pb
  let i : R →+* Lp := algebraMap R Lp
  let ib : R' →+* Lpb := algebraMap R' Lpb
  let j : T.ring →+* TP := algebraMap T.ring TP
  let jb : L.T'.ring →+* TPb := algebraMap L.T'.ring TPb
  let f : Lp →+* TP := Localization.localRingHom p P₁ T.toRing hp
  let fb : Lpb →+* TPb := Localization.localRingHom pb Pb L.T'.toRing hpbdef
  let g : TP →+* TPb := Localization.localRingHom P₁ Pb L.β hcomapβ.symm
  have hfi : f.comp i = j.comp T.toRing := RingHom.ext fun r =>
    Localization.localRingHom_to_map p P₁ T.toRing hp r
  have hfbi : fb.comp ib = jb.comp L.T'.toRing := RingHom.ext fun r =>
    Localization.localRingHom_to_map pb Pb L.T'.toRing hpbdef r
  have hgj : g.comp j = jb.comp L.β := RingHom.ext fun r =>
    Localization.localRingHom_to_map P₁ Pb L.β hcomapβ.symm r
  -- the maximal ideal of `(R₁)_{P₁}` is extended from `p`
  have hA : maximalIdeal TP ≤ (p.map T.toRing).map j := by
    have h1 : (maximalIdeal Lp).map f = maximalIdeal TP :=
      IsLocalRing.map_maximalIdeal_of_surjective f hf.2
    rw [← h1, ← Localization.AtPrime.map_eq_maximalIdeal (I := p), Ideal.map_map, hfi,
      ← Ideal.map_map]
  -- hence that of `(R̃₁)_{P₁R̃₁}` is extended from `pR̃`
  have hB : maximalIdeal TPb ≤ ((p.map α).map L.T'.toRing).map jb := by
    have h1 : maximalIdeal TPb = (maximalIdeal TP).map g :=
      calc maximalIdeal TPb = Pb.map jb :=
            (Localization.AtPrime.map_eq_maximalIdeal (I := Pb)).symm
        _ = P₁.map (jb.comp L.β) := Ideal.map_map _ _
        _ = P₁.map (g.comp j) := by rw [hgj]
        _ = (P₁.map j).map g := (Ideal.map_map _ _).symm
        _ = (maximalIdeal TP).map g := by rw [Localization.AtPrime.map_eq_maximalIdeal]
    calc maximalIdeal TPb = (maximalIdeal TP).map g := h1
      _ ≤ ((p.map T.toRing).map j).map g := Ideal.map_mono hA
      _ = p.map ((g.comp j).comp T.toRing) := by rw [Ideal.map_map, Ideal.map_map]
      _ = p.map ((jb.comp L.β).comp T.toRing) := by rw [hgj]
      _ = p.map (jb.comp (L.T'.toRing.comp α)) := by rw [RingHom.comp_assoc, hcomm]
      _ = ((p.map α).map L.T'.toRing).map jb := by
        rw [Ideal.map_map, Ideal.map_map, RingHom.comp_assoc]
  -- conclusion
  refine le_antisymm (fun r hr => ?_) hge
  have h1 : jb (L.T'.toRing r) ∈ ((p.map α).map L.T'.toRing).map jb := by
    refine hB ?_
    rw [← Localization.AtPrime.map_eq_maximalIdeal (I := Pb)]
    exact Ideal.mem_map_of_mem _ hr
  have h2 : jb (L.T'.toRing r) = fb (ib r) := (RingHom.congr_fun hfbi r).symm
  rw [h2, Ideal.map_map, Ideal.map_map, ← hfbi, ← Ideal.map_map] at h1
  have hbij : Function.Bijective fb := hf'
  have h3 : ib r ∈ (p.map α).map ib := by
    have h6 := Ideal.comap_map_of_bijective (I := (p.map α).map ib) fb hbij
    rw [← h6, Ideal.mem_comap, Ideal.map_map]
    exact h1
  have hdisj : Disjoint (pb.primeCompl : Set R') ((p.map α : Ideal R') : Set R') := by
    rw [Set.disjoint_left]
    intro a ha haI
    exact ha (hge haI)
  have h4 := IsLocalization.under_map_of_isPrime_disjoint pb.primeCompl Lpb hpmap.1 hdisj
  have h5 : r ∈ Ideal.under R' (Ideal.map (algebraMap R' Lpb) (p.map α)) := h3
  rwa [h4] at h5
end Properties

end BaseChangeLift

end Lift

/-! ### The extension of the reduction and Proposition 2 -/

section Proposition2

namespace CompleteSepClosedExtension

variable {R : Type u} [CommRing R] [IsRegularLocalRing R] [IsDomain R]
  (E : CompleteSepClosedExtension R) {Q : Ideal R} [Q.IsPrime] [IsRegularLocalRing (R ⧸ Q)]
  (T : MonoidalTransform R Q)

end CompleteSepClosedExtension

/-- **Proposition 2 for complete `R` and residually rational `R₁`** (p. 258: "We may assume that
`R` is complete, and that `R₁` is residually rational over `R`"): the statement of
Proposition 2 with these two additional hypotheses.  Proposition 2 itself follows from it
(`proposition2_of_complete_residuallyRational`). -/
def Proposition2Complete : Prop :=
  ∀ (R : Type u) [CommRing R] [IsRegularLocalRing R] [IsDomain R]
    [IsAdicComplete (maximalIdeal R) R]
    (_ : ringChar R = ringChar (ResidueField R)) (J P Q : Ideal R) [P.IsPrime] [Q.IsPrime]
    (_ : P ≤ Q) (_ : J ≤ P) (_ : Q ≠ P) [IsRegularLocalRing (R ⧸ P)]
    (_ : IsPermissibleCenter R J Q) (T : MonoidalTransform R Q) [IsLocalHom T.toRing]
    [IsRegularLocalRing T.ring]
    (_ : RingHom.IsResiduallySeparableAlgebraic (R := R) (R' := T.ring) T.toRing)
    (_ : RingHom.IsResiduallyRational (R := R) (R' := T.ring) T.toRing)
    (P₁ : Ideal T.ring) [P₁.IsPrime] (_ : P₁.comap T.toRing = P)
    (_ : nuStar T.ring (strictTransformIdeal T J) = nuStar R J)
    (_ : IsPermissibleCenter T.ring (strictTransformIdeal T J) P₁),
    IsPermissibleCenter R J P

set_option linter.overlappingInstances false in
/-- **The reduction of Proposition 2** (p. 258: "We may assume that `R` is complete, and that `R₁`
is residually rational over `R`"): Proposition 2 follows from `Proposition2Complete`.  The
conclusion is the statement of Proposition 2 (`isPermissibleCenter_of_nuStar_strictTransform_eq`
in `Ch3/FrameTransforms.lean`; also `Proposition2Statement` of
`Compat/NormalFlatnessLocalization.lean`). -/
theorem proposition2_of_complete_residuallyRational [Hironaka.Cited.IsSeparableFieldExtensionIff.{u}] (h : Proposition2Complete.{u}) :
    ∀ (R : Type u) [CommRing R] [IsRegularLocalRing R] [IsDomain R]
      (_ : ringChar R = ringChar (ResidueField R)) (J P Q : Ideal R) [P.IsPrime] [Q.IsPrime]
      (_ : P ≤ Q) (_ : J ≤ P) (_ : Q ≠ P) [IsRegularLocalRing (R ⧸ P)]
      (_ : IsPermissibleCenter R J Q) (T : MonoidalTransform R Q) [IsLocalHom T.toRing]
      [IsRegularLocalRing T.ring]
      (_ : RingHom.IsResiduallySeparableAlgebraic (R := R) (R' := T.ring) T.toRing)
      (P₁ : Ideal T.ring) [P₁.IsPrime] (_ : P₁.comap T.toRing = P)
      (_ : nuStar T.ring (strictTransformIdeal T J) = nuStar R J)
      (_ : IsPermissibleCenter T.ring (strictTransformIdeal T J) P₁),
      IsPermissibleCenter R J P := by
  intro R _ _ _ hchar J P Q _ _ hPQ hJP hQP _ hQperm T _ _ hsepT P₁ _ hP₁ hnu hperm₁
  classical
  obtain ⟨E⟩ := CompleteSepClosedExtension.nonempty R
  have hQtop : Q ≠ ⊤ := Ideal.IsPrime.ne_top ‹_›
  obtain ⟨hJQ, hQreg⟩ : J ≤ Q ∧ IsRegularLocalRing (R ⧸ Q) := by
    rcases hQperm with hQ | ⟨-, hJQ, hQreg, -⟩
    · exact absurd hQ hQtop
    · exact ⟨hJQ, hQreg⟩
  have hP₁top : P₁ ≠ ⊤ := Ideal.IsPrime.ne_top ‹_›
  obtain ⟨hJ₁P₁, hP₁reg⟩ : strictTransformIdeal T J ≤ P₁ ∧ IsRegularLocalRing (T.ring ⧸ P₁) := by
    rcases hperm₁ with hP | ⟨-, hJP, hreg, -⟩
    · exact absurd hP hP₁top
    · exact ⟨hJP, hreg⟩
  -- the lift of `T`
  obtain ⟨L⟩ := BaseChangeLift.nonempty E.mapsRSOP T
  have hα := E.mapsRSOP
  have hsep := E.isResiduallySeparableAlgebraic
  have _ : IsRegularLocalRing L.T'.ring := L.isRegularLocalRing hα
  have _ : IsAdicComplete (maximalIdeal E.ring) E.ring := E.isAdicComplete
  obtain ⟨hPb, hPbreg⟩ := E.isPrime_map P
  obtain ⟨hQb, -⟩ := E.isPrime_map Q
  have _ := hPb
  have _ := hQb
  have _ := hPbreg
  -- `P₁ R̃₁` is a prime ideal
  obtain ⟨hP₁b, -⟩ := RingHom.MapsRSOP.isPrime_map_and_isRegularLocalRing_quotient
    (L.mapsRSOP_β hα hsep) (inferInstance : P₁.IsPrime) hP₁reg
  have _ := hP₁b
  -- `x ∉ P₁`
  have hx : T.toRing T.x ∉ P₁ := fun hxP₁ => by
    refine hQP (le_antisymm ?_ hPQ)
    intro q hq
    have h1 : T.toRing q ∈ Ideal.span {T.xR} := by
      rw [T.span_xR_eq_map]
      exact Ideal.mem_map_of_mem _ hq
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp h1
    have h2 : T.toRing q ∈ P₁ := by
      rw [← hc]
      exact Ideal.mul_mem_left _ _ hxP₁
    rw [← hP₁]
    exact h2
  have _ : IsRegularLocalRing (R ⧸ P₁.comap T.toRing) := by rw [hP₁]; infer_instance
  have hcomap := L.comap_map_β_eq hα hsep P₁ hx
  have hstrict := L.strictTransformIdeal_map hα J hJQ
  have key := h E.ring (E.ringChar_eq hchar) (J.map E.hom) (P.map E.hom) (Q.map E.hom)
    (Ideal.map_mono hPQ) (Ideal.map_mono hJP) (fun hh => hQP (E.map_injective_ideal hh))
    ((E.isPermissibleCenter_map_iff J Q hJQ).mp hQperm) L.T'
    (RingHom.isResiduallySeparableAlgebraic_of_residueField_surjective
      (L.isResiduallyRational hα E.isSepClosed hsepT))
    (L.isResiduallyRational hα E.isSepClosed hsepT) (P₁.map L.β)
    (by rw [hcomap, hP₁])
    (by rw [L.nuStar_strictTransformIdeal hα hsep J hJQ, E.nuStar_map]; exact hnu)
    (by rw [hstrict]; exact (L.isPermissibleCenter_map_iff_β hα hsep _ P₁ hJ₁P₁).mp hperm₁)
  exact (E.isPermissibleCenter_map_iff J P hJP).mpr key

end Proposition2

end Hironaka
