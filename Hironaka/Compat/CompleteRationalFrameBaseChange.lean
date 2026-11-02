/-
Copyright (c) 2026 Daattavya Aggarwal, Minhyong Kim, Oisin Kim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daattavya Aggarwal, Minhyong Kim, Oisin Kim
-/
module

public import Hironaka.Compat.CompleteRationalBaseChange
public import Hironaka.Compat.TauZBaseChange
public import Hironaka.Ch3.Stability

/-!
# Compatibility layer: base change of regular frames (Ch. III pp. 254, 256, 258, 266)

The proofs of Lemma 20 (p. 254), Lemma 21 (p. 256), Proposition 2 (p. 258) and Lemma 25 begin with
the reduction: "Let `S → S̃` be any local homomorphism such that a regular system of parameters of
`S` is transformed into such a system of parameters of `S̃` and that the residue field of `S̃` is
separable algebraic over that of `S`. Then `S → S̃` induces in a canonical manner a local
homomorphism `R → S̃{z₁, …, z_r}` which also has the same properties as `S → S̃`. If we replace `S`
by `S̃`, `R` by `R̃ = S̃{z₁, …, z_r}`, … all the assumptions remain valid, and the conclusions are
replaced by equivalent ones."

The R-level part of the reduction (the complete regular local `S̃` with separably closed residue
field, canonical lifts of monoidal transforms) is in `Compat/CompleteRationalBaseChange.lean`.
This file is the frame-level part for a *general* local homomorphism `a : S → S̃` of regular local
rings (the data of the reduction, see `Compat/CompleteRationalBaseChange.lean`), with the structure
map `α = F.baseChangeHom a : R → R̃ = S̃⟦z₁, …, z_r⟧`:
* `RegularFrame.baseChange`: the regular frame `(S̃; z₁, …, z_r)` of `R̃`;
* `RegularFrame.tauZ_baseChangeHom`: `τ_{(z)}(α f₁, …, α f_i) = τ_{(z)}(f₁, …, f_i)`
  (`Compat/TauZBaseChange.lean`);
* `RegularFrame.frameESet_baseChangeHom`, `RegularFrame.isNormalizedBy_baseChangeHom`: E-sets and
  normalization are preserved (Remark 1, p. 245, for `k → k̃`);
* `RegularFrame.extendsToStandardBase_baseChangeHom`: standard bases are preserved (Remark 6).
* `RegularFrame.isAdicComplete_baseChange`: `S̃⟦z⟧` is complete when `S̃` is.
-/

@[expose] public section

open IsLocalRing MvPolynomial

namespace Hironaka
universe u

section SepAlgebraic

open scoped TensorProduct in
/-- A separable algebraic field extension stays reduced after any base change. -/
theorem isReduced_tensorProduct_left_of_isSeparable' (K K' K'' : Type u) [Field K]
    [Field K'] [Field K''] [Algebra K K'] [Algebra K K''] [Algebra.IsSeparable K K'] :
    IsReduced (K' ⊗[K] K'') := by
  suffices h : IsReduced (K'' ⊗[K] K') from
    isReduced_of_injective (Algebra.TensorProduct.comm K K' K'') (AlgEquiv.injective _)
  refine IsReduced.tensorProduct_of_flat_of_forall_fg fun B hB => ?_
  obtain ⟨s, rfl⟩ := hB
  have halg : ∀ x ∈ (s : Set K'), IsAlgebraic K x := fun x _ =>
    Algebra.IsAlgebraic.isAlgebraic x
  let F := IntermediateField.adjoin K (s : Set K')
  have hFB : F.toSubalgebra = Algebra.adjoin K (s : Set K') :=
    IntermediateField.adjoin_toSubalgebra_of_isAlgebraic halg
  have : FiniteDimensional K F :=
    IntermediateField.finiteDimensional_adjoin fun x hx => (halg x hx).isIntegral
  have : Algebra.IsSeparable K F := Algebra.IsSeparable.of_algHom K K' F.val
  have : Algebra.FormallyUnramified K F := Algebra.FormallyUnramified.of_isSeparable K F
  have hred := Algebra.FormallyUnramified.isReduced_of_field K'' (K'' ⊗[K] F)
  let e : (Algebra.adjoin K (s : Set K')) ≃ₐ[K] F :=
    (Subalgebra.equivOfEq _ _ hFB.symm).trans (AlgEquiv.refl)
  exact isReduced_of_injective
    (Algebra.TensorProduct.congr (AlgEquiv.refl (R := K) (A₁ := K'')) e)
    (AlgEquiv.injective _)

/-- A residually separable algebraic local homomorphism is residually separable in the sense of
pp. 211–212 (a separable algebraic extension stays reduced after base change). -/
theorem RingHom.IsResiduallySeparableAlgebraic.isResiduallySeparable {A B : Type u}
    [CommRing A] [CommRing B] [IsLocalRing A] [IsLocalRing B] {φ : A →+* B} [IsLocalHom φ]
    (h : RingHom.IsResiduallySeparableAlgebraic φ) : RingHom.IsResiduallySeparable φ := by
  let _ : Algebra (ResidueField A) (ResidueField B) := (ResidueField.map φ).toAlgebra
  have : Algebra.IsSeparable (ResidueField A) (ResidueField B) := h
  intro k' _ _ _
  exact isReduced_tensorProduct_left_of_isSeparable' _ _ _

end SepAlgebraic


section FrameBaseChange

open MvPowerSeries

variable {R : Type u} [CommRing R] [IsRegularLocalRing R] (F : RegularFrame R)
  {S' : Type u} [CommRing S'] [IsRegularLocalRing S'] (a : F.S →+* S') [IsLocalHom a]

/-- **The base change of a regular frame** (p. 254: "`R̃ = S̃{z₁, …, z_r}`"): for a local
homomorphism `a : S → S̃` of regular local rings, the regular frame `(S̃; z₁, …, z_r)` of the
power series ring `R̃ = S̃⟦z₁, …, z_r⟧`.  The homomorphism `R → R̃` is `F.baseChangeHom a`. -/
noncomputable abbrev RegularFrame.baseChange (S' : Type u) [CommRing S'] [IsRegularLocalRing S'] :
    RegularFrame (MvPowerSeries (Fin F.r) S') :=
  RegularFrame.mvPowerSeries S' F.r

theorem RegularFrame.baseChangeHom_injective (ha : RingHom.MapsRSOP a) :
    Function.Injective (F.baseChangeHom a) :=
  RingHom.MapsRSOP.injective _ (F.mapsRSOP_baseChangeHom a ha)

omit [IsRegularLocalRing S'] [IsLocalHom a] in
theorem RegularFrame.baseChangeHom_comp_algebraMap :
    (F.baseChangeHom a).comp (algebraMap F.S R) =
      (algebraMap S' (MvPowerSeries (Fin F.r) S')).comp a := by
  ext s
  rw [RingHom.comp_apply, F.baseChangeHom_algebraMap a, RingHom.comp_apply,
    algebraMap_mvPowerSeries_eq_C]

omit [IsLocalHom a] in
theorem RegularFrame.baseChangeHom_z' (j : Fin F.r) :
    F.baseChangeHom a (F.z j) = (F.baseChange S').z j :=
  F.baseChangeHom_z a j

variable {F a}

/-- `τ_{(z)}` does not change under the base change `R → S̃{z}` (Lemma 13 and Lemma 12 of §4 for
the `T` of Definition 10*, `tauZ_map`; used in the reductions "we may assume that `R` is complete"
of pp. 254, 256, 258). -/
theorem RegularFrame.tauZ_baseChangeHom [Hironaka.Cited.IsSeparableFieldExtensionIff.{u}] (ha : RingHom.MapsRSOP a)
    (hsep : RingHom.IsResiduallySeparableAlgebraic a) {i : ℕ} (f : Fin i → R) :
    tauZ (MvPowerSeries (Fin F.r) S') (F.baseChange S').z (fun j => F.baseChangeHom a (f j)) =
      tauZ R F.z f := by
  have hα := F.mapsRSOP_baseChangeHom a ha
  have hsep' := F.isResiduallySeparableAlgebraic_baseChangeHom a hsep
  have := tauZ_map (F.baseChangeHom a) hα hsep'.isResiduallySeparable F.z f
  rw [← this]
  congr 1
  exact funext fun j => (F.baseChangeHom_z' a j).symm

/-- The frame-free `τ` with empty frame (`τ(f₁, …, f_i) = τ_{()}(f₁, …, f_i)`) is invariant too. -/
theorem RegularFrame.tauZ_empty_baseChangeHom [Hironaka.Cited.IsSeparableFieldExtensionIff.{u}] (ha : RingHom.MapsRSOP a)
    (hsep : RingHom.IsResiduallySeparableAlgebraic a) {i : ℕ} (f : Fin i → R) :
    tauZ (MvPowerSeries (Fin F.r) S') (![] : Fin 0 → MvPowerSeries (Fin F.r) S')
      (fun j => F.baseChangeHom a (f j)) = tauZ R (![] : Fin 0 → R) f := by
  have hα := F.mapsRSOP_baseChangeHom a ha
  have hsep' := F.isResiduallySeparableAlgebraic_baseChangeHom a hsep
  have := tauZ_map (F.baseChangeHom a) hα hsep'.isResiduallySeparable (![] : Fin 0 → R) f
  rw [← this]
  congr 1
  exact funext fun j => j.elim0


attribute [local instance] MvPolynomial.gradedAlgebra in
/-- **The E-set does not change under the base change** `R → S̃{z}` (Remark 1, p. 245, for the
extension `k → k̃` of residue fields): the initial forms `φ_j ∈ k[Z]` of `(f₁, …, f_i)` are carried
by `ᾱ` to those of `(α f₁, …, α f_i)`, and the E-set of an ideal generated by forms over a field is
unchanged by a field extension. -/
theorem RegularFrame.frameESet_baseChangeHom (ha : RingHom.MapsRSOP a) {i : ℕ} (f : Fin i → R)
    (hf : ∀ j, initialForm (maximalIdeal R) (f j) ∈ Set.range (frameAlgHom F.z)) :
    frameESet (F.baseChange S').z (fun j => F.baseChangeHom a (f j)) = frameESet F.z f := by
  classical
  have hα := F.mapsRSOP_baseChangeHom a ha
  let _ : Field (R ⧸ maximalIdeal R) := Ideal.Quotient.field _
  let _ : Field (MvPowerSeries (Fin F.r) S' ⧸ maximalIdeal (MvPowerSeries (Fin F.r) S')) :=
    Ideal.Quotient.field _
  choose Pf hPf using hf
  have hI : frameInitialIdeal F.z f = Ideal.span (Set.range Pf) := by
    unfold frameInitialIdeal
    congr 1
    ext ψ
    constructor
    · rintro ⟨j, hj⟩
      exact ⟨j, F.frameAlgHom_injective (by rw [hj, hPf j])⟩
    · rintro ⟨j, rfl⟩
      exact ⟨j, hPf j⟩
  have hQ : ∀ j, frameAlgHom (F.baseChange S').z
      (MvPolynomial.map (residueQuotMap (F.baseChangeHom a)) (Pf j)) =
        initialForm (maximalIdeal _) (F.baseChangeHom a (f j)) := by
    intro j
    have h1 := grMapMax_frameAlgHom (F.baseChangeHom a) hα F.z (F.baseChange S').z
      (fun l => (F.baseChangeHom_z' a l).symm) (Pf j)
    rw [hPf j, ← initialForm_map_of_mapsRSOP _ hα] at h1
    exact h1.symm
  have hI' : frameInitialIdeal (F.baseChange S').z (fun j => F.baseChangeHom a (f j)) =
      Ideal.span (Set.range fun j => MvPolynomial.map (residueQuotMap (F.baseChangeHom a))
        (Pf j)) := by
    unfold frameInitialIdeal
    congr 1
    ext ψ
    constructor
    · rintro ⟨j, hj⟩
      exact ⟨j, (F.baseChange S').frameAlgHom_injective ((hQ j).trans hj.symm)⟩
    · rintro ⟨j, rfl⟩
      exact ⟨j, hQ j⟩
  have hhom : (frameInitialIdeal F.z f).IsHomogeneous
      (MvPolynomial.homogeneousSubmodule (Fin F.r) (R ⧸ maximalIdeal R)) := by
    rw [hI]
    apply Ideal.homogeneous_span
    rintro _ ⟨j, rfl⟩
    obtain ⟨d, hd⟩ := initialForm_mem_homogeneous_aux' (maximalIdeal R) (f j)
    exact ⟨d, F.isHomogeneous_of_frameAlgHom_mem_homogeneous (by rw [hPf j]; exact hd)⟩
  have hmap : frameInitialIdeal (F.baseChange S').z (fun j => F.baseChangeHom a (f j)) =
      (frameInitialIdeal F.z f).map
        (MvPolynomial.map (residueQuotMap (F.baseChangeHom a))) := by
    rw [hI', hI, Ideal.map_span, ← Set.range_comp]
    rfl
  have key := (eSet_map_of_injective (residueQuotMap (F.baseChangeHom a))
    (residueQuotMap_injective _) (frameInitialIdeal F.z f) hhom).2
    (fun c hc b hcb => (mul_eq_zero.mp hcb).resolve_left
      ((map_ne_zero_iff _ (residueQuotMap_injective _)).mpr hc))
  unfold frameESet
  rw [hmap]
  exact key

/-- If `g` is normalized by `(f₁, …, f_i)` with respect to `(S; z)`, then `α g` is normalized by
`(α f₁, …, α f_i)` with respect to `(S̃; z)` (p. 254: "all the assumptions remain valid"; the
coefficients of the expansion of `α g` are the images of those of `g`, and the E-sets agree,
`frameESet_baseChangeHom`). -/
theorem RegularFrame.isNormalizedBy_baseChangeHom (ha : RingHom.MapsRSOP a) {i : ℕ}
    (f : Fin i → R) (hf : ∀ j, initialForm (maximalIdeal R) (f j) ∈ Set.range (frameAlgHom F.z))
    (g : R) (h : F.IsNormalizedBy f g) :
    (F.baseChange S').IsNormalizedBy (fun j => F.baseChangeHom a (f j)) (F.baseChangeHom a g) := by
  rw [RegularFrame.isNormalizedBy_iff_expCoeff] at h ⊢
  intro A hA
  rw [F.frameESet_baseChangeHom ha f hf] at hA
  have := F.expCoeff_baseChangeHom a g (Finsupp.equivFunOnFinite.symm A)
  rw [h A hA, map_zero] at this
  exact this

/-- Standard bases are preserved by the base change `R → S̃{z}` (Remark 6 of §3 for the local
homomorphism `α`, which transforms a regular system of parameters into one); in particular a
system which can be extended to a standard base of `J` is carried to one which can be extended to
a standard base of `JR̃` (p. 254: "all the assumptions (1)–(10) remain valid"). -/
theorem RegularFrame.extendsToStandardBase_baseChangeHom (ha : RingHom.MapsRSOP a)
    (J : Ideal R) {i : ℕ} (f : Fin i → R) (h : ExtendsToStandardBase J f) :
    ExtendsToStandardBase (J.map (F.baseChangeHom a)) (fun j => F.baseChangeHom a (f j)) := by
  have hα := F.mapsRSOP_baseChangeHom a ha
  obtain ⟨m, g, him, hg, hgf⟩ := h
  refine ⟨m, fun j => F.baseChangeHom a (g j), him,
    (isStandardBase_iff_isStandardBase_map _ hα J g).mp hg, fun j => ?_⟩
  simp only [hgf]


/-- `R̃ = S̃⟦z₁, …, z_r⟧` is a domain (a regular local ring is a domain). -/
instance instIsDomainMvPowerSeries (S : Type u) [CommRing S] [IsRegularLocalRing S] (r : ℕ) :
    IsDomain (MvPowerSeries (Fin r) S) :=
  Transforms.isDomain_of_isRegularLocalRing _

omit [IsLocalHom a] in
/-- `R̃ = S̃⟦z₁, …, z_r⟧` is complete for its maximal ideal when `S̃` is (so that `R̃ = S̃{z}` is the
power series ring over the complete ring `S̃`, p. 254). -/
theorem RegularFrame.isAdicComplete_baseChange [h : IsAdicComplete (maximalIdeal S') S'] :
    IsAdicComplete (maximalIdeal (MvPowerSeries (Fin F.r) S')) (MvPowerSeries (Fin F.r) S') :=
  isAdicComplete_maximalIdeal_mvPowerSeries_of_isAdicComplete S' F.r

omit [IsLocalHom a] in
/-- The residue field of `R̃ = S̃⟦z⟧` is that of `S̃` (Definition 9(1): `R̃/(z)R̃ ≅ S̃`). -/
theorem RegularFrame.isSepClosed_residueField_baseChange [IsSepClosed (ResidueField S')] :
    IsSepClosed (ResidueField (MvPowerSeries (Fin F.r) S')) :=
  isSepClosed_of_ringEquiv' (k := ResidueField S') (RingEquiv.ofBijective _
    (F.baseChange S').residueField_map_algebraMap_bijective)

end FrameBaseChange

section InitialForms

open MvPolynomial

variable {R : Type u} [CommRing R] [IsRegularLocalRing R]

/-- `τ_{(z)}(f) = 0` forces the initial form of `f` into the image of `k[Z] → gr_M(R)`. -/
theorem RegularFrame.initialForm_mem_range_frameAlgHom_of_tauZ_eq_zero (F : RegularFrame R)
    (f : R) (h : tauZ R F.z (fun _ : Fin 1 => f) = 0) :
    initialForm (maximalIdeal R) f ∈ Set.range (frameAlgHom F.z) := by
  have := F.initialForm_mem_adjoin_of_tauZ_eq_zero f h
  rw [Algebra.adjoin_range_eq_range_aeval] at this
  exact this

end InitialForms

section Lift

variable {R : Type u} [CommRing R] [IsRegularLocalRing R] [IsDomain R] {F : RegularFrame R}
  {S' : Type u} [CommRing S'] [IsRegularLocalRing S'] {a : F.S →+* S'} [IsLocalHom a]
  {P : Ideal R} {T : MonoidalTransform R P}

omit [IsLocalHom a] in
/-- The canonical lift commutes with the structure maps: `T̃.toRing (α r) = β (T.toRing r)`. -/
theorem BaseChangeLift.toRing_baseChangeHom (L : BaseChangeLift (F.baseChangeHom a) T) (r : R) :
    L.T'.toRing (F.baseChangeHom a r) = L.β (T.toRing r) :=
  (RingHom.congr_fun L.isCanonicalLift.comm r).symm

omit [IsLocalHom a] in
/-- The images of `s ∈ S` in `R̃₁`: `T̃.toRing (a s) = β (T.toRing s)`. -/
theorem BaseChangeLift.toRing_algebraMap_baseChange (L : BaseChangeLift (F.baseChangeHom a) T)
    (s : F.S) :
    L.T'.toRing (algebraMap S' (MvPowerSeries (Fin F.r) S') (a s)) =
      L.β (T.toRing (algebraMap F.S R s)) := by
  rw [algebraMap_mvPowerSeries_eq_C, ← F.baseChangeHom_algebraMap a, L.toRing_baseChangeHom]

omit [IsLocalHom a] in
/-- `PR̃₁ = (a x) R̃₁` when `PR₁ = x R₁` (p. 254: assumption (7) remains valid). -/
theorem BaseChangeLift.map_eq_span_baseChange (L : BaseChangeLift (F.baseChangeHom a) T)
    (x : F.S) (h7 : P.map T.toRing = Ideal.span {T.toRing (algebraMap F.S R x)}) :
    (P.map (F.baseChangeHom a)).map L.T'.toRing =
      Ideal.span {L.T'.toRing (algebraMap S' (MvPowerSeries (Fin F.r) S') (a x))} := by
  rw [Ideal.map_map, ← L.isCanonicalLift.comm, ← Ideal.map_map, h7, Ideal.map_span,
    Set.image_singleton, L.toRing_algebraMap_baseChange]

omit [IsDomain R] [IsRegularLocalRing S'] [IsLocalHom a] in
/-- `a x ∈ PR̃` for `x ∈ P ∩ S`. -/
theorem RegularFrame.algebraMap_mem_map_baseChangeHom (x : F.S) (hxP : algebraMap F.S R x ∈ P) :
    algebraMap S' (MvPowerSeries (Fin F.r) S') (a x) ∈ P.map (F.baseChangeHom a) := by
  rw [algebraMap_mvPowerSeries_eq_C, ← F.baseChangeHom_algebraMap a]
  exact Ideal.mem_map_of_mem _ hxP

end Lift

end Hironaka
