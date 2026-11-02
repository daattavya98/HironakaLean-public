/-
Copyright (c) 2026 Daattavya Aggarwal, Minhyong Kim, Oisin Kim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daattavya Aggarwal, Minhyong Kim, Oisin Kim
-/
module

public import Mathlib.FieldTheory.PurelyInseparable.Basic
public import Mathlib.RingTheory.LocalProperties.Reduced
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.TensorProduct.Maps
public import Architect
public import Hironaka.Ch3.JStability
public import Hironaka.Ch3.SequenceLift
public import Hironaka.Statements

/-!
# Ch. III §9 (pp. 262–263): Remark 1

The lifted sequence of monoidal transforms of Remark 1 (p. 263), the transport of residual separability
along ring isomorphisms, one stage of the lifting ("`R_α → R'_α` has the same properties as `R → R'`", by
Lemma 4 of §2) and the lifting along a whole sequence, and Remark 1 itself.
-/

@[expose] public section

open IsLocalRing
open scoped TensorProduct

namespace Hironaka

universe u

/-! ### The lifted sequence of Remark 1 (p. 263) -/

section Transport

/-- Precomposing a residually separable local homomorphism with a ring isomorphism keeps it
residually separable (the residue field map of the isomorphism is bijective, so the tensor
products over the two residue fields of the source agree). -/
theorem RingHom.isResiduallySeparable_comp_ringEquiv {A B C : Type u} [CommRing A] [CommRing B]
    [CommRing C] [IsLocalRing A] [IsLocalRing B] [IsLocalRing C] (g : A ≃+* B)
    [IsLocalHom (g : A →+* B)] (β : B →+* C) [IsLocalHom β]
    (hβ : RingHom.IsResiduallySeparable β) :
    RingHom.IsResiduallySeparable (β.comp (g : A →+* B)) := by
  let gb : ResidueField A ≃+* ResidueField B := ResidueField.mapEquiv g
  let _ : Algebra (ResidueField B) (ResidueField C) := (ResidueField.map β).toAlgebra
  let _ : Algebra (ResidueField A) (ResidueField C) :=
    (ResidueField.map (β.comp (g : A →+* B))).toAlgebra
  let _ : Algebra (ResidueField A) (ResidueField B) := (gb : ResidueField A →+* ResidueField B).toAlgebra
  have hCC : IsScalarTower (ResidueField A) (ResidueField B) (ResidueField C) := by
    refine IsScalarTower.of_algebraMap_eq fun x => ?_
    obtain ⟨a, rfl⟩ := residue_surjective x
    simp [RingHom.algebraMap_toAlgebra, gb, ResidueField.map_residue]
  intro k'' _ _ hpi
  let _ : Algebra (ResidueField B) k'' :=
    ((algebraMap (ResidueField A) k'').comp (gb.symm : ResidueField B →+* ResidueField A)).toAlgebra
  have hk : IsScalarTower (ResidueField A) (ResidueField B) k'' := by
    refine IsScalarTower.of_algebraMap_eq fun x => ?_
    simp [RingHom.algebraMap_toAlgebra]
  have hrange : (algebraMap (ResidueField B) k'').range = (algebraMap (ResidueField A) k'').range := by
    ext y
    constructor
    · rintro ⟨b, rfl⟩
      exact ⟨gb.symm b, rfl⟩
    · rintro ⟨a, rfl⟩
      exact ⟨gb a, by simp [RingHom.algebraMap_toAlgebra]⟩
  have hpi' : IsPurelyInseparable (ResidueField B) k'' := by
    obtain ⟨q, hq⟩ := ExpChar.exists (ResidueField A)
    have hq' : ExpChar (ResidueField B) q := expChar_of_injective_ringHom gb.injective q
    rw [isPurelyInseparable_iff_pow_mem (ResidueField B) q]
    have := (isPurelyInseparable_iff_pow_mem (ResidueField A) q).mp hpi
    intro x
    obtain ⟨n, hn⟩ := this x
    exact ⟨n, hrange ▸ hn⟩
  have hred : IsReduced (ResidueField C ⊗[ResidueField B] k'') := hβ k'' hpi'
  have hc1 : TensorProduct.CompatibleSMul (ResidueField A) (ResidueField B) (ResidueField C) k'' := by
    refine ⟨fun b m n => ?_⟩
    have hb : b = algebraMap (ResidueField A) (ResidueField B) (gb.symm b) := by
      simp [RingHom.algebraMap_toAlgebra]
    have h1 : b • m = (gb.symm b) • m := by
      conv_lhs => rw [hb]
      exact algebraMap_smul (ResidueField B) (gb.symm b) m
    have h2 : b • n = (gb.symm b) • n := by
      conv_lhs => rw [hb]
      exact algebraMap_smul (ResidueField B) (gb.symm b) n
    rw [h1, h2]
    exact TensorProduct.smul_tmul _ _ _
  let e := Algebra.TensorProduct.equivOfCompatibleSMul (ResidueField B) (ResidueField A)
    (ResidueField C) (ResidueField C) k''
  exact isReduced_of_injective (e.toRingEquiv.toRingHom : ResidueField C ⊗[ResidueField A] k'' →+*
    ResidueField C ⊗[ResidueField B] k'') e.injective

end Transport

section Construction

/-- A ring isomorphism is a local homomorphism. -/
theorem isLocalHom_ringEquiv_remark1 {A B : Type u} [CommRing A] [CommRing B] (e : A ≃+* B) :
    IsLocalHom (e : A →+* B) :=
  ⟨fun a ha => by simpa using ha.map (e.symm : B →+* A)⟩

/-- The `n`-th stage of the lifted sequence of Remark 1: a regular local ring `R'_n` with a local
homomorphism `R_n → R'_n` which transforms a regular system of parameters into one and is
residually separable (the "same properties as `R → R'`" of Lemma 4, §2). -/
structure MonoidalSequence.Remark1Stage (S : MonoidalSequence.{u}) (n : ℕ) : Type (u + 1) where
  /-- The ring `R'_n`. -/
  ring : Type u
  [commRing : CommRing ring]
  [isRegularLocalRing : IsRegularLocalRing ring]
  /-- The homomorphism `R_n → R'_n`. -/
  φ : S.ring n →+* ring
  [isLocalHom : IsLocalHom φ]
  mapsRSOP : RingHom.MapsRSOP φ
  isResiduallySeparable : RingHom.IsResiduallySeparable φ

attribute [instance] MonoidalSequence.Remark1Stage.commRing
  MonoidalSequence.Remark1Stage.isRegularLocalRing MonoidalSequence.Remark1Stage.isLocalHom

namespace MonoidalSequence.Remark1Stage

variable {S : MonoidalSequence.{u}}

instance instIsDomain {n : ℕ} (D : S.Remark1Stage n) : IsDomain D.ring :=
  isDomain_of_isRegularLocalRing D.ring

theorem isRegularLocalRing_transform (S : MonoidalSequence.{u}) (n : ℕ) :
    IsRegularLocalRing (S.transform n).ring :=
  IsRegularLocalRing.of_ringEquiv (S.equiv n).symm

/-- The existence of the next stage: Lemma 4 of §2, with the canonical lift chosen so that the
closed fibre has a single prime ideal. -/
theorem exists_next (hS : S.HasRegularCenters) {n : ℕ} (D : S.Remark1Stage n) :
    ∃ (T' : MonoidalTransform D.ring ((S.center n).map D.φ))
      (β : (S.transform n).ring →+* T'.ring) (hβ : IsCanonicalLift D.φ (S.transform n) T' β)
      (_ : IsRegularLocalRing T'.ring),
        haveI := hβ.isLocalHom
        RingHom.MapsRSOP β ∧ RingHom.IsResiduallySeparable β := by
  have := isRegularLocalRing_transform S n
  have hP : S.center n = ⊤ ∨ ((S.center n).IsPrime ∧ IsRegularLocalRing (S.ring n ⧸ S.center n)) :=
    (hS n).2
  exact exists_isCanonicalLift_mapsRSOP_isResiduallySeparable D.φ D.mapsRSOP
    D.isResiduallySeparable hP (S.transform n)

/-- The monoidal transform `R'_{n+1}` of `R'_n` with center `P_nR'_n`. -/
noncomputable def transform (hS : S.HasRegularCenters) {n : ℕ} (D : S.Remark1Stage n) :
    MonoidalTransform D.ring ((S.center n).map D.φ) :=
  (exists_next hS D).choose

/-- The canonical local homomorphism `R_{n+1} → R'_{n+1}`, read on `S.transform n`. -/
noncomputable def canonicalHom (hS : S.HasRegularCenters) {n : ℕ} (D : S.Remark1Stage n) :
    (S.transform n).ring →+* (transform hS D).ring :=
  (exists_next hS D).choose_spec.choose

theorem isCanonicalLift (hS : S.HasRegularCenters) {n : ℕ} (D : S.Remark1Stage n) :
    IsCanonicalLift D.φ (S.transform n) (transform hS D) (canonicalHom hS D) :=
  (exists_next hS D).choose_spec.choose_spec.choose

instance isRegularLocalRing_transform_ring (hS : S.HasRegularCenters) {n : ℕ}
    (D : S.Remark1Stage n) : IsRegularLocalRing (transform hS D).ring :=
  (exists_next hS D).choose_spec.choose_spec.choose_spec.choose

instance isLocalHom_canonicalHom (hS : S.HasRegularCenters) {n : ℕ} (D : S.Remark1Stage n) :
    IsLocalHom (canonicalHom hS D) :=
  (isCanonicalLift hS D).isLocalHom

theorem mapsRSOP_canonicalHom (hS : S.HasRegularCenters) {n : ℕ} (D : S.Remark1Stage n) :
    RingHom.MapsRSOP (canonicalHom hS D) :=
  (exists_next hS D).choose_spec.choose_spec.choose_spec.choose_spec.1

theorem isResiduallySeparable_canonicalHom (hS : S.HasRegularCenters) {n : ℕ}
    (D : S.Remark1Stage n) : RingHom.IsResiduallySeparable (canonicalHom hS D) :=
  (exists_next hS D).choose_spec.choose_spec.choose_spec.choose_spec.2

instance isLocalHom_equiv_symm (n : ℕ) :
    IsLocalHom ((S.equiv n).symm : S.ring (n + 1) →+* (S.transform n).ring) :=
  isLocalHom_ringEquiv_remark1 _

/-- The next stage `R_{n+1} → R'_{n+1}`, the composite of `R_{n+1} ≃ T` with the canonical lift. -/
noncomputable def next (hS : S.HasRegularCenters) {n : ℕ} (D : S.Remark1Stage n) :
    S.Remark1Stage (n + 1) :=
  have := isRegularLocalRing_transform S n
  { ring := (transform hS D).ring
    φ := (canonicalHom hS D).comp ((S.equiv n).symm : S.ring (n + 1) →+* (S.transform n).ring)
    mapsRSOP := RingHom.mapsRSOP_comp (mapsRSOP_of_bijective_aux _ (S.equiv n).symm.bijective)
      (mapsRSOP_canonicalHom hS D)
    isResiduallySeparable := RingHom.isResiduallySeparable_comp_ringEquiv (S.equiv n).symm
      (canonicalHom hS D) (isResiduallySeparable_canonicalHom hS D) }

end MonoidalSequence.Remark1Stage

section Sequence

variable {R R' : Type u} [CommRing R] [IsRegularLocalRing R] [CommRing R'] [IsRegularLocalRing R']
  (α : R →+* R') [IsLocalHom α] (hα : RingHom.MapsRSOP α) (hsep : RingHom.IsResiduallySeparable α)
  (S : MonoidalSequence.{u}) (e : R ≃+* S.ring 0) (hS : S.HasRegularCenters)

/-- The stages `R'_n` of the lifted sequence: `R'_0 = R'`, and `R'_{n+1}` is the canonical lift
of `R_{n+1}` over `R_n → R'_n` chosen by Lemma 4 of §2. -/
noncomputable def MonoidalSequence.remark1Stage : ∀ n, S.Remark1Stage n
  | 0 =>
    have := isLocalHom_ringEquiv_remark1 e.symm
    { ring := R'
      φ := α.comp (e.symm : S.ring 0 →+* R)
      mapsRSOP := RingHom.mapsRSOP_comp (mapsRSOP_of_bijective_aux _ e.symm.bijective) hα
      isResiduallySeparable := RingHom.isResiduallySeparable_comp_ringEquiv e.symm α hsep }
  | n + 1 => (MonoidalSequence.remark1Stage n).next hS

/-- The ideals `J'_n` of the lifted sequence (the zero ideal at `α = 0`, then strict
transforms). -/
noncomputable def MonoidalSequence.remark1Ideal :
    ∀ n, Ideal (MonoidalSequence.remark1Stage α hα hsep S e hS n).ring
  | 0 => ⊥
  | n + 1 =>
    (strictTransformIdeal (MonoidalSequence.Remark1Stage.transform hS
      (MonoidalSequence.remark1Stage α hα hsep S e hS n)) (MonoidalSequence.remark1Ideal n)).map
      (RingEquiv.refl _ : (MonoidalSequence.Remark1Stage.transform hS
        (MonoidalSequence.remark1Stage α hα hsep S e hS n)).ring ≃+* _)

/-- The lifted sequence of monoidal transforms `{(R'_α, P'_{α−1})}` of `R'`. -/
noncomputable def MonoidalSequence.remark1Seq : MonoidalSequence.{u} where
  ring n := (MonoidalSequence.remark1Stage α hα hsep S e hS n).ring
  commRing _n := inferInstance
  isRegularLocalRing _n := inferInstance
  isDomain _n := inferInstance
  ideal n := MonoidalSequence.remark1Ideal α hα hsep S e hS n
  center n := (S.center n).map (MonoidalSequence.remark1Stage α hα hsep S e hS n).φ
  transform n := MonoidalSequence.Remark1Stage.transform hS
    (MonoidalSequence.remark1Stage α hα hsep S e hS n)
  equiv _n := RingEquiv.refl _
  ideal_succ _n := rfl

end Sequence

end Construction

section Existence

variable {R R' : Type u} [CommRing R] [IsRegularLocalRing R] [CommRing R'] [IsRegularLocalRing R']

/-- Remark 1, p. 263: "Given a sequence `{(R_α, P_{α−1})}` of monoidal transforms of `R`, there
exists always a sequence of monoidal transforms `{(R'_α, P'_{α−1})}` of `R'` such that we have a
commutative diagram of canonical local homomorphisms `R_{α−1} → R'_{α−1}`, `R_α → R'_α` for all
`α`, where `R₀ = R`, `R'₀ = R'` and `P'_{α−1} = P_{α−1}R'`."

The sequence is built stage by stage (`MonoidalSequence.remark1Seq`): if `R_{α−1} → R'_{α−1}`
transforms a regular system of parameters into one and is residually separable, then Lemma 4 of
§2 (`exists_isCanonicalLift_mapsRSOP_isResiduallySeparable`) gives a canonical lift
`R_α → R'_α`, chosen with a prime ideal of `R'_{α−1}[x⁻¹P'_{α−1}]` minimal over the maximal ideal
of `R_{α−1}`, so that the closed fibre is a field; `R'_α` is again regular and `R_α → R'_α` again
has the two properties, which lets the construction continue.  The diagram is `IsLiftAlong`
(with `P'_α = P_αR'_α`); `R` and `R'` are identified with the zeroth rings through
`e : R ≃+* S.ring 0` and `e' : R' ≃+* S'.ring 0`. -/
theorem exists_isLiftAlong_remark1 (α : R →+* R') [IsLocalHom α] (hα : RingHom.MapsRSOP α)
    (hsep : RingHom.IsResiduallySeparable α) (S : MonoidalSequence.{u}) (e : R ≃+* S.ring 0)
    (hS : S.HasRegularCenters) :
    ∃ (S' : MonoidalSequence.{u}) (e' : R' ≃+* S'.ring 0) (φ : ∀ n, S.ring n →+* S'.ring n),
      S'.HasRegularCenters ∧
        (φ 0).comp (e : R →+* S.ring 0) = (e' : R' →+* S'.ring 0).comp α ∧
        S.IsLiftAlong S' φ := by
  refine ⟨MonoidalSequence.remark1Seq α hα hsep S e hS, RingEquiv.refl R',
    fun n => (MonoidalSequence.remark1Stage α hα hsep S e hS n).φ, ?_, ?_, ?_⟩
  · intro n
    have hxm := (MonoidalSequence.Remark1Stage.transform hS
      (MonoidalSequence.remark1Stage α hα hsep S e hS n)).x_mem
    have hx0 := (MonoidalSequence.Remark1Stage.transform hS
      (MonoidalSequence.remark1Stage α hα hsep S e hS n)).x_ne_zero
    refine ⟨fun h => hx0 (Ideal.mem_bot.mp (h ▸ hxm)), ?_⟩
    rcases (hS n).2 with hc | ⟨hP, hreg⟩
    · left
      show (S.center n).map (MonoidalSequence.remark1Stage α hα hsep S e hS n).φ = ⊤
      rw [hc, Ideal.map_top]
    · right
      exact (RingHom.MapsRSOP.canonicalLift_properties
        (MonoidalSequence.remark1Stage α hα hsep S e hS n).φ
        (MonoidalSequence.remark1Stage α hα hsep S e hS n).mapsRSOP hP hreg).1
  · refine RingHom.ext fun x => ?_
    show α (e.symm (e x)) = α x
    rw [RingEquiv.symm_apply_apply]
  · refine ⟨fun n => (MonoidalSequence.remark1Stage α hα hsep S e hS n).isLocalHom,
      fun n => rfl, fun n => ?_⟩
    have hcomp : (((MonoidalSequence.remark1Seq α hα hsep S e hS).equiv n).symm :
        (MonoidalSequence.remark1Seq α hα hsep S e hS).ring (n + 1) →+*
          ((MonoidalSequence.remark1Seq α hα hsep S e hS).transform n).ring).comp
        ((MonoidalSequence.remark1Stage α hα hsep S e hS (n + 1)).φ.comp
          (S.equiv n : (S.transform n).ring →+* S.ring (n + 1))) =
        MonoidalSequence.Remark1Stage.canonicalHom hS
          (MonoidalSequence.remark1Stage α hα hsep S e hS n) :=
      RingHom.ext fun x => by
        show MonoidalSequence.Remark1Stage.canonicalHom hS
          (MonoidalSequence.remark1Stage α hα hsep S e hS n) ((S.equiv n).symm (S.equiv n x)) = _
        rw [RingEquiv.symm_apply_apply]
        rfl
    exact hcomp.symm ▸ MonoidalSequence.Remark1Stage.isCanonicalLift hS
      (MonoidalSequence.remark1Stage α hα hsep S e hS n)

end Existence

/-! ### Transport of residual separability along ring isomorphisms -/

section Transport

/-- Pure inseparability is transported along an isomorphism of the base field. -/
private theorem isPurelyInseparable_of_equiv_aux {k₁ k₂ L : Type u} [Field k₁] [Field k₂] [Field L]
    [Algebra k₂ L] [Algebra k₁ L] (e₁ : k₁ ≃+* k₂)
    (he : ∀ x, algebraMap k₁ L x = algebraMap k₂ L (e₁ x)) [IsPurelyInseparable k₂ L] :
    IsPurelyInseparable k₁ L := by
  let _ : Algebra k₁ k₂ := (e₁ : k₁ →+* k₂).toAlgebra
  have _ : IsScalarTower k₁ k₂ L := IsScalarTower.of_algebraMap_eq fun x => by
    rw [he]; rfl
  have hint : Algebra.IsIntegral k₁ k₂ := Algebra.IsIntegral.of_surjective (Algebra.ofId k₁ k₂) e₁.surjective
  have hrange : (algebraMap k₂ L).range ≤ (algebraMap k₁ L).range := by
    rintro _ ⟨x, rfl⟩
    exact ⟨e₁.symm x, by rw [he]; simp⟩
  refine ⟨⟨fun x => ?_⟩, fun x hx => ?_⟩
  · exact isIntegral_trans (R := k₁) (A := k₂) x (IsPurelyInseparable.isIntegral' k₂ x)
  · exact hrange (IsPurelyInseparable.inseparable' (F := k₂) x (hx.tower_top k₂))

/-- Separability of field extensions (pp. 211-212) is transported along isomorphisms of both fields. -/
private theorem isSeparableFieldExtension_of_equiv_aux {k₁ k₂ K₁ K₂ : Type u} [Field k₁]
    [Field k₂] [Field K₁] [Field K₂] [Algebra k₁ K₁] [Algebra k₂ K₂] (e₁ : k₁ ≃+* k₂)
    (e₂ : K₁ ≃+* K₂) (h : ∀ x, e₂ (algebraMap k₁ K₁ x) = algebraMap k₂ K₂ (e₁ x))
    (hK : IsSeparableFieldExtension k₁ K₁) : IsSeparableFieldExtension k₂ K₂ := by
  intro L _ _ hL
  let _ : Algebra k₁ L := ((algebraMap k₂ L).comp (e₁ : k₁ →+* k₂)).toAlgebra
  have he : ∀ x, algebraMap k₁ L x = algebraMap k₂ L (e₁ x) := fun x => rfl
  have : IsPurelyInseparable k₁ L := isPurelyInseparable_of_equiv_aux e₁ he
  have hred : IsReduced (K₁ ⊗[k₁] L) := hK L this
  have hs : ∀ c : k₂, e₂.symm (algebraMap k₂ K₂ c) = algebraMap k₁ K₁ (e₁.symm c) := fun c => by
    rw [RingEquiv.symm_apply_eq, h, RingEquiv.apply_symm_apply]
  -- the isomorphism `K₂ ⊗_{k₂} L ≅ K₁ ⊗_{k₁} L`
  let _ : Algebra k₂ (K₁ ⊗[k₁] L) := ((algebraMap k₁ (K₁ ⊗[k₁] L)).comp (e₁.symm : k₂ →+* k₁)).toAlgebra
  have hC : ∀ c : k₂, algebraMap k₂ (K₁ ⊗[k₁] L) c = algebraMap k₁ (K₁ ⊗[k₁] L) (e₁.symm c) :=
    fun c => rfl
  let f : K₂ →ₐ[k₂] K₁ ⊗[k₁] L :=
    { ((Algebra.TensorProduct.includeLeftRingHom : K₁ →+* K₁ ⊗[k₁] L).comp
        (e₂.symm : K₂ →+* K₁)) with
      commutes' := fun c => by
        show (e₂.symm (algebraMap k₂ K₂ c)) ⊗ₜ[k₁] (1 : L) = algebraMap k₂ (K₁ ⊗[k₁] L) c
        rw [hC, hs, Algebra.TensorProduct.algebraMap_apply]
        }
  let g : L →ₐ[k₂] K₁ ⊗[k₁] L :=
    { (Algebra.TensorProduct.includeRight : L →ₐ[k₁] K₁ ⊗[k₁] L).toRingHom with
      commutes' := fun c => by
        show (1 : K₁) ⊗ₜ[k₁] (algebraMap k₂ L c) = algebraMap k₂ (K₁ ⊗[k₁] L) c
        rw [hC, Algebra.TensorProduct.algebraMap_apply]
        have : algebraMap k₂ L c = algebraMap k₁ L (e₁.symm c) := by
          rw [he]; simp
        rw [this, Algebra.TensorProduct.tmul_one_eq_one_tmul] }
  let Ψ : K₂ ⊗[k₂] L →ₐ[k₂] K₁ ⊗[k₁] L :=
    Algebra.TensorProduct.lift f g fun _ _ => Commute.all _ _
  -- the inverse direction
  let _ : Algebra k₁ (K₂ ⊗[k₂] L) := ((algebraMap k₂ (K₂ ⊗[k₂] L)).comp (e₁ : k₁ →+* k₂)).toAlgebra
  have hD : ∀ c : k₁, algebraMap k₁ (K₂ ⊗[k₂] L) c = algebraMap k₂ (K₂ ⊗[k₂] L) (e₁ c) :=
    fun c => rfl
  let f' : K₁ →ₐ[k₁] K₂ ⊗[k₂] L :=
    { ((Algebra.TensorProduct.includeLeftRingHom : K₂ →+* K₂ ⊗[k₂] L).comp
        (e₂ : K₁ →+* K₂)) with
      commutes' := fun c => by
        show (e₂ (algebraMap k₁ K₁ c)) ⊗ₜ[k₂] (1 : L) = algebraMap k₁ (K₂ ⊗[k₂] L) c
        rw [hD, h, Algebra.TensorProduct.algebraMap_apply] }
  let g' : L →ₐ[k₁] K₂ ⊗[k₂] L :=
    { (Algebra.TensorProduct.includeRight : L →ₐ[k₂] K₂ ⊗[k₂] L).toRingHom with
      commutes' := fun c => by
        show (1 : K₂) ⊗ₜ[k₂] (algebraMap k₁ L c) = algebraMap k₁ (K₂ ⊗[k₂] L) c
        rw [hD, Algebra.TensorProduct.algebraMap_apply, he, Algebra.TensorProduct.tmul_one_eq_one_tmul] }
  let Ψ' : K₁ ⊗[k₁] L →ₐ[k₁] K₂ ⊗[k₂] L :=
    Algebra.TensorProduct.lift f' g' fun _ _ => Commute.all _ _
  have hΨ : ∀ (x : K₂) (y : L), Ψ (x ⊗ₜ[k₂] y) = (e₂.symm x) ⊗ₜ[k₁] y := fun x y => by
    show (e₂.symm x ⊗ₜ[k₁] (1 : L)) * ((1 : K₁) ⊗ₜ[k₁] y) = _
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  have hΨ' : ∀ (x : K₁) (y : L), Ψ' (x ⊗ₜ[k₁] y) = (e₂ x) ⊗ₜ[k₂] y := fun x y => by
    show (e₂ x ⊗ₜ[k₂] (1 : L)) * ((1 : K₂) ⊗ₜ[k₂] y) = _
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  have hleft : Function.LeftInverse Ψ' Ψ := by
    intro z
    induction z using TensorProduct.inductionOn with
    | tmul x y => rw [hΨ, hΨ', RingEquiv.apply_symm_apply]
    | add x y hx hy => rw [map_add, map_add, hx, hy]
  exact isReduced_of_injective (Ψ : K₂ ⊗[k₂] L →+* K₁ ⊗[k₁] L) hleft.injective

/-- `f ∘ α ∘ g` is residually separable if `α` is, for ring isomorphisms `f`, `g`. -/
private theorem isResiduallySeparable_comp_ringEquiv_aux {A₀ A B C : Type u} [CommRing A₀]
    [CommRing A] [CommRing B] [CommRing C] [IsLocalRing A₀] [IsLocalRing A] [IsLocalRing B]
    [IsLocalRing C] (α : A →+* B) [IsLocalHom α] (hα : RingHom.IsResiduallySeparable α)
    (f : B ≃+* C) (g : A₀ ≃+* A) [IsLocalHom ((f : B →+* C).comp (α.comp (g : A₀ →+* A)))] :
    RingHom.IsResiduallySeparable ((f : B →+* C).comp (α.comp (g : A₀ →+* A))) := by
  have _ := isLocalHom_ringEquiv_remark1 g
  have _ := isLocalHom_ringEquiv_remark1 f
  unfold RingHom.IsResiduallySeparable at hα ⊢
  let _ : Algebra (ResidueField A) (ResidueField B) := (ResidueField.map α).toAlgebra
  let _ : Algebra (ResidueField A₀) (ResidueField C) :=
    (ResidueField.map ((f : B →+* C).comp (α.comp (g : A₀ →+* A)))).toAlgebra
  refine isSeparableFieldExtension_of_equiv_aux (ResidueField.mapEquiv g).symm
    (ResidueField.mapEquiv f) (fun x => ?_) hα
  obtain ⟨a, rfl⟩ := residue_surjective x
  simp [RingHom.algebraMap_toAlgebra]

/-- If `α` and `β` transform a regular system of parameters into one, so does `f ∘ α ∘ g` for
ring isomorphisms `f`, `g`. -/
private theorem mapsRSOP_comp_ringEquiv_aux {A₀ A B C : Type u} [CommRing A₀] [CommRing A]
    [CommRing B] [CommRing C] [IsRegularLocalRing A₀] [IsRegularLocalRing A] [IsRegularLocalRing B]
    [IsRegularLocalRing C] (α : A →+* B) (hα : RingHom.MapsRSOP α) (f : B ≃+* C) (g : A₀ ≃+* A) :
    RingHom.MapsRSOP ((f : B →+* C).comp (α.comp (g : A₀ →+* A))) := by
  have _ := isLocalHom_ringEquiv_remark1 g
  have _ := isLocalHom_ringEquiv_remark1 f
  have h1 : RingHom.MapsRSOP (g : A₀ →+* A) := mapsRSOP_of_bijective_aux _ g.bijective
  have h2 : RingHom.MapsRSOP (f : B →+* C) := mapsRSOP_of_bijective_aux _ f.bijective
  exact RingHom.mapsRSOP_comp (RingHom.mapsRSOP_comp h1 hα) h2

end Transport

/-! ### One stage: "`R_α → R'_α` has the same properties as `R → R'`" (Lemma 4, §2) -/

section Stage

variable {R Rb : Type u} [CommRing R] [IsRegularLocalRing R] [IsDomain R] [CommRing Rb]
  [IsRegularLocalRing Rb] [IsDomain Rb]

private theorem isResiduallySeparable_congr_aux {A B : Type u} [CommRing A] [CommRing B]
    [IsLocalRing A] [IsLocalRing B] {β₁ β₂ : A →+* B} [IsLocalHom β₁] [IsLocalHom β₂]
    (h : β₁ = β₂) (h₁ : RingHom.IsResiduallySeparable β₁) : RingHom.IsResiduallySeparable β₂ := by
  subst h
  exact h₁

/-- One stage of the lifting of a sequence (Lemma 4 of §2, applied at the stage; Remark 1 of
§9, p. 263): if `α : R → R̄` transforms a regular system of parameters into one and is residually
separable, `t` is a monoidal transform of `R` which is residually algebraic over `R` with center
`⊤` or a prime `P` with `R/P` regular, and `β : t → t̄` is a canonical local homomorphism into a
regular monoidal transform of `R̄` with center `PR̄`, then `β` again transforms a regular system of
parameters into one and is residually separable. -/
theorem mapsRSOP_and_isResiduallySeparable_of_isCanonicalLift (α : R →+* Rb) [IsLocalHom α]
    (hα : RingHom.MapsRSOP α) (hsep : RingHom.IsResiduallySeparable α) {P : Ideal R}
    {Pb : Ideal Rb} (hPb : Pb = P.map α) (hP : P = ⊤ ∨ (P.IsPrime ∧ IsRegularLocalRing (R ⧸ P)))
    (t : MonoidalTransform R P) (tb : MonoidalTransform Rb Pb) [IsRegularLocalRing t.ring]
    [IsRegularLocalRing tb.ring] (β : t.ring →+* tb.ring) (hβ : IsCanonicalLift α t tb β)
    (hres : RingHom.IsResiduallyAlgebraic (R := R) (R' := t.ring) t.toRing) :
    haveI := hβ.isLocalHom
    RingHom.MapsRSOP β ∧ RingHom.IsResiduallySeparable β := by
  subst hPb
  have := hβ.isLocalHom
  rcases hP with hP | ⟨hPp, hPr⟩
  · -- the center is `R`: `β = tb.toRing ∘ α ∘ t.toRing⁻¹`
    have hP' : P.map α = ⊤ := by rw [hP, Ideal.map_top]
    have ht := MonoidalSequence.toRing_bijective_of_eq_top_aux t hP
    have htb := MonoidalSequence.toRing_bijective_of_eq_top_aux tb hP'
    let g : t.ring ≃+* R := (RingEquiv.ofBijective t.toRing ht).symm
    let f : Rb ≃+* tb.ring := RingEquiv.ofBijective tb.toRing htb
    have hβeq : β = (f : Rb →+* tb.ring).comp (α.comp (g : t.ring →+* R)) := by
      refine RingHom.ext fun y => ?_
      obtain ⟨r, rfl⟩ := ht.2 y
      have := RingHom.congr_fun hβ.comm r
      simp only [RingHom.coe_comp, Function.comp_apply] at this ⊢
      rw [this]
      have h2 : (RingEquiv.ofBijective t.toRing ht).symm (t.toRing r) = r :=
        (RingEquiv.ofBijective t.toRing ht).symm_apply_apply r
      show tb.toRing (α r) = tb.toRing (α ((RingEquiv.ofBijective t.toRing ht).symm (t.toRing r)))
      rw [h2]
    have _ := isLocalHom_ringEquiv_remark1 g
    have _ := isLocalHom_ringEquiv_remark1 f
    have _ : IsLocalHom ((f : Rb →+* tb.ring).comp (α.comp (g : t.ring →+* R))) := by
      rw [← hβeq]; infer_instance
    refine ⟨hβeq ▸ mapsRSOP_comp_ringEquiv_aux α hα f g, ?_⟩
    exact isResiduallySeparable_congr_aux hβeq.symm
      (isResiduallySeparable_comp_ringEquiv_aux α hsep f g)
  · obtain ⟨-, h1, -⟩ := RingHom.MapsRSOP.canonicalLift_properties α hα hPp hPr
    have hdim := (h1 t (Or.inr hres)).2.1 tb β hβ
    exact IsCanonicalLift.mapsRSOP_and_isResiduallySeparable_of_ringKrullDim_eq α hα hsep t tb β
      hβ hdim

/-- The Corollary to Lemma 5, §2 (pp. 215–216), at one stage of the lifting, including the case in
which the center is `R` itself: `J̄' = J'R̄'`. -/
theorem strictTransformIdeal_map_eq_map_of_isCanonicalLift (α : R →+* Rb) [IsLocalHom α]
    (hα : RingHom.MapsRSOP α) {P : Ideal R} {Pb : Ideal Rb} (hPb : Pb = P.map α)
    (hP : P = ⊤ ∨ (P.IsPrime ∧ IsRegularLocalRing (R ⧸ P))) (t : MonoidalTransform R P)
    (tb : MonoidalTransform Rb Pb) (β : t.ring →+* tb.ring) (hβ : IsCanonicalLift α t tb β)
    (J : Ideal R) : strictTransformIdeal tb (J.map α) = (strictTransformIdeal t J).map β := by
  subst hPb
  rcases hP with hP | ⟨hPp, hPr⟩
  · have hP' : P.map α = ⊤ := by rw [hP, Ideal.map_top]
    rw [MonoidalSequence.strictTransformIdeal_eq_map_of_eq_top_aux tb hP' (J.map α),
      MonoidalSequence.strictTransformIdeal_eq_map_of_eq_top_aux t hP J, Ideal.map_map, Ideal.map_map,
      hβ.comm]
  · exact IsCanonicalLift.strictTransformIdeal_map_eq_map_strictTransformIdeal α hα hPp hPr J t tb β hβ

end Stage

/-! ### Along a lifted sequence -/

section MapAux

private theorem map_map_equiv_left_aux {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    (f : A ≃+* B) (g : B →+* C) (I : Ideal A) :
    (I.map f).map g = I.map (g.comp (f : A →+* B)) := by
  rw [← Ideal.map_coe f, Ideal.map_map]

private theorem map_map_equiv_right_aux {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    (f : A →+* B) (g : B ≃+* C) (I : Ideal A) :
    (I.map f).map g = I.map ((g : B →+* C).comp f) := by
  rw [← Ideal.map_coe g, Ideal.map_map]

end MapAux

section Sequence

variable {R R' : Type u} [CommRing R] [IsRegularLocalRing R] [CommRing R'] [IsRegularLocalRing R']

/-- Remark 1, p. 263: "By Lemma 4, §2, `R_α → R'_α` has the same properties as `R → R'` for
every `α`": along a lift `{(R'_α, P'_{α−1})}` of a sequence `{(R_α, P_{α−1})}` of monoidal
transforms with every `R_α` residually algebraic over `R_{α−1}`, each `R_α → R'_α` transforms a
regular system of parameters into one and is residually separable. -/
theorem mapsRSOP_and_isResiduallySeparable_of_isLiftAlong (α : R →+* R') [IsLocalHom α]
    (hα : RingHom.MapsRSOP α) (hsep : RingHom.IsResiduallySeparable α) (S : MonoidalSequence.{u})
    (e : R ≃+* S.ring 0) (hS : S.HasRegularCenters) (S' : MonoidalSequence.{u})
    (e' : R' ≃+* S'.ring 0) (φ : ∀ n, S.ring n →+* S'.ring n)
    (h0 : (φ 0).comp (e : R →+* S.ring 0) = (e' : R' →+* S'.ring 0).comp α)
    (hφ : S.IsLiftAlong S' φ)
    (hres : ∀ n, RingHom.IsResiduallyAlgebraic (R := S.ring n) (R' := (S.transform n).ring)
        (S.transform n).toRing) :
    ∀ n, haveI := hφ.isLocalHom n
      RingHom.MapsRSOP (φ n) ∧ RingHom.IsResiduallySeparable (φ n) := by
  intro n
  induction n with
  | zero =>
    have _ := hφ.isLocalHom 0
    have _ := isLocalHom_ringEquiv_remark1 e
    have _ := isLocalHom_ringEquiv_remark1 e'
    have hφ0 : φ 0 = (e' : R' →+* S'.ring 0).comp (α.comp (e.symm : S.ring 0 →+* R)) := by
      refine RingHom.ext fun y => ?_
      obtain ⟨r, rfl⟩ := e.surjective y
      have := RingHom.congr_fun h0 r
      simpa using this
    have _ : IsLocalHom ((e' : R' →+* S'.ring 0).comp (α.comp (e.symm : S.ring 0 →+* R))) := by
      rw [← hφ0]; infer_instance
    refine ⟨hφ0 ▸ mapsRSOP_comp_ringEquiv_aux α hα e' e.symm, ?_⟩
    exact isResiduallySeparable_congr_aux hφ0.symm
      (isResiduallySeparable_comp_ringEquiv_aux α hsep e' e.symm)
  | succ n ih =>
    have hn := hφ.isLocalHom n
    have hn1 := hφ.isLocalHom (n + 1)
    obtain ⟨ihm, ihs⟩ := ih
    have _ : IsRegularLocalRing (S.transform n).ring :=
      IsRegularLocalRing.of_ringEquiv (S.equiv n).symm
    have _ : IsRegularLocalRing (S'.transform n).ring :=
      IsRegularLocalRing.of_ringEquiv (S'.equiv n).symm
    have hP : S.center n = ⊤ ∨ ((S.center n).IsPrime ∧ IsRegularLocalRing (S.ring n ⧸ S.center n)) :=
      (hS n).2
    have hstage := mapsRSOP_and_isResiduallySeparable_of_isCanonicalLift (φ n) ihm ihs
      (hφ.center_eq n) hP (S.transform n) (S'.transform n) _ (hφ.canonical n) (hres n)
    have hφn : φ (n + 1) = ((S'.equiv n : (S'.transform n).ring ≃+* S'.ring (n + 1)) :
        (S'.transform n).ring →+* S'.ring (n + 1)).comp
      ((((S'.equiv n).symm : S'.ring (n + 1) →+* (S'.transform n).ring).comp
        ((φ (n + 1)).comp (S.equiv n : (S.transform n).ring →+* S.ring (n + 1)))).comp
        ((S.equiv n).symm : S.ring (n + 1) →+* (S.transform n).ring)) := by
      refine RingHom.ext fun y => ?_
      simp
    have _ := isLocalHom_ringEquiv_remark1 (S'.equiv n)
    have _ := isLocalHom_ringEquiv_remark1 (S.equiv n).symm
    have _ : IsLocalHom ((((S'.equiv n : (S'.transform n).ring ≃+* S'.ring (n + 1)) :
        (S'.transform n).ring →+* S'.ring (n + 1))).comp
        ((((S'.equiv n).symm : S'.ring (n + 1) →+* (S'.transform n).ring).comp
        ((φ (n + 1)).comp (S.equiv n : (S.transform n).ring →+* S.ring (n + 1)))).comp
        ((S.equiv n).symm : S.ring (n + 1) →+* (S.transform n).ring))) := by
      rw [← hφn]; exact hn1
    have key := mapsRSOP_comp_ringEquiv_aux _ hstage.1 (S'.equiv n) (S.equiv n).symm
    rw [← hφn] at key
    refine ⟨key, ?_⟩
    exact isResiduallySeparable_congr_aux hφn.symm
      (isResiduallySeparable_comp_ringEquiv_aux _ hstage.2 (S'.equiv n) (S.equiv n).symm)

omit [IsRegularLocalRing R] [IsRegularLocalRing R'] in
/-- Remark 1, p. 263: "the strict transform `J'_α` of `J'` in `R'_α` along `{(R'_α, P'_{α−1})}` is
equal to `J_αR'_α` where `J_α` is the strict transform of `J` in `R_α` along `{(R_α, P_{α−1})}`,
by Corollary to Lemma 5, § 2". -/
theorem strictAlong_map_eq_map_of_isLiftAlong (α : R →+* R') [IsLocalHom α]
    (S : MonoidalSequence.{u})
    (e : R ≃+* S.ring 0) (hS : S.HasRegularCenters) (S' : MonoidalSequence.{u})
    (e' : R' ≃+* S'.ring 0) (φ : ∀ n, S.ring n →+* S'.ring n)
    (h0 : (φ 0).comp (e : R →+* S.ring 0) = (e' : R' →+* S'.ring 0).comp α)
    (hφ : S.IsLiftAlong S' φ)
    (hmaps : ∀ n, haveI := hφ.isLocalHom n; RingHom.MapsRSOP (φ n)) (J : Ideal R) :
    ∀ n, S'.strictAlong ((J.map α).map e') n = (S.strictAlong (J.map e) n).map (φ n) := by
  intro n
  induction n with
  | zero =>
    show (J.map α).map e' = (J.map e).map (φ 0)
    rw [map_map_equiv_right_aux, map_map_equiv_left_aux]
    congr 1
    exact h0.symm
  | succ n ih =>
    have hn := hφ.isLocalHom n
    have _ : IsRegularLocalRing (S.transform n).ring :=
      IsRegularLocalRing.of_ringEquiv (S.equiv n).symm
    have _ : IsRegularLocalRing (S'.transform n).ring :=
      IsRegularLocalRing.of_ringEquiv (S'.equiv n).symm
    have hP : S.center n = ⊤ ∨ ((S.center n).IsPrime ∧ IsRegularLocalRing (S.ring n ⧸ S.center n)) :=
      (hS n).2
    have hst := strictTransformIdeal_map_eq_map_of_isCanonicalLift (φ n) (hmaps n)
      (hφ.center_eq n) hP (S.transform n) (S'.transform n) _ (hφ.canonical n)
      (S.strictAlong (J.map e) n)
    show (strictTransformIdeal (S'.transform n) (S'.strictAlong ((J.map α).map e') n)).map
        (S'.equiv n) = ((strictTransformIdeal (S.transform n) (S.strictAlong (J.map e) n)).map
        (S.equiv n)).map (φ (n + 1))
    rw [ih, hst, map_map_equiv_right_aux, map_map_equiv_left_aux]
    congr 1
    refine RingHom.ext fun y => ?_
    simp

/-- Remark 1 of §5 (p. 226), at one stage: for a center `P` which is `R` or a prime ideal,
`P` is a permissible center for `I` if and only if `PR'` is one for `IR'`, for a local
homomorphism `R → R'` transforming a regular system of parameters into one. (For `P ⊉ I` both
sides fail, by faithful flatness.) -/
theorem isPermissibleCenter_map_iff_of_eq_top_or_isPrime (α : R →+* R') [IsLocalHom α]
    (hα : RingHom.MapsRSOP α) (I P : Ideal R) (hP : P = ⊤ ∨ P.IsPrime) :
    IsPermissibleCenter R I P ↔ IsPermissibleCenter R' (I.map α) (P.map α) := by
  rcases hP with hP | hP
  · have hP' : P.map α = ⊤ := by rw [hP, Ideal.map_top]
    exact ⟨fun _ => Or.inl hP', fun _ => Or.inl hP⟩
  · by_cases hIP : I ≤ P
    · exact (isPermissibleCenter_map_iff α hα I P hIP).2.2.2
    · let _ : Algebra R R' := α.toAlgebra
      have _ : IsLocalHom (algebraMap R R') := ‹IsLocalHom α›
      have _ : Module.Flat R R' := hα.flat
      have _ : Module.FaithfullyFlat R R' := Module.FaithfullyFlat.of_flat_of_isLocalHom
      have hPtop : P ≠ ⊤ := hP.ne_top
      have hP'top : P.map α ≠ ⊤ := fun h => hPtop (by
        rw [← Ideal.comap_map_eq_self_of_faithfullyFlat (B := R') P, show P.map (algebraMap R R')
          = P.map α from rfl, h, Ideal.comap_top])
      have hIP' : ¬ I.map α ≤ P.map α := fun h => hIP (by
        have := Ideal.comap_mono (f := algebraMap R R') h
        have h1 := Ideal.comap_map_eq_self_of_faithfullyFlat (B := R') I
        have h2 := Ideal.comap_map_eq_self_of_faithfullyFlat (B := R') P
        exact le_trans (le_of_eq h1.symm) (le_trans this (le_of_eq h2)))
      constructor
      · rintro (h | ⟨-, h, -⟩)
        · exact absurd h hPtop
        · exact absurd h hIP
      · rintro (h | ⟨-, h, -⟩)
        · exact absurd h hP'top
        · exact absurd h hIP'

omit [IsRegularLocalRing R] [IsRegularLocalRing R'] in
/-- Remark 1, p. 263: "`{(R'_α, P'_{α−1})}` is permissible for `J'` if and only if
`{(R_α, P_{α−1})}` is so for `J`" (Remark 1 of §5, p. 226, at every stage, with
`J'_α = J_αR'_α` and `P'_α = P_αR'_α`). -/
theorem isPermissibleFor_map_iff_of_isLiftAlong (α : R →+* R') [IsLocalHom α]
    (S : MonoidalSequence.{u})
    (e : R ≃+* S.ring 0) (hS : S.HasRegularCenters) (S' : MonoidalSequence.{u})
    (e' : R' ≃+* S'.ring 0) (φ : ∀ n, S.ring n →+* S'.ring n)
    (h0 : (φ 0).comp (e : R →+* S.ring 0) = (e' : R' →+* S'.ring 0).comp α)
    (hφ : S.IsLiftAlong S' φ)
    (hmaps : ∀ n, haveI := hφ.isLocalHom n; RingHom.MapsRSOP (φ n)) (J : Ideal R) :
    S'.IsPermissibleFor (J.map α) e' ↔ S.IsPermissibleFor J e := by
  have hstrict := strictAlong_map_eq_map_of_isLiftAlong α S e hS S' e' φ h0 hφ hmaps J
  unfold MonoidalSequence.IsPermissibleFor
  refine forall_congr' fun n => ?_
  have hn := hφ.isLocalHom n
  rw [hstrict n, hφ.center_eq n]
  have hP : S.center n = ⊤ ∨ (S.center n).IsPrime := (hS n).2.imp id fun h => h.1
  exact (isPermissibleCenter_map_iff_of_eq_top_or_isPrime (φ n) (hmaps n) _ _ hP).symm

/-- Remark 1, p. 263: "so that we have `ν*(J_α) = ν*(J)` if and only if `ν*(J'_α) = ν*(J')`, and
that `τ^{(a)}(J_α) = τ^{(a)}(J)` if and only if `τ^{(a)}(J'_α) = τ^{(a)}(J')` provided
`ν*(J_α) = ν*(J)`. (See Corollary to Lemma 2, § 1, and Lemma 13, § 4.)" -/
theorem nuStar_tau_map_iff_of_isLiftAlong [Hironaka.HironakaCitedResults.{u}] (α : R →+* R') [IsLocalHom α]
    (hα : RingHom.MapsRSOP α) (hsep : RingHom.IsResiduallySeparable α) (S : MonoidalSequence.{u})
    (e : R ≃+* S.ring 0) (hS : S.HasRegularCenters) (S' : MonoidalSequence.{u})
    (e' : R' ≃+* S'.ring 0) (φ : ∀ n, S.ring n →+* S'.ring n)
    (h0 : (φ 0).comp (e : R →+* S.ring 0) = (e' : R' →+* S'.ring 0).comp α)
    (hφ : S.IsLiftAlong S' φ)
    (hprop : ∀ n, haveI := hφ.isLocalHom n
      RingHom.MapsRSOP (φ n) ∧ RingHom.IsResiduallySeparable (φ n)) (J : Ideal R) :
    (∀ n, nuStar (S.ring n) (S.strictAlong (J.map e) n) = nuStar R J ↔
      nuStar (S'.ring n) (S'.strictAlong ((J.map α).map e') n) = nuStar R' (J.map α)) ∧
    (∀ n, nuStar (S.ring n) (S.strictAlong (J.map e) n) = nuStar R J →
      ∀ a, 1 ≤ a → a ≤ t R J →
        (tau (S.ring n) (S.strictAlong (J.map e) n) a = tau R J a ↔
          tau (S'.ring n) (S'.strictAlong ((J.map α).map e') n) a = tau R' (J.map α) a)) := by
  have hstrict := strictAlong_map_eq_map_of_isLiftAlong α S e hS S' e' φ h0 hφ
    (fun n => (hprop n).1) J
  refine ⟨fun n => ?_, fun n _ a ha _ => ?_⟩
  · have hn := hφ.isLocalHom n
    rw [hstrict n, ← nuStar_map_eq_of_mapsRSOP (φ n) (hprop n).1,
      ← nuStar_map_eq_of_mapsRSOP α hα J]
  · have hn := hφ.isLocalHom n
    rw [hstrict n, tau_map_of_mapsRSOP (φ n) (hprop n).1 (hprop n).2 _ a ha,
      tau_map_of_mapsRSOP α hα hsep J a ha]

/-- Remark 1, p. 263: "By Lemma 4, § 2, `R_α → R'_α` has the same properties as `R → R'`
for every `α`. Let `J` be an ideal in `R` and `J' = JR` [sic; read `JR'`]. Then `{(R'_α, P'_{α−1})}` is permissible
for `J'` if and only if `{(R_α, P_{α−1})}` is so for `J`. Moreover, the strict transform `J'_α` of
`J'` in `R'_α` along `{(R'_α, P'_{α−1})}` is equal to `J_αR'_α` where `J_α` is the strict transform
of `J` in `R_α` along `{(R_α, P_{α−1})}`, by Corollary to Lemma 5, § 2, so that we have
`ν*(J_α) = ν*(J)` if and only if `ν*(J'_α) = ν*(J')`, and that `τ^{(a)}(J_α) = τ^{(a)}(J)` if and
only if `τ^{(a)}(J'_α) = τ^{(a)}(J')` provided `ν*(J_α) = ν*(J)`. (See Corollary to Lemma 2, § 1,
and Lemma 13, § 4.)"

The properties of every lift `{(R'_α, P'_{α−1})}` of a sequence in which every `R_α` is
residually algebraic over `R_{α−1}` ("Let us assume this"): the `R_α → R'_α` have the same
properties as `R → R'` (stage by stage by Lemma 4, `mapsRSOP_and_isResiduallySeparable_of_isCanonicalLift`),
the sequences are permissible simultaneously (Remark 1 of § 5, p. 226, at every stage), the strict
transforms correspond (Corollary to Lemma 5, § 2), and the equivalences of `ν*` and `τ^{(a)}`
follow (Corollary to Lemma 2, § 1, and Lemma 13, § 4). -/
theorem remark1_properties_of_isLiftAlong [Hironaka.HironakaCitedResults.{u}] {R R' : Type u} [CommRing R] [IsRegularLocalRing R]
    [CommRing R'] [IsRegularLocalRing R'] (α : R →+* R') [IsLocalHom α] (hα : RingHom.MapsRSOP α)
    (hsep : RingHom.IsResiduallySeparable α) (S : MonoidalSequence.{u}) (e : R ≃+* S.ring 0)
    (hS : S.HasRegularCenters) (S' : MonoidalSequence.{u}) (e' : R' ≃+* S'.ring 0)
    (φ : ∀ n, S.ring n →+* S'.ring n) (_hS' : S'.HasRegularCenters)
    (h0 : (φ 0).comp (e : R →+* S.ring 0) = (e' : R' →+* S'.ring 0).comp α)
    (hφ : S.IsLiftAlong S' φ)
    (hres : ∀ n, RingHom.IsResiduallyAlgebraic (R := S.ring n) (R' := (S.transform n).ring)
        (S.transform n).toRing) :
    (∀ n, haveI := hφ.isLocalHom n
      RingHom.MapsRSOP (φ n) ∧ RingHom.IsResiduallySeparable (φ n)) ∧
    ∀ J : Ideal R,
      (S'.IsPermissibleFor (J.map α) e' ↔ S.IsPermissibleFor J e) ∧
      (∀ n, S'.strictAlong ((J.map α).map e') n = (S.strictAlong (J.map e) n).map (φ n)) ∧
      (∀ n, nuStar (S.ring n) (S.strictAlong (J.map e) n) = nuStar R J ↔
        nuStar (S'.ring n) (S'.strictAlong ((J.map α).map e') n) = nuStar R' (J.map α)) ∧
      (∀ n, nuStar (S.ring n) (S.strictAlong (J.map e) n) = nuStar R J →
        ∀ a, 1 ≤ a → a ≤ t R J →
          (tau (S.ring n) (S.strictAlong (J.map e) n) a = tau R J a ↔
            tau (S'.ring n) (S'.strictAlong ((J.map α).map e') n) a =
              tau R' (J.map α) a)) := by
  have hprop := mapsRSOP_and_isResiduallySeparable_of_isLiftAlong α hα hsep S e hS S' e' φ h0
    hφ hres
  have hmaps : ∀ n, haveI := hφ.isLocalHom n; RingHom.MapsRSOP (φ n) := fun n => (hprop n).1
  refine ⟨hprop, fun J => ⟨?_, ?_, ?_⟩⟩
  · exact isPermissibleFor_map_iff_of_isLiftAlong α S e hS S' e' φ h0 hφ hmaps J
  · exact strictAlong_map_eq_map_of_isLiftAlong α S e hS S' e' φ h0 hφ hmaps J
  · exact nuStar_tau_map_iff_of_isLiftAlong α hα hsep S e hS S' e' φ h0 hφ hprop J

end Sequence

/-! ### Remark 1 (pp. 262–263) -/

/-- Remark 1, pp. 262–263 (its statement; the rest of the remark is summarized below): "Let `R → R'`
be a local homomorphism of regular local rings such that a regular system of parameters of `R` is
transformed into such a system of parameters of `R'`, and that the residue field of `R'` is
separable over that of `R`. Given a sequence `{(R_α, P_{α−1})}` of monoidal transforms of `R`,
there exists always a sequence `{(R'_α, P'_{α−1})}` of monoidal transforms of `R'` such that we
have a commutative diagram of canonical local homomorphisms [`R_{α−1} → R'_{α−1}`, `R_α → R'_α`]
for all `α`, where `R₀ = R`, `R'₀ = R'` and `P'_{α−1} = P_{α−1}R'` [sic; read `P_{α−1}R'_{α−1}`].
If `R_α` is residually algebraic over `R_{α−1}`, then `R'_α` is so over `R'_{α−1}`. Let us assume
this."

The remark goes on: by Lemma 4, §2, every `R_α → R'_α` has the same properties as `R → R'`; for an
ideal `J` of `R` and `J' = JR'` (printed `J' = JR`), `{(R'_α, P'_{α−1})}` is permissible for `J'` if
and only if `{(R_α, P_{α−1})}` is so for `J`; the strict transforms satisfy `J'_α = J_αR'_α`
(Corollary to Lemma 5, §2), so that `ν*(J_α) = ν*(J)` if and only if `ν*(J'_α) = ν*(J')`, and,
provided this holds, `τ^{(a)}(J_α) = τ^{(a)}(J)` if and only if `τ^{(a)}(J'_α) = τ^{(a)}(J')`
(Corollary to Lemma 2, §1, and Lemma 13, §4).  It ends: "We can easily see that if an element `f` of
`R` (viewed as an element of `R'`) is `J'`-stable then `f` is `J`-stable."

(Formalization notes.
* The first part is stated for every sequence `S` of monoidal transforms of `R` (with
  `R ≃+* S.ring 0` and condition (1)): the existence of `S'` with a diagram
  (`MonoidalSequence.IsLiftAlong`, `R₀ → R'₀` being `R → R'`), and then the properties of *every*
  such `S'`; "Let us assume this" is the hypothesis that every `R_{α+1}` is residually algebraic
  over `R_α`; "`R_α → R'_α` has the same properties as `R → R'`" is `MapsRSOP` and residual
  separability.
* The two misprints `P_{α−1}R'` and `J' = JR` are read as `P_{α−1}R'_{α−1}` and `J' = JR'`.
* The strict transforms along the sequences are `strictAlong` (the sequences of monoidal
  transforms of Remark 1 carry no ideal); `τ^{(a)}` is compared for `1 ≤ a ≤ t(J)`.
* Two sentences of the remark are stated by the paper without proof or citation: "If `R_α` is
  residually algebraic over `R_{α−1}`, then `R'_α` is so over `R'_{α−1}`" and the last sentence.
  No formalized argument uses them, and they are not part of the Lean statement.)

Proof status. The existence of `S'` (`exists_isLiftAlong_remark1`) and the properties of every `S'`
(`remark1_properties_of_isLiftAlong`) are proved along the pointers of the text: Lemma 4 of §2 for
`R_α → R'_α` (with the dimension count of Lemma 4 (1), which is where "Let us assume this" enters),
Remark 1 of §5 (p. 226) for the permissibility, the Corollary to Lemma 5 of §2 for the strict
transforms, the Corollary to Lemma 2 of §1 and Lemma 13 of §4 for `ν*` and `τ^{(a)}`. -/
@[blueprint "rem:III.9-1"
  (statement := /-- Let $R\to R'$ be a local homomorphism of regular local rings such that a
    regular system of parameters of $R$ is transformed into such a system of parameters of
    $R'$ (\cref{def:III.rsop-map}), and that the residue field of $R'$ is separable over that of
    $R$ (\cref{def:III.2-residually}). Given a sequence $\{(R_\alpha,P_{\alpha-1})\}$ of
    monoidal transforms of $R$ (\cref{def:III.9-sequence}), there exists always a sequence
    $\{(R'_\alpha,P'_{\alpha-1})\}$ of monoidal transforms of $R'$ such that we have a
    commutative diagram of canonical local homomorphisms $R_{\alpha-1}\to R'_{\alpha-1}$,
    $R_\alpha\to R'_\alpha$ (\cref{def:III.2-canonical}) for all $\alpha$, where $R_0=R$,
    $R'_0=R'$ and $P'_{\alpha-1}=P_{\alpha-1}R'$ [sic; read $P_{\alpha-1}R'_{\alpha-1}$]. If
    $R_\alpha$ is residually algebraic over $R_{\alpha-1}$, then $R'_\alpha$ is so over
    $R'_{\alpha-1}$. Let us assume this. (Remark 1, pp.~262--263; the rest of the remark is
    summarized.) Then, by Lemma~4, \S2 (\cref{lem:III.4}), every $R_\alpha\to R'_\alpha$ has the
    same properties as $R\to R'$. For an ideal $J$ of $R$ and $J'=JR'$ (printed $J'=JR$),
    $\{(R'_\alpha,P'_{\alpha-1})\}$ is permissible for $J'$ if and only if
    $\{(R_\alpha,P_{\alpha-1})\}$ is so for $J$ (\cref{def:III.9-permissible-sequence}); the strict
    transforms (\cref{def:III.9-strict-sequence}) satisfy $J'_\alpha=J_\alpha R'_\alpha$, so that
    $\nu^*(J_\alpha)=\nu^*(J)$ if and only if $\nu^*(J'_\alpha)=\nu^*(J')$, and, provided this
    holds, $\tau^{(a)}(J_\alpha)=\tau^{(a)}(J)$ if and only if $\tau^{(a)}(J'_\alpha)=\tau^{(a)}(J')$
    (Corollary to Lemma~2, \S1, and Lemma~13, \S4). Finally, ``We can easily see that if an
    element $f$ of $R$ (viewed as an element of $R'$) is $J'$-stable then $f$ is $J$-stable''
    (\cref{def:III.11}).

    (Formalization note: the properties are asserted for every sequence of monoidal transforms
    of $R'$ with such a diagram; ``Let us assume this'' is the hypothesis that $R_\alpha$ is
    residually algebraic over $R_{\alpha-1}$ for all $\alpha$; the index $a$ runs over
    $1\le a\le t(J)$.)

    The sentence on residual algebraicity of $R'_\alpha$ and the last sentence are stated in
    the paper without proof or citation. No formalized argument uses them, and they are not part
    of the Lean statement. -/)
  (proof := /-- The existence of the sequence $\{(R'_\alpha,P'_{\alpha-1})\}$ and of the diagram is
    built stage by stage from \cref{lem:III.4}: if $R_{\alpha-1}\to R'_{\alpha-1}$ transforms a
    regular system of parameters into one and has separable residue field extension, a canonical
    lift $R'_\alpha$ with the same properties is chosen (with a prime of the closed fibre
    minimal over the maximal ideal, so that $\dim R'_\alpha=\dim R_\alpha$). By Lemma~4, \S2
    (\cref{lem:III.4}), applied inductively to $R_{\alpha-1}\to R'_{\alpha-1}$ (part~(1) gives
    $\dim R'_\alpha=\dim R_\alpha$ when $R_\alpha$ is residually algebraic over $R_{\alpha-1}$),
    $R_\alpha\to R'_\alpha$ transforms a regular system of parameters into such a system and
    has separable residue field extension. The permissibility equivalence follows from Remark~1
    of \S5 (\cref{rem:III.5-1}) applied to $R_{\alpha-1}\to R'_{\alpha-1}$, $P'=PR'$ and
    $J'_{\alpha-1}=J_{\alpha-1}R'_{\alpha-1}$. The equality $J'_\alpha=J_\alpha R'_\alpha$ is
    the Corollary to Lemma~5, \S2 (\cref{cor:III.lem5}), so that the assertions on $\nu^*$ and
    $\tau^{(a)}$ follow from the Corollary to Lemma~2, \S1 (\cref{cor:III.lem2}), and Lemma~13,
    \S4 (\cref{lem:III.13}). -/)
  (latexEnv := "remark")]
theorem remark1_sequence_lift [Hironaka.HironakaCitedResults.{u}] {R R' : Type u} [CommRing R] [IsRegularLocalRing R] [CommRing R']
    [IsRegularLocalRing R'] (α : R →+* R') [IsLocalHom α] (hα : RingHom.MapsRSOP α)
    (hsep : RingHom.IsResiduallySeparable α) :
    ∀ (S : MonoidalSequence.{u}) (e : R ≃+* S.ring 0), S.HasRegularCenters →
      (∃ (S' : MonoidalSequence.{u}) (e' : R' ≃+* S'.ring 0) (φ : ∀ n, S.ring n →+* S'.ring n),
        S'.HasRegularCenters ∧
          (φ 0).comp (e : R →+* S.ring 0) = (e' : R' →+* S'.ring 0).comp α ∧
          S.IsLiftAlong S' φ) ∧
      ∀ (S' : MonoidalSequence.{u}) (e' : R' ≃+* S'.ring 0) (φ : ∀ n, S.ring n →+* S'.ring n),
        S'.HasRegularCenters →
        (φ 0).comp (e : R →+* S.ring 0) = (e' : R' →+* S'.ring 0).comp α →
        ∀ hφ : S.IsLiftAlong S' φ,
        (∀ n, RingHom.IsResiduallyAlgebraic (R := S.ring n) (R' := (S.transform n).ring)
            (S.transform n).toRing) →
          (∀ n, haveI := hφ.isLocalHom n
            RingHom.MapsRSOP (φ n) ∧ RingHom.IsResiduallySeparable (φ n)) ∧
          ∀ J : Ideal R,
            (S'.IsPermissibleFor (J.map α) e' ↔ S.IsPermissibleFor J e) ∧
            (∀ n, S'.strictAlong ((J.map α).map e') n = (S.strictAlong (J.map e) n).map (φ n)) ∧
            (∀ n, nuStar (S.ring n) (S.strictAlong (J.map e) n) = nuStar R J ↔
              nuStar (S'.ring n) (S'.strictAlong ((J.map α).map e') n) =
                nuStar R' (J.map α)) ∧
            (∀ n, nuStar (S.ring n) (S.strictAlong (J.map e) n) = nuStar R J →
              ∀ a, 1 ≤ a → a ≤ t R J →
                (tau (S.ring n) (S.strictAlong (J.map e) n) a = tau R J a ↔
                  tau (S'.ring n) (S'.strictAlong ((J.map α).map e') n) a =
                    tau R' (J.map α) a)) :=
  fun S e hS => ⟨exists_isLiftAlong_remark1 α hα hsep S e hS,
    fun S' e' φ hS' h0 hφ hres =>
      remark1_properties_of_isLiftAlong α hα hsep S e hS S' e' φ hS' h0 hφ hres⟩

end Hironaka
