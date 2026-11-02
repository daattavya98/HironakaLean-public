/-
Copyright (c) 2026 Daattavya Aggarwal, Minhyong Kim, Oisin Kim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daattavya Aggarwal, Minhyong Kim, Oisin Kim
-/
module

public import Mathlib.FieldTheory.SeparableClosure
public import Hironaka.Ch3.PermissibleEffects
public import Hironaka.Compat.BlowupStalkPoints

/-!
# Compatibility layer: the fibres of a morphism of monoidal transformations (Lemma (AB.2), p. 295)

Hironaka (p. 295): "The following lemma is an immediate consequence of Lemma 4, §2, Ch. III, and its
corollaries.  LEMMA (AB.2).  The morphism `c_s` induces a bijective mapping of the point sets
`ĝ_s⁻¹(x̂₀) → g_s⁻¹(x₀)`."

The one-step version, for a commutative square `f̂ ≫ c = c' ≫ f` of monoidal transformations with
`B̂ = c⁻¹(B)`: if `R = O_{Y,y}` (`y = c ŷ`) and `R̃ = O_{Ŷ,ŷ}` are regular, `c` transforms a regular
system of parameters of `R` into one of `R̃` and induces an isomorphism of the residue fields, then
`c'` maps the points of `Ŷ'` over `ŷ` bijectively onto the points of `Y'` over `y`.

The proof is the count of Lemma 4 (1) of Ch. III, p. 212: the points of `Y'` over `y` are the monoidal
transforms `R'` of `R` with center `P = B_y`, the points of `Ŷ'` over `ŷ` the monoidal transforms `R̃'`
of `R̃` with center `P̃ = P R̃`, and `c'` sends `R̃'` to the `R'` with `R' → R̃'` canonical.  The
number of `R̃'` admitting a canonical homomorphism from a given `R'` is at most the separable degree
`[k̃ : k]_s = 1` of the residue field extension (`subsingleton_canonicalTransforms…`, Lemma 4 (1)); this
gives injectivity of `c'` (a point of `Ŷ'` is determined by its local ring,
`MonoidalTransformation.eq_of_subring_eq`).  Surjectivity: every `R'` has a canonical lift `R̃'`
(`exists_isCanonicalLift`), which is the local ring of a point of `Ŷ'` over `ŷ`
(`MonoidalTransformation.pointOfMonoidalTransform`) mapped by `c'` to the point given by `R'`
(`MonoidalTransformation.c_pointOfMonoidalTransform_eq`).  The case `y ∉ B` (center `P = R`) needs no
count: there is a single point over `y` and a single one over `ŷ`
(`MonoidalTransformation.eq_of_stalkIdeal_eq_top`).
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing

universe u

namespace Hironaka

/-! ### Lemma 4 (1) of Ch. III with `k̃ = k`: the lift is unique -/

section RingLevel

variable {R Rb : Type u} [CommRing R] [IsRegularLocalRing R] [IsDomain R] [CommRing Rb]
  [IsRegularLocalRing Rb] [IsDomain Rb]

/-- Lemma 4 (1), p. 212: "if `R̃` is residually algebraic over `R` the number of `R̃'` does not
exceed the separable degree of the residue field of `R̃` over that of `R`"; here the residue field
map is surjective, hence bijective, so the separable degree is `1` and there is at most one `R̃'`
(Corollary 1 uses the same count for `R → R̂`). -/
theorem subsingleton_canonicalTransforms_of_surjective_residueField_map (α : R →+* Rb)
    [IsLocalHom α] (hα : RingHom.MapsRSOP α) (hres : Function.Surjective (ResidueField.map α))
    {P : Ideal R} (hP : P.IsPrime) (hS : IsRegularLocalRing (R ⧸ P)) (t : MonoidalTransform R P) :
    Subsingleton ↥(canonicalTransforms α (Pb := P.map α) t) := by
  have hbij : Function.Bijective (ResidueField.map α) := ⟨(ResidueField.map α).injective, hres⟩
  have halg : RingHom.IsResiduallyAlgebraic α := by
    let := (ResidueField.map α).toAlgebra
    refine ⟨fun x => ?_⟩
    obtain ⟨w, hw⟩ := hres x
    have : x = algebraMap (ResidueField R) (ResidueField Rb) w := hw.symm
    rw [this]
    exact isAlgebraic_algebraMap w
  have hL := RingHom.MapsRSOP.canonicalLift_properties α hα hP hS
  have hcard := (hL.2.1 t (Or.inl halg)).2.2 halg
  have hsd : letI := (ResidueField.map α).toAlgebra
      Field.sepDegree (ResidueField R) (ResidueField Rb) = 1 := by
    let := (ResidueField.map α).toAlgebra
    let e : ResidueField R ≃ₐ[ResidueField R] ResidueField Rb :=
      AlgEquiv.ofBijective (Algebra.ofId _ _) hbij
    rw [← Field.sepDegree_eq_of_equiv _ _ _ e, Field.sepDegree_self]
  rw [hsd] at hcard
  exact Cardinal.le_one_iff_subsingleton.mp hcard

/-- Two monoidal transforms `R̃'₁`, `R̃'₂` of `R̃` with center `P̃ = PR̃` admitting a canonical local
homomorphism from the same monoidal transform `R'` of `R` are equal (as subrings of the field of
quotients of `R̃`), when `R → R̃` induces an isomorphism of the residue fields. -/
theorem subring_eq_of_isCanonicalLift (α : R →+* Rb) [IsLocalHom α] (hα : RingHom.MapsRSOP α)
    (hres : Function.Surjective (ResidueField.map α)) {P : Ideal R} (hP : P.IsPrime)
    (hS : IsRegularLocalRing (R ⧸ P)) {Pb : Ideal Rb} (hPb : Pb = P.map α)
    (t : MonoidalTransform R P) (tb₁ tb₂ : MonoidalTransform Rb Pb) (β₁ : t.ring →+* tb₁.ring)
    (β₂ : t.ring →+* tb₂.ring) (h₁ : IsCanonicalLift α t tb₁ β₁) (h₂ : IsCanonicalLift α t tb₂ β₂) :
    tb₁.subring = tb₂.subring := by
  subst hPb
  have := subsingleton_canonicalTransforms_of_surjective_residueField_map α hα hres hP hS t
  have h := Subsingleton.elim
    (⟨tb₁.subring, tb₁, ⟨β₁, h₁⟩, rfl⟩ : ↥(canonicalTransforms α (Pb := P.map α) t))
    ⟨tb₂.subring, tb₂, ⟨β₂, h₂⟩, rfl⟩
  exact congrArg Subtype.val h

/-- Existence of a canonical lift (the existence half of Lemma 4, `exists_isCanonicalLift`), for a
center `P̃` given as `PR̃` up to an equation. -/
theorem exists_isCanonicalLift_of_eq (α : R →+* Rb) [IsLocalHom α] (hα : RingHom.MapsRSOP α)
    {P : Ideal R} {Pb : Ideal Rb} (hPb : Pb = P.map α) (t : MonoidalTransform R P) :
    ∃ (tb : MonoidalTransform Rb Pb) (β : t.ring →+* tb.ring), IsCanonicalLift α t tb β := by
  subst hPb
  exact exists_isCanonicalLift α hα t

end RingLevel

/-! ### The fibres of a morphism of monoidal transformations -/

private theorem isLocalHom_ringEquiv' {A B : Type u} [CommRing A] [CommRing B] (e : A ≃+* B) :
    IsLocalHom (e : A →+* B) :=
  ⟨fun a ha => by simpa using ha.map e.symm.toRingHom⟩

namespace MonoidalTransformation

variable {Y Yh : Scheme.{u}} {B : Subscheme Y} {Bh : Subscheme Yh}
  (t : MonoidalTransformation Y B) (th : MonoidalTransformation Yh Bh) (c : Yh ⟶ Y)
  (c' : th.X' ⟶ t.X') (hcomm : th.f ≫ c = c' ≫ t.f)

include hcomm in
/-- The commutative square of stalk maps of `f̂ ≫ c = c' ≫ f` at a point `ŷ'` with `f̂ ŷ' = ŷ` and
`f (c' ŷ') = c ŷ`: `O_{Y,cŷ} → O_{Y',c'ŷ'} → O_{Ŷ',ŷ'}` equals `O_{Y,cŷ} → O_{Ŷ,ŷ} → O_{Ŷ',ŷ'}`. -/
theorem stalkMapOf_square {ŷ : Yh} {ŷ' : th.X'} (h : th.f ŷ' = ŷ) (hy' : t.f (c' ŷ') = c ŷ) :
    t.f.stalkMapOf hy' ≫ c'.stalkMap ŷ' = c.stalkMap ŷ ≫ th.f.stalkMapOf h := by
  have hfg : (c' ≫ t.f) ŷ' = c ŷ := hy'
  have hfg' : (th.f ≫ c) ŷ' = c ŷ := by rw [hcomm]; exact hfg
  have e1 := Scheme.Hom.stalkMapOf_comp c' t.f (z := ŷ') (w := c' ŷ') rfl hy' hfg
  have e2 := Scheme.Hom.stalkMapOf_comp th.f c h (rfl : c ŷ = c ŷ) hfg'
  have e3 := Scheme.Hom.stalkMapOf_congr_hom hcomm hfg' hfg
  rw [Scheme.Hom.stalkMapOf_rfl] at e1 e2
  rw [← e1, ← e3, e2]

include hcomm in
/-- The local homomorphism of local rings `O_{Y',y'} → O_{Ŷ',ŷ'}` induced by `c'` is, between the
monoidal transforms `s` (of `O_{Y,cŷ}`, with `e : s ≃ O_{Y',y'}`) and `ŝ` (of `O_{Ŷ,ŷ}`, with
`ê : ŝ ≃ O_{Ŷ',ŷ'}`), a canonical local homomorphism in the sense of p. 211. -/
theorem exists_isCanonicalLift_of_point {ŷ : Yh} {ŷ' : th.X'} (h : th.f ŷ' = ŷ)
    {y' : t.X'} (hc : c' ŷ' = y') (hy' : t.f y' = c ŷ)
    [IsRegularLocalRing (Y.presheaf.stalk (c ŷ))] [IsDomain (Y.presheaf.stalk (c ŷ))]
    [IsRegularLocalRing (Yh.presheaf.stalk ŷ)] [IsDomain (Yh.presheaf.stalk ŷ)]
    {s : MonoidalTransform (Y.presheaf.stalk (c ŷ)) (B.stalkIdeal (c ŷ))}
    (e : s.ring ≃+* t.X'.presheaf.stalk y')
    (he : e.toRingHom.comp s.toRing = (t.f.stalkMapOf hy').hom)
    {sh : MonoidalTransform (Yh.presheaf.stalk ŷ) (Bh.stalkIdeal ŷ)}
    (eh : sh.ring ≃+* th.X'.presheaf.stalk ŷ')
    (heh : eh.toRingHom.comp sh.toRing = (th.f.stalkMapOf h).hom) :
    ∃ β : s.ring →+* sh.ring, IsCanonicalLift (c.stalkMap ŷ).hom s sh β := by
  subst hc
  have hsq := stalkMapOf_square t th c c' hcomm h hy'
  have : IsLocalHom (e : s.ring →+* t.X'.presheaf.stalk (c' ŷ')) := isLocalHom_ringEquiv' e
  have : IsLocalHom (eh.symm : th.X'.presheaf.stalk ŷ' →+* sh.ring) := isLocalHom_ringEquiv' eh.symm
  refine ⟨(eh.symm : th.X'.presheaf.stalk ŷ' →+* sh.ring).comp
    ((c'.stalkMap ŷ').hom.comp (e : s.ring →+* t.X'.presheaf.stalk (c' ŷ'))), ?_, ?_⟩
  · exact RingHom.isLocalHom_comp _ _
  · ext r
    have h1 := RingHom.congr_fun he r
    have h2 := RingHom.congr_fun heh ((c.stalkMap ŷ).hom r)
    have h3 := congrArg (fun g => g.hom r) hsq
    simp only [RingHom.coe_comp, Function.comp_apply, RingEquiv.toRingHom_eq_coe,
      RingHom.coe_coe, CommRingCat.hom_comp] at h1 h2 h3 ⊢
    rw [h1, h3, ← h2]
    simp

include hcomm in
/-- **One step of Lemma (AB.2)** (p. 295, first assertion), by the count of Lemma 4 (1) of Ch. III
(p. 212): let `f̂ ≫ c = c' ≫ f` be a commutative square of monoidal transformations with centers
`B̂ = c⁻¹(B)`, `Y` non-singular, `B` non-singular, and `ŷ` a point of `Ŷ` such that `R̃ = O_{Ŷ,ŷ}` is
regular, `c` transforms a regular system of parameters of `R = O_{Y,cŷ}` into one of `R̃` and induces
an isomorphism of the residue fields.  Then `c'` maps the points of `Ŷ'` over `ŷ` bijectively onto
the points of `Y'` over `c ŷ`. -/
theorem bijOn_fibre_of_comm (hBh : Bh = Subscheme.totalTransform c B) (hY : Y.IsNonsingular)
    (hB : B.IsNonsingular) (ŷ : Yh) [IsRegularLocalRing (Yh.presheaf.stalk ŷ)]
    (hα : RingHom.MapsRSOP (c.stalkMap ŷ).hom)
    (hres : Function.Surjective (ResidueField.map (c.stalkMap ŷ).hom)) :
    Set.BijOn c'.base (th.f.base ⁻¹' {ŷ}) (t.f.base ⁻¹' {c ŷ}) := by
  have hreg : IsRegularLocalRing (Y.presheaf.stalk (c ŷ)) := hY _
  have hdom : IsDomain (Y.presheaf.stalk (c ŷ)) := isDomain_of_isRegularLocalRing _
  have hdomh : IsDomain (Yh.presheaf.stalk ŷ) := isDomain_of_isRegularLocalRing _
  have hBhy : Bh.stalkIdeal ŷ = (B.stalkIdeal (c ŷ)).map (c.stalkMap ŷ).hom := by
    rw [hBh]; exact stalkIdeal_totalTransform c B ŷ
  have hmaps : ∀ ŷ' : th.X', th.f ŷ' = ŷ → t.f (c' ŷ') = c ŷ := fun ŷ' h => by
    rw [← Scheme.Hom.comp_apply, ← hcomm, Scheme.Hom.comp_apply, h]
  refine ⟨fun ŷ' h => hmaps ŷ' h, ?_, ?_⟩
  · -- injectivity
    intro ŷ₁ (h₁ : th.f ŷ₁ = ŷ) ŷ₂ (h₂ : th.f ŷ₂ = ŷ) (hc : c' ŷ₁ = c' ŷ₂)
    by_cases hyB : c ŷ ∈ B.pts
    · -- over the center: the count of Lemma 4 (1)
      have hP := Subscheme.isPrime_stalkIdeal_of_isNonsingular hB hyB
      have hS := Subscheme.isRegularLocalRing_quotient_of_isNonsingular hB hyB
      have hy₁ := hmaps ŷ₁ h₁
      obtain ⟨s, e, he⟩ := t.exists_monoidalTransform_stalk_of_eq hy₁
      obtain ⟨s₁, e₁, he₁⟩ := th.exists_monoidalTransform_stalk_of_eq h₁
      obtain ⟨s₂, e₂, he₂⟩ := th.exists_monoidalTransform_stalk_of_eq h₂
      obtain ⟨β₁, hβ₁⟩ := exists_isCanonicalLift_of_point t th c c' hcomm h₁ rfl hy₁ e he e₁ he₁
      obtain ⟨β₂, hβ₂⟩ := exists_isCanonicalLift_of_point t th c c' hcomm h₂ hc.symm hy₁ e he e₂ he₂
      exact th.eq_of_subring_eq h₁ h₂ (subring_eq_of_isCanonicalLift _ hα hres hP hS hBhy s s₁ s₂
        β₁ β₂ hβ₁ hβ₂) e₁ he₁ e₂ he₂
    · -- off the center: `P = R`, one point
      have hBh_top : Bh.stalkIdeal ŷ = ⊤ := by
        rw [hBhy, Subscheme.stalkIdeal_eq_top_of_notMem_pts hyB, Ideal.map_top]
      exact th.eq_of_stalkIdeal_eq_top hBh_top h₁ h₂
  · -- surjectivity
    intro y' (hy' : t.f y' = c ŷ)
    obtain ⟨s, e, he⟩ := t.exists_monoidalTransform_stalk_of_eq hy'
    obtain ⟨sh, β, hβ⟩ := exists_isCanonicalLift_of_eq (c.stalkMap ŷ).hom hα hBhy s
    have := hβ.isLocalHom
    have hcomm' : β.comp s.toRing = sh.toRing.comp (c.stalkMapOf (rfl : c ŷ = c ŷ)).hom := by
      rw [Scheme.Hom.stalkMapOf_rfl]; exact hβ.comm
    refine ⟨th.pointOfMonoidalTransform sh, th.f_pointOfMonoidalTransform sh, ?_⟩
    exact (t.c_pointOfMonoidalTransform_eq s th c c' hBh hcomm rfl sh β hcomm').trans
      (t.pointOfMonoidalTransform_eq s hy' e he)

end MonoidalTransformation

end Hironaka
