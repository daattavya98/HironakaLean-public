/-
Copyright (c) 2026 Daattavya Aggarwal, Minhyong Kim, Oisin Kim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daattavya Aggarwal, Minhyong Kim, Oisin Kim
-/
module

public import Mathlib.AlgebraicGeometry.Birational.RationalMap
public import Architect
public import Hironaka.Ch0.RationalApplication
public import Hironaka.Compat.FunctionFieldMap
public import Hironaka.Compat.PairSuccession
public import Mathlib.AlgebraicGeometry.Restrict
public import Hironaka.Statements

/-!
# Pairs `(X, θ)`, the rational application of two pairs, domination and `𝔐(L/B)` (Ch. 0 §5, p. 144)

> Let `B` be a field of characteristic zero as above, and `L` a field containing `B` and finitely generated over `B`.
> Let us consider the pairs `(X, θ)` of reduced and irreducible algebraic `B`-schemes `X` and `B`-isomorphisms `θ` of `L`
> to the functions fields of `X`.  If `(X₁, θ₁)` and `(X₂, θ₂)` are two of such pairs, then there exists a unique rational
> application `f` of `X₁` to `X₂` which induces the isomorphism `θ₁∘θ₂⁻¹` of the function field of `X₂` to that of `X₁`.
> We call `f` the rational application of `(X₁, θ₁)` to `(X₂, θ₂)`.  If `f` is a morphism, then we say that `(X₁, θ₁)`
> dominates `(X₂, θ₂)`.  (p. 144)

> If `(X, θ)` is as above, and if `f : X' → X` is a monoidal transformation with center nowhere dense in `X`, we have a
> unique `B`-isomorphism `θ'` of `L` to the function field of `X'` such that `θ∘θ'⁻¹` is induced by `f`.  By abuse of
> language, we say that `f : (X', θ') → (X, θ)` is the monoidal transformation of `(X, θ)`.  Let `𝔐(L/B)` denote the class
> of those pairs `(X, θ)` with proper `X` (i.e., the structural morphisms of `X` to `Spec(B)` are proper).  (p. 144)

Encoding: a pair is `FunctionFieldPair B L`; the rational application of two pairs is Mathlib's `Scheme.RationalMap`,
obtained by `RationalMap.ofFunctionField` from the morphism `Spec K(X₁) → Spec K(X₂) → X₂` induced by `θ₁∘θ₂⁻¹`, so that
the paper's "unique rational application which induces the isomorphism" is `RationalMap.eq_of_fromFunctionField_eq`;
"`(X₁, θ₁)` dominates `(X₂, θ₂)`" is "the rational application is a morphism" (`RationalMap.IsMorphism`, p. 139); `𝔐(L/B)`
is `FunctionFieldPair.IsProper`.  "Obtained from `(X, θ)` by a finite succession of monoidal transformations with
non-singular centers" is `FunctionFieldPair.IsObtainedBy` (nowhere dense centers, non-singular centers, the structure
morphism is the composite, and the rational application of the new pair to the old one is the composite morphism: the
printed "`θ∘θ'⁻¹` is induced by `f`", for the whole succession).
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Scheme

namespace Hironaka

universe u

section SpecStalk

variable {X Y : Scheme.{u}}

/-- A morphism of irreducible schemes sending generic point to generic point: composing with the canonical morphism
`Spec K(X) ⟶ X` is the same as composing the map of function fields with `Spec K(Y) ⟶ Y`. -/
theorem fromSpecStalk_genericPoint_comp [IrreducibleSpace X] [IrreducibleSpace Y] (f : X ⟶ Y)
    (h : f (genericPoint X) = genericPoint Y) :
    X.fromSpecStalk (genericPoint X) ≫ f =
      Spec.map (functionFieldMap f h) ≫ Y.fromSpecStalk (genericPoint Y) := by
  rw [← Scheme.SpecMap_stalkMap_fromSpecStalk f (x := genericPoint X), functionFieldMap, Spec.map_comp,
    Category.assoc]
  congr 1
  exact (Scheme.SpecMap_stalkSpecializes_fromSpecStalk (X := Y) (specializes_of_eq h)).symm


end SpecStalk


namespace FunctionFieldPair

variable {B L : Type u} [Field B] [Field L] [Algebra B L]







/-- The rational application of two pairs induces `θ₁∘θ₂⁻¹` on the function fields. -/
theorem fromFunctionField_ratApp (P Q : FunctionFieldPair B L) :
    (P.ratApp Q).fromFunctionField = P.ratFn Q :=
  RationalMap.fromFunctionField_ofFunctionField _ _ _ _

/-- Uniqueness of the rational application of two pairs (p. 144: "there exists a unique rational application `f` of `X₁`
to `X₂` which induces the isomorphism `θ₁∘θ₂⁻¹`"). -/
theorem eq_ratApp_of_fromFunctionField_eq (P Q : FunctionFieldPair B L) {f : P.X ⤏ Q.X}
    (h : f.fromFunctionField = P.ratFn Q) : f = P.ratApp Q :=
  RationalMap.eq_of_fromFunctionField_eq _ _ (h.trans (P.fromFunctionField_ratApp Q).symm)

/-- The rational application of two pairs is a `B`-rational application. -/
theorem ratApp_compHom (P Q : FunctionFieldPair B L) :
    (P.ratApp Q).compHom Q.p = P.p.toRationalMap :=
  (RationalMap.equivFunctionField P.p Q.p ⟨P.ratFn Q, P.ratFn_comp Q⟩).2

/-- The restriction to the function field of the class of a morphism. -/
theorem fromFunctionField_toRationalMap_hom {X Y : Scheme.{u}} [IrreducibleSpace X] (g : X ⟶ Y) :
    g.toRationalMap.fromFunctionField = X.fromSpecStalk (genericPoint X) ≫ g :=
  Scheme.PartialMap.fromSpecStalkOfMem_toPartialMap g (genericPoint X)

/-- A morphism `g : X₁ ⟶ X₂` represents the rational application of two pairs iff it induces `θ₁∘θ₂⁻¹`. -/
theorem ratApp_eq_toRationalMap_iff (P Q : FunctionFieldPair B L) (g : P.X ⟶ Q.X) :
    P.ratApp Q = g.toRationalMap ↔ P.X.fromSpecStalk (genericPoint P.X) ≫ g = P.ratFn Q := by
  constructor
  · intro h
    rw [← fromFunctionField_toRationalMap_hom, ← h, fromFunctionField_ratApp]
  · intro h
    exact (P.eq_ratApp_of_fromFunctionField_eq Q (by rw [fromFunctionField_toRationalMap_hom, h])).symm

/-- The scheme of a pair is separated (it is separated over `Spec B`). -/
instance (P : FunctionFieldPair B L) : P.X.IsSeparated := by
  rw [Scheme.isSeparated_iff, ← Limits.terminal.comp_from P.p]
  infer_instance



/-- A morphism inducing `θ₁∘θ₂⁻¹` on the function fields shows that `(X₁, θ₁)` dominates `(X₂, θ₂)`. -/
theorem dominates_of_fromSpecStalk_comp_eq (P Q : FunctionFieldPair B L) (g : P.X ⟶ Q.X)
    (h : P.X.fromSpecStalk (genericPoint P.X) ≫ g = P.ratFn Q) : P.Dominates Q := by
  unfold Dominates
  rw [(P.ratApp_eq_toRationalMap_iff Q g).mpr h]
  exact RationalMap.isMorphism_toRationalMap g

/-- If `(X₁, θ₁)` dominates `(X₂, θ₂)` there is a `B`-morphism `X₁ ⟶ X₂` which is the rational application and induces
`θ₁∘θ₂⁻¹`. -/
theorem Dominates.exists_hom {P Q : FunctionFieldPair B L} (h : P.Dominates Q) :
    ∃ g : P.X ⟶ Q.X, g.toRationalMap = P.ratApp Q ∧ g ≫ Q.p = P.p ∧
      P.X.fromSpecStalk (genericPoint P.X) ≫ g = P.ratFn Q := by
  obtain ⟨g, h1⟩ : ∃ g : P.X ⟶ Q.X, g.toRationalMap = P.ratApp Q := ⟨h.toHom, h.toHom_toRationalMap⟩
  refine ⟨g, h1, ?_, (P.ratApp_eq_toRationalMap_iff Q g).mp h1.symm⟩
  refine RationalMap.eq_of_toRationalMap_eq ?_
  have h2 : (g ≫ Q.p).toRationalMap = g.toRationalMap.compHom Q.p := rfl
  rw [h2, h1]
  exact P.ratApp_compHom Q

/-- A morphism inducing `θ₁∘θ₂⁻¹` sends the generic point to the generic point. -/
theorem map_genericPoint_of_fromSpecStalk_comp_eq (P Q : FunctionFieldPair B L) (g : P.X ⟶ Q.X)
    (h : P.X.fromSpecStalk (genericPoint P.X) ≫ g = P.ratFn Q) : g (genericPoint P.X) = genericPoint Q.X := by
  let c : Spec (P.X.presheaf.stalk (genericPoint P.X)) := IsLocalRing.closedPoint _
  have h1 : g (genericPoint P.X) = (P.X.fromSpecStalk (genericPoint P.X) ≫ g) c := by
    rw [Scheme.Hom.comp_apply]
    exact congrArg g Scheme.fromSpecStalk_closedPoint.symm
  have : Subsingleton (Spec Q.X.functionField) := by
    have : Subsingleton (PrimeSpectrum Q.X.functionField) := inferInstance
    exact this
  have h2 : (Spec.map (P.thetaHom Q)) c = IsLocalRing.closedPoint (Q.X.presheaf.stalk (genericPoint Q.X)) :=
    Subsingleton.elim _ _
  rw [h1, h, ratFn, Scheme.Hom.comp_apply, h2]
  exact Scheme.fromSpecStalk_closedPoint

/-- A morphism inducing `θ₁∘θ₂⁻¹` has the map of function fields `θ₁∘θ₂⁻¹`. -/
theorem functionFieldMap_eq_thetaHom (P Q : FunctionFieldPair B L) (g : P.X ⟶ Q.X)
    (h : P.X.fromSpecStalk (genericPoint P.X) ≫ g = P.ratFn Q)
    (hη : g (genericPoint P.X) = genericPoint Q.X) : functionFieldMap g hη = P.thetaHom Q := by
  have h1 := fromSpecStalk_genericPoint_comp g hη
  rw [h, ratFn] at h1
  exact Spec.map_injective ((cancel_mono (Q.X.fromSpecStalk (genericPoint Q.X))).mp h1.symm)

/-- A pair obtained from `(X, θ)` by a succession of monoidal transformations with nowhere dense centers (p. 144: "we have
a unique `B`-isomorphism `θ'` of `L` to the function field of `X'` such that `θ∘θ'⁻¹` is induced by `f`", iterated):
`θ' = (K(X) ≃ K(Y)) ∘ θ`. -/
noncomputable def ofSuccession [Hironaka.HironakaCitedResults.{u}] (P : FunctionFieldPair B L) {Y : Scheme.{u}} (s : MonoidalSuccession P.X Y)
    (hs : s.NowhereDenseCenters) : FunctionFieldPair B L :=
  have := s.isIntegral_of_nowhereDenseCenters hs
  { X := Y
    p := s.composite ≫ P.p
    isIntegral := this
    locallyOfFiniteType := s.locallyOfFiniteType_composite_comp P.p
    quasiCompact := s.quasiCompact_composite_comp P.p
    isSeparated := s.isSeparated_composite_comp P.p
    θ := P.θ.trans (s.functionFieldIso hs)
    θ_algebraMap := fun b => by
      change s.functionFieldIso hs (P.θ (algebraMap B L b)) = _
      rw [P.θ_algebraMap b]
      exact s.functionFieldIso_algebraMap hs P.p b }


/-- The isomorphism `θ'∘θ⁻¹` of the function fields of `ofSuccession` and of the original pair is the map of function
fields of the composite. -/
theorem thetaHom_ofSuccession [Hironaka.HironakaCitedResults.{u}] (P : FunctionFieldPair B L) {Y : Scheme.{u}} [IsIntegral Y]
    (s : MonoidalSuccession P.X Y) (hs : s.NowhereDenseCenters) (hη : s.composite (genericPoint Y) = genericPoint P.X) :
    (P.ofSuccession s hs).thetaHom P = functionFieldMap s.composite hη := by
  ext x
  exact (RingEquiv.trans_apply P.θ (s.functionFieldIso hs) (P.θ.symm x)).trans
    (by rw [RingEquiv.apply_symm_apply]; rfl)

/-- The pair `ofSuccession` is obtained from `(X, θ)` by the succession. -/
theorem ofSuccession_isObtainedBy [Hironaka.HironakaCitedResults.{u}] (P : FunctionFieldPair B L) {Y : Scheme.{u}} (s : MonoidalSuccession P.X Y)
    (hs : s.NowhereDenseCenters) (hn : s.HasNonsingularCenters) : P.IsObtainedBy (P.ofSuccession s hs) s := by
  have : IsIntegral Y := s.isIntegral_of_nowhereDenseCenters hs
  refine ⟨hs, hn, rfl, ?_⟩
  rw [ratApp_eq_toRationalMap_iff]
  have hη := s.composite_genericPoint hs
  change Y.fromSpecStalk (genericPoint Y) ≫ s.composite = (P.ofSuccession s hs).ratFn P
  rw [fromSpecStalk_genericPoint_comp s.composite hη, ratFn]
  congr 1
  exact congrArg Spec.map (thetaHom_ofSuccession P s hs hη).symm

/-- The pair `ofSuccession` of a proper pair is proper (so `𝔐(L/B)` is stable under such successions). -/
theorem isProper_ofSuccession [Hironaka.HironakaCitedResults.{u}] {P : FunctionFieldPair B L} (hP : P.IsProper) {Y : Scheme.{u}}
    (s : MonoidalSuccession P.X Y) (hs : s.NowhereDenseCenters) : (P.ofSuccession s hs).IsProper := by
  have : AlgebraicGeometry.IsProper P.p := hP
  exact s.isProper_composite_comp P.p

/-- A pair obtained from a proper pair is proper. -/
theorem IsObtainedBy.isProper [Hironaka.HironakaCitedResults.{u}] {P Q : FunctionFieldPair B L} {s : MonoidalSuccession P.X Q.X}
    (h : P.IsObtainedBy Q s) (hP : P.IsProper) : Q.IsProper := by
  have : AlgebraicGeometry.IsProper P.p := hP
  change AlgebraicGeometry.IsProper Q.p
  rw [h.2.2.1]
  exact s.isProper_composite_comp P.p

/-- A pair obtained from a non-singular pair by a succession with non-singular centers is non-singular (p. 144 (1),
"If `X₁` is non-singular, so is `X'₁`"). -/
theorem IsObtainedBy.isNonsingular {P Q : FunctionFieldPair B L} {s : MonoidalSuccession P.X Q.X}
    (h : P.IsObtainedBy Q s) (hP : P.X.IsNonsingular) : Q.X.IsNonsingular :=
  s.isNonsingular_of_hasNonsingularCenters hP h.2.1

/-- A pair is obtained from itself by the empty succession. -/
theorem isObtainedBy_refl (P : FunctionFieldPair B L) : P.IsObtainedBy P (MonoidalSuccession.nil P.X) := by
  refine ⟨trivial, trivial, by simp, ?_⟩
  rw [ratApp_eq_toRationalMap_iff]
  have : P.thetaHom P = 𝟙 _ := by
    ext x
    simp [thetaHom_apply]
  simp [ratFn, this]

/-- Concatenation: a pair obtained from a pair obtained from `(X, θ)` is obtained from `(X, θ)`. -/
theorem IsObtainedBy.append {P Q R : FunctionFieldPair B L} {s : MonoidalSuccession P.X Q.X}
    {s' : MonoidalSuccession Q.X R.X} (h : P.IsObtainedBy Q s) (h' : Q.IsObtainedBy R s') :
    P.IsObtainedBy R (s.append s') := by
  refine ⟨(s.nowhereDenseCenters_append s').mpr ⟨h.1, h'.1⟩, (s.hasNonsingularCenters_append s').mpr ⟨h.2.1, h'.2.1⟩,
    ?_, ?_⟩
  · rw [MonoidalSuccession.composite_append, h'.2.2.1, h.2.2.1, Category.assoc]
  · rw [MonoidalSuccession.composite_append, ratApp_eq_toRationalMap_iff]
    have hRQ := (ratApp_eq_toRationalMap_iff R Q s'.composite).mp h'.2.2.2
    have hQP := (ratApp_eq_toRationalMap_iff Q P s.composite).mp h.2.2.2
    have hθ : Q.thetaHom P ≫ R.thetaHom Q = R.thetaHom P := by
      ext x
      simp [thetaHom_apply]
    have e1 : R.ratFn Q = Spec.map (R.thetaHom Q) ≫ Q.X.fromSpecStalk (genericPoint Q.X) := rfl
    have e2 : Q.ratFn P = Spec.map (Q.thetaHom P) ≫ P.X.fromSpecStalk (genericPoint P.X) := rfl
    have e3 : R.ratFn P = Spec.map (R.thetaHom P) ≫ P.X.fromSpecStalk (genericPoint P.X) := rfl
    rw [← Category.assoc, hRQ, e1, Category.assoc, hQP, e2, e3, ← Category.assoc, ← Spec.map_comp, hθ]

end FunctionFieldPair

end Hironaka

universe u

namespace AlgebraicGeometry.Scheme.RationalMap

variable {X X' Y : Scheme.{u}} [IrreducibleSpace X] [IrreducibleSpace X']

/-- Composition with a morphism `a : X' ⟶ X` with dense preimages (p. 139) and the restriction to the function field: the
composite `Spec K(X') → X' → Y` of `f ∘ a` is `Spec K(X') → Spec K(X) → Y`, provided `a` sends the generic point to the
generic point. -/
theorem fromFunctionField_precomp (f : X ⤏ Y) (a : X' ⟶ X) (ha : a.PreimageDense)
    (hη : a (genericPoint X') = genericPoint X) :
    (f.precomp a ha).fromFunctionField =
      Spec.map (Hironaka.functionFieldMap a hη) ≫ f.fromFunctionField := by
  obtain ⟨g, rfl⟩ := Scheme.PartialMap.toRationalMap_surjective f
  rw [Scheme.RationalMap.precomp_toRationalMap]
  simp only [Scheme.RationalMap.fromFunctionField_toRationalMap]
  have key : ∀ (U : X.Opens) (h' : genericPoint X' ∈ a ⁻¹ᵁ U) (h : genericPoint X ∈ U),
      (a ⁻¹ᵁ U).fromSpecStalkOfMem (genericPoint X') h' ≫ (a ∣_ U) =
        Spec.map (Hironaka.functionFieldMap a hη) ≫ U.fromSpecStalkOfMem (genericPoint X) h := by
    intro U h' h
    rw [← cancel_mono U.ι, Category.assoc, Category.assoc, morphismRestrict_ι,
      Scheme.Opens.fromSpecStalkOfMem_ι, Scheme.Opens.fromSpecStalkOfMem_ι_assoc,
      Hironaka.fromSpecStalk_genericPoint_comp a hη]
  unfold Scheme.PartialMap.fromFunctionField Scheme.PartialMap.fromSpecStalkOfMem
  simp only [Scheme.PartialMap.precomp_domain, Scheme.PartialMap.precomp_hom, ← Category.assoc]
  exact congrArg (· ≫ g.hom) (key _ _ _)

end AlgebraicGeometry.Scheme.RationalMap
