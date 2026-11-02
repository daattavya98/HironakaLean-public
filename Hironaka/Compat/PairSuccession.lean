/-
Copyright (c) 2026 Daattavya Aggarwal, Minhyong Kim, Oisin Kim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daattavya Aggarwal, Minhyong Kim, Oisin Kim
-/
module

public import Architect
public import Hironaka.Compat.NowhereDenseCenters
public import Hironaka.Compat.ProjectiveModelResolution
public import Hironaka.Compat.LocalizeSuccession
public import Hironaka.Ch0.BlowupLocal
public import Hironaka.Statements

/-!
# Successions of monoidal transformations of pairs `(X, θ)` (Ch. 0 §5, p. 144): bookkeeping

> If `(X, θ)` is as above, and if `f : X' → X` is a monoidal transformation with center nowhere dense in `X`, we have a
> unique `B`-isomorphism `θ'` of `L` to the function field of `X'` such that `θ ∘ θ'⁻¹` is induced by `f`.  By abuse of
> language, we say that `f : (X', θ') → (X, θ)` is the monoidal transformation of `(X, θ)`.  (p. 144)

This file collects, for a succession `s : MonoidalSuccession X Y` with nowhere dense centers (`NowhereDenseCenters`) of an
integral `B`-scheme, the facts that the paper uses tacitly when it says that `Y` with `θ'` is a pair again and that the
pair is in `𝔐(L/B)` when `X` is: the isomorphism of function fields induced by the composite (functoriality of
`functionFieldMap`, `functionFieldIso`), its compatibility with the `B`-structures, and with concatenation of
successions; the structure morphism `s.composite ≫ p` is locally of finite type, quasi-compact and separated (proper
when `p` is); a succession with non-singular centers of a non-singular scheme ends in a non-singular scheme; and a
strong resolution of an integral scheme has nowhere dense centers.  The pair `(Y, θ')` itself is built in
`Hironaka/Compat/FunctionFieldPair.lean`.  Encoding: bookkeeping of the encoding; not in the paper.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace Hironaka

universe u

section FunctionFieldMapComp

variable {X Y Z : Scheme.{u}} [IrreducibleSpace X] [IrreducibleSpace Y] [IrreducibleSpace Z]

/-- Functoriality of the map of function fields. -/
theorem functionFieldMap_comp (f : X ⟶ Y) (g : Y ⟶ Z) (hf : f (genericPoint X) = genericPoint Y)
    (hg : g (genericPoint Y) = genericPoint Z) (hfg : (f ≫ g) (genericPoint X) = genericPoint Z) :
    functionFieldMap (f ≫ g) hfg = functionFieldMap g hg ≫ functionFieldMap f hf := by
  simp only [functionFieldMap, Scheme.Hom.stalkMap_comp, Category.assoc]
  rw [← Scheme.Hom.stalkSpecializes_stalkMap_assoc g (f (genericPoint X)) (genericPoint Y)
    (specializes_of_eq hf), TopCat.Presheaf.stalkSpecializes_comp_assoc]
  rfl

/-- The map of function fields only depends on the morphism. -/
theorem functionFieldMap_congr {f g : X ⟶ Y} (e : f = g) (hf : f (genericPoint X) = genericPoint Y)
    (hg : g (genericPoint X) = genericPoint Y) : functionFieldMap f hf = functionFieldMap g hg := by
  subst e; rfl

end FunctionFieldMapComp

namespace MonoidalSuccession

variable {X Y Z : Scheme.{u}}

/-- Concatenation: the centers of `s.append s'` are nowhere dense iff those of `s` and `s'` are. -/
theorem nowhereDenseCenters_append (s : MonoidalSuccession X Y) (s' : MonoidalSuccession Y Z) :
    (s.append s').NowhereDenseCenters ↔ s.NowhereDenseCenters ∧ s'.NowhereDenseCenters := by
  induction s with
  | nil X => simp [NowhereDenseCenters]
  | cons B t rest ih => simp [NowhereDenseCenters, ih, and_assoc]

/-- Concatenation: the centers of `s.append s'` are non-singular iff those of `s` and `s'` are. -/
theorem hasNonsingularCenters_append (s : MonoidalSuccession X Y) (s' : MonoidalSuccession Y Z) :
    (s.append s').HasNonsingularCenters ↔ s.HasNonsingularCenters ∧ s'.HasNonsingularCenters := by
  induction s with
  | nil X => simp [HasNonsingularCenters]
  | cons B t rest ih => simp [HasNonsingularCenters, ih, and_assoc]

/-- The composite of a succession with nowhere dense centers of an integral scheme induces a bijection of function
fields. -/
theorem bijective_functionFieldMap_composite (s : MonoidalSuccession X Y) [IsIntegral X] [IsIntegral Y]
    (hs : s.NowhereDenseCenters) :
    Function.Bijective (functionFieldMap s.composite (s.composite_genericPoint hs)) := by
  revert ‹IsIntegral X› ‹IsIntegral Y›
  induction s with
  | nil X =>
    intro _ _
    have : functionFieldMap (nil X).composite ((nil X).composite_genericPoint hs) = 𝟙 _ := by
      simp only [functionFieldMap, composite_nil]
      simp
    rw [this]
    exact Function.bijective_id
  | cons D t rest ih =>
    intro _ _
    have hD := (Subscheme.interior_pts_eq_empty_iff D).mp hs.1
    have := t.isIntegral_of_genericPoint_notMem hD
    have hg := t.map_genericPoint hD
    have h1 := ih hs.2
    have h2 : Function.Bijective (functionFieldMap t.f hg) :=
      bijective_functionFieldMap t.f hg (t.bijective_stalkMap_of_notMem_pts _ (by rw [hg]; exact hD))
    have hη := (cons D t rest).composite_genericPoint hs
    have h3 := functionFieldMap_comp rest.composite t.f (rest.composite_genericPoint hs.2) hg hη
    change Function.Bijective (functionFieldMap (rest.composite ≫ t.f) hη)
    rw [h3]
    exact h1.comp h2

/-- The isomorphism of function fields `K(X) ≃ K(Y)` induced by the composite of a succession with nowhere dense
centers (the unprinted composition of the isomorphisms of p. 144, one for each monoidal transformation). -/
noncomputable def functionFieldIso (s : MonoidalSuccession X Y) [IsIntegral X] [IsIntegral Y]
    (hs : s.NowhereDenseCenters) : X.functionField ≃+* Y.functionField :=
  RingEquiv.ofBijective (functionFieldMap s.composite (s.composite_genericPoint hs)).hom
    (s.bijective_functionFieldMap_composite hs)

/-- The isomorphism of function fields of a succession is compatible with the `B`-structures. -/
theorem functionFieldIso_algebraMap {B : Type u} [CommRing B] (s : MonoidalSuccession X Y) [IsIntegral X]
    [IsIntegral Y] (hs : s.NowhereDenseCenters) (p : X ⟶ Spec (CommRingCat.of B)) (b : B) :
    s.functionFieldIso hs (functionFieldAlgebraMap p b) = functionFieldAlgebraMap (s.composite ≫ p) b := by
  have := congrArg (fun φ => φ b)
    (functionFieldAlgebraMap_comp s.composite (s.composite_genericPoint hs) p)
  exact this.symm

/-- The isomorphism of function fields of a concatenation is the composite of the isomorphisms. -/
theorem functionFieldIso_append (s : MonoidalSuccession X Y) (s' : MonoidalSuccession Y Z) [IsIntegral X]
    [IsIntegral Y] [IsIntegral Z] (hs : s.NowhereDenseCenters) (hs' : s'.NowhereDenseCenters) (x : X.functionField) :
    (s.append s').functionFieldIso ((s.nowhereDenseCenters_append s').mpr ⟨hs, hs'⟩) x =
      s'.functionFieldIso hs' (s.functionFieldIso hs x) := by
  have hsa := (s.nowhereDenseCenters_append s').mpr ⟨hs, hs'⟩
  have e : (s.append s').composite = s'.composite ≫ s.composite := s.composite_append s'
  have hη := (s.append s').composite_genericPoint hsa
  have hη' : (s'.composite ≫ s.composite) (genericPoint Z) = genericPoint X := by
    rw [Scheme.Hom.comp_apply, s'.composite_genericPoint hs', s.composite_genericPoint hs]
  have h1 := functionFieldMap_congr e hη hη'
  have h2 := functionFieldMap_comp s'.composite s.composite (s'.composite_genericPoint hs')
    (s.composite_genericPoint hs) hη'
  change (functionFieldMap (s.append s').composite hη).hom x = _
  rw [h1, h2]
  rfl

end MonoidalSuccession

/-! ### The structure morphism of the end of a succession -/

section StructureMorphism

variable {B : Type u} [Field B] {X Y : Scheme.{u}} (s : MonoidalSuccession X Y)
  (p : X ⟶ Spec (CommRingCat.of B))

/-- The composite of a succession of a scheme locally of finite type over a field is proper, hence of finite type,
quasi-compact and separated; so is `s.composite ≫ p` when `p` is. -/
theorem MonoidalSuccession.isProper_composite_of_locallyOfFiniteType [Hironaka.HironakaCitedResults.{u}] [LocallyOfFiniteType p] :
    IsProper s.composite := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian p
  exact s.isProper_composite

theorem MonoidalSuccession.locallyOfFiniteType_composite_comp [Hironaka.HironakaCitedResults.{u}] [LocallyOfFiniteType p] :
    LocallyOfFiniteType (s.composite ≫ p) := by
  have := s.isProper_composite_of_locallyOfFiniteType p
  infer_instance

theorem MonoidalSuccession.quasiCompact_composite_comp [Hironaka.HironakaCitedResults.{u}] [LocallyOfFiniteType p] [QuasiCompact p] :
    QuasiCompact (s.composite ≫ p) := by
  have := s.isProper_composite_of_locallyOfFiniteType p
  infer_instance

theorem MonoidalSuccession.isSeparated_composite_comp [Hironaka.HironakaCitedResults.{u}] [LocallyOfFiniteType p] [IsSeparated p] :
    IsSeparated (s.composite ≫ p) := by
  have := s.isProper_composite_of_locallyOfFiniteType p
  infer_instance

theorem MonoidalSuccession.isProper_composite_comp [Hironaka.HironakaCitedResults.{u}] [IsProper p] :
    IsProper (s.composite ≫ p) := by
  have := s.isProper_composite_of_locallyOfFiniteType p
  infer_instance

end StructureMorphism

/-! ### Non-singularity and strong resolutions -/

namespace MonoidalSuccession

variable {X Y : Scheme.{u}}

/-- A succession with non-singular centers of a non-singular scheme ends in a non-singular scheme (p. 142: "If `f` is
the monoidal transformation of `X` with center `D`, and if `X` and `D` are non-singular, then we know that `X'` and
`f⁻¹(D)` are also non-singular", iterated). -/
theorem isNonsingular_of_hasNonsingularCenters (s : MonoidalSuccession X Y) (hX : X.IsNonsingular)
    (hs : s.HasNonsingularCenters) : Y.IsNonsingular := by
  induction s with
  | nil X => exact hX
  | cons B t rest ih => exact ih (t.isNonsingular_and_isNonsingular_exceptional hX hs.1).1 hs.2

/-- A strong resolution of an integral scheme has non-singular centers. -/
theorem hasNonsingularCenters_of_isStrongResolution (s : MonoidalSuccession X Y) (hs : s.IsStrongResolution) :
    s.HasNonsingularCenters := by
  induction s with
  | nil X => trivial
  | cons B t rest ih => exact ⟨hs.1, ih hs.2.2.2⟩

/-- A strong resolution of an integral scheme has nowhere dense centers: no center contains a simple point, and the
generic point of an integral scheme is simple (`isSimpleAt_genericPoint`). -/
theorem nowhereDenseCenters_of_isStrongResolution (s : MonoidalSuccession X Y) [IsIntegral X]
    (hs : s.IsStrongResolution) : s.NowhereDenseCenters := by
  revert ‹IsIntegral X›
  induction s with
  | nil X => intro _; trivial
  | @cons X' D t Y' rest ih =>
    intro _
    have hD : genericPoint X' ∉ D.pts := genericPoint_notMem_of_isStrongResolution hs
    have := t.isIntegral_of_genericPoint_notMem hD
    exact ⟨(Subscheme.interior_pts_eq_empty_iff D).mpr hD, ih hs.2.2.2⟩

end MonoidalSuccession

end Hironaka
