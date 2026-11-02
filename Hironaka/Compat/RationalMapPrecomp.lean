/-
Copyright (c) 2026 Daattavya Aggarwal, Minhyong Kim, Oisin Kim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daattavya Aggarwal, Minhyong Kim, Oisin Kim
-/
module

public import Mathlib.AlgebraicGeometry.Birational.Dominant
public import Mathlib.AlgebraicGeometry.Birational.RationalMap
public import Architect
public import Hironaka.Statements

/-!
# Ch. 0 §5 (p. 139): composition of a rational application with a morphism

> If `f` (resp. `g`) is a rational application of `X` to `Y` (resp. `Y` to `Z`), and if `f` contains a morphism
> `f : X | U → Y` such that `f⁻¹(V)` is open and dense for every open dense subset `V` of the underlying topological
> space of `Y`, then we get a unique rational application of `X` to `Z` as the class of composed morphisms of those in
> `f` and those in `g`.  This rational application of `X` to `Z` will be called the composition of `f` and `g`, or the
> composed application of them.  (p. 139)

Mathlib's `Scheme.RationalMap` (`Mathlib/AlgebraicGeometry/Birational/RationalMap.lean`) is the paper's rational
application; its composition `RationalMap.comp` needs an irreducible source and a dominant first factor, which is not the
paper's hypothesis (on a reducible source, dense range does not give dense preimages).  This file defines the paper's
condition `Scheme.Hom.PreimageDense` and the composition `f ∘ a` of a rational map `f : X ⤏ Y` with a *morphism*
`a : X' ⟶ X` satisfying it (`Scheme.RationalMap.precomp`), the case needed for `f ∘ h`, `h` a monoidal transformation
(p. 139) and for Question (E) (p. 140), together with its elementary properties:

* `PreimageDense` is stable under composition and holds for the identity, for open immersions and for dominant
  morphisms with irreducible source;
* `precomp` respects the equivalence of partial maps, is compatible with restriction, identities, composition and
  `RationalMap.compHom`;
* `mem_domain_precomp_iff`: a point lies in the domain of `f ∘ a` iff some partial map, equivalent to `g ∘ a` for a
  representative `g` of `f`, is defined there; and `a⁻¹(domain f) ⊆ domain (f ∘ a)`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme

variable {X X' X'' Y Z : Scheme.{u}}


namespace Hom.PreimageDense


/-- A composite of morphisms with dense preimages has dense preimages. -/
theorem comp {a : X'' ⟶ X'} {b : X' ⟶ X} (ha : a.PreimageDense) (hb : b.PreimageDense) :
    (a ≫ b).PreimageDense := fun V hV => by
  rw [Hom.comp_preimage]
  exact ha _ (hb V hV)

/-- An open map has dense preimages: a non-empty open set of the source has non-empty open image, which meets every
dense open set. -/
theorem of_isOpenMap {a : X' ⟶ X} (ha : IsOpenMap a.base) : a.PreimageDense := fun V hV => by
  rw [dense_iff_inter_open]
  intro W hW hWne
  obtain ⟨y, hyW⟩ := hWne
  obtain ⟨z, ⟨w, hw, rfl⟩, hzV⟩ := (dense_iff_inter_open.mp hV) (a.base '' W) (ha W hW) ⟨_, y, hyW, rfl⟩
  exact ⟨w, hw, hzV⟩

/-- An open immersion has dense preimages. -/
theorem of_isOpenImmersion (a : X' ⟶ X) [IsOpenImmersion a] : a.PreimageDense :=
  of_isOpenMap a.isOpenEmbedding.isOpenMap

/-- A dominant morphism whose source is irreducible has dense preimages: the preimage of a non-empty open set is a
non-empty open subset of an irreducible space. -/
theorem of_isDominant [IrreducibleSpace X'] (a : X' ⟶ X) [IsDominant a] : a.PreimageDense :=
  fun V hV => by
  have : Nonempty X := ⟨a.base (Classical.arbitrary X')⟩
  have hne : ((a ⁻¹ᵁ V : X'.Opens) : Set X').Nonempty := by
    obtain ⟨v, hv⟩ := hV.nonempty
    obtain ⟨z, hzV, hzR⟩ := a.denseRange.inter_open_nonempty (V : Set X) V.2 ⟨v, hv⟩
    obtain ⟨w, rfl⟩ := hzR
    exact ⟨w, hzV⟩
  exact (a ⁻¹ᵁ V).2.dense hne

end Hom.PreimageDense

namespace PartialMap






set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency.types false in
/-- Precomposition with the identity changes nothing. -/
theorem precomp_id (g : X.PartialMap Y) : g.precomp (𝟙 X) (Hom.PreimageDense.id X) = g :=
  PartialMap.ext _ _ rfl (by
    simp only [precomp_hom, morphismRestrict_id]
    congr 1
    exact (Scheme.isoOfEq_rfl X g.domain).symm ▸ rfl)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency.types false in
/-- Precomposition is compatible with composition of the morphisms. -/
theorem precomp_comp (g : X.PartialMap Y) (a : X' ⟶ X) (ha : a.PreimageDense) (b : X'' ⟶ X')
    (hb : b.PreimageDense) :
    (g.precomp a ha).precomp b hb = g.precomp (b ≫ a) (hb.comp ha) := by
  refine PartialMap.ext _ _ rfl ?_
  simp [morphismRestrict_comp]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency.types false in
/-- Precomposition commutes with composition by a morphism on the target. -/
theorem precomp_compHom (g : X.PartialMap Y) (q : Y ⟶ Z) (a : X' ⟶ X) (ha : a.PreimageDense) :
    (g.compHom q).precomp a ha = (g.precomp a ha).compHom q := by
  refine PartialMap.ext _ _ rfl ?_
  simp

end PartialMap


namespace RationalMap

theorem precomp_toRationalMap (g : X.PartialMap Y) (a : X' ⟶ X) (ha : a.PreimageDense) :
    g.toRationalMap.precomp a ha = (g.precomp a ha).toRationalMap := rfl

/-- `f ∘ id = f`. -/
@[simp] theorem precomp_id (f : X ⤏ Y) : f.precomp (𝟙 X) (Hom.PreimageDense.id X) = f := by
  obtain ⟨g, rfl⟩ := PartialMap.toRationalMap_surjective f
  rw [precomp_toRationalMap]
  rw [PartialMap.precomp_id]

/-- `f ∘ a` depends only on the morphism `a` (the density proof is irrelevant). -/
theorem precomp_congr (f : X ⤏ Y) {a a' : X' ⟶ X} (h : a = a') (ha : a.PreimageDense)
    (ha' : a'.PreimageDense) : f.precomp a ha = f.precomp a' ha' := by
  subst h
  rfl

/-- `(f ∘ a) ∘ b = f ∘ (a ∘ b)`. -/
theorem precomp_precomp (f : X ⤏ Y) (a : X' ⟶ X) (ha : a.PreimageDense) (b : X'' ⟶ X')
    (hb : b.PreimageDense) : (f.precomp a ha).precomp b hb = f.precomp (b ≫ a) (hb.comp ha) := by
  obtain ⟨g, rfl⟩ := PartialMap.toRationalMap_surjective f
  simp only [precomp_toRationalMap, PartialMap.precomp_comp]

/-- Composition with a morphism on the target commutes with precomposition. -/
theorem precomp_compHom (f : X ⤏ Y) (q : Y ⟶ Z) (a : X' ⟶ X) (ha : a.PreimageDense) :
    (f.compHom q).precomp a ha = (f.precomp a ha).compHom q := by
  obtain ⟨g, rfl⟩ := PartialMap.toRationalMap_surjective f
  simp only [← compHom_toRationalMap, precomp_toRationalMap, PartialMap.precomp_compHom]

/-- A point lies in the domain of `f ∘ a` iff some partial map defined at it is equivalent to `g ∘ a` for a
representative `g` of `f`. -/
theorem mem_domain_precomp_iff (f : X ⤏ Y) (a : X' ⟶ X) (ha : a.PreimageDense) (x : X') :
    x ∈ (f.precomp a ha).domain ↔
      ∃ (g : X.PartialMap Y) (ψ : X'.PartialMap Y),
        g.toRationalMap = f ∧ x ∈ ψ.domain ∧ ψ.equiv (g.precomp a ha) := by
  obtain ⟨g₀, rfl⟩ := PartialMap.toRationalMap_surjective f
  rw [RationalMap.mem_domain]
  constructor
  · rintro ⟨ψ, hx, hψ⟩
    rw [precomp_toRationalMap, PartialMap.toRationalMap_eq_iff] at hψ
    exact ⟨g₀, ψ, rfl, hx, hψ⟩
  · rintro ⟨g, ψ, hg, hx, hψ⟩
    refine ⟨ψ, hx, ?_⟩
    rw [PartialMap.toRationalMap_eq_iff] at hg
    rw [precomp_toRationalMap, PartialMap.toRationalMap_eq_iff]
    exact PartialMap.equivalence_rel.trans hψ (PartialMap.precomp_equiv hg a ha)

/-- A point of `X'` mapped by `a` into the domain of `f` lies in the domain of `f ∘ a`. -/
theorem preimage_domain_le_domain_precomp (f : X ⤏ Y) (a : X' ⟶ X) (ha : a.PreimageDense) :
    a ⁻¹ᵁ f.domain ≤ (f.precomp a ha).domain := by
  intro x hx
  obtain ⟨g, hg, hgf⟩ := RationalMap.mem_domain.mp hx
  rw [← hgf, precomp_toRationalMap]
  exact PartialMap.le_domain_toRationalMap _ hg

/-- The domain of `f ∘ a` is dense. -/
theorem dense_domain_precomp (f : X ⤏ Y) (a : X' ⟶ X) (ha : a.PreimageDense) :
    Dense ((f.precomp a ha).domain : Set X') :=
  (f.precomp a ha).dense_domain

end RationalMap

end AlgebraicGeometry.Scheme
