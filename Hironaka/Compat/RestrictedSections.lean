/-
Copyright (c) 2026 Daattavya Aggarwal, Minhyong Kim, Oisin Kim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daattavya Aggarwal, Minhyong Kim, Oisin Kim
-/
module

public import Hironaka.Compat.ProjDegreeOne

/-!
# Sections over a subset of `Proj` of the restricted structure sheaf and of the sheaf of degree-one elements

Ch. 0 §2 (p. 125) uses the restriction `P(O_x, J_x) | 𝐏^x` of a pair (a local-ringed space and a sheaf of modules on
it) to a subset `𝐏^x` of the points of `Proj`, which is not open, and sections `Γ(W ∩ 𝐏^x, O_{P^x})`,
`Γ(W ∩ 𝐏^x, I^x)` of the restricted sheaves over subsets of `𝐏^x`.  For a graded ring `𝒜` and a set `V` of points of
`Proj 𝒜` this file describes these sections in the standard way: a section of the restriction of a sheaf `F` over `V` is
a function on `V` with values in the stalks of `F`, which is locally induced by a section of `F` over an open set of `Proj`.
For `F` the structure sheaf the stalks are the homogeneous localizations, for `F` the sheaf of degree-one elements
they are the modules `DegreeOne.stalk`.  `ORestr V` is a subring and `IRestr V` a submodule over it.  (Mathlib has
the restriction to a subset only for sheaves of rings, `Hironaka/Compat/RestrictSubset.lean`; the comparison with
the description used here is not proved.)  None of this is a claim of the paper.
-/

@[expose] public section

noncomputable section

namespace AlgebraicGeometry

open TopologicalSpace CategoryTheory Opposite TopCat

universe u

namespace ProjectiveSpectrum.DegreeOne

variable {A σ : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
variable (𝒜 : ℕ → σ) [GradedRing 𝒜]

/-- Sections over the subset `V` of `Proj 𝒜` of the restriction of the structure sheaf: functions into the
homogeneous localizations that are locally induced by sections of the structure sheaf over open sets of `Proj 𝒜`. -/
def ORestr (V : Set (ProjectiveSpectrum 𝒜)) : Subring (∀ q : V, loc 𝒜 q.1) where
  carrier := {s | ∀ q : V, ∃ (D : Opens (ProjectiveSpectrum.top 𝒜)) (_ : q.1 ∈ D)
      (t : (ProjectiveSpectrum.Proj.structureSheaf 𝒜).1.obj (op D)),
      ∀ (q' : V) (h : q'.1 ∈ D), s q' = t.1 ⟨q'.1, h⟩}
  zero_mem' q := ⟨⊤, trivial, 0, fun _ _ => rfl⟩
  one_mem' q := ⟨⊤, trivial, 1, fun _ _ => rfl⟩
  add_mem' {a b} ha hb q := by
    obtain ⟨D₁, h₁, t₁, e₁⟩ := ha q
    obtain ⟨D₂, h₂, t₂, e₂⟩ := hb q
    refine ⟨D₁ ⊓ D₂, ⟨h₁, h₂⟩,
      (ProjectiveSpectrum.Proj.structureSheaf 𝒜).1.map (homOfLE inf_le_left).op t₁ +
        (ProjectiveSpectrum.Proj.structureSheaf 𝒜).1.map (homOfLE inf_le_right).op t₂, ?_⟩
    intro q' h
    exact congrArg₂ (· + ·) (e₁ q' h.1) (e₂ q' h.2)
  neg_mem' {a} ha q := by
    obtain ⟨D, h, t, e⟩ := ha q
    exact ⟨D, h, -t, fun q' h' => congrArg (- ·) (e q' h')⟩
  mul_mem' {a b} ha hb q := by
    obtain ⟨D₁, h₁, t₁, e₁⟩ := ha q
    obtain ⟨D₂, h₂, t₂, e₂⟩ := hb q
    refine ⟨D₁ ⊓ D₂, ⟨h₁, h₂⟩,
      (ProjectiveSpectrum.Proj.structureSheaf 𝒜).1.map (homOfLE inf_le_left).op t₁ *
        (ProjectiveSpectrum.Proj.structureSheaf 𝒜).1.map (homOfLE inf_le_right).op t₂, ?_⟩
    intro q' h
    exact congrArg₂ (· * ·) (e₁ q' h.1) (e₂ q' h.2)

/-- Sections over the subset `V` of `Proj 𝒜` of the restriction of the sheaf of degree-one elements. -/
def IRestr (V : Set (ProjectiveSpectrum 𝒜)) :
    Submodule (ORestr 𝒜 V) (∀ q : V, stalk 𝒜 q.1) where
  carrier := {s | ∀ q : V, ∃ (D : Opens (ProjectiveSpectrum.top 𝒜)) (_ : q.1 ∈ D)
      (t : (inType 𝒜).1.obj (op D)),
      ∀ (q' : V) (h : q'.1 ∈ D), s q' = t.1 ⟨q'.1, h⟩}
  zero_mem' q := ⟨⊤, trivial, 0, fun _ _ => rfl⟩
  add_mem' {a b} ha hb q := by
    obtain ⟨D₁, h₁, t₁, e₁⟩ := ha q
    obtain ⟨D₂, h₂, t₂, e₂⟩ := hb q
    refine ⟨D₁ ⊓ D₂, ⟨h₁, h₂⟩,
      (inType 𝒜).1.map (homOfLE inf_le_left).op t₁ + (inType 𝒜).1.map (homOfLE inf_le_right).op t₂, ?_⟩
    intro q' h
    exact congrArg₂ (· + ·) (e₁ q' h.1) (e₂ q' h.2)
  smul_mem' {r b} hb q := by
    obtain ⟨D₁, h₁, t₁, e₁⟩ := r.2 q
    obtain ⟨D₂, h₂, t₂, e₂⟩ := hb q
    refine ⟨D₁ ⊓ D₂, ⟨h₁, h₂⟩,
      (((ProjectiveSpectrum.StructureSheaf.structureSheafInType 𝒜).1.map
        (homOfLE inf_le_left : D₁ ⊓ D₂ ⟶ D₁).op t₁ :
          (ProjectiveSpectrum.StructureSheaf.structureSheafInType 𝒜).1.obj (op (D₁ ⊓ D₂))) •
        ((inType 𝒜).1.map (homOfLE inf_le_right : D₁ ⊓ D₂ ⟶ D₂).op t₂ :
          (inType 𝒜).1.obj (op (D₁ ⊓ D₂))) :
        (inType 𝒜).1.obj (op (D₁ ⊓ D₂))), ?_⟩
    intro q' h
    change (r.1 q') • (b q') = _
    rw [e₁ q' h.1, e₂ q' h.2]
    rfl

variable {𝒜}

/-- Restriction of sections of the restricted structure sheaf from `V` to a subset `V' ⊆ V`. -/
def ORestr.res {V V' : Set (ProjectiveSpectrum 𝒜)} (h : V' ⊆ V) : ORestr 𝒜 V →+* ORestr 𝒜 V' where
  toFun s := ⟨fun q => s.1 ⟨q.1, h q.2⟩, fun q => by
    obtain ⟨D, hq, t, e⟩ := s.2 ⟨q.1, h q.2⟩
    exact ⟨D, hq, t, fun q' hq' => e ⟨q'.1, h q'.2⟩ hq'⟩⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

/-- Restriction of sections of the restricted sheaf of degree-one elements from `V` to `V' ⊆ V`. -/
def IRestr.res {V V' : Set (ProjectiveSpectrum 𝒜)} (h : V' ⊆ V) : IRestr 𝒜 V →+ IRestr 𝒜 V' where
  toFun s := ⟨fun q => s.1 ⟨q.1, h q.2⟩, fun q => by
    obtain ⟨D, hq, t, e⟩ := s.2 ⟨q.1, h q.2⟩
    exact ⟨D, hq, t, fun q' hq' => e ⟨q'.1, h q'.2⟩ hq'⟩⟩
  map_zero' := rfl
  map_add' _ _ := rfl

end ProjectiveSpectrum.DegreeOne

end AlgebraicGeometry

end
