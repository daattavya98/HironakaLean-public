/-
Copyright (c) 2026 Daattavya Aggarwal, Minhyong Kim, Oisin Kim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daattavya Aggarwal, Minhyong Kim, Oisin Kim
-/
module

public import Mathlib.RingTheory.RingHom.FaithfullyFlat
public import Mathlib.RingTheory.RingHom.FiniteType

/-!
# Compatibility layer: pushout squares of ring homomorphisms

For the reduction of property (c) of the class 𝔅 to the complete case (p. 161, footnote 31:
"Reduce the proof to the case in which S is complete"), the local rings of finite type algebras
are compared along several base changes.  This file packages Mathlib's categorical pushouts in
`CommRingCat` for commutative squares of ring homomorphisms (`IsRingPushout`), together with:

* pasting (`IsRingPushout.paste_horiz`, `IsRingPushout.of_left`) and the universal property
  (`IsRingPushout.exists_desc`);
* the tensor product square (`IsRingPushout.tensorProduct`) and the localization square
  (`IsRingPushout.of_isLocalization`);
* stability of flatness, faithful flatness and finite type under base change along a pushout
  square (`IsRingPushout.flat`, `IsRingPushout.faithfullyFlat`, `IsRingPushout.finiteType`);
* the characterization of localizations (`IsRingPushout.isLocalization`).
-/

@[expose] public section

open CategoryTheory
open scoped TensorProduct

noncomputable section

namespace Hironaka

universe u

/-- A commutative square of ring homomorphisms `f : Z → X`, `g : Z → Y`, `inl : X → P`,
`inr : Y → P` is a pushout square (in `CommRingCat`). -/
abbrev IsRingPushout {Z X Y P : Type u} [CommRing Z] [CommRing X] [CommRing Y] [CommRing P]
    (f : Z →+* X) (g : Z →+* Y) (inl : X →+* P) (inr : Y →+* P) : Prop :=
  IsPushout (CommRingCat.ofHom f) (CommRingCat.ofHom g) (CommRingCat.ofHom inl)
    (CommRingCat.ofHom inr)

namespace IsRingPushout

section Basic

variable {Z X Y P : Type u} [CommRing Z] [CommRing X] [CommRing Y] [CommRing P]
  {f : Z →+* X} {g : Z →+* Y} {inl : X →+* P} {inr : Y →+* P}

/-- The square commutes. -/
theorem comm (H : IsRingPushout f g inl inr) : inl.comp f = inr.comp g := by
  ext x
  exact congr(($H.w).hom x)

theorem flip (H : IsRingPushout f g inl inr) : IsRingPushout g f inr inl :=
  IsPushout.flip H

/-- The tensor product square of two algebras over a ring. -/
theorem tensorProduct (R A B : Type u) [CommRing R] [CommRing A] [CommRing B] [Algebra R A]
    [Algebra R B] :
    IsRingPushout (algebraMap R A) (algebraMap R B) Algebra.TensorProduct.includeLeftRingHom
      (Algebra.TensorProduct.includeRight (R := R) (A := A) (B := B)).toRingHom :=
  CommRingCat.isPushout_tensorProduct R A B

/-- The universal property: maps out of the pushout. -/
theorem exists_desc (H : IsRingPushout f g inl inr) {W : Type u} [CommRing W] (u : X →+* W)
    (v : Y →+* W) (w : u.comp f = v.comp g) :
    ∃ d : P →+* W, d.comp inl = u ∧ d.comp inr = v := by
  obtain ⟨d, h1, h2⟩ := IsPushout.exists_desc H (CommRingCat.ofHom u) (CommRingCat.ofHom v)
    (by ext x; exact congr($w x))
  exact ⟨d.hom, by ext x; exact congr(($h1).hom x), by ext x; exact congr(($h2).hom x)⟩

/-- Two maps out of a pushout agree if they agree on both legs. -/
theorem hom_ext (H : IsRingPushout f g inl inr) {W : Type u} [CommRing W] {k l : P →+* W}
    (h1 : k.comp inl = l.comp inl) (h2 : k.comp inr = l.comp inr) : k = l := by
  have := IsPushout.hom_ext H (k := CommRingCat.ofHom k) (l := CommRingCat.ofHom l)
    (by ext x; exact congr($h1 x)) (by ext x; exact congr($h2 x))
  ext x
  exact congr(($this).hom x)

end Basic

section Paste

variable {X₁ X₂ X₃ Y₁ Y₂ Y₃ : Type u} [CommRing X₁] [CommRing X₂] [CommRing X₃] [CommRing Y₁]
  [CommRing Y₂] [CommRing Y₃] {h₁₁ : X₁ →+* X₂} {h₁₂ : X₂ →+* X₃} {v₁₁ : X₁ →+* Y₁}
  {v₁₂ : X₂ →+* Y₂} {v₁₃ : X₃ →+* Y₃} {h₂₁ : Y₁ →+* Y₂} {h₂₂ : Y₂ →+* Y₃}

/-- Pasting of pushout squares along a common side.
```
X₁ - h₁₁ -> X₂ - h₁₂ -> X₃
|            |            |
v₁₁          v₁₂          v₁₃
↓            ↓            ↓
Y₁ - h₂₁ -> Y₂ - h₂₂ -> Y₃
```
-/
theorem paste_horiz (s : IsRingPushout h₁₁ v₁₁ v₁₂ h₂₁) (t : IsRingPushout h₁₂ v₁₂ v₁₃ h₂₂) :
    IsRingPushout (h₁₂.comp h₁₁) v₁₁ v₁₃ (h₂₂.comp h₂₁) := by
  have := IsPushout.paste_horiz s t
  simp only [IsRingPushout, CommRingCat.ofHom_comp]
  exact this

/-- If the big rectangle and the left square are pushouts, so is the right square. -/
theorem of_left (s : IsRingPushout (h₁₂.comp h₁₁) v₁₁ v₁₃ (h₂₂.comp h₂₁))
    (t : IsRingPushout h₁₁ v₁₁ v₁₂ h₂₁) (p : v₁₃.comp h₁₂ = h₂₂.comp v₁₂) :
    IsRingPushout h₁₂ v₁₂ v₁₃ h₂₂ := by
  simp only [IsRingPushout, CommRingCat.ofHom_comp] at s
  refine IsPushout.of_left s ?_ t
  ext x
  exact congr($p x)

end Paste

section BaseChange

variable {Z X Y P : Type u} [CommRing Z] [CommRing X] [CommRing Y] [CommRing P]
  {f : Z →+* X} {g : Z →+* Y} {inl : X →+* P} {inr : Y →+* P}

/-- A property of ring homomorphisms stable under base change (in the sense of
`RingHom.IsStableUnderBaseChange`) is stable along a pushout square: if `f` has it, so has `inr`. -/
theorem of_isStableUnderBaseChange
    {Q : ∀ {R S : Type u} [CommRing R] [CommRing S], (R →+* S) → Prop}
    (hQ : RingHom.IsStableUnderBaseChange Q) (H : IsRingPushout f g inl inr) (hf : Q f) :
    Q inr := by
  algebraize [f, g, inl, inr, inl.comp f]
  have h1 : IsScalarTower Z X P := IsScalarTower.of_algebraMap_eq fun x => rfl
  have h2 : IsScalarTower Z Y P := IsScalarTower.of_algebraMap_eq fun x => by
    simp only [RingHom.algebraMap_toAlgebra]
    have := congr(($H.w).hom x)
    simpa using this
  have h3 : Algebra.IsPushout Z X Y P := by
    rw [← CommRingCat.isPushout_iff_isPushout]
    simpa [RingHom.algebraMap_toAlgebra] using H
  exact hQ Z X Y P hf

/-- Flatness is stable along a pushout square. -/
theorem flat (H : IsRingPushout f g inl inr) (hf : f.Flat) : inr.Flat :=
  of_isStableUnderBaseChange (Q := fun f => f.Flat) RingHom.Flat.isStableUnderBaseChange
    H hf

/-- Faithful flatness is stable along a pushout square. -/
theorem faithfullyFlat (H : IsRingPushout f g inl inr) (hf : f.FaithfullyFlat) :
    inr.FaithfullyFlat :=
  of_isStableUnderBaseChange (Q := fun f => f.FaithfullyFlat)
    RingHom.FaithfullyFlat.isStableUnderBaseChange H hf

/-- Finite type is stable along a pushout square. -/
theorem finiteType (H : IsRingPushout f g inl inr) (hf : f.FiniteType) : inr.FiniteType :=
  of_isStableUnderBaseChange (Q := fun f => f.FiniteType)
    RingHom.finiteType_isStableUnderBaseChange H hf

end BaseChange

section Localization

/-- The localization square: a ring homomorphism `f : A → B` induces a pushout square between
`A → A_M` and `B → B_{f M}`. -/
theorem of_isLocalization {A B Am Bm : Type u} [CommRing A] [CommRing B] [CommRing Am]
    [Algebra A Am] [CommRing Bm] [Algebra B Bm] (f : A →+* B) (fm : Am →+* Bm)
    (H : fm.comp (algebraMap A Am) = (algebraMap B Bm).comp f) (M : Submonoid A)
    [IsLocalization M Am] [IsLocalization (M.map f) Bm] :
    IsRingPushout f (algebraMap A Am) (algebraMap B Bm) fm :=
  CommRingCat.isPushout_of_isLocalization f fm H M

/-- A pushout of a localization `A → A_M` along `u : A → D` is the localization of `D` at the
image of `M`. -/
theorem isLocalization {A Am D E : Type u} [CommRing A] [CommRing Am] [Algebra A Am] [CommRing D]
    [CommRing E] (M : Submonoid A) [IsLocalization M Am] (u : A →+* D) (j : Am →+* E)
    (e : D →+* E) (H : IsRingPushout (algebraMap A Am) u j e) :
    @IsLocalization D _ (M.map u) E _ e.toAlgebra := by
  algebraize [u, j, e, e.comp u]
  have h1 : IsScalarTower A D E := IsScalarTower.of_algebraMap_eq fun x => rfl
  have h2 : IsScalarTower A Am E := IsScalarTower.of_algebraMap_eq fun x => by
    simp only [RingHom.algebraMap_toAlgebra]
    have := congr(($H.w).hom x)
    simpa using this.symm
  have h3 : Algebra.IsPushout A Am D E := by
    rw [← CommRingCat.isPushout_iff_isPushout]
    simpa [RingHom.algebraMap_toAlgebra] using H
  exact (Algebra.isLocalization_iff_isPushout M Am).mpr h3.symm

end Localization

end IsRingPushout

end Hironaka
