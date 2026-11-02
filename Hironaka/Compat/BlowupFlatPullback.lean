/-
Copyright (c) 2026 Daattavya Aggarwal, Minhyong Kim, Oisin Kim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daattavya Aggarwal, Minhyong Kim, Oisin Kim
-/
module

public import Mathlib.AlgebraicGeometry.Pullbacks
public import Hironaka.Compat.BlowupBaseChange

/-!
# Compatibility layer: a monoidal transformation of a flat base is the base change

Hironaka (Ch. IV §3, p. 295): "The given succession of monoidal transformations `{f_s : X_{s+1} → X_s}`
of `X` induces a succession of monoidal transformations `{f̂_s : X̂_{s+1} → X̂_s}` of `X̂_0` such that we
have the following commutative diagrams of canonical morphisms … `f̂_s` is the monoidal transformation of
`X̂_s` with the non-singular center `B̂_s = c_s⁻¹(B_s)` … In view of the fact that `Ŝ` is faithfully flat over
`S`, one can show that `X̂_s` is canonically isomorphic to the product `X_s ×_X X̂_0` in the category of
schemes over `X` and that `c_s` is the projection to the first factor."

The inductive step of "one can show": if `c : Ŷ → Y` is flat, `f : Y' → Y` is the monoidal transformation
with center `B`, `f̂ : Ŷ' → Ŷ` is *a* monoidal transformation with center `c⁻¹(B)` and `c' : Ŷ' → Y'` is
the morphism induced by the universal mapping property of `f` (`f ∘ c' = c ∘ f̂`), then the square
`(c', f̂, f, c)` is a pullback square.  By flat base change `Y' ×_Y Ŷ → Ŷ` is also a monoidal transformation
of `Ŷ` with center `c⁻¹(B)` (`MonoidalTransformation.baseChange`), and any two monoidal transformations with
the same center are canonically isomorphic (p. 166, `MonoidalTransformation.unique_up_to_iso`).
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Hironaka

namespace MonoidalTransformation

variable {Y Ŷ : Scheme.{u}} {B : Subscheme Y} (t : MonoidalTransformation Y B) (c : Ŷ ⟶ Y)
  (th : MonoidalTransformation Ŷ (Subscheme.totalTransform c B)) (c' : th.X' ⟶ t.X')

/-- The morphism `c' : Ŷ' → Y'` over `c` is unique: two morphisms `Ŷ' → Y'` with the same composite with
`f` agree, the pull-back of `B` to `Ŷ'` being invertible (universal mapping property of `f`, p. 166). -/
theorem eq_of_comp_f_eq {c₁ c₂ : th.X' ⟶ t.X'} (h₁ : c₁ ≫ t.f = th.f ≫ c)
    (h₂ : c₂ ≫ t.f = th.f ≫ c) : c₁ = c₂ := by
  have hinv : (Subscheme.totalTransform (th.f ≫ c) B).IsInvertibleIdeal := by
    rw [Subscheme.totalTransform_comp]
    exact th.invertible
  exact ((t.universal th.X' (th.f ≫ c) hinv).unique h₁ h₂)

/-- **"One can show that `X̂_s` is canonically isomorphic to the product"** (p. 295), one step: if `c : Ŷ → Y`
is flat, `t` is the monoidal transformation of `Y` with center `B`, `th` a monoidal transformation of `Ŷ`
with center `c⁻¹(B)` and `c'` a morphism with `c' ≫ t.f = th.f ≫ c`, then `Ŷ' = Y' ×_Y Ŷ`, with projections
`c'` and `f̂`.  Flat base change gives a second monoidal transformation of `Ŷ` with center `c⁻¹(B)`,
`Y' ×_Y Ŷ → Ŷ`; the two are isomorphic over `Ŷ` by the universal mapping property. -/
theorem isPullback_of_flat [Flat c] (h : c' ≫ t.f = th.f ≫ c) : IsPullback c' th.f t.f c := by
  obtain ⟨e, he, -⟩ := MonoidalTransformation.unique_up_to_iso th (t.baseChange c)
  -- `(t.baseChange c).X'` is `pullback t.f c` by definition
  have hsnd : e.hom ≫ pullback.snd t.f c = th.f := he
  have hfst : e.hom ≫ pullback.fst t.f c = c' := by
    refine t.eq_of_comp_f_eq c th ?_ h
    exact ((Category.assoc _ _ _).trans (congrArg (fun x => e.hom ≫ x) pullback.condition)).trans
      ((Category.assoc _ _ _).symm.trans (congrArg (fun x => x ≫ c) hsnd))
  exact IsPullback.of_iso_pullback ⟨h⟩ e hfst hsnd

end MonoidalTransformation

end Hironaka
