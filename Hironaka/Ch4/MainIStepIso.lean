/-
Copyright (c) 2026 Daattavya Aggarwal, Minhyong Kim, Oisin Kim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daattavya Aggarwal, Minhyong Kim, Oisin Kim
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Architect
public import Hironaka.Compat.MainISystem
public import Hironaka.Compat.MonoidalSuccessionBaseChange
public import Hironaka.Ch4.ImplicationsAB
public import Hironaka.Ch4.LiftingOpen

/-!
# Main Theorem I(n), p. 176: "it induces the prolongation of the `{f̂_i}` by `ĝ` except for the `(r′ − r − 1)` monoidal
transformations with empty centers which should precede `ĝ`"

> Let `{f_i, 0 ≤ i < r′ − 1}` be the prolongation of the `{f_i, 0 ≤ i < r}` obtained by adding a succession in the above
> application of theorem I(n′), and let `C(i+1) → C(i)` for `r ≤ i < r′ − 1` be the succession of monoidal
> transformations induced by `f_i`, where `C(r) = C`.  Let `f_{r′−1} : V₀(r′) → V₀(r′ − 1)` be the monoidal
> transformation with center `C(r′ − 1)`.  We can easily see that `{f_i, 0 ≤ i < r′}` is a prolongation of the
> `{f_i, 0 ≤ i < r}` satisfying (1), (2) and (3), and that it induces the prolongation of the `{f̂_i}` by `ĝ` except for
> the `(r′ − r − 1)` monoidal transformations with empty centers which should precede `ĝ`.  (p. 176)

The comparison of the two monoidal transformations of `V̂₀(r)` with the same center `Ĉ = c_r⁻¹(C)`:
* `ĝ` (the given one);
* the base change along `c_r` of the whole prolongation `s' ++ [f_{r′−1}]` (`s'` the succession from I(n′), whose centers
  avoid the range of `c_r`, so that its base change has all centers empty and composite an isomorphism
  `ŝ'.composite : V̂₀(r)(r′−1) ≅ V̂₀(r)`; the base change of `f_{r′−1}` is a monoidal transformation with center
  `c⁻¹(C(r′−1))`, which `ŝ'.composite` carries to `Ĉ`).
They are isomorphic over `V̂₀(r)` (`MonoidalTransformation.unique_up_to_iso`), compatibly with the strict transforms
(`MonoidalTransformation.totalTransform_strictTransform_of_iso`, `strictTransform_ofIso`, `strictTransform_baseChangeSucc`,
`totalTransform_composite_eq_strictTransform_of_allCentersEmpty`).
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

namespace Hironaka

universe u

/-- The case of an empty center: `ĝ` is an isomorphism (`strictTransform = totalTransform`), and the prolongation is the
empty succession (`s ++ nil`); the iso is `ĝ.f⁻¹` (transported along `append_nil`). -/
theorem exists_iso_step_of_eq_empty {V₀ Y : Scheme.{u}} [IsAlgebraicScheme V₀] (x : V₀)
    (s : MonoidalSuccession V₀ Y) (Bh : Subscheme (s.baseChangeTarget (AB.c0 V₀ x)))
    (gh : MonoidalTransformation (s.baseChangeTarget (AB.c0 V₀ x)) Bh) (hB : Bh = Subscheme.empty) :
    ∃ e : ((s.append (MonoidalSuccession.nil Y)).baseChangeTarget (AB.c0 V₀ x)) ≅ gh.X', ∀ D : Subscheme Y,
      Subscheme.totalTransform ((s.append (MonoidalSuccession.nil Y)).baseChangeMap (AB.c0 V₀ x))
          ((MonoidalSuccession.nil Y).strictTransform D) =
        Subscheme.totalTransform e.hom
          (Subscheme.strictTransform gh (Subscheme.totalTransform (s.baseChangeMap (AB.c0 V₀ x)) D)) := by
  rw [AB.succession_append_nil]
  subst hB
  have : IsIso gh.f := MonoidalTransformation.isIso_of_eq_empty gh rfl
  refine ⟨(asIso gh.f).symm, fun D => ?_⟩
  rw [MonoidalTransformation.strictTransform_eq_totalTransform_of_eq_empty gh rfl,
    ← Subscheme.totalTransform_comp]
  have h : (asIso gh.f).symm.hom ≫ gh.f = 𝟙 _ := (asIso gh.f).symm.hom_inv_id
  rw [h, Subscheme.totalTransform_id]
  rfl

/-- The core of the comparison of p. 176, for a flat morphism `c : Ŷ₀ ⟶ Y` (`Ŷ₀ = V̂₀(r)`, `c = c_r`): a succession `s'`
of `Y` whose centers avoid the range of `c` has a base change `ŝ' : Ŷ₀ ⟶ Ŷ'` with all centers empty, whose composite is
an isomorphism `ι : Ŷ' ≅ Ŷ₀`; the base change of a monoidal transformation `tfin` of the end `Y'` of `s'` with center
`s'.strictTransform C` along `c' = c'_{s'}` is a monoidal transformation of `Ŷ'` with center `c'⁻¹(C(r′−1))`, which
`ι` carries to a monoidal transformation of `Ŷ₀` with center `c⁻¹(C)`; it is isomorphic over `Ŷ₀` to any given
monoidal transformation `ĝ` with center `c⁻¹(C)` (`MonoidalTransformation.unique_up_to_iso`), compatibly with strict
transforms. -/
theorem exists_iso_pullback_of_centersAvoid {Ŷ₀ Y Y' : Scheme.{u}} (c : Ŷ₀ ⟶ Y) [Flat c]
    (s' : MonoidalSuccession Y Y') (hs' : s'.CentersAvoid (Set.range c.base)) (C : Subscheme Y)
    (Bh : Subscheme Ŷ₀) (hC : Subscheme.totalTransform c C = Bh) (gh : MonoidalTransformation Ŷ₀ Bh)
    (tfin : MonoidalTransformation Y' (s'.strictTransform C)) :
    ∃ e : pullback tfin.f (s'.baseChangeMap c) ≅ gh.X', ∀ D : Subscheme Y,
      Subscheme.totalTransform (pullback.fst tfin.f (s'.baseChangeMap c))
          (Subscheme.strictTransform tfin (s'.strictTransform D)) =
        Subscheme.totalTransform e.hom (Subscheme.strictTransform gh (Subscheme.totalTransform c D)) := by
  -- "any succession which appears in the application of theorem I(n′) induces in `V̂₀(r)` a succession of
  -- monoidal transformations with empty centers": its composite is an isomorphism `ι`
  have hempty : (s'.baseChangeSucc c).AllCentersEmpty :=
    MonoidalSuccession.allCentersEmpty_baseChangeSucc s' c hs'
  have : IsIso (s'.baseChangeSucc c).composite :=
    MonoidalSuccession.isIso_composite_of_allCentersEmpty hempty
  let ι : s'.baseChangeTarget c ≅ Ŷ₀ := asIso (s'.baseChangeSucc c).composite
  -- the pull-back of the strict transform by `s'` along `c'` is the pull-back along `ι` of the pull-back along `c`
  have hD : ∀ D : Subscheme Y, Subscheme.totalTransform (s'.baseChangeMap c) (s'.strictTransform D) =
      Subscheme.totalTransform ι.hom (Subscheme.totalTransform c D) := fun D => by
    rw [← MonoidalSuccession.strictTransform_baseChangeSucc s' c D,
      ← MonoidalSuccession.totalTransform_composite_eq_strictTransform_of_allCentersEmpty hempty]
    rfl
  -- the base change of `tfin` along `c'`, a monoidal transformation of `Ŷ' = s'.baseChangeTarget c`
  let ĥ := tfin.baseChange (s'.baseChangeMap c)
  -- transported to `V̂₀(r)`, its center is `Ĉ = Bh`
  have hcen : Subscheme.totalTransform ι.symm.hom
      (Subscheme.totalTransform (s'.baseChangeMap c) (s'.strictTransform C)) = Bh := by
    rw [hD C, ← Subscheme.totalTransform_comp, Iso.symm_hom, ι.inv_hom_id, Subscheme.totalTransform_id]
    exact hC
  let t₂ : MonoidalTransformation Ŷ₀ Bh :=
    MonoidalTransformation.congrCenter hcen (MonoidalTransformation.ofIso ι.symm ĥ)
  obtain ⟨e₀, he₀, -⟩ := MonoidalTransformation.unique_up_to_iso gh t₂
  -- `e₀ : ĝ.X' ≅ t₂.X' = pullback tfin.f c'`; the iso of the statement is its inverse
  let e : pullback tfin.f (s'.baseChangeMap c) ≅ gh.X' := e₀.symm
  refine ⟨e, fun D => ?_⟩
  have h1 : ∀ V : Subscheme Ŷ₀, Subscheme.totalTransform e.hom (Subscheme.strictTransform gh V) =
      Subscheme.strictTransform t₂ V := fun V => by
    rw [← MonoidalTransformation.totalTransform_strictTransform_of_iso gh t₂ e₀ he₀ V,
      ← Subscheme.totalTransform_comp]
    show Subscheme.totalTransform (e₀.symm.hom ≫ e₀.hom) _ = _
    rw [Iso.symm_hom, e₀.inv_hom_id, Subscheme.totalTransform_id]
  rw [h1]
  -- `strictTransform t₂ E = strictTransform ĥ (totalTransform ι E)` (transport along `ι`, `strictTransform_ofIso`)
  have h2 : ∀ E : Subscheme Ŷ₀, Subscheme.strictTransform t₂ E =
      Subscheme.strictTransform ĥ (Subscheme.totalTransform ι.hom E) := fun E => by
    show Subscheme.strictTransform (MonoidalTransformation.congrCenter hcen
      (MonoidalTransformation.ofIso ι.symm ĥ)) E = _
    rw [MonoidalTransformation.strictTransform_congrCenter]
    have hE : Subscheme.totalTransform ι.symm.hom (Subscheme.totalTransform ι.hom E) = E := by
      rw [← Subscheme.totalTransform_comp, Iso.symm_hom, ι.inv_hom_id, Subscheme.totalTransform_id]
    have := MonoidalTransformation.strictTransform_ofIso ι.symm ĥ (Subscheme.totalTransform ι.hom E)
    rw [hE] at this
    exact this
  rw [h2, ← hD D]
  have hflc : Flat (s'.baseChangeMap c) := inferInstance
  have hfl : Flat (pullback.fst tfin.f (s'.baseChangeMap c)) := inferInstance
  exact @MonoidalTransformation.totalTransform_strictTransform_of_flat_square _ _ _ tfin _ ĥ
    (s'.baseChangeMap c) (pullback.fst tfin.f (s'.baseChangeMap c)) hfl pullback.condition rfl
    (s'.strictTransform D)

/-- The base change of a one-step succession `[t]`, `t : Y' ⟶ X'`, along a flat `c : Z ⟶ Y'`: the end scheme is
`pullback t.f c`, the end map `pullback.fst t.f c`. -/
theorem baseChange_single {Y' : Scheme.{u}} {B : Subscheme Y'} (t : MonoidalTransformation Y' B) {Z : Scheme.{u}}
    (c : Z ⟶ Y') [Flat c] :
    (MonoidalSuccession.cons B t (MonoidalSuccession.nil t.X')).baseChange c =
      ⟨pullback t.f c, MonoidalSuccession.cons (Subscheme.totalTransform c B) (t.baseChange c)
        (MonoidalSuccession.nil _), pullback.fst t.f c⟩ := rfl

/-- **The comparison of p. 176.**  `s` a succession of `V₀`, `s'` a succession of `V₀(r)` whose centers avoid the range of
`c_r` (`MonoidalSuccession.CentersAvoid`, from `centersAvoid_of_isMain123`), `C` a subscheme of `V₀(r)` with
`c_r⁻¹(C) = Ĉ`, `ĝ` a monoidal transformation of `V̂₀(r)` with center `Ĉ`, and `tfin` a monoidal transformation of the end
of `s'` with center `s'.strictTransform C` (= `C(r′ − 1)`).  Then the base change along `c_0` of the prolongation
`s ++ s' ++ [tfin]` has an end scheme isomorphic to `ĝ.X'`, the isomorphism carrying the pull-back of the strict transforms
by the prolongation to the strict transforms by `ĝ` of the pull-backs. -/
theorem exists_iso_step_of_centersAvoid {V₀ Y Y' : Scheme.{u}} [IsAlgebraicScheme V₀] (x : V₀)
    (s : MonoidalSuccession V₀ Y) (s' : MonoidalSuccession Y Y')
    (hs' : s'.CentersAvoid (Set.range (s.baseChangeMap (AB.c0 V₀ x)).base)) (C : Subscheme Y)
    (Bh : Subscheme (s.baseChangeTarget (AB.c0 V₀ x)))
    (hC : Subscheme.totalTransform (s.baseChangeMap (AB.c0 V₀ x)) C = Bh)
    (gh : MonoidalTransformation (s.baseChangeTarget (AB.c0 V₀ x)) Bh)
    (tfin : MonoidalTransformation Y' (s'.strictTransform C)) :
    ∃ e : ((s.append (s'.append (MonoidalSuccession.cons (s'.strictTransform C) tfin
        (MonoidalSuccession.nil tfin.X')))).baseChangeTarget (AB.c0 V₀ x)) ≅ gh.X',
      ∀ D : Subscheme Y,
        Subscheme.totalTransform ((s.append (s'.append (MonoidalSuccession.cons (s'.strictTransform C) tfin
            (MonoidalSuccession.nil tfin.X')))).baseChangeMap (AB.c0 V₀ x))
          ((s'.append (MonoidalSuccession.cons (s'.strictTransform C) tfin
            (MonoidalSuccession.nil tfin.X'))).strictTransform D) =
        Subscheme.totalTransform e.hom (Subscheme.strictTransform gh
          (Subscheme.totalTransform (s.baseChangeMap (AB.c0 V₀ x)) D)) := by
  have key := exists_iso_pullback_of_centersAvoid (s.baseChangeMap (AB.c0 V₀ x)) s' hs' C Bh hC gh tfin
  -- "the base change of `s ++ s' ++ [tfin]` is the base change of `s`, then of `s'`, then of `tfin`" (p. 175)
  change ∃ e : (((s.append (s'.append (MonoidalSuccession.cons (s'.strictTransform C) tfin
        (MonoidalSuccession.nil tfin.X')))).baseChange (AB.c0 V₀ x)).1 ≅ gh.X'),
      ∀ D : Subscheme Y,
        Subscheme.totalTransform ((s.append (s'.append (MonoidalSuccession.cons (s'.strictTransform C) tfin
            (MonoidalSuccession.nil tfin.X')))).baseChange (AB.c0 V₀ x)).2.2
          ((s'.append (MonoidalSuccession.cons (s'.strictTransform C) tfin
            (MonoidalSuccession.nil tfin.X'))).strictTransform D) =
        Subscheme.totalTransform e.hom (Subscheme.strictTransform gh
          (Subscheme.totalTransform (s.baseChangeMap (AB.c0 V₀ x)) D))
  rw [MonoidalSuccession.baseChange_append s (AB.c0 V₀ x), MonoidalSuccession.baseChange_append s',
    baseChange_single]
  simp only [MonoidalSuccession.strictTransform_append, MonoidalSuccession.strictTransform_cons,
    MonoidalSuccession.strictTransform_nil]
  exact key

end Hironaka
