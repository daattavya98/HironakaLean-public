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
public import Hironaka.Compat.FlatStrictTransform
public import Hironaka.Compat.BlowupBaseChange
public import Hironaka.Compat.BlowupLocalIso
public import Hironaka.Compat.LocalizeSuccession
public import Hironaka.Ch4.ImplicationsAB

/-!
# Main Theorem I(n), p. 175: flat base change of a succession of monoidal transformations

> Let `V̂₀ = Spec(Ô_{V₀,x})` … We have a canonical morphism of `V̂₀` to `V₀`.  We shall denote by `V̂_j(i)` (resp.
> `Ŵ(i)`) the product of `V₀`-schemes `V_j(i)` (resp. `W(i)`) and `V̂₀`.  Let `c_i` denote the canonical morphism of
> `V̂₀(i)` to `V₀(i)`.  We see that `c_i` is a flat morphism. … Moreover, we see that `V̂_j(i) = c_i⁻¹(V_j(i))` for all
> `j` and `i` and that, if `B̂_i = c_i⁻¹(B_i)` (= the product of `V₀`-schemes `B_i` and `V̂₀`), then the canonical
> morphisms `V̂_j(i+1) → V̂_j(i)` and `Ŵ(i+1) → Ŵ(i)` may be identified with the monoidal transformations with
> center `B̂_i` for every `i`. … For the same reason as above, we see that any prolongation of the succession `{f_i}`
> satisfying (1), (2) and (3) induces the same kind of prolongation of `{f̂_i}`.  (p. 175)

Contents:
* `MonoidalSuccession.baseChange`: the base change of a finite succession along a flat morphism `c`, by
  `MonoidalTransformation.baseChange` (`j' = pullback.fst`) at each stage; its flatness, the pull-back squares,
  its centers `c_i⁻¹(B_i)`, the compatibility with strict transforms (iterating
  `MonoidalTransformation.totalTransform_strictTransform_of_flat_square`, Compat/FlatStrictTransform), with append;
* the flatness of `AB.c0 X x : Spec(Ô_{X,x}) → X` for every point of a locally noetherian scheme (the existing
  `flat_c0` asks `X.IsSimpleAt x₀`);
* the strict transform of a reduced subscheme is reduced for an arbitrary (singular) ambient scheme (the existing
  `MonoidalTransformation.isReduced_strictTransform` asks `X.IsNonsingular`);
* the strict transform along isomorphic monoidal transformations with the same center;
* a succession whose centers avoid the range of a flat `c` has base change with all centers empty.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

namespace Hironaka

universe u

/-! ### The base change of a succession -/

namespace MonoidalSuccession

/-- The base change of a finite succession `s : X ⟶ Y` along a flat morphism `c : Z ⟶ X`: the monoidal
transformation `t` with center `B` is replaced by `t.baseChange c`, with center `c⁻¹(B)`, and the rest of the
succession by its base change along `pullback.fst t.f c : pullback t.f c ⟶ t.X'` (which is flat again).
Returns the end scheme `Z'`, the succession `Z ⟶ Z'` and the canonical morphism `c' : Z' ⟶ Y`. -/
noncomputable def baseChange : {X Y : Scheme.{u}} → MonoidalSuccession X Y → {Z : Scheme.{u}} →
    (c : Z ⟶ X) → [Flat c] → Σ Z' : Scheme.{u}, MonoidalSuccession Z Z' × (Z' ⟶ Y)
  | _, _, nil _, Z, c, _ => ⟨Z, nil Z, c⟩
  | _, _, cons B t rest, _, c, _ =>
      ⟨(rest.baseChange (pullback.fst t.f c)).1,
        cons (Subscheme.totalTransform c B) (t.baseChange c)
          (rest.baseChange (pullback.fst t.f c)).2.1,
        (rest.baseChange (pullback.fst t.f c)).2.2⟩

variable {X Y : Scheme.{u}} (s : MonoidalSuccession X Y) {Z : Scheme.{u}} (c : Z ⟶ X) [Flat c]

/-- The end scheme `V̂₀(r)` of the base change `{f̂_i}` of `{f_i}`. -/
noncomputable abbrev baseChangeTarget : Scheme.{u} := (s.baseChange c).1

/-- The base change `{f̂_i}` of `{f_i}` along `c`. -/
noncomputable abbrev baseChangeSucc : MonoidalSuccession Z (s.baseChangeTarget c) :=
  (s.baseChange c).2.1

/-- The canonical morphism `c_r : V̂₀(r) ⟶ V₀(r)`. -/
noncomputable abbrev baseChangeMap : s.baseChangeTarget c ⟶ Y := (s.baseChange c).2.2

/-- p. 175: "We see that `c_i` is a flat morphism." -/
instance flat_baseChangeMap : Flat (s.baseChangeMap c) := by
  induction s generalizing Z with
  | nil X => exact ‹Flat c›
  | cons B t rest ih => exact ih (pullback.fst t.f c)

/-- p. 175: "`V̂₀(i)` is the product of the `V₀`-schemes `V₀(i)` and `V̂₀`": the square `(c_r, ĝ_r, g_r, c)`
is a pull-back square. -/
theorem isPullback_baseChange :
    IsPullback (s.baseChangeMap c) (s.baseChangeSucc c).composite s.composite c := by
  induction s generalizing Z with
  | nil X => exact IsPullback.id_vert c
  | cons B t rest ih =>
    exact (ih (pullback.fst t.f c)).paste_vert (IsPullback.of_hasPullback t.f c)

theorem length_baseChangeSucc : (s.baseChangeSucc c).length = s.length := by
  induction s generalizing Z with
  | nil X => rfl
  | cons B t rest ih =>
    simp only [baseChangeSucc, baseChange, length_cons]
    exact congrArg (· + 1) (ih (pullback.fst t.f c))

/-- p. 175: "`f̂_i` is the monoidal transformation with center `B̂_i = c_i⁻¹(B_i)`": the centers of the base change
are the total transforms of the centers (stated through the strict transform of the centers; the shape
`cons (c⁻¹ B) (t.baseChange c) _` is `rfl`). -/
theorem baseChange_cons {B : Subscheme X} (t : MonoidalTransformation X B)
    (rest : MonoidalSuccession t.X' Y) :
    (cons B t rest).baseChange c =
      ⟨(rest.baseChange (pullback.fst t.f c)).1,
        cons (Subscheme.totalTransform c B) (t.baseChange c)
          (rest.baseChange (pullback.fst t.f c)).2.1,
        (rest.baseChange (pullback.fst t.f c)).2.2⟩ := rfl

/-- p. 175: "`V̂_j(i) = c_i⁻¹(V_j(i))` for all `j` and `i` … the canonical morphisms `V̂_j(i+1) → V̂_j(i)` may be
identified with the monoidal transformations with center `B̂_i`": the iterated form of
`MonoidalTransformation.totalTransform_strictTransform_of_flat_square`. -/
theorem strictTransform_baseChangeSucc (V : Subscheme X) :
    (s.baseChangeSucc c).strictTransform (Subscheme.totalTransform c V) =
      Subscheme.totalTransform (s.baseChangeMap c) (s.strictTransform V) := by
  induction s generalizing Z with
  | nil X => rfl
  | cons B t rest ih =>
    have hfl : Flat (pullback.fst t.f c) := inferInstance
    have hst := @MonoidalTransformation.totalTransform_strictTransform_of_flat_square _ _ _ t _
      (t.baseChange c) c (pullback.fst t.f c) hfl pullback.condition rfl V
    have := ih (pullback.fst t.f c) (Subscheme.strictTransform t V)
    change (rest.baseChangeSucc (pullback.fst t.f c)).strictTransform
      (Subscheme.strictTransform (t.baseChange c) (Subscheme.totalTransform c V)) = _
    rw [← hst]
    exact this

/-- "For the same reason as above, we see that any prolongation of the succession `{f_i}` … induces the same kind of
prolongation of `{f̂_i}`": the base change of `s.append s'` is the base change of `s` followed by the base change
of `s'` along `c_r`. -/
theorem baseChange_append {Y' : Scheme.{u}} (s' : MonoidalSuccession Y Y') :
    (s.append s').baseChange c =
      ⟨(s'.baseChange (s.baseChangeMap c)).1,
        (s.baseChangeSucc c).append (s'.baseChange (s.baseChangeMap c)).2.1,
        (s'.baseChange (s.baseChangeMap c)).2.2⟩ := by
  induction s generalizing Z with
  | nil X => rfl
  | cons B t rest ih =>
    have := ih (pullback.fst t.f c)
    rw [cons_append]
    simp only [baseChange]
    rw [this]
    rfl

/-! ### Successions whose centers are all empty -/

/-- All the centers of the succession are the empty subscheme (the monoidal transformations are isomorphisms). -/
def AllCentersEmpty : {X Y : Scheme.{u}} → MonoidalSuccession X Y → Prop
  | _, _, nil _ => True
  | _, _, cons B _ rest => B = Subscheme.empty ∧ rest.AllCentersEmpty

/-- p. 175–176: "any succession of monoidal transformations which appears in the application of theorem I(n′)
induces in `V̂₀(r)` a succession of monoidal transformations with empty centers": if the centers of `s` avoid the
range of the flat morphism `c` (`MonoidalSuccession.CentersAvoid`), the base change of `s` has all centers empty.
(`CentersAvoid` is the hypothesis of `exists_lift_of_centersAvoid`, which needs a preimmersion; here `c` is only
flat.) -/
theorem allCentersEmpty_baseChangeSucc (hs : s.CentersAvoid (Set.range c.base)) :
    (s.baseChangeSucc c).AllCentersEmpty := by
  induction s generalizing Z with
  | nil X => trivial
  | cons B t rest ih =>
    obtain ⟨hB, hrest⟩ := hs
    refine ⟨?_, ?_⟩
    · apply Subscheme.eq_empty_of_pts_eq_empty
      rw [FlatPreimm.pts_totalTransform]
      refine Set.eq_empty_iff_forall_notMem.mpr fun z hz => hB _ hz ⟨z, rfl⟩
    · have h : rest.CentersAvoid (Set.range (pullback.fst t.f c).base) := by
        rw [Scheme.Pullback.range_fst]
        exact hrest
      exact ih (pullback.fst t.f c) h

/-- A succession with all centers empty has an isomorphism as composite. -/
theorem isIso_composite_of_allCentersEmpty {s : MonoidalSuccession X Y} (hs : s.AllCentersEmpty) :
    IsIso s.composite := by
  induction s with
  | nil X => exact inferInstanceAs (IsIso (𝟙 X))
  | cons B t rest ih =>
    obtain ⟨hB, hrest⟩ := hs
    have h1 : IsIso t.f := MonoidalTransformation.isIso_of_eq_empty t hB
    have h2 := ih hrest
    exact inferInstanceAs (IsIso (rest.composite ≫ t.f))

/-- The strict transform along a monoidal transformation with empty center is the total transform: the
exceptional subscheme is empty, so the saturation `⋃ₙ (f⁻¹(I) : ⊤ⁿ)` of `strictTransform_stalkIdeal` is `f⁻¹(I)`. -/
theorem _root_.Hironaka.MonoidalTransformation.strictTransform_eq_totalTransform_of_eq_empty
    {X : Scheme.{u}} {B : Subscheme X} (t : MonoidalTransformation X B) (h : B = Subscheme.empty)
    (V : Subscheme X) : Subscheme.strictTransform t V = Subscheme.totalTransform t.f V := by
  subst h
  refine Subscheme.ext_stalkIdeal fun x' => ?_
  rw [Subscheme.strictTransform_stalkIdeal]
  have hE : t.exceptional.stalkIdeal x' = ⊤ := by
    unfold MonoidalTransformation.exceptional
    rw [Subscheme.totalTransform_empty]
    exact Subscheme.stalkIdeal_top_eq x'
  refine le_antisymm (iSup_le fun n => ?_) (le_iSup_of_le 0 ?_)
  · intro r hr
    rw [hE, Ideal.top_pow] at hr
    have := Submodule.mem_colon.mp hr 1 (Submodule.mem_top)
    simpa using this
  · intro r hr
    refine Submodule.mem_colon.mpr fun p _ => ?_
    rw [smul_eq_mul]
    exact Ideal.mul_mem_right _ _ hr

/-- Along a succession with all centers empty the strict transform is the total transform (the pull-back along the
composite, an isomorphism): the exceptional divisors are empty. -/
theorem totalTransform_composite_eq_strictTransform_of_allCentersEmpty {s : MonoidalSuccession X Y}
    (hs : s.AllCentersEmpty) (D : Subscheme X) :
    Subscheme.totalTransform s.composite D = s.strictTransform D := by
  induction s with
  | nil X => simp
  | cons B t rest ih =>
    obtain ⟨hB, hrest⟩ := hs
    rw [composite_cons, Subscheme.totalTransform_comp, strictTransform_cons,
      ← MonoidalTransformation.strictTransform_eq_totalTransform_of_eq_empty t hB D]
    exact ih hrest _

end MonoidalSuccession

/-! ### Flatness of the completion morphism at an arbitrary point -/

/-- `AB.c0 X x : Spec(Ô_{X,x}) → X` is flat for every point `x` of a locally noetherian scheme `X` (the
completion of a noetherian local ring is flat over it, `faithfullyFlat_adicCompletion_maximalIdeal`).  The existing
`flat_c0` (Ch4/ImplicationsAB) asks `X.IsSimpleAt x₀`, which its proof only uses to have `IsNoetherianRing`. -/
theorem flat_c0_of_isLocallyNoetherian (X : Scheme.{u}) [IsLocallyNoetherian X] (x : X) :
    Flat (AB.c0 X x) := by
  have := faithfullyFlat_adicCompletion_maximalIdeal (X.presheaf.stalk x)
  have h1 : Flat (Spec.map (CommRingCat.ofHom
      (algebraMap (X.presheaf.stalk x) (AB.Shat X x)))) :=
    Flat.SpecMap_iff.mpr (RingHom.flat_algebraMap_iff.mpr inferInstance)
  have := flat_fromSpecStalk X x
  exact (inferInstance : Flat (Spec.map (CommRingCat.ofHom
      (algebraMap (X.presheaf.stalk x) (AB.Shat X x))) ≫ X.fromSpecStalk x))

/-- p. 175: "We see that `c_i` is a flat morphism", for `i = 0`, on an algebraic scheme. -/
instance flat_c0_of_isAlgebraicScheme (X : Scheme.{u}) [IsAlgebraicScheme X] (x : X) : Flat (AB.c0 X x) := by
  have := IsAlgebraicScheme.isNoetherian X
  exact flat_c0_of_isLocallyNoetherian X x

/-! ### Strict transforms: reducedness for a singular ambient scheme, isomorphic transformations -/

namespace MonoidalTransformation

variable {X : Scheme.{u}} {B : Subscheme X}

/-- The strict transform of a reduced subscheme is reduced, for an arbitrary scheme `X` (no non-singularity: the
strict transform is the scheme-theoretic closure of the reduced part off the exceptional divisor, where the
monoidal transformation is a local isomorphism).  Generalizes `MonoidalTransformation.isReduced_strictTransform`
(Ch4/ImplicationsCD, which asks `X.IsNonsingular`); used for "`W(r)` is reduced" in Main Theorem I(n). -/
theorem isReduced_strictTransform_of_isReduced (t : MonoidalTransformation X B) (V : Subscheme X)
    (hV : V.IsReduced) : (Subscheme.strictTransform t V).IsReduced := by
  set D := Subscheme.strictTransform t V with hD
  have hle : D ≤ Scheme.IdealSheafData.radical D := by
    intro U
    exact Ideal.le_radical
  have hmem : Scheme.IdealSheafData.radical D ∈
      {V' : Subscheme t.X' | ∀ x' : t.X', x' ∉ t.exceptional.pts →
        V'.stalkIdeal x' = (Subscheme.totalTransform t.f V).stalkIdeal x'} := by
    intro x' hx'
    have hfx : t.f.base x' ∉ B.pts := fun h => hx' (by rw [t.pts_exceptional]; exact h)
    have hbij := bijective_stalkMap_of_notMem_pts t x' hfx
    have hDx : D.stalkIdeal x' = (Subscheme.totalTransform t.f V).stalkIdeal x' :=
      strictTransform_stalkIdeal_of_notMem t V hx'
    have hrad : ((Subscheme.totalTransform t.f V).stalkIdeal x').IsRadical := by
      rw [stalkIdeal_totalTransform]
      have h1 := Subscheme.isRadical_stalkIdeal_of_isReduced hV (t.f.base x')
      have hsurj : Function.Surjective (t.f.stalkMap x').hom := hbij.2
      have hker : RingHom.ker (t.f.stalkMap x').hom ≤ V.stalkIdeal (t.f.base x') := by
        rw [(RingHom.injective_iff_ker_eq_bot _).mp hbij.1]; exact bot_le
      have h2 := Ideal.map_radical_of_surjective hsurj hker
      rw [h1.radical] at h2
      exact Ideal.radical_eq_iff.mp h2.symm
    apply le_antisymm
    · calc Subscheme.stalkIdeal (Scheme.IdealSheafData.radical D) x' ≤ (D.stalkIdeal x').radical :=
            AB.stalkIdeal_radical_le D x'
        _ = D.stalkIdeal x' := by rw [hDx]; exact hrad.radical
        _ = _ := hDx
    · rw [← hDx]
      exact Subscheme.stalkIdeal_mono hle x'
  have h2 : Scheme.IdealSheafData.radical D ≤ D := le_sSup hmem
  exact Subscheme.isReduced_of_radical_eq D (le_antisymm h2 hle)

/-- Two monoidal transformations with the same center, isomorphic over `X` (`unique_up_to_iso`), have
corresponding strict transforms: if `e : t.X' ≅ t'.X'` and `e.hom ≫ t'.f = t.f` then the pull-back of the strict
transform along `t'` by `e` is the strict transform along `t`. -/
theorem totalTransform_strictTransform_of_iso (t t' : MonoidalTransformation X B) (e : t.X' ≅ t'.X')
    (he : e.hom ≫ t'.f = t.f) (V : Subscheme X) :
    Subscheme.totalTransform e.hom (Subscheme.strictTransform t' V) = Subscheme.strictTransform t V := by
  have hf : Flat e.hom := inferInstance
  have := @totalTransform_strictTransform_of_flat_square _ _ _ t' _ t (𝟙 X) e.hom hf
    (by simpa using he) (by simp) V
  simpa using this

end MonoidalTransformation

end Hironaka
