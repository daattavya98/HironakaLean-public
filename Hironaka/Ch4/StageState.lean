/-
Copyright (c) 2026 Daattavya Aggarwal, Minhyong Kim, Oisin Kim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daattavya Aggarwal, Minhyong Kim, Oisin Kim
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.Data.List.GetD
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Architect
public import Hironaka.Ch4.ImplicationsAB
public import Hironaka.Ch4.ComponentwiseConstruction
public import Hironaka.Compat.ExceptionalTransversal
public import Hironaka.Compat.DatumRefinement
public import Hironaka.Ch4.TowerExtension
public import Hironaka.Statements

/-!
# Ch. IV §3 (p. 310): the stage-`s` state of the construction, as a fold along a succession

Formalization infrastructure for the last step of the proof of Theorems A* and B* (p. 310):

  "by replacing the original succession `g_s : X_s → X` by one that includes the above
  succession, …"

The proof extends the succession `g_s` (the first `s` blow-ups of the tower) by further monoidal
transformations, and the objects of §3 at the stage `s` (the completion `X̂_s`, the subscheme
`X̄_s`, the ideal `J̄(s)`, the open set `X̂*'_s`, the boundary components `E_j(s)`, hence the datum
`ℜ^{N-1}_II` on `X̃`) must be *the same* for the old and the new tower: the paper writes "we
construct `X̂_s`, … in the same process" and keeps `X̃` and `ℜ^{N-1}` fixed.  A `Frame` is built
on an infinite `Tower`, and its stage-`s` objects are indexed by `s`, so two towers with the same
initial segment have no obviously equal stage-`s` objects.

This file removes that obstruction (it has no counterpart in the paper):

* `StageState Y` packages everything the stage after `Y = X_s` depends on, indexed by the
  *current scheme* `Y`;
* `StageState.step` is one stage of the construction (pp. 295–299, with the componentwise
  condition [g*], [h*] of `Hironaka.Ch4.ComponentwiseConstruction`);
* `StageState.fold` runs it along a finite `MonoidalSuccession` (front recursion, so
  `StageState.fold_append` holds by induction and no cast is needed);
* for a frame `Frame.canon` over the canonical completion `Tower.completion`, the stage-`s` state
  of the frame, `Frame.stageOf`, is the fold of `T.pre s` over the initial state
  (`Frame.canon_stageOf_eq_fold`), hence depends on the tower only through `T.pre s`
  (`Frame.canon_stageOf_locality`);
* the objects `X̃`, `J̄(s)` on `X̃` and `ℜ^{N-1}_II` of p. 308 are read off a state
  (`StageState.xTilde`, `jBarT`, `datumII`) and agree with those of the removal family
  `Frame.removalFamilyStar` of the frame (`Frame.stageOf_xTilde_eq` etc.), the datum being kept
  exactly as built (with all the `Ẽ_j`, no splitting and no removal);
* the trivial step (`StageState.exists_iso_xTilde_step_of_forall_notMem`): a center missing
  `c̃(X̃)` induces an isomorphism `X̃_{s+1} ≅ X̃_s` carrying `J̄` and the `Ẽ_j` along (the new
  exceptional component is empty).  This is the formal content of "These monoidal
  transformations are successively permissible for ℜ(s) and induce trivial monoidal
  transformations of X̃ by Remarks 4 and 5" (p. 310);
* the blow-up step (`StageState.BlowupHyp.exists_transform_eq_datumII`): a center whose trace on
  `X̃` is `B̃` induces the monoidal transformation of `X̃` with center `B̃`; the transform of the
  raw datum `ℜ^{N-1}_II` of the state is the datum of the next state (the `Ẽ'_j` are the strict
  transforms of the `Ẽ_j`), and `J̃' ∏ Ẽ'_j^{a'_j} = J̄(s+1)`.  This is the formal content of
  "Then the permissible monoidal transformation `f_{B_s}` … induces the given permissible
  monoidal transformation `f_B̃` of X̃ for ℜ^{N-1}_II" (p. 310);
* a standing tower from a prepared finite succession
  (`exists_standing_prepHyp_of_prepHypSucc`): a finite permissible succession `g` satisfying
  `[(1)]`, `[(2)]` and `x_0 ∈ g(S)` (`PrepHypSucc`) is the initial segment `g_m` of a tower with
  empty centers from `m` on which satisfies `Standing` and `PrepHyp` at `m` (the AB analogue of
  `CD.exists_standing_prepHyp_tower`); this is the tacit "by replacing the original succession
  `g_s` by one that includes the above succession" (p. 310).

No statement of the paper is formalized here, and nothing is cited.  The notation is that of
`Hironaka/Ch4/ImplicationsAB.lean`.
-/

@[expose] public section

open AlgebraicGeometry IsLocalRing CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

namespace Hironaka

universe u

noncomputable section

/-- Congruence for `divPow (f⁻¹ J) (f⁻¹ B) b` in the morphism `f` and the subschemes `J`, `B`:
the stage objects are compared through this lemma, since asking the unifier to compare them
directly unfolds the limit cones of the completion. -/
theorem Subscheme.divPow_totalTransform_congr {Z Z' : Scheme.{u}} {f g : Z ⟶ Z'} (h : f = g)
    {J B J' B' : Subscheme Z'} (hJ : J = J') (hB : B = B') (b : ℕ) :
    Subscheme.divPow (Subscheme.totalTransform f J) (Subscheme.totalTransform f B) b =
      Subscheme.divPow (Subscheme.totalTransform g J') (Subscheme.totalTransform g B') b := by
  subst h hJ hB
  rfl

namespace MonoidalSuccession

variable {X Y : Scheme.{u}}

/-- `g` followed by `t` is permissible for `(ℜ, F)` iff `g` is and `t` is permissible for the
transform. -/
theorem isPermissibleIClosed_snoc_iff (g : MonoidalSuccession X Y) (B : Subscheme Y)
    (t : MonoidalTransformation Y B) (ℜ : DatumI.Raw X) (F : Subscheme X) :
    (g.snoc B t).IsPermissibleIClosed ℜ F ↔
      g.IsPermissibleIClosed ℜ F ∧
        (g.transformI ℜ).IsPermissibleClosed (g.strictTransform F) B := by
  induction g with
  | nil X => simp [snoc, IsPermissibleIClosed, transformI, strictTransform]
  | cons B' t' rest ih =>
    simp only [snoc, IsPermissibleIClosed, transformI, strictTransform, ih, and_assoc]

/-- `g` followed by `t` is permissible for `(ℜ, U)` iff `g` is and `t` is permissible for the
transform. -/
theorem isPermissibleIOpen_snoc_iff (g : MonoidalSuccession X Y) (B : Subscheme Y)
    (t : MonoidalTransformation Y B) (ℜ : DatumI.Raw X) (U : Set X) :
    (g.snoc B t).IsPermissibleIOpen ℜ U ↔
      g.IsPermissibleIOpen ℜ U ∧ (g.transformI ℜ).IsPermissibleOpen (g.transformOpen U) B := by
  induction g with
  | nil X => simp [snoc, IsPermissibleIOpen, transformI, transformOpen]
  | cons B' t' rest ih =>
    simp only [snoc, IsPermissibleIOpen, transformI, transformOpen, ih, and_assoc]

end MonoidalSuccession

namespace DatumI.Raw

/-- The monoidal transformation with empty center is permissible for every datum (the extended
tuple `(E; V_1, …, V_β, W; ∅)` has an empty principal subscheme). -/
theorem isPermissible_empty {X : Scheme.{u}} {ℜ : DatumI.Raw X} (hℜ : ℜ.IsDatum) :
    ℜ.IsPermissible (Subscheme.empty : Subscheme X) := by
  refine ⟨Or.inl rfl, ⟨hℜ.1, hℜ.2.1, hℜ.2.2.1, Subscheme.isReduced_empty, fun j => ?_⟩,
    fun x hx => ?_⟩
  · refine Subscheme.isContainedIn_of_pts_subset Subscheme.isReduced_empty ?_
    show (Subscheme.empty : Subscheme X).pts ⊆ _
    rw [Subscheme.pts_empty]
    exact Set.empty_subset _
  · exfalso
    have : x ∈ (Subscheme.empty : Subscheme X).pts := hx
    rw [Subscheme.pts_empty] at this
    exact this

end DatumI.Raw

namespace AB

/-! ### The state -/

/-- The stage-`s` objects of the construction of pp. 295–299 (completion, frame, star family),
indexed by the current scheme `Y = X_s`: everything the next stage depends on.  Formalization
infrastructure for the replacement of `g_s` by an extension (p. 310). -/
structure StageState (Y : Scheme.{u}) where
  /-- `X̂_s`. -/
  xHat : Scheme.{u}
  /-- `c_s : X̂_s → X_s`. -/
  c : xHat ⟶ Y
  /-- `c_s` is flat. -/
  flat : Flat c
  /-- `X̄_s ⊆ X̂_s`. -/
  xBar : Subscheme xHat
  /-- `J̄(s)` on `X̄_s`. -/
  jBar : Subscheme xBar.toScheme
  /-- `X̂*'_s`, as a set: this makes `StageState.step` total, and openness is a separate fact
  (`Frame.isOpen_stageOf_xHatPrimeStar`). -/
  xHatPrimeStar : Set xHat
  /-- The boundary components `E_1(s), …, E_{α+s}(s)` on `X_s`. -/
  boundary : List (Subscheme Y)

attribute [instance] StageState.flat

namespace StageState

variable {Y : Scheme.{u}} (σ : StageState Y)

/-- `B̂ = c⁻¹(B)` in `X̂`. -/
def bHat (B : Subscheme Y) : Subscheme σ.xHat := Subscheme.totalTransform σ.c B

/-- `B̄ = ι⁻¹(B̂)` on `X̄`. -/
def bBarOn (B : Subscheme Y) : Subscheme σ.xBar.toScheme :=
  Subscheme.totalTransform σ.xBar.ι (σ.bHat B)

/-- A component `K` of `B̂` is good: `K ⊆ X̄` and `J̄ ⊆ P(B̄)^b` over `K` on `X̂*' ∩ X̄`
(the condition [g*] of `Hironaka.Ch4.ComponentwiseConstruction`). -/
def IsGoodComponent (b : ℕ) (B : Subscheme Y) (K : Subscheme σ.xHat) : Prop :=
  K.IsContainedIn σ.xBar ∧ ∀ xb : σ.xBar.toScheme, σ.xBar.ι.base xb ∈ σ.xHatPrimeStar →
    σ.xBar.ι.base xb ∈ K.pts → σ.jBar.stalkIdeal xb ≤ ((σ.bBarOn B).stalkIdeal xb) ^ b

/-- The bad locus `Bad`: the union of the components of `B̂` that are not good. -/
def badLocus (b : ℕ) (B : Subscheme Y) : Set σ.xHat :=
  ⋃ K ∈ {K ∈ (σ.bHat B).irreducibleComponents | ¬ σ.IsGoodComponent b B K}, K.pts

/-- One stage of the construction: `X̂_{s+1} = X_{s+1} ×_{X_s} X̂_s`, `X̄_{s+1}` the strict
transform of `X̄_s`, `J̄(s+1) = f̄_s⁻¹(J̄(s)) / (f̄_s⁻¹(B̄_s))^b`,
`X̂*'_{s+1} = f̂_s⁻¹(X̂*'_s − Bad_s)` and the boundary `E_j(s+1)` = the strict transforms of the
`E_j(s)` followed by the exceptional divisor (pp. 295–299). -/
@[reducible] noncomputable def step (b : ℕ) {B : Subscheme Y} (t : MonoidalTransformation Y B) :
    StageState t.X' where
  xHat := pullback t.f σ.c
  c := pullback.fst t.f σ.c
  flat := inferInstance
  xBar := Subscheme.strictTransform (t.baseChange σ.c) σ.xBar
  jBar := Subscheme.divPow
    (Subscheme.totalTransform ((t.baseChange σ.c).strictTransformMap σ.xBar) σ.jBar)
    (Subscheme.totalTransform ((t.baseChange σ.c).strictTransformMap σ.xBar) (σ.bBarOn B)) b
  xHatPrimeStar := (pullback.snd t.f σ.c).base ⁻¹' (σ.xHatPrimeStar \ σ.badLocus b B)
  boundary := σ.boundary.map (Subscheme.strictTransform t) ++ [t.exceptional]

/-- `J̄(s+1)` of a step, in terms of the strict transform `f̄_s`. -/
theorem step_jBar {B : Subscheme Y} (b : ℕ) (t : MonoidalTransformation Y B) :
    (σ.step b t).jBar = Subscheme.divPow
      (Subscheme.totalTransform ((t.baseChange σ.c).strictTransformMap σ.xBar) σ.jBar)
      (Subscheme.totalTransform ((t.baseChange σ.c).strictTransformMap σ.xBar)
        (σ.bBarOn B)) b := rfl

/-- `f̄_s : X̄_{s+1} → X̄_s`, induced by the step (p. 298). -/
def fBar (b : ℕ) {B : Subscheme Y} (t : MonoidalTransformation Y B) :
    (σ.step b t).xBar.toScheme ⟶ σ.xBar.toScheme :=
  (t.baseChange σ.c).strictTransformMap σ.xBar

/-- `ι_s ∘ f̄_s = f̂_s ∘ ι_{s+1}`, where `f̂_s : X̂_{s+1} → X̂_s` is the second projection. -/
theorem fBar_comp_ι (b : ℕ) {B : Subscheme Y} (t : MonoidalTransformation Y B) :
    σ.fBar b t ≫ σ.xBar.ι = (σ.step b t).xBar.ι ≫ pullback.snd t.f σ.c :=
  (t.baseChange σ.c).strictTransformMap_ι σ.xBar

/-- Extensionality for states, with the `HEq`s forced by the dependence of the fields on
`xHat` and `xBar`. -/
theorem ext_of_heq {σ₁ σ₂ : StageState Y} (h1 : σ₁.xHat = σ₂.xHat) (h2 : HEq σ₁.c σ₂.c)
    (h3 : HEq σ₁.xBar σ₂.xBar) (h4 : HEq σ₁.jBar σ₂.jBar)
    (h5 : HEq σ₁.xHatPrimeStar σ₂.xHatPrimeStar) (h6 : σ₁.boundary = σ₂.boundary) :
    σ₁ = σ₂ := by
  cases σ₁; cases σ₂
  simp only at h1 h6
  subst h1 h6
  simp only [heq_eq_eq] at h2 h3 h4 h5
  subst h2 h3 h4 h5
  rfl

/-- The initial state, from the tower-independent data: `X̂_0 = Spec Ŝ`, `c_0`, `X̄_0 = V(z)`,
`J̄(0)` the ideal generated by `jGen`, `X̂*'_0 = X̂_0` ([f*]) and the boundary `E_1, …, E_α`. -/
def initial {X : Scheme.{u}} {x₀ : X} {α : ℕ} (E : Fin α → Subscheme X) (hx : X.IsSimpleAt x₀)
    (z : Shat X x₀) (jGen : Set (Shat X x₀)) : StageState X where
  xHat := xHat0 X x₀
  c := c0 X x₀
  flat := flat_c0 X x₀ hx
  xBar := vZ X x₀ z
  jBar := Subscheme.totalTransform (vZ X x₀ z).ι (Scheme.IdealSheafData.ofIdealTop
    ((Ideal.span jGen).map (Scheme.ΓSpecIso (CommRingCat.of (Shat X x₀))).inv.hom))
  xHatPrimeStar := Set.univ
  boundary := List.ofFn E

end StageState

/-! ### The fold along a finite succession -/

/-- Fold the stage construction along a finite succession (front recursion: no casts). -/
noncomputable def StageState.fold (b : ℕ) :
    ∀ {Y Z : Scheme.{u}}, MonoidalSuccession Y Z → StageState Y → StageState Z
  | _, _, .nil _, σ => σ
  | _, _, .cons _ t rest, σ => StageState.fold b rest (σ.step b t)

/-- Folding a succession `(t, rest)` steps by `t` first, then folds `rest`. -/
theorem StageState.fold_cons (b : ℕ) {Y : Scheme.{u}} {B : Subscheme Y}
    (t : MonoidalTransformation Y B) {Z : Scheme.{u}} (rest : MonoidalSuccession t.X' Z)
    (σ : StageState Y) :
    StageState.fold b (MonoidalSuccession.cons B t rest) σ =
      StageState.fold b rest (σ.step b t) := rfl

/-- Folding an appended succession `g ++ h` folds `g` and then `h`. -/
theorem StageState.fold_append (b : ℕ) {Y Z W : Scheme.{u}} (g : MonoidalSuccession Y Z)
    (h : MonoidalSuccession Z W) (σ : StageState Y) :
    StageState.fold b (g.append h) σ = StageState.fold b h (StageState.fold b g σ) := by
  induction g with
  | nil X => rfl
  | cons B t rest ih => exact ih h (σ.step b t)

/-- Folding `g` followed by one more transformation `t` is one more step. -/
theorem StageState.fold_snoc (b : ℕ) {Y Z : Scheme.{u}} (g : MonoidalSuccession Y Z)
    {B : Subscheme Z} (t : MonoidalTransformation Z B) (σ : StageState Y) :
    StageState.fold b (g.snoc B t) σ = (StageState.fold b g σ).step b t := by
  induction g with
  | nil X => rfl
  | cons B' t' rest ih => exact ih t (σ.step b t')

/-! ### The bridge with a frame over the canonical completion -/

section Bridge

variable {N n : ℕ} {X : Scheme.{u}} {ℜ : DatumI.Raw X} {P : DatumI.Presentation ℜ}
  {r : Restriction X} {T : Tower X} {x₀ : X} {hS : Standing N n ℜ P r T x₀}

/-- The stage-`s` state of a frame (the star family `X̂*'_s` of
`Hironaka.Ch4.ComponentwiseConstruction`): `X̂_s`, `c_s`, `X̄_s`, `J̄(s)`, `X̂*'_s` and the
boundary `E_1(s), …, E_{α+s}(s)`. -/
def Frame.stageOf [Hironaka.HironakaCitedResults.{u}] (𝒮 : Frame hS) (s : ℕ) : StageState (T.X s) where
  xHat := 𝒮.tHat.X s
  c := 𝒮.c s
  flat := 𝒮.toCompletion.flat_c (hS.ambient.2.1 x₀) s
  xBar := 𝒮.xBar s
  jBar := 𝒮.jBar s
  xHatPrimeStar := ((𝒮.xHatPrimeStar s : (𝒮.tHat.X s).Opens) : Set (𝒮.tHat.X s))
  boundary := List.ofFn (T.Esys P.E s)

/-- The set `X̂*'_s` of a frame's state is open. -/
theorem Frame.isOpen_stageOf_xHatPrimeStar [Hironaka.HironakaCitedResults.{u}] (𝒮 : Frame hS) (s : ℕ) :
    IsOpen (𝒮.stageOf s).xHatPrimeStar :=
  (𝒮.xHatPrimeStar s).isOpen

variable [IsRegularLocalRing (Shat X x₀)] {z : Shat X x₀} {b : ℕ} {jGen : Set (Shat X x₀)}
  {fr : FrameSpec x₀ (hS.ambient.2.1 x₀) ℜ r z b jGen}

/-- The stage-`0` state of a frame over the canonical completion is the initial state. -/
theorem Frame.canon_stageOf_zero [Hironaka.HironakaCitedResults.{u}] :
    (Frame.canon hS z b jGen fr).stageOf 0 = StageState.initial P.E (hS.ambient.2.1 x₀) z jGen :=
  rfl

/-- `X̂_{s+1}` of the frame is that of the step of the stage-`s` state. -/
theorem Frame.canon_stageOf_succ_xHat [Hironaka.HironakaCitedResults.{u}] (s : ℕ) :
    ((Frame.canon hS z b jGen fr).stageOf (s + 1)).xHat =
      (((Frame.canon hS z b jGen fr).stageOf s).step b (T.monoidalTransformation s)).xHat := by
  cases s <;> rfl

/-- `c_{s+1}` of the frame is that of the step of the stage-`s` state. -/
theorem Frame.canon_stageOf_succ_c [Hironaka.HironakaCitedResults.{u}] (s : ℕ) :
    HEq ((Frame.canon hS z b jGen fr).stageOf (s + 1)).c
      (((Frame.canon hS z b jGen fr).stageOf s).step b (T.monoidalTransformation s)).c := by
  cases s <;> rfl

/-- `X̄_{s+1}` of the frame is that of the step of the stage-`s` state. -/
theorem Frame.canon_stageOf_succ_xBar [Hironaka.HironakaCitedResults.{u}] (s : ℕ) :
    HEq ((Frame.canon hS z b jGen fr).stageOf (s + 1)).xBar
      (((Frame.canon hS z b jGen fr).stageOf s).step b (T.monoidalTransformation s)).xBar := by
  cases s <;> rfl

/-- Over the canonical completion, `f̄_s` is the map induced by the base change of `f_s`. -/
theorem Frame.canon_fBar_heq [Hironaka.HironakaCitedResults.{u}] (s : ℕ) :
    HEq ((Frame.canon hS z b jGen fr).fBar s)
      (((T.monoidalTransformation s).baseChange
        ((Frame.canon hS z b jGen fr).stageOf s).c).strictTransformMap
        ((Frame.canon hS z b jGen fr).xBar s)) := by
  cases s <;> rfl

/-- `B̄_s` of the frame is that of the stage-`s` state. -/
theorem Frame.canon_bBarOn_stageOf [Hironaka.HironakaCitedResults.{u}] (s : ℕ) :
    (Frame.canon hS z b jGen fr).bBarOn s =
      ((Frame.canon hS z b jGen fr).stageOf s).bBarOn (T.B s) := by
  cases s <;> rfl

/-- `Bad_s` of the frame is that of the stage-`s` state. -/
theorem Frame.canon_badLocusStar_stageOf [Hironaka.HironakaCitedResults.{u}] (s : ℕ) :
    (Frame.canon hS z b jGen fr).badLocusStar s =
      ((Frame.canon hS z b jGen fr).stageOf s).badLocus b (T.B s) := by
  cases s <;> rfl

/-- `J̄(s+1)` of the frame is that of the step of the stage-`s` state. -/
theorem Frame.canon_stageOf_succ_jBar [Hironaka.HironakaCitedResults.{u}] (s : ℕ) :
    HEq ((Frame.canon hS z b jGen fr).stageOf (s + 1)).jBar
      (((Frame.canon hS z b jGen fr).stageOf s).step b (T.monoidalTransformation s)).jBar := by
  have hb := Frame.canon_bBarOn_stageOf (hS := hS) (fr := fr) s
  have hf := Frame.canon_fBar_heq (hS := hS) (fr := fr) s
  have e2 := Frame.jBar_succ (Frame.canon hS z b jGen fr) s
  cases s with
  | zero =>
    apply heq_of_eq
    have hf := eq_of_heq hf
    exact e2.trans (Subscheme.divPow_totalTransform_congr hf rfl hb b)
  | succ s =>
    apply heq_of_eq
    have hf := eq_of_heq hf
    have h1 := Subscheme.divPow_totalTransform_congr hf
      (J := (Frame.canon hS z b jGen fr).jBar (s + 1))
      (J' := (Frame.canon hS z b jGen fr).jBar (s + 1)) rfl hb b
    have A : ((Frame.canon hS z b jGen fr).stageOf (s + 1 + 1)).jBar = _ := e2
    have B := ((Frame.canon hS z b jGen fr).stageOf (s + 1)).step_jBar b
      (T.monoidalTransformation (s + 1))
    refine A.trans ?_
    refine h1.trans ?_
    exact B.symm

/-- `X̂*'_{s+1}` of the frame is that of the step of the stage-`s` state. -/
theorem Frame.canon_stageOf_succ_xHatPrimeStar [Hironaka.HironakaCitedResults.{u}] (s : ℕ) :
    HEq ((Frame.canon hS z b jGen fr).stageOf (s + 1)).xHatPrimeStar
      (((Frame.canon hS z b jGen fr).stageOf s).step b
        (T.monoidalTransformation s)).xHatPrimeStar := by
  have h := Frame.canon_badLocusStar_stageOf (hS := hS) (fr := fr) s
  have A := Frame.coe_xHatPrimeStar_succ (Frame.canon hS z b jGen fr) s
  rw [h] at A
  cases s with
  | zero =>
    apply heq_of_eq
    exact A
  | succ s =>
    apply heq_of_eq
    exact A

/-- The boundary components `E_j(s+1)` are the strict transforms of the `E_j(s)` and the exceptional
divisor. -/
theorem Frame.canon_stageOf_succ_boundary [Hironaka.HironakaCitedResults.{u}] (s : ℕ) :
    ((Frame.canon hS z b jGen fr).stageOf (s + 1)).boundary =
      (((Frame.canon hS z b jGen fr).stageOf s).step b (T.monoidalTransformation s)).boundary := by
  show List.ofFn (T.Esys P.E (s + 1)) =
    (List.ofFn (T.Esys P.E s)).map (Subscheme.strictTransform (T.monoidalTransformation s)) ++
      [(T.monoidalTransformation s).exceptional]
  rw [List.ofFn_succ' (fun i : Fin (P.α + (s + 1)) => T.Esys P.E (s + 1) i)]
  simp only [Tower.esys_succ_castSucc, List.concat_eq_append, List.map_ofFn]
  exact congrArg₂ _ rfl (congrArg (fun x => [x]) (Tower.esys_succ_last P.E s))

/-- The one-step recursion of the stages of a frame over the canonical completion:
`stageOf (s + 1) = (stageOf s).step`. -/
theorem Frame.canon_stageOf_succ [Hironaka.HironakaCitedResults.{u}] (s : ℕ) :
    (Frame.canon hS z b jGen fr).stageOf (s + 1) =
      ((Frame.canon hS z b jGen fr).stageOf s).step b (T.monoidalTransformation s) :=
  StageState.ext_of_heq (Frame.canon_stageOf_succ_xHat s) (Frame.canon_stageOf_succ_c s)
    (Frame.canon_stageOf_succ_xBar s) (Frame.canon_stageOf_succ_jBar s)
    (Frame.canon_stageOf_succ_xHatPrimeStar s) (Frame.canon_stageOf_succ_boundary s)

/-- The stage-`s` state of a frame over the canonical completion is the fold of the initial
segment `T.pre s` over the initial state. -/
theorem Frame.canon_stageOf_eq_fold [Hironaka.HironakaCitedResults.{u}] (s : ℕ) :
    (Frame.canon hS z b jGen fr).stageOf s =
      StageState.fold b (T.pre s) (StageState.initial P.E (hS.ambient.2.1 x₀) z jGen) := by
  induction s with
  | zero => exact Frame.canon_stageOf_zero
  | succ s ih =>
    rw [Frame.canon_stageOf_succ, ih]
    exact (StageState.fold_snoc b (T.pre s) (T.monoidalTransformation s) _).symm

/-- Locality: the stage-`n` state depends only on the finite succession `T.pre n` (and on the
tower-independent data `z, b, jGen`). -/
theorem Frame.canon_stageOf_eq_fold_of_pre_eq [Hironaka.HironakaCitedResults.{u}] {Y : Scheme.{u}} (g : MonoidalSuccession X Y)
    (n : ℕ) (h : T.X n = Y) (hpre : h ▸ T.pre n = g) :
    h ▸ (Frame.canon hS z b jGen fr).stageOf n =
      StageState.fold b g (StageState.initial P.E (hS.ambient.2.1 x₀) z jGen) := by
  subst h
  subst hpre
  exact Frame.canon_stageOf_eq_fold n

end Bridge

section Locality

variable {N n : ℕ} {X : Scheme.{u}} {ℜ : DatumI.Raw X} {P : DatumI.Presentation ℜ}
  {r : Restriction X} {x₀ : X} {T T' : Tower X} {hS : Standing N n ℜ P r T x₀}
  {hS' : Standing N n ℜ P r T' x₀}
  [IsRegularLocalRing (Shat X x₀)] {z : Shat X x₀} {b : ℕ} {jGen : Set (Shat X x₀)}
  {fr : FrameSpec x₀ (hS.ambient.2.1 x₀) ℜ r z b jGen}
  {fr' : FrameSpec x₀ (hS'.ambient.2.1 x₀) ℜ r z b jGen}

/-- Two towers with the same initial segment (and canonical frames with the same data) have the
same stage-`m` state. -/
theorem Frame.canon_stageOf_locality [Hironaka.HironakaCitedResults.{u}] (m : ℕ) (h : T.X m = T'.X m)
    (hpre : h ▸ T.pre m = T'.pre m) :
    h ▸ (Frame.canon hS z b jGen fr).stageOf m = (Frame.canon hS' z b jGen fr').stageOf m := by
  rw [Frame.canon_stageOf_eq_fold_of_pre_eq (T'.pre m) m h hpre, Frame.canon_stageOf_eq_fold m]

end Locality

section Extension

variable {N n : ℕ} {X : Scheme.{u}} {ℜ : DatumI.Raw X} {P : DatumI.Presentation ℜ}
  {r : Restriction X} {x₀ : X}
  [IsRegularLocalRing (Shat X x₀)] {z : Shat X x₀} {b : ℕ} {jGen : Set (Shat X x₀)}

variable {T T' : Tower X}

/-- **Extension of a succession.**  Let `T` and `T'` be towers (with canonical frames of the same
data `z, b, jGen`) such that the initial segment `T.pre m` is a succession `g` and `T'.pre k` is
an extension `g ++ h`.  Then the stage-`k` state of the second frame is obtained from the stage-`m`
state of the first one by folding `h`.  This is the statement behind p. 310, "by replacing the
original succession `g_s : X_s → X` by one that includes the above succession, …": the objects
of the construction at the stage `s` (hence `X̃` and `ℜ^{N-1}_II`) are kept, and the later stages
are computed from them. -/
theorem Frame.canon_stageOf_eq_fold_of_extension [Hironaka.HironakaCitedResults.{u}] (hS : Standing N n ℜ P r T x₀)
    (hS' : Standing N n ℜ P r T' x₀) (fr : FrameSpec x₀ (hS.ambient.2.1 x₀) ℜ r z b jGen)
    {Y Z : Scheme.{u}} (g : MonoidalSuccession X Y) (h : MonoidalSuccession Y Z) (m k : ℕ)
    (hm : T.X m = Y) (hk : T'.X k = Z) (hpre : hm ▸ T.pre m = g)
    (hpre' : hk ▸ T'.pre k = g.append h) :
    hk ▸ (Frame.canon hS' z b jGen fr).stageOf k =
      StageState.fold b h (hm ▸ (Frame.canon hS z b jGen fr).stageOf m) := by
  rw [Frame.canon_stageOf_eq_fold_of_pre_eq (g.append h) k hk hpre',
    Frame.canon_stageOf_eq_fold_of_pre_eq g m hm hpre, StageState.fold_append]

/-- The set `X̂*'` of a state obtained by folding the initial segment `T.pre m` of a tower over the
initial state is open (it is the set `X̂*'_m` of the frame). -/
theorem Frame.isOpen_xHatPrimeStar_fold_initial [Hironaka.HironakaCitedResults.{u}] (hS : Standing N n ℜ P r T x₀)
    (fr : FrameSpec x₀ (hS.ambient.2.1 x₀) ℜ r z b jGen) {Y : Scheme.{u}}
    (g : MonoidalSuccession X Y) (m : ℕ) (hm : T.X m = Y) (hpre : hm ▸ T.pre m = g) :
    IsOpen (StageState.fold b g
      (StageState.initial P.E (hS.ambient.2.1 x₀) z jGen)).xHatPrimeStar := by
  subst hm
  subst hpre
  rw [← Frame.canon_stageOf_eq_fold (hS := hS) (fr := fr) m]
  exact Frame.isOpen_stageOf_xHatPrimeStar _ m

end Extension

/-! ### The datum `ℜ^{N-1}_II` of p. 308, read off a state -/

section StateDatum

variable {Y : Scheme.{u}} (σ : StageState Y)

/-- `Ū_s = ι_s⁻¹(X̂*'_s) = X̂*'_s ∩ X̄_s`, an open subscheme of `X̄_s` (p. 308, once `X̂*'_s` is
known to be open). -/
noncomputable def StageState.uBar (hU : IsOpen σ.xHatPrimeStar) : σ.xBar.toScheme.Opens :=
  σ.xBar.ι ⁻¹ᵁ ⟨σ.xHatPrimeStar, hU⟩

/-- `X̃ = Ū_s = X̂*'_s ∩ X̄_s` (p. 308). -/
abbrev StageState.xTilde (hU : IsOpen σ.xHatPrimeStar) : Scheme.{u} :=
  (σ.uBar hU : Scheme.{u})

/-- The morphism `c̃ : X̃ → X_s` induced by `c_s` (p. 308). -/
noncomputable def StageState.cTilde (hU : IsOpen σ.xHatPrimeStar) : σ.xTilde hU ⟶ Y :=
  (σ.uBar hU).ι ≫ σ.xBar.ι ≫ σ.c

/-- `J̄(s)` as a sheaf of ideals on `X̃`. -/
noncomputable def StageState.jBarT (hU : IsOpen σ.xHatPrimeStar) : Subscheme (σ.xTilde hU) :=
  Subscheme.totalTransform (σ.uBar hU).ι σ.jBar

/-- `Ẽ_i`: the trace on `X̃` of `c⁻¹` of the `i`th boundary component `E_i(s)` (indices from `0`;
the empty subscheme if there is no such component). -/
noncomputable def StageState.eTildeAt (hU : IsOpen σ.xHatPrimeStar) (i : ℕ) :
    Subscheme (σ.xTilde hU) :=
  Subscheme.totalTransform (σ.uBar hU).ι (Subscheme.totalTransform σ.xBar.ι
    (Subscheme.totalTransform σ.c (σ.boundary.getD i Subscheme.empty)))

/-- The datum `ℜ^{N-1}_II = (Ẽ_1, …, Ẽ_α̃ | J̃, b | a_1, …, a_α̃)` of p. 308, read off the state:
`Ẽ_j` is the trace on `X̃` of `c⁻¹` of the boundary component `E_{α₀+j}(s)`, for
`1 ≤ j ≤ α̃`, where `α̃ = αT` (`α₀ = 0`, `αT = α + s` in the closed case; `α₀ = α`, `αT = s` in
the open case). -/
noncomputable def StageState.datumII (hU : IsOpen σ.xHatPrimeStar) (b α₀ αT : ℕ)
    (a : Fin αT → ℕ) (Jt : Subscheme (σ.xTilde hU)) : DatumII.Raw (σ.xTilde hU) where
  α := αT
  E := fun j => σ.eTildeAt hU (α₀ + j)
  a := a
  J := Jt
  b := b

end StateDatum

/-! ### The readers of a frame's state are those of its removal family -/

section Readers

variable {N n : ℕ} {X : Scheme.{u}} {ℜ : DatumI.Raw X} {P : DatumI.Presentation ℜ}
  {r : Restriction X} {T : Tower X} {x₀ : X} {hS : Standing N n ℜ P r T x₀} (𝒮 : Frame hS)

/-- The offset `α₀` of the boundary components that enter the `Ẽ_j` (Remark 2, p. 308): `0` in
the closed case (`Ẽ_j` for `1 ≤ j ≤ α + s`), `α` in the open case (`Ẽ_j = Ê'_{α+j}(s) ∩ X̄'_s`
for `1 ≤ j ≤ s`). -/
def Frame.eTildeOffset : ℕ :=
  match r with
  | .closed _ => 0
  | .opn _ => P.α

/-- The `j`th `Ẽ_j` (as a subscheme of `X̄_s`) is the trace of `c_s⁻¹` of the boundary component
of the tower with index `α₀ + j`. -/
theorem Frame.exists_eTilde_snd_eq (s : ℕ) (j : Fin (𝒮.eTilde s).1) :
    ∃ i : Fin (P.α + s), (i : ℕ) = 𝒮.eTildeOffset + j ∧
      (𝒮.eTilde s).2 j = Subscheme.totalTransform (𝒮.xBar s).ι
        (Subscheme.totalTransform (𝒮.c s) (T.Esys P.E s i)) := by
  cases r with
  | closed F => exact ⟨j, by simp [Frame.eTildeOffset], rfl⟩
  | opn U => exact ⟨Fin.natAdd P.α j, rfl, rfl⟩

/-- The boundary list of the state of a frame lists the `E_j(s)` of the tower. -/
theorem Frame.getD_boundary_stageOf [Hironaka.HironakaCitedResults.{u}] (s : ℕ) (i : Fin (P.α + s)) :
    (𝒮.stageOf s).boundary.getD i Subscheme.empty = T.Esys P.E s i := by
  show (List.ofFn (T.Esys P.E s)).getD i _ = _
  rw [List.getD_eq_getElem _ _ (by simp)]
  simp

/-- `X̃` of the state of a frame is `X̃ = Ū_s` of its removal family `removalFamilyStar`. -/
theorem Frame.stageOf_xTilde_eq [Hironaka.HironakaCitedResults.{u}] (s : ℕ) :
    (𝒮.stageOf s).xTilde (𝒮.isOpen_stageOf_xHatPrimeStar s) = 𝒮.removalFamilyStar.xTilde s :=
  rfl

/-- The datum `ℜ^{N-1}_II` of p. 308 read off the state of the frame is that of its removal
family `removalFamilyStar`. -/
theorem Frame.stageOf_datumII_eq [Hironaka.HironakaCitedResults.{u}] (s : ℕ) (a : Fin (𝒮.eTilde s).1 → ℕ)
    (Jt : Subscheme (𝒮.removalFamilyStar.xTilde s)) :
    (𝒮.stageOf s).datumII (𝒮.isOpen_stageOf_xHatPrimeStar s) 𝒮.b 𝒮.eTildeOffset
      (𝒮.eTilde s).1 a Jt = 𝒮.removalFamilyStar.datumII s a Jt := by
  have hE : ∀ j : Fin (𝒮.eTilde s).1,
      ((𝒮.stageOf s).datumII (𝒮.isOpen_stageOf_xHatPrimeStar s) 𝒮.b 𝒮.eTildeOffset
        (𝒮.eTilde s).1 a Jt).E j = (𝒮.removalFamilyStar.datumII s a Jt).E j := by
    intro j
    obtain ⟨i, hi, he⟩ := 𝒮.exists_eTilde_snd_eq s j
    have hb := 𝒮.getD_boundary_stageOf s i
    rw [hi] at hb
    have h1 : ((𝒮.stageOf s).datumII (𝒮.isOpen_stageOf_xHatPrimeStar s) 𝒮.b 𝒮.eTildeOffset
        (𝒮.eTilde s).1 a Jt).E j = Subscheme.totalTransform
          ((𝒮.stageOf s).uBar (𝒮.isOpen_stageOf_xHatPrimeStar s)).ι
          (Subscheme.totalTransform (𝒮.xBar s).ι (Subscheme.totalTransform (𝒮.c s)
            ((𝒮.stageOf s).boundary.getD (𝒮.eTildeOffset + j) Subscheme.empty))) := rfl
    have h2 : (𝒮.removalFamilyStar.datumII s a Jt).E j =
        Subscheme.totalTransform (𝒮.removalFamilyStar.uBar s).ι ((𝒮.eTilde s).2 j) := rfl
    rw [h1, h2, he, hb]
    rfl
  have hfun : (fun j : Fin (𝒮.eTilde s).1 => ((𝒮.stageOf s).datumII
      (𝒮.isOpen_stageOf_xHatPrimeStar s) 𝒮.b 𝒮.eTildeOffset (𝒮.eTilde s).1 a Jt).E j) =
      fun j => (𝒮.removalFamilyStar.datumII s a Jt).E j := funext hE
  exact congrArg (fun E => ({ α := (𝒮.eTilde s).1, E := E, a := a, J := Jt, b := 𝒮.b } :
    DatumII.Raw (𝒮.removalFamilyStar.xTilde s))) hfun

end Readers

/-! ### The trivial step -/

section TrivialStep

variable {Y : Scheme.{u}} (σ : StageState Y)

/-- `Bad ⊆ B̂`. -/
theorem StageState.badLocus_subset_pts (b : ℕ) (B : Subscheme Y) :
    σ.badLocus b B ⊆ (σ.bHat B).pts := by
  intro x hx
  simp only [StageState.badLocus, Set.mem_iUnion] at hx
  obtain ⟨K, ⟨hK, -⟩, hxK⟩ := hx
  exact Subscheme.pts_subset_of_mem_irreducibleComponents hK hxK

/-- A point of `X̄` lies in `B̄ = ι⁻¹(c⁻¹(B))` iff its image in `Y` lies in `B`. -/
theorem StageState.mem_pts_bBarOn_iff (B : Subscheme Y) (x : σ.xBar.toScheme) :
    x ∈ (σ.bBarOn B).pts ↔ σ.c.base (σ.xBar.ι.base x) ∈ B.pts := by
  unfold StageState.bBarOn StageState.bHat
  rw [Subscheme.pts_totalTransform_eq_preimage, Subscheme.pts_totalTransform_eq_preimage]
  rfl

/-- The core of the trivial step: if the center misses the image of `Ū = X̂*' ∩ X̄` in `Y`, then `f̄
: X̄_{s+1} → X̄_s` is an isomorphism over `Ū`, and `Ū_{s+1} = f̄⁻¹(Ū_s)`. -/
theorem StageState.exists_iso_uBar_step_of_forall_notMem [Hironaka.HironakaCitedResults.{u}] (b : ℕ) {B : Subscheme Y}
    (t : MonoidalTransformation Y B) (hU : IsOpen σ.xHatPrimeStar)
    (hU' : IsOpen (σ.step b t).xHatPrimeStar)
    (hdisj : ∀ x ∈ σ.uBar hU, σ.c.base (σ.xBar.ι.base x) ∉ B.pts) :
    ∃ e : (σ.step b t).xTilde hU' ≅ σ.xTilde hU,
      e.hom ≫ (σ.uBar hU).ι =
        ((σ.step b t).uBar hU').ι ≫ σ.fBar b t := by
  have hΩ : ∀ x ∈ σ.uBar hU, x ∉ (σ.bBarOn B).pts := fun x hx hxB =>
    hdisj x hx ((σ.mem_pts_bBarOn_iff B x).mp hxB)
  have hmono := (t.baseChange σ.c).isMonoidalTransformationOf_strictTransformMap σ.xBar
  have hiso : IsIso ((σ.fBar b t) ∣_ σ.uBar hU) :=
    hmono.isIso_morphismRestrict_of_forall_notMem _ hΩ
  have hcomm := (t.baseChange σ.c).strictTransformMap_ι σ.xBar
  have hopen : (σ.step b t).uBar hU' =
      (σ.fBar b t) ⁻¹ᵁ σ.uBar hU := by
    refine TopologicalSpace.Opens.ext (Set.ext fun x => ?_)
    have hx' : σ.xBar.ι.base ((σ.fBar b t).base x) =
        (pullback.snd t.f σ.c).base ((σ.step b t).xBar.ι.base x) :=
      congrArg (fun g => g.base x) hcomm
    constructor
    · intro hx
      show σ.xBar.ι.base ((σ.fBar b t).base x) ∈
        σ.xHatPrimeStar
      rw [hx']
      exact hx.1
    · intro hx
      have hx1 : σ.xBar.ι.base ((σ.fBar b t).base x) ∈
          σ.xHatPrimeStar := hx
      rw [hx'] at hx1
      refine ⟨hx1, fun hbad => ?_⟩
      have := σ.badLocus_subset_pts b B hbad
      rw [← hx'] at this
      have hmem : (σ.fBar b t).base x ∈
          (σ.bBarOn B).pts := by
        unfold StageState.bBarOn
        rw [Subscheme.pts_totalTransform_eq_preimage]
        exact this
      exact hΩ _ hx hmem
  let e₁ : (σ.step b t).xTilde hU' ≅
      ((σ.fBar b t) ⁻¹ᵁ σ.uBar hU : Scheme.{u}) :=
    Scheme.isoOfEq _ hopen
  let e₂ : ((σ.fBar b t) ⁻¹ᵁ σ.uBar hU : Scheme.{u}) ≅
      (σ.uBar hU : Scheme.{u}) := @asIso _ _ _ _ _ hiso
  refine ⟨e₁ ≪≫ e₂, ?_⟩
  have h1 : e₁.hom ≫ ((σ.fBar b t) ⁻¹ᵁ σ.uBar hU).ι =
      ((σ.step b t).uBar hU').ι := Scheme.isoOfEq_hom_ι _ hopen
  have h2 := morphismRestrict_ι (σ.fBar b t) (σ.uBar hU)
  exact (Category.assoc _ _ _).trans ((congrArg (fun g => e₁.hom ≫ g) h2).trans
    ((Category.assoc _ _ _).symm.trans
      (congrArg (fun g => g ≫ σ.fBar b t) h1)))

variable {σ}

/-- A morphism `f : X̃_{s+1} → X̃_s` over `f̄_s` is compatible with `c̃`. -/
theorem StageState.comp_cTilde_step_eq (b : ℕ) {B : Subscheme Y}
    (t : MonoidalTransformation Y B) (hU : IsOpen σ.xHatPrimeStar)
    (hU' : IsOpen (σ.step b t).xHatPrimeStar) (f : (σ.step b t).xTilde hU' ⟶ σ.xTilde hU)
    (hf : f ≫ (σ.uBar hU).ι = ((σ.step b t).uBar hU').ι ≫ σ.fBar b t) :
    f ≫ σ.cTilde hU = (σ.step b t).cTilde hU' ≫ t.f := by
  have hcomm := σ.fBar_comp_ι b t
  have hcond := pullback.condition (f := t.f) (g := σ.c)
  show f ≫ (σ.uBar hU).ι ≫ σ.xBar.ι ≫ σ.c =
    (((σ.step b t).uBar hU').ι ≫ (σ.step b t).xBar.ι ≫ pullback.fst t.f σ.c) ≫ t.f
  rw [← Category.assoc f, hf, Category.assoc, ← Category.assoc _ σ.xBar.ι, hcomm]
  have h3 : ((σ.step b t).xBar.ι ≫ pullback.snd t.f σ.c) ≫ σ.c =
      ((σ.step b t).xBar.ι ≫ pullback.fst t.f σ.c) ≫ t.f := by
    rw [Category.assoc, Category.assoc, hcond]
  exact congrArg (fun g => ((σ.step b t).uBar hU').ι ≫ g) h3

/-- The pull-back to an open subscheme `Ω` of a subscheme `D` that misses `Ω` is empty. -/
theorem _root_.Hironaka.Subscheme.totalTransform_ι_eq_empty_of_forall_notMem {Z : Scheme.{u}}
    (Ω : Z.Opens)
    (D : Subscheme Z) (h : ∀ z ∈ Ω, z ∉ D.pts) :
    Subscheme.totalTransform Ω.ι D = Subscheme.empty := by
  refine Subscheme.eq_empty_of_pts_eq_empty ?_
  rw [FlatPreimm.pts_totalTransform]
  exact Set.eq_empty_of_forall_notMem fun z hz => h z.val z.property hz

/-- `Ẽ_i` is the pull-back of the `i`th boundary component along `c̃`. -/
theorem StageState.eTildeAt_eq_totalTransform_cTilde (hU : IsOpen σ.xHatPrimeStar) (i : ℕ) :
    σ.eTildeAt hU i =
      Subscheme.totalTransform (σ.cTilde hU) (σ.boundary.getD i Subscheme.empty) := by
  unfold StageState.eTildeAt StageState.cTilde
  rw [Subscheme.totalTransform_comp, Subscheme.totalTransform_comp]

/-- The isomorphism of the trivial step carries `J̄(s)` on `X̃_s` to `J̄(s+1)` on `X̃_{s+1}` (the
division by `B̄^b` is trivial, as `B̄` misses `X̃_s`). -/
theorem StageState.totalTransform_jBarT_step [Hironaka.HironakaCitedResults.{u}] (b : ℕ) {B : Subscheme Y}
    (t : MonoidalTransformation Y B) (hU : IsOpen σ.xHatPrimeStar)
    (hU' : IsOpen (σ.step b t).xHatPrimeStar)
    (hdisj : ∀ x ∈ σ.uBar hU, σ.c.base (σ.xBar.ι.base x) ∉ B.pts)
    (e : (σ.step b t).xTilde hU' ≅ σ.xTilde hU)
    (he : e.hom ≫ (σ.uBar hU).ι = ((σ.step b t).uBar hU').ι ≫ σ.fBar b t) :
    Subscheme.totalTransform e.hom (σ.jBarT hU) = (σ.step b t).jBarT hU' := by
  have hmono := (t.baseChange σ.c).isMonoidalTransformationOf_strictTransformMap σ.xBar
  have hP : (Subscheme.totalTransform (σ.fBar b t) (σ.bBarOn B)).IsInvertibleIdeal := hmono.1
  have hΩ : ∀ x ∈ σ.uBar hU, x ∉ (σ.bBarOn B).pts := fun x hx hxB =>
    hdisj x hx ((σ.mem_pts_bBarOn_iff B x).mp hxB)
  have hPe : Subscheme.totalTransform ((σ.step b t).uBar hU').ι
      (Subscheme.totalTransform (σ.fBar b t) (σ.bBarOn B)) = Subscheme.empty := by
    rw [← Subscheme.totalTransform_comp, ← he, Subscheme.totalTransform_comp,
      Subscheme.totalTransform_ι_eq_empty_of_forall_notMem _ _ hΩ, Subscheme.totalTransform_empty]
  have h1 : (σ.step b t).jBarT hU' = Subscheme.totalTransform ((σ.step b t).uBar hU').ι
      (Subscheme.divPow (Subscheme.totalTransform (σ.fBar b t) σ.jBar)
        (Subscheme.totalTransform (σ.fBar b t) (σ.bBarOn B)) b) := rfl
  rw [h1, Subscheme.totalTransform_divPow _ _ _ hP, hPe, Subscheme.divPow_empty,
    ← Subscheme.totalTransform_comp, StageState.jBarT, ← Subscheme.totalTransform_comp, he]

/-- Off the exceptional divisor, the strict and the total transform of a subscheme agree: their
pull-backs along a morphism missing the exceptional divisor are equal. -/
theorem _root_.Hironaka.Subscheme.totalTransform_strictTransform_eq_of_forall_notMem
    {Z W : Scheme.{u}}
    {B : Subscheme Z} (t : MonoidalTransformation Z B) (D : Subscheme Z) (g : W ⟶ t.X')
    (hg : ∀ w, g.base w ∉ t.exceptional.pts) :
    Subscheme.totalTransform g (Subscheme.strictTransform t D) =
      Subscheme.totalTransform g (Subscheme.totalTransform t.f D) := by
  refine Subscheme.ext_stalkIdeal fun w => ?_
  rw [Hironaka.stalkIdeal_totalTransform, Hironaka.stalkIdeal_totalTransform,
    MonoidalTransformation.strictTransform_stalkIdeal_of_notMem t D (hg w)]

/-- The isomorphism of the trivial step carries `Ẽ_i(s)` to `Ẽ_i(s+1)`, for every `i`. -/
theorem StageState.totalTransform_eTildeAt_step (b : ℕ) {B : Subscheme Y}
    (t : MonoidalTransformation Y B) (hU : IsOpen σ.xHatPrimeStar)
    (hU' : IsOpen (σ.step b t).xHatPrimeStar)
    (hdisj : ∀ x ∈ σ.uBar hU, σ.c.base (σ.xBar.ι.base x) ∉ B.pts)
    (e : (σ.step b t).xTilde hU' ≅ σ.xTilde hU)
    (he : e.hom ≫ (σ.uBar hU).ι = ((σ.step b t).uBar hU').ι ≫ σ.fBar b t) (i : ℕ) :
    Subscheme.totalTransform e.hom (σ.eTildeAt hU i) = (σ.step b t).eTildeAt hU' i := by
  have hc := σ.comp_cTilde_step_eq b t hU hU' e.hom he
  have hg : ∀ w : (σ.step b t).xTilde hU',
      ((σ.step b t).cTilde hU').base w ∉ t.exceptional.pts := by
    intro w hw
    rw [MonoidalTransformation.pts_exceptional] at hw
    have h1 := congrArg (fun g => g.base w) hc
    have h2 : t.f.base (((σ.step b t).cTilde hU').base w) =
        σ.c.base (σ.xBar.ι.base ((σ.uBar hU).ι.base (e.hom.base w))) := h1.symm
    exact hdisj _ (e.hom.base w).2 (h2 ▸ hw)
  rw [StageState.eTildeAt_eq_totalTransform_cTilde, StageState.eTildeAt_eq_totalTransform_cTilde,
    ← Subscheme.totalTransform_comp, hc, Subscheme.totalTransform_comp]
  by_cases hi : i < σ.boundary.length
  · have : (σ.step b t).boundary.getD i Subscheme.empty =
        Subscheme.strictTransform t (σ.boundary.getD i Subscheme.empty) := by
      show (σ.boundary.map (Subscheme.strictTransform t) ++ [t.exceptional]).getD i _ = _
      rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
        List.getElem?_append_left (by simpa using hi), List.getElem?_map,
        List.getElem?_eq_getElem hi]
      rfl
    rw [this]
    exact (Subscheme.totalTransform_strictTransform_eq_of_forall_notMem t _ _ hg).symm
  · have hL : σ.boundary.getD i Subscheme.empty = Subscheme.empty :=
      List.getD_eq_default _ _ (not_lt.mp hi)
    rw [hL, Subscheme.totalTransform_empty, Subscheme.totalTransform_empty]
    rcases Nat.eq_or_lt_of_le (not_lt.mp hi) with h | h
    · have hR : (σ.step b t).boundary.getD i Subscheme.empty = t.exceptional := by
        show (σ.boundary.map (Subscheme.strictTransform t) ++ [t.exceptional]).getD i _ = _
        rw [List.getD_append_right _ _ _ _ (by simpa using h.le)]
        simp [← h]
      rw [hR]
      symm
      refine Subscheme.eq_empty_of_pts_eq_empty ?_
      rw [Subscheme.pts_totalTransform_eq_preimage]
      exact Set.eq_empty_of_forall_notMem fun w hw => hg w hw
    · have hR : (σ.step b t).boundary.getD i Subscheme.empty = Subscheme.empty :=
        List.getD_eq_default _ _ (by
          show (σ.boundary.map (Subscheme.strictTransform t) ++ [t.exceptional]).length ≤ i
          simpa using h)
      rw [hR, Subscheme.totalTransform_empty]

/-- **The trivial step** (p. 310: "These monoidal transformations are successively permissible
for ℜ(s) and induce trivial monoidal transformations of X̃ by Remarks 4 and 5").  If the center
`B` of `t : X_{s+1} → X_s` misses `c̃(X̃)`, the step `σ.step b t` induces an isomorphism
`e : X̃_{s+1} ≅ X̃_s` over `t` (`c̃_{s+1}` and `c̃_s` correspond), which carries `J̄(s)` to
`J̄(s+1)`
and each `Ẽ_i(s)` to `Ẽ_i(s+1)`; the new component `Ẽ_{α+s+1}(s+1)` (the exceptional divisor)
is empty.  Both `X̂*'_s` and `X̂*'_{s+1}` are assumed open (for the states of frames this is
`Frame.isOpen_stageOf_xHatPrimeStar`).

Deviation from the paper (gap filled): the paper says only "by Remarks 4 and 5".  This lemma is
the second half of that sentence: given that the center misses `c̃(X̃)` (the hypothesis `hdisj`,
which the caller must derive from Remarks 4 and 5), the triviality on `X̃` is proved as follows:
`f̄_s` is a monoidal transformation of `X̄_s` with center `B̄_s`, hence an isomorphism over the
open set `Ū_s` missing `B̄_s`. -/
@[blueprint "lem:IV.3-trivial-step"
  (statement := /-- Let $\sigma$ be the state of the construction at the stage $s$ (the objects
    $\hat X_s$, $\bar X_s$, $\bar J(s)$, $\hat X'^*_s$ and $E_1(s),\dots,E_{\alpha+s}(s)$ of
    \S3, with $\tilde X=\hat X'^*_s\cap\bar X_s$ open in $\bar X_s$), and let
    $f\colon X_{s+1}\to X_s$ be a monoidal transformation with center $B$ such that
    $B\cap c_s(\tilde X)=\emptyset$. Then, if $\hat X'^*_{s+1}$ is open, the morphism
    $\bar f_s$ induces an isomorphism $\varphi\colon\tilde X_{s+1}\to\tilde X_s$ such that
    $\tilde c_s\circ\varphi=f\circ\tilde c_{s+1}$, $\varphi^{-1}(\bar J(s))=\bar J(s+1)$,
    $\varphi^{-1}(\tilde E_i(s))=\tilde E_i(s+1)$ for all $i$ (the strict transforms of the
    $E_i(s)$), and the new component $\tilde E_{\alpha+s+1}(s+1)$, the trace of the exceptional
    divisor, is empty. This is the content of the sentence ``These monoidal transformations are
    successively permissible for $\mathfrak R(s)$ and induce trivial monoidal transformations of
    $\tilde X$ by Remarks 4 and 5'' (p.~310), once the centers are known to miss
    $c_s(\tilde X)$.

    \textbf{Deviation from the paper (gap filled).} The paper derives the triviality from
    Remarks 4 and 5 without argument; Lean proves that a monoidal transformation whose center
    misses $\tilde c(\tilde X)$ induces an isomorphism of $\tilde X$ carrying $\bar J$ and the
    $\tilde E_j$ along. That the centers miss $\tilde c(\tilde X)$ is supplied by the caller from
    Remarks 4 and 5. (Formalization note: the statement is made for the abstract state
    \texttt{StageState}, so that it applies to the stages of any extension of the succession
    $g_s$, \cref{rem:IV.3-4}, \cref{rem:IV.3-5}.) -/)
  (proof := /-- The morphism $\bar f_s\colon\bar X_{s+1}\to\bar X_s$ induced on the strict
    transform is a monoidal transformation of $\bar X_s$ with center $\bar B_s=\bar X_s\cap
    c_s^{-1}(B)$ (it is the strict transform of $\bar X_s$ under the base change of $f$ along
    $c_s$, \cref{compat:blowup-flat-base-change}). By the universal property, a monoidal
    transformation is an isomorphism over any open set missing its center; the open set
    $\bar U_s=\tilde X$ misses $\bar B_s$ by the assumption. Since $\mathrm{Bad}_s\subseteq
    \hat B_s$ and $\hat B_s\cap\tilde X=\emptyset$, $\tilde X_{s+1}=\bar f_s^{-1}(\tilde X_s)$,
    so $\bar f_s$ restricts to an isomorphism $\tilde X_{s+1}\to\tilde X_s$. The ideal
    $\bar J(s+1)=\bar f_s^{-1}(\bar J(s))\cdot\bar f_s^{-1}(\bar B_s)^{-b}$ pulls back
    on $\tilde X_{s+1}$ to $\bar f_s^{-1}(\bar J(s))$ because $\bar f_s^{-1}(\bar B_s)$ is
    the unit ideal there; and off the exceptional divisor the strict transform of $E_i(s)$
    equals its total transform.
    \textbf{Deviation from the paper (gap filled).} See the statement. -/)
  (proofUses := ["rem:IV.3-4", "rem:IV.3-5", "compat:blowup-flat-base-change"])
  (latexEnv := "lemma")]
theorem StageState.exists_iso_xTilde_step_of_forall_notMem [Hironaka.HironakaCitedResults.{u}] (b : ℕ) {B : Subscheme Y}
    (t : MonoidalTransformation Y B) (hU : IsOpen σ.xHatPrimeStar)
    (hU' : IsOpen (σ.step b t).xHatPrimeStar)
    (hdisj : ∀ xt : σ.xTilde hU, (σ.cTilde hU).base xt ∉ B.pts) :
    ∃ e : (σ.step b t).xTilde hU' ≅ σ.xTilde hU,
      e.hom ≫ σ.cTilde hU = (σ.step b t).cTilde hU' ≫ t.f ∧
      Subscheme.totalTransform e.hom (σ.jBarT hU) = (σ.step b t).jBarT hU' ∧
      (∀ i, Subscheme.totalTransform e.hom (σ.eTildeAt hU i) = (σ.step b t).eTildeAt hU' i) ∧
      (σ.step b t).eTildeAt hU' σ.boundary.length = Subscheme.empty := by
  have hd : ∀ x ∈ σ.uBar hU, σ.c.base (σ.xBar.ι.base x) ∉ B.pts := fun x hx =>
    hdisj ⟨x, hx⟩
  obtain ⟨e, he⟩ := σ.exists_iso_uBar_step_of_forall_notMem b t hU hU' hd
  have hE := σ.totalTransform_eTildeAt_step b t hU hU' hd e he
  refine ⟨e, σ.comp_cTilde_step_eq b t hU hU' e.hom he,
    σ.totalTransform_jBarT_step b t hU hU' hd e he, hE, ?_⟩
  rw [← hE σ.boundary.length, StageState.eTildeAt_eq_totalTransform_cTilde,
    List.getD_eq_default _ _ le_rfl, Subscheme.totalTransform_empty, Subscheme.totalTransform_empty]

end TrivialStep

/-! ### The blow-up step: restriction of `f̄_s` to `X̃` -/

section BlowupStep

variable {Y : Scheme.{u}} {σ : StageState Y}

/-- The step restricted to `X̃`: if `Bad` misses `Ū_s`, then `X̃_{s+1} = f̄_s⁻¹(X̃_s)` and `f̄_s`
induces a monoidal transformation `f̃ : X̃_{s+1} → X̃_s` of `X̃` whose center is
`B̂_s ∩ X̃ = c̃⁻¹(B)`. -/
theorem StageState.exists_isMonoidalTransformationOf_fTilde [Hironaka.HironakaCitedResults.{u}] (b : ℕ) {B : Subscheme Y}
    (t : MonoidalTransformation Y B) (hU : IsOpen σ.xHatPrimeStar)
    (hU' : IsOpen (σ.step b t).xHatPrimeStar)
    (hbad : ∀ x ∈ σ.uBar hU, σ.xBar.ι.base x ∉ σ.badLocus b B) :
    ∃ f : (σ.step b t).xTilde hU' ⟶ σ.xTilde hU,
      f ≫ (σ.uBar hU).ι = ((σ.step b t).uBar hU').ι ≫ σ.fBar b t ∧
      IsMonoidalTransformationOf f (Subscheme.totalTransform (σ.cTilde hU) B) := by
  have hmono := (t.baseChange σ.c).isMonoidalTransformationOf_strictTransformMap σ.xBar
  have hc : Subscheme.totalTransform (σ.cTilde hU) B = Subscheme.totalTransform (σ.uBar hU).ι
      (Subscheme.totalTransform σ.xBar.ι (Subscheme.totalTransform σ.c B)) := by
    unfold StageState.cTilde
    rw [Subscheme.totalTransform_comp, Subscheme.totalTransform_comp]
  have hres : IsMonoidalTransformationOf (σ.fBar b t ∣_ σ.uBar hU)
      (Subscheme.totalTransform (σ.cTilde hU) B) := by
    rw [hc]
    exact hmono.morphismRestrict (σ.uBar hU)
  have hopen : (σ.step b t).uBar hU' = σ.fBar b t ⁻¹ᵁ σ.uBar hU := by
    refine TopologicalSpace.Opens.ext (Set.ext fun x => ?_)
    have hx' : σ.xBar.ι.base ((σ.fBar b t).base x) =
        (pullback.snd t.f σ.c).base ((σ.step b t).xBar.ι.base x) :=
      congrArg (fun g => g.base x) (σ.fBar_comp_ι b t)
    constructor
    · intro hx
      show σ.xBar.ι.base ((σ.fBar b t).base x) ∈ σ.xHatPrimeStar
      rw [hx']
      exact hx.1
    · intro hx
      have hx1 : σ.xBar.ι.base ((σ.fBar b t).base x) ∈ σ.xHatPrimeStar := hx
      rw [hx'] at hx1
      refine ⟨hx1, fun hbd => hbad _ hx ?_⟩
      rw [hx']
      exact hbd
  let e₁ : (σ.step b t).xTilde hU' ≅ (σ.fBar b t ⁻¹ᵁ σ.uBar hU : Scheme.{u}) :=
    Scheme.isoOfEq _ hopen
  let s : MonoidalTransformation (σ.xTilde hU) (Subscheme.totalTransform (σ.cTilde hU) B) :=
    ⟨(σ.fBar b t ⁻¹ᵁ σ.uBar hU : Scheme.{u}), σ.fBar b t ∣_ σ.uBar hU, hres.1, hres.2⟩
  refine ⟨e₁.hom ≫ (σ.fBar b t ∣_ σ.uBar hU), ?_, ?_⟩
  · have h1 : e₁.hom ≫ (σ.fBar b t ⁻¹ᵁ σ.uBar hU).ι = ((σ.step b t).uBar hU').ι :=
      Scheme.isoOfEq_hom_ι _ hopen
    have h2 := morphismRestrict_ι (σ.fBar b t) (σ.uBar hU)
    exact (Category.assoc _ _ _).trans ((congrArg (fun g => e₁.hom ≫ g) h2).trans
      ((Category.assoc _ _ _).symm.trans (congrArg (fun g => g ≫ σ.fBar b t) h1)))
  · exact IsMonoidalTransformationOf.of_iso s e₁ _ rfl

end BlowupStep

/-! ### The blow-up step: the datum `ℜ^{N-1}_II` and `J̄(s+1)` -/

section BlowupStepDatum

/-- The `j`th old component of a transform is the strict transform. -/
theorem _root_.Hironaka.DatumII.Raw.transform_E_castSucc {X : Scheme.{u}} (ℜ : DatumII.Raw X)
    {B : Subscheme X} (t : MonoidalTransformation X B) (j : Fin ℜ.α) :
    (ℜ.transform t).E (Fin.castSucc j) = Subscheme.strictTransform t (ℜ.E j) := by
  simp [DatumII.Raw.transform]

/-- The new component of a transform is the exceptional divisor. -/
theorem _root_.Hironaka.DatumII.Raw.transform_E_last {X : Scheme.{u}} (ℜ : DatumII.Raw X)
    {B : Subscheme X} (t : MonoidalTransformation X B) :
    (ℜ.transform t).E (Fin.last ℜ.α) = t.exceptional := by
  simp [DatumII.Raw.transform]

/-- The old exponents of a transform are unchanged. -/
theorem _root_.Hironaka.DatumII.Raw.transform_a_castSucc {X : Scheme.{u}} (ℜ : DatumII.Raw X)
    {B : Subscheme X} (t : MonoidalTransformation X B) (j : Fin ℜ.α) :
    (ℜ.transform t).a (Fin.castSucc j) = ℜ.a j := by
  simp [DatumII.Raw.transform]

open Classical in
theorem _root_.Hironaka.DatumII.Raw.transform_a_last {X : Scheme.{u}} (ℜ : DatumII.Raw X)
    {B : Subscheme X} (t : MonoidalTransformation X B) :
    (ℜ.transform t).a (Fin.last ℜ.α) =
      (∑ i ∈ Finset.univ.filter fun i => B.IsContainedIn (ℜ.E i), ℜ.a i) + ℜ.nu.toNat - ℜ.b := by
  simp [DatumII.Raw.transform]

/-- A product over the components of a transform splits into the old components and the new one. -/
theorem _root_.Hironaka.DatumII.Raw.prod_transform {X : Scheme.{u}} (ℜ : DatumII.Raw X)
    {B : Subscheme X} (t : MonoidalTransformation X B) {M : Type*} [CommMonoid M]
    (F : Fin (ℜ.transform t).α → M) :
    ∏ i, F i = (∏ j : Fin ℜ.α, F (Fin.castSucc j)) * F (Fin.last ℜ.α) :=
  Fin.prod_univ_castSucc F

/-- The stalk of a finite product of ideal sheaves is the product of the stalks. -/
theorem _root_.Hironaka.Subscheme.stalkIdeal_finset_prod {X : Scheme.{u}} {ι : Type*}
    (s : Finset ι) (f : ι → Subscheme X) (x : X) :
    (∏ i ∈ s, f i).stalkIdeal x = ∏ i ∈ s, (f i).stalkIdeal x := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    have : (1 : Subscheme X) = ⊤ := rfl
    rw [Finset.prod_empty, Finset.prod_empty, this, Subscheme.stalkIdeal_top_eq]
    exact Ideal.one_eq_top.symm
  | insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.prod_insert hi, Subscheme.stalkIdeal_mul_eq, ih]


variable {Y : Scheme.{u}}

/-- The hypotheses on the center of a blow-up step. -/
structure StageState.BlowupHyp (σ : StageState Y) (b : ℕ) {B : Subscheme Y}
    (_t : MonoidalTransformation Y B) (hU : IsOpen σ.xHatPrimeStar)
    (Bt : Subscheme (σ.xTilde hU)) : Prop where
  nonsingular_Y : Y.IsNonsingular
  nonsingular_B : B.IsNonsingular
  irreducible_B : B.IsIrreducible
  divisor : ∀ i : Fin σ.boundary.length, (σ.boundary.get i).IsNonsingularIrreducibleCodimOne
  nc : (⨅ i : Fin σ.boundary.length, σ.boundary.get i).HasOnlyNormalCrossings
  nc_B : (⨅ i : Fin σ.boundary.length, σ.boundary.get i).HasOnlyNormalCrossingsWith B
  nonsingular_xTilde : (σ.xTilde hU).IsNonsingular
  nonsingular_Bt : Bt.IsNonsingular
  irreducible_Bt : Bt.IsIrreducible
  totalTransform_eq : Subscheme.totalTransform (σ.cTilde hU) B = Bt
  subset_closure : B.pts ⊆ closure ((σ.cTilde hU).base '' Bt.pts)
  notMem_badLocus : ∀ x ∈ σ.uBar hU, σ.xBar.ι.base x ∉ σ.badLocus b B

variable {σ : StageState Y} {b : ℕ} {B : Subscheme Y} {t : MonoidalTransformation Y B}
  {hU : IsOpen σ.xHatPrimeStar} {Bt : Subscheme (σ.xTilde hU)}

/-- `J̄(s) ⊆ P(B̄_s)^b` at the points of `Ū_s` over `B̂_s`: every component of `B̂_s` through such a
point is good, as the point is not in the bad locus (the condition [g*] of the construction). -/
theorem StageState.BlowupHyp.jBar_le (H : σ.BlowupHyp b t hU Bt) (x : σ.xBar.toScheme)
    (hx : x ∈ σ.uBar hU) (hxB : x ∈ (σ.bBarOn B).pts) :
    σ.jBar.stalkIdeal x ≤ ((σ.bBarOn B).stalkIdeal x) ^ b := by
  have hxh : σ.xBar.ι.base x ∈ (σ.bHat B).pts := by
    unfold StageState.bBarOn at hxB
    rw [Subscheme.pts_totalTransform_eq_preimage] at hxB
    exact hxB
  obtain ⟨K, hK, hxK⟩ := Subscheme.exists_mem_irreducibleComponents_of_mem_pts (σ.bHat B) hxh
  have hgood : σ.IsGoodComponent b B K := by
    by_contra hbad
    refine H.notMem_badLocus x hx ?_
    simp only [StageState.badLocus, Set.mem_iUnion]
    exact ⟨K, ⟨hK, hbad⟩, hxK⟩
  exact hgood.2 x hx hxK

/-- `B̃ ⊆ Ẽ_i` iff `B ⊆ E_i`. -/
theorem StageState.BlowupHyp.pts_subset_iff (H : σ.BlowupHyp b t hU Bt) (i : ℕ) :
    Bt.pts ⊆ (σ.eTildeAt hU i).pts ↔ B.pts ⊆ (σ.boundary.getD i Subscheme.empty).pts := by
  have hBt : Bt.pts = (σ.cTilde hU).base ⁻¹' B.pts := by
    rw [← H.totalTransform_eq, Subscheme.pts_totalTransform_eq_preimage]
  rw [StageState.eTildeAt_eq_totalTransform_cTilde, Subscheme.pts_totalTransform_eq_preimage]
  constructor
  · intro h x hx
    exact closure_minimal (Set.image_subset_iff.mpr h)
      (σ.boundary.getD i Subscheme.empty).support.isClosed (H.subset_closure hx)
  · intro h x hx
    rw [hBt] at hx
    exact h hx

/-- The boundary of a step in range. -/
theorem StageState.getD_boundary_step_of_lt (σ : StageState Y) (b : ℕ) {B : Subscheme Y}
    (t : MonoidalTransformation Y B) {i : ℕ} (hi : i < σ.boundary.length) :
    (σ.step b t).boundary.getD i Subscheme.empty =
      Subscheme.strictTransform t (σ.boundary.getD i Subscheme.empty) := by
  show (σ.boundary.map (Subscheme.strictTransform t) ++ [t.exceptional]).getD i _ = _
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
    List.getElem?_append_left (by simpa using hi), List.getElem?_map,
    List.getElem?_eq_getElem hi]
  rfl

/-- A morphism with the universal property of a monoidal transformation, as a
`MonoidalTransformation`. -/
abbrev IsMonoidalTransformationOf.toMonoidalTransformation {Z Z' : Scheme.{u}} {f : Z' ⟶ Z}
    {B : Subscheme Z} (h : IsMonoidalTransformationOf f B) : MonoidalTransformation Z B :=
  ⟨Z', f, h.1, h.2⟩

/-- Cancellation of a power of a principal ideal generated by a non-zero element of a domain. -/
theorem Ideal.eq_of_mul_pow_eq_of_eq_span {R : Type*} [CommRing R] [IsDomain R] {P I J : Ideal R}
    {g : R} (hP : P = Ideal.span {g}) (hg : g ≠ 0) {m : ℕ} (h : I * P ^ m = J * P ^ m) : I = J := by
  rw [hP, Ideal.span_singleton_pow, mul_comm I, mul_comm J] at h
  exact (Ideal.span_singleton_mul_right_inj (pow_ne_zero m hg)).mp h

open Classical DatumTransform in
/-- The total transform of a trace `Ẽ` under a blow-up of `X̃` with a permissible center `B̃` is the
product of the strict transform and the exceptional divisor to the power `m = 1` if
`B̃ ⊆ Ẽ`, `0` otherwise (the entries equal to `⊥` being handled separately).  Stalkwise. -/
theorem StageState.BlowupHyp.stalkIdeal_totalTransform_eTildeAt (H : σ.BlowupHyp b t hU Bt)
    {α₀ αT : ℕ} {a : Fin αT → ℕ} {Jt : Subscheme (σ.xTilde hU)}
    (hD : (σ.datumII hU b α₀ αT a Jt).emptyIfBot.IsWeakDatum)
    (hperm : (σ.datumII hU b α₀ αT a Jt).emptyIfBot.IsPermissible Bt)
    (T' : MonoidalTransformation (σ.xTilde hU) Bt) (j : Fin αT) (yb : T'.X')
    [IsRegularLocalRing (T'.X'.presheaf.stalk yb)] :
    (Subscheme.totalTransform T'.f (σ.eTildeAt hU (α₀ + j))).stalkIdeal yb =
      (Subscheme.strictTransform T' (σ.eTildeAt hU (α₀ + j))).stalkIdeal yb *
        (T'.exceptional.stalkIdeal yb) ^
          (if Bt.pts ⊆ (σ.eTildeAt hU (α₀ + j)).pts then 1 else 0) := by
  classical
  by_cases hbot : σ.eTildeAt hU (α₀ + j) = ⊥
  · rw [hbot, Subscheme.stalkIdeal_totalTransform_bot,
      MonoidalTransformation.strictTransform_bot, Subscheme.stalkIdeal_bot_eq, Ideal.bot_mul]
  · have hE : (σ.datumII hU b α₀ αT a Jt).emptyIfBot.E j = σ.eTildeAt hU (α₀ + j) :=
      Subscheme.emptyIfBot_of_ne_bot hbot
    have key :=
      stalkIdeal_totalTransform_eq_strict_mul_exceptional_pow_of_pts_subset_of_isNonsingularDivisor
      (B := Bt) (σ.datumII hU b α₀ αT a Jt).emptyIfBot.E H.nonsingular_xTilde hD.2.1 hD.2.2.1
      hperm.2.2 H.irreducible_Bt H.nonsingular_Bt T' j yb
    rw [hE] at key
    exact key

open Classical in
/-- **Strict transforms commute with `c̃`** (p. 324/310): the trace on `X̃_{s+1}` of the strict
transform of `E_{α₀+j}(s)` is the strict transform by `f̃` of the trace `Ẽ_{α₀+j}` on `X̃_s`. -/
theorem StageState.BlowupHyp.eTildeAt_step_eq_strictTransform (H : σ.BlowupHyp b t hU Bt)
    {α₀ αT : ℕ} {a : Fin αT → ℕ} {Jt : Subscheme (σ.xTilde hU)}
    (hlen : σ.boundary.length = α₀ + αT)
    (hD : (σ.datumII hU b α₀ αT a Jt).emptyIfBot.IsWeakDatum)
    (hperm : (σ.datumII hU b α₀ αT a Jt).emptyIfBot.IsPermissible Bt)
    (hU' : IsOpen (σ.step b t).xHatPrimeStar) (f : (σ.step b t).xTilde hU' ⟶ σ.xTilde hU)
    (hf : f ≫ (σ.uBar hU).ι = ((σ.step b t).uBar hU').ι ≫ σ.fBar b t)
    (hmono : IsMonoidalTransformationOf f Bt) (j : Fin αT) :
    (σ.step b t).eTildeAt hU' (α₀ + j) =
      Subscheme.strictTransform hmono.toMonoidalTransformation (σ.eTildeAt hU (α₀ + j)) := by
  have hi : α₀ + (j : ℕ) < σ.boundary.length := by have := j.2; omega
  set t' : MonoidalTransformation (σ.xTilde hU) Bt := hmono.toMonoidalTransformation with ht'
  have hX' : (t'.X').IsNonsingular :=
    (t'.isNonsingular_and_isNonsingular_exceptional H.nonsingular_xTilde H.nonsingular_Bt).1
  have hY' : t.X'.IsNonsingular :=
    (t.isNonsingular_and_isNonsingular_exceptional H.nonsingular_Y H.nonsingular_B).1
  have hc := σ.comp_cTilde_step_eq b t hU hU' f hf
  set g := (σ.step b t).cTilde hU' with hg
  set ED := σ.boundary.getD (α₀ + j) Subscheme.empty with hED
  have hLHS : (σ.step b t).eTildeAt hU' (α₀ + j) =
      Subscheme.totalTransform g (Subscheme.strictTransform t ED) := by
    rw [StageState.eTildeAt_eq_totalTransform_cTilde, StageState.getD_boundary_step_of_lt σ b t hi]
  have hF1 : Subscheme.totalTransform g (Subscheme.totalTransform t.f ED) =
      Subscheme.totalTransform f (σ.eTildeAt hU (α₀ + j)) := by
    rw [← Subscheme.totalTransform_comp, ← hc, Subscheme.totalTransform_comp,
      ← StageState.eTildeAt_eq_totalTransform_cTilde]
  have hF3 : Subscheme.totalTransform g t.exceptional = t'.exceptional := by
    show Subscheme.totalTransform g (Subscheme.totalTransform t.f B) =
      Subscheme.totalTransform f Bt
    rw [← Subscheme.totalTransform_comp, ← hc, Subscheme.totalTransform_comp,
      H.totalTransform_eq]
  have hED' : σ.boundary.get ⟨α₀ + j, hi⟩ = ED := by
    rw [hED, List.getD_eq_getElem _ _ hi]; rfl
  refine Subscheme.ext_stalkIdeal fun yb => ?_
  have : IsRegularLocalRing (t'.X'.presheaf.stalk yb) := hX' yb
  have : IsDomain (t'.X'.presheaf.stalk yb) := isDomain_of_isRegularLocalRing _
  have : IsRegularLocalRing (t.X'.presheaf.stalk (g.base yb)) := hY' _
  have hB := DatumTransform.stalkIdeal_totalTransform_eq_strict_mul_exceptional_pow_of_pts_subset
    (B := B) (fun i : Fin σ.boundary.length => σ.boundary.get i) H.nonsingular_Y H.divisor H.nc
    H.nc_B H.irreducible_B H.nonsingular_B t ⟨α₀ + j, hi⟩ (g.base yb)
  simp only [hED'] at hB
  have hA := H.stalkIdeal_totalTransform_eTildeAt hD hperm t' j yb
  have hm : (if B.pts ⊆ ED.pts then 1 else 0) =
      (if Bt.pts ⊆ (σ.eTildeAt hU (α₀ + j)).pts then 1 else 0) := by
    simp only [hED, ← H.pts_subset_iff (α₀ + j)]
  have hLS : (Subscheme.totalTransform g (Subscheme.totalTransform t.f ED)).stalkIdeal yb =
      (Subscheme.totalTransform g (Subscheme.strictTransform t ED)).stalkIdeal yb *
        (t'.exceptional.stalkIdeal yb) ^ (if B.pts ⊆ ED.pts then 1 else 0) := by
    rw [Hironaka.stalkIdeal_totalTransform g, hB, Ideal.map_mul, Ideal.map_pow,
      ← Hironaka.stalkIdeal_totalTransform g, ← Hironaka.stalkIdeal_totalTransform g, hF3]
  rw [hF1] at hLS
  rw [hLHS]
  obtain ⟨g0, hg0, hnz⟩ := t'.invertible.exists_stalkIdeal_eq_span yb
  have hg0ne : g0 ≠ 0 := nonZeroDivisors.ne_zero hnz
  refine Ideal.eq_of_mul_pow_eq_of_eq_span (m := if B.pts ⊆ ED.pts then 1 else 0) hg0 hg0ne ?_
  exact hLS.symm.trans (hA.trans (by rw [hm]; rfl))

/-- `J̄(s+1)` on `X̃_{s+1}` is the division of `f̃⁻¹(J̄(s))` by `P̃^b`, `P̃` the exceptional divisor
of `f̃` (the pull-back of the definition of `J̄(s+1)` to `X̃_{s+1}`). -/
theorem StageState.jBarT_step_eq_divPow [Hironaka.HironakaCitedResults.{u}] (σ : StageState Y) (b : ℕ) {B : Subscheme Y}
    (t : MonoidalTransformation Y B) (hU : IsOpen σ.xHatPrimeStar)
    (hU' : IsOpen (σ.step b t).xHatPrimeStar) {Bt : Subscheme (σ.xTilde hU)}
    (hBt : Subscheme.totalTransform (σ.cTilde hU) B = Bt)
    (f : (σ.step b t).xTilde hU' ⟶ σ.xTilde hU)
    (hf : f ≫ (σ.uBar hU).ι = ((σ.step b t).uBar hU').ι ≫ σ.fBar b t) :
    (σ.step b t).jBarT hU' =
      Subscheme.divPow (Subscheme.totalTransform f (σ.jBarT hU))
        (Subscheme.totalTransform f Bt) b := by
  have hmono := (t.baseChange σ.c).isMonoidalTransformationOf_strictTransformMap σ.xBar
  have hP : (Subscheme.totalTransform (σ.fBar b t) (σ.bBarOn B)).IsInvertibleIdeal := hmono.1
  have h1 : (σ.step b t).jBarT hU' = Subscheme.totalTransform ((σ.step b t).uBar hU').ι
      (Subscheme.divPow (Subscheme.totalTransform (σ.fBar b t) σ.jBar)
        (Subscheme.totalTransform (σ.fBar b t) (σ.bBarOn B)) b) := rfl
  have hP' : Subscheme.totalTransform ((σ.step b t).uBar hU').ι
      (Subscheme.totalTransform (σ.fBar b t) (σ.bBarOn B)) = Subscheme.totalTransform f Bt := by
    rw [← Subscheme.totalTransform_comp, ← hf, Subscheme.totalTransform_comp, ← hBt]
    unfold StageState.cTilde StageState.bBarOn StageState.bHat
    rw [Subscheme.totalTransform_comp, Subscheme.totalTransform_comp]
  have hJ' : Subscheme.totalTransform ((σ.step b t).uBar hU').ι
      (Subscheme.totalTransform (σ.fBar b t) σ.jBar) = Subscheme.totalTransform f (σ.jBarT hU) := by
    rw [← Subscheme.totalTransform_comp, ← hf, Subscheme.totalTransform_comp]
    rfl
  rw [h1, Subscheme.totalTransform_divPow _ _ _ hP, hP', hJ']

/-- `J̄(s) ⊆ P(B̃)^b` on all of `X̃` (stalkwise). -/
theorem StageState.BlowupHyp.stalkIdeal_jBarT_le (H : σ.BlowupHyp b t hU Bt)
    (z : σ.xTilde hU) : (σ.jBarT hU).stalkIdeal z ≤ (Bt.stalkIdeal z) ^ b := by
  have hBt' : Bt = Subscheme.totalTransform (σ.uBar hU).ι (σ.bBarOn B) := by
    rw [← H.totalTransform_eq]
    unfold StageState.cTilde StageState.bBarOn StageState.bHat
    rw [Subscheme.totalTransform_comp, Subscheme.totalTransform_comp]
  by_cases hz : (σ.uBar hU).ι z ∈ (σ.bBarOn B).pts
  · have hle := H.jBar_le ((σ.uBar hU).ι z) z.2 hz
    unfold StageState.jBarT
    rw [Hironaka.stalkIdeal_totalTransform, hBt', Hironaka.stalkIdeal_totalTransform,
      ← Ideal.map_pow]
    exact Ideal.map_mono hle
  · have hzB : z ∉ Bt.pts := by
      rw [hBt', Subscheme.pts_totalTransform_eq_preimage]
      exact hz
    rw [Subscheme.stalkIdeal_eq_top_of_notMem_pts hzB, Ideal.top_pow]
    exact le_top

/-- `f̃⁻¹(J̄(s)) ⊆ P̃^b` (stalkwise). -/
theorem StageState.BlowupHyp.stalkIdeal_totalTransform_jBarT_le (H : σ.BlowupHyp b t hU Bt)
    {Z : Scheme.{u}} (f : Z ⟶ σ.xTilde hU) (y : Z) :
    (Subscheme.totalTransform f (σ.jBarT hU)).stalkIdeal y ≤
      ((Subscheme.totalTransform f Bt).stalkIdeal y) ^ b := by
  rw [Hironaka.stalkIdeal_totalTransform, Hironaka.stalkIdeal_totalTransform, ← Ideal.map_pow]
  exact Ideal.map_mono (H.stalkIdeal_jBarT_le (f y))

open Classical in
/-- The numerical facts of the generic point of `B̃` (p. 325): `b ≤ ∑_{B̃ ⊆ Ẽ_j} a_j + ν` and
`ν ≤ ν((J̃)_ξ)` at the generic point `ξ` of `B̃`. -/
theorem StageState.BlowupHyp.generic (H : σ.BlowupHyp b t hU Bt)
    {α₀ αT : ℕ} {a : Fin αT → ℕ} {Jt : Subscheme (σ.xTilde hU)}
    (ha : ∀ j : Fin αT, σ.eTildeAt hU (α₀ + j) = ⊥ → a j = 0)
    (hD : (σ.datumII hU b α₀ αT a Jt).emptyIfBot.IsWeakDatum)
    (hperm : (σ.datumII hU b α₀ αT a Jt).emptyIfBot.IsPermissible Bt) :
    b ≤ (∑ j : Fin αT, if Bt.pts ⊆ (σ.eTildeAt hU (α₀ + j)).pts then a j else 0) +
        (σ.datumII hU b α₀ αT a Jt).nu.toNat ∧
      ∃ ξ : σ.xTilde hU, IsGenericPoint ξ Bt.pts ∧
        ((σ.datumII hU b α₀ αT a Jt).nu.toNat : ℕ∞) ≤ Ideal.nu (Jt.stalkIdeal ξ) := by
  have key := DatumII.Raw.b_le_sum_add_nu_and_exists_isGenericPoint_of_forall_stalkIdeal_ne_bot
    H.nonsingular_xTilde (σ.datumII hU b α₀ αT a Jt).emptyIfBot hD.2.2.2 H.irreducible_Bt hperm
  have hnu : (σ.datumII hU b α₀ αT a Jt).emptyIfBot.nu = (σ.datumII hU b α₀ αT a Jt).nu :=
    DatumII.Raw.emptyIfBot_nu _ ha
  rw [hnu] at key
  refine ⟨?_, key.2⟩
  refine le_of_le_of_eq key.1 ?_
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  by_cases hj : σ.eTildeAt hU (α₀ + j) = ⊥
  · have h0 : (σ.datumII hU b α₀ αT a Jt).a j = 0 := ha j hj
    simp [h0, ha j hj]
  · have hE : (σ.datumII hU b α₀ αT a Jt).emptyIfBot.E j = σ.eTildeAt hU (α₀ + j) :=
      Subscheme.emptyIfBot_of_ne_bot hj
    simp only [hE]
    rfl

open Classical in
/-- **The identity `J̃' ∏ (Ẽ'_j)^{a'_j} = J̄(s+1)`** (pp. 325–326): for the transform of the raw
datum `ℜ^{N-1}_II` by `f̃`, with `J̃ ∏ Ẽ_j^{a_j} = J̄(s)`.  The divisibility of `f̃⁻¹(J̃)` by
`P̃^ν` and the bound `b ≤ ∑_{B̃ ⊆ Ẽ_j} a_j + ν` are those of the generic point of `B̃`. -/
theorem StageState.BlowupHyp.prod_transform_eq [Hironaka.HironakaCitedResults.{u}] (H : σ.BlowupHyp b t hU Bt)
    {α₀ αT : ℕ} {a : Fin αT → ℕ} {Jt : Subscheme (σ.xTilde hU)}
    (ha : ∀ j : Fin αT, σ.eTildeAt hU (α₀ + j) = ⊥ → a j = 0)
    (hD : (σ.datumII hU b α₀ αT a Jt).emptyIfBot.IsWeakDatum)
    (hperm : (σ.datumII hU b α₀ αT a Jt).emptyIfBot.IsPermissible Bt)
    (hJt : Jt * ∏ j : Fin αT, (σ.eTildeAt hU (α₀ + j)) ^ (a j) = σ.jBarT hU)
    (hU' : IsOpen (σ.step b t).xHatPrimeStar) (f : (σ.step b t).xTilde hU' ⟶ σ.xTilde hU)
    (hf : f ≫ (σ.uBar hU).ι = ((σ.step b t).uBar hU').ι ≫ σ.fBar b t)
    (hmono : IsMonoidalTransformationOf f Bt) :
    ((σ.datumII hU b α₀ αT a Jt).transform hmono.toMonoidalTransformation).J *
      ∏ i, (((σ.datumII hU b α₀ αT a Jt).transform hmono.toMonoidalTransformation).E i) ^
        (((σ.datumII hU b α₀ αT a Jt).transform hmono.toMonoidalTransformation).a i) =
      (σ.step b t).jBarT hU' := by
  set t' : MonoidalTransformation (σ.xTilde hU) Bt := hmono.toMonoidalTransformation with ht'
  set D := σ.datumII hU b α₀ αT a Jt with hDdef
  have hX' : (t'.X').IsNonsingular :=
    (t'.isNonsingular_and_isNonsingular_exceptional H.nonsingular_xTilde H.nonsingular_Bt).1
  have hJT := StageState.jBarT_step_eq_divPow σ b t hU hU' H.totalTransform_eq f hf
  obtain ⟨hbsum, ξ, hξ, hνξ⟩ := H.generic ha hD hperm
  have hdiv : Subscheme.totalTransform f Jt ≤ t'.exceptional ^ D.nu.toNat :=
    Subscheme.totalTransform_le_exceptional_pow H.nonsingular_xTilde H.nonsingular_Bt t' Jt hξ
      hνξ
  refine Subscheme.ext_stalkIdeal fun yb => ?_
  have : IsRegularLocalRing (t'.X'.presheaf.stalk yb) := hX' yb
  have : IsDomain (t'.X'.presheaf.stalk yb) := isDomain_of_isRegularLocalRing _
  obtain ⟨g0, hg0, hnz⟩ := t'.invertible.exists_stalkIdeal_eq_span yb
  have hg0ne : g0 ≠ 0 := nonZeroDivisors.ne_zero hnz
  -- the multiplicities
  set m : Fin αT → ℕ := fun j => if Bt.pts ⊆ (σ.eTildeAt hU (α₀ + j)).pts then 1 else 0 with hm
  -- the left-hand side of the hypothesis of the ring lemma
  have hLeft : (Subscheme.totalTransform f
      (Jt * ∏ j : Fin αT, (σ.eTildeAt hU (α₀ + j)) ^ (a j))).stalkIdeal yb =
      (Subscheme.totalTransform f Jt).stalkIdeal yb *
        ∏ j : Fin αT, ((Subscheme.strictTransform t' (σ.eTildeAt hU (α₀ + j))).stalkIdeal yb *
          Ideal.span {g0} ^ (m j)) ^ (a j) := by
    rw [Hironaka.stalkIdeal_totalTransform, Subscheme.stalkIdeal_mul_eq,
      Subscheme.stalkIdeal_finset_prod, Ideal.map_mul, Ideal.map_finset_prod,
      ← Hironaka.stalkIdeal_totalTransform f Jt]
    congr 1
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [Subscheme.stalkIdeal_pow_eq, Ideal.map_pow, ← Hironaka.stalkIdeal_totalTransform f]
    have := H.stalkIdeal_totalTransform_eTildeAt hD hperm t' j yb
    have hexc : t'.exceptional.stalkIdeal yb = Ideal.span {g0} := hg0
    rw [this, hexc]
  -- the right-hand side
  have hIle : (Subscheme.totalTransform f (σ.jBarT hU)).stalkIdeal yb ≤
      Ideal.span {g0 ^ b} := by
    have := H.stalkIdeal_totalTransform_jBarT_le f yb
    rw [show (Subscheme.totalTransform f Bt).stalkIdeal yb = Ideal.span {g0} from hg0,
      Ideal.span_singleton_pow] at this
    exact this
  have hI := Ideal.eq_colon_mul_span_singleton_pow hIle
  set W := (Subscheme.totalTransform f (σ.jBarT hU)).stalkIdeal yb with hWdef
  have hRHS : ((σ.step b t).jBarT hU').stalkIdeal yb =
      W.colon ((Ideal.span {g0} ^ b : Ideal _) : Set _) := by
    rw [hJT, Subscheme.stalkIdeal_divPow t'.invertible b yb]
    show _ = _
    rw [show (Subscheme.totalTransform f Bt).stalkIdeal yb = Ideal.span {g0} from hg0]
  have hW : (Subscheme.totalTransform f
      (Jt * ∏ j : Fin αT, (σ.eTildeAt hU (α₀ + j)) ^ (a j))).stalkIdeal yb =
      Ideal.span {g0} ^ b * W.colon ((Ideal.span {g0} ^ b : Ideal _) : Set _) := by
    rw [hJt]
    exact hI.trans (mul_comm _ _)
  rw [hLeft] at hW
  have hdivst : (Subscheme.totalTransform f Jt).stalkIdeal yb ≤ Ideal.span {g0 ^ D.nu.toNat} := by
    have := (Subscheme.le_iff_stalkIdeal_le.mp hdiv) yb
    rw [Subscheme.stalkIdeal_pow_eq, show t'.exceptional.stalkIdeal yb = Ideal.span {g0} from hg0,
      Ideal.span_singleton_pow] at this
    exact this
  have hb : Ideal.span {g0} ≠ ⊤ → b ≤ (∑ j, m j * a j) + D.nu.toNat := by
    intro _
    refine le_of_le_of_eq hbsum ?_
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [hm]
    split_ifs <;> simp
  have key := Ideal.colon_mul_prod_mul_pow_eq hg0ne
    ((Subscheme.totalTransform f Jt).stalkIdeal yb)
    (fun j => (Subscheme.strictTransform t' (σ.eTildeAt hU (α₀ + j))).stalkIdeal yb) a m
    D.nu.toNat b _ hdivst hb hW
  -- the left-hand side of the goal
  have hBtred : Bt.IsReduced := Subscheme.isReduced_of_isNonsingular H.nonsingular_Bt
  have hanew : (∑ i ∈ Finset.univ.filter fun i : Fin D.α => Bt.IsContainedIn (D.E i), D.a i) +
      D.nu.toNat - D.b = (∑ j, m j * a j) + D.nu.toNat - b := by
    rw [Finset.sum_filter]
    have hDb : D.b = b := rfl
    rw [hDb]
    congr 2
    refine Finset.sum_congr rfl fun j _ => ?_
    have hiff : Bt.IsContainedIn (σ.eTildeAt hU (α₀ + j)) ↔
        Bt.pts ⊆ (σ.eTildeAt hU (α₀ + j)).pts :=
      ⟨pts_subset_of_isContainedIn, Subscheme.isContainedIn_of_pts_subset hBtred⟩
    show (if Bt.IsContainedIn (σ.eTildeAt hU (α₀ + j)) then a j else 0) = m j * a j
    simp only [hm]
    by_cases hc : Bt.IsContainedIn (σ.eTildeAt hU (α₀ + j))
    · simp [hc, hiff.mp hc]
    · have hn : ¬ Bt.pts ⊆ (σ.eTildeAt hU (α₀ + j)).pts := fun h => hc (hiff.mpr h)
      simp [hc, hn]
  have hprod : (∏ i, ((D.transform t').E i) ^ ((D.transform t').a i)).stalkIdeal yb =
      (∏ j : Fin αT, ((Subscheme.strictTransform t' (σ.eTildeAt hU (α₀ + j))).stalkIdeal yb) ^
        (a j)) * Ideal.span {g0} ^ ((∑ j, m j * a j) + D.nu.toNat - b) := by
    rw [DatumII.Raw.prod_transform D t', Subscheme.stalkIdeal_mul_eq,
      Subscheme.stalkIdeal_finset_prod, DatumII.Raw.transform_E_last,
      DatumII.Raw.transform_a_last, Subscheme.stalkIdeal_pow_eq]
    have hexc : t'.exceptional.stalkIdeal yb = Ideal.span {g0} := hg0
    congr 1
    · refine Finset.prod_congr rfl fun j _ => ?_
      rw [Subscheme.stalkIdeal_pow_eq, DatumII.Raw.transform_E_castSucc,
        DatumII.Raw.transform_a_castSucc]
      rfl
    · rw [hexc]
      congr 1
  have hJ' : (D.transform t').J.stalkIdeal yb =
      ((Subscheme.totalTransform f Jt).stalkIdeal yb).colon
        ((Ideal.span {g0} ^ D.nu.toNat : Ideal _) : Set _) := by
    show (Subscheme.divPow (Subscheme.totalTransform t'.f Jt) t'.exceptional
      D.nu.toNat).stalkIdeal yb = _
    rw [Subscheme.stalkIdeal_divPow (P := t'.exceptional) t'.invertible]
    have hexc : t'.exceptional.stalkIdeal yb = Ideal.span {g0} := hg0
    rw [hexc]
  rw [Subscheme.stalkIdeal_mul_eq, hprod, hJ', hRHS, ← key]
  ring

/-- The new boundary component of a step is the exceptional divisor. -/
theorem StageState.getD_boundary_step_length (σ : StageState Y) (b : ℕ) {B : Subscheme Y}
    (t : MonoidalTransformation Y B) :
    (σ.step b t).boundary.getD σ.boundary.length Subscheme.empty = t.exceptional := by
  show (σ.boundary.map (Subscheme.strictTransform t) ++ [t.exceptional]).getD
    σ.boundary.length _ = _
  rw [List.getD_append_right _ _ _ _ (by simp)]
  simp

/-- The trace on `X̃_{s+1}` of the new exceptional component is the exceptional divisor of
`f̃`. -/
theorem StageState.BlowupHyp.eTildeAt_step_length_eq (H : σ.BlowupHyp b t hU Bt)
    (hU' : IsOpen (σ.step b t).xHatPrimeStar) (f : (σ.step b t).xTilde hU' ⟶ σ.xTilde hU)
    (hf : f ≫ (σ.uBar hU).ι = ((σ.step b t).uBar hU').ι ≫ σ.fBar b t) :
    (σ.step b t).eTildeAt hU' σ.boundary.length = Subscheme.totalTransform f Bt := by
  have hc := σ.comp_cTilde_step_eq b t hU hU' f hf
  rw [StageState.eTildeAt_eq_totalTransform_cTilde, StageState.getD_boundary_step_length]
  show Subscheme.totalTransform ((σ.step b t).cTilde hU') (Subscheme.totalTransform t.f B) = _
  rw [← Subscheme.totalTransform_comp, ← hc, Subscheme.totalTransform_comp, H.totalTransform_eq]

/-- Extensionality for type II data with equal numbers of components. -/
private theorem datumII_ext_of_cast {X : Scheme.{u}} {R₁ R₂ : DatumII.Raw X} (hα : R₁.α = R₂.α)
    (hE : ∀ i : Fin R₁.α, R₁.E i = R₂.E (Fin.cast hα i))
    (ha : ∀ i : Fin R₁.α, R₁.a i = R₂.a (Fin.cast hα i)) (hJ : R₁.J = R₂.J) (hb : R₁.b = R₂.b) :
    R₁ = R₂ := by
  obtain ⟨α₁, E₁, a₁, J₁, b₁⟩ := R₁
  obtain ⟨α₂, E₂, a₂, J₂, b₂⟩ := R₂
  simp only at hα hJ hb
  subst hα hJ hb
  have hE' : E₁ = E₂ := funext hE
  have ha' : a₁ = a₂ := funext ha
  subst hE' ha'
  rfl

open Classical in
/-- **The blow-up step on states** (p. 310: "Then the permissible monoidal transformation
`f_{B_s}` of `X_s` with center `B_s` for `ℜ(s)` induces the given permissible monoidal
transformation `f_B̃` of `X̃` for `ℜ^{N-1}_II`").  Under the hypotheses `H` on the center `B` of the
step, on `B̃ = B̂ ∩ X̃` and on the bad locus, the step induces a monoidal transformation
`f̃ : X̃_{s+1} → X̃_s` with center `B̃`; the transform of the raw datum
`ℜ^{N-1}_II = (Ẽ_j | J̃, b | a_j)` of the state `σ` by `f̃` is the datum of the state `σ.step`
(with the exponents `a_1, …, a_α̃` followed by one new exponent `a_{α̃+1}`), and
`J̃' ∏ Ẽ'_j^{a'_j} = J̄(s+1)`.

Deviation from the paper (gap filled): the paper says only "induces" (p. 310; also "the relation
between `ℜ(s+1)` and `f̄_s*(ℜ^{N-1}_II)` is the same as that between `ℜ(s)` and `ℜ^{N-1}_II`",
p. 322, for Theorem C).  Lean proves it for the raw datum, whose entries `Ẽ_j` may be the whole
space (the case `F = E_i`); the hypotheses are expressed through the
emptied datum (`emptyIfBot`).  The argument is the one of pp. 324–326: `f̃⁻¹(Ẽ_j) = Ẽ'_j P̃^m` is
computed both on `X̃` (normal crossings with `B̃`) and on `X_{s+1}` (normal crossings with `B_s`),
`f̃⁻¹(J̄(s)) = P̃^b J̄(s+1)` by the bound `J̄(s) ⊆ P(B̄)^b`, and `J̃' = f̃⁻¹(J̃) P̃^{-ν}` with
`b ≤ ∑_{B̃ ⊆ Ẽ_j} a_j + ν` at the generic point of `B̃`. -/
@[blueprint "lem:IV.3-blowup-step"
  (statement := /-- Let $\sigma$ be the state of the construction at the stage $s$ (as in
    \cref{lem:IV.3-trivial-step}), $f\colon X_{s+1}\to X_s$ the monoidal transformation with
    center $B=B_s$, a non-singular irreducible subscheme such that $\bigcup_iE_i(s)$ has only
    normal crossings with $B$ (\cref{rem:IV.3-4}, \cref{rem:IV.3-5}), and $\tilde B$ a
    non-singular irreducible subscheme of $\tilde X$ with $\tilde B=\hat B_s\cap\tilde X$,
    $B_s\subseteq\overline{c_s(\tilde B)}$, such that $\mathrm{Bad}_s\cap\tilde X=\emptyset$
    (so that every component of $\hat B_s$ through $\tilde X$ is good, in particular
    $\bar J(s)\subseteq P(\bar B_s)^b$ over $\tilde B$), and such that $f_{\tilde B}$ is
    permissible for $\mathfrak R^{N-1}_{\mathrm{II}}=(\tilde E_1,\dots,\tilde E_{\tilde\alpha}\mid
    \tilde J,b\mid a_1,\dots,a_{\tilde\alpha})$ with $\tilde J\prod\tilde P_j^{a_j}=\bar
    J(s)$. Then $\bar f_s$ induces the monoidal transformation $f_{\tilde B}\colon
    \tilde X_{s+1}\to\tilde X_s$ with center $\tilde B$, and the transform
    $f_{\tilde B}^*(\mathfrak R^{N-1}_{\mathrm{II}})=(\tilde E_1',\dots,\tilde
    E_{\tilde\alpha+1}'\mid\tilde J',b\mid a_1,\dots,a_{\tilde\alpha},a_{\tilde\alpha+1})$ of
    Definition~7 (\cref{def:I.7-II}) is the datum $\mathfrak R^{N-1}_{\mathrm{II}}$ of the stage
    $s+1$ (the $\tilde E_j'$ being the traces on $\tilde X_{s+1}$ of the $E_j(s+1)$), and
    $\tilde J'\prod_j\tilde E_j'^{\,a_j'}=\bar J(s+1)$. (p.~310: ``Then the permissible monoidal
    transformation $f_{B_s}$ of $X_s$ with center $B_s$ for $\mathfrak R(s)$ induces the given
    permissible monoidal transformation $f_{\tilde B}$ of $\tilde X$ for
    $\mathfrak R^{N-1}_{\mathrm{II}}$.'')

    \textbf{Deviation from the paper (gap filled).} The paper says only ``induces''; Lean proves
    the identification of the transformed datum with the datum of the next stage, and the
    identity $\tilde J'\prod\tilde E_j'^{\,a_j'}=\bar J(s+1)$ that keeps the invariant, for the
    raw datum (whose entries $\tilde E_j$ may be all of $\tilde X$, the case $F=E_i$;
    hypotheses stated through the emptied datum). -/)
  (proof := /-- By the trivial-step argument (\cref{lem:IV.3-trivial-step}) $\bar f_s$ restricts to
    a monoidal transformation of $\tilde X$ with center $\bar B_s\cap\tilde X=\tilde B$, since
    $\mathrm{Bad}_s$ misses $\tilde X$. The total transform $f_{\tilde B}^{-1}(\tilde E_j)$ is
    computed twice: on $\tilde X$, as $\tilde E_j'\tilde P^m$ with $m=1$ iff $\tilde B\subseteq
    \tilde E_j$, by the normal crossings of the $\tilde E_j$ with $\tilde B$ (permissibility
    of $f_{\tilde B}$); and as the pull-back of $f^{-1}(E_j(s))=E_j(s+1)P^m$ on $X_{s+1}$,
    $m=1$ iff $B\subseteq E_j(s)$, by the normal crossings of the $E_j(s)$ with $B$; the two
    exponents agree since $B$ is the closure of $c_s(\tilde B)$, and cancelling $\tilde P^m$
    in the regular local rings of $\tilde X_{s+1}$ gives that $\tilde E_j'$ is the strict
    transform. The entries equal to $\tilde X$ have both sides equal to $\tilde X_{s+1}$. Then
    $\bar f_s^{-1}(\bar J(s))=\tilde P^b\bar J(s+1)$ because $\bar J(s)\subseteq
    P(\bar B_s)^b$; $f_{\tilde B}^{-1}(\tilde J)=\tilde P^{\nu}\tilde J'$ by Remark 2 of
    Ch.~III at the generic point of $\tilde B$, and $b\le\sum_{\tilde B\subseteq\tilde
    E_j}a_j+\nu$ since the generic point lies in $S(\mathfrak R^{N-1}_{\mathrm{II}})$; hence
    $\tilde J'\prod\tilde E_j'^{\,a_j}\tilde P^{a_{\tilde\alpha+1}}=\bar J(s+1)$ with
    $a_{\tilde\alpha+1}=\sum_{\tilde B\subseteq\tilde E_j}a_j+\nu-b$ (no truncation). -/)
  (proofUses := ["lem:IV.3-trivial-step", "def:I.7-II", "rem:IV.3-4", "rem:IV.3-5",
    "compat:blowup-flat-base-change"])
  (latexEnv := "lemma")]
theorem StageState.BlowupHyp.exists_transform_eq_datumII [Hironaka.HironakaCitedResults.{u}] (H : σ.BlowupHyp b t hU Bt)
    {α₀ αT : ℕ} {a : Fin αT → ℕ} {Jt : Subscheme (σ.xTilde hU)}
    (hlen : σ.boundary.length = α₀ + αT)
    (ha : ∀ j : Fin αT, σ.eTildeAt hU (α₀ + j) = ⊥ → a j = 0)
    (hD : (σ.datumII hU b α₀ αT a Jt).emptyIfBot.IsWeakDatum)
    (hperm : (σ.datumII hU b α₀ αT a Jt).emptyIfBot.IsPermissible Bt)
    (hJt : Jt * ∏ j : Fin αT, (σ.eTildeAt hU (α₀ + j)) ^ (a j) = σ.jBarT hU)
    (hU' : IsOpen (σ.step b t).xHatPrimeStar) :
    ∃ (f : (σ.step b t).xTilde hU' ⟶ σ.xTilde hU)
      (_ : f ≫ (σ.uBar hU).ι = ((σ.step b t).uBar hU').ι ≫ σ.fBar b t)
      (hmono : IsMonoidalTransformationOf f Bt) (anew : ℕ)
      (Jt' : Subscheme ((σ.step b t).xTilde hU')),
      (σ.datumII hU b α₀ αT a Jt).transform hmono.toMonoidalTransformation =
        (σ.step b t).datumII hU' b α₀ (αT + 1) (Fin.snoc (α := fun _ => ℕ) a anew) Jt' ∧
      Jt' * ∏ i : Fin (αT + 1), ((σ.step b t).eTildeAt hU' (α₀ + i)) ^
        (Fin.snoc (α := fun _ => ℕ) a anew i) = (σ.step b t).jBarT hU' := by
  obtain ⟨f, hf, hmono⟩ := σ.exists_isMonoidalTransformationOf_fTilde b t hU hU'
    H.notMem_badLocus
  rw [H.totalTransform_eq] at hmono
  set D := σ.datumII hU b α₀ αT a Jt with hDdef
  have hdat : D.transform hmono.toMonoidalTransformation =
      (σ.step b t).datumII hU' b α₀ (αT + 1)
        (Fin.snoc (α := fun _ => ℕ) a
          ((D.transform hmono.toMonoidalTransformation).a (Fin.last D.α)))
        (D.transform hmono.toMonoidalTransformation).J := by
    refine datumII_ext_of_cast rfl (fun i => ?_) (fun i => ?_) rfl rfl
    · induction i using Fin.lastCases with
      | last =>
        rw [DatumII.Raw.transform_E_last]
        show _ = (σ.step b t).eTildeAt hU' (α₀ + αT)
        rw [← hlen, H.eTildeAt_step_length_eq hU' f hf]
        rfl
      | cast j =>
        rw [DatumII.Raw.transform_E_castSucc]
        exact (H.eTildeAt_step_eq_strictTransform hlen hD hperm hU' f hf hmono j).symm
    · induction i using Fin.lastCases with
      | last => exact (Fin.snoc_last (α := fun _ => ℕ) _ a).symm
      | cast j =>
        rw [DatumII.Raw.transform_a_castSucc]
        exact (Fin.snoc_castSucc (α := fun _ => ℕ) _ a j).symm
  refine ⟨f, hf, hmono, _, _, hdat, ?_⟩
  have key := H.prod_transform_eq ha hD hperm hJt hU' f hf hmono
  rw [hdat] at key
  exact key

end BlowupStepDatum

/-! ### A standing tower from a prepared finite succession -/


section TowerStanding

variable {N n : ℕ} {X : Scheme.{u}} {ℜ : DatumI.Raw X} {r : Restriction X}

/-- A tower whose centers are empty from stage `m` on, and whose `m`th initial segment is
permissible for `(ℜ, r)`, is permissible for `(ℜ, r)` at every stage (tacit: p. 295, "the monoidal
transformation with the empty center is the identity isomorphism"). -/
theorem isPermissibleSucc_pre_of_forall_eq_empty [Hironaka.HironakaCitedResults.{u}] (T : Tower X) (m : ℕ)
    (hB : ∀ s, m ≤ s → T.B s = Subscheme.empty) (hgood : IsGoodDatumI N n X ℜ)
    (hr : r.IsFor ℜ) (hg : r.IsPermissibleSucc (T.pre m) ℜ) :
    ∀ s, r.IsPermissibleSucc (T.pre s) ℜ := by
  have hdown : ∀ k s, s + k = m → r.IsPermissibleSucc (T.pre s) ℜ := by
    intro k
    induction k with
    | zero =>
      intro s hs
      obtain rfl : s = m := by omega
      exact hg
    | succ k ih =>
      intro s hs
      have h := ih (s + 1) (by omega)
      cases r with
      | closed F =>
        exact ((MonoidalSuccession.isPermissibleIClosed_snoc_iff (T.pre s) (T.B s)
          (T.monoidalTransformation s) ℜ F).mp h).1
      | opn U =>
        exact ((MonoidalSuccession.isPermissibleIOpen_snoc_iff (T.pre s) (T.B s)
          (T.monoidalTransformation s) ℜ U).mp h).1
  have hup : ∀ k, r.IsPermissibleSucc (T.pre (m + k)) ℜ := by
    intro k
    induction k with
    | zero => exact hg
    | succ k ih =>
      have hgd := (isGoodDatumI_transformI_and_isFor_transformSucc (T.pre (m + k)) hgood hr ih).1
      cases r with
      | closed F =>
        refine (MonoidalSuccession.isPermissibleIClosed_snoc_iff (T.pre (m + k)) (T.B (m + k))
          (T.monoidalTransformation (m + k)) ℜ F).mpr ⟨ih, ?_⟩
        rw [hB (m + k) (by omega)]
        exact ⟨DatumI.Raw.isPermissible_empty hgd.2.1, by
          rw [Subscheme.pts_empty]; exact Set.empty_subset _⟩
      | opn U =>
        refine (MonoidalSuccession.isPermissibleIOpen_snoc_iff (T.pre (m + k)) (T.B (m + k))
          (T.monoidalTransformation (m + k)) ℜ U).mpr ⟨ih, ?_⟩
        rw [hB (m + k) (by omega)]
        exact ⟨DatumI.Raw.isPermissible_empty hgd.2.1, by
          rw [Subscheme.pts_empty]; exact Set.empty_subset _⟩
  intro s
  rcases le_total s m with h | h
  · exact hdown (m - s) s (by omega)
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
    exact hup k

/-- `S(ℜ) ⊆ W*`. -/
theorem S_subset_wStar (hr : r.IsFor ℜ) : S ℜ r ⊆ wStar ℜ r := by
  cases r with
  | closed F => exact fun x hx => hx
  | opn U =>
    intro x hx
    refine ⟨hx.1, fun hxU => hx.2 (hr.2.2 x hxU)⟩

/-- The hypotheses of Remarks 1–5 on the finite succession `g_s` (p. 307): the conditions [(1)],
[(2)] and `x_0 ∈ g_s(S(ℜ(s)))`.  For the `s`th initial segment of a tower it is `PrepHyp`. -/
def PrepHypSucc (N : ℕ) {X Y : Scheme.{u}} (ℜ : DatumI.Raw X) (P : DatumI.Presentation ℜ)
    (r : Restriction X) (g : MonoidalSuccession X Y) (x₀ : X) : Prop :=
  (g.composite.base '' S (g.transformI ℜ) (r.transformSucc g)).Finite ∧
  (∀ y ∈ g.composite.base '' S (g.transformI ℜ) (r.transformSucc g),
    X.dimAt y = (N : WithBot ℕ∞)) ∧
  (∀ U, r = .opn U → ∀ W₁ ∈ (g.transformI ℜ).W.irreducibleComponents,
    ∀ i : Fin P.α, W₁.IsContainedIn (g.strictTransform (P.E i)) ∨
      (g.strictTransform (P.E i)).pts ∩ W₁.pts ∩
        S (g.transformI ℜ) (r.transformSucc g) = ∅) ∧
  x₀ ∈ g.composite.base '' S (g.transformI ℜ) (r.transformSucc g)

/-- **A standing tower from a prepared finite succession** (tacit in p. 310: "by replacing the
original succession `g_s : X_s → X` by one that includes the above succession"): a finite
permissible succession `g` of `X` for `(ℜ, r)` satisfying `[(1)]`, `[(2)]` and `x_0 ∈ g(S)` is the
initial segment `g_m` of a tower with empty centers from `m` on that satisfies the standing
assumptions of p. 295 and `PrepHyp` at `m`. -/
theorem exists_standing_prepHyp_of_prepHypSucc [Hironaka.HironakaCitedResults.{u}] (P : DatumI.Presentation ℜ) (hlt : n < N)
    (hX : IsAmbient X N) (hℜ : ℜ.IsDatum) (hn : ℜ.n = (n : WithBot ℕ∞)) (hr : r.IsFor ℜ)
    {Y : Scheme.{u}} (g : MonoidalSuccession X Y) (hg : r.IsPermissibleSucc g ℜ) {x₀ : X}
    (hprep : PrepHypSucc N ℜ P r g x₀) :
    ∃ (T : Tower X) (m : ℕ) (h : T.X m = Y), h ▸ T.pre m = g ∧
      (∀ s, m ≤ s → T.B s = Subscheme.empty) ∧ Standing N n ℜ P r T x₀ ∧
      PrepHyp N ℜ P r T x₀ m := by
  obtain ⟨T, m, h, hpre, hB⟩ := Tower.exists_pre_eq_of_succession g
  subst h
  have hpre' : T.pre m = g := hpre
  subst hpre'
  have hgood : IsGoodDatumI N n X ℜ := ⟨hX, hℜ, hn.le⟩
  have hx₀ := hprep.2.2.2
  have hS := composite_image_S_subset (T.pre m) hgood hr hg
  refine ⟨T, m, rfl, rfl, hB, ⟨hlt, hX, hℜ, hn, hr,
    isPermissibleSucc_pre_of_forall_eq_empty T m hB hgood hr hg,
    S_subset_wStar hr (hS hx₀), hprep.2.1 x₀ hx₀⟩, hprep⟩

end TowerStanding

/-! ### The invariant of the induction on the length of the resolving succession -/

/-- The offset `α₀` of the boundary components that enter the `Ẽ_j` (Remark 2, p. 308): `0` in the
closed case, `α` in the open case (`= Frame.eTildeOffset`). -/
def Restriction.eTildeOffset {X : Scheme.{u}} : Restriction X → ℕ → ℕ
  | .closed _, _ => 0
  | .opn _, α => α

/-- At the stage `g` the emptied auxiliary datum `ℜ^{N-1}_II` of p. 308 (entries `Ẽ_j` read off the
stage state of the fold of `g`, exponents `a`, `J̃`) is resolvable by `k` monoidal transformations.
Formalization infrastructure for the induction on the length of the resolving succession of `X̃`
(p. 310: "applying Theorem `II₂^{N-1}` to the resolution datum `ℜ^{N-1}_II` on `X̃` …"). -/
def StageResolvable (b : ℕ) {X : Scheme.{u}} {ℜ : DatumI.Raw X} (P : DatumI.Presentation ℜ)
    (r : Restriction X) {x₀ : X} (hx₀ : X.IsSimpleAt x₀) (z : Shat X x₀)
    (Jgen : Set (Shat X x₀)) {Y : Scheme.{u}} (g : MonoidalSuccession X Y) (k : ℕ) : Prop :=
  ∃ (hU : IsOpen (StageState.fold b g (StageState.initial P.E hx₀ z Jgen)).xHatPrimeStar)
    (a : Fin (bdryCard r P.α g.length) → ℕ)
    (Jt : Subscheme ((StageState.fold b g (StageState.initial P.E hx₀ z Jgen)).xTilde hU)),
    Jt * ∏ j : Fin (bdryCard r P.α g.length),
        ((StageState.fold b g (StageState.initial P.E hx₀ z Jgen)).eTildeAt hU
          (r.eTildeOffset P.α + j)) ^ (a j) =
      (StageState.fold b g (StageState.initial P.E hx₀ z Jgen)).jBarT hU ∧
    DatumII.Raw.ResolvableLen k
      ((StageState.fold b g (StageState.initial P.E hx₀ z Jgen)).datumII hU b
        (r.eTildeOffset P.α) (bdryCard r P.α g.length) a Jt).emptyIfBot

section OffsetApi

variable {N n : ℕ} {X : Scheme.{u}} {ℜ : DatumI.Raw X} {P : DatumI.Presentation ℜ}
  {r : Restriction X} {T : Tower X} {x₀ : X} {hS : Standing N n ℜ P r T x₀} (𝒮 : Frame hS)

/-- `Frame.eTildeOffset` is `Restriction.eTildeOffset`. -/
theorem Frame.eTildeOffset_eq : 𝒮.eTildeOffset = r.eTildeOffset P.α := by
  cases r <;> rfl

end OffsetApi

section OpenAlong

variable {Y Z : Scheme.{u}}

/-- Openness of `X̂*'` along a succession `h`: for the starting state and all the following ones
(formalization infrastructure: the steps of the extension are compared one at a time). -/
def StageState.OpenAlong (b : ℕ) : ∀ {Y Z : Scheme.{u}}, StageState Y →
    MonoidalSuccession Y Z → Prop
  | _, _, σ, .nil _ => IsOpen σ.xHatPrimeStar
  | _, _, σ, .cons _ t rest => IsOpen σ.xHatPrimeStar ∧ StageState.OpenAlong b (σ.step b t) rest

/-- The starting state is open along `h`. -/
theorem StageState.OpenAlong.isOpen_head {b : ℕ} {σ : StageState Y} {h : MonoidalSuccession Y Z}
    (H : σ.OpenAlong b h) : IsOpen σ.xHatPrimeStar := by
  cases h with
  | nil => exact H
  | cons B t rest => exact H.1

/-- The final state is open along `h`. -/
theorem StageState.OpenAlong.isOpen_fold {b : ℕ} {σ : StageState Y} {h : MonoidalSuccession Y Z}
    (H : σ.OpenAlong b h) : IsOpen (StageState.fold b h σ).xHatPrimeStar := by
  induction h with
  | nil X => exact H
  | cons B t rest ih => exact ih H.2

/-- The second state is open along `cons`. -/
theorem StageState.OpenAlong.step {b : ℕ} {σ : StageState Y} {B : Subscheme Y}
    {t : MonoidalTransformation Y B} {rest : MonoidalSuccession t.X' Z}
    (H : σ.OpenAlong b (MonoidalSuccession.cons B t rest)) : (σ.step b t).OpenAlong b rest :=
  H.2

end OpenAlong

end AB

end

end Hironaka
