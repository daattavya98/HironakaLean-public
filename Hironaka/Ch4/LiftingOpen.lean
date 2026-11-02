/-
Copyright (c) 2026 Daattavya Aggarwal, Minhyong Kim, Oisin Kim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daattavya Aggarwal, Minhyong Kim, Oisin Kim
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Architect
public import Hironaka.Ch4.StageState
public import Hironaka.Statements

/-!
# Openness of `X̂*'` along an extension (formalization infrastructure for p. 310)

> by replacing the original succession `g_s : X_s → X` by one that includes the above
> succession, … (p. 310)

When the proof of Theorems A* and B* replaces a prepared succession `g` of `X` by an extension
`g ++ e` (permissible, with `x_0` still in the image of `S`), the objects of the construction of
pp. 295–299 are kept at the stage `g` and the later stages are computed by folding `e`
(`StageState.fold`).  This file proves that all the states of that fold have an open set `X̂*'`
(`StageState.OpenAlong`), so that the next stages can be compared one at a time.

This is infrastructure (tacit in the paper); there is no blueprint node.
-/

@[expose] public section

open AlgebraicGeometry IsLocalRing CategoryTheory CategoryTheory.Limits

namespace Hironaka

universe u

noncomputable section

namespace AB

section Succession

variable {X Y Z W : Scheme.{u}}

/-- Appending the empty succession does nothing (formalization infrastructure for p. 310). -/
theorem succession_append_nil (g : MonoidalSuccession X Y) :
    g.append (MonoidalSuccession.nil Y) = g := by
  induction g with
  | nil X => rfl
  | cons B t rest ih => exact congrArg (MonoidalSuccession.cons B t) ih

/-- Concatenation of successions is associative (formalization infrastructure for p. 310). -/
theorem succession_append_assoc (g : MonoidalSuccession X Y) (h : MonoidalSuccession Y Z)
    (e : MonoidalSuccession Z W) : (g.append h).append e = g.append (h.append e) := by
  induction g with
  | nil X => rfl
  | cons B t rest ih => exact congrArg (MonoidalSuccession.cons B t) (ih h)

/-- Appending `cons B t e` is appending the one-step succession `cons B t nil` and then `e`
(formalization infrastructure for p. 310). -/
theorem succession_append_cons_eq_append_cons_nil_append (g : MonoidalSuccession X Y)
    {B : Subscheme Y} (t : MonoidalTransformation Y B) (e : MonoidalSuccession t.X' Z) :
    g.append (MonoidalSuccession.cons B t e) =
      (g.append (MonoidalSuccession.cons B t (MonoidalSuccession.nil t.X'))).append e :=
  (succession_append_assoc g (MonoidalSuccession.cons B t (MonoidalSuccession.nil t.X')) e).symm

end Succession

section OpenAlong

variable {N n : ℕ} {X : Scheme.{u}} {ℜ : DatumI.Raw X} {P : DatumI.Presentation ℜ}
  {r : Restriction X}

/-- The state obtained by folding a prepared permissible succession `g` with `x_0` in the image of
`S` has an open set `X̂*'` (formalization infrastructure for p. 310): `g` is the initial segment of
a standing tower (`exists_standing_prepHyp_of_prepHypSucc`), and
`Frame.isOpen_xHatPrimeStar_fold_initial` applies. -/
theorem StageState.isOpen_fold_initial_of_isPrepared [Hironaka.HironakaCitedResults.{u}]
    (hNn : n < N) (hX : IsAmbient X N) (hℜ : ℜ.IsDatum) (hr : r.IsFor ℜ)
    (hn : ℜ.n = (n : WithBot ℕ∞)) {x₀ : X} (hx₀ : X.IsSimpleAt x₀)
    [IsRegularLocalRing (Shat X x₀)] (z : Shat X x₀) (b : ℕ) (Jgen : Set (Shat X x₀))
    (fr : FrameSpec x₀ hx₀ ℜ r z b Jgen)
    {Y : Scheme.{u}} (g : MonoidalSuccession X Y) (hg : r.IsPermissibleSucc g ℜ)
    (hp : IsPrepared N P r g)
    (hx : x₀ ∈ g.composite.base '' S (g.transformI ℜ) (r.transformSucc g)) :
    IsOpen (StageState.fold b g (StageState.initial P.E hx₀ z Jgen)).xHatPrimeStar := by
  have hprep : PrepHypSucc N ℜ P r g x₀ :=
    ⟨hp.1.1, hp.1.2, fun U hU W₁ hW₁ i => hp.2 i U hU W₁ hW₁, hx⟩
  obtain ⟨T, m, h, hpre, -, hS, -⟩ := exists_standing_prepHyp_of_prepHypSucc P hNn hX hℜ hn hr g
    hg hprep
  exact Frame.isOpen_xHatPrimeStar_fold_initial hS fr g m h hpre

end OpenAlong

/-- **Openness of `X̂*'` along an extension** (formalization infrastructure for p. 310, "by
replacing the original succession `g_s : X_s → X` by one that includes the above succession"):
for a prepared succession `g` and a permissible extension `g ++ e` with `x_0` still in the image of
`S`, all the states `fold (g ++ e_j)` along `e` have an open set `X̂*'`. -/
theorem StageState.openAlong_fold_initial_of_isPermissibleSucc [Hironaka.HironakaCitedResults.{u}]
    {N n : ℕ} (hNn : n < N) {X : Scheme.{u}} (hX : IsAmbient X N) {ℜ : DatumI.Raw X}
    (hℜ : ℜ.IsDatum) (P : DatumI.Presentation ℜ) (r : Restriction X) (hr : r.IsFor ℜ)
    (hn : ℜ.n = (n : WithBot ℕ∞)) {x₀ : X} (hx₀ : X.IsSimpleAt x₀)
    [IsRegularLocalRing (Shat X x₀)] (z : Shat X x₀) (b : ℕ) (Jgen : Set (Shat X x₀))
    (fr : FrameSpec x₀ hx₀ ℜ r z b Jgen)
    {Y Z : Scheme.{u}} (g : MonoidalSuccession X Y) (e : MonoidalSuccession Y Z)
    (hge : r.IsPermissibleSucc (g.append e) ℜ)
    (hfin : HasFiniteImageOfDimEq N ℜ r g) (hbd : HasPreparedBoundary P r g)
    (hx : x₀ ∈ (g.append e).composite.base ''
      S ((g.append e).transformI ℜ) (r.transformSucc (g.append e))) :
    (StageState.fold b g (StageState.initial P.E hx₀ z Jgen)).OpenAlong b e := by
  have hgood : IsGoodDatumI N n X ℜ := ⟨hX, hℜ, hn.le⟩
  have key : ∀ {Y Z : Scheme.{u}} (e : MonoidalSuccession Y Z) (g : MonoidalSuccession X Y),
      r.IsPermissibleSucc (g.append e) ℜ → IsPrepared N P r g →
      x₀ ∈ (g.append e).composite.base ''
        S ((g.append e).transformI ℜ) (r.transformSucc (g.append e)) →
      (StageState.fold b g (StageState.initial P.E hx₀ z Jgen)).OpenAlong b e := by
    intro Y Z e
    induction e with
    | nil Y' =>
      intro g hge hp hx
      rw [succession_append_nil] at hge hx
      exact StageState.isOpen_fold_initial_of_isPrepared hNn hX hℜ hr hn hx₀ z b Jgen fr g hge hp hx
    | cons C t rest ih =>
      intro g hge hp hx
      refine ⟨?_, ?_⟩
      · obtain ⟨hg1, -⟩ := (Restriction.isPermissibleSucc_append r g _ ℜ).mp hge
        exact StageState.isOpen_fold_initial_of_isPrepared hNn hX hℜ hr hn hx₀ z b Jgen fr g hg1
          hp (image_S_append_subset g _ hgood hr hge hx)
      · have heq := succession_append_cons_eq_append_cons_nil_append g t rest
        have hge' : r.IsPermissibleSucc
            ((g.append (MonoidalSuccession.cons C t (MonoidalSuccession.nil t.X'))).append rest)
            ℜ := by
          rw [← heq]; exact hge
        have hx' : x₀ ∈
            ((g.append (MonoidalSuccession.cons C t (MonoidalSuccession.nil t.X'))).append
              rest).composite.base ''
            S (((g.append (MonoidalSuccession.cons C t (MonoidalSuccession.nil t.X'))).append
              rest).transformI ℜ)
              (r.transformSucc ((g.append (MonoidalSuccession.cons C t
                (MonoidalSuccession.nil t.X'))).append rest)) := by
          rw [← heq]; exact hx
        obtain ⟨hg2, -⟩ := (Restriction.isPermissibleSucc_append r _ rest ℜ).mp hge'
        have hstep : (StageState.fold b g (StageState.initial P.E hx₀ z Jgen)).step b t =
            StageState.fold b (g.append (MonoidalSuccession.cons C t
              (MonoidalSuccession.nil t.X'))) (StageState.initial P.E hx₀ z Jgen) := by
          rw [StageState.fold_append]
          rfl
        rw [hstep]
        exact ih _ hge' (IsPrepared.append _ hgood hr hg2 hp) hx'
  exact key e g hge ⟨hfin, hbd⟩ hx

end AB

end

end Hironaka
