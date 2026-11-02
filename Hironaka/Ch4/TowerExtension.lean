/-
Copyright (c) 2026 Daattavya Aggarwal, Minhyong Kim, Oisin Kim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daattavya Aggarwal, Minhyong Kim, Oisin Kim
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Architect
public import Hironaka.Ch4.ImplicationsAB

/-!
# Ch. IV §3–§4 (pp. 295, 314–326): extending a finite succession to a tower

The tower `{f_s : X_{s+1} → X_s}_{s ≥ 0}` of Ch. IV §3 (`AB.Tower`) has an initial segment
`h_s = f_0 ∘ ⋯ ∘ f_{s-1}` (`AB.Tower.pre s`, a `MonoidalSuccession`).  This file collects the
tacit conversions between finite successions and towers that §4 needs, and that the proof of
Theorems A*, B* (§3) and C, D* (§4) share:

* `AB.Tower.empty`: the tower all of whose centers are empty (p. 295: "the monoidal
  transformation with the empty center is the identity isomorphism");
* `AB.Tower.cons`: the tower beginning with a monoidal transformation `t` and continuing with a
  tower of `t.X'`; `AB.Tower.pre_cons` computes its initial segments;
* `AB.Tower.exists_pre_eq_of_succession`: every finite succession is the initial segment `g_n`
  of a tower whose centers are empty from stage `n` on;
* `AB.Tower.exists_pre_heq_and_monoidalTransformation_heq`: the same for `g` followed by one more
  monoidal transformation `t` (the center `B_n` of the tower is the center of `t`), the extension
  of `h_s` by `f_s` of p. 322;
* `AB.Tower.length_pre`, `MonoidalSuccession.length_snoc`: the initial segment `h_n` has length `n`.

The block lives in this file so that the A*/B* assembly (`TheoremsAStarBStar.lean`) can use it
without importing `Ch4/ImplicationsCD.lean`.
-/

@[expose] public section

open AlgebraicGeometry IsLocalRing CategoryTheory CategoryTheory.Limits

namespace Hironaka

universe u

noncomputable section

namespace AB
namespace Tower

/-- An isomorphism is the monoidal transformation with empty center (p. 295). -/
theorem isMonoidalTransformationOf_empty_of_isIso {X X' : Scheme.{u}} (f : X' ⟶ X) [IsIso f] :
    IsMonoidalTransformationOf f (Subscheme.empty : Subscheme X) :=
  ⟨by rw [Subscheme.totalTransform_empty]; exact Subscheme.isInvertibleIdeal_empty,
    fun X'' f' _ => ⟨f' ≫ inv f, by simp, fun h hh => by rw [← hh]; simp⟩⟩

/-- The tower all of whose centers are empty (all `f_s` are identities). -/
noncomputable def empty (X : Scheme.{u}) : Tower X where
  xSucc := fun _ => X
  B := fun _ => Subscheme.empty
  f := fun s => match s with
    | 0 => 𝟙 X
    | _ + 1 => 𝟙 X
  isMonoidal := fun s => by
    cases s with
    | zero => exact isMonoidalTransformationOf_empty_of_isIso (𝟙 X)
    | succ s => exact isMonoidalTransformationOf_empty_of_isIso (𝟙 X)

/-- The tower starting with the monoidal transformation `t` with center `B` and continuing with
the tower `T'` of `X_1 = t.X'`. -/
noncomputable def cons {X : Scheme.{u}} {B : Subscheme X} (t : MonoidalTransformation X B)
    (T' : Tower t.X') : Tower X where
  xSucc := fun s => T'.X s
  B := fun s => match s with
    | 0 => B
    | s + 1 => T'.B s
  f := fun s => match s with
    | 0 => t.f
    | s + 1 => T'.f s
  isMonoidal := fun s => by
    cases s with
    | zero => exact ⟨t.invertible, t.universal⟩
    | succ s => exact T'.isMonoidal s

/-- The initial segments of `Tower.cons t T'`: `g_{k+1} = (t, g'_k)`. -/
theorem pre_cons {X : Scheme.{u}} {B : Subscheme X} (t : MonoidalTransformation X B)
    (T' : Tower t.X') (k : ℕ) :
    (cons t T').pre (k + 1) = MonoidalSuccession.cons B t (T'.pre k) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    show MonoidalSuccession.snoc ((cons t T').pre (k + 1)) (T'.B k) (T'.monoidalTransformation k) =
      MonoidalSuccession.cons B t (MonoidalSuccession.snoc (T'.pre k) (T'.B k)
        (T'.monoidalTransformation k))
    rw [ih]
    rfl

/-- Not in the paper (tacit): a finite succession `g` of monoidal transformations is the initial
segment `g_n` of a tower `{f_s : X_{s+1} → X_s}_{s ≥ 0}` whose centers are empty from stage `n`
on (p. 295: "the monoidal transformation with the empty center is the identity isomorphism"). -/
theorem exists_pre_eq_of_succession {X Y : Scheme.{u}} (g : MonoidalSuccession X Y) :
    ∃ (T : Tower X) (n : ℕ) (h : T.X n = Y), h ▸ T.pre n = g ∧
      ∀ s, n ≤ s → T.B s = Subscheme.empty := by
  induction g with
  | nil X => exact ⟨empty X, 0, rfl, rfl, fun s _ => rfl⟩
  | cons B t rest ih =>
    obtain ⟨T', n', h', hpre', hB'⟩ := ih
    refine ⟨cons t T', n' + 1, h', ?_, ?_⟩
    · subst h'
      subst hpre'
      exact pre_cons t T' n'
    · intro s hs
      obtain ⟨s', rfl⟩ : ∃ s', s = s' + 1 := ⟨s - 1, by omega⟩
      exact hB' s' (by omega)

/-- Not in the paper (tacit): a finite succession `g` followed by one more monoidal transformation
`t` (with center `B`) is the initial segment of a tower whose centers are empty from the next
stage on, and whose `n`-th initial segment is `g` and whose `n`-th monoidal transformation is `t`
(p. 322: "we extend the permissible succession `h_s` to include the monoidal transformation
`f_s` of `X_s` with center `B`").  The conclusions are `HEq`s, so that the statement does not
mention a cast; after `subst` of the first one (`T.X n = Y`) they become equalities. -/
theorem exists_pre_heq_and_monoidalTransformation_heq {X Y : Scheme.{u}}
    (g : MonoidalSuccession X Y) {B : Subscheme Y} (t : MonoidalTransformation Y B) :
    ∃ (T : Tower X) (n : ℕ) (_ : T.X n = Y), HEq (T.pre n) g ∧ HEq (T.B n) B ∧
      HEq (T.monoidalTransformation n) t ∧ ∀ s, n + 1 ≤ s → T.B s = Subscheme.empty := by
  induction g with
  | nil X =>
    refine ⟨cons t (empty t.X'), 0, rfl, HEq.rfl, HEq.rfl, HEq.rfl, fun s hs => ?_⟩
    obtain ⟨s', rfl⟩ : ∃ s', s = s' + 1 := ⟨s - 1, by omega⟩
    rfl
  | cons B' t' rest ih =>
    obtain ⟨T', n', h', hpre', hB', hmt', hT'⟩ := ih t
    refine ⟨cons t' T', n' + 1, h', ?_, hB', ?_, ?_⟩
    · subst h'
      have := eq_of_heq hpre'
      subst this
      exact heq_of_eq (pre_cons t' T' n')
    · exact hmt'
    · intro s hs
      obtain ⟨s', rfl⟩ : ∃ s', s = s' + 1 := ⟨s - 1, by omega⟩
      exact hT' s' (by omega)

end Tower
end AB

namespace MonoidalSuccession

theorem length_snoc {X Y : Scheme.{u}} (g : MonoidalSuccession X Y) {B : Subscheme Y}
    (t : MonoidalTransformation Y B) : (g.snoc B t).length = g.length + 1 := by
  induction g with
  | nil X => rfl
  | cons B' t' rest ih => exact congrArg (· + 1) (ih t)

end MonoidalSuccession

namespace AB
namespace Tower

/-- The initial segment `h_n` of a tower is a succession of length `n`. -/
theorem length_pre {X : Scheme.{u}} (T : Tower X) (n : ℕ) : (T.pre n).length = n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    show (MonoidalSuccession.snoc (T.pre n) (T.B n) (T.monoidalTransformation n)).length = n + 1
    rw [MonoidalSuccession.length_snoc, ih]

end Tower
end AB

end

end Hironaka
