/-
Copyright (c) 2026 Daattavya Aggarwal, Minhyong Kim, Oisin Kim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daattavya Aggarwal, Minhyong Kim, Oisin Kim
-/
module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Basic
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Architect
public import Hironaka.Compat.DatumPresentation
public import Hironaka.Compat.ResolvableData

/-!
# The split of the auxiliary datum `ℜ^{N-1}_II` (repair of the second error of Ch. IV §3–§4)

> In both cases, we see that `Ẽ_1, …, Ẽ_α̃` are non-singular irreducible subschemes of `X̄'_s` of
> codimension 1, and that `Ẽ_1 ∪ ⋯ ∪ Ẽ_α̃` has only normal crossings on `X̄'_s`.  (p. 308)
>
> Thus, applying Theorem `II₂^{N-1}` to the resolution datum `ℜ^{N-1}_II` on `X̃` (without
> restriction), we can prove that there exists a finite permissible succession of monoidal
> transformations of `X_s` for `ℜ(s)`, which induces a permissible succession of monoidal
> transformations of `X̃` for `ℜ^{N-1}_II` and which resolve the datum `ℜ^{N-1}_II`.  (p. 310)

The `Ẽ_j` need not be irreducible, and `Ẽ_i = X̃` when `F = E_i`.
This file is the generic part of the repair.  Nothing here mentions the frame `X̂_s ⊇ X̄_s ⊇ X̃`.

* **The split.**  `DatumII.Raw.IsRefinement ℜ' ℜ π`: `ℜ'` is obtained from `ℜ` by replacing every
  `E_i` by the pieces `E'_k`, `π k = i`, which are pairwise disjoint and whose union is `E_i`,
  with the same exponent, `J` and `b`.  It preserves `S`, `ν`, `S*`, resolvedness and
  permissibility, and is preserved by the transform of Definition 7 (II) along an arbitrary centre
  (`IsRefinement.transform`), hence along permissible successions
  (`Refines.isPermissibleII_transformII`).  Every *weak* datum (`DatumII.Raw.IsWeakDatum`: the `E_i`
  non-singular and everywhere of codimension one, but possibly reducible) is refined by a datum
  (`exists_isDatum_refines`: split each `E_i` into its connected components), so Theorem `II₂^M`
  gives `Resolvable` for weak data (`resolvable_of_isWeakDatum`).
* **The drop.**  An entry `Ẽ_j = X̃` (the zero ideal sheaf; it occurs for the component `E_i = F`)
  is replaced by the empty subscheme (`Subscheme.emptyIfBot`, `DatumII.Raw.emptyIfBot`); the paper
  allows empty entries (p. 165).  The operation commutes with the transform
  (`DatumII.Raw.emptyIfBot_transform`, and `emptyIfBot_transform_of_isPermissible` for a weak
  datum and a permissible centre); a datum with its whole-space entries emptied is a weak datum as
  soon as the other entries are non-singular divisors with only normal crossings
  (`DatumII.Raw.isWeakDatum_emptyIfBot`).
* **Stability.**  A permissible transform of a weak datum is a weak datum
  (`DatumII.Raw.IsWeakDatum.transform`), so the induction along a resolving succession needs the
  datum property only at its start.

The non-singular-divisor versions of the stalk lemmas of Remark 1
(`exists_rsop_adapted_of_isNonsingularDivisor`) are in `Compat/ExceptionalTransversal.lean`.

Not in the paper: the paper asserts that `ℜ^{N-1}_II` is a resolution datum.
-/

@[expose] public section

open Classical AlgebraicGeometry

namespace Hironaka

universe u

/-! ### The empty subscheme in place of the whole space -/

namespace Subscheme

variable {X : Scheme.{u}}

/-- The whole space (zero ideal sheaf) is replaced by the empty subscheme (unit ideal sheaf);
every other subscheme is unchanged.  The paper allows the empty subscheme among the `E_i`
(p. 165). -/
noncomputable def emptyIfBot (E : Subscheme X) : Subscheme X := if E = ⊥ then ⊤ else E

/-- A subscheme other than the whole space is unchanged by `emptyIfBot`. -/
theorem emptyIfBot_of_ne_bot {E : Subscheme X} (h : E ≠ ⊥) : E.emptyIfBot = E := by
  simp [emptyIfBot, h]

/-- The whole space becomes the empty subscheme. -/
theorem emptyIfBot_of_eq_bot {E : Subscheme X} (h : E = ⊥) : E.emptyIfBot = ⊤ := by
  simp [emptyIfBot, h]

/-- `emptyIfBot` of the whole space is the empty subscheme. -/
@[simp] theorem emptyIfBot_bot : (⊥ : Subscheme X).emptyIfBot = ⊤ :=
  emptyIfBot_of_eq_bot rfl

/-- The empty subscheme is unchanged by `emptyIfBot`. -/
@[simp] theorem emptyIfBot_top : (⊤ : Subscheme X).emptyIfBot = ⊤ := by
  by_cases h : (⊤ : Subscheme X) = ⊥
  · simp [emptyIfBot, h]
  · exact emptyIfBot_of_ne_bot h

/-- The emptied whole space has no points. -/
theorem pts_emptyIfBot_eq_empty {E : Subscheme X} (h : E = ⊥) : E.emptyIfBot.pts = ∅ := by
  rw [emptyIfBot_of_eq_bot h]
  exact DatumTransform.pts_empty

/-- `emptyIfBot` does not change the points of a subscheme other than the whole space. -/
theorem pts_emptyIfBot_of_ne_bot {E : Subscheme X} (h : E ≠ ⊥) :
    E.emptyIfBot.pts = E.pts := by
  rw [emptyIfBot_of_ne_bot h]

/-- A non-singular divisor on a non-empty scheme is not the whole space: at a point of the whole
space the ideal `(0)` has height `0`, not `1`. -/
theorem IsNonsingularDivisor.ne_bot [Nonempty X] {E : Subscheme X}
    (h : E.IsNonsingularDivisor) : E ≠ ⊥ := by
  intro hE
  obtain ⟨x⟩ := ‹Nonempty X›
  have hx : x ∈ E.pts := by
    rw [mem_pts_iff_stalkIdeal_ne_top, hE, stalkIdeal_bot_eq]
    exact bot_ne_top
  have h1 := h.2 x hx
  unfold codimAt at h1
  rw [hE, stalkIdeal_bot_eq, Ideal.height_bot] at h1
  exact absurd h1 (by norm_num)

/-- A subscheme which near every point of its support agrees with a non-singular divisor is a
non-singular divisor. -/
theorem isNonsingularDivisor_of_forall_stalkIdeal_eq {D : Subscheme X}
    (h : ∀ z ∈ D.pts, ∃ D' : Subscheme X, D'.IsNonsingularDivisor ∧
      D'.stalkIdeal z = D.stalkIdeal z) : D.IsNonsingularDivisor := by
  have hreg : ∀ z ∈ D.pts, IsRegularLocalRing (X.presheaf.stalk z ⧸ D.stalkIdeal z) := by
    intro z hz
    obtain ⟨D', ⟨hns, -⟩, heq⟩ := h z hz
    have hz' : z ∈ D'.pts := by
      rw [Subscheme.mem_pts_iff_stalkIdeal_ne_top, heq]
      exact Subscheme.mem_pts_iff_stalkIdeal_ne_top.mp hz
    have := Subscheme.isRegular_stalk_quot D' hns hz'
    rwa [heq] at this
  refine ⟨Subscheme.isNonsingular_of_stalk_quot D hreg, fun z hz => ?_⟩
  obtain ⟨D', ⟨hns, hcod⟩, heq⟩ := h z hz
  have hz' : z ∈ D'.pts := by
    rw [Subscheme.mem_pts_iff_stalkIdeal_ne_top, heq]
    exact Subscheme.mem_pts_iff_stalkIdeal_ne_top.mp hz
  have h1 := hcod z hz'
  unfold Subscheme.codimAt at h1 ⊢
  rwa [heq] at h1

/-- A non-singular irreducible subscheme of codimension one (or the empty one) is unchanged by
`emptyIfBot`: on a non-empty scheme it is a non-singular divisor, hence not the whole space. -/
theorem emptyIfBot_eq_self_of_isNonsingularIrreducibleCodimOne {E : Subscheme X}
    (h : E.IsNonsingularIrreducibleCodimOne) : E.emptyIfBot = E := by
  have hd := IsNonsingularIrreducibleCodimOne.isNonsingularDivisor h
  rcases h with h0 | ⟨-, hirr, -⟩
  · rw [h0]
    exact emptyIfBot_top
  · by_cases hE : E = ⊥
    · exfalso
      have : IrreducibleSpace E.toScheme := hirr
      have : Nonempty X := ⟨E.ι (Classical.arbitrary E.toScheme)⟩
      exact hd.ne_bot hE
    · exact emptyIfBot_of_ne_bot hE

/-- A finite union of non-singular subschemes, indexed by any finite type, is reduced
(`Subscheme.isReduced_iInf_of_isNonsingular` for `Fin α`-indexed families). -/
theorem isReduced_iInf_of_forall_isNonsingular {ι : Type*} [Fintype ι] (E : ι → Subscheme X)
    (h : ∀ i, (E i).IsNonsingular) : (⨅ i, E i).IsReduced := by
  refine Subscheme.isReduced_of_isRadical_stalkIdeal fun z => ?_
  rw [DatumTransform.stalkIdeal_iInf_fintype]
  refine Ideal.isRadical_iInf _ fun i => ?_
  by_cases hz : z ∈ (E i).pts
  · exact (Subscheme.isPrime_stalkIdeal_of_isNonsingular_of_mem_pts (E i) (h i) hz).isRadical
  · rw [Subscheme.stalkIdeal_eq_top_of_notMem_pts hz]
    exact (show (⊤ : Ideal (X.presheaf.stalk z)).IsRadical from fun _ _ => Submodule.mem_top)

/-- The union of the emptied members is the union of the members other than the whole space. -/
theorem iInf_emptyIfBot_eq {ι : Type*} (E : ι → Subscheme X) :
    (⨅ i, (E i).emptyIfBot) = ⨅ i : {i // E i ≠ ⊥}, E i.1 := by
  refine le_antisymm (le_iInf fun i => ?_) (le_iInf fun j => ?_)
  · exact (iInf_le _ i.1).trans (emptyIfBot_of_ne_bot i.2).le
  · by_cases hj : E j = ⊥
    · rw [emptyIfBot_of_eq_bot hj]
      exact le_top
    · rw [emptyIfBot_of_ne_bot hj]
      exact iInf_le (fun i : {i // E i ≠ ⊥} => E i.1) ⟨j, hj⟩

/-- An entry whose emptying is a non-singular divisor is the whole space or a non-singular
divisor. -/
theorem eq_bot_or_isNonsingularDivisor_of_emptyIfBot {E : Subscheme X}
    (h : E.emptyIfBot.IsNonsingularDivisor) : E = ⊥ ∨ E.IsNonsingularDivisor := by
  by_cases hE : E = ⊥
  · exact Or.inl hE
  · exact Or.inr (by rwa [emptyIfBot_of_ne_bot hE] at h)

end Subscheme

/-! ### Strict transforms of disjoint unions -/

namespace MonoidalTransformation

variable {X : Scheme.{u}} {B : Subscheme X}

/-- The stalks of the strict transforms of two subschemes with the same stalk at `f(y)` agree
at `y`. -/
theorem stalkIdeal_strictTransform_congr (t : MonoidalTransformation X B) {D D' : Subscheme X}
    (y : t.X') (h : D.stalkIdeal (t.f y) = D'.stalkIdeal (t.f y)) :
    (Subscheme.strictTransform t D).stalkIdeal y =
      (Subscheme.strictTransform t D').stalkIdeal y := by
  rw [Subscheme.strictTransform_stalkIdeal, Subscheme.strictTransform_stalkIdeal,
    stalkIdeal_totalTransform, stalkIdeal_totalTransform, h]

/-- The strict transform of a subscheme missing `f(y)` misses `y`. -/
theorem stalkIdeal_strictTransform_eq_top (t : MonoidalTransformation X B) {D : Subscheme X}
    (y : t.X') (h : D.stalkIdeal (t.f y) = ⊤) :
    (Subscheme.strictTransform t D).stalkIdeal y = ⊤ := by
  rw [Subscheme.strictTransform_stalkIdeal, stalkIdeal_totalTransform, h, Ideal.map_top]
  refine eq_top_iff.mpr (le_trans ?_ (le_iSup _ 0))
  simp only [pow_zero, Ideal.one_eq_top, Submodule.top_coe, Submodule.colon_univ, le_refl]

/-- The strict transform of a union of pairwise disjoint subschemes is the union of the strict
transforms (on stalks): at a point `y` only the member through `f(y)` has a proper stalk. -/
theorem stalkIdeal_strictTransform_iInf_of_disjoint (t : MonoidalTransformation X B)
    {ι : Type*} [Fintype ι] (E : ι → Subscheme X)
    (hdisj : ∀ i j, i ≠ j → Disjoint (E i).pts (E j).pts) (y : t.X') :
    (Subscheme.strictTransform t (⨅ i, E i)).stalkIdeal y =
      ⨅ i, (Subscheme.strictTransform t (E i)).stalkIdeal y := by
  by_cases hk : ∃ k, t.f y ∈ (E k).pts
  · obtain ⟨k, hk⟩ := hk
    have hother : ∀ i, i ≠ k → (E i).stalkIdeal (t.f y) = ⊤ := fun i hi =>
      Subscheme.stalkIdeal_eq_top_of_notMem_pts fun h =>
        Set.disjoint_left.mp (hdisj i k hi) h hk
    have h1 : (⨅ i, E i).stalkIdeal (t.f y) = (E k).stalkIdeal (t.f y) := by
      rw [DatumTransform.stalkIdeal_iInf_fintype]
      refine le_antisymm (iInf_le _ k) (le_iInf fun i => ?_)
      by_cases hi : i = k
      · subst hi; exact le_rfl
      · rw [hother i hi]; exact le_top
    rw [stalkIdeal_strictTransform_congr t y h1]
    refine le_antisymm (le_iInf fun i => ?_) (iInf_le _ k)
    by_cases hi : i = k
    · subst hi; exact le_rfl
    · rw [stalkIdeal_strictTransform_eq_top t y (hother i hi)]; exact le_top
  · push Not at hk
    have hall : ∀ i, (E i).stalkIdeal (t.f y) = ⊤ := fun i =>
      Subscheme.stalkIdeal_eq_top_of_notMem_pts (hk i)
    have h1 : (⨅ i, E i).stalkIdeal (t.f y) = ⊤ := by
      rw [DatumTransform.stalkIdeal_iInf_fintype]
      exact iInf_eq_top.mpr hall
    rw [stalkIdeal_strictTransform_eq_top t y h1]
    exact (iInf_eq_top.mpr fun i => stalkIdeal_strictTransform_eq_top t y (hall i)).symm

/-- The strict transform of the whole space is the whole space: the exceptional ideal is locally
generated by a non-zero-divisor. -/
theorem strictTransform_bot (t : MonoidalTransformation X B) :
    Subscheme.strictTransform t (⊥ : Subscheme X) = ⊥ := by
  refine Subscheme.ext_stalkIdeal fun y => ?_
  obtain ⟨g, hg, hnzd⟩ := t.invertible.exists_stalkIdeal_eq_span y
  have hg' : t.exceptional.stalkIdeal y = Ideal.span {g} := hg
  rw [Subscheme.strictTransform_stalkIdeal, stalkIdeal_totalTransform,
    Subscheme.stalkIdeal_bot_eq, Ideal.map_bot, hg', Subscheme.stalkIdeal_bot_eq]
  refine le_antisymm (iSup_le fun n => fun r hr => ?_) bot_le
  have hmem := Submodule.mem_colon.mp hr (g ^ n)
    (by rw [Ideal.span_singleton_pow]; exact Ideal.mem_span_singleton_self _)
  simp only [Ideal.mem_bot, smul_eq_mul] at hmem ⊢
  exact (mem_nonZeroDivisors_iff.mp (pow_mem hnzd n)).2 r hmem

/-- The strict transform of the empty subscheme is empty. -/
theorem strictTransform_top (t : MonoidalTransformation X B) :
    Subscheme.strictTransform t (⊤ : Subscheme X) = ⊤ :=
  Subscheme.ext_stalkIdeal fun y => by
    rw [Subscheme.stalkIdeal_top_eq]
    exact stalkIdeal_strictTransform_eq_top t y (Subscheme.stalkIdeal_top_eq _)

/-- On a non-empty scheme the exceptional divisor is not the whole space. -/
theorem exceptional_ne_bot (t : MonoidalTransformation X B) [Nonempty t.X'] :
    t.exceptional ≠ ⊥ := by
  intro h
  obtain ⟨y⟩ := ‹Nonempty t.X'›
  obtain ⟨g, hg, hnzd⟩ := t.invertible.exists_stalkIdeal_eq_span y
  have hg' : t.exceptional.stalkIdeal y = Ideal.span {g} := hg
  rw [h, Subscheme.stalkIdeal_bot_eq] at hg'
  have : g = 0 := by
    have := Ideal.mem_span_singleton_self g
    rw [← hg'] at this
    exact this
  rw [this] at hnzd
  exact zero_notMem_nonZeroDivisors hnzd

end MonoidalTransformation

/-! ### The refinement relation -/

namespace DatumII.Raw

variable {X : Scheme.{u}}

/-- `ℜ'` *refines* `ℜ` along `π`: same `J` and `b`; for each `i` the stalk of `E_i` at every point
is the intersection of the stalks of the pieces `E'_k`, `π k = i` (so `E_i` is the union of its
pieces; `E_i` without a piece is empty); the pieces of one `E_i` are pairwise disjoint; and the
exponents agree on the non-empty pieces.  This is "split each `Ẽ_j` into its connected components,
with the same exponent" (the repair of the paper's error on the subschemes `Ẽ_j`, p. 308). -/
structure IsRefinement (ℜ' ℜ : Raw X) (π : Fin ℜ'.α → Fin ℜ.α) : Prop where
  b_eq : ℜ'.b = ℜ.b
  J_eq : ℜ'.J = ℜ.J
  stalkIdeal_eq : ∀ (i : Fin ℜ.α) (x : X),
    (ℜ.E i).stalkIdeal x = ⨅ k : {i' : Fin ℜ'.α // π i' = i}, (ℜ'.E k).stalkIdeal x
  disjoint : ∀ i' j' : Fin ℜ'.α, i' ≠ j' → π i' = π j' → Disjoint (ℜ'.E i').pts (ℜ'.E j').pts
  a_eq : ∀ i' : Fin ℜ'.α, (ℜ'.E i').pts.Nonempty → ℜ'.a i' = ℜ.a (π i')

/-- `ℜ'` refines `ℜ` (along some map of indices). -/
def Refines (ℜ' ℜ : Raw X) : Prop := ∃ π, IsRefinement ℜ' ℜ π

namespace IsRefinement

variable {ℜ' ℜ : Raw X} {π : Fin ℜ'.α → Fin ℜ.α} (h : IsRefinement ℜ' ℜ π)
include h

/-- A point lies on `E_i` iff it lies on a piece of `E_i`. -/
theorem mem_pts_iff (i : Fin ℜ.α) (x : X) :
    x ∈ (ℜ.E i).pts ↔ ∃ k : Fin ℜ'.α, π k = i ∧ x ∈ (ℜ'.E k).pts := by
  rw [Subscheme.mem_pts_iff_stalkIdeal_ne_top, h.stalkIdeal_eq i x, Ne, iInf_eq_top]
  push Not
  constructor
  · rintro ⟨k, hk⟩
    exact ⟨k.1, k.2, Subscheme.mem_pts_iff_stalkIdeal_ne_top.mpr hk⟩
  · rintro ⟨k, hk, hx⟩
    exact ⟨⟨k, hk⟩, Subscheme.mem_pts_iff_stalkIdeal_ne_top.mp hx⟩

/-- `E_i` is the union of its pieces, as sets of points. -/
theorem pts_eq (i : Fin ℜ.α) :
    (ℜ.E i).pts = ⋃ k : {i' : Fin ℜ'.α // π i' = i}, (ℜ'.E k).pts := by
  ext x
  rw [h.mem_pts_iff i x, Set.mem_iUnion]
  constructor
  · rintro ⟨k, hk, hx⟩
    exact ⟨⟨k, hk⟩, hx⟩
  · rintro ⟨k, hx⟩
    exact ⟨k.1, k.2, hx⟩

/-- The unions `E_1 ∪ ⋯ ∪ E_α` of a refinement and of the refined datum coincide (the notion of
normal crossings sees only the union). -/
theorem eUnion_eq : ℜ'.eUnion = ℜ.eUnion := by
  refine Subscheme.ext_stalkIdeal fun x => ?_
  unfold DatumII.Raw.eUnion
  rw [DatumTransform.stalkIdeal_iInf_fintype, DatumTransform.stalkIdeal_iInf_fintype]
  simp only [h.stalkIdeal_eq]
  have e1 : ⨅ k : Fin ℜ'.α, (ℜ'.E k).stalkIdeal x =
      ⨅ p : (Σ i, {k : Fin ℜ'.α // π k = i}), (ℜ'.E p.2.1).stalkIdeal x :=
    (Equiv.iInf_comp (g := fun k => (ℜ'.E k).stalkIdeal x) (Equiv.sigmaFiberEquiv π)).symm
  rw [e1, iInf_sigma]

/-- A point lies on exactly one piece of `E_i` if it lies on `E_i`, and on none otherwise. -/
theorem card_fibre (i : Fin ℜ.α) (x : X) :
    (Finset.univ.filter fun i' : Fin ℜ'.α => x ∈ (ℜ'.E i').pts ∧ π i' = i).card =
      if x ∈ (ℜ.E i).pts then 1 else 0 := by
  split_ifs with hx
  · obtain ⟨k, hk, hxk⟩ := (h.mem_pts_iff i x).mp hx
    rw [Finset.card_eq_one]
    refine ⟨k, ?_⟩
    ext i'
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · rintro ⟨hx', hπ⟩
      by_contra hne
      exact Set.disjoint_left.mp (h.disjoint i' k hne (hπ.trans hk.symm)) hx' hxk
    · rintro rfl
      exact ⟨hxk, hk⟩
  · rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    rintro i' - ⟨hx', hπ⟩
    exact hx ((h.mem_pts_iff i x).mpr ⟨i', hπ, hx'⟩)

/-- The weights agree: a point lies on at most one piece of each `E_i`, and on one iff it lies on
`E_i`. -/
theorem weight_eq (x : X) : ℜ'.weight x = ℜ.weight x := by
  unfold DatumII.Raw.weight
  have h1 : ∑ i' ∈ Finset.univ.filter (fun i' => x ∈ (ℜ'.E i').pts), ℜ'.a i' =
      ∑ i' ∈ Finset.univ.filter (fun i' => x ∈ (ℜ'.E i').pts), ℜ.a (π i') := by
    refine Finset.sum_congr rfl fun i' hi' => ?_
    have hx : x ∈ (ℜ'.E i').pts := (Finset.mem_filter.mp hi').2
    exact h.a_eq i' ⟨x, hx⟩
  rw [h1, ← Finset.sum_fiberwise_of_maps_to
    (s := Finset.univ.filter (fun i' => x ∈ (ℜ'.E i').pts)) (t := Finset.univ) (g := π)
    (fun _ _ => Finset.mem_univ _), Finset.sum_filter]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hc : ∀ i' ∈ (Finset.univ.filter (fun i' : Fin ℜ'.α => x ∈ (ℜ'.E i').pts)).filter
      (fun i' => π i' = i), ℜ.a (π i') = ℜ.a i := fun i' hi' => by
    rw [(Finset.mem_filter.mp hi').2]
  rw [Finset.sum_congr rfl hc, Finset.sum_const, Finset.filter_filter, h.card_fibre i x]
  split_ifs <;> simp

/-- `ν(J_x)` is unchanged. -/
theorem nuAt_eq (x : X) : ℜ'.nuAt x = ℜ.nuAt x := by
  unfold DatumII.Raw.nuAt
  rw [h.J_eq]

/-- `S(ℜ') = S(ℜ)` (p. 165). -/
theorem S_eq : ℜ'.S = ℜ.S := by
  ext x
  show (ℜ'.b : ℕ∞) ≤ (ℜ'.weight x : ℕ∞) + ℜ'.nuAt x ↔ (ℜ.b : ℕ∞) ≤ (ℜ.weight x : ℕ∞) + ℜ.nuAt x
  rw [h.b_eq, h.weight_eq, h.nuAt_eq]

/-- `ν(ℜ') = ν(ℜ)` (p. 165). -/
theorem nu_eq : ℜ'.nu = ℜ.nu := by
  unfold DatumII.Raw.nu
  rw [h.S_eq]
  exact iSup_congr fun x => iSup_congr fun _ => h.nuAt_eq x

/-- `S_ν(ℜ') = S_ν(ℜ)`. -/
theorem sNu_eq (ν : ℕ∞) : ℜ'.sNu ν = ℜ.sNu ν := by
  ext x
  simp only [DatumII.Raw.sNu, Set.mem_ofPred_eq, h.S_eq, h.nuAt_eq]

/-- `S*(ℜ') = S*(ℜ)`. -/
theorem sStar_eq : ℜ'.sStar = ℜ.sStar := by
  unfold DatumII.Raw.sStar
  rw [h.nu_eq, h.sNu_eq]

/-- A centre is permissible (Definition 6) for `ℜ'` iff it is for `ℜ`: the conditions concern only
`S*` and the union. -/
theorem isPermissible_iff (B : Subscheme X) : ℜ'.IsPermissible B ↔ ℜ.IsPermissible B := by
  unfold DatumII.Raw.IsPermissible
  rw [h.sStar_eq, h.eUnion_eq]

/-- The stalk of `E_i` at `x` is `⊤` or the stalk of a piece of `E_i`. -/
theorem stalkIdeal_eq_top_or_exists (i : Fin ℜ.α) (x : X) :
    (ℜ.E i).stalkIdeal x = ⊤ ∨ ∃ k : Fin ℜ'.α, π k = i ∧
      (ℜ.E i).stalkIdeal x = (ℜ'.E k).stalkIdeal x := by
  by_cases hx : (ℜ.E i).stalkIdeal x = ⊤
  · exact Or.inl hx
  · right
    obtain ⟨k, hk, hxk⟩ := (h.mem_pts_iff i x).mp (Subscheme.mem_pts_iff_stalkIdeal_ne_top.mpr hx)
    refine ⟨k, hk, ?_⟩
    have hle : (⨅ k' : {i' : Fin ℜ'.α // π i' = i}, (ℜ'.E k').stalkIdeal x) ≤
        (ℜ'.E k).stalkIdeal x :=
      iInf_le (fun k' : {i' : Fin ℜ'.α // π i' = i} => (ℜ'.E k').stalkIdeal x) ⟨k, hk⟩
    have hge : (ℜ'.E k).stalkIdeal x ≤
        ⨅ k' : {i' : Fin ℜ'.α // π i' = i}, (ℜ'.E k').stalkIdeal x := by
      refine le_iInf fun k' => ?_
      by_cases hkk : k'.1 = k
      · rw [← hkk]
      · rw [Subscheme.stalkIdeal_eq_top_of_notMem_pts (fun hk' =>
          Set.disjoint_left.mp (h.disjoint k'.1 k hkk (k'.2.trans hk.symm)) hk' hxk)]
        exact le_top
    rw [h.stalkIdeal_eq i x]
    exact le_antisymm hle hge

/-- A reduced irreducible non-empty `B` lies in `E_i` iff it lies in exactly one piece of `E_i`
(an irreducible set contained in a finite union of closed sets lies in one of them). -/
theorem isContainedIn_iff_existsUnique {B : Subscheme X} (hBred : B.IsReduced)
    (hBirr : B.IsIrreducible) (hBne : B.pts.Nonempty) (i : Fin ℜ.α) :
    B.IsContainedIn (ℜ.E i) ↔ ∃! k : Fin ℜ'.α, π k = i ∧ B.IsContainedIn (ℜ'.E k) := by
  have hirr : _root_.IsIrreducible B.pts := Subscheme.isIrreducible_pts B hBirr
  constructor
  · intro hB
    have hsub : B.pts ⊆ (ℜ.E i).pts := pts_subset_of_isContainedIn hB
    obtain ⟨z, hz, hBz⟩ := (isIrreducible_iff_sUnion_isClosed.mp hirr)
      (Finset.univ.image fun k : {k : Fin ℜ'.α // π k = i} => (ℜ'.E k.1).pts)
      (by
        intro z hz
        obtain ⟨k, -, rfl⟩ := Finset.mem_image.mp hz
        exact (ℜ'.E k.1).support.isClosed)
      (by
        intro y hy
        obtain ⟨k, hk, hyk⟩ := (h.mem_pts_iff i y).mp (hsub hy)
        exact Set.mem_sUnion.mpr ⟨(ℜ'.E k).pts,
          Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨⟨k, hk⟩, Finset.mem_univ _, rfl⟩), hyk⟩)
    obtain ⟨k, -, rfl⟩ := Finset.mem_image.mp hz
    refine ⟨k.1, ⟨k.2, Subscheme.isContainedIn_of_pts_subset hBred hBz⟩, ?_⟩
    rintro k' ⟨hk', hBk'⟩
    by_contra hne
    obtain ⟨y, hy⟩ := hBne
    exact Set.disjoint_left.mp (h.disjoint k' k.1 hne (hk'.trans k.2.symm))
      (pts_subset_of_isContainedIn hBk' hy) (hBz hy)
  · rintro ⟨k, ⟨hk, hBk⟩, -⟩
    refine Subscheme.isContainedIn_of_pts_subset hBred fun y hy => ?_
    exact (h.mem_pts_iff i y).mpr ⟨k, hk, pts_subset_of_isContainedIn hBk hy⟩

/-- The exponent of the exceptional divisor agrees:
`∑_{B ⊆ E'_k} a'_k = ∑_{B ⊆ E_i} a_i` for a reduced irreducible non-empty `B`. -/
theorem sum_isContainedIn_eq {B : Subscheme X} (hBred : B.IsReduced)
    (hBirr : B.IsIrreducible) (hBne : B.pts.Nonempty) :
    ∑ i' ∈ Finset.univ.filter (fun i' => B.IsContainedIn (ℜ'.E i')), ℜ'.a i' =
      ∑ i ∈ Finset.univ.filter (fun i => B.IsContainedIn (ℜ.E i)), ℜ.a i := by
  have h1 : ∑ i' ∈ Finset.univ.filter (fun i' => B.IsContainedIn (ℜ'.E i')), ℜ'.a i' =
      ∑ i' ∈ Finset.univ.filter (fun i' => B.IsContainedIn (ℜ'.E i')), ℜ.a (π i') := by
    refine Finset.sum_congr rfl fun i' hi' => ?_
    have hB : B.IsContainedIn (ℜ'.E i') := (Finset.mem_filter.mp hi').2
    obtain ⟨y, hy⟩ := hBne
    exact h.a_eq i' ⟨y, pts_subset_of_isContainedIn hB hy⟩
  rw [h1, ← Finset.sum_fiberwise_of_maps_to
    (s := Finset.univ.filter (fun i' => B.IsContainedIn (ℜ'.E i'))) (t := Finset.univ) (g := π)
    (fun _ _ => Finset.mem_univ _), Finset.sum_filter]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hc : ∀ i' ∈ (Finset.univ.filter (fun i' : Fin ℜ'.α => B.IsContainedIn (ℜ'.E i'))).filter
      (fun i' => π i' = i), ℜ.a (π i') = ℜ.a i := fun i' hi' => by
    rw [(Finset.mem_filter.mp hi').2]
  rw [Finset.sum_congr rfl hc, Finset.sum_const, Finset.filter_filter]
  have hcard : (Finset.univ.filter fun i' : Fin ℜ'.α =>
      B.IsContainedIn (ℜ'.E i') ∧ π i' = i).card = if B.IsContainedIn (ℜ.E i) then 1 else 0 := by
    split_ifs with hB
    · obtain ⟨k, ⟨hk, hBk⟩, huniq⟩ := (h.isContainedIn_iff_existsUnique hBred hBirr hBne i).mp hB
      rw [Finset.card_eq_one]
      refine ⟨k, ?_⟩
      ext i'
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      exact ⟨fun hi' => huniq i' ⟨hi'.2, hi'.1⟩, fun hi' => hi' ▸ ⟨hBk, hk⟩⟩
    · rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      rintro i' - ⟨hB', hπ⟩
      exact hB ((h.isContainedIn_iff_existsUnique hBred hBirr hBne i).mpr
        ⟨i', ⟨hπ, hB'⟩, fun k' ⟨hk', hBk'⟩ => by
          by_contra hne
          obtain ⟨y, hy⟩ := hBne
          exact Set.disjoint_left.mp (h.disjoint k' i' hne (hk'.trans hπ.symm))
            (pts_subset_of_isContainedIn hBk' hy) (pts_subset_of_isContainedIn hB' hy)⟩)
  rw [hcard]
  split_ifs <;> simp

/-- **The transform preserves the refinement** (Definition 7 (II)): along a centre `B` (empty, or
non-singular and irreducible) the strict transforms of the pieces are the pieces of the strict
transform, the exceptional divisor is its own piece, and the new exponents agree.  For `B = ∅` the
printed formula for the exponent differs, but then the exceptional divisor is empty and the
exponent condition is void. -/
theorem transform {B : Subscheme X} (hB : B.IsCenter) (t : MonoidalTransformation X B) :
    IsRefinement (ℜ'.transform t) (ℜ.transform t)
      (Fin.snoc (α := fun _ => Fin (ℜ.α + 1)) (fun k => (π k).castSucc) (Fin.last ℜ.α)) := by
  have hπc : ∀ k : Fin ℜ'.α, (Fin.snoc (α := fun _ => Fin (ℜ.α + 1))
      (fun k => (π k).castSucc) (Fin.last ℜ.α) : Fin (ℜ'.α + 1) → Fin (ℜ.α + 1))
        (Fin.castSucc k) = Fin.castSucc (π k) := fun k => Fin.snoc_castSucc _ _ _
  have hπl : (Fin.snoc (α := fun _ => Fin (ℜ.α + 1))
      (fun k => (π k).castSucc) (Fin.last ℜ.α) : Fin (ℜ'.α + 1) → Fin (ℜ.α + 1))
        (Fin.last ℜ'.α) = Fin.last ℜ.α := Fin.snoc_last _ _
  refine ⟨h.b_eq, ?_, ?_, ?_, ?_⟩
  · show Subscheme.divPow (Subscheme.totalTransform t.f ℜ'.J) t.exceptional ℜ'.nu.toNat =
      Subscheme.divPow (Subscheme.totalTransform t.f ℜ.J) t.exceptional ℜ.nu.toNat
    rw [h.J_eq, h.nu_eq]
  · intro i y
    induction i using Fin.lastCases with
    | last =>
      have hfib : ∀ i' : Fin (ℜ'.α + 1), (Fin.snoc (α := fun _ => Fin (ℜ.α + 1))
          (fun k => (π k).castSucc) (Fin.last ℜ.α) : Fin (ℜ'.α + 1) → Fin (ℜ.α + 1)) i' =
            Fin.last ℜ.α → i' = Fin.last ℜ'.α := by
        intro i' hi'
        induction i' using Fin.lastCases with
        | last => rfl
        | cast k => rw [hπc] at hi'; exact absurd hi' (Fin.castSucc_lt_last _).ne
      have hlast : ((ℜ'.transform t).E (Fin.last ℜ'.α)).stalkIdeal y =
          ((ℜ.transform t).E (Fin.last ℜ.α)).stalkIdeal y := by
        simp only [DatumII.Raw.transform, Fin.snoc_last]
      refine le_antisymm (le_iInf fun k => ?_) ?_
      · rw [hfib k.1 k.2]
        exact hlast.symm.le
      · exact (iInf_le (fun i' : {i' : Fin (ℜ'.α + 1) //
          (Fin.snoc (α := fun _ => Fin (ℜ.α + 1))
            (fun k => (π k).castSucc) (Fin.last ℜ.α) : Fin (ℜ'.α + 1) → Fin (ℜ.α + 1)) i' =
              Fin.last ℜ.α} => ((ℜ'.transform t).E i'.1).stalkIdeal y)
          ⟨Fin.last ℜ'.α, hπl⟩).trans hlast.le
    | cast j =>
      let D' : Subscheme X := ⨅ k : {k : Fin ℜ'.α // π k = j}, ℜ'.E k.1
      have hD' : D'.stalkIdeal (t.f y) = (ℜ.E j).stalkIdeal (t.f y) := by
        rw [DatumTransform.stalkIdeal_iInf_fintype, h.stalkIdeal_eq j]
      have hL : ((ℜ.transform t).E (Fin.castSucc j)).stalkIdeal y =
          (Subscheme.strictTransform t (ℜ.E j)).stalkIdeal y := by
        simp only [DatumII.Raw.transform, Fin.snoc_castSucc]
      rw [hL, MonoidalTransformation.stalkIdeal_strictTransform_congr t y hD'.symm,
        MonoidalTransformation.stalkIdeal_strictTransform_iInf_of_disjoint t
          (fun k : {k : Fin ℜ'.α // π k = j} => ℜ'.E k.1)
          (fun k l hkl => h.disjoint k.1 l.1 (fun e => hkl (Subtype.ext e)) (k.2.trans l.2.symm)) y]
      refine le_antisymm (le_iInf fun i' => ?_) (le_iInf fun k => ?_)
      · obtain ⟨i', hi'⟩ := i'
        induction i' using Fin.lastCases with
        | last => rw [hπl] at hi'; exact absurd hi'.symm (Fin.castSucc_lt_last _).ne
        | cast k =>
          have hk : π k = j := Fin.castSucc_injective _ (by rw [← hπc]; exact hi')
          have := iInf_le (fun k : {k : Fin ℜ'.α // π k = j} =>
            (Subscheme.strictTransform t (ℜ'.E k.1)).stalkIdeal y) ⟨k, hk⟩
          simpa only [DatumII.Raw.transform, Fin.snoc_castSucc] using this
      · have := iInf_le (fun i' : {i' : Fin (ℜ'.α + 1) // (Fin.snoc (α := fun _ => Fin (ℜ.α + 1))
          (fun k => (π k).castSucc) (Fin.last ℜ.α) : Fin (ℜ'.α + 1) → Fin (ℜ.α + 1)) i' =
            Fin.castSucc j} => ((ℜ'.transform t).E i'.1).stalkIdeal y)
          ⟨Fin.castSucc k.1, by rw [hπc, k.2]⟩
        simpa only [DatumII.Raw.transform, Fin.snoc_castSucc] using this
  · intro i' j' hne hπ
    induction i' using Fin.lastCases with
    | last =>
      induction j' using Fin.lastCases with
      | last => exact absurd rfl hne
      | cast l => rw [hπl, hπc] at hπ; exact absurd hπ.symm (Fin.castSucc_lt_last _).ne
    | cast k =>
      induction j' using Fin.lastCases with
      | last => rw [hπl, hπc] at hπ; exact absurd hπ (Fin.castSucc_lt_last _).ne
      | cast l =>
        rw [hπc, hπc] at hπ
        have hkl : k ≠ l := fun e => hne (by rw [e])
        have hd := h.disjoint k l hkl (Fin.castSucc_injective _ hπ)
        simp only [DatumII.Raw.transform, Fin.snoc_castSucc]
        refine Set.disjoint_left.mpr fun y hy1 hy2 => ?_
        exact Set.disjoint_left.mp hd (MonoidalTransformation.pts_strictTransform_subset t _ hy1)
          (MonoidalTransformation.pts_strictTransform_subset t _ hy2)
  · intro i' hne
    induction i' using Fin.lastCases with
    | cast k =>
      simp only [hπc, DatumII.Raw.transform, Fin.snoc_castSucc] at hne ⊢
      obtain ⟨y, hy⟩ := hne
      exact h.a_eq k ⟨t.f.base y, MonoidalTransformation.pts_strictTransform_subset t _ hy⟩
    | last =>
      simp only [hπl, DatumII.Raw.transform, Fin.snoc_last] at hne ⊢
      obtain ⟨y, hy⟩ := hne
      have hBpts : B.pts.Nonempty :=
        ⟨t.f.base y, by
          have := hy
          rw [MonoidalTransformation.pts_exceptional t] at this
          exact this⟩
      rcases hB with hBe | ⟨hBns, hBirr⟩
      · exfalso
        have : B.pts = ∅ := by rw [hBe]; exact DatumTransform.pts_empty
        rw [this] at hBpts
        exact Set.not_nonempty_empty hBpts
      · rw [h.sum_isContainedIn_eq (DatumTransform.isReduced_of_isNonsingular hBns) hBirr hBpts,
          h.nu_eq, h.b_eq]

end IsRefinement


namespace Refines

variable {ℜ' ℜ : Raw X}

/-- The refinement is preserved by the transform along a centre. -/
theorem transform (h : Refines ℜ' ℜ) {B : Subscheme X} (hB : B.IsCenter)
    (t : MonoidalTransformation X B) : Refines (ℜ'.transform t) (ℜ.transform t) := by
  obtain ⟨π, hπ⟩ := h
  exact ⟨_, hπ.transform hB t⟩

/-- A succession permissible for the refinement `ℜ'` is permissible for `ℜ`, and the refinement
is preserved along it (Definition 8, iterating `IsRefinement.transform`). -/
theorem isPermissibleII_transformII {Y : Scheme.{u}} (σ : MonoidalSuccession X Y) :
    ∀ {ℜ' ℜ : Raw X}, Refines ℜ' ℜ → σ.IsPermissibleII ℜ' →
      σ.IsPermissibleII ℜ ∧ Refines (σ.transformII ℜ') (σ.transformII ℜ) := by
  induction σ with
  | nil X => exact fun h _ => ⟨trivial, h⟩
  | cons B t rest ih =>
    intro ℜ' ℜ h hσ
    obtain ⟨π, hπ⟩ := h
    have hp : ℜ.IsPermissible B := (hπ.isPermissible_iff B).mp hσ.1
    obtain ⟨h1, h2⟩ := ih (Refines.transform ⟨π, hπ⟩ hσ.1.1 t) hσ.2
    exact ⟨⟨hp, h1⟩, h2⟩

private theorem S_eq_empty_of_resolvedEverywhere {ℜ : Raw X} (h : ℜ.ResolvedEverywhere) :
    ℜ.S = ∅ :=
  Set.eq_empty_of_forall_notMem fun x hx => absurd (h x) (not_lt.2 hx)

/-- Resolvability passes from a refinement to the refined datum: the same succession is
permissible and resolves (the sets `S` agree). -/
theorem resolvable (h : Refines ℜ' ℜ) : ℜ'.Resolvable → ℜ.Resolvable := by
  rintro ⟨Z, σ, hσ, hS⟩
  obtain ⟨hp, π, hπ⟩ := isPermissibleII_transformII σ h hσ
  exact ⟨Z, σ, hp, by rw [← hπ.S_eq]; exact hS⟩

/-- If `ℜ'` refines `ℜ` and is a datum, then `ℜ` has the weak clauses of Definition 3 (II): the
`E_i` are non-singular divisors (their stalks are those of the irreducible pieces). -/
theorem isWeakDatum (h : Refines ℜ' ℜ) (hℜ' : ℜ'.IsDatum) : ℜ.IsWeakDatum := by
  obtain ⟨π, hπ⟩ := h
  refine ⟨by rw [← hπ.b_eq]; exact hℜ'.1, fun i => ?_, by rw [← hπ.eUnion_eq]; exact hℜ'.2.2.1,
    fun x => by rw [← hπ.J_eq]; exact hℜ'.2.2.2 x⟩
  refine Subscheme.isNonsingularDivisor_of_forall_stalkIdeal_eq fun z hz => ?_
  rcases hπ.stalkIdeal_eq_top_or_exists i z with htop | ⟨k, -, hk⟩
  · exact absurd htop (Subscheme.mem_pts_iff_stalkIdeal_ne_top.mp hz)
  · exact ⟨ℜ'.E k, (hℜ'.2.1 k).isNonsingularDivisor, hk.symm⟩

end Refines

/-! ### Splitting a weak datum into a datum -/

/-- **The split** (repair of p. 308 / p. 321: "`Ẽ_1, …, Ẽ_α̃` are non-singular irreducible
subschemes … of codimension 1"): a weak datum on an algebraic scheme is refined by a resolution
datum; each `E_j` is replaced by its irreducible (= connected) components, with the exponent of
`E_j`, the same `J` and `b`.

Deviation from the paper (proof corrected): the paper asserts that the `Ẽ_j` are irreducible;
this is false.  The sets `S`, `S_ν` and the
permissibility of centres concern only the union and the weights, which the splitting does not
change (`IsRefinement.S_eq`, `IsRefinement.isPermissible_iff`), and the transform of Definition 7
(II) commutes with the splitting (`IsRefinement.transform`,
`Refines.isPermissibleII_transformII`). -/
@[blueprint "lem:IV.tilde-split"
  (statement := /-- Let $X$ be a non-singular algebraic scheme and
    $\mathfrak R=(E_1,\dots,E_\alpha\,|\,J,b\,|\,a_1,\dots,a_\alpha)$ a tuple with $b>0$,
    $J_x\ne0$ at every point, the $E_i$ non-singular and everywhere of codimension one (empty or
    reducible allowed), and $E_1\cup\dots\cup E_\alpha$ having only normal crossings. Splitting
    each $E_i$ into its connected components, which are finitely many, pairwise disjoint,
    non-singular and irreducible of codimension one, each with the exponent $a_i$, gives a
    resolution datum $\mathfrak R'$ of type $\mathfrak R^N_{\mathrm{II}}$ (\cref{def:I.3-II}).
    Moreover $\mathfrak R'$ and $\mathfrak R$ have the same $S$, $S_\nu$, $\nu$, the same resolved
    points and the same permissible centres, and the transform $f^*(\mathfrak R')$ (Definition~7) is
    the splitting of $f^*(\mathfrak R)$ along every centre; hence a permissible succession for
    $\mathfrak R'$ is permissible for $\mathfrak R$ and resolves it iff it resolves $\mathfrak R'$.

    (Formalization note: the existence is \texttt{exists\_isDatum\_refines}; the other
    assertions are \texttt{IsRefinement.S\_eq}, \texttt{IsRefinement.isPermissible\_iff},
    \texttt{IsRefinement.transform}, \texttt{Refines.isPermissibleII\_transformII}.)

    \textbf{Deviation from the paper (proof corrected; repair of the paper's error on the subschemes $\tilde E_j$).} The paper asserts: ``In both cases, we see that $\tilde
    E_1,\cdots,\tilde E_{\tilde\alpha}$ are non-singular irreducible subschemes of $\bar X'_s$ of
    codimension 1, and that $\tilde E_1\cup\cdots\cup\tilde E_{\tilde\alpha}$ has only normal
    crossings on $\bar X'_s$'' (p.~308; the same on p.~321, \cref{lem:IV.4-tilde-facts}). The
    irreducibility is false (\cref{rem:IV.3-2}). Lean replaces each $\tilde E_j$ by its
    connected components, with the exponent of $\tilde E_j$, and applies Theorem
    $\mathrm{II}_2^{N-1}$ to the result. -/)
  (proof := /-- The irreducible components of a non-singular subscheme of pure codimension one are
    its connected components: they are finitely many, pairwise disjoint (the local rings are
    domains), non-singular irreducible of codimension one, and have at their points the stalk
    ideal of the subscheme. Number the pieces and give each the exponent $a_i$ of its $E_i$. The
    condition of normal crossings concerns the union, which is unchanged. The sums defining
    $S$ agree since a point lies on at most one piece of each $E_i$, and on one iff it lies on
    $E_i$. For the transform: the stalks of the strict transform of $\bigcup_kE_{ik}$ at $y$ are
    those of the strict transform of the unique piece through $f(y)$, so the strict transform of
    the disjoint union is the disjoint union of the strict transforms; the exceptional divisor over
    an irreducible centre is irreducible; and an irreducible centre $B$ lies in $E_i$ iff it
    lies in exactly one piece of $E_i$, so $\sum_{B\subseteq E_i}a_i$ is the same for $\mathfrak R$
    and $\mathfrak R'$ (for the empty centre the exceptional divisor is empty, and the exponent
    is irrelevant). A piece equal to the centre has empty strict transform, which is the empty
    subscheme, allowed in a datum (p.~165).

    \textbf{Deviation from the paper (proof corrected).} The paper does not split the $\tilde E_j$
    (it asserts that they are irreducible). -/)
  (proofUses := ["def:I.3-II", "def:I.6-II", "def:I.7-II", "rem:I.1-transform-is-datum-II"])
  (latexEnv := "lemma")]
theorem exists_isDatum_refines [IsAlgebraicScheme X] {ℜ : Raw X} (hℜ : ℜ.IsWeakDatum) :
    ∃ ℜ' : Raw X, ℜ'.IsDatum ∧ Refines ℜ' ℜ := by
  have := IsAlgebraicScheme.noetherianSpace X
  choose n C _ hdat hdisj _ heq using fun i : Fin ℜ.α =>
    Subscheme.exists_family_of_isNonsingular (hℜ.2.1 i).1 (hℜ.2.1 i).2
  let T := Σ i : Fin ℜ.α, Fin (n i)
  let e : T ≃ Fin (Fintype.card T) := Fintype.equivFin T
  let ℜ' : Raw X := ⟨Fintype.card T, fun k => C (e.symm k).1 (e.symm k).2,
    fun k => ℜ.a (e.symm k).1, ℜ.J, ℜ.b⟩
  have href : IsRefinement ℜ' ℜ (fun k => (e.symm k).1) := by
    refine ⟨rfl, rfl, fun i x => ?_, fun i' j' hne hπ => ?_, fun i' _ => rfl⟩
    · rw [heq i, DatumTransform.stalkIdeal_iInf_fintype]
      refine le_antisymm (le_iInf fun k => ?_) (le_iInf fun j => ?_)
      · obtain ⟨k, hk⟩ := k
        have hk' : (e.symm k).1 = i := hk
        show _ ≤ (C (e.symm k).1 (e.symm k).2).stalkIdeal x
        generalize e.symm k = p at hk' ⊢
        obtain ⟨i', j'⟩ := p
        simp only at hk' ⊢
        subst hk'
        exact iInf_le (fun j => (C i' j).stalkIdeal x) j'
      · have hs : e.symm (e ⟨i, j⟩) = ⟨i, j⟩ := e.symm_apply_apply _
        have key : (C (e.symm (e ⟨i, j⟩)).1 (e.symm (e ⟨i, j⟩)).2).stalkIdeal x =
            (C i j).stalkIdeal x := by rw [hs]
        exact (iInf_le (fun k : {k : Fin (Fintype.card T) // (e.symm k).1 = i} =>
          (C (e.symm k.1).1 (e.symm k.1).2).stalkIdeal x) ⟨e ⟨i, j⟩, by simp⟩).trans key.le
    · have hne' : e.symm i' ≠ e.symm j' := fun h => hne (e.symm.injective h)
      show Disjoint (C (e.symm i').1 (e.symm i').2).pts (C (e.symm j').1 (e.symm j').2).pts
      have hπ' : (e.symm i').1 = (e.symm j').1 := hπ
      generalize e.symm i' = p at hne' hπ' ⊢
      generalize e.symm j' = q at hne' hπ' ⊢
      obtain ⟨a, ja⟩ := p
      obtain ⟨b, jb⟩ := q
      simp only at hπ'
      subst hπ'
      have hj : ja ≠ jb := fun hj => hne' (by rw [hj])
      exact hdisj a ja jb hj
  refine ⟨ℜ', ⟨hℜ.1, fun k => hdat _ _, ?_, hℜ.2.2.2⟩, _, href⟩
  show ℜ'.eUnion.HasOnlyNormalCrossings
  rw [href.eUnion_eq]
  exact hℜ.2.2.1

/-- A permissible transform of a weak datum is a weak datum (Remark 1, p. 169, for the weak
clauses: it follows from Remark 1 for the split). -/
theorem IsWeakDatum.transform [Hironaka.Cited.IsHironakaBaseIsClosedSingularLocus.{u}] [Hironaka.Cited.CurveFiniteIntegralClosure.{u}] [Hironaka.Cited.IsRegularLocalRingLocalizationOfIsRegularLocalRing.{u}] [IsAlgebraicScheme X] (hX : X.IsNonsingular) {ℜ : Raw X}
    (hℜ : ℜ.IsWeakDatum) {B : Subscheme X} (t : MonoidalTransformation X B)
    (hB : ℜ.IsPermissible B) : (ℜ.transform t).IsWeakDatum := by
  obtain ⟨ℜ', hℜ', π, hπ⟩ := exists_isDatum_refines hℜ
  have hp : ℜ'.IsPermissible B := (hπ.isPermissible_iff B).mpr hB
  exact (Refines.transform ⟨π, hπ⟩ hB.1 t).isWeakDatum (transform_isDatum hX ℜ' hℜ' t hp).1

/-- **Theorem `II₂^M` for a weak datum** (repair of p. 310, "Thus, applying Theorem
`II₂^{N-1}` to the resolution datum `ℜ^{N-1}_II` on `X̃`"): on an ambient scheme of dimension `M`
a weak datum is resolvable.  The induction hypothesis is applied to the split.

Deviation from the paper (proof corrected): the paper applies `II₂^{N-1}` to `ℜ^{N-1}_II` itself,
which need not be a resolution datum. -/
@[blueprint "lem:IV.tilde-resolvable"
  (statement := /-- Assume Theorem $\mathrm{II}_2^{M}$ (\cref{thm:I.2-II2}). Let $X$ be a
    non-singular irreducible algebraic scheme of dimension $M$ and
    $\mathfrak R=(E_1,\dots,E_\alpha\,|\,J,b\,|\,a_1,\dots,a_\alpha)$ a tuple with $b>0$,
    $J_x\ne0$ at every point, the $E_i$ non-singular and everywhere of codimension one (possibly
    reducible or empty) and $\bigcup E_i$ having only normal crossings. Then there is a finite
    permissible succession of monoidal transformations of $X$ for $\mathfrak R$ after which
    $\mathfrak R$ is resolved everywhere.

    \textbf{Deviation from the paper (proof corrected; repair of the paper's error on the subschemes $\tilde E_j$).} The paper (p.~310): ``Thus, applying Theorem
    $\mathrm{II}_2^{N-1}$ to the resolution datum $\mathfrak R^{N-1}_{\mathrm{II}}$ on $\tilde X$
    (without restriction), we can prove that there exists a finite permissible succession of
    monoidal transformations of $X_s$ for $\mathfrak R(s)$, which induces a permissible
    succession of monoidal transformations of $\tilde X$ for $\mathfrak R^{N-1}_{\mathrm{II}}$
    and which resolve the datum $\mathfrak R^{N-1}_{\mathrm{II}}$'' (the same on p.~322). The
    datum $\mathfrak R^{N-1}_{\mathrm{II}}$ is not a resolution datum in general (its $\tilde
    E_j$ can be reducible, and $\tilde E_i=\tilde X$ if $F=E_i$), so Theorem
    $\mathrm{II}_2^{N-1}$ is applied to its splitting (\cref{lem:IV.tilde-split}). -/)
  (proof := /-- Split $\mathfrak R$ (\cref{lem:IV.tilde-split}) into a resolution datum
    $\mathfrak R'$, apply Theorem $\mathrm{II}_2^{M}$ to $\mathfrak R'$, and transport the
    resulting succession back: it is permissible for $\mathfrak R$ and resolves $\mathfrak R$,
    as $S(\sigma^*\mathfrak R)=S(\sigma^*\mathfrak R')=\emptyset$.

    \textbf{Deviation from the paper (proof corrected).} The paper applies the theorem to
    $\mathfrak R$ itself. -/)
  (proofUses := ["lem:IV.tilde-split", "thm:I.2-II2"])
  (latexEnv := "lemma")]
theorem resolvable_of_isWeakDatum {M : ℕ} (hII : FundamentalTheorem.II₂.{u} M) {X : Scheme.{u}}
    (hX : IsAmbient X M) {ℜ : Raw X} (hℜ : ℜ.IsWeakDatum) : ℜ.Resolvable := by
  have := hX.1
  obtain ⟨ℜ', hℜ', href⟩ := exists_isDatum_refines hℜ
  obtain ⟨Y, σ, hσ, hres⟩ := hII X hX ⟨ℜ', hℜ'⟩
  exact href.resolvable ⟨Y, σ, hσ, Refines.S_eq_empty_of_resolvedEverywhere hres⟩

/-! ### Emptying the entries equal to the whole space -/

/-- The datum with every entry equal to the whole space (zero ideal sheaf) replaced by the empty
subscheme.  This is the "drop" of the repair: for `F = E_i` the trace `Ẽ_i` is all of `X̃`. -/
noncomputable def emptyIfBot (ℜ : Raw X) : Raw X :=
  { ℜ with E := fun i => (ℜ.E i).emptyIfBot }

/-- `emptyIfBot` keeps the number of components. -/
@[simp] theorem emptyIfBot_α (ℜ : Raw X) : ℜ.emptyIfBot.α = ℜ.α := rfl

/-- The entries of `emptyIfBot`. -/
theorem emptyIfBot_E (ℜ : Raw X) (i : Fin ℜ.α) : ℜ.emptyIfBot.E i = (ℜ.E i).emptyIfBot := rfl

/-- `emptyIfBot` keeps the exponents. -/
@[simp] theorem emptyIfBot_a (ℜ : Raw X) : ℜ.emptyIfBot.a = ℜ.a := rfl

/-- `emptyIfBot` keeps `J`. -/
@[simp] theorem emptyIfBot_J (ℜ : Raw X) : ℜ.emptyIfBot.J = ℜ.J := rfl

/-- `emptyIfBot` keeps `b`. -/
@[simp] theorem emptyIfBot_b (ℜ : Raw X) : ℜ.emptyIfBot.b = ℜ.b := rfl

/-- Emptying the whole-space entries changes no weight, provided their exponents vanish. -/
theorem emptyIfBot_weight (ℜ : Raw X) (ha : ∀ i, ℜ.E i = ⊥ → ℜ.a i = 0) (x : X) :
    ℜ.emptyIfBot.weight x = ℜ.weight x := by
  unfold DatumII.Raw.weight
  rw [Finset.sum_filter, Finset.sum_filter]
  refine Finset.sum_congr rfl fun (i : Fin ℜ.α) _ => ?_
  by_cases hi : ℜ.E i = ⊥
  · rw [emptyIfBot_E, Subscheme.pts_emptyIfBot_eq_empty hi]
    simp [ha i hi]
  · rw [emptyIfBot_E, Subscheme.pts_emptyIfBot_of_ne_bot hi]
    rfl

/-- `emptyIfBot` keeps `S(ℜ)`. -/
theorem emptyIfBot_S (ℜ : Raw X) (ha : ∀ i, ℜ.E i = ⊥ → ℜ.a i = 0) :
    ℜ.emptyIfBot.S = ℜ.S := by
  ext x
  show (ℜ.b : ℕ∞) ≤ (ℜ.emptyIfBot.weight x : ℕ∞) + ℜ.nuAt x ↔
    (ℜ.b : ℕ∞) ≤ (ℜ.weight x : ℕ∞) + ℜ.nuAt x
  rw [emptyIfBot_weight ℜ ha]

/-- `emptyIfBot` keeps `ν(ℜ)`. -/
theorem emptyIfBot_nu (ℜ : Raw X) (ha : ∀ i, ℜ.E i = ⊥ → ℜ.a i = 0) :
    ℜ.emptyIfBot.nu = ℜ.nu := by
  unfold DatumII.Raw.nu
  rw [emptyIfBot_S ℜ ha]
  rfl

/-- **Emptying commutes with the transform** (Definition 7 (II)): the stage-to-stage equalities of
the frame, proved for the datum with all the `Ẽ_j`, are transported to the emptied datum.  The
hypotheses: the entries equal to the whole space have exponent `0` (the paper's choice, forced by
`J̄(s) ≠ 0`), and the other entries do not become the whole space under the strict transform
(for a weak datum this holds, see `emptyIfBot_transform_of_isPermissible`).

Deviation from the paper (proof corrected): for `F = E_i` the trace `Ẽ_i` is all of `X̃`, not a
subscheme of codimension one.  The entry is replaced by
the empty subscheme (allowed in a datum, p. 165), `isWeakDatum_emptyIfBot` records the clauses that
remain, and the strict transform of the whole space is the whole space
(`MonoidalTransformation.strictTransform_bot`), so the emptying is compatible with the transform. -/
@[blueprint "lem:IV.tilde-drop"
  (statement := /-- Let $\mathfrak R=(E_1,\dots,E_\alpha\,|\,J,b\,|\,a_1,\dots,a_\alpha)$ be a
    tuple in which each $E_i$ is either the whole space $X$ (with $a_i=0$) or non-singular and
    everywhere of codimension one, and let $\mathfrak R^e$ be obtained by replacing each $E_i=X$
    by the empty subscheme. Then $\mathfrak R^e$ has the same $S$ and $\nu$ as $\mathfrak R$, and
    for
    a monoidal transformation $f$ (with $f^{-1}(E_i)$-strict transforms of the other $E_i$ not
    equal to the whole space) the transform commutes with the replacement:
    $f^*(\mathfrak R^e)=(f^*\mathfrak R)^e$.

    \textbf{Deviation from the paper (proof corrected; repair of the paper's error on the subschemes $\tilde E_j$).} The paper (p.~308, similarly p.~321): ``In both cases, we see that
    $\tilde E_1,\cdots,\tilde E_{\tilde\alpha}$ are non-singular irreducible subschemes of
    $\bar X'_s$ of codimension 1, and that $\tilde E_1\cup\cdots\cup\tilde E_{\tilde\alpha}$
    has only normal crossings on $\bar X'_s$.'' If $F=E_i$ (allowed by Definition~5), then
    $\tilde E_i=\tilde X$. Lean replaces such a $\tilde E_i$ by the empty subscheme; the lifting of
    the normal crossings of a centre $B_s\subseteq F(s)=E_i(s)$ is then by the lemma of p.~309
    (``either $E_i(s)$ does not contain $x$ or it contains $B_s$''). -/)
  (proof := /-- The weights, $\nu(J_x)$, hence $S$ and $\nu$, are unchanged since the dropped
    entries have exponent $0$. The strict transform of the whole space is the whole space, because
    the exceptional ideal is locally generated by a non-zero-divisor, and that of the empty
    subscheme is empty; the strict transform of the other entries is not the whole space by
    hypothesis, and the exceptional divisor is not the whole space as it is nowhere dense. The
    new exponent $a_{\alpha+1}=\sum_{B\subseteq E_i}a_i+\nu-b$ is unchanged: the dropped entries
    contribute $0$ if they contain $B$, and are not counted otherwise.

    \textbf{Deviation from the paper (proof corrected).} The paper has no such case distinction:
    it asserts that all the $\tilde E_j$ are of codimension one. -/)
  (latexEnv := "lemma")]
theorem emptyIfBot_transform (ℜ : Raw X) {B : Subscheme X} (t : MonoidalTransformation X B)
    [Nonempty t.X'] (ha : ∀ i, ℜ.E i = ⊥ → ℜ.a i = 0)
    (hne : ∀ i, ℜ.E i ≠ ⊥ → Subscheme.strictTransform t (ℜ.E i) ≠ ⊥) :
    ℜ.emptyIfBot.transform t = (ℜ.transform t).emptyIfBot := by
  have hnu : ℜ.emptyIfBot.nu = ℜ.nu := emptyIfBot_nu ℜ ha
  have hexc : t.exceptional ≠ ⊥ := MonoidalTransformation.exceptional_ne_bot t
  have hsum : ∑ i ∈ Finset.univ.filter (fun i : Fin ℜ.α => B.IsContainedIn (ℜ.E i).emptyIfBot),
      ℜ.a i = ∑ i ∈ Finset.univ.filter (fun i : Fin ℜ.α => B.IsContainedIn (ℜ.E i)), ℜ.a i := by
    rw [Finset.sum_filter, Finset.sum_filter]
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases hi : ℜ.E i = ⊥
    · rw [Subscheme.emptyIfBot_of_eq_bot hi, ha i hi]
      simp
    · rw [Subscheme.emptyIfBot_of_ne_bot hi]
  have hE : ∀ i : Fin (ℜ.α + 1),
      Fin.snoc (α := fun _ => Subscheme t.X')
        (fun j => Subscheme.strictTransform t (ℜ.E j).emptyIfBot) t.exceptional i =
      (Fin.snoc (α := fun _ => Subscheme t.X')
        (fun j => Subscheme.strictTransform t (ℜ.E j)) t.exceptional i).emptyIfBot := by
    intro i
    induction i using Fin.lastCases with
    | last =>
      simp only [Fin.snoc_last]
      exact (Subscheme.emptyIfBot_of_ne_bot hexc).symm
    | cast j =>
      simp only [Fin.snoc_castSucc]
      by_cases hj : ℜ.E j = ⊥
      · rw [Subscheme.emptyIfBot_of_eq_bot hj, hj, MonoidalTransformation.strictTransform_top,
          MonoidalTransformation.strictTransform_bot, Subscheme.emptyIfBot_bot]
      · rw [Subscheme.emptyIfBot_of_ne_bot hj, Subscheme.emptyIfBot_of_ne_bot (hne j hj)]
  show (DatumII.Raw.mk (ℜ.α + 1)
      (Fin.snoc (α := fun _ => Subscheme t.X')
        (fun i => Subscheme.strictTransform t (ℜ.E i).emptyIfBot) t.exceptional)
      (Fin.snoc (α := fun _ => ℕ) ℜ.a
        (∑ i ∈ Finset.univ.filter (fun i : Fin ℜ.α => B.IsContainedIn (ℜ.E i).emptyIfBot), ℜ.a i +
          ℜ.emptyIfBot.nu.toNat - ℜ.b))
      (Subscheme.divPow (Subscheme.totalTransform t.f ℜ.J) t.exceptional
        ℜ.emptyIfBot.nu.toNat) ℜ.b : Raw t.X') =
    DatumII.Raw.mk (ℜ.α + 1)
      (fun i => (Fin.snoc (α := fun _ => Subscheme t.X')
        (fun i => Subscheme.strictTransform t (ℜ.E i)) t.exceptional i).emptyIfBot)
      (Fin.snoc (α := fun _ => ℕ) ℜ.a
        (∑ i ∈ Finset.univ.filter (fun i : Fin ℜ.α => B.IsContainedIn (ℜ.E i)), ℜ.a i +
          ℜ.nu.toNat - ℜ.b))
      (Subscheme.divPow (Subscheme.totalTransform t.f ℜ.J) t.exceptional ℜ.nu.toNat) ℜ.b
  rw [hnu, hsum]
  congr 1
  exact funext hE

/-- The clauses of Definition 3 (II) that the frame delivers for the auxiliary datum with the
whole-space traces emptied: every `Ẽ_j` is the whole space or a non-singular divisor, and the
others have only normal crossings. -/
theorem isWeakDatum_emptyIfBot {ℜ : Raw X} (hb : 0 < ℜ.b)
    (hE : ∀ i, ℜ.E i = ⊥ ∨ (ℜ.E i).IsNonsingularDivisor)
    (hNC : ℜ.emptyIfBot.eUnion.HasOnlyNormalCrossings) (hJ : ∀ x : X, ℜ.J.stalkIdeal x ≠ ⊥) :
    ℜ.emptyIfBot.IsWeakDatum := by
  refine ⟨hb, fun (i : Fin ℜ.α) => ?_, hNC, hJ⟩
  by_cases hbot : ℜ.E i = ⊥
  · rw [emptyIfBot_E, Subscheme.emptyIfBot_of_eq_bot hbot]
    refine ⟨Subscheme.isNonsingular_empty, fun x hx => ?_⟩
    exact absurd hx (by simp [show (⊤ : Subscheme X) = Subscheme.empty from rfl,
      DatumTransform.pts_empty])
  · rw [emptyIfBot_E, Subscheme.emptyIfBot_of_ne_bot hbot]
    exact (hE i).resolve_left hbot

/-- The generic point of an irreducible non-singular scheme is not in `S` of a weak datum
("obviously, the generic point of `X` does not belong to `S(ℜ)`", Lemma 2 of §1, for the
split datum). -/
theorem IsWeakDatum.genericPoint_notMem_S [IsAlgebraicScheme X] [IrreducibleSpace X]
    (hX : X.IsNonsingular) {ℜ : Raw X} (hℜ : ℜ.IsWeakDatum) : genericPoint X ∉ ℜ.S := by
  obtain ⟨ℜ', hℜ', π, hπ⟩ := exists_isDatum_refines hℜ
  rw [← hπ.S_eq]
  exact LocSucc.genericPoint_notMem_S hX ℜ' hℜ'

/-- A centre permissible for a weak datum on an irreducible non-singular scheme is not the whole
scheme: `B ⊆ S*(ℜ) ⊆ S(ℜ)` misses the generic point. -/
theorem IsWeakDatum.pts_ne_univ_of_isPermissible [IsAlgebraicScheme X] [IrreducibleSpace X]
    (hX : X.IsNonsingular) {ℜ : Raw X} (hℜ : ℜ.IsWeakDatum) {B : Subscheme X}
    (hB : ℜ.IsPermissible B) : B.pts ≠ Set.univ := by
  intro h
  have hη : genericPoint X ∈ B.pts := h ▸ Set.mem_univ _
  exact hℜ.genericPoint_notMem_S hX (hB.2.1 hη).1

/-- **Emptying commutes with the transform** for a weak datum and a permissible centre
(`emptyIfBot_transform` with its hypotheses on the strict transforms discharged). -/
theorem emptyIfBot_transform_of_isPermissible [Hironaka.Cited.IsHironakaBaseIsClosedSingularLocus.{u}] [Hironaka.Cited.MonoidalTransformationExistsIsProper.{u}] [Hironaka.Cited.CurveFiniteIntegralClosure.{u}] [Hironaka.Cited.IsRegularLocalRingLocalizationOfIsRegularLocalRing.{u}] [IsAlgebraicScheme X] [IrreducibleSpace X]
    (hX : X.IsNonsingular) (ℜ : Raw X) (hℜ : ℜ.emptyIfBot.IsWeakDatum)
    (ha : ∀ i, ℜ.E i = ⊥ → ℜ.a i = 0) {B : Subscheme X} (t : MonoidalTransformation X B)
    (hB : ℜ.emptyIfBot.IsPermissible B) :
    ℜ.emptyIfBot.transform t = (ℜ.transform t).emptyIfBot := by
  have hBX : B.pts ≠ Set.univ := hℜ.pts_ne_univ_of_isPermissible hX hB
  obtain ⟨-, -, hirr, -⟩ := MonoidalTransformation.transform_isAmbient hX hB.1 hBX t
  have : Nonempty t.X' := hirr.toNonempty
  have hw := hℜ.transform hX t hB
  refine emptyIfBot_transform ℜ t ha fun i hi => ?_
  have h1 := (hw.2.1 (Fin.castSucc i)).ne_bot
  have h2 : (ℜ.emptyIfBot.transform t).E (Fin.castSucc i) =
      Subscheme.strictTransform t (ℜ.E i) := by
    change Fin.snoc (α := fun _ => Subscheme t.X')
      (fun j => Subscheme.strictTransform t (ℜ.E j).emptyIfBot) t.exceptional (Fin.castSucc i) = _
    rw [Fin.snoc_castSucc, Subscheme.emptyIfBot_of_ne_bot hi]
  rwa [h2] at h1

/-- For a resolution datum no entry is the whole space (an irreducible subscheme of codimension one
of a non-empty scheme), so `emptyIfBot` is the identity. -/
theorem IsDatum.emptyIfBot_eq {ℜ : Raw X} (h : ℜ.IsDatum) : ℜ.emptyIfBot = ℜ := by
  unfold emptyIfBot
  obtain ⟨α, E, a, J, b⟩ := ℜ
  have hE : (fun i : Fin α => (E i).emptyIfBot) = E := funext fun i =>
    Subscheme.emptyIfBot_eq_self_of_isNonsingularIrreducibleCodimOne (h.2.1 i)
  simp only [hE]

end DatumII.Raw

end Hironaka
