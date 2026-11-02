/-
Copyright (c) 2026 Daattavya Aggarwal, Minhyong Kim, Oisin Kim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daattavya Aggarwal, Minhyong Kim, Oisin Kim
-/
module

public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.Data.Int.Star
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Architect
public import Hironaka.Ch4.ImplicationsCD
public import Hironaka.Compat.DatumRefinement
public import Hironaka.Statements

/-!
# The repaired auxiliary datum `ℜ^{N-1}_II` of Ch. IV §4 (repair of the paper's error on the subschemes `Ẽ_j`)

> In both cases, we see that `Ẽ_1, …, Ẽ_α̃` are non-singular irreducible subschemes of `X̄'_s` of
> codimension 1, and that `Ẽ_1 ∪ ⋯ ∪ Ẽ_α̃` has only normal crossings on `X̄'_s`.  (p. 321)

This is false in two ways: the `Ẽ_j` can be reducible, and
`Ẽ_i = X̃` when `F = E_i` (closed case).  `Compat/DatumRefinement.lean` is the generic part of the
repair: a weak datum (non-singular, possibly reducible divisors) is resolvable, and an entry equal
to the whole space can be replaced by the empty subscheme (`Subscheme.emptyIfBot`).  This file is
the part of the repair that mentions the frame of §4.  Every statement is "proof corrected (repair
of the paper's error on the subschemes `Ẽ_j`)", and each one that replaces a printed statement has its own
blueprint node `…-repaired`.

* **The facts of p. 321** for the datum with the whole-space traces emptied
  (`Frame.isWeakDatum_emptyIfBot_datumTilde`, no hypothesis `F ≠ E_i`): each `Ẽ_j` is the whole
  space or a non-singular divisor, because `X̄_s` is irreducible.
* **The shifted threshold** of the case `ν < b` (`Frame.droppedWeight`, `Frame.thresholdRep`,
  `Frame.jBarRep`, `Frame.bTildeRep`, `Frame.datumRep`, `Frame.le_nu_jBarRep_iff`): the traces equal
  to `X̃` carry the weight `δ_s = ∑ c_j`, which is subtracted from `b - ν` (the reason for the
  shift: without it `J̄*(s)` has a vanishing generator and Remark 2 fails).  For
  `δ_s = 0` (in particular without restriction) these are the printed objects
  (`jBarRep_eq_jBar_of_le`, `jBarRep_eq_jBarStar`, `datumRep_eq_datumTilde_of_unrestricted`).
* **Remarks 1 and 2** for the repaired datum, in one statement valid for every `ν`
  (`Frame.S_datumRep_eq_and_bijOn_cBar_and_exists_isPermissibleCenter`,
  `Frame.exists_isPermissibleCenter_of_isPermissible_datumRep`).  The normal crossings of `E(s)`
  with `B_s` are descended from `X̃` for the members of a regular system of parameters not in `B_x`
  only (`hasOnlyNormalCrossingsWith_eUnion_datumRep_aux`).
* **The relation of p. 322 and Remark 3** for the repaired datum, again uniform
  (`Frame.ker_eq_B_and_exists_transform_eq_datumRep`, `…_of_ge`): the transform of the emptied `ℜ̃`
  along `f̄_s` is the emptied `ℜ̃` of the next stage, `δ` being constant (`droppedWeight_succ`).
* **The interface of the induction** (end of the induction `S_datumRep_nonempty`, the initial
  datum `Frame.resolvable_datumRep_zero`) and the same objects on stage states
  (`FrameStage.datumRep`
  and its bridge lemmas to `Frame.stageOf`).
* **Which traces are dropped** (closed case): a trace `Ẽ_j = X̃` at a prepared stage is a component
  `E_j ⊇ F` of the original datum (`Frame.lt_and_pts_subset_of_xBar_pts_subset_eHat`), so `δ_s`
  is at most the weight of `F` (`Frame.droppedWeight_le_weight`) and threshold `0` puts the points
  of `F` into `S(ℜ)` (`Frame.mem_S_of_thresholdRep_eq_zero`), which is what the non-vanishing of
  `J̄(s)` needs.
-/

@[expose] public section

open Classical AlgebraicGeometry IsLocalRing CategoryTheory CategoryTheory.Limits

namespace Hironaka

universe u

/-! ### A trace containing the whole subscheme is the whole space -/

namespace Subscheme

variable {Y : Scheme.{u}}

/-- If a reduced subscheme `D` is contained (as a set) in `E`, the total transform of `E` to `D`
is the whole space `D` (the zero ideal sheaf): `E_x ⊆ D_x` for all `x ∈ D`, and `D_x` is the
kernel of the stalk map of `D → Y`. -/
theorem totalTransform_ι_eq_bot_of_pts_subset {E D : Subscheme Y} (hD : D.IsReduced)
    (h : D.pts ⊆ E.pts) : totalTransform D.ι E = ⊥ := by
  refine ext_stalkIdeal fun y => ?_
  rw [Hironaka.stalkIdeal_totalTransform, stalkIdeal_bot_eq, eq_bot_iff,
    Ideal.map_le_iff_le_comap]
  intro a ha
  have h1 := DatumTransform.stalkIdeal_le_of_pts_subset hD h (D.ι y) ha
  rw [stalkIdeal_eq_ker_stalkMap] at h1
  rw [Ideal.mem_comap, Ideal.mem_bot]
  exact h1

end Subscheme

namespace CD

variable {X : Scheme.{u}} {N : ℕ} {ℜ : DatumII.Raw X} {r : Restriction X} {ν : ℕ}
  {T : AB.Tower X} {x₀ : X}

/-! ## 1. The facts of p. 321 for the emptied datum (no hypothesis `F ≠ E_i`) -/

namespace Frame

variable {hS : Standing N ℜ r ν T x₀} (𝒮 : Frame hS)

/-- A trace `Ẽ_j` which is not the whole space of `X̃` comes from a component `Ê_j(s)` which does
not contain `X̄_s`. -/
theorem not_pts_xBar_subset_eHat_of_eTilde_ne_bot [Hironaka.HironakaCitedResults.{u}] {s : ℕ} {j : Fin (alphaT r ℜ.α s)}
    (hj : 𝒮.eTilde s j ≠ ⊥) : ¬ (𝒮.xBar s).pts ⊆ (𝒮.eHat s (idxT ℜ.α s r j)).pts :=
  fun h => hj (Subscheme.totalTransform_ι_eq_bot_of_pts_subset (𝒮.isReduced_xBar s) h)

/-- The components `Ê_j(s)` whose trace `Ẽ_j` is not the whole space are transversal to `X̄_s`
(`X̄_s` is irreducible and not contained in `Ê_j(s)`): the replacement of the hypothesis `F ≠ E_i`
of `isTransversalFamilyWith_eHat`. -/
theorem isTransversalFamilyWith_eHat_of_ne_bot [Hironaka.HironakaCitedResults.{u}] (s : ℕ) (hadm : 𝒮.IsAdmissibleAt s) :
    Subscheme.IsTransversalFamilyWith
      (fun i : {j : Fin (alphaT r ℜ.α s) // 𝒮.eTilde s j ≠ ⊥} =>
        𝒮.eHat s (idxT ℜ.α s r i.1)) (𝒮.xBar s) :=
  ⟨fun i x hx => 𝒮.isSimpleAt_and_codimAt_eq_one_totalTransform_c s
    (hS.isNonsingular_eSeq s (idxT ℜ.α s r i.1)) (hS.exists_stalkIdeal_eSeq s (idxT ℜ.α s r i.1))
    x hx.1,
   fun i _ hx =>
    Subscheme.not_stalkIdeal_le_of_isIrreducible_not_subset (E := 𝒮.eHat s (idxT ℜ.α s r i.1))
      (isIrreducible_pts _ hadm.1.2) (𝒮.not_pts_xBar_subset_eHat_of_eTilde_ne_bot i.2) le_rfl hx.2⟩

/-- The kept components `Ê_j(s)` (those with `Ẽ_j ≠ X̃`) have a reduced union with only normal
crossings with `X̄_s`: a sub-union of the normal crossings of the whole boundary
(`hasOnlyNormalCrossingsWith_xBar_boundary`). -/
theorem hasOnlyNormalCrossingsWith_xBar_of_ne_bot [Hironaka.HironakaCitedResults.{u}] (s : ℕ) (hadm : 𝒮.IsAdmissibleAt s) :
    (⨅ i : {j : Fin (alphaT r ℜ.α s) // 𝒮.eTilde s j ≠ ⊥},
        𝒮.eHat s (idxT ℜ.α s r i.1)).HasOnlyNormalCrossingsWith (𝒮.xBar s) := by
  intro y hy
  have : IsRegularLocalRing ((𝒮.tHat.X s).presheaf.stalk y) := 𝒮.isNonsingular_tHat_X s y
  exact Subscheme.hasOnlyNormalCrossingsWithAt_iInf_comp
    (E := fun i : Fin (alphaT r ℜ.α s) => 𝒮.eHat s (idxT ℜ.α s r i))
    (fun i : {j : Fin (alphaT r ℜ.α s) // 𝒮.eTilde s j ≠ ⊥} => i.1) (𝒮.isReduced_iInf_eHat s)
    (𝒮.hasOnlyNormalCrossingsWith_xBar_boundary s hadm y hy)
    (fun i hi => 𝒮.isSimpleAt_and_codimAt_eq_one_totalTransform_c s
      (hS.isNonsingular_eSeq s (idxT ℜ.α s r i)) (hS.exists_stalkIdeal_eSeq s (idxT ℜ.α s r i))
      y hi)

/-- **The traces `Ẽ_j` that are not the whole space are non-singular and everywhere of
codimension one** (p. 321: "we see that `Ẽ_1, …, Ẽ_α̃` are non-singular irreducible subschemes of
`X̄_s` of codimension 1").

Deviation from the paper (proof corrected, repair of the paper's error on the subschemes `Ẽ_j`): the irreducibility
is false and, in the closed case, `Ẽ_i = X̃` when `F = E_i` (counterexamples in the docstring of
`Frame.isNonsingular_xTilde_and_dim_xTilde_and_hasOnlyNormalCrossings_of_prepHyp`, blueprint
`lem:IV.4-tilde-facts`).  The dichotomy: a trace which is not the whole space comes from a
component `Ê_j(s)` not containing the irreducible `X̄_s`, hence transversal to it; no hypothesis
`F ≠ E_i`. -/
theorem isNonsingular_and_isEverywhereOfCodim_eTilde_of_ne_bot [Hironaka.HironakaCitedResults.{u}] {s : ℕ}
    (hprep : PrepHyp N ℜ r ν T x₀ s) {j : Fin (alphaT r ℜ.α s)} (hj : 𝒮.eTilde s j ≠ ⊥) :
    (𝒮.eTilde s j).IsNonsingular ∧ (𝒮.eTilde s j).IsEverywhereOfCodim 1 := by
  have hadm := 𝒮.isAdmissibleAt_of_prepHyp hprep
  let E : {j : Fin (alphaT r ℜ.α s) // 𝒮.eTilde s j ≠ ⊥} → Subscheme (𝒮.tHat.X s) :=
    fun i => 𝒮.eHat s (idxT ℜ.α s r i.1)
  have hE : (⨅ i, E i).IsReduced :=
    Subscheme.isReduced_iInf_of_forall_isNonsingular E fun i =>
      𝒮.isNonsingular_eHat s (idxT ℜ.α s r i.1)
  have h := Subscheme.isNonsingular_and_isEverywhereOfCodim_totalTransform_ι (E := E)
    (D := 𝒮.xBar s) (𝒮.isNonsingular_tHat_X s) hE
    (𝒮.hasOnlyNormalCrossingsWith_xBar_of_ne_bot s hadm)
    (𝒮.isTransversalFamilyWith_eHat_of_ne_bot s hadm) ⟨j, hj⟩
  have key : 𝒮.eTilde s j = Subscheme.totalTransform (𝒮.xBar s).ι (E ⟨j, hj⟩) := rfl
  rw [key]
  exact h

/-- Every trace `Ẽ_j` is the whole space `X̃` or a non-singular divisor. -/
theorem eTilde_eq_bot_or_isNonsingularDivisor [Hironaka.HironakaCitedResults.{u}] {s : ℕ} (hprep : PrepHyp N ℜ r ν T x₀ s)
    (j : Fin (alphaT r ℜ.α s)) : 𝒮.eTilde s j = ⊥ ∨ (𝒮.eTilde s j).IsNonsingularDivisor := by
  by_cases hj : 𝒮.eTilde s j = ⊥
  · exact Or.inl hj
  · exact Or.inr (𝒮.isNonsingular_and_isEverywhereOfCodim_eTilde_of_ne_bot hprep hj)

/-- The union of the emptied traces is the union of the kept ones. -/
theorem iInf_eTilde_emptyIfBot_eq (s : ℕ) :
    (⨅ j, (𝒮.eTilde s j).emptyIfBot) =
      ⨅ i : {j : Fin (alphaT r ℜ.α s) // 𝒮.eTilde s j ≠ ⊥}, 𝒮.eTilde s i.1 := by
  refine le_antisymm (le_iInf fun i => ?_) (le_iInf fun j => ?_)
  · exact (iInf_le _ i.1).trans (Subscheme.emptyIfBot_of_ne_bot i.2).le
  · by_cases hj : 𝒮.eTilde s j = ⊥
    · rw [Subscheme.emptyIfBot_of_eq_bot hj]
      exact le_top
    · rw [Subscheme.emptyIfBot_of_ne_bot hj]
      exact iInf_le (fun i : {j : Fin (alphaT r ℜ.α s) // 𝒮.eTilde s j ≠ ⊥} => 𝒮.eTilde s i.1)
        ⟨j, hj⟩

/-- **`Ẽ_1 ∪ ⋯ ∪ Ẽ_α̃` has only normal crossings on `X̃`** (p. 321), for the emptied traces and
without the hypothesis `F ≠ E_i`: the kept traces form a sub-family of transversal divisors of
`X̄_s` (`hasOnlyNormalCrossings_iInf_totalTransform_ι`), the others are empty. -/
theorem hasOnlyNormalCrossings_iInf_eTilde_emptyIfBot [Hironaka.HironakaCitedResults.{u}] {s : ℕ} (hprep : PrepHyp N ℜ r ν T x₀ s) :
    (⨅ j, (𝒮.eTilde s j).emptyIfBot).HasOnlyNormalCrossings := by
  have hadm := 𝒮.isAdmissibleAt_of_prepHyp hprep
  rw [iInf_eTilde_emptyIfBot_eq]
  let E : {j : Fin (alphaT r ℜ.α s) // 𝒮.eTilde s j ≠ ⊥} → Subscheme (𝒮.tHat.X s) :=
    fun i => 𝒮.eHat s (idxT ℜ.α s r i.1)
  have hE : (⨅ i, E i).IsReduced :=
    Subscheme.isReduced_iInf_of_forall_isNonsingular E fun i =>
      𝒮.isNonsingular_eHat s (idxT ℜ.α s r i.1)
  have h := Subscheme.hasOnlyNormalCrossings_iInf_totalTransform_ι (E := E)
    (D := 𝒮.xBar s) (𝒮.isNonsingular_tHat_X s) hE
    (𝒮.hasOnlyNormalCrossingsWith_xBar_of_ne_bot s hadm)
    (𝒮.isTransversalFamilyWith_eHat_of_ne_bot s hadm)
  have key : (⨅ i : {j : Fin (alphaT r ℜ.α s) // 𝒮.eTilde s j ≠ ⊥}, 𝒮.eTilde s i.1) =
      ⨅ i, Subscheme.totalTransform (𝒮.xBar s).ι (E i) := rfl
  rw [key]
  exact h

/-- **The auxiliary datum with the whole-space traces emptied is a weak datum** (p. 321, "the
datum `ℜ^{N-1}_II` is a resolution datum").  `b̃ > 0` and `J̃_x ≠ 0` are the remaining conditions
(i), (iii) of Def. 3 (II).  No hypothesis `F ≠ E_i`, and the irreducibility of the `Ẽ_j` is not
needed.

Deviation from the paper (proof corrected, repair of the paper's error on the subschemes `Ẽ_j`): the printed
sentence asserts that the `Ẽ_j` are non-singular irreducible of codimension one.  See
`isWeakDatum_datumTilde` and `isDatum_datumTilde`, which this replaces. -/
@[blueprint "lem:IV.4-tilde-facts-repaired"
  (statement := /-- Notation as in \cref{def:IV.4-conditions}, \cref{def:IV.4-tilde}. Let
    $\tilde b>0$ and let $\tilde J$ have non-zero stalks. Let $\tilde{\mathfrak R}^e$ be the
    datum $(\tilde E^e_1,\dots,\tilde E^e_{\tilde\alpha}\,|\,\tilde J,\tilde b\,|\,\tilde
    a_1,\dots,\tilde a_{\tilde\alpha})$ in which $\tilde E^e_j=\tilde E_j$ if $\tilde
    E_j\neq\tilde X$ and $\tilde E^e_j=\emptyset$ if $\tilde E_j=\tilde X$. Then every
    $\tilde E^e_j$ is empty or a non-singular subscheme of $\tilde X$ everywhere of codimension
    one, and $\tilde E^e_1\cup\dots\cup\tilde E^e_{\tilde\alpha}$ has only normal crossings
    on $\tilde X$. (Replaces p.~321: ``we see that $\tilde E_1,\dots,\tilde E_{\tilde\alpha}$
    are non-singular irreducible subschemes of $\bar X'_s$ of codimension 1, and that $\tilde
    E_1\cup\dots\cup\tilde E_{\tilde\alpha}$ has only normal crossings on $\bar
    X'_s$''.)

    \textbf{Deviation from the paper (proof corrected, repair of the paper's error on the subschemes $\tilde E_j$).} The
    printed sentence is false: the $\tilde E_j$ can be reducible and $\tilde E_i=\tilde X$ when
    $F=E_i$. -/)
  (proof := /-- A trace $\tilde E_j\neq\tilde X$ comes from a component $\hat E_j(s)$ which does
    not contain the irreducible $\bar X_s$ (otherwise $\tilde E_j$ would be the zero ideal sheaf,
    $\hat E_j(s)$ being reduced), so it is transversal to $\bar X_s$. The kept components form a
    sub-family of the family with only normal crossings with $\bar X_s$, and the generic lemma
    (\cref{lem:IV.4-tilde-facts-local}) applies to it; the union of the emptied traces is the union
    of the kept ones. -/)
  (latexEnv := "lemma")]
theorem isWeakDatum_emptyIfBot_datumTilde [Hironaka.HironakaCitedResults.{u}] {s : ℕ} (hprep : PrepHyp N ℜ r ν T x₀ s) (bt : ℕ)
    (a : Fin (alphaT r ℜ.α s) → ℕ) (Jt : Subscheme (𝒮.xTilde s)) (hbt : 0 < bt)
    (hJt : ∀ x, Jt.stalkIdeal x ≠ ⊥) : ((𝒮.datumTilde s bt a Jt).emptyIfBot).IsWeakDatum :=
  DatumII.Raw.isWeakDatum_emptyIfBot (ℜ := 𝒮.datumTilde s bt a Jt) hbt
    (fun j => 𝒮.eTilde_eq_bot_or_isNonsingularDivisor hprep j)
    (𝒮.hasOnlyNormalCrossings_iInf_eTilde_emptyIfBot hprep) hJt

end Frame

end CD

/-! ## 2. The order calculus for a weak datum

The stalks of the non-singular divisors of a weak datum are generated by an element of order `1`
(or are the unit ideal), so orders add up.  This is the content of "this is clear from the
definition of `J̄*(s)` and the fact that all the `Ẽ_j` are non-singular" (p. 323), for an arbitrary
weak datum. -/

namespace DatumII.Raw

variable {Y : Scheme.{u}}

/-- The stalks of the non-singular divisors of a weak datum are generated by one element of order
`1` (a member of a regular system of parameters), or are the unit ideal. -/
theorem exists_stalkIdeal_eq_top_or_span (D : Raw Y) (hY : Y.IsNonsingular) (hD : D.IsWeakDatum)
    (j : Fin D.α) (x : Y) :
    (D.E j).stalkIdeal x = ⊤ ∨
      ∃ p, Ideal.ordElem (maximalIdeal (Y.presheaf.stalk x)) p = 1 ∧
        (D.E j).stalkIdeal x = Ideal.span {p} := by
  classical
  have hreg : IsRegularLocalRing (Y.presheaf.stalk x) := hY x
  obtain ⟨Z, hZ, -, hE'⟩ := Hironaka.DatumTransform.exists_rsop_adapted_of_isNonsingularDivisor
    (B := ⊥) D.E hY hD.2.1 hD.2.2.1 (fun y _ => hD.2.2.1 y) x
  rcases hE' j with h | ⟨p, hpZ, hp⟩
  · exact Or.inl h
  · refine Or.inr ⟨p, ?_, hp⟩
    have hpM : p ∈ maximalIdeal (Y.presheaf.stalk x) := hZ.1 ▸ Ideal.subset_span hpZ
    have hp2 : p ∉ maximalIdeal (Y.presheaf.stalk x) ^ 2 := fun h2 =>
      rsop_notMem_span_erase_sup_sq hZ hpZ (Ideal.mem_sup_right h2)
    exact Ideal.ordElem_eq_one_of_mem_of_notMem_sq (maximalIdeal.isMaximal _).ne_top hpM hp2

open Classical in
/-- The product `∏_j (E_j)_x^{e_j}` of the stalks of the divisors of a weak datum is generated by
one element, of order `∑_{x ∈ E_j} e_j`. -/
theorem exists_prod_stalkIdeal_eq_span (D : Raw Y) (hY : Y.IsNonsingular) (hD : D.IsWeakDatum)
    (e : Fin D.α → ℕ) (x : Y) :
    ∃ u, (∏ j, ((D.E j).stalkIdeal x) ^ (e j)) = Ideal.span {u} ∧
      Ideal.ordElem (maximalIdeal (Y.presheaf.stalk x)) u =
        ((∑ j ∈ Finset.univ.filter fun j => x ∈ (D.E j).pts, e j : ℕ) : ℕ∞) := by
  have hreg : IsRegularLocalRing (Y.presheaf.stalk x) := hY x
  suffices h : ∀ t : Finset (Fin D.α), ∃ u,
      (∏ j ∈ t, ((D.E j).stalkIdeal x) ^ (e j)) = Ideal.span {u} ∧
        Ideal.ordElem (maximalIdeal (Y.presheaf.stalk x)) u =
          ((∑ j ∈ t.filter fun j => x ∈ (D.E j).pts, e j : ℕ) : ℕ∞) from h Finset.univ
  intro t
  induction t using Finset.induction_on with
  | empty =>
    refine ⟨1, by simp [Ideal.span_singleton_one], ?_⟩
    simp [Ideal.ordElem_eq_zero_of_isUnit isUnit_one]
  | insert j t hj ih =>
    obtain ⟨u, hu, hou⟩ := ih
    rcases exists_stalkIdeal_eq_top_or_span D hY hD j x with htop | ⟨p, hop, hp⟩
    · refine ⟨u, ?_, ?_⟩
      · rw [Finset.prod_insert hj, htop, Ideal.top_pow, hu, Ideal.top_mul]
      · have hx : x ∉ (D.E j).pts := fun hx =>
          Subscheme.mem_pts_iff_stalkIdeal_ne_top.mp hx htop
        rw [Finset.filter_insert, ite_eq_right hx]; exact hou
    · have hpnu : ¬ IsUnit p := by
        intro hunit
        have := Ideal.ordElem_eq_zero_of_isUnit hunit
        rw [hop] at this
        exact one_ne_zero this
      have hx : x ∈ (D.E j).pts := by
        rw [Subscheme.mem_pts_iff_stalkIdeal_ne_top, hp]
        intro htop
        rw [Ideal.span_singleton_eq_top] at htop
        exact hpnu htop
      refine ⟨p ^ (e j) * u, ?_, ?_⟩
      · rw [Finset.prod_insert hj, hp, hu, Ideal.span_singleton_pow,
          Ideal.span_singleton_mul_span_singleton]
      · rw [Finset.filter_insert, ite_eq_left hx, Finset.sum_insert (by simp [hj]),
          ordElem_mul_maximalIdeal, StableOrder.ordElem_pow_maximalIdeal, hop, hou]
        push_cast
        ring

open Classical in
/-- **`S(ℜ) = {x | ν(K_x) ≥ b}`** for a weak datum with `J ∏ E_j^{a_j} = K` (p. 323: "this is clear
from Definitions of Ch. I"): `ν(J_x ∏ (E_j)_x^{a_j}) = ν(J_x) + ∑_{x ∈ E_j} a_j`, the `E_j` being
non-singular divisors. -/
theorem S_eq_of_mul_prod_eq (D : Raw Y) (hY : Y.IsNonsingular) (hD : D.IsWeakDatum)
    (K : Subscheme Y) (hK : D.J * ∏ j, (D.E j) ^ (D.a j) = K) :
    D.S = {x | (D.b : ℕ∞) ≤ Ideal.nu (K.stalkIdeal x)} := by
  ext x
  have hreg : IsRegularLocalRing (Y.presheaf.stalk x) := hY x
  obtain ⟨u, hu, hou⟩ := exists_prod_stalkIdeal_eq_span D hY hD D.a x
  have hst : K.stalkIdeal x = (D.J.stalkIdeal x) * Ideal.span {u} := by
    rw [← hK, Subscheme.stalkIdeal_mul_eq, CD.stalkIdeal_prod_eq, ← hu]
    simp only [Subscheme.stalkIdeal_pow_eq]
  have hnu : Ideal.nu (K.stalkIdeal x) = Ideal.nu (D.J.stalkIdeal x) +
      ((∑ j ∈ Finset.univ.filter fun j => x ∈ (D.E j).pts, D.a j : ℕ) : ℕ∞) := by
    rw [hst, Ideal.nu_mul_span_singleton, hou]
  show (D.b : ℕ∞) ≤ ((∑ j ∈ Finset.univ.filter fun j => x ∈ (D.E j).pts, D.a j : ℕ) : ℕ∞) +
    Ideal.nu (D.J.stalkIdeal x) ↔ (D.b : ℕ∞) ≤ Ideal.nu (K.stalkIdeal x)
  rw [hnu, add_comm]

end DatumII.Raw

/-! ## 3. The shifted threshold and the repaired datum

Why the threshold is shifted: when some traces `Ẽ_j` are the whole
space `X̃` (closed case, `F = E_i`, `c_i > 0`), dropping them from `J̄*(s)` is not enough: the
generator `(∏_j P̃_j^{c_j})^{b̄}` of `J̄*(s)` vanishes (`P̃_i = 0`) and Remark 2 fails.  The weight
`δ_s = ∑_{Ẽ_j = X̃} c_j` of the dropped traces is carried by the threshold instead of `b - ν`:
`d_s = b - ν - δ_s`. -/

namespace CD

variable {X : Scheme.{u}} {N : ℕ} {ℜ : DatumII.Raw X} {r : Restriction X} {ν : ℕ}
  {T : AB.Tower X} {x₀ : X}

namespace Frame

variable {hS : Standing N ℜ r ν T x₀} (𝒮 : Frame hS)

open Classical in
/-- `δ_s`: the total exponent `∑ c_j` of the traces `Ẽ_j` which are the whole space `X̃` (this
happens exactly for the components `E_j(s) = F(s)`, when `F = E_i`; Definition 5 (II.1) allows it).
These traces are dropped from the auxiliary datum; their weight is carried by the threshold.
Constant along an extension of the succession (`droppedWeight_succ`). -/
noncomputable def droppedWeight (s : ℕ) : ℕ :=
  ∑ j ∈ Finset.univ.filter fun j => 𝒮.eTilde s j = ⊥, cT T ℜ r s j

/-- The shifted threshold `d_s = b - ν - δ_s` (truncated at `0`). -/
noncomputable def thresholdRep (s : ℕ) : ℕ := ℜ.b - ν - 𝒮.droppedWeight s

open Classical in
/-- The repaired sheaf of ideals `J̄*(s)` (p. 321 for `ν ≥ b`, p. 322 for `ν < b`): `J̄(s)` if
`b - ν - δ_s ≤ 0` (this covers `ν ≥ b`), and `(J̄(s)^{d_s}, (∏_j (Ẽ_j)^{c_j})^{b̄})` otherwise,
where the `Ẽ_j` equal to the whole space are replaced by the empty subscheme.  For `δ_s = 0` these
are the two printed definitions (`jBarRep_eq_jBar_of_le`, `jBarRep_eq_jBarStar`).

Why the shift: for `X = 𝔸³` with coordinates `(x, y, w)`, `ℜ = (V(x), V(w) | (x² + y²), 4 | 1, 1)` and
`F = V(x) = E₁` one has `ν = 2 < b = 4`, `J̄(0) = (y²)`, `Ẽ₁ = X̃`, `Ẽ₂ = V(w)`; the printed
`J̄*(0) = (y⁴)`, `b̃ = 4` gives `S(ℜ^{N-1}_II)` = the whole formal `w`-axis, whereas `δ_s = 1`, `d_s = 1`
gives `J̃ = (y², w²)`, `b̃ = 2` and `S = {x̂₀}`.  The full example is in the docstring of
`Frame.S_datumTilde_eq_and_bijOn_cBar_and_exists_isPermissibleCenter_of_lt` (`rem:IV.4-2`). -/
@[blueprint "def:IV.4-case-lt-repaired"
  (statement := /-- \emph{The case $\nu<b$, repaired} (replaces the definition of $\bar J^*(s)$ and
    of $\tilde b$ on p.~322, \cref{def:IV.4-case-lt}; for $\nu\ge b$ it replaces $\tilde J=\bar
    J(s)$, $\tilde b=\bar b$ of p.~321, \cref{def:IV.4-case-ge}). Let $\tilde E_j$ be as in
    \cref{def:IV.4-tilde}. Let $\delta_s=\sum c_j$ be the sum over those $j$ with $\tilde
    E_j=\tilde X$ (the whole space; this occurs for the components $E_j(s)=F(s)$ when $F=E_i$),
    and $d_s=\max(b-\nu-\delta_s,0)$. Let $\tilde E^e_j=\emptyset$ if $\tilde E_j=\tilde X$ and
    $\tilde E^e_j=\tilde E_j$ otherwise. If $d_s=0$ (in particular if $\nu\ge b$) put
    $\bar J^\sharp(s)=\bar J(s)$ and $\tilde b=\bar b$; if $d_s>0$ put $\bar J^\sharp(s)=\big(\bar
    J(s)^{d_s},(\prod_{j=1}^{\tilde\alpha}(\tilde P^e_j)^{c_j})^{\bar b}\big)$ and $\tilde
    b=\bar b\,d_s$, where $\tilde P^e_j$ is the sheaf of ideals of $\tilde E^e_j$. The resolution
    datum $\tilde{\mathfrak R}^e=(\tilde E^e_1,\dots,\tilde E^e_{\tilde\alpha}\,|\,\tilde J,
    \tilde b\,
    |\,\tilde a_1,\dots,\tilde a_{\tilde\alpha})$ on $\tilde X$ has $\tilde J\prod_j(\tilde
    P^e_j)^{\tilde a_j}=\bar J^\sharp(s)$ and $\tilde a_j=0$ for $\tilde E_j=\tilde X$. If no
    $\tilde E_j$ equals $\tilde X$ (for instance without restriction) then $\delta_s=0$ and this is
    the printed definition.

    \textbf{Deviation from the paper (proof corrected, repair of the paper's error on the subschemes $\tilde E_j$).} On
    p.~322 the paper puts $\bar J^*(s)=\big(\bar J(s)^{b-\nu},(\prod_j\tilde P_j^{c_j})^{\bar
    b}\big)$ and $\tilde b=\bar b(b-\nu)$. If some $\tilde E_i=\tilde X$ with $c_i>0$ (closed
    case, $F=E_i$, $a_i>0$), the ideal sheaf $\tilde P_i$ is zero, so the second generator of
    $\bar J^*(s)$ vanishes and Remark~2 (p.~323) fails: dropping $\tilde E_i$ from the datum
    without shifting the threshold loses the weight $c_i$ of $E_i(s)$ in $b-\nu\le\sum
    c_j$. The weight of the dropped traces is therefore subtracted from $b-\nu$. For example, for
    $X=\mathbb A^3$ with coordinates $(x,y,w)$, $\mathfrak R=(V(x),V(w)\,|\,(x^2+y^2),4\,|\,1,1)$
    and $F=V(x)=E_1$: $\nu=2<b=4$, $\bar J(0)=(y^2)$, $\tilde E_1=\tilde X$, $\tilde E_2=V(w)$, and
    the printed $\bar J^*(0)=(y^4)$, $\tilde b=4$ has $S(\mathfrak R^{N-1}_{\mathrm{II}})$ equal to
    the whole formal $w$-axis, whereas the shifted threshold ($\delta_s=1$, $d_s=1$) gives
    $\tilde J=(y^2,w^2)$, $\tilde b=2$ and $S=\{\hat x_0\}$ (the full example is at
    \cref{rem:IV.4-2}). -/)
  (latexEnv := "definition")]
noncomputable def jBarRep (s : ℕ) : Subscheme (𝒮.xTilde s) :=
  if 𝒮.thresholdRep s = 0 then 𝒮.jBar s
  else (𝒮.jBar s) ^ (𝒮.thresholdRep s) +
    (∏ j, ((𝒮.eTilde s j).emptyIfBot) ^ (cT T ℜ r s j)) ^ 𝒮.bBar

/-- The integer `b̃`: `b̄` if the threshold is `0`, `b̄ · d_s` otherwise (`b̄ (b - ν)` for `δ_s = 0`
and `ν < b`; `b̄` for `ν ≥ b`). -/
noncomputable def bTildeRep (s : ℕ) : ℕ :=
  if 𝒮.thresholdRep s = 0 then 𝒮.bBar else 𝒮.bBar * 𝒮.thresholdRep s

open Classical in
/-- The exponents of the repaired datum: those of the traces equal to the whole space are `0`
(the paper's choice, forced by `J̄(s) ≠ 0`; irrelevant for the emptied entries). -/
noncomputable def aRep (s : ℕ) (a : Fin (alphaT r ℜ.α s) → ℕ) : Fin (alphaT r ℜ.α s) → ℕ :=
  fun j => if 𝒮.eTilde s j = ⊥ then 0 else a j

/-- **The repaired auxiliary datum** `ℜ̃ = (Ẽ^e_1, …, Ẽ^e_α̃ | J̃, b̃ | ã_1, …, ã_α̃)`: the entries
equal to the whole space `X̃` are replaced by the empty subscheme, `b̃ = bTildeRep s`. -/
noncomputable def datumRep (s : ℕ) (a : Fin (alphaT r ℜ.α s) → ℕ) (Jt : Subscheme (𝒮.xTilde s)) :
    DatumII.Raw (𝒮.xTilde s) :=
  (𝒮.datumTilde s (𝒮.bTildeRep s) (𝒮.aRep s a) Jt).emptyIfBot

variable {𝒮}

theorem thresholdRep_eq_zero_of_le {s : ℕ} (hge : ℜ.b ≤ ν) : 𝒮.thresholdRep s = 0 := by
  unfold thresholdRep; omega

theorem jBarRep_eq_of_thresholdRep_eq_zero {s : ℕ} (h : 𝒮.thresholdRep s = 0) :
    𝒮.jBarRep s = 𝒮.jBar s := by
  unfold jBarRep; simp only [h, ↓reduceIte]

theorem bTildeRep_eq_of_thresholdRep_eq_zero {s : ℕ} (h : 𝒮.thresholdRep s = 0) :
    𝒮.bTildeRep s = 𝒮.bBar := by
  unfold bTildeRep; simp only [h, ↓reduceIte]

theorem jBarRep_eq_of_thresholdRep_ne_zero {s : ℕ} (h : 𝒮.thresholdRep s ≠ 0) :
    𝒮.jBarRep s = (𝒮.jBar s) ^ (𝒮.thresholdRep s) +
      (∏ j, ((𝒮.eTilde s j).emptyIfBot) ^ (cT T ℜ r s j)) ^ 𝒮.bBar := by
  unfold jBarRep; simp only [h, ↓reduceIte]

theorem bTildeRep_eq_of_thresholdRep_ne_zero {s : ℕ} (h : 𝒮.thresholdRep s ≠ 0) :
    𝒮.bTildeRep s = 𝒮.bBar * 𝒮.thresholdRep s := by
  unfold bTildeRep; simp only [h, ↓reduceIte]

/-- For `ν ≥ b`: `J̃ = J̄(s)`, `b̃ = b̄` (p. 321). -/
theorem jBarRep_eq_jBar_of_le {s : ℕ} (hge : ℜ.b ≤ ν) :
    𝒮.jBarRep s = 𝒮.jBar s ∧ 𝒮.bTildeRep s = 𝒮.bBar :=
  ⟨jBarRep_eq_of_thresholdRep_eq_zero (thresholdRep_eq_zero_of_le hge),
    bTildeRep_eq_of_thresholdRep_eq_zero (thresholdRep_eq_zero_of_le hge)⟩

/-- For `ν < b` and no weight on the dropped traces (in particular if nothing is dropped, e.g.
without restriction): the printed `J̄*(s)` and `b̃ = b̄ (b - ν)` (p. 322). -/
theorem jBarRep_eq_jBarStar {s : ℕ} (hδ : 𝒮.droppedWeight s = 0) (hlt : ν < ℜ.b) :
    𝒮.jBarRep s = 𝒮.jBarStar s ∧ 𝒮.bTildeRep s = 𝒮.bBar * (ℜ.b - ν) := by
  have hd : 𝒮.thresholdRep s = ℜ.b - ν := by unfold thresholdRep; rw [hδ]; rfl
  have hne : 𝒮.thresholdRep s ≠ 0 := by rw [hd]; omega
  refine ⟨?_, ?_⟩
  · rw [jBarRep_eq_of_thresholdRep_ne_zero hne, hd]
    unfold jBarStar
    congr 2
    refine Finset.prod_congr rfl fun j _ => ?_
    by_cases hj : 𝒮.eTilde s j = ⊥
    · have hc : cT T ℜ r s j = 0 := by
        unfold droppedWeight at hδ
        exact (Finset.sum_eq_zero_iff.mp hδ) j (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩)
      rw [hc, pow_zero, pow_zero]
    · rw [Subscheme.emptyIfBot_of_ne_bot hj]
  · rw [bTildeRep_eq_of_thresholdRep_ne_zero hne, hd]

open Classical in
/-- The weights of the traces through a point: the dropped traces contain every point. -/
theorem sum_filter_mem_pts_eTilde_eq {s : ℕ} (x : 𝒮.xTilde s) (e : Fin (alphaT r ℜ.α s) → ℕ) :
    (∑ j ∈ Finset.univ.filter fun j => x ∈ (𝒮.eTilde s j).pts, e j) =
      (∑ j ∈ Finset.univ.filter fun j => x ∈ ((𝒮.eTilde s j).emptyIfBot).pts, e j) +
        ∑ j ∈ Finset.univ.filter fun j => 𝒮.eTilde s j = ⊥, e j := by
  rw [Finset.sum_filter, Finset.sum_filter, Finset.sum_filter, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  by_cases hj : 𝒮.eTilde s j = ⊥
  · have hx : x ∈ (𝒮.eTilde s j).pts := by rw [hj]; exact Subscheme.mem_pts_bot x
    have hx' : x ∉ ((𝒮.eTilde s j).emptyIfBot).pts := by
      rw [Subscheme.pts_emptyIfBot_eq_empty hj]; exact Set.notMem_empty x
    have h1 : (if x ∈ (𝒮.eTilde s j).pts then e j else 0) = e j := by simp only [hx, ↓reduceIte]
    have h2 : (if x ∈ ((𝒮.eTilde s j).emptyIfBot).pts then e j else 0) = 0 := by
      simp only [hx', ↓reduceIte]
    have h3 : (if 𝒮.eTilde s j = ⊥ then e j else 0) = e j := by simp only [hj, ↓reduceIte]
    rw [h1, h2, h3, zero_add]
  · rw [Subscheme.pts_emptyIfBot_of_ne_bot hj]
    have h3 : (if 𝒮.eTilde s j = ⊥ then e j else 0) = 0 := by simp only [hj, ↓reduceIte]
    rw [h3, add_zero]

/-- The weight of the dropped traces is at most the weight of the traces through any point. -/
theorem droppedWeight_le_sum_filter {s : ℕ} (x : 𝒮.xTilde s) :
    𝒮.droppedWeight s ≤ ∑ j ∈ Finset.univ.filter fun j => x ∈ (𝒮.eTilde s j).pts,
      cT T ℜ r s j := by
  classical
  unfold droppedWeight
  refine Finset.sum_le_sum_of_subset fun j hj => ?_
  have hj' := (Finset.mem_filter.mp hj).2
  refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
  rw [hj']
  exact Subscheme.mem_pts_bot x

end Frame

end CD

/-! ## 4. `b̃ ≤ ν(J̄*(s)_x)` iff (a) and (b), and `S(ℜ̃)` -/

namespace CD

variable {X : Scheme.{u}} {N : ℕ} {ℜ : DatumII.Raw X} {r : Restriction X} {ν : ℕ}
  {T : AB.Tower X} {x₀ : X}

namespace Frame

variable {hS : Standing N ℜ r ν T x₀} {𝒮 : Frame hS}

open Classical in
/-- **`b̃ ≤ ν(J̃_x)` iff (a) and (b)**, for the repaired `J̃ = J̄*(s)` (p. 323: "`x̂ ∈
S(ℜ^{N-1}_II)` if and only if (a) `ν(J̄(s)_x̂) ≥ b̄`, and (b) `∑_{x̂ ∈ Ẽ_j} c_j ≥ b - ν`; this is
clear
from the definition of `J̄*(s)` and the fact that all the `Ẽ_j` are non-singular").

Deviation from the paper (proof corrected, repair of the paper's error on the subschemes `Ẽ_j`): the sum in (b) runs
over all `j` with `x̂ ∈ Ẽ_j`, the traces equal to `X̃` included (they contain every point).  The
threshold `b̃` is the shifted one (`bTildeRep`), and `J̃ = jBarRep`; the equivalence is the
additivity
of the order in the regular local ring `O_{X̃,x̂}`, applied to the kept traces only. -/
theorem le_nu_jBarRep_iff {s : ℕ} (hadm : 𝒮.IsAdmissibleAt s) {bt : ℕ}
    {a : Fin (alphaT r ℜ.α s) → ℕ} {Jt : Subscheme (𝒮.xTilde s)}
    (hII : ((𝒮.datumTilde s bt a Jt).emptyIfBot).IsWeakDatum) (x : 𝒮.xTilde s) :
    ((𝒮.bTildeRep s : ℕ) : ℕ∞) ≤ Ideal.nu ((𝒮.jBarRep s).stalkIdeal x) ↔
      ((𝒮.bBar : ℕ) : ℕ∞) ≤ Ideal.nu ((𝒮.jBar s).stalkIdeal x) ∧
        ℜ.b - ν ≤ ∑ j ∈ Finset.univ.filter fun j => x ∈ (𝒮.eTilde s j).pts, cT T ℜ r s j := by
  have hreg : IsRegularLocalRing ((𝒮.xTilde s).presheaf.stalk x) := hadm.1.1 x
  have hb1 : 1 ≤ 𝒮.bBar := Nat.factorial_pos ν
  have hsum := sum_filter_mem_pts_eTilde_eq (𝒮 := 𝒮) x (cT T ℜ r s)
  have hδW := droppedWeight_le_sum_filter (𝒮 := 𝒮) (s := s) x
  by_cases hd : 𝒮.thresholdRep s = 0
  · rw [jBarRep_eq_of_thresholdRep_eq_zero hd, bTildeRep_eq_of_thresholdRep_eq_zero hd]
    have : ℜ.b - ν ≤ ∑ j ∈ Finset.univ.filter fun j => x ∈ (𝒮.eTilde s j).pts,
        cT T ℜ r s j := by
      unfold thresholdRep at hd
      omega
    exact ⟨fun h => ⟨h, this⟩, fun h => h.1⟩
  · obtain ⟨u, hu, hou⟩ := DatumII.Raw.exists_prod_stalkIdeal_eq_span
      (𝒮.datumTilde s bt a Jt).emptyIfBot hadm.1.1 hII (cT T ℜ r s) x
    set M := maximalIdeal ((𝒮.xTilde s).presheaf.stalk x) with hM
    set k := 𝒮.thresholdRep s with hk
    have hk1 : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr hd
    set w := ∑ j ∈ Finset.univ.filter fun j => x ∈ ((𝒮.eTilde s j).emptyIfBot).pts,
      cT T ℜ r s j with hw
    have hou' : Ideal.ordElem M u = (w : ℕ∞) := hou
    have hst : (𝒮.jBarRep s).stalkIdeal x =
        ((𝒮.jBar s).stalkIdeal x) ^ k ⊔ (Ideal.span {u ^ 𝒮.bBar}) := by
      rw [jBarRep_eq_of_thresholdRep_ne_zero hd, Scheme.IdealSheafData.add_eq_sup,
        Subscheme.stalkIdeal_sup_eq, Subscheme.stalkIdeal_pow_eq, Subscheme.stalkIdeal_pow_eq,
        stalkIdeal_prod_eq, ← Ideal.span_singleton_pow]
      simp only [Subscheme.stalkIdeal_pow_eq]
      rw [show (∏ j, ((𝒮.eTilde s j).emptyIfBot).stalkIdeal x ^ cT T ℜ r s j) =
        Ideal.span {u} from hu]
    have hiff : ∀ (n : ℕ) (I K : Ideal ((𝒮.xTilde s).presheaf.stalk x)),
        (n : ℕ∞) ≤ Ideal.nu (I ⊔ K) ↔ (n : ℕ∞) ≤ Ideal.nu I ∧ (n : ℕ∞) ≤ Ideal.nu K := by
      intro n I K
      constructor
      · intro h
        have h1 := Ideal.le_pow_of_le_ord h
        exact ⟨Ideal.le_ord (le_sup_left.trans h1), Ideal.le_ord (le_sup_right.trans h1)⟩
      · rintro ⟨h1, h2⟩
        exact Ideal.le_ord (sup_le (Ideal.le_pow_of_le_ord h1) (Ideal.le_pow_of_le_ord h2))
    rw [bTildeRep_eq_of_thresholdRep_ne_zero hd, hst, hiff]
    have hK : ((𝒮.bBar * k : ℕ) : ℕ∞) ≤ Ideal.nu (Ideal.span {u ^ 𝒮.bBar}) ↔ k ≤ w := by
      rw [Ideal.nu, Ideal.ord_span_singleton, StableOrder.ordElem_pow_maximalIdeal, hou']
      have : ((𝒮.bBar : ℕ) : ℕ∞) * ((w : ℕ) : ℕ∞) = ((𝒮.bBar * w : ℕ) : ℕ∞) := by
        push_cast; ring
      rw [this]
      exact_mod_cast Nat.mul_le_mul_left_iff (by omega : 0 < 𝒮.bBar)
    have hJ : ((𝒮.bBar * k : ℕ) : ℕ∞) ≤ Ideal.nu (((𝒮.jBar s).stalkIdeal x) ^ k) ↔
        ((𝒮.bBar : ℕ) : ℕ∞) ≤ Ideal.nu ((𝒮.jBar s).stalkIdeal x) := by
      constructor
      · intro h
        have h1 := Ideal.nu_pow_le ((𝒮.jBar s).stalkIdeal x) k
        by_cases hJt : Ideal.nu ((𝒮.jBar s).stalkIdeal x) = ⊤
        · rw [hJt]; exact le_top
        obtain ⟨m, hm⟩ : ∃ m : ℕ, Ideal.nu ((𝒮.jBar s).stalkIdeal x) = m :=
          ⟨_, (ENat.natCast_toNat hJt).symm⟩
        rw [hm] at h1 ⊢
        have h2 : ((𝒮.bBar * k : ℕ) : ℕ∞) ≤ ((k * m : ℕ) : ℕ∞) := by
          push_cast; exact h.trans h1
        have h3 : 𝒮.bBar * k ≤ k * m := by exact_mod_cast h2
        exact_mod_cast Nat.le_of_mul_le_mul_left (by linarith) (by omega : 0 < k)
      · intro h
        refine Ideal.le_ord ?_
        calc ((𝒮.jBar s).stalkIdeal x) ^ k ≤ (M ^ 𝒮.bBar) ^ k :=
              Ideal.pow_right_mono (Ideal.le_pow_of_le_ord h) k
          _ = M ^ (𝒮.bBar * k) := (pow_mul M 𝒮.bBar k).symm
    rw [hJ, hK]
    have hkd : k = ℜ.b - ν - 𝒮.droppedWeight s := rfl
    have hδ : 𝒮.droppedWeight s =
        ∑ j ∈ Finset.univ.filter fun j => 𝒮.eTilde s j = ⊥, cT T ℜ r s j := rfl
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨h1, ?_⟩
      omega
    · rintro ⟨h1, h2⟩
      refine ⟨h1, ?_⟩
      omega

end Frame

end CD

/-! ## 4b. The repaired datum is a weak datum, and `S(ℜ̃)` -/

namespace CD

variable {X : Scheme.{u}} {N : ℕ} {ℜ : DatumII.Raw X} {r : Restriction X} {ν : ℕ}
  {T : AB.Tower X} {x₀ : X}

namespace Frame

variable {hS : Standing N ℜ r ν T x₀} {𝒮 : Frame hS}

open Classical in
/-- The exponents of the dropped traces are irrelevant in the factorization `J̃ ∏ Ẽ_j^{a_j}`. -/
theorem prod_emptyIfBot_pow_aRep (s : ℕ) (a : Fin (alphaT r ℜ.α s) → ℕ) :
    (∏ j, ((𝒮.eTilde s j).emptyIfBot) ^ (𝒮.aRep s a j)) =
      ∏ j, ((𝒮.eTilde s j).emptyIfBot) ^ (a j) := by
  refine Finset.prod_congr rfl fun j _ => ?_
  by_cases hj : 𝒮.eTilde s j = ⊥
  · have hn : ∀ n : ℕ, ((𝒮.eTilde s j).emptyIfBot) ^ n = ⊤ := fun n => by
      rw [Subscheme.emptyIfBot_of_eq_bot hj]
      exact one_pow n
    rw [hn, hn]
  · have : 𝒮.aRep s a j = a j := by unfold aRep; simp only [hj, ↓reduceIte]
    rw [this]

theorem bTildeRep_pos (s : ℕ) : 0 < 𝒮.bTildeRep s := by
  by_cases hd : 𝒮.thresholdRep s = 0
  · rw [bTildeRep_eq_of_thresholdRep_eq_zero hd]; exact Nat.factorial_pos ν
  · rw [bTildeRep_eq_of_thresholdRep_ne_zero hd]
    exact Nat.mul_pos (Nat.factorial_pos ν) (Nat.pos_of_ne_zero hd)

/-- The datum `ℜ̃` with the whole-space traces emptied is a weak datum (p. 321), as soon as `J̃` has
non-zero stalks. -/
theorem isWeakDatum_datumRep [Hironaka.HironakaCitedResults.{u}] {s : ℕ} (hprep : PrepHyp N ℜ r ν T x₀ s)
    (a : Fin (alphaT r ℜ.α s) → ℕ) (Jt : Subscheme (𝒮.xTilde s))
    (hJt : ∀ x, Jt.stalkIdeal x ≠ ⊥) : (𝒮.datumRep s a Jt).IsWeakDatum :=
  𝒮.isWeakDatum_emptyIfBot_datumTilde hprep _ _ Jt (bTildeRep_pos s) hJt

/-- The stalks of the repaired `J̄*(s)` are non-zero (the paper presupposes that `J̄(s)_x ≠ 0`,
Definition 3 (II) (iii)): for a positive threshold `d_s` they contain the `b̄`-th power of the
product of the (principal, non-zero) stalks of the kept traces; for `d_s = 0` this is the
hypothesis `hJ` on `J̄(s)` itself. -/
theorem stalkIdeal_jBarRep_ne_bot [Hironaka.HironakaCitedResults.{u}] {s : ℕ} (hprep : PrepHyp N ℜ r ν T x₀ s)
    (hJ : 𝒮.thresholdRep s = 0 → ∀ x, (𝒮.jBar s).stalkIdeal x ≠ ⊥) (x : 𝒮.xTilde s) :
    (𝒮.jBarRep s).stalkIdeal x ≠ ⊥ := by
  classical
  have hadm := 𝒮.isAdmissibleAt_of_prepHyp hprep
  by_cases hd : 𝒮.thresholdRep s = 0
  · rw [jBarRep_eq_of_thresholdRep_eq_zero hd]
    exact hJ hd x
  · have hII := 𝒮.isWeakDatum_emptyIfBot_datumTilde hprep 1 (fun _ => 0) ⊤ Nat.one_pos
      (fun x => by rw [Subscheme.stalkIdeal_top_eq]; exact top_ne_bot)
    have hreg : IsRegularLocalRing ((𝒮.xTilde s).presheaf.stalk x) := hadm.1.1 x
    obtain ⟨u, hu, hou⟩ := DatumII.Raw.exists_prod_stalkIdeal_eq_span
      (𝒮.datumTilde s 1 (fun _ => 0) ⊤).emptyIfBot hadm.1.1 hII (cT T ℜ r s) x
    have hu0 : u ≠ 0 := by
      intro h0
      rw [h0, Ideal.ordElem_eq_top_iff.mpr fun n => zero_mem _] at hou
      exact ENat.top_ne_natCast _ hou
    have hst : (𝒮.jBarRep s).stalkIdeal x =
        ((𝒮.jBar s).stalkIdeal x) ^ (𝒮.thresholdRep s) ⊔ (Ideal.span {u ^ 𝒮.bBar}) := by
      rw [jBarRep_eq_of_thresholdRep_ne_zero hd, Scheme.IdealSheafData.add_eq_sup,
        Subscheme.stalkIdeal_sup_eq, Subscheme.stalkIdeal_pow_eq, Subscheme.stalkIdeal_pow_eq,
        stalkIdeal_prod_eq, ← Ideal.span_singleton_pow]
      simp only [Subscheme.stalkIdeal_pow_eq]
      rw [show (∏ j, ((𝒮.eTilde s j).emptyIfBot).stalkIdeal x ^ cT T ℜ r s j) =
        Ideal.span {u} from hu]
    intro hbot
    have h1 : Ideal.span {u ^ 𝒮.bBar} ≤ ⊥ := by
      rw [← hbot, hst]; exact le_sup_right
    have h2 : u ^ 𝒮.bBar = 0 := by
      have := h1 (Ideal.mem_span_singleton_self _)
      simpa using this
    have := isDomain_of_isRegularLocalRing ((𝒮.xTilde s).presheaf.stalk x)
    exact hu0 (pow_eq_zero_iff (Nat.factorial_pos ν).ne' |>.mp h2)

/-- **`S(ℜ̃) = {x ∈ X̃ | ν(J̄*(s)_x) ≥ b̃}`** for the repaired datum (p. 323: "This is clear from
Definitions of Ch. I"). 

Deviation from the paper (proof corrected, repair of the paper's error on the subschemes `Ẽ_j`): the
statement is proved for the repaired datum `datumRep`. -/
theorem S_datumRep_eq [Hironaka.HironakaCitedResults.{u}] {s : ℕ} (hprep : PrepHyp N ℜ r ν T x₀ s)
    {a : Fin (alphaT r ℜ.α s) → ℕ} {Jt : Subscheme (𝒮.xTilde s)}
    (hJt : Jt * ∏ j, ((𝒮.eTilde s j).emptyIfBot) ^ (a j) = 𝒮.jBarRep s)
    (hJne : ∀ x, Jt.stalkIdeal x ≠ ⊥) :
    (𝒮.datumRep s a Jt).S =
      {x | ((𝒮.bTildeRep s : ℕ) : ℕ∞) ≤ Ideal.nu ((𝒮.jBarRep s).stalkIdeal x)} := by
  have hadm := 𝒮.isAdmissibleAt_of_prepHyp hprep
  refine DatumII.Raw.S_eq_of_mul_prod_eq (𝒮.datumRep s a Jt) hadm.1.1
    (𝒮.isWeakDatum_datumRep hprep a Jt hJne) (𝒮.jBarRep s) ?_
  show Jt * ∏ j, ((𝒮.eTilde s j).emptyIfBot) ^ (𝒮.aRep s a j) = _
  rw [prod_emptyIfBot_pow_aRep]
  exact hJt

end Frame

end CD

/-! ## 5. The bijection `S(ℜ̃) → S_ν(ℜ(s)) ∩ h_s⁻¹(x_0)` (Remarks 1 and 2, uniform in `ν`) -/

namespace CD

variable {X : Scheme.{u}} {N : ℕ} {ℜ : DatumII.Raw X} {r : Restriction X} {ν : ℕ}
  {T : AB.Tower X} {x₀ : X}

namespace Frame

variable {hS : Standing N ℜ r ν T x₀} {𝒮 : Frame hS}

open Classical in
/-- **`c̄_s` maps `S(ℜ̃)` into `S_ν(ℜ(s)) ∩ h_s⁻¹(x_0)`** (p. 323: "By Lemma (CD.5), (a) implies
`ν(J(s)_x) ≥ ν`, and (b) implies `∑_{x ∈ E_j(s)} a_j ≥ b - ν`; therefore `x ∈ S_ν(ℜ^N_II(s))`, and
in
the closed case `x ∈ F(s)`; and `[(1)]` gives `x ∈ h_s⁻¹(x_0)`"; for `ν ≥ b` p. 322, Remark 1).

Deviation from the paper (proof corrected, repair of the paper's error on the subschemes `Ẽ_j`): one statement for all
`ν`; the sum in (b) includes the dropped traces. -/
theorem cBar_mem_sNu_and_hBar_eq_of_mem_S_datumRep [Hironaka.HironakaCitedResults.{u}] {s : ℕ} (hprep : PrepHyp N ℜ r ν T x₀ s)
    {a : Fin (alphaT r ℜ.α s) → ℕ} {Jt : Subscheme (𝒮.xTilde s)}
    (hJt : Jt * ∏ j, ((𝒮.eTilde s j).emptyIfBot) ^ (a j) = 𝒮.jBarRep s)
    (hJne : ∀ x, Jt.stalkIdeal x ≠ ⊥) {xb : 𝒮.xTilde s} (hxb : xb ∈ (𝒮.datumRep s a Jt).S) :
    (𝒮.cBar s).base xb ∈ (datum T ℜ s).sNu ν ∧
      (𝒮.cBar s).base xb ∈ sNu (datum T ℜ s) (restriction T r s) ν ∧
      (T.pre s).composite.base ((𝒮.cBar s).base xb) = x₀ := by
  have hadm := 𝒮.isAdmissibleAt_of_prepHyp hprep
  have hII := 𝒮.isWeakDatum_emptyIfBot_datumTilde hprep (𝒮.bTildeRep s) (𝒮.aRep s a) Jt
    (bTildeRep_pos s) hJne
  rw [S_datumRep_eq hprep hJt hJne] at hxb
  obtain ⟨ha, hb⟩ := (le_nu_jBarRep_iff hadm hII xb).mp hxb
  have hν : (ν : ℕ∞) ≤ (datum T ℜ s).nuAt ((𝒮.cBar s).base xb) :=
    𝒮.le_nuAt_cBar_of_bBar_le_nu s hadm.2.2.1 xb ha
  have hw := 𝒮.weightC_le_weight_cBar xb
  have hS : (𝒮.cBar s).base xb ∈ (datum T ℜ s).S := by
    show ((datum T ℜ s).b : ℕ∞) ≤ ((datum T ℜ s).weight ((𝒮.cBar s).base xb) : ℕ∞) +
      (datum T ℜ s).nuAt ((𝒮.cBar s).base xb)
    rw [b_datum]
    have h1 : (ℜ.b : ℕ∞) ≤ ((ℜ.b - ν : ℕ) : ℕ∞) + (ν : ℕ∞) := by
      rw [← Nat.cast_add]; exact_mod_cast (by omega : ℜ.b ≤ ℜ.b - ν + ν)
    refine h1.trans (add_le_add ?_ hν)
    exact_mod_cast hb.trans hw
  have hsN : (𝒮.cBar s).base xb ∈ (datum T ℜ s).sNu ν := ⟨hS, hν⟩
  have hsN' : (𝒮.cBar s).base xb ∈ sNu (datum T ℜ s) (restriction T r s) ν :=
    mem_sNu_of_mem_sNu_of_forall_closed _ hsN fun F hF => 𝒮.cBar_mem_pts_of_closed hprep hF xb
  exact ⟨hsN, hsN', 𝒮.hBar_cBar_eq_of_mem_sNu hprep xb hsN'⟩

open Classical in
/-- **`c̄_s : S(ℜ̃) → S_ν(ℜ(s)) ∩ h_s⁻¹(x_0)` is a bijection** (p. 323: "Conversely, for
`x ∈ S_ν(ℜ(s)) ∩ h_s⁻¹(x_0)`, Lemma (CD.3) gives a unique `x̂` with `c_s(x̂) = x`, and the Corollary
of
Lemma (CD.4) gives `x̂ ∈ X̃` and (a).  Since `ν = ν(ℜ) ≥ ν(ℜ(s))`, `ν(J(s)_x) = ν`, so
`ν + ∑_{x ∈ E_j(s)} a_j ≥ b`, and (b) follows (in the unrestricted case using [(2)])"), for the
repaired datum and every `ν`. 

Deviation from the paper (proof corrected, repair of the paper's error on the subschemes `Ẽ_j`): the
statement is proved for the repaired datum `datumRep`. -/
theorem bijOn_cBar_S_datumRep [Hironaka.HironakaCitedResults.{u}] {s : ℕ} (hprep : PrepHyp N ℜ r ν T x₀ s)
    {a : Fin (alphaT r ℜ.α s) → ℕ} {Jt : Subscheme (𝒮.xTilde s)}
    (hJt : Jt * ∏ j, ((𝒮.eTilde s j).emptyIfBot) ^ (a j) = 𝒮.jBarRep s)
    (hJne : ∀ x, Jt.stalkIdeal x ≠ ⊥) :
    Set.BijOn (𝒮.cBar s).base (𝒮.datumRep s a Jt).S
      (sNu (datum T ℜ s) (restriction T r s) ν ∩ (T.pre s).composite.base ⁻¹' {x₀}) := by
  have hadm := 𝒮.isAdmissibleAt_of_prepHyp hprep
  have hII := 𝒮.isWeakDatum_emptyIfBot_datumTilde hprep (𝒮.bTildeRep s) (𝒮.aRep s a) Jt
    (bTildeRep_pos s) hJne
  have hCD3 := (hS.bijOn_and_mapsRSOP_and_exists_unique_totalTransform 𝒮.toCompletion s).1
  refine ⟨fun xb hxb => ?_, fun xb hxb xb' hxb' hEq => ?_, fun x hx => ?_⟩
  · obtain ⟨-, h2, h3⟩ := cBar_mem_sNu_and_hBar_eq_of_mem_S_datumRep hprep hJt hJne hxb
    exact ⟨h2, h3⟩
  · obtain ⟨-, -, h3⟩ := cBar_mem_sNu_and_hBar_eq_of_mem_S_datumRep hprep hJt hJne hxb
    obtain ⟨-, -, h3'⟩ := cBar_mem_sNu_and_hBar_eq_of_mem_S_datumRep hprep hJt hJne hxb'
    have h4 := 𝒮.hHat_eq_xh_of_hBar_eq xb h3
    have h4' := 𝒮.hHat_eq_xh_of_hBar_eq xb' h3'
    have h5 : (𝒮.xBar s).ι.base xb = (𝒮.xBar s).ι.base xb' :=
      hCD3.injOn (show (𝒮.xBar s).ι.base xb ∈ _ from h4) (show (𝒮.xBar s).ι.base xb' ∈ _ from h4')
        hEq
    exact (𝒮.xBar s).ι.isEmbedding.injective h5
  · obtain ⟨hxS, hx0⟩ := hx
    obtain ⟨xh, hxh, hcx⟩ := hCD3.surjOn hx0
    obtain ⟨xb, hxbι, -, hbar⟩ :=
      𝒮.exists_stalkIdeal_jBar_le_pow_and_bBar_le_nu_of_mem_Snu s x ⟨hx0, hxS⟩ xh hxh hcx
    have hcb : (𝒮.cBar s).base xb = x := by
      show (𝒮.c s).base ((𝒮.xBar s).ι.base xb) = x
      rw [hxbι]; exact hcx
    have hxS' : (𝒮.cBar s).base xb ∈ sNu (datum T ℜ s) (restriction T r s) ν := hcb ▸ hxS
    refine ⟨xb, ?_, hcb⟩
    rw [S_datumRep_eq hprep hJt hJne]
    refine (le_nu_jBarRep_iff hadm hII xb).mpr ⟨hbar, ?_⟩
    -- `(b)`: `b ≤ ∑ c_j + ν`
    have hSd : (𝒮.cBar s).base xb ∈ (datum T ℜ s).S := by
      cases hR : restriction T r s with
      | unrestricted => rw [hR] at hxS'; exact hxS'.1
      | closed F => rw [hR] at hxS'; exact hxS'.1.1
    have hνle : (datum T ℜ s).nuAt ((𝒮.cBar s).base xb) ≤ ν := by
      have h1 : (datum T ℜ s).nuAt ((𝒮.cBar s).base xb) ≤ (datum T ℜ s).nu :=
        le_iSup₂ (f := fun y (_ : y ∈ (datum T ℜ s).S) => (datum T ℜ s).nuAt y) _ hSd
      exact h1.trans (hS.nu_datum_le s)
    have hb : ((datum T ℜ s).b : ℕ∞) ≤ ((datum T ℜ s).weight ((𝒮.cBar s).base xb) : ℕ∞) +
        (datum T ℜ s).nuAt ((𝒮.cBar s).base xb) := hSd
    rw [b_datum, 𝒮.weight_cBar_eq_weightC hprep xb hxS'] at hb
    have h2 : (ℜ.b : ℕ∞) ≤ ((∑ j ∈ Finset.univ.filter fun j => xb ∈ (𝒮.eTilde s j).pts,
        cT T ℜ r s j : ℕ) : ℕ∞) + ν := hb.trans (add_le_add le_rfl hνle)
    have h3 : ℜ.b ≤ (∑ j ∈ Finset.univ.filter fun j => xb ∈ (𝒮.eTilde s j).pts,
        cT T ℜ r s j) + ν := by exact_mod_cast h2
    omega

end Frame

end CD

/-! ## 6. Normal crossings of `E(s)` with `B_s` (Remarks 1 and 2) -/

namespace CD

variable {X : Scheme.{u}} {N : ℕ} {ℜ : DatumII.Raw X} {r : Restriction X} {ν : ℕ}
  {T : AB.Tower X} {x₀ : X}

namespace Frame

variable {hS : Standing N ℜ r ν T x₀} (𝒮 : Frame hS)

open Classical in
/-- **Remark 1, p. 322, and Remark 2, p. 324: normal crossings of `E_1(s) ∪ ⋯ ∪ E_{α+s}(s)` with
`B`** ("this is clear from the fact that `Ẽ_1 ∪ ⋯ ∪ Ẽ_α̃` has only normal crossings with `B̃`"), for
the emptied datum.  The hypotheses `hover` (the points of `B̃` lie over `x̂_0`) and `hout` (without
restriction, the points of `B` miss the `E_i(s)`, `i ≤ α`) are consequences of `[(1)]`, `[(2)]`.

Deviation from the paper (proof corrected, repair of the paper's error on the subschemes `Ẽ_j`): the descent of
`CD.hasOnlyNormalCrossingsWith_eUnion_datum_aux` only for the members `k` of the regular system of
parameters of `O_{X,x}` that are not in `B_x`: such a `k` has a non-zero image in `O_{X̃,b̃}`
(`O_{X,x}/B_x ≃ O_{X̃,b̃}/B̃_{b̃}`), so its trace `Ẽ_i` is not the whole space and is transversal to
`X̄_s`.
The other members generate the traces `E_j(s) ⊇ B_s` (the dropped ones, `E_j(s) = F(s)`, among
them) and need no independence modulo `B_x`. -/
theorem hasOnlyNormalCrossingsWith_eUnion_datumRep_aux [Hironaka.HironakaCitedResults.{u}] {s : ℕ} (hprep : PrepHyp N ℜ r ν T x₀ s)
    {bt : ℕ}
    (a : Fin (alphaT r ℜ.α s) → ℕ) (Jt : Subscheme (𝒮.xTilde s))
    (hII : ((𝒮.datumTilde s bt a Jt).emptyIfBot).IsWeakDatum)
    (Bt : Subscheme (𝒮.xTilde s)) (hBt : Bt.IsNonsingular)
    (hperm : ((𝒮.datumTilde s bt a Jt).emptyIfBot).IsPermissible Bt)
    (B : Subscheme (T.X s)) (e : Bt.toScheme ≅ B.toScheme)
    (he : e.hom ≫ B.ι = Bt.ι ≫ 𝒮.cBar s)
    (hover : ∀ b : Bt.toScheme,
      (𝒮.tHat.pre s).composite.base ((𝒮.xBar s).ι.base (Bt.ι.base b)) = hS.xh)
    (hout : r = .unrestricted → ∀ (i : Fin ℜ.α) (b : Bt.toScheme),
      (𝒮.cBar s).base (Bt.ι.base b) ∉ (eSeq T ℜ s (Fin.castAdd s i)).pts) :
    (datum T ℜ s).eUnion.HasOnlyNormalCrossingsWith B := by
  classical
  have hadm := 𝒮.isAdmissibleAt_of_prepHyp hprep
  have hBns : B.IsNonsingular := isNonsingular_of_iso e.symm hBt
  intro x hx
  obtain ⟨b, hb⟩ : ∃ b : Bt.toScheme, (𝒮.cBar s).base (Bt.ι.base b) = x := by
    obtain ⟨w, hw⟩ := Subscheme.exists_ι_eq_of_mem_pts B hx
    refine ⟨e.inv.base w, ?_⟩
    have h1 := congrArg (fun φ : Bt.toScheme ⟶ T.X s => φ.base (e.inv.base w)) he.symm
    simp only [Scheme.Hom.comp_base, TopCat.hom_comp, ContinuousMap.comp_apply] at h1
    have h2 : e.hom (e.inv w) = w := by
      rw [← Scheme.Hom.comp_apply, e.inv_hom_id]; rfl
    rw [← hw]
    refine h1.trans ?_
    show B.ι (e.hom (e.inv w)) = B.ι w
    rw [h2]
  subst hb
  -- the point `ỹ = ι(b)` of `X̃` over `x`
  have hyBt : Bt.ι.base b ∈ Bt.pts := Subscheme.mem_pts_ι Bt b
  have hRx : IsRegularLocalRing ((T.X s).presheaf.stalk ((𝒮.cBar s).base (Bt.ι.base b))) :=
    hS.isNonsingular_X s _
  have hRt : IsRegularLocalRing ((𝒮.xBar s).toScheme.presheaf.stalk (Bt.ι.base b)) :=
    hadm.1.1 _
  have hd := hS.isDatum_datum s
  obtain ⟨Z₀, hZ₀, -, hE⟩ := DatumTransform.exists_rsop_adapted_of_isDatum (B := ⊥)
    (datum T ℜ s).E (hS.isNonsingular_X s) hd.2.1 hd.2.2.1 (fun x _ => hd.2.2.1 x)
    ((𝒮.cBar s).base (Bt.ι.base b))
  have hE' : ∀ j : Fin (ℜ.α + s),
      (eSeq T ℜ s j).stalkIdeal ((𝒮.cBar s).base (Bt.ι.base b)) = ⊤ ∨
      ∃ k ∈ Z₀, (eSeq T ℜ s j).stalkIdeal ((𝒮.cBar s).base (Bt.ι.base b)) = Ideal.span {k} :=
    fun j => hE (Fin.cast (alpha_datum T ℜ s).symm j)
  have hZ₀ext : ExtendsToRSOP _ Z₀ := ExtendsToRSOP.of_isRegularSystemOfParameters hZ₀
  obtain ⟨K₁, hK₁Z, hK₁gen, hK₁⟩ := DatumTransform.exists_iInf_eq_span_prod_and_forall_mem
    (fun j : Fin (ℜ.α + s) => (eSeq T ℜ s j).stalkIdeal ((𝒮.cBar s).base (Bt.ι.base b)))
    hZ₀ext hE'
  have hK₁ext : ExtendsToRSOP _ K₁ := hZ₀ext.mono hK₁Z
  -- (B) the prime of `B`
  have hP : (B.stalkIdeal ((𝒮.cBar s).base (Bt.ι.base b))).IsPrime :=
    Subscheme.isPrime_stalkIdeal_of_isNonsingular_of_mem_pts B hBns hx
  have hPreg : IsRegularLocalRing (_ ⧸ B.stalkIdeal ((𝒮.cBar s).base (Bt.ι.base b))) :=
    Subscheme.isRegularLocalRing_quotient_of_isNonsingular hBns hx
  -- (C) the isomorphism `O_{X,x}/B_x ≃ O_{X̃,ỹ}/B̃_ỹ`
  obtain ⟨Θ, hΘ⟩ := Subscheme.exists_ringEquiv_quotient_stalkMap (𝒮.cBar s) B Bt e he b
  -- (D) the adapted regular system of parameters on `X̃`, for the emptied traces
  obtain ⟨Zt, hZt, ⟨Tb, hTbZ, hBtTb⟩, hEj⟩ :=
    DatumTransform.exists_rsop_of_hasOnlyNormalCrossingsWithAt_of_isNonsingularDivisor
      (𝒮.datumTilde s bt a Jt).emptyIfBot.E hII.2.1 (fun i => iInf_le _ i) (D := Bt)
      (hperm.2.2 (Bt.ι.base b) (Subscheme.mem_pts_ι Bt b))
  -- (E) the generators of the `Ẽ_i` through `ỹ`
  have hmaxk : ∀ k ∈ K₁, k ∈ maximalIdeal _ := fun k hk => hZ₀ext.mem_maximalIdeal (hK₁Z hk)
  have hTi : ∀ (i : Fin (alphaT r ℜ.α s))
      (k : (T.X s).presheaf.stalk ((𝒮.cBar s).base (Bt.ι.base b))),
      (eSeq T ℜ s (idxT ℜ.α s r i)).stalkIdeal ((𝒮.cBar s).base (Bt.ι.base b)) = Ideal.span {k} →
      (𝒮.eTilde s i).stalkIdeal (Bt.ι.base b) =
        Ideal.span {((𝒮.cBar s).stalkMap (Bt.ι.base b)).hom k} := by
    intro i k hk
    have h1 : 𝒮.eTilde s i = Subscheme.totalTransform (𝒮.cBar s) (eSeq T ℜ s (idxT ℜ.α s r i)) :=
      (Subscheme.totalTransform_comp _ _ _).symm
    rw [h1, stalkIdeal_totalTransform, hk, Ideal.map_span, Set.image_singleton]
  -- the members of `K₁` outside `B_x` have a non-zero image in `O_{X̃,ỹ}` (`O_{X,x}/B_x ≃
  -- O_{X̃,ỹ}/B̃_ỹ`), so their traces are not the whole space; the members of `B_x` (the dropped
  -- traces `E_j(s) = F(s) ⊇ B_s` among them) need no independence
  set K' := K₁.filter (· ∉ B.stalkIdeal ((𝒮.cBar s).base (Bt.ι.base b))) with hK'
  have hφne : ∀ k ∈ K', ((𝒮.cBar s).stalkMap (Bt.ι.base b)).hom k ≠ 0 := by
    intro k hk h0
    have hkB : k ∉ B.stalkIdeal ((𝒮.cBar s).base (Bt.ι.base b)) := (Finset.mem_filter.mp hk).2
    apply hkB
    have h1 := hΘ k
    rw [h0, map_zero] at h1
    have h2 : (Ideal.Quotient.mk (B.stalkIdeal ((𝒮.cBar s).base (Bt.ι.base b)))) k = 0 :=
      Θ.injective (h1.trans (map_zero Θ).symm)
    exact Ideal.Quotient.eq_zero_iff_mem.mp h2
  have hex : ∀ k ∈ K', ∃ (i : Fin (alphaT r ℜ.α s)) (hi : 𝒮.eTilde s i ≠ ⊥),
      (eSeq T ℜ s (idxT ℜ.α s r i)).stalkIdeal ((𝒮.cBar s).base (Bt.ι.base b)) =
        Ideal.span {k} ∧ ∃ β ∈ Zt,
          Ideal.span {((𝒮.cBar s).stalkMap (Bt.ι.base b)).hom k} = Ideal.span {β} := by
    intro k hk'
    have hk := (Finset.mem_filter.mp hk').1
    obtain ⟨j, hj⟩ := hK₁gen k hk
    have hjx : ((𝒮.cBar s).base (Bt.ι.base b)) ∈ (eSeq T ℜ s j).pts :=
      Subscheme.mem_pts_iff_stalkIdeal_ne_top.mpr (by
        rw [hj]; exact (hZ₀ext.isPrime_span_singleton (hK₁Z hk)).ne_top)
    obtain ⟨i, rfl⟩ := exists_idxT_of_mem_pts (fun hr i => hout hr i b) j hjx
    have hne : (𝒮.eTilde s i).stalkIdeal (Bt.ι.base b) ≠ ⊤ := by
      rw [hTi i k hj, Ne, Ideal.span_singleton_eq_top]
      intro hu
      exact (IsLocalRing.mem_maximalIdeal _).mp (hmaxk k hk) (IsLocalHom.map_nonunit _ hu)
    have hbot : 𝒮.eTilde s i ≠ ⊥ := by
      intro h0
      have h1 := hTi i k hj
      rw [h0, Subscheme.stalkIdeal_bot_eq, eq_comm, Ideal.span_singleton_eq_bot] at h1
      exact hφne k hk' h1
    have hEi : (𝒮.datumTilde s bt a Jt).emptyIfBot.E i = 𝒮.eTilde s i :=
      Subscheme.emptyIfBot_of_ne_bot hbot
    obtain ⟨β, hβZ, hβ⟩ := (hEj i).resolve_left (by rw [hEi]; exact hne)
    rw [hEi] at hβ
    exact ⟨i, hbot, hj, β, hβZ, (hTi i k hj).symm.trans hβ⟩
  -- (F) transversality of the kept `Ê_i` to `X̄_s` at `ι(ỹ)`
  have hRhat : IsRegularLocalRing ((𝒮.tHat.X s).presheaf.stalk
      ((𝒮.xBar s).ι.base (Bt.ι.base b))) := 𝒮.isNonsingular_tHat_X s _
  let E' : {j : Fin (alphaT r ℜ.α s) // 𝒮.eTilde s j ≠ ⊥} → Subscheme (𝒮.tHat.X s) :=
    fun i => 𝒮.eHat s (idxT ℜ.α s r i.1)
  have hsimpleF : ∀ i : {j : Fin (alphaT r ℜ.α s) // 𝒮.eTilde s j ≠ ⊥},
      (𝒮.xBar s).ι.base (Bt.ι.base b) ∈ (E' i).pts →
      (E' i).IsSimpleAt ((𝒮.xBar s).ι.base (Bt.ι.base b)) ∧
        (E' i).codimAt ((𝒮.xBar s).ι.base (Bt.ι.base b)) = 1 :=
    fun i hi => 𝒮.isSimpleAt_and_codimAt_eq_one_totalTransform_c s
      (hS.isNonsingular_eSeq s _) (hS.exists_stalkIdeal_eSeq s _) _ hi
  have hTF : ∀ i : {j : Fin (alphaT r ℜ.α s) // 𝒮.eTilde s j ≠ ⊥},
      (𝒮.xBar s).ι.base (Bt.ι.base b) ∈ (E' i).pts →
      ¬ (E' i).stalkIdeal ((𝒮.xBar s).ι.base (Bt.ι.base b)) ≤
        (𝒮.xBar s).stalkIdeal ((𝒮.xBar s).ι.base (Bt.ι.base b)) :=
    fun i hi => (𝒮.isTransversalFamilyWith_eHat_of_ne_bot s hadm).2 i _
      ⟨hi, Subscheme.mem_pts_ι _ _⟩
  have hNCy := 𝒮.hasOnlyNormalCrossingsWith_xBar_of_ne_bot s hadm
    ((𝒮.xBar s).ι.base (Bt.ι.base b)) (Subscheme.mem_pts_ι _ _)
  have hEred : (⨅ i, E' i).IsReduced :=
    Subscheme.isReduced_iInf_of_forall_isNonsingular E' fun i => 𝒮.isNonsingular_eHat s _
  obtain ⟨-, zb, Kf, hzb, -, hKf1, -, hKfst, -, hKfinj⟩ :=
    Subscheme.exists_stalk_presentation_iInf_totalTransform_ι
      (E := E') (D := 𝒮.xBar s) hEred (Bt.ι.base b) hNCy hsimpleF hTF
  -- (G) choice of the generators `β k` and their injectivity
  have hβex : ∀ k ∈ K', ∃ β ∈ Zt, Ideal.span {((𝒮.cBar s).stalkMap (Bt.ι.base b)).hom k} =
      Ideal.span {β} := fun k hk => by
    obtain ⟨i, -, -, h⟩ := hex k hk
    exact h
  choose! β hβZ hβspan using hβex
  have hzbext : ExtendsToRSOP _ zb := ExtendsToRSOP.of_isRegularSystemOfParameters hzb
  have hinj : Set.InjOn β (K' : Set _) := by
    intro k hk k' hk'
    have hk := Finset.mem_coe.mp hk
    have hk' := Finset.mem_coe.mp hk'
    intro hkk
    obtain ⟨i, hbot, hi, -⟩ := hex k hk
    obtain ⟨i', hbot', hi', -⟩ := hex k' hk'
    have hspan : (𝒮.eTilde s i).stalkIdeal (Bt.ι.base b) =
        (𝒮.eTilde s i').stalkIdeal (Bt.ι.base b) := by
      rw [hTi _ _ (hi), hTi _ _ (hi'), hβspan k hk, hβspan k' hk', hkk]
    have hthrough : ∀ i : Fin (alphaT r ℜ.α s),
        (𝒮.eTilde s i).stalkIdeal (Bt.ι.base b) ≠ ⊤ →
        (𝒮.xBar s).ι.base (Bt.ι.base b) ∈ (𝒮.eHat s (idxT ℜ.α s r i)).pts := by
      intro i hi
      by_contra hn
      apply hi
      have : (Subscheme.totalTransform (𝒮.xBar s).ι (𝒮.eHat s (idxT ℜ.α s r i))).stalkIdeal
          (Bt.ι.base b) = ⊤ := by
        by_contra hne
        exact hn ((Subscheme.mem_pts_totalTransform_subschemeι_iff (Bt.ι.base b)).mp
          (Subscheme.mem_pts_iff_stalkIdeal_ne_top.mpr hne))
      exact this
    have hne : ∀ (i : Fin (alphaT r ℜ.α s)) (k : _), k ∈ K₁ →
        (eSeq T ℜ s (idxT ℜ.α s r i)).stalkIdeal ((𝒮.cBar s).base (Bt.ι.base b)) =
          Ideal.span {k} → (𝒮.eTilde s i).stalkIdeal (Bt.ι.base b) ≠ ⊤ := by
      intro i k hk hik
      rw [hTi i k hik, Ne, Ideal.span_singleton_eq_top]
      intro hu
      exact (IsLocalRing.mem_maximalIdeal _).mp (hmaxk k hk) (IsLocalHom.map_nonunit _ hu)
    obtain ⟨bi, hbi, hKi⟩ := hKf1 ⟨i, hbot⟩
      (hthrough _ (hne i k (Finset.mem_filter.mp hk).1 hi))
    obtain ⟨bi', hbi', hKi'⟩ := hKf1 ⟨i', hbot'⟩
      (hthrough _ (hne i' k' (Finset.mem_filter.mp hk').1 hi'))
    have hspan2 : Ideal.span {bi} = Ideal.span {bi'} := by
      have h1 := hKfst ⟨i, hbot⟩
      have h2 := hKfst ⟨i', hbot'⟩
      rw [hKi, Finset.prod_singleton] at h1
      rw [hKi', Finset.prod_singleton] at h2
      exact h1.symm.trans (hspan.trans h2)
    have hbb : bi = bi' := hzbext.span_singleton_injOn (Finset.mem_coe.mpr hbi)
      (Finset.mem_coe.mpr hbi') hspan2
    have hKK : Kf ⟨i, hbot⟩ = Kf ⟨i', hbot'⟩ := by rw [hKi, hKi', hbb]
    have hhat := hKfinj _ _ hKK
    -- faithful flatness of `c_s` at `ι(ỹ)`
    have hflat := 𝒮.toCompletion.comap_map_stalkMap (hS.ambient.2.1 x₀) hS.isNonsingular_X
      hS.isNonsingular_B s ((𝒮.xBar s).ι.base (Bt.ι.base b)) (hover b)
    have e1 : ∀ i : Fin (alphaT r ℜ.α s), (𝒮.eHat s (idxT ℜ.α s r i)).stalkIdeal
        ((𝒮.xBar s).ι.base (Bt.ι.base b)) =
        ((eSeq T ℜ s (idxT ℜ.α s r i)).stalkIdeal
          ((𝒮.c s).base ((𝒮.xBar s).ι.base (Bt.ι.base b)))).map
          ((𝒮.c s).stalkMap ((𝒮.xBar s).ι.base (Bt.ι.base b))).hom :=
      fun i => stalkIdeal_totalTransform _ _ _
    have hkk := hflat (Ideal.span {k})
    have hkk' := hflat (Ideal.span {k'})
    change (𝒮.eHat s (idxT ℜ.α s r i)).stalkIdeal ((𝒮.xBar s).ι.base (Bt.ι.base b)) =
      (𝒮.eHat s (idxT ℜ.α s r i')).stalkIdeal ((𝒮.xBar s).ι.base (Bt.ι.base b)) at hhat
    rw [e1, e1] at hhat
    have e2 : (eSeq T ℜ s (idxT ℜ.α s r i)).stalkIdeal
        ((𝒮.c s).base ((𝒮.xBar s).ι.base (Bt.ι.base b))) = Ideal.span {k} := hi
    have e3 : (eSeq T ℜ s (idxT ℜ.α s r i')).stalkIdeal
        ((𝒮.c s).base ((𝒮.xBar s).ι.base (Bt.ι.base b))) = Ideal.span {k'} := hi'
    rw [e2, e3] at hhat
    have : Ideal.span {k} = Ideal.span {k'} :=
      hkk.symm.trans ((congrArg (Ideal.comap _) hhat).trans hkk')
    exact hZ₀ext.span_singleton_injOn (Finset.mem_coe.mpr (hK₁Z (Finset.mem_filter.mp hk).1))
      (Finset.mem_coe.mpr (hK₁Z (Finset.mem_filter.mp hk').1)) this
  -- (H) independence of the members outside `P` modulo `P`
  have hPprime := hP
  let Θ' := Θ.trans (Ideal.quotEquivOfEq hBtTb)
  have hΘ' : ∀ a, Θ' (Ideal.Quotient.mk _ a) =
      Ideal.Quotient.mk _ (((𝒮.cBar s).stalkMap (Bt.ι.base b)).hom a) := fun a => by
    simp only [Θ', RingEquiv.trans_apply, hΘ, Ideal.quotEquivOfEq_mk]
  have hF := rsopIndep_quotient_of_associated_rsop
    (((𝒮.cBar s).stalkMap (Bt.ι.base b)).hom)
    (B.stalkIdeal ((𝒮.cBar s).base (Bt.ι.base b))) hPreg hZt hTbZ Θ' hΘ'
    K' (fun k hk => (Finset.mem_filter.mp hk).2) β (fun k hk => hβZ k hk)
    (fun k hk => hβspan k hk) hinj
  -- (I) conclusion
  obtain ⟨Z, T', hZ, hKZ, hT'Z, hT'⟩ :=
    exists_isRegularSystemOfParameters_subset_and_span_eq_prime
      (B.stalkIdeal ((𝒮.cBar s).base (Bt.ι.base b))) hPreg K₁ hK₁ext hF
  have hEst : (datum T ℜ s).eUnion.stalkIdeal ((𝒮.cBar s).base (Bt.ι.base b)) =
      Ideal.span {∏ k ∈ K₁, k} := by
    rw [eUnion_datum_eq, DatumTransform.stalkIdeal_iInf_fintype]
    exact hK₁
  exact Subscheme.hasOnlyNormalCrossingsWithAt_of_stalkIdeal_eq hZ hKZ hT'Z hEst hT'.symm

/-- Remark 1, p. 322, and Remark 2, p. 324, normal crossings of `E_1(s) ∪ ⋯ ∪ E_{α+s}(s)` with
`B`, for the emptied datum `ℜ̃` on `X̃` (any `b̃`) with a permissible center `B̃` all of whose
points
go into `S_ν(ℜ(s))` under `c̄_s` and `c̄_s` inducing `B̃ ≅ B`. -/
theorem hasOnlyNormalCrossingsWith_eUnion_datumRep_of_forall_mem_sNu [Hironaka.HironakaCitedResults.{u}] {s : ℕ}
    (hprep : PrepHyp N ℜ r ν T x₀ s) {bt : ℕ} (a : Fin (alphaT r ℜ.α s) → ℕ)
    (Jt : Subscheme (𝒮.xTilde s)) (hII : ((𝒮.datumTilde s bt a Jt).emptyIfBot).IsWeakDatum)
    (Bt : Subscheme (𝒮.xTilde s)) (hBt : Bt.IsNonsingular) (hBti : Bt.IsIrreducible)
    (hperm : ((𝒮.datumTilde s bt a Jt).emptyIfBot).IsPermissible Bt)
    (B : Subscheme (T.X s)) (hBe : ∃ e : Bt.toScheme ≅ B.toScheme, e.hom ≫ B.ι = Bt.ι ≫ 𝒮.cBar s)
    (hmem : ∀ xb ∈ Bt.pts, (𝒮.cBar s).base xb ∈ (datum T ℜ s).sNu ν) :
    (datum T ℜ s).eUnion.HasOnlyNormalCrossingsWith B := by
  classical
  obtain ⟨e, he⟩ := hBe
  have := 𝒮.regShat
  have hmemR : ∀ xb ∈ Bt.pts, (𝒮.cBar s).base xb ∈ sNu (datum T ℜ s) (restriction T r s) ν :=
    fun xb hxb => mem_sNu_of_mem_sNu_of_forall_closed _ (hmem xb hxb)
      fun F hF => 𝒮.cBar_mem_pts_of_closed hprep hF xb
  have himg := 𝒮.image_cBar_eq_singleton hprep Bt hBti fun xb hxb => ⟨_, hmemR xb hxb, rfl⟩
  refine 𝒮.hasOnlyNormalCrossingsWith_eUnion_datumRep_aux hprep a Jt hII Bt hBt hperm B e he
    (fun b => ?_) (fun hr i b hmem' => ?_)
  · refine eq_xhat0_of_c0_eq (hS.ambient.2.1 x₀) ?_
    rw [𝒮.c0_comp_pre_apply]
    have : (T.pre s).composite.base ((𝒮.cBar s).base (Bt.ι.base b)) ∈
        (T.pre s).composite.base '' ((𝒮.cBar s).base '' Bt.pts) :=
      ⟨_, ⟨Bt.ι.base b, Subscheme.mem_pts_ι Bt b, rfl⟩, rfl⟩
    rw [himg] at this
    exact this
  · have h0 := hprep.2.2.1 hr i
    exact (Set.eq_empty_iff_forall_notMem.mp h0) _ ⟨hmem', hmemR _ (Subscheme.mem_pts_ι Bt b)⟩

end Frame

end CD

/-! ## 7. Remarks 1 and 2 for the repaired datum -/

namespace CD

variable {X : Scheme.{u}} {N : ℕ} {ℜ : DatumII.Raw X} {r : Restriction X} {ν : ℕ}
  {T : AB.Tower X} {x₀ : X}

open Classical in
/-- **Remarks 1 and 2** (pp. 321–324) for the repaired datum, in one statement valid for every
`ν`: `S(ℜ̃) = {x ∈ X̃ | ν(J̄*(s)_x) ≥ b̃}`; `c̄_s` induces a bijection `S(ℜ̃) → S_ν(ℜ(s)) ∩
h_s⁻¹(x_0)`; and a non-singular irreducible `B̃ ⊆ X̃` such that the monoidal transformation with
center `B̃` is permissible for `ℜ̃` is `c_s⁻¹(B_s)` for a unique non-singular irreducible `B_s ⊆
X_s`
to which `c̄_s` restricts to an isomorphism `B̃ → B_s` and for which `f_s` is permissible for
`ℜ(s)`.

Deviation from the paper (proof corrected, repair of the paper's error on the subschemes `Ẽ_j`): the printed
statements are those of Remark 1 (`ν ≥ b`, `J̃ = J̄(s)`, `b̃ = b̄`) and Remark 2 (`ν < b`, `J̃ =
J̄*(s)`, `b̃ = b̄ (b - ν)`).  They are proved here for the datum whose entries `Ẽ_j = X̃` are
emptied
and with the threshold `b - ν` replaced by `b - ν - δ_s` (the weight `δ_s` of the dropped traces
enters the sum (b)); for `δ_s = 0` (no restriction, or no component equal to `F`) this is the
printed datum (`jBarRep_eq_jBar_of_le`, `jBarRep_eq_jBarStar`). -/
@[blueprint "rem:IV.4-2-repaired"
  (statement := /-- \textbf{Remark 2, repaired} (uniform in $\nu$). Notation as in
    \cref{def:IV.4-conditions} and \cref{def:IV.4-case-lt-repaired}. We have $S(\tilde{\mathfrak
    R}^e)=\{x\in\tilde X\mid\nu(\bar J^\sharp(s)_x)\ge\tilde b\}$. The morphism $c_s\colon\hat
    X_s\to X_s$ induces a bijection $S(\tilde{\mathfrak R}^e)\to S_\nu(\mathfrak R(s))\cap
    h_s^{-1}(x_0)$. Moreover, if $\tilde B$ is any non-singular irreducible subscheme of
    $\tilde X$ such that the monoidal transformation $\tilde f$ with center $\tilde B$ is
    permissible for $\tilde{\mathfrak R}^e$, then there exists a unique non-singular irreducible
    subscheme $B_s$ of $X_s$ such that $\tilde B=c_s^{-1}(B_s)$, that $c_s$ induces an
    isomorphism $\tilde B\to B_s$ and that the monoidal transformation $f_s$ of $X_s$ with
    center $B_s$ is permissible for $\mathfrak R(s)$. (Replaces Remark~2, \cref{rem:IV.4-2},
    p.~323, and Remark~1, \cref{rem:IV.4-1}, pp.~321--322.)

    \textbf{Deviation from the paper (proof corrected, repair of the paper's error on the subschemes $\tilde E_j$).} The
    printed Remark~2 (p.~323) says: ``$x\in S(\mathfrak R^{N-1}_{\mathrm{II}})$ if and only if
    (a) $\nu(\bar J(s)_{\hat x})\ge\bar b$, and (b) $\sum_{\hat x\in\tilde E_j}c_j\ge b-\nu$''
    for the datum $\mathfrak R^{N-1}_{\mathrm{II}}$ of \cref{def:IV.4-case-lt}, which is not a
    resolution datum (the $\tilde E_j$ can be reducible and $\tilde E_i=\tilde X$ if $F=E_i$). Here the datum is $\tilde{\mathfrak R}^e$ with the traces
    equal to $\tilde X$ emptied and the threshold shifted; the sum in (b) runs over all $j$, the
    dropped traces included (they contain every point of $\tilde X$). -/)
  (proof := /-- (pp.~323--324.) Let $\hat x\in\tilde X$. By the additivity of the order in the
    regular local ring $\mathcal O_{\tilde X,\hat x}$, in which the stalk of each kept $\tilde E_j$
    is generated by an element of order~$1$, $\hat x\in S(\tilde{\mathfrak R}^e)$ if and only if (a)
    $\nu(\bar J(s)_{\hat x})\ge\bar b$ and (b) $\sum_{\hat x\in\tilde E_j}c_j\ge b-\nu$ (sum over
    all
    $j$). By Lemma (CD.5) (\cref{lem:IV.CD-5}), (a) implies $\nu(J(s)_x)\ge\nu$ for $x=c_s(\hat
    x)$ and (b) implies $\sum_{x\in E_j(s)}a_j\ge b-\nu$; so $x\in S_\nu(\mathfrak R(s))$ and, by
    $[(1)]$, $x\in h_s^{-1}(x_0)$. Conversely a point $x\in S_\nu(\mathfrak R(s))\cap
    h_s^{-1}(x_0)$ has a unique $\hat x$ over it (Lemma (CD.3), \cref{lem:IV.CD-3}), which
    satisfies (a) (Corollary of Lemma (CD.4), \cref{cor:IV.CD-4}) and (b) since $\nu(J(s)_x)=\nu$.
    For $\tilde B$, $c_s(\tilde B)\subseteq S_\nu(\mathfrak R(s))\cap h_s^{-1}(x_0)$ and Lemma
    (CD.3) gives $B_s$; that $E_1(s)\cup\dots\cup E_{\alpha+s}(s)$ has only normal crossings with
    $B_s$ follows from the normal crossings of $\tilde E^e_1\cup\dots\cup\tilde E^e_{\tilde\alpha}$
    with $\tilde B$ by descent from $\tilde X$ to $X_s$ for the members of the regular system of
    parameters of $\mathcal O_{X_s,x}$ outside $B_{s,x}$; the others generate the traces
    $E_j(s)\supseteq B_s$ (among them the dropped ones, $E_j(s)=F(s)$) and need no independence.

    \textbf{Deviation from the paper (proof corrected, repair of the paper's error on the subschemes $\tilde E_j$).} See the
    statement: the paper's proof is carried out for the emptied datum with the shifted threshold
    $d_s=b-\nu-\delta_s$, in which the weight $\delta_s$ of the dropped traces replaces part of
    $b-\nu$. -/)
  (proofUses := ["def:IV.4-case-lt-repaired", "lem:IV.4-tilde-facts-repaired", "lem:IV.CD-5",
    "lem:IV.CD-3", "cor:IV.CD-4", "def:IV.4-conditions"])
  (latexEnv := "remark")]
theorem Frame.S_datumRep_eq_and_bijOn_cBar_and_exists_isPermissibleCenter [Hironaka.HironakaCitedResults.{u}]
    {hS : Standing N ℜ r ν T x₀} (𝒮 : Frame hS) (s : ℕ)
    (hprep : PrepHyp N ℜ r ν T x₀ s)
    (a : Fin (alphaT r ℜ.α s) → ℕ) (Jt : Subscheme (𝒮.xTilde s))
    (hJt : Jt * ∏ j, ((𝒮.eTilde s j).emptyIfBot) ^ (a j) = 𝒮.jBarRep s)
    (hJne : ∀ x, Jt.stalkIdeal x ≠ ⊥) :
    (𝒮.datumRep s a Jt).S =
      {x | ((𝒮.bTildeRep s : ℕ) : ℕ∞) ≤ Ideal.nu ((𝒮.jBarRep s).stalkIdeal x)} ∧
    Set.BijOn (𝒮.cBar s).base (𝒮.datumRep s a Jt).S
      (sNu (datum T ℜ s) (restriction T r s) ν ∩ (T.pre s).composite.base ⁻¹' {x₀}) ∧
    ∀ Bt : Subscheme (𝒮.xTilde s), Bt.IsNonsingular → Bt.IsIrreducible →
      (𝒮.datumRep s a Jt).IsPermissible Bt →
      ∃ Bs : Subscheme (T.X s),
        (Bs.IsNonsingular ∧ Bs.IsIrreducible ∧
          (Bt.ι ≫ (𝒮.xBar s).ι).ker = Subscheme.totalTransform (𝒮.c s) Bs ∧
          (∃ e : Bt.toScheme ≅ Bs.toScheme, e.hom ≫ Bs.ι = Bt.ι ≫ 𝒮.cBar s) ∧
          (restriction T r s).IsPermissibleCenter (datum T ℜ s) Bs) ∧
        ∀ Bs' : Subscheme (T.X s), Bs'.IsNonsingular → Bs'.IsIrreducible →
          (Bt.ι ≫ (𝒮.xBar s).ι).ker = Subscheme.totalTransform (𝒮.c s) Bs' →
          (∃ e : Bt.toScheme ≅ Bs'.toScheme, e.hom ≫ Bs'.ι = Bt.ι ≫ 𝒮.cBar s) →
          (restriction T r s).IsPermissibleCenter (datum T ℜ s) Bs' → Bs' = Bs := by
  have hadm := 𝒮.isAdmissibleAt_of_prepHyp hprep
  have hII := 𝒮.isWeakDatum_datumRep hprep a Jt hJne
  refine ⟨Frame.S_datumRep_eq hprep hJt hJne, Frame.bijOn_cBar_S_datumRep hprep hJt hJne, ?_⟩
  intro Bt hBt hBti hperm
  have hmem : ∀ xb ∈ Bt.pts, (𝒮.cBar s).base xb ∈ (datum T ℜ s).sNu ν := fun xb hxb =>
    (Frame.cBar_mem_sNu_and_hBar_eq_of_mem_S_datumRep hprep hJt hJne (hperm.2.1 hxb).1).1
  obtain ⟨B, hBns, hBirr, hker, hiso, hpts⟩ :=
    𝒮.exists_ker_eq_totalTransform_of_forall_mem_sNu s hprep Bt hBt hBti hmem
  refine ⟨B, ⟨hBns, hBirr, hker, hiso, ?_⟩, ?_⟩
  · have hnu : (datum T ℜ s).nu ≤ ν := hS.nu_datum_le s
    suffices ∀ R : Restriction (T.X s), R = restriction T r s →
        R.IsPermissibleCenter (datum T ℜ s) B from this _ rfl
    intro R hR
    have hP : (datum T ℜ s).IsPermissible B := by
      refine ⟨Or.inr ⟨hBns, hBirr⟩, ?_,
        𝒮.hasOnlyNormalCrossingsWith_eUnion_datumRep_of_forall_mem_sNu (bt := 𝒮.bTildeRep s) hprep
          (𝒮.aRep s a) Jt hII Bt hBt hBti
          hperm B hiso hmem⟩
      rw [hpts]
      rintro _ ⟨xb, hxb, rfl⟩
      exact ⟨(hmem xb hxb).1, hnu.trans (hmem xb hxb).2⟩
    cases R with
    | unrestricted => exact hP
    | closed F' =>
      refine ⟨hP, ?_⟩
      rw [hpts]
      rintro _ ⟨xb, hxb, rfl⟩
      exact 𝒮.cBar_mem_pts_of_closed hprep hR.symm xb
  · intro Bs' hBs'ns hBs'irr hker' hiso' hperm'
    exact AB.eq_of_isReduced_of_pts_eq
      (Hironaka.DatumTransform.isReduced_of_isNonsingular hBs'ns)
      (Hironaka.DatumTransform.isReduced_of_isNonsingular hBns)
      ((pts_eq_image_cBar_of_iso hiso').trans hpts.symm)

end CD

/-! ## 8. The relation of p. 322 and Remark 3 for the repaired datum

`f̄_s` is the monoidal transformation of `X̃` with center `B̃`.  The transform of the emptied datum
along it is the emptied datum of the next stage; `δ` is constant. -/

namespace CD

variable {X : Scheme.{u}} {N : ℕ} {ℜ : DatumII.Raw X} {r : Restriction X} {ν : ℕ}
  {T : AB.Tower X} {x₀ : X}

namespace Frame

variable {hS : Standing N ℜ r ν T x₀} {𝒮 : Frame hS}
  {s : ℕ} {Bt : Subscheme (𝒮.xTilde s)} {Bs : Subscheme (T.X s)}

/-- `X̃ = X̄_s` is an algebraic scheme, an irreducible space and non-singular (for an admissible
stage). -/
theorem isAlgebraicScheme_and_irreducibleSpace_and_isNonsingular_xTilde [Hironaka.HironakaCitedResults.{u}]
    (hadm : 𝒮.IsAdmissibleAt s) :
    IsAlgebraicScheme (𝒮.xTilde s) ∧ IrreducibleSpace (𝒮.xTilde s) ∧
      (𝒮.xTilde s).IsNonsingular := by
  have := 𝒮.isAlgebraicScheme_tHat_X s
  exact ⟨isAlgebraicScheme_toScheme (𝒮.xBar s), hadm.1.2, hadm.1.1⟩

/-- The scheme `X̄_{s+1}` is non-empty when `f̄_s` is the monoidal transformation of `X̃` with a
center `B̃` permissible for a weak datum on `X̃`. -/
theorem nonempty_tBar_X' [Hironaka.HironakaCitedResults.{u}] (hadm : 𝒮.IsAdmissibleAt s) {D : DatumII.Raw (𝒮.xTilde s)}
    (hII : D.IsWeakDatum) (hperm : D.IsPermissible Bt)
    (h : AB.IsMonoidalTransformationOf (𝒮.fBar s) Bt) : Nonempty (𝒮.tBar s h).X' := by
  obtain ⟨hA, hI, hN⟩ := isAlgebraicScheme_and_irreducibleSpace_and_isNonsingular_xTilde hadm
  have hBX : Bt.pts ≠ Set.univ := hII.pts_ne_univ_of_isPermissible hN hperm
  obtain ⟨-, -, hirr, -⟩ := MonoidalTransformation.transform_isAmbient hN hperm.1 hBX (𝒮.tBar s h)
  exact hirr.toNonempty

end Frame

end CD

namespace CD

variable {X : Scheme.{u}} {N : ℕ} {ℜ : DatumII.Raw X} {r : Restriction X} {ν : ℕ}
  {T : AB.Tower X} {x₀ : X}

namespace Frame

variable {hS : Standing N ℜ r ν T x₀} {𝒮 : Frame hS}
  {s : ℕ} {Bt : Subscheme (𝒮.xTilde s)} {Bs : Subscheme (T.X s)}

set_option linter.style.longLine false in
open Classical in
/-- **`Ẽ'_j` is the strict transform of `Ẽ_j`**, for the dropped traces too (p. 324: "the `Ẽ'_j` …
strict transforms commute with `c_{s+1}` and with the restriction to `X̄_{s+1}`"): a dropped trace
`Ẽ_j = X̃` has the total transform `X̄_{s+1}`, so `Ẽ'_j = X̄_{s+1}` is the strict transform of `X̃`;
for the kept traces this is `eTilde_succ_castSuccT_eq_strictBar` with the hypotheses on the
emptied datum. 

Deviation from the paper (proof corrected, repair of the paper's error on the subschemes `Ẽ_j`): the
statement is proved for the repaired datum `datumRep`. -/
theorem eTilde_succ_castSuccT_eq_strictBar_of_emptyIfBot [Hironaka.HironakaCitedResults.{u}] (hadm : 𝒮.IsAdmissibleAt s)
    (hd : 𝒮.CenterData s Bt Bs) {bt : ℕ} {a : Fin (alphaT r ℜ.α s) → ℕ}
    {Jt : Subscheme (𝒮.xTilde s)} (hII : ((𝒮.datumTilde s bt a Jt).emptyIfBot).IsWeakDatum)
    (hperm : ((𝒮.datumTilde s bt a Jt).emptyIfBot).IsPermissible Bt)
    (h : AB.IsMonoidalTransformationOf (𝒮.fBar s) Bt) (j : Fin (alphaT r ℜ.α s)) :
    𝒮.eTilde (s + 1) (castSuccT r ℜ.α s j) = 𝒮.strictBar s h (𝒮.eTilde s j) := by
  refine Subscheme.ext_stalkIdeal fun yb => ?_
  obtain ⟨hX1, hinv⟩ := 𝒮.isNonsingular_xBar_succ_and_isInvertibleIdeal_pBar s hadm.2.1 hadm.1
  have hreg : IsRegularLocalRing (((𝒮.xBar (s + 1)).toScheme).presheaf.stalk yb) := hX1 yb
  have := isDomain_of_isRegularLocalRing (((𝒮.xBar (s + 1)).toScheme).presheaf.stalk yb)
  obtain ⟨g, hg, hgnz⟩ := Subscheme.IsInvertibleIdeal.exists_stalkIdeal_eq_span hinv yb
  have hg0 : g ≠ 0 := nonZeroDivisors.ne_zero hgnz
  have h1 := stalkIdeal_totalTransform_eTilde hd j yb
  by_cases hj : 𝒮.eTilde s j = ⊥
  · -- a dropped trace
    rw [hj, Subscheme.stalkIdeal_totalTransform_bot, Subscheme.stalkIdeal_bot_eq] at h1
    have hbot : (𝒮.eTilde (s + 1) (castSuccT r ℜ.α s j)).stalkIdeal yb = ⊥ := by
      rcases Ideal.mul_eq_bot.mp h1.symm with h2 | h2
      · exact h2
      · exfalso
        rw [hg, Ideal.span_singleton_pow, Ideal.span_singleton_eq_bot] at h2
        exact pow_ne_zero _ hg0 h2
    have hsb : 𝒮.strictBar s h (⊥ : Subscheme (𝒮.xTilde s)) = ⊥ :=
      MonoidalTransformation.strictTransform_bot _
    rw [hbot, hj, hsb, Subscheme.stalkIdeal_bot_eq]
  · -- a kept trace
    have hDE : ((𝒮.datumTilde s bt a Jt).emptyIfBot).E j = 𝒮.eTilde s j :=
      Subscheme.emptyIfBot_of_ne_bot hj
    obtain ⟨hA, hI, hN⟩ := isAlgebraicScheme_and_irreducibleSpace_and_isNonsingular_xTilde hadm
    have hreg' : IsRegularLocalRing (((𝒮.tBar s h).X').presheaf.stalk yb) := hX1 yb
    have key :=
      Hironaka.DatumTransform.stalkIdeal_totalTransform_eq_strict_mul_exceptional_pow_of_pts_subset_of_isNonsingularDivisor
      (B := Bt) ((𝒮.datumTilde s bt a Jt).emptyIfBot).E hN hII.2.1 hII.2.2.1 hperm.2.2
      hd.irreducible_t hd.nonsingular_t (𝒮.tBar s h) j yb
    have hexc' : (𝒮.tBar s h).exceptional.stalkIdeal yb = (𝒮.pBar s).stalkIdeal yb :=
      congrArg (fun D : Subscheme (𝒮.xBar (s + 1)).toScheme => D.stalkIdeal yb)
        (𝒮.exceptional_tBar_eq_pBar s h hd.ker_eq_B)
    rw [hexc', hDE] at key
    replace key : (Subscheme.totalTransform (𝒮.fBar s) (𝒮.eTilde s j)).stalkIdeal yb =
        (𝒮.strictBar s h (𝒮.eTilde s j)).stalkIdeal yb *
          ((𝒮.pBar s).stalkIdeal yb) ^ (if Bt.pts ⊆ (𝒮.eTilde s j).pts then 1 else 0) := key
    have hm : (if Bt.pts ⊆ (𝒮.eTilde s j).pts then 1 else 0) =
        (if Bs.pts ⊆ (eSeq T ℜ s (idxT ℜ.α s r j)).pts then 1 else 0) := by
      simp only [hd.pts_subset_eTilde_iff j]
    rw [hm, h1] at key
    by_cases hsub : Bs.pts ⊆ (eSeq T ℜ s (idxT ℜ.α s r j)).pts
    · rw [ite_eq_left hsub, pow_one, hg, mul_comm _ (Ideal.span {g}),
        mul_comm _ (Ideal.span {g})] at key
      exact (Ideal.span_singleton_mul_right_inj hg0).mp key
    · rw [ite_eq_right hsub, pow_zero, mul_one, mul_one] at key
      exact key

end Frame

end CD

namespace CD

variable {X : Scheme.{u}} {N : ℕ} {ℜ : DatumII.Raw X} {r : Restriction X} {ν : ℕ}
  {T : AB.Tower X} {x₀ : X}

/-- The additive form of `prod_alphaT_succ`. -/
theorem sum_alphaT_succ {M : Type*} [AddCommMonoid M] (r : Restriction X) (α s : ℕ)
    (F : Fin (alphaT r α (s + 1)) → M) :
    ∑ i, F i = (∑ j, F (castSuccT r α s j)) + F (lastT r α s) := by
  have h1 := Fin.sum_univ_castSucc (fun k : Fin (alphaT r α s + 1) =>
    F (Fin.cast (alphaT_succ r α s).symm k))
  have h2 : ∑ k : Fin (alphaT r α s + 1), F (Fin.cast (alphaT_succ r α s).symm k) = ∑ i, F i :=
    Fintype.sum_equiv (finCongr (alphaT_succ r α s).symm) _ _ (fun k => rfl)
  rw [← h2, h1]
  rfl

namespace Frame

variable {hS : Standing N ℜ r ν T x₀} {𝒮 : Frame hS}
  {s : ℕ} {Bt : Subscheme (𝒮.xTilde s)} {Bs : Subscheme (T.X s)}

/-- The new divisor `P̄_{s+1}` is not the whole space (it is the exceptional divisor of `f̄_s`). -/
theorem pBar_ne_bot [Hironaka.HironakaCitedResults.{u}] {D : DatumII.Raw (𝒮.xTilde s)} (hadm : 𝒮.IsAdmissibleAt s)
    (hd : 𝒮.CenterData s Bt Bs) (hII : D.IsWeakDatum) (hperm : D.IsPermissible Bt)
    (h : AB.IsMonoidalTransformationOf (𝒮.fBar s) Bt) : 𝒮.pBar s ≠ ⊥ := by
  have := nonempty_tBar_X' hadm hII hperm h
  rw [← 𝒮.exceptional_tBar_eq_pBar s h hd.ker_eq_B]
  exact MonoidalTransformation.exceptional_ne_bot _

open Classical in
/-- **`Ẽ'_j = X̄_{s+1}` iff `Ẽ_j = X̃`**: a dropped trace stays dropped along the extension, and a
kept
one stays kept (its strict transform is a non-singular divisor of the weak datum `f̄_s*(ℜ̃)`). -/
theorem eTilde_succ_castSuccT_eq_bot_iff [Hironaka.HironakaCitedResults.{u}] (hadm : 𝒮.IsAdmissibleAt s)
    (hd : 𝒮.CenterData s Bt Bs) {bt : ℕ} {a : Fin (alphaT r ℜ.α s) → ℕ}
    {Jt : Subscheme (𝒮.xTilde s)} (hII : ((𝒮.datumTilde s bt a Jt).emptyIfBot).IsWeakDatum)
    (hperm : ((𝒮.datumTilde s bt a Jt).emptyIfBot).IsPermissible Bt)
    (h : AB.IsMonoidalTransformationOf (𝒮.fBar s) Bt) (j : Fin (alphaT r ℜ.α s)) :
    𝒮.eTilde (s + 1) (castSuccT r ℜ.α s j) = ⊥ ↔ 𝒮.eTilde s j = ⊥ := by
  rw [eTilde_succ_castSuccT_eq_strictBar_of_emptyIfBot hadm hd hII hperm h j]
  constructor
  · intro hbot
    by_contra hj
    obtain ⟨hA, hI, hN⟩ := isAlgebraicScheme_and_irreducibleSpace_and_isNonsingular_xTilde hadm
    have := nonempty_tBar_X' hadm hII hperm h
    have hw := hII.transform hN (𝒮.tBar s h) hperm
    have h1 := (hw.2.1 (Fin.castSucc j)).ne_bot
    have hE0 := E_transform_castSucc (𝒮.datumTilde s bt a Jt).emptyIfBot (𝒮.tBar s h) j
    rw [hE0] at h1
    have hDE : ((𝒮.datumTilde s bt a Jt).emptyIfBot).E j = 𝒮.eTilde s j :=
      Subscheme.emptyIfBot_of_ne_bot hj
    rw [hDE] at h1
    exact h1 hbot
  · intro hj
    rw [hj]
    exact MonoidalTransformation.strictTransform_bot _

open Classical in
/-- **`δ_{s+1} = δ_s`**: the weight of the dropped traces is constant along an extension of the
succession (the new divisor `P̄_{s+1}` is kept, the old exponents `c_j` do not change). -/
theorem droppedWeight_succ [Hironaka.HironakaCitedResults.{u}] (hadm : 𝒮.IsAdmissibleAt s)
    (hd : 𝒮.CenterData s Bt Bs) {bt : ℕ} {a : Fin (alphaT r ℜ.α s) → ℕ}
    {Jt : Subscheme (𝒮.xTilde s)} (hII : ((𝒮.datumTilde s bt a Jt).emptyIfBot).IsWeakDatum)
    (hperm : ((𝒮.datumTilde s bt a Jt).emptyIfBot).IsPermissible Bt)
    (h : AB.IsMonoidalTransformationOf (𝒮.fBar s) Bt) :
    𝒮.droppedWeight (s + 1) = 𝒮.droppedWeight s := by
  unfold droppedWeight
  rw [Finset.sum_filter, Finset.sum_filter, sum_alphaT_succ]
  have hlast : 𝒮.eTilde (s + 1) (lastT r ℜ.α s) ≠ ⊥ := by
    rw [eTilde_succ_lastT_eq_pBar]
    exact pBar_ne_bot hadm hd hII hperm h
  simp only [hlast, ↓reduceIte, add_zero]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [cT_succ_castSuccT]
  simp only [eTilde_succ_castSuccT_eq_bot_iff hadm hd hII hperm h j]

theorem thresholdRep_succ [Hironaka.HironakaCitedResults.{u}] (hadm : 𝒮.IsAdmissibleAt s)
    (hd : 𝒮.CenterData s Bt Bs) {bt : ℕ} {a : Fin (alphaT r ℜ.α s) → ℕ}
    {Jt : Subscheme (𝒮.xTilde s)} (hII : ((𝒮.datumTilde s bt a Jt).emptyIfBot).IsWeakDatum)
    (hperm : ((𝒮.datumTilde s bt a Jt).emptyIfBot).IsPermissible Bt)
    (h : AB.IsMonoidalTransformationOf (𝒮.fBar s) Bt) :
    𝒮.thresholdRep (s + 1) = 𝒮.thresholdRep s := by
  unfold thresholdRep
  rw [droppedWeight_succ hadm hd hII hperm h]

theorem bTildeRep_succ [Hironaka.HironakaCitedResults.{u}] (hadm : 𝒮.IsAdmissibleAt s)
    (hd : 𝒮.CenterData s Bt Bs) {bt : ℕ} {a : Fin (alphaT r ℜ.α s) → ℕ}
    {Jt : Subscheme (𝒮.xTilde s)} (hII : ((𝒮.datumTilde s bt a Jt).emptyIfBot).IsWeakDatum)
    (hperm : ((𝒮.datumTilde s bt a Jt).emptyIfBot).IsPermissible Bt)
    (h : AB.IsMonoidalTransformationOf (𝒮.fBar s) Bt) :
    𝒮.bTildeRep (s + 1) = 𝒮.bTildeRep s := by
  unfold bTildeRep
  rw [thresholdRep_succ hadm hd hII hperm h]

end Frame

end CD

namespace CD

variable {X : Scheme.{u}} {N : ℕ} {ℜ : DatumII.Raw X} {r : Restriction X} {ν : ℕ}
  {T : AB.Tower X} {x₀ : X}

namespace Frame

variable {hS : Standing N ℜ r ν T x₀} {𝒮 : Frame hS}
  {s : ℕ} {Bt : Subscheme (𝒮.xTilde s)} {Bs : Subscheme (T.X s)}

open Classical in
/-- Stalks of the total transforms `f̄_s⁻¹(Ẽ_j)` of the emptied traces (pp. 324–325): `f̄_s⁻¹(Ẽ^e_j)
=
(Ẽ'_j)^e · P̄_{s+1}^m` with `m = 1` iff `B̃ ⊆ Ẽ^e_j` (a dropped trace is empty, with total transform
empty, and stays dropped). 

Deviation from the paper (proof corrected, repair of the paper's error on the subschemes `Ẽ_j`): the
statement is proved for the repaired datum `datumRep`. -/
theorem stalkIdeal_totalTransform_eTilde_emptyIfBot [Hironaka.HironakaCitedResults.{u}] (hadm : 𝒮.IsAdmissibleAt s)
    (hd : 𝒮.CenterData s Bt Bs) {bt : ℕ} {a : Fin (alphaT r ℜ.α s) → ℕ}
    {Jt : Subscheme (𝒮.xTilde s)} (hII : ((𝒮.datumTilde s bt a Jt).emptyIfBot).IsWeakDatum)
    (hperm : ((𝒮.datumTilde s bt a Jt).emptyIfBot).IsPermissible Bt)
    (h : AB.IsMonoidalTransformationOf (𝒮.fBar s) Bt) (j : Fin (alphaT r ℜ.α s))
    (yb : (𝒮.xBar (s + 1)).toScheme) :
    (Subscheme.totalTransform (𝒮.fBar s) ((𝒮.eTilde s j).emptyIfBot)).stalkIdeal yb =
      ((𝒮.eTilde (s + 1) (castSuccT r ℜ.α s j)).emptyIfBot).stalkIdeal yb *
        ((𝒮.pBar s).stalkIdeal yb) ^
          (if Bt.pts ⊆ ((𝒮.eTilde s j).emptyIfBot).pts then 1 else 0) := by
  by_cases hj : 𝒮.eTilde s j = ⊥
  · have hj' := (eTilde_succ_castSuccT_eq_bot_iff hadm hd hII hperm h j).mpr hj
    have hne : Bt.pts.Nonempty := pts_nonempty_of_isIrreducible Bt hd.irreducible_t
    have hnsub : ¬ Bt.pts ⊆ ((𝒮.eTilde s j).emptyIfBot).pts := by
      rw [Subscheme.pts_emptyIfBot_eq_empty hj]
      intro hsub
      obtain ⟨x, hx⟩ := hne
      exact hsub hx
    rw [ite_eq_right hnsub, pow_zero, mul_one, Subscheme.emptyIfBot_of_eq_bot hj,
      Subscheme.emptyIfBot_of_eq_bot hj', Subscheme.totalTransform_top]
  · have hj' : 𝒮.eTilde (s + 1) (castSuccT r ℜ.α s j) ≠ ⊥ :=
      fun h0 => hj ((eTilde_succ_castSuccT_eq_bot_iff hadm hd hII hperm h j).mp h0)
    rw [Subscheme.emptyIfBot_of_ne_bot hj, Subscheme.emptyIfBot_of_ne_bot hj',
      stalkIdeal_totalTransform_eTilde hd j yb]
    simp only [hd.pts_subset_eTilde_iff j]

/-- The generic point of the center (p. 325: "`f̃` is permissible for `ℜ^{N-1}_II`"), for the
emptied datum: `b̃ ≤ ∑_{B̃ ⊆ Ẽ_j} ã_j + ν̃` and `ν(J̃_ξ) ≥ ν̃` at the generic point `ξ` of `B̃`. -/
theorem exists_isGenericPoint_nu_eq_of_emptyIfBot (hadm : 𝒮.IsAdmissibleAt s)
    (hBti : Bt.IsIrreducible) {bt : ℕ} {a : Fin (alphaT r ℜ.α s) → ℕ}
    {Jt : Subscheme (𝒮.xTilde s)} (hII : ((𝒮.datumTilde s bt a Jt).emptyIfBot).IsWeakDatum)
    (hperm : ((𝒮.datumTilde s bt a Jt).emptyIfBot).IsPermissible Bt) :
    bt ≤ (∑ j, if Bt.pts ⊆ ((𝒮.eTilde s j).emptyIfBot).pts then a j else 0) +
        ((𝒮.datumTilde s bt a Jt).emptyIfBot).nu.toNat ∧
      ∃ ξ : 𝒮.xTilde s, IsGenericPoint ξ Bt.pts ∧
        (((𝒮.datumTilde s bt a Jt).emptyIfBot).nu.toNat : ℕ∞) ≤ Ideal.nu (Jt.stalkIdeal ξ) :=
  DatumII.Raw.b_le_sum_add_nu_and_exists_isGenericPoint_of_forall_stalkIdeal_ne_bot hadm.1.1 _
    hII.2.2.2 hBti hperm

/-- `f̄_s⁻¹(J̃) ⊆ P̄_{s+1}^ν̃` for the emptied datum (Ch. 0 §5, Remark 2 of Ch. III). -/
theorem totalTransform_le_pBar_pow_of_emptyIfBot (hadm : 𝒮.IsAdmissibleAt s)
    (hd : 𝒮.CenterData s Bt Bs) {bt : ℕ} {a : Fin (alphaT r ℜ.α s) → ℕ}
    {Jt : Subscheme (𝒮.xTilde s)} (hII : ((𝒮.datumTilde s bt a Jt).emptyIfBot).IsWeakDatum)
    (hperm : ((𝒮.datumTilde s bt a Jt).emptyIfBot).IsPermissible Bt)
    (h : AB.IsMonoidalTransformationOf (𝒮.fBar s) Bt) :
    Subscheme.totalTransform (𝒮.fBar s) Jt ≤
      (𝒮.pBar s) ^ ((𝒮.datumTilde s bt a Jt).emptyIfBot).nu.toNat := by
  obtain ⟨-, ξ, hξ, hν⟩ := exists_isGenericPoint_nu_eq_of_emptyIfBot hadm hd.irreducible_t hII hperm
  have key := Subscheme.totalTransform_le_exceptional_pow hadm.1.1 hd.nonsingular_t (𝒮.tBar s h)
    Jt hξ hν
  rw [𝒮.exceptional_tBar_eq_pBar s h hd.ker_eq_B] at key
  exact key

open Classical in
/-- `∑_{B̃ ⊆ Ẽ^e_i} a_i = ∑_j m_j a_j` with `m_j = 1` iff `B̃ ⊆ Ẽ^e_j`. -/
theorem sum_filter_isContainedIn_emptyIfBot_eq (hd : 𝒮.CenterData s Bt Bs)
    (a : Fin (alphaT r ℜ.α s) → ℕ) :
    (∑ i ∈ Finset.univ.filter fun i : Fin (alphaT r ℜ.α s) =>
        Bt.IsContainedIn ((𝒮.eTilde s i).emptyIfBot), a i) =
      ∑ j, (if Bt.pts ⊆ ((𝒮.eTilde s j).emptyIfBot).pts then 1 else 0) * a j := by
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hiff : Bt.IsContainedIn ((𝒮.eTilde s j).emptyIfBot) ↔
      Bt.pts ⊆ ((𝒮.eTilde s j).emptyIfBot).pts :=
    ⟨pts_subset_of_isContainedIn, Subscheme.isContainedIn_of_pts_subset
      (Hironaka.DatumTransform.isReduced_of_isNonsingular hd.nonsingular_t)⟩
  by_cases hc : Bt.IsContainedIn ((𝒮.eTilde s j).emptyIfBot)
  · have hj := hiff.mp hc
    simp [hc, hj]
  · have hj : ¬ Bt.pts ⊆ ((𝒮.eTilde s j).emptyIfBot).pts := fun h' => hc (hiff.mpr h')
    simp [hc, hj]

open Classical in
/-- The stalk of the total transform of `J̃ ∏ (Ẽ^e_j)^{a_j}`. -/
theorem stalkIdeal_totalTransform_mul_prod_emptyIfBot [Hironaka.HironakaCitedResults.{u}] (hadm : 𝒮.IsAdmissibleAt s)
    (hd : 𝒮.CenterData s Bt Bs) {bt : ℕ} {a : Fin (alphaT r ℜ.α s) → ℕ}
    {Jt : Subscheme (𝒮.xTilde s)} (hII : ((𝒮.datumTilde s bt a Jt).emptyIfBot).IsWeakDatum)
    (hperm : ((𝒮.datumTilde s bt a Jt).emptyIfBot).IsPermissible Bt)
    (h : AB.IsMonoidalTransformationOf (𝒮.fBar s) Bt) (yb : (𝒮.xBar (s + 1)).toScheme) :
    (Subscheme.totalTransform (𝒮.fBar s)
        (Jt * ∏ j, ((𝒮.eTilde s j).emptyIfBot) ^ (a j))).stalkIdeal yb =
      (Subscheme.totalTransform (𝒮.fBar s) Jt).stalkIdeal yb *
        ∏ j, (((𝒮.eTilde (s + 1) (castSuccT r ℜ.α s j)).emptyIfBot).stalkIdeal yb *
          ((𝒮.pBar s).stalkIdeal yb) ^
            (if Bt.pts ⊆ ((𝒮.eTilde s j).emptyIfBot).pts then 1 else 0)) ^ (a j) := by
  rw [stalkIdeal_totalTransform, Subscheme.stalkIdeal_mul_eq, Ideal.map_mul, stalkIdeal_prod_eq,
    Ideal.map_finset_prod, ← stalkIdeal_totalTransform]
  congr 1
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [Subscheme.stalkIdeal_pow_eq, Ideal.map_pow, ← stalkIdeal_totalTransform,
    stalkIdeal_totalTransform_eTilde_emptyIfBot hadm hd hII hperm h j yb]

end Frame

end CD

namespace CD

variable {X : Scheme.{u}} {N : ℕ} {ℜ : DatumII.Raw X} {r : Restriction X} {ν : ℕ}
  {T : AB.Tower X} {x₀ : X}

namespace Frame

variable {hS : Standing N ℜ r ν T x₀} {𝒮 : Frame hS}
  {s : ℕ} {Bt : Subscheme (𝒮.xTilde s)} {Bs : Subscheme (T.X s)}

open Classical in
/-- **The transform of the emptied `ℜ^{N-1}_II` by `f̄_s` has the form of the emptied datum at stage
`s+1`** (pp. 322, 324: "`f̄_s*(ℜ^{N-1}_II)` can be written in the form `(Ẽ'_1, …, Ẽ'_{α̃+1} | J̃',
b̃ | ã_1, …, ã_{α̃+1})`"): the divisors are the emptied `Ẽ'_j` formed for `h_{s+1}`, the exponents
are
`a_1, …, a_α̃` followed by a new one, and `J̃'` is the quotient `f̄_s⁻¹(J̃) P̄_{s+1}^{-ν̃}` of
Definition 7 (II). 

Deviation from the paper (proof corrected, repair of the paper's error on the subschemes `Ẽ_j`): the
statement is proved for the repaired datum `datumRep`. -/
theorem transform_datumTilde_emptyIfBot_eq [Hironaka.HironakaCitedResults.{u}] (hadm : 𝒮.IsAdmissibleAt s)
    (hd : 𝒮.CenterData s Bt Bs) {bt : ℕ} {a : Fin (alphaT r ℜ.α s) → ℕ}
    {Jt : Subscheme (𝒮.xTilde s)} (hII : ((𝒮.datumTilde s bt a Jt).emptyIfBot).IsWeakDatum)
    (hperm : ((𝒮.datumTilde s bt a Jt).emptyIfBot).IsPermissible Bt)
    (h : AB.IsMonoidalTransformationOf (𝒮.fBar s) Bt) :
    ((𝒮.datumTilde s bt a Jt).emptyIfBot).transform (𝒮.tBar s h) =
      (𝒮.datumTilde (s + 1) bt
        (extendA a ((((𝒮.datumTilde s bt a Jt).emptyIfBot).transform (𝒮.tBar s h)).a
          (Fin.last _)))
        ((((𝒮.datumTilde s bt a Jt).emptyIfBot).transform (𝒮.tBar s h)).J)).emptyIfBot := by
  have hpb := pBar_ne_bot hadm hd hII hperm h
  refine DatumII.Raw.ext_of_cast (alphaT_succ r ℜ.α s).symm (fun i => ?_) (fun i => ?_) rfl rfl
  · induction i using Fin.lastCases with
    | last =>
      refine (E_transform_last _ (𝒮.tBar s h)).trans ?_
      change _ = (𝒮.eTilde (s + 1) (lastT r ℜ.α s)).emptyIfBot
      rw [𝒮.eTilde_succ_lastT_eq_pBar s, Subscheme.emptyIfBot_of_ne_bot hpb]
      exact 𝒮.exceptional_tBar_eq_pBar s h hd.ker_eq_B
    | cast j =>
      refine (E_transform_castSucc _ (𝒮.tBar s h) j).trans ?_
      change Subscheme.strictTransform (𝒮.tBar s h) ((𝒮.eTilde s j).emptyIfBot) =
        (𝒮.eTilde (s + 1) (castSuccT r ℜ.α s j)).emptyIfBot
      by_cases hj : 𝒮.eTilde s j = ⊥
      · have hj' := (eTilde_succ_castSuccT_eq_bot_iff hadm hd hII hperm h j).mpr hj
        rw [Subscheme.emptyIfBot_of_eq_bot hj, Subscheme.emptyIfBot_of_eq_bot hj']
        exact MonoidalTransformation.strictTransform_top _
      · have hj' : 𝒮.eTilde (s + 1) (castSuccT r ℜ.α s j) ≠ ⊥ :=
          fun h0 => hj ((eTilde_succ_castSuccT_eq_bot_iff hadm hd hII hperm h j).mp h0)
        rw [Subscheme.emptyIfBot_of_ne_bot hj, Subscheme.emptyIfBot_of_ne_bot hj']
        exact (eTilde_succ_castSuccT_eq_strictBar_of_emptyIfBot hadm hd hII hperm h j).symm
  · induction i using Fin.lastCases with
    | last => exact (extendA_lastT a _).symm
    | cast j =>
      exact (a_transform_castSucc _ (𝒮.tBar s h) j).trans (extendA_castSuccT a _ j).symm

end Frame

end CD

namespace CD

variable {X : Scheme.{u}} {N : ℕ} {ℜ : DatumII.Raw X} {r : Restriction X} {ν : ℕ}
  {T : AB.Tower X} {x₀ : X}

namespace Frame

variable {hS : Standing N ℜ r ν T x₀} {𝒮 : Frame hS}
  {s : ℕ} {Bt : Subscheme (𝒮.xTilde s)} {Bs : Subscheme (T.X s)}

open Classical in
/-- **The identity of Remarks 2 and 3 (pp. 325–326), stalkwise, for the emptied datum**: if the
total
transform of `J̃ ∏ (Ẽ^e_j)^{ã_j}` is `P̄_{s+1}^{b̃} · W`, then the datum `f̄_s*(ℜ̃)` has `J̃' ∏
((Ẽ'_j)^e)^{ã_j} = W`, where `J̃' = f̄_s⁻¹(J̃) P̄_{s+1}^{-ν̃}` and the exponent of the new divisor
`P̄_{s+1}` is `ã_{α̃+1} = (∑_{B̃ ⊆ Ẽ_j} ã_j) + ν̃ − b̃`. 

Deviation from the paper (proof corrected, repair of the paper's error on the subschemes `Ẽ_j`): the
statement is proved for the repaired datum `datumRep`. -/
theorem prod_eq_of_stalkIdeal_totalTransform_eq_of_emptyIfBot [Hironaka.HironakaCitedResults.{u}] (hadm : 𝒮.IsAdmissibleAt s)
    (hd : 𝒮.CenterData s Bt Bs) {bt : ℕ} {a : Fin (alphaT r ℜ.α s) → ℕ}
    {Jt : Subscheme (𝒮.xTilde s)} (hII : ((𝒮.datumTilde s bt a Jt).emptyIfBot).IsWeakDatum)
    (hperm : ((𝒮.datumTilde s bt a Jt).emptyIfBot).IsPermissible Bt)
    (h : AB.IsMonoidalTransformationOf (𝒮.fBar s) Bt)
    (W : Subscheme (𝒮.xBar (s + 1)).toScheme)
    (hW : ∀ yb : (𝒮.xBar (s + 1)).toScheme,
      (Subscheme.totalTransform (𝒮.fBar s)
        (Jt * ∏ j, ((𝒮.eTilde s j).emptyIfBot) ^ (a j))).stalkIdeal yb =
        ((𝒮.pBar s).stalkIdeal yb) ^ bt * W.stalkIdeal yb) :
    𝒮.jTransform s h ((𝒮.datumTilde s bt a Jt).emptyIfBot) *
      ∏ i, ((𝒮.eTilde (s + 1) i).emptyIfBot) ^
        (extendA a ((((𝒮.datumTilde s bt a Jt).emptyIfBot).transform (𝒮.tBar s h)).a
          (Fin.last _)) i) = W := by
  classical
  refine Subscheme.ext_stalkIdeal fun yb => ?_
  obtain ⟨hX1, hinv⟩ := 𝒮.isNonsingular_xBar_succ_and_isInvertibleIdeal_pBar s hadm.2.1 hadm.1
  have hreg : IsRegularLocalRing (((𝒮.xBar (s + 1)).toScheme).presheaf.stalk yb) := hX1 yb
  have hdom := isDomain_of_isRegularLocalRing (((𝒮.xBar (s + 1)).toScheme).presheaf.stalk yb)
  obtain ⟨g, hg, hgnz⟩ := Subscheme.IsInvertibleIdeal.exists_stalkIdeal_eq_span hinv yb
  have hg0 : g ≠ 0 := nonZeroDivisors.ne_zero hgnz
  have hker := hd.ker_eq_B
  have hpb := pBar_ne_bot hadm hd hII hperm h
  obtain ⟨hb, -⟩ := exists_isGenericPoint_nu_eq_of_emptyIfBot hadm hd.irreducible_t hII hperm
  have hanew : ((((𝒮.datumTilde s bt a Jt).emptyIfBot).transform (𝒮.tBar s h)).a (Fin.last _)) =
      (∑ j, (if Bt.pts ⊆ ((𝒮.eTilde s j).emptyIfBot).pts then 1 else 0) * a j) +
        ((𝒮.datumTilde s bt a Jt).emptyIfBot).nu.toNat - bt := by
    rw [a_transform_last]
    show (∑ i ∈ Finset.univ.filter fun i => Bt.IsContainedIn ((𝒮.eTilde s i).emptyIfBot), a i) +
      ((𝒮.datumTilde s bt a Jt).emptyIfBot).nu.toNat - bt = _
    rw [sum_filter_isContainedIn_emptyIfBot_eq hd a]
  have hprod : ∏ i, ((𝒮.eTilde (s + 1) i).emptyIfBot) ^
      (extendA a ((((𝒮.datumTilde s bt a Jt).emptyIfBot).transform (𝒮.tBar s h)).a
        (Fin.last _)) i) =
      (∏ j, ((𝒮.eTilde (s + 1) (castSuccT r ℜ.α s j)).emptyIfBot) ^ (a j)) *
        (𝒮.pBar s) ^ ((((𝒮.datumTilde s bt a Jt).emptyIfBot).transform (𝒮.tBar s h)).a
          (Fin.last _)) := by
    rw [prod_alphaT_succ, extendA_lastT, 𝒮.eTilde_succ_lastT_eq_pBar s,
      Subscheme.emptyIfBot_of_ne_bot hpb]
    simp only [extendA_castSuccT]
  rw [hprod, Subscheme.stalkIdeal_mul_eq, stalkIdeal_transform_J h hker,
    Subscheme.stalkIdeal_mul_eq, stalkIdeal_prod_eq, Subscheme.stalkIdeal_pow_eq, hg, hanew]
  simp only [Subscheme.stalkIdeal_pow_eq]
  have hJm := (Subscheme.le_iff_stalkIdeal_le.mp
    (totalTransform_le_pBar_pow_of_emptyIfBot hadm hd hII hperm h)) yb
  rw [Subscheme.stalkIdeal_pow_eq, hg, Ideal.span_singleton_pow] at hJm
  have hh := hW yb
  rw [stalkIdeal_totalTransform_mul_prod_emptyIfBot hadm hd hII hperm h yb, hg] at hh
  rw [← mul_assoc]
  refine Ideal.colon_mul_prod_mul_pow_eq hg0 _ (fun j => ((𝒮.eTilde (s + 1)
    (castSuccT r ℜ.α s j)).emptyIfBot).stalkIdeal yb) a
    (fun j => if Bt.pts ⊆ ((𝒮.eTilde s j).emptyIfBot).pts then 1 else 0)
    ((𝒮.datumTilde s bt a Jt).emptyIfBot).nu.toNat bt (W.stalkIdeal yb) hJm (fun _ => ?_) hh
  refine le_of_le_of_eq hb ?_
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  by_cases hj : Bt.pts ⊆ ((𝒮.eTilde s j).emptyIfBot).pts <;> simp [hj]

end Frame

end CD

namespace CD

variable {X : Scheme.{u}} {N : ℕ} {ℜ : DatumII.Raw X} {r : Restriction X} {ν : ℕ}
  {T : AB.Tower X} {x₀ : X}

namespace Frame

variable {hS : Standing N ℜ r ν T x₀} {𝒮 : Frame hS}
  {s : ℕ} {Bt : Subscheme (𝒮.xTilde s)} {Bs : Subscheme (T.X s)}

open Classical in
/-- The stalk of the total transform of `∏ (Ẽ^e_j)^{c_j}`. -/
theorem stalkIdeal_totalTransform_prod_emptyIfBot [Hironaka.HironakaCitedResults.{u}] (hadm : 𝒮.IsAdmissibleAt s)
    (hd : 𝒮.CenterData s Bt Bs) {bt : ℕ} {a : Fin (alphaT r ℜ.α s) → ℕ}
    {Jt : Subscheme (𝒮.xTilde s)} (hII : ((𝒮.datumTilde s bt a Jt).emptyIfBot).IsWeakDatum)
    (hperm : ((𝒮.datumTilde s bt a Jt).emptyIfBot).IsPermissible Bt)
    (h : AB.IsMonoidalTransformationOf (𝒮.fBar s) Bt) (c : Fin (alphaT r ℜ.α s) → ℕ)
    (yb : (𝒮.xBar (s + 1)).toScheme) :
    (Subscheme.totalTransform (𝒮.fBar s)
        (∏ j, ((𝒮.eTilde s j).emptyIfBot) ^ (c j))).stalkIdeal yb =
      ∏ j, (((𝒮.eTilde (s + 1) (castSuccT r ℜ.α s j)).emptyIfBot).stalkIdeal yb *
        ((𝒮.pBar s).stalkIdeal yb) ^
          (if Bt.pts ⊆ ((𝒮.eTilde s j).emptyIfBot).pts then 1 else 0)) ^ (c j) := by
  rw [stalkIdeal_totalTransform, stalkIdeal_prod_eq, Ideal.map_finset_prod]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [Subscheme.stalkIdeal_pow_eq, Ideal.map_pow, ← stalkIdeal_totalTransform,
    stalkIdeal_totalTransform_eTilde_emptyIfBot hadm hd hII hperm h j yb]

open Classical in
/-- `e = e_K + δ_s`: the multiplicity `∑_j [B_s ⊆ E_j(s)] c_j` splits into the part carried by the
kept traces and the weight of the dropped ones (every dropped `E_j(s) = F(s) ⊇ B_s`). -/
theorem sum_mul_cT_eq (hd : 𝒮.CenterData s Bt Bs) :
    (∑ j, (if Bs.pts ⊆ (eSeq T ℜ s (idxT ℜ.α s r j)).pts then 1 else 0) * cT T ℜ r s j) =
      (∑ j, (if Bt.pts ⊆ ((𝒮.eTilde s j).emptyIfBot).pts then 1 else 0) * cT T ℜ r s j) +
        𝒮.droppedWeight s := by
  unfold droppedWeight
  rw [Finset.sum_filter, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  by_cases hj : 𝒮.eTilde s j = ⊥
  · have h1 : Bs.pts ⊆ (eSeq T ℜ s (idxT ℜ.α s r j)).pts := by
      refine (hd.pts_subset_eTilde_iff j).mp ?_
      rw [hj]
      exact fun x _ => Subscheme.mem_pts_bot x
    have h2 : ¬ Bt.pts ⊆ ((𝒮.eTilde s j).emptyIfBot).pts := by
      rw [Subscheme.pts_emptyIfBot_eq_empty hj]
      intro hsub
      obtain ⟨x, hx⟩ := pts_nonempty_of_isIrreducible Bt hd.irreducible_t
      exact hsub hx
    have e1 : (if Bs.pts ⊆ (eSeq T ℜ s (idxT ℜ.α s r j)).pts then 1 else 0) = 1 := by
      simp only [h1, ↓reduceIte]
    have e2 : (if Bt.pts ⊆ ((𝒮.eTilde s j).emptyIfBot).pts then 1 else 0) = 0 := by
      simp only [h2, ↓reduceIte]
    have e3 : (if 𝒮.eTilde s j = ⊥ then cT T ℜ r s j else 0) = cT T ℜ r s j := by
      simp only [hj, ↓reduceIte]
    rw [e1, e2, e3]
    ring
  · rw [Subscheme.pts_emptyIfBot_of_ne_bot hj]
    have : (if Bs.pts ⊆ (eSeq T ℜ s (idxT ℜ.α s r j)).pts then 1 else 0) =
        (if Bt.pts ⊆ (𝒮.eTilde s j).pts then 1 else 0) := by
      simp only [hd.pts_subset_eTilde_iff j]
    rw [this]
    simp [hj]

open Classical in
/-- **The total transform of the repaired `J̄*(s)`** (p. 325): `f̄_s⁻¹(J̄*(s)) = P̄_{s+1}^{b̃} ·
J̄*(s+1)`, `b̃ = b̄ · d_s` (`b̄` if `d_s = 0`).  The exponent of the new divisor is `c'_{α̃+1} = e_K
-
d_s` where `e_K = ∑_{B̃ ⊆ Ẽ_j, kept} c_j`.

Deviation from the paper (proof corrected, repair of the paper's error on the subschemes `Ẽ_j`): for `d_s = 0`
(this covers `ν ≥ b`) it is `f̄_s⁻¹(J̄(s)) = J̄(s+1) P̄_{s+1}^{b̄}`; for `d_s > 0` it is the printed
computation with `b - ν` replaced by `d_s` and the dropped traces left out. -/
theorem stalkIdeal_totalTransform_jBarRep [Hironaka.HironakaCitedResults.{u}] (hprep : PrepHyp N ℜ r ν T x₀ s)
    (hd : 𝒮.CenterData s Bt Bs) {bt : ℕ} {a : Fin (alphaT r ℜ.α s) → ℕ}
    {Jt : Subscheme (𝒮.xTilde s)} (hII : ((𝒮.datumTilde s bt a Jt).emptyIfBot).IsWeakDatum)
    (hperm : ((𝒮.datumTilde s bt a Jt).emptyIfBot).IsPermissible Bt)
    (h : AB.IsMonoidalTransformationOf (𝒮.fBar s) Bt) (yb : (𝒮.xBar (s + 1)).toScheme) :
    (Subscheme.totalTransform (𝒮.fBar s) (𝒮.jBarRep s)).stalkIdeal yb =
      ((𝒮.pBar s).stalkIdeal yb) ^ (𝒮.bTildeRep s) * (𝒮.jBarRep (s + 1)).stalkIdeal yb := by
  have hadm := 𝒮.isAdmissibleAt_of_prepHyp hprep
  have hsucc := thresholdRep_succ hadm hd hII hperm h
  by_cases hdz : 𝒮.thresholdRep s = 0
  · have hdz' : 𝒮.thresholdRep (s + 1) = 0 := hsucc.trans hdz
    rw [jBarRep_eq_of_thresholdRep_eq_zero hdz, jBarRep_eq_of_thresholdRep_eq_zero hdz',
      bTildeRep_eq_of_thresholdRep_eq_zero hdz, stalkIdeal_totalTransform_jBar hadm yb, mul_comm]
  · have hdz' : 𝒮.thresholdRep (s + 1) ≠ 0 := hsucc ▸ hdz
    have hlt : ν < ℜ.b := by unfold thresholdRep at hdz; omega
    have hcl := cT_succ_lastT_add_eq (𝒮 := 𝒮) hprep hlt hd
    have hsplit := sum_mul_cT_eq hd
    set eK := ∑ j, (if Bt.pts ⊆ ((𝒮.eTilde s j).emptyIfBot).pts then 1 else 0) * cT T ℜ r s j
      with heK
    have hcl' : cT T ℜ r (s + 1) (lastT r ℜ.α s) + 𝒮.thresholdRep s = eK := by
      unfold thresholdRep at hdz ⊢
      omega
    have hpb := pBar_ne_bot hadm hd hII hperm h
    have hprod : ∏ j, (((𝒮.eTilde (s + 1) (castSuccT r ℜ.α s j)).emptyIfBot).stalkIdeal yb *
          ((𝒮.pBar s).stalkIdeal yb) ^
            (if Bt.pts ⊆ ((𝒮.eTilde s j).emptyIfBot).pts then 1 else 0)) ^ (cT T ℜ r s j) =
        (∏ j, (((𝒮.eTilde (s + 1) (castSuccT r ℜ.α s j)).emptyIfBot).stalkIdeal yb) ^
          (cT T ℜ r s j)) * ((𝒮.pBar s).stalkIdeal yb) ^ eK := by
      simp only [mul_pow, Finset.prod_mul_distrib, ← pow_mul, Finset.prod_pow_eq_pow_sum, heK]
    have hR : (𝒮.jBarRep (s + 1)).stalkIdeal yb =
        ((𝒮.jBar (s + 1)).stalkIdeal yb) ^ (𝒮.thresholdRep s) ⊔
          ((∏ j, (((𝒮.eTilde (s + 1) (castSuccT r ℜ.α s j)).emptyIfBot).stalkIdeal yb) ^
            (cT T ℜ r s j)) *
            ((𝒮.pBar s).stalkIdeal yb) ^ (cT T ℜ r (s + 1) (lastT r ℜ.α s))) ^ 𝒮.bBar := by
      rw [jBarRep_eq_of_thresholdRep_ne_zero hdz', hsucc, Scheme.IdealSheafData.add_eq_sup,
        Subscheme.stalkIdeal_sup_eq, Subscheme.stalkIdeal_pow_eq, Subscheme.stalkIdeal_pow_eq,
        prod_alphaT_succ, Subscheme.stalkIdeal_mul_eq, stalkIdeal_prod_eq,
        Subscheme.stalkIdeal_pow_eq, ← 𝒮.eTilde_succ_lastT_eq_pBar s,
        Subscheme.emptyIfBot_of_ne_bot (by rw [𝒮.eTilde_succ_lastT_eq_pBar s]; exact hpb)]
      simp only [Subscheme.stalkIdeal_pow_eq, cT_succ_castSuccT]
    rw [hR, jBarRep_eq_of_thresholdRep_ne_zero hdz, bTildeRep_eq_of_thresholdRep_ne_zero hdz,
      Scheme.IdealSheafData.add_eq_sup, stalkIdeal_totalTransform, Subscheme.stalkIdeal_sup_eq,
      Ideal.map_sup, Subscheme.stalkIdeal_pow_eq, Subscheme.stalkIdeal_pow_eq, Ideal.map_pow,
      Ideal.map_pow, ← stalkIdeal_totalTransform, ← stalkIdeal_totalTransform,
      stalkIdeal_totalTransform_jBar hadm yb,
      stalkIdeal_totalTransform_prod_emptyIfBot hadm hd hII hperm h _ yb, hprod]
    exact Ideal.sup_pow_mul_eq _ _ _ 𝒮.bBar (𝒮.thresholdRep s) _ eK hcl'.symm

end Frame

end CD

namespace CD

variable {X : Scheme.{u}} {N : ℕ} {ℜ : DatumII.Raw X} {r : Restriction X} {ν : ℕ}
  {T : AB.Tower X} {x₀ : X}

namespace Frame

variable {hS : Standing N ℜ r ν T x₀} {𝒮 : Frame hS}
  {s : ℕ} {Bt : Subscheme (𝒮.xTilde s)} {Bs : Subscheme (T.X s)}

open Classical in
/-- The normalization of the exponents commutes with the extension by a new exponent. -/
theorem aRep_succ_extendA [Hironaka.HironakaCitedResults.{u}] (hadm : 𝒮.IsAdmissibleAt s)
    (hd : 𝒮.CenterData s Bt Bs) {bt : ℕ} {a : Fin (alphaT r ℜ.α s) → ℕ}
    {Jt : Subscheme (𝒮.xTilde s)} (hII : ((𝒮.datumTilde s bt a Jt).emptyIfBot).IsWeakDatum)
    (hperm : ((𝒮.datumTilde s bt a Jt).emptyIfBot).IsPermissible Bt)
    (h : AB.IsMonoidalTransformationOf (𝒮.fBar s) Bt) (a₀ : Fin (alphaT r ℜ.α s) → ℕ)
    (anew : ℕ) : 𝒮.aRep (s + 1) (extendA a₀ anew) = extendA (𝒮.aRep s a₀) anew := by
  funext i
  obtain ⟨k, rfl⟩ : ∃ k : Fin (alphaT r ℜ.α s + 1), i = Fin.cast (alphaT_succ r ℜ.α s).symm k :=
    ⟨Fin.cast (alphaT_succ r ℜ.α s) i, Fin.ext rfl⟩
  induction k using Fin.lastCases with
  | last =>
    have hl : 𝒮.eTilde (s + 1) (lastT r ℜ.α s) ≠ ⊥ := by
      rw [eTilde_succ_lastT_eq_pBar]
      exact pBar_ne_bot hadm hd hII hperm h
    change (if 𝒮.eTilde (s + 1) (lastT r ℜ.α s) = ⊥ then 0 else
      extendA a₀ anew (lastT r ℜ.α s)) = extendA (𝒮.aRep s a₀) anew (lastT r ℜ.α s)
    rw [extendA_lastT, extendA_lastT]
    simp only [hl, ↓reduceIte]
  | cast j =>
    change (if 𝒮.eTilde (s + 1) (castSuccT r ℜ.α s j) = ⊥ then 0 else
      extendA a₀ anew (castSuccT r ℜ.α s j)) = extendA (𝒮.aRep s a₀) anew (castSuccT r ℜ.α s j)
    rw [extendA_castSuccT, extendA_castSuccT]
    unfold aRep
    simp only [eTilde_succ_castSuccT_eq_bot_iff hadm hd hII hperm h j]

end Frame

end CD

namespace CD

variable {X : Scheme.{u}} {N : ℕ} {ℜ : DatumII.Raw X} {r : Restriction X} {ν : ℕ}
  {T : AB.Tower X} {x₀ : X}

open Classical in
/-- **The relation of p. 322 and Remark 3 (pp. 324–326) for the repaired datum, uniform in `ν`.**
Let `B̃` be as in Remarks 1–2 and `B = B_s` the subscheme of `X_s` of Remark 1/2 (the center of
`f_s`).  Then `f̂_s` induces the monoidal transformation `f̄_s : X̄_{s+1} → X̄_s` with center `B̃`,
and the transform of the emptied `ℜ̃` along `f̄_s` is the emptied `ℜ̃` of the next stage,
`f̄_s*(ℜ̃) = (Ẽ'_1, …, Ẽ'_{α̃+1} | J̃', b̃ | ã_1, …, ã_{α̃+1})^e` with `J̃' ∏ ((Ẽ'_j)^e)^{ã_j} =
J̄*(s+1)`: "the relation between `ℜ(s+1)` and `f̄_s*(ℜ̃)` is the same as that between `ℜ(s)` and
`ℜ̃`".

Deviation from the paper (proof corrected, repair of the paper's error on the subschemes `Ẽ_j`): the printed
statements are the relation of p. 322 (`ν ≥ b`) and Remark 3 (`ν < b`).  Here the datum is the
emptied one and `b - ν` is replaced by `d_s = b - ν - δ_s`; `δ_{s+1} = δ_s` (the dropped traces stay
dropped), so `b̃` is unchanged and the sheaf of ideals `J̄*(s)` has the same form at `s+1`. -/
@[blueprint "rem:IV.4-3-repaired"
  (statement := /-- \textbf{Remark 3, repaired} (uniform in $\nu$). Let $\tilde B$ and $B_s$ be as
    in \cref{rem:IV.4-2-repaired}. Let $\tilde f\colon\tilde X'\to\tilde X$ be the monoidal
    transformation with center $\tilde B$, which is permissible for the resolution datum
    $\tilde{\mathfrak R}^e$, and $f_s\colon X_{s+1}\to X_s$ the one with center $B_s$, which is
    permissible for $\mathfrak R(s)$. Put $\mathfrak R(s+1)=f_s^*(\mathfrak R(s))$,
    $\bar X_{s+1}=$ the strict transform of $\bar X_s$ in $\hat X_{s+1}$, $\bar J(s+1)=\bar
    f_s^{-1}(\bar J(s))/(\bar P_{s+1})^{\bar b}$, and define $\tilde E'_j$, $c'_j$, $\bar
    J^\sharp(s+1)$ for $h_{s+1}=f_s\circ h_s$ as for $h_s$
    (\cref{def:IV.4-case-lt-repaired}); $\delta_{s+1}=\delta_s$. We may set $\tilde X'=\bar
    X_{s+1}$ and $\tilde f=\bar f_s$. Then $\tilde f^*(\tilde{\mathfrak R}^e)$ on $\tilde X'$ can
    be written in the form $\big((\tilde E'_1)^e,\dots,(\tilde E'_{\tilde\alpha+1})^e\,\big|\,
    \tilde J',\tilde b\,\big|\,\tilde a_1,\dots,\tilde a_{\tilde\alpha+1}\big)$ with $\tilde
    J'\prod_j((\tilde P'_j)^e)^{\tilde a_j}=\bar J^\sharp(s+1)$; the relation between
    $\mathfrak R(s+1)$ and $\tilde f^*(\tilde{\mathfrak R}^e)$ is the same as that between
    $\mathfrak R(s)$ and $\tilde{\mathfrak R}^e$. (Replaces Remark~3, \cref{rem:IV.4-3},
    pp.~324--325, and \cref{lem:IV.4-case-ge-relation}, p.~322.)

    \textbf{Deviation from the paper (proof corrected, repair of the paper's error on the subschemes $\tilde E_j$).} The
    printed Remark~3 reads: ``$\tilde f^*(\mathfrak R^{N-1}_{\mathrm{II}})$ on $\tilde X'$ can be
    written in the form $(\tilde E'_1,\dots,\tilde E'_{\tilde\alpha+1}\,|\,\tilde J',\tilde
    b\,|\,\tilde a_1,\dots,\tilde a_{\tilde\alpha+1})$'' for the datum of \cref{def:IV.4-case-lt},
    which is not a resolution datum. Here the datum is the
    emptied one with the shifted threshold: $\tilde b$ is unchanged because $\delta_{s+1}=
    \delta_s$ (a dropped trace stays dropped), and the exponent of the new divisor is
    $c'_{\tilde\alpha+1}=e_K-d_s$ with $e_K=\sum_{\tilde B\subseteq\tilde E_j,\,\mathrm{kept}}c_j$
    in place of $e-(b-\nu)$. -/)
  (proof := /-- (pp.~324--326.) The strict transform of a kept $\tilde E_j$ is $\tilde E'_j$, and
    $\bar f_s^{-1}(\tilde E_j)=\tilde E'_j\bar P_{s+1}^{m_j}$ with $m_j=1$ if and only if $B_s
    \subseteq E_j(s)$; a dropped trace stays dropped. By Definition~7 (II) the datum $\bar
    f_s^*(\tilde{\mathfrak R}^e)$ has the strict transforms of the $\tilde E^e_j$, the total
    transform $\bar P_{s+1}$ of $\tilde B$ as new divisor, and $\tilde J'\prod_j((\tilde
    P'_j)^e)^{\tilde a_j}=\bar f_s^{-1}(\tilde J\prod_j(\tilde P^e_j)^{\tilde a_j})\bar
    P_{s+1}^{-\tilde b}=\bar f_s^{-1}(\bar J^\sharp(s))\bar P_{s+1}^{-\tilde b}$. It remains to
    show $\bar f_s^{-1}(\bar J^\sharp(s))=\bar P_{s+1}^{\tilde b}\bar J^\sharp(s+1)$: for $d_s=0$
    this is $\bar f_s^{-1}(\bar J(s))=\bar P_{s+1}^{\bar b}\bar J(s+1)$; for $d_s>0$ it follows from
    $c'_{\tilde\alpha+1}+d_s=e_K$, which is $c'_{\tilde\alpha+1}+(b-\nu)=e$ (the sums over $B_s
    \subseteq E_j(s)$ and $\tilde B\subseteq\tilde E_j$ agree by $[(2)]$) and $e=e_K+\delta_s$,
    every dropped $E_j(s)=F(s)$ containing $B_s$.

    \textbf{Deviation from the paper (proof corrected, repair of the paper's error on the subschemes $\tilde E_j$).} See the
    statement. -/)
  (proofUses := ["rem:IV.4-2-repaired", "def:IV.4-case-lt-repaired", "lem:IV.4-Pbar",
    "def:I.7-II", "lem:IV.4-exceptional-transversal-nonsingular", "lem:IV.tilde-drop"])
  (latexEnv := "remark")]
theorem Frame.ker_eq_B_and_exists_transform_eq_datumRep [Hironaka.HironakaCitedResults.{u}] {hS : Standing N ℜ r ν T x₀}
    (𝒮 : Frame hS) (s : ℕ) (hprep : PrepHyp N ℜ r ν T x₀ s)
    (a : Fin (alphaT r ℜ.α s) → ℕ) (Jt : Subscheme (𝒮.xTilde s))
    (hJt : Jt * ∏ j, ((𝒮.eTilde s j).emptyIfBot) ^ (a j) = 𝒮.jBarRep s)
    (hJne : ∀ x, Jt.stalkIdeal x ≠ ⊥)
    (Bt : Subscheme (𝒮.xTilde s)) (hBt : Bt.IsNonsingular) (hBti : Bt.IsIrreducible)
    (hperm : (𝒮.datumRep s a Jt).IsPermissible Bt)
    (B : Subscheme (T.X s)) (hB : B.IsNonsingular ∧ B.IsIrreducible)
    (hBe : ∃ e : Bt.toScheme ≅ B.toScheme, e.hom ≫ B.ι = Bt.ι ≫ 𝒮.cBar s)
    (hBperm : (restriction T r s).IsPermissibleCenter (datum T ℜ s) B) (hTB : T.B s = B) :
    (Bt.ι ≫ (𝒮.xBar s).ι).ker = 𝒮.tHat.B s ∧
    ∃ h : AB.IsMonoidalTransformationOf (𝒮.fBar s) Bt,
      ∃ (anew : ℕ) (Jt' : Subscheme (𝒮.xTilde (s + 1))),
        (𝒮.datumRep s a Jt).transform
            (⟨_, 𝒮.fBar s, h.1, h.2⟩ : MonoidalTransformation (𝒮.xTilde s) Bt) =
          𝒮.datumRep (s + 1) (extendA a anew) Jt' ∧
        Jt' * ∏ j, ((𝒮.eTilde (s + 1) j).emptyIfBot) ^ (extendA a anew j) =
          𝒮.jBarRep (s + 1) := by
  classical
  have hadm := 𝒮.isAdmissibleAt_of_prepHyp hprep
  have hII := 𝒮.isWeakDatum_datumRep hprep a Jt hJne
  have hmem : ∀ xb ∈ Bt.pts, (𝒮.cBar s).base xb ∈ (datum T ℜ s).sNu ν := fun xb hxb =>
    (Frame.cBar_mem_sNu_and_hBar_eq_of_mem_S_datumRep hprep hJt hJne (hperm.2.1 hxb).1).1
  obtain ⟨B₀, hB₀ns, hB₀irr, hker₀, hiso₀, hpts₀⟩ :=
    𝒮.exists_ker_eq_totalTransform_of_forall_mem_sNu s hprep Bt hBt hBti hmem
  have hBeq : B = B₀ := AB.eq_of_isReduced_of_pts_eq
    (Hironaka.DatumTransform.isReduced_of_isNonsingular hB.1)
    (Hironaka.DatumTransform.isReduced_of_isNonsingular hB₀ns)
    ((pts_eq_image_cBar_of_iso hBe).trans hpts₀.symm)
  subst hBeq
  have hd : 𝒮.CenterData s Bt B := ⟨hBt, hBti, hB.1, hB.2, hker₀, hBe, hBperm, hTB⟩
  have h := 𝒮.isMonoidalTransformationOf_fBar_of_ker_eq s hd.ker_eq_B
  have hsucc := bTildeRep_succ hadm hd hII hperm h
  have heq := transform_datumTilde_emptyIfBot_eq hadm hd hII hperm h
  refine ⟨hd.ker_eq_B, h, (((𝒮.datumRep s a Jt).transform (𝒮.tBar s h)).a (Fin.last _)),
    ((𝒮.datumRep s a Jt).transform (𝒮.tBar s h)).J, ?_, ?_⟩
  · -- the transform is the emptied datum of the next stage
    have hrep : 𝒮.datumRep (s + 1) (extendA a
        (((𝒮.datumRep s a Jt).transform (𝒮.tBar s h)).a (Fin.last _)))
        ((𝒮.datumRep s a Jt).transform (𝒮.tBar s h)).J =
        (𝒮.datumTilde (s + 1) (𝒮.bTildeRep s)
          (extendA (𝒮.aRep s a)
            (((𝒮.datumRep s a Jt).transform (𝒮.tBar s h)).a (Fin.last _)))
          ((𝒮.datumRep s a Jt).transform (𝒮.tBar s h)).J).emptyIfBot := by
      unfold datumRep
      rw [hsucc, aRep_succ_extendA hadm hd hII hperm h]
    exact heq.trans hrep.symm
  · -- the identity `J̃' ∏ (Ẽ'_j)^{ã_j} = J̄*(s+1)`
    have hprodS := prod_emptyIfBot_pow_aRep (𝒮 := 𝒮) s a
    have hW : ∀ yb : (𝒮.xBar (s + 1)).toScheme,
        (Subscheme.totalTransform (𝒮.fBar s)
          (Jt * ∏ j, ((𝒮.eTilde s j).emptyIfBot) ^ (𝒮.aRep s a j))).stalkIdeal yb =
          ((𝒮.pBar s).stalkIdeal yb) ^ (𝒮.bTildeRep s) * (𝒮.jBarRep (s + 1)).stalkIdeal yb := by
      intro yb
      rw [hprodS, hJt]
      exact stalkIdeal_totalTransform_jBarRep hprep hd hII hperm h yb
    have key := prod_eq_of_stalkIdeal_totalTransform_eq_of_emptyIfBot hadm hd hII hperm h
      (𝒮.jBarRep (s + 1)) hW
    rw [← prod_emptyIfBot_pow_aRep (𝒮 := 𝒮) (s + 1) (extendA a _),
      aRep_succ_extendA hadm hd hII hperm h]
    exact key

end CD

/-! ## 9. The interface for the induction of Theorems C and D*

The three statements that the lifting of a resolving succession of `X̃` to `X_s` calls (one per
step), the end of the induction, the initial datum and the comparison with the printed datum
without restriction. -/

namespace CD

variable {X : Scheme.{u}} {N : ℕ} {ℜ : DatumII.Raw X} {r : Restriction X} {ν : ℕ}
  {T : AB.Tower X} {x₀ : X}

namespace Frame

variable {hS : Standing N ℜ r ν T x₀} (𝒮 : Frame hS)

/-- `X̃ = X̄_s` is a non-singular irreducible algebraic scheme of dimension `N - 1` (p. 321, first
sentence of the facts "we see"): it is an ambient scheme in the sense of Ch. I §2, so that Theorem
`II₂^{N-1}` can be applied to it.  No hypothesis `F ≠ E_i` (`isAmbient_xTilde` of `ImplicationsCD`
carries one that it does not use). 

Deviation from the paper (proof corrected, repair of the paper's error on the subschemes `Ẽ_j`): the
statement is proved for the repaired datum `datumRep`. -/
theorem isAmbient_xTilde_of_prepHyp [Hironaka.HironakaCitedResults.{u}] {s : ℕ} (hprep : PrepHyp N ℜ r ν T x₀ s) :
    IsAmbient (𝒮.xTilde s) (N - 1) := by
  obtain ⟨h1, h2, h3⟩ :=
    𝒮.isNonsingular_and_isIrreducible_and_dim_xBar s (𝒮.isAdmissibleAt_of_prepHyp hprep)
  have := 𝒮.isAlgebraicScheme_tHat_X s
  exact ⟨isAlgebraicScheme_toScheme (𝒮.xBar s), h1, h2, h3⟩

/-- **The end of the induction** (p. 322: "if `ℜ^{N-1}_II` is resolved, then `S_ν(ℜ(s)) ∩
h_s⁻¹(x_0)` is empty"): under `[(1)]`, `x_0 ∈ h_s(S_ν(ℜ(s)))`, the set `S(ℜ̃)` of the repaired
datum is non-empty, for every `ν`. 

Deviation from the paper (proof corrected, repair of the paper's error on the subschemes `Ẽ_j`): the
statement is proved for the repaired datum `datumRep`. -/
theorem S_datumRep_nonempty [Hironaka.HironakaCitedResults.{u}] {s : ℕ} (hprep : PrepHyp N ℜ r ν T x₀ s)
    (a : Fin (alphaT r ℜ.α s) → ℕ) (Jt : Subscheme (𝒮.xTilde s))
    (hJt : Jt * ∏ j, ((𝒮.eTilde s j).emptyIfBot) ^ (a j) = 𝒮.jBarRep s)
    (hJne : ∀ x, Jt.stalkIdeal x ≠ ⊥) : (𝒮.datumRep s a Jt).S.Nonempty := by
  obtain ⟨y, hy, hyx⟩ := hprep.2.2.2
  have hyfib : y ∈ (T.pre s).composite.base ⁻¹' {x₀} := hyx
  obtain ⟨xb, hxb, -⟩ := (bijOn_cBar_S_datumRep hprep hJt hJne).surjOn ⟨hy, hyfib⟩
  exact ⟨xb, hxb⟩

/-- If `J̃ ∏ (Ẽ^e_j)^{ã_j} = J̄*(s)` and `J̄*(s)` has non-zero stalks, so has `J̃`
(Definition 3 (II) (iii) for the auxiliary datum). -/
theorem stalkIdeal_ne_bot_of_mul_eq_jBarRep [Hironaka.HironakaCitedResults.{u}] {s : ℕ} (hprep : PrepHyp N ℜ r ν T x₀ s)
    (hJ : 𝒮.thresholdRep s = 0 → ∀ x, (𝒮.jBar s).stalkIdeal x ≠ ⊥)
    (a : Fin (alphaT r ℜ.α s) → ℕ) (Jt : Subscheme (𝒮.xTilde s))
    (hJt : Jt * ∏ j, ((𝒮.eTilde s j).emptyIfBot) ^ (a j) = 𝒮.jBarRep s)
    (x : 𝒮.xTilde s) : Jt.stalkIdeal x ≠ ⊥ := by
  intro h
  apply 𝒮.stalkIdeal_jBarRep_ne_bot hprep hJ x
  rw [← hJt, Subscheme.stalkIdeal_mul_eq, h, Ideal.bot_mul]

/-- Without restriction no trace `Ẽ_j` is the whole space: `X̄_s` is not contained in the boundary
(`modelDatum_main`, the hypothesis `F ≠ E_i` being void). -/
theorem eTilde_ne_bot_of_unrestricted [Hironaka.HironakaCitedResults.{u}] {s : ℕ} (hprep : PrepHyp N ℜ r ν T x₀ s)
    (hr : r = .unrestricted) (j : Fin (alphaT r ℜ.α s)) : 𝒮.eTilde s j ≠ ⊥ := by
  have hadm := 𝒮.isAdmissibleAt_of_prepHyp hprep
  obtain ⟨-, -, -, hWE⟩ := 𝒮.modelDatum_main s hadm (fun F hF => by rw [hr] at hF; cases hF)
  intro hj
  apply hWE
  intro x hx
  obtain ⟨x', rfl⟩ : x ∈ Set.range (𝒮.xBar s).ι.base := by
    rw [← pts_eq_range]; exact hx
  have h1 : x' ∈ (𝒮.eTilde s j).pts := by rw [hj]; exact Subscheme.mem_pts_bot x'
  have h2 : (𝒮.xBar s).ι.base x' ∈ (𝒮.eHat s (idxT ℜ.α s r j)).pts :=
    (Subscheme.mem_pts_totalTransform_subschemeι_iff x').mp h1
  rw [pts_transformI_modelDatum_E]
  exact Set.mem_iUnion₂.mpr ⟨idxT ℜ.α s r j, inBoundary_idxT r ℜ.α s j, h2⟩

/-- Without restriction nothing is dropped: `δ_s = 0`. -/
theorem droppedWeight_eq_zero_of_unrestricted [Hironaka.HironakaCitedResults.{u}] {s : ℕ} (hprep : PrepHyp N ℜ r ν T x₀ s)
    (hr : r = .unrestricted) : 𝒮.droppedWeight s = 0 := by
  classical
  unfold droppedWeight
  refine Finset.sum_eq_zero fun j hj => ?_
  exact absurd (Finset.mem_filter.mp hj).2 (𝒮.eTilde_ne_bot_of_unrestricted hprep hr j)

/-- Without restriction the repaired `b̃` is the printed one, `btOf b ν`. -/
theorem bTildeRep_eq_btOf_of_unrestricted [Hironaka.HironakaCitedResults.{u}] {s : ℕ} (hprep : PrepHyp N ℜ r ν T x₀ s)
    (hr : r = .unrestricted) : 𝒮.bTildeRep s = btOf ℜ.b ν := by
  by_cases hge : ℜ.b ≤ ν
  · rw [(jBarRep_eq_jBar_of_le hge).2]
    simp only [btOf, hge, ↓reduceIte]
    rfl
  · have hlt : ν < ℜ.b := by omega
    rw [(jBarRep_eq_jBarStar (𝒮.droppedWeight_eq_zero_of_unrestricted hprep hr) hlt).2]
    simp only [btOf, hge, ↓reduceIte]
    rfl

/-- Without restriction the repaired datum is the printed `ℜ̃`, `datumTilde`. -/
theorem datumRep_eq_datumTilde_of_unrestricted [Hironaka.HironakaCitedResults.{u}] {s : ℕ} (hprep : PrepHyp N ℜ r ν T x₀ s)
    (hr : r = .unrestricted) (a : Fin (alphaT r ℜ.α s) → ℕ) (Jt : Subscheme (𝒮.xTilde s)) :
    𝒮.datumRep s a Jt = 𝒮.datumTilde s (btOf ℜ.b ν) a Jt := by
  have hne := 𝒮.eTilde_ne_bot_of_unrestricted hprep hr
  have ha : 𝒮.aRep s a = a := by
    funext j; unfold aRep; simp only [hne j, ↓reduceIte]
  unfold datumRep
  rw [ha, 𝒮.bTildeRep_eq_btOf_of_unrestricted hprep hr]
  unfold DatumII.Raw.emptyIfBot
  congr 1
  funext j
  exact Subscheme.emptyIfBot_of_ne_bot (hne j)

end Frame

end CD

/-! ## 10. The statements called by the induction, in the shapes of Remarks 1 and 3 -/

namespace CD

variable {X : Scheme.{u}} {N : ℕ} {ℜ : DatumII.Raw X} {r : Restriction X} {ν : ℕ}
  {T : AB.Tower X} {x₀ : X}

/-- **Remark 1 for the repaired datum** (pp. 321–322): a non-singular irreducible `B̃ ⊆ X̃` such
that
the monoidal transformation with center `B̃` is permissible for `ℜ̃` comes from a non-singular
irreducible `B ⊆ X_s` with `B̃ = c_s⁻¹(B)`, `c̄_s` inducing `B̃ ≅ B`, and `f_s` permissible for
`ℜ(s)`.  A corollary of the uniform Remarks 1–2; valid for every `ν` (for `ν ≥ b` it is
the printed Remark 1). -/
@[blueprint "rem:IV.4-1-repaired"
  (statement := /-- \textbf{Remark 1, repaired.} Notation as in \cref{def:IV.4-conditions} and
    \cref{def:IV.4-case-lt-repaired} (for $\nu\ge b$: $\tilde J=\bar J(s)$, $\tilde b=\bar b$,
    \cref{def:IV.4-case-ge}). Let $\tilde B$ be a non-singular irreducible subscheme of $\tilde X$
    such that the monoidal transformation $\tilde f$ of $\tilde X$ with center $\tilde B$ is
    permissible for the resolution datum $\tilde{\mathfrak R}^e$. Then there exists a
    non-singular irreducible subscheme $B$ of $X_s$ such that $c_s\colon\hat X_s\to X_s$ induces
    an isomorphism of $\tilde B\to B$, and the monoidal transformation $f_s$ of $X_s$ with center
    $B$ is permissible for the resolution datum $\mathfrak R(s)$. (Replaces Remark~1,
    \cref{rem:IV.4-1}, pp.~321--322.)

    \textbf{Deviation from the paper (proof corrected, repair of the paper's error on the subschemes $\tilde E_j$).} The
    paper presupposes that $\mathfrak R^{N-1}_{\mathrm{II}}$ is a resolution datum ($\tilde E_j$
    non-singular irreducible of codimension one); this is false.
    The datum is the emptied $\tilde{\mathfrak R}^e$, a weak datum. -/)
  (proof := /-- A special case of \cref{rem:IV.4-2-repaired}, which treats every $\nu$ at
    once: the points of $\tilde B$ lie in $S(\tilde{\mathfrak R}^e)$, which $c_s$ maps into $S_\nu(
    \mathfrak R(s))\cap h_s^{-1}(x_0)$ (Lemma (CD.5), \cref{lem:IV.CD-5}), and Lemma (CD.3)
    (\cref{lem:IV.CD-3}) gives $B$. -/)
  (proofUses := ["rem:IV.4-2-repaired", "lem:IV.CD-5", "lem:IV.CD-3"])
  (latexEnv := "remark")]
theorem Frame.exists_isPermissibleCenter_of_isPermissible_datumRep [Hironaka.HironakaCitedResults.{u}] {hS : Standing N ℜ r ν T x₀}
    (𝒮 : Frame hS) (s : ℕ) (hprep : PrepHyp N ℜ r ν T x₀ s)
    (a : Fin (alphaT r ℜ.α s) → ℕ) (Jt : Subscheme (𝒮.xTilde s))
    (hJt : Jt * ∏ j, ((𝒮.eTilde s j).emptyIfBot) ^ (a j) = 𝒮.jBarRep s)
    (hJne : ∀ x, Jt.stalkIdeal x ≠ ⊥)
    (Bt : Subscheme (𝒮.xTilde s)) (hBt : Bt.IsNonsingular) (hBti : Bt.IsIrreducible)
    (hperm : (𝒮.datumRep s a Jt).IsPermissible Bt) :
    ∃ B : Subscheme (T.X s), B.IsNonsingular ∧ B.IsIrreducible ∧
      (Bt.ι ≫ (𝒮.xBar s).ι).ker = Subscheme.totalTransform (𝒮.c s) B ∧
      (∃ e : Bt.toScheme ≅ B.toScheme, e.hom ≫ B.ι = Bt.ι ≫ 𝒮.cBar s) ∧
      (restriction T r s).IsPermissibleCenter (datum T ℜ s) B := by
  obtain ⟨-, -, h3⟩ :=
    𝒮.S_datumRep_eq_and_bijOn_cBar_and_exists_isPermissibleCenter s hprep a Jt hJt hJne
  obtain ⟨B, hB, -⟩ := h3 Bt hBt hBti hperm
  exact ⟨B, hB⟩

/-- **The relation of p. 322 for `ν ≥ b`**, in the shape of
`ker_eq_B_and_exists_transform_eq_datumTilde_of_ge`:
here `J̃ = J̄(s)`, `b̃ = b̄`, and the datum has the whole-space traces emptied. -/
@[blueprint "lem:IV.4-case-ge-relation-repaired"
  (statement := /-- In the case $\nu\ge b$ (so $\tilde J\prod_j(\tilde P^e_j)^{\tilde a_j}=\bar
    J(s)$, $\tilde b=\bar b$), let $\tilde B$ and $B$ be as in \cref{rem:IV.4-1-repaired}. We
    extend the permissible succession $h_s$ to include the monoidal transformation $f_s\colon
    X_{s+1}\to X_s$ with center $B$, and we replace $\bar X_s$ by the proper transform $\bar
    X_{s+1}$ of $\bar X_s$ in $\hat X_{s+1}$, so that $\hat f_s$ is the monoidal transformation
    with center $\tilde B=c_s^{-1}(B)$ and induces the monoidal transformation $\bar f_s\colon
    \bar X_{s+1}\to\bar X_s$ with the non-singular irreducible center $\tilde B$. Then
    $\bar f_s^*(\tilde{\mathfrak R}^e)$ is the datum $\big((\tilde E'_1)^e,\dots,(\tilde
    E'_{\tilde\alpha+1})^e\,\big|\,\tilde J',\bar b\,\big|\,\tilde a_1,\dots,\tilde
    a_{\tilde\alpha+1}\big)$ formed for $h_{s+1}$ with $\tilde J'\prod_j((\tilde P'_j)^e)^{\tilde
    a_j}=\bar J(s+1)$: the relation between $\mathfrak R(s+1)=f_s^*(\mathfrak R(s))$ and
    $\bar f_s^*(\tilde{\mathfrak R}^e)$ is the same as that between $\mathfrak R(s)$ and
    $\tilde{\mathfrak R}^e$. (Replaces \cref{lem:IV.4-case-ge-relation}, p.~322.)

    \textbf{Deviation from the paper (proof corrected, repair of the paper's error on the subschemes $\tilde E_j$).} The
    datum is the emptied $\tilde{\mathfrak R}^e$ (see \cref{rem:IV.4-1-repaired}). -/)
  (proof := /-- A special case of \cref{rem:IV.4-3-repaired} (uniform in $\nu$), with
    $\tilde J=\bar J(s)$, $\tilde b=\bar b$. -/)
  (proofUses := ["rem:IV.4-3-repaired"])
  (latexEnv := "lemma")]
theorem Frame.ker_eq_B_and_exists_transform_eq_datumRep_of_ge [Hironaka.HironakaCitedResults.{u}] {hS : Standing N ℜ r ν T x₀}
    (𝒮 : Frame hS) (s : ℕ) (hprep : PrepHyp N ℜ r ν T x₀ s) (hge : ℜ.b ≤ ν)
    (a : Fin (alphaT r ℜ.α s) → ℕ) (Jt : Subscheme (𝒮.xTilde s))
    (hJt : Jt * ∏ j, ((𝒮.eTilde s j).emptyIfBot) ^ (a j) = 𝒮.jBar s)
    (hJne : ∀ x, Jt.stalkIdeal x ≠ ⊥)
    (Bt : Subscheme (𝒮.xTilde s)) (hBt : Bt.IsNonsingular) (hBti : Bt.IsIrreducible)
    (hperm : (𝒮.datumRep s a Jt).IsPermissible Bt)
    (B : Subscheme (T.X s)) (hB : B.IsNonsingular ∧ B.IsIrreducible)
    (hBe : ∃ e : Bt.toScheme ≅ B.toScheme, e.hom ≫ B.ι = Bt.ι ≫ 𝒮.cBar s)
    (hBperm : (restriction T r s).IsPermissibleCenter (datum T ℜ s) B) (hTB : T.B s = B) :
    (Bt.ι ≫ (𝒮.xBar s).ι).ker = 𝒮.tHat.B s ∧
    ∃ h : AB.IsMonoidalTransformationOf (𝒮.fBar s) Bt,
      ∃ (anew : ℕ) (Jt' : Subscheme (𝒮.xTilde (s + 1))),
        (𝒮.datumRep s a Jt).transform
            (⟨_, 𝒮.fBar s, h.1, h.2⟩ : MonoidalTransformation (𝒮.xTilde s) Bt) =
          𝒮.datumRep (s + 1) (extendA a anew) Jt' ∧
        Jt' * ∏ j, ((𝒮.eTilde (s + 1) j).emptyIfBot) ^ (extendA a anew j) =
          𝒮.jBar (s + 1) := by
  rw [← (jBarRep_eq_jBar_of_le hge).1] at hJt
  obtain ⟨hker, h, anew, Jt', h1, h2⟩ :=
    𝒮.ker_eq_B_and_exists_transform_eq_datumRep s hprep a Jt hJt hJne Bt hBt hBti hperm B hB hBe
      hBperm hTB
  refine ⟨hker, h, anew, Jt', h1, ?_⟩
  rw [h2]
  exact (jBarRep_eq_jBar_of_le hge).1

/-- **The initial datum is resolvable** (p. 310: "Thus, applying Theorem `II₂^{N-1}` to the
resolution datum `ℜ^{N-1}_II` on `X̃`"): the repaired datum with `ã_j = 0` and `J̃ = J̄*(s)` is a
weak datum on the ambient scheme `X̃`, so `hglue` (Theorem `II₂^{N-1}` for weak data,
`DatumII.Raw.resolvable_of_isWeakDatum`) applies.  `hJ` is the non-vanishing of `J̄(s)` when
`d_s = 0` (the gap of p. 321 filled). -/
@[blueprint "lem:IV.4-tilde-resolvable-repaired"
  (statement := /-- Notation as in \cref{def:IV.4-conditions}. Let $\tilde a_j=0$ and $\tilde J=\bar
    J^\sharp(s)$ (\cref{def:IV.4-case-lt-repaired}), so that $\tilde{\mathfrak R}^e$ is the datum
    with $\tilde J\prod_j(\tilde P^e_j)^{\tilde a_j}=\bar J^\sharp(s)$. If Theorem
    $\mathrm{II}_2^{N-1}$ holds, then $\tilde{\mathfrak R}^e$ can be resolved by a finite
    permissible succession of monoidal transformations of $\tilde X$. (Replaces p.~310 and
    p.~322: ``Thus, applying Theorem $\mathrm{II}_2^{N-1}$ to the resolution datum
    $\mathfrak R^{N-1}_{\mathrm{II}}$ on $\tilde X$''.)

    \textbf{Deviation from the paper (proof corrected, repair of the paper's error on the subschemes $\tilde E_j$).}
    $\mathfrak R^{N-1}_{\mathrm{II}}$ is not a resolution datum; the emptied datum is a weak
    datum, which is resolvable by \cref{lem:IV.tilde-resolvable}. -/)
  (proof := /-- $\tilde X$ is a non-singular irreducible algebraic scheme of dimension $N-1$, and
    $\tilde{\mathfrak R}^e$ is a weak datum (\cref{lem:IV.4-tilde-facts-repaired}; the stalks of
    $\bar J^\sharp(s)$ are non-zero), hence resolvable (\cref{lem:IV.tilde-resolvable}). -/)
  (proofUses := ["lem:IV.4-tilde-facts-repaired", "lem:IV.tilde-resolvable",
    "def:IV.4-case-lt-repaired"])
  (latexEnv := "lemma")]
theorem Frame.resolvable_datumRep_zero [Hironaka.HironakaCitedResults.{u}] {hS : Standing N ℜ r ν T x₀} (𝒮 : Frame hS) {s : ℕ}
    (hprep : PrepHyp N ℜ r ν T x₀ s)
    (hJ : 𝒮.thresholdRep s = 0 → ∀ x, (𝒮.jBar s).stalkIdeal x ≠ ⊥)
    (hglue : ∀ Z : Scheme.{u}, IsAmbient Z (N - 1) → ∀ D : DatumII.Raw Z, D.IsWeakDatum →
      D.Resolvable) :
    (𝒮.datumRep s (fun _ => 0) (𝒮.jBarRep s)).Resolvable :=
  hglue _ (𝒮.isAmbient_xTilde_of_prepHyp hprep) _
    (𝒮.isWeakDatum_datumRep hprep _ _ (𝒮.stalkIdeal_jBarRep_ne_bot hprep hJ))

end CD

/-! ## 11. The same objects at the level of stage states

`FrameStage` is the tower-independent state of the construction used by the induction
(`FrameStage.fold`); the objects of the repair are repeated there and compared with the frame
versions (`Frame.stageOf`). -/

namespace CD

namespace FrameStage

variable {X Y : Scheme.{u}} (σ : FrameStage Y)

open Classical in
/-- `δ`, read on the stage state: the total exponent of the traces equal to the whole space. -/
noncomputable def droppedWeight (D : DatumII.Raw Y) (r : Restriction X) (α n : ℕ) : ℕ :=
  ∑ j ∈ Finset.univ.filter fun j : Fin (alphaT r α n) => σ.eTilde D r α n j = ⊥,
    D.aAt (idxN r α j)

/-- The shifted threshold `b - ν - δ`, read on the stage state. -/
noncomputable def thresholdRep (D : DatumII.Raw Y) (r : Restriction X) (α n b ν : ℕ) : ℕ :=
  b - ν - σ.droppedWeight D r α n

open Classical in
/-- The repaired sheaf of ideals `J̄*(s)`, read on the stage state (`Frame.jBarRep`). -/
noncomputable def jBarRep (D : DatumII.Raw Y) (r : Restriction X) (α n b ν bBar : ℕ) :
    Subscheme σ.xBar.toScheme :=
  if σ.thresholdRep D r α n b ν = 0 then σ.jBar
  else σ.jBar ^ (σ.thresholdRep D r α n b ν) + (∏ j : Fin (alphaT r α n),
    ((σ.eTilde D r α n j).emptyIfBot) ^ (D.aAt (idxN r α j))) ^ bBar

/-- The repaired `b̃`, read on the stage state (`Frame.bTildeRep`). -/
noncomputable def bTildeRep (D : DatumII.Raw Y) (r : Restriction X) (α n b ν bBar : ℕ) : ℕ :=
  if σ.thresholdRep D r α n b ν = 0 then bBar else bBar * σ.thresholdRep D r α n b ν

open Classical in
/-- The normalized exponents (`Frame.aRep`), read on the stage state. -/
noncomputable def aRep (D : DatumII.Raw Y) (r : Restriction X) (α n : ℕ)
    (a : Fin (alphaT r α n) → ℕ) : Fin (alphaT r α n) → ℕ :=
  fun j => if σ.eTilde D r α n j = ⊥ then 0 else a j

/-- The repaired auxiliary datum, read on the stage state (`Frame.datumRep`). -/
noncomputable def datumRep (D : DatumII.Raw Y) (r : Restriction X) (α n b ν bBar : ℕ)
    (a : Fin (alphaT r α n) → ℕ) (Jt : Subscheme σ.xBar.toScheme) :
    DatumII.Raw σ.xBar.toScheme :=
  (σ.datumTilde D r α n (σ.bTildeRep D r α n b ν bBar) (σ.aRep D r α n a) Jt).emptyIfBot

end FrameStage

section Bridge

variable {X : Scheme.{u}} {N : ℕ} {ℜ : DatumII.Raw X} {r : Restriction X} {ν : ℕ}
  {T : AB.Tower X} {x₀ : X} {hS : Standing N ℜ r ν T x₀}

theorem Frame.droppedWeight_eq_stageOf (𝒮 : Frame hS) (s : ℕ) :
    𝒮.droppedWeight s = (𝒮.stageOf s).droppedWeight (datum T ℜ s) r ℜ.α s := by
  classical
  unfold Frame.droppedWeight FrameStage.droppedWeight
  have h : ∀ j, 𝒮.eTilde s j = (𝒮.stageOf s).eTilde (datum T ℜ s) r ℜ.α s j :=
    𝒮.eTilde_eq_stageOf s
  simp only [h]
  refine Finset.sum_congr rfl fun j _ => ?_
  unfold cT
  rw [← coe_idxT r ℜ.α s j]
  exact (aAt_datum_eq_aSeq T ℜ s (idxT ℜ.α s r j)).symm

theorem Frame.thresholdRep_eq_stageOf (𝒮 : Frame hS) (s : ℕ) :
    𝒮.thresholdRep s = (𝒮.stageOf s).thresholdRep (datum T ℜ s) r ℜ.α s ℜ.b ν := by
  unfold Frame.thresholdRep FrameStage.thresholdRep
  rw [𝒮.droppedWeight_eq_stageOf s]

theorem Frame.bTildeRep_eq_stageOf (𝒮 : Frame hS) (s : ℕ) :
    𝒮.bTildeRep s = (𝒮.stageOf s).bTildeRep (datum T ℜ s) r ℜ.α s ℜ.b ν 𝒮.bBar := by
  unfold Frame.bTildeRep FrameStage.bTildeRep
  rw [𝒮.thresholdRep_eq_stageOf s]

theorem Frame.jBarRep_eq_stageOf (𝒮 : Frame hS) (s : ℕ) :
    𝒮.jBarRep s = (𝒮.stageOf s).jBarRep (datum T ℜ s) r ℜ.α s ℜ.b ν 𝒮.bBar := by
  classical
  unfold Frame.jBarRep FrameStage.jBarRep
  rw [𝒮.thresholdRep_eq_stageOf s]
  have h : ∀ j, 𝒮.eTilde s j = (𝒮.stageOf s).eTilde (datum T ℜ s) r ℜ.α s j :=
    𝒮.eTilde_eq_stageOf s
  have hprod : (∏ j, ((𝒮.eTilde s j).emptyIfBot) ^ (cT T ℜ r s j)) =
      ∏ j : Fin (alphaT r ℜ.α s), (((𝒮.stageOf s).eTilde (datum T ℜ s) r ℜ.α s j).emptyIfBot) ^
        ((datum T ℜ s).aAt (idxN r ℜ.α j)) := by
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [h j]
    congr 1
    unfold cT
    rw [← coe_idxT r ℜ.α s j]
    exact (aAt_datum_eq_aSeq T ℜ s (idxT ℜ.α s r j)).symm
  by_cases hd : (𝒮.stageOf s).thresholdRep (datum T ℜ s) r ℜ.α s ℜ.b ν = 0
  · simp only [hd, ↓reduceIte]
    rfl
  · simp only [hd, ↓reduceIte]
    rw [hprod]
    rfl

theorem Frame.aRep_eq_stageOf (𝒮 : Frame hS) (s : ℕ) (a : Fin (alphaT r ℜ.α s) → ℕ) :
    𝒮.aRep s a = (𝒮.stageOf s).aRep (datum T ℜ s) r ℜ.α s a := by
  funext j
  unfold Frame.aRep FrameStage.aRep
  exact if_congr (by rw [𝒮.eTilde_eq_stageOf s j]; exact Iff.rfl) rfl rfl

theorem Frame.datumRep_eq_stageOf (𝒮 : Frame hS) (s : ℕ) (a : Fin (alphaT r ℜ.α s) → ℕ)
    (Jt : Subscheme (𝒮.xTilde s)) :
    𝒮.datumRep s a Jt =
      (𝒮.stageOf s).datumRep (datum T ℜ s) r ℜ.α s ℜ.b ν 𝒮.bBar a Jt := by
  unfold Frame.datumRep FrameStage.datumRep
  rw [𝒮.datumTilde_eq_stageOf, 𝒮.bTildeRep_eq_stageOf s, 𝒮.aRep_eq_stageOf s]
  rfl

end Bridge

end CD

/-! ## 12. The dropped traces are the components `E_j ⊇ F` (closed case)

The weight `δ_s` of the traces equal to `X̃` is at most the weight, at any point of `F`, of the
components `E_i` of the original datum that contain `F`.  (A dropped trace `Ẽ_j = X̃` stays
dropped along the extension and is born at the stage `0`: it is a component `E_j ⊇ F`, never an
exceptional divisor.)  This is what turns `δ_s ≥ b - ν` into the membership of the points of `F`
in `S(ℜ)`, which the non-vanishing of `J̄(s)` for `d_s = 0` needs. -/

namespace CD

variable {X : Scheme.{u}} {N : ℕ} {ℜ : DatumII.Raw X} {r : Restriction X} {ν : ℕ}
  {T : AB.Tower X} {x₀ : X}

namespace Frame

variable {hS : Standing N ℜ r ν T x₀} (𝒮 : Frame hS)

/-- `Ẽ_j = X̃` iff `X̄_s ⊆ Ê_j(s)` as sets (`X̄_s` is reduced). -/
theorem eTilde_eq_bot_iff [Hironaka.HironakaCitedResults.{u}] (s : ℕ) (j : Fin (alphaT r ℜ.α s)) :
    𝒮.eTilde s j = ⊥ ↔ (𝒮.xBar s).pts ⊆ (𝒮.eHat s (idxT ℜ.α s r j)).pts := by
  constructor
  · intro h y hy
    obtain ⟨y', rfl⟩ := Subscheme.exists_ι_eq_of_mem_pts _ hy
    have hy' : y' ∈ (𝒮.eTilde s j).pts := by
      rw [h]; exact Subscheme.mem_pts_bot y'
    exact (Subscheme.mem_pts_totalTransform_subschemeι_iff y').mp hy'
  · exact Subscheme.totalTransform_ι_eq_bot_of_pts_subset (𝒮.isReduced_xBar s)

/-- If `X̄_s` is contained in `B̂_s`, the strict transform `X̄_{s+1}` is empty. -/
theorem xBar_succ_pts_eq_empty_of_subset (s : ℕ) (h : (𝒮.xBar s).pts ⊆ (𝒮.tHat.B s).pts) :
    (𝒮.xBar (s + 1)).pts = ∅ :=
  pts_strictTransform_eq_empty_of_subset (𝒮.tHat.monoidalTransformation s) (𝒮.xBar s) h

/-- **`f̄_s : X̄_{s+1} → X̄_s` is surjective** when `X̄_{s+1}` is non-empty (and `X̄_s`
irreducible):
it is the monoidal transformation of `X̄_s` with a center which is not all of `X̄_s`, hence nowhere
dense. -/
theorem surjective_fBar [Hironaka.HironakaCitedResults.{u}] (s : ℕ) (hne : (𝒮.xBar (s + 1)).pts.Nonempty)
    (hirr : (𝒮.xBar s).IsIrreducible) : Function.Surjective (𝒮.fBar s).base := by
  have hA : IsAlgebraicScheme (𝒮.xTilde s) := by
    have := 𝒮.isAlgebraicScheme_tHat_X s
    exact isAlgebraicScheme_toScheme (𝒮.xBar s)
  have : IsNoetherian (𝒮.xTilde s) := IsAlgebraicScheme.isNoetherian _
  have : IrreducibleSpace (𝒮.xTilde s) := hirr
  have h := 𝒮.isMonoidalTransformationOf_fBar s
  have hne' : (𝒮.bBarOn s).pts ≠ Set.univ := by
    intro hu
    apply hne.ne_empty
    refine 𝒮.xBar_succ_pts_eq_empty_of_subset s fun y hy => ?_
    obtain ⟨y', rfl⟩ := Subscheme.exists_ι_eq_of_mem_pts _ hy
    have : y' ∈ (𝒮.bBarOn s).pts := by rw [hu]; trivial
    exact (Subscheme.mem_pts_totalTransform_subschemeι_iff y').mp this
  have hint : interior (𝒮.bBarOn s).pts = ∅ := by
    by_contra hh
    have hd := (isOpen_interior (s := (𝒮.bBarOn s).pts)).dense (Set.nonempty_iff_ne_empty.mpr hh)
    apply hne'
    refine Set.eq_univ_of_univ_subset ?_
    have := closure_minimal (interior_subset (s := (𝒮.bBarOn s).pts))
      (𝒮.bBarOn s).support.isClosed
    rw [hd.closure_eq] at this
    exact this
  have hnd : IsNowhereDense (𝒮.bBarOn s).pts := by
    unfold IsNowhereDense
    rwa [show closure (𝒮.bBarOn s).pts = (𝒮.bBarOn s).pts from
      (𝒮.bBarOn s).support.isClosed.closure_eq]
  exact (𝒮.tBar s h).surjective_of_isNowhereDense hnd

end Frame

end CD

namespace CD

variable {X : Scheme.{u}} {N : ℕ} {ℜ : DatumII.Raw X} {r : Restriction X} {ν : ℕ}
  {T : AB.Tower X} {x₀ : X}

namespace Frame

variable {hS : Standing N ℜ r ν T x₀} (𝒮 : Frame hS)

/-- The commutation `c_s ∘ f̂_s ∘ ι_{s+1} = f_s ∘ c_{s+1} ∘ ι_{s+1}` on points, in the form used
below: for `y : X̄_{s+1}`, `c_s (ι_s (f̄_s y)) = f_s (c_{s+1} (ι_{s+1} y))`. -/
theorem c_ι_fBar_apply (s : ℕ) (y : (𝒮.xBar (s + 1)).toScheme) :
    (𝒮.c s).base ((𝒮.xBar s).ι.base ((𝒮.fBar s).base y)) =
      (T.f s).base ((𝒮.c (s + 1)).base ((𝒮.xBar (s + 1)).ι.base y)) := by
  have h1 : (𝒮.xBar s).ι.base ((𝒮.fBar s).base y) =
      (𝒮.tHat.f s).base ((𝒮.xBar (s + 1)).ι.base y) :=
    (congrArg (fun φ => φ.base y) (𝒮.fBar_comm s))
  rw [h1]
  exact congrArg (fun φ => φ.base ((𝒮.xBar (s + 1)).ι.base y)) (𝒮.c_comm s)

/-- **A dropped trace stays dropped, backwards**: if `X̄_{s+1} ⊆ Ê_j(s+1)` for a component born
before (`j < α + s`), then `X̄_s ⊆ Ê_j(s)`: `E_j(s+1)` is the strict transform of `E_j(s)`, and
`f̄_s` is surjective. -/
theorem xBar_pts_subset_eHat_of_succ [Hironaka.HironakaCitedResults.{u}] (s : ℕ) (hne : (𝒮.xBar (s + 1)).pts.Nonempty)
    (hirr : (𝒮.xBar s).IsIrreducible) (j : Fin (ℜ.α + s))
    (h : (𝒮.xBar (s + 1)).pts ⊆ (𝒮.eHat (s + 1) ⟨j.val, by omega⟩).pts) :
    (𝒮.xBar s).pts ⊆ (𝒮.eHat s j).pts := by
  intro y hy
  obtain ⟨y0, rfl⟩ := Subscheme.exists_ι_eq_of_mem_pts _ hy
  obtain ⟨y1, rfl⟩ := 𝒮.surjective_fBar s hne hirr y0
  have h1 := h (Subscheme.mem_pts_ι _ y1)
  unfold eHat at h1 ⊢
  rw [Subscheme.pts_totalTransform_eq_preimage] at h1 ⊢
  change (𝒮.c (s + 1)).base ((𝒮.xBar (s + 1)).ι.base y1) ∈
    (eSeq T ℜ (s + 1) ⟨j.val, by omega⟩).pts at h1
  rw [eSeq_succ_of_lt T ℜ s j.val j.2] at h1
  have h2 := MonoidalTransformation.pts_strictTransform_subset (T.monoidalTransformation s) _ h1
  change (𝒮.c s).base ((𝒮.xBar s).ι.base ((𝒮.fBar s).base y1)) ∈ (eSeq T ℜ s j).pts
  rw [𝒮.c_ι_fBar_apply s y1]
  exact h2

/-- **The new exceptional divisor never contains `X̄_{s+1}`**: if `X̄_{s+1} ⊆ Ê_{α+s}(s+1)`, then
`X̄_s ⊆ B̂_s` and the strict transform `X̄_{s+1}` would be empty. -/
theorem not_xBar_pts_subset_eHat_last [Hironaka.HironakaCitedResults.{u}] (s : ℕ) (hne : (𝒮.xBar (s + 1)).pts.Nonempty)
    (hirr : (𝒮.xBar s).IsIrreducible) :
    ¬ (𝒮.xBar (s + 1)).pts ⊆ (𝒮.eHat (s + 1) ⟨ℜ.α + s, by omega⟩).pts := by
  intro h
  apply hne.ne_empty
  refine 𝒮.xBar_succ_pts_eq_empty_of_subset s fun y hy => ?_
  obtain ⟨y0, rfl⟩ := Subscheme.exists_ι_eq_of_mem_pts _ hy
  obtain ⟨y1, rfl⟩ := 𝒮.surjective_fBar s hne hirr y0
  have h1 := h (Subscheme.mem_pts_ι _ y1)
  unfold eHat at h1
  rw [Subscheme.pts_totalTransform_eq_preimage] at h1
  change (𝒮.c (s + 1)).base ((𝒮.xBar (s + 1)).ι.base y1) ∈
    (eSeq T ℜ (s + 1) ⟨ℜ.α + s, by omega⟩).pts at h1
  rw [eSeq_succ_last T ℜ s] at h1
  have h2 : (𝒮.c (s + 1)).base ((𝒮.xBar (s + 1)).ι.base y1) ∈
      (T.monoidalTransformation s).exceptional.pts := h1
  rw [MonoidalTransformation.pts_exceptional] at h2
  rw [𝒮.B_hat s, Subscheme.pts_totalTransform_eq_preimage]
  change (𝒮.c s).base ((𝒮.xBar s).ι.base ((𝒮.fBar s).base y1)) ∈ (T.B s).pts
  rw [𝒮.c_ι_fBar_apply s y1]
  exact h2

end Frame

end CD

namespace CD

variable {X : Scheme.{u}} {N : ℕ} {ℜ : DatumII.Raw X} {r : Restriction X} {ν : ℕ}
  {T : AB.Tower X} {x₀ : X}

namespace Frame

variable {hS : Standing N ℜ r ν T x₀} (𝒮 : Frame hS)

/-- **At the stage `0`, `X̄_0 ⊆ Ê_j(0)` forces `F ⊆ E_j`** (the contrapositive of
`not_subset_modelDatum_E_closed`, which assumes `F ⊄ E_j`): `X̄_0 = V(z)` with `z` generating `F`,
and `Ê_j(0) = c_0⁻¹(E_j)`; the stalk of `E_j` at `x_0` lies in that of `F`, and `F` is
irreducible. -/
theorem pts_subset_eSeq_zero_of_subset_eHat_zero [Hironaka.HironakaCitedResults.{u}] {F : Subscheme X} (hr : r = .closed F)
    (j : Fin (ℜ.α + 0)) (hsubj : (AB.vZ X x₀ 𝒮.z).pts ⊆ (𝒮.eHat 0 j).pts) :
    F.pts ⊆ (eSeq T ℜ 0 j).pts := by
  by_contra hnot
  let xh : 𝒮.tHat.X 0 := hS.xh
  have hle := DatumTransform.stalkIdeal_le_of_pts_subset (X := 𝒮.tHat.X 0) 𝒮.isReduced_vZ
    hsubj xh
  have hv := 𝒮.vZ_eq_totalTransform_c_zero hr
  rw [hv] at hle
  unfold eHat at hle
  have e1 : (Subscheme.totalTransform (𝒮.c 0) (eSeq T ℜ 0 j)).stalkIdeal xh =
      ((eSeq T ℜ 0 j).stalkIdeal ((𝒮.c 0).base xh)).map ((𝒮.c 0).stalkMap xh).hom :=
    stalkIdeal_totalTransform _ _ _
  have e2 : (Subscheme.totalTransform (𝒮.c 0) (F : Subscheme (T.X 0))).stalkIdeal xh =
      ((F : Subscheme (T.X 0)).stalkIdeal ((𝒮.c 0).base xh)).map ((𝒮.c 0).stalkMap xh).hom :=
    stalkIdeal_totalTransform _ _ _
  rw [e1, e2] at hle
  have hcm := 𝒮.toCompletion.comap_map_stalkMap (hS.ambient.2.1 x₀) hS.isNonsingular_X
    hS.isNonsingular_B 0 hS.xh rfl
  have hle' : (eSeq T ℜ 0 j).stalkIdeal ((𝒮.c 0).base hS.xh) ≤
      F.stalkIdeal ((𝒮.c 0).base hS.xh) := by
    exact Ideal.le_comap_map.trans ((Ideal.comap_mono hle).trans (hcm _).le)
  have hFr : F.IsNonsingularIrreducibleCodimOne := by
    have := hS.isFor; subst hr; exact this.1
  have hFx : x₀ ∈ F.pts := hS.mem_pts_closed_x₀ hr
  have hFirr : _root_.IsIrreducible F.pts := by
    rcases hFr with h | ⟨-, h, -⟩
    · rw [h, Subscheme.pts_empty] at hFx; exact hFx.elim
    · exact isIrreducible_pts F h
  exact Subscheme.not_stalkIdeal_le_of_isIrreducible_not_subset hFirr hnot
    (le_rfl : (eSeq T ℜ 0 j).pts ⊆ (eSeq T ℜ 0 j).pts) (by
      rw [𝒮.c_zero_base_xh]; exact hFx) hle'

end Frame

end CD

namespace CD

variable {X : Scheme.{u}} {N : ℕ} {ℜ : DatumII.Raw X} {r : Restriction X} {ν : ℕ}
  {T : AB.Tower X} {x₀ : X}

/-- The exponents `a_i`, `i ≤ α`, do not change along the extension. -/
theorem aSeq_eq_a_of_lt (T : AB.Tower X) (ℜ : DatumII.Raw X) (s i : ℕ) (hi : i < ℜ.α) :
    aSeq T ℜ s ⟨i, by omega⟩ = ℜ.a ⟨i, hi⟩ := by
  induction s with
  | zero => rfl
  | succ s ih =>
    rw [aSeq_succ_of_lt T ℜ s i (by omega)]
    exact ih

namespace Frame

variable {hS : Standing N ℜ r ν T x₀} (𝒮 : Frame hS)

/-- **A trace equal to `X̃` at the stage `t ≤ s` is a component `E_j ⊇ F`, `j ≤ α`** (closed case):
`X̄_t ⊆ Ê_j(t)` is inherited backwards along the extension (`xBar_pts_subset_eHat_of_succ`),
the new exceptional divisors never contain `X̄_{t+1}` (`not_xBar_pts_subset_eHat_last`), and at the
stage `0` this is `pts_subset_eSeq_zero_of_subset_eHat_zero`. -/
theorem lt_and_pts_subset_of_xBar_pts_subset_eHat [Hironaka.HironakaCitedResults.{u}] {F : Subscheme X} (hr : r = .closed F) {s : ℕ}
    (hprep : PrepHyp N ℜ r ν T x₀ s) :
    ∀ t, t ≤ s → ∀ j : Fin (ℜ.α + t), (𝒮.xBar t).pts ⊆ (𝒮.eHat t j).pts →
      ∃ h : j.val < ℜ.α, F.pts ⊆ (ℜ.E ⟨j.val, h⟩).pts := by
  have hadm := 𝒮.isAdmissibleAt_of_prepHyp hprep
  have hirr : ∀ t, t ≤ s → (𝒮.xBar t).IsIrreducible := fun t ht => by
    rcases ht.lt_or_eq with h | rfl
    · exact (hadm.2.2.1 t h).1.2
    · exact hadm.1.2
  intro t
  induction t with
  | zero =>
    intro _ j hj
    exact ⟨j.2, 𝒮.pts_subset_eSeq_zero_of_subset_eHat_zero hr j hj⟩
  | succ t ih =>
    intro ht j hj
    have hne : (𝒮.xBar (t + 1)).pts.Nonempty := pts_nonempty_of_isIrreducible _ (hirr _ ht)
    by_cases hjt : j.val < ℜ.α + t
    · have hj' : (𝒮.xBar (t + 1)).pts ⊆ (𝒮.eHat (t + 1) ⟨(⟨j.val, hjt⟩ : Fin (ℜ.α + t)).val,
          by omega⟩).pts := hj
      exact ih (by omega) ⟨j.val, hjt⟩
        (𝒮.xBar_pts_subset_eHat_of_succ t hne (hirr t (by omega)) ⟨j.val, hjt⟩ hj')
    · exfalso
      have hjeq : j = ⟨ℜ.α + t, by omega⟩ := Fin.ext (by have := j.2; simp only; omega)
      rw [hjeq] at hj
      exact 𝒮.not_xBar_pts_subset_eHat_last t hne (hirr t (by omega)) hj

end Frame

end CD

namespace CD

variable {X : Scheme.{u}} {N : ℕ} {ℜ : DatumII.Raw X} {r : Restriction X} {ν : ℕ}
  {T : AB.Tower X} {x₀ : X}

namespace Frame

variable {hS : Standing N ℜ r ν T x₀} (𝒮 : Frame hS)

open Classical in
/-- **The weight of the dropped traces is at most the weight, at a point of `F`, of the components
`E_i ⊇ F`** (closed case): `δ_s ≤ ∑_{y ∈ E_i} a_i = weight_ℜ(y)` for every `y ∈ F`.  Together with
`b - ν ≤ δ_s` (threshold `0`) this gives `b ≤ weight_ℜ(y) + ν` on `F`, i.e. `F ∩ {ν(J_y) ≥ ν} ⊆
S(ℜ)`, which is the hypothesis `hSmem` of the non-vanishing of `J̄(s)` when `d_s = 0`. -/
theorem droppedWeight_le_weight [Hironaka.HironakaCitedResults.{u}] {F : Subscheme X} (hr : r = .closed F) {s : ℕ}
    (hprep : PrepHyp N ℜ r ν T x₀ s) {y : X} (hy : y ∈ F.pts) :
    𝒮.droppedWeight s ≤ ℜ.weight y := by
  have hdrop := 𝒮.lt_and_pts_subset_of_xBar_pts_subset_eHat hr hprep s le_rfl
  -- the exponent function, extended by `0` beyond `α`
  let g : Fin (ℜ.α + s) → ℕ := fun j => if h : j.val < ℜ.α then ℜ.a ⟨j.val, h⟩ else 0
  let P : Fin (ℜ.α + s) → Prop := fun j => ∃ h : j.val < ℜ.α, y ∈ (ℜ.E ⟨j.val, h⟩).pts
  subst hr
  unfold droppedWeight
  rw [Finset.sum_filter]
  calc (∑ j : Fin (alphaT (Restriction.closed F) ℜ.α s),
        if 𝒮.eTilde s j = ⊥ then cT T ℜ (Restriction.closed F) s j else 0)
      ≤ ∑ j : Fin (ℜ.α + s), if P j then g j else 0 := by
        refine Finset.sum_le_sum fun j _ => ?_
        by_cases hj : 𝒮.eTilde s j = ⊥
        · obtain ⟨hlt, hsub⟩ := hdrop j ((𝒮.eTilde_eq_bot_iff s j).mp hj)
          have hP : P j := ⟨hlt, hsub hy⟩
          have hc : cT T ℜ (Restriction.closed F) s j = g j := by
            unfold cT
            change aSeq T ℜ s j = _
            simp only [g, hlt, ↓reduceDIte]
            exact aSeq_eq_a_of_lt T ℜ s j.val hlt
          simp only [hj, hP, hc, ↓reduceIte, le_refl]
        · simp only [hj, ↓reduceIte, zero_le]
    _ = ℜ.weight y := by
        rw [Fin.sum_univ_add]
        have h2 : ∑ k : Fin s, (if P (Fin.natAdd ℜ.α k) then g (Fin.natAdd ℜ.α k) else 0) = 0 := by
          refine Finset.sum_eq_zero fun k _ => ?_
          have : ¬ P (Fin.natAdd ℜ.α k) := fun ⟨h, _⟩ => by
            simp only [Fin.val_natAdd] at h; omega
          simp only [this, ↓reduceIte]
        rw [h2, add_zero]
        unfold DatumII.Raw.weight
        rw [Finset.sum_filter]
        refine Finset.sum_congr rfl fun i _ => ?_
        have hv : (Fin.castAdd s i).val < ℜ.α := i.2
        by_cases hi : y ∈ (ℜ.E i).pts
        · have hP : P (Fin.castAdd s i) := ⟨hv, hi⟩
          simp only [hP, hi, ↓reduceIte, g, hv, ↓reduceDIte]
          rfl
        · have hP : ¬ P (Fin.castAdd s i) := fun ⟨_, h⟩ => hi h
          simp only [hP, hi, ↓reduceIte]

end Frame

end CD

namespace CD

variable {X : Scheme.{u}} {N : ℕ} {ℜ : DatumII.Raw X} {r : Restriction X} {ν : ℕ}
  {T : AB.Tower X} {x₀ : X}

/-- A restriction which is not closed is the trivial one. -/
theorem Restriction.eq_unrestricted_of_forall_ne_closed (r : Restriction X)
    (h : ∀ F, r ≠ .closed F) : r = .unrestricted := by
  cases r with
  | closed F => exact absurd rfl (h F)
  | unrestricted => rfl

namespace Frame

variable {hS : Standing N ℜ r ν T x₀} (𝒮 : Frame hS)

open Classical in
/-- **Threshold `0` puts the points of `F` with `ν(J_y) ≥ ν` into `S(ℜ)`**: if `d_s = 0`, i.e. `b ≤
ν + δ_s`, then every point `y` of `F` (all points, without restriction) with `ν(J_y) ≥ ν` satisfies
`b ≤ weight_ℜ(y) + ν(J_y)`.  This is the hypothesis `hSmem` of the non-vanishing of `J̄(s)` (the
point of the argument being the generic point of `F`: its weight is that of the components
`E_i ⊇ F`, `droppedWeight_le_weight`). -/
theorem mem_S_of_thresholdRep_eq_zero [Hironaka.HironakaCitedResults.{u}] {s : ℕ} (hprep : PrepHyp N ℜ r ν T x₀ s)
    (hd : 𝒮.thresholdRep s = 0) {y : X} (hν : (ν : ℕ∞) ≤ ℜ.nuAt y)
    (hF : ∀ F, r = .closed F → y ∈ F.pts) : y ∈ ℜ.S := by
  have hδ : ℜ.b ≤ ν + 𝒮.droppedWeight s := by
    unfold thresholdRep at hd; omega
  have hw : 𝒮.droppedWeight s ≤ ℜ.weight y := by
    by_cases hc : ∃ F, r = .closed F
    · obtain ⟨F, hr⟩ := hc
      exact 𝒮.droppedWeight_le_weight hr hprep (hF F hr)
    · push Not at hc
      rw [𝒮.droppedWeight_eq_zero_of_unrestricted hprep
        (Restriction.eq_unrestricted_of_forall_ne_closed r hc)]
      exact Nat.zero_le _
  show (ℜ.b : ℕ∞) ≤ (ℜ.weight y : ℕ∞) + ℜ.nuAt y
  calc (ℜ.b : ℕ∞) ≤ ((ℜ.weight y : ℕ) : ℕ∞) + (ν : ℕ∞) := by
        exact_mod_cast (show ℜ.b ≤ ℜ.weight y + ν by omega)
    _ ≤ ((ℜ.weight y : ℕ) : ℕ∞) + ℜ.nuAt y := add_le_add le_rfl hν

end Frame

end CD

end Hironaka
