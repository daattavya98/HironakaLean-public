/-
Copyright (c) 2026 Daattavya Aggarwal, Minhyong Kim, Oisin Kim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daattavya Aggarwal, Minhyong Kim, Oisin Kim
-/
module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Architect
public import Hironaka.Compat.MainISystem
public import Hironaka.Ch4.ImplicationsAB
public import Hironaka.Statements

/-!
# Main Theorem I(n), the ambient case (Ch. I §3, p. 172): the datum with `E = ∅` and its open restriction

> … let `X` be a non-singular irreducible algebraic scheme of dimension `N`
> ... By taking the empty subscheme of `X` as `E`, … we obtain a resolution datum `(E; V_1, …, V_β; W)` of type `ℜ_I^{N,n}` on `X`.  Let `U` be the set of those
> points of `W` at which this datum is resolved.  Then we can prove that `U` [is] an open dense subset of `W`.  This is
> done by showing first that the set of simple points of a reduced algebraic scheme is open and dense (cf. the property
> (iii) of the class 𝔅 ...); and secondly that, if `V` is an algebraic scheme and `W` a reduced subscheme of `V`, the set
> of those points of `W` at which `V` is normally flat along `W` is an open dense subset of `W` …
> (p. 172; the paper prints "in", a typo for "is")

This file carries out the part of the argument of p. 172 which precedes the application of the fundamental theorem
`I₂^{N,n}` (that part is `Hironaka/Ch4/MainIAmbient.lean`):

* `DatumI.Raw.ofEmpty`, `DatumI.Raw.isDatum_ofEmpty`: the datum `(∅; V_1, …, V_β; W)`;
* `DatumI.Raw.resolvedAt_ofEmpty_iff`: for `E = ∅` the datum is resolved at `x` iff `x` is a simple point of `W` at which
  all `V_j`, `0 ≤ j ≤ β`, are normally flat along `W` (`V_0 = X`, which is normally flat along any subscheme simple at a
  point where `X` is regular, `Subscheme.isNormallyFlatAlongAt'_bot_of_isSimpleAt`);
* `DatumI.Raw.exists_isOpenRestriction_ofEmpty`: the set `U` of resolved points is an open dense subset of `W`.

Formalization note (the route of the density/openness): the printed proof shows that the simple points of `W` and, for each
`V_j`, the points of `W` at which `V_j` is normally flat along `W`, form open dense subsets of `W` and takes the
intersection.  In Lean the openness (that the unresolved set `S` is closed in `X`) is
`Subscheme.isClosed_mainUnresolved` of `Compat/MainISystem.lean`, which combines the same two open sets
(`Subscheme.exists_isOpen_isSimpleAt`, class 𝔅 (iii); `Subscheme.exists_isOpen_isNormallyFlatAlongAt'`, Cor. of Th. 1), and
the density is `Subscheme.pts_subset_closure_diff_mainUnresolved`: every point of a reduced `W` has a generization (the
generic point of an irreducible component of `W` through it) at which `W` is simple and all `V_j` are normally flat along
`W` (the ideal of `W` there is the maximal ideal), the "it is easy to see that `U` contains all the generic points of `W`"
of p. 189.

Deviation from the paper (statement modified, minimal): the datum `(∅; V; W)` is a resolution datum only if `X` is
non-singular (`∅` has normal crossings at `x` only if `O_{X,x}` is a regular local ring: the paper's `X` is non-singular
throughout); so `isDatum_ofEmpty` has the hypothesis `X.IsNonsingular`, and `resolvedAt_ofEmpty_iff` the hypothesis that
`X` is algebraic (used for the normal flatness of `V_0 = X` along a simple `W`).
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace Hironaka

universe u

section Datum

variable {X : Scheme.{u}} {β : ℕ}

/-- `X` is simple at `x` iff the subscheme `⊥ = X` is (`⊥` is the zero ideal sheaf, `X` itself). -/
theorem Subscheme.isSimpleAt_bot_of_isSimpleAt {x : X} (hX : X.IsSimpleAt x) :
    (⊥ : Subscheme X).IsSimpleAt x := by
  have : IsRegularLocalRing (X.presheaf.stalk x) := hX
  refine ⟨Subscheme.mem_pts_iff_stalkIdeal_ne_top.mpr ?_, ?_⟩
  · rw [Subscheme.stalkIdeal_bot_eq]
    exact bot_ne_top
  · rw [Subscheme.stalkIdeal_bot_eq]
    exact IsRegularLocalRing.of_ringEquiv (RingEquiv.quotientBot (X.presheaf.stalk x)).symm

/-- `V_0 = X` is normally flat along a subscheme `D` at a point `x` where `X` is regular and `D` is simple: a regular local
ring is normally flat along a prime with regular quotient (`isNormallyFlatAlongAt'_of_isSimpleAt` for `V = ⊥`).  Used for
the term `j = 0` of the conditions "all `V_j`, `0 ≤ j ≤ β`" of p. 173. -/
theorem Subscheme.isNormallyFlatAlongAt'_bot_of_isSimpleAt [IsAlgebraicScheme X] {D : Subscheme X}
    {x : X} (hX : X.IsSimpleAt x) (hD : D.IsSimpleAt x) :
    Subscheme.IsNormallyFlatAlongAt' (⊥ : Subscheme X) D x :=
  Subscheme.isNormallyFlatAlongAt'_of_isSimpleAt (fun _ => bot_le)
    (Subscheme.isSimpleAt_bot_of_isSimpleAt hX) hD

/-- A datum `ℜ` of type I resolved at `x` (for any `E`) has `W` simple at `x` with all `V_j`, `0 ≤ j ≤ β`, normally flat
along `W` at `x` (`V_0 = X`: `Subscheme.isNormallyFlatAlongAt'_bot_of_isSimpleAt`); the forward direction of "resolved
at `x`" versus the condition of p. 173. -/
theorem DatumI.Raw.isMainResolvedAt_of_resolvedAt [IsAlgebraicScheme X] (hX : X.IsNonsingular)
    (ℜ : DatumI.Raw X) {x : X} (h : ℜ.ResolvedAt x) :
    Subscheme.IsMainResolvedAt (mainSystem (fun j => ℜ.V j)) ℜ.W x := by
  refine ⟨h.1, fun j => ?_⟩
  refine Fin.cases ?_ (fun i => ?_) j
  · simpa [mainSystem] using Subscheme.isNormallyFlatAlongAt'_bot_of_isSimpleAt (hX x) h.1
  · simpa [mainSystem] using h.2.1 i

/-- p. 172: "by taking the empty subscheme of `X` as `E` … we obtain a resolution datum `(E; V_1, …, V_β; W)`". -/
def DatumI.Raw.ofEmpty (V : Fin β → Subscheme X) (W : Subscheme X) : DatumI.Raw X :=
  ⟨Subscheme.empty, β, V, W⟩

/-- The datum with `E = ∅` is a resolution datum on a non-singular scheme: `∅` is reduced, everywhere of codimension one
(vacuously) and has only normal crossings (at a point where `X` is regular, `∅` has normal crossings with `X`). -/
theorem DatumI.Raw.isDatum_ofEmpty (hX : X.IsNonsingular) (V : Fin β → Subscheme X) (W : Subscheme X)
    (hW : W.IsReduced) (hWV : ∀ j, W.IsContainedIn (V j)) : (DatumI.Raw.ofEmpty V W).IsDatum := by
  refine ⟨Subscheme.isReduced_empty, fun x hx => ?_, fun x => ?_, hW, hWV⟩
  · change x ∈ (Subscheme.empty : Subscheme X).pts at hx
    rw [Subscheme.pts_empty] at hx
    exact hx.elim
  · exact Subscheme.hasOnlyNormalCrossingsWithAt_empty (hX x)
      (Subscheme.isSimpleAt_bot_of_isSimpleAt (hX x))

/-- For `X` non-singular, `ℜ_I^{N,n} = (∅; V; W)` is resolved at `x` iff `x` is a simple point of `W` at which all `V_j`
(`1 ≤ j ≤ β`, and `V_0 = X`) are normally flat along `W` (`E = ∅` has normal crossings with `W` at a simple point of
`W`; `X` is normally flat along a regular quotient). -/
theorem DatumI.Raw.resolvedAt_ofEmpty_iff [IsAlgebraicScheme X] (hX : X.IsNonsingular)
    (V : Fin β → Subscheme X) (W : Subscheme X) (x : X) :
    (DatumI.Raw.ofEmpty V W).ResolvedAt x ↔ Subscheme.IsMainResolvedAt (mainSystem V) W x := by
  constructor
  · exact fun h => DatumI.Raw.isMainResolvedAt_of_resolvedAt hX (DatumI.Raw.ofEmpty V W) h
  · rintro ⟨hs, hnf⟩
    refine ⟨hs, fun j => ?_, Subscheme.hasOnlyNormalCrossingsWithAt_empty (hX x) hs⟩
    have := hnf j.succ
    simp only [mainSystem] at this
    exact this

/-- p. 172: "Then we can prove that `U` [is] an open dense subset of `W`", `U` the points of `W` at which `ℜ_I^{N,n}` is
resolved: `(ℜ, U)` is a datum with open restriction `U`.  The route is explained in the header of this file. -/
theorem DatumI.Raw.exists_isOpenRestriction_ofEmpty [Hironaka.HironakaCitedResults.{u}] [IsAlgebraicScheme X] (hX : X.IsNonsingular)
    (V : Fin β → Subscheme X) (W : Subscheme X) (hW : W.IsReduced)
    (hWV : ∀ j, W.IsContainedIn (V j)) :
    ∃ U : Set X, (DatumI.Raw.ofEmpty V W).IsOpenRestriction U ∧
      ∀ x ∈ W.pts, x ∈ U ↔ (DatumI.Raw.ofEmpty V W).ResolvedAt x := by
  have hWV' := mainSystem_isContainedIn V W hWV
  have hiff : ∀ x ∈ W.pts, x ∈ W.pts \ Subscheme.mainUnresolved (mainSystem V) W ↔
      (DatumI.Raw.ofEmpty V W).ResolvedAt x := fun x hx => by
    rw [DatumI.Raw.resolvedAt_ofEmpty_iff hX V W x]
    simp only [Set.mem_sdiff, Subscheme.mainUnresolved, Set.mem_ofPred_eq, not_and, not_not]
    exact ⟨fun h => h.2 hx, fun h => ⟨hx, fun _ => h⟩⟩
  refine ⟨W.pts \ Subscheme.mainUnresolved (mainSystem V) W,
    ⟨⟨(Subscheme.mainUnresolved (mainSystem V) W)ᶜ,
      (Subscheme.isClosed_mainUnresolved (mainSystem V) W hWV').isOpen_compl, ?_⟩,
      Subscheme.pts_subset_closure_diff_mainUnresolved (mainSystem V) W hW hWV',
      fun x hx => (hiff x hx.1).mp hx⟩, hiff⟩
  rw [Set.sdiff_eq, Set.inter_comm]
  rfl

end Datum

end Hironaka
