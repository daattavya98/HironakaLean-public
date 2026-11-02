/-
Copyright (c) 2026 Daattavya Aggarwal, Minhyong Kim, Oisin Kim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daattavya Aggarwal, Minhyong Kim, Oisin Kim
-/
module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Architect
public import Hironaka.Compat.MainISystem
public import Hironaka.Ch4.MainIAmbientDatum
public import Hironaka.Ch4.MainIAmbientElim
public import Hironaka.Ch4.Conclusion
public import Hironaka.Ch4.Preparation
public import Hironaka.Ch3.Stability
public import Hironaka.Compat.BlowupBaseChange
public import Hironaka.Statements

/-!
# Main Theorem I(n), pp. 172–174: the result for a non-singular irreducible ambient scheme

> Let `X` be a non-singular irreducible algebraic scheme of dimension `N`.  Let `V_i` (`1 ≤ i ≤ β`) be a finite number
> of subschemes of `X`, `β ≥ 0`, and `W` a reduced subscheme of `X` of dimension `n` such that `W ⊆ ⋂ V_i`.  Then, by
> taking the empty subscheme of `X` as `E`, … we obtain a resolution datum `(E; V_1, …, V_β; W)` of type `ℜ_I^{N,n}` on `X`.  Let us denote this datum by
> `ℜ_I^{N,n}`. … Thus we get a
> resolution datum `(ℜ_I^{N,n}, U)` of type `ℜ_I^{N,n}` with open restriction `U` on `X`.  By the fundamental theorem
> `I₂^{N,n}`, we have a finite succession of monoidal transformations `f : X′ → X`, which is permissible for
> `(ℜ_I^{N,n}, U)`, such that `f*(ℜ_I^{N,n})` is resolved everywhere. … (pp. 172–173)

Contents.  The ambient result `MainTheorem.IAmbient N n` (Compat/MainISystem) for `n < N`:
* A1/A2: the datum with `E = ∅` and its open restriction `U` (simple points open and dense: class 𝔅 (iii) and
  reducedness; normally flat points open dense: Cor. of Th. 1);
* A3: the fundamental theorem `I₂^{N,n}` (`allFundamentalTheorems_fundamentalFamily`);
* A4: the facts (1), (2), (3) from permissibility and resolvedness;
* A5: the dichotomy (Cor. 4 of Prop. 1, Cor. of Th. 3), the elimination of the centers outside `S(i)` (the new succession
  `{f̄_i}` with `g_i` and (a), (b), (c), "constructed without any difficulty"), the invariant "`g_i` is an isomorphism
  over an open set `N_i ⊇ S̄(i)`, `S(i) ⊆ g_i⁻¹(N_i)`";
* A6: assembly.
The case `n = N` (`W = X`) is not covered by the fundamental theorems (range `N > n`) and is avoided in Part B by the
choice of the embedding dimension (p. 172 does not exclude it, whereas Remark 1, p. 169, excludes `X = W`).

The elimination is in a further file (`Ch4/MainIAmbientElim.lean`).
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace Hironaka

universe u

/-! A1/A2 (the datum with `E = ∅` and its open restriction `U`) are in `Hironaka.Ch4.MainIAmbientDatum`. -/

section Dichotomy

variable {X : Scheme.{u}} [IsAlgebraicScheme X] {β : ℕ}

/-- p. 173: "(1′) … `B_i` is a non-singular irreducible subscheme of `W(i)` which is contained in `S(i)`. … In fact, by
Corollary 4 of Proposition 1, (§ 1, Ch. II), `B_i` of (1) is either contained in the singular locus of `W(i)` or in its
complement in `W(i)`.  Moreover, by Corollary of Theorem 3, (§ 3, Ch. II), for each `j`, `V_j(i)` is normally flat along
`W(i)` either at all the points of `B_i` or at no points of `B_i`.  Thus, `B_i` is either contained in `S(i)` or in the
complement of `S(i)` in `W(i)`."

Precise form: the Corollary of Theorem 3 needs a simple point of `W` in `B_i` at which `V_j` is normally flat along `W`;
if `B_i` meets the singular locus, then `B_i ⊆ S(i)` already (the printed sentence is imprecise). -/
theorem Subscheme.subset_mainUnresolved_or_disjoint [Hironaka.HironakaCitedResults.{u}] (V : Fin (β + 1) → Subscheme X) (W D : Subscheme X)
    (hWV : ∀ j, W.IsContainedIn (V j)) (hDW : D.IsContainedIn W) (hD : D.IsNonsingular)
    (hirr : D.IsIrreducible) (hVD : ∀ x ∈ D.pts, ∀ j, Subscheme.IsNormallyFlatAlongAt' (V j) D x)
    (hWD : ∀ x ∈ D.pts, Subscheme.IsNormallyFlatAlongAt' W D x) :
    D.pts ⊆ Subscheme.mainUnresolved V W ∨ Disjoint D.pts (Subscheme.mainUnresolved V W) := by
  by_cases h : ∃ x ∈ D.pts, Subscheme.IsMainResolvedAt V W x
  · right
    obtain ⟨x, hx, hxr⟩ := h
    -- "by Corollary 4 of Proposition 1 … and by Corollary of Theorem 3 …", once for each `j`
    have key : ∀ k, ∀ y ∈ D.pts, W.IsSimpleAt y ∧ Subscheme.IsNormallyFlatAlongAt' (V k) W y :=
      fun k => Subscheme.isSimpleAt_and_isNormallyFlatAlongAt'_of_chain (V k) W D (hWV k) hDW hD
        hirr (fun y hy => hVD y hy k) hWD ⟨x, hx, hxr.1, hxr.2 k⟩
    exact Set.disjoint_left.mpr fun y hy hyS =>
      hyS.2 ⟨(key 0 y hy).1, fun k => (key k y hy).2⟩
  · left
    intro y hy
    exact ⟨pts_subset_of_isContainedIn hDW hy, fun hres => h ⟨y, hy, hres⟩⟩

end Dichotomy

section Facts

/-- `V_0(i+1)` is the strict transform of `V_0(i)`: the strict transform of the whole scheme is the whole
scheme (`V_0 = V₀` is the scheme itself), so the system `(V_0, V_1, …, V_β)` is transformed termwise. -/
theorem mainSystem_strictTransform {X : Scheme.{u}} {B : Subscheme X} (t : MonoidalTransformation X B)
    {β : ℕ} (V : Fin β → Subscheme X) :
    (fun j => Subscheme.strictTransform t (mainSystem V j)) =
      mainSystem (fun k => Subscheme.strictTransform t (V k)) := by
  funext j
  refine Fin.cases ?_ (fun k => ?_) j
  · simp [mainSystem, MonoidalTransformation.strictTransform_bot]
  · simp [mainSystem]

/-- p. 173: "According to the fundamental theorem `I₂^{N,n}`, we have the following facts: (1) `B_i` is a non-singular
irreducible subscheme of `W(i)` which is nowhere dense; (2) all the `V_j(i)` and `W(i)` are normally flat along the
subscheme `B_i`; and (3) `W(r)` is a non-singular subscheme of `V_j(r)` …, and all the `V_j(r)` are normally flat
along `W(r)`", together with (1′) (the dichotomy), for a succession permissible for `(ℜ, U)` with `f*(ℜ)` resolved
everywhere.  (1), (2) come from permissibility (`ℜ.IsPermissible B`: `(E; V_1, …, V_β, W; B)` is a resolution datum
resolved everywhere, with `B ⊆ W`), nowhere density from the open restriction
(`DatumI.Raw.pts_subset_closure_diff_of_isPermissibleOpen`), (3) from resolvedness at the end; the index
`j = 0` (`V_0 = X` non-singular) is `Subscheme.isNormallyFlatAlongAt'_bot_of_isSimpleAt`. -/
theorem MonoidalSuccession.isMainPre_of_isPermissibleIOpen [Hironaka.HironakaCitedResults.{u}] {N n : ℕ} :
    ∀ {X Y : Scheme.{u}} (s : MonoidalSuccession X Y) {ℜ : DatumI.Raw X} {U : Set X},
      IsGoodDatumI N n X ℜ → ℜ.IsOpenRestriction U → s.IsPermissibleIOpen ℜ U →
      (s.transformI ℜ).ResolvedEverywhere →
      s.IsMainPre (mainSystem fun j => ℜ.V j) ℜ.W := by
  intro X Y s
  induction s with
  | nil X =>
    intro ℜ U h hU hs hres
    obtain ⟨⟨hXalg, hXns, -, -⟩, -⟩ := h
    refine Set.eq_empty_of_forall_notMem fun x ⟨hx, hn⟩ => hn ?_
    exact DatumI.Raw.isMainResolvedAt_of_resolvedAt hXns ℜ (hres x hx)
  | cons B t rest ih =>
    intro ℜ U h hU hs hres
    obtain ⟨h', hU'⟩ := IsGoodDatumI.transform_open h hU hs.1 t
    have ih' := ih h' hU' hs.2 hres
    obtain ⟨⟨hXalg, hXns, hXirr, -⟩, hℜ, -⟩ := h
    have hBc : B.IsCenter := hs.1.1.1
    have hBW : B.IsContainedIn ℜ.W := DatumI.Raw.IsPermissible.isContainedIn_W hs.1.1
    have hdense := DatumI.Raw.pts_subset_closure_diff_of_isPermissibleOpen hU hs.1
    have hWV : ∀ j, ℜ.W.IsContainedIn (mainSystem (fun k => ℜ.V k) j) :=
      mainSystem_isContainedIn (fun k => ℜ.V k) ℜ.W hℜ.2.2.2.2
    have hNF : ∀ x ∈ B.pts,
        (∀ j, Subscheme.IsNormallyFlatAlongAt' (mainSystem (fun k => ℜ.V k) j) B x) ∧
          Subscheme.IsNormallyFlatAlongAt' ℜ.W B x := by
      intro x hx
      obtain ⟨hsimple, hnf, -⟩ := hs.1.1.2.2 x hx
      refine ⟨fun j => ?_, ?_⟩
      · refine Fin.cases ?_ (fun k => ?_) j
        · exact Subscheme.isNormallyFlatAlongAt'_bot_of_isSimpleAt (hXns x) hsimple
        · simpa [mainSystem, DatumI.Raw.extendBy] using hnf (Fin.castSucc k)
      · simpa [DatumI.Raw.extendBy] using hnf (Fin.last _)
    -- (1′): "Thus, `B_i` is either contained in `S(i)` or in the complement of `S(i)` in `W(i)`"
    have hdich : B.pts ⊆ Subscheme.mainUnresolved (mainSystem fun k => ℜ.V k) ℜ.W ∨
        Disjoint B.pts (Subscheme.mainUnresolved (mainSystem fun k => ℜ.V k) ℜ.W) := by
      rcases hBc with hB0 | ⟨hns, hirr⟩
      · left
        rw [hB0, Subscheme.pts_empty]
        exact Set.empty_subset _
      · exact Subscheme.subset_mainUnresolved_or_disjoint _ ℜ.W B hWV hBW hns hirr
          (fun x hx => (hNF x hx).1) (fun x hx => (hNF x hx).2)
    refine ⟨⟨hXalg, hXns, hXirr⟩, ⟨hBc, hBW⟩, hdense, hNF, hdich, ?_⟩
    rw [mainSystem_strictTransform t (fun k => ℜ.V k)]
    exact ih'

end Facts

section Elimination

/-- p. 173–174, the elimination of the monoidal transformations with `B_i` not contained in `S(i)`: "we construct a new
succession of monoidal transformations `{f̄_i : X̄(i+1) → X̄(i)}` … such that there exists a morphism `g_i : X(i) → X̄(i)`
for every `i` having the following properties: (a) the center `B̄_i` of `f̄_i` is either the image of `B_i` or the empty
subscheme of `X̄(i)`; (b) … `B̄_i`, `W̄(i)` and `V̄_j(i)` for all `j` have the properties (1′), (2) and (3); and finally
(c) … there exists an open neighborhood of `S̄(i)` in `X̄(i)` in which `g_i⁻¹` exists as a morphism.  The new succession
may be constructed without any difficulty."

The construction is `MonoidalSuccession.exists_isMain123_and_mainUnresolvedAt_eq_empty`
(`Hironaka/Ch4/MainIAmbientElim.lean`), started from the trivial correspondence `X̄(0) = X` (`g_0` the identity); here
it is applied to the facts of `MonoidalSuccession.isMainPre_of_isPermissibleIOpen`.  Since `S(r) = ∅` and `g_r` is
an isomorphism over a neighborhood of `S̄(r)` containing it, `S̄(r) = ∅`, i.e. (4) holds (p. 174: "(4) holds iff `S(r)`
is empty").

Note on the hypotheses: the hypothesis `E = ∅` (`hE`) is not used (the facts hold for any good
datum) and is replaced by the bound `dim W ≤ n` of `IsGoodDatumI`. -/
@[blueprint "lem:I.3-elimination"
  (statement := /-- Let $X$ be a non-singular irreducible algebraic scheme, $\mathfrak R=(E;V_1,\dots,V_\beta;W)$ a
    datum of type $\mathfrak R^{N,n}_{\mathrm I}$ and $U$ an open restriction for it. If $s$ is a succession of monoidal
    transformations permissible for $(\mathfrak R,U)$ such that $s^*(\mathfrak R)$ is resolved everywhere, then there is a
    succession $\bar s$ of $X$ satisfying (1), (2), (3) for all $i$ and (4) of Main Theorem I($n$), obtained from $s$ by
    replacing the monoidal transformations whose centers are not contained in $S(i)$ by transformations with empty
    centers (properties (a), (b), (c) of p.~174). -/)
  (latexEnv := "lemma")]
theorem exists_isMainI_of_isPermissibleIOpen [Hironaka.HironakaCitedResults.{u}] {N n : ℕ} {X Y : Scheme.{u}} (hX : IsAmbient X N)
    (ℜ : DatumI X) (U : Set X) (hU : (ℜ : DatumI.Raw X).IsOpenRestriction U)
    (hn : (ℜ : DatumI.Raw X).W.dim ≤ (n : WithBot ℕ∞))
    (s : MonoidalSuccession X Y) (hs : s.IsPermissibleIOpen ℜ U)
    (hres : (s.transformI ℜ).ResolvedEverywhere) :
    ∃ (Y' : Scheme.{u}) (s' : MonoidalSuccession X Y'),
      s'.IsMainI (mainSystem (fun j => (ℜ : DatumI.Raw X).V j)) (ℜ : DatumI.Raw X).W := by
  have := hX.1
  have hpre := MonoidalSuccession.isMainPre_of_isPermissibleIOpen s
    (show IsGoodDatumI N n X ℜ from ⟨hX, ℜ.2, hn⟩) hU hs hres
  have hWV : ∀ j, (ℜ : DatumI.Raw X).W.IsContainedIn (mainSystem (fun k => (ℜ : DatumI.Raw X).V k) j) :=
    mainSystem_isContainedIn (fun k => (ℜ : DatumI.Raw X).V k) _ ℜ.2.2.2.2.2
  obtain ⟨Yb, sb, h123, hS⟩ := MonoidalSuccession.exists_isMain123_and_mainUnresolvedAt_eq_empty s
    (mainSystem fun k => (ℜ : DatumI.Raw X).V k) (ℜ : DatumI.Raw X).W
    (mainSystem fun k => (ℜ : DatumI.Raw X).V k) (ℜ : DatumI.Raw X).W hpre hWV hWV
    ⟨X, 𝟙 X, 𝟙 X, inferInstance, inferInstance, inferInstance, inferInstance, rfl, fun _ => rfl,
      fun x _ => ⟨x, rfl⟩, fun x _ => ⟨x, rfl⟩⟩
  exact ⟨Yb, sb, h123, (MonoidalSuccession.isMain4_iff_mainUnresolvedAt_eq_empty sb _ _).mpr hS⟩

end Elimination

namespace MainTheorem

/-- **The ambient result of pp. 172–174** ("the previous result", p. 175): Main Theorem I(n) for a non-singular
irreducible algebraic scheme of dimension `N > n`. -/
@[blueprint "thm:I.3-main-I-ambient"
  (statement := /-- Let $X$ be a non-singular irreducible algebraic scheme of dimension $N$, $V_j$ ($1\le j\le\beta$)
    subschemes and $W$ a reduced subscheme of dimension $n<N$ contained in $\bigcap V_j$. Then there is a finite
    succession of monoidal transformations of $X$ with centers $B_i$ such that (1) $B_i$ is a non-singular irreducible
    subscheme of $W(i)$; (2) $B_i$ contains no simple point of $W(i)$ at which all $V_j(i)$ ($0\le j\le\beta$) are
    normally flat along $W(i)$; (3) all $V_j(i)$ and $W(i)$ are normally flat along $B_i$; (4) $W(r)$ is non-singular and
    all $V_j(r)$ are normally flat along $W(r)$. (pp.~172--174.) -/)
  (proof := /-- $\mathfrak R=(\emptyset;V;W)$ is a resolution datum; the set $U$ of resolved points is open and dense in
    $W$ (simple points are open and dense, normally flat points are open and dense). By the fundamental theorem
    $\mathrm I_2^{N,n}$ there is a succession permissible for $(\mathfrak R,U)$ with $f^*\mathfrak R$ resolved everywhere. It
    satisfies the facts (1), (2), (3) of p.~173; by Cor.~4 of Prop.~1 and the Cor.\ of Th.~3, each $B_i$ is contained in
    $S(i)$ or disjoint from it, and the monoidal transformations with $B_i$ disjoint from $S(i)$ are eliminated. -/)
  (latexEnv := "theorem")]
theorem IAmbient_of_lt [Hironaka.HironakaCitedResults.{u}] {N n : ℕ} (h : n < N) : MainTheorem.IAmbient.{u} N n := by
  intro X hX β V W hW hWdim hWV
  have := hX.1
  -- "by taking the empty subscheme of `X` as `E` … we obtain a resolution datum"
  have hdat := DatumI.Raw.isDatum_ofEmpty hX.2.1 V W hW hWV
  -- "`U` is an open dense subset of `W`"
  obtain ⟨U, hU, -⟩ := DatumI.Raw.exists_isOpenRestriction_ofEmpty hX.2.1 V W hW hWV
  -- "By the fundamental theorem `I₂^{N,n}`, we have a finite succession of monoidal transformations …"
  obtain ⟨hI, -⟩ := allFundamentalTheorems_fundamentalFamily.{u}
  obtain ⟨Y, s, hs, hres⟩ := (hI N n h).2 X hX ⟨DatumI.Raw.ofEmpty V W, hdat⟩ U hU hWdim
  exact exists_isMainI_of_isPermissibleIOpen hX ⟨DatumI.Raw.ofEmpty V W, hdat⟩ U hU (le_of_eq hWdim) s hs hres

end MainTheorem

end Hironaka
