/-
Copyright (c) 2026 Daattavya Aggarwal, Minhyong Kim, Oisin Kim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daattavya Aggarwal, Minhyong Kim, Oisin Kim
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Architect
public import Hironaka.Ch4.Preparation
public import Hironaka.Compat.NormalCrossingsPullback
public import Hironaka.Compat.NormalCrossingsDescent
public import Hironaka.Compat.ResolvableData
public import Hironaka.Compat.StableOrder
public import Hironaka.Ch3.StabilityCor3c
public import Hironaka.Statements

/-!
# Exceptional divisors are transversal to the strict transform of a non-singular subscheme

> We see that `Ê_{α+1}(s) ∪ ⋯ ∪ Ê_{α+s}(s)` has only normal crossings with `X̃` in `X̂_s`. (p. 321)
> It is clear that `Ê'_{α+1}(s) ∪ ⋯ ∪ Ê'_{α+s}(s)` has only normal crossings with `X̄'_s` on `X̂'_s`. (p. 308)

General form: a type I datum `ℜ = (E; V; W)` on an ambient scheme, resolved along the irreducible
`W` (non-singular, `E` with only normal crossings with `W`), and a succession `s` whose centers
`B_t` are non-singular irreducible, `B_t ⊆ W_t`, `W_t ⊄ B_t`, with `E_t` having only normal crossings
with `B_t`. Then (`isNonsingular_and_hasOnlyNormalCrossingsWith_and_not_stalkIdeal_le`): `W_s` is
non-singular, `E_s` has only normal crossings with `W_s`, and no component of `E_s` through a point
of `W_s` has stalk contained in that of `W_s` (transversality, needed for `Ẽ_j = Ê_j ∩ X̃` to be
divisors of `X̃`). It is the induction of Lemma 4 of §2 (`DatumI.Raw.resolvedAt_transform_of_resolvedAt`)
along `s`, with `W_s` irreducible and `W_s ⊄ E_s` carried along.

* `DatumI.Raw.isPermissible_of_resolvedAt`: a center in `W` with normal crossings with `E` is permissible.
* `MonoidalSuccession.CentersAdapted`: the hypotheses on the centers, stage by stage.
* `Subscheme.hasOnlyNormalCrossingsWithAt_iInf_comp`: sub-unions of a family of divisors keep
  normal crossings (`E_{α+1}(s) ∪ ⋯ ∪ E_{α+s}(s)` inside `E_1(s) ∪ ⋯ ∪ E_{α+s}(s)`).

Deviation from the paper (gap filled): both sentences are given without proof.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry IsLocalRing

namespace Hironaka

universe u

namespace DatumI.Raw

variable {X : Scheme.{u}}

/-- A center `B ⊆ W` with `E` having only normal crossings with `B` is permissible for a datum
resolved at the points of `W` (the normal flatness of `V_j` and of `W` along `B` is automatic at
the simple points of `W`). -/
theorem isPermissible_of_resolvedAt [IsAlgebraicScheme X] {ℜ : DatumI.Raw X} (hℜ : ℜ.IsDatum)
    (hres : ∀ x ∈ ℜ.W.pts, ℜ.ResolvedAt x) {B : Subscheme X} (hB : B.IsCenter)
    (hBW : B.pts ⊆ ℜ.W.pts) (hEB : ∀ x ∈ B.pts, ℜ.E.HasOnlyNormalCrossingsWithAt B x) :
    ℜ.IsPermissible B := by
  have hBred : B.IsReduced := hB.isReduced
  have hBcont : B.IsContainedIn ℜ.W := Subscheme.isContainedIn_of_pts_subset hBred hBW
  refine ⟨hB, isDatum_extendBy hℜ hBred hBW, fun x hx => ?_⟩
  have hxB : x ∈ B.pts := hx
  have hxW := hres x (hBW hxB)
  have hBs : B.IsSimpleAt x := ⟨hxB, Subscheme.isRegular_stalk_quot B hB.isNonsingular hxB⟩
  refine ⟨hBs, fun j => ?_, hEB x hxB⟩
  refine Fin.lastCases ?_ (fun i => ?_) j
  · simp only [extendBy, Fin.snoc_last]
    exact Subscheme.isNormallyFlatAlongAt'_of_isSimpleAt hBcont hxW.1 hBs
  · simp only [extendBy, Fin.snoc_castSucc]
    exact Subscheme.isNormallyFlatAlongAt'_of_isContainedIn (hℜ.2.2.2.2 i) hBcont hxW.1 hBs (hxW.2.1 i)

end DatumI.Raw

namespace MonoidalSuccession

/-- The hypotheses on the centers in the situation of p. 321 (resp. p. 308): the center `B` of each
step is a center contained in `W`, with `E` having only normal crossings with `B`, and `W` is not
contained in `B`; stage by stage along the transforms of the datum. -/
def CentersAdapted : {X Y : Scheme.{u}} → MonoidalSuccession X Y → DatumI.Raw X → Prop
  | _, _, nil _, _ => True
  | _, _, cons B t rest, ℜ =>
      B.IsCenter ∧ B.pts ⊆ ℜ.W.pts ∧ (∀ x ∈ B.pts, ℜ.E.HasOnlyNormalCrossingsWithAt B x) ∧
        ¬ ℜ.W.pts ⊆ B.pts ∧ rest.CentersAdapted (ℜ.transform t)

/-- **Induction along a succession** (pp. 308, 321). Let `ℜ = (E; V; W)` be a datum on an ambient
scheme which is resolved at the points of the irreducible `W`, `W ⊄ E`, and let `s` be a succession
with centers `B_t ⊆ W_t` (non-singular irreducible, `W_t ⊄ B_t`) such that the transformed `E_t`
has only normal crossings with `B_t`.  Then `s` is permissible for `ℜ`, the transform is again a
datum resolved at the points of `W_s` (so `W_s` is non-singular and `E_s` has only normal crossings
with it), `W_s` is irreducible and `W_s ⊄ E_s`. -/
theorem isPermissibleI_and_resolvedAt_transformI_of_centersAdapted [Hironaka.HironakaCitedResults.{u}] {N : ℕ} :
    ∀ {X Y : Scheme.{u}} (s : MonoidalSuccession X Y) {ℜ : DatumI.Raw X},
      IsAmbient X N → ℜ.IsDatum → (∀ x ∈ ℜ.W.pts, ℜ.ResolvedAt x) →
      _root_.IsIrreducible ℜ.W.pts → ¬ ℜ.W.pts ⊆ ℜ.E.pts → s.CentersAdapted ℜ →
      s.IsPermissibleI ℜ ∧ IsAmbient Y N ∧ (s.transformI ℜ).IsDatum ∧
        (∀ y ∈ (s.transformI ℜ).W.pts, (s.transformI ℜ).ResolvedAt y) ∧
        _root_.IsIrreducible (s.transformI ℜ).W.pts ∧
        ¬ (s.transformI ℜ).W.pts ⊆ (s.transformI ℜ).E.pts := by
  intro X Y s
  induction s with
  | nil X =>
    intro ℜ hX hℜ hres hirr hE _
    exact ⟨trivial, hX, hℜ, hres, hirr, hE⟩
  | cons B t rest ih =>
    intro ℜ hX hℜ hres hirr hE hs
    obtain ⟨hBc, hBW, hEB, hWB, hrest⟩ := hs
    have := hX.1
    have := hX.2.2.1
    have hperm := DatumI.Raw.isPermissible_of_resolvedAt hℜ hres hBc hBW hEB
    have hBX : B.pts ≠ Set.univ := fun h => hWB (h ▸ Set.subset_univ _)
    obtain ⟨h1, h2, h3, h4⟩ := MonoidalTransformation.transform_isAmbient hX.2.1 hBc hBX t
    have hX' : IsAmbient t.X' N := ⟨h1, h2, h3, h4.trans hX.2.2.2⟩
    have hℜ' := (DatumI.Raw.transform_isDatum hX.2.1 ℜ hℜ t hperm).1
    have hdense : ℜ.W.pts ⊆ closure (ℜ.W.pts \ B.pts) := by
      obtain ⟨w, hw, hwB⟩ := Set.not_subset.mp hWB
      exact subset_closure_inter_of_isPreirreducible_of_isOpen hirr.2
        B.support.isClosed.isOpen_compl ⟨w, hw, hwB⟩
    have hres' : ∀ y ∈ (ℜ.transform t).W.pts, (ℜ.transform t).ResolvedAt y := fun y hy =>
      DatumI.Raw.resolvedAt_transform_of_resolvedAt hX.2.2.1 hX.2.1 hℜ hperm hdense t hy
        (hres _ (MonoidalTransformation.pts_strictTransform_subset t _ hy))
    have hirr' : _root_.IsIrreducible (ℜ.transform t).W.pts :=
      Subscheme.isIrreducible_pts _ (t.strictTransform_isIrreducible ℜ.W
        (Subscheme.isIrreducible_of_pts _ hirr) hWB)
    have hE' : ¬ (ℜ.transform t).W.pts ⊆ (ℜ.transform t).E.pts := by
      obtain ⟨w, hwW, hwE⟩ := Set.not_subset.mp hE
      obtain ⟨w', hw'W, hw'⟩ := hirr.2 (ℜ.E.pts)ᶜ (B.pts)ᶜ ℜ.E.support.isClosed.isOpen_compl
        B.support.isClosed.isOpen_compl ⟨w, hwW, hwE⟩
        (let ⟨b, hb, hbB⟩ := Set.not_subset.mp hWB; ⟨b, hb, hbB⟩)
      obtain ⟨Z, ι, j', -, -, -, -, -, hcomp, hrι, hrange, -, -⟩ :=
        Hironaka.DatumTransform.exists_flat_isPreimmersion_off_center t
      obtain ⟨v, hv⟩ : w' ∈ Set.range ι.base := by rw [hrι]; exact hw'.2
      have hzE : j'.base v ∉ t.exceptional.pts := by
        have : j'.base v ∈ Set.range j'.base := ⟨v, rfl⟩
        rwa [hrange] at this
      have hf : t.f.base (j'.base v) = w' := by rw [hcomp]; exact hv
      intro hsub
      have hmem : j'.base v ∈ (ℜ.transform t).W.pts := by
        change j'.base v ∈ (Subscheme.strictTransform t ℜ.W).pts
        rw [MonoidalTransformation.mem_pts_strictTransform_iff_of_notMem t _ hzE, hf]
        exact hw'W
      have := hsub hmem
      change j'.base v ∈ (Subscheme.strictTransform t ℜ.E ⊓ t.exceptional).pts at this
      rw [Subscheme.pts_inf] at this
      rcases this with h | h
      · rw [MonoidalTransformation.mem_pts_strictTransform_iff_of_notMem t _ hzE, hf] at h
        exact hw'.1 h
      · exact hzE h
    obtain ⟨hp, hY, hd, hr, hi, he⟩ := ih (ℜ := ℜ.transform t) hX' hℜ' hres' hirr' hE' hrest
    exact ⟨⟨hperm, hp⟩, hY, hd, hr, hi, he⟩

end MonoidalSuccession

namespace Subscheme

variable {Y : Scheme.{u}}

/-- Stalks of ideal sheaves at a generization are obtained by localizing: if `η ⤳ x` and
`C_x ≤ W_x` then `C_η ≤ W_η`. -/
theorem stalkIdeal_le_of_specializes_of_le {C W : Subscheme Y} {η x : Y} (h : η ⤳ x)
    (hle : C.stalkIdeal x ≤ W.stalkIdeal x) : C.stalkIdeal η ≤ W.stalkIdeal η := by
  obtain ⟨U, hxU⟩ := exists_affineOpen_mem x
  have hηU : η ∈ (U : Y.Opens) := h.mem_open U.1.isOpen hxU
  let φ := (Y.presheaf.stalkSpecializes h).hom
  have hgerm : ∀ a, φ (Y.presheaf.germ U x hxU a) = Y.presheaf.germ U η hηU a := fun a => by
    have := Y.presheaf.germ_stalkSpecializes hxU h
    exact congrArg (fun f => f.hom a) this
  have key : ∀ D : Subscheme Y, D.stalkIdeal η = (D.stalkIdeal x).map φ := by
    intro D
    rw [stalkIdeal_eq_map_germ_affine D U hxU, stalkIdeal_eq_map_germ_affine D U hηU,
      Ideal.map_map]
    congr 1
    ext a
    exact (hgerm a).symm
  rw [key C, key W]
  exact Ideal.map_mono hle

/-- **Transversality.** If `W` is irreducible and not contained in `E`, no subscheme `C` with
`C ⊆ E` (as a set) has stalk contained in that of `W` at a point of `W`: the generic point of `W`
would lie on `C`, hence `W ⊆ C ⊆ E`. -/
theorem not_stalkIdeal_le_of_isIrreducible_not_subset {E W C : Subscheme Y}
    (hirr : _root_.IsIrreducible W.pts) (hW : ¬ W.pts ⊆ E.pts) (hCE : C.pts ⊆ E.pts) {y : Y}
    (hy : y ∈ W.pts) : ¬ C.stalkIdeal y ≤ W.stalkIdeal y := by
  intro hle
  have hcl : IsClosed W.pts := W.support.isClosed
  have hη : closure {hirr.genericPoint} = W.pts := hirr.closure_genericPoint hcl
  have hηW : hirr.genericPoint ∈ W.pts := hη.le (subset_closure (Set.mem_singleton _))
  have hyη : hirr.genericPoint ⤳ y :=
    specializes_iff_mem_closure.mpr (by rw [hη]; exact hy)
  have h1 := stalkIdeal_le_of_specializes_of_le hyη hle
  have hηC : hirr.genericPoint ∈ C.pts := by
    rw [mem_pts_iff_stalkIdeal_ne_top] at hηW ⊢
    intro htop
    rw [htop, top_le_iff] at h1
    exact hηW h1
  refine hW fun z hz => hCE ?_
  rw [← hη] at hz
  exact closure_minimal (Set.singleton_subset_iff.mpr hηC) C.support.isClosed hz


/-- A subscheme simple at all its points is non-singular. -/
theorem isNonsingular_of_forall_isSimpleAt {W : Subscheme Y} (h : ∀ y ∈ W.pts, W.IsSimpleAt y) :
    W.IsNonsingular := by
  intro w
  obtain ⟨e⟩ := nonempty_stalk_quot_equiv W w
  have : IsRegularLocalRing (Y.presheaf.stalk (W.ι w) ⧸ W.stalkIdeal (W.ι w)) :=
    (h _ (mem_pts_ι W w)).2
  exact IsRegularLocalRing.of_ringEquiv e


open Classical in
/-- **Sub-unions keep normal crossings** (p. 321: "`Ê_{α+1}(s) ∪ ⋯ ∪ Ê_{α+s}(s)`" is a sub-union of
`Ê_1(s) ∪ ⋯ ∪ Ê_{α+s}(s)`).  If a finite family of divisors, non-singular of codimension one at
their points, has reduced union with only normal crossings with `D` at `x`, then so has the union
of any subfamily. -/
theorem hasOnlyNormalCrossingsWithAt_iInf_comp {ι ι' : Type*} [Fintype ι] [Fintype ι']
    (σ : ι' → ι) {E : ι → Subscheme Y} {D : Subscheme Y} {x : Y}
    [IsRegularLocalRing (Y.presheaf.stalk x)] (hE : (⨅ j, E j).IsReduced)
    (h : (⨅ j, E j).HasOnlyNormalCrossingsWithAt D x)
    (hsimple : ∀ j, x ∈ (E j).pts → (E j).IsSimpleAt x ∧ (E j).codimAt x = 1) :
    (⨅ i, E (σ i)).HasOnlyNormalCrossingsWithAt D x := by
  obtain ⟨z, hz, ⟨J, hJz, hEJ⟩, ⟨T, hTz, hDT⟩⟩ :=
    (hasOnlyNormalCrossingsWithAt_iff hE (by exact ‹IsRegularLocalRing (Y.presheaf.stalk x)›)).mp h
  have key : ∀ j, ∃ A : Finset (Y.presheaf.stalk x), A ⊆ J ∧
      (x ∈ (E j).pts → ∃ a, A = {a} ∧ (E j).stalkIdeal x = Ideal.span {a}) ∧
      (x ∉ (E j).pts → A = ∅ ∧ (E j).stalkIdeal x = ⊤) := by
    intro j
    by_cases hx : x ∈ (E j).pts
    · obtain ⟨hs, hc⟩ := hsimple j hx
      have hreg : IsRegularLocalRing (Y.presheaf.stalk x ⧸ (E j).stalkIdeal x) := hs.2
      have hPp : ((E j).stalkIdeal x).IsPrime :=
        (Ideal.Quotient.isDomain_iff_prime _).mp (Transforms.isDomain_of_isRegularLocalRing _)
      have hle : Ideal.span {∏ a ∈ J, a} ≤ (E j).stalkIdeal x := by
        rw [← hEJ, DatumTransform.stalkIdeal_iInf_fintype]
        exact iInf_le _ j
      obtain ⟨a, haJ, hPa⟩ := exists_eq_span_of_prod_mem hz hJz hc hle
      exact ⟨{a}, Finset.singleton_subset_iff.mpr haJ, fun _ => ⟨a, rfl, hPa⟩,
        fun hx' => absurd hx hx'⟩
    · exact ⟨∅, Finset.empty_subset _, fun hx' => absurd hx' hx,
        fun _ => ⟨rfl, stalkIdeal_eq_top_of_notMem_pts hx⟩⟩
  choose A hAJ hA1 hA0 using key
  have hst : ∀ j, (E j).stalkIdeal x = Ideal.span {∏ a ∈ A j, a} := by
    intro j
    by_cases hx : x ∈ (E j).pts
    · obtain ⟨a, haA, hEa⟩ := hA1 j hx
      rw [hEa, haA, Finset.prod_singleton]
    · obtain ⟨hA, hEt⟩ := hA0 j hx
      rw [hEt, hA, Finset.prod_empty, Ideal.span_singleton_one]
  have hext : ExtendsToRSOP _ (Finset.univ.biUnion fun i => A (σ i)) :=
    (ExtendsToRSOP.of_isRegularSystemOfParameters hz).mono (Finset.biUnion_subset.mpr
      fun i _ => (hAJ (σ i)).trans hJz)
  refine hasOnlyNormalCrossingsWithAt_of_stalkIdeal_eq hz
    (J := Finset.univ.biUnion fun i => A (σ i)) (Finset.biUnion_subset.mpr fun i _ => (hAJ (σ i)).trans hJz) hTz ?_ hDT
  rw [DatumTransform.stalkIdeal_iInf_fintype, ← iInf_span_prod_biUnion _ hext]
  exact iInf_congr fun i => hst (σ i)

end Subscheme




namespace MonoidalSuccession

/-- **The exceptional divisors are transversal to the strict transform of a non-singular
subscheme** (pp. 308, 321). In the situation of `isPermissibleI_and_resolvedAt_transformI_of_centersAdapted`:
(i) `W_s` is non-singular; (ii) `E_s` has only normal crossings with `W_s` at every point of
`W_s`; (iii) no component of `E_s` through a point of `W_s` has stalk contained in that of `W_s`.

Deviation from the paper (gap filled): p. 321 says "we see that `Ê_{α+1}(s) ∪ ⋯ ∪ Ê_{α+s}(s)` has
only normal crossings with `X̃` in `X̂_s`" and p. 308 "It is clear that `Ê'_{α+1}(s) ∪ ⋯ ∪
Ê'_{α+s}(s)` has only normal crossings with `X̄'_s` on `X̂'_s`" without proof; the statement is the induction
along the succession (Lemma 4 of §2 at the points of the centers, Cor. 2 of Th. 5 off them), with
the transversality (iii) of the exceptional divisors, which both sentences use tacitly. -/
@[blueprint "lem:IV.4-exceptional-transversal"
  (statement := /-- Let $X$ be a non-singular irreducible algebraic scheme, $\mathfrak R=(E;V;W)$ a
    resolution datum of type I resolved at every point of the irreducible subscheme $W$, with
    $W\not\subseteq E$, and $f\colon X_s\to X$ a succession of monoidal transformations whose
    $t$-th center $B_t$ is non-singular irreducible, contained in $W_t$ and not containing it,
    $E_t$ having only normal crossings with $B_t$. Then $W_s$ is non-singular and irreducible,
    $E_s$ has only normal crossings with $W_s$, and no irreducible component of $E_s$ through a
    point of $W_s$ contains $W_s$ near that point. (Used on pp.~308, 321.) -/)
  (proof := /-- By induction on $s$. The datum $\mathfrak R$ is resolved along $W$ and $B\subseteq W$
    is non-singular with $E$ having only normal crossings with $B$, so $B$ is a permissible center
    (the normal flatness of $W$ and of the $V_j$ along $B$ at the simple points of $W$ is automatic).
    Then $f^*\mathfrak R$ is a datum (Remark~1, p.~169), resolved at the points of $W'$ by Lemma~4
    of \S2 at the points over $B$ and off $f^{-1}(B)$ because $f$ is an isomorphism there; $W'$ is
    irreducible as a strict transform of an irreducible subscheme not contained in $B$, and
    $W'\not\subseteq E'=(E)'\cup f^{-1}(B)$ since a point of $W\setminus(E\cup B)$ lifts to $W'$. For
    the transversality: the generic point of the irreducible $W_s$ is a generization of every point
    of $W_s$ and lies on no component of $E_s$ (else $W_s\subseteq E_s$).

    \textbf{Deviation from the paper (gap filled).} The paper writes ``we see that \dots\ has only
    normal crossings with $\tilde X$ in $\hat X_s$'' (p.~321) and ``It is clear that \dots\ has only
    normal crossings with $\bar X_s'$ on $\hat X_s'$'' (p.~308) without proof, and uses the transversality of the
    exceptional divisors tacitly. -/)
  (proofUses := ["lem:IV.2-4", "rem:I.1-transform-is-datum-I"])
  (latexEnv := "lemma")]
theorem isNonsingular_and_hasOnlyNormalCrossingsWith_and_not_stalkIdeal_le [Hironaka.HironakaCitedResults.{u}] {N : ℕ}
    {X Y : Scheme.{u}} (s : MonoidalSuccession X Y) {ℜ : DatumI.Raw X}
    (hX : IsAmbient X N) (hℜ : ℜ.IsDatum) (hres : ∀ x ∈ ℜ.W.pts, ℜ.ResolvedAt x)
    (hirr : _root_.IsIrreducible ℜ.W.pts) (hE : ¬ ℜ.W.pts ⊆ ℜ.E.pts)
    (hs : s.CentersAdapted ℜ) :
    (s.transformI ℜ).W.IsNonsingular ∧
    (∀ y ∈ (s.transformI ℜ).W.pts, (s.transformI ℜ).E.HasOnlyNormalCrossingsWithAt
      (s.transformI ℜ).W y) ∧
    (∀ y ∈ (s.transformI ℜ).W.pts, ∀ C ∈ (s.transformI ℜ).E.irreducibleComponents,
      ¬ C.stalkIdeal y ≤ (s.transformI ℜ).W.stalkIdeal y) := by
  obtain ⟨-, -, -, hr, hi, he⟩ :=
    isPermissibleI_and_resolvedAt_transformI_of_centersAdapted s hX hℜ hres hirr hE hs
  refine ⟨Subscheme.isNonsingular_of_forall_isSimpleAt fun y hy => (hr y hy).1,
    fun y hy => (hr y hy).2.2, fun y hy C hC => ?_⟩
  exact Subscheme.not_stalkIdeal_le_of_isIrreducible_not_subset hi he
    (Subscheme.pts_subset_of_mem_irreducibleComponents hC) hy

/-- The hypotheses on the centers when the centers are only non-singular, not necessarily
irreducible (the centers `B̂_t = c_t⁻¹(B_t)` of `X̂_t` can be reducible): the center `B` of each step is non-singular, contained in `W`,
`E` has only normal crossings with `B` at its points, and `W` is not contained in `B`. -/
def CentersAdaptedNonsingular : {X Y : Scheme.{u}} → MonoidalSuccession X Y → DatumI.Raw X → Prop
  | _, _, nil _, _ => True
  | _, _, cons B t rest, ℜ =>
      B.IsNonsingular ∧ B.IsContainedIn ℜ.W ∧
        (∀ x ∈ B.pts, ℜ.E.HasOnlyNormalCrossingsWithAt B x) ∧
        ¬ ℜ.W.pts ⊆ B.pts ∧ rest.CentersAdaptedNonsingular (ℜ.transform t)

open Classical in
/-- **Induction along a succession with non-singular centers** (pointwise form of
`isPermissibleI_and_resolvedAt_transformI_of_centersAdapted`): normal crossings, simplicity and
transversality are local, so the induction runs on the stalk presentations
`E_y = (∏ K)`, `K` part of a regular system of parameters, without going through `IsDatum` or
`IsCenter`; the centers need not be irreducible.  (Core version: neither the irreducibility of `W`
nor `W ⊄ E` is needed for the normal crossings and the stalk presentations.) -/
theorem stalkwise_normalCrossings_transformI_of_centersAdaptedNonsingular_core :
    ∀ {X Y : Scheme.{u}} (s : MonoidalSuccession X Y) {ℜ : DatumI.Raw X}, X.IsNonsingular →
      (∀ y, ∃ K : Finset (X.presheaf.stalk y), ExtendsToRSOP _ K ∧
        ℜ.E.stalkIdeal y = Ideal.span {∏ k ∈ K, k}) →
      (∀ x ∈ ℜ.W.pts, ℜ.E.HasOnlyNormalCrossingsWithAt ℜ.W x) →
      s.CentersAdaptedNonsingular ℜ →
      Y.IsNonsingular ∧
      (∀ y, ∃ K : Finset (Y.presheaf.stalk y), ExtendsToRSOP _ K ∧
        (s.transformI ℜ).E.stalkIdeal y = Ideal.span {∏ k ∈ K, k}) ∧
      (∀ y ∈ (s.transformI ℜ).W.pts, (s.transformI ℜ).E.HasOnlyNormalCrossingsWithAt
        (s.transformI ℜ).W y) := by
  intro X Y s
  induction s with
  | nil X =>
    intro ℜ hX hE hres _
    exact ⟨hX, hE, hres⟩
  | @cons X₀ B t Y₀ rest ih =>
    intro ℜ hX hE hres hs
    obtain ⟨hBns, hBW, hEB, hWB, hrest⟩ := hs
    have hX' : t.X'.IsNonsingular := (t.isNonsingular_and_isNonsingular_exceptional hX hBns).1
    have hEred : ℜ.E.IsReduced := DatumTransform.isReduced_of_forall_stalk hX hE
    -- the stalk presentations of the transformed boundary
    have hE' : ∀ y : t.X', ∃ K : Finset (t.X'.presheaf.stalk y), ExtendsToRSOP _ K ∧
        (ℜ.transform t).E.stalkIdeal y = Ideal.span {∏ k ∈ K, k} := by
      intro y
      have : IsRegularLocalRing (t.X'.presheaf.stalk y) := hX' y
      have : IsRegularLocalRing (X₀.presheaf.stalk (t.f.base y)) := hX _
      obtain ⟨Z, hZ, J, hJZ, hEJ, hBZ⟩ : ∃ Z : Finset (X₀.presheaf.stalk (t.f.base y)),
          IsRegularSystemOfParameters _ Z ∧ ∃ J ⊆ Z,
            ℜ.E.stalkIdeal (t.f.base y) = Ideal.span {∏ z ∈ J, z} ∧
            (t.f.base y ∈ B.pts → ∃ T ⊆ Z, B.stalkIdeal (t.f.base y) = Ideal.span (T : Set _)) := by
        by_cases hy : t.f.base y ∈ B.pts
        · obtain ⟨Z, hZ, ⟨J, hJZ, hEJ⟩, ⟨T, hTZ, hBT⟩⟩ :=
            (Subscheme.hasOnlyNormalCrossingsWithAt_iff hEred (hX _)).mp (hEB _ hy)
          exact ⟨Z, hZ, J, hJZ, hEJ, fun _ => ⟨T, hTZ, hBT⟩⟩
        · obtain ⟨K, ⟨Z, hKZ, hZ⟩, hK⟩ := hE (t.f.base y)
          exact ⟨Z, hZ, K, hKZ, hK, fun h => absurd h hy⟩
      obtain ⟨K, hK, ⟨K₀, hK₀, -, hexc⟩, hst⟩ :=
        DatumTransform.exists_stalk_transform hX hBns t y hZ hBZ
      obtain ⟨K₁, hK₁, -, hstE⟩ := hst J hJZ ℜ.E hEJ
      refine ⟨K₁ ∪ K₀, hK.mono (Finset.union_subset hK₁ hK₀), ?_⟩
      show ((Subscheme.strictTransform t ℜ.E) ⊓ t.exceptional).stalkIdeal y = _
      rw [Subscheme.stalkIdeal_inf_eq, hstE, hexc, DatumTransform.span_prod_inf_of_subset hK hK₁ hK₀]
    -- normal crossings with the strict transform of `W`
    have hres' : ∀ y ∈ (Subscheme.strictTransform t ℜ.W).pts,
        (ℜ.transform t).E.HasOnlyNormalCrossingsWithAt (Subscheme.strictTransform t ℜ.W) y := by
      intro y hy
      have : IsRegularLocalRing (t.X'.presheaf.stalk y) := hX' y
      have hxW : t.f.base y ∈ ℜ.W.pts := MonoidalTransformation.pts_strictTransform_subset t _ hy
      by_cases hyB : t.f.base y ∈ B.pts
      · obtain ⟨K, ⟨Z', hKZ', hZ'⟩, ⟨K₁, hK₁, hD⟩, ⟨T, hT, hW⟩⟩ :=
          t.exists_extendsToRSOP_stalkIdeal_of_hasOnlyNormalCrossingsWithAt hX hBns hBW hEred
            (hres _ hxW) (hEB _ hyB) hy
        exact Subscheme.hasOnlyNormalCrossingsWithAt_of_stalkIdeal_eq hZ' (hK₁.trans hKZ')
          (hT.trans hKZ') hD hW
      · have : IsRegularLocalRing (X₀.presheaf.stalk (t.f.base y)) := hX _
        obtain ⟨e, hexc, hst⟩ := DatumTransform.exists_offCenter hX t y hyB
        obtain ⟨z, hz, ⟨J, hJz, hEJ⟩, ⟨T, hTz, hWT⟩⟩ :=
          (Subscheme.hasOnlyNormalCrossingsWithAt_iff hEred (hX _)).mp (hres _ hxW)
        refine Subscheme.hasOnlyNormalCrossingsWithAt_of_stalkIdeal_eq
          (isRegularSystemOfParameters_image_ringEquiv e hz) (J := J.image e) (T := T.image e)
          (Finset.image_subset_image hJz) (Finset.image_subset_image hTz) ?_ ?_
        · show ((Subscheme.strictTransform t ℜ.E) ⊓ t.exceptional).stalkIdeal y = _
          rw [Subscheme.stalkIdeal_inf_eq, hexc, inf_top_eq, hst, hEJ,
            DatumTransform.map_span_prod]
        · rw [hst, hWT, Ideal.map_span, Finset.coe_image]
    exact ih (ℜ := ℜ.transform t) hX' hE' hres' hrest

open Classical in
/-- Irreducibility of `W_s` and `W_s ⊄ E_s` along a succession with non-singular centers (the
transversality part of the induction). -/
theorem isIrreducible_and_not_subset_transformI_of_centersAdaptedNonsingular :
    ∀ {X Y : Scheme.{u}} (s : MonoidalSuccession X Y) {ℜ : DatumI.Raw X},
      _root_.IsIrreducible ℜ.W.pts → ¬ ℜ.W.pts ⊆ ℜ.E.pts → s.CentersAdaptedNonsingular ℜ →
      _root_.IsIrreducible (s.transformI ℜ).W.pts ∧
      ¬ (s.transformI ℜ).W.pts ⊆ (s.transformI ℜ).E.pts := by
  intro X Y s
  induction s with
  | nil X =>
    intro ℜ hirr hWE _
    exact ⟨hirr, hWE⟩
  | @cons X₀ B t Y₀ rest ih =>
    intro ℜ hirr hWE hs
    obtain ⟨hBns, hBW, hEB, hWB, hrest⟩ := hs
    have hirr' : _root_.IsIrreducible (ℜ.transform t).W.pts :=
      Subscheme.isIrreducible_pts _ (t.strictTransform_isIrreducible ℜ.W
        (Subscheme.isIrreducible_of_pts _ hirr) hWB)
    have hWE' : ¬ (ℜ.transform t).W.pts ⊆ (ℜ.transform t).E.pts := by
      obtain ⟨w, hwW, hwE⟩ := Set.not_subset.mp hWE
      obtain ⟨w', hw'W, hw'⟩ := hirr.2 (ℜ.E.pts)ᶜ (B.pts)ᶜ ℜ.E.support.isClosed.isOpen_compl
        B.support.isClosed.isOpen_compl ⟨w, hwW, hwE⟩
        (let ⟨b, hb, hbB⟩ := Set.not_subset.mp hWB; ⟨b, hb, hbB⟩)
      obtain ⟨Z, ι, j', -, -, -, -, -, hcomp, hrι, hrange, -, -⟩ :=
        Hironaka.DatumTransform.exists_flat_isPreimmersion_off_center t
      obtain ⟨v, hv⟩ : w' ∈ Set.range ι.base := by rw [hrι]; exact hw'.2
      have hzE : j'.base v ∉ t.exceptional.pts := by
        have : j'.base v ∈ Set.range j'.base := ⟨v, rfl⟩
        rwa [hrange] at this
      have hf : t.f.base (j'.base v) = w' := by rw [hcomp]; exact hv
      intro hsub
      have hmem : j'.base v ∈ (ℜ.transform t).W.pts := by
        change j'.base v ∈ (Subscheme.strictTransform t ℜ.W).pts
        rw [MonoidalTransformation.mem_pts_strictTransform_iff_of_notMem t _ hzE, hf]
        exact hw'W
      have := hsub hmem
      change j'.base v ∈ (Subscheme.strictTransform t ℜ.E ⊓ t.exceptional).pts at this
      rw [Subscheme.pts_inf] at this
      rcases this with h | h
      · rw [MonoidalTransformation.mem_pts_strictTransform_iff_of_notMem t _ hzE, hf] at h
        exact hw'.1 h
      · exact hzE h
    exact ih (ℜ := ℜ.transform t) hirr' hWE' hrest

/-- **Induction along a succession with non-singular centers**, with irreducibility of `W_s` and
`W_s ⊄ E_s` carried along. -/
theorem stalkwise_normalCrossings_transformI_of_centersAdaptedNonsingular {X Y : Scheme.{u}}
    (s : MonoidalSuccession X Y) {ℜ : DatumI.Raw X} (hX : X.IsNonsingular)
    (hE : ∀ y, ∃ K : Finset (X.presheaf.stalk y), ExtendsToRSOP _ K ∧
      ℜ.E.stalkIdeal y = Ideal.span {∏ k ∈ K, k})
    (hres : ∀ x ∈ ℜ.W.pts, ℜ.E.HasOnlyNormalCrossingsWithAt ℜ.W x)
    (hirr : _root_.IsIrreducible ℜ.W.pts) (hWE : ¬ ℜ.W.pts ⊆ ℜ.E.pts)
    (hs : s.CentersAdaptedNonsingular ℜ) :
    Y.IsNonsingular ∧
    (∀ y, ∃ K : Finset (Y.presheaf.stalk y), ExtendsToRSOP _ K ∧
      (s.transformI ℜ).E.stalkIdeal y = Ideal.span {∏ k ∈ K, k}) ∧
    (∀ y ∈ (s.transformI ℜ).W.pts, (s.transformI ℜ).E.HasOnlyNormalCrossingsWithAt
      (s.transformI ℜ).W y) ∧
    _root_.IsIrreducible (s.transformI ℜ).W.pts ∧
    ¬ (s.transformI ℜ).W.pts ⊆ (s.transformI ℜ).E.pts := by
  obtain ⟨h1, h2, h3⟩ :=
    stalkwise_normalCrossings_transformI_of_centersAdaptedNonsingular_core s hX hE hres hs
  obtain ⟨h4, h5⟩ :=
    isIrreducible_and_not_subset_transformI_of_centersAdaptedNonsingular s hirr hWE hs
  exact ⟨h1, h2, h3, h4, h5⟩


/-- **The exceptional divisors are transversal to the strict transform of a non-singular
subscheme, for non-singular (not necessarily irreducible) centers** (pp. 308, 321).  Version of
`isNonsingular_and_hasOnlyNormalCrossingsWith_and_not_stalkIdeal_le` with `CentersAdaptedNonsingular`
and a boundary given by stalk presentations (for instance `E = ∅`); also `E_s` has such
presentations (so is reduced, of codimension one, with only normal crossings).  The transversality
uses the irreducibility of `W_s`, not that of the centers.

Deviation from the paper (gap filled): "we see that `Ê_{α+1}(s) ∪ ⋯ ∪ Ê_{α+s}(s)` has only normal
crossings with `X̃` in `X̂_s`" (p. 321); the centers `B̂_t` of `X̂_t` can be reducible, which the version with `IsCenter` does not allow. -/
@[blueprint "lem:IV.4-exceptional-transversal-nonsingular"
  (statement := /-- Let $X$ be a non-singular scheme, $E\subseteq X$ a subscheme whose stalks are
    $(\prod_Ka)$ for parts $K$ of regular systems of parameters (so $E$ is reduced, of codimension
    one, with only normal crossings), $W\subseteq X$ an irreducible subscheme with $W\not\subseteq E$
    such that $E$ has only normal crossings with $W$, and $f\colon X_s\to X$ a succession of
    monoidal transformations whose $t$-th center $B_t$ is non-singular (not necessarily irreducible),
    contained in $W_t$ and not containing it, $E_t$ having only normal crossings with $B_t$. Then
    $X_s$ and $W_s$ are non-singular, $E_s$ has the same stalk presentations and only normal crossings
    with $W_s$, $W_s$ is irreducible, and no irreducible component of $E_s$ through a point of $W_s$
    contains $W_s$ near that point. (Used on p.~321, where the centers $\hat B_t=c_t^{-1}(B_t)$ can
    be reducible.) -/)
  (proof := /-- As for \cref{lem:IV.4-exceptional-transversal}, but the induction is run on the
    stalk presentations, which are local: the stalk of the boundary at a point is $(\prod_K)$ for a
    part $K$ of a regular system of parameters, a non-singular center whose ideal at the point is
    generated by part of such a system keeps this form for the transform (Remark~1, \S1, Ch.~I), and
    normal crossings with the strict transform of $W$ are read off the presentations (Lemma~4, \S2, at
    the points over the center; off the center the monoidal transformation is a local isomorphism).
    No irreducibility of the centers is used: irreducibility of $W_s$ and $W_s\not\subseteq E_s$ follow
    from those of $W$ and $W\not\subseteq B_t$.

    \textbf{Deviation from the paper (gap filled).} The paper uses the irreducibility of the centers
    $\hat B_t$ of $\hat X_t$ tacitly on p.~321; they can be reducible, so \cref{lem:IV.4-exceptional-transversal} does not
    apply to $\hat g_s$ and this version is used instead. -/)
  (proofUses := ["lem:IV.4-exceptional-transversal", "rem:I.1-transform-is-datum-I"])
  (latexEnv := "lemma")]
theorem isNonsingular_and_hasOnlyNormalCrossingsWith_and_not_stalkIdeal_le_of_centersAdaptedNonsingular
    {X Y : Scheme.{u}} (s : MonoidalSuccession X Y) {ℜ : DatumI.Raw X} (hX : X.IsNonsingular)
    (hE : ∀ y, ∃ K : Finset (X.presheaf.stalk y), ExtendsToRSOP _ K ∧
      ℜ.E.stalkIdeal y = Ideal.span {∏ k ∈ K, k})
    (hres : ∀ x ∈ ℜ.W.pts, ℜ.E.HasOnlyNormalCrossingsWithAt ℜ.W x)
    (hirr : _root_.IsIrreducible ℜ.W.pts) (hWE : ¬ ℜ.W.pts ⊆ ℜ.E.pts)
    (hs : s.CentersAdaptedNonsingular ℜ) :
    Y.IsNonsingular ∧ (s.transformI ℜ).W.IsNonsingular ∧
    (∀ y, ∃ K : Finset (Y.presheaf.stalk y), ExtendsToRSOP _ K ∧
      (s.transformI ℜ).E.stalkIdeal y = Ideal.span {∏ k ∈ K, k}) ∧
    (∀ y ∈ (s.transformI ℜ).W.pts, (s.transformI ℜ).E.HasOnlyNormalCrossingsWithAt
      (s.transformI ℜ).W y) ∧
    (∀ y ∈ (s.transformI ℜ).W.pts, ∀ C ∈ (s.transformI ℜ).E.irreducibleComponents,
      ¬ C.stalkIdeal y ≤ (s.transformI ℜ).W.stalkIdeal y) ∧
    _root_.IsIrreducible (s.transformI ℜ).W.pts ∧
    ¬ (s.transformI ℜ).W.pts ⊆ (s.transformI ℜ).E.pts := by
  obtain ⟨hY, hE', hres', hi, he⟩ :=
    stalkwise_normalCrossings_transformI_of_centersAdaptedNonsingular s hX hE hres hirr hWE hs
  refine ⟨hY, Subscheme.isNonsingular_of_forall_isSimpleAt fun y hy => ?_, hE', hres',
    fun y hy C hC => ?_, hi, he⟩
  · exact Subscheme.IsSimpleAt.of_hasOnlyNormalCrossingsWithAt (hY y) hy (hres' y hy)
  · exact Subscheme.not_stalkIdeal_le_of_isIrreducible_not_subset hi he
      (Subscheme.pts_subset_of_mem_irreducibleComponents hC) hy

/-- **Normal crossings of the boundary with the strict transform, for non-singular centers**
(pp. 308, 321), without any hypothesis on irreducibility: if `E` has stalk presentations and only
normal crossings with `W`, and the centers are non-singular and contained in the transforms of `W`,
then `E_s` has stalk presentations and only normal crossings with `W_s` at all points of `W_s`.
Core of `isNonsingular_and_hasOnlyNormalCrossingsWith_and_not_stalkIdeal_le_of_centersAdaptedNonsingular`.

Deviation from the paper (gap filled): "we see that `Ê_{α+1}(s) ∪ ⋯ ∪ Ê_{α+s}(s)` has only normal
crossings with `X̃` in `X̂_s`" (p. 321). -/
theorem hasOnlyNormalCrossingsWith_of_centersAdaptedNonsingular
    {X Y : Scheme.{u}} (s : MonoidalSuccession X Y) {ℜ : DatumI.Raw X} (hX : X.IsNonsingular)
    (hE : ∀ y, ∃ K : Finset (X.presheaf.stalk y), ExtendsToRSOP _ K ∧
      ℜ.E.stalkIdeal y = Ideal.span {∏ k ∈ K, k})
    (hres : ∀ x ∈ ℜ.W.pts, ℜ.E.HasOnlyNormalCrossingsWithAt ℜ.W x)
    (hs : s.CentersAdaptedNonsingular ℜ) :
    Y.IsNonsingular ∧ (s.transformI ℜ).W.IsNonsingular ∧
    (∀ y, ∃ K : Finset (Y.presheaf.stalk y), ExtendsToRSOP _ K ∧
      (s.transformI ℜ).E.stalkIdeal y = Ideal.span {∏ k ∈ K, k}) ∧
    (∀ y ∈ (s.transformI ℜ).W.pts, (s.transformI ℜ).E.HasOnlyNormalCrossingsWithAt
      (s.transformI ℜ).W y) := by
  obtain ⟨hY, hE', hres'⟩ :=
    stalkwise_normalCrossings_transformI_of_centersAdaptedNonsingular_core s hX hE hres hs
  exact ⟨hY, Subscheme.isNonsingular_of_forall_isSimpleAt fun y hy =>
    Subscheme.IsSimpleAt.of_hasOnlyNormalCrossingsWithAt (hY y) hy (hres' y hy), hE', hres'⟩

end MonoidalSuccession

/-! ### Generizations, reducedness and codimension one (used for the facts of p. 321) -/

namespace Subscheme

variable {Y : Scheme.{u}}

/-- **Codimension one at a generization.** If the stalk ideal of `D` at `y` is generated by a
member `a` of a regular system of parameters and the stalk ideal at the generization `η ⤳ y` is
prime, then `D` has codimension one at `η`. -/
theorem codimAt_eq_one_of_specializes {D : Subscheme Y} {η y : Y} (h : η ⤳ y)
    [IsRegularLocalRing (Y.presheaf.stalk y)] [IsRegularLocalRing (Y.presheaf.stalk η)]
    {a : Y.presheaf.stalk y} (ha : ExtendsToRSOP _ {a}) (hD : D.stalkIdeal y = Ideal.span {a})
    (hP : (D.stalkIdeal η).IsPrime) : D.codimAt η = 1 := by
  have ha0 : a ≠ 0 := by
    obtain ⟨Z, hsub, hZ⟩ := ha
    intro h0
    have := rsop_notMem_span hZ (Finset.empty_subset Z) (hsub (Finset.mem_singleton_self a))
      (Finset.notMem_empty a)
    apply this
    rw [Finset.coe_empty, Ideal.span_empty, h0]
    exact Ideal.zero_mem _
  let := (Y.presheaf.stalkSpecializes h).hom.toAlgebra
  have hloc := isLocalization_stalkSpecializes_of_specializes h
  have hdom : IsDomain (Y.presheaf.stalk y) := Transforms.isDomain_of_isRegularLocalRing _
  have hinj : Function.Injective (algebraMap (Y.presheaf.stalk y) (Y.presheaf.stalk η)) :=
    IsLocalization.injective (Y.presheaf.stalk η)
      (M := ((IsLocalRing.maximalIdeal (Y.presheaf.stalk η)).comap
        (Y.presheaf.stalkSpecializes h).hom).primeCompl)
      (Ideal.primeCompl_le_nonZeroDivisors _)
  have hid : D.stalkIdeal η = Ideal.span {algebraMap _ (Y.presheaf.stalk η) a} := by
    rw [stalkIdeal_eq_map_stalkSpecializes D h, hD, Ideal.map_span, Set.image_singleton]
    rfl
  have hne : algebraMap _ (Y.presheaf.stalk η) a ≠ 0 := fun h0 => ha0 (hinj (by simpa using h0))
  have hdomη : IsDomain (Y.presheaf.stalk η) := Transforms.isDomain_of_isRegularLocalRing _
  show (D.stalkIdeal η).height = 1
  rw [hid] at hP ⊢
  refine le_antisymm ?_ ?_
  · exact Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes (Ideal.span {_}) _
      ⟨⟨hP, le_rfl⟩, fun Q hQ _ => hQ.2⟩
  · refine Order.one_le_iff_ne_zero.mpr fun h0 => ?_
    have := Ideal.height_eq_zero_iff_eq_bot.mp h0
    exact hne (by simpa using (Ideal.span_singleton_eq_bot.mp this))

end Subscheme

namespace DatumII.Raw

/-- For a closed restriction `F`, the union `E_1 ∪ ⋯ ∪ E_α` has only normal crossings with `F`
(read off the normal crossings of `E_1 ∪ ⋯ ∪ E_α ∪ F`; the hypothesis of Definition 5 (II.1)). -/
theorem hasOnlyNormalCrossingsWith_eUnion_of_isClosedRestriction {X : Scheme.{u}}
    (hX : X.IsNonsingular) {ℜ : DatumII.Raw X} (hℜ : ℜ.IsDatum) {F : Subscheme X}
    (hF : ℜ.IsClosedRestriction F) : ℜ.eUnion.HasOnlyNormalCrossingsWith F := by
  classical
  intro x hx
  have : IsRegularLocalRing (X.presheaf.stalk x) := hX x
  have hG : ∀ o : Option (Fin ℜ.α), (o.elim F ℜ.E).IsNonsingularIrreducibleCodimOne := by
    rintro (_ | i)
    exacts [hF.1, hℜ.2.1 i]
  have hGle : ∀ o : Option (Fin ℜ.α), (ℜ.eUnion.union F) ≤ o.elim F ℜ.E := by
    rintro (_ | i)
    · exact inf_le_right
    · exact inf_le_left.trans (iInf_le _ i)
  obtain ⟨Z, hZ, -, hG'⟩ := DatumTransform.exists_rsop_of_hasOnlyNormalCrossingsWithAt _ hG hGle
    (D := ⊥) (hF.2 x)
  obtain ⟨f, hfZ, hFf⟩ := (hG' none).resolve_left (Subscheme.mem_pts_iff_stalkIdeal_ne_top.mp hx)
  obtain ⟨K, hKZ, hK⟩ := DatumTransform.iInf_eq_span_prod (fun i => (ℜ.E i).stalkIdeal x)
    ⟨Z, subset_rfl, hZ⟩ (fun i => hG' (some i))
  refine Subscheme.hasOnlyNormalCrossingsWithAt_of_stalkIdeal_eq hZ hKZ
    (T := {f}) (by simpa using hfZ) ?_ (by simpa using hFf)
  unfold DatumII.Raw.eUnion
  rw [DatumTransform.stalkIdeal_iInf_fintype]
  exact hK

end DatumII.Raw

namespace Subscheme

/-- A finite union of non-singular subschemes is reduced. -/
theorem isReduced_iInf_of_isNonsingular {Z : Scheme.{u}} {α : ℕ} (E : Fin α → Subscheme Z)
    (h : ∀ i, (E i).IsNonsingular) : (⨅ i, E i).IsReduced := by
  refine Subscheme.isReduced_of_isRadical_stalkIdeal fun z => ?_
  rw [DatumTransform.stalkIdeal_iInf_fintype]
  refine Ideal.isRadical_iInf _ fun i => ?_
  by_cases hz : z ∈ (E i).pts
  · exact (Subscheme.isPrime_stalkIdeal_of_isNonsingular_of_mem_pts (E i) (h i) hz).isRadical
  · rw [Subscheme.stalkIdeal_eq_top_of_notMem_pts hz]
    exact (show (⊤ : Ideal (Z.presheaf.stalk z)).IsRadical from fun _ _ => Submodule.mem_top)

end Subscheme

namespace Subscheme

theorem mem_pts_bot {Z : Scheme.{u}} (y : Z) : y ∈ (⊥ : Subscheme Z).pts := by
  rw [mem_pts_iff_stalkIdeal_ne_top, stalkIdeal_bot_eq]
  exact bot_ne_top

theorem stalkIdeal_totalTransform_bot {Y' Y : Scheme.{u}} (g : Y' ⟶ Y) (y : Y') :
    (totalTransform g (⊥ : Subscheme Y)).stalkIdeal y = (⊥ : Subscheme Y').stalkIdeal y := by
  rw [Hironaka.stalkIdeal_totalTransform, stalkIdeal_bot_eq, stalkIdeal_bot_eq, Ideal.map_bot]

end Subscheme

namespace Subscheme

/-- A simple point of codimension one: the stalk ideal is generated by a member of a regular
system of parameters. -/
theorem isSimpleAt_and_codimAt_eq_one_of_stalkIdeal_eq_span {Y : Scheme.{u}} {D : Subscheme Y}
    {x : Y} [IsRegularLocalRing (Y.presheaf.stalk x)] {a : Y.presheaf.stalk x}
    (ha : ExtendsToRSOP _ {a}) (hD : D.stalkIdeal x = Ideal.span {a}) :
    D.IsSimpleAt x ∧ D.codimAt x = 1 := by
  have hP : (D.stalkIdeal x).IsPrime := by
    rw [hD]
    simpa using ha.isPrime_span_singleton (k := a) (Finset.mem_singleton_self a)
  refine ⟨⟨mem_pts_iff_stalkIdeal_ne_top.mpr hP.ne_top, ?_⟩, ?_⟩
  · rw [hD]
    exact ha.isRegularLocalRing_quotient_span_singleton (Finset.mem_singleton_self a)
  · exact codimAt_eq_one_of_specializes (specializes_refl x) ha hD hP

end Subscheme

/-! ### Adapted regular systems of parameters and closed subschemes (Remark 1, p. 322) -/

open Classical in
/-- **Adapting a regular system of parameters to a prime and a family.**  Let `P` be a prime of the
regular local ring `R` with `R/P` regular, and `K` a part of a regular system of parameters whose
members outside `P` stay independent modulo `P`.  Then there is a regular system of parameters `Z`
containing `K`, and a part `T ⊆ Z` generating `P`. -/
theorem exists_isRegularSystemOfParameters_subset_and_span_eq_prime {R : Type u} [CommRing R]
    [IsRegularLocalRing R] (P : Ideal R) [P.IsPrime] (hP : IsRegularLocalRing (R ⧸ P))
    (K : Finset R) (hK : ExtendsToRSOP R K)
    (hF : RSOPIndep (K.filter (· ∉ P)) (fun k : R => Ideal.Quotient.mk P k)) :
    ∃ Z T : Finset R, IsRegularSystemOfParameters R Z ∧ K ⊆ Z ∧ T ⊆ Z ∧
      Ideal.span (T : Set R) = P := by
  -- a regular system of parameters adapted to `P`
  obtain ⟨S, T₁, hS, hScard, hT₁S, hT₁⟩ := exists_finset_span_eq_prime R P hP
  have hS' : IsRegularSystemOfParameters R S := by
    refine ⟨hS, ?_⟩
    rw [hScard, IsRegularLocalRing.spanFinrank_maximalIdeal]
  -- exchange the members of `K ∩ P` into the system
  have key : ∀ J : Finset R, J ⊆ K.filter (· ∈ P) →
      ∃ Z T : Finset R, IsRegularSystemOfParameters R Z ∧ J ⊆ Z ∧ T ⊆ Z ∧
        Ideal.span (T : Set R) = P := by
    intro J
    induction J using Finset.induction_on with
    | empty => intro _; exact ⟨S, T₁, hS', Finset.empty_subset _, hT₁S, hT₁⟩
    | insert f J hfJ ih =>
      intro hJ
      obtain ⟨Z, T, hZ, hJZ, hTZ, hT⟩ := ih ((Finset.subset_insert f J).trans hJ)
      have hfK : f ∈ K.filter (· ∈ P) := hJ (Finset.mem_insert_self f J)
      have hfP : f ∈ Ideal.span (T : Set R) := by rw [hT]; exact (Finset.mem_filter.mp hfK).2
      have hJf : ExtendsToRSOP R (insert f J) := hK.mono (fun a ha => by
        rcases Finset.mem_insert.mp ha with rfl | ha
        · exact (Finset.mem_filter.mp hfK).1
        · exact (Finset.mem_filter.mp (hJ (Finset.mem_insert_of_mem ha))).1)
      obtain ⟨Z', T', hZ', hJZ', hfZ', hT'Z', hT'⟩ :=
        ExtendsToRSOP.exchange hZ hJZ hTZ hfP hfJ hJf
      exact ⟨Z', T', hZ', Finset.insert_subset hfZ' hJZ', hT'Z', by rw [hT', hT]⟩
  obtain ⟨Z₂, T₂, hZ₂, hKZ₂, hT₂Z₂, hT₂⟩ := key (K.filter (· ∈ P)) subset_rfl
  -- `G = T₂ ∪ (K ∩ P)` is independent and generates `P`
  set G : Finset R := T₂ ∪ K.filter (· ∈ P) with hGdef
  have hGZ : G ⊆ Z₂ := Finset.union_subset hT₂Z₂ hKZ₂
  have hGind : RSOPIndep G (fun z : R => z) :=
    RSOPIndep.of_extends (fun a _ b _ h => h) (by
      rw [Finset.image_id']; exact ⟨Z₂, hGZ, hZ₂⟩)
  have hGP : Ideal.span (G : Set R) = P := by
    refine le_antisymm (Ideal.span_le.mpr fun a ha => ?_) ?_
    · rcases Finset.mem_union.mp (Finset.mem_coe.mp ha) with h | h
      · exact hT₂ ▸ Ideal.subset_span (Finset.mem_coe.mpr h)
      · exact (Finset.mem_filter.mp h).2
    · rw [← hT₂]
      exact Ideal.span_mono (by simp [hGdef])
  have hdisj : Disjoint G (K.filter (· ∉ P)) := by
    rw [Finset.disjoint_left]
    intro a haG haK
    have : a ∈ P := hGP ▸ Ideal.subset_span (Finset.mem_coe.mpr haG)
    exact (Finset.mem_filter.mp haK).2 this
  have hun := RSOPIndep.union_of_quotient hdisj hGind (J := P) (by simpa using hGP.symm) hF
  obtain ⟨-, hext⟩ := hun.injOn_and_extends
  obtain ⟨Z, hUZ, hZ⟩ := hext
  rw [Finset.image_id'] at hUZ
  refine ⟨Z, T₂, hZ, fun k hk => hUZ ?_, fun t ht => hUZ
    (Finset.mem_union_left _ (Finset.mem_union_left _ ht)), hT₂⟩
  by_cases hkP : k ∈ P
  · exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hk, hkP⟩))
  · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hk, hkP⟩)


namespace Subscheme

variable {A Y : Scheme.{u}}

/-- A morphism that is an isomorphism onto a closed subscheme `B` followed by `B ↪ Y` has surjective
stalk maps whose kernel is the stalk of the ideal of `B`. -/
theorem ker_stalkMap_eq_and_surjective_of_eq_iso_comp (f : A ⟶ Y) (B : Subscheme Y)
    (e : A ≅ B.toScheme) (hf : f = e.hom ≫ B.ι) (a : A) :
    RingHom.ker (f.stalkMap a).hom = B.stalkIdeal (f.base a) ∧
      Function.Surjective (f.stalkMap a).hom := by
  subst hf
  rw [Scheme.Hom.stalkMap_comp]
  have hker := stalkIdeal_eq_ker_stalkMap B (e.hom.base a)
  have hsurj := B.ι.stalkMap_surjective (e.hom.base a)
  have hbij : Function.Bijective (e.hom.stalkMap a).hom :=
    ConcreteCategory.bijective_of_isIso (C := CommRingCat) (e.hom.stalkMap a)
  refine ⟨?_, hbij.2.comp hsurj⟩
  change RingHom.ker (CommRingCat.Hom.hom (B.ι.stalkMap (e.hom.base a) ≫ e.hom.stalkMap a)) =
    B.stalkIdeal (B.ι.base (e.hom.base a))
  rw [hker, CommRingCat.hom_comp]
  ext r
  simp only [RingHom.mem_ker, RingHom.coe_comp, Function.comp_apply]
  rw [← map_zero (e.hom.stalkMap a).hom]
  exact hbij.1.eq_iff


/-- If a closed subscheme `B̃` of `X̃` maps isomorphically onto a closed subscheme `B` of `Y` through
`c̄ : X̃ → Y` (`e ≫ ι_B = ι_{B̃} ≫ c̄`), then at a point `b` of `B̃` the map of local rings
`O_{Y,x} → O_{X̃,ỹ}` induces an isomorphism `O_{Y,x}/B_x ≃ O_{X̃,ỹ}/B̃_ỹ`
(`ỹ = ι(b)`, `x = c̄(ỹ)`). -/
theorem exists_ringEquiv_quotient_stalkMap {X' : Scheme.{u}} (c : X' ⟶ Y) (B : Subscheme Y)
    (Bt : Subscheme X') (e : Bt.toScheme ≅ B.toScheme) (he : e.hom ≫ B.ι = Bt.ι ≫ c)
    (b : Bt.toScheme) :
    ∃ Θ : (Y.presheaf.stalk (c.base (Bt.ι.base b)) ⧸ B.stalkIdeal (c.base (Bt.ι.base b))) ≃+*
        (X'.presheaf.stalk (Bt.ι.base b) ⧸ Bt.stalkIdeal (Bt.ι.base b)),
      ∀ a, Θ (Ideal.Quotient.mk _ a) =
        Ideal.Quotient.mk _ ((c.stalkMap (Bt.ι.base b)).hom a) := by
  obtain ⟨hker, hsurj⟩ := ker_stalkMap_eq_and_surjective_of_eq_iso_comp (Bt.ι ≫ c) B e he.symm b
  have hcomp : (Bt.ι ≫ c).stalkMap b = c.stalkMap (Bt.ι.base b) ≫ Bt.ι.stalkMap b :=
    Scheme.Hom.stalkMap_comp _ _ _
  set ψ : Y.presheaf.stalk (c.base (Bt.ι.base b)) →+* Bt.toScheme.presheaf.stalk b :=
    ((Bt.ι ≫ c).stalkMap b).hom with hψ
  have hψφ : ∀ a, ψ a = (Bt.ι.stalkMap b).hom ((c.stalkMap (Bt.ι.base b)).hom a) := by
    intro a
    rw [hψ, hcomp]
    rfl
  have hker' : RingHom.ker ψ = B.stalkIdeal (c.base (Bt.ι.base b)) := hker
  have hker2 : RingHom.ker (Bt.ι.stalkMap b).hom = Bt.stalkIdeal (Bt.ι.base b) :=
    (stalkIdeal_eq_ker_stalkMap Bt b).symm
  let E₁ := RingHom.quotientKerEquivOfSurjective (f := ψ) hsurj
  let E₂ := RingHom.quotientKerEquivOfSurjective (f := (Bt.ι.stalkMap b).hom)
    (Bt.ι.stalkMap_surjective b)
  refine ⟨(Ideal.quotEquivOfEq hker'.symm).trans (E₁.trans
    (E₂.symm.trans (Ideal.quotEquivOfEq hker2))), fun a => ?_⟩
  have h1 : E₂.symm (E₁ (Ideal.Quotient.mk _ a)) =
      Ideal.Quotient.mk _ ((c.stalkMap (Bt.ι.base b)).hom a) := by
    rw [RingEquiv.symm_apply_eq]
    exact hψφ a
  simp only [RingEquiv.trans_apply, Ideal.quotEquivOfEq_mk]
  rw [h1, Ideal.quotEquivOfEq_mk]

end Subscheme

open Classical in
/-- The members of `K` outside `P` stay independent modulo `P` if their images generate, up to
units, distinct members of a regular system of parameters of a ring `R̃` outside the generators of
the ideal corresponding to `P` under an isomorphism `R/P ≃ R̃/(T̃)`. -/
theorem rsopIndep_quotient_of_associated_rsop {R R' : Type u} [CommRing R] [IsRegularLocalRing R]
    [CommRing R'] [IsRegularLocalRing R'] (φ : R →+* R') (P : Ideal R) [P.IsPrime]
    (hP : IsRegularLocalRing (R ⧸ P)) {Z Tb : Finset R'} (hZ : IsRegularSystemOfParameters R' Z)
    (hTb : Tb ⊆ Z) (Θ : (R ⧸ P) ≃+* (R' ⧸ Ideal.span (Tb : Set R')))
    (hΘ : ∀ a, Θ (Ideal.Quotient.mk P a) = Ideal.Quotient.mk _ (φ a)) (F : Finset R)
    (hFP : ∀ k ∈ F, k ∉ P) (β : R → R') (hβZ : ∀ k ∈ F, β k ∈ Z)
    (hβ : ∀ k ∈ F, Ideal.span {φ k} = Ideal.span {β k}) (hinj : Set.InjOn β F) :
    RSOPIndep F (fun k : R => Ideal.Quotient.mk P k) := by
  have hdom : IsDomain R' := Transforms.isDomain_of_isRegularLocalRing R'
  obtain ⟨hreg, hrs, hcard⟩ := rsop_quotient hZ hTb
  set mk' := Ideal.Quotient.mk (Ideal.span (Tb : Set R')) with hmk'
  have hinjZ : Set.InjOn mk' (Z \ Tb : Finset R') := Finset.injOn_of_card_image_eq hcard
  have hβT : ∀ k ∈ F, β k ∉ Tb := by
    intro k hk hmem
    have h1 : φ k ∈ Ideal.span (Tb : Set R') := by
      have : φ k ∈ Ideal.span {β k} := by
        rw [← hβ k hk]; exact Ideal.mem_span_singleton_self _
      exact Ideal.span_singleton_le_iff_mem _ |>.mpr (Ideal.subset_span (Finset.mem_coe.mpr hmem))
        this
    have h2 : Θ (Ideal.Quotient.mk P k) = 0 := by
      rw [hΘ]; exact Ideal.Quotient.eq_zero_iff_mem.mpr h1
    have h3 : Ideal.Quotient.mk P k = 0 := by
      have := congrArg Θ.symm h2
      simpa using this
    exact hFP k hk (Ideal.Quotient.eq_zero_iff_mem.mp h3)
  have hmem : ∀ k ∈ F, β k ∈ Z \ Tb := fun k hk =>
    Finset.mem_sdiff.mpr ⟨hβZ k hk, hβT k hk⟩
  -- independence of the classes of the `β k` in `R'/(Tb)`
  have hind : RSOPIndep F (fun k : R => mk' (β k)) := by
    refine RSOPIndep.of_extends (fun a ha b hb hab => hinj ha hb
      (hinjZ (hmem a ha) (hmem b hb) hab)) ?_
    have hsub : F.image (fun k => mk' (β k)) ⊆ (Z \ Tb).image mk' := by
      intro y hy
      obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hy
      exact Finset.mem_image_of_mem _ (hmem k hk)
    exact (ExtendsToRSOP.of_isRegularSystemOfParameters hrs).mono hsub
  -- associates
  have hassoc : ∀ k ∈ F, Associated (mk' (β k)) (mk' (φ k)) := by
    intro k hk
    have : Associated (β k) (φ k) :=
      (Ideal.span_singleton_eq_span_singleton.mp (hβ k hk).symm)
    exact this.map mk'
  have hind' : RSOPIndep F (fun k : R => mk' (φ k)) := hind.of_associated hassoc
  -- transport to `R/P`
  have := RSOPIndep.map_ringEquiv Θ.symm hind'
  have heq : (fun z : R => Θ.symm (mk' (φ z))) = fun z => Ideal.Quotient.mk P z :=
    funext fun z => by rw [← hΘ]; simp
  rwa [heq] at this



open Classical in
/-- The intersection of principal ideals generated by members of a part of a regular system of
parameters is generated by the product of the distinct generators (the generators being those
of the `D i` which are not the unit ideal). -/
theorem DatumTransform.exists_iInf_eq_span_prod_and_forall_mem {R : Type u} [CommRing R]
    [IsRegularLocalRing R] {ι : Type*} (D : ι → Ideal R) {K : Finset R} (hK : ExtendsToRSOP R K)
    (hD : ∀ i, D i = ⊤ ∨ ∃ k ∈ K, D i = Ideal.span {k}) :
    ∃ K₁ ⊆ K, (∀ k ∈ K₁, ∃ i, D i = Ideal.span {k}) ∧ ⨅ i, D i = Ideal.span {∏ k ∈ K₁, k} := by
  refine ⟨K.filter fun k => ∃ i, D i = Ideal.span {k}, Finset.filter_subset _ _,
    fun k hk => (Finset.mem_filter.mp hk).2, ?_⟩
  rw [← (hK.mono (Finset.filter_subset _ _)).iInf_span_singleton]
  apply le_antisymm
  · refine le_iInf₂ fun k hk => ?_
    obtain ⟨i, hi⟩ := (Finset.mem_filter.mp hk).2
    exact (iInf_le D i).trans hi.le
  · refine le_iInf fun i => ?_
    rcases hD i with h | ⟨k, hk, h⟩
    · rw [h]; exact le_top
    · rw [h]; exact iInf₂_le k (Finset.mem_filter.mpr ⟨hk, i, h⟩)

/-! ### Pointwise steps of the induction along a succession (Remark 2 of §3 for removal families) -/

section PrepLemmaFourPointwise'

open IsLocalRing Classical

variable {X : Scheme.{u}}

/-- Pointwise form of `MonoidalTransformation.exists_extendsToRSOP_stalkIdeal_of_hasOnlyNormalCrossingsWithAt`:
only the stalkwise containment `W_{f(y)} ≤ B_{f(y)}` at the point is used (not `B ⊆ W` globally). -/

theorem MonoidalTransformation.exists_extendsToRSOP_stalkIdeal_of_stalkIdeal_le
    (hX : X.IsNonsingular) {B W E : Subscheme X} (hBns : B.IsNonsingular)
    (hEred : E.IsReduced) (t : MonoidalTransformation X B)
    {y : t.X'} (hQP : W.stalkIdeal (t.f y) ≤ B.stalkIdeal (t.f y)) (hEW : E.HasOnlyNormalCrossingsWithAt W (t.f y))
    (hEB : E.HasOnlyNormalCrossingsWithAt B (t.f y))
    (hy : y ∈ (Subscheme.strictTransform t W).pts) :
    ∃ K : Finset (t.X'.presheaf.stalk y), ExtendsToRSOP _ K ∧
      (∃ K₁ ⊆ K, ((Subscheme.strictTransform t E).union t.exceptional).stalkIdeal y =
        Ideal.span {∏ k ∈ K₁, k}) ∧
      (∃ T ⊆ K, (Subscheme.strictTransform t W).stalkIdeal y =
        Ideal.span (T : Set (t.X'.presheaf.stalk y))) := by
  have : IsRegularLocalRing (t.X'.presheaf.stalk y) := t.isRegularLocalRing_stalk hX hBns y
  have : IsRegularLocalRing (X.presheaf.stalk (t.f y)) := hX _
  obtain ⟨ZW, hZW, ⟨JW, hJWZ, hEJW⟩, ⟨tW, htWZ, hWt⟩⟩ :=
    (Subscheme.hasOnlyNormalCrossingsWithAt_iff hEred (hX _)).mp hEW
  obtain ⟨ZB, hZB, ⟨JB, hJBZ, hEJB⟩, ⟨tB, htBZ, hBt⟩⟩ :=
    (Subscheme.hasOnlyNormalCrossingsWithAt_iff hEred (hX _)).mp hEB
  have hassoc : ∀ c ∈ JB, ∃ a ∈ ZW, Ideal.span {c} = Ideal.span {a} := by
    intro c hc
    have hext := (ExtendsToRSOP.of_isRegularSystemOfParameters hZB).mono hJBZ
    have hp := hext.isPrime_span_singleton hc
    have hp1 := DatumTransform.height_span_singleton_of_mem hext hc
    have hle : Ideal.span {∏ z ∈ JW, z} ≤ Ideal.span {c} := by
      rw [← hEJW, hEJB, ← hext.iInf_span_singleton]; exact iInf₂_le c hc
    obtain ⟨a, haJ, hca⟩ := DatumTransform.eq_span_of_prod_le hZW hJWZ hp1 hle
    exact ⟨a, hJWZ haJ, hca⟩
  obtain ⟨Z, hZ, hCZ, tP, htPZ, hPt, tQ, htQ, hQt⟩ :=
    exists_rsop_adapted_to_flag (W.stalkIdeal (t.f y)) (B.stalkIdeal (t.f y)) hQP ZB tB ZW tW JB
      hZB htBZ hBt hZW htWZ hWt hJBZ (fun c hc _ => hassoc c hc)
  obtain ⟨zt, φ, hzt, hexc, hztm, -, hrel, hinj, hext, hstP, hstS⟩ :=
    t.exists_chart_strictTransform_stalkIdeal hX y hZ htPZ hPt
  -- the strict transform of `W`
  have h1 := hstS tQ htQ W hQt
  have hne : (Subscheme.strictTransform t W).stalkIdeal y ≠ ⊤ :=
    Subscheme.mem_pts_iff_stalkIdeal_ne_top.mp hy
  rw [h1] at hne
  have hztQ : zt ∉ tQ := fun h => hne (by simp [h])
  simp only [hztQ, ↓reduceIte] at h1 hne
  have hnu : ∀ q ∈ tQ, φ q ∈ maximalIdeal (t.X'.presheaf.stalk y) := by
    intro q hq; by_contra h
    exact hne (Ideal.eq_top_of_isUnit_mem _ (Ideal.subset_span ⟨q, hq, rfl⟩)
      ((IsLocalRing.mem_maximalIdeal _).not.mp h |> not_not.mp))
  -- the strict transform of `E`
  have hE' := hstP JB hCZ E hEJB
  have hsubK : ∀ z ∈ (JB.erase zt).filter (fun z => φ z ∈ maximalIdeal (t.X'.presheaf.stalk y)),
      z ∈ Z ∧ φ z ∈ maximalIdeal (t.X'.presheaf.stalk y) := fun z hz =>
    ⟨hCZ (Finset.mem_of_mem_erase (Finset.mem_filter.mp hz).1), (Finset.mem_filter.mp hz).2⟩
  set K₁' := ((JB.erase zt).filter
    (fun z => φ z ∈ maximalIdeal (t.X'.presheaf.stalk y))).image φ with hK₁'
  have hK₁'K : K₁' ⊆ (Z.filter fun z => φ z ∈ maximalIdeal (t.X'.presheaf.stalk y)).image φ := by
    intro a ha
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp ha
    exact Finset.mem_image_of_mem φ (Finset.mem_filter.mpr (hsubK z hz))
  have hztK : φ zt ∈ (Z.filter fun z => φ z ∈ maximalIdeal (t.X'.presheaf.stalk y)).image φ :=
    Finset.mem_image_of_mem φ (Finset.mem_filter.mpr ⟨htPZ hzt, hztm⟩)
  have hE'prod : (Subscheme.strictTransform t E).stalkIdeal y = Ideal.span {∏ k ∈ K₁', k} := by
    rw [hE', hK₁', ← DatumTransform.prod_image_eq φ hinj _ hsubK]
  refine ⟨_, hext, ⟨K₁' ∪ {φ zt}, Finset.union_subset hK₁'K (Finset.singleton_subset_iff.mpr hztK),
    ?_⟩, ⟨tQ.image φ, ?_, ?_⟩⟩
  · show ((Subscheme.strictTransform t E) ⊓ t.exceptional).stalkIdeal y = _
    have hexc' : t.exceptional.stalkIdeal y = Ideal.span {∏ k ∈ ({φ zt} : Finset _), k} := by
      rw [hexc, Finset.prod_singleton]
    rw [Subscheme.stalkIdeal_inf_eq, hE'prod, hexc',
      DatumTransform.span_prod_inf_of_subset hext hK₁'K (Finset.singleton_subset_iff.mpr hztK)]
  · intro a ha
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp ha
    exact Finset.mem_image_of_mem φ (Finset.mem_filter.mpr ⟨htPZ (htQ hq), hnu q hq⟩)
  · rw [h1, Finset.coe_image]

end PrepLemmaFourPointwise'

namespace DatumTransform

variable {X : Scheme.{u}} {B : Subscheme X}

open Classical in
/-- **One step of the induction of Lemma 4 of §2, stalk presentations** (pp. 308, 321): if the
stalks of the boundary `E` are `(∏ K)` for parts `K` of regular systems of parameters and `E` has
only normal crossings with the non-singular center `B`, then the stalks of the boundary
`E' ∪ E_exc` of the transform have the same form. -/
theorem exists_stalk_presentation_strictTransform_inf_exceptional (hX : X.IsNonsingular)
    (hBns : B.IsNonsingular) {E : Subscheme X}
    (hE : ∀ y, ∃ K : Finset (X.presheaf.stalk y), ExtendsToRSOP _ K ∧
      E.stalkIdeal y = Ideal.span {∏ k ∈ K, k})
    (hEB : ∀ x ∈ B.pts, E.HasOnlyNormalCrossingsWithAt B x) (t : MonoidalTransformation X B)
    (y : t.X') : ∃ K : Finset (t.X'.presheaf.stalk y), ExtendsToRSOP _ K ∧
      ((Subscheme.strictTransform t E) ⊓ t.exceptional).stalkIdeal y =
        Ideal.span {∏ k ∈ K, k} := by
  have hX' : t.X'.IsNonsingular := (t.isNonsingular_and_isNonsingular_exceptional hX hBns).1
  have hEred : E.IsReduced := isReduced_of_forall_stalk hX hE
  have : IsRegularLocalRing (t.X'.presheaf.stalk y) := hX' y
  have : IsRegularLocalRing (X.presheaf.stalk (t.f.base y)) := hX _
  obtain ⟨Z, hZ, J, hJZ, hEJ, hBZ⟩ : ∃ Z : Finset (X.presheaf.stalk (t.f.base y)),
      IsRegularSystemOfParameters _ Z ∧ ∃ J ⊆ Z,
        E.stalkIdeal (t.f.base y) = Ideal.span {∏ z ∈ J, z} ∧
        (t.f.base y ∈ B.pts → ∃ T ⊆ Z, B.stalkIdeal (t.f.base y) = Ideal.span (T : Set _)) := by
    by_cases hy : t.f.base y ∈ B.pts
    · obtain ⟨Z, hZ, ⟨J, hJZ, hEJ⟩, ⟨T, hTZ, hBT⟩⟩ :=
        (Subscheme.hasOnlyNormalCrossingsWithAt_iff hEred (hX _)).mp (hEB _ hy)
      exact ⟨Z, hZ, J, hJZ, hEJ, fun _ => ⟨T, hTZ, hBT⟩⟩
    · obtain ⟨K, ⟨Z, hKZ, hZ⟩, hK⟩ := hE (t.f.base y)
      exact ⟨Z, hZ, K, hKZ, hK, fun h => absurd h hy⟩
  obtain ⟨K, hK, ⟨K₀, hK₀, -, hexc⟩, hst⟩ := exists_stalk_transform hX hBns t y hZ hBZ
  obtain ⟨K₁, hK₁, -, hstE⟩ := hst J hJZ E hEJ
  refine ⟨K₁ ∪ K₀, hK.mono (Finset.union_subset hK₁ hK₀), ?_⟩
  rw [Subscheme.stalkIdeal_inf_eq, hstE, hexc, span_prod_inf_of_subset hK hK₁ hK₀]

open Classical in
/-- **One step of the induction of Lemma 4 of §2, normal crossings with the strict transform** at
a point `y` of `W'`, where only the stalkwise containment `W_x ≤ B_x` is needed at the point
`x = f(y)` of the center (not `B ⊆ W` globally). -/
theorem hasOnlyNormalCrossingsWithAt_strictTransform_inf_exceptional (hX : X.IsNonsingular)
    (hBns : B.IsNonsingular) {E W : Subscheme X}
    (hE : ∀ y, ∃ K : Finset (X.presheaf.stalk y), ExtendsToRSOP _ K ∧
      E.stalkIdeal y = Ideal.span {∏ k ∈ K, k})
    (t : MonoidalTransformation X B) {y : t.X'} (hy : y ∈ (Subscheme.strictTransform t W).pts)
    (hEW : E.HasOnlyNormalCrossingsWithAt W (t.f.base y))
    (hEB : t.f.base y ∈ B.pts → E.HasOnlyNormalCrossingsWithAt B (t.f.base y))
    (hWB : t.f.base y ∈ B.pts → W.stalkIdeal (t.f.base y) ≤ B.stalkIdeal (t.f.base y)) :
    ((Subscheme.strictTransform t E) ⊓ t.exceptional).HasOnlyNormalCrossingsWithAt
      (Subscheme.strictTransform t W) y := by
  have hX' : t.X'.IsNonsingular := (t.isNonsingular_and_isNonsingular_exceptional hX hBns).1
  have hEred : E.IsReduced := isReduced_of_forall_stalk hX hE
  have : IsRegularLocalRing (t.X'.presheaf.stalk y) := hX' y
  by_cases hyB : t.f.base y ∈ B.pts
  · obtain ⟨K, ⟨Z', hKZ', hZ'⟩, ⟨K₁, hK₁, hD⟩, ⟨T, hT, hW⟩⟩ :=
      t.exists_extendsToRSOP_stalkIdeal_of_stalkIdeal_le hX hBns hEred (hWB hyB) hEW (hEB hyB) hy
    exact Subscheme.hasOnlyNormalCrossingsWithAt_of_stalkIdeal_eq hZ' (hK₁.trans hKZ')
      (hT.trans hKZ') hD hW
  · have : IsRegularLocalRing (X.presheaf.stalk (t.f.base y)) := hX _
    obtain ⟨e, hexc, hst⟩ := exists_offCenter hX t y hyB
    obtain ⟨z, hz, ⟨J, hJz, hEJ⟩, ⟨T, hTz, hWT⟩⟩ :=
      (Subscheme.hasOnlyNormalCrossingsWithAt_iff hEred (hX _)).mp hEW
    refine Subscheme.hasOnlyNormalCrossingsWithAt_of_stalkIdeal_eq
      (isRegularSystemOfParameters_image_ringEquiv e hz) (J := J.image e) (T := T.image e)
      (Finset.image_subset_image hJz) (Finset.image_subset_image hTz) ?_ ?_
    · rw [Subscheme.stalkIdeal_inf_eq, hexc, inf_top_eq, hst, hEJ, map_span_prod]
    · rw [hst, hWT, Ideal.map_span, Finset.coe_image]

end DatumTransform

namespace DatumTransform

variable {X : Scheme.{u}} {B : Subscheme X}

/-- The divisors `E_1', …, E_α', E_{α+1}'` of the transform of a family of non-singular irreducible
divisors with only normal crossings along a center `B` having only normal crossings with them
(Definition 7, p. 168, and Remark 1, p. 169): the strict transforms and the exceptional divisor are
again non-singular irreducible divisors, and their union has only normal crossings. -/
theorem isNonsingularIrreducibleCodimOne_and_hasOnlyNormalCrossings_snoc_transform
    [IsAlgebraicScheme X] {α : ℕ} (E : Fin α → Subscheme X) (hX : X.IsNonsingular)
    (hE : ∀ i, (E i).IsNonsingularIrreducibleCodimOne) (hNC : (⨅ i, E i).HasOnlyNormalCrossings)
    (hB : B.IsCenter) (hNCB : (⨅ i, E i).HasOnlyNormalCrossingsWith B)
    (t : MonoidalTransformation X B) :
    (∀ j, (Fin.snoc (α := fun _ => Subscheme t.X')
      (fun i => Subscheme.strictTransform t (E i)) t.exceptional j).IsNonsingularIrreducibleCodimOne) ∧
    (⨅ j, Fin.snoc (α := fun _ => Subscheme t.X')
      (fun i => Subscheme.strictTransform t (E i)) t.exceptional j).HasOnlyNormalCrossings := by
  classical
  have hBns := hB.isNonsingular
  have hX' := (t.isNonsingular_and_isNonsingular_exceptional hX hBns).1
  have hdata := exists_rsop_adapted_of_isDatum E hX hE hNC hNCB
  have hmem : ∀ y, ∃ K : Finset (t.X'.presheaf.stalk y), ExtendsToRSOP _ K ∧
      ∀ j, ∃ K₀ ⊆ K, K₀.card ≤ 1 ∧
        (Fin.snoc (α := fun _ => Subscheme t.X')
          (fun i => Subscheme.strictTransform t (E i)) t.exceptional j).stalkIdeal y =
          Ideal.span {∏ k ∈ K₀, k} := by
    intro y
    obtain ⟨K, hK, hexc, hst⟩ := exists_extendsToRSOP_stalkIdeal_family hX hBns t E hdata y
    refine ⟨K, hK, fun j => ?_⟩
    refine Fin.lastCases ?_ (fun i => ?_) j
    · simp only [Fin.snoc_last]; exact hexc
    · simp only [Fin.snoc_castSucc]; exact hst i
  refine ⟨fun j => ?_, ?_⟩
  · apply isNonsingularIrreducibleCodimOne_of_forall_stalk hX'
    · refine Fin.lastCases ?_ (fun i => ?_) j
      · simp only [Fin.snoc_last]
        intro hne
        rcases hB with hBe | ⟨-, hBirr⟩
        · exfalso
          obtain ⟨y, hy⟩ := hne
          have h3 : B.pts = ∅ := by rw [hBe]; exact pts_empty
          rw [MonoidalTransformation.pts_exceptional] at hy
          have h4 : t.f y ∈ B.pts := hy
          rw [h3] at h4
          exact h4
        · exact exceptional_isIrreducible hX hBns hBirr t hne
      · simp only [Fin.snoc_castSucc]
        exact strictTransform_isIrreducible_of_nonempty t (hE i)
    · intro y
      obtain ⟨K, hK, h⟩ := hmem y
      obtain ⟨K₀, h1, h2, h3⟩ := h j
      exact stalkIdeal_eq_top_or_exists_of_card_le_one hK h1 h2 h3
  · have hU : ∀ y, ∃ K : Finset (t.X'.presheaf.stalk y), ExtendsToRSOP _ K ∧
        (⨅ j, Fin.snoc (α := fun _ => Subscheme t.X')
          (fun i => Subscheme.strictTransform t (E i)) t.exceptional j).stalkIdeal y =
          Ideal.span {∏ k ∈ K, k} := by
      intro y
      have : IsRegularLocalRing (t.X'.presheaf.stalk y) := hX' y
      obtain ⟨K, hK, h⟩ := hmem y
      choose L hL _ hLe using h
      refine ⟨Finset.univ.biUnion L, hK.mono (Finset.biUnion_subset.mpr fun i _ => hL i), ?_⟩
      rw [stalkIdeal_iInf_fintype, ← iInf_span_prod_of_subset hK L hL]
      exact iInf_congr hLe
    exact hasOnlyNormalCrossings_of_forall_stalk hX' (isReduced_of_forall_stalk hX' hU) hU

end DatumTransform


/-- The union `E_1 ∪ ⋯ ∪ E_α` of a family of non-singular irreducible divisors has only normal
crossings with a closed restriction `F` if `E_1 ∪ ⋯ ∪ E_α ∪ F` has only normal crossings
(Definition 5 (I.1), (II.1)). -/
theorem hasOnlyNormalCrossingsWith_iInf_of_isClosedRestriction {X : Scheme.{u}}
    (hX : X.IsNonsingular) {α : ℕ} (E : Fin α → Subscheme X)
    (hE : ∀ i, (E i).IsNonsingularIrreducibleCodimOne) {F : Subscheme X}
    (hF : F.IsNonsingularIrreducibleCodimOne)
    (hEF : ((⨅ i, E i).union F).HasOnlyNormalCrossings) : (⨅ i, E i).HasOnlyNormalCrossingsWith F := by
  classical
  intro x hx
  have : IsRegularLocalRing (X.presheaf.stalk x) := hX x
  have hG : ∀ o : Option (Fin α), (o.elim F E).IsNonsingularIrreducibleCodimOne := by
    rintro (_ | i)
    exacts [hF, hE i]
  have hGle : ∀ o : Option (Fin α), ((⨅ i, E i).union F) ≤ o.elim F E := by
    rintro (_ | i)
    · exact inf_le_right
    · exact inf_le_left.trans (iInf_le _ i)
  obtain ⟨Z, hZ, -, hG'⟩ := DatumTransform.exists_rsop_of_hasOnlyNormalCrossingsWithAt _ hG hGle
    (D := ⊥) (hEF x)
  obtain ⟨f, hfZ, hFf⟩ := (hG' none).resolve_left (Subscheme.mem_pts_iff_stalkIdeal_ne_top.mp hx)
  obtain ⟨K, hKZ, hK⟩ := DatumTransform.iInf_eq_span_prod (fun i => (E i).stalkIdeal x)
    ⟨Z, subset_rfl, hZ⟩ (fun i => hG' (some i))
  refine Subscheme.hasOnlyNormalCrossingsWithAt_of_stalkIdeal_eq hZ hKZ
    (T := {f}) (by simpa using hfZ) ?_ (by simpa using hFf)
  rw [DatumTransform.stalkIdeal_iInf_fintype]
  exact hK


namespace MonoidalTransformation

variable {Y : Scheme.{u}} {B : Subscheme Y}

/-- The points of the strict transform of a subscheme whose points are a finite union. -/
theorem pts_strictTransform_of_pts_eq_iUnion (t : MonoidalTransformation Y B) {m : ℕ}
    {V₀ : Subscheme Y} {V : Fin m → Subscheme Y} (h : V₀.pts = ⋃ i, (V i).pts) :
    (Subscheme.strictTransform t V₀).pts = ⋃ i, (Subscheme.strictTransform t (V i)).pts := by
  rw [pts_strictTransform_eq_closure, h]
  have h1 : (t.f.base ⁻¹' (⋃ i, (V i).pts)) \ t.exceptional.pts =
      ⋃ i, ((t.f.base ⁻¹' (V i).pts) \ t.exceptional.pts) := by
    ext y; simp only [Set.mem_sdiff, Set.mem_preimage, Set.mem_iUnion]; tauto
  rw [h1, closure_iUnion_of_finite]
  simp only [pts_strictTransform_eq_closure]

/-- If `V ⊆ B` then the strict transform of `V` is empty (p. 167: the strict transform is the
closure of `f⁻¹(V ∖ B)`). -/
theorem pts_strictTransform_eq_empty_of_subset (t : MonoidalTransformation Y B) (V : Subscheme Y)
    (h : V.pts ⊆ B.pts) : (Subscheme.strictTransform t V).pts = ∅ := by
  refine Set.eq_empty_iff_forall_notMem.mpr fun p hp => ?_
  obtain ⟨q, hq, hqE, -⟩ := t.exists_generization_notMem_exceptional V hp
  apply hqE
  rw [t.pts_exceptional]
  exact h (t.pts_strictTransform_subset V hq)

open Classical in
/-- **`W' ⊄ E'`**: if `W` is irreducible, `W ⊄ E` and `W ⊄ B`, then the strict transform of `W`
is not contained in `E' ∪ E_exc` (a point of `W − (E ∪ B)` lifts to `W'` off the exceptional
divisor). -/
theorem not_pts_strictTransform_subset_strictTransform_inf_exceptional
    (t : MonoidalTransformation Y B) {W E : Subscheme Y} (hirr : _root_.IsIrreducible W.pts)
    (hWE : ¬ W.pts ⊆ E.pts) (hWB : ¬ W.pts ⊆ B.pts) :
    ¬ (Subscheme.strictTransform t W).pts ⊆
      (Subscheme.strictTransform t E ⊓ t.exceptional).pts := by
  obtain ⟨w, hwW, hwE⟩ := Set.not_subset.mp hWE
  obtain ⟨w', hw'W, hw'⟩ := hirr.2 (E.pts)ᶜ (B.pts)ᶜ E.support.isClosed.isOpen_compl
    B.support.isClosed.isOpen_compl ⟨w, hwW, hwE⟩
    (let ⟨b, hb, hbB⟩ := Set.not_subset.mp hWB; ⟨b, hb, hbB⟩)
  obtain ⟨Z, ι, j', -, -, -, -, -, hcomp, hrι, hrange, -, -⟩ :=
    Hironaka.DatumTransform.exists_flat_isPreimmersion_off_center t
  obtain ⟨v, hv⟩ : w' ∈ Set.range ι.base := by rw [hrι]; exact hw'.2
  have hzE : j'.base v ∉ t.exceptional.pts := by
    have : j'.base v ∈ Set.range j'.base := ⟨v, rfl⟩
    rwa [hrange] at this
  have hf : t.f.base (j'.base v) = w' := by rw [hcomp]; exact hv
  intro hsub
  have hmem : j'.base v ∈ (Subscheme.strictTransform t W).pts := by
    rw [MonoidalTransformation.mem_pts_strictTransform_iff_of_notMem t _ hzE, hf]
    exact hw'W
  have := hsub hmem
  rw [Subscheme.pts_inf] at this
  rcases this with h | h
  · rw [MonoidalTransformation.mem_pts_strictTransform_iff_of_notMem t _ hzE, hf] at h
    exact hw'.1 h
  · exact hzE h

end MonoidalTransformation

/-- A ring map of regular local rings that maps a regular system of parameters to part of one
(`RingHom.MapsRSOP`) is faithfully flat, so it reflects inclusions of ideals: `J R' ≤ P R'` implies
`J ≤ P`.  (Used for `X̄_0 ⊄ Ê_i(0)` in the closed case of Remark 2, p. 308: if `V(z_0) = c_0⁻¹(F)`
lay in `c_0⁻¹(E_i)` then `F ⊆ E_i` near `x_0`.) -/
theorem RingHom.MapsRSOP.le_of_map_le_map {R R' : Type u} [CommRing R] [IsRegularLocalRing R]
    [CommRing R'] [IsRegularLocalRing R'] {α : R →+* R'} [IsLocalHom α]
    (hα : RingHom.MapsRSOP α) {J P : Ideal R} (h : J.map α ≤ P.map α) : J ≤ P := by
  let _ : Algebra R R' := α.toAlgebra
  have _ : IsLocalHom (algebraMap R R') := ‹IsLocalHom α›
  have _ : Module.Flat R R' := hα.flat
  have _ : Module.FaithfullyFlat R R' := Module.FaithfullyFlat.of_flat_of_isLocalHom
  calc J ≤ (J.map (algebraMap R R')).comap (algebraMap R R') := Ideal.le_comap_map
    _ ≤ (P.map (algebraMap R R')).comap (algebraMap R R') := Ideal.comap_mono h
    _ = P := Ideal.comap_map_eq_self_of_faithfullyFlat P


namespace DatumTransform

variable {X : Scheme.{u}} {B : Subscheme X}

/-- `DatumTransform.exists_rsop_of_hasOnlyNormalCrossingsWithAt` for non-singular divisors
(everywhere of codimension one, not necessarily irreducible): the irreducibility is not needed to
see that the stalk of `E_i` at `x` is generated by a member of a regular system of parameters. -/
theorem exists_rsop_of_hasOnlyNormalCrossingsWithAt_of_isNonsingularDivisor {ι : Type*}
    (E : ι → Subscheme X) (hE : ∀ i, (E i).IsNonsingularDivisor) {D₀ : Subscheme X}
    (hD₀ : ∀ i, D₀ ≤ E i) {D : Subscheme X} {x : X} [IsRegularLocalRing (X.presheaf.stalk x)]
    (h : D₀.HasOnlyNormalCrossingsWithAt D x) :
    ∃ Z : Finset (X.presheaf.stalk x), IsRegularSystemOfParameters _ Z ∧
      (∃ T ⊆ Z, D.stalkIdeal x = Ideal.span (T : Set (X.presheaf.stalk x))) ∧
      ∀ i, (E i).stalkIdeal x = ⊤ ∨ ∃ a ∈ Z, (E i).stalkIdeal x = Ideal.span {a} :=
  Subscheme.exists_rsop_of_hasOnlyNormalCrossingsWithAt_of_isSimpleAt E hD₀
    (fun i hx => ⟨⟨hx, Subscheme.isRegular_stalk_quot _ (hE i).1 hx⟩, (hE i).2 _ hx⟩) h

/-- `DatumTransform.exists_rsop_adapted_of_isDatum` for non-singular divisors (not necessarily
irreducible). -/
theorem exists_rsop_adapted_of_isNonsingularDivisor {α : ℕ} (E : Fin α → Subscheme X)
    (hX : X.IsNonsingular) (hE : ∀ i, (E i).IsNonsingularDivisor)
    (hNC : (⨅ i, E i).HasOnlyNormalCrossings) (hNCB : (⨅ i, E i).HasOnlyNormalCrossingsWith B)
    (x : X) : ∃ Z : Finset (X.presheaf.stalk x), IsRegularSystemOfParameters _ Z ∧
      (x ∈ B.pts → ∃ T ⊆ Z, B.stalkIdeal x = Ideal.span (T : Set _)) ∧
      ∀ i, (E i).stalkIdeal x = ⊤ ∨ ∃ a ∈ Z, (E i).stalkIdeal x = Ideal.span {a} := by
  have : IsRegularLocalRing (X.presheaf.stalk x) := hX x
  by_cases hx : x ∈ B.pts
  · obtain ⟨Z, hZ, hT, hE'⟩ := exists_rsop_of_hasOnlyNormalCrossingsWithAt_of_isNonsingularDivisor
      E hE (fun i => iInf_le _ i) (hNCB _ hx)
    exact ⟨Z, hZ, fun _ => hT, hE'⟩
  · obtain ⟨Z, hZ, -, hE'⟩ := exists_rsop_of_hasOnlyNormalCrossingsWithAt_of_isNonsingularDivisor
      E hE (fun i => iInf_le _ i) (D := ⊥) (hNC x)
    exact ⟨Z, hZ, fun h => absurd h hx, hE'⟩

end DatumTransform

namespace DatumTransform

variable {X : Scheme.{u}} {B : Subscheme X}

open Classical in
/-- **The total transform of a divisor given by a regular parameter** (the chart computation of
p. 169 in the form used for Remarks 1–3 of §4, pp. 321–326): if `V` has stalk `(z)` at `x = f(y)`
with `z` a member of a regular system of parameters `Z` adapted to `B` (`T ⊆ Z` generating the
stalk of `B`), then `f⁻¹(V)_y` is the product of the strict transform and the `m`-th power of the
exceptional ideal, `m = 1` if `z ∈ T` (`B ⊆ V` near `x`) and `m = 0` otherwise. -/
theorem stalkIdeal_totalTransform_eq_strict_mul_exceptional_pow (hX : X.IsNonsingular)
    (t : MonoidalTransformation X B) (y : t.X') [IsRegularLocalRing (t.X'.presheaf.stalk y)]
    {Z T : Finset (X.presheaf.stalk (t.f y))} (hZ : IsRegularSystemOfParameters _ Z) (hTZ : T ⊆ Z)
    (hBT : B.stalkIdeal (t.f y) = Ideal.span (T : Set _)) {z : X.presheaf.stalk (t.f y)} (hz : z ∈ Z)
    (V : Subscheme X) (hV : V.stalkIdeal (t.f y) = Ideal.span {z}) :
    (Subscheme.totalTransform t.f V).stalkIdeal y =
      (Subscheme.strictTransform t V).stalkIdeal y *
        (t.exceptional.stalkIdeal y) ^ (if z ∈ T then 1 else 0) := by
  classical
  have : IsRegularLocalRing (X.presheaf.stalk (t.f y)) := hX _
  have := isDomain_of_isRegularLocalRing (X.presheaf.stalk (t.f y))
  obtain ⟨s, e, he⟩ := t.exists_monoidalTransform_stalk y
  have : IsRegularLocalRing s.ring := IsRegularLocalRing.of_ringEquiv e.symm
  obtain ⟨zt, φ, hzt, hspan, hφ₁, hφ₂, hφ₃, hinj, hext⟩ :=
    MonoidalTransform.exists_rsop_transform s hZ hTZ hBT.symm
  have hm := Hironaka.DatumTransform.mem_maximalIdeal_ringEquiv e
  have htot := t.stalkIdeal_totalTransform_eq_map y s e he
  have hexc : t.exceptional.stalkIdeal y = (Ideal.span {s.toRing zt}).map e := by
    rw [MonoidalTransformation.exceptional, htot, ← hspan]
  have hfilt : ∀ K : Finset (X.presheaf.stalk (t.f y)),
      (K.filter fun z => e (φ z) ∈ maximalIdeal (t.X'.presheaf.stalk y)) =
        K.filter fun z => φ z ∈ maximalIdeal s.ring :=
    fun K => Finset.filter_congr fun z _ => hm (φ z)
  have hsat := MonoidalTransform.saturation_span_prod s hZ hTZ hBT.symm
    (J := {z}) (Finset.singleton_subset_iff.mpr hz) hzt hspan hφ₁ hφ₂ hφ₃ hinj hext
  have hstrict : (Subscheme.strictTransform t V).stalkIdeal y =
      Ideal.span {(∏ z' ∈ (({z} : Finset (X.presheaf.stalk (t.f y))).erase zt).filter
        (fun z' => e (φ z') ∈ maximalIdeal (t.X'.presheaf.stalk y)), e (φ z'))} := by
    rw [Subscheme.strictTransform_stalkIdeal, hexc, htot, hV]
    rw [hfilt, ← map_prod e]
    have h2 : Ideal.span {e (∏ z' ∈ (({z} : Finset (X.presheaf.stalk (t.f y))).erase zt).filter
        (fun z' => φ z' ∈ maximalIdeal s.ring), φ z')} =
        (Ideal.span {(∏ z' ∈ (({z} : Finset (X.presheaf.stalk (t.f y))).erase zt).filter
        (fun z' => φ z' ∈ maximalIdeal s.ring), φ z')}).map e := by
      rw [Ideal.map_span, Set.image_singleton]
    rw [h2, ← hsat, Ideal.map_iSup]
    refine iSup_congr fun n => ?_
    rw [Ideal.map_colon_ringEquiv, Ideal.map_pow, Ideal.map_span s.toRing, Set.image_singleton]
    simp
  have hV' : (Subscheme.totalTransform t.f V).stalkIdeal y = Ideal.span {e (s.toRing z)} := by
    rw [htot, hV, Ideal.map_span, Set.image_singleton, Ideal.map_span, Set.image_singleton]
  -- a non-member of the maximal ideal gives the unit ideal
  have hunit : ∀ w : s.ring, w ∉ maximalIdeal s.ring → Ideal.span {e w} = ⊤ := fun w hw => by
    rw [Ideal.span_singleton_eq_top]
    exact (isUnit_map_iff e w).mpr (by simpa [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] using hw)
  have hexc' : t.exceptional.stalkIdeal y = Ideal.span {e (s.toRing zt)} := by
    rw [hexc, Ideal.map_span, Set.image_singleton]
  by_cases hzz : z = zt
  · subst hzz
    have hzT : z ∈ T := hzt
    rw [ite_eq_left hzT, pow_one, hV', hexc', hstrict]
    simp
  · have hs : (Subscheme.strictTransform t V).stalkIdeal y = Ideal.span {e (φ z)} := by
      rw [hstrict, Finset.erase_eq_of_notMem (by simp [Ne.symm hzz]), Finset.filter_singleton]
      by_cases hp : e (φ z) ∈ maximalIdeal (t.X'.presheaf.stalk y)
      · rw [ite_eq_left hp, Finset.prod_singleton]
      · rw [ite_eq_right hp, Finset.prod_empty, Ideal.span_singleton_one]
        have : φ z ∉ maximalIdeal s.ring := fun h => hp ((hm _).mpr h)
        exact (hunit _ this).symm
    by_cases hzT : z ∈ T
    · rw [ite_eq_left hzT, pow_one, hV', hexc', hs, ← hφ₃ z hzT hzz, map_mul,
        Ideal.span_singleton_mul_span_singleton, mul_comm]
    · rw [ite_eq_right hzT, pow_zero, mul_one, hV', hs, hφ₁ z hz hzT]

open Classical in
/-- Family form of `stalkIdeal_totalTransform_eq_strict_mul_exceptional_pow`: for the members `E_i`
of a type II datum (with non-singular divisors `E_i`, not necessarily irreducible) whose union has
only normal crossings with the permissible center `B`, `f⁻¹(E_i)_y = (E_i)'_y · P_y^m` with `m = 1`
if `E_i ⊇ B` at `f(y)` and `m = 0` otherwise. -/
theorem stalkIdeal_totalTransform_eq_strict_mul_exceptional_pow_of_isNonsingularDivisor {α : ℕ}
    (E : Fin α → Subscheme X) (hX : X.IsNonsingular)
    (hE : ∀ i, (E i).IsNonsingularDivisor) (hNC : (⨅ i, E i).HasOnlyNormalCrossings)
    (hNCB : (⨅ i, E i).HasOnlyNormalCrossingsWith B) (t : MonoidalTransformation X B) (i : Fin α)
    (y : t.X') [IsRegularLocalRing (t.X'.presheaf.stalk y)] :
    (Subscheme.totalTransform t.f (E i)).stalkIdeal y =
      (Subscheme.strictTransform t (E i)).stalkIdeal y *
        (t.exceptional.stalkIdeal y) ^
          (if (E i).stalkIdeal (t.f y) ≤ B.stalkIdeal (t.f y) then 1 else 0) := by
  have : IsRegularLocalRing (X.presheaf.stalk (t.f y)) := hX _
  by_cases hB : t.f y ∈ B.pts
  · obtain ⟨Z, hZ, hBZ, hEZ⟩ := exists_rsop_adapted_of_isNonsingularDivisor (B := B) E hX
      hE hNC hNCB (t.f y)
    obtain ⟨T, hTZ, hT⟩ := hBZ hB
    rcases hEZ i with h | ⟨a, ha, h⟩
    · have hnle : ¬ (E i).stalkIdeal (t.f y) ≤ B.stalkIdeal (t.f y) := by
        rw [h]
        intro hle
        exact Subscheme.mem_pts_iff_stalkIdeal_ne_top.mp hB (top_le_iff.mp hle)
      have htt : (Subscheme.totalTransform t.f (E i)).stalkIdeal y = ⊤ := by
        rw [stalkIdeal_totalTransform, h, Ideal.map_top]
      rw [ite_eq_right hnle, pow_zero, mul_one, htt]
      refine (top_le_iff.mp ?_).symm
      rw [Subscheme.strictTransform_stalkIdeal]
      exact le_iSup_of_le 0 (by simp [htt])
    · rw [stalkIdeal_totalTransform_eq_strict_mul_exceptional_pow hX t y hZ hTZ hT ha (E i) h]
      have hiff : (E i).stalkIdeal (t.f y) ≤ B.stalkIdeal (t.f y) ↔ a ∈ T := by
        rw [h, hT, Ideal.span_singleton_le_iff_mem]
        constructor
        · intro hmem
          by_contra haT
          exact rsop_notMem_span hZ hTZ ha haT hmem
        · exact fun haT => Ideal.subset_span haT
      simp only [hiff]
  · have hyE : y ∉ t.exceptional.pts := by
      rw [MonoidalTransformation.pts_exceptional]; exact hB
    rw [MonoidalTransformation.strictTransform_stalkIdeal_of_notMem t (E i) hyE,
      Subscheme.stalkIdeal_eq_top_of_notMem_pts hyE, Ideal.top_pow, Ideal.mul_top]

open Classical in
/-- Family form of `stalkIdeal_totalTransform_eq_strict_mul_exceptional_pow`: for the members `E_i`
of a resolution datum of type II whose union has only normal crossings with the permissible center
`B`, `f⁻¹(E_i)_y = (E_i)'_y · P_y^m` with `m = 1` if `E_i ⊇ B` at `f(y)` and `m = 0` otherwise. -/
theorem stalkIdeal_totalTransform_eq_strict_mul_exceptional_pow_of_isDatum {α : ℕ}
    (E : Fin α → Subscheme X) (hX : X.IsNonsingular)
    (hE : ∀ i, (E i).IsNonsingularIrreducibleCodimOne) (hNC : (⨅ i, E i).HasOnlyNormalCrossings)
    (hNCB : (⨅ i, E i).HasOnlyNormalCrossingsWith B) (t : MonoidalTransformation X B) (i : Fin α)
    (y : t.X') [IsRegularLocalRing (t.X'.presheaf.stalk y)] :
    (Subscheme.totalTransform t.f (E i)).stalkIdeal y =
      (Subscheme.strictTransform t (E i)).stalkIdeal y *
        (t.exceptional.stalkIdeal y) ^
          (if (E i).stalkIdeal (t.f y) ≤ B.stalkIdeal (t.f y) then 1 else 0) :=
  stalkIdeal_totalTransform_eq_strict_mul_exceptional_pow_of_isNonsingularDivisor E hX
    (fun i => (hE i).isNonsingularDivisor) hNC hNCB t i y

end DatumTransform


namespace Subscheme

/-- A closed subscheme `D` of a closed subscheme `W` of `Z` is recovered from its image in `Z`:
`ι_W⁻¹(ker(D ↪ W ↪ Z)) = D`. -/
theorem totalTransform_ι_ker_comp_ι {Z : Scheme.{u}} (W : Subscheme Z) (D : Subscheme W.toScheme) :
    totalTransform W.ι ((D.ι ≫ W.ι).ker) = D := by
  refine Subscheme.ext_stalkIdeal fun y => ?_
  set g := D.ι ≫ W.ι with hg
  set K : Subscheme Z := g.ker with hK
  by_cases hy : y ∈ D.pts
  · obtain ⟨w, rfl⟩ := Subscheme.exists_ι_eq_of_mem_pts D hy
    obtain ⟨hker, -⟩ := ker_stalkMap_eq_and_surjective_of_eq_iso_comp g K (asIso g.toImage)
      (Scheme.Hom.toImage_imageι g).symm w
    rw [stalkIdeal_totalTransform]
    have h1 : K.stalkIdeal (W.ι.base (D.ι.base w)) = RingHom.ker (g.stalkMap w).hom := hker.symm
    have hcomp : g.stalkMap w = W.ι.stalkMap (D.ι.base w) ≫ D.ι.stalkMap w :=
      Scheme.Hom.stalkMap_comp _ _ _
    have hψ : ∀ a, (g.stalkMap w).hom a =
        (D.ι.stalkMap w).hom ((W.ι.stalkMap (D.ι.base w)).hom a) := by
      intro a; rw [hcomp]; rfl
    have hker2 : RingHom.ker (g.stalkMap w).hom = Ideal.comap (W.ι.stalkMap (D.ι.base w)).hom
        (RingHom.ker (D.ι.stalkMap w).hom) := by
      ext a
      simp only [RingHom.mem_ker, hψ]
      exact Iff.rfl
    rw [h1, hker2, stalkIdeal_eq_ker_stalkMap D w]
    exact Ideal.map_comap_of_surjective _ (W.ι.stalkMap_surjective _) _
  · rw [stalkIdeal_eq_top_of_notMem_pts hy]
    have hK' : W.ι.base y ∉ K.pts := by
      intro hmem
      apply hy
      obtain ⟨k, hk⟩ := Subscheme.exists_ι_eq_of_mem_pts K hmem
      have he : (asIso g.toImage).hom ≫ K.ι = g := Scheme.Hom.toImage_imageι g
      have hmem' : ∃ w, g.base w = W.ι.base y := by
        refine ⟨(asIso g.toImage).inv.base k, ?_⟩
        have h2 := congrArg (fun φ => φ.base ((asIso g.toImage).inv.base k)) he
        simp only [Scheme.Hom.comp_base, TopCat.hom_comp, ContinuousMap.comp_apply] at h2
        rw [← h2]
        have h3 : (asIso g.toImage).hom.base ((asIso g.toImage).inv.base k) = k := by
          rw [← Scheme.Hom.comp_apply, Iso.inv_hom_id]; rfl
        rw [h3]
        exact hk
      obtain ⟨w, hw⟩ := hmem'
      have hw' : W.ι.base (D.ι.base w) = W.ι.base y := hw
      have := W.ι.isEmbedding.injective hw'
      rw [← this]
      exact Subscheme.mem_pts_ι D w
    rw [stalkIdeal_totalTransform, stalkIdeal_eq_top_of_notMem_pts hK', Ideal.map_top]

end Subscheme

namespace Ideal

/-- An ideal contained in the `ν`-th power of a principal ideal `(π)` is that power times its
colon ideal (the quotient `J · (π)^{-ν}` of Ch. 0 §5). -/
theorem eq_colon_mul_span_singleton_pow {A : Type*} [CommRing A] [IsDomain A]
    {π : A} {J : Ideal A} {ν : ℕ} (hJ : J ≤ Ideal.span {π ^ ν}) :
    J = J.colon ((Ideal.span {π} ^ ν : Ideal A) : Set A) * Ideal.span {π} ^ ν := by
  rw [Ideal.span_singleton_pow]
  apply le_antisymm
  · intro x hx
    obtain ⟨k, rfl⟩ := Ideal.mem_span_singleton'.mp (hJ hx)
    refine Ideal.mul_mem_mul (r := k) (s := π ^ ν) ?_ (Ideal.mem_span_singleton_self _)
    refine Submodule.mem_colon.mpr fun s hs => ?_
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp (SetLike.mem_coe.mp hs)
    have : k • (c * π ^ ν) = c * (k * π ^ ν) := by rw [smul_eq_mul]; ring
    rw [this]
    exact J.mul_mem_left c hx
  · refine Ideal.mul_le.mpr fun a ha b hb => ?_
    exact Submodule.mem_colon.mp ha b hb

/-- **The algebra of Remarks 2 and 3 (pp. 324–326)**, in the local ring of `X̄_{s+1}` at a point:
if `(f̄⁻¹ J̃)` is divisible by `π^ν̃`, `b̃ ≤ Σ m_j a_j + ν̃`, and
`f̄⁻¹(J̃ · ∏ P̃_j^{a_j}) = π^{b̃} · W` with `f̄⁻¹ P̃_j = P̃'_j π^{m_j}`, then
`(f̄⁻¹ J̃ : π^ν̃) · ∏ (P̃'_j)^{a_j} · π^{Σ m_j a_j + ν̃ - b̃} = W`. -/
theorem colon_mul_prod_mul_pow_eq {A : Type*} [CommRing A] [IsDomain A] {π : A} (hπ : π ≠ 0)
    {n : ℕ} (Jm : Ideal A) (E' : Fin n → Ideal A) (a m : Fin n → ℕ) (ν b : ℕ) (W : Ideal A)
    (hdiv : Jm ≤ Ideal.span {π ^ ν})
    (hb : Ideal.span {π} ≠ ⊤ → b ≤ (∑ j, m j * a j) + ν)
    (h : Jm * ∏ j, (E' j * Ideal.span {π} ^ (m j)) ^ (a j) = Ideal.span {π} ^ b * W) :
    Jm.colon ((Ideal.span {π} ^ ν : Ideal A) : Set A) * (∏ j, (E' j) ^ (a j)) *
      Ideal.span {π} ^ ((∑ j, m j * a j) + ν - b) = W := by
  set P : Ideal A := Ideal.span {π} with hP
  by_cases hPtop : P = ⊤
  · have hcol : Jm.colon ((P ^ ν : Ideal A) : Set A) = Jm := by
      rw [hPtop, Ideal.top_pow]
      ext r
      rw [Submodule.mem_colon]
      constructor
      · intro hr
        simpa using hr 1 (by simp)
      · intro hr s _
        simpa [smul_eq_mul] using Jm.mul_mem_right s hr
    rw [hcol]
    simp only [hPtop, Ideal.top_pow, Ideal.mul_top, Ideal.top_mul] at h ⊢
    exact h
  · have hb' := hb hPtop
    have hK := eq_colon_mul_span_singleton_pow hdiv
    set K := Jm.colon ((P ^ ν : Ideal A) : Set A) with hKdef
    have hprod : ∏ j, (E' j * P ^ (m j)) ^ (a j) =
        (∏ j, (E' j) ^ (a j)) * P ^ (∑ j, m j * a j) := by
      simp only [mul_pow, Finset.prod_mul_distrib, ← pow_mul, Finset.prod_pow_eq_pow_sum]
    rw [hK, hprod] at h
    have hk : (∑ j, m j * a j) + ν = b + ((∑ j, m j * a j) + ν - b) := by omega
    have hπb : π ^ b ≠ 0 := pow_ne_zero _ hπ
    have h2 : Ideal.span {π ^ b} *
        (K * (∏ j, (E' j) ^ (a j)) * P ^ ((∑ j, m j * a j) + ν - b)) =
        Ideal.span {π ^ b} * W := by
      rw [← Ideal.span_singleton_pow, ← h]
      calc P ^ b * (K * (∏ j, (E' j) ^ (a j)) * P ^ ((∑ j, m j * a j) + ν - b))
          = K * (∏ j, (E' j) ^ (a j)) * P ^ (b + ((∑ j, m j * a j) + ν - b)) := by
            rw [pow_add]; ring
        _ = K * (∏ j, (E' j) ^ (a j)) * P ^ ((∑ j, m j * a j) + ν) := by rw [← hk]
        _ = _ := by
            rw [pow_add, Ideal.span_singleton_pow]; ring
    exact (Ideal.span_singleton_mul_right_inj hπb).mp h2


/-- The extension of a finite product of ideals along a ring map is the product of the extensions. -/
theorem map_finset_prod {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) {ι : Type*}
    (s : Finset ι) (I : ι → Ideal R) : (∏ i ∈ s, I i).map f = ∏ i ∈ s, (I i).map f := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [Ideal.one_eq_top, Ideal.map_top]
  | insert i s hi ih => rw [Finset.prod_insert hi, Finset.prod_insert hi, Ideal.map_mul, ih]

end Ideal


namespace Subscheme

variable {X : Scheme.{u}}

/-- For an irreducible non-singular `B`, `E_x ⊆ B_x` at a point `x` of `B` means `B ⊆ E`. -/
theorem stalkIdeal_le_iff_pts_subset {B E : Subscheme X} (hB : B.IsIrreducible)
    (hBns : B.IsNonsingular) {x : X} (hx : x ∈ B.pts) :
    E.stalkIdeal x ≤ B.stalkIdeal x ↔ B.pts ⊆ E.pts := by
  constructor
  · intro hle
    have hirr := Subscheme.isIrreducible_pts B hB
    have hcl : IsClosed B.pts := B.support.isClosed
    have hη : closure {hirr.genericPoint} = B.pts := hirr.closure_genericPoint hcl
    have hηB : hirr.genericPoint ∈ B.pts := hη.le (subset_closure rfl)
    have hsp : hirr.genericPoint ⤳ x := specializes_iff_mem_closure.mpr (by rw [hη]; exact hx)
    have h1 := stalkIdeal_le_of_specializes_of_le hsp hle
    have hηE : hirr.genericPoint ∈ E.pts := by
      rw [mem_pts_iff_stalkIdeal_ne_top] at hηB ⊢
      intro htop
      rw [htop, top_le_iff] at h1
      exact hηB h1
    rw [← hη]
    exact closure_minimal (Set.singleton_subset_iff.mpr hηE) E.support.isClosed
  · intro hsub
    exact Hironaka.DatumTransform.stalkIdeal_le_of_pts_subset
      (Hironaka.DatumTransform.isReduced_of_isNonsingular hBns) hsub x

end Subscheme

namespace DatumTransform

variable {X : Scheme.{u}} {B : Subscheme X}

open Classical in
/-- Global form of `stalkIdeal_totalTransform_eq_strict_mul_exceptional_pow_of_isNonsingularDivisor`
for an irreducible non-singular center: the exponent is `1` iff `B ⊆ E_i`. -/
theorem stalkIdeal_totalTransform_eq_strict_mul_exceptional_pow_of_pts_subset_of_isNonsingularDivisor
    {α : ℕ} (E : Fin α → Subscheme X) (hX : X.IsNonsingular)
    (hE : ∀ i, (E i).IsNonsingularDivisor) (hNC : (⨅ i, E i).HasOnlyNormalCrossings)
    (hNCB : (⨅ i, E i).HasOnlyNormalCrossingsWith B) (hB : B.IsIrreducible)
    (hBns : B.IsNonsingular) (t : MonoidalTransformation X B) (i : Fin α)
    (y : t.X') [IsRegularLocalRing (t.X'.presheaf.stalk y)] :
    (Subscheme.totalTransform t.f (E i)).stalkIdeal y =
      (Subscheme.strictTransform t (E i)).stalkIdeal y *
        (t.exceptional.stalkIdeal y) ^ (if B.pts ⊆ (E i).pts then 1 else 0) := by
  rw [stalkIdeal_totalTransform_eq_strict_mul_exceptional_pow_of_isNonsingularDivisor E hX hE hNC
    hNCB t i y]
  by_cases hx : t.f y ∈ B.pts
  · rw [Subscheme.stalkIdeal_le_iff_pts_subset hB hBns hx]
  · have hyE : y ∉ t.exceptional.pts := by
      rw [MonoidalTransformation.pts_exceptional]; exact hx
    rw [Subscheme.stalkIdeal_eq_top_of_notMem_pts hyE]
    simp only [Ideal.top_pow, Ideal.mul_top]

open Classical in
/-- Global form of `stalkIdeal_totalTransform_eq_strict_mul_exceptional_pow_of_isDatum` for an
irreducible non-singular center: the exponent is `1` iff `B ⊆ E_i`. -/
theorem stalkIdeal_totalTransform_eq_strict_mul_exceptional_pow_of_pts_subset {α : ℕ}
    (E : Fin α → Subscheme X) (hX : X.IsNonsingular)
    (hE : ∀ i, (E i).IsNonsingularIrreducibleCodimOne) (hNC : (⨅ i, E i).HasOnlyNormalCrossings)
    (hNCB : (⨅ i, E i).HasOnlyNormalCrossingsWith B) (hB : B.IsIrreducible)
    (hBns : B.IsNonsingular) (t : MonoidalTransformation X B) (i : Fin α)
    (y : t.X') [IsRegularLocalRing (t.X'.presheaf.stalk y)] :
    (Subscheme.totalTransform t.f (E i)).stalkIdeal y =
      (Subscheme.strictTransform t (E i)).stalkIdeal y *
        (t.exceptional.stalkIdeal y) ^ (if B.pts ⊆ (E i).pts then 1 else 0) :=
  stalkIdeal_totalTransform_eq_strict_mul_exceptional_pow_of_pts_subset_of_isNonsingularDivisor E hX
    (fun i => (hE i).isNonsingularDivisor) hNC hNCB hB hBns t i y

end DatumTransform


namespace DatumII.Raw

variable {Y : Scheme.{u}}

open Classical in
/-- **The generic point of a permissible center** (p. 325: "`f` is permissible"): for an irreducible
permissible center `B` of a resolution datum `ℜ` of type II on a non-singular scheme, at the generic
point `ξ` of `B` one has `ν(J_ξ) = ν(ℜ) < ∞`, and `b ≤ ∑_{B ⊆ E_i} a_i + ν(ℜ)` (as `ξ ∈ S(ℜ)`). -/
theorem b_le_sum_add_nu_and_exists_isGenericPoint_of_forall_stalkIdeal_ne_bot
    (hY : Y.IsNonsingular) (R : DatumII.Raw Y) (hJ : ∀ x : Y, R.J.stalkIdeal x ≠ ⊥)
    {B : Subscheme Y} (hBi : B.IsIrreducible) (hperm : R.IsPermissible B) :
    R.b ≤ (∑ i, if B.pts ⊆ (R.E i).pts then R.a i else 0) + R.nu.toNat ∧
      ∃ ξ : Y, IsGenericPoint ξ B.pts ∧ (R.nu.toNat : ℕ∞) ≤ Ideal.nu (R.J.stalkIdeal ξ) := by
  have hirr := Subscheme.isIrreducible_pts B hBi
  have hcl : IsClosed B.pts := B.support.isClosed
  have hη : closure {hirr.genericPoint} = B.pts := hirr.closure_genericPoint hcl
  set ξ := hirr.genericPoint with hξdef
  have hξ : ξ ∈ B.pts := hη.le (subset_closure rfl)
  have hS' : ξ ∈ R.sStar := hperm.2.1 hξ
  obtain ⟨hξS, hνξ⟩ := hS'
  have hle : R.nuAt ξ ≤ R.nu :=
    le_iSup₂ (f := fun x (_ : x ∈ R.S) => R.nuAt x) ξ hξS
  have heq : R.nuAt ξ = R.nu := le_antisymm hle hνξ
  have : IsRegularLocalRing (Y.presheaf.stalk ξ) := hY ξ
  have hne : Ideal.nu (R.J.stalkIdeal ξ) ≠ ⊤ := by
    intro htop
    apply hJ ξ
    have h := ((Ideal.ord_basic _ (R.J.stalkIdeal ξ) ⊥ ⊥).1).mp htop
    rw [eq_bot_iff, ← Ideal.iInf_pow_eq_bot_of_isLocalRing (maximalIdeal _)
      (Ideal.IsMaximal.ne_top inferInstance)]
    exact le_iInf h
  have hnu : R.nu = ((R.nu.toNat : ℕ) : ℕ∞) := by
    have h1 : R.nu ≠ ⊤ := by
      rw [← heq]; exact hne
    exact (ENat.natCast_toNat h1).symm
  have hw : R.weight ξ = ∑ i, if B.pts ⊆ (R.E i).pts then R.a i else 0 := by
    unfold DatumII.Raw.weight
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun j _ => ?_
    have hiff : ξ ∈ (R.E j).pts ↔ B.pts ⊆ (R.E j).pts := by
      constructor
      · intro hj
        rw [← hη]
        exact closure_minimal (Set.singleton_subset_iff.mpr hj) (R.E j).support.isClosed
      · intro hsub
        exact hsub hξ
    simp only [hiff]
  refine ⟨?_, ξ, hη, ?_⟩
  · have h1 : (R.b : ℕ∞) ≤ (((∑ i, if B.pts ⊆ (R.E i).pts then R.a i else 0) +
        R.nu.toNat : ℕ) : ℕ∞) := by
      have h2 : (R.b : ℕ∞) ≤ (R.weight ξ : ℕ∞) + R.nuAt ξ := hξS
      rw [heq, hw] at h2
      calc (R.b : ℕ∞) ≤ _ := h2
        _ = _ := by rw [Nat.cast_add]; congr 1
    exact_mod_cast h1
  · rw [← hnu]
    exact heq.symm.le.trans' le_rfl

open Classical in
/-- **The generic point of a permissible center** (p. 325: "`f` is permissible"): for an irreducible
permissible center `B` of a resolution datum `ℜ` of type II on a non-singular scheme, at the generic
point `ξ` of `B` one has `ν(J_ξ) = ν(ℜ) < ∞`, and `b ≤ ∑_{B ⊆ E_i} a_i + ν(ℜ)` (as `ξ ∈ S(ℜ)`). -/
theorem b_le_sum_add_nu_and_exists_isGenericPoint (hY : Y.IsNonsingular) (R : DatumII.Raw Y)
    (hR : R.IsDatum) {B : Subscheme Y} (hBi : B.IsIrreducible) (hperm : R.IsPermissible B) :
    R.b ≤ (∑ i, if B.pts ⊆ (R.E i).pts then R.a i else 0) + R.nu.toNat ∧
      ∃ ξ : Y, IsGenericPoint ξ B.pts ∧ (R.nu.toNat : ℕ∞) ≤ Ideal.nu (R.J.stalkIdeal ξ) :=
  b_le_sum_add_nu_and_exists_isGenericPoint_of_forall_stalkIdeal_ne_bot hY R hR.2.2.2 hBi hperm

end DatumII.Raw


namespace Ideal

/-- Factoring `P^{b̄ k}` out of `J̄*(s)` (p. 325): `(J P^b)^k ⊔ (X P^e)^b = P^{bk} (J^k ⊔ (X P^c)^b)`
when `e = c + k`. -/
theorem sup_pow_mul_eq {A : Type*} [CommRing A] (P J X : Ideal A) (b k c e : ℕ) (he : e = c + k) :
    (J * P ^ b) ^ k ⊔ (X * P ^ e) ^ b = P ^ (b * k) * (J ^ k ⊔ (X * P ^ c) ^ b) := by
  subst he
  rw [Ideal.mul_sup]
  congr 1
  · rw [mul_pow, ← pow_mul, mul_comm]
  · rw [mul_pow, mul_pow, ← pow_mul, ← pow_mul, mul_left_comm, ← pow_add]
    congr 2
    ring

end Ideal


namespace Ideal

section Order

variable {R : Type u} [CommRing R]

/-- The order of an ideal of finite order is attained by an element. -/
theorem exists_mem_ordElem_eq_ord [IsLocalRing R] (I : Ideal R) (hI : Ideal.nu I ≠ ⊤) :
    ∃ f ∈ I, Ideal.ordElem (maximalIdeal R) f = Ideal.nu I := by
  obtain ⟨n, hn⟩ : ∃ n : ℕ, Ideal.nu I = n := ⟨_, (ENat.natCast_toNat hI).symm⟩
  have hle : I ≤ maximalIdeal R ^ n := Ideal.le_pow_of_le_ord hn.ge
  by_contra h
  have hall : I ≤ maximalIdeal R ^ (n + 1) := by
    intro f hf
    refine Ideal.mem_pow_of_le_ordElem ?_
    have h1 : (n : ℕ∞) ≤ Ideal.ordElem (maximalIdeal R) f := Ideal.le_ordElem (hle hf)
    have h2 : Ideal.ordElem (maximalIdeal R) f ≠ n := fun h' => h ⟨f, hf, h'.trans hn.symm⟩
    have h3 : (n : ℕ∞) < Ideal.ordElem (maximalIdeal R) f := lt_of_le_of_ne h1 (Ne.symm h2)
    exact_mod_cast Order.add_one_le_of_lt h3
  have := Ideal.le_ord (M := maximalIdeal R) hall
  rw [← Ideal.nu, hn] at this
  exact absurd (by exact_mod_cast this : n + 1 ≤ n) (by omega)

variable [IsRegularLocalRing R]

/-- **Subadditivity of the order** in a regular local ring (`gr_M(R)` is a domain): the order of a
product of ideals is at most the sum of the orders (the other inequality is `Ideal.ord_basic`). -/
theorem nu_mul_le (I K : Ideal R) : Ideal.nu (I * K) ≤ Ideal.nu I + Ideal.nu K := by
  by_cases hI : Ideal.nu I = ⊤
  · rw [hI, top_add]; exact le_top
  by_cases hK : Ideal.nu K = ⊤
  · rw [hK, add_top]; exact le_top
  obtain ⟨f, hf, hfo⟩ := exists_mem_ordElem_eq_ord I hI
  obtain ⟨g, hg, hgo⟩ := exists_mem_ordElem_eq_ord K hK
  refine Ideal.ord_le fun k hk => ?_
  have h1 : (k : ℕ∞) ≤ Ideal.ordElem (maximalIdeal R) (f * g) := Ideal.le_ordElem (hk (Ideal.mul_mem_mul hf hg))
  rwa [ordElem_mul_maximalIdeal, hfo, hgo] at h1

/-- **Additivity of the order** for a principal factor: `ν(I · (u)) = ν(I) + ν(u)`. -/
theorem nu_mul_span_singleton (I : Ideal R) (u : R) :
    Ideal.nu (I * Ideal.span {u}) = Ideal.nu I + Ideal.ordElem (maximalIdeal R) u := by
  apply le_antisymm
  · rw [← Ideal.ord_span_singleton]; exact nu_mul_le _ _
  · rw [← Ideal.ord_span_singleton]
    exact (Ideal.ord_basic _ ⊥ I (Ideal.span {u})).2.2.2

/-- `ν(J^k) ≤ k ν(J)` in a regular local ring. -/
theorem nu_pow_le (J : Ideal R) (k : ℕ) : Ideal.nu (J ^ k) ≤ k * Ideal.nu J := by
  induction k with
  | zero =>
    rw [pow_zero, Nat.cast_zero, zero_mul]
    refine Ideal.ord_le fun n hn => ?_
    rcases Nat.eq_zero_or_pos n with h | h
    · simp [h]
    · exfalso
      have h1 : (1 : R) ∈ maximalIdeal R ^ n := hn (by rw [Ideal.one_eq_top]; exact Submodule.mem_top)
      have h2 : maximalIdeal R ^ n ≤ maximalIdeal R :=
        (Ideal.pow_le_pow_right h).trans (pow_one _).le
      exact (maximalIdeal.isMaximal R).ne_top ((Ideal.eq_top_iff_one _).mpr (h2 h1))
  | succ k ih =>
    rw [pow_succ]
    refine (nu_mul_le _ _).trans ?_
    calc Ideal.nu (J ^ k) + Ideal.nu J ≤ k * Ideal.nu J + Ideal.nu J := by gcongr
      _ = ((k + 1 : ℕ) : ℕ∞) * Ideal.nu J := by push_cast; ring

end Order

end Ideal

end Hironaka
