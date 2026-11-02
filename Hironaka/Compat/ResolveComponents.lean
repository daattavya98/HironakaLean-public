/-
Copyright (c) 2026 Daattavya Aggarwal, Minhyong Kim, Oisin Kim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daattavya Aggarwal, Minhyong Kim, Oisin Kim
-/
module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.Order.CompletePartialOrder
public import Architect
public import Hironaka.Ch1.FundamentalTheorems
public import Hironaka.Compat.ExtendSuccessionII
public import Hironaka.Compat.DatumPresentation

/-!
# Theorem II₂ for a non-irreducible non-singular scheme (Ch. I §3, p. 176: "As is easily seen, the
proof of the main theorem can be reduced to the case in which `X` is irreducible")

Main Theorem II(N) is stated (p. 176) for a non-singular algebraic scheme `X` that need not be
irreducible; the fundamental theorem `II₂^N`, by which it is deduced, is for an irreducible one
(p. 170).  The reduction is "easily seen" to the paper; this file carries it out.

A non-singular algebraic scheme is the disjoint union of its finitely many irreducible components,
which are open and closed (the local rings are domains).  A permissible succession for a datum on
such a scheme is built from permissible and resolving successions of two complementary clopen
pieces `Z` and `W` by always performing the next monoidal transformation of the piece on which
`ν` is the larger one: the center of a transformation of `Z` is permissible for the datum on the
whole scheme only if `ν(ℜ|Z) = ν(ℜ)`, since a center lies in `S_{ν(ℜ)}`.  This is why the pieces
must be interleaved, and not treated one after the other: after a transformation of `Z`, the
datum on `W` has only acquired an empty component (it has the same essential characteristics,
`DatumII.Raw.SameChar`), so the succession of `W` remains permissible and resolving.

Deviation from the paper (gap filled): the paper says only "As is easily seen".
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

namespace Hironaka

universe u

namespace DatumII.Raw

section Pieces

variable {X Z W : Scheme.{u}}

theorem resolvedAt_pullback_iff (j : Z ⟶ X) [Flat j] [IsPreimmersion j] (ℜ : Raw X) (z : Z) :
    (ℜ.pullback j).ResolvedAt z ↔ ℜ.ResolvedAt (j z) := by
  unfold ResolvedAt
  rw [weight_pullback, nuAt_pullback]
  rfl

/-- A datum resolved everywhere has `ν(ℜ) = 0` (`S(ℜ)` is empty). -/
theorem nu_eq_zero_of_resolvedEverywhere (ℜ : Raw X) (h : ℜ.ResolvedEverywhere) : ℜ.nu = 0 := by
  have hS : ℜ.S = ∅ := Set.eq_empty_iff_forall_notMem.mpr fun x hx => (not_le.mpr (h x)) hx
  unfold nu
  rw [hS]
  simp

/-- `ν(ℜ)` is the larger of `ν` of the restrictions to two pieces that cover `X`. -/
theorem nu_eq_max_of_cover (jZ : Z ⟶ X) (jW : W ⟶ X) [Flat jZ] [IsPreimmersion jZ] [Flat jW]
    [IsPreimmersion jW] (hcov : Set.range jZ.base ∪ Set.range jW.base = Set.univ) (ℜ : Raw X) :
    ℜ.nu = max (ℜ.pullback jZ).nu (ℜ.pullback jW).nu := by
  refine le_antisymm (iSup₂_le fun x hx => ?_)
    (max_le (nu_pullback_le jZ ℜ) (nu_pullback_le jW ℜ))
  have hx' : x ∈ Set.range jZ.base ∪ Set.range jW.base := hcov ▸ Set.mem_univ x
  rcases hx' with ⟨z, rfl⟩ | ⟨w, rfl⟩
  · refine le_max_of_le_left ?_
    rw [← nuAt_pullback jZ ℜ z]
    exact le_iSup₂ (f := fun x (_ : x ∈ (ℜ.pullback jZ).S) => (ℜ.pullback jZ).nuAt x) z
      ((mem_S_pullback jZ ℜ z).mpr hx)
  · refine le_max_of_le_right ?_
    rw [← nuAt_pullback jW ℜ w]
    exact le_iSup₂ (f := fun x (_ : x ∈ (ℜ.pullback jW).S) => (ℜ.pullback jW).nuAt x) w
      ((mem_S_pullback jW ℜ w).mpr hx)

/-- A datum whose restrictions to two covering pieces are resolved everywhere is resolved
everywhere. -/
theorem resolvedEverywhere_of_cover (jZ : Z ⟶ X) (jW : W ⟶ X) [Flat jZ] [IsPreimmersion jZ]
    [Flat jW] [IsPreimmersion jW] (hcov : Set.range jZ.base ∪ Set.range jW.base = Set.univ)
    (ℜ : Raw X) (hZ : (ℜ.pullback jZ).ResolvedEverywhere)
    (hW : (ℜ.pullback jW).ResolvedEverywhere) : ℜ.ResolvedEverywhere := fun x => by
  have hx' : x ∈ Set.range jZ.base ∪ Set.range jW.base := hcov ▸ Set.mem_univ x
  rcases hx' with ⟨z, rfl⟩ | ⟨w, rfl⟩
  · exact (resolvedAt_pullback_iff jZ ℜ z).mp (hZ z)
  · exact (resolvedAt_pullback_iff jW ℜ w).mp (hW w)

/-- Two data with the same essential characteristics are resolved at the same points. -/
theorem SameChar.resolvedAt_iff {ℜ₁ ℜ₂ : Raw X} (h : SameChar ℜ₁ ℜ₂) (x : X) :
    ℜ₁.ResolvedAt x ↔ ℜ₂.ResolvedAt x := by
  unfold ResolvedAt
  rw [h.weight_eq, h.nuAt_eq, h.2.1]

theorem SameChar.resolvedEverywhere {ℜ₁ ℜ₂ : Raw X} (h : SameChar ℜ₁ ℜ₂)
    (h₁ : ℜ₁.ResolvedEverywhere) : ℜ₂.ResolvedEverywhere := fun x => (h.resolvedAt_iff x).mp (h₁ x)

end Pieces

end DatumII.Raw

namespace MonoidalSuccession

variable {X Y : Scheme.{u}}

/-- A succession permissible for a datum is permissible for any datum with the same essential
characteristics, and the transforms keep the same characteristics. -/
theorem isPermissibleII_of_sameChar (s : MonoidalSuccession X Y) {ℜ₁ ℜ₂ : DatumII.Raw X}
    (h : DatumII.Raw.SameChar ℜ₁ ℜ₂) (hs : s.IsPermissibleII ℜ₁) : s.IsPermissibleII ℜ₂ := by
  induction s with
  | nil X => trivial
  | cons B t rest ih => exact ⟨h.isPermissible hs.1, ih (h.transform t) hs.2⟩

end MonoidalSuccession

/-! ### Two complementary clopen pieces and one monoidal transformation of one of them -/

/-- Two flat preimmersions `jZ : Z → X`, `jW : W → X` with disjoint open ranges that cover `X`:
`X` is the disjoint union of the clopen pieces `Z` and `W`. -/
structure ClopenPair {X Z W : Scheme.{u}} (jZ : Z ⟶ X) (jW : W ⟶ X) : Prop where
  isOpen_range_left : IsOpen (Set.range jZ.base)
  isOpen_range_right : IsOpen (Set.range jW.base)
  cover : Set.range jZ.base ∪ Set.range jW.base = Set.univ
  disjoint : Disjoint (Set.range jZ.base) (Set.range jW.base)

namespace ClopenPair

variable {X Z W : Scheme.{u}} {jZ : Z ⟶ X} {jW : W ⟶ X}

theorem symm (h : ClopenPair jZ jW) : ClopenPair jW jZ :=
  ⟨h.isOpen_range_right, h.isOpen_range_left, by rw [Set.union_comm]; exact h.cover,
    h.disjoint.symm⟩

theorem isClosed_range_left (h : ClopenPair jZ jW) : IsClosed (Set.range jZ.base) := by
  have : Set.range jZ.base = (Set.range jW.base)ᶜ :=
    (IsCompl.eq_compl (isCompl_iff.mpr ⟨h.disjoint, codisjoint_iff.mpr h.cover⟩))
  rw [this]
  exact h.isOpen_range_right.isClosed_compl

end ClopenPair

/-- **One monoidal transformation of one of two complementary pieces, performed on the whole
scheme.**  Let `X` be the disjoint union of the pieces `Z` and `W`, `ℜ` a datum on `X` and `ts` a
monoidal transformation of `Z` whose center `B` is permissible for the restriction `ℜ_Z`, with
`ν(ℜ_W) ≤ ν(ℜ_Z)`, so that `ν(ℜ_Z) = ν(ℜ)`.  Then `ts` is induced by a monoidal transformation
`tY` of `X` with a center `BY` permissible for `ℜ`; the pull-back of `ℜ.transform tY` to the
transform of `Z` is `(ℜ_Z).transform ts`, and its pull-back to `W` has the same essential
characteristics as `ℜ_W` (it has acquired an empty component `E_{α+1}`).

Deviation from the paper (gap filled): this is the step of the reduction of Main Theorem II(N) to
irreducible `X` which the paper calls "easily seen" (p. 176). -/
@[blueprint "lem:I.3-main-II-step"
  (statement := /-- Let $X$ be a non-singular algebraic scheme, the disjoint union of two open and
    closed subschemes $Z$ and $W$, $\mathfrak R$ a resolution datum of type
    $\mathfrak R^N_{\mathrm{II}}$ on $X$ and $f_Z\colon Z'\to Z$ a monoidal transformation whose
    center $B$ is permissible for $\mathfrak R|_Z$, with $\nu(\mathfrak R|_W)\le
    \nu(\mathfrak R|_Z)$. Then there is a monoidal transformation $f\colon X'\to X$ with a
    center $B_X$ permissible for $\mathfrak R$, inducing $f_Z$ over $Z$ and an isomorphism over
    $W$, such that $f^*(\mathfrak R)|_{Z'}=f_Z^*(\mathfrak R|_Z)$ and $f^*(\mathfrak R)|_W$ has the
    same essential characteristics as $\mathfrak R|_W$ (p.~275). (The step of the reduction of
    main theorem II($N$) to irreducible $X$, p.~176.) -/)
  (proof := /-- $B$ is closed in $X$ ($Z$ is open and closed); let $B_X$ be $B$ in $X$ and $f$ a
    monoidal transformation of $X$ with center $B_X$ (\cref{thm:monoidal-transformation-exists});
    $f_Z$ is induced by $f$ and $f$ is an isomorphism over $W$ (\cref{compat:blowup-flat-base-change}).
    As $\nu(\mathfrak R)=\max(\nu(\mathfrak R|_Z),\nu(\mathfrak R|_W))=\nu(\mathfrak R|_Z)$,
    $B_X\subseteq S_{\nu(\mathfrak R)}$ and $E_1\cup\dots\cup E_\alpha$ has only normal
    crossings with $B_X$, so $B_X$ is permissible for $\mathfrak R$. The exponent
    $a_{\alpha+1}$ is the same for $\mathfrak R$ and $\mathfrak R|_Z$ as $B_X\subseteq E_i$ iff
    $B\subseteq E_i|_Z$; over $W$ the new component $E_{\alpha+1}$ is empty.

    \textbf{Deviation from the paper (gap filled).} ``As is easily seen'' (p.~176); the steps of
    the argument are supplied. -/)
  (latexEnv := "lemma")]
theorem DatumII.Raw.exists_step_of_clopenPair [Hironaka.Cited.IsHironakaBaseIsClosedSingularLocus.{u}] [Hironaka.Cited.MonoidalTransformationExistsIsProper.{u}] [Hironaka.Cited.CurveFiniteIntegralClosure.{u}] [Hironaka.Cited.IsRegularLocalRingLocalizationOfIsRegularLocalRing.{u}] {X Z W : Scheme.{u}} [IsAlgebraicScheme X]
    (hX : X.IsNonsingular) (ℜ : DatumII.Raw X) (hℜ : ℜ.IsDatum) (jZ : Z ⟶ X) (jW : W ⟶ X)
    [Flat jZ] [IsPreimmersion jZ] [Flat jW] [IsPreimmersion jW] (hp : ClopenPair jZ jW)
    {B : Subscheme Z} (ts : MonoidalTransformation Z B) (hperm : (ℜ.pullback jZ).IsPermissible B)
    (hν : (ℜ.pullback jW).nu ≤ (ℜ.pullback jZ).nu) :
    ∃ (BY : Subscheme X) (tY : MonoidalTransformation X BY) (jZ' : ts.X' ⟶ tY.X')
      (jW' : W ⟶ tY.X'), Flat jZ' ∧ IsPreimmersion jZ' ∧ Flat jW' ∧ IsPreimmersion jW' ∧
      ClopenPair jZ' jW' ∧ ℜ.IsPermissible BY ∧ IsAlgebraicScheme tY.X' ∧
      tY.X'.IsNonsingular ∧ (ℜ.transform tY).IsDatum ∧
      (ℜ.transform tY).pullback jZ' = (ℜ.pullback jZ).transform ts ∧
      DatumII.Raw.SameChar ((ℜ.transform tY).pullback jW') (ℜ.pullback jW) := by
  classical
  have hν' : (ℜ.pullback jZ).nu = ℜ.nu := by
    rw [DatumII.Raw.nu_eq_max_of_cover jZ jW hp.cover ℜ]
    exact (max_eq_left hν).symm
  have hBred : B.IsReduced := hperm.1.isReduced
  have hcl : IsClosed (jZ.base '' B.pts) :=
    (Topology.IsClosedEmbedding.mk jZ.isEmbedding hp.isClosed_range_left).isClosedMap _
      B.support.isClosed
  obtain ⟨BY, tY, j', hfl, hpre, hBYred, hBYpts, htt, hsq, hrange, hexc, hst⟩ :=
    MonoidalTransformation.exists_extend_step jZ hBred hcl ts
  have hrng : BY.pts ⊆ Set.range jZ.base := by
    rw [hBYpts]; rintro _ ⟨z, -, rfl⟩; exact ⟨z, rfl⟩
  have hpBY : ℜ.IsPermissible BY :=
    DatumII.Raw.isPermissible_of_isPermissible_pullback jZ htt hrng hν' hperm
  have hcont : ∀ i, BY.IsContainedIn (ℜ.E i) ↔
      B.IsContainedIn (Subscheme.totalTransform jZ (ℜ.E i)) := by
    intro i
    constructor
    · intro hc
      rw [← htt]
      exact fun U => FlatPreimm.totalTransform_mono jZ (show _ ≤ BY from fun U => hc U) U
    · intro hc
      refine Subscheme.isContainedIn_of_pts_subset hBYred ?_
      rw [hBYpts]
      rintro _ ⟨z, hz, rfl⟩
      have := pts_subset_of_isContainedIn hc hz
      rwa [FlatPreimm.pts_totalTransform] at this
  have htr1 : (ℜ.transform tY).pullback j' = (ℜ.pullback jZ).transform ts :=
    DatumII.Raw.pullback_transform_of_lift tY jZ ts j' hsq hexc hst ℜ hcont hν'
  have hY1a : IsAlgebraicScheme tY.X' := tY.isAlgebraicScheme
  have hY1 : tY.X'.IsNonsingular :=
    (tY.isNonsingular_and_isNonsingular_exceptional hX hpBY.1.isNonsingular).1
  have hℜ1 : (ℜ.transform tY).IsDatum :=
    (DatumII.Raw.transform_isDatum hX ℜ hℜ tY hpBY).1
  -- the other piece is not touched
  have hdisj : ∀ w, jW w ∉ BY.pts := fun w hw =>
    (Set.disjoint_left.mp hp.disjoint) (hrng hw) ⟨w, rfl⟩
  obtain ⟨jW', hflW, hpreW, hcompW, hrangeW, hexcW, hstW⟩ := tY.exists_lift_of_disjoint jW hdisj
  refine ⟨BY, tY, j', jW', hfl, hpre, hflW, hpreW, ⟨?_, ?_, ?_, ?_⟩, hpBY, hY1a, hY1, hℜ1, htr1,
    DatumII.Raw.sameChar_pullback_transform_of_lift_disjoint tY jW jW' hcompW hexcW hstW ℜ⟩
  · rw [hrange]; exact hp.isOpen_range_left.preimage tY.f.continuous
  · rw [hrangeW]; exact hp.isOpen_range_right.preimage tY.f.continuous
  · rw [hrange, hrangeW, ← Set.preimage_union, hp.cover, Set.preimage_univ]
  · rw [hrange, hrangeW]; exact hp.disjoint.preimage _

/-! ### Interleaving the successions of two complementary pieces -/

/-- The merging statement for successions of total length `n`: if `X` is the disjoint union of two
clopen pieces `Z` and `W`, and each of the restrictions of `ℜ` has a permissible succession that
resolves it, then `ℜ` has a permissible succession that resolves it. -/
def MergeStatement (n : ℕ) : Prop :=
  ∀ {X Z W Z₁ W₁ : Scheme.{u}} [IsAlgebraicScheme X], X.IsNonsingular →
    ∀ (ℜ : DatumII.Raw X), ℜ.IsDatum →
    ∀ (jZ : Z ⟶ X) (jW : W ⟶ X) [Flat jZ] [IsPreimmersion jZ] [Flat jW] [IsPreimmersion jW],
    ClopenPair jZ jW →
    ∀ (sZ : MonoidalSuccession Z Z₁) (sW : MonoidalSuccession W W₁),
    sZ.length + sW.length = n →
    sZ.IsPermissibleII (ℜ.pullback jZ) → (sZ.transformII (ℜ.pullback jZ)).ResolvedEverywhere →
    sW.IsPermissibleII (ℜ.pullback jW) → (sW.transformII (ℜ.pullback jW)).ResolvedEverywhere →
    ∃ (Y : Scheme.{u}) (s : MonoidalSuccession X Y),
      s.IsPermissibleII ℜ ∧ (s.transformII ℜ).ResolvedEverywhere

/-- The inductive step: perform the first monoidal transformation of the piece `Z` on the whole
scheme (its center is permissible for `ℜ` as `ν(ℜ_W) ≤ ν(ℜ_Z)`), and continue with the rest of
the succession of `Z` and the (unchanged) succession of `W`. -/
theorem mergeStatement_step [Hironaka.Cited.IsHironakaBaseIsClosedSingularLocus.{u}] [Hironaka.Cited.MonoidalTransformationExistsIsProper.{u}] [Hironaka.Cited.CurveFiniteIntegralClosure.{u}] [Hironaka.Cited.IsRegularLocalRingLocalizationOfIsRegularLocalRing.{u}] {n : ℕ} (IH : MergeStatement.{u} n) {X Z W Z₁ W₁ : Scheme.{u}}
    [IsAlgebraicScheme X] (hX : X.IsNonsingular) (ℜ : DatumII.Raw X) (hℜ : ℜ.IsDatum)
    (jZ : Z ⟶ X) (jW : W ⟶ X) [Flat jZ] [IsPreimmersion jZ] [Flat jW] [IsPreimmersion jW]
    (hp : ClopenPair jZ jW) {B : Subscheme Z} (ts : MonoidalTransformation Z B)
    (rest : MonoidalSuccession ts.X' Z₁) (sW : MonoidalSuccession W W₁)
    (hlen : rest.length + sW.length = n)
    (hZ : (MonoidalSuccession.cons B ts rest).IsPermissibleII (ℜ.pullback jZ))
    (hZr : ((MonoidalSuccession.cons B ts rest).transformII (ℜ.pullback jZ)).ResolvedEverywhere)
    (hW : sW.IsPermissibleII (ℜ.pullback jW))
    (hWr : (sW.transformII (ℜ.pullback jW)).ResolvedEverywhere)
    (hν : (ℜ.pullback jW).nu ≤ (ℜ.pullback jZ).nu) :
    ∃ (Y : Scheme.{u}) (s : MonoidalSuccession X Y),
      s.IsPermissibleII ℜ ∧ (s.transformII ℜ).ResolvedEverywhere := by
  obtain ⟨BY, tY, jZ', jW', hflZ, hpreZ, hflW, hpreW, hp', hpBY, hY1a, hY1, hℜ1, htr1, hsc⟩ :=
    DatumII.Raw.exists_step_of_clopenPair hX ℜ hℜ jZ jW hp ts hZ.1 hν
  have := hflZ
  have := hpreZ
  have := hflW
  have := hpreW
  obtain ⟨Y, s', hs', hres'⟩ := IH hY1 (ℜ.transform tY) hℜ1 jZ' jW' hp' rest sW hlen
    (by rw [htr1]; exact hZ.2)
    (by rw [htr1]; exact hZr)
    (sW.isPermissibleII_of_sameChar hsc.symm hW)
    ((MonoidalSuccession.sameChar_transformII sW hsc.symm).resolvedEverywhere hWr)
  exact ⟨Y, MonoidalSuccession.cons BY tY s', ⟨hpBY, hs'⟩, hres'⟩

/-- **Interleaving the successions of two complementary pieces.**  If `X` is a non-singular algebraic
scheme which is the disjoint union of two open and closed subschemes `Z` and `W` and a datum `ℜ` on
`X` restricts to data `ℜ_Z`, `ℜ_W` having permissible successions that resolve them, then `ℜ` has a
permissible succession that resolves it: perform the next monoidal transformation of the piece for
which `ν` is larger (`DatumII.Raw.exists_step_of_clopenPair`).

Deviation from the paper (gap filled): "As is easily seen" (p. 176); the successions of the pieces
must be interleaved, since the center of a transformation of `Z` is permissible for `ℜ` only when
`ν(ℜ_Z) = ν(ℜ)`. -/
@[blueprint "lem:I.3-main-II-merge"
  (statement := /-- Let $X$ be a non-singular algebraic scheme, the disjoint union of two open and
    closed subschemes $Z$ and $W$, and $\mathfrak R$ a resolution datum of type
    $\mathfrak R^N_{\mathrm{II}}$ on $X$. If the restrictions $\mathfrak R|_Z$ and $\mathfrak R|_W$ have
    permissible successions $s_Z$, $s_W$ such that $s_Z^*(\mathfrak R|_Z)$ and
    $s_W^*(\mathfrak R|_W)$ are resolved everywhere, then $\mathfrak R$ has a permissible succession
    $s$ such that $s^*(\mathfrak R)$ is resolved everywhere. (p.~176, ``easily seen''.) -/)
  (proof := /-- Induction on the sum of the lengths of $s_Z$ and $s_W$. If both are empty,
    $\mathfrak R|_Z$ and $\mathfrak R|_W$ are resolved, hence so is $\mathfrak R$. Otherwise let
    $Z$ be the piece with $\nu(\mathfrak R|_W)\le\nu(\mathfrak R|_Z)$ among those whose succession is
    not empty (a resolved datum has $\nu=0$) and apply \cref{lem:I.3-main-II-step} to its first
    monoidal transformation: the new datum on $X'$ restricts to the transform of $\mathfrak R|_Z$
    on the transform of $Z$, so the rest of $s_Z$ is permissible for it and resolves it, and to a
    datum with the same essential characteristics as $\mathfrak R|_W$ on $W$, for which $s_W$ is
    still permissible and resolving (the characteristics determine permissibility and the
    transforms, p.~275). Conclude by the induction hypothesis.

    \textbf{Deviation from the paper (gap filled).} ``As is easily seen'' (p.~176). -/)
  (proofUses := ["lem:I.3-main-II-step"])
  (latexEnv := "lemma")]
theorem mergeStatement [Hironaka.Cited.IsHironakaBaseIsClosedSingularLocus.{u}] [Hironaka.Cited.MonoidalTransformationExistsIsProper.{u}] [Hironaka.Cited.CurveFiniteIntegralClosure.{u}] [Hironaka.Cited.IsRegularLocalRingLocalizationOfIsRegularLocalRing.{u}] (n : ℕ) : MergeStatement.{u} n := by
  induction n with
  | zero =>
    intro X Z W Z₁ W₁ _ hX ℜ hℜ jZ jW _ _ _ _ hp sZ sW hlen hZ hZr hW hWr
    cases sZ with
    | nil _ =>
      cases sW with
      | nil _ =>
        exact ⟨X, MonoidalSuccession.nil X, trivial,
          DatumII.Raw.resolvedEverywhere_of_cover jZ jW hp.cover ℜ hZr hWr⟩
      | cons B t rest => simp at hlen
    | cons B t rest => simp at hlen
  | succ n ih =>
    intro X Z W Z₁ W₁ _ hX ℜ hℜ jZ jW _ _ _ _ hp sZ sW hlen hZ hZr hW hWr
    have hν0Z : (sZ.transformII (ℜ.pullback jZ)).ResolvedEverywhere →
        sZ.length = 0 → (ℜ.pullback jZ).nu = 0 := fun h hl => by
      cases sZ with
      | nil _ => exact DatumII.Raw.nu_eq_zero_of_resolvedEverywhere _ h
      | cons B t rest => simp at hl
    have hν0W : (sW.transformII (ℜ.pullback jW)).ResolvedEverywhere →
        sW.length = 0 → (ℜ.pullback jW).nu = 0 := fun h hl => by
      cases sW with
      | nil _ => exact DatumII.Raw.nu_eq_zero_of_resolvedEverywhere _ h
      | cons B t rest => simp at hl
    cases sZ with
    | nil _ =>
      cases sW with
      | nil _ => simp at hlen
      | cons B' ts' rest' =>
        have hlen' : rest'.length + (MonoidalSuccession.nil Z).length = n := by
          simp at hlen ⊢; omega
        exact mergeStatement_step ih hX ℜ hℜ jW jZ hp.symm ts' rest' (MonoidalSuccession.nil Z)
          hlen' hW hWr hZ hZr (by rw [hν0Z hZr rfl]; exact zero_le)
    | cons B ts rest =>
      cases sW with
      | nil _ =>
        have hlen' : rest.length + (MonoidalSuccession.nil W).length = n := by
          simp at hlen ⊢; omega
        exact mergeStatement_step ih hX ℜ hℜ jZ jW hp ts rest (MonoidalSuccession.nil W)
          hlen' hZ hZr hW hWr (by rw [hν0W hWr rfl]; exact zero_le)
      | cons B' ts' rest' =>
        rcases le_total (ℜ.pullback jW).nu (ℜ.pullback jZ).nu with hle | hle
        · have hlen' : rest.length + (MonoidalSuccession.cons B' ts' rest').length = n := by
            simp at hlen ⊢; omega
          exact mergeStatement_step ih hX ℜ hℜ jZ jW hp ts rest
            (MonoidalSuccession.cons B' ts' rest') hlen' hZ hZr hW hWr hle
        · have hlen' : rest'.length + (MonoidalSuccession.cons B ts rest).length = n := by
            simp at hlen ⊢; omega
          exact mergeStatement_step ih hX ℜ hℜ jW jZ hp.symm ts' rest'
            (MonoidalSuccession.cons B ts rest) hlen' hW hWr hZ hZr hle

/-! ### The decomposition of a non-singular algebraic scheme into its irreducible components -/

section Decomposition

variable {X : Scheme.{u}}

/-- A decomposition of `X` into `n` pairwise disjoint open pieces, each an irreducible scheme. -/
def IsIrreducibleDecomposition (n : ℕ) (F : Fin n → X.Opens) : Prop :=
  (∀ i, IrreducibleSpace (F i)) ∧ (∀ i j, i ≠ j → Disjoint (F i : Set X) (F j : Set X)) ∧
    ∀ x : X, ∃ i, x ∈ F i

theorem isNonsingular_bot_of_isNonsingular (hX : X.IsNonsingular) :
    (⊥ : Subscheme X).IsNonsingular :=
  Subscheme.isNonsingular_of_stalk_quot _ fun x _ => by
    have : IsRegularLocalRing (X.presheaf.stalk x) := hX x
    rw [Subscheme.stalkIdeal_bot_eq]
    exact IsRegularLocalRing.of_ringEquiv (RingEquiv.quotientBot (X.presheaf.stalk x)).symm

/-- A non-singular algebraic scheme is the disjoint union of its finitely many irreducible
components, which are open (its local rings are domains, so the components are disjoint).

Deviation from the paper (gap filled): "As is easily seen, the proof of the main theorem can be
reduced to the case in which `X` is irreducible" (p. 176): the reduction uses this decomposition. -/
@[blueprint "lem:I.3-main-II-decomposition"
  (statement := /-- A non-singular algebraic scheme $X$ is the disjoint union of finitely many open
    subschemes, each of which is an irreducible scheme (its irreducible components). -/)
  (proof := /-- $X$ is noetherian, so it has finitely many irreducible components. The local rings
    of $X$ are domains, so a point lies on only one component, i.e.\ the components are pairwise
    disjoint; hence each one is the complement of the (closed) union of the others, so it is open.
    \textbf{Gap filled.} Used tacitly on p.~176. -/)
  (latexEnv := "lemma")]
theorem exists_irreducibleDecomposition [IsAlgebraicScheme X] (hX : X.IsNonsingular) :
    ∃ (n : ℕ) (F : Fin n → X.Opens), IsIrreducibleDecomposition n F := by
  classical
  have := IsAlgebraicScheme.noetherianSpace X
  have hbot : (⊥ : Subscheme X).pts = Set.univ := by
    change ((⊥ : Scheme.IdealSheafData X).support : Set X) = _
    rw [Scheme.IdealSheafData.support_bot]
    rfl
  obtain ⟨α, C, hC, hinj, hcov⟩ := Subscheme.exists_family_irreducibleComponents (⊥ : Subscheme X)
  have hdis : ∀ i j, i ≠ j → Disjoint (C i).pts (C j).pts := fun i j hij =>
    Subscheme.disjoint_pts_of_mem_irreducibleComponents (isNonsingular_bot_of_isNonsingular hX)
      (hC i) (hC j) (fun h => hij (hinj h))
  have hunion : ∀ x : X, ∃ i, x ∈ (C i).pts := fun x => by
    have hx : x ∈ (⊥ : Subscheme X).pts := by rw [hbot]; trivial
    obtain ⟨G, hG, hxG⟩ := Subscheme.exists_mem_irreducibleComponents_of_mem_pts _ hx
    obtain ⟨i, rfl⟩ := hcov G hG
    exact ⟨i, hxG⟩
  have hopen : ∀ i, IsOpen (C i).pts := fun i => by
    have : (C i).pts = (⋃ j ∈ Finset.univ.erase i, (C j).pts)ᶜ := by
      ext x
      simp only [Set.mem_compl_iff, Set.mem_iUnion, Finset.mem_erase, Finset.mem_univ, and_true,
        exists_prop, not_exists, not_and]
      constructor
      · intro hx j hj hxj
        exact Set.disjoint_left.mp (hdis i j (Ne.symm hj)) hx hxj
      · intro h
        obtain ⟨j, hj⟩ := hunion x
        by_cases hji : j = i
        · exact hji ▸ hj
        · exact absurd hj (h j hji)
    rw [this]
    exact (isClosed_biUnion_finset fun j _ => (C j).support.isClosed).isOpen_compl
  refine ⟨α, fun i => ⟨(C i).pts, hopen i⟩, fun i => ?_, fun i j hij => hdis i j hij, hunion⟩
  have hirr : _root_.IsIrreducible (C i).pts :=
    Subscheme.isIrreducible_pts _ (Subscheme.isIrreducible_of_mem_irreducibleComponents (hC i))
  exact Subtype.irreducibleSpace (s := (C i).pts) hirr

/-- The irreducible case of the dimension: a non-empty open subscheme of dimension at most `N` of
an algebraic scheme is of dimension a natural number at most `N`. -/
theorem exists_nat_dim_of_isOpenImmersion {V : Scheme.{u}} (j : V ⟶ X) [IsOpenImmersion j]
    [Nonempty V] {N : ℕ} (hdim : X.dim ≤ (N : WithBot ℕ∞)) :
    ∃ m : ℕ, V.dim = (m : WithBot ℕ∞) ∧ m ≤ N := by
  obtain ⟨z⟩ := ‹Nonempty V›
  have hdimle : V.dim ≤ (N : WithBot ℕ∞) :=
    (LocSucc.dim_le_of_forall j fun z => LocSucc.dimAt_le_dim _).trans hdim
  have hne : V.dim ≠ ⊥ := by
    intro hb
    have h1 : V.dimAt z ≤ V.dim := LocSucc.dimAt_le_dim z
    have h2 : (0 : WithBot ℕ∞) ≤ V.dimAt z := ringKrullDim_nonneg_of_nontrivial
    rw [hb] at h1
    exact absurd (h2.trans h1) (by simp)
  exact LocSucc.exists_nat_of_le hne hdimle

/-- **Theorem `II₂` for a decomposable scheme.**  If `X` is a non-singular algebraic scheme of
dimension at most `N` which is the disjoint union of `n` open irreducible schemes, and the
fundamental theorems `II₂^{N'}` hold, then every datum on `X` has a permissible succession which
resolves it.  By induction on `n`, interleaving the successions of the pieces
(`mergeStatement`). -/
theorem exists_isPermissibleII_resolvedEverywhere_of_decomposition [Hironaka.Cited.IsHironakaBaseIsClosedSingularLocus.{u}] [Hironaka.Cited.MonoidalTransformationExistsIsProper.{u}] [Hironaka.Cited.CurveFiniteIntegralClosure.{u}] [Hironaka.Cited.IsRegularLocalRingLocalizationOfIsRegularLocalRing.{u}]
    (hII : ∀ N, FundamentalTheorem.II₂.{u} N) {N : ℕ} :
    ∀ (n : ℕ) {X : Scheme.{u}} [IsAlgebraicScheme X], X.IsNonsingular →
      X.dim ≤ (N : WithBot ℕ∞) → ∀ (F : Fin n → X.Opens), IsIrreducibleDecomposition n F →
      ∀ ℜ : DatumII.Raw X, ℜ.IsDatum →
        ∃ (Y : Scheme.{u}) (s : MonoidalSuccession X Y),
          s.IsPermissibleII ℜ ∧ (s.transformII ℜ).ResolvedEverywhere := by
  intro n
  induction n with
  | zero =>
    intro X _ hX hdim F hF ℜ hℜ
    have : IsEmpty X := ⟨fun x => by obtain ⟨i, -⟩ := hF.2.2 x; exact i.elim0⟩
    exact ⟨X, MonoidalSuccession.nil X, trivial, fun x => (IsEmpty.false x).elim⟩
  | succ n ih =>
    intro X _ hX hdim F hF ℜ hℜ
    classical
    -- the pieces: `F 0` and the union of the others
    set Wo : X.Opens := ⨆ i : Fin n, F i.succ with hWo
    have hF0 : IrreducibleSpace (F 0) := hF.1 0
    have hZa : IsAlgebraicScheme (F 0).toScheme := isAlgebraicScheme_of_isOpenImmersion (F 0).ι
    have hWa : IsAlgebraicScheme Wo.toScheme := isAlgebraicScheme_of_isOpenImmersion Wo.ι
    have hZns : (F 0).toScheme.IsNonsingular := LocSucc.isNonsingular (F 0).ι hX
    have hWns : Wo.toScheme.IsNonsingular := LocSucc.isNonsingular Wo.ι hX
    have hp : ClopenPair (F 0).ι Wo.ι := by
      refine ⟨?_, ?_, ?_, ?_⟩
      · rw [Scheme.Opens.range_ι]; exact (F 0).isOpen
      · rw [Scheme.Opens.range_ι]; exact Wo.isOpen
      · rw [Scheme.Opens.range_ι, Scheme.Opens.range_ι]
        refine Set.eq_univ_of_forall fun x => ?_
        obtain ⟨i, hi⟩ := hF.2.2 x
        rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨j, rfl⟩
        · exact Or.inl hi
        · exact Or.inr (TopologicalSpace.Opens.mem_iSup.mpr ⟨j, hi⟩)
      · rw [Scheme.Opens.range_ι, Scheme.Opens.range_ι]
        refine Set.disjoint_left.mpr fun x hx0 hxW => ?_
        obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.mp hxW
        exact Set.disjoint_left.mp (hF.2.1 0 j.succ (Fin.succ_ne_zero j).symm) hx0 hj
    -- the irreducible piece, by the fundamental theorem `II₂`
    have : Nonempty (F 0) := hF0.toNonempty
    obtain ⟨m, hm, -⟩ := exists_nat_dim_of_isOpenImmersion (F 0).ι hdim
    have hamb : IsAmbient (F 0).toScheme m := ⟨hZa, hZns, hF0, hm⟩
    obtain ⟨Z₁, sZ, hsZ, hrZ⟩ := hII m (F 0).toScheme hamb
      ⟨ℜ.pullback (F 0).ι, DatumII.Raw.isDatum_pullback (F 0).ι hℜ⟩
    -- the remaining pieces, by induction
    have hdecW : IsIrreducibleDecomposition n (fun i : Fin n => Wo.ι ⁻¹ᵁ F i.succ) := by
      refine ⟨fun i => ?_, fun i j hij => ?_, fun y => ?_⟩
      · have hirr : _root_.IsIrreducible (F i.succ : Set X) := by
          have := (@IrreducibleSpace.isIrreducible_univ _ _ (hF.1 i.succ)).image Subtype.val
            continuous_subtype_val.continuousOn
          convert this using 1
          ext x
          exact ⟨fun hx => ⟨⟨x, hx⟩, trivial, rfl⟩, fun h => by
            obtain ⟨y, -, rfl⟩ := h
            exact y.2⟩
        have hsub : (F i.succ : Set X) ⊆ Set.range Wo.ι.base := by
          rw [Scheme.Opens.range_ι]
          exact (le_iSup (fun i : Fin n => F i.succ) i :)
        exact Subtype.irreducibleSpace
          (s := ((Wo.ι ⁻¹ᵁ F i.succ : Wo.toScheme.Opens) : Set Wo.toScheme))
          (isIrreducible_preimage_of_isInducing Wo.ι.isOpenEmbedding.isInducing hirr hsub)
      · refine Set.disjoint_left.mpr fun y hy1 hy2 => ?_
        exact Set.disjoint_left.mp (hF.2.1 i.succ j.succ
          (fun h => hij (Fin.succ_injective _ h))) hy1 hy2
      · have : Wo.ι.base y ∈ Wo := y.2
        obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp this
        exact ⟨i, hi⟩
    obtain ⟨W₁, sW, hsW, hrW⟩ := ih hWns ((LocSucc.dim_le_of_forall Wo.ι
      fun z => LocSucc.dimAt_le_dim _).trans hdim) _ hdecW (ℜ.pullback Wo.ι)
      (DatumII.Raw.isDatum_pullback Wo.ι hℜ)
    exact mergeStatement _ hX ℜ hℜ (F 0).ι Wo.ι hp sZ sW rfl hsZ hrZ hsW hrW

/-- **Theorem `II₂` for a non-singular algebraic scheme which is not necessarily irreducible**
(the reduction "easily seen" on p. 176): if the fundamental theorems `II₂^{N'}` hold, then every
resolution datum of type `ℜ^N_II` on a non-singular algebraic scheme `X` of dimension at most `N`
has a permissible succession of monoidal transformations which resolves it.

Deviation from the paper (gap filled): "As is easily seen, the proof of the main theorem can be
reduced to the case in which `X` is irreducible" (p. 176).  Lean: `X` is the disjoint union of its
irreducible components (`exists_irreducibleDecomposition`), each of which has a permissible
succession resolving the restriction of `ℜ` by `II₂`, and by induction on their number these
successions are interleaved (`mergeStatement`). -/
@[blueprint "lem:I.3-main-II-components"
  (statement := /-- Assume the fundamental theorems $\mathrm{II}_2^{N'}$. Let $X$ be a
    non-singular algebraic scheme (not necessarily irreducible) of dimension at most $N$ and
    $\mathfrak R$ a resolution datum of type $\mathfrak R^N_{\mathrm{II}}$ on $X$. Then there is a
    finite succession of monoidal transformations of $X$, permissible for $\mathfrak R$, such that
    $f^*(\mathfrak R)$ is resolved everywhere. (The reduction of main theorem II($N$) to the case in
    which $X$ is irreducible, p.~176.) -/)
  (proof := /-- $X$ is the disjoint union of its irreducible components
    (\cref{lem:I.3-main-II-decomposition}), finitely many. Induction on their number: the first
    component $Z$ is irreducible (an ambient scheme of some dimension $\le N$), so by
    $\mathrm{II}_2$ the restriction $\mathfrak R|_Z$ has a permissible succession which resolves
    it; the union $W$ of the others has fewer components, so by induction the same holds for
    $\mathfrak R|_W$; the successions are interleaved by \cref{lem:I.3-main-II-merge}.

    \textbf{Deviation from the paper (gap filled).} ``As is easily seen, the proof of the main
    theorem can be reduced to the case in which $X$ is irreducible'' (p.~176). -/)
  (proofUses := ["thm:I.2-II2", "lem:I.3-main-II-decomposition", "lem:I.3-main-II-merge"])
  (latexEnv := "lemma")]
theorem exists_isPermissibleII_resolvedEverywhere_of_isNonsingular [Hironaka.Cited.IsHironakaBaseIsClosedSingularLocus.{u}] [Hironaka.Cited.MonoidalTransformationExistsIsProper.{u}] [Hironaka.Cited.CurveFiniteIntegralClosure.{u}] [Hironaka.Cited.IsRegularLocalRingLocalizationOfIsRegularLocalRing.{u}]
    (hII : ∀ N, FundamentalTheorem.II₂.{u} N) {N : ℕ} {X : Scheme.{u}} [IsAlgebraicScheme X]
    (hX : X.IsNonsingular) (hdim : X.dim ≤ (N : WithBot ℕ∞)) (ℜ : DatumII.Raw X)
    (hℜ : ℜ.IsDatum) :
    ∃ (Y : Scheme.{u}) (s : MonoidalSuccession X Y),
      s.IsPermissibleII ℜ ∧ (s.transformII ℜ).ResolvedEverywhere := by
  obtain ⟨n, F, hF⟩ := exists_irreducibleDecomposition hX
  exact exists_isPermissibleII_resolvedEverywhere_of_decomposition hII n hX hdim F hF ℜ hℜ

end Decomposition

end Hironaka
