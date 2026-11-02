/-
Copyright (c) 2026 Daattavya Aggarwal, Minhyong Kim, Oisin Kim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daattavya Aggarwal, Minhyong Kim, Oisin Kim
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.Data.List.GetD
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Architect
public import Hironaka.Ch4.StageState
public import Hironaka.Ch4.TheoremsAStarBStar
public import Hironaka.Ch4.AStarBStarAssembly
public import Hironaka.Ch4.LiftingTrivial
public import Hironaka.Ch4.LiftingOpen
public import Hironaka.Statements

/-!
# The one-block lemma (pp. 309–310)

> By applying Theorem I₂^{N,n'} (with n' < n) to the resolution datum (ℜ^{N,n'}_I(s), U_s), we can
> resolve ℜ^{N,n'}_I(s) by a finite permissible succession of monoidal transformations for
> (ℜ^{N,n'}_I(s), U_s).  These monoidal transformations are successively permissible for ℜ(s) and
> induce trivial monoidal transformations of X̃ by Remarks 4 and 5.  Therefore, by replacing the
> original succession g_s : X_s → X to include the above succession, we may assume that the
> monoidal transformation with center B_s is permissible for ℜ(s), while the scheme X̃ and the
> datum ℜ^{N-1} are kept the same.  Then the permissible monoidal transformation f_{B_s} of X_s with
> center B_s for ℜ(s) induces the given permissible monoidal transformation f_{B̃} of X̃ for
> ℜ^{N-1}_II. (p. 310)

This file proves the lemma that this paragraph is used for in the induction on the length of the
resolving succession of `X̃` (`AB.exists_extension_of_stageResolvable_succ`, whose statement is the
hypothesis `OneBlockHyp` of `Hironaka.Ch4.AStarBStarAssembly`): if the emptied auxiliary datum
`ℜ^{N-1}_II` of the stage `g` (p. 308, with the repair of the paper's error on the subschemes `Ẽ_j`) is
resolvable by `k + 1` monoidal transformations, then either it is resolvable by `k` at the same
stage (the first center is empty), or `g` has a permissible extension `g ++ e` at which, if `x_0`
is still in the image of `S`, it is resolvable by `k`.  The extension `e` is the succession `h`
given by Theorem `I₂^{N,n'}` followed by the monoidal transformation with center the strict
transform `B'` of `B_s`.

The proof is assembled from the following steps.
* `exists_succession_of_isOpenRestriction_extendBy`: the succession `h`, its permissibility for
  `ℜ(s)` (Remark 5 at the level of successions), and the permissibility of `B'`.
* `Frame.RemovalFamily.totalTransform_cTilde_eq`: `c̃⁻¹(B_s) = B̃`.
* `Frame.blowupHyp_stageOf`, `Frame.datum_facts_stageOf`: the hypotheses of the blow-up step at the
  stage of a frame (Lemma (AB.6)), used at the stage `g ++ h` (a standing tower exists for it,
  `exists_standing_prepHyp_of_prepHypSucc`).
* `StageState.auxResolvable_fold_snoc_of_isPermissibleIOpen_extendBy`: the trivial steps of `h`
  (`StageState.exists_iso_xTilde_fold_of_isPermissibleIOpen_extendBy`), the transport of the
  emptied datum (`StageState.sameChar_datumII_emptyIfBot_of_iso`,
  `DatumII.Raw.resolvableLen_transform_of_sameChar_pullback`) and the blow-up step
  (`StageState.auxResolvable_step_of_blowupHyp`).
-/

@[expose] public section

open AlgebraicGeometry IsLocalRing CategoryTheory CategoryTheory.Limits

namespace Hironaka

universe u

noncomputable section

namespace DatumII.Raw

/-- **Transport of a resolving step along a surjective flat preimmersion** (p. 310: the
permissible monoidal transformation `f_{B̃}` of `X̃` for `ℜ^{N-1}_II` is "the given" one): if
`ℜ.transform t` is resolvable by `k` monoidal transformations, then so is `ℜ'.transform t'` for
any datum `ℜ'` with the same characteristics as the pull-back of `ℜ` along `j`, and any monoidal
transformation `t'` with the total transform of the center. -/
theorem resolvableLen_transform_of_sameChar_pullback {Y Z : Scheme.{u}} (j : Z ⟶ Y) [Flat j]
    [IsPreimmersion j] (hj : Function.Surjective j.base) {B : Subscheme Y} (ℜ : Raw Y)
    (ℜ' : Raw Z) (hsc : SameChar (ℜ.pullback j) ℜ') (t : MonoidalTransformation Y B)
    (t' : MonoidalTransformation Z (Subscheme.totalTransform j B)) (k : ℕ)
    (h : ResolvableLen k (ℜ.transform t)) : ResolvableLen k (ℜ'.transform t') := by
  obtain ⟨j', hfl, hpre, hsq, hrange, hexc, hst⟩ := MonoidalTransformation.exists_lift t j
    (rfl : Subscheme.totalTransform j B = Subscheme.totalTransform j B) (t.baseChange j)
  have := hfl
  have := hpre
  have hcont : ∀ i, B.IsContainedIn (ℜ.E i) ↔
      (Subscheme.totalTransform j B).IsContainedIn (Subscheme.totalTransform j (ℜ.E i)) :=
    fun i => ((FlatPreimm.totalTransform_le_iff j hj).trans Iff.rfl).symm
  have hT := pullback_transform_of_lift t j (t.baseChange j) j' hsq hexc hst ℜ hcont
    (nu_pullback_eq_of_surjective j hj ℜ)
  have hj' : Function.Surjective j'.base := by
    rw [← Set.range_eq_univ, hrange, Set.range_eq_univ.mpr hj, Set.preimage_univ]
  have h1 := resolvableLen_pullback_of_surjective k j' hj' _ h
  rw [hT] at h1
  have h2 := resolvableLen_of_sameChar k (hsc.transform (t.baseChange j)) h1
  exact resolvableLen_transform_congr (t.baseChange j) t' ℜ' k h2

end DatumII.Raw

namespace AB

section PermissibleCenter

variable {Y : Scheme.{u}}

/-- p. 310 (Remark 5, last clause): "if `ℜ^{N,n'}_I(s)` is resolved at every point of `B_s`, then
the monoidal transformation of `X_s` with center `B_s` is permissible for `ℜ(s)`", for any datum:
the center `B` is reduced, irreducible, contained in `W` and in `W*`, and the extended tuple
`(E; V_1, …, V_β, W; B)` is resolved everywhere. -/
theorem isPermissibleCenter_of_resolvedEverywhere_extendBy {ℜ' : DatumI.Raw Y}
    {r : Restriction Y} (hℜ : ℜ'.IsDatum) {B : Subscheme Y} (hBred : B.IsReduced)
    (hBirr : B.IsIrreducible) (hBW : B.IsContainedIn ℜ'.W) (hBw : B.pts ⊆ wStar ℜ' r)
    (hres : (ℜ'.extendBy B).ResolvedEverywhere) : r.IsPermissibleCenter ℜ' B := by
  have hperm : ℜ'.IsPermissible B := by
    refine ⟨Or.inr ⟨?_, hBirr⟩, isDatum_extendBy_of_isContainedIn hℜ hBred hBW, hres⟩
    exact Subscheme.isNonsingular_of_stalk_quot B fun z hz => (hres z hz).1.2
  cases r with
  | closed F => exact ⟨hperm, hBw⟩
  | opn U => exact ⟨hperm, hBw⟩

end PermissibleCenter

section Dim

/-- An element `d ≠ ⊥` of `WithBot ℕ∞` with `d < n` is a natural number `< n`. -/
theorem _root_.Hironaka.exists_natCast_eq_of_lt_natCast {d : WithBot ℕ∞} {n : ℕ} (hne : d ≠ ⊥)
    (h : d < (n : WithBot ℕ∞)) :
    ∃ m : ℕ, d = m ∧ m < n := by
  induction d using WithBot.recBotCoe with
  | bot => exact absurd rfl hne
  | coe e =>
    induction e using ENat.recTopCoe with
    | top =>
      exfalso
      have h' : ((⊤ : ℕ∞) : WithBot ℕ∞) < ((n : ℕ∞) : WithBot ℕ∞) := by exact_mod_cast h
      rw [WithBot.coe_lt_coe] at h'
      exact absurd h' (by simp)
    | coe m =>
      refine ⟨m, rfl, ?_⟩
      have h' : ((m : ℕ) : WithBot ℕ∞) < (n : WithBot ℕ∞) := by exact_mod_cast h
      exact_mod_cast h'

end Dim

section StageOne

variable {X Y Z : Scheme.{u}}

/-- The centers of a succession permissible for `((E; V, W; B), Us)` avoid `U₀`, if `B ∩ U₀ ⊆ Us`
(each center lies in `B − Us`, and this persists for the strict transform of `B` and the
preimage of `U₀`). -/
theorem _root_.Hironaka.MonoidalSuccession.centersAvoid_of_isPermissibleIOpen_extendBy
    (s : MonoidalSuccession X Y) :
    ∀ (ℜ : DatumI.Raw X) (B : Subscheme X) (U₀ Us : Set X),
      s.IsPermissibleIOpen (ℜ.extendBy B) Us → B.pts ∩ U₀ ⊆ Us → s.CentersAvoid U₀ := by
  induction s with
  | nil X => intros; trivial
  | cons C t rest ih =>
    intro ℜ B U₀ Us hs hU
    obtain ⟨⟨hC, hCW⟩, hrest⟩ := hs
    refine ⟨fun y hy hyU => ?_, ?_⟩
    · have := hCW hy
      exact this.2 (hU ⟨this.1, hyU⟩)
    · rw [DatumI.Raw.transform_extendBy] at hrest
      refine ih (ℜ.transform t) (Subscheme.strictTransform t B) (t.f.base ⁻¹' U₀)
        (DatumI.Raw.transformOpen t Us) hrest ?_
      intro y hy
      exact hU ⟨MonoidalTransformation.pts_strictTransform_subset t B hy.1, hy.2⟩

/-- p. 280 ("`B*` is irreducible"), as used on p. 310: the strict transform of the irreducible `B`
along a succession permissible for `((E; V, W; B), U₀ ∩ B)`, `U₀` open meeting `B`, is
irreducible: the centers avoid `U₀`, and `U₀ ∩ B` is a non-empty open part of `B` that the strict
transform keeps. -/
theorem _root_.Hironaka.MonoidalSuccession.isIrreducible_strictTransform_of_isPermissibleIOpen
    (s : MonoidalSuccession X Y) (ℜ : DatumI.Raw X) (B : Subscheme X) (U₀ : Set X)
    (hU₀ : IsOpen U₀) (hs : s.IsPermissibleIOpen (ℜ.extendBy B) (U₀ ∩ B.pts))
    (hB : B.IsIrreducible) (hne : (U₀ ∩ B.pts).Nonempty) : (s.strictTransform B).IsIrreducible := by
  let U : X.Opens := ⟨U₀, hU₀⟩
  have hav : s.CentersAvoid (Set.range U.ι.base) := by
    rw [Scheme.Opens.range_ι]
    exact MonoidalSuccession.centersAvoid_of_isPermissibleIOpen_extendBy s ℜ B U₀ _ hs
      fun y hy => ⟨hy.2, hy.1⟩
  refine MonoidalSuccession.strictTransform_isIrreducible_of_centersAvoid s U.ι hav B hB ?_
  obtain ⟨y, hy1, hy2⟩ := hne
  rw [FlatPreimm.pts_totalTransform]
  exact ⟨⟨y, hy1⟩, hy2⟩

/-- **The succession of p. 310** ("By applying Theorem `I₂^{N,n'}` (with `n' < n`) to the resolution
datum `(ℜ^{N,n'}_I(s), U_s)` … we can resolve `ℜ^{N,n'}_I(s)` by a finite permissible succession …
These monoidal transformations are successively permissible for `ℜ(s)`", and "we may assume that
the monoidal transformation with center `B_s` is permissible for `ℜ(s)`"): for a reduced irreducible
`B_s ⊆ W(s) ∩ W*(s)` of dimension `< n` and an open restriction `U_s` of the extended datum, there
is a succession `h` permissible for `(ℜ^{N,n'}_I(s), U_s)`, hence for `ℜ(s)` (Remark 5), after which
the strict transform of `B_s` is irreducible and the monoidal transformation with this center is
permissible.

Deviation from the paper (gap filled): the paper (p. 310) says "These monoidal transformations are
successively permissible for `ℜ(s)` and induce trivial monoidal transformations of `X̃` by Remarks 4
and 5.  Therefore, by replacing the original succession `g_s : X_s → X` to include the above
succession, we may assume that the monoidal transformation with center `B_s` is permissible for
`ℜ(s)`".  Lean: the centers of `h` lie in `B_s − U_s`, hence `h` is permissible for `ℜ(s)`
(`isPermissibleIClosed_of_isPermissibleIOpen_extendBy`,
`isPermissibleIOpen_of_isPermissibleIOpen_extendBy`); they avoid the open set `U_0` with
`U_s = U_0 ∩ B_s`, so the strict transform `B'` of `B_s` is irreducible (p. 280, "`B*` is
irreducible"); and `B'` is a permissible center because `h*ℜ^{N,n'}_I(s) = (E'; V', W'; B')` is
resolved everywhere (the last clause of Remark 5,
`isPermissibleCenter_of_resolvedEverywhere_extendBy`).  After the replacement, "the monoidal
transformation with center `B_s`" is the one with center `B'`. -/
@[blueprint "lem:IV.3-one-block-succession"
  (statement := /-- Notation as in \cref{rem:IV.3-4-generic} and \cref{rem:IV.3-5-generic}, and
    assume Theorems $\mathrm I_2^{N,n''}$ for all $n''<n$. Let $g$ be a permissible succession for
    $(\mathfrak R,r)$ and $B_s$ a reduced irreducible subscheme of $X_s$ contained in $W(s)$ and in
    $W^*(s)$ with $n'=\dim B_s<n$, and let $U_s=U_0\cap B_s\ne\emptyset$ be an open restriction of
    $\mathfrak R^{N,n'}_{\mathrm I}(s)=(E(s);V_1(s),\dots,V_\beta(s),W(s);B_s)$. Then there is a
    finite succession $h$ of monoidal transformations of $X_s$, permissible for $(\mathfrak
    R^{N,n'}_{\mathrm I}(s),U_s)$, such that $g\cdot h$ is permissible for $(\mathfrak R,r)$, the
    strict transform $B'$ of $B_s$ by $h$ is irreducible, and the monoidal transformation with
    center $B'$ is permissible for $(g\cdot h)^*(\mathfrak R,r)$. -/)
  (proof := /-- Theorem $\mathrm I_2^{N,n'}$ gives a succession $h$ permissible for $(\mathfrak
    R^{N,n'}_{\mathrm I}(s),U_s)$ such that $h^*\mathfrak R^{N,n'}_{\mathrm I}(s)$ is resolved
    everywhere. Each center of $h$ is permissible for $\mathfrak R(s)$ and lies in $B_s-U_s\subseteq
    W(s)\cap W^*(s)$, so $h$ is permissible for $(g^*\mathfrak R,r)$. The centers avoid $U_0$, so
    the strict transform $B'$ of the irreducible $B_s$ stays irreducible (p.~280). Finally $B'$ lies
    in $W'\cap W'^*$ and $h^*\mathfrak R^{N,n'}_{\mathrm I}(s)=(E';V',W';B')$ is resolved
    everywhere, so the monoidal transformation with center $B'$ is permissible (the last clause of
    Remark~5).

    \textbf{Deviation from the paper (gap filled).} The paper (p.~310): ``These monoidal
    transformations are successively permissible for $\mathfrak R(s)$ and induce trivial monoidal
    transformations of $\tilde X$ by Remarks 4 and 5. Therefore, by replacing the original
    succession $g_s\colon X_s\to X$ to include the above succession, we may assume that the monoidal
    transformation with center $B_s$ is permissible for $\mathfrak R(s)$'' does not say that, after
    the replacement, the center is the strict transform $B'$ of $B_s$, that it is irreducible, and
    why it is permissible. -/)
  (proofUses := ["thm:I.2-I2", "rem:IV.3-5-generic"])
  (latexEnv := "lemma")]
theorem exists_succession_of_isOpenRestriction_extendBy [Hironaka.HironakaCitedResults.{u}]
    {N n : ℕ} (hI₂ : ∀ n'' : ℕ, n'' < n → FundamentalTheorem.I₂.{u} N n'')
    {X Y : Scheme.{u}} {ℜ : DatumI.Raw X} {r : Restriction X}
    (hgood : IsGoodDatumI N n X ℜ) (hr : r.IsFor ℜ) (g : MonoidalSuccession X Y)
    (hg : r.IsPermissibleSucc g ℜ) {Bs : Subscheme Y} (hBsred : Bs.IsReduced)
    (hBsirr : Bs.IsIrreducible) (hBsW : Bs.IsContainedIn (g.transformI ℜ).W)
    (hBsr : Bs.pts ⊆ wStar (g.transformI ℜ) (r.transformSucc g))
    (hdim : Bs.dim < (n : WithBot ℕ∞)) {Us : Set Y}
    (hOR : ((g.transformI ℜ).extendBy Bs).IsOpenRestriction Us) (hne : Us.Nonempty) :
    ∃ (Z : Scheme.{u}) (h : MonoidalSuccession Y Z),
      h.IsPermissibleIOpen ((g.transformI ℜ).extendBy Bs) Us ∧
      r.IsPermissibleSucc (g.append h) ℜ ∧
      (h.strictTransform Bs).IsIrreducible ∧
      (r.transformSucc (g.append h)).IsPermissibleCenter ((g.append h).transformI ℜ)
        (h.strictTransform Bs) := by
  classical
  obtain ⟨hgoods, hfor⟩ := isGoodDatumI_transformI_and_isFor_transformSucc g hgood hr hg
  have hdat : ((g.transformI ℜ).extendBy Bs).IsDatum :=
    isDatum_extendBy_of_isContainedIn hgoods.2.1 hBsred hBsW
  have hOR' := hOR
  obtain ⟨⟨U₀, hU₀, hUs⟩, -, -⟩ := hOR
  subst hUs
  have hBsne : Bs.pts.Nonempty := by
    obtain ⟨y, hy⟩ := hne
    exact ⟨y, hy.2⟩
  obtain ⟨n', hn'eq, hn'lt⟩ := exists_natCast_eq_of_lt_natCast (Subscheme.dim_ne_bot hBsne) hdim
  have hgood_ext : IsGoodDatumI N n' Y ((g.transformI ℜ).extendBy Bs) :=
    ⟨hgoods.1, hdat, hn'eq.le⟩
  obtain ⟨Z, h, hh, hres⟩ := hI₂ n' hn'lt Y hgoods.1
    ⟨(g.transformI ℜ).extendBy Bs, hdat⟩ (U₀ ∩ Bs.pts) hOR' hn'eq
  have hhr : (r.transformSucc g).IsPermissibleSucc h (g.transformI ℜ) := by
    cases r with
    | closed F =>
      have hBsr' : Bs.pts ⊆ (g.transformI ℜ).W.pts ∩ (g.strictTransform F).pts := hBsr
      exact MonoidalSuccession.isPermissibleIClosed_of_isPermissibleIOpen_extendBy h _ Bs _
        _ hh hBsW (Subscheme.isContainedIn_of_pts_subset hBsred fun y hy => (hBsr' hy).2)
    | opn U =>
      have hBsr' : Bs.pts ⊆ (g.transformI ℜ).W.pts \ g.transformOpen U := hBsr
      exact MonoidalSuccession.isPermissibleIOpen_of_isPermissibleIOpen_extendBy h _ Bs _ _
        hh hBsW fun y hy => absurd hy.2 (hBsr' hy.1).2
  refine ⟨Z, h, hh, (Restriction.isPermissibleSucc_append r g h ℜ).mpr ⟨hg, hhr⟩, ?_, ?_⟩
  · exact MonoidalSuccession.isIrreducible_strictTransform_of_isPermissibleIOpen h _ Bs
      U₀ hU₀ hh hBsirr hne
  · obtain ⟨hgoods', -⟩ := isGoodDatumI_transformI_and_isFor_transformSucc h hgoods hfor hhr
    have hBred : (h.strictTransform Bs).IsReduced := by
      have := (IsGoodDatumI.succession_open h hgood_ext hOR' hh).1.2.1.2.2.2.1
      rwa [MonoidalSuccession.transformI_W] at this
    have hBirr : (h.strictTransform Bs).IsIrreducible :=
      MonoidalSuccession.isIrreducible_strictTransform_of_isPermissibleIOpen h _ Bs
        U₀ hU₀ hh hBsirr hne
    have hBW : (h.strictTransform Bs).IsContainedIn (h.transformI (g.transformI ℜ)).W := by
      rw [MonoidalSuccession.transformI_W]
      exact MonoidalSuccession.isContainedIn_strictTransform h hBsW
    have hres' : ((h.transformI (g.transformI ℜ)).extendBy
        (h.strictTransform Bs)).ResolvedEverywhere := by
      rw [← MonoidalSuccession.transformI_extendBy]
      exact hres
    rw [Restriction.transformSucc_append, MonoidalSuccession.transformI_append]
    cases r with
    | closed F =>
      have hBsr' : Bs.pts ⊆ (g.transformI ℜ).W.pts ∩ (g.strictTransform F).pts := hBsr
      have hBsF : Bs.IsContainedIn (g.strictTransform F) :=
        Subscheme.isContainedIn_of_pts_subset hBsred fun y hy => (hBsr' hy).2
      exact isPermissibleCenter_of_resolvedEverywhere_extendBy hgoods'.2.1 hBred hBirr hBW
        (fun y hy => ⟨pts_subset_of_isContainedIn hBW hy, pts_subset_of_isContainedIn
          (MonoidalSuccession.isContainedIn_strictTransform h hBsF) hy⟩) hres'
    | opn U =>
      have hBsr' : Bs.pts ⊆ (g.transformI ℜ).W.pts \ g.transformOpen U := hBsr
      exact isPermissibleCenter_of_resolvedEverywhere_extendBy hgoods'.2.1 hBred hBirr hBW
        (fun y hy => ⟨pts_subset_of_isContainedIn hBW hy, fun hyU => by
          rw [MonoidalSuccession.transformOpen_eq] at hyU
          exact (hBsr' (MonoidalSuccession.pts_strictTransform_subset h Bs hy)).2 hyU⟩) hres'

end StageOne

section CoreStep

variable {Y : Scheme.{u}}

/-- **One blow-up step of the induction on `k`** (p. 310: "the permissible monoidal transformation
`f_{B_s}` of `X_s` with center `B_s` for `ℜ(s)` induces the given permissible monoidal
transformation `f_{B̃}` of `X̃` for `ℜ^{N-1}_II`"): at a state `σ` satisfying the hypotheses
`BlowupHyp` for a center `B` with `B̃ = c̃⁻¹(B)`, if `B̃` is permissible for the emptied
auxiliary datum, which is resolvable by `k` further monoidal transformations after the blow-up of
`B̃`, then the emptied auxiliary datum of the next state is resolvable by `k`. -/
theorem StageState.auxResolvable_step_of_blowupHyp [Hironaka.HironakaCitedResults.{u}] (σ : StageState Y) (b : ℕ)
    {B : Subscheme Y} (t : MonoidalTransformation Y B) {hU : IsOpen σ.xHatPrimeStar}
    {Bt : Subscheme (σ.xTilde hU)} (H : σ.BlowupHyp b t hU Bt) {α₀ αT : ℕ}
    (hlen : σ.boundary.length = α₀ + αT) {a : Fin αT → ℕ} {Jt : Subscheme (σ.xTilde hU)}
    (ha : ∀ j : Fin αT, σ.eTildeAt hU (α₀ + j) = ⊥ → a j = 0)
    (hD : (σ.datumII hU b α₀ αT a Jt).emptyIfBot.IsWeakDatum)
    (hperm : (σ.datumII hU b α₀ αT a Jt).emptyIfBot.IsPermissible Bt)
    (hJt : Jt * ∏ j : Fin αT, (σ.eTildeAt hU (α₀ + j)) ^ (a j) = σ.jBarT hU)
    [IsAlgebraicScheme (σ.xTilde hU)] [IrreducibleSpace (σ.xTilde hU)]
    (hU' : IsOpen (σ.step b t).xHatPrimeStar) (k : ℕ)
    (hk : ∀ tT : MonoidalTransformation (σ.xTilde hU) Bt,
      DatumII.Raw.ResolvableLen k ((σ.datumII hU b α₀ αT a Jt).emptyIfBot.transform tT)) :
    (σ.step b t).AuxResolvable b α₀ k := by
  obtain ⟨f, hf, hmono, anew, Jt', hdat, hfac⟩ :=
    H.exists_transform_eq_datumII hlen ha hD hperm hJt hU'
  refine ⟨hU', αT + 1, ?_, Fin.snoc (α := fun _ => ℕ) a anew, Jt', hfac, ?_⟩
  · show (σ.boundary.map (Subscheme.strictTransform t) ++ [t.exceptional]).length = _
    simp [hlen]
    omega
  · show DatumII.Raw.ResolvableLen k ((σ.step b t).datumII hU' b α₀ (αT + 1)
      (Fin.snoc (α := fun _ => ℕ) a anew) Jt').emptyIfBot
    rw [← hdat, ← DatumII.Raw.emptyIfBot_transform_of_isPermissible H.nonsingular_xTilde _ hD ha
      hmono.toMonoidalTransformation hperm]
    exact hk _

end CoreStep

section FrameFacts

namespace Frame.RemovalFamily

variable {N n : ℕ} {X : Scheme.{u}} {ℜ : DatumI.Raw X} {P : DatumI.Presentation ℜ}
  {r : Restriction X} {T : Tower X} {x₀ : X} {hS : Standing N n ℜ P r T x₀} {𝒮 : Frame hS}
  (R : 𝒮.RemovalFamily)

/-- The total transform of `B_s = closure c_s(B̃)` by `c_s` is the closed subscheme
`ker(B̄ ↪ X̄_s ↪ X̂_s)` (Corollary of Lemma (AB.3), p. 296, for the closure `B̄` of `B̃` in `X̄_s`).
-/
theorem totalTransform_c_eq_ker {s : ℕ} (Bt : Subscheme (R.xTilde s))
    (hBti : Bt.IsIrreducible) (hg : ∀ xt ∈ Bt.pts, (R.gTilde s).base xt = hS.xh) :
    Subscheme.totalTransform (𝒮.c s) (Subscheme.ofClosed
      ⟨closure ((R.cTilde s).base '' Bt.pts), isClosed_closure⟩) =
      ((R.bb s Bt).ι ≫ (𝒮.xBar s).ι).ker := by
  classical
  have hirrBt : IsIrreducible Bt.pts := Subscheme.isIrreducible_pts Bt hBti
  set A : Set (𝒮.xBar s).toScheme := (R.uBar s).ι.base '' Bt.pts with hA
  have hAg : ((𝒮.xBar s).ι ≫ (𝒮.tHat.pre s).composite).base '' A = {hS.xh} := by
    refine Set.eq_singleton_iff_unique_mem.mpr ⟨?_, ?_⟩
    · obtain ⟨xt, hxt⟩ := hirrBt.nonempty
      exact ⟨(R.uBar s).ι.base xt, ⟨xt, hxt, rfl⟩, hg xt hxt⟩
    · rintro _ ⟨_, ⟨xt, hxt, rfl⟩, rfl⟩
      exact hg xt hxt
  have hBbpts : (R.bb s Bt).pts = closure A := R.pts_bb s Bt
  have hBbred : (R.bb s Bt).IsReduced := Subscheme.ofClosed_isReduced _
  let K : Subscheme (𝒮.tHat.X s) := ((R.bb s Bt).ι ≫ (𝒮.xBar s).ι).ker
  obtain ⟨e₀, he₀⟩ := Subscheme.exists_iso_ker ((R.bb s Bt).ι ≫ (𝒮.xBar s).ι)
  have hKred : Subscheme.IsReduced K := by
    have : IsReduced (R.bb s Bt).toScheme := hBbred
    exact isReduced_of_isOpenImmersion e₀.hom
  have hKpts : Subscheme.pts K = closure ((𝒮.xBar s).ι.base '' A) := by
    have h1 : Subscheme.pts K = Set.range (Subscheme.ι K).base :=
      (Scheme.IdealSheafData.range_subschemeι (I := K)).symm
    have h2 : Set.range (Subscheme.ι K).base =
        Set.range (e₀.hom ≫ (R.bb s Bt).ι ≫ (𝒮.xBar s).ι).base := by
      rw [he₀]
    have hsurj : Function.Surjective e₀.hom.base := e₀.hom.homeomorph.surjective
    rw [h1, h2, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, hsurj.range_eq,
      Set.image_univ, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
      show Set.range (R.bb s Bt).ι.base = (R.bb s Bt).pts from
        Scheme.IdealSheafData.range_subschemeι (I := R.bb s Bt), hBbpts]
    exact ((𝒮.xBar s).ι.isClosedEmbedding.closure_image_eq A).symm
  have h2 := 𝒮.exists_iso_totalTransform_of_pts_eq A hAg K hKred hKpts
  have hcc : (𝒮.cBar s).base '' A = (R.cTilde s).base '' Bt.pts := by
    ext y
    constructor
    · rintro ⟨_, ⟨xt, hxt, rfl⟩, rfl⟩
      exact ⟨xt, hxt, rfl⟩
    · rintro ⟨xt, hxt, rfl⟩
      exact ⟨_, ⟨xt, hxt, rfl⟩, rfl⟩
  rw [hcc] at h2
  exact h2.choose_spec.2

/-- `c̃⁻¹(B_s) = B̃` for `B_s = closure c̃(B̃)` (p. 309: "by Corollary of Lemma (AB. 3), `c_s`
induces an open immersion of `B̃` into a reduced irreducible subscheme `B_s` of `X_s`, where `B_s`
is obtained as the closure of `c_s(B̃)` in `X_s`").

Deviation from the paper (gap filled): the paper does not say that `B̃` is the whole preimage of
`B_s` in `X̃`, which is what makes the monoidal transformation of `X̃` induced by `f_{B_s}` the
given `f_{B̃}` (p. 310: "induces the given permissible monoidal transformation `f_{B̃}` of `X̃`").
Lean: the total transform of `B_s` by `c_s` is `ker(B̄ ↪ X̄_s ↪ X̂_s)` (`totalTransform_c_eq_ker`,
the Corollary of Lemma (AB.3) for the closure `B̄` of `B̃` in `X̄_s`), and its restriction to the
open subscheme `X̃ ⊆ X̄_s` is `B̃` (`totalTransform_bb`). -/
@[blueprint "lem:IV.3-c-tilde-preimage"
  (statement := /-- Notation as in \cref{rem:IV.3-3-generic}. Let $\tilde B$ be a reduced
    irreducible subscheme of $\tilde X$ with $\tilde g(\tilde B)=\hat x_0$ and $B_s$ the closure of
    $c_s(\tilde B)$ in $X_s$ with its reduced structure. Then the total transform of $B_s$ by
    $\tilde c_s\colon\tilde X\to X_s$ is $\tilde B$. -/)
  (proof := /-- By the Corollary of Lemma (AB.3) (\cref{cor:IV.AB-3}) the total transform $\hat
    B_s=c_s^{-1}(B_s)$ is the closure $\bar B$ of $\tilde B$ in $\bar X_s$, considered as a closed
    subscheme of $\hat X_s$. Restricting to the open subscheme $\tilde X=\bar U_s$ of $\bar X_s$
    gives $\bar B\cap\tilde X=\tilde B$, as $\tilde B$ is reduced.

    \textbf{Deviation from the paper (gap filled).} The paper (p.~309): ``by Corollary of Lemma (AB.
    3), $c_s$ induces an open immersion of $\tilde B$ into a reduced irreducible subscheme $B_s$ of
    $X_s$'' does not say that $\tilde B$ is the whole preimage of $B_s$ in $\tilde X$, which is
    what makes the monoidal transformation of $\tilde X$ induced by $f_{B_s}$ the given
    $f_{\tilde B}$ (p.~310). -/)
  (proofUses := ["cor:IV.AB-3", "rem:IV.3-3-generic"])
  (latexEnv := "lemma")]
theorem totalTransform_cTilde_eq {s : ℕ} (Bt : Subscheme (R.xTilde s)) (hBtred : Bt.IsReduced)
    (hBti : Bt.IsIrreducible) (hg : ∀ xt ∈ Bt.pts, (R.gTilde s).base xt = hS.xh) :
    Subscheme.totalTransform (R.cTilde s) (Subscheme.ofClosed
      ⟨closure ((R.cTilde s).base '' Bt.pts), isClosed_closure⟩) = Bt := by
  have h := R.totalTransform_c_eq_ker Bt hBti hg
  have e2 : Subscheme.totalTransform (R.cTilde s) (Subscheme.ofClosed
      ⟨closure ((R.cTilde s).base '' Bt.pts), isClosed_closure⟩) =
      Subscheme.totalTransform (R.uBar s).ι (Subscheme.totalTransform (𝒮.xBar s).ι
        (Subscheme.totalTransform (𝒮.c s) (Subscheme.ofClosed
          ⟨closure ((R.cTilde s).base '' Bt.pts), isClosed_closure⟩))) := by
    rw [← Subscheme.totalTransform_comp, ← Subscheme.totalTransform_comp]
    rfl
  rw [e2, h, Subscheme.totalTransform_ι_ker_comp_ι, R.totalTransform_bb s Bt hBtred]

end Frame.RemovalFamily

end FrameFacts

section Reindex

/-- The meet of the members of the list `List.ofFn f` is the meet of the family `f`. -/
theorem _root_.Hironaka.Subscheme.iInf_get_ofFn {Y : Scheme.{u}} {m : ℕ} (f : Fin m → Subscheme Y) :
    (⨅ i : Fin (List.ofFn f).length, (List.ofFn f).get i) = ⨅ j, f j := by
  refine Equiv.iInf_congr (finCongr (List.length_ofFn (f := f))) (fun i => ?_)
  simp
  rfl

end Reindex

section KerPts

/-- The support of the kernel of a closed immersion is contained in its range. -/
theorem _root_.Hironaka.Subscheme.pts_ker_subset_range {Y Z : Scheme.{u}} (f : Y ⟶ Z)
    [IsClosedImmersion f] :
    Subscheme.pts f.ker ⊆ Set.range f.base := by
  obtain ⟨e, he⟩ := Subscheme.exists_iso_ker f
  have h1 : Subscheme.pts f.ker = Set.range f.ker.subschemeι.base :=
    (Scheme.IdealSheafData.range_subschemeι (I := f.ker)).symm
  rw [h1, ← he, Scheme.Hom.comp_base, TopCat.coe_comp]
  exact Set.range_comp_subset_range _ _

end KerPts

section Factorization

/-- **The emptied factorization** (p. 308, with the repair of the paper's error on the subschemes `Ẽ_j`): if
`J̃ ∏ Ẽ_j^{a_j} = J̄` with `J̄_z ≠ 0` at every point, then the exponents vanish on the entries equal
to the whole space (`⊥`), and the same factorization holds for the entries emptied. -/
theorem _root_.Hironaka.DatumII.Raw.emptyIfBot_factorization_of_ne_bot {Z : Scheme.{u}} [Nonempty Z]
    (D : DatumII.Raw Z) {Jbar : Subscheme Z}
    (hfac : D.J * ∏ j : Fin D.α, (D.E j) ^ (D.a j) = Jbar)
    (hJne : ∀ z : Z, Jbar.stalkIdeal z ≠ ⊥) :
    (∀ j, D.E j = ⊥ → D.a j = 0) ∧
      D.emptyIfBot.J * ∏ j : Fin D.emptyIfBot.α, (D.emptyIfBot.E j) ^ (D.emptyIfBot.a j) =
        Jbar := by
  classical
  obtain ⟨z⟩ := ‹Nonempty Z›
  have ha : ∀ j, D.E j = ⊥ → D.a j = 0 := by
    intro j hj
    by_contra hne
    apply hJne z
    rw [← hfac, Subscheme.stalkIdeal_mul_eq, AB.stalkIdeal_prod_eq']
    have h1 : ((D.E j) ^ (D.a j)).stalkIdeal z = 0 := by
      rw [Subscheme.stalkIdeal_pow_eq, hj, Subscheme.stalkIdeal_bot_eq, Ideal.zero_eq_bot]
      exact Ideal.bot_pow hne
    rw [Finset.prod_eq_zero (Finset.mem_univ j) h1, mul_zero]
    exact Ideal.zero_eq_bot
  refine ⟨ha, ?_⟩
  rw [← hfac]
  refine congrArg (D.J * ·) (Finset.prod_congr rfl fun j _ => ?_)
  show (D.E j).emptyIfBot ^ D.a j = _
  by_cases hj : D.E j = ⊥
  · rw [ha j hj, pow_zero, pow_zero]
  · rw [Subscheme.emptyIfBot_of_ne_bot hj]

/-- The factor `J̃` of a factorization of `J̄` has non-zero stalks if `J̄` has. -/
theorem _root_.Hironaka.Subscheme.stalkIdeal_ne_bot_of_mul_eq {Z : Scheme.{u}} {A B C : Subscheme Z}
    (h : A * B = C) (hC : ∀ z : Z, C.stalkIdeal z ≠ ⊥) (z : Z) : A.stalkIdeal z ≠ ⊥ := by
  intro hz
  apply hC z
  rw [← h, Subscheme.stalkIdeal_mul_eq, hz, Ideal.bot_mul]

/-- A reduced `B` with `c̃⁻¹(B) = B̃` and `B ⊆ closure c̃(B̃)` is the closure of `c̃(B̃)` with its
reduced structure. -/
theorem _root_.Hironaka.Subscheme.eq_ofClosed_closure_image {Y Z : Scheme.{u}} (f : Z ⟶ Y)
    {B : Subscheme Y} (hBred : B.IsReduced) {Bt : Subscheme Z}
    (htt : Subscheme.totalTransform f B = Bt)
    (hcl : B.pts ⊆ closure (f.base '' Bt.pts)) :
    B = Subscheme.ofClosed ⟨closure (f.base '' Bt.pts), isClosed_closure⟩ := by
  rw [Subscheme.eq_ofClosed_support B hBred]
  congr 1
  refine TopologicalSpace.Closeds.ext (Set.Subset.antisymm hcl ?_)
  refine closure_minimal ?_ B.support.isClosed
  rintro _ ⟨xt, hxt, rfl⟩
  rw [← htt, Subscheme.pts_totalTransform_eq_preimage] at hxt
  exact hxt

end Factorization


section FrameStage

variable {N n : ℕ} {X : Scheme.{u}} {ℜ : DatumI.Raw X} {P : DatumI.Presentation ℜ}
  {r : Restriction X} {T : Tower X} {x₀ : X} {hS : Standing N n ℜ P r T x₀}

namespace Frame.RemovalFamily

variable {𝒮 : Frame hS} (R : 𝒮.RemovalFamily)

/-- `X̃` is an algebraic scheme (open in a closed subscheme of the algebraic `X̂_s`). -/
theorem isAlgebraicScheme_xTilde [Hironaka.HironakaCitedResults.{u}] (s : ℕ) : IsAlgebraicScheme (R.xTilde s) := by
  have := 𝒮.regShat
  have := 𝒮.isAlgebraicScheme_tHat_X' s
  have := isAlgebraicScheme_toScheme (𝒮.xBar s)
  show IsAlgebraicScheme (R.uBar s : Scheme.{u})
  exact isAlgebraicScheme_of_isOpenImmersion (V := (R.uBar s : Scheme.{u})) (R.uBar s).ι

/-- `X̃` is irreducible when it is non-empty. -/
theorem irreducibleSpace_xTilde [Hironaka.HironakaCitedResults.{u}] (s : ℕ) [Nonempty (R.xTilde s)] :
    IrreducibleSpace (R.xTilde s) := by
  obtain ⟨xt⟩ := ‹Nonempty (R.xTilde s)›
  have hfacts := R.isSimpleAt_and_isIrreducible_and_isNonsingCodimOneOn s
  exact Subtype.irreducibleSpace (hfacts.2.1 ⟨(R.uBar s).ι.base xt, xt.2⟩)

end Frame.RemovalFamily

variable (𝒮 : Frame hS)

/-- **The auxiliary datum at the state of a frame** (p. 308): given a factorization
`J̃ ∏ Ẽ_j^{a_j} = J̄(s)`, `J̄(s)` and `J̃` have non-zero stalks, the exponents vanish on the entries
equal to the whole space, the datum with these entries emptied is weak, and `X̃` is an algebraic
irreducible scheme (formalization infrastructure for p. 310). -/
theorem Frame.datum_facts_stageOf [Hironaka.HironakaCitedResults.{u}] (s : ℕ) (hprep : PrepHyp N ℜ P r T x₀ s)
    {σ : StageState (T.X s)} (hσ : 𝒮.stageOf s = σ) (hU : IsOpen σ.xHatPrimeStar)
    [Nonempty (σ.xTilde hU)] {αT : ℕ} (hl : σ.boundary.length = 𝒮.eTildeOffset + αT)
    (a : Fin αT → ℕ) (Jt : Subscheme (σ.xTilde hU))
    (hfac : Jt * ∏ j : Fin αT, (σ.eTildeAt hU (𝒮.eTildeOffset + j)) ^ (a j) = σ.jBarT hU) :
    (∀ xt : σ.xTilde hU, (σ.jBarT hU).stalkIdeal xt ≠ ⊥) ∧
    (∀ j : Fin αT, σ.eTildeAt hU (𝒮.eTildeOffset + j) = ⊥ → a j = 0) ∧
    (σ.datumII hU 𝒮.b 𝒮.eTildeOffset αT a Jt).emptyIfBot.IsWeakDatum ∧
    IsAlgebraicScheme (σ.xTilde hU) ∧ IrreducibleSpace (σ.xTilde hU) := by
  subst hσ
  have hlen := 𝒮.boundary_length_stageOf s
  obtain rfl : αT = (𝒮.eTilde s).1 := by omega
  have hJne : ∀ xt : (𝒮.stageOf s).xTilde hU, ((𝒮.stageOf s).jBarT hU).stalkIdeal xt ≠ ⊥ :=
    𝒮.removalFamilyStar.stalkIdeal_jBarT_ne_bot s hprep
  have hJt : ∀ xt : (𝒮.stageOf s).xTilde hU, Jt.stalkIdeal xt ≠ ⊥ := fun xt =>
    Subscheme.stalkIdeal_ne_bot_of_mul_eq hfac hJne xt
  have : Nonempty (𝒮.removalFamilyStar.xTilde s) := ‹Nonempty ((𝒮.stageOf s).xTilde hU)›
  refine ⟨hJne, ?_, ?_, 𝒮.removalFamilyStar.isAlgebraicScheme_xTilde s,
    𝒮.removalFamilyStar.irreducibleSpace_xTilde s⟩
  · exact (DatumII.Raw.emptyIfBot_factorization_of_ne_bot
      ((𝒮.stageOf s).datumII hU 𝒮.b 𝒮.eTildeOffset (𝒮.eTilde s).1 a Jt) hfac hJne).1
  · have hdat : (𝒮.stageOf s).datumII hU 𝒮.b 𝒮.eTildeOffset (𝒮.eTilde s).1 a Jt =
        𝒮.removalFamilyStar.datumII s a Jt := 𝒮.stageOf_datumII_eq s a Jt
    rw [hdat]
    exact 𝒮.removalFamilyStar.isWeakDatum_emptyIfBot_datumII s a Jt hJt

/-- **The hypotheses on the center of a blow-up step, at the state of a frame** (p. 310: "the
permissible monoidal transformation `f_{B_s}` of `X_s` with center `B_s` for `ℜ(s)` induces the
given permissible monoidal transformation `f_B̃` of `X̃`"): for a non-singular irreducible `B` with
`c̃⁻¹(B) = B̃` non-singular irreducible, `B ⊆ closure c̃(B̃)`, `E` having only normal crossings with
`B`, and `B̃` permissible for the (emptied) auxiliary datum, the state of the frame satisfies
`BlowupHyp`.  The condition `[g*]` (`notMem_badLocus`) is Lemma (AB.6) (`ab6_inputs`): the total
transform of `B` is the kernel `B̄ ↪ X̄_s ↪ X̂_s`, whose irreducible components are good.

Deviation from the paper (gap filled): the paper (p. 310) says "Then the permissible monoidal
transformation `f_{B_s}` of `X_s` with center `B_s` for `ℜ(s)` induces the given permissible
monoidal transformation `f_{B̃}` of `X̃` for `ℜ^{N-1}_II`", after "we may assume that … the scheme
`X̃` and the datum `ℜ^{N-1}` are kept the same", and does not check that the construction of
pp. 295–299 can be continued at the new stage with the center `B'` (the hypotheses of the blow-up
step, in particular the condition `[g*]`). -/
@[blueprint "lem:IV.3-blowup-hyp-frame"
  (statement := /-- In the situation of \cref{lem:IV.3-blowup-step}, at the stage $s$ of a frame let
    $B\subseteq X_s$ be non-singular irreducible such that $E(s)$ has only normal crossings with
    $B$, let $\tilde B=\tilde c^{-1}(B)$ be non-singular irreducible with
    $B\subseteq\overline{\tilde c(\tilde B)}$, and assume that $f_{\tilde B}$ is permissible for the
    auxiliary datum $\mathfrak R^{N-1}_{\mathrm{II},\flat}$ (with $\tilde J\prod\tilde
    E_j^{a_j}=\bar J(s)$). Then the hypotheses of \cref{lem:IV.3-blowup-step} hold for the center
    $B$. -/)
  (proof := /-- The hypotheses on $X_s$, $E(s)$ and $\tilde X$ are among the facts on the standing
    tower and the frame (\cref{lem:IV.3-xtilde-ambient}). The condition [g*] (that $\bar
    J(s)\subseteq P(\bar B_s)^b$ on every component of $\hat B_s$ through $\bar U_s$) is Lemma
    (AB.6) (\cref{lem:IV.AB-6-generic}): by the Corollary of Lemma (AB.3) (\cref{cor:IV.AB-3}) the
    total transform $\hat B_s=c_s^{-1}(B)$ is the kernel of $\bar B\hookrightarrow\bar
    X_s\hookrightarrow\hat X_s$, where $\bar B$ is the closure of $\tilde B$ in $\bar X_s$, and
    $\bar J(s)\subseteq P(\bar B)^b$ at the points of $\bar U_s\cap\bar B$ by Lemma (AB.6).

    \textbf{Deviation from the paper (gap filled).} The paper (p.~310): ``Then the permissible
    monoidal transformation $f_{B_s}$ of $X_s$ with center $B_s$ for $\mathfrak R(s)$ induces the
    given permissible monoidal transformation $f_{\tilde B}$ of $\tilde X$ for $\mathfrak
    R^{N-1}_{\mathrm{II}}$'' does not check the hypotheses under which the construction of the
    frame goes on at the new stage. -/)
  (proofUses := ["lem:IV.AB-6-generic", "lem:IV.3-blowup-step", "lem:IV.3-xtilde-ambient",
    "cor:IV.AB-3"])
  (latexEnv := "lemma")]
theorem Frame.blowupHyp_stageOf [Hironaka.HironakaCitedResults.{u}] (s : ℕ) (hprep : PrepHyp N ℜ P r T x₀ s)
    {σ : StageState (T.X s)} (hσ : 𝒮.stageOf s = σ) (hU : IsOpen σ.xHatPrimeStar)
    {B : Subscheme (T.X s)} (t : MonoidalTransformation (T.X s) B)
    {Bt : Subscheme (σ.xTilde hU)} (hBns : B.IsNonsingular) (hBirr : B.IsIrreducible)
    (hncB : ((T.pre s).transformI ℜ).E.HasOnlyNormalCrossingsWith B)
    (hBtns : Bt.IsNonsingular) (hBtirr : Bt.IsIrreducible)
    (htt : Subscheme.totalTransform (σ.cTilde hU) B = Bt)
    (hcl : B.pts ⊆ closure ((σ.cTilde hU).base '' Bt.pts))
    {αT : ℕ} (hl : σ.boundary.length = 𝒮.eTildeOffset + αT) (a : Fin αT → ℕ)
    (Jt : Subscheme (σ.xTilde hU))
    (hfac : Jt * ∏ j : Fin αT, (σ.eTildeAt hU (𝒮.eTildeOffset + j)) ^ (a j) = σ.jBarT hU)
    (hperm : (σ.datumII hU 𝒮.b 𝒮.eTildeOffset αT a Jt).emptyIfBot.IsPermissible Bt) :
    σ.BlowupHyp 𝒮.b t hU Bt := by
  classical
  have hne : Nonempty (σ.xTilde hU) := by
    obtain ⟨xt, -⟩ := (Subscheme.isIrreducible_pts Bt hBtirr).nonempty
    exact ⟨xt⟩
  obtain ⟨hJne, ha, hweak, -, -⟩ := 𝒮.datum_facts_stageOf s hprep hσ hU hl a Jt hfac
  subst hσ
  have hlen := 𝒮.boundary_length_stageOf s
  obtain rfl : αT = (𝒮.eTilde s).1 := by omega
  set R := 𝒮.removalFamilyStar with hR
  have hdat : (𝒮.stageOf s).datumII hU 𝒮.b 𝒮.eTildeOffset (𝒮.eTilde s).1 a Jt =
      R.datumII s a Jt := 𝒮.stageOf_datumII_eq s a Jt
  rw [hdat] at hperm
  have hJt0 := (DatumII.Raw.emptyIfBot_factorization_of_ne_bot
      ((𝒮.stageOf s).datumII hU 𝒮.b 𝒮.eTildeOffset (𝒮.eTilde s).1 a Jt) hfac hJne).2
  rw [hdat] at hJt0
  have hJt' : (show Subscheme (R.xTilde s) from Jt) *
      ∏ j, (((R.datumII s a Jt).emptyIfBot).E j) ^ (a j) = R.jBarT s := hJt0
  have hBtred : Bt.IsReduced := Subscheme.isReduced_of_isNonsingular hBtns
  have hBred : B.IsReduced := Subscheme.isReduced_of_isNonsingular hBns
  have hBeq := Subscheme.eq_ofClosed_closure_image (R.cTilde s) hBred htt hcl
  have hsub : ∀ xt : R.xTilde s, xt ∈ Bt.pts → xt ∈ ((R.datumII s a Jt).emptyIfBot).S :=
    fun xt hx => (hperm.2.1 hx).1
  have hnu : ∀ xt : R.xTilde s, xt ∈ Bt.pts →
      (𝒮.b : ℕ∞) ≤ Ideal.nu ((R.jBarT s).stalkIdeal xt) :=
    fun xt hx => R.le_nu_jBarT_of_mem_S a Jt hJt' (hsub xt hx)
  have hg : ∀ xt : R.xTilde s, xt ∈ Bt.pts → (R.gTilde s).base xt = hS.xh :=
    fun xt hx => R.gTilde_eq_xh hprep (hnu xt hx)
  have hab6 := R.ab6_inputs a Jt hJt' Bt hBtns hBtirr hsub hg
  have hker := R.totalTransform_c_eq_ker Bt hBtirr hg
  have hgood : IsGoodDatumI N n X ℜ := ⟨hS.ambient, hS.isDatum, hS.dim_W.le⟩
  obtain ⟨hgoods, -⟩ := isGoodDatumI_transformI_and_isFor_transformSucc (T.pre s) hgood
    hS.isFor (hS.permissible s)
  obtain ⟨hdiv, hnc⟩ := hS.esys_isNonsingularIrreducibleCodimOne_and_hasOnlyNormalCrossings s
  have hbd : (𝒮.stageOf s).boundary = List.ofFn (T.Esys P.E s) := rfl
  refine
    { nonsingular_Y := hgoods.1.2.1
      nonsingular_B := hBns
      irreducible_B := hBirr
      divisor := fun i => ?_
      nc := ?_
      nc_B := ?_
      nonsingular_xTilde := R.isNonsingular_xTilde s
      nonsingular_Bt := hBtns
      irreducible_Bt := hBtirr
      totalTransform_eq := htt
      subset_closure := hcl
      notMem_badLocus := ?_ }
  · have hget : (𝒮.stageOf s).boundary.get i =
        T.Esys P.E s (Fin.cast (List.length_ofFn (f := T.Esys P.E s)) i) := by
      show (List.ofFn (T.Esys P.E s)).get i = _
      exact List.get_ofFn _ i
    rw [hget]
    exact hdiv _
  · show (⨅ i : Fin (List.ofFn (T.Esys P.E s)).length,
      (List.ofFn (T.Esys P.E s)).get i).HasOnlyNormalCrossings
    rw [Subscheme.iInf_get_ofFn]
    exact hnc
  · show (⨅ i : Fin (List.ofFn (T.Esys P.E s)).length,
      (List.ofFn (T.Esys P.E s)).get i).HasOnlyNormalCrossingsWith B
    rw [Subscheme.iInf_get_ofFn, ← hS.transformI_E_eq_iInf_esys s]
    exact hncB
  · intro x hx hbad
    simp only [StageState.badLocus, Set.mem_iUnion] at hbad
    obtain ⟨K, ⟨hK, hnot⟩, hxK⟩ := hbad
    apply hnot
    have hbHat : (𝒮.stageOf s).bHat B = ((R.bb s Bt).ι ≫ (𝒮.xBar s).ι).ker := by
      show Subscheme.totalTransform (𝒮.c s) B = _
      rw [hBeq]
      exact hker
    have hKpts : K.pts ⊆ Set.range ((R.bb s Bt).ι ≫ (𝒮.xBar s).ι).base := by
      refine (Subscheme.pts_subset_of_mem_irreducibleComponents hK).trans ?_
      rw [hbHat]
      exact Subscheme.pts_ker_subset_range ((R.bb s Bt).ι ≫ (𝒮.xBar s).ι)
    refine ⟨?_, fun xb hxb hxbK => ?_⟩
    · refine Subscheme.isContainedIn_of_pts_subset
        (Subscheme.isReduced_of_mem_irreducibleComponents hK) ?_
      intro y hy
      obtain ⟨w, rfl⟩ := hKpts hy
      rw [Scheme.Hom.comp_base, TopCat.coe_comp, Function.comp_apply]
      exact Subscheme.mem_pts_ι (𝒮.xBar s) _
    · have hbBar : (𝒮.stageOf s).bBarOn B = R.bb s Bt := by
        show Subscheme.totalTransform (𝒮.xBar s).ι ((𝒮.stageOf s).bHat B) = _
        rw [hbHat, Subscheme.totalTransform_ι_ker_comp_ι]
      have hxbb : xb ∈ (R.bb s Bt).pts := by
        have : xb ∈ ((𝒮.stageOf s).bBarOn B).pts := by
          rw [StageState.mem_pts_bBarOn_iff]
          have h2 : (𝒮.xBar s).ι.base xb ∈ (Subscheme.totalTransform (𝒮.c s) B).pts :=
            Subscheme.pts_subset_of_mem_irreducibleComponents hK hxbK
          rwa [Subscheme.pts_totalTransform_eq_preimage] at h2
        rwa [hbBar] at this
      rw [hbBar]
      exact hab6.2.2.2 xb ⟨hxbb, hxb⟩

end FrameStage


section StageTwo

/-- Openness along `h` followed by one more transformation gives openness along `h`. -/
theorem StageState.OpenAlong.of_snoc {b : ℕ} : ∀ {Y Z : Scheme.{u}} (h : MonoidalSuccession Y Z)
    (σ : StageState Y) {B : Subscheme Z} (t : MonoidalTransformation Z B),
    σ.OpenAlong b (h.snoc B t) → σ.OpenAlong b h := by
  intro Y Z h
  induction h with
  | nil X => intro σ B t H; exact H.1
  | cons B' t' rest ih => intro σ B t H; exact ⟨H.1, ih (σ.step b t') t H.2⟩

/-- **The block of p. 310 at the level of states** (p. 310: "These monoidal transformations are
successively permissible for `ℜ(s)` and induce trivial monoidal transformations of `X̃` by Remarks 4
and 5.  Therefore, by replacing the original succession `g_s : X_s → X` to include the above
succession, we may assume that the monoidal transformation with center `B_s` is permissible for
`ℜ(s)`, while the scheme `X̃` and the datum `ℜ^{N-1}` are kept the same.  Then the permissible
monoidal transformation `f_{B_s}` of `X_s` with center `B_s` for `ℜ(s)` induces the given
permissible monoidal transformation `f_{B̃}` of `X̃` for `ℜ^{N-1}_II`"): if the emptied
auxiliary datum of the state `σ` is resolved by `k` further transformations after the permissible
blow-up of `B̃`, and `h` is a succession permissible for `((E; V, W; B_s), U_s)` (so that the
centers of `h` miss `c̃(X̃)`), then the emptied auxiliary datum of the state after `h` followed by
the blow-up of the strict transform of `B_s` is resolvable by `k` transformations.  The hypothesis
`hF` is the statement that the state after `h` is the state of a frame (Remarks 3 and 5 and
Lemma (AB.6) at that stage; `Frame.blowupHyp_stageOf`, `Frame.datum_facts_stageOf`).

Deviation from the paper (gap filled): "induce trivial monoidal transformations of `X̃` by Remarks 4
and 5 … the scheme `X̃` and the datum `ℜ^{N-1}` are kept the same" (p. 310) is the iterated trivial
step (`StageState.exists_iso_xTilde_fold_of_isPermissibleIOpen_extendBy`): `X̃`, `J̄` and the `Ẽ_j`
are carried along an isomorphism `ε`, the new components being empty (exponent `0`); that the
emptied datum, its permissibility for the center and its resolvability are transported along `ε`,
and that the monoidal transformation with center `ε⁻¹(B̃)` is the given one up to isomorphism
(`DatumII.Raw.resolvableLen_transform_of_sameChar_pullback`), is tacit. -/
@[blueprint "lem:IV.3-one-block-step"
  (statement := /-- In the situation of \cref{lem:IV.3-one-block-succession}, let $\mathfrak
    R^{N-1}_{\mathrm{II},\flat}$ be the auxiliary datum at the stage $g$ with its whole-space
    entries emptied, $\tilde B$ the center of the first monoidal transformation of a resolution of
    it by $k+1$ transformations, $B_s$ the closure of $\tilde c(\tilde B)$ (so $\tilde
    c^{-1}(B_s)=\tilde B$), and $h$, $B'$ as in \cref{lem:IV.3-one-block-succession}. Then at the
    stage $g\cdot h\cdot[f_{B'}]$ the auxiliary datum, with its whole-space entries emptied, is
    resolvable by $k$ monoidal transformations. -/)
  (proof := /-- The centers of $h$ lie in $B_s-U_s$ and $\tilde c^{-1}(B_s)=\tilde B$ lies over
    $U_s$, so the centers miss $\tilde c(\tilde X)$ and $h$ induces trivial monoidal transformations
    of $\tilde X$ (\cref{lem:IV.3-trivial-step}, iterated): $\tilde X$, $\bar J$ and the $\tilde
    E_j$ are carried along an isomorphism $\varepsilon$, and the new components are empty with
    exponent $0$. The emptied datum is transported along $\varepsilon$ (resolvability is invariant
    under isomorphisms and under a change of the characteristics that only adds empty components),
    and the monoidal transformation with center $\varepsilon^{-1}(\tilde B)$ is unique up to
    isomorphism. At the stage $g\cdot h$ the hypotheses of \cref{lem:IV.3-blowup-step} hold for the
    center $B'$ (\cref{lem:IV.3-blowup-hyp-frame}), which gives the next state, and emptying the
    whole-space entries commutes with the transform for a weak datum and a permissible center
    (\cref{lem:IV.tilde-drop}).

    \textbf{Deviation from the paper (gap filled).} The paper (p.~310): ``These monoidal
    transformations are successively permissible for $\mathfrak R(s)$ and induce trivial monoidal
    transformations of $\tilde X$ by Remarks 4 and 5 \dots\ while the scheme $\tilde X$ and the
    datum $\mathfrak R^{N-1}$ are kept the same. Then the permissible monoidal transformation
    $f_{B_s}$ of $X_s$ with center $B_s$ for $\mathfrak R(s)$ induces the given permissible monoidal
    transformation $f_{\tilde B}$ of $\tilde X$ for $\mathfrak R^{N-1}_{\mathrm{II}}$'' is a
    sketch; the transport of the datum and of its resolvability along $\varepsilon$ is not
    said. -/)
  (proofUses := ["lem:IV.3-trivial-step", "lem:IV.3-blowup-step", "lem:IV.3-blowup-hyp-frame",
    "lem:IV.tilde-drop", "lem:IV.3-one-block-succession"])
  (latexEnv := "lemma")]
theorem StageState.auxResolvable_fold_snoc_of_isPermissibleIOpen_extendBy [Hironaka.HironakaCitedResults.{u}]
    (b : ℕ) {Y Z₀ : Scheme.{u}} (σ : StageState Y) (hU : IsOpen σ.xHatPrimeStar)
    {α₀ αT : ℕ} (hlen : σ.boundary.length = α₀ + αT) (a : Fin αT → ℕ)
    (Jt : Subscheme (σ.xTilde hU))
    (hfac : Jt * ∏ j : Fin αT, (σ.eTildeAt hU (α₀ + j)) ^ (a j) = σ.jBarT hU)
    {Bt : Subscheme (σ.xTilde hU)} (tT : MonoidalTransformation (σ.xTilde hU) Bt)
    (hBtns : Bt.IsNonsingular) (hBtirr : Bt.IsIrreducible)
    (hperm : (σ.datumII hU b α₀ αT a Jt).emptyIfBot.IsPermissible Bt) (k : ℕ)
    (hrest : DatumII.Raw.ResolvableLen k
      ((σ.datumII hU b α₀ αT a Jt).emptyIfBot.transform tT))
    (ℜY : DatumI.Raw Y) (Bs : Subscheme Y) (Us : Set Y) (h : MonoidalSuccession Y Z₀)
    (hh : h.IsPermissibleIOpen (ℜY.extendBy Bs) Us)
    (hBU : ∀ x : σ.xTilde hU, (σ.cTilde hU).base x ∈ Bs.pts → (σ.cTilde hU).base x ∈ Us)
    (hBsBt : Subscheme.totalTransform (σ.cTilde hU) Bs = Bt)
    (hBscl : Bs.pts ⊆ closure ((σ.cTilde hU).base '' Bt.pts))
    (t' : MonoidalTransformation Z₀ (h.strictTransform Bs))
    (hopen : σ.OpenAlong b (h.snoc (h.strictTransform Bs) t'))
    (hF : ∀ (hUh : IsOpen (StageState.fold b h σ).xHatPrimeStar)
      (Bt' : Subscheme ((StageState.fold b h σ).xTilde hUh)),
      Bt'.IsNonsingular → Bt'.IsIrreducible →
      Subscheme.totalTransform ((StageState.fold b h σ).cTilde hUh) (h.strictTransform Bs) =
        Bt' →
      (h.strictTransform Bs).pts ⊆
        closure (((StageState.fold b h σ).cTilde hUh).base '' Bt'.pts) →
      ∀ (αT' : ℕ), (StageState.fold b h σ).boundary.length = α₀ + αT' →
      ∀ (a' : Fin αT' → ℕ) (Jt' : Subscheme ((StageState.fold b h σ).xTilde hUh)),
        Jt' * ∏ j : Fin αT', ((StageState.fold b h σ).eTildeAt hUh (α₀ + j)) ^ (a' j) =
          (StageState.fold b h σ).jBarT hUh →
        ((StageState.fold b h σ).datumII hUh b α₀ αT' a' Jt').emptyIfBot.IsPermissible Bt' →
        (StageState.fold b h σ).BlowupHyp b t' hUh Bt' ∧
        ((StageState.fold b h σ).datumII hUh b α₀ αT' a' Jt').emptyIfBot.IsWeakDatum ∧
        (∀ xt, ((StageState.fold b h σ).jBarT hUh).stalkIdeal xt ≠ ⊥) ∧
        IsAlgebraicScheme ((StageState.fold b h σ).xTilde hUh) ∧
        IrreducibleSpace ((StageState.fold b h σ).xTilde hUh)) :
    (StageState.fold b (h.snoc (h.strictTransform Bs) t') σ).AuxResolvable b α₀ k := by
  classical
  have hopen_h : σ.OpenAlong b h := StageState.OpenAlong.of_snoc h σ t' hopen
  have hUh : IsOpen (StageState.fold b h σ).xHatPrimeStar := hopen_h.isOpen_fold
  have hUe : IsOpen (StageState.fold b (h.snoc (h.strictTransform Bs) t') σ).xHatPrimeStar :=
    hopen.isOpen_fold
  obtain ⟨hUh', ε, hcomp, hjB, hE, hTT, hclA⟩ :=
    StageState.exists_iso_xTilde_fold_of_isPermissibleIOpen_extendBy b σ hU ℜY Bs Us h hh hopen_h
      hBU
  set σh := StageState.fold b h σ with hσh
  have hl' : σh.boundary.length = α₀ + (αT + h.length) := by
    rw [hσh, StageState.length_boundary_fold, hlen]
    ring
  have hempty : ∀ i, α₀ + αT ≤ i → σ.eTildeAt hU i = Subscheme.empty := by
    intro i hi
    unfold StageState.eTildeAt
    rw [List.getD_eq_default _ _ (by omega), Subscheme.totalTransform_empty,
      Subscheme.totalTransform_empty, Subscheme.totalTransform_empty]
  obtain ⟨hfac', hsc⟩ := StageState.sameChar_datumII_emptyIfBot_of_iso b σ σh hU hUh ε hjB hE
    α₀ αT (αT + h.length) (Nat.le_add_right _ _) hempty a Jt hfac
  have hsurj : Function.Surjective ε.hom.base := ε.hom.homeomorph.surjective
  set a' : Fin (αT + h.length) → ℕ := fun j => if hj : (j : ℕ) < αT then a ⟨j, hj⟩ else 0
    with ha'
  set Jth := Subscheme.totalTransform ε.hom Jt with hJth
  set Bth := Subscheme.totalTransform ε.hom Bt with hBth
  have hBtne : Bt.pts.Nonempty := (Subscheme.isIrreducible_pts Bt hBtirr).nonempty
  have hBthne : Bth.pts.Nonempty := by
    obtain ⟨y, hy⟩ := hBtne
    obtain ⟨x, rfl⟩ := hsurj y
    refine ⟨x, ?_⟩
    rw [hBth, FlatPreimm.pts_totalTransform]
    exact hy
  have hBthns : Bth.IsNonsingular := FlatPreimm.isNonsingular_totalTransform ε.hom Bt hBtns
  have hBthirr : Bth.IsIrreducible := by
    rcases FlatPreimm.empty_or_isIrreducible_totalTransform ε.hom Bt hBtirr with h0 | h1
    · exfalso
      rw [← hBth] at h0
      obtain ⟨y, hy⟩ := hBthne
      rw [h0, Subscheme.pts_empty] at hy
      exact hy
    · exact h1
  have htt' : Subscheme.totalTransform (σh.cTilde hUh) (h.strictTransform Bs) = Bth := by
    rw [hTT, hBsBt]
  have hcl' := hclA Bt hBscl
  have hperm_h : (σh.datumII hUh b α₀ (αT + h.length) a' Jth).emptyIfBot.IsPermissible Bth :=
    hsc.isPermissible (DatumII.Raw.isPermissible_pullback ε.hom hsurj hperm)
  obtain ⟨H, hD, hJne, hAlg, hIrr⟩ := hF hUh Bth hBthns hBthirr htt' hcl' (αT + h.length) hl' a'
    Jth hfac' hperm_h
  have hnonempty : Nonempty (σh.xTilde hUh) := ⟨hBthne.choose⟩
  have ha := (DatumII.Raw.emptyIfBot_factorization_of_ne_bot
    (σh.datumII hUh b α₀ (αT + h.length) a' Jth) hfac' hJne).1
  rw [StageState.fold_snoc] at hUe ⊢
  have := hAlg
  have := hIrr
  exact StageState.auxResolvable_step_of_blowupHyp σh b t' H hl' ha hD hperm_h hfac' hUe k
    (fun t'' => DatumII.Raw.resolvableLen_transform_of_sameChar_pullback ε.hom hsurj _ _ hsc tT
      t'' k hrest)

end StageTwo

section MainHelpers

variable {X Y Z : Scheme.{u}}

/-- `g` followed by `t` is `g` followed by the one-step succession `[t]` (formalization
infrastructure for p. 310). -/
theorem succession_snoc_eq_append_cons_nil (g : MonoidalSuccession X Y) {B : Subscheme Y}
    (t : MonoidalTransformation Y B) :
    g.snoc B t = g.append (MonoidalSuccession.cons B t (MonoidalSuccession.nil t.X')) := by
  induction g with
  | nil X => rfl
  | cons B' t' rest ih => exact congrArg (MonoidalSuccession.cons B' t') (ih t)

/-- Appending `h` followed by `t` is appending `h` and then `t` (formalization infrastructure for
p. 310). -/
theorem succession_append_snoc (g : MonoidalSuccession X Y) (h : MonoidalSuccession Y Z)
    {B : Subscheme Z} (t : MonoidalTransformation Z B) :
    g.append (h.snoc B t) = (g.append h).snoc B t := by
  rw [succession_snoc_eq_append_cons_nil, succession_snoc_eq_append_cons_nil,
    succession_append_assoc]

/-- A succession followed by one more monoidal transformation is permissible for `(ℜ, r)` iff the
succession is and the transformation is permissible for the transform (Definition 8, p. 169). -/
theorem Restriction.isPermissibleSucc_snoc_iff (r : Restriction X) (g : MonoidalSuccession X Y)
    {B : Subscheme Y} (t : MonoidalTransformation Y B) (ℜ : DatumI.Raw X) :
    r.IsPermissibleSucc (g.snoc B t) ℜ ↔
      r.IsPermissibleSucc g ℜ ∧ (r.transformSucc g).IsPermissibleCenter (g.transformI ℜ) B := by
  cases r with
  | closed F => exact MonoidalSuccession.isPermissibleIClosed_snoc_iff g B t ℜ F
  | opn U => exact MonoidalSuccession.isPermissibleIOpen_snoc_iff g B t ℜ U

/-- A permissible center for `(ℜ, r)` is permissible for `ℜ`. -/
theorem Restriction.IsPermissibleCenter.isPermissible {r : Restriction Y} {ℜ : DatumI.Raw Y}
    {B : Subscheme Y} (h : r.IsPermissibleCenter ℜ B) : ℜ.IsPermissible B := by
  cases r with
  | closed F => exact h.1
  | opn U => exact h.1

/-- The conclusions of Remark 5 (p. 310) say that `B_s ⊆ W*(s)`. -/
theorem Restriction.pts_subset_wStar_transformSucc {X Y : Scheme.{u}} (r : Restriction X)
    (g : MonoidalSuccession X Y) (ℜs : DatumI.Raw Y) (B : Subscheme Y)
    (h1 : ∀ F, r = .closed F → B.pts ⊆ ℜs.W.pts ∩ (g.strictTransform F).pts)
    (h2 : ∀ U, r = .opn U → B.pts ⊆ ℜs.W.pts \ g.transformOpen U) :
    B.pts ⊆ wStar ℜs (r.transformSucc g) := by
  cases r with
  | closed F => exact h1 F rfl
  | opn U => exact h2 U rfl

end MainHelpers

section MainTheorem

/-- **The one-block lemma (M9), for a raw datum** (p. 310; the statement for `ℜ : DatumI X` is
`exists_extension_of_stageResolvable_succ`).  Proof: take a standing tower `T` with `T.pre m = g`
(`exists_standing_prepHyp_of_prepHypSucc`) and the frame over it; the first center `B̃` of the
resolution of `ℜ^{N-1}_II,♭` by `k + 1` monoidal transformations is empty (left alternative:
`DatumII.Raw.resolvableLen_of_transform_of_center_empty`) or non-singular irreducible; then `B_s`
is the closure of `c̃(B̃)` (Remarks 3, 4, 5 and `dim_Bs_lt` for the emptied datum), `h` and `B'` are
given by `exists_succession_of_isOpenRestriction_extendBy`, `e = h ++ [f_{B'}]`, and, if `x_0` is
still in the image of `S`, the blow-up step is
`StageState.auxResolvable_fold_snoc_of_isPermissibleIOpen_extendBy` at the stage `g ++ h` (a
standing tower for `g ++ h` is again given by
`exists_standing_prepHyp_of_prepHypSucc`). -/
theorem exists_extension_of_stageResolvable_succ_of_isDatum [Hironaka.HironakaCitedResults.{u}]
    (N n : ℕ) (hNn : n < N)
    (hI₂ : ∀ n'' : ℕ, n'' < n → FundamentalTheorem.I₂.{u} N n'')
    (X : Scheme.{u}) (hX : IsAmbient X N) (ℜ : DatumI.Raw X) (hℜ : ℜ.IsDatum)
    (P : DatumI.Presentation ℜ) (r : Restriction X) (hr : r.IsFor ℜ)
    (hn : ℜ.n = (n : WithBot ℕ∞))
    (x₀ : X) (hx₀ : X.IsSimpleAt x₀) [IsRegularLocalRing (Shat X x₀)] (z : Shat X x₀) (b : ℕ)
    (Jgen : Set (Shat X x₀)) (fr : FrameSpec x₀ hx₀ ℜ r z b Jgen)
    {Y : Scheme.{u}} (g : MonoidalSuccession X Y) (hg : r.IsPermissibleSucc g ℜ)
    (hfin : HasFiniteImageOfDimEq N ℜ r g) (hbd : HasPreparedBoundary P r g)
    (hx : x₀ ∈ g.composite.base '' S (g.transformI ℜ) (r.transformSucc g))
    (k : ℕ) (hQ : StageResolvable b P r hx₀ z Jgen g (k + 1)) :
    StageResolvable b P r hx₀ z Jgen g k ∨
      ∃ (Z : Scheme.{u}) (e : MonoidalSuccession Y Z),
        r.IsPermissibleSucc (g.append e) ℜ ∧
        (x₀ ∈ (g.append e).composite.base ''
            S ((g.append e).transformI ℜ) (r.transformSucc (g.append e)) →
          StageResolvable b P r hx₀ z Jgen (g.append e) k) := by
  classical
  have hgood : IsGoodDatumI N n X ℜ := ⟨hX, hℜ, hn.le⟩
  have hp : IsPrepared N P r g := ⟨hfin, hbd⟩
  obtain ⟨T, m, hm, hpre, -, hS, hprepm⟩ := exists_standing_prepHyp_of_prepHypSucc P hNn hX hℜ hn
    hr g hg (prepHypSucc_of_isPrepared hp hx)
  subst hm
  have hpre' : T.pre m = g := hpre
  subst hpre'
  have hσm := Frame.canon_stageOf_eq_fold (hS := hS) (z := z) (b := b) (jGen := Jgen) (fr := fr) m
  set 𝒮 : Frame hS := Frame.canon hS z b Jgen fr with h𝒮
  have hQ' : (𝒮.stageOf m).AuxResolvable b 𝒮.eTildeOffset (k + 1) := by
    rw [stageResolvable_iff_auxResolvable, ← hσm] at hQ
    rw [𝒮.eTildeOffset_eq]
    exact hQ
  obtain ⟨hU, αT, hlen, a, Jt, hfacD, hres⟩ := hQ'
  obtain rfl : αT = (𝒮.eTilde m).1 := by
    have := 𝒮.boundary_length_stageOf m
    omega
  set R := 𝒮.removalFamilyStar with hR
  have hdat : (𝒮.stageOf m).datumII hU b 𝒮.eTildeOffset (𝒮.eTilde m).1 a Jt =
      R.datumII m a Jt := 𝒮.stageOf_datumII_eq m a Jt
  have hfac : Jt * ∏ j : Fin (𝒮.eTilde m).1,
      ((𝒮.stageOf m).eTildeAt hU (𝒮.eTildeOffset + j)) ^ (a j) = (𝒮.stageOf m).jBarT hU :=
    hfacD
  have hfacR := hfacD
  rw [hdat] at hfacR
  obtain ⟨Bt, tT, hperm, hrest⟩ := hres
  rcases hperm.1 with hBt0 | ⟨hBtns, hBtirr⟩
  · -- the first center is empty: the left alternative
    subst hBt0
    left
    have hk := DatumII.Raw.resolvableLen_of_transform_of_center_empty tT _ k hrest
    rw [stageResolvable_iff_auxResolvable, ← hσm, ← 𝒮.eTildeOffset_eq]
    exact ⟨hU, (𝒮.eTilde m).1, hlen, a, Jt, hfacD, hk⟩
  right
  have hnonempty : Nonempty (R.xTilde m) :=
    ⟨(Subscheme.isIrreducible_pts Bt hBtirr).nonempty.choose⟩
  have hJne : ∀ xt : R.xTilde m, (R.jBarT m).stalkIdeal xt ≠ ⊥ :=
    R.stalkIdeal_jBarT_ne_bot m hprepm
  have hfacR' : (show Subscheme (R.xTilde m) from Jt) *
      ∏ j : Fin (𝒮.eTilde m).1, ((R.datumII m a Jt).E j) ^ (a j) = R.jBarT m := hfacR
  have hJt : ∀ xt : R.xTilde m, Jt.stalkIdeal xt ≠ ⊥ := fun xt =>
    Subscheme.stalkIdeal_ne_bot_of_mul_eq hfacR' hJne xt
  have hfacE : (show Subscheme (R.xTilde m) from Jt) *
      ∏ j, (((R.datumII m a Jt).emptyIfBot).E j) ^ (a j) = R.jBarT m :=
    (DatumII.Raw.emptyIfBot_factorization_of_ne_bot (R.datumII m a Jt) hfacR' hJne).2
  have hII := R.isWeakDatum_emptyIfBot_datumII m a Jt hJt
  have hpermR : (R.datumII m a Jt).emptyIfBot.IsPermissible Bt := by
    rw [← hdat]
    exact hperm
  have hdim := R.dim_Bs_lt m hprepm a Jt hfacE hII Bt hBtns hBtirr hpermR
  have hrem4 := R.isContainedIn_W_and_resolvedAt_extendBy_of_isPermissible m hprepm a Jt hfacE
    hII Bt hBtns hBtirr hpermR
  have hrem5 := R.isPermissibleCenter_of_isPermissibleOpen_extendBy m hprepm a Jt hfacE hII Bt
    hBtns hBtirr hpermR
  obtain ⟨hBsC, Us, ⟨U₀, hU₀, hUs⟩, hdens, hcUs, hresUs⟩ := hrem4
  set Bs : Subscheme (T.X m) :=
    Subscheme.ofClosed ⟨closure ((R.cTilde m).base '' Bt.pts), isClosed_closure⟩ with hBs
  have hBtred : Bt.IsReduced := Subscheme.isReduced_of_isNonsingular hBtns
  have hBtne : Bt.pts.Nonempty := (Subscheme.isIrreducible_pts Bt hBtirr).nonempty
  have hBsred : Bs.IsReduced := Subscheme.ofClosed_isReduced _
  have hBspts : Bs.pts = closure ((R.cTilde m).base '' Bt.pts) := Subscheme.pts_ofClosed _
  have hBsirr : Bs.IsIrreducible := by
    refine Subscheme.isIrreducible_of_pts _ ?_
    rw [hBspts]
    exact ((Subscheme.isIrreducible_pts Bt hBtirr).image _
      (R.cTilde m).base.hom.continuous.continuousOn).closure
  have hBsW : Bs.IsContainedIn ((T.pre m).transformI ℜ).W := by
    rw [MonoidalSuccession.transformI_W]
    exact hBsC
  have hBsr : Bs.pts ⊆ wStar ((T.pre m).transformI ℜ) (r.transformSucc (T.pre m)) :=
    Restriction.pts_subset_wStar_transformSucc r (T.pre m) _ Bs hrem5.1 hrem5.2.1
  have hdim' : Bs.dim < (n : WithBot ℕ∞) := by
    rw [← hn]
    exact hdim
  have hOR : (((T.pre m).transformI ℜ).extendBy Bs).IsOpenRestriction Us :=
    ⟨⟨U₀, hU₀, hUs⟩, hdens, hresUs⟩
  have hne : Us.Nonempty := by
    obtain ⟨xt, hxt⟩ := hBtne
    exact ⟨_, hcUs ⟨xt, hxt, rfl⟩⟩
  have hg0 : ∀ xt : R.xTilde m, xt ∈ Bt.pts → (R.gTilde m).base xt = hS.xh := fun xt hx =>
    R.gTilde_eq_xh hprepm (R.le_nu_jBarT_of_mem_S a Jt hfacE ((hpermR.2.1 hx).1))
  have hBsBt : Subscheme.totalTransform (R.cTilde m) Bs = Bt :=
    R.totalTransform_cTilde_eq Bt hBtred hBtirr hg0
  have hBU : ∀ x : (𝒮.stageOf m).xTilde hU, ((𝒮.stageOf m).cTilde hU).base x ∈ Bs.pts →
      ((𝒮.stageOf m).cTilde hU).base x ∈ Us := by
    intro x hx
    have hx' : x ∈ (Subscheme.totalTransform (R.cTilde m) Bs).pts := by
      rw [Subscheme.pts_totalTransform_eq_preimage]
      exact hx
    rw [hBsBt] at hx'
    exact hcUs ⟨x, hx', rfl⟩
  obtain ⟨Z₀, h, hh, hgh, hirr', hcenter⟩ := exists_succession_of_isOpenRestriction_extendBy hI₂
    hgood hr (T.pre m) hg hBsred hBsirr hBsW hBsr hdim' hOR hne
  obtain ⟨t', -⟩ := MonoidalTransformation.exists_isProper Z₀ (h.strictTransform Bs)
  have hge : r.IsPermissibleSucc ((T.pre m).append (h.snoc (h.strictTransform Bs) t')) ℜ := by
    rw [succession_append_snoc, Restriction.isPermissibleSucc_snoc_iff]
    exact ⟨hgh, hcenter⟩
  refine ⟨t'.X', h.snoc (h.strictTransform Bs) t', hge, fun hx' => ?_⟩
  have hrw : (T.pre m).append (h.snoc (h.strictTransform Bs) t') =
      ((T.pre m).append h).append (MonoidalSuccession.cons _ t' (MonoidalSuccession.nil _)) := by
    rw [succession_append_snoc, succession_snoc_eq_append_cons_nil]
  have hopen := StageState.openAlong_fold_initial_of_isPermissibleSucc hNn hX hℜ P r hr hn hx₀ z b
    Jgen fr (T.pre m) (h.snoc (h.strictTransform Bs) t') hge hfin hbd hx'
  rw [← hσm] at hopen
  have hx_h : x₀ ∈ ((T.pre m).append h).composite.base ''
      S (((T.pre m).append h).transformI ℜ) (r.transformSucc ((T.pre m).append h)) := by
    rw [hrw] at hx' hge
    exact image_S_append_subset ((T.pre m).append h) _ hgood hr hge hx'
  obtain ⟨T'', m'', hm'', hpre'', -, hS'', hprep''⟩ := exists_standing_prepHyp_of_prepHypSucc P
    hNn hX hℜ hn hr ((T.pre m).append h) hgh
    (prepHypSucc_of_isPrepared (hp.append h hgood hr hgh) hx_h)
  subst hm''
  have hσh := Frame.canon_stageOf_eq_fold (hS := hS'') (z := z) (b := b) (jGen := Jgen) (fr := fr)
    m''
  set 𝒮'' : Frame hS'' := Frame.canon hS'' z b Jgen fr with h𝒮''
  have hpre3 : T''.pre m'' = (T.pre m).append h := hpre''
  have hσh' : 𝒮''.stageOf m'' = StageState.fold b h (𝒮.stageOf m) := by
    rw [hσh, hpre3, StageState.fold_append, hσm]
  rw [stageResolvable_iff_auxResolvable, StageState.fold_append, ← hσm, ← 𝒮.eTildeOffset_eq]
  refine StageState.auxResolvable_fold_snoc_of_isPermissibleIOpen_extendBy b (𝒮.stageOf m) hU hlen
    a Jt hfac tT hBtns hBtirr hperm k hrest ((T.pre m).transformI ℜ) Bs Us h hh hBU hBsBt
    hBspts.le t' hopen ?_
  intro hUh Bt' hBt'ns hBt'irr htt hcl αT' hl' a' Jt' hfac' hperm'
  have hne' : Nonempty ((StageState.fold b h (𝒮.stageOf m)).xTilde hUh) :=
    ⟨(Subscheme.isIrreducible_pts Bt' hBt'irr).nonempty.choose⟩
  have e1 : 𝒮''.eTildeOffset = 𝒮.eTildeOffset := by
    rw [𝒮''.eTildeOffset_eq, 𝒮.eTildeOffset_eq]
  have eb : 𝒮''.b = b := rfl
  have hl'' : (StageState.fold b h (𝒮.stageOf m)).boundary.length = 𝒮''.eTildeOffset + αT' := by
    rw [e1]
    exact hl'
  have hfac'' : Jt' * ∏ j : Fin αT',
      ((StageState.fold b h (𝒮.stageOf m)).eTildeAt hUh (𝒮''.eTildeOffset + j)) ^ (a' j) =
        (StageState.fold b h (𝒮.stageOf m)).jBarT hUh := by
    rw [e1]
    exact hfac'
  have hperm'' : ((StageState.fold b h (𝒮.stageOf m)).datumII hUh 𝒮''.b 𝒮''.eTildeOffset αT' a'
      Jt').emptyIfBot.IsPermissible Bt' := by
    rw [e1, eb]
    exact hperm'
  obtain ⟨hBcenter, -, hBres⟩ := hcenter.isPermissible
  have hBne := (Subscheme.isIrreducible_pts _ hirr').nonempty
  have hBns : (h.strictTransform Bs).IsNonsingular := by
    rcases hBcenter with h0 | ⟨hns, -⟩
    · exfalso
      rw [h0, Subscheme.pts_empty] at hBne
      exact Set.not_nonempty_empty hBne
    · exact hns
  have hncB : ((T''.pre m'').transformI ℜ).E.HasOnlyNormalCrossingsWith (h.strictTransform Bs) := by
    rw [hpre3]
    exact fun x hx => (hBres x hx).2.2
  have H := 𝒮''.blowupHyp_stageOf m'' hprep'' hσh' hUh t' hBns hirr' hncB hBt'ns hBt'irr htt hcl
    hl'' a' Jt' hfac'' hperm''
  obtain ⟨hJne', -, hweak, hAlg, hIrr⟩ := 𝒮''.datum_facts_stageOf m'' hprep'' hσh' hUh hl'' a' Jt'
    hfac''
  rw [e1, eb] at hweak
  exact ⟨H, hweak, hJne', hAlg, hIrr⟩

/-- **The one-block lemma (M9)** (p. 310): at a prepared permissible stage `g` with `x_0 ∈ g(S)`,
if the emptied auxiliary datum `ℜ^{N-1}_II` (p. 308, with the repair of the paper's error on the subschemes `Ẽ_j`) is resolvable by
`k + 1` monoidal transformations, then either it is resolvable by `k` at the same stage, or `g` has
a permissible extension `g ++ e` at which, as long as `x_0` is in the image of `S`, it is
resolvable by `k`.  The extension is the succession `h` of Theorem `I₂^{N,n'}` (with `n' < n`),
trivial on `X̃`, followed by the monoidal transformation with center the strict transform of `B_s`.

Deviation from the paper (gap filled; proof corrected for the paper's error on the subschemes `Ẽ_j`): the paper
(p. 310) says "Then the permissible monoidal transformation `f_{B_s}` of `X_s` with center `B_s`
for `ℜ(s)` induces the given permissible monoidal transformation `f_{B̃}` of `X̃` for
`ℜ^{N-1}_II`. Thus, applying Theorem `II₂^{N-1}` to the resolution datum `ℜ^{N-1}_II` on `X̃`
(without restriction), we can prove that there exists a finite permissible succession of monoidal
transformations of `X_s` for `ℜ(s)`, which induces a permissible succession of monoidal
transformations of `X̃` for `ℜ^{N-1}_II` and which resolve the datum `ℜ^{N-1}_II`."  Lean makes the
replacement of `g_s` one monoidal transformation of `X̃` at a time (`lem:IV.3-extension-induction`),
works with the emptied weak datum, and proves the facts that are left implicit: `n' < n`
(`dim_Bs_lt`), `h` permissible for `ℜ(s)` and the irreducibility and permissibility of the strict
transform of `B_s` (`exists_succession_of_isOpenRestriction_extendBy`), `c̃⁻¹(B_s) = B̃`, the
transport of the datum along the trivial steps, and the hypotheses of the blow-up step at the new
stage. -/
@[blueprint "lem:IV.3-one-block"
  (statement := /-- In the situation of \cref{def:IV.3-conditions} with the frame data fixed, assume
    Theorems $\mathrm I_2^{N,n''}$ for $n''<n$. Let $g$ be a prepared permissible succession with
    $x_0\in g(S(\mathfrak R(s)))$ such that the auxiliary datum $\mathfrak R^{N-1}_{\mathrm{II}}$ of
    \cref{rem:IV.3-2-repaired}, with its whole-space entries emptied, is resolvable by $k+1$
    monoidal transformations. Then it is resolvable by $k$ monoidal transformations at the stage
    $g$, or $g$ has a permissible extension $g\cdot e$ such that, if $x_0$ is still in the image of
    $S$, the datum is resolvable by $k$ monoidal transformations at the stage $g\cdot e$. -/)
  (proof := /-- Let $\tilde B$ be the center of the first monoidal transformation of a resolution of
    the emptied auxiliary datum by $k+1$ monoidal transformations. If $\tilde B$ is empty, the datum
    is already resolvable by $k$ monoidal transformations. Otherwise $\tilde B$ is non-singular
    irreducible and permissible; let $B_s$ be the closure of $\tilde c(\tilde B)$. By Remarks 3, 4,
    5 (\cref{rem:IV.3-3-generic}, \cref{rem:IV.3-4-generic}, \cref{rem:IV.3-5-generic}) and
    \cref{lem:IV.3-dim-Bs-lt}, $B_s$ is a reduced irreducible subscheme of $W(s)\cap W^*(s)$ with
    $n'=\dim B_s<n$ and an open restriction $U_s$ of $\mathfrak R^{N,n'}_{\mathrm I}(s)$ with
    $\tilde c(\tilde B)\subseteq U_s$. Take $h$ and the strict transform $B'$ of $B_s$ as in
    \cref{lem:IV.3-one-block-succession} and $e=h\cdot[f_{B'}]$; $g\cdot e$ is permissible. If $x_0$
    is still in the image of $S$, a standing tower exists for $g\cdot h$ (it is a finite permissible
    succession satisfying [(1)], [(2)] with $x_0$ in the image of $S$), the stage $g\cdot h$ has the
    frame objects of $g$ carried along the trivial steps, and \cref{lem:IV.3-one-block-step} gives
    the resolvability by $k$ monoidal transformations at the stage $g\cdot e$.

    \textbf{Deviation from the paper (gap filled; proof corrected for the paper's error on the subschemes $\tilde E_j$).} The
    paper (p.~310): ``Then the permissible monoidal transformation $f_{B_s}$ of $X_s$ with center
    $B_s$ for $\mathfrak R(s)$ induces the given permissible monoidal transformation $f_{\tilde B}$
    of $\tilde X$ for $\mathfrak R^{N-1}_{\mathrm{II}}$. Thus, applying Theorem
    $\mathrm{II}_2^{N-1}$ to the resolution datum $\mathfrak R^{N-1}_{\mathrm{II}}$ on $\tilde X$
    (without restriction), we can prove that there exists a finite permissible succession \dots''
    is carried out one monoidal transformation of $\tilde X$ at a time, for the emptied weak datum;
    $n'<n$, the permissibility of $h$ and $B'$, $\tilde c^{-1}(B_s)=\tilde B$ and the transport of
    the datum are proved (\cref{lem:IV.3-dim-Bs-lt}, \cref{lem:IV.3-one-block-succession},
    \cref{lem:IV.3-c-tilde-preimage}, \cref{lem:IV.3-one-block-step}). -/)
  (proofUses := ["lem:IV.3-one-block-succession", "lem:IV.3-one-block-step",
    "lem:IV.3-c-tilde-preimage", "lem:IV.3-dim-Bs-lt", "rem:IV.3-3-generic",
    "rem:IV.3-4-generic", "rem:IV.3-5-generic", "lem:IV.3-datumII-weak", "lem:IV.3-jbar-nonzero",
    "thm:I.2-I2"])
  (latexEnv := "lemma")]
theorem exists_extension_of_stageResolvable_succ [Hironaka.HironakaCitedResults.{u}]
    (N n : ℕ) (hNn : n < N)
    (hI₂ : ∀ n'' : ℕ, n'' < n → FundamentalTheorem.I₂.{u} N n'')
    (X : Scheme.{u}) (hX : IsAmbient X N) (ℜ : DatumI X)
    (P : DatumI.Presentation (ℜ : DatumI.Raw X)) (r : Restriction X)
    (hr : r.IsFor (ℜ : DatumI.Raw X)) (hn : (ℜ : DatumI.Raw X).n = (n : WithBot ℕ∞))
    (x₀ : X) (hx₀ : X.IsSimpleAt x₀) [IsRegularLocalRing (Shat X x₀)] (z : Shat X x₀) (b : ℕ)
    (Jgen : Set (Shat X x₀)) (fr : FrameSpec x₀ hx₀ (ℜ : DatumI.Raw X) r z b Jgen)
    {Y : Scheme.{u}} (g : MonoidalSuccession X Y) (hg : r.IsPermissibleSucc g ℜ)
    (hfin : HasFiniteImageOfDimEq N ℜ r g) (hbd : HasPreparedBoundary P r g)
    (hx : x₀ ∈ g.composite.base '' S (g.transformI ℜ) (r.transformSucc g))
    (k : ℕ) (hQ : StageResolvable b P r hx₀ z Jgen g (k + 1)) :
    StageResolvable b P r hx₀ z Jgen g k ∨
      ∃ (Z : Scheme.{u}) (e : MonoidalSuccession Y Z),
        r.IsPermissibleSucc (g.append e) ℜ ∧
        (x₀ ∈ (g.append e).composite.base ''
            S ((g.append e).transformI ℜ) (r.transformSucc (g.append e)) →
          StageResolvable b P r hx₀ z Jgen (g.append e) k) :=
  exists_extension_of_stageResolvable_succ_of_isDatum N n hNn hI₂ X hX ℜ ℜ.2 P r hr hn x₀ hx₀ z b
    Jgen fr g hg hfin hbd hx k hQ

end MainTheorem

end AB

end

end Hironaka

