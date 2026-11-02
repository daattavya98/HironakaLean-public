/-
Copyright (c) 2026 Daattavya Aggarwal, Minhyong Kim, Oisin Kim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daattavya Aggarwal, Minhyong Kim, Oisin Kim
-/
module

public import Hironaka.Ch4.ImplicationsCD.LemmasCD3ToCD5
public import Hironaka.Statements

/-!
# Ch. IV §4 (pp. 320–326): the prepared succession `h_s`, Remarks 1–3, and Theorems D* and D

The prepared succession `h_s` and the scheme `X̃` (pp. 320–321), the Corollary of (CD.4), the induction of
p. 321 along `ĝ_s`, the case `ν ≧ b` (Remark 1, pp. 321–322), the case `ν < b` (Remarks 2 and 3,
pp. 322–326), the lifting of a resolving succession of `X̃` (the core step), and Theorems D* and D.

This is part 3 of 3 of `Hironaka.Ch4.ImplicationsCD`, which imports all parts; its description holds the
notation and the formalization notes for the whole section.
-/

@[expose] public section

open AlgebraicGeometry IsLocalRing CategoryTheory CategoryTheory.Limits

namespace Hironaka

universe u

noncomputable section

namespace CD

variable {X : Scheme.{u}}

variable {N : ℕ} {ℜ : DatumII.Raw X} {r : Restriction X} {ν : ℕ} {T : AB.Tower X} {x₀ : X}

/-! ## The prepared succession `h_s` and the scheme `X̃` (pp. 320–321) -/

/-- p. 320: the conditions `[(1)]`, `[(2)]` on `h_s = {f_t}_{0 ≤ t ≤ s-1}` and the choice of `x_0`
in `h_s(S_ν(ℜ(s)))`. -/
@[blueprint "def:IV.4-conditions"
  (statement := /-- ``First of all, by localization theorems (Propositions 3 and 4 of \S1,
    Ch.~IV, \cref{prop:IV.1-3}, \cref{prop:IV.1-4}), we can find a permissible succession of
    monoidal transformations of $X=X_0$ for $\mathfrak R$, say $h_s=\{f_t\colon X_{t+1}\to X_t\}$
    $(0\le t\le s-1)$ such that, notation being as above, [(1)] $h_s(S_\nu(\mathfrak R(s)))$
    consists of a finite number of points at which $X$ has dimension $N$, where
    $\nu=\nu(\mathfrak R)>0$. Moreover, for the case in which $\mathfrak R=
    \mathfrak R^N_{\mathrm{II}}$ without restriction, by applying Theorem $\mathrm{II}_1^N$ a
    finite number of times (in fact, at most $\alpha$ times), we may assume that [(2)]
    $E_i(s)\cap S_\nu(\mathfrak R(s))$ is empty for $1\le i\le\alpha$. Now, let $x_0$ be any
    point of $X$ which belongs to $h_s(S_\nu(\mathfrak R(s)))$'' (p.~320,
    \cref{def:IV.4-standing}, \cref{def:IV.4-symbols}). (Formalization note (encoding): $h_s$ is the
    initial segment of the succession of \cref{def:IV.4-standing}; [(1)], [(2)] and
    $x_0\in h_s(S_\nu(\mathfrak R(s)))$ are the hypotheses of \cref{lem:IV.4-x0},
    \cref{lem:IV.4-tilde-facts} and Remarks 1--3.) -/)
  (latexEnv := "definition")]
def PrepHyp (N : ℕ) (ℜ : DatumII.Raw X) (r : Restriction X) (ν : ℕ) (T : AB.Tower X) (x₀ : X)
    (s : ℕ) : Prop :=
  ((T.pre s).composite.base '' sNu (datum T ℜ s) (restriction T r s) ν).Finite ∧
  (∀ y ∈ (T.pre s).composite.base '' sNu (datum T ℜ s) (restriction T r s) ν,
    X.dimAt y = (N : WithBot ℕ∞)) ∧
  (r = .unrestricted → ∀ i : Fin ℜ.α,
    (eSeq T ℜ s (Fin.castAdd s i)).pts ∩ sNu (datum T ℜ s) (restriction T r s) ν = ∅) ∧
  x₀ ∈ (T.pre s).composite.base '' sNu (datum T ℜ s) (restriction T r s) ν

/-- The `E_i(s)`, `i ≤ α`, of `ℜ(s)` are the strict transforms of `E_i` along `h_s`. -/
theorem eSeq_castAdd (T : AB.Tower X) (ℜ : DatumII.Raw X) :
    ∀ (s : ℕ) (i : Fin ℜ.α), eSeq T ℜ s (Fin.castAdd s i) = (T.pre s).strictTransform (ℜ.E i) := by
  intro s
  induction s with
  | zero => intro i; rfl
  | succ s ih =>
    intro i
    have hd : datum T ℜ (s + 1) = (datum T ℜ s).transform (T.monoidalTransformation s) :=
      MonoidalSuccession.transformII_snoc (T.pre s) (T.B s) (T.monoidalTransformation s) ℜ
    unfold eSeq
    rw [DatumII.Raw.E_eq_of_eq hd (j := Fin.castSucc (Fin.cast (alpha_datum T ℜ s).symm
      (Fin.castAdd s i))) (by simp), E_transform_castSucc]
    show Subscheme.strictTransform (T.monoidalTransformation s) (eSeq T ℜ s (Fin.castAdd s i)) = _
    rw [ih i]
    exact (MonoidalSuccession.strictTransform_snoc (T.pre s) (T.B s)
      (T.monoidalTransformation s) (ℜ.E i)).symm

/-- A succession permissible up to stage `n`, with empty centers from stage `n` on, is permissible
at every stage. -/
theorem pre_isPermissibleII_of_empty_tail (T : AB.Tower X) (ℜ : DatumII.Raw X) (n : ℕ)
    (hB : ∀ s, n ≤ s → T.B s = Subscheme.empty) (hg : (T.pre n).IsPermissibleII ℜ) :
    ∀ s, (T.pre s).IsPermissibleII ℜ := by
  have hdown : ∀ k s, s + k = n → (T.pre s).IsPermissibleII ℜ := by
    intro k
    induction k with
    | zero =>
      intro s hs
      obtain rfl : s = n := by omega
      exact hg
    | succ k ih =>
      intro s hs
      have h := ih (s + 1) (by omega)
      exact ((MonoidalSuccession.isPermissibleII_snoc_iff (T.pre s) (T.B s)
        (T.monoidalTransformation s) ℜ).mp h).1
  have hup : ∀ k, (T.pre (n + k)).IsPermissibleII ℜ := by
    intro k
    induction k with
    | zero => exact hg
    | succ k ih =>
      refine (MonoidalSuccession.isPermissibleII_snoc_iff (T.pre (n + k)) (T.B (n + k))
        (T.monoidalTransformation (n + k)) ℜ).mpr ⟨ih, ?_⟩
      rw [hB (n + k) (by omega)]
      exact DatumII.Raw.isPermissible_empty _
  intro s
  rcases le_total s n with h | h
  · exact hdown (n - s) s (by omega)
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
    exact hup k

/-- Not in the paper (encoding): a finite permissible succession `g` of `X` for `ℜ` satisfying the
hypotheses of the core step (`[(1)]`, `[(2)]`, `x_0 ∈ h(S_ν)`) is the initial segment `h_n` of an
`ℕ`-indexed succession (with empty centers from `n` on) satisfying the standing assumptions of
p. 314 and the hypotheses `PrepHyp` of p. 320, without restriction. -/
theorem exists_standing_prepHyp_tower [Hironaka.HironakaCitedResults.{u}] {N : ℕ} (hN : 1 ≤ N) (hX : IsAmbient X N)
    (ℜ : DatumII.Raw X) (hℜ : ℜ.IsDatum) (ν : ℕ) (hν : 0 < ν) (hνeq : (ν : ℕ∞) = ℜ.nu)
    (hno : NoCodimOneComponent (ℜ.sNu ν)) {Y : Scheme.{u}} (g : MonoidalSuccession X Y)
    (hg : g.IsPermissibleII ℜ) (hfin : (sNuImage g ℜ ν).Finite)
    (hdim : ∀ y ∈ sNuImage g ℜ ν, X.dimAt y = (N : WithBot ℕ∞))
    (hdisj : ∀ i : Fin ℜ.α, (g.strictTransform (ℜ.E i)).pts ∩ (g.transformII ℜ).sNu ν = ∅)
    {x₀ : X} (hx₀ : x₀ ∈ sNuImage g ℜ ν) :
    ∃ (T : AB.Tower X) (n : ℕ) (h : T.X n = Y), h ▸ T.pre n = g ∧
      (∀ s, n ≤ s → T.B s = Subscheme.empty) ∧
      Standing N ℜ .unrestricted ν T x₀ ∧ PrepHyp N ℜ .unrestricted ν T x₀ n := by
  obtain ⟨T, n, h, hpre, hB⟩ := AB.Tower.exists_pre_eq_of_succession g
  subst h
  have hpre' : T.pre n = g := hpre
  subst hpre'
  have hmem : x₀ ∈ ℜ.sNu ν := by
    have := hX.1
    obtain ⟨y, hy, rfl⟩ := hx₀
    obtain ⟨hY, hd⟩ := (T.pre n).isAmbient_transformII hX ℜ hℜ hg
    exact MonoidalSuccession.mem_sNu_of_mem_sNu_transformII (T.pre n) hX.2.1 ℜ hℜ hg hy
  refine ⟨T, n, rfl, rfl, hB, ⟨hN, hX, hℜ, trivial, hνeq, hνeq, hν, hno,
    pre_isPermissibleII_of_empty_tail T ℜ n hB hg, hdim x₀ hx₀, hmem⟩,
    hfin, hdim, ?_, hx₀⟩
  intro _ i
  rw [eSeq_castAdd]
  exact hdisj i

section ClosedPrepared

variable {N : ℕ} {X : Scheme.{u}}

/-- A tower with empty centers from `n` on, whose `n`-th initial segment is permissible for
`(ℜ, F)`, is permissible for `(ℜ, F)` at every stage (closed analogue of
`pre_isPermissibleII_of_empty_tail`). -/
theorem pre_isPermissibleIIClosed_of_empty_tail (T : AB.Tower X) (ℜ : DatumII.Raw X)
    (F : Subscheme X) (n : ℕ) (hB : ∀ s, n ≤ s → T.B s = Subscheme.empty)
    (hg : (T.pre n).IsPermissibleIIClosed ℜ F) : ∀ s, (T.pre s).IsPermissibleIIClosed ℜ F := by
  have hdown : ∀ k s, s + k = n → (T.pre s).IsPermissibleIIClosed ℜ F := by
    intro k
    induction k with
    | zero =>
      intro s hs
      obtain rfl : s = n := by omega
      exact hg
    | succ k ih =>
      intro s hs
      have h := ih (s + 1) (by omega)
      exact ((MonoidalSuccession.isPermissibleIIClosed_snoc_iff (T.pre s) (T.B s)
        (T.monoidalTransformation s) ℜ F).mp h).1
  have hup : ∀ k, (T.pre (n + k)).IsPermissibleIIClosed ℜ F := by
    intro k
    induction k with
    | zero => exact hg
    | succ k ih =>
      refine (MonoidalSuccession.isPermissibleIIClosed_snoc_iff (T.pre (n + k)) (T.B (n + k))
        (T.monoidalTransformation (n + k)) ℜ F).mpr ⟨ih, ?_⟩
      rw [hB (n + k) (by omega)]
      exact ⟨DatumII.Raw.isPermissible_empty _, by
        rw [Subscheme.pts_empty]; exact Set.empty_subset _⟩
  intro s
  rcases le_total s n with h | h
  · exact hdown (n - s) s (by omega)
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
    exact hup k

/-- The image in `X` of `S_ν(g*(ℜ)) ∩ F(s)`: `h_s(S_ν(ℜ(s)))` of p. 320 for `ℜ = (ℜ^N_II, F)`. -/
def sNuImageClosed {Y : Scheme.{u}} (g : MonoidalSuccession X Y) (ℜ : DatumII.Raw X)
    (F : Subscheme X) (ν : ℕ∞) : Set X :=
  g.composite.base '' sNu (g.transformII ℜ) (.closed (g.strictTransform F)) ν

/-- Further permissible transformations do not enlarge `h_s(S_ν(ℜ(s)))` (closed case). -/
theorem sNuImageClosed_append_subset [Hironaka.HironakaCitedResults.{u}] {Y Z : Scheme.{u}} (hX : IsAmbient X N)
    (ℜ : DatumII.Raw X) (hℜ : ℜ.IsDatum) (F : Subscheme X) (g : MonoidalSuccession X Y)
    (hg : g.IsPermissibleIIClosed ℜ F) (e : MonoidalSuccession Y Z)
    (he : e.IsPermissibleIIClosed (g.transformII ℜ) (g.strictTransform F)) (ν : ℕ∞) :
    sNuImageClosed (g.append e) ℜ F ν ⊆ sNuImageClosed g ℜ F ν := by
  obtain ⟨hY, hd⟩ := g.isAmbient_transformII hX ℜ hℜ hg.isPermissibleII
  have := hY.1
  rintro _ ⟨y, hy, rfl⟩
  rw [MonoidalSuccession.transformII_append, MonoidalSuccession.strictTransform_append] at hy
  refine ⟨e.composite.base y, ⟨e.mem_sNu_of_mem_sNu_transformII hY.2.1 _ hd he.isPermissibleII hy.1,
    e.pts_strictTransform_subset _ hy.2⟩, ?_⟩
  rw [MonoidalSuccession.composite_append, Scheme.Hom.comp_base, TopCat.coe_comp]
  rfl

/-- The hypothesis `[(1)]` of the core step on a finite permissible succession `g` for
`(ℜ, F)` (`x_0 ∈ h_s(S_ν(ℜ(s)))` is separate).  There is no `[(2)]` in the closed case. -/
structure PreparedClosed (N : ℕ) (ℜ : DatumII.Raw X) (F : Subscheme X) (ν : ℕ) {Y : Scheme.{u}}
    (g : MonoidalSuccession X Y) : Prop where
  isPermissibleIIClosed : g.IsPermissibleIIClosed ℜ F
  finite : (sNuImageClosed g ℜ F ν).Finite
  dimAt_eq : ∀ y ∈ sNuImageClosed g ℜ F ν, X.dimAt y = (N : WithBot ℕ∞)

theorem PreparedClosed.append [Hironaka.HironakaCitedResults.{u}] (hX : IsAmbient X N) {ℜ : DatumII.Raw X} (hℜ : ℜ.IsDatum)
    {F : Subscheme X} {ν : ℕ} {Y Z : Scheme.{u}} {g : MonoidalSuccession X Y}
    (hg : PreparedClosed N ℜ F ν g) (e : MonoidalSuccession Y Z)
    (he : e.IsPermissibleIIClosed (g.transformII ℜ) (g.strictTransform F)) :
    PreparedClosed N ℜ F ν (g.append e) := by
  have hsub := sNuImageClosed_append_subset hX ℜ hℜ F g hg.isPermissibleIIClosed e he ν
  exact ⟨(MonoidalSuccession.isPermissibleIIClosed_append g e ℜ F).mpr
    ⟨hg.isPermissibleIIClosed, he⟩, hg.finite.subset hsub, fun y hy => hg.dimAt_eq y (hsub hy)⟩

/-- Not in the paper (encoding): a tower with empty centers from `m` on, whose initial segment
`T.pre m` is permissible for `(ℜ, F)` and whose `n`-th initial segment satisfies `[(1)]` and
`x_0 ∈ h_n(S_ν(ℜ(n)))`, satisfies the standing assumptions of p. 314 and `PrepHyp` at `n`, with
the closed restriction `F` (closed analogue of `standing_prepHyp_of_tower`). -/
theorem standing_prepHyp_of_tower_closed [Hironaka.HironakaCitedResults.{u}] (hN : 1 ≤ N) (hX : IsAmbient X N)
    (ℜ : DatumII.Raw X) (hℜ : ℜ.IsDatum) (F : Subscheme X) (hF : ℜ.IsClosedRestriction F)
    (ν : ℕ) (hν : 0 < ν) (hνeq : (ν : ℕ∞) = nu ℜ (.closed F)) (hνeq' : (ν : ℕ∞) = ℜ.nu)
    (hno : NoCodimOneComponent (sNu ℜ (.closed F) ν)) {x₀ : X} (T : AB.Tower X) (n m : ℕ)
    (hB : ∀ s, m ≤ s → T.B s = Subscheme.empty) (hgm : (T.pre m).IsPermissibleIIClosed ℜ F)
    (hP : PreparedClosed N ℜ F ν (T.pre n)) (hx₀ : x₀ ∈ sNuImageClosed (T.pre n) ℜ F ν) :
    Standing N ℜ (.closed F) ν T x₀ ∧ PrepHyp N ℜ (.closed F) ν T x₀ n := by
  have hmem : x₀ ∈ sNu ℜ (.closed F) ν := by
    have := hX.1
    obtain ⟨y, hy, rfl⟩ := hx₀
    obtain ⟨hY, hd⟩ := (T.pre n).isAmbient_transformII hX ℜ hℜ
      hP.isPermissibleIIClosed.isPermissibleII
    exact ⟨MonoidalSuccession.mem_sNu_of_mem_sNu_transformII (T.pre n) hX.2.1 ℜ hℜ
      hP.isPermissibleIIClosed.isPermissibleII hy.1,
      MonoidalSuccession.pts_strictTransform_subset _ F hy.2⟩
  exact ⟨⟨hN, hX, hℜ, hF, hνeq, hνeq', hν, hno,
    pre_isPermissibleIIClosed_of_empty_tail T ℜ F m hB hgm, hP.dimAt_eq x₀ hx₀, hmem⟩,
    hP.finite, hP.dimAt_eq, (fun h => nomatch h), hx₀⟩

/-- Not in the paper (encoding): a finite permissible succession `g` of `X` for `(ℜ, F)`
satisfying `[(1)]` and `x_0 ∈ h(S_ν)` is the initial segment `h_n` of an `ℕ`-indexed succession
(with empty centers from `n` on) satisfying the standing assumptions of p. 314 and the hypotheses
`PrepHyp` of p. 320, with the closed restriction `F` (Theorem C). -/
theorem exists_standing_prepHyp_tower_closed [Hironaka.HironakaCitedResults.{u}] (hN : 1 ≤ N) (hX : IsAmbient X N)
    (ℜ : DatumII.Raw X) (hℜ : ℜ.IsDatum) (F : Subscheme X) (hF : ℜ.IsClosedRestriction F)
    (ν : ℕ) (hν : 0 < ν) (hνeq : (ν : ℕ∞) = nu ℜ (.closed F)) (hνeq' : (ν : ℕ∞) = ℜ.nu)
    (hno : NoCodimOneComponent (sNu ℜ (.closed F) ν)) {Y : Scheme.{u}} (g : MonoidalSuccession X Y)
    (hP : PreparedClosed N ℜ F ν g) {x₀ : X} (hx₀ : x₀ ∈ sNuImageClosed g ℜ F ν) :
    ∃ (T : AB.Tower X) (n : ℕ) (h : T.X n = Y), h ▸ T.pre n = g ∧
      (∀ s, n ≤ s → T.B s = Subscheme.empty) ∧
      Standing N ℜ (.closed F) ν T x₀ ∧ PrepHyp N ℜ (.closed F) ν T x₀ n := by
  obtain ⟨T, n, h, hpre, hB⟩ := AB.Tower.exists_pre_eq_of_succession g
  subst h
  have hpre' : T.pre n = g := hpre
  subst hpre'
  exact ⟨T, n, rfl, rfl, hB, standing_prepHyp_of_tower_closed hN hX ℜ hℜ F hF ν hν hνeq hνeq' hno
    T n n hB hP.isPermissibleIIClosed hP hx₀⟩

end ClosedPrepared

/-- p. 320: "Clearly, `x_0` belongs to `S_ν(ℜ)`"; and `X` has dimension `N` at `x_0` by `[(1)]`. -/
@[blueprint "lem:IV.4-x0"
  (statement := /-- Let $h_s$ and $x_0\in h_s(S_\nu(\mathfrak R(s)))$ be as in
    \cref{def:IV.4-conditions}, $\nu=\nu(\mathfrak R)>0$. Clearly, $x_0$ belongs to
    $S_\nu(\mathfrak R)$; and $X$ has dimension $N$ at $x_0$. (p.~320.) -/)
  (proof := /-- The second assertion is [(1)]. For the first, a permissible monoidal
    transformation does not increase the orders: $\nu(J'_{x'})\le\nu(J_{f(x')})$ (Lemma~8, \S3,
    Ch.~III, \cref{lem:III.8}), and $f(S(f^*(\mathfrak R)))\subseteq S(\mathfrak R)$, so
    $h_s(S_\nu(\mathfrak R(s)))\subseteq S_\nu(\mathfrak R)$ (as in the proof of
    \cref{prop:IV.1-3}); in the closed case $h_s(F(s))\subseteq F$. -/)
  (proofUses := ["lem:III.8", "prop:IV.1-3"])
  (latexEnv := "lemma")]
theorem PrepHyp.x₀_mem_Snu_and_dimAt_eq [Hironaka.HironakaCitedResults.{u}] (hX : IsAmbient X N) (hℜ : ℜ.IsDatum) (hr : r.IsFor ℜ)
    (hνeq : (ν : ℕ∞) = nu ℜ r) (_hν : 0 < ν) (hT : ∀ s, r.IsPermissibleSucc (T.pre s) ℜ)
    (s : ℕ) (hprep : PrepHyp N ℜ r ν T x₀ s) :
    x₀ ∈ sNu ℜ r ν ∧ X.dimAt x₀ = (N : WithBot ℕ∞) := by
  obtain ⟨y, hy, rfl⟩ := hprep.2.2.2
  refine ⟨?_, hprep.2.1 _ ⟨y, hy, rfl⟩⟩
  have := hX.1
  cases r with
  | unrestricted =>
    exact MonoidalSuccession.mem_sNu_of_mem_sNu_transformII (T.pre s) hX.2.1 ℜ hℜ (hT s) hy
  | closed F =>
    exact ⟨MonoidalSuccession.mem_sNu_of_mem_sNu_transformII (T.pre s) hX.2.1 ℜ hℜ
      (MonoidalSuccession.IsPermissibleIIClosed.isPermissibleII (hT s)) hy.1,
      MonoidalSuccession.pts_strictTransform_subset _ F hy.2⟩

/-- `α̃` (p. 321): `α + s` for `ℜ = (ℜ^N_II, F)`, `s` without restriction. -/
def alphaT : Restriction X → ℕ → ℕ → ℕ
  | .closed _, α, s => α + s
  | .unrestricted, _, s => s

/-- `α̃` for `s + 1` is `α̃ + 1` (p. 324: "`1 ≦ j ≦ α̃ + 1 = α + s + 1`", resp. "`= s + 1`"). -/
theorem alphaT_succ (r : Restriction X) (α s : ℕ) : alphaT r α (s + 1) = alphaT r α s + 1 := by
  cases r <;> rfl

/-- The index of `E_j(s)` giving `Ẽ_j` (p. 321): `j` in the closed case, `α + j` without
restriction. -/
def idxT (α s : ℕ) : (r : Restriction X) → Fin (alphaT r α s) → Fin (α + s)
  | .closed _, j => j
  | .unrestricted, j => Fin.natAdd α j

/-- `c_j` (p. 322): `a_j` for `ℜ = (ℜ^N_II, F)`, `a_{α+j}` without restriction
(`1 ≦ j ≦ α̃`), the `a`'s being those of `ℜ^N_II(s)`. -/
def cT (T : AB.Tower X) (ℜ : DatumII.Raw X) (r : Restriction X) (s : ℕ)
    (j : Fin (alphaT r ℜ.α s)) : ℕ :=
  aSeq T ℜ s (idxT ℜ.α s r j)

/-- `(ã_1, …, ã_{α̃}, ã_{α̃+1})`: the integers `ã_j` followed by a new one, indexed for `s + 1`. -/
def extendA {r : Restriction X} {α s : ℕ} (a : Fin (alphaT r α s) → ℕ) (anew : ℕ) :
    Fin (alphaT r α (s + 1)) → ℕ :=
  fun j => Fin.snoc (α := fun _ => ℕ) a anew (Fin.cast (alphaT_succ r α s) j)

namespace Frame

variable {hS : Standing N ℜ r ν T x₀} (𝒮 : Frame hS)

/-- `X̃ = X̄_s` as a scheme (p. 321). -/
abbrev xTilde (s : ℕ) : Scheme.{u} := (𝒮.xBar s).toScheme

/-- `Ê_j(s) = c_s⁻¹(E_j(s))` for `1 ≦ j ≦ α + s` (p. 321). -/
def eHat (s : ℕ) (j : Fin (ℜ.α + s)) : Subscheme (𝒮.tHat.X s) :=
  Subscheme.totalTransform (𝒮.c s) (eSeq T ℜ s j)

/-- `Ẽ_j` (p. 321): `Ê_j(s) ∩ X̃` (`1 ≦ j ≦ α̃ = α + s`) for `ℜ = (ℜ^N_II, F)`, and
`Ê_{α+j}(s) ∩ X̃` (`1 ≦ j ≦ α̃ = s`) without restriction. -/
@[blueprint "def:IV.4-tilde"
  (statement := /-- With $h_s$ and $x_0$ as in \cref{def:IV.4-conditions}, construct
    $\hat h_s=\{\hat f_t\colon\hat X_{t+1}\to\hat X_t\}$ $(0\le t\le s-1)$ and coherent sheaves of
    ideals $\bar J(t)$ on $\bar X_t$ $(0\le t\le s)$ (\cref{def:IV.4-frame},
    \cref{def:IV.4-construction}). Let $\bar c_t\colon\bar X_t\to X_t$ be the morphism induced by
    $c_t\colon\hat X_t\to X_t$ for $0\le t\le s$. Let $\tilde X$ denote the non-singular
    irreducible scheme $\bar X_s$ of dimension $N-1$. Let us write $\mathfrak R^N_{\mathrm{II}}(s)
    =\big(E_1(s),\dots,E_{\alpha+s}(s)\,\big|\,J(s),b\,\big|\,a_1,\dots,a_{\alpha+s}\big)$ as
    above, and let $\hat E_j(s)=c_s^{-1}(E_j(s))$ for $1\le j\le\alpha+s$. We define in each case
    an integer $\tilde\alpha$ and non-singular irreducible subschemes $\tilde E_j$
    $(1\le j\le\tilde\alpha)$ of $\tilde X$ as follows: (i) If $\mathfrak R=
    (\mathfrak R^N_{\mathrm{II}},F)$, then $\tilde\alpha=\alpha+s$ and $\tilde E_j=\hat E_j(s)\cap
    \tilde X$ for $1\le j\le\tilde\alpha$. (ii) If $\mathfrak R=\mathfrak R^N_{\mathrm{II}}$, then
    $\tilde\alpha=s$ and $\tilde E_j=\hat E_{\alpha+j}(s)\cap\tilde X$ for $1\le j\le\tilde\alpha$.
    (p.~321.) (Formalization note (encoding): $\tilde E_j$ is the total transform of $\hat E_j(s)$ on
    $\tilde X$; the facts stated on p.~321 are \cref{lem:IV.4-tilde-facts}.) -/)
  (latexEnv := "definition")]
def eTilde (s : ℕ) (j : Fin (alphaT r ℜ.α s)) : Subscheme (𝒮.xTilde s) :=
  Subscheme.totalTransform (𝒮.xBar s).ι (𝒮.eHat s (idxT ℜ.α s r j))

/-- A resolution datum `(Ẽ_1, …, Ẽ_α̃ | J̃, b̃ | ã_1, …, ã_α̃)` on `X̃` (pp. 321, 323). -/
@[blueprint "def:IV.4-case-ge"
  (statement := /-- \emph{The case $\nu\ge b$} (p.~321). On the non-singular irreducible algebraic scheme $\tilde X=\bar X_s$
    (\cref{def:IV.4-tilde}), we have defined a coherent sheaf of ideals $\bar J(s)$. We have also
    defined a positive integer $\bar b$ (\cref{def:IV.4-construction}). We shall consider a
    resolution datum $\mathfrak R^{N-1}_{\mathrm{II}}$ on $\tilde X$ defined as follows:
    $\mathfrak R^{N-1}_{\mathrm{II}}=\big(\tilde E_1,\dots,\tilde E_{\tilde\alpha}\,\big|\,
    \tilde J,\tilde b\,\big|\,\tilde a_1,\dots,\tilde a_{\tilde\alpha}\big)$, where (i)
    $\tilde b=\bar b>0$, (ii) $\tilde a_j$ $(1\le j\le\tilde\alpha)$ are non-negative integers
    such that, if $\tilde P_j$ denotes the coherent sheaf of ideals of the subscheme $\tilde E_j$
    of $\tilde X$ for $1\le j\le\tilde\alpha$, then $\bar J(s)=\tilde J\cdot\prod_{j=1}^{\tilde
    \alpha}(\tilde P_j^{\tilde a_j})$, (iii) $\tilde J$ is a coherent sheaf of ideals on
    $\tilde X$, subject to the above equality. The above resolution datum
    $\mathfrak R^{N-1}_{\mathrm{II}}$ is not uniquely determined but will be abitrarily [sic]
    fixed. We can take, for example, $\tilde J$ to be $\bar J(s)$ and $\tilde a_j=0$ for all $j$.
    (p.~321.) (Formalization note (encoding): the datum is determined by $\tilde a$, $\tilde J$ and
    $\tilde b$, the equality being a hypothesis where it is used, and is assumed to be a
    resolution datum, \cref{def:I.3-II}.) -/)
  (latexEnv := "definition")]
def datumTilde (s : ℕ) (bt : ℕ) (a : Fin (alphaT r ℜ.α s) → ℕ) (Jt : Subscheme (𝒮.xTilde s)) :
    DatumII.Raw (𝒮.xTilde s) where
  α := alphaT r ℜ.α s
  E := 𝒮.eTilde s
  a := a
  J := Jt
  b := bt

/-- `J̄*(s) = (J̄(s)^{b-ν}, (∏_{j=1}^{α̃} P̃_j^{c_j})^{b̄})` (p. 322), the sheaf of ideals generated
by the two (the sum of ideal sheaves).

As printed this is wrong when `F = E_i` with `a_i > 0` (closed case): then `P̃_i = (0)` and the second
generator vanishes.  The counterexample is in the docstring of
`Frame.S_datumTilde_eq_and_bijOn_cBar_and_exists_isPermissibleCenter_of_lt` (Remark 2, `rem:IV.4-2`);
the repaired definition is `Frame.jBarRep` (`def:IV.4-case-lt-repaired`). -/
@[blueprint "def:IV.4-case-lt"
  (statement := /-- \emph{The case $\nu<b$} $(\nu=\nu(\mathfrak R)>0)$. Let $\bar J(s)$ and
    $\bar b$ be as before (\cref{def:IV.4-construction}). In this case we first define a coherent
    sheaf of ideals $\bar J^*(s)$ on $\bar X_s$ as follows:
    $\bar J^*(s)=\big(\bar J(s)^{b-\nu},(\prod_{j=1}^{\tilde\alpha}\tilde P_j^{c_j})^{\bar b}\big)$,
    which denotes the coherent sheaf of ideals on $\bar X_s$ generated by the $(b-\nu)$th power of
    $\bar J(s)$ and by the $\bar b$th power of the product $\prod_{j=1}^{\tilde\alpha}\tilde
    P_j^{c_j}$ (in the sheaf of local rings of $\bar X_s$), where $\tilde P_j=$ the sheaf of
    ideals of the subscheme $\tilde E_j$ of $\tilde X$ $(1\le j\le\tilde\alpha)$ and $c_j=a_j$ for
    the case of $\mathfrak R=(\mathfrak R^N_{\mathrm{II}},F)$, $c_j=a_{\alpha+j}$ for the case of
    $\mathfrak R=\mathfrak R^N_{\mathrm{II}}$ (without restriction) $(1\le j\le\tilde\alpha)$
    (\cref{def:IV.4-tilde}). We shall consider a resolution datum $\mathfrak R^{N-1}_{\mathrm{II}}$
    without restriction on $\tilde X$ defined as follows: $\mathfrak R^{N-1}_{\mathrm{II}}=
    \big(\tilde E_1,\dots,\tilde E_{\tilde\alpha}\,\big|\,\tilde J,\tilde b\,\big|\,\tilde a_1,
    \dots,\tilde a_{\tilde\alpha}\big)$ where (i) $\tilde b=\bar b(b-\nu)$, (ii) $\tilde a_j$
    $(1\le j\le\tilde\alpha)$ are non-negative integers, and (iii) $\tilde J$ is a coherent sheaf
    of ideals on $\tilde X$ such that $\bar J^*(s)=\tilde J\cdot\prod_{j=1}^{\tilde\alpha}
    (\tilde P_j^{\tilde a_j})$. Such a resolution datum is not uniquely determined except the
    last product equal to $\bar J^*(s)$. In the sequel we fix an arbitrary
    $\mathfrak R^{N-1}_{\mathrm{II}}$ on $\tilde X$ which is subject to the conditions. We can
    take, for example, $\tilde a_j=0$ for all $j$ and $\tilde J=\bar J^*(s)$. (pp.~322--323.)

    \textbf{Error of the paper ($F=E_i$).} If $F=E_i$ with $a_i>0$ (closed case) then
    $\tilde P_i=(0)$ and the second generator of $\bar J^*(s)$ vanishes; the consequences, with a
    counterexample, are at \cref{rem:IV.4-2}, and the repaired definition is
    \cref{def:IV.4-case-lt-repaired}.
    (Formalization notes (encoding): the sheaf generated by two sheaves of ideals is their sum; $b-\nu$ is
    a truncated difference, positive in this case; the datum is \cref{def:IV.4-case-ge}'s
    construction with $\tilde b=\bar b(b-\nu)$. The same definitions at $s+1$ give the
    $\tilde E'_j$, $c'_j$, $\tilde P'_j$ and $\bar J^*(s+1)$ of pp.~324--325.) -/)
  (latexEnv := "definition")]
def jBarStar (s : ℕ) : Subscheme (𝒮.xTilde s) :=
  (𝒮.jBar s) ^ (ℜ.b - ν) + (∏ j, (𝒮.eTilde s j) ^ (cT T ℜ r s j)) ^ 𝒮.bBar

end Frame

open StrictDim in
/-- `dim V(I) = dim R/I` for a prime `I` (the dimension of the closed subscheme `V(I)` of `Spec R`
is the supremum of the dimensions `dim R/q` over the primes `q ⊇ I`). -/
theorem dim_ofIdealTop_spec (R : CommRingCat.{u}) (I : Ideal R) [I.IsPrime] :
    Subscheme.dim (Scheme.IdealSheafData.ofIdealTop
      (I.map (Scheme.ΓSpecIso R).inv.hom) : Subscheme (Spec R)) = ringKrullDim (R ⧸ I) := by
  set D : Subscheme (Spec R) := Scheme.IdealSheafData.ofIdealTop
      (I.map (Scheme.ΓSpecIso R).inv.hom) with hD
  apply le_antisymm
  · refine StrictDim.dim_le_of_forall D fun x hx => ?_
    have hle := (mem_pts_ofIdealTop_spec R I x).mp hx
    rw [height_spec_eq_coheight, coheight_eq_ringKrullDim_quotient]
    exact ringKrullDim_le_of_surjective _ (Ideal.Quotient.factor_surjective hle)
  · have hx : (show Spec R from (⟨I, inferInstance⟩ : PrimeSpectrum R)) ∈ D.pts :=
      (mem_pts_ofIdealTop_spec R I _).mpr le_rfl
    have := StrictDim.height_le_dim D hx
    rwa [height_spec_eq_coheight, coheight_eq_ringKrullDim_quotient] at this

namespace Frame
variable {hS : Standing N ℜ r ν T x₀} (𝒮 : Frame hS)

/-- `dim X̄_0 = N - 1` (p. 316). -/
theorem dim_xBar_zero : (𝒮.xBar 0).dim = ((N - 1 : ℕ) : WithBot ℕ∞) := by
  have h := 𝒮.isPrime_span_z_and_ringKrullDim_quotient
  have := h.1
  have := dim_ofIdealTop_spec (CommRingCat.of (AB.Shat X x₀)) (Ideal.span {𝒮.z})
  exact this.trans h.2

end Frame

/-- The point set of an irreducible subscheme is irreducible. -/
theorem isIrreducible_pts {Y : Scheme.{u}} (D : Subscheme Y) (hD : D.IsIrreducible) :
    _root_.IsIrreducible D.pts := by
  have : IrreducibleSpace D.toScheme := hD
  have hpts : D.pts = Set.range D.ι := by
    ext x
    refine ⟨fun h => ?_, fun ⟨z, hz⟩ => hz ▸ Subscheme.mem_pts_ι D z⟩
    obtain ⟨z, hz⟩ := Subscheme.exists_ι_eq_of_mem_pts D h
    exact ⟨z, hz⟩
  rw [hpts, ← Set.image_univ]
  exact (IrreducibleSpace.isIrreducible_univ D.toScheme).image _ D.ι.continuous.continuousOn

/-- The point set of an irreducible subscheme is non-empty. -/
theorem pts_nonempty_of_isIrreducible {Y : Scheme.{u}} (D : Subscheme Y) (hD : D.IsIrreducible) :
    D.pts.Nonempty :=
  (isIrreducible_pts D hD).nonempty

/-! ### The induction of p. 321 along `ĝ_s` (facts on `Ê_j(s)`, `X̃`, `Ẽ_j`) -/

/-- `c_0(x̂_0) = x_0` (p. 295). -/
theorem c0_xhat0 {X : Scheme.{u}} (x₀ : X) (hx : X.IsSimpleAt x₀) :
    (AB.c0 X x₀).base (AB.xhat0 X x₀ hx) = x₀ := by
  have : IsRegularLocalRing (X.presheaf.stalk x₀) := hx
  show X.fromSpecStalk x₀ (Spec.map (CommRingCat.ofHom (algebraMap (X.presheaf.stalk x₀)
    (AB.Shat X x₀))) (IsLocalRing.closedPoint (AB.Shat X x₀))) = x₀
  have hloc : IsLocalHom (algebraMap (X.presheaf.stalk x₀) (AB.Shat X x₀)) := inferInstance
  have : IsLocalHom (CommRingCat.ofHom (algebraMap (X.presheaf.stalk x₀) (AB.Shat X x₀))).hom :=
    hloc
  rw [Spec_closedPoint, Scheme.fromSpecStalk_closedPoint]

/-- `CentersAdaptedNonsingular` along `g` followed by one more step. -/
theorem _root_.Hironaka.MonoidalSuccession.centersAdaptedNonsingular_snoc :
    ∀ {X Y : Scheme.{u}} (g : MonoidalSuccession X Y)
    (ℜ : DatumI.Raw X) (B : Subscheme Y) (t : MonoidalTransformation Y B),
    (MonoidalSuccession.snoc g B t).CentersAdaptedNonsingular ℜ ↔
      g.CentersAdaptedNonsingular ℜ ∧ (B.IsNonsingular ∧ B.IsContainedIn (g.transformI ℜ).W ∧
        (∀ x ∈ B.pts, (g.transformI ℜ).E.HasOnlyNormalCrossingsWithAt B x) ∧
        ¬ (g.transformI ℜ).W.pts ⊆ B.pts)
  | _, _, .nil _, ℜ, B, t => by
    simp only [MonoidalSuccession.snoc, Hironaka.MonoidalSuccession.CentersAdaptedNonsingular,
      and_true, true_and]
    rfl
  | _, _, .cons B' t' rest, ℜ, B, t => by
    simp only [MonoidalSuccession.snoc, Hironaka.MonoidalSuccession.CentersAdaptedNonsingular,
      Hironaka.MonoidalSuccession.transformI_cons]
    rw [Hironaka.MonoidalSuccession.centersAdaptedNonsingular_snoc rest (ℜ.transform t') B t]
    tauto

/-- `E_j(s+1)` for `j < α + s` is the strict transform of `E_j(s)` (p. 314, Definition 7 (II)). -/
theorem eSeq_succ_of_lt (T : AB.Tower X) (ℜ : DatumII.Raw X) (s j : ℕ) (hj : j < ℜ.α + s) :
    eSeq T ℜ (s + 1) ⟨j, by omega⟩ =
      Subscheme.strictTransform (T.monoidalTransformation s) (eSeq T ℜ s ⟨j, hj⟩) := by
  have hd : datum T ℜ (s + 1) = (datum T ℜ s).transform (T.monoidalTransformation s) :=
    MonoidalSuccession.transformII_snoc (T.pre s) (T.B s) (T.monoidalTransformation s) ℜ
  unfold eSeq
  rw [DatumII.Raw.E_eq_of_eq hd (j := Fin.castSucc (Fin.cast (alpha_datum T ℜ s).symm ⟨j, hj⟩))
    (by simp), E_transform_castSucc]

/-- `E_{α+s+1}(s+1)` is the exceptional divisor of `f_s` (p. 314). -/
theorem eSeq_succ_last (T : AB.Tower X) (ℜ : DatumII.Raw X) (s : ℕ) :
    eSeq T ℜ (s + 1) ⟨ℜ.α + s, by omega⟩ = (T.monoidalTransformation s).exceptional := by
  have hd : datum T ℜ (s + 1) = (datum T ℜ s).transform (T.monoidalTransformation s) :=
    MonoidalSuccession.transformII_snoc (T.pre s) (T.B s) (T.monoidalTransformation s) ℜ
  unfold eSeq
  rw [DatumII.Raw.E_eq_of_eq hd (j := Fin.last (datum T ℜ s).α)
    (by simp [alpha_datum]), E_transform_last]

/-- The indices `j` such that `E_j(s)` belongs to the boundary of the datum on `X̂_s` (p. 321):
all of them in the closed case, `α < j ≤ α + s` without restriction. -/
def inBoundary (r : Restriction X) (α s : ℕ) (j : Fin (α + s)) : Prop :=
  match r with
  | .closed _ => True
  | .unrestricted => α ≤ j.val

theorem inBoundary_succ (r : Restriction X) (α s : ℕ) (j : Fin (α + (s + 1))) :
    inBoundary r α (s + 1) j ↔
      j.val = α + s ∨ ∃ h : j.val < α + s, inBoundary r α s ⟨j.val, h⟩ := by
  cases r with
  | closed F =>
    simp only [inBoundary, true_iff]
    by_cases h : j.val < α + s
    · exact Or.inr ⟨h, trivial⟩
    · left; have := j.2; omega
  | unrestricted =>
    simp only [inBoundary]
    constructor
    · intro h1
      by_cases h : j.val < α + s
      · exact Or.inr ⟨h, h1⟩
      · left; have := j.2; omega
    · rintro (h | ⟨h, h2⟩)
      · omega
      · exact h2

/-- The datum `ℜ^N_II(s)` is a resolution datum, `X_s` is ambient (permissible succession). -/
theorem Standing.isDatum_datum [Hironaka.HironakaCitedResults.{u}] (hS : Standing N ℜ r ν T x₀) (s : ℕ) : (datum T ℜ s).IsDatum := by
  have := hS.ambient.1
  exact (MonoidalSuccession.isAmbient_transformII (T.pre s) hS.ambient ℜ hS.isDatum
    (hS.permissible s).isPermissibleII).2

/-- `(⨅ j, E_j(s))` is the union `E_1(s) ∪ ⋯ ∪ E_{α+s}(s)` of the datum `ℜ^N_II(s)`. -/
theorem eUnion_datum_eq (T : AB.Tower X) (ℜ : DatumII.Raw X) (s : ℕ) :
    (datum T ℜ s).eUnion = ⨅ j : Fin (ℜ.α + s), eSeq T ℜ s j :=
  (Equiv.iInf_comp (g := (datum T ℜ s).E) (finCongr (alpha_datum T ℜ s).symm)).symm

theorem Standing.isNonsingular_eSeq [Hironaka.HironakaCitedResults.{u}] (hS : Standing N ℜ r ν T x₀) (s : ℕ) (j : Fin (ℜ.α + s)) : (eSeq T ℜ s j).IsNonsingular :=
  (hS.isDatum_datum s).2.1 _ |>.isNonsingular

/-- Stalk presentation of every `E_j(s)` by a member of a regular system of parameters. -/
theorem Standing.exists_stalkIdeal_eSeq [Hironaka.HironakaCitedResults.{u}] (hS : Standing N ℜ r ν T x₀) (s : ℕ) (j : Fin (ℜ.α + s)) (x : T.X s) :
    (eSeq T ℜ s j).stalkIdeal x = ⊤ ∨
      ∃ a, ExtendsToRSOP _ {a} ∧ (eSeq T ℜ s j).stalkIdeal x = Ideal.span {a} := by
  have hd := hS.isDatum_datum s
  have : IsRegularLocalRing ((T.X s).presheaf.stalk x) := hS.isNonsingular_X s x
  obtain ⟨Z, hZ, -, hE⟩ := DatumTransform.exists_rsop_adapted_of_isDatum (B := ⊥)
    (datum T ℜ s).E (hS.isNonsingular_X s) hd.2.1 hd.2.2.1 (fun x _ => hd.2.2.1 x) x
  rcases hE (Fin.cast (alpha_datum T ℜ s).symm j) with h | ⟨a, haZ, h⟩
  · exact Or.inl h
  · exact Or.inr ⟨a, ⟨Z, by simpa using haZ, hZ⟩, h⟩

theorem Standing.mem_pts_closed_x₀ (hS : Standing N ℜ r ν T x₀) {F : Subscheme X}
    (hr : r = .closed F) : x₀ ∈ F.pts := by
  subst hr
  exact hS.mem_Snu.2

theorem pts_iInf_idxT {Z : Scheme.{u}} (r : Restriction X) (α t : ℕ) (E : Fin (α + t) → Subscheme Z) :
    (⨅ i : Fin (alphaT r α t), E (idxT α t r i)).pts =
      ⋃ j ∈ {j : Fin (α + t) | inBoundary r α t j}, (E j).pts := by
  cases r with
  | closed F =>
    rw [show (⨅ i : Fin (alphaT (.closed F) α t), E (idxT α t (.closed F) i)) =
      ⨅ i : Fin (α + t), E i from rfl, Subscheme.pts_iInf]
    ext x
    simp [inBoundary]
  | unrestricted =>
    rw [show (⨅ i : Fin (alphaT (.unrestricted : Restriction X) α t),
        E (idxT α t .unrestricted i)) = ⨅ i : Fin t, E (Fin.natAdd α i) from rfl,
      Subscheme.pts_iInf]
    ext x
    simp only [Set.mem_iUnion, Set.mem_ofPred_eq, inBoundary, exists_prop]
    constructor
    · rintro ⟨i, hi⟩
      exact ⟨Fin.natAdd α i, by simp, hi⟩
    · rintro ⟨j, hj, hx⟩
      refine ⟨⟨j.val - α, by omega⟩, ?_⟩
      have : Fin.natAdd α (⟨j.val - α, by omega⟩ : Fin t) = j := Fin.ext (by simp; omega)
      rw [this]; exact hx

theorem Standing.isPermissible_B (hS : Standing N ℜ r ν T x₀) (t : ℕ) :
    (datum T ℜ t).IsPermissible (T.B t) := by
  have h := hS.isPermissibleCenter_B t
  generalize restriction T r t = R at h
  cases R with
  | unrestricted => exact h
  | closed F => exact h.1

theorem Standing.exists_isSimpleAt_codimAt_eSeq [Hironaka.HironakaCitedResults.{u}] (hS : Standing N ℜ r ν T x₀) (s : ℕ)
    (j : Fin (ℜ.α + s)) (x : T.X s) (hx : x ∈ (eSeq T ℜ s j).pts) :
    (eSeq T ℜ s j).IsSimpleAt x ∧ (eSeq T ℜ s j).codimAt x = 1 := by
  have : IsRegularLocalRing ((T.X s).presheaf.stalk x) := hS.isNonsingular_X s x
  obtain ⟨a, ha, h⟩ := (hS.exists_stalkIdeal_eSeq s j x).resolve_left
    (Subscheme.mem_pts_iff_stalkIdeal_ne_top.mp hx)
  exact Subscheme.isSimpleAt_and_codimAt_eq_one_of_stalkIdeal_eq_span ha h

namespace Frame
variable {hS : Standing N ℜ r ν T x₀} (𝒮 : Frame hS)

/-- `dim X̄_{t+1} = dim X̄_t` when `X̄_t` and `X̄_{t+1}` are irreducible: the strict transform of an
irreducible subscheme not contained in the center (Remark 1, p. 169). -/
theorem dim_xBar_succ [Hironaka.HironakaCitedResults.{u}] (t : ℕ) [IsAlgebraicScheme (𝒮.tHat.X t)] (h0 : (𝒮.xBar t).IsIrreducible)
    (h1 : (𝒮.xBar (t + 1)).IsIrreducible) : (𝒮.xBar (t + 1)).dim = (𝒮.xBar t).dim := by
  have hne := pts_nonempty_of_isIrreducible _ h1
  show (Subscheme.strictTransform (𝒮.tHat.monoidalTransformation t) (𝒮.xBar t)).dim = _
  refine MonoidalTransformation.dim_strictTransform_eq _ _ ?_
  intro C hC hCB
  obtain ⟨Z, hZ, rfl⟩ := hC
  rw [Subscheme.pts_ofClosed] at hCB
  have hirr := isIrreducible_pts _ h0
  have hclosed : IsClosed (𝒮.xBar t).pts := (𝒮.xBar t).support.isClosed
  have hle : (𝒮.xBar t).pts ⊆ Z := by
    have := hZ.2 (y := ⟨(𝒮.xBar t).pts, hclosed⟩) ⟨hirr, le_rfl⟩ hZ.1.2
    exact this
  have := pts_strictTransform_eq_empty_of_subset (𝒮.tHat.monoidalTransformation t) (𝒮.xBar t)
    (hle.trans hCB)
  exact hne.ne_empty this

/-- The algebraic scheme `X̂_0 = Spec(Ŝ_0)` (p. 295: "The algebraic scheme `X̂_0 = Spec(Ŝ)`"). -/
theorem _root_.Hironaka.CD.Standing.isAlgebraicScheme_xHat0 [Hironaka.HironakaCitedResults.{u}] (hS : Standing N ℜ r ν T x₀) :
    IsAlgebraicScheme (AB.xHat0 X x₀) := by
  have := hS.ambient.1
  exact AB.isAlgebraicScheme_xHat0 X x₀

/-- Every `X̂_s` is an algebraic scheme: `X̂_{s+1}` is a monoidal transform of `X̂_s`. -/
theorem isAlgebraicScheme_tHat_X [Hironaka.HironakaCitedResults.{u}] : ∀ t : ℕ, IsAlgebraicScheme (𝒮.tHat.X t)
  | 0 => hS.isAlgebraicScheme_xHat0
  | t + 1 => by
    have := isAlgebraicScheme_tHat_X t
    exact (𝒮.tHat.monoidalTransformation t).isAlgebraicScheme

/-- `X̄_t` is non-singular, irreducible and of dimension `N - 1` for `t ≤ s` when the conditions
(1)–(3) of `[vii]` hold up to `s` (p. 321, first sentence of the "we see" facts). -/
theorem isNonsingular_and_isIrreducible_and_dim_xBar [Hironaka.HironakaCitedResults.{u}] (s : ℕ) (hadm : 𝒮.IsAdmissibleAt s) :
    (𝒮.xBar s).IsNonsingular ∧ (𝒮.xBar s).IsIrreducible ∧
      (𝒮.xBar s).dim = ((N - 1 : ℕ) : WithBot ℕ∞) := by
  have hirr : ∀ t, t ≤ s → (𝒮.xBar t).IsIrreducible := fun t ht => by
    rcases ht.lt_or_eq with h | rfl
    · exact (hadm.2.2.1 t h).1.2
    · exact hadm.1.2
  refine ⟨hadm.1.1, hadm.1.2, ?_⟩
  have key : ∀ t, t ≤ s → (𝒮.xBar t).dim = ((N - 1 : ℕ) : WithBot ℕ∞) := by
    intro t
    induction t with
    | zero => intro _; exact 𝒮.dim_xBar_zero
    | succ t ih =>
      intro ht
      have := 𝒮.isAlgebraicScheme_tHat_X t
      rw [𝒮.dim_xBar_succ t (hirr t (by omega)) (hirr (t + 1) ht)]
      exact ih (by omega)
  exact key s le_rfl

/-- `S_ν(ℜ(s))` is non-empty when `x_0 ∈ h_s(S_ν(ℜ(s)))` (p. 320). -/
theorem _root_.Hironaka.CD.PrepHyp.sNu_nonempty {s : ℕ} (hprep : PrepHyp N ℜ r ν T x₀ s) :
    (sNu (datum T ℜ s) (restriction T r s) ν).Nonempty := by
  obtain ⟨y, hy, -⟩ := hprep.2.2.2
  exact ⟨y, hy⟩

/-- `X̄_s` satisfies the conditions (1)–(3) of `[vii]` at `s` under the hypotheses of p. 320
(Lemma (CD.4), since `S_ν(ℜ(s))` is non-empty). -/
theorem isAdmissibleAt_of_prepHyp [Hironaka.HironakaCitedResults.{u}] {s : ℕ} (hprep : PrepHyp N ℜ r ν T x₀ s) :
    𝒮.IsAdmissibleAt s :=
  𝒮.isAdmissibleAt_of_mem_image_sNu s hprep.2.2.2

/-- At a point of `X̂_s` over `x̂_0` the local ring is regular and `c_s` induces a map of local rings
transforming a regular system of parameters into one (Lemma (AB.2)). -/
theorem isRegularLocalRing_and_mapsRSOP_stalkMap_c (s : ℕ) (y : 𝒮.tHat.X s)
    (hy : (𝒮.tHat.pre s).composite.base y = hS.xh) :
    IsRegularLocalRing ((𝒮.tHat.X s).presheaf.stalk y) ∧
      RingHom.MapsRSOP ((𝒮.c s).stalkMap y).hom := by
  obtain ⟨h1, h2, -⟩ := 𝒮.toCompletion.isRegularLocalRing_and_mapsRSOP_stalkMap
    (hS.ambient.2.1 x₀) hS.isNonsingular_X hS.isNonsingular_B s y hy
  exact ⟨h1, h2⟩

/-- Every point of `X̂_s` specializes to a point over `x̂_0`. -/
theorem exists_specializes_over [Hironaka.HironakaCitedResults.{u}] (s : ℕ) (y : 𝒮.tHat.X s) :
    ∃ y', y ⤳ y' ∧ (𝒮.tHat.pre s).composite.base y' = hS.xh :=
  𝒮.toCompletion.exists_specializes_xhat0 (hS.ambient.2.1 x₀) s y

/-- The schemes `X̂_s` are non-singular. -/
theorem isNonsingular_tHat_X [Hironaka.HironakaCitedResults.{u}] (s : ℕ) : (𝒮.tHat.X s).IsNonsingular :=
  𝒮.toCompletion.isNonsingular_tHat (hS.ambient.2.1 x₀) hS.isNonsingular_X hS.isNonsingular_B s

/-- `c_s⁻¹` of a non-singular subscheme is non-singular (the argument of `Completion.isNonsingular_B`,
for an arbitrary non-singular subscheme `D` of `X_s`). -/
theorem isNonsingular_totalTransform_c [Hironaka.HironakaCitedResults.{u}] (s : ℕ) {D : Subscheme (T.X s)} (hD : D.IsNonsingular) :
    (Subscheme.totalTransform (𝒮.c s) D).IsNonsingular := by
  intro z
  have := AB.isLocallyNoetherian_xHat0 (hS.ambient.2.1 x₀)
  have := MonoidalSuccession.isProper_composite (𝒮.tHat.pre s)
  obtain ⟨z', hsp, he⟩ := AB.exists_specializes_xhat0_of_universallyClosed (hS.ambient.2.1 x₀)
    ((Subscheme.totalTransform (𝒮.c s) D).ι ≫ (𝒮.tHat.pre s).composite) z
  suffices h : IsRegularLocalRing ((Subscheme.totalTransform (𝒮.c s) D).toScheme.presheaf.stalk z')
    from AB.isRegularLocalRing_stalk_of_specializes hsp
  set yh := (Subscheme.totalTransform (𝒮.c s) D).ι.base z'
  obtain ⟨hreg, hα⟩ := 𝒮.isRegularLocalRing_and_mapsRSOP_stalkMap_c s yh he
  have hyh : yh ∈ (Subscheme.totalTransform (𝒮.c s) D).pts := by
    show _ ∈ ((Subscheme.totalTransform (𝒮.c s) D).support : Set (𝒮.tHat.X s))
    rw [← Scheme.IdealSheafData.range_subschemeι]
    exact ⟨z', rfl⟩
  have hy : (𝒮.c s).base yh ∈ D.pts := by
    by_contra hy
    apply Subscheme.mem_pts_iff_stalkIdeal_ne_top.mp hyh
    rw [stalkIdeal_totalTransform, Subscheme.stalkIdeal_eq_top_of_notMem_pts hy, Ideal.map_top]
  have : IsRegularLocalRing ((T.X s).presheaf.stalk ((𝒮.c s).base yh)) := hS.isNonsingular_X s _
  have hQ := Subscheme.isPrime_stalkIdeal_of_isNonsingular hD hy
  have hQreg := Subscheme.isRegularLocalRing_quotient_of_isNonsingular hD hy
  have hq := (hα.isPrime_map_and_isRegularLocalRing_quotient hQ hQreg).2
  have hstalk : (Subscheme.totalTransform (𝒮.c s) D).stalkIdeal yh =
      (D.stalkIdeal ((𝒮.c s).base yh)).map ((𝒮.c s).stalkMap yh).hom := by
    rw [stalkIdeal_totalTransform]
  obtain ⟨e⟩ := nonempty_stalk_quot_equiv (Subscheme.totalTransform (𝒮.c s) D) z'
  rw [← hstalk] at hq
  exact IsRegularLocalRing.of_ringEquiv e

/-- `c_s⁻¹` of a divisor given locally by a member of a regular system of parameters is simple
and of codimension one at each of its points. -/
theorem isSimpleAt_and_codimAt_eq_one_totalTransform_c [Hironaka.HironakaCitedResults.{u}] (s : ℕ) {D : Subscheme (T.X s)}
    (hD : D.IsNonsingular)
    (hP : ∀ x, D.stalkIdeal x = ⊤ ∨ ∃ a, ExtendsToRSOP _ {a} ∧ D.stalkIdeal x = Ideal.span {a}) :
    ∀ y ∈ (Subscheme.totalTransform (𝒮.c s) D).pts,
      (Subscheme.totalTransform (𝒮.c s) D).IsSimpleAt y ∧
        (Subscheme.totalTransform (𝒮.c s) D).codimAt y = 1 := by
  classical
  intro y hy
  have hns := 𝒮.isNonsingular_totalTransform_c s hD
  have hsimple : (Subscheme.totalTransform (𝒮.c s) D).IsSimpleAt y :=
    ⟨hy, Subscheme.isRegularLocalRing_quotient_of_isNonsingular hns hy⟩
  refine ⟨hsimple, ?_⟩
  obtain ⟨y', hsp, he⟩ := 𝒮.exists_specializes_over s y
  have hy' : y' ∈ (Subscheme.totalTransform (𝒮.c s) D).pts :=
    hsp.mem_closed (Subscheme.totalTransform (𝒮.c s) D).support.isClosed hy
  obtain ⟨hreg, hα⟩ := 𝒮.isRegularLocalRing_and_mapsRSOP_stalkMap_c s y' he
  have hx : (𝒮.c s).base y' ∈ D.pts := by
    by_contra hx
    apply Subscheme.mem_pts_iff_stalkIdeal_ne_top.mp hy'
    rw [stalkIdeal_totalTransform, Subscheme.stalkIdeal_eq_top_of_notMem_pts hx, Ideal.map_top]
  have : IsRegularLocalRing ((T.X s).presheaf.stalk ((𝒮.c s).base y')) := hS.isNonsingular_X s _
  obtain ⟨a, ha, hDa⟩ := (hP _).resolve_left (Subscheme.mem_pts_iff_stalkIdeal_ne_top.mp hx)
  obtain ⟨Z, haZ, hZ⟩ := ha
  have hZ' := (hα.isRegularSystemOfParameters_image hZ).1
  have haZ' : ({((𝒮.c s).stalkMap y').hom a} : Finset _) ⊆ Z.image ((𝒮.c s).stalkMap y').hom := by
    intro b hb
    rw [Finset.mem_singleton] at hb
    subst hb
    exact Finset.mem_image_of_mem _ (haZ (Finset.mem_singleton_self a))
  have hst : (Subscheme.totalTransform (𝒮.c s) D).stalkIdeal y' =
      Ideal.span {((𝒮.c s).stalkMap y').hom a} := by
    rw [stalkIdeal_totalTransform, hDa, Ideal.map_span, Set.image_singleton]
  have : IsRegularLocalRing ((𝒮.tHat.X s).presheaf.stalk y) := 𝒮.isNonsingular_tHat_X s y
  have hprime : ((Subscheme.totalTransform (𝒮.c s) D).stalkIdeal y).IsPrime :=
    Subscheme.isPrime_stalkIdeal_of_isNonsingular hns hy
  exact Subscheme.codimAt_eq_one_of_specializes hsp ⟨_, haZ', hZ'⟩ hst hprime

/-- `Ê_j(s+1) = (Ê_j(s))'` for `j < α + s`: strict transforms commute with the flat base change
`c_{s+1}`. -/
theorem eHat_succ_of_lt (s j : ℕ) (hj : j < ℜ.α + s) :
    𝒮.eHat (s + 1) ⟨j, by omega⟩ =
      Subscheme.strictTransform (𝒮.tHat.monoidalTransformation s) (𝒮.eHat s ⟨j, hj⟩) := by
  have : Flat (show (𝒮.tHat.monoidalTransformation s).X' ⟶ (T.monoidalTransformation s).X' from
      𝒮.c (s + 1)) := flat_c_of_completion 𝒮.toCompletion (hS.ambient.2.1 x₀) (s + 1)
  have key := MonoidalTransformation.totalTransform_strictTransform_of_flat_square
    (T.monoidalTransformation s) (𝒮.tHat.monoidalTransformation s) (𝒮.c s) (𝒮.c (s + 1))
    (𝒮.c_comm s).symm (𝒮.B_hat s).symm (eSeq T ℜ s ⟨j, hj⟩)
  have e := eSeq_succ_of_lt T ℜ s j hj
  simp only [eHat]
  rw [e]
  exact key

/-- `Ê_{α+s+1}(s+1)` is the exceptional divisor of `f̂_s`. -/
theorem eHat_succ_last (s : ℕ) :
    𝒮.eHat (s + 1) ⟨ℜ.α + s, by omega⟩ = (𝒮.tHat.monoidalTransformation s).exceptional := by
  unfold eHat
  rw [eSeq_succ_last T ℜ s]
  exact MonoidalTransformation.totalTransform_exceptional_of_square (T.monoidalTransformation s)
    (𝒮.tHat.monoidalTransformation s) (𝒮.c s) (𝒮.c (s + 1)) (𝒮.c_comm s).symm (𝒮.B_hat s).symm

/-- The boundary `E` of the datum of type I on `X̂_0` used for the induction of p. 321:
`E = ⋃_{i ≤ α} Ê_i(0)` in the closed case, empty without restriction. -/
noncomputable def modelDatum : DatumI.Raw (AB.xHat0 X x₀) where
  E := match r with
    | .closed _ => ⨅ j : Fin (ℜ.α + 0), 𝒮.eHat 0 j
    | .unrestricted => Subscheme.empty
  β := 0
  V := Fin.elim0
  W := AB.vZ X x₀ 𝒮.z

theorem transformI_modelDatum_W (s : ℕ) :
    ((𝒮.tHat.pre s).transformI 𝒮.modelDatum).W = 𝒮.xBar s := by
  rw [MonoidalSuccession.transformI_W]
  induction s with
  | zero => rfl
  | succ s ih =>
    show (MonoidalSuccession.snoc (𝒮.tHat.pre s) (𝒮.tHat.B s)
      (𝒮.tHat.monoidalTransformation s)).strictTransform _ = _
    rw [MonoidalSuccession.strictTransform_snoc, ih]
    rfl

/-- The points of the boundary of the transformed datum of type I on `X̂_s` are those of
`⋃ Ê_j(s)` over the boundary indices (p. 321). -/
theorem pts_transformI_modelDatum_E (s : ℕ) :
    ((𝒮.tHat.pre s).transformI 𝒮.modelDatum).E.pts =
      ⋃ j ∈ {j : Fin (ℜ.α + s) | inBoundary r ℜ.α s j}, (𝒮.eHat s j).pts := by
  induction s with
  | zero =>
    cases r with
    | closed F =>
      show (⨅ j : Fin (ℜ.α + 0), 𝒮.eHat 0 j).pts = _
      rw [Subscheme.pts_iInf]
      simp [inBoundary]
    | unrestricted =>
      show (Subscheme.empty : Subscheme (𝒮.tHat.X 0)).pts = _
      rw [Subscheme.pts_empty]
      refine (Set.empty_subset _).antisymm ?_
      intro x hx
      obtain ⟨j, hj, -⟩ := Set.mem_iUnion₂.mp hx
      have h1 : ℜ.α ≤ j.val := hj
      have := j.2
      omega
  | succ s ih =>
    show ((MonoidalSuccession.snoc (𝒮.tHat.pre s) (𝒮.tHat.B s)
      (𝒮.tHat.monoidalTransformation s)).transformI 𝒮.modelDatum).E.pts = _
    rw [MonoidalSuccession.transformI_snoc]
    set t := 𝒮.tHat.monoidalTransformation s
    show (Subscheme.strictTransform t _ ⊓ t.exceptional).pts = _
    rw [Subscheme.pts_inf, MonoidalTransformation.pts_strictTransform_eq_closure, ih]
    have hfin : ({j : Fin (ℜ.α + s) | inBoundary r ℜ.α s j}).Finite := Set.toFinite _
    have hpre : t.f.base ⁻¹' (⋃ j ∈ {j : Fin (ℜ.α + s) | inBoundary r ℜ.α s j}, (𝒮.eHat s j).pts) \
        t.exceptional.pts = ⋃ j ∈ {j : Fin (ℜ.α + s) | inBoundary r ℜ.α s j},
          (t.f.base ⁻¹' (𝒮.eHat s j).pts \ t.exceptional.pts) := by
      ext x
      simp only [Set.mem_sdiff, Set.mem_preimage, Set.mem_iUnion, exists_prop]
      tauto
    rw [hpre, hfin.closure_biUnion]
    refine Set.Subset.antisymm ?_ ?_
    · rintro x (hx | hx)
      · obtain ⟨j, hj, hx⟩ := Set.mem_iUnion₂.mp hx
        refine Set.mem_iUnion₂.mpr ⟨⟨j.val, by omega⟩,
          (inBoundary_succ r ℜ.α s _).mpr (Or.inr ⟨j.2, hj⟩), ?_⟩
        rw [𝒮.eHat_succ_of_lt s j.val j.2]
        exact (Set.ext_iff.mp (MonoidalTransformation.pts_strictTransform_eq_closure t _) x).mpr hx
      · refine Set.mem_iUnion₂.mpr ⟨⟨ℜ.α + s, by omega⟩,
          (inBoundary_succ r ℜ.α s _).mpr (Or.inl rfl), ?_⟩
        rw [𝒮.eHat_succ_last s]
        exact hx
    · intro x hx
      obtain ⟨j, hj, hx⟩ := Set.mem_iUnion₂.mp hx
      rcases (inBoundary_succ r ℜ.α s j).mp hj with h | ⟨h, hj'⟩
      · right
        have : j = ⟨ℜ.α + s, by omega⟩ := Fin.ext h
        rw [this, 𝒮.eHat_succ_last s] at hx
        exact hx
      · left
        refine Set.mem_iUnion₂.mpr ⟨⟨j.val, h⟩, hj', ?_⟩
        have e : j = ⟨j.val, by omega⟩ := rfl
        rw [e, 𝒮.eHat_succ_of_lt s j.val h] at hx
        exact (Set.ext_iff.mp (MonoidalTransformation.pts_strictTransform_eq_closure t _) x).mp hx

/-- Normal crossings can be tested at the points over `x̂_0`: every point of `X̂_s` is a
generization of such a point, and the property is open (`exists_isOpen_hasOnlyNormalCrossingsWithAt`). -/
theorem hasOnlyNormalCrossingsWithAt_of_over [Hironaka.HironakaCitedResults.{u}] (s : ℕ) {E D : Subscheme (𝒮.tHat.X s)}
    (h : ∀ y ∈ D.pts, (𝒮.tHat.pre s).composite.base y = hS.xh →
      E.HasOnlyNormalCrossingsWithAt D y) :
    ∀ y ∈ D.pts, E.HasOnlyNormalCrossingsWithAt D y := by
  intro y hy
  obtain ⟨y', hsp, he⟩ := 𝒮.exists_specializes_over s y
  have hy' : y' ∈ D.pts := hsp.mem_closed D.support.isClosed hy
  have := 𝒮.isAlgebraicScheme_tHat_X s
  obtain ⟨U, hU, hy'U, hUall⟩ := Subscheme.exists_isOpen_hasOnlyNormalCrossingsWithAt
    (𝒮.isNonsingular_tHat_X s) E D y' (h y' hy' he)
  exact hUall y ⟨hsp.mem_open hU hy'U, hy⟩

theorem isIrreducible_pts_vZ [Hironaka.HironakaCitedResults.{u}] : _root_.IsIrreducible (AB.vZ X x₀ 𝒮.z).pts :=
  isIrreducible_pts (𝒮.xBar 0) 𝒮.xBar_zero_facts.2.1

theorem isReduced_vZ [Hironaka.HironakaCitedResults.{u}] : (AB.vZ X x₀ 𝒮.z).IsReduced :=
  DatumTransform.isReduced_of_isNonsingular 𝒮.xBar_zero_facts.1

theorem c_zero_base_xh : (𝒮.c 0).base hS.xh = x₀ := by
  rw [𝒮.c_zero]; exact c0_xhat0 x₀ (hS.ambient.2.1 x₀)

/-- Without restriction the boundary of the model datum is empty. -/
theorem modelDatum_E_unrestricted (hr : r = .unrestricted) :
    𝒮.modelDatum.E = Subscheme.empty := by
  subst hr; rfl

theorem modelDatum_E_closed {F : Subscheme X} (hr : r = .closed F) :
    𝒮.modelDatum.E = ⨅ j : Fin (ℜ.α + 0), 𝒮.eHat 0 j := by
  subst hr; rfl

/-- Stage `0`, unrestricted case: the boundary has stalk presentations (it is empty). -/
theorem exists_stalk_presentation_modelDatum_unrestricted [Hironaka.HironakaCitedResults.{u}] (hr : r = .unrestricted)
    (y : 𝒮.tHat.X 0) :
    ∃ K : Finset ((𝒮.tHat.X 0).presheaf.stalk y), ExtendsToRSOP _ K ∧
      𝒮.modelDatum.E.stalkIdeal y = Ideal.span {∏ k ∈ K, k} := by
  have : IsRegularLocalRing ((𝒮.tHat.X 0).presheaf.stalk y) := 𝒮.isNonsingular_tHat_X 0 y
  obtain ⟨-, Z, hZ⟩ := (isRegularLocalRing_iff_exists_rsop ((𝒮.tHat.X 0).presheaf.stalk y)).mp
    inferInstance
  refine ⟨∅, ⟨Z, Finset.empty_subset _, hZ⟩, ?_⟩
  rw [𝒮.modelDatum_E_unrestricted hr]
  show (⊤ : Subscheme (𝒮.tHat.X 0)).stalkIdeal y = _
  rw [Subscheme.stalkIdeal_top_eq, Finset.prod_empty, Ideal.span_singleton_one]

/-- `E_0 = ⋃ Ê_j(0)` is reduced and its pull-back facts at `x̂_0`: the union `⋃_{j<α} Ê_j(0)`
has only normal crossings with `c_0⁻¹(D)` at `x̂_0` as soon as `⋃ E_j` has with `D` at `x_0`. -/
theorem hasOnlyNormalCrossingsWithAt_iInf_eHat_zero [Hironaka.HironakaCitedResults.{u}] (D : Subscheme X)
    (h : (⨅ j : Fin (ℜ.α + 0), eSeq T ℜ 0 j).HasOnlyNormalCrossingsWithAt D x₀) :
    (⨅ j : Fin (ℜ.α + 0), 𝒮.eHat 0 j).HasOnlyNormalCrossingsWithAt
      (Subscheme.totalTransform (𝒮.c 0) D) hS.xh := by
  let xh : 𝒮.tHat.X 0 := hS.xh
  obtain ⟨hreg, hα⟩ := 𝒮.isRegularLocalRing_and_mapsRSOP_stalkMap_c 0 xh rfl
  have hx : (𝒮.c 0).base xh = x₀ := 𝒮.c_zero_base_xh
  have hEred : (⨅ j : Fin (ℜ.α + 0), eSeq T ℜ 0 j).IsReduced :=
    Subscheme.isReduced_iInf_of_isNonsingular _ fun j => hS.isNonsingular_eSeq 0 j
  have : IsRegularLocalRing ((T.X 0).presheaf.stalk ((𝒮.c 0).base xh)) :=
    hS.isNonsingular_X 0 _
  have h' : (⨅ j : Fin (ℜ.α + 0), eSeq T ℜ 0 j).HasOnlyNormalCrossingsWithAt D
      ((𝒮.c 0).base xh) := by rw [hx]; exact h
  have hloc : IsLocalHom ((𝒮.c 0).stalkMap xh).hom := inferInstance
  have key := Subscheme.hasOnlyNormalCrossingsWithAt_totalTransform_of_mapsRSOP (𝒮.c 0) xh hα
    hEred h'
  refine (Hironaka.Subscheme.hasOnlyNormalCrossingsWithAt_congr ?_ _ _).mp key
  rw [Subscheme.pts_totalTransform_eq_preimage, Subscheme.pts_iInf, Subscheme.pts_iInf]
  ext y
  simp only [Set.mem_preimage, Set.mem_iUnion, eHat]
  simp only [Subscheme.pts_totalTransform_eq_preimage, Set.mem_preimage]

theorem exists_stalk_presentation_modelDatum_closed [Hironaka.HironakaCitedResults.{u}] {F : Subscheme X} (hr : r = .closed F)
    (y : 𝒮.tHat.X 0) :
    ∃ K : Finset ((𝒮.tHat.X 0).presheaf.stalk y), ExtendsToRSOP _ K ∧
      𝒮.modelDatum.E.stalkIdeal y = Ideal.span {∏ k ∈ K, k} := by
  have : IsRegularLocalRing ((𝒮.tHat.X 0).presheaf.stalk y) := 𝒮.isNonsingular_tHat_X 0 y
  rw [𝒮.modelDatum_E_closed hr]
  have hUred : (⨅ j : Fin (ℜ.α + 0), 𝒮.eHat 0 j).IsReduced :=
    Subscheme.isReduced_iInf_of_isNonsingular _ fun j =>
      𝒮.isNonsingular_totalTransform_c 0 (hS.isNonsingular_eSeq 0 j)
  have h0 : (⨅ j : Fin (ℜ.α + 0), eSeq T ℜ 0 j).HasOnlyNormalCrossingsWithAt ⊥ x₀ := by
    rw [← eUnion_datum_eq]; exact (hS.isDatum_datum 0).2.2.1 x₀
  have hx := 𝒮.hasOnlyNormalCrossingsWithAt_iInf_eHat_zero ⊥ h0
  have hx' : (⨅ j : Fin (ℜ.α + 0), 𝒮.eHat 0 j).HasOnlyNormalCrossingsWithAt ⊥ hS.xh :=
    Hironaka.Subscheme.hasOnlyNormalCrossingsWithAt_congr_right hx
      (Subscheme.stalkIdeal_totalTransform_bot _ _)
  have hall := 𝒮.hasOnlyNormalCrossingsWithAt_of_over 0
    (E := ⨅ j : Fin (ℜ.α + 0), 𝒮.eHat 0 j) (D := ⊥) (fun y' _ hy' => by
      have : y' = hS.xh := hy'
      rw [this]; exact hx') y (Subscheme.mem_pts_bot y)
  obtain ⟨z, hz, ⟨J, hJz, hEJ⟩, -⟩ :=
    (Hironaka.Subscheme.hasOnlyNormalCrossingsWithAt_iff hUred this).mp hall
  exact ⟨J, (ExtendsToRSOP.of_isRegularSystemOfParameters hz).mono hJz, hEJ⟩

theorem vZ_eq_totalTransform_c_zero {F : Subscheme X} (hr : r = .closed F) :
    AB.vZ X x₀ 𝒮.z = Subscheme.totalTransform (𝒮.c 0) F := by
  subst hr
  obtain ⟨Fr, h1, hz, hFz, -⟩ := 𝒮.frame
  obtain ⟨z₀, hz₀, hFz₀⟩ := hFz F rfl
  rw [𝒮.c_zero, ← hz₀]
  exact vZ_eq_totalTransform_c0 F z₀ hFz₀

theorem modelDatum_hres_unrestricted [Hironaka.HironakaCitedResults.{u}] (hr : r = .unrestricted) :
    ∀ x ∈ 𝒮.modelDatum.W.pts, 𝒮.modelDatum.E.HasOnlyNormalCrossingsWithAt 𝒮.modelDatum.W x := by
  intro x hx
  rw [𝒮.modelDatum_E_unrestricted hr]
  exact Subscheme.hasOnlyNormalCrossingsWithAt_empty (𝒮.isNonsingular_tHat_X 0 x)
    ⟨hx, Subscheme.isRegularLocalRing_quotient_of_isNonsingular 𝒮.xBar_zero_facts.1 hx⟩

theorem modelDatum_hres_closed [Hironaka.HironakaCitedResults.{u}] {F : Subscheme X} (hr : r = .closed F) :
    ∀ x ∈ 𝒮.modelDatum.W.pts, 𝒮.modelDatum.E.HasOnlyNormalCrossingsWithAt 𝒮.modelDatum.W x := by
  have hcr : ℜ.IsClosedRestriction F := by have := hS.isFor; subst hr; exact this
  have hNCF := DatumII.Raw.hasOnlyNormalCrossingsWith_eUnion_of_isClosedRestriction
    (hS.ambient.2.1) hS.isDatum hcr x₀ (hS.mem_pts_closed_x₀ hr)
  have h0 : (⨅ j : Fin (ℜ.α + 0), eSeq T ℜ 0 j).HasOnlyNormalCrossingsWithAt F x₀ := by
    rw [← eUnion_datum_eq]; exact hNCF
  have hx := 𝒮.hasOnlyNormalCrossingsWithAt_iInf_eHat_zero F h0
  have hv := 𝒮.vZ_eq_totalTransform_c_zero hr
  have hx' : (⨅ j : Fin (ℜ.α + 0), 𝒮.eHat 0 j).HasOnlyNormalCrossingsWithAt
      (AB.vZ X x₀ 𝒮.z) hS.xh := by
    refine Hironaka.Subscheme.hasOnlyNormalCrossingsWithAt_congr_right hx ?_
    rw [hv]
  rw [𝒮.modelDatum_E_closed hr]
  exact 𝒮.hasOnlyNormalCrossingsWithAt_of_over 0 (fun y' _ hy' => by
      have : y' = hS.xh := hy'
      rw [this]; exact hx')

theorem not_subset_modelDatum_E_closed [Hironaka.HironakaCitedResults.{u}] {F : Subscheme X} (hr : r = .closed F)
    (hFE : ∀ i : Fin ℜ.α, ¬ F.pts ⊆ (ℜ.E i).pts) :
    ¬ 𝒮.modelDatum.W.pts ⊆ 𝒮.modelDatum.E.pts := by
  intro hsub
  rw [𝒮.modelDatum_E_closed hr] at hsub
  replace hsub := hsub.trans (Subscheme.pts_iInf (Z := 𝒮.tHat.X 0)
    (fun j : Fin (ℜ.α + 0) => 𝒮.eHat 0 j)).le
  have hirr := 𝒮.isIrreducible_pts_vZ
  have hcl : IsClosed (AB.vZ X x₀ 𝒮.z).pts := (AB.vZ X x₀ 𝒮.z).support.isClosed
  have hη : closure {hirr.genericPoint} = (AB.vZ X x₀ 𝒮.z).pts := hirr.closure_genericPoint hcl
  have hηW : hirr.genericPoint ∈ (AB.vZ X x₀ 𝒮.z).pts := hη.le (subset_closure rfl)
  obtain ⟨j, hj⟩ := Set.mem_iUnion.mp (hsub hηW)
  have hsubj : (AB.vZ X x₀ 𝒮.z).pts ⊆ (𝒮.eHat 0 j).pts := by
    rw [← hη]
    exact closure_minimal (Set.singleton_subset_iff.mpr hj) (𝒮.eHat 0 j).support.isClosed
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
  exact Subscheme.not_stalkIdeal_le_of_isIrreducible_not_subset hFirr
    (hFE (Fin.cast (by simp) j)) (le_rfl : (eSeq T ℜ 0 j).pts ⊆ (eSeq T ℜ 0 j).pts) (by
      rw [𝒮.c_zero_base_xh]; exact hFx) hle'

/-- `E_{α+1}(t) ∪ ⋯ ∪ E_{α+t}(t)` (resp. all of `E_1(t) ∪ ⋯ ∪ E_{α+t}(t)`) pulled back by `c_t` has
only normal crossings with `B̂_t = c_t⁻¹(B_t)`: sub-unions keep normal crossings, then the pull-back
by `c_t` (Lemma (AB.2)/(CD.3)) at the points over `x̂_0`, and openness elsewhere. -/
theorem hasOnlyNormalCrossingsWith_boundary_bHat [Hironaka.HironakaCitedResults.{u}] (t : ℕ) :
    (⨅ i : Fin (alphaT r ℜ.α t), 𝒮.eHat t (idxT ℜ.α t r i)).HasOnlyNormalCrossingsWith
      (𝒮.tHat.B t) := by
  refine 𝒮.hasOnlyNormalCrossingsWithAt_of_over t fun y hy hover => ?_
  obtain ⟨hreg, hα⟩ := 𝒮.isRegularLocalRing_and_mapsRSOP_stalkMap_c t y hover
  have hxB : (𝒮.c t).base y ∈ (T.B t).pts := by
    have hy' : y ∈ (Subscheme.totalTransform (𝒮.c t) (T.B t)).pts := by
      rw [← 𝒮.B_hat t]; exact hy
    rwa [Subscheme.pts_totalTransform_eq_preimage] at hy'
  have : IsRegularLocalRing ((T.X t).presheaf.stalk ((𝒮.c t).base y)) := hS.isNonsingular_X t _
  have hperm := (hS.isPermissible_B t).2.2 _ hxB
  rw [eUnion_datum_eq] at hperm
  have hfull : (⨅ j : Fin (ℜ.α + t), eSeq T ℜ t j).IsReduced :=
    Subscheme.isReduced_iInf_of_isNonsingular _ fun j => hS.isNonsingular_eSeq t j
  have hsub := Subscheme.hasOnlyNormalCrossingsWithAt_iInf_comp (idxT ℜ.α t r)
    (E := eSeq T ℜ t) hfull hperm (fun j hj => hS.exists_isSimpleAt_codimAt_eSeq t j _ hj)
  have hsubred : (⨅ i : Fin (alphaT r ℜ.α t), eSeq T ℜ t (idxT ℜ.α t r i)).IsReduced :=
    Subscheme.isReduced_iInf_of_isNonsingular _ fun i => hS.isNonsingular_eSeq t _
  have hloc : IsLocalHom ((𝒮.c t).stalkMap y).hom := inferInstance
  have key := Subscheme.hasOnlyNormalCrossingsWithAt_totalTransform_of_mapsRSOP (𝒮.c t) y hα
    hsubred hsub
  rw [← 𝒮.B_hat t] at key
  refine (Hironaka.Subscheme.hasOnlyNormalCrossingsWithAt_congr ?_ _ _).mp key
  rw [Subscheme.pts_totalTransform_eq_preimage, Subscheme.pts_iInf, Subscheme.pts_iInf]
  ext z
  simp only [Set.mem_preimage, Set.mem_iUnion, eHat]
  simp only [Subscheme.pts_totalTransform_eq_preimage, Set.mem_preimage]

/-- Hypothesis (c) of the induction along `ĝ_s`: the boundary of the model datum at stage `t` has only
normal crossings with `B̂_t`. -/
theorem hasOnlyNormalCrossingsWith_modelDatum_boundary_bHat [Hironaka.HironakaCitedResults.{u}] (t : ℕ) :
    ((𝒮.tHat.pre t).transformI 𝒮.modelDatum).E.HasOnlyNormalCrossingsWith (𝒮.tHat.B t) := by
  intro x hx
  refine (Hironaka.Subscheme.hasOnlyNormalCrossingsWithAt_congr ?_ _ _).mpr
    (𝒮.hasOnlyNormalCrossingsWith_boundary_bHat t x hx)
  rw [pts_transformI_modelDatum_E, Subscheme.pts_iInf]
  rw [← pts_iInf_idxT (Z := 𝒮.tHat.X t) r ℜ.α t (𝒮.eHat t), Subscheme.pts_iInf]

/-- Induction hypotheses (a)–(d) of the stalkwise theorem for the model datum along `ĝ_s`. -/
theorem centersAdaptedNonsingular_pre [Hironaka.HironakaCitedResults.{u}] (s : ℕ) (hc : ∀ t, t < s → 𝒮.IsCenterContained t)
    (hirr : ∀ t, t ≤ s → (𝒮.xBar t).IsIrreducible) :
    (𝒮.tHat.pre s).CentersAdaptedNonsingular 𝒮.modelDatum := by
  induction s with
  | zero => trivial
  | succ s ih =>
    show (MonoidalSuccession.snoc (𝒮.tHat.pre s) (𝒮.tHat.B s)
      (𝒮.tHat.monoidalTransformation s)).CentersAdaptedNonsingular _
    rw [MonoidalSuccession.centersAdaptedNonsingular_snoc]
    refine ⟨ih (fun t ht => hc t (by omega)) (fun t ht => hirr t (by omega)), ?_, ?_, ?_, ?_⟩
    · exact 𝒮.toCompletion.isNonsingular_B (hS.ambient.2.1 x₀) hS.isNonsingular_X
        hS.isNonsingular_B s
    · rw [𝒮.transformI_modelDatum_W]; exact hc s (by omega)
    · exact 𝒮.hasOnlyNormalCrossingsWith_modelDatum_boundary_bHat s
    · rw [𝒮.transformI_modelDatum_W]
      intro hsub
      have h1 := pts_strictTransform_eq_empty_of_subset (𝒮.tHat.monoidalTransformation s)
        (𝒮.xBar s) hsub
      exact (pts_nonempty_of_isIrreducible _ (hirr (s + 1) le_rfl)).ne_empty h1

/-- **The induction of p. 321 on `X̂_s`.**  For the datum `(E; ; V(z))` of type I on `X̂_0` (with
`E = ⋃_{i ≤ α} Ê_i(0)` in the closed case, `E = ∅` otherwise), whose successive centers are the
`B̂_t ⊆ X̄_t`: the boundary `E_s` of the transform along `ĝ_s` has stalk presentations (is reduced,
of codimension one, with only normal crossings), has only normal crossings with `X̄_s`, and
`X̄_s` is irreducible and not contained in `E_s`. -/
theorem modelDatum_main [Hironaka.HironakaCitedResults.{u}] (s : ℕ) (hadm : 𝒮.IsAdmissibleAt s)
    (hFE : ∀ F, r = .closed F → ∀ i : Fin ℜ.α, ¬ F.pts ⊆ (ℜ.E i).pts) :
    (∀ y : 𝒮.tHat.X s, ∃ K : Finset ((𝒮.tHat.X s).presheaf.stalk y), ExtendsToRSOP _ K ∧
      ((𝒮.tHat.pre s).transformI 𝒮.modelDatum).E.stalkIdeal y = Ideal.span {∏ k ∈ K, k}) ∧
    (∀ y ∈ (𝒮.xBar s).pts, ((𝒮.tHat.pre s).transformI 𝒮.modelDatum).E.HasOnlyNormalCrossingsWithAt
      (𝒮.xBar s) y) ∧
    _root_.IsIrreducible (𝒮.xBar s).pts ∧
    ¬ (𝒮.xBar s).pts ⊆ ((𝒮.tHat.pre s).transformI 𝒮.modelDatum).E.pts := by
  have hc : ∀ t, t < s → 𝒮.IsCenterContained t := fun t ht => (hadm.2.2.1 t ht).2.1
  have hirr : ∀ t, t ≤ s → (𝒮.xBar t).IsIrreducible := by
    intro t ht
    rcases ht.lt_or_eq with h | rfl
    · exact (hadm.2.2.1 t h).1.2
    · exact hadm.1.2
  have hCAN := 𝒮.centersAdaptedNonsingular_pre s hc hirr
  have hE0 : ∀ y : (AB.xHat0 X x₀), ∃ K : Finset ((AB.xHat0 X x₀).presheaf.stalk y),
      ExtendsToRSOP _ K ∧ 𝒮.modelDatum.E.stalkIdeal y = Ideal.span {∏ k ∈ K, k} := by
    intro y
    cases r with
    | closed F => exact 𝒮.exists_stalk_presentation_modelDatum_closed rfl y
    | unrestricted => exact 𝒮.exists_stalk_presentation_modelDatum_unrestricted rfl y
  have hres : ∀ x ∈ 𝒮.modelDatum.W.pts,
      𝒮.modelDatum.E.HasOnlyNormalCrossingsWithAt 𝒮.modelDatum.W x := by
    cases r with
    | closed F => exact 𝒮.modelDatum_hres_closed rfl
    | unrestricted => exact 𝒮.modelDatum_hres_unrestricted rfl
  have hWE : ¬ 𝒮.modelDatum.W.pts ⊆ 𝒮.modelDatum.E.pts := by
    cases r with
    | closed F => exact 𝒮.not_subset_modelDatum_E_closed rfl (hFE F rfl)
    | unrestricted =>
      rw [𝒮.modelDatum_E_unrestricted rfl, Subscheme.pts_empty]
      intro h
      obtain ⟨x, hx⟩ := 𝒮.isIrreducible_pts_vZ.nonempty
      exact h hx
  obtain ⟨-, -, hE, hNC, -, hi, he⟩ :=
    MonoidalSuccession.isNonsingular_and_hasOnlyNormalCrossingsWith_and_not_stalkIdeal_le_of_centersAdaptedNonsingular
      (𝒮.tHat.pre s) (ℜ := 𝒮.modelDatum) (𝒮.isNonsingular_tHat_X 0) hE0 hres
      𝒮.isIrreducible_pts_vZ hWE hCAN
  rw [𝒮.transformI_modelDatum_W] at hNC hi he
  exact ⟨hE, hNC, hi, he⟩

/-- Core of `modelDatum_main` (no hypothesis on `F ≠ E_i`): the boundary of the transform of the model
datum along `ĝ_s` has stalk presentations and only normal crossings with `X̄_s`. -/
theorem modelDatum_core [Hironaka.HironakaCitedResults.{u}] (s : ℕ) (hadm : 𝒮.IsAdmissibleAt s) :
    (∀ y : 𝒮.tHat.X s, ∃ K : Finset ((𝒮.tHat.X s).presheaf.stalk y), ExtendsToRSOP _ K ∧
      ((𝒮.tHat.pre s).transformI 𝒮.modelDatum).E.stalkIdeal y = Ideal.span {∏ k ∈ K, k}) ∧
    (∀ y ∈ (𝒮.xBar s).pts, ((𝒮.tHat.pre s).transformI 𝒮.modelDatum).E.HasOnlyNormalCrossingsWithAt
      (𝒮.xBar s) y) := by
  have hc : ∀ t, t < s → 𝒮.IsCenterContained t := fun t ht => (hadm.2.2.1 t ht).2.1
  have hirr : ∀ t, t ≤ s → (𝒮.xBar t).IsIrreducible := by
    intro t ht
    rcases ht.lt_or_eq with h | rfl
    · exact (hadm.2.2.1 t h).1.2
    · exact hadm.1.2
  have hCAN := 𝒮.centersAdaptedNonsingular_pre s hc hirr
  have hE0 : ∀ y : (AB.xHat0 X x₀), ∃ K : Finset ((AB.xHat0 X x₀).presheaf.stalk y),
      ExtendsToRSOP _ K ∧ 𝒮.modelDatum.E.stalkIdeal y = Ideal.span {∏ k ∈ K, k} := by
    intro y
    cases r with
    | closed F => exact 𝒮.exists_stalk_presentation_modelDatum_closed rfl y
    | unrestricted => exact 𝒮.exists_stalk_presentation_modelDatum_unrestricted rfl y
  have hres : ∀ x ∈ 𝒮.modelDatum.W.pts,
      𝒮.modelDatum.E.HasOnlyNormalCrossingsWithAt 𝒮.modelDatum.W x := by
    cases r with
    | closed F => exact 𝒮.modelDatum_hres_closed rfl
    | unrestricted => exact 𝒮.modelDatum_hres_unrestricted rfl
  obtain ⟨-, -, hE, hNC⟩ :=
    MonoidalSuccession.hasOnlyNormalCrossingsWith_of_centersAdaptedNonsingular
      (𝒮.tHat.pre s) (ℜ := 𝒮.modelDatum) (𝒮.isNonsingular_tHat_X 0) hE0 hres hCAN
  rw [𝒮.transformI_modelDatum_W] at hNC
  exact ⟨hE, hNC⟩

theorem hasOnlyNormalCrossingsWith_xBar_boundary [Hironaka.HironakaCitedResults.{u}] (s : ℕ) (hadm : 𝒮.IsAdmissibleAt s) :
    (⨅ i : Fin (alphaT r ℜ.α s), 𝒮.eHat s (idxT ℜ.α s r i)).HasOnlyNormalCrossingsWith
      (𝒮.xBar s) := by
  intro y hy
  refine (Hironaka.Subscheme.hasOnlyNormalCrossingsWithAt_congr ?_ _ _).mp
    ((𝒮.modelDatum_core s hadm).2 y hy)
  rw [pts_transformI_modelDatum_E, Subscheme.pts_iInf, ← pts_iInf_idxT (Z := 𝒮.tHat.X s) r ℜ.α s
    (𝒮.eHat s), Subscheme.pts_iInf]

theorem inBoundary_idxT (r : Restriction X) (α s : ℕ) (i : Fin (alphaT r α s)) :
    inBoundary r α s (idxT α s r i) := by
  cases r with
  | closed F => trivial
  | unrestricted => exact Nat.le_add_right _ _

theorem isNonsingular_eHat [Hironaka.HironakaCitedResults.{u}] (s : ℕ) (j : Fin (ℜ.α + s)) : (𝒮.eHat s j).IsNonsingular :=
  𝒮.isNonsingular_totalTransform_c s (hS.isNonsingular_eSeq s j)

theorem isReduced_iInf_eHat [Hironaka.HironakaCitedResults.{u}] (s : ℕ) :
    (⨅ i : Fin (alphaT r ℜ.α s), 𝒮.eHat s (idxT ℜ.α s r i)).IsReduced :=
  Subscheme.isReduced_iInf_of_isNonsingular _ fun _i => 𝒮.isNonsingular_eHat s _

/-- The family `Ê_j(s)` is transversal to `X̄_s` (needs `F ⊄ E_i` in the closed case). -/
theorem isTransversalFamilyWith_eHat [Hironaka.HironakaCitedResults.{u}] (s : ℕ) (hadm : 𝒮.IsAdmissibleAt s)
    (hFE : ∀ F, r = .closed F → ∀ i : Fin ℜ.α, ¬ F.pts ⊆ (ℜ.E i).pts) :
    Subscheme.IsTransversalFamilyWith
      (fun i : Fin (alphaT r ℜ.α s) => 𝒮.eHat s (idxT ℜ.α s r i)) (𝒮.xBar s) := by
  obtain ⟨-, -, hirr, hWE⟩ := 𝒮.modelDatum_main s hadm hFE
  refine ⟨fun i x hx => 𝒮.isSimpleAt_and_codimAt_eq_one_totalTransform_c s
    (hS.isNonsingular_eSeq s (idxT ℜ.α s r i)) (hS.exists_stalkIdeal_eSeq s (idxT ℜ.α s r i)) x
    hx.1, fun i x hx => ?_⟩
  refine Subscheme.not_stalkIdeal_le_of_isIrreducible_not_subset (E :=
    ((𝒮.tHat.pre s).transformI 𝒮.modelDatum).E) hirr hWE ?_ hx.2
  intro z hz
  rw [pts_transformI_modelDatum_E]
  exact Set.mem_iUnion₂.mpr ⟨idxT ℜ.α s r i, inBoundary_idxT r ℜ.α s i, hz⟩

/-- p. 321: "For the case in which `ℜ = (ℜ^N_II, F)`, we see that `Ê_1(s) ∪ ⋯ ∪ Ê_{α+s}(s)` has only
normal crossings with `X̃` in `X̂_s`."

Deviation from the paper (gap filled): "we see" is not proved in the paper.  Proved here by the
induction of Lemma 4 of §2 along `ĝ_s` (`Frame.modelDatum_core`), applied to the datum
`(⋃_{i ≤ α} Ê_i(0); ; X̄_0)` of type I on `X̂_0`, whose successive centers are the non-singular
`B̂_t = c_t⁻¹(B_t) ⊆ X̄_t` (not necessarily irreducible; hence the version of `ExceptionalTransversal` for non-singular
centers): at stage `t` the boundary has only normal crossings with `B̂_t` since `E_1(t) ∪ ⋯ ∪ E_{α+t}(t)`
has with `B_t` (permissibility), and `c_t` carries regular systems of parameters to such systems at the
points over `x̂_0` (Lemma (CD.3)), the other points being generizations of those; the boundary of the
transform has the points of `Ê_1(s) ∪ ⋯ ∪ Ê_{α+s}(s)` (`c_s⁻¹` commutes with strict transforms,
`totalTransform_strictTransform_of_flat_square`). -/
theorem hasOnlyNormalCrossingsWith_xBar_of_closed [Hironaka.HironakaCitedResults.{u}] {s : ℕ} (hprep : PrepHyp N ℜ r ν T x₀ s)
    (F : Subscheme X) (hF : r = .closed F) :
    (⨅ j : Fin (ℜ.α + s), 𝒮.eHat s j).HasOnlyNormalCrossingsWith (𝒮.xBar s) := by
  have := 𝒮.hasOnlyNormalCrossingsWith_xBar_boundary s (𝒮.isAdmissibleAt_of_prepHyp hprep)
  subst hF
  exact this

/-- p. 321: "In the other case, we see that `Ê_{α+1}(s) ∪ ⋯ ∪ Ê_{α+s}(s)` has only normal
crossings with `X̃` in `X̂_s`."  Deviation from the paper (gap filled), as in
`hasOnlyNormalCrossingsWith_xBar_of_closed`: the datum on `X̂_0` has empty boundary, the boundary
of its transform along `ĝ_s` is `Ê_{α+1}(s) ∪ ⋯ ∪ Ê_{α+s}(s)`. -/
theorem hasOnlyNormalCrossingsWith_xBar_of_unrestricted [Hironaka.HironakaCitedResults.{u}] {s : ℕ}
    (hprep : PrepHyp N ℜ r ν T x₀ s) (hr : r = .unrestricted) :
    (⨅ j : Fin s, 𝒮.eHat s (Fin.natAdd ℜ.α j)).HasOnlyNormalCrossingsWith (𝒮.xBar s) := by
  have := 𝒮.hasOnlyNormalCrossingsWith_xBar_boundary s (𝒮.isAdmissibleAt_of_prepHyp hprep)
  subst hr
  exact this

/-- p. 321: "We see that, in both cases, `Ẽ_j` `(1 ≦ j ≦ α̃)` are non-singular irreducible
subschemes of `X̃` of codimension `1`."

Statement false as printed in two ways.  (a) The irreducibility is false (counterexample in the
docstring of `Frame.isNonsingular_xTilde_and_dim_xTilde_and_hasOnlyNormalCrossings_of_prepHyp`, blueprint
`lem:IV.4-tilde-facts`); the true part is stated: `Ẽ_j` is non-singular
and everywhere of codimension `1`.  (b) (`F = E_i`) In the closed case, if the restriction `F` is one
of the `E_i`, then `Ê_i(s) = c_s⁻¹(F(s)) = X̄_s`, so `Ẽ_i = X̃` has codimension `0` in `X̃`.  Counterexample
at `s = 0`: `X = 𝔸²`, `E_1 = F = V(x)`, `J = (y² + x³)`, `b = 2`, `a_1 = 0`, `x_0 = 0`; Definition 5
(II.1) (p. 166) only asks that `E_1 ∪ ⋯ ∪ E_α ∪ F` have only normal crossings.  The hypothesis
`hFE`, that `F` is none of the `E_i` (as sets of points), is added.

Deviation from the paper (gap filled): "we see" is proved: `Ê_j(s)` is non-singular of codimension one
(`c_s` carries a regular system of parameters to one, at the points over `x̂_0`; the other points are
generizations of those) and transversal to `X̄_s` (`X̄_s` is irreducible and not contained in the
boundary, `Subscheme.not_stalkIdeal_le_of_isIrreducible_not_subset`; this is where `hFE` is used), so
the restriction to `X̃` is non-singular of codimension one
(`isNonsingular_and_isEverywhereOfCodim_totalTransform_ι`). -/
theorem isNonsingular_and_isEverywhereOfCodim_eTilde [Hironaka.HironakaCitedResults.{u}] {s : ℕ}
    (hprep : PrepHyp N ℜ r ν T x₀ s)
    (hFE : ∀ F, r = .closed F → ∀ i : Fin ℜ.α, ¬ F.pts ⊆ (ℜ.E i).pts)
    (j : Fin (alphaT r ℜ.α s)) :
    (𝒮.eTilde s j).IsNonsingular ∧ (𝒮.eTilde s j).IsEverywhereOfCodim 1 := by
  have hadm := 𝒮.isAdmissibleAt_of_prepHyp hprep
  exact Subscheme.isNonsingular_and_isEverywhereOfCodim_totalTransform_ι
    (E := fun i : Fin (alphaT r ℜ.α s) => 𝒮.eHat s (idxT ℜ.α s r i)) (D := 𝒮.xBar s)
    (𝒮.isNonsingular_tHat_X s) (𝒮.isReduced_iInf_eHat s)
    (𝒮.hasOnlyNormalCrossingsWith_xBar_boundary s hadm)
    (𝒮.isTransversalFamilyWith_eHat s hadm hFE) j

/-- p. 321: "… and `Ẽ_1 ∪ ⋯ ∪ Ẽ_α̃` has only normal crossings on `X̃`."

Statement false as printed (`F = E_i`, closed case): then `Ẽ_i = X̃`, whose ideal is zero, so
`Ẽ_1 ∪ ⋯ ∪ Ẽ_α̃ = X̃` does not have only normal crossings (same counterexample as for
`isNonsingular_and_isEverywhereOfCodim_eTilde`: `s = 0`, `X = 𝔸²`, `E_1 = F = V(x)`, `J = (y² + x³)`,
`b = 2`).  The hypothesis `hFE` is added.

Deviation from the paper (gap filled): proved from the normal crossings of `⋃ Ê_j(s)` with `X̄_s` and
the transversality (`hasOnlyNormalCrossings_iInf_totalTransform_ι`). -/
theorem hasOnlyNormalCrossings_iInf_eTilde [Hironaka.HironakaCitedResults.{u}] {s : ℕ}
    (hprep : PrepHyp N ℜ r ν T x₀ s)
    (hFE : ∀ F, r = .closed F → ∀ i : Fin ℜ.α, ¬ F.pts ⊆ (ℜ.E i).pts) :
    (⨅ j, 𝒮.eTilde s j).HasOnlyNormalCrossings := by
  have hadm := 𝒮.isAdmissibleAt_of_prepHyp hprep
  exact Subscheme.hasOnlyNormalCrossings_iInf_totalTransform_ι
    (E := fun i : Fin (alphaT r ℜ.α s) => 𝒮.eHat s (idxT ℜ.α s r i)) (D := 𝒮.xBar s)
    (𝒮.isNonsingular_tHat_X s) (𝒮.isReduced_iInf_eHat s)
    (𝒮.hasOnlyNormalCrossingsWith_xBar_boundary s hadm)
    (𝒮.isTransversalFamilyWith_eHat s hadm hFE)

/-- The datum `(Ẽ_1, …, Ẽ_α̃ | J̃, b̃ | ã_1, …, ã_α̃)` of pp. 321–323 is a resolution datum on
`X̃` as soon as `b̃ > 0` and the stalks of `J̃` are non-zero: conditions (ii) of Def. 3 (II) are
the facts of p. 321 (`lem:IV.4-tilde-facts`).

Not in the paper: the paper presupposes that `ℜ^{N-1}_II` is a resolution datum; the hypotheses
`0 < b̃`, `J̃_x ≠ 0` are exactly the remaining conditions (i), (iii) of Def. 3 (II).

Conditional: the paper's datum `ℜ̃` need not be a datum (the `Ẽ_j` can be reducible), so the irreducibility of the non-empty `Ẽ_j` is the hypothesis
`hirr`; the repair, splitting into components, is not made. -/
theorem isDatum_datumTilde [Hironaka.HironakaCitedResults.{u}] {s : ℕ} (hprep : PrepHyp N ℜ r ν T x₀ s)
    (hFE : ∀ F, r = .closed F → ∀ i : Fin ℜ.α, ¬ F.pts ⊆ (ℜ.E i).pts) (bt : ℕ)
    (a : Fin (alphaT r ℜ.α s) → ℕ) (Jt : Subscheme (𝒮.xTilde s)) (hbt : 0 < bt)
    (hirr : ∀ j, (𝒮.eTilde s j).pts.Nonempty → (𝒮.eTilde s j).IsIrreducible)
    (hJt : ∀ x, Jt.stalkIdeal x ≠ ⊥) : (𝒮.datumTilde s bt a Jt).IsDatum := by
  refine ⟨hbt, fun j => ?_, 𝒮.hasOnlyNormalCrossings_iInf_eTilde hprep hFE, hJt⟩
  by_cases hne : (𝒮.eTilde s j).pts.Nonempty
  · obtain ⟨h1, h2⟩ := 𝒮.isNonsingular_and_isEverywhereOfCodim_eTilde hprep hFE j
    refine Or.inr ⟨h1, hirr j hne, ?_⟩
    obtain ⟨x, hx⟩ := hne
    exact le_antisymm (iInf₂_le x hx |>.trans (h2 x hx).le) (le_iInf₂ fun y hy => (h2 y hy).ge)
  · left
    exact Subscheme.eq_empty_of_pts_eq_empty (Set.not_nonempty_iff_eq_empty.mp hne)

/-- The datum `ℜ̃ = (Ẽ_1, …, Ẽ_α̃ | J̃, b̃ | ã_1, …, ã_α̃)` of pp. 321–323 satisfies the clauses of Definition
3 (II) that the lifting of §4 needs (`DatumII.Raw.IsWeakDatum`): `b̃ > 0`, the `Ẽ_j` are non-singular and
everywhere of codimension `1` (the irreducibility asserted on p. 321 is false), `Ẽ_1 ∪ ⋯ ∪ Ẽ_α̃` has only normal crossings, and `J̃_x ≠ 0` (the last two
hypotheses are the remaining conditions (i), (iii) of Def. 3 (II); `J̃_x ≠ 0` is the subject of
`stalkIdeal_jBar_ne_bot`, proved).

Not in the paper: the paper presupposes that `ℜ^{N-1}_II` is a resolution datum.  Needs `hFE` in the
closed case (`Ẽ_i = X̃` if `F = E_i`). -/
theorem isWeakDatum_datumTilde [Hironaka.HironakaCitedResults.{u}] {s : ℕ} (hprep : PrepHyp N ℜ r ν T x₀ s)
    (hFE : ∀ F, r = .closed F → ∀ i : Fin ℜ.α, ¬ F.pts ⊆ (ℜ.E i).pts) (bt : ℕ)
    (a : Fin (alphaT r ℜ.α s) → ℕ) (Jt : Subscheme (𝒮.xTilde s)) (hbt : 0 < bt)
    (hJt : ∀ x, Jt.stalkIdeal x ≠ ⊥) : (𝒮.datumTilde s bt a Jt).IsWeakDatum :=
  ⟨hbt, fun j => 𝒮.isNonsingular_and_isEverywhereOfCodim_eTilde hprep hFE j,
    𝒮.hasOnlyNormalCrossings_iInf_eTilde hprep hFE, hJt⟩

end Frame

/-- **Corollary of Lemma (CD.4)** (p. 318).  `x̂` is taken as any point of `ĥ_s⁻¹(x̂_0)` with
`c_s(x̂) = x` (it is unique by Lemma (CD.3)).

As printed (p. 319): "The closure `B` of `{x}` in `X_s` may be viewed as an irreducible reduced
subscheme of `X_s`, and there exists a unique subscheme `B̂` of `X̂_s` such that `c_s` induces an
isomorphism `B̂ → B`.  `x̂` is the generic point of `B̂`, and `B̂` is an algebraic scheme over a field
(i.e., over the residue field of `Ŝ`, where `Ŝ` is the local ring of `X̂_0` at `x̂_0`).  Therefore, we
have only to prove the assertion for the case in which `x̂` is a closed point of `X̂_s`, hence, `x` is
a closed point of `X_s`.  In this case, the monoidal transformation of `X_s` with center `x` is
permissible for the resolution datum `ℜ` [sic; `ℜ(s)`].  Applying Lemma (CD.4) to `B_s = x`, we get
the assertion of the corollary."  The proof follows these sentences:
* `B̂ = closure {x̂}` and `B` (Lemma (CD.3), `Standing.bijOn_and_mapsRSOP_and_exists_unique_totalTransform`);
  `B` lies in the fibre of `g_s` over the closed point `x_0` (`Standing.isClosed_singleton`), so it is
  a Jacobson space (`jacobsonSpace_toScheme_of_pts_subset_preimage`: a closed subspace of the fibre,
  an algebraic scheme over a field);
* "we have only to prove the assertion for the case in which `x̂` is a closed point" (gap filled, see
  below): the set of points of `X̄_s` with `ν(J̄(s)) ≥ b̄` is closed, `x̂` outside it would give an open
  set of `B̂ ≅ B` outside it, and a closed point `ŷ` there, where the assertion holds;
* at a closed point `x` of `S_ν(ℜ(s))`: `{x}` is a permissible center for `ℜ(s)`
  (`Standing.isPermissibleCenter_ofClosed_singleton`; "In this case, … is permissible", not argued
  in the paper; closed since `x` is a closed point of `X_s`), and Lemma (CD.4) for `B_s = x`
  (`exists_jBar_le_bBar_pow_of_isPermissibleCenter`: the invariants (a)$_s$–(d)$_s$ of the given
  succession, whose induction involves only the centers `B_t`, `t < s`, and the center clause for
  the center `{x}`, `centerClause_of_subset`) gives `J̄(s)_x̂ ⊆ Q̄^{b̄}`, `Q̄` the ideal of `{x̂}` in
  `X̄_s`, the maximal ideal (`exists_stalkIdeal_jBar_le_pow_and_bBar_le_nu_of_isClosed`).

Deviation from the paper (gap filled): "we have only to prove the assertion for the case in which
`x̂` is a closed point" is not argued (it needs the semicontinuity of the order on the non-singular
algebraic scheme `X̄_s`, `Subscheme.isClosed_setOf_le_nu_stalkIdeal`, and the density of closed points
of the Jacobson space `B`); "`x` is a closed point of `X_s`" for a closed point `x̂` of `B̂`; the
permissibility of the center `{x}` (stated without proof); that `B ⊆ S_ν(ℜ(s))` (closedness of `S_ν`).  The
modified succession with center `B_s = x` is not built: Lemma (CD.4) is applied at the stage `s` to
an arbitrary permissible center (its invariants do not involve `B_s`). -/
@[blueprint "cor:IV.CD-4"
  (statement := /-- \textbf{Corollary} (of \cref{lem:IV.CD-4}). Let $x$ be any point of
    $h_s^{-1}(x_0)\cap S_\nu(h_s^*(\mathfrak R))$, and $\hat x$ the unique point of
    $\hat h_s^{-1}(\hat x_0)$ such that $c_s(\hat x)=x$ (\cref{lem:IV.CD-3}). Then $\hat x$ is a
    point of $\bar X_s$ and the stalk of $\bar J(s)$ at $\hat x$ is contained in the $\bar b$th
    power of the maximal ideal, i.e., $\nu(\bar J(s)_{\hat x})\ge\bar b$
    (\cref{def:IV.4-construction}). (p.~318.) -/)
  (proof := /-- The closure $B$ of $\{x\}$ in $X_s$ may be viewed as an irreducible reduced
    subscheme of $X_s$, and there exists a unique subscheme $\hat B$ of $\hat X_s$ such that
    $c_s$ induces an isomorphism $\hat B\to B$ (\cref{lem:IV.CD-3}). $\hat x$ is the generic point
    of $\hat B$, and $\hat B$ is an algebraic scheme over a field (the residue field of $\hat S$,
    $\hat S$ the local ring of $\hat X_0$ at $\hat x_0$). Therefore, we have only to prove the
    assertion for the case in which $\hat x$ is a closed point of $\hat X_s$, hence $x$ is a
    closed point of $X_s$. In this case, the monoidal transformation of $X_s$ with center $x$ is
    permissible for the resolution datum $\mathfrak R$ [sic; $\mathfrak R(s)$]. Applying Lemma
    (CD.4) to $B_s=x$ (the construction of $\bar J(s)$ only involves $B_t$, $t<s$), we get the
    assertion of the corollary. \textsc{q.e.d.}

    \textbf{Deviation from the paper (gap filled).} The reduction ``we have only to prove the assertion
    for the case in which $\hat x$ is a closed point'' is not argued by the paper. Lean proves it: the
    set of points $\hat y$ of $\bar X_s$ with $\nu(\bar J(s)_{\hat y})\ge\bar b$ is closed
    ($\bar X_s$ is a non-singular algebraic scheme), $B\cong\hat B$ is a closed subspace of the fibre
    of $g_s$ over the closed point $x_0$, hence a Jacobson space, so if $\hat x$ were outside this
    closed set the non-empty open subset of $\hat B$ outside it would contain a closed point. That the
    monoidal transformation with center the closed point $x$ is permissible (stated without proof) is proved
    ($\{x\}$ is non-singular and irreducible, contained in $S_*(\mathfrak R(s))$, and $\bigcup E_i$ has
    only normal crossings with it, its ideal being the maximal ideal). Lemma (CD.4) is applied at the
    stage $s$ to this center without building the modified succession: its invariants
    (a)$_s$--(d)$_s$ involve only $B_t$, $t<s$, and the center clause is proved for any
    non-singular irreducible center in $S_\nu(\mathfrak R(s))$.

    \textbf{Paper misprint.} The paper (p.~319) says the monoidal transformation with center $x$
    is permissible ``for the resolution datum $\mathfrak R$''; meant is $\mathfrak R(s)$. -/)
  (proofUses := ["lem:IV.CD-3", "lem:IV.CD-4"])
  (latexEnv := "corollary")]
theorem Frame.exists_stalkIdeal_jBar_le_pow_and_bBar_le_nu_of_mem_Snu [Hironaka.HironakaCitedResults.{u}] {hS : Standing N ℜ r ν T x₀} (𝒮 : Frame hS) (s : ℕ) (x : T.X s)
    (hx : x ∈ (T.pre s).composite.base ⁻¹' {x₀} ∩ sNu (datum T ℜ s) (restriction T r s) ν)
    (xh : 𝒮.tHat.X s) (hxh : (𝒮.tHat.pre s).composite.base xh = hS.xh)
    (hcx : (𝒮.c s).base xh = x) :
    ∃ xb : (𝒮.xBar s).toScheme, (𝒮.xBar s).ι.base xb = xh ∧
      (𝒮.jBar s).stalkIdeal xb ≤ (maximalIdeal ((𝒮.xBar s).toScheme.presheaf.stalk xb)) ^ 𝒮.bBar ∧
      (𝒮.bBar : ℕ∞) ≤ Ideal.nu ((𝒮.jBar s).stalkIdeal xb) := by
  classical
  have hXa : IsAlgebraicScheme X := hS.ambient.1
  have hTa : IsAlgebraicScheme (𝒮.tHat.X s) := 𝒮.isAlgebraicScheme_tHat_X s
  have hadm : 𝒮.IsAdmissibleAt s := 𝒮.isAdmissibleAt_of_mem_image_sNu s ⟨x, hx.2, hx.1⟩
  have hXbns : (𝒮.xBar s).toScheme.IsNonsingular :=
    (𝒮.isNonsingular_and_isIrreducible_and_dim_xBar s hadm).1
  have : IsAlgebraicScheme (𝒮.xBar s).toScheme := isAlgebraicScheme_toScheme (𝒮.xBar s)
  -- the closed set `{ŷ ∈ X̄_s | ν(J̄(s)_ŷ) ≥ b̄}`
  set C0 : Set (𝒮.xBar s).toScheme :=
    {xb | (𝒮.bBar : ℕ∞) ≤ Ideal.nu ((𝒮.jBar s).stalkIdeal xb)} with hC0def
  have hC0 : IsClosed C0 := Subscheme.isClosed_setOf_le_nu_stalkIdeal hXbns (𝒮.jBar s) _
  set C : Set (𝒮.tHat.X s) := (𝒮.xBar s).ι.base '' C0 with hCdef
  have hC : IsClosed C := (𝒮.xBar s).ι.isClosedEmbedding.isClosedMap _ hC0
  suffices hxhC : xh ∈ C by
    obtain ⟨xb, hxb, hxbeq⟩ := hxhC
    exact ⟨xb, hxbeq, Ideal.le_pow_of_le_ord hxb, hxb⟩
  by_contra hxhC
  -- `B̂`, the closure of `{x̂}`
  set Bh : Subscheme (𝒮.tHat.X s) := Subscheme.ofClosed ⟨closure {xh}, isClosed_closure⟩ with hBhdef
  have hBhpts : Bh.pts = closure {xh} := Subscheme.pts_ofClosed _
  have hBhirr : Bh.IsIrreducible := Subscheme.isIrreducible_of_pts _ (by
    rw [hBhpts]; exact isIrreducible_singleton.closure)
  have hx0 : IsClosed ({hS.xh} : Set (AB.xHat0 X x₀)) := by
    have : IsRegularLocalRing (X.presheaf.stalk x₀) := hS.ambient.2.1 x₀
    exact IsLocalRing.isClosed_singleton_closedPoint _
  have hxhmem : xh ∈ Bh.pts := by rw [hBhpts]; exact subset_closure rfl
  have himg : (𝒮.tHat.pre s).composite.base '' Bh.pts = {hS.xh} := by
    refine Set.Subset.antisymm ?_ (Set.singleton_subset_iff.mpr ⟨xh, hxhmem, hxh⟩)
    rintro _ ⟨y, hy, rfl⟩
    rw [hBhpts] at hy
    have h1 : (𝒮.tHat.pre s).composite.base y ∈ closure {hS.xh} := by
      refine map_mem_closure (𝒮.tHat.pre s).composite.base.hom.continuous hy ?_
      intro z hz
      rw [Set.mem_singleton_iff.mp hz]
      exact hxh
    rwa [hx0.closure_eq] at h1
  -- Lemma (CD.3): `B̂ ≅ B`
  obtain ⟨hbij, -, hex⟩ := hS.bijOn_and_mapsRSOP_and_exists_unique_totalTransform 𝒮.toCompletion s
  obtain ⟨B, ⟨hBirr, hBh, hBpts, e, he⟩, -⟩ := hex Bh hBhirr himg
  -- `B` lies in the fibre of `g_s` over `x_0`, a Jacobson space
  have := hXa
  have : IsLocallyNoetherian X := (IsAlgebraicScheme.isNoetherian X).toIsLocallyNoetherian
  have hpr : IsProper (T.pre s).composite := Hironaka.MonoidalSuccession.isProper_composite _
  have hBfib : B.pts ⊆ (T.pre s).composite ⁻¹' {x₀} := by
    rw [hBpts]
    rintro _ ⟨y, hy, rfl⟩
    have hy1 : y ∈ (𝒮.tHat.pre s).composite.base ⁻¹' {hS.xh} := by
      have : (𝒮.tHat.pre s).composite.base y ∈ ((𝒮.tHat.pre s).composite.base '' Bh.pts) :=
        ⟨y, hy, rfl⟩
      rw [himg] at this; exact this
    exact hbij.mapsTo hy1
  have : JacobsonSpace B.toScheme :=
    jacobsonSpace_toScheme_of_pts_subset_preimage (T.pre s).composite x₀ B hBfib
  -- the open set of points of `B ≅ B̂` outside `C`
  obtain ⟨w, hw⟩ := Subscheme.exists_ι_eq_of_mem_pts Bh hxhmem
  let U : Set B.toScheme := {b | Bh.ι (e.inv b) ∉ C}
  have hUo : IsOpen U := by
    have : Continuous fun b : B.toScheme => Bh.ι (e.inv b) :=
      Bh.ι.continuous.comp e.inv.continuous
    exact hC.isOpen_compl.preimage this
  have hee : ∀ b : B.toScheme, e.hom (e.inv b) = b := fun b => by
    rw [← Scheme.Hom.comp_apply, e.inv_hom_id]; rfl
  have hUne : U.Nonempty := ⟨e.hom w, by
    show Bh.ι (e.inv (e.hom w)) ∉ C
    have : e.inv (e.hom w) = w := by
      rw [← Scheme.Hom.comp_apply, e.hom_inv_id]; rfl
    rw [this, hw]; exact hxhC⟩
  obtain ⟨b, hbU, hbcl⟩ := nonempty_inter_closedPoints hUne hUo.isLocallyClosed
  set yh : 𝒮.tHat.X s := Bh.ι (e.inv b) with hyh
  have hcy : (𝒮.c s) yh = B.ι b := by
    have h1 : B.ι (e.hom (e.inv b)) = (𝒮.c s) (Bh.ι (e.inv b)) := by
      have := congrArg (fun φ => φ (e.inv b)) he
      simpa [Scheme.Hom.comp_apply] using this
    rw [hee] at h1
    exact h1.symm
  have hycl : IsClosed ({B.ι b} : Set (T.X s)) := by
    have := B.ι.isClosedEmbedding.isClosedMap {b} hbcl
    rwa [Set.image_singleton] at this
  -- `y = c_s(ŷ) ∈ S_ν(ℜ(s))`
  have hyS : B.ι b ∈ sNu (datum T ℜ s) (restriction T r s) ν := by
    have hyB : yh ∈ Bh.pts := Subscheme.mem_pts_ι Bh _
    rw [hBhpts] at hyB
    have h1 : (𝒮.c s) yh ∈ closure {(𝒮.c s) xh} :=
      map_mem_closure (𝒮.c s).base.hom.continuous hyB (by
        intro z hz; rw [Set.mem_singleton_iff.mp hz]; rfl)
    rw [hcy, hcx] at h1
    refine (hS.isClosed_sNu_restriction s).closure_subset_iff.mpr ?_ h1
    intro z hz
    rw [Set.mem_singleton_iff.mp hz]
    exact hx.2
  -- the corollary at the closed point `y`: `ŷ ∈ C`
  have hyh0 : (𝒮.tHat.pre s).composite.base yh = hS.xh := by
    have : (𝒮.tHat.pre s).composite.base yh ∈ (𝒮.tHat.pre s).composite.base '' Bh.pts :=
      ⟨yh, Subscheme.mem_pts_ι Bh _, rfl⟩
    rw [himg] at this; exact this
  obtain ⟨xb, hxb, -, hnu⟩ := 𝒮.exists_stalkIdeal_jBar_le_pow_and_bBar_le_nu_of_isClosed s _ hyS
    hycl yh hyh0 hcy
  exact hbU ⟨xb, hnu, hxb⟩

/-- The facts stated on p. 321.

Deviation from the paper (gap filled): the paper states them without proof (the normal crossings and the `Ẽ_j` with "we see", the
dimension of `X̃` with no marker word).  Proved
here: `X̃ = X̄_s` is non-singular and irreducible (Lemma (CD.4)) and `dim X̃ = N - 1`
(`dim Ŝ_0 = N`;
`Ŝ_0/(z_0)` is a regular local domain of dimension `N - 1` since `z_0` is a member of a regular
system of parameters; the strict transform of the irreducible `X̄_t` not contained in the center
`B̂_t` has the same dimension, Remark 1, p. 169).  The assertions on normal crossings and on the
`Ẽ_j` are `hasOnlyNormalCrossingsWith_xBar_of_closed`, `hasOnlyNormalCrossingsWith_xBar_of_unrestricted`,
`isNonsingular_and_isEverywhereOfCodim_eTilde`, `hasOnlyNormalCrossings_iInf_eTilde` (all proved).  The
irreducibility of the `Ẽ_j` asserted on p. 321 is false as printed and is not stated; the codimension-one and normal-crossings
assertions on the `Ẽ_j` are also false as printed when `F = E_i`, and are stated under the hypothesis `hFE`.

\textbf{Counterexample to the irreducibility of the `Ẽ_j`.}  Let `k` have characteristic 0, `X = 𝔸³_k`
with coordinates `(u, v, w)`, `g = v² − u²(1 + u)`, `C = {w = g = 0}` the nodal curve with node `x₀`, and
`ℜ = (∅ | J, b)` with `J = (w(w − g))`, `b = 2`, without restriction.  Then
`S(ℜ) = S_ν(ℜ) = C` (the two smooth sheets `w = 0`, `w = g` meet along `C`), `ν = 2 ≥ b`, and `S_ν(ℜ)`
has no component of codimension 1, as §4 assumes.  Blow up `B₀ = {x₀}`; in the chart `v = u v₁`,
`w = u w₁` one has `g = u² H` with `H = v₁² − 1 − u` and `J(1) = (w₁(w₁ − u H))`, and the strict
transform `C' = {w₁ = H = 0}` meets the exceptional plane in the two points `v₁ = ±1`.  Blow up
`B₁ = C'`.  Both centers are permissible, and this is a permissible succession as p. 314 allows;
afterwards `S_ν(ℜ(2))` is a line over `x₀`, so condition [(1)] of p. 320 holds and
`x₀ ∈ h₂(S_ν(ℜ(2)))`.  The frame at `x₀` is `z₀ = w − g/2`, so that `w(w − g) = z₀² − g²/4` (`g₁₁ = 0`), `b̄ = 2`,
`J̄(0) = (g²)` and `C ⊆ X̄₀`.  Since `C' → C` is finite,
`B̂₁ = c₁⁻¹(C') = Spec Ô_{C',x} ⊔ Spec Ô_{C',y}` for the two points `x`, `y` of `C'` over `x₀`: two
components, which already falsifies p. 315 ("the non-singular irreducible center `B̂_s = c_s⁻¹(B_s)`")
at `s = 1`.  Moreover `B̂₁` lies in `X̄₁` and is a divisor of the regular surface `X̄₁`, so
`X̄₂ ≅ X̄₁` and `Ẽ₂ = Ê₂(2) ∩ X̃ ≅ B̂₁`: non-singular of codimension 1, with two disjoint components, each
meeting the fibre over `x̂₀`.  Shrinking `X̃` does not help, and the choice of frame does not matter.

\textbf{Counterexample to codimension 1 when `F = E_i`.}  In the closed case Definition 5 (II.1)
(p. 166) allows `F = E_i`; then `Ê_i(s) = X̄_s` and `Ẽ_i = X̃`.  Take `s = 0`, `X = 𝔸²`, `x₀` the origin,
`E₁ = F = V(x)`, `J = (y² + x³)`, `b = 2`, `a₁ = 0`.  Then `S(ℜ) = S_ν(ℜ) = {x₀}`, `ν = 2 > 0`, there is
no component of codimension 1, and `X̃ = V(z₀)` with `z₀` a generator of the ideal of `F = E₁`, so
`Ẽ₁ = X̃`, of codimension 0. -/
@[blueprint "lem:IV.4-tilde-facts"
  (statement := /-- Notation as in \cref{def:IV.4-conditions} and \cref{def:IV.4-tilde}.
    $\tilde X=\bar X_s$ is a non-singular irreducible scheme of dimension $N-1$. For the case in
    which $\mathfrak R=(\mathfrak R^N_{\mathrm{II}},F)$, we see that $\hat E_1(s)\cup\dots\cup
    \hat E_{\alpha+s}(s)$ has only normal crossings with $\tilde X$ in $\hat X_s$. In the other
    case, we see that $\hat E_{\alpha+1}(s)\cup\dots\cup\hat E_{\alpha+s}(s)$ has only normal
    crossings with $\tilde X$ in $\hat X_s$ (\cref{def:0.2-normal-crossings-with}). We see that,
    in both cases, $\tilde E_j$ $(1\le j\le\tilde\alpha)$ are non-singular irreducible subschemes
    of $\tilde X$ of codimension $1$, and $\tilde E_1\cup\dots\cup\tilde E_{\tilde\alpha}$ has
    only normal crossings on $\tilde X$. (p.~321.) (Formalization note (encoding): ``non-singular
    irreducible of codimension one'' allows the empty subscheme, by the agreement of p.~163.) -/)
  (proof := /-- $x_0\in h_s(S_\nu(\mathfrak R(s)))$, so $S_\nu(h_s^*(\mathfrak R))$ is not empty
    and Lemma (CD.4) (\cref{lem:IV.CD-4}) gives (1) of [vii]: $\bar X_s$ is non-singular and
    irreducible, of dimension $N-1$ as the strict transform of $\bar X_0=\operatorname{Spec}
    (\bar T_0)$ (\cref{lem:IV.4-construction-facts}) along monoidal transformations with centers
    contained in it. The $E_{\alpha+j}(s)$ are the exceptional divisors of $h_s$, whose centers
    $\hat B_t$ were contained in $\bar X_t$ ((2) of [vii]); hence their inverse images meet
    $\bar X_s$ transversally, and $c_s$ preserves normal crossings because the local
    homomorphisms induced by $c_s$ transform regular systems of parameters into such systems
    (\cref{lem:IV.CD-3}). In the closed case $\bar X_s=c_s^{-1}(F(s))$ and
    $E_1(s)\cup\dots\cup E_{\alpha+s}(s)\cup F(s)$ has only normal crossings (Definition~5 (II.1)
    and Remark~1, \S1, Ch.~I). Restricting to $\tilde X$ gives the assertions on the
    $\tilde E_j$.

    \textbf{Deviation from the paper (gap filled).} The paper states these facts (``we see'')
    without proof. The Lean development proves that $\tilde X=\bar X_s$ is non-singular and
    irreducible (Lemma (CD.4), \cref{lem:IV.CD-4}, applies since $S_\nu(\mathfrak R(s))$ is not
    empty) and of dimension $N-1$: $\dim\hat S_0=N$ (the completion of the regular local ring
    $S_0$ has the same embedding dimension), $z_0$ is a member of a regular system of
    parameters, so $\hat S_0/(z_0)$ is a regular local ring, a domain, of dimension $N-1$, and
    $\dim\bar X_0=\dim\hat S_0/(z_0)$; each $\bar X_{t+1}$ is the strict transform of the
    irreducible $\bar X_t$, which is not contained in the center $\hat B_t$ (otherwise
    $\bar X_{t+1}$ would be empty), so $\dim\bar X_{t+1}=\dim\bar X_t$ (Remark~1, p.~169,
    \cref{compat:strict-transform-dim-eq}). That $\hat X_0=\operatorname{Spec}(\hat S_0)$ is an
    algebraic scheme (p.~295) is used for the latter. The remaining assertions (normal crossings
    of the $\hat E_j(s)$ with $\tilde X$, and the properties of the $\tilde E_j$) are treated in
    the next paragraph.

    \textbf{Deviation from the paper (gap filled).} The normal crossings of the $\hat E_j(s)$ with
    $\tilde X$ (both cases) are proved by the induction of Lemma~4 of \S2 along $\hat g_s$, applied
    to the datum of type~I $(E;\,;V(z_0))$ on $\hat X_0$ with $E=\bigcup_{i\le\alpha}\hat E_i(0)$ in
    the closed case and $E=\emptyset$ otherwise. Its successive centers are the $\hat B_t=c_t^{-1}(B_t)
    \subseteq\bar X_t$, which are non-singular but in general reducible, so the induction is run on
    stalk presentations (parts of regular systems of parameters), not on irreducible centers
    (\cref{lem:IV.4-exceptional-transversal-nonsingular}); the boundary of the transform is
    $\bigcup\hat E_j(s)$ over the boundary indices, since $c_{t+1}^{-1}$ commutes with strict
    transforms (flat base change). At stage $t$ the boundary has only normal crossings with $\hat B_t$:
    $E_1(t)\cup\dots\cup E_{\alpha+t}(t)$ has only normal crossings with $B_t$ (permissibility), so
    does the sub-union, and $c_t^{-1}$ preserves this at the points over $\hat x_0$ (Lemma (CD.3)); every
    point of $\hat X_t$ is a generization of such a point (properness of $\hat g_t$) and the property
    is open (\cref{lem:IV.4-exceptional-transversal-nonsingular}, \cref{lem:normal-crossings-open}). The
    properties of the $\tilde E_j$ follow from \cref{lem:IV.4-tilde-facts-local}, the transversality
    being that $\bar X_s$ is irreducible and not contained in the boundary.

    \textbf{Statement false as printed (irreducibility).} The irreducibility of the $\tilde E_j$ asserted
    in the statement is false; the Lean statement keeps the true part: each
    $\tilde E_j$ is non-singular and everywhere of codimension $1$ on $\tilde X$.

    \emph{Counterexample.} Let $k$ have characteristic $0$, $X=\mathbb A^3_k$ with coordinates
    $(u,v,w)$, $g=v^2-u^2(1+u)$, $C=\{w=g=0\}$ the nodal curve with node $x_0$, and
    $\mathfrak R=(\emptyset\,|\,J,b)$ with $J=(w(w-g))$, $b=2$, without restriction. Then
    $S(\mathfrak R)=S_\nu(\mathfrak R)=C$ (the two smooth sheets $w=0$, $w=g$ meet along $C$),
    $\nu=2\ge b$, and $S_\nu(\mathfrak R)$ has no component of codimension $1$, as \S4 assumes.
    Blow up $B_0=\{x_0\}$; in the chart $v=uv_1$, $w=uw_1$ one has $g=u^2H$ with $H=v_1^2-1-u$ and
    $J(1)=(w_1(w_1-uH))$, and the strict transform $C'=\{w_1=H=0\}$ meets the exceptional plane in
    the two points $v_1=\pm1$. Blow up $B_1=C'$. Both centers are permissible, so this is a
    permissible succession as p.~314 allows; afterwards $S_\nu(\mathfrak R(2))$ is a line over
    $x_0$, so condition [(1)] of p.~320 holds and $x_0\in h_2(S_\nu(\mathfrak R(2)))$. The frame at
    $x_0$ is $z_0=w-g/2$, so that $w(w-g)=z_0^2-g^2/4$ ($g_{11}=0$), $\bar b=2$, $\bar J(0)=(g^2)$ and
    $C\subseteq\bar X_0$. Since $C'\to C$ is finite, $\hat B_1=c_1^{-1}(C')=
    \operatorname{Spec}\hat{\mathcal O}_{C',x}\sqcup\operatorname{Spec}\hat{\mathcal O}_{C',y}$ for
    the two points $x,y$ of $C'$ over $x_0$: two components, which already falsifies p.~315
    (``the non-singular irreducible center $\hat B_s=c_s^{-1}(B_s)$'') at $s=1$. Moreover
    $\hat B_1$ lies in $\bar X_1$ and is a divisor of the regular surface $\bar X_1$, so
    $\bar X_2\cong\bar X_1$ and $\tilde E_2=\hat E_2(2)\cap\tilde X\cong\hat B_1$: non-singular of
    codimension $1$, with two disjoint components, each meeting the fibre over $\hat x_0$.
    Shrinking $\tilde X$ does not help, and the choice of frame does not matter.

    \textbf{Statement false as printed ($F=E_i$).} In the closed case Definition~5 (II.1) allows $F=E_i$;
    then $\hat E_i(s)=c_s^{-1}(F(s))=\bar X_s$ and $\tilde E_i=\tilde X$ has codimension $0$, and
    $\tilde E_1\cup\dots\cup\tilde E_{\tilde\alpha}=\tilde X$ does not have only normal crossings. Counterexample
    ($s=0$): $X=\mathbb A^2$, $E_1=F=V(x)$, $J=(y^2+x^3)$, $b=2$, $a_1=0$, $x_0=0$. Then
    $S(\mathfrak R)=S_\nu(\mathfrak R)=\{x_0\}$, $\nu=2>0$, there is no component of codimension
    $1$, and $\tilde X=V(z_0)$ with $z_0$ a generator of the ideal of $F=E_1$, so
    $\tilde E_1=\tilde X$. The hypothesis ``$F\not\subseteq E_i$ for all $i$'' is added to the last
    two assertions. -/)
  (proofUses := ["lem:IV.CD-4", "lem:IV.4-construction-facts", "lem:IV.CD-3",
    "rem:I.1-transform-is-datum-II", "compat:strict-transform-dim-eq"])
  (latexEnv := "lemma")]
theorem Frame.isNonsingular_xTilde_and_dim_xTilde_and_hasOnlyNormalCrossings_of_prepHyp [Hironaka.HironakaCitedResults.{u}] {hS : Standing N ℜ r ν T x₀} (𝒮 : Frame hS) (s : ℕ)
    (hprep : PrepHyp N ℜ r ν T x₀ s)
    (hFE : ∀ F, r = .closed F → ∀ i : Fin ℜ.α, ¬ F.pts ⊆ (ℜ.E i).pts) :
    (𝒮.xTilde s).IsNonsingular ∧ IrreducibleSpace (𝒮.xTilde s) ∧
    (𝒮.xTilde s).dim = ((N - 1 : ℕ) : WithBot ℕ∞) ∧
    (∀ F, r = .closed F →
      (⨅ j : Fin (ℜ.α + s), 𝒮.eHat s j).HasOnlyNormalCrossingsWith (𝒮.xBar s)) ∧
    (r = .unrestricted →
      (⨅ j : Fin s, 𝒮.eHat s (Fin.natAdd ℜ.α j)).HasOnlyNormalCrossingsWith (𝒮.xBar s)) ∧
    (∀ j, (𝒮.eTilde s j).IsNonsingular ∧ (𝒮.eTilde s j).IsEverywhereOfCodim 1) ∧
    (⨅ j, 𝒮.eTilde s j).HasOnlyNormalCrossings := by
  obtain ⟨h1, h2, h3⟩ :=
    𝒮.isNonsingular_and_isIrreducible_and_dim_xBar s (𝒮.isAdmissibleAt_of_prepHyp hprep)
  exact ⟨h1, h2, h3, fun F hF => 𝒮.hasOnlyNormalCrossingsWith_xBar_of_closed hprep F hF,
    fun hr => 𝒮.hasOnlyNormalCrossingsWith_xBar_of_unrestricted hprep hr,
    fun j => 𝒮.isNonsingular_and_isEverywhereOfCodim_eTilde hprep hFE j,
    𝒮.hasOnlyNormalCrossings_iInf_eTilde hprep hFE⟩

/-! ### Helper facts for Remark 1 -/

theorem stalkIdeal_prod_eq {ι : Type*} (s : Finset ι) (f : ι → Subscheme X) (x : X) :
    (∏ i ∈ s, f i).stalkIdeal x = ∏ i ∈ s, (f i).stalkIdeal x := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    have : (1 : Subscheme X) = ⊤ := rfl
    rw [Finset.prod_empty, Finset.prod_empty, this, Subscheme.stalkIdeal_top_eq]
    exact Ideal.one_eq_top.symm
  | insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.prod_insert hi, Subscheme.stalkIdeal_mul_eq, ih]

theorem ord_mul_prod_ge {R : Type*} [CommRing R] (M : Ideal R) {ι : Type*} (s : Finset ι)
    (P : ι → Ideal R) (I : Ideal R) :
    Ideal.ord M I + ∑ i ∈ s, Ideal.ord M (P i) ≤ Ideal.ord M (I * ∏ i ∈ s, P i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.sum_insert hi]
    have h1 := (Ideal.ord_basic M ⊥ (I * ∏ j ∈ s, P j) (P i)).2.2.2
    have h2 : I * (P i * ∏ j ∈ s, P j) = (I * ∏ j ∈ s, P j) * P i := by ring
    rw [h2]
    calc Ideal.ord M I + (Ideal.ord M (P i) + ∑ j ∈ s, Ideal.ord M (P j))
        = (Ideal.ord M I + ∑ j ∈ s, Ideal.ord M (P j)) + Ideal.ord M (P i) := by ring
      _ ≤ Ideal.ord M (I * ∏ j ∈ s, P j) + Ideal.ord M (P i) := by gcongr
      _ ≤ _ := h1

theorem le_ord_pow_of_le {R : Type*} [CommRing R] {M Q : Ideal R} (hQ : Q ≤ M) (a : ℕ) :
    (a : ℕ∞) ≤ Ideal.ord M (Q ^ a) :=
  Ideal.le_ord (Ideal.pow_right_mono hQ a)

/-- `b` is unchanged by transforms (Def. 7 (II)). -/
theorem _root_.Hironaka.MonoidalSuccession.b_transformII {X Y : Scheme.{u}}
    (g : MonoidalSuccession X Y) (ℜ : DatumII.Raw X) : (g.transformII ℜ).b = ℜ.b := by
  induction g with
  | nil X => rfl
  | cons B t rest ih => exact (ih (ℜ.transform t)).trans rfl

theorem b_datum (T : AB.Tower X) (ℜ : DatumII.Raw X) (s : ℕ) : (datum T ℜ s).b = ℜ.b :=
  (T.pre s).b_transformII ℜ

namespace Frame
variable {hS : Standing N ℜ r ν T x₀} (𝒮 : Frame hS)

/-- p. 322: at a point `x̂'` of `S(ℜ̃)`, `ν(J̄(s)_{x̂'}) ≥ b̃`, where `J̄(s) = J̃ · ∏ P̃_j^{ã_j}`
("since `f̃` is permissible for `ℜ^{N-1}_II`, `ν(J̄(s)_{x̂'}) ≥ b̄` for all points `x̂' ∈ B̃`"). -/
theorem le_nu_jBar_of_mem_S {s : ℕ} (bt : ℕ) (a : Fin (alphaT r ℜ.α s) → ℕ)
    (Jt : Subscheme (𝒮.xTilde s)) (hJt : Jt * ∏ j, (𝒮.eTilde s j) ^ (a j) = 𝒮.jBar s)
    {xb : 𝒮.xTilde s} (hx : xb ∈ (𝒮.datumTilde s bt a Jt).S) :
    (bt : ℕ∞) ≤ Ideal.nu ((𝒮.jBar s).stalkIdeal xb) := by
  classical
  rw [← hJt, Subscheme.stalkIdeal_mul_eq, stalkIdeal_prod_eq]
  simp only [Subscheme.stalkIdeal_pow_eq]
  refine hx.trans ?_
  have h1 := ord_mul_prod_ge (maximalIdeal ((𝒮.xTilde s).presheaf.stalk xb)) Finset.univ
    (fun j => ((𝒮.eTilde s j).stalkIdeal xb) ^ (a j)) (Jt.stalkIdeal xb)
  refine le_trans ?_ h1
  show ((((Finset.univ.filter fun i => xb ∈ ((𝒮.eTilde s i)).pts).sum a : ℕ) : ℕ∞)) +
    Ideal.nu (Jt.stalkIdeal xb) ≤ _
  rw [add_comm]
  refine add_le_add le_rfl ?_
  push_cast
  calc (∑ i ∈ Finset.univ.filter fun i => xb ∈ ((𝒮.eTilde s i)).pts, (a i : ℕ∞))
      ≤ ∑ i ∈ Finset.univ.filter fun i => xb ∈ ((𝒮.eTilde s i)).pts,
          Ideal.ord (maximalIdeal ((𝒮.xTilde s).presheaf.stalk xb))
            (((𝒮.eTilde s i).stalkIdeal xb) ^ (a i)) := by
        refine Finset.sum_le_sum fun i hi => ?_
        exact le_ord_pow_of_le
          (Subscheme.stalkIdeal_le_maximalIdeal _ (Finset.mem_filter.mp hi).2) _
    _ ≤ _ := Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)

/-- `ν ≤ ν(ℜ(s)_{c̄_s(x̂')})` and `c̄_s(x̂') ∈ S(ℜ^N_II(s))` for the points `x̂'` of the center `B̃`
of a permissible transformation of `X̃` for `ℜ^{N-1}_II`, in the case `ν ≥ b` (Remark 1, p. 322: "Hence,
by Lemma (CD.5), `ν(J(s)_{x'}) ≥ ν` for all `x' ∈ c_s(B̃)`.  Since `ν ≥ b`, `S_ν(ℜ^N_II(s)) =
{x ∈ X_s | ν(J(s)_x) ≥ ν}`"). -/
theorem cBar_mem_sNu_of_mem_of_isPermissible [Hironaka.HironakaCitedResults.{u}] {s : ℕ} (hprep : PrepHyp N ℜ r ν T x₀ s)
    (hge : ℜ.b ≤ ν) (a : Fin (alphaT r ℜ.α s) → ℕ) (Jt : Subscheme (𝒮.xTilde s))
    (hJt : Jt * ∏ j, (𝒮.eTilde s j) ^ (a j) = 𝒮.jBar s)
    (Bt : Subscheme (𝒮.xTilde s))
    (hperm : (𝒮.datumTilde s 𝒮.bBar a Jt).IsPermissible Bt) {xb : 𝒮.xTilde s}
    (hxb : xb ∈ Bt.pts) :
    (datum T ℜ s).nuAt ((𝒮.cBar s).base xb) ≥ ν ∧
      (𝒮.cBar s).base xb ∈ (datum T ℜ s).sNu ν := by
  have hS : xb ∈ (𝒮.datumTilde s 𝒮.bBar a Jt).S := (hperm.2.1 hxb).1
  have h1 := 𝒮.le_nu_jBar_of_mem_S 𝒮.bBar a Jt hJt hS
  have h2 := 𝒮.le_nuAt_cBar_of_bBar_le_nu s (𝒮.isAdmissibleAt_of_prepHyp hprep).2.2.1 xb h1
  refine ⟨h2, ?_, h2⟩
  show ((datum T ℜ s).b : ℕ∞) ≤ _
  rw [b_datum]
  exact (Nat.cast_le.mpr hge).trans (h2.trans le_add_self)

end Frame

/-- A proper specialization strictly increases the dimension of the local ring at a point of
finite dimension: if `p ⤳ q` and `dim_p = dim_q < ∞` then `p = q`. -/
theorem eq_of_specializes_of_dimAt_eq {Y : Scheme.{u}} {p q : Y} (h : p ⤳ q) {n : ℕ}
    (hp : Y.dimAt p = (n : WithBot ℕ∞)) (hq : Y.dimAt q = (n : WithBot ℕ∞)) : p = q := by
  by_contra hne
  have hqp : q < p := by
    rw [lt_iff_le_not_ge]
    refine ⟨Scheme.le_iff_specializes.mpr h, fun h' => hne ?_⟩
    exact ((Scheme.le_iff_specializes.mp h').antisymm h).eq.symm
  have hc : ∀ {y : Y} {m : ℕ}, Y.dimAt y = (m : WithBot ℕ∞) → Order.coheight y = (m : ℕ∞) := by
    intro y m hy
    have h1 : ((Order.coheight y : ℕ∞) : WithBot ℕ∞) = (m : WithBot ℕ∞) := by
      rw [← ringKrullDim_stalk_eq_coheight]; exact hy
    exact_mod_cast WithBot.coe_injective h1
  have hp' := hc hp
  have hq' := hc hq
  have := Order.coheight_strictAnti hqp (by rw [hp']; exact ENat.natCast_lt_top n)
  rw [hp', hq'] at this
  exact lt_irrefl _ this

namespace Frame
variable {hS : Standing N ℜ r ν T x₀} (𝒮 : Frame hS)

/-- Remark 1, p. 322: "This shows, by the assumption [(1)], that `h_s(c_s(B̃)) = x_0`": an
irreducible subscheme `B̃` of `X̃` all of whose points go into `S_ν(ℜ(s))` has image the single
point `x_0` under `h_s ∘ c̄_s`.

Gap in the paper filled: the paper does not say why a finite set containing the image of the
irreducible `B̃` is a point, nor why this point is `x_0`; the image is a finite irreducible set, so
it has a generic point, all of whose specializations in it have the same dimension `N` (`[(1)]`),
hence it is one point `p`; and `p` is a generization of `x_0 = c_0(x̂_0)` (every point of
`Spec Ŝ_0` specializes to the closed point) at which `X` has dimension `N`, so `p = x_0`. -/
theorem image_cBar_eq_singleton {s : ℕ} (hprep : PrepHyp N ℜ r ν T x₀ s)
    (Bt : Subscheme (𝒮.xTilde s)) (hBti : Bt.IsIrreducible)
    (hsub : ∀ xb ∈ Bt.pts, (T.pre s).composite.base ((𝒮.cBar s).base xb) ∈
      (T.pre s).composite.base '' sNu (datum T ℜ s) (restriction T r s) ν) :
    (T.pre s).composite.base '' ((𝒮.cBar s).base '' Bt.pts) = {x₀} := by
  classical
  have := 𝒮.regShat
  set G : (𝒮.xBar s).toScheme → X := fun xb => (T.pre s).composite.base ((𝒮.cBar s).base xb)
    with hG
  have hGc : Continuous G := (T.pre s).composite.continuous.comp (𝒮.cBar s).continuous
  have hirr := isIrreducible_pts Bt hBti
  have himg : (T.pre s).composite.base '' ((𝒮.cBar s).base '' Bt.pts) = G '' Bt.pts := by
    rw [Set.image_image]
  rw [himg]
  have hS' : _root_.IsIrreducible (G '' Bt.pts) := hirr.image G hGc.continuousOn
  have hfinS : (G '' Bt.pts).Finite :=
    hprep.1.subset (by rintro _ ⟨xb, hxb, rfl⟩; exact hsub xb hxb)
  have hdimS : ∀ q ∈ G '' Bt.pts, X.dimAt q = (N : WithBot ℕ∞) := fun q hq => by
    obtain ⟨xb, hxb, rfl⟩ := hq
    exact hprep.2.1 _ (hsub xb hxb)
  have hdx : X.dimAt x₀ = (N : WithBot ℕ∞) := hprep.2.1 _ hprep.2.2.2
  -- a generic point `p` of the finite irreducible set
  obtain ⟨p, hpS, hSp⟩ : ∃ p ∈ G '' Bt.pts, G '' Bt.pts ⊆ closure {p} := by
    have h := isIrreducible_iff_sUnion_isClosed.mp hS'
    obtain ⟨z, hz, hsz⟩ := h (hfinS.toFinset.image fun p => closure ({p} : Set X))
      (by
        intro z hz
        obtain ⟨p, -, rfl⟩ := Finset.mem_image.mp hz
        exact isClosed_closure)
      (by
        intro q hq
        refine Set.mem_sUnion.mpr ⟨closure {q}, ?_, subset_closure rfl⟩
        exact Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨q, hfinS.mem_toFinset.mpr hq, rfl⟩))
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hz
    exact ⟨p, hfinS.mem_toFinset.mp hp, hsz⟩
  have hSeq : G '' Bt.pts = {p} := by
    refine Set.Subset.antisymm (fun q hq => ?_) (Set.singleton_subset_iff.mpr hpS)
    have hsp : p ⤳ q := specializes_iff_mem_closure.mpr (hSp hq)
    exact (eq_of_specializes_of_dimAt_eq hsp (hdimS p hpS) (hdimS q hq)).symm
  -- `p = x₀`
  have hpS' := hpS
  obtain ⟨xb₀, hxb₀, hp⟩ : ∃ xb ∈ Bt.pts, G xb = p := hpS
  have hpx : p ⤳ x₀ := by
    have h1 : ((𝒮.tHat.pre s).composite.base ((𝒮.xBar s).ι.base xb₀)) ⤳ hS.xh := by
      exact (PrimeSpectrum.le_iff_specializes (R := AB.Shat X x₀) _ _).mp
        (IsLocalRing.le_maximalIdeal
          ((𝒮.tHat.pre s).composite.base ((𝒮.xBar s).ι.base xb₀) :
            PrimeSpectrum (AB.Shat X x₀)).isPrime.ne_top)
    have h2 := h1.map (AB.c0 X x₀).continuous
    rw [Standing.xh, c0_xhat0] at h2
    have hGeq : G xb₀ = (AB.c0 X x₀).base
        ((𝒮.tHat.pre s).composite.base ((𝒮.xBar s).ι.base xb₀)) := by
      have hw := (𝒮.isPullback s).w
      rw [𝒮.c_zero] at hw
      have h3 : (𝒮.cBar s).base xb₀ = (𝒮.c s).base ((𝒮.xBar s).ι.base xb₀) := by
        rw [Frame.cBar, Scheme.Hom.comp_base]; rfl
      show (T.pre s).composite.base ((𝒮.cBar s).base xb₀) = _
      rw [h3, ← Scheme.Hom.comp_apply, hw, Scheme.Hom.comp_apply]
    rw [← hp, hGeq]
    exact h2
  rw [hSeq]
  exact congrArg _ (eq_of_specializes_of_dimAt_eq hpx (hdimS p hpS') hdx)

end Frame

/-- The fibre of `c_0 : Spec(Ŝ_0) → X` over `x_0` is `{x̂_0}`. -/
theorem eq_xhat0_of_c0_eq {x₀ : X} (hx : X.IsSimpleAt x₀) {P : AB.xHat0 X x₀}
    (hP : (AB.c0 X x₀).base P = x₀) : P = AB.xhat0 X x₀ hx := by
  have : IsRegularLocalRing (X.presheaf.stalk x₀) := hx
  have := isRegularLocalRing_adicCompletion_of_isRegularLocalRing (X.presheaf.stalk x₀)
  have hloc : IsLocalHom (algebraMap (X.presheaf.stalk x₀) (AB.Shat X x₀)) := inferInstance
  have hQ : (Spec.map (CommRingCat.ofHom
      (algebraMap (X.presheaf.stalk x₀) (AB.Shat X x₀)))).base P =
      IsLocalRing.closedPoint (X.presheaf.stalk x₀) := by
    refine (X.fromSpecStalk x₀).isEmbedding.injective ?_
    rw [Scheme.fromSpecStalk_closedPoint]
    exact hP
  have hle : maximalIdeal (X.presheaf.stalk x₀) ≤
      Ideal.comap (algebraMap (X.presheaf.stalk x₀) (AB.Shat X x₀))
        (show PrimeSpectrum (AB.Shat X x₀) from P).asIdeal := by
    have := congrArg PrimeSpectrum.asIdeal hQ
    exact this.symm.le
  have hle2 : maximalIdeal (AB.Shat X x₀) ≤ (show PrimeSpectrum (AB.Shat X x₀) from P).asIdeal := by
    rw [AdicCompletion.maximalIdeal_eq_map]
    exact Ideal.map_le_iff_le_comap.mpr hle
  have heq := (maximalIdeal.isMaximal (AB.Shat X x₀)).eq_of_le
    (show PrimeSpectrum (AB.Shat X x₀) from P).isPrime.ne_top hle2
  exact PrimeSpectrum.ext heq.symm

theorem pts_eq_range (D : Subscheme X) : D.pts = Set.range D.ι.base := by
  ext x
  refine ⟨fun h => ?_, fun ⟨z, hz⟩ => hz ▸ Subscheme.mem_pts_ι D z⟩
  obtain ⟨z, hz⟩ := Subscheme.exists_ι_eq_of_mem_pts D h
  exact ⟨z, hz⟩

theorem mem_sNu_of_mem_sNu_of_forall_closed {Y : Scheme.{u}} {ℜ' : DatumII.Raw Y}
    (R : Restriction Y) {c : ℕ∞} {x : Y} (h : x ∈ ℜ'.sNu c)
    (hF : ∀ F, R = .closed F → x ∈ F.pts) : x ∈ sNu ℜ' R c := by
  cases R with
  | unrestricted => exact h
  | closed F => exact ⟨h, hF F rfl⟩

/-- A commutative square of monoidal transformations over `c₁ : Yh → Y`, `c₂ : Yh' → Y'` with
`B̂ = c₁⁻¹(B)` carries the strict transform of `Vh` into that of `V` when `c₁(Vh) ⊆ V`. -/
theorem image_pts_strictTransform_subset {Y Yh : Scheme.{u}} {B : Subscheme Y}
    {Bh : Subscheme Yh} (t : MonoidalTransformation Y B) (th : MonoidalTransformation Yh Bh)
    (c₁ : Yh ⟶ Y) (c₂ : th.X' ⟶ t.X') (hcomm : th.f ≫ c₁ = c₂ ≫ t.f)
    (hB : Bh = Subscheme.totalTransform c₁ B) (V : Subscheme Y) (Vh : Subscheme Yh)
    (hV : c₁.base '' Vh.pts ⊆ V.pts) :
    c₂.base '' (Subscheme.strictTransform th Vh).pts ⊆ (Subscheme.strictTransform t V).pts := by
  have hcl : IsClosed (Subscheme.strictTransform t V).pts :=
    (Subscheme.strictTransform t V).support.isClosed
  have hBpts : Bh.pts = c₁.base ⁻¹' B.pts := by
    rw [hB]; exact FlatPreimm.pts_totalTransform c₁ B
  rintro _ ⟨p, hp, rfl⟩
  obtain ⟨q, hq, hqE, hqp⟩ := th.exists_generization_notMem_exceptional Vh hp
  have hfq : th.f.base q ∈ Vh.pts := th.pts_strictTransform_subset Vh hq
  have hcq : c₂.base q ∈ (Subscheme.strictTransform t V).pts := by
    have hnot : c₂.base q ∉ t.exceptional.pts := by
      intro h
      rw [t.pts_exceptional] at h
      apply hqE
      rw [th.pts_exceptional, hBpts]
      show c₁.base (th.f.base q) ∈ B.pts
      have : t.f.base (c₂.base q) = c₁.base (th.f.base q) := by
        rw [← Scheme.Hom.comp_apply, ← hcomm, Scheme.Hom.comp_apply]
      rw [← this]; exact h
    rw [t.mem_pts_strictTransform_iff_of_notMem V hnot]
    have : t.f.base (c₂.base q) = c₁.base (th.f.base q) := by
      rw [← Scheme.Hom.comp_apply, ← hcomm, Scheme.Hom.comp_apply]
    rw [this]
    exact hV ⟨_, hfq, rfl⟩
  have h2 : c₂.base p ∈ closure {c₂.base q} :=
    (specializes_iff_mem_closure.mp (hqp.map c₂.continuous))
  exact closure_minimal (Set.singleton_subset_iff.mpr hcq) hcl h2

/-- Base case (`[i]`, p. 315): if `z_0 ∈ S_0` generates the ideal of `F` at `x_0`, then
`c_0(V(z_0)) ⊆ F`. -/
theorem c0_image_vZ_subset_of_stalkIdeal_eq_span (hx : X.IsSimpleAt x₀) (F : Subscheme X)
    (z₀ : X.presheaf.stalk x₀) (hF : F.stalkIdeal x₀ = Ideal.span {z₀}) (z : AB.Shat X x₀)
    (hz : algebraMap (X.presheaf.stalk x₀) (AB.Shat X x₀) z₀ = z) :
    (AB.c0 X x₀).base '' (AB.vZ X x₀ z).pts ⊆ F.pts := by
  classical
  have : IsRegularLocalRing (X.presheaf.stalk x₀) := hx
  have := isRegularLocalRing_adicCompletion_of_isRegularLocalRing (X.presheaf.stalk x₀)
  have hloc : IsLocalHom (algebraMap (X.presheaf.stalk x₀) (AB.Shat X x₀)) := inferInstance
  rintro _ ⟨P, hP, rfl⟩
  obtain ⟨U, hxU⟩ := Subscheme.exists_affineOpen_mem x₀
  have hspec : ∀ Q : AB.xHat0 X x₀, (AB.c0 X x₀).base Q ∈ (U : X.Opens) := by
    intro Q
    have h1 : Q ⤳ AB.xhat0 X x₀ hx :=
      (PrimeSpectrum.le_iff_specializes (R := AB.Shat X x₀) _ _).mp
        (IsLocalRing.le_maximalIdeal (show PrimeSpectrum (AB.Shat X x₀) from Q).isPrime.ne_top)
    have h2 := h1.map (AB.c0 X x₀).continuous
    rw [c0_xhat0] at h2
    exact h2.mem_open U.1.2 hxU
  have hle : (⊤ : (AB.xHat0 X x₀).Opens) ≤ (AB.c0 X x₀) ⁻¹ᵁ U.1 := fun Q _ => hspec Q
  have : IsAffine (AB.xHat0 X x₀) := inferInstanceAs (IsAffine (Spec _))
  have hDle : Subscheme.totalTransform (AB.c0 X x₀) F ≤ AB.vZ X x₀ z := by
    refine Scheme.IdealSheafData.le_of_isAffine ?_
    show (Scheme.IdealSheafData.comap F (AB.c0 X x₀)).ideal _ ≤ _
    rw [ideal_comap_eq_map_appLE (AB.c0 X x₀) F U ⟨⊤, isAffineOpen_top _⟩ hle]
    rw [Ideal.map_le_iff_le_comap]
    intro a ha
    have hga : X.presheaf.germ U x₀ hxU a ∈ Ideal.span {z₀} := by
      rw [← hF]; exact Ideal.subset_span ⟨U, hxU, a, ha, rfl⟩
    obtain ⟨w, hw⟩ := Ideal.mem_span_singleton'.mp hga
    have hc := appLE_specMap_fromSpecStalk
      (CommRingCat.ofHom (algebraMap (X.presheaf.stalk x₀) (AB.Shat X x₀))) U.1 hxU hle a
    rw [Ideal.mem_comap]
    have hz' : (CommRingCat.ofHom (algebraMap (X.presheaf.stalk x₀) (AB.Shat X x₀))).hom
        (X.presheaf.germ U x₀ hxU a) = algebraMap _ _ w * z := by
      rw [← hw, map_mul]; exact congrArg _ hz
    have hmem : (Scheme.ΓSpecIso (CommRingCat.of (AB.Shat X x₀))).inv.hom
        (algebraMap _ _ w * z) ∈ Ideal.map (Scheme.ΓSpecIso (CommRingCat.of (AB.Shat X x₀))).inv.hom
          (Ideal.span {z}) :=
      Ideal.mem_map_of_mem _ (Ideal.mul_mem_left _ _ (Ideal.subset_span rfl))
    have hc' : ((AB.c0 X x₀).appLE U.1 ⊤ hle).hom a = (Scheme.ΓSpecIso
        (CommRingCat.of (AB.Shat X x₀))).inv.hom ((CommRingCat.ofHom
          (algebraMap (X.presheaf.stalk x₀) (AB.Shat X x₀))).hom (X.presheaf.germ U x₀ hxU a)) :=
      hc
    show ((AB.c0 X x₀).appLE U.1 ⊤ hle).hom a ∈ _
    rw [hc', hz']
    unfold AB.vZ
    rw [Scheme.IdealSheafData.ofIdealTop_ideal]
    exact Ideal.mem_map_of_mem _ hmem
  have := Scheme.IdealSheafData.support_antitone hDle
  have hP' : P ∈ (Subscheme.totalTransform (AB.c0 X x₀) F).pts := this hP
  rw [FlatPreimm.pts_totalTransform] at hP'
  exact hP'

namespace Frame
variable {hS : Standing N ℜ r ν T x₀} (𝒮 : Frame hS)

/-- `c_0 ∘ ĝ_s = g_s ∘ c_s` on points (the commutative square `X̂_s = X_s ×_X X̂_0`). -/
theorem c0_comp_pre_apply (s : ℕ) (y : 𝒮.tHat.X s) :
    (AB.c0 X x₀).base ((𝒮.tHat.pre s).composite.base y) =
      (T.pre s).composite.base ((𝒮.c s).base y) := by
  have hw := (𝒮.isPullback s).w
  rw [𝒮.c_zero] at hw
  rw [← Scheme.Hom.comp_apply, ← hw, Scheme.Hom.comp_apply]

/-- `c_t(X̄_t) ⊆ F(t)` for all `t` (p. 321: "in the closed case `X̄_s = c_s⁻¹(F(s))`"), given the
base case `c_0(X̄_0) ⊆ F`. -/
theorem c_image_xBar_subset (F : Subscheme X)
    (h0 : (AB.c0 X x₀).base '' (𝒮.xBar 0).pts ⊆ F.pts) :
    ∀ t, (𝒮.c t).base '' (𝒮.xBar t).pts ⊆ ((T.pre t).strictTransform F).pts := by
  intro t
  induction t with
  | zero => rw [𝒮.c_zero]; exact h0
  | succ t ih =>
    have h := image_pts_strictTransform_subset (T.monoidalTransformation t)
      (𝒮.tHat.monoidalTransformation t) (𝒮.c t) (𝒮.c (t + 1)) (𝒮.c_comm t) (𝒮.B_hat t)
      ((T.pre t).strictTransform F) (𝒮.xBar t) ih
    have e := MonoidalSuccession.strictTransform_snoc (T.pre t) (T.B t)
      (T.monoidalTransformation t) F
    show _ ⊆ ((MonoidalSuccession.snoc (T.pre t) (T.B t)
      (T.monoidalTransformation t)).strictTransform F).pts
    rw [e]
    exact h

/-- Remark 1, p. 322 (closed case): "`B ⊆ F(s)` (= the closure of `c_s(X̃)` in `X_s`)": the image of
`X̄_s` under `c_s` lies in `F(s)`.

Gap in the paper filled: in the
closed case the paper says `X̄_s = c_s⁻¹(F(s))`; here `c_s(X̄_s) ⊆ F(s)` is proved by induction on
`s`: a point of `X̄_{s+1}` is a specialization of a point of the strict transform off the
exceptional divisor, which `c_{s+1}` sends off `E(s+1)` into `f_s⁻¹(F(s))`, hence into the strict
transform of `F(s)`; and the latter is closed. -/
theorem cBar_mem_pts_of_closed {s : ℕ} (_hprep : PrepHyp N ℜ r ν T x₀ s)
    {F' : Subscheme (T.X s)} (hF' : restriction T r s = .closed F') (xb : 𝒮.xTilde s) :
    (𝒮.cBar s).base xb ∈ F'.pts := by
  classical
  have := 𝒮.regShat
  obtain ⟨F, hr, rfl⟩ := exists_eq_closed_of_restriction_eq_closed hF'
  obtain ⟨Fr, h1, hz, hFz, -⟩ := 𝒮.frame
  obtain ⟨z₀, hz₀, hFz₀⟩ := hFz F hr
  refine 𝒮.c_image_xBar_subset F (c0_image_vZ_subset_of_stalkIdeal_eq_span
    (hS.ambient.2.1 x₀) F z₀ hFz₀ 𝒮.z hz₀)
    s ⟨(𝒮.xBar s).ι.base xb, Subscheme.mem_pts_ι _ xb, ?_⟩
  show (𝒮.c s).base ((𝒮.xBar s).ι.base xb) = (𝒮.cBar s).base xb
  rw [Frame.cBar, Scheme.Hom.comp_base]
  rfl

/-- The index of a boundary divisor through a point: without restriction the `E_i(s)`, `i ≤ α`, miss
the point. -/
theorem exists_idxT_of_mem_pts {s : ℕ} {y : T.X s}
    (hout : r = .unrestricted → ∀ i : Fin ℜ.α, y ∉ (eSeq T ℜ s (Fin.castAdd s i)).pts)
    (j : Fin (ℜ.α + s)) (hy : y ∈ (eSeq T ℜ s j).pts) :
    ∃ i : Fin (alphaT r ℜ.α s), idxT ℜ.α s r i = j := by
  cases r with
  | closed F => exact ⟨j, rfl⟩
  | unrestricted =>
    by_cases hj : j.val < ℜ.α
    · exact (hout rfl ⟨j.val, hj⟩ hy).elim
    · refine ⟨⟨j.val - ℜ.α, by have h := j.2; simp only [alphaT]; omega⟩, Fin.ext ?_⟩
      show ℜ.α + (j.val - ℜ.α) = j.val
      omega

/-- **Remark 1, p. 322, normal crossings** (the stalkwise descent from `X̃` to `X_s`): see
`hasOnlyNormalCrossingsWith_eUnion_datum`.  The hypotheses `hover` (the points of `B̃` lie over `x̂_0`)
and `hout` (without restriction, the points of `B` miss the `E_i(s)`, `i ≤ α`) are consequences of the
assumptions `[(1)]`, `[(2)]` of p. 314. -/
theorem hasOnlyNormalCrossingsWith_eUnion_datum_aux [Hironaka.HironakaCitedResults.{u}] {s : ℕ} (hprep : PrepHyp N ℜ r ν T x₀ s)
    {bt : ℕ}
    (a : Fin (alphaT r ℜ.α s) → ℕ) (Jt : Subscheme (𝒮.xTilde s))
    (hII : (𝒮.datumTilde s bt a Jt).IsWeakDatum)
    (Bt : Subscheme (𝒮.xTilde s)) (hBt : Bt.IsNonsingular)
    (hperm : (𝒮.datumTilde s bt a Jt).IsPermissible Bt)
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
  -- (D) the adapted regular system of parameters on `X̃`
  obtain ⟨Zt, hZt, ⟨Tb, hTbZ, hBtTb⟩, hEj⟩ :=
    DatumTransform.exists_rsop_of_hasOnlyNormalCrossingsWithAt_of_isNonsingularDivisor (𝒮.eTilde s)
      (fun i => hII.2.1 i) (fun i => iInf_le (𝒮.eTilde s) i) (D := Bt)
      (hperm.2.2 (Bt.ι.base b) (Subscheme.mem_pts_ι Bt b))
  -- (E) the generators of the `Ẽ_i` through `ỹ`
  have hmaxk : ∀ k ∈ K₁, k ∈ maximalIdeal _ := fun k hk => hZ₀ext.mem_maximalIdeal (hK₁Z hk)
  have hTi : ∀ (i : Fin (alphaT r ℜ.α s)) (k : (T.X s).presheaf.stalk ((𝒮.cBar s).base (Bt.ι.base b))),
      (eSeq T ℜ s (idxT ℜ.α s r i)).stalkIdeal ((𝒮.cBar s).base (Bt.ι.base b)) = Ideal.span {k} →
      (𝒮.eTilde s i).stalkIdeal (Bt.ι.base b) = Ideal.span {((𝒮.cBar s).stalkMap (Bt.ι.base b)).hom k} := by
    intro i k hk
    have h1 : 𝒮.eTilde s i = Subscheme.totalTransform (𝒮.cBar s) (eSeq T ℜ s (idxT ℜ.α s r i)) :=
      (Subscheme.totalTransform_comp _ _ _).symm
    rw [h1, stalkIdeal_totalTransform, hk, Ideal.map_span, Set.image_singleton]
  have hex : ∀ k ∈ K₁, ∃ i : Fin (alphaT r ℜ.α s), (eSeq T ℜ s (idxT ℜ.α s r i)).stalkIdeal ((𝒮.cBar s).base (Bt.ι.base b)) =
      Ideal.span {k} ∧ ∃ β ∈ Zt, Ideal.span {((𝒮.cBar s).stalkMap (Bt.ι.base b)).hom k} = Ideal.span {β} := by
    intro k hk
    obtain ⟨j, hj⟩ := hK₁gen k hk
    have hjx : ((𝒮.cBar s).base (Bt.ι.base b)) ∈ (eSeq T ℜ s j).pts := Subscheme.mem_pts_iff_stalkIdeal_ne_top.mpr (by
      rw [hj]; exact (hZ₀ext.isPrime_span_singleton (hK₁Z hk)).ne_top)
    obtain ⟨i, rfl⟩ := exists_idxT_of_mem_pts (fun hr i => hout hr i b) j hjx
    refine ⟨i, hj, ?_⟩
    have hne : (𝒮.eTilde s i).stalkIdeal (Bt.ι.base b) ≠ ⊤ := by
      rw [hTi i k hj, Ne, Ideal.span_singleton_eq_top]
      intro hu
      exact (IsLocalRing.mem_maximalIdeal _).mp (hmaxk k hk) (IsLocalHom.map_nonunit _ hu)
    obtain ⟨β, hβZ, hβ⟩ := (hEj i).resolve_left hne
    exact ⟨β, hβZ, (hTi i k hj).symm.trans hβ⟩
  -- (F) transversality of the `Ê_i` to `X̄_s` at `ι(ỹ)`
  have hRhat : IsRegularLocalRing ((𝒮.tHat.X s).presheaf.stalk
      ((𝒮.xBar s).ι.base (Bt.ι.base b))) := 𝒮.isNonsingular_tHat_X s _
  have hsimpleF : ∀ i : Fin (alphaT r ℜ.α s),
      (𝒮.xBar s).ι.base (Bt.ι.base b) ∈ (𝒮.eHat s (idxT ℜ.α s r i)).pts →
      (𝒮.eHat s (idxT ℜ.α s r i)).IsSimpleAt ((𝒮.xBar s).ι.base (Bt.ι.base b)) ∧
        (𝒮.eHat s (idxT ℜ.α s r i)).codimAt ((𝒮.xBar s).ι.base (Bt.ι.base b)) = 1 :=
    fun i hi => 𝒮.isSimpleAt_and_codimAt_eq_one_totalTransform_c s
      (hS.isNonsingular_eSeq s _) (hS.exists_stalkIdeal_eSeq s _) _ hi
  have hTF : ∀ i : Fin (alphaT r ℜ.α s),
      (𝒮.xBar s).ι.base (Bt.ι.base b) ∈ (𝒮.eHat s (idxT ℜ.α s r i)).pts →
      ¬ (𝒮.eHat s (idxT ℜ.α s r i)).stalkIdeal ((𝒮.xBar s).ι.base (Bt.ι.base b)) ≤
        (𝒮.xBar s).stalkIdeal ((𝒮.xBar s).ι.base (Bt.ι.base b)) := by
    intro i hi hle
    have hEi : (𝒮.eTilde s i).stalkIdeal (Bt.ι.base b) ≠ ⊤ :=
      Subscheme.mem_pts_iff_stalkIdeal_ne_top.mp
        ((Subscheme.mem_pts_totalTransform_subschemeι_iff (Bt.ι.base b)).mpr hi)
    have hle0 : (𝒮.eTilde s i).stalkIdeal (Bt.ι.base b) ≤ ⊥ := by
      have h1 : (𝒮.eTilde s i).stalkIdeal (Bt.ι.base b) =
          ((𝒮.eHat s (idxT ℜ.α s r i)).stalkIdeal ((𝒮.xBar s).ι.base (Bt.ι.base b))).map
            ((𝒮.xBar s).ι.stalkMap (Bt.ι.base b)).hom := stalkIdeal_totalTransform _ _ _
      rw [h1]
      refine (Ideal.map_mono hle).trans ?_
      rw [stalkIdeal_eq_ker_stalkMap (𝒮.xBar s) (Bt.ι.base b), Ideal.map_le_iff_le_comap]
      intro y hy
      exact hy
    obtain ⟨β, hβZ, hβ⟩ := (hEj i).resolve_left hEi
    rw [hβ, Ideal.span_singleton_le_iff_mem, Ideal.mem_bot] at hle0
    exact (ExtendsToRSOP.of_isRegularSystemOfParameters hZt).ne_zero hβZ hle0
  have hNCy := 𝒮.hasOnlyNormalCrossingsWith_xBar_boundary s hadm
    ((𝒮.xBar s).ι.base (Bt.ι.base b)) (Subscheme.mem_pts_ι _ _)
  obtain ⟨-, zb, Kf, hzb, -, hKf1, -, hKfst, -, hKfinj⟩ :=
    Subscheme.exists_stalk_presentation_iInf_totalTransform_ι
      (E := fun i : Fin (alphaT r ℜ.α s) => 𝒮.eHat s (idxT ℜ.α s r i)) (D := 𝒮.xBar s)
      (𝒮.isReduced_iInf_eHat s) (Bt.ι.base b) hNCy hsimpleF hTF
  -- (G) choice of the generators `β k` and their injectivity
  have hβex : ∀ k ∈ K₁, ∃ β ∈ Zt, Ideal.span {((𝒮.cBar s).stalkMap (Bt.ι.base b)).hom k} =
      Ideal.span {β} := fun k hk => by
    obtain ⟨i, -, h⟩ := hex k hk
    exact h
  choose! β hβZ hβspan using hβex
  have hzbext : ExtendsToRSOP _ zb := ExtendsToRSOP.of_isRegularSystemOfParameters hzb
  have hinj : Set.InjOn β (K₁ : Set _) := by
    intro k hk k' hk' hkk'
    have hk := Finset.mem_coe.mp hk
    have hk' := Finset.mem_coe.mp hk'
    obtain ⟨i, hi, -⟩ := hex k hk
    obtain ⟨i', hi', -⟩ := hex k' hk'
    have hspan : (𝒮.eTilde s i).stalkIdeal (Bt.ι.base b) =
        (𝒮.eTilde s i').stalkIdeal (Bt.ι.base b) := by
      rw [hTi _ _ (hi), hTi _ _ (hi'), hβspan k hk, hβspan k' hk', hkk']
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
    obtain ⟨bi, hbi, hKi⟩ := hKf1 i (hthrough _ (hne i k hk hi))
    obtain ⟨bi', hbi', hKi'⟩ := hKf1 i' (hthrough _ (hne i' k' hk' hi'))
    have hspan2 : Ideal.span {bi} = Ideal.span {bi'} := by
      have h1 := hKfst i
      have h2 := hKfst i'
      rw [hKi, Finset.prod_singleton] at h1
      rw [hKi', Finset.prod_singleton] at h2
      exact h1.symm.trans (hspan.trans h2)
    have hbb : bi = bi' := hzbext.span_singleton_injOn (Finset.mem_coe.mpr hbi)
      (Finset.mem_coe.mpr hbi') hspan2
    have hKK : Kf i = Kf i' := by rw [hKi, hKi', hbb]
    have hhat := hKfinj _ _ hKK
    -- faithful flatness of `c_s` at `ι(ỹ)`
    have hflat := 𝒮.toCompletion.comap_map_stalkMap (hS.ambient.2.1 x₀) hS.isNonsingular_X
      hS.isNonsingular_B s ((𝒮.xBar s).ι.base (Bt.ι.base b)) (hover b)
    have e1 : ∀ i : Fin (alphaT r ℜ.α s), (𝒮.eHat s (idxT ℜ.α s r i)).stalkIdeal
        ((𝒮.xBar s).ι.base (Bt.ι.base b)) =
        ((eSeq T ℜ s (idxT ℜ.α s r i)).stalkIdeal ((𝒮.c s).base ((𝒮.xBar s).ι.base (Bt.ι.base b)))).map
          ((𝒮.c s).stalkMap ((𝒮.xBar s).ι.base (Bt.ι.base b))).hom :=
      fun i => stalkIdeal_totalTransform _ _ _
    have hkk := hflat (Ideal.span {k})
    have hkk' := hflat (Ideal.span {k'})
    rw [e1, e1] at hhat
    have e2 : (eSeq T ℜ s (idxT ℜ.α s r i)).stalkIdeal ((𝒮.c s).base ((𝒮.xBar s).ι.base (Bt.ι.base b))) = Ideal.span {k} := hi
    have e3 : (eSeq T ℜ s (idxT ℜ.α s r i')).stalkIdeal ((𝒮.c s).base ((𝒮.xBar s).ι.base (Bt.ι.base b))) = Ideal.span {k'} := hi'
    rw [e2, e3] at hhat
    have : Ideal.span {k} = Ideal.span {k'} :=
      hkk.symm.trans ((congrArg (Ideal.comap _) hhat).trans hkk')
    exact hZ₀ext.span_singleton_injOn (Finset.mem_coe.mpr (hK₁Z hk))
      (Finset.mem_coe.mpr (hK₁Z hk')) this
  -- (H) independence of the members outside `P` modulo `P`
  have hPprime := hP
  let Θ' := Θ.trans (Ideal.quotEquivOfEq hBtTb)
  have hΘ' : ∀ a, Θ' (Ideal.Quotient.mk _ a) = Ideal.Quotient.mk _ (((𝒮.cBar s).stalkMap (Bt.ι.base b)).hom a) := fun a => by
    simp only [Θ', RingEquiv.trans_apply, hΘ, Ideal.quotEquivOfEq_mk]
  have hF := rsopIndep_quotient_of_associated_rsop (((𝒮.cBar s).stalkMap (Bt.ι.base b)).hom) (B.stalkIdeal ((𝒮.cBar s).base (Bt.ι.base b))) hPreg hZt
    hTbZ Θ' hΘ' (K₁.filter (· ∉ B.stalkIdeal ((𝒮.cBar s).base (Bt.ι.base b)))) (fun k hk => (Finset.mem_filter.mp hk).2) β
    (fun k hk => hβZ k (Finset.mem_filter.mp hk).1) (fun k hk => hβspan k (Finset.mem_filter.mp hk).1)
    (hinj.mono fun k hk => Finset.mem_coe.mpr (Finset.mem_filter.mp (Finset.mem_coe.mp hk)).1)
  -- (I) conclusion
  obtain ⟨Z, T', hZ, hKZ, hT'Z, hT'⟩ :=
    exists_isRegularSystemOfParameters_subset_and_span_eq_prime (B.stalkIdeal ((𝒮.cBar s).base (Bt.ι.base b))) hPreg K₁
      hK₁ext hF
  have hEst : (datum T ℜ s).eUnion.stalkIdeal ((𝒮.cBar s).base (Bt.ι.base b)) = Ideal.span {∏ k ∈ K₁, k} := by
    rw [eUnion_datum_eq, DatumTransform.stalkIdeal_iInf_fintype]
    exact hK₁
  exact Subscheme.hasOnlyNormalCrossingsWithAt_of_stalkIdeal_eq hZ hKZ hT'Z hEst hT'.symm

/-- Remark 1, p. 322, and Remark 2, p. 324, normal crossings of `E_1(s) ∪ ⋯ ∪ E_{α+s}(s)` with `B`, for any
datum `ℜ̃` on `X̃` (any `b̃`) with a permissible center `B̃` all of whose points go into `S_ν(ℜ(s))`
under `c̄_s` and `c̄_s` inducing `B̃ ≅ B`: see `hasOnlyNormalCrossingsWith_eUnion_datum`. -/
theorem hasOnlyNormalCrossingsWith_eUnion_datum_of_forall_mem_sNu [Hironaka.HironakaCitedResults.{u}] {s : ℕ}
    (hprep : PrepHyp N ℜ r ν T x₀ s) {bt : ℕ} (a : Fin (alphaT r ℜ.α s) → ℕ)
    (Jt : Subscheme (𝒮.xTilde s)) (hII : (𝒮.datumTilde s bt a Jt).IsWeakDatum)
    (Bt : Subscheme (𝒮.xTilde s)) (hBt : Bt.IsNonsingular) (hBti : Bt.IsIrreducible)
    (hperm : (𝒮.datumTilde s bt a Jt).IsPermissible Bt)
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
  refine 𝒮.hasOnlyNormalCrossingsWith_eUnion_datum_aux hprep a Jt hII Bt hBt hperm B e he
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

/-- Remark 1, p. 322: "`E_1(s) ∪ ⋯ ∪ E_{α+s}(s)` has only normal crossings with `B`": "For the
case in which `ℜ = (ℜ^N_II, F)`, this is clear from the fact that `Ẽ_1 ∪ ⋯ ∪ Ẽ_α̃` has only
normal crossings with `B̃`.  For the case in which `ℜ = ℜ^N_II`, by the assumption [(2)],
`E_i(s) ∩ B` is empty for `1 ≤ i ≤ α`; hence we have only to show that `E_{α+1}(s) ∪ ⋯ ∪
E_{α+s}(s)` has only normal crossings with `B`, which is clear from the fact that `Ẽ_1 ∪ ⋯ ∪ Ẽ_α̃`
has only normal crossings with `B̃`."

Deviation from the paper (gap filled): "this is clear from the fact that `Ẽ_1 ∪ ⋯ ∪ Ẽ_α̃` has only
normal crossings with `B̃`" is proved by descent from `X̃` to `X_s` at a point `x = c̄_s(b̃)` of `B`
(`hasOnlyNormalCrossingsWith_eUnion_datum_aux`).  The stalks of the `E_j(s)` at `x` are generated by
members `k` of one regular system of parameters; their images in `O_{X̃,b̃}` generate the stalks of the
`Ẽ_j`, hence (up to units) distinct members `β_k` of the regular system of parameters adapted to
`E ∪ B̃` given by the hypothesis `hperm` (distinct because the `Ê_j` are transversal to `X̄_s` and
`c_s` is faithfully flat at the points over `x̂_0`, `NormalCrossingsPullback`); `c̄_s` induces an
isomorphism `O_{X,x}/B_x ≃ O_{X̃,b̃}/B̃_{b̃}` (`B̃ ≅ B`), so the `k ∉ B_x` stay independent modulo
`B_x`, and a regular system of parameters containing the `k` and generating `B_x` exists
(`exists_isRegularSystemOfParameters_subset_and_span_eq_prime`).  Without restriction the `E_i(s)`,
`i ≤ α`, do not meet `B ⊆ S_ν` by `[(2)]`. -/
theorem hasOnlyNormalCrossingsWith_eUnion_datum [Hironaka.HironakaCitedResults.{u}] {s : ℕ} (hprep : PrepHyp N ℜ r ν T x₀ s)
    (hge : ℜ.b ≤ ν) (a : Fin (alphaT r ℜ.α s) → ℕ) (Jt : Subscheme (𝒮.xTilde s))
    (hJt : Jt * ∏ j, (𝒮.eTilde s j) ^ (a j) = 𝒮.jBar s)
    (hII : (𝒮.datumTilde s 𝒮.bBar a Jt).IsWeakDatum)
    (Bt : Subscheme (𝒮.xTilde s)) (hBt : Bt.IsNonsingular) (hBti : Bt.IsIrreducible)
    (hperm : (𝒮.datumTilde s 𝒮.bBar a Jt).IsPermissible Bt)
    (B : Subscheme (T.X s)) (_hBc : (Bt.ι ≫ (𝒮.xBar s).ι).ker = Subscheme.totalTransform (𝒮.c s) B)
    (hBe : ∃ e : Bt.toScheme ≅ B.toScheme, e.hom ≫ B.ι = Bt.ι ≫ 𝒮.cBar s) :
    (datum T ℜ s).eUnion.HasOnlyNormalCrossingsWith B := by
  classical
  refine 𝒮.hasOnlyNormalCrossingsWith_eUnion_datum_of_forall_mem_sNu hprep a Jt hII Bt hBt hBti hperm
    B hBe fun xb hxb => ?_
  have := 𝒮.cBar_mem_sNu_of_mem_of_isPermissible hprep hge a Jt hJt Bt hperm hxb
  exact this.2

end Frame

/-! ## Remarks 2 and 3 and the relation: the transform of `ℜ^{N-1}_II` by `f̄_s` (pp. 322–326)

The stalkwise computation behind "we can easily see that the relation between `ℜ(s+1)` and
`f̄_s*(ℜ^{N-1}_II)` is the same" (p. 322) and Remark 3 (pp. 324–326).  `CenterData` bundles the
hypotheses on `B̃ ⊆ X̃` and `B ⊆ X_s`.  The main steps are: the total transforms `f̄_s⁻¹(Ẽ_j) =
Ẽ'_j · P̄_{s+1}^m` (`m = 1` iff `B ⊆ E_j(s)`; chart computation `DatumTransform.stalkIdeal_totalTransform_eq_strict_mul_exceptional_pow`
and the flat base change `c_{s+1}`), so that `Ẽ'_j` is the strict transform of `Ẽ_j`
(`eTilde_succ_castSuccT_eq_strictBar`) and `f̄_s*(ℜ^{N-1}_II)` is a datum of the form of stage `s+1`
(`transform_datumTilde_eq`); and the identity `J̃' ∏ (P̃'_j)^{ã_j} = W` whenever
`f̄_s⁻¹(J̃ ∏ P̃_j^{ã_j}) = P̄_{s+1}^{b̃} W` (`prod_eq_of_stalkIdeal_totalTransform_eq`).

Deviation from the paper (gap filled): "It follows from the definition of `f̃*(ℜ^{N-1}_II)` that
`J̃' ∏ (P̃'_j)^{ã_j} = f̃⁻¹(J̃ ∏ P̃_j^{ã_j})(P̃'_{α̃+1})^{-b̃}`" (p. 325) uses the divisibility of
`f̃⁻¹(J̃)` by `P̃'^{ν̃}` (Remark 2 of Ch. III, `Subscheme.totalTransform_le_exceptional_pow`, at the
generic point of the irreducible `B̃`) and `b̃ ≤ ∑_{B̃ ⊆ Ẽ_j} ã_j + ν̃` (the generic point lies in
`S(ℜ^{N-1}_II)`). -/

namespace Frame

variable {hS : Standing N ℜ r ν T x₀} (𝒮 : Frame hS)

/-- The monoidal transformation `f̄_s : X̄_{s+1} → X̄_s` with center `B̃`, as a
`MonoidalTransformation` (pp. 322, 324). -/
def tBar (s : ℕ) {Bt : Subscheme (𝒮.xTilde s)}
    (h : AB.IsMonoidalTransformationOf (𝒮.fBar s) Bt) : MonoidalTransformation (𝒮.xTilde s) Bt :=
  ⟨_, 𝒮.fBar s, h.1, h.2⟩

/-- A closed subscheme `B̃` of `X̃ = X̄_s` whose image in `X̂_s` is `B̂_s` is `B̂_s ∩ X̄_s`. -/
theorem eq_bBarOn_of_ker_eq (s : ℕ) {Bt : Subscheme (𝒮.xTilde s)}
    (hker : (Bt.ι ≫ (𝒮.xBar s).ι).ker = 𝒮.tHat.B s) : Bt = 𝒮.bBarOn s := by
  rw [bBarOn, ← hker]
  exact (Subscheme.totalTransform_ι_ker_comp_ι (𝒮.xBar s) Bt).symm

/-- `f̄_s` is the monoidal transformation of `X̄_s` with center `B̃` (p. 322: "`f̂_s` induces the
monoidal transformation `f̄_s : X̄_{s+1} → X̄_s` with the non-singular irreducible center `B̃`"). -/
theorem isMonoidalTransformationOf_fBar_of_ker_eq [Hironaka.HironakaCitedResults.{u}] (s : ℕ) {Bt : Subscheme (𝒮.xTilde s)}
    (hker : (Bt.ι ≫ (𝒮.xBar s).ι).ker = 𝒮.tHat.B s) :
    AB.IsMonoidalTransformationOf (𝒮.fBar s) Bt := by
  rw [𝒮.eq_bBarOn_of_ker_eq s hker]
  exact 𝒮.isMonoidalTransformationOf_fBar s

/-- The exceptional divisor of `f̄_s` is `P̄_{s+1}`. -/
theorem exceptional_tBar_eq_pBar (s : ℕ) {Bt : Subscheme (𝒮.xTilde s)}
    (h : AB.IsMonoidalTransformationOf (𝒮.fBar s) Bt)
    (hker : (Bt.ι ≫ (𝒮.xBar s).ι).ker = 𝒮.tHat.B s) :
    (𝒮.tBar s h).exceptional = 𝒮.pBar s := by
  rw [𝒮.pBar_eq s, ← 𝒮.eq_bBarOn_of_ker_eq s hker]
  rfl

end Frame

theorem _root_.Hironaka.DatumII.Raw.a_eq_of_eq {R₁ R₂ : DatumII.Raw X} (h : R₁ = R₂) {i : Fin R₁.α} {j : Fin R₂.α}
    (hij : (i : ℕ) = j) : R₁.a i = R₂.a j := by
  subst h
  rw [Fin.ext hij]

/-- `a_j(s+1) = a_j(s)` for `j < α + s` (Definition 7 (II)). -/
theorem aSeq_succ_of_lt (T : AB.Tower X) (ℜ : DatumII.Raw X) (s j : ℕ) (hj : j < ℜ.α + s) :
    aSeq T ℜ (s + 1) ⟨j, by omega⟩ = aSeq T ℜ s ⟨j, hj⟩ := by
  have hd : datum T ℜ (s + 1) = (datum T ℜ s).transform (T.monoidalTransformation s) :=
    MonoidalSuccession.transformII_snoc (T.pre s) (T.B s) (T.monoidalTransformation s) ℜ
  unfold aSeq
  rw [DatumII.Raw.a_eq_of_eq hd (j := Fin.castSucc (Fin.cast (alpha_datum T ℜ s).symm ⟨j, hj⟩))
    (by simp), a_transform_castSucc]

open Classical in
/-- `a_{α+s+1}(s+1) = (∑_{B_s ⊆ E_i(s)} a_i(s)) + ν(ℜ(s)) − b` (Definition 7 (II)). -/
theorem aSeq_succ_last (T : AB.Tower X) (ℜ : DatumII.Raw X) (s : ℕ) :
    aSeq T ℜ (s + 1) ⟨ℜ.α + s, by omega⟩ =
      (∑ i ∈ Finset.univ.filter fun i : Fin (datum T ℜ s).α =>
          (T.B s).IsContainedIn ((datum T ℜ s).E i), (datum T ℜ s).a i) +
        (datum T ℜ s).nu.toNat - (datum T ℜ s).b := by
  have hd : datum T ℜ (s + 1) = (datum T ℜ s).transform (T.monoidalTransformation s) :=
    MonoidalSuccession.transformII_snoc (T.pre s) (T.B s) (T.monoidalTransformation s) ℜ
  unfold aSeq
  rw [DatumII.Raw.a_eq_of_eq hd (j := Fin.last (datum T ℜ s).α) (by simp [alpha_datum]),
    a_transform_last]

/-- The strict transform of a subscheme of `X_s` in `X_{s+1}` under `f_s`, typed in `X_{s+1}`. -/
abbrev strictT (T : AB.Tower X) (s : ℕ) (E : Subscheme (T.X s)) : Subscheme (T.X (s + 1)) :=
  Subscheme.strictTransform (T.monoidalTransformation s) E

/-- The exceptional divisor `E_{α+s+1}(s+1) = f_s⁻¹(B_s)` of `f_s`, typed in `X_{s+1}`. -/
abbrev excT (T : AB.Tower X) (s : ℕ) : Subscheme (T.X (s + 1)) :=
  (T.monoidalTransformation s).exceptional

namespace Frame

variable {hS : Standing N ℜ r ν T x₀} (𝒮 : Frame hS)

/-- The points of `Ẽ_j`: `c̄_s⁻¹(E_j(s))`. -/
theorem pts_eTilde (s : ℕ) (j : Fin (alphaT r ℜ.α s)) :
    (𝒮.eTilde s j).pts = (𝒮.cBar s).base ⁻¹' (eSeq T ℜ s (idxT ℜ.α s r j)).pts := by
  unfold eTilde eHat
  rw [Subscheme.pts_totalTransform_eq_preimage, Subscheme.pts_totalTransform_eq_preimage]
  rfl

/-- The common hypotheses of Remarks 1–3 on a pair of centers: `B̃ ⊆ X̃` and `B = B_s ⊆ X_s`, both
non-singular and irreducible, `B̃ = c_s⁻¹(B)` as a subscheme of `X̂_s`, `c̄_s` inducing an
isomorphism `B̃ → B`, `B` a permissible center for `ℜ(s)` and the center of `f_s`. -/
structure CenterData (s : ℕ) (Bt : Subscheme (𝒮.xTilde s)) (Bs : Subscheme (T.X s)) : Prop where
  nonsingular_t : Bt.IsNonsingular
  irreducible_t : Bt.IsIrreducible
  nonsingular_s : Bs.IsNonsingular
  irreducible_s : Bs.IsIrreducible
  ker_eq : (Bt.ι ≫ (𝒮.xBar s).ι).ker = Subscheme.totalTransform (𝒮.c s) Bs
  iso : ∃ e : Bt.toScheme ≅ Bs.toScheme, e.hom ≫ Bs.ι = Bt.ι ≫ 𝒮.cBar s
  perm : (restriction T r s).IsPermissibleCenter (datum T ℜ s) Bs
  center_eq : T.B s = Bs

variable {𝒮} {s : ℕ} {Bt : Subscheme (𝒮.xTilde s)} {Bs : Subscheme (T.X s)}

theorem CenterData.ker_eq_B (h : 𝒮.CenterData s Bt Bs) :
    (Bt.ι ≫ (𝒮.xBar s).ι).ker = 𝒮.tHat.B s := by
  rw [h.ker_eq, 𝒮.B_hat s, h.center_eq]

theorem pts_eq_image_cBar_of_iso
    (hBe : ∃ e : Bt.toScheme ≅ Bs.toScheme, e.hom ≫ Bs.ι = Bt.ι ≫ 𝒮.cBar s) :
    Bs.pts = (𝒮.cBar s).base '' Bt.pts := by
  obtain ⟨e, he⟩ := hBe
  rw [pts_eq_range Bs, pts_eq_range Bt]
  ext x
  constructor
  · rintro ⟨z, rfl⟩
    obtain ⟨w, rfl⟩ : ∃ w, e.hom.base w = z := ⟨e.inv.base z, by
      rw [← Scheme.Hom.comp_apply, e.inv_hom_id]; rfl⟩
    refine ⟨Bt.ι.base w, ⟨w, rfl⟩, ?_⟩
    have := congrArg (fun φ => φ.base w) he
    simpa using this.symm
  · rintro ⟨_, ⟨w, rfl⟩, rfl⟩
    refine ⟨e.hom.base w, ?_⟩
    have := congrArg (fun φ => φ.base w) he
    simpa using this

theorem CenterData.pts_eq (h : 𝒮.CenterData s Bt Bs) :
    Bs.pts = (𝒮.cBar s).base '' Bt.pts :=
  pts_eq_image_cBar_of_iso h.iso

/-- `B̃ ⊆ Ẽ_j` iff `B ⊆ E_j(s)` (the equality of sets of points, via `c̄_s : B̃ ≅ B`). -/
theorem CenterData.pts_subset_eTilde_iff (h : 𝒮.CenterData s Bt Bs) (j : Fin (alphaT r ℜ.α s)) :
    Bt.pts ⊆ (𝒮.eTilde s j).pts ↔ Bs.pts ⊆ (eSeq T ℜ s (idxT ℜ.α s r j)).pts := by
  rw [𝒮.pts_eTilde s j, h.pts_eq, Set.image_subset_iff]

end Frame

theorem Standing.isNonsingularIrreducibleCodimOne_eSeq [Hironaka.HironakaCitedResults.{u}] (hS : Standing N ℜ r ν T x₀) (s : ℕ)
    (j : Fin (ℜ.α + s)) : (eSeq T ℜ s j).IsNonsingularIrreducibleCodimOne :=
  (hS.isDatum_datum s).2.1 _

theorem Standing.hasOnlyNormalCrossings_iInf_eSeq [Hironaka.HironakaCitedResults.{u}] (hS : Standing N ℜ r ν T x₀) (s : ℕ) :
    (⨅ j : Fin (ℜ.α + s), eSeq T ℜ s j).HasOnlyNormalCrossings := by
  rw [← eUnion_datum_eq]; exact (hS.isDatum_datum s).2.2.1

theorem Standing.hasOnlyNormalCrossingsWith_iInf_eSeq (hS : Standing N ℜ r ν T x₀) (s : ℕ) :
    (⨅ j : Fin (ℜ.α + s), eSeq T ℜ s j).HasOnlyNormalCrossingsWith (T.B s) := by
  rw [← eUnion_datum_eq]; exact (hS.isPermissible_B s).2.2

namespace Frame

variable {hS : Standing N ℜ r ν T x₀} (𝒮 : Frame hS)

/-- The exceptional divisor `Ê_{α+s+1}(s+1) = f̂_s⁻¹(B̂_s)` of `f̂_s`, as a subscheme of `X̂_{s+1}`. -/
abbrev excHat (s : ℕ) : Subscheme (𝒮.tHat.X (s + 1)) :=
  (𝒮.tHat.monoidalTransformation s).exceptional

open Classical in
/-- Stalks of the total transforms `f̂_s⁻¹(Ê_j(s))` (p. 324–325): by the flat base change
`c_{s+1}`, `f̂_s⁻¹(Ê_j(s)) = Ê_j(s+1) · (Ê_{α+s+1}(s+1))^m` with `m = 1` iff `B_s ⊆ E_j(s)`. -/
theorem stalkIdeal_totalTransform_eHat [Hironaka.HironakaCitedResults.{u}] (s : ℕ)
    (hB : (T.B s).IsIrreducible) (j : Fin (ℜ.α + s)) (yh : 𝒮.tHat.X (s + 1)) :
    (Subscheme.totalTransform (𝒮.tHat.f s) (𝒮.eHat s j)).stalkIdeal yh =
      (𝒮.eHat (s + 1) ⟨j.val, by omega⟩).stalkIdeal yh *
        ((𝒮.excHat s).stalkIdeal yh) ^
          (if (T.B s).pts ⊆ (eSeq T ℜ s j).pts then 1 else 0) := by
  have hyreg : IsRegularLocalRing (((T.monoidalTransformation s).X').presheaf.stalk
      ((𝒮.c (s + 1)).base yh)) := hS.isNonsingular_X (s + 1) _
  have hkey := Hironaka.DatumTransform.stalkIdeal_totalTransform_eq_strict_mul_exceptional_pow_of_pts_subset
    (B := T.B s) (eSeq T ℜ s) (hS.isNonsingular_X s) (hS.isNonsingularIrreducibleCodimOne_eSeq s)
    (hS.hasOnlyNormalCrossings_iInf_eSeq s) (hS.hasOnlyNormalCrossingsWith_iInf_eSeq s) hB
    (hS.isNonsingular_B s) (T.monoidalTransformation s) j ((𝒮.c (s + 1)).base yh)
  have h1 : Subscheme.totalTransform (𝒮.tHat.f s) (𝒮.eHat s j) =
      Subscheme.totalTransform (𝒮.c (s + 1))
        (Subscheme.totalTransform (T.f s) (eSeq T ℜ s j)) := by
    unfold eHat
    rw [← Subscheme.totalTransform_comp, ← Subscheme.totalTransform_comp]
    exact congrArg (fun g => Subscheme.totalTransform g (eSeq T ℜ s j)) (𝒮.c_comm s)
  have h2 : (𝒮.eHat (s + 1) ⟨j.val, by omega⟩).stalkIdeal yh =
      ((strictT T s (eSeq T ℜ s j)).stalkIdeal ((𝒮.c (s + 1)).base yh)).map
        ((𝒮.c (s + 1)).stalkMap yh).hom := by
    rw [← stalkIdeal_totalTransform]
    unfold eHat
    rw [eSeq_succ_of_lt T ℜ s j.val j.2]
  have h3 : (𝒮.excHat s).stalkIdeal yh =
      ((excT T s).stalkIdeal ((𝒮.c (s + 1)).base yh)).map ((𝒮.c (s + 1)).stalkMap yh).hom := by
    have hexc : 𝒮.excHat s = 𝒮.eHat (s + 1) ⟨ℜ.α + s, by omega⟩ := (𝒮.eHat_succ_last s).symm
    rw [hexc, ← stalkIdeal_totalTransform]
    unfold eHat
    rw [eSeq_succ_last T ℜ s]
  have hkey' : (Subscheme.totalTransform (T.f s) (eSeq T ℜ s j)).stalkIdeal
        ((𝒮.c (s + 1)).base yh) =
      (strictT T s (eSeq T ℜ s j)).stalkIdeal ((𝒮.c (s + 1)).base yh) *
        ((excT T s).stalkIdeal ((𝒮.c (s + 1)).base yh)) ^
          (if (T.B s).pts ⊆ (eSeq T ℜ s j).pts then 1 else 0) := hkey
  rw [h1, stalkIdeal_totalTransform, hkey', Ideal.map_mul, Ideal.map_pow, h2, h3]

end Frame

/-- The index of `Ẽ_j` among the `Ẽ'_1, …, Ẽ'_{α̃+1}` of stage `s+1` (p. 324). -/
def castSuccT (r : Restriction X) (α s : ℕ) (j : Fin (alphaT r α s)) : Fin (alphaT r α (s + 1)) :=
  Fin.cast (alphaT_succ r α s).symm (Fin.castSucc j)

/-- The index of the new divisor `Ẽ'_{α̃+1}` (p. 324). -/
def lastT (r : Restriction X) (α s : ℕ) : Fin (alphaT r α (s + 1)) :=
  Fin.cast (alphaT_succ r α s).symm (Fin.last _)

theorem idxT_castSuccT (r : Restriction X) (α s : ℕ) (j : Fin (alphaT r α s)) :
    (idxT α (s + 1) r (castSuccT r α s j) : ℕ) = (idxT α s r j : ℕ) := by
  cases r <;> rfl

theorem idxT_lastT (r : Restriction X) (α s : ℕ) :
    (idxT α (s + 1) r (lastT r α s) : ℕ) = α + s := by
  cases r <;> simp [idxT, lastT, alphaT]

theorem extendA_castSuccT {r : Restriction X} {α s : ℕ} (a : Fin (alphaT r α s) → ℕ) (anew : ℕ)
    (j : Fin (alphaT r α s)) : extendA a anew (castSuccT r α s j) = a j := by
  simp [extendA, castSuccT]

theorem extendA_lastT {r : Restriction X} {α s : ℕ} (a : Fin (alphaT r α s) → ℕ) (anew : ℕ) :
    extendA a anew (lastT r α s) = anew := by
  simp [extendA, lastT]

namespace Frame

variable {hS : Standing N ℜ r ν T x₀} (𝒮 : Frame hS)

theorem pBar_eq_totalTransform_excHat (s : ℕ) :
    𝒮.pBar s = Subscheme.totalTransform (𝒮.xBar (s + 1)).ι (𝒮.excHat s) := by
  have hexc : 𝒮.excHat s = 𝒮.eHat (s + 1) ⟨ℜ.α + s, by omega⟩ := (𝒮.eHat_succ_last s).symm
  rw [hexc]
  unfold eHat pBar
  rw [eSeq_succ_last T ℜ s]
  rfl

theorem eTilde_succ_lastT_eq_pBar (s : ℕ) :
    𝒮.eTilde (s + 1) (lastT r ℜ.α s) = 𝒮.pBar s := by
  rw [𝒮.pBar_eq_totalTransform_excHat s]
  unfold eTilde
  have : idxT ℜ.α (s + 1) r (lastT r ℜ.α s) = ⟨ℜ.α + s, by omega⟩ :=
    Fin.ext (idxT_lastT r ℜ.α s)
  rw [this, 𝒮.eHat_succ_last s]

variable {𝒮}

open Classical in
/-- Stalks of the total transforms `f̄_s⁻¹(Ẽ_j)` (pp. 324–325): `f̄_s⁻¹(Ẽ_j) = Ẽ'_j · P̄_{s+1}^m`
with `m = 1` iff `B ⊆ E_j(s)`. -/
theorem stalkIdeal_totalTransform_eTilde [Hironaka.HironakaCitedResults.{u}] {s : ℕ} {Bt : Subscheme (𝒮.xTilde s)}
    {Bs : Subscheme (T.X s)} (hd : 𝒮.CenterData s Bt Bs) (j : Fin (alphaT r ℜ.α s))
    (yb : (𝒮.xBar (s + 1)).toScheme) :
    (Subscheme.totalTransform (𝒮.fBar s) (𝒮.eTilde s j)).stalkIdeal yb =
      (𝒮.eTilde (s + 1) (castSuccT r ℜ.α s j)).stalkIdeal yb *
        ((𝒮.pBar s).stalkIdeal yb) ^
          (if Bs.pts ⊆ (eSeq T ℜ s (idxT ℜ.α s r j)).pts then 1 else 0) := by
  have hB : (T.B s).IsIrreducible := hd.center_eq ▸ hd.irreducible_s
  have hhat := 𝒮.stalkIdeal_totalTransform_eHat s hB (idxT ℜ.α s r j)
    ((𝒮.xBar (s + 1)).ι.base yb)
  have h1 : Subscheme.totalTransform (𝒮.fBar s) (𝒮.eTilde s j) =
      Subscheme.totalTransform (𝒮.xBar (s + 1)).ι
        (Subscheme.totalTransform (𝒮.tHat.f s) (𝒮.eHat s (idxT ℜ.α s r j))) := by
    unfold eTilde
    rw [← Subscheme.totalTransform_comp, ← Subscheme.totalTransform_comp]
    exact congrArg (fun g => Subscheme.totalTransform g (𝒮.eHat s (idxT ℜ.α s r j)))
      (𝒮.fBar_comm s)
  have h2 : 𝒮.eTilde (s + 1) (castSuccT r ℜ.α s j) =
      Subscheme.totalTransform (𝒮.xBar (s + 1)).ι
        (𝒮.eHat (s + 1) ⟨(idxT ℜ.α s r j).val, by omega⟩) := by
    unfold eTilde
    congr 2
    exact Fin.ext (idxT_castSuccT r ℜ.α s j)
  have e1 : (Subscheme.totalTransform (𝒮.xBar (s + 1)).ι
        (𝒮.eHat (s + 1) ⟨(idxT ℜ.α s r j).val, by omega⟩)).stalkIdeal yb =
      ((𝒮.eHat (s + 1) ⟨(idxT ℜ.α s r j).val, by omega⟩).stalkIdeal
        ((𝒮.xBar (s + 1)).ι.base yb)).map ((𝒮.xBar (s + 1)).ι.stalkMap yb).hom :=
    stalkIdeal_totalTransform _ _ _
  have e2 : (Subscheme.totalTransform (𝒮.xBar (s + 1)).ι (𝒮.excHat s)).stalkIdeal yb =
      ((𝒮.excHat s).stalkIdeal ((𝒮.xBar (s + 1)).ι.base yb)).map
        ((𝒮.xBar (s + 1)).ι.stalkMap yb).hom := stalkIdeal_totalTransform _ _ _
  have e3 : (Subscheme.totalTransform (𝒮.xBar (s + 1)).ι
        (Subscheme.totalTransform (𝒮.tHat.f s) (𝒮.eHat s (idxT ℜ.α s r j)))).stalkIdeal yb =
      ((Subscheme.totalTransform (𝒮.tHat.f s) (𝒮.eHat s (idxT ℜ.α s r j))).stalkIdeal
        ((𝒮.xBar (s + 1)).ι.base yb)).map ((𝒮.xBar (s + 1)).ι.stalkMap yb).hom :=
    stalkIdeal_totalTransform _ _ _
  rw [h1, h2, 𝒮.pBar_eq_totalTransform_excHat s, e3, e1, e2, hhat, Ideal.map_mul, Ideal.map_pow,
    hd.center_eq]

end Frame

namespace Frame

variable {hS : Standing N ℜ r ν T x₀} {𝒮 : Frame hS}

/-- The strict transform by `f̄_s` of a subscheme of `X̃`, typed in `X̃' = X̄_{s+1}`. -/
abbrev strictBar (𝒮 : Frame hS) (s : ℕ) {Bt : Subscheme (𝒮.xTilde s)}
    (h : AB.IsMonoidalTransformationOf (𝒮.fBar s) Bt) (E : Subscheme (𝒮.xTilde s)) :
    Subscheme (𝒮.xBar (s + 1)).toScheme :=
  Subscheme.strictTransform (𝒮.tBar s h) E

open Classical in
/-- The same total transform, computed on the datum `ℜ̃`: `f̄_s⁻¹(Ẽ_j) = (Ẽ_j)' · P̄_{s+1}^m`
with `(Ẽ_j)'` the strict transform and `m = 1` iff `B̃ ⊆ Ẽ_j` (the non-singular divisors `Ẽ_j` of the
datum have only normal crossings with the permissible center `B̃`). -/
theorem stalkIdeal_totalTransform_eTilde_strict [Hironaka.HironakaCitedResults.{u}] {s : ℕ} (hadm : 𝒮.IsAdmissibleAt s)
    {Bt : Subscheme (𝒮.xTilde s)} {Bs : Subscheme (T.X s)} (hd : 𝒮.CenterData s Bt Bs)
    {bt : ℕ} {a : Fin (alphaT r ℜ.α s) → ℕ} {Jt : Subscheme (𝒮.xTilde s)}
    (hII : (𝒮.datumTilde s bt a Jt).IsWeakDatum) (hperm : (𝒮.datumTilde s bt a Jt).IsPermissible Bt)
    (h : AB.IsMonoidalTransformationOf (𝒮.fBar s) Bt) (j : Fin (alphaT r ℜ.α s))
    (yb : (𝒮.xBar (s + 1)).toScheme) :
    (Subscheme.totalTransform (𝒮.fBar s) (𝒮.eTilde s j)).stalkIdeal yb =
      (𝒮.strictBar s h (𝒮.eTilde s j)).stalkIdeal yb *
        ((𝒮.pBar s).stalkIdeal yb) ^ (if Bt.pts ⊆ (𝒮.eTilde s j).pts then 1 else 0) := by
  have hX1 := (𝒮.isNonsingular_xBar_succ_and_isInvertibleIdeal_pBar s hadm.2.1 hadm.1).1
  have hyreg : IsRegularLocalRing (((𝒮.tBar s h).X').presheaf.stalk yb) := hX1 yb
  have key := Hironaka.DatumTransform.stalkIdeal_totalTransform_eq_strict_mul_exceptional_pow_of_pts_subset_of_isNonsingularDivisor
    (B := Bt) (𝒮.eTilde s) hadm.1.1 hII.2.1 hII.2.2.1 hperm.2.2 hd.irreducible_t hd.nonsingular_t
    (𝒮.tBar s h) j yb
  have hexc' : (𝒮.tBar s h).exceptional.stalkIdeal yb = (𝒮.pBar s).stalkIdeal yb :=
    congrArg (fun D : Subscheme (𝒮.xBar (s + 1)).toScheme => D.stalkIdeal yb)
      (𝒮.exceptional_tBar_eq_pBar s h hd.ker_eq_B)
  rw [hexc'] at key
  exact key

end Frame

namespace Frame

variable {hS : Standing N ℜ r ν T x₀} {𝒮 : Frame hS}

open Classical in
/-- **`Ẽ'_j` is the strict transform of `Ẽ_j`** (p. 324: "the `Ẽ'_j` … strict transforms commute with
`c_{s+1}` and with the restriction to `X̄_{s+1}`"): comparing the two computations of the total
transform `f̄_s⁻¹(Ẽ_j)` (`stalkIdeal_totalTransform_eTilde` and
`stalkIdeal_totalTransform_eTilde_strict`) and cancelling the non-zero-divisor `P̄_{s+1}^m`. -/
theorem eTilde_succ_castSuccT_eq_strictBar [Hironaka.HironakaCitedResults.{u}] {s : ℕ} (hadm : 𝒮.IsAdmissibleAt s)
    {Bt : Subscheme (𝒮.xTilde s)} {Bs : Subscheme (T.X s)} (hd : 𝒮.CenterData s Bt Bs)
    {bt : ℕ} {a : Fin (alphaT r ℜ.α s) → ℕ} {Jt : Subscheme (𝒮.xTilde s)}
    (hII : (𝒮.datumTilde s bt a Jt).IsWeakDatum) (hperm : (𝒮.datumTilde s bt a Jt).IsPermissible Bt)
    (h : AB.IsMonoidalTransformationOf (𝒮.fBar s) Bt) (j : Fin (alphaT r ℜ.α s)) :
    𝒮.eTilde (s + 1) (castSuccT r ℜ.α s j) = 𝒮.strictBar s h (𝒮.eTilde s j) := by
  refine Subscheme.ext_stalkIdeal fun yb => ?_
  have h1 := stalkIdeal_totalTransform_eTilde hd j yb
  have h2 := stalkIdeal_totalTransform_eTilde_strict hadm hd hII hperm h j yb
  have hm : (if Bt.pts ⊆ (𝒮.eTilde s j).pts then 1 else 0) =
      (if Bs.pts ⊆ (eSeq T ℜ s (idxT ℜ.α s r j)).pts then 1 else 0) := by
    simp only [hd.pts_subset_eTilde_iff j]
  rw [hm, h1] at h2
  obtain ⟨hX1, hinv⟩ := 𝒮.isNonsingular_xBar_succ_and_isInvertibleIdeal_pBar s hadm.2.1 hadm.1
  have : IsRegularLocalRing (((𝒮.xBar (s + 1)).toScheme).presheaf.stalk yb) := hX1 yb
  have := isDomain_of_isRegularLocalRing (((𝒮.xBar (s + 1)).toScheme).presheaf.stalk yb)
  obtain ⟨g, hg, hgnz⟩ := Subscheme.IsInvertibleIdeal.exists_stalkIdeal_eq_span hinv yb
  have hg0 : g ≠ 0 := nonZeroDivisors.ne_zero hgnz
  by_cases hsub : Bs.pts ⊆ (eSeq T ℜ s (idxT ℜ.α s r j)).pts
  · rw [ite_eq_left hsub, pow_one, hg, mul_comm _ (Ideal.span {g}), mul_comm _ (Ideal.span {g})] at h2
    exact (Ideal.span_singleton_mul_right_inj hg0).mp h2
  · rw [ite_eq_right hsub, pow_zero, mul_one, mul_one] at h2
    exact h2

end Frame

theorem _root_.Hironaka.DatumII.Raw.ext_of_cast {R₁ R₂ : DatumII.Raw X} (hα : R₁.α = R₂.α)
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

namespace Frame

variable {hS : Standing N ℜ r ν T x₀} {𝒮 : Frame hS}

/-- **The transform of `ℜ^{N-1}_II` by `f̄_s` has the form of the datum at stage `s+1`** (pp. 322, 324:
"`f̄_s*(ℜ^{N-1}_II)` can be written in the form `(Ẽ'_1, …, Ẽ'_{α̃+1} | J̃', b̃ | ã_1, …, ã_{α̃+1})`"):
the divisors are the `Ẽ'_j` formed for `h_{s+1}` and the exponents are `a_1, …, a_α̃` followed by a
new one; `J̃'` is the quotient `f̄_s⁻¹(J̃) P̄_{s+1}^{-ν̃}` of Definition 7 (II). -/
theorem transform_datumTilde_eq [Hironaka.HironakaCitedResults.{u}] {s : ℕ} (hadm : 𝒮.IsAdmissibleAt s)
    {Bt : Subscheme (𝒮.xTilde s)} {Bs : Subscheme (T.X s)} (hd : 𝒮.CenterData s Bt Bs)
    {bt : ℕ} {a : Fin (alphaT r ℜ.α s) → ℕ} {Jt : Subscheme (𝒮.xTilde s)}
    (hII : (𝒮.datumTilde s bt a Jt).IsWeakDatum) (hperm : (𝒮.datumTilde s bt a Jt).IsPermissible Bt)
    (h : AB.IsMonoidalTransformationOf (𝒮.fBar s) Bt) :
    (𝒮.datumTilde s bt a Jt).transform (𝒮.tBar s h) =
      𝒮.datumTilde (s + 1) bt
        (extendA a (((𝒮.datumTilde s bt a Jt).transform (𝒮.tBar s h)).a (Fin.last _)))
        ((𝒮.datumTilde s bt a Jt).transform (𝒮.tBar s h)).J := by
  refine DatumII.Raw.ext_of_cast (alphaT_succ r ℜ.α s).symm (fun i => ?_) (fun i => ?_) rfl rfl
  · induction i using Fin.lastCases with
    | last =>
      exact (E_transform_last (𝒮.datumTilde s bt a Jt) (𝒮.tBar s h)).trans
        ((𝒮.exceptional_tBar_eq_pBar s h hd.ker_eq_B).trans
          (𝒮.eTilde_succ_lastT_eq_pBar s).symm)
    | cast j =>
      exact (E_transform_castSucc (𝒮.datumTilde s bt a Jt) (𝒮.tBar s h) j).trans
        (𝒮.eTilde_succ_castSuccT_eq_strictBar hadm hd hII hperm h j).symm
  · induction i using Fin.lastCases with
    | last => exact (extendA_lastT a _).symm
    | cast j =>
      exact (a_transform_castSucc (𝒮.datumTilde s bt a Jt) (𝒮.tBar s h) j).trans
        (extendA_castSuccT a _ j).symm

end Frame

namespace Frame

variable {hS : Standing N ℜ r ν T x₀} {𝒮 : Frame hS}

open Classical in
/-- **Generic point of the center** (p. 325: "`f̃` is permissible for `ℜ^{N-1}_II`"): at the generic
point `ξ` of the irreducible center `B̃`, `ν(J̃_ξ) = ν̃`, `ν̃ < ∞`, and
`b̃ ≤ ∑_{B̃ ⊆ Ẽ_j} ã_j + ν̃` (`ξ ∈ S(ℜ̃)`). -/
theorem exists_isGenericPoint_nu_eq {s : ℕ} (hadm : 𝒮.IsAdmissibleAt s)
    {Bt : Subscheme (𝒮.xTilde s)} (hBti : Bt.IsIrreducible)
    {bt : ℕ} {a : Fin (alphaT r ℜ.α s) → ℕ} {Jt : Subscheme (𝒮.xTilde s)}
    (hII : (𝒮.datumTilde s bt a Jt).IsWeakDatum) (hperm : (𝒮.datumTilde s bt a Jt).IsPermissible Bt) :
    bt ≤ (∑ j, if Bt.pts ⊆ (𝒮.eTilde s j).pts then a j else 0) +
        (𝒮.datumTilde s bt a Jt).nu.toNat ∧
      ∃ ξ : 𝒮.xTilde s, IsGenericPoint ξ Bt.pts ∧
        ((𝒮.datumTilde s bt a Jt).nu.toNat : ℕ∞) ≤ Ideal.nu (Jt.stalkIdeal ξ) := by
  exact DatumII.Raw.b_le_sum_add_nu_and_exists_isGenericPoint_of_forall_stalkIdeal_ne_bot hadm.1.1 _
    hII.2.2.2 hBti hperm

end Frame

theorem prod_alphaT_succ {M : Type*} [CommMonoid M] (r : Restriction X) (α s : ℕ)
    (F : Fin (alphaT r α (s + 1)) → M) :
    ∏ i, F i = (∏ j, F (castSuccT r α s j)) * F (lastT r α s) := by
  have h1 := Fin.prod_univ_castSucc (fun k : Fin (alphaT r α s + 1) =>
    F (Fin.cast (alphaT_succ r α s).symm k))
  have h2 : ∏ k : Fin (alphaT r α s + 1), F (Fin.cast (alphaT_succ r α s).symm k) = ∏ i, F i :=
    Fintype.prod_equiv (finCongr (alphaT_succ r α s).symm) _ _ (fun k => rfl)
  rw [← h2, h1]
  rfl

namespace Frame

variable {hS : Standing N ℜ r ν T x₀} {𝒮 : Frame hS}

/-- The exceptional divisor of `f̄_s` typed in `X̄_{s+1}`. -/
theorem stalkIdeal_exceptional_tBar (s : ℕ) {Bt : Subscheme (𝒮.xTilde s)}
    (h : AB.IsMonoidalTransformationOf (𝒮.fBar s) Bt)
    (hker : (Bt.ι ≫ (𝒮.xBar s).ι).ker = 𝒮.tHat.B s) (yb : (𝒮.xBar (s + 1)).toScheme) :
    (𝒮.tBar s h).exceptional.stalkIdeal yb = (𝒮.pBar s).stalkIdeal yb :=
  congrArg (fun D : Subscheme (𝒮.xBar (s + 1)).toScheme => D.stalkIdeal yb)
    (𝒮.exceptional_tBar_eq_pBar s h hker)

/-- The sheaf of ideals `J̃'` of the transform `f̄_s*(ℜ̃)`, typed in `X̄_{s+1}`. -/
abbrev jTransform (𝒮 : Frame hS) (s : ℕ) {Bt : Subscheme (𝒮.xTilde s)}
    (h : AB.IsMonoidalTransformationOf (𝒮.fBar s) Bt) (Rt : DatumII.Raw (𝒮.xTilde s)) :
    Subscheme (𝒮.xBar (s + 1)).toScheme :=
  (Rt.transform (𝒮.tBar s h)).J

open Classical in
/-- The stalk of `J̃' = f̄_s⁻¹(J̃) P̄_{s+1}^{-ν̃}`. -/
theorem stalkIdeal_transform_J {s : ℕ} {Bt : Subscheme (𝒮.xTilde s)}
    (h : AB.IsMonoidalTransformationOf (𝒮.fBar s) Bt)
    (hker : (Bt.ι ≫ (𝒮.xBar s).ι).ker = 𝒮.tHat.B s) (Rt : DatumII.Raw (𝒮.xTilde s))
    (yb : (𝒮.xBar (s + 1)).toScheme) :
    (𝒮.jTransform s h Rt).stalkIdeal yb =
      ((Subscheme.totalTransform (𝒮.fBar s) Rt.J).stalkIdeal yb).colon
        (((𝒮.pBar s).stalkIdeal yb ^ Rt.nu.toNat : Ideal _) : Set _) := by
  have h1 : 𝒮.jTransform s h Rt =
      Subscheme.divPow (Subscheme.totalTransform (𝒮.fBar s) Rt.J) (𝒮.tBar s h).exceptional
        Rt.nu.toNat := rfl
  have hinv : (𝒮.tBar s h).exceptional.IsInvertibleIdeal := (𝒮.tBar s h).invertible
  have key := Subscheme.stalkIdeal_divPow (I := Subscheme.totalTransform (𝒮.fBar s) Rt.J)
    (P := (𝒮.tBar s h).exceptional) hinv Rt.nu.toNat yb
  have e := stalkIdeal_exceptional_tBar s h hker yb
  rw [h1]
  exact key.trans (congrArg (fun I : Ideal ((𝒮.xBar (s + 1)).toScheme.presheaf.stalk yb) =>
    ((Subscheme.totalTransform (𝒮.fBar s) Rt.J).stalkIdeal yb).colon
      ((I ^ Rt.nu.toNat : Ideal _) : Set _)) e)

end Frame

namespace Frame

variable {hS : Standing N ℜ r ν T x₀} {𝒮 : Frame hS}

open Classical in
/-- `∑_{B̃ ⊆ Ẽ_i} a_i = ∑_j m_j a_j` with `m_j = 1` iff `B ⊆ E_j(s)`. -/
theorem sum_filter_isContainedIn_eq {s : ℕ} {Bt : Subscheme (𝒮.xTilde s)}
    {Bs : Subscheme (T.X s)} (hd : 𝒮.CenterData s Bt Bs) (a : Fin (alphaT r ℜ.α s) → ℕ) :
    (∑ i ∈ Finset.univ.filter fun i : Fin (alphaT r ℜ.α s) => Bt.IsContainedIn (𝒮.eTilde s i), a i) =
      ∑ j, (if Bs.pts ⊆ (eSeq T ℜ s (idxT ℜ.α s r j)).pts then 1 else 0) * a j := by
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hiff : Bt.IsContainedIn (𝒮.eTilde s j) ↔ Bs.pts ⊆ (eSeq T ℜ s (idxT ℜ.α s r j)).pts := by
    rw [← hd.pts_subset_eTilde_iff j]
    constructor
    · exact pts_subset_of_isContainedIn
    · exact Subscheme.isContainedIn_of_pts_subset
        (Hironaka.DatumTransform.isReduced_of_isNonsingular hd.nonsingular_t)
  by_cases hc : Bt.IsContainedIn (𝒮.eTilde s j)
  · have hj := hiff.mp hc
    simp [hc, hj]
  · have hj : ¬ Bs.pts ⊆ (eSeq T ℜ s (idxT ℜ.α s r j)).pts := fun h' => hc (hiff.mpr h')
    simp [hc, hj]

open Classical in
/-- The stalk of the total transform of `J̃ ∏ P̃_j^{a_j}`. -/
theorem stalkIdeal_totalTransform_mul_prod [Hironaka.HironakaCitedResults.{u}] {s : ℕ} {Bt : Subscheme (𝒮.xTilde s)}
    {Bs : Subscheme (T.X s)} (hd : 𝒮.CenterData s Bt Bs) (a : Fin (alphaT r ℜ.α s) → ℕ)
    (Jt : Subscheme (𝒮.xTilde s)) (yb : (𝒮.xBar (s + 1)).toScheme) :
    (Subscheme.totalTransform (𝒮.fBar s) (Jt * ∏ j, (𝒮.eTilde s j) ^ (a j))).stalkIdeal yb =
      (Subscheme.totalTransform (𝒮.fBar s) Jt).stalkIdeal yb *
        ∏ j, ((𝒮.eTilde (s + 1) (castSuccT r ℜ.α s j)).stalkIdeal yb *
          ((𝒮.pBar s).stalkIdeal yb) ^
            (if Bs.pts ⊆ (eSeq T ℜ s (idxT ℜ.α s r j)).pts then 1 else 0)) ^ (a j) := by
  rw [stalkIdeal_totalTransform, Subscheme.stalkIdeal_mul_eq, Ideal.map_mul, stalkIdeal_prod_eq,
    Ideal.map_finset_prod, ← stalkIdeal_totalTransform]
  congr 1
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [Subscheme.stalkIdeal_pow_eq, Ideal.map_pow, ← stalkIdeal_totalTransform,
    stalkIdeal_totalTransform_eTilde hd j yb]

end Frame

namespace Frame

variable {hS : Standing N ℜ r ν T x₀} {𝒮 : Frame hS}

/-- `f̄_s⁻¹(J̃) ⊆ P̄_{s+1}^ν̃` (Ch. 0 §5, Remark 2 of Ch. III: `ν(J̃_ξ) ≥ ν̃` at the generic point `ξ`
of the irreducible non-singular center `B̃`). -/
theorem totalTransform_le_pBar_pow {s : ℕ} (hadm : 𝒮.IsAdmissibleAt s)
    {Bt : Subscheme (𝒮.xTilde s)} {Bs : Subscheme (T.X s)} (hd : 𝒮.CenterData s Bt Bs)
    {bt : ℕ} {a : Fin (alphaT r ℜ.α s) → ℕ} {Jt : Subscheme (𝒮.xTilde s)}
    (hII : (𝒮.datumTilde s bt a Jt).IsWeakDatum) (hperm : (𝒮.datumTilde s bt a Jt).IsPermissible Bt)
    (h : AB.IsMonoidalTransformationOf (𝒮.fBar s) Bt) :
    Subscheme.totalTransform (𝒮.fBar s) Jt ≤
      (𝒮.pBar s) ^ (𝒮.datumTilde s bt a Jt).nu.toNat := by
  obtain ⟨-, ξ, hξ, hν⟩ := exists_isGenericPoint_nu_eq hadm hd.irreducible_t hII hperm
  have key := Subscheme.totalTransform_le_exceptional_pow hadm.1.1 hd.nonsingular_t (𝒮.tBar s h)
    Jt hξ hν
  rw [𝒮.exceptional_tBar_eq_pBar s h hd.ker_eq_B] at key
  exact key

end Frame

namespace Frame

variable {hS : Standing N ℜ r ν T x₀} {𝒮 : Frame hS}

open Classical in
/-- **The identity of Remarks 2 and 3 (pp. 325–326), stalkwise**: if the total transform of
`J̃ ∏ P̃_j^{ã_j}` is `P̄_{s+1}^{b̃} · W`, then the datum `f̄_s*(ℜ^{N-1}_II)` has
`J̃' ∏ (P̃'_j)^{ã_j} = W`, where `J̃' = f̄_s⁻¹(J̃) P̄_{s+1}^{-ν̃}` and the exponent of the new divisor
`P̃'_{α̃+1} = P̄_{s+1}` is `ã_{α̃+1} = (∑_{B̃ ⊆ Ẽ_j} ã_j) + ν̃ − b̃`. -/
theorem prod_eq_of_stalkIdeal_totalTransform_eq [Hironaka.HironakaCitedResults.{u}] {s : ℕ} (hadm : 𝒮.IsAdmissibleAt s)
    {Bt : Subscheme (𝒮.xTilde s)} {Bs : Subscheme (T.X s)} (hd : 𝒮.CenterData s Bt Bs)
    {bt : ℕ} {a : Fin (alphaT r ℜ.α s) → ℕ} {Jt : Subscheme (𝒮.xTilde s)}
    (hII : (𝒮.datumTilde s bt a Jt).IsWeakDatum) (hperm : (𝒮.datumTilde s bt a Jt).IsPermissible Bt)
    (h : AB.IsMonoidalTransformationOf (𝒮.fBar s) Bt)
    (W : Subscheme (𝒮.xBar (s + 1)).toScheme)
    (hW : ∀ yb : (𝒮.xBar (s + 1)).toScheme,
      (Subscheme.totalTransform (𝒮.fBar s) (Jt * ∏ j, (𝒮.eTilde s j) ^ (a j))).stalkIdeal yb =
        ((𝒮.pBar s).stalkIdeal yb) ^ bt * W.stalkIdeal yb) :
    𝒮.jTransform s h (𝒮.datumTilde s bt a Jt) *
      ∏ i, (𝒮.eTilde (s + 1) i) ^
        (extendA a (((𝒮.datumTilde s bt a Jt).transform (𝒮.tBar s h)).a (Fin.last _)) i) = W := by
  classical
  refine Subscheme.ext_stalkIdeal fun yb => ?_
  obtain ⟨hX1, hinv⟩ := 𝒮.isNonsingular_xBar_succ_and_isInvertibleIdeal_pBar s hadm.2.1 hadm.1
  have hreg : IsRegularLocalRing (((𝒮.xBar (s + 1)).toScheme).presheaf.stalk yb) := hX1 yb
  have hdom := isDomain_of_isRegularLocalRing (((𝒮.xBar (s + 1)).toScheme).presheaf.stalk yb)
  obtain ⟨g, hg, hgnz⟩ := Subscheme.IsInvertibleIdeal.exists_stalkIdeal_eq_span hinv yb
  have hg0 : g ≠ 0 := nonZeroDivisors.ne_zero hgnz
  have hker := hd.ker_eq_B
  obtain ⟨hb, -⟩ := exists_isGenericPoint_nu_eq hadm hd.irreducible_t hII hperm
  have hanew : ((𝒮.datumTilde s bt a Jt).transform (𝒮.tBar s h)).a (Fin.last _) =
      (∑ j, (if Bs.pts ⊆ (eSeq T ℜ s (idxT ℜ.α s r j)).pts then 1 else 0) * a j) +
        (𝒮.datumTilde s bt a Jt).nu.toNat - bt := by
    rw [a_transform_last]
    show (∑ i ∈ Finset.univ.filter fun i => Bt.IsContainedIn (𝒮.eTilde s i), a i) +
      (𝒮.datumTilde s bt a Jt).nu.toNat - bt = _
    rw [sum_filter_isContainedIn_eq hd a]
  have hprod : ∏ i, (𝒮.eTilde (s + 1) i) ^
      (extendA a (((𝒮.datumTilde s bt a Jt).transform (𝒮.tBar s h)).a (Fin.last _)) i) =
      (∏ j, (𝒮.eTilde (s + 1) (castSuccT r ℜ.α s j)) ^ (a j)) *
        (𝒮.pBar s) ^ (((𝒮.datumTilde s bt a Jt).transform (𝒮.tBar s h)).a (Fin.last _)) := by
    rw [prod_alphaT_succ, extendA_lastT, 𝒮.eTilde_succ_lastT_eq_pBar s]
    simp only [extendA_castSuccT]
  rw [hprod, Subscheme.stalkIdeal_mul_eq, stalkIdeal_transform_J h hker, Subscheme.stalkIdeal_mul_eq,
    stalkIdeal_prod_eq, Subscheme.stalkIdeal_pow_eq, hg, hanew]
  simp only [Subscheme.stalkIdeal_pow_eq]
  have hJm := (Subscheme.le_iff_stalkIdeal_le.mp
    (totalTransform_le_pBar_pow hadm hd hII hperm h)) yb
  rw [Subscheme.stalkIdeal_pow_eq, hg, Ideal.span_singleton_pow] at hJm
  have hh := hW yb
  rw [stalkIdeal_totalTransform_mul_prod hd a Jt yb, hg] at hh
  rw [← mul_assoc]
  refine Ideal.colon_mul_prod_mul_pow_eq hg0 _ (fun j => (𝒮.eTilde (s + 1)
    (castSuccT r ℜ.α s j)).stalkIdeal yb) a
    (fun j => if Bs.pts ⊆ (eSeq T ℜ s (idxT ℜ.α s r j)).pts then 1 else 0)
    (𝒮.datumTilde s bt a Jt).nu.toNat bt (W.stalkIdeal yb) hJm (fun _ => ?_) hh
  refine le_of_le_of_eq hb ?_
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  by_cases hj : Bs.pts ⊆ (eSeq T ℜ s (idxT ℜ.α s r j)).pts
  · have hj' := (hd.pts_subset_eTilde_iff j).mpr hj
    simp [hj, hj']
  · have hj' : ¬ Bt.pts ⊆ (𝒮.eTilde s j).pts := fun h' => hj ((hd.pts_subset_eTilde_iff j).mp h')
    simp [hj, hj']

end Frame

theorem sum_univ_eq_sum_idxT {α s : ℕ} (r : Restriction X) (F : Fin (α + s) → ℕ)
    (hzero : r = .unrestricted → ∀ i : Fin α, F (Fin.castAdd s i) = 0) :
    ∑ i, F i = ∑ j : Fin (alphaT r α s), F (idxT α s r j) := by
  cases r with
  | closed F' => rfl
  | unrestricted =>
    rw [Fin.sum_univ_add]
    simp only [hzero rfl, Finset.sum_const_zero, zero_add]
    rfl

namespace Frame

variable {hS : Standing N ℜ r ν T x₀} {𝒮 : Frame hS}

open Classical in
/-- `∑_{B_s ⊆ E_i(s)} a_i(s) = ∑_{B̃ ⊆ Ẽ_j} c_j` (p. 326: "In view of the definition of `c_j` and
`Ẽ_j`, this equality is clear for the case `ℜ = (ℜ^N_II, F)`, and it follows for the other case if
`B_s ⊄ E_j(s)` for `1 ≤ j ≤ α`, a consequence of the assumption `[(2)]`"). -/
theorem sum_isContainedIn_datum_eq [Hironaka.HironakaCitedResults.{u}] {s : ℕ} (hprep : PrepHyp N ℜ r ν T x₀ s)
    {Bt : Subscheme (𝒮.xTilde s)} {Bs : Subscheme (T.X s)} (hd : 𝒮.CenterData s Bt Bs) :
    (∑ i ∈ Finset.univ.filter fun i : Fin (datum T ℜ s).α =>
        (T.B s).IsContainedIn ((datum T ℜ s).E i), (datum T ℜ s).a i) =
      ∑ j, (if Bs.pts ⊆ (eSeq T ℜ s (idxT ℜ.α s r j)).pts then 1 else 0) * cT T ℜ r s j := by
  have hBsred : Bs.IsReduced := Hironaka.DatumTransform.isReduced_of_isNonsingular hd.nonsingular_s
  have hiffB : ∀ i : Fin (ℜ.α + s), (T.B s).IsContainedIn (eSeq T ℜ s i) ↔
      Bs.pts ⊆ (eSeq T ℜ s i).pts := by
    intro i
    rw [hd.center_eq]
    exact ⟨pts_subset_of_isContainedIn, Subscheme.isContainedIn_of_pts_subset hBsred⟩
  -- reindex `Fin (datum T ℜ s).α` to `Fin (ℜ.α + s)`
  have h1 : (∑ i ∈ Finset.univ.filter fun i : Fin (datum T ℜ s).α =>
        (T.B s).IsContainedIn ((datum T ℜ s).E i), (datum T ℜ s).a i) =
      ∑ i : Fin (ℜ.α + s), (if Bs.pts ⊆ (eSeq T ℜ s i).pts then aSeq T ℜ s i else 0) := by
    rw [Finset.sum_filter]
    refine (Fintype.sum_equiv (finCongr (alpha_datum T ℜ s).symm) _ _ (fun i => ?_)).symm
    split_ifs with h1 h2 h2
    · rfl
    · exact absurd ((hiffB i).mpr h1) h2
    · exact absurd ((hiffB i).mp h2) h1
    · rfl
  rw [h1]
  refine sum_univ_eq_sum_idxT r _ (fun hr i => ?_) |>.trans ?_
  · -- `[(2)]`: `B_s` misses `E_i(s)`, `i ≤ α`
    have hne : Bs.pts.Nonempty := pts_nonempty_of_isIrreducible Bs hd.irreducible_s
    by_cases hc : Bs.pts ⊆ (eSeq T ℜ s (Fin.castAdd s i)).pts
    · exfalso
      have hsN := hS.pts_B_subset_sNu s hprep.sNu_nonempty
      rw [hd.center_eq] at hsN
      obtain ⟨x, hx⟩ := hne
      have h0 := hprep.2.2.1 hr i
      exact (Set.eq_empty_iff_forall_notMem.mp h0) x ⟨hc hx, hsN hx⟩
    · simp [hc]
  · refine Finset.sum_congr rfl fun j _ => ?_
    by_cases hc : Bs.pts ⊆ (eSeq T ℜ s (idxT ℜ.α s r j)).pts <;> simp [hc, cT]

end Frame

theorem cT_succ_castSuccT (T : AB.Tower X) (ℜ : DatumII.Raw X) (r : Restriction X) (s : ℕ)
    (j : Fin (alphaT r ℜ.α s)) :
    cT T ℜ r (s + 1) (castSuccT r ℜ.α s j) = cT T ℜ r s j := by
  have hlt : (idxT ℜ.α s r j : ℕ) < ℜ.α + s := (idxT ℜ.α s r j).2
  have h1 : idxT ℜ.α (s + 1) r (castSuccT r ℜ.α s j) =
      ⟨(idxT ℜ.α s r j : ℕ), by omega⟩ := Fin.ext (idxT_castSuccT r ℜ.α s j)
  unfold cT
  rw [h1]
  exact aSeq_succ_of_lt T ℜ s _ hlt

theorem cT_succ_lastT_eq (T : AB.Tower X) (ℜ : DatumII.Raw X) (r : Restriction X) (s : ℕ) :
    cT T ℜ r (s + 1) (lastT r ℜ.α s) = aSeq T ℜ (s + 1) ⟨ℜ.α + s, by omega⟩ := by
  unfold cT
  have h1 : idxT ℜ.α (s + 1) r (lastT r ℜ.α s) = ⟨ℜ.α + s, by omega⟩ :=
    Fin.ext (idxT_lastT r ℜ.α s)
  rw [h1]

namespace Frame

variable {hS : Standing N ℜ r ν T x₀} {𝒮 : Frame hS}

open Classical in
/-- `b ≤ ∑_{B_s ⊆ E_i(s)} a_i + ν` (the center `B_s` is permissible for `ℜ(s)`; Definition 4 (II),
`S(ℜ(s)) ∋ ξ`, `ξ` the generic point of `B_s`). -/
theorem b_le_sum_filter_add_nu [Hironaka.HironakaCitedResults.{u}] (hS : Standing N ℜ r ν T x₀) {s : ℕ}
    (hprep : PrepHyp N ℜ r ν T x₀ s) (hBs : (T.B s).IsIrreducible) :
    ℜ.b ≤ (∑ i ∈ Finset.univ.filter fun i : Fin (datum T ℜ s).α =>
        (T.B s).IsContainedIn ((datum T ℜ s).E i), (datum T ℜ s).a i) + ν := by
  have hnu : (datum T ℜ s).nu = ν := hS.nu_datum_eq s hprep.sNu_nonempty
  obtain ⟨hb, -⟩ := DatumII.Raw.b_le_sum_add_nu_and_exists_isGenericPoint (hS.isNonsingular_X s)
    (datum T ℜ s) (hS.isDatum_datum s) hBs (hS.isPermissible_B s)
  rw [hnu, b_datum] at hb
  have hBred : (T.B s).IsReduced :=
    Hironaka.DatumTransform.isReduced_of_isNonsingular (hS.isNonsingular_B s)
  have hsum : (∑ i ∈ Finset.univ.filter fun i : Fin (datum T ℜ s).α =>
        (T.B s).IsContainedIn ((datum T ℜ s).E i), (datum T ℜ s).a i) =
      ∑ i, if (T.B s).pts ⊆ ((datum T ℜ s).E i).pts then (datum T ℜ s).a i else 0 := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun i _ => ?_
    have : (T.B s).IsContainedIn ((datum T ℜ s).E i) ↔ (T.B s).pts ⊆ ((datum T ℜ s).E i).pts :=
      ⟨pts_subset_of_isContainedIn, Subscheme.isContainedIn_of_pts_subset hBred⟩
    simp only [this]
  rw [hsum]
  simpa using hb

end Frame

namespace Frame

variable {hS : Standing N ℜ r ν T x₀} {𝒮 : Frame hS}

open Classical in
/-- `c'_{α̃+1} + (b − ν) = ∑_{B̃ ⊆ Ẽ_j} c_j` (p. 326: "`c'_{α̃+1} = a_{α+s+1} = (∑_{B_s ⊆ E_j(s)} a_j) +
ν − b`" and `c'_{α̃+1} = e − (b − ν)`), for `ν < b`. -/
theorem cT_succ_lastT_add_eq [Hironaka.HironakaCitedResults.{u}] {s : ℕ} (hprep : PrepHyp N ℜ r ν T x₀ s) (hlt : ν < ℜ.b)
    {Bt : Subscheme (𝒮.xTilde s)} {Bs : Subscheme (T.X s)} (hd : 𝒮.CenterData s Bt Bs) :
    cT T ℜ r (s + 1) (lastT r ℜ.α s) + (ℜ.b - ν) =
      ∑ j, (if Bs.pts ⊆ (eSeq T ℜ s (idxT ℜ.α s r j)).pts then 1 else 0) * cT T ℜ r s j := by
  have hnu : (datum T ℜ s).nu = ν := hS.nu_datum_eq s hprep.sNu_nonempty
  have hb := b_le_sum_filter_add_nu hS hprep (hd.center_eq ▸ hd.irreducible_s)
  rw [cT_succ_lastT_eq, aSeq_succ_last, hnu, b_datum, sum_isContainedIn_datum_eq hprep hd] at *
  simp only [ENat.toNat_natCast] at *
  omega

/-- `f̄_s⁻¹(J̄(s)) = J̄(s+1) · P̄_{s+1}^{b̄}` (p. 316: `J̄(s+1) = f̄_s⁻¹(J̄(s))/(P̄_{s+1})^{b̄}`, which
makes sense since `J̄(s)` lies in the `b̄`-th power of the ideal of `B̂_s`). -/
theorem stalkIdeal_totalTransform_jBar [Hironaka.HironakaCitedResults.{u}] {s : ℕ} (hadm : 𝒮.IsAdmissibleAt s) (yb : (𝒮.xBar (s + 1)).toScheme) :
    (Subscheme.totalTransform (𝒮.fBar s) (𝒮.jBar s)).stalkIdeal yb =
      (𝒮.jBar (s + 1)).stalkIdeal yb * ((𝒮.pBar s).stalkIdeal yb) ^ 𝒮.bBar := by
  obtain ⟨hX1, hinv⟩ := 𝒮.isNonsingular_xBar_succ_and_isInvertibleIdeal_pBar s hadm.2.1 hadm.1
  have hreg : IsRegularLocalRing (((𝒮.xBar (s + 1)).toScheme).presheaf.stalk yb) := hX1 yb
  have hdom := isDomain_of_isRegularLocalRing (((𝒮.xBar (s + 1)).toScheme).presheaf.stalk yb)
  obtain ⟨g, hg, hgnz⟩ := Subscheme.IsInvertibleIdeal.exists_stalkIdeal_eq_span hinv yb
  have hdiv : (Subscheme.totalTransform (𝒮.fBar s) (𝒮.jBar s)).stalkIdeal yb ≤
      Ideal.span {g ^ 𝒮.bBar} := by
    rw [stalkIdeal_totalTransform, ← Ideal.span_singleton_pow, ← hg, 𝒮.pBar_eq s,
      stalkIdeal_totalTransform, ← Ideal.map_pow]
    exact Ideal.map_mono (hadm.2.2.2 _)
  have hjb : (𝒮.jBar (s + 1)).stalkIdeal yb =
      ((Subscheme.totalTransform (𝒮.fBar s) (𝒮.jBar s)).stalkIdeal yb).colon
        (((𝒮.pBar s).stalkIdeal yb ^ 𝒮.bBar : Ideal _) : Set _) :=
    Subscheme.stalkIdeal_divPow hinv 𝒮.bBar yb
  rw [hjb, hg]
  conv_lhs => rw [Ideal.eq_colon_mul_span_singleton_pow hdiv]

end Frame

namespace Frame

variable {hS : Standing N ℜ r ν T x₀} {𝒮 : Frame hS}

open Classical in
/-- The stalk of the total transform of `∏ P̃_j^{c_j}`. -/
theorem stalkIdeal_totalTransform_prod [Hironaka.HironakaCitedResults.{u}] {s : ℕ} {Bt : Subscheme (𝒮.xTilde s)}
    {Bs : Subscheme (T.X s)} (hd : 𝒮.CenterData s Bt Bs) (c : Fin (alphaT r ℜ.α s) → ℕ)
    (yb : (𝒮.xBar (s + 1)).toScheme) :
    (Subscheme.totalTransform (𝒮.fBar s) (∏ j, (𝒮.eTilde s j) ^ (c j))).stalkIdeal yb =
      ∏ j, ((𝒮.eTilde (s + 1) (castSuccT r ℜ.α s j)).stalkIdeal yb *
        ((𝒮.pBar s).stalkIdeal yb) ^
          (if Bs.pts ⊆ (eSeq T ℜ s (idxT ℜ.α s r j)).pts then 1 else 0)) ^ (c j) := by
  rw [stalkIdeal_totalTransform, stalkIdeal_prod_eq, Ideal.map_finset_prod]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [Subscheme.stalkIdeal_pow_eq, Ideal.map_pow, ← stalkIdeal_totalTransform,
    stalkIdeal_totalTransform_eTilde hd j yb]

open Classical in
/-- **The total transform of `J̄*(s)`** (p. 325): `f̄_s⁻¹(J̄*(s)) = P̄_{s+1}^{b̃} · J̄*(s+1)`,
`b̃ = b̄(b − ν)`. -/
theorem stalkIdeal_totalTransform_jBarStar [Hironaka.HironakaCitedResults.{u}] {s : ℕ} (hprep : PrepHyp N ℜ r ν T x₀ s)
    (hlt : ν < ℜ.b) {Bt : Subscheme (𝒮.xTilde s)} {Bs : Subscheme (T.X s)}
    (hd : 𝒮.CenterData s Bt Bs) (yb : (𝒮.xBar (s + 1)).toScheme) :
    (Subscheme.totalTransform (𝒮.fBar s) (𝒮.jBarStar s)).stalkIdeal yb =
      ((𝒮.pBar s).stalkIdeal yb) ^ (𝒮.bBar * (ℜ.b - ν)) * (𝒮.jBarStar (s + 1)).stalkIdeal yb := by
  have hadm := 𝒮.isAdmissibleAt_of_prepHyp hprep
  have hcl := cT_succ_lastT_add_eq (𝒮 := 𝒮) hprep hlt hd
  set e := ∑ j, (if Bs.pts ⊆ (eSeq T ℜ s (idxT ℜ.α s r j)).pts then 1 else 0) * cT T ℜ r s j with he
  have hprod : ∏ j, ((𝒮.eTilde (s + 1) (castSuccT r ℜ.α s j)).stalkIdeal yb *
        ((𝒮.pBar s).stalkIdeal yb) ^
          (if Bs.pts ⊆ (eSeq T ℜ s (idxT ℜ.α s r j)).pts then 1 else 0)) ^ (cT T ℜ r s j) =
      (∏ j, ((𝒮.eTilde (s + 1) (castSuccT r ℜ.α s j)).stalkIdeal yb) ^ (cT T ℜ r s j)) *
        ((𝒮.pBar s).stalkIdeal yb) ^ e := by
    simp only [mul_pow, Finset.prod_mul_distrib, ← pow_mul, Finset.prod_pow_eq_pow_sum, he]
  have hR : (𝒮.jBarStar (s + 1)).stalkIdeal yb =
      ((𝒮.jBar (s + 1)).stalkIdeal yb) ^ (ℜ.b - ν) ⊔
        ((∏ j, ((𝒮.eTilde (s + 1) (castSuccT r ℜ.α s j)).stalkIdeal yb) ^ (cT T ℜ r s j)) *
          ((𝒮.pBar s).stalkIdeal yb) ^ (cT T ℜ r (s + 1) (lastT r ℜ.α s))) ^ 𝒮.bBar := by
    unfold jBarStar
    rw [Scheme.IdealSheafData.add_eq_sup, Subscheme.stalkIdeal_sup_eq, Subscheme.stalkIdeal_pow_eq,
      Subscheme.stalkIdeal_pow_eq, prod_alphaT_succ, Subscheme.stalkIdeal_mul_eq,
      stalkIdeal_prod_eq, Subscheme.stalkIdeal_pow_eq, ← 𝒮.eTilde_succ_lastT_eq_pBar s]
    simp only [Subscheme.stalkIdeal_pow_eq, cT_succ_castSuccT]
  rw [hR]
  unfold jBarStar
  rw [Scheme.IdealSheafData.add_eq_sup, stalkIdeal_totalTransform, Subscheme.stalkIdeal_sup_eq,
    Ideal.map_sup, Subscheme.stalkIdeal_pow_eq, Subscheme.stalkIdeal_pow_eq, Ideal.map_pow,
    Ideal.map_pow, ← stalkIdeal_totalTransform, ← stalkIdeal_totalTransform,
    stalkIdeal_totalTransform_jBar hadm yb, stalkIdeal_totalTransform_prod hd _ yb, hprod]
  exact Ideal.sup_pow_mul_eq _ _ _ 𝒮.bBar (ℜ.b - ν) _ e hcl.symm

end Frame

/-! ## The case `ν ≧ b`: Remark 1 (pp. 321–322) -/

/-- **The center `B̃` of `X̃` descends to `X_s`** (the second half of the proof of Remark 1, p. 322;
and of Remark 2, p. 323): if all points of the irreducible non-singular `B̃ ⊆ X̃` go into `S_ν(ℜ(s))`
under `c̄_s`, then `B̃ = c_s⁻¹(B)` (as a subscheme of `X̂_s`) for an irreducible non-singular
subscheme `B` of `X_s` to which `c̄_s` restricts to an isomorphism `B̃ → B`.

Deviation from the paper (gap filled): "This shows, by the assumption [(1)], that `h_s(c_s(B̃)) = x_0`"
(`Frame.image_cBar_eq_singleton`) and Lemma (CD.3) are applied to `B̂ = B̃ ⊆ X̂_s`, whose image under
`ĥ_s` is `x̂_0`; see `exists_isPermissibleCenter_of_isPermissible_datumTilde`. -/
theorem Frame.exists_ker_eq_totalTransform_of_forall_mem_sNu {hS : Standing N ℜ r ν T x₀}
    (𝒮 : Frame hS) (s : ℕ) (hprep : PrepHyp N ℜ r ν T x₀ s)
    (Bt : Subscheme (𝒮.xTilde s)) (hBt : Bt.IsNonsingular) (hBti : Bt.IsIrreducible)
    (hmem : ∀ xb ∈ Bt.pts, (𝒮.cBar s).base xb ∈ (datum T ℜ s).sNu ν) :
    ∃ B : Subscheme (T.X s), B.IsNonsingular ∧ B.IsIrreducible ∧
      (Bt.ι ≫ (𝒮.xBar s).ι).ker = Subscheme.totalTransform (𝒮.c s) B ∧
      (∃ e : Bt.toScheme ≅ B.toScheme, e.hom ≫ B.ι = Bt.ι ≫ 𝒮.cBar s) ∧
      B.pts = (𝒮.cBar s).base '' Bt.pts := by
  classical
  have := 𝒮.regShat
  have hXa := hS.ambient.1
  have hmemR : ∀ xb ∈ Bt.pts, (𝒮.cBar s).base xb ∈ sNu (datum T ℜ s) (restriction T r s) ν :=
    fun xb hxb => mem_sNu_of_mem_sNu_of_forall_closed _ (hmem xb hxb)
      fun F hF => 𝒮.cBar_mem_pts_of_closed hprep hF xb
  have himg := 𝒮.image_cBar_eq_singleton hprep Bt hBti fun xb hxb => ⟨_, hmemR xb hxb, rfl⟩
  -- the subscheme `B̂ = B̃` of `X̂_s`
  set g := Bt.ι ≫ (𝒮.xBar s).ι with hg
  have hgc : IsClosedImmersion g := inferInstance
  have hiso : IsIso g.toImage := inferInstance
  let Bh : Subscheme (𝒮.tHat.X s) := g.ker
  let e₁ : Bt.toScheme ≅ Bh.toScheme := asIso g.toImage
  have he₁ : e₁.hom ≫ Bh.ι = g := Scheme.Hom.toImage_imageι g
  have hBhpts : Bh.pts = (𝒮.xBar s).ι.base '' Bt.pts := by
    have key : ∀ w, Bh.ι.base (e₁.hom.base w) = (𝒮.xBar s).ι.base (Bt.ι.base w) := fun w => by
      rw [← Scheme.Hom.comp_apply, he₁, hg, Scheme.Hom.comp_apply]
    ext y
    constructor
    · intro hy
      obtain ⟨z, rfl⟩ := (pts_eq_range Bh ▸ hy : y ∈ Set.range Bh.ι.base)
      obtain ⟨w, rfl⟩ : ∃ w, e₁.hom.base w = z := ⟨e₁.inv.base z, by
        rw [← Scheme.Hom.comp_apply, e₁.inv_hom_id]; rfl⟩
      exact ⟨Bt.ι.base w, Subscheme.mem_pts_ι Bt w, (key w).symm⟩
    · rintro ⟨xb, hxb, rfl⟩
      obtain ⟨w, rfl⟩ := (pts_eq_range Bt ▸ hxb : xb ∈ Set.range Bt.ι.base)
      rw [← key w, pts_eq_range Bh]
      exact ⟨_, rfl⟩
  have hBhirr : Bh.IsIrreducible := by
    have : IrreducibleSpace Bt.toScheme := hBti
    exact irreducibleSpace_of_iso e₁.symm
  have hx0 : (𝒮.tHat.pre s).composite.base '' Bh.pts = {hS.xh} := by
    have hne : Bt.pts.Nonempty := pts_nonempty_of_isIrreducible Bt hBti
    refine Set.eq_singleton_iff_nonempty_unique_mem.mpr ⟨?_, ?_⟩
    · obtain ⟨xb, hxb⟩ := hne
      have : (𝒮.xBar s).ι.base xb ∈ Bh.pts := by
        rw [hBhpts]
        exact ⟨xb, hxb, rfl⟩
      exact ⟨_, _, this, rfl⟩
    · rintro _ ⟨y, hy, rfl⟩
      rw [hBhpts] at hy
      obtain ⟨xb, hxb, rfl⟩ := hy
      refine eq_xhat0_of_c0_eq (hS.ambient.2.1 x₀) ?_
      rw [𝒮.c0_comp_pre_apply]
      have : (T.pre s).composite.base ((𝒮.cBar s).base xb) ∈
          (T.pre s).composite.base '' ((𝒮.cBar s).base '' Bt.pts) := ⟨_, ⟨xb, hxb, rfl⟩, rfl⟩
      rw [himg] at this
      exact this
  obtain ⟨B, ⟨hBirr, hBh, hBpts, e₂, he₂⟩, -⟩ :=
    (hS.bijOn_and_mapsRSOP_and_exists_unique_totalTransform 𝒮.toCompletion s).2.2 Bh hBhirr hx0
  let e : Bt.toScheme ≅ B.toScheme := e₁ ≪≫ e₂
  have he : e.hom ≫ B.ι = Bt.ι ≫ 𝒮.cBar s := by
    show (e₁.hom ≫ e₂.hom) ≫ B.ι = _
    rw [Category.assoc, he₂, ← Category.assoc, he₁, hg, Category.assoc]
    rfl
  have hBns : B.IsNonsingular := isNonsingular_of_iso e.symm hBt
  have hBBpts : B.pts = (𝒮.cBar s).base '' Bt.pts := by
    rw [hBpts, hBhpts, Set.image_image]
    rfl
  exact ⟨B, hBns, hBirr, hBh, ⟨e, he⟩, hBBpts⟩

/-- **Remark 1** (pp. 321–322).  `c_s` inducing an isomorphism `B̃ → B` is an isomorphism of the
subschemes compatible with `c̄_s : X̃ → X_s`.

Deviation from the paper (gap filled): three steps are proved here that the paper only states:
`ν(J̄(s)_{x̂'}) ≥ b̄` on `B̃` (superadditivity of the order); `h_s(c_s(B̃)) = x_0`
(`Frame.image_cBar_eq_singleton`: a finite irreducible set of points of dimension `N` which are
generizations of `x_0`); and that `B̂ = B̃` satisfies the hypotheses of Lemma (CD.3).  Leaves left:
`Frame.cBar_mem_pts_of_closed` (`c_s(X̃) ⊆ F(s)`) and
`Frame.hasOnlyNormalCrossingsWith_eUnion_datum` (`E_1(s) ∪ ⋯ ∪ E_{α+s}(s)` has only normal
crossings with `B`), besides Lemmas (CD.3), (CD.5). -/
@[blueprint "rem:IV.4-1"
  (statement := /-- \textbf{Remark 1.} Notation as in \cref{def:IV.4-conditions},
    \cref{def:IV.4-tilde}, \cref{def:IV.4-case-ge}, in the case $\nu\ge b$. Let $\tilde B$ be a
    non-singular irreducible subscheme of $\tilde X$ such that the monoidal transformation
    $\tilde f$ of $\tilde X$ with center $\tilde B$ is permissible for the resolution datum
    $\mathfrak R^{N-1}_{\mathrm{II}}$ (\cref{def:I.6-II}). Then there exists a non-singular
    irreducible subscheme $B$ of $X_s$ such that $c_s\colon\hat X_s\to X_s$ induces an isomorphism
    of $\tilde B\to B$, and the monoidal transformation $f_s$ of $X_s$ with center $B$ is
    permissible for the resolution datum $\mathfrak R(s)$ (\cref{def:I.6-II},
    \cref{def:I.6-II-closed}). (pp.~321--322.)

    \textbf{Deviation from the paper (statement modified).} The paper presupposes that $\mathfrak R^{N-1}_{\mathrm{II}}$ is a resolution datum (cf.\ \cref{lem:IV.4-tilde-facts}); this is false in general (the $\tilde E_j$ can be reducible). The Lean statement assumes only the clauses of Definition~3 (II) that the proof uses (\texttt{IsWeakDatum}): $\tilde b>0$, the $\tilde E_j$ non-singular and everywhere of codimension~$1$ (not necessarily irreducible), $\tilde E_1\cup\dots\cup\tilde E_{\tilde\alpha}$ with only normal crossings, $\tilde J_x\neq0$. The proof is the paper's and uses no irreducibility of the $\tilde E_j$ (statement generalized). -/)
  (proof := /-- Since $\tilde f$ is permissible for $\mathfrak R^{N-1}_{\mathrm{II}}$,
    $\nu(\bar J(s)_{\hat x'})\ge\bar b$ for all points $\hat x'\in\tilde B$. Hence, by Lemma
    (CD.5) (\cref{lem:IV.CD-5}), $\nu(J(s)_{x'})\ge\nu$ for all $x'\in c_s(\tilde B)$. Since
    $\nu\ge b$, $S_\nu(\mathfrak R^N_{\mathrm{II}}(s))=\{x\in X_s\mid\nu(J(s)_x)\ge\nu\}$. Therefore
    $c_s(\tilde B)\subseteq S_\nu(\mathfrak R^N_{\mathrm{II}}(s))$. This shows, by the assemption
    [sic] [(1)], that $h_s(c_s(\tilde B))=x_0$, or equivalently, $\hat h_s(\tilde B)=\hat x_0$. By
    Lemma (CD.3) (\cref{lem:IV.CD-3}), $B=c_s(\tilde B)$ is an irreducible subscheme of $X_s$ and
    $c_s$ induces an isomorphism $\tilde B\to B$. Since
    $B\subseteq S_\nu(\mathfrak R^N_{\mathrm{II}}(s))=S_*(\mathfrak R^N_{\mathrm{II}}(s))$ and,
    for the case in which
    $\mathfrak R=(\mathfrak R^N_{\mathrm{II}},F)$, $B\subseteq F(s)$ (= the closure of
    $c_s(\tilde X)$ in $X_s$), we have only to prove that $E_1(s)\cup\dots\cup E_{\alpha+s}(s)$
    has only normal crossings with $B$. For the case in which $\mathfrak R=
    (\mathfrak R^N_{\mathrm{II}},F)$, this is clear from the fact that $\tilde E_1\cup\dots\cup
    \tilde E_{\tilde\alpha}$ has only normal crossings with $\tilde B$. For the case in which
    $\mathfrak R=\mathfrak R^N_{\mathrm{II}}$, by the assumption [(2)], $E_i(s)\cap B$ is empty
    for $1\le i\le\alpha$; hence we have only to show that $E_{\alpha+1}(s)\cup\dots\cup
    E_{\alpha+s}(s)$ has only normal crossings with $B$, which is clear from the fact that
    $\tilde E_1\cup\dots\cup\tilde E_{\tilde\alpha}$ has only normal crosssings [sic] with
    $\tilde B$. \textsc{q.e.d.}

    \textbf{Deviation from the paper (gap filled).} Three steps of the proof are stated without
    justification in the paper and are proved in Lean. (a) ``Since $\tilde f$ is permissible for
    $\mathfrak R^{N-1}_{\mathrm{II}}$, $\nu(\bar J(s)_{\hat x'})\ge\bar b$ for all points
    $\hat x'\in\tilde B$'': $\tilde B\subseteq S(\mathfrak R^{N-1}_{\mathrm{II}})$ gives
    $\bar b\le\sum_{\hat x'\in\tilde E_j}\tilde a_j+\nu(\tilde J_{\hat x'})$, and
    $\bar J(s)=\tilde J\cdot\prod_j\tilde P_j^{\tilde a_j}$ has order at least
    $\nu(\tilde J_{\hat x'})+\sum_{\hat x'\in\tilde E_j}\tilde a_j$ by the superadditivity of
    the order (\cref{lem:order-nu-basic}) and $\nu(\tilde P_j)\ge1$ at the points of
    $\tilde E_j$. (b) ``This shows, by the assumption [(1)], that $h_s(c_s(\tilde B))=x_0$'': the
    image of the irreducible $\tilde B$ in the finite set $h_s(S_\nu(\mathfrak R(s)))$ is a
    finite irreducible set, hence has a generic point, all of whose specializations in it have
    dimension $N$ (by [(1)]), so the image is one point $p$; and $p$ is a generization of
    $x_0=c_0(\hat x_0)$ (every point of $\operatorname{Spec}\hat S_0$ specializes to the closed
    point) at which $X$ has dimension $N$, so $p=x_0$ (a proper specialization strictly increases
    the dimension of the local ring). (c) The subscheme $\hat B=\tilde B\subseteq\bar X_s
    \subseteq\hat X_s$ is irreducible and $\hat h_s(\hat B)=\hat x_0$, since the fibre of
    $c_0$ over $x_0$ is $\{\hat x_0\}$; Lemma (CD.3) then gives $B$. (d) That $E_1(s)\cup\dots\cup
    E_{\alpha+s}(s)$ has only normal crossings with $B$ (``clear'' in the paper, from the normal
    crossings of $\tilde E_1\cup\dots\cup\tilde E_{\tilde\alpha}$ with $\tilde B$) is proved by descent
    from $\tilde X$ to $X_s$ at the points of $B$: the stalks of the $E_j(s)$ at $x=\bar c_s(\tilde
    b)$ are generated by members $k$ of a regular system of parameters, whose images generate, up to
    units, distinct members of the regular system of parameters of $\mathcal O_{\tilde X,\tilde b}$
    adapted to $\tilde E\cup\tilde B$ (distinct because the $\hat E_j(s)$ are transversal to $\bar X_s$
    and $c_s$ is faithfully flat at the points over $\hat x_0$); $\bar c_s$ induces an isomorphism
    $\mathcal O_{X,x}/B_x\simeq\mathcal O_{\tilde X,\tilde b}/\tilde B_{\tilde b}$, so the $k\notin B_x$ stay
    independent modulo $B_x$, and there is a regular system of parameters containing the $k$ with a
    part generating $B_x$. Without restriction the $E_i(s)$, $i\le\alpha$, miss $B$ by [(2)]. In the closed case
    $c_s(\tilde X)\subseteq F(s)$ is also proved (\texttt{cBar\_mem\_pts\_of\_closed}). -/)
  (proofUses := ["lem:IV.CD-5", "lem:IV.CD-3", "def:IV.4-conditions", "lem:order-nu-basic"])
  (latexEnv := "remark")]
theorem Frame.exists_isPermissibleCenter_of_isPermissible_datumTilde [Hironaka.HironakaCitedResults.{u}] {hS : Standing N ℜ r ν T x₀} (𝒮 : Frame hS) (s : ℕ)
    (hprep : PrepHyp N ℜ r ν T x₀ s) (hge : ℜ.b ≤ ν)
    (a : Fin (alphaT r ℜ.α s) → ℕ) (Jt : Subscheme (𝒮.xTilde s))
    (hJt : Jt * ∏ j, (𝒮.eTilde s j) ^ (a j) = 𝒮.jBar s)
    (hII : (𝒮.datumTilde s 𝒮.bBar a Jt).IsWeakDatum)
    (Bt : Subscheme (𝒮.xTilde s)) (hBt : Bt.IsNonsingular) (hBti : Bt.IsIrreducible)
    (hperm : (𝒮.datumTilde s 𝒮.bBar a Jt).IsPermissible Bt) :
    ∃ B : Subscheme (T.X s), B.IsNonsingular ∧ B.IsIrreducible ∧
      (Bt.ι ≫ (𝒮.xBar s).ι).ker = Subscheme.totalTransform (𝒮.c s) B ∧
      (∃ e : Bt.toScheme ≅ B.toScheme, e.hom ≫ B.ι = Bt.ι ≫ 𝒮.cBar s) ∧
      (restriction T r s).IsPermissibleCenter (datum T ℜ s) B := by
  classical
  have := 𝒮.regShat
  have hXa := hS.ambient.1
  have h1 : ∀ xb ∈ Bt.pts, (𝒮.cBar s).base xb ∈ (datum T ℜ s).sNu ν ∧
      (ν : ℕ∞) ≤ (datum T ℜ s).nuAt ((𝒮.cBar s).base xb) := fun xb hxb => by
    have := 𝒮.cBar_mem_sNu_of_mem_of_isPermissible hprep hge a Jt hJt Bt hperm hxb
    exact ⟨this.2, this.1⟩
  obtain ⟨B, hBns, hBirr, hBc, ⟨e, he⟩, hBBpts⟩ :=
    𝒮.exists_ker_eq_totalTransform_of_forall_mem_sNu s hprep Bt hBt hBti fun xb hxb => (h1 xb hxb).1
  refine ⟨B, hBns, hBirr, hBc, ⟨e, he⟩, ?_⟩
  have hnu : (datum T ℜ s).nu ≤ ν := by
    have := MonoidalSuccession.nu_transformII_le (T.pre s) hS.ambient.2.1 ℜ hS.isDatum
      (hS.permissible s).isPermissibleII
    exact hS.nu_eq_II ▸ this
  suffices ∀ R : Restriction (T.X s), R = restriction T r s →
      R.IsPermissibleCenter (datum T ℜ s) B from this _ rfl
  intro R hR
  have hP : (datum T ℜ s).IsPermissible B := by
    refine ⟨Or.inr ⟨hBns, hBirr⟩, ?_, ?_⟩
    · rw [hBBpts]
      rintro _ ⟨xb, hxb, rfl⟩
      exact ⟨(h1 xb hxb).1.1, hnu.trans (h1 xb hxb).2⟩
    · exact 𝒮.hasOnlyNormalCrossingsWith_eUnion_datum hprep hge a Jt hJt hII Bt hBt hBti hperm B
        hBc ⟨e, he⟩
  cases R with
  | unrestricted => exact hP
  | closed F' =>
    refine ⟨hP, ?_⟩
    rw [hBBpts]
    rintro _ ⟨xb, hxb, rfl⟩
    exact 𝒮.cBar_mem_pts_of_closed hprep hR.symm xb

/-- p. 322 (the case `ν ≧ b`): "Now, `B̃` and `B` being as in Remark 1, we extend the permissible
succession `h_s` to include the monoidal transformation `f_s : X_{s+1} → X_s` with center `B` and
we replace `X̄_s` by the proper transform `X̄_{s+1}` of `X̄_s` in `X̂_{s+1}`, so that
`f̂_s : X̂_{s+1} → X̂_s` is the monoidal transformation with center `B̃ = c_s⁻¹(B)`.  Then `f̂_s`
induces the monoidal transformation `f̄_s : X̄_{s+1} → X̄_s` with the non-singular irreducible
center `B̃`.  We can easily see that the relation between `ℜ(s+1) = f_s*(ℜ(s))` and
`f̄_s*(ℜ^{N-1}_II)` is the same as that between `ℜ(s)` and `ℜ^{N-1}_II`."

Formalization notes: extending `h_s` by `f_s` is the hypothesis `T.B s = B` on the (arbitrary)
succession of the setup; `B̃ = c_s⁻¹(B)` compares the image of `B̃` in `X̂_s` (the kernel of
`B̃ → X̂_s`) with `c_s⁻¹(B) = B̂_s`; the monoidal transformation `f̄_s` is built from the
universal property; "the same relation" is: `f̄_s*(ℜ^{N-1}_II)` is the datum
`(Ẽ'_1, …, Ẽ'_{α̃+1} | J̃', b̄ | ã_1, …, ã_α̃, ã_{α̃+1})` formed for `s + 1` with
`J̃' ∏ P̃'^{ã_j}_j = J̄(s+1)`.

Deviation from the paper (gap filled): "We can easily see that the relation … is the same" is proved.
(a) The image of `B̃` in `X̂_s` is `B̂_s = c_s⁻¹(B)` (`exists_ker_eq_totalTransform_of_forall_mem_sNu`:
Lemma (CD.3) for `B̂ = B̃`, whose points lie over `x̂_0`, `B = c_s(B̃)` since both are reduced with the
same points), so that `f̄_s` is the monoidal transformation of `X̄_s` with center `B̃`
(`isMonoidalTransformationOf_fBar_of_ker_eq`).  (b) `Ẽ'_j` (formed for `h_{s+1}`) is the strict
transform of `Ẽ_j` and `f̄_s⁻¹(Ẽ_j) = Ẽ'_j · P̄_{s+1}^m` (`m = 1` iff `B ⊆ E_j(s)`;
`eTilde_succ_castSuccT_eq_strictBar`, `stalkIdeal_totalTransform_eTilde`), the new divisor is
`P̄_{s+1}` (`lem:IV.4-Pbar`).  (c) `f̄_s⁻¹(J̄(s)) = J̄(s+1) P̄_{s+1}^{b̄}` and the stalkwise identity of
`prod_eq_of_stalkIdeal_totalTransform_eq` give `J̃' ∏ (P̃'_j)^{ã_j} = J̄(s+1)`, `ν̃` cancelling. -/
@[blueprint "lem:IV.4-case-ge-relation"
  (statement := /-- In the case $\nu\ge b$, let $\tilde B$ and $B$ be as in Remark~1
    (\cref{rem:IV.4-1}). We extend the permissible succession $h_s$ to include the monoidal
    transformation $f_s\colon X_{s+1}\to X_s$ with center $B$, and we replace $\bar X_s$ by the
    proper transform $\bar X_{s+1}$ of $\bar X_s$ in $\hat X_{s+1}$, so that $\hat f_s\colon
    \hat X_{s+1}\to\hat X_s$ is the monoidal transformation with center $\tilde B=c_s^{-1}(B)$.
    Then $\hat f_s$ induces the monoidal transformation $\bar f_s\colon\bar X_{s+1}\to\bar X_s$
    with the non-singular irreducible center $\tilde B$. We can easily see that the relation
    between $\mathfrak R(s+1)=f_s^*(\mathfrak R(s))$ and
    $\bar f_s^*(\mathfrak R^{N-1}_{\mathrm{II}})$ is the same as that between $\mathfrak R(s)$
    and $\mathfrak R^{N-1}_{\mathrm{II}}$
    (\cref{def:IV.4-case-ge}). (p.~322.) (Formalization note (encoding): ``the same relation''
    means that
    $\bar f_s^*(\mathfrak R^{N-1}_{\mathrm{II}})=\big(\tilde E'_1,\dots,\tilde E'_{\tilde\alpha+1}
    \,\big|\,\tilde J',\bar b\,\big|\,\tilde a_1,\dots,\tilde a_{\tilde\alpha},
    \tilde a_{\tilde\alpha+1}\big)$ with the $\tilde E'_j$ formed for $h_{s+1}$ and
    $\tilde J'\prod_j(\tilde P'_j)^{\tilde a_j}=\bar J(s+1)$.)

    \textbf{Deviation from the paper (statement modified).} The paper presupposes that $\mathfrak R^{N-1}_{\mathrm{II}}$ is a resolution datum (cf.\ \cref{lem:IV.4-tilde-facts}); this is false in general (the $\tilde E_j$ can be reducible). The Lean statement assumes only the clauses of Definition~3 (II) that the proof uses (\texttt{IsWeakDatum}): $\tilde b>0$, the $\tilde E_j$ non-singular and everywhere of codimension~$1$ (not necessarily irreducible), $\tilde E_1\cup\dots\cup\tilde E_{\tilde\alpha}$ with only normal crossings, $\tilde J_x\neq0$. The proof is the paper's and uses no irreducibility of the $\tilde E_j$ (statement generalized). -/)
  (proof := /-- $\hat B_s=c_s^{-1}(B)=\tilde B\subseteq\bar X_s$, so by
    \cref{lem:IV.4-construction-facts} $\bar f_s$ is the monoidal transformation of $\bar X_s$ with
    center $\tilde B$. By Definition~7 (II) (\cref{def:I.7-II}) with $\tilde\nu=
    \nu(\mathfrak R^{N-1}_{\mathrm{II}})$, $\bar f_s^*(\mathfrak R^{N-1}_{\mathrm{II}})$ has the
    strict transforms of the $\tilde E_j$, which are the $\tilde E'_j$ (strict transforms commute
    with $c_{s+1}$ and with the restriction to $\bar X_{s+1}$), the total transform
    $\tilde E'_{\tilde\alpha+1}=\bar P_{s+1}$ of $\tilde B$ (\cref{lem:IV.4-Pbar}), and
    $\tilde J'\prod_j(\tilde P'_j)^{\tilde a_j}=\bar f_s^{-1}(\tilde J\prod_j\tilde P_j^{\tilde
    a_j})
    \bar P_{s+1}^{-\bar b}=\bar f_s^{-1}(\bar J(s))\bar P_{s+1}^{-\bar b}=\bar J(s+1)$, exactly as
    in the proof of Remark~3 (\cref{rem:IV.4-3}).

    \textbf{Deviation from the paper (gap filled).} ``We can easily see'' is proved. The image of
    $\tilde B$ in $\hat X_s$ is $\hat B_s=c_s^{-1}(B)$ (Lemma (CD.3) for $\hat B=\tilde B$, whose points
    lie over $\hat x_0$, and $B=c_s(\tilde B)$ since both are reduced with the same points);
    $\tilde E'_j$ is the strict transform of $\tilde E_j$ and $\bar f_s^{-1}(\tilde E_j)=\tilde E'_j
    \bar P_{s+1}^{m_j}$ ($m_j=1$ iff $B\subseteq E_j(s)$), by the chart of p.~169 and the flat base change
    $c_{s+1}$; $\bar f_s^{-1}(\bar J(s))=\bar J(s+1)\bar P_{s+1}^{\bar b}$; the exponent $\tilde\nu$ cancels. -/)
  (proofUses := ["rem:IV.4-1", "lem:IV.4-construction-facts", "lem:IV.4-Pbar", "def:I.7-II",
    "lem:IV.4-exceptional-transversal-nonsingular"])
  (latexEnv := "lemma")]
theorem Frame.ker_eq_B_and_exists_transform_eq_datumTilde_of_ge [Hironaka.HironakaCitedResults.{u}] {hS : Standing N ℜ r ν T x₀} (𝒮 : Frame hS) (s : ℕ)
    (hprep : PrepHyp N ℜ r ν T x₀ s) (hge : ℜ.b ≤ ν)
    (a : Fin (alphaT r ℜ.α s) → ℕ) (Jt : Subscheme (𝒮.xTilde s))
    (hJt : Jt * ∏ j, (𝒮.eTilde s j) ^ (a j) = 𝒮.jBar s)
    (hII : (𝒮.datumTilde s 𝒮.bBar a Jt).IsWeakDatum)
    (Bt : Subscheme (𝒮.xTilde s)) (hBt : Bt.IsNonsingular) (hBti : Bt.IsIrreducible)
    (hperm : (𝒮.datumTilde s 𝒮.bBar a Jt).IsPermissible Bt)
    (B : Subscheme (T.X s)) (hB : B.IsNonsingular ∧ B.IsIrreducible)
    (hBe : ∃ e : Bt.toScheme ≅ B.toScheme, e.hom ≫ B.ι = Bt.ι ≫ 𝒮.cBar s)
    (hBperm : (restriction T r s).IsPermissibleCenter (datum T ℜ s) B) (hTB : T.B s = B) :
    (Bt.ι ≫ (𝒮.xBar s).ι).ker = 𝒮.tHat.B s ∧
    ∃ h : AB.IsMonoidalTransformationOf (𝒮.fBar s) Bt,
      ∃ (anew : ℕ) (Jt' : Subscheme (𝒮.xTilde (s + 1))),
        (𝒮.datumTilde s 𝒮.bBar a Jt).transform
            (⟨_, 𝒮.fBar s, h.1, h.2⟩ : MonoidalTransformation (𝒮.xTilde s) Bt) =
          𝒮.datumTilde (s + 1) 𝒮.bBar (extendA a anew) Jt' ∧
        Jt' * ∏ j, (𝒮.eTilde (s + 1) j) ^ (extendA a anew j) = 𝒮.jBar (s + 1) := by
  classical
  have hadm := 𝒮.isAdmissibleAt_of_prepHyp hprep
  -- `B̃ = c_s⁻¹(B₀)` for an irreducible non-singular `B₀` (Remark 1, Lemma (CD.3))
  have h1 : ∀ xb ∈ Bt.pts, (𝒮.cBar s).base xb ∈ (datum T ℜ s).sNu ν := fun xb hxb =>
    (𝒮.cBar_mem_sNu_of_mem_of_isPermissible hprep hge a Jt hJt Bt hperm hxb).2
  obtain ⟨B₀, hB₀ns, hB₀irr, hker₀, hiso₀, hpts₀⟩ :=
    𝒮.exists_ker_eq_totalTransform_of_forall_mem_sNu s hprep Bt hBt hBti h1
  -- `B = B₀`: both are reduced with the points `c̄_s(B̃)`
  have hBeq : B = B₀ := AB.eq_of_isReduced_of_pts_eq
    (Hironaka.DatumTransform.isReduced_of_isNonsingular hB.1)
    (Hironaka.DatumTransform.isReduced_of_isNonsingular hB₀ns)
    ((pts_eq_image_cBar_of_iso hBe).trans hpts₀.symm)
  subst hBeq
  have hd : 𝒮.CenterData s Bt B := ⟨hBt, hBti, hB.1, hB.2, hker₀, hBe, hBperm, hTB⟩
  have h := 𝒮.isMonoidalTransformationOf_fBar_of_ker_eq s hd.ker_eq_B
  refine ⟨hd.ker_eq_B, h, ((𝒮.datumTilde s 𝒮.bBar a Jt).transform (𝒮.tBar s h)).a (Fin.last _),
    ((𝒮.datumTilde s 𝒮.bBar a Jt).transform (𝒮.tBar s h)).J,
    Frame.transform_datumTilde_eq hadm hd hII hperm h, ?_⟩
  refine Frame.prod_eq_of_stalkIdeal_totalTransform_eq hadm hd hII hperm h _ (fun yb => ?_)
  rw [hJt, Frame.stalkIdeal_totalTransform_jBar hadm yb, mul_comm]

/-! ### Remark 2 (pp. 323–324): the set `S(ℜ^{N-1}_II)` and the descent of the center `B̃`

The order calculus in the regular local rings `O_{X̃,x̂}` behind "this is clear from the definition of
`J̄*(s)` and the fact that all the `Ẽ_j` are non-singular" (p. 323), the bijection `S(ℜ^{N-1}_II) →
S_ν(ℜ(s)) ∩ h_s⁻¹(x_0)` induced by `c̄_s` (Lemma (CD.3), the Corollary of Lemma (CD.4), Lemma (CD.5),
`[(1)]`, `[(2)]`), and the existence and uniqueness of the center `B_s`.

Deviation from the paper (gap filled): the paper says "this is clear" (p. 323) for
`S(ℜ^{N-1}_II) = {x ∈ X̃ | ν(J̄*(s)_x) ≥ b̃}` and for the equivalence of `ν(J̄*(s)_x̂) ≥ b̃` with (a) and
(b); the proofs use the additivity of the order in a regular local ring, `ν(I·(u)) = ν(I) + ν(u)` and
`ν(J^k) ≤ kν(J)` (`gr_M(R)` is a domain; `Ideal.nu_mul_span_singleton`, `Ideal.nu_pow_le`), and that
the stalk of each `Ẽ_j` is generated by an element of order `1`. -/

theorem sum_idxT_le_sum_univ {α s : ℕ} (r : Restriction X) (F : Fin (α + s) → ℕ) :
    ∑ j : Fin (alphaT r α s), F (idxT α s r j) ≤ ∑ i, F i := by
  cases r with
  | closed F' => exact le_of_eq rfl
  | unrestricted =>
    rw [Fin.sum_univ_add]
    exact le_add_self.trans' le_rfl

open Classical in
/-- The weight of a point of `X_s` for `ℜ(s)`, as a sum over `Fin (α + s)`. -/
theorem weight_datum_eq_sum (T : AB.Tower X) (ℜ : DatumII.Raw X) (s : ℕ) (y : T.X s) :
    (datum T ℜ s).weight y =
      ∑ i : Fin (ℜ.α + s), if y ∈ (eSeq T ℜ s i).pts then aSeq T ℜ s i else 0 := by
  unfold DatumII.Raw.weight
  rw [Finset.sum_filter]
  exact (Fintype.sum_equiv (finCongr (alpha_datum T ℜ s).symm) _ _ (fun i => rfl)).symm

namespace Frame

variable {hS : Standing N ℜ r ν T x₀} {𝒮 : Frame hS}

/-- The stalks of the non-singular divisors `Ẽ_j` of a resolution datum `ℜ̃` are generated by one
element of order `1` (a member of a regular system of parameters), or are the unit ideal. -/
theorem exists_stalkIdeal_eTilde {s : ℕ} (hadm : 𝒮.IsAdmissibleAt s) {bt : ℕ}
    {a : Fin (alphaT r ℜ.α s) → ℕ} {Jt : Subscheme (𝒮.xTilde s)}
    (hII : (𝒮.datumTilde s bt a Jt).IsWeakDatum) (j : Fin (alphaT r ℜ.α s)) (x : 𝒮.xTilde s) :
    (𝒮.eTilde s j).stalkIdeal x = ⊤ ∨
      ∃ p, Ideal.ordElem (maximalIdeal ((𝒮.xTilde s).presheaf.stalk x)) p = 1 ∧
        (𝒮.eTilde s j).stalkIdeal x = Ideal.span {p} := by
  classical
  have hreg : IsRegularLocalRing ((𝒮.xTilde s).presheaf.stalk x) := hadm.1.1 x
  obtain ⟨Z, hZ, -, hE'⟩ := Hironaka.DatumTransform.exists_rsop_adapted_of_isNonsingularDivisor (B := ⊥)
    (𝒮.eTilde s) hadm.1.1 hII.2.1 hII.2.2.1 (fun y _ => hII.2.2.1 y) x
  rcases hE' j with h | ⟨p, hpZ, hp⟩
  · exact Or.inl h
  · refine Or.inr ⟨p, ?_, hp⟩
    have hpM : p ∈ maximalIdeal ((𝒮.xTilde s).presheaf.stalk x) := hZ.1 ▸ Ideal.subset_span hpZ
    have hp2 : p ∉ maximalIdeal ((𝒮.xTilde s).presheaf.stalk x) ^ 2 := fun h2 =>
      rsop_notMem_span_erase_sup_sq hZ hpZ (Ideal.mem_sup_right h2)
    exact Ideal.ordElem_eq_one_of_mem_of_notMem_sq (maximalIdeal.isMaximal _).ne_top hpM hp2

open Classical in
/-- The product `∏_j (P̃_j)_x^{e_j}` of the stalks is generated by one element, of order
`∑_{x ∈ Ẽ_j} e_j` (the `Ẽ_j` are non-singular divisors). -/
theorem exists_prod_stalkIdeal_eTilde_eq_span {s : ℕ} (hadm : 𝒮.IsAdmissibleAt s) {bt : ℕ}
    {a : Fin (alphaT r ℜ.α s) → ℕ} {Jt : Subscheme (𝒮.xTilde s)}
    (hII : (𝒮.datumTilde s bt a Jt).IsWeakDatum) (e : Fin (alphaT r ℜ.α s) → ℕ) (x : 𝒮.xTilde s) :
    ∃ u, (∏ j, ((𝒮.eTilde s j).stalkIdeal x) ^ (e j)) = Ideal.span {u} ∧
      Ideal.ordElem (maximalIdeal ((𝒮.xTilde s).presheaf.stalk x)) u =
        ((∑ j ∈ Finset.univ.filter fun j => x ∈ (𝒮.eTilde s j).pts, e j : ℕ) : ℕ∞) := by
  have hreg : IsRegularLocalRing ((𝒮.xTilde s).presheaf.stalk x) := hadm.1.1 x
  suffices h : ∀ t : Finset (Fin (alphaT r ℜ.α s)), ∃ u,
      (∏ j ∈ t, ((𝒮.eTilde s j).stalkIdeal x) ^ (e j)) = Ideal.span {u} ∧
        Ideal.ordElem (maximalIdeal ((𝒮.xTilde s).presheaf.stalk x)) u =
          ((∑ j ∈ t.filter fun j => x ∈ (𝒮.eTilde s j).pts, e j : ℕ) : ℕ∞) from h Finset.univ
  intro t
  induction t using Finset.induction_on with
  | empty =>
    refine ⟨1, by simp [Ideal.span_singleton_one], ?_⟩
    simp [Ideal.ordElem_eq_zero_of_isUnit isUnit_one]
  | insert j t hj ih =>
    obtain ⟨u, hu, hou⟩ := ih
    rcases exists_stalkIdeal_eTilde hadm hII j x with htop | ⟨p, hop, hp⟩
    · refine ⟨u, ?_, ?_⟩
      · rw [Finset.prod_insert hj, htop, Ideal.top_pow, hu, Ideal.top_mul]
      · have hx : x ∉ (𝒮.eTilde s j).pts := fun hx =>
          Subscheme.mem_pts_iff_stalkIdeal_ne_top.mp hx htop
        rw [Finset.filter_insert, ite_eq_right hx]; exact hou
    · have hpnu : ¬ IsUnit p := by
        intro hunit
        have := Ideal.ordElem_eq_zero_of_isUnit hunit
        rw [hop] at this
        exact one_ne_zero this
      have hx : x ∈ (𝒮.eTilde s j).pts := by
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
/-- **`b̃ ≤ ν(J̄*(s)_x)` iff `(a)` and `(b)`** (p. 323: "`x̂ ∈ S(ℜ^{N-1}_II)` if and only if (a)
`ν(J̄(s)_x̂) ≥ b̄`, and (b) `∑_{x̂ ∈ Ẽ_j} c_j ≥ b − ν`; this is clear from the definition of `J̄*(s)`
and the fact that all the `Ẽ_j` are non-singular"): by additivity of the order in the regular local
ring `O_{X̃,x̂}`. -/
theorem le_nu_jBarStar_iff {s : ℕ} (hadm : 𝒮.IsAdmissibleAt s) (hlt : ν < ℜ.b) {bt : ℕ}
    {a : Fin (alphaT r ℜ.α s) → ℕ} {Jt : Subscheme (𝒮.xTilde s)}
    (hII : (𝒮.datumTilde s bt a Jt).IsWeakDatum) (x : 𝒮.xTilde s) :
    ((𝒮.bBar * (ℜ.b - ν) : ℕ) : ℕ∞) ≤ Ideal.nu ((𝒮.jBarStar s).stalkIdeal x) ↔
      ((𝒮.bBar : ℕ) : ℕ∞) ≤ Ideal.nu ((𝒮.jBar s).stalkIdeal x) ∧
        ℜ.b - ν ≤ ∑ j ∈ Finset.univ.filter fun j => x ∈ (𝒮.eTilde s j).pts, cT T ℜ r s j := by
  have hreg : IsRegularLocalRing ((𝒮.xTilde s).presheaf.stalk x) := hadm.1.1 x
  obtain ⟨u, hu, hou⟩ := exists_prod_stalkIdeal_eTilde_eq_span hadm hII (cT T ℜ r s) x
  set M := maximalIdeal ((𝒮.xTilde s).presheaf.stalk x) with hM
  set k := ℜ.b - ν with hk
  have hk1 : 1 ≤ k := by omega
  have hb1 : 1 ≤ 𝒮.bBar := Nat.factorial_pos ν
  set w := ∑ j ∈ Finset.univ.filter fun j => x ∈ (𝒮.eTilde s j).pts, cT T ℜ r s j with hw
  have hst : (𝒮.jBarStar s).stalkIdeal x =
      ((𝒮.jBar s).stalkIdeal x) ^ k ⊔ (Ideal.span {u ^ 𝒮.bBar}) := by
    unfold jBarStar
    rw [Scheme.IdealSheafData.add_eq_sup, Subscheme.stalkIdeal_sup_eq, Subscheme.stalkIdeal_pow_eq,
      Subscheme.stalkIdeal_pow_eq, stalkIdeal_prod_eq, ← Ideal.span_singleton_pow]
    simp only [Subscheme.stalkIdeal_pow_eq]
    rw [hu]
  have hiff : ∀ (n : ℕ) (I K : Ideal ((𝒮.xTilde s).presheaf.stalk x)),
      (n : ℕ∞) ≤ Ideal.nu (I ⊔ K) ↔ (n : ℕ∞) ≤ Ideal.nu I ∧ (n : ℕ∞) ≤ Ideal.nu K := by
    intro n I K
    constructor
    · intro h
      have h1 := Ideal.le_pow_of_le_ord h
      exact ⟨Ideal.le_ord (le_sup_left.trans h1), Ideal.le_ord (le_sup_right.trans h1)⟩
    · rintro ⟨h1, h2⟩
      exact Ideal.le_ord (sup_le (Ideal.le_pow_of_le_ord h1) (Ideal.le_pow_of_le_ord h2))
  rw [hst, hiff]
  have hK : ((𝒮.bBar * k : ℕ) : ℕ∞) ≤ Ideal.nu (Ideal.span {u ^ 𝒮.bBar}) ↔ k ≤ w := by
    rw [Ideal.nu, Ideal.ord_span_singleton, StableOrder.ordElem_pow_maximalIdeal, hou]
    have : ((𝒮.bBar : ℕ) : ℕ∞) * ((w : ℕ) : ℕ∞) = ((𝒮.bBar * w : ℕ) : ℕ∞) := by push_cast; ring
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

open Classical in
/-- **`S(ℜ^{N-1}_II) = {x ∈ X̃ | ν(J̄*(s)_x) ≥ b̃}`** (p. 323: "This is clear from Definitions of
Ch. I"): `ν(J̃_x ∏ (P̃_j)_x^{ã_j}) = ν(J̃_x) + ∑_{x ∈ Ẽ_j} ã_j`, the `Ẽ_j` being non-singular. -/
theorem S_datumTilde_eq_of_jBarStar {s : ℕ} (hadm : 𝒮.IsAdmissibleAt s) {bt : ℕ}
    {a : Fin (alphaT r ℜ.α s) → ℕ} {Jt : Subscheme (𝒮.xTilde s)}
    (hII : (𝒮.datumTilde s bt a Jt).IsWeakDatum) (K : Subscheme (𝒮.xTilde s))
    (hJt : Jt * ∏ j, (𝒮.eTilde s j) ^ (a j) = K) :
    (𝒮.datumTilde s bt a Jt).S = {x | (bt : ℕ∞) ≤ Ideal.nu (K.stalkIdeal x)} := by
  ext x
  have hreg : IsRegularLocalRing ((𝒮.xTilde s).presheaf.stalk x) := hadm.1.1 x
  obtain ⟨u, hu, hou⟩ := exists_prod_stalkIdeal_eTilde_eq_span hadm hII a x
  have hst : K.stalkIdeal x = (Jt.stalkIdeal x) * Ideal.span {u} := by
    rw [← hJt, Subscheme.stalkIdeal_mul_eq, stalkIdeal_prod_eq, ← hu]
    simp only [Subscheme.stalkIdeal_pow_eq]
  have hnu : Ideal.nu (K.stalkIdeal x) = Ideal.nu (Jt.stalkIdeal x) +
      ((∑ j ∈ Finset.univ.filter fun j => x ∈ (𝒮.eTilde s j).pts, a j : ℕ) : ℕ∞) := by
    rw [hst, Ideal.nu_mul_span_singleton, hou]
  show (bt : ℕ∞) ≤ ((∑ j ∈ Finset.univ.filter fun j => x ∈ (𝒮.eTilde s j).pts, a j : ℕ) : ℕ∞) +
    Ideal.nu (Jt.stalkIdeal x) ↔ (bt : ℕ∞) ≤ Ideal.nu (K.stalkIdeal x)
  rw [hnu, add_comm]

/-- A point `x̂'` of `X̃` going into `S_ν(ℜ(s))` under `c̄_s` goes to `x_0` under `h_s ∘ c̄_s`
(the pointwise form of `image_cBar_eq_singleton`, by `[(1)]`). -/
theorem hBar_cBar_eq_of_mem_sNu {s : ℕ} (hprep : PrepHyp N ℜ r ν T x₀ s) (xb : 𝒮.xTilde s)
    (hxb : (𝒮.cBar s).base xb ∈ sNu (datum T ℜ s) (restriction T r s) ν) :
    (T.pre s).composite.base ((𝒮.cBar s).base xb) = x₀ := by
  have := 𝒮.regShat
  have hpS : (T.pre s).composite.base ((𝒮.cBar s).base xb) ∈
      (T.pre s).composite.base '' sNu (datum T ℜ s) (restriction T r s) ν := ⟨_, hxb, rfl⟩
  have hdimp := hprep.2.1 _ hpS
  have hdx : X.dimAt x₀ = (N : WithBot ℕ∞) := hprep.2.1 _ hprep.2.2.2
  have hpx : (T.pre s).composite.base ((𝒮.cBar s).base xb) ⤳ x₀ := by
    have h1 : ((𝒮.tHat.pre s).composite.base ((𝒮.xBar s).ι.base xb)) ⤳ hS.xh := by
      exact (PrimeSpectrum.le_iff_specializes (R := AB.Shat X x₀) _ _).mp
        (IsLocalRing.le_maximalIdeal
          ((𝒮.tHat.pre s).composite.base ((𝒮.xBar s).ι.base xb) :
            PrimeSpectrum (AB.Shat X x₀)).isPrime.ne_top)
    have h2 := h1.map (AB.c0 X x₀).continuous
    rw [Standing.xh, c0_xhat0] at h2
    have hGeq : (T.pre s).composite.base ((𝒮.cBar s).base xb) =
        (AB.c0 X x₀).base ((𝒮.tHat.pre s).composite.base ((𝒮.xBar s).ι.base xb)) := by
      rw [𝒮.c0_comp_pre_apply]
      rfl
    rw [hGeq]
    exact h2
  exact eq_of_specializes_of_dimAt_eq hpx hdimp hdx

/-- A point of `X̃` over `x_0` (under `h_s ∘ c̄_s`) lies over `x̂_0` under `ĥ_s`. -/
theorem hHat_eq_xh_of_hBar_eq {s : ℕ} (xb : 𝒮.xTilde s)
    (h : (T.pre s).composite.base ((𝒮.cBar s).base xb) = x₀) :
    (𝒮.tHat.pre s).composite.base ((𝒮.xBar s).ι.base xb) = hS.xh := by
  refine eq_xhat0_of_c0_eq (hS.ambient.2.1 x₀) ?_
  rw [𝒮.c0_comp_pre_apply]
  exact h

open Classical in
/-- `∑_{x̂ ∈ Ẽ_j} c_j ≤ weight_{ℜ(s)}(c̄_s(x̂))`. -/
theorem weightC_le_weight_cBar {s : ℕ} (xb : 𝒮.xTilde s) :
    (∑ j ∈ Finset.univ.filter fun j => xb ∈ (𝒮.eTilde s j).pts, cT T ℜ r s j) ≤
      (datum T ℜ s).weight ((𝒮.cBar s).base xb) := by
  rw [weight_datum_eq_sum]
  refine le_trans (le_of_eq ?_) (sum_idxT_le_sum_univ r _)
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl fun j _ => ?_
  have : xb ∈ (𝒮.eTilde s j).pts ↔ (𝒮.cBar s).base xb ∈ (eSeq T ℜ s (idxT ℜ.α s r j)).pts := by
    rw [𝒮.pts_eTilde s j]; rfl
  simp only [this]
  rfl

open Classical in
/-- **`c̄_s` maps `S(ℜ^{N-1}_II)` into `S_ν(ℜ(s)) ∩ h_s⁻¹(x_0)`** (p. 323: "By Lemma (CD.5), (a)
implies `ν(J(s)_x) ≥ ν`, and (b) implies `∑_{x ∈ E_j(s)} a_j ≥ b − ν`; therefore
`x ∈ S_ν(ℜ^N_II(s))`, and in the closed case `x ∈ F(s)`; and `[(1)]` gives `x ∈ h_s⁻¹(x_0)`"). -/
theorem cBar_mem_sNu_and_hBar_eq_of_mem_S [Hironaka.HironakaCitedResults.{u}] {s : ℕ} (hprep : PrepHyp N ℜ r ν T x₀ s)
    (hlt : ν < ℜ.b) {a : Fin (alphaT r ℜ.α s) → ℕ} {Jt : Subscheme (𝒮.xTilde s)}
    (hII : (𝒮.datumTilde s (𝒮.bBar * (ℜ.b - ν)) a Jt).IsWeakDatum)
    (hJt : Jt * ∏ j, (𝒮.eTilde s j) ^ (a j) = 𝒮.jBarStar s) {xb : 𝒮.xTilde s}
    (hxb : xb ∈ (𝒮.datumTilde s (𝒮.bBar * (ℜ.b - ν)) a Jt).S) :
    (𝒮.cBar s).base xb ∈ (datum T ℜ s).sNu ν ∧
      (𝒮.cBar s).base xb ∈ sNu (datum T ℜ s) (restriction T r s) ν ∧
      (T.pre s).composite.base ((𝒮.cBar s).base xb) = x₀ := by
  have hadm := 𝒮.isAdmissibleAt_of_prepHyp hprep
  rw [𝒮.S_datumTilde_eq_of_jBarStar hadm hII _ hJt] at hxb
  obtain ⟨ha, hb⟩ := (𝒮.le_nu_jBarStar_iff hadm hlt hII xb).mp hxb
  have hν : (ν : ℕ∞) ≤ (datum T ℜ s).nuAt ((𝒮.cBar s).base xb) :=
    𝒮.le_nuAt_cBar_of_bBar_le_nu s hadm.2.2.1 xb ha
  have hw := 𝒮.weightC_le_weight_cBar xb
  have hS : (𝒮.cBar s).base xb ∈ (datum T ℜ s).S := by
    show ((datum T ℜ s).b : ℕ∞) ≤ ((datum T ℜ s).weight ((𝒮.cBar s).base xb) : ℕ∞) +
      (datum T ℜ s).nuAt ((𝒮.cBar s).base xb)
    rw [b_datum]
    have h1 : (ℜ.b : ℕ∞) = (ν : ℕ∞) + ((ℜ.b - ν : ℕ) : ℕ∞) := by
      rw [← Nat.cast_add]; congr 1; omega
    rw [h1, add_comm]
    exact add_le_add (by exact_mod_cast hb.trans hw) hν
  have hsN : (𝒮.cBar s).base xb ∈ (datum T ℜ s).sNu ν := ⟨hS, hν⟩
  have hsN' : (𝒮.cBar s).base xb ∈ sNu (datum T ℜ s) (restriction T r s) ν :=
    mem_sNu_of_mem_sNu_of_forall_closed _ hsN fun F hF => 𝒮.cBar_mem_pts_of_closed hprep hF xb
  exact ⟨hsN, hsN', 𝒮.hBar_cBar_eq_of_mem_sNu hprep xb hsN'⟩

open Classical in
/-- Under `[(2)]`, the weight of a point `c̄_s(x̂)` of `S_ν(ℜ(s))` for `ℜ(s)` is `∑_{x̂ ∈ Ẽ_j} c_j`. -/
theorem weight_cBar_eq_weightC {s : ℕ} (hprep : PrepHyp N ℜ r ν T x₀ s) (xb : 𝒮.xTilde s)
    (hxb : (𝒮.cBar s).base xb ∈ sNu (datum T ℜ s) (restriction T r s) ν) :
    (datum T ℜ s).weight ((𝒮.cBar s).base xb) =
      ∑ j ∈ Finset.univ.filter fun j => xb ∈ (𝒮.eTilde s j).pts, cT T ℜ r s j := by
  rw [weight_datum_eq_sum]
  rw [sum_univ_eq_sum_idxT r _ (fun hr i => ?_), Finset.sum_filter]
  · refine Finset.sum_congr rfl fun j _ => ?_
    have : xb ∈ (𝒮.eTilde s j).pts ↔ (𝒮.cBar s).base xb ∈ (eSeq T ℜ s (idxT ℜ.α s r j)).pts := by
      rw [𝒮.pts_eTilde s j]; rfl
    simp only [this]
    rfl
  · have h0 := hprep.2.2.1 hr i
    have hnot : (𝒮.cBar s).base xb ∉ (eSeq T ℜ s (Fin.castAdd s i)).pts := fun hmem =>
      (Set.eq_empty_iff_forall_notMem.mp h0) _ ⟨hmem, hxb⟩
    simp [hnot]

open Classical in
/-- **`c̄_s : S(ℜ^{N-1}_II) → S_ν(ℜ(s)) ∩ h_s⁻¹(x_0)` is a bijection** (p. 323: "Conversely, for
`x ∈ S_ν(ℜ(s)) ∩ h_s⁻¹(x_0)`, Lemma (CD.3) gives a unique `x̂` with `c_s(x̂) = x`, and the Corollary
of Lemma (CD.4) gives `x̂ ∈ X̃` and (a).  Since `ν = ν(ℜ) ≥ ν(ℜ(s))`, `ν(J(s)_x) = ν`, so
`ν + ∑_{x ∈ E_j(s)} a_j ≥ b`, and (b) follows (in the unrestricted case using [(2)])"). -/
theorem bijOn_cBar_S [Hironaka.HironakaCitedResults.{u}] {s : ℕ} (hprep : PrepHyp N ℜ r ν T x₀ s)
    (hlt : ν < ℜ.b) {a : Fin (alphaT r ℜ.α s) → ℕ} {Jt : Subscheme (𝒮.xTilde s)}
    (hII : (𝒮.datumTilde s (𝒮.bBar * (ℜ.b - ν)) a Jt).IsWeakDatum)
    (hJt : Jt * ∏ j, (𝒮.eTilde s j) ^ (a j) = 𝒮.jBarStar s) :
    Set.BijOn (𝒮.cBar s).base (𝒮.datumTilde s (𝒮.bBar * (ℜ.b - ν)) a Jt).S
      (sNu (datum T ℜ s) (restriction T r s) ν ∩ (T.pre s).composite.base ⁻¹' {x₀}) := by
  have hadm := 𝒮.isAdmissibleAt_of_prepHyp hprep
  have hCD3 := (hS.bijOn_and_mapsRSOP_and_exists_unique_totalTransform 𝒮.toCompletion s).1
  refine ⟨fun xb hxb => ?_, fun xb hxb xb' hxb' hEq => ?_, fun x hx => ?_⟩
  · obtain ⟨-, h2, h3⟩ := 𝒮.cBar_mem_sNu_and_hBar_eq_of_mem_S hprep hlt hII hJt hxb
    exact ⟨h2, h3⟩
  · obtain ⟨-, -, h3⟩ := 𝒮.cBar_mem_sNu_and_hBar_eq_of_mem_S hprep hlt hII hJt hxb
    obtain ⟨-, -, h3'⟩ := 𝒮.cBar_mem_sNu_and_hBar_eq_of_mem_S hprep hlt hII hJt hxb'
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
    rw [𝒮.S_datumTilde_eq_of_jBarStar hadm hII _ hJt]
    refine (𝒮.le_nu_jBarStar_iff hadm hlt hII xb).mpr ⟨hbar, ?_⟩
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

/-! ## The case `ν < b`: Remarks 2 and 3 (pp. 322–326) -/

/-- **Remark 2** (pp. 323–324).  "`B̃ = c_s⁻¹(B_s)`" compares the image of `B̃` in `X̂_s` (the
kernel of `B̃ → X̂_s`) with `c_s⁻¹(B_s)`; the bijection `S(ℜ^{N-1}_II) → S_ν(ℜ(s)) ∩ h_s⁻¹(x_0)` is
induced by `c̄_s`.

Deviation from the paper (gap filled): "this is clear from the definition of `J̄*(s)` and the fact that
all the `Ẽ_j` are non-singular" (p. 323) is proved with the additivity of the order in the regular
local rings `O_{X̃,x̂}` (`le_nu_jBarStar_iff`, `S_datumTilde_eq_of_jBarStar`); the bijection is
`bijOn_cBar_S` (Lemmas (CD.3), (CD.5), the Corollary of (CD.4), `[(1)]`, `[(2)]`), the center
`B_s` is `exists_ker_eq_totalTransform_of_forall_mem_sNu` (as in Remark 1) and its permissibility is
`hasOnlyNormalCrossingsWith_eUnion_datum_of_forall_mem_sNu`.  An irreducible `B̃` is non-empty.

\textbf{Error of the paper: `J̄*(s)` and this Remark when `F = E_i`.}  In the closed case Definition 5
(II.1) (p. 166) allows `F = E_i`; then `Ẽ_i = X̃`, so `P̃_i = (0)`.  If moreover `c_i = a_i > 0`, the second
generator `(∏ P̃_j^{c_j})^{b̄}` of the printed `J̄*(s)` (p. 322) vanishes, condition (b) of the proof is
lost, and `S(ℜ^{N-1}_II)` is strictly larger than the set of points satisfying (a) and (b); the
bijection of this Remark fails.  Counterexample: `k` algebraically closed of characteristic 0,
`X = 𝔸³_k` with coordinates `(x, y, w)`, `x₀` the origin, and
`ℜ = (V(x), V(w) | (x² + y²), 4 | 1, 1)` with closed restriction `F = V(x) = E₁`
(`V(x) ∪ V(w)` has normal crossings).  Since `x² + y² = (x + iy)(x − iy)`, `ν_p(J) = 2` exactly on the
`w`-axis `L = {x = y = 0}`; on `F` the weight is `1 + [w = 0]`; hence `S(ℜ) = {x₀}` (value 4 at `x₀`,
3 elsewhere on `L`), `ν = 2 < b = 4`, `S_ν(ℜ) = {x₀}` has no component of codimension 1, and [(1)] holds
with `s = 0`.  The frame is `z₀ = x`, `T₀ = k[[y, w]]`, `g₁ = z₀² + y²`, `b̄ = 2`, `J̄(0) = (y²)` on
`X̃ = X̄₀ = Spec k[[y, w]]`.  Here `Ẽ₁ = X̃`, `Ẽ₂ = V(w)`, `c = (1, 1)`.  The printed
`J̄*(0) = ((y²)², (0 · w)²) = (y⁴)` and `b̃ = 4`, so `S(ℜ^{N-1}_II) = V(y)`, the formal `w`-axis, whereas
only `x̂₀` satisfies (a) and (b).  The generic point of `V(y)` maps to the generic point of `L`, which is
neither in `S_ν(ℜ) = {x₀}` nor over `x₀`: the bijection fails.  The center `B̃ = V(y)` is permissible
for the datum (with `Ẽ₁` dropped), but the closure of its image is `L ⊄ S_ν(ℜ)`, so it does not lift to a
permissible center (the last assertion fails).  Keeping the printed formula but emptying `Ẽ₁` gives
`(y⁴, w²)`, whose `S` is empty although `S_ν(ℜ) ∩ h₀⁻¹(x₀) = {x₀}`: the bijection fails the other way.
The exponents `c_j` are those of `ℜ` and cannot be changed, so the defect goes into the threshold: with
`δ = 1` (the weight of the dropped trace) and `d = b − ν − δ = 1` one takes `J̃ = (y², w²)`, `b̃ = 2`, and
`S(ℜ^{N-1}_II) = {x̂₀}` as it should be (`rem:IV.4-2-repaired`).  For `F ≠ E_i` the Remark is as printed. -/
@[blueprint "rem:IV.4-2"
  (statement := /-- \textbf{Remark 2.} Notation as in \cref{def:IV.4-conditions},
    \cref{def:IV.4-tilde}, \cref{def:IV.4-case-lt}, in the case $\nu<b$. We have
    $S(\mathfrak R^{N-1}_{\mathrm{II}})=\{x\in\tilde X\mid\nu(\bar J^*(s)_x)\ge\tilde b\}$. (This is
    clear from Definitions of Ch.~I.) The morphism $c_s\colon\hat X_s\to X_s$ induces a bijection
    $S(\mathfrak R^{N-1}_{\mathrm{II}})\to S_\nu(\mathfrak R(s))\cap h_s^{-1}(x_0)$. Moreover, if
    $\tilde B$ is any non-singular irreducible subscheme of $\tilde X$ such that the monoidal
    transformation $\tilde f\colon\tilde X'\to\tilde X$ with center $\tilde B$ is permissible for
    $\mathfrak R^{N-1}_{\mathrm{II}}$, then there exists a unique non-singular irreducible
    subscheme $B_s$ of $X_s$ such that $\tilde B=c_s^{-1}(B_s)$, that $c_s$ induces an
    isomorphism $\tilde B\to B_s$ and that the monoidal transformation $f_s\colon X_{s+1}\to X_s$
    with center $B_s$ is permissible for $\mathfrak R(s)$. (p.~323.)

    \textbf{Error of the paper ($F=E_i$).} In the closed case Definition~5 (II.1) (p.~166) allows
    $F=E_i$; then $\tilde E_i=\tilde X$, so $\tilde P_i=(0)$. If moreover $c_i=a_i>0$, the second
    generator $(\prod_j\tilde P_j^{c_j})^{\bar b}$ of the printed $\bar J^*(s)$ (p.~322) vanishes,
    condition (b) of the proof is lost, and $S(\mathfrak R^{N-1}_{\mathrm{II}})$ is strictly larger
    than the set of points satisfying (a) and (b); the bijection fails. \emph{Counterexample.} Let $k$
    be algebraically closed of characteristic $0$, $X=\mathbb A^3_k$ with coordinates $(x,y,w)$, $x_0$
    the origin, and $\mathfrak R=(V(x),V(w)\,|\,(x^2+y^2),4\,|\,1,1)$ with closed restriction
    $F=V(x)=E_1$ ($V(x)\cup V(w)$ has normal crossings). Since $x^2+y^2=(x+iy)(x-iy)$, $\nu_p(J)=2$
    exactly on the $w$-axis $L=\{x=y=0\}$; on $F$ the weight is $1+[w=0]$; hence
    $S(\mathfrak R)=\{x_0\}$ (value $4$ at $x_0$, $3$ elsewhere on $L$), $\nu=2<b=4$,
    $S_\nu(\mathfrak R)=\{x_0\}$ has no component of codimension $1$, and [(1)] holds with $s=0$. The
    frame is $z_0=x$, $T_0=k[[y,w]]$, $g_1=z_0^2+y^2$, $\bar b=2$, $\bar J(0)=(y^2)$ on $\tilde X=\bar
    X_0=\operatorname{Spec}k[[y,w]]$. Here $\tilde E_1=\tilde X$, $\tilde E_2=V(w)$, $c=(1,1)$. The
    printed $\bar J^*(0)=((y^2)^2,(0\cdot w)^2)=(y^4)$ and $\tilde b=4$, so
    $S(\mathfrak R^{N-1}_{\mathrm{II}})=V(y)$, the formal $w$-axis, whereas only $\hat x_0$ satisfies
    (a) and (b). The generic point of $V(y)$ maps to the generic point of $L$, which is neither in
    $S_\nu(\mathfrak R)=\{x_0\}$ nor over $x_0$, so the bijection fails; and $\tilde B=V(y)$ is
    permissible for the datum (with $\tilde E_1$ dropped) but the closure of its image is
    $L\not\subseteq S_\nu(\mathfrak R)$, so it does not lift to a permissible center. Keeping the
    printed formula but emptying $\tilde E_1$ gives $(y^4,w^2)$, whose $S$ is empty although
    $S_\nu(\mathfrak R)\cap h_0^{-1}(x_0)=\{x_0\}$. The exponents $c_j$ are those of $\mathfrak R$
    and cannot be changed, so the defect goes into the threshold: with $\delta=1$ and
    $d=b-\nu-\delta=1$ one takes $\tilde J=(y^2,w^2)$, $\tilde b=2$, and
    $S(\mathfrak R^{N-1}_{\mathrm{II}})=\{\hat x_0\}$ as it should be
    (\cref{rem:IV.4-2-repaired}). For $F\neq E_i$ the Remark is as printed.

    \textbf{Deviation from the paper (statement modified).} The paper presupposes that $\mathfrak R^{N-1}_{\mathrm{II}}$ is a resolution datum (cf.\ \cref{lem:IV.4-tilde-facts}); this is false in general (the $\tilde E_j$ can be reducible). The Lean statement assumes only the clauses of Definition~3 (II) that the proof uses (\texttt{IsWeakDatum}): $\tilde b>0$, the $\tilde E_j$ non-singular and everywhere of codimension~$1$ (not necessarily irreducible), $\tilde E_1\cup\dots\cup\tilde E_{\tilde\alpha}$ with only normal crossings, $\tilde J_x\neq0$. The proof is the paper's and uses no irreducibility of the $\tilde E_j$ (statement generalized). -/)
  (proof := /-- (pp.~323--324.) Let $\hat x$ be any point of $\tilde X$. We have that
    $\hat x\in S(\mathfrak R^{N-1}_{\mathrm{II}})$ if and only if (a) $\nu(\bar J(s)_{\hat x})\ge
    \bar b$, and (b) $\sum_{\hat x\in\tilde E_j}c_j\ge b-\nu$; this is clear from the definition
    of $\bar J^*(s)$ and the fact that all the $\tilde E_j$ are non-singular. Assume (a) and (b)
    for $\hat x\in\bar X_s=\tilde X$ and let $x=c_s(\hat x)$. By Lemma (CD.5)
    (\cref{lem:IV.CD-5}), (a) implies $\nu(J(x)_x)$ [sic; $J(s)_x$] $\ge\nu$, and (b) implies
    $\sum_{x\in E_j(s)}a_j\ge b-\nu$; therefore $x\in S_\nu(\mathfrak R^N_{\mathrm{II}}(s))$, and
    in the closed case $x\in F(s)$ (the closure of $c_s(\tilde X)$), so $x\in S_\nu(\mathfrak R(s))$
    in both cases, and [(1)] gives $x\in S_\nu(\mathfrak R(s))\cap h_s^{-1}(x_0)$. Conversely,
    for $x\in S_\nu(\mathfrak R(s))\cap h_s^{-1}(x_0)$, Lemma (CD.3) gives a unique $\hat x$ with
    $c_s(\hat x)=x$, and the Corollary of Lemma (CD.4) (\cref{cor:IV.CD-4}) gives $\hat x\in
    \tilde X$ and (a). Since $\nu=\nu(\mathfrak R)\ge\nu(\mathfrak R(s))$, $\nu(J(s)_x)=\nu$, so
    $\nu+\sum_{x\in E_j(s)}a_j\ge b$, i.e.\ $\sum_{x\in E_j(s)}a_j\ge b-\nu$, and (b) follows (in
    the unrestricted case using [(2)]: $x\notin E_j(s)$ for $1\le j\le\alpha$). For the last
    assertion, $c_s(\tilde B)\subseteq S_\nu(\mathfrak R(s))\cap h_s^{-1}(x_0)$, Lemma (CD.3) gives
    $B_s$ with $\tilde B=c_s^{-1}(B_s)$ and $\tilde B\simeq B_s$, and it suffices to show that
    $E_1(s)\cup\dots\cup E_{\alpha+s}(s)$ has only normal crossings with $B_s$, which follows from
    the assumption that $\tilde E_1\cup\dots\cup\tilde E_{\tilde\alpha}$ has only normal crossings
    with $\tilde B$ (and [(2)] in the unrestricted case). \textsc{q.e.d.}

    \textbf{Deviation from the paper (gap filled).} The steps ``this is clear from the definition of
    $\bar J^*(s)$ and the fact that all the $\tilde E_j$ are non-singular'' and ``(in the unrestricted
    case using [(2)])'' are proved in Lean. $\nu(\bar J^*(s)_{\hat x})\ge\tilde b$ holds iff (a) and (b),
    by the additivity of the order in the regular local ring $\mathcal O_{\tilde X,\hat x}$
    ($\nu(I\cdot(u))=\nu(I)+\nu(u)$, $\nu(J^k)\le k\nu(J)$; $\mathrm{gr}_{\mathfrak m}$ is a domain) and
    since the stalk of each $\tilde E_j$ is generated by an element of order $1$; this also gives
    $S(\mathfrak R^{N-1}_{\mathrm{II}})=\{\nu(\bar J^*(s)_{\hat x})\ge\tilde b\}$. The point
    $x=c_s(\hat x)$ lies over $x_0$ by [(1)] (a generization of $x_0$ at which $X$ has dimension $N$ is
    $x_0$), as in Remark~1; then $\hat x$ lies over $\hat x_0$ and (CD.3) gives injectivity and, with
    the Corollary of (CD.4), surjectivity. The kernel of $\tilde B\to\hat X_s$ is $c_s^{-1}(B_s)$ for the
    irreducible non-singular $B_s=c_s(\tilde B)$ (Lemma (CD.3), as in Remark~1); uniqueness: two
    reduced subschemes with the same points coincide. -/)
  (proofUses := ["lem:IV.CD-5", "lem:IV.CD-3", "cor:IV.CD-4", "def:IV.4-conditions"])
  (latexEnv := "remark")]
theorem Frame.S_datumTilde_eq_and_bijOn_cBar_and_exists_isPermissibleCenter_of_lt [Hironaka.HironakaCitedResults.{u}] {hS : Standing N ℜ r ν T x₀} (𝒮 : Frame hS) (s : ℕ)
    (hprep : PrepHyp N ℜ r ν T x₀ s) (hlt : ν < ℜ.b)
    (a : Fin (alphaT r ℜ.α s) → ℕ) (Jt : Subscheme (𝒮.xTilde s))
    (hJt : Jt * ∏ j, (𝒮.eTilde s j) ^ (a j) = 𝒮.jBarStar s)
    (hII : (𝒮.datumTilde s (𝒮.bBar * (ℜ.b - ν)) a Jt).IsWeakDatum) :
    (𝒮.datumTilde s (𝒮.bBar * (ℜ.b - ν)) a Jt).S =
      {x | ((𝒮.bBar * (ℜ.b - ν) : ℕ) : ℕ∞) ≤ Ideal.nu ((𝒮.jBarStar s).stalkIdeal x)} ∧
    Set.BijOn (𝒮.cBar s).base (𝒮.datumTilde s (𝒮.bBar * (ℜ.b - ν)) a Jt).S
      (sNu (datum T ℜ s) (restriction T r s) ν ∩ (T.pre s).composite.base ⁻¹' {x₀}) ∧
    ∀ Bt : Subscheme (𝒮.xTilde s), Bt.IsNonsingular → Bt.IsIrreducible →
      (𝒮.datumTilde s (𝒮.bBar * (ℜ.b - ν)) a Jt).IsPermissible Bt →
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
  refine ⟨Frame.S_datumTilde_eq_of_jBarStar hadm hII _ hJt, Frame.bijOn_cBar_S hprep hlt hII hJt,
    ?_⟩
  intro Bt hBt hBti hperm
  have hmem : ∀ xb ∈ Bt.pts, (𝒮.cBar s).base xb ∈ (datum T ℜ s).sNu ν := fun xb hxb =>
    (𝒮.cBar_mem_sNu_and_hBar_eq_of_mem_S hprep hlt hII hJt (hperm.2.1 hxb).1).1
  obtain ⟨B, hBns, hBirr, hker, hiso, hpts⟩ :=
    𝒮.exists_ker_eq_totalTransform_of_forall_mem_sNu s hprep Bt hBt hBti hmem
  refine ⟨B, ⟨hBns, hBirr, hker, hiso, ?_⟩, ?_⟩
  · have hnu : (datum T ℜ s).nu ≤ ν := hS.nu_datum_le s
    suffices ∀ R : Restriction (T.X s), R = restriction T r s →
        R.IsPermissibleCenter (datum T ℜ s) B from this _ rfl
    intro R hR
    have hP : (datum T ℜ s).IsPermissible B := by
      refine ⟨Or.inr ⟨hBns, hBirr⟩, ?_,
        𝒮.hasOnlyNormalCrossingsWith_eUnion_datum_of_forall_mem_sNu hprep a Jt hII Bt hBt hBti hperm
          B hiso hmem⟩
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

/-- **Remark 3** (pp. 324–326).  As in `lem:IV.4-case-ge-relation`: the extension of `h_s` by
`f_s` with center `B_s` is the hypothesis `T.B s = B_s` on the succession of the setup, `B_s`
being the subscheme of Remark 2; `f̃ = f̄_s` is the monoidal transformation of `X̃` with center
`B̃` built from the universal property, `X̃' = X̄_{s+1}`.

Deviation from the paper (gap filled): the steps "It follows from the definition of `f̃*(ℜ^{N-1}_II)`
that …" and "this equality is clear for the case `(ℜ^N_II, F)`, and it follows for the other case if
`B_s ⊄ E_j(s)` for `1 ≤ j ≤ α`, a consequence of the assumption `[(2)]`" (p. 325–326) are proved in
Lean: `transform_datumTilde_eq` (the transform has the form of the datum at stage `s+1`, `Ẽ'_j` being the
strict transforms), `prod_eq_of_stalkIdeal_totalTransform_eq` (the identity `J̃' ∏ (P̃'_j)^{ã_j} =
f̄_s⁻¹(J̄*(s)) P̄_{s+1}^{-b̃}`), `stalkIdeal_totalTransform_jBarStar` (`f̄_s⁻¹(J̄*(s)) = P̄_{s+1}^{b̃} J̄*(s+1)`,
using `cT_succ_lastT_add_eq`, i.e. `c'_{α̃+1} + (b − ν) = e`) and `sum_isContainedIn_datum_eq` (the sums over
`B_s ⊆ E_j(s)` and `B̃ ⊆ Ẽ_j` agree, by `[(2)]`, `B_s ⊆ S_ν`).  For an empty `B_s` the paper's equality of
the sums fails (`B_s ⊆ E_j(s)` for all `j`) but is harmless; the irreducibility of `B_s` (non-empty)
excludes it. -/
@[blueprint "rem:IV.4-3"
  (statement := /-- Let $\tilde B$ and $B_s$ be as in Remark~2 (\cref{rem:IV.4-2}). Let
    $\tilde f\colon\tilde X'\to\tilde X$ be the monoidal transformation with center $\tilde B$,
    which is permissible for the resolution datum $\mathfrak R^{N-1}_{\mathrm{II}}$, and
    $f_s\colon X_{s+1}\to X_s$ the one with center $B_s$, which is permissible for
    $\mathfrak R(s)$. We put $\mathfrak R(s+1)=f_s^*(\mathfrak R(s))$ with
    $\mathfrak R^N_{\mathrm{II}}(s+1)=f_s^*(\mathfrak R^N_{\mathrm{II}}(s))=\big(E_1(s+1),\dots,
    E_{\alpha+s+1}(s+1)\,\big|\,J(s+1),b\,\big|\,a_1,\dots,a_{\alpha+s+1}\big)$ where
    $E_{\alpha+s+1}(s+1)$ denotes the total transform of $B_s$ in $X_{s+1}$. We put also
    $\bar X_{s+1}=$ the strict transform of $\bar X_s$ in $\hat X_{s+1}$, and $\bar J(s+1)=\bar
    f_s^{-1}(\bar J(s))/(\bar P_{s+1})^{\bar b}$ where $\bar f_s$ denotes the monoidal
    transformation $\bar X_{s+1}\to\bar X_s$ with center $\tilde B$, which is induced by
    $\hat f_s$, and $\bar P_{s+1}$ denotes the sheaf of ideals of the subscheme
    $c_s^{-1}(E_{\alpha+s+1}(s+1))\cap\bar X_{s+1}$ [sic; $c_{s+1}^{-1}$] of $\bar X_{s+1}$ (i.e.,
    the total transform of $\tilde B$ in $\bar X_{s+1}$). We may set $\tilde X'=\bar X_{s+1}$ and
    $\tilde f=\bar f_s$. We define $\tilde E'_j$ $(1\le j\le\tilde\alpha+1)$, $c'_j$,
    $\tilde P'_j$ and $\bar J^*(s+1)=\big(\bar J(s+1)^{b-\nu},(\prod_{j=1}^{\tilde\alpha+1}
    (\tilde P'_j)^{c'_j})^{\bar b}\big)$ for $h_{s+1}=f_s\circ h_s$ as we did for $h_s$
    (\cref{def:IV.4-tilde}, \cref{def:IV.4-case-lt}). \textbf{Remark 3.} Notation and the
    assumptions being as above, $\tilde f^*(\mathfrak R^{N-1}_{\mathrm{II}})$ on $\tilde X'$ can be
    written in the form $\big(\tilde E'_1,\dots,\tilde E'_{\tilde\alpha+1}\,\big|\,\tilde J',
    \tilde b\,\big|\,\tilde a_1,\dots,\tilde a_{\tilde\alpha+1}\big)$ where $\bar J^*(s+1)=
    \tilde J'\cdot\prod_{j=1}^{\tilde\alpha+1}((\tilde P'_j)^{\tilde a_j})$. In other words, the
    relation between $\mathfrak R(s+1)$ $(=f_s^*(\mathfrak R(s)))$ and
    $\tilde f^*(\mathfrak R^{N-1}_{\mathrm{II}})$ is the same as that between $\mathfrak R(s)$ and
    $\mathfrak R^{N-1}_{\mathrm{II}}$. (pp.~324--325.) (Formalization notes (encoding): the extension of
    $h_s$ by $f_s$ is the hypothesis $B_s=$ the center of the $s$th transformation of the
    succession of \cref{def:IV.4-standing}; $\tilde f=\bar f_s$ is asserted to be the monoidal
    transformation with center $\tilde B$ and is built from the universal property; the first
    $\tilde\alpha$ of the $\tilde a_j$ are those of $\mathfrak R^{N-1}_{\mathrm{II}}$.)

    \textbf{Deviation from the paper (statement modified).} The paper presupposes that $\mathfrak R^{N-1}_{\mathrm{II}}$ is a resolution datum (cf.\ \cref{lem:IV.4-tilde-facts}); this is false in general (the $\tilde E_j$ can be reducible). The Lean statement assumes only the clauses of Definition~3 (II) that the proof uses (\texttt{IsWeakDatum}): $\tilde b>0$, the $\tilde E_j$ non-singular and everywhere of codimension~$1$ (not necessarily irreducible), $\tilde E_1\cup\dots\cup\tilde E_{\tilde\alpha}$ with only normal crossings, $\tilde J_x\neq0$. The proof is the paper's and uses no irreducibility of the $\tilde E_j$ (statement generalized). -/)
  (proof := /-- (pp.~325--326.) It follows from the definition of $\tilde f^*(\mathfrak R^{N-1}_
    {\mathrm{II}})$ (\cref{def:I.7-II}) that $\tilde J'\cdot\prod_{j=1}^{\tilde\alpha+1}
    ((\tilde P'_j)^{\tilde a_j})=\tilde f^{-1}(\tilde J\cdot\prod_{j=1}^{\tilde\alpha}
    (\tilde P_j^{\tilde a_j}))(\tilde P'_{\tilde\alpha+1})^{-\tilde b}$, which is equal to
    $\tilde f^{-1}(\bar J^*(s))(\tilde P'_{\tilde\alpha+1})^{-\tilde b}$. Therefore the assertion is
    equivalent to $\bar J^*(s+1)=\tilde f^{-1}(\bar J^*(s))(\tilde P'_{\tilde\alpha+1})^{-\tilde
    b}$.
    Recall $\tilde b=\bar b(b-\nu)$ and $\bar J(s+1)=\tilde f^{-1}(\bar J(s))(\tilde
    P'_{\tilde\alpha+1})^{-\bar b}$; it is sufficient to prove $\prod_{j=1}^{\tilde\alpha+1}
    (\tilde P'_j)^{c'_j}=\tilde f^{-1}(\prod_{j=1}^{\tilde\alpha}(\tilde P_j)^{c_j})
    (\tilde P'_{\tilde\alpha+1})^{-(b-\nu)}$. The right hand side is equal to
    $(\prod_{j=1}^{\tilde\alpha}(\tilde P'_j)^{c_j})(\tilde P'_{\tilde\alpha+1})^{\,e-(b-\nu)}$ with
    $e=\sum_{\tilde B\subseteq\tilde E_j}c_j$. By definition $c'_j=c_j$ for $1\le j\le\tilde
    \alpha$, so all that we need to prove is $c'_{\tilde\alpha+1}=e-(b-\nu)$. Writing
    $\mathfrak R^N_{\mathrm{II}}(s)$ and $\mathfrak R^N_{\mathrm{II}}(s+1)$ as before, we have
    $c'_{\tilde\alpha+1}=a_{\alpha+s+1}=(\sum_{B_s\subseteq E_j(s)}a_j)+\nu-b$
    (\cref{def:I.7-II}). Thus we have only to prove $\sum_{B_s\subseteq E_j(s)}a_j=
    \sum_{\tilde B\subseteq\tilde E}c_j$ [sic; $\tilde E_j$]. In view of the definition of $c_j$
    and $\tilde E_j$, this equality is clear for the case in which $\mathfrak R=
    (\mathfrak R^N_{\mathrm{II}},F)$, and it follows for the other case if $B_s\not\subseteq
    E_j(s)$ for any $j$ with $1\le j\le\alpha$, a consequence of the assumption [(2)], as was
    already seen in the proof of Remark~2. \textsc{q.e.d.}

    \textbf{Deviation from the paper (gap filled).} The steps ``It follows from the definition of
    $\tilde f^*(\mathfrak R^{N-1}_{\mathrm{II}})$ that \dots'' (p.~325) are proved in Lean. (a) The
    chart of p.~169 and the flat base change $c_{s+1}$ give $\bar f_s^{-1}(\tilde E_j)=\tilde E'_j\,
    \bar P_{s+1}^{m_j}$ ($m_j=1$ iff $B_s\subseteq E_j(s)$), so that $\tilde E'_j$ is the strict transform
    of $\tilde E_j$ (``strict transforms commute with $c_{s+1}$ and with the restriction to
    $\bar X_{s+1}$''). (b) $\bar f_s^{-1}(\tilde J)$ is divisible by $\bar P_{s+1}^{\tilde\nu}$ (Remark~2
    of Ch.~III at the generic point of the irreducible $\tilde B$) and $\tilde b\le\sum_{\tilde
    B\subseteq\tilde E_j}\tilde a_j+\tilde\nu$ (the generic point of $\tilde B$ lies in
    $S(\mathfrak R^{N-1}_{\mathrm{II}})$), so $\tilde a_{\tilde\alpha+1}$ is computed without
    truncation. (c) $\bar f_s^{-1}(\bar J(s))=\bar J(s+1)\bar P_{s+1}^{\bar b}$, as $\bar J(s)$ lies in
    the $\bar b$th power of the ideal of $\hat B_s$. (d) $c'_{\tilde\alpha+1}+(b-\nu)=e$ with
    $e=\sum_{\tilde B\subseteq\tilde E_j}c_j$: $c'_{\tilde\alpha+1}=a_{\alpha+s+1}=(\sum_{B_s\subseteq
    E_j(s)}a_j)+\nu-b$, the sums agree by [(2)] (for $B_s\neq\emptyset$, which holds since $B_s$ is
    irreducible), and $b\le\sum_{B_s\subseteq E_j(s)}a_j+\nu$ by the permissibility of $B_s$ (the
    generic point of $B_s$ lies in $S(\mathfrak R(s))$). Then $\bar f_s^{-1}(\bar J^*(s))=\bar P_{s+1}^{\tilde
    b}\,\bar J^*(s+1)$ and the claim is cancellation of the non-zero-divisor $\bar P_{s+1}^{\tilde b}$
    in the stalks (regular local rings). The paper's last sentence is false for an empty center
    ($B_s=\emptyset\subseteq E_j(s)$ for all $j$), which is excluded by the irreducibility of $B_s$. -/)
  (proofUses := ["rem:IV.4-2", "def:I.7-II", "lem:IV.4-Pbar", "def:IV.4-conditions",
    "lem:IV.4-exceptional-transversal-nonsingular"])
  (latexEnv := "remark")]
theorem Frame.exists_transform_eq_datumTilde_of_lt [Hironaka.HironakaCitedResults.{u}] {hS : Standing N ℜ r ν T x₀} (𝒮 : Frame hS) (s : ℕ)
    (hprep : PrepHyp N ℜ r ν T x₀ s) (hlt : ν < ℜ.b)
    (a : Fin (alphaT r ℜ.α s) → ℕ) (Jt : Subscheme (𝒮.xTilde s))
    (hJt : Jt * ∏ j, (𝒮.eTilde s j) ^ (a j) = 𝒮.jBarStar s)
    (hII : (𝒮.datumTilde s (𝒮.bBar * (ℜ.b - ν)) a Jt).IsWeakDatum)
    (Bt : Subscheme (𝒮.xTilde s)) (hBt : Bt.IsNonsingular) (hBti : Bt.IsIrreducible)
    (hperm : (𝒮.datumTilde s (𝒮.bBar * (ℜ.b - ν)) a Jt).IsPermissible Bt)
    (Bs : Subscheme (T.X s)) (hBs : Bs.IsNonsingular ∧ Bs.IsIrreducible)
    (hBc : (Bt.ι ≫ (𝒮.xBar s).ι).ker = Subscheme.totalTransform (𝒮.c s) Bs)
    (hBe : ∃ e : Bt.toScheme ≅ Bs.toScheme, e.hom ≫ Bs.ι = Bt.ι ≫ 𝒮.cBar s)
    (hBperm : (restriction T r s).IsPermissibleCenter (datum T ℜ s) Bs) (hTB : T.B s = Bs) :
    ∃ h : AB.IsMonoidalTransformationOf (𝒮.fBar s) Bt,
      ∃ (anew : ℕ) (Jt' : Subscheme (𝒮.xTilde (s + 1))),
        (𝒮.datumTilde s (𝒮.bBar * (ℜ.b - ν)) a Jt).transform
            (⟨_, 𝒮.fBar s, h.1, h.2⟩ : MonoidalTransformation (𝒮.xTilde s) Bt) =
          𝒮.datumTilde (s + 1) (𝒮.bBar * (ℜ.b - ν)) (extendA a anew) Jt' ∧
        Jt' * ∏ j, (𝒮.eTilde (s + 1) j) ^ (extendA a anew j) = 𝒮.jBarStar (s + 1) := by
  have hd : 𝒮.CenterData s Bt Bs := ⟨hBt, hBti, hBs.1, hBs.2, hBc, hBe, hBperm, hTB⟩
  have hadm := 𝒮.isAdmissibleAt_of_prepHyp hprep
  have h := 𝒮.isMonoidalTransformationOf_fBar_of_ker_eq s hd.ker_eq_B
  refine ⟨h, ((𝒮.datumTilde s (𝒮.bBar * (ℜ.b - ν)) a Jt).transform (𝒮.tBar s h)).a (Fin.last _),
    ((𝒮.datumTilde s (𝒮.bBar * (ℜ.b - ν)) a Jt).transform (𝒮.tBar s h)).J,
    Frame.transform_datumTilde_eq hadm hd hII hperm h, ?_⟩
  refine Frame.prod_eq_of_stalkIdeal_totalTransform_eq hadm hd hII hperm h _ (fun yb => ?_)
  rw [hJt]
  exact Frame.stalkIdeal_totalTransform_jBarStar hprep hlt hd yb

end CD

/-! ## The lifting of a resolving succession of `X̃` (pp. 321–326): the core step

Formalization infrastructure for the last step of the proof of Theorems C and D*: the stage states `FrameStage`, the
lifting of the monoidal transformations of `X̃` one at a time, and the core step `exists_extension_not_mem_sNuImage`. -/

namespace MonoidalSuccession

variable {X Y Z W : Scheme.{u}}

theorem append_assoc (g : MonoidalSuccession X Y) (h : MonoidalSuccession Y Z)
    (k : MonoidalSuccession Z W) : (g.append h).append k = g.append (h.append k) := by
  induction g with
  | nil X => rfl
  | cons B t rest ih => exact congrArg (cons B t) (ih h)

theorem append_cons_eq_snoc_append (g : MonoidalSuccession X Y) {B : Subscheme Y}
    (t : MonoidalTransformation Y B) (e : MonoidalSuccession t.X' Z) :
    g.append (cons B t e) = (g.snoc B t).append e := by
  rw [snoc_eq_append, append_assoc]
  rfl

end MonoidalSuccession

namespace CD

section Induction

variable {N : ℕ} {X : Scheme.{u}}

/-- The hypotheses `[(1)]`, `[(2)]` of the core step on a finite permissible succession `g`
(`x_0 ∈ h_s(S_ν(ℜ(s)))` is separate). -/
structure Prepared (N : ℕ) (ℜ : DatumII.Raw X) (ν : ℕ) {Y : Scheme.{u}}
    (g : MonoidalSuccession X Y) : Prop where
  isPermissibleII : g.IsPermissibleII ℜ
  finite : (sNuImage g ℜ ν).Finite
  dimAt_eq : ∀ y ∈ sNuImage g ℜ ν, X.dimAt y = (N : WithBot ℕ∞)
  disjoint : ∀ i : Fin ℜ.α, (g.strictTransform (ℜ.E i)).pts ∩ (g.transformII ℜ).sNu ν = ∅

theorem Prepared.append [Hironaka.HironakaCitedResults.{u}] (hX : IsAmbient X N) {ℜ : DatumII.Raw X} (hℜ : ℜ.IsDatum) {ν : ℕ}
    {Y Z : Scheme.{u}} {g : MonoidalSuccession X Y} (hg : Prepared N ℜ ν g)
    (e : MonoidalSuccession Y Z) (he : e.IsPermissibleII (g.transformII ℜ)) :
    Prepared N ℜ ν (g.append e) := by
  have hsub := sNuImage_append_subset hX ℜ hℜ g hg.isPermissibleII e he ν
  obtain ⟨hY, hd⟩ := g.isAmbient_transformII hX ℜ hℜ hg.isPermissibleII
  have := hX.1
  have := hY.1
  refine ⟨(MonoidalSuccession.isPermissibleII_append g e ℜ).mpr ⟨hg.isPermissibleII, he⟩,
    hg.finite.subset hsub, fun y hy => hg.dimAt_eq y (hsub hy), fun i => ?_⟩
  refine Set.eq_empty_iff_forall_notMem.mpr fun y hy => ?_
  rw [MonoidalSuccession.transformII_append, MonoidalSuccession.strictTransform_append] at hy
  have h1 := MonoidalSuccession.pts_strictTransform_subset e _ hy.1
  have h2 := MonoidalSuccession.mem_sNu_of_mem_sNu_transformII e hY.2.1 _ hd he hy.2
  exact (Set.eq_empty_iff_forall_notMem.mp (hg.disjoint i)) (e.composite.base y) ⟨h1, h2⟩

/-- The induction over a resolving succession of `X̃`, abstractly: `Q g k` says that the auxiliary
datum at the stage `g` is resolvable by a succession of exactly `k` transformations. -/
theorem exists_extension_of_resolvableLen [Hironaka.HironakaCitedResults.{u}] (hX : IsAmbient X N) {ℜ : DatumII.Raw X}
    (hℜ : ℜ.IsDatum) {ν : ℕ} {x₀ : X}
    (Q : ∀ {Y : Scheme.{u}}, MonoidalSuccession X Y → ℕ → Prop)
    (hend : ∀ {Y : Scheme.{u}} (g : MonoidalSuccession X Y), Prepared N ℜ ν g →
      x₀ ∈ sNuImage g ℜ ν → ¬ Q g 0)
    (hstep : ∀ {Y : Scheme.{u}} (g : MonoidalSuccession X Y) (k : ℕ), Prepared N ℜ ν g →
      x₀ ∈ sNuImage g ℜ ν → Q g (k + 1) → Q g k ∨
        ∃ (B : Subscheme Y) (t : MonoidalTransformation Y B),
          (g.transformII ℜ).IsPermissible B ∧ Q (g.snoc B t) k) :
    ∀ (k : ℕ) {Y : Scheme.{u}} (g : MonoidalSuccession X Y), Prepared N ℜ ν g →
      x₀ ∈ sNuImage g ℜ ν → Q g k →
      ∃ (Z : Scheme.{u}) (e : MonoidalSuccession Y Z), e.IsPermissibleII (g.transformII ℜ) ∧
        x₀ ∉ sNuImage (g.append e) ℜ ν ∧
        ∀ i : Fin ℜ.α, ((g.append e).strictTransform (ℜ.E i)).pts ∩
          ((g.append e).transformII ℜ).sNu ν = ∅ := by
  intro k
  induction k with
  | zero => intro Y g hg hx hQ; exact absurd hQ (hend g hg hx)
  | succ k ih =>
    intro Y g hg hx hQ
    rcases hstep g k hg hx hQ with hQ' | ⟨B, t, hperm, hQ'⟩
    · exact ih g hg hx hQ'
    have he : (MonoidalSuccession.cons B t (MonoidalSuccession.nil t.X')).IsPermissibleII
        (g.transformII ℜ) := ⟨hperm, trivial⟩
    have hg' : Prepared N ℜ ν (g.snoc B t) := by
      rw [MonoidalSuccession.snoc_eq_append]
      exact hg.append hX hℜ _ he
    by_cases hx' : x₀ ∈ sNuImage (g.snoc B t) ℜ ν
    · obtain ⟨Z, e', he', hnot, hdisj⟩ := ih (g.snoc B t) hg' hx' hQ'
      refine ⟨Z, MonoidalSuccession.cons B t e', ⟨hperm, ?_⟩, ?_, ?_⟩
      · have := he'
        rwa [MonoidalSuccession.transformII_snoc] at this
      · rw [MonoidalSuccession.append_cons_eq_snoc_append]; exact hnot
      · rw [MonoidalSuccession.append_cons_eq_snoc_append]; exact hdisj
    · refine ⟨_, MonoidalSuccession.cons B t (MonoidalSuccession.nil t.X'), he, ?_, ?_⟩
      · rw [← MonoidalSuccession.snoc_eq_append]; exact hx'
      · intro i
        rw [← MonoidalSuccession.snoc_eq_append]
        exact hg'.disjoint i

/-- The induction over a resolving succession of `X̃`, abstractly, for `(ℜ, F)` (closed analogue
of `exists_extension_of_resolvableLen`): `Q g k` says that the auxiliary datum at the stage `g`
is resolvable by a succession of exactly `k` transformations. -/
theorem exists_extension_of_resolvableLen_closed [Hironaka.HironakaCitedResults.{u}] (hX : IsAmbient X N) {ℜ : DatumII.Raw X}
    (hℜ : ℜ.IsDatum) {F : Subscheme X} {ν : ℕ} {x₀ : X}
    (Q : ∀ {Y : Scheme.{u}}, MonoidalSuccession X Y → ℕ → Prop)
    (hend : ∀ {Y : Scheme.{u}} (g : MonoidalSuccession X Y), PreparedClosed N ℜ F ν g →
      x₀ ∈ sNuImageClosed g ℜ F ν → ¬ Q g 0)
    (hstep : ∀ {Y : Scheme.{u}} (g : MonoidalSuccession X Y) (k : ℕ), PreparedClosed N ℜ F ν g →
      x₀ ∈ sNuImageClosed g ℜ F ν → Q g (k + 1) → Q g k ∨
        ∃ (B : Subscheme Y) (t : MonoidalTransformation Y B),
          (g.transformII ℜ).IsPermissibleClosed (g.strictTransform F) B ∧ Q (g.snoc B t) k) :
    ∀ (k : ℕ) {Y : Scheme.{u}} (g : MonoidalSuccession X Y), PreparedClosed N ℜ F ν g →
      x₀ ∈ sNuImageClosed g ℜ F ν → Q g k →
      ∃ (Z : Scheme.{u}) (e : MonoidalSuccession Y Z),
        e.IsPermissibleIIClosed (g.transformII ℜ) (g.strictTransform F) ∧
        x₀ ∉ sNuImageClosed (g.append e) ℜ F ν := by
  intro k
  induction k with
  | zero => intro Y g hg hx hQ; exact absurd hQ (hend g hg hx)
  | succ k ih =>
    intro Y g hg hx hQ
    rcases hstep g k hg hx hQ with hQ' | ⟨B, t, hperm, hQ'⟩
    · exact ih g hg hx hQ'
    have he : (MonoidalSuccession.cons B t (MonoidalSuccession.nil t.X')).IsPermissibleIIClosed
        (g.transformII ℜ) (g.strictTransform F) := ⟨hperm, trivial⟩
    have hg' : PreparedClosed N ℜ F ν (g.snoc B t) := by
      rw [MonoidalSuccession.snoc_eq_append]
      exact hg.append hX hℜ _ he
    by_cases hx' : x₀ ∈ sNuImageClosed (g.snoc B t) ℜ F ν
    · obtain ⟨Z, e', he', hnot⟩ := ih (g.snoc B t) hg' hx' hQ'
      refine ⟨Z, MonoidalSuccession.cons B t e', ⟨hperm, ?_⟩, ?_⟩
      · have := he'
        rwa [MonoidalSuccession.transformII_snoc, MonoidalSuccession.strictTransform_snoc] at this
      · rw [MonoidalSuccession.append_cons_eq_snoc_append]; exact hnot
    · refine ⟨_, MonoidalSuccession.cons B t (MonoidalSuccession.nil t.X'), he, ?_⟩
      rw [← MonoidalSuccession.snoc_eq_append]; exact hx'

end Induction

end CD

namespace CD

/-- Congruence for `divPow (f⁻¹ J) (f⁻¹ B) b` in the morphism `f` and the subschemes `J`, `B`
(the stage objects are compared through this lemma: asking the unifier to compare them directly
unfolds the limit cones of the completion). -/
theorem divPow_totalTransform_congr {Z Z' : Scheme.{u}} {f g : Z ⟶ Z'} (h : f = g)
    {J B J' B' : Subscheme Z'} (hJ : J = J') (hB : B = B') (b : ℕ) :
    Subscheme.divPow (Subscheme.totalTransform f J) (Subscheme.totalTransform f B) b =
      Subscheme.divPow (Subscheme.totalTransform g J') (Subscheme.totalTransform g B') b := by
  subst h hJ hB
  rfl

/-- The stage-`s` objects of the construction of pp. 314-316 that the lifting of §4 needs:
`X̂_s`, `c_s`, `X̄_s` and `J̄(s)`. -/
structure FrameStage (Y : Scheme.{u}) where
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

attribute [instance] FrameStage.flat

namespace FrameStage

variable {Y : Scheme.{u}} (σ : FrameStage Y)

/-- `B̄ = ι⁻¹(c⁻¹(B))` on `X̄`. -/
def bBarOn (B : Subscheme Y) : Subscheme σ.xBar.toScheme :=
  Subscheme.totalTransform σ.xBar.ι (Subscheme.totalTransform σ.c B)

/-- One stage of the construction: `X̂_{s+1} = X_{s+1} ×_{X_s} X̂_s`, `X̄_{s+1}` the strict
transform of `X̄_s`, `J̄(s+1) = f̄_s⁻¹(J̄(s)) / (f̄_s⁻¹(B̄_s))^b`. -/
noncomputable def step (b : ℕ) {B : Subscheme Y} (t : MonoidalTransformation Y B) :
    FrameStage t.X' where
  xHat := pullback t.f σ.c
  c := pullback.fst t.f σ.c
  flat := inferInstance
  xBar := Subscheme.strictTransform (t.baseChange σ.c) σ.xBar
  jBar := Subscheme.divPow
    (Subscheme.totalTransform ((t.baseChange σ.c).strictTransformMap σ.xBar) σ.jBar)
    (Subscheme.totalTransform ((t.baseChange σ.c).strictTransformMap σ.xBar) (σ.bBarOn B)) b

theorem step_jBar {B : Subscheme Y} (b : ℕ) (t : MonoidalTransformation Y B) :
    (σ.step b t).jBar = Subscheme.divPow
      (Subscheme.totalTransform ((t.baseChange σ.c).strictTransformMap σ.xBar) σ.jBar)
      (Subscheme.totalTransform ((t.baseChange σ.c).strictTransformMap σ.xBar)
        (σ.bBarOn B)) b := rfl

theorem ext_of_heq {σ₁ σ₂ : FrameStage Y} (h1 : σ₁.xHat = σ₂.xHat) (h2 : HEq σ₁.c σ₂.c)
    (h3 : HEq σ₁.xBar σ₂.xBar) (h4 : HEq σ₁.jBar σ₂.jBar) : σ₁ = σ₂ := by
  cases σ₁; cases σ₂
  simp only at h1
  subst h1
  simp only [heq_eq_eq] at h2 h3 h4
  subst h2 h3 h4
  rfl

/-- The initial state `X̂_0 = Spec Ŝ_0`, `c_0`, `X̄_0 = V(z_0)`, `J̄(0)` generated by `jGen`. -/
def initial {X : Scheme.{u}} (x₀ : X) (hx : X.IsSimpleAt x₀) (z : AB.Shat X x₀)
    (jGen : Set (AB.Shat X x₀)) : FrameStage X where
  xHat := AB.xHat0 X x₀
  c := AB.c0 X x₀
  flat := AB.flat_c0 X x₀ hx
  xBar := AB.vZ X x₀ z
  jBar := Subscheme.totalTransform (AB.vZ X x₀ z).ι (Scheme.IdealSheafData.ofIdealTop
    ((Ideal.span jGen).map (Scheme.ΓSpecIso (CommRingCat.of (AB.Shat X x₀))).inv.hom))

end FrameStage

/-- Fold the stage construction along a finite succession (front recursion: no casts). -/
noncomputable def FrameStage.fold (b : ℕ) :
    ∀ {Y Z : Scheme.{u}}, MonoidalSuccession Y Z → FrameStage Y → FrameStage Z
  | _, _, .nil _, σ => σ
  | _, _, .cons _ t rest, σ => FrameStage.fold b rest (σ.step b t)

theorem FrameStage.fold_append (b : ℕ) {Y Z W : Scheme.{u}} (g : MonoidalSuccession Y Z)
    (h : MonoidalSuccession Z W) (σ : FrameStage Y) :
    FrameStage.fold b (g.append h) σ = FrameStage.fold b h (FrameStage.fold b g σ) := by
  induction g with
  | nil X => rfl
  | cons B t rest ih => exact ih h (σ.step b t)

theorem FrameStage.fold_snoc (b : ℕ) {Y Z : Scheme.{u}} (g : MonoidalSuccession Y Z)
    {B : Subscheme Z} (t : MonoidalTransformation Z B) (σ : FrameStage Y) :
    FrameStage.fold b (g.snoc B t) σ = (FrameStage.fold b g σ).step b t := by
  induction g with
  | nil X => rfl
  | cons B' t' rest ih => exact ih t (σ.step b t')

/-! ### The auxiliary datum read off a stage state -/

section Readers

variable {X : Scheme.{u}}

/-- The member `E_i` of a datum, read at a natural-number index (junk `⊤` beyond `α`). -/
def _root_.Hironaka.DatumII.Raw.eAt {Y : Scheme.{u}} (D : DatumII.Raw Y) (i : ℕ) : Subscheme Y :=
  if h : i < D.α then D.E ⟨i, h⟩ else Subscheme.empty

/-- The exponent `a_i` of a datum, read at a natural-number index (junk `0` beyond `α`). -/
def _root_.Hironaka.DatumII.Raw.aAt {Y : Scheme.{u}} (D : DatumII.Raw Y) (i : ℕ) : ℕ :=
  if h : i < D.α then D.a ⟨i, h⟩ else 0

/-- The index in `E_1(s), …, E_{α+s}(s)` of the `j`-th member giving `Ẽ_j` (p. 321). -/
def idxN (r : Restriction X) (α : ℕ) (j : ℕ) : ℕ :=
  match r with
  | .closed _ => j
  | .unrestricted => α + j

theorem coe_idxT (r : Restriction X) (α s : ℕ) (j : Fin (alphaT r α s)) :
    ((idxT α s r j : Fin (α + s)) : ℕ) = idxN r α j := by
  cases r <;> rfl

namespace FrameStage

variable {Y : Scheme.{u}} (σ : FrameStage Y)

/-- `Ẽ_j = ι⁻¹(c⁻¹(E_j(s)))`, with `ℜ^N_II(s) = D`. -/
def eTilde (D : DatumII.Raw Y) (r : Restriction X) (α n : ℕ) (j : Fin (alphaT r α n)) :
    Subscheme σ.xBar.toScheme :=
  Subscheme.totalTransform σ.xBar.ι (Subscheme.totalTransform σ.c (D.eAt (idxN r α j)))

/-- The auxiliary datum `(Ẽ_1, …, Ẽ_α̃ | J̃, b̃ | ã_1, …, ã_α̃)`. -/
def datumTilde (D : DatumII.Raw Y) (r : Restriction X) (α n : ℕ) (bt : ℕ)
    (a : Fin (alphaT r α n) → ℕ) (Jt : Subscheme σ.xBar.toScheme) :
    DatumII.Raw σ.xBar.toScheme where
  α := alphaT r α n
  E := σ.eTilde D r α n
  a := a
  J := Jt
  b := bt

/-- `J̄*(s) = (J̄(s)^{b-ν}, (∏ P̃_j^{c_j})^{b̄})`. -/
def jBarStar (D : DatumII.Raw Y) (r : Restriction X) (α n : ℕ) (b ν bBar : ℕ) :
    Subscheme σ.xBar.toScheme :=
  σ.jBar ^ (b - ν) + (∏ j : Fin (alphaT r α n),
    (σ.eTilde D r α n j) ^ (D.aAt (idxN r α j))) ^ bBar

/-- `J̄(s)` if `ν ≥ b`, `J̄*(s)` if `ν < b` (pp. 321, 322). -/
def kOf (D : DatumII.Raw Y) (r : Restriction X) (α n : ℕ) (b ν : ℕ) : Subscheme σ.xBar.toScheme :=
  if b ≤ ν then σ.jBar else σ.jBarStar D r α n b ν ν.factorial

end FrameStage

theorem eAt_datum_eq_eSeq (T : AB.Tower X) (ℜ : DatumII.Raw X) (s : ℕ) (j : Fin (ℜ.α + s)) :
    (datum T ℜ s).eAt j = eSeq T ℜ s j := by
  have h : (j : ℕ) < (datum T ℜ s).α := by rw [alpha_datum]; exact j.2
  unfold DatumII.Raw.eAt
  simp only [h, ↓reduceDIte]
  rfl

theorem aAt_datum_eq_aSeq (T : AB.Tower X) (ℜ : DatumII.Raw X) (s : ℕ) (j : Fin (ℜ.α + s)) :
    (datum T ℜ s).aAt j = aSeq T ℜ s j := by
  have h : (j : ℕ) < (datum T ℜ s).α := by rw [alpha_datum]; exact j.2
  unfold DatumII.Raw.aAt
  simp only [h, ↓reduceDIte]
  rfl

end Readers

section Bridge

variable {N : ℕ} {X : Scheme.{u}} {ℜ : DatumII.Raw X} {r : Restriction X} {ν : ℕ}
  {T : AB.Tower X} {x₀ : X} {hS : Standing N ℜ r ν T x₀}

/-- A CD frame over the canonical completion `Tower.completion`, built from the tower-independent
data `(z, jGen, FrameSpec)` (the construction of `Standing.nonempty_frame`). -/
noncomputable def Frame.canon (hS : Standing N ℜ r ν T x₀) [IsRegularLocalRing (AB.Shat X x₀)]
    (z : AB.Shat X x₀) (jGen : Set (AB.Shat X x₀)) (fr : FrameSpec N x₀ ℜ r ν z jGen) :
    Frame hS where
  toCompletion := T.completion x₀ (hS.ambient.2.1 x₀)
  regShat := ‹_›
  z := z
  jGen := jGen
  frame := fr
  fBar := fun s =>
    ((T.completion x₀ (hS.ambient.2.1 x₀)).tHat.monoidalTransformation s).strictTransformMap
    (AB.strictTransformZeroLocus (T.completion x₀ (hS.ambient.2.1 x₀)).tHat z s)
  fBar_comm := fun _ => MonoidalTransformation.strictTransformMap_ι _ _

/-- The stage-`s` state of a frame: `X̂_s`, `c_s`, `X̄_s`, `J̄(s)`. -/
def Frame.stageOf (𝒮 : Frame hS) (s : ℕ) : FrameStage (T.X s) where
  xHat := 𝒮.tHat.X s
  c := 𝒮.c s
  flat := 𝒮.toCompletion.flat_c (hS.ambient.2.1 x₀) s
  xBar := 𝒮.xBar s
  jBar := 𝒮.jBar s

theorem Frame.eTilde_eq_stageOf (𝒮 : Frame hS) (s : ℕ) (j : Fin (alphaT r ℜ.α s)) :
    𝒮.eTilde s j = (𝒮.stageOf s).eTilde (datum T ℜ s) r ℜ.α s j := by
  have h1 : (datum T ℜ s).eAt (idxN r ℜ.α j) = eSeq T ℜ s (idxT ℜ.α s r j) := by
    rw [← coe_idxT r ℜ.α s j]
    exact eAt_datum_eq_eSeq T ℜ s (idxT ℜ.α s r j)
  show Subscheme.totalTransform (𝒮.xBar s).ι
    (Subscheme.totalTransform (𝒮.c s) (eSeq T ℜ s (idxT ℜ.α s r j))) =
      Subscheme.totalTransform (𝒮.stageOf s).xBar.ι
        (Subscheme.totalTransform (𝒮.stageOf s).c ((datum T ℜ s).eAt (idxN r ℜ.α j)))
  rw [h1]
  rfl

theorem Frame.datumTilde_eq_stageOf (𝒮 : Frame hS) (s bt : ℕ)
    (a : Fin (alphaT r ℜ.α s) → ℕ) (Jt : Subscheme (𝒮.xTilde s)) :
    𝒮.datumTilde s bt a Jt = (𝒮.stageOf s).datumTilde (datum T ℜ s) r ℜ.α s bt a Jt := by
  have : 𝒮.eTilde s = (𝒮.stageOf s).eTilde (datum T ℜ s) r ℜ.α s :=
    funext (𝒮.eTilde_eq_stageOf s)
  show (⟨_, 𝒮.eTilde s, a, Jt, bt⟩ : DatumII.Raw _) =
    ⟨_, (𝒮.stageOf s).eTilde (datum T ℜ s) r ℜ.α s, a, Jt, bt⟩
  rw [this]

theorem Frame.jBarStar_eq_stageOf (𝒮 : Frame hS) (s : ℕ) :
    𝒮.jBarStar s = (𝒮.stageOf s).jBarStar (datum T ℜ s) r ℜ.α s ℜ.b ν 𝒮.bBar := by
  unfold Frame.jBarStar FrameStage.jBarStar
  congr 2
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [𝒮.eTilde_eq_stageOf s j]
  congr 1
  unfold cT
  rw [← coe_idxT r ℜ.α s j]
  exact (aAt_datum_eq_aSeq T ℜ s (idxT ℜ.α s r j)).symm

theorem Frame.kOf_eq_stageOf_aux (𝒮 : Frame hS) (s : ℕ) :
    (if ℜ.b ≤ ν then 𝒮.jBar s else 𝒮.jBarStar s) =
      (𝒮.stageOf s).kOf (datum T ℜ s) r ℜ.α s ℜ.b ν := by
  unfold FrameStage.kOf
  rw [𝒮.jBarStar_eq_stageOf s]
  rfl

variable [IsRegularLocalRing (AB.Shat X x₀)] {z : AB.Shat X x₀} {jGen : Set (AB.Shat X x₀)}
  {fr : FrameSpec N x₀ ℜ r ν z jGen}

theorem Frame.canon_stageOf_zero :
    (Frame.canon hS z jGen fr).stageOf 0 = FrameStage.initial x₀ (hS.ambient.2.1 x₀) z jGen :=
  rfl

theorem Frame.canon_stageOf_succ_xHat (s : ℕ) :
    ((Frame.canon hS z jGen fr).stageOf (s + 1)).xHat =
      (((Frame.canon hS z jGen fr).stageOf s).step ν.factorial
        (T.monoidalTransformation s)).xHat := by
  cases s <;> rfl

theorem Frame.canon_stageOf_succ_c (s : ℕ) :
    HEq ((Frame.canon hS z jGen fr).stageOf (s + 1)).c
      (((Frame.canon hS z jGen fr).stageOf s).step ν.factorial (T.monoidalTransformation s)).c := by
  cases s <;> rfl

theorem Frame.canon_stageOf_succ_xBar (s : ℕ) :
    HEq ((Frame.canon hS z jGen fr).stageOf (s + 1)).xBar
      (((Frame.canon hS z jGen fr).stageOf s).step ν.factorial
        (T.monoidalTransformation s)).xBar := by
  cases s <;> rfl

theorem Frame.canon_fBar_heq (s : ℕ) :
    HEq ((Frame.canon hS z jGen fr).fBar s)
      (((T.monoidalTransformation s).baseChange
        ((Frame.canon hS z jGen fr).stageOf s).c).strictTransformMap
        ((Frame.canon hS z jGen fr).xBar s)) := by
  cases s <;> rfl

theorem Frame.canon_bBarOn_stageOf (s : ℕ) :
    (Frame.canon hS z jGen fr).bBarOn s =
      ((Frame.canon hS z jGen fr).stageOf s).bBarOn (T.B s) := by
  cases s <;> rfl

theorem Frame.canon_stageOf_succ_jBar (s : ℕ) :
    HEq ((Frame.canon hS z jGen fr).stageOf (s + 1)).jBar
      (((Frame.canon hS z jGen fr).stageOf s).step ν.factorial
        (T.monoidalTransformation s)).jBar := by
  have hb := Frame.canon_bBarOn_stageOf (hS := hS) (fr := fr) s
  have hf := Frame.canon_fBar_heq (hS := hS) (fr := fr) s
  have e2 : (Frame.canon hS z jGen fr).jBar (s + 1) =
      Subscheme.divPow (Subscheme.totalTransform ((Frame.canon hS z jGen fr).fBar s)
        ((Frame.canon hS z jGen fr).jBar s))
        (Subscheme.totalTransform ((Frame.canon hS z jGen fr).fBar s)
          ((Frame.canon hS z jGen fr).bBarOn s)) ν.factorial := by
    show Subscheme.divPow _ ((Frame.canon hS z jGen fr).pBar s) _ = _
    rw [Frame.pBar_eq]
    rfl
  cases s with
  | zero =>
    apply heq_of_eq
    have hf := eq_of_heq hf
    exact e2.trans (divPow_totalTransform_congr hf rfl hb ν.factorial)
  | succ s =>
    apply heq_of_eq
    have hf := eq_of_heq hf
    have h1 := divPow_totalTransform_congr hf
      (J := (Frame.canon hS z jGen fr).jBar (s + 1))
      (J' := (Frame.canon hS z jGen fr).jBar (s + 1)) rfl hb ν.factorial
    have A : ((Frame.canon hS z jGen fr).stageOf (s + 1 + 1)).jBar = _ := e2
    have B := ((Frame.canon hS z jGen fr).stageOf (s + 1)).step_jBar ν.factorial
      (T.monoidalTransformation (s + 1))
    refine A.trans ?_
    refine h1.trans ?_
    exact B.symm

theorem Frame.canon_stageOf_succ (s : ℕ) :
    (Frame.canon hS z jGen fr).stageOf (s + 1) =
      ((Frame.canon hS z jGen fr).stageOf s).step ν.factorial (T.monoidalTransformation s) :=
  FrameStage.ext_of_heq (Frame.canon_stageOf_succ_xHat s) (Frame.canon_stageOf_succ_c s)
    (Frame.canon_stageOf_succ_xBar s) (Frame.canon_stageOf_succ_jBar s)

theorem Frame.canon_stageOf_eq_fold (s : ℕ) :
    (Frame.canon hS z jGen fr).stageOf s =
      FrameStage.fold ν.factorial (T.pre s) (FrameStage.initial x₀ (hS.ambient.2.1 x₀) z jGen) := by
  induction s with
  | zero => exact Frame.canon_stageOf_zero
  | succ s ih =>
    rw [Frame.canon_stageOf_succ, ih]
    exact (FrameStage.fold_snoc ν.factorial (T.pre s) (T.monoidalTransformation s) _).symm

theorem Frame.canon_stageOf_eq_fold_of_pre_eq {Y : Scheme.{u}} (g : MonoidalSuccession X Y)
    (n : ℕ) (h : T.X n = Y) (hpre : h ▸ T.pre n = g) :
    h ▸ (Frame.canon hS z jGen fr).stageOf n =
      FrameStage.fold ν.factorial g (FrameStage.initial x₀ (hS.ambient.2.1 x₀) z jGen) := by
  subst h
  subst hpre
  exact Frame.canon_stageOf_eq_fold n

end Bridge

section T3Block

section FormalFibreRing

variable {A B : Type u} [CommRing A] [CommRing B] [IsLocalRing A] [IsLocalRing B]
  [IsDomain A] [IsDomain B] [IsNoetherianRing B] [Algebra A B] [Module.Flat A B]
  [IsLocalHom (algebraMap A B)]

omit [IsDomain A] in
/-- For a flat local homomorphism `A → B` into a Noetherian local domain whose maximal ideal is
principal, `ht m_A ≤ 1` (going down). -/
theorem height_maximalIdeal_le_one_of_flat_of_principal (π : B)
    (hπ : maximalIdeal B = Ideal.span {π}) (hinj : Function.Injective (algebraMap A B)) :
    (maximalIdeal A).height ≤ 1 := by
  have hB : (maximalIdeal B).height ≤ ((1 : ℕ) : ℕ∞) := by
    have : (maximalIdeal B).IsPrincipal := ⟨⟨π, hπ⟩⟩
    refine Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes (maximalIdeal B) _ ?_
    exact ⟨⟨inferInstance, le_rfl⟩, fun q hq hqle => hq.2⟩
  have hunder : (maximalIdeal B).LiesOver (maximalIdeal A) := ⟨by
    rw [Ideal.under_def]
    exact (IsLocalRing.maximalIdeal_comap (algebraMap A B)).symm⟩
  suffices h : (maximalIdeal A).height ≤ ((1 : ℕ) : ℕ∞) by simpa using h
  rw [Ideal.height_le_iff]
  rw [Ideal.height_le_iff] at hB
  intro q hq hqlt
  by_contra hcon
  have hq0 : q ≠ ⊥ := fun h => by
    rw [h, Ideal.height_bot] at hcon
    exact hcon (by exact_mod_cast zero_lt_one)
  obtain ⟨Q, hQlt, hQ, hQo⟩ := Ideal.exists_ideal_lt_liesOver_of_lt (R := A) (S := B)
    (maximalIdeal B) hqlt
  have hQ0 : Q ≠ ⊥ := by
    rintro rfl
    apply hq0
    rw [hQo.over, Ideal.under_def]
    exact Ideal.comap_bot_of_injective _ hinj
  have := hB Q hQ hQlt
  have h0 : Q.height = 0 := by
    have : Q.height < ((1 : ℕ) : ℕ∞) := this
    simpa using this
  exact hQ0 (Ideal.height_eq_zero_iff_eq_bot.mp h0)

/-- If `B` is a Noetherian local domain with principal maximal ideal `(π)`, `π ≠ 0`, and `I ≠ 0`
is a proper ideal with `B/I` a domain, then `I = (π)`. -/
theorem eq_span_of_isDomain_quotient (π : B) (hπ : maximalIdeal B = Ideal.span {π})
    (hπ0 : π ≠ 0) (I : Ideal B) (hI0 : I ≠ ⊥) (hIle : I ≤ maximalIdeal B)
    (hdom : IsDomain (B ⧸ I)) : I = Ideal.span {π} := by
  have hprin : (maximalIdeal B).IsPrincipal := ⟨⟨π, hπ⟩⟩
  obtain ⟨n, hn⟩ := exists_maximalIdeal_pow_eq_of_principal B hprin I hI0
  have hπu : ¬ IsUnit π := by
    intro hu
    have : π ∈ maximalIdeal B := hπ ▸ Ideal.mem_span_singleton_self π
    exact this hu
  rw [hπ, Ideal.span_singleton_pow] at hn
  rcases Nat.lt_trichotomy n 1 with h0 | h1 | h2
  · obtain rfl : n = 0 := by omega
    rw [pow_zero, Ideal.span_singleton_one] at hn
    exact absurd (hn ▸ hIle) (by
      intro h
      exact (maximalIdeal.isMaximal B).ne_top (top_le_iff.mp h))
  · subst h1
    simpa using hn
  · exfalso
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
    have hmk : (Ideal.Quotient.mk I π) * (Ideal.Quotient.mk I (π ^ (m + 1))) = 0 := by
      rw [← map_mul, Ideal.Quotient.eq_zero_iff_mem, hn, ← pow_succ']
      exact Ideal.mem_span_singleton_self _
    rcases mul_eq_zero.mp hmk with h | h
    · rw [Ideal.Quotient.eq_zero_iff_mem, hn, Ideal.mem_span_singleton] at h
      obtain ⟨c, hc⟩ := h
      apply hπu
      have h1 : π * 1 = π * (π ^ (m + 1) * c) := by
        calc π * 1 = π := mul_one π
          _ = π ^ (m + 2) * c := hc
          _ = π * (π ^ (m + 1) * c) := by ring
      have h2 := mul_left_cancel₀ hπ0 h1
      exact IsUnit.of_mul_eq_one (π ^ m * c) (by linear_combination (-1 : B) * h2)
    · rw [Ideal.Quotient.eq_zero_iff_mem, hn, Ideal.mem_span_singleton] at h
      obtain ⟨c, hc⟩ := h
      apply hπu
      have h1 : π ^ (m + 1) * 1 = π ^ (m + 1) * (π * c) := by
        calc π ^ (m + 1) * 1 = π ^ (m + 1) := mul_one _
          _ = π ^ (m + 2) * c := hc
          _ = π ^ (m + 1) * (π * c) := by ring
      have h2 := mul_left_cancel₀ (pow_ne_zero _ hπ0) h1
      exact IsUnit.of_mul_eq_one c (by linear_combination (-1 : B) * h2)

/-- **Formal fibre of the regular case.**  Let `A → B` be a flat local homomorphism of local
domains, `B` Noetherian with principal maximal ideal `(π)`, and suppose that `B/(m_A B)` is a
domain.  If `J ≠ 0` is an ideal of `A` with `J B = (π^ν)`, `ν ≥ 1`, then `J ⊆ m_A^ν` and
`ht m_A = 1`. -/
theorem le_maximalIdeal_pow_of_map_eq_span_pow (π : B)
    (hπ : maximalIdeal B = Ideal.span {π}) (hπ0 : π ≠ 0) (J : Ideal A) (ν : ℕ) (hν : 1 ≤ ν)
    (hJ0 : J ≠ ⊥) (hJB : J.map (algebraMap A B) = Ideal.span {π ^ ν})
    (hdom : IsDomain (B ⧸ (maximalIdeal A).map (algebraMap A B))) :
    J ≤ maximalIdeal A ^ ν ∧ (maximalIdeal A).height = 1 := by
  have hff : Module.FaithfullyFlat A B := Module.FaithfullyFlat.of_flat_of_isLocalHom
  have hinj : Function.Injective (algebraMap A B) :=
    (RingHom.faithfullyFlat_algebraMap_iff (R := A) (S := B)).mpr hff |>.injective
  -- `J ⊆ m_A`
  have hJm : J ≤ maximalIdeal A := by
    intro a ha
    have h1 : algebraMap A B a ∈ Ideal.span {π ^ ν} := hJB ▸ Ideal.mem_map_of_mem _ ha
    have h2 : algebraMap A B a ∈ maximalIdeal B := by
      refine (Ideal.span_singleton_le_iff_mem _ |>.mpr ?_) h1
      rw [hπ]
      exact Ideal.pow_mem_of_mem _ (Ideal.mem_span_singleton_self π) ν (by omega)
    exact (IsLocalRing.maximalIdeal_comap (algebraMap A B)) ▸ h2
  have hmA0 : maximalIdeal A ≠ ⊥ := fun h => hJ0 (le_bot_iff.mp (h ▸ hJm))
  -- the maximal ideal of `B` is `m_A B`
  have hI0 : (maximalIdeal A).map (algebraMap A B) ≠ ⊥ := by
    intro h
    rw [Ideal.map_eq_bot_iff_le_ker, (RingHom.injective_iff_ker_eq_bot _).mp hinj] at h
    exact hmA0 (le_bot_iff.mp h)
  have hIle : (maximalIdeal A).map (algebraMap A B) ≤ maximalIdeal B :=
    IsLocalRing.map_maximalIdeal_le _
  have hI := eq_span_of_isDomain_quotient π hπ hπ0 _ hI0 hIle hdom
  refine ⟨?_, ?_⟩
  · have h1 : J.map (algebraMap A B) = ((maximalIdeal A) ^ ν).map (algebraMap A B) := by
      rw [hJB, Ideal.map_pow, hI, Ideal.span_singleton_pow]
    calc J ≤ (J.map (algebraMap A B)).comap (algebraMap A B) := Ideal.le_comap_map
      _ = (((maximalIdeal A) ^ ν).map (algebraMap A B)).comap (algebraMap A B) := by rw [h1]
      _ = maximalIdeal A ^ ν := Ideal.comap_map_eq_self_of_faithfullyFlat _
  · refine le_antisymm (height_maximalIdeal_le_one_of_flat_of_principal π hπ hinj) ?_
    exact Order.one_le_iff_ne_zero.mpr fun h => hmA0 (Ideal.height_eq_zero_iff_eq_bot.mp h)

end FormalFibreRing

variable {N : ℕ} {X : Scheme.{u}} {ℜ : DatumII.Raw X} {r : Restriction X} {ν : ℕ}
  {T : AB.Tower X} {x₀ : X} {hS : Standing N ℜ r ν T x₀} (𝒮 : Frame hS)

/-- `(z)` is a prime ideal of `Ŝ_0`, and `z` is a non-zero member of the maximal ideal. -/
theorem Frame.isPrime_span_z_and_ne_zero_and_mem_maximalIdeal
    [IsRegularLocalRing (AB.Shat X x₀)] :
    (Ideal.span {𝒮.z}).IsPrime ∧ 𝒮.z ≠ 0 ∧ 𝒮.z ∈ maximalIdeal (AB.Shat X x₀) := by
  classical
  obtain ⟨Fr, h1, hz, hF, ⟨kk, hkk, y, e, hc, hy, hrsop⟩, -⟩ := 𝒮.frame
  have hzmem : 𝒮.z ∈ insert 𝒮.z (Finset.image (fun i => algebraMap Fr.S (AB.Shat X x₀) (y i))
      Finset.univ) := Finset.mem_insert_self _ _
  have hzM : 𝒮.z ∈ maximalIdeal (AB.Shat X x₀) := hrsop.1 ▸ Ideal.subset_span hzmem
  have hext : ExtendsToRSOP (AB.Shat X x₀) {𝒮.z} :=
    ⟨_, Finset.singleton_subset_iff.mpr hzmem, hrsop⟩
  have hz0 : 𝒮.z ≠ 0 := hext.ne_zero (Finset.mem_singleton_self _)
  have hreg : IsRegularLocalRing (AB.Shat X x₀ ⧸ Ideal.span {𝒮.z}) :=
    hext.isRegularLocalRing_quotient_span_singleton (Finset.mem_singleton_self _)
  have : IsDomain (AB.Shat X x₀ ⧸ Ideal.span {𝒮.z}) := isDomain_of_isRegularLocalRing _
  exact ⟨(Ideal.Quotient.isDomain_iff_prime _).mp this, hz0, hzM⟩

open AB in
/-- If the stalk of `J̄(0)` at a point of `X̄_0 = V(z)` is zero, every generator of `J̄_0` lies in
`(z)Ŝ` (generic form: only `z` and the set `jGen` of generators intervene). -/
theorem mem_span_z_of_stalkIdeal_jBar0_eq_bot (x₀ : X) (z : Shat X x₀) (jGen : Set (Shat X x₀))
    (hzprime : (Ideal.span {z}).IsPrime) (xb : (vZ X x₀ z).toScheme)
    (h : (Subscheme.totalTransform (vZ X x₀ z).ι (Scheme.IdealSheafData.ofIdealTop
      ((Ideal.span jGen).map (Scheme.ΓSpecIso (CommRingCat.of (Shat X x₀))).inv.hom))).stalkIdeal
        xb = ⊥) : ∀ y ∈ jGen, y ∈ Ideal.span {z} := by
  classical
  set xh : xHat0 X x₀ := (vZ X x₀ z).ι.base xb with hxh
  let Pr : PrimeSpectrum (Shat X x₀) := xh
  let Pi : Ideal (Shat X x₀) := Pr.asIdeal
  have : Pi.IsPrime := Pr.isPrime
  have hzP : z ∈ Pi := by
    have hmem : xh ∈ (vZ X x₀ z).pts := Subscheme.mem_pts_ι (vZ X x₀ z) xb
    have := (mem_pts_ofIdealTop_spec (CommRingCat.of (Shat X x₀)) (Ideal.span {z}) xh).mp hmem
    exact this (Ideal.mem_span_singleton_self _)
  let e : Localization.AtPrime Pi ≃+* (xHat0 X x₀).presheaf.stalk xh :=
    (Spec.stalkIso (CommRingCat.of (Shat X x₀)) Pr).symm.commRingCatIsoToRingEquiv
  have hX0 : (vZ X x₀ z).stalkIdeal xh = Ideal.span {e (algebraMap _ _ z)} := by
    have h2 := stalkIdeal_ofIdealTop_spec (CommRingCat.of (Shat X x₀)) (Ideal.span {z}) Pr
    refine Eq.trans (show Subscheme.stalkIdeal (vZ X x₀ z) xh = _ from h2) ?_
    rw [Ideal.map_span, Set.image_singleton, Ideal.map_span, Set.image_singleton]
    rfl
  let O : Subscheme (xHat0 X x₀) := Scheme.IdealSheafData.ofIdealTop ((Ideal.span jGen).map
      (Scheme.ΓSpecIso (CommRingCat.of (Shat X x₀))).inv.hom)
  have hO : Subscheme.stalkIdeal O xh =
      ((Ideal.span jGen).map (algebraMap (Shat X x₀) (Localization.AtPrime Pi))).map e :=
    stalkIdeal_ofIdealTop_spec (CommRingCat.of (Shat X x₀)) (Ideal.span jGen) Pr
  set φ := ((vZ X x₀ z).ι.stalkMap xb).hom with hφ
  have hJ : (Subscheme.totalTransform (vZ X x₀ z).ι O).stalkIdeal xb = (O.stalkIdeal xh).map φ := by
    rw [stalkIdeal_totalTransform]
  have hφker : RingHom.ker φ = Ideal.span {e (algebraMap _ _ z)} := by
    rw [← hX0]
    exact (stalkIdeal_eq_ker_stalkMap (vZ X x₀ z) xb).symm
  intro y hy
  have hy1 : e (algebraMap _ _ y) ∈ O.stalkIdeal xh := by
    rw [hO]
    exact Ideal.mem_map_of_mem _ (Ideal.mem_map_of_mem _ (Ideal.subset_span hy))
  have hy2 : φ (e (algebraMap _ _ y)) ∈
      (Subscheme.totalTransform (vZ X x₀ z).ι O).stalkIdeal xb := by
    rw [hJ]
    exact Ideal.mem_map_of_mem _ hy1
  rw [h, Ideal.mem_bot] at hy2
  have hy3 : e (algebraMap _ _ y) ∈ RingHom.ker φ := hy2
  rw [hφker, Ideal.mem_span_singleton] at hy3
  obtain ⟨c, hc⟩ := hy3
  have hy4 : algebraMap (Shat X x₀) (Localization.AtPrime Pi) y ∈
      (Ideal.span {z}).map (algebraMap (Shat X x₀) (Localization.AtPrime Pi)) := by
    rw [Ideal.map_span, Set.image_singleton, Ideal.mem_span_singleton]
    exact ⟨e.symm c, by
      apply e.injective
      rw [map_mul, RingEquiv.apply_symm_apply]
      exact hc⟩
  have hdisj : Disjoint (Pi.primeCompl : Set (Shat X x₀)) (Ideal.span {z} : Set (Shat X x₀)) :=
    Set.disjoint_left.mpr fun a ha haz =>
      ha ((Ideal.span_singleton_le_iff_mem Pi).mpr hzP haz)
  have := IsLocalization.under_map_of_isPrime_disjoint Pi.primeCompl (Localization.AtPrime Pi)
    hzprime hdisj
  rw [← this]
  exact hy4

/-- If all the generators `g_{ji}^{b̄/i}` of `J̄` lie in `(z)Ŝ`, then all the coefficients `g_{ji}`
vanish, so `g_j = z^ν` and `Ĵ_0 = (z^ν)`. -/
theorem Frame.jHat0_eq_span_pow_of_jGen_subset [IsRegularLocalRing (AB.Shat X x₀)]
    (hJ0 : ℜ.J.stalkIdeal x₀ ≠ ⊥)
    (hinjα : Function.Injective (algebraMap (X.presheaf.stalk x₀) (AB.Shat X x₀)))
    (H : ∀ y ∈ 𝒮.jGen, y ∈ Ideal.span {𝒮.z}) :
    jHat0 ℜ x₀ = Ideal.span {𝒮.z ^ ν} := by
  classical
  obtain ⟨hzprime, hz0, hzM⟩ := 𝒮.isPrime_span_z_and_ne_zero_and_mem_maximalIdeal
  obtain ⟨Fr, h1, hFz, hF, hii, m, g, co, hspan, hord, hform, hunr, hjGen⟩ := 𝒮.frame
  have hrange : Set.range Fr.z = {𝒮.z} := by
    ext a
    constructor
    · rintro ⟨i, rfl⟩
      have : i = ⟨0, by rw [h1]; exact Nat.one_pos⟩ := Fin.ext (by have := i.2; omega)
      rw [this, hFz]; rfl
    · rintro rfl
      exact ⟨⟨0, by rw [h1]; exact Nat.one_pos⟩, hFz⟩
  have hinj : Function.Injective ((Ideal.Quotient.mk (Ideal.span (Set.range Fr.z))).comp
      (algebraMap Fr.S (AB.Shat X x₀))) := Fr.quot_bijective.1
  have : IsDomain Fr.S := isDomain_of_isRegularLocalRing Fr.S
  have hco : ∀ j i, co j i = 0 := by
    intro j i
    have hy : algebraMap Fr.S (AB.Shat X x₀) (co j i) ^ (ν.factorial / ((i : ℕ) + 1)) ∈ 𝒮.jGen := by
      rw [hjGen]; exact ⟨j, i, rfl⟩
    have hy' := H _ hy
    rw [← map_pow] at hy'
    have h0 : ((Ideal.Quotient.mk (Ideal.span (Set.range Fr.z))).comp
        (algebraMap Fr.S (AB.Shat X x₀))) (co j i ^ (ν.factorial / ((i : ℕ) + 1))) =
        ((Ideal.Quotient.mk (Ideal.span (Set.range Fr.z))).comp
          (algebraMap Fr.S (AB.Shat X x₀))) 0 := by
      rw [map_zero, RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem, hrange]
      exact hy'
    have h2 := hinj h0
    rcases Nat.eq_zero_or_pos (ν.factorial / ((i : ℕ) + 1)) with he | he
    · rw [he, pow_zero] at h2
      exact absurd h2 one_ne_zero
    · exact pow_eq_zero_iff he.ne' |>.mp h2
  have hg : ∀ j, g j = 𝒮.z ^ ν := fun j => by
    rw [hform j]
    simp [hco]
  rw [← hspan]
  rcases Nat.eq_zero_or_pos m with hm | hm
  · exfalso
    subst hm
    apply hJ0
    have h3 : jHat0 ℜ x₀ = ⊥ := by
      rw [← hspan]; simp
    unfold jHat0 at h3
    rw [Ideal.map_eq_bot_iff_le_ker, (RingHom.injective_iff_ker_eq_bot _).mp hinjα] at h3
    exact le_bot_iff.mp h3
  · have : Set.range g = {𝒮.z ^ ν} := by
      ext a
      constructor
      · rintro ⟨j, rfl⟩
        exact hg j
      · rintro rfl
        exact ⟨⟨0, hm⟩, hg _⟩
    rw [this]

open AB in
/-- **Gap filled (p. 321).**  If all the generators of `J̄` lie in `(z)Ŝ`, a contradiction with
`S_ν(ℜ)` having no component of codimension one.  The hypothesis `hSmem` says that the points of
`F` (resp. of `X`, without restriction) of order `≥ ν` belong to `S(ℜ^N_II)`: it holds if
`b ≤ ν`, and in the closed case also if `b ≤ ν + Σ_{F ⊆ E_i} a_i` (the repaired case `ν < b`,
`F = E_i`). -/
theorem Frame.false_of_jGen_subset_span_z [Hironaka.HironakaCitedResults.{u}] [IsRegularLocalRing (Shat X x₀)]
    (hSmem : ∀ y : X, (ν : ℕ∞) ≤ ℜ.nuAt y → (∀ F, r = .closed F → y ∈ F.pts) → y ∈ ℜ.S)
    (H : ∀ y ∈ 𝒮.jGen, y ∈ Ideal.span {𝒮.z}) : False := by
  classical
  have hx0 := hS.ambient.2.1 x₀
  have : IsRegularLocalRing (X.presheaf.stalk x₀) := hx0
  have : IsAlgebraicScheme X := hS.ambient.1
  have : IsHironakaBase (X.presheaf.stalk x₀) := isHironakaBase_stalk X x₀
  obtain ⟨hzprime, hz0, hzM⟩ := 𝒮.isPrime_span_z_and_ne_zero_and_mem_maximalIdeal
  have : IsDomain (Shat X x₀) := isDomain_of_isRegularLocalRing _
  let α := algebraMap (X.presheaf.stalk x₀) (Shat X x₀)
  have hinj : Function.Injective α :=
    RingHom.MapsRSOP.injective α mapsRSOP_algebraMap_adicCompletion
  have hJ0 : ℜ.J.stalkIdeal x₀ ≠ ⊥ := hS.isDatum.2.2.2 x₀
  have hJhat : jHat0 ℜ x₀ = Ideal.span {𝒮.z ^ ν} := 𝒮.jHat0_eq_span_pow_of_jGen_subset hJ0 hinj H
  have hν1 : 1 ≤ ν := hS.nu_pos
  -- the point `ŷ = (z)` of `X̂_0` and its image `y` in `X`
  let ŷ : xHat0 X x₀ := (⟨Ideal.span {𝒮.z}, hzprime⟩ : PrimeSpectrum (Shat X x₀))
  have hŷ : (show PrimeSpectrum (Shat X x₀) from ŷ).asIdeal = Ideal.span {𝒮.z} := rfl
  have hptsJ : ∀ Q : xHat0 X x₀, Q ∈ (Subscheme.totalTransform (c0 X x₀) ℜ.J).pts ↔
      𝒮.z ∈ (show PrimeSpectrum (Shat X x₀) from Q).asIdeal := by
    intro Q
    rw [mem_pts_totalTransform_c0_iff]
    change jHat0 ℜ x₀ ≤ _ ↔ _
    rw [hJhat, Ideal.span_singleton_le_iff_mem]
    exact (show PrimeSpectrum (Shat X x₀) from Q).isPrime.pow_mem_iff_mem ν hν1
  have hŷJ : ŷ ∈ (Subscheme.totalTransform (c0 X x₀) ℜ.J).pts :=
    (hptsJ ŷ).mpr (by rw [hŷ]; exact Ideal.mem_span_singleton_self _)
  have hyJ : (c0 X x₀).base ŷ ∈ ℜ.J.pts := by
    rw [Subscheme.pts_totalTransform_eq_preimage] at hŷJ
    exact hŷJ
  have hflat : Flat (c0 X x₀) := flat_c0 X x₀ hx0
  have hmin : ∀ y' ∈ ℜ.J.pts, y' ⤳ (c0 X x₀).base ŷ → y' = (c0 X x₀).base ŷ := by
    intro y' hy'J hy'y
    obtain ⟨ŷ', hŷ'ŷ, hcŷ'⟩ := Flat.generalizingMap (c0 X x₀) hy'y
    have hŷ'mem : ŷ' ∈ (Subscheme.totalTransform (c0 X x₀) ℜ.J).pts := by
      rw [Subscheme.pts_totalTransform_eq_preimage]
      show (c0 X x₀).base ŷ' ∈ ℜ.J.pts
      rw [hcŷ']
      exact hy'J
    have hz' := (hptsJ ŷ').mp hŷ'mem
    have hle : (show PrimeSpectrum (Shat X x₀) from ŷ') ≤
        (show PrimeSpectrum (Shat X x₀) from ŷ) :=
      (PrimeSpectrum.le_iff_specializes _ _).mpr hŷ'ŷ
    have heq : (show PrimeSpectrum (Shat X x₀) from ŷ') =
        (show PrimeSpectrum (Shat X x₀) from ŷ) :=
      PrimeSpectrum.ext (le_antisymm hle ((Ideal.span_singleton_le_iff_mem _).mpr hz'))
    rw [← hcŷ']
    exact congrArg (c0 X x₀).base heq
  -- the reduced closure `D` of the point `y`
  set y : X := (c0 X x₀).base ŷ with hy
  let D : Subscheme X := Subscheme.ofClosed ⟨closure {y}, isClosed_closure⟩
  have hDred : D.IsReduced := Subscheme.ofClosed_isReduced _
  have hDpts : D.pts = closure {y} := Subscheme.pts_ofClosed _
  have hyD : y ∈ D.pts := by rw [hDpts]; exact subset_closure rfl
  have hDy : D.stalkIdeal y = maximalIdeal (X.presheaf.stalk y) := by
    refine Subscheme.stalkIdeal_eq_maximalIdeal_of_forall_specializes hDred hyD ?_
    intro y' hy'D hy'y
    rw [hDpts] at hy'D
    exact ((specializes_iff_mem_closure.mpr hy'D).antisymm hy'y).eq.symm
  have hreg : IsRegularLocalRing (X.presheaf.stalk y ⧸ D.stalkIdeal y) := by
    have hfield : IsRegularLocalRing (X.presheaf.stalk y ⧸ maximalIdeal (X.presheaf.stalk y)) := by
      let _ : Field (X.presheaf.stalk y ⧸ maximalIdeal (X.presheaf.stalk y)) :=
        Ideal.Quotient.field _
      infer_instance
    exact IsRegularLocalRing.of_ringEquiv (Ideal.quotEquivOfEq hDy.symm)
  have hH : IsPullback (c0 X x₀) (𝟙 (xHat0 X x₀)) (𝟙 X)
      (Spec.map (CommRingCat.ofHom (algebraMap (X.presheaf.stalk x₀) (Shat X x₀))) ≫
        X.fromSpecStalk x₀) :=
    IsPullback.of_vert_isIso ⟨by simp [c0]⟩
  have hK5 := isRegularLocalRing_quotient_stalk_totalTransform_of_isPullback_completion x₀ (𝟙 X)
    (c0 X x₀) (𝟙 (xHat0 X x₀)) hH D ŷ hreg
  -- the local rings `A = O_{X,y}` and `B = O_{X̂_0,ŷ} ≃ Ŝ_{(z)}`
  let Pi : Ideal (Shat X x₀) := (show PrimeSpectrum (Shat X x₀) from ŷ).asIdeal
  have hPi : Pi = Ideal.span {𝒮.z} := rfl
  have : Pi.IsPrime := (show PrimeSpectrum (Shat X x₀) from ŷ).isPrime
  let e : Localization.AtPrime Pi ≃+* (xHat0 X x₀).presheaf.stalk ŷ :=
    (Spec.stalkIso (CommRingCat.of (Shat X x₀))
      (show PrimeSpectrum (Shat X x₀) from ŷ)).symm.commRingCatIsoToRingEquiv
  set πL : Localization.AtPrime Pi := algebraMap (Shat X x₀) (Localization.AtPrime Pi) 𝒮.z
    with hπL
  have hπL0 : πL ≠ 0 := fun h => hz0 (IsLocalization.injective (Localization.AtPrime Pi)
    (Ideal.primeCompl_le_nonZeroDivisors Pi) (h.trans (map_zero _).symm))
  have hmaxL : maximalIdeal (Localization.AtPrime Pi) = Ideal.span {πL} := by
    rw [← IsLocalization.AtPrime.map_eq_maximalIdeal Pi (Localization.AtPrime Pi)]
    change Ideal.map (algebraMap (Shat X x₀) (Localization.AtPrime Pi)) (Ideal.span {𝒮.z}) = _
    rw [Ideal.map_span, Set.image_singleton]
  have : IsNoetherianRing (Shat X x₀) := inferInstance
  have : IsNoetherianRing (Localization.AtPrime Pi) :=
    IsLocalization.isNoetherianRing Pi.primeCompl _ inferInstance
  have : IsDomain ((xHat0 X x₀).presheaf.stalk ŷ) :=
    MulEquiv.isDomain (Localization.AtPrime Pi) e.symm.toMulEquiv
  have : IsNoetherianRing ((xHat0 X x₀).presheaf.stalk ŷ) :=
    isNoetherianRing_of_ringEquiv (Localization.AtPrime Pi) e
  set π : (xHat0 X x₀).presheaf.stalk ŷ := e πL with hπ
  have hπ0 : π ≠ 0 := fun h => hπL0 (e.injective (h.trans (map_zero e).symm))
  have hmaxB : maximalIdeal ((xHat0 X x₀).presheaf.stalk ŷ) = Ideal.span {π} := by
    ext b
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, Ideal.mem_span_singleton]
    constructor
    · intro hb
      have : e.symm b ∈ maximalIdeal (Localization.AtPrime Pi) := by
        rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
        exact fun hu => hb (by simpa using hu.map e)
      rw [hmaxL, Ideal.mem_span_singleton] at this
      obtain ⟨c, hc⟩ := this
      exact ⟨e c, by rw [hπ, ← map_mul, ← hc, RingEquiv.apply_symm_apply]⟩
    · rintro ⟨c, rfl⟩ hu
      have : IsUnit πL := by
        have := hu.map e.symm
        rw [map_mul, hπ, RingEquiv.symm_apply_apply] at this
        exact isUnit_of_mul_isUnit_left this
      exact ((IsLocalization.AtPrime.to_map_mem_maximal_iff (Localization.AtPrime Pi) Pi _).mpr
        (by rw [hPi]; exact Ideal.mem_span_singleton_self _) : πL ∈ maximalIdeal _) this
  -- the flat local homomorphism `A = O_{X,y} → B = O_{X̂_0,ŷ}`
  let _ : Algebra (X.presheaf.stalk y) ((xHat0 X x₀).presheaf.stalk ŷ) :=
    ((c0 X x₀).stalkMap ŷ).hom.toAlgebra
  have : Module.Flat (X.presheaf.stalk y) ((xHat0 X x₀).presheaf.stalk ŷ) :=
    Flat.stalkMap (c0 X x₀) ŷ
  have : IsLocalHom (algebraMap (X.presheaf.stalk y) ((xHat0 X x₀).presheaf.stalk ŷ)) :=
    inferInstanceAs (IsLocalHom ((c0 X x₀).stalkMap ŷ).hom)
  -- `J_y B = (π^ν)`
  have h1 : (Subscheme.totalTransform (c0 X x₀) ℜ.J).stalkIdeal ŷ =
      (ℜ.J.stalkIdeal y).map ((c0 X x₀).stalkMap ŷ).hom :=
    stalkIdeal_totalTransform (c0 X x₀) ℜ.J ŷ
  have h2 : (Subscheme.totalTransform (c0 X x₀) ℜ.J).stalkIdeal ŷ =
      Ideal.map (e : _ →+* _) (Ideal.map (algebraMap (Shat X x₀) (Localization.AtPrime Pi))
        (jHat0 ℜ x₀)) :=
    Frame.stalkIdeal_totalTransform_c0_stalkIso x₀ ℜ.J ŷ
  have h3 : Ideal.map (e : _ →+* _) (Ideal.map (algebraMap (Shat X x₀) (Localization.AtPrime Pi))
        (jHat0 ℜ x₀)) = Ideal.span {π ^ ν} := by
    rw [hJhat, Ideal.map_span, Set.image_singleton, map_pow, Ideal.map_span, Set.image_singleton]
    simp only [RingHom.coe_coe, hπ, hπL, map_pow]
  have hJB : (ℜ.J.stalkIdeal y).map (algebraMap (X.presheaf.stalk y)
      ((xHat0 X x₀).presheaf.stalk ŷ)) = Ideal.span {π ^ ν} := h1.symm.trans (h2.trans h3)
  have hJy0 : ℜ.J.stalkIdeal y ≠ ⊥ := by
    intro h
    rw [h, Ideal.map_bot] at hJB
    exact pow_ne_zero ν hπ0 (Ideal.span_singleton_eq_bot.mp hJB.symm)
  -- `B/(m_A B)` is a domain (class 𝔅, (K5))
  have hTD : (Subscheme.totalTransform (c0 X x₀) D).stalkIdeal ŷ =
      (maximalIdeal (X.presheaf.stalk y)).map (algebraMap (X.presheaf.stalk y)
        ((xHat0 X x₀).presheaf.stalk ŷ)) :=
    (stalkIdeal_totalTransform (c0 X x₀) D ŷ).trans (by rw [hDy]; rfl)
  have hdom : IsDomain ((xHat0 X x₀).presheaf.stalk ŷ ⧸
      (maximalIdeal (X.presheaf.stalk y)).map (algebraMap (X.presheaf.stalk y)
        ((xHat0 X x₀).presheaf.stalk ŷ))) := by
    have : IsRegularLocalRing ((xHat0 X x₀).presheaf.stalk ŷ ⧸
        (maximalIdeal (X.presheaf.stalk y)).map (algebraMap (X.presheaf.stalk y)
          ((xHat0 X x₀).presheaf.stalk ŷ))) :=
      IsRegularLocalRing.of_ringEquiv (Ideal.quotEquivOfEq hTD) 
    exact isDomain_of_isRegularLocalRing _
  have hy0 := hS.ambient.2.1 y
  have : IsRegularLocalRing (X.presheaf.stalk y) := hy0
  have : IsDomain (X.presheaf.stalk y) := isDomain_of_isRegularLocalRing _
  obtain ⟨hJle, hht⟩ := le_maximalIdeal_pow_of_map_eq_span_pow π hmaxB hπ0 (ℜ.J.stalkIdeal y) ν
    hν1 hJy0 hJB hdom
  -- `y ∈ S_ν(ℜ)`
  have hnu : (ν : ℕ∞) ≤ ℜ.nuAt y := Ideal.le_ord hJle
  have hsNu : y ∈ sNu ℜ r ν := by
    cases r with
    | unrestricted => exact ⟨hSmem y hnu (fun F hF => nomatch hF), hnu⟩
    | closed F =>
      obtain ⟨-, -, -, hF, -⟩ := 𝒮.frame
      obtain ⟨z₀, hz₀, hFz₀⟩ := hF F rfl
      have hŷF : ŷ ∈ (Subscheme.totalTransform (c0 X x₀) F).pts := by
        rw [mem_pts_totalTransform_c0_iff, hFz₀, Ideal.map_span, Set.image_singleton, hz₀]
      have hyF : y ∈ F.pts := by
        rw [Subscheme.pts_totalTransform_eq_preimage] at hŷF
        exact hŷF
      exact ⟨⟨hSmem y hnu (fun F' hF' => by cases hF'; exact hyF), hnu⟩, hyF⟩
  -- `closure {y}` is a maximal irreducible subset of `S_ν(ℜ)`, of codimension one
  have hclosed : IsClosed (sNu ℜ r ν) := by
    cases r with
    | unrestricted => exact LocSucc.isClosed_sNu hS.ambient.2.1 ℜ ν
    | closed F => exact (LocSucc.isClosed_sNu hS.ambient.2.1 ℜ ν).inter F.support.isClosed
  have hsubJ : sNu ℜ r ν ⊆ ℜ.J.pts := by
    intro x hx
    obtain ⟨-, hxν⟩ := (mem_Snu_iff ℜ r ν x).1 hx
    rw [Subscheme.mem_pts_iff_stalkIdeal_ne_top]
    intro htop
    have h1 : (1 : ℕ∞) ≤ ℜ.nuAt x := (Nat.one_le_cast.mpr hν1).trans hxν
    have h2 := (Ideal.ord_basic (maximalIdeal (X.presheaf.stalk x)) (ℜ.J.stalkIdeal x) ⊥ ⊥).2.1.mp
      h1
    exact (maximalIdeal.isMaximal _).ne_top (top_le_iff.mp (htop ▸ h2))
  have hmax : Maximal (fun Y : Set X => IsIrreducible Y ∧ Y ⊆ sNu ℜ r ν) (closure {y}) := by
    refine ⟨⟨isIrreducible_singleton.closure,
      closure_minimal (Set.singleton_subset_iff.mpr hsNu) hclosed⟩, ?_⟩
    rintro Y ⟨hYirr, hYsub⟩ hle
    obtain ⟨y', hy'⟩ := QuasiSober.sober hYirr.closure isClosed_closure
    have hy'S : y' ∈ sNu ℜ r ν := closure_minimal hYsub hclosed hy'.mem
    have hyY : y ∈ Y := hle (subset_closure rfl)
    have hyy' : y' ⤳ y := specializes_iff_mem_closure.mpr (by
      rw [hy'.def]; exact subset_closure hyY)
    have hyy : y' = y := hmin y' (hsubJ hy'S) hyy'
    intro w hw
    have : w ∈ closure {y'} := by rw [hy'.def]; exact subset_closure hw
    rwa [hyy] at this
  have hcodim := hS.noCodimOne _ hmax
  rw [codim_ofClosed_closure_eq_stalkHeight (η := y) (by rw [closure_closure])] at hcodim
  exact hcodim hht

/-- Non-vanishing of `J̄(0)` (`ν ≥ b`): otherwise all the generators of `J̄` lie in `(z)Ŝ`. -/
theorem Frame.stalkIdeal_jBar_zero_ne_bot [Hironaka.HironakaCitedResults.{u}]
    (hSmem : ∀ y : X, (ν : ℕ∞) ≤ ℜ.nuAt y → (∀ F, r = .closed F → y ∈ F.pts) → y ∈ ℜ.S)
    (xb : (𝒮.xBar 0).toScheme) :
    (𝒮.jBar 0).stalkIdeal xb ≠ ⊥ := by
  have := 𝒮.regShat
  intro h
  obtain ⟨hzprime, -, -⟩ := 𝒮.isPrime_span_z_and_ne_zero_and_mem_maximalIdeal
  exact 𝒮.false_of_jGen_subset_span_z hSmem
    (mem_span_z_of_stalkIdeal_jBar0_eq_bot x₀ 𝒮.z 𝒮.jGen hzprime xb h)

/-- The stalks of `J̄(t)` are non-zero for `t ≤ s` (`ν ≥ b`), when `X̄_t` is non-singular for
`t < s`: the stalk maps of `f̄_t` are injective at the points of `X̄_{t+1}` (`X̄_t` is regular
there), so the division by the `b̄`-th power of the exceptional divisor does not make a non-zero
stalk zero. -/
theorem Frame.stalkIdeal_jBar_ne_bot_of_forall_isNonsingular [Hironaka.HironakaCitedResults.{u}]
    (hSmem : ∀ y : X, (ν : ℕ∞) ≤ ℜ.nuAt y → (∀ F, r = .closed F → y ∈ F.pts) → y ∈ ℜ.S)
    {s : ℕ}
    (hns : ∀ t, t < s → (𝒮.xBar t).IsNonsingular) :
    ∀ t, t ≤ s → ∀ xb : (𝒮.xBar t).toScheme, (𝒮.jBar t).stalkIdeal xb ≠ ⊥
  | 0, _ => fun xb => 𝒮.stalkIdeal_jBar_zero_ne_bot hSmem xb
  | t + 1, ht => fun xb => by
    have hIH := stalkIdeal_jBar_ne_bot_of_forall_isNonsingular hSmem hns t (by omega)
      ((𝒮.fBar t).base xb)
    have : IsRegularLocalRing ((𝒮.xBar t).toScheme.presheaf.stalk ((𝒮.fBar t).base xb)) :=
      hns t (by omega) _
    have hinj := MonoidalTransformation.injective_stalkMap_strictTransform
      (𝒮.tHat.monoidalTransformation t) (𝒮.xBar t) (𝒮.fBar t) (𝒮.fBar_comm t) xb
    have hlp : (𝒮.pBar t).IsLocallyPrincipal :=
      (((T.monoidalTransformation t).invertible.isLocallyPrincipal.totalTransform
        (𝒮.c (t + 1))).totalTransform (𝒮.xBar (t + 1)).ι)
    show (Subscheme.divPow _ (𝒮.pBar t) 𝒮.bBar).stalkIdeal xb ≠ ⊥
    rw [Subscheme.stalkIdeal_divPow_of_isLocallyPrincipal hlp]
    intro h
    apply hIH
    rw [eq_bot_iff]
    intro a ha
    have h1 : ((𝒮.fBar t).stalkMap xb).hom a ∈
        (Subscheme.totalTransform (𝒮.fBar t) (𝒮.jBar t)).stalkIdeal xb := by
      rw [stalkIdeal_totalTransform]
      exact Ideal.mem_map_of_mem _ ha
    have h2 := Ideal.le_colon (S := ((((𝒮.pBar t).stalkIdeal xb ^ 𝒮.bBar : Ideal _)) : Set _)) h1
    rw [h, Submodule.mem_bot] at h2
    exact (Submodule.mem_bot _).mpr (hinj (h2.trans (map_zero _).symm))

end T3Block

section Lift

variable {N : ℕ} {X : Scheme.{u}}

/-- `b̃`: `b̄ = ν!` if `ν ≥ b` and `b̄(b - ν)` if `ν < b` (pp. 321, 322). -/
def btOf (b ν : ℕ) : ℕ := if b ≤ ν then ν.factorial else ν.factorial * (b - ν)

theorem btOf_pos (b ν : ℕ) : 0 < btOf b ν := by
  unfold btOf
  split_ifs with h
  · exact Nat.factorial_pos ν
  · exact Nat.mul_pos (Nat.factorial_pos ν) (by omega)

namespace Frame

variable {ℜ : DatumII.Raw X} {r : Restriction X} {ν : ℕ} {T : AB.Tower X} {x₀ : X}
  {hS : Standing N ℜ r ν T x₀} (𝒮 : Frame hS)

/-- `J̄(s)` if `ν ≥ b`, `J̄*(s)` if `ν < b`: the ideal sheaf of which `J̃ ∏ P̃_j^{ã_j}` is a
factorization (pp. 321, 322). -/
def kOf (s : ℕ) : Subscheme (𝒮.xTilde s) := if ℜ.b ≤ ν then 𝒮.jBar s else 𝒮.jBarStar s

/-- **`J̄(s)` has non-zero stalks** (`ν ≥ b`, p. 321).

\textbf{Deviation from the paper (gap filled).} The paper (p. 321): "We shall consider a resolution
datum `ℜ^{N-1}_II` on `X̃` of the following form" presupposes that `J̄(s)` has non-zero stalks,
which Definition 3 (II) (p. 165) requires of the sheaf of ideals of a resolution datum, and which
the paper never proves.  It is true because `S_ν(ℜ)` has no component of codimension one
(p. 314).  If the stalk of `J̄(0)` at a point of `X̄_0` vanished, all the generators of `J̄` would
lie in `(z)Ŝ_0`, so that `Ĵ_0 = (z^ν)` (`Frame.jHat0_eq_span_pow_of_jGen_subset`).  The prime
`(z)` of `Ŝ_0` lies over a point `y` of `X` with no proper generization in `V(J)` (generizations
lift along the flat map `S_0 → Ŝ_0`); by class 𝔅 (`(K5)`, applied to the reduced closure of `y`)
the local ring `Ŝ_{(z)}/(m_y Ŝ_{(z)})` is regular, hence a domain, which as `Ŝ_{(z)}` is a
discrete valuation ring gives `m_y Ŝ_{(z)} = (z)`; by faithful flatness `J_y ⊆ m_y^ν` and
`ht m_y = 1`.  As `ν ≥ b`, `y ∈ S_ν(ℜ)` (and `y ∈ F` in the closed case, since `F_{x_0}Ŝ_0 = (z)`),
so `closure {y}` is a component of `S_ν(ℜ)` of codimension one, contradicting p. 314.  For `s > 0`
the stalk maps of `f̄_t` are injective at the points of `X̄_{t+1}` (`X̄_t` is regular there), so the
division by the `b̄`-th power of the exceptional divisor does not make a non-zero stalk zero. -/
@[blueprint "lem:IV.4-jbar-nonzero"
  (statement := /-- Notation as in \cref{def:IV.4-frame} and \cref{def:IV.4-construction}, under the
    standing assumptions with $\nu\ge b$ and the hypotheses of \cref{lem:IV.4-x0}: the sheaf of
    ideals $\bar J(s)$ on $\tilde X=\bar X_s$ has non-zero stalks. (Needed for $\mathfrak
    R^{N-1}_{\mathrm{II}}$ to be a resolution datum, Definition~3 (II), p.~165.) -/)
  (proof := /-- If $\bar J(0)$ were zero at a point, all the generators $g_{jki}^{\bar b/i}$ would
    lie in $(z)\hat S_0$, so $\hat J_0=(z^\nu)$. The prime $(z)$ lies over a point $y$ of $X$
    without proper generization in $V(J)$; by class $\mathfrak B$ ($(\mathrm{K}5)$ for the reduced
    closure of $y$) the ring $\hat S_{(z)}/(\mathfrak m_y\hat S_{(z)})$ is regular, hence a
    domain, so $\mathfrak m_y\hat S_{(z)}=(z)$ ($\hat S_{(z)}$ is a discrete valuation ring); by
    faithful flatness $J_y\subseteq\mathfrak m_y^\nu$ and $\operatorname{ht}\mathfrak m_y=1$. Since
    $\nu\ge b$, $y\in S_\nu(\mathfrak R)$ (and $y\in F$ in the closed case, as $F_{x_0}\hat S_0=
    (z)$), so $\overline{\{y\}}$ is a component of $S_\nu(\mathfrak R)$ of codimension one,
    contradicting p.~314. For $s>0$,
    $\bar J(s+1)=\bar f_s^{-1}(\bar J(s))\cdot\bar P_{s+1}^{-\bar b}$ and the stalk maps of
    $\bar f_s$ are injective at the points of $\bar X_{s+1}$.

    \textbf{Deviation from the paper (gap filled).} The paper (p.~321: ``We shall consider a
    resolution datum $\mathfrak R^{N-1}_{\mathrm{II}}$ on $\tilde X$'') presupposes that $\bar J(s)$
    is a sheaf of non-zero ideals, which a resolution datum of type II requires (Definition~3 (II))
    but the paper never proves. -/)
  (latexEnv := "lemma")]
theorem stalkIdeal_jBar_ne_bot [Hironaka.HironakaCitedResults.{u}] {s : ℕ} (hprep : PrepHyp N ℜ r ν T x₀ s) (hge : ℜ.b ≤ ν)
    (xb : 𝒮.xTilde s) : (𝒮.jBar s).stalkIdeal xb ≠ ⊥ := by
  have hadm := 𝒮.isAdmissibleAt_of_prepHyp hprep
  have hSmem : ∀ y : X, (ν : ℕ∞) ≤ ℜ.nuAt y → (∀ F, r = .closed F → y ∈ F.pts) → y ∈ ℜ.S :=
    fun y hy _ => by
      show (ℜ.b : ℕ∞) ≤ (ℜ.weight y : ℕ∞) + ℜ.nuAt y
      calc (ℜ.b : ℕ∞) ≤ ν := Nat.cast_le.mpr hge
        _ ≤ ℜ.nuAt y := hy
        _ ≤ (ℜ.weight y : ℕ∞) + ℜ.nuAt y := le_add_self
  exact 𝒮.stalkIdeal_jBar_ne_bot_of_forall_isNonsingular hSmem
    (fun t ht => (hadm.2.2.1 t ht).1.1) s le_rfl xb

/-- In the case `ν < b` the stalks of `J̄*(s)` are non-zero: they contain the `b̄`-th power of the
product `∏ P̃_j^{c_j}` of the (principal, non-zero) stalks of the non-singular divisors `Ẽ_j`. -/
theorem stalkIdeal_jBarStar_ne_bot [Hironaka.HironakaCitedResults.{u}] {s : ℕ} (hprep : PrepHyp N ℜ r ν T x₀ s)
    (hFE : ∀ F, r = .closed F → ∀ i : Fin ℜ.α, ¬ F.pts ⊆ (ℜ.E i).pts) (xb : 𝒮.xTilde s) :
    (𝒮.jBarStar s).stalkIdeal xb ≠ ⊥ := by
  classical
  have hadm := 𝒮.isAdmissibleAt_of_prepHyp hprep
  have hII := 𝒮.isWeakDatum_datumTilde hprep hFE 1 (fun _ => 0) ⊤ Nat.one_pos
    (fun x => by rw [Subscheme.stalkIdeal_top_eq]; exact top_ne_bot)
  have hreg : IsRegularLocalRing ((𝒮.xTilde s).presheaf.stalk xb) := hadm.1.1 xb
  obtain ⟨u, hu, hou⟩ := 𝒮.exists_prod_stalkIdeal_eTilde_eq_span hadm hII (cT T ℜ r s) xb
  have hu0 : u ≠ 0 := by
    intro h0
    rw [h0, Ideal.ordElem_eq_top_iff.mpr fun n => zero_mem _] at hou
    exact ENat.top_ne_natCast _ hou
  have hst : (𝒮.jBarStar s).stalkIdeal xb =
      ((𝒮.jBar s).stalkIdeal xb) ^ (ℜ.b - ν) ⊔ (Ideal.span {u ^ 𝒮.bBar}) := by
    unfold jBarStar
    rw [Scheme.IdealSheafData.add_eq_sup, Subscheme.stalkIdeal_sup_eq, Subscheme.stalkIdeal_pow_eq,
      Subscheme.stalkIdeal_pow_eq, stalkIdeal_prod_eq, ← Ideal.span_singleton_pow]
    simp only [Subscheme.stalkIdeal_pow_eq]
    rw [hu]
  intro hbot
  have h1 : Ideal.span {u ^ 𝒮.bBar} ≤ ⊥ := by
    rw [← hbot, hst]; exact le_sup_right
  have h2 : u ^ 𝒮.bBar = 0 := by
    have := h1 (Ideal.mem_span_singleton_self _)
    simpa using this
  have := isDomain_of_isRegularLocalRing ((𝒮.xTilde s).presheaf.stalk xb)
  exact hu0 (pow_eq_zero_iff (Nat.factorial_pos ν).ne' |>.mp h2)

theorem stalkIdeal_kOf_ne_bot [Hironaka.HironakaCitedResults.{u}] {s : ℕ} (hprep : PrepHyp N ℜ r ν T x₀ s)
    (hFE : ∀ F, r = .closed F → ∀ i : Fin ℜ.α, ¬ F.pts ⊆ (ℜ.E i).pts) (xb : 𝒮.xTilde s) :
    (𝒮.kOf s).stalkIdeal xb ≠ ⊥ := by
  by_cases hge : ℜ.b ≤ ν
  · have : 𝒮.kOf s = 𝒮.jBar s := by simp only [kOf, hge, ↓reduceIte]
    rw [this]
    exact 𝒮.stalkIdeal_jBar_ne_bot hprep hge xb
  · have : 𝒮.kOf s = 𝒮.jBarStar s := by simp only [kOf, hge, ↓reduceIte]
    rw [this]
    exact 𝒮.stalkIdeal_jBarStar_ne_bot hprep hFE xb

theorem stalkIdeal_ne_bot_of_mul_eq {s : ℕ} (a : Fin (alphaT r ℜ.α s) → ℕ)
    (Jt : Subscheme (𝒮.xTilde s)) (hJt : Jt * ∏ j, (𝒮.eTilde s j) ^ (a j) = 𝒮.kOf s)
    (hK : ∀ xb, (𝒮.kOf s).stalkIdeal xb ≠ ⊥) (xb : 𝒮.xTilde s) : Jt.stalkIdeal xb ≠ ⊥ := by
  intro h
  apply hK xb
  rw [← hJt, Subscheme.stalkIdeal_mul_eq, h, Ideal.bot_mul]

/-- **The end of the induction (p. 322: "if `ℜ^{N-1}_II` is resolved, then `S_ν(ℜ(s)) ∩
h_s⁻¹(x_0)` is empty").**  Under `[(1)]`, `x_0 ∈ h_s(S_ν(ℜ(s)))`, the set `S(ℜ^{N-1}_II)` is
non-empty: for `ν ≥ b` by the Corollary of Lemma (CD.4), for `ν < b` by the bijection of
Remark 2. -/
theorem S_datumTilde_nonempty [Hironaka.HironakaCitedResults.{u}] {s : ℕ} (hprep : PrepHyp N ℜ r ν T x₀ s)
    (hFE : ∀ F, r = .closed F → ∀ i : Fin ℜ.α, ¬ F.pts ⊆ (ℜ.E i).pts)
    (a : Fin (alphaT r ℜ.α s) → ℕ) (Jt : Subscheme (𝒮.xTilde s))
    (hJt : Jt * ∏ j, (𝒮.eTilde s j) ^ (a j) = 𝒮.kOf s) :
    (𝒮.datumTilde s (btOf ℜ.b ν) a Jt).S.Nonempty := by
  classical
  have hadm := 𝒮.isAdmissibleAt_of_prepHyp hprep
  have hK := 𝒮.stalkIdeal_kOf_ne_bot hprep hFE
  have hJne := 𝒮.stalkIdeal_ne_bot_of_mul_eq a Jt hJt hK
  obtain ⟨y, hy, hyx⟩ := hprep.2.2.2
  have hyfib : y ∈ (T.pre s).composite.base ⁻¹' {x₀} := hyx
  obtain ⟨xh, hxh, hcx⟩ := (hS.bijOn_and_mapsRSOP_and_exists_unique_totalTransform
    𝒮.toCompletion s).1.surjOn hyfib
  by_cases hge : ℜ.b ≤ ν
  · have hbt : btOf ℜ.b ν = 𝒮.bBar := by unfold btOf; simp only [hge, ↓reduceIte]; rfl
    have hKj : 𝒮.kOf s = 𝒮.jBar s := by simp only [kOf, hge, ↓reduceIte]
    rw [hbt]
    have hII := 𝒮.isWeakDatum_datumTilde hprep hFE 𝒮.bBar a Jt (Nat.factorial_pos ν) hJne
    obtain ⟨xb, -, -, hxb⟩ := 𝒮.exists_stalkIdeal_jBar_le_pow_and_bBar_le_nu_of_mem_Snu s y
      ⟨hyx, hy⟩ xh hxh hcx
    refine ⟨xb, ?_⟩
    rw [𝒮.S_datumTilde_eq_of_jBarStar hadm hII (𝒮.kOf s) hJt, hKj]
    exact hxb
  · have hlt : ν < ℜ.b := by omega
    have hbt : btOf ℜ.b ν = 𝒮.bBar * (ℜ.b - ν) := by unfold btOf; simp only [hge, ↓reduceIte]; rfl
    have hKj : 𝒮.kOf s = 𝒮.jBarStar s := by simp only [kOf, hge, ↓reduceIte]
    rw [hbt]
    have hII := 𝒮.isWeakDatum_datumTilde hprep hFE (𝒮.bBar * (ℜ.b - ν)) a Jt
      (Nat.mul_pos (Nat.factorial_pos ν) (by omega)) hJne
    have hbij := 𝒮.bijOn_cBar_S hprep hlt hII (hKj ▸ hJt)
    obtain ⟨xb, hxb, -⟩ := hbij.surjOn ⟨hy, hyfib⟩
    exact ⟨xb, hxb⟩

/-- `X̃ = X̄_s` is a non-singular irreducible algebraic scheme of dimension `N - 1` (p. 321, first
sentence of the facts "we see";
`isNonsingular_xTilde_and_dim_xTilde_and_hasOnlyNormalCrossings_of_prepHyp`): it is an ambient
scheme in the sense of Ch. I §2, so that Theorem `II₂^{N-1}` can be applied to it. -/
theorem isAmbient_xTilde [Hironaka.HironakaCitedResults.{u}] {s : ℕ} (hprep : PrepHyp N ℜ r ν T x₀ s)
    (hFE : ∀ F, r = .closed F → ∀ i : Fin ℜ.α, ¬ F.pts ⊆ (ℜ.E i).pts) :
    IsAmbient (𝒮.xTilde s) (N - 1) := by
  have h := 𝒮.isNonsingular_xTilde_and_dim_xTilde_and_hasOnlyNormalCrossings_of_prepHyp s hprep hFE
  have := 𝒮.isAlgebraicScheme_tHat_X s
  exact ⟨isAlgebraicScheme_toScheme (𝒮.xBar s), h.1, h.2.1, h.2.2.1⟩

end Frame

/-- The tower-independent data of the frame of pp. 314-315 (the choices `z_0`, `jGen` and the
`FrameSpec`), kept fixed along the lifting of a resolving succession of `X̃`. -/
structure LiftData (N : ℕ) {X : Scheme.{u}} (ℜ : DatumII.Raw X) (r : Restriction X) (ν : ℕ)
    (x₀ : X) where
  [reg : IsRegularLocalRing (AB.Shat X x₀)]
  hx : X.IsSimpleAt x₀
  z : AB.Shat X x₀
  jGen : Set (AB.Shat X x₀)
  fr : FrameSpec N x₀ ℜ r ν z jGen

/-- Not in the paper (encoding): a tower with empty centers from `m` on, whose initial segments
`T.pre m` is permissible and whose `n`-th initial segment satisfies `[(1)]`, `[(2)]` and
`x_0 ∈ h_n(S_ν(ℜ(n)))`, satisfies the standing assumptions of p. 314 and `PrepHyp` at `n`
(without restriction).  (The proof of `exists_standing_prepHyp_tower`, for a tower given in
advance.) -/
theorem standing_prepHyp_of_tower [Hironaka.HironakaCitedResults.{u}] {N : ℕ} (hN : 1 ≤ N) (hX : IsAmbient X N)
    (ℜ : DatumII.Raw X) (hℜ : ℜ.IsDatum) (ν : ℕ) (hν : 0 < ν) (hνeq : (ν : ℕ∞) = ℜ.nu)
    (hno : NoCodimOneComponent (ℜ.sNu ν)) {x₀ : X} (T : AB.Tower X) (n m : ℕ)
    (hB : ∀ s, m ≤ s → T.B s = Subscheme.empty) (hgm : (T.pre m).IsPermissibleII ℜ)
    (hP : Prepared N ℜ ν (T.pre n)) (hx₀ : x₀ ∈ sNuImage (T.pre n) ℜ ν) :
    Standing N ℜ .unrestricted ν T x₀ ∧ PrepHyp N ℜ .unrestricted ν T x₀ n := by
  have hmem : x₀ ∈ ℜ.sNu ν := by
    have := hX.1
    obtain ⟨y, hy, rfl⟩ := hx₀
    obtain ⟨hY, hd⟩ := (T.pre n).isAmbient_transformII hX ℜ hℜ hP.isPermissibleII
    exact MonoidalSuccession.mem_sNu_of_mem_sNu_transformII (T.pre n) hX.2.1 ℜ hℜ
      hP.isPermissibleII hy
  refine ⟨⟨hN, hX, hℜ, trivial, hνeq, hνeq, hν, hno,
    pre_isPermissibleII_of_empty_tail T ℜ m hB hgm, hP.dimAt_eq x₀ hx₀, hmem⟩,
    hP.finite, hP.dimAt_eq, ?_, hx₀⟩
  intro _ i
  rw [eSeq_castAdd]
  exact hP.disjoint i

/-- `ã` extended by a new exponent, as a function on `ℕ` (junk beyond the range). -/
def extendN (m : ℕ) (a : ℕ → ℕ) (anew : ℕ) : ℕ → ℕ :=
  fun j => if j = m then anew else a j

theorem snoc_eq_extendN (m : ℕ) (a : ℕ → ℕ) (anew : ℕ) (j : Fin (m + 1)) :
    Fin.snoc (α := fun _ => ℕ) (fun i : Fin m => a i) anew j = extendN m a anew j := by
  refine Fin.lastCases ?_ (fun i => ?_) j
  · simp [extendN]
  · have hi : (i : ℕ) < m := i.2
    simp only [Fin.snoc_castSucc, extendN, Fin.val_castSucc]
    simp only [hi.ne, ↓reduceIte]

theorem extendA_eq_extendN {r : Restriction X} {α s : ℕ} (a : ℕ → ℕ) (anew : ℕ)
    (j : Fin (alphaT r α (s + 1))) :
    extendA (fun i : Fin (alphaT r α s) => a i) anew j = extendN (alphaT r α s) a anew j := by
  unfold extendA
  exact snoc_eq_extendN _ a anew (Fin.cast (alphaT_succ r α s) j)

namespace LiftData

variable {ℜ : DatumII.Raw X} {r : Restriction X} {ν : ℕ} {x₀ : X} (L : LiftData N ℜ r ν x₀)

/-- The stage state attached to a finite succession `g` (the fold of `g`). -/
def stage {Y : Scheme.{u}} (g : MonoidalSuccession X Y) : FrameStage Y :=
  FrameStage.fold ν.factorial g (FrameStage.initial x₀ L.hx L.z L.jGen)

/-- At the stage `g`, the auxiliary datum `ℜ̃` (with its factorization `J̃ ∏ P̃_j^{ã_j}` of
`J̄(s)` resp. `J̄*(s)`) is resolvable by a succession of exactly `k` monoidal transformations. -/
def Q {Y : Scheme.{u}} (g : MonoidalSuccession X Y) (k : ℕ) : Prop :=
  ∃ (n : ℕ) (σ : FrameStage Y) (D : DatumII.Raw Y), g.length = n ∧ σ = L.stage g ∧
    D = g.transformII ℜ ∧
    ∃ (a : ℕ → ℕ) (Jt : Subscheme σ.xBar.toScheme),
      Jt * ∏ j : Fin (alphaT r ℜ.α n), (σ.eTilde D r ℜ.α n j) ^ a j =
        σ.kOf D r ℜ.α n ℜ.b ν ∧
      DatumII.Raw.ResolvableLen k
        (σ.datumTilde D r ℜ.α n (btOf ℜ.b ν) (fun j => a j) Jt)

/-- The end of the induction at the level of stages: if `x_0 ∈ h(S_ν(ℜ(s)))`, the datum `ℜ̃` is not
resolved at the stage `g`. -/
theorem not_Q_zero [Hironaka.HironakaCitedResults.{u}] {ℜ : DatumII.Raw X} {ν : ℕ} {x₀ : X}
    (L : LiftData N ℜ .unrestricted ν x₀) (hN : 1 ≤ N) (hX : IsAmbient X N) (hℜ : ℜ.IsDatum)
    (hν : 0 < ν) (hνeq : (ν : ℕ∞) = ℜ.nu) (hno : NoCodimOneComponent (ℜ.sNu ν))
    {Y : Scheme.{u}} (g : MonoidalSuccession X Y) (hP : Prepared N ℜ ν g)
    (hx : x₀ ∈ sNuImage g ℜ ν) : ¬ L.Q g 0 := by
  rintro ⟨n, σ, D, hn, hσ, hD, a, Jt, hJt, hres⟩
  obtain ⟨T, n', h, hpre, -, hS, hprep⟩ := exists_standing_prepHyp_tower hN hX ℜ hℜ ν hν hνeq hno g
    hP.isPermissibleII hP.finite hP.dimAt_eq hP.disjoint hx
  subst h
  have hpre' : T.pre n' = g := hpre
  subst hpre'
  obtain rfl : n = n' := hn.symm.trans (AB.Tower.length_pre T n')
  have := L.reg
  have hσ' : σ = (Frame.canon hS L.z L.jGen L.fr).stageOf n :=
    hσ.trans (Frame.canon_stageOf_eq_fold n).symm
  subst hσ'
  subst hD
  generalize Frame.canon hS L.z L.jGen L.fr = 𝒮 at *
  change Subscheme (𝒮.xTilde n) at Jt
  have hS' : (𝒮.datumTilde n (btOf ℜ.b ν) (fun j => a j) Jt).S = ∅ := by
    rw [𝒮.datumTilde_eq_stageOf]
    exact hres
  have hJt' : Jt * ∏ j, (𝒮.eTilde n j) ^ (a j) = 𝒮.kOf n := by
    have h1 : (∏ j : Fin (alphaT Restriction.unrestricted ℜ.α n), (𝒮.eTilde n j) ^ (a j)) =
        ∏ j, ((𝒮.stageOf n).eTilde (datum T ℜ n) Restriction.unrestricted ℜ.α n j) ^ (a j) :=
      Finset.prod_congr rfl fun j _ => by rw [𝒮.eTilde_eq_stageOf]; rfl
    rw [h1]
    exact hJt.trans (𝒮.kOf_eq_stageOf_aux n).symm
  obtain ⟨xb, hxb⟩ := 𝒮.S_datumTilde_nonempty hprep (fun F hF => by cases hF) (fun j => a j) Jt hJt'
  rw [hS'] at hxb
  exact hxb

end LiftData

section Unrestricted

variable {ℜ : DatumII.Raw X} {ν : ℕ} {x₀ : X} (L : LiftData N ℜ .unrestricted ν x₀)

/-- **Remarks 1 and 2 at the level of stages** (pp. 322-323): a monoidal transformation of `X̃`
permissible for `ℜ̃` and with non-singular irreducible center `B̃` comes from a center `B_s` of
`X_s` permissible for `ℜ(s)`, with `B̃ = c_s⁻¹(B_s)`. -/
theorem LiftData.exists_center [Hironaka.HironakaCitedResults.{u}] (hN : 1 ≤ N) (hX : IsAmbient X N) (hℜ : ℜ.IsDatum) (hν : 0 < ν)
    (hνeq : (ν : ℕ∞) = ℜ.nu) (hno : NoCodimOneComponent (ℜ.sNu ν)) {Y : Scheme.{u}}
    (g : MonoidalSuccession X Y) (hP : Prepared N ℜ ν g) (hx : x₀ ∈ sNuImage g ℜ ν)
    {n : ℕ} (hn : g.length = n) {σ : FrameStage Y} (hσ : σ = L.stage g) {D : DatumII.Raw Y}
    (hD : D = g.transformII ℜ) (a : ℕ → ℕ) (Jt : Subscheme σ.xBar.toScheme)
    (hJt : Jt * ∏ j : Fin (alphaT (Restriction.unrestricted : Restriction X) ℜ.α n),
      (σ.eTilde D (Restriction.unrestricted : Restriction X) ℜ.α n j) ^ a j =
        σ.kOf D (Restriction.unrestricted : Restriction X) ℜ.α n ℜ.b ν)
    (Bt : Subscheme σ.xBar.toScheme) (hBt : Bt.IsNonsingular) (hBti : Bt.IsIrreducible)
    (hperm : (σ.datumTilde D (Restriction.unrestricted : Restriction X) ℜ.α n (btOf ℜ.b ν)
      (fun j => a j) Jt).IsPermissible Bt) :
    ∃ B : Subscheme Y, B.IsNonsingular ∧ B.IsIrreducible ∧
      (Bt.ι ≫ σ.xBar.ι).ker = Subscheme.totalTransform σ.c B ∧
      (∃ e : Bt.toScheme ≅ B.toScheme, e.hom ≫ B.ι = Bt.ι ≫ σ.xBar.ι ≫ σ.c) ∧
      D.IsPermissible B := by
  obtain ⟨T, n', h, hpre, -, hS, hprep⟩ := exists_standing_prepHyp_tower hN hX ℜ hℜ ν hν hνeq hno g
    hP.isPermissibleII hP.finite hP.dimAt_eq hP.disjoint hx
  subst h
  have hpre' : T.pre n' = g := hpre
  subst hpre'
  obtain rfl : n = n' := hn.symm.trans (AB.Tower.length_pre T n')
  have := L.reg
  have hσ' : σ = (Frame.canon hS L.z L.jGen L.fr).stageOf n :=
    hσ.trans (Frame.canon_stageOf_eq_fold n).symm
  subst hσ'
  subst hD
  generalize Frame.canon hS L.z L.jGen L.fr = 𝒮 at *
  change Subscheme (𝒮.xTilde n) at Jt Bt
  have hJt' : Jt * ∏ j, (𝒮.eTilde n j) ^ (a j) = 𝒮.kOf n := by
    have h1 : (∏ j : Fin (alphaT (Restriction.unrestricted : Restriction X) ℜ.α n),
        (𝒮.eTilde n j) ^ (a j)) =
        ∏ j, ((𝒮.stageOf n).eTilde (datum T ℜ n) (Restriction.unrestricted : Restriction X)
          ℜ.α n j) ^ (a j) :=
      Finset.prod_congr rfl fun j _ => by rw [𝒮.eTilde_eq_stageOf]; rfl
    rw [h1]
    exact hJt.trans (𝒮.kOf_eq_stageOf_aux n).symm
  have hperm' : (𝒮.datumTilde n (btOf ℜ.b ν) (fun j => a j) Jt).IsPermissible Bt := by
    rw [𝒮.datumTilde_eq_stageOf]
    exact hperm
  have hFE : ∀ F, Restriction.unrestricted = Restriction.closed F → ∀ i : Fin ℜ.α,
      ¬ F.pts ⊆ (ℜ.E i).pts := fun F hF => by cases hF
  have hJne := 𝒮.stalkIdeal_ne_bot_of_mul_eq (fun j => a j) Jt hJt'
    (𝒮.stalkIdeal_kOf_ne_bot hprep hFE)
  by_cases hge : ℜ.b ≤ ν
  · have hbt : btOf ℜ.b ν = 𝒮.bBar := by unfold btOf; simp only [hge, ↓reduceIte]; rfl
    have hKj : 𝒮.kOf n = 𝒮.jBar n := by simp only [Frame.kOf, hge, ↓reduceIte]
    rw [hbt] at hperm'
    rw [hKj] at hJt'
    have hII := 𝒮.isWeakDatum_datumTilde hprep hFE 𝒮.bBar (fun j => a j) Jt
      (Nat.factorial_pos ν) hJne
    exact 𝒮.exists_isPermissibleCenter_of_isPermissible_datumTilde n hprep hge (fun j => a j) Jt
      hJt' hII Bt hBt hBti hperm'
  · have hlt : ν < ℜ.b := by omega
    have hbt : btOf ℜ.b ν = 𝒮.bBar * (ℜ.b - ν) := by
      unfold btOf; simp only [hge, ↓reduceIte]; rfl
    have hKj : 𝒮.kOf n = 𝒮.jBarStar n := by simp only [Frame.kOf, hge, ↓reduceIte]
    rw [hbt] at hperm'
    rw [hKj] at hJt'
    have hII := 𝒮.isWeakDatum_datumTilde hprep hFE (𝒮.bBar * (ℜ.b - ν)) (fun j => a j) Jt
      (Nat.mul_pos (Nat.factorial_pos ν) (by omega)) hJne
    obtain ⟨-, -, h3⟩ := 𝒮.S_datumTilde_eq_and_bijOn_cBar_and_exists_isPermissibleCenter_of_lt n
      hprep hlt (fun j => a j) Jt hJt' hII
    obtain ⟨B, ⟨hBns, hBirr, hker, he, hBperm⟩, -⟩ := h3 Bt hBt hBti hperm'
    exact ⟨B, hBns, hBirr, hker, he, hBperm⟩

theorem LiftData.exists_Q_snoc [Hironaka.HironakaCitedResults.{u}] (hN : 1 ≤ N) (hX : IsAmbient X N) (hℜ : ℜ.IsDatum) (hν : 0 < ν)
    (hνeq : (ν : ℕ∞) = ℜ.nu) (hno : NoCodimOneComponent (ℜ.sNu ν)) {Y : Scheme.{u}}
    (g : MonoidalSuccession X Y) (hP : Prepared N ℜ ν g) (hx : x₀ ∈ sNuImage g ℜ ν)
    {n : ℕ} (hn : g.length = n) {σ : FrameStage Y} (hσ : σ = L.stage g) {D : DatumII.Raw Y}
    (hD : D = g.transformII ℜ) (a : ℕ → ℕ) (Jt : Subscheme σ.xBar.toScheme)
    (hJt : Jt * ∏ j : Fin (alphaT (Restriction.unrestricted : Restriction X) ℜ.α n),
      (σ.eTilde D (Restriction.unrestricted : Restriction X) ℜ.α n j) ^ a j =
        σ.kOf D (Restriction.unrestricted : Restriction X) ℜ.α n ℜ.b ν)
    (Bt : Subscheme σ.xBar.toScheme) (hBt : Bt.IsNonsingular) (hBti : Bt.IsIrreducible)
    (tTil : MonoidalTransformation σ.xBar.toScheme Bt) {k : ℕ}
    (hperm : (σ.datumTilde D (Restriction.unrestricted : Restriction X) ℜ.α n (btOf ℜ.b ν)
      (fun j => a j) Jt).IsPermissible Bt)
    (hrest : DatumII.Raw.ResolvableLen k
      ((σ.datumTilde D (Restriction.unrestricted : Restriction X) ℜ.α n (btOf ℜ.b ν)
        (fun j => a j) Jt).transform tTil))
    (B : Subscheme Y) (hB : B.IsNonsingular) (hBi : B.IsIrreducible)
    (hker : (Bt.ι ≫ σ.xBar.ι).ker = Subscheme.totalTransform σ.c B)
    (he : ∃ e : Bt.toScheme ≅ B.toScheme, e.hom ≫ B.ι = Bt.ι ≫ σ.xBar.ι ≫ σ.c)
    (hBperm : D.IsPermissible B) (t : MonoidalTransformation Y B) :
    L.Q (g.snoc B t) k := by
  obtain ⟨T, n', h, hpre, hBheq, hmt, hT⟩ :=
    AB.Tower.exists_pre_heq_and_monoidalTransformation_heq g t
  subst h
  have hpre' : T.pre n' = g := eq_of_heq hpre
  subst hpre'
  have hB' : T.B n' = B := eq_of_heq hBheq
  subst hB'
  have hmt' : T.monoidalTransformation n' = t := eq_of_heq hmt
  subst hmt'
  obtain rfl : n = n' := hn.symm.trans (AB.Tower.length_pre T n')
  subst hD
  have hgm : (T.pre (n + 1)).IsPermissibleII ℜ :=
    (MonoidalSuccession.isPermissibleII_snoc_iff (T.pre n) (T.B n) (T.monoidalTransformation n)
      ℜ).mpr ⟨hP.isPermissibleII, hBperm⟩
  obtain ⟨hS, hprep⟩ := standing_prepHyp_of_tower hN hX ℜ hℜ ν hν hνeq hno T n (n + 1) hT hgm hP hx
  have := L.reg
  obtain ⟨𝒮, h𝒮⟩ : ∃ 𝒮, 𝒮 = Frame.canon hS L.z L.jGen L.fr := ⟨_, rfl⟩
  have hσ' : σ = 𝒮.stageOf n := by
    rw [hσ, h𝒮]; exact (Frame.canon_stageOf_eq_fold n).symm
  subst hσ'
  change Subscheme (𝒮.xTilde n) at Jt Bt
  have hFE : ∀ F, (Restriction.unrestricted : Restriction X) = Restriction.closed F →
      ∀ i : Fin ℜ.α, ¬ F.pts ⊆ (ℜ.E i).pts := fun F hF => by cases hF
  have hJt' : Jt * ∏ j, (𝒮.eTilde n j) ^ (a j) = 𝒮.kOf n := by
    have h1 : (∏ j : Fin (alphaT (Restriction.unrestricted : Restriction X) ℜ.α n),
        (𝒮.eTilde n j) ^ (a j)) =
        ∏ j, ((𝒮.stageOf n).eTilde (datum T ℜ n) (Restriction.unrestricted : Restriction X)
          ℜ.α n j) ^ (a j) :=
      Finset.prod_congr rfl fun j _ => by rw [𝒮.eTilde_eq_stageOf]; rfl
    rw [h1]
    exact hJt.trans (𝒮.kOf_eq_stageOf_aux n).symm
  have hperm' : (𝒮.datumTilde n (btOf ℜ.b ν) (fun j => a j) Jt).IsPermissible Bt := by
    rw [𝒮.datumTilde_eq_stageOf]
    exact hperm
  have hrest' : DatumII.Raw.ResolvableLen k
      ((𝒮.datumTilde n (btOf ℜ.b ν) (fun j => a j) Jt).transform tTil) := by
    rw [𝒮.datumTilde_eq_stageOf]
    exact hrest
  have hJne := 𝒮.stalkIdeal_ne_bot_of_mul_eq (fun j => a j) Jt hJt'
    (𝒮.stalkIdeal_kOf_ne_bot hprep hFE)
  have final : ∀ (h : AB.IsMonoidalTransformationOf (𝒮.fBar n) Bt) (anew : ℕ)
      (Jt' : Subscheme (𝒮.xTilde (n + 1))),
      (𝒮.datumTilde n (btOf ℜ.b ν) (fun j => a j) Jt).transform
        (⟨_, 𝒮.fBar n, h.1, h.2⟩ : MonoidalTransformation (𝒮.xTilde n) Bt) =
        𝒮.datumTilde (n + 1) (btOf ℜ.b ν) (extendA (fun j => a j) anew) Jt' →
      Jt' * ∏ j, (𝒮.eTilde (n + 1) j) ^ (extendA (fun j => a j) anew j) = 𝒮.kOf (n + 1) →
      L.Q ((T.pre n).snoc (T.B n) (T.monoidalTransformation n)) k := by
    intro h anew Jt' htr hJt''
    have hres1 := DatumII.Raw.resolvableLen_transform_congr tTil
      (⟨_, 𝒮.fBar n, h.1, h.2⟩ : MonoidalTransformation (𝒮.xTilde n) Bt) _ k hrest'
    have hres2 : DatumII.Raw.ResolvableLen k
        (𝒮.datumTilde (n + 1) (btOf ℜ.b ν) (extendA (fun j => a j) anew) Jt') := by
      rw [← htr]; exact hres1
    have hsnoc : (T.pre n).snoc (T.B n) (T.monoidalTransformation n) = T.pre (n + 1) := rfl
    rw [hsnoc]
    have hst : 𝒮.stageOf (n + 1) = L.stage (T.pre (n + 1)) := by
      rw [h𝒮]; exact Frame.canon_stageOf_eq_fold (n + 1)
    refine ⟨n + 1, 𝒮.stageOf (n + 1), datum T ℜ (n + 1), AB.Tower.length_pre T (n + 1), hst, rfl,
      extendN (alphaT (Restriction.unrestricted : Restriction X) ℜ.α n) (fun j => a j) anew,
      Jt', ?_, ?_⟩
    · have h1 : (∏ j : Fin (alphaT (Restriction.unrestricted : Restriction X) ℜ.α (n + 1)),
          ((𝒮.stageOf (n + 1)).eTilde (datum T ℜ (n + 1))
            (Restriction.unrestricted : Restriction X) ℜ.α (n + 1) j) ^
              (extendN (alphaT (Restriction.unrestricted : Restriction X) ℜ.α n)
                (fun j => a j) anew j)) =
          ∏ j, (𝒮.eTilde (n + 1) j) ^ (extendA (fun j => a j) anew j) :=
        Finset.prod_congr rfl fun j _ => by
          rw [𝒮.eTilde_eq_stageOf, extendA_eq_extendN]; rfl
      exact (congrArg (fun P => Jt' * P) h1).trans (hJt''.trans (𝒮.kOf_eq_stageOf_aux (n + 1)))
    · have h3 := 𝒮.datumTilde_eq_stageOf (n + 1) (btOf ℜ.b ν) (extendA (fun j => a j) anew) Jt'
      rw [h3] at hres2
      have h2 : (fun j : Fin (alphaT (Restriction.unrestricted : Restriction X) ℜ.α (n + 1)) =>
          extendN (alphaT (Restriction.unrestricted : Restriction X) ℜ.α n) (fun j => a j) anew j) =
          extendA (fun j => a j) anew :=
        funext fun j => (extendA_eq_extendN _ anew j).symm
      rw [h2]
      exact hres2
  have hBe' : ∃ e : Bt.toScheme ≅ (T.B n).toScheme, e.hom ≫ (T.B n).ι = Bt.ι ≫ 𝒮.cBar n := he
  have hBperm' : (restriction T Restriction.unrestricted n).IsPermissibleCenter (datum T ℜ n)
      (T.B n) := hBperm
  have hker' : (Bt.ι ≫ (𝒮.xBar n).ι).ker = Subscheme.totalTransform (𝒮.c n) (T.B n) := hker
  by_cases hge : ℜ.b ≤ ν
  · have hbt : btOf ℜ.b ν = 𝒮.bBar := by unfold btOf; simp only [hge, ↓reduceIte]; rfl
    have hKj : ∀ s, 𝒮.kOf s = 𝒮.jBar s := fun s => by simp only [Frame.kOf, hge, ↓reduceIte]
    rw [hbt] at hperm' hrest' final
    rw [hKj] at hJt' final
    have hII := 𝒮.isWeakDatum_datumTilde hprep hFE 𝒮.bBar (fun j => a j) Jt
      (Nat.factorial_pos ν) hJne
    obtain ⟨-, h, anew, Jt', htr, hJt''⟩ :=
      𝒮.ker_eq_B_and_exists_transform_eq_datumTilde_of_ge n hprep hge (fun j => a j) Jt hJt' hII Bt
        hBt hBti hperm' (T.B n) ⟨hB, hBi⟩ hBe' hBperm' rfl
    exact final h anew Jt' htr hJt''
  · have hlt : ν < ℜ.b := by omega
    have hbt : btOf ℜ.b ν = 𝒮.bBar * (ℜ.b - ν) := by
      unfold btOf; simp only [hge, ↓reduceIte]; rfl
    have hKj : ∀ s, 𝒮.kOf s = 𝒮.jBarStar s := fun s => by simp only [Frame.kOf, hge, ↓reduceIte]
    rw [hbt] at hperm' hrest' final
    rw [hKj] at hJt' final
    have hII := 𝒮.isWeakDatum_datumTilde hprep hFE (𝒮.bBar * (ℜ.b - ν)) (fun j => a j) Jt
      (Nat.mul_pos (Nat.factorial_pos ν) (by omega)) hJne
    obtain ⟨h, anew, Jt', htr, hJt''⟩ := 𝒮.exists_transform_eq_datumTilde_of_lt n hprep hlt
      (fun j => a j) Jt hJt' hII Bt hBt hBti hperm' (T.B n) ⟨hB, hBi⟩ hker' hBe' hBperm' rfl
    exact final h anew Jt' htr hJt''

/-- One step of the induction: either the first transformation of the resolving succession of
`X̃` has empty center (and is dropped), or it is lifted to the center `B_s` of `X_s` and the
resolvability of the next stage is read off the relation of `ℜ(s+1)` with `f̄_s*(ℜ̃)`
(Remarks 1--3, pp. 321--326). -/
theorem LiftData.step [Hironaka.HironakaCitedResults.{u}] (hN : 1 ≤ N) (hX : IsAmbient X N) (hℜ : ℜ.IsDatum) (hν : 0 < ν)
    (hνeq : (ν : ℕ∞) = ℜ.nu) (hno : NoCodimOneComponent (ℜ.sNu ν)) {Y : Scheme.{u}}
    (g : MonoidalSuccession X Y) (hP : Prepared N ℜ ν g) (hx : x₀ ∈ sNuImage g ℜ ν) (k : ℕ)
    (hQ : L.Q g (k + 1)) :
    L.Q g k ∨ ∃ (B : Subscheme Y) (t : MonoidalTransformation Y B),
      (g.transformII ℜ).IsPermissible B ∧ L.Q (g.snoc B t) k := by
  obtain ⟨n, σ, D, hn, hσ, hD, a, Jt, hJt, Bt, tTil, hperm, hrest⟩ := hQ
  rcases hperm.1 with hBt | ⟨hBt, hBti⟩
  · subst hBt
    left
    exact ⟨n, σ, D, hn, hσ, hD, a, Jt, hJt,
      DatumII.Raw.resolvableLen_of_transform_of_center_empty tTil _ k hrest⟩
  · right
    obtain ⟨B, hB, hBi, hker, he, hBperm⟩ := L.exists_center hN hX hℜ hν hνeq hno g hP hx hn hσ hD
      a Jt hJt Bt hBt hBti hperm
    obtain ⟨t, -⟩ := MonoidalTransformation.exists_isProper Y B
    exact ⟨B, t, hD ▸ hBperm, L.exists_Q_snoc hN hX hℜ hν hνeq hno g hP hx hn hσ hD a Jt hJt Bt
      hBt hBti tTil hperm hrest B hB hBi hker he hBperm t⟩

/-- **The core step, conditionally on the resolvability of the auxiliary datum** (pp. 314-326,
Theorems C and D*, unrestricted case).  The only hypothesis on `ℜ̃ = ℜ^{N-1}_II` is `hRes`: at the
prepared stage `s` (the stage of the given succession `g`) the datum with `ã_j = 0`,
`J̃ = J̄(s)` resp. `J̄*(s)`, `b̃ = b̄` resp. `b̄(b - ν)` is resolvable (`DatumII.Raw.Resolvable`),
which Theorem `II₂^{N-1}` provides once `ℜ̃` is replaced by a resolution datum (the repair of the
the paper's error on the subschemes `Ẽ_j`).  Everything else is proved: the lifting of the resolving
succession of `X̃` to `X_s` one transformation at a time, with the frame of §4 rebuilt at every
stage (`FrameStage.fold`, `Frame.canon`). -/
theorem exists_extension_not_mem_sNuImage_of_resolvable [Hironaka.HironakaCitedResults.{u}] {N : ℕ} (hN : 1 ≤ N)
    {X : Scheme.{u}} (hX : IsAmbient X N) {ℜ : DatumII.Raw X} (hℜ : ℜ.IsDatum) {ν : ℕ}
    (hν : 0 < ν) (hνeq : (ν : ℕ∞) = ℜ.nu) (hno : NoCodimOneComponent (ℜ.sNu ν))
    {Y : Scheme.{u}} (g : MonoidalSuccession X Y) (hg : g.IsPermissibleII ℜ)
    (hfin : (sNuImage g ℜ ν).Finite)
    (hdim : ∀ y ∈ sNuImage g ℜ ν, X.dimAt y = (N : WithBot ℕ∞))
    (hdisj : ∀ i : Fin ℜ.α, (g.strictTransform (ℜ.E i)).pts ∩ (g.transformII ℜ).sNu ν = ∅)
    {x₀ : X} (hx₀ : x₀ ∈ sNuImage g ℜ ν)
    (hRes : ∀ (T : AB.Tower X) (n : ℕ) (hS : Standing N ℜ .unrestricted ν T x₀) (𝒮 : Frame hS),
      PrepHyp N ℜ .unrestricted ν T x₀ n →
        (𝒮.datumTilde n (btOf ℜ.b ν) (fun _ => 0) (𝒮.kOf n)).Resolvable) :
    ∃ (Z : Scheme.{u}) (e : MonoidalSuccession Y Z), e.IsPermissibleII (g.transformII ℜ) ∧
      x₀ ∉ sNuImage (g.append e) ℜ ν ∧
      ∀ i : Fin ℜ.α, ((g.append e).strictTransform (ℜ.E i)).pts ∩
        ((g.append e).transformII ℜ).sNu ν = ∅ := by
  have hP : Prepared N ℜ ν g := ⟨hg, hfin, hdim, hdisj⟩
  -- the tower-independent data of the frame, and the initial resolvability
  obtain ⟨T, n, h, hpre, -, hS, hprep⟩ := exists_standing_prepHyp_tower hN hX ℜ hℜ ν hν hνeq hno g
    hg hfin hdim hdisj hx₀
  obtain ⟨𝒮₀⟩ := hS.nonempty_frame
  let L : LiftData N ℜ .unrestricted ν x₀ :=
    { reg := 𝒮₀.regShat, hx := hX.2.1 x₀, z := 𝒮₀.z, jGen := 𝒮₀.jGen, fr := 𝒮₀.frame }
  have hQ : ∃ k, L.Q g k := by
    subst h
    have hpre' : T.pre n = g := hpre
    subst hpre'
    have := L.reg
    obtain ⟨k, hk⟩ := (DatumII.Raw.resolvable_iff_exists_resolvableLen _).mp
      (hRes T n hS (Frame.canon hS L.z L.jGen L.fr) hprep)
    refine ⟨k, n, (Frame.canon hS L.z L.jGen L.fr).stageOf n, datum T ℜ n,
      AB.Tower.length_pre T n, Frame.canon_stageOf_eq_fold n, rfl, fun _ => 0,
      (Frame.canon hS L.z L.jGen L.fr).kOf n, ?_, ?_⟩
    · simp only [pow_zero, Finset.prod_const_one]
      exact (mul_one _).trans ((Frame.canon hS L.z L.jGen L.fr).kOf_eq_stageOf_aux n)
    · have h3 := (Frame.canon hS L.z L.jGen L.fr).datumTilde_eq_stageOf n (btOf ℜ.b ν)
        (fun j => 0) ((Frame.canon hS L.z L.jGen L.fr).kOf n)
      rw [h3] at hk
      exact hk
  obtain ⟨k, hk⟩ := hQ
  exact exists_extension_of_resolvableLen hX hℜ (fun {Y} g k => L.Q g k)
    (fun g hP hx => L.not_Q_zero hN hX hℜ hν hνeq hno g hP hx)
    (fun g k hP hx hQ => L.step hN hX hℜ hν hνeq hno g hP hx k hQ) k g hP hx₀ hk

/-- **The core step with the resolvability of weak data as the only hypothesis** (pp. 314-326,
Theorems C and D*, unrestricted case).  `hglue` is what Theorem `II₂^{N-1}` gives for a datum
whose `E_j` are non-singular divisors (not necessarily irreducible) with only normal crossings:
`DatumII.Raw.resolvable_of_isWeakDatum` (the repair of the paper's error on the subschemes `Ẽ_j`). -/
theorem exists_extension_not_mem_sNuImage_of_isWeakDatum_resolvable [Hironaka.HironakaCitedResults.{u}] {N : ℕ} (hN : 1 ≤ N)
    {X : Scheme.{u}} (hX : IsAmbient X N) {ℜ : DatumII.Raw X} (hℜ : ℜ.IsDatum) {ν : ℕ}
    (hν : 0 < ν) (hνeq : (ν : ℕ∞) = ℜ.nu) (hno : NoCodimOneComponent (ℜ.sNu ν))
    {Y : Scheme.{u}} (g : MonoidalSuccession X Y) (hg : g.IsPermissibleII ℜ)
    (hfin : (sNuImage g ℜ ν).Finite)
    (hdim : ∀ y ∈ sNuImage g ℜ ν, X.dimAt y = (N : WithBot ℕ∞))
    (hdisj : ∀ i : Fin ℜ.α, (g.strictTransform (ℜ.E i)).pts ∩ (g.transformII ℜ).sNu ν = ∅)
    {x₀ : X} (hx₀ : x₀ ∈ sNuImage g ℜ ν)
    (hglue : ∀ Z : Scheme.{u}, IsAmbient Z (N - 1) → ∀ D : DatumII.Raw Z, D.IsWeakDatum →
      D.Resolvable) :
    ∃ (Z : Scheme.{u}) (e : MonoidalSuccession Y Z), e.IsPermissibleII (g.transformII ℜ) ∧
      x₀ ∉ sNuImage (g.append e) ℜ ν ∧
      ∀ i : Fin ℜ.α, ((g.append e).strictTransform (ℜ.E i)).pts ∩
        ((g.append e).transformII ℜ).sNu ν = ∅ := by
  refine exists_extension_not_mem_sNuImage_of_resolvable hN hX hℜ hν hνeq hno g hg hfin hdim
    hdisj hx₀ fun T n hS 𝒮 hprep => ?_
  have hFE : ∀ F, (Restriction.unrestricted : Restriction X) = Restriction.closed F →
      ∀ i : Fin ℜ.α, ¬ F.pts ⊆ (ℜ.E i).pts := fun F hF => by cases hF
  exact hglue _ (𝒮.isAmbient_xTilde hprep hFE) _
    (𝒮.isWeakDatum_datumTilde hprep hFE (btOf ℜ.b ν) (fun _ => 0) (𝒮.kOf n) (btOf_pos _ _)
      (𝒮.stalkIdeal_kOf_ne_bot hprep hFE))

end Unrestricted

end Lift

end CD

namespace CD

variable {X : Scheme.{u}}

/-- The core of the proof of Theorems C and D* (pp. 314–326): for a point `x_0` of
`h_s(S_ν(ℜ(s)))` one can extend the permissible succession `h_s` so that `x_0` is no longer in
`h_{s'}(S_ν(ℜ(s')))`, keeping the conditions `[(2)]`.  In the paper: construct, for `x_0`, the
completion `Ŝ_0`, the frame, the schemes `X̂_s`, `X̄_s`, the ideals `J̄(s)` and the scheme
`X̃ = X̃_s` of dimension `N − 1` (Lemmas (CD.3)–(CD.5), Remarks 1–3); in the cases `ν ≥ b̄` and
`ν < b̄` form the datum `ℜ̃^{N−1}_II` on `X̃`; resolve it by Theorem II₂^{N−1}; lift the resulting
permissible succession of `X̃` to `X_s` (Remarks 1, 2 give the centers, Remark 3 the transforms);
then "if `ℜ̃^{N−1}` is resolved then `S_ν(ℜ(s)) ∩ h_s^{-1}(x_0)` is empty" (Corollary of Lemma
(CD.4)).  Here `ν = ν(ℜ) > 0`, `S_ν(ℜ)` has no component of codimension one (p. 314), and
`h_s(S_ν(ℜ(s)))` is a finite set of points at which `X` has dimension `N` (`[(1)]`).

Deviation from the paper (proof corrected; the paper's error on the subschemes `Ẽ_j`).  The paper applies
Theorem `II₂^{N−1}` to `ℜ̃^{N−1}_II`, asserted to be a resolution datum; the `Ẽ_j` need not be
irreducible.  Lean applies it to the datum obtained by splitting the `Ẽ_j` into their connected
components (`DatumII.Raw.resolvable_of_isWeakDatum`, `Compat/DatumRefinement.lean`), and the
Remarks 1–3 are proved for the weak datum (`DatumII.Raw.IsWeakDatum`).

Deviation from the paper (gap filled).  (i) The lifting of the resolving succession of `X̃` to `X_s`
one transformation at a time (`exists_extension_of_resolvableLen`, `LiftData.step`): the paper says
"the proof of Theorems C and D* can be easily reduced to the resolution of the `ℜ^{N-1}_II` on `X̃`"
(p. 326).  The frame of §4 is rebuilt at every stage (`FrameStage.fold`, `Frame.canon`; the
stage-`s` objects depend on the succession only through `h_s`,
`Frame.canon_stageOf_eq_fold_of_pre_eq`); the
transform of `ℜ̃` by the monoidal transformation produced by Theorem `II₂^{N−1}` and the one
induced by `f̂_s` are transformations with the same center, hence isomorphic over `X̃`
(`DatumII.Raw.resolvableLen_transform_congr`).  (ii) The stalks of `J̄(s)` are non-zero
(`Frame.stalkIdeal_jBar_ne_bot`, proved): the paper presupposes that `ℜ̃` is a resolution datum (Def. 3 (II) (iii)). -/
@[blueprint "lem:IV.4-core-step"
  (statement := /-- Let $X$ be a non-singular irreducible algebraic scheme of dimension $N\ge1$ and
    $\mathfrak R=\mathfrak R^N_{\mathrm{II}}$ a resolution datum on $X$ without restriction with
    $\nu=\nu(\mathfrak R)=\nu(\mathfrak R^N_{\mathrm{II}})>0$ such that $S_\nu(\mathfrak R)$ has no
    non-empty component of codimension $1$. Suppose Theorems $\mathrm{II}_2^{N''}$, $N''<N$, were
    verified. Let $h_s$ be a permissible succession of monoidal transformations of $X$ for
    $\mathfrak R$ satisfying [(1)] $h_s(S_\nu(\mathfrak R(s)))$ is a finite set of points at which
    $X$ has dimension $N$, and [(2)] $E_i(s)\cap S_\nu(\mathfrak R(s))=\emptyset$
    $(1\le i\le\alpha)$ (\cref{def:IV.4-conditions}), and let
    $x_0\in h_s(S_\nu(\mathfrak R(s)))$. Then $h_s$ can be extended by a permissible succession
    such that $x_0\notin h_{s'}(S_\nu(\mathfrak R(s')))$ and [(2)] still holds. (The core of the
    proof of Theorem~D*, pp.~314--326.) -/)
  (proof := /-- With reference to $x_0$ construct $\hat X_t$, $c_t$, $\bar X_t$, $\bar J(t)$,
    $\tilde X=\bar X_s$ and the datum $\mathfrak R^{N-1}_{\mathrm{II}}$ on $\tilde X$
    (\cref{def:IV.4-frame}, \cref{def:IV.4-construction}, \cref{def:IV.4-tilde},
    \cref{def:IV.4-case-ge}, \cref{def:IV.4-case-lt}). By Theorem $\mathrm{II}_2^{N-1}$ there is a
    permissible succession of monoidal transformations of $\tilde X$ for it resolving it. Lift it
    one transformation at a time: by Remarks~1 and~2 (\cref{rem:IV.4-1}, \cref{rem:IV.4-2}) the
    center $\tilde B$ comes from a center $B_s$ of $X_s$ permissible for $\mathfrak R(s)$;
    extending $h_s$ by $f_s$ with center $B_s$, the relation between $\mathfrak R(s+1)$ and
    $\bar f_s^*(\mathfrak R^{N-1}_{\mathrm{II}})$ is the same as between $\mathfrak R(s)$ and
    $\mathfrak R^{N-1}_{\mathrm{II}}$ (\cref{lem:IV.4-case-ge-relation}, \cref{rem:IV.4-3}). When
    $\mathfrak R^{N-1}_{\mathrm{II}}$ is resolved, the Corollary of Lemma (CD.4)
    (\cref{cor:IV.CD-4}) shows that $x_0\notin h_{s'}(S_\nu(\mathfrak R(s')))$; condition [(2)] is
    kept because $f(S_\nu(f^*\mathfrak R))\subseteq S_\nu(\mathfrak R)$ (\cref{lem:IV.4-x0}).

    \textbf{Deviation from the paper (proof corrected).} The paper applies Theorem
    $\mathrm{II}_2^{N-1}$ to $\mathfrak R^{N-1}_{\mathrm{II}}$ as a resolution datum, asserting that
    the $\tilde E_j$ are irreducible (p.~321), which is false. Lean
    splits each $\tilde E_j$ into its connected components (\cref{lem:IV.tilde-split},
    \cref{lem:IV.tilde-resolvable}) and proves Remarks~1--3 and the relation under the weaker
    hypotheses that the $\tilde E_j$ are non-singular divisors with only normal crossings.

    \textbf{Deviation from the paper (gap filled).} The paper closes with ``the proof of Theorems C
    and D* can be easily reduced to the resolution of the $\mathfrak R^{N-1}_{\mathrm{II}}$ on
    $\tilde X$'' (p.~326). Lean makes the induction explicit: the frame of the construction is
    rebuilt at every stage, its stage-$s$ objects depending only on $h_s$
    (\texttt{FrameStage.fold}); the
    transform of $\mathfrak R^{N-1}_{\mathrm{II}}$ by the monoidal transformation given by
    Theorem~$\mathrm{II}_2^{N-1}$ and the one induced by $\hat f_s$ are monoidal transformations of
    $\tilde X$ with the same center, hence isomorphic over $\tilde X$. The stalks of $\bar J(s)$ are
    non-zero (the paper presupposes that $\mathfrak R^{N-1}_{\mathrm{II}}$ is a datum, Def.~3 (II)
    (iii)); this is \cref{lem:IV.4-jbar-nonzero}. -/)
  (proofUses := ["def:IV.4-conditions", "lem:IV.4-x0", "def:IV.4-frame", "def:IV.4-construction",
    "def:IV.4-tilde", "def:IV.4-case-ge", "def:IV.4-case-lt", "rem:IV.4-1", "rem:IV.4-2",
    "rem:IV.4-3", "lem:IV.4-case-ge-relation", "cor:IV.CD-4", "thm:I.2-II2",
    "lem:IV.tilde-split", "lem:IV.tilde-resolvable"])
  (latexEnv := "lemma")]
theorem exists_extension_not_mem_sNuImage [Hironaka.HironakaCitedResults.{u}] {N : ℕ} (hN : 1 ≤ N)
    (hII₂ : ∀ N'' : ℕ, N'' < N → FundamentalTheorem.II₂.{u} N'')
    (X : Scheme.{u}) (hX : IsAmbient X N) (ℜ : DatumII.Raw X) (hℜ : ℜ.IsDatum) (ν : ℕ)
    (hν : 0 < ν) (hνeq : (ν : ℕ∞) = ℜ.nu) (hno : NoCodimOneComponent (ℜ.sNu ν))
    {Y : Scheme.{u}} (g : MonoidalSuccession X Y) (hg : g.IsPermissibleII ℜ)
    (hfin : (sNuImage g ℜ ν).Finite) (hdim : ∀ y ∈ sNuImage g ℜ ν, X.dimAt y = (N : WithBot ℕ∞))
    (hdisj : ∀ i : Fin ℜ.α, (g.strictTransform (ℜ.E i)).pts ∩ (g.transformII ℜ).sNu ν = ∅)
    {x₀ : X} (hx₀ : x₀ ∈ sNuImage g ℜ ν) :
    ∃ (Z : Scheme.{u}) (e : MonoidalSuccession Y Z), e.IsPermissibleII (g.transformII ℜ) ∧
      x₀ ∉ sNuImage (g.append e) ℜ ν ∧
      ∀ i : Fin ℜ.α,
        ((g.append e).strictTransform (ℜ.E i)).pts ∩ ((g.append e).transformII ℜ).sNu ν = ∅ := by
  exact exists_extension_not_mem_sNuImage_of_isWeakDatum_resolvable hN hX hℜ hν hνeq hno g hg hfin
    hdim hdisj hx₀
    (fun Z hZ D hD => DatumII.Raw.resolvable_of_isWeakDatum (hII₂ (N - 1) (by omega)) hZ hD)

/-- p. 326: after finitely many applications of the core step, `h_s(S_ν(ℜ(s)))` is empty, hence so
is `S_ν(ℜ(s))` (induction on the number of points of the finite set `h_s(S_ν(ℜ(s)))`, each step
removing the point `x_0`, no new point being created by further permissible transformations). -/
theorem exists_isPermissibleII_sNu_eq_empty_of_sNuImage_finite [Hironaka.HironakaCitedResults.{u}] {N : ℕ} (hN : 1 ≤ N)
    (hII₂ : ∀ N'' : ℕ, N'' < N → FundamentalTheorem.II₂.{u} N'')
    (X : Scheme.{u}) (hX : IsAmbient X N) (ℜ : DatumII.Raw X) (hℜ : ℜ.IsDatum) (ν : ℕ)
    (hν : 0 < ν) (hνeq : (ν : ℕ∞) = ℜ.nu) (hno : NoCodimOneComponent (ℜ.sNu ν))
    {Y₀ : Scheme.{u}} (g₀ : MonoidalSuccession X Y₀) (hg₀ : g₀.IsPermissibleII ℜ)
    (hfin : (sNuImage g₀ ℜ ν).Finite)
    (hdim : ∀ y ∈ sNuImage g₀ ℜ ν, X.dimAt y = (N : WithBot ℕ∞))
    (hdisj : ∀ i : Fin ℜ.α, (g₀.strictTransform (ℜ.E i)).pts ∩ (g₀.transformII ℜ).sNu ν = ∅) :
    ∃ (Y : Scheme.{u}) (g : MonoidalSuccession X Y), g.IsPermissibleII ℜ ∧
      (g.transformII ℜ).sNu ν = ∅ := by
  classical
  have key : ∀ n : ℕ, ∀ (Y : Scheme.{u}) (g : MonoidalSuccession X Y), g.IsPermissibleII ℜ →
      sNuImage g ℜ ν ⊆ sNuImage g₀ ℜ ν →
      (∀ i : Fin ℜ.α, (g.strictTransform (ℜ.E i)).pts ∩ (g.transformII ℜ).sNu ν = ∅) →
      (sNuImage g ℜ ν).ncard ≤ n →
      ∃ (Y' : Scheme.{u}) (g' : MonoidalSuccession X Y'), g'.IsPermissibleII ℜ ∧
        (g'.transformII ℜ).sNu ν = ∅ := by
    intro n
    induction n with
    | zero =>
      intro Y g hg hsub hd hn
      refine ⟨Y, g, hg, Set.eq_empty_iff_forall_notMem.mpr fun y hy => ?_⟩
      have hfin' : (sNuImage g ℜ ν).Finite := hfin.subset hsub
      have h0 : sNuImage g ℜ ν = ∅ := (Set.ncard_eq_zero hfin').mp (Nat.le_zero.mp hn)
      exact (Set.eq_empty_iff_forall_notMem.mp h0) _ ⟨y, hy, rfl⟩
    | succ n ih =>
      intro Y g hg hsub hd hn
      by_cases hZ : sNuImage g ℜ ν = ∅
      · refine ⟨Y, g, hg, Set.eq_empty_iff_forall_notMem.mpr fun y hy => ?_⟩
        exact (Set.eq_empty_iff_forall_notMem.mp hZ) _ ⟨y, hy, rfl⟩
      obtain ⟨x₀, hx₀⟩ := Set.nonempty_iff_ne_empty.mpr hZ
      obtain ⟨Z, e, he, hx₀', hd'⟩ := exists_extension_not_mem_sNuImage hN hII₂ X hX ℜ hℜ ν hν
        hνeq hno g hg (hfin.subset hsub) (fun y hy => hdim y (hsub hy)) hd hx₀
      have hsub' : sNuImage (g.append e) ℜ ν ⊆ sNuImage g ℜ ν :=
        sNuImage_append_subset hX ℜ hℜ g hg e he ν
      refine ih Z (g.append e) ((MonoidalSuccession.isPermissibleII_append g e ℜ).mpr ⟨hg, he⟩)
        (hsub'.trans hsub) hd' ?_
      have hlt : sNuImage (g.append e) ℜ ν ⊂ sNuImage g ℜ ν :=
        ⟨hsub', fun h => hx₀' (h hx₀)⟩
      have := Set.ncard_lt_ncard hlt (hfin.subset hsub)
      omega
  exact key _ Y₀ g₀ hg₀ subset_rfl hdisj le_rfl

/-- Theorem D* under the standing assumption of p. 314 that `S_ν(ℜ)` has no component of
codimension one: Propositions 3/4 (localization), Theorem II₁^N (condition `[(2)]`), then the core
step for each of the finitely many points of `h_s(S_ν(ℜ(s)))`. -/
theorem exists_isPermissibleII_sNu_eq_empty_of_noCodimOneComponent [Hironaka.HironakaCitedResults.{u}] {N : ℕ} (hN : 1 ≤ N)
    (hII₂ : ∀ N'' : ℕ, N'' < N → FundamentalTheorem.II₂.{u} N'')
    (hI₂ : ∀ n : ℕ, n < N → FundamentalTheorem.I₂.{u} N n)
    (hII₁ : FundamentalTheorem.II₁.{u} N)
    (X : Scheme.{u}) (hX : IsAmbient X N) (ℜ : DatumII.Raw X) (hℜ : ℜ.IsDatum) (ν : ℕ)
    (hν : 0 < ν) (hνeq : (ν : ℕ∞) = ℜ.nu) (hno : NoCodimOneComponent (ℜ.sNu ν)) :
    ∃ (Y : Scheme.{u}) (g : MonoidalSuccession X Y), g.IsPermissibleII ℜ ∧
      (g.transformII ℜ).sNu ν = ∅ := by
  classical
  have hνpos : 0 < ℜ.nu := by rw [← hνeq]; exact_mod_cast hν
  obtain ⟨Y₁, g₁, hg₁, hfin₁, hdim₁⟩ := exists_isPermissibleII_finite_image_Snu_dimAt_eq N hN
    hII₂ hI₂ X hX ⟨ℜ, hℜ⟩ hνpos
  rw [← hνeq] at hfin₁ hdim₁
  obtain ⟨hY₁, hd₁⟩ := g₁.isAmbient_transformII hX ℜ hℜ hg₁
  have := hX.1
  have hν₁ : (g₁.transformII ℜ).nu ≤ ℜ.nu := MonoidalSuccession.nu_transformII_le g₁ hX.2.1 ℜ hℜ hg₁
  by_cases hlt : (g₁.transformII ℜ).nu < (ν : ℕ∞)
  · exact ⟨Y₁, g₁, hg₁, DatumII.Raw.sNu_eq_empty_of_nu_lt hlt⟩
  · have heq : (g₁.transformII ℜ).nu = ℜ.nu := le_antisymm hν₁ (by rw [← hνeq]; exact not_lt.mp hlt)
    obtain ⟨Y₂, e₁, he₁, hdisj₁⟩ := exists_isPermissibleII_inter_strictTransform_sNu_eq_empty hII₁
      Y₁ hY₁ (g₁.transformII ℜ) hd₁ (by rw [heq]; exact hνpos) Finset.univ
    have hg₀ : (g₁.append e₁).IsPermissibleII ℜ :=
      (MonoidalSuccession.isPermissibleII_append g₁ e₁ ℜ).mpr ⟨hg₁, he₁⟩
    refine exists_isPermissibleII_sNu_eq_empty_of_sNuImage_finite hN hII₂ X hX ℜ hℜ ν hν hνeq hno
      (g₁.append e₁) hg₀ ?_ ?_ ?_
    · exact hfin₁.subset (sNuImage_append_subset hX ℜ hℜ g₁ hg₁ e₁ he₁ _)
    · exact fun y hy => hdim₁ y (sNuImage_append_subset hX ℜ hℜ g₁ hg₁ e₁ he₁ _ hy)
    · intro i
      obtain ⟨j, hj⟩ := g₁.exists_index_E_transformII_eq_strictTransform ℜ i
      rw [MonoidalSuccession.transformII_append, MonoidalSuccession.strictTransform_append, ← hj]
      have h := hdisj₁ j (Finset.mem_univ j)
      rwa [heq, ← hνeq] at h

section ClosedAssembly

variable {N : ℕ} {X : Scheme.{u}}

/-- p. 314: "A comparatively trivial observation shows that we may also assume the same for
Theorem C".  The closed analogue of `lem:IV.4-no-codim-one` (first assertion): the Localization
Theorem (Proposition 3 of §1) and Lemma (D.2) give a permissible succession for `(ℜ, F)` after
which `S_ν(f*(ℜ)) = S_ν(f*(ℜ^N_II)) ∩ F'` has no non-empty component of codimension one (the
second assertion, "continues to hold", is `noCodimOneComponent_transform_closed`).

\textbf{Deviation from the paper (gap filled).} The paper says only "a comparatively trivial
observation".  Lemma (D.2) for `ℜ^N_II` applies since `S_ν(f*ℜ) ⊆ S_ν(f*ℜ^N_II)`; a point of
`S_ν(f*ℜ) ∩ F'` whose local ring has dimension one maps to such a point of `X` (propagation lemma)
and the closed Localization Theorem puts the images at points of dimension `N`, whence the case
`N ≥ 2`.  For `N = 1` the closed points of `S_ν ∩ F` are blown up one at a time. -/
@[blueprint "lem:IV.4-no-codim-one-closed"
  (statement := /-- Let $N\ge1$ and suppose Theorems $\mathrm{II}_1^{N'}$ with $N'<N$ and
    Theorems $\mathrm I_2^{N,n}$ with $n<N$ are verified. Let $\mathfrak R=
    (\mathfrak R^N_{\mathrm{II}},F)$ be a resolution datum with closed restriction on a
    non-singular irreducible algebraic scheme $X$ of dimension $N$, and $\nu=\nu(\mathfrak R^N_{
    \mathrm{II}})>0$. Then there exists a permissible succession of monoidal transformations
    $f\colon X'\to X$ for $\mathfrak R$ such that $S_\nu(f^*(\mathfrak R))=S_\nu(f^*(\mathfrak
    R^N_{\mathrm{II}}))\cap F'$ does not contain any non-empty component of codimension $1$;
    moreover this continues to hold by any permissible monoidal transformation for $f^*(\mathfrak
    R)$. Thus in the proof of Theorem C, we may assume that $S_\nu(\mathfrak R)$ has no non-empty
    component of codimension $1$ in $X$. (p.~314: ``A comparatively trivial observation shows that
    we may also assume the same for Theorem C''.) -/)
  (proof := /-- As for \cref{lem:IV.4-no-codim-one}, with the Localization Theorem with closed
    restriction (\cref{prop:IV.1-3}) and Lemma (D.2) (\cref{lem:IV.D-2}) applied to $\mathfrak
    R^N_{\mathrm{II}}$, since $S_\nu(f^*\mathfrak R)\subseteq S_\nu(f^*\mathfrak
    R^N_{\mathrm{II}})$. A component of codimension $1$ of $S_\nu(f^*\mathfrak R)$ maps to a
    point of $X$ of dimension $1$, whereas the images of $S_\nu(f^*\mathfrak R)$ are points of
    dimension $N$ (for $N\ge2$). For the second assertion, a codimension-one component of
    $S_\nu\cap F$ after a permissible monoidal transformation is the strict transform of one
    before it (the strict transform of $F$ maps into $F$) or a component of the new exceptional
    divisor, which Lemma (D.2) excludes.

    \textbf{Deviation from the paper (gap filled).} The paper says only ``a comparatively trivial
    observation'' (p.~314). For $N=1$ the argument does not apply (every non-generic point of a
    curve has dimension $1=N$); Lean blows up the closed points of $S_\nu\cap F$ one at a time:
    each leaves $S_\nu$ by Lemma (D.2), and no new point enters since
    $f(S_\nu(f^*\mathfrak R))\subseteq S_\nu(\mathfrak R)$. -/)
  (proofUses := ["prop:IV.1-3", "lem:IV.D-2", "lem:IV.4-no-codim-one"])
  (latexEnv := "lemma")]
theorem exists_isPermissibleIIClosed_noCodimOneComponent_Snu [Hironaka.HironakaCitedResults.{u}] (N : ℕ) (hN : 1 ≤ N)
    (hII₁ : ∀ N' : ℕ, N' < N → FundamentalTheorem.II₁.{u} N')
    (hI₂ : ∀ n : ℕ, n < N → FundamentalTheorem.I₂.{u} N n)
    (X : Scheme.{u}) (hX : IsAmbient X N) (ℜ : DatumII X) (F : Subscheme X)
    (hF : (ℜ : DatumII.Raw X).IsClosedRestriction F)
    (hν : 0 < (ℜ : DatumII.Raw X).nu) :
    ∃ (X' : Scheme.{u}) (f : MonoidalSuccession X X'), f.IsPermissibleIIClosed ℜ F ∧
      NoCodimOneComponent (sNu (f.transformII ℜ) (.closed (f.strictTransform F))
        (ℜ : DatumII.Raw X).nu) := by
  rcases Nat.lt_or_ge N 2 with h | h
  · obtain rfl : N = 1 := by omega
    exact exists_permissible_noCodimOne_closed_of_eq_one X hX ℜ F hF hν
  · exact exists_permissible_noCodimOne_closed_of_two_le N h hII₁ hI₂ X hX ℜ F hF hν

end ClosedAssembly

end CD

/-- **Theorem D*** (p. 312): "Let the notation and the assumptions be the same as in Theorem D.
We assume that `ν = ν(ℜ) > 0`.  Then there exists a permissible succession of monoidal
transformations `f : X' → X` for `ℜ` such that `S_ν(f*(ℜ))` is empty." -/
@[blueprint "thm:IV.D-star"
  (statement := /-- \textbf{Theorem D*.} Let the notation and the assumptions be the same as in
    Theorem D (\cref{thm:IV.D}): $X$ is a non-singular irreducible algebraic scheme of dimension
    $N\ge1$, $\mathfrak R=\mathfrak R^N_{\mathrm{II}}$ a resolution datum on $X$ without
    restriction, and Theorems $\mathrm{II}_2^{N''}$ with $N''<N$, Theorems
    $\mathrm I_2^{N',n'}$ with $n'<N'\le N$, and Theorem $\mathrm{II}_1^N$ were verified. We
    assume that $\nu=\nu(\mathfrak R)>0$. Then there exists a permissible succession of
    monoidal transformations $f\colon X'\to X$ for $\mathfrak R$ such that
    $S_\nu(f^*(\mathfrak R))$ is empty (\cref{rem:IV.4-symbols-II}). (p.~312.) -/)
  (proof := /-- (pp.~314--326.) By Lemma (D.2) and the Localization Theorem (Proposition~4,
    \S1) we may assume that $S_\nu(\mathfrak R)$ has no non-empty component of codimension $1$
    in $X$ (\cref{lem:IV.4-no-codim-one}). By the localization theorems (Propositions~3 and~4
    of \S1, \cref{prop:IV.1-4}) we find a permissible succession $h_s$ such that [(1)]
    $h_s(S_\nu(\mathfrak R(s)))$ consists of a finite number of points at which $X$ has dimension
    $N$; ``moreover, for the case in which $\mathfrak R=\mathfrak R^N_{\mathrm{II}}$ without
    restriction, by applying Theorem $\mathrm{II}_1^N$ a finite number of times (in fact, at
    most $\alpha$ times), we may assume that [(2)] $E_i(s)\cap S_\nu(\mathfrak R(s))$ is empty
    for $1\le i\le\alpha$'' (p.~320; Theorem $\mathrm{II}_1^N$, \cref{thm:I.2-II1}, is applied to
    $\mathfrak R(s)$ with the closed restriction $E_i(s)$), \cref{def:IV.4-conditions}. The rest
    is the proof of pp.~320--326, common to Theorems C and D* and summarized at Theorem C
    (\cref{thm:IV.C}; \cref{lem:IV.4-x0}, \cref{lem:IV.4-setup-exists},
    \cref{lem:IV.4-tilde-facts}, \cref{lem:IV.4-case-ge-relation}, \cref{cor:IV.CD-4}), with
    $\tilde E_j=\hat E_{\alpha+j}(s)\cap\tilde X$, $1\le j\le\tilde\alpha=s$
    (\cref{def:IV.4-tilde}), the assumption [(2)] being used in Remarks~1--3
    (\cref{rem:IV.4-1}, \cref{rem:IV.4-2}, \cref{rem:IV.4-3}) to show that the $E_i(s)$,
    $i\le\alpha$, do not meet the centers, and Theorem $\mathrm{II}_2^{N-1}$
    (\cref{thm:I.2-II2}) resolving the datum $\mathfrak R^{N-1}_{\mathrm{II}}$ on $\tilde X$.

    \textbf{Deviation from the paper (gap filled).} The paper treats the finitely many points of
    $h_s(S_\nu(\mathfrak R(s)))$ implicitly (``we have now completed the proof''); Lean makes the
    induction explicit: for each point $x_0$ the core step (pp.~320--326) extends $h_s$ so that
    $x_0$ leaves $h_s(S_\nu)$ and $[(2)]$ is kept, no new point being created
    ($f(S_\nu(f^*\mathfrak R))\subseteq S_\nu(\mathfrak R)$), and the number of points drops; the
    application of Theorem $\mathrm{II}_1^N$ at most $\alpha$ times is made explicit for any finite
    set of indices. If $\nu(h_s^*\mathfrak R)<\nu$ after the localization, $S_\nu$ is already
    empty. The core step (\texttt{CD.exists\_extension\_not\_mem\_sNuImage}) is proved, including
    the non-vanishing of the stalks of $\bar J(s)$ (\cref{lem:IV.4-jbar-nonzero}). -/)
  (proofUses := ["lem:IV.4-no-codim-one", "prop:IV.1-4", "thm:I.2-II1", "def:IV.4-conditions",
    "lem:IV.4-x0", "lem:IV.4-setup-exists", "lem:IV.4-tilde-facts", "lem:IV.4-case-ge-relation",
    "cor:IV.CD-4", "rem:IV.4-1", "rem:IV.4-2", "rem:IV.4-3", "lem:IV.4-jbar-nonzero",
    "thm:I.2-II2"])
  (latexEnv := "theorem")]
theorem exists_isPermissibleII_Snu_eq_empty [Hironaka.HironakaCitedResults.{u}] (N : ℕ) (hN : 1 ≤ N)
    (hII₂ : ∀ N'' : ℕ, N'' < N → FundamentalTheorem.II₂.{u} N'')
    (hI₂ : ∀ N' n' : ℕ, n' < N' → N' ≤ N → FundamentalTheorem.I₂.{u} N' n')
    (hII₁ : FundamentalTheorem.II₁.{u} N)
    (X : Scheme.{u}) (hX : IsAmbient X N) (ℜ : DatumII X)
    (hν : 0 < (ℜ : DatumII.Raw X).nu) :
    ∃ (X' : Scheme.{u}) (f : MonoidalSuccession X X'),
      f.IsPermissibleII ℜ ∧ (f.transformII ℜ).sNu (ℜ : DatumII.Raw X).nu = ∅ := by
  classical
  obtain ⟨⟨X₀, f₀, hf₀, hno⟩, -⟩ :=
    exists_isPermissibleII_noCodimOneComponent_Snu_and_forall_transform
    N hN hII₂ (fun n hn => hI₂ N n hn le_rfl) X hX ℜ hν
  obtain ⟨hX₀, hd₀⟩ := f₀.isAmbient_transformII hX ℜ.1 ℜ.2 hf₀
  have := hX.1
  have hν₀ : (f₀.transformII ℜ.1).nu ≤ ℜ.1.nu :=
    MonoidalSuccession.nu_transformII_le f₀ hX.2.1 ℜ.1 ℜ.2 hf₀
  by_cases hlt : (f₀.transformII ℜ.1).nu < ℜ.1.nu
  · exact ⟨X₀, f₀, hf₀, DatumII.Raw.sNu_eq_empty_of_nu_lt hlt⟩
  · have heq : (f₀.transformII ℜ.1).nu = ℜ.1.nu := le_antisymm hν₀ (not_lt.mp hlt)
    have hfin : ℜ.1.nu ≠ ⊤ := DatumII.Raw.nu_ne_top hX.2.1 ℜ.1 ℜ.2.2.2.2
    have hn : ((ℜ.1.nu.toNat : ℕ) : ℕ∞) = ℜ.1.nu := ENat.natCast_toNat hfin
    have hnpos : 0 < ℜ.1.nu.toNat := by
      have : (0 : ℕ∞) < (ℜ.1.nu.toNat : ℕ∞) := by rw [hn]; exact hν
      exact_mod_cast this
    obtain ⟨Y, g', hg', hS⟩ := CD.exists_isPermissibleII_sNu_eq_empty_of_noCodimOneComponent hN hII₂
      (fun n hn' => hI₂ N n hn' le_rfl) hII₁ X₀ hX₀ (f₀.transformII ℜ.1) hd₀ ℜ.1.nu.toNat hnpos
      (by rw [hn, heq]) (by rw [hn]; exact hno)
    refine ⟨Y, f₀.append g', (MonoidalSuccession.isPermissibleII_append f₀ g' ℜ.1).mpr
      ⟨hf₀, hg'⟩, ?_⟩
    rw [MonoidalSuccession.transformII_append, ← hn]
    exact hS

/-- **Theorem D** (p. 311).  The hypotheses are read off the printed text: "Suppose Theorems `II₂^{N''}`
with `N'' < N`, Theorems `I₂^{N',n'}` with `n' < N' ≦ N`, and Theorem `II₁^N` were verified."
"`f*(ℜ)` is resolved at every
point of `X'`, i.e., `S(f*(ℜ))` is empty": the equivalence is `rem:IV.4-resolved-iff`.

Stated on p. 311; the declaration is placed after Theorem D*, Lemma (D.1) and the deduction
`exists_isPermissibleII_resolvedEverywhere_of_forall_exists_Snu_eq_empty` (`lem:IV.D-from-D-star`), because its proof in Lean is exactly the
paper's "Theorem D follows Theorem D*". -/
@[blueprint "thm:IV.D"
  (statement := /-- \textbf{Theorem D.} Let $X$ be a non-singular irreducible algebraic scheme
    of dimension $N\ge1$ and $\mathfrak R=\mathfrak R^N_{\mathrm{II}}$ a resolution datum on $X$
    (without restriction). Suppose Theorems $\mathrm{II}_2^{N''}$ with $N''<N$, Theorems
    $\mathrm I_2^{N',n'}$ with $n'<N'\le N$, and Theorem $\mathrm{II}_1^N$ were verified
    (\cref{thm:I.2-II2}, \cref{thm:I.2-I2}, \cref{thm:I.2-II1}). Then there exists a
    permissible succession of monoidal transformations $f\colon X'\to X$ for $\mathfrak R$ such
    that $f^*(\mathfrak R)$ is resolved at every point of $X'$ (\cref{def:I.4-II}), i.e.,
    $S(f^*(\mathfrak R))$ is empty (\cref{rem:IV.4-resolved-iff}). (p.~311.) -/)
  (proof := /-- ``We shall consider the following Theorem D*, which is a priori weaker than
    Theorem D, and shall prove that Theorem D follows Theorem D*'' (pp.~311--312). By Theorem D*
    (\cref{thm:IV.D-star}), applied to all data on non-singular irreducible schemes of dimension
    $N$ (the hypotheses of Theorem D* are those of Theorem D), there is a permissible succession
    $f_1\colon X_1\to X$ for $\mathfrak R$ such that $S_1(f_1^*(\mathfrak R))$ is empty, i.e.\
    $J'_{x'}$ is the local ring of $X_1$ at every $x'\in S(f_1^*(\mathfrak R))$
    (\cref{lem:IV.D-star-consequence}). Then Lemma (D.1) (\cref{lem:IV.D-1}) applied to
    $f_1^*(\mathfrak R)$ on $X_1$ gives a permissible succession $f_2\colon X'\to X_1$ with
    $S(f_2^*f_1^*(\mathfrak R))$ empty, and $f=f_1\circ f_2$ is a permissible succession for
    $\mathfrak R$ with $S(f^*(\mathfrak R))$ empty (\cref{def:I.8}), i.e.\ $f^*(\mathfrak R)$ is
    resolved at every point of $X'$ (\cref{rem:IV.4-resolved-iff}). This deduction is
    \cref{lem:IV.D-from-D-star}, checked in Lean. -/)
  (proofUses := ["thm:IV.D-star", "lem:IV.D-star-consequence", "lem:IV.D-1",
    "rem:IV.4-resolved-iff", "lem:IV.D-from-D-star"])
  (latexEnv := "theorem")]
theorem exists_isPermissibleII_resolvedEverywhere [Hironaka.HironakaCitedResults.{u}] (N : ℕ) (hN : 1 ≤ N)
    (hII₂ : ∀ N'' : ℕ, N'' < N → FundamentalTheorem.II₂.{u} N'')
    (hI₂ : ∀ N' n' : ℕ, n' < N' → N' ≤ N → FundamentalTheorem.I₂.{u} N' n')
    (hII₁ : FundamentalTheorem.II₁.{u} N)
    (X : Scheme.{u}) (hX : IsAmbient X N) (ℜ : DatumII X) :
    ∃ (X' : Scheme.{u}) (f : MonoidalSuccession X X'),
      f.IsPermissibleII ℜ ∧ (f.transformII ℜ).ResolvedEverywhere :=
  exists_isPermissibleII_resolvedEverywhere_of_forall_exists_Snu_eq_empty N (exists_isPermissibleII_Snu_eq_empty N hN hII₂ hI₂ hII₁) X hX ℜ

end

end Hironaka

/-- Paper name (Hironaka 1964) of `exists_isPermissibleII_Snu_eq_empty`. -/
alias _root_.Hironaka.theoremDStar := Hironaka.exists_isPermissibleII_Snu_eq_empty
/-- Paper name (Hironaka 1964) of `exists_isPermissibleII_resolvedEverywhere`. -/
alias _root_.Hironaka.theoremD := Hironaka.exists_isPermissibleII_resolvedEverywhere
