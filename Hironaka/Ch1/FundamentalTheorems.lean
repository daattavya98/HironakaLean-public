/-
Copyright (c) 2026 Daattavya Aggarwal, Minhyong Kim, Oisin Kim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daattavya Aggarwal, Minhyong Kim, Oisin Kim
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Architect
public import Hironaka.Ch1.ResolutionData
public import Hironaka.Ch1.InductionScheme
public import Hironaka.Statements

/-!
# Ch. I §2 (pp. 170–172): the fundamental theorems I₁^{N,n}, I₂^{N,n}, II₁^N, II₂^N

> In this section, we denote by X any non-singular irreducible algebraic scheme of dimension
> N ≧ 0. … The following four theorems will be referred to as the fundamental theorems of
> this paper, each of which depends upon either a pair of integers (N, n) or a single
> integer N such that N > n ≧ −1. The remainder of this paper is devoted primarily to the
> proofs of these four fundamental theorems for all (N, n) and N.

The statements are transcribed from pp. 170–171; the implication diagram from pp. 171–172 is
proved in Ch. IV (see the pointer at the end of this file).
Note: the predicate `IsAmbient` below requires only `N ≧ 0`, as in the paper, so the cases
`N = 0` of II₁, II₂ are not vacuous; they are proved (`FundamentalTheorem.II₁_zero_and_II₂_zero`).
The induction bookkeeping (that (A)–(D) plus the trivial cases yield everything) is proved,
Mathlib-free and sorry-free, in `Hironaka.Ch1.InductionScheme`.
-/

@[expose] public section

open AlgebraicGeometry

namespace Hironaka

universe u


/-! ### The four fundamental theorems (pp. 170–171) -/





/-- The four families, packaged for the induction scheme of `InductionScheme.lean`.
Note the indexing convention explained there: `n : ℕ`, the case `n = -1` (empty `W`) being
vacuous (it is stated and proved separately: `FundamentalTheorem.I₁Bot`, `FundamentalTheorem.I₂Bot`,
`FundamentalTheorem.I₁Bot_and_I₂Bot`). -/
@[blueprint "def:I.2-fundamental-family"
  (statement := /-- The family of fundamental theorems (\cref{def:I.2-family}) of the paper:
    $\mathrm I_1^{N,n}$, $\mathrm I_2^{N,n}$, $\mathrm{II}_1^N$, $\mathrm{II}_2^N$ are
    \cref{thm:I.2-I1}, \cref{thm:I.2-I2}, \cref{thm:I.2-II1}, \cref{thm:I.2-II2}
    respectively. -/)
  (latexEnv := "definition")]
def fundamentalFamily : FundamentalTheoremFamily where
  I₁ := FundamentalTheorem.I₁.{u}
  I₂ := FundamentalTheorem.I₂.{u}
  II₁ := FundamentalTheorem.II₁.{u}
  II₂ := FundamentalTheorem.II₂.{u}

/-! ### Trivial cases (p. 171) -/

/-- p. 171: "Theorems I₁^{N,n} and I₂^{N,n} are trivially true if n ≦ 0".
For `n = 0`, `W` is a finite set of closed points, so every subset of `W` is closed: for a
closed restriction `F`, density of `W − W ∩ F` in `W` forces `W ∩ F = ∅`; for an open
restriction, `U = W`.  The empty succession works.

Deviation from the paper (gap filled): the paper gives no argument; the one above is ours.
Only `n = 0` is stated here (`n = -1` is absent from the indexing; it is
`FundamentalTheorem.I₁Bot_and_I₂Bot` below). -/
@[blueprint "lem:I.2-trivial-I-n0"
  (statement := /-- Theorems $\mathrm I_1^{N,n}$ and $\mathrm I_2^{N,n}$ are trivially true if
    $n\le0$. (p.\ 171.) -/)
  (proof := /-- Take the empty succession, so nothing is transformed.  Since $X$ is an
    algebraic scheme its underlying space is noetherian, and $W$ is a subscheme of dimension
    $0$: its underlying space is a noetherian sober $T_0$ space in which every irreducible
    closed subset is maximal, so every point is closed and, the irreducible components being
    finitely many closures of points, $W$ is a finite set of closed points.  Hence every
    subset of $W$ is closed in $X$.  For a closed restriction $F$, $W-W\cap F$ is closed and
    dense in $W$, so $W\subseteq W-W\cap F$, i.e.\ $W\cap F=\emptyset$.  For an open
    restriction $U$, $U\subseteq W$ is closed and dense in $W$, so $U=W$ and $\mathfrak R$ is
    resolved at every point of $W$.

    \textbf{Gap in the paper filled.} The paper says only ``trivially true'' (p.~171); the
    argument above is ours. Only the case $n=0$ is formalized here ($n=-1$ is absent from the
    indexing, see \cref{def:I.2-family}; it is \cref{lem:I.2-trivial-I-minus-one}). -/)
  (latexEnv := "lemma")]
theorem FundamentalTheorem.I₁_zero_and_I₂_zero (N : ℕ) : FundamentalTheorem.I₁.{u} N 0 ∧ FundamentalTheorem.I₂.{u} N 0 := by
  constructor
  · intro X hX ℜ F hF hn
    have := hX.1
    have := IsAlgebraicScheme.noetherianSpace X
    have hW : (ℜ : DatumI.Raw X).W.dim ≤ 0 := by
      have : (ℜ : DatumI.Raw X).W.dim = 0 := by simpa [DatumI.Raw.n] using hn
      exact this.le
    refine ⟨X, MonoidalSuccession.nil X, trivial, ?_⟩
    show (ℜ : DatumI.Raw X).W.pts ∩ F.pts = ∅
    have hcl : IsClosed ((ℜ : DatumI.Raw X).W.pts \ F.pts) :=
      Subscheme.isClosed_of_subset_pts_of_dim_nonpos _ hW Set.sdiff_subset
    have hsub := hF.2.2
    rw [hcl.closure_eq] at hsub
    ext x
    simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false, not_and]
    intro hxW hxF
    exact (hsub hxW).2 hxF
  · intro X hX ℜ U hU hn
    have := hX.1
    have := IsAlgebraicScheme.noetherianSpace X
    have hW : (ℜ : DatumI.Raw X).W.dim ≤ 0 := by
      have : (ℜ : DatumI.Raw X).W.dim = 0 := by simpa [DatumI.Raw.n] using hn
      exact this.le
    refine ⟨X, MonoidalSuccession.nil X, trivial, ?_⟩
    show (ℜ : DatumI.Raw X).ResolvedEverywhere
    obtain ⟨⟨U₀, hU₀, rfl⟩, hdense, hres⟩ := hU
    have hcl : IsClosed (U₀ ∩ (ℜ : DatumI.Raw X).W.pts) :=
      Subscheme.isClosed_of_subset_pts_of_dim_nonpos _ hW Set.inter_subset_right
    rw [hcl.closure_eq] at hdense
    intro x hx
    exact hres x (hdense hx)

/-- In a non-singular scheme of dimension `0` every local ring is a field: it is a regular
local ring of dimension `0`, so its maximal ideal is generated by `0` elements. -/
theorem maximalIdeal_stalk_eq_bot_of_dim_eq_zero {X : Scheme.{u}} (hX : X.IsNonsingular)
    (hdim : X.dim = 0) (x : X) : IsLocalRing.maximalIdeal (X.presheaf.stalk x) = ⊥ := by
  have : IsRegularLocalRing (X.presheaf.stalk x) := hX x
  have hle : ringKrullDim (X.presheaf.stalk x) ≤ 0 := by
    have h : X.dimAt x ≤ X.dim := le_iSup (fun y => X.dimAt y) x
    rwa [hdim] at h
  have h := IsRegularLocalRing.spanFinrank_maximalIdeal (R := X.presheaf.stalk x)
  have h0 : (IsLocalRing.maximalIdeal (X.presheaf.stalk x)).spanFinrank = 0 := by
    have h1 : ((IsLocalRing.maximalIdeal (X.presheaf.stalk x)).spanFinrank : WithBot ℕ∞) ≤ 0 :=
      h ▸ hle
    exact Nat.le_zero.mp (by exact_mod_cast h1)
  exact (Submodule.spanFinrank_eq_zero_iff_eq_bot (IsNoetherian.noetherian _)).mp h0

/-- On an ambient scheme of dimension `0`, a resolution datum of type II has, at every point,
no `E_i` through the point and `ν(J_x) = 0`: the local ring is a field, so the non-zero ideal
`J_x` is the unit ideal, and an `E_i` through `x` would have codimension
`≤ ht(E_i)_x ≤ dim O_{X,x} = 0`. -/
theorem DatumII.Raw.weight_eq_zero_and_nuAt_eq_zero_of_dim_zero {X : Scheme.{u}}
    (hX : IsAmbient X 0) (ℜ : DatumII.Raw X) (hℜ : ℜ.IsDatum) (x : X) :
    ℜ.weight x = 0 ∧ ℜ.nuAt x = 0 := by
  have hdim : X.dim = 0 := by simpa using hX.2.2.2
  have hm := maximalIdeal_stalk_eq_bot_of_dim_eq_zero hX.2.1 hdim x
  have hle : ringKrullDim (X.presheaf.stalk x) ≤ 0 := by
    have h : X.dimAt x ≤ X.dim := le_iSup (fun y => X.dimAt y) x
    rwa [hdim] at h
  constructor
  · refine Finset.sum_eq_zero fun i hi => ?_
    exfalso
    have hx : x ∈ (ℜ.E i).pts := by
      simp only [Finset.mem_filter] at hi
      exact hi.2
    rcases hℜ.2.1 i with h | ⟨-, -, hcodim⟩
    · rw [h, DatumTransform.pts_empty] at hx
      exact hx
    · have hne := Subscheme.mem_pts_iff_stalkIdeal_ne_top.mp hx
      have hht : (((ℜ.E i).stalkIdeal x).height : WithBot ℕ∞) ≤ 0 :=
        (Ideal.height_le_ringKrullDim_of_ne_top hne).trans hle
      have hht0 : ((ℜ.E i).stalkIdeal x).height = 0 := by
        have : ((ℜ.E i).stalkIdeal x).height ≤ 0 := by exact_mod_cast hht
        exact nonpos_iff_eq_zero.mp this
      have hc : (ℜ.E i).codim ≤ (ℜ.E i).codimAt x := iInf₂_le x hx
      rw [hcodim, Subscheme.codimAt, hht0] at hc
      exact absurd hc (by norm_num)
  · have hJ : ¬ ℜ.J.stalkIdeal x ≤ IsLocalRing.maximalIdeal (X.presheaf.stalk x) := by
      rw [hm, le_bot_iff]
      exact hℜ.2.2.2 x
    have h1 : ¬ 1 ≤ ℜ.nuAt x := fun h =>
      hJ (((Ideal.ord_basic _ _ ⊥ ⊥).2.1).mp h)
    exact Order.lt_one_iff.mp (not_le.mp h1)

/-- p. 171: "theorems II₁^N and II₂^N [are trivially true] if N = 0", and more generally the
cases `N ≦ 1` are "more or less trivial and verified directly".  For the induction only the
`N = 0` cases are needed.

Deviation from the paper (gap filled): the paper gives no argument.  The proof is the paper's
intended one at every point `x` (`DatumII.Raw.weight_eq_zero_and_nuAt_eq_zero_of_dim_zero`):
the local ring `O_{X,x}` is regular of dimension `0`, hence a field, so `ν(J_x) = 0` and no
`E_i` (of codimension one) passes through `x`; so the datum is resolved everywhere and the
empty succession proves II₂⁰, while `ν(ℜ) = 0` makes II₁⁰ vacuous.  The Lean proof does not
use that `X` is a single point. -/
@[blueprint "lem:I.2-trivial-II-N0"
  (statement := /-- Theorems $\mathrm{II}_1^{N}$ and $\mathrm{II}_2^{N}$ are trivially true if
    $N=0$. (p.\ 171.) -/)
  (proof := /-- The paper gives no argument. Let $X$ be non-singular of dimension $0$ and let
    $x\in X$. The local ring $\mathcal O_{X,x}$ is regular of dimension $0$, hence a field.
    So the non-zero ideal $J_x$ is the unit ideal and $\nu(J_x)=0$, and no $E_i$ passes
    through $x$, since its codimension at $x$ would be at most $\dim\mathcal O_{X,x}=0$.
    Hence $\sum_{x\in E_i}a_i+\nu(J_x)=0<b$, so the datum is resolved everywhere and the empty
    succession proves $\mathrm{II}_2^0$. Moreover $\nu(\mathfrak R)=0$, so
    $\mathrm{II}_1^0$ is vacuous.

    \textbf{Gap in the paper filled.} The paper says only ``trivially true'' (p.~171); the
    argument above is ours, and it does not use that $X$ is a single point. -/)
  (latexEnv := "lemma")]
theorem FundamentalTheorem.II₁_zero_and_II₂_zero : FundamentalTheorem.II₁.{u} 0 ∧ FundamentalTheorem.II₂.{u} 0 := by
  constructor
  · intro X hX ℜ F hF hν
    exfalso
    have h0 : (ℜ : DatumII.Raw X).nu = 0 :=
      le_antisymm (iSup₂_le fun x _ =>
        (DatumII.Raw.weight_eq_zero_and_nuAt_eq_zero_of_dim_zero hX _ ℜ.2 x).2.le) bot_le
    rw [h0] at hν
    exact lt_irrefl 0 hν
  · intro X hX ℜ
    refine ⟨X, MonoidalSuccession.nil X, trivial, ?_⟩
    show (ℜ : DatumII.Raw X).ResolvedEverywhere
    intro x
    obtain ⟨hw, hn⟩ := DatumII.Raw.weight_eq_zero_and_nuAt_eq_zero_of_dim_zero hX _ ℜ.2 x
    show ((ℜ : DatumII.Raw X).weight x : ℕ∞) + (ℜ : DatumII.Raw X).nuAt x < (ℜ : DatumII.Raw X).b
    rw [hw, hn]
    exact_mod_cast ℜ.2.1

/-! ### The instances `n = -1` of Theorems I₁, I₂ (p. 171)

> In each of the above theorems, we do not exclude the empty succession of monoidal
> transformations. … In other words, we can take the empty succession of monoidal
> transformations in each of the theorems if the given resolution datum has the properties
> required on its transform by the succession. …  However, according to the implication diagram
> of induction stated below … all that must be maintained at this moment are theorems
> I₁^{N,−1}, I₂^{N,−1}, II₁⁰, and II₂⁰ for all non-negative integers N, which are all
> absolutely trivial.   (p. 171)

The families `FundamentalTheorem.I₁`, `FundamentalTheorem.I₂` above are indexed by `n : ℕ`, so the
paper's instances `n = -1` (empty `W`) are stated here as separate declarations, with the
hypothesis `ℜ.n = ⊥`: `-1` is the dimension of the empty scheme (p. 163, `Scheme.dim`:
`⊥ : WithBot ℕ∞` plays the role of `-1`), and `DatumI.Raw.n_eq_bot_iff` shows that `ℜ.n = ⊥` says
exactly that `W` is empty.  The instances II₁⁰, II₂⁰ are `FundamentalTheorem.II₁_zero_and_II₂_zero`. -/

/-- A subscheme has dimension `-1` (`⊥` in `WithBot ℕ∞`; p. 163: "We take the integer −1 as the
dimension of the empty scheme") if and only if it is empty: a point of `D` gives a local ring, of Krull dimension `≥ 0`, at a point of the scheme
`D`, and the supremum over no points is `⊥`. -/
theorem Subscheme.dim_eq_bot_iff {X : Scheme.{u}} (D : Subscheme X) : D.dim = ⊥ ↔ D.pts = ∅ := by
  have hpts : D.pts = Set.range D.ι := D.range_subschemeι.symm
  constructor
  · intro h
    refine Set.eq_empty_of_forall_notMem fun y hy => ?_
    rw [hpts] at hy
    obtain ⟨p, -⟩ := hy
    have h1 : D.toScheme.dimAt p ≤ D.dim := le_iSup (fun q => D.toScheme.dimAt q) p
    have h2 : (0 : WithBot ℕ∞) ≤ D.toScheme.dimAt p := ringKrullDim_nonneg_of_nontrivial
    rw [h] at h1
    exact absurd (h2.trans h1) (by simp)
  · intro h
    have hempty : IsEmpty D.toScheme := by
      refine ⟨fun p => ?_⟩
      have hp : D.ι p ∈ D.pts := by
        rw [hpts]
        exact Set.mem_range_self p
      rw [h] at hp
      exact absurd hp (Set.notMem_empty _)
    exact iSup_of_empty _

/-- For a datum of type I, `n = dim W = -1` (`ℜ.n = ⊥`) holds if and only if the principal
subscheme `W` is empty (Def. 3 (I)(iv), p. 164, with `-1` the dimension of the empty scheme, p. 163). -/
theorem DatumI.Raw.n_eq_bot_iff {X : Scheme.{u}} (ℜ : DatumI.Raw X) :
    ℜ.n = ⊥ ↔ ℜ.W.pts = ∅ :=
  ℜ.W.dim_eq_bot_iff



/-- p. 171: "all that must be maintained at this moment are theorems I₁^{N,−1}, I₂^{N,−1}, II₁⁰,
and II₂⁰ for all non-negative integers N, which are all absolutely trivial."  The printed route
(p. 171): "we can take the empty succession of monoidal transformations in each of the theorems if
the given resolution datum has the properties required on its transform by the succession".  For
`n = -1` the principal subscheme `W` is empty, so the datum has the required properties: `W` has no
point in common with `F`, and the datum is resolved at every point of the empty `W`.

Deviation from the paper (gap filled): the paper gives no argument beyond "absolutely trivial";
the one above (the empty succession, `W = ∅`) is ours. -/
@[blueprint "lem:I.2-trivial-I-minus-one"
  (statement := /-- Theorems $\mathrm I_1^{N,-1}$ and $\mathrm I_2^{N,-1}$ hold for every
    $N\ge0$. (p.\ 171: ``absolutely trivial''.) -/)
  (proof := /-- Take the empty succession, for which $f$ and $f^*$ are the identities (p.~171: ``we
    can take the empty succession of monoidal transformations in each of the theorems if the given
    resolution datum has the properties required on its transform by the succession'').  Since
    $\dim W=-1$, $W$ is empty (the dimension of a non-empty scheme is $\ge0$, \cref{def:I.0-dimension}).
    Hence $W$ has no point in common with $F$, and $\mathfrak R$ is resolved at every point of the
    empty $W$.

    \textbf{Gap in the paper filled.} The paper says only ``absolutely trivial'' (p.~171); the
    argument above is ours. -/)
  (latexEnv := "lemma")]
theorem FundamentalTheorem.I₁Bot_and_I₂Bot (N : ℕ) :
    FundamentalTheorem.I₁Bot.{u} N ∧ FundamentalTheorem.I₂Bot.{u} N := by
  constructor
  · intro X _ ℜ F _ hn
    have hW : (ℜ : DatumI.Raw X).W.pts = ∅ := (DatumI.Raw.n_eq_bot_iff _).mp hn
    refine ⟨X, MonoidalSuccession.nil X, trivial, ?_⟩
    show (ℜ : DatumI.Raw X).W.pts ∩ F.pts = ∅
    rw [hW, Set.empty_inter]
  · intro X _ ℜ U _ hn
    have hW : (ℜ : DatumI.Raw X).W.pts = ∅ := (DatumI.Raw.n_eq_bot_iff _).mp hn
    refine ⟨X, MonoidalSuccession.nil X, trivial, ?_⟩
    show (ℜ : DatumI.Raw X).ResolvedEverywhere
    intro x hx
    rw [hW] at hx
    exact absurd hx (Set.notMem_empty x)

/-! ### The families over the printed range `N > n ≧ −1` (p. 170)

> The following four theorems will be referred to as the fundamental theorems of this paper,
> each of which depends upon either a pair of integers `(N, n)` or a single integer `N` such that
> `N > n ≧ −1`.   (p. 170)

`FundamentalTheorem.I₁`, `FundamentalTheorem.I₂` are indexed by `n : ℕ`; `FundamentalTheorem.I₁Bot`,
`FundamentalTheorem.I₂Bot` are the instances `n = −1`.  The two definitions below put them in one
family indexed by the paper's `n ≧ −1`, with `WithBot ℕ` for `{−1, 0, 1, …}` (`⊥` is `−1`, as for
dimensions, p. 163). -/



theorem FundamentalTheorem.I₁WithBot_bot (N : ℕ) :
    FundamentalTheorem.I₁WithBot.{u} N ⊥ = FundamentalTheorem.I₁Bot.{u} N := rfl

theorem FundamentalTheorem.I₁WithBot_coe (N n : ℕ) :
    FundamentalTheorem.I₁WithBot.{u} N (n : WithBot ℕ) = FundamentalTheorem.I₁.{u} N n := rfl

theorem FundamentalTheorem.I₂WithBot_bot (N : ℕ) :
    FundamentalTheorem.I₂WithBot.{u} N ⊥ = FundamentalTheorem.I₂Bot.{u} N := rfl

theorem FundamentalTheorem.I₂WithBot_coe (N n : ℕ) :
    FundamentalTheorem.I₂WithBot.{u} N (n : WithBot ℕ) = FundamentalTheorem.I₂.{u} N n := rfl

/-! ### The implication diagram and the fundamental theorems (pp. 171–172): proved in Chapter IV

The implications (A)–(D) (`impl:A`–`impl:D`) and the fundamental theorems for all `(N, n)`
(`thm:I.2-fundamental`) are proved in Ch. IV, where the nodes now live (Ch. I cannot import it):
* `AB.implicationA_fundamentalFamily`, `AB.implicationB_fundamentalFamily`
  (`Hironaka/Ch4/TheoremsAB.lean`: Theorems A, B of §3, from Theorems A*, B*);
* `implicationC_fundamentalFamily` (`Hironaka/Ch4/TheoremC.lean`: Theorem C of §4);
* `implicationD_fundamentalFamily` and `allFundamentalTheorems_fundamentalFamily`
  (`Hironaka/Ch4/Conclusion.lean`: Theorem D of §4 and the conclusion of the paper, p. 326).

What stays here is p. 172: "It should be checked, and this is easily done, that these implications
(A), (B), (C), and (D) are sufficient for the fundamental theorems", checked in
`FundamentalTheoremFamily.allFundamentalTheorems_of_implications` (`Hironaka/Ch1/InductionScheme.lean`,
compiled, sorry-free), together with the base cases `FundamentalTheorem.I₁_zero_and_I₂_zero` and
`FundamentalTheorem.II₁_zero_and_II₂_zero` above. -/

end Hironaka

