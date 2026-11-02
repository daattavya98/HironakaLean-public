/-
Copyright (c) 2026 Daattavya Aggarwal, Minhyong Kim, Oisin Kim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daattavya Aggarwal, Minhyong Kim, Oisin Kim
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Architect
public import Hironaka.Ch4.TheoremC
public import Hironaka.Ch4.TheoremsAB
public import Hironaka.Statements

/-!
# Ch. IV §4, end (p. 326): the fundamental theorems

> We have now completed the proof of Theorems C and D, and combining this with the result of the
> preceding section we have established an inductive proof of the *fundamental theorems* which
> were announced in §2, Ch. I.  (p. 326)

The last file of the chain: the implication (D) from Theorem D (`Ch4/ImplicationsCD.lean`), the
implication (C) from Theorem C (`Ch4/TheoremC.lean`) and the implications (A), (B) from Theorems
A and B (`Ch4/TheoremsAStarBStar.lean`) give the fundamental theorems by the induction scheme of
Ch. I §2.
-/

@[expose] public section

open AlgebraicGeometry IsLocalRing CategoryTheory CategoryTheory.Limits

namespace Hironaka

universe u

noncomputable section

/-! ## The end of the paper (p. 326)

> In view of Remarks 2 and 3, the proof of Theorems C and D* can be easily reduced to the
> resolution of the `ℜ^{N-1}_II` on `X̃`, defined as above, which can be done by Theorem
> `II₂^{N-1}`.
>
> We have now completed the proof of Theorems C and D, and combining this with the result of the
> preceding section we have established an inductive proof of the *fundamental theorems* which
> were announced in §2, Ch. I.  (p. 326.) -/

/-- The implication (D) of Ch. I §2 (p. 172) follows from Theorem D (`impl:D`; the Ch. I node is a
pointer to this proof). -/
@[blueprint "impl:D"
  (statement := /-- \textbf{The implication (D).} Given $N\ge1$:
    Th.\ $\mathrm{II}_2^{N'}$ for $N'<N$, Th.\ $\mathrm I_2^{N^*,n^*}$ for $n^*<N^*\le N$, and
    Th.\ $\mathrm{II}_1^{N}$ together imply Th.\ $\mathrm{II}_2^{N}$. (Lean:
    \cref{def:I.2-implication-D}.) The proof is in Ch.~IV: Theorem~D (\cref{thm:IV.D}, p.~311). -/)
  (proof := /-- Theorem D (\cref{thm:IV.D}) has exactly these hypotheses, and its conclusion,
    for every non-singular irreducible $X$ of dimension $N$ and every datum
    $\mathfrak R^N_{\mathrm{II}}$ on $X$, is the conclusion of Theorem $\mathrm{II}_2^N$
    (\cref{thm:I.2-II2}). -/)
  (latexEnv := "corollary")]
theorem implicationD_fundamentalFamily [Hironaka.HironakaCitedResults.{u}] : fundamentalFamily.{u}.ImplicationD := by
  intro N hN hII₂ hI₂ hII₁ X hX ℜ
  exact exists_isPermissibleII_resolvedEverywhere N hN hII₂ hI₂ hII₁ X hX ℜ

/-- p. 172 and p. 326: the fundamental theorems for all `(N, n)` (`thm:I.2-fundamental`; the Ch. I
node is a pointer to this proof).  "We have now completed the proof of Theorems C and D, and
combining this with the result of the preceding section we have established an inductive proof of
the fundamental theorems which were announced in §2, Ch. I." (p. 326)

Deviation from the paper (statement modified): the Lean statement covers `n ≥ 0` only (the
trivially true `n = -1` instances are `FundamentalTheorem.I₁Bot_and_I₂Bot`; the two together, over
the printed range `N > n ≧ −1`, are `allFundamentalTheorems_printedRange`).  The `N = 0` instances of II₁, II₂ are covered
non-vacuously (`IsAmbient` does not require `0 < N`). -/
@[blueprint "thm:I.2-fundamental"
  (statement := /-- The fundamental theorems $\mathrm I_1^{N,n}$, $\mathrm I_2^{N,n}$,
    $\mathrm{II}_1^N$, $\mathrm{II}_2^N$ hold for all integers $N>n\ge-1$, $N\ge0$.

    \textbf{Deviation from the paper (statement modified).} The Lean statement covers only
    $n\ge0$ (the ``absolutely trivial'' instances with $n=-1$ are \cref{lem:I.2-trivial-I-minus-one};
    both together, over the printed range, are \cref{thm:I.2-fundamental-printed}). The instances
    $N=0$ of $\mathrm{II}_1$, $\mathrm{II}_2$ are covered non-vacuously (the Lean predicate
    \texttt{IsAmbient} does not require $0<N$).

    The proof is in Ch.~IV: ``In view of Remarks 2 and 3, the proof of Theorems C and D* can be
    easily reduced to the resolution of the $\mathfrak R^{N-1}_{\mathrm{II}}$ on $\tilde X$,
    defined as above, which can be done by Theorem $\mathrm{II}_2^{N-1}$. We have now completed
    the proof of Theorems C and D, and combining this with the result of the preceding section we
    have established an inductive proof of the fundamental theorems which were announced in
    \S2, Ch.~I'' (p.~326). -/)
  (proof := /-- Apply the induction scheme (\cref{thm:I.2-induction-scheme}) to the family of
    fundamental theorems (\cref{def:I.2-fundamental-family}): the implications (A), (B) follow
    from Theorems A and B of \S3 (\cref{impl:A}, \cref{impl:B}), the implications (C), (D) from
    Theorems C and D (\cref{impl:C}, \cref{impl:D}), and the base cases are
    \cref{lem:I.2-trivial-II-N0}. -/)
  (proofUses := ["thm:I.2-induction-scheme", "impl:A", "impl:B", "impl:C", "impl:D",
    "lem:I.2-trivial-II-N0"])
  (latexEnv := "theorem")]
theorem allFundamentalTheorems_fundamentalFamily [Hironaka.HironakaCitedResults.{u}] : fundamentalFamily.{u}.AllFundamentalTheorems :=
  FundamentalTheoremFamily.allFundamentalTheorems_of_implications fundamentalFamily.{u}
    AB.implicationA_fundamentalFamily AB.implicationB_fundamentalFamily
    implicationC_fundamentalFamily implicationD_fundamentalFamily
    ⟨FundamentalTheorem.II₁_zero_and_II₂_zero.1, FundamentalTheorem.II₁_zero_and_II₂_zero.2⟩

/-- The fundamental theorems over the printed range (pp. 170–171): "each of which depends upon
either a pair of integers `(N, n)` or a single integer `N` such that `N > n ≧ −1`", established "for
all possible integers `N` and `n` (`N > n ≧ −1` and `N ≧ 0`)" (p. 171).

Here `N : ℕ` (so `N ≧ 0`) and `n : WithBot ℕ`, with `⊥` playing `−1` (as for dimensions, p. 163), so
that `n < N` is `N > n ≧ −1`.  For `n ≧ 0` this is `allFundamentalTheorems_fundamentalFamily`; for
`n = −1` it is `FundamentalTheorem.I₁Bot_and_I₂Bot` (p. 171: "absolutely trivial"); `II₁^N`,
`II₂^N` are for all `N`.  Statements of the four theorems are unchanged. -/
@[blueprint "thm:I.2-fundamental-printed"
  (statement := /-- The fundamental theorems $\mathrm I_1^{N,n}$, $\mathrm I_2^{N,n}$,
    $\mathrm{II}_1^N$, $\mathrm{II}_2^N$ hold for all integers $N>n\ge-1$ and $N\ge0$ (pp.~170,
    171: ``for all possible integers $N$ and $n$ ($N>n\geqq-1$ and $N\geqq0$)''). Formalization
    note (encoding): $n$ ranges over the natural numbers and $-1$ (Lean: \texttt{WithBot}~$\mathbb N$,
    with $\bot=-1$); the instances $n\ge0$ are \cref{thm:I.2-fundamental}, the instances $n=-1$ are
    \cref{lem:I.2-trivial-I-minus-one}. -/)
  (proof := /-- Split on $n$: for $n\ge0$ this is \cref{thm:I.2-fundamental}; for $n=-1$ it is
    \cref{lem:I.2-trivial-I-minus-one}; $\mathrm{II}_1^N$, $\mathrm{II}_2^N$ are from
    \cref{thm:I.2-fundamental}. -/)
  (proofUses := ["thm:I.2-fundamental", "lem:I.2-trivial-I-minus-one"])
  (latexEnv := "theorem")]
theorem allFundamentalTheorems_printedRange [Hironaka.HironakaCitedResults.{u}] :
    (∀ (N : ℕ) (n : WithBot ℕ), n < (N : WithBot ℕ) →
      FundamentalTheorem.I₁WithBot.{u} N n ∧ FundamentalTheorem.I₂WithBot.{u} N n) ∧
    (∀ N : ℕ, FundamentalTheorem.II₁.{u} N ∧ FundamentalTheorem.II₂.{u} N) := by
  obtain ⟨hI, hII⟩ := allFundamentalTheorems_fundamentalFamily.{u}
  refine ⟨fun N n hn => ?_, hII⟩
  induction n using WithBot.recBotCoe with
  | bot => exact FundamentalTheorem.I₁Bot_and_I₂Bot N
  | coe n => exact hI N n (WithBot.coe_lt_coe.mp hn)

/-! ## How Theorems C and D yield the implications (C) and (D) of Ch. I §2

The implications (C), (D) of Ch. I §2 (`impl:C`, `impl:D`, whose Lean statements are
`fundamentalFamily.ImplicationC` and `fundamentalFamily.ImplicationD` of
`Hironaka/Ch1/InductionScheme.lean`) are, for each `N ≥ 1`, the statements "the assumed
fundamental theorems imply `II₁^N`, resp. `II₂^N`".  Theorems C and D (p. 311) have precisely
these hypotheses (read off the printed text: `II₁^{N'}` for `N' < N`, `I₂^{N',n'}` for `n' < N' ≦ N`,
`II₂^{N'}` for `N' < N`, resp. `II₂^{N''}` for `N'' < N`, `I₂^{N',n'}` for `n' < N' ≦ N`,
`II₁^N`).  The conclusion of Theorem D is that of `II₂^N`.  Theorem C carries the extra
assumption `ν(ℜ) = ν(ℜ^N_II)`; the remaining case `ν(ℜ) < ν(ℜ^N_II)` of `II₁^N` is trivial (the
empty succession), which `implicationC_fundamentalFamily` (in `Ch4/TheoremC.lean`) proves.  Hence
`implicationC_fundamentalFamily` and `implicationD_fundamentalFamily` are proved in Lean from
`exists_isPermissibleIIClosed_Snu_eq_empty_of_nu_closed_eq` and
`exists_isPermissibleII_resolvedEverywhere`, and `allFundamentalTheorems_fundamentalFamily`
re-derives all four fundamental theorems from Theorems A–D.

Status of the pieces (`#print axioms` of each declaration lists the cited results that
remain): Theorem D rests on Theorem D*, which is the core step
(`exists_extension_not_mem_sNuImage`: Lemma (D.2) and
`exists_isPermissibleII_noCodimOneComponent_Snu_and_forall_transform`, Lemmas (CD.3)–(CD.5), the
Corollary of (CD.4), Remarks 1–3, the localization theorems `prop:IV.1-3`, `prop:IV.1-4`, Theorem
`II₁^N` for `[(2)]` and Theorem `II₂^{N-1}` for the datum on `X̃`) with the induction on the
finitely many points of `h_s(S_ν(ℜ(s)))`; Theorem C is the same with the closed restriction and
the repaired auxiliary datum (`CD.exists_extension_not_mem_sNuImageClosed`, `Ch4/TheoremC.lean`).
The nodes `impl:A`–`impl:D` and `thm:I.2-fundamental` of Ch. I §2 live in Ch. IV (Ch. I cannot
cite this file): they are `AB.implicationA_fundamentalFamily`, `AB.implicationB_fundamentalFamily`
(`Ch4/TheoremsAB.lean`), `implicationC_fundamentalFamily` (`Ch4/TheoremC.lean`),
`implicationD_fundamentalFamily` and `allFundamentalTheorems_fundamentalFamily` (this file). -/

end

end Hironaka

