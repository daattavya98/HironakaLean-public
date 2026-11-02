/-
Copyright (c) 2026 Daattavya Aggarwal, Minhyong Kim, Oisin Kim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daattavya Aggarwal, Minhyong Kim, Oisin Kim
-/
module

public import Architect

/-!
# Hironaka (1964), Chapter I, §2 — the implication diagram of induction

This file is *Mathlib-free*.  It isolates the purely combinatorial content of
Ch. I §2 (Annals 79, pp. 170–172): the four fundamental theorems are four families
of propositions

  I₁^{N,n}, I₂^{N,n}  (N > n ≥ -1),   II₁^N, II₂^N  (N ≥ 0),

and Hironaka claims (p. 172): "It should be checked, and this is easily done, that
these implications (A), (B), (C), and (D) are sufficient for the fundamental theorems."

Here we check it.  Indexing convention: the paper allows n = -1 (empty W) and notes
that I₁^{N,-1}, I₂^{N,-1}, II₁^0, II₂^0 are "absolutely trivial".  We index by `n : ℕ`
(so n = -1 is simply absent); the hypotheses "n'' < n" of (A), (B) are then vacuous at
n = 0, which is exactly the effect of the trivial n = -1 theorems.  The N = 0 cases of
II₁, II₂ remain explicit base cases.

The four implications are transcribed *verbatim* from pp. 171–172:

(A)  Given (N,n), 0 ≤ n < N:
       I₁^{N',n'} (n' < N' < N),  I₂^{N,n''} (n'' < n),  II₂^{N'} (N' < N)   ⟹  I₁^{N,n}.
(B)  Given (N,n), 0 ≤ n < N:
       I₂^{N',n'} (n' < N' < N),  I₂^{N,n''} (n'' < n),
       I₁^{N*,n*} (n* < N* ≤ N, n* ≤ n),  II₂^{N'} (N' < N)                  ⟹  I₂^{N,n}.
(C)  Given N ≥ 1:
       II₁^{N'} (N' < N),  I₂^{N*,n*} (n* < N* ≤ N),  II₂^{N'} (N' < N)      ⟹  II₁^N.
(D)  Given N ≥ 1:
       II₂^{N'} (N' < N),  I₂^{N*,n*} (n* < N* ≤ N),  II₁^N                  ⟹  II₂^N.

The only import is `Architect` (LeanArchitect), for the `@[blueprint]` annotations; the file
remains Mathlib-free.
-/

@[expose] public section

namespace Hironaka

/-- The four families of fundamental theorems of Ch. I §2, abstractly.
`I₁ N n` stands for Th. I₁^{N,n}, etc.  Only the values with `n < N` are meaningful. -/
@[blueprint "def:I.2-family"
  (statement := /-- A \emph{family of fundamental theorems} $T$ consists of four families of
    propositions $\mathrm I_1^{N,n}$, $\mathrm I_2^{N,n}$ ($N,n\in\mathbb N$) and
    $\mathrm{II}_1^N$, $\mathrm{II}_2^N$ ($N\in\mathbb N$).  Only the values with $n<N$ are
    meaningful.  Formalization note (encoding): the paper's index $n=-1$ (empty $W$) is
    absent: we index by $n\in\mathbb N$, so the hypotheses ``$n''<n$'' of (A) and (B) are
    vacuous at $n=0$, which is exactly the effect of the ``absolutely trivial'' theorems
    $\mathrm I_1^{N,-1}$, $\mathrm I_2^{N,-1}$. -/)
  (latexEnv := "definition")]
structure FundamentalTheoremFamily where
  I₁ : Nat → Nat → Prop
  I₂ : Nat → Nat → Prop
  II₁ : Nat → Prop
  II₂ : Nat → Prop

namespace FundamentalTheoremFamily

variable (T : FundamentalTheoremFamily)

/-- The implication (A) of p. 171. -/
@[blueprint "def:I.2-implication-A"
  (statement := /-- \textbf{Implication (A)} for a family $T$ (\cref{def:I.2-family}): for all
    $(N,n)$ with $0\le n<N$,
    \[ \mathrm I_1^{N',n'}\ (n'<N'<N),\quad \mathrm I_2^{N,n''}\ (n''<n),\quad
       \mathrm{II}_2^{N'}\ (N'<N) \qquad\Longrightarrow\qquad \mathrm I_1^{N,n}. \] -/)
  (latexEnv := "definition")]
def ImplicationA : Prop :=
  ∀ N n, n < N →
    (∀ N' n', n' < N' → N' < N → T.I₁ N' n') →
    (∀ n'', n'' < n → T.I₂ N n'') →
    (∀ N', N' < N → T.II₂ N') →
    T.I₁ N n

/-- The implication (B) of pp. 171–172. -/
@[blueprint "def:I.2-implication-B"
  (statement := /-- \textbf{Implication (B)} for a family $T$ (\cref{def:I.2-family}): for all
    $(N,n)$ with $0\le n<N$,
    \[ \mathrm I_2^{N',n'}\ (n'<N'<N),\quad \mathrm I_2^{N,n''}\ (n''<n),\quad
       \mathrm I_1^{N^*,n^*}\ (n^*<N^*\le N,\ n^*\le n),\quad
       \mathrm{II}_2^{N'}\ (N'<N) \qquad\Longrightarrow\qquad \mathrm I_2^{N,n}. \] -/)
  (latexEnv := "definition")]
def ImplicationB : Prop :=
  ∀ N n, n < N →
    (∀ N' n', n' < N' → N' < N → T.I₂ N' n') →
    (∀ n'', n'' < n → T.I₂ N n'') →
    (∀ N' n', n' < N' → N' ≤ N → n' ≤ n → T.I₁ N' n') →
    (∀ N', N' < N → T.II₂ N') →
    T.I₂ N n

/-- The implication (C) of p. 172. -/
@[blueprint "def:I.2-implication-C"
  (statement := /-- \textbf{Implication (C)} for a family $T$ (\cref{def:I.2-family}): for all
    $N\ge1$,
    \[ \mathrm{II}_1^{N'}\ (N'<N),\quad \mathrm I_2^{N^*,n^*}\ (n^*<N^*\le N),\quad
       \mathrm{II}_2^{N'}\ (N'<N) \qquad\Longrightarrow\qquad \mathrm{II}_1^{N}. \] -/)
  (latexEnv := "definition")]
def ImplicationC : Prop :=
  ∀ N, 1 ≤ N →
    (∀ N', N' < N → T.II₁ N') →
    (∀ N' n', n' < N' → N' ≤ N → T.I₂ N' n') →
    (∀ N', N' < N → T.II₂ N') →
    T.II₁ N

/-- The implication (D) of p. 172. -/
@[blueprint "def:I.2-implication-D"
  (statement := /-- \textbf{Implication (D)} for a family $T$ (\cref{def:I.2-family}): for all
    $N\ge1$,
    \[ \mathrm{II}_2^{N'}\ (N'<N),\quad \mathrm I_2^{N^*,n^*}\ (n^*<N^*\le N),\quad
       \mathrm{II}_1^{N} \qquad\Longrightarrow\qquad \mathrm{II}_2^{N}. \] -/)
  (latexEnv := "definition")]
def ImplicationD : Prop :=
  ∀ N, 1 ≤ N →
    (∀ N', N' < N → T.II₂ N') →
    (∀ N' n', n' < N' → N' ≤ N → T.I₂ N' n') →
    T.II₁ N →
    T.II₂ N

/-- The "absolutely trivial" base cases II₁^0 and II₂^0 (p. 171).  (The n = -1 base
cases are absorbed by the indexing convention, see the file header.) -/
@[blueprint "def:I.2-base-cases"
  (statement := /-- The \emph{base cases} for a family $T$ (\cref{def:I.2-family}): the
    propositions $\mathrm{II}_1^0$ and $\mathrm{II}_2^0$, which the paper calls ``absolutely
    trivial'' (p.~171).  The remaining trivial cases $\mathrm I_1^{N,-1}$, $\mathrm I_2^{N,-1}$
    are absorbed by the indexing convention. -/)
  (latexEnv := "definition")]
def BaseCases : Prop := T.II₁ 0 ∧ T.II₂ 0

/-- The complete statement Hironaka wants: all four families for all admissible indices. -/
@[blueprint "def:I.2-all-fundamental-theorems"
  (statement := /-- \emph{All fundamental theorems} for a family $T$ (\cref{def:I.2-family}):
    $\mathrm I_1^{N,n}$ and $\mathrm I_2^{N,n}$ hold for all $n<N$, and $\mathrm{II}_1^N$ and
    $\mathrm{II}_2^N$ hold for all $N$. -/)
  (latexEnv := "definition")]
def AllFundamentalTheorems : Prop :=
  (∀ N n, n < N → T.I₁ N n ∧ T.I₂ N n) ∧ (∀ N, T.II₁ N ∧ T.II₂ N)

/-- Ch. I §2, p. 172: the implications (A)–(D) together with the trivial base cases
imply all four fundamental theorems for all (N, n).  Proof: strong induction on N;
for fixed N, strong induction on n proves I₁^{N,n} (by (A)) and then I₂^{N,n} (by (B),
which needs I₁^{N,n} itself — hence the order); then (C) gives II₁^N and (D) gives II₂^N.

Deviation from the paper (gap filled): the paper leaves this check to the reader ("this is
easily done", p. 172); the argument is ours. -/
@[blueprint "thm:I.2-induction-scheme"
  (statement := /-- Let $T$ be a family of fundamental theorems (\cref{def:I.2-family})
    satisfying the implications (A), (B), (C), (D) (\cref{def:I.2-implication-A},
    \cref{def:I.2-implication-B}, \cref{def:I.2-implication-C}, \cref{def:I.2-implication-D})
    and the base cases (\cref{def:I.2-base-cases}).  Then all fundamental theorems hold for
    $T$ (\cref{def:I.2-all-fundamental-theorems}).  This is the claim of p.~172: ``It should
    be checked, and this is easily done, that these implications (A), (B), (C), and (D) are
    sufficient for the fundamental theorems.'' -/)
  (proof := /-- Strong induction on $N$.  Fix $N$ and assume all four families of theorems
    for every $N'<N$.  First, by strong induction on $n<N$: implication (A) gives
    $\mathrm I_1^{N,n}$, its hypotheses $\mathrm I_1^{N',n'}$ ($n'<N'<N$) and
    $\mathrm{II}_2^{N'}$ ($N'<N$) coming from the outer induction and $\mathrm I_2^{N,n''}$
    ($n''<n$) from the inner one.  Then implication (B) gives $\mathrm I_2^{N,n}$; its
    hypothesis $\mathrm I_1^{N^*,n^*}$ ($n^*<N^*\le N$, $n^*\le n$) is supplied by the outer
    induction when $N^*<N$, by the inner induction when $N^*=N$ and $n^*<n$, and by the
    $\mathrm I_1^{N,n}$ just obtained when $(N^*,n^*)=(N,n)$.  This is why (A) must be
    applied before (B).  Second, for $N=0$ the theorems $\mathrm{II}_1^0$, $\mathrm{II}_2^0$
    are the base cases; for $N\ge1$ implication (C) gives $\mathrm{II}_1^N$, using the
    $\mathrm I_2^{N^*,n^*}$ ($n^*<N^*\le N$) obtained so far, and then implication (D) gives
    $\mathrm{II}_2^N$.

    \textbf{Gap in the paper filled.} The paper only says ``It should be checked, and this is
    easily done'' (p.~172); the argument above is ours. The one point needing care is that
    (B) uses $\mathrm I_1^{N,n}$ itself, so (A) must be applied before (B) at each $(N,n)$. -/)
  (latexEnv := "theorem")]
theorem allFundamentalTheorems_of_implications
    (hA : T.ImplicationA) (hB : T.ImplicationB) (hC : T.ImplicationC) (hD : T.ImplicationD)
    (h0 : T.BaseCases) : T.AllFundamentalTheorems := by
  have key : ∀ N, (∀ n, n < N → T.I₁ N n ∧ T.I₂ N n) ∧ (T.II₁ N ∧ T.II₂ N) := by
    intro N
    induction N using Nat.strongRecOn with
    | ind N ih =>
      -- Step 1: the theorems I₁^{N,n}, I₂^{N,n} for all n < N, by strong induction on n.
      have hI : ∀ n, n < N → T.I₁ N n ∧ T.I₂ N n := by
        intro n
        induction n using Nat.strongRecOn with
        | ind n ihn =>
          intro hn
          have hI₁n : T.I₁ N n :=
            hA N n hn
              (fun N' n' hn'N' hN'N => ((ih N' hN'N).1 n' hn'N').1)
              (fun n'' h => (ihn n'' h (Nat.lt_trans h hn)).2)
              (fun N' h => (ih N' h).2.2)
          have hI₂n : T.I₂ N n :=
            hB N n hn
              (fun N' n' hn'N' hN'N => ((ih N' hN'N).1 n' hn'N').2)
              (fun n'' h => (ihn n'' h (Nat.lt_trans h hn)).2)
              (fun N' n' hn'N' hN'N hn'n => by
                rcases Nat.lt_or_eq_of_le hN'N with hN'N | rfl
                · exact ((ih N' hN'N).1 n' hn'N').1
                · rcases Nat.lt_or_eq_of_le hn'n with hn'n | rfl
                  · exact (ihn n' hn'n hn'N').1
                  · exact hI₁n)
              (fun N' h => (ih N' h).2.2)
          exact ⟨hI₁n, hI₂n⟩
      refine ⟨hI, ?_⟩
      -- Step 2: the theorems II₁^N, II₂^N.
      rcases Nat.eq_zero_or_pos N with rfl | hN
      · exact h0
      · have hI₂ : ∀ N' n', n' < N' → N' ≤ N → T.I₂ N' n' := by
          intro N' n' h1 h2
          rcases Nat.lt_or_eq_of_le h2 with h2 | rfl
          · exact ((ih N' h2).1 n' h1).2
          · exact (hI n' h1).2
        have hII₁ : T.II₁ N :=
          hC N hN (fun N' h => (ih N' h).2.1) hI₂ (fun N' h => (ih N' h).2.2)
        exact ⟨hII₁, hD N hN (fun N' h => (ih N' h).2.2) hI₂ hII₁⟩
  exact ⟨fun N n h => (key N).1 n h, fun N => (key N).2⟩

end FundamentalTheoremFamily

end Hironaka
