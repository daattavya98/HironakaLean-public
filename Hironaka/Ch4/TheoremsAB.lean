/-
Copyright (c) 2026 Daattavya Aggarwal, Minhyong Kim, Oisin Kim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daattavya Aggarwal, Minhyong Kim, Oisin Kim
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Architect
public import Hironaka.Ch4.AStarBStarLifting
public import Hironaka.Ch4.AStarBStarAssembly
public import Hironaka.Statements

/-!
# Ch. IV §3 (pp. 293–310): Theorems A*, B*, A, B and the implications (A), (B)

The last file of the chain of §3 (after `Hironaka/Ch4/AStarBStarLifting.lean`):

* pp. 293–294: Theorems A* and B* (`thm:IV.A-star`, `thm:IV.B-star`), proved from the one-block
  lemma (`exists_extension_of_stageResolvable_succ`, p. 310) by
  `exists_isPermissibleI{Closed,Open}_hasEffectiveProperties_of_oneBlockHyp`
  (`Hironaka/Ch4/AStarBStarAssembly.lean`);
* p. 293: Theorems A and B (`thm:IV.A`, `thm:IV.B`), from Theorems A*, B* by Lemma (AB.1)
  (`lem:IV.AB-1-consequence`);
* the implications (A), (B) of Ch. I §2 as consequences of Theorems A, B (`impl:A`, `impl:B`; the
  Ch. I nodes are pointers to these proofs).

These declarations keep the names, namespaces and blueprint labels they had in
`Hironaka/Ch4/TheoremsAStarBStar.lean` (from which they were moved when the proof of Theorems A*,
B* was completed).  The notation and the formalization notes are those of the module header of
`Hironaka/Ch4/ImplicationsAB.lean`.
-/

@[expose] public section

open AlgebraicGeometry IsLocalRing CategoryTheory CategoryTheory.Limits

namespace Hironaka

universe u

noncomputable section

namespace AB

/-! ## Theorems A* and B* (pp. 293–294) -/

/-- **Theorem A*** (p. 293).

Proved, with the proof corrected for the paper's error on the subschemes `Ẽ_j`: the finite iteration
over the points of `g_s(S(ℜ(s)))` is `exists_hasEffectiveProperties_of_onePointStep`
(`lem:IV.3-finite-iteration`), the step at one point `x_0` is the one-point step
(`onePointStep_of_oneBlockStep`, `lem:IV.3-one-point-step`), and the block of p. 310, replacing
`g_s` by an extension that induces one monoidal transformation of `X̃`, is the one-block lemma
`exists_extension_of_stageResolvable_succ` (`lem:IV.3-one-block`,
`Hironaka/Ch4/AStarBStarLifting.lean`).  The statement is the printed one. -/
@[blueprint "thm:IV.A-star"
  (statement := /-- \textbf{Theorem A*.} Let the notation and assumptions be the same as in
    Theorem A (\cref{thm:IV.A}). Then there exists a permissible succession of monoidal
    transformations of $X$ for $\mathfrak R$, say $f\colon X'\to X$, such that if
    $\mathfrak R'=f^*(\mathfrak R)$ and
    $f^*(\mathfrak R^{N,n}_{\mathrm I})=(\bigcup_{i=1}^{\alpha'}E_i';V_1',\dots,V_\beta';W')$,
    we have
    \begin{enumerate}
      \item[(i)] $f(S(\mathfrak R'))$ (\cref{def:IV.3-S}) is at most a finite number of points
        of $X$ at which $X$ has dimension $N$, and
      \item[(ii)] for every $x'\in S(\mathfrak R')$ at which $X'$ has dimension $N$, we have
        either (a) $\nu^*_{x'}(V_1',\dots,V_\beta',W'/X')<\nu^*_x(V_1,\dots,V_\beta,W/X)$, or
        (b) $\nu^*_{x'}(V_1',\dots,V_\beta',W'/X')=\nu^*_x(V_1,\dots,V_\beta,W/X)$ and
        $\tau^*_{x'}(V_1',\dots,V_\beta',W'/X')>\tau^*_x(V_1,\dots,V_\beta,W/X)$
        (\cref{def:IV.3-characters}, \cref{def:IV.3-inequalities}),
    \end{enumerate}
    where $x=f(x')$. (p.~293.) (Formalization notes (encoding): $V_j'$, $W'$ are the strict
    transforms
    of $V_j$, $W$, which are the members of $f^*(\mathfrak R^{N,n}_{\mathrm I})$; the
    characters at $x'$ and $x$ are formed where $X'$ and $X$ are simple, and (a) or (b) is
    asserted whenever they are.) -/)
  (proof := /-- (pp.~307--310.) First of all, by the Localization Theorem
    (\cref{prop:IV.1-1}) we can find a permissible succession of monoidal transformations
    $g_s=\{f_t\colon X_{t+1}\to X_t\}$ $(0\le t<s)$ such that [(1)] the image in $X=X_0$ of
    $S(\mathfrak R(s))=F(s)\cap W(s)$ consists of a finite number of points, at which $X$ has
    dimension $N$. Let $x_0$ be any point of $X$ which is in the image
    $g_s(S(\mathfrak R(s)))$. With reference to $x_0$ and to $g_s$ we construct, as on
    pp.~294--299, the succession $\hat g_s=\{\hat f_t\}$ with the morphisms
    $c_t\colon\hat X_t\to X_t$, the integer $b$, the open subschemes $X_t'$, $\hat X_t'$, the
    subschemes $\bar X_t$, $\bar X_t'$ and the sheaves $\bar J(t)$ on $\bar X_t'$
    (\cref{def:IV.3-setup}, \cref{def:IV.3-frame}, \cref{def:IV.3-construction},
    \cref{lem:IV.3-setup-exists}). We are only interested in the case in which $\bar X_s'$ has
    dimension $N-1$, which is the case if there is a point of $S(\mathfrak R(s))$ with the
    properties (1), (2), (3) of Lemma (AB.4) (by its Corollary, \cref{cor:IV.AB-4-componentwise}).
    Let
    $\tilde X=\bar X_s'$ and consider the datum $\mathfrak R^{N-1}_{\mathrm{II}}
    =(\tilde E_1,\dots,\tilde E_{\tilde\alpha}\,|\,\tilde J,b\,|\,a_1,\dots,a_{\tilde\alpha})$
    of \cref{rem:IV.3-2}, \cref{rem:IV.3-3}. If $\tilde B$ is the center of a permissible
    monoidal transformation of $\tilde X$ for $\mathfrak R^{N-1}_{\mathrm{II}}$ and $B_s$ the
    corresponding reduced irreducible subscheme of $X_s$, then, applying Theorem
    $\mathrm I_2^{N,n'}$ (\cref{thm:I.2-I2}, $n'=\dim B_s<n$) to the datum
    $(\mathfrak R^{N,n'}_{\mathrm I}(s),U_s)$ of \cref{rem:IV.3-4}, we resolve
    $\mathfrak R^{N,n'}_{\mathrm I}(s)$ by a finite permissible succession, whose members are
    successively permissible for $\mathfrak R(s)$ and induce trivial monoidal transformations
    of $\tilde X$ (\cref{rem:IV.3-4}, \cref{rem:IV.3-5}). Replacing $g_s$ to include this
    succession, the monoidal transformation with center $B_s$ is permissible for
    $\mathfrak R(s)$ and induces the given one of $\tilde X$ for
    $\mathfrak R^{N-1}_{\mathrm{II}}$. Thus, applying Theorem $\mathrm{II}_2^{N-1}$
    (\cref{thm:I.2-II2}) to $\mathfrak R^{N-1}_{\mathrm{II}}$ on $\tilde X$, there is a finite
    permissible succession of monoidal transformations of $X_s$ for $\mathfrak R(s)$ which
    induces one of $\tilde X$ resolving $\mathfrak R^{N-1}_{\mathrm{II}}$; including it in
    $g_s$, we may assume $\nu_x(\bar J(s))<b$ for every point $x$ of $\tilde X$. By
    the Corollary of Lemma (AB.4) (\cref{cor:IV.AB-4-componentwise}) there is then no point of
    $X_s$ having the properties (1), (2), (3) of Lemma (AB.4) with reference to $x_0$; equivalently,
    by \cref{lem:IV.3-thm3-consequence}, if $x$ is any point of $X_s$ at which $X_s$ has
    dimension $N$ and $g_s(x)=x_0$, then either
    $\nu^*_x(V_1(s),\dots,V_\beta(s),W(s)/X_s)<\nu^*_{x_0}(V_1,\dots,V_\beta,W/X)$ or they
    are equal and $\tau^*_x(V_1(s),\dots,V_\beta(s),W(s)/X_s)>
    \tau^*_{x_0}(V_1,\dots,V_\beta,W/X)$. Since $g_s(S(\mathfrak R(s)))$ consists of a finite
    number of points at which $X$ has dimension $N$, repeating the above process at most a
    finite number of times we achieve the demonstration of Theorem A*.

    \textbf{Deviation from the paper (construction corrected).} The printed condition [g] of
    \cref{def:IV.3-construction} and the first assertion of Lemma (AB.4) rest on the false
    irreducibility of $\hat B_s$ (\cref{lem:IV.AB-4-componentwise}). The Lean main
    line uses, in place of $X_t'$, $\hat X_t'$, $\bar X_t'$, the open subschemes
    $\hat X_t^{*\prime}$, $\bar X_t^{*\prime}$ of the corrected construction
    (\cref{def:IV.3-construction-componentwise}, the family $U_t=\hat X_t^{*\prime}$ of
    \cref{lem:IV.3-construction-facts-generic}): the step ``which is the case if there is a
    point of $S(\mathfrak R(s))$ with the properties (1), (2), (3)'' and the step ``By the
    Corollary of Lemma (AB.4) there is then no point of $X_s$ having the properties (1), (2),
    (3)'' use \cref{cor:IV.AB-4-componentwise} (proved from
    \cref{lem:IV.AB-4-componentwise}) instead of the printed Corollary; Lemmas (AB.5), (AB.6) and
    Remarks~2--5 are used for the family $\hat X_t^{*\prime}$
    (\cref{lem:IV.AB-5-generic}, \cref{lem:IV.AB-6-generic}, \cref{rem:IV.3-2-generic},
    \cref{rem:IV.3-3-generic}, \cref{rem:IV.3-4-generic}, \cref{rem:IV.3-5-generic}). The
    rest of the argument is unchanged.

    \textbf{Deviation from the paper (proof corrected; repair of the paper's error on the subschemes $\tilde E_j$).} The
    datum $\mathfrak R^{N-1}_{\mathrm{II}}$ to which the paper applies Theorem
    $\mathrm{II}_2^{N-1}$ is not a resolution datum in general;
    Lean applies it to the weak datum with its whole-space entries emptied. The replacement of
    $g_s$ is carried out one monoidal transformation of $\tilde X$ at a time:
    \cref{lem:IV.3-finite-iteration} (the iteration over the finitely many points of
    $g_s(S(\mathfrak R(s)))$), \cref{lem:IV.3-one-point-step} (the step at one point $x_0$) and
    \cref{lem:IV.3-one-block} (the block of p.~310: $B_s$, the succession of Theorem
    $\mathrm I_2^{N,n'}$, the monoidal transformation with center the strict transform of
    $B_s$). -/)
  (proofUses := ["prop:IV.1-1", "lem:IV.3-setup-exists", "lem:IV.3-thm3-consequence",
    "def:IV.3-construction-componentwise", "lem:IV.AB-4-componentwise",
    "cor:IV.AB-4-componentwise", "lem:IV.AB-5-generic", "lem:IV.AB-6-generic",
    "rem:IV.3-2-generic", "rem:IV.3-3-generic", "rem:IV.3-4-generic", "rem:IV.3-5-generic",
    "thm:I.2-I2", "thm:I.2-II2", "lem:IV.3-finite-iteration", "lem:IV.3-one-point-step",
    "lem:IV.3-one-block"])
  (latexEnv := "theorem")]
theorem exists_isPermissibleIClosed_hasEffectiveProperties [Hironaka.HironakaCitedResults.{u}] (N n : ℕ) (hNn : n < N)
    (hI₁ : ∀ N' n' : ℕ, n' < N' → N' < N → FundamentalTheorem.I₁.{u} N' n')
    (hI₂ : ∀ n'' : ℕ, n'' < n → FundamentalTheorem.I₂.{u} N n'')
    (hII₂ : ∀ N' : ℕ, N' < N → FundamentalTheorem.II₂.{u} N')
    (X : Scheme.{u}) (hX : IsAmbient X N) (ℜ : DatumI X) (F : Subscheme X)
    (hF : (ℜ : DatumI.Raw X).IsClosedRestriction F)
    (hn : (ℜ : DatumI.Raw X).n = (n : WithBot ℕ∞)) :
    ∃ (X' : Scheme.{u}) (f : MonoidalSuccession X X'),
      f.IsPermissibleIClosed ℜ F ∧ HasEffectiveProperties N ℜ (.closed F) f := by
  have hFr : (Restriction.closed F).IsFor (ℜ : DatumI.Raw X) := hF
  exact exists_isPermissibleIClosed_hasEffectiveProperties_of_oneBlockHyp N n hNn hI₁ hI₂ hII₂ X
    hX ℜ F hF hn fun P x₀ hx₀ _ z b Jgen fr {Y} g hg hfin hbd hx k hQ =>
      exists_extension_of_stageResolvable_succ N n hNn hI₂ X hX ℜ P (.closed F) hFr hn x₀ hx₀ z b
        Jgen fr g hg hfin hbd hx k hQ

/-- **Theorem B*** (pp. 293–294).

Proved, with the proof corrected for the paper's error on the subschemes `Ẽ_j`, exactly as Theorem A*
(`exists_isPermissibleIClosed_hasEffectiveProperties`): the finite iteration, the one-point step and
the one-block lemma `exists_extension_of_stageResolvable_succ` for the open restriction `U`.  The
statement is the printed one. -/
@[blueprint "thm:IV.B-star"
  (statement := /-- \textbf{Theorem B*.} Let the notation and the assumptions be the same as in
    Theorem B (\cref{thm:IV.B}). Then there exists a permissible succession of monoidal
    transformations of $X$ for $\mathfrak R$ which has the same properties (i) and (ii) as in
    Theorem A* (\cref{thm:IV.A-star}). (pp.~293--294.) -/)
  (proof := /-- (pp.~307--310.) The proof is the same as that of Theorem A*
    (\cref{thm:IV.A-star}), with the following changes. The succession $g_s$ is found by the
    Localization Theorem on $(\mathfrak R^{N,n}_{\mathrm I},U)$ (\cref{prop:IV.1-2}) and the
    Preparation Theorem (\cref{prop:IV.2-5}), applied $\alpha$ times repeatedly, so that
    [(1)] the image in $X$ of $S(\mathfrak R(s))$ (the closed subset of $W(s)$ of the points
    at which $\mathfrak R(s)$ is not resolved) consists of a finite number of points at which
    $X$ has dimension $N$, and [(2)] if $W_1(s)$ is any irreducible component of $W(s)$ and
    $1\le i\le\alpha$, then either $W_1(s)\subseteq E_i(s)$ or $E_i(s)\cap W_1(s)\cap
    S(\mathfrak R(s))$ is empty. By Remark 1 (\cref{rem:IV.3-1}), $W$ is singular at $x_0$ or
    some $V_j$ is not normally flat along $W$ at $x_0$, which is what makes
    \cref{rem:IV.3-3}, \cref{rem:IV.3-4}, \cref{rem:IV.3-5} applicable through
    \cref{lem:IV.AB-5}. The frame $(T;z)$ is chosen $\hat J_0$-stable ([b] of
    \cref{def:IV.3-frame}). The rest of the argument is literally the same.

    \textbf{Deviation from the paper (construction corrected).} As for Theorem A*
    (\cref{thm:IV.A-star}): the Lean main line uses the corrected construction
    \cref{def:IV.3-construction-componentwise} with \cref{cor:IV.AB-4-componentwise} in place
    of the printed Corollary of Lemma (AB.4), and Lemmas (AB.5), (AB.6), Remarks~2--5 for the family
    $\hat X_t^{*\prime}$.

    \textbf{Deviation from the paper (proof corrected; repair of the paper's error on the subschemes $\tilde E_j$).} As for
    Theorem A* (\cref{thm:IV.A-star}): Theorem $\mathrm{II}_2^{N-1}$ is applied to the weak datum
    $\mathfrak R^{N-1}_{\mathrm{II}}$ with its whole-space entries emptied, and $g_s$ is replaced
    one monoidal transformation of $\tilde X$ at a time (\cref{lem:IV.3-finite-iteration},
    \cref{lem:IV.3-one-point-step}, \cref{lem:IV.3-one-block}). -/)
  (proofUses := ["prop:IV.1-2", "prop:IV.2-5", "rem:IV.3-1", "lem:IV.3-setup-exists",
    "lem:IV.3-thm3-consequence", "def:IV.3-construction-componentwise",
    "lem:IV.AB-4-componentwise", "cor:IV.AB-4-componentwise", "lem:IV.AB-5-generic",
    "lem:IV.AB-6-generic", "rem:IV.3-2-generic", "rem:IV.3-3-generic", "rem:IV.3-4-generic",
    "rem:IV.3-5-generic", "thm:I.2-I2", "thm:I.2-II2", "lem:IV.3-finite-iteration",
    "lem:IV.3-one-point-step", "lem:IV.3-one-block"])
  (latexEnv := "theorem")]
theorem exists_isPermissibleIOpen_hasEffectiveProperties [Hironaka.HironakaCitedResults.{u}] (N n : ℕ) (hNn : n < N)
    (hI₂' : ∀ N' n' : ℕ, n' < N' → N' < N → FundamentalTheorem.I₂.{u} N' n')
    (hI₂ : ∀ n'' : ℕ, n'' < n → FundamentalTheorem.I₂.{u} N n'')
    (hI₁ : ∀ N' n' : ℕ, n' < N' → N' ≤ N → n' ≤ n → FundamentalTheorem.I₁.{u} N' n')
    (hII₂ : ∀ N' : ℕ, N' < N → FundamentalTheorem.II₂.{u} N')
    (X : Scheme.{u}) (hX : IsAmbient X N) (ℜ : DatumI X) (U : Set X)
    (hU : (ℜ : DatumI.Raw X).IsOpenRestriction U)
    (hn : (ℜ : DatumI.Raw X).n = (n : WithBot ℕ∞)) :
    ∃ (X' : Scheme.{u}) (f : MonoidalSuccession X X'),
      f.IsPermissibleIOpen ℜ U ∧ HasEffectiveProperties N ℜ (.opn U) f := by
  have hUr : (Restriction.opn U).IsFor (ℜ : DatumI.Raw X) := hU
  exact exists_isPermissibleIOpen_hasEffectiveProperties_of_oneBlockHyp N n hNn hI₂' hI₂ hI₁ hII₂
    X hX ℜ U hU hn fun P x₀ hx₀ _ z b Jgen fr {Y} g hg hfin hbd hx k hQ =>
      exists_extension_of_stageResolvable_succ N n hNn hI₂ X hX ℜ P (.opn U) hUr hn x₀ hx₀ z b
        Jgen fr g hg hfin hbd hx k hQ

/-! ## Theorems A and B (p. 293)

Stated here, after Theorems A*, B* and the consequence of Lemma (AB.1), from which they follow. -/

/-- **Theorem A** (p. 293).  The index conditions are read off the printed text: "Assume that
Theorems `I₁^{N',n'}` with `n' < N' < N`, Theorems `I₂^{N,n''}` with `n'' < n`, and Theorems
`II₂^{N'}` with `N' < N` are all verified."

Formalization note: the expression `(⋃ E_i; V_1, …, V_β; W)` is notation (p. 274) and does not
enter the statement. -/
@[blueprint "thm:IV.A"
  (statement := /-- \textbf{Theorem A.} Let $X$ be a non-singular irreducible algebraic scheme
    of dimension $N$, and let $\mathfrak R=(\mathfrak R^{N,n}_{\mathrm I},F)$ with
    $\mathfrak R^{N,n}_{\mathrm I}=(\bigcup_{i=1}^\alpha E_i;V_1,\dots,V_\beta;W)$ be the
    given resolution datum on $X$ (\cref{def:I.3-I}, \cref{def:I.5-I.1}), where $N>n\ge0$.
    Assume that Theorems $\mathrm I_1^{N',n'}$ with $n'<N'<N$, Theorems
    $\mathrm I_2^{N,n''}$ with $n''<n$, and Theorems $\mathrm{II}_2^{N'}$ with $N'<N$ are all
    verified (\cref{thm:I.2-I1}, \cref{thm:I.2-I2}, \cref{thm:I.2-II2}). Then we can find a
    permissible succession of monoidal transformations of $X$ for the datum $\mathfrak R$,
    say $f\colon X'\to X$, such that $W'\cap F'$ is empty, where
    $f^*(\mathfrak R)=(f^*(\mathfrak R^{N,n}_{\mathrm I}),F')$ with
    $f^*(\mathfrak R^{N,n}_{\mathrm I})=(\bigcup_{i=1}^{\alpha'}E_i';V_1',\dots,V_\beta';W')$.
    (p.~293.) -/)
  (proof := /-- Theorem A follows from Theorem A* (\cref{thm:IV.A-star}) by Lemma (AB.1)
    (\cref{lem:IV.AB-1}), in the form \cref{lem:IV.AB-1-consequence}: ``We first claim that
    Theorems A and B follow Theorems A* and B* respectively. In other words, we have Lemma
    (AB.1)'' (p.~294). The assumptions of Theorem A for $(N,n)$ contain those of Theorem A* for
    $(N,n')$ for every $n'\le n$, so every datum $(\mathfrak R^{N,n'}_{\mathrm I},F)$ with
    $n'\le n$ on a non-singular irreducible algebraic scheme of dimension $N$ admits an
    effective modification (\cref{def:IV.3-effective-modification}). By
    \cref{lem:IV.AB-1-consequence} there is a permissible succession $f$ with
    $S(f^*(\mathfrak R))=W'\cap F'=\emptyset$ (\cref{def:IV.3-S}). The proof of Theorem A*
    occupies pp.~294--310. -/)
  (proofUses := ["thm:IV.A-star", "lem:IV.AB-1", "lem:IV.AB-1-consequence"])
  (latexEnv := "theorem")]
theorem exists_isPermissibleIClosed_inter_eq_empty [Hironaka.HironakaCitedResults.{u}] (N n : ℕ) (hNn : n < N)
    (hI₁ : ∀ N' n' : ℕ, n' < N' → N' < N → FundamentalTheorem.I₁.{u} N' n')
    (hI₂ : ∀ n'' : ℕ, n'' < n → FundamentalTheorem.I₂.{u} N n'')
    (hII₂ : ∀ N' : ℕ, N' < N → FundamentalTheorem.II₂.{u} N')
    (X : Scheme.{u}) (hX : IsAmbient X N) (ℜ : DatumI X) (F : Subscheme X)
    (hF : (ℜ : DatumI.Raw X).IsClosedRestriction F)
    (hn : (ℜ : DatumI.Raw X).n = (n : WithBot ℕ∞)) :
    ∃ (X' : Scheme.{u}) (f : MonoidalSuccession X X'),
      f.IsPermissibleIClosed ℜ F ∧
      (f.transformI ℜ).W.pts ∩ (f.strictTransform F).pts = ∅ := by
  have heff : ∀ (X' : Scheme.{u}), IsAmbient X' N → ∀ (ℜ' : DatumI.Raw X'), ℜ'.IsDatum →
      ∀ r' : Restriction X', r'.IsFor ℜ' → (r'.IsClosedKind ↔ (Restriction.closed F).IsClosedKind) →
      ∀ n' : ℕ, n' ≤ n → ℜ'.n = (n' : WithBot ℕ∞) →
        ∃ (Y : Scheme.{u}) (f : MonoidalSuccession X' Y), IsEffectiveModification N ℜ' r' f := by
    intro X' hX' ℜ' hℜ' r' hr' hk n' hn' hnn'
    cases r' with
    | closed F' =>
      obtain ⟨Y, f, hf, hfe⟩ := exists_isPermissibleIClosed_hasEffectiveProperties N n'
        (lt_of_le_of_lt hn' hNn) hI₁
        (fun n'' h => hI₂ n'' (lt_of_lt_of_le h hn')) hII₂ X' hX' ⟨ℜ', hℜ'⟩ F' hr' hnn'
      exact ⟨Y, f, hf, hfe⟩
    | opn U' => exact absurd (hk.mpr trivial) id
  obtain ⟨Y, f, hf, hS⟩ :=
    exists_isPermissibleSucc_S_eq_empty_of_forall_exists_isEffectiveModification N n hNn X hX ℜ
      ℜ.2 hn (.closed F) hF heff
  exact ⟨Y, f, hf, hS⟩

/-- **Theorem B** (p. 293).  The index conditions are read off the printed text: "Assume that
Theorems `I₂^{N',n'}` with `n' < N' < N`, Theorems `I₂^{N,n''}` with `n'' < n`, Theorems
`I₁^{N*,n*}` with `n* < N* ≤ N` and `n* ≤ n`, and Theorems `II₂^{N'}` with `N' < N` are all
verified." -/
@[blueprint "thm:IV.B"
  (statement := /-- \textbf{Theorem B.} Let $X$ be a non-singular irreducible algebraic scheme
    of dimension $N$, and let $\mathfrak R=(\mathfrak R^{N,n}_{\mathrm I},U)$ with
    $\mathfrak R^{N,n}_{\mathrm I}=(\bigcup_{i=1}^\alpha E_i;V_1,\dots,V_\beta;W)$ be the
    given resolution datum on $X$ (\cref{def:I.3-I}, \cref{def:I.5-I.2}), where $N>n\ge0$.
    Assume that Theorems $\mathrm I_2^{N',n'}$ with $n'<N'<N$, Theorems
    $\mathrm I_2^{N,n''}$ with $n''<n$, Theorems $\mathrm I_1^{N^*,n^*}$ with
    $n^*<N^*\le N$ and $n^*\le n$, and Theorems $\mathrm{II}_2^{N'}$ with $N'<N$ are all
    verified (\cref{thm:I.2-I1}, \cref{thm:I.2-I2}, \cref{thm:I.2-II2}). Then we can find a
    permissible succession of monoidal transformations of $X$ for the datum $\mathfrak R$,
    say $f\colon X'\to X$, such that $f^*(\mathfrak R^{N,n}_{\mathrm I})$ is resolved at every
    point of $W'$ (\cref{def:I.4-I}), where $W'$ is as in Theorem A (\cref{thm:IV.A}).
    (p.~293.) -/)
  (proof := /-- Theorem B follows from Theorem B* (\cref{thm:IV.B-star}) by Lemma (AB.1)
    (\cref{lem:IV.AB-1}), in the form \cref{lem:IV.AB-1-consequence}, exactly as Theorem A
    follows from Theorem A* (\cref{thm:IV.A}): the assumptions of Theorem B for $(N,n)$
    contain those of Theorem B* for $(N,n')$, $n'\le n$, so every datum
    $(\mathfrak R^{N,n'}_{\mathrm I},U)$ with $n'\le n$ admits an effective modification, and
    a permissible succession $f$ with $S(f^*(\mathfrak R))=\emptyset$ is one for which
    $f^*(\mathfrak R^{N,n}_{\mathrm I})$ is resolved at every point of $W'$
    (\cref{def:IV.3-S}). -/)
  (proofUses := ["thm:IV.B-star", "lem:IV.AB-1", "lem:IV.AB-1-consequence"])
  (latexEnv := "theorem")]
theorem exists_isPermissibleIOpen_resolvedEverywhere [Hironaka.HironakaCitedResults.{u}] (N n : ℕ) (hNn : n < N)
    (hI₂' : ∀ N' n' : ℕ, n' < N' → N' < N → FundamentalTheorem.I₂.{u} N' n')
    (hI₂ : ∀ n'' : ℕ, n'' < n → FundamentalTheorem.I₂.{u} N n'')
    (hI₁ : ∀ N' n' : ℕ, n' < N' → N' ≤ N → n' ≤ n → FundamentalTheorem.I₁.{u} N' n')
    (hII₂ : ∀ N' : ℕ, N' < N → FundamentalTheorem.II₂.{u} N')
    (X : Scheme.{u}) (hX : IsAmbient X N) (ℜ : DatumI X) (U : Set X)
    (hU : (ℜ : DatumI.Raw X).IsOpenRestriction U)
    (hn : (ℜ : DatumI.Raw X).n = (n : WithBot ℕ∞)) :
    ∃ (X' : Scheme.{u}) (f : MonoidalSuccession X X'),
      f.IsPermissibleIOpen ℜ U ∧ (f.transformI ℜ).ResolvedEverywhere := by
  have heff : ∀ (X' : Scheme.{u}), IsAmbient X' N → ∀ (ℜ' : DatumI.Raw X'), ℜ'.IsDatum →
      ∀ r' : Restriction X', r'.IsFor ℜ' → (r'.IsClosedKind ↔ (Restriction.opn U).IsClosedKind) →
      ∀ n' : ℕ, n' ≤ n → ℜ'.n = (n' : WithBot ℕ∞) →
        ∃ (Y : Scheme.{u}) (f : MonoidalSuccession X' Y), IsEffectiveModification N ℜ' r' f := by
    intro X' hX' ℜ' hℜ' r' hr' hk n' hn' hnn'
    cases r' with
    | closed F' => exact absurd (hk.mp trivial) id
    | opn U' =>
      obtain ⟨Y, f, hf, hfe⟩ := exists_isPermissibleIOpen_hasEffectiveProperties N n'
        (lt_of_le_of_lt hn' hNn)
        (fun N' n'' h1 h2 => hI₂' N' n'' h1 h2)
        (fun n'' h => hI₂ n'' (lt_of_lt_of_le h hn'))
        (fun N' n'' h1 h2 h3 => hI₁ N' n'' h1 h2 (h3.trans hn')) hII₂ X' hX' ⟨ℜ', hℜ'⟩ U' hr' hnn'
      exact ⟨Y, f, hf, hfe⟩
  obtain ⟨Y, f, hf, hS⟩ :=
    exists_isPermissibleSucc_S_eq_empty_of_forall_exists_isEffectiveModification N n hNn X hX ℜ
      ℜ.2 hn (.opn U) hU heff
  refine ⟨Y, f, hf, fun x hx => ?_⟩
  by_contra hres
  have hmem : x ∈ S (f.transformI ℜ) ((Restriction.opn U).transformSucc f) := ⟨hx, hres⟩
  rw [hS] at hmem
  exact hmem

/-! ## How Theorems A and B yield the implications (A) and (B) of Ch. I §2

The implications (A), (B) of Ch. I §2 (`impl:A`, `impl:B`, whose Lean statements are
`fundamentalFamily.ImplicationA` and `fundamentalFamily.ImplicationB` of
`Hironaka/Ch1/InductionScheme.lean`) are, for each `(N, n)` with `0 ≤ n < N`, exactly the
statements "the assumed fundamental theorems imply `I₁^{N,n}`, resp. `I₂^{N,n}`".  Theorems A
and B (p. 293) have precisely these hypotheses (read off the printed text: `I₁^{N',n'}` for
`n' < N' < N`, `I₂^{N,n''}` for `n'' < n`, `II₂^{N'}` for `N' < N`, resp. `I₂^{N',n'}` for
`n' < N' < N`, `I₂^{N,n''}` for `n'' < n`, `I₁^{N*,n*}` for `n* < N* ≤ N`, `n* ≤ n`,
`II₂^{N'}` for `N' < N`) and their conclusions are, for a given `X`, `ℜ`, `F` (resp. `U`), the
conclusions of `I₁^{N,n}` (`W' ∩ F' = ∅`, the principal subscheme of `f*(ℜ)` being `W'`) and
`I₂^{N,n}` (`f*(ℜ)` resolved at every point of `W'`).  Hence `implicationA_fundamentalFamily` and
`implicationB_fundamentalFamily` below are proved in Lean by merely introducing the variables and
applying `exists_isPermissibleIClosed_inter_eq_empty`, resp.
`exists_isPermissibleIOpen_resolvedEverywhere`.  Theorems A, B follow from Theorems A*, B* by
Lemma (AB.1) (`exists_isPermissibleIClosed_inter_eq_empty`,
`exists_isPermissibleIOpen_resolvedEverywhere`), and Theorems A*, B* are proved above from the
one-block lemma (pp. 293–310).  Ch. I cannot cite these proofs because it is imported by this
file; the nodes `impl:A`, `impl:B` therefore live here, and `allFundamentalTheorems_fundamentalFamily`
(`Hironaka/Ch4/Conclusion.lean`, node `thm:I.2-fundamental`) re-derives the fundamental theorems
from `implicationA_fundamentalFamily`, `implicationB_fundamentalFamily` and the analogous results
for (C), (D). -/

/-- The implication (A) of Ch. I §2 (p. 171) follows from Theorem A (`impl:A`; the Ch. I node is a
pointer to this proof). -/
@[blueprint "impl:A"
  (statement := /-- \textbf{The implication (A).} Given $(N,n)$ with $0\le n<N$:
    Th.\ $\mathrm I_1^{N',n'}$ for $n'<N'<N$, Th.\ $\mathrm I_2^{N,n''}$ for $n''<n$, and
    Th.\ $\mathrm{II}_2^{N'}$ for $N'<N$ together imply Th.\ $\mathrm I_1^{N,n}$. (Lean:
    \cref{def:I.2-implication-A}.) The proof is in Ch.~IV: Theorem~A (\cref{thm:IV.A}, p.~293;
    ``In this section, we shall give proofs to the implications (A) and (B) which were announced
    in Ch.~I, \S2'', p.~292). -/)
  (proof := /-- Theorem A (\cref{thm:IV.A}) has exactly these hypotheses, and its conclusion,
    for every non-singular irreducible $X$ of dimension $N$ and every
    $(\mathfrak R^{N,n}_{\mathrm I},F)$ on $X$, is the conclusion of Theorem
    $\mathrm I_1^{N,n}$ (\cref{thm:I.2-I1}). -/)
  (latexEnv := "corollary")]
theorem implicationA_fundamentalFamily [Hironaka.HironakaCitedResults.{u}] : fundamentalFamily.{u}.ImplicationA := by
  intro N n hNn hI₁ hI₂ hII₂ X hX ℜ F hF hn
  exact exists_isPermissibleIClosed_inter_eq_empty N n hNn hI₁ hI₂ hII₂ X hX ℜ F hF hn

/-- The implication (B) of Ch. I §2 (pp. 171–172) follows from Theorem B (`impl:B`; the Ch. I node
is a pointer to this proof). -/
@[blueprint "impl:B"
  (statement := /-- \textbf{The implication (B).} Given $(N,n)$ with $0\le n<N$:
    Th.\ $\mathrm I_2^{N',n'}$ for $n'<N'<N$, Th.\ $\mathrm I_2^{N,n''}$ for $n''<n$,
    Th.\ $\mathrm I_1^{N^*,n^*}$ for $n^*<N^*\le N$ and $n^*\le n$, and
    Th.\ $\mathrm{II}_2^{N'}$ for $N'<N$ together imply Th.\ $\mathrm I_2^{N,n}$. (Lean:
    \cref{def:I.2-implication-B}.) The proof is in Ch.~IV: Theorem~B (\cref{thm:IV.B}, p.~293). -/)
  (proof := /-- Theorem B (\cref{thm:IV.B}) has exactly these hypotheses, and its conclusion,
    for every non-singular irreducible $X$ of dimension $N$ and every
    $(\mathfrak R^{N,n}_{\mathrm I},U)$ on $X$, is the conclusion of Theorem
    $\mathrm I_2^{N,n}$ (\cref{thm:I.2-I2}). -/)
  (latexEnv := "corollary")]
theorem implicationB_fundamentalFamily [Hironaka.HironakaCitedResults.{u}] : fundamentalFamily.{u}.ImplicationB := by
  intro N n hNn hI₂' hI₂ hI₁ hII₂ X hX ℜ U hU hn
  exact exists_isPermissibleIOpen_resolvedEverywhere N n hNn hI₂' hI₂ hI₁ hII₂ X hX ℜ U hU hn

end AB

end

end Hironaka

/-- Paper name (Hironaka 1964) of `AB.exists_isPermissibleIClosed_inter_eq_empty`. -/
alias _root_.Hironaka.AB.theoremA := Hironaka.AB.exists_isPermissibleIClosed_inter_eq_empty
/-- Paper name (Hironaka 1964) of `AB.exists_isPermissibleIOpen_resolvedEverywhere`. -/
alias _root_.Hironaka.AB.theoremB := Hironaka.AB.exists_isPermissibleIOpen_resolvedEverywhere
