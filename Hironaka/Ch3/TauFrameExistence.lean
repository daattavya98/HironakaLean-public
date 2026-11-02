/-
Copyright (c) 2026 Daattavya Aggarwal, Minhyong Kim, Oisin Kim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daattavya Aggarwal, Minhyong Kim, Oisin Kim
-/
module

public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.MvPowerSeries.Rename
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Architect
public import Hironaka.Ch3.JStability
public import Hironaka.Compat.CoefficientField
public import Hironaka.Compat.FrameChain
public import Hironaka.Compat.WeierstrassSequence
public import Hironaka.Compat.ShiftSubstitution
public import Hironaka.Compat.TauOrderedFrame
public import Hironaka.Compat.TauZStandardBase
public import Hironaka.Compat.TauZSystem
public import Hironaka.Compat.TauZMonotone
public import Hironaka.Compat.TauZTransport
public import Hironaka.Compat.TauZStableElement
public import Hironaka.Statements

/-!
# Ch. III §10: Lemma 25 (pp. 269–273) and Theorem 9 (pp. 273–274)

> **Theorem 9.** *Let `R` be a complete regular local ring whose residue field has characteristic
> zero, and `J` an ideal in `R`. Then there exists a `J`-stable regular `τ`-frame of `R` for `J`
> and a `J`-stable standard base of `J`.*  (p. 273)

These two declarations are in this file, rather than in `Hironaka/Ch3/JStability.lean`
(which this file imports), so that their proofs may use `Hironaka/Compat/CoefficientField.lean`
(Cohen's coefficient field, a cited leaf), `Hironaka/Compat/ShiftSubstitution.lean` and
`Hironaka/Compat/TauZSystem.lean`, which are not upstream of `JStability`.
-/

@[expose] public section

open IsLocalRing

namespace Hironaka

universe u

/-! ### Lemma 25 (pp. 269–273) -/

section Lemma25

variable {R : Type u} [CommRing R] [IsRegularLocalRing R]

open Classical in
/-- Lemma 25, p. 269: "Let `R` be a complete regular local ring whose residue field has
characteristic zero, and `J` an ideal in `R`. Let `(z₁, …, z_r)` be a system of elements of `R`, and
`f` an element of `R` such that (i) `(z) = (z₁, …, z_r)` is `J`-stable and can be extended to a
regular system of parameters of `R`, and (ii) `f` is `(J, τ_{(z)})`-stable. If `τ_{(z)}(f) ≥ 1`,
then there exists an element `w` of `R` such that (1) `(z, w) = (z₁, …, z_r, w)` is `J`-stable and
can be extended to a regular system of parameters of `R`, (2) `τ_{(z,w)}(f) = τ_{(z)}(f) − 1`, and
(3) `f` is `(J, τ_{(z,w)})`-stable."

(Formalization notes: "complete" is `IsAdicComplete (maximalIdeal R) R`; `(z, w)` is
`Fin.snoc z w`; "`(J, τ_{(z)})`-stable" is `IsJTauZStable J z` of Definition 13 (printed there
`(J; τ_{(z)})`); the subtraction in (2) is in `ℕ`, where `τ_{(z)}(f) ≥ 1`.

**Transcription note.**  The Lean statement has the hypothesis `hz` and an injectivity conclusion:
`ExtendsToRSOP R (Finset.image …)` only sees the *set* of the members and `tauZ` only counts
entries, so without them, for `r ≥ 1`, the degenerate witness `w = z 0` would satisfy (1), (2), (3)
without any use of the hypotheses.  The paper's `z`, `w` are a *system* (distinct members, as
for every "system which can be extended to a regular system of parameters"); the hypothesis
`Function.Injective z` and the conclusion `Function.Injective (Fin.snoc z w)` are therefore part of the statement.) -/
@[blueprint "lem:III.25"
  (statement := /-- Let $R$ be a complete regular local ring whose residue field has
    characteristic zero, and $J$ an ideal in $R$. Let $(z_1,\dots,z_r)$ be a system of elements
    of $R$, and $f$ an element of $R$ such that (i) $(z)=(z_1,\dots,z_r)$ is $J$-stable
    (\cref{def:III.11}) and can be extended to a regular system of parameters of $R$, and (ii)
    $f$ is $(J,\tau_{(z)})$-stable (\cref{def:III.13}). If $\tau_{(z)}(f)\ge1$
    (\cref{def:III.10-star}), then there exists an element $w$ of $R$ such that (1)
    $(z,w)=(z_1,\dots,z_r,w)$ is $J$-stable and can be extended to a regular system of
    parameters of $R$, (2) $\tau_{(z,w)}(f)=\tau_{(z)}(f)-1$, and (3) $f$ is
    $(J,\tau_{(z,w)})$-stable. (Lemma 25, p.~269.)

    \textbf{Transcription note.} The system $(z_1,\dots,z_r)$ and the system
    $(z,w)$ consist of distinct elements (as always for ``a system which can be extended to a
    regular system of parameters''): the formal statement has the hypothesis that $z$ is
    injective and the conclusion that $(z,w)$ is injective. Without them the statement would see
    only the set of members and be satisfied, for $r\ge1$, by the degenerate witness $w=z_1$. -/)
  (proof := /-- Let us take a regular system of parameters $(z_1,\dots,z_r,x_1,\dots,x_s)$ of
    $R$ such that, if $t=\tau_{(z)}(f)$, $(x_1,\dots,x_t)$ is a regular system of
    $\tau_{(z)}$-parameters of $R$ for $f$ (\cref{def:III.10-star}). We have a subfield $k$ of
    $R$ such that $R=k\{z_1,\dots,z_r,x_1,\dots,x_s\}$ by the structure theorem of a complete
    regular local ring (equi-characteristic). Let $M$ be the maximal ideal of $R$ and
    $\nu=\nu_M(f)$. By the symbol $k$, we shall also denote the residue field $R/M$ which is
    canonically isomorphic to the coefficient field $k$ of $R$. The graded $k$-algebra
    $\operatorname{gr}_M(R)$ can be identified with the polynomial ring
    $k[Z_1,\dots,Z_r,X_1,\dots,X_s]$, where $Z_j$ (resp.\ $X_j$) denotes the initial form of
    $z_j$ (resp.\ $x_j$) in $\operatorname{gr}_M(R)$. Let $\varphi$ be the initial form of $f$
    in $\operatorname{gr}_M(R)$. Then $\varphi$ is a form of degree $\nu$ in
    $Z_1,\dots,Z_r,X_1,\dots,X_t$. Let $S=k\{x_1,\dots,x_s\}$ and $S_0=k\{x_2,\dots,x_s\}$
    ($=k$ if $s=1$). Let us write
    $$f=\textstyle\sum_{A\in\mathbb Z^r_0}h_Az^A\qquad\text{with }h_A\in S.$$
    Let $\varphi_A$ be the initial form of $h_A$ in $\operatorname{gr}_M(R)$ only for those $A$
    with $|A|+\nu_M(h_A)=\nu$. Then
    $$\varphi=\textstyle\sum_A\varphi_AZ^A\qquad\text{for }|A|+\nu_M(h_A)=\nu.$$
    Since $(x_1,\dots,x_t)$ is a regular system of $\tau_{(z)}$-parameters of $R$ for $f$, those
    $\varphi_A$ are forms in $X_1,\dots,X_t$, and there exists $\bar A\in\mathbb Z^r_0$ such that
    $|\bar A|+\nu_M(h_{\bar A})=\nu$ and that $\deg\varphi_{\bar A}>0$. Let
    $\deg\varphi_{\bar A}=\nu_M(h_{\bar A})=e$. By taking a suitable linear (non-singular)
    transformation of $(x_1,\dots,x_t)$ with coefficients in $k$, we may assume that
    $\varphi_{\bar A}$ has the term of $X_1^e$ with non-zero coefficient in $k$. Then by the
    Weierstrass preparation theorem, we can write
    $$h_{\bar A}=u(x_1^e+p'_1x_1^{e-1}+\dots+p'_e),$$
    where $u$ is a unit element of $S$ and $p'_j\in S_0$ for $1\le j\le e$. Since
    $\varphi_{\bar A}$ is a form in $X_1,\dots,X_t$, the class of $p'_1$ in
    $\operatorname{gr}^1_M(R)=M/M^2$ must be a form only in $X_2,\dots,X_t$, which may be zero.
    Therefore, we may replace $x_1$ by $x_1+e^{-1}p'_1$ without affecting the assumption that
    $(x_1,\dots,x_t)$ is a regular system of $\tau_{(z)}$-parameters of $R$ for $f$. Thus we may
    assume that
    $$h_{\bar A}=u(x_1^e+p_2x_1^{e-2}+\dots+p_e),$$
    where $p_j\in S_0$ for $2\le j\le e$. We shall prove that $w=x_1$ has the property required
    in the Lemma. The property (2) is clear from our selection of $w$.

    In order to prove (1) and (3), we reformulate the assertion in the following form:
    \emph{Let $R$ be a regular local ring whose residue field has characteristic zero, $J$ an
    ideal in $R$, $(S;z_1,\dots,z_r)$ a regular frame of $R$ and $(S_0;w)$ a regular frame of
    $S$. Let $f$ be an element of $R$. Suppose:
    (1) $(z_1,\dots,z_r)$ is $J$-stable, i.e., $(S;z_1,\dots,z_r)$ is $J$-stable,
    (2) $f$ is $(J,\tau_{(z)})$-stable,
    (3) $(w)$ can be extended to a regular system of $\tau_{(z)}$-parameters of $R$ for $f$,
    and
    (4) $f$ can be written in the form
    $$f=g+uz^{\bar A}(w^e+p_2w^{e-2}+\dots+p_e)$$
    where $g=\sum_{A\in\mathbb Z^r_0,\,A\ne\bar A}h_Az^A$ with $h_A\in S$, $u$ = a unit in $S$,
    $e=\nu_M(f)-|\bar A|>0$, and $p_j\in S_0$ for $2\le j\le e$.
    Let $P$ be any prime ideal in $R$ which is a permissible center for $J$, $R_1$ a monoidal
    transform of $R$ with center $P$ which is residually algebraic (necessarily, separable
    algebraic) over $R$, and $J_1$ the strict transform of $J$ in $R_1$. We shall prove that
    (a) $P\supseteq(z_1,\dots,z_r,w)R$,
    (b) $\nu_P(f)=\nu$ (throughout, $\nu$ denotes $\nu_M(f)$),
    (c) if $\nu^*(J_1)=\nu^*(J)$ and $\tau^*(J_1)=\tau^*(J)$, then there exists
    $y\in P\cap S_0$ such that $PR_1=(y)R_1$ and such that:
    (i) $\bar z_j=z_j/y$ ($1\le j\le r$) and $\bar w=w/y$ are non-units in $R_1$, hence,
    $(S;z_1,\dots,z_r)$ admits a frame transform $(S_1;\bar z_1,\dots,\bar z_r)$ in $R_1$, and
    $(S_0;w)$ admits a frame transform $(S_{01};\bar w)$ in $S_1$,
    (ii) if $\bar f=x^{-\nu}f$ [sic; read $y^{-\nu}f$], then $(\bar w)$ can be extended to a
    regular system of $\tau_{(\bar z)}$-parameters of $R_1$ for $\bar f$ and
    $\tau_{(\bar z,\bar w)}(\bar f)=\tau_{(z,w)}(f)$, and
    (iii) $\bar f$ can be written in the same form as $f$ in (4) where $(z,w)$ and $(S,S_0)$
    are replaced by $(\bar z,\bar w)$ and $(S_1,S_{01})$ respectively.}

    One can easily see that, if we prove these facts, then the proof of the lemma is completed.
    Now, (1) implies that $P\supseteq(z_1,\dots,z_r)R$. By (2), we have $\nu_P(f)=\nu$, i.e.,
    (b), and therefore by (4) we have
    $$w^e+p_2w^{e-2}+\dots+p_e\in Q^e,$$
    where $Q$ is the prime ideal $P\cap S$ in $S$. (Note that $S/Q$ is regular.) By Lemma~22
    (\cref{lem:III.22}), we then have $w\in Q\subseteq P$. Thus (a). Let
    $Q_0=Q\cap S_0=P\cap S_0$. We have $y\in Q_0$ such that $(y)R_1=PR_1$. In fact, if $y$ is
    any element of $P$ such that $(y)R_1=PR_1$, then we have $z_j/y\in M_1$ for all $j$, where
    $M_1$ denotes the maximal ideal of $R_1$. (See (1).) Moreover, by Lemma~24
    (\cref{lem:III.24}), (2) implies that $w/y\in M_1$. We thus see that $y\in Q_0$ exists and
    that all the $\bar z_j$ and $\bar w$ are non-units in $R_1$, i.e., (i) of (c). (iii) of (c)
    is clear, and we have only to show (ii) of (c). As in the proof of Lemma~22, the proof of
    (ii) of (c) can be reduced to the case in which the residue field $k$ of $S_0$ is
    algebraically closed, so that $R_1$ is residually rational over $R$. Let us choose a
    minimal base $(y_1,\dots,y_i)$ of $Q_0$ in such a way that $y=y_i$ and
    $\bar y_j=y_j/y\in M_1$ for $1\le j\le i-1$. Lemma~24 shows that, if
    $\tau=\tau_{(z)}(f)-1$ ($=\tau_{(z,w)}(f)$), there exist $\tau$ independent linear
    combinations of $y_1,\dots,y_{i-1}$ with coefficients in $S_0$ which form a regular system
    of $\tau_{(z,w)}$-parameters of $R$ for $f$. Therefore, we may assume that
    $(w,y_1,\dots,y_\tau)$ is a regular system of $\tau_{(z)}$-parameters of $R$ for $f$
    ($\tau\le i-1$). Let $b=i-1$. Let us choose a regular system of parameters
    $(y_1,\dots,y_b,y,x_1,\dots,x_a)$ of $S_0$. Then
    $(z_1,\dots,z_r,w,y_1,\dots,y_b,y,x_1,\dots,x_a)$ is a regular system of parameters of
    $R$, and $(\bar z_1,\dots,\bar z_r,\bar w,\bar y_1,\dots,\bar y_b,y,x_1,\dots,x_a)$ is a
    regular system of parameters of $R_1$. Then
    $$\operatorname{gr}_M(R)=k[Z_1,\dots,Z_r,W,Y_1,\dots,Y_b,Y,X_1,\dots,X_a]$$
    where $Z_j$ (resp.\ $W$, resp.\ $Y_j$, resp.\ $Y$, resp.\ $X_j$) denotes the initial form of
    $z_j$ (resp.\ $w$, resp.\ $y_j$, resp.\ $y$, resp.\ $x_j$) in $\operatorname{gr}_M(R)$, and
    $$\operatorname{gr}_{M_1}(R_1)=k[\bar Z_1,\dots,\bar Z_r,\bar W,\bar Y_1,\dots,\bar Y_b,Y,
      X_1,\dots,X_a],$$
    where $\bar Z_j$ (resp.\ $\bar W$, resp.\ $\bar Y_j$, resp.\ $Y$, resp.\ $X_j$) denotes the
    initial form of $\bar z_j$ (resp.\ $\bar w$, resp.\ $\bar y_j$, resp.\ $y$, resp.\ $x_j$) in
    $\operatorname{gr}_{M_1}(R_1)$. Let $\varphi$ (resp.\ $\bar\varphi$) denote the initial form
    of $f$ (resp.\ $\bar f$) in $\operatorname{gr}_M(R)$ (resp.\ $\operatorname{gr}_{M_1}(R_1)$).
    Then $\deg\varphi=\deg\bar\varphi=\nu$, $\varphi$ is a form only in
    $Z_1,\dots,Z_r,W,Y_1,\dots,Y_\tau$, and
    $$\bar\varphi=\varphi(\bar Z_1,\dots,\bar Z_r,\bar W,\bar Y_1,\dots,\bar Y_\tau)
      +\bar\varphi^*$$
    with $\bar\varphi^*\in(Y,X_1,\dots,X_a)\operatorname{gr}_{M_1}(R_1)$. By the assumption (2),
    we can find a system of linear forms $(L,L_1,\dots,L_\tau)$ in $Y,X_1,\dots,X_a$ with
    coefficients in $k$ such that
    $$\bar\varphi=\varphi(\bar Z_1,\dots,\bar Z_r,\bar W+L,\bar Y_1+L_1,\dots,
      \bar Y_\tau+L_\tau).$$
    We can find linear combinations $v_1,\dots,v_\tau$ of $y,x_1,\dots,x_a$ with coefficients in
    $S_0$ such that $L_j$ is the initial form of $v_j$ in $\operatorname{gr}_M(R)$ (hence, in
    $\operatorname{gr}_{M_1}(R_1)$) for $1\le j\le\tau$. We may replace $y_j$ by $y_j+v_jy$ for
    $1\le j\le\tau$ without affecting any of the assumptions on $(y_1,\dots,y_b)$ in the above
    argument, so that we may assume that $L_1=\dots=L_\tau=0$. We then have
    $$\bar\varphi=\varphi(\bar Z_1,\dots,\bar Z_r,\bar W+L,\bar Y_1,\dots,\bar Y_\tau).$$
    On the other hand, we can write
    $$\bar f=\bar g+u\bar z^{\bar A}(\bar w^e+\bar p_2\bar w^{e-2}+\dots\ \bar p_e)$$
    [sic; a $+$ is missing before $\bar p_e$] where
    $\bar g=\sum_{A\in\mathbb Z^r_0,\,A\ne\bar A}\bar h_A\bar z^A$ with
    $\bar h_A=h_Ay^{-(\nu-|A|)}\in S_1$, $u$ = a unit in $S_1$, $e=\nu-|\bar A|$, and
    $\bar p_j=y^{-j}p_j\in S_{01}$ ($2\le j\le e$). Hence $\bar\varphi$ is of the form
    $$\bar\varphi=\bar\psi+c\bar Z^{\bar A}(\bar W^e+\bar\lambda_2\bar W^{e-2}+\dots
      +\bar\lambda_e),$$
    where $\bar\psi=\sum_{A\ne\bar A}\bar\delta_A\bar Z^A$ with
    $\bar\delta_A\in k[\bar W,\bar Y_1,\dots,\bar Y_b,\bar Y,\bar X_1,\dots,\bar X_a]$, $c\ne0$
    (a constant in $k$), and $\bar\lambda_j\in k[\bar Y_1,\dots,\bar Y_b,\bar Y,\bar X_1,\dots,
    \bar X_a]$. On the other hand, $\varphi$ is of the form
    $$\varphi=\psi+cZ^{\bar A}(W^e+\lambda_2W^{e-2}+\dots+\lambda_e)$$
    where $\psi=\sum_{A\ne\bar A}\delta_AZ^A$ with
    $\delta_A\in k[W,Y_1,\dots,Y_b,Y,X_1,\dots,X_a]$, $c$ = the same non-zero constant in $k$ as
    above, and $\lambda_j\in k[Y_1,\dots,Y_b,Y,X_1,\dots,X_a]$. Therefore the equality
    $$\bar\varphi=\varphi(\bar Z_1,\dots,\bar Z_r,\bar W+L,\bar Y_1,\dots,\bar Y_\tau)$$
    implies that
    $$\bar W^e+\bar\lambda_2\bar W^{e-2}+\dots+\bar\lambda_e=(\bar W+L)^e
      +\lambda_2(\bar W+L)^{e-2}+\dots+\lambda_e.$$
    It follows that $eL=0$, hence $L=0$. Thus
    $$\bar\varphi=\varphi(\bar Z_1,\dots,\bar Z_r,\bar W,\bar Y_1,\dots,\bar Y_\tau).$$
    It follows that $(\bar w)$ can be extended to a regular system of $\tau_{(\bar z)}$-parameters
    of $R_1$ for $\bar f$, and that $\tau_{(\bar z,\bar w)}(\bar f)=\tau_{(z,w)}(f)$ ($=\tau$).
    \qed -/)
  (latexEnv := "lemma")]
theorem exists_isJTauZStable_snoc [Hironaka.HironakaCitedResults.{u}] [IsAdicComplete (maximalIdeal R) R]
    [CharZero (ResidueField R)] (J : Ideal R) {r : ℕ} (z : Fin r → R) (hz : Function.Injective z)
    (f : R) (h_i : IsJStableSystem J z ∧ ExtendsToRSOP R (Finset.image z Finset.univ))
    (h_ii : IsJTauZStable J z f) (hτ : 1 ≤ tauZ R z (fun _ : Fin 1 => f)) :
    ∃ w : R, Function.Injective (Fin.snoc z w : Fin (r + 1) → R) ∧
      (IsJStableSystem J (Fin.snoc z w : Fin (r + 1) → R) ∧
        ExtendsToRSOP R (Finset.image (Fin.snoc z w : Fin (r + 1) → R) Finset.univ)) ∧
      tauZ R (Fin.snoc z w : Fin (r + 1) → R) (fun _ : Fin 1 => f) =
        tauZ R z (fun _ : Fin 1 => f) - 1 ∧
      IsJTauZStable J (Fin.snoc z w : Fin (r + 1) → R) f :=
  exists_isJTauZStable_snoc_aux J z hz f h_i h_ii hτ

end Lemma25

/-! ### The induction of Theorem 9 (pp. 273–274) -/

section TauFrameStage

variable {R : Type u} [CommRing R] [IsRegularLocalRing R]

/-- A standard base is at least as long as any other (`ν^{(m+1)}(J) = ∞`, `ν^{(j)}(J) < ∞`
for `j ≤ m'`; Lemma 1). -/
theorem IsStandardBase.length_le {J : Ideal R} {m m' : ℕ} {g : Fin m → R} {g' : Fin m' → R}
    (hg : IsStandardBase R J g) (hg' : IsStandardBase R J g') : m' ≤ m := by
  obtain ⟨-, htop⟩ := nuI_eq_of_hasLemma1Properties R J _ hg.2
  obtain ⟨⟨d', -, hnu'⟩, -⟩ := nuI_eq_of_hasLemma1Properties R J _ hg'.2
  by_contra h
  push Not at h
  have h1 := htop ⟨m + 1, Nat.succ_pos _⟩ (Nat.lt_succ_self m)
  have h2 := hnu' ⟨m, h⟩
  exact ENat.top_ne_natCast (d' ⟨m, h⟩) (h1.symm.trans h2)

/-- All standard bases of `J` have the same length. -/
theorem IsStandardBase.length_eq {J : Ideal R} {m m' : ℕ} {g : Fin m → R} {g' : Fin m' → R}
    (hg : IsStandardBase R J g) (hg' : IsStandardBase R J g') : m = m' :=
  le_antisymm (hg'.length_le hg) (hg.length_le hg')


/-- A standard base which extends a system of the same length is that system. -/
theorem ExtendsToStandardBase.isStandardBase_of_length_eq {J : Ideal R} {i : ℕ} {f : Fin i → R}
    (h : ExtendsToStandardBase J f) {m : ℕ} {g : Fin m → R} (hg : IsStandardBase R J g)
    (hmi : m ≤ i) : i = m ∧ IsStandardBase R J f := by
  obtain ⟨m₁, g₁, him, hg₁, hfg⟩ := h
  have hm : m₁ = m := hg₁.length_eq hg
  subst hm
  have hi : i = m₁ := le_antisymm him hmi
  subst hi
  refine ⟨rfl, ?_⟩
  have : f = g₁ := funext fun j => (hfg j).symm.trans (by simp)
  rwa [this]

/-- The last index of a non-empty system. -/
def lastIdx {i : ℕ} (h : 0 < i) : Fin i := ⟨i - 1, Nat.sub_one_lt h.ne'⟩

open Classical in
/-- The data `(f_1, …, f_i)`, `(z_1, …, z_r)` of the induction in the proof of Theorem 9
(p. 273): conditions (1)–(6) of the paper, with "regular system of `τ`-parameters" read, as the
paper does, through the spaces `T` of Definition 10* (`tauZSubmodule`) and `T_a` of
Definition 7 (`tauSubmodule`); the field `filtration` records, in addition, that `(z)` is an
initial segment of an *ordered* regular system of `τ`-parameters for `J` as soon as a level
`μ^{(b)}(J)` is exhausted (Definition 12 needs the ordered notion of Definition 7). -/
structure TauFrameStage (J : Ideal R) {i r : ℕ} (f : Fin i → R) (z : Fin r → R) : Prop where
  /-- (1) `(f₁, …, f_i)` is extendable to a standard base of `J`. -/
  extends_std : ExtendsToStandardBase J f
  /-- The members of `(z)` are distinct. -/
  injective : Function.Injective z
  /-- `(z)` can be extended to a regular system of parameters of `R`. -/
  extendsToRSOP : ExtendsToRSOP R (Finset.image z Finset.univ)
  /-- (2) `(z)` can be extended to a regular system of `τ`-parameters of `R` for `(f₁, …, f_i)`. -/
  mem_tauZSubmodule : ∀ j, frameForm z j ∈ tauZSubmodule R f
  /-- (3) `τ_{(z)}(f_j) = 0` for `1 ≤ j ≤ i - 1`. -/
  tauZ_eq_zero : ∀ j : Fin i, (j : ℕ) + 1 < i → tauZ R z (fun _ : Fin 1 => f j) = 0
  /-- (3) `τ(f₁, …, f_i) = r + τ_{(z)}(f_i)`. -/
  tauZ_eq : ∀ h : 0 < i, tauZ R (![] : Fin 0 → R) f =
    r + tauZ R z (fun _ : Fin 1 => f (lastIdx h))
  /-- (4) the extension of `(z)` by a regular system of `τ_{(z)}`-parameters for `(f_i)` is
  extendable to a regular system of `τ`-parameters of `R` for `J`. -/
  star_le : ∀ h : 0 < i, tauZSubmoduleStar R z (fun _ : Fin 1 => f (lastIdx h)) ≤
    tauSubmodule R J (t R J)
  /-- (5) `(z)` is `J`-stable. -/
  isJStableSystem : IsJStableSystem J z
  /-- (6) `f_j` is `(J, τ_{(z)})`-stable for all `j`. -/
  isJTauZStable : ∀ j, IsJTauZStable J z (f j)
  /-- The first `τ^{(b)}(J)` members of `(z)` span `T_b` once the level `μ^{(b)}(J)` is
  exhausted. -/
  filtration : ∀ b, 1 ≤ b → b ≤ t R J →
    (∃ j : Fin i, (mu R J b : ℕ∞) < Ideal.ordElem (maximalIdeal R) (f j)) →
      ∃ h : tau R J b ≤ r, Submodule.span (R ⧸ maximalIdeal R)
        (Set.range fun l : Fin (tau R J b) => frameForm z (Fin.castLE h l)) = tauSubmodule R J b
  /-- There is no `(z)` before the first element: `r = 0` if `i = 0`. -/
  r_eq_zero : i = 0 → r = 0
  /-- Once the level `μ^{(b)}(J)` is exhausted, the `f_j` with `ν_M(f_j) ≤ μ^{(b)}(J)` are
  `(J, τ_{(z)'})`-stable with `τ_{(z)'}(f_j) = 0` for the initial segment
  `(z)' = (z_1, …, z_{τ^{(b)}(J)})`.  (The paper's induction needs this for Definition 12 of the
  final `τ`-frame: the transforms of `(z)` must again be regular systems of `τ`-parameters, which
  are ordered.) -/
  prefix_stable : ∀ b, 1 ≤ b → b ≤ t R J →
    (∃ j : Fin i, (mu R J b : ℕ∞) < Ideal.ordElem (maximalIdeal R) (f j)) →
      ∀ (h : tau R J b ≤ r) (j : Fin i),
        Ideal.ordElem (maximalIdeal R) (f j) ≤ (mu R J b : ℕ∞) →
          IsJTauZStable J (fun l : Fin (tau R J b) => z (Fin.castLE h l)) (f j) ∧
            tauZ R (fun l : Fin (tau R J b) => z (Fin.castLE h l)) (fun _ : Fin 1 => f j) = 0

/-- The start of the induction: `i = r = 0`, all of (1)–(6) hold trivially. -/
theorem TauFrameStage.zero (J : Ideal R) : TauFrameStage J (![] : Fin 0 → R) (![] : Fin 0 → R) where
  extends_std := by
    obtain ⟨m, g, hg⟩ := exists_isStandardBase J
    exact ⟨m, g, Nat.zero_le _, hg, fun j => j.elim0⟩
  injective := fun a b _ => Subsingleton.elim a b
  extendsToRSOP := by
    obtain ⟨-, s, hs⟩ := (isRegularLocalRing_iff_exists_rsop R).mp inferInstance
    exact ⟨s, fun x hx => by simp at hx, hs⟩
  mem_tauZSubmodule := fun j => j.elim0
  tauZ_eq_zero := fun j => j.elim0
  tauZ_eq := fun h => absurd h (lt_irrefl 0)
  star_le := fun h => absurd h (lt_irrefl 0)
  isJStableSystem := fun j => j.elim0
  isJTauZStable := fun j => j.elim0
  filtration := fun _ _ _ h => by obtain ⟨j, -⟩ := h; exact j.elim0
  r_eq_zero := fun _ => rfl
  prefix_stable := fun _ _ _ hex => by obtain ⟨j, -⟩ := hex; exact j.elim0

/-- `τ_{(z)}(f_i)`, and `0` if `i = 0`: the integer which decreases in step (A). -/
noncomputable def lastTauZ {i r : ℕ} (f : Fin i → R) (z : Fin r → R) : ℕ :=
  if h : 0 < i then tauZ R z (fun _ : Fin 1 => f (lastIdx h)) else 0

section Stable

/-- A `(J; τ_{(z)})`-stable element is `J`-stable: the strict transforms `z_j^{(ᾱ)}` that
Definition 13 asks for exist along every sequence (the strict transform of a principal ideal is
principal), and its conclusions include those of Definition 11. -/
theorem IsJTauZStable.isJStable {J : Ideal R} {r : ℕ} {z : Fin r → R} {f : R}
    (h : IsJTauZStable J z f) : IsJStable J f := by
  intro Sq e he hperm hsep α hν ht hτ fα hfα
  choose zα hzα using fun j =>
    MonoidalSequence.exists_strictAlong_span_singleton_eq_aux Sq e hperm.hasRegularCenters
      (z j) α
  have := h.2.2 Sq e he hperm hsep α hν ht hτ zα (fun j => (hzα j).symm) fα hfα
  exact ⟨this.1, this.2.1⟩

/-- The members of a stage are `J`-stable elements. -/
theorem TauFrameStage.isJStableSystem_f {J : Ideal R} {i r : ℕ} {f : Fin i → R} {z : Fin r → R}
    (hS : TauFrameStage J f z) : IsJStableSystem J f :=
  fun j => (hS.isJTauZStable j).isJStable

open Classical in
/-- `(J; τ_{(z)})`-stability passes from `(z)` to `(z, w)` for an element `f` with
`τ_{(z)}(f) = 0`: `T*` is then spanned by the `Z_j` (and the `W`), at every stage of the
sequences, as long as `(z, w)` is `J`-stable and independent modulo `M²`
(Definition 13's parenthetical note, `extendsToRSOP_strictTransform_of_isJStableSystem`). -/
theorem IsJTauZStable.snoc_of_tauZ_eq_zero [Hironaka.HironakaCitedResults.{u}] {J : Ideal R} {r : ℕ} {z : Fin r → R} {w f : R}
    (hinj : Function.Injective (Fin.snoc z w : Fin (r + 1) → R))
    (hz : ExtendsToRSOP R (Finset.image (Fin.snoc z w : Fin (r + 1) → R) Finset.univ))
    (hzs : IsJStableSystem J (Fin.snoc z w : Fin (r + 1) → R))
    (h : IsJTauZStable J z f) (h0 : tauZ R z (fun _ : Fin 1 => f) = 0) :
    IsJTauZStable J (Fin.snoc z w : Fin (r + 1) → R) f := by
  refine ⟨hz, hzs, ?_⟩
  intro Sq e he hperm hsep αb hν ht hτ zα hzα fα hfα
  obtain ⟨h1, h2, h3⟩ := h.2.2 Sq e he hperm hsep αb hν ht hτ (Fin.init zα)
    (fun j => by have := hzα j.castSucc; rwa [Fin.snoc_castSucc] at this) fα hfα
  refine ⟨h1, h2, ?_⟩
  obtain ⟨hinjα, hzα'⟩ := extendsToRSOP_strictTransform_of_isJStableSystem J _ hinj hz hzs Sq e
    he hperm hsep αb hν ht hτ zα hzα
  rw [tauZ_snoc_eq_zero_of_tauZ_eq_zero hinj hz _ h0]
  have hz0 : tauZ (Sq.ring αb) (Fin.init zα) (fun _ : Fin 1 => fα) = 0 := h3.trans h0
  have := tauZ_snoc_eq_zero_of_tauZ_eq_zero (z := Fin.init zα) (w := zα (Fin.last r))
    (by rwa [Fin.snoc_init_self]) (by rwa [Fin.snoc_init_self]) _ hz0
  rwa [Fin.snoc_init_self] at this

end Stable

section StageSteps

variable {J : Ideal R} {i r : ℕ} {f : Fin i → R} {z : Fin r → R}

open Classical in
/-- In a stage, `T*` of the last element `f_i` for `(z)` is the space `T` of the whole system
`(f_1, …, f_i)`: it contains it (the initial forms of the `f_j` lie in `k[T*]`, as
`T*_{(z)}(f_j) = ⟨Z⟩` for `j < i`) and has the same rank (condition (3) of the paper's
induction). -/
theorem TauFrameStage.tauZSubmoduleStar_last_eq (hS : TauFrameStage J f z) (hi : 0 < i) :
    tauZSubmoduleStar R z (fun _ : Fin 1 => f (lastIdx hi)) = tauZSubmodule R f := by
  obtain ⟨-, hord⟩ := linearIndependent_frameForm hS.injective hS.extendsToRSOP
  have hle : tauZSubmodule R f ≤ tauZSubmoduleStar R z (fun _ : Fin 1 => f (lastIdx hi)) := by
    refine tauZSubmodule_le_of_forall_mem_adjoin f _
      (tauZSubmoduleStar_le_homogeneous_one hord) fun j => ?_
    by_cases hj : (j : ℕ) + 1 < i
    · have h0 := tauZSubmoduleStar_eq_span_of_tauZ_eq_zero hS.injective hS.extendsToRSOP
        (fun _ : Fin 1 => f j) (hS.tauZ_eq_zero j hj)
      have h1 := initialForm_mem_adjoin_tauZSubmoduleStar z (f j)
      rw [h0] at h1
      exact Algebra.adjoin_mono (SetLike.coe_subset_coe.mpr le_sup_right) h1
    · have hjl : j = lastIdx hi := Fin.ext (by simp only [lastIdx]; omega)
      rw [hjl]
      exact initialForm_mem_adjoin_tauZSubmoduleStar z _
  let _ : Field (R ⧸ maximalIdeal R) := Ideal.Quotient.field _
  have : FiniteDimensional (R ⧸ maximalIdeal R)
      (tauZSubmoduleStar R z (fun _ : Fin 1 => f (lastIdx hi))) :=
    finite_tauZSubmoduleStar hord _
  refine (Submodule.eq_of_le_of_finrank_eq hle ?_).symm
  rw [← tauZ_empty, hS.tauZ_eq hi, finrank_tauZSubmoduleStar_eq hS.injective hS.extendsToRSOP]
  omega

open Classical in
/-- At the end of the induction `r = τ^{(t)}(J)`: `τ(f_1, …, f_i) = r + τ_{(z)}(f_i) = r` is the
rank of the `T` of the standard base `(f_1, …, f_i)`, which is `T_t` (Definition 7). -/
theorem TauFrameStage.tau_eq_r (hS : TauFrameStage J f z) (hstd : IsStandardBase R J f)
    (hτ : ∀ h : 0 < i, tauZ R z (fun _ : Fin 1 => f (lastIdx h)) = 0) :
    tau R J (t R J) = r := by
  rcases Nat.eq_zero_or_pos i with hi | hi
  · subst hi
    rw [hS.r_eq_zero rfl, t_eq_zero_of_isStandardBase_nil f hstd,
      tau_eq_zero_of_isStandardBase_nil f hstd]
  · have ht1 := one_le_t_of_isStandardBase hstd hi
    obtain ⟨m', hm', -, hhigh, -, hfin⟩ :=
      exists_prefix_tauZSubmodule_eq_tauSubmodule J f hstd ht1 le_rfl
    have hm : m' = i := by
      by_contra hne
      have hlt : m' < i := lt_of_le_of_ne hm' hne
      exact absurd (ordElem_le_mu_t J hstd ⟨m', hlt⟩) (not_le.mpr (hhigh ⟨m', hlt⟩ le_rfl))
    subst hm
    have h1 := hS.tauZ_eq hi
    rw [hτ hi, tauZ_empty] at h1
    rw [← hfin]
    exact h1.trans (add_zero r)

open Classical in
/-- At the end of the induction, for every level `b ≤ t(J)` and every `f_j` with
`ν_M(f_j) ≤ μ^{(b)}(J)`, `f_j` is `(J, τ_{(z)'})`-stable with `τ_{(z)'}(f_j) = 0` for the initial
segment `(z)' = (z_1, …, z_{τ^{(b)}(J)})` (the trigger of `prefix_stable` holds for `b < t`, and
`(z)' = (z)` for `b = t`). -/
theorem TauFrameStage.prefix_stable_all (hS : TauFrameStage J f z) (hstd : IsStandardBase R J f)
    (hτ : ∀ h : 0 < i, tauZ R z (fun _ : Fin 1 => f (lastIdx h)) = 0) {b : ℕ} (hb : 1 ≤ b)
    (hbt : b ≤ t R J) (h : tau R J b ≤ r) (j : Fin i)
    (hj : Ideal.ordElem (maximalIdeal R) (f j) ≤ (mu R J b : ℕ∞)) :
    IsJTauZStable J (fun l : Fin (tau R J b) => z (Fin.castLE h l)) (f j) ∧
      tauZ R (fun l : Fin (tau R J b) => z (Fin.castLE h l)) (fun _ : Fin 1 => f j) = 0 := by
  have hi : 0 < i := Nat.pos_of_ne_zero fun h0 => by subst h0; exact j.elim0
  rcases lt_or_eq_of_le hbt with hlt | heq
  · obtain ⟨j', hj'⟩ := exists_ordElem_eq_mu_t J hstd (one_le_t_of_isStandardBase hstd hi)
    refine hS.prefix_stable b hb hbt ⟨j', ?_⟩ h j hj
    rw [hj']
    exact_mod_cast mu_lt_mu_t J hb hlt
  · subst heq
    have hrt := hS.tau_eq_r hstd hτ
    have hz0 : tauZ R z (fun _ : Fin 1 => f j) = 0 := by
      by_cases hj1 : (j : ℕ) + 1 < i
      · exact hS.tauZ_eq_zero j hj1
      · have hjl : j = lastIdx hi := Fin.ext (by simp only [lastIdx]; omega)
        rw [hjl]
        exact hτ hi
    have key : ∀ (n : ℕ) (hn : n = r) (h : n ≤ r),
        IsJTauZStable J (fun l : Fin n => z (Fin.castLE h l)) (f j) ∧
          tauZ R (fun l : Fin n => z (Fin.castLE h l)) (fun _ : Fin 1 => f j) = 0 := by
      intro n hn h
      subst hn
      exact ⟨hS.isJTauZStable j, hz0⟩
    exact key _ hrt h

end StageSteps

section Exhausted

variable {J : Ideal R} {i : ℕ} {f : Fin i → R} {g : R}

/-- **The level `b` is exhausted by `(f₁, …, f_i)`** (the case of the field `filtration` where
the trigger comes from the new element `g` only): if all `f_j` have order `≤ μ^{(b)}(J)` and
`ν_M(g) > μ^{(b)}(J)`, the members `f_j` are exactly those of the standard base of order
`≤ μ^{(b)}(J)`, so `T_b(J) = T(f₁, …, f_i) = ⟨Z⟩` and `τ^{(b)}(J) = r`. -/
theorem tauSubmodule_eq_span_of_exhausted (F : RegularFrame R) (hS : TauFrameStage J f F.z)
    (hτ : ∀ h : 0 < i, tauZ R F.z (fun _ : Fin 1 => f (lastIdx h)) = 0)
    (hext : ExtendsToStandardBase J (Fin.snoc f g : Fin (i + 1) → R)) {b : ℕ} (hb1 : 1 ≤ b)
    (hbt : b ≤ t R J) (hB : ∀ j : Fin i, Ideal.ordElem (maximalIdeal R) (f j) ≤ (mu R J b : ℕ∞))
    (hg : (mu R J b : ℕ∞) < Ideal.ordElem (maximalIdeal R) g) :
    tauSubmodule R J b = Submodule.span (R ⧸ maximalIdeal R) (Set.range (frameForm F.z)) ∧
      tau R J b = F.r := by
  classical
  obtain ⟨m, σ, him, hσ, hσf⟩ := hext
  obtain ⟨m', hm', hlow, hhigh, heq, hfin⟩ :=
    exists_prefix_tauZSubmodule_eq_tauSubmodule J σ hσ hb1 hbt
  have hσi : σ ⟨i, by omega⟩ = g := by
    have := hσf (Fin.last i)
    rw [Fin.snoc_last] at this
    exact this
  have hσj : ∀ j : Fin i, σ ⟨j, by omega⟩ = f j := fun j => by
    have := hσf j.castSucc
    rw [Fin.snoc_castSucc] at this
    exact this
  have hm'i : m' = i := by
    apply le_antisymm
    · by_contra hlt
      push Not at hlt
      have := hlow ⟨i, by omega⟩ hlt
      rw [hσi] at this
      exact absurd this (not_le.mpr hg)
    · by_contra hlt
      push Not at hlt
      have := hhigh ⟨m', by omega⟩ le_rfl
      rw [hσj ⟨m', hlt⟩] at this
      exact absurd (hB ⟨m', hlt⟩) (not_le.mpr this)
  subst hm'i
  have hfun : (fun j : Fin m' => σ (Fin.castLE hm' j)) = f := funext fun j => hσj j
  rw [hfun] at heq
  have hTf : tauZSubmodule R f = Submodule.span (R ⧸ maximalIdeal R)
      (Set.range (frameForm F.z)) := by
    rcases Nat.eq_zero_or_pos m' with h0 | hi
    · subst h0
      have hr0 : F.r = 0 := hS.r_eq_zero rfl
      rw [tauZSubmodule_nil f]
      have : Set.range (frameForm F.z) = ∅ := by
        refine Set.range_eq_empty_iff.mpr ?_
        rw [hr0]
        infer_instance
      rw [this, Submodule.span_empty]
    · rw [← hS.tauZSubmoduleStar_last_eq hi]
      exact tauZSubmoduleStar_eq_span_of_tauZ_eq_zero hS.injective hS.extendsToRSOP _ (hτ hi)
  have hTb := heq.symm.trans hTf
  refine ⟨hTb, ?_⟩
  obtain ⟨hli, -⟩ := linearIndependent_frameForm hS.injective hS.extendsToRSOP
  rw [← (tauSubmodule_spec R J b hb1 hbt).2.1, hTb, finrank_span_eq_card hli, Fintype.card_fin]

end Exhausted

section Assembly

variable {J : Ideal R} {i : ℕ} {f : Fin i → R} {g : R}

/-- **The stage with `f_{i+1}` adjoined** (claim (B), p. 274): from the choice of
`f_{i+1} = g` (extendable to a standard base, normalized by `(f₁, …, f_i)`) and its
`(J, τ_{(z)})`-stability, the conditions (1)–(6) hold for `(f₁, …, f_{i+1})` and the same `(z)`,
as do the added conditions `filtration`, `r_eq_zero` and `prefix_stable`. -/
theorem TauFrameStage.snoc_of_isJTauZStable (F : RegularFrame R) (hS : TauFrameStage J f F.z)
    (hτ : ∀ h : 0 < i, tauZ R F.z (fun _ : Fin 1 => f (lastIdx h)) = 0)
    (hext : ExtendsToStandardBase J (Fin.snoc f g : Fin (i + 1) → R))
    (hnorm : F.IsNormalizedBy f g) (hstab : IsJTauZStable J F.z g) :
    TauFrameStage J (Fin.snoc f g : Fin (i + 1) → R) F.z := by
  classical
  have hτf : ∀ j : Fin i, tauZ R F.z (fun _ : Fin 1 => f j) = 0 := by
    intro j
    by_cases hj : (j : ℕ) + 1 < i
    · exact hS.tauZ_eq_zero j hj
    · have hi : 0 < i := by have := j.2; omega
      have : j = lastIdx hi := Fin.ext (by simp only [lastIdx]; have := j.2; omega)
      rw [this]
      exact hτ hi
  obtain ⟨d, d₀, hd, hdle, hg⟩ := exists_degrees_snoc hext
  have hmono := tauZSubmodule_le_snoc f g hd hdle hg
  have hTeq := tauZSubmodule_snoc_eq F hτf hnorm hext (fun l => hS.mem_tauZSubmodule l)
  have hlast : ∀ h : 0 < i + 1, lastIdx h = Fin.last i := fun h =>
    Fin.ext (by simp [lastIdx])
  have hmo := ordElem_le_ordElem_last hext
  exact
  { extends_std := hext
    injective := hS.injective
    extendsToRSOP := hS.extendsToRSOP
    mem_tauZSubmodule := fun l => hmono (hS.mem_tauZSubmodule l)
    tauZ_eq_zero := by
      intro j hj
      obtain ⟨j', rfl⟩ : ∃ j' : Fin i, j = j'.castSucc := ⟨⟨j, by omega⟩, Fin.ext rfl⟩
      simp only [Fin.snoc_castSucc]
      exact hτf j'
    tauZ_eq := by
      intro h
      rw [hlast h, Fin.snoc_last, tauZ_empty, hTeq,
        finrank_tauZSubmoduleStar_eq hS.injective hS.extendsToRSOP]
      omega
    star_le := by
      intro h
      rw [hlast h, Fin.snoc_last, ← hTeq]
      exact tauZSubmodule_snoc_le_tauSubmodule_t hext
    isJStableSystem := hS.isJStableSystem
    isJTauZStable := by
      intro j
      refine Fin.lastCases ?_ (fun j' => ?_) j
      · simpa using hstab
      · simpa using hS.isJTauZStable j'
    filtration := by
      intro b hb1 hbt ⟨jt, hjt⟩
      by_cases hA : ∃ j' : Fin i, (mu R J b : ℕ∞) < Ideal.ordElem (maximalIdeal R) (f j')
      · obtain ⟨j', hj'⟩ := hA
        exact hS.filtration b hb1 hbt ⟨j', hj'⟩
      · push Not at hA
        have hgb : (mu R J b : ℕ∞) < Ideal.ordElem (maximalIdeal R) g := by
          revert hjt
          refine Fin.lastCases ?_ (fun j' => ?_) jt
          · simp
          · intro hjt
            simp only [Fin.snoc_castSucc] at hjt
            exact absurd hjt (not_lt.mpr (hA j'))
        obtain ⟨hTb, hτb⟩ := tauSubmodule_eq_span_of_exhausted F hS hτ hext hb1 hbt hA hgb
        refine ⟨hτb.le, ?_⟩
        have key : ∀ (n : ℕ) (hn : n = F.r) (h : n ≤ F.r),
            Submodule.span (R ⧸ maximalIdeal R)
              (Set.range fun l : Fin n => frameForm F.z (Fin.castLE h l)) =
            Submodule.span (R ⧸ maximalIdeal R) (Set.range (frameForm F.z)) := by
          intro n hn h
          subst hn
          rfl
        exact (key _ hτb hτb.le).trans hTb.symm
    r_eq_zero := fun h => absurd h (Nat.succ_ne_zero i)
    prefix_stable := by
      intro b hb1 hbt ⟨jt, hjt⟩ h j hj
      by_cases hA : ∃ j' : Fin i, (mu R J b : ℕ∞) < Ideal.ordElem (maximalIdeal R) (f j')
      · obtain ⟨j'', hj''⟩ := hA
        by_cases hjl : j = Fin.last i
        · subst hjl
          rw [Fin.snoc_last] at hj
          exact absurd (hj''.trans_le (hmo j'')) (not_lt.mpr hj)
        · obtain ⟨j', rfl⟩ := Fin.exists_castSucc_eq.mpr hjl
          simp only [Fin.snoc_castSucc] at hj ⊢
          exact hS.prefix_stable b hb1 hbt ⟨j'', hj''⟩ h j' hj
      · push Not at hA
        have hgb : (mu R J b : ℕ∞) < Ideal.ordElem (maximalIdeal R) g := by
          revert hjt
          refine Fin.lastCases ?_ (fun j' => ?_) jt
          · simp
          · intro hjt
            simp only [Fin.snoc_castSucc] at hjt
            exact absurd hjt (not_lt.mpr (hA j'))
        obtain ⟨-, hτb⟩ := tauSubmodule_eq_span_of_exhausted F hS hτ hext hb1 hbt hA hgb
        by_cases hjl : j = Fin.last i
        · subst hjl
          rw [Fin.snoc_last] at hj
          exact absurd hgb (not_lt.mpr hj)
        · obtain ⟨j', rfl⟩ := Fin.exists_castSucc_eq.mpr hjl
          simp only [Fin.snoc_castSucc]
          have key : ∀ (n : ℕ) (hn : n = F.r) (h : n ≤ F.r),
              IsJTauZStable J (fun l : Fin n => F.z (Fin.castLE h l)) (f j') ∧
                tauZ R (fun l : Fin n => F.z (Fin.castLE h l)) (fun _ : Fin 1 => f j') = 0 := by
            intro n hn h
            subst hn
            exact ⟨hS.isJTauZStable j', hτf j'⟩
          exact key _ hτb h }

end Assembly

section Steps

variable [IsAdicComplete (maximalIdeal R) R] [CharZero (ResidueField R)] (J : Ideal R)
  {i r : ℕ} {f : Fin i → R} {z : Fin r → R}

/-- **Claim (A)** (p. 273): if `τ_{(z)}(f_i) > 0`, there is `z_{r+1}` such that replacing `(z)` by
`(z_1, …, z_{r+1})` maintains (1)–(6).  "Immediate from Lemma 25". -/
theorem TauFrameStage.exists_snoc_system [Hironaka.HironakaCitedResults.{u}] (hS : TauFrameStage J f z) (hi : 0 < i)
    (hτ : 1 ≤ tauZ R z (fun _ : Fin 1 => f (lastIdx hi))) :
    ∃ w : R, TauFrameStage J f (Fin.snoc z w : Fin (r + 1) → R) ∧
      tauZ R (Fin.snoc z w : Fin (r + 1) → R) (fun _ : Fin 1 => f (lastIdx hi)) <
        tauZ R z (fun _ : Fin 1 => f (lastIdx hi)) := by
  obtain ⟨w, hinj, ⟨hJS, hext⟩, hτ2, hstab⟩ :=
    exists_isJTauZStable_snoc J z hS.injective (f (lastIdx hi))
      ⟨hS.isJStableSystem, hS.extendsToRSOP⟩ (hS.isJTauZStable (lastIdx hi)) hτ
  have hwT := initialForm_mem_tauZSubmoduleStar_of_tauZ_snoc hinj hext
    (fun _ : Fin 1 => f (lastIdx hi)) hτ hτ2
  have hstar := hS.tauZSubmoduleStar_last_eq hi
  have hsnoc_eq := tauZSubmoduleStar_snoc_eq_of_mem z (fun _ : Fin 1 => f (lastIdx hi)) w hwT
  refine ⟨w, ?_, by omega⟩
  exact
  { extends_std := hS.extends_std
    injective := hinj
    extendsToRSOP := hext
    mem_tauZSubmodule := by
      intro j
      refine Fin.lastCases ?_ (fun j => ?_) j
      · rw [← hstar]
        simpa [frameForm] using hwT
      · simpa [frameForm] using hS.mem_tauZSubmodule j
    tauZ_eq_zero := fun j hj =>
      tauZ_snoc_eq_zero_of_tauZ_eq_zero hinj hext _ (hS.tauZ_eq_zero j hj)
    tauZ_eq := by
      intro h
      obtain rfl : h = hi := rfl
      have := hS.tauZ_eq h
      omega
    star_le := by
      intro h
      obtain rfl : h = hi := rfl
      rw [hsnoc_eq]
      exact hS.star_le h
    isJStableSystem := hJS
    isJTauZStable := by
      intro j
      by_cases hj : (j : ℕ) + 1 < i
      · exact IsJTauZStable.snoc_of_tauZ_eq_zero hinj hext hJS (hS.isJTauZStable j)
          (hS.tauZ_eq_zero j hj)
      · have hjl : j = lastIdx hi := Fin.ext (by simp only [lastIdx]; omega)
        rw [hjl]
        exact hstab
    filtration := by
      intro b hb1 hbt hex
      obtain ⟨h, hspan⟩ := hS.filtration b hb1 hbt hex
      refine ⟨h.trans (Nat.le_succ r), ?_⟩
      have hfun : (fun l : Fin (tau R J b) =>
          frameForm (Fin.snoc z w : Fin (r + 1) → R) (Fin.castLE (h.trans (Nat.le_succ r)) l)) =
          fun l => frameForm z (Fin.castLE h l) := by
        funext l
        show frameForm (Fin.snoc z w : Fin (r + 1) → R) (Fin.castSucc (Fin.castLE h l)) = _
        simp only [frameForm, Fin.snoc_castSucc]
      rw [hfun]
      exact hspan
    r_eq_zero := fun h0 => absurd hi (by omega)
    prefix_stable := by
      intro b hb1 hbt hex h' j hj
      obtain ⟨h, -⟩ := hS.filtration b hb1 hbt hex
      have hfun : (fun l : Fin (tau R J b) => (Fin.snoc z w : Fin (r + 1) → R) (Fin.castLE h' l)) =
          fun l => z (Fin.castLE h l) := by
        funext l
        show (Fin.snoc z w : Fin (r + 1) → R) (Fin.castSucc (Fin.castLE h l)) = _
        simp only [Fin.snoc_castSucc]
      rw [hfun]
      exact hS.prefix_stable b hb1 hbt hex h j hj }

/-- **Claim (B)** (p. 274): if `τ_{(z)}(f_i) = 0` (or `i = 0`) and `(f_1, …, f_i)` is not yet a
standard base of `J`, there is `f_{i+1} ∈ J` such that replacing `(f_1, …, f_i)` by
`(f_1, …, f_{i+1})` maintains (1)–(6).  The proof is "Lemmas 18–19, §7, and Lemmas 20–21, §8".

Printed route: "take a regular frame of `R` of the form `(S; z₁, …, z_r)`"
(`exists_regularFrame_of_extendsToRSOP`); "take an element `f_{i+1}` of `J` such that
`(f₁, …, f_{i+1})` is extendable to a standard base of `J` and that `f_{i+1}` is normalized by
`(f₁, …, f_i)` with respect to `(S; z₁, …, z_r)`" (`RegularFrame.exists_snoc_isNormalizedBy`,
Lemma 17 and footnote 11); the conditions (1)–(6) for `(f₁, …, f_{i+1})` are
`TauFrameStage.snoc_of_isJTauZStable` and the `(J, τ_{(z)})`-stability of `f_{i+1}` is
`isJTauZStable_snoc_element` (`Compat/TauZStableElement.lean`).

Deviation from the paper (gap filled): the paper gives no argument beyond the quoted references.
(a) (2), (3), (4) for `(f₁, …, f_{i+1})`: `T(f₁, …, f_i) ⊆ T(f₁, …, f_{i+1})`
(`tauZSubmodule_le_snoc`, the degrees of the initial forms of a standard base do not decrease),
and `T(f₁, …, f_{i+1}) = T(f_{i+1}) + ⟨Z⟩` (`tauZSubmodule_snoc_eq`), i.e.
`τ(f₁, …, f_{i+1}) = r + τ_{(z)}(f_{i+1})`, by the core of Lemma 19 applied to the ideal
`(φ₁, …, φ_i, ψ)gr_M(R)` of the system itself
(`RegularFrame.initialForm_mem_adjoin_of_isTauZSubmodule_snoc`), not to `gr_M(J, R)` and `T*_a`;
(4) follows from `T(f₁, …, f_{i+1}) ⊆ T(standard base) = T_{t}(J)`
(`tauZSubmodule_snoc_le_tauSubmodule_t`).  (b) (6) is a statement about all permissible
sequences; the quoted lemmas treat one monoidal transform.  Lean proves it by induction along the
sequence (`ElemInv`): at every stage the frame of Remark 3 (strict transforms of the `z_j`), the
strict transforms of the `f_j` and of `f_{i+1}` satisfy again the hypotheses of Lemmas 18, 20, 21;
(8), (9) of Lemma 20 and (2) come from the `(J, τ_{(z)})`-stability of the `f_j`, (10), (12) from the
invariance of `ν*` and the `τ^{(a)}`, and `ν_P(f_{i+1}) = ν_{i+1}` from Lemma 18.  (c) Lemma 21
needs (11) `τ(f₁, …, f_i) = r` at every stage; the paper does not say that (11) is preserved by the
quotients `g_j = x^{-ν_j} f_j`.  Lean proves it (`Z ⊆ T(f)` implies `W ⊆ T(g)`,
`RegularFrame.FrameTransform.frameForm_mem_tauZSubmodule`) from `ψ_j = φ_j(W)`
(`FrameTransform.exists_polynomials_initialForm`) by the descent of Lemma 12 along the residue
field extension.  (d) The added conditions `filtration`, `prefix_stable`, `r_eq_zero` need no
further induction: the old `f_j` are already `(J, τ_{(z)})`-stable with `τ_{(z)}(f_j) = 0`, and once
the level `b` is exhausted by `(f₁, …, f_i)` one has `T_b = T(f₁, …, f_i) = ⟨Z⟩`
(`tauSubmodule_eq_span_of_exhausted`). -/
theorem TauFrameStage.exists_snoc_element [Hironaka.HironakaCitedResults.{u}] (hS : TauFrameStage J f z)
    (hτ : ∀ h : 0 < i, tauZ R z (fun _ : Fin 1 => f (lastIdx h)) = 0)
    (hnot : ¬ IsStandardBase R J f) :
    ∃ g : R, TauFrameStage J (Fin.snoc f g : Fin (i + 1) → R) z := by
  classical
  have : IsDomain R := Transforms.isDomain_of_isRegularLocalRing R
  -- "take a regular frame of `R` of the form `(S; z₁, …, z_r)`"
  obtain ⟨m, σ, hσ, Φ, -, -, -, F, hr, hFz, -⟩ :=
    exists_regularFrame_of_extendsToRSOP hS.injective hS.extendsToRSOP
  subst hr
  have hFz' : F.z = z := funext fun k => hFz k
  subst hFz'
  have hτf : ∀ j : Fin i, tauZ R F.z (fun _ : Fin 1 => f j) = 0 := by
    intro j
    by_cases hj : (j : ℕ) + 1 < i
    · exact hS.tauZ_eq_zero j hj
    · have hi : 0 < i := by have := j.2; omega
      have : j = lastIdx hi := Fin.ext (by simp only [lastIdx]; have := j.2; omega)
      rw [this]
      exact hτ hi
  -- "Then take an element `f_{i+1}` of `J` such that `(f₁, …, f_{i+1})` is extendable to a
  -- standard base of `J` and that `f_{i+1}` is normalized by `(f₁, …, f_i)` with respect to
  -- `(S; z₁, …, z_r)`"
  obtain ⟨g, hgJ, hext, hnorm⟩ := F.exists_snoc_isNormalizedBy J f
    (fun j => hS.extends_std.mem_ideal j) hS.extends_std
    (fun j => RegularFrame.initialForm_mem_adjoin_of_tauZ_eq_zero F (f j) (hτf j)) hnot
  -- "The proof of (B) for this `f_{i+1}` can be obtained by Lemmas 18–19, §7, and Lemmas 20–21, §8"
  exact ⟨g, TauFrameStage.snoc_of_isJTauZStable F hS hτ hext hnorm
    (isJTauZStable_snoc_element hS.isJStableSystem hS.isJTauZStable hτf hext hnorm
      hS.mem_tauZSubmodule)⟩

/-- **The end of the induction** (not written in the paper): at a stage where `(f_1, …, f_i)` is a
standard base of `J` and `τ_{(z)}(f_i) = 0`, the system `(z)` is the system of a `J`-stable
regular `τ`-frame of `R` for `J` (Definition 12). -/
theorem TauFrameStage.exists_isJStableTauFrame [Hironaka.HironakaCitedResults.{u}] (hS : TauFrameStage J f z)
    (hstd : IsStandardBase R J f)
    (hτ : ∀ h : 0 < i, tauZ R z (fun _ : Fin 1 => f (lastIdx h)) = 0) :
    ∃ F : RegularFrame R, F.IsJStableTauFrame J := by
  obtain ⟨m, σ, hσ, Φ, -, -, -, F, hr, hFz, -⟩ :=
    exists_regularFrame_of_extendsToRSOP hS.injective hS.extendsToRSOP
  have hFz' : ∀ k : Fin F.r, F.z k = z (Fin.cast hr k) := fun k => by
    have := hFz (Fin.cast hr k)
    rwa [show Fin.cast hr.symm (Fin.cast hr k) = k from Fin.ext rfl] at this
  have hJF : F.IsJStable J := fun k => by
    rw [hFz' k]
    exact hS.isJStableSystem _
  have htr : tau R J (t R J) = F.r := (hS.tau_eq_r hstd hτ).trans hr.symm
  refine ⟨F, ?_, hJF, ?_⟩
  · -- `F` is a regular `τ`-frame: the ordered notion, from the initial segments of `(z)`
    refine RegularFrame.isRegularTauFrame_of_forall_tauZ_eq_zero F J f hstd htr
      fun b hb hbt h j hj => ?_
    have h0 : tau R J b ≤ r := h.trans hr.le
    have hfun : (fun l : Fin (tau R J b) => F.z (Fin.castLE h l)) =
        fun l => z (Fin.castLE h0 l) := funext fun l => by rw [hFz']; rfl
    rw [hfun]
    exact (hS.prefix_stable_all hstd hτ hb hbt h0 j hj).2
  · intro Sq e he hperm hsep αb hαb hnu ht htau
    obtain ⟨c, -⟩ := exists_frameTransformAlong_of_isJStable F J hJF Sq e he hperm hsep αb hnu htau
    refine ⟨c.frame αb, ?_, ⟨c, rfl⟩⟩
    obtain ⟨hrG, hstrict⟩ :=
      MonoidalSequence.FrameTransformAlong.isStrictTransformElem_frame F J hJF Sq e he hperm hsep
        αb hnu htau c αb le_rfl
    -- the strict transforms of the `f_j` form a standard base of `J_ᾱ`
    choose g hg using fun j => MonoidalSequence.exists_strictAlong_span_singleton_eq_aux Sq e
      hperm.hasRegularCenters (f j) αb
    have hg' : ∀ j, Sq.IsStrictTransformElem e (f j) αb (g j) := fun j => (hg j).symm
    have hgstd := isStandardBase_strictTransform_of_isJStableSystem J f hstd
      hS.isJStableSystem_f Sq e he hperm hsep αb hnu ht htau g hg'
    have hord : ∀ j, Ideal.ordElem (maximalIdeal (Sq.ring αb)) (g j) =
        Ideal.ordElem (maximalIdeal R) (f j) := fun j =>
      (hS.isJStableSystem_f j Sq e he hperm hsep αb hnu ht htau (g j) (hg' j)).1
    have hmu := mu_congr_of_nuStar_eq hnu
    -- the arity
    have harity :
        tau (Sq.ring αb) (Sq.ideal αb) (t (Sq.ring αb) (Sq.ideal αb)) = (c.frame αb).r := by
      rw [hrG]
      rcases Nat.eq_zero_or_pos i with hi | hi
      · subst hi
        rw [tau_eq_zero_of_isStandardBase_nil g hgstd, ← htr,
          t_eq_zero_of_isStandardBase_nil f hstd, tau_eq_zero_of_isStandardBase_nil f hstd]
      · rw [ht, htau (t R J) (one_le_t_of_isStandardBase hstd hi) le_rfl]
        exact htr
    refine RegularFrame.isRegularTauFrame_of_forall_tauZ_eq_zero (c.frame αb) (Sq.ideal αb) g
      hgstd harity fun b hb hbt h j hj => ?_
    have hbt' : b ≤ t R J := ht ▸ hbt
    have htb : tau (Sq.ring αb) (Sq.ideal αb) b = tau R J b := htau b hb hbt'
    have h0 : tau R J b ≤ r := htb ▸ (h.trans (hrG.trans hr).le)
    have hj' : Ideal.ordElem (maximalIdeal R) (f j) ≤ (mu R J b : ℕ∞) := by
      rw [← hord j, ← hmu b]
      exact hj
    obtain ⟨hstab, hz0⟩ := hS.prefix_stable_all hstd hτ hb hbt' h0 j hj'
    generalize hn : tau (Sq.ring αb) (Sq.ideal αb) b = n at h ⊢
    obtain rfl : n = tau R J b := hn.symm.trans htb
    have hzα : ∀ l : Fin (tau R J b), Sq.IsStrictTransformElem e (z (Fin.castLE h0 l)) αb
        ((c.frame αb).z (Fin.castLE h l)) := fun l => by
      have := hstrict (Fin.castLE h l)
      rwa [hFz', show Fin.cast hr (Fin.cast hrG (Fin.castLE h l)) = Fin.castLE h0 l from
        Fin.ext rfl] at this
    have := (hstab.2.2 Sq e he hperm hsep αb hnu ht htau _ hzα (g j) (hg' j)).2.2
    rw [this]
    exact hz0

/-- **The iteration** of (A) and (B), which stops because the length of a standard base is
bounded (the paper does not describe the termination). -/
theorem exists_tauFrameStage_final [Hironaka.HironakaCitedResults.{u}] :
    ∃ (i r : ℕ) (f : Fin i → R) (z : Fin r → R), TauFrameStage J f z ∧ IsStandardBase R J f ∧
      ∀ h : 0 < i, tauZ R z (fun _ : Fin 1 => f (lastIdx h)) = 0 := by
  classical
  obtain ⟨N, g₀, hg₀⟩ := exists_isStandardBase J
  -- the measure `(N - i, τ)`, lexicographically
  suffices H : ∀ a b : ℕ, ∀ (i r : ℕ) (f : Fin i → R) (z : Fin r → R), N - i = a →
      lastTauZ f z = b → TauFrameStage J f z →
      ∃ (i r : ℕ) (f : Fin i → R) (z : Fin r → R), TauFrameStage J f z ∧ IsStandardBase R J f ∧
        ∀ h : 0 < i, tauZ R z (fun _ : Fin 1 => f (lastIdx h)) = 0 by
    exact H _ _ 0 0 ![] ![] rfl rfl (TauFrameStage.zero J)
  intro a
  induction a using Nat.strong_induction_on with
  | _ a iha =>
  intro b
  induction b using Nat.strong_induction_on with
  | _ b ihb =>
  intro i r f z ha hb hS
  by_cases hpos : ∃ hi : 0 < i, 1 ≤ tauZ R z (fun _ : Fin 1 => f (lastIdx hi))
  · -- (A)
    obtain ⟨hi, hτ⟩ := hpos
    obtain ⟨w, hw, hlt⟩ := hS.exists_snoc_system J hi hτ
    refine ihb (lastTauZ f (Fin.snoc z w : Fin (r + 1) → R)) ?_ i (r + 1) f _ ha rfl hw
    simp only [← hb, lastTauZ, hi, ↓reduceDIte]
    exact hlt
  · have hτ0 : ∀ h : 0 < i, tauZ R z (fun _ : Fin 1 => f (lastIdx h)) = 0 := by
      intro h
      by_contra hne
      exact hpos ⟨h, by omega⟩
    by_cases hstd : IsStandardBase R J f
    · exact ⟨i, r, f, z, hS, hstd, hτ0⟩
    · obtain ⟨g, hg⟩ := hS.exists_snoc_element J hτ0 hstd
      -- `i < N`: otherwise `f` is itself a standard base
      have hiN : i < N := by
        by_contra hge
        obtain ⟨m₁, g₁, him, hg₁, -⟩ := hS.extends_std
        have hmN : m₁ = N := hg₁.length_eq hg₀
        exact hstd (hS.extends_std.isStandardBase_of_length_eq hg₀ (by omega)).2
      exact iha (N - (i + 1)) (by omega) (lastTauZ (Fin.snoc f g : Fin (i + 1) → R) z)
        (i + 1) r _ z rfl rfl hg

end Steps

end TauFrameStage

/-! ### Theorem 9 (pp. 273–274) -/

section Theorem9

variable {R : Type u} [CommRing R] [IsRegularLocalRing R]

/-- Theorem 9, p. 273: "Let `R` be a complete regular local ring whose residue field has
characteristic zero, and `J` an ideal in `R`. Then there exists a `J`-stable regular `τ`-frame of
`R` for `J` and a `J`-stable standard base of `J`."

(Formalization note: the two objects are asserted to exist independently, as printed; "complete"
is `IsAdicComplete (maximalIdeal R) R`.) -/
@[blueprint "thm:III.9"
  (statement := /-- Let $R$ be a complete regular local ring whose residue field has
    characteristic zero, and $J$ an ideal in $R$. Then there exists a $J$-stable regular
    $\tau$-frame of $R$ for $J$ (\cref{def:III.12}) and a $J$-stable standard base of $J$
    (\cref{def:III.3}, \cref{def:III.11}). (Theorem 9, p.~273.) -/)
  (proof := /-- We may assume that $J\ne(0)$. Let us assume that there exists a system of
    elements $(f_1,\dots,f_i)$ of $J$ and $(z_1,\dots,z_r)$ of the maximal ideal $M$ of $R$
    ($i\ge0$, $r\ge0$) such that
    \begin{enumerate}
      \item[(1)] $(f_1,\dots,f_i)$ is extendable to a standard base of $J$
        (\cref{def:III.7-extends-standard-base}),
      \item[(2)] $(z)=(z_1,\dots,z_r)$ can be extended to a regular system of $\tau$-parameters
        of $R$ for the system $(f_1,\dots,f_i)$,
      \item[(3)] $\tau_{(z)}(f_j)=0$ ($1\le j\le i-1$), and
        $\tau(f_1,\dots,f_i)=r+\tau_{(z)}(f_i)$,
      \item[(4)] the extension of $(z)$ by a regular system of $\tau_{(z)}$-parameters of $R$ for
        $(f_i)$ is extendable to a regular system of $\tau$-parameters of $R$ for $J$,
      \item[(5)] $(z)$ is $J$-stable, and finally
      \item[(6)] $f_j$ is $(J,\tau_{(z)})$-stable for all $j$ ($1\le j\le i$).
    \end{enumerate}
    (Recall Definitions 7 (\S4), 10* (\S7), 11 (\S9) and 13 (\S10): \cref{def:III.7},
    \cref{def:III.10-star}, \cref{def:III.11}, \cref{def:III.13}.) We then claim:
    \begin{enumerate}
      \item[(A)] If $\tau_{(z)}(f_i)>0$, then there exists an element $z_{r+1}\in M$ such that
        replacing $(z)$ by $(z_1,\dots,z_r,z_{r+1})$ we maintain (1)--(6).
      \item[(B)] If $\tau_{(z)}(f_i)=0$, then there exists an element $f_{i+1}\in J$ such that
        replacing $(f_1,\dots,f_i)$ by $(f_1,\dots,f_i,f_{i+1})$ we maintain (1)--(6).
    \end{enumerate}
    (A) is immediate from Lemma~25 (\cref{lem:III.25}). To prove (B), take a regular frame of
    $R$ of the form $(S;z_1,\dots,z_r)$. Then take an element $f_{i+1}$ of $J$ such that
    $(f_1,\dots,f_i,f_{i+1})$ is extendable to a standard base of $J$ and that $f_{i+1}$ is
    normalized by $(f_1,\dots,f_i)$ with respect to $(S;z_1,\dots,z_r)$
    (\cref{def:III.9-normalized-by}). (We should refer to Lemma~17, \S7, \cref{lem:III.17}.
    See also the footnote 11 of this chapter, \cref{lem:III.8-normalized-standard-base-exists}.)
    The proof of (B) for this $f_{i+1}$ can be obtained by Lemmas 18--19, \S7
    (\cref{lem:III.18}, \cref{lem:III.19}), and Lemmas 20--21, \S8 (\cref{lem:III.20},
    \cref{lem:III.21}).

    [Editorial gloss, not in the paper, which ends here: starting from $i=r=0$, where (1)--(6)
    hold trivially, (A) and (B) are applied as long as possible; this stops after finitely many
    steps because $r\le\dim R$ and $i$ is bounded by the number of elements of a standard base
    of $J$, and the resulting systems $(z)$ and $(f_1,\dots,f_i)$ yield the assertion.]

    \textbf{Deviation from the paper (gap filled), claim (B).} The paper's proof of (B) is the
    quoted sentence. (a) $T(f_1,\dots,f_i)\subseteq T(f_1,\dots,f_{i+1})$ and
    $T(f_1,\dots,f_{i+1})=T(f_{i+1})+\langle Z\rangle$ (so (2), (3), (4)) are proved from the
    core of Lemma~19 applied to the ideal $(\varphi_1,\dots,\varphi_i,\psi)\operatorname{gr}_M(R)$
    of the system itself and from the identification of $T$ of a standard base with $T_t(J)$.
    (b) Condition (6) is a statement about all permissible sequences, while Lemmas~18, 20, 21 treat
    one monoidal transform: it is proved by induction along the sequence, with the frames of
    Remark~3 and the strict transforms of the $f_j$ and $f_{i+1}$, the hypotheses of the lemmas at
    each stage coming from the $(J,\tau_{(z)})$-stability of $f_1,\dots,f_i$. (c) Lemma~21 needs
    $\tau(g_1,\dots,g_i)=r$ at the next stage, which the paper does not state: it is proved from
    $\psi_j=\varphi_j(W)$ and Lemma~12 (descent along the extension of residue fields).
    (d) The conditions of the formalization beyond (1)--(6) follow from these. -/)
  (latexEnv := "theorem")]
theorem exists_isJStableTauFrame_and_isJStable_standardBase [Hironaka.HironakaCitedResults.{u}]
    [IsAdicComplete (maximalIdeal R) R] [CharZero (ResidueField R)] (J : Ideal R) :
    (∃ F : RegularFrame R, F.IsJStableTauFrame J) ∧
      ∃ (m : ℕ) (f : Fin m → R), IsStandardBase R J f ∧ IsJStableSystem J f := by
  obtain ⟨i, r, f, z, hS, hstd, hτ⟩ := exists_tauFrameStage_final J
  exact ⟨hS.exists_isJStableTauFrame J hstd hτ, i, f, hstd, hS.isJStableSystem_f⟩

end Theorem9

end Hironaka
