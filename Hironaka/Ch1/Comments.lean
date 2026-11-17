/-
Copyright (c) 2026 Daattavya Aggarwal, Minhyong Kim, Oisin Kim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daattavya Aggarwal, Minhyong Kim, Oisin Kim
-/
module

public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Architect
public import Hironaka.Statements
public import Hironaka.Compat.Graded
public import Hironaka.Ch1.ResolutionData
public import Hironaka.Ch1.InductionScheme
public import Hironaka.Ch1.FundamentalTheorems
public import Hironaka.Ch3.TauStar

/-!
# Hironaka (1964), Chapter I, §4 (pp. 177–180): comments on the fundamental theorems and their proofs

This file states, and does not prove, what the paper says in §4 "Comments on fundamental theorems
and on their proofs".  The paper gives no proofs here: it announces modified proofs "left to the
reader" and a theorem (Theorem III^N) with an outline of an inductive proof, followed by a Main
Theorem III(N, n) that "can be deduced easily" from it.  Every statement below is a `def … : Prop`
(the encoding used for the fundamental theorems, `Hironaka/Statements.lean`).

Printed text (p. 177): "we remark that a simple modification of the proof of the implication
(A), given in Ch. IV, gives us the following implication:
Th. I₁^{N',n'} with {n' < N' < N, n' < n}, Th. I₂^{N,n''} with n'' < n, and Th. II₂^{N''} with
N'' ≦ n ⟹ Th. I₁^{N,n}, and also that a simple modification of the proof of the implication (B),
given in Chapter IV, gives us the following implication: …⟹ Th. I₂^{N,n}."

Printed text (p. 178): "Here we must use the fact that if J is an ideal in a regular local ring
R which is different from R and if (z₁, ⋯, z_τ) is a regular system of τ-parameters of R for J,
then dim(R) ≦ τ + dim(R/J).  (This follows from the fact that if M is the maximal ideal of R, then
dim(gr_M(R/J)) = dim(R/J), which is well-known.)"

Printed text (pp. 178–179), Theorem III^N: "Let X be a non-singular irreducible algebraic scheme of
dimension N ≧ 0.  Let {ℜ_i (1 ≦ i ≦ r), ℜ'_j (1 ≦ j ≦ s)} be a finite number of resolution data
on X which have the following forms: ℜ_i = (E; V_{i1}, ⋯, V_{iβ}; W_i) for 1 ≦ i ≦ r, and
ℜ'_j = (E₁, ⋯, E_α | J_j, b_j ; a_{j1}, ⋯, a_{jα}) for 1 ≦ j ≦ s, where E = ⋃_{k=1}^α E_k and
ν(j) = ν(ℜ'_j) > 0 for all j (1 ≦ j ≦ s).  Here we do not exclude the case in which the principal
subscheme W_i of ℜ_i is equal to X for some i.  Then there exists a finite succession of monoidal
transformations f : X̃ → X, which is permissible for all the data ℜ_i and ℜ'_j, such that (either
X̃ is empty or) ⋂_{j=1}^s S_{ν(j)}(f*(ℜ'_j)) has no points in the intersection of the principal
subschemes of the f*(ℜ_i) for 1 ≦ i ≦ r."

Printed text (p. 180), Main Theorem III(N, n): "Let X, J and E be the same as in the main theorem
II(N) of § 3, this chapter.  Let W be a reduced subscheme of dimension n of X.  Then there exists a
finite succession of monoidal transformations {f_i : X_{i+1} → X_i} with centers B_i in X_i, where
0 < i < r [sic] and X = X₀, which has the following properties: (a) If W_i is the strict transform
of W in X_i by the succession of monoidal transformations, then B_i is a non-singular irreducible
subscheme of W_i along which W_i is normally flat, (b) if J_i is the weak transform of J in X_i by
the succession of monoidal transformations, then ν(J_{iz}) = d_i for all the points z of B_i, where
d_i is the maximal integer attained by ν(J_{iy}) with a point y of W_i, (c) the same as (3) of
II(N), § 3, and (d) W_r is empty."  Footnote 38: "This assertion (d) is equivalent to saying that
B_{r−1} ⊇ W_{r−1} (hence, by (a), B_{r−1} = W_{r−1})."

Classification (see the docstring of each declaration): the two implications are statements that
the paper makes and whose proofs it leaves to the reader (pp. 177–178); the fact of p. 178 is
argued from a "well-known" fact (not cited), and proved in `Hironaka.Ch1.CommentsProofs` from that fact
as an explicit hypothesis; Theorem III^N and Main Theorem III(N, n) are stated with the proof left to
the reader; footnote 38 is stated without proof, its parenthesis "hence, by (a)" being argued from (a)
and proved in `Hironaka.Ch1.CommentsProofs`.  The other statements are not proved here.
-/

@[expose] public section

noncomputable section

universe u
open IsLocalRing AlgebraicGeometry

namespace Hironaka

/-! ### The implications (A′) and (B′) (pp. 177–178) -/

namespace FundamentalTheoremFamily

variable (T : FundamentalTheoremFamily)

/-- The implication (A′) of p. 177: "a simple modification of the proof of the implication (A), given
in Ch. IV, gives us the following implication:
Th. I₁^{N',n'} with {n' < N' < N, n' < n}, Th. I₂^{N,n''} with n'' < n, and
Th. II₂^{N''} with N'' ≦ n ⟹ Th. I₁^{N,n}."

Stated without proof here; the paper leaves the details of the modified proof to the reader (p. 178:
"The details in the modified proofs will be left to the reader"); not proved here.

Formalization notes (encoding): as for `ImplicationA`, the pair `(N, n)` is given with `n < N`
(the context of (A), pp. 171–172), and all indices are natural numbers (the index `n = -1` is
absent, as in `FundamentalTheoremFamily`).  The three hypotheses of the display are the three
rows; the hypothesis `N'' ≦ n` ranges over all `N''`, and `II₂^0` is the base case. -/
@[blueprint "def:I.4-implication-A-prime"
  (statement := /-- \textbf{Implication (A$'$)} for a family $T$ (\cref{def:I.2-family}): for all
    $(N,n)$ with $0\le n<N$,
    \[ \mathrm I_1^{N',n'}\ (n'<N'<N,\ n'<n),\quad \mathrm I_2^{N,n''}\ (n''<n),\quad
       \mathrm{II}_2^{N''}\ (N''\le n) \qquad\Longrightarrow\qquad \mathrm I_1^{N,n}. \]
    (p.~177.) Formalization note (encoding): as for \cref{def:I.2-implication-A}, $(N,n)$ is
    given with $n<N$ and the indices are natural numbers. -/)
  (latexEnv := "definition")]
def ImplicationAPrime : Prop :=
  ∀ N n, n < N →
    (∀ N' n', n' < N' → N' < N → n' < n → T.I₁ N' n') →
    (∀ n'', n'' < n → T.I₂ N n'') →
    (∀ N'', N'' ≤ n → T.II₂ N'') →
    T.I₁ N n

/-- The implication (B′) of p. 177: "a simple modification of the proof of the implication (B), given
in Chapter IV, gives us the following implication:
Th. I₂^{N',n'} with {n' < N' < N, n' < n}, Th. I₂^{N,n''} with n'' < n, and
Th. II₂^{N''} with N'' ≦ n ⟹ Th. I₂^{N,n}."

Stated without proof here; the paper leaves the details of the modified proof to the reader (p. 178);
not proved here.

Deviation (misprint, read from the page image): in the printed display of (B′) the primes of the
first two rows are interchanged: the first row reads "Th. I₂^{N,n''} with {n' < N' < N, n' < n}"
and the second "Th. I₂^{N',n'} with n'' < n", so that the conditions on `N', n'` stand beside a
theorem in `N, n''` and conversely.  We read the first row as `I₂^{N',n'}` with its conditions
and the second as `I₂^{N,n''}` with `n'' < n`, in analogy with (A′) and with the printed (B)
(`ImplicationB`).  Formalization notes (encoding): as for `ImplicationAPrime`; note that (B′) has no
hypothesis on `I₁`, unlike (B). -/
@[blueprint "def:I.4-implication-B-prime"
  (statement := /-- \textbf{Implication (B$'$)} for a family $T$ (\cref{def:I.2-family}): for all
    $(N,n)$ with $0\le n<N$,
    \[ \mathrm I_2^{N',n'}\ (n'<N'<N,\ n'<n),\quad \mathrm I_2^{N,n''}\ (n''<n),\quad
       \mathrm{II}_2^{N''}\ (N''\le n) \qquad\Longrightarrow\qquad \mathrm I_2^{N,n}. \]
    (p.~177.) Formalization note (misprint): in the printed display the primes of the first two
    rows are interchanged (the first row reads $\mathrm I_2^{N,n''}$ beside the conditions on
    $N',n'$, the second $\mathrm I_2^{N',n'}$ beside $n''<n$); we read the rows as above, as in
    (A$'$). The encoding is as for \cref{def:I.4-implication-A-prime}. -/)
  (latexEnv := "definition")]
def ImplicationBPrime : Prop :=
  ∀ N n, n < N →
    (∀ N' n', n' < N' → N' < N → n' < n → T.I₂ N' n') →
    (∀ n'', n'' < n → T.I₂ N n'') →
    (∀ N'', N'' ≤ n → T.II₂ N'') →
    T.I₂ N n

end FundamentalTheoremFamily

/-- The claim of p. 177 that the fundamental theorems satisfy the implication (A′): "we remark that a
simple modification of the proof of the implication (A), given in Ch. IV, gives us the following
implication" (the display `ImplicationAPrime`).

Left to the reader (p. 178: "The details in the modified proofs will be left to the reader"); not
proved here.  Formalization note (encoding): the statement is `ImplicationAPrime` for the family of
the actual fundamental theorems (`fundamentalFamily`). -/
@[blueprint "thm:I.4-implication-A-prime"
  (statement := /-- The family of fundamental theorems (\cref{def:I.2-fundamental-family})
    satisfies the implication (A$'$) (\cref{def:I.4-implication-A-prime}): ``a simple
    modification of the proof of the implication (A), given in Ch.~IV, gives us the following
    implication'' (p.~177); ``the details in the modified proofs will be left to the reader''
    (p.~178). Not proved here: left to the reader. -/)
  (latexEnv := "theorem")]
def FundamentalTheorem.implicationAPrime : Prop :=
  fundamentalFamily.{u}.ImplicationAPrime

/-- The claim of p. 177 that the fundamental theorems satisfy the implication (B′): "a simple
modification of the proof of the implication (B), given in Chapter IV, gives us the following
implication" (the display `ImplicationBPrime`, read as explained there).

Left to the reader (p. 178: "The details in the modified proofs will be left to the reader"); not
proved here. -/
@[blueprint "thm:I.4-implication-B-prime"
  (statement := /-- The family of fundamental theorems (\cref{def:I.2-fundamental-family})
    satisfies the implication (B$'$) (\cref{def:I.4-implication-B-prime}): ``a simple
    modification of the proof of the implication (B), given in Chapter~IV, gives us the following
    implication'' (p.~177); the details are left to the reader (p.~178). Not proved here: left to
    the reader. -/)
  (latexEnv := "theorem")]
def FundamentalTheorem.implicationBPrime : Prop :=
  fundamentalFamily.{u}.ImplicationBPrime

/-! ### The dimension fact of p. 178 -/

/-- The fact of p. 178 that the paper uses for the modified proofs: "if J is an ideal in a regular
local ring R which is different from R and if (z₁, ⋯, z_τ) is a regular system of τ-parameters of R
for J, then dim(R) ≦ τ + dim(R/J)".

Argued, from a "well-known" fact (`DimAssocGradedQuotient`): "(This follows from the fact that if M is
the maximal ideal of R, then dim(gr_M(R/J)) = dim(R/J), which is well-known.)" (p. 178).  Proved, with
that fact as an explicit hypothesis, in `dimLeTauAddDimQuotient_of_dimAssocGradedQuotient`
(`Hironaka/Ch1/CommentsProofs.lean`).

Formalization notes (encoding): a regular system of τ-parameters of `R` for `J` is a regular system
of `t(J)`-th τ-parameters (Definition 7, p. 223: `IsRegularSystemOfTauParameters R J (t R J) z`),
whose length is `τ = τ^{(t)}(J) = tau R J (t R J)`; dimensions are Krull dimensions in
`WithBot ℕ∞`.  For `J = 0` the paper's `t(J) = 0` and `τ^{(0)}` is not defined; `tau R J 0`
is the junk value `0` and the statement reads `dim R ≦ dim R`, true.  The printed inequality is
`≦` (read on the page image). -/
@[blueprint "lem:I.4-dim-tau"
  (statement := /-- Let $J$ be an ideal in a regular local ring $R$ which is different from $R$,
    and $(z_1,\dots,z_\tau)$ a regular system of $\tau$-parameters of $R$ for $J$
    (\cref{def:III.7}). Then $\dim(R)\le\tau+\dim(R/J)$. (This follows from the fact that if $M$ is
    the maximal ideal of $R$, then $\dim(\operatorname{gr}_M(R/J))=\dim(R/J)$, which is
    well-known; \cref{lem:I.4-dim-gr}.) (p.~178.) Formalization note (encoding): $\tau$ is the
    length $\tau^{(t)}(J)$ of the system, $t=t(J)$ (\cref{def:III.6-t}); for $J=0$, where $t=0$,
    the statement reads $\dim R\le\dim R$. Argued in the paper from a well-known fact
    (\cref{lem:I.4-dim-gr}), which is stated without proof and enters as a hypothesis. -/)
  (proof := /-- The paper's argument is the one sentence ``This follows from the fact that if $M$ is
    the maximal ideal of $R$, then $\dim(\operatorname{gr}_M(R/J))=\dim(R/J)$, which is
    well-known'' (the hypothesis, \cref{lem:I.4-dim-gr}, assumed as in the paper).

    \textbf{Gaps in the paper filled.} Extend $(z_1,\dots,z_\tau)$ to a regular system of parameters
    $(y_1,\dots,y_n)$ of $R$, $n=\dim R$ (p.~223), so that $\operatorname{gr}_M(R)=K[X_1,\dots,X_n]$
    (p.~225), $K=R/M$, and $\operatorname{gr}_M(R/J)=\operatorname{gr}_M(R)/\operatorname{gr}_M(J,R)$.
    By Definition~7 with $b=t$ and because $\operatorname{gr}_M(J,R)$ is generated in degrees
    $\le\mu_t$, $\operatorname{gr}_M(J,R)=(\operatorname{gr}_M(J,R)\cap K[T])
    \operatorname{gr}_M(R)$ with $T$ spanned by the classes of $z_1,\dots,z_\tau$
    (\cref{lem:I.4-dim-tau-gr-ideal}). So $\operatorname{gr}_M(R/J)$ maps onto a polynomial ring in
    $n-\tau$ variables over a field (\cref{lem:I.4-dim-tau-polynomial}) and
    $\dim\operatorname{gr}_M(R/J)\ge n-\tau$; with the hypothesis, $\dim R=n\le\tau+\dim(R/J)$
    (\cref{lem:I.4-dim-tau-core}). For $J=0$, where $t=0$, the statement is $\dim R\le\dim R$. -/)
  (proofUses := ["lem:I.4-dim-gr", "lem:I.4-dim-tau-core", "lem:I.4-dim-tau-gr-ideal",
    "lem:I.4-dim-tau-polynomial", "lem:III.7-extends-system"])
  (latexEnv := "lemma")]
def DimLeTauAddDimQuotient : Prop :=
  ∀ (R : Type u) [CommRing R] [IsRegularLocalRing R] (J : Ideal R), J ≠ ⊤ →
    ∀ z : Fin (tau R J (t R J)) → maximalIdeal R,
      IsRegularSystemOfTauParameters R J (t R J) z →
        ringKrullDim R ≤ (tau R J (t R J) : WithBot ℕ∞) + ringKrullDim (R ⧸ J)

/-- The "well-known" fact quoted on p. 178: "if M is the maximal ideal of R, then
dim(gr_M(R/J)) = dim(R/J), which is well-known" (`R` a regular local ring, `J ≠ R`).

Stated without proof or citation (p. 178: "which is well-known"); not proved here.

Formalization notes (encoding): `gr_M(R/J)` is the associated graded ring of the local ring `R/J`
with respect to the ideal `M(R/J)`, the image of `M` (`AssocGraded`, Ch. II §1); both dimensions are
Krull dimensions.  Mathlib has no dimension theory of associated graded rings, so this is not
a Mathlib statement. -/
@[blueprint "lem:I.4-dim-gr"
  (statement := /-- Let $R$ be a regular local ring with maximal ideal $M$ and $J\ne R$ an ideal.
    Then $\dim(\operatorname{gr}_M(R/J))=\dim(R/J)$, which is ``well-known'' (p.~178). Formalization
    note (encoding): $\operatorname{gr}_M(R/J)$ is the associated graded ring of $R/J$ with respect
    to the image of $M$ (\cref{def:II.1-associated-graded-algebra}). Not proved here: stated
    without proof or citation. -/)
  (latexEnv := "lemma")]
def DimAssocGradedQuotient : Prop :=
  ∀ (R : Type u) [CommRing R] [IsRegularLocalRing R] (J : Ideal R), J ≠ ⊤ →
    ringKrullDim (AssocGraded (Ideal.map (Ideal.Quotient.mk J) (maximalIdeal R))) =
      ringKrullDim (R ⧸ J)

/-! ### Theorem III^N (pp. 178–179) -/

namespace MonoidalSuccession

/-- A succession of monoidal transformations is *permissible for all the data* of a finite family of
data of type I and a finite family of data of type II (p. 179: "permissible for all the data ℜ_i
and ℜ'_j"): each step is permissible for every datum, each datum being transformed at every step
(Definition 8, p. 169).  The recursion is that of `IsPermissibleI` and `IsPermissibleII`, with the
whole families carried along.

Formalization note (encoding): the paper's phrase is not defined separately; this is Definition 8
for every datum of the families at once.  It is equivalent to `∀ i, s.IsPermissibleI (ℜ i)` together
with `∀ j, s.IsPermissibleII (ℜ' j)`, since the transforms of the different data do not interact. -/
@[blueprint "def:I.4-permissible-for-all"
  (statement := /-- A succession of monoidal transformations $f=\{f_i\}$ with centers $B_i$ is
    \emph{permissible for all the data} $\mathfrak R_1,\dots,\mathfrak R_r$ (type $\mathrm I$) and
    $\mathfrak R'_1,\dots,\mathfrak R'_s$ (type $\mathrm{II}$) if each $f_i$ is permissible for the
    transform by $f_0,\dots,f_{i-1}$ of every one of them (Definition~8, p.~169, applied to every
    datum; p.~179). Formalization note (encoding): defined by the recursion of
    \cref{def:I.8}, carrying both families. -/)
  (latexEnv := "definition")]
def IsPermissibleForAll {r s : ℕ} : {X Y : Scheme.{u}} → MonoidalSuccession X Y →
    (Fin r → DatumI.Raw X) → (Fin s → DatumII.Raw X) → Prop
  | _, _, nil _, _, _ => True
  | _, _, cons B t rest, ℜ, ℜ' =>
      (∀ i, (ℜ i).IsPermissible B) ∧ (∀ j, (ℜ' j).IsPermissible B) ∧
        rest.IsPermissibleForAll (fun i => (ℜ i).transform t) (fun j => (ℜ' j).transform t)

end MonoidalSuccession

/-- Theorem III^N (pp. 178–179): "Let X be a non-singular irreducible algebraic scheme of dimension
N ≧ 0.  Let {ℜ_i (1 ≦ i ≦ r), ℜ'_j (1 ≦ j ≦ s)} be a finite number of resolution data on X which
have the following forms: ℜ_i = (E; V_{i1}, ⋯, V_{iβ}; W_i) for 1 ≦ i ≦ r, and
ℜ'_j = (E₁, ⋯, E_α | J_j, b_j ; a_{j1}, ⋯, a_{jα}) for 1 ≦ j ≦ s, where E = ⋃_{k=1}^α E_k and
ν(j) = ν(ℜ'_j) > 0 for all j (1 ≦ j ≦ s).  Here we do not exclude the case in which the principal
subscheme W_i of ℜ_i is equal to X for some i.  Then there exists a finite succession of monoidal
transformations f : X̃ → X, which is permissible for all the data ℜ_i and ℜ'_j, such that (either
X̃ is empty or) ⋂_{j=1}^s S_{ν(j)}(f*(ℜ'_j)) has no points in the intersection of the principal
subschemes of the f*(ℜ_i) for 1 ≦ i ≦ r."

Left to the reader (p. 178: "the reader who finds himself familiar with the arguments in Ch. IV will
easily find an inductive proof of the following theorem"; p. 180: "A detailed proof is left to the
reader"); not proved here.

Formalization notes (encoding): `X` is `IsAmbient X N` (non-singular, irreducible, algebraic, of
dimension `N ≧ 0`, as in the fundamental theorems); `r, s ≧ 0` are arbitrary (with `r = s = 0` the
statement asks that `X̃` be empty: this is the paper's parenthesis).  The data are
`ℜ i = (⋃ₖ E k; V i 1, …, V i β; W i)` of type I (one `β` for all `i`, as printed) and
`ℜ' j = (E 1, …, E α | J j, b j; a j 1, …, a j α)` of type II (one `α` and the same `E k` for all
`j`), each a resolution datum (`IsDatum`); the union `E = ⋃ₖ E k` is the intersection of the ideal
sheaves, `⨅ k, E k` (as `DatumII.Raw.eUnion`).  "ν(j) = ν(ℜ'_j) > 0" is `0 < (ℜ' j).nu`; "permissible
for all the data" is `MonoidalSuccession.IsPermissibleForAll`; `S_{ν(j)}(f*(ℜ'_j))` is
`(s.transformII (ℜ' j)).sNu (ℜ' j).nu` with `ν(j)` the order of the original datum; "the principal
subscheme of `f*(ℜ_i)`" is `(s.transformI (ℜ i)).principal`; intersections over an empty index set
are the whole space.  The clause "(either X̃ is empty or)" is kept as a disjunct (it is implied by
the second one).  The case `W_i = X` needs no encoding: nothing excludes it. -/
@[blueprint "thm:I.4-III"
  (statement := /-- \textbf{Theorem III$^N$.} Let $X$ be a non-singular irreducible algebraic
    scheme of dimension $N\ge0$. Let $\{\mathfrak R_i\,(1\le i\le r),\ \mathfrak R'_j\,(1\le j\le
    s)\}$ be a finite number of resolution data on $X$ of the forms
    $\mathfrak R_i=(E;V_{i1},\dots,V_{i\beta};W_i)$ for $1\le i\le r$ and
    $\mathfrak R'_j=\big(E_1,\dots,E_\alpha\,\big|\,J_j,b_j\,\big|\,a_{j1},\dots,a_{j\alpha}\big)$
    for $1\le j\le s$, where $E=\bigcup_{k=1}^\alpha E_k$ and $\nu(j)=\nu(\mathfrak R'_j)>0$ for all
    $j$. Here we do not exclude the case in which the principal subscheme $W_i$ of
    $\mathfrak R_i$ is equal to $X$ for some $i$. Then there exists a finite succession of
    monoidal transformations $f\colon\tilde X\to X$, which is permissible for all the data
    $\mathfrak R_i$ and $\mathfrak R'_j$ (\cref{def:I.4-permissible-for-all}), such that (either
    $\tilde X$ is empty or) $\bigcap_{j=1}^sS_{\nu(j)}(f^*(\mathfrak R'_j))$ has no points in the
    intersection of the principal subschemes of the $f^*(\mathfrak R_i)$ for $1\le i\le r$.
    (pp.~178--179.)

    Formalization note (encoding): the data are of the types of \cref{def:I.3-I} and
    \cref{def:I.3-II} with one $\beta$, one $\alpha$ and the same $E_k$ for all the data; $E$ is
    the intersection of the ideal sheaves of the $E_k$; $\nu(j)$ is the order of the original
    $\mathfrak R'_j$ (\cref{def:I.nu}); intersections over an empty family are the whole space.
    Not proved here: left to the reader. -/)
  (latexEnv := "theorem")]
def FundamentalTheorem.III (N : ℕ) : Prop :=
  ∀ (X : Scheme.{u}), IsAmbient X N →
  ∀ (r s α β : ℕ) (E : Fin α → Subscheme X) (V : Fin r → Fin β → Subscheme X)
    (W : Fin r → Subscheme X) (a : Fin s → Fin α → ℕ) (J : Fin s → Subscheme X) (b : Fin s → ℕ)
    (ℜ : Fin r → DatumI.Raw X) (ℜ' : Fin s → DatumII.Raw X),
  (∀ i, ℜ i = { E := ⨅ k, E k, β := β, V := V i, W := W i }) →
  (∀ j, ℜ' j = { α := α, E := E, a := a j, J := J j, b := b j }) →
  (∀ i, (ℜ i).IsDatum) → (∀ j, (ℜ' j).IsDatum) →
  (∀ j, 0 < (ℜ' j).nu) →
  ∃ (Y : Scheme.{u}) (f : MonoidalSuccession X Y),
    f.IsPermissibleForAll ℜ ℜ' ∧
    (IsEmpty Y ∨
      ((⋂ j, (f.transformII (ℜ' j)).sNu (ℜ' j).nu) ∩
        (⋂ i, (f.transformI (ℜ i)).principal.pts) = ∅))

/-! ### Main Theorem III(N, n) and footnote 38 (p. 180) -/

namespace MonoidalSuccession

/-- The properties (a), (b), (c) of Main Theorem III(N, n) (p. 180) of a finite succession of monoidal
transformations `{f_i : X_{i+1} → X_i}` with centers `B_i`, for the sheaves `J = J_0`, `E = E_0` and
the subscheme `W = W_0`; the property (d) is `IsMainIII`.  For the first transformation `f₀` with
center `B₀`: (a) `B₀` is a non-singular irreducible subscheme (possibly empty, p. 163) of `W₀` along
which `W₀` is normally flat; (b) `ν(J₀z) = d₀` for all points `z` of `B₀`, where `d₀` is the maximal
integer attained by `ν(J₀y)` for the points `y` of `W₀`; (c) `E₀` has only normal crossings with `B₀`
(the property (3) of Main Theorem II(N), p. 176); and the rest of the succession has the properties
for the weak transform `J₁` of `J₀`, the reduced subscheme `E₁ = red(f₀⁻¹(E₀ ∪ B₀))`, and the strict
transform `W₁` of `W₀` (the data `J_i`, `E_i`, `W_i` are carried along the succession, as in
`IsMainSuccession`).

Reading (b): the maximal integer `d₀` need not exist when `W₀` is empty; the clause is read as a
condition on the points `z` of `B₀`: for every point `z` of `B₀` (and then `W₀`, containing `B₀`,
is non-empty) the maximum `d₀` exists and `ν(J₀z) = d₀`.  When `B₀` is empty there is no condition. -/
@[blueprint "def:I.4-main-III-steps"
  (statement := /-- The properties (a), (b), (c) of Main Theorem III$(N,n)$ (p.~180) of a succession
    $\{f_i\colon X_{i+1}\to X_i\}$ with centers $B_i$, for $J_0=J$, $E_0=E$, $W_0=W$:
    (a) $B_i$ is a non-singular irreducible subscheme (possibly empty) of $W_i$ along which $W_i$
    is normally flat; (b) $\nu(J_{iz})=d_i$ for all points $z$ of $B_i$, where $d_i$ is the maximal
    integer attained by $\nu(J_{iy})$ for the points $y$ of $W_i$; (c) $E_i$ has only normal
    crossings with $B_i$; where $J_{i+1}$ is the weak transform of $J_i$, $W_{i+1}$ the strict
    transform of $W_i$ and $E_{i+1}=\operatorname{red}(f_i^{-1}(E_i\cup B_i))$.
    Formalization note (encoding): the data $J_i,E_i,W_i$ are carried along the succession, as in
    \cref{thm:I.3-main-II}; in (b) the statement is a condition on the points $z$ of $B_i$, so
    there is none when $B_i$ is empty (in particular when $W_i$ is empty, since $B_i\subseteq W_i$).
    Not proved here: statement only. -/)
  (latexEnv := "definition")]
def IsMainIIISteps : {X Y : Scheme.{u}} → MonoidalSuccession X Y → Subscheme X → Subscheme X →
    Subscheme X → Prop
  | _, _, nil _, _, _, _ => True
  | _, _, cons B t rest, J, E, W =>
      (B.IsCenter ∧ B.IsContainedIn W ∧
        ∀ x ∈ B.pts, Subscheme.IsNormallyFlatAlongAt' W B x) ∧
      (∀ z ∈ B.pts, ∃ d : ℕ,
        IsGreatest ((fun y => Ideal.nu (J.stalkIdeal y)) '' W.pts) (d : ℕ∞) ∧
          Ideal.nu (J.stalkIdeal z) = d) ∧
      E.HasOnlyNormalCrossingsWith B ∧
      rest.IsMainIIISteps (Subscheme.weakTransform t J)
        (Subscheme.totalTransform t.f (E.union B)).radical (Subscheme.strictTransform t W)

/-- The properties (a)–(d) of Main Theorem III(N, n) (p. 180): `IsMainIIISteps` (a), (b), (c) and (d)
"`W_r` is empty", `W_r` being the strict transform of `W` by the whole succession. -/
@[blueprint "def:I.4-main-III-conclusion"
  (statement := /-- The properties (a)--(d) of Main Theorem III$(N,n)$ (p.~180) of a succession:
    (a), (b), (c) as in \cref{def:I.4-main-III-steps} and (d) $W_r$ is empty, where $W_r$ is the
    strict transform of $W$ by the succession. -/)
  (latexEnv := "definition")]
def IsMainIII {X Y : Scheme.{u}} (s : MonoidalSuccession X Y) (J E W : Subscheme X) : Prop :=
  s.IsMainIIISteps J E W ∧ (s.strictTransform W).pts = ∅

/-- `LastStep P s W`: for a succession with at least one transformation, the relation `P B W'`
holds, where `B` is the center of the last transformation `f_{r-1}` and `W'` is the strict
transform `W_{r-1}` of `W` by the succession `f₀, …, f_{r-2}`.  For the empty succession (`r = 0`)
there is no last center and the value is `False`.  Used for footnote 38 (p. 180). -/
@[blueprint "def:I.4-last-step"
  (statement := /-- For a succession $\{f_i\}_{0\le i<r}$ with centers $B_i$, $r\ge1$, and a
    subscheme $W=W_0$, the relation $P(B_{r-1},W_{r-1})$ between the last center and the strict
    transform $W_{r-1}$ of $W$ by $f_0,\dots,f_{r-2}$ (used for footnote~38, p.~180). For $r=0$ the
    value is false: there is no last center. -/)
  (latexEnv := "definition")]
def LastStep (P : ∀ {X : Scheme.{u}}, Subscheme X → Subscheme X → Prop) :
    {X Y : Scheme.{u}} → MonoidalSuccession X Y → Subscheme X → Prop
  | _, _, nil _, _ => False
  | _, _, cons B _ (nil _), W => P B W
  | _, _, cons _ t (cons B' t' rest'), W =>
      LastStep P (cons B' t' rest') (Subscheme.strictTransform t W)

end MonoidalSuccession

namespace MainTheorem

/-- Main Theorem III(N, n) (p. 180): "Let X, J and E be the same as in the main theorem II(N) of § 3,
this chapter.  Let W be a reduced subscheme of dimension n of X.  Then there exists a finite
succession of monoidal transformations {f_i : X_{i+1} → X_i} with centers B_i in X_i, where
0 < i < r [sic] and X = X₀, which has the following properties: (a) If W_i is the strict transform
of W in X_i by the succession of monoidal transformations, then B_i is a non-singular irreducible
subscheme of W_i along which W_i is normally flat, (b) if J_i is the weak transform of J in X_i by
the succession of monoidal transformations, then ν(J_{iz}) = d_i for all the points z of B_i, where
d_i is the maximal integer attained by ν(J_{iy}) with a point y of W_i, (c) the same as (3) of II(N),
§ 3, and (d) W_r is empty."

Left to the reader (p. 180: "The following theorem can be deduced easily from the above theorem
III^N (cf. the deduction of the main theorem II(N) from the fundamental theorem II₂^N)" and "The
details of the proof will be left to the reader"); not proved here.

Deviation (misprint, read from the page image): the printed range of the indices is "0 < i < r";
we read it as `0 ≦ i < r`, as in Main Theorem II(N) (p. 176), since `B₀` is the first center and
`X = X₀`.

Formalization notes (encoding): `X`, `J`, `E` are as in `MainTheorem.II`; `W` is a reduced subscheme
with `W.dim = n`, `n : ℕ` (the empty `W`, `n = -1`, is absent, as in the indexing of the fundamental
theorems); the succession and (a)–(d) are `MonoidalSuccession.IsMainIII`; (c) is the property (3) of
`MonoidalSuccession.IsMainSuccession`, with `E_i` carried along; "a point `y` of `W_i`" is a point
of the support of `W_i`; the reading of (b) when `W_i` is empty is explained at
`MonoidalSuccession.IsMainIIISteps`. -/
@[blueprint "thm:I.4-main-III"
  (statement := /-- \textbf{Main Theorem III$(N,n)$.} Let $X$, $J$ and $E$ be the same as in the
    main theorem II$(N)$ of \S3 (\cref{thm:I.3-main-II}). Let $W$ be a reduced subscheme of
    dimension $n$ of $X$. Then there exists a finite succession of monoidal transformations
    $\{f_i\colon X_{i+1}\to X_i\}$ with centers $B_i$ in $X_i$, where $0\le i<r$ and $X=X_0$,
    which has the following properties: (a) if $W_i$ is the strict transform of $W$ in $X_i$ by
    the succession, then $B_i$ is a non-singular irreducible subscheme of $W_i$ along which $W_i$
    is normally flat; (b) if $J_i$ is the weak transform of $J$ in $X_i$ by the succession, then
    $\nu(J_{iz})=d_i$ for all the points $z$ of $B_i$, where $d_i$ is the maximal integer attained
    by $\nu(J_{iy})$ with a point $y$ of $W_i$; (c) the same as (3) of II$(N)$, \S3; and (d) $W_r$
    is empty. (p.~180.)

    \textbf{Deviation (misprint).} The printed range is ``$0<i<r$''; it is read as $0\le i<r$, as
    in Main Theorem II$(N)$. Formalization note (encoding): as for
    \cref{def:I.4-main-III-steps}; for the empty $W_i$ the condition (b) is on the points of
    $B_i$, so there is none. Not proved here: left to the reader. -/)
  (latexEnv := "theorem")]
def III (N n : ℕ) : Prop :=
  ∀ (X : Scheme.{u}), IsAlgebraicScheme X → X.IsNonsingular → X.dim = (N : WithBot ℕ∞) →
  ∀ (J : Subscheme X), (∀ x, J.stalkIdeal x ≠ ⊥) →
  ∀ (E : Subscheme X), E.IsReduced → E.IsEverywhereCodimOne → E.HasOnlyNormalCrossings →
  ∀ (W : Subscheme X), W.IsReduced → W.dim = (n : WithBot ℕ∞) →
  ∃ (Y : Scheme.{u}) (s : MonoidalSuccession X Y), s.IsMainIII J E W

/-- Footnote 38 (p. 180), attached to the property (d) "W_r is empty" of Main Theorem III(N, n): "This
assertion (d) is equivalent to saying that B_{r−1} ⊇ W_{r−1} (hence, by (a), B_{r−1} = W_{r−1})."

The equivalence is stated without proof (p. 180, footnote 38) and is not proved here; the parenthesis
"hence, by (a), B_{r−1} = W_{r−1}" is argued, from the property (a), and is proved in
`MonoidalSuccession.lastStep_eq_of_isMainIIISteps` (`Hironaka/Ch1/CommentsProofs.lean`).

Formalization notes (encoding): `B ⊇ W'` between subschemes is the containment of ideal sheaves
(p. 165): `W'.IsContainedIn B`; `B = W'` is equality of subschemes.  The statement is: for every
succession satisfying (a), (b), (c) (`IsMainIIISteps`) for the data `J`, `E`, `W` as in
`MainTheorem.III`, (d) holds iff `B_{r−1} ⊇ W_{r−1}`, and in that case `B_{r−1} = W_{r−1}`
(using (a), `B_{r−1} ⊆ W_{r−1}`).  For `r = 0` there is no `B_{r−1}`: `LastStep` is `False` and (d)
fails as well, `W` being non-empty of dimension `n ≧ 0`. -/
@[blueprint "fn:I.4-38"
  (statement := /-- \textbf{Footnote 38.} For a succession as in Main Theorem III$(N,n)$ with the
    properties (a), (b), (c), the assertion (d) ($W_r$ is empty) is equivalent to saying that
    $B_{r-1}\supseteq W_{r-1}$ (hence, by (a), $B_{r-1}=W_{r-1}$). (p.~180.)
    Formalization note (encoding): $\supseteq$ is the containment of ideal sheaves, $B_{r-1}\supseteq
    W_{r-1}$ meaning that the ideal of $B_{r-1}$ is contained in that of $W_{r-1}$; $r\ge1$ (for
    $r=0$ both sides are false). The equivalence is stated without proof (not proved here); the
    parenthesis ``hence, by (a)'' is argued from (a). -/)
  (proof := /-- The equivalence of (d) with $B_{r-1}\supseteq W_{r-1}$ is stated without argument and
    is not proved here. The parenthesis ``hence, by (a), $B_{r-1}=W_{r-1}$'' is proved: (a) gives
    $B_{r-1}\subseteq W_{r-1}$, and with $B_{r-1}\supseteq W_{r-1}$ the two ideal sheaves are
    contained in one another, so they are equal. \textbf{Gap filled:} the induction along the
    succession that reaches the last step, carrying $J_i$, $E_i$, $W_i$, is not printed. -/)
  (latexEnv := "remark")]
def footnote38 (N n : ℕ) : Prop :=
  ∀ (X : Scheme.{u}), IsAlgebraicScheme X → X.IsNonsingular → X.dim = (N : WithBot ℕ∞) →
  ∀ (J : Subscheme X), (∀ x, J.stalkIdeal x ≠ ⊥) →
  ∀ (E : Subscheme X), E.IsReduced → E.IsEverywhereCodimOne → E.HasOnlyNormalCrossings →
  ∀ (W : Subscheme X), W.IsReduced → W.dim = (n : WithBot ℕ∞) →
  ∀ (Y : Scheme.{u}) (s : MonoidalSuccession X Y), s.IsMainIIISteps J E W →
    ((s.strictTransform W).pts = ∅ ↔
      s.LastStep (fun {_} B W' => W'.IsContainedIn B) W) ∧
    (s.LastStep (fun {_} B W' => W'.IsContainedIn B) W →
      s.LastStep (fun {_} B W' => B = W') W)

end MainTheorem

end Hironaka
