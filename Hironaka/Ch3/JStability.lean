/-
Copyright (c) 2026 Daattavya Aggarwal, Minhyong Kim, Oisin Kim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daattavya Aggarwal, Minhyong Kim, Oisin Kim
-/
module

public import Mathlib.Algebra.Module.StablyFree.Basic
public import Mathlib.LinearAlgebra.Dimension.OrzechProperty
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.Coalgebra.IsFrobenius
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.HopfAlgebra.Basic
public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
public import Mathlib.RingTheory.MvPowerSeries.Derivative
public import Mathlib.RingTheory.PicardGroup
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.TotallySplit
public import Architect
public import Hironaka.Ch3.Basic
public import Hironaka.Ch3.NuStar
public import Hironaka.Ch3.TauStar
public import Hironaka.Ch3.Transforms
public import Hironaka.Ch3.Frames
public import Hironaka.Ch3.PermissibleEffects
public import Hironaka.Ch3.FrameTransforms
public import Hironaka.Compat.DerivationExtension
public import Hironaka.Statements

/-!
# Ch. III §9: The notion of J-stability with reference to a local ideal J (pp. 261–265)
# Ch. III §10: The existence of a J-stable regular τ-frame and a J-stable standard base
# (pp. 265–274)

> 9. The notion of J-stability with reference to a local ideal J
>
> Let R be a regular local ring. By a sequence of monoidal transforms of R, we shall mean a
> sequence (finite or infinite) of pairs, say {(R_α, P_{α−1})} (1 ≤ α < e, where e is either a
> positive integer or ∞), which has the following properties: (1) If R₀ denotes R, P_α is a
> non-zero ideal in R_α such that either P_α = R_α or R_α/P_α is regular, for all α ≥ 0, and
> (2) R_α is a monoidal transform of R_{α−1} with center P_{α−1} for every α ≥ 1.
> (pp. 261–262)

> 10. The existence of a J-stable regular τ-frame and a J-stable standard base
>
> Definition 13. Let R be a regular local ring, and J an ideal in R. Let (z) = (z₁, …, z_r) be a
> system of elements of R which can be extended to a regular system of parameters of R. Let us
> assume that (z) is J-stable. …  (p. 265)

Contents, in the paper's order:

* §9, pp. 261–262: sequences of monoidal transforms (`def:III.9-sequence`), sequences of strict
  monoidal transforms and the strict transform of `J` along a sequence
  (`def:III.9-strict-sequence`), permissible sequences (`def:III.9-permissible-sequence`), the
  strict transform of an element (`def:III.9-strict-transform-element`, with the two sentences
  "`J_α` is a principal ideal" `lem:III.9-strict-transform-principal` and "`f_α` is unique only
  up to a unit multiple" `lem:III.9-strict-transform-unique`, the latter proved);
* Definition 11 (p. 262, `def:III.11`); Remarks 1, 2, 3 (pp. 262–264, `rem:III.9-1` (the statement is
  in `Hironaka/Ch3/Remark1.lean`), `rem:III.9-2`, `rem:III.9-3`), with the frame transform along a sequence of Remark 3
  (`def:III.9-frame-transform-along`); Definition 12 (p. 264, `def:III.12`); Theorem 8
  (pp. 264–265, `thm:III.8`) is in `Hironaka/Ch3/JStableStandardBase.lean`;
* §10: Definition 13 (p. 265, `def:III.13`, with its parenthetical note `lem:III.13-extends`);
  Lemma 23 (pp. 267–268, with its geometric interpretation in the docstring), Lemma 24
  (pp. 268–269); Lemma 22 (pp. 265–267) is in `Hironaka/Ch3/JStabilityLemma22.lean`, Lemma 25
  (pp. 269–273) and Theorem 9 (pp. 273–274) are in `Hironaka/Ch3/TauFrameExistence.lean`.

## Encoding

* **Sequences.**  A sequence `{(R_α, P_{α−1})}` of monoidal transforms of `R` is a
  `MonoidalSequence` `S` (§5, `Hironaka/Ch3/PermissibleEffects.lean`) together with a ring
  isomorphism `e : R ≃+* S.ring 0` ("`R₀` denotes `R`").  Condition (2) is built into the
  structure (`S.transform α : MonoidalTransform (S.ring α) (S.center α)`, identified with
  `S.ring (α + 1)` by `S.equiv α`); condition (1) is `S.HasRegularCenters`.  The sequences are
  indexed by `ℕ`: a finite sequence (`e < ∞`) is one whose centers are `R_α` itself from
  `α = e − 1` on (the monoidal transform with center `R_α` being `R_α` itself, p. 209; the paper
  allows `P_α = R_α` anywhere in the sequence, condition (1)).  Accordingly the paper's proviso
  "provided `P_ᾱ` exists and is different from `R_ᾱ`" is `S.center ᾱ ≠ ⊤`.  Since a
  `MonoidalTransform` contains an element `x ≠ 0` of its center, `P_α ≠ (0)` is automatic, and
  condition (1) follows from permissibility (`MonoidalSequence.IsPermissible.hasRegularCenters`,
  proved); it is therefore not repeated in statements about permissible sequences.
* **Strict transforms along a sequence.**  `S.strictAlong I α` is the strict transform of an
  ideal `I` of `R₀` in `R_α` (defined by recursion).  A sequence of strict monoidal transforms of
  `(J, R)` is a sequence `S` with `S.ideal 0 = J.map e` (its `ideal` field is then the sequence of
  the `J_α`, by the field `ideal_succ`; `strictAlong_ideal_zero`, proved).
* **Strict transform of an element.**  `f_α` is a strict transform of `f` in `R_α` iff
  `(f_α) = S.strictAlong ((e f)) α`.  For `α = 0` these are the unit multiples of `f`, whereas the
  paper takes `f₀ = f`; every statement below only involves `ν_{M_α}(f_α)`, `ν_{P_α}(f_α)`,
  `τ_{(z)}(f_α)` and standard bases, which do not change under multiplication by units.
* **`τ*`.**  "`τ*(J') = τ*(J)`" is, as in Lemma 13 (`lem:III.13`) and §5, `t(J') = t(J)` together
  with `τ^{(a)}(J') = τ^{(a)}(J)` for `1 ≤ a ≤ t(J)`.
* **Definition 11** (`IsJStable`) is the `J`-stability used in Ch. IV (`Hironaka/Ch4/ImplicationsAB.lean`).
* **Frame transforms along a sequence** (Remark 3): `MonoidalSequence.FrameTransformAlong`, a
  chain of frame transforms in the sense of §8 (`RegularFrame.FrameTransform`), each frame of
  `(S.transform β).ring` being carried to `S.ring (β + 1)` by `RegularFrame.transport` along
  `S.equiv β`.  `(S.transform β).ring` is a regular local ring by
  `IsRegularLocalRing.of_ringEquiv` (instance `MonoidalSequence.isRegularLocalRing_transform`).
* **Commutative diagrams along two sequences** (Remark 1): `MonoidalSequence.IsLiftAlong`, a
  family of local homomorphisms `R_α → R'_α` each of which is canonical
  (`IsCanonicalLift`, `def:III.2-canonical`) for the monoidal transforms `R_{α+1}`, `R'_{α+1}`.
* That `R → R₁` is a local homomorphism is the instance `MonoidalTransform.isLocalHom_toRing`
  of §2; that a monoidal transform `R₁` of `R` is regular is a hypothesis
  `[IsRegularLocalRing T.ring]` where needed, and `[IsDomain R]` is assumed to form monoidal
  transforms of `R`, as in the other files of Ch. III.
* `ν_P(f)` is `Ideal.ordElem P f`; "complete" is `IsAdicComplete (maximalIdeal R) R`; "the residue
  field has characteristic zero" is `CharZero (ResidueField R)`; "perfect" is `PerfectField`.

## Notes on the printed text

The printed text is read as follows (inequalities, bars, primes and indices): p. 261 "`1 ≤ α < e`"; p. 262 "for all `α ≥ 0`", "for every `ᾱ ≥ 0`",
"`1 ≤ a ≤ t(J) = t(J_ᾱ)`", "`J_ᾱ = J` if `ᾱ = 0`", "`ν_{M_ᾱ}(f_ᾱ) = ν` and `ν_{P_ᾱ}(f_ᾱ) = ν`
(provided `P_ᾱ` exists and is different from `R_ᾱ`)", "`f₀ = f`"; p. 263 "`τ*(J_ᾱ) = τ*(J)`",
"`P₀ ⊇ (z₁, …, z_r)R`", "an index `ᾱ (≥ 1)`", "`β ≤ ᾱ`"; p. 264 the frame of Theorem 8 is
written `(S; z₁, …, z_τ)`, "`ν_P(f_j) = ν_j`", "`S^{(a)} = S{z_{τ_a+1}, …, z_τ}`"; p. 265 Lemma 22
"`f = x^ν + g₂x^{ν−2} + … + g_ν (ν > 0)`", "`ν_{PR_P}(f) ≥ ν`"; p. 267 Lemma 23 "`F₀ = F/X₀^ν`"
(with the exponent), "`ν_{NA_N}(F₀) ≥ ν`"; p. 268 Lemma 24 "`(y₁, …, y_τ)`",
"`f̄ = f x^{−ν}`", "(iii) `z̄_j ∈ M₁`", "`ȳ_i ∈ M₁` for all `i (1 ≤ i ≤ τ)`"; p. 269 Lemma 25
"If `τ_{(z)}(f) ≥ 1`" (not `>`), "(2) `τ_{(z,w)}(f) = τ_{(z)}(f) − 1`"; p. 273 Theorem 9
"(3) `τ_{(z)}(f_j) = 0 (1 ≤ j ≤ i − 1)`, and `τ(f₁, …, f_i) = r + τ_{(z)}(f_i)`", "(A) If
`τ_{(z)}(f_i) > 0`" (not `f_j`).

## Misprints of the printed text (marked [sic] in the proof texts)

* p. 262 (twice): "`{R_α, P_{α−1})}`" (unbalanced parenthesis).
* p. 263 (Remark 1): "`P'_{α−1} = P_{α−1}R'`" — read `P_{α−1}R'_{α−1}`; "`J' = JR`" — read
  `J' = JR'`.
* p. 263 (Remark 3): "`(S, z₁, …, z_r)` admits a frame transform" (comma for semicolon).
* p. 264: a stray prime in "`z_r^{'(β)}`"; "`(S_{x̄}; z₁^{(ᾱ)}, …, z_r^{(ᾱ)})`" — read `S_ᾱ`;
  "can be extend to a standard base" — read "extended".
* p. 265 (Definition 13): "regular systen of parameters"; a missing "and" before
  "`τ_{(z^{(ᾱ)})}(f^{(ᾱ)}) = τ_{(z)}(f)`".
* p. 269 (proof of Lemma 24): "`φ` is viewed as a form in `Z₁, …, Z_r, X, Y₁, …, Y_r`" — read
  `Y_{τ−1}`.
* p. 271 (proof of Lemma 25, (c)(ii)): "if `f̄ = x^{−ν}f`" — read `y^{−ν}f` (the denominator is
  called `y` in (c)).
* p. 272: "`w̄^e + p̄₂w̄^{e−2} + ⋯ p̄_e`" (a `+` is missing); on p. 273 the initial forms of
  `y, x_j` in `gr_{M₁}(R₁)` are written `Ȳ, X̄_j`, on p. 272 `Y, X_j` (transcribed as printed).
-/

@[expose] public section

open IsLocalRing

namespace Hironaka

universe u

attribute [local instance] RegularFrame.isDomain_S

/-! ### Sequences of monoidal transforms (pp. 261–262) -/

namespace MonoidalSequence

variable (S : MonoidalSequence.{u})

/-- The underlying local ring of the `α`-th monoidal transform of a sequence is `R_{α+1}` up to
the isomorphism `S.equiv α`, hence a regular local ring. -/
instance isRegularLocalRing_transform (n : ℕ) : IsRegularLocalRing (S.transform n).ring :=
  IsRegularLocalRing.of_ringEquiv (S.equiv n).symm

/-- pp. 261–262: "By a *sequence of monoidal transforms of `R`*, we shall mean a sequence (finite
or infinite) of pairs, say `{(R_α, P_{α−1})}` (`1 ≤ α < e`, where `e` is either a positive integer
or `∞`), which has the following properties: (1) If `R₀` denotes `R`, `P_α` is a non-zero ideal in
`R_α` such that either `P_α = R_α` or `R_α/P_α` is regular, for all `α ≥ 0`, and (2) `R_α` is a
monoidal transform of `R_{α−1}` with center `P_{α−1}` for every `α ≥ 1`."

A sequence of monoidal transforms of `R` is a `MonoidalSequence` `S` with an isomorphism
`R ≃+* S.ring 0` which satisfies this predicate, condition (1).  (Formalization notes: condition
(2) is part of the structure `MonoidalSequence`; the sequence is indexed by `ℕ`, a finite sequence
being continued by the trivial monoidal transforms with center `R_α` (p. 209), see the module
docstring; "`R_α/P_α` is regular" includes that `P_α` is prime, a regular local ring being a
domain.) -/
@[blueprint "def:III.9-sequence"
  (statement := /-- Let $R$ be a regular local ring. A \emph{sequence of monoidal transforms of
    $R$} is a sequence (finite or infinite) of pairs $\{(R_\alpha,P_{\alpha-1})\}$
    ($1\le\alpha<e$, where $e$ is either a positive integer or $\infty$) with the following
    properties: (1) if $R_0$ denotes $R$, $P_\alpha$ is a non-zero ideal in $R_\alpha$ such that
    either $P_\alpha=R_\alpha$ or $R_\alpha/P_\alpha$ is regular, for all $\alpha\ge0$, and (2)
    $R_\alpha$ is a monoidal transform of $R_{\alpha-1}$ with center $P_{\alpha-1}$
    (\cref{def:III.2-monoidal-transform}) for every $\alpha\ge1$. (pp.~261--262.)

    (Formalization note: the sequences are indexed by all $\alpha\ge0$; a finite sequence is
    continued by the monoidal transforms with center $P_\alpha=R_\alpha$, which are $R_\alpha$
    itself (p.~209), so that ``$P_{\bar\alpha}$ exists and is different from $R_{\bar\alpha}$''
    becomes ``$P_{\bar\alpha}\ne R_{\bar\alpha}$''. Condition (2) is built into the data;
    condition (1) is the predicate recorded here.) -/)
  (latexEnv := "definition")]
def HasRegularCenters : Prop :=
  ∀ n, S.center n ≠ ⊥ ∧
    (S.center n = ⊤ ∨ ((S.center n).IsPrime ∧ IsRegularLocalRing (S.ring n ⧸ S.center n)))

/-- p. 262: "Let `J` be an ideal in `R`. By a *sequence of strict monoidal transforms of*
`(J, R)`, we shall mean a sequence of triples, say `{(J_α, R_α, P_{α−1})}` (`1 ≤ α < e`, where `e`
is either a positive integer or `∞`), such that `{(R_α, P_{α−1})}` is a sequence of monoidal
transforms of `R` and that, if `J₀` denotes `J`, `J_α` is the strict transform of `J_{α−1}` in `R_α`
for every `α ≥ 1`. If `{(J_α, R_α, P_{α−1})}` is such, we shall say that, for each `α ≥ 1`, `J_α` is
*the strict transform of `J` in `R_α` along the sequence of monoidal transforms*
`{(R_α, P_{α−1})}` of `R`."

The sequence `S` (with `R ≃+* S.ring 0`) is a sequence of strict monoidal transforms of `(J, R)`,
its field `S.ideal α` being `J_α`, iff it satisfies condition (1) and `J₀ = J`; the relation
"`J_α` is the strict transform of `J_{α−1}`" is the field `S.ideal_succ`. -/
@[blueprint "def:III.9-strict-sequence"
  (statement := /-- Let $J$ be an ideal in $R$. A \emph{sequence of strict monoidal transforms
    of $(J,R)$} is a sequence of triples $\{(J_\alpha,R_\alpha,P_{\alpha-1})\}$ ($1\le\alpha<e$,
    where $e$ is either a positive integer or $\infty$) such that $\{(R_\alpha,P_{\alpha-1})\}$ is
    a sequence of monoidal transforms of $R$ (\cref{def:III.9-sequence}) and that, if $J_0$
    denotes $J$, $J_\alpha$ is the strict transform of $J_{\alpha-1}$ in $R_\alpha$
    (\cref{def:III.5-strict}) for every $\alpha\ge1$. If $\{(J_\alpha,R_\alpha,P_{\alpha-1})\}$
    is such, we say that, for each $\alpha\ge1$, $J_\alpha$ is \emph{the strict transform of $J$
    in $R_\alpha$ along the sequence of monoidal transforms} $\{(R_\alpha,P_{\alpha-1})\}$ of
    $R$. (p.~262.)

    (Formalization note: the data of a sequence of monoidal transforms carry a sequence of
    ideals $J_\alpha$ with $J_\alpha$ the strict transform of $J_{\alpha-1}$; the sequence is one
    of strict monoidal transforms of $(J,R)$ iff condition (1) holds and $J_0$ corresponds to
    $J$ under the identification $R=R_0$. For any ideal $I$ of $R_0$ the strict transform
    $I_\alpha$ of $I$ in $R_\alpha$ along the sequence is defined by recursion: $I_0=I$ and
    $I_\alpha$ = the strict transform of $I_{\alpha-1}$ in $R_\alpha$
    (\cref{def:III.5-strict}).) -/)
  (latexEnv := "definition")]
def IsStrictSequenceOf {R : Type u} [CommRing R] (J : Ideal R) (e : R ≃+* S.ring 0) : Prop :=
  S.HasRegularCenters ∧ S.ideal 0 = J.map e

/-- p. 262: "`J_α` is the strict transform of `J_{α−1}` in `R_α` for every `α ≥ 1`": the strict
transform `I_α` of an ideal `I` of `R₀` in `R_α` along the sequence, by recursion on `α`
(Definition 5, `strictTransformIdeal`, moved to `R_{α+1}` along `S.equiv α`). -/
@[blueprint "def:III.9-strict-sequence"
  (statement := /-- Let $\{(R_\alpha,P_{\alpha-1})\}$ be a sequence of monoidal transforms of
    $R$ (\cref{def:III.9-sequence}) and $I$ an ideal in $R_0$. The \emph{strict transform}
    $I_\alpha$ of $I$ in $R_\alpha$ along the sequence is defined by $I_0=I$ and $I_\alpha$ = the
    strict transform of $I_{\alpha-1}$ in $R_\alpha$ (\cref{def:III.5-strict}) for $\alpha\ge1$.
    (p.~262.) -/)
  (latexEnv := "definition")]
noncomputable def strictAlong (I : Ideal (S.ring 0)) : ∀ n, Ideal (S.ring n)
  | 0 => I
  | n + 1 => (strictTransformIdeal (S.transform n) (strictAlong I n)).map (S.equiv n)

/-- The ideals `J_α` carried by a sequence are the strict transforms of `J₀` along it. -/
theorem strictAlong_ideal_zero (n : ℕ) : S.strictAlong (S.ideal 0) n = S.ideal n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [strictAlong, ih, S.ideal_succ n]

/-- p. 262: "We shall say that a sequence of monoidal transforms `{(R_α, P_{α−1})}` of `R` *is
permissible for* `J` if `P_{α−1}` is a permissible center for `J_{α−1}` for every `α ≥ 1`, where
`J₀ = J`, and `J_α` is the strict monoidal transform of `J` in `R_α` along the sequence. If this
is the case, we shall also say that the sequence of strict monoidal transforms
`{(J_α, R_α, P_{α−1})}` of `(J, R)` is permissible."

The second sentence is `MonoidalSequence.IsPermissible` of §5 (each `P_α` is a permissible center
for the ideal `J_α` carried by the sequence); the two notions agree by
`isPermissibleFor_iff_isPermissible`. -/
@[blueprint "def:III.9-permissible-sequence"
  (statement := /-- A sequence of monoidal transforms $\{(R_\alpha,P_{\alpha-1})\}$ of $R$
    (\cref{def:III.9-sequence}) is \emph{permissible for} $J$ if $P_{\alpha-1}$ is a permissible
    center for $J_{\alpha-1}$ (\cref{def:III.8}) for every $\alpha\ge1$, where $J_0=J$ and
    $J_\alpha$ is the strict monoidal transform of $J$ in $R_\alpha$ along the sequence
    (\cref{def:III.9-strict-sequence}). If this is the case, we also say that the sequence of
    strict monoidal transforms $\{(J_\alpha,R_\alpha,P_{\alpha-1})\}$ of $(J,R)$ is
    permissible. (p.~262.) -/)
  (latexEnv := "definition")]
def IsPermissibleFor {R : Type u} [CommRing R] (J : Ideal R) (e : R ≃+* S.ring 0) : Prop :=
  ∀ n, IsPermissibleCenter (S.ring n) (S.strictAlong (J.map e) n) (S.center n)

/-- For a sequence of strict monoidal transforms of `(J, R)`, "permissible for `J`" is the
permissibility `MonoidalSequence.IsPermissible` of §5. -/
theorem isPermissibleFor_iff_isPermissible {R : Type u} [CommRing R] (J : Ideal R)
    (e : R ≃+* S.ring 0) (h0 : S.ideal 0 = J.map e) :
    S.IsPermissibleFor J e ↔ S.IsPermissible := by
  unfold IsPermissibleFor IsPermissible
  rw [← h0]
  simp only [strictAlong_ideal_zero]

/-- Condition (1) of a sequence of monoidal transforms (p. 262) is implied by permissibility:
a monoidal transform has an element `x ≠ 0` of its center, and a permissible center is either
`R_α` or a prime `P_α` with `R_α/P_α` regular (Definition 8). -/
theorem IsPermissible.hasRegularCenters {S : MonoidalSequence.{u}} (h : S.IsPermissible) :
    S.HasRegularCenters := by
  intro n
  have key : ∀ P : Ideal (S.ring n), P = ⊥ → (S.transform n).x ∈ P → (S.transform n).x = 0 := by
    rintro P rfl hx
    exact Ideal.mem_bot.mp hx
  refine ⟨fun hbot => (S.transform n).x_ne_zero (key _ hbot (S.transform n).x_mem), ?_⟩
  rcases h n with htop | ⟨hP, -, hreg, -⟩
  · exact Or.inl htop
  · exact Or.inr ⟨hP, hreg⟩

/-- p. 262: "Let `f` be a non-zero element of `R`. If `J = (f)R`, and if `{(J_α, R_α, P_{α−1})}` is
a sequence of strict monoidal transforms of `(J, R)`, then `J_α` is a principal ideal of `R_α`, for
every `α ≥ 1`. A generator `f_α` of the principal ideal `J_α` will be called a *strict transform
of the element `f` in `R_α` along the sequence of monoidal transforms* `{(R_α, P_{α−1})}` of `R`."

(Formalization note: the relation "`f_α` is a strict transform of `f` in `R_α`", for an element
`f` of `R` and the sequence `S` with `R ≃+* S.ring 0`; for `α = 0` it says that `f₀` is a unit
multiple of `f`.) -/
@[blueprint "def:III.9-strict-transform-element"
  (statement := /-- Let $f$ be a non-zero element of $R$. If $J=(f)R$ and
    $\{(J_\alpha,R_\alpha,P_{\alpha-1})\}$ is a sequence of strict monoidal transforms of $(J,R)$
    (\cref{def:III.9-strict-sequence}), then $J_\alpha$ is a principal ideal of $R_\alpha$ for
    every $\alpha\ge1$ (\cref{lem:III.9-strict-transform-principal}). A generator $f_\alpha$ of
    the principal ideal $J_\alpha$ is called a \emph{strict transform of the element $f$ in
    $R_\alpha$ along the sequence of monoidal transforms} $\{(R_\alpha,P_{\alpha-1})\}$ of $R$.
    (p.~262.)

    (Formalization note: $f_\alpha$ is a strict transform of $f$ iff $(f_\alpha)R_\alpha$ is the
    strict transform of $(f)R$ in $R_\alpha$ along the sequence; for $\alpha=0$ this means that
    $f_0$ is a unit multiple of $f$, the paper taking $f_0=f$.) -/)
  (latexEnv := "definition")]
def IsStrictTransformElem {R : Type u} [CommRing R] (e : R ≃+* S.ring 0) (f : R) (n : ℕ)
    (fn : S.ring n) : Prop :=
  Ideal.span {fn} = S.strictAlong (Ideal.span {e f}) n

/-- The canonical map `R → R'` of a monoidal transform is injective. -/
theorem toRing_injective_aux {R : Type u} [CommRing R] [IsRegularLocalRing R]
    [IsDomain R] {P : Ideal R} (t : MonoidalTransform R P) : Function.Injective t.toRing := by
  have h1 : Function.Injective (algebraMap R (blowupAlgebra R P t.x)) := by
    intro a b hab
    have := congrArg (fun y : blowupAlgebra R P t.x => (y : FractionRing R)) hab
    simp only [Subalgebra.coe_algebraMap] at this
    exact IsFractionRing.injective R (FractionRing R) this
  have h2 : Function.Injective (algebraMap (blowupAlgebra R P t.x) t.ring) :=
    IsLocalization.injective t.ring (Ideal.primeCompl_le_nonZeroDivisors t.M')
  exact h2.comp h1

/-- `g ∈ I ^ ν_I(g)` (with `ν_I(g) = ∞` read as `0`). -/
private theorem mem_pow_toNat_ordElem_aux {A : Type*} [CommRing A] (I : Ideal A) (g : A) :
    g ∈ I ^ (Ideal.ordElem I g).toNat := by
  by_cases h : Ideal.ordElem I g = ⊤
  · rw [h, ENat.toNat_top, pow_zero, Ideal.one_eq_top]
    exact Submodule.mem_top
  · exact Ideal.mem_pow_of_ordElem (ENat.natCast_toNat h).symm

/-- If `(x)R' = PR'` and `g ∈ Pⁿ`, then `g = xⁿ c` in `R'`. -/
theorem exists_mul_pow_eq_toRing_aux {R : Type u} [CommRing R] [IsRegularLocalRing R]
    [IsDomain R] {P : Ideal R} (t : MonoidalTransform R P) {x : R}
    (hxP : Ideal.span {t.toRing x} = P.map t.toRing) {n : ℕ} {g : R} (hg : g ∈ P ^ n) :
    ∃ c, t.toRing x ^ n * c = t.toRing g := by
  have hmem : t.toRing g ∈ (P ^ n).map t.toRing := Ideal.mem_map_of_mem _ hg
  rw [Ideal.map_pow, ← hxP, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at hmem
  obtain ⟨c, hc⟩ := hmem
  exact ⟨c, hc.symm⟩

/-- `PR' = R'` for a monoidal transform with center `P = R`. -/
theorem map_eq_top_of_eq_top_aux {R : Type u} [CommRing R] [IsRegularLocalRing R]
    [IsDomain R] {P : Ideal R} (t : MonoidalTransform R P) (hP : P = ⊤) :
    P.map t.toRing = ⊤ := by
  have h1 : (1 : R) ∈ P := hP ▸ Submodule.mem_top
  rw [Ideal.eq_top_iff_one, ← map_one t.toRing]
  exact Ideal.mem_map_of_mem _ h1

/-- The strict transform of an ideal `I` with center `P = R` is `IR'` (Definition 5: the
generators `x^{-ν} f` have `x` a unit). -/
theorem strictTransformIdeal_eq_map_of_eq_top_aux {R : Type u} [CommRing R]
    [IsRegularLocalRing R] [IsDomain R] {P : Ideal R} (t : MonoidalTransform R P) (hP : P = ⊤)
    (I : Ideal R) : strictTransformIdeal t I = I.map t.toRing := by
  have htop := map_eq_top_of_eq_top_aux t hP
  apply le_antisymm
  · rw [strictTransformIdeal, Ideal.span_le]
    rintro y ⟨x, hx, f, hf, ν, -, hy⟩
    rw [htop, Ideal.span_singleton_eq_top] at hx
    obtain ⟨u, rfl⟩ := hx
    have hy' : y = ↑(u⁻¹) ^ ν * t.toRing f := by
      rw [← hy, ← mul_assoc, ← mul_pow, Units.inv_mul, one_pow, one_mul]
    rw [SetLike.mem_coe, hy']
    exact Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _ hf)
  · rw [Ideal.map_le_iff_le_comap]
    intro f hf
    rw [Ideal.mem_comap]
    exact Ideal.subset_span ⟨1, by rw [htop, Ideal.span_singleton_one], f, hf, 0, by simp,
      by simp⟩

/-- A monoidal transform with center `P = R` is `R` itself (p. 209): `R → R'` is bijective. -/
theorem toRing_bijective_of_eq_top_aux {R : Type u} [CommRing R] [IsRegularLocalRing R]
    [IsDomain R] {P : Ideal R} (t : MonoidalTransform R P) (hP : P = ⊤) :
    Function.Bijective t.toRing := by
  refine ⟨toRing_injective_aux t, fun y => ?_⟩
  have h1 : (1 : R) ∈ P := hP ▸ Submodule.mem_top
  have hx0 : algebraMap R (FractionRing R) t.x ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective R (FractionRing R))).mpr t.x_ne_zero
  -- `x` is a unit of `R`: otherwise `1 = x · (1/x) ∈ M'`
  have hxu : IsUnit t.x := by
    by_contra hx
    have hxM : t.x ∈ maximalIdeal R := hx
    let q : blowupAlgebra R P t.x := ⟨algebraMap R (FractionRing R) 1 /
      algebraMap R (FractionRing R) t.x, Algebra.subset_adjoin ⟨1, h1, rfl⟩⟩
    have hq : algebraMap R (blowupAlgebra R P t.x) t.x * q = 1 := by
      apply Subtype.ext
      simp only [MulMemClass.coe_mul, Subalgebra.coe_algebraMap, map_one, OneMemClass.coe_one, q]
      field_simp
    have hmem : algebraMap R (blowupAlgebra R P t.x) t.x ∈ t.M' :=
      t.le (Ideal.mem_map_of_mem _ hxM)
    have h1M : (1 : blowupAlgebra R P t.x) ∈ t.M' := hq ▸ t.M'.mul_mem_right q hmem
    exact t.isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr h1M)
  obtain ⟨v, hv⟩ := hxu
  -- every element of `R[x⁻¹P]` comes from `R`
  have hA : ∀ a : blowupAlgebra R P t.x, ∃ r : R, algebraMap R _ r = a := by
    intro a
    have hle : blowupAlgebra R P t.x ≤ (⊥ : Subalgebra R (FractionRing R)) := by
      rw [blowupAlgebra, Algebra.adjoin_le_iff]
      rintro _ ⟨p, -, rfl⟩
      refine Algebra.mem_bot.mpr ⟨p * ↑v⁻¹, ?_⟩
      rw [map_mul, eq_div_iff hx0, mul_assoc, ← map_mul, ← hv, Units.inv_mul, map_one, mul_one]
    obtain ⟨r, hr⟩ := Algebra.mem_bot.mp (hle a.2)
    exact ⟨r, Subtype.ext (by simpa using hr)⟩
  obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective t.M'.primeCompl y
  obtain ⟨ra, hra⟩ := hA a
  obtain ⟨rs, hrs⟩ := hA s
  have hrsu : IsUnit rs := by
    by_contra hns
    exact s.2 (hrs ▸ t.le (Ideal.mem_map_of_mem _ (show rs ∈ maximalIdeal R from hns)))
  obtain ⟨w, hw⟩ := hrsu
  refine ⟨ra * ↑w⁻¹, ?_⟩
  rw [eq_comm, IsLocalization.mk'_eq_iff_eq_mul, MonoidalTransform.toRing, RingHom.comp_apply,
    ← map_mul, ← hra, ← hrs, ← map_mul, ← hw, mul_assoc, Units.inv_mul, mul_one]

/-- The strict transform of a principal ideal `(g)R` with center `P = R` is `(g)R'`. -/
private theorem strictTransformIdeal_span_singleton_of_eq_top_aux {R : Type u} [CommRing R]
    [IsRegularLocalRing R] [IsDomain R] {P : Ideal R} (t : MonoidalTransform R P) (hP : P = ⊤)
    (g : R) : strictTransformIdeal t (Ideal.span {g}) = Ideal.span {t.toRing g} := by
  rw [strictTransformIdeal_eq_map_of_eq_top_aux t hP, Ideal.map_span, Set.image_singleton]

/-- The strict transform of a principal ideal `(g)R` with a center `P` with `R/P` regular is
generated by `x^{-ν} g`, `ν = ν_P(g)` (Lemma 6,
`MonoidalTransform.strictTransformIdeal_eq_span_of_span_initialForm_eq_grIdeal`, with the
one-element system `(g)`: `gr_P(R)` is a domain, so `gr_P((g)R, R)` is generated by the initial
form of `g`). -/
theorem strictTransformIdeal_span_singleton_aux {R : Type u} [CommRing R]
    [IsRegularLocalRing R] [IsDomain R] {P : Ideal R} (t : MonoidalTransform R P)
    (hP : P.IsPrime) (hS : IsRegularLocalRing (R ⧸ P)) (g x : R) (hx : x ∈ P)
    (hxP : Ideal.span {t.toRing x} = P.map t.toRing) (g' : t.ring)
    (hg' : t.toRing x ^ (Ideal.ordElem P g).toNat * g' = t.toRing g) :
    strictTransformIdeal t (Ideal.span {g}) = Ideal.span {g'} := by
  have hX0 : t.toRing x ≠ 0 := by
    intro h0
    have hmem : t.toRing t.x ∈ P.map t.toRing := Ideal.mem_map_of_mem _ t.x_mem
    rw [← hxP, h0, Ideal.span_singleton_eq_bot.mpr rfl, Ideal.mem_bot, ← map_zero t.toRing] at hmem
    exact t.x_ne_zero (toRing_injective_aux t hmem)
  have hgen : Ideal.span (Set.range fun _ : Fin 1 => initialForm P g) =
      grIdeal P (Ideal.span {g}) := by
    apply le_antisymm
    · rw [Ideal.span_le]
      rintro _ ⟨_, rfl⟩
      exact Ideal.subset_span ⟨g, Ideal.mem_span_singleton_self g, rfl⟩
    · rw [grIdeal, Ideal.span_le]
      rintro _ ⟨a, ha, rfl⟩
      obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp ha
      rw [SetLike.mem_coe, initialForm_mul_of_isRegularLocalRing P hS]
      exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨0, rfl⟩)
  rw [MonoidalTransform.strictTransformIdeal_eq_span_of_span_initialForm_eq_grIdeal hP hS
    (Ideal.span {g}) (fun _ : Fin 1 => g)
    (fun _ => Ideal.mem_span_singleton_self g) hgen t x hx hxP]
  congr 1
  ext y
  simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff, exists_const]
  exact ⟨fun h => mul_left_cancel₀ (pow_ne_zero _ hX0) (h.trans hg'.symm), fun h => h ▸ hg'⟩

/-- Explicit generators of the principal ideals `J_α` (`strictAlong_span_singleton_isPrincipal`):
one step at a time, with Lemma 6 for a prime center and `J_{α+1} = J_αR_{α+1}` for the center
`R_α`. -/
theorem exists_strictAlong_span_singleton_eq_aux {R : Type u} [CommRing R]
    (e : R ≃+* S.ring 0) (hS : S.HasRegularCenters) (f : R) (k : ℕ) :
    ∃ a : S.ring k, S.strictAlong (Ideal.span {e f}) k = Ideal.span {a} := by
  induction k with
  | zero => exact ⟨e f, rfl⟩
  | succ k ih =>
    obtain ⟨a, ha⟩ := ih
    have key : ∃ b, strictTransformIdeal (S.transform k) (Ideal.span {a}) = Ideal.span {b} := by
      rcases (hS k).2 with htop | ⟨hP, hreg⟩
      · exact ⟨_, strictTransformIdeal_span_singleton_of_eq_top_aux _ htop a⟩
      · have hxP : Ideal.span {(S.transform k).toRing (S.transform k).x} =
            (S.center k).map (S.transform k).toRing := (S.transform k).span_xR_eq_map
        obtain ⟨b, hb⟩ := exists_mul_pow_eq_toRing_aux (S.transform k) hxP
          (mem_pow_toNat_ordElem_aux (S.center k) a)
        exact ⟨b, strictTransformIdeal_span_singleton_aux _ hP hreg a _
          (S.transform k).x_mem hxP b hb⟩
    obtain ⟨b, hb⟩ := key
    refine ⟨S.equiv k b, ?_⟩
    rw [strictAlong, ha, hb, Ideal.map_span, Set.image_singleton]

/-- p. 262: "If `J = (f)R`, and if `{(J_α, R_α, P_{α−1})}` is a sequence of strict monoidal
transforms of `(J, R)`, then `J_α` is a principal ideal of `R_α`, for every `α ≥ 1`."  (`f ≠ 0`;
"sequence of strict monoidal transforms" includes condition (1), `HasRegularCenters`.) -/
@[blueprint "lem:III.9-strict-transform-principal"
  (statement := /-- Let $f$ be a non-zero element of $R$, $J=(f)R$, and
    $\{(J_\alpha,R_\alpha,P_{\alpha-1})\}$ a sequence of strict monoidal transforms of $(J,R)$
    (\cref{def:III.9-strict-sequence}). Then $J_\alpha$ is a principal ideal of $R_\alpha$ for
    every $\alpha\ge1$. (p.~262.) -/)
  (proof := /-- Stated without proof in the paper. [Editorial gloss, not in the paper: by
    induction on $\alpha$ it suffices to treat one monoidal transform $R_1$ of $R$ with center
    $P$ and $J=(f)R$, $f\ne0$. If $P=R$ then $J_1=JR_1$. Otherwise $R/P$ is regular, so
    $\operatorname{gr}_P(R)$ is a polynomial ring over $R/P$, hence a domain, and
    $\operatorname{gr}_P(J,R)$ is generated by the initial form of $f$; by Lemma~6 of \S2
    (\cref{lem:III.6}) the strict transform $J_1$ is generated by $x^{-\nu}f$ with
    $\nu=\nu_P(f)$ and $(x)R_1=PR_1$.] -/)
  (latexEnv := "lemma")]
theorem strictAlong_span_singleton_isPrincipal {R : Type u} [CommRing R] (e : R ≃+* S.ring 0)
    (hS : S.HasRegularCenters) (f : R) (hf : f ≠ 0) (n : ℕ) (hn : 1 ≤ n) :
    (S.strictAlong (Ideal.span {e f}) n).IsPrincipal := by
  -- (the hypotheses `f ≠ 0` and `n ≥ 1` are not needed)
  have _ := hf
  have _ := hn
  obtain ⟨a, ha⟩ := exists_strictAlong_span_singleton_eq_aux S e hS f n
  exact ⟨⟨a, ha⟩⟩

/-- p. 262: "Note that `f_α` is unique only up to a unit multiple in `R_α`." (`R_α` is a domain.) -/
@[blueprint "lem:III.9-strict-transform-unique"
  (statement := /-- A strict transform $f_\alpha$ of $f$ in $R_\alpha$ along a sequence of
    monoidal transforms (\cref{def:III.9-strict-transform-element}) is unique only up to a unit
    multiple in $R_\alpha$: if $f_\alpha$ and $f'_\alpha$ are strict transforms of $f$ in
    $R_\alpha$, then $f'_\alpha=uf_\alpha$ with a unit $u$ of $R_\alpha$. (p.~262.) -/)
  (proof := /-- Both $f_\alpha$ and $f'_\alpha$ generate the same principal ideal of the domain
    $R_\alpha$, hence are associated. -/)
  (latexEnv := "lemma")]
theorem IsStrictTransformElem.unique {R : Type u} [CommRing R] {e : R ≃+* S.ring 0} {f : R}
    {n : ℕ} {fn fn' : S.ring n} (h : S.IsStrictTransformElem e f n fn)
    (h' : S.IsStrictTransformElem e f n fn') : ∃ u : (S.ring n)ˣ, fn' = u * fn := by
  obtain ⟨u, hu⟩ := Ideal.span_singleton_eq_span_singleton.mp (h.trans h'.symm)
  exact ⟨u, by rw [← hu, mul_comm]⟩

end MonoidalSequence

/-! ### Definition 11 (p. 262) -/

section Definition11

variable {R : Type u} [CommRing R] [IsRegularLocalRing R]

/-- Definition 11, p. 262: "Let `R` be a regular local ring, and `J` an ideal in `R`. Let `f` be an
element of `R`. Let `M` be the maximal ideal of `R` and `ν = ν_M(f)`. We say that `f` is
*`J`-stable* (or, stable with respect to `J`) if the following condition is satisfied: Let
`{(R_α, P_{α−1})}` be any permissible sequence (finite or infinite) of monoidal transforms of `R`
for `J` such that `R_α` is residually separable algebraic over `R_{α−1}` (`= R` if `α = 1`). Let
`J_α` be the strict transform of `J` in `R_α` along the sequence, and `f_α` a strict transform of
`f` in `R_α` along the sequence. Then, for every `ᾱ ≥ 0`, such that `ν*(J_ᾱ) = ν*(J)` and that
`τ^{(a)}(J_ᾱ) = τ^{(a)}(J)` for `1 ≤ a ≤ t(J) = t(J_ᾱ)` (where `J_ᾱ = J` if `ᾱ = 0`), we have
`ν_{M_ᾱ}(f_ᾱ) = ν` and `ν_{P_ᾱ}(f_ᾱ) = ν` (provided `P_ᾱ` exists and is different from `R_ᾱ`),
where `M_ᾱ` denotes the maximal ideal of `R_ᾱ` and `f₀ = f`."

(Formalization notes.
* The sequence is a `MonoidalSequence` `Sq` with `e : R ≃+* Sq.ring 0` and `J₀ = J`
  (`Sq.ideal 0 = J.map e`); its field `Sq.ideal α` is then `J_α`.  Permissibility for `J` is
  `Sq.IsPermissible` (`isPermissibleFor_iff_isPermissible`), which implies condition (1) of a
  sequence of monoidal transforms (`IsPermissible.hasRegularCenters`).
* Finite sequences are continued by trivial monoidal transforms (module docstring), so that
  "`P_ᾱ` exists and is different from `R_ᾱ`" is `Sq.center ᾱ ≠ ⊤`.
* `f_ᾱ` ranges over all strict transforms of `f` in `R_ᾱ` (all unit multiples of one another;
  for `ᾱ = 0` the unit multiples of `f`, the paper's `f₀ = f`), which does not change the
  orders `ν_{M_ᾱ}`, `ν_{P_ᾱ}`.
* The hypothesis `t(J) = t(J_ᾱ)` of the printed text is kept.
* This is the `J`-stability used in Ch. IV (`Hironaka/Ch4/ImplicationsAB.lean`).) -/
@[blueprint "def:III.11"
  (statement := /-- Let $R$ be a regular local ring, and $J$ an ideal in $R$. Let $f$ be an
    element of $R$. Let $M$ be the maximal ideal of $R$ and $\nu=\nu_M(f)$. We say that $f$ is
    \emph{$J$-stable} (or, stable with respect to $J$) if the following condition is satisfied:
    Let $\{(R_\alpha,P_{\alpha-1})\}$ be any permissible sequence (finite or infinite) of
    monoidal transforms of $R$ for $J$ (\cref{def:III.9-permissible-sequence}) such that
    $R_\alpha$ is residually separable algebraic over $R_{\alpha-1}$ ($=R$ if $\alpha=1$)
    (\cref{def:III.2-residually}). Let $J_\alpha$ be the strict transform of $J$ in $R_\alpha$
    along the sequence (\cref{def:III.9-strict-sequence}), and $f_\alpha$ a strict transform of
    $f$ in $R_\alpha$ along the sequence (\cref{def:III.9-strict-transform-element}). Then, for
    every $\bar\alpha\ge0$ such that $\nu^*(J_{\bar\alpha})=\nu^*(J)$ (\cref{def:III.2}) and
    that $\tau^{(a)}(J_{\bar\alpha})=\tau^{(a)}(J)$ for $1\le a\le t(J)=t(J_{\bar\alpha})$
    (\cref{def:III.6}) (where $J_{\bar\alpha}=J$ if $\bar\alpha=0$), we have
    $\nu_{M_{\bar\alpha}}(f_{\bar\alpha})=\nu$ and $\nu_{P_{\bar\alpha}}(f_{\bar\alpha})=\nu$
    (provided $P_{\bar\alpha}$ exists and is different from $R_{\bar\alpha}$), where
    $M_{\bar\alpha}$ denotes the maximal ideal of $R_{\bar\alpha}$ and $f_0=f$.

    A system of elements $(f_1,\dots,f_m)$ of $R$ is said to be \emph{$J$-stable} (or, stable
    with respect to $J$) if $f_j$ is so for all $j$ ($1\le j\le m$). A regular frame
    $(S;z_1,\dots,z_r)$ of $R$ (\cref{def:III.9}) is said to be \emph{$J$-stable} (or, stable
    with respect to $J$) if the system $(z_1,\dots,z_r)$ is so. (Definition 11, p.~262.)

    (Formalization note: sequences are indexed by all $\alpha\ge0$, a finite sequence being
    continued by trivial monoidal transforms with $P_\alpha=R_\alpha$, so that the proviso reads
    $P_{\bar\alpha}\ne R_{\bar\alpha}$; $R$ is identified with $R_0$ by a ring isomorphism;
    $f_{\bar\alpha}$ runs over all strict transforms of $f$, which differ by units, and for
    $\bar\alpha=0$ over the unit multiples of $f$; this does not affect the orders.) -/)
  (latexEnv := "definition")]
def IsJStable (J : Ideal R) (f : R) : Prop :=
  ∀ (Sq : MonoidalSequence.{u}) (e : R ≃+* Sq.ring 0), Sq.ideal 0 = J.map e →
    Sq.IsPermissible → Sq.IsResiduallySeparableAlgebraic →
    ∀ α : ℕ, nuStar (Sq.ring α) (Sq.ideal α) = nuStar R J →
      t (Sq.ring α) (Sq.ideal α) = t R J →
      (∀ a, 1 ≤ a → a ≤ t R J → tau (Sq.ring α) (Sq.ideal α) a = tau R J a) →
      ∀ fα : Sq.ring α, Sq.IsStrictTransformElem e f α fα →
        Ideal.ordElem (maximalIdeal (Sq.ring α)) fα = Ideal.ordElem (maximalIdeal R) f ∧
        (Sq.center α ≠ ⊤ →
          Ideal.ordElem (Sq.center α) fα = Ideal.ordElem (maximalIdeal R) f)

/-- Definition 11, p. 262: "A system of elements `(f₁, …, f_m)` of `R` is said to be *`J`-stable*
(or, stable with respect to `J`) if `f_j` is so for all `j` (`1 ≤ j ≤ m`)." -/
@[blueprint "def:III.11"
  (statement := /-- A system of elements $(f_1,\dots,f_m)$ of $R$ is \emph{$J$-stable} if $f_j$
    is $J$-stable for all $j$ ($1\le j\le m$). (Definition 11, p.~262.) -/)
  (latexEnv := "definition")]
def IsJStableSystem (J : Ideal R) {m : ℕ} (f : Fin m → R) : Prop :=
  ∀ j, IsJStable J (f j)

/-- Definition 11, p. 262: "A regular frame `(S; z₁, …, z_r)` of `R` is said to be *`J`-stable*
(or, stable with respect to `J`) if the system `(z₁, …, z_r)` is so." -/
@[blueprint "def:III.11"
  (statement := /-- A regular frame $(S;z_1,\dots,z_r)$ of $R$ is \emph{$J$-stable} if the
    system $(z_1,\dots,z_r)$ is $J$-stable. (Definition 11, p.~262.) -/)
  (latexEnv := "definition")]
def RegularFrame.IsJStable (F : RegularFrame R) (J : Ideal R) : Prop :=
  IsJStableSystem J F.z

end Definition11

/-! ### Remark 1 (pp. 262–263) -/

section Remark1

/-- The commutative diagrams of canonical local homomorphisms of Remark 1 (p. 263)
```
  R_α     →  R'_α
   ↑           ↑
  R_{α−1} →  R'_{α−1}
```
along two sequences of monoidal transforms `S` of `R` and `S'` of `R'`, with
`P'_{α−1} = P_{α−1}R'_{α−1}`: a family `φ α : R_α → R'_α` of local homomorphisms such that
`P'_α = P_α R'_α` and that `φ (α+1)` (read on the monoidal transforms `R_α[x⁻¹P_α]_{M'}` and
`R'_α[x'⁻¹P'_α]_{M''}` through `S.equiv α`, `S'.equiv α`) is a canonical local homomorphism over
`φ α` in the sense of p. 211 (`IsCanonicalLift`, `def:III.2-canonical`). -/
structure MonoidalSequence.IsLiftAlong (S S' : MonoidalSequence.{u})
    (φ : ∀ n, S.ring n →+* S'.ring n) : Prop where
  /-- Each `R_α → R'_α` is a local homomorphism. -/
  isLocalHom : ∀ n, IsLocalHom (φ n)
  /-- `P'_α = P_α R'_α`. -/
  center_eq : ∀ n, S'.center n = (S.center n).map (φ n)
  /-- The square over `R_α → R'_α` commutes, with `R_{α+1} → R'_{α+1}` local. -/
  canonical : ∀ n, IsCanonicalLift (φ n) (S.transform n) (S'.transform n)
    (((S'.equiv n).symm : S'.ring (n + 1) →+* (S'.transform n).ring).comp
      ((φ (n + 1)).comp (S.equiv n : (S.transform n).ring →+* S.ring (n + 1))))

end Remark1

/-! ### Remark 2 (p. 263) -/

section Remark2

/-- A bijective homomorphism of regular local rings transforms a regular system of parameters
into a regular system of parameters. -/
theorem mapsRSOP_of_bijective_aux {A B : Type u} [CommRing A] [IsRegularLocalRing A]
    [CommRing B] [IsRegularLocalRing B] (φ : A →+* B) (hφ : Function.Bijective φ) :
    RingHom.MapsRSOP φ := by
  classical
  obtain ⟨-, s, hs⟩ := (isRegularLocalRing_iff_exists_rsop A).mp inferInstance
  refine ⟨s, hs, ?_, hφ.1.injOn⟩
  obtain ⟨hspan, hcard⟩ := hs
  refine ⟨?_, ?_⟩
  · rw [Finset.coe_image, ← Ideal.map_span, hspan]
    exact map_maximalIdeal_of_surjective φ hφ.2
  · rw [Finset.card_image_of_injective _ hφ.1, hcard,
      ringKrullDim_eq_of_ringEquiv (RingEquiv.ofBijective φ hφ)]

/-- A bijective local homomorphism is residually separable. -/
theorem isResiduallySeparable_of_bijective_aux {A B : Type u} [CommRing A]
    [IsRegularLocalRing A] [CommRing B] [IsRegularLocalRing B] (φ : A →+* B) [IsLocalHom φ]
    (hφ : Function.Bijective φ) : RingHom.IsResiduallySeparable φ := by
  let _ := (ResidueField.map φ).toAlgebra
  have hbij : Function.Bijective (ResidueField.map φ) := by
    refine ⟨(ResidueField.map φ).injective, fun y => ?_⟩
    obtain ⟨b, rfl⟩ := IsLocalRing.residue_surjective y
    obtain ⟨a, rfl⟩ := hφ.2 b
    exact ⟨IsLocalRing.residue A a, ResidueField.map_residue φ a⟩
  intro k' _ _ _
  let eB : ResidueField B ≃ₐ[ResidueField A] ResidueField A :=
    (AlgEquiv.ofBijective (Algebra.ofId (ResidueField A) (ResidueField B)) hbij).symm
  let e' := (Algebra.TensorProduct.congr eB (AlgEquiv.refl : k' ≃ₐ[ResidueField A] k')).trans
    (Algebra.TensorProduct.lid (ResidueField A) k')
  exact isReduced_of_injective e' e'.injective

/-- `ν*`, `t` and the `τ^{(a)}` are preserved by bijective homomorphisms (Corollary to Lemma 2,
§1, and Lemma 13, §4). -/
theorem nuStar_t_tau_map_of_bijective_aux [Hironaka.HironakaCitedResults.{u}] {A B : Type u} [CommRing A]
    [IsRegularLocalRing A] [CommRing B] [IsRegularLocalRing B] (φ : A →+* B)
    (hφ : Function.Bijective φ) (I : Ideal A) :
    nuStar B (I.map φ) = nuStar A I ∧ t B (I.map φ) = t A I ∧
      ∀ i, 1 ≤ i → i ≤ t A I → tau B (I.map φ) i = tau A I i := by
  have := IsLocalHom.of_surjective φ hφ.2
  have hα := mapsRSOP_of_bijective_aux φ hφ
  obtain ⟨h1, h2, -⟩ := tauStar_map φ hα (isResiduallySeparable_of_bijective_aux φ hφ) I
  exact ⟨(nuStar_map_eq_of_mapsRSOP φ hα I).symm, h1, h2⟩

/-- Standard bases are preserved by bijective homomorphisms. -/
theorem isStandardBase_map_of_bijective_aux {A B : Type u} [CommRing A]
    [IsRegularLocalRing A] [CommRing B] [IsRegularLocalRing B] (φ : A →+* B)
    (hφ : Function.Bijective φ) (I : Ideal A) {m : ℕ} (f : Fin m → A)
    (hf : IsStandardBase A I f) : IsStandardBase B (I.map φ) fun j => φ (f j) := by
  have := IsLocalHom.of_surjective φ hφ.2
  exact (isStandardBase_iff_isStandardBase_map φ (mapsRSOP_of_bijective_aux φ hφ) I f).mp hf

/-- The order function of the maximal ideal is preserved by ring isomorphisms. -/
theorem ordElem_maximalIdeal_ringEquiv_aux {A B : Type u} [CommRing A]
    [IsRegularLocalRing A] [CommRing B] [IsRegularLocalRing B] (e : A ≃+* B) (a : A) :
    Ideal.ordElem (maximalIdeal B) (e a) = Ideal.ordElem (maximalIdeal A) a := by
  have hmem : ∀ ν : ℕ, e a ∈ maximalIdeal B ^ ν ↔ a ∈ maximalIdeal A ^ ν := by
    intro ν
    rw [← map_ringEquiv_maximalIdeal e, ← Ideal.map_pow, ← Ideal.comap_symm, Ideal.mem_comap]
    simp
  simp only [Ideal.ordElem, hmem]

/-- The initial form of a unit `u` is the image of its class `ū ∈ k = A/M` in `gr_M(A)`. -/
private theorem initialForm_unit_aux {A : Type u} [CommRing A] [IsRegularLocalRing A]
    (u : Aˣ) :
    initialForm (maximalIdeal A) (u : A) =
      algebraMap (A ⧸ maximalIdeal A) (AssocGraded (maximalIdeal A))
        (Ideal.Quotient.mk (maximalIdeal A) u) := by
  have h0 : Ideal.ordElem (maximalIdeal A) (u : A) = ((0 : ℕ) : ℕ∞) := by
    refine le_antisymm (Ideal.ordElem_le_of_notMem ?_) (by simp)
    rw [zero_add, pow_one]
    exact fun h => (maximalIdeal.isMaximal A).ne_top (Ideal.eq_top_of_isUnit_mem _ h u.isUnit)
  rw [initialForm_eq_mk _ h0]
  show AssocGraded.mk _ 0 _ _ = AssocGraded.algebraMapQuot _ (Ideal.Quotient.mk _ _)
  rw [AssocGraded.algebraMapQuot, Ideal.Quotient.lift_mk, AssocGraded.algebraMap_apply,
    AssocGraded.mk]
  congr 1

/-- Multiplying the members of a standard base by units gives a standard base (the initial
forms change by non-zero constants of `k`). -/
private theorem isStandardBase_of_unit_mul_aux {A : Type u} [CommRing A] [IsRegularLocalRing A]
    (J : Ideal A) {m : ℕ} {f f' : Fin m → A} (hf : IsStandardBase A J f) (u : Fin m → Aˣ)
    (hu : ∀ j, f' j = u j * f j) : IsStandardBase A J f' := by
  have hfwd : ∀ j, initialForm (maximalIdeal A) (f' j) =
      Ideal.Quotient.mk (maximalIdeal A) (u j : A) • initialForm (maximalIdeal A) (f j) :=
    fun j => by
      rw [hu j, initialForm_mul_maximalIdeal, Algebra.smul_def, ← initialForm_unit_aux]
  have hbwd : ∀ j, initialForm (maximalIdeal A) (f j) =
      initialForm (maximalIdeal A) (((u j)⁻¹ : Aˣ) : A) * initialForm (maximalIdeal A) (f' j) :=
    fun j => by
      rw [← initialForm_mul_maximalIdeal, hu j, ← mul_assoc, ← Units.val_mul, inv_mul_cancel,
        Units.val_one, one_mul]
  have hle : ∀ {n : ℕ} (ψ χ : Fin n → AssocGraded (maximalIdeal A)),
      (∀ j, ∃ a, ψ j = a * χ j) → Ideal.span (Set.range ψ) ≤ Ideal.span (Set.range χ) := by
    intro n ψ χ h
    rw [Ideal.span_le]
    rintro _ ⟨j, rfl⟩
    obtain ⟨a, ha⟩ := h j
    rw [SetLike.mem_coe, ha]
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨j, rfl⟩)
  have hfwd' : ∀ j, ∃ a, initialForm (maximalIdeal A) (f' j) =
      a * initialForm (maximalIdeal A) (f j) := fun j =>
    ⟨_, (hfwd j).trans (Algebra.smul_def _ _)⟩
  have hbwd' : ∀ j, ∃ a, initialForm (maximalIdeal A) (f j) =
      a * initialForm (maximalIdeal A) (f' j) := fun j => ⟨_, hbwd j⟩
  obtain ⟨hJ, hin, ⟨d, hd, hmono⟩, hspan, hiii⟩ := hf
  refine ⟨fun j => (hu j) ▸ J.mul_mem_left _ (hJ j), fun j => ?_, ⟨d, fun j => ?_, hmono⟩,
    hspan.trans (le_antisymm (hle _ _ hbwd') (hle _ _ hfwd')), fun i h => hiii i ?_⟩
  · beta_reduce
    rw [hfwd j]
    exact Submodule.smul_of_tower_mem _ _ (hin j)
  · beta_reduce
    rw [hfwd j]
    exact Submodule.smul_mem _ _ (hd j)
  · have h' := hle (fun j : Fin i => initialForm (maximalIdeal A) (f' (Fin.castLE i.2.le j)))
      (fun j : Fin i => initialForm (maximalIdeal A) (f (Fin.castLE i.2.le j)))
      (fun j => hfwd' _) h
    beta_reduce
    rw [hbwd i]
    exact Ideal.mul_mem_left _ _ h'

/-- Remark 2, p. 263: "Let `(f₁, …, f_m)` be a standard base of an ideal `J` in `R`. If the system
`(f₁, …, f_m)` is `J`-stable, if `{(J_α, R_α, P_{α−1})}` is a sequence of strict monoidal
transforms of `(J, R)` such that the sequence `{(R_α, P_{α−1})}` is permissible for `J` and that
`R_α` is residually separable algebraic over `R_{α−1}` for all `α`, where `R₀ = R`, and if `ᾱ` is
an index such that `ν*(J_ᾱ) = ν*(J)` and `τ*(J_ᾱ) = τ*(J)`, then `(f₁^{(ᾱ)}, …, f_m^{(ᾱ)})` with a
strict transform `f_j^{(ᾱ)}` of `f_j` in `R_ᾱ` along `{(R_α, P_{α−1})}` for `1 ≤ j ≤ m` is a
standard base of `J_ᾱ`. (See Theorem 5 of §6.)"

(Formalization note: `τ*(J_ᾱ) = τ*(J)` is `t(J_ᾱ) = t(J)` and `τ^{(a)}(J_ᾱ) = τ^{(a)}(J)` for
`1 ≤ a ≤ t(J)`; the index `ᾱ` runs over `ℕ`.) -/
@[blueprint "rem:III.9-2"
  (statement := /-- Let $(f_1,\dots,f_m)$ be a standard base of an ideal $J$ in $R$
    (\cref{def:III.3}). If the system $(f_1,\dots,f_m)$ is $J$-stable (\cref{def:III.11}), if
    $\{(J_\alpha,R_\alpha,P_{\alpha-1})\}$ is a sequence of strict monoidal transforms of
    $(J,R)$ (\cref{def:III.9-strict-sequence}) such that the sequence
    $\{(R_\alpha,P_{\alpha-1})\}$ is permissible for $J$ (\cref{def:III.9-permissible-sequence})
    and that $R_\alpha$ is residually separable algebraic over $R_{\alpha-1}$ for all $\alpha$,
    where $R_0=R$, and if $\bar\alpha$ is an index such that $\nu^*(J_{\bar\alpha})=\nu^*(J)$
    and $\tau^*(J_{\bar\alpha})=\tau^*(J)$, then $(f^{(\bar\alpha)}_1,\dots,f^{(\bar\alpha)}_m)$
    with a strict transform $f^{(\bar\alpha)}_j$ of $f_j$ in $R_{\bar\alpha}$ along
    $\{(R_\alpha,P_{\alpha-1})\}$ (\cref{def:III.9-strict-transform-element}) for
    $1\le j\le m$ is a standard base of $J_{\bar\alpha}$. (See Theorem~5 of \S6,
    \cref{thm:III.5}.) (Remark 2, p.~263.)

    (Formalization note: $\tau^*(J_{\bar\alpha})=\tau^*(J)$ is transcribed as
    $t(J_{\bar\alpha})=t(J)$ together with $\tau^{(a)}(J_{\bar\alpha})=\tau^{(a)}(J)$ for
    $1\le a\le t(J)$.) -/)
  (proof := /-- ``See Theorem~5 of \S6'' (\cref{thm:III.5}); no further argument is given.
    [Editorial gloss, not in the paper: by $J$-stability and the monotonicity of $\nu^*$ and
    $\tau^*$ (\cref{thm:III.3}), for every $\alpha<\bar\alpha$ we have
    $\nu^*(J_\alpha)=\nu^*(J)$ and $\nu_{P_\alpha}(f^{(\alpha)}_j)=\nu_{M_\alpha}(f^{(\alpha)}_j)=
    \nu_M(f_j)=\nu^{(j)}(J)$, so that Theorem~5 (\cref{thm:III.5}) applies inductively to the
    monoidal transforms $R_\alpha\to R_{\alpha+1}$.] -/)
  (latexEnv := "remark")]
theorem isStandardBase_strictTransform_of_isJStableSystem [Hironaka.HironakaCitedResults.{u}] {R : Type u} [CommRing R]
    [IsRegularLocalRing R] (J : Ideal R) {m : ℕ} (f : Fin m → R) (hf : IsStandardBase R J f)
    (hstab : IsJStableSystem J f) (S : MonoidalSequence.{u}) (e : R ≃+* S.ring 0)
    (h0 : S.ideal 0 = J.map e) (hperm : S.IsPermissible)
    (hsep : S.IsResiduallySeparableAlgebraic) (αb : ℕ)
    (hnu : nuStar (S.ring αb) (S.ideal αb) = nuStar R J)
    (ht : t (S.ring αb) (S.ideal αb) = t R J)
    (htau : ∀ a, 1 ≤ a → a ≤ t R J → tau (S.ring αb) (S.ideal αb) a = tau R J a)
    (g : Fin m → S.ring αb) (hg : ∀ j, S.IsStrictTransformElem e (f j) αb (g j)) :
    IsStandardBase (S.ring αb) (S.ideal αb) g := by
  classical
  -- one step `R_n → R_{n+1}`: `ν*` does not increase, and if it stays the same then `t` stays
  -- the same and the `τ^{(i)}` do not decrease (Theorem 3, §5)
  have step : ∀ n, nuStar (S.ring (n + 1)) (S.ideal (n + 1)) ≤ nuStar (S.ring n) (S.ideal n) ∧
      (nuStar (S.ring (n + 1)) (S.ideal (n + 1)) = nuStar (S.ring n) (S.ideal n) →
        t (S.ring (n + 1)) (S.ideal (n + 1)) = t (S.ring n) (S.ideal n) ∧
        ∀ i, 1 ≤ i → i ≤ t (S.ring n) (S.ideal n) →
          tau (S.ring n) (S.ideal n) i ≤ tau (S.ring (n + 1)) (S.ideal (n + 1)) i) := by
    intro n
    rcases hperm n with htop | ⟨hP, hJP, hreg, -⟩
    · -- center `R_n`: `R_n → R_{n+1}` is an isomorphism
      have hbij := MonoidalSequence.toRing_bijective_of_eq_top_aux (S.transform n) htop
      have hφ : Function.Bijective
          ((S.equiv n : (S.transform n).ring →+* S.ring (n + 1)).comp (S.transform n).toRing) :=
        (S.equiv n).bijective.comp hbij
      have hI : S.ideal (n + 1) = (S.ideal n).map
          ((S.equiv n : (S.transform n).ring →+* S.ring (n + 1)).comp (S.transform n).toRing) := by
        rw [S.ideal_succ n, MonoidalSequence.strictTransformIdeal_eq_map_of_eq_top_aux _ htop]
        exact Ideal.map_map (S.transform n).toRing
          (S.equiv n : (S.transform n).ring →+* S.ring (n + 1))
      obtain ⟨h1, h2, h3⟩ := nuStar_t_tau_map_of_bijective_aux _ hφ (S.ideal n)
      rw [← hI] at h1 h2 h3
      exact ⟨h1.le, fun _ => ⟨h2, fun i hi hit => (h3 i hi hit).ge⟩⟩
    · have := hP
      have := hreg
      obtain ⟨h1, h2⟩ := nuStar_strictTransform_le (S.ring n) (S.center n) (S.ideal n) hJP
        (S.transform n) (hsep n) (hperm n)
      obtain ⟨e1, e2, e3⟩ := nuStar_t_tau_map_of_bijective_aux
        (S.equiv n : (S.transform n).ring →+* S.ring (n + 1)) (S.equiv n).bijective
        (strictTransformIdeal (S.transform n) (S.ideal n))
      have hI : S.ideal (n + 1) = (strictTransformIdeal (S.transform n) (S.ideal n)).map
          (S.equiv n : (S.transform n).ring →+* S.ring (n + 1)) := S.ideal_succ n
      rw [← hI] at e1 e2 e3
      refine ⟨e1.trans_le h1, fun heq => ?_⟩
      obtain ⟨ht', htau'⟩ := h2 (e1.symm.trans heq)
      exact ⟨e2.trans ht', fun i hi hit =>
        (htau' i hi hit).trans (e3 i hi (hit.trans ht'.ge)).ge⟩
  -- `R₀ = R`
  obtain ⟨hN0, ht0, hτ0⟩ := nuStar_t_tau_map_of_bijective_aux (e : R →+* S.ring 0) e.bijective J
  rw [← show S.ideal 0 = J.map (e : R →+* S.ring 0) from h0] at hN0 ht0 hτ0
  -- `ν*` along the sequence
  have chain : ∀ n k,
      nuStar (S.ring (n + k)) (S.ideal (n + k)) ≤ nuStar (S.ring n) (S.ideal n) := by
    intro n k
    induction k with
    | zero => exact le_rfl
    | succ k ih => exact (step (n + k)).1.trans ih
  have hnuα : ∀ n ≤ αb, nuStar (S.ring n) (S.ideal n) = nuStar R J := by
    intro n hn
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
    refine le_antisymm ?_ (hnu.symm.trans_le (chain n k))
    have := chain 0 n
    rw [zero_add] at this
    exact this.trans_eq hN0
  have htα : ∀ n ≤ αb, t (S.ring n) (S.ideal n) = t R J := by
    intro n
    induction n with
    | zero => exact fun _ => ht0
    | succ n ih =>
      intro hn
      exact ((step n).2 ((hnuα (n + 1) hn).trans (hnuα n (by omega)).symm)).1.trans (ih (by omega))
  have hτup : ∀ n k, n + k ≤ αb → ∀ i, 1 ≤ i → i ≤ t R J →
      tau (S.ring n) (S.ideal n) i ≤ tau (S.ring (n + k)) (S.ideal (n + k)) i := by
    intro n k
    induction k with
    | zero => exact fun _ _ _ _ => le_rfl
    | succ k ih =>
      intro hk i hi hit
      refine (ih (by omega) i hi hit).trans (((step (n + k)).2
        ((hnuα (n + k + 1) hk).trans (hnuα (n + k) (by omega)).symm)).2 i hi ?_)
      rw [htα (n + k) (by omega)]
      exact hit
  have hτα : ∀ n ≤ αb, ∀ a, 1 ≤ a → a ≤ t R J → tau (S.ring n) (S.ideal n) a = tau R J a := by
    intro n hn a ha hat
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
    refine le_antisymm ((hτup n k le_rfl a ha hat).trans_eq (htau a ha hat)) ?_
    have := hτup 0 n (by omega) a ha hat
    rw [zero_add] at this
    exact (hτ0 a ha hat).symm.trans_le this
  -- the `J`-stability of the `f_j`
  have hstabn : ∀ n ≤ αb, ∀ j (gn : S.ring n), S.IsStrictTransformElem e (f j) n gn →
      Ideal.ordElem (maximalIdeal (S.ring n)) gn = Ideal.ordElem (maximalIdeal R) (f j) ∧
      (S.center n ≠ ⊤ →
        Ideal.ordElem (S.center n) gn = Ideal.ordElem (maximalIdeal R) (f j)) :=
    fun n hn j gn hgn => hstab j S e h0 hperm hsep n (hnuα n hn) (htα n hn) (hτα n hn) gn hgn
  -- `ν_j = ν_M(f_j) < ∞`
  have hfin : ∀ j, ∃ ν : ℕ, (ν : ℕ∞) = Ideal.ordElem (maximalIdeal R) (f j) := by
    intro j
    have hne : Ideal.ordElem (maximalIdeal R) (f j) ≠ ⊤ := by
      intro htop
      apply hf.2.2.2.2 j
      have h0' : initialForm (maximalIdeal R) (f j) = 0 := by rw [initialForm, dite_eq_left htop]
      beta_reduce
      rw [h0']
      exact zero_mem _
    obtain ⟨ν, hν⟩ := ENat.ne_top_iff_exists.mp hne
    exact ⟨ν, hν⟩
  choose ν hν using hfin
  -- induction along the sequence (Theorem 5, §6, at each step)
  have main : ∀ n ≤ αb, ∀ gn : Fin m → S.ring n,
      (∀ j, S.IsStrictTransformElem e (f j) n (gn j)) →
      IsStandardBase (S.ring n) (S.ideal n) gn := by
    intro n
    induction n with
    | zero =>
      intro _ gn hgn
      have hbase : IsStandardBase (S.ring 0) (S.ideal 0) fun j => e (f j) := by
        rw [show S.ideal 0 = J.map (e : R →+* S.ring 0) from h0]
        exact isStandardBase_map_of_bijective_aux (e : R →+* S.ring 0) e.bijective J f hf
      choose u hu using fun j => MonoidalSequence.IsStrictTransformElem.unique S
        (rfl : S.IsStrictTransformElem e (f j) 0 (e (f j))) (hgn j)
      exact isStandardBase_of_unit_mul_aux _ hbase u hu
    | succ n ih =>
      intro hn gn hgn
      choose g0 hg0 using fun j =>
        MonoidalSequence.exists_strictAlong_span_singleton_eq_aux S e hperm.hasRegularCenters
          (f j) n
      have hg0' : ∀ j, S.IsStrictTransformElem e (f j) n (g0 j) := fun j => (hg0 j).symm
      have hstd := ih (by omega) g0 hg0'
      rcases hperm n with htop | ⟨hP, hJP, hreg, -⟩
      · -- center `R_n`
        have hbij := MonoidalSequence.toRing_bijective_of_eq_top_aux (S.transform n) htop
        have hφ : Function.Bijective
            ((S.equiv n : (S.transform n).ring →+* S.ring (n + 1)).comp
              (S.transform n).toRing) :=
          (S.equiv n).bijective.comp hbij
        have hI : S.ideal (n + 1) = (S.ideal n).map
            ((S.equiv n : (S.transform n).ring →+* S.ring (n + 1)).comp
              (S.transform n).toRing) := by
          rw [S.ideal_succ n, MonoidalSequence.strictTransformIdeal_eq_map_of_eq_top_aux _ htop]
          exact Ideal.map_map (S.transform n).toRing
            (S.equiv n : (S.transform n).ring →+* S.ring (n + 1))
        have hstd' := isStandardBase_map_of_bijective_aux _ hφ (S.ideal n) g0 hstd
        rw [← hI] at hstd'
        have hst : ∀ j, S.IsStrictTransformElem e (f j) (n + 1)
            (S.equiv n ((S.transform n).toRing (g0 j))) := by
          intro j
          show Ideal.span {_} = S.strictAlong (Ideal.span {e (f j)}) (n + 1)
          rw [MonoidalSequence.strictAlong, hg0 j,
            MonoidalSequence.strictTransformIdeal_eq_map_of_eq_top_aux _ htop,
            Ideal.map_span, Set.image_singleton, Ideal.map_span, Set.image_singleton]
        choose u hu using fun j => MonoidalSequence.IsStrictTransformElem.unique S (hst j) (hgn j)
        exact isStandardBase_of_unit_mul_aux _ hstd' u hu
      · -- a prime center `P_n` with `R_n/P_n` regular: Theorem 5
        have := hP
        have := hreg
        have hxP : Ideal.span {(S.transform n).toRing (S.transform n).x} =
            (S.center n).map (S.transform n).toRing := (S.transform n).span_xR_eq_map
        have hPne : S.center n ≠ ⊤ := hP.ne_top
        have hordn := fun j => hstabn n (by omega) j (g0 j) (hg0' j)
        have hmemP : ∀ j, g0 j ∈ S.center n ^ ν j := fun j => by
          apply Ideal.mem_pow_of_ordElem
          rw [(hordn j).2 hPne, hν j]
        choose g' hg' using fun j =>
          MonoidalSequence.exists_mul_pow_eq_toRing_aux (S.transform n) hxP (hmemP j)
        have hst : ∀ j, S.IsStrictTransformElem e (f j) (n + 1) (S.equiv n (g' j)) := by
          intro j
          have htoNat : (Ideal.ordElem (S.center n) (g0 j)).toNat = ν j := by
            rw [(hordn j).2 hPne, ← hν j, ENat.toNat_natCast]
          show Ideal.span {_} = S.strictAlong (Ideal.span {e (f j)}) (n + 1)
          rw [MonoidalSequence.strictAlong, hg0 j,
            MonoidalSequence.strictTransformIdeal_span_singleton_aux _ hP hreg (g0 j) _
            (S.transform n).x_mem hxP (g' j) (by rw [htoNat]; exact hg' j), Ideal.map_span,
            Set.image_singleton]
        have hord1 : ∀ j, Ideal.ordElem (maximalIdeal (S.transform n).ring) (g' j) =
            (ν j : ℕ∞) := by
          intro j
          rw [← ordElem_maximalIdeal_ringEquiv_aux (S.equiv n),
            (hstabn (n + 1) hn j _ (hst j)).1, hν j]
        have h5 := (isStandardBase_strictTransform (S.ideal n) (S.center n) hJP (S.transform n)
          (hsep n) (S.transform n).x (S.transform n).x_mem hxP.symm g0 ν g'
          (fun j => (hν j).trans (hordn j).1.symm) hg' hstd
          (fun j => ((hordn j).2 hPne).trans (hordn j).1.symm) hord1).1
        have hstd' := isStandardBase_map_of_bijective_aux
          (S.equiv n : (S.transform n).ring →+* S.ring (n + 1)) (S.equiv n).bijective _ g' h5
        rw [← show S.ideal (n + 1) = (strictTransformIdeal (S.transform n) (S.ideal n)).map
          (S.equiv n : (S.transform n).ring →+* S.ring (n + 1)) from S.ideal_succ n] at hstd'
        choose u hu using fun j => MonoidalSequence.IsStrictTransformElem.unique S (hst j) (hgn j)
        exact isStandardBase_of_unit_mul_aux _ hstd' u hu
  exact main αb le_rfl g hg


end Remark2

/-! ### Auxiliary results on sequences: monotonicity, strict transforms of elements, one-step
sequences (used for Remarks 3 and Definition 13) -/

section SequenceAux

/-- Along a permissible residually separable algebraic sequence, `ν*`, `t` and the `τ^{(a)}` of
`J_n` equal those of `J` for every `n ≤ ᾱ` as soon as they do for `ᾱ` (Theorem 3 of §5: `ν*` does
not increase, and if it stays the same `t` is unchanged and the `τ^{(a)}` do not decrease).  This is
the monotonicity argument inside the proof of Remark 2, stated separately. -/
theorem MonoidalSequence.nuStar_t_tau_eq_of_le [Hironaka.HironakaCitedResults.{u}] {R : Type u} [CommRing R] [IsRegularLocalRing R]
    (J : Ideal R) (S : MonoidalSequence.{u}) (e : R ≃+* S.ring 0) (h0 : S.ideal 0 = J.map e)
    (hperm : S.IsPermissible) (hsep : S.IsResiduallySeparableAlgebraic) (αb : ℕ)
    (hnu : nuStar (S.ring αb) (S.ideal αb) = nuStar R J)
    (htau : ∀ a, 1 ≤ a → a ≤ t R J → tau (S.ring αb) (S.ideal αb) a = tau R J a) :
    ∀ n ≤ αb, nuStar (S.ring n) (S.ideal n) = nuStar R J ∧
      t (S.ring n) (S.ideal n) = t R J ∧
      ∀ a, 1 ≤ a → a ≤ t R J → tau (S.ring n) (S.ideal n) a = tau R J a := by
  classical
  -- one step `R_n → R_{n+1}`: `ν*` does not increase, and if it stays the same then `t` stays
  -- the same and the `τ^{(i)}` do not decrease (Theorem 3, §5)
  have step : ∀ n, nuStar (S.ring (n + 1)) (S.ideal (n + 1)) ≤ nuStar (S.ring n) (S.ideal n) ∧
      (nuStar (S.ring (n + 1)) (S.ideal (n + 1)) = nuStar (S.ring n) (S.ideal n) →
        t (S.ring (n + 1)) (S.ideal (n + 1)) = t (S.ring n) (S.ideal n) ∧
        ∀ i, 1 ≤ i → i ≤ t (S.ring n) (S.ideal n) →
          tau (S.ring n) (S.ideal n) i ≤ tau (S.ring (n + 1)) (S.ideal (n + 1)) i) := by
    intro n
    rcases hperm n with htop | ⟨hP, hJP, hreg, -⟩
    · -- center `R_n`: `R_n → R_{n+1}` is an isomorphism
      have hbij := MonoidalSequence.toRing_bijective_of_eq_top_aux (S.transform n) htop
      have hφ : Function.Bijective
          ((S.equiv n : (S.transform n).ring →+* S.ring (n + 1)).comp (S.transform n).toRing) :=
        (S.equiv n).bijective.comp hbij
      have hI : S.ideal (n + 1) = (S.ideal n).map
          ((S.equiv n : (S.transform n).ring →+* S.ring (n + 1)).comp (S.transform n).toRing) := by
        rw [S.ideal_succ n, MonoidalSequence.strictTransformIdeal_eq_map_of_eq_top_aux _ htop]
        exact Ideal.map_map (S.transform n).toRing
          (S.equiv n : (S.transform n).ring →+* S.ring (n + 1))
      obtain ⟨h1, h2, h3⟩ := nuStar_t_tau_map_of_bijective_aux _ hφ (S.ideal n)
      rw [← hI] at h1 h2 h3
      exact ⟨h1.le, fun _ => ⟨h2, fun i hi hit => (h3 i hi hit).ge⟩⟩
    · have := hP
      have := hreg
      obtain ⟨h1, h2⟩ := nuStar_strictTransform_le (S.ring n) (S.center n) (S.ideal n) hJP
        (S.transform n) (hsep n) (hperm n)
      obtain ⟨e1, e2, e3⟩ := nuStar_t_tau_map_of_bijective_aux
        (S.equiv n : (S.transform n).ring →+* S.ring (n + 1)) (S.equiv n).bijective
        (strictTransformIdeal (S.transform n) (S.ideal n))
      have hI : S.ideal (n + 1) = (strictTransformIdeal (S.transform n) (S.ideal n)).map
          (S.equiv n : (S.transform n).ring →+* S.ring (n + 1)) := S.ideal_succ n
      rw [← hI] at e1 e2 e3
      refine ⟨e1.trans_le h1, fun heq => ?_⟩
      obtain ⟨ht', htau'⟩ := h2 (e1.symm.trans heq)
      exact ⟨e2.trans ht', fun i hi hit =>
        (htau' i hi hit).trans (e3 i hi (hit.trans ht'.ge)).ge⟩
  -- `R₀ = R`
  obtain ⟨hN0, ht0, hτ0⟩ := nuStar_t_tau_map_of_bijective_aux (e : R →+* S.ring 0) e.bijective J
  rw [← show S.ideal 0 = J.map (e : R →+* S.ring 0) from h0] at hN0 ht0 hτ0
  -- `ν*` along the sequence
  have chain : ∀ n k,
      nuStar (S.ring (n + k)) (S.ideal (n + k)) ≤ nuStar (S.ring n) (S.ideal n) := by
    intro n k
    induction k with
    | zero => exact le_rfl
    | succ k ih => exact (step (n + k)).1.trans ih
  have hnuα : ∀ n ≤ αb, nuStar (S.ring n) (S.ideal n) = nuStar R J := by
    intro n hn
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
    refine le_antisymm ?_ (hnu.symm.trans_le (chain n k))
    have := chain 0 n
    rw [zero_add] at this
    exact this.trans_eq hN0
  have htα : ∀ n ≤ αb, t (S.ring n) (S.ideal n) = t R J := by
    intro n
    induction n with
    | zero => exact fun _ => ht0
    | succ n ih =>
      intro hn
      exact ((step n).2 ((hnuα (n + 1) hn).trans (hnuα n (by omega)).symm)).1.trans (ih (by omega))
  have hτup : ∀ n k, n + k ≤ αb → ∀ i, 1 ≤ i → i ≤ t R J →
      tau (S.ring n) (S.ideal n) i ≤ tau (S.ring (n + k)) (S.ideal (n + k)) i := by
    intro n k
    induction k with
    | zero => exact fun _ _ _ _ => le_rfl
    | succ k ih =>
      intro hk i hi hit
      refine (ih (by omega) i hi hit).trans (((step (n + k)).2
        ((hnuα (n + k + 1) hk).trans (hnuα (n + k) (by omega)).symm)).2 i hi ?_)
      rw [htα (n + k) (by omega)]
      exact hit
  have hτα : ∀ n ≤ αb, ∀ a, 1 ≤ a → a ≤ t R J → tau (S.ring n) (S.ideal n) a = tau R J a := by
    intro n hn a ha hat
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
    refine le_antisymm ((hτup n k le_rfl a ha hat).trans_eq (htau a ha hat)) ?_
    have := hτup 0 n (by omega) a ha hat
    rw [zero_add] at this
    exact (hτ0 a ha hat).symm.trans_le this
  exact fun n hn => ⟨hnuα n hn, htα n hn, hτα n hn⟩

namespace MonoidalSequence

variable (S : MonoidalSequence.{u})

/-- One more step of a strict transform of an element, for a proper center: if `g` is a strict
transform of `z` in `R_n` with `ν_{P_n}(g) = ν` and `x^ν w = g` in `R_{n+1}` for a generator `x`
of `P_nR_{n+1}`, then `w` (carried to `R_{n+1}`) is a strict transform of `z` in `R_{n+1}`. -/
theorem isStrictTransformElem_succ_of_center_ne_top {R : Type u} [CommRing R]
    (e : R ≃+* S.ring 0) (hS : S.HasRegularCenters) {z : R} {n : ℕ} {g : S.ring n}
    (hg : S.IsStrictTransformElem e z n g) (hne : S.center n ≠ ⊤) {ν : ℕ}
    (hν : Ideal.ordElem (S.center n) g = ν) {x : (S.transform n).ring}
    (hx : Ideal.span {x} = (S.center n).map (S.transform n).toRing)
    {w : (S.transform n).ring} (hw : x ^ ν * w = (S.transform n).toRing g) :
    S.IsStrictTransformElem e z (n + 1) (S.equiv n w) := by
  obtain ⟨hP, hreg⟩ := ((hS n).2).resolve_left hne
  have hxP : Ideal.span {(S.transform n).toRing (S.transform n).x} =
      (S.center n).map (S.transform n).toRing := (S.transform n).span_xR_eq_map
  obtain ⟨u, hu⟩ := Ideal.span_singleton_eq_span_singleton.mp (hx.trans hxP.symm)
  have hg' : (S.transform n).toRing (S.transform n).x ^ (Ideal.ordElem (S.center n) g).toNat *
      (((u⁻¹ : ((S.transform n).ring)ˣ) : (S.transform n).ring) ^ ν * w) =
        (S.transform n).toRing g := by
    rw [hν, ENat.toNat_natCast, ← hw, ← hu, mul_pow, mul_assoc,
      ← mul_assoc ((u : (S.transform n).ring) ^ ν), ← mul_pow, Units.mul_inv, one_pow, one_mul]
  show Ideal.span {_} = S.strictAlong (Ideal.span {e z}) (n + 1)
  rw [MonoidalSequence.strictAlong, ← hg, MonoidalSequence.strictTransformIdeal_span_singleton_aux
    _ hP hreg g _ (S.transform n).x_mem hxP _ hg', Ideal.map_span, Set.image_singleton, map_mul]
  exact (Ideal.span_singleton_mul_left_unit
    (((Units.isUnit _).pow ν).map (S.equiv n : (S.transform n).ring →+* S.ring (n + 1))) _).symm

/-- One more step of a strict transform of an element, for the center `R_n`. -/
theorem isStrictTransformElem_succ_of_center_eq_top {R : Type u} [CommRing R]
    (e : R ≃+* S.ring 0) {z : R} {n : ℕ} {g : S.ring n}
    (hg : S.IsStrictTransformElem e z n g) (htop : S.center n = ⊤) :
    S.IsStrictTransformElem e z (n + 1) (S.equiv n ((S.transform n).toRing g)) := by
  show Ideal.span {_} = S.strictAlong (Ideal.span {e z}) (n + 1)
  rw [MonoidalSequence.strictAlong, ← hg,
    MonoidalSequence.strictTransformIdeal_span_singleton_of_eq_top_aux _ htop, Ideal.map_span,
    Set.image_singleton]

end MonoidalSequence

end SequenceAux

/-! ### The sequence `R, R₁, R₁, …` of one monoidal transform followed by trivial ones -/

section OfStep

/-- A monoidal transform of a regular local domain with center `R` itself exists (p. 209: it is
`R`). -/
theorem MonoidalTransform.nonempty_top (A : Type u) [CommRing A] [IsRegularLocalRing A]
    [IsDomain A] : Nonempty (MonoidalTransform A ⊤) := by
  set K := FractionRing A
  have hgen : ∀ b : blowupAlgebra A ⊤ 1, ∃ r : A, (b : K) = algebraMap A K r := by
    intro b
    have hb := b.2
    unfold blowupAlgebra at hb
    refine Algebra.adjoin_induction (p := fun y _ => ∃ r : A, y = algebraMap A K r) ?_ ?_ ?_ ?_ hb
    · rintro _ ⟨q, -, rfl⟩
      exact ⟨q, by simp; rfl⟩
    · intro r; exact ⟨r, rfl⟩
    · rintro _ _ _ _ ⟨r, rfl⟩ ⟨r', rfl⟩; exact ⟨r + r', by simp⟩
    · rintro _ _ _ _ ⟨r, rfl⟩ ⟨r', rfl⟩; exact ⟨r * r', by simp⟩
  have hinj : Function.Injective (algebraMap A (blowupAlgebra A ⊤ 1)) := by
    intro a b hab
    have := congrArg (fun y : blowupAlgebra A ⊤ 1 => (y : K)) hab
    simp only [Subalgebra.coe_algebraMap] at this
    exact IsFractionRing.injective A K this
  have hsurj : Function.Surjective (algebraMap A (blowupAlgebra A ⊤ 1)) := by
    intro b
    obtain ⟨r, hr⟩ := hgen b
    exact ⟨r, Subtype.ext (by simpa using hr.symm)⟩
  have hne : (maximalIdeal A).map (algebraMap A (blowupAlgebra A ⊤ 1)) ≠ ⊤ := by
    intro h
    have := Ideal.comap_map_of_bijective (f := algebraMap A (blowupAlgebra A ⊤ 1))
      ⟨hinj, hsurj⟩ (I := maximalIdeal A)
    rw [h, Ideal.comap_top] at this
    exact (maximalIdeal.isMaximal A).ne_top this.symm
  obtain ⟨M', hM', hle⟩ := Ideal.exists_le_maximal _ hne
  exact ⟨{ x := 1, x_mem := Submodule.mem_top, x_ne_zero := one_ne_zero, M' := M'
           isPrime := hM'.isPrime, le := hle }⟩

/-- A monoidal transform with a center equal to `⊤` exists. -/
theorem MonoidalTransform.nonempty_of_eq_top {A : Type u} [CommRing A] [IsRegularLocalRing A]
    [IsDomain A] {P : Ideal A} (hP : P = ⊤) : Nonempty (MonoidalTransform A P) := by
  subst hP
  exact MonoidalTransform.nonempty_top A

/-- A residually separable algebraic local homomorphism: a bijective local homomorphism is
residually separable algebraic. -/
theorem RingHom.isResiduallySeparableAlgebraic_of_bijective {A B : Type u} [CommRing A]
    [CommRing B] [IsLocalRing A] [IsLocalRing B] (φ : A →+* B) [IsLocalHom φ]
    (hφ : Function.Bijective φ) : RingHom.IsResiduallySeparableAlgebraic φ := by
  let e := RingEquiv.ofBijective φ hφ
  let _ : Algebra (ResidueField A) (ResidueField B) := (ResidueField.map φ).toAlgebra
  show Algebra.IsSeparable (ResidueField A) (ResidueField B)
  refine Algebra.IsSeparable.of_equiv_equiv (A₁ := ResidueField A) (B₁ := ResidueField A)
    (RingEquiv.refl _) (ResidueField.mapEquiv e) (RingHom.ext fun x => ?_)
  obtain ⟨a, rfl⟩ := residue_surjective x
  simp [RingHom.algebraMap_toAlgebra, e]

end OfStep

section OfStepSeq

/-- The trivial monoidal transform of a regular local domain (center `⊤`, p. 209). -/
noncomputable def MonoidalTransform.top (A : Type u) [CommRing A] [IsRegularLocalRing A]
    [IsDomain A] : MonoidalTransform A ⊤ :=
  Classical.choice (MonoidalTransform.nonempty_top A)

/-- The canonical map `R → R'` of the trivial monoidal transform is bijective. -/
theorem MonoidalTransform.top_toRing_bijective (A : Type u) [CommRing A] [IsRegularLocalRing A]
    [IsDomain A] : Function.Bijective (MonoidalTransform.top A).toRing :=
  MonoidalSequence.toRing_bijective_of_eq_top_aux _ rfl

/-- The trivial monoidal transform of a regular local ring is regular. -/
instance MonoidalTransform.isRegularLocalRing_top (A : Type u) [CommRing A]
    [IsRegularLocalRing A] [IsDomain A] : IsRegularLocalRing (MonoidalTransform.top A).ring :=
  IsRegularLocalRing.of_ringEquiv
    (RingEquiv.ofBijective _ (MonoidalTransform.top_toRing_bijective A))

namespace MonoidalSequence

section OfStep

variable {R : Type u} [CommRing R] [IsRegularLocalRing R] [IsDomain R] {P : Ideal R}
  (T : MonoidalTransform R P) [IsRegularLocalRing T.ring]

/-- The rings of `ofStep`: `R, R₁, R₁, …`. -/
@[reducible] def OfStep.ring : ℕ → Type u
  | 0 => R
  | _ + 1 => T.ring

/-- Ring structure of `OfStep.ring`. -/
noncomputable instance (n : ℕ) : CommRing (OfStep.ring T n) :=
  match n with
  | 0 => inferInstanceAs (CommRing R)
  | _ + 1 => inferInstanceAs (CommRing T.ring)

/-- Regularity of `OfStep.ring`. -/
noncomputable instance (n : ℕ) : IsRegularLocalRing (OfStep.ring T n) :=
  match n with
  | 0 => inferInstanceAs (IsRegularLocalRing R)
  | _ + 1 => inferInstanceAs (IsRegularLocalRing T.ring)

/-- `OfStep.ring` consists of domains. -/
noncomputable instance (n : ℕ) : IsDomain (OfStep.ring T n) :=
  match n with
  | 0 => inferInstanceAs (IsDomain R)
  | _ + 1 => inferInstanceAs (IsDomain T.ring)

/-- The centers of `ofStep`: `P, R₁, R₁, …`. -/
noncomputable def OfStep.center : ∀ n, Ideal (OfStep.ring T n)
  | 0 => P
  | _ + 1 => ⊤

/-- The transforms of `ofStep`: `T` and then trivial ones. -/
noncomputable def OfStep.transform :
    ∀ n, MonoidalTransform (OfStep.ring T n) (OfStep.center T n)
  | 0 => T
  | _ + 1 => MonoidalTransform.top T.ring

/-- The identifications of the transforms with the next rings. -/
noncomputable def OfStep.equiv : ∀ n, (OfStep.transform T n).ring ≃+* OfStep.ring T (n + 1)
  | 0 => RingEquiv.refl T.ring
  | _ + 1 => (RingEquiv.ofBijective _ (MonoidalTransform.top_toRing_bijective T.ring)).symm

/-- The canonical maps of the transforms of `ofStep` are local. -/
noncomputable instance (n : ℕ) : IsLocalHom (OfStep.transform T n).toRing :=
  MonoidalTransform.isLocalHom_toRing _

/-- The ideals of `ofStep`: strict transforms of `J`. -/
noncomputable def OfStep.ideal (J : Ideal R) : ∀ n, Ideal (OfStep.ring T n)
  | 0 => J
  | n + 1 => (strictTransformIdeal (OfStep.transform T n) (OfStep.ideal J n)).map
    (OfStep.equiv T n)

/-- The sequence `R, R₁, R₁, …` of one monoidal transform `T` with center `P` followed by trivial
monoidal transforms (the monoidal transform with center `R_n` being `R_n` itself, p. 209), with
`J₀ = J`. -/
noncomputable def ofStep (J : Ideal R) : MonoidalSequence.{u} where
  ring := OfStep.ring T
  ideal := OfStep.ideal T J
  center := OfStep.center T
  transform := OfStep.transform T
  equiv := OfStep.equiv T
  ideal_succ := fun _ => rfl

/-- The identification `R = R₀` of `ofStep`. -/
noncomputable def ofStepEquiv (J : Ideal R) : R ≃+* (ofStep T J).ring 0 := RingEquiv.refl R

/-- `J₀ = J`. -/
theorem ofStep_ideal_zero (J : Ideal R) :
    (ofStep T J).ideal 0 = J.map (ofStepEquiv T J) := by
  show J = J.map (RingEquiv.refl R)
  exact (Ideal.map_id J).symm

/-- `J₁` is the strict transform of `J` in `R₁`. -/
theorem ofStep_ideal_one (J : Ideal R) : (ofStep T J).ideal 1 = strictTransformIdeal T J := by
  show Ideal.map (RingEquiv.refl T.ring) (strictTransformIdeal T J) = _
  exact Ideal.map_id _

/-- `ofStep` is permissible for `J` as soon as `P` is a permissible center for `J` (the later
centers being `R_n`). -/
theorem ofStep_isPermissible (J : Ideal R) (hJP : IsPermissibleCenter R J P) :
    (ofStep T J).IsPermissible := by
  intro n
  cases n with
  | zero => exact hJP
  | succ n => exact Or.inl rfl

/-- `ofStep` is residually separable algebraic if `R₁` is over `R`. -/
theorem ofStep_isResiduallySeparableAlgebraic (J : Ideal R)
    (hsep : RingHom.IsResiduallySeparableAlgebraic (R := R) (R' := T.ring) T.toRing) :
    (ofStep T J).IsResiduallySeparableAlgebraic := by
  intro n
  cases n with
  | zero => exact hsep
  | succ n =>
    exact RingHom.isResiduallySeparableAlgebraic_of_bijective _
      (MonoidalTransform.top_toRing_bijective T.ring)

end OfStep

end MonoidalSequence

end OfStepSeq

/-! ### Frame transforms along a sequence (Remark 3, pp. 263–264) -/

section Transport

variable {A B : Type u} [CommRing A] [IsRegularLocalRing A] [CommRing B] [IsRegularLocalRing B]

open Classical in
/-- A ring isomorphism carries a regular system of parameters to a regular system of
parameters. -/
theorem isRegularSystemOfParameters_image_ringEquiv (e : A ≃+* B) {s : Finset A}
    (h : IsRegularSystemOfParameters A s) : IsRegularSystemOfParameters B (s.image e) := by
  obtain ⟨hspan, hcard⟩ := h
  refine ⟨?_, ?_⟩
  · rw [Finset.coe_image, ← Ideal.map_span, hspan]
    exact map_ringEquiv_maximalIdeal e
  · rw [Finset.card_image_of_injective _ e.injective, hcard, ringKrullDim_eq_of_ringEquiv e]

open Classical in
/-- A ring isomorphism preserves the property "can be extended to a regular system of
parameters". -/
theorem extendsToRSOP_image_ringEquiv (e : A ≃+* B) {t : Finset A} (h : ExtendsToRSOP A t) :
    ExtendsToRSOP B (t.image e) := by
  obtain ⟨s, hts, hs⟩ := h
  exact ⟨s.image e, Finset.image_subset_image hts, isRegularSystemOfParameters_image_ringEquiv e hs⟩

open Classical in
/-- The regular frame `(S; e(z₁), …, e(z_r))` of `B` obtained from a regular frame
`(S; z₁, …, z_r)` of `A` and a ring isomorphism `e : A ≃+* B` (the structure map is
`S → A → B`).  Used to move the frames of the monoidal transforms `(S.transform β).ring` of a
sequence to the rings `R_{β+1}` of the sequence, and the frame of `R` to `R₀`. -/
noncomputable def RegularFrame.transport (F : RegularFrame A) (e : A ≃+* B) :
    RegularFrame B where
  S := F.S
  algebra := ((e : A →+* B).comp (algebraMap F.S A)).toAlgebra
  isLocalHom := by
    show IsLocalHom ((e : A →+* B).comp (algebraMap F.S A))
    infer_instance
  r := F.r
  z := fun j => e (F.z j)
  z_injective := e.injective.comp F.z_injective
  extends_rsop := by
    have h := extendsToRSOP_image_ringEquiv e F.extends_rsop
    rwa [Finset.image_image] at h
  quot_bijective := by
    have hmap : Ideal.span (Set.range fun j => e (F.z j)) =
        (Ideal.span (Set.range F.z)).map (e : A →+* B) := by
      rw [Ideal.map_span, ← Set.range_comp]
      rfl
    let φ := Ideal.quotientEquiv (Ideal.span (Set.range F.z))
      (Ideal.span (Set.range fun j => e (F.z j))) e hmap
    have hcomp : (Ideal.Quotient.mk (Ideal.span (Set.range fun j => e (F.z j)))).comp
        ((e : A →+* B).comp (algebraMap F.S A)) =
        (φ : A ⧸ Ideal.span (Set.range F.z) →+* _).comp
          ((Ideal.Quotient.mk (Ideal.span (Set.range F.z))).comp (algebraMap F.S A)) := by
      ext s
      rfl
    show Function.Bijective ((Ideal.Quotient.mk (Ideal.span (Set.range fun j => e (F.z j)))).comp
      ((e : A →+* B).comp (algebraMap F.S A)))
    rw [hcomp]
    exact φ.bijective.comp F.quot_bijective

end Transport

namespace MonoidalSequence

variable (S : MonoidalSequence.{u})

/-- Remark 3, pp. 263–264: "we can find a sequence of regular frames `(S_β; z₁^{(β)}, …, z_r^{(β)})`
of `R_β` for all `β ≤ ᾱ` such that `(S_β; z₁^{(β)}, …, z_r^{(β)})` is a frame transform of
`(S_{β−1}; z₁^{(β−1)}, …, z_r^{(β−1)})` in `R_β` for all `β ≥ 1`, where
`(S₀; z₁^{(0)}, …, z_r^{(0)})` denotes `(S; z₁, …, z_r)`. … We shall call
`(S_ᾱ; z₁^{(ᾱ)}, …, z_r^{(ᾱ)})` a *frame transform of `(S; z₁, …, z_r)` in `R_ᾱ` along the
sequence* `{(R_α, P_{α−1})}`."

A chain of frame transforms of length `n` starting at the regular frame `F₀` of `R₀`: regular
frames `frame β` of `R_β` (only `β ≤ n` matter) with `frame 0 = F₀`, and for `β < n` a frame
transform `step β` of `frame β` in the monoidal transform `R_β[x⁻¹P_β]_{M'}` (§8,
`RegularFrame.FrameTransform`) which is `frame (β + 1)` once carried to `R_{β+1}` along
`S.equiv β`.  (The denominators are not required to lie in `P_β ∩ S_β`; that they can be so
chosen is asserted in Remark 3, see `HasDenominatorsInCenters`.) -/
@[blueprint "def:III.9-frame-transform-along"
  (statement := /-- Let $\{(R_\alpha,P_{\alpha-1})\}$ be a sequence of monoidal transforms of
    $R$ (\cref{def:III.9-sequence}), $(S;z_1,\dots,z_r)$ a regular frame of $R$
    (\cref{def:III.9}) and $\bar\alpha\ge0$. A sequence of regular frames
    $(S_\beta;z^{(\beta)}_1,\dots,z^{(\beta)}_r)$ of $R_\beta$ for $\beta\le\bar\alpha$ such that
    $(S_\beta;z^{(\beta)}_1,\dots,z^{(\beta)}_r)$ is a frame transform of
    $(S_{\beta-1};z^{(\beta-1)}_1,\dots,z^{(\beta-1)}_r)$ in $R_\beta$
    (\cref{def:III.8-frame-transform}) for all $\beta\ge1$, where
    $(S_0;z^{(0)}_1,\dots,z^{(0)}_r)$ denotes $(S;z_1,\dots,z_r)$; then
    $(S_{\bar\alpha};z^{(\bar\alpha)}_1,\dots,z^{(\bar\alpha)}_r)$ is called a \emph{frame
    transform of $(S;z_1,\dots,z_r)$ in $R_{\bar\alpha}$ along the sequence}
    $\{(R_\alpha,P_{\alpha-1})\}$. (Remark 3, pp.~263--264.)

    (Formalization note: the frames of the monoidal transforms $R_{\beta-1}[x^{-1}P_{\beta-1}]
    _{M'}$ are carried to $R_\beta$, and the frame of $R$ to $R_0$, along the given ring
    isomorphisms; the denominators are not required to lie in $P_{\beta-1}\cap S_{\beta-1}$,
    Remark~3 asserting that they can be so taken.) -/)
  (latexEnv := "definition")]
structure FrameTransformAlong (F₀ : RegularFrame (S.ring 0)) (n : ℕ) where
  /-- The regular frames `(S_β; z^{(β)})` of `R_β` (only `β ≤ n` matter). -/
  frame : ∀ β : ℕ, RegularFrame (S.ring β)
  /-- `(S₀; z^{(0)}) = (S; z)`. -/
  frame_zero : frame 0 = F₀
  /-- The frame transform of `(S_β; z^{(β)})` in the monoidal transform `R_{β+1}` of `R_β`. -/
  step : ∀ β, β < n → (frame β).FrameTransform (S.transform β)
  /-- `(S_{β+1}; z^{(β+1)})` is that frame transform, carried to `R_{β+1}`. -/
  frame_succ : ∀ β (h : β < n),
    frame (β + 1) = RegularFrame.transport (step β h).toRegularFrame (S.equiv β)

/-- Remark 3, p. 264: "Here the denominator of the above frame transform
`(S_β; z₁^{(β)}, …, z_r^{(β)})` of `(S_{β−1}; z₁^{(β−1)}, …, z_r^{(β−1)})` can be taken in
`P_{β−1} ∩ S_{β−1}`": every denominator is the image of an element of `S_β` lying in `P_β`. -/
def FrameTransformAlong.HasDenominatorsInCenters {S : MonoidalSequence.{u}}
    {F₀ : RegularFrame (S.ring 0)} {n : ℕ} (c : S.FrameTransformAlong F₀ n) : Prop :=
  ∀ β (h : β < n), ∃ x : (c.frame β).S,
    algebraMap (c.frame β).S (S.ring β) x ∈ S.center β ∧
      (c.step β h).x = (S.transform β).toRing (algebraMap (c.frame β).S (S.ring β) x)

end MonoidalSequence

/-- Remark 3, p. 264: "`(S_ᾱ; z₁^{(ᾱ)}, …, z_r^{(ᾱ)})` [is] a frame transform of
`(S; z₁, …, z_r)` in `R_ᾱ` along the sequence `{(R_α, P_{α−1})}`": `G` is the last frame of a chain
of frame transforms of length `ᾱ` starting at the frame of `R₀` corresponding to `(S; z₁, …, z_r)`.
-/
@[blueprint "def:III.9-frame-transform-along"
  (statement := /-- A regular frame $G$ of $R_{\bar\alpha}$ is a frame transform of
    $(S;z_1,\dots,z_r)$ in $R_{\bar\alpha}$ along the sequence if it is the last member
    $(S_{\bar\alpha};z^{(\bar\alpha)}_1,\dots,z^{(\bar\alpha)}_r)$ of such a sequence of frame
    transforms. (Remark 3, p.~264.) -/)
  (latexEnv := "definition")]
def RegularFrame.IsFrameTransformAlong {R : Type u} [CommRing R] [IsRegularLocalRing R]
    (F : RegularFrame R) (S : MonoidalSequence.{u}) (e : R ≃+* S.ring 0) (n : ℕ)
    (G : RegularFrame (S.ring n)) : Prop :=
  ∃ c : S.FrameTransformAlong (F.transport e) n, c.frame n = G

/-! ### Remark 3 (pp. 263–264) -/

section Remark3

variable {R : Type u} [CommRing R] [IsRegularLocalRing R] [IsDomain R]

/-! #### Auxiliary results for Remark 3 and Definition 13 -/

section Remark3Aux

/-- In a local domain, if a principal ideal `(a)`, `a ≠ 0`, is generated by a set `G`, then it is
generated by one element of `G`: `a = ∑ bᵢ gᵢ`, `gᵢ = cᵢ a`, so `∑ bᵢ cᵢ = 1` and some `bᵢ cᵢ`
is a unit. -/
theorem exists_mem_span_singleton_eq_of_span_eq {B : Type*} [CommRing B] [IsLocalRing B]
    [IsDomain B] {a : B} (ha : a ≠ 0) (G : Set B) (h : Ideal.span {a} = Ideal.span G) :
    ∃ g ∈ G, Ideal.span {g} = Ideal.span {a} := by
  have haG : a ∈ Ideal.span G := h ▸ Ideal.mem_span_singleton_self a
  obtain ⟨n, f, g, hsum⟩ := Submodule.mem_span_set'.mp haG
  have hgc : ∀ i, ∃ c, (g i : B) = c * a := fun i => by
    have : (g i : B) ∈ Ideal.span {a} := h ▸ Ideal.subset_span (g i).2
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp this
    exact ⟨c, hc.symm⟩
  choose c hc using hgc
  have h1 : (∑ i, f i * c i) = 1 := by
    have : (∑ i, f i * c i) * a = 1 * a := by
      rw [one_mul, Finset.sum_mul]
      conv_rhs => rw [← hsum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [smul_eq_mul, hc i]
      ring
    exact mul_right_cancel₀ ha this
  have : ∃ i, f i * c i ∉ maximalIdeal B := by
    by_contra hcon
    push Not at hcon
    have : (∑ i, f i * c i) ∈ maximalIdeal B := Ideal.sum_mem _ fun i _ => hcon i
    rw [h1] at this
    exact (maximalIdeal.isMaximal B).ne_top ((Ideal.eq_top_iff_one _).mpr this)
  obtain ⟨i, hi⟩ := this
  have hu : IsUnit (f i * c i) := by
    by_contra hu
    exact hi hu
  refine ⟨g i, (g i).2, ?_⟩
  rw [hc i, Ideal.span_singleton_mul_left_unit (isUnit_of_mul_isUnit_right hu)]

/-- An element of a regular system of parameters has order `1` along the maximal ideal. -/
theorem ordElem_maximalIdeal_eq_one_of_mem_extendsToRSOP {A : Type u} [CommRing A]
    [IsRegularLocalRing A] {K : Finset A} (h : ExtendsToRSOP A K) {k : A} (hk : k ∈ K) :
    Ideal.ordElem (maximalIdeal A) k = 1 := by
  refine le_antisymm ?_ ?_
  · exact_mod_cast Ideal.ordElem_le_of_notMem (m := 1) (h.notMem_maximalIdeal_sq hk)
  · exact_mod_cast Ideal.le_ordElem (ν := 1) (by rw [pow_one]; exact h.mem_maximalIdeal hk)

end Remark3Aux

section Remark3Frames

/-- The denominator of a frame transform can be taken in `P ∩ S` (the generator of `PR₁` is the
image of an element of the coefficient ring): if `(z)R ⊆ P` and all the quotients `z_j/x` of the
generator `x` of `PR₁` are non-units, then `PR₁ = (x₀)R₁` for some `x₀ ∈ P ∩ S`.  (Nakayama:
`P R₁ = (P ∩ S) R₁ + (x) 𝔪₁`, since `P = (P ∩ S) + (z)R` and `z_j ∈ x 𝔪₁`.) -/
theorem RegularFrame.exists_mem_span_eq_of_nonunit (F : RegularFrame R) {P : Ideal R}
    (T : MonoidalTransform R P) [IsRegularLocalRing T.ring] (hzP : F.idealZ ≤ P)
    {w : Fin F.r → T.ring} (hw : ∀ j, T.toRing T.x * w j = T.toRing (F.z j))
    (hnu : ∀ j, ¬ IsUnit (w j)) :
    ∃ x : F.S, algebraMap F.S R x ∈ P ∧
      P.map T.toRing = Ideal.span {T.toRing (algebraMap F.S R x)} := by
  classical
  have hxP : Ideal.span {T.toRing T.x} = P.map T.toRing := T.span_xR_eq_map
  have hwM : ∀ j, w j ∈ maximalIdeal T.ring := fun j => hnu j
  have hx0 : T.toRing T.x ≠ 0 := fun h0 =>
    T.x_ne_zero (MonoidalTransform.toRing_injective T (h0.trans (map_zero _).symm))
  set I : Ideal T.ring :=
    (P.comap (algebraMap F.S R)).map (T.toRing.comp (algebraMap F.S R)) with hI
  have hIle : I ≤ Ideal.span {T.toRing T.x} := by
    rw [hxP, hI, Ideal.map_le_iff_le_comap]
    intro s hs
    rw [Ideal.mem_comap]
    exact Ideal.mem_map_of_mem _ hs
  have hN : Ideal.span {T.toRing T.x} ≤ I ⊔ maximalIdeal T.ring • Ideal.span {T.toRing T.x} := by
    rw [hxP, Ideal.map_le_iff_le_comap]
    intro p hp
    rw [Ideal.mem_comap]
    obtain ⟨s, hs⟩ := F.quot_bijective.2 (Ideal.Quotient.mk _ p)
    have hsz : algebraMap F.S R s - p ∈ F.idealZ := Ideal.Quotient.eq.mp hs
    have hsP : algebraMap F.S R s ∈ P := by
      have h2 := add_mem (hzP hsz) hp
      rwa [sub_add_cancel] at h2
    have hp' : T.toRing p = T.toRing (algebraMap F.S R s) -
        T.toRing (algebraMap F.S R s - p) := by
      rw [map_sub]
      ring
    rw [hp']
    refine sub_mem (Ideal.mem_sup_left ?_) (Ideal.mem_sup_right ?_)
    · exact Ideal.mem_map_of_mem (T.toRing.comp (algebraMap F.S R)) hsP
    · obtain ⟨c, hc⟩ := (Ideal.mem_span_range_iff_exists_fun).mp hsz
      rw [← hc, map_sum, Ideal.smul_eq_mul]
      refine Ideal.sum_mem _ fun j _ => ?_
      rw [map_mul, ← hw j]
      have hcomm : T.toRing (c j) * (T.toRing T.x * w j) =
          (T.toRing (c j) * w j) * T.toRing T.x := by ring
      rw [hcomm]
      exact Ideal.mul_mem_mul (Ideal.mul_mem_left _ _ (hwM j))
        (Ideal.mem_map_of_mem _ T.x_mem)
  have hfg : (Ideal.span {T.toRing T.x}).FG := ⟨{T.toRing T.x}, by simp⟩
  have hle : Ideal.span {T.toRing T.x} ≤ I :=
    Submodule.le_of_le_smul_of_le_jacobson_bot hfg (IsLocalRing.maximalIdeal_le_jacobson ⊥) hN
  obtain ⟨g, hg, hgspan⟩ := exists_mem_span_singleton_eq_of_span_eq hx0
    (((fun s : F.S => T.toRing (algebraMap F.S R s)) '' (P.comap (algebraMap F.S R))))
    (le_antisymm hle hIle)
  obtain ⟨s, hs, rfl⟩ := hg
  exact ⟨s, hs, hxP.symm.trans hgspan.symm⟩

namespace RegularFrame

variable {F : RegularFrame R} {P : Ideal R} {T : MonoidalTransform R P}
  [IsRegularLocalRing T.ring]

/-- Rescaling the denominator of a frame transform by a unit `v` of `R₁`: `(S₁; v⁻¹ w₁, …)` is the
frame transform with denominator `x v` (the denominator is only determined up to a unit,
p. 253). -/
noncomputable def FrameTransform.rescale (FT : F.FrameTransform T) (v : T.ringˣ) :
    F.FrameTransform T where
  x := FT.x * v
  span_x := by rw [Ideal.span_singleton_mul_right_unit v.isUnit]; exact FT.span_x
  TS := FT.TS
  β := FT.β
  canonical := FT.canonical
  isRegular := FT.isRegular
  w := fun j => ((v⁻¹ : T.ringˣ) : T.ring) * FT.w j
  mul_w := fun j => by
    rw [← FT.mul_w j]
    calc FT.x * (v : T.ring) * (((v⁻¹ : T.ringˣ) : T.ring) * FT.w j)
        = FT.x * ((v : T.ring) * ((v⁻¹ : T.ringˣ) : T.ring)) * FT.w j := by ring
      _ = FT.x * FT.w j := by rw [Units.mul_inv, mul_one]
  extends_rsop := by
    classical
    have h := FT.extends_rsop.image_of_associated (fun a => ((v⁻¹ : T.ringˣ) : T.ring) * a)
      (fun a _ b _ hab => by simpa using hab)
      (fun a _ => ⟨v⁻¹, mul_comm _ _⟩)
    rwa [Finset.image_image] at h
  quot_bijective := by
    have hspan : Ideal.span (Set.range fun j => ((v⁻¹ : T.ringˣ) : T.ring) * FT.w j) =
        Ideal.span (Set.range FT.w) := by
      refine le_antisymm (Ideal.span_le.mpr ?_) (Ideal.span_le.mpr ?_)
      · rintro _ ⟨j, rfl⟩
        exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨j, rfl⟩)
      · rintro _ ⟨j, rfl⟩
        have : FT.w j = (v : T.ring) * (((v⁻¹ : T.ringˣ) : T.ring) * FT.w j) := by
          rw [← mul_assoc, Units.mul_inv, one_mul]
        rw [SetLike.mem_coe, this]
        exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨j, rfl⟩)
    show Function.Bijective ((Ideal.Quotient.mk (Ideal.span (Set.range fun j =>
      ((v⁻¹ : T.ringˣ) : T.ring) * FT.w j))).comp FT.β)
    rw [hspan]
    exact FT.quot_bijective

/-- The denominator of `rescale`. -/
theorem FrameTransform.rescale_x (FT : F.FrameTransform T) (v : T.ringˣ) :
    (FT.rescale v).x = FT.x * v := rfl

/-- Given a frame transform, the denominator may be replaced by any generator of `PR₁`. -/
theorem exists_frameTransform_x_eq [P.IsPrime] [IsRegularLocalRing (R ⧸ P)] (x : F.S)
    (hxP : algebraMap F.S R x ∈ P)
    (hx : P.map T.toRing = Ideal.span {T.toRing (algebraMap F.S R x)})
    {w : Fin F.r → T.ring} (hw : ∀ j, T.toRing (algebraMap F.S R x) * w j = T.toRing (F.z j))
    (hnu : ∀ j, ¬ IsUnit (w j)) :
    ∃ FT : F.FrameTransform T, FT.x = T.toRing (algebraMap F.S R x) := by
  have hex : F.AdmitsFrameTransform T :=
    (RegularFrame.admitsFrameTransform_iff (F := F) T).mpr ⟨x, hxP, hx, w, hw, hnu⟩
  obtain ⟨FT⟩ := hex
  obtain ⟨u, hu⟩ := Ideal.span_singleton_eq_span_singleton.mp (FT.span_x.trans hx)
  exact ⟨FT.rescale u, hu⟩

end RegularFrame

end Remark3Frames

section Remark3Chain

namespace RegularFrame

/-- The trivial regular frame `(R; )` of `R` (`r = 0`, `S = R`). -/
noncomputable def trivial (A : Type u) [CommRing A] [IsRegularLocalRing A] : RegularFrame A where
  S := A
  r := 0
  z := fun i => i.elim0
  z_injective := fun i => i.elim0
  extends_rsop := by
    classical
    obtain ⟨-, W, hW⟩ := (isRegularLocalRing_iff_exists_rsop A).mp inferInstance
    have : Finset.image (fun i : Fin 0 => (i.elim0 : A)) Finset.univ = ∅ := by simp
    rw [this]
    exact ⟨W, Finset.empty_subset _, hW⟩
  quot_bijective := by
    have hr : Set.range (fun i : Fin 0 => (i.elim0 : A)) = ∅ := Set.range_eq_empty _
    rw [hr, Ideal.span_empty]
    refine ⟨fun a b h => ?_, fun y => ⟨Quotient.out y, ?_⟩⟩
    · have := Ideal.Quotient.eq.mp h
      simpa [sub_eq_zero] using this
    · exact Ideal.Quotient.mk_surjective y |>.choose_spec

/-- The frame transform of a frame in the trivial monoidal transform with center `R` (`P = R`,
denominator `1`). -/
noncomputable def topFrameTransform (F : RegularFrame R) {P : Ideal R} (hP : P = ⊤)
    (T : MonoidalTransform R P) [IsRegularLocalRing T.ring] : F.FrameTransform T :=
  let hcomap : P.comap (algebraMap F.S R) = ⊤ := by rw [hP]; exact Ideal.comap_top
  let TS : MonoidalTransform F.S (P.comap (algebraMap F.S R)) :=
    Classical.choice (MonoidalTransform.nonempty_of_eq_top hcomap)
  let eS : TS.ring ≃+* F.S := (RingEquiv.ofBijective TS.toRing
    (MonoidalSequence.toRing_bijective_of_eq_top_aux TS hcomap)).symm
  let eT : R ≃+* T.ring := RingEquiv.ofBijective T.toRing
    (MonoidalSequence.toRing_bijective_of_eq_top_aux T hP)
  have hloc : IsLocalHom ((eT : R →+* T.ring).comp ((algebraMap F.S R).comp
      (eS : TS.ring →+* F.S))) := by
    have : IsLocalHom (eS : TS.ring →+* F.S) := IsLocalHom.of_surjective _ eS.surjective
    have : IsLocalHom (eT : R →+* T.ring) := IsLocalHom.of_surjective _ eT.surjective
    infer_instance
  { x := 1
    span_x := by rw [MonoidalSequence.map_eq_top_of_eq_top_aux T hP, Ideal.span_singleton_one]
    TS := TS
    β := (eT : R →+* T.ring).comp ((algebraMap F.S R).comp (eS : TS.ring →+* F.S))
    canonical := ⟨hloc, by
      refine RingHom.ext fun s => ?_
      simp only [RingHom.coe_comp, Function.comp_apply, RingHom.coe_coe]
      have h1 : eS (TS.toRing s) = s := (RingEquiv.ofBijective TS.toRing
        (MonoidalSequence.toRing_bijective_of_eq_top_aux TS hcomap)).symm_apply_apply s
      rw [h1]
      rfl⟩
    isRegular := IsRegularLocalRing.of_ringEquiv eS.symm
    w := fun j => T.toRing (F.z j)
    mul_w := fun j => one_mul _
    extends_rsop := by
      classical
      have h := extendsToRSOP_image_ringEquiv eT F.extends_rsop
      rwa [Finset.image_image] at h
    quot_bijective := by
      have hmap : Ideal.span (Set.range fun j => T.toRing (F.z j)) =
          (Ideal.span (Set.range F.z)).map (eT : R →+* T.ring) := by
        rw [Ideal.map_span, ← Set.range_comp]
        rfl
      let φ := Ideal.quotientEquiv (Ideal.span (Set.range F.z))
        (Ideal.span (Set.range fun j => T.toRing (F.z j))) eT hmap
      have hcomp : (Ideal.Quotient.mk (Ideal.span (Set.range fun j => T.toRing (F.z j)))).comp
          ((eT : R →+* T.ring).comp ((algebraMap F.S R).comp (eS : TS.ring →+* F.S))) =
          (φ : R ⧸ Ideal.span (Set.range F.z) →+* _).comp
            (((Ideal.Quotient.mk (Ideal.span (Set.range F.z))).comp (algebraMap F.S R)).comp
              (eS : TS.ring →+* F.S)) := by
        ext s
        rfl
      show Function.Bijective ((Ideal.Quotient.mk (Ideal.span (Set.range fun j =>
        T.toRing (F.z j)))).comp ((eT : R →+* T.ring).comp ((algebraMap F.S R).comp
          (eS : TS.ring →+* F.S))))
      rw [hcomp]
      exact φ.bijective.comp (F.quot_bijective.comp eS.bijective) }

/-- If `(z)R ⊆ P` and all quotients `z_j/x` (`x` the generator of `PR₁` given by `T`) are
non-units, then the frame transform exists with a denominator in `P ∩ S`. -/
theorem exists_denominator_frameTransform (F : RegularFrame R) {P : Ideal R} [P.IsPrime]
    [IsRegularLocalRing (R ⧸ P)] (T : MonoidalTransform R P) [IsRegularLocalRing T.ring]
    (hzP : F.idealZ ≤ P)
    (hnu : ∀ (j : Fin F.r) (w : T.ring), T.toRing T.x * w = T.toRing (F.z j) → ¬ IsUnit w) :
    ∃ x : F.S, algebraMap F.S R x ∈ P ∧
      ∃ FT : F.FrameTransform T, FT.x = T.toRing (algebraMap F.S R x) := by
  have hxP : Ideal.span {T.toRing T.x} = P.map T.toRing := T.span_xR_eq_map
  have hex : ∀ j, ∃ w, T.toRing T.x * w = T.toRing (F.z j) := fun j => by
    have : T.toRing (F.z j) ∈ Ideal.span {T.toRing T.x} := by
      rw [hxP]
      exact Ideal.mem_map_of_mem _ (hzP (Ideal.subset_span ⟨j, rfl⟩))
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp this
    exact ⟨c, by rw [mul_comm]; exact hc⟩
  choose w hw using hex
  obtain ⟨x, hxPx, hx⟩ := F.exists_mem_span_eq_of_nonunit T hzP hw
    (fun j => hnu j (w j) (hw j))
  obtain ⟨u, hu⟩ := Ideal.span_singleton_eq_span_singleton.mp (hxP.trans hx)
  -- `π x₀ * u = π x`
  refine ⟨x, hxPx, ?_⟩
  refine exists_frameTransform_x_eq (F := F) (T := T) x hxPx hx
    (w := fun j => ((u⁻¹ : T.ringˣ) : T.ring) * w j) (fun j => ?_) (fun j hwj => ?_)
  · rw [← hu, ← hw j]
    calc T.toRing T.x * (u : T.ring) * (((u⁻¹ : T.ringˣ) : T.ring) * w j)
        = T.toRing T.x * ((u : T.ring) * ((u⁻¹ : T.ringˣ) : T.ring)) * w j := by ring
      _ = T.toRing T.x * w j := by rw [Units.mul_inv, mul_one]
  · refine hnu j (w j) (hw j) ?_
    have h2 := (Units.isUnit u).mul hwj
    rwa [Units.mul_inv_cancel_left] at h2

end RegularFrame

end Remark3Chain

section Remark3Chain2

namespace MonoidalSequence

variable (S : MonoidalSequence.{u})

/-- The denominator of the frame transform `FT` of a frame `G` of `R_β` in the monoidal transform
`R_{β+1}` is the image of an element of `S_β` lying in the center `P_β` (Remark 3, p. 264: "can be
taken in `P_{β−1} ∩ S_{β−1}`"). -/
def IsDenominatorInCenter (β : ℕ) (G : RegularFrame (S.ring β))
    (FT : G.FrameTransform (S.transform β)) : Prop :=
  ∃ x : G.S, algebraMap G.S (S.ring β) x ∈ S.center β ∧
    FT.x = (S.transform β).toRing (algebraMap G.S (S.ring β) x)

open Classical in
/-- The frames `(S_β; z^{(β)})` of Remark 3, chosen step by step: the transform of the previous
frame with a denominator in `P_β ∩ S_β` if there is one (and a trivial frame otherwise). -/
noncomputable def chainFrame (F₀ : RegularFrame (S.ring 0)) :
    ∀ β : ℕ, RegularFrame (S.ring β)
  | 0 => F₀
  | β + 1 =>
    if h : ∃ FT : (chainFrame F₀ β).FrameTransform (S.transform β),
        S.IsDenominatorInCenter β _ FT then
      RegularFrame.transport (Classical.choose h).toRegularFrame (S.equiv β)
    else RegularFrame.trivial _

/-- The next frame of `chainFrame` when a good step exists. -/
theorem chainFrame_succ_of_exists (F₀ : RegularFrame (S.ring 0)) {β : ℕ}
    (h : ∃ FT : (S.chainFrame F₀ β).FrameTransform (S.transform β),
      S.IsDenominatorInCenter β _ FT) :
    S.chainFrame F₀ (β + 1) =
      RegularFrame.transport (Classical.choose h).toRegularFrame (S.equiv β) := by
  rw [chainFrame, dif_pos h]

/-- A chain of frame transforms with denominators in the centers exists as soon as each step
exists. -/
theorem exists_frameTransformAlong_of_forall_exists (F₀ : RegularFrame (S.ring 0)) (n : ℕ)
    (hex : ∀ β < n, ∃ FT : (S.chainFrame F₀ β).FrameTransform (S.transform β),
      S.IsDenominatorInCenter β _ FT) :
    ∃ c : S.FrameTransformAlong F₀ n, c.HasDenominatorsInCenters :=
  ⟨{ frame := S.chainFrame F₀
     frame_zero := rfl
     step := fun β h => Classical.choose (hex β h)
     frame_succ := fun β h => S.chainFrame_succ_of_exists F₀ (hex β h) },
   fun β h => Classical.choose_spec (hex β h)⟩

end MonoidalSequence

end Remark3Chain2

section Remark3Chain3

omit [IsDomain R] in
/-- The invariant of the induction in the proof of Remark 3 (third assertion): the members of the
regular frame `G` of `R_β` are strict transforms of the members of the regular frame `F` of `R`
along the sequence (p. 264: the `z_j^{(ᾱ)}` are "a system of strict monoidal transforms `z_j^{(ᾱ)}`
of `z_j`", Definition 13). -/
def MonoidalSequence.IsStrictFrame (Sq : MonoidalSequence.{u}) (F : RegularFrame R)
    (e : R ≃+* Sq.ring 0) (β : ℕ) (G : RegularFrame (Sq.ring β)) : Prop :=
  ∃ hr : G.r = F.r, ∀ j : Fin G.r,
    Sq.IsStrictTransformElem e (F.z (Fin.cast hr j)) β (G.z j)

omit [IsDomain R] in
/-- The frame `F` of `R` is carried to `R_0` by `e`. -/
theorem MonoidalSequence.IsStrictFrame.zero (Sq : MonoidalSequence.{u}) (F : RegularFrame R)
    (e : R ≃+* Sq.ring 0) : Sq.IsStrictFrame F e 0 (F.transport e) :=
  ⟨rfl, fun _ => rfl⟩

omit [IsDomain R] in
/-- For a `J`-stable regular frame `F`, the members of a frame `G` of `R_β` which are strict
transforms of the members of `F` have order `1` along the center `P_β ≠ R_β` (Definition 11, with
`ν_M(z_j) = 1`, `z_j` being part of a regular system of parameters). -/
theorem MonoidalSequence.IsStrictFrame.ordElem_center_eq_one [Hironaka.HironakaCitedResults.{u}] {F : RegularFrame R} {J : Ideal R}
    (hF : F.IsJStable J) {Sq : MonoidalSequence.{u}} {e : R ≃+* Sq.ring 0}
    (h0 : Sq.ideal 0 = J.map e) (hperm : Sq.IsPermissible)
    (hsep : Sq.IsResiduallySeparableAlgebraic) {αb : ℕ}
    (hnu : nuStar (Sq.ring αb) (Sq.ideal αb) = nuStar R J)
    (htau : ∀ a, 1 ≤ a → a ≤ t R J → tau (Sq.ring αb) (Sq.ideal αb) a = tau R J a)
    {β : ℕ} (hβ : β ≤ αb) {G : RegularFrame (Sq.ring β)} (hG : Sq.IsStrictFrame F e β G)
    (hc : Sq.center β ≠ ⊤) (j : Fin G.r) : Ideal.ordElem (Sq.center β) (G.z j) = 1 := by
  classical
  have hmono := MonoidalSequence.nuStar_t_tau_eq_of_le J Sq e h0 hperm hsep αb hnu htau
  obtain ⟨hr, hz⟩ := hG
  have := (hF (Fin.cast hr j) Sq e h0 hperm hsep β (hmono β hβ).1 (hmono β hβ).2.1
    (hmono β hβ).2.2 (G.z j) (hz j)).2 hc
  rw [this]
  exact ordElem_maximalIdeal_eq_one_of_mem_extendsToRSOP F.extends_rsop
    (Finset.mem_image_of_mem _ (Finset.mem_univ _))

omit [IsDomain R] in
/-- For a `J`-stable regular frame `F` and a proper center `P_β`, the ideal `(z^{(β)})R_β` of a
frame `G` of strict transforms of the members of `F` is contained in `P_β`. -/
theorem MonoidalSequence.IsStrictFrame.idealZ_le_center [Hironaka.HironakaCitedResults.{u}] {F : RegularFrame R} {J : Ideal R}
    (hF : F.IsJStable J) {Sq : MonoidalSequence.{u}} {e : R ≃+* Sq.ring 0}
    (h0 : Sq.ideal 0 = J.map e) (hperm : Sq.IsPermissible)
    (hsep : Sq.IsResiduallySeparableAlgebraic) {αb : ℕ}
    (hnu : nuStar (Sq.ring αb) (Sq.ideal αb) = nuStar R J)
    (htau : ∀ a, 1 ≤ a → a ≤ t R J → tau (Sq.ring αb) (Sq.ideal αb) a = tau R J a)
    {β : ℕ} (hβ : β ≤ αb) {G : RegularFrame (Sq.ring β)} (hG : Sq.IsStrictFrame F e β G)
    (hc : Sq.center β ≠ ⊤) : G.idealZ ≤ Sq.center β := by
  rw [RegularFrame.idealZ, Ideal.span_le]
  rintro _ ⟨j, rfl⟩
  have h1 : G.z j ∈ Sq.center β ^ 1 :=
    Ideal.mem_pow_of_ordElem (by
      rw [MonoidalSequence.IsStrictFrame.ordElem_center_eq_one hF h0 hperm hsep hnu htau hβ hG hc j]
      rfl)
  rwa [pow_one] at h1

omit [IsDomain R] in
/-- The step `β → β + 1` of the induction of Remark 3: a frame `G` of `R_β` whose members are
strict transforms of the members of the `J`-stable frame `F` has a frame transform in `R_{β+1}`
with a denominator in `P_β ∩ S_β` (Remark 3, second assertion; for the center `R_β` the frame
transform with denominator `1`). -/
theorem MonoidalSequence.IsStrictFrame.exists_isDenominatorInCenter [Hironaka.HironakaCitedResults.{u}] {F : RegularFrame R}
    {J : Ideal R} (hF : F.IsJStable J) {Sq : MonoidalSequence.{u}} {e : R ≃+* Sq.ring 0}
    (h0 : Sq.ideal 0 = J.map e) (hperm : Sq.IsPermissible)
    (hsep : Sq.IsResiduallySeparableAlgebraic) {αb : ℕ}
    (hnu : nuStar (Sq.ring αb) (Sq.ideal αb) = nuStar R J)
    (htau : ∀ a, 1 ≤ a → a ≤ t R J → tau (Sq.ring αb) (Sq.ideal αb) a = tau R J a)
    {β : ℕ} (hβ : β < αb) {G : RegularFrame (Sq.ring β)} (hG : Sq.IsStrictFrame F e β G) :
    ∃ FT : G.FrameTransform (Sq.transform β), Sq.IsDenominatorInCenter β G FT := by
  classical
  have hmono := MonoidalSequence.nuStar_t_tau_eq_of_le J Sq e h0 hperm hsep αb hnu htau
  have hreg := hperm.hasRegularCenters
  by_cases hc : Sq.center β = ⊤
  · refine ⟨RegularFrame.topFrameTransform G hc (Sq.transform β), 1, ?_, ?_⟩
    · rw [map_one, hc]
      exact Submodule.mem_top
    · show (1 : (Sq.transform β).ring) = _
      rw [map_one, map_one]
  · obtain ⟨hP, hS⟩ := ((hreg β).2).resolve_left hc
    have : (Sq.center β).IsPrime := hP
    have : IsRegularLocalRing (Sq.ring β ⧸ Sq.center β) := hS
    have hz1 := MonoidalSequence.IsStrictFrame.ordElem_center_eq_one hF h0 hperm hsep hnu htau
      hβ.le hG hc
    have hzP : G.idealZ ≤ Sq.center β :=
      MonoidalSequence.IsStrictFrame.idealZ_le_center hF h0 hperm hsep hnu htau hβ.le hG hc
    obtain ⟨hr, hz⟩ := hG
    have hnu' : ∀ (j : Fin G.r) (w : (Sq.transform β).ring),
        (Sq.transform β).toRing (Sq.transform β).x * w =
          (Sq.transform β).toRing (G.z j) → ¬ IsUnit w := by
      intro j w hw hunit
      have hstr := Sq.isStrictTransformElem_succ_of_center_ne_top e hreg (hz j) hc
        (ν := 1) (by rw [hz1 j]; rfl) (x := (Sq.transform β).toRing (Sq.transform β).x)
        (Sq.transform β).span_xR_eq_map (w := w) (by rwa [pow_one])
      have h2 := (hF (Fin.cast hr j) Sq e h0 hperm hsep (β + 1) (hmono (β + 1) hβ).1
        (hmono (β + 1) hβ).2.1 (hmono (β + 1) hβ).2.2 (Sq.equiv β w) hstr).1
      rw [ordElem_maximalIdeal_eq_one_of_mem_extendsToRSOP F.extends_rsop
        (Finset.mem_image_of_mem _ (Finset.mem_univ _))] at h2
      have h3 := Ideal.ordElem_eq_zero_of_isUnit (hunit.map (Sq.equiv β))
      rw [h3] at h2
      exact absurd h2 (by simp)
    obtain ⟨x, hxP, FT, hFT⟩ :=
      RegularFrame.exists_denominator_frameTransform G (Sq.transform β) hzP hnu'
    exact ⟨FT, x, hxP, hFT⟩

omit [IsDomain R] in
/-- The invariant propagates: the transport to `R_{β+1}` of any frame transform of a frame `G` of
`R_β` of strict transforms of the members of `F` is again a frame of strict transforms of the
members of `F`. -/
theorem MonoidalSequence.IsStrictFrame.transport_frameTransform [Hironaka.HironakaCitedResults.{u}] {F : RegularFrame R}
    {J : Ideal R} (hF : F.IsJStable J) {Sq : MonoidalSequence.{u}} {e : R ≃+* Sq.ring 0}
    (h0 : Sq.ideal 0 = J.map e) (hperm : Sq.IsPermissible)
    (hsep : Sq.IsResiduallySeparableAlgebraic) {αb : ℕ}
    (hnu : nuStar (Sq.ring αb) (Sq.ideal αb) = nuStar R J)
    (htau : ∀ a, 1 ≤ a → a ≤ t R J → tau (Sq.ring αb) (Sq.ideal αb) a = tau R J a)
    {β : ℕ} (hβ : β < αb) {G : RegularFrame (Sq.ring β)} (hG : Sq.IsStrictFrame F e β G)
    (FT : G.FrameTransform (Sq.transform β)) :
    Sq.IsStrictFrame F e (β + 1) (RegularFrame.transport FT.toRegularFrame (Sq.equiv β)) := by
  classical
  have hreg := hperm.hasRegularCenters
  obtain ⟨hr, hz⟩ := hG
  refine ⟨hr, fun j => ?_⟩
  by_cases hc : Sq.center β = ⊤
  · have h1 := Sq.isStrictTransformElem_succ_of_center_eq_top e (hz j) hc
    have hunit : IsUnit FT.x := by
      have := FT.span_x
      rw [MonoidalSequence.map_eq_top_of_eq_top_aux (Sq.transform β) hc] at this
      exact Ideal.span_singleton_eq_top.mp this
    have h1' : Ideal.span {Sq.equiv β ((Sq.transform β).toRing (G.z j))} =
        Sq.strictAlong (Ideal.span {e (F.z (Fin.cast hr j))}) (β + 1) := h1
    refine Eq.trans ?_ h1'
    show Ideal.span {Sq.equiv β (FT.w j)} = _
    rw [← FT.mul_w j, map_mul]
    exact (Ideal.span_singleton_mul_left_unit (hunit.map (Sq.equiv β)) _).symm
  · exact Sq.isStrictTransformElem_succ_of_center_ne_top e hreg (hz j) hc (ν := 1)
      (MonoidalSequence.IsStrictFrame.ordElem_center_eq_one hF h0 hperm hsep hnu htau hβ.le
        ⟨hr, hz⟩ hc j) (x := FT.x) FT.span_x (w := FT.w j)
      (by rw [pow_one]; exact FT.mul_w j)

omit [IsDomain R] in
/-- The third assertion of Remark 3, in the form used below: for a `J`-stable regular frame `F`
and a permissible residually separable algebraic sequence with `ν*`, `t`, `τ^{(a)}` unchanged up
to `ᾱ`, there is a chain of frame transforms of length `ᾱ` with all denominators in the centers.
(The frames `z^{(β)}` of the chain are strict transforms of the `z_j` along the sequence; this is
the invariant of the induction, `MonoidalSequence.IsStrictFrame`.) -/
theorem exists_frameTransformAlong_of_isJStable [Hironaka.HironakaCitedResults.{u}] (F : RegularFrame R) (J : Ideal R)
    (hF : F.IsJStable J) (Sq : MonoidalSequence.{u}) (e : R ≃+* Sq.ring 0)
    (h0 : Sq.ideal 0 = J.map e) (hperm : Sq.IsPermissible)
    (hsep : Sq.IsResiduallySeparableAlgebraic) (αb : ℕ)
    (hnu : nuStar (Sq.ring αb) (Sq.ideal αb) = nuStar R J)
    (htau : ∀ a, 1 ≤ a → a ≤ t R J → tau (Sq.ring αb) (Sq.ideal αb) a = tau R J a) :
    ∃ c : Sq.FrameTransformAlong (F.transport e) αb, c.HasDenominatorsInCenters := by
  classical
  let G := Sq.chainFrame (F.transport e)
  have hinv : ∀ β ≤ αb, Sq.IsStrictFrame F e β (G β) := by
    intro β
    induction β with
    | zero => exact fun _ => MonoidalSequence.IsStrictFrame.zero Sq F e
    | succ β ih =>
      intro hβ
      have hI := ih (by omega)
      have hexβ := MonoidalSequence.IsStrictFrame.exists_isDenominatorInCenter hF h0 hperm
        hsep hnu htau (by omega) hI
      have hG : G (β + 1) = RegularFrame.transport (Classical.choose hexβ).toRegularFrame
          (Sq.equiv β) := Sq.chainFrame_succ_of_exists _ hexβ
      rw [hG]
      exact MonoidalSequence.IsStrictFrame.transport_frameTransform hF h0 hperm hsep hnu htau
        (by omega) hI _
  exact Sq.exists_frameTransformAlong_of_forall_exists _ _ fun β hβ =>
    MonoidalSequence.IsStrictFrame.exists_isDenominatorInCenter hF h0 hperm hsep hnu htau hβ
      (hinv β hβ.le)

end Remark3Chain3

section Remark3Exist

/-- A retraction of the chart algebra: if `P = (x) + 𝔭` and `x` is a non-zero-divisor modulo `𝔭`
(`R/𝔭` a domain, `x ∉ 𝔭`), the quotient map `R → R/𝔭` extends to a ring homomorphism
`R[x⁻¹P] → R/𝔭` (`p/x ↦ c̄` for `p = cx + q`, `q ∈ 𝔭`). -/
theorem exists_ringHom_blowupAlgebra {R : Type u} [CommRing R] [IsRegularLocalRing R]
    [IsDomain R] (x : R) (𝔭 P : Ideal R) (hP : P = Ideal.span {x} ⊔ 𝔭) [IsDomain (R ⧸ 𝔭)]
    (hx𝔭 : x ∉ 𝔭) (hx0 : x ≠ 0) :
    ∃ ψ : blowupAlgebra R P x →+* R ⧸ 𝔭,
      ∀ r, ψ (algebraMap R (blowupAlgebra R P x) r) = Ideal.Quotient.mk 𝔭 r := by
  classical
  let C := R ⧸ 𝔭
  let ρ : R →+* C := Ideal.Quotient.mk 𝔭
  let L := FractionRing C
  let ρ' : R →+* L := (algebraMap C L).comp ρ
  have hj : Function.Injective (algebraMap C L) := IsFractionRing.injective C L
  have hρx : ρ x ≠ 0 := fun h => hx𝔭 (Ideal.Quotient.eq_zero_iff_mem.mp h)
  have hρ'x : IsUnit (ρ' x) := by
    rw [isUnit_iff_ne_zero]
    exact fun h => hρx (hj (by simpa [ρ'] using h))
  let K := FractionRing R
  have hxK : IsUnit (algebraMap R K x) := by
    rw [isUnit_iff_ne_zero]
    exact (map_ne_zero_iff _ (IsFractionRing.injective R K)).mpr hx0
  have hgK : ∀ y : Submonoid.powers x, IsUnit (algebraMap R K (y : R)) := by
    rintro ⟨y, n, rfl⟩
    rw [map_pow]
    exact hxK.pow n
  have hgL : ∀ y : Submonoid.powers x, IsUnit (ρ' (y : R)) := by
    rintro ⟨y, n, rfl⟩
    rw [map_pow]
    exact hρ'x.pow n
  let ι : Localization.Away x →+* K := IsLocalization.lift (M := Submonoid.powers x) hgK
  let Φ : Localization.Away x →+* L := IsLocalization.lift (M := Submonoid.powers x) hgL
  have hιalg : ∀ r, ι (algebraMap R (Localization.Away x) r) = algebraMap R K r := fun r =>
    IsLocalization.lift_eq hgK r
  have hΦalg : ∀ r, Φ (algebraMap R (Localization.Away x) r) = ρ' r := fun r =>
    IsLocalization.lift_eq hgL r
  have hι : Function.Injective ι := by
    refine (IsLocalization.lift_injective_iff (M := Submonoid.powers x) hgK).mpr fun a b => ?_
    have h1 : Function.Injective (algebraMap R (Localization.Away x)) :=
      IsLocalization.injective _ (powers_le_nonZeroDivisors_of_noZeroDivisors hx0)
    exact ⟨fun h => congrArg _ (h1 h), fun h => by rw [IsFractionRing.injective R K h]⟩
  -- every element of `R[x⁻¹P]` comes from `R[x⁻¹]`, with image in `C`
  have hA : ∀ b ∈ blowupAlgebra R P x, ∃ a : Localization.Away x, ι a = b ∧
      Φ a ∈ (algebraMap C L).range := by
    intro b hb
    unfold blowupAlgebra at hb
    induction hb using Algebra.adjoin_induction with
    | mem y hy =>
      obtain ⟨p, hp, rfl⟩ := hy
      rw [hP] at hp
      obtain ⟨c, q, hq, hcq⟩ := Ideal.mem_span_singleton_sup.mp hp
      let a := IsLocalization.mk' (Localization.Away x) p (⟨x, Submonoid.mem_powers x⟩ :
        Submonoid.powers x)
      have hxx : ρ' p = ρ' x * ρ' c := by
        rw [← hcq, map_add, map_mul]
        have : ρ' q = 0 := by
          simp only [ρ', RingHom.comp_apply, ρ]
          rw [Ideal.Quotient.eq_zero_iff_mem.mpr hq, map_zero]
        rw [this, add_zero, mul_comm]
      refine ⟨a, ?_, ⟨ρ c, ?_⟩⟩
      · rw [IsLocalization.lift_mk'_spec]
        have hxK0 : algebraMap R K x ≠ 0 := (isUnit_iff_ne_zero.mp hxK)
        show algebraMap R K p = algebraMap R K x * (algebraMap R K p / algebraMap R K x)
        rw [mul_comm]
        exact (div_mul_cancel₀ _ hxK0).symm
      · refine Eq.symm ?_
        rw [IsLocalization.lift_mk'_spec]
        exact hxx
    | algebraMap r =>
      exact ⟨algebraMap R _ r, hιalg r, ⟨ρ r, (hΦalg r).symm⟩⟩
    | add y z _ _ hy hz =>
      obtain ⟨a, ha, hΦa⟩ := hy
      obtain ⟨a', ha', hΦa'⟩ := hz
      exact ⟨a + a', by rw [map_add, ha, ha'], by rw [map_add]; exact add_mem hΦa hΦa'⟩
    | mul y z _ _ hy hz =>
      obtain ⟨a, ha, hΦa⟩ := hy
      obtain ⟨a', ha', hΦa'⟩ := hz
      exact ⟨a * a', by rw [map_mul, ha, ha'], by rw [map_mul]; exact mul_mem hΦa hΦa'⟩
  have hmemA : ∀ b : blowupAlgebra R P x, ∃ a : Localization.Away x, ι a = b := fun b => by
    obtain ⟨a, ha, -⟩ := hA b b.2
    exact ⟨a, ha⟩
  let eι : Localization.Away x ≃+* ι.range := RingEquiv.ofBijective ι.rangeRestrict
    ⟨fun a b hab => hι (congrArg Subtype.val hab), ι.rangeRestrict_surjective⟩
  let e1 : ι.range ≃+* Localization.Away x := eι.symm
  let ψ0 : blowupAlgebra R P x →+* Localization.Away x :=
    (e1 : ι.range →+* Localization.Away x).comp
      ((blowupAlgebra R P x).val.toRingHom.codRestrict ι.range hmemA)
  have hψ0 : ∀ b, ι (ψ0 b) = b := fun b => by
    have := eι.apply_symm_apply (⟨(b : K), hmemA b⟩ : ι.range)
    exact congrArg Subtype.val this
  have hrange : ∀ b, Φ (ψ0 b) ∈ (algebraMap C L).range := fun b => by
    obtain ⟨a, ha, hΦa⟩ := hA b b.2
    have : ψ0 b = a := hι (by rw [hψ0 b, ha])
    rw [this]
    exact hΦa
  let eC : C ≃+* (algebraMap C L).range := RingEquiv.ofBijective (algebraMap C L).rangeRestrict
    ⟨fun a b hab => hj (congrArg Subtype.val hab), (algebraMap C L).rangeRestrict_surjective⟩
  let ψ2 : blowupAlgebra R P x →+* C :=
    (eC.symm : (algebraMap C L).range →+* C).comp
      ((Φ.comp ψ0).codRestrict (algebraMap C L).range hrange)
  refine ⟨ψ2, fun r => hj ?_⟩
  have h1 : algebraMap C L (ψ2 (algebraMap R (blowupAlgebra R P x) r)) =
      Φ (ψ0 (algebraMap R (blowupAlgebra R P x) r)) :=
    congrArg Subtype.val (eC.apply_symm_apply
      ⟨Φ (ψ0 (algebraMap R (blowupAlgebra R P x) r)), hrange _⟩)
  rw [h1]
  have h2 : ψ0 (algebraMap R (blowupAlgebra R P x) r) = algebraMap R (Localization.Away x) r :=
    hι (by rw [hψ0, hιalg]; rfl)
  rw [h2, hΦalg]
  rfl

/-- A monoidal transform whose prime `M'` is the kernel of a retraction
`ε : R[x⁻¹P] → R/M` of `R → R[x⁻¹P]` is residually rational. -/
theorem MonoidalTransform.isResiduallyRational_of_ker_eq {R : Type u} [CommRing R]
    [IsRegularLocalRing R] [IsDomain R] {P : Ideal R} (τ : MonoidalTransform R P)
    (ε : blowupAlgebra R P τ.x →+* ResidueField R)
    (hε : ∀ r, ε (algebraMap R (blowupAlgebra R P τ.x) r) = IsLocalRing.residue R r)
    (hker : τ.M' = RingHom.ker ε) :
    RingHom.IsResiduallyRational (R := R) (R' := τ.ring) τ.toRing := by
  have hg : ∀ s : τ.M'.primeCompl, IsUnit (ε s) := fun s => by
    refine isUnit_iff_ne_zero.mpr fun h => ?_
    have h2 : (s : blowupAlgebra R P τ.x) ∈ RingHom.ker ε := RingHom.mem_ker.mpr h
    rw [← hker] at h2
    exact s.2 h2
  let ε' : τ.ring →+* ResidueField R := IsLocalization.lift (M := τ.M'.primeCompl) hg
  have hε'alg : ε'.comp (algebraMap (blowupAlgebra R P τ.x) τ.ring) = ε :=
    IsLocalization.lift_comp hg
  have hε'toRing : ∀ r, ε' (τ.toRing r) = IsLocalRing.residue R r := fun r => by
    show ε' (algebraMap (blowupAlgebra R P τ.x) τ.ring (algebraMap R _ r)) = _
    rw [← RingHom.comp_apply, hε'alg, hε]
  have hloc : IsLocalHom ε' := IsLocalHom.of_surjective ε' fun y => by
    obtain ⟨r, rfl⟩ := IsLocalRing.residue_surjective y
    exact ⟨τ.toRing r, hε'toRing r⟩
  intro y
  obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective y
  obtain ⟨r, hr⟩ := IsLocalRing.residue_surjective (ε' a)
  refine ⟨IsLocalRing.residue R r, ?_⟩
  rw [ResidueField.map_residue, eq_comm, ← sub_eq_zero, ← map_sub,
    IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal]
  intro hunit
  have h1 := hunit.map ε'
  rw [map_sub, hε'toRing, hr, sub_self] at h1
  exact not_isUnit_zero h1

/-- (Existence of a residually rational chart point.)  For a regular system of parameters `S`
of `R` and `x ∈ T ⊆ S`, the prime `P = (T)` has a monoidal transform with `T.x = x` whose
residue field is that of `R`: the quotient map `R → R/𝔭`, `𝔭 = (T ∖ {x})`, extends to the chart
`R[x⁻¹P]` (`exists_ringHom_blowupAlgebra`), and the kernel of the composite `R[x⁻¹P] → R/M` is a
maximal ideal `M'` over `M` with `R[x⁻¹P]/M' = R/M`. -/
theorem exists_monoidalTransform_isResiduallyRational {R : Type u} [CommRing R]
    [IsRegularLocalRing R] [IsDomain R] {S T : Finset R} (hS : IsRegularSystemOfParameters R S)
    (hTS : T ⊆ S) {x : R} (hx : x ∈ T) :
    ∃ τ : MonoidalTransform R (Ideal.span (T : Set R)), τ.x = x ∧
      RingHom.IsResiduallyRational (R := R) (R' := τ.ring) τ.toRing := by
  classical
  set P := Ideal.span (T : Set R) with hP
  set 𝔭 := Ideal.span ((T.erase x : Finset R) : Set R) with h𝔭
  have hTerase : T.erase x ⊆ S := (Finset.erase_subset _ _).trans hTS
  obtain ⟨hCreg, -⟩ := rsop_quotient hS hTerase
  have hCdom : IsDomain (R ⧸ 𝔭) := isDomain_of_isRegularLocalRing _
  have hxS : x ∈ S := hTS hx
  have hx𝔭 : x ∉ 𝔭 := rsop_notMem_span hS hTerase hxS (Finset.notMem_erase x T)
  have hxM2 : x ∉ maximalIdeal R ^ 2 := fun h =>
    rsop_notMem_span_erase_sup_sq hS hxS (Ideal.mem_sup_right h)
  have hx0 : x ≠ 0 := fun h => hxM2 (h ▸ zero_mem _)
  have hPeq : P = Ideal.span {x} ⊔ 𝔭 := by
    rw [hP, h𝔭, ← Ideal.span_insert, ← Finset.coe_insert, Finset.insert_erase hx]
  have h𝔭M : 𝔭 ≤ maximalIdeal R := by
    rw [h𝔭, Ideal.span_le]
    intro a ha
    have := Finset.mem_of_mem_erase (Finset.mem_coe.mp ha)
    exact hS.1 ▸ Ideal.subset_span (hTS this)
  obtain ⟨ψ, hψ⟩ := exists_ringHom_blowupAlgebra x 𝔭 P hPeq hx𝔭 hx0
  let ε : blowupAlgebra R P x →+* ResidueField R := (Ideal.Quotient.factor h𝔭M).comp ψ
  have hε : ∀ r, ε (algebraMap R (blowupAlgebra R P x) r) = IsLocalRing.residue R r := by
    intro r
    show Ideal.Quotient.factor h𝔭M (ψ (algebraMap R (blowupAlgebra R P x) r)) = _
    rw [hψ, Ideal.Quotient.factor_mk]
    rfl
  have hεsurj : Function.Surjective ε := fun y => by
    obtain ⟨r, rfl⟩ := IsLocalRing.residue_surjective y
    exact ⟨algebraMap R _ r, hε r⟩
  have hmax : (RingHom.ker ε).IsMaximal := RingHom.ker_isMaximal_of_surjective ε hεsurj
  let τ : MonoidalTransform R P :=
    { x := x
      x_mem := Ideal.subset_span hx
      x_ne_zero := hx0
      M' := RingHom.ker ε
      isPrime := hmax.isPrime
      le := Ideal.map_le_iff_le_comap.mpr fun m hm => by
        rw [Ideal.mem_comap, RingHom.mem_ker, hε]
        exact (IsLocalRing.residue_eq_zero_iff m).mpr hm }
  exact ⟨τ, rfl, τ.isResiduallyRational_of_ker_eq ε hε rfl⟩

end Remark3Exist
section Remark3OneStep

/-- `ν*`, `t` and `τ^{(a)}` of `J₀ = J.map e` are those of `J`. -/
theorem MonoidalSequence.nuStar_t_tau_zero [Hironaka.HironakaCitedResults.{u}] {R : Type u} [CommRing R] [IsRegularLocalRing R]
    (J : Ideal R) (S : MonoidalSequence.{u}) (e : R ≃+* S.ring 0) (h0 : S.ideal 0 = J.map e) :
    nuStar (S.ring 0) (S.ideal 0) = nuStar R J ∧ t (S.ring 0) (S.ideal 0) = t R J ∧
      ∀ a, 1 ≤ a → a ≤ t R J → tau (S.ring 0) (S.ideal 0) a = tau R J a := by
  obtain ⟨hN0, ht0, hτ0⟩ := nuStar_t_tau_map_of_bijective_aux (e : R →+* S.ring 0) e.bijective J
  rw [← show S.ideal 0 = J.map (e : R →+* S.ring 0) from h0] at hN0 ht0 hτ0
  exact ⟨hN0, ht0, hτ0⟩

variable {R : Type u} [CommRing R] [IsRegularLocalRing R] [IsDomain R]

/-- Definition 11 at `ᾱ = 0` for the one-step sequence `R, R₁, R₁, …`: `ν_P(z) = ν_M(z)`. -/
theorem ordElem_eq_of_isJStable_of_monoidalTransform [Hironaka.HironakaCitedResults.{u}] {J : Ideal R} {z : R}
    (hz : IsJStable J z) {P : Ideal R} (hP : P ≠ ⊤) (T : MonoidalTransform R P)
    [IsRegularLocalRing T.ring] (hJP : IsPermissibleCenter R J P)
    (hsep : RingHom.IsResiduallySeparableAlgebraic (R := R) (R' := T.ring) T.toRing) :
    Ideal.ordElem P z = Ideal.ordElem (maximalIdeal R) z := by
  have h0 := MonoidalSequence.nuStar_t_tau_zero J (MonoidalSequence.ofStep T J)
    (MonoidalSequence.ofStepEquiv T J) (MonoidalSequence.ofStep_ideal_zero T J)
  exact (hz (MonoidalSequence.ofStep T J) (MonoidalSequence.ofStepEquiv T J)
    (MonoidalSequence.ofStep_ideal_zero T J) (MonoidalSequence.ofStep_isPermissible T J hJP)
    (MonoidalSequence.ofStep_isResiduallySeparableAlgebraic T J hsep) 0 h0.1 h0.2.1 h0.2.2
    (MonoidalSequence.ofStepEquiv T J z) rfl).2 hP

/-- Definition 11 at `ᾱ = 1` for the one-step sequence: if `ν_M(z) = 1` and the `ν*`, `t`, `τ^{(a)}`
of `J₁` are those of `J`, then the strict transform `w = z/x` of `z` in `R₁` has `ν_{M₁}(w) = 1`,
in particular is a non-unit of `R₁`. -/
theorem ordElem_quotient_eq_of_isJStable_of_monoidalTransform [Hironaka.HironakaCitedResults.{u}] {J : Ideal R} {z : R}
    (hz : IsJStable J z) (hz1 : Ideal.ordElem (maximalIdeal R) z = 1) {P : Ideal R}
    (hP : P ≠ ⊤) (T : MonoidalTransform R P) [IsRegularLocalRing T.ring]
    (hJP : IsPermissibleCenter R J P)
    (hsep : RingHom.IsResiduallySeparableAlgebraic (R := R) (R' := T.ring) T.toRing)
    (hnu : nuStar T.ring (strictTransformIdeal T J) = nuStar R J)
    (ht : t T.ring (strictTransformIdeal T J) = t R J)
    (htau : ∀ a, 1 ≤ a → a ≤ t R J → tau T.ring (strictTransformIdeal T J) a = tau R J a)
    {w : T.ring} (hw : T.toRing T.x * w = T.toRing z) :
    Ideal.ordElem (maximalIdeal T.ring) w = 1 := by
  have hS := (MonoidalSequence.ofStep_isPermissible T J hJP).hasRegularCenters
  have hord : Ideal.ordElem P z = 1 :=
    (ordElem_eq_of_isJStable_of_monoidalTransform hz hP T hJP hsep).trans hz1
  have hw' : T.toRing T.x ^ 1 * w = T.toRing z := by rwa [pow_one]
  have hstr := (MonoidalSequence.ofStep T J).isStrictTransformElem_succ_of_center_ne_top
    (MonoidalSequence.ofStepEquiv T J) hS (z := z) (n := 0)
    (g := MonoidalSequence.ofStepEquiv T J z) rfl hP (ν := 1)
    (by show Ideal.ordElem P z = ((1 : ℕ) : ℕ∞); rw [hord]; rfl) (x := T.toRing T.x)
    T.span_xR_eq_map (w := w) hw'
  have h1 := MonoidalSequence.ofStep_ideal_one T J
  have := (hz (MonoidalSequence.ofStep T J) (MonoidalSequence.ofStepEquiv T J)
    (MonoidalSequence.ofStep_ideal_zero T J) (MonoidalSequence.ofStep_isPermissible T J hJP)
    (MonoidalSequence.ofStep_isResiduallySeparableAlgebraic T J hsep) 1
    (by rw [h1]; exact hnu) (by rw [h1]; exact ht) (by rw [h1]; exact htau) w hstr).1
  rw [hz1] at this
  exact this

end Remark3OneStep

section Remark3Parts

omit [IsDomain R] in
/-- A residually rational local homomorphism is residually separable algebraic. -/
theorem RingHom.isResiduallySeparableAlgebraic_of_isResiduallyRational {A B : Type u}
    [CommRing A] [CommRing B] [IsLocalRing A] [IsLocalRing B] (φ : A →+* B) [IsLocalHom φ]
    (h : RingHom.IsResiduallyRational φ) : RingHom.IsResiduallySeparableAlgebraic φ := by
  let _ : Algebra (ResidueField A) (ResidueField B) := (ResidueField.map φ).toAlgebra
  show Algebra.IsSeparable (ResidueField A) (ResidueField B)
  have hbij : Function.Bijective (ResidueField.map φ) := ⟨(ResidueField.map φ).injective, h⟩
  refine Algebra.IsSeparable.of_equiv_equiv (A₁ := ResidueField A) (B₁ := ResidueField A)
    (RingEquiv.refl _) (RingEquiv.ofBijective _ hbij) (RingHom.ext fun x => ?_)
  simp [RingHom.algebraMap_toAlgebra]

/-- The ideal `(z)R` is contained in a permissible center `P ≠ (0)` of a `J`-stable frame
(first assertion of Remark 3, for `P ≠ (0)`): apply Definition 11 to the one-step sequence
`R, R₁, R₁, …` with a residually rational monoidal transform `R₁` with center `P`. -/
theorem RegularFrame.idealZ_le_of_isJStable_of_ne_bot [Hironaka.HironakaCitedResults.{u}] (F : RegularFrame R) (J : Ideal R)
    (hF : F.IsJStable J) {P₀ : Ideal R} [P₀.IsPrime] (hP₀ : P₀ ≠ ⊥)
    (hperm₀ : IsPermissibleCenter R J P₀) : F.idealZ ≤ P₀ := by
  classical
  have hne : P₀ ≠ ⊤ := (‹P₀.IsPrime›).ne_top
  obtain ⟨-, -, hreg, -⟩ := hperm₀.resolve_left hne
  obtain ⟨S, T, hSM, hScard, hTS, hTP⟩ := exists_finset_span_eq_prime R P₀ hreg
  have hS : IsRegularSystemOfParameters R S :=
    rsop_of_span_of_card_le hSM (le_of_eq hScard)
  obtain ⟨x, hxT⟩ : T.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    rintro rfl
    exact hP₀ (by rw [← hTP, Finset.coe_empty, Ideal.span_empty])
  obtain ⟨τ, -, hrat⟩ := exists_monoidalTransform_isResiduallyRational hS hTS hxT
  subst hTP
  have hτreg := (τ.isRegularLocalRing_and_isLocalHom_and_span_xR_eq_map ‹_› hP₀ hreg).1
  have hsep := RingHom.isResiduallySeparableAlgebraic_of_isResiduallyRational τ.toRing hrat
  rw [RegularFrame.idealZ, Ideal.span_le]
  rintro _ ⟨j, rfl⟩
  have h1 := ordElem_eq_of_isJStable_of_monoidalTransform (hF j) hne τ
    hperm₀ hsep
  rw [ordElem_maximalIdeal_eq_one_of_mem_extendsToRSOP F.extends_rsop
    (Finset.mem_image_of_mem _ (Finset.mem_univ j))] at h1
  have h2 : F.z j ∈ Ideal.span (T : Set R) ^ 1 := Ideal.mem_pow_of_ordElem (by rw [h1]; rfl)
  rwa [pow_one] at h2

/-- Second assertion of Remark 3. -/
theorem RegularFrame.exists_denominator_of_isJStable [Hironaka.HironakaCitedResults.{u}] (F : RegularFrame R) (J : Ideal R)
    (hF : F.IsJStable J) {P₀ : Ideal R} [P₀.IsPrime] (hperm₀ : IsPermissibleCenter R J P₀)
    (T : MonoidalTransform R P₀) [IsRegularLocalRing T.ring]
    (hsep : RingHom.IsResiduallySeparableAlgebraic (R := R) (R' := T.ring) T.toRing)
    (hnu : nuStar T.ring (strictTransformIdeal T J) = nuStar R J)
    (ht : t T.ring (strictTransformIdeal T J) = t R J)
    (htau : ∀ a, 1 ≤ a → a ≤ t R J → tau T.ring (strictTransformIdeal T J) a = tau R J a) :
    ∃ x : F.S, algebraMap F.S R x ∈ P₀ ∧
      ∃ FT : F.FrameTransform T, FT.x = T.toRing (algebraMap F.S R x) := by
  classical
  have hP₀top : P₀ ≠ ⊤ := (‹P₀.IsPrime›).ne_top
  obtain ⟨-, -, hreg, -⟩ := hperm₀.resolve_left hP₀top
  have hz1 : ∀ j, Ideal.ordElem (maximalIdeal R) (F.z j) = 1 := fun j =>
    ordElem_maximalIdeal_eq_one_of_mem_extendsToRSOP F.extends_rsop
      (Finset.mem_image_of_mem _ (Finset.mem_univ j))
  have hzP : F.idealZ ≤ P₀ := by
    rw [RegularFrame.idealZ, Ideal.span_le]
    rintro _ ⟨j, rfl⟩
    have h1 := ordElem_eq_of_isJStable_of_monoidalTransform (hF j) hP₀top T hperm₀ hsep
    rw [hz1 j] at h1
    have h2 : F.z j ∈ P₀ ^ 1 := Ideal.mem_pow_of_ordElem (by rw [h1]; rfl)
    rwa [pow_one] at h2
  refine F.exists_denominator_frameTransform T hzP fun j w hw hunit => ?_
  have h1 := ordElem_quotient_eq_of_isJStable_of_monoidalTransform (hF j) (hz1 j) hP₀top T
    hperm₀ hsep hnu ht htau hw
  rw [Ideal.ordElem_eq_zero_of_isUnit hunit] at h1
  exact absurd h1 (by simp)

end Remark3Parts

section Remark3Degenerate

/-- `ν^{(i)}((0)) = ∞`: the zero system works for every `ν` since `gr_M((0), R) = 0`. -/
theorem nuI_bot (A : Type u) [CommRing A] [IsRegularLocalRing A] (i : ℕ+) :
    nuI A ⊥ i = ⊤ := by
  have hgr : grIdeal (maximalIdeal A) (⊥ : Ideal A) = ⊥ := by
    rw [grIdeal, Ideal.span_eq_bot]
    rintro _ ⟨a, ha, rfl⟩
    have : a = 0 := ha
    subst this
    rw [initialForm, dif_pos (Ideal.ordElem_eq_top_iff.mpr fun n => zero_mem _)]
  rw [ENat.eq_top_iff_forall_ge]
  intro N
  have hsp : Ideal.span (Set.range fun _ : Fin ((i : ℕ) - 1) =>
      (0 : AssocGraded (maximalIdeal A))) = ⊥ :=
    Ideal.span_eq_bot.mpr (by rintro _ ⟨j, rfl⟩; rfl)
  refine le_iSup₂_of_le N ⟨fun _ => 0, fun j => ⟨?_, 0, zero_mem _⟩, fun μ _ ψ _ => ?_⟩ le_rfl
  · rw [hgr]
    exact zero_mem _
  · rw [hsp, hgr]

/-- `t((0)) = 0`. -/
theorem t_bot (A : Type u) [CommRing A] [IsRegularLocalRing A] : t A ⊥ = 0 := by
  have : muSet A ⊥ = ∅ := by
    ext μ
    simp only [muSet, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_exists]
    intro i h
    rw [nuI_bot] at h
    exact ENat.top_ne_coe μ h
  rw [t, this, Set.ncard_empty]

/-- The strict transform of `(0)` is `(0)`. -/
theorem strictTransformIdeal_bot {R : Type u} [CommRing R] [IsRegularLocalRing R]
    [IsDomain R] {P : Ideal R} (T : MonoidalTransform R P) :
    strictTransformIdeal T ⊥ = ⊥ := by
  rw [strictTransformIdeal, Ideal.span_eq_bot]
  rintro y ⟨x, hx, f, hf, ν, -, hxy⟩
  have hf0 : f = 0 := hf
  subst hf0
  rw [map_zero] at hxy
  have hx0 : x ≠ 0 := by
    intro h0
    have hT0 : T.toRing T.x ≠ 0 := fun h =>
      T.x_ne_zero (MonoidalTransform.toRing_injective T (h.trans (map_zero _).symm))
    apply hT0
    have : T.toRing T.x ∈ Ideal.span {x} := by
      rw [hx]
      exact Ideal.mem_map_of_mem _ T.x_mem
    rw [h0, Ideal.span_singleton_eq_bot.mpr rfl] at this
    exact this
  exact (mul_eq_zero.mp hxy).resolve_left (pow_ne_zero _ hx0)

/-- The degenerate case of the first assertion of Remark 3: `J = (0)` has the permissible center
`P₀ = (0)`, and a `(0)`-stable frame has `(z) = 0`. -/
theorem RegularFrame.idealZ_le_bot_of_isJStable [Hironaka.HironakaCitedResults.{u}] (F : RegularFrame R) (hF : F.IsJStable ⊥) :
    F.idealZ ≤ ⊥ := by
  classical
  rw [RegularFrame.idealZ, Ideal.span_le]
  rintro _ ⟨j, rfl⟩
  exfalso
  obtain ⟨S, hsub, hS⟩ := F.extends_rsop
  have hjS : F.z j ∈ S := hsub (Finset.mem_image_of_mem _ (Finset.mem_univ j))
  obtain ⟨τ, hτx, hrat⟩ :=
    exists_monoidalTransform_isResiduallyRational hS (Finset.Subset.refl S) hjS
  have hprime : (Ideal.span (S : Set R)).IsPrime := hS.1 ▸ (maximalIdeal.isMaximal R).isPrime
  have hreg : IsRegularLocalRing (R ⧸ Ideal.span (S : Set R)) :=
    (rsop_quotient hS (Finset.Subset.refl S)).1
  have hP0 : Ideal.span (S : Set R) ≠ ⊥ := fun h =>
    τ.x_ne_zero ((Submodule.mem_bot R).mp (h ▸ τ.x_mem))
  have hτreg : IsRegularLocalRing τ.ring :=
    (τ.isRegularLocalRing_and_isLocalHom_and_span_xR_eq_map hprime hP0 hreg).1
  have hsep := RingHom.isResiduallySeparableAlgebraic_of_isResiduallyRational τ.toRing hrat
  -- `(span S)` is a permissible center for `(0)`
  have hmax : ((Ideal.span (S : Set R)).map (Ideal.Quotient.mk (⊥ : Ideal R))).IsMaximal := by
    have : Nontrivial (R ⧸ (⊥ : Ideal R)) := Ideal.Quotient.nontrivial_iff.mpr bot_ne_top
    have : IsLocalRing (R ⧸ (⊥ : Ideal R)) :=
      IsLocalRing.of_surjective' (Ideal.Quotient.mk ⊥) Ideal.Quotient.mk_surjective
    rw [hS.1, IsLocalRing.map_maximalIdeal_of_surjective _ Ideal.Quotient.mk_surjective]
    exact maximalIdeal.isMaximal _
  have hJP : IsPermissibleCenter R ⊥ (Ideal.span (S : Set R)) := by
    refine Or.inr ⟨hprime, bot_le, hreg, fun p => ?_⟩
    let _ := Ideal.Quotient.field ((Ideal.span (S : Set R)).map (Ideal.Quotient.mk (⊥ : Ideal R)))
    exact Module.Free.of_divisionRing _ _
  have hz1 : Ideal.ordElem (maximalIdeal R) (F.z j) = 1 :=
    ordElem_maximalIdeal_eq_one_of_mem_extendsToRSOP F.extends_rsop
      (Finset.mem_image_of_mem _ (Finset.mem_univ j))
  have hnuStar : ∀ (A : Type u) [CommRing A] [IsRegularLocalRing A], nuStar A ⊥ =
      toLex fun _ : ℕ+ => (⊤ : ℕ∞) := fun A _ _ => by
    unfold nuStar
    congr 1
    funext i
    exact nuI_bot A i
  have := ordElem_quotient_eq_of_isJStable_of_monoidalTransform (hF j) hz1 hprime.ne_top τ hJP
    hsep (by rw [strictTransformIdeal_bot, hnuStar, hnuStar])
    (by rw [strictTransformIdeal_bot, t_bot, t_bot])
    (fun a ha hat => by rw [t_bot] at hat; omega) (w := 1) (by rw [hτx, mul_one])
  rw [Ideal.ordElem_eq_zero_of_isUnit isUnit_one] at this
  exact absurd this (by simp)

end Remark3Degenerate

section Independence

/-- An identity of sums used in `rsopIndep_of_div`. -/
theorem sum_identity_aux {K ι : Type*} [Field K] [Fintype ι] (n : ℕ) (a0 : K) (a : Fin n → K)
    (ρ : ι → K) (b0 : ι → K) (b : ι → Fin n → K) (x : Fin n → K) :
    (a0 + ∑ j, a j * x j) - ∑ l, ρ l * (b0 l + ∑ j, b l j * x j) =
      (a0 - ∑ l, ρ l * b0 l) + ∑ j, (a j - ∑ l, ρ l * b l j) * x j := by
  simp only [mul_add, Finset.sum_add_distrib, Finset.mul_sum, sub_mul, Finset.sum_sub_distrib,
    Finset.sum_mul]
  rw [Finset.sum_comm (f := fun l j => ρ l * (b l j * x j))]
  have : ∀ l j, ρ l * b l j * x j = ρ l * (b l j * x j) := fun l j => mul_assoc _ _ _
  simp only [this]
  ring

variable {R : Type u} [CommRing R] [IsRegularLocalRing R] [IsDomain R]

/-- The algebraic core of `rsopIndep_of_div`: if `y_k = a_{k0} + ∑ a_{kj} X_j` lie in the maximal
ideal of a local ring `B`, `D_j y_k = a_{kj}` for derivations `D_j`, and `y_i - ∑ β_l y_l ∈ 𝔪²`,
then the residues of `a_{kJ}` satisfy `res a_{iJ} = ∑ res β_l res a_{lJ}` for all `J`. -/
theorem relation_mod_square {S B : Type*} [CommRing S] [CommRing B] [Algebra S B] [IsLocalRing B]
    {m : ℕ} {ι : Type*} (Fe : Finset ι) (i : ι) (y a0 : ι → B) (a : ι → Fin m → B)
    (X : Fin m → B) (D : Fin m → Derivation S B B) (β : ↥Fe → B)
    (hy : ∀ k, y k = a0 k + ∑ j, a k j * X j) (hDy : ∀ k j, D j (y k) = a k j)
    (hyQ : ∀ l : ↥Fe, y l ∈ maximalIdeal B)
    (hg : y i - ∑ l : ↥Fe, β l * y l ∈ maximalIdeal B ^ 2) :
    (∀ j, residue B (a i j) - ∑ l : ↥Fe, residue B (β l) * residue B (a l j) = 0) ∧
      residue B (a0 i) - ∑ l : ↥Fe, residue B (β l) * residue B (a0 l) = 0 := by
  have hEj : ∀ j, residue B (a i j) - ∑ l : ↥Fe, residue B (β l) * residue B (a l j) = 0 := by
    intro j
    have h1 : D j (y i - ∑ l : ↥Fe, β l * y l) ∈ maximalIdeal B := by
      have := derivation_mem_pow_of_mem_pow_succ (maximalIdeal B) (D j) (n := 1) hg
      simpa using this
    have h2 : a i j - ∑ l : ↥Fe, β l * a l j =
        D j (y i - ∑ l : ↥Fe, β l * y l) + ∑ l : ↥Fe, y l * D j (β l) := by
      simp only [map_sub, map_sum, Derivation.leibniz, hDy, smul_eq_mul]
      rw [Finset.sum_add_distrib]
      ring
    have h3 : a i j - ∑ l : ↥Fe, β l * a l j ∈ maximalIdeal B := by
      rw [h2]
      exact add_mem h1 (Ideal.sum_mem _ fun l _ => Ideal.mul_mem_right _ _ (hyQ l))
    have := (residue_eq_zero_iff _).mpr h3
    simpa only [map_sub, map_sum, map_mul] using this
  refine ⟨hEj, ?_⟩
  have hg0 : residue B (y i - ∑ l : ↥Fe, β l * y l) = 0 :=
    (residue_eq_zero_iff _).mpr (Ideal.pow_le_self two_ne_zero hg)
  simp only [map_sub, map_sum, map_mul, hy, map_add] at hg0
  rw [sum_identity_aux m (residue B (a0 i)) (fun j => residue B (a i j))
    (fun l => residue B (β l)) (fun l => residue B (a0 l)) (fun l j => residue B (a l j))
    (fun j => residue B (X j))] at hg0
  have hz : ∑ j, (residue B (a i j) - ∑ l : ↥Fe, residue B (β l) * residue B (a l j)) *
      residue B (X j) = 0 := Finset.sum_eq_zero fun j _ => by rw [hEj j, zero_mul]
  rw [hz, add_zero] at hg0
  exact hg0

/-- The rows `(c_{kJ} mod M)` of the coefficients of `z_k = ∑ c_{kJ} z'_J` in a minimal base `z'` of
`P ⊆ M` are linearly independent over `R/M` if the `z_k` are independent modulo `M²`. -/
theorem row_not_mem_span_of_rsopIndep {R : Type u} [CommRing R] [IsRegularLocalRing R]
    {ι : Type*} [DecidableEq ι] (F : Finset ι) (z : ι → R) (hz : RSOPIndep F z)
    {P : Ideal R} (hPM : P ≤ maximalIdeal R) {r : ℕ} (z' : Fin (r + 1) → R)
    (hzP' : Ideal.span (Set.range z') = P) (c : ι → Fin (r + 1) → R)
    (hc : ∀ k ∈ F, ∑ J, c k J * z' J = z k) {i : ι} (hi : i ∈ F) :
    (fun J => IsLocalRing.residue R (c i J)) ∉ Submodule.span (ResidueField R)
      (Set.range fun l : ↥(F.erase i) => fun J => IsLocalRing.residue R (c l J)) := by
  classical
  let row : ι → Fin (r + 1) → ResidueField R := fun k J => IsLocalRing.residue R (c k J)
  show row i ∉ Submodule.span (ResidueField R) (Set.range fun l : ↥(F.erase i) => row l)
  intro hspan
  obtain ⟨lam, hlam⟩ := (Submodule.mem_span_range_iff_exists_fun (ResidueField R)).mp hspan
  choose lam' hlam' using fun l : ↥(F.erase i) => IsLocalRing.residue_surjective (lam l)
  have hcoefM : ∀ J, c i J - ∑ l : ↥(F.erase i), lam' l * c l J ∈ maximalIdeal R := by
    intro J
    rw [← IsLocalRing.residue_eq_zero_iff, map_sub, map_sum]
    have := congrFun hlam J
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at this
    simp only [map_mul, hlam']
    exact sub_eq_zero.mpr this.symm
  apply (hz i hi).2
  have hzi : z i = ∑ l : ↥(F.erase i), lam' l * z l +
      ∑ J, (c i J - ∑ l : ↥(F.erase i), lam' l * c l J) * z' J := by
    rw [← hc i hi]
    simp only [sub_mul, Finset.sum_sub_distrib, Finset.sum_mul]
    have : ∀ l : ↥(F.erase i), ∑ J, lam' l * c l J * z' J = lam' l * z l := fun l => by
      rw [← hc l (Finset.mem_of_mem_erase l.2), Finset.mul_sum]
      exact Finset.sum_congr rfl fun J _ => by ring
    rw [Finset.sum_comm]
    simp only [this]
    ring
  rw [hzi]
  refine add_mem (Ideal.mem_sup_left (Ideal.sum_mem _ fun l _ => Ideal.mul_mem_left _ _
    (Ideal.subset_span ⟨l, ⟨Finset.mem_of_mem_erase l.2, (Finset.mem_erase.mp l.2).1⟩, rfl⟩)))
    (Ideal.mem_sup_right ?_)
  rw [pow_two]
  exact Ideal.sum_mem _ fun J _ => Ideal.mul_mem_mul (hcoefM J)
    (hPM (hzP' ▸ Ideal.subset_span ⟨J, rfl⟩))

/-- If a vector `row i` over a field `k` is not in the span of the vectors `row l` (`l ∈ Fe`), then
it is not a combination `∑ ρ_l row l` over a field `κ` receiving `k` by `σ'` either. -/
theorem false_of_row_not_mem_span {k κ : Type*} [Field k] [Field κ] (σ' : k →+* κ) {n : ℕ}
    {ι : Type*} [DecidableEq ι] (Fe : Finset ι) (row : ι → Fin n → k) (i : ι)
    (hrow : row i ∉ Submodule.span k (Set.range fun l : ↥Fe => row l)) (ρ : ↥Fe → κ)
    (hE : ∀ J : Fin n, σ' (row i J) = ∑ l : ↥Fe, ρ l * σ' (row l J)) : False := by
  obtain ⟨f, hfi, hfp⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hrow inferInstance
  have hfl : ∀ l : ↥Fe, f (row l) = 0 := fun l => by
    have : f (row l) ∈ (Submodule.span k (Set.range fun l : ↥Fe => row l)).map f :=
      Submodule.mem_map_of_mem (Submodule.subset_span ⟨l, rfl⟩)
    rw [hfp] at this
    exact (Submodule.mem_bot _).mp this
  have hfexp : ∀ x : Fin n → k, f x = ∑ J, x J * f (fun j => if J = j then 1 else 0) := fun x => by
    rw [LinearMap.pi_apply_eq_sum_univ f x]
    simp only [smul_eq_mul]
  have hzero : σ' (f (row i)) = 0 := by
    rw [hfexp (row i), map_sum]
    simp only [map_mul]
    rw [Finset.sum_congr rfl fun J _ => by rw [hE J]]
    simp only [Finset.sum_mul, mul_assoc]
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun l _ => ?_
    rw [← Finset.mul_sum]
    have := congrArg σ' (hfl l)
    rw [hfexp (row l), map_sum] at this
    simp only [map_mul, map_zero] at this
    rw [this, mul_zero]
  exact hfi ((map_eq_zero σ').mp hzero)

/-- The one-step lemma behind the note after Definition 13 (p. 265): if `(z_j)` is independent
modulo `M²` (a part of a regular system of parameters) in `R`, `z_j ∈ P`, and `z_j = x w_j` in a
monoidal transform `R₁` with center `P` (`PR₁ = (x)R₁`) with all `w_j` non-units, then `(w_j)` is
independent modulo `M₁²` in `R₁`.  Proof: modulo `x`, `R₁/(x) = (R/P)[T]_q` and `w_j` becomes the
affine linear form `c_{j0} + ∑ c_{ji} T_i` (`z_j = c_{j0} x + ∑ c_{ji} t_i` for a minimal base
`(x, t_i)` of `P`); a derivative `∂/∂T_i` lowers the order along `q` by one, which turns a relation
among the `w_j` modulo `M₁²` into a relation among the rows `(c_{j·})` over the residue field. -/
theorem rsopIndep_of_div {P : Ideal R} [P.IsPrime] [IsRegularLocalRing (R ⧸ P)]
    (T : MonoidalTransform R P) [IsRegularLocalRing T.ring] {ι : Type*} [DecidableEq ι]
    (F : Finset ι)
    (z : ι → R) (hz : RSOPIndep F z) (hzP : ∀ j ∈ F, z j ∈ P) (w : ι → T.ring)
    (hw : ∀ j ∈ F, T.toRing T.x * w j = T.toRing (z j))
    (hwM : ∀ j ∈ F, w j ∈ maximalIdeal T.ring) : RSOPIndep F w := by
  classical
  intro i hi
  refine ⟨hwM i hi, fun hmem => ?_⟩
  -- minimal generators `(x, t₁, …, t_r)` of `P` and `R₁/(x) = (R/P)[T]_q`
  obtain ⟨S, r, z', hSM, hScard, hinj, hzS, hz0, hzP'⟩ := T.exists_minimal_generators inferInstance
  obtain ⟨q, hq, e, hqC, -, he1, he2⟩ :=
    T.exists_quotient_equiv_localization inferInstance hSM hScard hinj hzS hz0 hzP'
  have hxP : Ideal.span {T.toRing T.x} = P.map T.toRing := T.span_xR_eq_map
  have hx0 : T.toRing T.x ≠ 0 := fun h0 =>
    T.x_ne_zero (MonoidalTransform.toRing_injective T (h0.trans (map_zero _).symm))
  have hu : ∀ j : Fin r, ∃ v : T.ring, T.toRing T.x * v = T.toRing (z' j.succ) := fun j => by
    have : T.toRing (z' j.succ) ∈ Ideal.span {T.toRing T.x} := by
      rw [hxP]
      exact Ideal.mem_map_of_mem _ (hzP' ▸ Ideal.subset_span ⟨j.succ, rfl⟩)
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp this
    exact ⟨c, by rw [mul_comm]; exact hc⟩
  choose u hu using hu
  have hcoef : ∀ k : ι, ∃ c : Fin (r + 1) → R, k ∈ F → ∑ j, c j * z' j = z k := by
    intro k
    by_cases hk : k ∈ F
    · have : z k ∈ Ideal.span (Set.range z') := hzP' ▸ hzP k hk
      obtain ⟨c, hc⟩ := Ideal.mem_span_range_iff_exists_fun.mp this
      exact ⟨c, fun _ => hc⟩
    · exact ⟨0, fun h => absurd h hk⟩
  choose c hc using hcoef
  have hwform : ∀ k ∈ F, w k = T.toRing (c k 0) + ∑ j : Fin r, T.toRing (c k j.succ) * u j := by
    intro k hk
    apply mul_left_cancel₀ hx0
    rw [hw k hk, ← hc k hk, map_sum, Fin.sum_univ_succ, mul_add, Finset.mul_sum]
    simp only [map_mul, hz0, ← hu]
    congr 1
    · ring
    · exact Finset.sum_congr rfl fun j _ => by ring
  let row : ι → Fin (r + 1) → ResidueField R := fun k J => IsLocalRing.residue R (c k J)
  have hPM : P ≤ maximalIdeal R := IsLocalRing.le_maximalIdeal (‹P.IsPrime›).ne_top
  have hrow : row i ∉ Submodule.span (ResidueField R)
      (Set.range fun l : ↥(F.erase i) => row l) :=
    row_not_mem_span_of_rsopIndep F z hz hPM z' hzP' c hc hi
  -- the affine forms `L_k = c_{k0} + ∑ c_{kj} T_j` over `R/P` and the map `ψ : R₁ → (R/P)[T]_q`
  have hX : ∀ j : Fin r, e (algebraMap (MvPolynomial (Fin r) (R ⧸ P))
      (Localization.AtPrime q) (MvPolynomial.X j)) =
        Ideal.Quotient.mk (Ideal.span {T.xR}) (u j) := fun j => (he2 u hu j).2
  let Lk : ι → MvPolynomial (Fin r) (R ⧸ P) := fun k =>
    MvPolynomial.C (Ideal.Quotient.mk P (c k 0)) +
      ∑ j : Fin r, MvPolynomial.C (Ideal.Quotient.mk P (c k j.succ)) * MvPolynomial.X j
  let ψ : T.ring →+* Localization.AtPrime q :=
    (e.symm : T.ring ⧸ Ideal.span {T.xR} →+* _).comp (Ideal.Quotient.mk (Ideal.span {T.xR}))
  have hψLk : ∀ k ∈ F, ψ (w k) = algebraMap _ (Localization.AtPrime q) (Lk k) := by
    intro k hk
    show e.symm (Ideal.Quotient.mk (Ideal.span {T.xR}) (w k)) = _
    rw [e.symm_apply_eq]
    simp only [Lk, map_add, map_sum, map_mul, he1, hX]
    rw [hwform k hk]
    simp only [map_add, map_sum, map_mul]
  have hψsurj : Function.Surjective ψ := fun y => by
    obtain ⟨b, rfl⟩ := e.symm.surjective y
    obtain ⟨t, rfl⟩ := Ideal.Quotient.mk_surjective b
    exact ⟨t, rfl⟩
  have hψM : (maximalIdeal T.ring).map ψ = maximalIdeal (Localization.AtPrime q) := by
    have := IsLocalRing.map_maximalIdeal_of_surjective (R := T.ring)
      (S := Localization.AtPrime q) ψ hψsurj
    exact this
  have hLkQ : ∀ k ∈ F, algebraMap _ (Localization.AtPrime q) (Lk k) ∈
      maximalIdeal (Localization.AtPrime q) := fun k hk => by
    rw [← hψLk k hk, ← hψM]
    exact Ideal.mem_map_of_mem _ (hwM k hk)
  -- the relation `w_i = ∑ b_l w_l + m`, `m ∈ M₁²`
  have hset : w '' ((F : Set ι) \ {i}) = Set.range (fun l : ↥(F.erase i) => w l) := by
    ext y
    constructor
    · rintro ⟨l, ⟨hlF, hlne⟩, rfl⟩
      exact ⟨⟨l, Finset.mem_erase.mpr ⟨hlne, hlF⟩⟩, rfl⟩
    · rintro ⟨⟨l, hl⟩, rfl⟩
      exact ⟨l, ⟨(Finset.mem_erase.mp hl).2, (Finset.mem_erase.mp hl).1⟩, rfl⟩
  rw [hset] at hmem
  obtain ⟨a, ha, m, hm, hsum⟩ := Submodule.mem_sup.mp hmem
  obtain ⟨b, hb⟩ := Ideal.mem_span_range_iff_exists_fun.mp ha
  have hg : algebraMap _ (Localization.AtPrime q) (Lk i) -
      ∑ l : ↥(F.erase i), ψ (b l) * algebraMap _ (Localization.AtPrime q) (Lk l) ∈
        maximalIdeal (Localization.AtPrime q) ^ 2 := by
    have h1 : ψ m = algebraMap _ (Localization.AtPrime q) (Lk i) -
        ∑ l : ↥(F.erase i), ψ (b l) * algebraMap _ (Localization.AtPrime q) (Lk l) := by
      have : m = w i - ∑ l : ↥(F.erase i), b l * w l := by
        rw [hb, ← hsum]
        ring
      rw [this, map_sub, map_sum, hψLk i hi]
      congr 1
      exact Finset.sum_congr rfl fun l _ => by
        rw [map_mul, hψLk l (Finset.mem_of_mem_erase l.2)]
    rw [← h1, ← hψM, ← Ideal.map_pow]
    exact Ideal.mem_map_of_mem _ hm
  -- derivatives: `∂/∂T_j` extends to the localization and lowers the order along `Q` by one
  have hpd : ∀ k (j : Fin r), MvPolynomial.pderiv j (Lk k) =
      MvPolynomial.C (Ideal.Quotient.mk P (c k j.succ)) := by
    intro k j
    simp only [Lk, map_add, map_sum, Derivation.leibniz, MvPolynomial.pderiv_C,
      MvPolynomial.pderiv_X, smul_eq_mul, mul_zero, zero_add, Pi.single_apply]
    simp [Finset.sum_ite_eq']
  -- the reduction `σ' : k = R/M → κ(R₁/(x))`
  have hmkM : ∀ a ∈ maximalIdeal R, Ideal.Quotient.mk P a ∈ maximalIdeal (R ⧸ P) := by
    intro a ha
    have : IsLocalHom (Ideal.Quotient.mk P) :=
      IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective
    exact (IsLocalRing.mem_maximalIdeal _).mpr fun hu =>
      (IsLocalRing.mem_maximalIdeal a).mp ha (isUnit_of_map_unit (Ideal.Quotient.mk P) a hu)
  have hQ : maximalIdeal (Localization.AtPrime q) =
      q.map (algebraMap (MvPolynomial (Fin r) (R ⧸ P)) (Localization.AtPrime q)) :=
    (Localization.AtPrime.map_eq_maximalIdeal (I := q)).symm
  let σ' : ResidueField R →+* IsLocalRing.ResidueField (Localization.AtPrime q) :=
    Ideal.Quotient.lift (maximalIdeal R) ((IsLocalRing.residue (Localization.AtPrime q)).comp
      ((algebraMap (MvPolynomial (Fin r) (R ⧸ P)) (Localization.AtPrime q)).comp
        (MvPolynomial.C.comp (Ideal.Quotient.mk P)))) (fun a ha => by
      simp only [RingHom.comp_apply]
      rw [IsLocalRing.residue_eq_zero_iff, hQ]
      refine Ideal.mem_map_of_mem _ ?_
      have h2 := hmkM a ha
      rw [← hqC] at h2
      exact Ideal.mem_comap.mp h2)
  have hσ' : ∀ a : R, σ' (IsLocalRing.residue R a) =
      IsLocalRing.residue (Localization.AtPrime q)
        (algebraMap (MvPolynomial (Fin r) (R ⧸ P)) (Localization.AtPrime q)
          (MvPolynomial.C (Ideal.Quotient.mk P a))) := fun a => rfl
  clear_value σ'
  -- the equations over the residue field `κ` of `(R/P)[T]_q`
  choose D hD using fun j : Fin r => exists_derivation_of_isLocalization (S := q.primeCompl)
    (B := Localization.AtPrime q) (MvPolynomial.pderiv (R := R ⧸ P) j)
  have hy : ∀ k, algebraMap (MvPolynomial (Fin r) (R ⧸ P)) (Localization.AtPrime q) (Lk k) =
      algebraMap (MvPolynomial (Fin r) (R ⧸ P)) (Localization.AtPrime q)
        (MvPolynomial.C (Ideal.Quotient.mk P (c k 0))) +
        ∑ j : Fin r, algebraMap (MvPolynomial (Fin r) (R ⧸ P)) (Localization.AtPrime q)
          (MvPolynomial.C (Ideal.Quotient.mk P (c k j.succ))) *
          algebraMap (MvPolynomial (Fin r) (R ⧸ P)) (Localization.AtPrime q)
            (MvPolynomial.X j) := by
    intro k
    simp only [Lk, map_add, map_sum, map_mul]
  have hDy : ∀ (k : ι) (j : Fin r), D j (algebraMap (MvPolynomial (Fin r) (R ⧸ P))
      (Localization.AtPrime q) (Lk k)) = algebraMap (MvPolynomial (Fin r) (R ⧸ P))
        (Localization.AtPrime q) (MvPolynomial.C (Ideal.Quotient.mk P (c k j.succ))) := by
    intro k j
    rw [hD j, hpd]
  have hrel := relation_mod_square (S := R ⧸ P) (B := Localization.AtPrime q)
    (F.erase i) i
    (fun k => algebraMap (MvPolynomial (Fin r) (R ⧸ P)) (Localization.AtPrime q) (Lk k))
    (fun k => algebraMap (MvPolynomial (Fin r) (R ⧸ P)) (Localization.AtPrime q)
      (MvPolynomial.C (Ideal.Quotient.mk P (c k 0))))
    (fun k j => algebraMap (MvPolynomial (Fin r) (R ⧸ P)) (Localization.AtPrime q)
      (MvPolynomial.C (Ideal.Quotient.mk P (c k j.succ))))
    (fun j => algebraMap (MvPolynomial (Fin r) (R ⧸ P)) (Localization.AtPrime q)
      (MvPolynomial.X j)) D (fun l => ψ (b l)) ?_ ?_ ?_ ?_
  obtain ⟨hEj, hE0⟩ := hrel
  let ρ : ↥(F.erase i) → IsLocalRing.ResidueField (Localization.AtPrime q) := fun l =>
    IsLocalRing.residue (Localization.AtPrime q) (ψ (b l))
  have hρ : ∀ l, ρ l = IsLocalRing.residue (Localization.AtPrime q) (ψ (b l)) := fun _ => rfl
  clear_value ρ
  have hkey : ∀ (k : ι) (J : Fin (r + 1)), σ' (row k J) =
      IsLocalRing.residue (Localization.AtPrime q)
        (algebraMap (MvPolynomial (Fin r) (R ⧸ P)) (Localization.AtPrime q)
          (MvPolynomial.C (Ideal.Quotient.mk P (c k J)))) := fun k J => hσ' (c k J)
  have hE : ∀ J : Fin (r + 1), σ' (row i J) = ∑ l : ↥(F.erase i), ρ l * σ' (row l J) := by
    intro J
    simp only [hkey, hρ]
    refine Fin.cases ?_ (fun j => ?_) J
    · exact sub_eq_zero.mp hE0
    · exact sub_eq_zero.mp (hEj j)
  exact false_of_row_not_mem_span σ' (F.erase i) row i hrow ρ hE
  · exact hy
  · exact hDy
  · exact fun l => hLkQ l (Finset.mem_of_mem_erase l.2)
  · exact hg

end Independence

/-- Remark 3, pp. 263–264: "Let `(S; z₁, …, z_r)` be a regular frame of `R`. Let `J` be an ideal
in `R`. Suppose `(S; z₁, …, z_r)` is `J`-stable. Then for every prime ideal `P₀` in `R` which is a
permissible center for `J` we have `P₀ ⊇ (z₁, …, z_r)R`. Moreover, for every strict monoidal
transform `(J₁, R₁, P₀)` of `(J, R)` which is permissible for `J` and such that `R₁` is residually
separable algebraic over `R`, and that `ν*(J₁) = ν*(J)`, and `τ*(J₁) = τ*(J)`, we have that
`(S, z₁, …, z_r)` [sic: `(S; z₁, …, z_r)`] admits a frame transform `(S₁; z₁/x, …, z_r/x)` in `R₁`
with a denominator `x ∈ P₀ ∩ S`. Moreover, if `{(J_α, R_α, P_{α−1})}` is a sequence of strict
monoidal transforms of `(J, R)` such that the sequence `{(R_α, P_{α−1})}` is permissible for `J`
and that `R_α` is residually separable algebraic over `R_{α−1}` for all `α ≥ 1` (`R₀ = R`), and if
an index `ᾱ (≥ 1)` is such that `ν*(J_ᾱ) = ν*(J)` and `τ*(J_ᾱ) = τ*(J)`, then we can find a sequence
of regular frames `(S_β; z₁^{(β)}, …, z_r^{(β)})` of `R_β` for all `β ≤ ᾱ` such that
`(S_β; z₁^{(β)}, …, z_r^{(β)})` is a frame transform of `(S_{β−1}; z₁^{(β−1)}, …, z_r^{(β−1)})` in
`R_β` for all `β ≥ 1`, where `(S₀; z₁^{(0)}, …, z_r^{(0)})` denotes `(S; z₁, …, z_r)`. Here the
denominator of the above frame transform … can be taken in `P_{β−1} ∩ S_{β−1}`."

(Formalization notes.
* In the second assertion `P₀` is, as in the first, a prime ideal which is a permissible center
  for `J`; `R₁` is a monoidal transform `T` of `R` with center `P₀`, regular by §2 (hypothesis);
  "with a denominator `x ∈ P₀ ∩ S`" is an element `x` of `S` whose image lies in `P₀` and whose
  image in `R₁` is the denominator of the frame transform (as in Lemma 20).
* In the third assertion the chain of frames is a `FrameTransformAlong` of length `ᾱ` with all
  its denominators in the centers; `τ*` equalities as in the module docstring.)

Deviation from the paper (gap filled; the paper asserts Remark 3 without proof).  (1) Definition 11
is applied, at `ᾱ = 0`, to the one-step sequence `R, R₁, R₁, …` (`MonoidalSequence.ofStep`) with a
residually rational monoidal transform `R₁` with center `P₀`; the existence of such an `R₁` is not
stated in the paper and is proved (`exists_monoidalTransform_isResiduallyRational`: for a minimal
base `T ∋ x` of `P₀`, the chart `R[x⁻¹P₀]` has the rational point `p/x = 0`, `p ∈ (T ∖ {x})`).
The case `P₀ = (0)`, a permissible center of `J = (0)`, is a degenerate case which the paper does
not mention: a `(0)`-stable frame has `(z) = 0` (`idealZ_le_bot_of_isJStable`; take `P = M` and the
chart of `z_j`).  (2) `PR₁ = (x₀)R₁` with `x₀ ∈ P ∩ S` by Nakayama (`P = (P ∩ S) + (z)R` and
`z_j/x ∈ 𝔪₁`), and the frame transform is the one of the criterion of §8
(`admitsFrameTransform_iff`), its denominator rescaled to `x₀`.  (3) The frames `z^{(β)}` are
chosen step by step (`MonoidalSequence.chainFrame`); by induction `z^{(β)}_j` is a strict
transform of `z_j` along the sequence, so that the `J`-stability of `F` (indices `β` and `β + 1`,
where `ν*`, `τ*` are unchanged by Theorem 3) gives `z^{(β)}_j ∈ P_β` and `z^{(β)}_j/x ∈ 𝔪_{β+1}`;
a step with center `R_β` uses the trivial frame transform. -/
@[blueprint "rem:III.9-3"
  (statement := /-- Let $(S;z_1,\dots,z_r)$ be a regular frame of $R$ (\cref{def:III.9}). Let
    $J$ be an ideal in $R$. Suppose $(S;z_1,\dots,z_r)$ is $J$-stable (\cref{def:III.11}). Then
    for every prime ideal $P_0$ in $R$ which is a permissible center for $J$ (\cref{def:III.8})
    we have $P_0\supseteq(z_1,\dots,z_r)R$. Moreover, for every strict monoidal transform
    $(J_1,R_1,P_0)$ of $(J,R)$ which is permissible for $J$ and such that $R_1$ is residually
    separable algebraic over $R$, and that $\nu^*(J_1)=\nu^*(J)$, and $\tau^*(J_1)=\tau^*(J)$, we
    have that $(S,z_1,\dots,z_r)$ [sic: $(S;z_1,\dots,z_r)$] admits a frame transform
    $(S_1;z_1/x,\dots,z_r/x)$ in $R_1$ with a denominator $x\in P_0\cap S$
    (\cref{def:III.8-admits-frame-transform}). Moreover, if
    $\{(J_\alpha,R_\alpha,P_{\alpha-1})\}$ is a sequence of strict monoidal transforms of $(J,R)$
    (\cref{def:III.9-strict-sequence}) such that the sequence $\{(R_\alpha,P_{\alpha-1})\}$ is
    permissible for $J$ (\cref{def:III.9-permissible-sequence}) and that $R_\alpha$ is
    residually separable algebraic over $R_{\alpha-1}$ for all $\alpha\ge1$ ($R_0=R$), and if an
    index $\bar\alpha$ ($\ge1$) is such that $\nu^*(J_{\bar\alpha})=\nu^*(J)$ and
    $\tau^*(J_{\bar\alpha})=\tau^*(J)$, then we can find a sequence of regular frames
    $(S_\beta;z^{(\beta)}_1,\dots,z^{(\beta)}_r)$ of $R_\beta$ for all $\beta\le\bar\alpha$ such
    that $(S_\beta;z^{(\beta)}_1,\dots,z^{(\beta)}_r)$ is a frame transform of
    $(S_{\beta-1};z^{(\beta-1)}_1,\dots,z^{(\beta-1)}_r)$ in $R_\beta$ for all $\beta\ge1$, where
    $(S_0;z^{(0)}_1,\dots,z^{(0)}_r)$ denotes $(S;z_1,\dots,z_r)$. Here the denominator of the
    frame transform $(S_\beta;z^{(\beta)}_1,\dots,z^{(\beta)}_r)$ of
    $(S_{\beta-1};z^{(\beta-1)}_1,\dots,z^{(\beta-1)}_r)$ can be taken in
    $P_{\beta-1}\cap S_{\beta-1}$ (\cref{def:III.9-frame-transform-along}). (Remark 3,
    pp.~263--264.)

    (Formalization note: in the second assertion $P_0$ is a prime permissible center, as in the
    first; $\tau^*(J')=\tau^*(J)$ is $t(J')=t(J)$ with $\tau^{(a)}(J')=\tau^{(a)}(J)$ for
    $1\le a\le t(J)$; that monoidal transforms of $R$ are regular is a lemma of \S2 taken as a
    hypothesis.) -/)
  (proof := /-- No proof is given in the paper. [Editorial gloss, not in the paper: for the
    first assertion apply the $J$-stability of $z_j$ (\cref{def:III.11}) to a one-step sequence
    with center $P_0$: then $\nu_{P_0}(z_j)=\nu_M(z_j)=1$, so $z_j\in P_0$. For the second, the
    $J$-stability of $z_j$ at $\bar\alpha=1$ gives $\nu_{M_1}(z_j/x)=\nu_M(z_j)=1$ for the strict
    transform $z_j/x$ of $z_j$, so all the $z_j/x$ are non-units of $R_1$, and one concludes by
    the criterion of \S8 (\cref{lem:III.8-frame-transform-criterion}), the denominator being
    chosen in $P_0\cap S$ because $P_0=(z_1,\dots,z_r)R+(P_0\cap S)R$. The third assertion
    follows by induction on $\bar\alpha$, applying the second one to the $J_\beta$-stable
    frames obtained at each step, since by \cref{thm:III.3} the equalities
    $\nu^*(J_\beta)=\nu^*(J)$, $\tau^*(J_\beta)=\tau^*(J)$ hold for all $\beta\le\bar\alpha$.]

    \textbf{Deviation from the paper (gap filled).} The paper states Remark~3 without proof; the
    formalization supplies the arguments sketched above, with the following additions that the
    paper does not mention. (1) For the first assertion Definition~11 is applied to the one-step
    sequence $R,R_1,R_1,\dots$ with $R_1$ a \emph{residually rational} monoidal transform with
    center $P_0$; its existence (the chart $R[x^{-1}P_0]$ has the rational point $p/x=0$,
    $p\in(T\setminus\{x\})$, for a minimal base $T\ni x$ of $P_0$) is proved. The case
    $P_0=(0)$ ($J=(0)$) is degenerate and is treated separately: a $(0)$-stable frame has
    $(z)=0$. (2) The denominator $x_0\in P_0\cap S$ is obtained by Nakayama's lemma from
    $P_0R_1=(P_0\cap S)R_1+x\mathfrak m_1$ and the criterion of \S8
    (\cref{lem:III.8-frame-transform-criterion}), whose denominator is rescaled by a unit to
    $x_0$. (3) The frames are chosen step by step; the induction carries the statement that
    $z^{(\beta)}_j$ is a strict transform of $z_j$, which is what lets the $J$-stability of $F$
    be used at the indices $\beta$ and $\beta+1$ (the equalities $\nu^*(J_\beta)=\nu^*(J)$,
    $\tau^*(J_\beta)=\tau^*(J)$ for $\beta\le\bar\alpha$ following from Theorem~3); steps with
    center $R_\beta$ use the trivial frame transform. -/)
  (latexEnv := "remark")]
theorem remark3_frameTransform [Hironaka.HironakaCitedResults.{u}] (F : RegularFrame R) (J : Ideal R) (hF : F.IsJStable J) :
    (∀ (P₀ : Ideal R) [P₀.IsPrime], IsPermissibleCenter R J P₀ → F.idealZ ≤ P₀) ∧
    (∀ (P₀ : Ideal R) [P₀.IsPrime], IsPermissibleCenter R J P₀ →
      ∀ (T : MonoidalTransform R P₀) [IsRegularLocalRing T.ring],
        RingHom.IsResiduallySeparableAlgebraic (R := R) (R' := T.ring) T.toRing →
        nuStar T.ring (strictTransformIdeal T J) = nuStar R J →
        t T.ring (strictTransformIdeal T J) = t R J →
        (∀ a, 1 ≤ a → a ≤ t R J → tau T.ring (strictTransformIdeal T J) a = tau R J a) →
        ∃ x : F.S, algebraMap F.S R x ∈ P₀ ∧
          ∃ FT : F.FrameTransform T, FT.x = T.toRing (algebraMap F.S R x)) ∧
    (∀ (Sq : MonoidalSequence.{u}) (e : R ≃+* Sq.ring 0), Sq.ideal 0 = J.map e →
      Sq.IsPermissible → Sq.IsResiduallySeparableAlgebraic →
      ∀ αb : ℕ, 1 ≤ αb → nuStar (Sq.ring αb) (Sq.ideal αb) = nuStar R J →
        t (Sq.ring αb) (Sq.ideal αb) = t R J →
        (∀ a, 1 ≤ a → a ≤ t R J → tau (Sq.ring αb) (Sq.ideal αb) a = tau R J a) →
        ∃ c : Sq.FrameTransformAlong (F.transport e) αb, c.HasDenominatorsInCenters) := by
  refine ⟨fun P₀ _ hperm => ?_, fun P₀ _ hperm T _ hsep hnu ht htau => ?_,
    fun Sq e h0 hperm hsep αb _ hnu _ htau => ?_⟩
  · -- the first assertion
    have hne : P₀ ≠ ⊤ := (‹P₀.IsPrime›).ne_top
    by_cases hbot : P₀ = ⊥
    · -- the degenerate case `P₀ = (0)`, `J = (0)`
      obtain ⟨-, hJP, -, -⟩ := hperm.resolve_left hne
      have hJ : J = ⊥ := by
        rw [hbot] at hJP
        exact le_bot_iff.mp hJP
      subst hJ
      rw [hbot]
      exact F.idealZ_le_bot_of_isJStable hF
    · exact F.idealZ_le_of_isJStable_of_ne_bot J hF hbot hperm
  · -- the second assertion
    exact F.exists_denominator_of_isJStable J hF hperm T hsep hnu ht htau
  · -- the third assertion
    exact exists_frameTransformAlong_of_isJStable F J hF Sq e h0 hperm hsep αb hnu htau

end Remark3

/-! ### Definition 12 (p. 264) -/

section Definition12

variable {R : Type u} [CommRing R] [IsRegularLocalRing R]

/-- Definition 12, p. 264: "A regular `τ`-frame of `R` for `J`, say `(S; z₁, …, z_r)`, is said to be
*`J`-stable* (or, stable with respect to `J`) if it is a `J`-stable regular frame of `R` and if, at
the same time, it satisfies the following condition: For every permissible sequence of strict
monoidal transforms `{(J_α, R_α, P_{α−1})}` of `(J, R)` such that `R_α` is residually separable
algebraic over `R_{α−1}` for all `α ≥ 1` (`R₀ = R`) and for every index `ᾱ ≥ 1` such that
`ν*(J_ᾱ) = ν*(J)` and `τ*(J_ᾱ) = τ*(J)`, we have a regular `τ`-frame `(S_ᾱ; z₁^{(ᾱ)}, …, z_r^{(ᾱ)})`
of `R_ᾱ` for `J_ᾱ`, which is a frame transform of `(S; z₁, …, z_r)` in `R_ᾱ` along the sequence
`{(R_α, P_{α−1})}`."

(Formalization notes: "a regular `τ`-frame of `R` for `J`" is part of the definiens; sequences and
`τ*` equalities are encoded as in Definition 11.) -/
@[blueprint "def:III.12"
  (statement := /-- A regular $\tau$-frame of $R$ for $J$ (\cref{def:III.10}), say
    $(S;z_1,\dots,z_r)$, is said to be \emph{$J$-stable} (or, stable with respect to $J$) if it
    is a $J$-stable regular frame of $R$ (\cref{def:III.11}) and if, at the same time, it
    satisfies the following condition: For every permissible sequence of strict monoidal
    transforms $\{(J_\alpha,R_\alpha,P_{\alpha-1})\}$ of $(J,R)$
    (\cref{def:III.9-permissible-sequence}) such that $R_\alpha$ is residually separable
    algebraic over $R_{\alpha-1}$ for all $\alpha\ge1$ ($R_0=R$) and for every index
    $\bar\alpha\ge1$ such that $\nu^*(J_{\bar\alpha})=\nu^*(J)$ and
    $\tau^*(J_{\bar\alpha})=\tau^*(J)$, we have a regular $\tau$-frame
    $(S_{\bar\alpha};z^{(\bar\alpha)}_1,\dots,z^{(\bar\alpha)}_r)$ of $R_{\bar\alpha}$ for
    $J_{\bar\alpha}$, which is a frame transform of $(S;z_1,\dots,z_r)$ in $R_{\bar\alpha}$
    along the sequence $\{(R_\alpha,P_{\alpha-1})\}$ (\cref{def:III.9-frame-transform-along}).
    (Definition 12, p.~264.)

    (Formalization note: $\tau^*(J_{\bar\alpha})=\tau^*(J)$ is $t(J_{\bar\alpha})=t(J)$ with
    $\tau^{(a)}(J_{\bar\alpha})=\tau^{(a)}(J)$ for $1\le a\le t(J)$.) -/)
  (latexEnv := "definition")]
def RegularFrame.IsJStableTauFrame (F : RegularFrame R) (J : Ideal R) : Prop :=
  F.IsRegularTauFrame J ∧ F.IsJStable J ∧
    ∀ (Sq : MonoidalSequence.{u}) (e : R ≃+* Sq.ring 0), Sq.ideal 0 = J.map e →
      Sq.IsPermissible → Sq.IsResiduallySeparableAlgebraic →
      ∀ αb : ℕ, 1 ≤ αb → nuStar (Sq.ring αb) (Sq.ideal αb) = nuStar R J →
        t (Sq.ring αb) (Sq.ideal αb) = t R J →
        (∀ a, 1 ≤ a → a ≤ t R J → tau (Sq.ring αb) (Sq.ideal αb) a = tau R J a) →
        ∃ G : RegularFrame (Sq.ring αb), G.IsRegularTauFrame (Sq.ideal αb) ∧
          F.IsFrameTransformAlong Sq e αb G

end Definition12

/-! ### Theorem 8 (pp. 264–265)

Theorem 8 (`isJStableSystem_of_isNormalizedStandardBase`, blueprint node `thm:III.8`) is in
`Hironaka/Ch3/JStableStandardBase.lean`, which imports this file. -/


/-! ### Definition 13 (p. 265) -/

section Definition13

variable {R : Type u} [CommRing R] [IsRegularLocalRing R]

open Classical in
/-- Definition 13, p. 265: "Let `R` be a regular local ring, and `J` an ideal in `R`. Let
`(z) = (z₁, …, z_r)` be a system of elements of `R` which can be extended to a regular systen [sic]
of parameters of `R`. Let us assume that `(z)` is `J`-stable. Then we say that an element `f` of
`R` is *`(J; τ_{(z)})`-stable* if it has the following property: Let `{(J_α, R_α, P_{α−1})}` be any
permissible sequence of strict monoidal transforms of `(J, R)`, such that `R_α` is residually
separable algebraic over `R_{α−1}` (`= R` if `α = 1`) for all `α`. Let `ᾱ` be any index `≥ 0` such
that `ν*(J_ᾱ) = ν*(J)` and `τ*(J_ᾱ) = τ*(J)`, where `J_ᾱ = J` if `ᾱ = 0`. Let
`(z^{(ᾱ)}) = (z₁^{(ᾱ)}, …, z_r^{(ᾱ)})` be a system of strict monoidal transforms `z_j^{(ᾱ)}` of
`z_j` (`1 ≤ j ≤ r`) in `R_ᾱ` along the sequence `{(R_α, P_{α−1})}`, if `ᾱ ≥ 1`, and
`(z^{(0)}) = (z)`. (Note that `(z^{(ᾱ)})` can be extended to a regular system of parameters of
`R_ᾱ`, for `(z)` is `J`-stable.) Let `f^{(ᾱ)}` be a strict transform of `f` in `R_ᾱ` along the
sequence `{(R_α, P_{α−1})}`, if `ᾱ ≥ 1`, and `f^{(0)} = f`. Then we have
`ν_{M_ᾱ}(f^{(ᾱ)}) = ν_M(f)`, `ν_{P_ᾱ}(f^{(ᾱ)}) = ν_M(f)` (provided `P_ᾱ` exists and is different
from `R_ᾱ`) [and] `τ_{(z^{(ᾱ)})}(f^{(ᾱ)}) = τ_{(z)}(f)`, where `M_ᾱ` (resp. `M`) denotes the maximal
ideal of `R_ᾱ` (resp. `R`) and `M₀ = M`."

(Formalization notes.
* The standing assumptions on `(z)` ("can be extended to a regular system of parameters",
  "`J`-stable") are made conjuncts of the definition: an element is `(J; τ_{(z)})`-stable only
  for such `(z)`.
* Sequences, strict transforms, the proviso on `P_ᾱ` and `τ*` are encoded as in Definition 11;
  for `ᾱ = 0` the systems `z^{(0)}`, `f^{(0)}` run over unit multiples of `z_j`, `f`, which
  changes neither the orders nor `τ_{(z)}` (the initial forms change by non-zero constants).
* `τ_{(z)}(f)` is `tauZ R z` of the one-element system `(f)` (Definition 10*).) -/
@[blueprint "def:III.13"
  (statement := /-- Let $R$ be a regular local ring, and $J$ an ideal in $R$. Let
    $(z)=(z_1,\dots,z_r)$ be a system of elements of $R$ which can be extended to a regular
    system [printed: systen] of parameters of $R$. Let us assume that $(z)$ is $J$-stable
    (\cref{def:III.11}). Then we say that an element $f$ of $R$ is
    \emph{$(J;\tau_{(z)})$-stable} if it has the following property: Let
    $\{(J_\alpha,R_\alpha,P_{\alpha-1})\}$ be any permissible sequence of strict monoidal
    transforms of $(J,R)$ (\cref{def:III.9-permissible-sequence}), such that $R_\alpha$ is
    residually separable algebraic over $R_{\alpha-1}$ ($=R$ if $\alpha=1$) for all $\alpha$.
    Let $\bar\alpha$ be any index $\ge0$ such that $\nu^*(J_{\bar\alpha})=\nu^*(J)$ and
    $\tau^*(J_{\bar\alpha})=\tau^*(J)$, where $J_{\bar\alpha}=J$ if $\bar\alpha=0$. Let
    $(z^{(\bar\alpha)})=(z^{(\bar\alpha)}_1,\dots,z^{(\bar\alpha)}_r)$ be a system of strict
    monoidal transforms $z^{(\bar\alpha)}_j$ of $z_j$ ($1\le j\le r$) in $R_{\bar\alpha}$ along
    the sequence $\{(R_\alpha,P_{\alpha-1})\}$ (\cref{def:III.9-strict-transform-element}), if
    $\bar\alpha\ge1$, and $(z^{(0)})=(z)$. (Note that $(z^{(\bar\alpha)})$ can be extended to a
    regular system of parameters of $R_{\bar\alpha}$, for $(z)$ is $J$-stable;
    \cref{lem:III.13-extends}.) Let $f^{(\bar\alpha)}$ be a strict transform of $f$ in
    $R_{\bar\alpha}$ along the sequence $\{(R_\alpha,P_{\alpha-1})\}$, if $\bar\alpha\ge1$, and
    $f^{(0)}=f$. Then we have $\nu_{M_{\bar\alpha}}(f^{(\bar\alpha)})=\nu_M(f)$,
    $\nu_{P_{\bar\alpha}}(f^{(\bar\alpha)})=\nu_M(f)$ (provided $P_{\bar\alpha}$ exists and is
    different from $R_{\bar\alpha}$) [and]
    $\tau_{(z^{(\bar\alpha)})}(f^{(\bar\alpha)})=\tau_{(z)}(f)$ (\cref{def:III.10-star}), where
    $M_{\bar\alpha}$ (resp.\ $M$) denotes the maximal ideal of $R_{\bar\alpha}$ (resp.\ $R$) and
    $M_0=M$. (Definition 13, p.~265.)

    (Formalization note: the standing assumptions on $(z)$ are made part of the definition;
    sequences, strict transforms, the proviso on $P_{\bar\alpha}$ and the equality of $\tau^*$
    are encoded as in \cref{def:III.11}; for $\bar\alpha=0$ the systems run over unit multiples
    of $z_j$ and $f$, which changes neither the orders nor $\tau_{(z)}$.)

    An element $f$ of $R$ will be said to be \emph{$(J,\tau)$-stable} if it is
    $(J;\tau_{(z)})$-stable with an empty system $(z)$. (Definition 13, p.~265.) -/)
  (latexEnv := "definition")]
def IsJTauZStable (J : Ideal R) {r : ℕ} (z : Fin r → R) (f : R) : Prop :=
  ExtendsToRSOP R (Finset.image z Finset.univ) ∧ IsJStableSystem J z ∧
    ∀ (Sq : MonoidalSequence.{u}) (e : R ≃+* Sq.ring 0), Sq.ideal 0 = J.map e →
      Sq.IsPermissible → Sq.IsResiduallySeparableAlgebraic →
      ∀ αb : ℕ, nuStar (Sq.ring αb) (Sq.ideal αb) = nuStar R J →
        t (Sq.ring αb) (Sq.ideal αb) = t R J →
        (∀ a, 1 ≤ a → a ≤ t R J → tau (Sq.ring αb) (Sq.ideal αb) a = tau R J a) →
        ∀ zα : Fin r → Sq.ring αb, (∀ j, Sq.IsStrictTransformElem e (z j) αb (zα j)) →
        ∀ fα : Sq.ring αb, Sq.IsStrictTransformElem e f αb fα →
          Ideal.ordElem (maximalIdeal (Sq.ring αb)) fα = Ideal.ordElem (maximalIdeal R) f ∧
          (Sq.center αb ≠ ⊤ →
            Ideal.ordElem (Sq.center αb) fα = Ideal.ordElem (maximalIdeal R) f) ∧
          tauZ (Sq.ring αb) zα (fun _ : Fin 1 => fα) = tauZ R z (fun _ : Fin 1 => f)

/-- Definition 13, p. 265: "An element `f` of `R` will be said to be *`(J, τ)`-stable* if it is
`(J; τ_{(z)})`-stable with an empty system `(z)`." -/
@[blueprint "def:III.13"
  (statement := /-- An element $f$ of $R$ is said to be \emph{$(J,\tau)$-stable} if it is
    $(J;\tau_{(z)})$-stable with an empty system $(z)$. (Definition 13, p.~265.) -/)
  (latexEnv := "definition")]
def IsJTauStable (J : Ideal R) (f : R) : Prop :=
  IsJTauZStable J (![] : Fin 0 → R) f

open Classical in
/-- Definition 13, p. 265 (parenthetical note): "Note that `(z^{(ᾱ)})` can be extended to a
regular system of parameters of `R_ᾱ`, for `(z)` is `J`-stable."

Deviation from the paper (statement corrected): a "system `(z₁, …, z_r)` which can be extended to
a regular system of parameters" has distinct members, and so has its transform.  The conclusion
`ExtendsToRSOP … (Finset.image zα Finset.univ)` only sees the SET of the `zα j`, so a family with
repeated members satisfies it.  The statement is therefore stated for injective `z` (hypothesis
`hzinj`; without it the statement is false: for `z₁ = z₂` the strict transforms may be chosen
`zα₁ = e z₁`, `zα₂ = u · e z₁` with a unit `u ≠ 1`, and two associated elements are not part of a
regular system of parameters) and its conclusion is that `zα` is injective and its image extends
to a regular system of parameters, i.e. that the family `zα` is independent modulo `M²`
(`RSOPIndep`).  The as-printed (weaker) conclusion is the second conjunct.

Deviation from the paper (gap filled): the paper's only justification is "for `(z)` is `J`-stable"
(p. 265).  The Lean proof supplies the missing argument.  By induction on `n ≤ ᾱ`: the invariants
`ν*`, `t`, `τ^{(a)}` of `J_n` are those of `J` for all `n ≤ ᾱ` (`nuStar_t_tau_eq_of_le`, the
monotonicity argument of Remark 2), so `J`-stability of `z_j` applies at every `n ≤ ᾱ` and gives
`ν_{M_n}(z_j^{(n)}) = ν_{P_n}(z_j^{(n)}) = 1`.  Hence, for a prime centre `P_n`, `z_j^{(n)} ∈ P_n`
and `z_j^{(n)} = x z_j^{(n+1)}` (up to a unit) with `z_j^{(n+1)} ∈ M_{n+1}`; independence modulo
`M²` passes from the `z_j^{(n)}` to the `z_j^{(n+1)}` by `rsopIndep_of_div` (an argument in
`R_{n+1}/(x) = (R_n/P_n)[T]_q`, with the derivatives `∂/∂T_i`; not in the paper).  For the centre
`R_n` the transform is an isomorphism, and independence is invariant under unit multiples. -/
@[blueprint "lem:III.13-extends"
  (statement := /-- Let $(z)=(z_1,\dots,z_r)$ be a $J$-stable system of elements of $R$ which
    can be extended to a regular system of parameters of $R$, and let
    $\{(J_\alpha,R_\alpha,P_{\alpha-1})\}$, $\bar\alpha$ and $(z^{(\bar\alpha)})$ be as in
    \cref{def:III.13}. Then $(z^{(\bar\alpha)})$ can be extended to a regular system of
    parameters of $R_{\bar\alpha}$. (Definition 13, p.~265.)

    \textbf{Deviation from the paper (statement corrected).} A system which can be extended to a
    regular system of parameters has distinct members, and so has its transform; the formalized
    statement assumes $z$ injective and concludes that $(z^{(\bar\alpha)})$ is injective and
    extends to a regular system of parameters (independence modulo $M^2$). Without the injectivity
    the statement is false, and its conclusion about the \emph{set} of the members would be
    weaker than the paper's. -/)
  (proof := /-- The paper states this in Definition~13 with the only justification ``for $(z)$
    is $J$-stable''. [\textbf{Deviation from the paper (gap filled).} The following argument is
    supplied by the formalization.] Independence modulo $M^2$ is invariant under unit multiples
    and under ring isomorphisms, and is equivalent to ``injective and extendable to a regular
    system of parameters''. We show by induction on $n\le\bar\alpha$ that every system of strict
    transforms $(z^{(n)}_j)$ of the $z_j$ in $R_n$ is independent modulo $M_n^2$. For $n=0$ this is
    the hypothesis. Since $\nu^*$ does not increase along the sequence and $t$, $\tau^{(a)}$ do
    not decrease as long as $\nu^*$ stays constant (Theorem~3, as in the proof of
    \cref{rem:III.9-2}), the invariants $\nu^*(J_n)$, $t(J_n)$, $\tau^{(a)}(J_n)$ are those of
    $J$ for every $n\le\bar\alpha$, so $J$-stability of the $z_j$ (\cref{def:III.11}) applies at
    every index $n\le\bar\alpha$: $\nu_{M_n}(z^{(n)}_j)=\nu_M(z_j)=1$ and, if the centre $P_n$ is
    proper, $\nu_{P_n}(z^{(n)}_j)=1$. If $P_n=R_n$, then $R_{n+1}=R_n$ and nothing changes. If
    $P_n$ is a prime with $R_n/P_n$ regular, then $z^{(n)}_j\in P_n\setminus P_n^2$, so
    $z^{(n)}_j=x\,w_j$ in $R_{n+1}$ with $(x)R_{n+1}=P_nR_{n+1}$, and $w_j$ is a strict transform
    of $z_j$ (\cref{lem:III.6}), with $w_j\in M_{n+1}$ because $\nu_{M_{n+1}}(w_j)=1$. Then
    $(w_j)$ is independent modulo $M_{n+1}^2$: modulo $x$ one has
    $R_{n+1}/(x)=(R_n/P_n)[T_1,\dots,T_r]_{\mathfrak q}$ and $w_j$ becomes the affine linear form
    $c_{j0}+\sum_i c_{ji}T_i$, where $z^{(n)}_j=c_{j0}x+\sum_ic_{ji}t_i$ in a minimal base
    $(x,t_1,\dots,t_r)$ of $P_n$; a relation $w_i\equiv\sum_l\beta_lw_l \pmod{M_{n+1}^2}$ would,
    after applying the derivations $\partial/\partial T_i$, which lower the order along
    $\mathfrak q$ by one, give a linear relation among the rows $(c_{j\cdot})$ modulo $M_n$,
    contradicting the independence of the $z^{(n)}_j$ modulo $M_n^2$ (the $(x,t_i)$ being
    independent modulo $M_n^2$). Finally the strict transforms of the $z_j$ in $R_{n+1}$ are the
    unit multiples of the $w_j$. -/)
  (latexEnv := "lemma")]
theorem extendsToRSOP_strictTransform_of_isJStableSystem [Hironaka.HironakaCitedResults.{u}] (J : Ideal R) {r : ℕ} (z : Fin r → R)
    (hzinj : Function.Injective z)
    (hz : ExtendsToRSOP R (Finset.image z Finset.univ)) (hzs : IsJStableSystem J z)
    (Sq : MonoidalSequence.{u}) (e : R ≃+* Sq.ring 0) (h0 : Sq.ideal 0 = J.map e)
    (hperm : Sq.IsPermissible) (hsep : Sq.IsResiduallySeparableAlgebraic) (αb : ℕ)
    (hnu : nuStar (Sq.ring αb) (Sq.ideal αb) = nuStar R J)
    (ht : t (Sq.ring αb) (Sq.ideal αb) = t R J)
    (htau : ∀ a, 1 ≤ a → a ≤ t R J → tau (Sq.ring αb) (Sq.ideal αb) a = tau R J a)
    (zα : Fin r → Sq.ring αb) (hzα : ∀ j, Sq.IsStrictTransformElem e (z j) αb (zα j)) :
    Function.Injective zα ∧ ExtendsToRSOP (Sq.ring αb) (Finset.image zα Finset.univ) := by
  classical
  -- (`ht` is implied by `hnu`, see `MonoidalSequence.nuStar_t_tau_eq_of_le`)
  have _ := ht
  -- the system `(z_j)` is independent modulo `M²`, and has order `1` along `M`
  have hind : RSOPIndep Finset.univ z := RSOPIndep.of_extends hzinj.injOn hz
  have hord1 : ∀ j, Ideal.ordElem (maximalIdeal R) (z j) = ((1 : ℕ) : ℕ∞) := fun j => by
    rw [ordElem_maximalIdeal_eq_one_of_mem_extendsToRSOP hz
      (Finset.mem_image_of_mem z (Finset.mem_univ j))]
    norm_cast
  -- `ν*`, `t`, `τ^{(a)}` of `J_n` are those of `J` for all `n ≤ ᾱ`, so `J`-stability applies
  -- at every index `n ≤ ᾱ`
  have hmono := MonoidalSequence.nuStar_t_tau_eq_of_le J Sq e h0 hperm hsep αb hnu htau
  have hstabn : ∀ n ≤ αb, ∀ j (gn : Sq.ring n), Sq.IsStrictTransformElem e (z j) n gn →
      Ideal.ordElem (maximalIdeal (Sq.ring n)) gn = Ideal.ordElem (maximalIdeal R) (z j) ∧
      (Sq.center n ≠ ⊤ →
        Ideal.ordElem (Sq.center n) gn = Ideal.ordElem (maximalIdeal R) (z j)) :=
    fun n hn j gn hgn => hzs j Sq e h0 hperm hsep n (hmono n hn).1 (hmono n hn).2.1
      (hmono n hn).2.2 gn hgn
  -- induction along the sequence, one monoidal transform at a time
  have main : ∀ n ≤ αb, ∀ gn : Fin r → Sq.ring n,
      (∀ j, Sq.IsStrictTransformElem e (z j) n (gn j)) → RSOPIndep Finset.univ gn := by
    intro n
    induction n with
    | zero =>
      intro _ gn hgn
      have hbase : RSOPIndep Finset.univ fun j => e (z j) := hind.map_ringEquiv e
      choose u hu using fun j => MonoidalSequence.IsStrictTransformElem.unique Sq
        (rfl : Sq.IsStrictTransformElem e (z j) 0 (e (z j))) (hgn j)
      exact hbase.of_associated fun j _ => ⟨u j, by rw [hu j]; exact mul_comm _ _⟩
    | succ n ih =>
      intro hn gn hgn
      choose g0 hg0 using fun j =>
        MonoidalSequence.exists_strictAlong_span_singleton_eq_aux Sq e hperm.hasRegularCenters
          (z j) n
      have hg0' : ∀ j, Sq.IsStrictTransformElem e (z j) n (g0 j) := fun j => (hg0 j).symm
      have hind0 := ih (by omega) g0 hg0'
      rcases hperm n with htop | ⟨hP, hJP, hreg, -⟩
      · -- center `R_n`: `R_n → R_{n+1}` is an isomorphism
        have hbij := MonoidalSequence.toRing_bijective_of_eq_top_aux (Sq.transform n) htop
        have hst : ∀ j, Sq.IsStrictTransformElem e (z j) (n + 1)
            (Sq.equiv n ((Sq.transform n).toRing (g0 j))) := by
          intro j
          show Ideal.span {_} = Sq.strictAlong (Ideal.span {e (z j)}) (n + 1)
          rw [MonoidalSequence.strictAlong, hg0 j,
            MonoidalSequence.strictTransformIdeal_eq_map_of_eq_top_aux _ htop,
            Ideal.map_span, Set.image_singleton, Ideal.map_span, Set.image_singleton]
        let φ : Sq.ring n ≃+* Sq.ring (n + 1) :=
          (RingEquiv.ofBijective (Sq.transform n).toRing hbij).trans (Sq.equiv n)
        choose u hu using fun j => MonoidalSequence.IsStrictTransformElem.unique Sq (hst j) (hgn j)
        exact (hind0.map_ringEquiv φ).of_associated fun j _ =>
          ⟨u j, by rw [hu j]; exact mul_comm _ _⟩
      · -- a prime center `P_n` with `R_n/P_n` regular: `z_j^{(n)} = x z_j^{(n+1)}`
        have := hP
        have := hreg
        have hxP : Ideal.span {(Sq.transform n).toRing (Sq.transform n).x} =
            (Sq.center n).map (Sq.transform n).toRing := (Sq.transform n).span_xR_eq_map
        have hPne : Sq.center n ≠ ⊤ := hP.ne_top
        have hordn := fun j => hstabn n (by omega) j (g0 j) (hg0' j)
        have hmemP : ∀ j, g0 j ∈ Sq.center n ^ 1 := fun j => by
          apply Ideal.mem_pow_of_ordElem
          rw [(hordn j).2 hPne, hord1 j]
        choose g' hg' using fun j =>
          MonoidalSequence.exists_mul_pow_eq_toRing_aux (Sq.transform n) hxP (hmemP j)
        have hst : ∀ j, Sq.IsStrictTransformElem e (z j) (n + 1) (Sq.equiv n (g' j)) := by
          intro j
          have htoNat : (Ideal.ordElem (Sq.center n) (g0 j)).toNat = 1 := by
            rw [(hordn j).2 hPne, hord1 j, ENat.toNat_natCast]
          show Ideal.span {_} = Sq.strictAlong (Ideal.span {e (z j)}) (n + 1)
          rw [MonoidalSequence.strictAlong, hg0 j,
            MonoidalSequence.strictTransformIdeal_span_singleton_aux _ hP hreg (g0 j) _
            (Sq.transform n).x_mem hxP (g' j) (by rw [htoNat]; exact hg' j), Ideal.map_span,
            Set.image_singleton]
        choose u hu using fun j => MonoidalSequence.IsStrictTransformElem.unique Sq (hst j) (hgn j)
        -- the `z_j^{(n+1)}` lie in the maximal ideal (`ν_{M_{n+1}} = 1`), hence so do the `g' j`
        have hgM : ∀ j, g' j ∈ maximalIdeal (Sq.transform n).ring := by
          intro j hunit
          have hord := (hstabn (n + 1) hn j (gn j) (hgn j)).1
          rw [hord1 j] at hord
          have hmem : gn j ∈ maximalIdeal (Sq.ring (n + 1)) := by
            have := Ideal.mem_pow_of_ordElem hord
            rwa [pow_one] at this
          apply hmem
          rw [hu j]
          exact (Units.isUnit _).mul (hunit.map (Sq.equiv n))
        have hdiv := rsopIndep_of_div (Sq.transform n) Finset.univ g0 hind0
          (fun j _ => by simpa using hmemP j) g' (fun j _ => by simpa using hg' j)
          (fun j _ => hgM j)
        exact (hdiv.map_ringEquiv (Sq.equiv n)).of_associated fun j _ =>
          ⟨u j, by rw [hu j]; exact mul_comm _ _⟩
  obtain ⟨hinj, hext⟩ := (main αb le_rfl zα hzα).injOn_and_extends
  exact ⟨fun a b hab => hinj (Finset.mem_coe.mpr (Finset.mem_univ a))
    (Finset.mem_coe.mpr (Finset.mem_univ b)) hab, hext⟩

end Definition13

/-! ### Lemma 22 (pp. 265–267)

Lemma 22 (`mem_prime_of_ordElem_localization_ge`, `lem:III.22`) is in
`Hironaka/Ch3/JStabilityLemma22.lean`: its proof follows the printed one, whose reduction to a
complete `R` with algebraically closed residue field and whose sequence of monoidal transforms use
files that import this one (the base change of regular frames, the frame transforms of §8 in the
form of `Hironaka/Compat/FrameCore.lean`, the resolution of curve germs of Theorem 1). -/

/-! ### Lemma 23 (pp. 267–268) -/

section Lemma23

variable (k : Type u) [Field k]

/-- Lemma 23, p. 267: "the smallest `k`-module `T` of linear forms in `S` such that `k[T]` contains
`F`", for `S = k[X₀, …, X_n]` a polynomial ring; encoded without choice, as `tauZSubmodule` of
Definition 10* and `tauSubmodule` of §4, as the intersection of all `k`-submodules of the linear
forms whose generated `k`-subalgebra contains `F` (that this intersection has the property is
Lemma 10 of §4). -/
noncomputable def linearFormModule {n : ℕ} (F : MvPolynomial (Fin (n + 1)) k) :
    Submodule k (MvPolynomial (Fin (n + 1)) k) :=
  sInf {T | T ≤ MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k 1 ∧
    F ∈ Algebra.adjoin k (T : Set (MvPolynomial (Fin (n + 1)) k))}

/-- The dehomogenization `k[X₀, X₁, …, X_n] → A = k[X₁/X₀, …, X_n/X₀]`,
`G ↦ G(1, X₁/X₀, …, X_n/X₀)`, with `A` identified with the polynomial ring `k[Y₁, …, Y_n]` in the
algebraically independent elements `Y_i = X_i/X₀` (`MvPolynomial (Fin n) k`, `Y_i = X (i − 1)`).
For a form `G` of degree `d` it sends `G` to `G/X₀^d`; in particular `F₀ = F/X₀^ν` and `Y/X₀` (`Y` a
linear form) of Lemma 23 are the images of `F` and `Y`. -/
noncomputable def dehomogenize (n : ℕ) :
    MvPolynomial (Fin (n + 1)) k →ₐ[k] MvPolynomial (Fin n) k :=
  MvPolynomial.aeval (Fin.cons 1 MvPolynomial.X : Fin (n + 1) → MvPolynomial (Fin n) k)

open MvPolynomial in
/-- The homogeneous component of degree `μ ≤ ν` of `g F`, for a form `F` of degree `ν`: it is
`0` for `μ < ν` and `g(0) F` for `μ = ν`. -/
theorem homogeneousComponent_mul_form_aux {σ E : Type*} [CommRing E]
    {F : MvPolynomial σ E} {ν : ℕ} (hF : F ∈ homogeneousSubmodule σ E ν)
    (g : MvPolynomial σ E) (μ : ℕ) (hμ : μ ≤ ν) :
    homogeneousComponent μ (g * F) = if μ = ν then C (g.coeff 0) * F else 0 := by
  classical
  conv_lhs => rw [← sum_homogeneousComponent g]
  rw [Finset.sum_mul, map_sum]
  have h : ∀ i, homogeneousComponent μ (homogeneousComponent i g * F) =
      if μ = i + ν then homogeneousComponent i g * F else 0 := fun i =>
    homogeneousComponent_of_mem ((homogeneousComponent_isHomogeneous i g).mul hF)
  simp_rw [h]
  split_ifs with hμν
  · subst hμν
    rw [Finset.sum_eq_single 0]
    · simp [homogeneousComponent_zero]
    · intro i _ hi
      rw [ite_eq_right (by omega)]
    · intro h0
      exact absurd (Finset.mem_range.mpr (Nat.succ_pos _)) h0
  · exact Finset.sum_eq_zero fun i _ => ite_eq_right (by omega)

open MvPolynomial in
/-- The homogeneous components of an element of `E[T]`, `T` a set of linear forms, lie in `E[T]`. -/
theorem homogeneousComponent_mem_adjoin_aux {σ E : Type*} [CommRing E]
    {T : Set (MvPolynomial σ E)} (hT : T ⊆ homogeneousSubmodule σ E 1)
    {h : MvPolynomial σ E} (hh : h ∈ Algebra.adjoin E T) (μ : ℕ) :
    homogeneousComponent μ h ∈ Algebra.adjoin E T := by
  classical
  induction hh using Algebra.adjoin_induction generalizing μ with
  | mem x hx =>
    rw [homogeneousComponent_of_mem (hT hx)]
    split_ifs
    · exact Algebra.subset_adjoin hx
    · exact zero_mem _
  | algebraMap r =>
    rw [MvPolynomial.algebraMap_eq, homogeneousComponent_of_mem (isHomogeneous_C σ r)]
    split_ifs
    · exact Subalgebra.algebraMap_mem _ r
    · exact zero_mem _
  | add x y _ _ hx hy =>
    rw [map_add]
    exact add_mem (hx μ) (hy μ)
  | mul x y _ _ hx hy =>
    rw [← sum_homogeneousComponent x, ← sum_homogeneousComponent y, Finset.sum_mul_sum, map_sum]
    refine sum_mem fun i _ => ?_
    rw [map_sum]
    refine sum_mem fun j _ => ?_
    rw [homogeneousComponent_of_mem ((homogeneousComponent_isHomogeneous i x).mul
      (homogeneousComponent_isHomogeneous j y))]
    split_ifs
    · exact mul_mem (hx i) (hy j)
    · exact zero_mem _


open MvPolynomial in
/-- If a form `F` of degree `ν` lies in `E[T]` (`T` a module of linear forms), then `T` has the
property of Lemma 10 for the principal ideal `(F)` up to degree `ν`. -/
theorem isTauSubmoduleMv_span_singleton_aux {E : Type u} [Field E] {m : ℕ}
    {F : MvPolynomial (Fin m) E} {ν : ℕ} (hF : F ∈ homogeneousSubmodule (Fin m) E ν)
    {T : Submodule E (MvPolynomial (Fin m) E)} (hT : T ≤ homogeneousSubmodule (Fin m) E 1)
    (hFT : F ∈ Algebra.adjoin E (T : Set (MvPolynomial (Fin m) E))) :
    IsTauSubmoduleMv E m (Ideal.span {F}) T ν := by
  refine ⟨hT, fun μ hμ ψ hψ => ⟨fun hψF => ?_, fun h => ?_⟩⟩
  · obtain ⟨g, rfl⟩ := Ideal.mem_span_singleton'.mp hψF
    have hgF : g * F = homogeneousComponent μ (g * F) := by
      rw [homogeneousComponent_of_mem hψ, ite_eq_left rfl]
    rw [hgF, homogeneousComponent_mul_form_aux hF g μ hμ]
    split_ifs
    · exact Ideal.mul_mem_left _ _
        (Ideal.subset_span ⟨Ideal.mem_span_singleton_self F, hFT⟩)
    · exact zero_mem _
  · refine (Ideal.span_le.mpr ?_) h
    exact fun x hx => hx.1

open MvPolynomial in
/-- Conversely, if `L` has the property of Lemma 10 for `(F)` up to the degree `ν` of the form
`F`, then `F ∈ k[L]`. -/
theorem mem_adjoin_of_isTauSubmoduleMv_aux {E : Type u} [Field E] {m : ℕ}
    {F : MvPolynomial (Fin m) E} {ν : ℕ} (hF : F ∈ homogeneousSubmodule (Fin m) E ν)
    {L : Submodule E (MvPolynomial (Fin m) E)}
    (hL : IsTauSubmoduleMv E m (Ideal.span {F}) L ν) :
    F ∈ Algebra.adjoin E (L : Set (MvPolynomial (Fin m) E)) := by
  have hmem := (hL.2 ν le_rfl F hF).mp (Ideal.mem_span_singleton_self F)
  -- the degree-`ν` component maps `span((F) ∩ E[L])` into `E[L]`
  have key : ∀ x ∈ Ideal.span ((Ideal.span {F} : Set (MvPolynomial (Fin m) E)) ∩
      (Algebra.adjoin E (L : Set (MvPolynomial (Fin m) E)) : Set (MvPolynomial (Fin m) E))),
      x ∈ Ideal.span {F} ∧
        homogeneousComponent ν x ∈ Algebra.adjoin E (L : Set (MvPolynomial (Fin m) E)) := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      exact ⟨hx.1, homogeneousComponent_mem_adjoin_aux (fun y hy => hL.1 hy) hx.2 ν⟩
    | zero => exact ⟨zero_mem _, by rw [map_zero]; exact zero_mem _⟩
    | add x y _ _ hx hy =>
      exact ⟨add_mem hx.1 hy.1, by rw [map_add]; exact add_mem hx.2 hy.2⟩
    | smul a x _ hx =>
      refine ⟨Ideal.mul_mem_left _ a hx.1, ?_⟩
      obtain ⟨g, rfl⟩ := Ideal.mem_span_singleton'.mp hx.1
      have h2 := hx.2
      rw [homogeneousComponent_mul_form_aux hF g ν le_rfl, ite_eq_left rfl] at h2
      rw [smul_eq_mul, ← mul_assoc, homogeneousComponent_mul_form_aux hF (a * g) ν le_rfl,
        ite_eq_left rfl, ← constantCoeff_eq, map_mul, constantCoeff_eq, constantCoeff_eq,
        map_mul, mul_assoc]
      exact mul_mem (by rw [← MvPolynomial.algebraMap_eq]; exact Subalgebra.algebraMap_mem _ _) h2
  have := (key F hmem).2
  rwa [homogeneousComponent_of_mem hF, ite_eq_left rfl] at this

open MvPolynomial in
/-- Over a perfect field every field extension is separable in the sense of pp. 211–212: a purely
inseparable extension of a perfect field is trivial. -/
private theorem isSeparableFieldExtension_of_perfectField_aux (k K : Type u) [Field k] [Field K]
    [Algebra k K] [PerfectField k] : IsSeparableFieldExtension k K := by
  intro k'' _ _ hpi
  have hbij := IsPurelyInseparable.bijective_algebraMap_of_isSeparable k k''
  let e : k'' ≃ₐ[k] k := (AlgEquiv.ofBijective (Algebra.ofId k k'') hbij).symm
  let e' := (Algebra.TensorProduct.congr (AlgEquiv.refl : K ≃ₐ[k] K) e).trans
    (Algebra.TensorProduct.rid k k K)
  exact isReduced_of_injective e' e'.injective

open MvPolynomial in
/-- Every monomial of an element of `(X₁, …, X_n)^ν` has degree at least `ν`. -/
private theorem le_degree_of_mem_pow_ker_constantCoeff_aux {σ E : Type*} [CommRing E]
    (ν : ℕ) {p : MvPolynomial σ E}
    (hp : p ∈ (RingHom.ker (constantCoeff : MvPolynomial σ E →+* E)) ^ ν) :
    ∀ d ∈ p.support, ν ≤ d.degree := by
  classical
  induction ν generalizing p with
  | zero => exact fun _ _ => Nat.zero_le _
  | succ ν ih =>
    rw [pow_succ'] at hp
    refine Submodule.mul_induction_on (C := fun p => ∀ d ∈ p.support, ν + 1 ≤ d.degree) hp
      ?_ ?_
    · intro a ha b hb d hd
      obtain ⟨d₁, hd₁, d₂, hd₂, rfl⟩ := Finset.mem_add.mp (support_mul a b hd)
      have h1 : d₁ ≠ 0 := by
        rintro rfl
        rw [RingHom.mem_ker, constantCoeff_eq] at ha
        exact (mem_support_iff.mp hd₁) ha
      have h1' : 1 ≤ d₁.degree := Nat.one_le_iff_ne_zero.mpr
        (fun h => h1 ((Finsupp.degree_eq_zero_iff d₁).mp h))
      rw [map_add]
      have := ih hb d₂ hd₂
      omega
    · intro x y hx hy d hd
      rcases Finset.mem_union.mp (support_add hd) with h | h
      · exact hx d h
      · exact hy d h

open MvPolynomial in
/-- `ν ≤ ν_I(f)` implies `f ∈ Iᵛ`. -/
private theorem mem_pow_of_le_ordElem_aux {A : Type*} [CommRing A] {I : Ideal A} {f : A}
    {ν : ℕ} (h : (ν : ℕ∞) ≤ Ideal.ordElem I f) : f ∈ I ^ ν := by
  by_contra hf
  cases ν with
  | zero => exact hf (by simp)
  | succ m =>
    have h' := h.trans (Ideal.ordElem_le_of_notMem hf)
    rw [Nat.cast_le] at h'
    omega

open MvPolynomial in
/-- The degree of `m : Fin (n + 1) →₀ ℕ` is `m 0 + deg (tail m)`. -/
private theorem degree_eq_zero_add_tail_aux {n : ℕ} (m : Fin (n + 1) →₀ ℕ) :
    m.degree = m 0 + (Finsupp.tail m).degree := by
  rw [Finsupp.degree_eq_sum, Finsupp.degree_eq_sum, Fin.sum_univ_succ]
  rfl

open MvPolynomial in
/-- The dehomogenization `X₀ ↦ 1` of a monomial `c X^m` is `c Y^{tail m}`. -/
private theorem aeval_cons_one_monomial_aux {E : Type*} [CommRing E] {n : ℕ}
    (m : Fin (n + 1) →₀ ℕ) (c : E) :
    aeval (Fin.cons 1 X : Fin (n + 1) → MvPolynomial (Fin n) E) (monomial m c) =
      monomial (Finsupp.tail m) c := by
  rw [aeval_monomial, Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Fin.prod_univ_succ,
    Fin.cons_zero, one_pow, one_mul, MvPolynomial.algebraMap_eq, monomial_eq,
    Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
  rfl

open MvPolynomial in
/-- For a form `G` of degree `ν` in `X₀, …, X_n`, the coefficient of `Y^{tail m}` in the
dehomogenization `G(1, Y)` is the coefficient of `X^m` in `G`, for every monomial `m` of `G`. -/
private theorem coeff_aeval_cons_one_aux {E : Type*} [CommRing E] {n ν : ℕ}
    {G : MvPolynomial (Fin (n + 1)) E} (hG : G.IsHomogeneous ν) {m : Fin (n + 1) →₀ ℕ}
    (hm : m ∈ G.support) :
    (aeval (Fin.cons 1 X : Fin (n + 1) → MvPolynomial (Fin n) E) G).coeff (Finsupp.tail m) =
      G.coeff m := by
  classical
  conv_lhs => rw [G.as_sum]
  rw [map_sum, coeff_sum]
  simp_rw [aeval_cons_one_monomial_aux, coeff_monomial]
  rw [Finset.sum_eq_single m]
  · rw [ite_eq_left rfl]
  · intro m' hm' hne
    rw [ite_eq_right]
    intro htail
    apply hne
    have hdeg : ∀ m'' ∈ G.support, m''.degree = ν := fun m'' h'' => by
      have := hG (mem_support_iff.mp h'')
      rw [Finsupp.degree_eq_weight_one]
      exact this
    have h0 : m' 0 = m 0 := by
      have e1 := degree_eq_zero_add_tail_aux m'
      have e2 := degree_eq_zero_add_tail_aux m
      rw [hdeg m' hm', htail] at e1
      rw [hdeg m hm] at e2
      omega
    ext i
    refine Fin.cases h0 (fun j => ?_) i
    have := DFunLike.congr_fun htail j
    simpa [Finsupp.tail_apply] using this
  · intro h
    exact absurd hm h

open MvPolynomial in
/-- The smallest module `T` of linear forms with `F ∈ k[T]` (Lemma 23) has the property
`F ∈ k[T]`: the intersection of two modules with the property has it (Lemma 10 of §4,
`isTauSubmoduleMv_inf`), and the modules lie in the finite-dimensional space of linear forms. -/
theorem linearFormModule_spec {k : Type u} [Field k] {n ν : ℕ} (hν : 0 < ν)
    {F : MvPolynomial (Fin (n + 1)) k} (hF : F ∈ homogeneousSubmodule (Fin (n + 1)) k ν) :
    linearFormModule k F ≤ homogeneousSubmodule (Fin (n + 1)) k 1 ∧
      F ∈ Algebra.adjoin k (linearFormModule k F : Set (MvPolynomial (Fin (n + 1)) k)) := by
  classical
  let _ := MvPolynomial.gradedAlgebra (σ := Fin (n + 1)) (R := k)
  set 𝒮 : Set (Submodule k (MvPolynomial (Fin (n + 1)) k)) :=
    {T | T ≤ homogeneousSubmodule (Fin (n + 1)) k 1 ∧
      F ∈ Algebra.adjoin k (T : Set (MvPolynomial (Fin (n + 1)) k))} with h𝒮
  have hI : (Ideal.span {F}).IsHomogeneous (homogeneousSubmodule (Fin (n + 1)) k) :=
    Ideal.homogeneous_span _ _ (by rintro x rfl; exact ⟨ν, hF⟩)
  have hinf : ∀ T ∈ 𝒮, ∀ T' ∈ 𝒮, T ⊓ T' ∈ 𝒮 := by
    intro T hT T' hT'
    have h1 := isTauSubmoduleMv_span_singleton_aux hF hT.1 hT.2
    have h2 := isTauSubmoduleMv_span_singleton_aux hF hT'.1 hT'.2
    have h3 := isTauSubmoduleMv_inf k (n + 1) (Ideal.span {F}) hI ν hν T T' h1 h2
    exact ⟨inf_le_left.trans hT.1, mem_adjoin_of_isTauSubmoduleMv_aux hF h3⟩
  have hone : homogeneousSubmodule (Fin (n + 1)) k 1 ∈ 𝒮 := by
    refine ⟨le_rfl, ?_⟩
    have : Algebra.adjoin k
        (Set.range (MvPolynomial.X : Fin (n + 1) → MvPolynomial (Fin (n + 1)) k))
        ≤ Algebra.adjoin k (homogeneousSubmodule (Fin (n + 1)) k 1 :
          Set (MvPolynomial (Fin (n + 1)) k)) := by
      refine Algebra.adjoin_mono ?_
      rintro _ ⟨i, rfl⟩
      exact MvPolynomial.isHomogeneous_X k i
    refine this ?_
    rw [MvPolynomial.adjoin_range_X]
    exact Algebra.mem_top
  have hfd : FiniteDimensional k (homogeneousSubmodule (Fin (n + 1)) k 1) := by
    rw [MvPolynomial.homogeneousSubmodule_one_eq_span_X]
    exact FiniteDimensional.span_of_finite _ (Set.finite_range _)
  obtain ⟨T₀, hT₀, hmin⟩ := (InvImage.wf (fun T : Submodule k (MvPolynomial (Fin (n + 1)) k) =>
    Module.finrank k T) wellFounded_lt).has_min 𝒮 ⟨_, hone⟩
  have hfdT₀ : FiniteDimensional k T₀ := Submodule.finiteDimensional_of_le hT₀.1
  have hle : ∀ T ∈ 𝒮, T₀ ≤ T := by
    intro T hT
    have hmem := hinf T₀ hT₀ T hT
    have h1 : T₀ ⊓ T = T₀ := by
      refine Submodule.eq_of_le_of_finrank_le inf_le_left ?_
      by_contra hlt
      exact hmin _ hmem (not_le.mp hlt)
    rw [← h1]
    exact inf_le_right
  have heq : linearFormModule k F = T₀ := le_antisymm (sInf_le hT₀) (le_sInf hle)
  rw [heq]
  exact ⟨hT₀.1, hT₀.2⟩

open MvPolynomial in
/-- The `E`-module `V_c` of the linear forms `X_i - c_iX₀` (`1 ≤ i ≤ n`), which vanish at the point
`(1, c)`; the module `k[X_1 - c_1X_0, …, X_n - c_nX_0]` of p. 268 is `E[V_c]`. -/
private noncomputable def translateModule {E : Type*} [Field E] {n : ℕ} (c : Fin n → E) :
    Submodule E (MvPolynomial (Fin (n + 1)) E) :=
  Submodule.span E (Set.range fun i : Fin n => X i.succ - C (c i) * X 0)

open MvPolynomial in
private theorem translateModule_le_homogeneous {E : Type*} [Field E] {n : ℕ} (c : Fin n → E) :
    translateModule c ≤ homogeneousSubmodule (Fin (n + 1)) E 1 := by
  rw [translateModule, Submodule.span_le]
  rintro _ ⟨i, rfl⟩
  exact (isHomogeneous_X E i.succ).sub (isHomogeneous_C_mul_X (c i) 0)

open MvPolynomial in
/-- Lemma 23, p. 268: "This implies that `F` is contained in `(X₁ - c₁X₀, …, X_n - c_nX₀)^ν S`, so
that `F` is a form in `k[X₁ - c₁X₀, …, X_n - c_nX₀]`."  For a form `F` of degree `ν` over a field `E`
and a point `c ∈ Eⁿ`: if the translate `F₀(Y + c)` of the dehomogenization `F₀ = F(1, Y)` lies in
`(Y₁, …, Y_n)^ν` (this is `F₀ ∈ (Y - c)^ν`), then `F ∈ E[V_c]`.  Proof: `G = F(X₀, X₁ + c₁X₀, …,
X_n + c_nX₀)` is a form of degree `ν` with `G(1, Y) = F₀(Y + c) ∈ (Y)^ν`, so every monomial of `G`
has degree `≥ ν` in `X₁, …, X_n` hence none contains `X₀`, and `F = G(X₀, X₁ - c₁X₀, …)` is a
polynomial in the linear forms `X_i - c_iX₀`. -/
private theorem mem_adjoin_translateModule_of_translate_mem_pow {E : Type u} [Field E] {n ν : ℕ}
    {F : MvPolynomial (Fin (n + 1)) E} (hF : F ∈ homogeneousSubmodule (Fin (n + 1)) E ν)
    (c : Fin n → E)
    (hF0 : eval₂Hom C (fun i => X i + C (c i)) (dehomogenize E n F) ∈
      (RingHom.ker (constantCoeff : MvPolynomial (Fin n) E →+* E)) ^ ν) :
    F ∈ Algebra.adjoin E (translateModule c : Set (MvPolynomial (Fin (n + 1)) E)) := by
  classical
  let ψ : MvPolynomial (Fin n) E →+* MvPolynomial (Fin n) E := eval₂Hom C (fun i => X i + C (c i))
  -- `G = F(X₀, X₁ + c₁X₀, …, X_n + c_nX₀)` is a form of degree `ν` with `G(1, Y) = ψ(F₀)`
  let gΦ : Fin (n + 1) → MvPolynomial (Fin (n + 1)) E := Fin.cons (X 0) fun i =>
    X i.succ + C (c i) * X 0
  let Φ : MvPolynomial (Fin (n + 1)) E →+* MvPolynomial (Fin (n + 1)) E := eval₂Hom C gΦ
  have hG : (Φ F).IsHomogeneous ν := by
    have hg : ∀ i, (gΦ i).IsHomogeneous 1 := by
      intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · simpa [gΦ] using isHomogeneous_X E (0 : Fin (n + 1))
      · simpa [gΦ] using (isHomogeneous_X E j.succ).add (isHomogeneous_C_mul_X (c j) 0)
    have := (show F.IsHomogeneous ν from hF).eval₂ C _ (fun r => isHomogeneous_C _ _) hg
    rw [one_mul] at this
    exact this
  have hdeh : ∀ p, aeval (R := E) (Fin.cons 1 X : Fin (n + 1) → MvPolynomial (Fin n) E) (Φ p) =
      ψ (dehomogenize E n p) := by
    intro p
    have : ((aeval (R := E) (Fin.cons 1 X : Fin (n + 1) → MvPolynomial (Fin n) E) :
        MvPolynomial (Fin (n + 1)) E →+* _).comp Φ) =
        ψ.comp (dehomogenize E n : MvPolynomial (Fin (n + 1)) E →+* MvPolynomial (Fin n) E) := by
      apply ringHom_ext
      · intro a
        simp [Φ, gΦ, ψ, dehomogenize]
      · intro i
        refine Fin.cases ?_ (fun j => ?_) i
        · simp [Φ, gΦ, ψ, dehomogenize]
        · simp [Φ, gΦ, ψ, dehomogenize]
    exact RingHom.congr_fun this p
  -- as `ψ(F₀) ∈ (Y)ᵛ`, `G` does not involve `X₀`
  have hsupp : ∀ m ∈ (Φ F).support, m 0 = 0 := by
    intro m hm
    by_contra h0
    have hc := coeff_aeval_cons_one_aux hG hm
    have hmem : Finsupp.tail m ∈ (aeval (R := E) (Fin.cons 1 X :
        Fin (n + 1) → MvPolynomial (Fin n) E) (Φ F)).support := by
      rw [mem_support_iff, hc]
      exact mem_support_iff.mp hm
    rw [hdeh] at hmem
    have hle := le_degree_of_mem_pow_ker_constantCoeff_aux ν hF0 _ hmem
    have hdegm : m.degree = ν := by
      have := hG (mem_support_iff.mp hm)
      rw [Finsupp.degree_eq_weight_one]
      exact this
    have := degree_eq_zero_add_tail_aux m
    omega
  -- hence `F = G(X₀, X₁ - c₁X₀, …, X_n - c_nX₀) ∈ E[V_c]`
  let ρ : MvPolynomial (Fin (n + 1)) E →ₐ[E] MvPolynomial (Fin (n + 1)) E :=
    aeval (Fin.cons (X 0) fun i => X i.succ - C (c i) * X 0)
  have hρΦ : ρ (Φ F) = F := by
    have : (ρ : MvPolynomial (Fin (n + 1)) E →+* _).comp Φ = RingHom.id _ := by
      apply ringHom_ext
      · intro a
        simp [ρ, Φ, gΦ]
      · intro i
        refine Fin.cases ?_ (fun j => ?_) i
        · simp [ρ, Φ, gΦ]
        · simp [ρ, Φ, gΦ]
    exact RingHom.congr_fun this F
  have hGs : Φ F ∈ supported E (Set.range Fin.succ) := by
    rw [mem_supported]
    intro i hi
    rw [Finset.mem_coe, mem_vars_iff_mem_support] at hi
    obtain ⟨m, hm, hmi⟩ := hi
    induction i using Fin.cases with
    | zero => exact absurd (hsupp m hm) (Finsupp.mem_support_iff.mp hmi)
    | succ j => exact ⟨j, rfl⟩
  have h1 : ρ (Φ F) ∈ (supported E (Set.range Fin.succ)).map ρ :=
    Subalgebra.mem_map.mpr ⟨_, hGs, rfl⟩
  rw [supported_eq_adjoin_X, AlgHom.map_adjoin, hρΦ] at h1
  refine Algebra.adjoin_mono ?_ h1
  rintro _ ⟨_, ⟨_, ⟨j, rfl⟩, rfl⟩, rfl⟩
  exact Submodule.subset_span ⟨j, by simp [ρ]⟩

open MvPolynomial in
/-- Lemma 23, p. 268, the case of an algebraically closed field, at one point: "Then every maximal
ideal `N` in `A` has a base of the form `(X₁/X₀ - c₁, …, X_n/X₀ - c_n)`, where `c_j ∈ k`.  The
assumption `ν_{NA_N}(F₀) ≥ ν` is equivalent to saying that `N^ν` contains `F₀`.  This implies that `F`
is contained in `(X₁ - c₁X₀, …, X_n - c_nX₀)^ν S`, so that `F` is a form in `k[X₁ - c₁X₀, …,
X_n - c_nX₀]`.  Thus `N` contains `I₀`.  (See Lemma 10, § 4.)"

Here `N = ker (aeval c)` is the maximal ideal of the point `c`, `N^ν ∋ F₀` is the hypothesis `hFc`, and
the conclusion is that every `Y` in the smallest module `T` of linear forms with `F ∈ E[T]` satisfies
`Y(1, c) = 0`, i.e. `Y/X₀ ∈ N` (equivalently `N ⊇ I₀`).  The base `(Y_i - c_i)` of `N` is used through the
translation `ψ(a) = a(Y + c)`, which maps `N` into `(Y)` and `Y_i - c_i` to `Y_i`
(`mem_adjoin_translateModule_of_translate_mem_pow`); "Lemma 10 of § 4" is the minimality of `T`
(`linearFormModule` is the intersection of all modules `T'` with `F ∈ E[T']`, so `T ≤ V_c`). -/
private theorem aeval_dehomogenize_eq_zero_of_mem_linearFormModule {E : Type u} [Field E]
    {n ν : ℕ} {F : MvPolynomial (Fin (n + 1)) E}
    (hF : F ∈ homogeneousSubmodule (Fin (n + 1)) E ν) (c : Fin n → E)
    (hFc : dehomogenize E n F ∈
      (RingHom.ker (aeval c : MvPolynomial (Fin n) E →ₐ[E] E)) ^ ν) :
    ∀ Y ∈ linearFormModule E F, aeval c (dehomogenize E n Y) = 0 := by
  classical
  -- the translation `ψ(a) = a(Y + c)` maps `N = ker (aeval c)` into `(Y) = ker constantCoeff`
  let ψ : MvPolynomial (Fin n) E →+* MvPolynomial (Fin n) E := eval₂Hom C (fun i => X i + C (c i))
  have hψc : ∀ a, constantCoeff (ψ a) = aeval c a := by
    intro a
    have : (constantCoeff : MvPolynomial (Fin n) E →+* E).comp ψ =
        (aeval c : MvPolynomial (Fin n) E →ₐ[E] E).toRingHom := by
      apply ringHom_ext
      · intro a
        simp [ψ]
      · intro i
        simp [ψ]
    exact RingHom.congr_fun this a
  have hF0 : ψ (dehomogenize E n F) ∈
      (RingHom.ker (constantCoeff : MvPolynomial (Fin n) E →+* E)) ^ ν := by
    have hle : ((RingHom.ker (aeval c : MvPolynomial (Fin n) E →ₐ[E] E)) ^ ν).map ψ ≤
        (RingHom.ker (constantCoeff : MvPolynomial (Fin n) E →+* E)) ^ ν := by
      rw [Ideal.map_pow]
      refine Ideal.pow_right_mono (Ideal.map_le_iff_le_comap.mpr fun a ha => ?_) ν
      rw [Ideal.mem_comap, RingHom.mem_ker, hψc]
      exact RingHom.mem_ker.mp ha
    exact hle (Ideal.mem_map_of_mem ψ hFc)
  -- `F` is a form in `E[X₁ - c₁X₀, …, X_n - c_nX₀]`, hence `T ⊆ V_c` by minimality of `T`
  have hFV := mem_adjoin_translateModule_of_translate_mem_pow hF c hF0
  have hTV : linearFormModule E F ≤ translateModule c :=
    sInf_le ⟨translateModule_le_homogeneous c, hFV⟩
  -- the members of `V_c` vanish at `(1, c)`, i.e. `Y/X₀ ∈ N` for `Y ∈ T`
  let ev : MvPolynomial (Fin (n + 1)) E →ₐ[E] E := aeval (Fin.cons 1 c : Fin (n + 1) → E)
  have hevV : ∀ L ∈ translateModule c, ev L = 0 := by
    intro L hL
    induction hL using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      simp [ev]
    | zero => simp
    | add x y _ _ hx hy => rw [map_add, hx, hy, add_zero]
    | smul a x _ hx => rw [map_smul, hx, smul_zero]
  have hev : ∀ p, aeval c (dehomogenize E n p) = ev p := by
    intro p
    have : ((aeval c : MvPolynomial (Fin n) E →ₐ[E] E) : MvPolynomial (Fin n) E →+* E).comp
        (dehomogenize E n : MvPolynomial (Fin (n + 1)) E →+* MvPolynomial (Fin n) E) =
        (ev : MvPolynomial (Fin (n + 1)) E →+* E) := by
      apply ringHom_ext
      · intro a
        simp [ev, dehomogenize]
      · intro i
        refine Fin.cases ?_ (fun j => ?_) i
        · simp [ev, dehomogenize]
        · simp [ev, dehomogenize]
    exact RingHom.congr_fun this p
  intro Y hY
  rw [hev]
  exact hevV Y (hTV hY)

open MvPolynomial in
/-- Lemma 23, p. 267: "Since `k` is perfect, `k̃` is separable over `k` and, by Lemma 12, § 4, we see
that if `T̃` is the smallest `k̃`-module of linear forms in `S̃` such that `k̃[T̃]` contains `F`, then we
have `T̃ ∩ S = T`."  The inclusion `T ⊆ T̃ ∩ S` (the one used in the proof of Lemma 23): for any field
extension `K` of the perfect field `k` (every extension is separable, pp. 211–212), the smallest `k`-module
`T` of linear forms with `F ∈ k[T]` lies in `T̃ ∩ S` (`linearFormsOver`), where `T̃` is the smallest
`K`-module of linear forms with `F ∈ K[T̃]` (`F` read in `K[X₀, …, X_n]`).  Proof: `T̃` has the property
of Lemma 10 for `(F)` (since `F ∈ K[T̃]`), so by Lemma 12 `T̃ ∩ S` has it, i.e. `F ∈ k[T̃ ∩ S]`, and `T`
is contained in every such module. -/
private theorem linearFormModule_le_linearFormsOver [Hironaka.HironakaCitedResults.{u}] {k : Type u} [Field k] [PerfectField k]
    {n ν : ℕ} (hν : 0 < ν) {F : MvPolynomial (Fin (n + 1)) k}
    (hF : F ∈ homogeneousSubmodule (Fin (n + 1)) k ν) (K : Type u) [Field K] [Algebra k K] :
    linearFormModule k F ≤
      linearFormsOver k (linearFormModule K (MvPolynomial.map (algebraMap k K) F)) := by
  classical
  have hF' : MvPolynomial.map (algebraMap k K) F ∈
      homogeneousSubmodule (Fin (n + 1)) K ν :=
    (show F.IsHomogeneous ν from hF).map _
  obtain ⟨hV, hFK⟩ := linearFormModule_spec hν hF'
  have hsep := isSeparableFieldExtension_of_perfectField_aux k K
  let _ := MvPolynomial.gradedAlgebra (σ := Fin (n + 1)) (R := k)
  have hI : (Ideal.span {F}).IsHomogeneous (homogeneousSubmodule (Fin (n + 1)) k) :=
    Ideal.homogeneous_span _ _ (by rintro x rfl; exact ⟨ν, hF⟩)
  have hKτ : IsTauSubmoduleMv K (n + 1)
      ((Ideal.span {F}).map (MvPolynomial.map (algebraMap k K)))
      (linearFormModule K (MvPolynomial.map (algebraMap k K) F)) ν := by
    rw [Ideal.map_span, Set.image_singleton]
    exact isTauSubmoduleMv_span_singleton_aux hF' hV hFK
  have hkτ := (isTauSubmoduleMv_map_iff k hsep (Ideal.span {F}) hI _ hV ν hν).mp hKτ
  exact sInf_le ⟨inf_le_right, mem_adjoin_of_isTauSubmoduleMv_aux hF hkτ⟩

open MvPolynomial in
/-- `dehomogenize` commutes with the coefficientwise extension of scalars. -/
private theorem dehomogenize_map {k K : Type*} [Field k] [Field K] (f : k →+* K) (n : ℕ)
    (p : MvPolynomial (Fin (n + 1)) k) :
    dehomogenize K n (MvPolynomial.map f p) = MvPolynomial.map f (dehomogenize k n p) := by
  have : (dehomogenize K n : MvPolynomial (Fin (n + 1)) K →+* MvPolynomial (Fin n) K).comp
      (MvPolynomial.map f) = (MvPolynomial.map f).comp
      (dehomogenize k n : MvPolynomial (Fin (n + 1)) k →+* MvPolynomial (Fin n) k) := by
    apply ringHom_ext
    · intro a
      simp [dehomogenize]
    · intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · simp [dehomogenize]
      · simp [dehomogenize]
  exact RingHom.congr_fun this p

open MvPolynomial in
/-- Lemma 23, pp. 267–268, for a maximal ideal `N` of `A`: the proof printed after the reduction.
"Let `k̃` be an algebraic closure of `k`. Let `S̃ = k̃S`. Since `k` is perfect, `k̃` is separable over `k`
and, by Lemma 12, § 4, … `T̃ ∩ S = T`. In view of this fact, we can easily conclude that we may assume
the algebraic closedness of `k` in the proof of Lemma 23. (In fact, replace `k` by `k̃`.) Then every
maximal ideal `N` in `A` has a base of the form `(X₁/X₀ - c₁, …, X_n/X₀ - c_n)`, where `c_j ∈ k`.  The
assumption `ν_{NA_N}(F₀) ≥ ν` is equivalent to saying that `N^ν` contains `F₀`. [...] Thus `N` contains
`I₀`."

In Lean: `N` is the vanishing ideal of a point `c ∈ k̃ⁿ` (the Nullstellensatz, `MvPolynomial.
eq_vanishingIdeal_singleton_of_isMaximal`), `N^ν ∋ F₀` extends to `ker (aeval c) ^ ν ∋ F̃₀` over `k̃`,
`aeval_dehomogenize_eq_zero_of_mem_linearFormModule` shows `Y(1, c) = 0` for the members `Y` of the smallest
`k̃`-module `T̃`, and `T ⊆ T̃ ∩ S` (`linearFormModule_le_linearFormsOver`, Lemma 12) transfers this to `T`. -/
private theorem span_dehomogenize_le_of_isMaximal [Hironaka.HironakaCitedResults.{u}] {k : Type u} [Field k] [PerfectField k]
    {n ν : ℕ} (hν : 0 < ν) {F : MvPolynomial (Fin (n + 1)) k}
    (hF : F ∈ homogeneousSubmodule (Fin (n + 1)) k ν)
    (N : Ideal (MvPolynomial (Fin n) k)) [hNmax : N.IsMaximal]
    (hFN : dehomogenize k n F ∈ N ^ ν) :
    Ideal.span (dehomogenize k n ''
      (linearFormModule k F : Set (MvPolynomial (Fin (n + 1)) k))) ≤ N := by
  classical
  let K := AlgebraicClosure k
  -- `N` has a `K`-point `c`: `N = {a | a(c) = 0}`
  obtain ⟨c, hc⟩ := MvPolynomial.eq_vanishingIdeal_singleton_of_isMaximal K hNmax
  have hNmem : ∀ a, a ∈ N ↔ aeval c a = 0 := fun a => by
    rw [hc]
    exact MvPolynomial.mem_vanishingIdeal_singleton_iff c a
  -- replace `k` by `K`: `F ∈ K[X]`, and `F₀ ∈ N^ν` gives `F₀ ∈ ker (aeval c)^ν` over `K`
  have hF' : MvPolynomial.map (algebraMap k K) F ∈
      homogeneousSubmodule (Fin (n + 1)) K ν := (show F.IsHomogeneous ν from hF).map _
  have hFc : dehomogenize K n (MvPolynomial.map (algebraMap k K) F) ∈
      (RingHom.ker (aeval c : MvPolynomial (Fin n) K →ₐ[K] K)) ^ ν := by
    rw [dehomogenize_map]
    have hle : (N ^ ν).map (MvPolynomial.map (algebraMap k K)) ≤
        (RingHom.ker (aeval c : MvPolynomial (Fin n) K →ₐ[K] K)) ^ ν := by
      rw [Ideal.map_pow]
      refine Ideal.pow_right_mono (Ideal.map_le_iff_le_comap.mpr fun a ha => ?_) ν
      rw [Ideal.mem_comap, RingHom.mem_ker, aeval_map_algebraMap]
      exact (hNmem a).mp ha
    exact hle (Ideal.mem_map_of_mem _ hFN)
  have hcore := aeval_dehomogenize_eq_zero_of_mem_linearFormModule hF' c hFc
  -- `T ⊆ T̃ ∩ S` (Lemma 12), so the members `Y` of `T` satisfy `Y(1, c) = 0`
  have hT := linearFormModule_le_linearFormsOver hν hF K
  rw [Ideal.span_le]
  rintro _ ⟨Y, hY, rfl⟩
  have hYK : MvPolynomial.map (algebraMap k K) Y ∈
      linearFormModule K (MvPolynomial.map (algebraMap k K) F) := by
    have := (Submodule.mem_inf.mp (hT hY)).1
    simpa using this
  have h0 := hcore _ hYK
  rw [dehomogenize_map, aeval_map_algebraMap] at h0
  exact (hNmem _).mpr h0

open MvPolynomial in
/-- Lemma 23, p. 268: "The assumption `ν_{NA_N}(F₀) ≥ ν` is equivalent to saying that `N^ν` contains
`F₀`" for a maximal ideal `N` of `A`: `s F₀ ∈ N^ν` for some `s ∉ N`, and `N^ν` is primary
(`rad N^ν = N`). -/
private theorem mem_pow_of_le_ordElem_of_isMaximal {A : Type*} [CommRing A] [IsDomain A] (I : Ideal A)
    [hI : I.IsMaximal] {f : A} {ν : ℕ} (hν : 0 < ν)
    (h : (ν : ℕ∞) ≤ Ideal.ordElem (I.map (algebraMap A (Localization.AtPrime I)))
      (algebraMap A (Localization.AtPrime I) f)) : f ∈ I ^ ν := by
  obtain ⟨s, hsI, hsF⟩ : ∃ s ∉ I, s * f ∈ I ^ ν := by
    have h1 := mem_pow_of_le_ordElem_aux h
    rw [← Ideal.map_pow, IsLocalization.mem_map_algebraMap_iff I.primeCompl] at h1
    obtain ⟨⟨⟨a, ha⟩, ⟨t, ht⟩⟩, h⟩ := h1
    refine ⟨t, ht, ?_⟩
    have hinj := IsLocalization.injective (Localization.AtPrime I)
      (Ideal.primeCompl_le_nonZeroDivisors I)
    rw [← map_mul] at h
    rw [mul_comm, hinj h]
    exact ha
  have hrad : (I ^ ν).radical = I := by
    rw [Ideal.radical_pow I hν.ne', hI.isPrime.radical]
  have hprim : (I ^ ν).IsPrimary := Ideal.isPrimary_of_isMaximal_radical (by rw [hrad]; exact hI)
  rw [mul_comm] at hsF
  rcases (Ideal.isPrimary_iff.mp hprim).2 hsF with h' | h'
  · exact h'
  · rw [hrad] at h'
    exact absurd h' hsI

open MvPolynomial in
/-- Theorem 1 of § 3 (Zariski-Nagata, p. 218: `ν(J) ≥ ν(JR_P)`) for the regular domain `A`: for primes
`Q ⊆ Q'` of `A`, `ν_{QA_Q}(f) ≤ ν_{Q'A_{Q'}}(f)`.  This is the step "can be easily reduced to the case in
which `N` is a maximal ideal" of Lemma 23 (p. 267): a prime `N` with `ν_{NA_N}(F₀) ≥ ν` is contained in
maximal ideals `N'` with `ν_{N'A_{N'}}(F₀) ≥ ν`.  The proof is that of `Ideal.ordElem_localization_mono`
(`Hironaka/Ch3/StabilityCor3c.lean`) for the regular local ring `R`, with `R` replaced by the regular
ring `A` (every localization `A_{Q'}` is a regular local ring: `IsRegularRing`). -/
private theorem ordElem_localization_mono_of_isRegularRing [Hironaka.HironakaCitedResults.{u}] {A : Type u} [CommRing A] [IsDomain A]
    [IsRegularRing A] (Q Q' : Ideal A) [Q.IsPrime] [Q'.IsPrime] (hQQ' : Q ≤ Q') (f : A) :
    Ideal.ordElem (Q.map (algebraMap A (Localization.AtPrime Q)))
        (algebraMap A (Localization.AtPrime Q) f) ≤
      Ideal.ordElem (Q'.map (algebraMap A (Localization.AtPrime Q')))
        (algebraMap A (Localization.AtPrime Q') f) := by
  classical
  by_cases hf : f = 0
  · have h0 : Ideal.ordElem (Q'.map (algebraMap A (Localization.AtPrime Q')))
        (0 : Localization.AtPrime Q') = ⊤ := Ideal.ordElem_eq_top_iff.mpr fun ν => zero_mem _
    rw [hf, map_zero, map_zero, h0]
    exact le_top
  have _ : IsRegularLocalRing (Localization.AtPrime Q') := inferInstance
  have hdisj : Disjoint (Q'.primeCompl : Set A) (Q : Set A) :=
    Set.disjoint_left.mpr fun a ha haQ => ha (hQQ' haQ)
  have _ : (Q.map (algebraMap A (Localization.AtPrime Q'))).IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint Q'.primeCompl _ Q inferInstance hdisj
  have hpQ : (Q.map (algebraMap A (Localization.AtPrime Q'))).comap
      (algebraMap A (Localization.AtPrime Q')) = Q :=
    IsLocalization.under_map_of_isPrime_disjoint Q'.primeCompl _ inferInstance hdisj
  let p := Q.map (algebraMap A (Localization.AtPrime Q'))
  let g : A →+* Localization.AtPrime p :=
    (algebraMap (Localization.AtPrime Q') (Localization.AtPrime p)).comp
      (algebraMap A (Localization.AtPrime Q'))
  have hg : ∀ y : Q.primeCompl, IsUnit (g y) := by
    intro y
    refine (IsLocalization.AtPrime.isUnit_to_map_iff (Localization.AtPrime p) p _).mpr ?_
    intro hy
    have hy' : (y : A) ∈ p.comap (algebraMap A (Localization.AtPrime Q')) := hy
    exact y.2 (hpQ.le hy')
  let φ : Localization.AtPrime Q →+* Localization.AtPrime p :=
    IsLocalization.lift (M := Q.primeCompl) hg
  have hmap : (Q.map (algebraMap A (Localization.AtPrime Q))).map φ =
      IsLocalRing.maximalIdeal (Localization.AtPrime p) := by
    rw [Ideal.map_map, IsLocalization.lift_comp, ← Localization.AtPrime.map_eq_maximalIdeal,
      Ideal.map_map]
  have hx0 : algebraMap A (Localization.AtPrime Q') f ≠ 0 := by
    intro h
    apply hf
    exact IsLocalization.injective (Localization.AtPrime Q')
      (Ideal.primeCompl_le_nonZeroDivisors Q') (h.trans (map_zero _).symm)
  have h1 := nu_localization_le (Localization.AtPrime Q')
    (Ideal.span {algebraMap A (Localization.AtPrime Q') f})
    (by rwa [ne_eq, Ideal.span_singleton_eq_bot]) p
  simp only [Ideal.nu, Ideal.map_span, Set.image_singleton, Ideal.ord_span_singleton] at h1
  calc _ ≤ Ideal.ordElem ((Q.map (algebraMap A (Localization.AtPrime Q))).map φ)
        (φ (algebraMap A (Localization.AtPrime Q) f)) := Ideal.ordElem_le_ordElem_map φ _ _
    _ = Ideal.ordElem (IsLocalRing.maximalIdeal (Localization.AtPrime p))
        (algebraMap (Localization.AtPrime Q') (Localization.AtPrime p)
          (algebraMap A (Localization.AtPrime Q') f)) := by
      rw [hmap, IsLocalization.lift_eq]
      rfl
    _ ≤ Ideal.ordElem (IsLocalRing.maximalIdeal (Localization.AtPrime Q'))
        (algebraMap A (Localization.AtPrime Q') f) := h1
    _ = _ := by rw [Localization.AtPrime.map_eq_maximalIdeal]

/-- Lemma 23, pp. 267–268: "Let `S = k[X₀, X₁, …, X_n]` be a polynomial ring of `n + 1`
indeterminates over a perfect field `k`. Let `F` be a form of degree `ν > 0` in `S`. Let `T` be the
smallest `k`-module of linear forms in `S` such that `k[T]` contains `F`. Let
`A = k[X₁/X₀, …, X_n/X₀]`, `F₀ = F/X₀^ν ∈ A`, and `I₀` the ideal in `A` generated by the elements of
the form `Y/X₀` with `Y ∈ T`. If `N` is any prime ideal in `A` such that `ν_{NA_N}(F₀) ≥ ν`, then
`N` contains `I₀`."

"This lemma has the following geometric interpretation, which is interesting in its own right:
Let `X` be a projective linear scheme over a perfect field `k`, i.e., `X = Proj(S)` with a graded
polynomial ring `S = k[X₀, X₁, …, X_n]` of `n + 1` indeterminates over `k`. Let `V` be a subscheme
of `X` defined by a form of degree `ν > 0` in `S`, i.e., a hypersurface of order `ν` in `X`. Then
there exists a linear subscheme `L` of `X` which has the following property: a point `x` of `X`
belongs to `L` if and only if `x` is a point of `V` at which `V` has multiplicity `ν`. (`L` can be
empty.)" (p. 268; not formalized.)

(Formalization notes: `S` is `MvPolynomial (Fin (n + 1)) k` with `X₀ = X 0`; "a form of degree
`ν`" is membership in the homogeneous component of degree `ν` (the zero form satisfies the
conclusion trivially); `T` is `linearFormModule k F`; `A = k[X₁/X₀, …, X_n/X₀]` is identified with
`MvPolynomial (Fin n) k` through `dehomogenize` (module docstring of that definition), so that
`F₀ = dehomogenize F` and `I₀` is generated by the `dehomogenize Y`, `Y ∈ T`; `ν_{NA_N}` is the
order function of `NA_N` in the localization `A_N`.)

The proof is the printed one (pp. 267–268), step by step:
* "The proof can be easily reduced to the case in which `N` is a maximal ideal in `A`": `A` is a
  Jacobson ring, so the prime `N` is the intersection of the maximal ideals `N'` containing it, and
  `ν_{NA_N}(F₀) ≤ ν_{N'A_{N'}}(F₀)` for such `N'` by Theorem 1 of § 3
  (`ordElem_localization_mono_of_isRegularRing`); it remains to show `I₀ ⊆ N'`
  (`span_dehomogenize_le_of_isMaximal`).
* "Let `k̃` be an algebraic closure of `k` [...] by Lemma 12, § 4, we see that [...] `T̃ ∩ S = T`":
  `linearFormModule_le_linearFormsOver` (the inclusion `T ⊆ T̃ ∩ S`, the only one used), and "we may assume
  the algebraic closedness of `k`" is the passage from `k` to `k̃` in `span_dehomogenize_le_of_isMaximal`.
* "Then every maximal ideal `N` in `A` has a base of the form `(X_i/X₀ - c_i)`" (the Nullstellensatz),
  "`ν_{NA_N}(F₀) ≥ ν` is equivalent to saying that `N^ν` contains `F₀`"
  (`mem_pow_of_le_ordElem_of_isMaximal`), "`F` is contained in `(X_i - c_iX₀)^ν S`, so that `F` is a form in
  `k[X_i - c_iX₀]`" (`mem_adjoin_translateModule_of_translate_mem_pow`), "thus `N` contains `I₀` (see
  Lemma 10, § 4)" (`aeval_dehomogenize_eq_zero_of_mem_linearFormModule`).

Deviations from the paper (gaps filled; none in the route).  "Can be easily reduced to the case in which `N`
is a maximal ideal" is not argued by the paper: Lean uses the Jacobson property of `A` and Theorem 1 of § 3.
"We can easily conclude that we may assume the algebraic closedness of `k`" is carried out: `k` is replaced by
`k̃` at the point `c ∈ k̃ⁿ` of the maximal ideal `N` (Nullstellensatz), `N^ν ∋ F₀` is extended to
`ker (aeval c)^ν ∋ F̃₀`, and the conclusion for `T̃` is transferred to `T ⊆ T̃ ∩ S`.  "`N` has a base
`(X_i/X₀ - c_i)`" is used through the translation `ψ(a) = a(Y + c)`. -/

@[blueprint "lem:III.23"
  (statement := /-- Let $S=k[X_0,X_1,\dots,X_n]$ be a polynomial ring of $n+1$ indeterminates
    over a perfect field $k$. Let $F$ be a form of degree $\nu>0$ in $S$. Let $T$ be the smallest
    $k$-module of linear forms in $S$ such that $k[T]$ contains $F$. Let
    $A=k[X_1/X_0,\dots,X_n/X_0]$, $F_0=F/X_0^\nu\in A$, and $I_0$ the ideal in $A$ generated by
    the elements of the form $Y/X_0$ with $Y\in T$. If $N$ is any prime ideal in $A$ such that
    $\nu_{NA_N}(F_0)\ge\nu$, then $N$ contains $I_0$. (Lemma 23, p.~267.)

    This lemma has the following geometric interpretation: let $X=\operatorname{Proj}(S)$ be a
    projective linear scheme over a perfect field $k$, and $V$ a subscheme of $X$ defined by a
    form of degree $\nu>0$ in $S$, i.e., a hypersurface of order $\nu$ in $X$. Then there exists
    a linear subscheme $L$ of $X$ such that a point $x$ of $X$ belongs to $L$ if and only if $x$
    is a point of $V$ at which $V$ has multiplicity $\nu$ ($L$ can be empty). (p.~268; not
    formalized.)

    (Formalization note: $A$ is identified with the polynomial ring in the $n$ algebraically
    independent elements $X_i/X_0$, so that $F_0$ and the $Y/X_0$ are the dehomogenizations
    $G\mapsto G(1,X_1/X_0,\dots,X_n/X_0)$ of $F$ and $Y$.) -/)
  (proof := /-- The proof can be easily reduced to the case in which $N$ is a maximal ideal in
    $A$. Let $\tilde k$ be an algebraic closure of $k$. Let
    $\tilde S=\tilde kS=\tilde k[X_0,X_1,\dots,X_n]$. Since $k$ is perfect, $\tilde k$ is
    separable over $k$ and, by Lemma~12, \S4 (\cref{lem:III.12}), we see that if $\tilde T$ is the
    smallest $\tilde k$-module of linear forms in $\tilde S$ such that $\tilde k[\tilde T]$
    contains $F$, then we have $\tilde T\cap S=T$. In view of this fact, we can easily conclude
    that we may assume the algebraic closedness of $k$ in the proof of Lemma~23. (In fact,
    replace $k$ by $\tilde k$.) Then every maximal ideal $N$ in $A$ has a base of the form
    $(X_1/X_0-c_1,\dots,X_n/X_0-c_n)$, where $c_j\in k$. The assumption
    $\nu_{NA_N}(F_0)\ge\nu$ is equivalent to saying that $N^\nu$ contains $F_0$. This implies
    that $F$ is contained in $(X_1-c_1X_0,\dots,X_n-c_nX_0)^\nu S$, so that $F$ is a form in
    $k[X_1-c_1X_0,\dots,X_n-c_nX_0]$. Thus $N$ contains $I_0$. (See Lemma~10, \S4,
    \cref{lem:III.10}.) \qed

    \textbf{Lean.} The proof is the printed one. ``Easily reduced to the case in which $N$ is a
    maximal ideal'' is Theorem~1 of \S3 (\cref{thm:III.1}): for a maximal ideal $N'\supseteq N$ one has
    $\nu_{N'A_{N'}}(F_0)\ge\nu_{NA_N}(F_0)\ge\nu$, and $A$ is a Jacobson ring, so that $N$ is
    the intersection of these $N'$. The passage to $\tilde k$ is Lemma~12 (\cref{lem:III.12}) in the form
    $T\subseteq\tilde T\cap S$, applied at a point $c\in\tilde k^n$ of the maximal ideal $N$
    (Nullstellensatz); the minimality of $\tilde T$ is Lemma~10 (\cref{lem:III.10}). \textbf{Gaps in the paper
    filled.} The reductions to maximal ideals and to $\tilde k$ are asserted as ``easily'' (pp.~267--268);
    Lean carries them out. -/)
  (proofUses := ["thm:III.1", "lem:III.10", "lem:III.12"])
  (latexEnv := "lemma")]
theorem span_dehomogenize_le_of_ordElem_ge [Hironaka.HironakaCitedResults.{u}] [PerfectField k] (n ν : ℕ) (hν : 0 < ν)
    (F : MvPolynomial (Fin (n + 1)) k)
    (hF : F ∈ MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k ν)
    (N : Ideal (MvPolynomial (Fin n) k)) [N.IsPrime]
    (hN : (ν : ℕ∞) ≤ Ideal.ordElem
      (N.map (algebraMap (MvPolynomial (Fin n) k) (Localization.AtPrime N)))
      (algebraMap (MvPolynomial (Fin n) k) (Localization.AtPrime N) (dehomogenize k n F))) :
    Ideal.span (dehomogenize k n ''
      (linearFormModule k F : Set (MvPolynomial (Fin (n + 1)) k))) ≤ N := by
  classical
  -- "The proof can be easily reduced to the case in which `N` is a maximal ideal in `A`":
  -- `A` is a Jacobson ring, and the order does not drop at a maximal ideal `N' ⊇ N` (Theorem 1 of § 3)
  have hjac : N.jacobson = N := IsJacobsonRing.out' N (Ideal.IsPrime.isRadical inferInstance)
  refine le_trans ?_ hjac.le
  rw [Ideal.jacobson, le_sInf_iff]
  rintro N' ⟨hNN', hN'max⟩
  have hord := hN.trans (ordElem_localization_mono_of_isRegularRing N N' hNN' _)
  exact span_dehomogenize_le_of_isMaximal hν hF N'
    (mem_pow_of_le_ordElem_of_isMaximal N' hν hord)

end Lemma23

/-! ### Lemma 24 (pp. 268–269) -/

section Lemma24Aux

open MvPolynomial

/-- Scaling the variables of a form of degree `d` by `x` multiplies its value by `x ^ d`. -/
theorem eval₂_mul_eq_pow_mul_of_isHomogeneous {R B σ : Type*} [CommRing R] [CommRing B]
    (f : R →+* B) (g : σ → B) (x : B) {K : MvPolynomial σ R} {d : ℕ} (hK : K.IsHomogeneous d) :
    eval₂ f (fun i => x * g i) K = x ^ d * eval₂ f g K := by
  classical
  rw [MvPolynomial.eval₂_eq, MvPolynomial.eval₂_eq, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hdeg : m.degree = d := by
    have := hK (MvPolynomial.mem_support_iff.mp hm)
    rwa [Finsupp.degree_eq_weight_one]
  have : (∏ i ∈ m.support, (x * g i) ^ m i) = x ^ d * ∏ i ∈ m.support, g i ^ m i := by
    simp only [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
    rw [← hdeg]
    rfl
  rw [this]
  ring


/-- The reduction of the chart of a monoidal transform modulo the maximal ideals (pp. 209–210 and
268): for a minimal base `z = (x, z₁, …, z_n)` of `P` (with `x = T.x`), part of a minimal base of
`M`, there are a prime `N` of `(R/M)[T₁, …, T_n]` and a local homomorphism
`Ψ : R₁ → (R/M)[T]_N` (the composite of `R₁ → R₁/(x) ≅ (R/P)[T]_q` and the reduction modulo `M`),
mapping `c ∈ R` to its residue class and every `u_i = z_i/x` to `T_i`. -/
theorem MonoidalTransform.exists_chart_hom {R : Type u} [CommRing R] [IsRegularLocalRing R]
    [IsDomain R] {P : Ideal R} [P.IsPrime] (T : MonoidalTransform R P)
    (hS : IsRegularLocalRing (R ⧸ P))
    {S : Finset R} {n : ℕ} {z : Fin (n + 1) → R}
    (hSM : Ideal.span (S : Set R) = maximalIdeal R)
    (hScard : S.card = (maximalIdeal R).spanFinrank) (hinj : Function.Injective z)
    (hzS : ∀ i, z i ∈ S) (hz0 : z 0 = T.x) (hzP : Ideal.span (Set.range z) = P) :
    ∃ (N : Ideal (MvPolynomial (Fin n) (R ⧸ maximalIdeal R))) (_ : N.IsPrime)
      (Ψ : T.ring →+* Localization.AtPrime N), IsLocalHom Ψ ∧
      (∀ c : R, Ψ (T.toRing c) = algebraMap (MvPolynomial (Fin n) (R ⧸ maximalIdeal R))
        (Localization.AtPrime N) (MvPolynomial.C (Ideal.Quotient.mk (maximalIdeal R) c))) ∧
      ∀ u : Fin n → T.ring, (∀ i, T.toRing T.x * u i = T.toRing (z i.succ)) →
        ∀ i, Ψ (u i) = algebraMap (MvPolynomial (Fin n) (R ⧸ maximalIdeal R))
          (Localization.AtPrime N) (MvPolynomial.X i) := by
  classical
  obtain ⟨q, hq, e, hqC, -, hec, heX⟩ :=
    T.exists_quotient_equiv_localization hS hSM hScard hinj hzS hz0 hzP
  have hPM : P ≤ maximalIdeal R := IsLocalRing.le_maximalIdeal (Ideal.IsPrime.ne_top ‹_›)
  -- reduction `R/P → R/M`
  let ρ : R ⧸ P →+* R ⧸ maximalIdeal R := Ideal.Quotient.factor hPM
  have hρs : Function.Surjective ρ := Ideal.Quotient.factor_surjective hPM
  have hρmk : ∀ c : R, ρ (Ideal.Quotient.mk P c) = Ideal.Quotient.mk (maximalIdeal R) c :=
    fun c => Ideal.Quotient.factor_mk hPM c
  have hmkM : ∀ a ∈ maximalIdeal R, Ideal.Quotient.mk P a ∈ maximalIdeal (R ⧸ P) := by
    intro a ha
    have : IsLocalHom (Ideal.Quotient.mk P) :=
      IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective
    exact (IsLocalRing.mem_maximalIdeal _).mpr fun hu =>
      (IsLocalRing.mem_maximalIdeal a).mp ha (isUnit_of_map_unit (Ideal.Quotient.mk P) a hu)
  have hker : RingHom.ker (MvPolynomial.map ρ) ≤ q := by
    rw [MvPolynomial.ker_map, Ideal.map_le_iff_le_comap]
    intro a ha
    rw [RingHom.mem_ker] at ha
    obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective a
    rw [hρmk, Ideal.Quotient.eq_zero_iff_mem] at ha
    have := hmkM c ha
    rw [← hqC] at this
    exact this
  have hmap_surj : Function.Surjective (MvPolynomial.map ρ : MvPolynomial (Fin n) (R ⧸ P) →+*
      MvPolynomial (Fin n) (R ⧸ maximalIdeal R)) := MvPolynomial.map_surjective ρ hρs
  have hN : (q.map (MvPolynomial.map ρ)).IsPrime :=
    Ideal.map_isPrime_of_surjective hmap_surj hker
  have hcomap : q = (q.map (MvPolynomial.map ρ)).comap (MvPolynomial.map ρ) := by
    rw [Ideal.comap_map_of_surjective' _ hmap_surj, sup_eq_left.mpr hker]
  have hnt : Nontrivial (T.ring ⧸ Ideal.span {T.xR}) := e.symm.toEquiv.nontrivial
  have : IsLocalHom (Ideal.Quotient.mk (Ideal.span {T.xR})) :=
    IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective
  have : IsLocalHom e.symm.toRingHom :=
    ⟨fun a ha => by simpa using ha.map e.toRingHom⟩
  have hloc := Localization.isLocalHom_localRingHom q (q.map (MvPolynomial.map ρ))
    (MvPolynomial.map ρ) hcomap
  refine ⟨q.map (MvPolynomial.map ρ), hN,
    (Localization.localRingHom q (q.map (MvPolynomial.map ρ)) (MvPolynomial.map ρ) hcomap).comp
      (e.symm.toRingHom.comp (Ideal.Quotient.mk (Ideal.span {T.xR}))),
    inferInstance, ?_, ?_⟩
  · intro c
    have h1 : e.symm.toRingHom (Ideal.Quotient.mk (Ideal.span {T.xR}) (T.toRing c)) =
        algebraMap (MvPolynomial (Fin n) (R ⧸ P)) (Localization.AtPrime q)
          (MvPolynomial.C (Ideal.Quotient.mk P c)) := by
      rw [← hec c]
      exact e.symm_apply_apply _
    simp only [RingHom.comp_apply]
    rw [h1, Localization.localRingHom_to_map, MvPolynomial.map_C, hρmk]
  · intro u hu i
    have h1 : e.symm.toRingHom (Ideal.Quotient.mk (Ideal.span {T.xR}) (u i)) =
        algebraMap (MvPolynomial (Fin n) (R ⧸ P)) (Localization.AtPrime q) (MvPolynomial.X i) := by
      rw [← (heX u hu i).2]
      exact e.symm_apply_apply _
    simp only [RingHom.comp_apply]
    rw [h1, Localization.localRingHom_to_map, MvPolynomial.map_X]


/-- Evaluation in the chart: if `x^d w = K(z)` for a form `K` of degree `d` in `R[X₀, …, X_n]`
(`z₀ = x`, `z_{i+1} = x u_i`), then any ring homomorphism `Ψ` from `R₁` which sends `c ∈ R` to
`ι (κ c)` and `u_i` to `ι (ε i)` maps `w` to `ι (K^κ (1, ε))`, the dehomogenization of `K^κ`
(`R₁` being a domain, `x^d` is cancelled). -/
theorem MonoidalTransform.chart_apply_eq_eval₂ {R : Type u} [CommRing R] [IsRegularLocalRing R]
    [IsDomain R] {P : Ideal R} (T : MonoidalTransform R P) [IsDomain T.ring] {n : ℕ}
    {z : Fin (n + 1) → R}
    (hz0 : z 0 = T.x) {A B : Type*} [CommRing A] [CommRing B] (Ψ : T.ring →+* B) (κ : R →+* A)
    (ι : A →+* B) (ε : Fin n → A) (u : Fin n → T.ring)
    (hu : ∀ i, T.toRing T.x * u i = T.toRing (z i.succ))
    (hΨc : ∀ c, Ψ (T.toRing c) = ι (κ c)) (hΨu : ∀ i, Ψ (u i) = ι (ε i))
    {K : MvPolynomial (Fin (n + 1)) R} {d : ℕ} (hK : K.IsHomogeneous d) {w : T.ring}
    (hw : T.toRing T.x ^ d * w = T.toRing (eval z K)) :
    Ψ w = ι (eval₂ κ (Fin.cons 1 ε : Fin (n + 1) → A) K) := by
  classical
  have hx0 : T.toRing T.x ≠ 0 := fun h =>
    T.x_ne_zero (MonoidalTransform.toRing_injective T (h.trans (map_zero _).symm))
  have h1 : T.toRing (eval z K) = eval₂ T.toRing
      (fun i => T.toRing T.x * (Fin.cons 1 u : Fin (n + 1) → T.ring) i) K := by
    have := MvPolynomial.eval₂_comp_left T.toRing (RingHom.id R) z K
    rw [RingHom.comp_id] at this
    refine (this.trans ?_)
    congr 1
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [hz0]
    · simp [hu j]
  have h2 := eval₂_mul_eq_pow_mul_of_isHomogeneous T.toRing (Fin.cons 1 u : Fin (n + 1) → T.ring)
    (T.toRing T.x) hK
  have hwK : w = eval₂ T.toRing (Fin.cons 1 u : Fin (n + 1) → T.ring) K := by
    refine mul_left_cancel₀ (pow_ne_zero d hx0) ?_
    rw [hw, h1, h2]
  rw [hwK, MvPolynomial.eval₂_comp_left Ψ T.toRing, MvPolynomial.eval₂_comp_left ι κ]
  congr 1
  · exact RingHom.ext hΨc
  · funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp
    · simp [hΨu j]


end Lemma24Aux

section ChangeOfDenominator

variable {R : Type u} [CommRing R] [IsRegularLocalRing R] [IsDomain R] {P : Ideal R}

/-- The canonical map `R' → Frac(R)` of a monoidal transform is injective. -/
theorem MonoidalTransform.toFractionRing_injective (T : MonoidalTransform R P) :
    Function.Injective T.toFractionRing := by
  unfold MonoidalTransform.toFractionRing
  rw [IsLocalization.lift_injective_iff]
  intro a b
  constructor
  · intro h
    have : a = b := IsLocalization.injective T.ring (Ideal.primeCompl_le_nonZeroDivisors T.M') h
    rw [this]
  · intro h
    have : a = b := Subtype.ext h
    rw [this]

/-- The canonical map `R' → Frac(R)` restricts to the inclusion on `R[x⁻¹P]`. -/
theorem MonoidalTransform.toFractionRing_algebraMap (T : MonoidalTransform R P)
    (a : blowupAlgebra R P T.x) :
    T.toFractionRing (algebraMap (blowupAlgebra R P T.x) T.ring a) = (a : FractionRing R) :=
  IsLocalization.lift_eq _ a

/-- If the subalgebra `R[x⁻¹P]` of `Frac(R)` lies in the monoidal transform `R'` (as a subring of
`Frac(R)`), it embeds into `R'`. -/
noncomputable def MonoidalTransform.embedOfLE (T : MonoidalTransform R P) {x'' : R}
    (h : ∀ a ∈ blowupAlgebra R P x'', a ∈ T.toFractionRing.range) :
    blowupAlgebra R P x'' →+* T.ring :=
  (RingEquiv.ofBijective T.toFractionRing.rangeRestrict
    ⟨fun a b hab => T.toFractionRing_injective (by simpa using congrArg Subtype.val hab),
      T.toFractionRing.rangeRestrict_surjective⟩).symm.toRingHom.comp
    ((blowupAlgebra R P x'').val.toRingHom.codRestrict T.toFractionRing.range fun a => h a a.2)

/-- The embedding `embedOfLE` is the inclusion of subrings of `Frac(R)`. -/
theorem MonoidalTransform.toFractionRing_embedOfLE (T : MonoidalTransform R P) {x'' : R}
    (h : ∀ a ∈ blowupAlgebra R P x'', a ∈ T.toFractionRing.range) (a : blowupAlgebra R P x'') :
    T.toFractionRing (T.embedOfLE h a) = (a : FractionRing R) := by
  have h1 := RingEquiv.apply_symm_apply (RingEquiv.ofBijective T.toFractionRing.rangeRestrict
    ⟨fun a b hab => T.toFractionRing_injective (by simpa using congrArg Subtype.val hab),
      T.toFractionRing.rangeRestrict_surjective⟩) ⟨(a : FractionRing R), h a a.2⟩
  exact congrArg Subtype.val h1

/-- The embedding `embedOfLE` is compatible with the maps from `R`. -/
theorem MonoidalTransform.embedOfLE_algebraMap (T : MonoidalTransform R P) {x'' : R}
    (h : ∀ a ∈ blowupAlgebra R P x'', a ∈ T.toFractionRing.range) (r : R) :
    T.embedOfLE h (algebraMap R (blowupAlgebra R P x'') r) = T.toRing r := by
  refine T.toFractionRing_injective ?_
  rw [T.toFractionRing_embedOfLE, T.toFractionRing_toRing]
  rfl

/-- Change of denominator (pp. 209–210 and the proof of Lemma 24, p. 268: "Then we may take
`y_τ` to be the element `x`"): if `x' ∈ P` satisfies `(x')R' = PR'` for a monoidal transform `R'`
with center `P`, then `R'` is also (canonically isomorphic to) the monoidal transform with
denominator `x'`, that is `R[x'⁻¹P]_{M''}` with `M'' = M'R' ∩ R[x'⁻¹P]`. -/
theorem MonoidalTransform.exists_equiv_of_denominator (T : MonoidalTransform R P)
    {x' : R} (hx'P : x' ∈ P) (hx'0 : x' ≠ 0)
    (hx' : Ideal.span {T.toRing x'} = P.map T.toRing) :
    ∃ (T' : MonoidalTransform R P) (σ : T.ring ≃+* T'.ring), T'.x = x' ∧
      ∀ r, σ (T.toRing r) = T'.toRing r := by
  classical
  let K := FractionRing R
  let φ := T.toFractionRing
  have hφ : Function.Injective φ := T.toFractionRing_injective
  have hx'K : algebraMap R K x' ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective R K)).mpr hx'0
  have hx0K : algebraMap R K T.x ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective R K)).mpr T.x_ne_zero
  have hφto : ∀ r, φ (T.toRing r) = algebraMap R K r := T.toFractionRing_toRing
  have hx'R : T.toRing x' ≠ 0 := fun h => hx'0 (MonoidalTransform.toRing_injective T
    (h.trans (map_zero _).symm))
  have hx0R : T.toRing T.x ≠ 0 := fun h => T.x_ne_zero (MonoidalTransform.toRing_injective T
    (h.trans (map_zero _).symm))
  -- `p / x'` lies in `R'` for `p ∈ P`
  have hdiv : ∀ p ∈ P, ∃ w : T.ring, T.toRing x' * w = T.toRing p := by
    intro p hp
    have hmem : T.toRing p ∈ Ideal.span {T.toRing x'} := by
      rw [hx']
      exact Ideal.mem_map_of_mem _ hp
    obtain ⟨w, hw⟩ := Ideal.mem_span_singleton'.mp hmem
    exact ⟨w, by rw [mul_comm]; exact hw⟩
  have hmem : ∀ a ∈ blowupAlgebra R P x', a ∈ φ.range := by
    intro a ha
    induction ha using Algebra.adjoin_induction with
    | mem y hy =>
      obtain ⟨p, hp, rfl⟩ := hy
      obtain ⟨w, hw⟩ := hdiv p hp
      refine ⟨w, ?_⟩
      have := congrArg φ hw
      rw [map_mul, hφto, hφto] at this
      show φ w = _
      rw [eq_div_iff hx'K, mul_comm]
      exact this
    | algebraMap r => exact ⟨T.toRing r, hφto r⟩
    | add y z _ _ hy hz => exact add_mem hy hz
    | mul y z _ _ hy hz => exact mul_mem hy hz
  -- the monoidal transform `T'` with denominator `x'`, defined through the embedding of `R[x'⁻¹P]`
  obtain ⟨T', hT'x, hT'M⟩ : ∃ (T' : MonoidalTransform R P) (hx : T'.x = x'),
      ∀ a : blowupAlgebra R P T'.x, a ∈ T'.M' ↔
        T.embedOfLE (fun b hb => hmem b (hx ▸ hb)) a ∈ maximalIdeal T.ring := by
    refine ⟨⟨x', hx'P, hx'0, Ideal.comap (T.embedOfLE hmem) (maximalIdeal T.ring),
      Ideal.comap_isPrime _ _, ?_⟩, rfl, fun a => Iff.rfl⟩
    rw [Ideal.map_le_iff_le_comap]
    intro m hm
    rw [Ideal.mem_comap, Ideal.mem_comap, T.embedOfLE_algebraMap]
    exact (IsLocalRing.mem_maximalIdeal _).mpr (fun hu =>
      (IsLocalRing.mem_maximalIdeal m).mp hm (isUnit_of_map_unit T.toRing m hu))
  subst hT'x
  have hmem' : ∀ b ∈ blowupAlgebra R P T'.x, b ∈ φ.range := hmem
  let ι' : blowupAlgebra R P T'.x →+* T.ring := T.embedOfLE hmem'
  have hι : ∀ a, φ (ι' a) = (a : K) := fun a => T.toFractionRing_embedOfLE hmem' a
  have hιalg : ∀ r, ι' (algebraMap R (blowupAlgebra R P T'.x) r) = T.toRing r :=
    fun r => T.embedOfLE_algebraMap hmem' r
  have hunit : ∀ y : T'.M'.primeCompl, IsUnit (ι' y) := by
    intro y
    refine IsLocalRing.notMem_maximalIdeal.mp fun h => y.2 ((hT'M y).mpr h)
  -- the comparison map `λ : R[x'⁻¹P]_{M''} → R'`
  let lam : T'.ring →+* T.ring := IsLocalization.lift (M := T'.M'.primeCompl) (S := T'.ring)
    (g := ι') hunit
  have hlam : ∀ a, lam (algebraMap (blowupAlgebra R P T'.x) T'.ring a) = ι' a := fun a =>
    IsLocalization.lift_eq hunit a
  have hlamto : ∀ r, lam (T'.toRing r) = T.toRing r := by
    intro r
    show lam (algebraMap (blowupAlgebra R P T'.x) T'.ring
      (algebraMap R (blowupAlgebra R P T'.x) r)) = _
    rw [hlam]
    exact hιalg r
  have hlaminj : Function.Injective lam := by
    have hcomp : φ.comp lam = T'.toFractionRing := by
      refine IsLocalization.ringHom_ext T'.M'.primeCompl ?_
      refine RingHom.ext fun a => ?_
      simp only [RingHom.comp_apply]
      rw [hlam]
      exact (hι a).trans (T'.toFractionRing_algebraMap a).symm
    intro a b hab
    apply T'.toFractionRing_injective
    rw [← hcomp]
    exact congrArg φ hab
  have hlamunit : ∀ v, IsUnit (lam v) → IsUnit v := by
    intro v hv
    obtain ⟨⟨b, t⟩, rfl⟩ := IsLocalization.mk'_surjective T'.M'.primeCompl v
    have h1 := (IsLocalization.lift_mk'_spec hunit b
      (lam (IsLocalization.mk' T'.ring b t)) t).mp rfl
    have hι_b : IsUnit (ι' b) := by
      rw [h1]
      exact (hunit t).mul hv
    have hbM : b ∈ T'.M'.primeCompl := fun hb =>
      (IsLocalRing.notMem_maximalIdeal.mpr hι_b) ((hT'M b).mp hb)
    exact (IsLocalization.AtPrime.isUnit_mk'_iff T'.ring T'.M' b t).mpr hbM
  -- `λ` is surjective
  have hx'Rne : T.toRing T'.x ≠ 0 := hx'R
  obtain ⟨w₁, hw₁⟩ : ∃ w₁ : T.ring, w₁ * T.toRing T.x = T.toRing T'.x := by
    have : T.toRing T'.x ∈ Ideal.span {T.xR} := by
      rw [T.span_xR_eq_map]
      exact Ideal.mem_map_of_mem _ hx'P
    exact Ideal.mem_span_singleton'.mp this
  have hφw₁ : φ w₁ * algebraMap R K T.x = algebraMap R K T'.x := by
    have := congrArg φ hw₁
    rwa [map_mul, hφto, hφto] at this
  -- the element `α = x₀ / x'` of `R[x'⁻¹P]` and its image in `R'`
  let bp : ∀ p ∈ P, blowupAlgebra R P T'.x := fun p hp =>
    ⟨algebraMap R K p / algebraMap R K T'.x, Algebra.subset_adjoin ⟨p, hp, rfl⟩⟩
  have hbp : ∀ p hp, T.toRing T'.x * ι' (bp p hp) = T.toRing p := by
    intro p hp
    refine hφ ?_
    rw [map_mul, hι, hφto, hφto]
    show algebraMap R K T'.x * (algebraMap R K p / algebraMap R K T'.x) = _
    rw [← mul_div_assoc, mul_comm, mul_div_assoc, div_self hx'K, mul_one]
  have hα : ι' (bp T.x T.x_mem) * w₁ = 1 := by
    refine mul_left_cancel₀ hx'Rne ?_
    calc T.toRing T'.x * (ι' (bp T.x T.x_mem) * w₁)
        = (T.toRing T'.x * ι' (bp T.x T.x_mem)) * w₁ := by ring
      _ = T.toRing T.x * w₁ := by rw [hbp T.x T.x_mem]
      _ = T.toRing T'.x * 1 := by rw [mul_comm, hw₁, mul_one]
  have hαunit : IsUnit (algebraMap (blowupAlgebra R P T'.x) T'.ring (bp T.x T.x_mem)) := by
    refine hlamunit _ ?_
    rw [hlam]
    exact isUnit_iff_exists_inv.mpr ⟨w₁, hα⟩
  obtain ⟨u, hu⟩ := hαunit
  have hw₁L : w₁ ∈ lam.range := by
    refine ⟨((u⁻¹ : T'.ringˣ) : T'.ring), ?_⟩
    have h1 : lam (u : T'.ring) = ι' (bp T.x T.x_mem) := by rw [hu, hlam]
    have h2 : lam ((u⁻¹ : T'.ringˣ) : T'.ring) * ι' (bp T.x T.x_mem) = 1 := by
      rw [← h1, ← map_mul, Units.inv_mul, map_one]
    calc lam ((u⁻¹ : T'.ringˣ) : T'.ring)
        = lam ((u⁻¹ : T'.ringˣ) : T'.ring) * (ι' (bp T.x T.x_mem) * w₁) := by rw [hα, mul_one]
      _ = (lam ((u⁻¹ : T'.ringˣ) : T'.ring) * ι' (bp T.x T.x_mem)) * w₁ := by ring
      _ = w₁ := by rw [h2, one_mul]
  have hKmem : ∀ y ∈ blowupAlgebra R P T.x, ∃ w ∈ lam.range, φ w = y := by
    intro y hy
    induction hy using Algebra.adjoin_induction with
    | mem y hy =>
      obtain ⟨p, hp, rfl⟩ := hy
      refine ⟨w₁ * ι' (bp p hp), mul_mem hw₁L ⟨algebraMap _ T'.ring (bp p hp), hlam _⟩, ?_⟩
      rw [map_mul, hι]
      show φ w₁ * (algebraMap R K p / algebraMap R K T'.x) = _
      rw [eq_div_iff hx0K, mul_right_comm, hφw₁, ← mul_div_assoc, mul_comm, mul_div_assoc,
        div_self hx'K, mul_one]
    | algebraMap r => exact ⟨T.toRing r, ⟨T'.toRing r, hlamto r⟩, hφto r⟩
    | add y z _ _ hy hz =>
      obtain ⟨w, hw, hwy⟩ := hy
      obtain ⟨w', hw', hwz⟩ := hz
      exact ⟨w + w', add_mem hw hw', by rw [map_add, hwy, hwz]⟩
    | mul y z _ _ hy hz =>
      obtain ⟨w, hw, hwy⟩ := hy
      obtain ⟨w', hw', hwz⟩ := hz
      exact ⟨w * w', mul_mem hw hw', by rw [map_mul, hwy, hwz]⟩
  have hAL : ∀ a : blowupAlgebra R P T.x, algebraMap (blowupAlgebra R P T.x) T.ring a ∈
      lam.range := by
    intro a
    obtain ⟨y, hy, hφy⟩ := hKmem a.1 a.2
    have : y = algebraMap (blowupAlgebra R P T.x) T.ring a :=
      hφ (by rw [hφy, T.toFractionRing_algebraMap])
    exact this ▸ hy
  have hlamsurj : Function.Surjective lam := by
    intro w
    obtain ⟨⟨a, s⟩, hws⟩ := IsLocalization.surj T.M'.primeCompl w
    obtain ⟨b, hb⟩ := hAL a
    obtain ⟨v, hv⟩ := hAL s
    have hvunit : IsUnit v := hlamunit v (by
      rw [hv]
      exact IsLocalization.map_units T.ring s)
    obtain ⟨u, hu⟩ := hvunit
    refine ⟨b * ((u⁻¹ : T'.ringˣ) : T'.ring), ?_⟩
    have h1 : lam ((u : T'.ring)) = algebraMap (blowupAlgebra R P T.x) T.ring s := by rw [hu, hv]
    have h2 : lam ((u⁻¹ : T'.ringˣ) : T'.ring) * lam (u : T'.ring) = 1 := by
      rw [← map_mul, Units.inv_mul, map_one]
    calc lam (b * ((u⁻¹ : T'.ringˣ) : T'.ring))
        = algebraMap (blowupAlgebra R P T.x) T.ring a * lam ((u⁻¹ : T'.ringˣ) : T'.ring) := by
          rw [map_mul, hb]
      _ = w * lam (u : T'.ring) * lam ((u⁻¹ : T'.ringˣ) : T'.ring) := by rw [h1, hws]
      _ = w * (lam ((u⁻¹ : T'.ringˣ) : T'.ring) * lam (u : T'.ring)) := by ring
      _ = w := by rw [h2, mul_one]
  let σ : T.ring ≃+* T'.ring := (RingEquiv.ofBijective lam ⟨hlaminj, hlamsurj⟩).symm
  refine ⟨T', σ, rfl, fun r => ?_⟩
  apply hlaminj
  have h1 : lam (σ (T.toRing r)) = T.toRing r :=
    (RingEquiv.ofBijective lam ⟨hlaminj, hlamsurj⟩).apply_symm_apply _
  rw [h1, hlamto]

end ChangeOfDenominator

section MinimalBase

variable {R : Type u} [CommRing R] [IsRegularLocalRing R]

/-- Part of a regular system of parameters contained in a prime `P` with `R/P` regular can be
completed to a regular system of parameters `Z` having a subset `T ⊇ W` which generates `P`
(iterated exchange step, `ExtendsToRSOP.exchange`). -/
theorem exists_isRegularSystemOfParameters_subset_span_eq_prime (P : Ideal R) [P.IsPrime]
    (hS : IsRegularLocalRing (R ⧸ P)) (W : Finset R) (hWP : ∀ w ∈ W, w ∈ P)
    (hW : ExtendsToRSOP R W) :
    ∃ Z T : Finset R, IsRegularSystemOfParameters R Z ∧ W ⊆ T ∧ T ⊆ Z ∧
      Ideal.span (T : Set R) = P := by
  classical
  have key : ∀ W : Finset R, (∀ w ∈ W, w ∈ P) → ExtendsToRSOP R W →
      ∃ Z T : Finset R, IsRegularSystemOfParameters R Z ∧ W ⊆ Z ∧ T ⊆ Z ∧
        Ideal.span (T : Set R) = P := by
    intro W
    induction W using Finset.induction_on with
    | empty =>
      intro _ _
      obtain ⟨S, T, hSM, hScard, hTS, hTP⟩ := exists_finset_span_eq_prime R P hS
      exact ⟨S, T, rsop_of_span_of_card_le hSM hScard.le, Finset.empty_subset _, hTS, hTP⟩
    | insert w W₀ hw ih =>
      intro hWP hext
      obtain ⟨Z, T, hZ, hWZ, hTZ, hTP⟩ := ih (fun a ha => hWP a (Finset.mem_insert_of_mem ha))
        (hext.mono (Finset.subset_insert _ _))
      obtain ⟨Z', T', hZ', hJ, hwZ', hT'Z', hT'⟩ := ExtendsToRSOP.exchange hZ hWZ hTZ
        (f := w) (hTP ▸ hWP w (Finset.mem_insert_self _ _)) hw hext
      exact ⟨Z', T', hZ', Finset.insert_subset hwZ' hJ, hT'Z', hT'.trans hTP⟩
  obtain ⟨Z, T, hZ, hWZ, hTZ, hTP⟩ := key W hWP hW
  refine ⟨Z, T, hZ, fun w hw => ?_, hTZ, hTP⟩
  by_contra hwT
  exact rsop_notMem_span hZ hTZ (hWZ hw) hwT (hTP ▸ hWP w hw)

/-- A minimal base `(x, t₁, …, t_n)` of `P` beginning with the prescribed element `x ∈ W` and
containing the independent family `W ⊆ P`, part of a minimal system of generators of `M`
(the shape used on p. 268: "a minimal base of `P` of the form
`(z₁, …, z_r, y₁, …, y_{τ−1}, x, x₁, …, x_s)`"). -/
theorem exists_minimalBase_first (P : Ideal R) [P.IsPrime] (hS : IsRegularLocalRing (R ⧸ P))
    (W : Finset R) (hWP : ∀ w ∈ W, w ∈ P) (hW : ExtendsToRSOP R W) {x : R} (hx : x ∈ W) :
    ∃ (S : Finset R) (n : ℕ) (z : Fin (n + 1) → R),
      Ideal.span (S : Set R) = maximalIdeal R ∧ S.card = (maximalIdeal R).spanFinrank ∧
      Function.Injective z ∧ (∀ i, z i ∈ S) ∧ z 0 = x ∧ Ideal.span (Set.range z) = P ∧
      ∀ w ∈ W, w ≠ x → ∃ i : Fin n, z i.succ = w := by
  classical
  obtain ⟨Z, T, hZ, hWT, hTZ, hTP⟩ :=
    exists_isRegularSystemOfParameters_subset_span_eq_prime P hS W hWP hW
  have hxT : x ∈ T := hWT hx
  let e := (T.erase x).equivFin
  have hxne : ∀ i, ((e.symm i : T.erase x) : R) ≠ x := fun i =>
    (Finset.mem_erase.mp (e.symm i).2).1
  refine ⟨Z, (T.erase x).card, Fin.cons x (fun i => ((e.symm i : T.erase x) : R)),
    hZ.1, rsop_card_eq_spanFinrank hZ, ?_, ?_, Fin.cons_zero _ _, ?_, ?_⟩
  · rw [Fin.cons_injective_iff]
    refine ⟨fun ⟨i, hi⟩ => hxne i hi, fun i j hij => e.symm.injective (Subtype.ext hij)⟩
  · intro i
    refine Fin.cases (hTZ hxT) (fun i => ?_) i
    simp only [Fin.cons_succ]
    exact hTZ (Finset.mem_of_mem_erase (e.symm i).2)
  · have hrange : Set.range (fun i => ((e.symm i : T.erase x) : R)) = (T.erase x : Set R) := by
      ext a
      constructor
      · rintro ⟨i, rfl⟩
        exact (e.symm i).2
      · intro ha
        exact ⟨e ⟨a, ha⟩, by simp⟩
    rw [Fin.range_cons, hrange, ← hTP]
    congr 1
    ext a
    simp only [Set.mem_insert_iff, Finset.mem_coe, Finset.mem_erase]
    constructor
    · rintro (rfl | ⟨-, ha⟩)
      · exact hxT
      · exact ha
    · intro ha
      by_cases hax : a = x
      · exact Or.inl hax
      · exact Or.inr ⟨hax, ha⟩
  · intro w hw hwx
    have hwT : w ∈ T.erase x := Finset.mem_erase.mpr ⟨hwx, hWT hw⟩
    exact ⟨e ⟨w, hwT⟩, by simp⟩

end MinimalBase

section TauZIndependence

/-- If `a ∈ (v_i)_{i ∈ T} + I²` with `a, v_i ∈ I`, then the class of `a` in `gr¹_I` is a
combination of the classes of the `v_i` (`gr¹_I(A) = I/I²`). -/
theorem mk_one_mem_span_of_mem_span_sup_sq {A : Type*} [CommRing A] (I : Ideal A) {ι : Type*}
    (v : ι → A) (hv : ∀ i, v i ∈ I ^ 1) (T : Set ι) {a : A} (ha : a ∈ I ^ 1)
    (h : a ∈ Ideal.span (v '' T) ⊔ I ^ 2) :
    AssocGraded.mk I 1 a ha ∈ Submodule.span (A ⧸ I)
      ((fun i => AssocGraded.mk I 1 (v i) (hv i)) '' T) := by
  obtain ⟨s, hs, m, hm, rfl⟩ := Submodule.mem_sup.mp h
  have hspan : ∀ s ∈ Ideal.span (v '' T), ∃ hs1 : s ∈ I ^ 1,
      AssocGraded.mk I 1 s hs1 ∈ Submodule.span (A ⧸ I)
        ((fun i => AssocGraded.mk I 1 (v i) (hv i)) '' T) := by
    intro s hs
    induction hs using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨i, hi, rfl⟩ := hx
      exact ⟨hv i, Submodule.subset_span ⟨i, hi, rfl⟩⟩
    | zero =>
      refine ⟨zero_mem _, ?_⟩
      rw [(AssocGraded.mk_eq_zero_iff I (zero_mem _)).mpr (zero_mem _)]
      exact zero_mem _
    | add x y _ _ hx hy =>
      obtain ⟨hx1, hx2⟩ := hx
      obtain ⟨hy1, hy2⟩ := hy
      refine ⟨add_mem hx1 hy1, ?_⟩
      rw [AssocGraded.mk_add I 1 x y hx1 hy1]
      exact add_mem hx2 hy2
    | smul c x _ hx =>
      obtain ⟨hx1, hx2⟩ := hx
      have hc : c • x ∈ I ^ 1 := by
        rw [smul_eq_mul]
        exact Ideal.mul_mem_left _ _ hx1
      refine ⟨hc, ?_⟩
      have := (AssocGraded.mkLinear I 1).map_smul c ⟨x, hx1⟩
      rw [AssocGraded.mkLinear_apply] at this
      have h2 : AssocGraded.mk I 1 (c • x) hc = c • AssocGraded.mk I 1 x hx1 := by
        simpa [AssocGraded.mkLinear_apply] using this
      rw [h2]
      exact Submodule.smul_of_tower_mem _ c hx2
  obtain ⟨hs1, hs2⟩ := hspan s hs
  have hm1 : m ∈ I ^ 1 := by
    rw [pow_one]
    exact (Ideal.pow_le_self (by norm_num)) hm
  have hmz : AssocGraded.mk I 1 m hm1 = 0 := (AssocGraded.mk_eq_zero_iff I hm1).mpr hm
  rw [AssocGraded.mk_add I 1 s m hs1 hm1, hmz, add_zero]
  exact hs2

open Classical in
/-- A regular system of `τ_{(z)}`-parameters of `R` for `(f)`, together with the system `(z)`, is
independent modulo `M²` (when `τ > 0`): `T*` has rank `τ + r` and is generated by the
`τ + r` classes of the `y_i` and the `Z_j` in `gr¹_M(R)`, which are therefore linearly independent
(Definition 10*, p. 251: "rank of `T*` minus `r`"). -/
theorem rsopIndep_sum_of_isRegularSystemOfTauZParameters {R : Type u} [CommRing R]
    [IsRegularLocalRing R] {r : ℕ} (z : Fin r → R) (hzM : ∀ j, z j ∈ maximalIdeal R)
    (hz : ExtendsToRSOP R (Finset.image z Finset.univ)) {m : ℕ} (f : Fin m → R)
    (y : Fin (tauZ R z f) → maximalIdeal R) (hy : IsRegularSystemOfTauZParameters R z f y)
    (hτ : 0 < tauZ R z f) :
    RSOPIndep (Finset.univ : Finset (Fin (tauZ R z f) ⊕ Fin r))
      (Sum.elim (fun i => (y i : R)) z) := by
  classical
  let _ : Field (R ⧸ maximalIdeal R) := Ideal.Quotient.field _
  set v : Fin (tauZ R z f) ⊕ Fin r → R := Sum.elim (fun i => (y i : R)) z with hv
  have hvM : ∀ i, v i ∈ maximalIdeal R ^ 1 := by
    rintro (i | j)
    · rw [pow_one]
      exact (y i).2
    · rw [pow_one]
      exact hzM j
  let b : Fin (tauZ R z f) ⊕ Fin r → AssocGraded (maximalIdeal R) := fun i =>
    AssocGraded.mk (maximalIdeal R) 1 (v i) (hvM i)
  have hb : b = Sum.elim (linearForms R y) (frameForm z) := by
    funext i
    rcases i with i | j
    · rfl
    · have hord1 := ordElem_maximalIdeal_eq_one_of_mem_extendsToRSOP hz
        (Finset.mem_image_of_mem z (Finset.mem_univ j))
      show _ = initialForm (maximalIdeal R) (z j)
      rw [initialForm_eq_mk _ (show Ideal.ordElem (maximalIdeal R) (z j) = ((1 : ℕ) : ℕ∞) by
        rw [hord1]; norm_cast)]
      rfl
  have hspan : Submodule.span (R ⧸ maximalIdeal R) (Set.range b) =
      tauZSubmoduleStar R z f := by
    rw [hb, Set.Sum.elim_range]
    exact hy
  have hpos : 0 < Module.finrank (R ⧸ maximalIdeal R) (tauZSubmoduleStar R z f) - r := hτ
  have hrank : Module.finrank (R ⧸ maximalIdeal R) (tauZSubmoduleStar R z f) =
      tauZ R z f + r := by
    unfold tauZ
    omega
  have hli : LinearIndependent (R ⧸ maximalIdeal R) b := by
    rw [linearIndependent_iff_card_eq_finrank_span]
    rw [Set.finrank, hspan, hrank, Fintype.card_sum, Fintype.card_fin, Fintype.card_fin]
  intro i _
  refine ⟨?_, fun h => ?_⟩
  · have := hvM i
    rwa [pow_one] at this
  · set T : Set (Fin (tauZ R z f) ⊕ Fin r) :=
      (↑(Finset.univ : Finset (Fin (tauZ R z f) ⊕ Fin r)) : Set _) \ {i} with hT
    have h1 := mk_one_mem_span_of_mem_span_sup_sq (maximalIdeal R) v hvM T (hvM i) h
    have hiT : i ∉ T := fun hi => hi.2 rfl
    exact hli.notMem_span_image hiT h1

end TauZIndependence

section Lemma24Core

open MvPolynomial

open Classical in
/-- The core of Lemma 24 (pp. 268–269) after the change of denominator `x = y_{i₀}` ("Then we may
take `y_τ` to be the element `x` in the assertion"): the denominator of `T` is `y_{i₀}` and
`ȳ_{i₀} = 1` is a unit; the hypotheses lead to a contradiction.  See
`mem_maximalIdeal_of_ordElem_eq` for the comparison with the printed proof. -/
theorem mem_maximalIdeal_of_ordElem_eq_denominator [Hironaka.HironakaCitedResults.{u}] {R : Type u} [CommRing R]
    [IsRegularLocalRing R] [IsDomain R] [PerfectField (ResidueField R)] {r : ℕ} (z : Fin r → R)
    (hzM : ∀ j, z j ∈ maximalIdeal R) (hz : ExtendsToRSOP R (Finset.image z Finset.univ))
    (f : R) (y : Fin (tauZ R z (fun _ : Fin 1 => f)) → maximalIdeal R)
    (hy : IsRegularSystemOfTauZParameters R z (fun _ : Fin 1 => f) y)
    (P : Ideal R) [P.IsPrime] (h_i : Ideal.span (Set.range z ∪ Set.range fun j => (y j : R)) ≤ P)
    [hS : IsRegularLocalRing (R ⧸ P)]
    (h_ii : Ideal.ordElem P f = Ideal.ordElem (maximalIdeal R) f)
    (T : MonoidalTransform R P)
    (ν : ℕ) (hν : (ν : ℕ∞) = Ideal.ordElem (maximalIdeal R) f)
    (fb : T.ring) (hfb : T.toRing T.x ^ ν * fb = T.toRing f)
    (zb : Fin r → T.ring) (hzb : ∀ j, T.toRing T.x * zb j = T.toRing (z j))
    (h_iii : ∀ j, zb j ∈ maximalIdeal T.ring)
    (hord : Ideal.ordElem (maximalIdeal T.ring) fb = Ideal.ordElem (maximalIdeal R) f)
    (i0 : Fin (tauZ R z (fun _ : Fin 1 => f))) (hxy : T.x = (y i0 : R)) : False := by
  classical
  -- the field `k = R/M`
  let _ : Field (R ⧸ maximalIdeal R) := Ideal.Quotient.field _
  have : PerfectField (R ⧸ maximalIdeal R) := ‹PerfectField (ResidueField R)›
  have hP0 : P ≠ ⊥ := fun h => T.x_ne_zero (Ideal.mem_bot.mp (h ▸ T.x_mem))
  obtain ⟨hregT, -, -⟩ := MonoidalTransform.isRegularLocalRing_and_isLocalHom_and_span_xR_eq_map
    T ‹P.IsPrime› hP0 hS
  have := hregT
  have hx0R : T.toRing T.x ≠ 0 := fun h => T.x_ne_zero (MonoidalTransform.toRing_injective T
    (h.trans (map_zero _).symm))
  -- Step 2 (p. 268): "We then have a minimal base of `P` of the form
  -- `(z₁, …, z_r, y₁, …, y_{τ−1}, x, x₁, …, x_s)`" with `x = y_{i₀}`
  have hτ : 0 < tauZ R z (fun _ : Fin 1 => f) := Fin.pos i0
  have hind := rsopIndep_sum_of_isRegularSystemOfTauZParameters z hzM hz _ y hy hτ
  obtain ⟨hvinj, hvext⟩ := hind.injOn_and_extends
  have hvP : ∀ i, Sum.elim (fun i => (y i : R)) z i ∈ P := by
    rintro (i | j)
    · exact h_i (Ideal.subset_span (Or.inr ⟨i, rfl⟩))
    · exact h_i (Ideal.subset_span (Or.inl ⟨j, rfl⟩))
  have hxW : T.x ∈ Finset.univ.image (Sum.elim (fun i => (y i : R)) z) := by
    rw [hxy]
    exact Finset.mem_image.mpr ⟨Sum.inl i0, Finset.mem_univ _, rfl⟩
  obtain ⟨S, n, z', hSM, hScard, hinj, hzS, hz0, hzP, hzW⟩ := exists_minimalBase_first P hS
    (Finset.univ.image (Sum.elim (fun i => (y i : R)) z))
    (fun w hw => by
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hw
      exact hvP i) hvext hxW
  have hiz : ∀ j, ∃ i : Fin n, z' i.succ = z j := by
    intro j
    refine hzW (z j) (Finset.mem_image.mpr ⟨Sum.inr j, Finset.mem_univ _, rfl⟩) ?_
    intro h
    have := hvinj (Finset.mem_coe.mpr (Finset.mem_univ (Sum.inr j)))
      (Finset.mem_coe.mpr (Finset.mem_univ (Sum.inl i0))) (by simp [h, hxy])
    exact absurd this (by simp)
  choose iz hiz using hiz
  have hPM : P ≤ maximalIdeal R := IsLocalRing.le_maximalIdeal (Ideal.IsPrime.ne_top ‹_›)
  -- the isomorphism `k[X_w] ≅ gr_M(R)` of the regular system of parameters `S`
  let w : Fin S.card → R := fun i => (S.equivFin.symm i : R)
  have hwinj : Function.Injective w := Subtype.val_injective.comp S.equivFin.symm.injective
  have hwS : ∀ i, w i ∈ S := fun i => (S.equivFin.symm i).2
  have hwrange : Set.range w = (S : Set R) := by
    ext v
    constructor
    · rintro ⟨i, rfl⟩
      exact hwS i
    · intro hv
      exact ⟨S.equivFin ⟨v, hv⟩, by simp [w]⟩
  have hwspan : Ideal.span (Set.range w) = maximalIdeal R := by rw [hwrange, hSM]
  have hw1 : ∀ i, w i ∈ maximalIdeal R ^ 1 := fun i => by
    rw [pow_one, ← hwspan]
    exact Ideal.subset_span ⟨i, rfl⟩
  let Γ := assocGradedAlgEquiv hSM hScard hwinj hwS hwspan hw1
  let σ : Fin (n + 1) → Fin S.card := fun j => S.equivFin ⟨z' j, hzS j⟩
  have hσ : ∀ j, w (σ j) = z' j := fun j => by simp [w, σ]
  have hσinj : Function.Injective σ := fun a b hab => hinj (by rw [← hσ a, ← hσ b, hab])
  have hz'1 : ∀ j, z' j ∈ maximalIdeal R ^ 1 := fun j => by
    rw [pow_one]
    exact hPM (hzP ▸ Ideal.subset_span ⟨j, rfl⟩)
  let Γ' : MvPolynomial (Fin (n + 1)) (R ⧸ maximalIdeal R) →ₐ[R ⧸ maximalIdeal R]
      AssocGraded (maximalIdeal R) :=
    aeval fun j => AssocGraded.mk (maximalIdeal R) 1 (z' j) (hz'1 j)
  have hΓ' : ∀ p, Γ' p = Γ (rename σ p) := by
    intro p
    rw [assocGradedAlgEquiv_apply, aeval_rename]
    refine congrArg (fun g => aeval g p) (funext fun j => ?_)
    simp only [Function.comp, hσ]
  have hΓ'inj : Function.Injective Γ' := by
    intro p q h
    rw [hΓ', hΓ'] at h
    exact rename_injective σ hσinj (Γ.injective h)
  -- the values at `z'` of forms
  have hgr : ∀ {K : MvPolynomial (Fin (n + 1)) R} {d : ℕ} (hK : K.IsHomogeneous d),
      Γ' (map (Ideal.Quotient.mk (maximalIdeal R)) K) = AssocGraded.mk (maximalIdeal R) d
        (eval z' K) (eval_mem_pow_of_isHomogeneous _ z' hz'1 hK) := fun hK =>
    aeval_mk_map_of_isHomogeneous (maximalIdeal R) z' hz'1 hK
  have mk_congr : ∀ {a b : R} (h : a = b) {d : ℕ} (ha : a ∈ maximalIdeal R ^ d)
      (hb : b ∈ maximalIdeal R ^ d),
      AssocGraded.mk (maximalIdeal R) d a ha = AssocGraded.mk (maximalIdeal R) d b hb := by
    rintro a b rfl d ha hb
    rfl
  have hPexp : ∀ g ∈ P, ∃ H : MvPolynomial (Fin (n + 1)) R, H.IsHomogeneous 1 ∧ eval z' H = g := by
    intro g hg
    have : g ∈ Ideal.span (Set.range z') ^ 1 := by rw [hzP, pow_one]; exact hg
    exact (Ideal.mem_span_pow_iff_exists_isHomogeneous z' g).mp this
  -- `f ∈ Pᵛ`: `f = K_f(z')` with a form `K_f` of degree `ν`
  have hfn : f ∈ P ^ ν := Ideal.mem_pow_of_le_ordElem (le_of_eq (hν.trans h_ii.symm))
  obtain ⟨Kf, hKf, hKfe⟩ := (Ideal.mem_span_pow_iff_exists_isHomogeneous z' f).mp
    (by rw [hzP]; exact hfn)
  have hν' : Ideal.ordElem (maximalIdeal R) f = (ν : ℕ∞) := hν.symm
  -- the form `F` of the initial form `φ` of `f`, in `k[X₀, …, X_n]`
  let F : MvPolynomial (Fin (n + 1)) (R ⧸ maximalIdeal R) :=
    map (Ideal.Quotient.mk (maximalIdeal R)) Kf
  have hFhom : F ∈ homogeneousSubmodule (Fin (n + 1)) (R ⧸ maximalIdeal R) ν :=
    (hKf.map _)
  have hφ : initialForm (maximalIdeal R) f = Γ' F := by
    rw [hgr hKf, initialForm_eq_mk _ hν']
    exact mk_congr hKfe.symm _ _
  -- `LF = T_F`, the module of Lemma 23, has the defining property of `T`
  have hbot : ν = 0 → linearFormModule (R ⧸ maximalIdeal R) F ≤ ⊥ ∧
      F ∈ Algebra.adjoin (R ⧸ maximalIdeal R) ((⊥ : Submodule (R ⧸ maximalIdeal R)
        (MvPolynomial (Fin (n + 1)) (R ⧸ maximalIdeal R))) : Set (MvPolynomial (Fin (n + 1))
          (R ⧸ maximalIdeal R))) := by
    intro h0
    have hF0 := hFhom
    rw [h0, homogeneousSubmodule_zero] at hF0
    obtain ⟨c, hc⟩ := Submodule.mem_one.mp hF0
    have hFad : F ∈ Algebra.adjoin (R ⧸ maximalIdeal R) ((⊥ : Submodule (R ⧸ maximalIdeal R)
        (MvPolynomial (Fin (n + 1)) (R ⧸ maximalIdeal R))) : Set (MvPolynomial (Fin (n + 1))
          (R ⧸ maximalIdeal R))) := by
      rw [← hc]
      exact Subalgebra.algebraMap_mem _ c
    exact ⟨sInf_le ⟨bot_le, hFad⟩, hFad⟩
  have hLF : linearFormModule (R ⧸ maximalIdeal R) F ≤
      homogeneousSubmodule (Fin (n + 1)) (R ⧸ maximalIdeal R) 1 ∧
      F ∈ Algebra.adjoin (R ⧸ maximalIdeal R)
        (linearFormModule (R ⧸ maximalIdeal R) F : Set (MvPolynomial (Fin (n + 1))
          (R ⧸ maximalIdeal R))) := by
    rcases Nat.eq_zero_or_pos ν with h0 | hpos
    · obtain ⟨h1, h2⟩ := hbot h0
      refine ⟨h1.trans bot_le, ?_⟩
      exact Algebra.adjoin_mono (SetLike.coe_subset_coe.mpr bot_le) h2
    · exact linearFormModule_spec hpos hFhom
  -- the smallest module `T` of `gr¹_M(R)` is contained in the image of `LF`
  have hTmin : tauZSubmodule R (fun _ : Fin 1 => f) ≤
      (linearFormModule (R ⧸ maximalIdeal R) F).map Γ'.toLinearMap := by
    refine sInf_le ⟨?_, ?_⟩
    · refine (Submodule.map_mono hLF.1).trans ?_
      rw [homogeneousSubmodule_one_eq_span_X, Submodule.map_span, Submodule.span_le]
      rintro _ ⟨_, ⟨j, rfl⟩, rfl⟩
      have : Γ'.toLinearMap (X j) = AssocGraded.mk (maximalIdeal R) 1 (z' j) (hz'1 j) := by
        simp [Γ']
      rw [SetLike.mem_coe, this]
      exact AssocGraded.mk_mem_homogeneous (maximalIdeal R) (hz'1 j)
    · refine le_antisymm (Ideal.span_le.mpr fun x hx => hx.1) (Ideal.span_le.mpr ?_)
      rintro _ ⟨j, rfl⟩
      refine Ideal.subset_span ⟨Ideal.subset_span ⟨j, rfl⟩, ?_⟩
      have hcoe : (((linearFormModule (R ⧸ maximalIdeal R) F).map Γ'.toLinearMap :
          Submodule (R ⧸ maximalIdeal R) (AssocGraded (maximalIdeal R))) :
            Set (AssocGraded (maximalIdeal R))) =
          Γ' '' (linearFormModule (R ⧸ maximalIdeal R) F : Set _) := by
        ext a
        simp
      rw [hcoe, SetLike.mem_coe, ← AlgHom.map_adjoin]
      beta_reduce
      rw [hφ]
      exact Subalgebra.mem_map.mpr ⟨F, hLF.2, rfl⟩
  -- the chart `R₁ → (R/M)[T₁, …, T_n]_N`
  obtain ⟨N, hN, Ψ, hΨloc, hΨc, hΨu⟩ :=
    MonoidalTransform.exists_chart_hom T hS hSM hScard hinj hzS hz0 hzP
  have hu : ∀ i : Fin n, ∃ u : T.ring, T.toRing T.x * u = T.toRing (z' i.succ) := by
    intro i
    have hmem : T.toRing (z' i.succ) ∈ Ideal.span {T.toRing T.x} := by
      rw [show Ideal.span {T.toRing T.x} = P.map T.toRing from T.span_xR_eq_map]
      exact Ideal.mem_map_of_mem _ (hzP ▸ Ideal.subset_span ⟨i.succ, rfl⟩)
    obtain ⟨u, hu⟩ := Ideal.mem_span_singleton'.mp hmem
    exact ⟨u, by rw [mul_comm]; exact hu⟩
  choose u hu using hu
  have hev : ∀ {K : MvPolynomial (Fin (n + 1)) R} {d : ℕ} (_ : K.IsHomogeneous d) {v : T.ring},
      T.toRing T.x ^ d * v = T.toRing (eval z' K) →
      Ψ v = algebraMap (MvPolynomial (Fin n) (R ⧸ maximalIdeal R)) (Localization.AtPrime N)
        (dehomogenize (R ⧸ maximalIdeal R) n (map (Ideal.Quotient.mk (maximalIdeal R)) K)) := by
    intro K d hK v hv
    have h1 := MonoidalTransform.chart_apply_eq_eval₂
      (A := MvPolynomial (Fin n) (R ⧸ maximalIdeal R))
      (B := Localization.AtPrime N) T hz0 Ψ ((MvPolynomial.C : (R ⧸ maximalIdeal R) →+*
        MvPolynomial (Fin n) (R ⧸ maximalIdeal R)).comp (Ideal.Quotient.mk (maximalIdeal R)))
      (algebraMap (MvPolynomial (Fin n) (R ⧸ maximalIdeal R)) (Localization.AtPrime N))
      MvPolynomial.X u hu hΨc (hΨu u hu) hK hv
    refine h1.trans ?_
    congr 1
    rw [dehomogenize, MvPolynomial.aeval_def, MvPolynomial.eval₂_map]
    rfl
  have hfchart : Ψ fb = algebraMap (MvPolynomial (Fin n) (R ⧸ maximalIdeal R))
      (Localization.AtPrime N) (dehomogenize (R ⧸ maximalIdeal R) n F) :=
    hev hKf (by rw [hfb, hKfe])
  -- `Ψ` is local
  have hΨmax : ∀ v ∈ maximalIdeal T.ring, Ψ v ∈ maximalIdeal (Localization.AtPrime N) := by
    intro v hv
    by_contra hnot
    exact hv (isUnit_of_map_unit Ψ v (IsLocalRing.notMem_maximalIdeal.mp hnot))
  -- (iii): `z̄_j = z'_{iz j}/x` is the variable `T_{iz j}`, which therefore lies in `N`
  have hzN : ∀ j, (MvPolynomial.X (iz j) : MvPolynomial (Fin n) (R ⧸ maximalIdeal R)) ∈ N := by
    intro j
    have hzu : zb j = u (iz j) := by
      refine mul_left_cancel₀ hx0R ?_
      rw [hzb j, hu (iz j), hiz j]
    have h1 := hΨmax _ (h_iii j)
    rw [hzu, hΨu u hu (iz j)] at h1
    exact (IsLocalization.AtPrime.to_map_mem_maximal_iff (Localization.AtPrime N) N _).mp h1
  -- `ν_{M₁}(f̄) = ν` gives the order condition of Lemma 23 for the image of `F`
  have hfN : (ν : ℕ∞) ≤ Ideal.ordElem (N.map (algebraMap (MvPolynomial (Fin n)
      (R ⧸ maximalIdeal R)) (Localization.AtPrime N)))
      (algebraMap (MvPolynomial (Fin n) (R ⧸ maximalIdeal R)) (Localization.AtPrime N)
        (dehomogenize (R ⧸ maximalIdeal R) n F)) := by
    have h1 : fb ∈ maximalIdeal T.ring ^ ν := Ideal.mem_pow_of_ordElem (hord.trans hν')
    have h2 : Ψ fb ∈ maximalIdeal (Localization.AtPrime N) ^ ν := by
      have hle : (maximalIdeal T.ring).map Ψ ≤ maximalIdeal (Localization.AtPrime N) :=
        Ideal.map_le_iff_le_comap.mpr hΨmax
      have := Ideal.pow_right_mono hle ν
      rw [← Ideal.map_pow] at this
      exact this (Ideal.mem_map_of_mem Ψ h1)
    rw [hfchart] at h2
    rw [Localization.AtPrime.map_eq_maximalIdeal]
    exact Ideal.le_ordElem h2
  -- Lemma 23
  have hL23 : ∀ a ∈ linearFormModule (R ⧸ maximalIdeal R) F,
      dehomogenize (R ⧸ maximalIdeal R) n a ∈ N := by
    intro a ha
    rcases Nat.eq_zero_or_pos ν with h0 | hpos
    · have : a = 0 := by
        have := ((hbot h0).1 ha)
        exact (Submodule.mem_bot _).mp this
      rw [this, map_zero]
      exact N.zero_mem
    · exact span_dehomogenize_le_of_ordElem_ge (R ⧸ maximalIdeal R) n ν hpos F hFhom N hfN
        (Ideal.subset_span ⟨a, ha, rfl⟩)
  -- `Y = a + ∑ c_j Z_j` with `a ∈ T`, where `Y` is the class of `x = y_{i₀}`
  have hYmem : linearForms R y i0 ∈ tauZSubmoduleStar R z (fun _ : Fin 1 => f) := by
    rw [← hy]
    exact Submodule.subset_span (Or.inl ⟨i0, rfl⟩)
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp hYmem
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun (R ⧸ maximalIdeal R)).mp hb
  obtain ⟨a', ha', rfl⟩ := Submodule.mem_map.mp (hTmin ha)
  have hY : linearForms R y i0 = Γ' (MvPolynomial.X 0) := by
    show AssocGraded.mk (maximalIdeal R) 1 (y i0 : R) _ = _
    simp only [Γ', aeval_X]
    exact mk_congr (by rw [hz0, hxy]) _ _
  have hZ : ∀ j, frameForm z j = Γ' (MvPolynomial.X (iz j).succ) := by
    intro j
    have hord1 := ordElem_maximalIdeal_eq_one_of_mem_extendsToRSOP hz
      (Finset.mem_image_of_mem z (Finset.mem_univ j))
    rw [frameForm, initialForm_eq_mk _ (show Ideal.ordElem (maximalIdeal R) (z j) =
      ((1 : ℕ) : ℕ∞) by rw [hord1]; norm_cast)]
    simp only [Γ', aeval_X]
    exact mk_congr (hiz j).symm _ _
  have hrel : Γ' (MvPolynomial.X 0) =
      Γ' (a' + ∑ j, c j • (MvPolynomial.X (iz j).succ :
        MvPolynomial (Fin (n + 1)) (R ⧸ maximalIdeal R))) := by
    rw [← hY, map_add, map_sum, ← hab, ← hc]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_smul, hZ j]
  have hrel' := hΓ'inj hrel
  -- dehomogenizing: `1 = X₀/X₀ ∈ N`, which is absurd
  have h3 : (1 : MvPolynomial (Fin n) (R ⧸ maximalIdeal R)) ∈ N := by
    have h4 := congrArg (dehomogenize (R ⧸ maximalIdeal R) n) hrel'
    rw [map_add, map_sum] at h4
    have h0 : dehomogenize (R ⧸ maximalIdeal R) n (MvPolynomial.X 0) = 1 := by
      simp [dehomogenize]
    rw [h0] at h4
    rw [h4]
    refine N.add_mem (hL23 a' ha') (N.sum_mem fun j _ => ?_)
    rw [map_smul]
    have h5 : dehomogenize (R ⧸ maximalIdeal R) n (MvPolynomial.X (iz j).succ) =
        MvPolynomial.X (iz j) := by
      simp [dehomogenize]
    rw [h5]
    exact Submodule.smul_of_tower_mem N (c j) (hzN j)
  exact hN.ne_top ((Ideal.eq_top_iff_one N).mpr h3)

end Lemma24Core

section Lemma24

variable {R : Type u} [CommRing R] [IsRegularLocalRing R] [IsDomain R]

open Classical in
/-- Lemma 24, p. 268: "Let `R` be a regular local ring, `M` the maximal ideal of `R` and
`(z₁, …, z_r)` a system of elements of `M` which can be extended to a regular system of parameters
of `R`. Let `f` be an element of `R`, and `(y₁, …, y_τ)` a regular system of `τ_{(z)}`-parameters of
`R` for `f`, where `τ = τ_{(z)}(f)`. Let `P` be a prime ideal in `R` such that (i)
`P ⊇ (z₁, …, z_r, y₁, …, y_τ)R`, (ii) `R/P` is regular and `ν_P(f) = ν_M(f)`. We assume that the
residue field `R/M` of `R` is perfect. Let `R₁` be a monoidal transform of `R` with center `P`, and
`M₁` the maximal ideal of `R₁`. Let `x ∈ P` such that `(x)R₁ = PR₁`. Let `ν = ν_M(f)`,
`f̄ = fx^{−ν}`, `z̄_j = z_jx^{−1}` (`1 ≤ j ≤ r`) and `ȳ_j = y_jx^{−1}` (`1 ≤ j ≤ τ`). We assume that
(iii) `z̄_j ∈ M₁` for all `j` (`1 ≤ j ≤ r`). If `ν_{M₁}(f̄) = ν_M(f)`, then we have `ȳ_i ∈ M₁` for
all `i` (`1 ≤ i ≤ τ`)."

(Formalization notes: `ν = ν_M(f)` is carried by a natural number `ν` with `ν = ν_M(f)` (so
`f ≠ 0`); the quotients `fx^{−ν}`, `z_jx^{−1}`, `y_jx^{−1}` are elements of `R₁` satisfying
`x^ν f̄ = f`, `x z̄_j = z_j`, `x ȳ_j = y_j` (unique, `R₁` being a domain); `τ_{(z)}(f)` and its
regular systems of parameters are those of the one-element system `(f)` (Definition 10*).)

Following the printed proof (pp. 268–269), whose unjustified steps are filled as follows (each
"gap filled" quotes the paper).  The printed proof argues by contradiction: suppose `ȳ_i` is a
unit of `R₁` for some `i`.
(1) Gap filled: "Then we may take `y_τ` to be the element `x` in the assertion."  Since `ȳ_τ` is a
unit, `(y_τ)R₁ = (x)R₁ = PR₁` and `f̄`, `z̄_j` change by a unit factor, which changes neither
`ν_{M₁}(f̄)` nor the membership in `M₁`; in Lean a monoidal transform records its denominator, so
`R₁` is re-presented as `R[y_τ⁻¹P]_{M''}` (`MonoidalTransform.exists_equiv_of_denominator`).
(2) Gap filled: "We then have a minimal base of `P` of the form
`(z₁, …, z_r, y₁, …, y_{τ−1}, x, x₁, …, x_s)`."  The classes of `(z, y)` are linearly independent in
`M/M²` (`T*` has rank `τ + r` and is generated by `τ + r` classes:
`rsopIndep_sum_of_isRegularSystemOfTauZParameters`), they lie in `P` by (i), and `R/P` is regular,
so they are part of a minimal base of `P` which is part of a regular system of parameters of `R`
(`exists_minimalBase_first`, by the exchange step `ExtendsToRSOP.exchange`).
(3) Gap filled: "We can identify `A/MA` with the following polynomial ring of `r + τ + s − 1`
indeterminates over the residue field `k` of `R`" (with "`A = R[z̄₁, …, x̄_s]`, `R₁ = A_N`,
`N ⊇ MA`, `NA_N = M₁`").  The identification of p. 268 is obtained from the description of
monoidal transforms on pp. 209–210 (localized at `N̄`): Lean uses
`R₁/xR₁ ≅ (R/P)[T₁, …, T_n]_q` (`MonoidalTransform.exists_quotient_equiv_localization`,
`T_k ↔ b_k/x` for the base `b` of (2)) and its reduction modulo `M`: a local homomorphism
`Ψ : R₁ → k[T]_N` with `Ψ(z̄_j) = Z̄_j` (`MonoidalTransform.exists_chart_hom`).
(4) Gap filled: "the image of `f̄` in `A/MA` is equal to `φ(Z̄₁, …, 1, …)`" ("From this, it
follows").  By (ii), `f ∈ Pᵛ`, so `f = K(z')` for a form `K` of degree `ν` in the base `z'`, and
`Ψ(f̄) = F(1, T)` with `F = K mod M` (`MonoidalTransform.chart_apply_eq_eval₂`); `F` represents
`φ` in `gr_M(R) ≅ k[Z, X, Y, …]`, which is the paper's "the canonical homomorphism of `gr_P(R)` into
`gr_M(R)` maps `Φ` to `φ`".  (The remark that `φ` involves only `Z`, `X`, `Y_{<τ}` is not needed.)
(5) Gap filled: "the assumption that `ν_{M₁}(f̄) = ν_M(f)` should imply that
`ν_{N̄Ā_N̄}(F̄) ≥ ν`": `f̄ ∈ M₁ᵛ` and `Ψ` is local.
(6) Lemma 23 is used as stated, in the `n + 1` variables of the minimal base (`φ` need not
involve all of them, so no extension of Lemma 23 to further indeterminates is needed).  Gap filled:
the module `T` of Definition 10* is contained in the image of the module `T_F` of Lemma 23, which
requires that `T_F` itself has the defining property (`linearFormModule_spec`, by Lemma 10 of §4);
the paper identifies them tacitly ("if `T` is the smallest `k`-submodule ... then we have `W/X ∈ N̄`
for all `W ∈ T`").  Then "(iii) shows that `N̄` contains all the `Z̄_i`.  Since `X` is contained in
the module generated by `T` and the `Z_i`" (`y_τ ∈ T*`, `T* = T + (Z)`), "`1 = X/X ∈ N̄`, which is
absurd".
(7) The hypothesis `x ∈ P` is not used: `y_τ ∈ P` is part of (i), and `x` enters only through
`(x)R₁ = PR₁`.  The hypothesis `z_j ∈ M` is used for the independence modulo `M²` in (2). -/
@[blueprint "lem:III.24"
  (statement := /-- Let $R$ be a regular local ring, $M$ the maximal ideal of $R$ and
    $(z_1,\dots,z_r)$ a system of elements of $M$ which can be extended to a regular system of
    parameters of $R$. Let $f$ be an element of $R$, and $(y_1,\dots,y_\tau)$ a regular system of
    $\tau_{(z)}$-parameters of $R$ for $f$, where $\tau=\tau_{(z)}(f)$ (\cref{def:III.10-star}).
    Let $P$ be a prime ideal in $R$ such that (i) $P\supseteq(z_1,\dots,z_r,y_1,\dots,y_\tau)R$,
    (ii) $R/P$ is regular and $\nu_P(f)=\nu_M(f)$. We assume that the residue field $R/M$ of $R$
    is perfect. Let $R_1$ be a monoidal transform of $R$ with center $P$
    (\cref{def:III.2-monoidal-transform}), and $M_1$ the maximal ideal of $R_1$. Let $x\in P$
    such that $(x)R_1=PR_1$. Let $\nu=\nu_M(f)$, $\bar f=fx^{-\nu}$, $\bar z_j=z_jx^{-1}$
    ($1\le j\le r$) and $\bar y_j=y_jx^{-1}$ ($1\le j\le\tau$). We assume that (iii)
    $\bar z_j\in M_1$ for all $j$ ($1\le j\le r$). If $\nu_{M_1}(\bar f)=\nu_M(f)$, then we have
    $\bar y_i\in M_1$ for all $i$ ($1\le i\le\tau$). (Lemma 24, p.~268.)

    (Formalization note: $\nu$ is taken finite; the quotients by powers of $x$ are the elements
    $\bar f,\bar z_j,\bar y_j$ of $R_1$ with $x^\nu\bar f=f$, $x\bar z_j=z_j$, $x\bar y_j=y_j$.) -/)
  (proof := /-- Suppose we have an index $i$ such that $y_ix^{-1}$ is a unit in $R_1$, say
    $i=\tau$. Then we may take $y_\tau$ to be the element $x$ in the assertion. We then have a
    minimal base of $P$ of the form $(z_1,\dots,z_r,y_1,\dots,y_{\tau-1},x,x_1,\dots,x_s)$. Let
    $\bar z_j$ and $\bar y_i$ be the same as in the assertion, and $\bar x_k=x_kx^{-1}$ for
    $1\le k\le s$. Let $A=R[\bar z_1,\dots,\bar z_r,\bar y_1,\dots,\bar y_\tau,\bar x_1,\dots,
    \bar x_s]$. We have a prime ideal $N$ in $A$ such that $R_1=A_N$. Then we have
    $N\supseteq MA$ and $NA_N=M_1$. We can identify $A/MA$ with the following polynomial ring of
    $(r+\tau+s-1)$ indeterminates over the residue field $k$ of $R$:
    $$k[\bar Z_1,\dots,\bar Z_r,\bar Y_1,\dots,\bar Y_{\tau-1},\bar X_1,\dots,\bar X_s],$$
    where $\bar Z_i$ (resp.\ $\bar Y_j$, resp.\ $\bar X_k$) denotes the image of $\bar z_i$
    (resp.\ $\bar y_j$, resp.\ $\bar x_k$) in $A/MA$. Let $Z_i$ (resp.\ $Y_j$, resp.\ $X_k$) be
    the initial form of $z_i$ (resp.\ $y_j$, resp.\ $x_k$) in $\operatorname{gr}_M(R)$. Let $X$
    be also the same of $x$ in $\operatorname{gr}_M(R)$. By the choice of
    $(y_1,\dots,y_\tau=x)$, if $\varphi$ denotes the initial form of $f$ in
    $\operatorname{gr}_M(R)$, then $\varphi$ is a form of degree $\nu$ only in
    $Z_1,\dots,Z_r,X,Y_1,\dots,Y_{\tau-1}$. Moreover, by (ii), if $\Phi$ denotes the initial form
    of $f$ in $\operatorname{gr}_P(R)$, then the canonical homomorphism of
    $\operatorname{gr}_P(R)$ into $\operatorname{gr}_M(R)$ maps $\Phi$ to $\varphi$. From this, it
    follows that the image of $\bar f$ in $A/MA$ is equal to
    $$\varphi(\bar Z_1,\dots,\bar Z_r,1,\bar Y_1,\dots,\bar Y_{\tau-1}),$$
    i.e., it is obtained by replacing $Z_i/X$ by $\bar Z_i$ and $Y_j/X$ by $\bar Y_j$ in the
    quotient $\varphi/X^\nu$. ($\varphi$ is viewed as a form in
    $Z_1,\dots,Z_r,X,Y_1,\dots,Y_r$ [sic; read $Y_{\tau-1}$] with coefficients in $k$.) Now, the
    assumption that $\nu_{M_1}(\bar f)=\nu_M(f)$ should imply that
    $\nu_{\bar N\bar A_{\bar N}}(\bar F)\ge\nu$ where $\bar A=A/MA$, $\bar N=N/MA$ and $\bar F$
    the image of $\bar f$ in $\bar A$. In view of Lemma~23 (\cref{lem:III.23}), if $T$ is the
    smallest $k$-submodule of $\operatorname{gr}^1_M(R)$ such that $\varphi\in k[T]$, which is
    contained in the module generated by $Z_1,\dots,Z_r,X,Y_1,\dots,Y_{\tau-1}$, then we have
    $W/X\in\bar N$ for all $W\in T$ in the sense of the above identifications among
    indeterminates. On the other hand, (iii) shows that $\bar N$ contains all the $\bar Z_i$.
    Since $X$ is contained in the module generated by $T$ and the $Z_i$, we should have
    $1=X/X\in\bar N$, which is absurd. \qed

    \textbf{Gap fills} (the paper's words are quoted). (1) ``Then we may take $y_\tau$ to be the
    element $x$ in the assertion'': since $\bar y_\tau$ is a unit, $(y_\tau)R_1=(x)R_1=PR_1$ and
    $\bar f,\bar z_j$ change by a unit factor, which changes neither $\nu_{M_1}(\bar f)$ nor the
    membership in $M_1$. (2) ``We then have a minimal base of $P$ of the form
    $(z_1,\dots,z_r,y_1,\dots,y_{\tau-1},x,x_1,\dots,x_s)$'': the classes of $(z,y)$ are linearly
    independent in $M/M^2$ ($T^*$ has rank $\tau+r$ and is generated by $\tau+r$ classes), they lie
    in $P$ by (i) and $R/P$ is regular, so they are part of a minimal base of $P$, which is part of
    a regular system of parameters of $R$. (3) ``We can identify $A/MA$ with the following
    polynomial ring'': the identification of p.~268 is obtained from the description of monoidal
    transforms on pp.~209--210 (localized at $\bar N$); the formalization uses
    $R_1/xR_1\cong(R/P)[T_1,\dots,T_n]_{\mathfrak q}$, $T_k\leftrightarrow b_k/x$ for the base $b$
    of (2), and its reduction modulo $M$, a local homomorphism
    $\Psi\colon R_1\to k[T]_{N}$ with $\Psi(\bar z_j)=\bar Z_j$. (4)
    ``the image of $\bar f$ in $A/MA$ is equal to $\varphi(\bar Z_1,\dots,1,\dots)$'' (``From this,
    it follows''): by (ii), $f\in P^\nu$, so $f=K(x,t_1,\dots,t_n)$ for a form $K$ of degree $\nu$,
    and $\Psi(\bar f)=F(1,T)$ with $F=K\bmod M$, which represents $\varphi$ in
    $\operatorname{gr}_M(R)$ (this is ``the canonical homomorphism of $\operatorname{gr}_P(R)$ into
    $\operatorname{gr}_M(R)$ maps $\Phi$ to $\varphi$''). (5) ``the assumption that
    $\nu_{M_1}(\bar f)=\nu_M(f)$ should imply that $\nu_{\bar N\bar A_{\bar N}}(\bar F)\ge\nu$'':
    $\bar f\in M_1^\nu$ and $\Psi$ is local. (6) Lemma~23 is used as stated, in the $n+1$
    variables of the minimal base ($\varphi$ need not involve all of them). The module $T$ of
    Definition~10* is contained in the image of the module $T_F$ of Lemma~23, because $T_F$ itself
    has the defining property (Lemma~10, \S4); the paper identifies them tacitly. The conclusion
    $1=X/X\in\bar N$ is then as printed. (7) The hypothesis $x\in P$ is not used ($y_\tau\in P$
    is part of (i), and $x$ enters only through $(x)R_1=PR_1$). -/)
  (latexEnv := "lemma")]
theorem mem_maximalIdeal_of_ordElem_eq [Hironaka.HironakaCitedResults.{u}] [PerfectField (ResidueField R)] {r : ℕ} (z : Fin r → R)
    (hzM : ∀ j, z j ∈ maximalIdeal R) (hz : ExtendsToRSOP R (Finset.image z Finset.univ))
    (f : R) (y : Fin (tauZ R z (fun _ : Fin 1 => f)) → maximalIdeal R)
    (hy : IsRegularSystemOfTauZParameters R z (fun _ : Fin 1 => f) y)
    (P : Ideal R) [P.IsPrime]
    (h_i : Ideal.span (Set.range z ∪ Set.range fun j => (y j : R)) ≤ P)
    [IsRegularLocalRing (R ⧸ P)]
    (h_ii : Ideal.ordElem P f = Ideal.ordElem (maximalIdeal R) f)
    (T : MonoidalTransform R P) (x : R) (hxP : x ∈ P)
    (hx : Ideal.span {T.toRing x} = P.map T.toRing)
    (ν : ℕ) (hν : (ν : ℕ∞) = Ideal.ordElem (maximalIdeal R) f)
    (fb : T.ring) (hfb : T.toRing x ^ ν * fb = T.toRing f)
    (zb : Fin r → T.ring) (hzb : ∀ j, T.toRing x * zb j = T.toRing (z j))
    (yb : Fin (tauZ R z (fun _ : Fin 1 => f)) → T.ring)
    (hyb : ∀ j, T.toRing x * yb j = T.toRing (y j))
    (h_iii : ∀ j, zb j ∈ maximalIdeal T.ring) :
    Ideal.ordElem (maximalIdeal T.ring) fb = Ideal.ordElem (maximalIdeal R) f →
      ∀ i, yb i ∈ maximalIdeal T.ring := by
  intro hord i0
  by_contra hi0
  have hyu : IsUnit (yb i0) := IsLocalRing.notMem_maximalIdeal.mp hi0
  -- (the hypothesis `x ∈ P` is not needed: `x` enters only through `(x)R₁ = PR₁`)
  have _ := hxP
  have hP0 : P ≠ ⊥ := fun h => T.x_ne_zero (Ideal.mem_bot.mp (h ▸ T.x_mem))
  obtain ⟨hregT, -, -⟩ := MonoidalTransform.isRegularLocalRing_and_isLocalHom_and_span_xR_eq_map
    T ‹P.IsPrime› hP0 ‹IsRegularLocalRing (R ⧸ P)›
  have := hregT
  -- Step 1 (p. 268): "Then we may take `y_τ` to be the element `x` in the assertion":
  -- `(y_{i₀})R₁ = (x)R₁ = PR₁`, since `ȳ_{i₀}` is a unit
  have hy0 : (y i0 : R) ∈ P := h_i (Ideal.subset_span (Or.inr ⟨i0, rfl⟩))
  have hxne : T.toRing x ≠ 0 := by
    intro h0
    have : T.toRing T.x ∈ Ideal.span {T.toRing x} := by
      rw [hx]
      exact Ideal.mem_map_of_mem _ T.x_mem
    rw [h0, Ideal.span_singleton_eq_bot.mpr rfl, Ideal.mem_bot] at this
    exact T.x_ne_zero (MonoidalTransform.toRing_injective T (this.trans (map_zero _).symm))
  have hy0ne : (y i0 : R) ≠ 0 := by
    intro h0
    have := hyb i0
    rw [h0, map_zero] at this
    exact hxne ((mul_eq_zero.mp this).resolve_right hyu.ne_zero)
  have hxy : Ideal.span {T.toRing (y i0 : R)} = P.map T.toRing := by
    rw [← hyb i0, Ideal.span_singleton_mul_right_unit hyu, hx]
  obtain ⟨T', σ, hT'x, hσ⟩ := T.exists_equiv_of_denominator hy0 hy0ne hxy
  obtain ⟨hregT', -, -⟩ := MonoidalTransform.isRegularLocalRing_and_isLocalHom_and_span_xR_eq_map
    T' ‹P.IsPrime› hP0 ‹IsRegularLocalRing (R ⧸ P)›
  have := hregT'
  -- the elements `f̄`, `z̄_j` of `R₁` for the denominator `y_{i₀}`, transported to `T'`
  have hxv : T.toRing x = T.toRing (y i0 : R) * ↑hyu.unit⁻¹ := by
    rw [← hyb i0, mul_assoc]
    have : (yb i0) * ↑hyu.unit⁻¹ = 1 := by
      have := hyu.unit.mul_inv
      rwa [hyu.unit_spec] at this
    rw [this, mul_one]
  have hσx : σ (T.toRing (y i0 : R)) = T'.toRing T'.x := by
    rw [hσ, hT'x]
  refine mem_maximalIdeal_of_ordElem_eq_denominator z hzM hz f y hy P h_i h_ii T' ν hν
    (σ (↑hyu.unit⁻¹ ^ ν * fb)) ?_ (fun j => σ (↑hyu.unit⁻¹ * zb j)) ?_ ?_ ?_ i0 hT'x
  · rw [← hσx, ← map_pow, ← map_mul, show T.toRing (y i0 : R) ^ ν * (↑hyu.unit⁻¹ ^ ν * fb) =
      T.toRing f by rw [← hfb, hxv]; ring, hσ f]
  · intro j
    rw [← hσx, ← map_mul, show T.toRing (y i0 : R) * (↑hyu.unit⁻¹ * zb j) = T.toRing (z j) by
      rw [← hzb j, hxv]; ring, hσ]
  · intro j
    have h1 : ↑hyu.unit⁻¹ * zb j ∈ maximalIdeal T.ring := Ideal.mul_mem_left _ _ (h_iii j)
    refine (IsLocalRing.mem_maximalIdeal _).mpr fun hu => ?_
    have := hu.map σ.symm.toRingHom
    simp only [RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, RingEquiv.symm_apply_apply] at this
    exact (IsLocalRing.mem_maximalIdeal _).mp h1 this
  · rw [ordElem_maximalIdeal_ringEquiv_aux σ,
      Ideal.ordElem_isUnit_mul _ ((hyu.unit⁻¹).isUnit.pow ν), hord]

end Lemma24

/-! ### Lemma 25 (pp. 269–273) and Theorem 9 (pp. 273–274)

These two declarations (`exists_isJTauZStable_snoc` and
`exists_isJStableTauFrame_and_isJStable_standardBase`) are in
`Hironaka/Ch3/TauFrameExistence.lean`, which imports this file. -/


end Hironaka
