/-
Copyright (c) 2026 Daattavya Aggarwal, Minhyong Kim, Oisin Kim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daattavya Aggarwal, Minhyong Kim, Oisin Kim
-/
module

public import Mathlib.FieldTheory.PurelyInseparable.Basic
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Architect
public import Hironaka.Compat.RegularLocalRing
public import Hironaka.Compat.Graded
public import Hironaka.Compat.RSOPFlat
public import Hironaka.Ch0.NormalFlatness

/-!
# Ch. III, shared definitions (pp. 205–214)

The definitions of Ch. III §1–§2 that every later section of the chapter uses:

* Definition 1 (p. 205): the characters ν^{(i)}(J) of an ideal `J` of a regular local ring `R`;
* Definition 2 (p. 207): the sequence ν*(J) and its lexicographic order;
* Definition 3 (p. 208): standard bases;
* p. 207: local homomorphisms of regular local rings "which transform a regular system of
  parameters of R into such a system of parameters of R'";
* p. 209: monoidal transforms of a regular local ring with center a prime ideal;
* p. 210, p. 211: residually algebraic / rational / separable local homomorphisms;
* Definition 5 (p. 213): the strict and weak transforms of an ideal in a monoidal transform;
* Definition 8 (p. 226): permissible centers for an ideal.

Throughout, `gr_M(R)` is `AssocGraded (maximalIdeal R)`, its homogeneous part of degree `μ` is
`AssocGraded.homogeneous _ μ`, and `gr_M(J, R)` is `grIdeal (maximalIdeal R) J`
(`Hironaka/Compat/Graded.lean`, after Ch. II §2, p. 189).
-/

@[expose] public section

open IsLocalRing

namespace Hironaka

universe u

/-! ### Definition 1 (p. 205): the characters ν^{(i)}(J) -/

section NuI

variable (R : Type u) [CommRing R] [IsRegularLocalRing R] (J : Ideal R)

/-- A *system of homogeneous elements* `(φ₁, …, φ_k)` of `gr_M(J, R)` "having the property that
`(φ₁, …, φ_k) gr_M(R) ∩ gr^μ_M(R) = gr^μ_M(J, R)` for all `μ < ν`" (Definition 1, p. 205).
"An empty system of elements generates the zero ideal." -/
def IsNuSystem (ν k : ℕ) (φ : Fin k → AssocGraded (maximalIdeal R)) : Prop :=
  (∀ j, φ j ∈ grIdeal (maximalIdeal R) J ∧
    ∃ d : ℕ, φ j ∈ AssocGraded.homogeneous (maximalIdeal R) d) ∧
  ∀ μ < ν, ∀ ψ ∈ AssocGraded.homogeneous (maximalIdeal R) μ,
    (ψ ∈ Ideal.span (Set.range φ) ↔ ψ ∈ grIdeal (maximalIdeal R) J)

/-- Definition 1, p. 205: "Given `R` and `J` as above, we define `ν^{(i)}(J)` (a non-negative
integer or infinity) for every positive integer `i` as follows: `ν^{(i)}(J)` is the maximal
integer `ν`, if it exists, such that there exists a system of homogeneous elements
`(φ₁, …, φ_{i-1})` in `gr_M(J, R)` having the property that
`(φ₁, …, φ_{i-1}) gr_M(R) ∩ gr^μ_M(R) = gr^μ_M(J, R)` for all `μ < ν`; and, if such `ν` does not
exist, we set `ν^{(i)}(J) = ∞`."

Formalization note (encoding): `ν^{(i)}(J)` is the supremum in `ℕ∞` of the admissible `ν`; these
form a downward closed set containing `0`, so the supremum is the maximum when it is finite and
`∞` otherwise. -/
@[blueprint "def:III.1"
  (statement := /-- Let $R$ be a regular local ring with maximal ideal $M$ and $J$ an ideal in
    $R$. For every positive integer $i$, $\nu^{(i)}(J)$ is the maximal integer $\nu$, if it
    exists, such that there exists a system of homogeneous elements
    $(\varphi_1,\dots,\varphi_{i-1})$ in $\operatorname{gr}_M(J,R)$ having the property that
    $(\varphi_1,\dots,\varphi_{i-1})\operatorname{gr}_M(R)\cap\operatorname{gr}^\mu_M(R)
    =\operatorname{gr}^\mu_M(J,R)$ for all $\mu<\nu$; and, if such $\nu$ does not exist,
    $\nu^{(i)}(J)=\infty$. (An empty system of elements generates the zero ideal.)
    (Definition 1, p.~205.) Formalization note (encoding): $\nu^{(i)}(J)$ is defined as the
    supremum in $\mathbb N\cup\{\infty\}$ of the admissible $\nu$, which form a downward closed
    set containing $0$. -/)
  (latexEnv := "definition")]
noncomputable def nuI (i : ℕ+) : ℕ∞ :=
  ⨆ (ν : ℕ) (_ : ∃ φ : Fin ((i : ℕ) - 1) → AssocGraded (maximalIdeal R),
    IsNuSystem R J ν ((i : ℕ) - 1) φ), (ν : ℕ∞)

/-! ### Definition 2 (p. 207): ν*(J) and the lexicographic order -/

/-- Definition 2, p. 207: "Given an ideal `J` in a regular local ring `R`, the sequence
`{ν^{(i)}(J)}_{i ∈ ℤ⁺}` will be denoted by `ν*(J)`. We define the lexicographical ordering in
the set of sequences `ν* = {ν^{(i)}}_{i ∈ ℤ⁺}` where `ν^{(i)}` are either integers or `∞`;
namely, for given `ν₁* = {ν₁^{(i)}}` and `ν₂* = {ν₂^{(i)}}`, we say that `ν₁* > ν₂*` if there
exists a positive integer `i` such that `ν₁^{(j)} = ν₂^{(j)}` for all `j < i` and
`ν₁^{(i)} > ν₂^{(i)}`."  Mathlib's `Lex (ℕ+ → ℕ∞)` carries exactly this order
(`Pi.Lex`: `x < y ↔ ∃ i, (∀ j < i, x j = y j) ∧ x i < y i`), and it is a linear order. -/
@[blueprint "def:III.2"
  (statement := /-- The sequence $\nu^*(J)=\{\nu^{(i)}(J)\}_{i\in\mathbb Z^+}$
    (\cref{def:III.1}). Sequences $\nu^*=\{\nu^{(i)}\}$ of integers or $\infty$ are ordered
    lexicographically: $\nu_1^*>\nu_2^*$ if there exists a positive integer $i$ such that
    $\nu_1^{(j)}=\nu_2^{(j)}$ for all $j<i$ and $\nu_1^{(i)}>\nu_2^{(i)}$.
    (Definition 2, p.~207.) -/)
  (latexEnv := "definition")]
noncomputable def nuStar : Lex (ℕ+ → ℕ∞) := toLex fun i => nuI R J i

/-! ### Definition 3 (p. 208): standard bases -/

/-- The properties (i), (ii), (iii) of Lemma 1 (p. 205) for a system `(φ₁, …, φ_m)` of
homogeneous elements of `gr_M(J, R)`: (i) `gr_M(J, R) = (φ₁, …, φ_m) gr_M(R)`; (ii) if
`ν_i = deg φ_i` then `ν₁ ≤ ν₂ ≤ … ≤ ν_m`; (iii) for every `i ≥ 1`, `φ_i ∉ (φ₁, …, φ_{i-1}) gr_M(R)`
(where the empty system of elements generates the zero ideal).  The degrees are recorded by a
function `d` with `φ_i ∈ gr^{d i}_M(R)`; by (iii) no `φ_i` is zero, so `d` is determined. -/
def IsMinimalGradedGenerators {m : ℕ} (φ : Fin m → AssocGraded (maximalIdeal R)) : Prop :=
  (∀ j, φ j ∈ grIdeal (maximalIdeal R) J) ∧
  (∃ d : Fin m → ℕ, (∀ j, φ j ∈ AssocGraded.homogeneous (maximalIdeal R) (d j)) ∧ Monotone d) ∧
  grIdeal (maximalIdeal R) J = Ideal.span (Set.range φ) ∧
  ∀ i : Fin m, φ i ∉ Ideal.span (Set.range fun j : Fin i => φ (Fin.castLE i.2.le j))

/-- Definition 3, p. 208: "Let `J` be an ideal in a regular local ring `R`. Then a system of
elements `(f₁, …, f_m)` of `J` (`m ≥ 0`) is called a *standard base* of `J` if the system of
their initial forms in `gr_M(R)` has the properties (i), (ii), and (iii) of Lemma 1." -/
@[blueprint "def:III.3"
  (statement := /-- Let $J$ be an ideal in a regular local ring $R$. A system of elements
    $(f_1,\dots,f_m)$ of $J$ ($m\ge0$) is a \emph{standard base} of $J$ if the system of their
    initial forms in $\operatorname{gr}_M(R)$ (\cref{def:II.2-initial-form}) has the
    properties (i), (ii), (iii) of Lemma~1 (\cref{lem:III.1}): (i)
    $\operatorname{gr}_M(J,R)=(\varphi_1,\dots,\varphi_m)\operatorname{gr}_M(R)$; (ii) if
    $\nu_i=\deg\varphi_i$ then $\nu_1\le\nu_2\le\dots\le\nu_m$; (iii) for every $i\ge1$,
    $\varphi_i\notin(\varphi_1,\dots,\varphi_{i-1})\operatorname{gr}_M(R)$.
    (Definition 3, p.~208.) -/)
  (latexEnv := "definition")]
def IsStandardBase {m : ℕ} (f : Fin m → R) : Prop :=
  (∀ j, f j ∈ J) ∧ IsMinimalGradedGenerators R J fun j => initialForm (maximalIdeal R) (f j)

end NuI

/-! ### Local homomorphisms preserving regular systems of parameters (p. 207) -/

section RSOP

variable {R R' : Type u} [CommRing R] [CommRing R'] [IsLocalRing R] [IsLocalRing R']

open Classical in
/-- p. 207 (and throughout Ch. III): "a local homomorphism `α : R → R'` of regular local rings
which transforms a regular system of parameters of `R` into such a system of parameters of
`R'`".

Formalization note (encoding): the paper speaks of the *system* `(α(x₁), …, α(x_n))`: it is a
regular system of parameters of `R'`, so in particular its `n` members are distinct.  A regular
system of parameters is a finite set here (`IsRegularSystemOfParameters`), so the distinctness is
the condition `Set.InjOn α s`; without it two parameters could collapse (e.g.
`k[[x, y]] → k[[x]]`, `x, y ↦ x`), and the corollary to Lemma 2 and Lemma 13 would fail.  With
it the definition is equivalent to the paper's. -/
@[blueprint "def:III.rsop-map"
  (statement := /-- A local homomorphism $\alpha\colon R\to R'$ of regular local rings
    \emph{transforms a regular system of parameters of $R$ into such a system of parameters
    of $R'$} if for some regular system of parameters $(x_1,\dots,x_n)$ of $R$
    (\cref{def:rsop}), $(\alpha(x_1),\dots,\alpha(x_n))$ is a regular system of parameters of
    $R'$. (p.~207.) Formalization note (encoding): regular systems of parameters are finite
    sets in the formalization; as the $n$ members of the system
    $(\alpha(x_1),\dots,\alpha(x_n))$ are distinct, $\alpha$ is required to be injective on
    $\{x_1,\dots,x_n\}$, which makes the definition equivalent to the paper's. -/)
  (latexEnv := "definition")]
def RingHom.MapsRSOP (α : R →+* R') : Prop :=
  ∃ s : Finset R, IsRegularSystemOfParameters R s ∧
    IsRegularSystemOfParameters R' (s.image α) ∧ Set.InjOn α s

/-- p. 210: "for a pair of local rings `R` and `R'` with a local homomorphism of `R` into `R'`,
`R'` will be said to be residually algebraic (resp. residually rational) over `R` if the
residue field of `R'` is algebraic (resp. algebraic of degree 1) over that of `R`."  The
residue field of `R'` is an extension of that of `R` through `ResidueField.map α`; "algebraic
of degree 1" means that this field homomorphism is surjective. -/
@[blueprint "def:III.2-residually"
  (statement := /-- Let $R\to R'$ be a local homomorphism of local rings. $R'$ is
    \emph{residually algebraic} (resp.\ \emph{residually rational}) over $R$ if the residue
    field of $R'$ is algebraic (resp.\ algebraic of degree $1$) over that of $R$ (p.~210).
    $R'$ is \emph{residually separable} over $R$ if the residue field $\bar k$ of $R'$ is
    separable over the residue field $k$ of $R$ ``in the sense that for every purely
    inseparable extension $k'$ over $k$ the tensor product $\bar k\otimes_k k'$ has no
    nilpotent elements'' (pp.~211--212). -/)
  (latexEnv := "definition")]
def RingHom.IsResiduallyAlgebraic (α : R →+* R') [IsLocalHom α] : Prop :=
  letI := (ResidueField.map α).toAlgebra
  Algebra.IsAlgebraic (ResidueField R) (ResidueField R')

/-- Residually rational (p. 210): the residue field extension has degree 1. -/
def RingHom.IsResiduallyRational (α : R →+* R') [IsLocalHom α] : Prop :=
  Function.Surjective (ResidueField.map α)

/-- Residually separable (pp. 211–212): for every purely inseparable extension `k'` of the
residue field `k` of `R`, the tensor product `k̄ ⊗_k k'` with the residue field `k̄` of `R'`
"has no nilpotent elements".

Formalization note (encoding): `k'` ranges over fields in the universe of `R`; this loses
nothing, a purely inseparable extension of `k` being algebraic over `k`. -/
def RingHom.IsResiduallySeparable (α : R →+* R') [IsLocalHom α] : Prop :=
  letI := (ResidueField.map α).toAlgebra
  ∀ (k' : Type u) [Field k'] [Algebra (ResidueField R) k'],
    IsPurelyInseparable (ResidueField R) k' →
      IsReduced (TensorProduct (ResidueField R) (ResidueField R') k')

/-- Residually separable algebraic (Theorem 3, p. 233): the residue field of `R'` is a separable
algebraic extension of that of `R`. -/
def RingHom.IsResiduallySeparableAlgebraic (α : R →+* R') [IsLocalHom α] : Prop :=
  letI := (ResidueField.map α).toAlgebra
  Algebra.IsSeparable (ResidueField R) (ResidueField R')

end RSOP

section RSOPFlat

variable {R R' : Type u} [CommRing R] [CommRing R'] [IsRegularLocalRing R] [IsRegularLocalRing R']

/-- p. 207 (proof of the Corollary to Lemma 2): "The assumption on `α` implies that `R'` is flat
over `R`."  The paper gives no argument, and the fact is used again for Lemma 5 of §2 (p. 216).

Deviation from the paper (gap filled): the paper asserts this without proof or reference. It is
proved in `Hironaka.Compat.RSOPFlat` (`flat_of_isRegularSystemOfParameters_image`): induction on the
number of parameters and the local criterion of flatness (cf. Matsumura, *Commutative Ring
Theory*, Theorem 23.1). -/
@[blueprint "lem:III.rsop-map-flat"
  (statement := /-- Let $\alpha\colon R\to R'$ be a local homomorphism of regular local rings
    which transforms a regular system of parameters of $R$ into such a system of parameters
    of $R'$ (\cref{def:III.rsop-map}). Then $R'$ is flat over $R$. (Used without proof on
    pp.~207 and~216.) -/)
  (proof := /-- Not proved in the paper. Immediate from \cref{lem:III.2-rsop-flat}, applied to
    the regular system of parameters $s$ of $R$ which $\alpha$ maps injectively onto a regular
    system of parameters of $R'$.

    \textbf{Deviation from the paper (gap filled).} The paper asserts this fact without proof
    or reference (``The assumption on $\alpha$ implies that $R'$ is flat over $R$'', p.~207).
    It is proved here (\cref{lem:III.2-rsop-flat}: induction on the number of parameters and the
    local criterion of flatness; cf.\ Matsumura, \emph{Commutative Ring Theory}, Theorem~23.1). -/)
  (latexEnv := "lemma")]
theorem RingHom.MapsRSOP.flat {α : R →+* R'} [IsLocalHom α] (hα : RingHom.MapsRSOP α) :
    letI := α.toAlgebra
    Module.Flat R R' := by
  obtain ⟨s, hs, hs', hinj⟩ := hα
  exact Hironaka.flat_of_isRegularSystemOfParameters_image α s hs hs' hinj

end RSOPFlat

/-! ### Monoidal transforms of a regular local ring (p. 209) -/

section MonoidalTransform

variable (R : Type u) [CommRing R] [IsRegularLocalRing R] [IsDomain R]

/-- The ring `R[x⁻¹P]` of p. 209: the subalgebra of the field of quotients of `R` generated by the
elements `p/x`, `p ∈ P`. -/
noncomputable def blowupAlgebra (P : Ideal R) (x : R) : Subalgebra R (FractionRing R) :=
  Algebra.adjoin R ((fun p => algebraMap R (FractionRing R) p / algebraMap R (FractionRing R) x) ''
    (P : Set R))

/-- p. 209: "Let `R` be a regular local ring and `P` a prime ideal in `R` such that `P ≠ (0)` and
`S = R/P` is regular. By a *monoidal transform of `R` with center `P`*, we shall mean a local
ring in the field of quotients of `R` which is obtained as a localization of a ring of the form
`R[x⁻¹P]` with `x ∈ P` with respect to a prime ideal in `R[x⁻¹P]` containing the maximal ideal
of `R`. In this definition of monoidal transform, it is convenient to include the case in which
`P = R`."

Formalization note (encoding): a monoidal transform is recorded by its data, the element `x`
(non-zero, so that `x⁻¹` exists in the field of quotients) and the prime ideal `M'`; the local
ring is `R' = R[x⁻¹P]_{M'}` (`MonoidalTransform.ring`), an abstract localization isomorphic to a
subring of the field of quotients, with its canonical local homomorphism from `R`
(`MonoidalTransform.toRing`).  Different data giving the same subring are different objects.
The hypotheses "`P ≠ (0)` and `R/P` regular" are those of the statements that use the notion and
are not part of the data; for `P = R` the condition `M' ⊇ M` forces `x` to be a unit and
`R' ≅ R`, as in the paper. -/
@[blueprint "def:III.2-monoidal-transform"
  (statement := /-- Let $R$ be a regular local ring and $P$ a prime ideal in $R$. A
    \emph{monoidal transform of $R$ with center $P$} is a local ring in the field of quotients
    of $R$ obtained as a localization of a ring of the form $R[x^{-1}P]$, $x\in P$, with
    respect to a prime ideal in $R[x^{-1}P]$ containing the maximal ideal of $R$. The case
    $P=R$ is included, the monoidal transform being then canonically isomorphic to $R$.
    (p.~209.) Formalization note (encoding): a monoidal transform is recorded by the data
    $(x,M')$, $x\in P$ non-zero and $M'$ a prime of $R[x^{-1}P]$ containing $M$, the ring being
    the localization $R[x^{-1}P]_{M'}$; the standing hypotheses $P\ne(0)$ and $R/P$ regular are
    imposed by the statements that use the notion. -/)
  (latexEnv := "definition")]
structure MonoidalTransform (P : Ideal R) where
  /-- The element `x ∈ P` (non-zero) defining `R[x⁻¹P]`. -/
  x : R
  x_mem : x ∈ P
  x_ne_zero : x ≠ 0
  /-- A prime ideal of `R[x⁻¹P]` containing the maximal ideal of `R`. -/
  M' : Ideal (blowupAlgebra R P x)
  isPrime : M'.IsPrime
  le : (maximalIdeal R).map (algebraMap R (blowupAlgebra R P x)) ≤ M'

namespace MonoidalTransform

variable {R} {P : Ideal R} (t : MonoidalTransform R P)

attribute [instance] MonoidalTransform.isPrime

/-- The monoidal transform itself, `R' = R[x⁻¹P]_{M'}`, a local ring.

Implementation note: this is a `def`, not an `abbrev`, with its algebraic structure transported
explicitly below.  `Localization.AtPrime` of a subalgebra of a field reaches its ring structure
along several instance paths (through `OreLocalization`, `Localization`, `Subalgebra`,
`SubringClass`, …), which are definitionally but not syntactically equal; as an `abbrev`,
two independent elaborations of e.g. the associated graded ring `gr_{M'}(R')` could take
minutes to unify.  A `def` with one instance per structure gives a single path. -/
def ring : Type u := Localization.AtPrime t.M'

noncomputable instance : CommRing t.ring := inferInstanceAs (CommRing (Localization.AtPrime t.M'))

instance : IsLocalRing t.ring := inferInstanceAs (IsLocalRing (Localization.AtPrime t.M'))

instance : IsDomain t.ring := inferInstanceAs (IsDomain (Localization.AtPrime t.M'))

noncomputable instance : Algebra (blowupAlgebra R P t.x) t.ring :=
  inferInstanceAs (Algebra (blowupAlgebra R P t.x) (Localization.AtPrime t.M'))

instance : IsLocalization.AtPrime t.ring t.M' :=
  inferInstanceAs (IsLocalization.AtPrime (Localization.AtPrime t.M') t.M')

/-- The canonical local homomorphism `R → R'`. -/
noncomputable def toRing : R →+* t.ring :=
  (algebraMap (blowupAlgebra R P t.x) t.ring).comp (algebraMap R (blowupAlgebra R P t.x))

/-- The image of `x` in `R'`; by construction `P R' = (x) R'`. -/
noncomputable def xR : t.ring := t.toRing t.x

end MonoidalTransform

end MonoidalTransform

/-! ### Definition 5 (p. 213): strict and weak transforms of an ideal -/

section Transforms

variable {R : Type u} [CommRing R] [IsRegularLocalRing R] [IsDomain R] {P : Ideal R}
  (t : MonoidalTransform R P)

/-- Definition 5, p. 213: "Let `R` be a regular local ring, `P` a prime ideal in `R` such that
`R/P` is regular, and `J` an ideal in `R`. We also consider the special case in which `R = P`.
Let `R'` be a monoidal transform of `R` with center `P`. We define the *strict transform of `J`
in `R'`* (with respect to the center `P`) to be the ideal in `R'` which is generated by those
elements of the form `x⁻ᵛ f` with `x ∈ R'` such that `(x)R' = PR'` and with `f ∈ J` such that
`ν_P(f) ≥ ν`."

Formalization note (encoding): in the domain `R'`, "`y = x⁻ᵛ f`" is expressed as `xᵛ y = f`. -/
@[blueprint "def:III.5-strict"
  (statement := /-- Let $R$ be a regular local ring, $P$ a prime ideal in $R$ such that $R/P$
    is regular, $J$ an ideal in $R$ (the case $P=R$ included), and $R'$ a monoidal transform
    of $R$ with center $P$ (\cref{def:III.2-monoidal-transform}). The \emph{strict transform
    of $J$ in $R'$} (with respect to the center $P$) is the ideal in $R'$ generated by the
    elements of the form $x^{-\nu}f$ with $x\in R'$ such that $(x)R'=PR'$ and $f\in J$ such
    that $\nu_P(f)\ge\nu$. (Definition 5, p.~213.) Formalization note (encoding): in the
    domain $R'$, ``$y=x^{-\nu}f$'' is expressed as $x^\nu y=f$. -/)
  (latexEnv := "definition")]
noncomputable def strictTransformIdeal (J : Ideal R) : Ideal t.ring :=
  Ideal.span {y : t.ring | ∃ (x : t.ring) (_ : Ideal.span {x} = P.map t.toRing) (f : R)
    (_ : f ∈ J) (ν : ℕ), (ν : ℕ∞) ≤ Ideal.ordElem P f ∧ x ^ ν * y = t.toRing f}

/-- Definition 5, p. 213, continued: "We define the *weak transform of `J` in `R'`* (with
respect to the center `P`) to be the ideal in `R'` which is generated by those elements of the
form `x⁻ᵛ f` with `x ∈ R'` such that `(x)R = PR'` [sic], with `f ∈ J` and with `ν ≤ ν_P(J)`.
(Here, `ν_P(J) = ∞` if `P = R`.)"  (`Ideal.ord P J` is `∞` for `P = R`,
\cref{lem:order-nu-basic}.)  As for the strict transform, `x⁻ᵛ f = y` is expressed as `xᵛ y = f`.

Deviation from the paper (paper misprint): the paper prints "`(x)R = PR'`" in the definition of
the weak transform; the meaning is `(x)R' = PR'`, as in the definition of the strict transform two
lines earlier (`(x)R ⊆ R` makes no sense for `x ∈ R'`).  The formalization uses `(x)R' = PR'`. -/
@[blueprint "def:III.5-weak"
  (statement := /-- Notation as in \cref{def:III.5-strict}. The \emph{weak transform of $J$
    in $R'$} (with respect to the center $P$) is the ideal in $R'$ generated by the elements
    of the form $x^{-\nu}f$ with $x\in R'$ such that $(x)R'=PR'$, $f\in J$ and
    $\nu\le\nu_P(J)$ (\cref{def:order-nu}; $\nu_P(J)=\infty$ if $P=R$).
    (Definition 5, p.~213.)

    \textbf{Paper misprint.} For the weak transform the paper prints ``$(x)\mathbf R
    =\mathbf P\mathbf R'$''; the intended condition is $(x)R'=PR'$, as in the definition of
    the strict transform two lines earlier, and this is what is formalized. -/)
  (latexEnv := "definition")]
noncomputable def weakTransformIdeal (J : Ideal R) : Ideal t.ring :=
  Ideal.span {y : t.ring | ∃ (x : t.ring) (_ : Ideal.span {x} = P.map t.toRing) (f : R)
    (_ : f ∈ J) (ν : ℕ), (ν : ℕ∞) ≤ Ideal.ord P J ∧ x ^ ν * y = t.toRing f}

end Transforms

/-! ### Definition 8 (p. 226): permissible centers -/

section PermissibleCenter

variable (R : Type u) [CommRing R] [IsRegularLocalRing R]

/-- Definition 8, p. 226: "A prime ideal `P` in `R` is called a *permissible center* (of monoidal
transformation) for `J`, if it satisfies the following conditions: (i) `P ⊇ J` and `R/P` is
regular, (ii) `gr_{P/J}(R/J)` is flat over `R/P`. … For the sake of convenience, we agree that
`P = R` is a permissible center for every ideal `J` in `R`."  The paper's equivalent forms
(ii)*, (ii)** (Cor. 1 of Th. 2, Ch. II §2) are recorded in Ch. III §5.

Formalization note (encoding): condition (ii) is Definition 1 of Ch. 0 for the local ring `R/J`
and the ideal `P/J` (`IsNormallyFlatAlongIdeal`: every `P̄ⁿ/P̄ⁿ⁺¹` is free over `O/P̄`, cf.
p. 136), which for the noetherian local ring `O = R/J` is equivalent to the flatness of
`gr_{P/J}(R/J)` (`isNormallyFlatAlongIdeal_iff_isGrFlat`). -/
@[blueprint "def:III.8"
  (statement := /-- Let $R$ be a regular local ring and $J$ an ideal in $R$. A prime ideal $P$
    in $R$ is a \emph{permissible center} (of monoidal transformation) for $J$ if (i)
    $P\supseteq J$ and $R/P$ is regular, and (ii) $\operatorname{gr}_{P/J}(R/J)$ is flat over
    $R/P$ (\cref{def:normally-flat-ideal}). By convention $P=R$ is a permissible center for
    every ideal $J$. (Definition 8, p.~226.) Formalization note (encoding): (ii) is expressed
    as the freeness of every $\bar P^n/\bar P^{n+1}$ over $O/\bar P$ ($O=R/J$, $\bar P=P/J$),
    equivalent to the flatness of $\operatorname{gr}_{\bar P}(O)$ for the noetherian local ring
    $O$. -/)
  (latexEnv := "definition")]
def IsPermissibleCenter (J P : Ideal R) : Prop :=
  P = ⊤ ∨ (P.IsPrime ∧ J ≤ P ∧ IsRegularLocalRing (R ⧸ P) ∧
    IsNormallyFlatAlongIdeal (P.map (Ideal.Quotient.mk J)))

end PermissibleCenter

end Hironaka

