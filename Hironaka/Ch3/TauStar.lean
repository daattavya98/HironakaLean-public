/-
Copyright (c) 2026 Daattavya Aggarwal, Minhyong Kim, Oisin Kim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daattavya Aggarwal, Minhyong Kim, Oisin Kim
-/
module

public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.Algebra.Module.StablyFree.Basic
public import Mathlib.Data.Finset.Functor
public import Mathlib.Data.Nat.Nth
public import Mathlib.FieldTheory.FinTrdeg
public import Mathlib.LinearAlgebra.Dimension.OrzechProperty
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.Coalgebra.IsFrobenius
public import Mathlib.RingTheory.Etale.Weakly
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.HopfAlgebra.Basic
public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.TotallySplit
public import Mathlib.RingTheory.Trace.Basic
public import Architect
public import Hironaka.Ch3.Basic
public import Hironaka.Compat.RegularGraded
public import Hironaka.Ch3.NuStar
public import Hironaka.Statements

/-!
# Ch. III §4: The numerical characters τ*(J) of a local ideal J, and a regular system of
τ-parameters for J (pp. 221–226)

> Let R be a regular local ring, M the maximal ideal of R, and J an ideal in R. Let
> (μ₁, …, μ_t) be the system of distinct integers which appear in the sequence ν*(J), and
> which are arranged in the increasing order: μ₁ < μ₂ < … < μ_t. The system of integers
> (μ₁, …, μ_t) is uniquely determined by the ideal J and is non-empty unless J = (0).  (p. 221)

Contents, in the paper's order: Definition 6 (t(J), μ*(J), τ*(J)), Lemma 10 (intersection of
two submodules with the property of Definition 6), its Corollary (the smallest submodule
T_a), Definition 7 (regular systems of a-th τ-parameters), Lemma 11, the characterization of
separable field extensions of p. 223 (MacLane), Lemma 12 (base change of the property of
Definition 6 along a separable extension of the coefficient field) and Lemma 13 (invariance
of t(J) and τ*(J) under local homomorphisms transforming a regular system of parameters into
such a system, with separable residue field extension).

## Encoding of the property of Definition 6

Throughout, `gr_M(R)` is `AssocGraded (maximalIdeal R)`, a `K = R/M`-algebra
(`AssocGraded.instAlgebraQuotient`), `gr^μ_M(R)` is `AssocGraded.homogeneous _ μ` and
`gr_M(J, R)` is `grIdeal (maximalIdeal R) J` (`Hironaka/Compat/Graded.lean`).  "Linear forms"
are the elements of `gr¹_M(R)`; for a `K`-submodule `T ⊆ gr¹_M(R)`, the `K`-subalgebra
`K[T]` is `Algebra.adjoin K (T : Set _)`, the ideal `(gr_M(J, R) ∩ K[T]) gr_M(R)` is
`Ideal.span ((grIdeal M J : Set _) ∩ (Algebra.adjoin K T : Set _))`, and the equality
`gr^μ_M(J, R) = gr^μ_M(R) ∩ (gr_M(J, R) ∩ K[T]) gr_M(R)` is
`∀ ψ ∈ homogeneous M μ, ψ ∈ grIdeal M J ↔ ψ ∈ Ideal.span (…)`.  The predicate
`IsTauSubmodule R J T μ₀` ("`T ⊆ gr¹_M(R)` and the equality holds for all `μ ≤ μ₀`") packages
this and is used by every statement of the section; `IsTauSubmoduleMv` is the same predicate
for a polynomial ring `K[X₁, …, X_n]` (Lemmas 10 and 12).
-/

@[expose] public section

open IsLocalRing

namespace Hironaka

universe u

/-! ### Definition 6 (p. 221): t(J), μ*(J) and τ*(J) -/

section Definition6

variable (R : Type u) [CommRing R] [IsRegularLocalRing R] (J : Ideal R)

/-- p. 221: the set of "distinct integers which appear in the sequence ν*(J)", i.e. the finite
values `nuI R J i ≠ ∞` of the characters ν^{(i)}(J) (\cref{def:III.1}).  Arranged in
increasing order they form the system `(μ₁, …, μ_t) = μ*(J)` (`mu R J`). -/
def muSet : Set ℕ := {μ | ∃ i : ℕ+, nuI R J i = (μ : ℕ∞)}

/-- Definition 6, p. 221: "The number `t` of distinct integers which appear in the sequence
`ν*(J)` will be denoted by `t(J)`."  Encoded as the cardinality `Set.ncard` of `muSet R J`;
this set is finite (`muSet_finite`), and `Set.ncard` is total in any case. -/
@[blueprint "def:III.6-t"
  (statement := /-- Let $R$ be a regular local ring, $M$ its maximal ideal, and $J$ an ideal
    in $R$. Let $(\mu_1,\dots,\mu_t)$ be the system of distinct integers which appear in the
    sequence $\nu^*(J)$ (\cref{def:III.2}), arranged in increasing order
    $\mu_1<\mu_2<\dots<\mu_t$; it is uniquely determined by $J$ and is non-empty unless
    $J=(0)$. The number $t$ of distinct integers which appear in $\nu^*(J)$ is denoted by
    $t(J)$. (Definition 6, p.~221.) -/)
  (latexEnv := "definition")]
noncomputable def t : ℕ := (muSet R J).ncard

/-- Definition 6, p. 221: "The integer `μ_a` (`1 ≤ a ≤ t`) will be denoted by `μ^{(a)}(J)`, and
the system `(μ₁, …, μ_t)` by `μ*(J)`."  `mu R J a` is the `a`-th smallest element of
`muSet R J`, **1-indexed** as in the paper (`Nat.nth` is 0-indexed, whence the `a - 1`).
Junk values: for `a = 0` it is `μ₁` (since `0 - 1 = 0` in `ℕ`), and for `a > t(J)` it is `0`
(`Nat.nth_of_card_le`); every statement below restricts to `1 ≤ a ≤ t(J)`. -/
@[blueprint "def:III.6-mu"
  (statement := /-- Notation as in \cref{def:III.6-t}. For $1\le a\le t=t(J)$ the integer
    $\mu_a$ is denoted by $\mu^{(a)}(J)$, and the system $(\mu_1,\dots,\mu_t)$ by $\mu^*(J)$.
    (Definition 6, p.~221.) -/)
  (latexEnv := "definition")]
noncomputable def mu (a : ℕ) : ℕ := Nat.nth (· ∈ muSet R J) (a - 1)

/-- The property required of a system of linear forms in Definition 6, of a `K`-submodule
`T` of `gr¹_M(R)` and a bound `μ₀`: "`gr^μ_M(J, R) = gr^μ_M(R) ∩ (gr_M(J, R) ∩ K[T]) gr_M(R)`
for all non-negative integers `μ ≤ μ₀`, where `K = R/M` and `K[T]` denotes the `K`-subalgebra
of `gr_M(R)` generated by `T`" (p. 221).  The first conjunct records that `T` consists of
linear forms (`T ⊆ gr¹_M(R)`); see the module docstring for the encoding of the equality. -/
@[blueprint "def:III.6-property"
  (statement := /-- Let $R$ be a regular local ring with maximal ideal $M$, $K=R/M$, $J$ an
    ideal in $R$ and $\mu_0\ge0$. A $K$-submodule $T$ of $\operatorname{gr}^1_M(R)$ \emph{has
    the property of Definition 6 up to degree $\mu_0$} if
    $\operatorname{gr}^\mu_M(J,R)=\operatorname{gr}^\mu_M(R)\cap(\operatorname{gr}_M(J,R)\cap
    K[T])\operatorname{gr}_M(R)$ for all non-negative integers $\mu\le\mu_0$, where $K[T]$
    denotes the $K$-subalgebra of $\operatorname{gr}_M(R)$ generated by the elements of $T$.
    (The property of a system of linear forms $W_1,\dots,W_\tau$ in Definition 6, p.~221,
    is this property of the $K$-submodule they generate, since
    $K[W_1,\dots,W_\tau]=K[T]$.) -/)
  (latexEnv := "definition")]
def IsTauSubmodule (T : Submodule (R ⧸ maximalIdeal R) (AssocGraded (maximalIdeal R)))
    (μ₀ : ℕ) : Prop :=
  T ≤ AssocGraded.homogeneous (maximalIdeal R) 1 ∧
  ∀ μ ≤ μ₀, ∀ ψ ∈ AssocGraded.homogeneous (maximalIdeal R) μ,
    (ψ ∈ grIdeal (maximalIdeal R) J ↔
      ψ ∈ Ideal.span ((grIdeal (maximalIdeal R) J : Set (AssocGraded (maximalIdeal R))) ∩
        (Algebra.adjoin (R ⧸ maximalIdeal R) (T : Set (AssocGraded (maximalIdeal R))) :
          Set (AssocGraded (maximalIdeal R)))))

/-- Definition 6, p. 221: "For every positive integer `a ≤ t`, we define `τ^{(a)}(J)` to be the
smallest integer `τ_a (≥ 0)` such that: There exists a system of `τ_a` linear forms
`W₁, …, W_{τ_a}` in `gr_M(R)` which has the property that
`gr^μ_M(J, R) = gr^μ_M(R) ∩ (gr_M(J, R) ∩ K[W₁, …, W_{τ_a}]) gr_M(R)` for all non-negative
integers `μ ≤ μ_a = μ^{(a)}(J)`, where `K = R/M` and `K[W₁, …, W_{τ_a}]` denotes the
`K`-subalgebra of `gr_M(R)` generated by `W₁, …, W_{τ_a}`.  (We have `τ_a > 0` for all `a`
unless `J = R`.  If `J = R`, then `μ*(J) = (μ₁)` with `μ₁ = 0`, and `τ₁ = 0`.  The empty
system generates the `K`-subalgebra `K` of `gr_M(R)`.)"

Encoded as the infimum (`sInf` on `ℕ`) of the set of `τ` for which a system `W : Fin τ → gr_M(R)`
of linear forms exists whose `K`-span satisfies `IsTauSubmodule R J _ (mu R J a)`; this set is
non-empty (`tau_spec`: take a `K`-basis of the finite-dimensional `K`-module `gr¹_M(R)`, which
generates `gr_M(R)`), so the infimum is attained.  Junk values for `a = 0` and `a > t(J)`
are inherited from `mu R J a`.

The parenthetical claims are proved (gaps filled): "`τ_a > 0` for all `a` unless `J = R`" is
`tau_pos`; "If `J = R`, then `μ*(J) = (μ₁)` with `μ₁ = 0`, and `τ₁ = 0`" is `tau_of_eq_top`
(with `muSet_of_eq_top`); "The empty system generates the `K`-subalgebra `K` of `gr_M(R)`" is
`adjoin_span_range_elim_zero`. -/
@[blueprint "def:III.6"
  (statement := /-- Notation as in \cref{def:III.6-t}. For every positive integer $a\le t$,
    $\tau^{(a)}(J)$ is the smallest integer $\tau_a\ (\ge0)$ such that there exists a system of
    $\tau_a$ linear forms $W_1,\dots,W_{\tau_a}$ in $\operatorname{gr}_M(R)$ which has the
    property that $\operatorname{gr}^\mu_M(J,R)=\operatorname{gr}^\mu_M(R)\cap
    (\operatorname{gr}_M(J,R)\cap K[W_1,\dots,W_{\tau_a}])\operatorname{gr}_M(R)$ for all
    non-negative integers $\mu\le\mu_a=\mu^{(a)}(J)$, where $K=R/M$ and
    $K[W_1,\dots,W_{\tau_a}]$ denotes the $K$-subalgebra of $\operatorname{gr}_M(R)$ generated
    by $W_1,\dots,W_{\tau_a}$ (\cref{def:III.6-property}). (We have $\tau_a>0$ for all $a$
    unless $J=R$. If $J=R$, then $\mu^*(J)=(\mu_1)$ with $\mu_1=0$, and $\tau_1=0$. The empty
    system generates the $K$-subalgebra $K$ of $\operatorname{gr}_M(R)$.)
    (Definition 6, p.~221.)

    \textbf{Gaps in the paper filled.} The parenthetical claims are proved: ``$\tau_a>0$ for all
    $a$ unless $J=R$'' is \cref{lem:III.6-tau-pos}, and the case $J=R$ ($\mu^*(J)=(0)$, $t=1$,
    $\tau_1=0$, the empty system generating the $K$-subalgebra $K$) is
    \cref{lem:III.6-unit-ideal}. -/)
  (latexEnv := "definition")]
noncomputable def tau (a : ℕ) : ℕ :=
  sInf {τ : ℕ | ∃ W : Fin τ → AssocGraded (maximalIdeal R),
    (∀ i, W i ∈ AssocGraded.homogeneous (maximalIdeal R) 1) ∧
    IsTauSubmodule R J (Submodule.span (R ⧸ maximalIdeal R) (Set.range W)) (mu R J a)}

/-- Definition 6, p. 221: "We denote by `τ*(J)` the system `(τ^{(1)}(J), …, τ^{(t)}(J))`."
Indexed by `Fin (t R J)` (0-indexed), so that `tauStar R J a = tau R J (a + 1)`. -/
@[blueprint "def:III.6-tau-star"
  (statement := /-- Notation as in \cref{def:III.6}. $\tau^*(J)$ denotes the system
    $(\tau^{(1)}(J),\dots,\tau^{(t)}(J))$, $t=t(J)$. (Definition 6, p.~221.) -/)
  (latexEnv := "definition")]
noncomputable def tauStar : Fin (t R J) → ℕ := fun a => tau R J ((a : ℕ) + 1)

/-- The initial form of an element is homogeneous (of degree `ν_I(f)`, or `0` if it vanishes). -/
private theorem exists_initialForm_mem_homogeneous {A : Type*} [CommRing A] (I : Ideal A) (f : A) :
    ∃ d, initialForm I f ∈ AssocGraded.homogeneous I d := by
  by_cases htop : Ideal.ordElem I f = ⊤
  · exact ⟨0, by rw [initialForm, dite_eq_left htop]; exact zero_mem _⟩
  · obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp htop
    exact ⟨n, by rw [initialForm_eq_mk I hn.symm]; exact AssocGraded.mk_mem_homogeneous I _⟩

/-- `gr_M(J, R)` is generated by finitely many homogeneous elements of `gr_M(J, R)` (the ring
`gr_M(R)` is noetherian, being a quotient of the Rees algebra of the noetherian ring `R`, so
finitely many of the generating initial forms suffice). -/
private theorem exists_fin_homogeneous_generators :
    ∃ (m : ℕ) (φ : Fin m → AssocGraded (maximalIdeal R)),
      (∀ j, φ j ∈ grIdeal (maximalIdeal R) J ∧
        ∃ d, φ j ∈ AssocGraded.homogeneous (maximalIdeal R) d) ∧
      grIdeal (maximalIdeal R) J = Ideal.span (Set.range φ) := by
  have : IsNoetherianRing (AssocGraded (maximalIdeal R)) :=
    inferInstanceAs (IsNoetherianRing (reesAlgebra (maximalIdeal R) ⧸ _))
  obtain ⟨s, hs, hspan⟩ := (Submodule.fg_span_iff_fg_span_finset_subset
    (initialForm (maximalIdeal R) '' (J : Set R))).mp
      (IsNoetherian.noetherian (grIdeal (maximalIdeal R) J))
  refine ⟨s.card, fun j => (s.equivFin.symm j : AssocGraded (maximalIdeal R)), fun j => ?_, ?_⟩
  · obtain ⟨f, -, hf⟩ := hs (s.equivFin.symm j).2
    refine ⟨Ideal.subset_span (hs (s.equivFin.symm j).2), ?_⟩
    show ∃ d, (s.equivFin.symm j : AssocGraded (maximalIdeal R)) ∈ _
    rw [← hf]
    exact exists_initialForm_mem_homogeneous _ f
  · refine hspan.trans (congrArg (Submodule.span _) ?_)
    ext x
    refine ⟨fun hx => ⟨s.equivFin ⟨x, hx⟩, by simp⟩, ?_⟩
    rintro ⟨j, rfl⟩
    exact (s.equivFin.symm j).2

/-- `ν^{(i)}(J) = ∞` as soon as `i > m`, if `gr_M(J, R)` is generated by `m` homogeneous elements
of `gr_M(J, R)` (pad the generators by zeros, as in the second half of Lemma 1). -/
private theorem nuI_eq_top_of_generators {m : ℕ} (φ : Fin m → AssocGraded (maximalIdeal R))
    (hφ : ∀ j, φ j ∈ grIdeal (maximalIdeal R) J ∧
      ∃ d, φ j ∈ AssocGraded.homogeneous (maximalIdeal R) d)
    (h₁ : grIdeal (maximalIdeal R) J = Ideal.span (Set.range φ)) (i : ℕ+) (hi : m < (i : ℕ)) :
    nuI R J i = ⊤ := by
  let ψ : Fin ((i : ℕ) - 1) → AssocGraded (maximalIdeal R) := fun j =>
    if h : (j : ℕ) < m then φ ⟨j, h⟩ else 0
  have hspan : Ideal.span (Set.range ψ) = Ideal.span (Set.range φ) := by
    refine le_antisymm (Ideal.span_le.mpr ?_) (Ideal.span_le.mpr ?_)
    · rintro _ ⟨j, rfl⟩
      simp only [ψ]
      split_ifs with h
      · exact Ideal.subset_span ⟨_, rfl⟩
      · exact zero_mem _
    · rintro _ ⟨j, rfl⟩
      refine Ideal.subset_span ⟨⟨j, by omega⟩, ?_⟩
      simp [ψ, j.2]
  have hsys : ∀ ν : ℕ, ∃ ψ' : Fin ((i : ℕ) - 1) → AssocGraded (maximalIdeal R),
      IsNuSystem R J ν ((i : ℕ) - 1) ψ' := by
    intro ν
    refine ⟨ψ, fun j => ?_, fun μ _ χ _ => by rw [hspan, h₁]⟩
    simp only [ψ]
    split_ifs with h
    · exact hφ _
    · exact ⟨zero_mem _, 0, zero_mem _⟩
  unfold nuI
  refine le_antisymm le_top ?_
  rw [← ENat.iSup_natCast]
  exact iSup_le fun ν => le_iSup₂ (f := fun (ν : ℕ) (_ : ∃ ψ' : Fin ((i : ℕ) - 1) →
    AssocGraded (maximalIdeal R), IsNuSystem R J ν ((i : ℕ) - 1) ψ') => (ν : ℕ∞)) ν (hsys ν)

/-- p. 221: the system `(μ₁, …, μ_t)` of distinct integers appearing in `ν*(J)` is finite (so
that `t(J)` is a genuine count), and "is non-empty unless `J = (0)`".

Gap in the paper filled: the paper asserts this without argument; the proof below uses
finitely many homogeneous generators of `gr_M(J, R)` (padded by zeros) and Krull's
intersection theorem, not standard bases or Lemma 1. -/
@[blueprint "lem:III.6-mu-finite"
  (statement := /-- Let $R$ be a regular local ring and $J$ an ideal in $R$. The set of
    distinct integers which appear in the sequence $\nu^*(J)$ is finite, and it is non-empty
    unless $J=(0)$. (p.~221.) -/)
  (proof := /-- (The paper states this without argument.) Since $\operatorname{gr}_M(R)$ is
    noetherian, $\operatorname{gr}_M(J,R)$ is generated by finitely many homogeneous elements
    $\varphi_1,\dots,\varphi_m$ of $\operatorname{gr}_M(J,R)$. For $i>m$ the system
    $(\varphi_1,\dots,\varphi_m,0,\dots,0)$ of $i-1$ elements has the property of
    \cref{def:III.1} for every $\nu$, so $\nu^{(i)}(J)=\infty$; hence the finite values of
    $\nu^*(J)$ are among $\nu^{(1)}(J),\dots,\nu^{(m)}(J)$. If $J\ne(0)$, pick $0\ne f\in J$;
    then $\nu_M(f)=n<\infty$ (Krull), and the empty system cannot have the property of
    \cref{def:III.1} up to degree $n+1$ (the class of $f$ in $\operatorname{gr}^n_M(J,R)$ is
    non-zero), so $\nu^{(1)}(J)\le n<\infty$. -/)
  (latexEnv := "lemma")]
theorem muSet_finite : (muSet R J).Finite ∧ (J ≠ ⊥ → (muSet R J).Nonempty) := by
  refine ⟨?_, fun hJ => ?_⟩
  · -- with `m` homogeneous generators of `gr_M(J, R)`, `ν^{(i)}(J) = ∞` for `i > m`
    obtain ⟨m, φ, hφ, h₁⟩ := exists_fin_homogeneous_generators R J
    refine (((Set.finite_le_nat m).preimage PNat.coe_injective.injOn).image
      fun i : ℕ+ => (nuI R J i).toNat).subset ?_
    rintro μ ⟨i, hi⟩
    refine ⟨i, ?_, by simp only; rw [hi, ENat.toNat_natCast]⟩
    by_contra hlt
    rw [nuI_eq_top_of_generators R J φ hφ h₁ i (not_le.mp hlt)] at hi
    exact ENat.top_ne_natCast μ hi
  · -- `ν^{(1)}(J) ≤ ν_M(f) < ∞` for any `0 ≠ f ∈ J` (Krull)
    obtain ⟨f, hfJ, hf0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hJ
    have htop : Ideal.ordElem (maximalIdeal R) f ≠ ⊤ := fun h =>
      hf0 ((Ideal.ordElem_eq_top_iff_eq_zero (maximalIdeal.isMaximal R).ne_top).mp h)
    obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp htop
    have hle : nuI R J 1 ≤ n := by
      refine iSup₂_le fun ν ⟨φ, hφ⟩ => ?_
      by_contra hlt
      rw [not_le, Nat.cast_lt] at hlt
      have hmem := (hφ.2 n hlt (AssocGraded.mk (maximalIdeal R) n f
        (Ideal.mem_pow_of_ordElem hn.symm)) (AssocGraded.mk_mem_homogeneous _ _)).mpr
          (mk_mem_grIdeal _ hfJ _)
      have hbot : Ideal.span (Set.range φ) = ⊥ := by
        rw [Ideal.span_eq_bot]
        rintro _ ⟨j, rfl⟩
        exact absurd j.2 (by simp)
      rw [hbot, Ideal.mem_bot, AssocGraded.mk_eq_zero_iff] at hmem
      have := Ideal.le_ordElem hmem
      rw [← hn, Nat.cast_le] at this
      omega
    refine ⟨(nuI R J 1).toNat, 1, ?_⟩
    rw [ENat.natCast_toNat (ne_top_of_le_ne_top (ENat.natCast_ne_top n) hle)]

/-- `[a Xᵐ] · [b Xⁿ] = [ab Xᵐ⁺ⁿ]` in `gr_I(A)`. -/
private theorem mk_mul_mk_eq_mk_add {A : Type*} [CommRing A] (I : Ideal A) {m n : ℕ} {a b : A}
    (ha : a ∈ I ^ m) (hb : b ∈ I ^ n) :
    AssocGraded.mk I m a ha * AssocGraded.mk I n b hb =
      AssocGraded.mk I (m + n) (a * b) (by rw [pow_add]; exact Ideal.mul_mem_mul ha hb) := by
  refine (map_mul (Ideal.Quotient.mk (Ideal.map (algebraMap A (reesAlgebra I)) I)) _ _).symm.trans
    (congrArg _ (Subtype.ext ?_))
  exact Polynomial.monomial_mul_monomial m n a b

/-- The class of `a X⁰` is the image of `a mod I` under `A/I → gr_I(A)`. -/
private theorem mk_zero_eq_algebraMap_mk {A : Type*} [CommRing A] (I : Ideal A) (a : A)
    (ha : a ∈ I ^ 0) :
    AssocGraded.mk I 0 a ha = algebraMap (A ⧸ I) (AssocGraded I) (Ideal.Quotient.mk I a) := by
  show Ideal.Quotient.mk _ _ = Ideal.Quotient.mk _ (algebraMap A (reesAlgebra I) a)
  refine congrArg _ (Subtype.ext ?_)
  show Polynomial.monomial 0 a = Polynomial.C a
  rfl

/-- Every homogeneous element `[a Xⁿ]` lies in the `A/I`-subalgebra generated by `gr¹_I(A)`
(induction on `n`, using `Iⁿ⁺¹ = Iⁿ · I`). -/
private theorem mk_mem_adjoin {A : Type*} [CommRing A] (I : Ideal A) (n : ℕ) :
    ∀ (a : A) (ha : a ∈ I ^ n), AssocGraded.mk I n a ha ∈ Algebra.adjoin (A ⧸ I)
      (AssocGraded.homogeneous I 1 : Set (AssocGraded I)) := by
  induction n with
  | zero =>
    intro a ha
    rw [mk_zero_eq_algebraMap_mk]
    exact Subalgebra.algebraMap_mem _ _
  | succ n ih =>
    have key : ∀ (x : A) (hx : x ∈ I ^ n * I), AssocGraded.mk I (n + 1) x (by rwa [pow_succ])
        ∈ Algebra.adjoin (A ⧸ I) (AssocGraded.homogeneous I 1 : Set (AssocGraded I)) := by
      intro x hx
      induction hx using Submodule.mul_induction_on' with
      | mem_mul_mem m hm y hy =>
        rw [← mk_mul_mk_eq_mk_add I hm (by rwa [pow_one] : y ∈ I ^ 1)]
        exact Subalgebra.mul_mem _ (ih m hm)
          (Algebra.subset_adjoin (AssocGraded.mk_mem_homogeneous I _))
      | add x hx y hy ihx ihy =>
        rw [AssocGraded.mk_add I (n + 1) x y (by rwa [pow_succ]) (by rwa [pow_succ])]
        exact Subalgebra.add_mem _ ihx ihy
    intro a ha
    exact key a (by rwa [← pow_succ])

/-- `gr_I(A)` is generated as an `A/I`-algebra by its homogeneous part of degree `1`. -/
private theorem adjoin_homogeneous_one_eq_top {A : Type*} [CommRing A] (I : Ideal A) :
    Algebra.adjoin (A ⧸ I) (AssocGraded.homogeneous I 1 : Set (AssocGraded I)) = ⊤ := by
  refine eq_top_iff.mpr fun φ _ => ?_
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective φ
  rw [mk_eq_sum_mk]
  exact Subalgebra.sum_mem _ fun i _ => mk_mem_adjoin I i _ _

/-- For noetherian `A`, the homogeneous part `grⁿ_I(A)` is a finitely generated `A/I`-module. -/
private theorem homogeneous_fg {A : Type*} [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    (n : ℕ) : (AssocGraded.homogeneous I n).FG := by
  rw [AssocGraded.homogeneous, LinearMap.range_eq_map]
  exact Module.Finite.fg_top.map _

/-- `τ^{(a)}(J)` is attained: there is a system of `τ^{(a)}(J)` linear forms with the property
of Definition 6 up to degree `μ^{(a)}(J)` (the defining set of `tau` is non-empty). -/
@[blueprint "lem:III.6-tau-attained"
  (statement := /-- Notation as in \cref{def:III.6}. For every $a$ there exists a system of
    $\tau^{(a)}(J)$ linear forms $W_1,\dots,W_{\tau_a}$ in $\operatorname{gr}_M(R)$ with the
    property of \cref{def:III.6-property} up to degree $\mu^{(a)}(J)$; i.e. the minimum
    defining $\tau^{(a)}(J)$ exists. -/)
  (proof := /-- (Implicit in the paper.) $\operatorname{gr}_M(R)$ is generated as a
    $K$-algebra by its homogeneous part $\operatorname{gr}^1_M(R)$, a finitely generated
    $K$-module (this does not use the regularity of $R$). Hence a finite system of generators
    $W$ of $\operatorname{gr}^1_M(R)$ is a system of linear forms with
    $K[W]=\operatorname{gr}_M(R)$, which has the property for all $\mu$. Thus the set of
    admissible $\tau$ is a non-empty set of non-negative integers and has a least element. -/)
  (latexEnv := "lemma")]
theorem tau_spec (a : ℕ) :
    ∃ W : Fin (tau R J a) → AssocGraded (maximalIdeal R),
      (∀ i, W i ∈ AssocGraded.homogeneous (maximalIdeal R) 1) ∧
      IsTauSubmodule R J (Submodule.span (R ⧸ maximalIdeal R) (Set.range W)) (mu R J a) := by
  -- a finite family `W` spanning `gr¹_M(R)` has `K[W] = gr_M(R)`, hence the property for all `μ`
  obtain ⟨τ, W, hW⟩ := Submodule.fg_iff_exists_fin_generating_family.mp
    (homogeneous_fg (maximalIdeal R) 1)
  refine Nat.sInf_mem (s := {τ : ℕ | ∃ W : Fin τ → AssocGraded (maximalIdeal R),
    (∀ i, W i ∈ AssocGraded.homogeneous (maximalIdeal R) 1) ∧
    IsTauSubmodule R J (Submodule.span (R ⧸ maximalIdeal R) (Set.range W)) (mu R J a)})
    ⟨τ, W, fun i => hW ▸ Submodule.subset_span ⟨i, rfl⟩, hW.le, fun μ _ ψ _ => ?_⟩
  rw [hW, adjoin_homogeneous_one_eq_top, Algebra.coe_top, Set.inter_univ, Ideal.span_eq]

/-- Minimality of `τ^{(a)}(J)`: any system of `τ` linear forms with the property of Definition 6
up to degree `μ^{(a)}(J)` has `τ ≥ τ^{(a)}(J)`. -/
theorem tau_le {a τ : ℕ} (W : Fin τ → AssocGraded (maximalIdeal R))
    (hW : ∀ i, W i ∈ AssocGraded.homogeneous (maximalIdeal R) 1)
    (hT : IsTauSubmodule R J (Submodule.span (R ⧸ maximalIdeal R) (Set.range W)) (mu R J a)) :
    tau R J a ≤ τ :=
  Nat.sInf_le ⟨W, hW, hT⟩

/-- `μ^{(a)}(J)` is one of the integers which appear in `ν*(J)`, for `1 ≤ a ≤ t(J)`. -/
theorem mu_mem_muSet {a : ℕ} (ha : 1 ≤ a) (hat : a ≤ t R J) : mu R J a ∈ muSet R J := by
  have hf := (muSet_finite R J).1
  have hcard : hf.toFinset.card = t R J := (Set.ncard_eq_toFinset_card _ hf).symm
  exact Nat.nth_mem_of_lt_card (p := (· ∈ muSet R J)) hf (by rw [hcard]; omega)

/-- `ν^{(1)}(J) ≤ ν^{(i)}(J)`: a system for `ν^{(1)}` (the empty system) is padded by zeros to a
system of `i - 1` elements. -/
private theorem nuI_one_le_nuI (i : ℕ+) : nuI R J 1 ≤ nuI R J i := by
  refine iSup₂_le fun ν ⟨φ, hφ⟩ => ?_
  have hbot : Ideal.span (Set.range φ) = ⊥ := by
    rw [Ideal.span_eq_bot]
    rintro _ ⟨j, rfl⟩
    exact absurd j.2 (by simp)
  have hbot' : Ideal.span (Set.range fun _ : Fin ((i : ℕ) - 1) =>
      (0 : AssocGraded (maximalIdeal R))) = ⊥ := by
    rw [Ideal.span_eq_bot]
    rintro _ ⟨j, rfl⟩
    rfl
  refine le_iSup₂_of_le (f := fun (ν : ℕ) (_ : ∃ φ : Fin ((i : ℕ) - 1) →
    AssocGraded (maximalIdeal R), IsNuSystem R J ν ((i : ℕ) - 1) φ) => (ν : ℕ∞)) ν
    ⟨fun _ => 0, fun j => ⟨zero_mem _, 0, zero_mem _⟩, fun μ hμ ψ hψ => ?_⟩ le_rfl
  rw [hbot']
  have := hφ.2 μ hμ ψ hψ
  rwa [hbot] at this

/-- `1 ∉ gr_M(J, R)` for a proper ideal `J`: a homogeneous element of degree `0` of `gr_M(J, R)`
is the class of an element of `J ⊆ M`, hence is `0`. -/
private theorem one_notMem_grIdeal (hJ : J ≠ ⊤) : (1 : AssocGraded (maximalIdeal R)) ∉
    grIdeal (maximalIdeal R) J := by
  intro h1
  have h0 : (1 : AssocGraded (maximalIdeal R)) = AssocGraded.mk (maximalIdeal R) 0 1 (by simp) :=
    rfl
  obtain ⟨b, ⟨hbJ, -⟩, hb, hmk⟩ := (grIdeal_homogeneous_eq (maximalIdeal R) J 0 1
    (by rw [h0]; exact AssocGraded.mk_mem_homogeneous _ _)).mp h1
  have hbM : b ∈ maximalIdeal R ^ (0 + 1) := by rw [zero_add, pow_one]; exact le_maximalIdeal hJ hbJ
  have h2 : AssocGraded.mk (maximalIdeal R) 0 b hb = 0 := (AssocGraded.mk_eq_zero_iff _ hb).mpr hbM
  rw [h2] at hmk
  have h3 := (AssocGraded.mk_eq_zero_iff (maximalIdeal R) (show (1 : R) ∈ maximalIdeal R ^ 0 by simp)).mp
    hmk.symm
  rw [zero_add, pow_one] at h3
  exact (maximalIdeal.isMaximal R).ne_top (Ideal.eq_top_of_isUnit_mem _ h3 isUnit_one)

/-- The `K`-subalgebra of `gr_M(R)` generated by the empty system is `K` (p. 221: "The empty
system generates the `K`-subalgebra `K` of `gr_M(R)`"). -/
theorem adjoin_span_range_elim_zero :
    Algebra.adjoin (R ⧸ maximalIdeal R)
      ((Submodule.span (R ⧸ maximalIdeal R)
        (Set.range (Fin.elim0 : Fin 0 → AssocGraded (maximalIdeal R))) : Submodule _ _) :
          Set (AssocGraded (maximalIdeal R))) = ⊥ := by
  refine le_antisymm (Algebra.adjoin_le ?_) bot_le
  rw [Set.range_eq_empty, Submodule.span_empty]
  rintro x (rfl : x = 0)
  exact zero_mem _

/-- Definition 6, p. 221, parenthetical remark: "We have `τ_a > 0` for all `a` unless `J = R`."

Gap in the paper filled: the paper states this without argument.  If `τ_a = 0` the empty system
has the property of Definition 6 up to `μ_a`, i.e. `gr^μ_M(J, R) = gr^μ_M(R) ∩ (gr_M(J, R) ∩ K) gr_M(R)`
for `μ ≤ μ_a`.  For `J ≠ R` one has `gr_M(J, R) ∩ K = 0` (a non-zero element of `K` is a unit and
`1 ∉ gr_M(J, R)`), so `gr^μ_M(J, R) = 0` for all `μ ≤ μ_a`.  But `μ_1 = ν^{(1)}(J) = ν_M(J) ≤ μ_a`
and `gr^{ν_M(J)}_M(J, R)` contains the initial form of an element of order `ν_M(J)`, which is
non-zero.  (For `J = (0)` the statement is vacuous: `t = 0`.) -/
@[blueprint "lem:III.6-tau-pos"
  (statement := /-- Let $R$ be a regular local ring and $J\ne R$ an ideal in $R$. Then
    $\tau^{(a)}(J)>0$ for $1\le a\le t(J)$. (Definition 6, p.~221, parenthetical remark.) -/)
  (proof := /-- (The paper states this without argument.) Suppose $\tau_a=0$. The empty system
    generates the $K$-subalgebra $K$ of $\operatorname{gr}_M(R)$ and the property of
    \cref{def:III.6} says $\operatorname{gr}^\mu_M(J,R)=\operatorname{gr}^\mu_M(R)\cap
    (\operatorname{gr}_M(J,R)\cap K)\operatorname{gr}_M(R)$ for $\mu\le\mu_a$. Since $J\subseteq M$,
    $1\notin\operatorname{gr}_M(J,R)$ (a homogeneous element of degree $0$ of
    $\operatorname{gr}_M(J,R)$ is the class of an element of $J\subseteq M$, hence zero), and a
    non-zero element of $K$ is a unit; so $\operatorname{gr}_M(J,R)\cap K=0$ and
    $\operatorname{gr}^\mu_M(J,R)=0$ for all $\mu\le\mu_a$. But $\mu_1=\nu^{(1)}(J)=\nu_M(J)$
    is $\le\mu_a$ ($\nu^{(i)}(J)$ is non-decreasing in $i$), and for $f\in J$ with
    $\nu_M(f)=\nu_M(J)<\infty$ the initial form of $f$ is a non-zero element of
    $\operatorname{gr}^{\nu_M(J)}_M(J,R)$. Contradiction. -/)
  (latexEnv := "lemma")]
theorem tau_pos (hJ : J ≠ ⊤) {a : ℕ} (ha : 1 ≤ a) (hat : a ≤ t R J) : 0 < tau R J a := by
  by_contra h0
  have h0' : tau R J a = 0 := Nat.eq_zero_of_not_pos h0
  let _ : Field (R ⧸ maximalIdeal R) := Ideal.Quotient.field _
  obtain ⟨W, -, hW⟩ := tau_spec R J a
  have hspan : Submodule.span (R ⧸ maximalIdeal R) (Set.range W) = ⊥ := by
    rw [Submodule.span_eq_bot]
    rintro _ ⟨i, rfl⟩
    exact absurd (lt_of_lt_of_eq i.2 h0') (Nat.not_lt_zero _)
  rw [hspan] at hW
  -- `ν^{(1)}(J) = ν_M(J) ≤ μ_a`, and `ν_M(J) = ν_M(f)` for some `f ∈ J`
  obtain ⟨i, hi⟩ := mu_mem_muSet R J ha hat
  have hν : nuI R J 1 ≤ (mu R J a : ℕ∞) := by
    rw [← hi]
    exact nuI_one_le_nuI R J i
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp (ne_top_of_le_ne_top (ENat.natCast_ne_top _) hν)
  have hnle : n ≤ mu R J a := by
    rw [← hn] at hν
    exact_mod_cast hν
  have hinf := (nuI_one_eq_nu_and_nuI_two_and_nuI_le_nuParen R J).1.1
  obtain ⟨f, hfJ, hfn⟩ : ∃ f ∈ J, Ideal.ordElem (maximalIdeal R) f = n := by
    have hlt : (⨅ f ∈ J, Ideal.ordElem (maximalIdeal R) f) < ((n + 1 : ℕ) : ℕ∞) := by
      rw [← hinf, ← hn]
      exact_mod_cast Nat.lt_succ_self n
    obtain ⟨f, hf⟩ := iInf_lt_iff.mp hlt
    obtain ⟨hfJ, hf'⟩ := iInf_lt_iff.mp hf
    obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.mp (ne_top_of_lt hf')
    rw [← hk] at hf'
    have hkn : k ≤ n := Nat.lt_succ_iff.mp (by exact_mod_cast hf')
    have hnk : (n : ℕ∞) ≤ Ideal.ordElem (maximalIdeal R) f := by
      rw [hn, hinf]
      exact iInf₂_le f hfJ
    refine ⟨f, hfJ, ?_⟩
    rw [← hk] at hnk ⊢
    exact_mod_cast le_antisymm hkn (by exact_mod_cast hnk)
  have hfM : f ∈ maximalIdeal R ^ n := Ideal.mem_pow_of_ordElem hfn
  have hψJ : AssocGraded.mk (maximalIdeal R) n f hfM ∈ grIdeal (maximalIdeal R) J :=
    mk_mem_grIdeal _ hfJ hfM
  have hψ := (hW.2 n hnle _ (AssocGraded.mk_mem_homogeneous _ hfM)).mp hψJ
  -- `gr_M(J, R) ∩ K = 0`
  have hbot : Ideal.span ((grIdeal (maximalIdeal R) J : Set (AssocGraded (maximalIdeal R))) ∩
      (Algebra.adjoin (R ⧸ maximalIdeal R) ((⊥ : Submodule (R ⧸ maximalIdeal R)
        (AssocGraded (maximalIdeal R))) : Set (AssocGraded (maximalIdeal R))) :
          Set (AssocGraded (maximalIdeal R)))) = ⊥ := by
    rw [Ideal.span_eq_bot]
    rintro x ⟨hxJ, hxA⟩
    have hxbot : x ∈ (⊥ : Subalgebra (R ⧸ maximalIdeal R) (AssocGraded (maximalIdeal R))) :=
      Algebra.adjoin_le (by rintro y (rfl : y = 0); exact zero_mem _) hxA
    obtain ⟨c, rfl⟩ := Algebra.mem_bot.mp hxbot
    by_cases hc : c = 0
    · rw [hc, map_zero]
    · exact absurd (Ideal.eq_top_of_isUnit_mem _ hxJ
        ((isUnit_iff_ne_zero.mpr hc).map _) ▸ Submodule.mem_top) (one_notMem_grIdeal R J hJ)
  rw [hbot, Ideal.mem_bot, AssocGraded.mk_eq_zero_iff] at hψ
  have := Ideal.le_ordElem hψ
  rw [hfn] at this
  have : n + 1 ≤ n := by exact_mod_cast this
  omega

/-! #### The unit ideal (p. 221): "If `J = R`, then `μ*(J) = (μ₁)` with `μ₁ = 0`, and `τ₁ = 0`." -/

private theorem ordElem_one : Ideal.ordElem (maximalIdeal R) (1 : R) = 0 :=
  le_antisymm (Ideal.ordElem_le_of_notMem (m := 0) (by simp)) (by simp)

private theorem initialForm_one : initialForm (maximalIdeal R) (1 : R) = 1 := by
  have h0 := ordElem_one R
  unfold initialForm
  split_ifs with h
  · rw [h0] at h
    exact absurd h ENat.zero_ne_top
  · simp only [h0, ENat.toNat_zero]
    rfl

private theorem grIdeal_top : grIdeal (maximalIdeal R) (⊤ : Ideal R) = ⊤ :=
  (Ideal.eq_top_iff_one _).mpr (Ideal.subset_span ⟨1, Submodule.mem_top, initialForm_one R⟩)

private theorem one_mem_homogeneous_zero :
    (1 : AssocGraded (maximalIdeal R)) ∈ AssocGraded.homogeneous (maximalIdeal R) 0 := by
  have : (1 : AssocGraded (maximalIdeal R)) = AssocGraded.mk _ 0 1 (by simp) := rfl
  rw [this]
  exact AssocGraded.mk_mem_homogeneous _ _

/-- `ν^{(1)}(R) = 0`. -/
private theorem nuI_top_one : nuI R (⊤ : Ideal R) 1 = 0 := by
  rw [(nuI_one_eq_nu_and_nuI_two_and_nuI_le_nuParen R ⊤).1.1]
  exact le_antisymm ((iInf₂_le 1 Submodule.mem_top).trans (ordElem_one R).le) (by simp)

/-- `ν^{(i)}(R) = ∞` for `i ≥ 2`: the system `(1, …, 1)` generates `gr_M(R) = gr_M(R, R)`. -/
private theorem nuI_top_of_ne_one {i : ℕ+} (hi : i ≠ 1) : nuI R (⊤ : Ideal R) i = ⊤ := by
  have hi' : 1 ≤ (i : ℕ) - 1 := by
    have h2 : ((1 : ℕ+) : ℕ) < i :=
      PNat.coe_lt_coe _ _ |>.mpr (lt_of_le_of_ne (one_le (a := i)) (Ne.symm hi))
    rw [PNat.one_coe] at h2
    omega
  have hsys : ∀ ν : ℕ, IsNuSystem R ⊤ ν ((i : ℕ) - 1) fun _ => 1 := by
    intro ν
    refine ⟨fun _ => ⟨by rw [grIdeal_top]; exact Submodule.mem_top,
      0, one_mem_homogeneous_zero R⟩, fun μ _ ψ _ => ?_⟩
    have hspan : Ideal.span (Set.range fun _ : Fin ((i : ℕ) - 1) =>
        (1 : AssocGraded (maximalIdeal R))) = ⊤ :=
      (Ideal.eq_top_iff_one _).mpr (Ideal.subset_span ⟨⟨0, hi'⟩, rfl⟩)
    rw [hspan, grIdeal_top]
  refine ENat.eq_top_iff_forall_ge.mpr fun m => ?_
  exact le_iSup₂_of_le (f := fun (ν : ℕ) (_ : ∃ φ : Fin ((i : ℕ) - 1) → AssocGraded
    (maximalIdeal R), IsNuSystem R ⊤ ν ((i : ℕ) - 1) φ) => (ν : ℕ∞)) m ⟨_, hsys m⟩ le_rfl

/-- Definition 6, p. 221: for `J = R`, the only integer which appears in `ν*(J) = (0, ∞, ∞, …)`
is `0`, i.e. `μ*(J) = (μ₁)` with `μ₁ = 0`. -/
theorem muSet_of_eq_top (hJ : J = ⊤) : muSet R J = {0} := by
  subst hJ
  ext μ
  simp only [muSet, Set.mem_ofPred_eq, Set.mem_singleton_iff]
  constructor
  · rintro ⟨i, hi⟩
    by_cases h1 : i = 1
    · rw [h1, nuI_top_one] at hi
      exact_mod_cast hi.symm
    · rw [nuI_top_of_ne_one R h1] at hi
      exact absurd hi.symm (ENat.natCast_ne_top μ)
  · rintro rfl
    exact ⟨1, by rw [nuI_top_one]; rfl⟩

/-- Definition 6, p. 221: "If `J = R`, then `μ*(J) = (μ₁)` with `μ₁ = 0`, and `τ₁ = 0`.  The empty
system generates the `K`-subalgebra `K` of `gr_M(R)`."  (`t(R) = 1`, `μ^{(1)}(R) = 0`,
`τ^{(1)}(R) = 0`; the first is `muSet_of_eq_top`, the last is the existence of the empty system with
the property of Definition 6, as `gr_M(R, R) = gr_M(R)` contains `1 ∈ K`.)

Gap in the paper filled: the paper states this parenthetical remark without proof. -/
@[blueprint "lem:III.6-unit-ideal"
  (statement := /-- Let $R$ be a regular local ring. For $J=R$ we have $\mu^*(J)=(\mu_1)$ with
    $\mu_1=0$ (so $t(J)=1$), and $\tau^{(1)}(J)=0$. (Definition 6, p.~221, parenthetical
    remark.) -/)
  (proof := /-- (The paper states this without proof.) $\nu^{(1)}(R)=\nu_M(R)=0$, and for
    $i\ge2$ the system $(1,\dots,1)$ of $i-1$ elements generates $\operatorname{gr}_M(R)=
    \operatorname{gr}_M(R,R)$, so $\nu^{(i)}(R)=\infty$; hence the only integer which appears in
    $\nu^*(R)$ is $0$, $t=1$ and $\mu_1=0$. The empty system generates the $K$-subalgebra $K$
    of $\operatorname{gr}_M(R)$, and $\operatorname{gr}_M(R,R)\cap K\ni1$ generates the unit
    ideal of $\operatorname{gr}_M(R)$, so the property of \cref{def:III.6} holds for it for all
    $\mu$; thus $\tau^{(1)}(R)=0$. -/)
  (latexEnv := "lemma")]
theorem tau_of_eq_top (hJ : J = ⊤) : muSet R J = {0} ∧ t R J = 1 ∧ mu R J 1 = 0 ∧ tau R J 1 = 0 := by
  have hμ := muSet_of_eq_top R J hJ
  refine ⟨hμ, ?_, ?_, ?_⟩
  · rw [t, hμ, Set.ncard_singleton]
  · rw [mu, hμ]
    exact Nat.nth_zero_of_zero (by simp)
  · subst hJ
    refine Nat.sInf_eq_zero.mpr (Or.inl ?_)
    refine ⟨Fin.elim0, fun i => i.elim0, ?_, fun μ _ ψ _ => ?_⟩
    · exact Submodule.span_le.mpr (by rintro _ ⟨i, -⟩; exact i.elim0)
    · have hspan : Ideal.span ((grIdeal (maximalIdeal R) ⊤ : Set (AssocGraded (maximalIdeal R))) ∩
          (Algebra.adjoin (R ⧸ maximalIdeal R) (Submodule.span (R ⧸ maximalIdeal R)
            (Set.range (Fin.elim0 : Fin 0 → AssocGraded (maximalIdeal R))) :
              Set (AssocGraded (maximalIdeal R))) : Set (AssocGraded (maximalIdeal R)))) = ⊤ :=
        (Ideal.eq_top_iff_one _).mpr (Ideal.subset_span ⟨by rw [grIdeal_top]; trivial,
          Subalgebra.one_mem _⟩)
      rw [hspan, grIdeal_top]

end Definition6

/-! ### Lemma 10 (pp. 221–222) -/

section Lemma10

variable (K : Type u) [Field K] (n : ℕ)

/-- The property of Definition 6 (\cref{def:III.6-property}) for a polynomial ring
`G = K[X₁, …, X_n]` "graded in a natural way" (`MvPolynomial.homogeneousSubmodule`), a
homogeneous ideal `I` of `G`, a `K`-submodule `T ⊆ G₁` and a bound `μ₀`:
"`I_μ = G_μ ∩ (I ∩ K[T]) G` for all `μ ≤ μ₀`", where `K[T]` is the `K`-subalgebra of `G`
generated by the elements of `T` (Lemma 10, p. 221). -/
def IsTauSubmoduleMv (I : Ideal (MvPolynomial (Fin n) K))
    (T : Submodule K (MvPolynomial (Fin n) K)) (μ₀ : ℕ) : Prop :=
  T ≤ MvPolynomial.homogeneousSubmodule (Fin n) K 1 ∧
  ∀ μ ≤ μ₀, ∀ ψ ∈ MvPolynomial.homogeneousSubmodule (Fin n) K μ,
    (ψ ∈ I ↔ ψ ∈ Ideal.span ((I : Set (MvPolynomial (Fin n) K)) ∩
      (Algebra.adjoin K (T : Set (MvPolynomial (Fin n) K)) : Set (MvPolynomial (Fin n) K))))

attribute [local instance] MvPolynomial.gradedAlgebra

open MvPolynomial in
/-- The homogeneous component of degree `d` of `a x` with `a` homogeneous of degree `i`. -/
private theorem homogeneousComponent_mul_of_mem {K σ : Type*} [Field K]
    {a : MvPolynomial σ K} {i : ℕ} (ha : a ∈ homogeneousSubmodule σ K i)
    (x : MvPolynomial σ K) (d : ℕ) :
    homogeneousComponent d (a * x) =
      if i ≤ d then a * homogeneousComponent (d - i) x else 0 := by
  have h := DirectSum.coe_decompose_mul_of_left_mem (𝒜 := homogeneousSubmodule σ K) (b := x) d ha
  rw [← decomposition.decompose'_apply, ← decomposition.decompose'_apply]
  exact h

open MvPolynomial in
/-- If a set `X` of polynomials is closed under taking homogeneous components, then the
homogeneous component of degree `μ` of an element of the ideal `(X)` lies in the ideal generated
by the homogeneous elements of `X` of degree `≤ μ`. -/
private theorem homogeneousComponent_mem_span {K σ : Type*} [Field K]
    (X : Set (MvPolynomial σ K)) (hX : ∀ x ∈ X, ∀ d, homogeneousComponent d x ∈ X)
    {f : MvPolynomial σ K} (hf : f ∈ Ideal.span X) (μ : ℕ) :
    homogeneousComponent μ f ∈
      Ideal.span {x | x ∈ X ∧ ∃ d ≤ μ, x ∈ homogeneousSubmodule σ K d} := by
  induction hf using Submodule.span_induction generalizing μ with
  | mem x hx => exact Ideal.subset_span ⟨hX x hx μ, μ, le_rfl, homogeneousComponent_mem μ x⟩
  | zero => rw [map_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact add_mem (hx μ) (hy μ)
  | smul c x _ hx =>
    rw [smul_eq_mul, ← sum_homogeneousComponent c, Finset.sum_mul, map_sum]
    refine sum_mem fun i _ => ?_
    rw [homogeneousComponent_mul_of_mem (homogeneousComponent_mem i c)]
    split_ifs
    · refine Ideal.mul_mem_left _ _ (Ideal.span_mono ?_ (hx (μ - i)))
      rintro y ⟨hy, d, hd, hyd⟩
      exact ⟨hy, d, hd.trans (Nat.sub_le _ _), hyd⟩
    · exact zero_mem _

open MvPolynomial in
/-- The `K`-subalgebra generated by linear forms is closed under taking homogeneous
components. -/
private theorem homogeneousComponent_mem_adjoin {K σ : Type*} [Field K]
    {S : Submodule K (MvPolynomial σ K)} (hS : S ≤ homogeneousSubmodule σ K 1)
    {g : MvPolynomial σ K} (hg : g ∈ Algebra.adjoin K (S : Set (MvPolynomial σ K))) (d : ℕ) :
    homogeneousComponent d g ∈ Algebra.adjoin K (S : Set (MvPolynomial σ K)) := by
  induction hg using Algebra.adjoin_induction generalizing d with
  | mem x hx =>
    rw [homogeneousComponent_of_mem (hS hx)]
    split_ifs
    · exact Algebra.subset_adjoin hx
    · exact zero_mem _
  | algebraMap r =>
    rw [algebraMap_eq, homogeneousComponent_of_mem (m := d) (n := 0) (isHomogeneous_C _ r)]
    split_ifs
    · exact Subalgebra.algebraMap_mem _ r
    · exact zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact add_mem (hx d) (hy d)
  | mul x y _ _ hx hy =>
    rw [← sum_homogeneousComponent x, Finset.sum_mul, map_sum]
    refine sum_mem fun i _ => ?_
    rw [homogeneousComponent_mul_of_mem (homogeneousComponent_mem i x)]
    split_ifs
    · exact Subalgebra.mul_mem _ (hx i) (hy _)
    · exact zero_mem _

open MvPolynomial in
/-- If `S` has the property of Definition 6 up to `μ̄`, then every element of `I_μ`, `μ ≤ μ̄`,
lies in the ideal generated by the homogeneous elements of `I ∩ K[S]` of degree `≤ μ̄`. -/
private theorem mem_span_homogeneous {I : Ideal (MvPolynomial (Fin n) K)}
    (hI : I.IsHomogeneous (homogeneousSubmodule (Fin n) K))
    {S : Submodule K (MvPolynomial (Fin n) K)} {μbar : ℕ} (hS : IsTauSubmoduleMv K n I S μbar)
    {μ : ℕ} (hμ : μ ≤ μbar)
    {ψ : MvPolynomial (Fin n) K} (hψ : ψ ∈ homogeneousSubmodule (Fin n) K μ) (hψI : ψ ∈ I) :
    ψ ∈ Ideal.span {g | g ∈ (I : Set (MvPolynomial (Fin n) K)) ∩
      (Algebra.adjoin K (S : Set (MvPolynomial (Fin n) K)) : Set (MvPolynomial (Fin n) K)) ∧
        ∃ d ≤ μbar, g ∈ homogeneousSubmodule (Fin n) K d} := by
  have h := homogeneousComponent_mem_span ((I : Set (MvPolynomial (Fin n) K)) ∩
    (Algebra.adjoin K (S : Set (MvPolynomial (Fin n) K)) : Set (MvPolynomial (Fin n) K)))
    (fun x hx d =>
    ⟨homogeneousComponent_mem_of_mem hI hx.1 d, homogeneousComponent_mem_adjoin hS.1 hx.2 d⟩)
    ((hS.2 μ hμ ψ hψ).mp hψI) μ
  rw [homogeneousComponent_eq_self hψ] at h
  refine Ideal.span_mono ?_ h
  rintro y ⟨hy, d, hd, hyd⟩
  exact ⟨hy, d, hd.trans hμ, hyd⟩

open MvPolynomial in
/-- Enlarging a submodule with the property of Definition 6 (inside `G₁`) preserves the property:
`K[T] ⊆ K[T']` gives `(I ∩ K[T]) G ⊆ (I ∩ K[T']) G ⊆ I`. -/
private theorem isTauSubmoduleMv_mono {I : Ideal (MvPolynomial (Fin n) K)}
    {S S' : Submodule K (MvPolynomial (Fin n) K)} {μbar : ℕ}
    (hS : IsTauSubmoduleMv K n I S μbar) (hSS' : S ≤ S')
    (hS' : S' ≤ homogeneousSubmodule (Fin n) K 1) : IsTauSubmoduleMv K n I S' μbar := by
  refine ⟨hS', fun μ hμ ψ hψ => ⟨fun h => ?_, fun h => (Ideal.span_le.mpr fun x hx => hx.1) h⟩⟩
  exact Ideal.span_mono (Set.inter_subset_inter_right _
    (SetLike.coe_subset_coe.mpr (Algebra.adjoin_mono hSS'))) ((hS.2 μ hμ ψ hψ).mp h)

open MvPolynomial in
/-- Lemma 10, p. 222: "We may assume that `T` and `T'` generate the whole `K`-module `G₁`.  (If
otherwise, enlarge `T'` in such a way that `T ∩ T'` remains the same, and `T + T' = G₁`.)" -/
private theorem exists_enlarge {T T' : Submodule K (MvPolynomial (Fin n) K)}
    (hT : T ≤ homogeneousSubmodule (Fin n) K 1) (hT' : T' ≤ homogeneousSubmodule (Fin n) K 1) :
    ∃ T₁ : Submodule K (MvPolynomial (Fin n) K), T' ≤ T₁ ∧
      T₁ ≤ homogeneousSubmodule (Fin n) K 1 ∧ T ⊓ T₁ = T ⊓ T' ∧
      T ⊔ T₁ = homogeneousSubmodule (Fin n) K 1 := by
  -- `T₁ = (T' + C) ∩ G₁` for a complement `C` of `T + T'` in `G`
  obtain ⟨C, hC⟩ := Submodule.exists_isCompl (T ⊔ T')
  refine ⟨(T' ⊔ C) ⊓ homogeneousSubmodule (Fin n) K 1, le_inf le_sup_left hT', inf_le_right,
    le_antisymm ?_ (inf_le_inf_left T (le_inf le_sup_left hT')), le_antisymm ?_ ?_⟩
  · rintro x ⟨hxT, hx, -⟩
    obtain ⟨t', ht', c, hc, rfl⟩ := Submodule.mem_sup.mp hx
    have hc' : c ∈ T ⊔ T' := by
      have : c = (t' + c) - t' := by abel
      rw [this]
      exact sub_mem (Submodule.mem_sup_left hxT) (Submodule.mem_sup_right ht')
    have hc0 := (Submodule.disjoint_def.mp hC.disjoint) c hc' hc
    subst hc0
    rw [add_zero] at hxT ⊢
    exact ⟨hxT, ht'⟩
  · exact sup_le hT inf_le_right
  · intro g hg
    have hg' : g ∈ (T ⊔ T') ⊔ C := by rw [hC.sup_eq_top]; exact Submodule.mem_top
    obtain ⟨a, ha, c, hc, rfl⟩ := Submodule.mem_sup.mp hg'
    obtain ⟨t, ht, t', ht', rfl⟩ := Submodule.mem_sup.mp ha
    have hsum : t + t' ∈ homogeneousSubmodule (Fin n) K 1 := add_mem (hT ht) (hT' ht')
    have hc1 : c ∈ homogeneousSubmodule (Fin n) K 1 := by
      have : c = (t + t' + c) - (t + t') := by abel
      rw [this]
      exact sub_mem hg hsum
    refine Submodule.mem_sup.mpr ⟨t, ht, t' + c, ⟨Submodule.mem_sup.mpr ⟨t', ht', c, hc, rfl⟩,
      add_mem (hT' ht') hc1⟩, by abel⟩

open MvPolynomial in
/-- Lemma 10, p. 222: "Let `T''` be the `K`-submodule of `T'` such that `G₁` is a direct sum of
`T` and `T''`." (A complement of `T ∩ T'` in `T'`, for `T + T' = G₁`.)  Moreover `T'` is the sum of
`T ∩ T'` and `T''`. -/
private theorem exists_complement_of_sup_eq {T T' : Submodule K (MvPolynomial (Fin n) K)}
    (hT : T ≤ homogeneousSubmodule (Fin n) K 1)
    (hsup : T ⊔ T' = homogeneousSubmodule (Fin n) K 1) :
    ∃ T'' : Submodule K (MvPolynomial (Fin n) K), T'' ≤ T' ∧ Disjoint T T'' ∧
      T ⊔ T'' = homogeneousSubmodule (Fin n) K 1 ∧ ∀ t ∈ T', ∃ a ∈ T ⊓ T', ∃ d ∈ T'', a + d = t := by
  obtain ⟨D₀, hD₀⟩ := Submodule.exists_isCompl ((T ⊓ T').comap T'.subtype)
  have hsplit : ∀ t ∈ T', ∃ a ∈ T ⊓ T', ∃ d ∈ D₀.map T'.subtype, a + d = t := by
    intro t ht
    have hmem : (⟨t, ht⟩ : T') ∈ (T ⊓ T').comap T'.subtype ⊔ D₀ := by
      rw [hD₀.sup_eq_top]; exact Submodule.mem_top
    obtain ⟨a, ha, d, hd, had⟩ := Submodule.mem_sup.mp hmem
    exact ⟨a, ha, d, Submodule.mem_map_of_mem hd, by simpa using congrArg Subtype.val had⟩
  have hdisj : Disjoint T (D₀.map T'.subtype) := by
    rw [Submodule.disjoint_def]
    intro x hxT hxD
    obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.mp hxD
    have hy' : y ∈ (T ⊓ T').comap T'.subtype := ⟨hxT, y.2⟩
    rw [(Submodule.disjoint_def.mp hD₀.disjoint) y hy' hy]
    rfl
  refine ⟨D₀.map T'.subtype, Submodule.map_subtype_le _ _, hdisj, le_antisymm ?_ ?_, hsplit⟩
  · exact sup_le hT ((Submodule.map_subtype_le _ _).trans (le_sup_right.trans hsup.le))
  · rw [← hsup]
    refine sup_le le_sup_left fun t ht => ?_
    obtain ⟨a, ha, d, hd, rfl⟩ := hsplit t ht
    exact add_mem (Submodule.mem_sup_left ha.1) (Submodule.mem_sup_right hd)

open MvPolynomial in
/-- Lemma 10, p. 222: "Let `ρ` be the natural homomorphism `G → G/(T'')G` where `(T'')G` is the
ideal in `G` generated by the elements of `T''`.  Then `ρ` induces an isomorphism of graded
`K`-algebras `K[T] → G/(T'')G`.  Therefore, we may view `ρ` as an endomorphism of `G` which maps
`G` onto `K[T]` in a natural way."

Here `G₁ = T ⊕ T''`.  The endomorphism is `ρ = aeval (π ∘ X)` for the projection `π` of `G₁`
onto `T` along `T''`; it is graded, has kernel `(T'')G` (so it is the natural homomorphism
`G → G/(T'')G`), maps `G` into `K[T]` and is the identity on `K[T]`, and the induced homomorphism
`K[T] → G/(T'')G` is bijective.  (The paper states the isomorphism without proof: gap filled.) -/
private theorem exists_retraction {T T'' : Submodule K (MvPolynomial (Fin n) K)}
    (hT : T ≤ homogeneousSubmodule (Fin n) K 1) (hT'' : T'' ≤ homogeneousSubmodule (Fin n) K 1)
    (hdisj : Disjoint T T'') (hsup : T ⊔ T'' = homogeneousSubmodule (Fin n) K 1) :
    ∃ ρ : MvPolynomial (Fin n) K →ₐ[K] MvPolynomial (Fin n) K,
      RingHom.ker ρ = Ideal.span (T'' : Set (MvPolynomial (Fin n) K)) ∧
      (∀ g, ρ g ∈ Algebra.adjoin K (T : Set (MvPolynomial (Fin n) K))) ∧
      (∀ g ∈ Algebra.adjoin K (T : Set (MvPolynomial (Fin n) K)), ρ g = g) ∧
      Function.Bijective ((Ideal.Quotient.mkₐ K (Ideal.span (T'' : Set (MvPolynomial (Fin n) K)))).comp
        (Algebra.adjoin K (T : Set (MvPolynomial (Fin n) K))).val) ∧
      ∀ d, ∀ g ∈ homogeneousSubmodule (Fin n) K d, ρ g ∈ homogeneousSubmodule (Fin n) K d := by
  -- the projection `π` of `G` onto `T` along `T'' ⊕ C`, `C` a complement of `G₁` in `G`
  obtain ⟨C, hC⟩ := Submodule.exists_isCompl (homogeneousSubmodule (Fin n) K 1)
  have hcompl : IsCompl T (T'' ⊔ C) := by
    refine ⟨?_, codisjoint_iff.mpr (by rw [← sup_assoc, hsup]; exact hC.sup_eq_top)⟩
    rw [Submodule.disjoint_def]
    intro x hxT hx
    obtain ⟨d, hd, c, hc, rfl⟩ := Submodule.mem_sup.mp hx
    have hc1 : c ∈ homogeneousSubmodule (Fin n) K 1 := by
      have : c = (d + c) - d := by abel
      rw [this]
      exact sub_mem (hT hxT) (hT'' hd)
    rw [(Submodule.disjoint_def.mp hC.disjoint) c hc1 hc, add_zero] at hxT ⊢
    exact (Submodule.disjoint_def.mp hdisj) d hxT hd
  set π : MvPolynomial (Fin n) K →ₗ[K] MvPolynomial (Fin n) K := T.projection (T'' ⊔ C) hcompl
    with hπ
  have hπT : ∀ t ∈ T, π t = t := fun t ht => Submodule.projection_apply_of_mem_left hcompl ht
  have hπT'' : ∀ t ∈ T'', π t = 0 := fun t ht =>
    Submodule.projection_apply_of_mem_right hcompl (Submodule.mem_sup_left ht)
  have hπmem : ∀ x, π x ∈ T := fun x => Submodule.projection_apply_mem hcompl x
  have hsubπ : ∀ x ∈ homogeneousSubmodule (Fin n) K 1, x - π x ∈ T'' := by
    intro x hx
    rw [← hsup] at hx
    obtain ⟨a, ha, d, hd, rfl⟩ := Submodule.mem_sup.mp hx
    rw [map_add, hπT a ha, hπT'' d hd, add_zero, add_sub_cancel_left]
    exact hd
  obtain ⟨ρ, hρeq⟩ : ∃ ρ : MvPolynomial (Fin n) K →ₐ[K] MvPolynomial (Fin n) K,
      ρ = MvPolynomial.aeval fun i => π (MvPolynomial.X i) := ⟨_, rfl⟩
  have hρX : ∀ i, ρ (MvPolynomial.X i) = π (MvPolynomial.X i) := fun i => by
    rw [hρeq, MvPolynomial.aeval_X]
  have hρ1 : ∀ t ∈ homogeneousSubmodule (Fin n) K 1, ρ t = π t := by
    intro t ht
    rw [homogeneousSubmodule_one_eq_span_X] at ht
    induction ht using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      exact hρX i
    | zero => rw [map_zero, map_zero]
    | add x y _ _ hx hy => rw [map_add, map_add, hx, hy]
    | smul c x _ hx => rw [map_smul, map_smul, hx]
  have hρT'' : ∀ t ∈ T'', ρ t = 0 := fun t ht => by rw [hρ1 t (hT'' ht), hπT'' t ht]
  have hρT : ∀ g ∈ Algebra.adjoin K (T : Set (MvPolynomial (Fin n) K)), ρ g = g := by
    intro g hg
    induction hg using Algebra.adjoin_induction with
    | mem x hx => rw [hρ1 x (hT hx), hπT x hx]
    | algebraMap r => exact ρ.commutes r
    | add x y _ _ hx hy => rw [map_add, hx, hy]
    | mul x y _ _ hx hy => rw [map_mul, hx, hy]
  have hρrange : ∀ g, ρ g ∈ Algebra.adjoin K (T : Set (MvPolynomial (Fin n) K)) := by
    intro g
    induction g using MvPolynomial.induction_on with
    | C a => rw [← MvPolynomial.algebraMap_eq, ρ.commutes]; exact Subalgebra.algebraMap_mem _ a
    | add p q hp hq => rw [map_add]; exact add_mem hp hq
    | mul_X p i hp =>
      rw [map_mul, hρX]
      exact Subalgebra.mul_mem _ hp (Algebra.subset_adjoin (hπmem _))
  -- `ρ` is the identity modulo `(T'')G`
  have hcong : ∀ g, g - ρ g ∈ Ideal.span (T'' : Set (MvPolynomial (Fin n) K)) := by
    intro g
    induction g using MvPolynomial.induction_on with
    | C a => rw [← MvPolynomial.algebraMap_eq, ρ.commutes, sub_self]; exact zero_mem _
    | add p q hp hq =>
      rw [map_add, show p + q - (ρ p + ρ q) = (p - ρ p) + (q - ρ q) by abel]
      exact add_mem hp hq
    | mul_X p i hp =>
      rw [map_mul, hρX,
        show p * MvPolynomial.X i - ρ p * π (MvPolynomial.X i) =
          (p - ρ p) * MvPolynomial.X i + ρ p * (MvPolynomial.X i - π (MvPolynomial.X i)) by ring]
      exact add_mem (Ideal.mul_mem_right _ _ hp) (Ideal.mul_mem_left _ _ (Ideal.subset_span
        (hsubπ _ ((mem_homogeneousSubmodule 1 _).mpr (isHomogeneous_X K i)))))
  have hker : RingHom.ker ρ = Ideal.span (T'' : Set (MvPolynomial (Fin n) K)) := by
    refine le_antisymm (fun f hf => ?_) (Ideal.span_le.mpr fun t ht => ?_)
    · have := hcong f
      rwa [RingHom.mem_ker.mp hf, sub_zero] at this
    · exact RingHom.mem_ker.mpr (hρT'' t ht)
  refine ⟨ρ, hker, hρrange, hρT, ⟨?_, ?_⟩, fun d g hg => ?_⟩
  · -- injective: `K[T] ∩ (T'')G = 0`
    refine (injective_iff_map_eq_zero _).mpr fun x hx => ?_
    have hx' : (x : MvPolynomial (Fin n) K) ∈ Ideal.span (T'' : Set (MvPolynomial (Fin n) K)) :=
      Ideal.Quotient.eq_zero_iff_mem.mp hx
    rw [← hker] at hx'
    exact Subtype.ext (by rw [← hρT x x.2]; exact RingHom.mem_ker.mp hx')
  · -- surjective: `G = K[T] + (T'')G`
    intro y
    obtain ⟨g, rfl⟩ := Ideal.Quotient.mk_surjective y
    refine ⟨⟨ρ g, hρrange g⟩, ?_⟩
    show Ideal.Quotient.mk _ (ρ g) = Ideal.Quotient.mk _ g
    rw [Ideal.Quotient.eq, ← neg_sub]
    exact neg_mem (hcong g)
  · -- graded
    have h := ((mem_homogeneousSubmodule d g).mp hg).aeval
      (fun i => π (MvPolynomial.X i)) (n := 1) fun i =>
        (mem_homogeneousSubmodule 1 _).mp (hT (hπmem _))
    rw [one_mul] at h
    rw [hρeq]
    exact (mem_homogeneousSubmodule d _).mpr h

open MvPolynomial in
/-- Lemma 10, pp. 221-222, for `T + T' = G₁` (the case to which the proof reduces).  The steps are
the printed ones, in the printed order:

* `T''` and `ρ`: "Let `T''` be the `K`-submodule of `T'` such that `G₁` is a direct sum of `T` and
  `T''`.  Let `ρ` be the natural homomorphism `G → G/(T'')G` [...] we may view `ρ` as an
  endomorphism of `G` which maps `G` onto `K[T]` in a natural way" (`exists_complement_of_sup_eq`,
  `exists_retraction`);
* (a) "Now, we have `I_μ = G_μ ∩ (I ∩ K[T])G` for all `μ ≤ μ̄` and therefore
  `ρ(I)_μ = (I ∩ K[T])_μ ⊆ I_μ` for all `μ ≤ μ̄`" (`ha`);
* (b) "On the other hand, we have `I_μ = G_μ ∩ (I ∩ K[T'])G` for all `μ ≤ μ̄` and therefore, in
  view of `ρ(I_ν) ⊆ I_ν` for all `ν ≤ μ̄`, we get `ρ(I)_μ ⊆ {(I ∩ K[T ∩ T'])K[T]}_μ` for all
  `μ ≤ μ̄`" (`hb`);
* (c) "Thus we get `(I ∩ K[T])_μ ⊆ {(I ∩ K[T ∩ T'])K[T]}_μ` for all `μ ≤ μ̄`" (`hc`);
* (d) "Here the reversed inclusion is obvious.  Hence `{(I ∩ K[T ∩ T'])G}_μ = {(I ∩ K[T])G}_μ =
  I_μ` for all `μ ≤ μ̄`" (the end of the proof).

The ideal `(I ∩ K[T ∩ T'])K[T]` of the ring `K[T]` is `U` (an `Ideal` of the subalgebra), the
degree-`μ` part of a subset is expressed through membership in `G_μ`, and `ρ(I)_μ` is `ρ(I_μ)`
(`ρ` is graded). -/
private theorem isTauSubmoduleMv_inf_of_sup_eq {I : Ideal (MvPolynomial (Fin n) K)}
    (hI : I.IsHomogeneous (homogeneousSubmodule (Fin n) K)) {μbar : ℕ}
    {T T' : Submodule K (MvPolynomial (Fin n) K)}
    (hT : IsTauSubmoduleMv K n I T μbar) (hT' : IsTauSubmoduleMv K n I T' μbar)
    (hsup : T ⊔ T' = homogeneousSubmodule (Fin n) K 1) :
    IsTauSubmoduleMv K n I (T ⊓ T') μbar := by
  -- `T''` with `G₁ = T ⊕ T''`, and `ρ : G → K[T]`
  obtain ⟨T'', hT''T', hdisj, hsup'', hsplit⟩ := exists_complement_of_sup_eq K n hT.1 hsup
  obtain ⟨ρ, hker, hrange, hfix, -, hgr⟩ :=
    exists_retraction K n hT.1 (hT''T'.trans hT'.1) hdisj hsup''
  have hρT'' : ∀ t ∈ T'', ρ t = 0 := fun t ht =>
    RingHom.mem_ker.mp (by rw [hker]; exact Ideal.subset_span ht)
  -- `ρ(T') ⊆ T ∩ T'`, hence `ρ(K[T']) ⊆ K[T ∩ T']`
  have hρT' : ∀ t ∈ T', ρ t ∈ T ⊓ T' := by
    intro t ht
    obtain ⟨a, ha, d, hd, rfl⟩ := hsplit t ht
    rw [map_add, hρT'' d hd, add_zero, hfix a (Algebra.subset_adjoin ha.1)]
    exact ha
  have hρadj : ∀ g ∈ Algebra.adjoin K (T' : Set (MvPolynomial (Fin n) K)),
      ρ g ∈ Algebra.adjoin K ((T ⊓ T' : Submodule K (MvPolynomial (Fin n) K)) :
        Set (MvPolynomial (Fin n) K)) := by
    intro g hg
    induction hg using Algebra.adjoin_induction with
    | mem x hx => exact Algebra.subset_adjoin (hρT' x hx)
    | algebraMap r => rw [ρ.commutes r]; exact Subalgebra.algebraMap_mem _ r
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | mul x y _ _ hx hy => rw [map_mul]; exact Subalgebra.mul_mem _ hx hy
  -- (a) `ρ(I_μ) = (I ∩ K[T])_μ ⊆ I_μ` for `μ ≤ μ̄`
  have ha : ∀ μ ≤ μbar,
      ρ '' {ψ | ψ ∈ I ∧ ψ ∈ homogeneousSubmodule (Fin n) K μ} =
        {g | g ∈ I ∧ g ∈ Algebra.adjoin K (T : Set (MvPolynomial (Fin n) K)) ∧
          g ∈ homogeneousSubmodule (Fin n) K μ} := by
    intro μ hμ
    ext g
    constructor
    · rintro ⟨ψ, ⟨hψI, hψ⟩, rfl⟩
      -- `I_μ ⊆ (I ∩ K[T]) G` and `ρ` fixes `K[T]`
      have h1 := Ideal.mem_map_of_mem ρ ((hT.2 μ hμ ψ hψ).mp hψI)
      rw [Ideal.map_span] at h1
      refine ⟨(Ideal.span_le.mpr ?_) h1, hrange ψ, hgr μ ψ hψ⟩
      rintro _ ⟨x, hx, rfl⟩
      rw [hfix x hx.2]
      exact hx.1
    · rintro ⟨hgI, hgT, hg⟩
      exact ⟨g, ⟨hgI, hg⟩, hfix g hgT⟩
  have hρI : ∀ ν ≤ μbar, ∀ ψ ∈ homogeneousSubmodule (Fin n) K ν, ψ ∈ I → ρ ψ ∈ I := fun ν hν ψ hψ hψI =>
    ((ha ν hν).subset ⟨ψ, ⟨hψI, hψ⟩, rfl⟩).1
  -- (b) `ρ(I)_μ ⊆ {(I ∩ K[T ∩ T'])K[T]}_μ` for `μ ≤ μ̄`
  let ρ' : MvPolynomial (Fin n) K →ₐ[K] Algebra.adjoin K (T : Set (MvPolynomial (Fin n) K)) :=
    ρ.codRestrict _ hrange
  let U : Ideal (Algebra.adjoin K (T : Set (MvPolynomial (Fin n) K))) :=
    Ideal.span {x | (x : MvPolynomial (Fin n) K) ∈ I ∧ (x : MvPolynomial (Fin n) K) ∈
      Algebra.adjoin K ((T ⊓ T' : Submodule K (MvPolynomial (Fin n) K)) :
        Set (MvPolynomial (Fin n) K))}
  have hb : ∀ μ ≤ μbar, ∀ ψ ∈ homogeneousSubmodule (Fin n) K μ, ψ ∈ I → ρ' ψ ∈ U := by
    intro μ hμ ψ hψ hψI
    have h1 := Ideal.mem_map_of_mem ρ' (mem_span_homogeneous K n hI hT' hμ hψ hψI)
    rw [Ideal.map_span] at h1
    refine (Ideal.span_le.mpr ?_) h1
    rintro _ ⟨g, ⟨⟨hgI, hgT'⟩, d, hd, hgd⟩, rfl⟩
    exact Ideal.subset_span ⟨hρI d hd g hgd hgI, hρadj g hgT'⟩
  -- (c) `(I ∩ K[T])_μ ⊆ {(I ∩ K[T ∩ T'])K[T]}_μ` for `μ ≤ μ̄`
  have hc : ∀ μ ≤ μbar, ∀ x : Algebra.adjoin K (T : Set (MvPolynomial (Fin n) K)),
      (x : MvPolynomial (Fin n) K) ∈ I → (x : MvPolynomial (Fin n) K) ∈
        homogeneousSubmodule (Fin n) K μ → x ∈ U := by
    intro μ hμ x hxI hx
    have h := hb μ hμ x hx hxI
    rwa [show ρ' (x : MvPolynomial (Fin n) K) = x from Subtype.ext (hfix x x.2)] at h
  -- (d) the reversed inclusion is obvious; hence `I_μ = G_μ ∩ (I ∩ K[T ∩ T'])G` for `μ ≤ μ̄`
  have hUle : U ≤ Ideal.comap (Algebra.adjoin K (T : Set (MvPolynomial (Fin n) K))).val
      (Ideal.span ((I : Set (MvPolynomial (Fin n) K)) ∩
        (Algebra.adjoin K ((T ⊓ T' : Submodule K (MvPolynomial (Fin n) K)) :
          Set (MvPolynomial (Fin n) K)) : Set (MvPolynomial (Fin n) K)))) :=
    Ideal.span_le.mpr fun x hx => Ideal.subset_span ⟨hx.1, hx.2⟩
  refine ⟨inf_le_left.trans hT.1, fun μ hμ ψ hψ =>
    ⟨fun hψI => ?_, fun h => (Ideal.span_le.mpr fun x hx => hx.1) h⟩⟩
  refine (Ideal.span_le.mpr ?_) (mem_span_homogeneous K n hI hT hμ hψ hψI)
  rintro g ⟨⟨hgI, hgT⟩, d, hd, hgd⟩
  exact hUle (hc d hd ⟨g, hgT⟩ hgI hgd)

/-- Lemma 10, p. 221: "Let `G` be a polynomial ring over a field `K`, graded in a natural way.
Let `G_μ` denote the homogeneous part of degree `μ ≥ 0`.  Let `μ̄` be a positive integer.  Let
`I` be a homogeneous ideal in `G` and `I_μ` the homogeneous part of degree `μ ≥ 0` of `I`.  Let
`T` and `T'` be two `K`-submodules of `G₁` which have the property that
`I_μ = G_μ ∩ (I ∩ K[T]) G = G_μ ∩ (I ∩ K[T']) G` for all `μ ≤ μ̄` where `K[T]` (resp. `K[T']`)
denotes the `K`-subalgebra of `G` generated by the elements of `T` (resp. `T'`).  Then we have
`I_μ = G_μ ∩ (I ∩ K[T ∩ T']) G` for all `μ ≤ μ̄`."  Here `G = MvPolynomial (Fin n) K`.

Proof as printed (p. 222): "We may assume that `T` and `T'` generate the whole `K`-module `G₁`.
(If otherwise, enlarge `T'` in such a way that `T ∩ T'` remains the same, and `T + T' = G₁`.)"
(`exists_enlarge`, `isTauSubmoduleMv_mono`); the rest is `isTauSubmoduleMv_inf_of_sup_eq`: the
complement `T''`, the endomorphism `ρ` of `G` onto `K[T]` with kernel `(T'')G`, and the steps
(a)-(d) of the printed proof.  The hypothesis `0 < μ̄` is a hypothesis of the paper and is not used
in its proof.  Gap in the paper filled: "`ρ` induces an isomorphism of graded `K`-algebras
`K[T] → G/(T'')G`" (`exists_retraction`). -/
@[blueprint "lem:III.10"
  (statement := /-- Let $G$ be a polynomial ring over a field $K$, graded in a natural way,
    and $G_\mu$ its homogeneous part of degree $\mu\ge0$. Let $\bar\mu$ be a positive integer.
    Let $I$ be a homogeneous ideal in $G$ and $I_\mu$ its homogeneous part of degree $\mu$.
    Let $T$ and $T'$ be two $K$-submodules of $G_1$ which have the property that
    $I_\mu=G_\mu\cap(I\cap K[T])G=G_\mu\cap(I\cap K[T'])G$ for all $\mu\le\bar\mu$, where
    $K[T]$ (resp.\ $K[T']$) denotes the $K$-subalgebra of $G$ generated by the elements of $T$
    (resp.\ $T'$). Then $I_\mu=G_\mu\cap(I\cap K[T\cap T'])G$ for all $\mu\le\bar\mu$.
    (Lemma 10, p.~221.) Formalization note (encoding): $G=K[X_1,\dots,X_n]$ is a polynomial
    ring in finitely many variables (the only case used). -/)
  (proof := /-- We may assume that $T$ and $T'$ generate the whole $K$-module $G_1$. (If
    otherwise, enlarge $T'$ in such a way that $T\cap T'$ remains the same, and $T+T'=G_1$.)
    Let $T''$ be the $K$-submodule of $T'$ such that $G_1$ is a direct sum of $T$ and $T''$.
    Let $\rho$ be the natural homomorphism $G\to G/(T'')G$ where $(T'')G$ is the ideal in $G$
    generated by the elements of $T''$. Then $\rho$ induces an isomorphism of graded
    $K$-algebras $K[T]\to G/(T'')G$. Therefore, we may view $\rho$ as an endomorphism of $G$
    which maps $G$ onto $K[T]$ in a natural way. Now, we have $I_\mu=G_\mu\cap(I\cap K[T])G$
    for all $\mu\le\bar\mu$, and therefore $\rho(I)_\mu=(I\cap K[T])_\mu\subseteq I_\mu$ for all
    $\mu\le\bar\mu$. (The suffix $\mu$ indicates the homogeneous part of degree $\mu$.) On the
    other hand, we have $I_\mu=G_\mu\cap(I\cap K[T'])G$ for all $\mu\le\bar\mu$ and therefore,
    in view of $\rho(I_\nu)\subseteq I_\nu$ for all $\nu\le\bar\mu$, we get
    $\rho(I)_\mu\subseteq\{(I\cap K[T\cap T'])K[T]\}_\mu$ for all $\mu\le\bar\mu$. Thus we get
    $(I\cap K[T])_\mu\subseteq\{(I\cap K[T\cap T'])K[T]\}_\mu$ for all $\mu\le\bar\mu$. Here the
    reversed inclusion is obvious. Hence
    $\{(I\cap K[T\cap T'])G\}_\mu=\{(I\cap K[T])G\}_\mu=I_\mu$ for all $\mu\le\bar\mu$.

    (Lean: the reduction to $T+T'=G_1$ is \texttt{exists\_enlarge}, the complement $T''$ is
    \texttt{exists\_complement\_of\_sup\_eq}, and the endomorphism $\rho$, with kernel $(T'')G$,
    image $K[T]$ and the isomorphism $K[T]\to G/(T'')G$, is \texttt{exists\_retraction}; the
    remaining steps are the displayed ones, in the same order. The hypothesis $\bar\mu>0$ of the
    paper is not used in its proof.)

    \textbf{Gap in the paper filled.} ``$\rho$ induces an isomorphism of graded $K$-algebras
    $K[T]\to G/(T'')G$'' is not argued in the paper; Lean proves that $\rho$, built from the
    projection of $G_1$ onto $T$ along $T''$, is graded, has kernel $(T'')G$, maps $G$ into
    $K[T]$ and is the identity on $K[T]$, so that $K[T]\to G/(T'')G$ is bijective. -/)
  (latexEnv := "lemma")]
theorem isTauSubmoduleMv_inf (I : Ideal (MvPolynomial (Fin n) K))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin n) K))
    (μbar : ℕ) (hμ : 0 < μbar) (T T' : Submodule K (MvPolynomial (Fin n) K))
    (hT : IsTauSubmoduleMv K n I T μbar) (hT' : IsTauSubmoduleMv K n I T' μbar) :
    IsTauSubmoduleMv K n I (T ⊓ T') μbar := by
  -- (the hypothesis `0 < μ̄` is not used in the printed proof either)
  have _ := hμ
  -- "We may assume that `T` and `T'` generate the whole `K`-module `G₁`."
  obtain ⟨T₁, hT'T₁, hT₁1, hinf, hsup⟩ := exists_enlarge K n hT.1 hT'.1
  have hT₁ := isTauSubmoduleMv_mono K n hT' hT'T₁ hT₁1
  rw [← hinf]
  exact isTauSubmoduleMv_inf_of_sup_eq K n hI hT hT₁ hsup

end Lemma10

/-! ### Corollary to Lemma 10 (p. 222): the submodules T_a -/

section Corollary10

variable (R : Type u) [CommRing R] [IsRegularLocalRing R] (J : Ideal R)

/-- The `K`-submodule `T_a` of `gr¹_M(R)` of the Corollary to Lemma 10 (p. 222): "the
`K`-submodule `T_a` of `gr¹_M(R)` generated by `W₁, …, W_{τ_a}` is uniquely determined by the
given ideal `J` in `R` and `T_a` is the smallest `K`-submodule of `gr¹_M(R)` such that
`gr^μ_M(J, R) = gr^μ_M(R) ∩ (gr_M(J, R) ∩ K[T_a]) gr_M(R)` for all `μ ≤ μ^{(a)}(J)`".

Encoded, without any choice, as the infimum of all `K`-submodules of `gr¹_M(R)` with the
property of Definition 6 up to degree `μ^{(a)}(J)`; the Corollary (`tauSubmodule_spec`)
says that this infimum has the property, has rank `τ^{(a)}(J)` and is the span of every
system `W₁, …, W_{τ_a}` as in Definition 6. -/
noncomputable def tauSubmodule (a : ℕ) :
    Submodule (R ⧸ maximalIdeal R) (AssocGraded (maximalIdeal R)) :=
  sInf {T | IsTauSubmodule R J T (mu R J a)}

/-- `T_a` is contained in every `K`-submodule with the property of Definition 6 up to degree
`μ^{(a)}(J)` (immediate from the encoding as an infimum). -/
theorem tauSubmodule_le (a : ℕ) (T : Submodule (R ⧸ maximalIdeal R) (AssocGraded (maximalIdeal R)))
    (hT : IsTauSubmodule R J T (mu R J a)) : tauSubmodule R J a ≤ T :=
  sInf_le hT

/-- For `x ∈ grᵉ_I(A)`, `x` is recovered from its degree-`e` component. -/
private theorem ofGrPiece_grProj_of_mem {A : Type*} [CommRing A] (I : Ideal A) {e : ℕ}
    {x : AssocGraded I} (hx : x ∈ AssocGraded.homogeneous I e) :
    AssocGraded.ofGrPiece I e (grProj I e x) = x := by
  obtain ⟨y, rfl⟩ := LinearMap.mem_range.mp hx
  rw [grProj_ofGrPiece_same]

/-- For `x ∈ gr^{e'}_I(A)` and `e ≠ e'`, the degree-`e` component of `x` vanishes. -/
private theorem grProj_of_mem_ne {A : Type*} [CommRing A] (I : Ideal A) {e e' : ℕ}
    (h : e' ≠ e) {x : AssocGraded I} (hx : x ∈ AssocGraded.homogeneous I e') :
    grProj I e x = 0 := by
  obtain ⟨y, rfl⟩ := LinearMap.mem_range.mp hx
  exact grProj_ofGrPiece_ne I h y

/-- `gr_M(R) ≅ K[Z₁, …, Z_r]` as graded `K`-algebras (`K = R/M`), with `r = dim R` the number of
generators of `M` (p. 180 and p. 235: `gr_M(R)` is a polynomial ring in `n = dim R` variables over
`K`): an isomorphism `e` of `K`-algebras which maps the homogeneous part `G_d` onto `gr^d_M(R)` and
commutes with taking homogeneous components. -/
theorem exists_gradedAlgEquiv :
    ∃ (r : ℕ) (e : MvPolynomial (Fin r) (R ⧸ maximalIdeal R) ≃ₐ[R ⧸ maximalIdeal R]
      AssocGraded (maximalIdeal R)), r = (maximalIdeal R).spanFinrank ∧
      (∀ (d : ℕ) (p : MvPolynomial (Fin r) (R ⧸ maximalIdeal R)),
        p ∈ MvPolynomial.homogeneousSubmodule (Fin r) (R ⧸ maximalIdeal R) d ↔
          e p ∈ AssocGraded.homogeneous (maximalIdeal R) d) ∧
      ∀ (d : ℕ) (p : MvPolynomial (Fin r) (R ⧸ maximalIdeal R)),
        AssocGraded.ofGrPiece (maximalIdeal R) d (grProj (maximalIdeal R) d (e p)) =
          e (MvPolynomial.homogeneousComponent d p) := by
  obtain ⟨S, hScard, hSspan⟩ :=
    (IsNoetherian.noetherian (maximalIdeal R)).exists_span_finset_card_eq_spanFinrank
  have hS : Ideal.span (S : Set R) = maximalIdeal R := hSspan
  let z : Fin S.card → R := fun i => (S.equivFin.symm i : R)
  have hinj : Function.Injective z := Subtype.val_injective.comp S.equivFin.symm.injective
  have hrange : Set.range z = (S : Set R) := by
    ext y
    constructor
    · rintro ⟨i, rfl⟩
      exact (S.equivFin.symm i).2
    · intro hy
      exact ⟨S.equivFin ⟨y, hy⟩, by simp [z]⟩
  have hP : Ideal.span (Set.range z) = maximalIdeal R := by rw [hrange, hS]
  have hz : ∀ i, z i ∈ maximalIdeal R ^ 1 := fun i => by
    rw [pow_one, ← hP]
    exact Ideal.subset_span ⟨i, rfl⟩
  let e := assocGradedAlgEquiv hS hScard hinj (fun i => (S.equivFin.symm i).2) hP hz
  -- `e` maps `G_d` into `gr^d_M(R)`: lift a form of degree `d` to a form over `R`
  have h1 : ∀ (d : ℕ) (p : MvPolynomial (Fin S.card) (R ⧸ maximalIdeal R)),
      p ∈ MvPolynomial.homogeneousSubmodule (Fin S.card) (R ⧸ maximalIdeal R) d →
        e p ∈ AssocGraded.homogeneous (maximalIdeal R) d := by
    intro d p hp
    obtain ⟨q, rfl⟩ := MvPolynomial.map_surjective _ Ideal.Quotient.mk_surjective p
    have hq : (MvPolynomial.homogeneousComponent d q).map (Ideal.Quotient.mk (maximalIdeal R)) =
        q.map (Ideal.Quotient.mk (maximalIdeal R)) := by
      rw [← MvPolynomial.homogeneousComponent_eq_self hp]
      ext m
      simp only [MvPolynomial.coeff_map, MvPolynomial.coeff_homogeneousComponent]
      split_ifs <;> simp
    rw [← hq]
    show MvPolynomial.aeval _ _ ∈ _
    rw [aeval_mk_map_of_isHomogeneous (maximalIdeal R) z hz
      (MvPolynomial.homogeneousComponent_isHomogeneous d q)]
    exact AssocGraded.mk_mem_homogeneous _ _
  -- taking homogeneous components commutes with `e`
  have h2 : ∀ (d : ℕ) (p : MvPolynomial (Fin S.card) (R ⧸ maximalIdeal R)),
      AssocGraded.ofGrPiece (maximalIdeal R) d (grProj (maximalIdeal R) d (e p)) =
        e (MvPolynomial.homogeneousComponent d p) := by
    intro d p
    conv_lhs => rw [← MvPolynomial.sum_homogeneousComponent p]
    rw [map_sum, map_sum, map_sum]
    rw [Finset.sum_eq_single d]
    · exact ofGrPiece_grProj_of_mem _
        (h1 d _ (MvPolynomial.homogeneousComponent_mem d p))
    · intro d' _ hd'
      rw [grProj_of_mem_ne _ hd' (h1 d' _ (MvPolynomial.homogeneousComponent_mem d' p)),
        map_zero]
    · intro hd
      rw [MvPolynomial.homogeneousComponent_eq_zero d p (by
        simp only [Finset.mem_range, not_lt] at hd; omega), map_zero, map_zero, map_zero]
  refine ⟨S.card, e, hScard, fun d p => ⟨h1 d p, fun hp => ?_⟩, h2⟩
  -- conversely, if `e p ∈ gr^d_M(R)` then all other homogeneous components of `p` vanish
  have hzero : ∀ d', d' ≠ d → MvPolynomial.homogeneousComponent d' p = 0 := by
    intro d' hd'
    apply e.injective
    rw [← h2, grProj_of_mem_ne _ (Ne.symm hd') hp, map_zero, map_zero]
  have hpd : p = MvPolynomial.homogeneousComponent d p := by
    conv_lhs => rw [← MvPolynomial.sum_homogeneousComponent p]
    rw [Finset.sum_eq_single d (fun d' _ hd' => hzero d' hd')]
    intro hd
    rw [MvPolynomial.homogeneousComponent_eq_zero d p (by
      simp only [Finset.mem_range, not_lt] at hd; omega)]
  rw [hpd]
  exact MvPolynomial.homogeneousComponent_mem d p

/-- The property of Definition 6 transfers along a graded isomorphism
`e : K[Z₁, …, Z_r] ≅ gr_M(R)`: `T` has it for `gr_M(J, R)` iff `e⁻¹(T)` has it for the
homogeneous ideal `e⁻¹(gr_M(J, R))`. -/
private theorem isTauSubmodule_iff {r : ℕ}
    (e : MvPolynomial (Fin r) (R ⧸ maximalIdeal R) ≃ₐ[R ⧸ maximalIdeal R]
      AssocGraded (maximalIdeal R))
    (hE : ∀ (d : ℕ) (p : MvPolynomial (Fin r) (R ⧸ maximalIdeal R)),
      p ∈ MvPolynomial.homogeneousSubmodule (Fin r) (R ⧸ maximalIdeal R) d ↔
        e p ∈ AssocGraded.homogeneous (maximalIdeal R) d)
    (T : Submodule (R ⧸ maximalIdeal R) (AssocGraded (maximalIdeal R))) (μ₀ : ℕ) :
    let _ : Field (R ⧸ maximalIdeal R) := Ideal.Quotient.field _
    (IsTauSubmodule R J T μ₀ ↔
      IsTauSubmoduleMv (R ⧸ maximalIdeal R) r (Ideal.comap e (grIdeal (maximalIdeal R) J))
        (T.comap e.toLinearMap) μ₀) := by
  let _ : Field (R ⧸ maximalIdeal R) := Ideal.Quotient.field _
  have hadj : ∀ p, p ∈ Algebra.adjoin (R ⧸ maximalIdeal R)
      ((T.comap e.toLinearMap : Submodule _ _) : Set (MvPolynomial (Fin r) (R ⧸ maximalIdeal R)))
      ↔ e p ∈ Algebra.adjoin (R ⧸ maximalIdeal R) (T : Set (AssocGraded (maximalIdeal R))) := by
    intro p
    have hmap : (Algebra.adjoin (R ⧸ maximalIdeal R) ((T.comap e.toLinearMap : Submodule _ _) :
        Set (MvPolynomial (Fin r) (R ⧸ maximalIdeal R)))).map (e : _ →ₐ[R ⧸ maximalIdeal R] _) =
        Algebra.adjoin (R ⧸ maximalIdeal R) (T : Set (AssocGraded (maximalIdeal R))) := by
      rw [AlgHom.map_adjoin]
      congr 1
      ext y
      refine ⟨?_, fun hy => ⟨e.symm y, by simpa using hy, by simp⟩⟩
      rintro ⟨x, hx, rfl⟩
      simpa using hx
    rw [← hmap, Subalgebra.mem_map]
    refine ⟨fun h => ⟨p, h, rfl⟩, ?_⟩
    rintro ⟨q, hq, hqp⟩
    rwa [← e.injective hqp]
  have hspan : ∀ p, p ∈ Ideal.span ((Ideal.comap e (grIdeal (maximalIdeal R) J) :
      Set (MvPolynomial (Fin r) (R ⧸ maximalIdeal R))) ∩
      (Algebra.adjoin (R ⧸ maximalIdeal R) ((T.comap e.toLinearMap : Submodule _ _) :
        Set (MvPolynomial (Fin r) (R ⧸ maximalIdeal R))) :
        Set (MvPolynomial (Fin r) (R ⧸ maximalIdeal R)))) ↔
      e p ∈ Ideal.span ((grIdeal (maximalIdeal R) J : Set (AssocGraded (maximalIdeal R))) ∩
        (Algebra.adjoin (R ⧸ maximalIdeal R) (T : Set (AssocGraded (maximalIdeal R))) :
          Set (AssocGraded (maximalIdeal R)))) := by
    intro p
    have himg : (e : MvPolynomial (Fin r) (R ⧸ maximalIdeal R) → AssocGraded (maximalIdeal R)) ''
        ((Ideal.comap e (grIdeal (maximalIdeal R) J) :
          Set (MvPolynomial (Fin r) (R ⧸ maximalIdeal R))) ∩
        (Algebra.adjoin (R ⧸ maximalIdeal R) ((T.comap e.toLinearMap : Submodule _ _) :
          Set (MvPolynomial (Fin r) (R ⧸ maximalIdeal R))) :
          Set (MvPolynomial (Fin r) (R ⧸ maximalIdeal R)))) =
        (grIdeal (maximalIdeal R) J : Set (AssocGraded (maximalIdeal R))) ∩
          (Algebra.adjoin (R ⧸ maximalIdeal R) (T : Set (AssocGraded (maximalIdeal R))) :
            Set (AssocGraded (maximalIdeal R))) := by
      ext y
      constructor
      · rintro ⟨x, ⟨hx1, hx2⟩, rfl⟩
        exact ⟨hx1, (hadj x).mp hx2⟩
      · rintro ⟨hy1, hy2⟩
        refine ⟨e.symm y, ⟨?_, (hadj _).mpr (by simpa using hy2)⟩, by simp⟩
        rw [SetLike.mem_coe, Ideal.mem_comap, AlgEquiv.apply_symm_apply]
        exact hy1
    rw [← himg, ← Ideal.map_span, Ideal.mem_map_of_equiv]
    refine ⟨fun h => ⟨p, h, rfl⟩, ?_⟩
    rintro ⟨q, hq, hqp⟩
    rwa [← e.injective hqp]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun p hp => (hE 1 p).mpr (h1 hp), fun μ hμ p hp => ?_⟩
    rw [Ideal.mem_comap, hspan]
    exact h2 μ hμ (e p) ((hE μ p).mp hp)
  · rintro ⟨h1, h2⟩
    refine ⟨fun t ht => ?_, fun μ hμ ψ hψ => ?_⟩
    · have hmem : e.symm t ∈ T.comap e.toLinearMap := by simpa using ht
      simpa using (hE 1 _).mp (h1 hmem)
    · have hp : e.symm ψ ∈ MvPolynomial.homogeneousSubmodule (Fin r) (R ⧸ maximalIdeal R) μ :=
        (hE μ _).mpr (by simpa using hψ)
      have := h2 μ hμ _ hp
      rwa [Ideal.mem_comap, hspan, AlgEquiv.apply_symm_apply] at this

/-- Lemma 10 for `gr_M(R)`: if `T` and `T'` have the property of Definition 6 up to `μ₀`, so
does `T ∩ T'`.  (For `μ₀ = 0` the property holds for every `T ⊆ gr¹_M(R)`, since
`gr⁰_M(R) = K ⊆ K[T]`; for `μ₀ > 0` it is Lemma 10 transported along `gr_M(R) ≅ K[Z]`.) -/
private theorem isTauSubmodule_inf
    (T T' : Submodule (R ⧸ maximalIdeal R) (AssocGraded (maximalIdeal R))) (μ₀ : ℕ)
    (hT : IsTauSubmodule R J T μ₀) (hT' : IsTauSubmodule R J T' μ₀) :
    IsTauSubmodule R J (T ⊓ T') μ₀ := by
  rcases Nat.eq_zero_or_pos μ₀ with rfl | hμ₀
  · refine ⟨inf_le_left.trans hT.1, fun μ hμ ψ hψ => ⟨fun h => ?_, fun h => ?_⟩⟩
    · obtain rfl : μ = 0 := by omega
      obtain ⟨y, rfl⟩ := LinearMap.mem_range.mp hψ
      obtain ⟨⟨a, ha⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ y
      refine Ideal.subset_span ⟨h, ?_⟩
      rw [AssocGraded.ofGrPiece_mk, mk_zero_eq_algebraMap_mk]
      exact Subalgebra.algebraMap_mem _ _
    · exact (Ideal.span_le.mpr fun x hx => hx.1) h
  let _ : Field (R ⧸ maximalIdeal R) := Ideal.Quotient.field _
  obtain ⟨r, e, -, hE, hpr⟩ := exists_gradedAlgEquiv R
  let _ : GradedAlgebra (MvPolynomial.homogeneousSubmodule (Fin r) (R ⧸ maximalIdeal R)) :=
    MvPolynomial.gradedAlgebra
  have hI : (Ideal.comap e (grIdeal (maximalIdeal R) J)).IsHomogeneous
      (MvPolynomial.homogeneousSubmodule (Fin r) (R ⧸ maximalIdeal R)) := by
    intro i p hp
    rw [show ((DirectSum.decompose (MvPolynomial.homogeneousSubmodule (Fin r)
      (R ⧸ maximalIdeal R)) p i : MvPolynomial (Fin r) (R ⧸ maximalIdeal R))) =
        MvPolynomial.homogeneousComponent i p from
      MvPolynomial.decomposition.decompose'_apply p i, Ideal.mem_comap, ← hpr]
    obtain ⟨a, haJ, ha, hmk⟩ := grIdeal_le_bound (maximalIdeal R) J hp i
    rw [← hmk, AssocGraded.ofGrPiece_mk]
    exact mk_mem_grIdeal _ haJ ha
  refine (isTauSubmodule_iff R J e hE _ μ₀).mpr ?_
  rw [Submodule.comap_inf]
  exact isTauSubmoduleMv_inf _ r _ hI μ₀ hμ₀ _ _ ((isTauSubmodule_iff R J e hE _ μ₀).mp hT)
    ((isTauSubmodule_iff R J e hE _ μ₀).mp hT')

/-- Corollary to Lemma 10, p. 222: "The notation and assumptions being the same as in
Definition 6, the `K`-submodule `T_a` of `gr¹_M(R)` generated by `W₁, …, W_{τ_a}` is uniquely
determined by the given ideal `J` in `R` and `T_a` is the smallest `K`-submodule of `gr¹_M(R)`
such that `gr^μ_M(J, R) = gr^μ_M(R) ∩ (gr_M(J, R) ∩ K[T_a]) gr_M(R)` for all `μ ≤ μ^{(a)}(J)`."

With `T_a := tauSubmodule R J a` (the infimum of all submodules with the property): `T_a` has
the property, its rank is `τ^{(a)}(J)`, and the span of every system of `τ^{(a)}(J)` linear
forms with the property equals `T_a` (uniqueness); minimality is `tauSubmodule_le`.

Deviation from the paper (statement modified): the conclusion `rank T_a = τ^{(a)}(J)` is added
(implicit in the paper).  Gap in the paper filled: the paper gives no proof; Lean transports
Lemma 10 to `gr_M(R)` and treats `μ^{(a)}(J) = 0` (`J = R`) separately. -/
@[blueprint "cor:III.lem10"
  (statement := /-- The notation and assumptions being the same as in \cref{def:III.6}, let
    $1\le a\le t(J)$. The $K$-submodule $T_a$ of $\operatorname{gr}^1_M(R)$ generated by
    $W_1,\dots,W_{\tau_a}$ is uniquely determined by the given ideal $J$ in $R$ (it is the same
    for every system of $\tau^{(a)}(J)$ linear forms with the property of \cref{def:III.6}), and
    $T_a$ is the smallest $K$-submodule of $\operatorname{gr}^1_M(R)$ such that
    $\operatorname{gr}^\mu_M(J,R)=\operatorname{gr}^\mu_M(R)\cap(\operatorname{gr}_M(J,R)\cap
    K[T_a])\operatorname{gr}_M(R)$ for all $\mu\le\mu^{(a)}(J)$. (Corollary to Lemma 10,
    p.~222.) Formalization note (encoding): $T_a$ is encoded as the intersection of all
    $K$-submodules of $\operatorname{gr}^1_M(R)$ with the property up to degree
    $\mu^{(a)}(J)$; the statement is that this intersection has the property, has rank
    $\tau^{(a)}(J)$ and equals the span of every system $W_1,\dots,W_{\tau_a}$ as in
    \cref{def:III.6}.

    \textbf{Deviation from the paper (statement modified).} The conclusion
    $\operatorname{rank}_K T_a=\tau^{(a)}(J)$ is added; it is implicit in the paper ($T_a$ is
    generated by a minimal system $W_1,\dots,W_{\tau_a}$). -/)
  (proof := /-- (The paper gives no proof.) Since $R$ is regular, $\operatorname{gr}_M(R)$ is a
    polynomial ring over $K$ graded in the natural way, and $\operatorname{gr}_M(J,R)$ is a
    homogeneous ideal; so \cref{lem:III.10} applies: if $T$ and $T'$ have the property up to
    $\mu^{(a)}(J)$, so does $T\cap T'$. (If $\mu^{(a)}(J)=0$, i.e.\ $J=R$, every
    $T\subseteq\operatorname{gr}^1_M(R)$ has the property, since
    $\operatorname{gr}^0_M(R)=K\subseteq K[T]$; this case is treated directly, as
    \cref{lem:III.10} is stated for positive $\bar\mu$.) Let $T_0$ be a submodule with the
    property of minimal rank. For every $T$ with the property, $T_0\cap T$ has the property, so
    $T_0\cap T=T_0$ by minimality, i.e.\ $T_0\subseteq T$; hence $T_0$ is the smallest submodule
    with the property. The span of a system $W_1,\dots,W_{\tau_a}$ as in Definition~6 contains
    $T_0$, so $\operatorname{rank}T_0\le\tau_a$; a $K$-basis of $T_0$ is a system of
    $\operatorname{rank}T_0$ linear forms with the property, so $\operatorname{rank}T_0\ge\tau_a$.
    Finally the span of any system $W_1,\dots,W_{\tau_a}$ with the property contains $T_0$ and has
    rank $\le\tau_a=\operatorname{rank}T_0$, hence equals $T_0$ (uniqueness). -/)
  (latexEnv := "corollary")]
theorem tauSubmodule_spec (a : ℕ) (ha : 1 ≤ a) (hat : a ≤ t R J) :
    IsTauSubmodule R J (tauSubmodule R J a) (mu R J a) ∧
    Module.finrank (R ⧸ maximalIdeal R) (tauSubmodule R J a) = tau R J a ∧
    ∀ W : Fin (tau R J a) → AssocGraded (maximalIdeal R),
      (∀ i, W i ∈ AssocGraded.homogeneous (maximalIdeal R) 1) →
      IsTauSubmodule R J (Submodule.span (R ⧸ maximalIdeal R) (Set.range W)) (mu R J a) →
      Submodule.span (R ⧸ maximalIdeal R) (Set.range W) = tauSubmodule R J a := by
  -- (the hypotheses `1 ≤ a ≤ t(J)` are not needed)
  have _ := ha
  have _ := hat
  classical
  let _ : Field (R ⧸ maximalIdeal R) := Ideal.Quotient.field _
  -- every submodule with the property lies in the finite-dimensional `gr¹_M(R)`
  have hfin : ∀ T : Submodule (R ⧸ maximalIdeal R) (AssocGraded (maximalIdeal R)),
      IsTauSubmodule R J T (mu R J a) → FiniteDimensional (R ⧸ maximalIdeal R) T := by
    intro T hT
    have : FiniteDimensional (R ⧸ maximalIdeal R) (AssocGraded.homogeneous (maximalIdeal R) 1) :=
      Module.Finite.iff_fg.mpr (homogeneous_fg _ 1)
    exact Submodule.finiteDimensional_of_le hT.1
  -- a submodule `T₀` with the property, of minimal rank
  obtain ⟨W₀, -, hT₀⟩ := tau_spec R J a
  have hex : ∃ k, ∃ T : Submodule (R ⧸ maximalIdeal R) (AssocGraded (maximalIdeal R)),
      IsTauSubmodule R J T (mu R J a) ∧ Module.finrank (R ⧸ maximalIdeal R) T = k :=
    ⟨_, _, hT₀, rfl⟩
  obtain ⟨T₀, hPT₀, hk⟩ := Nat.find_spec hex
  have := hfin T₀ hPT₀
  have hmin : ∀ T : Submodule (R ⧸ maximalIdeal R) (AssocGraded (maximalIdeal R)),
      IsTauSubmodule R J T (mu R J a) →
        Module.finrank (R ⧸ maximalIdeal R) T₀ ≤ Module.finrank (R ⧸ maximalIdeal R) T :=
    fun T hT => hk ▸ Nat.find_min' hex ⟨T, hT, rfl⟩
  -- by Lemma 10, `T₀ ∩ T` has the property, so `T₀ ∩ T = T₀` by minimality: `T₀ ⊆ T`
  have hle : ∀ T : Submodule (R ⧸ maximalIdeal R) (AssocGraded (maximalIdeal R)),
      IsTauSubmodule R J T (mu R J a) → T₀ ≤ T := by
    intro T hT
    have h1 : T₀ ⊓ T = T₀ := Submodule.eq_of_le_of_finrank_le inf_le_left
      (hmin _ (isTauSubmodule_inf R J T₀ T _ hPT₀ hT))
    rw [← h1]
    exact inf_le_right
  have heq : tauSubmodule R J a = T₀ := le_antisymm (sInf_le hPT₀) (le_sInf hle)
  -- the span of any system `W` of `τ` linear forms with the property contains `T₀`
  have hspan : ∀ {τ : ℕ} (W : Fin τ → AssocGraded (maximalIdeal R)),
      IsTauSubmodule R J (Submodule.span (R ⧸ maximalIdeal R) (Set.range W)) (mu R J a) →
        Module.finrank (R ⧸ maximalIdeal R) T₀ ≤ τ := by
    intro τ W hW
    have := hfin _ hW
    exact (Submodule.finrank_mono (hle _ hW)).trans
      ((finrank_range_le_card (R := R ⧸ maximalIdeal R) W).trans_eq (Fintype.card_fin τ))
  have hrank : Module.finrank (R ⧸ maximalIdeal R) T₀ = tau R J a := by
    refine le_antisymm (hspan W₀ hT₀) ?_
    -- a basis of `T₀` is a system of `rank T₀` linear forms with the property
    let b := Module.finBasis (R ⧸ maximalIdeal R) T₀
    have hb : Submodule.span (R ⧸ maximalIdeal R)
        (Set.range fun i => (b i : AssocGraded (maximalIdeal R))) = T₀ := by
      rw [show (fun i => (b i : AssocGraded (maximalIdeal R))) = T₀.subtype ∘ b from rfl,
        Set.range_comp, Submodule.span_image, b.span_eq, Submodule.map_top,
        Submodule.range_subtype]
    exact tau_le R J (fun i => (b i : AssocGraded (maximalIdeal R))) (fun i => hPT₀.1 (b i).2)
      (by rw [hb]; exact hPT₀)
  refine ⟨heq ▸ hPT₀, heq ▸ hrank, fun W _ hW => ?_⟩
  rw [heq]
  have := hfin _ hW
  exact (Submodule.eq_of_le_of_finrank_le (hle _ hW) (by
    rw [hrank]
    exact (finrank_range_le_card (R := R ⧸ maximalIdeal R) W).trans_eq (Fintype.card_fin _))).symm

/-- Corollary to Lemma 10, p. 222, second part: "In particular, `T_a ⊇ T_{a-1}` and
`τ^{(a)}(J) ≥ τ^{(a-1)}(J)` for all `a > 1`." -/
@[blueprint "cor:III.lem10-mono"
  (statement := /-- Notation as in \cref{cor:III.lem10}. In particular, $T_a\supseteq T_{a-1}$
    and $\tau^{(a)}(J)\ge\tau^{(a-1)}(J)$ for all $1<a\le t(J)$. (Corollary to Lemma 10,
    p.~222.) -/)
  (proof := /-- (The paper gives no proof.) Since $\mu^{(a-1)}(J)<\mu^{(a)}(J)$, the property
    up to degree $\mu^{(a)}(J)$ implies the property up to degree $\mu^{(a-1)}(J)$; hence $T_a$
    has the latter property and $T_{a-1}\subseteq T_a$ by the minimality of $T_{a-1}$
    (\cref{cor:III.lem10}). Likewise a system of $\tau^{(a)}(J)$ linear forms with the property
    up to $\mu^{(a)}(J)$ has it up to $\mu^{(a-1)}(J)$, whence
    $\tau^{(a-1)}(J)\le\tau^{(a)}(J)$ by the minimality in \cref{def:III.6}. -/)
  (latexEnv := "corollary")]
theorem tauSubmodule_mono (a : ℕ) (ha : 1 < a) (hat : a ≤ t R J) :
    tauSubmodule R J (a - 1) ≤ tauSubmodule R J a ∧ tau R J (a - 1) ≤ tau R J a := by
  -- `μ^{(a-1)}(J) < μ^{(a)}(J)`, so the property up to `μ^{(a)}(J)` implies the one up to
  -- `μ^{(a-1)}(J)`
  have hmu : mu R J (a - 1) ≤ mu R J a := by
    have hf : (muSet R J).Finite := (muSet_finite R J).1
    have hcard : hf.toFinset.card = t R J := (Set.ncard_eq_toFinset_card _ hf).symm
    have key := Nat.nth_strictMonoOn (p := (· ∈ muSet R J)) hf
    refine (key (Set.mem_Iio.mpr ?_) (Set.mem_Iio.mpr ?_) (by omega : a - 1 - 1 < a - 1)).le
    · rw [hcard]; omega
    · rw [hcard]; omega
  have hle : ∀ T, IsTauSubmodule R J T (mu R J a) → IsTauSubmodule R J T (mu R J (a - 1)) :=
    fun T hT => ⟨hT.1, fun μ hμ => hT.2 μ (hμ.trans hmu)⟩
  refine ⟨sInf_le_sInf fun T hT => hle T hT, ?_⟩
  obtain ⟨W, hW, hT⟩ := tau_spec R J a
  exact tau_le R J W hW (hle _ hT)

end Corollary10

/-! ### Definition 7 (pp. 222–223): regular systems of τ-parameters -/

section Definition7

variable (R : Type u) [CommRing R] [IsRegularLocalRing R] (J : Ideal R)

/-- Definition 7, pp. 222–223: "Let `R`, `M`, `J`, `μ*(J)`, and `τ*(J)` be the same as in
Definition 6.  Let `τ_a = τ^{(a)}(J)` for `1 ≤ a ≤ t = t(J)`.  Then a system of elements
`(z₁, …, z_{τ_a})` of `M` will be called a *regular system of `a`-th `τ`-parameters of `R` for
`J`* if we have, for every positive integer `b ≤ a`,
`gr^μ_M(J, R) = gr^μ_M(R) ∩ (gr_M(J, R) ∩ K[T_b]) gr_M(R)` for all `μ ≤ μ^{(b)}(J)`, where
`T_b` is the `K`-submodule of `gr¹_M(R)` generated by the classes of `z₁, …, z_{τ_b}` in
`gr¹_M(R)` with `τ_b = τ^{(b)}(J)`.  If `t = t(J)`, a regular system of `t`-th `τ`-parameters
of `R` for `J` will be simply called a *regular system of `τ`-parameters of `R` for `J`*."

Formalization note (encoding): `z : Fin (tau R J a) → maximalIdeal R` (elements of `M`, so their classes
`AssocGraded.mk M 1 (z i) _` in `gr¹_M(R) = M/M²` are defined); "`z₁, …, z_{τ_b}`" are the
`z i` with `(i : ℕ) < tau R J b`, indexed by the subtype `{i // (i : ℕ) < tau R J b}` rather
than by `Fin (tau R J b)` through a cast, so that the definition does not depend on the
inequality `τ_b ≤ τ_a` (\cref{cor:III.lem10-mono}, whose proof is a theorem, not part of the
data).  A regular system of τ-parameters of `R` for `J` is
`IsRegularSystemOfTauParameters R J (t R J) z`. -/
@[blueprint "def:III.7"
  (statement := /-- Let $R$, $M$, $J$, $\mu^*(J)$ and $\tau^*(J)$ be as in \cref{def:III.6}.
    Let $\tau_a=\tau^{(a)}(J)$ for $1\le a\le t=t(J)$. A system of elements
    $(z_1,\dots,z_{\tau_a})$ of $M$ is called a \emph{regular system of $a$-th
    $\tau$-parameters of $R$ for $J$} if, for every positive integer $b\le a$,
    $\operatorname{gr}^\mu_M(J,R)=\operatorname{gr}^\mu_M(R)\cap(\operatorname{gr}_M(J,R)\cap
    K[T_b])\operatorname{gr}_M(R)$ for all $\mu\le\mu^{(b)}(J)$, where $T_b$ is the
    $K$-submodule of $\operatorname{gr}^1_M(R)$ generated by the classes of
    $z_1,\dots,z_{\tau_b}$ in $\operatorname{gr}^1_M(R)$ with $\tau_b=\tau^{(b)}(J)$
    (\cref{def:III.6-property}). If $t=t(J)$, a regular system of $t$-th $\tau$-parameters
    of $R$ for $J$ is simply called a \emph{regular system of $\tau$-parameters of $R$ for
    $J$}. (Definition 7, pp.~222--223.) -/)
  (latexEnv := "definition")]
def IsRegularSystemOfTauParameters (a : ℕ) (z : Fin (tau R J a) → maximalIdeal R) : Prop :=
  ∀ b, 1 ≤ b → b ≤ a →
    IsTauSubmodule R J
      (Submodule.span (R ⧸ maximalIdeal R)
        (Set.range fun i : {i : Fin (tau R J a) // (i : ℕ) < tau R J b} =>
          AssocGraded.mk (maximalIdeal R) 1 (z i.1) (by rw [pow_one]; exact (z i.1).2)))
      (mu R J b)

/-- `(a mod I) · [x Xⁿ] = [ax Xⁿ]` in `gr_I(A)`. -/
private theorem smul_mk {A : Type*} [CommRing A] (I : Ideal A) (n : ℕ) (r x : A)
    (hx : x ∈ I ^ n) :
    (Ideal.Quotient.mk I r) • AssocGraded.mk I n x hx =
      AssocGraded.mk I n (r * x) (Ideal.mul_mem_left _ r hx) := by
  rw [← Ideal.Quotient.algebraMap_eq, IsScalarTower.algebraMap_smul]
  exact (map_smul (AssocGraded.mkLinear I n) r ⟨x, hx⟩).symm

/-- Every element of `grⁿ_I(A)` is the class `[y Xⁿ]` of some `y ∈ Iⁿ`. -/
private theorem exists_mk_eq_of_mem_homogeneous {A : Type*} [CommRing A] (I : Ideal A)
    {n : ℕ} {x : AssocGraded I} (hx : x ∈ AssocGraded.homogeneous I n) :
    ∃ y : A, ∃ hy : y ∈ I ^ n, AssocGraded.mk I n y hy = x := by
  obtain ⟨q, rfl⟩ := LinearMap.mem_range.mp hx
  induction q using Submodule.Quotient.induction_on with
  | H y => exact ⟨y, y.2, rfl⟩

/-- The classes in `gr¹_M(R) = M/M²` of a system of generators of `M` span `gr¹_M(R)`. -/
private theorem homogeneous_one_le_span {g : Set R} (hg : Ideal.span g = maximalIdeal R) :
    AssocGraded.homogeneous (maximalIdeal R) 1 ≤ Submodule.span (R ⧸ maximalIdeal R)
      (Set.range fun y : g => AssocGraded.mk (maximalIdeal R) 1 y.1
        (by rw [pow_one, ← hg]; exact Ideal.subset_span y.2)) := by
  intro x hx
  obtain ⟨y, hy, rfl⟩ := exists_mk_eq_of_mem_homogeneous _ hx
  clear hx
  have hy' : y ∈ Ideal.span g := by rw [hg, ← pow_one (maximalIdeal R)]; exact hy
  induction hy' using Submodule.span_induction with
  | mem y h => exact Submodule.subset_span ⟨⟨y, h⟩, rfl⟩
  | zero =>
    rw [(AssocGraded.mk_eq_zero_iff _ hy).mpr (zero_mem _)]
    exact zero_mem _
  | add x y hx' hy' ihx ihy =>
    have hx1 : x ∈ maximalIdeal R ^ 1 := by rw [pow_one, ← hg]; exact hx'
    have hy1 : y ∈ maximalIdeal R ^ 1 := by rw [pow_one, ← hg]; exact hy'
    rw [AssocGraded.mk_add _ 1 x y hx1 hy1]
    exact add_mem (ihx hx1) (ihy hy1)
  | smul r x hx' ihx =>
    have hx1 : x ∈ maximalIdeal R ^ 1 := by rw [pow_one, ← hg]; exact hx'
    rw [show AssocGraded.mk (maximalIdeal R) 1 (r • x) hy = _ from
      (smul_mk (maximalIdeal R) 1 r x hx1).symm]
    exact Submodule.smul_mem _ _ (ihx hx1)

/-- Generic finset lemma: an injective family `z` with values in a finite set `s` is the initial
segment of an injective enumeration of `s`. -/
private theorem exists_fin_extension {α : Type*} [DecidableEq α] (s : Finset α) {τ : ℕ}
    (z : Fin τ → α) (hz : Function.Injective z) (hzs : ∀ i, z i ∈ s) :
    ∃ (hn : τ ≤ s.card) (y : Fin s.card → α), Function.Injective y ∧ Finset.univ.image y = s ∧
      ∀ i, y (Fin.castLE hn i) = z i := by
  set u : Finset α := Finset.univ.image z with hu
  have hucard : u.card = τ := by
    rw [hu, Finset.card_image_of_injective _ hz, Finset.card_univ, Fintype.card_fin]
  have hus : u ⊆ s := by
    intro x hx
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hx
    exact hzs i
  have hn : τ ≤ s.card := hucard ▸ Finset.card_le_card hus
  set r : Finset α := s \ u with hr
  have hrcard : r.card = s.card - τ := by
    rw [hr, Finset.card_sdiff_of_subset hus, hucard]
  let e : Fin r.card ≃ r := r.equivFin.symm
  let y : Fin s.card → α := fun i =>
    if h : (i : ℕ) < τ then z ⟨i, h⟩ else (e ⟨(i : ℕ) - τ, by have := i.2; omega⟩ : α)
  have hy1 : ∀ (i : Fin s.card) (h : (i : ℕ) < τ), y i = z ⟨i, h⟩ := fun i h => by simp [y, h]
  have hy2 : ∀ (i : Fin s.card) (h : ¬ (i : ℕ) < τ),
      y i = (e ⟨(i : ℕ) - τ, by have := i.2; omega⟩ : α) := fun i h => by simp [y, h]
  have hyz : ∀ i : Fin τ, y (Fin.castLE hn i) = z i := fun i => by
    rw [hy1 _ (by simp)]
    rfl
  have hyr : ∀ (i : Fin s.card) (h : ¬ (i : ℕ) < τ), y i ∈ r := fun i h => by
    rw [hy2 i h]
    exact (e _).2
  have hnot : ∀ i : Fin τ, z i ∉ r := fun i hzr =>
    (Finset.mem_sdiff.mp hzr).2 (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)
  have hyinj : Function.Injective y := by
    intro i j hij
    by_cases hi : (i : ℕ) < τ <;> by_cases hj : (j : ℕ) < τ
    · rw [hy1 i hi, hy1 j hj] at hij
      have := hz hij
      exact Fin.ext (by simpa using congrArg Fin.val this)
    · exact absurd (hij ▸ hyr j hj) (by rw [hy1 i hi]; exact hnot _)
    · exact absurd (hij ▸ hyr i hi) (by rw [hy1 j hj]; exact hnot _)
    · rw [hy2 i hi, hy2 j hj] at hij
      have := e.injective (Subtype.ext hij)
      exact Fin.ext (by have := congrArg Fin.val this; simp at this; omega)
  refine ⟨hn, y, hyinj, ?_, hyz⟩
  apply Finset.Subset.antisymm
  · intro x hx
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hx
    by_cases hi : (i : ℕ) < τ
    · rw [hy1 i hi]
      exact hzs _
    · exact (Finset.mem_sdiff.mp (hyr i hi)).1
  · intro x hx
    by_cases hxu : x ∈ u
    · obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hxu
      exact Finset.mem_image.mpr ⟨Fin.castLE hn i, Finset.mem_univ _, hyz i⟩
    · have hxr : x ∈ r := Finset.mem_sdiff.mpr ⟨hx, hxu⟩
      have hk := (e.symm ⟨x, hxr⟩).2
      refine Finset.mem_image.mpr ⟨⟨τ + (e.symm ⟨x, hxr⟩ : ℕ), by omega⟩, Finset.mem_univ _, ?_⟩
      have h : ¬ (τ + (e.symm ⟨x, hxr⟩ : ℕ) < τ) := by omega
      rw [hy2 _ (by simp)]
      simp

open Classical in
/-- Proof of `IsRegularSystemOfTauParameters.exists_isRegularSystemOfParameters`: the `z_i` are
pairwise distinct and the set `{z_i}` is contained in a regular system of parameters (the
classes of the `z_i` in `gr¹_M(R) = M/M²` are linearly independent, are completed to a basis of
`M/M²`, whose lifts generate `M` by Nakayama's lemma, and their number is `dim R`). -/
private theorem extendsToRSOP_aux (a : ℕ) (ha : 1 ≤ a) (hat : a ≤ t R J)
    (z : Fin (tau R J a) → maximalIdeal R) (hz : IsRegularSystemOfTauParameters R J a z) :
    Function.Injective (fun i => (z i : R)) ∧
      ExtendsToRSOP R (Finset.univ.image fun i => (z i : R)) := by
  -- (the bound `a ≤ t(J)` is not needed)
  have _ := hat
  let _ : Field (R ⧸ maximalIdeal R) := Ideal.Quotient.field _
  -- the classes `w i` of the `z i` in `gr¹_M(R)`
  let w : Fin (tau R J a) → AssocGraded (maximalIdeal R) := fun i =>
    AssocGraded.mk (maximalIdeal R) 1 (z i) (by rw [pow_one]; exact (z i).2)
  have hw1 : ∀ i, w i ∈ AssocGraded.homogeneous (maximalIdeal R) 1 := fun i =>
    AssocGraded.mk_mem_homogeneous _ _
  have hprop : IsTauSubmodule R J (Submodule.span (R ⧸ maximalIdeal R) (Set.range w))
      (mu R J a) := by
    have h := hz a ha le_rfl
    have hr : (Set.range fun i : {i : Fin (tau R J a) // (i : ℕ) < tau R J a} =>
        AssocGraded.mk (maximalIdeal R) 1 (z i.1) (by rw [pow_one]; exact (z i.1).2)) =
        Set.range w := by
      ext x
      constructor
      · rintro ⟨i, rfl⟩
        exact ⟨i.1, rfl⟩
      · rintro ⟨i, rfl⟩
        exact ⟨⟨i, i.2⟩, rfl⟩
    rwa [hr] at h
  -- the `w i` are linearly independent: otherwise a basis of their span would be a system of
  -- fewer than `τ^{(a)}(J)` linear forms with the property (minimality of `τ^{(a)}(J)`)
  have hli : LinearIndependent (R ⧸ maximalIdeal R) w := by
    by_contra hnli
    have hlt : Set.finrank (R ⧸ maximalIdeal R) (Set.range w) < tau R J a := by
      have h1 := finrank_range_le_card (R := R ⧸ maximalIdeal R) w
      have h2 : Fintype.card (Fin (tau R J a)) ≠ Set.finrank _ (Set.range w) := fun h =>
        hnli (linearIndependent_iff_card_eq_finrank_span.mpr h)
      simp only [Fintype.card_fin] at h1 h2
      omega
    let S := Submodule.span (R ⧸ maximalIdeal R) (Set.range w)
    have : FiniteDimensional (R ⧸ maximalIdeal R) S :=
      FiniteDimensional.span_of_finite _ (Set.finite_range w)
    let bS := Module.finBasis (R ⧸ maximalIdeal R) S
    let W' : Fin (Module.finrank _ S) → AssocGraded (maximalIdeal R) := fun i => (bS i : _)
    have hspanW' : Submodule.span (R ⧸ maximalIdeal R) (Set.range W') = S := by
      have : Set.range W' = S.subtype '' Set.range bS := by
        rw [← Set.range_comp]
        rfl
      rw [this, ← Submodule.map_span, bS.span_eq, Submodule.map_subtype_top]
    have hle := tau_le R J W' (fun i => hprop.1 (bS i).2) (by rw [hspanW']; exact hprop)
    exact absurd hle (not_le.mpr hlt)
  -- extend the `w i` to a basis `b` of `gr¹_M(R) = M/M²`
  have hsub : Set.range w ⊆ (AssocGraded.homogeneous (maximalIdeal R) 1 : Set _) := by
    rintro _ ⟨i, rfl⟩
    exact hw1 i
  obtain ⟨b, hb1, hwb, hbspan, hbli⟩ :=
    exists_linearIndepOn_id_extension hli.linearIndepOn_id hsub
  obtain ⟨τ', W, hW⟩ := Submodule.fg_iff_exists_fin_generating_family.mp
    (homogeneous_fg (maximalIdeal R) 1)
  have hbfin : b.Finite := by
    have : Finite b := LinearIndependent.finite_of_le_span_finite
      (fun x : b => (x : AssocGraded (maximalIdeal R))) hbli (Set.range W)
      (by rintro _ ⟨x, rfl⟩; rw [hW]; exact hb1 x.2)
    exact Set.toFinite b
  have hbeq :
      Submodule.span (R ⧸ maximalIdeal R) b = AssocGraded.homogeneous (maximalIdeal R) 1 :=
    le_antisymm (Submodule.span_le.mpr hb1) hbspan
  -- lift the elements of `b` to elements `L x` of `M`, lifting `w i` to `z i`
  have hlift : ∀ x ∈ AssocGraded.homogeneous (maximalIdeal R) 1, ∃ y : R,
      ∃ hy : y ∈ maximalIdeal R ^ 1, AssocGraded.mk (maximalIdeal R) 1 y hy = x :=
    fun x hx => exists_mk_eq_of_mem_homogeneous _ hx
  let L : AssocGraded (maximalIdeal R) → R := fun x =>
    if h : x ∈ Set.range w then (z h.choose : R)
    else if h' : x ∈ AssocGraded.homogeneous (maximalIdeal R) 1 then (hlift x h').choose else 0
  have hL : ∀ x ∈ b, ∃ hy : L x ∈ maximalIdeal R ^ 1,
      AssocGraded.mk (maximalIdeal R) 1 (L x) hy = x := by
    intro x hx
    by_cases h : x ∈ Set.range w
    · simp only [L, dite_eq_left h]
      exact ⟨by rw [pow_one]; exact (z h.choose).2, h.choose_spec⟩
    · have h' : x ∈ AssocGraded.homogeneous (maximalIdeal R) 1 := hb1 hx
      simp only [L, dite_eq_right h, dite_eq_left h']
      exact (hlift x h').choose_spec
  have hLz : ∀ i, L (w i) = z i := by
    intro i
    have h : w i ∈ Set.range w := ⟨i, rfl⟩
    simp only [L, dite_eq_left h]
    rw [hli.injective h.choose_spec]
  have hmk : ∀ (x y : R) (hx : x ∈ maximalIdeal R ^ 1) (hy : y ∈ maximalIdeal R ^ 1), x = y →
      AssocGraded.mk (maximalIdeal R) 1 x hx = AssocGraded.mk (maximalIdeal R) 1 y hy := by
    rintro x y hx hy rfl
    rfl
  have hLinj : Set.InjOn L b := by
    intro x hx x' hx' hxx'
    obtain ⟨hy, hmkx⟩ := hL x hx
    obtain ⟨hy', hmkx'⟩ := hL x' hx'
    rw [← hmkx, ← hmkx']
    exact hmk _ _ hy hy' hxx'
  let s : Finset R := hbfin.toFinset.image L
  have hsM : (s : Set R) ⊆ maximalIdeal R := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
    obtain ⟨hy, -⟩ := hL x (hbfin.mem_toFinset.mp hx)
    rwa [pow_one] at hy
  -- `M = (s)R + M²`: the classes of the elements of `s` span `M/M²`
  have hsup : maximalIdeal R ≤ Ideal.span (s : Set R) ⊔ maximalIdeal R ^ 2 := by
    let π := AssocGraded.mkLinear (maximalIdeal R) 1
    let N₀ : Submodule R ↥(maximalIdeal R ^ 1) := Submodule.comap (maximalIdeal R ^ 1).subtype
      (Ideal.span (s : Set R) ⊔ maximalIdeal R ^ 2)
    have hker : LinearMap.ker π ≤ N₀ := by
      intro y hy
      rw [LinearMap.mem_ker, AssocGraded.mkLinear_apply, AssocGraded.mk_eq_zero_iff] at hy
      exact Submodule.mem_sup_right hy
    have hrange : Submodule.map π ⊤ ≤ Submodule.map π N₀ := by
      rw [Submodule.map_top]
      rintro _ ⟨y, rfl⟩
      have h1 : π y ∈ Submodule.span (R ⧸ maximalIdeal R) b :=
        hbspan (AssocGraded.mk_mem_homogeneous _ y.2)
      have h2 : π y ∈ Submodule.span R b := by
        rw [← Submodule.restrictScalars_span R (R ⧸ maximalIdeal R) Ideal.Quotient.mk_surjective]
        exact h1
      refine Submodule.span_le.mpr ?_ h2
      intro x hx
      obtain ⟨hy, hmkx⟩ := hL x hx
      exact ⟨⟨L x, hy⟩, Submodule.mem_sup_left (Ideal.subset_span
        (Finset.mem_image_of_mem L (hbfin.mem_toFinset.mpr hx))), hmkx⟩
    have hle := (LinearMap.map_le_map_iff π).mp hrange
    rw [sup_eq_left.mpr hker] at hle
    intro m hm
    exact hle (Submodule.mem_top (x := (⟨m, by rwa [pow_one]⟩ : ↥(maximalIdeal R ^ 1))))
  -- Nakayama: `M = (s)R`
  have hspan : Ideal.span (s : Set R) = maximalIdeal R := by
    refine le_antisymm (Ideal.span_le.mpr hsM) ?_
    refine Submodule.le_of_le_smul_of_le_jacobson_bot (IsNoetherian.noetherian _)
      (IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top).symm.le ?_
    rw [Ideal.smul_eq_mul, ← sq]
    exact hsup
  -- counting: `#s = dim_K M/M² = spanFinrank M = dim R`
  have hcard_s : s.card = hbfin.toFinset.card :=
    Finset.card_image_of_injOn (by rw [hbfin.coe_toFinset]; exact hLinj)
  have hcard_b : hbfin.toFinset.card =
      Module.finrank (R ⧸ maximalIdeal R) (AssocGraded.homogeneous (maximalIdeal R) 1) := by
    have : Fintype b := hbfin.fintype
    rw [← hbeq, finrank_span_set_eq_card hbli]
    simp [Set.toFinset_card]
  have hge : (maximalIdeal R).spanFinrank ≤ s.card := by
    have := Submodule.spanFinrank_span_le_ncard_of_finite (R := R) s.finite_toSet
    rw [Set.ncard_coe_finset] at this
    rwa [← hspan]
  have hle : s.card ≤ (maximalIdeal R).spanFinrank := by
    obtain ⟨g, hgcard, hgspan⟩ :=
      (IsNoetherian.noetherian (maximalIdeal R)).exists_span_finset_card_eq_spanFinrank
    have hsp := homogeneous_one_le_span R (g := (g : Set R)) hgspan
    have : FiniteDimensional (R ⧸ maximalIdeal R) (Submodule.span (R ⧸ maximalIdeal R)
        (Set.range fun y : (g : Set R) => AssocGraded.mk (maximalIdeal R) 1 y.1
          (by rw [pow_one, ← hgspan]; exact Ideal.subset_span y.2))) :=
      FiniteDimensional.span_of_finite _ (Set.finite_range _)
    have h1 := Submodule.finrank_mono hsp
    have h2 := finrank_range_le_card (R := R ⧸ maximalIdeal R)
      (fun y : (g : Set R) => AssocGraded.mk (maximalIdeal R) 1 y.1
        (by rw [pow_one, ← hgspan]; exact Ideal.subset_span y.2))
    rw [hcard_s, hcard_b, ← hgcard]
    simp only [Finset.coe_sort_coe, Fintype.card_coe] at h2
    exact h1.trans h2
  have hzinj : Function.Injective (fun i => (z i : R)) := fun i j hij =>
    hli.injective (hmk _ _ _ _ hij)
  refine ⟨hzinj, s, ?_, hspan, ?_⟩
  · intro y hy
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hy
    rw [← hLz i]
    exact Finset.mem_image_of_mem L (hbfin.mem_toFinset.mpr (hwb ⟨i, rfl⟩))
  · rw [le_antisymm hle hge]
    exact IsRegularLocalRing.spanFinrank_maximalIdeal

open Classical in
/-- p. 223: "Note that any regular system of `a`-th `τ`-parameters of `R` for `J` (`1 ≤ a ≤ t`) can
be extended to a regular system of parameters of `R`": the *system* `(z₁, …, z_{τ_a})` is the
initial segment of a regular system of parameters `(y₁, …, y_n)`, `n = dim R`, `y_i = z_i` for
`i ≤ τ_a` (in particular the `z_i` are pairwise distinct).

The paper gives no proof (gap filled).  The classes of the `z_i` in `gr¹_M(R) = M/M²` are linearly
independent over `K` (otherwise a basis of their span would be a system of fewer than `τ_a` linear
forms with the property of Definition 6), hence the `z_i` are distinct; completing them to a basis
of `M/M²` and lifting gives, by Nakayama's lemma, a system of `dim R` generators of `M`
(`extendsToRSOP_aux`), which is enumerated with the `z_i` first.  The bound `a ≤ t(J)` is not
used. -/
@[blueprint "lem:III.7-extends-system"
  (statement := /-- Notation as in \cref{def:III.7}. Let $(z_1,\dots,z_{\tau_a})$ be a regular
    system of $a$-th $\tau$-parameters of $R$ for $J$ ($1\le a\le t$). Then the system
    $(z_1,\dots,z_{\tau_a})$ can be extended to a regular system of parameters of $R$: there is a
    system $(y_1,\dots,y_n)$ of pairwise distinct elements, $n=\dim R$, which is a regular system of
    parameters (\cref{def:rsop}) with $y_i=z_i$ for $i\le\tau_a$. (p.~223.) -/)
  (proof := /-- (The paper gives no proof.) The classes of $z_1,\dots,z_{\tau_a}$ in
    $\operatorname{gr}^1_M(R)=M/M^2$ are linearly independent over $K$: otherwise a $K$-basis of
    their span would be a system of fewer than $\tau_a$ linear forms with the property of
    \cref{def:III.6} up to $\mu^{(a)}(J)$, contradicting the minimality of $\tau_a$; in
    particular the $z_i$ are pairwise distinct. They can be completed to a $K$-basis of $M/M^2$ by
    the classes of elements $z_{\tau_a+1},\dots,z_n$ of $M$, $n=\dim_K M/M^2=\dim R$. Then
    $(z_1,\dots,z_n)$ generates $M$ by Nakayama's lemma and is a regular system of
    parameters of $R$. -/)
  (latexEnv := "lemma")]
theorem IsRegularSystemOfTauParameters.exists_isRegularSystemOfParameters (a : ℕ) (ha : 1 ≤ a)
    (hat : a ≤ t R J) (z : Fin (tau R J a) → maximalIdeal R)
    (hz : IsRegularSystemOfTauParameters R J a z) :
    ∃ (n : ℕ) (hn : tau R J a ≤ n) (y : Fin n → R), Function.Injective y ∧
      (∀ i, y (Fin.castLE hn i) = z i) ∧ IsRegularSystemOfParameters R (Finset.univ.image y) := by
  obtain ⟨hzinj, s, hzs, hs⟩ := extendsToRSOP_aux R J a ha hat z hz
  obtain ⟨hn, y, hyinj, hys, hyz⟩ := exists_fin_extension s (fun i => (z i : R)) hzinj fun i =>
    hzs (Finset.mem_image_of_mem _ (Finset.mem_univ i))
  refine ⟨s.card, hn, y, hyinj, hyz, ?_⟩
  rw [hys]
  exact hs

open Classical in
/-- p. 223: "Note that any regular system of `a`-th `τ`-parameters of `R` for `J` (`1 ≤ a ≤ t`)
can be extended to a regular system of parameters of `R`", in the weaker form in which regular
systems of parameters are finite sets: the set `{z_i}` is contained in a regular system of
parameters (a consequence of `IsRegularSystemOfTauParameters.exists_isRegularSystemOfParameters`,
which records the distinctness of the `z_i`). -/
@[blueprint "lem:III.7-extends"
  (statement := /-- Notation as in \cref{def:III.7}. Any regular system of $a$-th
    $\tau$-parameters of $R$ for $J$ ($1\le a\le t$) can be extended to a regular system of
    parameters of $R$ (\cref{def:rsop}). (p.~223.)

    \textbf{Deviation from the paper (statement modified).} Regular systems of parameters are
    finite sets in Lean, so this statement only says that the set $\{z_1,\dots,z_{\tau_a}\}$ is
    contained in a regular system of parameters; the printed statement, about the system, is
    \cref{lem:III.7-extends-system}. -/)
  (proof := /-- Immediate from \cref{lem:III.7-extends-system}: the set of the $y_i$ contains
    $\{z_1,\dots,z_{\tau_a}\}$. -/)
  (latexEnv := "lemma")]
theorem IsRegularSystemOfTauParameters.extendsToRSOP (a : ℕ) (ha : 1 ≤ a) (hat : a ≤ t R J)
    (z : Fin (tau R J a) → maximalIdeal R) (hz : IsRegularSystemOfTauParameters R J a z) :
    ExtendsToRSOP R (Finset.univ.image fun i => (z i : R)) := by
  obtain ⟨n, hn, y, -, hyz, hy⟩ :=
    IsRegularSystemOfTauParameters.exists_isRegularSystemOfParameters R J a ha hat z hz
  refine ⟨Finset.univ.image y, fun x hx => ?_, hy⟩
  obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hx
  exact Finset.mem_image.mpr ⟨Fin.castLE hn i, Finset.mem_univ _, hyz i⟩

end Definition7

/-! ### Lemma 11 (p. 223) -/

section Lemma11

variable (R : Type u) [CommRing R] [IsRegularLocalRing R] (J : Ideal R)

/-- Every element of the `K`-submodule of `gr¹_M(R)` spanned by the classes of the elements of
an ideal `P` is itself the class of an element of `P`. -/
private theorem mem_span_classes (P : Ideal R) {x : AssocGraded (maximalIdeal R)}
    (hx : x ∈ Submodule.span (R ⧸ maximalIdeal R) {y | ∃ p ∈ P, ∃ hp : p ∈ maximalIdeal R ^ 1,
      AssocGraded.mk (maximalIdeal R) 1 p hp = y}) :
    ∃ p ∈ P, ∃ hp : p ∈ maximalIdeal R ^ 1, AssocGraded.mk (maximalIdeal R) 1 p hp = x := by
  induction hx using Submodule.span_induction with
  | mem y hy => exact hy
  | zero => exact ⟨0, zero_mem _, zero_mem _, (AssocGraded.mk_eq_zero_iff _ _).mpr (zero_mem _)⟩
  | add x y _ _ hx hy =>
    obtain ⟨p, hpP, hp, rfl⟩ := hx
    obtain ⟨q, hqP, hq, rfl⟩ := hy
    exact ⟨p + q, add_mem hpP hqP, add_mem hp hq, AssocGraded.mk_add _ 1 p q hp hq⟩
  | smul c x _ hx =>
    obtain ⟨p, hpP, hp, rfl⟩ := hx
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective c
    exact ⟨r * p, P.mul_mem_left r hpP, Ideal.mul_mem_left _ r hp,
      (smul_mk (maximalIdeal R) 1 r p hp).symm⟩

/-- For `x ∈ Pᵈ`, the class of `x` in `grᵈ_M(R)` lies in the `K`-subalgebra generated by the
classes in `gr¹_M(R)` of the elements of `P` (induction on `d`, `Pᵈ⁺¹ = Pᵈ P`). -/
private theorem mk_mem_adjoin_classes (P : Ideal R) (hPM : P ≤ maximalIdeal R) (d : ℕ) :
    ∀ (x : R) (_ : x ∈ P ^ d) (hx : x ∈ maximalIdeal R ^ d),
      AssocGraded.mk (maximalIdeal R) d x hx ∈ Algebra.adjoin (R ⧸ maximalIdeal R)
        ((Submodule.span (R ⧸ maximalIdeal R) {y | ∃ p ∈ P, ∃ hp : p ∈ maximalIdeal R ^ 1,
          AssocGraded.mk (maximalIdeal R) 1 p hp = y} : Submodule _ _) :
            Set (AssocGraded (maximalIdeal R))) := by
  induction d with
  | zero =>
    intro x _ hx
    rw [mk_zero_eq_algebraMap_mk]
    exact Subalgebra.algebraMap_mem _ _
  | succ d ih =>
    have key : ∀ (x : R) (hxP : x ∈ P ^ d * P), AssocGraded.mk (maximalIdeal R) (d + 1) x
        (Ideal.pow_right_mono hPM (d + 1) (by rwa [pow_succ])) ∈
          Algebra.adjoin (R ⧸ maximalIdeal R)
            ((Submodule.span (R ⧸ maximalIdeal R) {y | ∃ p ∈ P, ∃ hp : p ∈ maximalIdeal R ^ 1,
              AssocGraded.mk (maximalIdeal R) 1 p hp = y} : Submodule _ _) :
                Set (AssocGraded (maximalIdeal R))) := by
      intro x hxP
      induction hxP using Submodule.mul_induction_on' with
      | mem_mul_mem y hy p hp =>
        have hyM : y ∈ maximalIdeal R ^ d := Ideal.pow_right_mono hPM d hy
        have hpM : p ∈ maximalIdeal R ^ 1 := by rw [pow_one]; exact hPM hp
        rw [← mk_mul_mk_eq_mk_add (maximalIdeal R) hyM hpM]
        exact Subalgebra.mul_mem _ (ih y hy hyM)
          (Algebra.subset_adjoin (Submodule.subset_span ⟨p, hp, hpM, rfl⟩))
      | add x hx y hy ihx ihy =>
        rw [AssocGraded.mk_add _ (d + 1) x y (Ideal.pow_right_mono hPM (d + 1) (by rwa [pow_succ]))
          (Ideal.pow_right_mono hPM (d + 1) (by rwa [pow_succ]))]
        exact Subalgebra.add_mem _ ihx ihy
    intro x hxP hx
    exact key x (by rwa [← pow_succ])

/-- A member of a minimal system `S` of generators of `M` lies in `M ∖ M²` (otherwise `S ∖ {z}`
would generate `M`, by Nakayama), so its initial form is its class in `gr¹_M(R)` (p. 223: "the
initial forms of `z₁, …, z_r` in `gr_M(R), which are all forms in `gr¹_M(R)`"). -/
private theorem ordElem_eq_one_of_mem_minimal {S : Finset R}
    (hS : Ideal.span (S : Set R) = maximalIdeal R)
    (hScard : S.card = (maximalIdeal R).spanFinrank) {z : R} (hz : z ∈ S) :
    Ideal.ordElem (maximalIdeal R) z = 1 := by
  classical
  have hzM : z ∈ maximalIdeal R ^ 1 := by
    rw [pow_one, ← hS]
    exact Ideal.subset_span hz
  refine le_antisymm (Ideal.ordElem_le_of_notMem (m := 1) fun hz2 => ?_)
    (by exact_mod_cast Ideal.le_ordElem hzM)
  have h1 := span_erase_eq_of_mem hS hz (Ideal.mem_sup_right hz2)
  have h2 : (maximalIdeal R).spanFinrank ≤ (S.erase z).card := by
    rw [← h1, ← Set.ncard_coe_finset]
    exact Submodule.spanFinrank_span_le_ncard_of_finite (Finset.finite_toSet _)
  have h3 := Finset.card_erase_add_one hz
  omega

/-- The `K`-submodule of `gr¹_M(R)` generated by the initial forms of a minimal base `z₁, …, z_r`
of `P` (a subset of a minimal system of generators of `M`) is the span of the classes in
`gr¹_M(R)` of all elements of `P`. -/
private theorem span_initialForm_eq {S Tz : Finset R}
    (hS : Ideal.span (S : Set R) = maximalIdeal R)
    (hScard : S.card = (maximalIdeal R).spanFinrank) (hTS : Tz ⊆ S) {P : Ideal R}
    (hTP : Ideal.span (Tz : Set R) = P) :
    Submodule.span (R ⧸ maximalIdeal R) (initialForm (maximalIdeal R) '' (Tz : Set R)) =
      Submodule.span (R ⧸ maximalIdeal R) {y | ∃ p ∈ P, ∃ hp : p ∈ maximalIdeal R ^ 1,
        AssocGraded.mk (maximalIdeal R) 1 p hp = y} := by
  have hzM : ∀ z ∈ Tz, z ∈ maximalIdeal R ^ 1 := fun z hz => by
    rw [pow_one, ← hS]
    exact Ideal.subset_span (hTS hz)
  have hinit : ∀ (z : R) (hz : z ∈ Tz), initialForm (maximalIdeal R) z =
      AssocGraded.mk (maximalIdeal R) 1 z (hzM z hz) := fun z hz =>
    initialForm_eq_mk _ (by exact_mod_cast ordElem_eq_one_of_mem_minimal R hS hScard (hTS hz))
  have hPM : ∀ p ∈ Ideal.span (Tz : Set R), p ∈ maximalIdeal R ^ 1 := fun p hp => by
    rw [pow_one, ← hS]
    exact Ideal.span_mono (by exact_mod_cast hTS) hp
  apply le_antisymm
  · refine Submodule.span_le.mpr ?_
    rintro _ ⟨z, hz, rfl⟩
    rw [hinit z hz]
    exact Submodule.subset_span ⟨z, hTP ▸ Ideal.subset_span hz, hzM z hz, rfl⟩
  · have key : ∀ p ∈ Ideal.span (Tz : Set R), ∀ hp : p ∈ maximalIdeal R ^ 1,
        AssocGraded.mk (maximalIdeal R) 1 p hp ∈
          Submodule.span (R ⧸ maximalIdeal R) (initialForm (maximalIdeal R) '' (Tz : Set R)) := by
      intro p hpP
      induction hpP using Submodule.span_induction with
      | mem y h =>
        intro hy
        rw [← hinit y h]
        exact Submodule.subset_span ⟨y, h, rfl⟩
      | zero =>
        intro hy
        rw [(AssocGraded.mk_eq_zero_iff _ _).mpr (zero_mem _)]
        exact zero_mem _
      | add x y hx hy ihx ihy =>
        intro hxy
        rw [AssocGraded.mk_add _ 1 x y (hPM x hx) (hPM y hy)]
        exact add_mem (ihx _) (ihy _)
      | smul r x hx ihx =>
        intro hrx
        rw [show AssocGraded.mk (maximalIdeal R) 1 (r • x) hrx = _ from
          (smul_mk (maximalIdeal R) 1 r x (hPM x hx)).symm]
        exact Submodule.smul_mem _ _ (ihx _)
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨p, hpP, hp, rfl⟩
    rw [← hTP] at hpP
    exact key p hpP hp

/-- A family of vectors adapted to an increasing sequence of finite-dimensional subspaces. -/

private theorem exists_flag_family {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (T : ℕ → Submodule K V) (hT : Monotone T) (hfin : ∀ b, FiniteDimensional K (T b)) (n : ℕ) :
    ∃ w : ℕ → V, ∀ b ≤ n,
      Submodule.span K (w '' Set.Iio (Module.finrank K (T b))) = T b := by
  have hrk : Monotone fun b => Module.finrank K (T b) := fun b b' h => by
    have := hfin b'
    exact Submodule.finrank_mono (hT h)
  induction n with
  | zero =>
    let c := Module.finBasis K (T 0)
    refine ⟨fun i => if h : i < Module.finrank K (T 0) then (c ⟨i, h⟩ : V) else 0, ?_⟩
    intro b hb
    obtain rfl : b = 0 := by omega
    have himg : (fun i => if h : i < Module.finrank K (T 0) then (c ⟨i, h⟩ : V) else 0) ''
        Set.Iio (Module.finrank K (T 0)) = Set.range fun i => (c i : V) := by
      ext x
      constructor
      · rintro ⟨i, hi, rfl⟩
        exact ⟨⟨i, hi⟩, by simp [Set.mem_Iio.mp hi]⟩
      · rintro ⟨i, rfl⟩
        exact ⟨i, i.2, by simp⟩
    rw [himg, show (fun i => (c i : V)) = (T 0).subtype ∘ c from rfl, Set.range_comp,
      Submodule.span_image, c.span_eq, Submodule.map_top, Submodule.range_subtype]
  | succ n ih =>
    obtain ⟨w, hw⟩ := ih
    -- a complement `C` of `T n` in `T (n + 1)`
    obtain ⟨D₀, hD₀⟩ := Submodule.exists_isCompl ((T n).comap (T (n + 1)).subtype)
    set C := D₀.map (T (n + 1)).subtype with hC
    have hCle : C ≤ T (n + 1) := Submodule.map_subtype_le _ _
    have hsup : T n ⊔ C = T (n + 1) := by
      refine le_antisymm (sup_le (hT (Nat.le_succ n)) hCle) fun x hx => ?_
      have hmem : (⟨x, hx⟩ : T (n + 1)) ∈ (T n).comap (T (n + 1)).subtype ⊔ D₀ := by
        rw [hD₀.sup_eq_top]; exact Submodule.mem_top
      obtain ⟨a, ha, d, hd, had⟩ := Submodule.mem_sup.mp hmem
      exact Submodule.mem_sup.mpr ⟨a, ha, d, Submodule.mem_map_of_mem hd,
        by simpa using congrArg Subtype.val had⟩
    have hinf : T n ⊓ C = ⊥ := by
      rw [eq_bot_iff]
      rintro x ⟨hxT, hxC⟩
      obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.mp hxC
      have hy' : y ∈ (T n).comap (T (n + 1)).subtype := hxT
      rw [(Submodule.disjoint_def.mp hD₀.disjoint) y hy' hy]
      exact zero_mem _
    have := hfin (n + 1)
    have hCfin : FiniteDimensional K C := Submodule.finiteDimensional_of_le hCle
    have hrkC : Module.finrank K C =
        Module.finrank K (T (n + 1)) - Module.finrank K (T n) := by
      have h := Submodule.finrank_sup_add_finrank_inf_eq (T n) C
      rw [hsup, hinf, finrank_bot] at h
      omega
    let c := Module.finBasisOfFinrankEq K C hrkC
    set d₀ := Module.finrank K (T n) with hd₀
    set d₁ := Module.finrank K (T (n + 1)) with hd₁
    have hd : d₀ ≤ d₁ := hrk (Nat.le_succ n)
    refine ⟨fun i => if i < d₀ then w i else
      if h : i - d₀ < d₁ - d₀ then (c ⟨i - d₀, h⟩ : V) else 0, fun b hb => ?_⟩
    rcases Nat.lt_or_ge b (n + 1) with hbn | hbn
    · -- the old part of the family is unchanged
      have hbd : Module.finrank K (T b) ≤ d₀ := hrk (by omega)
      refine Eq.trans ?_ (hw b (by omega))
      congr 1
      refine Set.image_congr fun i hi => ?_
      simp [lt_of_lt_of_le (Set.mem_Iio.mp hi) hbd]
    · obtain rfl : b = n + 1 := by omega
      have himg : (fun i => if i < d₀ then w i else
          if h : i - d₀ < d₁ - d₀ then (c ⟨i - d₀, h⟩ : V) else 0) '' Set.Iio d₁ =
          w '' Set.Iio d₀ ∪ Set.range fun i => (c i : V) := by
        ext x
        constructor
        · rintro ⟨i, hi, rfl⟩
          by_cases h0 : i < d₀
          · exact Or.inl ⟨i, h0, by simp [h0]⟩
          · have h1 : i - d₀ < d₁ - d₀ := by rw [Set.mem_Iio] at hi; omega
            exact Or.inr ⟨⟨i - d₀, h1⟩, by simp [h0, h1]⟩
        · rintro (⟨i, hi, rfl⟩ | ⟨i, rfl⟩)
          · exact ⟨i, lt_of_lt_of_le hi hd, by simp [Set.mem_Iio.mp hi]⟩
          · have h0 : ¬ (i + d₀ : ℕ) < d₀ := by omega
            have h1 : (i + d₀ : ℕ) - d₀ < d₁ - d₀ := by have := i.2; omega
            refine ⟨i + d₀, by have := i.2; rw [Set.mem_Iio]; omega, ?_⟩
            simp only [h0, h1, ite_false, dite_true]
            congr 2
            ext
            simp
      rw [himg, Submodule.span_union, hw n le_rfl,
        show (fun i => (c i : V)) = C.subtype ∘ c from rfl, Set.range_comp,
        Submodule.span_image, c.span_eq, Submodule.map_top, Submodule.range_subtype, hsup]


/-- Lemma 11, p. 223: "Let `R`, `M`, and `J` be as above.  Let `P` be a prime ideal in `R` such
that `P ⊇ J` and `R/P` is regular.  Suppose we have a system of elements `(f₁, …, f_m)` of `J`
such that (i) `ν_M(f_j) = ν_P(f_j)` for `1 ≤ j ≤ m`, and (ii) the initial forms of the `f_j`
in `gr_M(R)` generate the ideal `gr_M(J, R)`.  Then we have a regular system of
`τ`-parameters `(z₁, …, z_τ)` of `R` for `J`, where `τ = τ^{(t)}(J)` with `t = t(J)`, such
that `z_j ∈ P` for `1 ≤ j ≤ τ`."

Proof as printed: the proof of p. 223 is followed sentence by sentence.
(1) "Let `(z₁, …, z_r)` be a minimal base of `P`, where `r = dim R − dim R/P`": `exists_finset_span_eq_prime`
(`R/P` regular: `P` is generated by part of a minimal base of `M`).
(2) "Let `T` be the `K`-submodule of `gr¹_M(R)` generated by the initial forms of `z₁, …, z_r` in
`gr_M(R)`, which are all forms in `gr¹_M(R)`": `T` is the span of `initialForm M z`, `z ∈ {z_i}`, and
`ordElem_eq_one_of_mem_minimal` shows that these are forms of degree 1 (`z_i ∈ M ∖ M²`).
(3) "By (i), it is clear that the initial form of `f_j` in `gr_M(R)` belongs to `K[T]`": `f_j ∈ P^d`,
`d = ν_M(f_j) = ν_P(f_j)`, and `T` is the span of the classes of all elements of `P`
(`span_initialForm_eq`, `P = (z₁, …, z_r)`), so `mk_mem_adjoin_classes` applies (induction on `d`).
(4) "Hence by (ii), we have `gr^μ_M(J, R) = gr^μ_M(R) ∩ (gr_M(J, R) ∩ K[T]) gr_M(R)` for all `μ`".
(5) "Hence the `K`-modules `T_i` defined in Lemma 10 are all contained in `T`": `tauSubmodule_le`.
(6) "Since every non-zero element of `T` is the initial form of an element of `P`, the assertion of
the lemma is clear": `mem_span_classes`.  The hypotheses `P ⊇ J` and `f_j ∈ J` are not used in the
printed proof either.

Gap in the paper filled: "the assertion of the lemma is clear" requires choosing the `z_j`
compatibly with the whole flag `T₁ ⊆ … ⊆ T_t` (Definition 7 asks that `z₁, …, z_{τ_b}` span `T_b`
for every `b ≤ t`): the `z_j` are lifts to `P` of a basis of `T_t` adapted to the flag
(`exists_flag_family`). -/
@[blueprint "lem:III.11"
  (statement := /-- Let $R$ be a regular local ring, $M$ its maximal ideal and $J$ an ideal
    in $R$. Let $P$ be a prime ideal in $R$ such that $P\supseteq J$ and $R/P$ is regular.
    Suppose we have a system of elements $(f_1,\dots,f_m)$ of $J$ such that (i)
    $\nu_M(f_j)=\nu_P(f_j)$ for $1\le j\le m$ (\cref{def:II.2-order-element}), and (ii) the
    initial forms of the $f_j$ in $\operatorname{gr}_M(R)$ generate the ideal
    $\operatorname{gr}_M(J,R)$. Then we have a regular system of $\tau$-parameters
    $(z_1,\dots,z_\tau)$ of $R$ for $J$ (\cref{def:III.7}), where $\tau=\tau^{(t)}(J)$ with
    $t=t(J)$, such that $z_j\in P$ for $1\le j\le\tau$. (Lemma 11, p.~223.) -/)
  (proof := /-- Let $(z_1,\dots,z_r)$ be a minimal base of $P$, where $r=\dim R-\dim R/P$.
    Let $T$ be the $K$-submodule of $\operatorname{gr}^1_M(R)$ generated by the initial forms
    of $z_1,\dots,z_r$ in $\operatorname{gr}_M(R)$, which are all forms in
    $\operatorname{gr}^1_M(R)$. By (i), it is clear that the initial form of $f_j$ in
    $\operatorname{gr}_M(R)$ belongs to the $K$-subalgebra $K[T]$ of $\operatorname{gr}_M(R)$
    for all $j$ ($1\le j\le m$). Hence by (ii), we have
    $\operatorname{gr}^\mu_M(J,R)=\operatorname{gr}^\mu_M(R)\cap(\operatorname{gr}_M(J,R)\cap
    K[T])\operatorname{gr}_M(R)$ for all $\mu$. Hence the $K$-modules $T_i$ ($1\le i\le t$)
    defined in Lemma~10 [i.e.\ in the Corollary to Lemma~10, \cref{cor:III.lem10}] are all
    contained in $T$. Since every non-zero element of $T$ is the initial form of an element of
    $P$, the assertion of the lemma is clear.

    \textbf{Formal proof.} The formal proof follows this proof sentence by sentence. A minimal
    base of $P$ is a subset of a minimal base of $M$ ($R/P$ regular), so its elements lie in
    $M\setminus M^2$ and their initial forms are their classes in $\operatorname{gr}^1_M(R)=M/M^2$;
    $T$ is their $K$-span, which is the $K$-span of the classes of all elements of $P$. By (i),
    $f_j\in P^d$ with $d=\nu_M(f_j)$, so its initial form is a polynomial in the classes of
    elements of $P$, i.e.\ lies in $K[T]$. Every element of $T$ is the class of an element of $P$.

    \textbf{Gap in the paper filled.} ``The assertion of the lemma is clear'' requires choosing
    the $z_j$ compatibly with the whole flag $T_1\subseteq\dots\subseteq T_t$ (Definition~7
    asks that $z_1,\dots,z_{\tau_b}$ span $T_b$ for every $b\le t$); Lean picks a basis of
    $T_t$ adapted to this flag and lifts it to $P$. -/)
  (latexEnv := "lemma")]
theorem exists_regularSystemOfTauParameters_mem_prime (P : Ideal R) [P.IsPrime] (hJP : J ≤ P)
    (hP : IsRegularLocalRing (R ⧸ P)) {m : ℕ} (f : Fin m → R) (hf : ∀ j, f j ∈ J)
    (hi : ∀ j, Ideal.ordElem (maximalIdeal R) (f j) = Ideal.ordElem P (f j))
    (hii : Ideal.span (Set.range fun j => initialForm (maximalIdeal R) (f j)) =
      grIdeal (maximalIdeal R) J) :
    ∃ z : Fin (tau R J (t R J)) → maximalIdeal R,
      IsRegularSystemOfTauParameters R J (t R J) z ∧ ∀ j, (z j : R) ∈ P := by
  -- (the hypotheses `J ⊆ P` and `f_j ∈ J` are not used in the printed proof either)
  have _ := hJP
  have _ := hf
  let _ : Field (R ⧸ maximalIdeal R) := Ideal.Quotient.field _
  have hPM : P ≤ maximalIdeal R := le_maximalIdeal (Ideal.IsPrime.ne_top ‹_›)
  -- "Let `(z₁, …, z_r)` be a minimal base of `P`, where `r = dim R − dim R/P`" (`R/P` regular:
  -- it is part of a minimal base of `M`)
  obtain ⟨S, Tz, hSM, hScard, hTS, hTP⟩ := exists_finset_span_eq_prime R P hP
  -- "Let `T` be the `K`-submodule of `gr¹_M(R)` generated by the initial forms of `z₁, …, z_r` in
  -- `gr_M(R)`, which are all forms in `gr¹_M(R)`."
  set T : Submodule (R ⧸ maximalIdeal R) (AssocGraded (maximalIdeal R)) :=
    Submodule.span (R ⧸ maximalIdeal R) (initialForm (maximalIdeal R) '' (Tz : Set R)) with hTdef
  have hT1 : T ≤ AssocGraded.homogeneous (maximalIdeal R) 1 := by
    rw [hTdef, Submodule.span_le]
    rintro _ ⟨z, hz, rfl⟩
    rw [initialForm_eq_mk _ (by exact_mod_cast ordElem_eq_one_of_mem_minimal R hSM hScard (hTS hz))]
    exact AssocGraded.mk_mem_homogeneous _ _
  -- `T` is the span of the classes in `gr¹_M(R)` of all elements of `P`; in particular every
  -- element of `T` is the class (initial form) of an element of `P`
  have hTP' : T = Submodule.span (R ⧸ maximalIdeal R) {y | ∃ p ∈ P, ∃ hp : p ∈ maximalIdeal R ^ 1,
      AssocGraded.mk (maximalIdeal R) 1 p hp = y} := span_initialForm_eq R hSM hScard hTS hTP
  -- "By (i), it is clear that the initial form of `f_j` in `gr_M(R)` belongs to the
  -- `K`-subalgebra `K[T]` of `gr_M(R)` for all `j`": `f_j ∈ P^d`, `d = ν_M(f_j) = ν_P(f_j)`
  have hinK : ∀ j, initialForm (maximalIdeal R) (f j) ∈
      Algebra.adjoin (R ⧸ maximalIdeal R) (T : Set (AssocGraded (maximalIdeal R))) := by
    intro j
    by_cases htop : Ideal.ordElem (maximalIdeal R) (f j) = ⊤
    · rw [initialForm, dite_eq_left htop]
      exact zero_mem _
    · obtain ⟨d, hd⟩ := ENat.ne_top_iff_exists.mp htop
      rw [initialForm_eq_mk _ hd.symm, hTP']
      exact mk_mem_adjoin_classes R P hPM d _
        (Ideal.mem_pow_of_ordElem (by rw [← hi j, ← hd])) _
  -- hence, by (ii), `T` has the property of Definition 6 for all `μ`
  have hTprop : ∀ μ₀, IsTauSubmodule R J T μ₀ := by
    intro μ₀
    refine ⟨hT1, fun μ _ ψ _ => ⟨fun h => ?_, fun h => (Ideal.span_le.mpr fun x hx => hx.1) h⟩⟩
    rw [← hii] at h
    refine Ideal.span_mono ?_ h
    rintro _ ⟨j, rfl⟩
    exact ⟨by rw [SetLike.mem_coe, ← hii]; exact Ideal.subset_span ⟨j, rfl⟩, hinK j⟩
  -- so every `T_a` (Corollary to Lemma 10) is contained in `T`
  have hTa : ∀ a, tauSubmodule R J a ≤ T := fun a => tauSubmodule_le R J a T (hTprop _)
  rcases Nat.eq_zero_or_pos (t R J) with ht0 | ht0
  · -- `t(J) = 0`: nothing to prove
    refine ⟨fun _ => 0, fun b hb hbt => absurd (hb.trans hbt) (by omega), fun _ => zero_mem _⟩
  -- the flag `T₁ ⊆ T₂ ⊆ … ⊆ T_t` and a family `w` adapted to it
  have hmono : ∀ a a', 1 ≤ a → a ≤ a' → a' ≤ t R J → tauSubmodule R J a ≤ tauSubmodule R J a' := by
    intro a a' ha haa' ha't
    induction a', haa' using Nat.le_induction with
    | base => exact le_rfl
    | succ a' haa' ih =>
      exact (ih (by omega)).trans (by
        simpa using (tauSubmodule_mono R J (a' + 1) (by omega) ha't).1)
  have hfin : ∀ a, FiniteDimensional (R ⧸ maximalIdeal R) (tauSubmodule R J a) := by
    intro a
    have : FiniteDimensional (R ⧸ maximalIdeal R) (AssocGraded.homogeneous (maximalIdeal R) 1) :=
      Module.Finite.iff_fg.mpr (homogeneous_fg _ 1)
    exact Submodule.finiteDimensional_of_le ((hTa a).trans hT1)
  obtain ⟨w, hw⟩ := exists_flag_family (fun b => tauSubmodule R J (min (b + 1) (t R J)))
    (fun b b' hbb' => hmono _ _ (by omega) (by omega) (by omega)) (fun b => hfin _) (t R J - 1)
  have hwa : ∀ a, 1 ≤ a → a ≤ t R J → Submodule.span (R ⧸ maximalIdeal R)
      (w '' Set.Iio (tau R J a)) = tauSubmodule R J a := by
    intro a ha hat
    have h := hw (a - 1) (by omega)
    rw [show min (a - 1 + 1) (t R J) = a by omega,
      (tauSubmodule_spec R J a ha hat).2.1] at h
    exact h
  -- lift the `w i`, `i < τ_t`, to elements of `P`
  have hlift : ∀ i : Fin (tau R J (t R J)), ∃ p ∈ P, ∃ hp : p ∈ maximalIdeal R ^ 1,
      AssocGraded.mk (maximalIdeal R) 1 p hp = w i := by
    intro i
    refine mem_span_classes R P (hTP'.le (hTa (t R J) ?_))
    rw [← hwa (t R J) ht0 le_rfl]
    exact Submodule.subset_span ⟨i, i.2, rfl⟩
  choose p hpP hpM hpw using hlift
  refine ⟨fun i => ⟨p i, by simpa using hpM i⟩, fun b hb hbt => ?_, hpP⟩
  have hτ : tau R J b ≤ tau R J (t R J) := by
    rw [← (tauSubmodule_spec R J b hb hbt).2.1, ← (tauSubmodule_spec R J _ ht0 le_rfl).2.1]
    have := hfin (t R J)
    exact Submodule.finrank_mono (hmono b _ hb hbt le_rfl)
  have hrange : (Set.range fun i : {i : Fin (tau R J (t R J)) // (i : ℕ) < tau R J b} =>
      AssocGraded.mk (maximalIdeal R) 1 (p i.1) (by simpa using hpM i.1)) =
      w '' Set.Iio (tau R J b) := by
    ext x
    constructor
    · rintro ⟨⟨i, hi⟩, rfl⟩
      exact ⟨i, hi, (hpw i).symm⟩
    · rintro ⟨i, hi, rfl⟩
      exact ⟨⟨⟨i, lt_of_lt_of_le hi hτ⟩, hi⟩, hpw _⟩
  show IsTauSubmodule R J (Submodule.span (R ⧸ maximalIdeal R) (Set.range fun
    i : {i : Fin (tau R J (t R J)) // (i : ℕ) < tau R J b} =>
      AssocGraded.mk (maximalIdeal R) 1 (p i.1) (by simpa using hpM i.1))) (mu R J b)
  rw [hrange, hwa b hb hbt]
  exact (tauSubmodule_spec R J b hb hbt).1

end Lemma11

/-! ### Separable field extensions (p. 223) -/

section Separable


/-- A local homomorphism is residually separable (\cref{def:III.2-residually}) iff the residue
field of `R'` is a separable extension of that of `R` in the sense of
`IsSeparableFieldExtension`. -/
theorem isResiduallySeparable_iff {R R' : Type u} [CommRing R] [CommRing R'] [IsLocalRing R]
    [IsLocalRing R'] (α : R →+* R') [IsLocalHom α] :
    RingHom.IsResiduallySeparable α ↔
      (letI := (ResidueField.map α).toAlgebra;
        IsSeparableFieldExtension (ResidueField R) (ResidueField R')) :=
  Iff.rfl


/-- p. 223: "An extension of fields, `k'` over `k`, is separable if and only if every `k`-subfield
of finite type of `k'` is separably algebraic over a purely transcendental extension of `k` in
`k'`" (footnote 4: S. MacLane, Modular fields I, Duke Math. J. 5 (1939); Nagata, Local rings,
§39).  The left-hand side is the tensor-product definition of pp. 211–212; on the right, "a
purely transcendental extension of `k` in `k'`" over which `L` is separably algebraic is
`k(x)` for a family `x` of algebraically independent elements of `L`.  Cited leaf (footnote 4). -/
@[blueprint "lem:III.4-separable-characterization"
  (statement := /-- An extension of fields $k'$ over $k$ is separable (in the sense of
    \cref{def:III.2-residually}: for every purely inseparable extension $k''$ of $k$ the
    tensor product $k'\otimes_kk''$ has no nilpotent elements) if and only if every
    $k$-subfield of finite type of $k'$ is separably algebraic over a purely transcendental
    extension of $k$ in $k'$. (p.~223, footnote 4: MacLane, \emph{Modular fields I}, Duke
    Math.\ J.\ 5 (1939), 372--393; Nagata, \emph{Local rings}, \S39.) -/)
  (proof := /-- Cited: MacLane's criterion for separability of arbitrary field extensions
    (Nagata, \emph{Local rings}, Ch.~IV, \S39). -/)
  (latexEnv := "lemma")]
theorem isSeparableFieldExtension_iff [Hironaka.Cited.IsSeparableFieldExtensionIff.{u}] :
    ∀ (K K' : Type u) [Field K] [Field K'] [Algebra K K'],
    IsSeparableFieldExtension K K' ↔
      ∀ L : IntermediateField K K',
        (∃ s : Finset K', L = IntermediateField.adjoin K (s : Set K')) →
        ∃ (ι : Type u) (x : ι → L), AlgebraicIndependent K x ∧
          Algebra.IsSeparable (IntermediateField.adjoin K (Set.range x)) L :=
  @Hironaka.Cited.IsSeparableFieldExtensionIff.isSeparableFieldExtension_iff _

end Separable

/-! ### Lemma 12 (pp. 223–225) -/

section Lemma12Defs

variable (k : Type u) [Field k] {k' : Type u} [Field k'] [Algebra k k'] {n : ℕ}

/-- For a `k'`-submodule `L'` of `k'[X]₁`, the `k`-submodule `L = L' ∩ k[X]₁` of `k[X]₁`
(Lemma 12, p. 223): the elements of `k[X]₁` whose image under the coefficientwise inclusion
`k[X] → k'[X]` lies in `L'`.  Encoded as the preimage of `L'` (restricted to `k`-scalars) under
`MvPolynomial.mapAlgHom (Algebra.ofId k k')`, intersected with `k[X]₁`. -/
noncomputable def linearFormsOver (L' : Submodule k' (MvPolynomial (Fin n) k')) :
    Submodule k (MvPolynomial (Fin n) k) :=
  (L'.restrictScalars k).comap (MvPolynomial.mapAlgHom (σ := Fin n) (Algebra.ofId k k')).toLinearMap
    ⊓ MvPolynomial.homogeneousSubmodule (Fin n) k 1

end Lemma12Defs

/-! ### Auxiliary material for Lemma 12

The proof of Lemma 12 follows the printed proof (pp. 224–225) step by step; every printed step is a
lemma of the section `Lemma12Aux`.  For fields `F ⊆ K`, `HasTauOnlyIf n μ̄ F K` is the only-if part
of the Lemma for the extension `K/F`, for every homogeneous ideal `I` of `F[X]` and every
`K`-submodule `L'` of `K[X]₁`.  The steps, in the printed order:

* the if-part ("clear"): `isTau_map_of_isTau`;
* towers ("it is sufficient to prove the assertion in two cases"): `hasTauOnlyIf_trans`;
* the finitely generated subfield `k₁` ("there exists a subfield `k₁` of `k'` [...]"):
  `exists_fg_isTau`; MacLane's criterion (cited, `isSeparableFieldExtension_iff`) and the reduction to
  the two cases: `hasTauOnlyIf_of_fg`, `hasTauOnlyIf_of_algebraicIndependent`;
* the case `k' = k(u)`: `hasTauOnlyIf_of_transcendental` (the ring `𝔬 = k[u]_{(u)}` and `β`), whose
  proof is `hasTauOnlyIf_of_pid_retraction` with the pieces `pid_exists_adapted_basis` (direct
  summand, base `(Z, Y)`), `pid_mem_span_of_mem_span` (claim (1)), `pid_map_mem_of_map_mem` and
  `pid_linearIndependent_map` (specialization `β`);
* the finite separable case: `hasTauOnlyIf_of_finite_separable` (reduction to Galois) and
  `hasTauOnlyIf_of_isGalois` (invariance of the smallest submodule under the Galois group, Galois
  descent, "without difficulty").

The module-level preamble below collects general facts (existence of the smallest submodule from
Lemma 10, base change of polynomials, ranks) used by several steps. -/

section Lemma12Aux

open MvPolynomial

attribute [local instance] MvPolynomial.gradedAlgebra

section Preamble

variable (n μbar : ℕ)

private theorem homogeneousComponent_map {R R' : Type*} [CommSemiring R] [CommSemiring R']
    (f : R →+* R') (d : ℕ) (p : MvPolynomial (Fin n) R) :
    homogeneousComponent d (map f p) = map f (homogeneousComponent d p) := by
  ext m
  simp only [coeff_homogeneousComponent, coeff_map]
  split_ifs <;> simp

/-- The extension of a homogeneous ideal along a field homomorphism is homogeneous. -/
private theorem isHomogeneous_map {K K' : Type u} [Field K] [Field K'] (f : K →+* K')
    {I : Ideal (MvPolynomial (Fin n) K)} (hI : I.IsHomogeneous (homogeneousSubmodule (Fin n) K)) :
    (I.map (map f)).IsHomogeneous (homogeneousSubmodule (Fin n) K') := by
  intro i r hr
  rw [show ((DirectSum.decompose (homogeneousSubmodule (Fin n) K') r i :
      MvPolynomial (Fin n) K')) = homogeneousComponent i r from
    MvPolynomial.decomposition.decompose'_apply r i]
  have h := homogeneousComponent_mem_span (map f '' (I : Set (MvPolynomial (Fin n) K)))
    (by
      rintro _ ⟨g, hg, rfl⟩ d
      exact ⟨homogeneousComponent d g, homogeneousComponent_mem_of_mem hI hg d,
        (homogeneousComponent_map n f d g).symm⟩) hr i
  exact Ideal.span_mono (fun x hx => hx.1) h

/-- Enlarging a submodule with the property of Definition 6 (inside `G₁`) preserves the property. -/
private theorem isTau_mono {K : Type u} [Field K] {I : Ideal (MvPolynomial (Fin n) K)}
    {L L₂ : Submodule K (MvPolynomial (Fin n) K)} (hL : IsTauSubmoduleMv K n I L μbar)
    (hLL : L ≤ L₂) (hL₂ : L₂ ≤ homogeneousSubmodule (Fin n) K 1) :
    IsTauSubmoduleMv K n I L₂ μbar :=
  isTauSubmoduleMv_mono K n hL hLL hL₂

private theorem finiteDimensional_homogeneousSubmodule_one {K : Type u} [Field K] :
    FiniteDimensional K (homogeneousSubmodule (Fin n) K 1) := by
  rw [homogeneousSubmodule_one_eq_span_X]
  exact FiniteDimensional.span_of_finite K (Set.finite_range _)

private theorem finiteDimensional_of_isTau {K : Type u} [Field K] {I : Ideal (MvPolynomial (Fin n) K)}
    {W : Submodule K (MvPolynomial (Fin n) K)} (hW : IsTauSubmoduleMv K n I W μbar) :
    FiniteDimensional K W := by
  have := finiteDimensional_homogeneousSubmodule_one (K := K) n
  exact Submodule.finiteDimensional_of_le hW.1

private theorem isTau_homogeneousSubmodule_one {K : Type u} [Field K]
    (I : Ideal (MvPolynomial (Fin n) K)) :
    IsTauSubmoduleMv K n I (homogeneousSubmodule (Fin n) K 1) μbar := by
  have htop : Algebra.adjoin K (homogeneousSubmodule (Fin n) K 1 : Set (MvPolynomial (Fin n) K)) =
      ⊤ := by
    rw [eq_top_iff, ← MvPolynomial.adjoin_range_X]
    refine Algebra.adjoin_mono ?_
    rintro _ ⟨i, rfl⟩
    rw [SetLike.mem_coe, homogeneousSubmodule_one_eq_span_X]
    exact Submodule.subset_span ⟨i, rfl⟩
  refine ⟨le_rfl, fun μ _ ψ _ => ⟨fun h => Ideal.subset_span ⟨h, ?_⟩,
    fun h => (Ideal.span_le.mpr fun _ hx => hx.1) h⟩⟩
  rw [SetLike.mem_coe, htop]
  exact Algebra.mem_top

/-- The smallest `K`-submodule of `K[X]₁` with the property of Definition 6 (Lemma 10 and its
Corollary): it exists and lies in every submodule with the property. -/
private theorem exists_min (hμ : 0 < μbar) {K : Type u} [Field K]
    {I : Ideal (MvPolynomial (Fin n) K)}
    (hI : I.IsHomogeneous (homogeneousSubmodule (Fin n) K)) :
    ∃ W₀, IsTauSubmoduleMv K n I W₀ μbar ∧
      ∀ W, IsTauSubmoduleMv K n I W μbar → W₀ ≤ W := by
  classical
  have hex : ∃ d, ∃ W, IsTauSubmoduleMv K n I W μbar ∧ Module.finrank K W = d :=
    ⟨_, _, isTau_homogeneousSubmodule_one n μbar I, rfl⟩
  obtain ⟨W₀, hW₀, hd⟩ := Nat.find_spec hex
  refine ⟨W₀, hW₀, fun W hW => ?_⟩
  have := finiteDimensional_of_isTau n μbar hW₀
  have hinf := isTauSubmoduleMv_inf K n I hI μbar hμ W₀ W hW₀ hW
  have h1 : Module.finrank K (W₀ ⊓ W : Submodule K _) ≤ Module.finrank K W₀ :=
    Submodule.finrank_mono inf_le_left
  have h2 : Nat.find hex ≤ Module.finrank K (W₀ ⊓ W : Submodule K _) :=
    Nat.find_min' hex ⟨_, hinf, rfl⟩
  have : W₀ ⊓ W = W₀ := Submodule.eq_of_le_of_finrank_eq inf_le_left (by omega)
  rw [← this]
  exact inf_le_right

/-- `HasTauOnlyIf n μbar F K`: the only-if part of Lemma 12 for the extension `K/F`, for every
homogeneous ideal `I` of `F[X₁, …, X_n]` and every `K`-submodule `L'` of `K[X]₁`:
if `L'` has the property of Definition 6 for `I K[X]` up to `μ̄`, then `L = L' ∩ F[X]₁` has it for
`I` up to `μ̄`. -/
private def HasTauOnlyIf (F K : Type u) [Field F] [Field K] [Algebra F K] : Prop :=
  ∀ (I : Ideal (MvPolynomial (Fin n) F)), I.IsHomogeneous (homogeneousSubmodule (Fin n) F) →
  ∀ (L' : Submodule K (MvPolynomial (Fin n) K)), L' ≤ homogeneousSubmodule (Fin n) K 1 →
    IsTauSubmoduleMv K n (I.map (MvPolynomial.map (algebraMap F K))) L' μbar →
    IsTauSubmoduleMv F n I (linearFormsOver F L') μbar

/-- Coefficientwise application of a `k`-linear map `λ : k' → k` is an additive map
`k'[X] → k[X]` with `λ(c · b) = λ(c) b` for `b ∈ k[X]`, `c ∈ k'`. -/
private theorem exists_coeffwise {k k' σ : Type*} [Field k] [CommRing k'] [Algebra k k']
    (lam : k' →ₗ[k] k) :
    ∃ Pr : MvPolynomial σ k' →+ MvPolynomial σ k,
      (∀ q m, (Pr q).coeff m = lam (q.coeff m)) ∧
      ∀ (c : k') (b : MvPolynomial σ k),
        Pr (c • MvPolynomial.map (algebraMap k k') b) = lam c • b := by
  let Pr : MvPolynomial σ k' →+ MvPolynomial σ k :=
    { toFun := fun q => AddMonoidAlgebra.ofCoeff (Finsupp.mapRange lam (map_zero lam) q.coeff)
      map_zero' := by
        ext m
        show lam _ = _
        simp
      map_add' := fun q₁ q₂ => by
        ext m
        show lam _ = lam _ + lam _
        simp }
  have hPr : ∀ q m, (Pr q).coeff m = lam (q.coeff m) := fun q m => rfl
  refine ⟨Pr, hPr, fun c b => ?_⟩
  ext m
  rw [hPr, MvPolynomial.coeff_smul, MvPolynomial.coeff_smul, MvPolynomial.coeff_map, smul_eq_mul,
    mul_comm, ← Algebra.smul_def, map_smul, smul_eq_mul, smul_eq_mul, mul_comm]

/-- Linear independence of forms with coefficients in `k` is preserved under extension of the
coefficient field `k → k'`. -/
private theorem linearIndependent_map {k k' σ ι : Type*} [Field k] [Field k'] [Algebra k k']
    [Fintype ι] {v : ι → MvPolynomial σ k} (hv : LinearIndependent k v) :
    LinearIndependent k' fun i => MvPolynomial.map (algebraMap k k') (v i) := by
  rw [Fintype.linearIndependent_iff] at hv ⊢
  intro c hc i
  by_contra hci
  obtain ⟨φ, hφ⟩ : ∃ φ : Module.Dual k k', φ (c i) ≠ 0 := by
    by_contra hall
    push Not at hall
    exact hci ((Module.forall_dual_apply_eq_zero_iff k (c i)).mp hall)
  obtain ⟨Pr, -, hPr⟩ := exists_coeffwise (σ := σ) φ
  have h0 := congrArg Pr hc
  rw [map_sum, map_zero] at h0
  simp only [hPr] at h0
  exact hφ (hv _ h0 i)


/-- `L' ∩ k[X]₁ = L` for the `k'`-span `L'` of a `k`-submodule `L ⊆ k[X]₁` (a `k`-linear
retraction `k' → k` applied coefficientwise). -/
private theorem linearFormsOver_span_map {k k' : Type u} [Field k] [Field k'] [Algebra k k']
    {n : ℕ} (L : Submodule k (MvPolynomial (Fin n) k))
    (hL : L ≤ MvPolynomial.homogeneousSubmodule (Fin n) k 1) :
    linearFormsOver k (Submodule.span k' (MvPolynomial.map (algebraMap k k') ''
      (L : Set (MvPolynomial (Fin n) k)))) = L := by
  refine le_antisymm (fun p hp => ?_) (fun l hl => ⟨?_, hL hl⟩)
  · obtain ⟨hp1, -⟩ := hp
    have hpm : MvPolynomial.map (algebraMap k k') p ∈ Submodule.span k'
        (MvPolynomial.map (algebraMap k k') '' (L : Set (MvPolynomial (Fin n) k))) := hp1
    obtain ⟨π, hπ⟩ := LinearMap.exists_leftInverse_of_injective (Algebra.linearMap k k')
      (LinearMap.ker_eq_bot.mpr (algebraMap k k').injective)
    have hπ1 : π 1 = 1 := by
      have := LinearMap.congr_fun hπ 1
      simpa using this
    obtain ⟨Pr, -, hPr⟩ := exists_coeffwise (σ := Fin n) π
    have key : ∀ y ∈ Submodule.span k' (MvPolynomial.map (algebraMap k k') ''
        (L : Set (MvPolynomial (Fin n) k))), ∀ c : k', Pr (c • y) ∈ L := by
      intro y hy
      induction hy using Submodule.span_induction with
      | mem y hy =>
        obtain ⟨l, hl, rfl⟩ := hy
        intro c
        rw [hPr]
        exact L.smul_mem _ hl
      | zero => intro c; rw [smul_zero, map_zero]; exact zero_mem _
      | add x y _ _ hx hy => intro c; rw [smul_add, map_add]; exact add_mem (hx c) (hy c)
      | smul d x _ hx => intro c; rw [smul_smul]; exact hx (c * d)
    have := key _ hpm 1
    rwa [hPr, hπ1, one_smul] at this
  · show MvPolynomial.map (algebraMap k k') l ∈ Submodule.span k'
      (MvPolynomial.map (algebraMap k k') '' (L : Set (MvPolynomial (Fin n) k)))
    exact Submodule.subset_span ⟨l, hl, rfl⟩


private theorem finrank_span_map_le {F K : Type u} [Field F] [Field K] (f : F →+* K)
    (W : Submodule F (MvPolynomial (Fin n) F)) [FiniteDimensional F W] :
    Module.finrank K (Submodule.span K (map f '' (W : Set (MvPolynomial (Fin n) F)))) ≤
      Module.finrank F W := by
  set b := Module.finBasis F W
  have hle : Submodule.span K (map f '' (W : Set (MvPolynomial (Fin n) F))) ≤
      Submodule.span K (Set.range fun j => map f ((b j : W) : MvPolynomial (Fin n) F)) := by
    rw [Submodule.span_le]
    rintro _ ⟨ℓ, hℓ, rfl⟩
    have hsum := b.sum_repr ⟨ℓ, hℓ⟩
    have : ℓ = ∑ j, (b.repr ⟨ℓ, hℓ⟩ j) • ((b j : W) : MvPolynomial (Fin n) F) := by
      have := congrArg Subtype.val hsum
      simp only [Submodule.coe_sum, Submodule.coe_smul] at this
      exact this.symm
    rw [SetLike.mem_coe, this, map_sum]
    refine Submodule.sum_mem _ fun j _ => ?_
    rw [smul_eq_C_mul, map_mul, map_C, ← smul_eq_C_mul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
  have : FiniteDimensional K
      (Submodule.span K (Set.range fun j => map f ((b j : W) : MvPolynomial (Fin n) F))) :=
    FiniteDimensional.span_of_finite K (Set.finite_range _)
  exact (Submodule.finrank_mono hle).trans ((finrank_range_le_card _).trans (by simp))


end Preamble



section Basic

attribute [local instance] MvPolynomial.gradedAlgebra

variable (n μbar : ℕ)

/-- `map (algebraMap F K) = map (algebraMap E K) ∘ map (algebraMap F E)` for a tower of fields. -/
private theorem map_algebraMap_tower {F E K : Type u} [Field F] [Field E] [Field K] [Algebra F E]
    [Algebra E K] [Algebra F K] [IsScalarTower F E K] (p : MvPolynomial (Fin n) F) :
    MvPolynomial.map (algebraMap F K) p =
      MvPolynomial.map (algebraMap E K) (MvPolynomial.map (algebraMap F E) p) := by
  rw [MvPolynomial.map_map, ← IsScalarTower.algebraMap_eq]

private theorem map_map_algebraMap_tower_ideal {F E K : Type u} [Field F] [Field E] [Field K]
    [Algebra F E] [Algebra E K] [Algebra F K] [IsScalarTower F E K]
    (I : Ideal (MvPolynomial (Fin n) F)) :
    I.map (MvPolynomial.map (algebraMap F K)) =
      (I.map (MvPolynomial.map (algebraMap F E))).map (MvPolynomial.map (algebraMap E K)) := by
  rw [Ideal.map_map]
  congr 1
  exact RingHom.ext fun p => map_algebraMap_tower n p

/-- Lemma 12, p. 224: "The if-part of the assertion is clear."  If `W ⊆ F[X]₁` has the property of
Definition 6 for `I` up to `μ̄`, and `L' ⊆ K[X]₁` contains the image of `W`, then `L'` has the property
for `I' = I K[X]` up to `μ̄`.  (The paper does not argue this step; here: the degree-`μ` part of `I'`
lies in the ideal generated by the images of the homogeneous elements of `I` of degree `≤ μ`, each of
which lies in `(I ∩ F[W]) F[X]` by the property of `W`, and `F[W]` maps into `K[L']`.) -/
private theorem isTau_map_of_isTau {F K : Type u} [Field F] [Field K] [Algebra F K]
    {I : Ideal (MvPolynomial (Fin n) F)} (hI : I.IsHomogeneous (homogeneousSubmodule (Fin n) F))
    {W : Submodule F (MvPolynomial (Fin n) F)} (hW : IsTauSubmoduleMv F n I W μbar)
    {L' : Submodule K (MvPolynomial (Fin n) K)} (hL' : L' ≤ homogeneousSubmodule (Fin n) K 1)
    (hWL : ∀ ℓ ∈ W, MvPolynomial.map (algebraMap F K) ℓ ∈ L') :
    IsTauSubmoduleMv K n (I.map (MvPolynomial.map (algebraMap F K))) L' μbar := by
  refine ⟨hL', fun μ hμ ψ hψ => ⟨fun hψI => ?_, fun h => (Ideal.span_le.mpr fun _ hx => hx.1) h⟩⟩
  -- `map` sends `F[W]` into `K[L']`
  have key : ∀ g ∈ Algebra.adjoin F (W : Set (MvPolynomial (Fin n) F)),
      MvPolynomial.map (algebraMap F K) g ∈ Algebra.adjoin K (L' : Set (MvPolynomial (Fin n) K)) := by
    intro g hg
    induction hg using Algebra.adjoin_induction with
    | mem x hx => exact Algebra.subset_adjoin (hWL x hx)
    | algebraMap r =>
      rw [MvPolynomial.algebraMap_eq, MvPolynomial.map_C, ← MvPolynomial.algebraMap_eq]
      exact Subalgebra.algebraMap_mem _ _
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | mul x y _ _ hx hy => rw [map_mul]; exact Subalgebra.mul_mem _ hx hy
  -- the degree-`μ` part of `I'` lies in the ideal generated by the images of homogeneous `g ∈ I` of
  -- degree `≤ μ`
  have h1 := homogeneousComponent_mem_span
    (MvPolynomial.map (algebraMap F K) '' (I : Set (MvPolynomial (Fin n) F)))
    (by
      rintro _ ⟨g, hg, rfl⟩ d
      exact ⟨homogeneousComponent d g, homogeneousComponent_mem_of_mem hI hg d,
        (homogeneousComponent_map n _ d g).symm⟩) hψI μ
  rw [homogeneousComponent_eq_self hψ] at h1
  refine (Ideal.span_le.mpr ?_) h1
  rintro _ ⟨⟨g, hg, rfl⟩, d, hd, hgd⟩
  -- `g ∈ I_d`, `d ≤ μ ≤ μ̄`
  have hgd' : g ∈ homogeneousSubmodule (Fin n) F d :=
    (mem_homogeneousSubmodule d g).mpr (IsHomogeneous.of_map (algebraMap F K).injective
      ((mem_homogeneousSubmodule d _).mp hgd))
  have h2 := (hW.2 d (hd.trans hμ) g hgd').mp hg
  have h3 := Ideal.mem_map_of_mem (MvPolynomial.map (algebraMap F K)) h2
  rw [Ideal.map_span] at h3
  refine (Ideal.span_le.mpr ?_) h3
  rintro _ ⟨g', ⟨hg'I, hg'W⟩, rfl⟩
  exact Ideal.subset_span ⟨Ideal.mem_map_of_mem _ hg'I, key g' hg'W⟩

/-- Membership in `linearFormsOver` (definitional). -/
private theorem mem_linearFormsOver {k k' : Type u} [Field k] [Field k'] [Algebra k k'] {n : ℕ}
    {L' : Submodule k' (MvPolynomial (Fin n) k')} {ℓ : MvPolynomial (Fin n) k} :
    ℓ ∈ linearFormsOver k L' ↔
      MvPolynomial.map (algebraMap k k') ℓ ∈ L' ∧ ℓ ∈ homogeneousSubmodule (Fin n) k 1 := Iff.rfl

/-- For a tower `F ⊆ E ⊆ K`: `(L' ∩ E[X]₁) ∩ F[X]₁ = L' ∩ F[X]₁`. -/
private theorem linearFormsOver_tower {F E K : Type u} [Field F] [Field E] [Field K] [Algebra F E]
    [Algebra E K] [Algebra F K] [IsScalarTower F E K] (L' : Submodule K (MvPolynomial (Fin n) K)) :
    linearFormsOver F (linearFormsOver E L') = linearFormsOver F L' := by
  ext p
  rw [mem_linearFormsOver, mem_linearFormsOver, mem_linearFormsOver, map_algebraMap_tower n (E := E) (K := K) p]
  constructor
  · rintro ⟨⟨h, -⟩, hp⟩
    exact ⟨h, hp⟩
  · rintro ⟨h, hp⟩
    exact ⟨⟨h, (mem_homogeneousSubmodule 1 _).mpr
      (((mem_homogeneousSubmodule 1 p).mp hp).map _)⟩, hp⟩

/-- Towers: if the only-if part of Lemma 12 holds for `E/F` and for `K/E` then for `K/F`
(p. 224: "it is sufficient to prove the assertion in two cases"; the tower step is not argued in
the paper). -/
private theorem hasTauOnlyIf_trans {F E K : Type u} [Field F] [Field E] [Field K] [Algebra F E]
    [Algebra E K] [Algebra F K] [IsScalarTower F E K]
    (h₁ : HasTauOnlyIf n μbar F E) (h₂ : HasTauOnlyIf n μbar E K) : HasTauOnlyIf n μbar F K := by
  intro I hI L' hL' hP
  have hIE := isHomogeneous_map n (algebraMap F E) hI
  rw [map_map_algebraMap_tower_ideal n (F := F) (E := E) (K := K) I] at hP
  have h := h₂ _ hIE L' hL' hP
  have h' := h₁ I hI (linearFormsOver E L') h.1 h
  rwa [linearFormsOver_tower] at h'

end Basic



section PidBasis

/-- The abstract core of the adapted-basis statement: for an injective `R`-linear map `ι` from a
finite free `R`-module `V` into a `K`-module `VK` (`K = Frac R`, `R` a principal ideal domain) and a
`K`-submodule `W` of `VK` all of whose elements become integral after clearing denominators, there
is a basis `b` of `V` adapted to `L'' = ι⁻¹ W` and `W`.  The paper does not argue this step: it is
the passage from "`L''` is a direct summand" to the base `(Z, Y)`, here for a principal ideal
domain by the Smith normal form of `L'' ⊆ V`. -/
private theorem pidb_core {R K V VK : Type*} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    [Field K] [Algebra R K] [IsFractionRing R K] [AddCommGroup V] [Module R V]
    [AddCommGroup VK] [Module K VK] [Module R VK] [IsScalarTower R K VK] {n : ℕ}
    (bV : Module.Basis (Fin n) R V) (ι : V →ₗ[R] VK) (hι : Function.Injective ι)
    (W : Submodule K VK) (hden : ∀ w ∈ W, ∃ c : R, c ≠ 0 ∧ ∃ v : V, c • w = ι v) :
    ∃ (b : Module.Basis (Fin n) R V) (T : Finset (Fin n)),
      (∀ v : V, ι v ∈ W ↔ v ∈ Submodule.span R (b '' (T : Set (Fin n)))) ∧
      W = Submodule.span K ((fun i => ι (b i)) '' (T : Set (Fin n))) ∧
      Module.finrank K W = T.card := by
  classical
  -- `L''`, the `R`-submodule of `V` of those `v` with `ι v ∈ W`
  set L : Submodule R V := (W.restrictScalars R).comap ι with hL
  have hmemL : ∀ v : V, v ∈ L ↔ ι v ∈ W := fun v => Iff.rfl
  -- saturation: `c • v ∈ L''` with `c ≠ 0` implies `v ∈ L''`
  have hsat : ∀ (c : R), c ≠ 0 → ∀ v : V, c • v ∈ L → v ∈ L := by
    intro c hc v hv
    rw [hmemL, map_smul] at hv
    rw [hmemL]
    have hcK : algebraMap R K c ≠ 0 := by
      simpa using (map_ne_zero_iff _ (IsFractionRing.injective R K)).mpr hc
    have := W.smul_mem (algebraMap R K c)⁻¹ hv
    rwa [← algebraMap_smul K c, smul_smul, inv_mul_cancel₀ hcK, one_smul] at this
  -- a Smith normal form of `L''` in `V`
  obtain ⟨r, snf⟩ := L.smithNormalForm bV
  have ha : ∀ j, snf.a j ≠ 0 := by
    intro j h0
    have h1 := snf.snf j
    rw [h0, zero_smul] at h1
    exact snf.bN.ne_zero j (Subtype.ext h1)
  set b := snf.bM with hb
  set T : Finset (Fin n) := Finset.univ.image snf.f with hT
  -- (i) `L'' = span_R {b_i | i ∈ T}`
  have hLspan : L = Submodule.span R (b '' (T : Set (Fin n))) := by
    apply le_antisymm
    · intro v hv
      have hv' : (⟨v, hv⟩ : L) ∈ Submodule.span R (Set.range snf.bN) := by
        rw [snf.bN.span_eq]; trivial
      have : v ∈ Submodule.map L.subtype (Submodule.span R (Set.range snf.bN)) :=
        ⟨_, hv', rfl⟩
      rw [Submodule.map_span, ← Set.range_comp] at this
      refine Submodule.span_le.mpr ?_ this
      rintro _ ⟨j, rfl⟩
      have h1 : (L.subtype ∘ snf.bN) j = snf.a j • b (snf.f j) := snf.snf j
      rw [h1]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨snf.f j, by simp [hT], rfl⟩)
    · refine Submodule.span_le.mpr ?_
      rintro _ ⟨i, hi, rfl⟩
      obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hi
      refine hsat (snf.a j) (ha j) _ ?_
      rw [← snf.snf j]
      exact (snf.bN j).2
  have hbT : ∀ i ∈ T, ι (b i) ∈ W := by
    intro i hi
    rw [← hmemL, hLspan]
    exact Submodule.subset_span ⟨i, hi, rfl⟩
  -- (ii) `W = span_K {ι (b_i) | i ∈ T}`
  have hWeq : W = Submodule.span K ((fun i => ι (b i)) '' (T : Set (Fin n))) := by
    apply le_antisymm
    · intro w hw
      obtain ⟨c, hc, v, hcv⟩ := hden w hw
      have hcK : algebraMap R K c ≠ 0 := by
        simpa using (map_ne_zero_iff _ (IsFractionRing.injective R K)).mpr hc
      have hvL : v ∈ L := by
        rw [hmemL, ← hcv, ← algebraMap_smul K c]
        exact W.smul_mem _ hw
      rw [hLspan] at hvL
      have h1 : ι v ∈ Submodule.span K ((fun i => ι (b i)) '' (T : Set (Fin n))) := by
        have : ι v ∈ Submodule.map ι (Submodule.span R (b '' (T : Set (Fin n)))) := ⟨v, hvL, rfl⟩
        rw [Submodule.map_span, ← Set.image_comp] at this
        exact Submodule.span_subset_span R K _ this
      have h2 := (Submodule.span K ((fun i => ι (b i)) '' (T : Set (Fin n)))).smul_mem
        (algebraMap R K c)⁻¹ h1
      rwa [← hcv, ← algebraMap_smul K c, smul_smul, inv_mul_cancel₀ hcK, one_smul] at h2
    · refine Submodule.span_le.mpr ?_
      rintro _ ⟨i, hi, rfl⟩
      exact hbT i hi
  refine ⟨b, T, fun v => ?_, hWeq, ?_⟩
  · rw [← hmemL, hLspan]
  -- (iii) `finrank_K W = |T|`: the `ι (b_i)` are `R`-, hence `K`-linearly independent
  · have hli : LinearIndependent K (fun i => ι (b i)) := by
      rw [← LinearIndependent.iff_fractionRing R K]
      exact LinearIndependent.map' b.linearIndependent ι (LinearMap.ker_eq_bot.mpr hι)
    have hliT : LinearIndependent K (fun i : T => ι (b i)) :=
      hli.comp _ Subtype.val_injective
    have hcard := finrank_span_eq_card hliT
    rw [Fintype.card_coe] at hcard
    rw [hWeq, Set.image_eq_range]
    exact hcard

/-- `R[X]₁` is a free `R`-module with basis the variables `X_i`, `i ∈ Fin n`. -/
private theorem pidb_nonempty_basis (R : Type*) [CommRing R] [Nontrivial R] (n : ℕ) :
    Nonempty (Module.Basis (Fin n) R (homogeneousSubmodule (Fin n) R 1)) :=
  ⟨(Module.Basis.span (MvPolynomial.linearIndependent_X (Fin n) R)).map
    (LinearEquiv.ofEq _ _ (homogeneousSubmodule_one_eq_span_X (σ := Fin n) (R := R)).symm)⟩

/-- Every `K`-linear form `w ∈ K[X]₁`, `K = Frac R`, has a nonzero multiple `c • w` with `c ∈ R`
lying in (the image of) `R[X]₁`: clear the denominators of the coefficients of `w` with respect
to the variables `X_i`.  The paper does not argue this step. -/
private theorem pidb_exists_smul_mem {R K : Type*} [CommRing R] [IsDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K] {n : ℕ} (w : MvPolynomial (Fin n) K)
    (hw : w ∈ homogeneousSubmodule (Fin n) K 1) :
    ∃ c : R, c ≠ 0 ∧ ∃ v : homogeneousSubmodule (Fin n) R 1,
      c • w = MvPolynomial.map (algebraMap R K) (v : MvPolynomial (Fin n) R) := by
  rw [homogeneousSubmodule_one_eq_span_X, Submodule.mem_span_range_iff_exists_fun] at hw
  obtain ⟨d, rfl⟩ := hw
  obtain ⟨c, hc⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors R)
    (S := K) d
  choose a ha using hc
  refine ⟨(c : R), nonZeroDivisors.coe_ne_zero c, ⟨∑ i, a i • X i, ?_⟩, ?_⟩
  · rw [homogeneousSubmodule_one_eq_span_X]
    exact Submodule.sum_mem _ fun i _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  · simp only [map_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← smul_assoc, ← ha i]
    simp [smul_eq_C_mul]
    rw [Algebra.smul_def, MvPolynomial.algebraMap_apply]

/-- P1.  Lemma 12, p. 224: "Since `𝔬` is a valuation ring, `L''` must be a direct summand of the free
`𝔬`-module `𝔬[X]₁`.  Let `(Z₁, …, Z_r)` be an `𝔬`-free base of `L''`, and let us extend it to an `𝔬`-free
base `(Z₁, …, Z_r, Y₁, …, Y_s)` of `𝔬[X]₁`.  Then `r + s = n` and `𝔬[X] = 𝔬[Z, Y]`."
Here `L'' = W ∩ 𝔬[X]₁`; the base `b` of `𝔬[X]₁` is indexed by `Fin n`, `T` is the set of indices of the
`Z_j`.  (`𝔬 = R` is a principal ideal domain with fraction field `K`.)  The paper's "direct summand"
is replaced by the Smith normal form of `L'' ⊆ 𝔬[X]₁` over the principal ideal domain `R`
(`pidb_core`); the paper does not argue that the resulting base can be taken adapted to `L''`
with `W` the `K`-span of its first `r` members, nor that `r = dim_K W`. -/
private theorem pid_exists_adapted_basis {R K : Type u} [CommRing R] [IsDomain R]
    [IsPrincipalIdealRing R] [Field K] [Algebra R K] [IsFractionRing R K] {n : ℕ}
    (W : Submodule K (MvPolynomial (Fin n) K)) (hW : W ≤ homogeneousSubmodule (Fin n) K 1) :
    ∃ (b : Module.Basis (Fin n) R (homogeneousSubmodule (Fin n) R 1)) (T : Finset (Fin n)),
      (∀ v : homogeneousSubmodule (Fin n) R 1,
        MvPolynomial.map (algebraMap R K) (v : MvPolynomial (Fin n) R) ∈ W ↔
          v ∈ Submodule.span R ((fun i => b i) '' (T : Set (Fin n)))) ∧
      W = Submodule.span K ((fun i => MvPolynomial.map (algebraMap R K)
        ((b i : homogeneousSubmodule (Fin n) R 1) : MvPolynomial (Fin n) R)) '' (T : Set (Fin n))) ∧
      Module.finrank K W = T.card := by
  classical
  obtain ⟨bV⟩ := pidb_nonempty_basis R n
  -- the coefficient extension `R[X]₁ → K[X]`
  let ι : homogeneousSubmodule (Fin n) R 1 →ₗ[R] MvPolynomial (Fin n) K :=
    (MvPolynomial.mapAlgHom (Algebra.ofId R K)).toLinearMap ∘ₗ
      (homogeneousSubmodule (Fin n) R 1).subtype
  have hιapp : ∀ v, ι v = MvPolynomial.map (algebraMap R K) (v : MvPolynomial (Fin n) R) :=
    fun v => rfl
  have hι : Function.Injective ι := fun x y h =>
    Subtype.ext (MvPolynomial.map_injective _ (IsFractionRing.injective R K) h)
  have hden : ∀ w ∈ W, ∃ c : R, c ≠ 0 ∧ ∃ v, c • w = ι v := fun w hw =>
    pidb_exists_smul_mem w (hW hw)
  exact pidb_core bV ι hι W hden

end PidBasis



section PidCoord

/-- The standard `R`-basis `X₁, …, X_n` of the free module `R[X]₁` of linear forms. -/
private noncomputable def pidc_stdBasis (R : Type u) [CommRing R] (n : ℕ) :
    Module.Basis (Fin n) R (homogeneousSubmodule (Fin n) R 1) :=
  (Module.Basis.span (linearIndependent_X (σ := Fin n) (R := R))).map
    (LinearEquiv.ofEq _ _ homogeneousSubmodule_one_eq_span_X.symm)

private theorem pidc_stdBasis_apply {R : Type u} [CommRing R] {n : ℕ} (i : Fin n) :
    ((pidc_stdBasis R n i : homogeneousSubmodule (Fin n) R 1) : MvPolynomial (Fin n) R) = X i := by
  simp [pidc_stdBasis, Module.Basis.span_apply]

/-- Substituting `X_i ↦ w (X_i)` for an `R`-linear endomorphism `w` of `R[X]₁` acts on a linear form
`v` as `w`. -/
private theorem pidc_aeval_stdBasis_apply {R : Type u} [CommRing R] {n : ℕ}
    (w : homogeneousSubmodule (Fin n) R 1 →ₗ[R] homogeneousSubmodule (Fin n) R 1)
    (v : homogeneousSubmodule (Fin n) R 1) :
    aeval (fun i => ((w (pidc_stdBasis R n i) : homogeneousSubmodule (Fin n) R 1) :
        MvPolynomial (Fin n) R)) (v : MvPolynomial (Fin n) R) =
      ((w v : homogeneousSubmodule (Fin n) R 1) : MvPolynomial (Fin n) R) := by
  set c := pidc_stdBasis R n
  conv_lhs => rw [← c.sum_repr v]
  conv_rhs => rw [← c.sum_repr v]
  simp only [map_sum, map_smul, Submodule.coe_sum, Submodule.coe_smul]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hci : ((c i : homogeneousSubmodule (Fin n) R 1) : MvPolynomial (Fin n) R) = X i :=
    pidc_stdBasis_apply i
  rw [hci, aeval_X]

/-- Step (a) of the printed chain, over `𝔬 = R`: the substitution `X_i ↦ b_i` (change of variables
`𝔬[X] = 𝔬[Z, Y]`) has a two-sided inverse on generators.  The paper does not argue this step. -/
private theorem pidc_exists_inverse {R : Type u} [CommRing R] {n : ℕ}
    (b : Module.Basis (Fin n) R (homogeneousSubmodule (Fin n) R 1)) :
    ∃ ψ : MvPolynomial (Fin n) R →ₐ[R] MvPolynomial (Fin n) R,
      (∀ i, ψ ((b i : homogeneousSubmodule (Fin n) R 1) : MvPolynomial (Fin n) R) = X i) ∧
      ∀ i, aeval (fun j => ((b j : homogeneousSubmodule (Fin n) R 1) : MvPolynomial (Fin n) R))
        (ψ (X i)) = X i := by
  let u : homogeneousSubmodule (Fin n) R 1 ≃ₗ[R] homogeneousSubmodule (Fin n) R 1 :=
    (pidc_stdBasis R n).equiv b (Equiv.refl _)
  have hu : ∀ i, u (pidc_stdBasis R n i) = b i := fun i => by simp [u]
  have hu' : ∀ i, u.symm (b i) = pidc_stdBasis R n i := fun i => by
    rw [LinearEquiv.symm_apply_eq, hu]
  refine ⟨aeval (fun i => ((u.symm (pidc_stdBasis R n i) : homogeneousSubmodule (Fin n) R 1) :
    MvPolynomial (Fin n) R)), fun i => ?_, fun i => ?_⟩
  · have := pidc_aeval_stdBasis_apply (u.symm : _ →ₗ[R] _) (b i)
    simp only [LinearEquiv.coe_coe] at this
    rw [this, hu', pidc_stdBasis_apply]
  · have h2 := pidc_aeval_stdBasis_apply (u : _ →ₗ[R] _) (u.symm (pidc_stdBasis R n i))
    simp only [LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply, hu] at h2
    rw [aeval_X]
    exact h2.trans (pidc_stdBasis_apply i)

/-- The coordinates `𝔬[X] = 𝔬[Z, Y]` as a ring homomorphism: `Z`-variables (indices in `T`) become
constants in `A[X_T]`, the other variables stay variables. -/
private noncomputable def pidc_split (A : Type u) [CommRing A] {n : ℕ} (T : Finset (Fin n)) :
    MvPolynomial (Fin n) A →ₐ[A] MvPolynomial {i : Fin n // i ∉ T} (MvPolynomial ↥T A) :=
  aeval (fun i => if h : i ∈ T then C (X ⟨i, h⟩) else X ⟨i, h⟩)

/-- The inclusion `A[X_T] → A[X]`. -/
private noncomputable def pidc_incl (A : Type u) [CommRing A] {n : ℕ} (T : Finset (Fin n)) :
    MvPolynomial ↥T A →ₐ[A] MvPolynomial (Fin n) A :=
  rename Subtype.val

/-- The inverse of `pidc_split` (as a ring homomorphism). -/
private noncomputable def pidc_glue (A : Type u) [CommRing A] {n : ℕ} (T : Finset (Fin n)) :
    MvPolynomial {i : Fin n // i ∉ T} (MvPolynomial ↥T A) →+* MvPolynomial (Fin n) A :=
  eval₂Hom (pidc_incl A T : MvPolynomial ↥T A →+* MvPolynomial (Fin n) A) (fun y => X y.1)

section Split

variable {A : Type u} [CommRing A] {n : ℕ} (T : Finset (Fin n))

private theorem pidc_split_X_of_mem {i : Fin n} (h : i ∈ T) :
    pidc_split A T (X i) = C (X ⟨i, h⟩) := by
  simp [pidc_split, h]

private theorem pidc_split_X_of_not_mem {i : Fin n} (h : i ∉ T) :
    pidc_split A T (X i) = X ⟨i, h⟩ := by
  simp [pidc_split, h]

/-- In the coordinates `𝔬[Z, Y]`, a polynomial in the `Z` alone is a constant. -/
private theorem pidc_split_incl (p : MvPolynomial ↥T A) :
    pidc_split A T (pidc_incl A T p) = C p := by
  have : (pidc_split A T).toRingHom.comp (pidc_incl A T).toRingHom = C := by
    refine ringHom_ext (fun a => ?_) (fun t => ?_)
    · simp [pidc_incl]
    · simp [pidc_incl, pidc_split_X_of_mem T t.2]
  exact RingHom.congr_fun this p

private theorem pidc_glue_C (p : MvPolynomial ↥T A) : pidc_glue A T (C p) = pidc_incl A T p := by
  simp [pidc_glue]

/-- The change of coordinates `pidc_split` has `pidc_glue` as a left inverse. -/
private theorem pidc_glue_split (x : MvPolynomial (Fin n) A) :
    pidc_glue A T (pidc_split A T x) = x := by
  have : (pidc_glue A T).comp (pidc_split A T).toRingHom = RingHom.id _ := by
    refine ringHom_ext (fun a => ?_) (fun i => ?_)
    · simp [pidc_glue, pidc_incl]
    · by_cases h : i ∈ T
      · simp [pidc_split_X_of_mem T h, pidc_glue, pidc_incl]
      · simp [pidc_split_X_of_not_mem T h, pidc_glue]
  exact RingHom.congr_fun this x

private theorem pidc_split_map {B : Type u} [CommRing B] (φ : A →+* B) (x : MvPolynomial (Fin n) A) :
    pidc_split B T (map φ x) = map (map φ) (pidc_split A T x) := by
  have : (pidc_split B T).toRingHom.comp (map φ) =
      (map (map φ)).comp (pidc_split A T).toRingHom := by
    refine ringHom_ext (fun a => ?_) (fun i => ?_)
    · simp
    · by_cases h : i ∈ T
      · simp [pidc_split_X_of_mem T h]
      · simp [pidc_split_X_of_not_mem T h]
  exact RingHom.congr_fun this x

end Split

section Base

variable {R K : Type u} [CommRing R] [CommRing K] [Algebra R K] {n : ℕ}

/-- The inverse substitution `ψ`, base-changed from `𝔬` to the field of fractions. -/
private noncomputable def pidc_psiK (ψ : MvPolynomial (Fin n) R →ₐ[R] MvPolynomial (Fin n) R) :
    MvPolynomial (Fin n) K →ₐ[K] MvPolynomial (Fin n) K :=
  aeval (fun i => map (algebraMap R K) (ψ (X i)))

private theorem pidc_psiK_map (ψ : MvPolynomial (Fin n) R →ₐ[R] MvPolynomial (Fin n) R)
    (x : MvPolynomial (Fin n) R) :
    pidc_psiK (K := K) ψ (map (algebraMap R K) x) = map (algebraMap R K) (ψ x) := by
  have : (pidc_psiK (K := K) ψ).toRingHom.comp (map (algebraMap R K)) =
      (map (algebraMap R K)).comp ψ.toRingHom := by
    refine ringHom_ext (fun r => ?_) (fun i => ?_)
    · have : ψ (C r) = C r := by
        rw [← MvPolynomial.algebraMap_eq]; exact ψ.commutes r
      simp [pidc_psiK, this]
    · simp [pidc_psiK]
  exact RingHom.congr_fun this x

/-- The `𝔬`-algebra `𝔬[Z] = 𝔬[X_T] → 𝔬[X]`, `Z_t ↦ b_t`. -/
private noncomputable def pidc_kappaR
    (b : Module.Basis (Fin n) R (homogeneousSubmodule (Fin n) R 1)) (T : Finset (Fin n)) :
    MvPolynomial ↥T R →ₐ[R] MvPolynomial (Fin n) R :=
  aeval (fun t : ↥T => ((b t.1 : homogeneousSubmodule (Fin n) R 1) : MvPolynomial (Fin n) R))

/-- The `K`-algebra `K[Z] = K[X_T] → K[X]`, `Z_t ↦ b_t`. -/
private noncomputable def pidc_kappaK
    (b : Module.Basis (Fin n) R (homogeneousSubmodule (Fin n) R 1)) (T : Finset (Fin n)) :
    MvPolynomial ↥T K →ₐ[K] MvPolynomial (Fin n) K :=
  aeval (fun t : ↥T => map (algebraMap R K)
    ((b t.1 : homogeneousSubmodule (Fin n) R 1) : MvPolynomial (Fin n) R))

private theorem pidc_kappaK_map
    (b : Module.Basis (Fin n) R (homogeneousSubmodule (Fin n) R 1)) (T : Finset (Fin n))
    (p : MvPolynomial ↥T R) :
    map (algebraMap R K) (pidc_kappaR b T p) =
      pidc_kappaK (K := K) b T (map (algebraMap R K) p) := by
  have : (map (algebraMap R K)).comp (pidc_kappaR b T).toRingHom =
      (pidc_kappaK (K := K) b T).toRingHom.comp (map (algebraMap R K)) := by
    refine ringHom_ext (fun r => ?_) (fun t => ?_)
    · simp [pidc_kappaR, pidc_kappaK]
    · simp [pidc_kappaR, pidc_kappaK]
  exact RingHom.congr_fun this p

/-- `ψ` carries the `Z`-polynomials `κ p` back to `p` in the standard coordinates. -/
private theorem pidc_psiK_kappaK
    (b : Module.Basis (Fin n) R (homogeneousSubmodule (Fin n) R 1)) (T : Finset (Fin n))
    (ψ : MvPolynomial (Fin n) R →ₐ[R] MvPolynomial (Fin n) R)
    (hψ : ∀ i, ψ ((b i : homogeneousSubmodule (Fin n) R 1) : MvPolynomial (Fin n) R) = X i)
    (p : MvPolynomial ↥T K) :
    pidc_psiK ψ (pidc_kappaK b T p) = pidc_incl K T p := by
  have : ((pidc_psiK (K := K) ψ).comp (pidc_kappaK b T) : MvPolynomial ↥T K →ₐ[K] _) =
      pidc_incl K T := by
    refine algHom_ext (fun t => ?_)
    simp [pidc_kappaK, pidc_incl, pidc_psiK_map, hψ]
  exact AlgHom.congr_fun this p

private theorem pidc_theta_incl
    (b : Module.Basis (Fin n) R (homogeneousSubmodule (Fin n) R 1)) (T : Finset (Fin n))
    (p : MvPolynomial ↥T R) :
    aeval (fun i => ((b i : homogeneousSubmodule (Fin n) R 1) : MvPolynomial (Fin n) R))
      (pidc_incl R T p) = pidc_kappaR b T p := by
  unfold pidc_incl pidc_kappaR
  rw [aeval_rename]
  rfl

private theorem pidc_adjoin_eq_range_kappaR
    (b : Module.Basis (Fin n) R (homogeneousSubmodule (Fin n) R 1)) (T : Finset (Fin n)) :
    Algebra.adjoin R ((fun i => ((b i : homogeneousSubmodule (Fin n) R 1) :
      MvPolynomial (Fin n) R)) '' (T : Set (Fin n))) = (pidc_kappaR b T).range := by
  rw [pidc_kappaR, ← Algebra.adjoin_range_eq_range_aeval, Set.image_eq_range]
  rfl

private theorem pidc_adjoin_eq_range_kappaK
    (b : Module.Basis (Fin n) R (homogeneousSubmodule (Fin n) R 1)) (T : Finset (Fin n)) :
    Algebra.adjoin K ((fun i => map (algebraMap R K)
      ((b i : homogeneousSubmodule (Fin n) R 1) : MvPolynomial (Fin n) R)) '' (T : Set (Fin n))) =
      (pidc_kappaK (K := K) b T).range := by
  rw [pidc_kappaK, ← Algebra.adjoin_range_eq_range_aeval, Set.image_eq_range]
  rfl

end Base

/-- P2.  Lemma 12, p. 224, the chain of equalities proving (1): with `J = I'`,
"`(I' ∩ k'[L'])k'[X] ∩ 𝔬[X] = (I' ∩ k'[Z])k'[Z, Y] ∩ 𝔬[Z, Y] = (I' ∩ k'[Z] ∩ 𝔬[Z])𝔬[Z, Y] =
(I' ∩ 𝔬[Z, Y] ∩ 𝔬[Z])𝔬[Z, Y] = (I'' ∩ 𝔬[Z])𝔬[Z, Y] = (I'' ∩ 𝔬[L''])𝔬[X]`", for `f ∈ 𝔬[X]`.
Here `(Z_j)_{j ∈ T}` are `b i`, `i ∈ T`, and `I'' ∩ 𝔬[X]` is `{g | map g ∈ J}`; `k'[L'] = k'[Z]` is
`Algebra.adjoin K (map '' b_T)`.

The paper does not argue the change of variables `𝔬[X] = 𝔬[Z, Y]` or the coefficient criterion
(an element `Σ_β f_β(Z) Y^β` lies in the extension of an ideal `I'` of `k'[Z]` iff every `f_β` lies in
`I'`); both are proved here (`pidc_exists_inverse`, `MvPolynomial.mem_map_C_iff`). -/
private theorem pid_mem_span_of_mem_span {R K : Type u} [CommRing R] [Field K] [Algebra R K]
    [FaithfulSMul R K] {n : ℕ} (b : Module.Basis (Fin n) R (homogeneousSubmodule (Fin n) R 1))
    (T : Finset (Fin n)) (J : Ideal (MvPolynomial (Fin n) K)) (f : MvPolynomial (Fin n) R)
    (hf : MvPolynomial.map (algebraMap R K) f ∈ Ideal.span ((J : Set (MvPolynomial (Fin n) K)) ∩
      (Algebra.adjoin K ((fun i => MvPolynomial.map (algebraMap R K)
        ((b i : homogeneousSubmodule (Fin n) R 1) : MvPolynomial (Fin n) R)) '' (T : Set (Fin n))) :
          Set (MvPolynomial (Fin n) K)))) :
    f ∈ Ideal.span ({g : MvPolynomial (Fin n) R | MvPolynomial.map (algebraMap R K) g ∈ J} ∩
      (Algebra.adjoin R ((fun i => ((b i : homogeneousSubmodule (Fin n) R 1) :
        MvPolynomial (Fin n) R)) '' (T : Set (Fin n))) : Set (MvPolynomial (Fin n) R))) := by
  classical
  -- (a) "Then `r + s = n` and `𝔬[X] = 𝔬[Z, Y]`": the substitution `X_i ↦ b_i` is invertible
  obtain ⟨ψ, hψb, hbψ⟩ := pidc_exists_inverse b
  have hθψ : ∀ x, aeval (fun j => ((b j : homogeneousSubmodule (Fin n) R 1) :
      MvPolynomial (Fin n) R)) (ψ x) = x := by
    intro x
    have : (aeval (fun j => ((b j : homogeneousSubmodule (Fin n) R 1) :
        MvPolynomial (Fin n) R))).comp ψ = AlgHom.id R _ :=
      algHom_ext fun i => by simpa using hbψ i
    exact AlgHom.congr_fun this x
  -- `I' ∩ k'[Z]` as an ideal `JK` of `k'[Z]`, and `I'' ∩ 𝔬[Z]` as the ideal `JR` of `𝔬[Z]`
  let JK : Ideal (MvPolynomial ↥T K) := Ideal.comap (pidc_kappaK (K := K) b T).toRingHom J
  let JR : Ideal (MvPolynomial ↥T R) := Ideal.comap (map (algebraMap R K)) JK
  -- hypothesis `f ∈ (I' ∩ k'[Z])k'[Z, Y]`, read in the coordinates `Z, Y`
  have h3 : pidc_split K T (pidc_psiK ψ (map (algebraMap R K) f)) ∈
      Ideal.map (C : MvPolynomial ↥T K →+*
        MvPolynomial {i : Fin n // i ∉ T} (MvPolynomial ↥T K)) JK := by
    have hmem := Ideal.mem_map_of_mem
      ((pidc_split K T).toRingHom.comp (pidc_psiK (K := K) ψ).toRingHom) hf
    rw [Ideal.map_span] at hmem
    refine (Ideal.span_le.mpr ?_) hmem
    rintro _ ⟨z, ⟨hzJ, hzA⟩, rfl⟩
    rw [SetLike.mem_coe, pidc_adjoin_eq_range_kappaK] at hzA
    obtain ⟨p, rfl⟩ := hzA
    have hp : p ∈ JK := hzJ
    have := Ideal.mem_map_of_mem (C : MvPolynomial ↥T K →+*
      MvPolynomial {i : Fin n // i ∉ T} (MvPolynomial ↥T K)) hp
    simpa [pidc_psiK_kappaK b T ψ hψb, pidc_split_incl] using this
  -- (b) "`(I' ∩ k'[Z])k'[Z, Y] ∩ 𝔬[Z, Y] = (I' ∩ k'[Z] ∩ 𝔬[Z])𝔬[Z, Y]`": every `Y`-coefficient of
  -- `f` lies in `I' ∩ k'[Z]` and in `𝔬[Z]`, i.e. in `JR`
  have h4 : pidc_split K T (pidc_psiK ψ (map (algebraMap R K) f)) =
      map (map (algebraMap R K)) (pidc_split R T (ψ f)) := by
    rw [pidc_psiK_map, pidc_split_map]
  have h5 : pidc_split R T (ψ f) ∈
      Ideal.map (C : MvPolynomial ↥T R →+*
        MvPolynomial {i : Fin n // i ∉ T} (MvPolynomial ↥T R)) JR := by
    rw [h4, MvPolynomial.mem_map_C_iff] at h3
    rw [MvPolynomial.mem_map_C_iff]
    intro m
    have := h3 m
    rw [coeff_map] at this
    exact this
  -- `f ∈ (I'' ∩ 𝔬[Z])𝔬[Z, Y]`, written in the standard coordinates `X_T, X_{Tᶜ}`
  have h6 : ψ f ∈ Ideal.map (pidc_incl R T).toRingHom JR := by
    have := Ideal.mem_map_of_mem (pidc_glue R T) h5
    rw [pidc_glue_split, Ideal.map_map] at this
    have hcomp : (pidc_glue R T).comp C = (pidc_incl R T).toRingHom :=
      RingHom.ext fun p => pidc_glue_C T p
    rwa [hcomp] at this
  -- and back in the coordinates `X`: `f ∈ (I'' ∩ 𝔬[Z])𝔬[X]`
  have h7 : f ∈ Ideal.map (pidc_kappaR b T).toRingHom JR := by
    have := Ideal.mem_map_of_mem (aeval (fun j => ((b j : homogeneousSubmodule (Fin n) R 1) :
      MvPolynomial (Fin n) R))).toRingHom h6
    rw [Ideal.map_map] at this
    have hcomp : (aeval (fun j => ((b j : homogeneousSubmodule (Fin n) R 1) :
        MvPolynomial (Fin n) R))).toRingHom.comp (pidc_incl R T).toRingHom =
        (pidc_kappaR b T).toRingHom :=
      RingHom.ext fun p => pidc_theta_incl b T p
    have e : (aeval (fun j => ((b j : homogeneousSubmodule (Fin n) R 1) :
        MvPolynomial (Fin n) R))).toRingHom (ψ f) = f := hθψ f
    rw [hcomp] at this
    rwa [e] at this
  -- the generators `p ∈ I'' ∩ 𝔬[Z]` lie in `{g | map g ∈ J} ∩ 𝔬[Z]`, whence `f ∈ (I'' ∩ 𝔬[L''])𝔬[X]`
  refine (Ideal.span_le.mpr ?_) h7
  rintro _ ⟨p, hp, rfl⟩
  refine Ideal.subset_span ⟨?_, ?_⟩
  · show map (algebraMap R K) (pidc_kappaR b T p) ∈ J
    rw [pidc_kappaK_map]
    exact hp
  · rw [SetLike.mem_coe, pidc_adjoin_eq_range_kappaR]
    exact ⟨p, rfl⟩

end PidCoord



section PidSpec

attribute [local instance] MvPolynomial.gradedAlgebra

variable (n μbar : ℕ)

/-- Coefficientwise extension to `A[X]` of an `F`-linear endomorphism `φ` of `F[X]`, for an
`F`-algebra `A` (it is `A[X] ≅ A ⊗_F F[X]` and `φ ⊗ id`): the `A`-linear map sending the monomial
`X^m` to `φ(X^m)` read in `A[X]`. -/
private noncomputable def pids_ext {F : Type u} [Field F] (A : Type*) [CommRing A] [Algebra F A]
    {n : ℕ} (φ : MvPolynomial (Fin n) F →ₗ[F] MvPolynomial (Fin n) F) :
    MvPolynomial (Fin n) A →ₗ[A] MvPolynomial (Fin n) A :=
  (MvPolynomial.basisMonomials (Fin n) A).constr A
    fun m => MvPolynomial.map (algebraMap F A) (φ (monomial m 1))

private theorem pids_ext_monomial {F : Type u} [Field F] (A : Type*) [CommRing A] [Algebra F A]
    {n : ℕ} (φ : MvPolynomial (Fin n) F →ₗ[F] MvPolynomial (Fin n) F) (m : Fin n →₀ ℕ) (a : A) :
    pids_ext A φ (monomial m a) = a • MvPolynomial.map (algebraMap F A) (φ (monomial m 1)) := by
  have h1 : (monomial m a : MvPolynomial (Fin n) A) = a • (MvPolynomial.basisMonomials (Fin n) A m) := by
    rw [MvPolynomial.coe_basisMonomials, MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
  rw [h1, map_smul]
  unfold pids_ext
  rw [Module.Basis.constr_basis]

/-- The coefficientwise extension is compatible with `F`-algebra homomorphisms `A → B`. -/
private theorem pids_map_ext {F : Type u} [Field F] {A B : Type*} [CommRing A] [CommRing B]
    [Algebra F A] [Algebra F B] {n : ℕ}
    (φ : MvPolynomial (Fin n) F →ₗ[F] MvPolynomial (Fin n) F) (h : A →ₐ[F] B)
    (q : MvPolynomial (Fin n) A) :
    MvPolynomial.map (h : A →+* B) (pids_ext A φ q) =
      pids_ext B φ (MvPolynomial.map (h : A →+* B) q) := by
  induction q using MvPolynomial.induction_on' with
  | monomial m a =>
    rw [pids_ext_monomial, map_monomial, pids_ext_monomial, smul_eq_C_mul, smul_eq_C_mul,
      map_mul, map_C, MvPolynomial.map_map, h.comp_algebraMap]
  | add p q hp hq => rw [map_add, map_add, hp, hq, map_add, map_add]

/-- Over `F` itself the extension is `φ`. -/
private theorem pids_ext_self {F : Type u} [Field F] {n : ℕ}
    (φ : MvPolynomial (Fin n) F →ₗ[F] MvPolynomial (Fin n) F) :
    pids_ext F φ = φ := by
  refine (MvPolynomial.basisMonomials (Fin n) F).ext fun m => ?_
  rw [MvPolynomial.coe_basisMonomials, pids_ext_monomial, Algebra.algebraMap_self,
    MvPolynomial.map_id, one_smul]

/-- `I K[X]` is the `K`-span of the image of `I` (the ideal generated by the image of `I` is
closed under multiplication by the monomials, as `I` is an ideal). -/
private theorem pids_mem_span_of_mem_map {F K : Type u} [Field F] [Field K] [Algebra F K] {n : ℕ}
    (I : Ideal (MvPolynomial (Fin n) F)) {x : MvPolynomial (Fin n) K}
    (hx : x ∈ I.map (MvPolynomial.map (algebraMap F K))) :
    x ∈ Submodule.span K (MvPolynomial.map (algebraMap F K) '' (I : Set (MvPolynomial (Fin n) F))) := by
  have hmul : ∀ (m : Fin n →₀ ℕ), ∀ y ∈ Submodule.span K
      (MvPolynomial.map (algebraMap F K) '' (I : Set (MvPolynomial (Fin n) F))),
      (monomial m (1 : K) : MvPolynomial (Fin n) K) * y ∈ Submodule.span K
        (MvPolynomial.map (algebraMap F K) '' (I : Set (MvPolynomial (Fin n) F))) := by
    intro m y hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨i, hi, rfl⟩ := hy
      apply Submodule.subset_span
      refine ⟨monomial m 1 * i, I.mul_mem_left _ hi, ?_⟩
      rw [map_mul, map_monomial, map_one]
    | zero => rw [mul_zero]; exact zero_mem _
    | add y z _ _ hy hz => rw [mul_add]; exact add_mem hy hz
    | smul c y _ hy => rw [mul_smul_comm]; exact Submodule.smul_mem _ _ hy
  unfold Ideal.map at hx
  induction hx using Submodule.span_induction with
  | mem y hy => exact Submodule.subset_span hy
  | zero => exact zero_mem _
  | add y z _ _ hy hz => exact add_mem hy hz
  | smul c y _ hy =>
    induction c using MvPolynomial.induction_on' with
    | monomial m a =>
      have h : (monomial m a : MvPolynomial (Fin n) K) * y = a • (monomial m 1 * y) := by
        rw [← smul_mul_assoc, MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
      rw [smul_eq_mul, h]
      exact Submodule.smul_mem _ _ (hmul m y hy)
    | add p q hp hq => rw [add_smul]; exact add_mem hp hq

/-- P3.  Lemma 12, p. 224: "It is clear that `I''_μ = I'_μ ∩ 𝔬[X]_μ` for all `μ`, because a `k`-free
base of `I_μ` is necessarily a `k'`-free base of `I'_μ` and can be extended to a `k`-free base of
`k[X]_μ` which is necessarily an `𝔬`-free base of `𝔬[X]_μ`", in the form needed for the
specialization `β`: an element of `𝔬[X]` lying in `I K[X]` is sent by `β` into `I`.

The paper does not write out the passage from bases to this form.  Here: choose an `F`-linear
projection `φ` of `F[X]` onto the `F`-subspace `I` ("a `k`-free base of `I_μ` extended to a `k`-free
base of `k[X]_μ`"), extend it coefficientwise to `A[X]` for every `F`-algebra `A` (`pids_ext`;
this is the "necessarily a free base" step), and use that it fixes `I K[X]`, hence `g`, because
`𝔬[X] → K[X]` is injective. -/
private theorem pid_map_mem_of_map_mem {F R K : Type u} [Field F] [CommRing R] [Field K]
    [Algebra F R] [Algebra R K] [Algebra F K] [IsScalarTower F R K] [FaithfulSMul R K] {n : ℕ}
    (β : R →ₐ[F] F) (I : Ideal (MvPolynomial (Fin n) F)) (g : MvPolynomial (Fin n) R)
    (hg : MvPolynomial.map (algebraMap R K) g ∈ I.map (MvPolynomial.map (algebraMap F K))) :
    MvPolynomial.map (β : R →+* F) g ∈ I := by
  -- an `F`-linear projection `φ` of `F[X]` onto the `F`-subspace `I`
  have hinj : Function.Injective ((I.restrictScalars F).subtype) := Subtype.val_injective
  obtain ⟨π, hπ⟩ := LinearMap.exists_leftInverse_of_injective ((I.restrictScalars F).subtype)
    (LinearMap.ker_eq_bot.mpr hinj)
  set φ : MvPolynomial (Fin n) F →ₗ[F] MvPolynomial (Fin n) F :=
    (I.restrictScalars F).subtype ∘ₗ π with hφ
  have hφI : ∀ q, φ q ∈ I := fun q => (π q).2
  have hφfix : ∀ q ∈ I, φ q = q := by
    intro q hq
    have := LinearMap.congr_fun hπ ⟨q, hq⟩
    simpa [hφ] using congrArg Subtype.val this
  -- the extension of `φ` to `K[X]` fixes `I K[X]`, the `K`-span of the image of `I`
  have hK : pids_ext K φ (MvPolynomial.map (algebraMap R K) g) =
      MvPolynomial.map (algebraMap R K) g := by
    have key : ∀ y ∈ Submodule.span K (MvPolynomial.map (algebraMap F K) ''
        (I : Set (MvPolynomial (Fin n) F))), pids_ext K φ y = y := by
      intro y hy
      induction hy using Submodule.span_induction with
      | mem y hy =>
        obtain ⟨i, hi, rfl⟩ := hy
        have h := pids_map_ext φ (Algebra.ofId F K) i
        rw [pids_ext_self, hφfix i hi] at h
        exact h.symm
      | zero => exact map_zero _
      | add y z _ _ hy hz => rw [map_add, hy, hz]
      | smul c y _ hy => rw [map_smul, hy]
    exact key _ (pids_mem_span_of_mem_map I hg)
  -- hence the extension of `φ` to `R[X]` fixes `g`
  have hR : pids_ext R φ g = g := by
    have h := pids_map_ext φ (IsScalarTower.toAlgHom F R K) g
    rw [IsScalarTower.coe_toAlgHom] at h
    rw [hK] at h
    exact MvPolynomial.map_injective (algebraMap R K) (FaithfulSMul.algebraMap_injective R K) h
  -- finally `β̃ g = β̃ (φ_R g) = φ (β̃ g) ∈ I`
  have h := pids_map_ext φ β g
  rw [hR, pids_ext_self] at h
  rw [h]
  exact hφI _

/-- P3b.  Lemma 12, p. 225: "Since `L''` is a direct summand of `𝔬[X]₁`, the `k`-module `β(L'')` has the
same rank as the `k'`-module `L'`": the images under `β` (coefficientwise) of an `𝔬`-base of `𝔬[X]₁`
are `k`-linearly independent.

The paper does not argue this step.  Here: the images span the `F`-space `F[X]₁` (each `X_j` is an
`𝔬`-combination of the base and `β(X_j) = X_j`), which has dimension `n`, and there are `n` of them. -/
private theorem pid_linearIndependent_map {F R : Type u} [Field F] [CommRing R] [Algebra F R] {n : ℕ}
    (β : R →ₐ[F] F) (b : Module.Basis (Fin n) R (homogeneousSubmodule (Fin n) R 1)) :
    LinearIndependent F (fun i => MvPolynomial.map (β : R →+* F)
      ((b i : homogeneousSubmodule (Fin n) R 1) : MvPolynomial (Fin n) R)) := by
  set w : Fin n → MvPolynomial (Fin n) F := fun i => MvPolynomial.map (β : R →+* F)
      ((b i : homogeneousSubmodule (Fin n) R 1) : MvPolynomial (Fin n) R) with hw
  -- every `X_j` is an `F`-combination of the `w i`
  have hX : ∀ j, (X j : MvPolynomial (Fin n) F) ∈ Submodule.span F (Set.range w) := by
    intro j
    have hXj : (X j : MvPolynomial (Fin n) R) ∈ homogeneousSubmodule (Fin n) R 1 :=
      (mem_homogeneousSubmodule _ _).mpr (isHomogeneous_X R j)
    have hsum := b.sum_repr ⟨X j, hXj⟩
    have h1 : (X j : MvPolynomial (Fin n) R) = ∑ i, (b.repr ⟨X j, hXj⟩ i) •
        ((b i : homogeneousSubmodule (Fin n) R 1) : MvPolynomial (Fin n) R) := by
      have := congrArg Subtype.val hsum
      simp only [Submodule.coe_sum, Submodule.coe_smul] at this
      exact this.symm
    have h2 : (X j : MvPolynomial (Fin n) F) = MvPolynomial.map (β : R →+* F) (X j) := by
      rw [map_X]
    rw [h2, h1, map_sum]
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [smul_eq_C_mul, map_mul, map_C, ← smul_eq_C_mul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  rw [linearIndependent_iff_card_eq_finrank_span]
  refine le_antisymm ?_ ?_
  · -- `n ≤ finrank span(range w)`: `span (range w)` contains the `n` independent forms `X_j`
    have hle : Submodule.span F (Set.range (X : Fin n → MvPolynomial (Fin n) F)) ≤
        Submodule.span F (Set.range w) := by
      rw [Submodule.span_le]
      rintro _ ⟨j, rfl⟩
      exact hX j
    have : FiniteDimensional F (Submodule.span F (Set.range w)) :=
      FiniteDimensional.span_of_finite F (Set.finite_range _)
    have h1 := Submodule.finrank_mono hle
    rw [finrank_span_eq_card (MvPolynomial.linearIndependent_X (Fin n) F)] at h1
    exact h1
  · exact finrank_range_le_card w

private theorem pids_mem_linearFormsOver {F K : Type u} [Field F] [Field K] [Algebra F K] {n : ℕ}
    (W : Submodule K (MvPolynomial (Fin n) K)) (ℓ : MvPolynomial (Fin n) F) :
    ℓ ∈ linearFormsOver F W ↔
      MvPolynomial.map (algebraMap F K) ℓ ∈ W ∧ ℓ ∈ homogeneousSubmodule (Fin n) F 1 := Iff.rfl

/-- P4.  The purely transcendental case of the only-if part of Lemma 12 (pp. 224-225), from claim
(1) on: with `k' = K`, `𝔬 = R`, `L' = W`, `L'' = L' ∩ 𝔬[X]₁`, `I' = I K[X]`, `I'' = I 𝔬[X]`:

"Now, let `β` be the homomorphism of `𝔬` onto `k` which induces the identity in `k` and annihilates
`u`.  This `β` can be extended to a homomorphism of `𝔬[X]` onto `k[X]` in such a way that
`β(X_i) = X_i` for all `i`.  Then we have, by (1), `I_μ = β(I''_μ) ⊆ k[X]_μ ∩ (I ∩ k[β(L'')])k[X]`,
for all `μ ≤ μ̄`.  Hence, (2) `I_μ = k[X]_μ ∩ (I ∩ k[β(L'')])k[X]` for all `μ ≤ μ̄`.  Since `L''` is a
direct summand of `𝔬[X]₁`, the `k`-module `β(L'')` has the same rank as the `k'`-module `L'`.
Moreover, by the if-part of the assertion, if `L'₁` is the `k'`-module generated by `β(L'')` then
`L'₁` has the same property as `L'`.  If `L'` is the smallest `k'`-submodule of `k'[X]₁` with the
property, then we must have `L' = L'₁`; hence, `β(L'') = L' ∩ k[X]₁ = L`.  Therefore, in this case, (2)
implies the lemma.  Now, in general, `L'` must contain the smallest one with the same property, by
Lemma 10, and therefore `L' ∩ k[X]₁ = L` must have the required property.  This completes the proof
for the purely transcendental case."

The proof follows this order: "in general" (the smallest `W`, reduction via `isTau_mono`), then
(1)/(2) (`M = β(L'')`), the rank, `L'₁`, and `M = L' ∩ k[X]₁`. -/
private theorem hasTauOnlyIf_of_pid_retraction (hμ : 0 < μbar) {F K R : Type u} [Field F] [Field K]
    [Algebra F K] [CommRing R] [IsDomain R] [IsPrincipalIdealRing R] [Algebra F R] [Algebra R K]
    [IsScalarTower F R K] [IsFractionRing R K] (β : R →ₐ[F] F) : HasTauOnlyIf n μbar F K := by
  classical
  intro I hI L' hL' hP'
  have hI' := isHomogeneous_map n (algebraMap F K) hI
  -- "Now, in general, `L'` must contain the smallest one with the same property, by Lemma 10":
  -- so it suffices to treat the smallest `W`
  obtain ⟨W, hW, hWmin⟩ := exists_min n μbar hμ hI'
  have hWL' : W ≤ L' := hWmin L' hP'
  suffices hmain : IsTauSubmoduleMv F n I (linearFormsOver F W) μbar by
    refine isTau_mono n μbar hmain ?_ inf_le_right
    intro ℓ hℓ
    exact (pids_mem_linearFormsOver L' ℓ).mpr
      ⟨hWL' ((pids_mem_linearFormsOver W ℓ).mp hℓ).1, ((pids_mem_linearFormsOver W ℓ).mp hℓ).2⟩
  -- "Since `𝔬` is a valuation ring, `L''` must be a direct summand ..." (`Z = b_T`)
  obtain ⟨b, T, -, hWspan, hrank⟩ := pid_exists_adapted_basis (R := R) W hW.1
  set Z : Fin n → MvPolynomial (Fin n) R :=
    fun i => ((b i : homogeneousSubmodule (Fin n) R 1) : MvPolynomial (Fin n) R) with hZ
  -- `M = β(L'')`: the `k`-module generated by the `β(Z_j)`
  set M : Submodule F (MvPolynomial (Fin n) F) :=
    Submodule.span F ((fun i => MvPolynomial.map (β : R →+* F) (Z i)) '' (T : Set (Fin n))) with hM
  have hMhom : M ≤ homogeneousSubmodule (Fin n) F 1 := by
    rw [hM, Submodule.span_le]
    rintro _ ⟨i, -, rfl⟩
    exact (mem_homogeneousSubmodule 1 _).mpr
      (((mem_homogeneousSubmodule 1 (Z i)).mp (b i).2).map _)
  -- "Then we have, by (1), `I_μ = β(I''_μ) ⊆ k[X]_μ ∩ (I ∩ k[β(L'')])k[X]`, ... Hence (2)":
  -- `M` has the property of Definition 6 for `I`
  have hMtau : IsTauSubmoduleMv F n I M μbar := by
    refine ⟨hMhom, fun μ hμμ ψ hψ => ⟨fun hψI => ?_, fun h => (Ideal.span_le.mpr fun x hx => hx.1) h⟩⟩
    have hψK : MvPolynomial.map (algebraMap F K) ψ ∈ homogeneousSubmodule (Fin n) K μ :=
      (mem_homogeneousSubmodule μ _).mpr (((mem_homogeneousSubmodule μ ψ).mp hψ).map _)
    -- `ψ ∈ I` gives `ψ ∈ I'`, and `I'` has the property of Definition 6 with `W = k'[Z]`
    have h1 := (hW.2 μ hμμ _ hψK).mp (Ideal.mem_map_of_mem _ hψI)
    have hadj : Algebra.adjoin K (W : Set (MvPolynomial (Fin n) K)) =
        Algebra.adjoin K ((fun i => MvPolynomial.map (algebraMap R K) (Z i)) '' (T : Set (Fin n))) := by
      rw [hWspan, Algebra.adjoin_span]
    rw [hadj] at h1
    -- (1): `ψ ∈ (I'' ∩ 𝔬[Z])𝔬[X]`
    have hf : MvPolynomial.map (algebraMap R K) (MvPolynomial.map (algebraMap F R) ψ) ∈
        Ideal.span (((I.map (MvPolynomial.map (algebraMap F K)) : Ideal (MvPolynomial (Fin n) K)) :
          Set (MvPolynomial (Fin n) K)) ∩
          (Algebra.adjoin K ((fun i => MvPolynomial.map (algebraMap R K) (Z i)) ''
            (T : Set (Fin n))) : Set (MvPolynomial (Fin n) K))) := by
      rw [MvPolynomial.map_map, ← IsScalarTower.algebraMap_eq]
      exact h1
    have h2 := pid_mem_span_of_mem_span b T (I.map (MvPolynomial.map (algebraMap F K)))
      (MvPolynomial.map (algebraMap F R) ψ) hf
    -- apply `β`: `β(ψ) = ψ`, and `β` maps the generators into `I ∩ k[β(L'')]`
    have h3 := Ideal.mem_map_of_mem (MvPolynomial.map (β : R →+* F)) h2
    rw [Ideal.map_span] at h3
    have hβψ : MvPolynomial.map (β : R →+* F) (MvPolynomial.map (algebraMap F R) ψ) = ψ := by
      rw [MvPolynomial.map_map, β.comp_algebraMap, Algebra.algebraMap_self, MvPolynomial.map_id]
    rw [hβψ] at h3
    refine Ideal.span_mono ?_ h3
    rintro _ ⟨g, ⟨hgJ, hgadj⟩, rfl⟩
    refine ⟨pid_map_mem_of_map_mem β I g hgJ, ?_⟩
    -- `β` maps `𝔬[Z]` into `k[β(Z)] ⊆ k[M]`
    have hadjmap : ∀ g ∈ Algebra.adjoin R (Z '' (T : Set (Fin n))),
        MvPolynomial.map (β : R →+* F) g ∈ Algebra.adjoin F (M : Set (MvPolynomial (Fin n) F)) := by
      intro g hg
      induction hg using Algebra.adjoin_induction with
      | mem x hx =>
        obtain ⟨i, hi, rfl⟩ := hx
        exact Algebra.subset_adjoin (Submodule.subset_span ⟨i, hi, rfl⟩)
      | algebraMap r =>
        rw [MvPolynomial.algebraMap_eq, map_C, ← MvPolynomial.algebraMap_eq]
        exact Subalgebra.algebraMap_mem _ _
      | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
      | mul x y _ _ hx hy => rw [map_mul]; exact mul_mem hx hy
    exact hadjmap g hgadj
  -- "Since `L''` is a direct summand of `𝔬[X]₁`, the `k`-module `β(L'')` has the same rank as `L'`"
  have hMfin : FiniteDimensional F M := finiteDimensional_of_isTau n μbar hMtau
  have hMrank : Module.finrank F M = T.card := by
    have hli : LinearIndependent F
        (fun i : T => MvPolynomial.map (β : R →+* F) (Z i)) :=
      (pid_linearIndependent_map β b).comp (fun i : T => (i : Fin n)) Subtype.val_injective
    have h := finrank_span_eq_card hli
    have hrange : Set.range (fun i : T => MvPolynomial.map (β : R →+* F) (Z i)) =
        (fun i => MvPolynomial.map (β : R →+* F) (Z i)) '' (T : Set (Fin n)) := by
      ext x
      simp
    rw [hrange] at h
    rw [hM, h]
    simp
  -- "if `L'₁` is the `k'`-module generated by `β(L'')` then `L'₁` has the same property as `L'`"
  set L1 : Submodule K (MvPolynomial (Fin n) K) :=
    Submodule.span K (MvPolynomial.map (algebraMap F K) '' (M : Set (MvPolynomial (Fin n) F)))
    with hL1
  have hL1hom : L1 ≤ homogeneousSubmodule (Fin n) K 1 := by
    rw [hL1, Submodule.span_le]
    rintro _ ⟨ℓ, hℓ, rfl⟩
    exact (mem_homogeneousSubmodule 1 _).mpr
      (((mem_homogeneousSubmodule 1 ℓ).mp (hMhom hℓ)).map _)
  have hL1tau := isTau_map_of_isTau n μbar hI hMtau hL1hom
    (fun ℓ hℓ => Submodule.subset_span ⟨ℓ, hℓ, rfl⟩)
  -- "If `L'` is the smallest ... we must have `L' = L'₁`": `W = L'₁`
  have hWL1 : W ≤ L1 := hWmin L1 hL1tau
  have := finiteDimensional_of_isTau n μbar hL1tau
  have hdim : Module.finrank K L1 ≤ Module.finrank K W :=
    (finrank_span_map_le n (algebraMap F K) M).trans (by rw [hMrank, hrank])
  have hWL1eq : W = L1 := Submodule.eq_of_le_of_finrank_le hWL1 hdim
  -- "hence, `β(L'') = L' ∩ k[X]₁ = L`": `M = linearFormsOver F W`
  have hMV : M ≤ linearFormsOver F W := by
    intro ℓ hℓ
    refine (pids_mem_linearFormsOver W ℓ).mpr ⟨?_, hMhom hℓ⟩
    rw [hWL1eq]
    exact Submodule.subset_span ⟨ℓ, hℓ, rfl⟩
  have hVfin : FiniteDimensional F (linearFormsOver F W) := by
    have := finiteDimensional_homogeneousSubmodule_one (K := F) n
    exact Submodule.finiteDimensional_of_le (inf_le_right :
      linearFormsOver F W ≤ homogeneousSubmodule (Fin n) F 1)
  have hVrank : Module.finrank F (linearFormsOver F W) ≤ Module.finrank K W := by
    have := finiteDimensional_of_isTau n μbar hW
    set V := linearFormsOver F W with hV
    let bV := Module.finBasis F V
    have hli : LinearIndependent F (fun i => ((bV i : V) : MvPolynomial (Fin n) F)) :=
      bV.linearIndependent.map' V.subtype (Submodule.ker_subtype V)
    have hli' : LinearIndependent K
        (fun i => MvPolynomial.map (algebraMap F K) ((bV i : V) : MvPolynomial (Fin n) F)) :=
      linearIndependent_map hli
    have hmem : ∀ i, MvPolynomial.map (algebraMap F K) ((bV i : V) : MvPolynomial (Fin n) F) ∈ W :=
      fun i => ((pids_mem_linearFormsOver W _).mp (bV i).2).1
    have hli'' : LinearIndependent K (fun i => (⟨_, hmem i⟩ : W)) :=
      LinearIndependent.of_comp W.subtype hli'
    have h := hli''.fintype_card_le_finrank
    simpa using h
  have hMeq : M = linearFormsOver F W :=
    Submodule.eq_of_le_of_finrank_le hMV (hVrank.trans (hrank.trans hMrank.symm).le)
  -- "Therefore, in this case, (2) implies the lemma."
  rw [← hMeq]
  exact hMtau

end PidSpec



section Transc

attribute [local instance] MvPolynomial.gradedAlgebra

variable (n μbar : ℕ)

/-- The ideal `(X)` of `F[X]` is prime. -/
private instance trc_isPrime_span_X {F : Type u} [Field F] :
    (Ideal.span {(Polynomial.X : Polynomial F)}).IsPrime :=
  (Ideal.span_singleton_prime Polynomial.X_ne_zero).mpr Polynomial.prime_X

/-- An element of the complement of the prime ideal `(X)` of `F[X]` has nonzero constant
coefficient, i.e. it does not vanish at `0`. -/
private theorem trc_eval_zero_ne_zero {F : Type u} [Field F] {q : Polynomial F}
    (hq : q ∈ (Ideal.span {(Polynomial.X : Polynomial F)}).primeCompl) :
    Polynomial.eval 0 q ≠ 0 := by
  rw [← Polynomial.coeff_zero_eq_eval_zero]
  intro h
  exact hq (Ideal.mem_span_singleton.mpr (Polynomial.X_dvd_iff.mpr h))

/-- Lemma 12, p. 224: "Let us first consider the case in which k' = k(u) with a variable u over k.
Let O be the localization of k[u] with respect to the prime ideal (u)k[u]." ...
"Now, let β be the homomorphism of O onto k which induces the identity in k and annihilates u."
(Here `F = k`, `K = k' = F(u)`.)  The paper does not say how `O` is realised inside `k'`, nor that
`O` is a principal ideal domain with fraction field `k'`; we build `O = F[X]_{(X)}`, its structure
map to `K = F(u)` and the retraction `β`, and apply the abstract statement
`hasTauOnlyIf_of_pid_retraction`. -/
private theorem hasTauOnlyIf_of_transcendental (hμ : 0 < μbar) {F K : Type u} [Field F] [Field K]
    [Algebra F K] (u : K) (hu : Transcendental F u) (hK : IntermediateField.adjoin F {u} = ⊤) :
    HasTauOnlyIf n μbar F K := by
  classical
  -- the prime ideal `(u) k[u]`, written `p = (X)` in `F[X]`
  set p : Ideal (Polynomial F) := Ideal.span {Polynomial.X} with hp
  have hp0 : p ≠ ⊥ := by
    rw [hp, Ne, Ideal.span_singleton_eq_bot]
    exact Polynomial.X_ne_zero
  have hinj : Function.Injective (Polynomial.aeval u : Polynomial F →ₐ[F] K) :=
    transcendental_iff_injective.mp hu
  -- `k[u]` is a subring of `k' = k(u)` via `aeval u`
  let algPK : Algebra (Polynomial F) K :=
    (Polynomial.aeval u : Polynomial F →ₐ[F] K).toRingHom.toAlgebra
  have halg : ∀ q : Polynomial F, algebraMap (Polynomial F) K q = Polynomial.aeval u q :=
    fun q => rfl
  have towerFP : IsScalarTower F (Polynomial F) K :=
    IsScalarTower.of_algebraMap_eq fun c => by
      rw [halg, IsScalarTower.algebraMap_apply F (Polynomial F) K, halg]
  -- elements of `k[u]` outside `(u)` become units of `k'`
  have hunit : ∀ y : p.primeCompl, IsUnit (algebraMap (Polynomial F) K y) := by
    intro y
    refine isUnit_iff_ne_zero.mpr ?_
    rw [halg, Ne, map_eq_zero_iff _ hinj]
    intro h0
    apply trc_eval_zero_ne_zero y.2
    rw [h0, Polynomial.eval_zero]
  -- `O = k[u]_{(u)}` with its structure map to `k'`
  let algRK : Algebra (Localization.AtPrime p) K :=
    (IsLocalization.lift (S := Localization.AtPrime p) hunit).toAlgebra
  have tower1 : IsScalarTower (Polynomial F) (Localization.AtPrime p) K :=
    IsScalarTower.of_algebraMap_eq fun x => by
      exact (IsLocalization.lift_eq hunit x).symm
  have tower2 : IsScalarTower F (Localization.AtPrime p) K :=
    IsScalarTower.of_algebraMap_eq fun c => by
      rw [IsScalarTower.algebraMap_apply F (Polynomial F) (Localization.AtPrime p) c,
        ← IsScalarTower.algebraMap_apply (Polynomial F) (Localization.AtPrime p) K,
        ← IsScalarTower.algebraMap_apply F (Polynomial F) K]
  -- `k'` is the fraction field of `k[u]`
  have hfrac : IsFractionRing (Polynomial F) K := by
    refine (isLocalization_iff (nonZeroDivisors (Polynomial F)) K).mpr ⟨fun y => ?_, fun z => ?_, fun {x y} h => ?_⟩
    · exact isUnit_iff_ne_zero.mpr
        ((map_ne_zero_iff _ hinj).mpr (nonZeroDivisors.coe_ne_zero y))
    · obtain ⟨r, s, hrs⟩ := (IntermediateField.mem_adjoin_simple_iff F z).mp
        (hK ▸ IntermediateField.mem_top)
      by_cases hs : s = 0
      · refine ⟨(0, 1), ?_⟩
        rw [hrs, hs]
        simp
      · refine ⟨(r, ⟨s, mem_nonZeroDivisors_of_ne_zero hs⟩), ?_⟩
        have hs' : Polynomial.aeval u s ≠ 0 := (map_ne_zero_iff _ hinj).mpr hs
        simp only [halg]
        rw [hrs, div_mul_cancel₀ _ hs']
    · exact ⟨1, by rw [hinj h]⟩
  -- hence also the fraction field of the localization `O`
  have hfrac' : IsFractionRing (Localization.AtPrime p) K :=
    IsFractionRing.isFractionRing_of_isDomain_of_isLocalization p.primeCompl
      (Localization.AtPrime p) K
  -- `O` is a discrete valuation ring (`k[u]` is a Dedekind domain, `(u) ≠ 0`), hence a PID
  have hdvr : IsDiscreteValuationRing (Localization.AtPrime p) :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain (Polynomial F) hp0
      (Localization.AtPrime p)
  -- "the homomorphism of O onto k which induces the identity in k and annihilates u"
  have hβ : ∀ y : p.primeCompl, IsUnit ((Polynomial.aeval (0 : F) : Polynomial F →ₐ[F] F) y) := by
    intro y
    rw [Polynomial.coe_aeval_eq_eval]
    exact isUnit_iff_ne_zero.mpr (trc_eval_zero_ne_zero y.2)
  let β : Localization.AtPrime p →ₐ[F] F := IsLocalization.liftAlgHom hβ
  exact hasTauOnlyIf_of_pid_retraction n μbar hμ (R := Localization.AtPrime p) β

end Transc



section Gal

attribute [local instance] MvPolynomial.gradedAlgebra

variable (n μbar : ℕ)

/-- Membership in `linearFormsOver F L'` unfolds to: the image lies in `L'` and the form is
homogeneous of degree one. -/
private theorem gal_mem_linearFormsOver_iff {F K : Type u} [Field F] [Field K] [Algebra F K]
    {L' : Submodule K (MvPolynomial (Fin n) K)} {q : MvPolynomial (Fin n) F} :
    q ∈ linearFormsOver F L' ↔
      MvPolynomial.map (algebraMap F K) q ∈ L' ∧ q ∈ homogeneousSubmodule (Fin n) F 1 :=
  Iff.rfl

/-! ### Coefficientwise descent from `K[X]` to `F[X]` -/

/-- Descent along a coefficientwise `F`-linear map `K → F`: an element of the `K`-span of the image
of an `F`-submodule `N ⊆ F[X]` is sent into `N`.  The paper does not argue this step (it is part of
"the assertion follows without difficulty"). -/
private theorem gal_coeffwise_mem {F K : Type u} [Field F] [Field K] [Algebra F K]
    (lam : K →ₗ[F] F) (Pr : MvPolynomial (Fin n) K →+ MvPolynomial (Fin n) F)
    (hPr : ∀ (c : K) (b : MvPolynomial (Fin n) F),
      Pr (c • MvPolynomial.map (algebraMap F K) b) = lam c • b)
    (N : Submodule F (MvPolynomial (Fin n) F)) {y : MvPolynomial (Fin n) K}
    (hy : y ∈ Submodule.span K
      (MvPolynomial.map (algebraMap F K) '' (N : Set (MvPolynomial (Fin n) F)))) :
    Pr y ∈ N := by
  have key : ∀ y ∈ Submodule.span K (MvPolynomial.map (algebraMap F K) ''
      (N : Set (MvPolynomial (Fin n) F))), ∀ c : K, Pr (c • y) ∈ N := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨l, hl, rfl⟩ := hy
      intro c
      rw [hPr]
      exact N.smul_mem _ hl
    | zero => intro c; rw [smul_zero, map_zero]; exact zero_mem _
    | add x y _ _ hx hy => intro c; rw [smul_add, map_add]; exact add_mem (hx c) (hy c)
    | smul d x _ hx => intro c; rw [smul_smul]; exact hx (c * d)
  simpa using key y hy 1

/-- The extension `J K[X]` of an ideal `J` of `F[X]` is contained in the `K`-span of the image of
`J` (as `K[X]` is spanned over `K` by monomials). -/
private theorem gal_ideal_map_subset_span {F K : Type u} [Field F] [Field K] [Algebra F K]
    (J : Ideal (MvPolynomial (Fin n) F)) {y : MvPolynomial (Fin n) K}
    (hy : y ∈ J.map (MvPolynomial.map (algebraMap F K))) :
    y ∈ Submodule.span K
      (MvPolynomial.map (algebraMap F K) '' (J : Set (MvPolynomial (Fin n) F))) := by
  set S := Submodule.span K
    (MvPolynomial.map (algebraMap F K) '' (J : Set (MvPolynomial (Fin n) F))) with hS
  have hmon : ∀ (a : MvPolynomial (Fin n) K), ∀ j ∈ J,
      a * MvPolynomial.map (algebraMap F K) j ∈ S := by
    intro a j hj
    induction a using MvPolynomial.induction_on' with
    | monomial u c =>
      have h : monomial u c * MvPolynomial.map (algebraMap F K) j =
          c • MvPolynomial.map (algebraMap F K) (monomial u 1 * j) := by
        rw [map_mul, map_monomial, map_one, smul_eq_C_mul, ← mul_assoc, C_mul_monomial, mul_one]
      rw [h]
      exact S.smul_mem _ (Submodule.subset_span ⟨_, J.mul_mem_left _ hj, rfl⟩)
    | add p q hp hq => rw [add_mul]; exact add_mem hp hq
  have hmul : ∀ (a : MvPolynomial (Fin n) K), ∀ y ∈ S, a * y ∈ S := by
    intro a y hy
    induction hy using Submodule.span_induction with
    | mem y hy => obtain ⟨j, hj, rfl⟩ := hy; exact hmon a j hj
    | zero => rw [mul_zero]; exact zero_mem _
    | add x y _ _ hx hy => rw [mul_add]; exact add_mem hx hy
    | smul d x _ hx => rw [mul_smul_comm]; exact S.smul_mem _ hx
  change y ∈ Ideal.span _ at hy
  induction hy using Submodule.span_induction with
  | mem y hy => obtain ⟨j, hj, rfl⟩ := hy; exact Submodule.subset_span ⟨j, hj, rfl⟩
  | zero => exact zero_mem _
  | add x y _ _ hx hy => exact add_mem hx hy
  | smul a x _ hx => rw [smul_eq_mul]; exact hmul a x hx

/-- Expansion of a polynomial over `K` along an `F`-basis `b` of `K`:
`h = ∑ⱼ bⱼ · (Prⱼ h)` where `Prⱼ` is the coefficientwise coordinate functional. -/
private theorem gal_eq_sum_basis {F K : Type u} [Field F] [Field K] [Algebra F K] {ι : Type*}
    [Fintype ι] (b : Module.Basis ι F K)
    (Pr : ι → MvPolynomial (Fin n) K →+ MvPolynomial (Fin n) F)
    (hPr : ∀ j q m, (Pr j q).coeff m = b.coord j (q.coeff m)) (h : MvPolynomial (Fin n) K) :
    h = ∑ j, b j • MvPolynomial.map (algebraMap F K) (Pr j h) := by
  ext m
  rw [coeff_sum]
  simp only [coeff_smul, coeff_map, hPr, smul_eq_mul]
  conv_lhs => rw [← b.sum_repr (h.coeff m)]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Module.Basis.coord_apply, Algebra.smul_def, mul_comm]

/-- Base change commutes with intersections: the `K`-span of the image of `N₁ ⊓ N₂` is the
intersection of the `K`-spans of the images of `N₁` and `N₂` (one inclusion; by expansion along an
`F`-basis of `K`).  The paper does not argue this step. -/
private theorem gal_mem_span_inf {F K : Type u} [Field F] [Field K] [Algebra F K]
    [FiniteDimensional F K] (N₁ N₂ : Submodule F (MvPolynomial (Fin n) F))
    {h : MvPolynomial (Fin n) K}
    (h₁ : h ∈ Submodule.span K
      (MvPolynomial.map (algebraMap F K) '' (N₁ : Set (MvPolynomial (Fin n) F))))
    (h₂ : h ∈ Submodule.span K
      (MvPolynomial.map (algebraMap F K) '' (N₂ : Set (MvPolynomial (Fin n) F)))) :
    h ∈ Submodule.span K (MvPolynomial.map (algebraMap F K) ''
      ((N₁ ⊓ N₂ : Submodule F (MvPolynomial (Fin n) F)) : Set (MvPolynomial (Fin n) F))) := by
  set b := Module.finBasis F K
  have hex : ∀ j, ∃ Pr : MvPolynomial (Fin n) K →+ MvPolynomial (Fin n) F,
      (∀ q m, (Pr q).coeff m = b.coord j (q.coeff m)) ∧
      ∀ (c : K) (a : MvPolynomial (Fin n) F),
        Pr (c • MvPolynomial.map (algebraMap F K) a) = b.coord j c • a :=
    fun j => exists_coeffwise (σ := Fin n) (b.coord j)
  choose Pr hcoef hsm using hex
  rw [gal_eq_sum_basis n b Pr hcoef h]
  refine Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _
    (Submodule.subset_span ⟨Pr j h, ?_, rfl⟩)
  exact ⟨gal_coeffwise_mem n (b.coord j) (Pr j) (hsm j) N₁ h₁,
    gal_coeffwise_mem n (b.coord j) (Pr j) (hsm j) N₂ h₂⟩

/-- If a `K`-submodule `W` lies in the `K`-span of the image of an `F`-subalgebra `A ⊆ F[X]`,
then so does `K[W]`. -/
private theorem gal_adjoin_subset_span {F K : Type u} [Field F] [Field K] [Algebra F K]
    (A : Subalgebra F (MvPolynomial (Fin n) F)) (W : Submodule K (MvPolynomial (Fin n) K))
    (hW : W ≤ Submodule.span K
      (MvPolynomial.map (algebraMap F K) '' (A : Set (MvPolynomial (Fin n) F))))
    {h : MvPolynomial (Fin n) K} (hh : h ∈ Algebra.adjoin K (W : Set (MvPolynomial (Fin n) K))) :
    h ∈ Submodule.span K
      (MvPolynomial.map (algebraMap F K) '' (A : Set (MvPolynomial (Fin n) F))) := by
  set S := Submodule.span K
    (MvPolynomial.map (algebraMap F K) '' (A : Set (MvPolynomial (Fin n) F))) with hS
  have hmul : S * S ≤ S := by
    rw [hS, Submodule.span_mul_span]
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨_, ⟨a, ha, rfl⟩, _, ⟨b, hb, rfl⟩, rfl⟩
    exact Submodule.subset_span ⟨a * b, A.mul_mem ha hb, map_mul _ _ _⟩
  induction hh using Algebra.adjoin_induction with
  | mem x hx => exact hW hx
  | algebraMap r =>
    rw [Algebra.algebraMap_eq_smul_one]
    exact S.smul_mem _ (Submodule.subset_span
      (⟨1, A.one_mem, map_one _⟩ : (1 : MvPolynomial (Fin n) K) ∈ _ '' _))
  | add x y _ _ hx hy => exact add_mem hx hy
  | mul x y _ _ hx hy => exact hmul (Submodule.mul_mem_mul hx hy)

/-! ### The Galois group acts on `K[X]` -/

/-- Applying an automorphism of `K` over `F` coefficientwise twice, in opposite directions, is the
identity. -/
private theorem gal_map_symm_map {F K : Type u} [Field F] [Field K] [Algebra F K]
    (σ : K ≃ₐ[F] K) (p : MvPolynomial (Fin n) K) :
    MvPolynomial.map (σ.symm : K →+* K) (MvPolynomial.map (σ : K →+* K) p) = p := by
  rw [MvPolynomial.map_map]
  have : (σ.symm : K →+* K).comp (σ : K →+* K) = RingHom.id K := by ext x; simp
  rw [this, MvPolynomial.map_id]

/-- The extended ideal `I K[X]` is stable under the Galois group, which fixes the coefficients
of `I ⊆ F[X]`. -/
private theorem gal_map_mem_ideal {F K : Type u} [Field F] [Field K] [Algebra F K]
    (I : Ideal (MvPolynomial (Fin n) F)) (σ : K ≃ₐ[F] K) {y : MvPolynomial (Fin n) K}
    (hy : y ∈ I.map (MvPolynomial.map (algebraMap F K))) :
    MvPolynomial.map (σ : K →+* K) y ∈ I.map (MvPolynomial.map (algebraMap F K)) := by
  have hle : I.map (MvPolynomial.map (algebraMap F K)) ≤
      (I.map (MvPolynomial.map (algebraMap F K))).comap (MvPolynomial.map (σ : K →+* K)) := by
    rw [Ideal.map_le_iff_le_comap]
    intro p hp
    rw [Ideal.mem_comap, Ideal.mem_comap, MvPolynomial.map_map]
    have : (σ : K →+* K).comp (algebraMap F K) = algebraMap F K := by ext; simp
    rw [this]
    exact Ideal.mem_map_of_mem _ hp
  exact hle hy

/-- The twist `{ℓ | σ(ℓ) ∈ W}` of a `K`-submodule `W ⊆ K[X]` by an automorphism `σ` of `K`
(acting coefficientwise on `K[X]`). -/
private def galTwist {F K : Type u} [Field F] [Field K] [Algebra F K] (σ : K ≃ₐ[F] K)
    (W : Submodule K (MvPolynomial (Fin n) K)) : Submodule K (MvPolynomial (Fin n) K) where
  carrier := {ℓ | MvPolynomial.map (σ : K →+* K) ℓ ∈ W}
  add_mem' := fun {a b} ha hb => by
    show MvPolynomial.map (σ : K →+* K) (a + b) ∈ W
    rw [map_add]
    exact add_mem ha hb
  zero_mem' := by
    show MvPolynomial.map (σ : K →+* K) 0 ∈ W
    rw [map_zero]
    exact zero_mem _
  smul_mem' := fun c ℓ hℓ => by
    show MvPolynomial.map (σ : K →+* K) (c • ℓ) ∈ W
    rw [smul_eq_C_mul, map_mul, map_C, ← smul_eq_C_mul]
    exact W.smul_mem _ hℓ

/-- The twist of a submodule with the property of Definition 6 for `I K[X]` by an element of the
Galois group again has the property (transport of the defining equivalence by the ring
automorphism `σ` of `K[X]`, which fixes `I K[X]`).  The paper does not argue this step. -/
private theorem gal_isTau_twist {F K : Type u} [Field F] [Field K] [Algebra F K]
    {I : Ideal (MvPolynomial (Fin n) F)} {W : Submodule K (MvPolynomial (Fin n) K)}
    (hW : IsTauSubmoduleMv K n (I.map (MvPolynomial.map (algebraMap F K))) W μbar)
    (σ : K ≃ₐ[F] K) :
    IsTauSubmoduleMv K n (I.map (MvPolynomial.map (algebraMap F K))) (galTwist n σ W) μbar := by
  have hhom : ∀ (τ : K ≃ₐ[F] K) (p : MvPolynomial (Fin n) K) (d : ℕ),
      p ∈ homogeneousSubmodule (Fin n) K d →
        MvPolynomial.map (τ : K →+* K) p ∈ homogeneousSubmodule (Fin n) K d :=
    fun τ p d hp => (mem_homogeneousSubmodule d _).mpr (((mem_homogeneousSubmodule d _).mp hp).map _)
  have hinv' : ∀ p : MvPolynomial (Fin n) K,
      MvPolynomial.map (σ : K →+* K) (MvPolynomial.map (σ.symm : K →+* K) p) = p := by
    intro p
    have := gal_map_symm_map n σ.symm p
    rwa [AlgEquiv.symm_symm] at this
  have hadj : ∀ x ∈ Algebra.adjoin K (W : Set (MvPolynomial (Fin n) K)),
      MvPolynomial.map (σ.symm : K →+* K) x ∈
        Algebra.adjoin K ((galTwist n σ W : Submodule K (MvPolynomial (Fin n) K)) :
          Set (MvPolynomial (Fin n) K)) := by
    intro x hx
    induction hx using Algebra.adjoin_induction with
    | mem x hx =>
      apply Algebra.subset_adjoin
      show MvPolynomial.map (σ : K →+* K) (MvPolynomial.map (σ.symm : K →+* K) x) ∈ W
      rw [hinv']
      exact hx
    | algebraMap r =>
      rw [MvPolynomial.algebraMap_eq, map_C, ← MvPolynomial.algebraMap_eq]
      exact Subalgebra.algebraMap_mem _ _
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | mul x y _ _ hx hy => rw [map_mul]; exact mul_mem hx hy
  refine ⟨?_, fun μ hμ ψ hψ => ⟨fun hψI => ?_, fun h => (Ideal.span_le.mpr fun _ hx => hx.1) h⟩⟩
  · intro ℓ hℓ
    have h1 : MvPolynomial.map (σ : K →+* K) ℓ ∈ homogeneousSubmodule (Fin n) K 1 := hW.1 hℓ
    have := hhom σ.symm _ 1 h1
    rwa [gal_map_symm_map] at this
  · have h1 := gal_map_mem_ideal n I σ hψI
    have h2 := (hW.2 μ hμ _ (hhom σ ψ μ hψ)).mp h1
    have h3 := Ideal.mem_map_of_mem (MvPolynomial.map (σ.symm : K →+* K)) h2
    rw [Ideal.map_span, gal_map_symm_map] at h3
    refine Ideal.span_mono ?_ h3
    rintro _ ⟨x, ⟨hxI, hxA⟩, rfl⟩
    exact ⟨gal_map_mem_ideal n I σ.symm hxI, hadj x hxA⟩

/-- "Such `L'` is unique (see Lemma 10) and therefore `L'` must be invariant under the operation of
Galois group of the extension `k'` over `k` which operates on `k'[X]` in a natural way."  The
smallest submodule `W` with the property is stable under every `σ ∈ Gal(K/F)`: the twist of `W`
again has the property, so it contains `W` by minimality. -/
private theorem gal_map_mem_of_min {F K : Type u} [Field F] [Field K] [Algebra F K]
    {I : Ideal (MvPolynomial (Fin n) F)} {W : Submodule K (MvPolynomial (Fin n) K)}
    (hW : IsTauSubmoduleMv K n (I.map (MvPolynomial.map (algebraMap F K))) W μbar)
    (hmin : ∀ W', IsTauSubmoduleMv K n (I.map (MvPolynomial.map (algebraMap F K))) W' μbar →
      W ≤ W')
    (σ : K ≃ₐ[F] K) {ℓ : MvPolynomial (Fin n) K} (hℓ : ℓ ∈ W) :
    MvPolynomial.map (σ : K →+* K) ℓ ∈ W :=
  hmin _ (gal_isTau_twist n μbar hW σ) hℓ

/-! ### Galois descent of a Galois-stable submodule of `K[X]₁` -/

/-- The coefficientwise trace `K[X] → F[X]` is the sum over the Galois group, after extension of
scalars. -/
private theorem gal_map_trace {F K : Type u} [Field F] [Field K] [Algebra F K]
    [FiniteDimensional F K] [IsGalois F K]
    (Pr : MvPolynomial (Fin n) K →+ MvPolynomial (Fin n) F)
    (hPr : ∀ q m, (Pr q).coeff m = Algebra.trace F K (q.coeff m)) (q : MvPolynomial (Fin n) K) :
    MvPolynomial.map (algebraMap F K) (Pr q) =
      ∑ σ : K ≃ₐ[F] K, MvPolynomial.map (σ : K →+* K) q := by
  ext m
  rw [coeff_map, hPr, coeff_sum, trace_eq_sum_automorphisms]
  simp only [coeff_map]
  rfl

/-- "Since `k'` is separable over `k`, the invariance of `L'` implies that `L'` is generated by
`L = L' ∩ k[X]₁` over the field `k'`."  A Galois-stable `K`-submodule `W ⊆ K[X]₁` lies in the
`K`-span of `linearFormsOver F W`: for `ℓ ∈ W` and a basis `b` of `K/F` with trace-dual basis `d`,
`ℓ = ∑ₖ dₖ · (Tr(bₖ ℓ))` and `Tr(bₖ ℓ) = ∑_σ σ(bₖ ℓ) ∈ W ∩ F[X]₁`. -/
private theorem gal_le_span_linearForms {F K : Type u} [Field F] [Field K] [Algebra F K]
    [FiniteDimensional F K] [IsGalois F K] {W : Submodule K (MvPolynomial (Fin n) K)}
    (hW1 : W ≤ homogeneousSubmodule (Fin n) K 1)
    (hinv : ∀ (σ : K ≃ₐ[F] K) (ℓ : MvPolynomial (Fin n) K), ℓ ∈ W →
      MvPolynomial.map (σ : K →+* K) ℓ ∈ W) :
    W ≤ Submodule.span K (MvPolynomial.map (algebraMap F K) ''
      (linearFormsOver F W : Set (MvPolynomial (Fin n) F))) := by
  classical
  intro ℓ hℓ
  set b := Module.finBasis F K
  have hB := traceForm_nondegenerate F K
  set d := (Algebra.traceForm F K).dualBasis hB b
  obtain ⟨Pr, hcoef, hsm⟩ := exists_coeffwise (σ := Fin n) (Algebra.trace F K)
  have hsum : ℓ = ∑ k, d k • MvPolynomial.map (algebraMap F K) (Pr (b k • ℓ)) := by
    ext m
    rw [coeff_sum]
    simp only [coeff_smul, coeff_map, hcoef, smul_eq_mul]
    conv_lhs => rw [← d.sum_repr (ℓ.coeff m)]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [LinearMap.BilinForm.dualBasis_repr_apply, Algebra.traceForm_apply, Algebra.smul_def,
      mul_comm (b k) (ℓ.coeff m), mul_comm]
  have hℓ1 : ℓ.IsHomogeneous 1 := (mem_homogeneousSubmodule 1 ℓ).mp (hW1 hℓ)
  have hmem : ∀ k, Pr (b k • ℓ) ∈ linearFormsOver F W := by
    intro k
    rw [gal_mem_linearFormsOver_iff]
    constructor
    · rw [gal_map_trace n Pr hcoef]
      exact Submodule.sum_mem _ fun σ _ => hinv σ _ (W.smul_mem _ hℓ)
    · rw [mem_homogeneousSubmodule]
      intro m hm
      refine hℓ1 fun h0 => hm ?_
      rw [hcoef, coeff_smul, h0, smul_zero, map_zero]
  rw [hsum]
  exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _
    (Submodule.subset_span ⟨_, hmem k, rfl⟩)

/-! ### Lemma 12 for finite Galois extensions -/

/-- Lemma 12, p. 225, the case of a finite Galois extension `k' = K` of `k = F`:
"Now, let us consider the case in which k' is finitely separably algebraic. We may assume that k'
is Galois extension of k. We may also assume that L' is the smallest k'-submodule of k'[X]_1 with
the property. Such L' is unique (see Lemma 10) and therefore L' must be invariant under the
operation of Galois group of the extension k' over k which operates on k'[X] in a natural way.
Since k' is separable over k, the invariance of L' implies that L' is generated by
L = L' ∩ k[X]_1 over the field k'. Then the assertion follows without difficulty."
The paper does not argue the last step; it is proved here by descent along coefficientwise
`F`-linear maps `K → F` (an `F`-basis of `K` and a retraction `K → F`). -/
private theorem hasTauOnlyIf_of_isGalois (hμ : 0 < μbar) {F K : Type u} [Field F] [Field K]
    [Algebra F K] [FiniteDimensional F K] [IsGalois F K] : HasTauOnlyIf n μbar F K := by
  intro I hI L' hL'1 hL'
  -- "We may also assume that L' is the smallest k'-submodule of k'[X]_1 with the property."
  obtain ⟨W, hW, hWmin⟩ := exists_min n μbar hμ (isHomogeneous_map n (algebraMap F K) hI)
  have hWL' : W ≤ L' := hWmin L' hL'
  suffices h : IsTauSubmoduleMv F n I (linearFormsOver F W) μbar from
    isTau_mono n μbar h
      (fun p hp => (gal_mem_linearFormsOver_iff n).mpr
        ⟨hWL' ((gal_mem_linearFormsOver_iff n).mp hp).1, ((gal_mem_linearFormsOver_iff n).mp hp).2⟩)
      inf_le_right
  -- "Such L' is unique (see Lemma 10) and therefore L' must be invariant under the operation of
  -- Galois group of the extension k' over k which operates on k'[X] in a natural way."
  have hinv : ∀ (σ : K ≃ₐ[F] K) (ℓ : MvPolynomial (Fin n) K), ℓ ∈ W →
      MvPolynomial.map (σ : K →+* K) ℓ ∈ W :=
    fun σ ℓ hℓ => gal_map_mem_of_min n μbar hW hWmin σ hℓ
  -- "Since k' is separable over k, the invariance of L' implies that L' is generated by
  -- L = L' ∩ k[X]_1 over the field k'."
  have hspan := gal_le_span_linearForms n hW.1 hinv
  -- "Then the assertion follows without difficulty."
  refine ⟨inf_le_right, fun μ hμ' ψ hψ => ⟨fun hψI => ?_, fun h =>
    (Ideal.span_le.mpr fun _ hx => hx.1) h⟩⟩
  set A := Algebra.adjoin F ((linearFormsOver F W : Submodule F (MvPolynomial (Fin n) F)) :
    Set (MvPolynomial (Fin n) F)) with hA
  have hspanA : W ≤ Submodule.span K (MvPolynomial.map (algebraMap F K) ''
      (A : Set (MvPolynomial (Fin n) F))) :=
    hspan.trans (Submodule.span_mono (Set.image_mono Algebra.subset_adjoin))
  set J : Ideal (MvPolynomial (Fin n) F) :=
    Ideal.span ((I : Set (MvPolynomial (Fin n) F)) ∩ (A : Set (MvPolynomial (Fin n) F))) with hJ
  -- `ψ ∈ I` gives `ψ ∈ I K[X]`, hence `ψ ∈ (I' ∩ K[W]) K[X]`
  have h1 : MvPolynomial.map (algebraMap F K) ψ ∈ I.map (MvPolynomial.map (algebraMap F K)) :=
    Ideal.mem_map_of_mem _ hψI
  have hψK : MvPolynomial.map (algebraMap F K) ψ ∈ homogeneousSubmodule (Fin n) K μ :=
    (mem_homogeneousSubmodule μ _).mpr (((mem_homogeneousSubmodule μ _).mp hψ).map _)
  have h2 := (hW.2 μ hμ' _ hψK).mp h1
  -- `(I' ∩ K[W]) K[X] ⊆ (I ∩ F[L]) K[X]`, by descent along an `F`-basis of `K`
  have h3 : Ideal.span ((I.map (MvPolynomial.map (algebraMap F K)) : Set (MvPolynomial (Fin n) K)) ∩
      (Algebra.adjoin K (W : Set (MvPolynomial (Fin n) K)) : Set (MvPolynomial (Fin n) K))) ≤
      J.map (MvPolynomial.map (algebraMap F K)) := by
    rw [Ideal.span_le]
    rintro h ⟨hhI, hhA⟩
    have e1 := gal_ideal_map_subset_span n I hhI
    have e2 := gal_adjoin_subset_span n A W hspanA hhA
    have e3 := gal_mem_span_inf n (I.restrictScalars F) A.toSubmodule e1 e2
    have hle : Submodule.span K (MvPolynomial.map (algebraMap F K) ''
        ((I.restrictScalars F ⊓ A.toSubmodule : Submodule F (MvPolynomial (Fin n) F)) :
          Set (MvPolynomial (Fin n) F))) ≤
        (J.map (MvPolynomial.map (algebraMap F K))).restrictScalars K := by
      refine Submodule.span_le.mpr ?_
      rintro _ ⟨x, ⟨hxI, hxA⟩, rfl⟩
      exact Ideal.mem_map_of_mem _ (Ideal.subset_span ⟨hxI, hxA⟩)
    exact hle e3
  have h4 := h3 h2
  -- apply a `F`-linear retraction `π : K → F` coefficientwise
  have h5 := gal_ideal_map_subset_span n J h4
  obtain ⟨π, hπ⟩ := LinearMap.exists_leftInverse_of_injective (Algebra.linearMap F K)
    (LinearMap.ker_eq_bot.mpr (algebraMap F K).injective)
  have hπ1 : π 1 = 1 := by
    have := LinearMap.congr_fun hπ 1
    simpa using this
  obtain ⟨Pr, -, hPr⟩ := exists_coeffwise (σ := Fin n) π
  have h6 := gal_coeffwise_mem n π Pr hPr (J.restrictScalars F) h5
  have h7 : Pr (MvPolynomial.map (algebraMap F K) ψ) = ψ := by
    have := hPr 1 ψ
    rwa [one_smul, hπ1, one_smul] at this
  rw [h7] at h6
  exact h6

end Gal





section FGSep

attribute [local instance] MvPolynomial.gradedAlgebra

variable (n μbar : ℕ)

/-! ### Lemma 12 for finite separable extensions -/

/-- If `K` lies between `F` and an extension `N` of `F` for which the only-if part of Lemma 12 is
known, then it holds for `K/F`.  This is the step of the proof of Lemma 12, p. 225, that passes
from `k'` to a Galois extension `N` containing it: the `K`-submodule `L'` of `K[X]₁` is replaced
by the `N`-submodule `L'_N` it generates; `L'_N` has the property of Definition 6 for `I N[X]` (the
if-part), and `linearFormsOver F L'_N = linearFormsOver F L'`.  The paper does not argue this
step. -/
private theorem fgs_hasTauOnlyIf_of_tower {F K N : Type u} [Field F] [Field K] [Field N]
    [Algebra F K] [Algebra K N] [Algebra F N] [IsScalarTower F K N]
    (hN : HasTauOnlyIf n μbar F N) : HasTauOnlyIf n μbar F K := by
  intro I hI L' hL' h
  -- `L'_N` is the `N`-span of the image of `L'`
  set LN : Submodule N (MvPolynomial (Fin n) N) :=
    Submodule.span N (MvPolynomial.map (algebraMap K N) ''
      (L' : Set (MvPolynomial (Fin n) K))) with hLN
  have hLN1 : LN ≤ homogeneousSubmodule (Fin n) N 1 := by
    rw [hLN, Submodule.span_le]
    rintro _ ⟨ℓ, hℓ, rfl⟩
    exact (mem_homogeneousSubmodule 1 _).mpr
      (((mem_homogeneousSubmodule 1 _).mp (hL' hℓ)).map (algebraMap K N))
  have hIK : (I.map (MvPolynomial.map (algebraMap F K))).IsHomogeneous
      (homogeneousSubmodule (Fin n) K) := isHomogeneous_map n (algebraMap F K) hI
  have h1 := isTau_map_of_isTau n μbar hIK h hLN1
    (fun ℓ hℓ => Submodule.subset_span ⟨ℓ, hℓ, rfl⟩)
  have hmap : (I.map (MvPolynomial.map (algebraMap F K))).map
      (MvPolynomial.map (algebraMap K N)) = I.map (MvPolynomial.map (algebraMap F N)) := by
    rw [Ideal.map_map]
    congr 1
    exact RingHom.ext fun p => by
      rw [RingHom.comp_apply, MvPolynomial.map_map, ← IsScalarTower.algebraMap_eq]
  rw [hmap] at h1
  have h2 := hN I hI LN hLN1 h1
  have h3 : linearFormsOver F LN = linearFormsOver F L' := by
    rw [← linearFormsOver_tower n (E := K) LN, hLN, linearFormsOver_span_map L' hL']
  rwa [h3] at h2

/-- Lemma 12, p. 225: "Now, let us consider the case in which `k'` is finitely separably
algebraic.  We may assume that `k'` is Galois extension of `k`."  A finite separable
extension `K/F` embeds (over `F`) in the separable closure of `F`; the normal closure `N` of `K/F`
there is a finite Galois extension of `F` containing `K`, and the case of `N` is the finite Galois
case. -/
private theorem hasTauOnlyIf_of_finite_separable (hμ : 0 < μbar) {F K : Type u} [Field F] [Field K]
    [Algebra F K] [FiniteDimensional F K] [Algebra.IsSeparable F K] : HasTauOnlyIf n μbar F K := by
  -- a finite Galois extension `N/F` containing `K`
  let S := SeparableClosure F
  let _ : Algebra K S :=
    (IsSepClosed.lift (K := F) (L := K) (M := S)).toRingHom.toAlgebra
  have : IsScalarTower F K S :=
    IsScalarTower.of_algebraMap_eq fun x =>
      ((IsSepClosed.lift (K := F) (L := K) (M := S)).commutes x).symm
  have : FiniteDimensional F (IntermediateField.normalClosure F K S) := inferInstance
  have : IsGalois F (IntermediateField.normalClosure F K S) := IsGalois.normalClosure F K S
  exact fgs_hasTauOnlyIf_of_tower n μbar (N := IntermediateField.normalClosure F K S)
    (hasTauOnlyIf_of_isGalois n μbar hμ)

/-! ### Lemma 12 for purely transcendental extensions -/

/-- A family `y` in an intermediate field `P`, whose image in the ambient field generates `P`
as a field, generates the field `P` itself.  (Bookkeeping: the paper identifies the family with
its image.) -/
private theorem fgs_adjoin_range_eq_top {F K : Type*} [Field F] [Field K] [Algebra F K]
    {ι : Type*} (P : IntermediateField F K) (y : ι → P)
    (hy : IntermediateField.adjoin F (Set.range fun i => (y i : K)) = P) :
    IntermediateField.adjoin F (Set.range y) = ⊤ := by
  apply IntermediateField.map_injective P.val
  rw [IntermediateField.adjoin_map, ← AlgHom.fieldRange_eq_map, IntermediateField.fieldRange_val,
    ← Set.range_comp]
  exact hy

/-- Lemma 12, p. 224: "Since `k'` is then finitely separably algebraic over an extension of `k`
by a finite number of independent variables, it is sufficient to prove the assertion in two
cases; one in which `k' = k(u)` with a variable `u`, ...".  The purely transcendental extension
`F(x₁, …, x_m)` is built one variable at a time, `F ⊆ F(x₁, …, x_{m-1}) ⊆ F(x₁, …, x_m)`
(`hasTauOnlyIf_of_transcendental` for the last variable, the induction hypothesis for the others,
`hasTauOnlyIf_trans` to combine); for `m = 0` the extension is trivial, hence finite separable.
The paper does not argue the induction. -/
private theorem hasTauOnlyIf_of_algebraicIndependent (hμ : 0 < μbar) :
    ∀ (m : ℕ) {F K : Type u} [Field F] [Field K] [Algebra F K] (x : Fin m → K),
      AlgebraicIndependent F x → IntermediateField.adjoin F (Set.range x) = ⊤ →
        HasTauOnlyIf n μbar F K := by
  intro m
  induction m with
  | zero =>
    intro F K _ _ _ x _ hx
    -- no variables: `K = F`, a finite separable extension
    have hrange : Set.range x = ∅ := Set.range_eq_empty x
    rw [hrange, IntermediateField.adjoin_empty] at hx
    have hsurj : Function.Surjective (algebraMap F K) := fun y => by
      have hy : y ∈ (⊥ : IntermediateField F K) := hx ▸ IntermediateField.mem_top
      exact IntermediateField.mem_bot.mp hy
    have : FiniteDimensional F K := Module.Finite.of_surjective (Algebra.linearMap F K) hsurj
    have : Algebra.IsSeparable F K :=
      ⟨fun y => by
        obtain ⟨a, rfl⟩ := hsurj y
        exact isSeparable_algebraMap a⟩
    exact hasTauOnlyIf_of_finite_separable n μbar hμ
  | succ m ih =>
    intro F K _ _ _ x hx hspan
    set E : IntermediateField F K :=
      IntermediateField.adjoin F (Set.range (x ∘ Fin.castSucc)) with hE
    -- the first `m` variables, as a family in `E`
    have hxE : ∀ i : Fin m, x (Fin.castSucc i) ∈ E := fun i =>
      IntermediateField.subset_adjoin F _ ⟨i, rfl⟩
    let y : Fin m → E := fun i => ⟨x (Fin.castSucc i), hxE i⟩
    have hy : AlgebraicIndependent F y :=
      AlgebraicIndependent.of_comp E.val (hx.comp Fin.castSucc (Fin.castSucc_injective m))
    have hyspan : IntermediateField.adjoin F (Set.range y) = ⊤ :=
      fgs_adjoin_range_eq_top E y rfl
    -- `F ⊆ E` by induction
    have h₁ : HasTauOnlyIf n μbar F E := ih y hy hyspan
    -- `K = E(u)` with `u = x_m` transcendental over `E`
    have hu : Transcendental E (x (Fin.last m)) := by
      have h := hx.transcendental_adjoin (s := Set.range (Fin.castSucc : Fin m → Fin (m + 1)))
        (i := Fin.last m) (by rintro ⟨j, hj⟩; exact (Fin.castSucc_lt_last j).ne hj)
      rw [← Set.range_comp] at h
      exact IntermediateField.transcendental_adjoin_iff.mpr h
    have hK : IntermediateField.adjoin E {x (Fin.last m)} = ⊤ := by
      apply IntermediateField.restrictScalars_injective F
      rw [IntermediateField.adjoin_adjoin_left, IntermediateField.restrictScalars_top, ← hspan]
      congr 1
      ext z
      constructor
      · rintro (⟨j, rfl⟩ | rfl)
        · exact ⟨Fin.castSucc j, rfl⟩
        · exact ⟨Fin.last m, rfl⟩
      · rintro ⟨j, rfl⟩
        induction j using Fin.lastCases with
        | last => exact Or.inr rfl
        | cast j => exact Or.inl ⟨j, rfl⟩
    have h₂ : HasTauOnlyIf n μbar E K :=
      hasTauOnlyIf_of_transcendental n μbar hμ (x (Fin.last m)) hu hK
    exact hasTauOnlyIf_trans n μbar h₁ h₂

/-! ### Lemma 12 for finitely generated subfields of a separable extension -/

/-- Lemma 12, p. 224: "Therefore, we may and shall assume that `k'` is finitely generated over
`k`.  Since `k'` is then finitely separably algebraic over an extension of `k` by a finite number
of independent variables, it is sufficient to prove the assertion in two cases; one in which
`k' = k(u)` with a variable `u`, and the other in which `k'` is finitely separably algebraic over
`k`."  Here `k'` is the finitely generated subfield `E` of the separable extension; the first
sentence about `E` is MacLane's criterion (p. 223, footnote 4, `isSeparableFieldExtension_iff`):
`E` is separably algebraic over `P = k(x)` for an algebraically independent family `x`.  The paper
does not argue that `x` is finite (a finitely generated field extension has finite transcendence
degree) nor that `E/P` is finite (finitely generated and algebraic); both are proved here.  The
two cases are the finite separable case (`hasTauOnlyIf_of_finite_separable`, for `P ⊆ E`) and the
purely transcendental case (`hasTauOnlyIf_of_algebraicIndependent`, for `k ⊆ P`), combined by
`hasTauOnlyIf_trans`. -/
private theorem hasTauOnlyIf_of_fg [Hironaka.Cited.IsSeparableFieldExtensionIff.{u}] (hμ : 0 < μbar) {k k' : Type u} [Field k] [Field k']
    [Algebra k k'] (hsep : IsSeparableFieldExtension k k') (E : IntermediateField k k')
    (hE : E.FG) : HasTauOnlyIf n μbar k E := by
  -- MacLane's criterion: `E` is separably algebraic over `P = k(x)`, `x` algebraically independent
  have hEfg := hE
  obtain ⟨s, hs⟩ := hE
  obtain ⟨ι, x, hx, hsepx⟩ := (isSeparableFieldExtension_iff k k').mp hsep E ⟨s, hs.symm⟩
  -- gap (i): the family `x` is finite, since `E` is finitely generated over `k`
  have : Algebra.EssFiniteType k E := IntermediateField.essFiniteType_iff.mpr hEfg
  have : Finite ι := finite_of_algebraicIndependent hx
  let e : Fin (Nat.card ι) ≃ ι := (Finite.equivFin ι).symm
  have hr : Set.range (fun i => x (e i)) = Set.range x := e.surjective.range_comp x
  -- `P = k(x_1, …, x_m)`
  set P : IntermediateField k E := IntermediateField.adjoin k (Set.range x)
  have hxP : ∀ i, x (e i) ∈ P := fun i => IntermediateField.subset_adjoin k _ ⟨e i, rfl⟩
  let y : Fin (Nat.card ι) → P := fun i => ⟨x (e i), hxP i⟩
  have hy : AlgebraicIndependent k y :=
    AlgebraicIndependent.of_comp P.val (hx.comp e e.injective)
  have hyspan : IntermediateField.adjoin k (Set.range y) = ⊤ :=
    fgs_adjoin_range_eq_top P y (by
      show IntermediateField.adjoin k (Set.range fun i => x (e i)) =
        IntermediateField.adjoin k (Set.range x)
      rw [hr])
  -- case one: `P/k` is purely transcendental
  have h₁ : HasTauOnlyIf n μbar k P :=
    hasTauOnlyIf_of_algebraicIndependent n μbar hμ _ y hy hyspan
  -- gap (ii): `E/P` is finite (finitely generated and algebraic)
  have : Algebra.EssFiniteType P E := Algebra.EssFiniteType.of_comp k P E
  have : Algebra.IsAlgebraic P E := inferInstance
  have : FiniteDimensional P E := Algebra.finite_of_essFiniteType_of_isAlgebraic
  -- case two: `E/P` is finite separable
  have h₂ : HasTauOnlyIf n μbar P E := hasTauOnlyIf_of_finite_separable n μbar hμ
  -- gap (iii): the tower `k ⊆ P ⊆ E`
  exact hasTauOnlyIf_trans n μbar h₁ h₂

end FGSep




section FgSub

attribute [local instance] MvPolynomial.gradedAlgebra

variable (n μbar : ℕ)

/-- A polynomial whose image under an injective ring map is homogeneous is homogeneous. -/
private theorem fgb_isHomogeneous_of_map {R S : Type*} [CommSemiring R] [CommSemiring S]
    {f : R →+* S} (hf : Function.Injective f) {p : MvPolynomial (Fin n) R} {d : ℕ}
    (hp : (map f p).IsHomogeneous d) : p.IsHomogeneous d := by
  intro m hm
  exact hp (by rw [coeff_map]; exact fun h => hm (hf (by simpa using h)))

/-- A polynomial over `k'` with all coefficients in an intermediate field `E` comes from `E[X]`. -/
private theorem fgb_exists_map_of_coeffs_subset {k k' : Type u} [Field k] [Field k'] [Algebra k k']
    (E : IntermediateField k k') (c : MvPolynomial (Fin n) k') (hc : (c.coeffs : Set k') ⊆ E) :
    ∃ cE : MvPolynomial (Fin n) E, map (algebraMap E k') cE = c := by
  have : c ∈ Set.range (MvPolynomial.map (algebraMap E k')) := by
    rw [mem_range_map_iff_coeffs_subset]
    intro x hx
    exact ⟨⟨x, hc hx⟩, rfl⟩
  exact this

section Good

variable {k k' : Type u} [Field k] [Field k'] [Algebra k k']

/-- `fgb_Good P x`: the polynomial `x ∈ k'[X]` is, for every intermediate field `E` containing a
suitable finite subset `F` of `k'`, the image of an element of `P E ⊆ E[X]`. -/
private def fgb_Good (P : ∀ E : IntermediateField k k', Set (MvPolynomial (Fin n) E))
    (x : MvPolynomial (Fin n) k') : Prop :=
  ∃ F : Finset k', ∀ E : IntermediateField k k', (F : Set k') ⊆ E →
    ∃ xE ∈ P E, map (algebraMap E k') xE = x

private theorem fgb_good_zero (P : ∀ E : IntermediateField k k', Set (MvPolynomial (Fin n) E))
    (h0 : ∀ E : IntermediateField k k', (0 : MvPolynomial (Fin n) E) ∈ P E) : fgb_Good n P 0 :=
  ⟨∅, fun E _ => ⟨0, h0 E, map_zero _⟩⟩

private theorem fgb_good_add (P : ∀ E : IntermediateField k k', Set (MvPolynomial (Fin n) E))
    (hadd : ∀ (E : IntermediateField k k') (a b : MvPolynomial (Fin n) E), a ∈ P E → b ∈ P E → a + b ∈ P E) {x y : MvPolynomial (Fin n) k'}
    (hx : fgb_Good n P x) (hy : fgb_Good n P y) : fgb_Good n P (x + y) := by
  classical
  obtain ⟨F, hF⟩ := hx
  obtain ⟨G, hG⟩ := hy
  refine ⟨F ∪ G, fun E hE => ?_⟩
  rw [Finset.coe_union, Set.union_subset_iff] at hE
  obtain ⟨a, ha, rfl⟩ := hF E hE.1
  obtain ⟨b, hb, rfl⟩ := hG E hE.2
  exact ⟨a + b, hadd E a b ha hb, map_add _ _ _⟩

private theorem fgb_good_mul (P : ∀ E : IntermediateField k k', Set (MvPolynomial (Fin n) E))
    (hmul : ∀ (E : IntermediateField k k') (a b : MvPolynomial (Fin n) E), a ∈ P E → b ∈ P E → a * b ∈ P E) {x y : MvPolynomial (Fin n) k'}
    (hx : fgb_Good n P x) (hy : fgb_Good n P y) : fgb_Good n P (x * y) := by
  classical
  obtain ⟨F, hF⟩ := hx
  obtain ⟨G, hG⟩ := hy
  refine ⟨F ∪ G, fun E hE => ?_⟩
  rw [Finset.coe_union, Set.union_subset_iff] at hE
  obtain ⟨a, ha, rfl⟩ := hF E hE.1
  obtain ⟨b, hb, rfl⟩ := hG E hE.2
  exact ⟨a * b, hmul E a b ha hb, map_mul _ _ _⟩

private theorem fgb_good_mul_left (P : ∀ E : IntermediateField k k', Set (MvPolynomial (Fin n) E))
    (hmul : ∀ (E : IntermediateField k k') (c a : MvPolynomial (Fin n) E), a ∈ P E → c * a ∈ P E)
    (c : MvPolynomial (Fin n) k') {x : MvPolynomial (Fin n) k'} (hx : fgb_Good n P x) :
    fgb_Good n P (c * x) := by
  classical
  obtain ⟨F, hF⟩ := hx
  refine ⟨F ∪ c.coeffs, fun E hE => ?_⟩
  rw [Finset.coe_union, Set.union_subset_iff] at hE
  obtain ⟨a, ha, rfl⟩ := hF E hE.1
  obtain ⟨cE, rfl⟩ := fgb_exists_map_of_coeffs_subset n E c hE.2
  exact ⟨cE * a, hmul E cE a ha, map_mul _ _ _⟩

/-- Intersection: two `fgb_Good` witnesses for the same `x` combine (`map` is injective). -/
private theorem fgb_good_inter (P Q : ∀ E : IntermediateField k k', Set (MvPolynomial (Fin n) E))
    {x : MvPolynomial (Fin n) k'} (hP : fgb_Good n P x) (hQ : fgb_Good n Q x) :
    fgb_Good n (fun E => P E ∩ Q E) x := by
  classical
  obtain ⟨F, hF⟩ := hP
  obtain ⟨G, hG⟩ := hQ
  refine ⟨F ∪ G, fun E hE => ?_⟩
  rw [Finset.coe_union, Set.union_subset_iff] at hE
  obtain ⟨a, ha, h1⟩ := hF E hE.1
  obtain ⟨b, hb, h2⟩ := hG E hE.2
  have hab : a = b := MvPolynomial.map_injective _ (algebraMap E k').injective (h1.trans h2.symm)
  subst hab
  exact ⟨a, ⟨ha, hb⟩, h1⟩

/-- Every element of the extension `I k'[X]` of an ideal of `k[X]` comes, after adjoining finitely
many elements of `k'` to `k`, from `I E[X]`. -/
private theorem fgb_good_ideal_map {I : Ideal (MvPolynomial (Fin n) k)}
    {x : MvPolynomial (Fin n) k'} (hx : x ∈ I.map (map (algebraMap k k'))) :
    fgb_Good n (fun E : IntermediateField k k' =>
      ((I.map (map (algebraMap k E)) : Ideal (MvPolynomial (Fin n) E)) :
        Set (MvPolynomial (Fin n) E))) x := by
  have hx' : x ∈ Ideal.span (map (algebraMap k k') '' (I : Set (MvPolynomial (Fin n) k))) := hx
  clear hx
  induction hx' using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨g, hg, rfl⟩ := hx
    refine ⟨∅, fun E _ => ⟨map (algebraMap k E) g, Ideal.mem_map_of_mem _ hg, ?_⟩⟩
    rw [map_map]
    congr 1
  | zero => exact fgb_good_zero n _ fun E => zero_mem _
  | add x y _ _ hx hy => exact fgb_good_add n _ (fun E a b ha hb => add_mem ha hb) hx hy
  | smul c x _ hx =>
    exact fgb_good_mul_left n _ (fun E c a ha => Ideal.mul_mem_left _ c ha) c hx

/-- Every element of the `k'`-algebra generated by a set of linear forms comes, after adjoining
finitely many elements of `k'` to `k`, from the `E`-algebra generated by `L' ∩ E[X]₁`. -/
private theorem fgb_good_adjoin {L' : Submodule k' (MvPolynomial (Fin n) k')}
    (hL' : L' ≤ homogeneousSubmodule (Fin n) k' 1) {x : MvPolynomial (Fin n) k'}
    (hx : x ∈ Algebra.adjoin k' (L' : Set (MvPolynomial (Fin n) k'))) :
    fgb_Good n (fun E : IntermediateField k k' =>
      (Algebra.adjoin E (linearFormsOver E L' : Set (MvPolynomial (Fin n) E)) :
        Set (MvPolynomial (Fin n) E))) x := by
  classical
  induction hx using Algebra.adjoin_induction with
  | mem x hx =>
    refine ⟨x.coeffs, fun E hE => ?_⟩
    obtain ⟨xE, rfl⟩ := fgb_exists_map_of_coeffs_subset n E x hE
    refine ⟨xE, Algebra.subset_adjoin ⟨hx, ?_⟩, rfl⟩
    rw [SetLike.mem_coe, mem_homogeneousSubmodule]
    exact fgb_isHomogeneous_of_map n (algebraMap E k').injective
      ((mem_homogeneousSubmodule _ _).mp (hL' hx))
  | algebraMap r =>
    refine ⟨{r}, fun E hE => ?_⟩
    have hr : r ∈ E := hE (Finset.mem_singleton_self r)
    refine ⟨algebraMap E _ ⟨r, hr⟩, Subalgebra.algebraMap_mem _ _, ?_⟩
    simp [MvPolynomial.algebraMap_eq]
  | add x y _ _ hx hy =>
    exact fgb_good_add n _ (fun E a b ha hb => add_mem ha hb) hx hy
  | mul x y _ _ hx hy =>
    exact fgb_good_mul n _ (fun E a b ha hb => mul_mem ha hb) hx hy

/-- Every element of `(I k'[X] ∩ k'[L']) k'[X]` comes, after adjoining finitely many elements of
`k'` to `k`, from `(I E[X] ∩ E[L' ∩ E[X]₁]) E[X]`. -/
private theorem fgb_good_span {I : Ideal (MvPolynomial (Fin n) k)}
    {L' : Submodule k' (MvPolynomial (Fin n) k')}
    (hL' : L' ≤ homogeneousSubmodule (Fin n) k' 1) {x : MvPolynomial (Fin n) k'}
    (hx : x ∈ Ideal.span ((I.map (map (algebraMap k k')) : Set (MvPolynomial (Fin n) k')) ∩
      (Algebra.adjoin k' (L' : Set (MvPolynomial (Fin n) k')) :
        Set (MvPolynomial (Fin n) k')))) :
    fgb_Good n (fun E : IntermediateField k k' =>
      (Ideal.span (((I.map (map (algebraMap k E)) : Ideal (MvPolynomial (Fin n) E)) :
        Set (MvPolynomial (Fin n) E)) ∩
        (Algebra.adjoin E (linearFormsOver E L' : Set (MvPolynomial (Fin n) E)) :
          Set (MvPolynomial (Fin n) E))) : Set (MvPolynomial (Fin n) E))) x := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨F, hF⟩ := fgb_good_inter n _ _ (fgb_good_ideal_map n hx.1) (fgb_good_adjoin n hL' hx.2)
    exact ⟨F, fun E hE => by
      obtain ⟨a, ha, h⟩ := hF E hE
      exact ⟨a, Ideal.subset_span ha, h⟩⟩
  | zero => exact fgb_good_zero n _ fun E => zero_mem _
  | add x y _ _ hx hy => exact fgb_good_add n _ (fun E a b ha hb => add_mem ha hb) hx hy
  | smul c x _ hx =>
    exact fgb_good_mul_left n _ (fun E c a ha => Ideal.mul_mem_left _ c ha) c hx

end Good

/-- Lemma 12, p. 224: "Since L' is a k'-module of finite type, there exists a subfield k_1 of k'
which is finitely generated over k and such that the same equalities for μ ≤ μ̄ remain valid if we
replace k' by k_1 and L' by L' ∩ k_1[X]_1. Therefore, we may and shall assume that k' is finitely
generated over k."  The paper does not argue this step.  Proof: the ideal generated by the
homogeneous elements of `I` of degree `≤ μ̄` is generated by finitely many of them (Hilbert's basis
theorem); for each of them the hypothesis over `k'` gives a finite expression; the finitely many
elements of `k'` occurring in these expressions generate `E`.  (Finite type of `L'` is not used.) -/
private theorem exists_fg_isTau {k k' : Type u} [Field k] [Field k'] [Algebra k k']
    {I : Ideal (MvPolynomial (Fin n) k)} (hI : I.IsHomogeneous (homogeneousSubmodule (Fin n) k))
    {L' : Submodule k' (MvPolynomial (Fin n) k')} (hL' : L' ≤ homogeneousSubmodule (Fin n) k' 1)
    (h : IsTauSubmoduleMv k' n (I.map (MvPolynomial.map (algebraMap k k'))) L' μbar) :
    ∃ E : IntermediateField k k', E.FG ∧
      IsTauSubmoduleMv E n (I.map (MvPolynomial.map (algebraMap k E))) (linearFormsOver E L')
        μbar := by
  classical
  -- the homogeneous elements of `I` of degree `≤ μ̄` generate `I_{≤ μ̄}`, which has a finite basis
  set J : Set (MvPolynomial (Fin n) k) :=
    {g | g ∈ I ∧ ∃ d ≤ μbar, g ∈ homogeneousSubmodule (Fin n) k d} with hJ
  obtain ⟨T, hTJ, hT⟩ := (Submodule.fg_span_iff_fg_span_finset_subset J).mp
    (IsNoetherian.noetherian (Ideal.span J))
  -- each of them gives a finite expression over `k'`
  have hgood : ∀ t ∈ T, fgb_Good n (fun E : IntermediateField k k' =>
      (Ideal.span (((I.map (map (algebraMap k E)) : Ideal (MvPolynomial (Fin n) E)) :
        Set (MvPolynomial (Fin n) E)) ∩
        (Algebra.adjoin E (linearFormsOver E L' : Set (MvPolynomial (Fin n) E)) :
          Set (MvPolynomial (Fin n) E))) : Set (MvPolynomial (Fin n) E)))
      (map (algebraMap k k') t) := by
    intro t ht
    obtain ⟨htI, d, hd, htd⟩ := hTJ ht
    have h1 : map (algebraMap k k') t ∈ I.map (map (algebraMap k k')) :=
      Ideal.mem_map_of_mem _ htI
    have h2 : map (algebraMap k k') t ∈ homogeneousSubmodule (Fin n) k' d :=
      (mem_homogeneousSubmodule _ _).mpr (((mem_homogeneousSubmodule _ _).mp htd).map _)
    exact fgb_good_span n hL' ((h.2 d hd _ h2).mp h1)
  choose! F hF using hgood
  set Fall : Finset k' := T.biUnion F with hFall
  set E : IntermediateField k k' := IntermediateField.adjoin k (Fall : Set k') with hE
  have hsub : ∀ t ∈ T, (F t : Set k') ⊆ E := by
    intro t ht x hx
    exact IntermediateField.subset_adjoin k _
      (by simpa [hFall] using ⟨t, ht, hx⟩)
  refine ⟨E, IntermediateField.fg_adjoin_finset Fall, inf_le_right, fun μ hμ ψ hψ => ⟨fun hψI => ?_, ?_⟩⟩
  · -- the generators `t` lie in the ideal over `E`
    have hgen : ∀ t ∈ T, map (algebraMap k E) t ∈
        Ideal.span (((I.map (map (algebraMap k E)) : Ideal (MvPolynomial (Fin n) E)) :
          Set (MvPolynomial (Fin n) E)) ∩
          (Algebra.adjoin E (linearFormsOver E L' : Set (MvPolynomial (Fin n) E)) :
            Set (MvPolynomial (Fin n) E))) := by
      intro t ht
      obtain ⟨xE, hxE, hx⟩ := hF t ht E (hsub t ht)
      have : xE = map (algebraMap k E) t := by
        refine MvPolynomial.map_injective _ (algebraMap E k').injective ?_
        rw [hx, map_map]
        congr 1
      rw [← this]
      exact hxE
    -- `ψ` lies in the ideal generated by the homogeneous elements of `I` of degree `≤ μ`
    have hX : ∀ x ∈ (map (algebraMap k E) '' (I : Set (MvPolynomial (Fin n) k))),
        ∀ d, homogeneousComponent d x ∈
          (map (algebraMap k E) '' (I : Set (MvPolynomial (Fin n) k))) := by
      rintro _ ⟨g, hg, rfl⟩ d
      exact ⟨homogeneousComponent d g, homogeneousComponent_mem_of_mem hI hg d,
        (homogeneousComponent_map n _ d g).symm⟩
    have hψ1 := homogeneousComponent_mem_span _ hX
      (show ψ ∈ Ideal.span (map (algebraMap k E) '' (I : Set (MvPolynomial (Fin n) k))) from hψI) μ
    simp only [homogeneousComponent_of_mem hψ, ↓reduceIte] at hψ1
    -- those homogeneous elements lie in the ideal generated by the finite set `T`
    have hle1 : Ideal.span {x | x ∈ (map (algebraMap k E) '' (I : Set (MvPolynomial (Fin n) k))) ∧
        ∃ d ≤ μ, x ∈ homogeneousSubmodule (Fin n) E d} ≤
        Ideal.span (map (algebraMap k E) '' (T : Set (MvPolynomial (Fin n) k))) := by
      rw [Ideal.span_le]
      rintro _ ⟨⟨g, hg, rfl⟩, d, hd, hgd⟩
      have hgJ : g ∈ J := ⟨hg, d, hd.trans hμ, (mem_homogeneousSubmodule _ _).mpr
        (fgb_isHomogeneous_of_map n (algebraMap k E).injective
          ((mem_homogeneousSubmodule _ _).mp hgd))⟩
      have hgT : g ∈ Ideal.span (T : Set (MvPolynomial (Fin n) k)) := by
        have h0 : g ∈ Submodule.span (MvPolynomial (Fin n) k) J := Submodule.subset_span hgJ
        rw [hT] at h0
        exact h0
      have := Ideal.mem_map_of_mem (map (algebraMap k E)) hgT
      rwa [Ideal.map_span] at this
    have hle2 : Ideal.span (map (algebraMap k E) '' (T : Set (MvPolynomial (Fin n) k))) ≤
        Ideal.span (((I.map (map (algebraMap k E)) : Ideal (MvPolynomial (Fin n) E)) :
          Set (MvPolynomial (Fin n) E)) ∩
          (Algebra.adjoin E (linearFormsOver E L' : Set (MvPolynomial (Fin n) E)) :
            Set (MvPolynomial (Fin n) E))) := by
      rw [Ideal.span_le]
      rintro _ ⟨t, ht, rfl⟩
      exact hgen t ht
    exact hle2 (hle1 hψ1)
  · exact fun hψS => (Ideal.span_le.mpr fun _ hx => hx.1) hψS

end FgSub


end Lemma12Aux

section Lemma12

variable (k : Type u) [Field k] {k' : Type u} [Field k'] [Algebra k k'] {n : ℕ}

attribute [local instance] MvPolynomial.gradedAlgebra

/-- Lemma 12, p. 223: "Let `k[X] = k[X₁, …, X_n]` be a polynomial ring of `n` indeterminates over
a field `k`.  Let `I` be a homogeneous ideal in `k[X]`.  Let `k'` be a field extension of `k`
which is separable over `k`.  Let `I' = I k'[X]`.  We denote by `k[X]_μ`, `I_μ`, `k'[X]_μ`,
`I'_μ` the homogeneous parts of degree `μ` of `k[X]`, `I`, `k'[X]`, `I'` respectively.  Let
`L'` be a `k'`-submodule of `k'[X]₁`, and let `L = L' ∩ k[X]₁`.  Let `μ̄` be a positive
integer.  Then we have `k'[X]_μ ∩ (I' ∩ k'[L']) k'[X] = I'_μ` for all `μ ≤ μ̄`, if and only if
`k[X]_μ ∩ (I ∩ k[L]) k[X] = I_μ` for all `μ ≤ μ̄`."

Separability of `k'/k` is `IsSeparableFieldExtension k k'` (the tensor-product definition of
pp. 211–212; `k'` is not assumed algebraic over `k`); `I'` is `I.map (MvPolynomial.map
(algebraMap k k'))` and `L` is `linearFormsOver k L'`.  Both sides are stated through
`IsTauSubmoduleMv`, whose first conjunct (`L' ⊆ k'[X]₁`, resp. `L ⊆ k[X]₁`) holds by
hypothesis, resp. by construction.

Proof as printed (pp. 224–225), in the printed order; each step is a lemma of the section
`Lemma12Aux` above (`HasTauOnlyIf n μ̄ F K` is the only-if part for the extension `K/F`):

* "The if-part of the assertion is clear." (`isTau_map_of_isTau`.)
* Only-if, p. 224: "Since `L'` is a `k'`-module of finite type, there exists a subfield `k₁` of `k'`
  which is finitely generated over `k` and such that the same equalities for `μ ≤ μ̄` remain valid if
  we replace `k'` by `k₁` and `L'` by `L' ∩ k₁[X]₁`." (`exists_fg_isTau`; the paper gives no
  argument.)  "Since `k'` is then finitely separably algebraic over an extension of `k` by a finite
  number of independent variables, it is sufficient to prove the assertion in two cases" (`hasTauOnlyIf_of_fg`:
  MacLane's criterion `isSeparableFieldExtension_iff`, a cited leaf; finiteness of the family of
  variables; the tower step `hasTauOnlyIf_trans`; `hasTauOnlyIf_of_algebraicIndependent` for the
  variables one at a time).
* "Let us first consider the case in which `k' = k(u)` with a variable `u` over `k`. Let `𝔬` be the
  localization of `k[u]` with respect to the prime ideal `(u)k[u]`." (`hasTauOnlyIf_of_transcendental`,
  which supplies `𝔬 = k[u]_{(u)}` as a principal ideal domain with fraction field `k(u)` and `β : u ↦ 0`, and applies
  `hasTauOnlyIf_of_pid_retraction`.)  There: the direct summand and the base `(Z, Y)`
  (`pid_exists_adapted_basis`), claim (1) (`pid_mem_span_of_mem_span`, with `I'' ∩ 𝔬[X] = I' ∩ 𝔬[X]`
  and `β(I'' ∩ 𝔬[X]) ⊆ I`: `pid_map_mem_of_map_mem`), the specialization `β`, the equality of ranks
  (`pid_linearIndependent_map`), "if `L'` is the smallest `k'`-submodule [...] then we must have
  `L' = L'₁`", and "in general, `L'` must contain the smallest one with the same property, by Lemma 10".
* "Now, let us consider the case in which `k'` is finitely separably algebraic. We may assume that
  `k'` is Galois extension of `k`." (`hasTauOnlyIf_of_finite_separable`, via the normal closure.)
  "We may also assume that `L'` is the smallest [...]. Such `L'` is unique (see Lemma 10) and therefore
  `L'` must be invariant under the operation of Galois group [...]. Since `k'` is separable over `k`,
  the invariance of `L'` implies that `L'` is generated by `L = L' ∩ k[X]₁` over the field `k'`. Then
  the assertion follows without difficulty." (`hasTauOnlyIf_of_isGalois`.)

Gaps in the paper filled (each step the paper leaves unargued): the existence of `k₁`; that the family
of independent variables is finite and that `k'` is finite over `k(x)`; the tower step; the reduction
of "finitely separably algebraic" to "Galois"; that the Galois-invariant smallest submodule is
generated by its `k`-points, and "the assertion follows without difficulty"; `I'' ∩ 𝔬[X] = I' ∩ 𝔬[X]`
and the rank of `β(L'')`. -/
@[blueprint "lem:III.12"
  (statement := /-- Let $k[X]=k[X_1,\dots,X_n]$ be a polynomial ring of $n$ indeterminates
    over a field $k$. Let $I$ be a homogeneous ideal in $k[X]$. Let $k'$ be a field extension
    of $k$ which is separable over $k$ (\cref{lem:III.4-separable-characterization}). Let
    $I'=Ik'[X]$. We denote by $k[X]_\mu$, $I_\mu$, $k'[X]_\mu$, $I'_\mu$ the homogeneous parts
    of degree $\mu$ of $k[X]$, $I$, $k'[X]$, $I'$ respectively. Let $L'$ be a $k'$-submodule
    of $k'[X]_1$, and let $L=L'\cap k[X]_1$. Let $\bar\mu$ be a positive integer. Then we have
    $k'[X]_\mu\cap(I'\cap k'[L'])k'[X]=I'_\mu$ for all $\mu\le\bar\mu$, if and only if
    $k[X]_\mu\cap(I\cap k[L])k[X]=I_\mu$ for all $\mu\le\bar\mu$. (Lemma 12, p.~223.) -/)
  (proof := /-- The if-part of the assertion is clear. We shall prove the only-if-part.
    Since $L'$ is a $k'$-module of finite type, there exists a subfield $k_1$ of $k'$ which is
    finitely generated over $k$ and such that the same equalities for $\mu\le\bar\mu$ remain
    valid if we replace $k'$ by $k_1$ and $L'$ by $L'\cap k_1[X]_1$. Therefore, we may and
    shall assume that $k'$ is finitely generated over $k$. Since $k'$ is then finitely
    separably algebraic over an extension of $k$ by a finite number of independent variables,
    it is sufficient to prove the assertion in two cases; one in which $k'=k(u)$ with a
    variable $u$, and the other in which $k'$ is finitely separably algebraic over $k$.

    Let us first consider the case in which $k'=k(u)$ with a variable $u$ over $k$. Let
    $\mathfrak o$ be the localization of $k[u]$ with respect to the prime ideal $(u)k[u]$. Let
    $L''=L'\cap\mathfrak o[X]_1$ and $I''=I\mathfrak o[X]$. It is clear that
    $I''_\mu=I'_\mu\cap\mathfrak o[X]_\mu$ for all $\mu$, because a $k$-free base of $I_\mu$ is
    necessarily a $k'$-free base of $I'_\mu$ and can be extended to a $k$-free base of
    $k[X]_\mu$ which is necessarily an $\mathfrak o$-free base of $\mathfrak o[X]_\mu$. We claim
    that (1) $\mathfrak o[X]_\mu\cap(I''\cap\mathfrak o[L''])\mathfrak o[X]=I''_\mu
    \ (=I'_\mu\cap\mathfrak o[X]_\mu)$ for all $\mu\le\bar\mu$. It suffices to show
    $(I'\cap k'[L'])k'[X]\cap\mathfrak o[X]=(I''\cap\mathfrak o[L''])\mathfrak o[X]$. Since
    $\mathfrak o$ is a valuation ring, $L''$ must be a direct summand of the free
    $\mathfrak o$-module $\mathfrak o[X]_1$. Let $(Z_1,\dots,Z_r)$ be an $\mathfrak o$-free base
    of $L''$, and let us extend it to an $\mathfrak o$-free base $(Z_1,\dots,Z_r,Y_1,\dots,Y_s)$
    of $\mathfrak o[X]_1$. Then $r+s=n$ and $\mathfrak o[X]=\mathfrak o[Z,Y]$. Thus
    $(I'\cap k'[L'])k'[X]\cap\mathfrak o[X]=(I'\cap k'[Z])k'[Z,Y]\cap\mathfrak o[Z,Y]
    =(I'\cap k'[Z]\cap\mathfrak o[Z])\mathfrak o[Z,Y]
    =(I'\cap\mathfrak o[Z,Y]\cap\mathfrak o[Z])\mathfrak o[Z,Y]
    =(I''\cap\mathfrak o[Z])\mathfrak o[Z,Y]=(I''\cap\mathfrak o[L''])\mathfrak o[X]$.
    Thus we have established (1). Now, let $\beta$ be the homomorphism of $\mathfrak o$ onto
    $k$ which induces the identity in $k$ and annihilates $u$. This $\beta$ can be extended to
    a homomorphism of $\mathfrak o[X]$ onto $k[X]$ in such a way that $\beta(X_i)=X_i$ for all
    $i$. Then we have, by (1), $I_\mu=\beta(I''_\mu)\subseteq k[X]_\mu\cap
    (I\cap k[\beta(L'')])k[X]$, for all $\mu\le\bar\mu$. Hence, (2)
    $I_\mu=k[X]_\mu\cap(I\cap k[\beta(L'')])k[X]$ for all $\mu\le\bar\mu$. Since $L''$ is a
    direct summand of $\mathfrak o[X]_1$, the $k$-module $\beta(L'')$ has the same rank as the
    $k'$-module $L'$. Moreover, by the if-part of the assertion, if $L'_1$ is the
    $k'$-module generated by $\beta(L'')$ then $L'_1$ has the same property as $L'$. If
    $L'$ is the smallest $k'$-submodule of $k'[X]_1$ with the property, then we must have
    $L'=L'_1$; hence, $\beta(L'')=L'\cap k[X]_1=L$. Therefore, in this case, (2) implies
    the lemma. Now, in general, $L'$ must contain the smallest one with the same property, by
    \cref{lem:III.10}, and therefore $L'\cap k[X]_1=L$ must have the required property. This
    completes the proof for the purely transcendental case.

    Now, let us consider the case in which $k'$ is finitely separably algebraic. We may
    assume that $k'$ is a Galois extension of $k$. We may also assume that $L'$ is the
    smallest $k'$-submodule of $k'[X]_1$ with the property. Such $L'$ is unique (see
    \cref{lem:III.10}) and therefore $L'$ must be invariant under the operation of the Galois
    group of the extension $k'$ over $k$ which operates on $k'[X]$ in a natural way. Since
    $k'$ is separable over $k$, the invariance of $L'$ implies that $L'$ is generated by
    $L=L'\cap k[X]_1$ over the field $k'$. Then the assertion follows without difficulty.

    (Lean: each printed step is one lemma of the section \texttt{Lemma12Aux}; see the docstring of
    \texttt{isTauSubmoduleMv\_map\_iff} for the correspondence. The paper's valuation ring
    $\mathfrak o=k[u]_{(u)}$ enters as a principal ideal domain with fraction field $k(u)$ and a retraction
    $\beta$ onto $k$.)

    \textbf{Gap in the paper filled.} The existence of the finitely generated subfield $k_1$; that the
    family of independent variables given by MacLane's criterion is finite and $k'$ is finite over
    $k(x)$; the tower step (``it is sufficient to prove the assertion in two cases''); the reduction to a
    Galois extension (normal closure); that the smallest submodule, being Galois-invariant, is
    generated by its $k$-points (Galois descent), and ``the assertion follows without difficulty'';
    $I''\cap\mathfrak o[X]=I'\cap\mathfrak o[X]$ and the rank of $\beta(L'')$ are proved. -/)
  (latexEnv := "lemma")]
theorem isTauSubmoduleMv_map_iff [Hironaka.Cited.IsSeparableFieldExtensionIff.{u}] (hsep : IsSeparableFieldExtension k k')
    (I : Ideal (MvPolynomial (Fin n) k))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin n) k))
    (L' : Submodule k' (MvPolynomial (Fin n) k'))
    (hL' : L' ≤ MvPolynomial.homogeneousSubmodule (Fin n) k' 1) (μbar : ℕ) (hμ : 0 < μbar) :
    IsTauSubmoduleMv k' n (I.map (MvPolynomial.map (algebraMap k k'))) L' μbar ↔
      IsTauSubmoduleMv k n I (linearFormsOver k L') μbar := by
  constructor
  · -- only if: the printed proof of pp. 224-225
    intro h
    -- "there exists a subfield `k₁` of `k'` which is finitely generated over `k` and such that the same
    -- equalities for `μ ≤ μ̄` remain valid if we replace `k'` by `k₁` and `L'` by `L' ∩ k₁[X]₁`"
    obtain ⟨E, hE, hPE⟩ := exists_fg_isTau n μbar hI hL' h
    -- "Therefore, we may and shall assume that `k'` is finitely generated over `k`" and the two
    -- cases (`k(u)`, finitely separably algebraic), assembled in `hasTauOnlyIf_of_fg`
    have h1 := hasTauOnlyIf_of_fg n μbar hμ hsep E hE I hI (linearFormsOver E L')
      (fun p hp => hp.2) hPE
    rwa [linearFormsOver_tower] at h1
  · -- "The if-part of the assertion is clear."
    intro hP
    exact isTau_map_of_isTau n μbar hI hP hL' fun ℓ hℓ => ((mem_linearFormsOver).mp hℓ).1

end Lemma12

/-! ### Lemma 13 (pp. 225–226) -/

section Lemma13

variable {R R' : Type u} [CommRing R] [CommRing R'] [IsRegularLocalRing R] [IsRegularLocalRing R']

/-- The polynomial picture `k[Z₁, …, Z_n] → gr_M(R)`, `Z_i ↦ [z_i]`, of a regular system of
parameters `z` is graded: it maps `G_d` onto `gr^d_M(R)` and commutes with taking homogeneous
components. -/
private theorem aeval_mk_graded {n : ℕ} (z : Fin n → R)
    (hz : ∀ i, z i ∈ maximalIdeal R ^ 1)
    (hbij : Function.Bijective (MvPolynomial.aeval (R := R ⧸ maximalIdeal R)
      fun i => AssocGraded.mk (maximalIdeal R) 1 (z i) (hz i))) :
    (∀ (d : ℕ) (p : MvPolynomial (Fin n) (R ⧸ maximalIdeal R)),
      p ∈ MvPolynomial.homogeneousSubmodule (Fin n) (R ⧸ maximalIdeal R) d ↔
        MvPolynomial.aeval (R := R ⧸ maximalIdeal R)
          (fun i => AssocGraded.mk (maximalIdeal R) 1 (z i) (hz i)) p ∈
            AssocGraded.homogeneous (maximalIdeal R) d) ∧
    ∀ (d : ℕ) (p : MvPolynomial (Fin n) (R ⧸ maximalIdeal R)),
      AssocGraded.ofGrPiece (maximalIdeal R) d (grProj (maximalIdeal R) d
        (MvPolynomial.aeval (R := R ⧸ maximalIdeal R)
          (fun i => AssocGraded.mk (maximalIdeal R) 1 (z i) (hz i)) p)) =
        MvPolynomial.aeval (R := R ⧸ maximalIdeal R)
          (fun i => AssocGraded.mk (maximalIdeal R) 1 (z i) (hz i))
          (MvPolynomial.homogeneousComponent d p) := by
  let e := MvPolynomial.aeval (R := R ⧸ maximalIdeal R)
    fun i => AssocGraded.mk (maximalIdeal R) 1 (z i) (hz i)
  -- `e` maps `G_d` into `gr^d_M(R)`: lift a form of degree `d` to a form over `R`
  have h1 : ∀ (d : ℕ) (p : MvPolynomial (Fin n) (R ⧸ maximalIdeal R)),
      p ∈ MvPolynomial.homogeneousSubmodule (Fin n) (R ⧸ maximalIdeal R) d →
        e p ∈ AssocGraded.homogeneous (maximalIdeal R) d := by
    intro d p hp
    obtain ⟨q, rfl⟩ := MvPolynomial.map_surjective _ Ideal.Quotient.mk_surjective p
    have hq : (MvPolynomial.homogeneousComponent d q).map (Ideal.Quotient.mk (maximalIdeal R)) =
        q.map (Ideal.Quotient.mk (maximalIdeal R)) := by
      rw [← MvPolynomial.homogeneousComponent_eq_self hp]
      ext m
      simp only [MvPolynomial.coeff_map, MvPolynomial.coeff_homogeneousComponent]
      split_ifs <;> simp
    rw [← hq]
    show MvPolynomial.aeval _ _ ∈ _
    rw [aeval_mk_map_of_isHomogeneous (maximalIdeal R) z hz
      (MvPolynomial.homogeneousComponent_isHomogeneous d q)]
    exact AssocGraded.mk_mem_homogeneous _ _
  -- taking homogeneous components commutes with `e`
  have h2 : ∀ (d : ℕ) (p : MvPolynomial (Fin n) (R ⧸ maximalIdeal R)),
      AssocGraded.ofGrPiece (maximalIdeal R) d (grProj (maximalIdeal R) d (e p)) =
        e (MvPolynomial.homogeneousComponent d p) := by
    intro d p
    conv_lhs => rw [← MvPolynomial.sum_homogeneousComponent p]
    rw [map_sum, map_sum, map_sum]
    rw [Finset.sum_eq_single d]
    · exact ofGrPiece_grProj_of_mem _
        (h1 d _ (MvPolynomial.homogeneousComponent_mem d p))
    · intro d' _ hd'
      rw [grProj_of_mem_ne _ hd' (h1 d' _ (MvPolynomial.homogeneousComponent_mem d' p)),
        map_zero]
    · intro hd
      rw [MvPolynomial.homogeneousComponent_eq_zero d p (by
        simp only [Finset.mem_range, not_lt] at hd; omega), map_zero, map_zero, map_zero]
  refine ⟨fun d p => ⟨h1 d p, fun hp => ?_⟩, h2⟩
  -- conversely, if `e p ∈ gr^d_M(R)` then all other homogeneous components of `p` vanish
  have hzero : ∀ d', d' ≠ d → MvPolynomial.homogeneousComponent d' p = 0 := by
    intro d' hd'
    apply hbij.1
    rw [← h2, grProj_of_mem_ne _ (Ne.symm hd') hp, map_zero, map_zero]
  have hpd : p = MvPolynomial.homogeneousComponent d p := by
    conv_lhs => rw [← MvPolynomial.sum_homogeneousComponent p]
    rw [Finset.sum_eq_single d (fun d' _ hd' => hzero d' hd')]
    intro hd
    rw [MvPolynomial.homogeneousComponent_eq_zero d p (by
      simp only [Finset.mem_range, not_lt] at hd; omega)]
  rw [hpd]
  exact MvPolynomial.homogeneousComponent_mem d p


/-- Every `T ⊆ gr¹_M(R)` has the property of Definition 6 up to degree `0`
(`gr⁰_M(R) = K ⊆ K[T]`). -/
private theorem isTauSubmodule_zero (J : Ideal R)
    (T : Submodule (R ⧸ maximalIdeal R) (AssocGraded (maximalIdeal R)))
    (hT : T ≤ AssocGraded.homogeneous (maximalIdeal R) 1) : IsTauSubmodule R J T 0 := by
  refine ⟨hT, fun μ hμ ψ hψ => ⟨fun h => ?_, fun h => (Ideal.span_le.mpr fun x hx => hx.1) h⟩⟩
  obtain rfl : μ = 0 := by omega
  obtain ⟨y, rfl⟩ := LinearMap.mem_range.mp hψ
  obtain ⟨⟨a, ha⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  refine Ideal.subset_span ⟨h, ?_⟩
  rw [AssocGraded.ofGrPiece_mk, mk_zero_eq_algebraMap_mk]
  exact Subalgebra.algebraMap_mem _ _

/-- Reindexing a range along `Fin.cast`. -/
private theorem range_subtype_cast {X Y : Type*} {N N' B B' : ℕ} (h : N' = N) (hB : B' = B)
    (f : Fin N → X) (g : X → Y) :
    (Set.range fun i : {i : Fin N' // (i : ℕ) < B'} => g (f (Fin.cast h i.1))) =
      g '' Set.range fun i : {i : Fin N // (i : ℕ) < B} => f i.1 := by
  subst h
  subst hB
  ext y
  constructor
  · rintro ⟨⟨i, hi⟩, rfl⟩
    exact ⟨_, ⟨⟨i, hi⟩, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨⟨i, hi⟩, rfl⟩, rfl⟩
    exact ⟨⟨i, hi⟩, rfl⟩

open Classical in
/-- Lemma 13 for a homomorphism `σ : gr_M(R) → gr_{M'}(R')` sending the class of `a` to the class
of `α(a)` whose image of `gr_M(J, R)` generates `gr_{M'}(J', R')` (Lemma 2). -/
private theorem tauStar_map_of_gradedMap [Hironaka.Cited.IsSeparableFieldExtensionIff.{u}] (α : R →+* R') [IsLocalHom α] (s : Finset R)
    (hs : IsRegularSystemOfParameters R s) (hs' : IsRegularSystemOfParameters R' (s.image α))
    (hinj : Set.InjOn α s) (hsep : RingHom.IsResiduallySeparable α) (J : Ideal R)
    (P' : Ideal R') (hP' : P' = maximalIdeal R')
    (σ : AssocGraded (maximalIdeal R) →+* AssocGraded P')
    (hσ : ∀ (n : ℕ) (a : R) (ha : a ∈ maximalIdeal R ^ n) (ha' : α a ∈ P' ^ n),
      σ (AssocGraded.mk _ n a ha) = AssocGraded.mk P' n (α a) ha')
    (hσJ : Ideal.map σ (grIdeal (maximalIdeal R) J) = grIdeal P' (J.map α)) :
    t R' (J.map α) = t R J ∧
    (∀ i, 1 ≤ i → i ≤ t R J → tau R' (J.map α) i = tau R J i) ∧
    ∀ (h : tau R' (J.map α) (t R' (J.map α)) = tau R J (t R J))
      (z : Fin (tau R J (t R J)) → maximalIdeal R),
      IsRegularSystemOfTauParameters R J (t R J) z →
      IsRegularSystemOfTauParameters R' (J.map α) (t R' (J.map α))
        (fun i => ⟨α (z (Fin.cast h i)), map_nonunit α _ (z (Fin.cast h i)).2⟩) := by
  subst hP'
  -- `ν*(J) = ν*(J')` (Corollary to Lemma 2), hence `t(J) = t(J')` and `μ*(J) = μ*(J')`
  have hν : ∀ i, nuI R J i = nuI R' (J.map α) i :=
    nuI_map_eq_of_mapsRSOP α ⟨s, hs, hs', hinj⟩ J
  have hmuSet : muSet R' (J.map α) = muSet R J := by
    ext μ
    simp only [muSet, Set.mem_ofPred_eq, hν]
  have ht : t R' (J.map α) = t R J := by
    unfold t
    rw [hmuSet]
  have hmu : ∀ a, mu R' (J.map α) a = mu R J a := by
    intro a
    unfold mu
    rw [hmuSet]
  let _ : Field (R ⧸ maximalIdeal R) := Ideal.Quotient.field _
  let _ : Field (R' ⧸ maximalIdeal R') := Ideal.Quotient.field _
  have hMM : ∀ a ∈ maximalIdeal R, α a ∈ maximalIdeal R' := fun a ha => map_nonunit α a ha
  have hαn : ∀ (n : ℕ) (a : R), a ∈ maximalIdeal R ^ n → α a ∈ maximalIdeal R' ^ n := by
    intro n a ha
    have h1 : α a ∈ ((maximalIdeal R) ^ n).map α := Ideal.mem_map_of_mem α ha
    rw [Ideal.map_pow] at h1
    exact Ideal.pow_right_mono (Ideal.map_le_iff_le_comap.mpr hMM) n h1
  let ρ : R ⧸ maximalIdeal R →+* R' ⧸ maximalIdeal R' :=
    Ideal.quotientMap (maximalIdeal R') α fun a ha => hMM a ha
  have hρ : ∀ r, ρ (Ideal.Quotient.mk _ r) = Ideal.Quotient.mk _ (α r) := fun r =>
    Ideal.quotientMap_mk
  let _ : Algebra (R ⧸ maximalIdeal R) (R' ⧸ maximalIdeal R') := ρ.toAlgebra
  have hsep' : IsSeparableFieldExtension (R ⧸ maximalIdeal R) (R' ⧸ maximalIdeal R') := hsep
  -- the polynomial pictures of `gr_M(R)` and `gr_{M'}(R')`
  let z : Fin s.card → R := fun i => ((s.equivFin.symm i : s) : R)
  have hz : ∀ i, z i ∈ maximalIdeal R ^ 1 := fun i => by
    rw [pow_one, ← hs.1]
    exact Ideal.subset_span (s.equivFin.symm i).2
  have hz' : ∀ i, α (z i) ∈ maximalIdeal R' ^ 1 := fun i => hαn 1 _ (hz i)
  have hbij := assocGraded_maximalIdeal_aeval_bijective_of_rsop hs hz
  have hspan' : Ideal.span (Set.range fun i => α (z i)) = maximalIdeal R' := by
    have h := hs'.1
    rw [Finset.coe_image] at h
    rw [← h]
    congr 1
    ext y
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨_, (s.equivFin.symm i).2, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨s.equivFin ⟨x, hx⟩, by simp [z]⟩
  have hn' : (s.card : WithBot ℕ∞) = ringKrullDim R' := by
    rw [← hs'.2, Finset.card_image_of_injOn hinj]
  have hbij' := assocGraded_maximalIdeal_aeval_bijective hspan' hn' hz'
  let e := AlgEquiv.ofBijective _ hbij
  let e' := AlgEquiv.ofBijective _ hbij'
  obtain ⟨hE, hpr⟩ := aeval_mk_graded z hz hbij
  obtain ⟨hE', -⟩ := aeval_mk_graded (fun i => α (z i)) hz' hbij'
  -- `σ` is the coefficient extension along `ρ`, and is `ρ`-semilinear
  have hcomm : ∀ p, σ (e p) = e' (MvPolynomial.map ρ p) := by
    intro p
    have : σ.comp (e : MvPolynomial (Fin s.card) (R ⧸ maximalIdeal R) →+*
        AssocGraded (maximalIdeal R)) =
        (e' : MvPolynomial (Fin s.card) (R' ⧸ maximalIdeal R') →+*
          AssocGraded (maximalIdeal R')).comp (MvPolynomial.map ρ) := by
      refine MvPolynomial.ringHom_ext (fun c => ?_) (fun i => ?_)
      · obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective c
        simp only [RingHom.coe_comp, Function.comp_apply, RingHom.coe_coe, MvPolynomial.map_C,
          e, e', AlgEquiv.ofBijective_apply, MvPolynomial.aeval_C]
        rw [← mk_zero_eq_algebraMap_mk _ r (by simp), hσ 0 r _ (by simp), hρ,
          ← mk_zero_eq_algebraMap_mk]
      · simp only [RingHom.coe_comp, Function.comp_apply, RingHom.coe_coe, MvPolynomial.map_X,
          e, e', AlgEquiv.ofBijective_apply, MvPolynomial.aeval_X]
        exact hσ 1 _ (hz i) (hz' i)
    exact RingHom.congr_fun this p
  have hσsmul : ∀ (c : R ⧸ maximalIdeal R) (x : AssocGraded (maximalIdeal R)),
      σ (c • x) = ρ c • σ x := by
    intro c x
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective c
    rw [Algebra.smul_def, Algebra.smul_def, map_mul, ← mk_zero_eq_algebraMap_mk _ r (by simp),
      hσ 0 r _ (by simp), hρ, ← mk_zero_eq_algebraMap_mk]
  have hspanσ : ∀ X : Set (AssocGraded (maximalIdeal R)),
      Submodule.span (R' ⧸ maximalIdeal R')
          (σ '' (Submodule.span (R ⧸ maximalIdeal R) X : Set (AssocGraded (maximalIdeal R)))) =
        Submodule.span (R' ⧸ maximalIdeal R') (σ '' X) := by
    intro X
    refine le_antisymm (Submodule.span_le.mpr ?_)
      (Submodule.span_mono (Set.image_mono Submodule.subset_span))
    rintro _ ⟨x, hx, rfl⟩
    induction hx using Submodule.span_induction with
    | mem x hx => exact Submodule.subset_span ⟨x, hx, rfl⟩
    | zero => rw [map_zero]; exact zero_mem _
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | smul c x _ hx => rw [hσsmul]; exact Submodule.smul_mem _ _ hx
  have hσ1 : ∀ x ∈ AssocGraded.homogeneous (maximalIdeal R) 1,
      σ x ∈ AssocGraded.homogeneous (maximalIdeal R') 1 := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := exists_mk_eq_of_mem_homogeneous _ hx
    rw [hσ 1 y hy (hαn 1 y hy)]
    exact AssocGraded.mk_mem_homogeneous _ _
  -- the homogeneous ideals `I = gr_M(J, R)` in `k[X]` and `I' = I k'[X]` in `k'[X]`
  let _ : GradedAlgebra (MvPolynomial.homogeneousSubmodule (Fin s.card) (R ⧸ maximalIdeal R)) :=
    MvPolynomial.gradedAlgebra
  have hI : (Ideal.comap e (grIdeal (maximalIdeal R) J)).IsHomogeneous
      (MvPolynomial.homogeneousSubmodule (Fin s.card) (R ⧸ maximalIdeal R)) := by
    intro i p hp
    rw [show ((DirectSum.decompose (MvPolynomial.homogeneousSubmodule (Fin s.card)
      (R ⧸ maximalIdeal R)) p i : MvPolynomial (Fin s.card) (R ⧸ maximalIdeal R))) =
        MvPolynomial.homogeneousComponent i p from
      MvPolynomial.decomposition.decompose'_apply p i, Ideal.mem_comap]
    have hp' : MvPolynomial.aeval (R := R ⧸ maximalIdeal R)
        (fun i => AssocGraded.mk (maximalIdeal R) 1 (z i) (hz i)) p ∈
          grIdeal (maximalIdeal R) J := hp
    show MvPolynomial.aeval _ _ ∈ _
    rw [← hpr]
    obtain ⟨a, haJ, ha, hmk⟩ := grIdeal_le_bound (maximalIdeal R) J hp' i
    rw [← hmk, AssocGraded.ofGrPiece_mk]
    exact mk_mem_grIdeal _ haJ ha
  have hI' : Ideal.comap e' (grIdeal (maximalIdeal R') (J.map α)) =
      (Ideal.comap e (grIdeal (maximalIdeal R) J)).map
        (MvPolynomial.map (algebraMap (R ⧸ maximalIdeal R) (R' ⧸ maximalIdeal R'))) := by
    let eR : MvPolynomial (Fin s.card) (R ⧸ maximalIdeal R) →+* AssocGraded (maximalIdeal R) := e
    let eR' : MvPolynomial (Fin s.card) (R' ⧸ maximalIdeal R') →+*
      AssocGraded (maximalIdeal R') := e'
    have h1 : grIdeal (maximalIdeal R) J = Ideal.map eR (Ideal.comap eR
        (grIdeal (maximalIdeal R) J)) :=
      (Ideal.map_comap_of_surjective eR e.surjective _).symm
    have h2 : σ.comp eR = eR'.comp (MvPolynomial.map ρ) := RingHom.ext hcomm
    have h3 : grIdeal (maximalIdeal R') (J.map α) = Ideal.map eR' (Ideal.map (MvPolynomial.map ρ)
        (Ideal.comap eR (grIdeal (maximalIdeal R) J))) := by
      rw [← hσJ]
      conv_lhs => rw [h1]
      rw [Ideal.map_map, h2, ← Ideal.map_map]
    rw [h3]
    exact Ideal.comap_map_of_bijective eR' e'.bijective
  -- finite-dimensionality of submodules of `gr¹`
  have hfin : ∀ T : Submodule (R ⧸ maximalIdeal R) (AssocGraded (maximalIdeal R)),
      T ≤ AssocGraded.homogeneous (maximalIdeal R) 1 →
        FiniteDimensional (R ⧸ maximalIdeal R) T := fun T hT => by
    have : FiniteDimensional (R ⧸ maximalIdeal R)
        (AssocGraded.homogeneous (maximalIdeal R) 1) :=
      Module.Finite.iff_fg.mpr (homogeneous_fg _ 1)
    exact Submodule.finiteDimensional_of_le hT
  have hfin' : ∀ T : Submodule (R' ⧸ maximalIdeal R') (AssocGraded (maximalIdeal R')),
      T ≤ AssocGraded.homogeneous (maximalIdeal R') 1 →
        FiniteDimensional (R' ⧸ maximalIdeal R') T := fun T hT => by
    have : FiniteDimensional (R' ⧸ maximalIdeal R')
        (AssocGraded.homogeneous (maximalIdeal R') 1) :=
      Module.Finite.iff_fg.mpr (homogeneous_fg _ 1)
    exact Submodule.finiteDimensional_of_le hT
  -- (→) by Lemma 12 (if-part): the `k'`-span of `σ(T)` has the property for `J'`
  have hfwd : ∀ μ, 0 < μ → ∀ T : Submodule (R ⧸ maximalIdeal R) (AssocGraded (maximalIdeal R)),
      IsTauSubmodule R J T μ → IsTauSubmodule R' (J.map α)
        (Submodule.span (R' ⧸ maximalIdeal R')
          (σ '' (T : Set (AssocGraded (maximalIdeal R))))) μ := by
    intro μ hμ T hTJ
    have hL := (isTauSubmodule_iff R J e hE T μ).mp hTJ
    have hL'1 : Submodule.span (R' ⧸ maximalIdeal R') (MvPolynomial.map
        (algebraMap (R ⧸ maximalIdeal R) (R' ⧸ maximalIdeal R')) ''
          ((T.comap e.toLinearMap : Submodule _ _) : Set _)) ≤
        MvPolynomial.homogeneousSubmodule (Fin s.card) (R' ⧸ maximalIdeal R') 1 := by
      rw [Submodule.span_le]
      rintro _ ⟨l, hl, rfl⟩
      exact (hL.1 hl).map _
    have hL' := (isTauSubmoduleMv_map_iff (R ⧸ maximalIdeal R) hsep' _ hI _ hL'1 μ hμ).mpr
      (by rw [linearFormsOver_span_map _ hL.1]; exact hL)
    rw [← hI'] at hL'
    have hmap : Submodule.span (R' ⧸ maximalIdeal R')
        (σ '' (T : Set (AssocGraded (maximalIdeal R)))) =
        (Submodule.span (R' ⧸ maximalIdeal R') (MvPolynomial.map
          (algebraMap (R ⧸ maximalIdeal R) (R' ⧸ maximalIdeal R')) ''
            ((T.comap e.toLinearMap : Submodule _ _) : Set _))).map e'.toLinearMap := by
      rw [Submodule.map_span, ← Set.image_comp]
      congr 1
      ext y
      constructor
      · rintro ⟨x, hx, rfl⟩
        obtain ⟨p, rfl⟩ := e.surjective x
        exact ⟨p, by simpa using hx, by simp [hcomm]; rfl⟩
      · rintro ⟨p, hp, rfl⟩
        refine ⟨e p, by simpa using hp, ?_⟩
        simp [hcomm]
        rfl
    rw [← Submodule.comap_map_eq_of_injective (f := e'.toLinearMap) e'.injective
      (Submodule.span (R' ⧸ maximalIdeal R') _), ← hmap] at hL'
    exact (isTauSubmodule_iff R' (J.map α) e' hE' _ μ).mpr hL'
  -- `σ` in terms of the polynomial pictures: `σ x = e' (k'-extension of e⁻¹ x)`
  have hcomm' : ∀ x : AssocGraded (maximalIdeal R),
      σ x = e' (MvPolynomial.map (algebraMap (R ⧸ maximalIdeal R) (R' ⧸ maximalIdeal R'))
        (e.symm x)) := by
    intro x
    have := hcomm (e.symm x)
    rw [AlgEquiv.apply_symm_apply] at this
    exact this
  -- (←) by Lemma 12 (only-if part): the `k`-points `T = {x ∈ gr¹_M(R) | σ x ∈ T'}` of a
  -- submodule `T'` with the property for `J'` have the property for `J`
  have hbwd : ∀ μ, 0 < μ →
      ∀ T' : Submodule (R' ⧸ maximalIdeal R') (AssocGraded (maximalIdeal R')),
      IsTauSubmodule R' (J.map α) T' μ →
        ∃ T : Submodule (R ⧸ maximalIdeal R) (AssocGraded (maximalIdeal R)),
          IsTauSubmodule R J T μ ∧ ∀ x ∈ T, σ x ∈ T' := by
    intro μ hμ T' hT'J
    have hL' := (isTauSubmodule_iff R' (J.map α) e' hE' T' μ).mp hT'J
    rw [hI'] at hL'
    have hL := (isTauSubmoduleMv_map_iff (R ⧸ maximalIdeal R) hsep' _ hI _ hL'.1 μ hμ).mp hL'
    have hTJ : IsTauSubmodule R J ((linearFormsOver (R ⧸ maximalIdeal R)
        (T'.comap e'.toLinearMap)).map e.toLinearMap) μ :=
      (isTauSubmodule_iff R J e hE _ μ).mpr
        (by rw [Submodule.comap_map_eq_of_injective (f := e.toLinearMap) e.injective]; exact hL)
    refine ⟨_, hTJ, fun x hx => ?_⟩
    obtain ⟨p, hp, rfl⟩ := Submodule.mem_map.mp hx
    have hp1 : MvPolynomial.map (algebraMap (R ⧸ maximalIdeal R) (R' ⧸ maximalIdeal R')) p ∈
        T'.comap e'.toLinearMap := hp.1
    have hp2 : e' (MvPolynomial.map (algebraMap (R ⧸ maximalIdeal R) (R' ⧸ maximalIdeal R'))
        p) ∈ T' := hp1
    rw [AlgEquiv.toLinearMap_apply, hcomm']
    simpa using hp2
  -- the `k'`-span of `σ(T)` has the same rank as `T` (`k → k'` preserves linear independence)
  have hrankσ : ∀ T : Submodule (R ⧸ maximalIdeal R) (AssocGraded (maximalIdeal R)),
      T ≤ AssocGraded.homogeneous (maximalIdeal R) 1 →
      Module.finrank (R' ⧸ maximalIdeal R') (Submodule.span (R' ⧸ maximalIdeal R')
        (σ '' (T : Set (AssocGraded (maximalIdeal R))))) =
        Module.finrank (R ⧸ maximalIdeal R) T := by
    intro T hT
    have := hfin _ hT
    let b := Module.finBasis (R ⧸ maximalIdeal R) T
    have hspanb : Submodule.span (R ⧸ maximalIdeal R)
        (Set.range fun i => (b i : AssocGraded (maximalIdeal R))) = T := by
      rw [show (fun i => (b i : AssocGraded (maximalIdeal R))) = T.subtype ∘ b from rfl,
        Set.range_comp, Submodule.span_image, b.span_eq, Submodule.map_top,
        Submodule.range_subtype]
    have hvli : LinearIndependent (R ⧸ maximalIdeal R)
        fun j => e.symm (b j : AssocGraded (maximalIdeal R)) :=
      (b.linearIndependent.map' _ (Submodule.ker_subtype _)).map' e.symm.toLinearMap
        (LinearMap.ker_eq_bot.mpr e.symm.injective)
    have hwli := linearIndependent_map (k' := R' ⧸ maximalIdeal R') hvli
    have hli : LinearIndependent (R' ⧸ maximalIdeal R')
        fun j => σ (b j : AssocGraded (maximalIdeal R)) := by
      have hfun : (fun j => σ (b j : AssocGraded (maximalIdeal R))) =
          e'.toLinearMap ∘ fun j => MvPolynomial.map
            (algebraMap (R ⧸ maximalIdeal R) (R' ⧸ maximalIdeal R'))
              (e.symm (b j : AssocGraded (maximalIdeal R))) :=
        funext fun j => hcomm' _
      rw [hfun]
      exact hwli.map' e'.toLinearMap (LinearMap.ker_eq_bot.mpr e'.injective)
    have hspan := hspanσ (Set.range fun i => (b i : AssocGraded (maximalIdeal R)))
    rw [hspanb, ← Set.range_comp] at hspan
    rw [hspan, show (σ ∘ fun i => (b i : AssocGraded (maximalIdeal R))) =
        fun j => σ (b j : AssocGraded (maximalIdeal R)) from rfl,
      finrank_span_eq_card hli, Fintype.card_fin]
  -- p. 225, last lines: "Applying Lemma 12 to the homogeneous ideal `I = gr_M(J, R)` in `k[X]`, we
  -- see that for every positive integer `μ̄`, if `T` is the smallest `k`-submodule of `gr¹_M(R)`
  -- such that `gr^μ_M(J, R) = gr^μ_M(R) ∩ (gr_M(J, R) ∩ k[T]) gr_M(R)` for all `μ ≤ μ̄`, then the
  -- `k'`-submodule `T'` of `gr_{M'}(R')` generated by `T` is the smallest one such that
  -- `gr^μ_{M'}(J', R') = gr^μ_{M'}(R') ∩ (gr_{M'}(J', R') ∩ k'[T']) gr_{M'}(R')` for all `μ ≤ μ̄`."
  have hsmallest : ∀ μbar, 0 < μbar →
      ∀ T : Submodule (R ⧸ maximalIdeal R) (AssocGraded (maximalIdeal R)),
      IsTauSubmodule R J T μbar → (∀ S, IsTauSubmodule R J S μbar → T ≤ S) →
        IsTauSubmodule R' (J.map α) (Submodule.span (R' ⧸ maximalIdeal R')
          (σ '' (T : Set (AssocGraded (maximalIdeal R))))) μbar ∧
        ∀ S', IsTauSubmodule R' (J.map α) S' μbar →
          Submodule.span (R' ⧸ maximalIdeal R')
            (σ '' (T : Set (AssocGraded (maximalIdeal R)))) ≤ S' := by
    intro μbar hμbar T hT hTmin
    refine ⟨hfwd _ hμbar T hT, fun S' hS' => ?_⟩
    -- `T'` has the property by the if-part of Lemma 12; if `S'` has the property for `J'`, then by
    -- the only-if part the `k`-points of `S'` have it for `J`, so contain `T` by minimality of `T`
    obtain ⟨S, hSJ, hSS'⟩ := hbwd _ hμbar S' hS'
    rw [Submodule.span_le]
    rintro _ ⟨x, hx, rfl⟩
    exact hSS' x (hTmin S hSJ hx)
  -- the characters `τ^{(a)}` coincide
  have htau : ∀ a, 1 ≤ a → a ≤ t R J → tau R' (J.map α) a = tau R J a := by
    intro a ha hat
    have hat' : a ≤ t R' (J.map α) := by rw [ht]; exact hat
    rcases Nat.eq_zero_or_pos (mu R J a) with h0 | hpos
    · -- `μ^{(a)}(J) = 0` (i.e. `J = R`): both sides are `0` (the empty system has the property)
      have h1 : tau R J a = 0 := Nat.le_zero.mp (tau_le R J (Fin.elim0 : Fin 0 → _)
        (fun i => i.elim0) (by
          rw [h0]
          exact isTauSubmodule_zero J _ (Submodule.span_le.mpr (by
            rintro _ ⟨i, _⟩
            exact i.elim0))))
      have h2 : tau R' (J.map α) a = 0 := Nat.le_zero.mp (tau_le R' (J.map α)
        (Fin.elim0 : Fin 0 → _) (fun i => i.elim0) (by
          rw [hmu a, h0]
          exact isTauSubmodule_zero (J.map α) _ (Submodule.span_le.mpr (by
            rintro _ ⟨i, _⟩
            exact i.elim0))))
      rw [h1, h2]
    · -- `T_a` is the smallest `k`-submodule up to `μ^{(a)}(J)` (Corollary to Lemma 10), hence
      -- `T'_a = k' σ(T_a)` is the smallest `k'`-submodule for `J'` (previous step), i.e. the
      -- submodule `T_a(J')` of the Corollary to Lemma 10 for `J'`; `τ^{(a)}` is its rank
      obtain ⟨hTspec, hrank, -⟩ := tauSubmodule_spec R J a ha hat
      obtain ⟨hT'spec, hrank', -⟩ := tauSubmodule_spec R' (J.map α) a ha hat'
      obtain ⟨hprop', hmin'⟩ := hsmallest _ hpos _ hTspec (fun S hS => tauSubmodule_le R J a S hS)
      have hT'eq : tauSubmodule R' (J.map α) a = Submodule.span (R' ⧸ maximalIdeal R')
          (σ '' (tauSubmodule R J a : Set (AssocGraded (maximalIdeal R)))) :=
        le_antisymm (tauSubmodule_le R' (J.map α) a _ (by rw [hmu a]; exact hprop'))
          (hmin' _ (by rw [← hmu a]; exact hT'spec))
      rw [← hrank', hT'eq, hrankσ _ hTspec.1, hrank]
  refine ⟨ht, htau, fun h z hz b hb hbt' => ?_⟩
  -- regular systems of `τ`-parameters are carried to such systems
  have hbt : b ≤ t R J := by rw [← ht]; exact hbt'
  have hτb := htau b hb hbt
  have hSb := hz b hb hbt
  have key : IsTauSubmodule R' (J.map α) (Submodule.span (R' ⧸ maximalIdeal R')
      (σ '' (Submodule.span (R ⧸ maximalIdeal R) (Set.range
        fun i : {i : Fin (tau R J (t R J)) // (i : ℕ) < tau R J b} =>
          AssocGraded.mk (maximalIdeal R) 1 (z i.1 : R)
            (by rw [pow_one]; exact (z i.1).2)) : Set (AssocGraded (maximalIdeal R)))))
      (mu R' (J.map α) b) := by
    rw [hmu b]
    rcases Nat.eq_zero_or_pos (mu R J b) with h0 | hpos
    · rw [h0]
      refine isTauSubmodule_zero _ _ (Submodule.span_le.mpr ?_)
      rintro _ ⟨x, hx, rfl⟩
      exact hσ1 _ (hSb.1 hx)
    · exact hfwd _ hpos _ hSb
  rw [hspanσ] at key
  have hfun : (fun i : {i : Fin (tau R' (J.map α) (t R' (J.map α))) //
      (i : ℕ) < tau R' (J.map α) b} => AssocGraded.mk (maximalIdeal R') 1
        (α (z (Fin.cast h i.1)))
        (by rw [pow_one]; exact map_nonunit α _ (z (Fin.cast h i.1)).2)) =
      fun i => σ ((fun j : Fin (tau R J (t R J)) => AssocGraded.mk (maximalIdeal R) 1 (z j : R)
        (by rw [pow_one]; exact (z j).2)) (Fin.cast h i.1)) :=
    funext fun i => (hσ 1 _ _ _).symm
  show IsTauSubmodule R' (J.map α) (Submodule.span (R' ⧸ maximalIdeal R')
    (Set.range fun i : {i : Fin (tau R' (J.map α) (t R' (J.map α))) //
      (i : ℕ) < tau R' (J.map α) b} => AssocGraded.mk (maximalIdeal R') 1
        (α (z (Fin.cast h i.1)))
        (by rw [pow_one]; exact map_nonunit α _ (z (Fin.cast h i.1)).2))) (mu R' (J.map α) b)
  rw [hfun, range_subtype_cast h hτb (fun j : Fin (tau R J (t R J)) =>
    AssocGraded.mk (maximalIdeal R) 1 (z j : R) (by rw [pow_one]; exact (z j).2)) σ]
  exact key

/-- Lemma 13, p. 225: "Let `α : R → R'` be a local homomorphism of regular local rings such that
`α` transforms a regular system of parameters of `R` into such a system of `R'`.  Assume that
the residue field of `R'` is separable over that of `R`.  Let `J` be an ideal in `R` and `J'`
the ideal in `R'` generated by `α(J)`.  Then we have `t(J') = t(J)` and `τ^{(i)}(J') = τ^{(i)}(J)`
for all `i`, and a regular system of `τ`-parameters of `R` for `J` is transformed into such a
system of `R'` for `J'`."

The third assertion is stated for the transported system `i ↦ α(z_i)` (a system of elements of
`M'` since `α` is local), whose index type `Fin (τ^{(t)}(J'))` is identified with
`Fin (τ^{(t)}(J))` through the equality `h` provided by the first two assertions; `τ^{(i)}`
is only defined for `1 ≤ i ≤ t(J)`, to which the second assertion is restricted (paper
misprint: the paper prints "for all `i ≥ 0`").

Proof as printed (p. 225, last lines, and p. 226): `gr_M(R) = k[X]` and `gr_{M'}(R') = k'[X]` are
identified through the regular system of parameters (`e`, `e'`); `σ = ᾱ` induces `k → k'` and
fixes the `X_j` (`hcomm`); by Lemma 2, §1 (`hσJ`), `σ(gr_M(J, R))` generates `gr_{M'}(J', R')`
(`hI'`).  Lemma 12 is then applied to `I = gr_M(J, R)`: its if-part gives that the `k'`-span of
`σ(T)` has the property for `J'` whenever `T` has it for `J` (`hfwd`), its only-if part that the
`k`-points `T = {x | σ x ∈ T'}` of a submodule `T'` having it for `J'` have it for `J` (`hbwd`).
These give the displayed claim of p. 226 (`hsmallest`): "if `T` is the smallest `k`-submodule
of `gr¹_M(R)` such that [the property] for all `μ ≤ μ̄`, then the `k'`-submodule `T'` of
`gr_{M'}(R')` generated by `T` is the smallest one such that [the property for `J'`] for all
`μ ≤ μ̄`": `T'` has the property by the if-part, and if `S'` has it, the `k`-points of `S'` have
it for `J`, hence contain the smallest `T`, so `S' ⊇ k'σ(T) = T'`.  For `T = T_a` (Corollary
to Lemma 10) and `μ̄ = μ^{(a)}(J) = μ^{(a)}(J')` this says `T_a(J') = k'σ(T_a(J))`, and
`τ^{(a)}(J') = rank T_a(J') = rank T_a(J) = τ^{(a)}(J)` since the extension `k → k'` preserves
linear independence (`hrankσ`).  "The assertions of Lemma 13 follow immediately": the transport of
a regular system of `τ`-parameters uses the if-part (`hfwd`) for each `b ≤ t` and the equality
`τ^{(b)}(J') = τ^{(b)}(J)`.
Gaps in the paper filled: `t(J') = t(J)` and `μ*(J') = μ*(J)` via `ν*(J') = ν*(J)`
(`nuI_map_eq_of_mapsRSOP`, Corollary to Lemma 2); the case `μ^{(a)}(J) = 0` (i.e. `J = R`), not
covered by "every positive integer `μ̄`" (both `τ`'s are `0`); the rank statement for `k'σ(T)`. -/
@[blueprint "lem:III.13"
  (statement := /-- Let $\alpha\colon R\to R'$ be a local homomorphism of regular local rings
    such that $\alpha$ transforms a regular system of parameters of $R$ into such a system of
    $R'$ (\cref{def:III.rsop-map}). Assume that the residue field of $R'$ is separable over
    that of $R$ (\cref{def:III.2-residually}). Let $J$ be an ideal in $R$ and $J'$ the ideal
    in $R'$ generated by $\alpha(J)$. Then we have $t(J')=t(J)$ and
    $\tau^{(i)}(J')=\tau^{(i)}(J)$ for all $i$ ($1\le i\le t(J)$), and a regular system of
    $\tau$-parameters of $R$ for $J$ is transformed into such a system of $R'$ for $J'$
    (\cref{def:III.7}). (Lemma 13, p.~225.)

    \textbf{Paper misprint.} The paper prints ``$\tau^{(i)}(J')=\tau^{(i)}(J)$ for all
    $i\ge0$''; since $\tau^{(i)}$ is defined only for $1\le i\le t(J)$ (\cref{def:III.6}), what
    is meant (and stated here) is $1\le i\le t(J)=t(J')$. -/)
  (proof := /-- Let $(x_1,\dots,x_n)$ be a regular system of parameters of $R$. Let $M$
    (resp.\ $M'$) be the maximal ideal of $R$ (resp.\ $R'$). Then $\operatorname{gr}_M(R)$ can
    be identified with a polynomial ring $k[X]=k[X_1,\dots,X_n]$ with $k=R/M$, in such a way
    that $X_j$ corresponds to the class of $x_j$ in $\operatorname{gr}^1_M(R)$. Accordingly, we
    identify $\operatorname{gr}_{M'}(R')$ with a polynomial ring $k'[X]=k'[X_1,\dots,X_n]$ with
    $k'=R'/M'$, in such a way that $X_j$ corresponds to the class of $\alpha(x_j)$ in
    $\operatorname{gr}^1_{M'}(R')$. The canonical homomorphism
    $\bar\alpha\colon\operatorname{gr}_M(R)\to\operatorname{gr}_{M'}(R')$, induced by $\alpha$,
    induces the canonical homomorphism of $k$ into $k'$ and leaves the $X_j$ fixed. By
    Lemma~2 of \S1 (\cref{lem:III.2}), we have that $\bar\alpha(\operatorname{gr}_M(J,R))$ generates
    $\operatorname{gr}_{M'}(J',R')$. Applying \cref{lem:III.12} to the homogeneous ideal
    $I=\operatorname{gr}_M(J,R)$ in $k[X]$, we see that for every positive integer $\bar\mu$,
    if $T$ is the smallest $k$-submodule of $\operatorname{gr}^1_M(R)$ such that
    $\operatorname{gr}^\mu_M(J,R)=\operatorname{gr}^\mu_M(R)\cap(\operatorname{gr}_M(J,R)\cap
    k[T])\operatorname{gr}_M(R)$ for all $\mu\le\bar\mu$, then the $k'$-submodule $T'$ of
    $\operatorname{gr}_{M'}(R')$ generated by $T$ [i.e.\ by $\bar\alpha(T)$] is the smallest one
    such that
    $\operatorname{gr}^\mu_{M'}(J',R')=\operatorname{gr}^\mu_{M'}(R')\cap
    (\operatorname{gr}_{M'}(J',R')\cap k'[T'])\operatorname{gr}_{M'}(R')$ for all
    $\mu\le\bar\mu$. The assertions of Lemma~13 follow immediately (\cref{cor:III.lem10}).

    (Lean: \texttt{hfwd} is the if-part and \texttt{hbwd} the only-if part of
    \cref{lem:III.12} for $I=\operatorname{gr}_M(J,R)$; \texttt{hsmallest} is the displayed
    claim just quoted, proved as the paper indicates from \cref{lem:III.12} and the minimality of
    $T$ (\cref{cor:III.lem10}); then $T_a(J')=k'\bar\alpha(T_a(J))$ and
    $\tau^{(a)}(J')=\operatorname{rank}T_a(J')=\operatorname{rank}T_a(J)=\tau^{(a)}(J)$.
    The transport of a regular system of $\tau$-parameters uses the if-part of
    \cref{lem:III.12} for each $b\le t$.)

    \textbf{Gap in the paper filled.} ``Follow immediately'' is spelled out: $t(J')=t(J)$ and
    $\mu^*(J')=\mu^*(J)$ come from $\nu^*(J')=\nu^*(J)$ (Corollary to Lemma~2), and the case
    $\mu^{(a)}(J)=0$ (i.e.\ $J=R$), not covered by ``every positive integer $\bar\mu$'', is
    treated directly ($\tau=0$ on both sides), and the rank equality
    $\operatorname{rank}(k'\bar\alpha(T))=\operatorname{rank}T$ is proved (the extension
    $k\to k'$ preserves linear independence). -/)
  (latexEnv := "lemma")]
theorem tauStar_map [Hironaka.Cited.IsSeparableFieldExtensionIff.{u}] (α : R →+* R') [IsLocalHom α] (hα : RingHom.MapsRSOP α)
    (hsep : RingHom.IsResiduallySeparable α) (J : Ideal R) :
    t R' (J.map α) = t R J ∧
    (∀ i, 1 ≤ i → i ≤ t R J → tau R' (J.map α) i = tau R J i) ∧
    ∀ (h : tau R' (J.map α) (t R' (J.map α)) = tau R J (t R J))
      (z : Fin (tau R J (t R J)) → maximalIdeal R),
      IsRegularSystemOfTauParameters R J (t R J) z →
      IsRegularSystemOfTauParameters R' (J.map α) (t R' (J.map α))
        (fun i => ⟨α (z (Fin.cast h i)), map_nonunit α _ (z (Fin.cast h i)).2⟩) := by
  classical
  let _ := α.toAlgebra
  have hflat : Module.Flat R R' := RingHom.MapsRSOP.flat hα
  obtain ⟨s, hs, hs', hinj⟩ := hα
  have hM : (maximalIdeal R).map α = maximalIdeal R' := by
    have h := hs'.1
    rw [Finset.coe_image] at h
    rw [← hs.1, Ideal.map_span, h]
  have hjac : (maximalIdeal R).map (algebraMap R R') ≤ Ring.jacobson R' := by
    rw [ringJacobson_eq_maximalIdeal]
    exact hM.le
  exact tauStar_map_of_gradedMap α s hs hs' hinj hsep J _ hM (AssocGraded.map α (maximalIdeal R))
    (fun n a ha _ => AssocGraded.map_mk α _ n a ha)
    (map_grIdeal_eq_grIdeal_map_of_flat R R' (maximalIdeal R) J hjac)

end Lemma13

end Hironaka
