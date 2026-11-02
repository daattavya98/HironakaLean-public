/-
Copyright (c) 2026 Daattavya Aggarwal, Minhyong Kim, Oisin Kim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daattavya Aggarwal, Minhyong Kim, Oisin Kim
-/
module

public import Mathlib.Algebra.CharP.Algebra
public import Mathlib.Algebra.Field.ULift
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.AlgebraicGeometry.IdealSheaf.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.Coalgebra.IsFrobenius
public import Mathlib.RingTheory.DualNumber
public import Mathlib.RingTheory.Finiteness.Prod
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.HopfAlgebra.Basic
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Architect
public import Hironaka.Ch0.NormalFlatness
public import Hironaka.Ch2.Flatness
public import Hironaka.Ch2.GradedIdeal
public import Hironaka.Compat.BlowupBaseChange
public import Hironaka.Compat.ComponentStalk
public import Hironaka.Compat.SubschemeStalk

/-!
# Ch. 0 §4 (I), (II) (p. 136): normal flatness and equimultiplicity

Hironaka states (I) and (II) in Ch. 0 and refers for their proofs to Ch. II (footnotes 18,
19): Proposition 1 of §1 and its Corollaries 3, 4, Corollary 2 of Theorem 2 of §2, and
Theorem 1 of §1 with its corollary.

Formalization note: this module only fixes the position of the Ch. 0 statements after the
Ch. II results on which their proofs rest (`Hironaka/Ch2/Flatness.lean`,
`Hironaka/Ch2/GradedIdeal.lean`); the statements are those of Ch. 0 and the arguments are
the cited ones of Ch. II.  The hypothesis `[IsAlgebraicScheme X]` is explicit, and (I) is false
for non-noetherian `X` (see the docstring of `equimultiple_of_normallyFlat`).

Deviation from the paper (statement modified): in Ch. 0 §4 `X` is "either an algebraic
B-scheme or an analytic K-space", where an algebraic B-scheme is of finite type over an
arbitrary noetherian ring `B` (p. 118).  Here `X` is an algebraic scheme in the sense of Ch. I
(of finite type over some `S ∈ 𝔅`), the setting of the Ch. II proofs cited in footnotes 18, 19,
and the analytic case is not formalized.
-/

@[expose] public section

open AlgebraicGeometry IsLocalRing Filter Polynomial

namespace Hironaka

universe u

namespace Subscheme

variable {X : Scheme.{u}}

/-- Ch. 0 §4 (I), p. 136: "Let D be a non-singular algebraic subscheme of X. If X is normally
flat along D, then X is equi-multiple along D. (Moreover, if D contains a simple point of X then
every point of D is a simple point of X.)"  Footnote 18 refers for the proof to Prop. 1 of §1
and Th. 2 of §2 of Ch. II "and also their corollaries".  The corollaries in question (Cor. 3 and
Cor. 4 of Prop. 1) assume `D` *irreducible*, and the statement is false without that
hypothesis: two closed points of different multiplicities form a non-singular subscheme along
which `X` is normally flat (every local ring is normally flat along its maximal ideal).  We
therefore state (I) with the irreducibility hypothesis under which the paper proves it.

Correction of the paper (statement corrected): "D irreducible" is added (for non-singular `D`
equivalently: connected); the printed statement, including its "moreover" clause, fails for
`X = Spec k[x, y]/(xy)` and `D` the two closed points `(0, 0)`, `(1, 0)`.

Deviation from the paper (statement modified): `X` is an algebraic scheme in the sense of
Ch. I rather than an algebraic B-scheme over an arbitrary noetherian ring (or an analytic
space).  Some noetherian hypothesis is needed: for
`A = ℚ[t, y₁, y₂, …]/(yᵢyⱼ)` and `D = V(y) ≅ Spec ℚ[t]`, `X = Spec A` is normally flat along
`D` (`P² = 0` and `P/P²` is free), but the Samuel multiplicity (as defined here, with
`finrank = 0` for infinite-dimensional spaces) is `1` at the generic point of `D` and `0` at
the closed point `(t, y)`, where `mⁿ/mⁿ⁺¹` is not finite-dimensional. -/
@[blueprint "prop:0.4-I"
  (statement := /-- Let $X$ be an algebraic scheme and $D$ a non-singular \emph{irreducible}
    subscheme of $X$. If $X$ is normally flat along $D$, then $X$ is equi-multiple along $D$
    (\cref{def:equimultiple-along}). Moreover, if $D$ contains a simple point of $X$ then every
    point of $D$ is a simple point of $X$. (Ch.~0 \S4 (I), p.~136.)
    \textbf{Correction of the paper (statement).} The paper omits ``irreducible'' (for
    non-singular $D$ equivalently: connected); the results it cites for the proof,
    Corollaries~3 and~4 of Proposition~1 of Ch.~II \S1, assume it, and the statement is false
    without it: for $X=\operatorname{Spec}k[x,y]/(xy)$ and $D$ the two closed points $(0,0)$,
    $(1,0)$, $X$ is normally flat along $D$ but has multiplicities $2$ and $1$ there.
    \textbf{Deviation from the paper (statement modified).} $X$ is an algebraic scheme in the
    sense of Ch.~I (base ring in $\mathfrak B$), whereas Ch.~0 \S4 allows an algebraic
    $B$-scheme over any noetherian ring $B$ or an analytic space. -/)
  (proof := /-- \cref{cor:II.1-prop1-3} and \cref{cor:II.1-prop1-4} (footnote 18). -/)
  (latexEnv := "proposition")]
theorem equimultiple_of_normallyFlat [Hironaka.Cited.IsHironakaBaseIsClosedSingularLocus.{u}] [Hironaka.Cited.ExistsHilbertSamuelPoly.{u}] [IsAlgebraicScheme X] (D : Subscheme X)
    (hD : D.IsNonsingular) (hirr : D.IsIrreducible) (h : D.IsNormallyFlatAlong) :
    D.IsEquimultipleAlong ∧ ((∃ x ∈ D.pts, X.IsSimpleAt x) → ∀ x ∈ D.pts, X.IsSimpleAt x) :=
  ⟨isEquimultipleAlong_of_isNormallyFlatAlong D hD hirr h,
    fun hx => forall_isSimpleAt_of_isNormallyFlatAlong D hD hirr h hx⟩

/-- Ch. 0 §4 (I), p. 136, AS PRINTED, without the hypothesis "`D` irreducible": "Let `D` be a
non-singular algebraic subscheme of `X`. If `X` is normally flat along `D`, then `X` is
equi-multiple along `D`.  (Moreover, if `D` contains a simple point of `X` then every point of
`D` is a simple point of `X`.)"

Statement as printed (false); see the corrected statement `equimultiple_of_normallyFlat`.  It
fails for the reduced scheme on the two points of
`Spec (ℚ × ℚ[ε])` (`not_equimultipleOfNormallyFlatAsPrinted`); another example is the node
`Spec k[x, y]/(xy)` together with a smooth point, which needs a one-dimensional Hilbert–Samuel
computation, while the example below has the same two features (two points of different
multiplicity along which `X` is normally flat) and is zero-dimensional. -/
@[blueprint "prop:0.4-I-as-printed"
  (statement := /-- Let $X$ be an algebraic scheme and $D$ a non-singular subscheme of $X$. If
    $X$ is normally flat along $D$, then $X$ is equi-multiple along $D$. Moreover, if $D$
    contains a simple point of $X$ then every point of $D$ is a simple point of $X$.
    (Ch.~0 \S4 (I), p.~136, without the hypothesis ``$D$ irreducible''.)
    \textbf{Statement as printed (false); see the corrected statement \cref{prop:0.4-I}.} -/)
  (latexEnv := "proposition")]
def EquimultipleOfNormallyFlatAsPrinted : Prop :=
  ∀ (X : Scheme.{u}) [IsAlgebraicScheme X] (D : Subscheme X), D.IsNonsingular →
    D.IsNormallyFlatAlong →
    D.IsEquimultipleAlong ∧ ((∃ x ∈ D.pts, X.IsSimpleAt x) → ∀ x ∈ D.pts, X.IsSimpleAt x)

/-- Ch. 0 §4 (I), p. 136, continued: "The converse is true if X is imbedded in a non-singular
algebraic B-scheme Y such that the sheaf of ideals of X on Y is everywhere locally principal;
but not in general."  This is Corollary 2 of Theorem 2, Ch. II §2 (footnote 18), where the
subscheme is moreover assumed irreducible.

Deviation from the paper (statement modified): the hypotheses are those of Ch. II Cor. 2 of
Th. 2, which are stronger than those of the Ch. 0 sentence: `W` is assumed irreducible, and the
ideal of `V` is assumed generated locally by a non-zero-divisor, whereas p. 136 only asks that
it be "everywhere locally principal" and that `D` be non-singular.  Both missing cases are true
(normal flatness is local, so one may pass to the connected components of `W`; and where the
ideal of `V` is zero, `V` is regular); the printed statement is
`Subscheme.isNormallyFlatAlong_of_isEquimultipleAlong_of_isLocallyPrincipal`
(`Hironaka/Compat/LocallyPrincipalConverse.lean`, downstream of this file).  The ambient scheme is an
algebraic scheme in the sense of Ch. I.  Not formalized:
"but not in general". -/
@[blueprint "prop:0.4-I-converse"
  (statement := /-- Let $V$ be a subscheme of a non-singular algebraic scheme $X$ whose sheaf of
    ideals on $X$ is invertible, and $W$ a non-singular irreducible subscheme of $V$. If $V$ is
    equi-multiple along $W$ then $V$ is normally flat along $W$. (Ch.~0 \S4 (I), p.~136,
    ``the converse''.)
    \textbf{Deviation from the paper (statement modified).} The paper asks only that the sheaf
    of ideals of $V$ be ``everywhere locally principal'' and that $W$ be non-singular; Lean takes
    the stronger hypotheses of Ch.~II Cor.~2 of Th.~2 ($W$ irreducible, the ideal locally
    generated by a non-zero-divisor), so it proves a weaker statement. The missing cases are
    true; the printed statement is \cref{prop:0.4-I-converse-printed}.
    \textbf{Not formalized.} The paper's addition ``but not in general'' (the converse fails
    without the hypersurface hypothesis). -/)
  (proof := /-- \cref{cor:II.2-thm2-2} (footnote 18). -/)
  (latexEnv := "proposition")]
theorem isNormallyFlatAlong_of_isEquimultipleAlong [IsAlgebraicScheme X] (hX : X.IsNonsingular)
    (V W : Subscheme X) (hV : V.IsInvertibleIdeal) (hW : W.IsNonsingular)
    (hirr : W.IsIrreducible) (hWV : W.IsContainedIn V)
    (h : (totalTransform V.ι W).IsEquimultipleAlong) :
    V.IsNormallyFlatAlong' W :=
  (isNormallyFlatAlong'_iff_isEquimultipleAlong hX V W hV hW hirr hWV).mpr h

/-- Ch. 0 §4 (II), p. 136: "Let D be an algebraic subscheme of X. Then there exists an algebraic
subscheme S of D such that for a point x of D, X is normally flat along D at the point x if
and only if x is not a point of S."  Footnote 19: Theorem 1 of §1, Ch. II, and its corollary. -/
@[blueprint "prop:0.4-II"
  (statement := /-- Let $D$ be a subscheme of the algebraic scheme $X$. There exists a
    subscheme $S$ of $D$ such that for a point $x$ of $D$, $X$ is normally flat along $D$ at
    $x$ if and only if $x$ is not a point of $S$. (Ch.~0 \S4 (II), p.~136.)
    \textbf{Deviation from the paper (statement modified).} $X$ is an algebraic scheme in the
    sense of Ch.~I, whereas Ch.~0 \S4 allows an algebraic $B$-scheme over any noetherian ring
    $B$ or an analytic space. -/)
  (proof := /-- \cref{thm:II.1-1} and \cref{cor:II.1-thm1} (footnote 19): the set of points of
    $D$ at which $X$ is not normally flat along $D$ is closed; take $S$ to be the reduced
    subscheme on it. -/)
  (latexEnv := "proposition")]
theorem exists_nonNormallyFlatLocus [IsAlgebraicScheme X] (D : Subscheme X) :
    ∃ S : Subscheme X, S.IsContainedIn D ∧
      ∀ x ∈ D.pts, (D.IsNormallyFlatAlongAt x ↔ x ∉ S.pts) := by
  -- Theorem 1 of Ch. II §1 on affine charts: the normally flat locus is open in `D`
  obtain ⟨U₀, hU₀, hiff⟩ := exists_isOpen_isNormallyFlatAlongAt D
  -- the reduced subscheme on the closed set `D ∖ U₀`
  let Z : TopologicalSpace.Closeds X :=
    ⟨D.pts ∩ U₀ᶜ, D.support.isClosed.inter hU₀.isClosed_compl⟩
  have hZ : (ofClosed Z).pts = D.pts ∩ U₀ᶜ :=
    Scheme.IdealSheafData.coe_support_vanishingIdeal Z
  refine ⟨ofClosed Z, fun U => ?_, fun x hx => ?_⟩
  · have hle : D ≤ ofClosed Z :=
      Scheme.IdealSheafData.le_support_iff_le_vanishingIdeal.mp fun y hy => hy.1
    exact hle U
  · rw [hZ, ← hiff x hx]
    exact ⟨fun h h' => h'.2 h, fun h => by_contra fun h' => h ⟨hx, h'⟩⟩

end Subscheme

namespace Subscheme

/-- A reduced subscheme has maximal ideal as stalk ideal at points of `X` with square-zero maximal
ideal. -/
theorem stalkIdeal_eq_maximalIdeal_of_isReduced_of_sq_eq_bot {X : Scheme.{u}} (D : Subscheme X)
    (hD : D.IsReduced) {x : X} (hx : x ∈ D.pts)
    (h2 : maximalIdeal (X.presheaf.stalk x) ^ 2 = ⊥) :
    D.stalkIdeal x = maximalIdeal (X.presheaf.stalk x) := by
  refine le_antisymm (stalkIdeal_le_maximalIdeal_of_mem_pts D hx) fun a ha => ?_
  refine (isRadical_stalkIdeal_of_isReduced hD x) ⟨2, ?_⟩
  have : a ^ 2 ∈ maximalIdeal (X.presheaf.stalk x) ^ 2 := Ideal.pow_mem_pow ha 2
  rw [h2, Ideal.mem_bot] at this
  rw [this]; exact Ideal.zero_mem _

end Subscheme

section MultiplicityOfSquareZero
variable {R : Type u} [CommRing R] [IsLocalRing R]

omit [IsLocalRing R] in
theorem grPiece_subsingleton_of_pow_eq_bot {I : Ideal R} {p : ℕ} (h : I ^ p = ⊥) :
    Subsingleton (GrPiece I p) := by
  refine ⟨fun a b => ?_⟩
  induction a using Submodule.Quotient.induction_on with
  | H x =>
  induction b using Submodule.Quotient.induction_on with
  | H y =>
    have hx : (x : R) = 0 := Ideal.mem_bot.mp (h ▸ x.2)
    have hy : (y : R) = 0 := Ideal.mem_bot.mp (h ▸ y.2)
    have : x = y := Subtype.ext (hx.trans hy.symm)
    rw [this]

theorem finrank_grPiece_maximalIdeal_zero :
    Module.finrank (R ⧸ maximalIdeal R) (GrPiece (maximalIdeal R) 0) = 1 := by
  let _ : Field (R ⧸ maximalIdeal R) := Ideal.Quotient.field _
  let v : GrPiece (maximalIdeal R) 0 := Submodule.Quotient.mk ⟨1, by simp⟩
  have hv : v ≠ 0 := by
    intro h
    rw [Submodule.Quotient.mk_eq_zero, Submodule.mem_comap] at h
    simp at h
  refine (finrank_eq_one_iff_of_nonzero' v hv).mpr fun w => ?_
  induction w using Submodule.Quotient.induction_on with
  | H x =>
    refine ⟨Ideal.Quotient.mk _ (x : R), ?_⟩
    change (x : R) • v = _
    rw [← Submodule.Quotient.mk_smul]
    congr 1
    apply Subtype.ext
    simp

theorem finrank_grPiece_maximalIdeal_one_of_eq_span (e : R) (he : e ≠ 0)
    (hm : maximalIdeal R = Ideal.span {e}) (h2 : maximalIdeal R ^ 2 = ⊥) :
    Module.finrank (R ⧸ maximalIdeal R) (GrPiece (maximalIdeal R) 1) = 1 := by
  let _ : Field (R ⧸ maximalIdeal R) := Ideal.Quotient.field _
  have heM : e ∈ maximalIdeal R ^ 1 := by rw [pow_one, hm]; exact Ideal.mem_span_singleton_self e
  let v : GrPiece (maximalIdeal R) 1 := Submodule.Quotient.mk ⟨e, heM⟩
  have hv : v ≠ 0 := by
    intro h
    rw [Submodule.Quotient.mk_eq_zero, Submodule.mem_comap] at h
    have h' : e ∈ maximalIdeal R ^ (1 + 1) := h
    have h2' : maximalIdeal R ^ (1 + 1) = ⊥ := h2
    rw [h2'] at h'
    exact he (Ideal.mem_bot.mp h')
  refine (finrank_eq_one_iff_of_nonzero' v hv).mpr fun w => ?_
  induction w using Submodule.Quotient.induction_on with
  | H x =>
    have hx : (x : R) ∈ Ideal.span {e} := by rw [← hm]; simpa using x.2
    obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.mp hx
    refine ⟨Ideal.Quotient.mk _ r, ?_⟩
    change r • v = _
    change r • (Submodule.Quotient.mk _ : GrPiece (maximalIdeal R) 1) = _
    rw [← Submodule.Quotient.mk_smul]
    congr 1
    apply Subtype.ext
    simpa [smul_eq_mul] using hr

theorem dimNat_eq_zero_of_maximalIdeal_pow_two_eq_bot (h2 : maximalIdeal R ^ 2 = ⊥) :
    dimNat R = 0 := by
  have hK : Ring.KrullDimLE 0 R := by
    rw [Ring.krullDimLE_zero_iff]
    intro P hP
    have hle : maximalIdeal R ≤ P := fun a ha => by
      refine hP.mem_of_pow_mem 2 ?_
      have : a ^ 2 ∈ maximalIdeal R ^ 2 := Ideal.pow_mem_pow ha 2
      rw [h2] at this
      rw [Ideal.mem_bot.mp this]; exact P.zero_mem
    have : P = maximalIdeal R :=
      le_antisymm (le_maximalIdeal hP.ne_top) hle
    rw [this]; exact maximalIdeal.isMaximal R
  have h0 : ringKrullDim R = 0 :=
    le_antisymm (by simpa using (Ring.krullDimLE_iff.mp hK)) (ringKrullDim_nonneg_of_nontrivial)
  simp only [dimNat, h0]
  rfl

theorem hilbertSamuel_succ_of_maximalIdeal_pow_two_eq_bot (h2 : maximalIdeal R ^ 2 = ⊥)
    (n : ℕ) :
    hilbertSamuel R (n + 1) =
      1 + Module.finrank (R ⧸ maximalIdeal R) (GrPiece (maximalIdeal R) 1) := by
  have hF : ∀ i, 2 ≤ i →
      Module.finrank (R ⧸ maximalIdeal R) (GrPiece (maximalIdeal R) i) = 0 := by
    intro i hi
    have : maximalIdeal R ^ i = ⊥ := by
      obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hi
      rw [pow_add, h2, Ideal.bot_mul]
    have := grPiece_subsingleton_of_pow_eq_bot this
    exact Module.finrank_zero_of_subsingleton
  induction n with
  | zero =>
    unfold hilbertSamuel
    rw [Finset.sum_range_succ, Finset.sum_range_one, finrank_grPiece_maximalIdeal_zero]
  | succ n ih =>
    unfold hilbertSamuel at ih ⊢
    rw [Finset.sum_range_succ, ih, hF (n + 1 + 1) (by omega), add_zero]

theorem samuelMultiplicity_eq_of_maximalIdeal_pow_two_eq_bot (h2 : maximalIdeal R ^ 2 = ⊥) :
    samuelMultiplicity R =
      1 + Module.finrank (R ⧸ maximalIdeal R) (GrPiece (maximalIdeal R) 1) := by
  set c := 1 + Module.finrank (R ⧸ maximalIdeal R) (GrPiece (maximalIdeal R) 1) with hc
  have hex : ∃ p : ℚ[X], ∀ᶠ n : ℕ in atTop,
      p.eval (n : ℚ) = (hilbertSamuel R n : ℚ) := by
    refine ⟨C (c : ℚ), Filter.eventually_atTop.mpr ⟨1, fun n hn => ?_⟩⟩
    obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hn
    rw [add_comm 1 m, hilbertSamuel_succ_of_maximalIdeal_pow_two_eq_bot h2 m]
    simp [hc]
  have hp : hilbertSamuelPoly R = C (c : ℚ) := by
    unfold hilbertSamuelPoly
    split_ifs
    refine hilbertSamuelPoly_unique R (Classical.choose_spec hex) ?_
    refine Filter.eventually_atTop.mpr ⟨1, fun n hn => ?_⟩
    obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hn
    rw [add_comm 1 m, hilbertSamuel_succ_of_maximalIdeal_pow_two_eq_bot h2 m]
    simp [hc]
  unfold samuelMultiplicity
  rw [dimNat_eq_zero_of_maximalIdeal_pow_two_eq_bot h2, hp]
  simp
end MultiplicityOfSquareZero

section DualNumberAndLocalization
variable {k : Type u} [Field k]

theorem eq_inl_snd_mul_eps_of_fst_eq_zero (b : DualNumber k) (h : b.fst = 0) :
    b = TrivSqZeroExt.inl b.snd * DualNumber.eps := by
  apply TrivSqZeroExt.ext
  · simp only [DualNumber.eps, TrivSqZeroExt.fst_mul, TrivSqZeroExt.fst_inl, TrivSqZeroExt.fst_inr,
      mul_zero, h]
  · simp only [DualNumber.eps, TrivSqZeroExt.snd_mul, TrivSqZeroExt.fst_inl, TrivSqZeroExt.snd_inl,
      TrivSqZeroExt.snd_inr, TrivSqZeroExt.fst_inr, smul_eq_mul, mul_one, MulOpposite.op_zero,
      zero_smul, add_zero]

theorem fst_eq_zero_of_mul_eps_eq_zero (b : DualNumber k) (h : b * DualNumber.eps = 0) :
    b.fst = 0 := by
  have := congrArg TrivSqZeroExt.snd h
  simpa only [DualNumber.eps, TrivSqZeroExt.snd_mul, TrivSqZeroExt.fst_inr, TrivSqZeroExt.snd_inr,
    TrivSqZeroExt.snd_zero, MulOpposite.op_zero, zero_smul, add_zero, smul_eq_mul,
    mul_one] using this

theorem isUnit_of_fst_ne_zero (b : DualNumber k) (h : b.fst ≠ 0) : IsUnit b :=
  TrivSqZeroExt.isUnit_iff_isUnit_fst.mpr (isUnit_iff_ne_zero.mpr h)

/-- case A: the prime contains `(0,1)`: the local ring is a field. -/
theorem maximalIdeal_localization_eq_bot_of_mem (P : Ideal (k × DualNumber k)) [P.IsPrime]
    (h2 : ((0 : k), (1 : DualNumber k)) ∈ P) :
    maximalIdeal (Localization.AtPrime P) = ⊥ := by
  have h1 : ((1 : k), (0 : DualNumber k)) ∉ P := by
    intro h
    have := P.add_mem h h2
    simp only [Prod.mk_add_mk, add_zero, zero_add] at this
    exact (Ideal.IsPrime.ne_top ‹P.IsPrime›) (P.eq_top_of_isUnit_mem this isUnit_one)
  rw [← IsLocalization.AtPrime.map_eq_maximalIdeal P (Localization.AtPrime P)]
  rw [eq_bot_iff, Ideal.map_le_iff_le_comap]
  rintro ⟨a, b⟩ hx
  rw [Ideal.mem_comap, Ideal.mem_bot]
  have hb : ((0 : k), b) ∈ P := by
    have : ((0 : k), b) = ((0 : k), b) * ((0 : k), (1 : DualNumber k)) := by simp
    rw [this]; exact P.mul_mem_left _ h2
  have ha : a = 0 := by
    by_contra ha
    have hab : (a, (0 : DualNumber k)) ∈ P := by
      have := P.sub_mem hx hb
      simpa using this
    have : ((1 : k), (0 : DualNumber k)) ∈ P := by
      have := P.mul_mem_left (a⁻¹, (0 : DualNumber k)) hab
      simpa [ha] using this
    exact h1 this
  subst ha
  rw [IsLocalization.map_eq_zero_iff P.primeCompl]
  exact ⟨⟨((1 : k), (0 : DualNumber k)), h1⟩, by simp⟩

/-- case B: the prime does not contain `(0,1)`: the local ring has maximal ideal generated by a
nonzero element of square zero. -/
theorem exists_maximalIdeal_localization_eq_span_of_notMem (P : Ideal (k × DualNumber k))
    [hP : P.IsPrime]
    (h2 : ((0 : k), (1 : DualNumber k)) ∉ P) :
    ∃ e : Localization.AtPrime P, e ≠ 0 ∧
      maximalIdeal (Localization.AtPrime P) = Ideal.span {e} ∧
      maximalIdeal (Localization.AtPrime P) ^ 2 = ⊥ := by
  have h1 : ((1 : k), (0 : DualNumber k)) ∈ P := by
    have : ((1 : k), (0 : DualNumber k)) * ((0 : k), (1 : DualNumber k)) ∈ P := by
      have h0 : ((1 : k), (0 : DualNumber k)) * ((0 : k), (1 : DualNumber k)) = 0 := by
        ext <;> simp
      rw [h0]; exact P.zero_mem
    exact (hP.mem_or_mem this).resolve_right h2
  set ε : k × DualNumber k := ((0 : k), (DualNumber.eps : DualNumber k)) with hε
  have hεP : ε ∈ P := by
    refine hP.mem_of_pow_mem 2 ?_
    have : ε ^ 2 = 0 := by
      ext <;> simp [hε, pow_two, DualNumber.eps_mul_eps]
    rw [this]; exact P.zero_mem
  -- every element of `P` is a multiple of `ε` up to elements killed by a unit
  have key : ∀ x ∈ P, ∃ y : k, algebraMap (k × DualNumber k) (Localization.AtPrime P) x =
      algebraMap _ _ ((0 : k), (TrivSqZeroExt.inl y : DualNumber k)) * algebraMap _ _ ε := by
    rintro ⟨a, b⟩ hx
    have hab : (a, (0 : DualNumber k)) ∈ P := by
      have : (a, (0 : DualNumber k)) = (a, (0 : DualNumber k)) * ((1 : k), (0 : DualNumber k)) := by
        simp
      rw [this]; exact P.mul_mem_left _ h1
    have hb : ((0 : k), b) ∈ P := by
      have := P.sub_mem hx hab
      simpa using this
    have hbf : b.fst = 0 := by
      by_contra hbf
      have hu := isUnit_of_fst_ne_zero b hbf
      obtain ⟨u, hu'⟩ := hu
      have : ((0 : k), (1 : DualNumber k)) ∈ P := by
        have := P.mul_mem_left ((0 : k), (((u⁻¹ : (DualNumber k)ˣ)) : DualNumber k)) hb
        simpa [← hu'] using this
      exact h2 this
    refine ⟨b.snd, ?_⟩
    have hsplit : ((a, b) : k × DualNumber k) =
        (a, 0) + ((0 : k), (TrivSqZeroExt.inl b.snd : DualNumber k)) * ε := by
      refine Prod.ext (by simp [hε]) ?_
      change b = (0 : DualNumber k) + (TrivSqZeroExt.inl b.snd : DualNumber k) * DualNumber.eps
      rw [zero_add]; exact eq_inl_snd_mul_eps_of_fst_eq_zero b hbf
    have hz : algebraMap (k × DualNumber k) (Localization.AtPrime P)
        (a, (0 : DualNumber k)) = 0 := by
      rw [IsLocalization.map_eq_zero_iff P.primeCompl]
      exact ⟨⟨((0 : k), (1 : DualNumber k)), h2⟩, by simp⟩
    rw [hsplit, map_add, hz, zero_add, map_mul]
  have hsq : ε ^ 2 = 0 := by
    ext <;> simp [hε, pow_two, DualNumber.eps_mul_eps]
  set e := algebraMap (k × DualNumber k) (Localization.AtPrime P) ε with he
  have hmax : maximalIdeal (Localization.AtPrime P) = Ideal.span {e} := by
    rw [← IsLocalization.AtPrime.map_eq_maximalIdeal P (Localization.AtPrime P)]
    apply le_antisymm
    · rw [Ideal.map_le_iff_le_comap]
      intro x hx
      obtain ⟨y, hy⟩ := key x hx
      rw [Ideal.mem_comap, hy]
      exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self e)
    · rw [Ideal.span_le, Set.singleton_subset_iff]
      exact Ideal.mem_map_of_mem _ hεP
  refine ⟨e, ?_, hmax, ?_⟩
  · intro h0
    rw [he, IsLocalization.map_eq_zero_iff P.primeCompl] at h0
    obtain ⟨⟨⟨s1, s2⟩, hs⟩, hs0⟩ := h0
    have hs2 : s2 * DualNumber.eps = 0 := by
      have := congrArg Prod.snd hs0
      simpa [hε] using this
    have hf := fst_eq_zero_of_mul_eps_eq_zero s2 hs2
    apply hs
    have hs1 : (s1, (0 : DualNumber k)) ∈ P := by
      have : (s1, (0 : DualNumber k)) =
          (s1, (0 : DualNumber k)) * ((1 : k), (0 : DualNumber k)) := by
        simp
      rw [this]; exact P.mul_mem_left _ h1
    have hs3 : ((0 : k), s2) ∈ P := by
      have : ((0 : k), s2) = ((0 : k), (TrivSqZeroExt.inl s2.snd : DualNumber k)) * ε := by
        refine Prod.ext (by simp [hε]) ?_
        change s2 = (TrivSqZeroExt.inl s2.snd : DualNumber k) * DualNumber.eps
        exact eq_inl_snd_mul_eps_of_fst_eq_zero s2 hf
      rw [this]; exact P.mul_mem_left _ hεP
    have := P.add_mem hs1 hs3
    simpa using this
  · rw [hmax, Ideal.span_singleton_pow, Ideal.span_singleton_eq_bot, he, ← map_pow, hsq,
      map_zero]

end DualNumberAndLocalization

/-! ### The counterexample `Spec (ℚ × ℚ[ε])` to Ch. 0 §4 (I) without irreducibility -/

namespace NormalFlatnessCounterexample

/-- The base field `ℚ` (in the universe of the scheme). -/
abbrev BaseField : Type u := ULift.{u} ℚ

/-- The ring `ℚ × ℚ[ε]` (dual numbers): `Spec` of it has two points, a smooth one of
multiplicity `1` and a non-reduced one of multiplicity `2`. -/
abbrev TwoPointRing : Type u := BaseField.{u} × DualNumber BaseField.{u}

theorem charZero_baseField : CharZero BaseField.{u} :=
  charZero_of_injective_ringHom
    (f := ((ULift.ringEquiv.{0, u} (R := ℚ)).symm.toRingHom : ℚ →+* BaseField.{u}))
    (ULift.ringEquiv.{0, u} (R := ℚ)).symm.injective

theorem algebraFiniteType : Algebra.FiniteType BaseField.{u} TwoPointRing.{u} := by
  have h1 : Module.Finite BaseField.{u} (DualNumber BaseField.{u}) := by
    show Module.Finite BaseField.{u} (BaseField.{u} × BaseField.{u})
    infer_instance
  have h2 : Module.Finite BaseField.{u} TwoPointRing.{u} := by
    show Module.Finite BaseField.{u} (BaseField.{u} × DualNumber BaseField.{u})
    infer_instance
  exact @Module.Finite.finiteType _ _ _ _ _ h2

/-- `Spec (ℚ × ℚ[ε])` is an algebraic scheme.  This rests on the fact that fields of
characteristic zero belong to the class `𝔅` ((a) of p. 161, `IsHironakaBase.of_field`, proved). -/
theorem isAlgebraicScheme_spec : IsAlgebraicScheme (Spec (CommRingCat.of TwoPointRing.{u})) := by
  have := charZero_baseField.{u}
  have : IsHironakaBase BaseField.{u} := IsHironakaBase.of_field _
  refine ⟨⟨BaseField.{u}, inferInstance, inferInstance, inferInstance,
    Spec.map (CommRingCat.ofHom (algebraMap BaseField.{u} TwoPointRing.{u})), ?_, ?_⟩⟩
  · rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)]
    exact RingHom.finiteType_algebraMap.mpr algebraFiniteType.{u}
  · infer_instance

/-- The prime ideal of a point of `Spec (ℚ × ℚ[ε])`. -/
def primeIdeal (x : Spec (CommRingCat.of TwoPointRing.{u})) : Ideal TwoPointRing.{u} :=
  (show PrimeSpectrum TwoPointRing.{u} from x).asIdeal

instance (x : Spec (CommRingCat.of TwoPointRing.{u})) : (primeIdeal x).IsPrime :=
  (show PrimeSpectrum TwoPointRing.{u} from x).isPrime

/-- The ring isomorphism between the stalk of `Spec R` at a prime and the localization. -/
noncomputable def stalkEquivLocalization (x : Spec (CommRingCat.of TwoPointRing.{u})) :
    (Spec (CommRingCat.of TwoPointRing.{u})).presheaf.stalk x ≃+*
      Localization.AtPrime (primeIdeal x) :=
  (Spec.stalkIso (CommRingCat.of TwoPointRing.{u}) x).commRingCatIsoToRingEquiv

/-- The maximal ideal of the stalk is the image of that of the localization. -/
theorem map_stalkEquivLocalization_symm_maximalIdeal
    (x : Spec (CommRingCat.of TwoPointRing.{u})) :
    Ideal.map (stalkEquivLocalization x).symm (maximalIdeal (Localization.AtPrime (primeIdeal x))) =
      maximalIdeal ((Spec (CommRingCat.of TwoPointRing.{u})).presheaf.stalk x) := by
  have := IsLocalRing.map_ringEquiv_maximalIdeal
    (R := Localization.AtPrime (primeIdeal x))
    (S := (Spec (CommRingCat.of TwoPointRing.{u})).presheaf.stalk x)
    (by exact (stalkEquivLocalization x).symm)
  exact this

theorem maximalIdeal_stalk_eq_bot_of_mem (x : Spec (CommRingCat.of TwoPointRing.{u}))
    (h : (((0 : BaseField.{u}), (1 : DualNumber BaseField.{u})) : TwoPointRing.{u}) ∈
      primeIdeal x) :
    maximalIdeal ((Spec (CommRingCat.of TwoPointRing.{u})).presheaf.stalk x) = ⊥ := by
  have h1 := maximalIdeal_localization_eq_bot_of_mem (primeIdeal x) h
  rw [← map_stalkEquivLocalization_symm_maximalIdeal x, h1, Ideal.map_bot]

theorem exists_maximalIdeal_stalk_eq_span_of_notMem
    (x : Spec (CommRingCat.of TwoPointRing.{u}))
    (h : (((0 : BaseField.{u}), (1 : DualNumber BaseField.{u})) : TwoPointRing.{u}) ∉
      primeIdeal x) :
    ∃ e : (Spec (CommRingCat.of TwoPointRing.{u})).presheaf.stalk x, e ≠ 0 ∧
      maximalIdeal ((Spec (CommRingCat.of TwoPointRing.{u})).presheaf.stalk x) =
        Ideal.span {e} ∧
      maximalIdeal ((Spec (CommRingCat.of TwoPointRing.{u})).presheaf.stalk x) ^ 2 = ⊥ := by
  obtain ⟨e, he0, hm, hsq⟩ := exists_maximalIdeal_localization_eq_span_of_notMem
    (primeIdeal x) h
  have hmap := map_stalkEquivLocalization_symm_maximalIdeal x
  refine ⟨(stalkEquivLocalization x).symm e, ?_, ?_, ?_⟩
  · simpa using he0
  · rw [← hmap, hm, Ideal.map_span, Set.image_singleton]
  · rw [← hmap, ← Ideal.map_pow, hsq, Ideal.map_bot]

theorem maximalIdeal_stalk_pow_two_eq_bot (x : Spec (CommRingCat.of TwoPointRing.{u})) :
    maximalIdeal ((Spec (CommRingCat.of TwoPointRing.{u})).presheaf.stalk x) ^ 2 = ⊥ := by
  by_cases h : (((0 : BaseField.{u}), (1 : DualNumber BaseField.{u})) : TwoPointRing.{u}) ∈
      primeIdeal x
  · rw [maximalIdeal_stalk_eq_bot_of_mem x h]; simp
  · exact (exists_maximalIdeal_stalk_eq_span_of_notMem x h).choose_spec.2.2

/-- The point of `Spec (ℚ × ℚ[ε])` where `ε` is non-zero in the stalk: the prime
`{(a, b) | b ∈ (ε)}`; it does not contain `(0, 1)`. -/
noncomputable def pointDualNumber : Spec (CommRingCat.of TwoPointRing.{u}) :=
  (⟨Ideal.comap (RingHom.snd BaseField.{u} (DualNumber BaseField.{u}))
    (maximalIdeal (DualNumber BaseField.{u})),
    Ideal.comap_isPrime _ _⟩ : PrimeSpectrum TwoPointRing.{u})

/-- The smooth point of `Spec (ℚ × ℚ[ε])`: the prime `0 × ℚ[ε]`; it contains `(0, 1)`. -/
noncomputable def pointField : Spec (CommRingCat.of TwoPointRing.{u}) :=
  (⟨Ideal.comap (RingHom.fst BaseField.{u} (DualNumber BaseField.{u})) ⊥,
    Ideal.comap_isPrime _ _⟩ : PrimeSpectrum TwoPointRing.{u})

theorem multAt_pointField :
    (Spec (CommRingCat.of TwoPointRing.{u})).multAt pointField.{u} = 1 := by
  have hmem : (((0 : BaseField.{u}), (1 : DualNumber BaseField.{u})) : TwoPointRing.{u}) ∈
      primeIdeal pointField.{u} := by
    show _ ∈ Ideal.comap _ _
    simp
  have hbot := maximalIdeal_stalk_eq_bot_of_mem _ hmem
  have hsq := maximalIdeal_stalk_pow_two_eq_bot pointField.{u}
  unfold Scheme.multAt
  rw [samuelMultiplicity_eq_of_maximalIdeal_pow_two_eq_bot hsq]
  have : Subsingleton (GrPiece (maximalIdeal
      ((Spec (CommRingCat.of TwoPointRing.{u})).presheaf.stalk pointField.{u})) 1) :=
    grPiece_subsingleton_of_pow_eq_bot (by rw [pow_one]; exact hbot)
  rw [Module.finrank_zero_of_subsingleton]

theorem multAt_pointDualNumber :
    (Spec (CommRingCat.of TwoPointRing.{u})).multAt pointDualNumber.{u} = 2 := by
  have hnmem : (((0 : BaseField.{u}), (1 : DualNumber BaseField.{u})) : TwoPointRing.{u}) ∉
      primeIdeal pointDualNumber.{u} := by
    show ¬ _ ∈ Ideal.comap _ _
    intro h
    rw [Ideal.mem_comap] at h
    exact (maximalIdeal.isMaximal (DualNumber BaseField.{u})).ne_top
      (Ideal.eq_top_of_isUnit_mem _ h isUnit_one)
  obtain ⟨e, he0, hm, hsq⟩ := exists_maximalIdeal_stalk_eq_span_of_notMem _ hnmem
  unfold Scheme.multAt
  rw [samuelMultiplicity_eq_of_maximalIdeal_pow_two_eq_bot hsq,
    finrank_grPiece_maximalIdeal_one_of_eq_span e he0 hm hsq]

/-- The reduced structure on all of `Spec (ℚ × ℚ[ε])`: its stalk ideals are the maximal
ideals. -/
noncomputable def reducedSubscheme : Subscheme (Spec (CommRingCat.of TwoPointRing.{u})) :=
  Subscheme.ofClosed ⊤

theorem stalkIdeal_reducedSubscheme (x : Spec (CommRingCat.of TwoPointRing.{u})) :
    reducedSubscheme.{u}.stalkIdeal x =
      maximalIdeal ((Spec (CommRingCat.of TwoPointRing.{u})).presheaf.stalk x) := by
  have hx : x ∈ reducedSubscheme.{u}.pts := by
    unfold reducedSubscheme
    rw [Subscheme.pts_ofClosed]; trivial
  exact Subscheme.stalkIdeal_eq_maximalIdeal_of_isReduced_of_sq_eq_bot _
    (Subscheme.ofClosed_isReduced _) hx (maximalIdeal_stalk_pow_two_eq_bot x)

theorem isNonsingular_reducedSubscheme : (reducedSubscheme.{u}).IsNonsingular := by
  intro y
  have hfld : IsField ((Spec (CommRingCat.of TwoPointRing.{u})).presheaf.stalk
      (reducedSubscheme.{u}.ι y) ⧸
        reducedSubscheme.{u}.stalkIdeal (reducedSubscheme.{u}.ι y)) := by
    rw [stalkIdeal_reducedSubscheme]
    exact (Ideal.Quotient.field _).toIsField
  obtain ⟨e⟩ := nonempty_stalk_quot_equiv reducedSubscheme.{u} y
  have hf := MulEquiv.isField hfld e.symm.toMulEquiv
  let _ := hf.toField
  show IsRegularLocalRing _
  infer_instance

theorem isNormallyFlatAlong_reducedSubscheme : (reducedSubscheme.{u}).IsNormallyFlatAlong := by
  intro x hx
  refine ⟨hx, fun p => ?_⟩
  rw [stalkIdeal_reducedSubscheme]
  let _ := Ideal.Quotient.field (maximalIdeal
    ((Spec (CommRingCat.of TwoPointRing.{u})).presheaf.stalk x))
  exact Module.Free.of_divisionRing _ _

end NormalFlatnessCounterexample

/-- The statement of Ch. 0 §4 (I) as printed (without "`D` irreducible") is false: on
`Spec (ℚ × ℚ[ε])`, the reduced subscheme `D` on the two points is non-singular (its local rings are
fields) and `X` is normally flat along `D`, but the multiplicities at the two points are `1` and
`2`.  The first conjunct already fails.

Statement as printed (false); see the corrected statement `equimultiple_of_normallyFlat`.  The disproof uses the fact that fields of characteristic zero lie
in the class `𝔅` (`IsHironakaBase.of_field`, (a) of p. 161, proved; needed for
`Spec` of a finite-type algebra to be an algebraic scheme) and no cited result: the multiplicities are computed
directly from the Hilbert–Samuel function (`samuelMultiplicity_eq_of_maximalIdeal_pow_two_eq_bot`),
not via `exists_hilbertSamuelPoly`. -/
@[blueprint "prop:0.4-I-as-printed-false"
  (statement := /-- The statement \cref{prop:0.4-I-as-printed} is false: for $X=\operatorname{Spec}
    (\mathbb Q\times\mathbb Q[\varepsilon]/(\varepsilon^2))$ and $D$ the reduced subscheme on
    the two
    points of $X$, $D$ is non-singular and $X$ is normally flat along $D$, but $X$ has
    multiplicity $1$ at one point and $2$ at the other.
    \textbf{Statement as printed (false); see the corrected statement \cref{prop:0.4-I}.} -/)
  (proof := /-- At the point $(0\times\mathbb Q[\varepsilon])$ the local ring is $\mathbb Q$ and at
    the other
    point it is $\mathbb Q[\varepsilon]$. In both, $\mathfrak m^2=0$, so $D$ (the reduced
    structure) has the maximal ideal as ideal, hence is non-singular, and $X$ is normally flat
    along $D$ since $\mathcal O/\mathfrak m$ is a field. The Samuel function is $1,1,1,\dots$
    resp.\ $1,2,2,\dots$, so the multiplicities are $1$ and $2$. -/)
  (latexEnv := "proposition")]
theorem Subscheme.not_equimultipleOfNormallyFlatAsPrinted :
    ¬ Subscheme.EquimultipleOfNormallyFlatAsPrinted.{u} := by
  intro H
  have := NormalFlatnessCounterexample.isAlgebraicScheme_spec.{u}
  have hpts : ∀ x, x ∈ (NormalFlatnessCounterexample.reducedSubscheme.{u}).pts := fun x => by
    unfold NormalFlatnessCounterexample.reducedSubscheme
    rw [Subscheme.pts_ofClosed]; trivial
  have := (H _ NormalFlatnessCounterexample.reducedSubscheme.{u}
    NormalFlatnessCounterexample.isNonsingular_reducedSubscheme
    NormalFlatnessCounterexample.isNormallyFlatAlong_reducedSubscheme).1
    _ (hpts NormalFlatnessCounterexample.pointField) _
    (hpts NormalFlatnessCounterexample.pointDualNumber)
  rw [NormalFlatnessCounterexample.multAt_pointField,
    NormalFlatnessCounterexample.multAt_pointDualNumber] at this
  exact absurd this (by norm_num)

end Hironaka

