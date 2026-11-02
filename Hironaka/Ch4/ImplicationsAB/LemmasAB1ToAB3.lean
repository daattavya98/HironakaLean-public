/-
Copyright (c) 2026 Daattavya Aggarwal, Minhyong Kim, Oisin Kim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daattavya Aggarwal, Minhyong Kim, Oisin Kim
-/
module

public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
public import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.Data.Nat.Nth
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.AdicCompletion.LocalRing
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.KrullDimension.Regular
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Architect
public import Hironaka.Ch0.AlgebraicScheme
public import Hironaka.Ch0.Blowup
public import Hironaka.Ch0.NormalCrossings
public import Hironaka.Ch0.NormalFlatness
public import Hironaka.Ch1.ResolutionData
public import Hironaka.Ch1.FundamentalTheorems
public import Hironaka.Compat.LocalizeSuccession
public import Hironaka.Ch3.Basic
public import Hironaka.Ch3.NuStar
public import Hironaka.Ch3.TauStar
public import Hironaka.Ch3.Frames
public import Hironaka.Ch3.PermissibleEffects
public import Hironaka.Ch3.JStability
public import Hironaka.Ch3.TauFrameExistence
public import Hironaka.Compat.CoefficientField
public import Hironaka.Ch4.Preparation
public import Hironaka.Compat.LocalizeDim
public import Hironaka.Ch3.TransformsCompletion
public import Hironaka.Compat.GenericWeierstrass
public import Hironaka.Compat.FlatStrictTransform
public import Hironaka.Compat.StalkFrameStep
public import Hironaka.Compat.FrameCore
public import Hironaka.Compat.StrictTransformRegular
public import Hironaka.Compat.FrameLocalization
public import Hironaka.Compat.StableOrder
public import Hironaka.Compat.FrameStepLocal
public import Hironaka.Compat.SingularStandardBase
public import Hironaka.Compat.LocalizeSuccessionII
public import Hironaka.Compat.ExceptionalTransversal
public import Hironaka.Compat.PermissibleCenterDescent
public import Hironaka.Compat.NagataFinite
public import Hironaka.Compat.DatumPresentation
public import Hironaka.Compat.DatumRefinement
public import Hironaka.Compat.BlowupFibreBijection
public import Hironaka.Compat.BlowupFlatPullback
public import Hironaka.Compat.TransformNormalCrossingsLocalized
public import Hironaka.Statements

/-!
# Ch. IV §3 (pp. 292–299): the setup, and Lemmas (AB.1), (AB.2) and (AB.3)

The expression `ℜ^{N,n}_I = (⋃ E_i; V_1, …, V_β; W)` (p. 274), the characters `ν*(V/X)`, `τ*(V/X)` and the
two inequalities (pp. 292–293), the symbol `S(ℜ)`, Theorems A* and B* and effective modifications
(pp. 293–294), Lemma (AB.1) (p. 294), the fixed succession `{f_s}`, the standing choices, the completion and
the schemes `X̂_s` (pp. 294–295), Lemmas (AB.2), (AB.3) and the Corollary of (AB.3) (pp. 295–296), the regular
frame `(T; z)`, `X̄_s` and `f̄_s` (pp. 296–298), and the consequence of Theorem 3 of Ch. III recalled on p. 299.

This is part 1 of 3 of `Hironaka.Ch4.ImplicationsAB`, which imports all parts; its description holds the
notation and the formalization notes for the whole section.
-/

@[expose] public section

open AlgebraicGeometry IsLocalRing CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

namespace Hironaka

universe u

/-! ## The expression `ℜ^{N,n}_I = (⋃_{i=1}^α E_i; V_1,…,V_β; W)` (Ch. IV, introduction, p. 274)

The datum `DatumI.Raw` of Ch. I carries the reduced subscheme `E` of Def. 3 (I); the chapter
introduction fixes a *presentation* of `E` as a union of `α` non-singular irreducible
subschemes of codimension one, repetitions and the empty subscheme being allowed. -/

/-- Ch. IV, p. 274: the expression `ℜ^{N,n}_I = (⋃_{i=1}^α E_i; V_1,…,V_β; W)` of a resolution
datum of type `ℜ^{N,n}_I`.  The union of a family of subschemes is the infimum of the ideal
sheaves, as in `DatumII.Raw.eUnion`. -/
@[blueprint "def:IV.0-expression"
  (statement := /-- A \emph{presentation} of a resolution datum $\mathfrak R^{N,n}_{\mathrm I}$
    (\cref{def:I.3-I}) on a non-singular irreducible algebraic scheme $X$ is an expression
    \[\mathfrak R^{N,n}_{\mathrm I}=\Big(\bigcup_{i=1}^{\alpha}E_i;V_1,V_2,\dots,V_\beta;W\Big)\]
    in which all the $E_j$ are non-singular irreducible subschemes of $X$ of codimension one
    (\cref{def:I.0-everywhere-codimension}) whose union is $E$. We do not require that $E_i$
    differ from $E_j$ if $i\ne j$, and we may find the empty subscheme of $X$ among the $E_i$,
    which is a non-singular irreducible subscheme of $X$ of codimension one according to our
    agreement upon the codimension of the empty subscheme. (Ch.\ IV, p.\ 274.) -/)
  (latexEnv := "definition")]
structure DatumI.Presentation {X : Scheme.{u}} (ℜ : DatumI.Raw X) where
  /-- The number `α` of subschemes `E_i`. -/
  α : ℕ
  /-- The subschemes `E_1, …, E_α`. -/
  E : Fin α → Subscheme X
  /-- Each `E_i` is a non-singular irreducible subscheme of codimension one (the empty
  subscheme being allowed, p. 274). -/
  E_codimOne : ∀ i, (E i).IsNonsingularIrreducibleCodimOne
  /-- `E = E_1 ∪ ⋯ ∪ E_α`. -/
  E_union : ℜ.E = ⨅ i, E i

/-- **Every datum has a presentation** `ℜ^{N,n}_I = (⋃_{i=1}^α E_i; V_1, …, V_β; W)` (the tacit
assertion of p. 274): `DatumI.Raw.isUnionOfDivisors_of_isDatum`. -/
theorem DatumI.nonempty_presentation {X : Scheme.{u}} {N : ℕ} (hX : IsAmbient X N)
    (ℜ : DatumI X) : Nonempty (DatumI.Presentation (ℜ : DatumI.Raw X)) := by
  obtain ⟨α, E, hE, hEu⟩ := DatumI.Raw.isUnionOfDivisors_of_isDatum hX (ℜ : DatumI.Raw X) ℜ.2
  exact ⟨⟨α, E, hE, hEu⟩⟩

/-! ## The characters `ν*(V/X)`, `τ*(V/X)` and the two inequalities (pp. 292–293) -/

namespace Subscheme

variable {X : Scheme.{u}}

/-- `t(V/X) = t(J_x)`, the number of distinct integers occurring in `ν*(V/X)`
(Definition 6 of Ch. III §4). -/
noncomputable def tAt (V : Subscheme X) (x : X) (hx : X.IsSimpleAt x) : ℕ :=
  @t (X.presheaf.stalk x) _ hx (V.stalkIdeal x)

/-- p. 292: "We shall also denote by `τ^{(j)}(V/X)` the integer `τ^{(j)}(J)` for
`1 ≤ j ≤ t(J)`."  (Formalization note: `Hironaka.tau` is total, so this is defined for every
`i : ℕ`; only the values `1 ≤ i ≤ t(V/X)` are the paper's.) -/
noncomputable def tauAt (V : Subscheme X) (x : X) (hx : X.IsSimpleAt x) (i : ℕ) : ℕ :=
  @tau (X.presheaf.stalk x) _ hx (V.stalkIdeal x) i

/-- p. 292: `τ*(V/X) = τ*(J_x) = (τ^{(1)}(J_x), …, τ^{(t)}(J_x))`, `t = t(J_x)`
(Definition 6 of Ch. III §4), the analogue for `τ*` of `Subscheme.nuStarAt`. -/
@[blueprint "def:IV.3-characters"
  (statement := /-- Let $X$ be a non-singular irreducible algebraic scheme, $V$ a subscheme of
    $X$ and $x$ a point of $X$. Let $S$ be the local ring of $X$ at $x$, which is a regular
    local ring, and $J$ the ideal of $V$ in $S$. Then we denote by $\nu^*_x(V/X)$ the numerical
    character $\nu^*(J)=(\nu^{(1)}(J),\nu^{(2)}(J),\dots)$ of the ideal $J$ in $S$
    (\cref{def:III.2}, \cref{def:III.4}), and by $\tau^*_x(V/X)$ the numerical character
    $\tau^*(J)=(\tau^{(1)}(J),\dots,\tau^{(t)}(J))$ with $t=t(J)$ of the ideal $J$ in $S$
    (\cref{def:III.6-t}, \cref{def:III.6-tau-star}). We shall also denote by
    $\tau^{(j)}_x(V/X)$ the integer $\tau^{(j)}(J)$ for $1\le j\le t(J)$. (p.~292.)
    (Formalization note (encoding): as for \cref{def:III.4}, this is stated at any point $x$ of $X$ at
    which $X$ is simple, and $\tau^{(i)}_x(V/X)$ is the total function $\tau^{(i)}$ of
    \cref{def:III.6}, whose values for $i>t(J)$ are not used.) -/)
  (latexEnv := "definition")]
noncomputable def tauStarAt (V : Subscheme X) (x : X) (hx : X.IsSimpleAt x) :
    Fin (V.tAt x hx) → ℕ := fun a => V.tauAt x hx ((a : ℕ) + 1)

end Subscheme

section Systems

variable {X X' : Scheme.{u}} {ι : Type*}

/-- p. 292: "If `(V_1, …, V_β)` is a system of subschemes of `X`, then we shall write
`ν*_x(V_1,…,V_β/X)` for `(ν*_x(V_1/X), …, ν*_x(V_β/X))`." -/
noncomputable def nuStarSystemAt (V : ι → Subscheme X) (x : X) (hx : X.IsSimpleAt x) :
    ι → Lex (ℕ+ → ℕ∞) := fun j => (V j).nuStarAt x hx

/-- p. 292: "and `τ*_x(V_1,…,V_β/X)` for `(τ*_x(V_1/X), …, τ*_x(V_β/X))`."  The system is
recorded as the doubly indexed family `(j, i) ↦ τ^{(i)}_x(V_j/X)` of p. 292. -/
noncomputable def tauStarSystemAt (V : ι → Subscheme X) (x : X) (hx : X.IsSimpleAt x) :
    ι → ℕ+ → ℕ := fun j i => (V j).tauAt x hx (i : ℕ)

/-- p. 292, the inequality `ν*_x(V_1,…,V_β/X) > ν*_{x'}(V_1',…,V_β'/X')`:
`ν*_x(V_j/X) ≥ ν*_{x'}(V_j'/X')` for all `j`, with strict inequality for at least one `j`. -/
@[blueprint "def:IV.3-inequalities"
  (statement := /-- Let $f\colon X'\to X$ be a finite succession of monoidal transformations
    with non-singular centers, and $V_j'$ the strict transform of $V_j$ on $X'$ for
    $1\le j\le\beta$. Let $x'$ be a point of $X'$ and $x=f(x')\in X$. Then by the inequality
    \[\nu^*_x(V_1,\dots,V_\beta/X)>\nu^*_{x'}(V_1',\dots,V_\beta'/X')\]
    we shall mean that $\nu^*_x(V_j/X)\ge\nu^*_{x'}(V_j'/X')$ (\cref{def:III.2}) for all
    $j$ $(1\le j\le\beta)$ where the strict inequality occurs for at least one $j$. And
    similarly, by the inequality
    \[\tau^*_x(V_1,\dots,V_\beta/X)<\tau^*_{x'}(V_1',\dots,V_\beta'/X')\]
    we shall mean that $\tau^{(i)}_x(V_j/X)\le\tau^{(i)}_{x'}(V_j'/X')$ for all $i$ and all
    $j$ $(1\le j\le\beta)$ where the strict inequality occurs for at least one pair $(i,j)$.
    (p.~292.) (Formalization note (encoding): the comparisons are defined for any two systems
    indexed by a common index type, in particular for $V_j'$ the strict transforms, and the
    comparison of the $\tau^{(i)}$ runs over all $i\ge1$; the values $\tau^{(i)}(J)$ for
    $i>t(J)$ of the total function are $0$, so this agrees with the paper's comparison whenever
    the two characters $\nu^*$ agree, the only situation in which it is used; see the module
    header.) -/)
  (latexEnv := "definition")]
def NuStarSystemGT (V : ι → Subscheme X) (x : X) (hx : X.IsSimpleAt x)
    (V' : ι → Subscheme X') (x' : X') (hx' : X'.IsSimpleAt x') : Prop :=
  (∀ j, nuStarSystemAt V' x' hx' j ≤ nuStarSystemAt V x hx j) ∧
    ∃ j, nuStarSystemAt V' x' hx' j < nuStarSystemAt V x hx j

/-- Equality of the systems `ν*`, i.e. `ν*_x(V_j/X) = ν*_{x'}(V_j'/X')` for all `j`. -/
def NuStarSystemEq (V : ι → Subscheme X) (x : X) (hx : X.IsSimpleAt x)
    (V' : ι → Subscheme X') (x' : X') (hx' : X'.IsSimpleAt x') : Prop :=
  ∀ j, nuStarSystemAt V' x' hx' j = nuStarSystemAt V x hx j

/-- p. 292, the inequality `τ*_x(V_1,…,V_β/X) < τ*_{x'}(V_1',…,V_β'/X')`. -/
def TauStarSystemLT (V : ι → Subscheme X) (x : X) (hx : X.IsSimpleAt x)
    (V' : ι → Subscheme X') (x' : X') (hx' : X'.IsSimpleAt x') : Prop :=
  (∀ j i, tauStarSystemAt V x hx j i ≤ tauStarSystemAt V' x' hx' j i) ∧
    ∃ j i, tauStarSystemAt V x hx j i < tauStarSystemAt V' x' hx' j i

/-- Equality of the systems `τ*`. -/
def TauStarSystemEq (V : ι → Subscheme X) (x : X) (hx : X.IsSimpleAt x)
    (V' : ι → Subscheme X') (x' : X') (hx' : X'.IsSimpleAt x') : Prop :=
  ∀ j i, tauStarSystemAt V x hx j i = tauStarSystemAt V' x' hx' j i

end Systems

/-- At a point outside the support of a subscheme, the stalk of its ideal sheaf is the unit
ideal. -/
private theorem stalkIdeal_eq_top_of_notMem {X : Scheme.{u}} (V : Subscheme X) {x : X}
    (hx : x ∉ V.pts) : V.stalkIdeal x = ⊤ := by
  have hx' : ¬ ∀ U, x ∈ X.zeroLocus (U := U.1) (V.ideal U) :=
    fun h => hx (Scheme.IdealSheafData.mem_support_iff.mpr h)
  push Not at hx'
  obtain ⟨U, hU⟩ := hx'
  rw [Scheme.mem_zeroLocus_iff] at hU
  push Not at hU
  obtain ⟨f, hf, hxf⟩ := hU
  have hxU : x ∈ (U : X.Opens) := X.basicOpen_le f hxf
  rw [Scheme.mem_basicOpen _ _ _ hxU] at hxf
  refine Ideal.eq_top_of_isUnit_mem _ (Ideal.subset_span ⟨U, hxU, f, hf, rfl⟩) hxf

section NuStarUnit

variable (R : Type u) [CommRing R] [IsRegularLocalRing R]

private theorem ordElem_one : Ideal.ordElem (maximalIdeal R) (1 : R) = 0 :=
  le_antisymm (Ideal.ordElem_le_of_notMem (m := 0) (by simp)) (by simp)

private theorem initialForm_one : initialForm (maximalIdeal R) (1 : R) = 1 := by
  have h0 := ordElem_one R
  unfold initialForm
  split_ifs with h
  · rw [h0] at h; exact absurd h ENat.zero_ne_top
  · simp only [h0, ENat.toNat_zero]
    rfl

private theorem grIdeal_top : grIdeal (maximalIdeal R) (⊤ : Ideal R) = ⊤ :=
  (Ideal.eq_top_iff_one _).mpr
    (Ideal.subset_span ⟨1, Submodule.mem_top, initialForm_one R⟩)

private theorem one_mem_homogeneous_zero :
    (1 : AssocGraded (maximalIdeal R)) ∈ AssocGraded.homogeneous (maximalIdeal R) 0 := by
  have : (1 : AssocGraded (maximalIdeal R)) = AssocGraded.mk _ 0 1 (by simp) := rfl
  rw [this]
  exact AssocGraded.mk_mem_homogeneous _ _

/-- `ν^{(1)}(J) = 0` if and only if `J` is the unit ideal. -/
private theorem nuI_one_eq_zero_iff (J : Ideal R) : nuI R J 1 = 0 ↔ J = ⊤ := by
  rw [(nuI_one_eq_nu_and_nuI_two_and_nuI_le_nuParen R J).1.1]
  constructor
  · intro h
    by_contra hJ
    have h1 : (1 : ℕ∞) ≤ ⨅ f ∈ J, Ideal.ordElem (maximalIdeal R) f :=
      le_iInf₂ fun f hf => Ideal.le_ordElem (by simpa using le_maximalIdeal hJ hf)
    rw [h] at h1
    exact absurd h1 (by simp)
  · rintro rfl
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

/-- `ν*(J) = (0, ∞, ∞, …)` if and only if `J` is the unit ideal. -/
private theorem nuStar_eq_iff_eq_top (J : Ideal R) :
    nuStar R J = toLex (fun i : ℕ+ => if i = 1 then (0 : ℕ∞) else ⊤) ↔ J = ⊤ := by
  constructor
  · intro h
    have := congrFun (congrArg ofLex h) 1
    exact (nuI_one_eq_zero_iff R J).mp (by simpa [nuStar] using this)
  · rintro rfl
    refine congrArg toLex (funext fun i => ?_)
    split_ifs with hi
    · rw [hi]; exact (nuI_one_eq_zero_iff R ⊤).mpr rfl
    · exact nuI_top_of_ne_one R hi

end NuStarUnit

/-- p. 292: "We note that `ν*(J) = (0, ∞, ∞, …)` if and only if `x ∉ V`, in which case
`t(J) = 1` and `τ^{(1)}(J) = 0`."  (At a point `x ∉ V` the stalk `J_x` is the unit ideal.) -/
@[blueprint "rem:IV.3-nu-star-empty"
  (statement := /-- Notation as in \cref{def:IV.3-characters}. We have
    $\nu^*_x(V/X)=(0,\infty,\infty,\dots)$ if and only if $x\notin V$, in which case
    $t(V/X)=1$ and $\tau^{(1)}_x(V/X)=0$. (p.~292.) -/)
  (proof := /-- $x\notin V$ means that the stalk $J_x$ is the unit ideal of $S$, i.e.\
    $\operatorname{gr}_M(J,S)=\operatorname{gr}_M(S)$; then the empty system of homogeneous
    elements has the property of \cref{def:III.1} for no $\mu$, so $\nu^{(1)}(J)=0$, while
    the system $(1)$ has it for every $\mu$, so $\nu^{(i)}(J)=\infty$ for $i\ge2$.
    Conversely $\nu^{(1)}(J)=\nu(J)=0$ forces $J_x=S$ (\cref{rem:III.1-nu}). Only the integer
    $0$ occurs in $\nu^*(J)$, so $t(J)=1$ and $\mu_1=0$; the empty system of linear forms
    generates the subalgebra $K$, which already satisfies the equality of \cref{def:III.6} for
    $\mu\le0$, so $\tau^{(1)}(J)=0$. -/)
  (latexEnv := "remark")]
theorem Subscheme.nuStarAt_eq_iff_notMem {X : Scheme.{u}} (V : Subscheme X) (x : X)
    (hx : X.IsSimpleAt x) :
    (V.nuStarAt x hx = toLex (fun i : ℕ+ => if i = 1 then (0 : ℕ∞) else ⊤) ↔ x ∉ V.pts) ∧
      (x ∉ V.pts → V.tAt x hx = 1 ∧ V.tauAt x hx 1 = 0) := by
  have : IsRegularLocalRing (X.presheaf.stalk x) := hx
  have hiff : V.stalkIdeal x = ⊤ ↔ x ∉ V.pts := by
    refine ⟨fun h hxV => ?_, stalkIdeal_eq_top_of_notMem V⟩
    have := stalkIdeal_le_maximalIdeal_of_mem_pts V hxV
    rw [h, top_le_iff] at this
    exact (maximalIdeal.isMaximal _).ne_top this
  refine ⟨(nuStar_eq_iff_eq_top _ _).trans hiff, fun hxV => ?_⟩
  -- "in which case `t(J) = 1` and `τ^{(1)}(J) = 0`": `J_x = R` (`tau_of_eq_top`)
  have h := tau_of_eq_top (X.presheaf.stalk x) (V.stalkIdeal x) (hiff.mpr hxV)
  exact ⟨h.2.1, h.2.2.2⟩

/-! ## Preliminaries for the regular frame `(T; z)` (p. 297)

The ring-theoretic facts behind "the existence of such a regular frame `(T; z)` of `Ŝ`" (p. 297):
the power series expansion of a complete regular local ring with respect to a regular frame is an
isomorphism; Cohen's coefficient field (cited) gives `Ŝ = k{z, y₁, …, y_{N-1}}` and the regular
frame `(T; z)`, `T = k{y₁, …, y_{N-1}}`; the choice of `z` in [a] and [b]; the morphisms `f̄_s`;
and the statement of [c] (`exists_regularFrame_one_and_isJStable_standardBase_weierstrass`). -/

section FramePreliminaries

/-- An element `z` of a finite set `s` can be put first in an enumeration of `s`. -/
theorem exists_fin_cons_enumeration {A : Type u} [DecidableEq A] {s : Finset A} {z : A}
    (hz : z ∈ s) : ∃ (m : ℕ) (x : Fin (m + 1) → A), Function.Injective x ∧ x 0 = z ∧
      Finset.univ.image x = s ∧ s.card = m + 1 := by
  set t := s.erase z
  have hcard : s.card = t.card + 1 := by
    rw [Finset.card_erase_of_mem hz]
    have : 0 < s.card := Finset.card_pos.mpr ⟨z, hz⟩
    omega
  let y : Fin t.card → A := fun i => (t.equivFin.symm i : A)
  have hy : Function.Injective y := fun i j h => t.equivFin.symm.injective (Subtype.ext h)
  have hyz : z ∉ Set.range y := by
    rintro ⟨i, hi⟩
    have := (t.equivFin.symm i).2
    rw [show (t.equivFin.symm i : A) = z from hi] at this
    exact (Finset.notMem_erase z s) this
  refine ⟨t.card, Fin.cons z y, Fin.cons_injective_iff.mpr ⟨hyz, hy⟩, rfl, ?_, hcard⟩
  ext w
  simp only [Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨i, rfl⟩
    refine Fin.cases ?_ (fun j => ?_) i
    · simpa using hz
    · simp only [Fin.cons_succ]
      exact Finset.mem_of_mem_erase (t.equivFin.symm j).2
  · intro hw
    by_cases hwz : w = z
    · exact ⟨0, by simp [hwz]⟩
    · obtain ⟨j, hj⟩ := t.equivFin.symm.surjective ⟨w, Finset.mem_erase.mpr ⟨hwz, hw⟩⟩
      exact ⟨j.succ, by simp [y, hj]⟩

/-- p. 297: "`(T; z)` with this `T` is a regular frame of `Ŝ`": if `Φ : R ≃ K{Z, Y₁, …, Y_m}`
sends `z` to `Z`, then `T = Φ⁻¹(K{Y₁, …, Y_m})` gives a regular frame `(T; z)` of `R` with
`r = 1` (and `R = T{z}`). -/
theorem exists_regularFrame_one_of_ringEquiv_mvPowerSeries {R : Type u} [CommRing R]
    [IsRegularLocalRing R] {K : Type u} [Field K] {m : ℕ}
    (Φ : R ≃+* MvPowerSeries (Fin (m + 1)) K) {z : R} (hz : ExtendsToRSOP R {z})
    (hΦz : Φ z = MvPowerSeries.X 0) :
    ∃ (Fr : RegularFrame R) (h1 : Fr.r = 1), Fr.z ⟨0, by rw [h1]; exact Nat.one_pos⟩ = z ∧
      ∃ ET : Fr.S ≃+* MvPowerSeries (Fin m) K, ∀ s,
        Φ (algebraMap Fr.S R s) = (MvPowerSeries.finSuccEquiv K m).symm (PowerSeries.C (ET s)) := by
  classical
  let E : R ≃+* PowerSeries (MvPowerSeries (Fin m) K) :=
    Φ.trans (MvPowerSeries.finSuccEquiv K m).toRingEquiv
  have hEz : E z = PowerSeries.X := by
    show MvPowerSeries.finSuccEquiv K m (Φ z) = PowerSeries.X
    rw [hΦz, MvPowerSeries.finSuccEquiv_X_zero]
  let T := MvPowerSeries (Fin m) K
  let ι : T →+* R := (E.symm : PowerSeries T →+* R).comp PowerSeries.C
  let φ : T →+* R ⧸ Ideal.span {z} := (Ideal.Quotient.mk _).comp ι
  have hφ : Function.Bijective φ := by
    refine ⟨(injective_iff_map_eq_zero φ).mpr fun t ht => ?_, fun w => ?_⟩
    · rw [RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton'] at ht
      obtain ⟨c, hc⟩ := ht
      have h2 := congrArg E hc
      rw [map_mul, hEz] at h2
      have h3 : E (ι t) = PowerSeries.C t := E.apply_symm_apply _
      rw [h3] at h2
      have := congrArg PowerSeries.constantCoeff h2
      rwa [map_mul, PowerSeries.constantCoeff_X, mul_zero, PowerSeries.constantCoeff_C,
        eq_comm] at this
    · obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective w
      refine ⟨PowerSeries.constantCoeff (E r), ?_⟩
      rw [RingHom.comp_apply, Ideal.Quotient.eq, Ideal.mem_span_singleton']
      have hdvd : PowerSeries.X ∣ E r - PowerSeries.C (PowerSeries.constantCoeff (E r)) := by
        rw [PowerSeries.X_dvd_iff, map_sub, PowerSeries.constantCoeff_C, sub_self]
      obtain ⟨g, hg⟩ := hdvd
      refine ⟨-E.symm g, ?_⟩
      apply E.injective
      have h3 : E (ι (PowerSeries.constantCoeff (E r))) =
          PowerSeries.C (PowerSeries.constantCoeff (E r)) := E.apply_symm_apply _
      rw [map_mul, map_neg, E.apply_symm_apply, hEz, map_sub, h3]
      linear_combination hg
  have hreg : IsRegularLocalRing (R ⧸ Ideal.span {z}) :=
    ExtendsToRSOP.isRegularLocalRing_quotient_span_singleton hz (Finset.mem_singleton_self z)
  let eφ := RingEquiv.ofBijective φ hφ
  have hregT : IsRegularLocalRing T := IsRegularLocalRing.of_ringEquiv eφ.symm
  have hloc : IsLocalHom ι := ⟨fun t ht => by
    have h1 : IsUnit (φ t) := ht.map (Ideal.Quotient.mk _)
    have h2 : IsUnit (eφ.symm (φ t)) := h1.map eφ.symm
    rwa [show eφ.symm (φ t) = t from eφ.symm_apply_apply t] at h2⟩
  let Fr : RegularFrame R :=
    { S := T
      algebra := ι.toAlgebra
      isRegular := hregT
      isLocalHom := hloc
      r := 1
      z := fun _ => z
      z_injective := fun i j _ => Subsingleton.elim i j
      extends_rsop := by
        rw [Finset.image_const Finset.univ_nonempty]
        exact hz
      quot_bijective := by
        rw [Set.range_const]
        exact hφ }
  refine ⟨Fr, rfl, rfl, RingEquiv.refl T, fun s => ?_⟩
  show Φ (Φ.symm ((MvPowerSeries.finSuccEquiv K m).toRingEquiv.symm (PowerSeries.C s))) = _
  rw [Φ.apply_symm_apply]
  rfl

/-- p. 297: "By Cohen's structure theorem of a complete regular local ring, we have a subfield
`k` of `Ŝ` and a regular system of parameters `(z, y₁, …, y_{N-1})` of `Ŝ` such that
`Ŝ = k{z, y₁, …, y_{N-1}}` (the formal power series ring of `N` variables)", for a given member
`z` of a regular system of parameters; with `T = k{y₁, …, y_{N-1}}`, `(T; z)` is a regular frame
of `Ŝ` with `r = 1`.  Here `Φ : R ≃ k{Z, Y}` sends `z ↦ Z`, `σ(t) ↦ t` (and `y_i ↦ Y_i` for
`y_i = Φ⁻¹(Y_i)`), and identifies `T` with `k{Y}`.

\textbf{Deviation from the paper (gap filled).} The paper takes `Ŝ = k{z, y}` from Cohen's
theorem; here only the existence of the coefficient field `k` is cited
(`exists_residue_comp_eq_id_of_isAdicComplete`), and `Ŝ ≃ k{z, y}` is proved: the power series
expansion of Ch. III, §9 (`RegularFrame.idealZ_isPrime_and_completion`) is bijective for a
complete ring (`RegularFrame.bijective_of_isExpansion`); that `(T; z)` is a regular frame
("Then we see that `(T; z)` with this `T` is a regular frame") is
`exists_regularFrame_one_of_ringEquiv_mvPowerSeries`. -/
@[blueprint "lem:IV.3-frame-cohen"
  (statement := /-- Let $R$ be a complete regular local ring whose residue field has
    characteristic zero, and $z$ a member of a regular system of parameters of $R$. Then there
    are a subfield $k$ of $R$ mapped isomorphically onto the residue field, and a regular system
    of parameters $(z,y_1,\dots,y_m)$ of $R$ such that $R=k\{z,y_1,\dots,y_m\}$: there is an
    isomorphism $\Phi\colon R\to k\{Z,Y_1,\dots,Y_m\}$ with $\Phi(z)=Z$ which is the identity
    on $k$. With $T=\Phi^{-1}(k\{Y_1,\dots,Y_m\})$, $(T;z)$ is a regular frame of $R$
    (\cref{def:III.9}) with $r=1$. (p.~297.) -/)
  (proof := /-- \cref{thm:cohen-coefficient-field} gives $k$. Extend $z$ to a regular system of
    parameters $(z,y_1,\dots,y_m)$; as $k\to R/M$ is bijective, $(k;z,y_1,\dots,y_m)$ is a
    regular frame of $R$. Its power series expansion $e\colon R\to k\{Z,Y\}$
    (\cref{lem:III.9-frame-completion}) is bijective because $R$ is complete: $M^n/M^{n+1}$ is
    spanned over $k$ by the monomials of degree $n$ in $z,y$, so an element of the kernel lies
    in every $M^n$ and is $0$ by Krull's intersection theorem; a power series $Q$ is the image
    of the limit of its truncations $Q_{\le n}(z,y)$. Then $T=e^{-1}(k\{Y\})\to R/zR$ is
    bijective, $R/zR$ is regular, so $T$ is a regular local ring and $(T;z)$ is a regular frame
    with $r=1$.

    \textbf{Deviation from the paper (gap filled).} The paper takes
    $\hat S=k\{z,y_1,\dots,y_{N-1}\}$ directly from Cohen's structure theorem; here only the
    existence of the coefficient field is cited (\cref{thm:cohen-coefficient-field}), and the
    isomorphism with the formal power series ring is proved from the expansion of
    \cref{lem:III.9-frame-completion}. -/)
  (proofUses := ["thm:cohen-coefficient-field", "lem:III.9-frame-completion", "def:III.9"])
  (latexEnv := "lemma")]
theorem exists_coefficientField_and_regularFrame_one [Hironaka.HironakaCitedResults.{u}] {R : Type u} [CommRing R]
    [IsRegularLocalRing R] [IsAdicComplete (maximalIdeal R) R] [CharZero (ResidueField R)]
    {z : R} (hz : ExtendsToRSOP R {z}) :
    ∃ (σ : ResidueField R →+* R) (_ : (IsLocalRing.residue R).comp σ = RingHom.id _) (m : ℕ)
      (Φ : R ≃+* MvPowerSeries (Fin (m + 1)) (ResidueField R)),
      Φ z = MvPowerSeries.X 0 ∧ (∀ t, Φ (σ t) = MvPowerSeries.C t) ∧
      (∀ a, (Φ a).order = Ideal.ordElem (maximalIdeal R) a) ∧
      ∃ (Fr : RegularFrame R) (h1 : Fr.r = 1), Fr.z ⟨0, by rw [h1]; exact Nat.one_pos⟩ = z ∧
        ∃ ET : Fr.S ≃+* MvPowerSeries (Fin m) (ResidueField R), ∀ s,
          Φ (algebraMap Fr.S R s) =
            (MvPowerSeries.finSuccEquiv _ m).symm (PowerSeries.C (ET s)) := by
  classical
  obtain ⟨σ, hσ⟩ := exists_residue_comp_eq_id_of_isAdicComplete R
  obtain ⟨s, hzs, hs⟩ := hz
  obtain ⟨m, x, hx, hx0, himg, -⟩ :=
    exists_fin_cons_enumeration (hzs (Finset.mem_singleton_self z))
  have hxs : IsRegularSystemOfParameters R (Finset.univ.image x) := by rw [himg]; exact hs
  obtain ⟨Φ, hΦx, hΦσ, hΦord⟩ :=
    exists_ringEquiv_mvPowerSeries_of_coefficientField σ hσ x hx hxs
  have hΦz : Φ z = MvPowerSeries.X 0 := by rw [← hx0]; exact hΦx 0
  exact ⟨σ, hσ, m, Φ, hΦz, hΦσ, hΦord,
    exists_regularFrame_one_of_ringEquiv_mvPowerSeries Φ ⟨s, hzs, hs⟩ hΦz⟩

/-- `τ^{(t)}(J) ≥ 1` for a proper non-zero ideal `J` of a regular local ring: an element of `J`
of the minimal order `ν^{(1)}(J) ≤ μ^{(t)}(J)` has a non-zero initial form in `gr_M(J, R)`,
which is not generated by forms of degree `0` of `gr_M(J, R)` (there are none but `0`).

\textbf{Deviation from the paper (gap filled).} Used tacitly on p. 297 ("in the case [b] we use
Theorem 9"): the `Ĵ_0`-stable regular `τ`-frame of Theorem 9 has `τ^{(t)}(Ĵ_0)` members, and one
of them is taken as `z`, which needs `τ^{(t)}(Ĵ_0) ≥ 1`. -/
theorem one_le_tau_t {R : Type u} [CommRing R] [IsRegularLocalRing R] (J : Ideal R)
    (hJ0 : J ≠ ⊥) (hJ1 : J ≠ ⊤) : 1 ≤ tau R J (t R J) := by
  classical
  by_contra h
  have h0 : tau R J (t R J) = 0 := by omega
  obtain ⟨W, -, hT⟩ := tau_spec R J (t R J)
  have hspan : Submodule.span (R ⧸ maximalIdeal R) (Set.range W) = ⊥ := by
    have : IsEmpty (Fin (tau R J (t R J))) := by rw [h0]; infer_instance
    rw [Set.range_eq_empty, Submodule.span_empty]
  rw [hspan] at hT
  have hex : ∃ d : ℕ, ∃ f ∈ J, Ideal.ordElem (maximalIdeal R) f = d := by
    obtain ⟨f, hfJ, hf0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hJ0
    have : Ideal.ordElem (maximalIdeal R) f ≠ ⊤ := fun h =>
      hf0 ((Ideal.ordElem_eq_top_iff_eq_zero (maximalIdeal.isMaximal R).ne_top).mp h)
    obtain ⟨d, hd⟩ := ENat.ne_top_iff_exists.mp this
    exact ⟨d, f, hfJ, hd.symm⟩
  obtain ⟨f₀, hf₀J, hf₀⟩ := Nat.find_spec hex
  set d₀ := Nat.find hex
  have hnu1 : nuI R J 1 = d₀ := by
    rw [(nuI_one_eq_nu_and_nuI_two_and_nuI_le_nuParen R J).1.1]
    refine le_antisymm ((iInf₂_le f₀ hf₀J).trans hf₀.le) (le_iInf₂ fun f hf => ?_)
    rcases eq_or_ne (Ideal.ordElem (maximalIdeal R) f) ⊤ with htop | htop
    · rw [htop]; exact le_top
    · obtain ⟨d, hd⟩ := ENat.ne_top_iff_exists.mp htop
      rw [← hd]
      exact_mod_cast Nat.find_min' hex ⟨f, hf, hd.symm⟩
  have hmu : d₀ ≤ mu R J (t R J) := by
    have hfin := (muSet_finite R J).1
    have hmem : d₀ ∈ muSet R J := ⟨1, hnu1⟩
    obtain ⟨k, hk, hkx⟩ := Nat.exists_lt_card_finite_nth_eq hfin hmem
    have ht : t R J = hfin.toFinset.card := Set.ncard_eq_toFinset_card _ hfin
    rw [← hkx]
    have hkt : k < t R J := by rw [ht]; exact hk
    have hk' : k ≤ t R J - 1 := by omega
    exact Nat.nth_le_nth' hk' fun hf => by
      have h1 : hf.toFinset.card = t R J := ht.symm
      omega
  have hmem0 : f₀ ∈ maximalIdeal R ^ d₀ := Ideal.mem_pow_of_ordElem hf₀
  let ψ := AssocGraded.mk (maximalIdeal R) d₀ f₀ hmem0
  have hψ0 : ψ ≠ 0 := by
    intro h
    have := (AssocGraded.mk_eq_zero_iff (maximalIdeal R) hmem0).mp h
    have h2 := Ideal.le_ordElem this
    rw [hf₀] at h2
    have h3 : d₀ + 1 ≤ d₀ := by exact_mod_cast h2
    omega
  have hψ := (hT.2 d₀ hmu ψ (AssocGraded.mk_mem_homogeneous (maximalIdeal R) hmem0)).mp
    (mk_mem_grIdeal (maximalIdeal R) hf₀J hmem0)
  have hJm : J ≤ maximalIdeal R := le_maximalIdeal hJ1
  have hzero : ∀ x ∈ (grIdeal (maximalIdeal R) J : Set (AssocGraded (maximalIdeal R))) ∩
      (Algebra.adjoin (R ⧸ maximalIdeal R)
        ((⊥ : Submodule (R ⧸ maximalIdeal R) (AssocGraded (maximalIdeal R))) :
          Set (AssocGraded (maximalIdeal R))) : Set (AssocGraded (maximalIdeal R))), x = 0 := by
    rintro x ⟨hxJ, hxA⟩
    have hxb : x ∈ (⊥ : Subalgebra (R ⧸ maximalIdeal R) (AssocGraded (maximalIdeal R))) := by
      refine Algebra.adjoin_le ?_ hxA
      rw [Submodule.bot_coe, Set.singleton_subset_iff]
      exact Subalgebra.zero_mem _
    obtain ⟨c, rfl⟩ := Algebra.mem_bot.mp hxb
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective c
    have ha0 : a ∈ maximalIdeal R ^ 0 := by rw [pow_zero, Ideal.one_eq_top]; exact Submodule.mem_top
    have hmk : algebraMap (R ⧸ maximalIdeal R) (AssocGraded (maximalIdeal R))
        (Ideal.Quotient.mk _ a) = AssocGraded.mk (maximalIdeal R) 0 a ha0 := by
      show Ideal.Quotient.mk _ _ = Ideal.Quotient.mk _ _
      congr 1
    rw [hmk] at hxJ ⊢
    obtain ⟨a', ⟨ha'J, -⟩, ha', he⟩ := (grIdeal_homogeneous_eq (maximalIdeal R) J 0 _
      (AssocGraded.mk_mem_homogeneous (maximalIdeal R) ha0)).mp hxJ
    have hsub : a - a' ∈ maximalIdeal R ^ (0 + 1) := by
      have h2 : AssocGraded.mk (maximalIdeal R) 0 (a - a') (sub_mem ha0 ha') = 0 := by
        have key : AssocGraded.mk (maximalIdeal R) 0 (a - a') (sub_mem ha0 ha') =
            AssocGraded.mk (maximalIdeal R) 0 a ha0 - AssocGraded.mk (maximalIdeal R) 0 a' ha' := by
          rw [eq_sub_iff_add_eq, ← AssocGraded.mk_add]
          congr 1
          ring
        rw [key, he, sub_self]
      exact (AssocGraded.mk_eq_zero_iff (maximalIdeal R) _).mp h2
    rw [AssocGraded.mk_eq_zero_iff]
    have := add_mem hsub (by rw [zero_add, pow_one]; exact hJm ha'J)
    rwa [sub_add_cancel] at this
  have : Ideal.span ((grIdeal (maximalIdeal R) J : Set (AssocGraded (maximalIdeal R))) ∩
      (Algebra.adjoin (R ⧸ maximalIdeal R)
        ((⊥ : Submodule (R ⧸ maximalIdeal R) (AssocGraded (maximalIdeal R))) :
          Set (AssocGraded (maximalIdeal R))) : Set (AssocGraded (maximalIdeal R)))) = ⊥ :=
    Ideal.span_eq_bot.mpr hzero
  rw [this] at hψ
  exact hψ0 ((Submodule.mem_bot _).mp hψ)

/-- [b] (p. 296, with Theorem 9, §10, Ch. III): a complete regular local ring whose residue field
has characteristic zero has, for a proper non-zero ideal `J`, a `J`-stable element `z` which is
part of a regular system of parameters (the first member of a `J`-stable regular `τ`-frame).

\textbf{Deviation from the paper (gap filled).} "First we choose `z ∈ Ŝ` as in [a] and [b],
where in the case [b] we use Theorem 9, § 10, Ch. III" (p. 297): Theorem 9 gives a `J`-stable
regular `τ`-frame `(T; z₁, …, z_τ)`, `τ = τ^{(t)}(J)`, and we take `z = z₁`; that `τ ≥ 1`
(`one_le_tau_t`) is not stated in the paper. -/
@[blueprint "lem:IV.3-frame-b"
  (statement := /-- Let $R$ be a complete regular local ring whose residue field has
    characteristic zero, and $J$ an ideal of $R$ with $0\ne J\ne R$. Then there is a $J$-stable
    element $z$ of $R$ (\cref{def:III.11}) which is a member of a regular system of parameters
    of $R$. (The choice of $z$ in case [b], p.~297.) -/)
  (proof := /-- By Theorem~9 (\cref{thm:III.9}) there is a $J$-stable regular $\tau$-frame
    $(T;z_1,\dots,z_r)$ of $R$ with $r=\tau^{(t)}(J)$, $t=t(J)$ (\cref{def:III.6}); its members
    are $J$-stable and extend to a regular system of parameters. Take $z=z_1$.

    \textbf{Deviation from the paper (gap filled).} This needs $r\ge1$, i.e.
    $\tau^{(t)}(J)\ge1$, which the paper uses tacitly (``in the case [b] we use Theorem~9'',
    p.~297). Proof: an element $f\in J$ of the least order $\nu^{(1)}(J)=\nu(J)\le\mu^{(t)}(J)$
    has a non-zero initial form in $\operatorname{gr}_M(J,R)$; if $\tau^{(t)}(J)=0$ it would lie
    in the ideal generated by the elements of $\operatorname{gr}_M(J,R)$ of degree $0$, which are
    $0$ since $J\subseteq M$. -/)
  (proofUses := ["thm:III.9", "def:III.6", "def:III.11"])
  (latexEnv := "lemma")]
theorem exists_isJStable_and_extendsToRSOP [Hironaka.HironakaCitedResults.{u}] {R : Type u} [CommRing R] [IsRegularLocalRing R]
    [IsAdicComplete (maximalIdeal R) R] [CharZero (ResidueField R)] (J : Ideal R)
    (hJ0 : J ≠ ⊥) (hJ1 : J ≠ ⊤) : ∃ z : R, IsJStable J z ∧ ExtendsToRSOP R {z} := by
  classical
  obtain ⟨⟨F, hFτ, hFJ, -⟩, -⟩ := exists_isJStableTauFrame_and_isJStable_standardBase J
  obtain ⟨hr, -, -⟩ := hFτ
  have h1 : 0 < F.r := hr ▸ one_le_tau_t J hJ0 hJ1
  refine ⟨F.z ⟨0, h1⟩, hFJ ⟨0, h1⟩, F.extends_rsop.mono ?_⟩
  rw [Finset.singleton_subset_iff]
  exact Finset.mem_image_of_mem _ (Finset.mem_univ _)

/-- A subscheme of an irreducible scheme not containing the generic point has non-zero stalks
(the argument of `MonoidalTransformation.irreducibleSpace_and_dim_eq`). -/
theorem Subscheme.stalkIdeal_ne_bot_of_genericPoint_notMem {X : Scheme.{u}} [IrreducibleSpace X]
    (D : Subscheme X) (hD : genericPoint X ∉ D.pts) (x : X) : D.stalkIdeal x ≠ ⊥ := by
  intro hbot
  set η := genericPoint X
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  have hsp : η ⤳ x := genericPoint_specializes x
  have hηU : η ∈ U := hsp.mem_open U.isOpen hxU
  have htop := Subscheme.stalkIdeal_eq_top_of_notMem_pts hD
  rw [stalkIdeal_eq_map_germ D ⟨U, hU⟩ hηU] at htop
  have hle : (D.ideal ⟨U, hU⟩).map (X.presheaf.germ U η hηU).hom ≤ ⊥ := by
    rw [Ideal.map_le_iff_le_comap]
    intro c hc
    have h0 : X.presheaf.germ U x hxU c = 0 := by
      have : (X.presheaf.germ U x hxU).hom c ∈ D.stalkIdeal x := by
        rw [stalkIdeal_eq_map_germ D ⟨U, hU⟩ hxU]
        exact Ideal.mem_map_of_mem _ hc
      rw [hbot] at this
      exact (Submodule.mem_bot _).mp this
    rw [Ideal.mem_comap, Submodule.mem_bot, ← X.presheaf.germ_stalkSpecializes hxU hsp]
    change (X.presheaf.stalkSpecializes hsp) (X.presheaf.germ U x hxU c) = 0
    rw [h0, map_zero]
  rw [htop] at hle
  exact top_ne_bot (le_bot_iff.mp hle)

/-- [a] (p. 296): if `F` is a closed restriction for the datum `ℜ` of type I and `x ∈ F`, the
ideal of `F` in `O_{X,x}` is generated by an element `z₀` which is part of a regular system of
parameters ("`z` is an element of `S` which generates the prime ideal of `F` in `S`").

\textbf{Deviation from the paper (gap filled).} "First we choose `z ∈ Ŝ` as in [a]" (p. 297):
the paper does not argue that the ideal of `F` in `S` is generated by one member of a regular
system of parameters of `S`; it follows from `F` being non-singular of codimension one with normal
crossings with `E` (Definition 5 (I.1)) via an adapted regular system of parameters
(`DatumTransform.exists_rsop_adapted_of_isClosedRestriction_datumI`). -/
@[blueprint "lem:IV.3-frame-a"
  (statement := /-- Let $X$ be non-singular, $\mathfrak R$ a resolution datum of type I on $X$,
    $F$ a closed restriction for $\mathfrak R$ (\cref{def:I.5-I.1}) and $x\in F$. Then the ideal of
    $F$ in $\mathcal O_{X,x}$ is generated by one element $z_0$ which is a member of a regular
    system of parameters of $\mathcal O_{X,x}$. (The choice of $z$ in case [a], p.~297.) -/)
  (proof := /-- $F$ is non-singular of codimension one and has only normal crossings with $E$,
    so there is a regular system of parameters of $\mathcal O_{X,x}$ adapted to $F$: the ideal of
    $F$ is generated by the product of at most one of its members; it is not the unit ideal since
    $x\in F$.

    \textbf{Deviation from the paper (gap filled).} The paper (``First we choose $z$ \dots\ as
    in [a]'', p.~297) does not argue that the ideal of $F$ in $S$ is generated by a member of a
    regular system of parameters of $S$. -/)
  (latexEnv := "lemma")]
theorem DatumI.Raw.exists_extendsToRSOP_and_stalkIdeal_eq_span_of_isClosedRestriction
    {X : Scheme.{u}} (hX : X.IsNonsingular) {ℜ : DatumI.Raw X} (hℜ : ℜ.IsDatum)
    {F : Subscheme X} (hF : ℜ.IsClosedRestriction F) {x : X} (hx : x ∈ F.pts) :
    ∃ z₀ : X.presheaf.stalk x, ExtendsToRSOP _ {z₀} ∧ F.stalkIdeal x = Ideal.span {z₀} := by
  classical
  have hBred : (Subscheme.empty : Subscheme X).IsReduced :=
    DatumTransform.isReduced_of_isNonsingular Subscheme.isNonsingular_empty
  obtain ⟨Z, hZ, -, -, J, hJZ, hJ1, hFJ⟩ :=
    DatumTransform.exists_rsop_adapted_of_isClosedRestriction_datumI (B := Subscheme.empty) hX
      hℜ.1 hℜ.2.2.1 (fun y hy => by rw [Subscheme.pts_empty] at hy; exact hy.elim) hF.1 hF.2.1
      hBred (by rw [Subscheme.pts_empty]; exact Set.empty_subset _) x
  obtain ⟨z₀, hJz⟩ := Finset.card_le_one_iff_subset_singleton.mp hJ1
  rcases Finset.subset_singleton_iff.mp hJz with rfl | rfl
  · exfalso
    rw [Finset.prod_empty, Ideal.span_singleton_one] at hFJ
    exact Subscheme.mem_pts_iff_stalkIdeal_ne_top.mp hx hFJ
  · exact ⟨z₀, ⟨Z, hJZ, hZ⟩, by rwa [Finset.prod_singleton] at hFJ⟩

/-- The strict transform `V'` of `V` maps into `V`: the monoidal transformation induces a morphism
`V' → V` (p. 167; `f̄_s` on p. 298). -/
noncomputable def MonoidalTransformation.strictTransformMap {X : Scheme.{u}} {B : Subscheme X}
    (t : MonoidalTransformation X B) (V : Subscheme X) :
    (Subscheme.strictTransform t V).toScheme ⟶ V.toScheme :=
  Scheme.IdealSheafData.subschemeMap _ _ t.f
    ((Scheme.IdealSheafData.map_gc t.f).le_u (t.totalTransform_le_strictTransform V))

/-- The morphism `V' → V` induced by `t` is the restriction of `t.f`: `ι_V ∘ f̄ = f ∘ ι_{V'}`. -/
theorem MonoidalTransformation.strictTransformMap_ι {X : Scheme.{u}} {B : Subscheme X}
    (t : MonoidalTransformation X B) (V : Subscheme X) :
    t.strictTransformMap V ≫ V.ι = (Subscheme.strictTransform t V).ι ≫ t.f :=
  Scheme.IdealSheafData.subschemeMap_subschemeι _ _ _ _

/-- The inclusion `k{Y₁, …, Y_n} → k{Z, Y₁, …, Y_n}` does not lower orders. -/
theorem le_order_coeffRingInclusion {k : Type u} [Field k] {n : ℕ}
    (a : MvPowerSeries (Fin n) k) : a.order ≤ (coeffRingInclusion k n a).order := by
  refine MvPowerSeries.le_order fun e he => ?_
  have h1 : MvPowerSeries.finSuccEquiv k n (coeffRingInclusion k n a) = PowerSeries.C a :=
    (MvPowerSeries.finSuccEquiv k n).apply_symm_apply _
  have h2 : MvPowerSeries.coeff e (coeffRingInclusion k n a) = MvPowerSeries.coeff
      (Finsupp.tail e) (PowerSeries.coeff (e 0) (MvPowerSeries.finSuccEquiv k n
        (coeffRingInclusion k n a))) := by
    rw [MvPowerSeries.coeff_coeff_finSuccEquiv, Finsupp.cons_tail]
  rw [h2, h1, PowerSeries.coeff_C]
  split_ifs with h0
  · refine MvPowerSeries.coeff_of_lt_order (lt_of_le_of_lt ?_ he)
    have h3 := degree_cons (e 0) (Finsupp.tail e)
    rw [Finsupp.cons_tail, h0, zero_add] at h3
    rw [h3]
  · exact map_zero _

/-- p. 297 ([c]) and p. 315 ([ii], [iii]): let `R` be a complete regular local ring whose residue
field has characteristic zero, `z` a member of a regular system of parameters of `R`, and `g_i`
(`i` in a finite set) non-zero elements of `R`.  Then there is a regular frame `(T; z)` of `R`
(`r = 1`) such that `g_i = u_i(z^{ν_i} + g_{i1} z^{ν_i-1} + ⋯ + g_{iν_i})` with
`ν_i = ν(g_i)`, `u_i` a unit, `g_{il} ∈ T` and `g_{il} ∈ Nˡ` (`N` the maximal ideal of `T`).
Moreover `T = Φ⁻¹(k{Y₁, …, Y_n})` for an isomorphism `Φ : R ≃ k{Z, Y₁, …, Y_n}` with `Φ(z) = Z`,
`k` the residue field, `n + 1 = dim R`.

The paper: "By Cohen's structure theorem … `Ŝ = k{z, y₁, …, y_{N-1}}` … By replacing `y_j` by
`y_j + c_j z` with suitable `c_j ∈ k` (`1 ≤ j ≤ N - 1`), we may assume that all the `g_{jk}` can
be written in the form described in [c], where `T = k{y₁, …, y_{N-1}}`" (p. 297), and similarly
[iii] on p. 315 ("`(y₁, …, y_{N-1})` is so chosen that each `g_j` can be written in the form
`g_j = u_j(z₀^ν + g_{j1} z₀^{ν-1} + ⋯ + g_{jν})`").

\textbf{Deviation from the paper (gap filled).} The paper does not say why suitable `c_j` exist
nor how the form follows: `k` is infinite and the initial forms of the finitely many `g_i ≠ 0` are
non-zero, so for generic `c` every `g_i` becomes regular in `z` of order `ν(g_i)`, and the
Weierstrass preparation theorem (Mathlib; the paper cites it for the analogous step on p. 270, not
on p. 297) gives the form with `ν(g_{il}) ≥ l`: `exists_generic_weierstrass_form`
(`Hironaka/Compat/GenericWeierstrass.lean`), applied in `k{Z, Y}` to the `Φ(g_i)`.

\textbf{Deviation from the paper (gap filled).} The transport back to `R`, which the paper does
not need as it identifies `Ŝ` with `k{z, y}`: the new frame is `T = Φ'⁻¹(k{Y})` for
`Φ' = (y_j ↦ y_j + c_j z) ∘ Φ` (`exists_regularFrame_one_of_ringEquiv_mvPowerSeries`);
`ν_i = ord Φ(g_i) = ν(g_i)`, as `Φ` transforms `ν_M` into the order of power series
(`RegularFrame.order_eq_ordElem_of_isExpansion`); and `g_{il} ∈ Nˡ`, as
`ν_M(g_{il}) ≥ ord a_{il} ≥ l` (the substitution and `k{Y} ⊆ k{Z, Y}` do not lower orders) and
`Mˡ ∩ T ⊆ Nˡ` (`RegularFrame.mem_maximalIdeal_pow_of_algebraMap_mem_pow`). -/
@[blueprint "lem:IV.3-frame-weierstrass"
  (statement := /-- Let $R$ be a complete regular local ring whose residue field $k$ has
    characteristic zero, $z$ a member of a regular system of parameters of $R$, and $g_i$ ($i$ in
    a finite set) non-zero elements of $R$. Then there is a regular frame $(T;z)$ of $R$
    (\cref{def:III.9}) with $r=1$ such that
    $g_i=u_i(z^{\nu_i}+g_{i1}z^{\nu_i-1}+\dots+g_{i\nu_i})$ with $\nu_i=\nu(g_i)$, $u_i$ a unit of
    $R$, $g_{il}\in T$ and $\nu(g_{il})\ge l$; moreover $T=\Phi^{-1}(k\{Y_1,\dots,Y_n\})$ for an
    isomorphism $\Phi\colon R\to k\{Z,Y_1,\dots,Y_n\}$ with $\Phi(z)=Z$, $n+1=\dim R$.
    (pp.~297 and~315.) -/)
  (proof := /-- By \cref{lem:IV.3-frame-cohen}, $R=k\{z,y\}$ through an isomorphism
    $\Phi\colon R\to k\{Z,Y\}$ with $\Phi(z)=Z$, which transforms the order $\nu_M$ into the
    order of power series (the leading form of an element of $M^d\setminus M^{d+1}$ is a
    non-zero homogeneous polynomial of degree $d$ in $z,y$). ``By replacing $y_j$ by $y_j+c_jz$
    with suitable $c_j\in k$ $(1\le j\le N-1)$, we may assume that all the $g_{jk}$ can be
    written in the form described in [c], where $T=k\{y_1,\dots,y_{N-1}\}$'' (p.~297).

    \textbf{Deviation from the paper (gap filled).} The paper does not say why suitable $c_j$
    exist nor how the form follows: $k$ is infinite and the initial forms of the finitely many
    $g_i\ne0$ are non-zero, so for generic $c$ every $g_i$ becomes regular in $z$ of order
    $\nu(g_i)$, and the Weierstrass preparation theorem (cited by the paper for the analogous step
    on p.~270, not on p.~297) gives the form with $\nu(g_{il})\ge l$
    (\cref{lem:IV.3-frame-generic-weierstrass}, applied in $k\{Z,Y\}$ to the $\Phi(g_i)$).

    \textbf{Deviation from the paper (gap filled).} The transport back to $R$, which the paper
    does not need as it identifies $\hat S$ with $k\{z,y\}$: the new $T$ is
    $\Phi'^{-1}(k\{Y\})$ for $\Phi'=(y_j\mapsto y_j+c_jz)\circ\Phi$, a regular frame by
    \cref{lem:IV.3-frame-cohen}; $\nu_i=\operatorname{ord}\Phi(g_i)=\nu(g_i)$; and
    $g_{il}\in N^l$ ($N$ the maximal ideal of $T$), as $\nu_M(g_{il})\ge\operatorname{ord}
    a_{il}\ge l$ (the substitution does not lower orders) and $M^l\cap T\subseteq N^l$ (the
    retraction $R\to R/zR\simeq T$ maps $M$ into $N$). -/)
  (proofUses := ["lem:IV.3-frame-cohen", "lem:IV.3-frame-generic-weierstrass", "def:III.9"])
  (latexEnv := "lemma")]
theorem exists_regularFrame_one_and_weierstrass_form [Hironaka.HironakaCitedResults.{u}] {R : Type u} [CommRing R]
    [IsRegularLocalRing R] [IsAdicComplete (maximalIdeal R) R] [CharZero (ResidueField R)]
    {z : R} (hz : ExtendsToRSOP R {z}) {ι : Type*} [Fintype ι] (g : ι → R)
    (hg : ∀ i, g i ≠ 0) :
    ∃ (Fr : RegularFrame R) (h1 : Fr.r = 1), Fr.z ⟨0, by rw [h1]; exact Nat.one_pos⟩ = z ∧
      ∃ (ν : ι → ℕ) (u : ι → Rˣ) (co : ∀ i, Fin (ν i) → Fr.S),
        (∀ i, (ν i : ℕ∞) = Ideal.ordElem (maximalIdeal R) (g i)) ∧
        (∀ i, g i = (u i : R) * (z ^ ν i + ∑ l : Fin (ν i),
          algebraMap Fr.S R (co i l) * z ^ (ν i - ((l : ℕ) + 1)))) ∧
        (∀ i (l : Fin (ν i)), co i l ∈ maximalIdeal Fr.S ^ ((l : ℕ) + 1)) ∧
        ∃ (n : ℕ) (Φ : R ≃+* MvPowerSeries (Fin (n + 1)) (ResidueField R))
          (ET : Fr.S ≃+* MvPowerSeries (Fin n) (ResidueField R)),
          Φ z = MvPowerSeries.X 0 ∧
          (∀ s, Φ (algebraMap Fr.S R s) =
            (MvPowerSeries.finSuccEquiv _ n).symm (PowerSeries.C (ET s))) ∧
          ((n + 1 : ℕ) : WithBot ℕ∞) = ringKrullDim R := by
  classical
  -- Cohen: `R = k{z, y₁, …, y_n}`
  obtain ⟨σ, hσ⟩ := exists_residue_comp_eq_id_of_isAdicComplete R
  obtain ⟨s, hzs, hs⟩ := hz
  obtain ⟨n, x, hx, hx0, himg, hcard⟩ :=
    exists_fin_cons_enumeration (hzs (Finset.mem_singleton_self z))
  have hxs : IsRegularSystemOfParameters R (Finset.univ.image x) := by rw [himg]; exact hs
  obtain ⟨Φ, hΦx, -, hΦord⟩ := exists_ringEquiv_mvPowerSeries_of_coefficientField σ hσ x hx hxs
  have hΦz : Φ z = MvPowerSeries.X 0 := by rw [← hx0]; exact hΦx 0
  set K := ResidueField R
  -- "By replacing `y_j` by `y_j + c_j z` with suitable `c_j ∈ k`": generic coordinates and
  -- Weierstrass preparation for all the `g_i` at once
  let eM := (Fintype.equivFin ι).symm
  let G : Fin (Fintype.card ι) → MvPowerSeries (Fin (n + 1)) K := fun i => Φ (g (eM i))
  have hG0 : ∀ i, G i ≠ 0 := fun i => (map_ne_zero_iff _ Φ.injective).mpr (hg _)
  obtain ⟨c, hc⟩ := exists_generic_weierstrass_form K G hG0
  have hc' : ∀ p : ι, ∃ (u : (MvPowerSeries (Fin (n + 1)) K)ˣ)
      (a : Fin (Φ (g p)).order.toNat → MvPowerSeries (Fin n) K),
      genericShift c (Φ (g p)) =
        (u : MvPowerSeries (Fin (n + 1)) K) * (MvPowerSeries.X 0 ^ (Φ (g p)).order.toNat +
          ∑ l : Fin (Φ (g p)).order.toNat, coeffRingInclusion K n (a l) *
            MvPowerSeries.X 0 ^ ((Φ (g p)).order.toNat - ((l : ℕ) + 1))) ∧
      ∀ l : Fin (Φ (g p)).order.toNat, (((l : ℕ) + 1 : ℕ) : ℕ∞) ≤ (a l).order := by
    intro p
    have hp : G (eM.symm p) = Φ (g p) := by
      show Φ (g (eM (eM.symm p))) = _
      rw [Equiv.apply_symm_apply]
    have h := hc (eM.symm p)
    rw [hp] at h
    exact h
  choose u a hu ha using hc'
  -- the new coordinates: `Φ' = (y_j ↦ y_j + c_j z) ∘ Φ`, and `T = Φ'⁻¹(k{Y})`
  let Φ' : R ≃+* MvPowerSeries (Fin (n + 1)) K :=
    Φ.trans (RingEquiv.ofBijective (genericShift c) (genericShift_bijective c))
  have hΦ' : ∀ y, Φ' y = genericShift c (Φ y) := fun y => rfl
  have hΦ'z : Φ' z = MvPowerSeries.X 0 := by
    rw [hΦ', hΦz, genericShift_apply, MvPowerSeries.subst_X (hasSubst_genericShiftData c),
      genericShiftData_zero]
  obtain ⟨Fr, h1, hFz, ET, hET⟩ :=
    exists_regularFrame_one_of_ringEquiv_mvPowerSeries Φ' ⟨s, hzs, hs⟩ hΦ'z
  have hincl : ∀ b, Φ' (algebraMap Fr.S R (ET.symm b)) = coeffRingInclusion K n b := fun b => by
    rw [hET, RingEquiv.apply_symm_apply]
    rfl
  have hv : ∀ p, Φ' ((Units.map (Φ'.symm : MvPowerSeries (Fin (n + 1)) K →* R) (u p) : Rˣ) : R) =
      u p := fun p => by
    rw [Units.coe_map, MonoidHom.coe_ofClass, RingEquiv.apply_symm_apply]
  refine ⟨Fr, h1, hFz, fun p => (Φ (g p)).order.toNat,
    fun p => Units.map (Φ'.symm : MvPowerSeries (Fin (n + 1)) K →* R) (u p),
    fun p l => ET.symm (a p l), fun p => ?_, fun p => ?_, fun p l => ?_,
    n, Φ', ET, hΦ'z, hET, by rw [← hcard]; exact hs.2⟩
  · -- `ν_i = ord Φ(g_i) = ν(g_i)`
    rw [MvPowerSeries.ne_zero_iff_order_finite.mp ((map_ne_zero_iff _ Φ.injective).mpr (hg p)),
      hΦord]
  · -- the Weierstrass form
    apply Φ'.injective
    rw [hΦ' (g p), hu p, map_mul, hv, map_add, map_pow, hΦ'z, map_sum]
    congr 2
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [map_mul, map_pow, hΦ'z, hincl]
  · -- `ν(g_{il}) ≥ l`
    refine Fr.mem_maximalIdeal_pow_of_algebraMap_mem_pow ?_
    rw [← Ideal.natCast_le_ordElem_iff, ← hΦord]
    have h2 : Φ (algebraMap Fr.S R (ET.symm (a p l))) =
        genericShift (-c) (Φ' (algebraMap Fr.S R (ET.symm (a p l)))) := by
      rw [hΦ', genericShift_neg_genericShift]
    rw [h2, hincl]
    exact (ha p l).trans ((le_order_coeffRingInclusion _).trans
      (le_order_genericShift (-c) _))

/-- [c] (p. 297), the ring-theoretic part: let `R` be a complete regular local ring whose residue
field has characteristic zero, `z` a member of a regular system of parameters of `R`, and
`(J_j)` finitely many ideals of `R`.  Then there are a regular frame `(T; z)` of `R` (`r = 1`) and
`J_j`-stable standard bases `(g_{j1}, …, g_{jm_j})` of the `J_j` such that
`g_{jk} = u_{jk}(z^{ν_{jk}} + g_{jk1} z^{ν_{jk}-1} + ⋯ + g_{jkν_{jk}})` with
`ν_{jk} = ν^{(k)}(J_j)`, `u_{jk}` a unit and `g_{jki} ∈ T`; moreover `ν(g_{jki}) ≥ i`.

The paper's argument (p. 297): "By Cohen's structure theorem of a complete regular local ring, we
have a subfield `k` of `Ŝ` and a regular system of parameters `(z, y₁, …, y_{N-1})` of `Ŝ` such
that `Ŝ = k{z, y₁, …, y_{N-1}}`" (`exists_coefficientField_and_regularFrame_one`). "Then we
choose a `Ĵ_j`-stable standard base of `Ĵ_j` for each `j` …, say `(g_{j1}, …, g_{jm_j})` (see
Theorem 9, §10, Ch. III)" (`exists_isJStableTauFrame_and_isJStable_standardBase`). "By replacing
`y_j` by `y_j + c_j z` with suitable `c_j ∈ k` (`1 ≤ j ≤ N - 1`), we may assume that all the
`g_{jk}` can be written in the form described in [c], where `T = k{y₁, …, y_{N-1}}`. Then we see
that `(T; z)` with this `T` is a regular frame of `Ŝ`"
(`exists_regularFrame_one_of_ringEquiv_mvPowerSeries`).

The change of coordinates and `J`-stability: `J`-stability (Definition 11, Ch. III, §9,
`IsJStable`) is a property of the ideal `J` and the element `g` of `R` alone (it quantifies over
all permissible successions of monoidal transforms and the strict transforms of `g`); it does not
involve a frame or a system of coordinates.  The replacement `y_j ↦ y_j + c_j z` changes the
subring `T` and the coefficients `g_{jki}`, but neither the elements `g_{jk}` nor `z`, so the
`g_{jk}` stay `Ĵ_j`-stable and `z` stays `Ĵ_0`-stable; this is the paper's remark "in [b] we may
replace `T` by any local subring `T'` of `Ŝ` such that the natural homomorphism `Ŝ → Ŝ/(z)Ŝ`
induces an isomorphism `T' → Ŝ/(z)Ŝ`".  No gap here.

\textbf{Deviation from the paper (gap filled).} The choice of the `c_j`, the Weierstrass
preparation and the transport back to `R` (not argued in the paper) are
`exists_regularFrame_one_and_weierstrass_form`, applied to all the `g_{jk}` at once; then
`ν_{jk} = ν(g_{jk}) = ν^{(k)}(J_j)` (`ordElem_eq_nuI_of_isStandardBase`). -/
@[blueprint "lem:IV.3-frame-c"
  (statement := /-- Let $R$ be a complete regular local ring whose residue field has
    characteristic zero, $z$ a member of a regular system of parameters of $R$, and $J_j$
    ($j$ in a finite set) ideals of $R$. Then there are a regular frame $(T;z)$ of $R$
    (\cref{def:III.9}) with $r=1$ and $J_j$-stable standard bases $(g_{j1},\dots,g_{jm_j})$ of
    $J_j$ (\cref{def:III.3}, \cref{def:III.11}) such that
    $g_{jk}=u_{jk}(z^{\nu_{jk}}+g_{jk1}z^{\nu_{jk}-1}+\dots+g_{jk\nu_{jk}})$ where
    $\nu_{jk}=\nu^{(k)}(J_j)$ (\cref{def:III.1}), $u_{jk}$ is a unit of $R$, $g_{jki}\in T$ and
    $\nu(g_{jki})\ge i$. (The existence of [c], p.~297.) -/)
  (proof := /-- ``By Cohen's structure theorem of a complete regular local ring, we have a
    subfield $k$ of $\hat S$ and a regular system of parameters $(z,y_1,\dots,y_{N-1})$ of
    $\hat S$ such that $\hat S=k\{z,y_1,\dots,y_{N-1}\}$'' (\cref{lem:IV.3-frame-cohen}).
    ``Then we choose a $\hat J_j$-stable standard base of $\hat J_j$ for each $j$
    $(0\le j\le\beta)$, say $(g_{j1},\dots,g_{jm_j})$ (see Theorem~9, \S10, Ch.~III)''
    (\cref{thm:III.9}). ``By replacing $y_j$ by $y_j+c_jz$ with suitable $c_j\in k$
    $(1\le j\le N-1)$, we may assume that all the $g_{jk}$ can be written in the form described
    in [c], where $T=k\{y_1,\dots,y_{N-1}\}$. Then we see that $(T;z)$ with this $T$ is a regular
    frame of $\hat S$'' (p.~297; \cref{lem:IV.3-frame-cohen}).

    $J$-stability (\cref{def:III.11}) is a property of the ideal and of the element of $R$
    alone, not of a frame or of coordinates; the replacement $y_j\mapsto y_j+c_jz$ changes $T$
    and the $g_{jki}$ but neither the $g_{jk}$ nor $z$, so the $g_{jk}$ stay $\hat J_j$-stable
    and $z$ stays $\hat J_0$-stable (the paper's remark that in [b] $T$ may be replaced by any
    $T'$ with $T'\simeq\hat S/(z)\hat S$).

    \textbf{Deviation from the paper (gap filled).} The paper does not say why suitable $c_j$
    exist nor how the form [c] follows; the generic choice of the $c_j$, the Weierstrass
    preparation theorem and the transport back to $\hat S$ are \cref{lem:IV.3-frame-weierstrass},
    applied to all the $g_{jk}$ at once; then $\nu_{jk}=\nu(g_{jk})=\nu^{(k)}(J_j)$, as the
    initial forms of a standard base have the degrees $\nu^{(k)}(J_j)$. -/)
  (proofUses := ["lem:IV.3-frame-weierstrass", "thm:III.9", "def:III.3", "def:III.11"])
  (latexEnv := "lemma")]
theorem exists_regularFrame_one_and_isJStable_standardBase_weierstrass [Hironaka.HironakaCitedResults.{u}] {R : Type u}
    [CommRing R] [IsRegularLocalRing R] [IsAdicComplete (maximalIdeal R) R]
    [CharZero (ResidueField R)] {z : R} (hz : ExtendsToRSOP R {z}) {ι : Type*} [Fintype ι]
    (J : ι → Ideal R) :
    ∃ (Fr : RegularFrame R) (h1 : Fr.r = 1), Fr.z ⟨0, by rw [h1]; exact Nat.one_pos⟩ = z ∧
      ∃ (m : ι → ℕ) (g : ∀ j, Fin (m j) → R) (v : ∀ j, Fin (m j) → Rˣ)
        (ν : ∀ j, Fin (m j) → ℕ) (co : ∀ j k, Fin (ν j k) → Fr.S),
        (∀ j, IsStandardBase R (J j) (g j)) ∧ (∀ j k, IsJStable (J j) (g j k)) ∧
        (∀ j k, (ν j k : ℕ∞) = nuI R (J j) (k : ℕ).succPNat) ∧
        (∀ j k, g j k = (v j k : R) * (z ^ ν j k + ∑ i : Fin (ν j k),
          algebraMap Fr.S R (co j k i) * z ^ (ν j k - ((i : ℕ) + 1)))) ∧
        ∀ j k (i : Fin (ν j k)), co j k i ∈ maximalIdeal Fr.S ^ ((i : ℕ) + 1) := by
  classical
  -- Theorem 9, §10, Ch. III: `J_j`-stable standard bases `(g_{j1}, …, g_{jm_j})`
  choose m g hstd hJst using fun j =>
    (exists_isJStableTauFrame_and_isJStable_standardBase (J j)).2
  have hg0 : ∀ j k, g j k ≠ 0 := fun j k h0 => by
    have hne : initialForm (maximalIdeal R) (g j k) ≠ 0 := fun h =>
      (hstd j).2.2.2.2 k (by beta_reduce; rw [h]; exact zero_mem _)
    apply hne
    rw [initialForm, dite_eq_left (Ideal.ordElem_eq_top_iff.mpr fun ν => by
      rw [h0]; exact zero_mem _)]
  -- Cohen, the generic coordinates `y_j + c_j z` and Weierstrass, for all the `g_{jk}` at once
  obtain ⟨Fr, h1, hFz, ν, u, co, hν, hform, hco, -⟩ :=
    exists_regularFrame_one_and_weierstrass_form hz (fun p : Σ j, Fin (m j) => g p.1 p.2)
      fun p => hg0 p.1 p.2
  refine ⟨Fr, h1, hFz, m, g, fun j k => u ⟨j, k⟩, fun j k => ν ⟨j, k⟩, fun j k => co ⟨j, k⟩,
    hstd, hJst, fun j k => ?_, fun j k => hform ⟨j, k⟩, fun j k => hco ⟨j, k⟩⟩
  -- `ν_{jk} = ν(g_{jk}) = ν^{(k)}(J_j)`
  exact (hν ⟨j, k⟩).trans (ordElem_eq_nuI_of_isStandardBase (J j) (g j) (hstd j) k)

end FramePreliminaries

noncomputable section

namespace AB

/-! ## Finite successions: appending a transformation, and the system `(V_1, …, V_β, W)` -/

/-- Appending one monoidal transformation at the end of a finite succession (the successions of
`Hironaka/Ch0/Blowup.lean` are built from the front). -/
def _root_.Hironaka.MonoidalSuccession.snoc : {X Y : Scheme.{u}} → MonoidalSuccession X Y → (B : Subscheme Y) →
    (t : MonoidalTransformation Y B) → MonoidalSuccession X t.X'
  | _, _, .nil _, B, t => .cons B t (.nil t.X')
  | _, _, .cons B' t' rest, B, t => .cons B' t' (Hironaka.MonoidalSuccession.snoc rest B t)

/-- The transform of a datum along `g` followed by `t` is the transform by `t` of the transform
along `g` (Definition 8). -/
theorem _root_.Hironaka.MonoidalSuccession.transformI_snoc {X Y : Scheme.{u}} (g : MonoidalSuccession X Y) (B : Subscheme Y)
    (t : MonoidalTransformation Y B) (ℜ : DatumI.Raw X) :
    (Hironaka.MonoidalSuccession.snoc g B t).transformI ℜ = (g.transformI ℜ).transform t := by
  induction g with
  | nil X => rfl
  | cons B' t' rest ih => exact ih B t (ℜ.transform t')

/-- The strict transform along `g` followed by `t` is the strict transform by `t` of the strict
transform along `g` (p. 167). -/
theorem _root_.Hironaka.MonoidalSuccession.strictTransform_snoc {X Y : Scheme.{u}} (g : MonoidalSuccession X Y) (B : Subscheme Y)
    (t : MonoidalTransformation Y B) (V : Subscheme X) :
    (Hironaka.MonoidalSuccession.snoc g B t).strictTransform V = Subscheme.strictTransform t (g.strictTransform V) := by
  induction g with
  | nil X => rfl
  | cons B' t' rest ih => exact ih B t (Subscheme.strictTransform t' V)

/-- The number `β` of the `V_j` does not change under transforms (Definition 7). -/
theorem _root_.Hironaka.MonoidalSuccession.β_transformI {X Y : Scheme.{u}} (g : MonoidalSuccession X Y) (ℜ : DatumI.Raw X) :
    (g.transformI ℜ).β = ℜ.β := by
  induction g with
  | nil X => rfl
  | cons B t rest ih => exact ih (ℜ.transform t)

/-- The `V_j'` of the transform of a datum are the strict transforms of the `V_j`
(Definition 7, iterated). -/
theorem _root_.Hironaka.MonoidalSuccession.V_transformI {X Y : Scheme.{u}} (g : MonoidalSuccession X Y) (ℜ : DatumI.Raw X)
    (j : Fin ℜ.β) :
    (g.transformI ℜ).V (Fin.cast (Hironaka.MonoidalSuccession.β_transformI g ℜ).symm j) = g.strictTransform (ℜ.V j) := by
  induction g with
  | nil X => rfl
  | cons B t rest ih => exact ih (ℜ.transform t) j

/-- The system `(V_1, …, V_β, W)` of a datum `ℜ = (E; V_1, …, V_β; W)` (pp. 292–294, e.g.
`ν*_x(V_1, …, V_β, W/X)` in Theorem A*): the `V_j` at the indices `j < β` and `W` at the last
index. -/
def datumSystem {X : Scheme.{u}} (ℜ : DatumI.Raw X) : Fin (ℜ.β + 1) → Subscheme X :=
  Fin.snoc (α := fun _ => Subscheme X) ℜ.V ℜ.W

/-- The system `(V_1', …, V_β', W')` of the transform `f*(ℜ)` along a finite succession `f`,
formed by strict transforms (p. 292: "`V_j'` the strict transform of `V_j` on `X'`"). -/
def succSystem {X Y : Scheme.{u}} (g : MonoidalSuccession X Y) (ℜ : DatumI.Raw X) :
    Fin (ℜ.β + 1) → Subscheme Y :=
  fun j => g.strictTransform (datumSystem ℜ j)

/-- `succSystem` consists of the members of the transformed datum `g*(ℜ)`: its last member is
the principal subscheme `W'` and the others are the `V_j'`. -/
theorem succSystem_eq_transformI {X Y : Scheme.{u}} (g : MonoidalSuccession X Y)
    (ℜ : DatumI.Raw X) :
    succSystem g ℜ (Fin.last ℜ.β) = (g.transformI ℜ).W ∧
      ∀ j : Fin ℜ.β, succSystem g ℜ j.castSucc =
        (g.transformI ℜ).V (Fin.cast (Hironaka.MonoidalSuccession.β_transformI g ℜ).symm j) := by
  refine ⟨?_, fun j => ?_⟩
  · simp only [succSystem, datumSystem, Fin.snoc_last]
    exact (MonoidalSuccession.transformI_W g ℜ).symm
  · simp only [succSystem, datumSystem, Fin.snoc_castSucc]
    exact (Hironaka.MonoidalSuccession.V_transformI g ℜ j).symm

/-! ## Resolution data with restriction and the symbol `S(ℜ)` (p. 293) -/

/-- p. 292: "let `ℜ` be any resolution datum on `X` of the form either `ℜ = (ℜ^{N,n}_I, F)`
or `ℜ = (ℜ^{N,n}_I, U)`".  The second member of such a pair: a closed restriction `F` or an
open restriction `U` (Definition 5 (I.1), (I.2)). -/
inductive Restriction (X : Scheme.{u}) : Type u
  /-- A closed restriction `F`. -/
  | closed (F : Subscheme X)
  /-- An open restriction `U`. -/
  | opn (U : Set X)

namespace Restriction

variable {X Y : Scheme.{u}}

/-- `r` is a restriction for the datum `ℜ` (Definition 5 (I.1), resp. (I.2)). -/
def IsFor (r : Restriction X) (ℜ : DatumI.Raw X) : Prop :=
  match r with
  | closed F => ℜ.IsClosedRestriction F
  | opn U => ℜ.IsOpenRestriction U

/-- The restriction is closed (as opposed to open). -/
def IsClosedKind (r : Restriction X) : Prop :=
  match r with
  | closed _ => True
  | opn _ => False

/-- A center `B` is permissible for `(ℜ, r)` (Definition 6, p. 168). -/
def IsPermissibleCenter (r : Restriction X) (ℜ : DatumI.Raw X) (B : Subscheme X) : Prop :=
  match r with
  | closed F => ℜ.IsPermissibleClosed F B
  | opn U => ℜ.IsPermissibleOpen U B

/-- A finite succession is permissible for `(ℜ, r)` (Definition 8, p. 169). -/
def IsPermissibleSucc (r : Restriction X) (g : MonoidalSuccession X Y) (ℜ : DatumI.Raw X) :
    Prop :=
  match r with
  | closed F => g.IsPermissibleIClosed ℜ F
  | opn U => g.IsPermissibleIOpen ℜ U

/-- The transform of the restriction along a finite succession: the strict transform `F'` of
`F`, resp. `U' = f⁻¹(U)` (Definition 7, p. 168, iterated). -/
def transformSucc (r : Restriction X) (g : MonoidalSuccession X Y) : Restriction Y :=
  match r with
  | closed F => closed (g.strictTransform F)
  | opn U => opn (g.transformOpen U)

/-- The transform of a restriction is of the same kind. -/
theorem isClosedKind_transformSucc (r : Restriction X) (g : MonoidalSuccession X Y) :
    (r.transformSucc g).IsClosedKind ↔ r.IsClosedKind := by
  cases r <;> exact Iff.rfl

end Restriction

/-- p. 293: the symbol `S(ℜ)`. -/
@[blueprint "def:IV.3-S"
  (statement := /-- To prove Theorems A and B (\cref{thm:IV.A}, \cref{thm:IV.B}), we introduce
    the symbol $S(\mathfrak R)$ which is defined as follows: if
    $\mathfrak R=(\mathfrak R^{N,n}_{\mathrm I},F)$, then $S(\mathfrak R)$ denotes the set of
    points of $W\cap F$, and if $\mathfrak R=(\mathfrak R^{N,n}_{\mathrm I},U)$ then
    $S(\mathfrak R)$ denotes the set of points of $W$ at which the datum
    $\mathfrak R^{N,n}_{\mathrm I}$ is not resolved (\cref{def:I.4-I}). (p.~293.)
    (Formalization note (encoding): a datum with restriction is a pair of a datum
    $\mathfrak R^{N,n}_{\mathrm I}$ and a restriction, closed $F$ or open $U$, and
    $S(\mathfrak R)$ is defined by cases.) -/)
  (latexEnv := "definition")]
def S {X : Scheme.{u}} (ℜ : DatumI.Raw X) (r : Restriction X) : Set X :=
  match r with
  | .closed F => ℜ.W.pts ∩ F.pts
  | .opn _ => ℜ.unresolvedSet

/-- p. 295: "`W*` denotes `W ∩ F` (resp. `W − U`) for the case in which `ℜ = (ℜ^{N,n}_I, F)`
(resp. `ℜ = (ℜ^{N,n}_I, U)`)". -/
def wStar {X : Scheme.{u}} (ℜ : DatumI.Raw X) (r : Restriction X) : Set X :=
  match r with
  | .closed F => ℜ.W.pts ∩ F.pts
  | .opn U => ℜ.W.pts \ U

/-! ## Theorems A* and B*, effective modifications (pp. 293–294) -/

/-- The properties (i) and (ii) of Theorems A* and B* (pp. 293–294) of a finite succession
`f : X' → X` for the datum `(ℜ, r)`, with `ℜ' = f*(ℜ)`:
(i) `f(S(ℜ'))` is at most a finite number of points of `X` at which `X` has dimension `N`;
(ii) for every `x' ∈ S(ℜ')` at which `X'` has dimension `N`, with `x = f(x')`, either
(a) `ν*_{x'}(V_1', …, V_β', W'/X') < ν*_x(V_1, …, V_β, W/X)`, or (b) these are equal and
`τ*_{x'}(V_1', …, V_β', W'/X') > τ*_x(V_1, …, V_β, W/X)`.
The characters are formed where `X'` and `X` are simple, and (a) ∨ (b) is asserted whenever
they are (see the module header). -/
def HasEffectiveProperties (N : ℕ) {X Y : Scheme.{u}} (ℜ : DatumI.Raw X) (r : Restriction X)
    (f : MonoidalSuccession X Y) : Prop :=
  (f.composite.base '' S (f.transformI ℜ) (r.transformSucc f)).Finite ∧
  (∀ y ∈ f.composite.base '' S (f.transformI ℜ) (r.transformSucc f),
    X.dimAt y = (N : WithBot ℕ∞)) ∧
  ∀ x' ∈ S (f.transformI ℜ) (r.transformSucc f), Y.dimAt x' = (N : WithBot ℕ∞) →
    ∀ (hx' : Y.IsSimpleAt x') (hx : X.IsSimpleAt (f.composite.base x')),
      NuStarSystemGT (datumSystem ℜ) (f.composite.base x') hx (succSystem f ℜ) x' hx' ∨
        (NuStarSystemEq (datumSystem ℜ) (f.composite.base x') hx (succSystem f ℜ) x' hx' ∧
          TauStarSystemLT (datumSystem ℜ) (f.composite.base x') hx (succSystem f ℜ) x' hx')

/-- p. 294: an effective modification of `X` for `ℜ`. -/
@[blueprint "def:IV.3-effective-modification"
  (statement := /-- The notation being as in Theorems A* and B* (\cref{thm:IV.A-star},
    \cref{thm:IV.B-star}), a permissible succession of monoidal transformations of $X$ for the
    given resolution datum $\mathfrak R$ (\cref{def:I.8}) will be called an \emph{effective
    modification of $X$ for $\mathfrak R$} if it has the properties (i) and (ii) of Theorems
    A* and B* respectively. (p.~294.) -/)
  (latexEnv := "definition")]
def IsEffectiveModification (N : ℕ) {X Y : Scheme.{u}} (ℜ : DatumI.Raw X) (r : Restriction X)
    (f : MonoidalSuccession X Y) : Prop :=
  r.IsPermissibleSucc f ℜ ∧ HasEffectiveProperties N ℜ r f

/-! ## Helpers for Lemma (AB.1) and its consequence -/

section

variable {X Y Z : Scheme.{u}}

/-- The transform of a restriction along a composite succession (iterating Definition 7, p. 168). -/
theorem Restriction.transformSucc_append (r : Restriction X) (s : MonoidalSuccession X Y)
    (s' : MonoidalSuccession Y Z) :
    r.transformSucc (s.append s') = (r.transformSucc s).transformSucc s' := by
  cases r with
  | closed F => simp [Restriction.transformSucc, MonoidalSuccession.strictTransform_append]
  | opn U => simp [Restriction.transformSucc, MonoidalSuccession.transformOpen_append]

/-- Permissibility of a composite succession (Definition 8, p. 169), for a restriction. -/
theorem Restriction.isPermissibleSucc_append (r : Restriction X) (s : MonoidalSuccession X Y)
    (s' : MonoidalSuccession Y Z) (ℜ : DatumI.Raw X) :
    r.IsPermissibleSucc (s.append s') ℜ ↔
      r.IsPermissibleSucc s ℜ ∧ (r.transformSucc s).IsPermissibleSucc s' (s.transformI ℜ) := by
  cases r with
  | closed F => exact MonoidalSuccession.isPermissibleIClosed_append s s' ℜ F
  | opn U => exact MonoidalSuccession.isPermissibleIOpen_append s s' ℜ U

theorem Restriction.IsPermissibleSucc.isPermissibleI {X Y : Scheme.{u}} {r : Restriction X}
    {s : MonoidalSuccession X Y} {ℜ : DatumI.Raw X} (h : r.IsPermissibleSucc s ℜ) :
    s.IsPermissibleI ℜ := by
  cases r with
  | closed F => exact MonoidalSuccession.IsPermissibleIClosed.isPermissibleI h
  | opn U => exact MonoidalSuccession.IsPermissibleIOpen.isPermissibleI h

/-- Along a permissible succession for `(ℜ, r)`, the ambient scheme stays ambient of dimension `N`, the transformed tuple stays a datum with `dim W ≤ n`, and the transformed restriction stays a restriction (Remark 1 of Ch. I, p. 169, and `rem:I.1-transform-is-datum-I`). -/
theorem isGoodDatumI_transformI_and_isFor_transformSucc [Hironaka.HironakaCitedResults.{u}] {N n : ℕ} (s : MonoidalSuccession X Y)
    {ℜ : DatumI.Raw X} {r : Restriction X} (h : IsGoodDatumI N n X ℜ) (hr : r.IsFor ℜ)
    (hs : r.IsPermissibleSucc s ℜ) :
    IsGoodDatumI N n Y (s.transformI ℜ) ∧ (r.transformSucc s).IsFor (s.transformI ℜ) := by
  cases r with
  | closed F => exact IsGoodDatumI.succession_closed s h hr hs
  | opn U => exact IsGoodDatumI.succession_open s h hr hs

/-- Off the center, resolvedness is transported by a monoidal transformation: if `y` is not on
`f⁻¹(B)` and `ℜ` is resolved at `f(y)`, then `f*(ℜ)` is resolved at `y` (`f` is a local isomorphism
there; compare the proof that the transform of an open restriction is an open restriction). -/
theorem _root_.Hironaka.DatumI.Raw.resolvedAt_transform_of_notMem_exceptional {B : Subscheme X} {ℜ : DatumI.Raw X}
    (hℜ : ℜ.IsDatum) (t : MonoidalTransformation X B) {y : t.X'}
    (hyE : y ∉ t.exceptional.pts) (hres : ℜ.ResolvedAt (t.f.base y)) :
    (ℜ.transform t).ResolvedAt y := by
  obtain ⟨Z, ι, j', h1, h2, h3, h4, -, hcomp, hrι, hrange, hexc, htt⟩ :=
    Hironaka.DatumTransform.exists_flat_isPreimmersion_off_center t
  have hyr : y ∈ Set.range j'.base := by rw [hrange]; exact hyE
  obtain ⟨u, rfl⟩ := hyr
  rw [hcomp] at hres
  refine ⟨?_, fun j => ?_, ?_⟩
  · refine (FlatPreimm.isSimpleAt_totalTransform_iff j' _ u).mp ?_
    show (Subscheme.totalTransform j' (Subscheme.strictTransform t ℜ.W)).IsSimpleAt u
    rw [htt]
    exact (FlatPreimm.isSimpleAt_totalTransform_iff ι _ u).mpr hres.1
  · refine (FlatPreimm.isNormallyFlatAlongAt'_totalTransform_iff j' _ _
      ((hℜ.2.2.2.2 j).strictTransform t) u).mp ?_
    show Subscheme.IsNormallyFlatAlongAt'
      (Subscheme.totalTransform j' (Subscheme.strictTransform t (ℜ.V j)))
      (Subscheme.totalTransform j' (Subscheme.strictTransform t ℜ.W)) u
    rw [htt, htt]
    exact (FlatPreimm.isNormallyFlatAlongAt'_totalTransform_iff ι _ _
      (hℜ.2.2.2.2 j) u).mpr (hres.2.1 j)
  · refine (FlatPreimm.hasOnlyNormalCrossingsWithAt_totalTransform_iff j' _ _ u).mp ?_
    have hE' : Subscheme.totalTransform j' ((ℜ.transform t).E) =
        Subscheme.totalTransform ι ℜ.E := by
      show Subscheme.totalTransform j'
        ((Subscheme.strictTransform t ℜ.E).union t.exceptional) = _
      rw [FlatPreimm.totalTransform_union, htt, hexc]
      exact inf_top_eq _
    show (Subscheme.totalTransform j' (ℜ.transform t).E).HasOnlyNormalCrossingsWithAt
      (Subscheme.totalTransform j' (Subscheme.strictTransform t ℜ.W)) u
    rw [hE', htt]
    exact (FlatPreimm.hasOnlyNormalCrossingsWithAt_totalTransform_iff ι _ _ u).mpr hres.2.2

/-- A subscheme `D` with `E` having only normal crossings with `D` at a point `y` of `D` of a
non-singular scheme is simple at `y`. -/
theorem _root_.Hironaka.Subscheme.isSimpleAt_of_hasOnlyNormalCrossingsWithAt {Y : Scheme.{u}} {E D : Subscheme Y}
    {y : Y} (hY : Y.IsSimpleAt y) (hyD : y ∈ D.pts) (h : E.HasOnlyNormalCrossingsWithAt D y) :
    D.IsSimpleAt y := by
  obtain ⟨z, hz, -, T, hTz, hD⟩ := h
  have : IsRegularLocalRing (Y.presheaf.stalk y) := hY
  refine ⟨hyD, ?_⟩
  rw [hD]
  exact ((ExtendsToRSOP.of_isRegularSystemOfParameters hz).mono hTz).isRegularLocalRing_quotient

/-- p. 294: "`f_i(S(ℜ_{i+1})) ⊆ S(ℜ_i)` (See Corollary 2 of Theorem 5, §6, Ch. III, and Lemma 4, §2,
Ch. IV)", open case, one step: if `f*(ℜ)` is not resolved at a point `y` of `W'`, then `ℜ` is not
resolved at `f(y)`.  Contrapositive: if `ℜ` is resolved at `x = f(y)`, then `f*(ℜ)` is resolved at
`y`.  Off the center this is the local isomorphism
(`DatumI.Raw.resolvedAt_transform_of_notMem_exceptional`).  Over a point of the center `B` (a
center permissible for the open restriction `U`, so `W − B` is dense in `W`): `W'` is simple at
`y`, the `V_j'` are normally flat along `W'` at `y` (Corollary 2 of Theorem 5,
`isNormallyFlatAlongAt'_strictTransform`) and `E' ∪ f⁻¹(B)` has only normal crossings with `W'` at
`y` (Lemma 4, §2, Ch. IV, itself: `DatumI.Raw.hasOnlyNormalCrossingsWithAt_transform_of_resolvedAt_localized`
of `Hironaka/Ch4/Preparation.lean` applies Lemma 4,
`MonoidalTransformation.hasOnlyNormalCrossingsWith_strictTransform_and_inter_exceptional`, to the open
neighbourhood of `x` on which its hypotheses hold, the implicit localization of the citation; its conclusion
also gives that `W'` is simple at `y`).

Deviation from the paper (gap filled): the paper cites the two results, which are statements about one
monoidal transformation, for the whole succession; Lean applies them to the successive monoidal
transformations of the succession (`composite_image_S_subset`).  Lean proves the case distinction, the
density of `W − B` in `W` from `U` (needed for Corollary 2), the restriction to an open neighbourhood of `x` on
which Lemma 4 applies as stated (the paper's citation implicitly localizes: `W` simple at `x`, `E` with only
normal crossings with `W` at `x`, hence near `x`, and the datum resolved only at `x`, not on `X`), and the
simplicity of `W'` (from the normal crossings with `W'`). -/
theorem _root_.Hironaka.MonoidalTransformation.image_unresolvedSet_transform_subset [Hironaka.HironakaCitedResults.{u}] {N n : ℕ}
    {B : Subscheme X} {ℜ : DatumI.Raw X} (h : IsGoodDatumI N n X ℜ) {U : Set X} (hU : ℜ.IsOpenRestriction U)
    (hB : ℜ.IsPermissibleOpen U B) (t : MonoidalTransformation X B) :
    t.f.base '' (ℜ.transform t).unresolvedSet ⊆ ℜ.unresolvedSet := by
  rintro _ ⟨y, ⟨hyW, hyres⟩, rfl⟩
  have hyW0 : t.f.base y ∈ ℜ.W.pts := t.pts_strictTransform_subset _ hyW
  refine ⟨hyW0, fun hres => hyres ?_⟩
  by_cases hyE : y ∈ t.exceptional.pts
  · -- the point lies over the center
    have hxB : t.f.base y ∈ B.pts := by
      rw [MonoidalTransformation.pts_exceptional] at hyE
      exact hyE
    obtain ⟨hXamb, hℜ, -⟩ := h
    have := hXamb.1
    have := hXamb.2.2.1
    have hX := hXamb.2.1
    have hBne : B ≠ Subscheme.empty := fun hE => by
      have h2 := congrArg Subscheme.pts hE
      rw [h2, Subscheme.pts_empty] at hxB
      exact hxB
    obtain ⟨hBns, hBirr⟩ := hB.1.1.resolve_left hBne
    have hdense : ℜ.W.pts ⊆ closure (ℜ.W.pts \ B.pts) := by
      obtain ⟨⟨U₀, -, hUeq⟩, hdU, -⟩ := hU
      intro w hw
      refine closure_mono ?_ (hdU hw)
      intro u hu
      exact ⟨(hUeq ▸ hu : u ∈ U₀ ∩ ℜ.W.pts).2, fun huB => (hB.2 huB).2 hu⟩
    have hNF : ∀ j, Subscheme.IsNormallyFlatAlongAt' (Subscheme.strictTransform t (ℜ.V j))
        (Subscheme.strictTransform t ℜ.W) y := fun j =>
      isNormallyFlatAlongAt'_strictTransform hXamb.2.2.1 hX (ℜ.V j) ℜ.W B (hℜ.2.2.2.2 j)
        (DatumI.Raw.IsPermissible.isContainedIn_W hB.1) hBns hBirr hdense t _ hxB hres.1
        (hres.2.1 j) y hyW rfl
    have hnc := DatumI.Raw.hasOnlyNormalCrossingsWithAt_transform_of_resolvedAt_localized hXamb.2.2.1
      hX hℜ hB.1 t hxB hres hyW rfl
    have hX' := (t.isNonsingular_and_isNonsingular_exceptional hX hBns).1
    exact ⟨Subscheme.isSimpleAt_of_hasOnlyNormalCrossingsWithAt (hX' y) hyW hnc, hNF, hnc⟩
  · exact DatumI.Raw.resolvedAt_transform_of_notMem_exceptional h.2.1 t hyE hres

/-- p. 294: "Since `f_i : X_{i+1} → X_i` is a permissible succession of monoidal transformations of `X_i` for `ℜ_i`, we have `f_i(S(ℜ_{i+1})) ⊆ S(ℜ_i)`."  Closed case: strict transforms lie over the subscheme.  Open case: induction on the succession from the one-step statement
`MonoidalTransformation.image_unresolvedSet_transform_subset` (which applies Lemma 4 itself, `lem:IV.2-4`, on a
neighbourhood of the point: `DatumI.Raw.hasOnlyNormalCrossingsWithAt_transform_of_resolvedAt_localized` of
Preparation.lean). -/
theorem composite_image_S_subset [Hironaka.HironakaCitedResults.{u}] {N n : ℕ} (s : MonoidalSuccession X Y)
    {ℜ : DatumI.Raw X} {r : Restriction X} (h : IsGoodDatumI N n X ℜ) (hr : r.IsFor ℜ)
    (hs : r.IsPermissibleSucc s ℜ) :
    s.composite.base '' S (s.transformI ℜ) (r.transformSucc s) ⊆ S ℜ r := by
  cases r with
  | closed F =>
    rintro _ ⟨y, ⟨hyW, hyF⟩, rfl⟩
    rw [MonoidalSuccession.transformI_W] at hyW
    exact ⟨s.pts_strictTransform_subset _ hyW, s.pts_strictTransform_subset _ hyF⟩
  | opn U =>
    induction s with
    | nil X => rintro _ ⟨y, hy, rfl⟩; exact hy
    | cons B t rest ih =>
      obtain ⟨h', hU'⟩ := IsGoodDatumI.transform_open h hr hs.1 t
      rintro _ ⟨y, hy, rfl⟩
      have := ih h' (DatumI.Raw.transformOpen t U) hU' hs.2 ⟨y, hy, rfl⟩
      exact MonoidalTransformation.image_unresolvedSet_transform_subset h hr hs.1 t
        ⟨_, this, rfl⟩

/-- `S(ℜ)` lies in the principal subscheme `W`. -/
theorem S_subset_pts_W {ℜ : DatumI.Raw X} {r : Restriction X} : S ℜ r ⊆ ℜ.W.pts := by
  cases r with
  | closed F => exact Set.inter_subset_left
  | opn U => exact fun x hx => hx.1

/-- If `S(ℜ) = ∅`, the empty succession is an effective modification. -/
theorem isEffectiveModification_nil {N : ℕ} {ℜ : DatumI.Raw X} {r : Restriction X}
    (hS : S ℜ r = ∅) : IsEffectiveModification N ℜ r (MonoidalSuccession.nil X) := by
  have h : S ((MonoidalSuccession.nil X).transformI ℜ)
      (r.transformSucc (MonoidalSuccession.nil X)) = ∅ := by
    cases r <;> exact hS
  have h2 : S ℜ (r.transformSucc (MonoidalSuccession.nil X)) = ∅ := h
  refine ⟨by cases r <;> trivial, ?_, ?_, ?_⟩ <;> simp [h2]

/-- A stage of the recursion defining the sequence of effective modifications of the proof of the consequence of Lemma (AB.1): an ambient scheme of dimension `N` with a datum with `dim W ≤ n` and a restriction of the given kind. -/
structure EffectiveStage (N n : ℕ) (k : Prop) where
  /-- The scheme `X_i`. -/
  X : Scheme.{u}
  /-- The datum `ℜ_i`. -/
  ℜ : DatumI.Raw X
  /-- The restriction `F_i`, resp. `U_i`. -/
  r : Restriction X
  /-- `X_i` is ambient of dimension `N` and `ℜ_i` is a datum with `dim W_i ≤ n`. -/
  good : IsGoodDatumI N n X ℜ
  /-- `r` is a restriction for `ℜ`. -/
  isFor : r.IsFor ℜ
  /-- `r` has the given kind. -/
  kind : r.IsClosedKind ↔ k

/-- If `S(ℜ)` is nonempty, `W` is nonempty and `ℜ.n = n'` for a natural number `n' ≤ n`. -/
theorem exists_natCast_eq_n_of_S_ne_empty {N n : ℕ} {ℜ : DatumI.Raw X} {r : Restriction X}
    (h : IsGoodDatumI N n X ℜ) (hS : S ℜ r ≠ ∅) : ∃ n' : ℕ, ℜ.n = (n' : WithBot ℕ∞) ∧ n' ≤ n := by
  obtain ⟨x, hx⟩ := Set.nonempty_iff_ne_empty.mpr hS
  obtain ⟨z, -⟩ := Subscheme.exists_ι_eq_of_mem_pts ℜ.W (S_subset_pts_W hx)
  have h0 : (0 : WithBot ℕ∞) ≤ ℜ.W.dim :=
    (ringKrullDim_nonneg_of_nontrivial (R := ℜ.W.toScheme.presheaf.stalk z)).trans
      (LocSucc.dimAt_le_dim z)
  have hne : ℜ.n ≠ ⊥ := by
    intro hb
    have : ℜ.W.dim = ⊥ := hb
    rw [this] at h0
    exact absurd h0 (by simp)
  obtain ⟨m, hm, hmN⟩ := LocSucc.exists_nat_of_le hne h.2.2
  exact ⟨m, hm, hmN⟩

/-- The effectiveness hypothesis of the consequence of Lemma (AB.1). -/
def HasEffectiveModifications (N n : ℕ) (k : Prop) : Prop :=
  ∀ (X' : Scheme.{u}), IsAmbient X' N → ∀ (ℜ' : DatumI.Raw X'), ℜ'.IsDatum →
    ∀ r' : Restriction X', r'.IsFor ℜ' → (r'.IsClosedKind ↔ k) →
    ∀ n' : ℕ, n' ≤ n → ℜ'.n = (n' : WithBot ℕ∞) →
      ∃ (Y : Scheme.{u}) (f : MonoidalSuccession X' Y), IsEffectiveModification N ℜ' r' f

open Classical in
/-- The effective modification chosen at a stage: the empty succession if `S(ℜ) = ∅` ("if that subscheme is empty … we stop"), and otherwise the succession given by the hypothesis `heff` for `n' = dim W`. -/
noncomputable def EffectiveStage.step {N n : ℕ} {k : Prop} (heff : HasEffectiveModifications.{u} N n k)
    (st : EffectiveStage.{u} N n k) :
    Σ' (Y : Scheme.{u}) (f : MonoidalSuccession st.X Y),
      IsEffectiveModification N st.ℜ st.r f :=
  if hS : S st.ℜ st.r = ∅ then ⟨st.X, MonoidalSuccession.nil st.X, isEffectiveModification_nil hS⟩
  else
    let hn := exists_natCast_eq_n_of_S_ne_empty st.good hS
    let hex := heff st.X st.good.1 st.ℜ st.good.2.1 st.r st.isFor st.kind
      (Classical.choose hn) (Classical.choose_spec hn).2 (Classical.choose_spec hn).1
    ⟨hex.choose, hex.choose_spec.choose, hex.choose_spec.choose_spec⟩

/-- The next stage: the transform of the datum and restriction by the chosen effective modification. -/
noncomputable def EffectiveStage.next [Hironaka.HironakaCitedResults.{u}] {N n : ℕ} {k : Prop} (heff : HasEffectiveModifications.{u} N n k)
    (st : EffectiveStage.{u} N n k) : EffectiveStage.{u} N n k :=
  let h := st.step heff
  { X := h.1
    ℜ := h.2.1.transformI st.ℜ
    r := st.r.transformSucc h.2.1
    good := (isGoodDatumI_transformI_and_isFor_transformSucc h.2.1 st.good st.isFor h.2.2.1).1
    isFor := (isGoodDatumI_transformI_and_isFor_transformSucc h.2.1 st.good st.isFor h.2.2.1).2
    kind := (Restriction.isClosedKind_transformSucc st.r h.2.1).trans st.kind }

/-- The sequence of stages `(X_i, ℜ_i, r_i)` of the proof of the consequence of Lemma (AB.1). -/
noncomputable def EffectiveStage.seq [Hironaka.HironakaCitedResults.{u}] {N n : ℕ} {k : Prop} (heff : HasEffectiveModifications.{u} N n k)
    (st : EffectiveStage.{u} N n k) : ℕ → EffectiveStage.{u} N n k
  | 0 => st
  | i + 1 => (EffectiveStage.seq heff st i).next heff

/-- The composite of the first `i` chosen effective modifications, a succession from `X_0` to `X_i`. -/
noncomputable def EffectiveStage.pre [Hironaka.HironakaCitedResults.{u}] {N n : ℕ} {k : Prop} (heff : HasEffectiveModifications.{u} N n k)
    (st : EffectiveStage.{u} N n k) : ∀ i, MonoidalSuccession st.X (EffectiveStage.seq heff st i).X
  | 0 => MonoidalSuccession.nil st.X
  | i + 1 => (EffectiveStage.pre heff st i).append ((EffectiveStage.seq heff st i).step heff).2.1

/-- The composite of the first `i` chosen modifications transforms `(ℜ_0, r_0)` into `(ℜ_i, r_i)` and is permissible for `(ℜ_0, r_0)`. -/
theorem EffectiveStage.transformI_pre_and_transformSucc_pre_and_isPermissibleSucc_pre [Hironaka.HironakaCitedResults.{u}] {N n : ℕ} {k : Prop} (heff : HasEffectiveModifications.{u} N n k)
    (st : EffectiveStage.{u} N n k) (i : ℕ) :
    (EffectiveStage.pre heff st i).transformI st.ℜ = (EffectiveStage.seq heff st i).ℜ ∧
    st.r.transformSucc (EffectiveStage.pre heff st i) = (EffectiveStage.seq heff st i).r ∧
    st.r.IsPermissibleSucc (EffectiveStage.pre heff st i) st.ℜ := by
  induction i with
  | zero =>
    refine ⟨rfl, ?_, ?_⟩
    · show st.r.transformSucc (MonoidalSuccession.nil st.X) = st.r
      cases st.r <;> rfl
    · show st.r.IsPermissibleSucc (MonoidalSuccession.nil st.X) st.ℜ
      cases st.r <;> trivial
  | succ i ih =>
    obtain ⟨h1, h2, h3⟩ := ih
    have e1 := MonoidalSuccession.transformI_append (EffectiveStage.pre heff st i)
      ((EffectiveStage.seq heff st i).step heff).2.1 st.ℜ
    have e2 := Restriction.transformSucc_append st.r (EffectiveStage.pre heff st i)
      ((EffectiveStage.seq heff st i).step heff).2.1
    have e3 := Restriction.isPermissibleSucc_append st.r (EffectiveStage.pre heff st i)
      ((EffectiveStage.seq heff st i).step heff).2.1 st.ℜ
    rw [h1] at e1
    rw [h2] at e2
    rw [h2, h1] at e3
    exact ⟨e1, e2, e3.mpr ⟨h3, ((EffectiveStage.seq heff st i).step heff).2.2.1⟩⟩

/-! ### An infinite chain through the points of `S(ℜ_i)` that lift arbitrarily far -/

/-- Generic lemma: an antitone family of nonempty sets, the second of which is finite, has a
common point. -/
theorem exists_forall_mem_of_antitone_finite {β : Type*} (A : ℕ → Set β) (hA : Antitone A)
    (hne : ∀ k, (A k).Nonempty) (hfin : (A 1).Finite) : ∃ y, ∀ k, y ∈ A k := by
  by_contra h
  push Not at h
  choose g hg using h
  set K := hfin.toFinset.sup g
  obtain ⟨y, hy⟩ := hne (K + 1)
  have hy1 : y ∈ A 1 := hA (by omega) hy
  have : g y ≤ K := Finset.le_sup (hfin.mem_toFinset.mpr hy1)
  exact hg y (hA this (hA (Nat.le_succ K) hy))

/-- The points of `S' i` which are images, under the maps `f`, of points of `S' (i + k)`. -/
def deepSet {α : ℕ → Type*} (f : ∀ i, α (i + 1) → α i) (S' : ∀ i, Set (α i)) :
    ℕ → ∀ i, Set (α i)
  | 0, i => S' i
  | k + 1, i => f i '' deepSet f S' k (i + 1)

theorem deepSet_succ_subset {α : ℕ → Type*} (f : ∀ i, α (i + 1) → α i) (S' : ∀ i, Set (α i))
    (hsub : ∀ i, f i '' S' (i + 1) ⊆ S' i) (k : ℕ) :
    ∀ i, deepSet f S' (k + 1) i ⊆ deepSet f S' k i := by
  induction k with
  | zero => exact fun i => hsub i
  | succ k ih => exact fun i => Set.image_mono (ih (i + 1))

theorem deepSet_nonempty {α : ℕ → Type*} (f : ∀ i, α (i + 1) → α i) (S' : ∀ i, Set (α i))
    (hne : ∀ i, (S' i).Nonempty) (k : ℕ) : ∀ i, (deepSet f S' k i).Nonempty := by
  induction k with
  | zero => exact hne
  | succ k ih => exact fun i => (ih (i + 1)).image (f i)

/-- (König-type argument.) If the sets `S' i` are nonempty, `f i '' S' (i + 1) ⊆ S' i` and each `f i '' S' (i + 1)` is finite, there is a sequence `x i ∈ f i '' S' (i + 1)` with `f i (x (i + 1)) = x i`. -/
theorem exists_chain_of_finite_image {α : ℕ → Type*} (f : ∀ i, α (i + 1) → α i)
    (S' : ∀ i, Set (α i)) (hsub : ∀ i, f i '' S' (i + 1) ⊆ S' i) (hne : ∀ i, (S' i).Nonempty)
    (hfin : ∀ i, (f i '' S' (i + 1)).Finite) :
    ∃ x : ∀ i, α i, (∀ i, x i ∈ f i '' S' (i + 1)) ∧ ∀ i, f i (x (i + 1)) = x i := by
  have hanti : ∀ i, Antitone fun k => deepSet f S' k i := fun i =>
    antitone_nat_of_succ_le fun k => deepSet_succ_subset f S' hsub k i
  have hfin' : ∀ i, (deepSet f S' 1 i).Finite := fun i => hfin i
  -- the step
  have hstep : ∀ i (x : α i), (∀ k, x ∈ deepSet f S' k i) →
      ∃ x' : α (i + 1), (∀ k, x' ∈ deepSet f S' k (i + 1)) ∧ f i x' = x := by
    intro i x hx
    obtain ⟨y, hy⟩ := exists_forall_mem_of_antitone_finite
      (fun k => {y | y ∈ deepSet f S' k (i + 1) ∧ f i y = x})
      (fun a b hab y hy => ⟨hanti (i + 1) hab hy.1, hy.2⟩)
      (fun k => by
        obtain ⟨y, hy, hyx⟩ := hx (k + 1)
        exact ⟨y, hy, hyx⟩)
      ((hfin' (i + 1)).subset fun y hy => hy.1)
    exact ⟨y, fun k => (hy k).1, (hy 0).2⟩
  obtain ⟨x0, hx0⟩ := exists_forall_mem_of_antitone_finite (fun k => deepSet f S' k 0) (hanti 0)
    (fun k => deepSet_nonempty f S' hne k 0) (hfin' 0)
  choose g hg1 hg2 using hstep
  let xs : ∀ i, {x : α i // ∀ k, x ∈ deepSet f S' k i} :=
    fun i => Nat.rec (motive := fun i => {x : α i // ∀ k, x ∈ deepSet f S' k i}) ⟨x0, hx0⟩
      (fun i p => ⟨g i p.1 p.2, hg1 i p.1 p.2⟩) i
  refine ⟨fun i => (xs i).1, fun i => (xs i).2 1, fun i => ?_⟩
  exact hg2 i (xs i).1 (xs i).2

end

/-! ### Ring-level facts of Ch. III used in the proof of Lemma (AB.1) -/

/-- Junk values: `τ^{(a)}(J) = 0` for `a > t(J)` (`tau` is a total function). -/
theorem tau_eq_zero_of_t_lt {R : Type u} [CommRing R] [IsRegularLocalRing R] (J : Ideal R)
    {a : ℕ} (ha : t R J < a) : tau R J a = 0 := by
  have hfin := (muSet_finite R J).1
  have hmu : mu R J a = 0 := by
    unfold mu
    have hfin' : (Set.ofPred fun μ => μ ∈ muSet R J).Finite := hfin
    refine Nat.nth_of_card_le hfin' ?_
    have h1 : (muSet R J).ncard = hfin'.toFinset.card := Set.ncard_eq_toFinset_card _ hfin'
    unfold t at ha
    omega
  unfold tau
  refine Nat.sInf_eq_zero.mpr (Or.inl ?_)
  refine ⟨Fin.elim0, fun i => i.elim0, ?_, fun μ hμ ψ hψ => ?_⟩
  · exact Submodule.span_le.mpr (by rintro _ ⟨i, -⟩; exact i.elim0)
  · rw [hmu] at hμ
    obtain rfl : μ = 0 := Nat.le_zero.mp hμ
    have hψ' : ψ ∈ Algebra.adjoin (R ⧸ maximalIdeal R) (↑(Submodule.span (R ⧸ maximalIdeal R)
        (Set.range (Fin.elim0 : Fin 0 → AssocGraded (maximalIdeal R)))) :
        Set (AssocGraded (maximalIdeal R))) := by
      obtain ⟨c, rfl⟩ := hψ
      induction c using Submodule.Quotient.induction_on with
      | H x =>
        have : AssocGraded.ofGrPiece (maximalIdeal R) 0 (Submodule.Quotient.mk x) =
            algebraMap (R ⧸ maximalIdeal R) (AssocGraded (maximalIdeal R))
              (Ideal.Quotient.mk _ x.1) := by
          rfl
        rw [this]
        exact Subalgebra.algebraMap_mem _ _
    constructor
    · intro h
      exact Ideal.subset_span ⟨h, hψ'⟩
    · intro h
      exact (Ideal.span_le.mpr Set.inter_subset_left) h

/-- A ring isomorphism of regular local rings transforms a regular system of parameters into one. -/
theorem mapsRSOP_ringEquiv {R R' : Type u} [CommRing R] [IsRegularLocalRing R] [CommRing R']
    [IsRegularLocalRing R'] (e : R ≃+* R') : RingHom.MapsRSOP (e : R →+* R') := by
  classical
  obtain ⟨s, hs⟩ := (isRegularLocalRing_iff_exists_rsop (R := R)).mp inferInstance |>.2
  refine ⟨s, hs, ?_, e.injective.injOn⟩
  refine ⟨?_, ?_⟩
  · have hmax : (maximalIdeal R).map e = maximalIdeal R' := by
      have : ((maximalIdeal R).map e).IsMaximal :=
        Ideal.map_isMaximal_of_equiv e
      exact IsLocalRing.eq_maximalIdeal this
    rw [Finset.coe_image, ← Ideal.map_span, hs.1, Ideal.map_coe, hmax]
  · rw [Finset.card_image_of_injective _ (show Function.Injective ((e : R →+* R') : R → R') from
    e.injective), ← ringKrullDim_eq_of_ringEquiv e]
    exact hs.2

/-- A ring isomorphism of local rings is residually separable (its residue field map is an
isomorphism). -/
theorem isResiduallySeparable_ringEquiv {R R' : Type u} [CommRing R] [IsRegularLocalRing R]
    [CommRing R'] [IsRegularLocalRing R'] (e : R ≃+* R') [IsLocalHom (e : R →+* R')] :
    RingHom.IsResiduallySeparable (e : R →+* R') := by
  let _ := (ResidueField.map (e : R →+* R')).toAlgebra
  intro k' _ _ _
  have hbij : Function.Bijective (algebraMap (ResidueField R) (ResidueField R')) := by
    refine ⟨(ResidueField.map (e : R →+* R')).injective, fun w => ?_⟩
    obtain ⟨y, rfl⟩ := IsLocalRing.residue_surjective w
    obtain ⟨a, rfl⟩ := e.surjective y
    exact ⟨IsLocalRing.residue R a, ResidueField.map_residue _ _⟩
  let f : ResidueField R' ≃ₐ[ResidueField R] ResidueField R :=
    (AlgEquiv.ofBijective (Algebra.ofId (ResidueField R) (ResidueField R')) hbij).symm
  let g := (Algebra.TensorProduct.congr f (AlgEquiv.refl : k' ≃ₐ[ResidueField R] k')).trans
    (Algebra.TensorProduct.lid (ResidueField R) k')
  exact isReduced_of_injective (g : _ →+* k') g.injective

/-- The characters `ν*`, `t`, `τ*` are invariant under ring isomorphism. -/
theorem nuStar_t_tau_map_ringEquiv [Hironaka.HironakaCitedResults.{u}] {R R' : Type u} [CommRing R] [IsRegularLocalRing R]
    [CommRing R'] [IsRegularLocalRing R'] (e : R ≃+* R') (J : Ideal R) :
    nuStar R' (J.map e) = nuStar R J ∧ t R' (J.map e) = t R J ∧
      ∀ a, tau R' (J.map e) a = tau R J a := by
  have : IsLocalHom (e : R →+* R') := ⟨fun a ha => by simpa using ha.map (e.symm : R' →+* R)⟩
  have hα := mapsRSOP_ringEquiv e
  have hsep := isResiduallySeparable_ringEquiv e
  rw [← Ideal.map_coe e J]
  obtain ⟨ht, hτ, -⟩ := tauStar_map (e : R →+* R') hα hsep J
  have key : ∀ a, 1 ≤ a → tau R' (J.map (e : R →+* R')) a = tau R J a := fun a ha => by
    by_cases h : a ≤ t R J
    · exact hτ a ha h
    · push Not at h
      rw [tau_eq_zero_of_t_lt J h, tau_eq_zero_of_t_lt _ (ht ▸ h)]
  refine ⟨(nuStar_map_eq_of_mapsRSOP _ hα J).symm, ht, fun a => ?_⟩
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · exact key 1 le_rfl
  · exact key a ha

/-! ### Reindexing the comparisons of systems -/

theorem NuStarSystemGT.comp_equiv {X X' : Scheme.{u}} {ι ι' : Type*} (σ : ι ≃ ι')
    {V : ι' → Subscheme X} {x : X} {hx : X.IsSimpleAt x} {V' : ι' → Subscheme X'} {x' : X'}
    {hx' : X'.IsSimpleAt x'} (h : NuStarSystemGT V x hx V' x' hx') :
    NuStarSystemGT (fun j => V (σ j)) x hx (fun j => V' (σ j)) x' hx' :=
  ⟨fun j => h.1 (σ j), by
    obtain ⟨j, hj⟩ := h.2
    exact ⟨σ.symm j, by simpa [nuStarSystemAt] using hj⟩⟩

theorem NuStarSystemEq.comp_equiv {X X' : Scheme.{u}} {ι ι' : Type*} (σ : ι ≃ ι')
    {V : ι' → Subscheme X} {x : X} {hx : X.IsSimpleAt x} {V' : ι' → Subscheme X'} {x' : X'}
    {hx' : X'.IsSimpleAt x'} (h : NuStarSystemEq V x hx V' x' hx') :
    NuStarSystemEq (fun j => V (σ j)) x hx (fun j => V' (σ j)) x' hx' := fun j => h (σ j)

theorem TauStarSystemLT.comp_equiv {X X' : Scheme.{u}} {ι ι' : Type*} (σ : ι ≃ ι')
    {V : ι' → Subscheme X} {x : X} {hx : X.IsSimpleAt x} {V' : ι' → Subscheme X'} {x' : X'}
    {hx' : X'.IsSimpleAt x'} (h : TauStarSystemLT V x hx V' x' hx') :
    TauStarSystemLT (fun j => V (σ j)) x hx (fun j => V' (σ j)) x' hx' :=
  ⟨fun j i => h.1 (σ j) i, by
    obtain ⟨j, i, hj⟩ := h.2
    exact ⟨σ.symm j, i, by simpa [tauStarSystemAt] using hj⟩⟩

/-! ### The scheme-to-ring bridge -/

section Bridge

variable {X : Scheme.{u}} {B : Subscheme X}

/-- Bridge, one step (residual separability).  Let `R' = O_{X',y}` be (by
`MonoidalTransformation.exists_monoidalTransform_stalk`, the isomorphism `e`) the monoidal transform
`s` of `R = O_{X,f(y)}` with center the stalk `B_{f(y)}` of `B`.  If `dim R' = dim R`, i.e.
`dim_y X' = dim_{f(y)} X`, then `R'` is residually separable algebraic over `R`.

* If `f(y) ∈ B`: `B_{f(y)}` is a non-zero prime with regular quotient (`B` non-singular), so
  `dim R' = dim R` is equivalent to `R'` being residually algebraic over `R`
  (`MonoidalTransform.ringKrullDim_eq_iff`: `M'` is maximal, Zariski's lemma).  *Characteristic
  `0` enters only here, in passing from algebraic to separable*: the base `S ∈ 𝔅` of an algebraic
  scheme has residue field of characteristic zero (`charZero_residueField_stalk`: every positive
  integer is a unit of `S`, hence of every local ring of the scheme), so the residue field of
  `R` is perfect (`PerfectField.ofCharZero`) and an algebraic extension of it is separable
  (`Algebra.IsAlgebraic.isSeparable_of_perfectField`).  The paper says "residually algebraic
  (hence, in characteristic zero, residually separable algebraic)".
* If `f(y) ∉ B`: the center is the unit ideal, `R → R'` is bijective
  (`MonoidalTransform.bijective_toRing_of_eq_top`) and the residue field map is surjective, so
  the extension is trivially separable (no characteristic assumption).

The dimension hypothesis is where "`X'` has dimension `N` at the point" is used in the proof of
Lemma (AB.1): `dimAt` does not increase along a succession (`dimAt_le_composite`), so the
dimension `N` at the last point of a succession forces it at all intermediate points. -/
theorem _root_.Hironaka.MonoidalTransformation.isResiduallySeparableAlgebraic_toRing_of_dimAt_eq
    [IsAlgebraicScheme X] (hB : B.IsNonsingular)
    (t : MonoidalTransformation X B) (y : t.X')
    [IsRegularLocalRing (X.presheaf.stalk (t.f.base y))]
    [IsDomain (X.presheaf.stalk (t.f.base y))]
    (hdim : t.X'.dimAt y = X.dimAt (t.f.base y))
    (s : MonoidalTransform (X.presheaf.stalk (t.f.base y)) (B.stalkIdeal (t.f.base y)))
    (e : s.ring ≃+* t.X'.presheaf.stalk y) :
    RingHom.IsResiduallySeparableAlgebraic (R := X.presheaf.stalk (t.f.base y)) (R' := s.ring)
      s.toRing := by
  unfold RingHom.IsResiduallySeparableAlgebraic
  let _ := (ResidueField.map s.toRing).toAlgebra
  by_cases hxB : t.f.base y ∈ B.pts
  · have hP := Subscheme.isPrime_stalkIdeal_of_isNonsingular hB hxB
    have hS := Subscheme.isRegularLocalRing_quotient_of_isNonsingular hB hxB
    have hP0 : B.stalkIdeal (t.f.base y) ≠ ⊥ :=
      (Submodule.ne_bot_iff _).mpr ⟨s.x, s.x_mem, s.x_ne_zero⟩
    have hres : RingHom.IsResiduallyAlgebraic (R := X.presheaf.stalk (t.f.base y))
        (R' := s.ring) s.toRing :=
      (MonoidalTransform.ringKrullDim_eq_iff s hP hP0 hS).mp
        ((ringKrullDim_eq_of_ringEquiv e).trans hdim)
    have := charZero_residueField_stalk X (t.f.base y)
    have : Algebra.IsAlgebraic (ResidueField (X.presheaf.stalk (t.f.base y)))
        (ResidueField s.ring) := hres
    exact Algebra.IsAlgebraic.isSeparable_of_perfectField
  · have hbij := s.bijective_toRing_of_eq_top (Subscheme.stalkIdeal_eq_top_of_notMem_pts hxB)
    refine ⟨fun w => ?_⟩
    obtain ⟨z, rfl⟩ := IsLocalRing.residue_surjective w
    obtain ⟨r, rfl⟩ := hbij.2 z
    have : algebraMap (ResidueField (X.presheaf.stalk (t.f.base y))) (ResidueField s.ring)
        (IsLocalRing.residue _ r) = IsLocalRing.residue _ (s.toRing r) :=
      ResidueField.map_residue _ _
    rw [← this]
    exact isSeparable_algebraMap _

/-- Bridge, one step (permissible centers).  If `B` is a permissible center for a datum `ℜ`, its
stalk at any point is a permissible center (in the sense of Definition 8 of Ch. III) for the
stalk of every member `V_j`, `W` of the system of `ℜ`: `B ⊆ W ⊆ V_j`, `B` is non-singular and the
`V_j` and `W` are normally flat along `B` at the points of `B` (the datum `(E; V, W; B)` is
resolved everywhere), and the stalk of `B` at a point off `B` is the unit ideal (`P = R` is a
permissible center for every ideal). -/
theorem _root_.Hironaka.DatumI.Raw.isPermissibleCenter_stalkIdeal_datumSystem
    {ℜ : DatumI.Raw X} (hB : ℜ.IsPermissible B) (x : X)
    [IsRegularLocalRing (X.presheaf.stalk x)] (j : Fin (ℜ.β + 1)) :
    IsPermissibleCenter (X.presheaf.stalk x) ((datumSystem ℜ j).stalkIdeal x)
      (B.stalkIdeal x) := by
  by_cases hxB : x ∈ B.pts
  · right
    have hBne : B ≠ Subscheme.empty := fun hE => by
      have h2 := congrArg Subscheme.pts hE
      rw [h2, Subscheme.pts_empty] at hxB
      exact hxB
    obtain ⟨hBns, -⟩ := hB.1.resolve_left hBne
    have hcont : B.IsContainedIn (datumSystem ℜ j) := hB.2.1.2.2.2.2 j
    refine ⟨Subscheme.isPrime_stalkIdeal_of_isNonsingular hBns hxB, ?_,
      Subscheme.isRegularLocalRing_quotient_of_isNonsingular hBns hxB, ?_⟩
    · exact Subscheme.stalkIdeal_mono (show datumSystem ℜ j ≤ B from fun U => hcont U) x
    · have hNF : Subscheme.IsNormallyFlatAlongAt' (datumSystem ℜ j) B x := (hB.2.2 x hxB).2.1 j
      exact ((Subscheme.isNormallyFlatAlongAt'_iff _ _ hcont x).mp hNF).2
  · left
    exact Subscheme.stalkIdeal_eq_top_of_notMem_pts hxB

end Bridge

/-- One step of a transform of a datum: the system of the transformed datum is the system of strict
transforms (`β` is unchanged, so no reindexing is needed). -/
theorem datumSystem_transform {X : Scheme.{u}} {B : Subscheme X} (ℜ : DatumI.Raw X)
    (t : MonoidalTransformation X B) (j : Fin (ℜ.β + 1)) :
    datumSystem (ℜ.transform t) j = Subscheme.strictTransform t (datumSystem ℜ j) := by
  refine Fin.lastCases ?_ (fun j => ?_) j
  · show Fin.snoc (α := fun _ => Subscheme t.X') (fun j => Subscheme.strictTransform t (ℜ.V j))
      (Subscheme.strictTransform t ℜ.W) (Fin.last ℜ.β) = _
    rw [Fin.snoc_last]
    simp only [datumSystem, Fin.snoc_last]
  · show Fin.snoc (α := fun _ => Subscheme t.X') (fun j => Subscheme.strictTransform t (ℜ.V j))
      (Subscheme.strictTransform t ℜ.W) j.castSucc = _
    rw [Fin.snoc_castSucc]
    simp only [datumSystem, Fin.snoc_castSucc]

/-- Along a monoidal transformation with a permissible center, ambient schemes of dimension `N`
and data with `dim W ≤ n < N` are preserved. -/
theorem isGoodDatumI_transform_of_isPermissible [Hironaka.HironakaCitedResults.{u}] {N n : ℕ} (hNn : n < N) {X : Scheme.{u}}
    {ℜ : DatumI.Raw X} (h : IsGoodDatumI N n X ℜ) {B : Subscheme X} (hB : ℜ.IsPermissible B)
    (t : MonoidalTransformation X B) : IsGoodDatumI N n t.X' (ℜ.transform t) := by
  obtain ⟨hX, hℜ, hW⟩ := h
  have := hX.1
  have := hX.2.2.1
  have hBX : B.pts ≠ Set.univ := by
    intro hB'
    have hWu : ℜ.W.pts = Set.univ :=
      Set.eq_univ_of_univ_subset (hB' ▸ hB.pts_subset_W)
    have hlt : ℜ.W.dim < X.dim := by
      rw [hX.2.2.2]
      exact lt_of_le_of_lt hW (by exact_mod_cast hNn)
    exact LocSucc.genericPoint_notMem_of_dim_lt hlt (hWu ▸ Set.mem_univ _)
  obtain ⟨h1, h2, h3, h4⟩ := MonoidalTransformation.transform_isAmbient hX.2.1 hB.1 hBX t
  exact ⟨⟨h1, h2, h3, h4.trans hX.2.2.2⟩,
    (DatumI.Raw.transform_isDatum hX.2.1 ℜ hℜ t hB).1,
    (DatumI.Raw.dim_transform_W hX.2.1 ℜ hℜ t hB).1.trans hW⟩

section Padding

variable {X : Scheme.{u}}

/-- The isomorphism between the stalks at equal points. -/
noncomputable def stalkEquivOfEq {p q : X} (h : p = q) : X.presheaf.stalk p ≃+* X.presheaf.stalk q := by
  subst h
  exact RingEquiv.refl _

theorem map_stalkEquivOfEq (V : Subscheme X) {p q : X} (h : p = q) :
    (V.stalkIdeal p).map (stalkEquivOfEq h) = V.stalkIdeal q := by
  subst h
  show Ideal.map (RingEquiv.refl (X.presheaf.stalk p) : _ ≃+* _) _ = _
  rw [← Ideal.map_coe]
  exact Ideal.map_id _

/-- The strict transform of an ideal with center `P = R` is `J R'` (the generators `x⁻ᵛ f` have
`x` a unit); cf. the private `strictTransformIdeal_eq_map_of_eq_top` of Ch. III. -/
theorem strictTransformIdeal_eq_map_toRing_of_eq_top {R : Type u} [CommRing R] [IsRegularLocalRing R]
    [IsDomain R] {P : Ideal R} (hP : P = ⊤) (T : MonoidalTransform R P) (J : Ideal R) :
    strictTransformIdeal T J = J.map T.toRing := by
  subst hP
  refine le_antisymm (Ideal.span_le.mpr ?_) (Ideal.map_le_iff_le_comap.mpr fun f hf => ?_)
  · rintro y ⟨x, hx, f, hf, ν, -, hy⟩
    rw [Ideal.map_top, Ideal.span_singleton_eq_top] at hx
    obtain ⟨w, hw⟩ := hx.pow ν
    rw [← hw] at hy
    have : y = ↑w⁻¹ * T.toRing f := by rw [← hy, ← mul_assoc, Units.inv_mul, one_mul]
    rw [SetLike.mem_coe, this]
    exact Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _ hf)
  · refine Ideal.subset_span ⟨1, by rw [Ideal.map_top, Ideal.span_singleton_one], f, hf, 0,
      by simp, by rw [pow_zero, one_mul]⟩

/-- A monoidal transform with center the unit ideal is isomorphic to the base, compatibly with the
canonical homomorphism. -/
theorem exists_ringEquiv_of_center_eq_top {R : Type u} [CommRing R] [IsRegularLocalRing R]
    [IsDomain R] {c : Ideal R} (hc : c = ⊤) (T : MonoidalTransform R c) :
    ∃ e : T.ring ≃+* R, ∀ r, e (T.toRing r) = r := by
  have hbij := T.bijective_toRing_of_eq_top hc
  refine ⟨(RingEquiv.ofBijective T.toRing hbij).symm, fun r => ?_⟩
  exact (RingEquiv.ofBijective T.toRing hbij).symm_apply_apply r

/-- The monoidal transform of `O_{Z,z}` with center the unit ideal, obtained from the identity
monoidal transformation with empty center (`MonoidalTransformation.idEmpty`), in a form free of
the identification `(idEmpty Z).X' = Z`. -/
theorem exists_unit_center_transform (Z : Scheme.{u}) [IsAlgebraicScheme Z] (z : Z)
    [IsRegularLocalRing (Z.presheaf.stalk z)] [IsDomain (Z.presheaf.stalk z)] :
    ∃ (c : Ideal (Z.presheaf.stalk z)) (T : MonoidalTransform (Z.presheaf.stalk z) c),
      c = ⊤ ∧ RingHom.IsResiduallySeparableAlgebraic T.toRing := by
  have : IsRegularLocalRing (Z.presheaf.stalk ((MonoidalTransformation.idEmpty Z).f.base z)) :=
    ‹IsRegularLocalRing (Z.presheaf.stalk z)›
  have : IsDomain (Z.presheaf.stalk ((MonoidalTransformation.idEmpty Z).f.base z)) :=
    ‹IsDomain (Z.presheaf.stalk z)›
  obtain ⟨T, e0, -⟩ := (MonoidalTransformation.idEmpty Z).exists_monoidalTransform_stalk z
  have hc : Subscheme.empty.stalkIdeal ((MonoidalTransformation.idEmpty Z).f.base z) = ⊤ :=
    Subscheme.stalkIdeal_top_eq _
  exact ⟨_, T, hc, MonoidalTransformation.isResiduallySeparableAlgebraic_toRing_of_dimAt_eq
      (Subscheme.isNonsingular_empty) (MonoidalTransformation.idEmpty Z) z rfl T e0⟩

/-- The trivial (padding) step: a monoidal transform `T` of `O_{Z,z}` with center `O_{Z,z}` which
is an isomorphism, residually separable algebraic, and whose strict transform of an ideal `J` is
`J` (transported along `stalkEquivOfEq`). -/
theorem exists_padding_step (Z : Scheme.{u}) [IsAlgebraicScheme Z] {z p : Z} (hzp : z = p)
    [IsRegularLocalRing (Z.presheaf.stalk z)] [IsDomain (Z.presheaf.stalk z)] :
    ∃ (c : Ideal (Z.presheaf.stalk z)) (T : MonoidalTransform (Z.presheaf.stalk z) c)
      (e : T.ring ≃+* Z.presheaf.stalk p), c = ⊤ ∧
      (∀ J : Ideal (Z.presheaf.stalk z),
        (strictTransformIdeal T J).map e = J.map (stalkEquivOfEq hzp)) ∧
      RingHom.IsResiduallySeparableAlgebraic T.toRing := by
  obtain ⟨c, T, hc, hsep⟩ := exists_unit_center_transform Z z
  obtain ⟨e1, he1⟩ := exists_ringEquiv_of_center_eq_top hc T
  refine ⟨c, T, e1.trans (stalkEquivOfEq hzp), hc, fun J => ?_, hsep⟩
  rw [strictTransformIdeal_eq_map_toRing_of_eq_top hc T J,
    ← Ideal.map_coe (e1.trans (stalkEquivOfEq hzp)), ← Ideal.map_coe (stalkEquivOfEq hzp),
    Ideal.map_map]
  congr 1
  ext r
  simp [he1]

end Padding

section ConsStep

variable {Y : Scheme.{u}} {B : Subscheme Y}

/-- One real step of the chain: for a monoidal transformation `t` with a center `B` and a point `y'`
of `X'` over `y`, the local ring of `X'` at `y'` is a monoidal transform `T` of `O_{Y,y}` with center
`B_y` (`exists_monoidalTransform_stalk`), the stalk of the strict transform of `V` is the strict
transform of the stalk of `V` (`stalkIdeal_strictTransformIdealSheaf_eq_map` at a point of the
center, where `B ⊆ V` is used; the local isomorphism off the center), and `T` is residually
separable algebraic when the local dimensions agree. -/
theorem exists_consStep [IsAlgebraicScheme Y] (hY : Y.IsNonsingular) (hB : B.IsCenter)
    (t : MonoidalTransformation Y B) (y' : t.X') (V : Subscheme Y)
    (hdim : t.X'.dimAt y' = Y.dimAt (t.f.base y'))
    (hBV : t.f.base y' ∈ B.pts → B.IsContainedIn V)
    [IsRegularLocalRing (Y.presheaf.stalk (t.f.base y'))]
    [IsDomain (Y.presheaf.stalk (t.f.base y'))] :
    ∃ (T : MonoidalTransform (Y.presheaf.stalk (t.f.base y')) (B.stalkIdeal (t.f.base y')))
      (e : T.ring ≃+* t.X'.presheaf.stalk y'),
      (Subscheme.strictTransform t V).stalkIdeal y' =
        (strictTransformIdeal T (V.stalkIdeal (t.f.base y'))).map e ∧
      RingHom.IsResiduallySeparableAlgebraic T.toRing := by
  obtain ⟨T, e, he⟩ := t.exists_monoidalTransform_stalk y'
  have hBns := hB.isNonsingular
  refine ⟨T, e, ?_, MonoidalTransformation.isResiduallySeparableAlgebraic_toRing_of_dimAt_eq
    hBns t y' hdim T e⟩
  by_cases hyB : t.f.base y' ∈ B.pts
  · have hBne : B ≠ Subscheme.empty := fun hE => by
      have h2 := congrArg Subscheme.pts hE
      rw [h2, Subscheme.pts_empty] at hyB
      exact hyB
    obtain ⟨-, hBirr⟩ := hB.resolve_left hBne
    obtain ⟨ξ, hξ⟩ := Subscheme.exists_isGenericPoint hBirr
    rw [← MonoidalTransformation.strictTransformIdealSheaf_eq_strictTransform hY hBirr hBns t V
      (hBV hyB)]
    exact Subscheme.stalkIdeal_strictTransformIdealSheaf_eq_map hY hBns t V hξ y' T e he
  · have hyE : y' ∉ t.exceptional.pts := fun h =>
      hyB (MonoidalTransformation.mem_pts_of_mem_exceptional t h)
    have hc : B.stalkIdeal (t.f.base y') = ⊤ := Subscheme.stalkIdeal_eq_top_of_notMem_pts hyB
    rw [MonoidalTransformation.strictTransform_stalkIdeal_of_notMem t V hyE,
      stalkIdeal_totalTransform, strictTransformIdeal_eq_map_toRing_of_eq_top hc T,
      ← Ideal.map_coe e, Ideal.map_map, ← he]
    rfl

end ConsStep

/-! ### The state machine -/

section Chain

/-- The data of the chain of Lemma (AB.1): schemes `X_i`, data `ℜ_i`, successions `f_i`, points
`x_i` over each other, and the index `j_i` of a member of the system of `ℜ_i` (a member `V_j(i)`
with `V_j(i+1)` the strict transform of `V_j(i)` along `f_i`). -/
structure ChainData (N n : ℕ) where
  /-- The schemes `X_i`. -/
  Xs : ℕ → Scheme.{u}
  /-- The data `ℜ_i`. -/
  ℜs : ∀ i, DatumI.Raw (Xs i)
  /-- The successions `f_i : X_{i+1} → X_i`. -/
  fs : ∀ i, MonoidalSuccession (Xs i) (Xs (i + 1))
  /-- The points `x_i`. -/
  x : ∀ i, Xs i
  /-- The index of the chosen member of the system of `ℜ_i`. -/
  jf : ∀ i, Fin ((ℜs i).β + 1)
  hNn : n < N
  hgood : ∀ i, IsGoodDatumI N n (Xs i) (ℜs i)
  hℜs : ∀ i, ℜs (i + 1) = (fs i).transformI (ℜs i)
  hperm : ∀ i, (fs i).IsPermissibleI (ℜs i)
  hx : ∀ i, (fs i).composite.base (x (i + 1)) = x i
  hdim : ∀ i, (Xs i).dimAt (x i) = (N : WithBot ℕ∞)
  hjf : ∀ i, succSystem (fs i) (ℜs i) (jf i) = datumSystem (ℜs (i + 1)) (jf (i + 1))

/-- A state of the machine that runs through the steps of `f_0, f_1, …` one after the other: the
block `i`, the current scheme `Y` (an intermediate scheme of `f_i`), the steps `s` of `f_i` still to
be performed, the transform `ℜ` of `ℜ_i` along the steps performed, and the index of the member of
its system.  The current point is `s.composite (x_{i+1})`. -/
structure State {N n : ℕ} (C : ChainData.{u} N n) where
  /-- The block (`f_i`) the state is in. -/
  i : ℕ
  /-- The current (intermediate) scheme. -/
  Y : Scheme.{u}
  /-- The steps of `f_i` still to be performed. -/
  s : MonoidalSuccession Y (C.Xs (i + 1))
  /-- The transform of `ℜ_i` along the steps performed. -/
  ℜ : DatumI.Raw Y
  /-- The index of the member of the system of `ℜ`. -/
  j : Fin (ℜ.β + 1)
  hℜ : s.transformI ℜ = C.ℜs (i + 1)
  hV : s.strictTransform (datumSystem ℜ j) = datumSystem (C.ℜs (i + 1)) (C.jf (i + 1))
  hperm : s.IsPermissibleI ℜ
  hgood : IsGoodDatumI N n Y ℜ

namespace State

variable {N n : ℕ} {C : ChainData.{u} N n} (σ : State C)

/-- The current point. -/
noncomputable def pt : σ.Y := σ.s.composite.base (C.x (σ.i + 1))

/-- The current local ring. -/
noncomputable abbrev ring : Type u := σ.Y.presheaf.stalk σ.pt

/-- The current ideal: the stalk of the current member of the system. -/
noncomputable def ideal : Ideal σ.ring := (datumSystem σ.ℜ σ.j).stalkIdeal σ.pt

instance : IsRegularLocalRing σ.ring := σ.hgood.1.2.1 σ.pt

instance : IsDomain σ.ring := isDomain_of_isRegularLocalRing σ.ring

/-- The dimension at the current point is `N`: `dimAt` does not increase along a succession and
is `≤ N` on an ambient scheme of dimension `N`. -/
theorem dimAt_pt [Hironaka.HironakaCitedResults.{u}] : σ.Y.dimAt σ.pt = (N : WithBot ℕ∞) := by
  have : IsAlgebraicScheme σ.Y := σ.hgood.1.1
  have h1 : (C.Xs (σ.i + 1)).dimAt (C.x (σ.i + 1)) ≤ σ.Y.dimAt σ.pt :=
    MonoidalSuccession.dimAt_le_composite_of_isAlgebraicScheme σ.s _
  have h2 : σ.Y.dimAt σ.pt ≤ (N : WithBot ℕ∞) :=
    (LocSucc.dimAt_le_dim _).trans σ.hgood.1.2.2.2.le
  exact le_antisymm h2 (C.hdim _ ▸ h1)

/-- The data of one step of the machine from a state `σ`: a monoidal transform `T` of the current
local ring with center `center` (the stalk of the center of the next step of `s`, or the unit ideal
if `s` is exhausted, in which case the step is a padding step), the next state, and the relations
required of a `MonoidalSequence` (the ideal of the next state is the strict transform, the center is
permissible, `T` is residually separable algebraic), together with the block bookkeeping. -/
structure StepData (σ : State C) where
  /-- The center of the monoidal transform. -/
  center : Ideal σ.ring
  /-- The monoidal transform of the current local ring. -/
  T : MonoidalTransform σ.ring center
  /-- The next state. -/
  next : State C
  /-- The identification of the transform with the next local ring. -/
  e : T.ring ≃+* next.ring
  /-- The next ideal is the strict transform. -/
  ideal_eq : next.ideal = (strictTransformIdeal T σ.ideal).map e
  /-- The center is permissible. -/
  perm : IsPermissibleCenter σ.ring σ.ideal center
  /-- The step is residually separable algebraic. -/
  sep : RingHom.IsResiduallySeparableAlgebraic T.toRing
  /-- A real step stays in the block and shortens `s`. -/
  cons_case : σ.s.length ≠ 0 → next.i = σ.i ∧ next.s.length + 1 = σ.s.length
  /-- A padding step passes to the next block. -/
  nil_case : σ.s.length = 0 → next.i = σ.i + 1 ∧
    ∃ e' : next.ring ≃+* (C.Xs (σ.i + 1)).presheaf.stalk (C.x (σ.i + 1)),
      next.ideal.map e' =
        (datumSystem (C.ℜs (σ.i + 1)) (C.jf (σ.i + 1))).stalkIdeal (C.x (σ.i + 1))

/-- Every state admits a step. -/
theorem exists_stepData [Hironaka.HironakaCitedResults.{u}] (σ : State C) : Nonempty (StepData σ) := by
  obtain ⟨i, Y, s, ℜ, j, hℜ, hV, hperm, hgood⟩ := σ
  cases s with
  | nil _ =>
    have hℜ' : ℜ = C.ℜs (i + 1) := hℜ
    subst hℜ'
    have hZ : IsAlgebraicScheme (C.Xs (i + 1)) := hgood.1.1
    have hzp : (C.x (i + 1)) = (C.fs (i + 1)).composite.base (C.x (i + 1 + 1)) :=
      (C.hx (i + 1)).symm
    have : IsRegularLocalRing ((C.Xs (i + 1)).presheaf.stalk (C.x (i + 1))) :=
      hgood.1.2.1 _
    have : IsDomain ((C.Xs (i + 1)).presheaf.stalk (C.x (i + 1))) :=
      isDomain_of_isRegularLocalRing _
    obtain ⟨c, T, e, hc, hmap, hsep⟩ := exists_padding_step (C.Xs (i + 1)) hzp
    have hVj : datumSystem (C.ℜs (i + 1)) j = datumSystem (C.ℜs (i + 1)) (C.jf (i + 1)) := hV
    refine ⟨⟨c, T, ⟨i + 1, C.Xs (i + 1), C.fs (i + 1), C.ℜs (i + 1), j, (C.hℜs (i + 1)).symm,
        by rw [hVj]; exact C.hjf (i + 1), C.hperm (i + 1), C.hgood (i + 1)⟩, e, ?_, Or.inl hc, hsep,
        fun h => absurd rfl h, fun _ => ⟨rfl, ?_⟩⟩⟩
    · show (datumSystem (C.ℜs (i + 1)) j).stalkIdeal
        ((C.fs (i + 1)).composite.base (C.x (i + 1 + 1))) =
        (strictTransformIdeal T ((datumSystem (C.ℜs (i + 1)) j).stalkIdeal (C.x (i + 1)))).map e
      rw [hmap, map_stalkEquivOfEq]
    · refine ⟨stalkEquivOfEq (C.hx (i + 1)), ?_⟩
      show Ideal.map (stalkEquivOfEq (C.hx (i + 1))) ((datumSystem (C.ℜs (i + 1)) j).stalkIdeal
        ((C.fs (i + 1)).composite.base (C.x (i + 1 + 1)))) = _
      rw [hVj]
      exact map_stalkEquivOfEq _ (C.hx (i + 1))
  | cons B t rest =>
    have hY : IsAlgebraicScheme Y := hgood.1.1
    have hYns : Y.IsNonsingular := hgood.1.2.1
    have hℜ' : rest.transformI (ℜ.transform t) = C.ℜs (i + 1) := hℜ
    have hV' : rest.strictTransform (datumSystem (ℜ.transform t) j) =
        datumSystem (C.ℜs (i + 1)) (C.jf (i + 1)) := by
      rw [datumSystem_transform]
      exact hV
    let nxt : State C := ⟨i, t.X', rest, ℜ.transform t, j, hℜ', hV', hperm.2,
      isGoodDatumI_transform_of_isPermissible C.hNn hgood hperm.1 t⟩
    have h1 : t.X'.dimAt (rest.composite.base (C.x (i + 1))) = (N : WithBot ℕ∞) :=
      nxt.dimAt_pt
    have h2 : Y.dimAt (t.f.base (rest.composite.base (C.x (i + 1)))) = (N : WithBot ℕ∞) :=
      State.dimAt_pt (⟨i, Y, MonoidalSuccession.cons B t rest, ℜ, j, hℜ, hV, hperm, hgood⟩ :
        State C)
    have : IsRegularLocalRing (Y.presheaf.stalk (t.f.base (rest.composite.base (C.x (i + 1))))) :=
      hYns _
    have : IsDomain (Y.presheaf.stalk (t.f.base (rest.composite.base (C.x (i + 1))))) :=
      isDomain_of_isRegularLocalRing _
    obtain ⟨T, e, hideal, hsep⟩ := exists_consStep hYns hperm.1.1 t
      (rest.composite.base (C.x (i + 1))) (datumSystem ℜ j) (h1.trans h2.symm)
      (fun _ => hperm.1.2.1.2.2.2.2 j)
    refine ⟨⟨B.stalkIdeal (t.f.base (rest.composite.base (C.x (i + 1)))), T, nxt, e, ?_,
      DatumI.Raw.isPermissibleCenter_stalkIdeal_datumSystem hperm.1
        (t.f.base (rest.composite.base (C.x (i + 1)))) j, hsep,
      fun _ => ⟨rfl, rfl⟩, fun h => absurd h (Nat.succ_ne_zero _)⟩⟩
    show (datumSystem (ℜ.transform t) j).stalkIdeal (rest.composite.base (C.x (i + 1))) =
      (strictTransformIdeal T ((datumSystem ℜ j).stalkIdeal
        (t.f.base (rest.composite.base (C.x (i + 1)))))).map e
    rw [datumSystem_transform]
    exact hideal

/-- A chosen step from `σ`. -/
noncomputable def step [Hironaka.HironakaCitedResults.{u}] (σ : State C) : StepData σ := Classical.choice (exists_stepData σ)

/-- The next state of the machine. -/
noncomputable def nextState [Hironaka.HironakaCitedResults.{u}] (σ : State C) : State C := (step σ).next

/-- The initial state: the first step of `f_0`. -/
noncomputable def init (C : ChainData.{u} N n) : State C :=
  ⟨0, C.Xs 0, C.fs 0, C.ℜs 0, C.jf 0, (C.hℜs 0).symm, C.hjf 0, C.hperm 0, C.hgood 0⟩

/-- The run of the machine. -/
noncomputable def seq [Hironaka.HironakaCitedResults.{u}] (C : ChainData.{u} N n) : ℕ → State C
  | 0 => init C
  | m + 1 => nextState (seq C m)

/-- Iterating the machine from a given state. -/
noncomputable def run [Hironaka.HironakaCitedResults.{u}] : ℕ → State C → State C
  | 0, σ => σ
  | m + 1, σ => run m (nextState σ)

/-- The run of the machine is the iteration of the step. -/
theorem seq_add [Hironaka.HironakaCitedResults.{u}] (C : ChainData.{u} N n) (m k : ℕ) : seq C (m + k) = run k (seq C m) := by
  induction k generalizing m with
  | zero => rfl
  | succ k ih =>
    rw [show m + (k + 1) = (m + 1) + k by omega, ih]
    rfl

/-- The block index never decreases. -/
theorem i_nextState_le [Hironaka.HironakaCitedResults.{u}] (σ : State C) : σ.i ≤ (nextState σ).i := by
  by_cases h : σ.s.length = 0
  · exact ((step σ).nil_case h).1 ▸ Nat.le_succ _
  · exact ((step σ).cons_case h).1.ge

/-- The block index of the run is monotone. -/
theorem i_seq_mono [Hironaka.HironakaCitedResults.{u}] (C : ChainData.{u} N n) : Monotone fun m => (seq C m).i :=
  monotone_nat_of_le_succ fun m => i_nextState_le (seq C m)

/-- From any state the machine reaches, after finitely many steps, a state with no step left in
the same block. -/
theorem exists_run_nil [Hironaka.HironakaCitedResults.{u}] (ℓ : ℕ) : ∀ σ : State C, σ.s.length = ℓ →
    ∃ m, (run m σ).s.length = 0 ∧ (run m σ).i = σ.i := by
  induction ℓ with
  | zero => exact fun σ h => ⟨0, h, rfl⟩
  | succ ℓ ih =>
    intro σ h
    obtain ⟨hi, hl⟩ := (step σ).cons_case (by omega)
    have hl' : (nextState σ).s.length + 1 = σ.s.length := hl
    obtain ⟨m, hm0, hmi⟩ := ih (nextState σ) (by omega)
    exact ⟨m + 1, hm0, hmi.trans hi⟩

/-- Every block is eventually exhausted. -/
theorem exists_seq_nil [Hironaka.HironakaCitedResults.{u}] (C : ChainData.{u} N n) (i : ℕ) :
    ∃ m, (seq C m).s.length = 0 ∧ (seq C m).i = i := by
  induction i with
  | zero =>
    obtain ⟨m, h0, hi⟩ := exists_run_nil (seq C 0).s.length (seq C 0) rfl
    exact ⟨0 + m, by rw [seq_add]; exact h0, by rw [seq_add]; exact hi⟩
  | succ i ih =>
    obtain ⟨m, h0, hi⟩ := ih
    have hi1 : (seq C (m + 1)).i = i + 1 := by
      have := ((step (seq C m)).nil_case h0).1
      rw [hi] at this
      exact this
    obtain ⟨m', h0', hi'⟩ := exists_run_nil (seq C (m + 1)).s.length (seq C (m + 1)) rfl
    exact ⟨m + 1 + m', by rw [seq_add]; exact h0', by rw [seq_add]; exact hi'.trans hi1⟩

/-- The position at which block `i` is exhausted. -/
noncomputable def blockEnd [Hironaka.HironakaCitedResults.{u}] (C : ChainData.{u} N n) (i : ℕ) : ℕ := Nat.find (exists_seq_nil C i)

/-- Block `blockEnd C i` is exhausted at position `blockEnd C i`. -/
theorem blockEnd_spec [Hironaka.HironakaCitedResults.{u}] (C : ChainData.{u} N n) (i : ℕ) :
    (seq C (blockEnd C i)).s.length = 0 ∧ (seq C (blockEnd C i)).i = i :=
  Nat.find_spec (exists_seq_nil C i)

/-- The blocks are exhausted in order. -/
theorem blockEnd_lt [Hironaka.HironakaCitedResults.{u}] (C : ChainData.{u} N n) (i : ℕ) : blockEnd C i < blockEnd C (i + 1) := by
  by_contra h
  push Not at h
  have h1 := i_seq_mono C h
  have h2 := (blockEnd_spec C i).2
  have h3 := (blockEnd_spec C (i + 1)).2
  simp only at h1
  omega

/-- The position at which the machine starts block `i`: `0` for `i = 0` and one step after the
exhaustion of block `i - 1` otherwise. -/
noncomputable def startPos [Hironaka.HironakaCitedResults.{u}] (C : ChainData.{u} N n) : ℕ → ℕ
  | 0 => 0
  | i + 1 => blockEnd C i + 1

/-- The block start positions are strictly increasing. -/
theorem startPos_strictMono [Hironaka.HironakaCitedResults.{u}] (C : ChainData.{u} N n) : StrictMono (startPos C) := by
  refine strictMono_nat_of_lt_succ fun i => ?_
  cases i with
  | zero => simp [startPos]
  | succ i => exact Nat.succ_lt_succ (blockEnd_lt C i)

/-- At the exhaustion of block `i` the next state is the start of block `i + 1`, whose ring is
(isomorphic to) the stalk at `x_{i+1}` and whose ideal is the stalk of the member of the system. -/
theorem nextState_nil_spec [Hironaka.HironakaCitedResults.{u}] (σ : State C) (k : ℕ) (hi : σ.i = k) (h0 : σ.s.length = 0) :
    ∃ e : (nextState σ).ring ≃+* (C.Xs (k + 1)).presheaf.stalk (C.x (k + 1)),
      (nextState σ).ideal.map e =
        (datumSystem (C.ℜs (k + 1)) (C.jf (k + 1))).stalkIdeal (C.x (k + 1)) := by
  subst hi
  obtain ⟨-, e', he'⟩ := (step σ).nil_case h0
  exact ⟨e', he'⟩

/-- The ring and the ideal at the start of block `i` are the stalk at `x_i` and the stalk of the
member of the system. -/
theorem startPos_spec [Hironaka.HironakaCitedResults.{u}] (C : ChainData.{u} N n) (i : ℕ) :
    ∃ e : (seq C (startPos C i)).ring ≃+* (C.Xs i).presheaf.stalk (C.x i),
      (seq C (startPos C i)).ideal.map e =
        (datumSystem (C.ℜs i) (C.jf i)).stalkIdeal (C.x i) := by
  cases i with
  | zero =>
    refine ⟨stalkEquivOfEq (C.hx 0), ?_⟩
    exact map_stalkEquivOfEq _ (C.hx 0)
  | succ i =>
    obtain ⟨h0, hi⟩ := blockEnd_spec C i
    exact nextState_nil_spec (seq C (blockEnd C i)) i hi h0

/-- The infinite sequence of monoidal transforms of local rings produced by the machine. -/
noncomputable def toMonoidalSequence [Hironaka.HironakaCitedResults.{u}] (C : ChainData.{u} N n) : MonoidalSequence.{u} where
  ring m := (seq C m).ring
  commRing _ := inferInstance
  isRegularLocalRing _ := inferInstance
  isDomain _ := inferInstance
  ideal m := (seq C m).ideal
  center m := (step (seq C m)).center
  transform m := (step (seq C m)).T
  equiv m := (step (seq C m)).e
  ideal_succ m := (step (seq C m)).ideal_eq

/-- The centers of the sequence are permissible. -/
theorem toMonoidalSequence_isPermissible [Hironaka.HironakaCitedResults.{u}] (C : ChainData.{u} N n) :
    (toMonoidalSequence C).IsPermissible := fun m => (step (seq C m)).perm

/-- The steps of the sequence are residually separable algebraic. -/
theorem toMonoidalSequence_isResiduallySeparableAlgebraic [Hironaka.HironakaCitedResults.{u}] (C : ChainData.{u} N n) :
    (toMonoidalSequence C).IsResiduallySeparableAlgebraic := fun m => (step (seq C m)).sep

/-- The chain for one member of the system: a sequence of monoidal transforms of local rings whose
ring and ideal at the positions `startPos C i` are the stalk at `x_i` and the stalk of the member of
the system of `ℜ_i`. -/
theorem exists_monoidalSequence_of_chainData [Hironaka.HironakaCitedResults.{u}] (C : ChainData.{u} N n) :
    ∃ (S : MonoidalSequence.{u}) (a : ℕ → ℕ), StrictMono a ∧ S.IsPermissible ∧
      S.IsResiduallySeparableAlgebraic ∧
      ∀ i, ∃ e : S.ring (a i) ≃+* (C.Xs i).presheaf.stalk (C.x i),
        (S.ideal (a i)).map e = (datumSystem (C.ℜs i) (C.jf i)).stalkIdeal (C.x i) :=
  ⟨toMonoidalSequence C, startPos C, startPos_strictMono C, toMonoidalSequence_isPermissible C,
    toMonoidalSequence_isResiduallySeparableAlgebraic C, startPos_spec C⟩

end State

end Chain

/-- Bridge, assembled.  Let `X_i` be a sequence of ambient schemes of dimension `N` with permissible
successions `f_i : X_{i+1} → X_i` for data `ℜ_i`, and `x_i ∈ X_i` points of dimension `N` with
`f_i(x_{i+1}) = x_i`.  For every member `V_j(i) = σ_i(j)` of the systems, the local rings of
the intermediate schemes of the `f_i` at the points over `x_i` form one infinite sequence of
monoidal transforms (`MonoidalSequence`) satisfying the hypotheses of Theorem 4 of Ch. III, whose
ring and ideal at the position `a j i` are the stalk at `x_i` and the stalk of `V_j(i)`.

Construction (see `State`): a machine running through the steps of `f_0, f_1, …` one after the
other; each step is `exists_stepData`: a real step of `f_i` (`exists_consStep`: the monoidal
transform of `O_{Y,y}` given by `MonoidalTransformation.exists_monoidalTransform_stalk`, the stalk
of the strict transform by `Subscheme.stalkIdeal_strictTransformIdealSheaf_eq_map` at a point of
the center and the local isomorphism off the center, the center permissible
(`DatumI.Raw.isPermissibleCenter_stalkIdeal_datumSystem`), residually separable algebraic
(`MonoidalTransformation.isResiduallySeparableAlgebraic_toRing_of_dimAt_eq`; the dimension is `N` at
all intermediate points since `dimAt` does not increase along a succession,
`State.dimAt_pt`)) or, when the steps of `f_i` are exhausted, a padding step passing to `f_{i+1}`
(`exists_padding_step`: the identity transformation with empty center, "the monoidal transformation
with the empty center is the identity", p. 295).  The invariants carried by a state (the datum is
the transform of `ℜ_i`, it is a good datum, the remaining steps are permissible, the current
member of the system is carried to the member of `ℜ_{i+1}`) are exactly those needed for the next
step.

Deviation from the paper (gap filled): the paper does not construct this sequence ("as is easily
seen", p. 294).  The padding steps make the sequence infinite as Theorem 4 requires (finite
sequences are continued by trivial monoidal transforms, Ch. III).

The same single-step facts, applied along the finite initial segment `g_s` of a tower, prove
`Standing.nuStarSystemAt_le_and_tauStarSystemAt_ge_of_nuStarSystemEq` (Theorem 3 of Ch. III step
by step), so the single-step facts are shared. -/
theorem exists_monoidalSequence_of_chain [Hironaka.HironakaCitedResults.{u}] {N n : ℕ} (hNn : n < N) {ι : Type}
    (Xs : ℕ → Scheme.{u})
    (ℜs : ∀ i, DatumI.Raw (Xs i)) (fs : ∀ i, MonoidalSuccession (Xs i) (Xs (i + 1)))
    (hgood : ∀ i, IsGoodDatumI N n (Xs i) (ℜs i))
    (hℜs : ∀ i, ℜs (i + 1) = (fs i).transformI (ℜs i))
    (hperm : ∀ i, (fs i).IsPermissibleI (ℜs i))
    (σ : ∀ i, ι ≃ Fin ((ℜs i).β + 1))
    (hσ : ∀ i j, succSystem (fs i) (ℜs i) (σ i j) = datumSystem (ℜs (i + 1)) (σ (i + 1) j))
    (x : ∀ i, Xs i) (hx : ∀ i, (fs i).composite.base (x (i + 1)) = x i)
    (hdim : ∀ i, (Xs i).dimAt (x i) = (N : WithBot ℕ∞)) :
    ∃ (S : ι → MonoidalSequence.{u}) (a : ι → ℕ → ℕ), (∀ j, StrictMono (a j)) ∧
      (∀ j, (S j).IsPermissible) ∧ (∀ j, (S j).IsResiduallySeparableAlgebraic) ∧
      ∀ i j, ∃ e : (S j).ring (a j i) ≃+* (Xs i).presheaf.stalk (x i),
        ((S j).ideal (a j i)).map e = (datumSystem (ℜs i) (σ i j)).stalkIdeal (x i) := by
  have key := fun j => State.exists_monoidalSequence_of_chainData
    (⟨Xs, ℜs, fs, x, fun i => σ i j, hNn, hgood, hℜs, hperm, hx, hdim, fun i => hσ i j⟩ :
      ChainData.{u} N n)
  choose S a ha hp hs he using key
  exact ⟨S, a, ha, hp, hs, fun i j => he j i⟩

/-- The contradiction of the proof of Lemma (AB.1): "As is easily seen, these inequalities for all
non-negative integers `i` lead to a contradiction by virtue of Theorem 4, §5, Ch. III."

Proof: the bridge gives, for every member `j` of the systems, a sequence of monoidal transforms
satisfying the hypotheses of Theorem 4 (`MonoidalSequence.exists_stationary`), whose rings and
ideals at the positions `a i` are the stalks at `x_i` of the members of the system.  Theorem 4
makes `ν*`, `t` and `τ^{(k)}` (`k ≤ t`) of the `j`-th ideal constant from some position on, for
each of the finitely many `j`; taking `i` so large that `a i` and `a (i+1)` are beyond all these
positions, `ν*_{x_i}(V_j) = ν*_{x_{i+1}}(V_j')` and `τ*_{x_i}(V_j) = τ*_{x_{i+1}}(V_j')` for all
`j`, which excludes both (a) and (b) at `x_{i+1}`.  (Theorem 3 of Ch. III is not needed here:
Theorem 4 already covers the whole sequence.)

Deviation from the paper (gap filled): the paper says "As is easily seen".  Lean needs (i) the
bridge; (ii) the comparison of `τ^{(k)}` for all `k ≥ 1`, whereas Theorem 4 only gives `k ≤ t`: for
`k > t` both sides are `0` (`tau_eq_zero_of_t_lt`); (iii) the invariance of `ν*`, `t`, `τ*` under
ring isomorphism (`nuStar_t_tau_map_ringEquiv`); (iv) that `ι` is finite, so that one position
works for all `j`. -/
theorem false_of_forall_nuStarSystemGT_or_tauStarSystemLT [Hironaka.HironakaCitedResults.{u}] {N n : ℕ} (hNn : n < N) {ι : Type}
    [Finite ι]
    (Xs : ℕ → Scheme.{u}) (ℜs : ∀ i, DatumI.Raw (Xs i))
    (fs : ∀ i, MonoidalSuccession (Xs i) (Xs (i + 1)))
    (hgood : ∀ i, IsGoodDatumI N n (Xs i) (ℜs i))
    (hℜs : ∀ i, ℜs (i + 1) = (fs i).transformI (ℜs i))
    (hperm : ∀ i, (fs i).IsPermissibleI (ℜs i))
    (σ : ∀ i, ι ≃ Fin ((ℜs i).β + 1))
    (hσ : ∀ i j, succSystem (fs i) (ℜs i) (σ i j) = datumSystem (ℜs (i + 1)) (σ (i + 1) j))
    (x : ∀ i, Xs i) (hx : ∀ i, (fs i).composite.base (x (i + 1)) = x i)
    (hdim : ∀ i, (Xs i).dimAt (x i) = (N : WithBot ℕ∞))
    (himp : ∀ i (p : Xs i), (fs i).composite.base (x (i + 1)) = p →
      ∀ (hx' : (Xs (i + 1)).IsSimpleAt (x (i + 1))) (hx0 : (Xs i).IsSimpleAt p),
      NuStarSystemGT (fun j => datumSystem (ℜs i) (σ i j)) p hx0
          (fun j => succSystem (fs i) (ℜs i) (σ i j)) (x (i + 1)) hx' ∨
        (NuStarSystemEq (fun j => datumSystem (ℜs i) (σ i j)) p hx0
            (fun j => succSystem (fs i) (ℜs i) (σ i j)) (x (i + 1)) hx' ∧
          TauStarSystemLT (fun j => datumSystem (ℜs i) (σ i j)) p hx0
            (fun j => succSystem (fs i) (ℜs i) (σ i j)) (x (i + 1)) hx')) : False := by
  classical
  obtain ⟨S, a, ha, hSperm, hSsep, hSe⟩ :=
    exists_monoidalSequence_of_chain hNn Xs ℜs fs hgood hℜs hperm σ hσ x hx hdim
  choose α₀ hα₀pos hν ht hτ using fun j => (S j).exists_stationary (hSperm j) (hSsep j)
  obtain ⟨A, hA⟩ := (Set.finite_range α₀).bddAbove
  have hAj : ∀ j, α₀ j ≤ A := fun j => hA ⟨j, rfl⟩
  have hx' : (Xs (A + 1)).IsSimpleAt (x (A + 1)) := (hgood (A + 1)).1.2.1 _
  have hx0 : (Xs A).IsSimpleAt (x A) := (hgood A).1.2.1 _
  have himpA := himp A (x A) (hx A) hx' hx0
  have : IsRegularLocalRing ((Xs A).presheaf.stalk (x A)) := hx0
  have : IsRegularLocalRing ((Xs (A + 1)).presheaf.stalk (x (A + 1))) := hx'
  -- the comparison, for each member `j` of the system
  have hcmp : ∀ j,
      nuStar ((Xs (A + 1)).presheaf.stalk (x (A + 1)))
          ((succSystem (fs A) (ℜs A) (σ A j)).stalkIdeal (x (A + 1))) =
        nuStar ((Xs A).presheaf.stalk (x A)) ((datumSystem (ℜs A) (σ A j)).stalkIdeal (x A)) ∧
      ∀ k : ℕ+,
        tau ((Xs A).presheaf.stalk (x A)) ((datumSystem (ℜs A) (σ A j)).stalkIdeal (x A)) (k : ℕ) =
          tau ((Xs (A + 1)).presheaf.stalk (x (A + 1)))
            ((succSystem (fs A) (ℜs A) (σ A j)).stalkIdeal (x (A + 1))) (k : ℕ) := by
    intro j
    obtain ⟨e₁, he₁⟩ := hSe A j
    obtain ⟨e₂, he₂⟩ := hSe (A + 1) j
    rw [← hσ A j] at he₂
    obtain ⟨hν₁, ht₁, hτ₁⟩ := nuStar_t_tau_map_ringEquiv e₁ ((S j).ideal (a j A))
    obtain ⟨hν₂, ht₂, hτ₂⟩ := nuStar_t_tau_map_ringEquiv e₂ ((S j).ideal (a j (A + 1)))
    rw [he₁] at hν₁ ht₁ hτ₁
    rw [he₂] at hν₂ ht₂ hτ₂
    have h1 := hν j (a j A) ((hAj j).trans ((ha j).id_le A))
    have h2 := hν j (a j (A + 1)) ((hAj j).trans ((Nat.le_succ A).trans ((ha j).id_le (A + 1))))
    have h3 := ht j (a j A) ((hAj j).trans ((ha j).id_le A))
    have h4 := ht j (a j (A + 1)) ((hAj j).trans ((Nat.le_succ A).trans ((ha j).id_le (A + 1))))
    refine ⟨by rw [hν₂, hν₁, h2, h1], fun k => ?_⟩
    rw [hτ₁, hτ₂]
    by_cases hk : (k : ℕ) ≤ t ((S j).ring (α₀ j)) ((S j).ideal (α₀ j))
    · rw [hτ j (a j A) ((hAj j).trans ((ha j).id_le A)) k k.pos hk,
        hτ j (a j (A + 1)) ((hAj j).trans ((Nat.le_succ A).trans ((ha j).id_le (A + 1)))) k k.pos hk]
    · push Not at hk
      rw [tau_eq_zero_of_t_lt _ (h3 ▸ hk), tau_eq_zero_of_t_lt _ (h4 ▸ hk)]
  rcases himpA with hgt | ⟨-, hlt⟩
  · obtain ⟨j, hj⟩ := hgt.2
    exact hj.ne (hcmp j).1
  · obtain ⟨j, k, hjk⟩ := hlt.2
    exact hjk.ne ((hcmp j).2 k)

/-- `datumSystem` of a transformed datum, reindexed along `β_transformI`, is `succSystem`. -/
theorem datumSystem_transformI_cast {X Y : Scheme.{u}} (g : MonoidalSuccession X Y)
    (ℜ : DatumI.Raw X) (j : Fin (ℜ.β + 1)) :
    datumSystem (g.transformI ℜ)
        (Fin.cast (congrArg (· + 1) (MonoidalSuccession.β_transformI g ℜ).symm) j) =
      succSystem g ℜ j := by
  refine Fin.lastCases ?_ (fun j => ?_) j
  · have h := (succSystem_eq_transformI g ℜ).1
    rw [Fin.cast_last, h]
    simp only [datumSystem, Fin.snoc_last]
  · have h := (succSystem_eq_transformI g ℜ).2 j
    rw [Fin.cast_castSucc, h]
    simp only [datumSystem, Fin.snoc_castSucc]

/-! ## Lemma (AB.1) (p. 294) -/

/-- **Lemma (AB.1)** (p. 294).  Each `f_i : X_{i+1} → X_i` is a finite succession of monoidal
transformations of `X_i` ending at `X_{i+1}` (`fs i : MonoidalSuccession (Xs i) (Xs (i + 1))`),
with `ℜ_{i+1} = f_i*(ℜ_i)` and the transformed restrictions; the paper's `X_0 = X` and
`ℜ_0 = ℜ` are the values at `0`.

Deviation from the paper (gap filled): the paper says "if `S(ℜ_i)` is not empty for arbitrarily
large integers `i`, then we can find a sequence of points `x_i ∈ S(ℜ_i)` such that
`f_i(x_{i+1}) = x_i` and `X_i` has dimension `N` at `x_i`".  Lean derives this: `S(ℜ_i)` is
nonempty for all `i` (by `f_i(S(ℜ_{i+1})) ⊆ S(ℜ_i)`), and the points of `S(ℜ_i)` that are images
of points of `S(ℜ_{i+k})` for every `k` form chains because the images `f_i(S(ℜ_{i+1}))` are
finite (property (i) of an effective modification; König-type argument,
`exists_chain_of_finite_image`); the dimension `N` at `x_i` is property (i) for `f_i`.  That the
stages stay ambient of dimension `N` and the data stay data with `dim W ≤ n` is
`isGoodDatumI_transformI_and_isFor_transformSucc` (Remark 1 of Ch. I).

Gap filled: `f_i(S(ℜ_{i+1})) ⊆ S(ℜ_i)`, which the paper cites (Corollary 2 of Theorem 5, §6,
Ch. III, and Lemma 4, §2, Ch. IV), is `composite_image_S_subset`; the closed case needs neither
result, and the open case is `MonoidalTransformation.image_unresolvedSet_transform_subset`.

Gap filled: "As is easily seen, these inequalities for all non-negative integers `i` lead to a
contradiction by virtue of Theorem 4, §5, Ch. III" is
`false_of_forall_nuStarSystemGT_or_tauStarSystemLT`, proved from Theorem 4
(`MonoidalSequence.exists_stationary`) and the scheme-to-ring bridge
`exists_monoidalSequence_of_chain` (a sequence of monoidal transforms of the local rings along the
intermediate points of the `f_i`, padded by trivial steps). -/
@[blueprint "lem:IV.AB-1"
  (statement := /-- \textbf{Lemma (AB.1).} Let $X$ and $\mathfrak R$ be as above: $X$ is a
    non-singular irreducible algebraic scheme of dimension $N$ and
    $\mathfrak R=(\mathfrak R^{N,n}_{\mathrm I},F)$ or $(\mathfrak R^{N,n}_{\mathrm I},U)$ with
    $N>n\ge0$. Let $\{f_i\colon X_{i+1}\to X_i\}$ be any sequence of effective modifications
    of $X_i$ for the resolution data $\mathfrak R_i$ on $X_i$
    (\cref{def:IV.3-effective-modification}), where $X_0=X$, $\mathfrak R_0=\mathfrak R$ and
    $\mathfrak R_{i+1}=f_i^*(\mathfrak R_i)$ for all $i\ge0$. Then $S(\mathfrak R_i)$
    (\cref{def:IV.3-S}) is empty for all sufficiently large integers $i$. (p.~294.) -/)
  (proof := /-- Let ${}^i\mathfrak R^{N,n}_{\mathrm I}$ be the resolution datum on $X_i$ such
    that ${}^0\mathfrak R^{N,n}_{\mathrm I}=\mathfrak R^{N,n}_{\mathrm I}$ and
    ${}^{i+1}\mathfrak R^{N,n}_{\mathrm I}=f_i^*({}^i\mathfrak R^{N,n}_{\mathrm I})$ for all
    $i\ge0$, and write ${}^i\mathfrak R^{N,n}_{\mathrm I}=(\bigcup_jE_j^{(i)};V_1^{(i)},\dots,
    V_\beta^{(i)};W^{(i)})$. Since $f_i\colon X_{i+1}\to X_i$ is a permissible succession of
    monoidal transformations of $X_i$ for $\mathfrak R_i$, we have
    $f_i(S(\mathfrak R_{i+1}))\subseteq S(\mathfrak R_i)$ for all $i\ge0$ (see Corollary~2 of
    Theorem~5, \S6, Ch.~III, \cref{cor:III.thm5-2}, and Lemma~4, \S2, Ch.~IV,
    \cref{lem:IV.2-4}). Therefore, if $S(\mathfrak R_i)$ is not empty for arbitrarily large
    integers $i$, then we can find a sequence of points $x_i\in S(\mathfrak R_i)$ such that
    $f_i(x_{i+1})=x_i$ and $X_i$ has dimension $N$ at $x_i$ for all $i\ge0$. By the property
    (ii) of an effective modification, we must have either
    $\nu^*_{x_{i+1}}(V_1^{(i+1)},\dots,V_\beta^{(i+1)},W^{(i+1)}/X_{i+1})<
    \nu^*_{x_i}(V_1^{(i)},\dots,V_\beta^{(i)},W^{(i)}/X_i)$, or these two are equal and
    $\tau^*_{x_{i+1}}(V_1^{(i+1)},\dots,W^{(i+1)}/X_{i+1})>
    \tau^*_{x_i}(V_1^{(i)},\dots,W^{(i)}/X_i)$. As is easily seen, these inequalities for all
    non-negative integers $i$ lead to a contradiction by virtue of Theorem~4, \S5, Ch.~III
    (\cref{thm:III.4}). \textsc{q.e.d.}

    \textbf{Deviation from the paper (gap filled).} ``Then we can find a sequence of points
    $x_i\in S(\mathfrak R_i)$ such that $f_i(x_{i+1})=x_i$ and $X_i$ has dimension $N$ at
    $x_i$'': Lean shows that $S(\mathfrak R_i)$ is nonempty for every $i$ (by the inclusion
    $f_i(S(\mathfrak R_{i+1}))\subseteq S(\mathfrak R_i)$), and obtains the sequence by a
    K\"onig-type argument from the finiteness of $f_i(S(\mathfrak R_{i+1}))$ (property (i) of an
    effective modification), which also gives the dimension $N$ at $x_i$. That each $X_i$ stays
    non-singular irreducible of dimension $N$ and $\mathfrak R_i$ stays a resolution datum with
    $\dim W_i\le n$ is Remark~1 of Ch.~I (\cref{lem:I.8-transform-is-datum}).

    \textbf{Deviation from the paper (gap filled).} In the closed case $S(\mathfrak R)=W\cap F$,
    and $f_i(S(\mathfrak R_{i+1}))\subseteq S(\mathfrak R_i)$ holds because strict transforms lie
    over the subschemes they are strict transforms of; the cited results (Corollary~2 of
    Theorem~5 and Lemma~4, \S2, Ch.~IV) are not needed.

    \textbf{Deviation from the paper (gap filled).} In the open case the inclusion
    $f_i(S(\mathfrak R_{i+1}))\subseteq S(\mathfrak R_i)$, cited by the paper (Corollary~2 of
    Theorem~5 and Lemma~4, \S2, Ch.~IV, which are statements about one monoidal transformation), is
    proved by applying them to the successive monoidal transformations of the succession: if
    $\mathfrak R$ is resolved at $x=f(y)$ then $f^*(\mathfrak R)$ is resolved at $y$. Off the
    center $f$ is a local isomorphism; over a point of the center $B$ the density of $W-B$ in $W$
    (needed for Corollary~2) follows from the open restriction $U\subseteq W-B$, $W'$ is simple
    at $y$ (it has normal crossings with $E'\cup f^{-1}(B)$ at $y$), the $V_j'$ are normally flat
    along $W'$ (Corollary~2 of Theorem~5), and $E'\cup f^{-1}(B)$ has only normal crossings with
    $W'$ (Lemma~4, \S2, Ch.~IV, \cref{lem:IV.2-4}, applied on an open neighbourhood of $x$ on which
    its hypotheses hold: the implicit localization of the citation).

    \textbf{Deviation from the paper (gap filled).} The final contradiction (``as is easily
    seen'') is proved from Theorem~4 (\cref{thm:III.4}) applied, for each member $V_j$, $W$ of the
    systems, to the sequence of monoidal transforms formed by the local rings along the
    intermediate points of the $f_i$: the ring at an intermediate point of a step is a monoidal
    transform of the ring at its image (\cref{def:III.2-monoidal-transform}) with center the stalk
    of the center, permissible and residually separable algebraic (the dimension being $N$ at
    every intermediate point, characteristic zero), the ideals are the stalks of the strict
    transforms, and the sequence is made infinite by padding with trivial steps (the monoidal
    transformation with the empty center is the identity, p.~295).

    \textbf{Deviation from the paper (gap filled).} ``As is easily seen'': the comparison of
    $\tau^{(k)}$ for all $k\ge1$ (Lean compares all $k$, Theorem~4 gives $k\le t$) uses that
    $\tau^{(k)}=0$ for $k>t$ on both sides; Theorem~3 is not needed since Theorem~4 already
    covers the whole infinite sequence; a single position works for all the finitely many
    members of the systems. -/)
  (proofUses := ["cor:III.thm5-2", "lem:IV.2-4", "thm:III.4"])
  (latexEnv := "lemma")]
theorem exists_forall_ge_S_eq_empty_of_forall_isEffectiveModification [Hironaka.HironakaCitedResults.{u}] (N n : ℕ) (hNn : n < N) (Xs : ℕ → Scheme.{u}) (hX : IsAmbient (Xs 0) N)
    (ℜs : ∀ i, DatumI.Raw (Xs i)) (rs : ∀ i, Restriction (Xs i)) (hℜ : (ℜs 0).IsDatum)
    (hr : (rs 0).IsFor (ℜs 0)) (hn : (ℜs 0).n = (n : WithBot ℕ∞))
    (fs : ∀ i, MonoidalSuccession (Xs i) (Xs (i + 1)))
    (hℜs : ∀ i, ℜs (i + 1) = (fs i).transformI (ℜs i))
    (hrs : ∀ i, rs (i + 1) = (rs i).transformSucc (fs i))
    (heff : ∀ i, IsEffectiveModification N (ℜs i) (rs i) (fs i)) :
    ∃ i₀ : ℕ, ∀ i, i₀ ≤ i → S (ℜs i) (rs i) = ∅ := by
  by_contra hcon
  push Not at hcon
  have hgood : ∀ i, IsGoodDatumI N n (Xs i) (ℜs i) ∧ (rs i).IsFor (ℜs i) := by
    intro i
    induction i with
    | zero => exact ⟨⟨hX, hℜ, le_of_eq hn⟩, hr⟩
    | succ i ih =>
      have := isGoodDatumI_transformI_and_isFor_transformSucc (fs i) ih.1 ih.2 (heff i).1
      rw [hℜs i, hrs i]
      exact this
  have hSeq : ∀ i, S ((fs i).transformI (ℜs i)) ((rs i).transformSucc (fs i)) =
      S (ℜs (i + 1)) (rs (i + 1)) := fun i => by rw [hℜs i, hrs i]
  have hsub : ∀ i, (fs i).composite.base '' S (ℜs (i + 1)) (rs (i + 1)) ⊆ S (ℜs i) (rs i) := by
    intro i
    rw [← hSeq i]
    exact composite_image_S_subset (fs i) (hgood i).1 (hgood i).2 (heff i).1
  have hstep : ∀ j, S (ℜs (j + 1)) (rs (j + 1)) ≠ ∅ → S (ℜs j) (rs j) ≠ ∅ := by
    intro j hS hj
    obtain ⟨y, hy⟩ := Set.nonempty_iff_ne_empty.mpr hS
    have := hsub j ⟨y, hy, rfl⟩
    rw [hj] at this
    exact this
  have hne0 : ∀ j i, i ≤ j → S (ℜs j) (rs j) ≠ ∅ → S (ℜs i) (rs i) ≠ ∅ := by
    intro j
    induction j with
    | zero => intro i hi hS; obtain rfl := Nat.le_zero.mp hi; exact hS
    | succ j ih =>
      intro i hi hS
      rcases Nat.of_le_succ hi with h | rfl
      · exact ih i h (hstep j hS)
      · exact hS
  have hne : ∀ i, (S (ℜs i) (rs i)).Nonempty := fun i => by
    obtain ⟨j, hj, hSj⟩ := hcon i
    exact Set.nonempty_iff_ne_empty.mpr (hne0 j i hj (Set.nonempty_iff_ne_empty.mp hSj))
  have hfin : ∀ i, ((fs i).composite.base '' S (ℜs (i + 1)) (rs (i + 1))).Finite := fun i => by
    rw [← hSeq i]
    exact (heff i).2.1
  obtain ⟨x, hxim, hxf⟩ := exists_chain_of_finite_image
    (α := fun i => (Xs i : Type u)) (fun i y => (fs i).composite.base y)
    (fun i => S (ℜs i) (rs i)) hsub hne hfin
  have hdim : ∀ i, (Xs i).dimAt (x i) = (N : WithBot ℕ∞) := fun i => by
    have := hxim i
    rw [← hSeq i] at this
    exact (heff i).2.2.1 _ this
  have hβ : ∀ i, (ℜs i).β = (ℜs 0).β := by
    intro i
    induction i with
    | zero => rfl
    | succ i ih => rw [hℜs i, MonoidalSuccession.β_transformI]; exact ih
  let σ : ∀ i, Fin ((ℜs 0).β + 1) ≃ Fin ((ℜs i).β + 1) := fun i =>
    finCongr (congrArg (· + 1) (hβ i).symm)
  have hσ : ∀ i j, succSystem (fs i) (ℜs i) (σ i j) = datumSystem (ℜs (i + 1)) (σ (i + 1) j) := by
    intro i j
    have key : ∀ (ℜ' : DatumI.Raw (Xs (i + 1))), ℜ' = (fs i).transformI (ℜs i) →
        ∀ j' : Fin (ℜ'.β + 1), (j' : ℕ) = (σ i j : ℕ) →
          datumSystem ℜ' j' = succSystem (fs i) (ℜs i) (σ i j) := by
      intro ℜ' h
      subst h
      intro j' hj'
      have : j' = Fin.cast (congrArg (· + 1) (MonoidalSuccession.β_transformI (fs i)
          (ℜs i)).symm) (σ i j) := Fin.ext hj'
      rw [this]
      exact datumSystem_transformI_cast _ _ _
    exact (key (ℜs (i + 1)) (hℜs i) (σ (i + 1) j) (by simp [σ])).symm
  refine false_of_forall_nuStarSystemGT_or_tauStarSystemLT hNn (ι := Fin ((ℜs 0).β + 1)) Xs ℜs fs
    (fun i => (hgood i).1) hℜs (fun i => (heff i).1.isPermissibleI) σ hσ x hxf hdim
    (fun i p hp hx' hx0 => ?_)
  subst hp
  have hxS : x (i + 1) ∈ S ((fs i).transformI (ℜs i)) ((rs i).transformSucc (fs i)) := by
    rw [hSeq i]
    exact hsub (i + 1) (hxim (i + 1))
  rcases (heff i).2.2.2 (x (i + 1)) hxS (hdim (i + 1)) hx' hx0 with h | ⟨h1, h2⟩
  · exact Or.inl (NuStarSystemGT.comp_equiv (σ i) (V := datumSystem (ℜs i))
      (V' := succSystem (fs i) (ℜs i)) h)
  · exact Or.inr ⟨NuStarSystemEq.comp_equiv (σ i) (V := datumSystem (ℜs i))
      (V' := succSystem (fs i) (ℜs i)) h1, TauStarSystemLT.comp_equiv (σ i)
      (V := datumSystem (ℜs i)) (V' := succSystem (fs i) (ℜs i)) h2⟩

/-- p. 294: "We first claim that Theorems A and B follow Theorems A* and B* respectively.  In
other words, we have Lemma (AB.1)."  The claim, made explicit: if effective modifications exist
for all data of the relevant kind, then some permissible succession makes `S` empty.

Deviation from the paper (gap filled): the paper only says "We first claim that Theorems A and B
follow Theorems A* and B* respectively".  Lean builds the sequence `f_i` by recursion
(`EffectiveStage`): at each stage `X_i` is ambient of dimension `N` and `ℜ_i` is a datum with
`dim W_i ≤ n` (`isGoodDatumI_transformI_and_isFor_transformSucc`: Remark 1 of Ch. I); if
`S(ℜ_i) = ∅` the empty succession is chosen (the paper stops), otherwise the hypothesis is applied
with `n' = dim W_i ≤ n`.  The composite of `f_0, …, f_{i-1}` is formed with `MonoidalSuccession.append`
and shown permissible for `(ℜ, r)` with transform `(ℜ_i, r_i)`. -/
@[blueprint "lem:IV.AB-1-consequence"
  (statement := /-- ``We first claim that Theorems A and B follow Theorems A* and B*
    respectively'' (p.~294). Precisely: let $N>n\ge0$ and suppose that every resolution datum
    $\mathfrak R'=(\mathfrak R^{N,n'}_{\mathrm I},F')$ (resp.\
    $(\mathfrak R^{N,n'}_{\mathrm I},U')$) with $n'\le n$ on a non-singular irreducible
    algebraic scheme $X'$ of dimension $N$ admits an effective modification
    (\cref{def:IV.3-effective-modification}). Then for every resolution datum
    $\mathfrak R=(\mathfrak R^{N,n}_{\mathrm I},F)$ (resp.\ $(\mathfrak R^{N,n}_{\mathrm I},U)$)
    on a non-singular irreducible algebraic scheme $X$ of dimension $N$ there is a permissible
    succession of monoidal transformations $f$ of $X$ for $\mathfrak R$ with
    $S(f^*(\mathfrak R))=\emptyset$ (\cref{def:IV.3-S}), i.e.\ $W'\cap F'=\emptyset$ (resp.\
    $f^*(\mathfrak R^{N,n}_{\mathrm I})$ is resolved at every point of $W'$). (Formalization
    note: this makes explicit the deduction of Theorems A, B from Theorems A*, B*, whose
    content the paper states as Lemma (AB.1), \cref{lem:IV.AB-1}.) -/)
  (proof := /-- Choose inductively effective modifications $f_i\colon X_{i+1}\to X_i$ of $X_i$
    for $\mathfrak R_i$, where $X_0=X$, $\mathfrak R_0=\mathfrak R$ and
    $\mathfrak R_{i+1}=f_i^*(\mathfrak R_i)$: each $X_{i+1}$ is again a non-singular
    irreducible algebraic scheme of dimension $N$ (the centers are non-singular and nowhere
    dense, \cref{lem:monoidal-transformation-nonsingular}), $\mathfrak R_{i+1}$ is a resolution
    datum of the same kind (\cref{rem:I.1-transform-is-datum-I}), and the dimension of its
    principal subscheme is at most $n$; if that subscheme is empty, $S(\mathfrak R_{i+1})$ is
    empty and we stop. By Lemma (AB.1) (\cref{lem:IV.AB-1}), $S(\mathfrak R_i)$ is empty for
    some $i$, and the composite of $f_0,\dots,f_{i-1}$ is a permissible succession of monoidal
    transformations of $X$ for $\mathfrak R$ with $S(\mathfrak R_i)=\emptyset$.

    \textbf{Deviation from the paper (gap filled).} The sequence is constructed in Lean by
    recursion, each stage carrying the invariants ``$X_i$ ambient of dimension $N$, $\mathfrak R_i$
    a datum with $\dim W_i\le n$'' (Remark~1 of Ch.~I); when $S(\mathfrak R_i)=\emptyset$ the
    empty succession is chosen instead of stopping, so that the sequence is infinite as
    Lemma~(AB.1) requires, and otherwise the hypothesis is applied with $n'=\dim W_i\le n$. -/)
  (proofUses := ["lem:IV.AB-1"])
  (latexEnv := "corollary")]
theorem exists_isPermissibleSucc_S_eq_empty_of_forall_exists_isEffectiveModification [Hironaka.HironakaCitedResults.{u}] (N n : ℕ) (hNn : n < N)
    (X : Scheme.{u}) (hX : IsAmbient X N) (ℜ : DatumI.Raw X) (hℜ : ℜ.IsDatum)
    (hn : ℜ.n = (n : WithBot ℕ∞)) (r : Restriction X) (hr : r.IsFor ℜ)
    (heff : ∀ (X' : Scheme.{u}), IsAmbient X' N → ∀ (ℜ' : DatumI.Raw X'), ℜ'.IsDatum →
      ∀ r' : Restriction X', r'.IsFor ℜ' → (r'.IsClosedKind ↔ r.IsClosedKind) →
      ∀ n' : ℕ, n' ≤ n → ℜ'.n = (n' : WithBot ℕ∞) →
        ∃ (Y : Scheme.{u}) (f : MonoidalSuccession X' Y), IsEffectiveModification N ℜ' r' f) :
    ∃ (Y : Scheme.{u}) (f : MonoidalSuccession X Y),
      r.IsPermissibleSucc f ℜ ∧ S (f.transformI ℜ) (r.transformSucc f) = ∅ := by
  let st0 : EffectiveStage.{u} N n r.IsClosedKind := ⟨X, ℜ, r, ⟨hX, hℜ, le_of_eq hn⟩, hr, Iff.rfl⟩
  obtain ⟨i₀, hi⟩ := exists_forall_ge_S_eq_empty_of_forall_isEffectiveModification N n hNn
    (fun i => (EffectiveStage.seq heff st0 i).X) hX (fun i => (EffectiveStage.seq heff st0 i).ℜ)
    (fun i => (EffectiveStage.seq heff st0 i).r) hℜ hr hn
    (fun i => ((EffectiveStage.seq heff st0 i).step heff).2.1) (fun i => rfl) (fun i => rfl)
    (fun i => ((EffectiveStage.seq heff st0 i).step heff).2.2)
  obtain ⟨h1, h2, h3⟩ := EffectiveStage.transformI_pre_and_transformSucc_pre_and_isPermissibleSucc_pre heff st0 i₀
  exact ⟨_, EffectiveStage.pre heff st0 i₀, h3, by rw [h1, h2]; exact hi i₀ le_rfl⟩

/-! ## The fixed succession `{f_s : X_{s+1} → X_s}` (pp. 294–295) -/

/-- The universal property (i), (ii) of a monoidal transformation with center `B` (p. 166),
for a given morphism `f : X' → X` (the predicate version of the fields of
`MonoidalTransformation`). -/
def IsMonoidalTransformationOf {X X' : Scheme.{u}} (f : X' ⟶ X) (B : Subscheme X) : Prop :=
  (Subscheme.totalTransform f B).IsInvertibleIdeal ∧
  ∀ (X'' : Scheme.{u}) (f' : X'' ⟶ X), (Subscheme.totalTransform f' B).IsInvertibleIdeal →
    ∃! h : X'' ⟶ X', h ≫ f = f'

/-- A morphism isomorphic over `X` to a monoidal transformation with center `B` has the
universal property of one. -/
theorem IsMonoidalTransformationOf.of_iso {X X'' : Scheme.{u}} {B : Subscheme X}
    (s : MonoidalTransformation X B) (e : X'' ≅ s.X') (f : X'' ⟶ X) (hf : e.hom ≫ s.f = f) :
    IsMonoidalTransformationOf f B := by
  subst hf
  refine ⟨?_, fun Y f' hf' => ?_⟩
  · have : Subscheme.totalTransform (e.hom ≫ s.f) B =
        Subscheme.totalTransform e.hom (Subscheme.totalTransform s.f B) := by
      rw [← Subscheme.totalTransform_comp]
    rw [this]
    exact isInvertibleIdeal_totalTransform_of_flat e.hom s.invertible
  · obtain ⟨h, hh, huniq⟩ := s.universal Y f' hf'
    refine ⟨h ≫ e.inv, by simp [hh], fun h2 hh2 => ?_⟩
    have : (h2 ≫ e.hom) = h :=
      huniq _ (by show (h2 ≫ e.hom) ≫ s.f = f'; rw [Category.assoc]; exact hh2)
    rw [← this]; simp

/-- The map `f̄ : V' → V` induced on a strict transform by a monoidal transformation `t` is a
monoidal transformation of `V` with center `V ∩ B` (p. 167; the morphism `f̄_s` on p. 298). -/
theorem _root_.Hironaka.MonoidalTransformation.isMonoidalTransformationOf_strictTransformMap [Hironaka.HironakaCitedResults.{u}]
    {X : Scheme.{u}} {B : Subscheme X} (t : MonoidalTransformation X B) (V : Subscheme X) :
    IsMonoidalTransformationOf (t.strictTransformMap V) (Subscheme.totalTransform V.ι B) := by
  obtain ⟨⟨s⟩, hs⟩ := Subscheme.nonempty_monoidalTransformation_strictTransform t V
  obtain ⟨e, he⟩ := hs s
  refine IsMonoidalTransformationOf.of_iso s e.symm _ ?_
  rw [← cancel_mono V.ι, Category.assoc, MonoidalTransformation.strictTransformMap_ι]
  have h2 := congrArg (fun g => e.inv ≫ g) he
  simp only [Iso.inv_hom_id_assoc] at h2
  rw [Iso.symm_hom]
  exact h2.symm

/-- A monoidal transformation is an isomorphism over any open set that misses its center. -/
theorem IsMonoidalTransformationOf.isIso_morphismRestrict_of_forall_notMem {Z Z' : Scheme.{u}}
    {f : Z' ⟶ Z} {B : Subscheme Z} (hf : IsMonoidalTransformationOf f B) (Ω : Z.Opens)
    (hΩ : ∀ z ∈ Ω, z ∉ B.pts) : IsIso (f ∣_ Ω) := by
  have hB : Subscheme.totalTransform Ω.ι B = Subscheme.empty := by
    refine Subscheme.eq_empty_of_pts_eq_empty ?_
    rw [FlatPreimm.pts_totalTransform]
    exact Set.eq_empty_of_forall_notMem fun z hz => hΩ z.val z.property hz
  obtain ⟨s, hs, -⟩ := hf.2 Ω Ω.ι (by rw [hB]; exact Subscheme.isInvertibleIdeal_empty)
  have hw : 𝟙 (Ω : Scheme.{u}) ≫ Ω.ι = s ≫ f := by rw [Category.id_comp]; exact hs.symm
  set s' := (isPullback_morphismRestrict f Ω).lift (𝟙 (Ω : Scheme.{u})) s hw with hs'
  have hs'r : s' ≫ (f ∣_ Ω) = 𝟙 _ := (isPullback_morphismRestrict f Ω).lift_fst _ _ hw
  have hs'ι : s' ≫ (f ⁻¹ᵁ Ω).ι = s := (isPullback_morphismRestrict f Ω).lift_snd _ _ hw
  have hinv : (Subscheme.totalTransform ((f ⁻¹ᵁ Ω).ι ≫ f) B).IsInvertibleIdeal := by
    rw [Subscheme.totalTransform_comp]
    exact isInvertibleIdeal_totalTransform_of_flat (f ⁻¹ᵁ Ω).ι hf.1
  have hrs : (f ∣_ Ω) ≫ s = (f ⁻¹ᵁ Ω).ι := by
    refine (hf.2 (f ⁻¹ᵁ Ω) ((f ⁻¹ᵁ Ω).ι ≫ f) hinv).unique ?_ rfl
    rw [Category.assoc, hs, ← morphismRestrict_ι]
  refine ⟨⟨s', ?_, hs'r⟩⟩
  rw [← cancel_mono (f ⁻¹ᵁ Ω).ι, Category.assoc, hs'ι, hrs, Category.id_comp]

/-- A monoidal transformation restricted to an open subscheme of the target is a monoidal
transformation with the restricted center. -/
theorem IsMonoidalTransformationOf.morphismRestrict {Z Z' : Scheme.{u}} {f : Z' ⟶ Z}
    {B : Subscheme Z} (hf : IsMonoidalTransformationOf f B) (Ω : Z.Opens) :
    IsMonoidalTransformationOf (f ∣_ Ω) (Subscheme.totalTransform Ω.ι B) := by
  have hpb := isPullback_morphismRestrict f Ω
  refine ⟨?_, fun W g hg => ?_⟩
  · have : Subscheme.totalTransform (f ∣_ Ω) (Subscheme.totalTransform Ω.ι B) =
        Subscheme.totalTransform (f ⁻¹ᵁ Ω).ι (Subscheme.totalTransform f B) := by
      rw [← Subscheme.totalTransform_comp, ← Subscheme.totalTransform_comp, morphismRestrict_ι]
    rw [this]
    exact isInvertibleIdeal_totalTransform_of_flat _ hf.1
  · have hg' : (Subscheme.totalTransform (g ≫ Ω.ι) B).IsInvertibleIdeal := by
      rw [Subscheme.totalTransform_comp]; exact hg
    obtain ⟨k, hk, hku⟩ := hf.2 W (g ≫ Ω.ι) hg'
    have hw : g ≫ Ω.ι = k ≫ f := hk.symm
    refine ⟨hpb.lift g k hw, hpb.lift_fst g k hw, fun h' hh' => ?_⟩
    apply hpb.hom_ext
    · rw [hpb.lift_fst]; exact hh'
    · rw [hpb.lift_snd]
      apply hku
      rw [Category.assoc, ← morphismRestrict_ι, ← Category.assoc, hh']

/-- A scheme isomorphic to a non-singular scheme is non-singular. -/
theorem _root_.Hironaka.CD.isNonsingular_of_iso {A B : Scheme.{u}} (e : A ≅ B) (hB : B.IsNonsingular) :
    A.IsNonsingular := by
  intro a
  have : IsRegularLocalRing (B.presheaf.stalk (e.hom a)) := hB (e.hom a)
  exact IsRegularLocalRing.of_ringEquiv (CategoryTheory.asIso
    (e.hom.stalkMap a)).commRingCatIsoToRingEquiv

/-- The total transform of `D ⊆ V` in the scheme `V` is isomorphic to `D`. -/
theorem _root_.Hironaka.CD.nonempty_totalTransform_iso_of_isContainedIn {Y : Scheme.{u}} {V D : Subscheme Y}
    (hDV : D.IsContainedIn V) :
    Nonempty ((Subscheme.totalTransform V.ι D).toScheme ≅ D.toScheme) := by
  have hVD : V ≤ D := fun U => hDV U
  have hsq : CategoryTheory.IsPullback (Scheme.IdealSheafData.inclusion hVD)
      (CategoryTheory.CategoryStruct.id D.toScheme) V.ι D.ι :=
    CategoryTheory.IsPullback.of_vert_isIso_mono ⟨by
      rw [Scheme.IdealSheafData.inclusion_subschemeι, CategoryTheory.Category.id_comp]⟩
  exact ⟨D.comapIso V.ι ≪≫ hsq.isoPullback.symm⟩

/-- The schemes `X_0 = X₀, X_1, X_2, …` of a sequence given by `X₀` and `(X_{s+1})_s`. -/
def towerScheme (X₀ : Scheme.{u}) (Xs : ℕ → Scheme.{u}) : ℕ → Scheme.{u}
  | 0 => X₀
  | s + 1 => Xs s

/-- p. 294: "any permissible succession (finite or infinite) of monoidal transformations of `X`
for the given resolution datum `ℜ`, say `{f_s : X_{s+1} → X_s}` (`s = 0, 1, 2, …`) where `X_0`
denotes `X`."  The data of the succession (permissibility is `Standing.permissible`): the
schemes `X_{s+1}`, the centers `B_s ⊆ X_s` and the monoidal transformations
`f_s : X_{s+1} → X_s` with center `B_s`.  A finite succession is one whose centers are
eventually empty ("the monoidal transformation with the empty center is the identity
isomorphism", p. 295). -/
@[blueprint "def:IV.3-succession"
  (statement := /-- Let us fix and study any permissible succession (finite or infinite) of
    monoidal transformations of $X$ for the given resolution datum $\mathfrak R$, say
    $\{f_s\colon X_{s+1}\to X_s\}$ $(s=0,1,2,\dots)$, where $X_0$ denotes $X$. Let
    $\mathfrak R(s)$ denote the resolution datum on $X_s$ $(s\ge0)$ such that
    $\mathfrak R(0)=\mathfrak R$ and $\mathfrak R(s+1)=f_s^*(\mathfrak R(s))$ for all $s\ge0$.
    For the case in which $\mathfrak R=(\mathfrak R^{N,n}_{\mathrm I},F)$ (resp.\
    $\mathfrak R=(\mathfrak R^{N,n}_{\mathrm I},U)$), we write
    $\mathfrak R(s)=(\mathfrak R^{N,n}_{\mathrm I}(s),F(s))$ (resp.\
    $\mathfrak R(s)=(\mathfrak R^{N,n}_{\mathrm I}(s),U(s))$). In both cases, we write
    $\mathfrak R^{N,n}_{\mathrm I}(s)=(\bigcup_{i=1}^{\alpha+s}E_i(s);V_1(s),\dots,V_\beta(s);
    W(s))$. Let $B_s$ denote the center of $f_s$ in $X_s$, and set the symbols $E_i(s)$ in
    such a way that $E_i(0)=E_i$ $(1\le i\le\alpha)$, $E_j(s+1)=$ the strict transform of
    $E_j(s)$ $(1\le j\le\alpha+s)$ and $E_{\alpha+s+1}(s+1)=$ the total transform
    $f_s^{-1}(B_s)$ of the center $B_s$. We denote by $g_s$ the morphism $X_s\to X_0$ obtained
    as the composition of the $f_j$ for $0\le j\le s-1$. (pp.~294--295.)
    (Formalization notes (encoding): the succession is indexed by $\mathbb N$, a finite succession being
    one whose centers are eventually empty, since the monoidal transformation with the empty
    center is the identity isomorphism (p.~295, \cref{lem:monoidal-transformation-empty-center});
    each $f_s$ is recorded with the universal property of \cref{def:monoidal-transformation};
    $g_s$ is the initial segment $\{f_t\}_{t<s}$, a finite succession in the sense of
    \cref{def:succession}, along which $\mathfrak R(s)$, $F(s)$, $U(s)$, $V_j(s)$ and $W(s)$
    are formed (\cref{def:I.7-I}, \cref{def:I.8}).) -/)
  (latexEnv := "definition")]
structure Tower (X₀ : Scheme.{u}) where
  /-- The schemes `X_{s+1}`, `s ≥ 0`. -/
  xSucc : ℕ → Scheme.{u}
  /-- The center `B_s` of `f_s` in `X_s`. -/
  B : ∀ s, Subscheme (towerScheme X₀ xSucc s)
  /-- The morphism `f_s : X_{s+1} → X_s`. -/
  f : ∀ s, towerScheme X₀ xSucc (s + 1) ⟶ towerScheme X₀ xSucc s
  /-- `f_s` is the monoidal transformation of `X_s` with center `B_s`. -/
  isMonoidal : ∀ s, IsMonoidalTransformationOf (f s) (B s)

namespace Tower

variable {X₀ : Scheme.{u}} (T : Tower X₀)

/-- The scheme `X_s` (`X_0 = X₀`). -/
abbrev X (s : ℕ) : Scheme.{u} := towerScheme X₀ T.xSucc s

/-- `f_s` as a `MonoidalTransformation` of `X_s` with center `B_s`; its blown-up scheme is
`X_{s+1}` by definition. -/
def monoidalTransformation (s : ℕ) : MonoidalTransformation (T.X s) (T.B s) where
  X' := T.X (s + 1)
  f := T.f s
  invertible := (T.isMonoidal s).1
  universal := (T.isMonoidal s).2

/-- The initial segment `g_s = {f_t : X_{t+1} → X_t}_{0 ≤ t < s}`, a finite succession from
`X_0` to `X_s`; its composite is the morphism `g_s : X_s → X_0` of p. 295. -/
def pre : (s : ℕ) → MonoidalSuccession X₀ (T.X s)
  | 0 => .nil X₀
  | s + 1 => Hironaka.MonoidalSuccession.snoc (pre s) (T.B s) (T.monoidalTransformation s)

/-- The system `(V_1(s), …, V_β(s), W(s))` of `ℜ(s)` (strict transforms along `g_s`). -/
def sys (ℜ : DatumI.Raw X₀) (s : ℕ) : Fin (ℜ.β + 1) → Subscheme (T.X s) :=
  succSystem (T.pre s) ℜ

/-- p. 295: `E_i(0) = E_i` (`1 ≤ i ≤ α`), `E_j(s+1)` = the strict transform of `E_j(s)`
(`1 ≤ j ≤ α + s`) and `E_{α+s+1}(s+1)` = the total transform `f_s⁻¹(B_s)` of the center. -/
def Esys {α : ℕ} (E : Fin α → Subscheme X₀) : ∀ s, Fin (α + s) → Subscheme (T.X s)
  | 0 => E
  | s + 1 => Fin.snoc (α := fun _ => Subscheme (T.X (s + 1)))
      (fun j => Subscheme.strictTransform (T.monoidalTransformation s) (Esys E s j)) (T.monoidalTransformation s).exceptional

end Tower

/-! ## The standing choices, the completion and the frame (pp. 292–298) -/

/-- The standing assumptions of pp. 292–295 on the data `(N, n, X, ℜ, ⋃ E_i, r, {f_s}, x_0)`. -/
@[blueprint "def:IV.3-standing"
  (statement := /-- The standing assumptions of pp.~292--295: $X$ is a non-singular irreducible
    algebraic scheme of dimension $N$, $\mathfrak R=(\mathfrak R^{N,n}_{\mathrm I},F)$ or
    $\mathfrak R=(\mathfrak R^{N,n}_{\mathrm I},U)$ is a resolution datum on $X$ with
    $\mathfrak R^{N,n}_{\mathrm I}=(\bigcup_{i=1}^\alpha E_i;V_1,\dots,V_\beta;W)$
    (\cref{def:IV.0-expression}) and $N>n\ge0$, $\{f_s\colon X_{s+1}\to X_s\}$ is a
    permissible succession of monoidal transformations of $X$ for $\mathfrak R$
    (\cref{def:IV.3-succession}), and ``let us choose and fix any point $x_0$ of $W^*$ at
    which $X$ has dimension $N$, where $W^*$ denotes $W\cap F$ (resp.\ $W-U$) for the case in
    which $\mathfrak R=(\mathfrak R^{N,n}_{\mathrm I},F)$ (resp.\
    $\mathfrak R=(\mathfrak R^{N,n}_{\mathrm I},U)$)'' (p.~295). -/)
  (latexEnv := "definition")]
structure Standing (N n : ℕ) {X : Scheme.{u}} (ℜ : DatumI.Raw X) (P : DatumI.Presentation ℜ)
    (r : Restriction X) (T : Tower X) (x₀ : X) : Prop where
  /-- `N > n ≥ 0`. -/
  lt : n < N
  /-- `X` is a non-singular irreducible algebraic scheme of dimension `N`. -/
  ambient : IsAmbient X N
  /-- `ℜ` is a resolution datum of type `ℜ^{N,n}_I`. -/
  isDatum : ℜ.IsDatum
  /-- `n = dim W`. -/
  dim_W : ℜ.n = (n : WithBot ℕ∞)
  /-- `r` is a closed (resp. open) restriction for `ℜ`. -/
  isFor : r.IsFor ℜ
  /-- The succession `{f_s}` is permissible for `(ℜ, r)`: each initial segment is. -/
  permissible : ∀ s, r.IsPermissibleSucc (T.pre s) ℜ
  /-- `x_0 ∈ W*`. -/
  mem_wStar : x₀ ∈ wStar ℜ r
  /-- `X` has dimension `N` at `x_0`. -/
  dimAt_x₀ : X.dimAt x₀ = (N : WithBot ℕ∞)

/-- The completion `Ŝ` of the local ring `S = O_{X,x_0}` (p. 295), with respect to its maximal
ideal. -/
abbrev Shat (X : Scheme.{u}) (x₀ : X) : Type u :=
  AdicCompletion (maximalIdeal (X.presheaf.stalk x₀)) (X.presheaf.stalk x₀)

/-- `X̂_0 = Spec(Ŝ)` (p. 295). -/
def xHat0 (X : Scheme.{u}) (x₀ : X) : Scheme.{u} :=
  Spec (CommRingCat.of (Shat X x₀))

/-- `c_0 : X̂_0 → X`, "the morphism `X̂_0 → X` induced by the canonical local homomorphism
`S → Ŝ`" (p. 295): `Spec(Ŝ) → Spec(S) → X`. -/
def c0 (X : Scheme.{u}) (x₀ : X) : xHat0 X x₀ ⟶ X :=
  Spec.map (CommRingCat.ofHom (algebraMap (X.presheaf.stalk x₀) (Shat X x₀))) ≫
    X.fromSpecStalk x₀

/-- "The algebraic scheme `X̂_0 = Spec(Ŝ)` has the unique closed point `x̂_0`" (p. 295). -/
def xhat0 (X : Scheme.{u}) (x₀ : X) (hx : X.IsSimpleAt x₀) : xHat0 X x₀ :=
  haveI : IsRegularLocalRing (X.presheaf.stalk x₀) := hx
  IsLocalRing.closedPoint (Shat X x₀)

/-- p. 295: the setup attached to the chosen point `x_0`: "The given succession of monoidal
transformations `{f_s : X_{s+1} → X_s}` of `X` induces a succession of monoidal transformations
`{f̂_s : X̂_{s+1} → X̂_s}` of `X̂_0` such that we have the following commutative diagrams of
canonical morphisms [`f_s ∘ c_{s+1} = c_s ∘ f̂_s`] where `c_0` is the morphism `X̂_0 → X` induced
by the canonical local homomorphism `S → Ŝ`, and `f̂_s` is the monoidal transformation of `X̂_s`
with the non-singular center `B̂_s = c_s⁻¹(B_s)` for `s ≥ 0`. … In view of the fact that `Ŝ` is
faithfully flat over `S`, one can show that `X̂_s` is canonically isomorphic to the product
`X_s ×_X X̂_0` in the category of schemes over `X` and that `c_s` is the projection to the
first factor."

Formalization notes: `Ŝ`, `X̂_0` and `c_0` are constructed (`Shat`, `xHat0`, `c0`); the induced
succession `{f̂_s}` (a `Tower` of `X̂_0`) and the morphisms `c_s` are recorded as data subject
to the stated properties, the product property being the pullback square
`X̂_s = X_s ×_X X̂_0` with projections `c_s` and `ĝ_s`; `ĝ_s` is the composite of the initial
segment of `{f̂_s}`.  Existence: `lem:IV.3-setup-exists`. -/
@[blueprint "def:IV.3-setup"
  (statement := /-- Let $S$ be the local ring of $X$ at $x_0$, and $\hat S$ the completion of
    $S$. Let $\hat X_0=\operatorname{Spec}(\hat S)$. The given succession of monoidal
    transformations $\{f_s\colon X_{s+1}\to X_s\}$ of $X$ (\cref{def:IV.3-succession})
    induces a succession of monoidal transformations $\{\hat f_s\colon\hat X_{s+1}\to\hat X_s\}$
    of $\hat X_0$ such that we have the commutative diagrams $c_s\circ\hat f_s=f_s\circ
    c_{s+1}$ of canonical morphisms, where $c_0$ is the morphism $\hat X_0\to X$ induced by the
    canonical local homomorphism $S\to\hat S$, and $\hat f_s$ is the monoidal transformation of
    $\hat X_s$ with the non-singular center $\hat B_s=c_s^{-1}(B_s)$ for $s\ge0$. Here it
    should be noted that the monoidal transformation with the empty center is the identity
    isomorphism. In view of the fact that $\hat S$ is faithfully flat over $S$, one can show
    that $\hat X_s$ is canonically isomorphic to the product $X_s\times_X\hat X_0$ in the
    category of schemes over $X$ and that $c_s$ is the projection to the first factor. The
    algebraic scheme $\hat X_0=\operatorname{Spec}(\hat S)$ has the unique closed point
    $\hat x_0$ such that $c_0(\hat x_0)=x_0$. We shall denote by $g_s$ (resp.\ $\hat g_s$) the
    morphism $X_s\to X_0$ (resp.\ $\hat X_s\to\hat X_0$) obtained as the composition of the
    $f_j$ (resp.\ $\hat f_j$) for $0\le j\le s-1$. (p.~295.) (Formalization notes (encoding): $\hat S$ is
    the completion of $S$ with respect to its maximal ideal; $\hat X_0$, $c_0$, $\hat x_0$ are
    constructed; the induced succession $\{\hat f_s\}$ and the $c_s$ are recorded as data with
    the stated properties, the product property as the pullback square with projections $c_s$
    and $\hat g_s$; they exist by \cref{lem:IV.3-setup-exists}.) -/)
  (latexEnv := "definition")]
structure Completion {X : Scheme.{u}} (T : Tower X) (x₀ : X) where
  /-- The induced succession `{f̂_s : X̂_{s+1} → X̂_s}` of `X̂_0 = Spec(Ŝ)`. -/
  tHat : Tower (xHat0 X x₀)
  /-- The morphisms `c_s : X̂_s → X_s`. -/
  c : ∀ s, tHat.X s ⟶ T.X s
  /-- `c_0` is induced by `S → Ŝ`. -/
  c_zero : c 0 = c0 X x₀
  /-- The commutative diagrams `c_s ∘ f̂_s = f_s ∘ c_{s+1}`. -/
  c_comm : ∀ s, tHat.f s ≫ c s = c (s + 1) ≫ T.f s
  /-- `f̂_s` has the center `B̂_s = c_s⁻¹(B_s)`. -/
  B_hat : ∀ s, tHat.B s = Subscheme.totalTransform (c s) (T.B s)
  /-- `X̂_s = X_s ×_X X̂_0`, with projections `c_s` and `ĝ_s`. -/
  isPullback : ∀ s, IsPullback (c s) (tHat.pre s).composite (T.pre s).composite (c 0)

/-- The closed point `x̂_0` of `X̂_0` for the standing data. -/
def Standing.xh {N n : ℕ} {X : Scheme.{u}} {ℜ : DatumI.Raw X} {P : DatumI.Presentation ℜ}
    {r : Restriction X} {T : Tower X} {x₀ : X} (hS : Standing N n ℜ P r T x₀) : xHat0 X x₀ :=
  xhat0 X x₀ (hS.ambient.2.1 x₀)

/-! ## The local rings of `X̂_s` over `x̂_0` (for Lemma (AB.2), pp. 295–296) -/

section LocalAlgebra

variable {R R' R'' : Type u} [CommRing R] [CommRing R'] [CommRing R'']

/-- If `α` and `β` transform a regular system of parameters into such a system, so does
`β ∘ α`. -/
theorem _root_.Hironaka.RingHom.MapsRSOP.comp [IsRegularLocalRing R] [IsRegularLocalRing R']
    [IsRegularLocalRing R''] {α : R →+* R'} {β : R' →+* R''} (hβ : RingHom.MapsRSOP β)
    (hα : RingHom.MapsRSOP α) : RingHom.MapsRSOP (β.comp α) := by
  classical
  obtain ⟨s, hs, hs', hinj⟩ := hα
  obtain ⟨h2, hcard2⟩ := hβ.isRegularSystemOfParameters_image hs'
  have himg : (s.image α).image β = s.image (β.comp α) := by
    rw [Finset.image_image, RingHom.coe_comp]
  refine ⟨s, hs, himg ▸ h2, Finset.injOn_of_card_image_eq ?_⟩
  rw [← himg, hcard2, Finset.card_image_of_injOn hinj]

/-- A ring isomorphism of local rings induces a surjective map of residue fields. -/
theorem surjective_residueField_map_ringEquiv [IsLocalRing R] [IsLocalRing R'] (e : R ≃+* R')
    [IsLocalHom (e : R →+* R')] : Function.Surjective (ResidueField.map (e : R →+* R')) := by
  intro w
  obtain ⟨y, rfl⟩ := IsLocalRing.residue_surjective w
  refine ⟨IsLocalRing.residue R (e.symm y), ?_⟩
  rw [ResidueField.map_residue]
  simp

/-- Equal local homomorphisms induce equal maps of residue fields (the instance arguments
may differ). -/
theorem residueField_map_congr [IsLocalRing R] [IsLocalRing R'] {f g : R →+* R'}
    [IsLocalHom f] [IsLocalHom g] (h : f = g) : ResidueField.map f = ResidueField.map g := by
  subst h
  rfl

/-- A ring isomorphism is a local homomorphism. -/
theorem isLocalHom_ringEquiv (e : R ≃+* R') : IsLocalHom (e : R →+* R') :=
  ⟨fun a ha => by simpa using ha.map (e.symm : R' →+* R)⟩

end LocalAlgebra

section CompletionStalks

variable {X : Scheme.{u}}

/-! ### The morphism `c_0 : X̂_0 → X` at the closed point `x̂_0` -/

/-- `c_0(x̂_0) = x_0` (p. 295: "`X̂_0` has the unique closed point `x̂_0` such that
`c_0(x̂_0) = x_0`"). -/
theorem c0_apply_xhat0 (X : Scheme.{u}) (x₀ : X) (hx : X.IsSimpleAt x₀) :
    (c0 X x₀).base (xhat0 X x₀ hx) = x₀ := by
  have : IsRegularLocalRing (X.presheaf.stalk x₀) := hx
  show X.fromSpecStalk x₀ (Spec.map (CommRingCat.ofHom (algebraMap (X.presheaf.stalk x₀)
    (Shat X x₀))) (IsLocalRing.closedPoint (Shat X x₀))) = x₀
  have hloc : IsLocalHom (algebraMap (X.presheaf.stalk x₀) (Shat X x₀)) := inferInstance
  have : IsLocalHom (CommRingCat.ofHom (algebraMap (X.presheaf.stalk x₀) (Shat X x₀))).hom :=
    hloc
  rw [Spec_closedPoint, Scheme.fromSpecStalk_closedPoint]

/-- The local homomorphism induced by `c_0` at `x̂_0` is the canonical homomorphism `S → Ŝ`, up
to the identifications `O_{X, c_0(x̂_0)} = O_{X, x_0} = S` and `O_{X̂_0, x̂_0} = Ŝ`. -/
theorem stalkMap_c0_xhat0 (X : Scheme.{u}) (x₀ : X) (hx : X.IsSimpleAt x₀) :
    haveI : IsRegularLocalRing (X.presheaf.stalk x₀) := hx
    (c0 X x₀).stalkMap (xhat0 X x₀ hx) ≫
        (stalkClosedPointIso (CommRingCat.of (Shat X x₀))).hom =
      (X.presheaf.stalkCongr (Inseparable.of_eq (c0_apply_xhat0 X x₀ hx))).hom ≫
        CommRingCat.ofHom (algebraMap (X.presheaf.stalk x₀) (Shat X x₀)) := by
  have : IsRegularLocalRing (X.presheaf.stalk x₀) := hx
  have hloc : IsLocalHom (CommRingCat.ofHom
      (algebraMap (X.presheaf.stalk x₀) (Shat X x₀))).hom :=
    (inferInstance : IsLocalHom (algebraMap (X.presheaf.stalk x₀) (Shat X x₀)))
  have := (SpecToEquivOfLocalRing X (CommRingCat.of (Shat X x₀))).apply_symm_apply ⟨x₀, _, hloc⟩
  obtain ⟨h1, h'⟩ := SpecToEquivOfLocalRing_eq_iff.mp this
  exact h'

/-- A ring isomorphism in `CommRingCat` between local rings induces a bijection of residue
fields. -/
theorem bijective_residueField_map_of_isIso {A B : CommRingCat.{u}} [IsLocalRing A]
    [IsLocalRing B] (f : A ⟶ B) [IsIso f] : Function.Bijective (ResidueField.map f.hom) := by
  refine ⟨(ResidueField.map f.hom).injective, fun w => ?_⟩
  obtain ⟨y, rfl⟩ := IsLocalRing.residue_surjective w
  refine ⟨IsLocalRing.residue A ((inv f).hom y), ?_⟩
  rw [ResidueField.map_residue, ← CommRingCat.comp_apply, IsIso.inv_hom_id,
    CommRingCat.id_apply]

/-- p. 295 (with Corollary 1 of Lemma 4, Ch. III, for `S → Ŝ`): the local homomorphism
induced by `c_0` at `x̂_0` transforms a regular system of parameters into such a system and
induces an isomorphism of the residue fields. -/
theorem mapsRSOP_and_bijective_residueField_map_stalkMap_c0 (X : Scheme.{u}) (x₀ : X)
    (hx : X.IsSimpleAt x₀) :
    RingHom.MapsRSOP ((c0 X x₀).stalkMap (xhat0 X x₀ hx)).hom ∧
      Function.Bijective (ResidueField.map ((c0 X x₀).stalkMap (xhat0 X x₀ hx)).hom) := by
  have : IsRegularLocalRing (X.presheaf.stalk x₀) := hx
  have hx' : IsRegularLocalRing (X.presheaf.stalk ((c0 X x₀).base (xhat0 X x₀ hx))) := by
    rw [c0_apply_xhat0 X x₀ hx]; exact hx
  let ι := X.presheaf.stalkCongr (Inseparable.of_eq (c0_apply_xhat0 X x₀ hx))
  let κ : (xHat0 X x₀).presheaf.stalk (xhat0 X x₀ hx) ≅ CommRingCat.of (Shat X x₀) :=
    stalkClosedPointIso (CommRingCat.of (Shat X x₀))
  have hreg : IsRegularLocalRing ((xHat0 X x₀).presheaf.stalk (xhat0 X x₀ hx)) :=
    IsRegularLocalRing.of_ringEquiv κ.symm.commRingCatIsoToRingEquiv
  have hκ : IsLocalHom κ.inv.hom := isLocalHom_of_isIso _
  have hι : IsLocalHom ι.hom.hom := isLocalHom_of_isIso _
  have hφ0 : IsLocalHom (algebraMap (X.presheaf.stalk x₀) (Shat X x₀)) := inferInstance
  have h1 : IsLocalHom ((algebraMap (X.presheaf.stalk x₀) (Shat X x₀)).comp ι.hom.hom) :=
    RingHom.isLocalHom_comp _ _
  have h2 : IsLocalHom (κ.inv.hom.comp
      ((algebraMap (X.presheaf.stalk x₀) (Shat X x₀)).comp ι.hom.hom)) :=
    RingHom.isLocalHom_comp _ _
  have e1 : (c0 X x₀).stalkMap (xhat0 X x₀ hx) =
      (ι.hom ≫ CommRingCat.ofHom (algebraMap (X.presheaf.stalk x₀) (Shat X x₀))) ≫ κ.inv :=
    (Iso.eq_comp_inv _).mpr (stalkMap_c0_xhat0 X x₀ hx)
  have e2 : ((c0 X x₀).stalkMap (xhat0 X x₀ hx)).hom = κ.inv.hom.comp
      ((algebraMap (X.presheaf.stalk x₀) (Shat X x₀)).comp ι.hom.hom) := by
    rw [e1]; rfl
  have hφ : IsLocalHom (CommRingCat.ofHom
      (algebraMap (X.presheaf.stalk x₀) (Shat X x₀))).hom :=
    (inferInstance : IsLocalHom (algebraMap (X.presheaf.stalk x₀) (Shat X x₀)))
  refine ⟨?_, ?_⟩
  · rw [e2]
    refine RingHom.MapsRSOP.comp ?_ (RingHom.MapsRSOP.comp ?_ ?_)
    · exact mapsRSOP_ringEquiv κ.symm.commRingCatIsoToRingEquiv
    · exact mapsRSOP_algebraMap_adicCompletion
    · exact mapsRSOP_ringEquiv ι.commRingCatIsoToRingEquiv
  · rw [residueField_map_congr e2, ResidueField.map_comp, ResidueField.map_comp]
    exact (bijective_residueField_map_of_isIso κ.inv).comp
      ((AdicCompletion.residueField_map_bijective _).comp
        (bijective_residueField_map_of_isIso ι.hom))

/-- `κ(x_0) → κ(x̂_0)`, induced by `c_0`, is an isomorphism. -/
theorem isIso_residueFieldMap_c0_xhat0 (X : Scheme.{u}) (x₀ : X) (hx : X.IsSimpleAt x₀) :
    IsIso ((c0 X x₀).residueFieldMap (xhat0 X x₀ hx)) := by
  rw [ConcreteCategory.isIso_iff_bijective]
  exact (mapsRSOP_and_bijective_residueField_map_stalkMap_c0 X x₀ hx).2

/-! ### Commutative squares and stalks -/

/-- A commutative square `f̂ ≫ c = c' ≫ f` of schemes gives a commutative square of local
homomorphisms at a point `ŷ'` (`O_{Y, f(c'(ŷ'))} → O_{Ŷ', ŷ'}`), up to the identification of the
stalks of `Y` at the equal points `f(c'(ŷ')) = c(f̂(ŷ'))`. -/
theorem exists_stalkMap_comm {Y Y' Yh Yh' : Scheme.{u}} {f : Y' ⟶ Y} {fh : Yh' ⟶ Yh}
    {c : Yh ⟶ Y} {c' : Yh' ⟶ Y'} (hcomm : fh ≫ c = c' ≫ f) (yh' : Yh') :
    ∃ h : f.base (c'.base yh') = c.base (fh.base yh'),
      f.stalkMap (c'.base yh') ≫ c'.stalkMap yh' =
        (Y.presheaf.stalkCongr (Inseparable.of_eq h)).hom ≫ c.stalkMap (fh.base yh') ≫
          fh.stalkMap yh' := by
  have h : f.base (c'.base yh') = c.base (fh.base yh') := by
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, hcomm]
  refine ⟨h, ?_⟩
  have A := Scheme.Hom.stalkMap_comp c' f yh'
  have B := Scheme.Hom.stalkMap_comp fh c yh'
  have C := Scheme.Hom.stalkMap_congr_hom (fh ≫ c) (c' ≫ f) hcomm yh'
  have D : (Y.presheaf.stalkCongr (Inseparable.of_eq h)).hom ≫
      (Y.presheaf.stalkCongr (Inseparable.of_eq (hcomm ▸ rfl :
        (fh ≫ c).base yh' = (c' ≫ f).base yh'))).hom = 𝟙 _ := by
    simp only [TopCat.Presheaf.stalkCongr_hom]
    exact (Y.presheaf.stalkSpecializes_comp _ _).trans
      (Y.presheaf.stalkSpecializes_refl (f.base (c'.base yh')))
  have E3 := congrArg (fun g => (Y.presheaf.stalkCongr (Inseparable.of_eq h)).hom ≫ g)
    (B.symm.trans C)
  have E4 := congrArg (fun g => g ≫ (c' ≫ f).stalkMap yh') D
  simp only at E4
  exact A.symm.trans (E4.symm.trans E3.symm)

/-- The stalks of a subscheme at equal points correspond under the identification of the
stalks. -/
theorem stalkIdeal_map_stalkCongr {Y : Scheme.{u}} (D : Subscheme Y) {p q : Y} (h : p = q) :
    (D.stalkIdeal p).map (Y.presheaf.stalkCongr (Inseparable.of_eq h)).hom.hom =
      D.stalkIdeal q := by
  subst h
  simp only [TopCat.Presheaf.stalkCongr_hom, TopCat.Presheaf.stalkSpecializes_refl,
    CommRingCat.hom_id]
  exact Ideal.map_id _

/-! ### One step of the induction of Lemma (AB.2) -/

/-- One step of the proof of Lemma (AB.2) at a point over the center, by Lemma 4 (2), (3) of
Ch. III: let `α : R → Rh` be a local homomorphism of regular local rings which transforms a
regular system of parameters into such a system and induces an isomorphism of residue fields,
`Q` a prime of `R` with `R/Q` regular, `R₁ ≅ R'` a monoidal transform of `R` with center `Q`
and `Rh₁ ≅ Rh'` one of `Rh` with center `QRh`, and `γ : R₁ → Rh₁` a local homomorphism compatible
with `α`.  Then `R₁`, `Rh₁` are regular, `γ` transforms a regular system of parameters into
such a system and induces an isomorphism of residue fields. -/
theorem mapsRSOP_and_surjective_residueField_map_of_monoidalTransform
    {R Rh R₁ Rh₁ : Type u} [CommRing R] [IsRegularLocalRing R] [IsDomain R] [CommRing Rh]
    [IsRegularLocalRing Rh] [IsDomain Rh] [CommRing R₁] [IsLocalRing R₁] [CommRing Rh₁]
    [IsLocalRing Rh₁] (α : R →+* Rh) [IsLocalHom α] (hα : RingHom.MapsRSOP α)
    (hres : Function.Surjective (ResidueField.map α)) {Q : Ideal R} (hQ : Q.IsPrime)
    (hQreg : IsRegularLocalRing (R ⧸ Q)) {Qh : Ideal Rh} (hQh : Qh = Q.map α)
    (tt : MonoidalTransform R Q) (e : tt.ring ≃+* R₁) (tb : MonoidalTransform Rh Qh)
    (eh : tb.ring ≃+* Rh₁) (γ : R₁ →+* Rh₁) [IsLocalHom γ]
    (hcomm : ∀ r, γ (e (tt.toRing r)) = eh (tb.toRing (α r))) :
    IsRegularLocalRing R₁ ∧ IsRegularLocalRing Rh₁ ∧ RingHom.MapsRSOP γ ∧
      Function.Surjective (ResidueField.map γ) := by
  subst hQh
  have hL := RingHom.MapsRSOP.canonicalLift_properties α hα hQ hQreg
  obtain ⟨hQp, hQreg'⟩ := hL.1
  have hQ0 : Q ≠ ⊥ := (Submodule.ne_bot_iff Q).mpr ⟨tt.x, tt.x_mem, tt.x_ne_zero⟩
  have hQ0' : Q.map α ≠ ⊥ := (Submodule.ne_bot_iff _).mpr ⟨tb.x, tb.x_mem, tb.x_ne_zero⟩
  obtain ⟨hreg1, -, -⟩ := tt.isRegularLocalRing_and_isLocalHom_and_span_xR_eq_map hQ hQ0 hQreg
  obtain ⟨hreg2, -, -⟩ :=
    tb.isRegularLocalRing_and_isLocalHom_and_span_xR_eq_map hQp hQ0' hQreg'
  have : IsLocalHom (e : tt.ring →+* R₁) := isLocalHom_ringEquiv e
  have : IsLocalHom (eh.symm : Rh₁ →+* tb.ring) := isLocalHom_ringEquiv eh.symm
  have : IsLocalHom (eh : tb.ring →+* Rh₁) := isLocalHom_ringEquiv eh
  have : IsLocalHom (e.symm : R₁ →+* tt.ring) := isLocalHom_ringEquiv e.symm
  let β : tt.ring →+* tb.ring := (eh.symm : Rh₁ →+* tb.ring).comp (γ.comp (e : tt.ring →+* R₁))
  have hβl : IsLocalHom β := RingHom.isLocalHom_comp _ _
  have hcan : IsCanonicalLift α tt tb β := ⟨hβl, by
    ext r
    simp only [β, RingHom.coe_comp, Function.comp_apply, RingHom.coe_coe, hcomm,
      RingEquiv.symm_apply_apply]⟩
  have hsep : RingHom.IsResiduallySeparableAlgebraic α := by
    let _ := (ResidueField.map α).toAlgebra
    refine ⟨fun x => ?_⟩
    obtain ⟨y, rfl⟩ := hres x
    exact isSeparable_algebraMap y
  obtain ⟨-, -, -, hβinj, hgen⟩ := hL.2.2.1 tt tb β hcan
  obtain ⟨s, hs⟩ := ((isRegularLocalRing_iff_exists_rsop (R := tt.ring)).mp hreg1).2
  have hβ : RingHom.MapsRSOP β := ⟨s, hs, (hL.2.2.2 tt tb β hcan).2 hsep s hs, hβinj.injOn⟩
  have hreg1' : IsRegularLocalRing R₁ := IsRegularLocalRing.of_ringEquiv e
  have hreg2' : IsRegularLocalRing Rh₁ := IsRegularLocalRing.of_ringEquiv eh
  have hγ : γ = (eh : tb.ring →+* Rh₁).comp (β.comp (e.symm : R₁ →+* tt.ring)) := by
    ext x
    simp [β]
  have hβres : Function.Surjective (ResidueField.map β) := by
    intro w
    have hw : w ∈ Subfield.closure
        (Set.range (ResidueField.map (R := tt.ring) (S := tb.ring) β) ∪
          Set.range (ResidueField.map (R := Rh) (S := tb.ring) tb.toRing)) := by
      rw [hgen]; trivial
    have hle : Subfield.closure
        (Set.range (ResidueField.map (R := tt.ring) (S := tb.ring) β) ∪
          Set.range (ResidueField.map (R := Rh) (S := tb.ring) tb.toRing)) ≤
        (ResidueField.map (R := tt.ring) (S := tb.ring) β).fieldRange := by
      rw [Subfield.closure_le]
      rintro _ (h | ⟨z, rfl⟩)
      · exact h
      · obtain ⟨v, rfl⟩ := hres z
        obtain ⟨r, rfl⟩ := IsLocalRing.residue_surjective v
        refine ⟨IsLocalRing.residue _ (tt.toRing r), ?_⟩
        rw [ResidueField.map_residue, ResidueField.map_residue, ResidueField.map_residue]
        have := RingHom.congr_fun hcan.comm r
        simp only [RingHom.coe_comp, Function.comp_apply] at this
        rw [this]
    exact hle hw
  refine ⟨hreg1', hreg2', ?_, ?_⟩
  · rw [hγ]
    exact (mapsRSOP_ringEquiv eh).comp (hβ.comp (mapsRSOP_ringEquiv e.symm))
  · rw [residueField_map_congr hγ, ResidueField.map_comp, ResidueField.map_comp]
    exact (surjective_residueField_map_ringEquiv eh).comp
      (hβres.comp (surjective_residueField_map_ringEquiv e.symm))

/-- One step of the proof of Lemma (AB.2) at a point off the center: if `R → R₁` and
`Rh → Rh₁` are isomorphisms compatible with `α` and `γ`, then `γ` inherits the properties of
`α`. -/
theorem mapsRSOP_and_surjective_residueField_map_of_bijective
    {R Rh R₁ Rh₁ : Type u} [CommRing R] [IsRegularLocalRing R] [CommRing Rh]
    [IsRegularLocalRing Rh] [CommRing R₁] [IsLocalRing R₁] [CommRing Rh₁] [IsLocalRing Rh₁]
    (α : R →+* Rh) [IsLocalHom α] (hα : RingHom.MapsRSOP α)
    (hres : Function.Surjective (ResidueField.map α)) (φ : R →+* R₁) (hφ : Function.Bijective φ)
    (φh : Rh →+* Rh₁) (hφh : Function.Bijective φh) (γ : R₁ →+* Rh₁) [IsLocalHom γ]
    (hcomm : ∀ r, γ (φ r) = φh (α r)) :
    IsRegularLocalRing R₁ ∧ IsRegularLocalRing Rh₁ ∧ RingHom.MapsRSOP γ ∧
      Function.Surjective (ResidueField.map γ) := by
  let e := RingEquiv.ofBijective φ hφ
  let eh := RingEquiv.ofBijective φh hφh
  have hreg1 : IsRegularLocalRing R₁ := IsRegularLocalRing.of_ringEquiv e
  have hreg2 : IsRegularLocalRing Rh₁ := IsRegularLocalRing.of_ringEquiv eh
  have : IsLocalHom (eh : Rh →+* Rh₁) := isLocalHom_ringEquiv eh
  have : IsLocalHom (e.symm : R₁ →+* R) := isLocalHom_ringEquiv e.symm
  have hγ : γ = (eh : Rh →+* Rh₁).comp (α.comp (e.symm : R₁ →+* R)) := by
    ext x
    obtain ⟨r, rfl⟩ := hφ.2 x
    have : e.symm (φ r) = r := e.symm_apply_apply r
    simp [this, hcomm, eh]
  refine ⟨hreg1, hreg2, ?_, ?_⟩
  · rw [hγ]
    exact (mapsRSOP_ringEquiv eh).comp (hα.comp (mapsRSOP_ringEquiv e.symm))
  · rw [residueField_map_congr hγ, ResidueField.map_comp, ResidueField.map_comp]
    exact (surjective_residueField_map_ringEquiv eh).comp
      (hres.comp (surjective_residueField_map_ringEquiv e.symm))

/-- One step of the proof of Lemma (AB.2), for a commutative square `f̂ ≫ c = c' ≫ f` in which
`f` is a monoidal transformation of the non-singular `Y` with non-singular center `B` and `f̂` the
monoidal transformation of `Ŷ` with center `B̂ = c⁻¹(B)`: if `c` transforms a regular system of
parameters of `O_{Y, c(f̂(ŷ'))}` into such a system of `O_{Ŷ, f̂(ŷ')}` (a regular local ring) and
induces an isomorphism of residue fields, then `O_{Ŷ', ŷ'}` is regular and `c'` has the same two
properties at `ŷ'`.  At a point over the center this is Lemma 4 (2), (3) of Ch. III; off the
center `f` and `f̂` are local isomorphisms. -/
theorem _root_.Hironaka.MonoidalTransformation.mapsRSOP_stalkMap_of_comm {Y Yh : Scheme.{u}}
    {B : Subscheme Y}
    {Bh : Subscheme Yh} (t : MonoidalTransformation Y B) (th : MonoidalTransformation Yh Bh)
    (c : Yh ⟶ Y) (c' : th.X' ⟶ t.X') (hBh : Bh = Subscheme.totalTransform c B)
    (hcomm : th.f ≫ c = c' ≫ t.f) (hY : Y.IsNonsingular) (hB : B.IsNonsingular) (yh' : th.X')
    [IsRegularLocalRing (Yh.presheaf.stalk (th.f.base yh'))]
    (hα : RingHom.MapsRSOP (c.stalkMap (th.f.base yh')).hom)
    (hres : Function.Surjective (ResidueField.map (c.stalkMap (th.f.base yh')).hom)) :
    IsRegularLocalRing (th.X'.presheaf.stalk yh') ∧ RingHom.MapsRSOP (c'.stalkMap yh').hom ∧
      Function.Surjective (ResidueField.map (c'.stalkMap yh').hom) := by
  subst hBh
  obtain ⟨h, hsq⟩ := exists_stalkMap_comm hcomm yh'
  have : IsRegularLocalRing (Y.presheaf.stalk (t.f.base (c'.base yh'))) := hY _
  have : IsRegularLocalRing (Y.presheaf.stalk (c.base (th.f.base yh'))) := hY _
  have : IsDomain (Y.presheaf.stalk (t.f.base (c'.base yh'))) :=
    isDomain_of_isRegularLocalRing _
  have : IsDomain (Yh.presheaf.stalk (th.f.base yh')) := isDomain_of_isRegularLocalRing _
  let ι := Y.presheaf.stalkCongr (Inseparable.of_eq h)
  have hι : IsLocalHom ι.hom.hom := isLocalHom_of_isIso _
  let α := (c.stalkMap (th.f.base yh')).hom.comp ι.hom.hom
  have hαl : IsLocalHom α := RingHom.isLocalHom_comp _ _
  have hα' : RingHom.MapsRSOP α := hα.comp (mapsRSOP_ringEquiv ι.commRingCatIsoToRingEquiv)
  have hres' : Function.Surjective (ResidueField.map α) := by
    rw [ResidueField.map_comp]
    exact hres.comp (bijective_residueField_map_of_isIso ι.hom).2
  have hcomm' : ∀ r, (c'.stalkMap yh').hom ((t.f.stalkMap (c'.base yh')).hom r) =
      (th.f.stalkMap yh').hom (α r) := fun r => by
    exact congrArg (fun g => g.hom r) hsq
  by_cases hyB : t.f.base (c'.base yh') ∈ B.pts
  · have hQ := Subscheme.isPrime_stalkIdeal_of_isNonsingular hB hyB
    have hQreg := Subscheme.isRegularLocalRing_quotient_of_isNonsingular hB hyB
    obtain ⟨tt, e, he⟩ := t.exists_monoidalTransform_stalk (c'.base yh')
    obtain ⟨tb, eh, heh⟩ := th.exists_monoidalTransform_stalk yh'
    have hQh : (Subscheme.totalTransform c B).stalkIdeal (th.f.base yh') =
        (B.stalkIdeal (t.f.base (c'.base yh'))).map α := by
      rw [stalkIdeal_totalTransform, ← Ideal.map_map, stalkIdeal_map_stalkCongr B h]
    refine (mapsRSOP_and_surjective_residueField_map_of_monoidalTransform α hα' hres' hQ hQreg
      hQh tt e tb eh (c'.stalkMap yh').hom fun r => ?_).2
    have h1 := RingHom.congr_fun he r
    have h2 := RingHom.congr_fun heh (α r)
    simp only [RingEquiv.toRingHom_eq_coe, RingHom.coe_comp, Function.comp_apply,
      RingHom.coe_coe] at h1 h2
    rw [h1, h2, hcomm']
  · have hyBh : th.f.base yh' ∉ (Subscheme.totalTransform c B).pts := by
      have hyB' : c.base (th.f.base yh') ∉ B.pts := h ▸ hyB
      rw [Subscheme.mem_pts_iff_stalkIdeal_ne_top, not_not, stalkIdeal_totalTransform,
        Subscheme.stalkIdeal_eq_top_of_notMem_pts hyB', Ideal.map_top]
    exact (mapsRSOP_and_surjective_residueField_map_of_bijective α hα' hres'
      (t.f.stalkMap (c'.base yh')).hom (t.bijective_stalkMap_of_notMem _ hyB)
      (th.f.stalkMap yh').hom (th.bijective_stalkMap_of_notMem _ hyBh)
      (c'.stalkMap yh').hom hcomm').2

/-- Appending a monoidal transformation composes the composite morphism with it. -/
theorem _root_.Hironaka.MonoidalSuccession.composite_snoc {X Y : Scheme.{u}}
    (g : MonoidalSuccession X Y) (B : Subscheme Y) (t : MonoidalTransformation Y B) :
    (Hironaka.MonoidalSuccession.snoc g B t).composite = t.f ≫ g.composite := by
  induction g with
  | nil X =>
    show MonoidalSuccession.composite (MonoidalSuccession.nil t.X') ≫ t.f = t.f ≫ 𝟙 X
    simp
  | cons B' t' rest ih =>
    show (Hironaka.MonoidalSuccession.snoc rest B t).composite ≫ t'.f =
      t.f ≫ (rest.composite ≫ t'.f)
    rw [ih, Category.assoc]

/-- `ĝ_{s+1} = f̂_s ≫ ĝ_s`. -/
theorem Tower.composite_pre_succ {X₀ : Scheme.{u}} (T : Tower X₀) (s : ℕ) :
    (T.pre (s + 1)).composite = T.f s ≫ (T.pre s).composite :=
  Hironaka.MonoidalSuccession.composite_snoc (T.pre s) (T.B s) (T.monoidalTransformation s)

variable {T : Tower X} {x₀ : X}

/-- The local ring of `X̂_0` at `x̂_0` is regular (it is `Ŝ`). -/
theorem isRegularLocalRing_stalk_xhat0 (hx : X.IsSimpleAt x₀) :
    IsRegularLocalRing ((xHat0 X x₀).presheaf.stalk (xhat0 X x₀ hx)) := by
  have : IsRegularLocalRing (X.presheaf.stalk x₀) := hx
  exact IsRegularLocalRing.of_ringEquiv
    (stalkClosedPointIso (CommRingCat.of (Shat X x₀))).symm.commRingCatIsoToRingEquiv

/-- **Lemma (AB.2)**, second assertion, with the regularity of the local rings of `X̂_s` at the
points over `x̂_0` and the isomorphism of residue fields, for a given `Completion` of a
succession with non-singular `X_s` and non-singular centers `B_s`: induction on `s`, the step
being Lemma 4 (2), (3) of Ch. III (`MonoidalTransformation.mapsRSOP_stalkMap_of_comm`) and the
case `s = 0` Corollary 1 of Lemma 4 for `S → Ŝ`. -/
theorem Completion.isRegularLocalRing_and_mapsRSOP_stalkMap (𝒞 : Completion T x₀)
    (hx : X.IsSimpleAt x₀) (hX : ∀ s, (T.X s).IsNonsingular) (hB : ∀ s, (T.B s).IsNonsingular) :
    ∀ (s : ℕ) (yh : 𝒞.tHat.X s), (𝒞.tHat.pre s).composite.base yh = xhat0 X x₀ hx →
      IsRegularLocalRing ((𝒞.tHat.X s).presheaf.stalk yh) ∧
        RingHom.MapsRSOP ((𝒞.c s).stalkMap yh).hom ∧
        Function.Surjective (ResidueField.map ((𝒞.c s).stalkMap yh).hom)
  | 0, yh, hyh => by
    have hyh' : yh = xhat0 X x₀ hx := hyh
    subst hyh'
    have h0 := mapsRSOP_and_bijective_residueField_map_stalkMap_c0 X x₀ hx
    refine ⟨isRegularLocalRing_stalk_xhat0 hx, ?_⟩
    rw [𝒞.c_zero]
    exact ⟨h0.1, h0.2.2⟩
  | s + 1, yh, hyh => by
    have hyh' : (𝒞.tHat.pre s).composite.base ((𝒞.tHat.f s).base yh) = xhat0 X x₀ hx :=
      (congrArg (fun φ => φ.base yh) (Tower.composite_pre_succ 𝒞.tHat s)).symm.trans hyh
    obtain ⟨hreg, hα, hres⟩ := 𝒞.isRegularLocalRing_and_mapsRSOP_stalkMap hx hX hB s _ hyh'
    have : IsRegularLocalRing ((𝒞.tHat.X s).presheaf.stalk
        ((𝒞.tHat.monoidalTransformation s).f.base yh)) := hreg
    exact MonoidalTransformation.mapsRSOP_stalkMap_of_comm (T.monoidalTransformation s)
      (𝒞.tHat.monoidalTransformation s) (𝒞.c s) (𝒞.c (s + 1)) (𝒞.B_hat s) (𝒞.c_comm s) (hX s)
      (hB s) yh hα hres

/-- **Lemma (AB.2)**, first assertion, along the printed route (p. 295): "The morphism `c_s` induces a
bijective mapping of the point sets `ĝ_s⁻¹(x̂_0) → g_s⁻¹(x_0)`", "an immediate consequence of Lemma 4,
§2, Ch. III, and its corollaries".  By induction on `s`: for `s = 0` both sets are the points `x̂_0`,
`x_0` (`c_0(x̂_0) = x_0`).  Step: the points of `X̂_{s+1}` over `ŷ ∈ ĝ_s⁻¹(x̂_0)` are the points whose local
rings are the monoidal transforms `R̃'` of `R̃ = O_{X̂_s,ŷ}` with center `B̂_ŷ = B_y R̃` (`y = c_s(ŷ)`), those of
`X_{s+1}` over `y` the monoidal transforms `R'` of `R = O_{X_s,y}` with center `B_y`, and `c_{s+1}` sends
`R̃'` to the `R'` with a canonical homomorphism `R' → R̃'`; by the count of Lemma 4 (1) (the number of `R̃'` over a
given `R'` is at most the separable degree `[k̃ : k]_s = 1` of the residue field extension, which is an isomorphism
by Corollary 1 at `s = 0` and then by the second assertion carried along,
`Completion.isRegularLocalRing_and_mapsRSOP_stalkMap`) `c_{s+1}` is injective on these points, and every `R'` has a
canonical lift `R̃'` which is the local ring of a point of `X̂_{s+1}` over `ŷ`
(`MonoidalTransformation.bijOn_fibre_of_comm`, `Hironaka/Compat/BlowupFibreBijection.lean`).  Lemma 4 is
applied to the stalks, so the `X_s` and the `B_s` are non-singular, as in the second assertion (the standing
assumptions of §3). -/
theorem Completion.bijOn_c_of_isNonsingular (𝒞 : Completion T x₀) (hx : X.IsSimpleAt x₀)
    (hX : ∀ s, (T.X s).IsNonsingular) (hB : ∀ s, (T.B s).IsNonsingular) (s : ℕ) :
    Set.BijOn (𝒞.c s).base ((𝒞.tHat.pre s).composite.base ⁻¹' {xhat0 X x₀ hx})
      ((T.pre s).composite.base ⁻¹' {x₀}) := by
  induction s with
  | zero =>
    have hc0 : (𝒞.c 0).base (xhat0 X x₀ hx) = x₀ := by
      rw [𝒞.c_zero]; exact c0_apply_xhat0 X x₀ hx
    have h1 : (𝒞.tHat.pre 0).composite.base ⁻¹' {xhat0 X x₀ hx} = {xhat0 X x₀ hx} :=
      Set.ext fun _ => Iff.rfl
    have h2 : (T.pre 0).composite.base ⁻¹' {x₀} = {x₀} := Set.ext fun _ => Iff.rfl
    rw [h1, h2]
    exact Set.bijOn_singleton.mpr hc0
  | succ s IH =>
    have hfst : ∀ ŷ' : 𝒞.tHat.X (s + 1), (𝒞.tHat.pre (s + 1)).composite.base ŷ' =
        (𝒞.tHat.pre s).composite.base ((𝒞.tHat.f s).base ŷ') := fun ŷ' =>
      congrArg (fun φ => φ.base ŷ') (Tower.composite_pre_succ 𝒞.tHat s)
    have hfst' : ∀ y' : T.X (s + 1), (T.pre (s + 1)).composite.base y' =
        (T.pre s).composite.base ((T.f s).base y') := fun y' =>
      congrArg (fun φ => φ.base y') (Tower.composite_pre_succ T s)
    have hcomm : ∀ ŷ' : 𝒞.tHat.X (s + 1), (𝒞.c s).base ((𝒞.tHat.f s).base ŷ') =
        (T.f s).base ((𝒞.c (s + 1)).base ŷ') := fun ŷ' =>
      congrArg (fun φ => φ.base ŷ') (𝒞.c_comm s)
    -- the one-step count of Lemma 4 (1): `c_{s+1}` maps `f̂_s⁻¹(ŷ)` bijectively onto `f_s⁻¹(c_s ŷ)`
    have hfib : ∀ ŷ : 𝒞.tHat.X s, (𝒞.tHat.pre s).composite.base ŷ = xhat0 X x₀ hx →
        Set.BijOn (𝒞.c (s + 1)).base ((𝒞.tHat.f s).base ⁻¹' {ŷ})
          ((T.f s).base ⁻¹' {(𝒞.c s).base ŷ}) := fun ŷ hŷ => by
      obtain ⟨hreg, hα, hres⟩ := 𝒞.isRegularLocalRing_and_mapsRSOP_stalkMap hx hX hB s ŷ hŷ
      exact MonoidalTransformation.bijOn_fibre_of_comm (T.monoidalTransformation s)
        (𝒞.tHat.monoidalTransformation s) (𝒞.c s) (𝒞.c (s + 1)) (𝒞.c_comm s) (𝒞.B_hat s)
        (hX s) (hB s) ŷ hα hres
    refine ⟨fun ŷ' hŷ' => ?_, fun ŷ₁ hŷ₁ ŷ₂ hŷ₂ hc => ?_, fun y' hy' => ?_⟩
    · simp only [Set.mem_preimage, Set.mem_singleton_iff] at hŷ' ⊢
      have h1 : (𝒞.tHat.pre s).composite.base ((𝒞.tHat.f s).base ŷ') = xhat0 X x₀ hx :=
        (hfst ŷ').symm.trans hŷ'
      have h2 : (T.f s).base ((𝒞.c (s + 1)).base ŷ') = (𝒞.c s).base ((𝒞.tHat.f s).base ŷ') :=
        (hfib _ h1).mapsTo (show ŷ' ∈ (𝒞.tHat.f s).base ⁻¹' {(𝒞.tHat.f s).base ŷ'} from rfl)
      have h3 := IH.mapsTo (show (𝒞.tHat.f s).base ŷ' ∈
        (𝒞.tHat.pre s).composite.base ⁻¹' {xhat0 X x₀ hx} from h1)
      simp only [Set.mem_preimage, Set.mem_singleton_iff] at h3
      rw [hfst', h2]
      exact h3
    · simp only [Set.mem_preimage, Set.mem_singleton_iff] at hŷ₁ hŷ₂
      have h1 : (𝒞.tHat.pre s).composite.base ((𝒞.tHat.f s).base ŷ₁) = xhat0 X x₀ hx :=
        (hfst ŷ₁).symm.trans hŷ₁
      have h2 : (𝒞.tHat.pre s).composite.base ((𝒞.tHat.f s).base ŷ₂) = xhat0 X x₀ hx :=
        (hfst ŷ₂).symm.trans hŷ₂
      have hcc : (𝒞.c s).base ((𝒞.tHat.f s).base ŷ₁) = (𝒞.c s).base ((𝒞.tHat.f s).base ŷ₂) := by
        rw [hcomm, hcomm, hc]
      have heq : (𝒞.tHat.f s).base ŷ₁ = (𝒞.tHat.f s).base ŷ₂ := IH.injOn h1 h2 hcc
      exact (hfib _ h1).injOn (show ŷ₁ ∈ (𝒞.tHat.f s).base ⁻¹' {(𝒞.tHat.f s).base ŷ₁} from rfl)
        (show ŷ₂ ∈ (𝒞.tHat.f s).base ⁻¹' {(𝒞.tHat.f s).base ŷ₁} from heq.symm) hc
    · simp only [Set.mem_preimage, Set.mem_singleton_iff] at hy'
      have h1 : (T.pre s).composite.base ((T.f s).base y') = x₀ := (hfst' y').symm.trans hy'
      obtain ⟨ŷ, hŷ, hcŷ⟩ := IH.surjOn
        (show (T.f s).base y' ∈ (T.pre s).composite.base ⁻¹' {x₀} from h1)
      have hŷ' : (𝒞.tHat.pre s).composite.base ŷ = xhat0 X x₀ hx := hŷ
      obtain ⟨ŷ', hŷ'1, hŷ'2⟩ := (hfib ŷ hŷ').surjOn
        (show y' ∈ (T.f s).base ⁻¹' {(𝒞.c s).base ŷ} from hcŷ.symm)
      refine ⟨ŷ', ?_, hŷ'2⟩
      simp only [Set.mem_preimage, Set.mem_singleton_iff] at hŷ'1 ⊢
      rw [hfst, hŷ'1]
      exact hŷ'

/-! ### The standing succession: non-singularity of the `X_s` and of the centers `B_s` -/

/-- The last center of a permissible succession `g` followed by `t` (with center `B`) is a
permissible center for the transform of the datum along `g` (Definition 8, p. 169). -/
theorem isPermissible_transformI_of_isPermissibleI_snoc {X' Y : Scheme.{u}}
    (g : MonoidalSuccession X' Y) (B : Subscheme Y) (t : MonoidalTransformation Y B)
    (ℜ : DatumI.Raw X') (h : (Hironaka.MonoidalSuccession.snoc g B t).IsPermissibleI ℜ) :
    (g.transformI ℜ).IsPermissible B := by
  induction g with
  | nil X => exact h.1
  | cons B' t' rest ih => exact ih B t (ℜ.transform t') h.2

/-- The last center of a succession `g` followed by `t` (with center `B`), permissible for
`(ℜ, F)`, is a permissible center for the transform of `(ℜ, F)` along `g` (Definition 6,
p. 168); in particular `B ⊆ W' ∩ F'`, `F'` being the strict transform of `F` along `g`. -/
theorem isPermissibleClosed_transformI_of_isPermissibleIClosed_snoc {X' Y : Scheme.{u}}
    (g : MonoidalSuccession X' Y) (B : Subscheme Y) (t : MonoidalTransformation Y B)
    (ℜ : DatumI.Raw X') (F : Subscheme X')
    (h : (Hironaka.MonoidalSuccession.snoc g B t).IsPermissibleIClosed ℜ F) :
    (g.transformI ℜ).IsPermissibleClosed (g.strictTransform F) B := by
  induction g with
  | nil X => exact h.1
  | cons B' t' rest ih => exact ih B t (ℜ.transform t') _ h.2

/-- The centers `B_s` of the standing permissible succession are non-singular (Definition 6,
p. 167). -/
theorem Standing.isNonsingular_B {N n : ℕ} {ℜ : DatumI.Raw X} {P : DatumI.Presentation ℜ}
    {r : Restriction X} (hS : Standing N n ℜ P r T x₀) (s : ℕ) : (T.B s).IsNonsingular :=
  (isPermissible_transformI_of_isPermissibleI_snoc (T.pre s) (T.B s)
    (T.monoidalTransformation s) ℜ (hS.permissible (s + 1)).isPermissibleI).1.isNonsingular

/-- The schemes `X_s` of the standing permissible succession are non-singular (p. 142). -/
theorem Standing.isNonsingular_X {N n : ℕ} {ℜ : DatumI.Raw X} {P : DatumI.Presentation ℜ}
    {r : Restriction X} (hS : Standing N n ℜ P r T x₀) : ∀ s, (T.X s).IsNonsingular
  | 0 => hS.ambient.2.1
  | s + 1 => ((T.monoidalTransformation s).isNonsingular_and_isNonsingular_exceptional
      (hS.isNonsingular_X s) (hS.isNonsingular_B s)).1

end CompletionStalks

/-! ## Existence of the completion datum; `X̂_0` is algebraic (p. 295) -/

section CompletionExists

variable {X : Scheme.{u}}

/-- `c_0 : X̂_0 → X` is flat: `S → Ŝ` is flat and `Spec(S) → X` is flat. -/
theorem flat_c0 (X : Scheme.{u}) (x₀ : X) (hx : X.IsSimpleAt x₀) : Flat (c0 X x₀) := by
  have : IsRegularLocalRing (X.presheaf.stalk x₀) := hx
  have := faithfullyFlat_adicCompletion_maximalIdeal (X.presheaf.stalk x₀)
  have h1 : Flat (Spec.map (CommRingCat.ofHom
      (algebraMap (X.presheaf.stalk x₀) (Shat X x₀)))) :=
    Flat.SpecMap_iff.mpr (RingHom.flat_algebraMap_iff.mpr inferInstance)
  have := flat_fromSpecStalk X x₀
  exact (inferInstance : Flat (Spec.map (CommRingCat.ofHom
      (algebraMap (X.presheaf.stalk x₀) (Shat X x₀))) ≫ X.fromSpecStalk x₀))

/-- The schemes `X̂_s = X_s ×_{X_{s-1}} X̂_{s-1}` (`X̂_0 = Spec(Ŝ)`) with their flat projections
`c_s : X̂_s → X_s`, built by successive base changes along the `f_s`. -/
noncomputable def completionStage (T : Tower X) (x₀ : X) (hx : X.IsSimpleAt x₀) :
    (s : ℕ) → Σ Y : Scheme.{u}, {c : Y ⟶ T.X s // Flat c}
  | 0 => ⟨xHat0 X x₀, c0 X x₀, flat_c0 X x₀ hx⟩
  | s + 1 =>
    haveI := (completionStage T x₀ hx s).2.2
    ⟨pullback (T.f s) (completionStage T x₀ hx s).2.1, pullback.fst _ _, inferInstance⟩

variable (T : Tower X) (x₀ : X) (hx : X.IsSimpleAt x₀)

/-- The schemes `X̂_{s+1}`. -/
noncomputable def completionXSucc (s : ℕ) : Scheme.{u} := (completionStage T x₀ hx (s + 1)).1

/-- The morphisms `c_s : X̂_s → X_s` (`c_0` induced by `S → Ŝ`). -/
noncomputable def completionC :
    ∀ s, towerScheme (xHat0 X x₀) (completionXSucc T x₀ hx) s ⟶ T.X s
  | 0 => c0 X x₀
  | s + 1 => (completionStage T x₀ hx (s + 1)).2.1

/-- The morphisms `f̂_s : X̂_{s+1} → X̂_s`, the second projections. -/
noncomputable def completionF :
    ∀ s, towerScheme (xHat0 X x₀) (completionXSucc T x₀ hx) (s + 1) ⟶
      towerScheme (xHat0 X x₀) (completionXSucc T x₀ hx) s
  | 0 => pullback.snd (T.f 0) (c0 X x₀)
  | s + 1 => pullback.snd (T.f (s + 1)) (completionStage T x₀ hx (s + 1)).2.1

/-- The morphisms `c_s` are flat. -/
theorem flat_completionC : ∀ s, Flat (completionC T x₀ hx s)
  | 0 => flat_c0 X x₀ hx
  | s + 1 => (completionStage T x₀ hx (s + 1)).2.2

/-- The square `c_{s+1}`, `f̂_s`, `f_s`, `c_s` is a pullback square. -/
theorem isPullback_completionC_succ (s : ℕ) :
    IsPullback (completionC T x₀ hx (s + 1)) (completionF T x₀ hx s) (T.f s)
      (completionC T x₀ hx s) := by
  cases s with
  | zero => exact IsPullback.of_hasPullback (T.f 0) (c0 X x₀)
  | succ s => exact IsPullback.of_hasPullback (T.f (s + 1)) (completionStage T x₀ hx (s + 1)).2.1

/-- `f̂_s` is the monoidal transformation of `X̂_s` with center `c_s⁻¹(B_s)` (flat base change,
`MonoidalTransformation.baseChange`). -/
theorem isMonoidalTransformationOf_completionF (s : ℕ) :
    IsMonoidalTransformationOf (completionF T x₀ hx s)
      (Subscheme.totalTransform (completionC T x₀ hx s) (T.B s)) := by
  cases s with
  | zero =>
    have : Flat (completionC T x₀ hx 0) := flat_c0 X x₀ hx
    let bc := (T.monoidalTransformation 0).baseChange (completionC T x₀ hx 0)
    exact ⟨bc.invertible, bc.universal⟩
  | succ s =>
    have : Flat (completionC T x₀ hx (s + 1)) := (completionStage T x₀ hx (s + 1)).2.2
    let bc := (T.monoidalTransformation (s + 1)).baseChange (completionC T x₀ hx (s + 1))
    exact ⟨bc.invertible, bc.universal⟩

/-- The induced succession `{f̂_s : X̂_{s+1} → X̂_s}` of `X̂_0 = Spec(Ŝ)`: `f̂_s` is the monoidal
transformation of `X̂_s` with center `c_s⁻¹(B_s)`. -/
noncomputable def completionTower : Tower (xHat0 X x₀) where
  xSucc := completionXSucc T x₀ hx
  B s := Subscheme.totalTransform (completionC T x₀ hx s) (T.B s)
  f := completionF T x₀ hx
  isMonoidal := isMonoidalTransformationOf_completionF T x₀ hx

/-- `X̂_s = X_s ×_X X̂_0`, with projections `c_s` and `ĝ_s`. -/
theorem isPullback_completionC :
    ∀ s, IsPullback (completionC T x₀ hx s) ((completionTower T x₀ hx).pre s).composite
      (T.pre s).composite (completionC T x₀ hx 0)
  | 0 => IsPullback.id_vert (c0 X x₀)
  | s + 1 => by
    have h := (isPullback_completionC_succ T x₀ hx s).paste_vert (isPullback_completionC s)
    rw [Tower.composite_pre_succ, Tower.composite_pre_succ]
    exact h

/-- The canonical completion datum of p. 295, constructed by flat base change: `X̂_s = X_s ×_X X̂_0`,
`c_s` the first projection, `f̂_s` the second projection of `X̂_{s+1} = X_{s+1} ×_{X_s} X̂_s`.  This is the
datum over which the frames of §3 and §4 are built (`Frame.canon`, `StageState`): there `X̂_{s+1}` is the
fibre product by definition, which the bridge `Frame.canon_stageOf_succ_xHat` uses definitionally.  That it
is a completion datum is proved here by flat base change; the existence of the datum in the order of the
paper, from the monoidal transformations `f̂_s` (`Tower.completionOfBlowups`), is `nonempty_completion`. -/
noncomputable def Tower.completion : Completion T x₀ where
  tHat := completionTower T x₀ hx
  c := completionC T x₀ hx
  c_zero := rfl
  c_comm s := (isPullback_completionC_succ T x₀ hx s).w.symm
  B_hat _ := rfl
  isPullback := isPullback_completionC T x₀ hx

/-- The morphisms `c_s` of `Tower.completion` are flat. -/
theorem Tower.flat_completion_c (s : ℕ) : Flat ((T.completion x₀ hx).c s) :=
  flat_completionC T x₀ hx s

section PrintedOrder

/-- p. 295: "`f̂_s` is the monoidal transformation of `X̂_s` with the non-singular center `B̂_s = c_s⁻¹(B_s)`":
a monoidal transformation of `Ŷ` with center `c⁻¹(B_s)`, for a morphism `c : Ŷ → X_s`.  It exists by
Grothendieck, EGA II §3 (cited by the paper, footnote 33, p. 166; `MonoidalTransformation.exists_isProper`);
one is chosen. -/
noncomputable def completionBlowup [Hironaka.HironakaCitedResults.{u}] (s : ℕ) {Y : Scheme.{u}} (c : Y ⟶ T.X s) :
    MonoidalTransformation Y (Subscheme.totalTransform c (T.B s)) :=
  (MonoidalTransformation.exists_isProper Y (Subscheme.totalTransform c (T.B s))).choose

/-- The canonical morphism `c_{s+1} : X̂_{s+1} → X_{s+1}` of the diagram of p. 295: for the monoidal
transformation `f̂_s` of `Ŷ` with center `c_s⁻¹(B_s)`, the pull-back of `B_s` by `f̂_s ≫ c_s` is the
invertible ideal `f̂_s⁻¹(c_s⁻¹(B_s))`, so `f̂_s ≫ c_s` factors through the monoidal transformation `f_s` of `X_s`
with center `B_s` (universal mapping property, p. 166). -/
noncomputable def completionLift [Hironaka.HironakaCitedResults.{u}] (s : ℕ) {Y : Scheme.{u}} (c : Y ⟶ T.X s) :
    (completionBlowup T s c).X' ⟶ T.X (s + 1) :=
  ((T.monoidalTransformation s).universal (completionBlowup T s c).X'
    ((completionBlowup T s c).f ≫ c) (by
      rw [Subscheme.totalTransform_comp]
      exact (completionBlowup T s c).invertible)).exists.choose

/-- The commutative diagram of p. 295: `f_s ∘ c_{s+1} = c_s ∘ f̂_s`. -/
theorem completionLift_f [Hironaka.HironakaCitedResults.{u}] (s : ℕ) {Y : Scheme.{u}} (c : Y ⟶ T.X s) :
    completionLift T s c ≫ T.f s = (completionBlowup T s c).f ≫ c :=
  ((T.monoidalTransformation s).universal (completionBlowup T s c).X'
    ((completionBlowup T s c).f ≫ c) (by
      rw [Subscheme.totalTransform_comp]
      exact (completionBlowup T s c).invertible)).exists.choose_spec

/-- The schemes `X̂_s` with the morphisms `c_s : X̂_s → X_s`, in the order of p. 295: `X̂_0 = Spec(Ŝ)` with
`c_0` induced by `S → Ŝ`; `f̂_s : X̂_{s+1} → X̂_s` the monoidal transformation with center `c_s⁻¹(B_s)`, and
`c_{s+1}` the canonical morphism with `f_s ∘ c_{s+1} = c_s ∘ f̂_s`. -/
noncomputable def blowupStage [Hironaka.HironakaCitedResults.{u}] : (s : ℕ) → Σ Y : Scheme.{u}, Y ⟶ T.X s
  | 0 => ⟨xHat0 X x₀, c0 X x₀⟩
  | s + 1 => ⟨(completionBlowup T s (blowupStage s).2).X',
      completionLift T s (blowupStage s).2⟩

/-- The schemes `X̂_{s+1}`. -/
noncomputable def blowupXSucc [Hironaka.HironakaCitedResults.{u}] (s : ℕ) : Scheme.{u} := (blowupStage T x₀ (s + 1)).1

/-- The morphisms `c_s : X̂_s → X_s` (`c_0` induced by `S → Ŝ`). -/
noncomputable def blowupC [Hironaka.HironakaCitedResults.{u}] :
    ∀ s, towerScheme (xHat0 X x₀) (blowupXSucc T x₀) s ⟶ T.X s
  | 0 => c0 X x₀
  | s + 1 => (blowupStage T x₀ (s + 1)).2

/-- The morphisms `f̂_s : X̂_{s+1} → X̂_s`, the monoidal transformations with center `c_s⁻¹(B_s)`. -/
noncomputable def blowupF [Hironaka.HironakaCitedResults.{u}] :
    ∀ s, towerScheme (xHat0 X x₀) (blowupXSucc T x₀) (s + 1) ⟶
      towerScheme (xHat0 X x₀) (blowupXSucc T x₀) s
  | 0 => (completionBlowup T 0 (c0 X x₀)).f
  | s + 1 => (completionBlowup T (s + 1) (blowupStage T x₀ (s + 1)).2).f

/-- The commutative diagrams `c_s ∘ f̂_s = f_s ∘ c_{s+1}` of p. 295. -/
theorem blowupF_comp_c [Hironaka.HironakaCitedResults.{u}] (s : ℕ) :
    blowupF T x₀ s ≫ blowupC T x₀ s = blowupC T x₀ (s + 1) ≫ T.f s :=
  match s with
  | 0 => (completionLift_f T 0 (c0 X x₀)).symm
  | s + 1 => (completionLift_f T (s + 1) (blowupStage T x₀ (s + 1)).2).symm

/-- `f̂_s` is the monoidal transformation of `X̂_s` with center `c_s⁻¹(B_s)` (by construction). -/
theorem isMonoidalTransformationOf_blowupF [Hironaka.HironakaCitedResults.{u}] (s : ℕ) :
    IsMonoidalTransformationOf (blowupF T x₀ s)
      (Subscheme.totalTransform (blowupC T x₀ s) (T.B s)) :=
  match s with
  | 0 => ⟨(completionBlowup T 0 (c0 X x₀)).invertible, (completionBlowup T 0 (c0 X x₀)).universal⟩
  | s + 1 => ⟨(completionBlowup T (s + 1) (blowupStage T x₀ (s + 1)).2).invertible,
      (completionBlowup T (s + 1) (blowupStage T x₀ (s + 1)).2).universal⟩

/-- The induced succession `{f̂_s : X̂_{s+1} → X̂_s}` of `X̂_0 = Spec(Ŝ)`: `f̂_s` is the monoidal
transformation of `X̂_s` with center `c_s⁻¹(B_s)`. -/
noncomputable def blowupTower [Hironaka.HironakaCitedResults.{u}] : Tower (xHat0 X x₀) where
  xSucc := blowupXSucc T x₀
  B s := Subscheme.totalTransform (blowupC T x₀ s) (T.B s)
  f := blowupF T x₀
  isMonoidal := isMonoidalTransformationOf_blowupF T x₀

/-- p. 295: "In view of the fact that `Ŝ` is faithfully flat over `S`, one can show that `X̂_s` is
canonically isomorphic to the product `X_s ×_X X̂_0` in the category of schemes over `X` and that `c_s` is
the projection to the first factor": by induction on `s`, the `c_s` are flat and the squares
`(c_s, ĝ_s, g_s, c_0)` are pullback squares.  For `s = 0` this is `c_0` (flat, `flat_c0`); the step is the
square `(c_{s+1}, f̂_s, f_s, c_s)`, a pullback square because `c_s` is flat and `f̂_s` is a monoidal
transformation with center `c_s⁻¹(B_s)` (`MonoidalTransformation.isPullback_of_flat`: flat base change of
`f_s` is another such monoidal transformation, and the two are canonically isomorphic); it makes `c_{s+1}` flat
and pastes with the square for `s`. -/
theorem flat_and_isPullback_blowupC [Hironaka.HironakaCitedResults.{u}] (hx : X.IsSimpleAt x₀) :
    ∀ s, Flat (blowupC T x₀ s) ∧
      IsPullback (blowupC T x₀ s) ((blowupTower T x₀).pre s).composite
        (T.pre s).composite (blowupC T x₀ 0)
  | 0 => ⟨flat_c0 X x₀ hx, IsPullback.id_vert (c0 X x₀)⟩
  | s + 1 => by
    obtain ⟨hflat, hpb⟩ := flat_and_isPullback_blowupC hx s
    have hsq : IsPullback (blowupC T x₀ (s + 1)) (blowupF T x₀ s) (T.f s)
        (blowupC T x₀ s) := by
      have := hflat
      exact (T.monoidalTransformation s).isPullback_of_flat (blowupC T x₀ s)
        ((blowupTower T x₀).monoidalTransformation s) (blowupC T x₀ (s + 1))
        (blowupF_comp_c T x₀ s).symm
    refine ⟨MorphismProperty.of_isPullback hsq.flip hflat, ?_⟩
    have h := hsq.paste_vert hpb
    rw [Tower.composite_pre_succ, Tower.composite_pre_succ]
    exact h

/-- The completion datum of p. 295: `X̂_0 = Spec(Ŝ)`, the monoidal transformations `f̂_s` of `X̂_s` with
center `c_s⁻¹(B_s)`, the canonical morphisms `c_s`, and `X̂_s = X_s ×_X X̂_0`
(`flat_and_isPullback_blowupC`). -/
noncomputable def Tower.completionOfBlowups [Hironaka.HironakaCitedResults.{u}] (hx : X.IsSimpleAt x₀) : Completion T x₀ where
  tHat := blowupTower T x₀
  c := blowupC T x₀
  c_zero := rfl
  c_comm := blowupF_comp_c T x₀
  B_hat _ := rfl
  isPullback s := (flat_and_isPullback_blowupC T x₀ hx s).2

/-- The morphisms `c_s` of `Tower.completion` are flat. -/
theorem Tower.flat_completionOfBlowups_c [Hironaka.HironakaCitedResults.{u}] (hx : X.IsSimpleAt x₀) (s : ℕ) :
    Flat ((T.completionOfBlowups x₀ hx).c s) :=
  (flat_and_isPullback_blowupC T x₀ hx s).1

/-- p. 295: existence of the completion datum.  "The given succession of monoidal
transformations `{f_s : X_{s+1} → X_s}` of `X` induces a succession of monoidal transformations
`{f̂_s : X̂_{s+1} → X̂_s}` of `X̂_0` such that we have the following commutative diagrams of
canonical morphisms … `f̂_s` is the monoidal transformation of `X̂_s` with the non-singular
center `B̂_s = c_s⁻¹(B_s)` … In view of the fact that `Ŝ` is faithfully flat over `S`, one can
show that `X̂_s` is canonically isomorphic to the product `X_s ×_X X̂_0` in the category of
schemes over `X` and that `c_s` is the projection to the first factor."

Proof as printed: the `f̂_s` are taken first (`completionBlowup`: the monoidal
transformation of `X̂_s` with center `c_s⁻¹(B_s)`, which exists by EGA II §3, the cited existence of
monoidal transformations), `c_{s+1}` being the canonical morphism with `f_s ∘ c_{s+1} = c_s ∘ f̂_s`
(`completionLift`, universal mapping property of `f_s`); then "one can show" that `X̂_s` is the product
`X_s ×_X X̂_0` with first projection `c_s` (`flat_and_isPullback_blowupC`).

Deviation from the paper (gap filled): "one can show" is not proved in the paper.  By induction on `s` each
square `(c_{s+1}, f̂_s, f_s, c_s)` is a pullback square: `c_s` is flat (`c_0 : Spec(Ŝ) → Spec(S) → X` is flat
since `S → Ŝ` is flat, and flatness is stable under base change), so the flat base change of `f_s` along `c_s` is
also a monoidal transformation of `X̂_s` with center `c_s⁻¹(B_s)` (`MonoidalTransformation.baseChange`,
`compat:blowup-flat-base-change`), and two monoidal transformations with the same center are canonically
isomorphic over `X̂_s` (`MonoidalTransformation.isPullback_of_flat`); the squares paste to `X̂_s = X_s ×_X X̂_0`.
Only the flatness of `Ŝ` over `S` is used, not its faithful flatness.  The datum built here is
`Tower.completionOfBlowups`; the datum `Tower.completion`, built from the products `X̂_{s+1} = X_{s+1} ×_{X_s} X̂_s`
(no use of the existence of monoidal transformations), is the one over which the frames of §3 and §4 are
built, because their bridge with `StageState` is definitional on the fibre products; it is unchanged. -/
@[blueprint "lem:IV.3-completion-exists"
  (statement := /-- Let $\{f_s\colon X_{s+1}\to X_s\}$ be a succession of monoidal
    transformations of $X$ (\cref{def:IV.3-succession}) and $x_0$ a simple point of $X$. Then
    the induced succession $\{\hat f_s\colon\hat X_{s+1}\to\hat X_s\}$ of
    $\hat X_0=\operatorname{Spec}(\hat S)$ and the morphisms $c_s\colon\hat X_s\to X_s$ of
    \cref{def:IV.3-setup} exist: $c_s\circ\hat f_s=f_s\circ c_{s+1}$, $\hat f_s$ is the
    monoidal transformation of $\hat X_s$ with center $\hat B_s=c_s^{-1}(B_s)$, and
    $\hat X_s=X_s\times_X\hat X_0$ with projections $c_s$ and $\hat g_s$. (p.~295: ``In view of
    the fact that $\hat S$ is faithfully flat over $S$, one can show that $\hat X_s$ is
    canonically isomorphic to the product $X_s\times_X\hat X_0$ in the category of schemes
    over $X$ and that $c_s$ is the projection to the first factor.'') -/)
  (proof := /-- \textbf{Proof as printed.} The monoidal transformations $\hat f_s$ are taken
    first: $\hat X_0=\operatorname{Spec}(\hat S)$ with $c_0$ induced by $S\to\hat S$, $\hat f_s\colon
    \hat X_{s+1}\to\hat X_s$ a monoidal transformation of $\hat X_s$ with center
    $\hat B_s=c_s^{-1}(B_s)$ (it exists by Grothendieck, EGA II \S3, cited on p.~166), and $c_{s+1}\colon
    \hat X_{s+1}\to X_{s+1}$ the canonical morphism with $f_s\circ c_{s+1}=c_s\circ\hat f_s$ given by the
    universal mapping property of $f_s$ (the pull-back of $B_s$ by $c_s\circ\hat f_s$ is the invertible
    ideal $\hat f_s^{-1}(\hat B_s)$). This gives the commutative diagrams of p.~295. Then ``one can
    show'' that $\hat X_s$ is canonically isomorphic to $X_s\times_X\hat X_0$ with $c_s$ the first
    projection.

    \textbf{Deviation from the paper (gap filled).} The paper says ``one can show'' without proof. By
    induction on $s$ each $c_s$ is flat and $(c_s,\hat g_s,g_s,c_0)$ is a pullback square. For $s=0$:
    $c_0\colon\operatorname{Spec}(\hat S)\to\operatorname{Spec}(S)\to X$ is flat, $\hat S$ being flat over
    $S$ and $\operatorname{Spec}(S)\to X$ flat. Step: $c_s$ is flat, so by flat base change of monoidal
    transformations (\cref{compat:blowup-flat-base-change}) the projection $X_{s+1}\times_{X_s}\hat
    X_s\to\hat X_s$ is also a monoidal transformation of $\hat X_s$ with center $c_s^{-1}(B_s)$; two
    monoidal transformations with the same center are canonically isomorphic over $\hat X_s$ (universal
    mapping property, \cref{def:monoidal-transformation}), and $c_{s+1}$ corresponds to the first
    projection by the uniqueness in the universal mapping property of $f_s$. So $(c_{s+1},\hat f_s,f_s,c_s)$
    is a pullback square; hence $c_{s+1}$, a base change of $c_s$, is flat, and pasting with the square for $s$
    gives that for $s+1$. Only the flatness of $\hat S$ over $S$ is used, not its faithful flatness. -/)
  (proofUses := ["compat:blowup-flat-base-change", "def:IV.3-setup", "thm:monoidal-transformation-exists"])
  (latexEnv := "lemma")]
theorem nonempty_completion [Hironaka.HironakaCitedResults.{u}] (hx : X.IsSimpleAt x₀) : Nonempty (Completion T x₀) :=
  ⟨T.completionOfBlowups x₀ hx⟩

end PrintedOrder

end CompletionExists

section XHat0Algebraic

/-- p. 295: "The algebraic scheme `X̂_0 = Spec(Ŝ)`": `X̂_0` is an algebraic scheme.

Deviation from the paper (gap filled): the paper calls `X̂_0` algebraic without argument.  On an
affine open `Spec A ∋ x_0` with `A` of finite type over the base `S₀ ∈ 𝔅` of `X`, the local
ring `S = O_{X,x_0}` is `A_p`, which belongs to 𝔅 by (c) of p. 161; the completion of `A_p`
belongs to 𝔅 by (b) of p. 161 and is isomorphic to `Ŝ`, so `X̂_0 = Spec(Ŝ)` is isomorphic to, in
particular of finite type over, the spectrum of a ring of 𝔅.  (b) is
`IsHironakaBase.adicCompletion_maximalIdeal` (`prop:class-A-b`, proved); (c) is the leaf
`IsHironakaBase.localization_atPrime_of_finiteType` (`prop:class-A-c`). -/
@[blueprint "lem:IV.3-xhat0-algebraic"
  (statement := /-- Let $X$ be an algebraic scheme, $x_0$ a point of $X$, $S$ the local ring of
    $X$ at $x_0$ and $\hat S$ its completion. Then $\hat X_0=\operatorname{Spec}(\hat S)$ is an
    algebraic scheme (\cref{def:algebraic-scheme}). (p.~295: ``The algebraic scheme
    $\hat X_0=\operatorname{Spec}(\hat S)$''.) -/)
  (proof := /-- \textbf{Deviation from the paper (gap filled).} The paper uses this without
    argument. Let $S_0\in\mathfrak B$ be a base of $X$ and $\operatorname{Spec}A$ an affine open
    neighbourhood of $x_0$; $A$ is of finite type over $S_0$ and $S\simeq A_{\mathfrak p}$, which
    belongs to $\mathfrak B$ by (c) of p.~161 (\cref{prop:class-A-c}); its completion belongs to
    $\mathfrak B$ by (b) of p.~161 (\cref{prop:class-A-b}) and is isomorphic to $\hat S$. Hence
    $\hat X_0$ is isomorphic to the spectrum of a ring of $\mathfrak B$, in particular of finite
    type over it. -/)
  (proofUses := ["prop:class-A-b", "prop:class-A-c", "def:algebraic-scheme"])
  (latexEnv := "lemma")]
theorem isAlgebraicScheme_xHat0 [Hironaka.HironakaCitedResults.{u}] (X : Scheme.{u}) [IsAlgebraicScheme X] (x₀ : X) :
    IsAlgebraicScheme (xHat0 X x₀) := by
  obtain ⟨S, i1, i2, i3, p, hp, -⟩ := IsAlgebraicScheme.exists_base (X := X)
  obtain ⟨_, ⟨U, hU₀, rfl⟩, hxU, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x₀) isOpen_univ
  have hU : IsAffineOpen U := hU₀
  let φ : S →+* Γ(X, U) :=
    (p.appLE ⊤ U le_top).hom.comp (Scheme.ΓSpecIso (CommRingCat.of S)).inv.hom
  let _ : Algebra S Γ(X, U) := φ.toAlgebra
  have hφ : φ.FiniteType := by
    refine RingHom.FiniteType.comp ?_ (RingHom.FiniteType.of_surjective _ ?_)
    · exact HasRingHomProperty.appLE @LocallyOfFiniteType p hp ⟨⊤, isAffineOpen_top _⟩ ⟨U, hU⟩
        le_top
    · exact (Scheme.ΓSpecIso (CommRingCat.of S)).commRingCatIsoToRingEquiv.symm.surjective
  have : Algebra.FiniteType S Γ(X, U) := hφ
  set q := hU.primeIdealOf ⟨x₀, hxU⟩
  have hB : IsHironakaBase (Localization.AtPrime q.asIdeal) :=
    IsHironakaBase.localization_atPrime_of_finiteType S Γ(X, U) q
  have hBh : IsHironakaBase (AdicCompletion (maximalIdeal (Localization.AtPrime q.asIdeal))
      (Localization.AtPrime q.asIdeal)) :=
    IsHironakaBase.adicCompletion_maximalIdeal _
  let _ := TopCat.Presheaf.algebra_section_stalk X.presheaf (U := U) ⟨x₀, hxU⟩
  have : IsLocalization q.asIdeal.primeCompl (X.presheaf.stalk x₀) :=
    hU.isLocalization_stalk ⟨x₀, hxU⟩
  let e : Localization.AtPrime q.asIdeal ≃+* X.presheaf.stalk x₀ :=
    (IsLocalization.algEquiv q.asIdeal.primeCompl _ _).toRingEquiv
  have hmax' : (maximalIdeal (Localization.AtPrime q.asIdeal)).map e =
      maximalIdeal (X.presheaf.stalk x₀) :=
    IsLocalRing.eq_maximalIdeal (Ideal.map_isMaximal_of_equiv e)
  have hmax : (maximalIdeal (Localization.AtPrime q.asIdeal)).map (e : _ →+* _) =
      maximalIdeal (X.presheaf.stalk x₀) := by
    rw [Ideal.map_coe]; exact hmax'
  have hc : ∀ n, ((maximalIdeal (X.presheaf.stalk x₀)) ^ n).comap (e : _ →+* _) =
      (maximalIdeal (Localization.AtPrime q.asIdeal)) ^ n := by
    intro n
    rw [← hmax, ← Ideal.map_pow]
    exact Ideal.comap_map_of_bijective _ e.bijective
  have hs : ∀ n (b : X.presheaf.stalk x₀), ∃ a, b - (e : _ →+* _) a ∈
      (maximalIdeal (X.presheaf.stalk x₀)) ^ n := fun n b =>
    ⟨e.symm b, by simp⟩
  obtain ⟨eh⟩ := AdicCompletion.nonempty_ringEquiv_of_comap_pow_eq
    (e : Localization.AtPrime q.asIdeal →+* X.presheaf.stalk x₀)
    (maximalIdeal (Localization.AtPrime q.asIdeal)) (maximalIdeal (X.presheaf.stalk x₀)) hc hs
  let p' : xHat0 X x₀ ⟶ Spec (CommRingCat.of (AdicCompletion
      (maximalIdeal (Localization.AtPrime q.asIdeal)) (Localization.AtPrime q.asIdeal))) :=
    Spec.map eh.toCommRingCatIso.hom
  have : IsIso p' := (inferInstance : IsIso (Spec.map eh.toCommRingCatIso.hom))
  exact ⟨⟨_, inferInstance, inferInstance, hBh, p', inferInstance, inferInstance⟩⟩

/-- p. 295: "The algebraic scheme `X̂_0 = Spec(Ŝ)` has the unique closed point `x̂_0` such that
`c_0(x̂_0) = x_0`": `x̂_0` is the only closed point of `X̂_0`, and `c_0(x̂_0) = x_0`.

Deviation from the paper (gap filled): stated without proof in the paper; `Ŝ` is a local ring
(closed points of `Spec` are the maximal ideals) and `S → Ŝ` is local. -/
theorem isClosed_singleton_iff_eq_xhat0_and_c0_apply_xhat0 {X : Scheme.{u}} (x₀ : X)
    (hx : X.IsSimpleAt x₀) :
    (∀ p : xHat0 X x₀, IsClosed ({p} : Set (xHat0 X x₀)) ↔ p = xhat0 X x₀ hx) ∧
      (c0 X x₀).base (xhat0 X x₀ hx) = x₀ := by
  have : IsRegularLocalRing (X.presheaf.stalk x₀) := hx
  have key : ∀ q : PrimeSpectrum (Shat X x₀),
      IsClosed ({q} : Set (PrimeSpectrum (Shat X x₀))) ↔ q = IsLocalRing.closedPoint _ := by
    intro q
    rw [PrimeSpectrum.isClosed_singleton_iff_isMaximal]
    constructor
    · intro h
      exact PrimeSpectrum.ext (IsLocalRing.eq_maximalIdeal h)
    · rintro rfl
      exact IsLocalRing.maximalIdeal.isMaximal _
  exact ⟨fun p => key p, c0_apply_xhat0 X x₀ hx⟩

end XHat0Algebraic

/-! ## Lemmas (AB.2), (AB.3) and the Corollary of (AB.3) (pp. 295–296) -/

/-- **Lemma (AB.2)** (p. 295): "The morphism `c_s` induces a bijective mapping of the point sets
`ĝ_s⁻¹(x̂_0) → g_s⁻¹(x_0)`.  Moreover, if `ŷ ∈ ĝ_s⁻¹(x̂_0)` and `y = c_s(ŷ) ∈ g_s⁻¹(x_0)`, the local
homomorphism induced by `c_s` of the local ring of `X_s` at `y` into that of `X̂_s` at `ŷ`
transforms a regular system of parameters into such a system of parameters."

"The following lemma is an immediate consequence of Lemma 4, §2, Ch. III, and its corollaries."

Proof, along the printed route.  *Second assertion*: by induction on `s`
(`Completion.isRegularLocalRing_and_mapsRSOP_stalkMap`), carrying along the regularity of the local
rings of `X̂_s` and the isomorphism of residue fields: `s = 0` is Corollary 1 of Lemma 4 for `S → Ŝ`;
the step is Lemma 4 (2), (3) of Ch. III at points over the center
(`MonoidalTransformation.mapsRSOP_stalkMap_of_comm`), the local isomorphism off it.  Lemma 4 is used
directly rather than its Corollaries 1, 2 at every step (`S_s → Ŝ_s` is not a completion map for
`s ≥ 1`); Corollary 2 is not used.  *First assertion*
(`Completion.bijOn_c_of_isNonsingular`): "an immediate consequence of Lemma 4 … and its corollaries": by
induction on `s`, `c_{s+1}` maps the points of `X̂_{s+1}` over `ŷ ∈ ĝ_s⁻¹(x̂_0)` bijectively onto those of
`X_{s+1}` over `y = c_s(ŷ)`, which are the monoidal transforms of the local rings: "(1) If either `R̃` or `R'`
is residually algebraic over `R`, then there exist only a finite number of `R̃'`, all the `R̃'` have the same
dimension as `R'`, and if `R̃` is residually algebraic over `R` the number of `R̃'` does not exceed the
separable degree of the residue field of `R̃` over that of `R`" (Lemma 4 (1), p. 212) with the separable
degree `[k̃ : k]_s = 1` (`κ(x_0) ≅ κ(x̂_0)`, Corollary 1 for `s = 0`, then the second assertion carried
along); this is injectivity of `c_{s+1}` on the fibres of `f̂_s`
(`subsingleton_canonicalTransforms_of_surjective_residueField_map`,
`MonoidalTransformation.bijOn_fibre_of_comm`); surjectivity: a canonical lift `R̃'` of `R'` exists
(`exists_isCanonicalLift`) and is the local ring of a point of `X̂_{s+1}` over `ŷ` mapped by `c_{s+1}` to the
point of `R'` (`MonoidalTransformation.pointOfMonoidalTransform`,
`MonoidalTransformation.c_pointOfMonoidalTransform_eq`).

Gaps filled (the paper says only "an immediate consequence"): the induction on `s`; the identification of
the points of the blow-up over `y` with the monoidal transforms of `O_{X_s,y}` with center `B_y`, which uses the
two scheme-level facts (i) every monoidal transform of `O_{X̂_s,ŷ}` with center `B̂_ŷ` is the local ring of a point of
`X̂_{s+1}` over `ŷ`, compatibly with `c_{s+1}`, (ii) a point of the blow-up over `y` is determined by its local
ring as a subring of the field of quotients (`Hironaka/Compat/BlowupStalkPoints.lean`, from the universal
mapping property of p. 166 alone); the existence of a canonical lift (Lemma 4 asserts only the bound; Corollary 1
gives existence for completions, and `S_s → Ŝ_s` is not one); the case `y ∉ B_s`, where the center is the
whole local ring and there is one point over `y` and one over `ŷ` (p. 209: for `P = R` the monoidal transform of `R` is
`R`).  The product description `X̂_s = X_s ×_X X̂_0` of p. 295 is not used for the first assertion. -/
@[blueprint "lem:IV.AB-2"
  (statement := /-- \textbf{Lemma (AB.2).} Notation as in \cref{def:IV.3-setup}. The morphism
    $c_s$ induces a bijective mapping of the point sets
    $\hat g_s^{-1}(\hat x_0)\to g_s^{-1}(x_0)$. Moreover, if $\hat y\in\hat g_s^{-1}(\hat x_0)$
    and $y=c_s(\hat y)\in g_s^{-1}(x_0)$, the local homomorphism induced by $c_s$ of the local
    ring of $X_s$ at $y$ into that of $\hat X_s$ at $\hat y$ transforms a regular system of
    parameters into such a system of parameters (\cref{def:III.rsop-map}). (p.~295.) -/)
  (proof := /-- ``The following lemma is an immediate consequence of Lemma~4, \S2, Ch.~III,
    and its corollaries'' (\cref{lem:III.4}, \cref{cor:III.lem4-1}, \cref{cor:III.lem4-2}).
    The paper gives no further argument. Both assertions are proved by induction on $s$.

    \textbf{Second assertion} (gap filled). Carry along the regularity of the local ring $\hat S_s$
    of $\hat X_s$ at $\hat y\in\hat g_s^{-1}(\hat x_0)$ and the fact that $S_s\to\hat S_s$ induces
    an isomorphism of residue fields. For $s=0$, $\hat g_0^{-1}(\hat x_0)=\{\hat x_0\}$ and the
    local homomorphism induced by $c_0$ is $S\to\hat S$, which has both properties
    (\cref{cor:III.lem4-1}). For the step, let $\hat y'\in\hat g_{s+1}^{-1}(\hat x_0)$,
    $\hat y=\hat f_s(\hat y')$, $y'=c_{s+1}(\hat y')$ and $y=f_s(y')=c_s(\hat y)$. If
    $y\in B_s$, the local rings of $X_{s+1}$ at $y'$ and of $\hat X_{s+1}$ at $\hat y'$ are
    monoidal transforms of $S_s$ and $\hat S_s$ with centers $Q$, the ideal of $B_s$, and
    $Q\hat S_s$, the ideal of $\hat B_s=c_s^{-1}(B_s)$
    (\cref{compat:blowup-stalk-monoidal-transform}); by the commutative diagrams
    $c_s\circ\hat f_s=f_s\circ c_{s+1}$ the homomorphism induced by $c_{s+1}$ is a canonical
    local homomorphism between them; the residue field extension of $S_s\to\hat S_s$ being
    trivial, hence separable algebraic, \cref{lem:III.4}~(3) gives the regular systems of
    parameters, \cref{lem:III.4}~(2) the isomorphism of residue fields, and the monoidal
    transform $\hat S_{s+1}$ is regular (\cref{lem:III.2-monoidal-transform-regular}). If
    $y\notin B_s$, $f_s$ and $\hat f_s$ are local isomorphisms at $y'$ and $\hat y'$
    (\cref{compat:blowup-local-iso}). Lemma~4 is thus used directly, the isomorphism of residue
    fields being carried along the induction, rather than Corollaries~1 and~2 at every step
    ($S_s\to\hat S_s$ is not a completion map for $s\ge1$); Corollary~2 is not used.

    \textbf{First assertion} (printed route). For $s=0$ both point sets are one point. For the step,
    let $\hat y\in\hat g_s^{-1}(\hat x_0)$, $y=c_s(\hat y)$, $R=S_s$ the local ring of $X_s$ at $y$,
    $\tilde R=\hat S_s$ that of $\hat X_s$ at $\hat y$, $P$ the ideal of $B_s$ in $R$ and
    $\tilde P=P\tilde R$ that of $\hat B_s$. The points of $X_{s+1}$ over $y$ correspond to the
    monoidal transforms $R'$ of $R$ with center $P$, those of $\hat X_{s+1}$ over $\hat y$ to the
    monoidal transforms $\tilde R'$ of $\tilde R$ with center $\tilde P$
    (\cref{compat:blowup-stalk-monoidal-transform}), and $c_{s+1}$ sends the point of $\tilde R'$
    to that of the $R'$ for which there is a commutative diagram of canonical local homomorphisms
    (p.~211). By Lemma~4 (1) (\cref{lem:III.4}), ``the number of $\tilde R'$ does not exceed the
    separable degree of the residue field of $\tilde R$ over that of $R$'', which is $1$
    since $R\to\tilde R$ induces an isomorphism of the residue fields (Corollary~1 for $s=0$, the
    second assertion afterwards): this is the injectivity of $c_{s+1}$ on $\hat f_s^{-1}(\hat y)$.
    Surjectivity: every $R'$ has such an $\tilde R'$ (existence of a canonical lift), which is the
    local ring of a point of $\hat X_{s+1}$ over $\hat y$ mapped to the point of $R'$. For
    $y\notin B_s$ the center is the whole local ring: there is one point over $y$ and one over
    $\hat y$.

    \textbf{Gaps in the paper filled.} The paper says only ``an immediate consequence''. Lean
    proves the induction on $s$; the identification of the points of the blow-up over $y$ with the
    monoidal transforms of $\mathcal O_{X_s,y}$ with center $B_y$ from the universal mapping property
    of p.~166 alone: every monoidal transform of $\mathcal O_{\hat X_s,\hat y}$ with center
    $\hat B_{\hat y}$ is the local ring of a point of $\hat X_{s+1}$ over $\hat y$, compatibly
    with $c_{s+1}$, and a point of the blow-up over $y$ is determined by its local ring as a subring
    of the field of quotients; the existence of a canonical lift (Lemma~4 asserts only the bound,
    Corollary~1 existence for completions, and $S_s\to\hat S_s$ is not a completion); the case
    $y\notin B_s$. The product description $\hat X_s=X_s\times_X\hat X_0$ of p.~295 is not used for
    this assertion; $X_s$ and $B_s$ are non-singular (standing assumptions), as needed to apply
    Lemma~4 to the stalks, for both assertions. -/)
  (proofUses := ["lem:III.4", "cor:III.lem4-1", "def:IV.3-setup",
    "compat:blowup-stalk-monoidal-transform", "compat:blowup-local-iso",
    "lem:III.2-monoidal-transform-regular"])
  (latexEnv := "lemma")]
theorem Completion.bijOn_and_mapsRSOP_stalkMap {N n : ℕ} {X : Scheme.{u}} {ℜ : DatumI.Raw X} {P : DatumI.Presentation ℜ}
    {r : Restriction X} {T : Tower X} {x₀ : X} (hS : Standing N n ℜ P r T x₀)
    (𝒞 : Completion T x₀) (s : ℕ) :
    Set.BijOn (𝒞.c s).base ((𝒞.tHat.pre s).composite.base ⁻¹' {hS.xh})
      ((T.pre s).composite.base ⁻¹' {x₀}) ∧
    ∀ yh ∈ (𝒞.tHat.pre s).composite.base ⁻¹' {hS.xh},
      RingHom.MapsRSOP ((𝒞.c s).stalkMap yh).hom :=
  ⟨𝒞.bijOn_c_of_isNonsingular (hS.ambient.2.1 x₀) hS.isNonsingular_X hS.isNonsingular_B s,
    fun yh hyh =>
    (𝒞.isRegularLocalRing_and_mapsRSOP_stalkMap (hS.ambient.2.1 x₀) hS.isNonsingular_X
      hS.isNonsingular_B s yh hyh).2.1⟩

section CompletionNonsingular

variable {X : Scheme.{u}} {T : Tower X} {x₀ : X}

/-! ### Non-singularity of the schemes `X̂_s` -/

/-- A scheme is regular at every generization of a point at which it is regular: the local ring
at the generization is a localization of the local ring at the point (Serre's theorem, Ch. III,
footnote 9, p. 243, `isRegularLocalRing_localization_of_isRegularLocalRing`). -/
theorem isRegularLocalRing_stalk_of_specializes [Hironaka.HironakaCitedResults.{u}] {Y : Scheme.{u}} {η y : Y} (h : η ⤳ y)
    [IsRegularLocalRing (Y.presheaf.stalk y)] : IsRegularLocalRing (Y.presheaf.stalk η) := by
  let := (Y.presheaf.stalkSpecializes h).hom.toAlgebra
  have hloc := isLocalization_stalkSpecializes_of_specializes h
  set p := (IsLocalRing.maximalIdeal (Y.presheaf.stalk η)).comap
    (Y.presheaf.stalkSpecializes h).hom
  have : p.IsPrime := Ideal.comap_isPrime _ _
  have := isRegularLocalRing_localization_of_isRegularLocalRing (Y.presheaf.stalk y) p
  exact IsRegularLocalRing.of_ringEquiv
    (IsLocalization.algEquiv p.primeCompl (Localization.AtPrime p) (Y.presheaf.stalk η)).toRingEquiv

/-- Every point of a scheme which is universally closed over `X̂_0 = Spec(Ŝ)` specializes to a
point over the closed point `x̂_0`: the image of the closure of the point is closed, and every
point of `Spec(Ŝ)` specializes to `x̂_0`. -/
theorem exists_specializes_xhat0_of_universallyClosed (hx : X.IsSimpleAt x₀) {Z : Scheme.{u}}
    (g : Z ⟶ xHat0 X x₀) [UniversallyClosed g] (z : Z) :
    ∃ z', z ⤳ z' ∧ g.base z' = xhat0 X x₀ hx := by
  have : IsRegularLocalRing (X.presheaf.stalk x₀) := hx
  have hcl : IsClosed (g.base '' closure {z}) := g.isClosedMap _ isClosed_closure
  have hsp : g.base z ⤳ xhat0 X x₀ hx :=
    (PrimeSpectrum.le_iff_specializes (g.base z) (IsLocalRing.closedPoint (Shat X x₀))).mp
      (IsLocalRing.le_maximalIdeal ((g.base z : PrimeSpectrum (Shat X x₀)).isPrime.ne_top))
  obtain ⟨z', hz', he⟩ := hsp.mem_closed hcl ⟨z, subset_closure rfl, rfl⟩
  exact ⟨z', specializes_iff_mem_closure.mpr hz', he⟩

/-- `X̂_0 = Spec(Ŝ)` is locally noetherian. -/
theorem isLocallyNoetherian_xHat0 (hx : X.IsSimpleAt x₀) : IsLocallyNoetherian (xHat0 X x₀) := by
  have : IsRegularLocalRing (X.presheaf.stalk x₀) := hx
  exact (inferInstance : IsLocallyNoetherian (Spec (CommRingCat.of (Shat X x₀))))

/-- Every point of `X̂_s` specializes to a point of `ĝ_s⁻¹(x̂_0)`: `ĝ_s` is proper
(`MonoidalSuccession.isProper_composite`, `X̂_0 = Spec(Ŝ)` being noetherian). -/
theorem Completion.exists_specializes_xhat0 [Hironaka.HironakaCitedResults.{u}] (𝒞 : Completion T x₀) (hx : X.IsSimpleAt x₀)
    (s : ℕ) (yh : 𝒞.tHat.X s) :
    ∃ yh', yh ⤳ yh' ∧ (𝒞.tHat.pre s).composite.base yh' = xhat0 X x₀ hx := by
  have := isLocallyNoetherian_xHat0 hx
  have := MonoidalSuccession.isProper_composite (𝒞.tHat.pre s)
  exact exists_specializes_xhat0_of_universallyClosed hx _ yh

/-- pp. 295, 315: the schemes `X̂_s` of a `Completion` of a succession of non-singular schemes
with non-singular centers are non-singular (p. 295: "`f̂_s` is the monoidal transformation of
`X̂_s` with the non-singular center `B̂_s`"; p. 315: "a sequence of non-singular irreducible
algebraic schemes `X̂_s`").

Deviation from the paper (gap filled): the paper states this without proof.  At the points of
`ĝ_s⁻¹(x̂_0)` the local rings are regular by the induction of Lemma (AB.2)
(`Completion.isRegularLocalRing_and_mapsRSOP_stalkMap`: monoidal transforms, Ch. III §2, of
regular local rings with centers `QŜ_t` which are prime with regular quotient by Lemma 4,
Ch. III); every other point of `X̂_s` is a generization of such a point
(`Completion.exists_specializes_xhat0`: `ĝ_s` is proper), and a localization of a regular local
ring is regular (Serre's theorem, recalled in Ch. III, footnote 9, p. 243; a cited leaf). -/
@[blueprint "lem:IV.3-setup-nonsingular"
  (statement := /-- Notation as in \cref{def:IV.3-setup}, the $X_s$ and the centers $B_s$
    being non-singular. Then the schemes $\hat X_s$ are non-singular, and so are the centers
    $\hat B_s=c_s^{-1}(B_s)$. (p.~295: ``$\hat f_s$ is the monoidal transformation of $\hat X_s$
    with the non-singular center $\hat B_s=c_s^{-1}(B_s)$''; p.~315: ``a sequence of
    non-singular irreducible algebraic schemes $\hat X_s$''.) -/)
  (proof := /-- \textbf{Deviation from the paper (gap filled).} The paper asserts these facts
    without proof. Let $\hat y\in\hat g_s^{-1}(\hat x_0)$. By the induction of
    \cref{lem:IV.AB-2}, the local ring $\hat S_s$ of $\hat X_s$ at $\hat y$ is regular (a
    monoidal transform of a regular local ring with a prime center with regular quotient,
    \cref{lem:III.2-monoidal-transform-regular}, the center $Q\hat S_t$ being such by
    \cref{lem:III.4}), and if $\hat y\in\hat B_s$ the ideal of $\hat B_s$ at $\hat y$ is
    $Q\hat S_s$, $Q$ the ideal of $B_s$ at $y=c_s(\hat y)$, so that $\hat S_s/Q\hat S_s$ is
    regular by the first assertion of \cref{lem:III.4}, since $S_s\to\hat S_s$ transforms a
    regular system of parameters into such a system. Every point of $\hat X_s$ (resp.\
    $\hat B_s$) specializes to a point of $\hat g_s^{-1}(\hat x_0)$: $\hat g_s$ is proper
    (\cref{lem:succession-proper}, $\hat X_0$ being noetherian), so the image of the closure of
    a point is closed in $\operatorname{Spec}\hat S$ and contains $\hat x_0$. The local ring
    at a generization is a localization of the local ring at the specialization, hence
    regular (\cref{lem:regular-localization-serre}, J.-P.~Serre's theorem, recalled by the
    paper in Ch.~III, footnote~9, p.~243). -/)
  (proofUses := ["lem:IV.AB-2", "lem:III.4", "lem:III.2-monoidal-transform-regular",
    "lem:succession-proper", "lem:regular-localization-serre"])
  (latexEnv := "lemma")]
theorem Completion.isNonsingular_tHat [Hironaka.HironakaCitedResults.{u}] (𝒞 : Completion T x₀) (hx : X.IsSimpleAt x₀)
    (hX : ∀ s, (T.X s).IsNonsingular) (hB : ∀ s, (T.B s).IsNonsingular) (s : ℕ) :
    (𝒞.tHat.X s).IsNonsingular := by
  intro yh
  obtain ⟨yh', hsp, he⟩ := 𝒞.exists_specializes_xhat0 hx s yh
  have := (𝒞.isRegularLocalRing_and_mapsRSOP_stalkMap hx hX hB s yh' he).1
  exact isRegularLocalRing_stalk_of_specializes hsp

/-- p. 295: "`f̂_s` is the monoidal transformation of `X̂_s` with the non-singular center
`B̂_s = c_s⁻¹(B_s)`": the centers `B̂_s` of a `Completion` of a succession of non-singular
schemes with non-singular centers are non-singular (second half of `lem:IV.3-setup-nonsingular`).

Deviation from the paper (gap filled): the paper states this without proof.  At a point `ŷ` of
`B̂_s` over `x̂_0`, the ideal of `B̂_s` is `QŜ_s`, `Q` the (prime) ideal of `B_s` in `S_s`, and
`Ŝ_s/QŜ_s` is regular by Lemma 4 of Ch. III (first assertion), `S_s → Ŝ_s` transforming a regular
system of parameters into one (Lemma (AB.2)); every point of `B̂_s` is a generization of such a
point (`B̂_s → X̂_0` is proper), and a localization of a regular local ring is regular (Serre's theorem,
Ch. III, footnote 9, p. 243; a cited leaf). -/
theorem Completion.isNonsingular_B [Hironaka.HironakaCitedResults.{u}] (𝒞 : Completion T x₀) (hx : X.IsSimpleAt x₀)
    (hX : ∀ s, (T.X s).IsNonsingular) (hB : ∀ s, (T.B s).IsNonsingular) (s : ℕ) :
    (𝒞.tHat.B s).IsNonsingular := by
  intro z
  have := isLocallyNoetherian_xHat0 hx
  have := MonoidalSuccession.isProper_composite (𝒞.tHat.pre s)
  obtain ⟨z', hsp, he⟩ :=
    exists_specializes_xhat0_of_universallyClosed hx ((𝒞.tHat.B s).ι ≫ (𝒞.tHat.pre s).composite) z
  suffices h : IsRegularLocalRing ((𝒞.tHat.B s).toScheme.presheaf.stalk z') from
    isRegularLocalRing_stalk_of_specializes hsp
  set yh := (𝒞.tHat.B s).ι.base z'
  obtain ⟨hreg, hα, -⟩ := 𝒞.isRegularLocalRing_and_mapsRSOP_stalkMap hx hX hB s yh he
  have hyh : yh ∈ (𝒞.tHat.B s).pts := by
    show _ ∈ ((𝒞.tHat.B s).support : Set (𝒞.tHat.X s))
    rw [← Scheme.IdealSheafData.range_subschemeι]
    exact ⟨z', rfl⟩
  have hy : (𝒞.c s).base yh ∈ (T.B s).pts := by
    by_contra hy
    apply Subscheme.mem_pts_iff_stalkIdeal_ne_top.mp hyh
    rw [𝒞.B_hat s, stalkIdeal_totalTransform, Subscheme.stalkIdeal_eq_top_of_notMem_pts hy,
      Ideal.map_top]
  have : IsRegularLocalRing ((T.X s).presheaf.stalk ((𝒞.c s).base yh)) := hX s _
  have hQ := Subscheme.isPrime_stalkIdeal_of_isNonsingular (hB s) hy
  have hQreg := Subscheme.isRegularLocalRing_quotient_of_isNonsingular (hB s) hy
  have hq := (hα.isPrime_map_and_isRegularLocalRing_quotient hQ hQreg).2
  have hstalk : (𝒞.tHat.B s).stalkIdeal yh =
      ((T.B s).stalkIdeal ((𝒞.c s).base yh)).map ((𝒞.c s).stalkMap yh).hom := by
    rw [𝒞.B_hat s, stalkIdeal_totalTransform]
  obtain ⟨e⟩ := nonempty_stalk_quot_equiv (𝒞.tHat.B s) z'
  rw [← hstalk] at hq
  exact IsRegularLocalRing.of_ringEquiv e

end CompletionNonsingular

/-- Lemma (AB.3), p. 296, the proof of the second assertion up to the surjectivity of
`R_1/MR_1 → R_1'/MR_1'`, as printed: "we take a minimal base `(y_1,…,y_r)` of `P` such that if
`A = R[y_2/y_1,…,y_r/y_1]`, then `R_1 = A_N` with a prime ideal `N` in `A`. By the assumption on
`R → R'`, `(y_1,…,y_r)` is also a minimal base of the prime ideal `P'` in `R'` and, if
`A' = R'[y_2/y_1,…,y_r/y_1]`, `R_1'` is a localization of `A'`. Let `N'` be the prime ideal in `A'`
such that `R_1' = A'_{N'}`. Then `N'` is an associated prime ideal of `NA'`. (See § 2, Ch. III.)
By the assumption on `R/M → R'/MR'`, `R → R'` induces an isomorphism of residue fields so that `NA'`
is a prime ideal. Thus `N' = NA'`. Since `R/M → R'/MR'` is surjective, so is `A/MA → A'/MA'`. We have
`N ⊇ MA` and `N' ⊇ MA'` by the assumption on `M`, and therefore `R_1/MR_1 → R_1'/MR_1'` is surjective."

Steps: `N'` is the prime of `A'` over `N` with `R_1' = A'_{N'}` (`IsCanonicalLift.exists_ringEquiv_ofLift`,
Lemma 4); it is an associated prime of `NA'` (`MonoidalTransform.mem_associatedPrimes_of_mem_liftPrimes`,
Lemma 4, p. 211: the associated primes of `NA'` are the primes over `N` if `R → R'` is residually
algebraic); `NA'` is prime; the only associated prime of a prime ideal is itself, so `N' = NA'`
(`associatedPrimes`); `A/MA → A'/MA'` is onto (`MonoidalTransform.exists_sub_mem_map_blowupMap`);
`MA ⊆ N` and so `MA' ⊆ NA' = N'`; hence every element of `A'_{N'}` is congruent modulo `MA'_{N'}` to the
image of an element of `A_N`.

Deviation from the paper (gap filled): "so that `NA'` is a prime ideal" is not argued.  Lean proves it:
`A' = bm(A) + NA'` (from `A/MA → A'/MA'` onto and `MA ⊆ N`) and `NA' ∩ A = N` (as `NA' ⊆ N'` and
`N' ∩ A = N`), so `A/N ≅ A'/NA'` is a domain. -/
theorem _root_.Hironaka.IsCanonicalLift.surjective_quotientMap_of_associatedPrimes
    {R Rb : Type u} [CommRing R] [IsRegularLocalRing R] [IsDomain R] [CommRing Rb]
    [IsRegularLocalRing Rb] [IsDomain Rb] {P : Ideal R} (α : R →+* Rb) [IsLocalHom α]
    (hα : RingHom.MapsRSOP α) (hP : P.IsPrime) (hS : IsRegularLocalRing (R ⧸ P))
    (t : MonoidalTransform R P) (tb : MonoidalTransform Rb (P.map α)) (β : t.ring →+* tb.ring)
    (hβ : IsCanonicalLift α t tb β) (M : Ideal R) (hMm : M ≤ maximalIdeal R)
    (hsurj : ∀ y : Rb, ∃ r : R, α r - y ∈ M.map α) (halg : RingHom.IsResiduallyAlgebraic α) :
    Function.Surjective (Ideal.quotientMap ((M.map t.toRing).map β) β Ideal.le_comap_map) := by
  classical
  have hαinj := RingHom.MapsRSOP.injective α hα
  have := isNoetherianRing_blowupAlgebra (R := Rb) (P := P.map α) (α t.x)
  set bm := blowupMap α hαinj P t.x with hbm
  -- `R_1' = A'_{N'}` for a prime `N'` of `A'` over `N` ("Let `N'` be the prime ideal in `A'` such that
  -- `R_1' = A'_{N'}`")
  obtain ⟨N', hN', e, he⟩ := hβ.exists_ringEquiv_ofLift α hα t tb β
  have hN'p : N'.IsPrime := hN'.1
  have hN'c : N'.comap bm = t.M' := hN'.2
  -- "Then `N'` is an associated prime ideal of `NA'`. (See § 2, Ch. III.)"
  have hass : N' ∈ associatedPrimes (blowupAlgebra Rb (P.map α) (α t.x))
      (blowupAlgebra Rb (P.map α) (α t.x) ⧸ t.M'.map bm) :=
    t.mem_associatedPrimes_of_mem_liftPrimes α hα hP hS (Or.inl halg) N' hN'
  -- "Since `R/M → R'/MR'` is surjective, so is `A/MA → A'/MA'`", and `N ⊇ MA`
  have hMA' : ∀ z : blowupAlgebra Rb (P.map α) (α t.x), ∃ a : blowupAlgebra R P t.x,
      z - bm a ∈ (M.map α).map (algebraMap Rb (blowupAlgebra Rb (P.map α) (α t.x))) :=
    fun z => t.exists_sub_mem_map_blowupMap α hα M hsurj z
  have hMN : M.map (algebraMap R (blowupAlgebra R P t.x)) ≤ t.M' :=
    (Ideal.map_mono hMm).trans t.le
  have hJN : (M.map α).map (algebraMap Rb (blowupAlgebra Rb (P.map α) (α t.x))) ≤
      t.M'.map bm := by
    have h1 : (M.map α).map (algebraMap Rb (blowupAlgebra Rb (P.map α) (α t.x))) =
        (M.map (algebraMap R (blowupAlgebra R P t.x))).map bm := by
      rw [Ideal.map_map, Ideal.map_map]
      congr 1
      exact RingHom.ext fun r => (blowupMap_algebraMap α hαinj P t.x r).symm
    rw [h1]
    exact Ideal.map_mono hMN
  have hA : ∀ z : blowupAlgebra Rb (P.map α) (α t.x), ∃ a : blowupAlgebra R P t.x,
      z - bm a ∈ t.M'.map bm := fun z => by
    obtain ⟨a, ha⟩ := hMA' z
    exact ⟨a, hJN ha⟩
  -- "so that `NA'` is a prime ideal" (gap filled): `A/N ≅ A'/NA'`
  have hNA'N' : t.M'.map bm ≤ N' := by
    rw [Ideal.map_le_iff_le_comap, hN'c]
  have hNA'prime : (t.M'.map bm).IsPrime := by
    have hinj : Function.Injective
        (Ideal.quotientMap (t.M'.map bm) bm Ideal.le_comap_map) := by
      refine Ideal.quotientMap_injective' fun a ha => ?_
      have : a ∈ N'.comap bm := Ideal.mem_comap.mpr (hNA'N' ha)
      rwa [hN'c] at this
    have hsurjq : Function.Surjective
        (Ideal.quotientMap (t.M'.map bm) bm Ideal.le_comap_map) := by
      intro w
      obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective w
      obtain ⟨a, ha⟩ := hA z
      refine ⟨Ideal.Quotient.mk _ a, ?_⟩
      rw [Ideal.quotientMap_mk, Ideal.Quotient.eq]
      simpa using (t.M'.map bm).neg_mem ha
    let f := RingEquiv.ofBijective (Ideal.quotientMap (t.M'.map bm) bm Ideal.le_comap_map)
      ⟨hinj, hsurjq⟩
    have : IsDomain (blowupAlgebra Rb (P.map α) (α t.x) ⧸ t.M'.map bm) :=
      Function.Injective.isDomain f.symm.toRingHom f.symm.injective
    exact (Ideal.Quotient.isDomain_iff_prime _).mp this
  -- "Thus `N' = NA'`": the only associated prime of a prime ideal is itself
  have hN'eq : N' = t.M'.map bm := by
    have := IsAssociatedPrime.eq_radical hNA'prime.isPrimary hass
    rwa [hNA'prime.radical] at this
  -- "We have `N ⊇ MA` and `N' ⊇ MA'` by the assumption on `M`"
  have hJN' : (M.map α).map (algebraMap Rb (blowupAlgebra Rb (P.map α) (α t.x))) ≤ N' :=
    hN'eq ▸ hJN
  -- "and therefore `R_1/MR_1 → R_1'/MR_1'` is surjective"
  have hβT := MonoidalTransform.isCanonicalLift_ofLiftHom α hα t N' hN'
  have hI : ((M.map α).map (algebraMap Rb (blowupAlgebra Rb (P.map α) (α t.x)))).map
      (algebraMap (blowupAlgebra Rb (P.map α) (α t.x)) (Localization.AtPrime N')) ≤
      (M.map t.toRing).map (MonoidalTransform.ofLiftHom α hα t N' hN') :=
    le_of_eq (map_map_eq_of_comp_eq α _ _
      ((MonoidalTransform.ofLift α hα t N' hN').toRing.comp α) rfl t.toRing _ hβT.comm M)
  have key := exists_sub_mem_map_localRingHom_of_surjective bm N' t.M' hN'c.symm
    ((M.map α).map (algebraMap Rb (blowupAlgebra Rb (P.map α) (α t.x)))) hJN' hMA'
    (M.map t.toRing) hI
  -- transport along `e : R_1' ≃ A'_{N'}`
  have hIe : Ideal.map e ((M.map t.toRing).map β) =
      (M.map t.toRing).map (MonoidalTransform.ofLiftHom α hα t N' hN') := by
    show Ideal.map e.toRingHom (Ideal.map β (M.map t.toRing)) = _
    rw [Ideal.map_map]
    congr 1
    exact RingHom.ext he
  have hmem : ∀ x : tb.ring,
      e x ∈ (M.map t.toRing).map (MonoidalTransform.ofLiftHom α hα t N' hN') →
        x ∈ (M.map t.toRing).map β := by
    intro x hx
    rw [← hIe] at hx
    have h3 : Ideal.map e.symm.toRingHom (Ideal.map e.toRingHom ((M.map t.toRing).map β)) =
        (M.map t.toRing).map β := by
      rw [Ideal.map_map]
      have : e.symm.toRingHom.comp e.toRingHom = RingHom.id _ := RingHom.ext fun x => by simp
      rw [this, Ideal.map_id]
    have h4 : e.symm.toRingHom (e x) ∈ (M.map t.toRing).map β := by
      rw [← h3]
      exact Ideal.mem_map_of_mem _ hx
    simpa using h4
  intro w
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective w
  obtain ⟨c, hc⟩ : ∃ c : t.ring, MonoidalTransform.ofLiftHom α hα t N' hN' c - e y ∈
      (M.map t.toRing).map (MonoidalTransform.ofLiftHom α hα t N' hN') := key (e y)
  refine ⟨Ideal.Quotient.mk _ c, ?_⟩
  rw [Ideal.quotientMap_mk, Ideal.Quotient.eq]
  refine hmem _ ?_
  rw [map_sub, he]
  exact hc

/-- **Lemma (AB.3)** (pp. 295–296).  Encoding as in `rem:III.5-2`: the commutative diagram of
canonical local homomorphisms is `β : R₁ → R₁'` with `β ∘ (R → R₁) = (R' → R₁') ∘ α`; `R₁'` is
any monoidal transform of `R'` with center `P' = PR'` admitting such a diagram (the paper's "the
unique" one); "`R → R'` induces an isomorphism `R/M → R'/MR'`" is the bijectivity of the
induced map, and `MR₁'` is written `(MR₁)R₁'`, equal to it by commutativity.

Deviation from the paper (statement modified): `R₁'` is any monoidal transform with such a
diagram (the paper's "the unique" is not asserted).  The hypotheses `[IsDomain R]`,
`[IsDomain R']` are redundant (a regular local ring is a domain,
`isDomain_of_isRegularLocalRing`); they are only needed because the signature of
`MonoidalTransform` asks for them.  The facts that `R → R₁`, `R' → R₁'` are local and that `R₁`,
`R₁'` are regular (Ch. III §2) are no longer hypotheses: they are derived below.

Deviation from the paper (gap filled): "The first assertion is clear from Lemma 4, §2, Ch. III".
Lean first shows that `R/M ≅ R'/MR'` with `M ≠ R` makes the residue field extension an
isomorphism, hence separable algebraic, and then applies Lemma 4 (3) to a regular system of
parameters of `R₁` (and Lemma 4 (2) for the injectivity of `β`, needed for the distinctness of
the images).

Proof as printed: the paper takes a minimal base `(y₁,…,y_r)` of `P` with
`R₁ = A_N`, `A = R[y₂/y₁,…,y_r/y₁]`, notes that it is also a minimal base of `P'` with
`R₁' = A'_{N'}`, `A' = R'[y₂/y₁,…]` (Lemma 4 and its proof: `R₁'` is `A'_{N'}` for a prime `N'`
of `A'` over `N`, `IsCanonicalLift.exists_ringEquiv_ofLift`), and "`N'` is an associated prime
ideal of `NA'`" (`MonoidalTransform.mem_associatedPrimes_of_mem_liftPrimes`: the associated primes of
`NA'` are the primes of `A'` over `N` when `R → R'` is residually algebraic, which holds since
`R/M ≅ R'/MR'`).  Since `R/M → R'/MR'` is surjective so is `A/MA → A'/MA'`
(`MonoidalTransform.exists_sub_mem_map_blowupMap`); `NA'` is a prime ideal, so `N' = NA'` (the only
associated prime of a prime ideal is itself); `N ⊇ MA` and `N' ⊇ MA'`, whence `R₁/MR₁ → R₁'/MR₁'` is
surjective (`IsCanonicalLift.surjective_quotientMap_of_associatedPrimes`).  Injectivity is the
paper's (faithful flatness of `R₁'` over `R₁`).  Gap filled: "so that `NA'` is a prime ideal" is not
argued by the paper; Lean proves `A/N ≅ A'/NA'`. -/
@[blueprint "lem:IV.AB-3"
  (statement := /-- \textbf{Lemma (AB.3).} Let $R\to R'$ be a local homomorphism of regular
    local rings, and $M$ an ideal in $R$, such that a regular system of parameters of $R$ is
    transformed into such a system of parameters of $R'$ (\cref{def:III.rsop-map}) and that
    $R\to R'$ induces an isomorphism $R/M\to R'/MR'$. Let $P$ be a prime ideal in $R$ such
    that $R/P$ is regular, and $P'=PR'$. Let $R_1$ be a monoidal transform of $R$ with center
    $P$, and $R_1'$ the unique monoidal transform of $R'$ with center $P'$ which admits a
    commutative diagram of canonical local homomorphisms $R_1\to R_1'$ over $R\to R'$
    (\cref{def:III.2-monoidal-transform}, \cref{def:III.2-canonical}). We assume that
    $M\ne R$. Then $R_1\to R_1'$ transforms a regular system of parameters of $R_1$ into such
    a system of parameters of $R_1'$ and, moreover, it induces an isomorphism
    $R_1/MR_1\to R_1'/MR_1'$. (pp.~295--296.)

    \textbf{Deviation from the paper (statement modified).} $R_1'$ is any monoidal transform of
    $R'$ with center $P'$ admitting such a diagram (its uniqueness is neither assumed nor
    asserted). The hypotheses that $R$, $R'$ are domains are redundant (a regular local ring is
    a domain, \cref{lem:III.2-regular-local-domain}) and only needed by the signature of the
    notion of monoidal transform; that the canonical homomorphisms $R\to R_1$, $R'\to R_1'$ are
    local and that $R_1$, $R_1'$ are regular (lemmas of Ch.~III \S2) are proved, not assumed. -/)
  (proof := /-- The first assertion is clear from Lemma~4, \S2, Ch.~III (\cref{lem:III.4}).
    To prove the second assertion, we take a minimal base $(y_1,\dots,y_r)$ of $P$ such that
    if $A=R[y_2/y_1,\dots,y_r/y_1]$, then $R_1=A_N$ with a prime ideal $N$ in $A$. By the
    assumption on $R\to R'$, $(y_1,\dots,y_r)$ is also a minimal base of the prime ideal $P'$
    in $R'$ and, if $A'=R'[y_2/y_1,\dots,y_r/y_1]$, $R_1'$ is a localization of $A'$. Let $N'$
    be the prime ideal in $A'$ such that $R_1'=A'_{N'}$. Then $N'$ is an associated prime ideal
    of $NA'$ (see \S2, Ch.~III). By the assumption on $R/M\to R'/MR'$, $R\to R'$ induces an
    isomorphism of residue fields so that $NA'$ is a prime ideal. Thus $N'=NA'$. Since
    $R/M\to R'/MR'$ is surjective, so is $A/MA\to A'/MA'$. We have $N\supseteq MA$ and
    $N'\supseteq MA'$ by the assumption on $M$, and therefore $R_1/MR_1\to R_1'/MR_1'$ is
    surjective. By the first assertion, $R_1'$ is faithfully flat over $R_1$
    (\cref{lem:II.3-faithfully-flat-local}). It follows that $R_1/MR_1\to R_1'/MR_1'$ is
    injective. Thus $R_1/MR_1\to R_1'/MR_1'$ is bijective. \textsc{q.e.d.}

    \textbf{Deviation from the paper (gap filled).} ``The first assertion is clear from Lemma
    4'': $R/M\simeq R'/MR'$ with $M\ne R$ makes the residue field extension an isomorphism,
    hence separable algebraic, so that Lemma~4 (3) applies to a regular system of parameters
    of $R_1$; Lemma~4 (2) gives the injectivity of $R_1\to R_1'$ (the distinctness of the
    images of the parameters).

    \textbf{In Lean} (the printed route). By the proof of Lemma~4
    (\cref{lem:III.4}), $R_1'=A'_{N'}$ for a prime $N'$ of $A'=R'[y_2/y_1,\dots,y_r/y_1]$ lying over
    $N$; $N'$ is an associated prime ideal of $NA'$ (\cref{lem:III.4-associated-primes}: the
    associated primes of $NA'$ are the primes of $A'$ over $N$, as $R\to R'$ is residually algebraic,
    $R/M\simeq R'/MR'$). Since $R/M\to R'/MR'$ is surjective, so is $A/MA\to A'/MA'$
    ($R'=\alpha(R)+MR'$ and $A'$ is generated over $R'$ by the same quotients $y_i/y_1$), so
    $A'=\operatorname{im}(A)+NA'$ ($MA\subseteq N$); $NA'\cap A=N$ because $NA'\subseteq N'$ and
    $N'\cap A=N$, so $A/N\simeq A'/NA'$ is a domain and $NA'$ is a prime ideal (the paper's ``so
    that $NA'$ is a prime ideal'', not argued there). The only associated prime of a prime ideal is
    itself: $N'=NA'$. As $M\subseteq M_R$, $MA\subseteq N$ and $MA'\subseteq NA'=N'$; hence every
    element $\tilde a/\tilde s$ of $R_1'=A'_{N'}$ is congruent modulo $MR_1'$ to the image of
    $a/s\in R_1$ ($\tilde s\equiv s\bmod MA'$, so $s\notin N$). Injectivity is as in the paper
    (faithful flatness, \cref{lem:III.rsop-map-flat}). -/)
  (proofUses := ["lem:III.4", "lem:III.4-associated-primes", "lem:III.rsop-map-flat"])
  (latexEnv := "lemma")]
theorem mapsRSOP_and_bijective_quotientMap_of_monoidalTransform {R R' : Type u} [CommRing R] [IsRegularLocalRing R] [IsDomain R] [CommRing R']
    [IsRegularLocalRing R'] [IsDomain R'] (α : R →+* R') [IsLocalHom α]
    (hα : RingHom.MapsRSOP α) (M : Ideal R)
    (hM : Function.Bijective (Ideal.quotientMap (M.map α) α Ideal.le_comap_map))
    (P : Ideal R) [hP : P.IsPrime] [hS : IsRegularLocalRing (R ⧸ P)]
    (R₁ : MonoidalTransform R P) (R₁' : MonoidalTransform R' (P.map α))
    (β : R₁.ring →+* R₁'.ring) [hβl : IsLocalHom β]
    (hβ : β.comp R₁.toRing = R₁'.toRing.comp α) (hMR : M ≠ ⊤) :
    RingHom.MapsRSOP β ∧
      Function.Bijective (Ideal.quotientMap ((M.map R₁.toRing).map β) β Ideal.le_comap_map) := by
  have hP0 : P ≠ ⊥ := (Submodule.ne_bot_iff P).mpr ⟨R₁.x, R₁.x_mem, R₁.x_ne_zero⟩
  obtain ⟨hPp, hPreg⟩ := (RingHom.MapsRSOP.canonicalLift_properties α hα (P := P) hP hS).1
  have hP'0 : P.map α ≠ ⊥ :=
    (Submodule.ne_bot_iff _).mpr ⟨R₁'.x, R₁'.x_mem, R₁'.x_ne_zero⟩
  obtain ⟨h1reg, -, -⟩ := MonoidalTransform.isRegularLocalRing_and_isLocalHom_and_span_xR_eq_map R₁ hP hP0 hS
  obtain ⟨h2reg, -, -⟩ := MonoidalTransform.isRegularLocalRing_and_isLocalHom_and_span_xR_eq_map R₁' hPp hP'0 hPreg
  have hcan : IsCanonicalLift α R₁ R₁' β := ⟨hβl, hβ⟩
  -- M lies in the maximal ideal
  have hMm : M ≤ maximalIdeal R := le_maximalIdeal hMR
  have hmaxα : (maximalIdeal R).map α = maximalIdeal R' := RingHom.MapsRSOP.map_maximalIdeal hα
  -- every element of `R'` is congruent to an element of `α(R)` modulo `M R'`
  have hsurj : ∀ y : R', ∃ r : R, α r - y ∈ M.map α := by
    intro y
    obtain ⟨c, hc⟩ := hM.2 (Ideal.Quotient.mk _ y)
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective c
    refine ⟨r, ?_⟩
    rw [Ideal.quotientMap_mk, Ideal.Quotient.eq] at hc
    exact hc
  -- residue field map bijective
  have hres : Function.Bijective (ResidueField.map α) := by
    refine ⟨(ResidueField.map α).injective, fun w => ?_⟩
    obtain ⟨y, rfl⟩ := IsLocalRing.residue_surjective w
    obtain ⟨r, hr⟩ := hsurj y
    refine ⟨IsLocalRing.residue R r, ?_⟩
    rw [ResidueField.map_residue, ← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff,
      ← hmaxα]
    exact Ideal.map_mono hMm hr
  have hsep : RingHom.IsResiduallySeparableAlgebraic α := by
    let _ := (ResidueField.map α).toAlgebra
    refine ⟨fun x => ?_⟩
    obtain ⟨y, rfl⟩ := hres.2 x
    exact isSeparable_algebraMap y
  have halg : RingHom.IsResiduallyAlgebraic α := by
    let _ := (ResidueField.map α).toAlgebra
    refine ⟨fun x => ?_⟩
    obtain ⟨y, rfl⟩ := hres.2 x
    exact isAlgebraic_algebraMap y
  -- first assertion
  obtain ⟨-, -, -, hinj, -⟩ := (RingHom.MapsRSOP.canonicalLift_properties α hα (P := P) hP hS).2.2.1 R₁ R₁' β hcan
  have hmaps : RingHom.MapsRSOP β := by
    obtain ⟨s, hs⟩ := (isRegularLocalRing_iff_exists_rsop (R := R₁.ring)).mp h1reg |>.2
    refine ⟨s, hs, ?_, hinj.injOn⟩
    exact ((RingHom.MapsRSOP.canonicalLift_properties α hα (P := P) hP hS).2.2.2 R₁ R₁' β hcan).2 hsep s hs
  -- local homomorphisms preserve maximal ideals
  have hloc : ∀ {A B : Type u} [CommRing A] [CommRing B] [IsLocalRing A] [IsLocalRing B]
      (f : A →+* B) [IsLocalHom f] (a : A), a ∈ maximalIdeal A → f a ∈ maximalIdeal B :=
    by
    intro A B _ _ _ _ f _ a ha
    exact (mem_maximalIdeal _).mpr (mem_nonunits_iff.mpr fun hu =>
      (mem_maximalIdeal _).mp ha (IsLocalHom.map_nonunit a hu))
  have hJm : M.map R₁.toRing ≤ maximalIdeal R₁.ring := by
    rw [Ideal.map_le_iff_le_comap]
    exact fun m hm => hloc R₁.toRing m (hMm hm)
  have hIle : (M.map R₁.toRing).map β ≤ maximalIdeal R₁'.ring := by
    rw [Ideal.map_le_iff_le_comap]
    exact fun a ha => hloc β a (hJm ha)
  refine ⟨hmaps, ?_, ?_⟩
  · -- injectivity: `R₁'` is faithfully flat over `R₁`
    refine Ideal.quotientMap_injective' ?_
    let _ := β.toAlgebra
    have : IsLocalHom (algebraMap R₁.ring R₁'.ring) := hβl
    have : Module.Flat R₁.ring R₁'.ring := hmaps.flat
    have : Module.FaithfullyFlat R₁.ring R₁'.ring := Module.FaithfullyFlat.of_flat_of_isLocalHom
    exact le_of_eq (Ideal.comap_map_eq_self_of_faithfullyFlat (B := R₁'.ring) _)
  · -- surjectivity: `A/MA → A'/MA'` is surjective, `N ⊇ MA`, `N' ⊇ MA'` (p. 296)
    exact IsCanonicalLift.surjective_quotientMap_of_associatedPrimes α hα hP hS R₁ R₁' β hcan M hMm
      hsurj halg

section CompletionQuotient

variable {X : Scheme.{u}} {T : Tower X} {x₀ : X}

/-! ### The Corollary of Lemma (AB.3): `S_s/MS_s ≅ Ŝ_s/M̂Ŝ_s` -/

/-- The ideal `m_{g(y)} O_{Y,y}` generated by the maximal ideal of the local ring of `Z` at
`g(y)` in the local ring of `Y` at `y` (the paper's `MS_s`, `M̂Ŝ_s`, p. 296). -/
noncomputable def fiberIdeal {Y Z : Scheme.{u}} (g : Y ⟶ Z) (y : Y) :
    Ideal (Y.presheaf.stalk y) :=
  (maximalIdeal (Z.presheaf.stalk (g.base y))).map (g.stalkMap y).hom

/-- `fiberIdeal` only depends on the morphism. -/
theorem fiberIdeal_congr {Y Z : Scheme.{u}} {g g' : Y ⟶ Z} (h : g = g') (y : Y) :
    fiberIdeal g y = fiberIdeal g' y := by
  subst h; rfl

/-- The ideal of the fibre of the identity is the maximal ideal. -/
theorem fiberIdeal_id {Y : Scheme.{u}} (y : Y) :
    fiberIdeal (𝟙 Y) y = maximalIdeal (Y.presheaf.stalk y) := by
  rw [fiberIdeal, Scheme.Hom.stalkMap_id]
  exact Ideal.map_id _

/-- `m_{g(f(y))} O_y = (m_{g(f(y))} O_{f(y)}) O_y`. -/
theorem fiberIdeal_comp {Y Y' Z : Scheme.{u}} (f : Y' ⟶ Y) (g : Y ⟶ Z) (y : Y') :
    fiberIdeal (f ≫ g) y = (fiberIdeal g (f.base y)).map (f.stalkMap y).hom := by
  rw [fiberIdeal, fiberIdeal, Ideal.map_map, ← CommRingCat.hom_comp,
    ← Scheme.Hom.stalkMap_comp]
  rfl

/-- `fiberIdeal` at equal points, under the identification of the stalks. -/
theorem map_fiberIdeal_stalkCongr {Y Z : Scheme.{u}} (g : Y ⟶ Z) {p q : Y} (h : p = q) :
    (fiberIdeal g p).map (Y.presheaf.stalkCongr (Inseparable.of_eq h)).hom.hom =
      fiberIdeal g q := by
  subst h
  simp only [TopCat.Presheaf.stalkCongr_hom, TopCat.Presheaf.stalkSpecializes_refl,
    CommRingCat.hom_id]
  exact Ideal.map_id _

/-- The ideal of the fibre is proper (stalk maps are local). -/
theorem fiberIdeal_ne_top {Y Z : Scheme.{u}} (g : Y ⟶ Z) (y : Y) : fiberIdeal g y ≠ ⊤ :=
  ne_top_of_le_ne_top (maximalIdeal.isMaximal _).ne_top (map_maximalIdeal_le _)

section QuotientIso

variable {A A' B B' : Type u} [CommRing A] [CommRing A'] [CommRing B] [CommRing B']

/-- `A/I → B/IB` is bijective iff `IB ∩ A ⊆ I` and `B = f(A) + IB`. -/
theorem bijective_quotientMap_map_iff (f : A →+* B) (I : Ideal A) :
    Function.Bijective (Ideal.quotientMap (I.map f) f Ideal.le_comap_map) ↔
      (I.map f).comap f ≤ I ∧ ∀ b, ∃ a, f a - b ∈ I.map f := by
  constructor
  · rintro ⟨hi, hs⟩
    refine ⟨fun a ha => ?_, fun b => ?_⟩
    · have h0 : Ideal.quotientMap (I.map f) f Ideal.le_comap_map (Ideal.Quotient.mk I a) =
          Ideal.quotientMap (I.map f) f Ideal.le_comap_map 0 := by
        rw [Ideal.quotientMap_mk, map_zero, Ideal.Quotient.eq_zero_iff_mem]
        exact ha
      exact Ideal.Quotient.eq_zero_iff_mem.mp (hi h0)
    · obtain ⟨c, hc⟩ := hs (Ideal.Quotient.mk _ b)
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective c
      refine ⟨a, ?_⟩
      rw [Ideal.quotientMap_mk, Ideal.Quotient.eq] at hc
      exact hc
  · rintro ⟨hc, hs⟩
    refine ⟨Ideal.quotientMap_injective' hc, fun z => ?_⟩
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective z
    obtain ⟨a, ha⟩ := hs b
    exact ⟨Ideal.Quotient.mk _ a, by rw [Ideal.quotientMap_mk, Ideal.Quotient.eq]; exact ha⟩

/-- The bijectivity of `A/N → B/NB` is transported along ring isomorphisms `A ≅ A'`,
`B ≅ B'` compatible with `β : A → B` and `γ : A' → B'`. -/
theorem comap_map_le_and_exists_sub_mem_of_ringEquiv (β : A →+* B) (γ : A' →+* B')
    (e : A ≃+* A') (eh : B ≃+* B') (hγ : ∀ a, γ (e a) = eh (β a)) (N : Ideal A)
    (h : (N.map β).comap β ≤ N ∧ ∀ b, ∃ a, β a - b ∈ N.map β) :
    ((N.map (e : A →+* A')).map γ).comap γ ≤ N.map (e : A →+* A') ∧
      ∀ b', ∃ a', γ a' - b' ∈ (N.map (e : A →+* A')).map γ := by
  have hmap : (N.map (e : A →+* A')).map γ = (N.map β).map (eh : B →+* B') := by
    rw [Ideal.map_map, Ideal.map_map]
    congr 1
    ext a
    exact hγ a
  rw [hmap]
  refine ⟨fun x hx => ?_, fun b' => ?_⟩
  · obtain ⟨a, rfl⟩ := e.surjective x
    rw [Ideal.mem_comap, hγ] at hx
    have hb : β a ∈ N.map β := by
      have h' : β a ∈ ((N.map β).map (eh : B →+* B')).comap (eh : B →+* B') := hx
      rwa [Ideal.comap_map_of_bijective (eh : B →+* B') eh.bijective] at h'
    exact Ideal.mem_map_of_mem _ (h.1 hb)
  · obtain ⟨b, rfl⟩ := eh.surjective b'
    obtain ⟨a, ha⟩ := h.2 b
    refine ⟨e a, ?_⟩
    rw [hγ, ← map_sub]
    exact Ideal.mem_map_of_mem _ ha

end QuotientIso

/-- One step of the proof of the Corollary of Lemma (AB.3), for a commutative square as in
`MonoidalTransformation.mapsRSOP_stalkMap_of_comm`: if `α : O_{Y, f(c'(ŷ'))} → O_{Ŷ, f̂(ŷ')}`
(induced by `c`) transforms a regular system of parameters into such a system and induces
`R/M ≅ R̂/MR̂` for a proper ideal `M`, then `c'` induces `R₁/MR₁ ≅ R̂₁/MR̂₁` at `ŷ'` (Lemma (AB.3)
over the center; off the center `f`, `f̂` are local isomorphisms). -/
theorem _root_.Hironaka.MonoidalTransformation.comap_map_le_and_exists_sub_mem_stalkMap_of_comm
    {Y Yh : Scheme.{u}}
    {B : Subscheme Y} {Bh : Subscheme Yh} (t : MonoidalTransformation Y B)
    (th : MonoidalTransformation Yh Bh) (c : Yh ⟶ Y) (c' : th.X' ⟶ t.X')
    (hBh : Bh = Subscheme.totalTransform c B) (hcomm : th.f ≫ c = c' ≫ t.f)
    (hY : Y.IsNonsingular) (hB : B.IsNonsingular) (yh' : th.X')
    [IsRegularLocalRing (Yh.presheaf.stalk (th.f.base yh'))]
    (hα : RingHom.MapsRSOP (c.stalkMap (th.f.base yh')).hom)
    (h : t.f.base (c'.base yh') = c.base (th.f.base yh'))
    (M : Ideal (Y.presheaf.stalk (t.f.base (c'.base yh')))) (hMtop : M ≠ ⊤)
    (hM : (M.map ((c.stalkMap (th.f.base yh')).hom.comp
        (Y.presheaf.stalkCongr (Inseparable.of_eq h)).hom.hom)).comap
          ((c.stalkMap (th.f.base yh')).hom.comp
            (Y.presheaf.stalkCongr (Inseparable.of_eq h)).hom.hom) ≤ M ∧
      ∀ b, ∃ a, (c.stalkMap (th.f.base yh')).hom
        ((Y.presheaf.stalkCongr (Inseparable.of_eq h)).hom.hom a) - b ∈
          M.map ((c.stalkMap (th.f.base yh')).hom.comp
            (Y.presheaf.stalkCongr (Inseparable.of_eq h)).hom.hom)) :
    ((M.map (t.f.stalkMap (c'.base yh')).hom).map (c'.stalkMap yh').hom).comap
        (c'.stalkMap yh').hom ≤ M.map (t.f.stalkMap (c'.base yh')).hom ∧
      ∀ b, ∃ a, (c'.stalkMap yh').hom a - b ∈
        (M.map (t.f.stalkMap (c'.base yh')).hom).map (c'.stalkMap yh').hom := by
  subst hBh
  obtain ⟨h0, hsq⟩ := exists_stalkMap_comm hcomm yh'
  have : IsRegularLocalRing (Y.presheaf.stalk (t.f.base (c'.base yh'))) := hY _
  have : IsRegularLocalRing (Y.presheaf.stalk (c.base (th.f.base yh'))) := hY _
  have : IsDomain (Y.presheaf.stalk (t.f.base (c'.base yh'))) :=
    isDomain_of_isRegularLocalRing _
  have : IsDomain (Yh.presheaf.stalk (th.f.base yh')) := isDomain_of_isRegularLocalRing _
  let ι := Y.presheaf.stalkCongr (Inseparable.of_eq h)
  have hι : IsLocalHom ι.hom.hom := isLocalHom_of_isIso _
  let α := (c.stalkMap (th.f.base yh')).hom.comp ι.hom.hom
  have hαl : IsLocalHom α := RingHom.isLocalHom_comp _ _
  have hα' : RingHom.MapsRSOP α := hα.comp (mapsRSOP_ringEquiv ι.commRingCatIsoToRingEquiv)
  have hcomm' : ∀ r, (c'.stalkMap yh').hom ((t.f.stalkMap (c'.base yh')).hom r) =
      (th.f.stalkMap yh').hom (α r) := fun r => by
    exact congrArg (fun g => g.hom r) hsq
  by_cases hyB : t.f.base (c'.base yh') ∈ B.pts
  · have hQ := Subscheme.isPrime_stalkIdeal_of_isNonsingular hB hyB
    have hQreg := Subscheme.isRegularLocalRing_quotient_of_isNonsingular hB hyB
    obtain ⟨tt, e, he⟩ := t.exists_monoidalTransform_stalk (c'.base yh')
    obtain ⟨tb, eh, heh⟩ := th.exists_monoidalTransform_stalk yh'
    have hQh : (Subscheme.totalTransform c B).stalkIdeal (th.f.base yh') =
        (B.stalkIdeal (t.f.base (c'.base yh'))).map α := by
      rw [stalkIdeal_totalTransform, ← Ideal.map_map, stalkIdeal_map_stalkCongr B h]
    obtain ⟨tb', eh', heh'⟩ : ∃ (tb' : MonoidalTransform (Yh.presheaf.stalk (th.f.base yh'))
        ((B.stalkIdeal (t.f.base (c'.base yh'))).map α))
        (eh' : tb'.ring ≃+* th.X'.presheaf.stalk yh'),
        eh'.toRingHom.comp tb'.toRing = (th.f.stalkMap yh').hom := by
      rw [← hQh]; exact ⟨tb, eh, heh⟩
    have : IsLocalHom (e : tt.ring →+* t.X'.presheaf.stalk (c'.base yh')) :=
      isLocalHom_ringEquiv e
    have : IsLocalHom (eh'.symm : th.X'.presheaf.stalk yh' →+* tb'.ring) :=
      isLocalHom_ringEquiv eh'.symm
    let β : tt.ring →+* tb'.ring := (eh'.symm : th.X'.presheaf.stalk yh' →+* tb'.ring).comp
      ((c'.stalkMap yh').hom.comp (e : tt.ring →+* t.X'.presheaf.stalk (c'.base yh')))
    have hβl : IsLocalHom β := RingHom.isLocalHom_comp _ _
    have hβ : β.comp tt.toRing = tb'.toRing.comp α := by
      ext r
      have h1 := RingHom.congr_fun he r
      have h2 := RingHom.congr_fun heh' (α r)
      simp only [RingEquiv.toRingHom_eq_coe, RingHom.coe_comp, Function.comp_apply,
        RingHom.coe_coe] at h1 h2
      simp only [β, RingHom.coe_comp, Function.comp_apply, RingHom.coe_coe, h1, hcomm', ← h2,
        RingEquiv.symm_apply_apply]
    have hMb : Function.Bijective (Ideal.quotientMap (M.map α) α Ideal.le_comap_map) :=
      (bijective_quotientMap_map_iff α M).mpr hM
    obtain ⟨-, hbij⟩ := mapsRSOP_and_bijective_quotientMap_of_monoidalTransform (hP := hQ)
      (hS := hQreg) α hα' M hMb _ tt tb' β hβ hMtop
    have hQ1 := (bijective_quotientMap_map_iff β (M.map tt.toRing)).mp hbij
    have hγ : ∀ a, (c'.stalkMap yh').hom (e a) = eh' (β a) := fun a => by
      simp [β]
    have := comap_map_le_and_exists_sub_mem_of_ringEquiv β (c'.stalkMap yh').hom e eh' hγ
      (M.map tt.toRing) hQ1
    have hM' : (M.map tt.toRing).map (e : tt.ring →+* t.X'.presheaf.stalk (c'.base yh')) =
        M.map (t.f.stalkMap (c'.base yh')).hom := by
      rw [Ideal.map_map, ← he]; rfl
    rwa [hM'] at this
  · have hyBh : th.f.base yh' ∉ (Subscheme.totalTransform c B).pts := by
      have hyB' : c.base (th.f.base yh') ∉ B.pts := h ▸ hyB
      rw [Subscheme.mem_pts_iff_stalkIdeal_ne_top, not_not, stalkIdeal_totalTransform,
        Subscheme.stalkIdeal_eq_top_of_notMem_pts hyB', Ideal.map_top]
    have h1 := t.bijective_stalkMap_of_notMem _ hyB
    have h2 := th.bijective_stalkMap_of_notMem _ hyBh
    exact comap_map_le_and_exists_sub_mem_of_ringEquiv α (c'.stalkMap yh').hom
      (RingEquiv.ofBijective _ h1) (RingEquiv.ofBijective _ h2) hcomm' M hM

/-- At a local homomorphism `α` with `MR' = M'` inducing a surjection of residue fields,
`R/M → R'/MR'` is bijective (in the elementwise form of `bijective_quotientMap_map_iff`). -/
theorem comap_map_maximalIdeal_le_and_exists_sub_mem {R R' : Type u} [CommRing R]
    [CommRing R'] [IsLocalRing R] [IsLocalRing R'] (α : R →+* R') [IsLocalHom α]
    (hmax : (maximalIdeal R).map α = maximalIdeal R')
    (hres : Function.Surjective (ResidueField.map α)) :
    ((maximalIdeal R).map α).comap α ≤ maximalIdeal R ∧
      ∀ b, ∃ a, α a - b ∈ (maximalIdeal R).map α := by
  rw [hmax, IsLocalRing.maximalIdeal_comap]
  refine ⟨le_rfl, fun b => ?_⟩
  obtain ⟨v, hv⟩ := hres (IsLocalRing.residue R' b)
  obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective v
  refine ⟨a, ?_⟩
  rw [ResidueField.map_residue] at hv
  rw [← IsLocalRing.residue_eq_zero_iff, map_sub, hv, sub_self]

/-- `c_0` maps the maximal ideal of `O_{X, x_0}` onto that of `O_{X̂_0, x̂_0} = Ŝ` (`MŜ = M̂`). -/
theorem fiberIdeal_c0_xhat0 (X : Scheme.{u}) (x₀ : X) (hx : X.IsSimpleAt x₀) :
    fiberIdeal (c0 X x₀) (xhat0 X x₀ hx) =
      maximalIdeal ((xHat0 X x₀).presheaf.stalk (xhat0 X x₀ hx)) := by
  have := isRegularLocalRing_stalk_xhat0 hx
  have h0 := mapsRSOP_and_bijective_residueField_map_stalkMap_c0 X x₀ hx
  have hx' : IsRegularLocalRing (X.presheaf.stalk ((c0 X x₀).base (xhat0 X x₀ hx))) := by
    rw [c0_apply_xhat0 X x₀ hx]; exact hx
  exact h0.1.map_maximalIdeal

/-- `c_0` maps the maximal ideal of `O_{X, x_0}` onto that of `O_{X̂_0, x̂_0} = Ŝ` (`MŜ = M̂`),
for the `c_0` of a `Completion`. -/
theorem Completion.fiberIdeal_c_zero (𝒞 : Completion T x₀) (hx : X.IsSimpleAt x₀)
    (p : 𝒞.tHat.X 0) (hp : p = xhat0 X x₀ hx) :
    fiberIdeal (𝒞.c 0) p = maximalIdeal ((𝒞.tHat.X 0).presheaf.stalk p) := by
  subst hp
  exact (fiberIdeal_congr 𝒞.c_zero _).trans (fiberIdeal_c0_xhat0 X x₀ hx)

/-- The Corollary of Lemma (AB.3), first assertion, in elementwise form, for a given
`Completion`: by induction on `s` with Lemma (AB.3) (and Lemma (AB.2) for the regular systems of
parameters), starting from `S/M ≅ Ŝ/M̂`. -/
theorem Completion.comap_map_le_and_exists_sub_mem_fiberIdeal (𝒞 : Completion T x₀)
    (hx : X.IsSimpleAt x₀) (hX : ∀ s, (T.X s).IsNonsingular) (hB : ∀ s, (T.B s).IsNonsingular) :
    ∀ (s : ℕ) (yh : 𝒞.tHat.X s), (𝒞.tHat.pre s).composite.base yh = xhat0 X x₀ hx →
      ((fiberIdeal (T.pre s).composite ((𝒞.c s).base yh)).map ((𝒞.c s).stalkMap yh).hom).comap
          ((𝒞.c s).stalkMap yh).hom ≤ fiberIdeal (T.pre s).composite ((𝒞.c s).base yh) ∧
        ∀ b, ∃ a, ((𝒞.c s).stalkMap yh).hom a - b ∈
          (fiberIdeal (T.pre s).composite ((𝒞.c s).base yh)).map ((𝒞.c s).stalkMap yh).hom
  | 0, yh, hyh => by
    have hyh' : yh = xhat0 X x₀ hx := hyh
    have hid : fiberIdeal (T.pre 0).composite ((𝒞.c 0).base yh) =
        maximalIdeal ((T.X 0).presheaf.stalk ((𝒞.c 0).base yh)) :=
      fiberIdeal_id (Y := T.X 0) _
    rw [hid]
    have hmax := 𝒞.fiberIdeal_c_zero hx yh hyh'
    have hres := (𝒞.isRegularLocalRing_and_mapsRSOP_stalkMap hx hX hB 0 yh hyh).2.2
    exact comap_map_maximalIdeal_le_and_exists_sub_mem _ hmax hres
  | s + 1, yh, hyh => by
    have hyh' : (𝒞.tHat.pre s).composite.base ((𝒞.tHat.f s).base yh) = xhat0 X x₀ hx :=
      (congrArg (fun φ => φ.base yh) (Tower.composite_pre_succ 𝒞.tHat s)).symm.trans hyh
    have IH := 𝒞.comap_map_le_and_exists_sub_mem_fiberIdeal hx hX hB s _ hyh'
    obtain ⟨hreg, hα, -⟩ := 𝒞.isRegularLocalRing_and_mapsRSOP_stalkMap hx hX hB s _ hyh'
    have : IsRegularLocalRing ((𝒞.tHat.X s).presheaf.stalk
        ((𝒞.tHat.monoidalTransformation s).f.base yh)) := hreg
    obtain ⟨h, -⟩ := exists_stalkMap_comm (𝒞.c_comm s) yh
    let ι := (T.X s).presheaf.stalkCongr (Inseparable.of_eq h)
    let M := fiberIdeal (T.pre s).composite ((T.f s).base ((𝒞.c (s + 1)).base yh))
    have hM1 : M.map ι.hom.hom =
        fiberIdeal (T.pre s).composite ((𝒞.c s).base ((𝒞.tHat.f s).base yh)) :=
      map_fiberIdeal_stalkCongr _ h
    have hιa : ∀ a, ι.hom.hom (ι.symm.commRingCatIsoToRingEquiv a) = a := fun a => by
      show ι.hom.hom (ι.inv.hom a) = a
      rw [← CommRingCat.comp_apply, Iso.inv_hom_id, CommRingCat.id_apply]
    have hιa' : ∀ a, ι.symm.commRingCatIsoToRingEquiv (ι.hom.hom a) = a := fun a => by
      show ι.inv.hom (ι.hom.hom a) = a
      rw [← CommRingCat.comp_apply, Iso.hom_inv_id, CommRingCat.id_apply]
    have hγ : ∀ a, ((𝒞.c s).stalkMap ((𝒞.tHat.f s).base yh)).hom.comp ι.hom.hom
        (ι.symm.commRingCatIsoToRingEquiv a) =
          RingEquiv.refl _ (((𝒞.c s).stalkMap ((𝒞.tHat.f s).base yh)).hom a) := fun a => by
      simp only [RingHom.comp_apply, hιa, RingEquiv.refl_apply]
    have hQ := comap_map_le_and_exists_sub_mem_of_ringEquiv _ _ ι.symm.commRingCatIsoToRingEquiv
      (RingEquiv.refl _) hγ _ IH
    have hNM : (fiberIdeal (T.pre s).composite ((𝒞.c s).base ((𝒞.tHat.f s).base yh))).map
        (ι.symm.commRingCatIsoToRingEquiv : _ →+* _) = M := by
      rw [← hM1, Ideal.map_map]
      have : (ι.symm.commRingCatIsoToRingEquiv : _ →+* _).comp ι.hom.hom = RingHom.id _ := by
        ext a
        simp only [RingHom.comp_apply, RingHom.coe_coe, hιa', RingHom.id_apply]
      rw [this, Ideal.map_id]
    have hfib : fiberIdeal (T.pre (s + 1)).composite ((𝒞.c (s + 1)).base yh) =
        M.map ((T.f s).stalkMap ((𝒞.c (s + 1)).base yh)).hom := by
      rw [fiberIdeal_congr (Tower.composite_pre_succ T s), fiberIdeal_comp]
    rw [hNM] at hQ
    rw [hfib]
    exact MonoidalTransformation.comap_map_le_and_exists_sub_mem_stalkMap_of_comm
      (T.monoidalTransformation s) (𝒞.tHat.monoidalTransformation s) (𝒞.c s) (𝒞.c (s + 1))
      (𝒞.B_hat s) (𝒞.c_comm s) (hX s) (hB s) yh hα h M (fiberIdeal_ne_top _ _) hQ

/-- The Corollary of Lemma (AB.3), first assertion, for a given `Completion`: `M̂Ŝ_s = (MS_s)Ŝ_s`
and `S_s/MS_s → Ŝ_s/M̂Ŝ_s` is bijective at every point `ŷ` of `ĝ_s⁻¹(x̂_0)`. -/
theorem Completion.fiberIdeal_eq_and_bijective_quotientMap (𝒞 : Completion T x₀)
    (hx : X.IsSimpleAt x₀) (hX : ∀ s, (T.X s).IsNonsingular) (hB : ∀ s, (T.B s).IsNonsingular)
    (s : ℕ) (yh : 𝒞.tHat.X s) (hyh : (𝒞.tHat.pre s).composite.base yh = xhat0 X x₀ hx) :
    fiberIdeal (𝒞.tHat.pre s).composite yh =
        (fiberIdeal (T.pre s).composite ((𝒞.c s).base yh)).map ((𝒞.c s).stalkMap yh).hom ∧
      Function.Bijective (Ideal.quotientMap
        ((fiberIdeal (T.pre s).composite ((𝒞.c s).base yh)).map ((𝒞.c s).stalkMap yh).hom)
        ((𝒞.c s).stalkMap yh).hom Ideal.le_comap_map) := by
  refine ⟨?_, (bijective_quotientMap_map_iff _ _).mpr
    (𝒞.comap_map_le_and_exists_sub_mem_fiberIdeal hx hX hB s yh hyh)⟩
  have h1 := fiberIdeal_congr (𝒞.isPullback s).w yh
  rw [fiberIdeal_comp] at h1
  have h2 : fiberIdeal ((𝒞.tHat.pre s).composite ≫ 𝒞.c 0) yh =
      (fiberIdeal (𝒞.c 0) ((𝒞.tHat.pre s).composite.base yh)).map
        ((𝒞.tHat.pre s).composite.stalkMap yh).hom :=
    fiberIdeal_comp _ _ _
  have h3 := 𝒞.fiberIdeal_c_zero hx ((𝒞.tHat.pre s).composite.base yh) hyh
  rw [h3] at h2
  exact (h1.trans h2).symm

end CompletionQuotient

/-! ### The Corollary of Lemma (AB.3): reduced subschemes over `x̂_0` -/

section CompletionReduced

/-- In a pullback square `P = Y' ×_Z Y` in which `g : Y → Z` induces an isomorphism of residue
fields at `y`, the first projection maps the fibre of the second projection over `y`
homeomorphically onto the fibre of `f` over `g(y)`. -/
theorem exists_homeomorph_preimage_of_isPullback {P Y' Y Z : Scheme.{u}} {fst : P ⟶ Y'}
    {snd : P ⟶ Y} {f : Y' ⟶ Z} {g : Y ⟶ Z} (h : IsPullback fst snd f g) (y : Y)
    (hy : IsIso (g.residueFieldMap y)) :
    ∃ H : snd.base ⁻¹' {y} ≃ₜ f.base ⁻¹' {g.base y}, ∀ p, (H p).1 = fst.base p.1 := by
  have F := isPullback_fiberToSpecResidueField_of_isPullback h y
  let θ : snd.fiber y ⟶ f.fiber (g y) :=
    pullback.map _ _ _ _ fst (Spec.map (g.residueFieldMap y)) g h.w.symm (by simp)
  have hθ : IsIso θ := F.isIso_fst_of_isIso
  have hθι : θ ≫ f.fiberι (g y) = snd.fiberι y ≫ fst := pullback.lift_fst _ _ _
  refine ⟨(snd.fiberHomeo y).symm.trans (θ.homeomorph.trans (f.fiberHomeo (g y))), fun p => ?_⟩
  simp only [Homeomorph.trans_apply, Scheme.Hom.fiberHomeo_apply, Scheme.Hom.homeomorph_apply]
  rw [← Scheme.Hom.comp_apply, hθι, Scheme.Hom.comp_apply, Scheme.Hom.fiberι_fiberHomeo_symm]

/-- `c_0⁻¹(x_0) = {x̂_0}`: the only point of `Spec(Ŝ)` over `x_0` is the closed point
(`MŜ = M̂`). -/
theorem eq_xhat0_of_c0_apply_eq {X : Scheme.{u}} {x₀ : X} (hx : X.IsSimpleAt x₀)
    (p : xHat0 X x₀) (hp : (c0 X x₀).base p = x₀) : p = xhat0 X x₀ hx := by
  have : IsRegularLocalRing (X.presheaf.stalk x₀) := hx
  let φ := CommRingCat.ofHom (algebraMap (X.presheaf.stalk x₀) (Shat X x₀))
  have hq : (Spec.map φ).base p = closedPoint (X.presheaf.stalk x₀) := by
    apply (X.fromSpecStalk x₀).isEmbedding.injective
    rw [Scheme.fromSpecStalk_closedPoint]
    exact hp
  have hcomap : (p : PrimeSpectrum (Shat X x₀)).asIdeal.comap
      (algebraMap (X.presheaf.stalk x₀) (Shat X x₀)) = maximalIdeal (X.presheaf.stalk x₀) :=
    congrArg PrimeSpectrum.asIdeal hq
  have hle : maximalIdeal (Shat X x₀) ≤ (p : PrimeSpectrum (Shat X x₀)).asIdeal := by
    rw [AdicCompletion.maximalIdeal_eq_map, Ideal.map_le_iff_le_comap, hcomap]
  exact PrimeSpectrum.ext (le_antisymm
    (IsLocalRing.le_maximalIdeal (p : PrimeSpectrum (Shat X x₀)).isPrime.ne_top) hle)

/-- If a reduced closed subset `Z` of `Y` lies in the fibre of `g : Y → X` over `x_0`, the stalks
of the reduced subscheme on `Z` contain the ideal `m_{x_0} O_{Y,y}` of the fibre. -/
theorem fiberIdeal_le_stalkIdeal_ofClosed {Y X : Scheme.{u}} (g : Y ⟶ X) {x₀ : X}
    (Z : TopologicalSpace.Closeds Y) (hZ : (Z : Set Y) ⊆ g.base ⁻¹' {x₀}) (y : Y)
    (hy : g.base y = x₀) : fiberIdeal g y ≤ (Subscheme.ofClosed Z).stalkIdeal y := by
  subst hy
  let D0 : Subscheme X := Subscheme.ofClosed ⟨closure {g.base y}, isClosed_closure⟩
  have hD0 : maximalIdeal (X.presheaf.stalk (g.base y)) ≤ D0.stalkIdeal (g.base y) := by
    obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (g.base y)) isOpen_univ
    set q := hU.primeIdealOf ⟨g.base y, hxU⟩
    have hq : hU.fromSpec q = g.base y := hU.fromSpec_primeIdealOf ⟨g.base y, hxU⟩
    have h1 := Subscheme.compStalk_stalkIdeal_ofClosed_closure hU hxU q
    rw [hq] at h1
    rw [h1]
    let _ := TopCat.Presheaf.algebra_section_stalk X.presheaf (⟨g.base y, hxU⟩ : U)
    have := hU.isLocalization_stalk ⟨g.base y, hxU⟩
    exact (IsLocalization.AtPrime.map_eq_maximalIdeal q.asIdeal (X.presheaf.stalk (g.base y))).ge
  have hle : Subscheme.totalTransform g D0 ≤ Subscheme.ofClosed Z := by
    refine Scheme.IdealSheafData.le_support_iff_le_vanishingIdeal.mp fun w hw => ?_
    have hw' : g.base w ∈ D0.pts := by
      rw [Subscheme.pts_ofClosed]
      exact subset_closure (hZ hw)
    have : w ∈ (Subscheme.totalTransform g D0).pts := by
      rw [FlatPreimm.pts_totalTransform]; exact hw'
    exact this
  have h1 := Subscheme.stalkIdeal_mono hle y
  rw [stalkIdeal_totalTransform] at h1
  exact (Ideal.map_mono hD0).trans h1

section QuotientLe

variable {A B : Type u} [CommRing A] [CommRing B]

/-- If `A/N → B/NB` is bijective and `N ⊆ J`, then `A/J → B/JB` is bijective (elementwise form). -/
theorem comap_map_le_and_exists_sub_mem_of_le (f : A →+* B) {N J : Ideal A} (hNJ : N ≤ J)
    (h : (N.map f).comap f ≤ N ∧ ∀ b, ∃ a, f a - b ∈ N.map f) :
    (J.map f).comap f ≤ J ∧ ∀ b, ∃ a, f a - b ∈ J.map f := by
  have key : ∀ z ∈ J.map f, ∃ j ∈ J, z - f j ∈ N.map f := by
    intro z hz
    induction hz using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨j, hj, rfl⟩ := hx
      exact ⟨j, hj, by simp⟩
    | zero => exact ⟨0, J.zero_mem, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨j, hj, hj'⟩ := hx
      obtain ⟨k, hk, hk'⟩ := hy
      refine ⟨j + k, J.add_mem hj hk, ?_⟩
      have := (N.map f).add_mem hj' hk'
      convert this using 1
      rw [map_add]; ring
    | smul r x _ hx =>
      obtain ⟨j, hj, hj'⟩ := hx
      obtain ⟨a, ha⟩ := h.2 r
      refine ⟨a * j, J.mul_mem_left a hj, ?_⟩
      have e : r • x - f (a * j) = r * (x - f j) - (f a - r) * f j := by
        rw [smul_eq_mul, map_mul]; ring
      rw [e]
      exact sub_mem (Ideal.mul_mem_left _ _ hj') (Ideal.mul_mem_right _ _ ha)
  refine ⟨fun x hx => ?_, fun b => ?_⟩
  · obtain ⟨j, hj, hj'⟩ := key _ hx
    have hxj : x - j ∈ N := h.1 (by rw [Ideal.mem_comap, map_sub]; exact hj')
    have := J.add_mem (hNJ hxj) hj
    simpa using this
  · obtain ⟨a, ha⟩ := h.2 b
    exact ⟨a, Ideal.map_mono hNJ ha⟩

/-- If `A/J → B/JB` is bijective and `J` is radical, then `JB` is radical. -/
theorem isRadical_map_of_comap_map_le_and_exists_sub_mem (f : A →+* B) {J : Ideal A}
    (hJ : J.IsRadical) (h : (J.map f).comap f ≤ J ∧ ∀ b, ∃ a, f a - b ∈ J.map f) :
    (J.map f).IsRadical := by
  have hb := (bijective_quotientMap_map_iff f J).mpr h
  let e := RingEquiv.ofBijective _ hb
  rw [Ideal.isRadical_iff_quotient_reduced] at hJ ⊢
  exact isReduced_of_injective e.symm.toRingHom e.symm.injective

end QuotientLe

variable {X : Scheme.{u}} {T : Tower X} {x₀ : X}

/-- A point of `X̂_s` whose image in `X_s` lies over `x_0` lies over `x̂_0`. -/
theorem Completion.composite_tHat_eq_xhat0 (𝒞 : Completion T x₀) (hx : X.IsSimpleAt x₀) (s : ℕ)
    (yh : 𝒞.tHat.X s) (h : (T.pre s).composite.base ((𝒞.c s).base yh) = x₀) :
    (𝒞.tHat.pre s).composite.base yh = xhat0 X x₀ hx := by
  have e : (T.pre s).composite.base ((𝒞.c s).base yh) =
      (𝒞.c 0).base ((𝒞.tHat.pre s).composite.base yh) :=
    congrArg (fun φ => φ.base yh) (𝒞.isPullback s).w
  have hc : ∀ p : 𝒞.tHat.X 0, (𝒞.c 0).base p = (c0 X x₀).base p := fun p =>
    congrArg (fun φ => φ.base p) 𝒞.c_zero
  exact eq_xhat0_of_c0_apply_eq hx _ ((hc _).symm.trans (e.symm.trans h))

/-- If `c` maps the points of the total transform `c⁻¹(D)` of a closed subscheme `D` embeddingly
onto those of `D`, and induces `O_{Y, c(ŷ)}/D_{c(ŷ)} ≅ O_{Ŷ, ŷ}/D_{c(ŷ)}O_{Ŷ, ŷ}` at its points,
then `c` induces an isomorphism of schemes `c⁻¹(D) ≅ D`. -/
theorem exists_iso_totalTransform {Y Yh : Scheme.{u}} (c : Yh ⟶ Y) (D : Subscheme Y)
    (hemb : Topology.IsEmbedding (c.base ∘ (Subscheme.totalTransform c D).ι.base))
    (hsurj : ∀ y ∈ D.pts, ∃ yh ∈ (Subscheme.totalTransform c D).pts, c.base yh = y)
    (hQ : ∀ yh ∈ (Subscheme.totalTransform c D).pts,
      ((D.stalkIdeal (c.base yh)).map (c.stalkMap yh).hom).comap (c.stalkMap yh).hom ≤
          D.stalkIdeal (c.base yh) ∧
        ∀ b, ∃ a, (c.stalkMap yh).hom a - b ∈ (D.stalkIdeal (c.base yh)).map (c.stalkMap yh).hom) :
    ∃ e : (Subscheme.totalTransform c D).toScheme ≅ D.toScheme,
      e.hom ≫ D.ι = (Subscheme.totalTransform c D).ι ≫ c := by
  set Bh := Subscheme.totalTransform c D
  let φ : Bh.toScheme ⟶ D.toScheme := (D.comapIso c).hom ≫ pullback.snd _ _
  have hφ : φ ≫ D.ι = Bh.ι ≫ c := by
    show ((D.comapIso c).hom ≫ pullback.snd c D.subschemeι) ≫ D.subschemeι =
      (D.comap c).subschemeι ≫ c
    rw [Category.assoc, ← pullback.condition, ← Category.assoc,
      Scheme.IdealSheafData.comapIso_hom_fst]
  have hcomp : D.ι.base ∘ φ.base = c.base ∘ Bh.ι.base := by
    funext p
    exact congrArg (fun g => g.base p) hφ
  have hDemb := D.ι.isClosedEmbedding
  have hφemb : Topology.IsEmbedding φ.base := by
    rw [← hDemb.isEmbedding.of_comp_iff, hcomp]
    exact hemb
  have hBhpts : ∀ p, Bh.ι.base p ∈ Bh.pts := fun p => by
    have : Bh.ι.base p ∈ Set.range Bh.ι.base := ⟨p, rfl⟩
    rw [Scheme.IdealSheafData.range_subschemeι] at this
    exact this
  have hDpts : ∀ z, D.ι.base z ∈ D.pts := fun z => by
    have : D.ι.base z ∈ Set.range D.ι.base := ⟨z, rfl⟩
    rw [Scheme.IdealSheafData.range_subschemeι] at this
    exact this
  have hφsurj : Function.Surjective φ.base := by
    intro z
    obtain ⟨yh, hyh, he⟩ := hsurj _ (hDpts z)
    have : yh ∈ Set.range Bh.ι.base := by
      rw [Scheme.IdealSheafData.range_subschemeι]; exact hyh
    obtain ⟨p, rfl⟩ := this
    refine ⟨p, hDemb.injective ?_⟩
    rw [← he]
    exact congrFun hcomp p
  have hstalk : ∀ p, IsIso (φ.stalkMap p) := by
    intro p
    obtain ⟨h, hsq⟩ := exists_stalkMap_comm hφ.symm p
    set yh := Bh.ι.base p
    obtain ⟨hQ1, hQ2⟩ := hQ yh (hBhpts p)
    let ι' := Y.presheaf.stalkCongr (Inseparable.of_eq h)
    have hsq' : ∀ a, (φ.stalkMap p).hom ((D.ι.stalkMap (φ.base p)).hom a) =
        (Bh.ι.stalkMap p).hom ((c.stalkMap yh).hom (ι'.hom.hom a)) := fun a =>
      congrArg (fun g => g.hom a) hsq
    have hkerv : RingHom.ker (Bh.ι.stalkMap p).hom =
        (D.stalkIdeal (c.base yh)).map (c.stalkMap yh).hom := by
      rw [← stalkIdeal_eq_ker_stalkMap, stalkIdeal_totalTransform]
    have hkeru : RingHom.ker (D.ι.stalkMap (φ.base p)).hom = D.stalkIdeal (D.ι.base (φ.base p)) :=
      (stalkIdeal_eq_ker_stalkMap D (φ.base p)).symm
    have hJ : (D.stalkIdeal (D.ι.base (φ.base p))).map ι'.hom.hom = D.stalkIdeal (c.base yh) :=
      stalkIdeal_map_stalkCongr D h
    rw [ConcreteCategory.isIso_iff_bijective]
    refine ⟨(injective_iff_map_eq_zero (φ.stalkMap p).hom).mpr fun w hw => ?_, fun w => ?_⟩
    · obtain ⟨a, rfl⟩ := D.ι.stalkMap_surjective (φ.base p) w
      rw [hsq'] at hw
      have h1 : (c.stalkMap yh).hom (ι'.hom.hom a) ∈
          (D.stalkIdeal (c.base yh)).map (c.stalkMap yh).hom := by
        rw [← hkerv]; exact hw
      have h2 : ι'.hom.hom a ∈ D.stalkIdeal (c.base yh) := hQ1 h1
      rw [← hJ] at h2
      have h3 : a ∈ D.stalkIdeal (D.ι.base (φ.base p)) := by
        have : a ∈ ((D.stalkIdeal (D.ι.base (φ.base p))).map ι'.hom.hom).comap ι'.hom.hom := h2
        rwa [Ideal.comap_map_of_bijective _ ((ConcreteCategory.isIso_iff_bijective _).mp
          inferInstance)] at this
      rw [← hkeru] at h3
      exact h3
    · obtain ⟨b, rfl⟩ := Bh.ι.stalkMap_surjective p w
      obtain ⟨a₀, ha₀⟩ := hQ2 b
      obtain ⟨a, rfl⟩ := ((ConcreteCategory.isIso_iff_bijective ι'.hom).mp inferInstance).2 a₀
      refine ⟨(D.ι.stalkMap (φ.base p)).hom a, ?_⟩
      rw [hsq']
      rw [← hkerv] at ha₀
      have := (RingHom.mem_ker).mp ha₀
      rw [map_sub, sub_eq_zero] at this
      exact this
  have hopen := hφemb.isOpenEmbedding_of_surjective hφsurj
  have := IsOpenImmersion.of_isIso_stalkMap φ hopen
  have hiso : IsIso φ := by
    rw [isIso_iff_isOpenImmersion_and_epi_base]
    exact ⟨inferInstance, (TopCat.epi_iff_surjective _).mpr hφsurj⟩
  exact ⟨asIso φ, hφ⟩

/-- Two reduced subschemes with the same points are equal. -/
theorem eq_of_isReduced_of_pts_eq {Y : Scheme.{u}} {D D' : Subscheme Y} (hD : D.IsReduced)
    (hD' : D'.IsReduced) (h : D.pts = D'.pts) : D = D' := by
  rw [Subscheme.eq_ofClosed_support D hD, Subscheme.eq_ofClosed_support D' hD']
  congr 1
  exact TopologicalSpace.Closeds.ext h

/-- The Corollary of Lemma (AB.3), second assertion, for a given `Completion` (`x_0` a closed
point): a reduced subscheme `B̂` of `X̂_s` with `ĝ_s(B̂) = x̂_0` is `c_s⁻¹(B)` for a unique reduced
subscheme `B` of `X_s` with `g_s(B) = x_0`; `B = c_s(B̂)` and `c_s` induces `B̂ ≅ B`. -/
theorem Completion.exists_unique_isReduced_totalTransform (𝒞 : Completion T x₀)
    (hx : X.IsSimpleAt x₀) (hX : ∀ s, (T.X s).IsNonsingular) (hB : ∀ s, (T.B s).IsNonsingular)
    (hclosed : IsClosed ({x₀} : Set X)) (s : ℕ) (Bh : Subscheme (𝒞.tHat.X s))
    (hBh : Bh.IsReduced) (himg : (𝒞.tHat.pre s).composite.base '' Bh.pts = {xhat0 X x₀ hx}) :
    ∃ B : Subscheme (T.X s),
      (B.IsReduced ∧ (T.pre s).composite.base '' B.pts = {x₀} ∧
        Bh = Subscheme.totalTransform (𝒞.c s) B) ∧
      B.pts = (𝒞.c s).base '' Bh.pts ∧
      (∀ B' : Subscheme (T.X s), B'.IsReduced → (T.pre s).composite.base '' B'.pts = {x₀} →
        Bh = Subscheme.totalTransform (𝒞.c s) B' → B' = B) ∧
      ∃ e : Bh.toScheme ≅ B.toScheme, e.hom ≫ B.ι = Bh.ι ≫ 𝒞.c s := by
  have hbij := 𝒞.bijOn_c_of_isNonsingular hx hX hB s
  have hBhF : ∀ yh ∈ Bh.pts, (𝒞.tHat.pre s).composite.base yh = xhat0 X x₀ hx :=
    fun yh hyh => by
      have : (𝒞.tHat.pre s).composite.base yh ∈ (𝒞.tHat.pre s).composite.base '' Bh.pts :=
        ⟨yh, hyh, rfl⟩
      rw [himg] at this
      exact this
  have hpre : ∀ yh : 𝒞.tHat.X s, (T.pre s).composite.base ((𝒞.c s).base yh) = x₀ →
      (𝒞.tHat.pre s).composite.base yh = xhat0 X x₀ hx := 𝒞.composite_tHat_eq_xhat0 hx s
  have hmaps : ∀ yh : 𝒞.tHat.X s, (𝒞.tHat.pre s).composite.base yh = xhat0 X x₀ hx →
      (T.pre s).composite.base ((𝒞.c s).base yh) = x₀ := fun yh h => hbij.mapsTo h
  have hc0 : (𝒞.c 0).base (xhat0 X x₀ hx) = x₀ := by
    rw [𝒞.c_zero]; exact c0_apply_xhat0 X x₀ hx
  have hres : IsIso ((𝒞.c 0).residueFieldMap (xhat0 X x₀ hx)) := by
    rw [𝒞.c_zero]; exact isIso_residueFieldMap_c0_xhat0 X x₀ hx
  obtain ⟨H, hH⟩ := exists_homeomorph_preimage_of_isPullback (𝒞.isPullback s) (xhat0 X x₀ hx) hres
  have hFcl : IsClosed ((T.pre s).composite.base ⁻¹' {(𝒞.c 0).base (xhat0 X x₀ hx)}) := by
    rw [hc0]; exact hclosed.preimage (T.pre s).composite.continuous
  have hZ : IsClosed ((𝒞.c s).base '' Bh.pts) := by
    have h1 : IsClosed ((Subtype.val : ((𝒞.tHat.pre s).composite.base ⁻¹'
        {xhat0 X x₀ hx}) → 𝒞.tHat.X s) ⁻¹' Bh.pts) :=
      Bh.support.isClosed.preimage continuous_subtype_val
    have h2 := hFcl.isClosedMap_subtype_val _ (H.isClosedMap _ h1)
    convert h2 using 1
    ext y
    constructor
    · rintro ⟨yh, hyh, rfl⟩
      exact ⟨H ⟨yh, hBhF yh hyh⟩, ⟨⟨yh, hBhF yh hyh⟩, hyh, rfl⟩, hH _⟩
    · rintro ⟨_, ⟨p, hp, rfl⟩, rfl⟩
      exact ⟨p.1, hp, (hH p).symm⟩
  let Z : TopologicalSpace.Closeds (T.X s) := ⟨_, hZ⟩
  have hZpts : (Subscheme.ofClosed Z).pts = (𝒞.c s).base '' Bh.pts := Subscheme.pts_ofClosed Z
  have hZF : ((𝒞.c s).base '' Bh.pts) ⊆ (T.pre s).composite.base ⁻¹' {x₀} := by
    rintro _ ⟨yh, hyh, rfl⟩
    exact hmaps yh (hBhF yh hyh)
  have hpreZ : (𝒞.c s).base ⁻¹' ((𝒞.c s).base '' Bh.pts) = Bh.pts := by
    ext yh
    constructor
    · rintro ⟨yh₁, hyh₁, he⟩
      have h1 : (𝒞.tHat.pre s).composite.base yh = xhat0 X x₀ hx :=
        hpre yh (he ▸ hmaps yh₁ (hBhF yh₁ hyh₁))
      have := hbij.injOn (hBhF yh₁ hyh₁) h1 he
      exact this ▸ hyh₁
    · intro hyh
      exact ⟨yh, hyh, rfl⟩
  have hQ : ∀ yh, (𝒞.tHat.pre s).composite.base yh = xhat0 X x₀ hx →
      (((Subscheme.ofClosed Z).stalkIdeal ((𝒞.c s).base yh)).map
          ((𝒞.c s).stalkMap yh).hom).comap ((𝒞.c s).stalkMap yh).hom ≤
        (Subscheme.ofClosed Z).stalkIdeal ((𝒞.c s).base yh) ∧
      ∀ b, ∃ a, ((𝒞.c s).stalkMap yh).hom a - b ∈
        ((Subscheme.ofClosed Z).stalkIdeal ((𝒞.c s).base yh)).map ((𝒞.c s).stalkMap yh).hom :=
    fun yh hyh => comap_map_le_and_exists_sub_mem_of_le _
      (fiberIdeal_le_stalkIdeal_ofClosed _ Z hZF _ (hmaps yh hyh))
      (𝒞.comap_map_le_and_exists_sub_mem_fiberIdeal hx hX hB s yh hyh)
  have hred : (Subscheme.totalTransform (𝒞.c s) (Subscheme.ofClosed Z)).IsReduced := by
    refine Subscheme.isReduced_of_isRadical_stalkIdeal fun yh => ?_
    rw [stalkIdeal_totalTransform]
    by_cases hyh : (𝒞.c s).base yh ∈ (𝒞.c s).base '' Bh.pts
    · exact isRadical_map_of_comap_map_le_and_exists_sub_mem _
        (Subscheme.isRadical_stalkIdeal_of_isReduced (Subscheme.ofClosed_isReduced Z) _)
        (hQ yh (hpre yh (hZF hyh)))
    · rw [Subscheme.stalkIdeal_eq_top_of_notMem_pts (hZpts ▸ hyh), Ideal.map_top]
      exact fun _ _ => Submodule.mem_top
  have hEq : Bh = Subscheme.totalTransform (𝒞.c s) (Subscheme.ofClosed Z) := by
    refine eq_of_isReduced_of_pts_eq hBh hred ?_
    rw [FlatPreimm.pts_totalTransform, hZpts, hpreZ]
  refine ⟨Subscheme.ofClosed Z, ⟨Subscheme.ofClosed_isReduced Z, ?_, hEq⟩, hZpts, ?_, ?_⟩
  · rw [hZpts]
    ext y
    simp only [Set.mem_image, Set.mem_singleton_iff]
    constructor
    · rintro ⟨_, ⟨yh, hyh, rfl⟩, rfl⟩
      exact hmaps yh (hBhF yh hyh)
    · rintro rfl
      obtain ⟨yh, hyh⟩ : Bh.pts.Nonempty := by
        by_contra hne
        rw [Set.not_nonempty_iff_eq_empty] at hne
        rw [hne, Set.image_empty] at himg
        exact (Set.singleton_ne_empty _) himg.symm
      exact ⟨_, ⟨yh, hyh, rfl⟩, hmaps yh (hBhF yh hyh)⟩
  · intro B' hB'red hB'img hB'eq
    refine eq_of_isReduced_of_pts_eq hB'red (Subscheme.ofClosed_isReduced Z) ?_
    rw [hZpts]
    have hpts' : Bh.pts = (𝒞.c s).base ⁻¹' B'.pts := by
      rw [hB'eq, FlatPreimm.pts_totalTransform]
    ext y
    constructor
    · intro hy
      have hyF : (T.pre s).composite.base y = x₀ := by
        have : (T.pre s).composite.base y ∈ (T.pre s).composite.base '' B'.pts := ⟨y, hy, rfl⟩
        rw [hB'img] at this
        exact this
      obtain ⟨yh, -, rfl⟩ := hbij.surjOn hyF
      refine ⟨yh, ?_, rfl⟩
      rw [hpts']
      exact hy
    · rintro ⟨yh, hyh, rfl⟩
      rw [hpts'] at hyh
      exact hyh
  · have hBhpts : ∀ p, Bh.ι.base p ∈ Bh.pts := fun p => by
      have : Bh.ι.base p ∈ Set.range Bh.ι.base := ⟨p, rfl⟩
      rw [Scheme.IdealSheafData.range_subschemeι] at this
      exact this
    have hembBh : Topology.IsEmbedding ((𝒞.c s).base ∘ Bh.ι.base) := by
      have hk := Bh.ι.isClosedEmbedding.isEmbedding.codRestrict
        ((𝒞.tHat.pre s).composite.base ⁻¹' {xhat0 X x₀ hx}) fun p => hBhF _ (hBhpts p)
      have h3 := Topology.IsEmbedding.subtypeVal.comp (H.isEmbedding.comp hk)
      convert h3 using 1
      funext p
      exact (hH ⟨Bh.ι.base p, hBhF _ (hBhpts p)⟩).symm
    have hemb : Topology.IsEmbedding ((𝒞.c s).base ∘
        (Subscheme.totalTransform (𝒞.c s) (Subscheme.ofClosed Z)).ι.base) := by
      rw [← hEq]; exact hembBh
    have hsurj : ∀ y ∈ (Subscheme.ofClosed Z).pts, ∃ yh ∈
        (Subscheme.totalTransform (𝒞.c s) (Subscheme.ofClosed Z)).pts, (𝒞.c s).base yh = y := by
      intro y hy
      rw [hZpts] at hy
      obtain ⟨yh, hyh, rfl⟩ := hy
      exact ⟨yh, hEq ▸ hyh, rfl⟩
    obtain ⟨e, he⟩ := exists_iso_totalTransform (𝒞.c s) (Subscheme.ofClosed Z) hemb hsurj
      fun yh hyh => hQ yh (hBhF yh (hEq ▸ hyh))
    rw [hEq]
    exact ⟨e, he⟩

/-- The chosen point `x_0` is a closed point of `X` (`X` has dimension `N` at `x_0`, and
`dim X = N`). -/
theorem Standing.isClosed_singleton {N n : ℕ} {ℜ : DatumI.Raw X} {P : DatumI.Presentation ℜ}
    {r : Restriction X} (hS : Standing N n ℜ P r T x₀) : IsClosed ({x₀} : Set X) := by
  refine closure_subset_iff_isClosed.mp fun y hy => ?_
  have hsp : x₀ ⤳ y := specializes_iff_mem_closure.mpr hy
  by_contra hne
  have h1 := LocSucc.dimAt_add_one_le_of_specializes hsp (Ne.symm hne)
  have h2 := LocSucc.dimAt_le_dim y
  rw [hS.dimAt_x₀] at h1
  rw [hS.ambient.2.2.2] at h2
  have h3 : ((N + 1 : ℕ) : WithBot ℕ∞) ≤ (N : WithBot ℕ∞) := by
    have := h1.trans h2
    exact_mod_cast this
  have h4 : N + 1 ≤ N := by exact_mod_cast h3
  omega

end CompletionReduced

/-- **Corollary of Lemma (AB.3)** (p. 296).  "`MS_s`" is the extension to `S_s` of the maximal
ideal of the local ring of `X` at `g_s(y) = x_0` by the local homomorphism induced by `g_s`, and
"`M̂Ŝ_s`" that of the maximal ideal `M̂ = MŜ` of the local ring of `X̂_0` at `ĝ_s(ŷ) = x̂_0`;
"`g_s(B) = x_0`" is `g_s(B) = {x_0}`.

Deviation from the paper (gap filled): the paper gives no proof.  First assertion: by induction
on `s` (`Completion.comap_map_le_and_exists_sub_mem_fiberIdeal`), Lemma (AB.3) being applied at
each step to `S_t → Ŝ_t` (which transforms a regular system of parameters into such a system by
Lemma (AB.2)), the ideal `MS_t` and the center of `f_t`, starting from `S/M ≅ Ŝ/M̂`; off the
center `f_t`, `f̂_t` are local isomorphisms; `M̂Ŝ_s = (MS_s)Ŝ_s` by the commutativity
`g_s ∘ c_s = c_0 ∘ ĝ_s` and `MŜ = M̂` (`Completion.fiberIdeal_eq_and_bijective_quotientMap`).
"In particular" (`Completion.exists_unique_isReduced_totalTransform`): `c_s` maps
`ĝ_s⁻¹(x̂_0)` homeomorphically onto `g_s⁻¹(x_0)` (the fibres are isomorphic, by the product
structure `X̂_s = X_s ×_X X̂_0` of p. 295 and `κ(x_0) ≅ κ(x̂_0)`) and `x_0` is a closed point
(`X` has dimension `N = dim X` at `x_0`), so `c_s(B̂)` is closed and `B` is the reduced
subscheme on it; its ideal contains `MS_s` at every point, so `S_s/B_y ≅ Ŝ_s/B_yŜ_s` by the first
assertion, `c_s⁻¹(B)` is reduced with the points of `B̂`, hence equal to `B̂`, and
`c_s⁻¹(B) → B` is a homeomorphism inducing isomorphisms of local rings, hence an isomorphism. -/
@[blueprint "cor:IV.AB-3"
  (statement := /-- \textbf{Corollary} (of \cref{lem:IV.AB-3}). Let the notation and the
    assumptions be the same as before (\cref{def:IV.3-setup}). Let $M$ be the maximal ideal of
    $S$ and $\hat M=M\hat S$. Let $\hat y\in\hat g_s^{-1}(\hat x_0)$ and
    $y=c_s(\hat y)\in g_s^{-1}(x_0)$. Let $\hat S_s$ (resp.\ $S_s$) be the local ring of
    $\hat X_s$ at $\hat y$ (resp.\ $X_s$ at $y$). Then the local homomorphism
    $S_s\to\hat S_s$, induced by $c_s$, induces an isomorphism $S_s/MS_s\to\hat S_s/\hat M\hat
    S_s$. In particular, if $\hat B$ is any reduced subscheme of $\hat X_s$ such that
    $\hat g_s(\hat B)=\hat x_0$, then there exists a unique reduced subscheme $B$ of $X_s$ such
    that $g_s(B)=x_0$ and $\hat B=c_s^{-1}(B)$. Moreover, $c_s$ induces an isomorphism
    $\hat B\to B$. (p.~296.) -/)
  (proof := /-- The paper gives no separate proof.

    \textbf{Deviation from the paper (gap filled).} \emph{First assertion.} By induction on
    $s$. For $s=0$, $S/M\to\hat S/\hat M$ is the isomorphism of the residue fields of $S$ and
    $\hat S$. For the step, let $\hat y'\in\hat g_{s+1}^{-1}(\hat x_0)$ lie over
    $\hat y\in\hat g_s^{-1}(\hat x_0)$, $y'=c_{s+1}(\hat y')$, $y=f_s(y')=c_s(\hat y)$. If
    $y\in B_s$, apply Lemma (AB.3) (\cref{lem:IV.AB-3}) to $R=S_s\to R'=\hat S_s$, which
    transforms a regular system of parameters into such a system (\cref{lem:IV.AB-2}), to the
    ideal $MS_s$ (by the induction hypothesis $S_s/MS_s\simeq\hat S_s/(MS_s)\hat S_s$), to the
    ideal $P$ of $B_s$ at $y$ and to the local rings of $X_{s+1}$ at $y'$ and of $\hat X_{s+1}$
    at $\hat y'$, which are monoidal transforms of $S_s$, $\hat S_s$ with centers $P$, $P\hat S_s$
    (\cref{compat:blowup-stalk-monoidal-transform}); $MS_{s+1}=(MS_s)S_{s+1}$ since
    $g_{s+1}=g_s\circ f_s$. If $y\notin B_s$, $f_s$ and $\hat f_s$ are local isomorphisms at
    $y'$, $\hat y'$ (\cref{compat:blowup-local-iso}). Finally $\hat M\hat S_s=(MS_s)\hat S_s$
    because $g_s\circ c_s=c_0\circ\hat g_s$ and $M\hat S=\hat M$.

    \emph{Second assertion} (``in particular''). By the product structure
    $\hat X_s=X_s\times_X\hat X_0$ (\cref{def:IV.3-setup}) and the isomorphism
    $\kappa(x_0)\simeq\kappa(\hat x_0)$, the scheme-theoretic fibres of $\hat g_s$ over
    $\hat x_0$ and of $g_s$ over $x_0$ are isomorphic, so $c_s$ maps $\hat g_s^{-1}(\hat x_0)$
    homeomorphically onto $g_s^{-1}(x_0)$ (\cref{lem:IV.AB-2}). The point $x_0$ is closed, $X$
    having dimension $N=\dim X$ at $x_0$; hence $c_s(\hat B)$ is closed in $X_s$, and $B$ is the
    reduced subscheme of $X_s$ on $c_s(\hat B)$, so that $g_s(B)=x_0$. As $B$ lies in the fibre
    of $g_s$ over the reduced point $x_0$, its ideal $B_y$ contains $MS_s$ at every point $y$;
    by the first assertion, $S_s/B_y\simeq\hat S_s/B_y\hat S_s$ at every point $\hat y$ over
    $\hat x_0$. Hence $c_s^{-1}(B)$ is reduced; its points are those of $\hat B$ ($c_s$ being
    injective on $\hat g_s^{-1}(\hat x_0)$ and $c_s^{-1}(g_s^{-1}(x_0))=\hat g_s^{-1}(\hat x_0)$,
    as $c_0^{-1}(x_0)=\{\hat x_0\}$), so $c_s^{-1}(B)=\hat B$, both being reduced. A second such
    $B'$ has the same points as $B$, hence equals $B$. The morphism $\hat B=c_s^{-1}(B)\to B$
    induced by $c_s$ is a homeomorphism inducing the isomorphisms
    $S_s/B_y\simeq\hat S_s/B_y\hat S_s$ of local rings, hence an isomorphism. The paper's
    ``in particular'' is thus completed by topological facts on the fibres which it does not
    state. -/)
  (proofUses := ["lem:IV.AB-3", "lem:IV.AB-2", "def:IV.3-setup",
    "compat:blowup-stalk-monoidal-transform", "compat:blowup-local-iso"])
  (latexEnv := "corollary")]
theorem Completion.bijective_quotientMap_and_exists_unique_reduced_totalTransform {N n : ℕ} {X : Scheme.{u}} {ℜ : DatumI.Raw X} {P : DatumI.Presentation ℜ}
    {r : Restriction X} {T : Tower X} {x₀ : X} (hS : Standing N n ℜ P r T x₀)
    (𝒞 : Completion T x₀) (s : ℕ) :
    (∀ yh : 𝒞.tHat.X s, (𝒞.tHat.pre s).composite.base yh = hS.xh →
      let φ := ((𝒞.c s).stalkMap yh).hom
      let MS := (maximalIdeal (X.presheaf.stalk ((T.pre s).composite.base ((𝒞.c s).base yh)))).map
        ((T.pre s).composite.stalkMap ((𝒞.c s).base yh)).hom
      let MSh := (maximalIdeal
        ((xHat0 X x₀).presheaf.stalk ((𝒞.tHat.pre s).composite.base yh))).map
          ((𝒞.tHat.pre s).composite.stalkMap yh).hom
      ∃ h : MS ≤ MSh.comap φ, Function.Bijective (Ideal.quotientMap MSh φ h)) ∧
    ∀ Bh : Subscheme (𝒞.tHat.X s), Bh.IsReduced →
      (𝒞.tHat.pre s).composite.base '' Bh.pts = {hS.xh} →
      ∃ B : Subscheme (T.X s),
        (B.IsReduced ∧ (T.pre s).composite.base '' B.pts = {x₀} ∧
          Bh = Subscheme.totalTransform (𝒞.c s) B) ∧
        (∀ B' : Subscheme (T.X s), B'.IsReduced → (T.pre s).composite.base '' B'.pts = {x₀} →
          Bh = Subscheme.totalTransform (𝒞.c s) B' → B' = B) ∧
        ∃ e : Bh.toScheme ≅ B.toScheme, e.hom ≫ B.ι = Bh.ι ≫ 𝒞.c s := by
  refine ⟨fun yh hyh => ?_, ?_⟩
  · obtain ⟨h1, h2⟩ := 𝒞.fiberIdeal_eq_and_bijective_quotientMap (hS.ambient.2.1 x₀)
      hS.isNonsingular_X hS.isNonsingular_B s yh hyh
    show ∃ h : fiberIdeal (T.pre s).composite ((𝒞.c s).base yh) ≤
        (fiberIdeal (𝒞.tHat.pre s).composite yh).comap ((𝒞.c s).stalkMap yh).hom,
      Function.Bijective (Ideal.quotientMap (fiberIdeal (𝒞.tHat.pre s).composite yh)
        ((𝒞.c s).stalkMap yh).hom h)
    rw [h1]
    exact ⟨Ideal.le_comap_map, h2⟩
  · intro Bh hBh himg
    obtain ⟨B, h1, -, h3, h4⟩ := 𝒞.exists_unique_isReduced_totalTransform (hS.ambient.2.1 x₀)
      hS.isNonsingular_X hS.isNonsingular_B hS.isClosed_singleton s Bh hBh himg
    exact ⟨B, h1, h3, h4⟩

/-! ## The regular frame `(T; z)`, `b`, `J̄`, `X̄_s` and `f̄_s` (pp. 296–298) -/

/-- `X̄_0 = Spec(T̄)`, `T̄ = Ŝ/(z)Ŝ`, as the closed subscheme `V(z)` of `X̂_0 = Spec(Ŝ)`
(p. 297). -/
def vZ (X : Scheme.{u}) (x₀ : X) (z : Shat X x₀) : Subscheme (xHat0 X x₀) :=
  Scheme.IdealSheafData.ofIdealTop
    ((Ideal.span {z}).map (Scheme.ΓSpecIso (CommRingCat.of (Shat X x₀))).inv.hom)

/-- p. 297: "Let `X̄_s` (`s ≥ 0`) be the strict transform of `X̄_0` in `X̂_s` by the succession
of monoidal transformations `ĝ_s : X̂_s → X̂_0`." -/
def strictTransformZeroLocus {X : Scheme.{u}} {x₀ : X} (Th : Tower (xHat0 X x₀)) (z : Shat X x₀) :
    ∀ s, Subscheme (Th.X s)
  | 0 => vZ X x₀ z
  | s + 1 => Subscheme.strictTransform (Th.monoidalTransformation s) (strictTransformZeroLocus Th z s)

/-- `c_s : X̂_s → X_s` is flat: it is the base change of `c_0 : Spec Ŝ → X` (`X̂_s = X_s ×_X X̂_0`)
(the argument of `CD.flat_c_of_completion`). -/
theorem Completion.flat_c {X : Scheme.{u}} {T : Tower X} {x₀ : X} (𝒞 : Completion T x₀)
    (hx : X.IsSimpleAt x₀) (s : ℕ) : Flat (𝒞.c s) := by
  have := flat_c0 X x₀ hx
  have h := 𝒞.isPullback s
  rw [𝒞.c_zero] at h
  exact MorphismProperty.of_isPullback h.flip this

/-- `X̄_0 = V(z) = c_0⁻¹(F)` when `z ∈ S` generates the ideal of `F` at `x_0` ([a], p. 296)
(the argument of `CD.vZ_eq_totalTransform_c0`). -/
theorem vZ_algebraMap_eq_totalTransform_c0 {X : Scheme.{u}} {x₀ : X} (F : Subscheme X)
    (z₀ : X.presheaf.stalk x₀) (hF : F.stalkIdeal x₀ = Ideal.span {z₀}) :
    vZ X x₀ (algebraMap _ (Shat X x₀) z₀) = Subscheme.totalTransform (c0 X x₀) F := by
  refine Subscheme.ext_stalkIdeal fun P => ?_
  have h1 := stalkIdeal_ofIdealTop_spec (CommRingCat.of (Shat X x₀))
    (Ideal.span {algebraMap _ (Shat X x₀) z₀}) P
  have h2 := stalkIdeal_comap_specMap_fromSpecStalk F x₀ (CommRingCat.of (Shat X x₀))
    (CommRingCat.ofHom (algebraMap (X.presheaf.stalk x₀) (Shat X x₀))) P
  refine h1.trans (Eq.trans ?_ h2.symm)
  rw [hF]
  simp only [Ideal.map_span, Set.image_singleton]
  rfl

/-- p. 297: "For the case in which `ℜ = (ℜ^{N,n}_I, F)`, we have `X̄_s = c_s⁻¹(F(s))` for all
`s ≥ 0`", for any completion datum, when `X̄_0 = V(z) = c_0⁻¹(F)` (the induction of
`CD.strictTransformZeroLocus_eq_totalTransform`).

\textbf{Deviation from the paper (gap filled).} The paper states this without proof.  Induction
on `s`: `X̄_0 = V(z) = c_0⁻¹(F)`, and the strict transform commutes with the flat base change
`c_{s+1}` (`MonoidalTransformation.totalTransform_strictTransform_of_flat_square`), using
`B̂_s = c_s⁻¹(B_s)` and `c_s ∘ f̂_s = f_s ∘ c_{s+1}`. -/
theorem Completion.strictTransformZeroLocus_eq_totalTransform {X : Scheme.{u}} {T : Tower X}
    {x₀ : X} (𝒞 : Completion T x₀) (hx : X.IsSimpleAt x₀) (z : Shat X x₀) (F : Subscheme X)
    (h0 : vZ X x₀ z = Subscheme.totalTransform (c0 X x₀) F) (s : ℕ) :
    strictTransformZeroLocus 𝒞.tHat z s =
      Subscheme.totalTransform (𝒞.c s) ((T.pre s).strictTransform F) := by
  induction s with
  | zero => rw [𝒞.c_zero]; exact h0
  | succ s ih =>
    have : Flat (show (𝒞.tHat.monoidalTransformation s).X' ⟶ (T.monoidalTransformation s).X' from
        𝒞.c (s + 1)) := 𝒞.flat_c hx (s + 1)
    have e := Hironaka.MonoidalSuccession.strictTransform_snoc (T.pre s) (T.B s)
      (T.monoidalTransformation s) F
    show Subscheme.strictTransform (𝒞.tHat.monoidalTransformation s)
      (strictTransformZeroLocus 𝒞.tHat z s) = Subscheme.totalTransform (𝒞.c (s + 1))
        ((Hironaka.MonoidalSuccession.snoc (T.pre s) (T.B s)
          (T.monoidalTransformation s)).strictTransform F)
    rw [e, ih]
    exact (MonoidalTransformation.totalTransform_strictTransform_of_flat_square
      (T.monoidalTransformation s) (𝒞.tHat.monoidalTransformation s) (𝒞.c s) (𝒞.c (s + 1))
      (𝒞.c_comm s).symm (𝒞.B_hat s).symm _).symm

/-- p. 296: "Let `J_0` (resp. `J_j`) denote the ideal of `W` (resp. `V_j`) in the local ring
`S`, where `1 ≤ j ≤ β`."  Index `0` is `W`, index `j + 1` is `V_{j+1}`. -/
def jSys {X : Scheme.{u}} (ℜ : DatumI.Raw X) (x₀ : X) :
    Fin (ℜ.β + 1) → Ideal (X.presheaf.stalk x₀) :=
  Fin.cons (α := fun _ => Ideal (X.presheaf.stalk x₀)) (ℜ.W.stalkIdeal x₀)
    (fun j => (ℜ.V j).stalkIdeal x₀)

/-- The conditions [a]–[e] of pp. 296–297 on the data `z`, `b` and the set `Jgen` of the
elements `g_{jki}^{b/i}` of `Ŝ` whose images generate `J̄ ⊆ T̄ = Ŝ/(z)Ŝ`: there is a regular
frame `(T; z)` of `Ŝ` with [a] (closed case) `z ∈ S` generates the prime ideal of `F` in `S`,
[b] (open case) `(T; z)` is `Ĵ_0`-stable, [c] `Ĵ_j`-stable standard bases
`(g_{j1}, …, g_{jm_j})` of `Ĵ_j = J_j Ŝ` with
`g_{jk} = u_{jk}(z^{ν_{jk}} + g_{jk1} z^{ν_{jk}-1} + ⋯ + g_{jkν_{jk}})`, `ν_{jk} = ν^{(k)}(J_j)`,
`u_{jk}` a unit and `g_{jki} ∈ T`, [d] `b = ∏_j ∏_k ν_{jk}!` and [e] `J̄ = (g_{jki}^{b/i}) T̄`. -/
def FrameSpec {X : Scheme.{u}} (x₀ : X) (hx : X.IsSimpleAt x₀) (ℜ : DatumI.Raw X)
    (r : Restriction X) [IsRegularLocalRing (Shat X x₀)] (z : Shat X x₀) (b : ℕ)
    (Jgen : Set (Shat X x₀)) : Prop :=
  haveI : IsRegularLocalRing (X.presheaf.stalk x₀) := hx
  let Jhat : Fin (ℜ.β + 1) → Ideal (Shat X x₀) := fun j =>
    (jSys ℜ x₀ j).map (algebraMap (X.presheaf.stalk x₀) (Shat X x₀))
  ∃ (Fr : RegularFrame (Shat X x₀)) (h1 : Fr.r = 1),
    Fr.z ⟨0, by rw [h1]; exact Nat.one_pos⟩ = z ∧
    (∀ F, r = .closed F → ∃ z₀ : X.presheaf.stalk x₀,
      algebraMap (X.presheaf.stalk x₀) (Shat X x₀) z₀ = z ∧
        F.stalkIdeal x₀ = Ideal.span {z₀}) ∧
    (∀ U, r = .opn U → ∀ i, IsJStable (Jhat 0) (Fr.z i)) ∧
    ∃ (m : Fin (ℜ.β + 1) → ℕ) (g : ∀ j, Fin (m j) → Shat X x₀)
      (v : ∀ j, Fin (m j) → (Shat X x₀)ˣ) (ν : ∀ j, Fin (m j) → ℕ)
      (co : ∀ j k, Fin (ν j k) → Fr.S),
      (∀ j, IsStandardBase (Shat X x₀) (Jhat j) (g j)) ∧
      (∀ j k, IsJStable (Jhat j) (g j k)) ∧
      (∀ j k, (ν j k : ℕ∞) = nuI (X.presheaf.stalk x₀) (jSys ℜ x₀ j) (k : ℕ).succPNat) ∧
      (∀ j k, g j k = (v j k : Shat X x₀) * (z ^ ν j k + ∑ i : Fin (ν j k),
        algebraMap Fr.S (Shat X x₀) (co j k i) * z ^ (ν j k - ((i : ℕ) + 1)))) ∧
      b = ∏ j, ∏ k, (ν j k).factorial ∧
      Jgen = {y | ∃ (j : Fin (ℜ.β + 1)) (k : Fin (m j)) (i : Fin (ν j k)),
        y = algebraMap Fr.S (Shat X x₀) (co j k i) ^ (b / ((i : ℕ) + 1))}

/-- pp. 296–298: the regular frame `(T; z)` of `Ŝ` with [a], [b], [c], the integer `b` and the
ideal `J̄` of [d], [e], and the morphisms `f̄_s : X̄_{s+1} → X̄_s` induced by `f̂_s`.

Formalization notes: the regularity of `Ŝ` is recorded as a field; the choice of `(T; z)`, of
the standard bases and of the coefficients `g_{jki}` is recorded existentially together with
[a]–[e] (`FrameSpec`), the data kept being `z`, `b` and the set `jGen` of the lifts
`g_{jki}^{b/i} ∈ Ŝ` of the generators of `J̄`; `X̄_0 = Spec(T̄)` is the closed subscheme `V(z)`
of `Spec(Ŝ)` (`vZ`) and `X̄_s` its strict transform (`strictTransformZeroLocus`); the morphisms `f̄_s`, determined
by `ι ∘ f̄_s = f̂_s ∘ ι`, are recorded as data.  Existence: `lem:IV.3-setup-exists`. -/
@[blueprint "def:IV.3-frame"
  (statement := /-- Let $J_0$ (resp.\ $J_j$) denote the ideal of $W$ (resp.\ $V_j$) in the
    local ring $S$, where $1\le j\le\beta$. Let $\hat J_j=J_j\hat S$ for $0\le j\le\beta$. We
    choose and fix a regular frame $(T;z)$ of $\hat S$ (\cref{def:III.9}) as follows:
    [a] if $\mathfrak R=(\mathfrak R^{N,n}_{\mathrm I},F)$, then $z$ is an element of $S$ which
    generates the prime ideal of $F$ in $S$; [b] if $\mathfrak R=(\mathfrak R^{N,n}_{\mathrm I},
    U)$, then $(T;z)$ is a $\hat J_0$-stable regular frame of $\hat S$; [c] we have a
    $\hat J_j$-stable standard base $(g_{j1},\dots,g_{jm_j})$ of $\hat J_j$ (\cref{def:III.3})
    for $0\le j\le\beta$, such that we can write
    $g_{jk}=u_{jk}(z^{\nu_{jk}}+g_{jk1}z^{\nu_{jk}-1}+\dots+g_{jk\nu_{jk}})$ where
    $\nu_{jk}=\nu^{(k)}(J_j)$ (\cref{def:III.1}), $u_{jk}$ is a unit in $\hat S$ and
    $g_{jki}\in T$ for $0\le j\le\beta$, $1\le k\le m_j$ and $1\le i\le\nu_{jk}$. By replacing
    $g_{jk}$ by $g_{jk}/u_{jk}$ we may assume $g_{jk}=z^{\nu_{jk}}+\sum_{i=1}^{\nu_{jk}}
    g_{jki}z^{\nu_{jk}-i}$. Let $\bar T=\hat S/(z)\hat S$; we have the canonical isomorphism
    $T\to\bar T$. We define a positive integer $b$ and an ideal $\bar J$ in $\bar T$ as
    follows: [d] $b=\prod_{j=0}^\beta(\prod_{k=1}^{m_j}(\nu_{jk}!))$, and [e]
    $\bar J=(g_{jki}^{b/i})\bar T$, which denotes the ideal in $\bar T$ generated by the images
    in $\bar T$ of the $(b/i)$th powers of $g_{jki}$ for $1\le i\le\nu_{jk}$, $1\le k\le m_j$
    and $0\le j\le\beta$. Let $\bar X_0=\operatorname{Spec}(\bar T)$, which is a non-singular
    subscheme of $\hat X_0$ of codimension $1$ and of dimension $N-1$. Let $\bar X_s$
    $(s\ge0)$ be the strict transform of $\bar X_0$ in $\hat X_s$ by the succession of
    monoidal transformations $\hat g_s\colon\hat X_s\to\hat X_0$ (\cref{def:IV.3-setup}). For
    the case in which $\mathfrak R=(\mathfrak R^{N,n}_{\mathrm I},F)$, we have
    $\bar X_s=c_s^{-1}(F(s))$ for all $s\ge0$. We denote by $\bar f_s$ the morphism
    $\bar X_{s+1}\to\bar X_s$ induced by $\hat f_s$. (pp.~296--298.) (Formalization notes (encoding):
    $J$-stability is Definition~11 of Ch.~III \S9 (\cref{def:III.11}); the regularity of $\hat S$ is recorded as a hypothesis; the choice of
    $(T;z)$, of the standard bases and of the $g_{jki}$ is recorded existentially together
    with [a]--[e], the data kept being $z$, $b$ and the lifts $g_{jki}^{b/i}\in\hat S$ of the
    generators of $\bar J$; $\bar X_0$ is the closed subscheme $V(z)$ of
    $\operatorname{Spec}\hat S$; the morphisms $\bar f_s$ are recorded as data; everything
    exists by \cref{lem:IV.3-setup-exists}.) -/)
  (latexEnv := "definition")]
structure Frame {N n : ℕ} {X : Scheme.{u}} {ℜ : DatumI.Raw X} {P : DatumI.Presentation ℜ}
    {r : Restriction X} {T : Tower X} {x₀ : X} (hS : Standing N n ℜ P r T x₀)
    extends Completion T x₀ where
  /-- `Ŝ` is a regular local ring. -/
  [regShat : IsRegularLocalRing (Shat X x₀)]
  /-- The element `z` of the regular frame `(T; z)`. -/
  z : Shat X x₀
  /-- The positive integer `b` of [d]. -/
  b : ℕ
  /-- The elements `g_{jki}^{b/i}` of `Ŝ` whose images generate `J̄` in `T̄` ([e]). -/
  jGen : Set (Shat X x₀)
  /-- [a]–[e]. -/
  frame : FrameSpec x₀ (hS.ambient.2.1 x₀) ℜ r z b jGen
  /-- The morphisms `f̄_s : X̄_{s+1} → X̄_s` induced by `f̂_s`. -/
  fBar : ∀ s, (strictTransformZeroLocus tHat z (s + 1)).toScheme ⟶
    (strictTransformZeroLocus tHat z s).toScheme
  /-- `f̄_s` is induced by `f̂_s`. -/
  fBar_comm : ∀ s, fBar s ≫ (strictTransformZeroLocus tHat z s).ι =
    (strictTransformZeroLocus tHat z (s + 1)).ι ≫ tHat.f s

/-- pp. 295–298: the objects of the setup exist. -/
@[blueprint "lem:IV.3-setup-exists"
  (statement := /-- Under the standing assumptions (\cref{def:IV.3-standing}), the objects of
    \cref{def:IV.3-setup} and \cref{def:IV.3-frame} exist: the succession $\{f_s\}$ of $X$
    induces a succession $\{\hat f_s\}$ of $\hat X_0=\operatorname{Spec}(\hat S)$ with
    morphisms $c_s\colon\hat X_s\to X_s$ making the diagrams commute, $\hat f_s$ having center
    $c_s^{-1}(B_s)$ and $\hat X_s$ being the product $X_s\times_X\hat X_0$ with first
    projection $c_s$; $\hat S$ is regular; there is a regular frame $(T;z)$ of $\hat S$ with
    [a], [b], [c], and the integer $b$ and the ideal $\bar J$ of [d], [e]; and $\hat f_s$ induces
    morphisms $\bar f_s\colon\bar X_{s+1}\to\bar X_s$. (pp.~295--298.) -/)
  (proof := /-- The monoidal transformations $\hat f_s$ are induced from the $f_s$ by the base
    change $\hat X_0\to X$, and ``in view of the fact that $\hat S$ is faithfully flat over $S$,
    one can show that $\hat X_s$ is canonically isomorphic to the product $X_s\times_X\hat X_0$
    in the category of schemes over $X$ and that $c_s$ is the projection to the first factor''
    (p.~295). The completion of the regular local ring $S$ is regular. ``The existence of such
    a regular frame $(T;z)$ of $\hat S$ can be seen as follows: First we choose $z\in S$ as in
    [a] and [b], where in the case [b] we use Theorem~9, \S10, Ch.~III. We note that in [b] we
    may replace $T$ by any local subring $T'$ of $\hat S$ such that the natural homomorphism
    $\hat S\to\hat S/(z)\hat S$ induces an isomorphism $T'\to\hat S/(z)\hat S$. By Cohen's
    structure theorem of a complete regular local ring, we have a subfield $k$ of $\hat S$ and
    a regular system of parameters $(z,y_1,\dots,y_{N-1})$ of $\hat S$ such that
    $\hat S=k\{z,y_1,\dots,y_{N-1}\}$ (the formal power series ring of $N$ variables). Then we
    choose a $\hat J_j$-stable standard base of $\hat J_j$ for each $j$ $(0\le j\le\beta)$, say
    $(g_{j1},\dots,g_{jm_j})$ (see Theorem~9, \S10, Ch.~III). By replacing $y_j$ by
    $y_j+c_jz$ with suitable $c_j\in k$ $(1\le j\le N-1)$, we may assume that all the $g_{jk}$
    can be written in the form described in [c], where $T=k\{y_1,\dots,y_{N-1}\}$. Then we see
    that $(T;z)$ with this $T$ is a regular frame of $\hat S$ having the properties [a], [b]
    and [c]'' (p.~297). Finally $\bar X_{s+1}$ is the strict transform of $\bar X_s$ by
    $\hat f_s$, so $\hat f_s$ maps it into $\bar X_s$ and induces $\bar f_s$ (p.~167).

    In the formalization: the completion datum is \cref{lem:IV.3-completion-exists}; $z$ is
    chosen by \cref{lem:IV.3-frame-a} in case [a] (the image in $\hat S$ of the generator
    $z_0\in S$ is a member of a regular system of parameters of $\hat S$, as $S\to\hat S$
    transforms regular systems of parameters into such systems) and by \cref{lem:IV.3-frame-b}
    with $J=\hat J_0$ in case [b]; the frame $(T;z)$ and [c] come from \cref{lem:IV.3-frame-c}
    for the ideals $\hat J_0,\dots,\hat J_\beta$; [d] and [e] are definitions; $\bar f_s$ is the
    morphism of the strict transform $\bar X_{s+1}$ into $\bar X_s$ induced by $\hat f_s$ (the
    total transform of $\bar X_s$ is contained in its strict transform).

    \textbf{Deviation from the paper (gap filled).} Theorem~9 is applied to $\hat S$ and
    $\hat J_0$; the paper does not check its hypotheses: $\hat S$ is complete and its residue
    field, that of $S$, has characteristic zero ($X$ is algebraic over a base of characteristic
    zero); $\hat J_0\ne\hat S$ since $x_0\in W$; and $\hat J_0\ne0$ since $\dim W=n<N=\dim X$,
    so that the generic point of $X$ is not on $W$, $J_0\ne0$, and $S\to\hat S$ is injective.
    It also uses tacitly that $\nu^{(k)}(\hat J_j)=\nu^{(k)}(J_j)$ (\cref{cor:III.lem2}, as
    $S\to\hat S$ transforms a regular system of parameters into one). -/)
  (proofUses := ["lem:IV.3-completion-exists", "lem:IV.3-frame-a", "lem:IV.3-frame-b",
    "lem:IV.3-frame-c", "cor:III.lem2"])
  (latexEnv := "lemma")]
theorem Standing.nonempty_frame [Hironaka.HironakaCitedResults.{u}] {N n : ℕ} {X : Scheme.{u}} {ℜ : DatumI.Raw X}
    {P : DatumI.Presentation ℜ} {r : Restriction X} {T : Tower X} {x₀ : X}
    (hS : Standing N n ℜ P r T x₀) : Nonempty (Frame hS) := by
  classical
  have hx : X.IsSimpleAt x₀ := hS.ambient.2.1 x₀
  have : IsRegularLocalRing (X.presheaf.stalk x₀) := hx
  have : IsAlgebraicScheme X := hS.ambient.1
  have : IrreducibleSpace X := hS.ambient.2.2.1
  let α := algebraMap (X.presheaf.stalk x₀) (Shat X x₀)
  have : CharZero (ResidueField (Shat X x₀)) :=
    (RingHom.charZero_iff (ResidueField.map α).injective).mp (charZero_residueField_stalk X x₀)
  have hmaps : RingHom.MapsRSOP α := mapsRSOP_algebraMap_adicCompletion
  have hinj : Function.Injective α := RingHom.MapsRSOP.injective α hmaps
  -- [a] and [b]: the choice of `z`
  obtain ⟨z, hzr, ha, hb⟩ : ∃ z : Shat X x₀, ExtendsToRSOP _ {z} ∧
      (∀ F, r = .closed F → ∃ z₀ : X.presheaf.stalk x₀, α z₀ = z ∧
        F.stalkIdeal x₀ = Ideal.span {z₀}) ∧
      (∀ U, r = .opn U → IsJStable ((jSys ℜ x₀ 0).map α) z) := by
    cases r with
    | closed F =>
      have hxF : x₀ ∈ F.pts := hS.mem_wStar.2
      obtain ⟨z₀, ⟨Z, hzZ, hZ⟩, hF⟩ :=
        ℜ.exists_extendsToRSOP_and_stalkIdeal_eq_span_of_isClosedRestriction hS.ambient.2.1
          hS.isDatum hS.isFor hxF
      refine ⟨α z₀, ⟨Z.image α, ?_, (hmaps.isRegularSystemOfParameters_image hZ).1⟩,
        fun F' hF' => ?_, fun U hU => (by cases hU)⟩
      · rw [Finset.singleton_subset_iff]
        exact Finset.mem_image_of_mem _ (hzZ (Finset.mem_singleton_self z₀))
      · obtain rfl : F = F' := Restriction.closed.inj hF'
        exact ⟨z₀, rfl, hF⟩
    | opn U =>
      have hxW : x₀ ∈ ℜ.W.pts := hS.mem_wStar.1
      have hlt : ℜ.W.dim < X.dim := by
        rw [hS.ambient.2.2.2]
        exact (show ℜ.W.dim = n from hS.dim_W).trans_lt (by exact_mod_cast hS.lt)
      have hW0 : ℜ.W.stalkIdeal x₀ ≠ ⊥ := Subscheme.stalkIdeal_ne_bot_of_genericPoint_notMem ℜ.W
        (LocSucc.genericPoint_notMem_of_dim_lt hlt) x₀
      have hW1 : ℜ.W.stalkIdeal x₀ ≠ ⊤ := Subscheme.mem_pts_iff_stalkIdeal_ne_top.mp hxW
      have hJ : jSys ℜ x₀ 0 = ℜ.W.stalkIdeal x₀ := by simp only [jSys, Fin.cons_zero]
      have hJ0 : (jSys ℜ x₀ 0).map α ≠ ⊥ := by
        rw [hJ]
        intro h
        rw [Ideal.map_eq_bot_iff_le_ker, (RingHom.injective_iff_ker_eq_bot α).mp hinj] at h
        exact hW0 (le_bot_iff.mp h)
      have hJ1 : (jSys ℜ x₀ 0).map α ≠ ⊤ := by
        rw [hJ]
        refine ne_top_of_le_ne_top (maximalIdeal.isMaximal _).ne_top ?_
        rw [Ideal.map_le_iff_le_comap]
        exact (le_maximalIdeal hW1).trans fun a ha => map_nonunit α a ha
      obtain ⟨z, hzJ, hzr⟩ := exists_isJStable_and_extendsToRSOP _ hJ0 hJ1
      exact ⟨z, hzr, fun F hF => (by cases hF), fun _ _ => hzJ⟩
  -- [c]
  obtain ⟨Fr, h1, hFz, m, g, v, ν, co, hstd, hJst, hν, hg, -⟩ :=
    exists_regularFrame_one_and_isJStable_standardBase_weierstrass hzr
      (fun j => (jSys ℜ x₀ j).map α)
  let 𝒞 := T.completion x₀ hx
  refine ⟨{ toCompletion := 𝒞
            z := z
            b := ∏ j, ∏ k, (ν j k).factorial
            jGen := {y | ∃ (j : Fin (ℜ.β + 1)) (k : Fin (m j)) (i : Fin (ν j k)),
              y = algebraMap Fr.S (Shat X x₀) (co j k i) ^
                ((∏ j, ∏ k, (ν j k).factorial) / ((i : ℕ) + 1))}
            frame := ?_
            fBar := fun s => (𝒞.tHat.monoidalTransformation s).strictTransformMap
              (strictTransformZeroLocus 𝒞.tHat z s)
            fBar_comm := fun s => MonoidalTransformation.strictTransformMap_ι _ _ }⟩
  -- [d], [e] are definitions; [a], [b], [c] were arranged above
  refine ⟨Fr, h1, hFz, ha, fun U hU i => ?_, m, g, v, ν, co, hstd, hJst, fun j k => ?_, hg,
    rfl, rfl⟩
  · have hi : Fr.z i = z := by
      rw [← hFz]
      congr 1
      exact Fin.ext (by have := i.2; omega)
    rw [hi]
    exact hb U hU
  · exact (hν j k).trans (nuI_map_eq_of_mapsRSOP α hmaps _ _).symm

/-- The tower-independent data of a frame: the regularity of `Ŝ`, the element `z`, the integer `b`, the
set `jGen` and the conditions [a]-[e] (`FrameSpec`).  A frame exists for every `Standing`
(`Standing.nonempty_frame`) and its data does not depend on the tower beyond the hypotheses of
`Standing`; this extracts it.  (Not in the paper: used to build frames over different towers
with the same data, `Frame.canon`.) -/
theorem Standing.exists_frameData [Hironaka.HironakaCitedResults.{u}] {N n : ℕ} {X : Scheme.{u}} {ℜ : DatumI.Raw X}
    {P : DatumI.Presentation ℜ} {r : Restriction X} {T : Tower X} {x₀ : X}
    (hS : Standing N n ℜ P r T x₀) :
    ∃ (_ : IsRegularLocalRing (Shat X x₀)) (z : Shat X x₀) (b : ℕ) (Jgen : Set (Shat X x₀)),
      Nonempty (FrameSpec x₀ (hS.ambient.2.1 x₀) ℜ r z b Jgen) := by
  obtain ⟨𝒮⟩ := hS.nonempty_frame
  exact ⟨𝒮.regShat, 𝒮.z, 𝒮.b, 𝒮.jGen, ⟨𝒮.frame⟩⟩

/-- A frame over the canonical completion `Tower.completion`, built from the tower-independent
data `(z, b, Jgen)` and `FrameSpec` (the construction of `Standing.nonempty_frame`; the morphisms
`f̄_s` are the maps induced on strict transforms).  For these frames the stage-`s` objects satisfy
the one-step recursion of `StageState.step` definitionally, and depend on the tower only through
`T.pre s`. -/
noncomputable def Frame.canon {N n : ℕ} {X : Scheme.{u}} {ℜ : DatumI.Raw X}
    {P : DatumI.Presentation ℜ} {r : Restriction X} {T : Tower X} {x₀ : X}
    (hS : Standing N n ℜ P r T x₀) [IsRegularLocalRing (Shat X x₀)] (z : Shat X x₀) (b : ℕ)
    (Jgen : Set (Shat X x₀)) (fr : FrameSpec x₀ (hS.ambient.2.1 x₀) ℜ r z b Jgen) : Frame hS where
  toCompletion := T.completion x₀ (hS.ambient.2.1 x₀)
  z := z
  b := b
  jGen := Jgen
  frame := fr
  fBar := fun s => ((T.completion x₀ (hS.ambient.2.1 x₀)).tHat.monoidalTransformation s).strictTransformMap
    (strictTransformZeroLocus (T.completion x₀ (hS.ambient.2.1 x₀)).tHat z s)
  fBar_comm := fun _ => MonoidalTransformation.strictTransformMap_ι _ _

/-- `D` restricted to the open subset `U` is non-singular and everywhere of codimension one in
`U` (the empty subscheme being allowed).  This is what remains true of the paper's
"non-singular irreducible subscheme … of codimension 1" on pp. 298 and 308, whose irreducibility
is false in general. -/
def IsNonsingCodimOneOn {Z : Scheme.{u}} (D : Subscheme Z) (U : Set Z) : Prop :=
  (∀ x ∈ D.pts ∩ U, D.IsSimpleAt x) ∧ ∀ x ∈ D.pts ∩ U, D.codimAt x = 1

namespace Frame

variable {N n : ℕ} {X : Scheme.{u}} {ℜ : DatumI.Raw X} {P : DatumI.Presentation ℜ}
  {r : Restriction X} {T : Tower X} {x₀ : X} {hS : Standing N n ℜ P r T x₀}
  (𝒮 : Frame hS)

/-- `X̄_s`, a subscheme of `X̂_s`. -/
abbrev xBar (s : ℕ) : Subscheme (𝒮.tHat.X s) := strictTransformZeroLocus 𝒮.tHat 𝒮.z s

/-- `c̄_s : X̄_s → X_s`, induced by `c_s` (p. 298). -/
def cBar (s : ℕ) : (𝒮.xBar s).toScheme ⟶ T.X s := (𝒮.xBar s).ι ≫ 𝒮.c s

/-- The sheaf of ideals of `B̂_s = c_s⁻¹(B_s)` restricted to `X̄_s` (p. 298: "the sheaf of
prime ideals of `B̂_s` on `X̄'_s`", i.e. of `B̄'_s = B̂_s ∩ X̄'_s` on `X̄'_s`). -/
def bBarOn (s : ℕ) : Subscheme (𝒮.xBar s).toScheme :=
  Subscheme.totalTransform (𝒮.xBar s).ι (𝒮.tHat.B s)

/-- [f]: "`J̄(0)` = the coherent sheaf of ideals on `X̄_0 (= Spec(T̄))` generated by the ideal
`J̄` in `T̄`", i.e. by the images of the `g_{jki}^{b/i}`. -/
def jBar0 : Subscheme (𝒮.xBar 0).toScheme :=
  Subscheme.totalTransform (𝒮.xBar 0).ι (Scheme.IdealSheafData.ofIdealTop
    ((Ideal.span 𝒮.jGen).map (Scheme.ΓSpecIso (CommRingCat.of (Shat X x₀))).inv.hom))

/-- The condition of [g] (p. 298) for given `X'_s` and `J̄(s)`: `B̂_s = c_s⁻¹(B_s)` is contained
in `X̄_s` and the `b`-th power of the sheaf of prime ideals of `B̂_s` on `X̄'_s = c̄_s⁻¹(X'_s)`
contains `J̄(s)` (at the points of `X̄'_s`). -/
def CondG (s : ℕ) (Xp : (T.X s).Opens) (J : Subscheme (𝒮.xBar s).toScheme) : Prop :=
  (𝒮.tHat.B s).IsContainedIn (𝒮.xBar s) ∧
    ∀ x ∈ 𝒮.cBar s ⁻¹ᵁ Xp, J.stalkIdeal x ≤ ((𝒮.bBarOn s).stalkIdeal x) ^ 𝒮.b

open Classical in
/-- [f]–[i] (pp. 297–299): the open subschemes `X'_s` of `X_s` and the sheaves of ideals `J̄(s)`,
by induction on `s`.  `J̄(s)` is recorded on all of `X̄_s`; only its restriction to `X̄'_s` is
the paper's `J̄(s)` (see `def:IV.3-construction`). -/
@[blueprint "def:IV.3-construction"
  (statement := /-- We define the open subscheme $X_s'$ of $X_s$, $\bar X_s'$ of $\bar X_s$,
    $\hat X_s'$ of $\hat X_s$ and the coherent sheaf of ideals $\bar J(s)$ on $\bar X_s'$, all
    together by induction on $s\ge0$, as follows (\cref{def:IV.3-setup},
    \cref{def:IV.3-frame}):
    [f] $X_0'=X_0$, $\hat X_0'=\hat X_0$, $\bar X_0'=\bar X_0$ and $\bar J(0)=$ the coherent
    sheaf of ideals on $\bar X_0(=\operatorname{Spec}(\bar T))$ generated by the ideal
    $\bar J$ in $\bar T$;
    [g] if $\hat B_s=c_s^{-1}(B_s)$ is contained in $\bar X_s$ and if, at the same time, the
    $b$th power of the sheaf of prime ideals of $\hat B_s$ on $\bar X_s'$ contains the sheaf of
    ideals $\bar J(s)$, then we define $X_{s+1}'=f_s^{-1}(X_s')$,
    $\hat X_{s+1}'=\hat f_s^{-1}(\hat X_s')=c_{s+1}^{-1}(X_{s+1}')$ and
    $\bar X_{s+1}'=\bar f_s^{-1}(\bar X_s')=\hat X_{s+1}'\cap\bar X_{s+1}=
    \bar c_{s+1}^{-1}(X_{s+1}')$, where $\bar f_s$ denotes the morphism
    $\bar X_{s+1}\to\bar X_s$ induced by $\hat f_s$, and $\bar c_{s+1}$ the morphism
    $\bar X_{s+1}\to X_{s+1}$ induced by $c_{s+1}$;
    [h] if either one of the conditions in [g] is not satisfied, then
    $X_{s+1}'=f_s^{-1}(X_s'-B_s)=f_s^{-1}(X_s')-E_{\alpha+s+1}(s+1)$,
    $\hat X_{s+1}'=\hat f_s^{-1}(\hat X_s'-\hat B_s)=c_{s+1}^{-1}(X_{s+1}')$ and
    $\bar X_{s+1}'=\bar f_s^{-1}(\bar X_s'-\hat B_s\cap\bar X_s')=\hat X_{s+1}'\cap
    \bar X_{s+1}=\bar c_{s+1}^{-1}(X_{s+1}')$.
    In both cases we denote by $\bar f_s'\colon\bar X_{s+1}'\to\bar X_s'$ the morphism induced
    by $\bar f_s$; if $\bar B_s'=\hat B_s\cap\bar X_s'$, then $\bar f_s'$ is the monoidal
    transformation with the non-singular center $\bar B_s'$ in the case [g] and an isomorphism
    of $\bar X_{s+1}'$ to $\bar X_s'-\bar B_s'$ in the case [h]. In both cases we set
    $\bar E_{\alpha+s+1}'(s+1)=(\bar f_s')^{-1}(\bar B_s')$, and
    $P(\bar E_{\alpha+s+1}'(s+1))$ its coherent sheaf of ideals on $\bar X_{s+1}'$; it is a
    sheaf of principal ideals whose $b$th power contains $(\bar f_s')^{-1}(\bar J(s))$; and
    [i] we define the coherent sheaf of ideals
    $\bar J(s+1)=(\bar f_s')^{-1}(\bar J(s))/P(\bar E_{\alpha+s+1}'(s+1))^b$ on the
    non-singular irreducible scheme $\bar X_{s+1}'$. (pp.~297--299.)
    (Formalization notes (encoding): the equalities $\hat X_s'=c_s^{-1}(X_s')$ and
    $\bar X_s'=\bar c_s^{-1}(X_s')$ stated in [g], [h] are taken as the definitions of
    $\hat X_s'$ and $\bar X_s'$; $\bar J(s)$ is formed on all of $\bar X_s$ by the same
    formulas (inverse image by $\bar f_s$, division by the $b$th power of the inverse image of
    the ideal of $\hat B_s$, \cref{def:I.7-II}) and agrees with the paper's $\bar J(s)$ on
    $\bar X_s'$, which is the only place where it is used; the containment conditions in [g]
    are required at the points of $\bar X_s'$.) -/)
  (latexEnv := "definition")]
def state : ∀ s, (T.X s).Opens × Subscheme (𝒮.xBar s).toScheme
  | 0 => (⊤, 𝒮.jBar0)
  | s + 1 =>
    ((if 𝒮.CondG s (state s).1 (state s).2
      then T.f s ⁻¹ᵁ (state s).1
      else T.f s ⁻¹ᵁ ((state s).1 ⊓ (T.B s).support.compl)),
     Subscheme.divPow (Subscheme.totalTransform (𝒮.fBar s) (state s).2)
       (Subscheme.totalTransform (𝒮.fBar s) (𝒮.bBarOn s)) 𝒮.b)

/-- The open subscheme `X'_s` of `X_s` ([f]–[h]). -/
def xPrime (s : ℕ) : (T.X s).Opens := (𝒮.state s).1

/-- `X̂'_s = c_s⁻¹(X'_s)` (p. 298). -/
def xHatPrime (s : ℕ) : (𝒮.tHat.X s).Opens := 𝒮.c s ⁻¹ᵁ 𝒮.xPrime s

/-- `X̄'_s = c̄_s⁻¹(X'_s) = X̂'_s ∩ X̄_s` (p. 298). -/
def xBarPrime (s : ℕ) : (𝒮.xBar s).toScheme.Opens := 𝒮.cBar s ⁻¹ᵁ 𝒮.xPrime s

/-- `J̄(s)` ([f], [i]); the paper's sheaf is its restriction to `X̄'_s`. -/
def jBar (s : ℕ) : Subscheme (𝒮.xBar s).toScheme := (𝒮.state s).2

/-- The condition of [g] (p. 298): `B̂_s = c_s⁻¹(B_s)` is contained in `X̄_s` and the `b`-th
power of the sheaf of prime ideals of `B̂_s` on `X̄'_s` contains `J̄(s)`; [h] is its negation. -/
def CaseG (s : ℕ) : Prop := 𝒮.CondG s (𝒮.xPrime s) (𝒮.jBar s)

open Classical in
/-- [g], [h]: `X'_{s+1} = f_s⁻¹(X'_s)` in the case [g] and `f_s⁻¹(X'_s − B_s)` in the case [h]. -/
theorem xPrime_succ (s : ℕ) :
    𝒮.xPrime (s + 1) = if 𝒮.CaseG s then T.f s ⁻¹ᵁ 𝒮.xPrime s
      else T.f s ⁻¹ᵁ (𝒮.xPrime s ⊓ (T.B s).support.compl) := rfl

/-- [i]: `J̄(s+1) = (f̄'_s)⁻¹(J̄(s)) / P(Ē'_{α+s+1}(s+1))^b`. -/
theorem jBar_succ (s : ℕ) :
    𝒮.jBar (s + 1) = Subscheme.divPow (Subscheme.totalTransform (𝒮.fBar s) (𝒮.jBar s))
      (Subscheme.totalTransform (𝒮.fBar s) (𝒮.bBarOn s)) 𝒮.b := rfl

/-- `f̄_s⁻¹(B̄_s)` is a sheaf of principal ideals on `X̄_{s+1}`: it is the restriction of the
exceptional divisor of `f̂_s`. -/
theorem isLocallyPrincipal_totalTransform_fBar_bBarOn (s : ℕ) :
    (Subscheme.totalTransform (𝒮.fBar s) (𝒮.bBarOn s)).IsLocallyPrincipal := by
  show (Subscheme.totalTransform (𝒮.fBar s)
    (Subscheme.totalTransform (𝒮.xBar s).ι (𝒮.tHat.B s))).IsLocallyPrincipal
  rw [← Subscheme.totalTransform_comp, 𝒮.fBar_comm s, Subscheme.totalTransform_comp]
  exact ((𝒮.tHat.monoidalTransformation s).invertible.isLocallyPrincipal).totalTransform _

/-- `f̄_s⁻¹(B̄_s) = c̄_{s+1}⁻¹(E_{α+s+1}(s+1))` as subschemes of `X̄_{s+1}` (p. 298:
"`Ē'_{α+s+1}(s+1) = (f̄'_s)⁻¹(B̄'_s) = c̄_{s+1}⁻¹(E_{α+s+1}(s+1)) ∩ X̄'_{s+1}`"): both are
`ι_{s+1}⁻¹(f̂_s⁻¹(B̂_s))`, by `ι_s ∘ f̄_s = f̂_s ∘ ι_{s+1}`, `c_s ∘ f̂_s = f_s ∘ c_{s+1}` and
`B̂_s = c_s⁻¹(B_s)`. -/
theorem totalTransform_fBar_bBarOn_eq (s : ℕ) :
    Subscheme.totalTransform (𝒮.fBar s) (𝒮.bBarOn s) =
      Subscheme.totalTransform (𝒮.cBar (s + 1)) (T.monoidalTransformation s).exceptional := by
  show Subscheme.totalTransform (𝒮.fBar s) (Subscheme.totalTransform (𝒮.xBar s).ι (𝒮.tHat.B s)) =
    Subscheme.totalTransform ((𝒮.xBar (s + 1)).ι ≫ 𝒮.c (s + 1))
      (Subscheme.totalTransform (T.f s) (T.B s))
  rw [← Subscheme.totalTransform_comp, 𝒮.fBar_comm s, ← Subscheme.totalTransform_comp,
    Category.assoc, ← 𝒮.c_comm s, Subscheme.totalTransform_comp, Subscheme.totalTransform_comp,
    Subscheme.totalTransform_comp, ← 𝒮.B_hat s]

/-- The stalks of a locally principal sheaf of ideals are principal. -/
theorem _root_.Hironaka.Subscheme.exists_stalkIdeal_eq_span_singleton_of_isLocallyPrincipal
    {Y : Scheme.{u}} {D : Subscheme Y} (hD : D.IsLocallyPrincipal) (y : Y) :
    ∃ a, D.stalkIdeal y = Ideal.span {a} := by
  obtain ⟨U, hyU, a, ha⟩ := hD y
  refine ⟨(Y.presheaf.germ (U : Y.Opens) y hyU).hom a, ?_⟩
  rw [Subscheme.stalkIdeal_eq_map_germ_affine D U hyU, ha, Ideal.map_span, Set.image_singleton]

/-- p. 297: "`X̄_0 = Spec(T̄)`" is non-singular and irreducible ("we see", p. 298): `X̄_0 = V(z)`
with `z` a member of a regular system of parameters of the regular local ring `Ŝ`, so `Ŝ/(z)` is
a regular local ring (hence a domain), and the local rings of `V(z)` are its localizations
(Serre, the cited leaf `isRegularLocalRing_localization_of_isRegularLocalRing`).

\textbf{Deviation from the paper (gap filled).} The paper says only "we see" (p. 298); the
argument is that of `CD.Frame.xBar_zero_facts`. -/
theorem xBar_zero_isNonsingular_and_isIrreducible [Hironaka.HironakaCitedResults.{u}] (𝒮 : Frame hS) :
    (𝒮.xBar 0).IsNonsingular ∧ (𝒮.xBar 0).IsIrreducible := by
  classical
  have hreg0 := 𝒮.regShat
  obtain ⟨Fr, h1, hz, -⟩ := 𝒮.frame
  obtain ⟨K, hK, hrsop⟩ := Fr.extends_rsop
  have hzK : 𝒮.z ∈ K := hK (hz ▸ Finset.mem_image_of_mem _ (Finset.mem_univ _))
  have hzM : 𝒮.z ∈ maximalIdeal (Shat X x₀) := hrsop.1 ▸ Ideal.subset_span hzK
  have hext : ExtendsToRSOP (Shat X x₀) {𝒮.z} :=
    ⟨K, Finset.singleton_subset_iff.mpr hzK, hrsop⟩
  have hreg : IsRegularLocalRing (Shat X x₀ ⧸ Ideal.span {𝒮.z}) :=
    hext.isRegularLocalRing_quotient_span_singleton (Finset.mem_singleton_self _)
  have hz0 : 𝒮.z ≠ 0 := hext.ne_zero (Finset.mem_singleton_self _)
  have : IsRegularLocalRing (CommRingCat.of (Shat X x₀)) := hreg0
  have : IsRegularLocalRing (CommRingCat.of (Shat X x₀) ⧸ Ideal.span {𝒮.z}) := hreg
  have : IsDomain (Shat X x₀) := isDomain_of_isRegularLocalRing _
  have : (Ideal.span {𝒮.z}).IsPrime :=
    (Ideal.Quotient.isDomain_iff_prime _).mp (isDomain_of_isRegularLocalRing _)
  have hh : (Ideal.span {𝒮.z}).height = 1 := by
    refine Ideal.height_span_singleton_eq_one_of_mem_nonZeroDivisors
      (mem_nonZeroDivisors_of_ne_zero hz0) ?_
    intro hu
    exact (IsLocalRing.mem_maximalIdeal _).mp hzM hu
  exact ⟨isNonsingular_ofIdealTop_spec (CommRingCat.of (Shat X x₀)) (Ideal.span {𝒮.z}),
    (isIrreducible_and_codim_ofIdealTop_spec (CommRingCat.of (Shat X x₀))
      (Ideal.span {𝒮.z}) hh).1⟩

/-! ### Open families with removals

The facts asserted in the course of the construction (pp. 297–298) concern the open subschemes
`X̄'_s` of the `X̄_s`.  They are stated here for an arbitrary family of open subschemes
`U_s ⊆ X̂_s` with `U_{s+1} = f̂_s⁻¹(U_s − Bad_s)`, where `Bad_s ⊆ B̂_s` is such that the two
containments of [g] hold off `Bad_s`: the printed construction is the family with `Bad_s = ∅`
([g]) or `Bad_s = B̂_s` ([h]), and the corrected construction of
`Hironaka.Ch4.ComponentwiseConstruction` (which removes only the components of `B̂_s` on which
[g] fails) is another such family. -/

/-- An *open family with removals* for the frame `𝒮`: open subschemes `U_s` of the `X̂_s` with
`U_{s+1} = f̂_s⁻¹(U_s − Bad_s)`, where `Bad_s ⊆ B̂_s` is such that, off `Bad_s`, `B̂_s` is
contained in `X̄_s` (stalkwise) and `J̄(s)` is contained in the `b`th power of the ideal of `B̄_s`
at the points of `ι_s⁻¹(U_s)` over `B̂_s`.  The printed construction [f]–[h] is the family with
`Bad_s = ∅` in the case [g] and `Bad_s = B̂_s` in the case [h] (`Frame.removalFamily`). -/
structure RemovalFamily where
  /-- The open subschemes `U_s ⊆ X̂_s`. -/
  U : ∀ s, (𝒮.tHat.X s).Opens
  /-- The removed subsets `Bad_s ⊆ B̂_s`. -/
  bad : ∀ s, Set (𝒮.tHat.X s)
  /-- `Bad_s ⊆ B̂_s`. -/
  bad_subset : ∀ s, bad s ⊆ (𝒮.tHat.B s).pts
  /-- `U_{s+1} = f̂_s⁻¹(U_s − Bad_s)`. -/
  coe_U_succ : ∀ s, (U (s + 1) : Set (𝒮.tHat.X (s + 1))) =
    (𝒮.tHat.f s).base ⁻¹' ((U s : Set (𝒮.tHat.X s)) \ bad s)
  /-- Off `Bad_s`, `B̂_s` is contained in `X̄_s`. -/
  stalkIdeal_xBar_le : ∀ s, ∀ xh ∈ (𝒮.tHat.B s).pts \ bad s,
    (𝒮.xBar s).stalkIdeal xh ≤ (𝒮.tHat.B s).stalkIdeal xh
  /-- Off `Bad_s`, at the points of `ι_s⁻¹(U_s)` over `B̂_s`, `J̄(s) ⊆ P(B̄_s)^b`. -/
  stalkIdeal_jBar_le : ∀ s, ∀ xb : (𝒮.xBar s).toScheme, (𝒮.xBar s).ι.base xb ∈ U s →
    (𝒮.xBar s).ι.base xb ∈ (𝒮.tHat.B s).pts \ bad s →
    (𝒮.jBar s).stalkIdeal xb ≤ ((𝒮.bBarOn s).stalkIdeal xb) ^ 𝒮.b

namespace RemovalFamily

variable {𝒮} (R : 𝒮.RemovalFamily)

/-- The open subschemes `Ū_s = ι_s⁻¹(U_s) = U_s ∩ X̄_s` of the `X̄_s`. -/
def uBar (s : ℕ) : (𝒮.xBar s).toScheme.Opens := (𝒮.xBar s).ι ⁻¹ᵁ R.U s

/-- A point of `Ū_{s+1}` lies over a point of `U_s − Bad_s`. -/
theorem mem_diff_of_mem_uBar_succ (s : ℕ) (xb : (𝒮.xBar (s + 1)).toScheme)
    (hxb : xb ∈ R.uBar (s + 1)) :
    (𝒮.xBar s).ι.base ((𝒮.fBar s).base xb) ∈ (R.U s : Set (𝒮.tHat.X s)) \ R.bad s := by
  have hcomm : (𝒮.tHat.f s).base ((𝒮.xBar (s + 1)).ι.base xb) =
      (𝒮.xBar s).ι.base ((𝒮.fBar s).base xb) :=
    (congrArg (fun φ => φ.base xb) (𝒮.fBar_comm s)).symm
  have h : (𝒮.xBar (s + 1)).ι.base xb ∈ (R.U (s + 1) : Set (𝒮.tHat.X (s + 1))) := hxb
  rw [R.coe_U_succ s] at h
  rw [← hcomm]
  exact h

/-- Local step: at a point of `Ū_{s+1}`, `X̄_s` is simple at the image point (IH) implies the
conclusions of `isRegularLocalRing_stalk_and_exceptional_strictTransform`. -/
theorem isRegularLocalRing_stalk_and_exceptional_of_isSimpleAt_image [Hironaka.HironakaCitedResults.{u}] (s : ℕ) (xb : (𝒮.xBar (s + 1)).toScheme) (hxb : xb ∈ R.uBar (s + 1))
    (hIH : (𝒮.xBar s).toScheme.IsSimpleAt ((𝒮.fBar s).base xb)) :
    IsRegularLocalRing ((𝒮.xBar (s + 1)).toScheme.presheaf.stalk xb) ∧
      (xb ∈ (Subscheme.totalTransform (𝒮.fBar s) (𝒮.bBarOn s)).pts →
        (Subscheme.totalTransform (𝒮.fBar s) (𝒮.bBarOn s)).IsSimpleAt xb ∧
          (Subscheme.totalTransform (𝒮.fBar s) (𝒮.bBarOn s)).codimAt xb = 1) := by
  have hx := R.mem_diff_of_mem_uBar_succ s xb hxb
  have : IsRegularLocalRing ((𝒮.xBar s).toScheme.presheaf.stalk ((𝒮.fBar s).base xb)) := hIH
  exact (𝒮.tHat.monoidalTransformation s).isRegularLocalRing_stalk_and_exceptional_strictTransform
    (𝒮.xBar s) (𝒮.fBar s) (𝒮.fBar_comm s) xb fun hB => ⟨
      R.stalkIdeal_xBar_le s _ ⟨hB, hx.2⟩,
      Subscheme.isRegularLocalRing_quotient_of_isNonsingular
        (𝒮.toCompletion.isNonsingular_B (hS.ambient.2.1 x₀) hS.isNonsingular_X
          hS.isNonsingular_B s) hB⟩

theorem isSimpleAt_of_isSimpleAt_zero [Hironaka.HironakaCitedResults.{u}] (h0 : ∀ xb ∈ R.uBar 0, (𝒮.xBar 0).toScheme.IsSimpleAt xb) :
    ∀ s, ∀ xb ∈ R.uBar s, (𝒮.xBar s).toScheme.IsSimpleAt xb
  | 0 => h0
  | s + 1 => fun xb hxb => by
    have hx := R.mem_diff_of_mem_uBar_succ s xb hxb
    have hIH := isSimpleAt_of_isSimpleAt_zero h0 s ((𝒮.fBar s).base xb) hx.1
    exact (R.isRegularLocalRing_stalk_and_exceptional_of_isSimpleAt_image s xb hxb hIH).1

theorem isIrreducible_xBar_of_isIrreducible_zero (hirr0 : ((𝒮.xBar 0).pts).Nonempty → (𝒮.xBar 0).IsIrreducible) :
    ∀ s, ((𝒮.xBar s).pts).Nonempty → (𝒮.xBar s).IsIrreducible
  | 0 => hirr0
  | s + 1 => fun hne => by
    have hne' := (𝒮.tHat.monoidalTransformation s).pts_nonempty_of_strictTransform _ hne
    exact (𝒮.tHat.monoidalTransformation s).isIrreducible_strictTransform_of_nonempty _
      (isIrreducible_xBar_of_isIrreducible_zero hirr0 s hne') hne

theorem isSimpleAt_and_isIrreducible_and_isNonsingCodimOneOn_of_zero [Hironaka.HironakaCitedResults.{u}] (h0 : ∀ xb ∈ R.uBar 0, (𝒮.xBar 0).toScheme.IsSimpleAt xb)
    (hirr0 : ((𝒮.xBar 0).pts).Nonempty → (𝒮.xBar 0).IsIrreducible) (s : ℕ) :
    (∀ xb ∈ R.uBar s, (𝒮.xBar s).toScheme.IsSimpleAt xb) ∧
    ((R.uBar s : Set (𝒮.xBar s).toScheme).Nonempty →
      IsIrreducible (R.uBar s : Set (𝒮.xBar s).toScheme)) ∧
    IsNonsingCodimOneOn (Subscheme.totalTransform (𝒮.fBar s) (𝒮.bBarOn s))
      (R.uBar (s + 1) : Set (𝒮.xBar (s + 1)).toScheme) := by
  refine ⟨isSimpleAt_of_isSimpleAt_zero R h0 s, fun hne => ?_, ?_⟩
  · obtain ⟨xb, hxb⟩ := hne
    have hp : ((𝒮.xBar s).pts).Nonempty := ⟨(𝒮.xBar s).ι xb, Subscheme.mem_pts_ι _ xb⟩
    exact Subscheme.isIrreducible_of_isOpen (isIrreducible_xBar_of_isIrreducible_zero (𝒮 := 𝒮) hirr0 s hp)
      (R.uBar s).isOpen ⟨xb, hxb⟩
  · refine ⟨fun x hx => ?_, fun x hx => ?_⟩
    · have hxb : x ∈ R.uBar (s + 1) := hx.2
      have hIH := isSimpleAt_of_isSimpleAt_zero R h0 s ((𝒮.fBar s).base x) (R.mem_diff_of_mem_uBar_succ s x hxb).1
      exact ((R.isRegularLocalRing_stalk_and_exceptional_of_isSimpleAt_image s x hxb hIH).2 hx.1).1
    · have hxb : x ∈ R.uBar (s + 1) := hx.2
      have hIH := isSimpleAt_of_isSimpleAt_zero R h0 s ((𝒮.fBar s).base x) (R.mem_diff_of_mem_uBar_succ s x hxb).1
      exact ((R.isRegularLocalRing_stalk_and_exceptional_of_isSimpleAt_image s x hxb hIH).2 hx.1).2

/-- The facts of pp. 297–298 that rest on the theory of monoidal transformations with
non-singular centers, for an arbitrary open family with removals: `X̄_s` is non-singular at the
points of `Ū_s`; `Ū_s` is irreducible when non-empty; and `Ē = f̄_s⁻¹(B̄_s)` is non-singular and
everywhere of codimension `1` on `Ū_{s+1}`.

Proved.

\textbf{Deviation from the paper (gap filled).} The paper says only "We see that
`Ē'_{α+s+1}(s+1)` is a non-singular … subscheme of `X̄'_{s+1}` of codimension 1" and
"`f̄'_s` is the monoidal transformation with the non-singular center `B̄'_s`" (p. 298).  In Lean:
the strict transform `X̄_{s+1}` is identified with the blow-up of `X̄_s` along `B̂_s ∩ X̄_s` and
the regularity of its local rings and of the exceptional divisor are obtained pointwise from
Ch. III § 2 (`StrictTransformRegular.lean`); the irreducibility of `X̄_s` (not only of `Ū_s`)
follows from the irreducibility of strict transforms, and that of `Ū_s` from `X̄_s` being
irreducible; the base case `X̄_0 = V(z)` is `xBar_zero_isNonsingular_and_isIrreducible`.  The argument: 
`X̄_0 = Spec(Ŝ/zŜ)` is the spectrum of a regular local domain, hence non-singular and
irreducible; at a point of `Ū_{s+1}` over `p ∈ U_s − Bad_s`, either `p ∉ B̂_s`, where `f̂_s` is a
local isomorphism and `X̄_{s+1}` is `X̄_s` locally, or `p ∈ B̂_s − Bad_s`, where `B̂_s ⊆ X̄_s` and
`B̄_s = B̂_s ∩ X̄_s` is a non-singular center of the non-singular `X̄_s` at `p`; the strict
transform of `X̄_s` by `f̂_s` is the monoidal transformation of `X̄_s` with center `B̄_s`, which
is non-singular with non-singular exceptional divisor `f̄_s⁻¹(B̄_s)` of codimension `1` (p. 298:
"`f̄'_s` is the monoidal transformation with the non-singular center `B̄'_s`"); a non-empty open
subset of the irreducible `X̄_s` is irreducible. -/
@[blueprint "lem:IV.3-construction-facts-generic"
  (statement := /-- Notation as in \cref{def:IV.3-frame}. Let $U_s\subseteq\hat X_s$ ($s\ge0$)
    be open subschemes with $U_{s+1}=\hat f_s^{-1}(U_s-\mathrm{Bad}_s)$, where
    $\mathrm{Bad}_s\subseteq\hat B_s$ is a subset off which $\hat B_s$ is contained in
    $\bar X_s$ and $\bar J(s)$ is contained in the $b$th power of the ideal of
    $\bar B_s=\hat B_s\cap\bar X_s$ at the points of $\bar U_s=U_s\cap\bar X_s$. Then $\bar X_s$
    is non-singular at the points of $\bar U_s$, $\bar U_s$ is irreducible when non-empty, and
    $\bar f_s^{-1}(\bar B_s)$ is non-singular and everywhere of codimension $1$ on
    $\bar U_{s+1}$. (The facts of pp.~297--298 on $\bar X_s'$ and $\bar E_{\alpha+s+1}'(s+1)$,
    for an arbitrary such family: the construction [f]--[h] of \cref{def:IV.3-construction} is
    the case $\mathrm{Bad}_s=\emptyset$ ([g]) or $\mathrm{Bad}_s=\hat B_s$ ([h]), and the
    corrected construction of \cref{def:IV.3-construction-componentwise} is the case where
    $\mathrm{Bad}_s$ is the union of the bad components of $\hat B_s$.) -/)
  (proof := /-- $\bar X_0=\operatorname{Spec}(\hat S/(z)\hat S)$ is the spectrum of a regular
    local domain. At a point of $\bar U_{s+1}$ over $p\in U_s-\mathrm{Bad}_s$: if
    $p\notin\hat B_s$, $\hat f_s$ is a local isomorphism there and $\bar X_{s+1}$ is $\bar X_s$
    locally; if $p\in\hat B_s-\mathrm{Bad}_s$, then $\hat B_s\subseteq\bar X_s$ at $p$, so
    $\bar B_s$ is a non-singular center of the non-singular $\bar X_s$ there, and the strict
    transform $\bar X_{s+1}$ of $\bar X_s$ is its monoidal transformation with center
    $\bar B_s$ (p.~298), non-singular with the non-singular exceptional divisor
    $\bar f_s^{-1}(\bar B_s)$ of codimension one
    (\cref{lem:monoidal-transformation-nonsingular}). A non-empty open subset of the
    irreducible $\bar X_s$ is irreducible.

    \textbf{Deviation from the paper (gap filled).} The paper says only ``We see'' (p.~298)
    that $\bar f_s'$ is the monoidal transformation with non-singular center $\bar B_s'$. In
    Lean the strict transform $\bar X_{s+1}$ is identified with the blow-up of $\bar X_s$ along
    $\hat B_s\cap\bar X_s$ and the regularity of its local rings and of the exceptional divisor
    is proved pointwise from Ch.~III \S2; irreducibility of $\bar X_s$ (not only of $\bar U_s$)
    follows from the irreducibility of strict transforms; the base case is
    $\bar X_0=V(z)$ with $\hat S/(z)$ regular. -/)
  (latexEnv := "lemma")]
theorem isSimpleAt_and_isIrreducible_and_isNonsingCodimOneOn [Hironaka.HironakaCitedResults.{u}] (s : ℕ) :
    (∀ xb ∈ R.uBar s, (𝒮.xBar s).toScheme.IsSimpleAt xb) ∧
    ((R.uBar s : Set (𝒮.xBar s).toScheme).Nonempty →
      IsIrreducible (R.uBar s : Set (𝒮.xBar s).toScheme)) ∧
    IsNonsingCodimOneOn (Subscheme.totalTransform (𝒮.fBar s) (𝒮.bBarOn s))
      (R.uBar (s + 1) : Set (𝒮.xBar (s + 1)).toScheme) := by
  obtain ⟨h0, hirr0⟩ := xBar_zero_isNonsingular_and_isIrreducible 𝒮
  exact R.isSimpleAt_and_isIrreducible_and_isNonsingCodimOneOn_of_zero (fun xb _ => h0 xb)
    (fun _ => hirr0) s

/-- "`P(Ē'_{α+s+1}(s+1))` is a sheaf of principal ideals on `X̄'_{s+1}` whose `b`th power
contains the sheaf of ideals `(f̄'_s)⁻¹(J̄(s))`" (p. 298), at the points of `Ū_{s+1}`: the bound
`J̄(s) ⊆ P(B̄_s)^b` at the image point pulls back, and over the complement of `B̂_s` the ideal
of `f̄_s⁻¹(B̄_s)` is the unit ideal. -/
theorem stalkIdeal_totalTransform_jBar_le_pow (s : ℕ) (xb : (𝒮.xBar (s + 1)).toScheme)
    (hxb : xb ∈ R.uBar (s + 1)) :
    (Subscheme.totalTransform (𝒮.fBar s) (𝒮.jBar s)).stalkIdeal xb ≤
      ((Subscheme.totalTransform (𝒮.fBar s) (𝒮.bBarOn s)).stalkIdeal xb) ^ 𝒮.b := by
  have hx := R.mem_diff_of_mem_uBar_succ s xb hxb
  rw [stalkIdeal_totalTransform, stalkIdeal_totalTransform, ← Ideal.map_pow]
  refine Ideal.map_mono ?_
  by_cases hB : (𝒮.xBar s).ι.base ((𝒮.fBar s).base xb) ∈ (𝒮.tHat.B s).pts
  · exact R.stalkIdeal_jBar_le s _ hx.1 ⟨hB, hx.2⟩
  · have hB' : (𝒮.bBarOn s).stalkIdeal ((𝒮.fBar s).base xb) = ⊤ := by
      show (Subscheme.totalTransform (𝒮.xBar s).ι (𝒮.tHat.B s)).stalkIdeal _ = ⊤
      rw [stalkIdeal_totalTransform, Subscheme.stalkIdeal_eq_top_of_notMem_pts hB, Ideal.map_top]
    rw [hB', Ideal.top_pow]
    exact le_top

end RemovalFamily

open Classical in
/-- `X̂'_{s+1} = f̂_s⁻¹(X̂'_s)` in the case [g] and `f̂_s⁻¹(X̂'_s − B̂_s)` in the case [h] (p. 298),
from `X̂'_s = c_s⁻¹(X'_s)`, [g], [h], `c_s ∘ f̂_s = f_s ∘ c_{s+1}` and `B̂_s = c_s⁻¹(B_s)`. -/
theorem coe_xHatPrime_succ (s : ℕ) :
    (𝒮.xHatPrime (s + 1) : Set (𝒮.tHat.X (s + 1))) = (𝒮.tHat.f s).base ⁻¹'
      (if 𝒮.CaseG s then (𝒮.xHatPrime s : Set (𝒮.tHat.X s))
        else (𝒮.xHatPrime s : Set (𝒮.tHat.X s)) \ (𝒮.tHat.B s).pts) := by
  ext yh
  have hcc : (𝒮.c s).base ((𝒮.tHat.f s).base yh) = (T.f s).base ((𝒮.c (s + 1)).base yh) :=
    congrArg (fun φ => φ.base yh) (𝒮.c_comm s)
  have hB : (𝒮.tHat.f s).base yh ∈ (𝒮.tHat.B s).pts ↔
      (T.f s).base ((𝒮.c (s + 1)).base yh) ∈ (T.B s).pts := by
    rw [𝒮.B_hat s, Subscheme.pts_totalTransform_eq_preimage, Set.mem_preimage, hcc]
  show (𝒮.c (s + 1)).base yh ∈ 𝒮.xPrime (s + 1) ↔ _
  rw [xPrime_succ, Set.mem_preimage]
  split_ifs with hc
  · show (T.f s).base ((𝒮.c (s + 1)).base yh) ∈ 𝒮.xPrime s ↔
      (𝒮.c s).base ((𝒮.tHat.f s).base yh) ∈ 𝒮.xPrime s
    rw [hcc]
  · show (T.f s).base ((𝒮.c (s + 1)).base yh) ∈ 𝒮.xPrime s ⊓ (T.B s).support.compl ↔
      (𝒮.c s).base ((𝒮.tHat.f s).base yh) ∈ 𝒮.xPrime s ∧
        (𝒮.tHat.f s).base yh ∉ (𝒮.tHat.B s).pts
    rw [hB, hcc]
    exact Iff.rfl

open Classical in
/-- `X̄'_{s+1} = f̄_s⁻¹(X̄'_s)` in the case [g] and `f̄_s⁻¹(X̄'_s − B̂_s ∩ X̄'_s)` in the case [h]
(p. 298), from `coe_xHatPrime_succ` and `ι_s ∘ f̄_s = f̂_s ∘ ι_{s+1}`. -/
theorem coe_xBarPrime_succ (s : ℕ) :
    (𝒮.xBarPrime (s + 1) : Set (𝒮.xBar (s + 1)).toScheme) = (𝒮.fBar s).base ⁻¹'
      (if 𝒮.CaseG s then (𝒮.xBarPrime s : Set (𝒮.xBar s).toScheme)
        else (𝒮.xBarPrime s : Set (𝒮.xBar s).toScheme) \ (𝒮.bBarOn s).pts) := by
  ext xb
  have hcomm : (𝒮.tHat.f s).base ((𝒮.xBar (s + 1)).ι.base xb) =
      (𝒮.xBar s).ι.base ((𝒮.fBar s).base xb) :=
    (congrArg (fun φ => φ.base xb) (𝒮.fBar_comm s)).symm
  have h1 : xb ∈ (𝒮.xBarPrime (s + 1) : Set (𝒮.xBar (s + 1)).toScheme) ↔
      (𝒮.xBar (s + 1)).ι.base xb ∈ (𝒮.xHatPrime (s + 1) : Set (𝒮.tHat.X (s + 1))) := Iff.rfl
  have hBb : (𝒮.fBar s).base xb ∈ (𝒮.bBarOn s).pts ↔
      (𝒮.xBar s).ι.base ((𝒮.fBar s).base xb) ∈ (𝒮.tHat.B s).pts := by
    show (𝒮.fBar s).base xb ∈ (Subscheme.totalTransform (𝒮.xBar s).ι (𝒮.tHat.B s)).pts ↔ _
    rw [Subscheme.pts_totalTransform_eq_preimage, Set.mem_preimage]
  rw [h1, 𝒮.coe_xHatPrime_succ s, Set.mem_preimage, Set.mem_preimage, hcomm]
  split_ifs with hc
  · exact Iff.rfl
  · rw [Set.mem_sdiff, Set.mem_sdiff, hBb]
    exact Iff.rfl

open Classical in
/-- The printed construction [f]–[h] (pp. 297–299) as an open family with removals: `U_s = X̂'_s`,
and `Bad_s = ∅` in the case [g], `Bad_s = B̂_s` in the case [h]. -/
def removalFamily : 𝒮.RemovalFamily where
  U := 𝒮.xHatPrime
  bad s := if 𝒮.CaseG s then ∅ else (𝒮.tHat.B s).pts
  bad_subset s := by split_ifs <;> simp
  coe_U_succ s := by
    rw [𝒮.coe_xHatPrime_succ s]
    split_ifs <;> simp
  stalkIdeal_xBar_le s xh hxh := by
    split_ifs at hxh with hc
    · exact Subscheme.stalkIdeal_le_stalkIdeal_of_isContainedIn hc.1 xh
    · exact absurd hxh.1 hxh.2
  stalkIdeal_jBar_le s xb hU hB := by
    split_ifs at hB with hc
    · exact hc.2 xb hU
    · exact absurd hB.1 hB.2

/-- p. 297: "For the case in which `ℜ = (ℜ^{N,n}_I, F)`, we have `X̄_s = c_s⁻¹(F(s))` for all
`s ≥ 0`" (the first assertion of `lem:IV.3-construction-facts`).

\textbf{Deviation from the paper (gap filled).} The paper states this without proof; it follows
from [a] and the commutation of strict transforms with the flat base change `c_s`
(`Completion.strictTransformZeroLocus_eq_totalTransform`). -/
theorem xBar_eq_totalTransform_of_closed (s : ℕ) (F : Subscheme X) (hF : r = .closed F) :
    𝒮.xBar s = Subscheme.totalTransform (𝒮.c s) ((T.pre s).strictTransform F) := by
  obtain ⟨Fr, h1, hFz, ha, -⟩ := 𝒮.frame
  obtain ⟨z₀, hz₀, hFz₀⟩ := ha F hF
  refine 𝒮.strictTransformZeroLocus_eq_totalTransform (hS.ambient.2.1 x₀) 𝒮.z F ?_ s
  rw [← hz₀]
  exact vZ_algebraMap_eq_totalTransform_c0 F z₀ hFz₀

open Classical in
/-- The facts asserted in the course of the construction (pp. 297–298).

The further remark of p. 298, that `f̄'_s` is the monoidal transformation with the non-singular
center `B̄'_s` in the case [g] and an isomorphism onto `X̄'_s − B̄'_s` in the case [h], is the
separate node `lem:IV.3-construction-facts-fbar-prime`
(`isMonoidalTransformationOf_and_exists_iso_fBarPrime`).

\textbf{Deviation from the paper (gap filled).} The first assertion ("For the case in which
`ℜ = (ℜ^{N,n}_I, F)`, we have `X̄_s = c_s⁻¹(F(s))` for all `s ≥ 0`", p. 297) is stated without
proof; it is proved from [a] and the commutation of strict transforms with the flat base change
`c_s` (`Completion.strictTransformZeroLocus_eq_totalTransform`).  The descriptions of `X̂'_{s+1}`
and `X̄'_{s+1}` (`coe_xHatPrime_succ`, `coe_xBarPrime_succ`), the identification
`f̄_s⁻¹(B̄_s) = c̄_{s+1}⁻¹(E_{α+s+1}(s+1))` (`totalTransform_fBar_bBarOn_eq`), the principality of
its ideal and the bound on `(f̄'_s)⁻¹(J̄(s))` (`RemovalFamily.stalkIdeal_totalTransform_jBar_le_pow`)
are proved; the non-singularity of `X̄'_s`, its irreducibility and the non-singularity and
codimension of `Ē'_{α+s+1}(s+1)` are taken from `lem:IV.3-construction-facts-generic` (proved, stated
for any open family with removals, `RemovalFamily`), applied to the printed family
`removalFamily`.

Statement false as printed (the irreducibility): "We see that `Ē'_{α+s+1}(s + 1)` is a
non-singular irreducible subscheme of `X̄'_{s+1}` of codimension 1, and that
`P(Ē'_{α+s+1}(s + 1))` is a sheaf of principal ideals on `X̄'_{s+1}` whose `b`th power contains
the sheaf of ideals `(f̄'_s)⁻¹(J̄(s))` on `X̄'_{s+1}` generated by `J̄(s)` by means of `f̄'_{s+1}`
[sic: `f̄'_s`]" (p. 298).  The Lean statement asserts only that `Ē'_{α+s+1}(s + 1)` is
non-singular and everywhere of codimension 1 on `X̄'_{s+1}` (`IsNonsingCodimOneOn`). -/
@[blueprint "lem:IV.3-construction-facts"
  (statement := /-- In the construction of \cref{def:IV.3-frame} and
    \cref{def:IV.3-construction}: for the case in which
    $\mathfrak R=(\mathfrak R^{N,n}_{\mathrm I},F)$, we have $\bar X_s=c_s^{-1}(F(s))$ for all
    $s\ge0$ (p.~297); $\hat X_{s+1}'=\hat f_s^{-1}(\hat X_s')$ in the case [g] and
    $\hat X_{s+1}'=\hat f_s^{-1}(\hat X_s'-\hat B_s)$ in the case [h], and
    $\bar X_{s+1}'=\bar f_s^{-1}(\bar X_s')$ in the case [g] and
    $\bar X_{s+1}'=\bar f_s^{-1}(\bar X_s'-\hat B_s\cap\bar X_s')$ in the case [h]; the
    scheme $\bar X_s'$ is non-singular and irreducible; in both cases
    $\bar E_{\alpha+s+1}'(s+1)=(\bar f_s')^{-1}(\bar B_s')=\bar c_{s+1}^{-1}(E_{\alpha+s+1}(s+1))
    \cap\bar X_{s+1}'$, it is non-singular and everywhere of codimension $1$ in
    $\bar X_{s+1}'$, and $P(\bar E_{\alpha+s+1}'(s+1))$ is a sheaf of principal ideals on
    $\bar X_{s+1}'$ whose $b$th power contains the sheaf of ideals
    $(\bar f_s')^{-1}(\bar J(s))$ on $\bar X_{s+1}'$ generated by $\bar J(s)$. (pp.~297--298.)
    (Formalization notes (encoding): the sheaves are compared at the points of
    $\bar X_{s+1}'$; irreducibility of $\bar X_s'$ is asserted when it is non-empty.)

    \textbf{Statement false as printed (the irreducibility).} The paper: ``We see that
    $\bar E_{\alpha+s+1}'(s+1)$ is a non-singular irreducible subscheme of $\bar X_{s+1}'$ of
    codimension 1'' (p.~298). It need not be irreducible (as $\hat B_s$ need not be,
    \cref{lem:IV.AB-4-componentwise}); only its non-singularity and codimension are stated.

    \textbf{Not part of this statement.} The further remark of p.~298 that $\bar f_s'$ is the
    monoidal transformation with the non-singular center $\bar B_s'$ in the case [g], and an
    isomorphism of $\bar X_{s+1}'$ onto $\bar X_s'-\bar B_s'$ in the case [h], is the separate
    node \cref{lem:IV.3-construction-facts-fbar-prime}. -/)
  (proof := /-- $\bar X_0=V(z)$ and, by [a], $z$ generates the ideal of $F$ at $x_0$, so
    $\bar X_0=c_0^{-1}(F)$; strict transforms commute with the flat base change $c_s$, whence
    $\bar X_s=c_s^{-1}(F(s))$. The descriptions of $\hat X_{s+1}'$ and $\bar X_{s+1}'$ follow
    from $\hat X_{s+1}'=c_{s+1}^{-1}(X_{s+1}')$, $\bar X_{s+1}'=\bar c_{s+1}^{-1}(X_{s+1}')$, the
    commutativity $c_s\circ\hat f_s=f_s\circ c_{s+1}$ and $\hat B_s=c_s^{-1}(B_s)$. $\bar X_0$
    is the spectrum of the regular local ring $\hat S/(z)\hat S$, and strict transforms of a
    non-singular irreducible scheme along monoidal transformations with non-singular centers
    are non-singular and irreducible (\cref{lem:monoidal-transformation-nonsingular}). In the
    case [g], $\bar B_s'$ is a non-singular center in $\bar X_s'$, its inverse image is the
    exceptional divisor of $\bar f_s'$, invertible (\cref{def:monoidal-transformation}) and
    non-singular of codimension one, and the containment
    $\bar J(s)\subseteq P(\bar B_s')^b$ pulls back; in the case [h], $\bar X_{s+1}'$ maps into
    $\bar X_s'-\bar B_s'$, so $\bar E_{\alpha+s+1}'(s+1)$ is empty.

    \textbf{Deviation from the paper (gap filled).} The paper states $\bar X_s=c_s^{-1}(F(s))$
    without proof. It is proved by induction on $s$: $\bar X_0=V(z)=c_0^{-1}(F)$ by [a], and
    $\bar X_{s+1}$, the strict transform of $\bar X_s=c_s^{-1}(F(s))$ by $\hat f_s$, is
    $c_{s+1}^{-1}$ of the strict transform $F(s+1)$ of $F(s)$, because $c_{s+1}$ is flat (a base
    change of $\hat X_0\to X$) and colon ideals commute with flat extensions. The descriptions
    of $\hat X_{s+1}'$ and $\bar X_{s+1}'$, the identification
    $\bar f_s^{-1}(\bar B_s)=\bar c_{s+1}^{-1}(E_{\alpha+s+1}(s+1))$, the principality of its
    ideal and the bound on $(\bar f_s')^{-1}(\bar J(s))$ are proved as stated; the
    non-singularity and irreducibility of $\bar X_s'$ and the non-singularity and codimension of
    $\bar E_{\alpha+s+1}'(s+1)$ are the case $\mathrm{Bad}_s=\emptyset$ ([g]) or $\hat B_s$ ([h])
    of \cref{lem:IV.3-construction-facts-generic}. -/)
  (proofUses := ["lem:IV.3-construction-facts-generic", "def:IV.3-construction"])
  (latexEnv := "lemma")]
theorem xBar_eq_totalTransform_and_xbp_succ_eq_preimage [Hironaka.HironakaCitedResults.{u}] (s : ℕ) :
    (∀ F, r = .closed F →
      𝒮.xBar s = Subscheme.totalTransform (𝒮.c s) ((T.pre s).strictTransform F)) ∧
    ((𝒮.xHatPrime (s + 1) : Set (𝒮.tHat.X (s + 1))) = (𝒮.tHat.f s).base ⁻¹'
      (if 𝒮.CaseG s then (𝒮.xHatPrime s : Set (𝒮.tHat.X s))
        else (𝒮.xHatPrime s : Set (𝒮.tHat.X s)) \ (𝒮.tHat.B s).pts)) ∧
    ((𝒮.xBarPrime (s + 1) : Set (𝒮.xBar (s + 1)).toScheme) = (𝒮.fBar s).base ⁻¹'
      (if 𝒮.CaseG s then (𝒮.xBarPrime s : Set (𝒮.xBar s).toScheme)
        else (𝒮.xBarPrime s : Set (𝒮.xBar s).toScheme) \ (𝒮.bBarOn s).pts)) ∧
    (∀ x ∈ 𝒮.xBarPrime s, (𝒮.xBar s).toScheme.IsSimpleAt x) ∧
    ((𝒮.xBarPrime s : Set (𝒮.xBar s).toScheme).Nonempty →
      IsIrreducible (𝒮.xBarPrime s : Set (𝒮.xBar s).toScheme)) ∧
    IsNonsingCodimOneOn (Subscheme.totalTransform (𝒮.fBar s) (𝒮.bBarOn s))
      (𝒮.xBarPrime (s + 1) : Set (𝒮.xBar (s + 1)).toScheme) ∧
    ∀ x ∈ 𝒮.xBarPrime (s + 1),
      (Subscheme.totalTransform (𝒮.fBar s) (𝒮.bBarOn s)).stalkIdeal x =
        (Subscheme.totalTransform (𝒮.cBar (s + 1)) (T.monoidalTransformation s).exceptional).stalkIdeal x ∧
      (∃ a, (Subscheme.totalTransform (𝒮.fBar s) (𝒮.bBarOn s)).stalkIdeal x = Ideal.span {a}) ∧
      (Subscheme.totalTransform (𝒮.fBar s) (𝒮.jBar s)).stalkIdeal x ≤
        ((Subscheme.totalTransform (𝒮.fBar s) (𝒮.bBarOn s)).stalkIdeal x) ^ 𝒮.b := by
  obtain ⟨hns, hirr, hE⟩ :=
    𝒮.removalFamily.isSimpleAt_and_isIrreducible_and_isNonsingCodimOneOn s
  refine ⟨fun F hF => 𝒮.xBar_eq_totalTransform_of_closed s F hF, 𝒮.coe_xHatPrime_succ s,
    𝒮.coe_xBarPrime_succ s, hns, hirr, hE, fun x hx => ⟨?_, ?_, ?_⟩⟩
  · exact congrArg (fun D => Subscheme.stalkIdeal D x) (𝒮.totalTransform_fBar_bBarOn_eq s)
  · exact Subscheme.exists_stalkIdeal_eq_span_singleton_of_isLocallyPrincipal
      (𝒮.isLocallyPrincipal_totalTransform_fBar_bBarOn s) x
  · exact 𝒮.removalFamily.stalkIdeal_totalTransform_jBar_le_pow s x hx

/-! ### The map `f̄'_s : X̄'_{s+1} → X̄'_s` (p. 298) -/

/-- `f̄_s : X̄_{s+1} → X̄_s` is the map induced by `f̂_s` on strict transforms (`ι ∘ f̄_s = f̂_s ∘ ι`
and `ι` is a monomorphism). -/
theorem fBar_eq_strictTransformMap (s : ℕ) :
    𝒮.fBar s = (𝒮.tHat.monoidalTransformation s).strictTransformMap (𝒮.xBar s) :=
  (cancel_mono (𝒮.xBar s).ι).mp
    ((𝒮.fBar_comm s).trans (MonoidalTransformation.strictTransformMap_ι _ _).symm)

/-- p. 167, (a), (b): `f̄_s : X̄_{s+1} → X̄_s` is a monoidal transformation of `X̄_s` with center
`B̂_s ∩ X̄_s` (the strict transform of `X̄_s` by `f̂_s`, `B̂_s = c_s⁻¹(B_s)`). -/
theorem isMonoidalTransformationOf_fBar [Hironaka.HironakaCitedResults.{u}] (s : ℕ) :
    IsMonoidalTransformationOf (𝒮.fBar s) (𝒮.bBarOn s) := by
  rw [𝒮.fBar_eq_strictTransformMap s]
  exact (𝒮.tHat.monoidalTransformation s).isMonoidalTransformationOf_strictTransformMap (𝒮.xBar s)

/-- `B̄'_s = B̂_s ∩ X̄'_s`, as a subscheme of `X̄'_s` (p. 298: "if `B̄'_s` denotes the subscheme
`B̂_s ∩ X̄'_s` of `X̄'_s`"). -/
def bBarPrime (s : ℕ) : Subscheme (𝒮.xBarPrime s).toScheme :=
  Subscheme.totalTransform (𝒮.xBarPrime s).ι (𝒮.bBarOn s)

open Classical in
/-- `X̄'_{s+1} ⊆ f̄_s⁻¹(X̄'_s)` (by `coe_xBarPrime_succ`), so that `f̄_s` induces a morphism
`X̄'_{s+1} → X̄'_s`. -/
theorem xBarPrime_succ_le (s : ℕ) : 𝒮.xBarPrime (s + 1) ≤ 𝒮.fBar s ⁻¹ᵁ 𝒮.xBarPrime s := by
  intro x hx
  have h : x ∈ (𝒮.xBarPrime (s + 1) : Set (𝒮.xBar (s + 1)).toScheme) := hx
  rw [𝒮.coe_xBarPrime_succ s, Set.mem_preimage] at h
  split_ifs at h with hc
  · exact h
  · exact h.1

/-- `f̄'_s : X̄'_{s+1} → X̄'_s`, "the morphism induced by `f̄_s` (hence, by `f̂_s`)" (p. 298). -/
def fBarPrime (s : ℕ) : (𝒮.xBarPrime (s + 1)).toScheme ⟶ (𝒮.xBarPrime s).toScheme :=
  (𝒮.fBar s).resLE (𝒮.xBarPrime s) (𝒮.xBarPrime (s + 1)) (𝒮.xBarPrime_succ_le s)

/-- `ι'_s ∘ f̄'_s = ι'_{s+1} ∘ f̄_s`, `ι'_s : X̄'_s → X̄_s` the inclusion of the open subscheme. -/
theorem fBarPrime_comp_ι (s : ℕ) :
    𝒮.fBarPrime s ≫ (𝒮.xBarPrime s).ι = (𝒮.xBarPrime (s + 1)).ι ≫ 𝒮.fBar s :=
  Scheme.Hom.resLE_comp_ι _ _

open Classical in
/-- [g] (p. 298): `X̄'_{s+1} = f̄_s⁻¹(X̄'_s)`. -/
theorem xBarPrime_succ_of_caseG (s : ℕ) (hc : 𝒮.CaseG s) :
    𝒮.xBarPrime (s + 1) = 𝒮.fBar s ⁻¹ᵁ 𝒮.xBarPrime s := by
  refine TopologicalSpace.Opens.ext ?_
  rw [𝒮.coe_xBarPrime_succ s]
  split_ifs
  rfl

open Classical in
/-- [h] (p. 298): `X̄'_{s+1} = f̄_s⁻¹(X̄'_s − B̂_s ∩ X̄'_s)`, the open set `X̄'_s − B̂_s` of `X̄_s`
being `X̄'_s ∩ (X̄_s − B̂_s ∩ X̄_s)`. -/
theorem xBarPrime_succ_of_not_caseG (s : ℕ) (hc : ¬ 𝒮.CaseG s) :
    𝒮.xBarPrime (s + 1) = 𝒮.fBar s ⁻¹ᵁ (𝒮.xBarPrime s ⊓ (𝒮.bBarOn s).support.compl) := by
  refine TopologicalSpace.Opens.ext ?_
  rw [𝒮.coe_xBarPrime_succ s]
  split_ifs
  rfl

/-- The center `B̄'_s = B̂_s ∩ X̄'_s` is non-singular when `B̂_s ⊆ X̄_s` (first condition of [g]):
then `B̂_s ∩ X̄_s` is isomorphic to `B̂_s`, which is non-singular, and `X̄'_s ⊆ X̄_s` is open. -/
theorem isNonsingular_bBarPrime [Hironaka.HironakaCitedResults.{u}] (s : ℕ) (hc : (𝒮.tHat.B s).IsContainedIn (𝒮.xBar s)) :
    (𝒮.bBarPrime s).IsNonsingular := by
  obtain ⟨e⟩ := CD.nonempty_totalTransform_iso_of_isContainedIn hc
  have h1 : (𝒮.bBarOn s).IsNonsingular :=
    CD.isNonsingular_of_iso e (𝒮.toCompletion.isNonsingular_B (hS.ambient.2.1 x₀)
      hS.isNonsingular_X hS.isNonsingular_B s)
  exact FlatPreimm.isNonsingular_totalTransform (𝒮.xBarPrime s).ι (𝒮.bBarOn s) h1

/-- The case [g] of the remark of p. 298: `f̄'_s : X̄'_{s+1} → X̄'_s` is the monoidal
transformation with center `B̄'_s = B̂_s ∩ X̄'_s` of `X̄'_s`.  By the case [g], `X̄'_{s+1} =
f̄_s⁻¹(X̄'_s)`, so `f̄'_s` is `f̄_s` restricted over the open subscheme `X̄'_s` of `X̄_s`, and
`f̄_s` is a monoidal transformation with center `B̂_s ∩ X̄_s`. -/
theorem isMonoidalTransformationOf_fBarPrime [Hironaka.HironakaCitedResults.{u}] (s : ℕ) (hc : 𝒮.CaseG s) :
    IsMonoidalTransformationOf (𝒮.fBarPrime s) (𝒮.bBarPrime s) := by
  have hopen := 𝒮.xBarPrime_succ_of_caseG s hc
  have hres := (𝒮.isMonoidalTransformationOf_fBar s).morphismRestrict (𝒮.xBarPrime s)
  let e₁ : (𝒮.xBarPrime (s + 1)).toScheme ≅ (𝒮.fBar s ⁻¹ᵁ 𝒮.xBarPrime s).toScheme :=
    Scheme.isoOfEq _ hopen
  let m : MonoidalTransformation (𝒮.xBarPrime s).toScheme (𝒮.bBarPrime s) :=
    ⟨(𝒮.fBar s ⁻¹ᵁ 𝒮.xBarPrime s).toScheme, 𝒮.fBar s ∣_ 𝒮.xBarPrime s, hres.1, hres.2⟩
  refine IsMonoidalTransformationOf.of_iso m e₁ _ ?_
  have h1 : e₁.hom ≫ (𝒮.fBar s ⁻¹ᵁ 𝒮.xBarPrime s).ι = (𝒮.xBarPrime (s + 1)).ι :=
    Scheme.isoOfEq_hom_ι _ hopen
  refine (cancel_mono (𝒮.xBarPrime s).ι).mp ?_
  show (e₁.hom ≫ (𝒮.fBar s ∣_ 𝒮.xBarPrime s)) ≫ (𝒮.xBarPrime s).ι = _
  rw [𝒮.fBarPrime_comp_ι s, Category.assoc, morphismRestrict_ι, ← Category.assoc, h1]

/-- The open subscheme `X̄'_s − B̄'_s` of `X̄'_s` (p. 298). -/
def bBarPrimeCompl (s : ℕ) : (𝒮.xBarPrime s).toScheme.Opens := (𝒮.bBarPrime s).support.compl

/-- The case [h] of the remark of p. 298: `f̄'_s : X̄'_{s+1} → X̄'_s` is an isomorphism of
`X̄'_{s+1}` onto the open subscheme `X̄'_s − B̄'_s` of `X̄'_s`.  By [h], `X̄'_{s+1} = f̄_s⁻¹(Ω)` with
`Ω = X̄'_s − B̂_s` an open subscheme of `X̄_s` missing the center of the monoidal transformation
`f̄_s`, over which `f̄_s` is an isomorphism. -/
theorem exists_iso_fBarPrime [Hironaka.HironakaCitedResults.{u}] (s : ℕ) (hc : ¬ 𝒮.CaseG s) :
    ∃ e : (𝒮.xBarPrime (s + 1)).toScheme ≅ (𝒮.bBarPrimeCompl s).toScheme,
      e.hom ≫ (𝒮.bBarPrimeCompl s).ι = 𝒮.fBarPrime s := by
  have hopen := 𝒮.xBarPrime_succ_of_not_caseG s hc
  set Ω' : (𝒮.xBar s).toScheme.Opens := 𝒮.xBarPrime s ⊓ (𝒮.bBarOn s).support.compl with hΩ'
  have hiso : IsIso (𝒮.fBar s ∣_ Ω') :=
    (𝒮.isMonoidalTransformationOf_fBar s).isIso_morphismRestrict_of_forall_notMem Ω'
      (fun z hz => hz.2)
  let e₁ : (𝒮.xBarPrime (s + 1)).toScheme ≅ (𝒮.fBar s ⁻¹ᵁ Ω').toScheme :=
    Scheme.isoOfEq _ hopen
  have h1 : e₁.hom ≫ (𝒮.fBar s ⁻¹ᵁ Ω').ι = (𝒮.xBarPrime (s + 1)).ι :=
    Scheme.isoOfEq_hom_ι _ hopen
  have hcomp : 𝒮.fBarPrime s ≫ (𝒮.xBarPrime s).ι = (e₁.hom ≫ (𝒮.fBar s ∣_ Ω')) ≫ Ω'.ι := by
    rw [𝒮.fBarPrime_comp_ι s, ← h1, Category.assoc, ← morphismRestrict_ι, Category.assoc]
  have hop : IsOpenImmersion (𝒮.fBarPrime s ≫ (𝒮.xBarPrime s).ι) := by
    rw [hcomp]; infer_instance
  have : IsOpenImmersion (𝒮.fBarPrime s) := IsOpenImmersion.of_comp _ (𝒮.xBarPrime s).ι
  have hpts : ∀ y : (𝒮.xBarPrime s).toScheme, y ∈ (𝒮.bBarPrime s).pts ↔
      (𝒮.xBarPrime s).ι y ∈ (𝒮.bBarOn s).pts := fun y => by
    show y ∈ (Subscheme.totalTransform (𝒮.xBarPrime s).ι (𝒮.bBarOn s)).pts ↔ _
    rw [Subscheme.pts_totalTransform_eq_preimage, Set.mem_preimage]
  have hrange0 : Set.range (𝒮.fBarPrime s ≫ (𝒮.xBarPrime s).ι) = (Ω' : Set (𝒮.xBar s).toScheme) := by
    rw [hcomp]
    have hs : Function.Surjective (e₁.hom ≫ (𝒮.fBar s ∣_ Ω')) := Scheme.Hom.surjective _
    have h2 : Set.range ((e₁.hom ≫ (𝒮.fBar s ∣_ Ω')) ≫ Ω'.ι) = Set.range Ω'.ι := by
      show Set.range (Ω'.ι ∘ (e₁.hom ≫ (𝒮.fBar s ∣_ Ω'))) = _
      rw [Set.range_comp, hs.range_eq, Set.image_univ]
    rw [h2, Scheme.Opens.range_ι]
  have hinj : Function.Injective (𝒮.xBarPrime s).ι := (𝒮.xBarPrime s).ι.isOpenEmbedding.injective
  have hrange : Set.range (𝒮.fBarPrime s) = (𝒮.bBarPrimeCompl s : Set (𝒮.xBarPrime s).toScheme) := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      have h2 : (𝒮.xBarPrime s).ι (𝒮.fBarPrime s x) ∈
          Set.range (𝒮.fBarPrime s ≫ (𝒮.xBarPrime s).ι) := ⟨x, rfl⟩
      rw [hrange0] at h2
      exact fun hmem => h2.2 ((hpts _).mp hmem)
    · intro hy
      have h2 : (𝒮.xBarPrime s).ι y ∈ Set.range (𝒮.fBarPrime s ≫ (𝒮.xBarPrime s).ι) := by
        rw [hrange0]
        exact ⟨y.2, fun hm => hy ((hpts y).mpr hm)⟩
      obtain ⟨x, hx⟩ := h2
      exact ⟨x, hinj hx⟩
  exact ⟨IsOpenImmersion.isoOfRangeEq (𝒮.fBarPrime s) (𝒮.bBarPrimeCompl s).ι
    (hrange.trans (Scheme.Opens.range_ι _).symm),
    IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _⟩

/-- p. 298: "We remark that, if `B̄'_s` denotes the subscheme `B̂_s ∩ X̄'_s` of `X̄'_s`, then
`f̄'_s : X̄'_{s+1} → X̄'_s` is the monoidal transformation with a non-singular center `B̄'_s` in
`X̄'_s` for the case [g], and it is an isomorphism of `X̄'_{s+1}` to `X̄'_s − B̄'_s` for the case
[h]."  "Is the monoidal transformation with center `B̄'_s`" is the universal property (i), (ii)
of p. 166 (`IsMonoidalTransformationOf`); "is an isomorphism of `X̄'_{s+1}` to
`X̄'_s − B̄'_s`" is an isomorphism `e` onto the open subscheme `bBarPrimeCompl` of `X̄'_s` with
`e ≫ ι = f̄'_s`.

\textbf{Deviation from the paper (gap filled).} The paper states the remark without proof.  In
Lean: `f̄_s` is the map induced on strict transforms by `f̂_s`, hence (p. 167, (a), (b); the
cited facts of Ch. 0) the monoidal transformation of `X̄_s` with center `B̂_s ∩ X̄_s`
(`isMonoidalTransformationOf_fBar`).  In the case [g], `X̄'_{s+1} = f̄_s⁻¹(X̄'_s)`
(`xBarPrime_succ_of_caseG`), so `f̄'_s` is `f̄_s` restricted over the open subscheme `X̄'_s`
(`IsMonoidalTransformationOf.morphismRestrict`), the monoidal transformation with the restricted
center; `B̂_s ⊆ X̄_s` (the first condition of [g]) makes `B̂_s ∩ X̄_s` isomorphic to the
non-singular `B̂_s`, so `B̄'_s`, an open part of it, is non-singular.  In the case [h],
`X̄'_{s+1} = f̄_s⁻¹(X̄'_s − B̂_s)` (`xBarPrime_succ_of_not_caseG`) and the open subscheme
`X̄'_s − B̂_s` of `X̄_s` misses the center, over which a monoidal transformation is an
isomorphism (`IsMonoidalTransformationOf.isIso_morphismRestrict_of_forall_notMem`); hence `f̄'_s`
is an open immersion with image `X̄'_s − B̄'_s` (`exists_iso_fBarPrime`). -/
@[blueprint "lem:IV.3-construction-facts-fbar-prime"
  (statement := /-- In the construction of \cref{def:IV.3-frame} and
    \cref{def:IV.3-construction}, let $\bar B_s'=\hat B_s\cap\bar X_s'$, the subscheme of
    $\bar X_s'$, and $\bar f_s'\colon\bar X_{s+1}'\to\bar X_s'$ the morphism induced by $\bar f_s$
    (hence by $\hat f_s$). Then $\bar f_s'$ is the monoidal transformation of $\bar X_s'$ with a
    non-singular center $\bar B_s'$ for the case [g], and it is an isomorphism of
    $\bar X_{s+1}'$ onto $\bar X_s'-\bar B_s'$ for the case [h]. (p.~298.) (Formalization notes
    (encoding): ``is the monoidal transformation with center $\bar B_s'$'' is the universal
    property (i), (ii) of \cref{def:monoidal-transformation} for the morphism $\bar f_s'$;
    ``isomorphism onto $\bar X_s'-\bar B_s'$'' is an isomorphism onto the open subscheme
    $\bar X_s'-\bar B_s'$ of $\bar X_s'$ compatible with the inclusion.) -/)
  (proof := /-- $\bar f_s$ is the morphism induced by $\hat f_s$ on the strict transform
    $\bar X_{s+1}$ of $\bar X_s$, so it is the monoidal transformation of $\bar X_s$ with center
    $\hat B_s\cap\bar X_s$ ((a), (b) of p.~167, \cref{lem:strict-transform-is-blowup}). In the
    case [g], $\bar X_{s+1}'=\bar f_s^{-1}(\bar X_s')$, so $\bar f_s'$ is $\bar f_s$ restricted
    over the open subscheme $\bar X_s'$ of $\bar X_s$, which is the monoidal transformation of
    $\bar X_s'$ with the restricted center $\bar B_s'$. As $\hat B_s\subseteq\bar X_s$ in [g],
    $\hat B_s\cap\bar X_s\cong\hat B_s$ is non-singular, hence so is its open part $\bar B_s'$.
    In the case [h], $\bar X_{s+1}'=\bar f_s^{-1}(\bar X_s'-\hat B_s)$; the open subscheme
    $\bar X_s'-\hat B_s$ of $\bar X_s$ misses the center, so over it the monoidal transformation
    $\bar f_s$ is an isomorphism (\cref{lem:monoidal-transformation-empty-center}); hence
    $\bar f_s'$ is an open immersion with image $\bar X_s'-\bar B_s'$.

    \textbf{Deviation from the paper (gap filled).} The paper states the remark without proof;
    the argument above is supplied. -/)
  (proofUses := ["lem:strict-transform-is-blowup", "lem:monoidal-transformation-empty-center",
    "def:IV.3-construction"])
  (latexEnv := "lemma")]
theorem isMonoidalTransformationOf_and_exists_iso_fBarPrime [Hironaka.HironakaCitedResults.{u}] (s : ℕ) :
    (𝒮.CaseG s → IsMonoidalTransformationOf (𝒮.fBarPrime s) (𝒮.bBarPrime s) ∧
      (𝒮.bBarPrime s).IsNonsingular) ∧
    (¬ 𝒮.CaseG s → ∃ e : (𝒮.xBarPrime (s + 1)).toScheme ≅ (𝒮.bBarPrimeCompl s).toScheme,
      e.hom ≫ (𝒮.bBarPrimeCompl s).ι = 𝒮.fBarPrime s) :=
  ⟨fun hc => ⟨𝒮.isMonoidalTransformationOf_fBarPrime s hc, 𝒮.isNonsingular_bBarPrime s hc.1⟩,
    fun hc => 𝒮.exists_iso_fBarPrime s hc⟩

end Frame

/-! ## The consequence of Theorem 3 of Ch. III recalled on p. 299 -/

/-- Theorem 3, §5, Ch. III at a point of a monoidal transformation (p. 299: "Now, let us recall
Theorem 3, § 5, Ch. III, which shows that, if `x` is any point of `X_s` at which `X_s` has
dimension `N`, then `ν*_x(V_1(s), …, V_β(s), W(s)/X_s) ≤ ν*_{f_{s-1}(x)}(V_1(s-1), …, V_β(s-1),
W(s-1)/X_{s-1})` and if this equality holds, then `τ*_x(…/X_s) ≥ τ*_{f_{s-1}(x)}(…/X_{s-1})`",
quoted with the paper's two misprints `W_{s-1}` for `X_{s-1}` and `≤` for `≥` corrected): for a center `B` permissible for `ℜ` and a point `y`
of `X'` with `dim_y X' = dim_{f(y)} X`, the characters of the strict transform of every member
of `(V_1, …, V_β, W)` at `y` compare as stated with those of the member at `f(y)`.

\textbf{Deviation from the paper (gap filled).} The paper recalls the ring-theoretic Theorem 3
(`nuStar_strictTransform_le`) without the translation to schemes, which is supplied here: the
local ring of `X'` at `y` is a monoidal transform of that of `X` at `f(y)` in which the stalk of
the strict transform is the strict transform of the stalk (`exists_consStep`); it is residually
separable algebraic since the local dimensions agree and the residue fields have characteristic
zero (`MonoidalTransformation.isResiduallySeparableAlgebraic_toRing_of_dimAt_eq`); the stalk of
`B` is a permissible center for the stalk of the member
(`DatumI.Raw.isPermissibleCenter_stalkIdeal_datumSystem`); off the center (`f(y) ∉ B`, not
covered by Theorem 3, whose center is a prime) the local rings are isomorphic and the characters
agree; and `τ^{(i)}` for `i > t` is `0`. -/
theorem _root_.Hironaka.DatumI.Raw.nuStarAt_strictTransform_le_and_tauAt_le [Hironaka.HironakaCitedResults.{u}] {X : Scheme.{u}}
    [IsAlgebraicScheme X] (hX : X.IsNonsingular) {ℜ : DatumI.Raw X} {B : Subscheme X}
    (hB : ℜ.IsPermissible B) (t : MonoidalTransformation X B) (y : t.X')
    (hy : t.X'.IsSimpleAt y) (hdim : t.X'.dimAt y = X.dimAt (t.f.base y))
    (j : Fin (ℜ.β + 1)) :
    (Subscheme.strictTransform t (datumSystem ℜ j)).nuStarAt y hy ≤
        (datumSystem ℜ j).nuStarAt (t.f.base y) (hX _) ∧
      ((Subscheme.strictTransform t (datumSystem ℜ j)).nuStarAt y hy =
          (datumSystem ℜ j).nuStarAt (t.f.base y) (hX _) →
        ∀ i : ℕ, 1 ≤ i → (datumSystem ℜ j).tauAt (t.f.base y) (hX _) i ≤
          (Subscheme.strictTransform t (datumSystem ℜ j)).tauAt y hy i) := by
  classical
  set y₀ := t.f.base y with hy₀
  have : IsRegularLocalRing (X.presheaf.stalk y₀) := hX y₀
  have : IsDomain (X.presheaf.stalk y₀) := Transforms.isDomain_of_isRegularLocalRing _
  set V := datumSystem ℜ j with hV
  obtain ⟨T, e, hst, hsep⟩ := exists_consStep hX hB.1 t y V hdim fun _ => hB.2.1.2.2.2.2 j
  have : IsRegularLocalRing (t.X'.presheaf.stalk y) := hy
  have : IsRegularLocalRing T.ring := IsRegularLocalRing.of_ringEquiv e.symm
  have hperm := DatumI.Raw.isPermissibleCenter_stalkIdeal_datumSystem hB y₀ j
  -- the stalk of `V'` at `y` is the strict transform of `V_{y₀}` in `T ≅ O_{X',y}`
  obtain ⟨hν, -, hτ⟩ := nuStar_t_tau_map_ringEquiv e (strictTransformIdeal T (V.stalkIdeal y₀))
  have hνy : (Subscheme.strictTransform t V).nuStarAt y hy =
      nuStar T.ring (strictTransformIdeal T (V.stalkIdeal y₀)) := by
    show nuStar _ ((Subscheme.strictTransform t V).stalkIdeal y) = _
    rw [hst]
    exact hν
  have hτy : ∀ i, (Subscheme.strictTransform t V).tauAt y hy i =
      tau T.ring (strictTransformIdeal T (V.stalkIdeal y₀)) i := fun i => by
    show tau _ ((Subscheme.strictTransform t V).stalkIdeal y) i = _
    rw [hst]
    exact hτ i
  have hνx : V.nuStarAt y₀ (hX _) = nuStar _ (V.stalkIdeal y₀) := rfl
  have hτx : ∀ i, V.tauAt y₀ (hX _) i = tau _ (V.stalkIdeal y₀) i := fun i => rfl
  rw [hνy, hνx]
  simp_rw [hτy, hτx]
  by_cases hyB : y₀ ∈ B.pts
  · -- the center is a prime: Theorem 3, §5, Ch. III
    obtain hP | ⟨hP, hJP, -, -⟩ := id hperm
    · exact absurd hP (Subscheme.mem_pts_iff_stalkIdeal_ne_top.mp hyB)
    have := hP
    obtain ⟨h1, h2⟩ := nuStar_strictTransform_le _ _ _ hJP T hsep hperm
    refine ⟨h1, fun heq i hi => ?_⟩
    by_cases hit : i ≤ Hironaka.t _ (V.stalkIdeal y₀)
    · exact (h2 heq).2 i hi hit
    · rw [tau_eq_zero_of_t_lt _ (by omega)]
      exact Nat.zero_le _
  · -- the center is the unit ideal: `O_{X,y₀} → O_{X',y}` is an isomorphism
    have htop := Subscheme.stalkIdeal_eq_top_of_notMem_pts hyB
    let E := RingEquiv.ofBijective T.toRing (T.bijective_toRing_of_eq_top htop)
    obtain ⟨h1, -, h3⟩ := nuStar_t_tau_map_ringEquiv E (V.stalkIdeal y₀)
    have hmap : strictTransformIdeal T (V.stalkIdeal y₀) = (V.stalkIdeal y₀).map E := by
      rw [strictTransformIdeal_eq_map_toRing_of_eq_top htop T, ← Ideal.map_coe E]
      rfl
    rw [hmap, h1]
    exact ⟨le_rfl, fun _ i _ => (h3 i).ge⟩

/-- The schemes `X_s` of the standing succession are algebraic. -/
theorem Standing.isAlgebraicScheme_X [Hironaka.HironakaCitedResults.{u}] {N n : ℕ} {X : Scheme.{u}} {ℜ : DatumI.Raw X}
    {P : DatumI.Presentation ℜ} {r : Restriction X} {T : Tower X} {x₀ : X}
    (hS : Standing N n ℜ P r T x₀) (s : ℕ) :
    IsAlgebraicScheme (T.X s) := by
  induction s with
  | zero => exact hS.ambient.1
  | succ s ih =>
    have := ih
    exact (T.monoidalTransformation s).isAlgebraicScheme

/-- The schemes `X_s` of the standing succession have dimension at most `N` at every point. -/
theorem Standing.dimAt_X_le {N n : ℕ} {X : Scheme.{u}} {ℜ : DatumI.Raw X}
    {P : DatumI.Presentation ℜ} {r : Restriction X} {T : Tower X} {x₀ : X}
    (hS : Standing N n ℜ P r T x₀) (s : ℕ) (x : T.X s) :
    (T.X s).dimAt x ≤ N := by
  induction s with
  | zero => exact (LocSucc.dimAt_le_dim x).trans hS.ambient.2.2.2.le
  | succ s ih => exact (MonoidalTransformation.dimAt_le (hS.isNonsingular_X s)
      (hS.isNonsingular_B s) (T.monoidalTransformation s) x).trans (ih _)

/-- The members `V_j(s)`, `W(s)` of the system of `ℜ(s)` are those of the transformed datum. -/
theorem exists_datumSystem_transformI_eq_sys {X : Scheme.{u}} (ℜ : DatumI.Raw X) (T : Tower X)
    (s : ℕ) (j : Fin (ℜ.β + 1)) : ∃ j', datumSystem ((T.pre s).transformI ℜ) j' = T.sys ℜ s j := by
  obtain ⟨hW, hV⟩ := succSystem_eq_transformI (T.pre s) ℜ
  refine Fin.lastCases ?_ (fun i => ?_) j
  · exact ⟨Fin.last _, by simp only [datumSystem, Fin.snoc_last]; exact hW.symm⟩
  · exact ⟨(Fin.cast (Hironaka.MonoidalSuccession.β_transformI (T.pre s) ℜ).symm i).castSucc,
      by simp only [datumSystem, Fin.snoc_castSucc]; exact (hV i).symm⟩

/-- One step of the standing succession: Theorem 3, §5, Ch. III at a point `x` of `X_{s+1}` of
dimension `N`, for the members of the system (`DatumI.Raw.nuStarAt_strictTransform_le_and_tauAt_le`;
`X_s` again has dimension `N` at `f_s(x)`). -/
theorem Standing.nuStarAt_sys_succ_le_and_tauAt_le [Hironaka.HironakaCitedResults.{u}] {N n : ℕ} {X : Scheme.{u}} {ℜ : DatumI.Raw X}
    {P : DatumI.Presentation ℜ} {r : Restriction X} {T : Tower X} {x₀ : X}
    (hS : Standing N n ℜ P r T x₀) (s : ℕ)
    (x : T.X (s + 1)) (hx : (T.X (s + 1)).IsSimpleAt x)
    (hxdim : (T.X (s + 1)).dimAt x = N) (j : Fin (ℜ.β + 1)) :
    (T.sys ℜ (s + 1) j).nuStarAt x hx ≤
        (T.sys ℜ s j).nuStarAt ((T.f s).base x) (hS.isNonsingular_X s _) ∧
      ((T.sys ℜ (s + 1) j).nuStarAt x hx =
          (T.sys ℜ s j).nuStarAt ((T.f s).base x) (hS.isNonsingular_X s _) →
        ∀ i : ℕ, 1 ≤ i → (T.sys ℜ s j).tauAt ((T.f s).base x) (hS.isNonsingular_X s _) i ≤
          (T.sys ℜ (s + 1) j).tauAt x hx i) := by
  have := hS.isAlgebraicScheme_X s
  have hydim : (T.X s).dimAt ((T.f s).base x) = N := le_antisymm (hS.dimAt_X_le s _)
    (hxdim ▸ MonoidalTransformation.dimAt_le (hS.isNonsingular_X s) (hS.isNonsingular_B s)
      (T.monoidalTransformation s) x)
  have hBperm := isPermissible_transformI_of_isPermissibleI_snoc (T.pre s) (T.B s)
    (T.monoidalTransformation s) ℜ (hS.permissible (s + 1)).isPermissibleI
  obtain ⟨j', hj'⟩ := exists_datumSystem_transformI_eq_sys ℜ T s j
  have hsys : T.sys ℜ (s + 1) j =
      Subscheme.strictTransform (T.monoidalTransformation s) (T.sys ℜ s j) :=
    Hironaka.MonoidalSuccession.strictTransform_snoc _ _ _ _
  have h := DatumI.Raw.nuStarAt_strictTransform_le_and_tauAt_le (hS.isNonsingular_X s) hBperm
    (T.monoidalTransformation s) x hx (hxdim.trans hydim.symm) j'
  rw [hj'] at h
  rw [hsys]
  exact h

/-- p. 299: "It follows that, if `x` is any point of `X_s` such that `X_s` has dimension `N` at
`x` and `g_s(x) = x_0`, then `ν*_x(V_1(s), …, V_β(s), W(s)/X_s) ≤ ν*_{x_0}(V_1, …, V_β, W/X)`
and if this equality holds, then `τ*_x(V_1(s), …, W(s)/X_s) ≥ τ*_{x_0}(V_1, …, W/X)`."

Paper misprint: the one-step inequality recalled just before (p. 299) is printed with
`W(s-1)/W_{s-1}` for `W(s-1)/X_{s-1}` and with `≤` for `≥` in the `τ*` comparison.

\textbf{Deviation from the paper (gap filled).} "It follows that" (p. 299) is an induction on `s`
which the paper leaves implicit: at `x ∈ X_s` over `y = f_{s-1}(x) ∈ X_{s-1}`, the one-step
comparison (`DatumI.Raw.nuStarAt_strictTransform_le_and_tauAt_le`, itself a gap fill) applies
because `X_{s-1}` again has dimension `N` at `y` (`N = dim_x X_s ≤ dim_y X_{s-1} ≤ N`, the `X_t`
having dimension at most `N`), the center `B_{s-1}` is permissible for `ℜ(s-1)` whose members are
the `V_j(s-1)`, `W(s-1)`, and equality of the `ν*` at `x` with those at `x_0` forces equality at
`y`. -/
@[blueprint "lem:IV.3-thm3-consequence"
  (statement := /-- Under the standing assumptions (\cref{def:IV.3-standing}): if $x$ is any
    point of $X_s$ such that $X_s$ has dimension $N$ at $x$ and $g_s(x)=x_0$, then
    $\nu^*_x(V_1(s),\dots,V_\beta(s),W(s)/X_s)\le\nu^*_{x_0}(V_1,\dots,V_\beta,W/X)$, and if
    this equality holds, then $\tau^*_x(V_1(s),\dots,V_\beta(s),W(s)/X_s)\ge
    \tau^*_{x_0}(V_1,\dots,V_\beta,W/X)$ (\cref{def:IV.3-characters},
    \cref{def:IV.3-inequalities}). (p.~299.) (Formalization note (encoding): the comparisons
    are made member by member, $\nu^*$ in the lexicographic order of \cref{def:III.2} and
    $\tau^*$ entry by entry.)

    \textbf{Paper misprint.} In the one-step inequality recalled just before on p.~299 the paper
    prints ``$\nu^*_x(\dots/X_s)\le\nu^*_{f_{s-1}(x)}(V_1(s-1),\dots,W(s-1)/W_{s-1})$'' and
    ``$\tau^*_x(\dots/X_s)\le\tau^*_{f_{s-1}(x)}(\dots/X_{s-1})$''; meant are $W(s-1)/X_{s-1}$
    and $\ge$, as Theorem~3, \S5, Ch.~III, and the consequence stated here show. -/)
  (proof := /-- ``Now, let us recall Theorem~3, \S5, Ch.~III (\cref{thm:III.3}), which shows
    that, if $x$ is any point of $X_s$ at which $X_s$ has dimension $N$, then
    $\nu^*_x(V_1(s),\dots,V_\beta(s),W(s)/X_s)\le\nu^*_{f_{s-1}(x)}(V_1(s-1),\dots,
    V_\beta(s-1),W(s-1)/X_{s-1})$, and if this equality holds, then
    $\tau^*_x(V_1(s),\dots,W(s)/X_s)\ge\tau^*_{f_{s-1}(x)}(V_1(s-1),\dots,W(s-1)/X_{s-1})$''
    (p.~299, quoted with the two misprints noted in the statement corrected): the local ring of $X_s$ at $x$ is a monoidal transform, with a permissible center,
    of the local ring of $X_{s-1}$ at $f_{s-1}(x)$, residually algebraic (hence, in
    characteristic zero, residually separable algebraic) because $X_s$ has dimension $N$ at
    $x$, and the ideals of $V_j(s)$, $W(s)$ are the strict transforms. Induction on $s$, using
    that $X_{s-1}$ again has dimension $N$ at $f_{s-1}(x)$, gives the assertion.

    \textbf{Deviation from the paper (gap filled).} The paper only recalls Theorem~3 and states
    the consequence (``It follows that''). Lean supplies the translation from schemes to local
    rings (the local ring of $X_s$ at $x$ is a monoidal transform of that of $X_{s-1}$ at
    $f_{s-1}(x)$ with the stalks of $V_j(s)$, $W(s)$ the strict transforms; residual separability
    from $\dim_xX_s=\dim_{f_{s-1}(x)}X_{s-1}$ and characteristic zero; the stalk of $B_{s-1}$ a
    permissible center), the case $f_{s-1}(x)\notin B_{s-1}$ (not covered by Theorem~3, whose
    center is a prime; there the local rings are isomorphic), and the induction on $s$
    ($N=\dim_xX_s\le\dim_{f_{s-1}(x)}X_{s-1}\le N$; equality of the $\nu^*$ with those at $x_0$
    forces equality at the intermediate points). -/)
  (proofUses := ["thm:III.3"])
  (latexEnv := "lemma")]
theorem Standing.nuStarSystemAt_le_and_tauStarSystemAt_ge_of_nuStarSystemEq [Hironaka.HironakaCitedResults.{u}] {N n : ℕ} {X : Scheme.{u}} {ℜ : DatumI.Raw X}
    {P : DatumI.Presentation ℜ} {r : Restriction X} {T : Tower X} {x₀ : X}
    (hS : Standing N n ℜ P r T x₀) (s : ℕ) (x : T.X s)
    (hdim : (T.X s).dimAt x = (N : WithBot ℕ∞)) (hg : (T.pre s).composite.base x = x₀)
    (hx : (T.X s).IsSimpleAt x) :
    (∀ j, nuStarSystemAt (T.sys ℜ s) x hx j ≤
      nuStarSystemAt (datumSystem ℜ) x₀ (hS.ambient.2.1 x₀) j) ∧
    (NuStarSystemEq (datumSystem ℜ) x₀ (hS.ambient.2.1 x₀) (T.sys ℜ s) x hx →
      ∀ j i, tauStarSystemAt (datumSystem ℜ) x₀ (hS.ambient.2.1 x₀) j i ≤
        tauStarSystemAt (T.sys ℜ s) x hx j i) := by
  classical
  have hX := hS.isNonsingular_X
  -- induction on `s`, comparing with the point `x₁ = g_s(x)` of `X`
  have key : ∀ s (x : T.X s) (x₁ : X), (T.pre s).composite.base x = x₁ →
      (T.X s).dimAt x = N → ∀ hx : (T.X s).IsSimpleAt x,
      (∀ j, nuStarSystemAt (T.sys ℜ s) x hx j ≤
        nuStarSystemAt (datumSystem ℜ) x₁ (hS.ambient.2.1 x₁) j) ∧
      (NuStarSystemEq (datumSystem ℜ) x₁ (hS.ambient.2.1 x₁) (T.sys ℜ s) x hx →
        ∀ j i, tauStarSystemAt (datumSystem ℜ) x₁ (hS.ambient.2.1 x₁) j i ≤
          tauStarSystemAt (T.sys ℜ s) x hx j i) := by
    intro s
    induction s with
    | zero =>
      intro x x₁ h1 _ hx
      subst h1
      exact ⟨fun j => le_rfl, fun _ j i => le_rfl⟩
    | succ s ih =>
      intro x x₁ h1 hxdim hx
      set y := (T.f s).base x with hy
      have h1' : (T.pre s).composite.base y = x₁ := by
        rw [← h1, Tower.composite_pre_succ]
        rfl
      have hydim : (T.X s).dimAt y = N := le_antisymm (hS.dimAt_X_le s y)
        (hxdim ▸ MonoidalTransformation.dimAt_le (hX s) (hS.isNonsingular_B s)
          (T.monoidalTransformation s) x)
      have hyx : (T.X s).IsSimpleAt y := hX s y
      obtain ⟨ihν, ihτ⟩ := ih y x₁ h1' hydim hyx
      -- one step: Theorem 3, §5, Ch. III at `x` over `y = f_s(x)`
      have hstep := hS.nuStarAt_sys_succ_le_and_tauAt_le s x hx hxdim
      have hν : ∀ j, nuStarSystemAt (T.sys ℜ (s + 1)) x hx j ≤
          nuStarSystemAt (datumSystem ℜ) x₁ (hS.ambient.2.1 x₁) j := fun j =>
        (hstep j).1.trans (ihν j)
      refine ⟨hν, fun heq j i => ?_⟩
      have heqs : NuStarSystemEq (datumSystem ℜ) x₁ (hS.ambient.2.1 x₁) (T.sys ℜ s) y hyx :=
        fun j => le_antisymm (ihν j) ((heq j).symm.le.trans (hstep j).1)
      have hab : (T.sys ℜ (s + 1) j).nuStarAt x hx = (T.sys ℜ s j).nuStarAt y hyx :=
        (heq j).trans (heqs j).symm
      exact (ihτ heqs j i).trans ((hstep j).2 hab (i : ℕ) i.pos)
  exact key s x x₀ hg hdim hx

end AB

end

end Hironaka
