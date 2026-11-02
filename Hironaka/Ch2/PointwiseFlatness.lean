/-
Copyright (c) 2026 Daattavya Aggarwal, Minhyong Kim, Oisin Kim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daattavya Aggarwal, Minhyong Kim, Oisin Kim
-/
module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Basic
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Architect
public import Hironaka.Ch0.NormalFlatness
public import Hironaka.Ch1.ResolutionData
public import Hironaka.Ch2.Flatness
public import Hironaka.Ch2.GradedIdeal
public import Hironaka.Compat.BlowupBaseChange
public import Hironaka.Compat.SubschemeStalk

/-!
# Ch. II §1: Corollary 1 of Proposition 1, pointwise and for subschemes `V ⊇ W ⊇ D`

The global Corollary 1 of Proposition 1 (`Subscheme.isNormallyFlatAlong_of_isContainedIn` in
`Hironaka/Ch2/Flatness.lean`) is stated for the ambient scheme `V` and its non-singular subschemes
`W ⊇ W₁`.  The resolution data of Ch. I use the form
`Subscheme.IsNormallyFlatAlongAt' V W x` ("the subscheme `V` of `X` is normally flat along
`W ⊆ V` at `x`", Ch. 0, `Hironaka/Ch0/NormalFlatness.lean`) at a single point `x`.  This file
proves Corollary 1 of Proposition 1 in that form: it is used on p. 289 ("the resolution datum
`ℜ̄ = (⋃ E_j; V_1, …, V_β, W; F)` is resolved at every point of `F ∩ U`.  (See Corollary 1 of
Proposition 1, §1, Ch. II.)").
-/

@[expose] public section

open AlgebraicGeometry

universe u

namespace Hironaka

namespace Subscheme

variable {X : Scheme.{u}}

/-- Containment of subschemes gives the reverse inclusion of the stalks of the ideal sheaves. -/
theorem stalkIdeal_le_stalkIdeal_of_isContainedIn {W W₁ : Subscheme X}
    (h : W₁.IsContainedIn W) (x : X) :
    W.stalkIdeal x ≤ W₁.stalkIdeal x :=
  Ideal.span_mono fun _ ⟨U, hxU, s, hs, hsa⟩ => ⟨U, hxU, s, h U hs, hsa⟩

/-- Containment of subschemes is transitive. -/
theorem IsContainedIn.trans {D W V : Subscheme X} (hDW : D.IsContainedIn W)
    (hWV : W.IsContainedIn V) : D.IsContainedIn V := fun U => (hWV U).trans (hDW U)

/-- At a simple point `x` of a subscheme `D`, `O_{X,x}/D_x` is regular, hence `D_x` is prime. -/
theorem isPrime_stalkIdeal_of_isSimpleAt {D : Subscheme X} {x : X} (hD : D.IsSimpleAt x) :
    (D.stalkIdeal x).IsPrime := by
  have := hD.2
  have := isDomain_of_isRegularLocalRing (X.presheaf.stalk x ⧸ D.stalkIdeal x)
  exact (Ideal.Quotient.isDomain_iff_prime _).mp this

variable [IsAlgebraicScheme X]

/-- Corollary 1 of Proposition 1, p. 185 (pointwise form for subschemes): "Let `V` be an algebraic
scheme and `W` a non-singular subscheme of `V`.  Suppose `V` be normally flat along `W`.  Then,
for every non-singular subscheme `W₁` of `W`, `V` is normally flat along `W₁`."  Here `V ⊆ X` is
a subscheme, `D ⊆ W ⊆ V` are subschemes of `X`, `x` is a point which is simple on `W` and on
`D`, and "normally flat" is `Subscheme.IsNormallyFlatAlongAt'`: if `V` is normally flat along `W`
at `x`, then `V` is normally flat along `D` at `x`.

Deviation from the paper (statement modified): the paper states the corollary globally; this is
the same statement at a single point `x` (non-singular at `x` meaning that `O_{W,x}` and `O_{D,x}`
are regular), the form used in the proof of the Preparation Lemma (Ch. IV, p. 289) and in
`Raw.ResolvedAt`.  Deviation from the paper (alternative proof): none; the proof is the paper's,
applied to `O = O_{V,x}`, `P = W_x/V_x` and `𝔪 = D_x/V_x` through
`isNormallyFlatAlongAt'_iff`. -/
@[blueprint "cor:II.1-prop1-1-pointwise"
  (statement := /-- Let $X$ be an algebraic scheme, $D\subseteq W\subseteq V$ subschemes of $X$
    and $x\in D$ a point which is simple on $W$ and on $D$. If $V$ is normally flat along $W$ at
    $x$ (\cref{def:0.1-normally-flat-at}, for the subscheme $V$ and the subscheme $W$ of $V$),
    then $V$ is normally flat along $D$ at $x$. (Corollary 1 of Proposition 1, p.~185, at a
    point.) -/)
  (proof := /-- Let $O=\mathcal O_{V,x}$, $P$ the ideal of $W$ in $O$ and $\mathfrak m$ that of
    $D$. Then $O/P\cong\mathcal O_{W,x}$ and $O/\mathfrak m\cong\mathcal O_{D,x}$ are regular,
    so $P\subseteq\mathfrak m$ are prime, and $\operatorname{gr}_P(O)$ is flat over $O/P$ by
    assumption. By \cref{prop:II.1-1}, $\operatorname{gr}_{\mathfrak m}(O)$ is flat over
    $O/\mathfrak m$. -/)
  (latexEnv := "corollary")]
theorem isNormallyFlatAlongAt'_of_isContainedIn {V W D : Subscheme X} (hWV : W.IsContainedIn V)
    (hDW : D.IsContainedIn W) {x : X} (hW : W.IsSimpleAt x) (hD : D.IsSimpleAt x)
    (h : IsNormallyFlatAlongAt' V W x) : IsNormallyFlatAlongAt' V D x := by
  have hDV : D.IsContainedIn V := hDW.trans hWV
  rw [isNormallyFlatAlongAt'_iff V W hWV] at h
  rw [isNormallyFlatAlongAt'_iff V D hDV]
  refine ⟨hD.1, ?_⟩
  have hxV : x ∈ V.pts := pts_subset_of_isContainedIn hDV hD.1
  have hVW : V.stalkIdeal x ≤ W.stalkIdeal x := stalkIdeal_le_stalkIdeal_of_isContainedIn hWV x
  have hVD : V.stalkIdeal x ≤ D.stalkIdeal x := stalkIdeal_le_stalkIdeal_of_isContainedIn hDV x
  have hWD : W.stalkIdeal x ≤ D.stalkIdeal x := stalkIdeal_le_stalkIdeal_of_isContainedIn hDW x
  have := IsAlgebraicScheme.isNoetherian X
  have hVne : V.stalkIdeal x ≠ ⊤ :=
    ne_top_of_le_ne_top Ideal.IsPrime.ne_top' (stalkIdeal_le_maximalIdeal_of_mem_pts V hxV)
  have : Nontrivial (X.presheaf.stalk x ⧸ V.stalkIdeal x) := Ideal.Quotient.nontrivial_iff.mpr hVne
  have : IsLocalRing (X.presheaf.stalk x ⧸ V.stalkIdeal x) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective
  have := hW.2
  have := hD.2
  have := isPrime_stalkIdeal_of_isSimpleAt hW
  have := isPrime_stalkIdeal_of_isSimpleAt hD
  have hP : ((W.stalkIdeal x).map (Ideal.Quotient.mk (V.stalkIdeal x))).IsPrime :=
    Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective
      (by rw [Ideal.mk_ker]; exact hVW)
  have hm : ((D.stalkIdeal x).map (Ideal.Quotient.mk (V.stalkIdeal x))).IsPrime :=
    Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective
      (by rw [Ideal.mk_ker]; exact hVD)
  have : IsRegularLocalRing ((X.presheaf.stalk x ⧸ V.stalkIdeal x) ⧸
      (W.stalkIdeal x).map (Ideal.Quotient.mk (V.stalkIdeal x))) :=
    IsRegularLocalRing.of_ringEquiv (DoubleQuot.quotQuotEquivQuotOfLE hVW).symm
  have : IsRegularLocalRing ((X.presheaf.stalk x ⧸ V.stalkIdeal x) ⧸
      (D.stalkIdeal x).map (Ideal.Quotient.mk (V.stalkIdeal x))) :=
    IsRegularLocalRing.of_ringEquiv (DoubleQuot.quotQuotEquivQuotOfLE hVD).symm
  exact (isNormallyFlatAlongIdeal_of_le _ _ (Ideal.map_mono hWD) h.2).2

/-- If `V` is simple at `x`, then `V` is normally flat at `x` along every subscheme `D ⊆ V`
simple at `x`: `O_{V,x}` is regular, `D_x` is a prime with regular quotient, so `gr_{D_x}(O_{V,x})`
is a polynomial ring over `O_{D,x}`.  This is the case `P = 0` of
`isNormallyFlatAlongAt'_of_isContainedIn` (a regular local ring is normally flat along the zero
ideal, and the zero ideal of `O_{V,x}` is prime). -/
theorem isNormallyFlatAlongAt'_of_isSimpleAt {V D : Subscheme X} (hDV : D.IsContainedIn V)
    {x : X} (hV : V.IsSimpleAt x) (hD : D.IsSimpleAt x) : IsNormallyFlatAlongAt' V D x := by
  rw [isNormallyFlatAlongAt'_iff V D hDV]
  refine ⟨hD.1, ?_⟩
  have hVD : V.stalkIdeal x ≤ D.stalkIdeal x := stalkIdeal_le_stalkIdeal_of_isContainedIn hDV x
  have := IsAlgebraicScheme.isNoetherian X
  have hxV : x ∈ V.pts := hV.1
  have hVne : V.stalkIdeal x ≠ ⊤ :=
    ne_top_of_le_ne_top Ideal.IsPrime.ne_top' (stalkIdeal_le_maximalIdeal_of_mem_pts V hxV)
  have : Nontrivial (X.presheaf.stalk x ⧸ V.stalkIdeal x) := Ideal.Quotient.nontrivial_iff.mpr hVne
  have : IsLocalRing (X.presheaf.stalk x ⧸ V.stalkIdeal x) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective
  have := hV.2
  have := hD.2
  have := isPrime_stalkIdeal_of_isSimpleAt hD
  have hm : ((D.stalkIdeal x).map (Ideal.Quotient.mk (V.stalkIdeal x))).IsPrime :=
    Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective
      (by rw [Ideal.mk_ker]; exact hVD)
  have : IsRegularLocalRing ((X.presheaf.stalk x ⧸ V.stalkIdeal x) ⧸
      (D.stalkIdeal x).map (Ideal.Quotient.mk (V.stalkIdeal x))) :=
    IsRegularLocalRing.of_ringEquiv (DoubleQuot.quotQuotEquivQuotOfLE hVD).symm
  exact isNormallyFlatAlongIdeal_of_isRegularLocalRing_quotient _

end Subscheme

namespace DatumI

variable {X : Scheme.{u}} [IsAlgebraicScheme X]

/-- Corollary 1 of Proposition 1 (§1, Ch. II) for the datum `ℜ̄ = ℜ.extendBy F` of p. 289: if
`W` is simple at `x`, all `V_j` are normally flat along `W` at `x`, and `F ⊆ W` is simple at `x`,
then all the subschemes `V_1, …, V_β, W` of `ℜ̄` are normally flat along `F` at `x`, which is
condition (ii) of `Raw.ResolvedAt` (with `F` as principal subscheme) for `ℜ.extendBy F`
(condition (i) is `hF`, since `(ℜ.extendBy F).W = F`).

Deviation from the paper (gap filled): the paper says only "resolved at every point of `F ∩ U`
(See Corollary 1 of Proposition 1, §1, Ch. II)"; the case of the new subscheme `V_{β+1} = W`
(`isNormallyFlatAlongAt'_of_isSimpleAt`) and the transport along the closed immersions
`V_j ↪ X` (`isNormallyFlatAlongAt'_iff`) are left implicit. -/
theorem isNormallyFlatAlongAt'_extendBy {ℜ : Raw X} (hℜ : ℜ.IsDatum) {F : Subscheme X}
    (hFW : F.IsContainedIn ℜ.W) {x : X} (hW : ℜ.W.IsSimpleAt x) (hF : F.IsSimpleAt x)
    (hV : ∀ j, Subscheme.IsNormallyFlatAlongAt' (ℜ.V j) ℜ.W x) :
    ∀ j, Subscheme.IsNormallyFlatAlongAt' ((ℜ.extendBy F).V j) (ℜ.extendBy F).W x := by
  intro j
  induction j using Fin.lastCases with
  | last =>
    simp only [Raw.extendBy, Fin.snoc_last]
    exact Subscheme.isNormallyFlatAlongAt'_of_isSimpleAt hFW hW hF
  | cast j =>
    simp only [Raw.extendBy, Fin.snoc_castSucc]
    exact Subscheme.isNormallyFlatAlongAt'_of_isContainedIn (hℜ.2.2.2.2 j) hFW hW hF (hV j)

end DatumI

end Hironaka
