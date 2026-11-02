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
public import Mathlib.Data.Int.Star
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.AdicCompletion.LocalRing
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.KrullDimension.NonZeroDivisors
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Architect
public import Hironaka.Ch0.AlgebraicScheme
public import Hironaka.Ch0.Blowup
public import Hironaka.Ch0.NormalCrossings
public import Hironaka.Ch1.ResolutionData
public import Hironaka.Ch1.FundamentalTheorems
public import Hironaka.Ch3.Basic
public import Hironaka.Ch3.Frames
public import Hironaka.Ch4.Localization
public import Hironaka.Ch4.ImplicationsAB
public import Hironaka.Ch4.TowerExtension
public import Hironaka.Compat.ResolvableData
public import Hironaka.Compat.DatumRefinement
public import Hironaka.Ch4.TheoremsAStarBStar
public import Hironaka.Ch4.MaximalContact
public import Hironaka.Ch4.CompletionFibre
public import Hironaka.Compat.FlatStrictTransform
public import Hironaka.Compat.StalkFrameStep
public import Hironaka.Ch4.CDFrame
public import Hironaka.Compat.CompletionStalk
public import Hironaka.Compat.ExceptionalTransversal
public import Hironaka.Compat.ExtendSuccessionII
public import Hironaka.Ch3.JStabilityLemma22
public import Hironaka.Statements

/-!
# Ch. IV §4 (pp. 311–316): Theorems C and D, and Lemmas (D.1) and (D.2)

The symbols `S(ℜ^N_II)`, `S_ν(ℜ^N_II)`, `S_*(ℜ^N_II)` of p. 311, Theorems C and D and Theorem D*
(pp. 311–312), Lemma (D.1) and its induction (pp. 311–313), Theorem D from Theorem D* (p. 312), Lemma (D.2)
and the reduction to `S_ν` without components of codimension one (p. 314), the closed restriction of
Theorem C, the assembly of Theorem D* from the core step, and the running setup (pp. 314–316).

This is part 1 of 3 of `Hironaka.Ch4.ImplicationsCD`, which imports all parts; its description holds the
notation and the formalization notes for the whole section.
-/

@[expose] public section

open AlgebraicGeometry IsLocalRing CategoryTheory CategoryTheory.Limits

namespace Hironaka

universe u

noncomputable section

/-! ## The symbols of p. 311 -/

/-- p. 311: "Let us recall the definition of the symbols `S(ℜ^N_II)`, `S_*(ℜ^N_II)`, and
`S_ν(ℜ^N_II)` with a non-negative integer `ν`."  These are the symbols `S`, `S_ν`, `S^*`, `ν` of
Ch. I (`DatumII.Raw.S`, `sNu`, `sStar`, `nu`), which are reused; Ch. I writes `S^*` for the set
written `S_*` here.  The equalities hold by definition. -/
@[blueprint "rem:IV.4-symbols-II"
  (statement := /-- Let us recall the definition of the symbols $S(\mathfrak R^N_{\mathrm{II}})$,
    $S_*(\mathfrak R^N_{\mathrm{II}})$, and $S_\nu(\mathfrak R^N_{\mathrm{II}})$ with a
    non-negative integer $\nu$, for $\mathfrak R^N_{\mathrm{II}}=\big(E_1,\dots,E_\alpha\,\big|\,
    J,b\,\big|\,a_1,\dots,a_\alpha\big)$ on $X$:
    $S(\mathfrak R^N_{\mathrm{II}})=\{x\in X\mid\sum_{x\in E_i}a_i+\nu(J_x)\ge b\}$,
    $S_\nu(\mathfrak R^N_{\mathrm{II}})=\{x\in S(\mathfrak R^N_{\mathrm{II}})\mid\nu(J_x)\ge
    \nu\}$, $S_*(\mathfrak R^N_{\mathrm{II}})=S_\nu(\mathfrak R^N_{\mathrm{II}})$ with
    $\nu=\nu(\mathfrak R^N_{\mathrm{II}})$, where $\nu(\mathfrak R^N_{\mathrm{II}})=
    \max_{x\in S(\mathfrak R^N_{\mathrm{II}})}\{\nu(J_x)\}$. (p.~311.) These are the symbols of
    Ch.~I (\cref{def:I.S}, \cref{def:I.S-nu}, \cref{def:I.S-star}, \cref{def:I.nu}); the set
    written $S^*$ in Ch.~I is written $S_*$ here. (Formalization note (encoding): $\nu$ ranges over
    $\mathbb N\cup\{\infty\}$, and the maximum is a supremum, $0$ on the empty set.) -/)
  (proof := /-- By the definitions of Ch.~I. -/)
  (latexEnv := "remark")]
theorem DatumII.Raw.S_eq_and_Snu_eq_and_Sstar_eq_and_nu_eq {X : Scheme.{u}} (ℜ : DatumII.Raw X) :
    ℜ.S = {x | (ℜ.b : ℕ∞) ≤ (ℜ.weight x : ℕ∞) + ℜ.nuAt x} ∧
    (∀ ν : ℕ∞, ℜ.sNu ν = {x ∈ ℜ.S | ν ≤ ℜ.nuAt x}) ∧
    ℜ.sStar = ℜ.sNu ℜ.nu ∧ ℜ.nu = ⨆ x ∈ ℜ.S, ℜ.nuAt x :=
  ⟨rfl, fun _ => rfl, rfl, rfl⟩

namespace CD

/-- p. 311: "a resolution datum `ℜ` on `X` which is either of the form `(ℜ^N_II, F)` with closed
restriction `F`, or `ℜ^N_II` without restriction".  The second member of such a datum. -/
inductive Restriction (X : Scheme.{u}) : Type u
  /-- No restriction: `ℜ = ℜ^N_II`. -/
  | unrestricted
  /-- A closed restriction `F`: `ℜ = (ℜ^N_II, F)`. -/
  | closed (F : Subscheme X)

namespace Restriction

variable {X Y : Scheme.{u}}

/-- `r` is admissible for the datum `ℜ` (Definition 5 (II.1), p. 166, in the closed case). -/
def IsFor (r : Restriction X) (ℜ : DatumII.Raw X) : Prop :=
  match r with
  | unrestricted => True
  | closed F => ℜ.IsClosedRestriction F

/-- A center `B` is permissible for `(ℜ, r)` (Definition 6, pp. 167–168). -/
def IsPermissibleCenter (r : Restriction X) (ℜ : DatumII.Raw X) (B : Subscheme X) : Prop :=
  match r with
  | unrestricted => ℜ.IsPermissible B
  | closed F => ℜ.IsPermissibleClosed F B

/-- A finite succession is permissible for `(ℜ, r)` (Definition 8, p. 169). -/
def IsPermissibleSucc (r : Restriction X) (g : MonoidalSuccession X Y) (ℜ : DatumII.Raw X) :
    Prop :=
  match r with
  | unrestricted => g.IsPermissibleII ℜ
  | closed F => g.IsPermissibleIIClosed ℜ F

/-- The transform of the restriction along a finite succession: `F' ` is the strict transform of
`F` (Definition 7, p. 168, iterated). -/
def transformSucc (r : Restriction X) (g : MonoidalSuccession X Y) : Restriction Y :=
  match r with
  | unrestricted => unrestricted
  | closed F => closed (g.strictTransform F)

end Restriction

variable {X : Scheme.{u}}

/-- p. 311: `S(ℜ) = S(ℜ^N_II) ∩ F` for `ℜ = (ℜ^N_II, F)`, and `S(ℜ^N_II)` without restriction. -/
@[blueprint "def:IV.4-symbols"
  (statement := /-- For the case in which $\mathfrak R=(\mathfrak R^N_{\mathrm{II}},F)$, we shall
    use the following symbols: $S(\mathfrak R)=S(\mathfrak R^N_{\mathrm{II}})\cap F$,
    $S_\nu(\mathfrak R)=S_\nu(\mathfrak R^N_{\mathrm{II}})\cap F$ and
    $\nu(\mathfrak R)=\max_{x\in S(\mathfrak R)}\{\nu(J_x)\}$, which denote the respective sets
    of points of $X$ (\cref{rem:IV.4-symbols-II}). (p.~311.) (Formalization notes (encoding): a datum
    $\mathfrak R$ is a pair of a datum $\mathfrak R^N_{\mathrm{II}}$ and a restriction, closed
    $F$ or none; without restriction the symbols are those of $\mathfrak R^N_{\mathrm{II}}$; the
    maximum is a supremum in $\mathbb N\cup\{\infty\}$, $0$ on the empty set, as in
    \cref{def:I.nu}.) -/)
  (latexEnv := "definition")]
def S (ℜ : DatumII.Raw X) : Restriction X → Set X
  | .unrestricted => ℜ.S
  | .closed F => ℜ.S ∩ F.pts

/-- p. 311: `S_ν(ℜ) = S_ν(ℜ^N_II) ∩ F` for `ℜ = (ℜ^N_II, F)`. -/
@[blueprint "def:IV.4-symbols"
  (statement := /-- $S_\nu(\mathfrak R)=S_\nu(\mathfrak R^N_{\mathrm{II}})\cap F$ for
    $\mathfrak R=(\mathfrak R^N_{\mathrm{II}},F)$. (p.~311.) -/)
  (latexEnv := "definition")]
def sNu (ℜ : DatumII.Raw X) (r : Restriction X) (ν : ℕ∞) : Set X :=
  match r with
  | .unrestricted => ℜ.sNu ν
  | .closed F => ℜ.sNu ν ∩ F.pts

/-- p. 311: `ν(ℜ) = max_{x∈S(ℜ)} {ν(J_x)}` (a supremum in `ℕ∞`, `0` on the empty set). -/
@[blueprint "def:IV.4-symbols"
  (statement := /-- $\nu(\mathfrak R)=\max_{x\in S(\mathfrak R)}\{\nu(J_x)\}$. (p.~311.) -/)
  (latexEnv := "definition")]
def nu (ℜ : DatumII.Raw X) (r : Restriction X) : ℕ∞ := ⨆ x ∈ S ℜ r, ℜ.nuAt x

theorem sNu_unrestricted (ℜ : DatumII.Raw X) (ν : ℕ∞) : sNu ℜ .unrestricted ν = ℜ.sNu ν := rfl

/-- `x ∈ S_ν(ℜ)` iff `x ∈ S(ℜ)` and `ν(J_x) ≥ ν`. -/
theorem mem_Snu_iff (ℜ : DatumII.Raw X) (r : Restriction X) (ν : ℕ∞) (x : X) :
    x ∈ sNu ℜ r ν ↔ x ∈ S ℜ r ∧ ν ≤ ℜ.nuAt x := by
  cases r with
  | unrestricted => exact Iff.rfl
  | closed F =>
    exact ⟨fun ⟨⟨h1, h2⟩, h3⟩ => ⟨⟨h1, h3⟩, h2⟩, fun ⟨⟨h1, h3⟩, h2⟩ => ⟨⟨h1, h2⟩, h3⟩⟩

/-- `ν(ℜ) ≤ ν(ℜ^N_II)`, since `S(ℜ) ⊆ S(ℜ^N_II)`. -/
theorem nu_le (ℜ : DatumII.Raw X) (r : Restriction X) : nu ℜ r ≤ ℜ.nu := by
  cases r with
  | unrestricted => exact le_rfl
  | closed F => exact biSup_mono fun x hx => hx.1

/-- `ν(J_x) ≤ ν(ℜ)` at every point of `S(ℜ)`. -/
theorem nuAt_le_nu (ℜ : DatumII.Raw X) (r : Restriction X) {x : X} (hx : x ∈ S ℜ r) :
    ℜ.nuAt x ≤ nu ℜ r :=
  le_iSup₂ (f := fun x _ => ℜ.nuAt x) x hx

end CD

/-! ## Theorems C and D (p. 311) -/

-- Theorem C (`exists_isPermissibleIIClosed_Snu_eq_empty_of_nu_closed_eq`) is stated after Theorem D*,
-- where its proof is assembled (closed case of the core step, `CD.exists_extension_not_mem_sNuImageClosed`).

/-- The "i.e." of Theorem D (p. 311): a datum `ℜ^N_II` is resolved at every point iff `S(ℜ)` is
empty (Definition 4 (II) and the definition of `S`, p. 165). -/
@[blueprint "rem:IV.4-resolved-iff"
  (statement := /-- A resolution datum $\mathfrak R^N_{\mathrm{II}}$ on $X$ is resolved at every
    point of $X$ (\cref{def:I.4-II}) if and only if $S(\mathfrak R^N_{\mathrm{II}})$ is empty
    (\cref{def:I.S}); this is the ``i.e.'' of Theorem D (\cref{thm:IV.D}). (p.~311.) -/)
  (proof := /-- $\mathfrak R$ is resolved at $x$ iff $\sum_{x\in E_i}a_i+\nu(J_x)<b$, iff
    $x\notin S(\mathfrak R)$. -/)
  (latexEnv := "remark")]
theorem DatumII.Raw.resolvedEverywhere_iff_S_eq_empty {X : Scheme.{u}} (ℜ : DatumII.Raw X) :
    ℜ.ResolvedEverywhere ↔ ℜ.S = ∅ := by
  constructor
  · intro h
    exact Set.eq_empty_of_forall_notMem fun x hx => absurd (h x) (not_lt.2 hx)
  · intro h x
    refine lt_of_not_ge fun hx => ?_
    have : x ∈ ℜ.S := hx
    rw [h] at this
    exact this

/-! ## Theorem D* and Lemma (D.1) (p. 312) -/

/-- p. 312: "If Theorem D* is verified, then we can immediately conclude that there exists a
permissible succession of monoidal transformations `f : X' → X` for `ℜ = ℜ^N_II`, such that
`S_1(f*(ℜ))` is empty; that is to say, if `f*(ℜ) = (E'_1, …, E'_{α'} | J', b | a'_1, …, a'_{α'})`
then `J'_{x'}` is equal to the local ring of `X'` at every point `x' ∈ S(f*(ℜ))`."

Formalization note: "Theorem D* is verified" is the hypothesis `hDstar`, the conclusion of
Theorem D* for every resolution datum on every non-singular irreducible algebraic scheme of
dimension `N` (the inductive assumptions of Theorem D* being fixed); "`J'_{x'}` is equal to the
local ring" is `J'_{x'} = ⊤`. -/
@[blueprint "lem:IV.D-star-consequence"
  (statement := /-- If Theorem D* (\cref{thm:IV.D-star}) is verified, then we can immediately
    conclude that there exists a permissible succession of monoidal transformations
    $f\colon X'\to X$ for $\mathfrak R=\mathfrak R^N_{\mathrm{II}}$, such that
    $S_1(f^*(\mathfrak R))$ is empty; that is to say, if $f^*(\mathfrak R)=\big(E_1',\dots,
    E_{\alpha'}'\,\big|\,J',b\,\big|\,a_1',\dots,a_{\alpha'}'\big)$ then $J'_{x'}$ is equal to the
    local ring of $X'$ at every point $x'\in S(f^*(\mathfrak R))$. (p.~312.) (Formalization note
    (encoding):
    ``Theorem D* is verified'' is taken to mean its conclusion for every resolution datum on
    every non-singular irreducible algebraic scheme of dimension $N$.) -/)
  (proof := /-- If $\nu(\mathfrak R)=0$, then $S_1(\mathfrak R)$ is already empty. Otherwise
    Theorem D* gives $f_1$ with $S_\nu(f_1^*(\mathfrak R))=\emptyset$, $\nu=\nu(\mathfrak R)$,
    hence $\nu(f_1^*(\mathfrak R))<\nu$; $X_1$ is again a non-singular irreducible algebraic
    scheme of dimension $N$ (the centers are non-singular and, lying in
    $S^*$, nowhere dense, \cref{lem:monoidal-transformation-nonsingular}, \cref{lem:IV.1-2}) and
    $f_1^*(\mathfrak R)$ is a resolution datum (\cref{lem:I.8-transform-is-datum}). Repeating
    this at most $\nu(\mathfrak R)$ times we reach a transform with $\nu=0$, i.e.\
    $S_1=\emptyset$; composites of permissible successions are permissible (\cref{def:I.8}).
    Finally $\nu(J'_{x'})=0$ means $J'_{x'}\not\subseteq M_{x'}$, i.e.\ $J'_{x'}$ is the local
    ring (\cref{lem:order-nu-basic}). -/)
  (proofUses := ["thm:IV.D-star", "lem:I.8-transform-is-datum", "lem:order-nu-basic"])
  (latexEnv := "lemma")]
theorem exists_isPermissibleII_Snu_one_eq_empty_of_forall_exists_Snu_eq_empty [Hironaka.HironakaCitedResults.{u}] (N : ℕ)
    (hDstar : ∀ (X : Scheme.{u}), IsAmbient X N → ∀ (ℜ : DatumII X),
      0 < (ℜ : DatumII.Raw X).nu →
      ∃ (X' : Scheme.{u}) (f : MonoidalSuccession X X'),
        f.IsPermissibleII ℜ ∧ (f.transformII ℜ).sNu (ℜ : DatumII.Raw X).nu = ∅)
    (X : Scheme.{u}) (hX : IsAmbient X N) (ℜ : DatumII X) :
    ∃ (X' : Scheme.{u}) (f : MonoidalSuccession X X'),
      f.IsPermissibleII ℜ ∧ (f.transformII ℜ).sNu 1 = ∅ ∧
      ∀ x' ∈ (f.transformII ℜ).S, (f.transformII ℜ).J.stalkIdeal x' = ⊤ := by
  classical
  have hempty : ∀ {Y : Scheme.{u}} (ℜ' : DatumII.Raw Y) (c : ℕ∞), ℜ'.nu < c → ℜ'.sNu c = ∅ :=
    fun ℜ' c h => Set.eq_empty_iff_forall_notMem.mpr fun x hx =>
      absurd (hx.2.trans (le_iSup₂ (f := fun x (_ : x ∈ ℜ'.S) => ℜ'.nuAt x) x hx.1))
        (not_le.mpr h)
  -- `J'_{x'}` is the local ring where `ν(J'_{x'}) = 0`
  have hconcl : ∀ {Y : Scheme.{u}} (ℜ' : DatumII.Raw Y), ℜ'.sNu 1 = ∅ →
      ∀ x ∈ ℜ'.S, ℜ'.J.stalkIdeal x = ⊤ := by
    intro Y ℜ' h x hx
    by_contra hne
    have hle : ℜ'.J.stalkIdeal x ≤ IsLocalRing.maximalIdeal _ := IsLocalRing.le_maximalIdeal hne
    have h1 : (1 : ℕ∞) ≤ ℜ'.nuAt x :=
      (Ideal.ord_basic (IsLocalRing.maximalIdeal _) (ℜ'.J.stalkIdeal x) ⊤ ⊤).2.1.mpr hle
    exact (Set.eq_empty_iff_forall_notMem.mp h) x ⟨hx, h1⟩
  have hnil : ∀ (Y : Scheme.{u}) (ℜ' : DatumII.Raw Y),
      (MonoidalSuccession.nil Y).transformII ℜ' = ℜ' := fun _ _ => rfl
  have key : ∀ n : ℕ, ∀ (X : Scheme.{u}), IsAmbient X N → ∀ (ℜ : DatumII X),
      (ℜ : DatumII.Raw X).nu.toNat ≤ n →
      ∃ (X' : Scheme.{u}) (f : MonoidalSuccession X X'),
        f.IsPermissibleII ℜ ∧ (f.transformII ℜ).sNu 1 = ∅ := by
    intro n
    induction n with
    | zero =>
      intro X hX ℜ hn
      have hfin : (ℜ : DatumII.Raw X).nu ≠ ⊤ := by
        have := hX.1
        exact DatumII.Raw.nu_ne_top hX.2.1 ℜ.1 ℜ.2.2.2.2
      have h0 : (ℜ : DatumII.Raw X).nu = 0 := by
        rw [← ENat.natCast_toNat hfin, Nat.le_zero.mp hn]; rfl
      exact ⟨X, MonoidalSuccession.nil X, trivial, hempty _ _ (by
        rw [hnil, h0]; exact zero_lt_one)⟩
    | succ n ih =>
      intro X hX ℜ hn
      have := hX.1
      have hfin : (ℜ : DatumII.Raw X).nu ≠ ⊤ := DatumII.Raw.nu_ne_top hX.2.1 ℜ.1 ℜ.2.2.2.2
      by_cases h0 : (ℜ : DatumII.Raw X).nu = 0
      · exact ⟨X, MonoidalSuccession.nil X, trivial, hempty _ _ (by
          rw [hnil, h0]; exact zero_lt_one)⟩
      · obtain ⟨X₁, f₁, hf₁, hS⟩ := hDstar X hX ℜ (pos_iff_ne_zero.mpr h0)
        obtain ⟨hX₁, hd₁⟩ := f₁.isAmbient_transformII hX ℜ.1 ℜ.2 hf₁
        -- `ν(f₁*ℜ) < ν(ℜ)` since `S_ν(f₁*ℜ)` is empty
        have hlt : (f₁.transformII ℜ.1).nu < ℜ.1.nu := by
          have hle := MonoidalSuccession.nu_transformII_le f₁ hX.2.1 ℜ.1 ℜ.2 hf₁
          refine lt_of_le_of_ne hle fun heq => ?_
          have hfin₁ : (f₁.transformII ℜ.1).nu ≠ ⊤ := heq ▸ hfin
          obtain ⟨m, hm⟩ : ∃ m : ℕ, ℜ.1.nu = (m : ℕ∞) + 1 := by
            obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.mp hfin
            have hk0 : k ≠ 0 := fun h => h0 (by rw [← hk, h]; rfl)
            exact ⟨k - 1, by rw [← hk]; exact_mod_cast (Nat.succ_pred_eq_of_ne_zero hk0).symm⟩
          have hbound : (f₁.transformII ℜ.1).nu ≤ m := by
            refine iSup₂_le fun x hx => ?_
            have hnot : ¬ ℜ.1.nu ≤ (f₁.transformII ℜ.1).nuAt x := fun h =>
              (Set.eq_empty_iff_forall_notMem.mp hS) x ⟨hx, h⟩
            exact ENat.lt_natCast_add_one_iff.mp (hm ▸ not_le.mp hnot)
          rw [heq, hm] at hbound
          exact lt_irrefl _ ((ENat.lt_natCast_add_one_iff.mpr le_rfl).trans_le hbound)
        have hn₁ : (f₁.transformII ℜ.1).nu.toNat ≤ n := by
          have hfin₁ : (f₁.transformII ℜ.1).nu ≠ ⊤ := ne_top_of_lt hlt
          have h := hlt
          rw [← ENat.natCast_toNat hfin₁, ← ENat.natCast_toNat hfin] at h
          have := Nat.cast_lt.mp h
          omega
        obtain ⟨X₂, f₂, hf₂, hS₂⟩ := ih X₁ hX₁ ⟨f₁.transformII ℜ.1, hd₁⟩ hn₁
        exact ⟨X₂, f₁.append f₂, (MonoidalSuccession.isPermissibleII_append f₁ f₂ ℜ.1).mpr
          ⟨hf₁, hf₂⟩, by rw [MonoidalSuccession.transformII_append]; exact hS₂⟩
  obtain ⟨X', f, hf, hS⟩ := key _ X hX ℜ le_rfl
  exact ⟨X', f, hf, hS, hconcl _ hS⟩

namespace CD

variable {X : Scheme.{u}}

open Classical in
/-- The weight `∑_{E_i ⊇ H} a_i` of a subscheme `H` (pp. 312–313). -/
def weightOn (ℜ : DatumII.Raw X) (H : Subscheme X) : ℕ :=
  ∑ i ∈ Finset.univ.filter (fun i => H.IsContainedIn (ℜ.E i)), ℜ.a i

/-- p. 312: "`K⁰_r(ℜ)` = the set of those non-singular subschemes of `X` of codimension `r` which
are irreducible components of `⋂_{i∈T_r} E_i` for a subset `T_r` of `r` indices of
`{1, …, α}`."  The intersection of subschemes is the sum of the ideal sheaves (p. 165). -/
@[blueprint "def:IV.D-1-symbols"
  (statement := /-- In the proof of Lemma (D.1) (\cref{lem:IV.D-1}), for a resolution datum
    $\mathfrak R=\big(E_1,\dots,E_\alpha\,\big|\,J,b\,\big|\,a_1,\dots,a_\alpha\big)$ on $X$ and
    an integer $r\ge1$: $K^0_r(\mathfrak R)=$ the set of those non-singular subschemes of $X$ of
    codimension $r$ which are irreducible components of $\bigcap_{i\in T_r}E_i$ for a subset $T_r$
    of $r$ indices of $\{1,\dots,\alpha\}$; $A_r(\mathfrak R)=\max_{H\in K^0_r(\mathfrak R)}
    \{\sum_{E_i\supseteq H}a_i\}$; $K_r(\mathfrak R)=$ the subset of $K^0_r(\mathfrak R)$ of those
    $H$ such that $A_r(\mathfrak R)=\sum_{E_i\supseteq H}a_i$; $k_r(\mathfrak R)=$ the number of
    subschemes of $X$ [which] belong to $K_r(\mathfrak R)$. (p.~312; the paper prints the maximum
    over ``$H\in K^0_r(\ )$'' [sic].)

    \textbf{Paper misprint.} The paper prints the maximum in $A_r(\mathfrak R)$ over
    ``$H\in K^0_r(\ )$'' (the argument $\mathfrak R$ is missing).

    (Formalization notes (encoding): the irreducible components are taken
    with their reduced structure, and the codimension is that of \cref{def:I.0-codimension}; the
    maximum is a supremum of
    natural numbers, $0$ on the empty set, and $k_r$ is the cardinality of a finite set, $0$ if
    it were infinite.) -/)
  (latexEnv := "definition")]
def K0 (ℜ : DatumII.Raw X) (r : ℕ) : Set (Subscheme X) :=
  {H | H.IsNonsingular ∧ H.codim = (r : ℕ∞) ∧
    ∃ T : Finset (Fin ℜ.α), T.card = r ∧ H ∈ (⨆ i ∈ T, ℜ.E i).irreducibleComponents}

/-- p. 312: `A_r(ℜ) = max_{H ∈ K⁰_r(ℜ)} {∑_{E_i ⊇ H} a_i}`. -/
@[blueprint "def:IV.D-1-symbols"
  (statement := /-- $A_r(\mathfrak R)=\max_{H\in K^0_r(\mathfrak R)}\{\sum_{E_i\supseteq H}a_i\}$.
    (p.~312.) -/)
  (latexEnv := "definition")]
def A (ℜ : DatumII.Raw X) (r : ℕ) : ℕ := sSup (weightOn ℜ '' K0 ℜ r)

/-- p. 312: "`K_r(ℜ)` = the subset of `K⁰_r(ℜ)` of those `H` such that
`A_r(ℜ) = ∑_{E_i ⊇ H} a_i`". -/
@[blueprint "def:IV.D-1-symbols"
  (statement := /-- $K_r(\mathfrak R)=\{H\in K^0_r(\mathfrak R)\mid A_r(\mathfrak R)=
    \sum_{E_i\supseteq H}a_i\}$. (p.~312.) -/)
  (latexEnv := "definition")]
def K (ℜ : DatumII.Raw X) (r : ℕ) : Set (Subscheme X) :=
  {H ∈ K0 ℜ r | A ℜ r = weightOn ℜ H}

/-- p. 312: "`k_r(ℜ)` = the number of subschemes of `X` belong to `K_r(ℜ)`" [sic]. -/
@[blueprint "def:IV.D-1-symbols"
  (statement := /-- $k_r(\mathfrak R)=$ the number of elements of $K_r(\mathfrak R)$.
    (p.~312.) -/)
  (latexEnv := "definition")]
def k (ℜ : DatumII.Raw X) (r : ℕ) : ℕ := (K ℜ r).ncard

end CD

section OrderHelpers
variable {S : Type u} [CommRing S]

theorem Ideal.le_pow_of_ord_eq {M J : Ideal S} {k : ℕ} (h : Ideal.ord M J = k) : J ≤ M ^ k := by
  by_contra hJ
  have : Ideal.ord M J ≤ ((k - 1 : ℕ) : ℕ∞) := Ideal.ord_le fun n hn => by
    have hlt : n < k := by
      by_contra hnk
      exact hJ (hn.trans (Ideal.pow_le_pow_right (not_lt.mp hnk)))
    exact_mod_cast Nat.le_sub_one_of_lt hlt
  rw [h] at this
  have hk : 0 < k := by
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · exact absurd (by simp) hJ
    · exact hk
  have := Nat.cast_le.mp this
  omega

theorem Ideal.not_le_pow_succ_of_ord_eq {M J : Ideal S} {k : ℕ} (h : Ideal.ord M J = k) :
    ¬ J ≤ M ^ (k + 1) := fun hle => by
  have := Ideal.le_ord hle
  rw [h] at this
  have := Nat.cast_le.mp this
  omega

theorem Ideal.nu_top [IsLocalRing S] : Ideal.nu (⊤ : Ideal S) = 0 := by
  refine le_antisymm (Ideal.ord_le fun n hn => ?_) bot_le
  rcases Nat.eq_zero_or_pos n with rfl | hn0
  · simp
  · exfalso
    have : (⊤ : Ideal S) ≤ maximalIdeal S := hn.trans (by simpa using Ideal.pow_le_pow_right hn0 (I := maximalIdeal S))
    exact (maximalIdeal.isMaximal S).ne_top (top_le_iff.mp this)
end OrderHelpers

namespace MonoidalTransformation

variable {X : Scheme.{u}} {B : Subscheme X}

/-- If the strict transform of `V` is contained in that of `W`, then `V ⊆ W`, for `V` irreducible
with non-empty strict transform. -/
theorem pts_subset_of_pts_strictTransform_subset (t : MonoidalTransformation X B)
    {V W : Subscheme X} (hV : IsIrreducible V.pts) (hne : (Subscheme.strictTransform t V).pts.Nonempty)
    (h : (Subscheme.strictTransform t V).pts ⊆ (Subscheme.strictTransform t W).pts) :
    V.pts ⊆ W.pts := by
  have hopen : IsOpen (B.ptsᶜ) := B.support.isClosed.isOpen_compl
  have hinter : (V.pts ∩ B.ptsᶜ).Nonempty := by
    rw [pts_strictTransform_eq_closure, closure_nonempty_iff] at hne
    obtain ⟨y, hyV, hyE⟩ := hne
    rw [pts_exceptional] at hyE
    exact ⟨t.f y, hyV, hyE⟩
  have h1 : V.pts ⊆ closure (V.pts ∩ B.ptsᶜ) :=
    subset_closure_inter_of_isPreirreducible_of_isOpen hV.isPreirreducible hopen hinter
  refine h1.trans (closure_minimal (fun x ⟨hxV, hxB⟩ => ?_) W.support.isClosed)
  obtain ⟨y, rfl⟩ := t.exists_apply_eq_of_notMem hxB
  have hyE : y ∉ t.exceptional.pts := by rw [pts_exceptional]; exact hxB
  have hy : y ∈ (Subscheme.strictTransform t V).pts := by
    rw [pts_strictTransform_eq_closure]
    exact subset_closure ⟨hxV, hyE⟩
  have hy' := h hy
  rw [pts_strictTransform_eq_closure] at hy'
  have : t.f.base y ∈ closure (t.f.base '' (t.f.base ⁻¹' W.pts \ t.exceptional.pts)) :=
    image_closure_subset_closure_image t.f.base.hom.continuous ⟨y, hy', rfl⟩
  refine closure_minimal ?_ W.support.isClosed this
  rintro _ ⟨z, ⟨hzW, -⟩, rfl⟩
  exact hzW

/-- Non-singular irreducible subschemes with equal non-empty strict transforms are equal. -/
theorem eq_of_strictTransform_eq (t : MonoidalTransformation X B) {V W : Subscheme X}
    (hVns : V.IsNonsingular) (hVirr : V.IsIrreducible) (hWns : W.IsNonsingular)
    (hWirr : W.IsIrreducible) (hne : (Subscheme.strictTransform t V).pts.Nonempty)
    (heq : Subscheme.strictTransform t V = Subscheme.strictTransform t W) : V = W := by
  have hne' : (Subscheme.strictTransform t W).pts.Nonempty := heq ▸ hne
  have h1 := pts_subset_of_pts_strictTransform_subset t (Subscheme.isIrreducible_pts V hVirr) hne
    (fun x hx => by rw [← heq]; exact hx)
  have h2 := pts_subset_of_pts_strictTransform_subset t (Subscheme.isIrreducible_pts W hWirr) hne'
    (fun x hx => by rw [heq]; exact hx)
  have hpts : V.support = W.support := SetLike.coe_injective (Set.Subset.antisymm h1 h2)
  rw [Subscheme.eq_ofClosed_support V (Subscheme.isReduced_of_isNonsingular hVns),
    Subscheme.eq_ofClosed_support W (Subscheme.isReduced_of_isNonsingular hWns), hpts]

end MonoidalTransformation

/-! ### Lemma (D.1): reductions and the induction (pp. 311-313) -/

namespace DatumII.Raw
variable {X : Scheme.{u}}

/-- `J_x` is the local ring at every point of `S(ℜ)` (the hypothesis of Lemma (D.1)). -/
def HasUnitJOnS (ℜ : Raw X) : Prop := ∀ x ∈ ℜ.S, ℜ.J.stalkIdeal x = ⊤

theorem nuAt_eq_zero_of_hasUnitJOnS {ℜ : Raw X} (h : ℜ.HasUnitJOnS) {x : X} (hx : x ∈ ℜ.S) :
    ℜ.nuAt x = 0 := by
  unfold nuAt
  rw [h x hx]
  exact Ideal.nu_top

theorem nu_eq_zero_of_hasUnitJOnS {ℜ : Raw X} (h : ℜ.HasUnitJOnS) : ℜ.nu = 0 :=
  le_antisymm (iSup₂_le fun _ hx => (nuAt_eq_zero_of_hasUnitJOnS h hx).le) bot_le

theorem divPow_top_zero {B : Subscheme X} (t : MonoidalTransformation X B) :
    Subscheme.divPow (Subscheme.totalTransform t.f ⊤) t.exceptional 0 = ⊤ := by
  refine Subscheme.ext_stalkIdeal fun x => ?_
  rw [Subscheme.stalkIdeal_divPow (P := t.exceptional) t.invertible, Subscheme.totalTransform_top,
    Subscheme.stalkIdeal_top_eq]
  simp

end DatumII.Raw

namespace MonoidalSuccession

variable {X Y : Scheme.{u}}

end MonoidalSuccession

namespace DatumII.Raw
variable {X : Scheme.{u}}

open Classical in
/-- The finite set of non-empty subschemes among the `E_i`. -/
noncomputable def nonemptyComponents (ℜ : Raw X) : Finset (Subscheme X) :=
  (Finset.univ.image ℜ.E).filter fun D => D.pts.Nonempty

open Classical in
/-- The datum with the non-empty `E_i` listed without repetition and the coefficients added up
(p. 275, "the essential characteristics"): `a(E) = ∑_{E_i = E} a_i`. -/
noncomputable def dedup (ℜ : Raw X) : Raw X where
  α := ℜ.nonemptyComponents.card
  E := fun j => ((ℜ.nonemptyComponents.equivFin.symm j : ℜ.nonemptyComponents) : Subscheme X)
  a := fun j => ∑ i ∈ Finset.univ.filter
    (fun i => ℜ.E i = ((ℜ.nonemptyComponents.equivFin.symm j : ℜ.nonemptyComponents) :
      Subscheme X)), ℜ.a i
  J := ℜ.J
  b := ℜ.b

theorem mem_nonemptyComponents_iff (ℜ : Raw X) {D : Subscheme X} (hD : D.pts.Nonempty) :
    D ∈ ℜ.nonemptyComponents ↔ ∃ i, ℜ.E i = D := by
  classical
  unfold nonemptyComponents
  simp [hD]

theorem sameChar_dedup (ℜ : Raw X) : SameChar ℜ ℜ.dedup := by
  classical
  refine ⟨rfl, rfl, fun D hD => ?_⟩
  have hmem := ℜ.mem_nonemptyComponents_iff hD
  set e := ℜ.nonemptyComponents.equivFin with he
  constructor
  · show (∃ i, ℜ.E i = D) ↔ ∃ j : Fin ℜ.nonemptyComponents.card,
      ((e.symm j : ℜ.nonemptyComponents) : Subscheme X) = D
    rw [← hmem]
    constructor
    · intro hD'
      exact ⟨e ⟨D, hD'⟩, by simp⟩
    · rintro ⟨j, hj⟩
      rw [← hj]
      exact (e.symm j).2
  · show (∑ i ∈ Finset.univ.filter (fun i => ℜ.E i = D), ℜ.a i) =
      ∑ j ∈ (Finset.univ : Finset (Fin ℜ.nonemptyComponents.card)).filter
        (fun j => ((e.symm j : ℜ.nonemptyComponents) : Subscheme X) = D),
        ∑ i ∈ Finset.univ.filter
          (fun i => ℜ.E i = ((e.symm j : ℜ.nonemptyComponents) : Subscheme X)), ℜ.a i
    by_cases hD' : D ∈ ℜ.nonemptyComponents
    · have hfilt : (Finset.univ : Finset (Fin ℜ.nonemptyComponents.card)).filter
          (fun j => ((e.symm j : ℜ.nonemptyComponents) : Subscheme X) = D) = {e ⟨D, hD'⟩} := by
        ext j
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
        constructor
        · intro h
          rw [← Equiv.symm_apply_eq]
          exact Subtype.ext h
        · rintro rfl
          simp
      rw [hfilt, Finset.sum_singleton]
      simp
    · have h1 : ∀ i, ℜ.E i ≠ D := fun i hi => hD' ((hmem).mpr ⟨i, hi⟩)
      have h2 : ∀ j : Fin ℜ.nonemptyComponents.card,
          ((e.symm j : ℜ.nonemptyComponents) : Subscheme X) ≠ D := fun j hj =>
        hD' (hj ▸ (e.symm j).2)
      simp [h1, h2]

theorem dedup_distinct (ℜ : Raw X) :
    ∀ i j, i ≠ j → ℜ.dedup.E i ≠ Subscheme.empty → ℜ.dedup.E i ≠ ℜ.dedup.E j := by
  intro i j hij _ h
  apply hij
  have : (ℜ.nonemptyComponents.equivFin.symm i) = (ℜ.nonemptyComponents.equivFin.symm j) :=
    Subtype.ext h
  exact ℜ.nonemptyComponents.equivFin.symm.injective this

end DatumII.Raw

namespace Subscheme
variable {X : Scheme.{u}}

/-- The stalk at `x` of the reduced structure on the closure of a generization `ζ` of `x`
determines `ζ`: if the stalks at `x` of two such coincide, so do the points. -/
theorem eq_of_stalkIdeal_ofClosed_closure_eq {ζ ζ' x : X} (hζ : ζ ⤳ x) (hζ' : ζ' ⤳ x)
    (h : (ofClosed ⟨closure {ζ}, isClosed_closure⟩).stalkIdeal x =
      (ofClosed ⟨closure {ζ'}, isClosed_closure⟩).stalkIdeal x) : ζ = ζ' := by
  obtain ⟨⟨U, hU⟩, hxU⟩ := exists_affineOpen_mem x
  replace hU : IsAffineOpen U := hU
  replace hxU : x ∈ U := hxU
  have hζU : ζ ∈ U := hζ.mem_open U.isOpen hxU
  have hζ'U : ζ' ∈ U := hζ'.mem_open U.isOpen hxU
  set q := hU.primeIdealOf ⟨ζ, hζU⟩
  set q' := hU.primeIdealOf ⟨ζ', hζ'U⟩
  have hq : hU.fromSpec q = ζ := hU.fromSpec_primeIdealOf ⟨ζ, hζU⟩
  have hq' : hU.fromSpec q' = ζ' := hU.fromSpec_primeIdealOf ⟨ζ', hζ'U⟩
  have hqx : q.asIdeal ≤ (hU.primeIdealOf ⟨x, hxU⟩).asIdeal := by
    refine (compStalk_fromSpec_specializes_iff hU q _).mp ?_
    rw [hq, hU.fromSpec_primeIdealOf]
    exact hζ
  have hqx' : q'.asIdeal ≤ (hU.primeIdealOf ⟨x, hxU⟩).asIdeal := by
    refine (compStalk_fromSpec_specializes_iff hU q' _).mp ?_
    rw [hq', hU.fromSpec_primeIdealOf]
    exact hζ'
  have h1 := compStalk_stalkIdeal_ofClosed_closure hU hxU q
  have h2 := compStalk_stalkIdeal_ofClosed_closure hU hxU q'
  rw [hq] at h1
  rw [hq'] at h2
  let _ := TopCat.Presheaf.algebra_section_stalk X.presheaf (⟨x, hxU⟩ : U)
  have := hU.isLocalization_stalk ⟨x, hxU⟩
  rw [h1, h2] at h
  change q.asIdeal.map (algebraMap Γ(X, U) (X.presheaf.stalk x)) =
    q'.asIdeal.map (algebraMap Γ(X, U) (X.presheaf.stalk x)) at h
  have h' := congrArg (Ideal.comap (algebraMap Γ(X, U) (X.presheaf.stalk x))) h
  rw [compStalk_under_map _ q.asIdeal hqx, compStalk_under_map _ q'.asIdeal hqx'] at h'
  have : q = q' := PrimeSpectrum.ext h'
  rw [← hq, ← hq', this]

/-- Two non-singular irreducible subschemes with the same stalk at a common point are equal. -/
theorem eq_of_stalkIdeal_eq_of_isIrreducible {F F' : Subscheme X} (hF : F.IsNonsingular)
    (hFirr : F.IsIrreducible) (hF' : F'.IsNonsingular) (hF'irr : F'.IsIrreducible) {x : X}
    (hx : x ∈ F.pts) (hx' : x ∈ F'.pts) (h : F.stalkIdeal x = F'.stalkIdeal x) : F = F' := by
  obtain ⟨ζ, hζ⟩ := QuasiSober.sober (isIrreducible_pts F hFirr) F.support.isClosed
  obtain ⟨ζ', hζ'⟩ := QuasiSober.sober (isIrreducible_pts F' hF'irr) F'.support.isClosed
  have e1 : F = ofClosed ⟨closure {ζ}, isClosed_closure⟩ := by
    rw [eq_ofClosed_support F (isReduced_of_isNonsingular hF)]
    congr 1
    exact TopologicalSpace.Closeds.ext hζ.def.symm
  have e2 : F' = ofClosed ⟨closure {ζ'}, isClosed_closure⟩ := by
    rw [eq_ofClosed_support F' (isReduced_of_isNonsingular hF')]
    congr 1
    exact TopologicalSpace.Closeds.ext hζ'.def.symm
  have hsp : ζ ⤳ x := hζ.specializes hx
  have hsp' : ζ' ⤳ x := hζ'.specializes hx'
  rw [e1, e2] at h ⊢
  rw [eq_of_stalkIdeal_ofClosed_closure_eq hsp hsp' h]

end Subscheme

section MinimalPoints

/-- `a` is a point of `P` without proper generization in `P` (the generic point of a component of
`P` when `P` is closed). -/
def IsMinimalPoint {A : Type*} [TopologicalSpace A] (P : Set A) (a : A) : Prop :=
  a ∈ P ∧ ∀ w ∈ P, w ⤳ a → w = a

/-- Minimal points correspond under two embeddings with the same pulled-back set, whose ranges
are closed under generization. -/
theorem isMinimalPoint_iff_of_isEmbedding {Y A B : Type*} [TopologicalSpace Y]
    [TopologicalSpace A] [TopologicalSpace B] {g₁ : Y → A} {g₂ : Y → B}
    (h₁ : Topology.IsEmbedding g₁) (h₂ : Topology.IsEmbedding g₂)
    (hr₁ : ∀ y w, w ⤳ g₁ y → w ∈ Set.range g₁) (hr₂ : ∀ y w, w ⤳ g₂ y → w ∈ Set.range g₂)
    {PA : Set A} {PB : Set B} (hP : ∀ y, g₁ y ∈ PA ↔ g₂ y ∈ PB) (y : Y) :
    IsMinimalPoint PA (g₁ y) ↔ IsMinimalPoint PB (g₂ y) := by
  constructor
  · rintro ⟨hy, hmin⟩
    refine ⟨(hP y).mp hy, fun w hw hwy => ?_⟩
    obtain ⟨y', rfl⟩ := hr₂ y w hwy
    have h1 : y' ⤳ y := h₂.isInducing.specializes_iff.mp hwy
    have h2 := hmin (g₁ y') ((hP y').mpr hw) (h₁.isInducing.specializes_iff.mpr h1)
    rw [h₁.injective h2]
  · rintro ⟨hy, hmin⟩
    refine ⟨(hP y).mpr hy, fun w hw hwy => ?_⟩
    obtain ⟨y', rfl⟩ := hr₁ y w hwy
    have h1 : y' ⤳ y := h₁.isInducing.specializes_iff.mp hwy
    have h2 := hmin (g₂ y') ((hP y').mp hw) (h₂.isInducing.specializes_iff.mpr h1)
    rw [h₂.injective h2]

end MinimalPoints

namespace Subscheme
variable {X : Scheme.{u}}

/-- The irreducible components of `D` are the reduced closures of the points of `D` without proper
generization in `D`. -/
theorem mem_irreducibleComponents_iff_exists_isMinimalPoint (D : Subscheme X) (C : Subscheme X) :
    C ∈ D.irreducibleComponents ↔
      ∃ η, IsMinimalPoint D.pts η ∧ C = ofClosed ⟨closure {η}, isClosed_closure⟩ := by
  constructor
  · rintro ⟨Z, ⟨⟨hirr, hsub⟩, hmax⟩, rfl⟩
    obtain ⟨η, hη⟩ := QuasiSober.sober hirr Z.isClosed
    have hηZ : η ∈ (Z : Set X) := hη.mem
    refine ⟨η, ⟨hsub hηZ, fun w hw hwη => ?_⟩, ?_⟩
    · let Z₂ : TopologicalSpace.Closeds X := ⟨closure {w}, isClosed_closure⟩
      have hZ₂ : Z ≤ Z₂ := by
        show (Z : Set X) ≤ closure {w}
        rw [← hη.def]
        exact closure_minimal (Set.singleton_subset_iff.mpr (specializes_iff_mem_closure.mp hwη))
          isClosed_closure
      have hle : Z₂ ≤ Z := hmax (y := Z₂) ⟨isIrreducible_singleton.closure,
        closure_minimal (Set.singleton_subset_iff.mpr hw) D.support.isClosed⟩ hZ₂
      have hwZ : w ∈ (Z : Set X) := hle (subset_closure rfl)
      rw [← hη.def] at hwZ
      exact (hwη.antisymm (specializes_iff_mem_closure.mpr hwZ)).eq
    · congr 1
      exact TopologicalSpace.Closeds.ext hη.def.symm
  · rintro ⟨η, ⟨hη, hmin⟩, rfl⟩
    refine ⟨⟨closure {η}, isClosed_closure⟩, ⟨⟨isIrreducible_singleton.closure,
      closure_minimal (Set.singleton_subset_iff.mpr hη) D.support.isClosed⟩, fun Z₂ hZ₂ hle => ?_⟩,
      rfl⟩
    obtain ⟨ζ, hζ⟩ := QuasiSober.sober hZ₂.1 Z₂.isClosed
    have hηZ₂ : η ∈ (Z₂ : Set X) := hle (subset_closure rfl)
    have hζη : ζ ⤳ η := hζ.specializes hηZ₂
    have hζD : ζ ∈ D.pts := hZ₂.2 hζ.mem
    have : ζ = η := hmin ζ hζD hζη
    show (Z₂ : Set X) ⊆ closure {η}
    rw [← hζ.def, this]

/-- The points of a finite intersection of subschemes. -/
theorem pts_iSup_finset {ι : Type*} (T : Finset ι) (E : ι → Subscheme X) :
    (⨆ i ∈ T, E i).pts = ⋂ i ∈ T, (E i).pts := by
  ext x
  simp only [Set.mem_iInter]
  rw [show x ∈ (⨆ i ∈ T, E i).pts ↔ _ from mem_pts_iff_stalkIdeal_ne_top]
  rw [stalkIdeal_iSup_eq']
  simp only [stalkIdeal_iSup_eq']
  constructor
  · intro h i hi
    refine mem_pts_iff_stalkIdeal_ne_top.mpr fun htop => h ?_
    rw [eq_top_iff]
    exact htop ▸ le_iSup₂_of_le i hi le_rfl
  · intro h htop
    have hle : (⨆ i, ⨆ (_ : i ∈ T), (E i).stalkIdeal x) ≤ maximalIdeal (X.presheaf.stalk x) :=
      iSup_le fun i => iSup_le fun hi =>
        stalkIdeal_le_maximalIdeal (E i) (h i hi)
    rw [htop] at hle
    exact (maximalIdeal.isMaximal _).ne_top (top_le_iff.mp hle)

end Subscheme

namespace MonoidalTransformation
variable {X : Scheme.{u}} {B : Subscheme X}

/-- Over `X − B` the monoidal transformation is an isomorphism (p. 167): points of `X' − f⁻¹(B)`
and of `X − B` are identified by two embeddings of a common scheme `Z`. -/
theorem exists_isEmbedding_off_exceptional (t : MonoidalTransformation X B) :
    ∃ (Z : Scheme.{u}) (ι : Z ⟶ X) (j : Z ⟶ t.X'), Topology.IsEmbedding ι.base ∧
      Topology.IsEmbedding j.base ∧ (∀ z, t.f (j z) = ι z) ∧ Set.range ι.base = B.ptsᶜ ∧
      Set.range j.base = t.exceptional.ptsᶜ := by
  obtain ⟨Z, ι, j, -, hι, -, hj, -, hcomp, hrι, hrj, -, -⟩ :=
    DatumTransform.exists_flat_isPreimmersion_off_center t
  exact ⟨Z, ι, j, ι.isEmbedding, j.isEmbedding, hcomp, hrι, hrj⟩

/-- Points off the exceptional subscheme: a point has no proper generization in a set `P'` iff
its image has none in a set `P` that corresponds to `P'` off `E`. -/
theorem isMinimalPoint_iff_of_notMem_exceptional (t : MonoidalTransformation X B)
    {P' : Set t.X'} {P : Set X} (hP : ∀ w, w ∉ t.exceptional.pts → (w ∈ P' ↔ t.f w ∈ P))
    {w : t.X'} (hw : w ∉ t.exceptional.pts) :
    IsMinimalPoint P' w ↔ IsMinimalPoint P (t.f w) := by
  obtain ⟨Z, ι, j, hι, hj, hcomp, hrι, hrj⟩ := t.exists_isEmbedding_off_exceptional
  have hwr : w ∈ Set.range j.base := by rw [hrj]; exact hw
  obtain ⟨z, rfl⟩ := hwr
  have h1 := isMinimalPoint_iff_of_isEmbedding (g₁ := j.base) (g₂ := ι.base) hj hι
    (fun z' w' hw' => by
      rw [hrj]
      exact Specializes.mem_open hw' t.exceptional.support.isClosed.isOpen_compl
        (by rw [← hrj]; exact ⟨z', rfl⟩))
    (fun z' w' hw' => by
      rw [hrι]
      exact Specializes.mem_open hw' B.support.isClosed.isOpen_compl
        (by rw [← hrι]; exact ⟨z', rfl⟩))
    (PA := P') (PB := P) (fun z' => by
      have : j.base z' ∉ t.exceptional.pts := by
        have : j.base z' ∈ Set.range j.base := ⟨z', rfl⟩
        rw [hrj] at this
        exact this
      rw [hP _ this, hcomp]) z
  rw [hcomp z]
  exact h1

/-- Specialization off the exceptional subscheme is reflected by `f`. -/
theorem specializes_of_specializes_apply_of_notMem_exceptional (t : MonoidalTransformation X B)
    {w₁ w₂ : t.X'} (h₁ : w₁ ∉ t.exceptional.pts) (h₂ : w₂ ∉ t.exceptional.pts)
    (h : t.f w₁ ⤳ t.f w₂) : w₁ ⤳ w₂ := by
  obtain ⟨Z, ι, j, hι, hj, hcomp, hrι, hrj⟩ := t.exists_isEmbedding_off_exceptional
  have hw₁ : w₁ ∈ Set.range j.base := by rw [hrj]; exact h₁
  have hw₂ : w₂ ∈ Set.range j.base := by rw [hrj]; exact h₂
  obtain ⟨z₁, rfl⟩ := hw₁
  obtain ⟨z₂, rfl⟩ := hw₂
  rw [hcomp, hcomp] at h
  exact hj.isInducing.specializes_iff.mpr (hι.isInducing.specializes_iff.mp h)

/-- The closure of the strict preimage of the closure of `f(η')` is the closure of `η'`. -/
theorem closure_preimage_closure_sdiff_eq (t : MonoidalTransformation X B) {η' : t.X'}
    (hη' : η' ∉ t.exceptional.pts) :
    closure (t.f.base ⁻¹' closure {t.f η'} \ t.exceptional.pts) = closure {η'} := by
  apply Set.Subset.antisymm
  · refine closure_minimal (fun w hw => ?_) isClosed_closure
    have hsp : t.f η' ⤳ t.f w := specializes_iff_mem_closure.mpr hw.1
    exact specializes_iff_mem_closure.mp
      (t.specializes_of_specializes_apply_of_notMem_exceptional hη' hw.2 hsp)
  · exact closure_mono (Set.singleton_subset_iff.mpr ⟨subset_closure rfl, hη'⟩)

end MonoidalTransformation

namespace CD

variable {X : Scheme.{u}}

/-- `K⁰_r(ℜ)` is empty for `r > N`: the codimension of a non-empty subscheme is at most the
dimension.  The paper does not state this; Lean uses it to bound the induction of Lemma (D.1)
(gap filled, see `exists_isPermissibleII_S_eq_empty_of_forall_stalkIdeal_eq_top`). -/
theorem not_mem_K0_of_dim_lt {N : ℕ} (hdim : X.dim = (N : WithBot ℕ∞)) (ℜ : DatumII.Raw X)
    {r : ℕ} (hr : N < r) (H : Subscheme X) : H ∉ K0 ℜ r := by
  rintro ⟨-, hcodim, -⟩
  by_cases hne : H.pts.Nonempty
  · obtain ⟨x, hx⟩ := hne
    have h1 : H.codim ≤ H.codimAt x := iInf₂_le x hx
    have h2 : H.codimAt x ≤ N := by
      have hne' : H.stalkIdeal x ≠ ⊤ := Subscheme.mem_pts_iff_stalkIdeal_ne_top.mp hx
      have h3 := Ideal.height_le_ringKrullDim_of_ne_top hne'
      have h4 : X.dimAt x ≤ X.dim := le_iSup (fun x => X.dimAt x) x
      have h5 : ((H.codimAt x : ℕ∞) : WithBot ℕ∞) ≤ (N : WithBot ℕ∞) :=
        h3.trans (hdim ▸ h4)
      exact_mod_cast h5
    rw [hcodim] at h1
    have : (r : ℕ∞) ≤ N := h1.trans h2
    exact absurd (by exact_mod_cast this : r ≤ N) (by omega)
  · have : H.pts = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
    unfold Subscheme.codim at hcodim
    have : (⨅ x ∈ H.pts, H.codimAt x) = ⊤ := by simp [this]
    rw [this] at hcodim
    exact absurd hcodim.symm (ENat.natCast_ne_top r)

theorem A_eq_zero_of_dim_lt {N : ℕ} (hdim : X.dim = (N : WithBot ℕ∞)) (ℜ : DatumII.Raw X)
    {r : ℕ} (hr : N < r) : A ℜ r = 0 := by
  unfold A
  have : weightOn ℜ '' K0 ℜ r = ∅ := by
    ext n
    simp only [Set.mem_image, Set.mem_empty_iff_false, iff_false, not_exists, not_and]
    intro H hH
    exact absurd hH (not_mem_K0_of_dim_lt hdim ℜ hr H)
  rw [this]
  exact csSup_empty

theorem _root_.Hironaka.ExtendsToRSOP.height_span_eq_card {R : Type u} [CommRing R] [IsRegularLocalRing R]
    {K : Finset R} (h : ExtendsToRSOP R K) : (Ideal.span (K : Set R)).height = K.card := by
  classical
  have hP := h.isPrime_span
  refine le_antisymm ?_ h.card_le_height_span
  exact Ideal.height_le_card_of_mem_minimalPrimes_span_finset
    ⟨⟨hP, le_rfl⟩, fun q hq _ => hq.2⟩

theorem _root_.Hironaka.Subscheme.isContainedIn_ofClosed {T T' : TopologicalSpace.Closeds X} (h : T ≤ T') :
    (Subscheme.ofClosed T).IsContainedIn (Subscheme.ofClosed T') := fun U => by
  show PrimeSpectrum.vanishingIdeal (U.2.fromSpec ⁻¹' (T' : Set X)) ≤
    PrimeSpectrum.vanishingIdeal (U.2.fromSpec ⁻¹' (T : Set X))
  exact PrimeSpectrum.vanishingIdeal_anti_mono (Set.preimage_mono h)

/-- The union `E₁ ∪ ⋯ ∪ E_α` of the components of a datum is reduced. -/
theorem _root_.Hironaka.DatumII.Raw.isReduced_eUnion (ℜ : DatumII.Raw X) (hℜ : ℜ.IsDatum) : ℜ.eUnion.IsReduced := by
  refine Subscheme.isReduced_of_isRadical_stalkIdeal fun z => ?_
  unfold DatumII.Raw.eUnion
  rw [DatumTransform.stalkIdeal_iInf_fintype]
  refine Ideal.isRadical_iInf _ fun i => ?_
  by_cases hz : z ∈ (ℜ.E i).pts
  · have := Subscheme.isPrime_stalkIdeal_of_isNonsingular_of_mem_pts (ℜ.E i)
      (hℜ.2.1 i).isNonsingular hz
    exact this.isRadical
  · rw [Subscheme.stalkIdeal_eq_top_of_notMem_pts hz]
    exact (show (⊤ : Ideal (X.presheaf.stalk z)).IsRadical from fun _ _ => Submodule.mem_top)

/-- Local structure of the distinct components `E_i`, `i ∈ T`, through a point `y`: by the normal
crossings at `y` their stalks are generated by distinct members of a regular system of parameters,
so the stalk of `⋂_{i ∈ T} E_i` is generated by `|T|` elements extendable to such a system. -/
theorem exists_rsop_adapted_stalkIdeal_iSup (hXns : X.IsNonsingular)
    (ℜ : DatumII.Raw X) (hℜ : ℜ.IsDatum)
    (hE : ∀ i j, i ≠ j → ℜ.E i ≠ Subscheme.empty → ℜ.E i ≠ ℜ.E j) {y : X}
    (T : Finset (Fin ℜ.α)) (hT : ∀ i ∈ T, y ∈ (ℜ.E i).pts) :
    ∃ z : Finset (X.presheaf.stalk y), IsRegularSystemOfParameters _ z ∧
      (∃ J ⊆ z, ℜ.eUnion.stalkIdeal y = Ideal.span {∏ a ∈ J, a}) ∧
      ∃ K ⊆ z, K.card = T.card ∧
        (⨆ i ∈ T, ℜ.E i).stalkIdeal y = Ideal.span (K : Set (X.presheaf.stalk y)) := by
  classical
  have : IsRegularLocalRing (X.presheaf.stalk y) := hXns y
  have hred := DatumII.Raw.isReduced_eUnion ℜ hℜ
  obtain ⟨z, hz, ⟨J, hJz, hEJ⟩, -⟩ :=
    (Subscheme.hasOnlyNormalCrossingsWithAt_iff hred (hXns y)).mp (hℜ.2.2.1 y)
  have hgen : ∀ i, i ∈ T → ∃ a ∈ J, (ℜ.E i).stalkIdeal y = Ideal.span {a} := by
    intro i hi
    have hne : ℜ.E i ≠ Subscheme.empty := fun h => by
      have := hT i hi
      rw [h, Subscheme.pts_empty] at this
      exact this
    obtain ⟨hns, hirr, hcodim⟩ := (hℜ.2.1 i).resolve_left hne
    have hprime := Subscheme.isPrime_stalkIdeal_of_isNonsingular_of_mem_pts (ℜ.E i) hns (hT i hi)
    have hht : ((ℜ.E i).stalkIdeal y).height = 1 := by
      rw [← Subscheme.codim_eq_height (ℜ.E i) hns hirr (hT i hi), hcodim]
    have hle : Ideal.span {∏ a ∈ J, a} ≤ (ℜ.E i).stalkIdeal y := by
      rw [← hEJ]
      unfold DatumII.Raw.eUnion
      rw [DatumTransform.stalkIdeal_iInf_fintype]
      exact iInf_le _ i
    exact DatumTransform.eq_span_of_prod_le hz hJz hht hle
  choose! κ hκJ hκeq using hgen
  have hinj : Set.InjOn κ (T : Set (Fin ℜ.α)) := by
    intro i hi i' hi' hκ
    by_contra hne
    have hnemp : ℜ.E i ≠ Subscheme.empty := fun h => by
      have := hT i hi
      rw [h, Subscheme.pts_empty] at this
      exact this
    refine hE i i' hne hnemp ?_
    obtain ⟨hns, hirr, -⟩ := (hℜ.2.1 i).resolve_left hnemp
    have hnemp' : ℜ.E i' ≠ Subscheme.empty := fun h => by
      have := hT i' hi'
      rw [h, Subscheme.pts_empty] at this
      exact this
    obtain ⟨hns', hirr', -⟩ := (hℜ.2.1 i').resolve_left hnemp'
    exact Subscheme.eq_of_stalkIdeal_eq_of_isIrreducible hns hirr hns' hirr' (hT i hi) (hT i' hi')
      (by rw [hκeq i hi, hκeq i' hi', hκ])
  refine ⟨z, hz, ⟨J, hJz, hEJ⟩, T.image κ, ?_, Finset.card_image_of_injOn hinj, ?_⟩
  · intro a ha
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp ha
    exact hJz (hκJ i hi)
  · have hsup : (⨆ i ∈ T, ℜ.E i).stalkIdeal y = ⨆ i ∈ T, (ℜ.E i).stalkIdeal y := by
      simp only [Subscheme.stalkIdeal_iSup_eq']
    rw [hsup]
    apply le_antisymm
    · refine iSup₂_le fun i hi => ?_
      rw [hκeq i hi, Ideal.span_le]
      intro b hb
      rw [Set.mem_singleton_iff.mp hb]
      exact Ideal.subset_span (Finset.mem_coe.mpr (Finset.mem_image_of_mem κ hi))
    · rw [Ideal.span_le]
      intro b hb
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hb)
      refine Ideal.mem_iSup_of_mem i (Ideal.mem_iSup_of_mem hi ?_)
      rw [hκeq i hi]
      exact Ideal.mem_span_singleton_self _

/-- The stalk of `⋂_{i ∈ T} E_i` at such a point is generated by `|T|` elements extendable to a
regular system of parameters. -/
theorem exists_extendsToRSOP_stalkIdeal_iSup_eq_span (hXns : X.IsNonsingular)
    (ℜ : DatumII.Raw X) (hℜ : ℜ.IsDatum)
    (hE : ∀ i j, i ≠ j → ℜ.E i ≠ Subscheme.empty → ℜ.E i ≠ ℜ.E j) {y : X}
    (T : Finset (Fin ℜ.α)) (hT : ∀ i ∈ T, y ∈ (ℜ.E i).pts) :
    ∃ K : Finset (X.presheaf.stalk y), ExtendsToRSOP _ K ∧ K.card = T.card ∧
      (⨆ i ∈ T, ℜ.E i).stalkIdeal y = Ideal.span (K : Set (X.presheaf.stalk y)) := by
  have : IsRegularLocalRing (X.presheaf.stalk y) := hXns y
  obtain ⟨z, hz, -, K, hKz, hcard, hD⟩ := exists_rsop_adapted_stalkIdeal_iSup hXns ℜ hℜ hE T hT
  exact ⟨K, (ExtendsToRSOP.of_isRegularSystemOfParameters hz).mono hKz, hcard, hD⟩

/-- The component of `⋂_{i ∈ T} E_i` through a point on all these `E_i` (distinct, normal
crossings): it is non-singular of codimension `|T|`, hence lies in `K⁰_{|T|}(ℜ)`. -/
theorem exists_mem_K0_of_forall_mem_pts (hXns : X.IsNonsingular)
    (ℜ : DatumII.Raw X) (hℜ : ℜ.IsDatum)
    (hE : ∀ i j, i ≠ j → ℜ.E i ≠ Subscheme.empty → ℜ.E i ≠ ℜ.E j) {x : X}
    (T : Finset (Fin ℜ.α)) (hT : ∀ i ∈ T, x ∈ (ℜ.E i).pts) :
    ∃ H ∈ K0 ℜ T.card, ∀ i ∈ T, H.IsContainedIn (ℜ.E i) := by
  classical
  obtain ⟨K, hK, hcard, hDx⟩ := exists_extendsToRSOP_stalkIdeal_iSup_eq_span hXns ℜ hℜ hE T hT
  set D : Subscheme X := ⨆ i ∈ T, ℜ.E i with hD
  have : IsRegularLocalRing (X.presheaf.stalk x) := hXns x
  have hprime := hK.isPrime_span
  have hmin : D.stalkIdeal x ∈ (D.stalkIdeal x).minimalPrimes := by
    rw [hDx]
    exact ⟨⟨hprime, le_rfl⟩, fun q hq _ => hq.2⟩
  obtain ⟨C, hC, hxC, hCx⟩ :=
    Subscheme.exists_mem_irreducibleComponents_of_mem_minimalPrimes D x hmin
  -- the points of `C` lie on all `E_i`, `i ∈ T`
  have hCsub : ∀ y ∈ C.pts, ∀ i ∈ T, y ∈ (ℜ.E i).pts := by
    obtain ⟨Z, ⟨⟨-, hZsub⟩, -⟩, hZ⟩ := hC
    intro y hy i hi
    rw [hZ, Subscheme.pts_ofClosed] at hy
    have h1 := hZsub hy
    have h2 : ℜ.E i ≤ D := le_iSup₂ (f := fun i (_ : i ∈ T) => ℜ.E i) i hi
    exact Scheme.IdealSheafData.support_antitone h2 h1
  -- the stalks of `C` are the (prime) stalks of `D`
  have hCy : ∀ y ∈ C.pts, ∃ K' : Finset (X.presheaf.stalk y), ExtendsToRSOP _ K' ∧
      K'.card = T.card ∧ C.stalkIdeal y = Ideal.span (K' : Set (X.presheaf.stalk y)) := by
    intro y hy
    have : IsRegularLocalRing (X.presheaf.stalk y) := hXns y
    obtain ⟨K', hK', hcard', hDy⟩ := exists_extendsToRSOP_stalkIdeal_iSup_eq_span hXns ℜ hℜ hE T
      (hCsub y hy)
    refine ⟨K', hK', hcard', ?_⟩
    have hmem := Subscheme.stalkIdeal_mem_minimalPrimes hC hy
    rw [hDy] at hmem
    have hP' := hK'.isPrime_span
    exact le_antisymm (hmem.2 ⟨hP', le_rfl⟩ hmem.1.2 |> fun h => h) hmem.1.2
  have hns : C.IsNonsingular := by
    refine Subscheme.isNonsingular_of_stalk_quot C fun y hy => ?_
    have : IsRegularLocalRing (X.presheaf.stalk y) := hXns y
    obtain ⟨K', hK', -, hCy'⟩ := hCy y hy
    rw [hCy']
    exact hK'.isRegularLocalRing_quotient
  have hirr : C.IsIrreducible := by
    obtain ⟨Z, ⟨⟨hZirr, -⟩, -⟩, hZ⟩ := hC
    refine Subscheme.isIrreducible_of_pts C ?_
    rw [hZ, Subscheme.pts_ofClosed]
    exact hZirr
  refine ⟨C, ⟨hns, ?_, T, rfl, hC⟩, fun i hi => ?_⟩
  · rw [Subscheme.codim_eq_height C hns hirr hxC]
    obtain ⟨K', hK', hcard', hCy'⟩ := hCy x hxC
    rw [hCy', ExtendsToRSOP.height_span_eq_card hK', hcard']
  · obtain ⟨Z, ⟨⟨-, hZsub⟩, -⟩, hZ⟩ := hC
    have hE' : ℜ.E i = Subscheme.ofClosed (ℜ.E i).support :=
      Subscheme.eq_ofClosed_support _ (Subscheme.isReduced_of_isNonsingular
        (hℜ.2.1 i).isNonsingular)
    rw [hZ]
    conv_rhs => rw [hE']
    refine Subscheme.isContainedIn_ofClosed fun y hy => ?_
    have : y ∈ C.pts := by rw [hZ, Subscheme.pts_ofClosed]; exact hy
    exact hCsub y this i hi

/-- In the reduced situation of the proof of Lemma (D.1) (`J = O_X`, distinct non-empty `E_i`):
if `A_s(ℜ) < b` for all `s ≥ 1` then `S(ℜ)` is empty.

Deviation from the paper (gap filled): the paper never states this.  Its proof of
Lemma (D.1) takes "the smallest integer (positive) `r` such that `A_r(ℜ) ≥ b`" (p. 312) and
ends with "It is obvious that if this is proved then Lemma (D.1) follows by induction" (p. 313);
that the induction can only stop with `S(ℜ) = ∅` is this tacit step.  Lean's argument: a point
`x ∈ S(ℜ)` lies on the `E_i`, `i ∈ T`, with `∑_{i ∈ T} a_i ≥ b ≥ 1` (as `J = O_X`), so `T ≠ ∅`; by
the normal crossings at the points of `⋂_{i ∈ T} E_i` (`CD.exists_extendsToRSOP_stalkIdeal_iSup_eq_span`)
a component `H` of `⋂_{i ∈ T} E_i` through `x` is non-singular of codimension `|T|`, i.e. lies in
`K⁰_{|T|}(ℜ)` (`CD.exists_mem_K0_of_forall_mem_pts`), and `H ⊆ E_i` for `i ∈ T`, so
`b ≤ ∑_{i ∈ T} a_i ≤ ∑_{E_i ⊇ H} a_i ≤ A_{|T|}(ℜ)`, a contradiction. -/
@[blueprint "lem:IV.D-1-S-empty"
  (statement := /-- In the proof of Lemma (D.1) (\cref{lem:IV.D-1}), suppose $J=\mathcal O_X$
    and $E_i\ne E_j$ if $i\ne j$ and $E_i$ is not empty. If $A_s(\mathfrak R)<b$ for every
    $s\ge1$ (\cref{def:IV.D-1-symbols}), then $S(\mathfrak R)$ is empty.

    \textbf{Not in the paper (tacit step).} The paper takes ``the smallest integer (positive)
    [$r$] such that $A_r(\mathfrak R)\ge b$'' (p.~312) without saying why one exists while
    $S(\mathfrak R)\ne\emptyset$, and ends with ``It is obvious that if this is proved then Lemma
    (D.1) follows by induction'' (p.~313). This lemma is the step that makes the induction end
    with $S=\emptyset$. -/)
  (proof := /-- (Not in the paper.) Let $x\in S(\mathfrak R)$ and
    $T=\{i\mid x\in E_i\}$. As $J=\mathcal O_X$, $\sum_{i\in T}a_i\ge b\ge1$, so $T\ne\emptyset$.
    The $E_i$, $i\in T$, are distinct and have only normal crossings at $x$, so the irreducible
    component $H$ of $\bigcap_{i\in T}E_i$ through $x$ is non-singular of codimension $|T|$, i.e.\
    $H\in K^0_{|T|}(\mathfrak R)$ (at every point $y$ of $\bigcap_{i\in T}E_i$ the ideals of the
    $E_i$, $i\in T$, are generated by $|T|$ distinct members of a regular system of parameters, so
    the ideal of $\bigcap_{i\in T}E_i$ at $y$ is prime, with regular quotient, of height $|T|$);
    $H\subseteq E_i$ for $i\in T$. Hence
    $b\le\sum_{i\in T}a_i\le\sum_{E_i\supseteq H}a_i\le A_{|T|}(\mathfrak R)$, a
    contradiction. -/)
  (proofUses := ["def:IV.D-1-symbols"])
  (latexEnv := "lemma")]
theorem S_eq_empty_of_forall_A_lt {N : ℕ} (hX : IsAmbient X N) (ℜ : DatumII.Raw X)
    (hℜ : ℜ.IsDatum) (hJ : ℜ.J = ⊤)
    (hE : ∀ i j, i ≠ j → ℜ.E i ≠ Subscheme.empty → ℜ.E i ≠ ℜ.E j)
    (h : ∀ s, 1 ≤ s → A ℜ s < ℜ.b) : ℜ.S = ∅ := by
  classical
  refine Set.eq_empty_iff_forall_notMem.mpr fun x hx => ?_
  have hν : ℜ.nuAt x = 0 := by
    unfold DatumII.Raw.nuAt
    rw [hJ, Subscheme.stalkIdeal_top_eq]
    exact Ideal.nu_top
  have hb : ℜ.b ≤ ℜ.weight x := by
    have := hx
    simp only [DatumII.Raw.S, Set.mem_ofPred_eq, hν, add_zero] at this
    exact_mod_cast this
  set T : Finset (Fin ℜ.α) := Finset.univ.filter (fun i => x ∈ (ℜ.E i).pts) with hT
  have hw : ℜ.weight x = ∑ i ∈ T, ℜ.a i := by
    unfold DatumII.Raw.weight
    exact Finset.sum_congr (by ext; simp [hT]) fun _ _ => rfl
  have hTmem : ∀ i ∈ T, x ∈ (ℜ.E i).pts := fun i hi => (Finset.mem_filter.mp hi).2
  have hTne : 1 ≤ T.card := by
    rw [Nat.one_le_iff_ne_zero, Ne, Finset.card_eq_zero]
    intro hT0
    rw [hw, hT0, Finset.sum_empty] at hb
    exact absurd hℜ.1 (by omega)
  obtain ⟨H, hH0, hHsub⟩ := exists_mem_K0_of_forall_mem_pts hX.2.1 ℜ hℜ hE T hTmem
  have hweight : ∑ i ∈ T, ℜ.a i ≤ weightOn ℜ H := by
    unfold weightOn
    refine Finset.sum_le_sum_of_subset ?_
    intro i hi
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hHsub i hi⟩
  have hA : weightOn ℜ H ≤ A ℜ T.card := by
    unfold A
    refine le_csSup ⟨∑ i, ℜ.a i, ?_⟩ ⟨H, hH0, rfl⟩
    rintro _ ⟨H', -, rfl⟩
    unfold weightOn
    exact Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
  have := h T.card hTne
  omega

/-- "Note that the transform of `ℜ` by any permissible succession of monoidal transformations of
`X` for `ℜ` has also these properties" (p. 312): after a monoidal transformation, `J = O_X` and
the non-empty `E_i` are still distinct (the strict transforms of distinct non-singular
irreducible `E_i` with non-empty strict transform are distinct, and differ from the exceptional
subscheme).

Deviation from the paper (gap filled): the paper asserts this without proof. -/
theorem J_eq_top_and_distinct_transform (ℜ : DatumII.Raw X)
    (hℜ : ℜ.IsDatum) (hJ : ℜ.J = ⊤)
    (hE : ∀ i j, i ≠ j → ℜ.E i ≠ Subscheme.empty → ℜ.E i ≠ ℜ.E j)
    {B : Subscheme X} (t : MonoidalTransformation X B) :
    (ℜ.transform t).J = ⊤ ∧
      ∀ i j, i ≠ j → (ℜ.transform t).E i ≠ Subscheme.empty →
        (ℜ.transform t).E i ≠ (ℜ.transform t).E j := by
  have hU : ℜ.HasUnitJOnS := fun x _ => by rw [hJ]; exact Subscheme.stalkIdeal_top_eq x
  refine ⟨?_, ?_⟩
  · show Subscheme.divPow (Subscheme.totalTransform t.f ℜ.J) t.exceptional ℜ.nu.toNat = ⊤
    rw [hJ, DatumII.Raw.nu_eq_zero_of_hasUnitJOnS hU]
    exact DatumII.Raw.divPow_top_zero t
  · -- the strict transform of a non-empty `E_a` is non-empty only if `E_a` is non-empty
    have hst : ∀ a, Subscheme.strictTransform t (ℜ.E a) ≠ Subscheme.empty → ℜ.E a ≠ Subscheme.empty :=
      fun a h hEa => h (by
        rw [hEa]
        exact top_le_iff.mp (by
          have := MonoidalTransformation.totalTransform_le_strictTransform t
            (Subscheme.empty : Subscheme X)
          rwa [Subscheme.totalTransform_empty] at this))
    -- a point of `f⁻¹(V) ∖ E` lies on the strict transform of `V`
    have hpt : ∀ V : Subscheme X, Subscheme.strictTransform t V ≠ Subscheme.empty →
        ∃ y, y ∈ t.f.base ⁻¹' V.pts \ t.exceptional.pts := by
      intro V hV
      have hne : (Subscheme.strictTransform t V).pts.Nonempty :=
        Set.nonempty_iff_ne_empty.mpr fun h => hV (Subscheme.eq_empty_of_pts_eq_empty h)
      rw [MonoidalTransformation.pts_strictTransform_eq_closure, closure_nonempty_iff] at hne
      exact hne
    have hsub : ∀ V : Subscheme X, t.f.base ⁻¹' V.pts \ t.exceptional.pts ⊆
        (Subscheme.strictTransform t V).pts := fun V y hy => by
      rw [MonoidalTransformation.pts_strictTransform_eq_closure]
      exact subset_closure hy
    intro i j hij hne
    rcases Fin.eq_castSucc_or_eq_last i with ⟨a, rfl⟩ | rfl <;>
      rcases Fin.eq_castSucc_or_eq_last j with ⟨b, rfl⟩ | rfl
    · simp only [DatumII.Raw.transform, Fin.snoc_castSucc] at hne ⊢
      intro heq
      have hEa := hst a hne
      have hab : a ≠ b := fun h => hij (by rw [h])
      refine hE a b hab hEa (MonoidalTransformation.eq_of_strictTransform_eq t ?_ ?_ ?_ ?_ ?_ heq)
      · exact ((hℜ.2.1 a).resolve_left hEa).1
      · exact ((hℜ.2.1 a).resolve_left hEa).2.1
      · exact ((hℜ.2.1 b).resolve_left fun hEb => hne (by
          rw [heq, hEb]
          exact top_le_iff.mp (by
            have := MonoidalTransformation.totalTransform_le_strictTransform t
              (Subscheme.empty : Subscheme X)
            rwa [Subscheme.totalTransform_empty] at this))).1
      · exact ((hℜ.2.1 b).resolve_left fun hEb => hne (by
          rw [heq, hEb]
          exact top_le_iff.mp (by
            have := MonoidalTransformation.totalTransform_le_strictTransform t
              (Subscheme.empty : Subscheme X)
            rwa [Subscheme.totalTransform_empty] at this))).2.1
      · exact Set.nonempty_iff_ne_empty.mpr fun h => hne (Subscheme.eq_empty_of_pts_eq_empty h)
    · simp only [DatumII.Raw.transform, Fin.snoc_castSucc, Fin.snoc_last] at hne ⊢
      intro heq
      obtain ⟨y, hy⟩ := hpt _ hne
      exact hy.2 (heq ▸ hsub _ hy)
    · simp only [DatumII.Raw.transform, Fin.snoc_castSucc, Fin.snoc_last] at hne ⊢
      intro heq
      have hb : Subscheme.strictTransform t (ℜ.E b) ≠ Subscheme.empty := fun h => hne (heq.trans h)
      obtain ⟨y, hy⟩ := hpt _ hb
      exact hy.2 (heq ▸ hsub _ hy)
    · exact absurd rfl hij

theorem weightOn_le_A {ℜ : DatumII.Raw X} {s : ℕ} {G : Subscheme X} (hG : G ∈ K0 ℜ s) :
    weightOn ℜ G ≤ A ℜ s := by
  classical
  unfold A
  refine le_csSup ⟨∑ i, ℜ.a i, ?_⟩ ⟨G, hG, rfl⟩
  rintro _ ⟨H', -, rfl⟩
  unfold weightOn
  exact Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)

theorem A_lt_of_forall_lt {ℜ : DatumII.Raw X} {s c : ℕ} (hc : 0 < c)
    (h : ∀ G ∈ K0 ℜ s, weightOn ℜ G < c) : A ℜ s < c := by
  classical
  unfold A
  by_cases hne : (weightOn ℜ '' K0 ℜ s).Nonempty
  · have hbdd : BddAbove (weightOn ℜ '' K0 ℜ s) := ⟨∑ i, ℜ.a i, by
      rintro _ ⟨H', -, rfl⟩
      unfold weightOn
      exact Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)⟩
    obtain ⟨G, hG, hw⟩ := Nat.sSup_mem hne hbdd
    rw [← hw]
    exact h G hG
  · rw [Set.not_nonempty_iff_eq_empty] at hne
    rw [hne]
    simpa using hc

/-- A component of `⋂_{i ∈ T} E_i` is contained in each `E_i`, `i ∈ T`. -/
theorem isContainedIn_of_mem_irreducibleComponents (ℜ : DatumII.Raw X) (hℜ : ℜ.IsDatum)
    {T : Finset (Fin ℜ.α)} {C : Subscheme X} (hC : C ∈ (⨆ i ∈ T, ℜ.E i).irreducibleComponents)
    {i : Fin ℜ.α} (hi : i ∈ T) : C.IsContainedIn (ℜ.E i) := by
  obtain ⟨Z, ⟨⟨-, hZsub⟩, -⟩, hZ⟩ := hC
  have hE' : ℜ.E i = Subscheme.ofClosed (ℜ.E i).support :=
    Subscheme.eq_ofClosed_support _ (Subscheme.isReduced_of_isNonsingular
      (hℜ.2.1 i).isNonsingular)
  rw [hZ]
  conv_rhs => rw [hE']
  refine Subscheme.isContainedIn_ofClosed fun y hy => ?_
  have h2 : ℜ.E i ≤ ⨆ i ∈ T, ℜ.E i := le_iSup₂ (f := fun i (_ : i ∈ T) => ℜ.E i) i hi
  exact Scheme.IdealSheafData.support_antitone h2 (hZsub hy)

theorem isIrreducible_of_mem_K0 {ℜ : DatumII.Raw X} {s : ℕ} {G : Subscheme X}
    (hG : G ∈ K0 ℜ s) : G.IsIrreducible := by
  obtain ⟨-, -, T, -, Z, ⟨⟨hZirr, -⟩, -⟩, hZ⟩ := hG
  refine Subscheme.isIrreducible_of_pts G ?_
  rw [hZ, Subscheme.pts_ofClosed]
  exact hZirr

theorem pts_nonempty_of_mem_K0 {ℜ : DatumII.Raw X} {s : ℕ} {G : Subscheme X}
    (hG : G ∈ K0 ℜ s) : G.pts.Nonempty := by
  by_contra hne
  have h : G.pts = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
  have hcodim := hG.2.1
  unfold Subscheme.codim at hcodim
  have : (⨅ x ∈ G.pts, G.codimAt x) = ⊤ := by simp [h]
  rw [this] at hcodim
  exact ENat.natCast_ne_top s hcodim.symm

open Classical in
/-- A member of `K⁰_s(ℜ)` lies in at most `s` of the `E_i`: the `E_i ⊇ G` have stalks generated by
distinct members of a regular system of parameters, so their number is at most the height of the
stalk of `G`, which is `s`. -/
theorem card_filter_isContainedIn_le_of_mem_K0 (hXns : X.IsNonsingular) (ℜ : DatumII.Raw X)
    (hℜ : ℜ.IsDatum) (hE : ∀ i j, i ≠ j → ℜ.E i ≠ Subscheme.empty → ℜ.E i ≠ ℜ.E j)
    {s : ℕ} {G : Subscheme X} (hG : G ∈ K0 ℜ s) :
    (Finset.univ.filter (fun i => G.IsContainedIn (ℜ.E i))).card ≤ s := by
  classical
  obtain ⟨y, hy⟩ := pts_nonempty_of_mem_K0 hG
  have hT : ∀ i ∈ Finset.univ.filter (fun i => G.IsContainedIn (ℜ.E i)), y ∈ (ℜ.E i).pts :=
    fun i hi => pts_subset_of_isContainedIn (Finset.mem_filter.mp hi).2 hy
  obtain ⟨K, hK, hcard, hD⟩ :=
    exists_extendsToRSOP_stalkIdeal_iSup_eq_span hXns ℜ hℜ hE _ hT
  have : IsRegularLocalRing (X.presheaf.stalk y) := hXns y
  have hle : (⨆ i ∈ Finset.univ.filter (fun i => G.IsContainedIn (ℜ.E i)), ℜ.E i).stalkIdeal y ≤
      G.stalkIdeal y := by
    have : (⨆ i ∈ Finset.univ.filter (fun i => G.IsContainedIn (ℜ.E i)), ℜ.E i) ≤ G :=
      iSup₂_le fun i hi => Scheme.IdealSheafData.le_def.mpr (Finset.mem_filter.mp hi).2
    exact Subscheme.stalkIdeal_mono this y
  rw [hD] at hle
  have h1 := hK.card_le_height_span
  have h2 := Ideal.height_mono hle
  have h3 := Subscheme.codim_eq_height G hG.1 (isIrreducible_of_mem_K0 hG) hy
  rw [hG.2.1] at h3
  have : ((Finset.univ.filter (fun i => G.IsContainedIn (ℜ.E i))).card : ℕ∞) ≤ s := by
    rw [← hcard]
    exact h1.trans (h2.trans h3.ge)
  exact_mod_cast this

/-- A component of `⋂_{i ∈ T} E_i` has, at each of its points, the stalk of `⋂_{i ∈ T} E_i`
(which is prime there by the normal crossings). -/
theorem stalkIdeal_eq_of_mem_irreducibleComponents (hXns : X.IsNonsingular)
    (ℜ : DatumII.Raw X) (hℜ : ℜ.IsDatum)
    (hE : ∀ i j, i ≠ j → ℜ.E i ≠ Subscheme.empty → ℜ.E i ≠ ℜ.E j)
    {T : Finset (Fin ℜ.α)} {C : Subscheme X} (hC : C ∈ (⨆ i ∈ T, ℜ.E i).irreducibleComponents)
    {y : X} (hy : y ∈ C.pts) :
    C.stalkIdeal y = (⨆ i ∈ T, ℜ.E i).stalkIdeal y := by
  have : IsRegularLocalRing (X.presheaf.stalk y) := hXns y
  have hTy : ∀ i ∈ T, y ∈ (ℜ.E i).pts := fun i hi =>
    pts_subset_of_isContainedIn (isContainedIn_of_mem_irreducibleComponents ℜ hℜ hC hi) hy
  obtain ⟨z, hz, -, K, hKz, -, hDy⟩ := exists_rsop_adapted_stalkIdeal_iSup hXns ℜ hℜ hE T hTy
  have hmem := Subscheme.stalkIdeal_mem_minimalPrimes hC hy
  rw [hDy] at hmem ⊢
  have hP := ((ExtendsToRSOP.of_isRegularSystemOfParameters hz).mono hKz).isPrime_span
  exact le_antisymm (hmem.2 ⟨hP, le_rfl⟩ hmem.1.2) hmem.1.2

/-- A non-empty irreducible component of `⋂_{i ∈ T} E_i` belongs to `K⁰_{|T|}(ℜ)`: it is
non-singular of codimension `|T|` (the normal crossings at each of its points). -/
theorem mem_K0_of_mem_irreducibleComponents (hXns : X.IsNonsingular) (ℜ : DatumII.Raw X)
    (hℜ : ℜ.IsDatum) (hE : ∀ i j, i ≠ j → ℜ.E i ≠ Subscheme.empty → ℜ.E i ≠ ℜ.E j)
    {T : Finset (Fin ℜ.α)} {C : Subscheme X}
    (hC : C ∈ (⨆ i ∈ T, ℜ.E i).irreducibleComponents) (hne : C.pts.Nonempty) :
    C ∈ K0 ℜ T.card := by
  classical
  have hTy : ∀ y ∈ C.pts, ∀ i ∈ T, y ∈ (ℜ.E i).pts := fun y hy i hi =>
    pts_subset_of_isContainedIn (isContainedIn_of_mem_irreducibleComponents ℜ hℜ hC hi) hy
  have hCy : ∀ y ∈ C.pts, ∃ K' : Finset (X.presheaf.stalk y), ExtendsToRSOP _ K' ∧
      K'.card = T.card ∧ C.stalkIdeal y = Ideal.span (K' : Set (X.presheaf.stalk y)) := by
    intro y hy
    have : IsRegularLocalRing (X.presheaf.stalk y) := hXns y
    obtain ⟨K', hK', hcard', hDy⟩ :=
      exists_extendsToRSOP_stalkIdeal_iSup_eq_span hXns ℜ hℜ hE T (hTy y hy)
    exact ⟨K', hK', hcard', (stalkIdeal_eq_of_mem_irreducibleComponents hXns ℜ hℜ hE hC hy).trans
      hDy⟩
  have hns : C.IsNonsingular := by
    refine Subscheme.isNonsingular_of_stalk_quot C fun y hy => ?_
    have : IsRegularLocalRing (X.presheaf.stalk y) := hXns y
    obtain ⟨K', hK', -, hCy'⟩ := hCy y hy
    rw [hCy']
    exact hK'.isRegularLocalRing_quotient
  have hirr : C.IsIrreducible := by
    obtain ⟨Z, ⟨⟨hZirr, -⟩, -⟩, hZ⟩ := hC
    refine Subscheme.isIrreducible_of_pts C ?_
    rw [hZ, Subscheme.pts_ofClosed]
    exact hZirr
  obtain ⟨x, hx⟩ := hne
  refine ⟨hns, ?_, T, rfl, hC⟩
  rw [Subscheme.codim_eq_height C hns hirr hx]
  have : IsRegularLocalRing (X.presheaf.stalk x) := hXns x
  obtain ⟨K', hK', hcard', hCy'⟩ := hCy x hx
  rw [hCy', ExtendsToRSOP.height_span_eq_card hK', hcard']

/-- "It is clear that the monoidal transformation `f_H` with center `H` is permissible for `ℜ`"
(p. 312): `H ∈ K_r(ℜ)` is non-singular and irreducible, lies in `S(ℜ) = S_*(ℜ)` since
`A_r(ℜ) ≥ b` (here `ν(ℜ) = 0`), and has normal crossings with the `E_i`. -/
theorem isPermissible_of_mem_K {N : ℕ} (hX : IsAmbient X N) (ℜ : DatumII.Raw X)
    (hℜ : ℜ.IsDatum) (hJ : ℜ.J = ⊤)
    (hE : ∀ i j, i ≠ j → ℜ.E i ≠ Subscheme.empty → ℜ.E i ≠ ℜ.E j) {r : ℕ}
    (hbr : ℜ.b ≤ A ℜ r) {H : Subscheme X} (hH : H ∈ K ℜ r) : ℜ.IsPermissible H := by
  classical
  obtain ⟨hXa, hXns, hXirr, -⟩ := id hX
  have hU : ℜ.HasUnitJOnS := fun x _ => by rw [hJ]; exact Subscheme.stalkIdeal_top_eq x
  have hnu := DatumII.Raw.nu_eq_zero_of_hasUnitJOnS hU
  obtain ⟨hH0, hA⟩ := hH
  have hirr := isIrreducible_of_mem_K0 hH0
  obtain ⟨hns, hcodim, T, hcard, hC⟩ := hH0
  refine ⟨Or.inr ⟨hns, hirr⟩, fun y hy => ?_, fun y hy => ?_⟩
  · have hν0 : ℜ.nuAt y = 0 := by
      unfold DatumII.Raw.nuAt
      rw [hJ, Subscheme.stalkIdeal_top_eq]
      exact Ideal.nu_top
    have hw : ℜ.b ≤ ℜ.weight y := by
      have h1 : ℜ.b ≤ weightOn ℜ H := hA ▸ hbr
      refine h1.trans ?_
      unfold weightOn DatumII.Raw.weight
      refine Finset.sum_le_sum_of_subset fun i hi => ?_
      have hi' := (Finset.mem_filter.mp hi).2
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, pts_subset_of_isContainedIn hi' hy⟩
    unfold DatumII.Raw.sStar DatumII.Raw.sNu
    rw [hnu]
    refine ⟨?_, bot_le⟩
    show (ℜ.b : ℕ∞) ≤ (ℜ.weight y : ℕ∞) + ℜ.nuAt y
    rw [hν0, add_zero]
    exact_mod_cast hw
  · have hred := DatumII.Raw.isReduced_eUnion ℜ hℜ
    refine (Subscheme.hasOnlyNormalCrossingsWithAt_iff hred (hXns y)).mpr ?_
    have hTy : ∀ i ∈ T, y ∈ (ℜ.E i).pts := fun i hi =>
      pts_subset_of_isContainedIn (isContainedIn_of_mem_irreducibleComponents ℜ hℜ hC hi) hy
    obtain ⟨z, hz, hJ', K, hKz, -, hDy⟩ := exists_rsop_adapted_stalkIdeal_iSup hXns ℜ hℜ hE T hTy
    exact ⟨z, hz, hJ', K, hKz, (stalkIdeal_eq_of_mem_irreducibleComponents hXns ℜ hℜ hE hC hy).trans
      hDy⟩

theorem E_transform_castSucc (ℜ : DatumII.Raw X) {B : Subscheme X} (t : MonoidalTransformation X B)
    (j : Fin ℜ.α) :
    (ℜ.transform t).E (Fin.castSucc j) = Subscheme.strictTransform t (ℜ.E j) := by
  simp [DatumII.Raw.transform]

theorem E_transform_last (ℜ : DatumII.Raw X) {B : Subscheme X} (t : MonoidalTransformation X B) :
    (ℜ.transform t).E (Fin.last ℜ.α) = t.exceptional := by
  simp [DatumII.Raw.transform]

theorem a_transform_castSucc (ℜ : DatumII.Raw X) {B : Subscheme X}
    (t : MonoidalTransformation X B) (j : Fin ℜ.α) : (ℜ.transform t).a (Fin.castSucc j) = ℜ.a j := by
  simp [DatumII.Raw.transform]

open Classical in
theorem a_transform_last (ℜ : DatumII.Raw X) {B : Subscheme X} (t : MonoidalTransformation X B) :
    (ℜ.transform t).a (Fin.last ℜ.α) =
      (∑ i ∈ Finset.univ.filter fun i => B.IsContainedIn (ℜ.E i), ℜ.a i) + ℜ.nu.toNat - ℜ.b := by
  simp [DatumII.Raw.transform]

open Classical in
/-- The weight of a subscheme of `X'` for the transform: the old components contribute through
their strict transforms, and the new one `E_{α+1}` through `a_{α+1}`. -/
theorem weightOn_transform (ℜ : DatumII.Raw X) {B : Subscheme X} (t : MonoidalTransformation X B)
    (G : Subscheme t.X') :
    weightOn (ℜ.transform t) G =
      (∑ i ∈ Finset.univ.filter (fun i => G.IsContainedIn (Subscheme.strictTransform t (ℜ.E i))),
        ℜ.a i) +
      (if G.IsContainedIn t.exceptional then
        (∑ i ∈ Finset.univ.filter fun i => B.IsContainedIn (ℜ.E i), ℜ.a i) + ℜ.nu.toNat - ℜ.b
        else 0) := by
  unfold weightOn
  rw [Finset.sum_filter, Finset.sum_filter]
  change ∑ i : Fin (ℜ.α + 1), (if G.IsContainedIn ((ℜ.transform t).E i) then (ℜ.transform t).a i
    else 0) = _
  rw [Fin.sum_univ_castSucc]
  simp only [E_transform_castSucc, E_transform_last, a_transform_castSucc, a_transform_last]

open Classical in
/-- The index set `T_r` of `H ∈ K⁰_r(ℜ)`: the `E_i` containing `H` are exactly the `r` of
`T_r` (a member of `K⁰_r` lies in at most `r` of the `E_i`). -/
theorem filter_isContainedIn_eq_of_mem_K0 (hXns : X.IsNonsingular) (ℜ : DatumII.Raw X)
    (hℜ : ℜ.IsDatum) (hE : ∀ i j, i ≠ j → ℜ.E i ≠ Subscheme.empty → ℜ.E i ≠ ℜ.E j)
    {r : ℕ} {H : Subscheme X} (hH : H ∈ K0 ℜ r) {T : Finset (Fin ℜ.α)} (hcard : T.card = r)
    (hC : H ∈ (⨆ i ∈ T, ℜ.E i).irreducibleComponents) :
    Finset.univ.filter (fun i => H.IsContainedIn (ℜ.E i)) = T := by
  symm
  refine Finset.eq_of_subset_of_card_le (fun i hi => Finset.mem_filter.mpr
    ⟨Finset.mem_univ _, isContainedIn_of_mem_irreducibleComponents ℜ hℜ hC hi⟩) ?_
  rw [hcard]
  exact card_filter_isContainedIn_le_of_mem_K0 hXns ℜ hℜ hE hH

/-- The weights of the members of `K⁰_s(ℜ')` lying in the new component `E_{α+1} = f⁻¹(H)`
(the paper's (i) for `G' ⊆ E'_{α+1}` and (ii*), p. 313). -/
theorem weightOn_transform_lt_of_isContainedIn_exceptional [Hironaka.HironakaCitedResults.{u}] {N : ℕ} (hX : IsAmbient X N)
    (ℜ : DatumII.Raw X) (hℜ : ℜ.IsDatum) (hJ : ℜ.J = ⊤)
    (hE : ∀ i j, i ≠ j → ℜ.E i ≠ Subscheme.empty → ℜ.E i ≠ ℜ.E j) {r : ℕ} (hr : 1 ≤ r)
    (hbr : ℜ.b ≤ A ℜ r) (hmin : ∀ s, 1 ≤ s → s < r → A ℜ s < ℜ.b) {H : Subscheme X}
    (hH : H ∈ K ℜ r) (t : MonoidalTransformation X H) {s : ℕ} (hsr : s ≤ r)
    {G' : Subscheme t.X'} (hG' : G' ∈ K0 (ℜ.transform t) s)
    (hsub : G'.IsContainedIn t.exceptional) :
    (s < r → weightOn (ℜ.transform t) G' < ℜ.b) ∧ weightOn (ℜ.transform t) G' < A ℜ r := by
  classical
  obtain ⟨hXa, hXns, hXirr, -⟩ := id hX
  have hperm := isPermissible_of_mem_K hX ℜ hℜ hJ hE hbr hH
  obtain ⟨hX', hd'⟩ := (MonoidalSuccession.cons H t (MonoidalSuccession.nil t.X')).isAmbient_transformII
    hX ℜ hℜ ⟨hperm, trivial⟩
  have hℜ' : (ℜ.transform t).IsDatum := hd'
  obtain ⟨-, hE'⟩ := J_eq_top_and_distinct_transform ℜ hℜ hJ hE t
  have hU : ℜ.HasUnitJOnS := fun x _ => by rw [hJ]; exact Subscheme.stalkIdeal_top_eq x
  have hnu := DatumII.Raw.nu_eq_zero_of_hasUnitJOnS hU
  have hH0 := hH.1
  obtain ⟨hAH, hAH'⟩ : H ∈ K0 ℜ r ∧ A ℜ r = weightOn ℜ H := hH
  obtain ⟨-, -, Tr, hTrcard, hHC⟩ := hH0
  have hfilt := filter_isContainedIn_eq_of_mem_K0 hXns ℜ hℜ hE hAH hTrcard hHC
  have hAr : A ℜ r = ∑ i ∈ Tr, ℜ.a i := by
    rw [hAH']; unfold weightOn; rw [hfilt]
  -- the new coefficient
  have hlast : (∑ i ∈ Finset.univ.filter fun i => H.IsContainedIn (ℜ.E i), ℜ.a i) +
      ℜ.nu.toNat - ℜ.b = A ℜ r - ℜ.b := by
    rw [hnu, hAr, hfilt]; simp
  -- the `E_i ⊇ G'` among the old ones
  set U : Finset (Fin ℜ.α) := Finset.univ.filter
    (fun i => G'.IsContainedIn (Subscheme.strictTransform t (ℜ.E i))) with hUdef
  -- "Let `G'` be an irreducible component of `E'_{j_1} ∩ ⋯ ∩ E'_{j_{s-1}} ∩ E'_{α+1}`, where the `s`
  -- indices are necessarily distinct": `G' ∈ K⁰_s(ℜ')` is a component of `⋂_{i ∈ T'} E'_i`, `|T'| = s`,
  -- and the `E'_i ⊇ G'` are exactly those of `T'`; `E'_{α+1} ⊇ G'`, so `T' = {j_1, …, j_{s-1}, α+1}`
  obtain ⟨-, -, T', hT'card, hC'⟩ := id hG'
  have hfilt' := filter_isContainedIn_eq_of_mem_K0 hX'.2.1 (ℜ.transform t) hℜ' hE' hG' hT'card hC'
  have hfilt'' : Finset.univ.filter
      (fun i : Fin (ℜ.α + 1) => G'.IsContainedIn ((ℜ.transform t).E i)) =
      (T' : Finset (Fin (ℜ.α + 1))) := hfilt'
  have hT'eq : (T' : Finset (Fin (ℜ.α + 1))) =
      insert (Fin.last ℜ.α) (U.map Fin.castSuccEmb) := by
    rw [← hfilt'']
    ext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and, E_transform_last,
        Finset.mem_insert, true_or, iff_true]
      exact hsub
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and, E_transform_castSucc,
        Finset.mem_insert, Finset.mem_map, Fin.coe_castSuccEmb, hUdef,
        Fin.castSucc_ne_last, false_or]
      constructor
      · intro h; exact ⟨j, h, rfl⟩
      · rintro ⟨j', hj', hjj'⟩
        rw [← Fin.castSucc_injective _ hjj']
        exact hj'
  have hUcard : U.card + 1 = s := by
    have h1 : (insert (Fin.last ℜ.α) (U.map Fin.castSuccEmb) : Finset (Fin (ℜ.α + 1))).card =
        U.card + 1 := by
      rw [Finset.card_insert_of_notMem (by simp), Finset.card_map]
    have h2 : (insert (Fin.last ℜ.α) (U.map Fin.castSuccEmb) : Finset (Fin (ℜ.α + 1))).card =
        s := by
      rw [← hT'eq]; exact hT'card
    exact h1.symm.trans h2
  -- "The image `f(G')` is contained in `E_{j_1} ∩ ⋯ ∩ E_{j_{s-1}} ∩ H`" (p. 313)
  have hfH : ∀ z ∈ G'.pts, t.f.base z ∈ H.pts := fun z hz =>
    t.mem_pts_of_mem_exceptional (pts_subset_of_isContainedIn hsub hz)
  have hfU : ∀ z ∈ G'.pts, ∀ j ∈ U, t.f.base z ∈ (ℜ.E j).pts := fun z hz j hj =>
    t.pts_strictTransform_subset _ (pts_subset_of_isContainedIn (Finset.mem_filter.mp hj).2 hz)
  have hfTr : ∀ z ∈ G'.pts, ∀ i ∈ Tr, t.f.base z ∈ (ℜ.E i).pts := fun z hz i hi =>
    pts_subset_of_isContainedIn (isContainedIn_of_mem_irreducibleComponents ℜ hℜ hHC hi)
      (hfH z hz)
  -- "Take `i_a ∈ T_r` which is different from any of `j_1, …, j_{s-1}`"
  obtain ⟨i₀, hi₀Tr, hi₀U⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (s := U) (t := Tr) (by omega)
  -- `A_r - a_{i₀} < b`
  have hdrop : ∑ i ∈ Tr.erase i₀, ℜ.a i < ℜ.b := by
    by_cases h0 : (Tr.erase i₀).card = 0
    · rw [Finset.card_eq_zero.mp h0, Finset.sum_empty]
      exact hℜ.1
    · obtain ⟨x₀, hx₀⟩ := pts_nonempty_of_mem_K0 hAH
      obtain ⟨G₂, hG₂, hG₂sub⟩ := exists_mem_K0_of_forall_mem_pts hXns ℜ hℜ hE (Tr.erase i₀)
        (x := x₀) fun i hi => pts_subset_of_isContainedIn
          (isContainedIn_of_mem_irreducibleComponents ℜ hℜ hHC (Finset.mem_of_mem_erase hi)) hx₀
      have hc : (Tr.erase i₀).card = r - 1 := by rw [Finset.card_erase_of_mem hi₀Tr, hTrcard]
      have h1 : ∑ i ∈ Tr.erase i₀, ℜ.a i ≤ weightOn ℜ G₂ := by
        unfold weightOn
        exact Finset.sum_le_sum_of_subset fun i hi =>
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, hG₂sub i hi⟩
      have h2 := weightOn_le_A hG₂
      rw [hc] at h2
      have := hmin (r - 1) (by omega) (by omega)
      omega
  have hAr' : A ℜ r = ℜ.a i₀ + ∑ i ∈ Tr.erase i₀, ℜ.a i := by
    rw [hAr, Finset.add_sum_erase _ _ hi₀Tr]
  -- "Then `E_{j_1} ∩ ⋯ ∩ E_{j_{s-1}} ∩ E_{i_a}` has an irreducible component `G ∈ K⁰_s(ℜ)` containing
  -- `f(G')`", whence `a_{j_1} + ⋯ + a_{j_{s-1}} + a_{i_a} ≤ A_s(ℜ)`
  have : TopologicalSpace.NoetherianSpace X := IsAlgebraicScheme.noetherianSpace X
  obtain ⟨y, hy⟩ := pts_nonempty_of_mem_K0 hG'
  have hirrG' : _root_.IsIrreducible G'.pts :=
    Subscheme.isIrreducible_pts _ (isIrreducible_of_mem_K0 hG')
  have hirrC : _root_.IsIrreducible (closure (t.f.base '' G'.pts)) :=
    (hirrG'.image _ t.f.base.hom.continuous.continuousOn).closure
  let Bc : Subscheme X := Subscheme.ofClosed ⟨closure (t.f.base '' G'.pts), isClosed_closure⟩
  have hBc : Bc.pts = closure (t.f.base '' G'.pts) := Subscheme.pts_ofClosed _
  have hBcD : Bc.pts ⊆ (⨆ i ∈ insert i₀ U, ℜ.E i).pts := by
    rw [hBc, Subscheme.pts_iSup_finset]
    refine closure_minimal ?_ (isClosed_biInter fun i _ => (ℜ.E i).support.isClosed)
    rintro _ ⟨z, hz, rfl⟩
    simp only [Set.mem_iInter]
    intro i hi
    rcases Finset.mem_insert.mp hi with rfl | hi
    · exact hfTr z hz _ hi₀Tr
    · exact hfU z hz i hi
  obtain ⟨G, hGC, hGBc⟩ := Subscheme.exists_mem_irreducibleComponents_pts_subset
    (by rw [hBc]; exact hirrC)
    hBcD
  have hGne : G.pts.Nonempty :=
    ⟨t.f.base y, hGBc (by rw [hBc]; exact subset_closure ⟨y, hy, rfl⟩)⟩
  have hG : G ∈ K0 ℜ (insert i₀ U).card :=
    mem_K0_of_mem_irreducibleComponents hXns ℜ hℜ hE hGC hGne
  have hGsub : ∀ i ∈ insert i₀ U, G.IsContainedIn (ℜ.E i) := fun i hi =>
    isContainedIn_of_mem_irreducibleComponents ℜ hℜ hGC hi
  have hc2 : (insert i₀ U).card = U.card + 1 := Finset.card_insert_of_notMem hi₀U
  have hsum : ℜ.a i₀ + ∑ i ∈ U, ℜ.a i ≤ A ℜ (U.card + 1) := by
    have h1 : ℜ.a i₀ + ∑ i ∈ U, ℜ.a i = ∑ i ∈ insert i₀ U, ℜ.a i := (Finset.sum_insert hi₀U).symm
    have h2 : ∑ i ∈ insert i₀ U, ℜ.a i ≤ weightOn ℜ G := by
      unfold weightOn
      exact Finset.sum_le_sum_of_subset fun i hi =>
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, hGsub i hi⟩
    have h3 := weightOn_le_A hG
    rw [hc2] at h3
    omega
  -- the weight of `G'`
  have hW : weightOn (ℜ.transform t) G' = ∑ i ∈ U, ℜ.a i + (A ℜ r - ℜ.b) := by
    rw [weightOn_transform, ite_eq_left hsub, hlast]
  have hlt : weightOn (ℜ.transform t) G' < A ℜ (U.card + 1) := by
    rw [hW]
    omega
  have hm1 : 1 ≤ U.card + 1 := by omega
  refine ⟨fun hsr' => ?_, ?_⟩
  · exact hlt.trans (hmin _ hm1 (by omega))
  · rcases Nat.lt_or_ge (U.card + 1) r with hm | hm
    · exact hlt.trans_le ((hmin _ hm1 hm).le.trans hbr)
    · have : U.card + 1 = r := by omega
      rw [this] at hlt
      exact hlt

/-- For reduced subschemes, containment of the sets of points is containment of subschemes. -/
theorem isContainedIn_of_pts_subset_of_isReduced {V W : Subscheme X} (hV : V.IsReduced)
    (hW : W.IsReduced) (h : V.pts ⊆ W.pts) : V.IsContainedIn W := by
  rw [Subscheme.eq_ofClosed_support V hV, Subscheme.eq_ofClosed_support W hW]
  exact Subscheme.isContainedIn_ofClosed h

/-- The stalk at `y` of the reduced structure on `closure {y}` is the maximal ideal. -/
theorem stalkIdeal_ofClosed_closure_self (y : X) :
    (Subscheme.ofClosed ⟨closure {y}, isClosed_closure⟩).stalkIdeal y =
      maximalIdeal (X.presheaf.stalk y) := by
  obtain ⟨⟨U, hU⟩, hyU⟩ := Subscheme.exists_affineOpen_mem y
  replace hU : IsAffineOpen U := hU
  replace hyU : y ∈ U := hyU
  set q := hU.primeIdealOf ⟨y, hyU⟩
  have hq : hU.fromSpec q = y := hU.fromSpec_primeIdealOf ⟨y, hyU⟩
  have hst := Subscheme.compStalk_stalkIdeal_ofClosed_closure hU hyU q
  rw [hq] at hst
  rw [hst]
  let _ := TopCat.Presheaf.algebra_section_stalk X.presheaf (⟨y, hyU⟩ : U)
  have := hU.isLocalization_stalk ⟨y, hyU⟩
  exact IsLocalization.AtPrime.map_eq_maximalIdeal q.asIdeal (X.presheaf.stalk y)

/-- Two members of `K⁰_r(ℜ)`, one contained in the other, coincide (both are irreducible of
codimension `r`). -/
theorem eq_of_pts_subset_of_mem_K0 (ℜ : DatumII.Raw X) {r : ℕ} {H H' : Subscheme X}
    (hH : H ∈ K0 ℜ r) (hH' : H' ∈ K0 ℜ r) (hsub : H'.pts ⊆ H.pts) : H' = H := by
  have hirr := isIrreducible_of_mem_K0 hH
  have hirr' := isIrreducible_of_mem_K0 hH'
  obtain ⟨ζ, hζ⟩ := QuasiSober.sober (Subscheme.isIrreducible_pts H' hirr') H'.support.isClosed
  have hζH' : ζ ∈ H'.pts := hζ.mem
  have hζH : ζ ∈ H.pts := hsub hζH'
  have e : H' = Subscheme.ofClosed ⟨closure {ζ}, isClosed_closure⟩ := by
    rw [Subscheme.eq_ofClosed_support H' (Subscheme.isReduced_of_isNonsingular hH'.1)]
    congr 1
    exact TopologicalSpace.Closeds.ext hζ.def.symm
  have h1 : H'.stalkIdeal ζ = maximalIdeal (X.presheaf.stalk ζ) := by
    rw [e]; exact stalkIdeal_ofClosed_closure_self ζ
  have h2 : H.stalkIdeal ζ ≤ maximalIdeal (X.presheaf.stalk ζ) :=
    stalkIdeal_le_maximalIdeal_of_mem_pts H hζH
  have hpr := Subscheme.isPrime_stalkIdeal_of_isNonsingular_of_mem_pts H hH.1 hζH
  have hht := Subscheme.codim_eq_height H hH.1 hirr hζH
  have hht' := Subscheme.codim_eq_height H' hH'.1 hirr' hζH'
  rw [hH.2.1] at hht
  rw [hH'.2.1, h1] at hht'
  refine Subscheme.eq_of_stalkIdeal_eq_of_isIrreducible hH'.1 hirr' hH.1 hirr hζH' hζH ?_
  rw [h1]
  by_contra hne
  have hlt : H.stalkIdeal ζ < maximalIdeal (X.presheaf.stalk ζ) :=
    lt_of_le_of_ne h2 (fun h => hne h.symm)
  have hfin : (H.stalkIdeal ζ).FiniteHeight :=
    (H.stalkIdeal ζ).finiteHeight_iff.mpr (Or.inr (by rw [← hht]; exact ENat.natCast_ne_top r))
  have := Ideal.height_strict_mono_of_isPrime hlt
  rw [← hht, ← hht'] at this
  exact lt_irrefl _ this

/-- A subscheme of a noetherian scheme has only finitely many irreducible components. -/
theorem finite_irreducibleComponents [IsAlgebraicScheme X] (D : Subscheme X) :
    D.irreducibleComponents.Finite := by
  have := IsAlgebraicScheme.noetherianSpace X
  obtain ⟨S, hSf, hSc, hSi, hSU⟩ :=
    TopologicalSpace.NoetherianSpace.exists_finite_set_isClosed_irreducible D.support.isClosed
  refine (hSf.image fun u => Subscheme.ofClosed ⟨closure u, isClosed_closure⟩).subset ?_
  rintro C ⟨Z, ⟨⟨hZirr, hZsub⟩, hZmax⟩, rfl⟩
  have hZS : (Z : Set X) ⊆ ⋃₀ S := by
    rw [← hSU]; exact hZsub
  obtain ⟨u, huS, hZu⟩ := (isIrreducible_iff_sUnion_isClosed.mp hZirr) hSf.toFinset
    (fun t ht => hSc t (hSf.mem_toFinset.mp ht))
    (by simpa using hZS)
  have huS' : u ∈ S := hSf.mem_toFinset.mp huS
  have hsub : u ⊆ D.pts := by
    show u ⊆ (D.support : Set X)
    rw [hSU]; exact Set.subset_sUnion_of_mem huS'
  have hle : (⟨u, hSc u huS'⟩ : TopologicalSpace.Closeds X) ≤ Z :=
    hZmax (y := ⟨u, hSc u huS'⟩) ⟨hSi u huS', hsub⟩ hZu
  refine ⟨u, huS', ?_⟩
  have : (⟨closure u, isClosed_closure⟩ : TopologicalSpace.Closeds X) = Z := by
    refine TopologicalSpace.Closeds.ext ?_
    show closure u = (Z : Set X)
    rw [(hSc u huS').closure_eq]
    exact Set.Subset.antisymm hle hZu
  show Subscheme.ofClosed ⟨closure u, isClosed_closure⟩ = Subscheme.ofClosed Z
  rw [this]

theorem finite_K0 [IsAlgebraicScheme X] (ℜ : DatumII.Raw X) (r : ℕ) : (K0 ℜ r).Finite := by
  refine (Set.finite_iUnion fun T : Finset (Fin ℜ.α) =>
    finite_irreducibleComponents (⨆ i ∈ T, ℜ.E i)).subset ?_
  rintro H ⟨-, -, T, -, hC⟩
  exact Set.mem_iUnion.mpr ⟨T, hC⟩

/-- The reduced image `f(G'')` of a subscheme of `X'` (the closure of its image in `X`). -/
noncomputable def imageClosure {B : Subscheme X} (t : MonoidalTransformation X B)
    (G : Subscheme t.X') : Subscheme X :=
  Subscheme.ofClosed ⟨closure (t.f.base '' G.pts), isClosed_closure⟩

/-- The reduced strict preimage `closure (f⁻¹(G) − E)` of a subscheme of `X`. -/
noncomputable def strictPreimage {B : Subscheme X} (t : MonoidalTransformation X B)
    (G : Subscheme X) : Subscheme t.X' :=
  Subscheme.ofClosed ⟨closure (t.f.base ⁻¹' G.pts \ t.exceptional.pts), isClosed_closure⟩

/-- The weights of the reduced closure of a point `η'` off `E'_{α+1}` and of the reduced closure
of its image: the strict transforms `E'_i` contain `η'` exactly when `E_i` contains `f(η')`, and
`E'_{α+1}` does not contain it ("(iii*) `∑_{E'_i ⊇ G''} a_i = ∑_{E_i ⊇ f(G'')} a_i`", p. 313). -/
theorem weightOn_transform_ofClosed_closure (hXns : X.IsNonsingular) (ℜ : DatumII.Raw X)
    (hℜ : ℜ.IsDatum) {H : Subscheme X} (t : MonoidalTransformation X H) {η' : t.X'}
    (hη' : η' ∉ t.exceptional.pts) :
    weightOn (ℜ.transform t) (Subscheme.ofClosed ⟨closure {η'}, isClosed_closure⟩) =
      weightOn ℜ (Subscheme.ofClosed ⟨closure {t.f η'}, isClosed_closure⟩) := by
  classical
  rw [weightOn_transform, ite_eq_right_iff.mpr ?_, add_zero]
  · unfold weightOn
    refine Finset.sum_congr (Finset.filter_congr fun i _ => ?_) fun _ _ => rfl
    have hEi : (ℜ.E i).IsReduced :=
      Subscheme.isReduced_of_isNonsingular (hℜ.2.1 i).isNonsingular
    have hEi' : (Subscheme.strictTransform t (ℜ.E i)).IsReduced :=
      Subscheme.isReduced_of_isRadical_stalkIdeal fun y =>
        DatumTransform.isRadical_stalkIdeal_strictTransform hXns t hEi y
    have hG' := Subscheme.ofClosed_isReduced (⟨closure {η'}, isClosed_closure⟩ :
      TopologicalSpace.Closeds t.X')
    have hG := Subscheme.ofClosed_isReduced (⟨closure {t.f η'}, isClosed_closure⟩ :
      TopologicalSpace.Closeds X)
    constructor
    · intro h
      have h1 : η' ∈ (Subscheme.strictTransform t (ℜ.E i)).pts :=
        pts_subset_of_isContainedIn h (by rw [Subscheme.pts_ofClosed]; exact subset_closure rfl)
      have h2 := (t.mem_pts_strictTransform_iff_of_notMem (ℜ.E i) hη').mp h1
      exact isContainedIn_of_pts_subset_of_isReduced hG hEi (by
        rw [Subscheme.pts_ofClosed]
        exact closure_minimal (Set.singleton_subset_iff.mpr h2) (ℜ.E i).support.isClosed)
    · intro h
      have h1 : t.f η' ∈ (ℜ.E i).pts :=
        pts_subset_of_isContainedIn h (by rw [Subscheme.pts_ofClosed]; exact subset_closure rfl)
      have h2 := (t.mem_pts_strictTransform_iff_of_notMem (ℜ.E i) hη').mpr h1
      exact isContainedIn_of_pts_subset_of_isReduced hG' hEi' (by
        rw [Subscheme.pts_ofClosed]
        exact closure_minimal (Set.singleton_subset_iff.mpr h2)
          (Subscheme.strictTransform t (ℜ.E i)).support.isClosed)
  · intro h
    exfalso
    apply hη'
    have := pts_subset_of_isContainedIn h (show η' ∈ (Subscheme.ofClosed
      (⟨closure {η'}, isClosed_closure⟩ : TopologicalSpace.Closeds t.X')).pts by
        rw [Subscheme.pts_ofClosed]; exact subset_closure rfl)
    exact this

open Classical in
/-- The indices `castSucc j`, `j ∈ T'`, of the strict transforms `E'_j` among the components of
the transform. -/
def castSuccFinset (ℜ : DatumII.Raw X) {H : Subscheme X} (t : MonoidalTransformation X H)
    (T' : Finset (Fin ℜ.α)) : Finset (Fin (ℜ.transform t).α) :=
  T'.map Fin.castSuccEmb

theorem card_castSuccFinset (ℜ : DatumII.Raw X) {H : Subscheme X}
    (t : MonoidalTransformation X H) (T' : Finset (Fin ℜ.α)) :
    (castSuccFinset ℜ t T').card = T'.card := Finset.card_map _

theorem mem_castSuccFinset (ℜ : DatumII.Raw X) {H : Subscheme X}
    (t : MonoidalTransformation X H) (T' : Finset (Fin ℜ.α)) (i : Fin (ℜ.transform t).α) :
    i ∈ castSuccFinset ℜ t T' ↔ ∃ j ∈ T', Fin.castSucc j = i := by
  unfold castSuccFinset
  exact Finset.mem_map.trans Iff.rfl

/-- The strict preimage of the closure of `f(η')`. -/
theorem strictPreimage_ofClosed_closure {H : Subscheme X} (t : MonoidalTransformation X H)
    {η' : t.X'} (hη' : η' ∉ t.exceptional.pts) :
    strictPreimage t (Subscheme.ofClosed ⟨closure {t.f η'}, isClosed_closure⟩) =
      Subscheme.ofClosed ⟨closure {η'}, isClosed_closure⟩ := by
  unfold strictPreimage
  congr 1
  refine TopologicalSpace.Closeds.ext ?_
  show closure (t.f.base ⁻¹' (Subscheme.ofClosed
    (⟨closure {t.f η'}, isClosed_closure⟩ : TopologicalSpace.Closeds X)).pts \
      t.exceptional.pts) = closure {η'}
  rw [Subscheme.pts_ofClosed]
  exact MonoidalTransformation.closure_preimage_closure_sdiff_eq t hη'

/-- The points of the intersection of the strict transforms `E'_j`, `j ∈ T'`. -/
theorem pts_iSup_castSuccFinset (ℜ : DatumII.Raw X) {H : Subscheme X}
    (t : MonoidalTransformation X H) (T' : Finset (Fin ℜ.α)) :
    (⨆ i ∈ castSuccFinset ℜ t T', (ℜ.transform t).E i).pts =
      ⋂ j ∈ T', (Subscheme.strictTransform t (ℜ.E j)).pts := by
  rw [Subscheme.pts_iSup_finset]
  ext w
  simp only [Set.mem_iInter, mem_castSuccFinset]
  constructor
  · intro h j hj
    have := h (Fin.castSucc j) ⟨j, hj, rfl⟩
    rwa [E_transform_castSucc] at this
  · rintro h i ⟨j, hj, rfl⟩
    rw [E_transform_castSucc]
    exact h j hj

/-- A component of an intersection of components of `ℜ'` not contained in `E'_{α+1}` only involves
the strict transforms `E'_j`. -/
theorem exists_eq_castSuccFinset_of_mem_irreducibleComponents (ℜ : DatumII.Raw X)
    {H : Subscheme X} (t : MonoidalTransformation X H) (hℜ' : (ℜ.transform t).IsDatum)
    {T'' : Finset (Fin (ℜ.transform t).α)} {G'' : Subscheme t.X'}
    (hC : G'' ∈ (⨆ i ∈ T'', (ℜ.transform t).E i).irreducibleComponents)
    (hnot : ¬ G''.pts ⊆ t.exceptional.pts) :
    ∃ T' : Finset (Fin ℜ.α), T'' = castSuccFinset ℜ t T' := by
  classical
  have hlast : Fin.last ℜ.α ∉ T'' := fun hl => hnot (by
    have := isContainedIn_of_mem_irreducibleComponents (ℜ.transform t) hℜ' hC hl
    rw [show (ℜ.transform t).E (Fin.last ℜ.α) = t.exceptional from E_transform_last ℜ t] at this
    exact pts_subset_of_isContainedIn this)
  refine ⟨Finset.univ.filter fun i => Fin.castSucc i ∈ T'', ?_⟩
  ext i
  rw [mem_castSuccFinset]
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro hi
    obtain ⟨j, rfl⟩ := Fin.exists_castSucc_eq.mpr (fun h => hlast (h ▸ hi))
    exact ⟨j, hi, rfl⟩
  · rintro ⟨j, hj, rfl⟩
    exact hj

/-- Geometric fact used in (iii*) (p. 313: "`∑_{E'_i ⊇ G''} a_i = ∑_{E_i ⊇ f(G'')} a_i`, provided
`G'' ⊄ E'_{α+1}`", tacitly: `f(G'')` is again a member of `K⁰_s(ℜ)` not contained in `H`).
Off the exceptional subscheme `f` is an isomorphism over `X − H`, carrying the strict transforms
`E'_i` to the `E_i`; hence the components of `⋂ E'_i` not contained in `E'_{α+1}` correspond to
the components of `⋂ E_i` not contained in `H`. -/
theorem imageClosure_mem_K0_of_mem_K0_transform [Hironaka.HironakaCitedResults.{u}] {N : ℕ} (hX : IsAmbient X N)
    (ℜ : DatumII.Raw X) (hℜ : ℜ.IsDatum) (_hJ : ℜ.J = ⊤)
    (hE : ∀ i j, i ≠ j → ℜ.E i ≠ Subscheme.empty → ℜ.E i ≠ ℜ.E j) {H : Subscheme X}
    (hperm : ℜ.IsPermissible H) (t : MonoidalTransformation X H) {s : ℕ}
    {G'' : Subscheme t.X'} (hG'' : G'' ∈ K0 (ℜ.transform t) s)
    (hnot : ¬ G''.pts ⊆ t.exceptional.pts) :
    imageClosure t G'' ∈ K0 ℜ s ∧ ¬ (imageClosure t G'').pts ⊆ H.pts ∧
      weightOn ℜ (imageClosure t G'') = weightOn (ℜ.transform t) G'' ∧
      G''.pts = (strictPreimage t (imageClosure t G'')).pts := by
  classical
  obtain ⟨hXa, hXns, hXirr, -⟩ := id hX
  obtain ⟨hX', hd'⟩ := (MonoidalSuccession.cons H t (MonoidalSuccession.nil t.X')).isAmbient_transformII
    hX ℜ hℜ ⟨hperm, trivial⟩
  have hℜ' : (ℜ.transform t).IsDatum := hd'
  obtain ⟨-, -, T'', hcard, hC⟩ := hG''
  obtain ⟨T', rfl⟩ := exists_eq_castSuccFinset_of_mem_irreducibleComponents ℜ t hℜ' hC hnot
  have hcardT' : T'.card = s := by rw [← hcard, card_castSuccFinset]
  have hD' := pts_iSup_castSuccFinset ℜ t T'
  have hD := Subscheme.pts_iSup_finset T' ℜ.E
  rw [Subscheme.mem_irreducibleComponents_iff_exists_isMinimalPoint] at hC
  obtain ⟨η', hmin', hG⟩ := hC
  subst hG
  have hη' : η' ∉ t.exceptional.pts := fun hη => hnot (by
    rw [Subscheme.pts_ofClosed]
    exact closure_minimal (Set.singleton_subset_iff.mpr hη) t.exceptional.support.isClosed)
  have hmin : IsMinimalPoint (⨆ j ∈ T', ℜ.E j).pts (t.f η') := by
    refine (t.isMinimalPoint_iff_of_notMem_exceptional ?_ hη').mp hmin'
    intro w hw
    rw [hD', hD]
    simp only [Set.mem_iInter]
    exact forall₂_congr fun j _ => t.mem_pts_strictTransform_iff_of_notMem (ℜ.E j) hw
  have himg : imageClosure t (Subscheme.ofClosed ⟨closure {η'}, isClosed_closure⟩) =
      Subscheme.ofClosed ⟨closure {t.f η'}, isClosed_closure⟩ := by
    unfold imageClosure
    congr 1
    refine TopologicalSpace.Closeds.ext ?_
    show closure (t.f.base '' (Subscheme.ofClosed
      (⟨closure {η'}, isClosed_closure⟩ : TopologicalSpace.Closeds t.X')).pts) =
        closure {t.f η'}
    rw [Subscheme.pts_ofClosed]
    refine Set.Subset.antisymm (closure_minimal ?_ isClosed_closure)
      (closure_mono (Set.singleton_subset_iff.mpr ⟨η', subset_closure rfl, rfl⟩))
    refine (image_closure_subset_closure_image t.f.base.hom.continuous).trans ?_
    rw [Set.image_singleton]
  have hGim : Subscheme.ofClosed ⟨closure {t.f η'}, isClosed_closure⟩ ∈
      (⨆ j ∈ T', ℜ.E j).irreducibleComponents :=
    (Subscheme.mem_irreducibleComponents_iff_exists_isMinimalPoint _ _).mpr ⟨_, hmin, rfl⟩
  have hK0 := mem_K0_of_mem_irreducibleComponents hXns ℜ hℜ hE hGim
    ⟨t.f η', by rw [Subscheme.pts_ofClosed]; exact subset_closure rfl⟩
  rw [hcardT'] at hK0
  rw [himg]
  refine ⟨hK0, ?_, ?_, ?_⟩
  · intro hsub
    apply hη'
    have : t.f η' ∈ H.pts := hsub (by rw [Subscheme.pts_ofClosed]; exact subset_closure rfl)
    rwa [MonoidalTransformation.pts_exceptional]
  · exact (weightOn_transform_ofClosed_closure hXns ℜ hℜ t hη').symm
  · rw [strictPreimage_ofClosed_closure t hη']

/-- The converse of `imageClosure_mem_K0_of_mem_K0_transform`: a member of `K⁰_s(ℜ)` not
contained in `H` lifts to a member of `K⁰_s(ℜ')` not contained in `E'_{α+1}` with the same weight
(used tacitly in (iii): "`A_r(ℜ') = A_r(ℜ)`"). -/
theorem strictPreimage_mem_K0_transform_of_mem_K0 [Hironaka.HironakaCitedResults.{u}] {N : ℕ} (hX : IsAmbient X N)
    (ℜ : DatumII.Raw X) (hℜ : ℜ.IsDatum) (hJ : ℜ.J = ⊤)
    (hE : ∀ i j, i ≠ j → ℜ.E i ≠ Subscheme.empty → ℜ.E i ≠ ℜ.E j) {H : Subscheme X}
    (hperm : ℜ.IsPermissible H) (t : MonoidalTransformation X H) {s : ℕ} {G : Subscheme X}
    (hG : G ∈ K0 ℜ s) (hnot : ¬ G.pts ⊆ H.pts) :
    strictPreimage t G ∈ K0 (ℜ.transform t) s ∧
      ¬ (strictPreimage t G).pts ⊆ t.exceptional.pts ∧
      weightOn (ℜ.transform t) (strictPreimage t G) = weightOn ℜ G := by
  classical
  obtain ⟨hXa, hXns, hXirr, -⟩ := id hX
  obtain ⟨hX', hd'⟩ := (MonoidalSuccession.cons H t (MonoidalSuccession.nil t.X')).isAmbient_transformII
    hX ℜ hℜ ⟨hperm, trivial⟩
  have hℜ' : (ℜ.transform t).IsDatum := hd'
  obtain ⟨hJ', hE'⟩ := J_eq_top_and_distinct_transform ℜ hℜ hJ hE t
  obtain ⟨-, -, T, hcard, hC⟩ := hG
  have hD' := pts_iSup_castSuccFinset ℜ t T
  have hD := Subscheme.pts_iSup_finset T ℜ.E
  rw [Subscheme.mem_irreducibleComponents_iff_exists_isMinimalPoint] at hC
  obtain ⟨η, hmin, hGeq⟩ := hC
  subst hGeq
  have hηH : η ∉ H.pts := fun hη => hnot (by
    rw [Subscheme.pts_ofClosed]
    exact closure_minimal (Set.singleton_subset_iff.mpr hη) H.support.isClosed)
  obtain ⟨η', rfl⟩ := t.exists_apply_eq_of_notMem hηH
  have hη' : η' ∉ t.exceptional.pts := by
    rw [MonoidalTransformation.pts_exceptional]; exact hηH
  have hmin' : IsMinimalPoint (⨆ i ∈ castSuccFinset ℜ t T, (ℜ.transform t).E i).pts η' := by
    refine (t.isMinimalPoint_iff_of_notMem_exceptional ?_ hη').mpr hmin
    intro w hw
    rw [hD', hD]
    simp only [Set.mem_iInter]
    exact forall₂_congr fun j _ => t.mem_pts_strictTransform_iff_of_notMem (ℜ.E j) hw
  have hpre := strictPreimage_ofClosed_closure t hη'
  have hGim : Subscheme.ofClosed ⟨closure {η'}, isClosed_closure⟩ ∈
      (⨆ i ∈ castSuccFinset ℜ t T, (ℜ.transform t).E i).irreducibleComponents :=
    (Subscheme.mem_irreducibleComponents_iff_exists_isMinimalPoint _ _).mpr ⟨_, hmin', rfl⟩
  have hK0 := mem_K0_of_mem_irreducibleComponents hX'.2.1 (ℜ.transform t) hℜ' hE' hGim
    ⟨η', by rw [Subscheme.pts_ofClosed]; exact subset_closure rfl⟩
  rw [card_castSuccFinset, hcard] at hK0
  rw [hpre]
  refine ⟨hK0, ?_, ?_⟩
  · intro hsub
    apply hη'
    exact hsub (by rw [Subscheme.pts_ofClosed]; exact subset_closure rfl)
  · exact weightOn_transform_ofClosed_closure hXns ℜ hℜ t hη'

theorem A_le_of_forall_le {ℜ : DatumII.Raw X} {s c : ℕ} (h : ∀ G ∈ K0 ℜ s, weightOn ℜ G ≤ c) :
    A ℜ s ≤ c := by
  unfold A
  refine csSup_le' ?_
  rintro _ ⟨G, hG, rfl⟩
  exact h G hG

/-- The claims (i)–(iii) in the proof of Lemma (D.1) (pp. 312–313), in the reduced situation of
that proof: `J = O_X` (the ideal sheaf `⊤`) and `E_i ≠ E_j` for `i ≠ j` whenever `E_i` is not
empty.

Deviation from the paper (gap filled): "It is clear that `f_H` is permissible" is proved
(`CD.isPermissible_of_mem_K`); "(iii*) is clear" hides the correspondence of the members of
`K⁰_s(ℜ')` not contained in `E'_{α+1}` with those of `K⁰_s(ℜ)` not contained in `H`, which is proved
(`CD.imageClosure_mem_K0_of_mem_K0_transform`, `CD.strictPreimage_mem_K0_transform_of_mem_K0`).
As printed (p. 313), for (i) and (ii*): "Let `G'` be an irreducible component of
`E'_{j₁} ∩ … ∩ E'_{j_{s-1}} ∩ E'_{α+1}`, where the `s` indices are necessarily distinct" is the
description of `G' ∈ K⁰_s(ℜ')` with `G' ⊆ E'_{α+1}`: it is a component of `⋂_{i ∈ T'} E'_i`, `|T'| = s`,
and the `E'_i ⊇ G'` are exactly those of `T'` (`CD.filter_isContainedIn_eq_of_mem_K0`), so
`T' = {j₁, …, j_{s-1}, α+1}`; "Then `E_{j₁} ∩ … ∩ E_{j_{s-1}} ∩ E_{i_a}` has an irreducible component
`G ∈ K⁰_s(ℜ)` containing `f(G')`" is proved with `G` a component containing the closure of `f(G')`
(`Subscheme.exists_mem_irreducibleComponents_pts_subset`, `CD.mem_K0_of_mem_irreducibleComponents`);
"it contains a subscheme which belongs to `K_{r-1}(ℜ)`" is a component of `⋂_{i ≠ i_a} E_i`
through a point of `H` (`CD.exists_mem_K0_of_forall_mem_pts`).  The paper has a misprint `K` for `K⁰`. -/
@[blueprint "lem:IV.D-1-claim"
  (statement := /-- In the proof of Lemma (D.1) (\cref{lem:IV.D-1}), suppose $J=\mathcal O_X$
    and $E_i\ne E_j$ if $i\ne j$ and $E_i$ is not empty. Let $r$ be the smallest integer
    (positive) such that $A_r(\mathfrak R)\ge b$, so that $A_s(\mathfrak R)<b$ for $1\le s<r$
    (\cref{def:IV.D-1-symbols}). Let $H$ be any one of the subschemes in $K_r(\mathfrak R)$. It
    is clear that the monoidal transformation $f_H\colon X'\to X$ with center $H$ is permissible
    for $\mathfrak R$. Let $\mathfrak R'=f_H^*(\mathfrak R)$. Then we claim that (i)
    $A_s(\mathfrak R')<b$ for $1\le s<r$ (which is trivial if $r=1$), (ii) if $K_r(\mathfrak R)$
    consists of only $H$, then $A_r(\mathfrak R')<A_r(\mathfrak R)$, and (iii) if
    $K_r(\mathfrak R)$ contains subschemes other than $H$ then $A_r(\mathfrak R')=
    A_r(\mathfrak R)$ and $k_r(\mathfrak R')<k_r(\mathfrak R)$. (pp.~312--313.) -/)
  (proof := /-- (p.~313.) Take $T_r=\{i_1,\dots,i_r\}$ such that $H$ is an irreducible
    component of $\bigcap_{i\in T_r}E_i$; then $A_r(\mathfrak R)=a_{i_1}+\dots+a_{i_r}$. Let
    $E_i'$ be the strict transform of $E_i$ $(1\le i\le\alpha)$ on $X'$ and $E'_{\alpha+1}$ the
    total transform of $H$. In case $r=1$, $H=E_{i_1}$, $E'_{i_1}$ is empty and
    $\mathfrak R'=(E'_1,\dots,\emptyset,\dots,E'_{\alpha+1}\,|\,\mathcal O_{X'},b\,|\,a_1,\dots,
    a_{i_1},\dots,a_{i_1}-b)$ with $a_{i_1}-b=A_1(\mathfrak R)-b<A_1(\mathfrak R)$. If $r>1$,
    $\mathfrak R'=(E_1',\dots,E_\alpha',E'_{\alpha+1}\,|\,\mathcal O_{X'},b\,|\,a_1,\dots,a_\alpha,
    a_{\alpha+1})$ with $a_{\alpha+1}=A_r(\mathfrak R)-b$. (i): let $G'\in K_s(\mathfrak R')$,
    $1\le s<r$; this is clear if $G'\not\subseteq E'_{\alpha+1}$. If $G'\subseteq
    E'_{\alpha+1}$, $G'$ is a component of $E'_{j_1}\cap\dots\cap E'_{j_{s-1}}\cap E'_{\alpha+1}$
    and $f(G')\subseteq E_{j_1}\cap\dots\cap E_{j_{s-1}}\cap H$; taking $i_a\in T_r$ different
    from the $j$'s, $E_{j_1}\cap\dots\cap E_{j_{s-1}}\cap E_{i_a}$ has a component
    $G\in K_s(\mathfrak R)$ containing $f(G')$, so $a_{j_1}+\dots+a_{j_{s-1}}+a_{i_a}\le
    A_s(\mathfrak R)<b$; and
    $\bigcap_{i_a\ne i\in T_r}E_i\supseteq H$ contains a member of $K_{r-1}(\mathfrak R)$, so
    $A_r(\mathfrak R)-a_{i_a}\le A_{r-1}(\mathfrak R)<b$, i.e.\ $a_{\alpha+1}<a_{i_a}$. ``Combing''
    [sic] these, $\sum_{E_i'\supseteq G'}a_i=a_{j_1}+\dots+a_{j_{s-1}}+a_{\alpha+1}<b$ (the paper
    indexes this sum by $E'_t$ [sic]). (ii), (iii): it suffices that for $G''\in
    K_r(\mathfrak R')$, (ii*) $\sum_{E_i'\supseteq G''}a_i<A_r(\mathfrak R)$ provided
    $G''\subset E'_{\alpha+1}$, and (iii*) $\sum_{E_i'\supseteq G''}a_i=
    \sum_{E_i\supseteq f(G'')}a_i$ provided $G''\not\subset E'_{\alpha+1}$. (iii*) is clear; for
    (ii*), as above there is $i_a\in T_r$ with $a_{j_1}+\dots+a_{j_{r-1}}+a_{i_a}\le
    A_r(\mathfrak R)$ (the paper prints the first index as $j$ [sic]), and
    $a_{\alpha+1}<a_{i_a}$ gives the assertion. \textsc{q.e.d.}

    \textbf{Paper misprint.} In this proof (p.~313) the paper takes the auxiliary components
    from $K_s(\mathfrak R)$, $K_{r-1}(\mathfrak R)$ and $K_r(\mathfrak R)$ (``has an irreducible
    component $G\in K_s(\mathfrak R)$ containing $f(G')$'', ``it contains a subscheme of $X$
    which belongs to $K_{r-1}(\mathfrak R)$'', ``it has an irreducible component belonging to
    $K_r(\mathfrak R)$''); meant are $K^0_s(\mathfrak R)$, $K^0_{r-1}(\mathfrak R)$ and
    $K^0_r(\mathfrak R)$: such a component need not realize the maximum, and only its membership
    in $K^0$ is used, for the inequalities $\le A_s(\mathfrak R)$, $\le A_{r-1}(\mathfrak R)$,
    $\le A_r(\mathfrak R)$. The other slips are marked [sic] above.

    \textbf{Deviation from the paper (gap filled).} (a) ``It is clear that the monoidal
    transformation $f_H$ is permissible'' is proved: $H\in K^0_r$ is non-singular and irreducible,
    lies in $S(\mathfrak R)=S_*(\mathfrak R)$ because $\nu(\mathfrak R)=0$ and $A_r\ge b$, and has
    normal crossings with the $E_i$ (the stalk of $H$ is generated by part of the regular system
    of parameters adapted to $\bigcup E_i$). (b) ``$A_r(\mathfrak R)=a_{i_1}+\dots+a_{i_r}$'' uses
    that the $E_i\supseteq H$ are exactly those of $T_r$: a member of $K^0_s$ lies in at most $s$
    of the $E_i$ (the heights of the stalks). (c) ``(iii*) is clear'' hides these correspondences,
    which are proved: for $G''\in K^0_s(\mathfrak R')$ with $G''\not\subseteq E'_{\alpha+1}$ the
    reduced closure of $f(G'')$ is a member of $K^0_s(\mathfrak R)$ not contained in $H$ with the
    same weight $\sum_{E_i\supseteq f(G'')}a_i=\sum_{E'_i\supseteq G''}a_i$, and $G''$ is
    recovered as the closure of $f^{-1}(f(G''))-E'_{\alpha+1}$; conversely every member of
    $K^0_s(\mathfrak R)$ not contained in $H$ lifts to one of $K^0_s(\mathfrak R')$ with the same
    weight. This is used for $A_r(\mathfrak R')\ge A_r(\mathfrak R)$ in (iii) (a member of
    $K_r(\mathfrak R)$ other than $H$ is not contained in $H$) and for the injectivity behind
    $k_r(\mathfrak R')<k_r(\mathfrak R)$. The proof is that $f$ is an isomorphism over $X-H$
    (\cref{def:strict-transform}), so that points without proper generization in the
    intersections of the $E_i$ resp.\ of the $E'_i$ correspond.

    \textbf{Gap filled.} (d) ``$G'$ is an irreducible component of $E'_{j_1}\cap\dots\cap
    E'_{j_{s-1}}\cap E'_{\alpha+1}$, where the $s$ indices are necessarily distinct'': $G'\in
    K^0_s(\mathfrak R')$ is a component of $\bigcap_{i\in T'}E'_i$ with $|T'|=s$, and the $E'_i$
    containing $G'$ are exactly those with $i\in T'$ (their stalks are generated by distinct members
    of a regular system of parameters, so there are at most $s$ of them); since $G'\subseteq
    E'_{\alpha+1}$, $T'=\{j_1,\dots,j_{s-1},\alpha+1\}$. (e) ``$E_{j_1}\cap\dots\cap E_{i_a}$ has an
    irreducible component $G\in K^0_s(\mathfrak R)$ containing $f(G')$'': the closure of $f(G')$ is
    irreducible and lies in this intersection, hence in an irreducible component $G$, which belongs
    to $K^0_s(\mathfrak R)$; the member of $K^0_{r-1}(\mathfrak R)$ in $\bigcap_{i\ne i_a}E_i$ is a
    component of this (non-empty) intersection through a point of $H$. -/)
  (latexEnv := "lemma")]
theorem isPermissible_and_A_transform_lt_and_k_transform_lt_of_mem_K [Hironaka.HironakaCitedResults.{u}] (N : ℕ) (hX : IsAmbient X N) (ℜ : DatumII.Raw X) (hℜ : ℜ.IsDatum)
    (hJ : ℜ.J = ⊤)
    (hE : ∀ i j, i ≠ j → ℜ.E i ≠ Subscheme.empty → ℜ.E i ≠ ℜ.E j)
    (r : ℕ) (hr : 0 < r) (hbr : ℜ.b ≤ A ℜ r) (hmin : ∀ s, 1 ≤ s → s < r → A ℜ s < ℜ.b)
    (H : Subscheme X) (hH : H ∈ K ℜ r) (t : MonoidalTransformation X H) :
    ℜ.IsPermissible H ∧
    (∀ s, 1 ≤ s → s < r → A (ℜ.transform t) s < ℜ.b) ∧
    (K ℜ r = {H} → A (ℜ.transform t) r < A ℜ r) ∧
    ((∃ H' ∈ K ℜ r, H' ≠ H) →
      A (ℜ.transform t) r = A ℜ r ∧ k (ℜ.transform t) r < k ℜ r) := by
  classical
  obtain ⟨hXa, hXns, hXirr, -⟩ := id hX
  have hr1 : 1 ≤ r := hr
  have hperm := isPermissible_of_mem_K hX ℜ hℜ hJ hE hbr hH
  have hH0 : H ∈ K0 ℜ r := hH.1
  have hAH : A ℜ r = weightOn ℜ H := hH.2
  have hbpos : 0 < ℜ.b := hℜ.1
  obtain ⟨hX', hd'⟩ := (MonoidalSuccession.cons H t (MonoidalSuccession.nil t.X')).isAmbient_transformII
    hX ℜ hℜ ⟨hperm, trivial⟩
  have hexcRed : t.exceptional.IsReduced := Subscheme.isReduced_of_isNonsingular
    (MonoidalTransformation.exceptional_isNonsingular_and_totalTransform_le_pow hXns
      (isIrreducible_of_mem_K0 hH0) hH0.1 t Subscheme.empty).1.1
  -- off `E'_{α+1}`: transport to `X`; on `E'_{α+1}`: the bound of the paper
  have hoff : ∀ {s : ℕ} {G'' : Subscheme t.X'}, G'' ∈ K0 (ℜ.transform t) s →
      ¬ G''.pts ⊆ t.exceptional.pts → ∃ G ∈ K0 ℜ s, ¬ G.pts ⊆ H.pts ∧
        weightOn ℜ G = weightOn (ℜ.transform t) G'' := fun hG'' hnot => by
    obtain ⟨h1, h2, h3, -⟩ := imageClosure_mem_K0_of_mem_K0_transform hX ℜ hℜ hJ hE hperm t hG'' hnot
    exact ⟨_, h1, h2, h3⟩
  have hon : ∀ {s : ℕ} {G'' : Subscheme t.X'}, 1 ≤ s → s ≤ r → G'' ∈ K0 (ℜ.transform t) s →
      G''.pts ⊆ t.exceptional.pts →
      (s < r → weightOn (ℜ.transform t) G'' < ℜ.b) ∧ weightOn (ℜ.transform t) G'' < A ℜ r :=
    fun hs1 hsr hG'' hsub => weightOn_transform_lt_of_isContainedIn_exceptional hX ℜ hℜ hJ hE hr1
      hbr hmin hH t hsr hG''
      (isContainedIn_of_pts_subset_of_isReduced (Subscheme.isReduced_of_isNonsingular hG''.1)
        hexcRed hsub)
  refine ⟨hperm, ?_, ?_, ?_⟩
  · -- (i)
    intro s hs1 hsr
    refine A_lt_of_forall_lt hbpos fun G'' hG'' => ?_
    by_cases hsub : G''.pts ⊆ t.exceptional.pts
    · exact (hon hs1 hsr.le hG'' hsub).1 hsr
    · obtain ⟨G, hG, -, hw⟩ := hoff hG'' hsub
      rw [← hw]
      exact (weightOn_le_A hG).trans_lt (hmin s hs1 hsr)
  · -- (ii)
    intro hK
    refine A_lt_of_forall_lt (lt_of_lt_of_le hbpos hbr) fun G'' hG'' => ?_
    by_cases hsub : G''.pts ⊆ t.exceptional.pts
    · exact (hon hr1 le_rfl hG'' hsub).2
    · obtain ⟨G, hG, hGH, hw⟩ := hoff hG'' hsub
      rw [← hw]
      refine lt_of_le_of_ne (weightOn_le_A hG) fun heq => ?_
      have : G ∈ K ℜ r := ⟨hG, heq.symm⟩
      rw [hK] at this
      exact hGH (by rw [Set.mem_singleton_iff.mp this])
  · -- (iii)
    rintro ⟨H', hH'K, hne⟩
    have hle : ∀ G'' ∈ K0 (ℜ.transform t) r, weightOn (ℜ.transform t) G'' ≤ A ℜ r := by
      intro G'' hG''
      by_cases hsub : G''.pts ⊆ t.exceptional.pts
      · exact (hon hr1 le_rfl hG'' hsub).2.le
      · obtain ⟨G, hG, -, hw⟩ := hoff hG'' hsub
        rw [← hw]
        exact weightOn_le_A hG
    have hA1 : A (ℜ.transform t) r ≤ A ℜ r := A_le_of_forall_le hle
    have hH'0 : H' ∈ K0 ℜ r := hH'K.1
    have hH'not : ¬ H'.pts ⊆ H.pts := fun hsub => hne (eq_of_pts_subset_of_mem_K0 ℜ hH0 hH'0 hsub)
    obtain ⟨hG1, hG2, hG3⟩ := strictPreimage_mem_K0_transform_of_mem_K0 hX ℜ hℜ hJ hE hperm t
      hH'0 hH'not
    have hA2 : A ℜ r ≤ A (ℜ.transform t) r := by
      have := weightOn_le_A hG1
      rw [hG3, ← hH'K.2] at this
      exact this
    have hAeq : A (ℜ.transform t) r = A ℜ r := le_antisymm hA1 hA2
    refine ⟨hAeq, ?_⟩
    -- `k_r(ℜ') < k_r(ℜ)`: `G'' ↦ f(G'')` embeds `K_r(ℜ')` into `K_r(ℜ) ∖ {H}`
    have hK'sub : ∀ G'' ∈ K (ℜ.transform t) r, ¬ G''.pts ⊆ t.exceptional.pts ∧
        imageClosure t G'' ∈ K ℜ r ∧ imageClosure t G'' ≠ H := by
      intro G'' hG''
      have hw : A (ℜ.transform t) r = weightOn (ℜ.transform t) G'' := hG''.2
      have hnot : ¬ G''.pts ⊆ t.exceptional.pts := fun hsub => by
        have := (hon hr1 le_rfl hG''.1 hsub).2
        rw [← hw, hAeq] at this
        exact lt_irrefl _ this
      obtain ⟨h1, h2, h3, -⟩ := imageClosure_mem_K0_of_mem_K0_transform hX ℜ hℜ hJ hE hperm t
        hG''.1 hnot
      refine ⟨hnot, ⟨h1, ?_⟩, fun heq => h2 (by rw [heq])⟩
      rw [h3, ← hw, hAeq]
    have hinj : Set.InjOn (imageClosure t) (K (ℜ.transform t) r) := by
      intro G₁ hG₁ G₂ hG₂ heq
      obtain ⟨hn₁, -⟩ := hK'sub G₁ hG₁
      obtain ⟨hn₂, -⟩ := hK'sub G₂ hG₂
      obtain ⟨-, -, -, hp₁⟩ := imageClosure_mem_K0_of_mem_K0_transform hX ℜ hℜ hJ hE hperm t
        hG₁.1 hn₁
      obtain ⟨-, -, -, hp₂⟩ := imageClosure_mem_K0_of_mem_K0_transform hX ℜ hℜ hJ hE hperm t
        hG₂.1 hn₂
      have hpts : G₁.pts = G₂.pts := by rw [hp₁, hp₂, heq]
      rw [Subscheme.eq_ofClosed_support G₁ (Subscheme.isReduced_of_isNonsingular hG₁.1.1),
        Subscheme.eq_ofClosed_support G₂ (Subscheme.isReduced_of_isNonsingular hG₂.1.1)]
      congr 1
      exact TopologicalSpace.Closeds.ext hpts
    have hfin : (K ℜ r).Finite := (finite_K0 ℜ r).subset fun G hG => hG.1
    have hss : imageClosure t '' K (ℜ.transform t) r ⊂ K ℜ r := by
      refine ⟨?_, fun hsup => ?_⟩
      · rintro _ ⟨G'', hG'', rfl⟩
        exact (hK'sub G'' hG'').2.1
      · obtain ⟨G'', hG'', hGH⟩ := hsup hH
        exact (hK'sub G'' hG'').2.2 hGH
    unfold k
    calc (K (ℜ.transform t) r).ncard = (imageClosure t '' K (ℜ.transform t) r).ncard :=
          (hinj.ncard_image).symm
      _ < (K ℜ r).ncard := Set.ncard_lt_ncard hss hfin

end CD

namespace CD

variable {X : Scheme.{u}}

/-- Lemma (D.1) in the reduced situation of the paper's proof (`J = O_X`, the non-empty `E_i`
distinct): induction on `(N - r, A_r, k_r)` in the lexicographic order, `r` the least positive
integer with `A_r ≥ b`. -/
theorem exists_isPermissibleII_S_eq_empty_of_J_eq_top_of_distinct [Hironaka.HironakaCitedResults.{u}] {N : ℕ} :
    ∀ (X : Scheme.{u}), IsAmbient X N → ∀ (ℜ : DatumII.Raw X), ℜ.IsDatum → ℜ.J = ⊤ →
      (∀ i j, i ≠ j → ℜ.E i ≠ Subscheme.empty → ℜ.E i ≠ ℜ.E j) →
      ∃ (Y : Scheme.{u}) (g : MonoidalSuccession X Y),
        g.IsPermissibleII ℜ ∧ (g.transformII ℜ).S = ∅ := by
  classical
  have key : ∀ m : ℕ ×ₗ (ℕ ×ₗ ℕ), ∀ (X : Scheme.{u}), IsAmbient X N → ∀ (ℜ : DatumII.Raw X),
      ℜ.IsDatum → ℜ.J = ⊤ →
      (∀ i j, i ≠ j → ℜ.E i ≠ Subscheme.empty → ℜ.E i ≠ ℜ.E j) →
      ∀ r, 1 ≤ r → ℜ.b ≤ A ℜ r → (∀ s, 1 ≤ s → s < r → A ℜ s < ℜ.b) →
      toLex (N - r, toLex (A ℜ r, k ℜ r)) = m →
      ∃ (Y : Scheme.{u}) (g : MonoidalSuccession X Y),
        g.IsPermissibleII ℜ ∧ (g.transformII ℜ).S = ∅ := by
    intro m
    induction m using WellFoundedLT.induction with
    | _ m ih =>
    intro X hX ℜ hℜ hJ hE r hr hbr hmin hm
    have hdim : X.dim = (N : WithBot ℕ∞) := hX.2.2.2
    have hbpos : 0 < ℜ.b := hℜ.1
    have hApos : 0 < A ℜ r := lt_of_lt_of_le hbpos hbr
    obtain ⟨H, hH0, hHw⟩ : ∃ H ∈ K0 ℜ r, weightOn ℜ H = A ℜ r := by
      have hne : (weightOn ℜ '' K0 ℜ r).Nonempty := by
        by_contra hne
        rw [Set.not_nonempty_iff_eq_empty] at hne
        unfold A at hApos
        rw [hne] at hApos
        simp at hApos
      have hbdd : BddAbove (weightOn ℜ '' K0 ℜ r) := ⟨∑ i, ℜ.a i, by
        rintro _ ⟨H, -, rfl⟩
        unfold weightOn
        exact Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)⟩
      obtain ⟨H, hH, h⟩ := Nat.sSup_mem hne hbdd
      exact ⟨H, hH, h⟩
    have hH : H ∈ K ℜ r := ⟨hH0, hHw.symm⟩
    obtain ⟨t, -⟩ := MonoidalTransformation.exists_isProper X H
    obtain ⟨hperm, hi, hii, hiii⟩ :=
      isPermissible_and_A_transform_lt_and_k_transform_lt_of_mem_K N hX ℜ hℜ hJ hE r hr hbr hmin
        H hH t
    obtain ⟨hX', hd⟩ := (MonoidalSuccession.cons H t (MonoidalSuccession.nil t.X')).isAmbient_transformII
      hX ℜ hℜ ⟨hperm, trivial⟩
    have hd' : (ℜ.transform t).IsDatum := hd
    obtain ⟨hJ', hE'⟩ := J_eq_top_and_distinct_transform ℜ hℜ hJ hE t
    by_cases hS' : (ℜ.transform t).S = ∅
    · exact ⟨t.X', MonoidalSuccession.cons H t (MonoidalSuccession.nil _), ⟨hperm, trivial⟩, hS'⟩
    · have hex : ∃ r', 1 ≤ r' ∧ (ℜ.transform t).b ≤ A (ℜ.transform t) r' := by
        by_contra hno
        push Not at hno
        exact hS' (S_eq_empty_of_forall_A_lt hX' _ hd' hJ' hE' fun s hs => hno s hs)
      have hr'spec := Nat.find_spec hex
      have hr'min : ∀ s, s < Nat.find hex → ¬ (1 ≤ s ∧ (ℜ.transform t).b ≤ A (ℜ.transform t) s) :=
        fun s hs => Nat.find_min hex hs
      set r' := Nat.find hex with hr'
      have hge : r ≤ r' := by
        by_contra hlt
        push Not at hlt
        exact absurd hr'spec.2 (not_le.mpr (hi r' hr'spec.1 hlt))
      have hle : r' ≤ N := by
        by_contra h
        push Not at h
        have h1 := A_eq_zero_of_dim_lt hX'.2.2.2 (ℜ.transform t) h
        have h2 := hr'spec.2
        rw [h1] at h2
        exact absurd h2 (by show ¬ ℜ.b ≤ 0; omega)
      have hmin' : ∀ s, 1 ≤ s → s < r' → A (ℜ.transform t) s < (ℜ.transform t).b := by
        intro s hs1 hs
        have := hr'min s hs
        push Not at this
        exact this hs1
      have hdecr : toLex (N - r', toLex (A (ℜ.transform t) r', k (ℜ.transform t) r')) < m := by
        rw [← hm, Prod.Lex.lt_iff]
        simp only [ofLex_toLex]
        rcases hge.lt_or_eq with hlt | heq
        · exact Or.inl (by omega)
        · have heq' : r' = r := heq.symm
          rw [heq']
          refine Or.inr ⟨rfl, ?_⟩
          rw [Prod.Lex.lt_iff]
          simp only [ofLex_toLex]
          by_cases hK : K ℜ r = {H}
          · exact Or.inl (hii hK)
          · obtain ⟨H', hH', hne⟩ : ∃ H' ∈ K ℜ r, H' ≠ H := by
              by_contra hno
              push Not at hno
              exact hK (Set.eq_singleton_iff_unique_mem.mpr ⟨hH, fun H' hH' => hno H' hH'⟩)
            obtain ⟨hA, hk⟩ := hiii ⟨H', hH', hne⟩
            exact Or.inr ⟨hA, hk⟩
      obtain ⟨Y, g, hg, hSg⟩ := ih _ hdecr t.X' hX' (ℜ.transform t) hd' hJ' hE' r' hr'spec.1
        hr'spec.2 hmin' rfl
      exact ⟨Y, MonoidalSuccession.cons H t g, ⟨hperm, hg⟩, hSg⟩
  intro X hX ℜ hℜ hJ hE
  by_cases hex : ∃ r, 1 ≤ r ∧ ℜ.b ≤ A ℜ r
  · have hr := Nat.find_spec hex
    exact key _ X hX ℜ hℜ hJ hE (Nat.find hex) hr.1 hr.2
      (fun s hs1 hs => by
        have := Nat.find_min hex hs
        push Not at this
        exact this hs1) rfl
  · push Not at hex
    exact ⟨X, MonoidalSuccession.nil X, trivial,
      S_eq_empty_of_forall_A_lt hX ℜ hℜ hJ hE fun s hs => hex s hs⟩

end CD

namespace MonoidalSuccession

variable {X Y : Scheme.{u}}

theorem isPermissibleII_of_sameChar {s : MonoidalSuccession X Y} {ℜ₁ ℜ₂ : DatumII.Raw X}
    (h : DatumII.Raw.SameChar ℜ₁ ℜ₂) (hs : s.IsPermissibleII ℜ₁) : s.IsPermissibleII ℜ₂ := by
  induction s with
  | nil X => trivial
  | cons B t rest ih => exact ⟨h.isPermissible hs.1, ih (h.transform t) hs.2⟩

end MonoidalSuccession

/-- **Lemma (D.1)** (p. 312): "Let `X` and `ℜ = ℜ^N_II` be as above.  We assume that `J_x` is equal
to the local ring of `X` at every point `x` of `S(ℜ)`.  Then there exists a permissible succession
of monoidal transformations `f : X' → X` for `ℜ`, such that `S(f*(ℜ))` is empty."

As printed (p. 312): "by replacing `X` by `X − S(J)` where `S(J) = {x ∈ X | ν(J_x) ≥ 1}`, we may
assume that `J` is the sheaf of local rings `O_X` of `X`": the open subscheme `U = X − S(J)` is
taken, with the restriction `ℜ_U = DatumII.Raw.pullback` of the datum (`J_U = O_U`, a datum:
`DatumII.Raw.isDatum_pullback`), the rest of the proof is carried out on `U`
(`CD.exists_isPermissibleII_S_eq_empty_of_J_eq_top_of_distinct`), and the succession found on `U` is
extended back over `X` (`MonoidalSuccession.exists_extensionII`, `Compat/ExtendSuccessionII.lean`:
its centers lie in the transforms of `S(ℜ)`, which is closed in `X` and, by the hypothesis
`J_x = O_{X,x}` on `S(ℜ)`, contained in `U`).
Gap filled: that the extension is permissible for `ℜ`, that its transform restricts to the transform
of `ℜ_U`, and that `S` of its transform stays in `U` (hence is empty) is what the paper's "as is
easily seen" covers.
Deviation from the paper (gap filled): "Moreover we may assume that `E_i ≠ E_j` if `i ≠ j` and if
`E_i` is not empty (See the introductory paragraph of this chapter.)" is carried out by merging
equal components and dropping empty ones (`DatumII.Raw.dedup`), a datum with the same
characteristics in the sense of p. 275 (`DatumII.Raw.sameChar_dedup`,
`MonoidalSuccession.isPermissibleII_of_sameChar`).
Deviation from the paper (gap filled): "Note that the transform of `ℜ` … has also these
properties" is proved (`CD.J_eq_top_and_distinct_transform`).
Deviation from the paper (gap filled): "It is obvious that if this is proved then Lemma (D.1)
follows by induction" is made explicit: induction on `(N - r, A_r, k_r)` in the lexicographic
order (`CD.exists_isPermissibleII_S_eq_empty_of_J_eq_top_of_distinct`), with `K⁰_r = ∅` for
`r > N` (`CD.not_mem_K0_of_dim_lt`, not stated in the paper).
Deviation from the paper (gap filled): the paper does not say why `r` exists while
`S(ℜ) ≠ ∅`, i.e. that `A_s(ℜ) < b` for all `s ≥ 1` forces `S(ℜ) = ∅`
(`CD.S_eq_empty_of_forall_A_lt`, proved).
The claim (i)-(iii) (`CD.isPermissible_and_A_transform_lt_and_k_transform_lt_of_mem_K`) is proved. -/
@[blueprint "lem:IV.D-1"
  (statement := /-- \textbf{Lemma (D.1).} Let $X$ and $\mathfrak R=\mathfrak R^N_{\mathrm{II}}$ be
    as above ($X$ a non-singular irreducible algebraic scheme of dimension $N\ge1$,
    $\mathfrak R$ a resolution datum on $X$ without restriction). We assume that $J_x$ is equal
    to the local ring of $X$ at every point $x$ of $S(\mathfrak R)$. Then there exists a
    permissible succession of monoidal transformations $f\colon X'\to X$ for $\mathfrak R$, such
    that $S(f^*(\mathfrak R))$ is empty. (p.~312.) -/)
  (proof := /-- (pp.~312--313.) As is easily seen, by replacing $X$ by $X-S(J)$ where
    $S(J)=\{x\in X\mid\nu(J_x)\ge1\}$, we may assume that $J$ is the sheaf of local rings
    $\mathcal O_X$ of $X$. We have $\mathfrak R=(E_1,\dots,E_\alpha\,|\,\mathcal O_X,b\,|\,
    a_1,\dots,a_\alpha)$. Moreover we may assume that $E_i\ne E_j$ if $i\ne j$ and if $E_i$ is
    not empty. (See the introductory paragraph of this chapter.) Note that the transform of
    $\mathfrak R$ by any permissible succession of monoidal transformations of $X$ for
    $\mathfrak R$ has also these properties. With the symbols $K_r^0(\mathfrak R)$,
    $A_r(\mathfrak R)$, $K_r(\mathfrak R)$, $k_r(\mathfrak R)$ of \cref{def:IV.D-1-symbols}, let $r$
    be the smallest integer (positive) such that $A_r(\mathfrak R)\ge b$, so that
    $A_s(\mathfrak R)<b$ for $1\le s<r$. Let $H$ be any one of the subschemes in
    $K_r(\mathfrak R)$. It is clear that the monoidal transformation $f_H\colon X'\to X$ with
    center $H$ is permissible for $\mathfrak R$. Let $\mathfrak R'=f_H^*(\mathfrak R)$. Then we
    claim that (i) $A_s(\mathfrak R')<b$ for $1\le s<r$ (which is trivial if $r=1$), (ii) if
    $K_r(\mathfrak R)$ consists of only $H$, then $A_r(\mathfrak R')<A_r(\mathfrak R)$, and (iii) if $K_r(\mathfrak R)$ contains
    subschemes other than $H$ then $A_r(\mathfrak R')=A_r(\mathfrak R)$ and
    $k_r(\mathfrak R')<k_r(\mathfrak R)$ (\cref{lem:IV.D-1-claim}). It is obvious that if this
    is proved then Lemma (D.1) follows by induction.

    \textbf{Gap filled.} ``By replacing $X$ by $X-S(J)$'' is carried out as printed: Lean takes
    the open subscheme $U=X-S(J)$ (non-empty, ambient of some dimension $N'\le N$) with the
    restriction $\mathfrak R_U$ of the datum, whose $J_U$ is the sheaf of local rings $\mathcal O_U$,
    runs the rest of the proof on $U$, and extends the resulting succession back over $X$: the centers
    lie in the transforms of $S(\mathfrak R)$, which is closed in $X$ and contained in $U$ (as $J_x=
    \mathcal O_{X,x}$ on $S(\mathfrak R)$), so each is the closure of a center of $U$; the extension is
    permissible for $\mathfrak R$, its transform restricts to the transform of $\mathfrak R_U$, and
    $S$ of its transform lies in $U$, hence is empty. The paper does not spell this out.

    \textbf{Deviation from the paper (gap filled).} ``We may assume that $E_i\ne E_j$ if $i\ne j$
    and if $E_i$ is not empty'', for which the paper refers to p.~275, is carried out: equal
    components are merged, their coefficients added, and empty ones dropped; the result has the
    same characteristics in the sense of p.~275, so permissible successions, $S$ and transforms
    are unchanged.

    \textbf{Deviation from the paper (gap filled).} ``Note that the transform \dots\ has also
    these properties'' is proved: $J'=\mathcal O_{X'}$ since $\nu=0$; strict transforms of
    distinct non-singular irreducible $E_i$ with non-empty strict transform are distinct, and
    differ from the exceptional subscheme.

    \textbf{Deviation from the paper (gap filled).} ``It is obvious that if this is proved then
    Lemma (D.1) follows by induction'' is made explicit: the induction is on the triple
    $(N-r,A_r,k_r)$ in the lexicographic order, $r$ the least positive integer with $A_r\ge b$.
    By (i) the new $r$ is not smaller, and by (ii), (iii) the pair $(A_r,k_r)$ drops when $r$
    stays. That $r\le N$ uses $K^0_r(\mathfrak R)=\emptyset$, so $A_r(\mathfrak R)=0$, for $r>N$
    (a non-empty subscheme has codimension at most $N$), which the paper does not state.

    \textbf{Deviation from the paper (gap filled).} The paper does not say why $r$ exists while
    $S(\mathfrak R)\ne\emptyset$, i.e.\ that $A_s(\mathfrak R)<b$ for all $s\ge1$ forces
    $S(\mathfrak R)=\emptyset$; this is \cref{lem:IV.D-1-S-empty} (proved).
    The claim (i)--(iii) (\cref{lem:IV.D-1-claim}) is proved. -/)
  (proofUses := ["def:IV.D-1-symbols", "lem:IV.D-1-claim", "lem:IV.D-1-S-empty"])
  (latexEnv := "lemma")]
theorem exists_isPermissibleII_S_eq_empty_of_forall_stalkIdeal_eq_top [Hironaka.HironakaCitedResults.{u}] (N : ℕ) (X : Scheme.{u})
    (hX : IsAmbient X N) (ℜ : DatumII X)
    (hJ : ∀ x ∈ (ℜ : DatumII.Raw X).S, (ℜ : DatumII.Raw X).J.stalkIdeal x = ⊤) :
    ∃ (X' : Scheme.{u}) (f : MonoidalSuccession X X'),
      f.IsPermissibleII ℜ ∧ (f.transformII ℜ).S = ∅ := by
  classical
  have hℜ : (ℜ : DatumII.Raw X).IsDatum := ℜ.2
  have hXa : IsAlgebraicScheme X := hX.1
  by_cases hSe : (ℜ : DatumII.Raw X).S = ∅
  · exact ⟨X, MonoidalSuccession.nil X, trivial, hSe⟩
  -- p. 312: "by replacing `X` by `X − S(J)` where `S(J) = {x ∈ X | ν(J_x) ≥ 1}`"
  let U : X.Opens :=
    ⟨((ℜ : DatumII.Raw X).J.pts)ᶜ, (ℜ : DatumII.Raw X).J.support.isClosed.isOpen_compl⟩
  let j : (U : Scheme.{u}) ⟶ X := U.ι
  have hrange : Set.range j.base = ((ℜ : DatumII.Raw X).J.pts)ᶜ := Scheme.Opens.range_ι U
  -- `S(ℜ)` lies in `X − S(J)`: `J_x = O_{X,x}` at the points of `S(ℜ)`
  have hSj : (ℜ : DatumII.Raw X).S ⊆ Set.range j.base := by
    intro x hx
    rw [hrange]
    intro hxJ
    exact (Subscheme.mem_pts_iff_stalkIdeal_ne_top.mp hxJ) (hJ x hx)
  obtain ⟨x₁, hx₁⟩ := Set.nonempty_iff_ne_empty.mpr hSe
  have : Nonempty (U : Scheme.{u}) := by
    obtain ⟨z, -⟩ := hSj hx₁
    exact ⟨z⟩
  obtain ⟨N', -, hU⟩ := exists_isAmbient_of_isOpenImmersion hX j
  -- the restriction `ℜ_U` of `ℜ` to `X − S(J)`: `J_U` is the sheaf of local rings `O_U`
  have hℜU : ((ℜ : DatumII.Raw X).pullback j).IsDatum := DatumII.Raw.isDatum_pullback j hℜ
  have hJU : ((ℜ : DatumII.Raw X).pullback j).J = ⊤ := by
    refine Subscheme.eq_empty_of_pts_eq_empty ?_
    show (Subscheme.totalTransform j (ℜ : DatumII.Raw X).J).pts = ∅
    rw [FlatPreimm.pts_totalTransform]
    refine Set.eq_empty_of_forall_notMem fun z hz => ?_
    have hz' : j.base z ∈ Set.range j.base := ⟨z, rfl⟩
    rw [hrange] at hz'
    exact hz' hz
  -- "Moreover we may assume that `E_i ≠ E_j` if `i ≠ j` and if `E_i` is not empty."
  have hsc := DatumII.Raw.sameChar_dedup ((ℜ : DatumII.Raw X).pullback j)
  have hd1 := hsc.isDatum hℜU
  -- the rest of the proof, on `X − S(J)`, where `J = O_U`
  obtain ⟨Y, g, hg, hS⟩ := CD.exists_isPermissibleII_S_eq_empty_of_J_eq_top_of_distinct (N := N')
    U hU _ hd1 hJU (DatumII.Raw.dedup_distinct _)
  have hg0 : g.IsPermissibleII ((ℜ : DatumII.Raw X).pullback j) :=
    MonoidalSuccession.isPermissibleII_of_sameChar hsc.symm hg
  have hSg : (g.transformII ((ℜ : DatumII.Raw X).pullback j)).S = ∅ := by
    rw [(MonoidalSuccession.sameChar_transformII g hsc).S_eq]
    exact hS
  -- the succession of `X − S(J)` is induced by a permissible succession of `X`: its centers lie in
  -- the transforms of `S(ℜ)`, which is closed in `X` and contained in `X − S(J)`
  have : IsAlgebraicScheme X := hXa
  obtain ⟨Y', sY, j', hfl, hpre, -, -, -, htr, hpermY, hSY⟩ :=
    MonoidalSuccession.exists_extensionII g j hX.2.1 (ℜ : DatumII.Raw X) hℜ
      (ℜ : DatumII.Raw X).S (LocSucc.isClosed_S hX.2.1 (ℜ : DatumII.Raw X)) hSj subset_rfl hg0
  have := hfl
  have := hpre
  refine ⟨Y', sY, hpermY, Set.eq_empty_of_forall_notMem fun y hy => ?_⟩
  obtain ⟨z, rfl⟩ := hSY hy
  have hz := (DatumII.Raw.mem_S_pullback j' (sY.transformII (ℜ : DatumII.Raw X)) z).mpr hy
  rw [htr, hSg] at hz
  exact hz

/-! ## Theorem D follows from Theorem D* (p. 312) -/

namespace CD

/-- The scheme reached by a permissible succession is again ambient of the same dimension.  Used
without comment throughout Ch. IV (e.g. p. 312, where Lemma (D.1) is applied on `X'` after
Theorem D*); not a numbered statement of the paper.

Gap in the paper filled: the paper uses this fact without comment.  It is proved by
`MonoidalSuccession.isAmbient_transformII` (induction on the succession: a permissible center
lies in `S(ℜ)`, which misses the generic point, so each monoidal transformation of the
non-singular irreducible `X` keeps it non-singular, irreducible, algebraic and of dimension `N`). -/
@[blueprint "lem:IV.4-ambient"
  (statement := /-- Let $X$ be a non-singular irreducible algebraic scheme of dimension $N$,
    $\mathfrak R^N_{\mathrm{II}}$ a resolution datum on $X$ and $f\colon X'\to X$ a permissible
    succession of monoidal transformations for $\mathfrak R^N_{\mathrm{II}}$ (\cref{def:I.8}).
    Then $X'$ is again a non-singular irreducible algebraic scheme of dimension $N$.
    \textbf{Gap in the paper filled.} This fact is used without comment in the paper (e.g.\
    on p.~312, where Lemma (D.1) is applied on $X'$ after Theorem D*); it is neither a numbered
    statement nor a cited result. It is proved in the formalization. -/)
  (proof := /-- By induction on the length of $f$. A permissible center $B$ is empty (and then
    the monoidal transformation is an isomorphism, \cref{lem:monoidal-transformation-empty-center})
    or non-singular irreducible and contained in $S^*(\mathfrak R^N_{\mathrm{II}})$, which has
    codimension at least one (\cref{lem:IV.1-2}); the monoidal transformation of the
    non-singular irreducible $X$ with a nowhere dense non-singular center is proper and
    birational, so $X'$ is algebraic, irreducible of dimension $N$, and non-singular
    (\cref{lem:monoidal-transformation-proper}, \cref{lem:monoidal-transformation-nonsingular});
    the transform is again a resolution datum (\cref{rem:I.1-transform-is-datum-II}). -/)
  (proofUses := ["lem:monoidal-transformation-empty-center", "lem:IV.1-2",
    "lem:monoidal-transformation-proper", "lem:monoidal-transformation-nonsingular",
    "rem:I.1-transform-is-datum-II"])
  (latexEnv := "lemma")]
theorem isAmbient_of_isPermissibleII [Hironaka.HironakaCitedResults.{u}] {N : ℕ} {X Y : Scheme.{u}} (hX : IsAmbient X N)
    (f : MonoidalSuccession X Y) (ℜ : DatumII.Raw X) (hℜ : ℜ.IsDatum)
    (hf : f.IsPermissibleII ℜ) : IsAmbient Y N :=
  (f.isAmbient_transformII hX ℜ hℜ hf).1

end CD

/-- pp. 311–312: "We shall consider the following Theorem D*, which is a priori weaker than
Theorem D, and shall prove that Theorem D follows Theorem D*. … Then Theorem D follows by virtue
of the following: Lemma (D.1)."  Proved in Lean from `exists_isPermissibleII_Snu_one_eq_empty_of_forall_exists_Snu_eq_empty` and
`exists_isPermissibleII_S_eq_empty_of_forall_stalkIdeal_eq_top`: the composite of the two successions they provide.  "Theorem D* is verified" is the
hypothesis `hDstar`, as in `lem:IV.D-star-consequence`. -/
@[blueprint "lem:IV.D-from-D-star"
  (statement := /-- Theorem D follows Theorem D*: if Theorem D* (\cref{thm:IV.D-star}) is
    verified, i.e.\ its conclusion holds for every resolution datum
    $\mathfrak R^N_{\mathrm{II}}$ on every non-singular irreducible algebraic scheme of
    dimension $N$, then the conclusion of Theorem D (\cref{thm:IV.D}) holds for every such
    datum: there is a permissible succession of monoidal transformations $f\colon X'\to X$ for
    $\mathfrak R$ such that $f^*(\mathfrak R)$ is resolved at every point of $X'$. (pp.~311--312.)
 -/)
  (proof := /-- By \cref{lem:IV.D-star-consequence} there is a permissible succession
    $f_1\colon X_1\to X$ for $\mathfrak R$ such that $J'_{x'}$ is the local ring of $X_1$ at every
    point of $S(f_1^*(\mathfrak R))$. $X_1$ is again a non-singular irreducible algebraic scheme
    of dimension $N$ (\cref{lem:IV.4-ambient}) and $f_1^*(\mathfrak R)$ a resolution datum
    (\cref{lem:I.8-transform-is-datum}), so Lemma (D.1) (\cref{lem:IV.D-1}) gives a permissible
    succession $f_2\colon X'\to X_1$ for $f_1^*(\mathfrak R)$ with $S(f_2^*f_1^*(\mathfrak R))$
    empty. The composite $f_1\circ f_2$ is permissible for $\mathfrak R$ (\cref{def:I.8}) and
    $f^*(\mathfrak R)$ is resolved at every point (\cref{rem:IV.4-resolved-iff}). -/)
  (proofUses := ["lem:IV.D-star-consequence", "lem:IV.4-ambient", "lem:I.8-transform-is-datum",
    "lem:IV.D-1", "rem:IV.4-resolved-iff"])
  (latexEnv := "lemma")]
theorem exists_isPermissibleII_resolvedEverywhere_of_forall_exists_Snu_eq_empty [Hironaka.HironakaCitedResults.{u}] (N : ℕ)
    (hDstar : ∀ (X : Scheme.{u}), IsAmbient X N → ∀ (ℜ : DatumII X),
      0 < (ℜ : DatumII.Raw X).nu →
      ∃ (X' : Scheme.{u}) (f : MonoidalSuccession X X'),
        f.IsPermissibleII ℜ ∧ (f.transformII ℜ).sNu (ℜ : DatumII.Raw X).nu = ∅)
    (X : Scheme.{u}) (hX : IsAmbient X N) (ℜ : DatumII X) :
    ∃ (X' : Scheme.{u}) (f : MonoidalSuccession X X'),
      f.IsPermissibleII ℜ ∧ (f.transformII ℜ).ResolvedEverywhere := by
  obtain ⟨X₁, f₁, hf₁, -, hJ⟩ := exists_isPermissibleII_Snu_one_eq_empty_of_forall_exists_Snu_eq_empty N hDstar X hX ℜ
  have hd : (f₁.transformII (ℜ : DatumII.Raw X)).IsDatum :=
    have := hX.1
    MonoidalSuccession.transformII_isDatum f₁ hX.2.1 _ ℜ.2 hf₁
  obtain ⟨X', f₂, hf₂, hS⟩ :=
    exists_isPermissibleII_S_eq_empty_of_forall_stalkIdeal_eq_top N X₁ (CD.isAmbient_of_isPermissibleII hX f₁ _ ℜ.2 hf₁) ⟨_, hd⟩ hJ
  refine ⟨X', MonoidalSuccession.append f₁ f₂, (MonoidalSuccession.isPermissibleII_append f₁ f₂ _).2 ⟨hf₁, hf₂⟩, ?_⟩
  rw [MonoidalSuccession.transformII_append, DatumII.Raw.resolvedEverywhere_iff_S_eq_empty]
  exact hS

/-! ## Lemma (D.2) and the reduction to `S_ν` without components of codimension one (p. 314) -/

/-! ### Helpers for Lemma (D.2): the local computation at a generic point of `E'` -/

namespace CD
variable {X : Scheme.{u}} {B : Subscheme X}

/-- copy of `key` in `exceptional_isIrreducible`: generic points of `E = f⁻¹(B)`. -/
theorem exists_generic_exceptional [IsAlgebraicScheme X] (hX : X.IsNonsingular)
    (hBns : B.IsNonsingular) (t : MonoidalTransformation X B)
    (hne : t.exceptional.pts.Nonempty) :
    ∃ η ∈ t.exceptional.pts, (∀ w ∈ t.exceptional.pts, w ⤳ η → w = η) ∧
      t.exceptional.stalkIdeal η = maximalIdeal (t.X'.presheaf.stalk η) ∧
      B.stalkIdeal (t.f η) = maximalIdeal (X.presheaf.stalk (t.f η)) := by
  obtain ⟨y₀, hy₀⟩ := hne
  obtain ⟨η, hη, hgen, -⟩ := Subscheme.exists_maximalGeneric_specializes t.exceptional hy₀
  have hprime : (t.exceptional.stalkIdeal η).IsPrime := by
    have := t.isRegularLocalRing_quotient_exceptional hX hBns hη
    have := isDomain_of_isRegularLocalRing (t.X'.presheaf.stalk η ⧸ t.exceptional.stalkIdeal η)
    exact (Ideal.Quotient.isDomain_iff_prime _).mp this
  have hmax := Subscheme.stalkIdeal_eq_maximalIdeal_of_maximalGeneric t.exceptional hη hgen hprime
  refine ⟨η, hη, hgen, hmax, ?_⟩
  have hfη := t.mem_pts_of_mem_exceptional hη
  refine le_antisymm (Subscheme.stalkIdeal_le_maximalIdeal B hfη) fun g hg => ?_
  rw [← pow_one (B.stalkIdeal _),
    ← MonoidalTransformation.stalkMap_mem_exceptional_pow_iff hX hBns t hη 1 g, pow_one, hmax]
  exact map_nonunit (t.f.stalkMap η).hom g hg

/-- A permissible center of a datum on an ambient scheme: `E = f⁻¹(B)` is non-empty if `B` is. -/
theorem exceptional_pts_nonempty [Hironaka.HironakaCitedResults.{u}] [IsAlgebraicScheme X] [IrreducibleSpace X]
    (hX : X.IsNonsingular) (ℜ : DatumII.Raw X) (hℜ : ℜ.IsDatum) (hB : ℜ.IsPermissible B)
    (hBne : B.IsNonempty) (t : MonoidalTransformation X B) : t.exceptional.pts.Nonempty := by
  have hBX : B.pts ≠ Set.univ := fun h =>
    LocSucc.genericPoint_notMem_S hX ℜ hℜ ((hB.2.1 (h ▸ Set.mem_univ _)).1)
  have hint : interior B.pts = ∅ := by
    by_contra hne
    have hd : Dense (interior B.pts) := isOpen_interior.dense (Set.nonempty_iff_ne_empty.mpr hne)
    apply hBX
    refine Set.eq_univ_of_univ_subset ?_
    rw [← hd.closure_eq]
    exact closure_minimal interior_subset B.support.isClosed
  have hnd : IsNowhereDense B.pts := by
    unfold IsNowhereDense
    have hcl : closure B.pts = B.pts := B.support.isClosed.closure_eq
    rw [hcl]; exact hint
  have := IsAlgebraicScheme.isNoetherian X
  have : IsLocallyNoetherian X := inferInstance
  have hsurj := t.surjective_of_isNowhereDense hnd
  obtain ⟨b, hb⟩ := hBne
  obtain ⟨y, rfl⟩ := hsurj b
  exact ⟨y, by rw [MonoidalTransformation.pts_exceptional]; exact hb⟩

/-- Core local computation of Lemma (D.2): at a generic point `η` of `E = f⁻¹(B)` the transform
`J' = f⁻¹(J)P^{-ν}` is the unit ideal. -/
theorem stalkIdeal_transform_ideal_eq_top [Hironaka.HironakaCitedResults.{u}] [IsAlgebraicScheme X] (hX : X.IsNonsingular)
    (ℜ : DatumII.Raw X) (hℜ : ℜ.IsDatum) (hB : ℜ.IsPermissible B) (hBne : B.IsNonempty)
    (t : MonoidalTransformation X B) {η : t.X'} (hη : η ∈ t.exceptional.pts)
    (hE : t.exceptional.stalkIdeal η = maximalIdeal (t.X'.presheaf.stalk η))
    (hBη : B.stalkIdeal (t.f η) = maximalIdeal (X.presheaf.stalk (t.f η))) :
    (ℜ.transform t).J.stalkIdeal η = ⊤ := by
  have hBns : B.IsNonsingular := (hB.1.resolve_left (by
    rintro rfl; obtain ⟨y, hy⟩ := hBne; rw [Subscheme.pts_empty] at hy; exact hy)).1
  have hfη : t.f η ∈ B.pts := by rwa [MonoidalTransformation.pts_exceptional] at hη
  have hξS : t.f η ∈ ℜ.sStar := hB.2.1 hfη
  have hνξ : ℜ.nuAt (t.f η) = ℜ.nu :=
    le_antisymm (le_iSup₂ (f := fun x (_ : x ∈ ℜ.S) => ℜ.nuAt x) (t.f η) hξS.1) hξS.2
  have hνtop : ℜ.nu ≠ ⊤ := (DatumII.Raw.transform_isDatum hX ℜ hℜ t hB).2.2
  set k := ℜ.nu.toNat with hk
  have hkν : (k : ℕ∞) = ℜ.nu := ENat.natCast_toNat hνtop
  have hord : Ideal.ord (maximalIdeal (X.presheaf.stalk (t.f η))) (ℜ.J.stalkIdeal (t.f η)) = k := by
    rw [hkν]; exact hνξ   -- nuAt unfolds to Ideal.nu = Ideal.ord (maximalIdeal _)
  have h1 := Ideal.le_pow_of_ord_eq hord          -- J_ξ ≤ M^k   (not actually needed for ⊤)
  have h2 := Ideal.not_le_pow_succ_of_ord_eq hord -- J_ξ ⊄ M^(k+1)
  have : IsRegularLocalRing (X.presheaf.stalk (t.f η)) := hX _
  have : IsDomain (X.presheaf.stalk (t.f η)) := isDomain_of_isRegularLocalRing _
  obtain ⟨g, hgJ, hg2⟩ := Set.not_subset.mp h2
  -- stalkMap g ∈ I := (f⁻¹ J)_η, ∈ E^k, ∉ E^(k+1)
  have hgI : t.f.stalkMap η g ∈ (Subscheme.totalTransform t.f ℜ.J).stalkIdeal η := by
    rw [stalkIdeal_totalTransform]
    exact Ideal.mem_map_of_mem _ hgJ
  have hgk : t.f.stalkMap η g ∈ t.exceptional.stalkIdeal η ^ k :=
    (MonoidalTransformation.stalkMap_mem_exceptional_pow_iff hX hBns t hη k g).mpr
      (by rw [hBη]; exact h1 hgJ)
  have hgk1 : t.f.stalkMap η g ∉ t.exceptional.stalkIdeal η ^ (k + 1) := fun h =>
    hg2 (by rw [← hBη]; exact (MonoidalTransformation.stalkMap_mem_exceptional_pow_iff hX hBns t hη (k+1) g).mp h)
  -- regular local ring of dim 1 with principal maximal ideal: E_η = span {π}
  have : IsRegularLocalRing (t.X'.presheaf.stalk η) := t.isRegularLocalRing_stalk hX hBns η
  have : IsDomain (t.X'.presheaf.stalk η) := isDomain_of_isRegularLocalRing _
  obtain ⟨s, e, -, hEs⟩ := t.exists_monoidalTransform_stalk_exceptional η
  set π := e s.xR            -- E_η = span {π}
  have hEπ : t.exceptional.stalkIdeal η = Ideal.span {π} := by
    rw [hEs]
  rw [hEπ, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at hgk hgk1
  obtain ⟨w, hw⟩ := hgk
  have hwu : IsUnit w := by
    by_contra hwn
    have hwm : w ∈ maximalIdeal (t.X'.presheaf.stalk η) := (mem_maximalIdeal _).mpr hwn
    rw [← hE, hEπ] at hwm
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp hwm  -- hc : c * π = w
    exact hgk1 ⟨c, by rw [hw, ← hc]; ring⟩
  -- so π^k ∈ I, hence E_η^k ≤ I, hence 1 ∈ I : E_η^k
  have hπk : π ^ k ∈ (Subscheme.totalTransform t.f ℜ.J).stalkIdeal η := by
    have : π ^ k = (t.f.stalkMap η g) * ↑hwu.unit⁻¹ := by
      rw [hw, mul_assoc, IsUnit.mul_val_inv, mul_one]
    rw [this]; exact Ideal.mul_mem_right _ _ hgI
  have hle : t.exceptional.stalkIdeal η ^ k ≤ (Subscheme.totalTransform t.f ℜ.J).stalkIdeal η := by
    rw [hEπ, Ideal.span_singleton_pow, Ideal.span_singleton_le_iff_mem]; exact hπk
  show (Subscheme.divPow (Subscheme.totalTransform t.f ℜ.J) t.exceptional k).stalkIdeal η = ⊤
  rw [Subscheme.stalkIdeal_divPow (P := t.exceptional) t.invertible k η, eq_top_iff]
  intro x _
  refine Submodule.mem_colon.mpr fun p hp => ?_
  -- x • p = x * p ∈ I since p ∈ E_η^k ≤ I
  exact Ideal.mul_mem_left _ x (hle hp)

/-- The identity as the monoidal transformation with empty center. -/
noncomputable def monoidalTransformationEmpty (X : Scheme.{u}) :
    MonoidalTransformation X (Subscheme.empty : Subscheme X) where
  X' := X
  f := 𝟙 X
  invertible := by rw [Subscheme.totalTransform_id]; exact Subscheme.isInvertibleIdeal_empty
  universal := fun X'' f' _ => ⟨f', Category.comp_id _, fun h hh => by simpa using hh⟩

end CD

/-- **Lemma (D.2)** (p. 314).  "As in Theorem D*" is read as fixing `X`, `ℜ` and
`ν = ν(ℜ) > 0`.

Correction of the paper (statement): the center `B` is assumed non-empty; for the empty center,
which the paper allows (p. 168; "the monoidal transformation with the empty center is the
identity", p. 295), `E'` is empty and contained in every set, so the printed assertion fails.
Deviation from the paper (statement modified): the inductive assumptions of Theorem D* are not
used ("the following Lemma is clear by the definition of a transform") and are omitted, which
makes the statement stronger.

Deviation from the paper (gap filled): the paper gives no argument ("clear by the definition of a
transform").  Lean proves it: `E'` is non-empty (the center is nowhere dense, hence the monoidal
transformation is surjective), at a generic point `η` of `E'` one has `E'_η = M_η` and
`B_{f η} = M_{f η}`, `ν(J_{f η}) = ν` (as `f η ∈ B ⊆ S_*`), whence `f⁻¹(J)_η = P_η^ν` (both
`J ⊆ B^ν` and `J ⊄ B^{ν+1}` are needed) and `J'_η = O_{X',η}`, so `ν(J'_η) = 0 < ν`. -/
@[blueprint "lem:IV.D-2"
  (statement := /-- \textbf{Lemma (D.2).} Let $\mathfrak R=\mathfrak R^N_{\mathrm{II}}$ on $X$ be
    as in Theorem D* (\cref{thm:IV.D-star}), so that $\nu=\nu(\mathfrak R)>0$. Let
    $f\colon X'\to X$ be a permissible monoidal transformation of $X$ with center $B$ for
    $\mathfrak R$ (\cref{def:I.6-II}), and $E'$ the total transform of $B$ on $X'$. Then $E'$ is
    not contained in $S_\nu(f^*(\mathfrak R))$. (p.~314.)

    \textbf{Correction of the paper (statement).} $B$ is assumed non-empty: for the empty center,
    which the paper allows (p.~168; ``the monoidal transformation with the empty center is the
    identity isomorphism'', p.~295), $E'$ is empty and hence contained in
    $S_\nu(f^*(\mathfrak R))$, so the printed conclusion fails.
    \textbf{Deviation from the paper (statement modified).} The inductive assumptions of
    Theorem D* are not used and are omitted (a stronger statement). -/)
  (proof := /-- ``The following Lemma is clear by the definition of a transform of
    $\mathfrak R^N_{\mathrm{II}}$ by a permissible monoidal transformation. (See Definition 7
    (II).)'' (\cref{def:I.7-II}.) At the generic point $\eta$ of a component of $E'$ the local
    ring of $X'$ is a discrete valuation ring whose maximal ideal is the ideal $P_\eta$ of $E'$;
    since $B\subseteq S_*(\mathfrak R)$ is a permissible center, $f^{-1}(J)_\eta=P_\eta^\nu$, so
    the transform $J'=f^{-1}(J)P^{-\nu}$ has $J'_\eta=\mathcal O_{X',\eta}$ and
    $\nu(J'_\eta)=0<\nu$; hence $\eta\notin S_\nu(f^*(\mathfrak R))$.

    \textbf{Deviation from the paper (gap filled).} On p.~314 the paper says only: ``The following
    Lemma is clear by the definition of a transform of $\mathfrak R^N_{\mathrm{II}}$ by a
    permissible monoidal transformation. (See Definition 7 (II).)'' and gives no argument. Lean
    proves the following, none of which is in the paper: (a) $E'\neq\emptyset$: the non-empty
    center $B\subseteq S_*(\mathfrak R)$ is nowhere dense ($S_*$ misses the generic point of $X$,
    \cref{lem:IV.1-2}), so $f$ is surjective (it is proper and an isomorphism off $B$); (b) a
    generic point $\eta$ of $E'$ (a point of $E'$ without proper generization in $E'$) exists, and
    there $E'_\eta$ is the maximal ideal of $\mathcal O_{X',\eta}$, generated by one element $\pi$,
    and $B_{f(\eta)}$ is the maximal ideal of $\mathcal O_{X,f(\eta)}$ (as in the proof of
    \cref{compat:blowup-exceptional-irreducible}); (c) both inclusions behind
    $f^{-1}(J)_\eta=P_\eta^\nu$: since $\nu(J_{f(\eta)})=\nu$ (as $f(\eta)\in B\subseteq S_*$) we
    have $J_{f(\eta)}\subseteq B_{f(\eta)}^\nu$, and there is $g\in J_{f(\eta)}\setminus
    B_{f(\eta)}^{\nu+1}$, whose image is $\pi^\nu w$ with $w$ a unit; (d) hence the colon ideal
    $f^{-1}(J)_\eta:P_\eta^\nu$ is the unit ideal, $J'_\eta=(1)$ and $\nu(J'_\eta)=0<\nu$. -/)
  (proofUses := ["def:I.7-II"])
  (latexEnv := "lemma")]
theorem not_exceptional_pts_subset_Snu_transform [Hironaka.HironakaCitedResults.{u}] (N : ℕ) (X : Scheme.{u}) (hX : IsAmbient X N) (ℜ : DatumII X)
    (hν : 0 < (ℜ : DatumII.Raw X).nu) (B : Subscheme X)
    (hB : (ℜ : DatumII.Raw X).IsPermissible B) (hBne : B.IsNonempty)
    (t : MonoidalTransformation X B) :
    ¬ t.exceptional.pts ⊆ ((ℜ : DatumII.Raw X).transform t).sNu (ℜ : DatumII.Raw X).nu := by
  obtain ⟨hXa, hXns, hXirr, -⟩ := hX
  have hBns : B.IsNonsingular := (hB.1.resolve_left (by
    rintro rfl; obtain ⟨y, hy⟩ := hBne; rw [Subscheme.pts_empty] at hy; exact hy)).1
  obtain ⟨η, hη, -, hE, hBη⟩ := CD.exists_generic_exceptional hXns hBns t
    (CD.exceptional_pts_nonempty hXns _ ℜ.2 hB hBne t)
  intro hsub
  have hJ := CD.stalkIdeal_transform_ideal_eq_top hXns _ ℜ.2 hB hBne t hη hE hBη
  have hnu0 : ((ℜ : DatumII.Raw X).transform t).nuAt η = 0 := by
    unfold DatumII.Raw.nuAt; rw [hJ]; exact Ideal.nu_top
  have := (hsub hη).2        -- ν ≤ nuAt η
  rw [hnu0] at this
  exact absurd (lt_of_lt_of_le hν this) (lt_irrefl _)

/-- **Lemma (D.2) as printed is false** (p. 314, without the hypothesis that the center is
non-empty).  For every datum `ℜ` as in Theorem D* the empty subscheme is a permissible center
(p. 168), it has a monoidal transformation (the identity, p. 295), and for every such the total
transform `E'` of the center is empty, hence contained in `S_ν(f*(ℜ))`.  So the printed assertion
"`E'` is not contained in `S_ν(f*(ℜ))`" fails for every datum.

Deviation from the paper (statement corrected): the printed Lemma (D.2) is proved as `not_exceptional_pts_subset_Snu_transform`
with the extra hypothesis `hBne`. -/
@[blueprint "lem:IV.D-2-as-printed"
  (statement := /-- Statement as printed (false); see \cref{lem:IV.D-2}. For every resolution datum $\mathfrak R$ as in Theorem D* the empty
    subscheme is a permissible center, the monoidal transformation with this center exists, and
    for each such $f$ the total transform $E'$ of the center is empty, hence contained in
    $S_\nu(f^*(\mathfrak R))$; so the printed assertion ``$E'$ is not contained in
    $S_\nu(f^*(\mathfrak R))$'' fails. -/)
  (proof := /-- The empty subscheme is a center and is permissible (it is contained in $S_*$ and
    the normal-crossing condition at the points of $B$ is empty). The identity is a monoidal
    transformation with empty center, since $f^{-1}(\emptyset)=\emptyset$ has the unit ideal,
    invertible, and the universal property is trivial. For any monoidal transformation with
    empty center the points of $f^{-1}(B)$ are the points over $B=\emptyset$, so $E'=\emptyset$.
    \textbf{Deviation from the paper (statement corrected).} This is the failure of the printed
    statement; \cref{lem:IV.D-2} adds the hypothesis that $B$ is non-empty. -/)
  (proofUses := ["lem:IV.D-2"])
  (latexEnv := "lemma")]
theorem isPermissible_empty_and_exceptional_pts_subset_Snu_transform_empty (N : ℕ) (X : Scheme.{u}) (_hX : IsAmbient X N) (ℜ : DatumII X)
    (_hν : 0 < (ℜ : DatumII.Raw X).nu) :
    (ℜ : DatumII.Raw X).IsPermissible (Subscheme.empty : Subscheme X) ∧
    Nonempty (MonoidalTransformation X (Subscheme.empty : Subscheme X)) ∧
    ∀ t : MonoidalTransformation X (Subscheme.empty : Subscheme X),
      t.exceptional.pts ⊆ ((ℜ : DatumII.Raw X).transform t).sNu (ℜ : DatumII.Raw X).nu := by
  refine ⟨⟨Or.inl rfl, by rw [Subscheme.pts_empty]; exact Set.empty_subset _,
    fun x hx => by rw [Subscheme.pts_empty] at hx; exact hx.elim⟩,
    ⟨CD.monoidalTransformationEmpty X⟩, fun t y hy => ?_⟩
  rw [MonoidalTransformation.pts_exceptional, Subscheme.pts_empty] at hy
  exact hy.elim

namespace CD

variable {X : Scheme.{u}}

/-- "`Z` has no non-empty component of codimension `1` in `X`" (p. 314): no maximal irreducible
subset of `Z` has closure of codimension one (with the reduced structure). -/
def NoCodimOneComponent (Z : Set X) : Prop :=
  ∀ Y : Set X, Maximal (fun Y : Set X => IsIrreducible Y ∧ Y ⊆ Z) Y →
    (Subscheme.ofClosed ⟨closure Y, isClosed_closure⟩).codim ≠ 1

section NoCodimOneInfrastructure

variable {B : Subscheme X}

/-- The height of the maximal ideal of the local ring at `x` (the dimension of `X` at `x`). -/
noncomputable abbrev stalkHeight (x : X) : ℕ∞ := (maximalIdeal (X.presheaf.stalk x)).height

/-- `stalkHeight x` is the height of the prime of `x` in an affine open containing `x`. -/
theorem stalkHeight_eq_height_primeIdealOf {U : X.Opens} (hU : IsAffineOpen U) {x : X}
    (hx : x ∈ U) : stalkHeight x = (hU.primeIdealOf ⟨x, hx⟩).asIdeal.height := by
  let _ := TopCat.Presheaf.algebra_section_stalk X.presheaf (⟨x, hx⟩ : U)
  have := hU.isLocalization_stalk ⟨x, hx⟩
  have h1 := IsLocalization.AtPrime.ringKrullDim_eq_height
    (hU.primeIdealOf ⟨x, hx⟩).asIdeal (X.presheaf.stalk x)
  have h2 := IsLocalRing.maximalIdeal_height_eq_ringKrullDim (R := X.presheaf.stalk x)
  rw [h1] at h2
  exact_mod_cast h2

/-- A strict specialization strictly increases the dimension of the local ring, provided the
generization has finite dimension. -/
theorem eq_of_specializes_of_stalkHeight_le {ζ η : X} (hsp : ζ ⤳ η)
    (hle : stalkHeight η ≤ stalkHeight ζ) (hfin : stalkHeight ζ ≠ ⊤) : ζ = η := by
  obtain ⟨⟨U, hU⟩, hηU⟩ := Subscheme.exists_affineOpen_mem η
  replace hηU : η ∈ U := hηU
  replace hU : IsAffineOpen U := hU
  have hζU : ζ ∈ U := hsp.mem_open U.isOpen hηU
  rw [stalkHeight_eq_height_primeIdealOf hU hζU, stalkHeight_eq_height_primeIdealOf hU hηU]
    at hle
  rw [stalkHeight_eq_height_primeIdealOf hU hζU] at hfin
  set p := hU.primeIdealOf ⟨ζ, hζU⟩
  set q := hU.primeIdealOf ⟨η, hηU⟩
  have hpq : p.asIdeal ≤ q.asIdeal := by
    rw [← Subscheme.compStalk_fromSpec_specializes_iff hU, hU.fromSpec_primeIdealOf,
      hU.fromSpec_primeIdealOf]
    exact hsp
  have hpq' : p.asIdeal = q.asIdeal := by
    by_contra hne
    have hlt : p.asIdeal < q.asIdeal := lt_of_le_of_ne hpq hne
    have : p.asIdeal.FiniteHeight := p.asIdeal.finiteHeight_iff.mpr (Or.inr hfin)
    exact absurd (Ideal.height_strict_mono_of_isPrime hlt) (not_lt.mpr hle)
  have : p = q := PrimeSpectrum.ext hpq'
  calc ζ = hU.fromSpec p := (hU.fromSpec_primeIdealOf ⟨ζ, hζU⟩).symm
    _ = hU.fromSpec q := by rw [this]
    _ = η := hU.fromSpec_primeIdealOf ⟨η, hηU⟩

theorem stalkHeight_le_of_specializes {ζ η : X} (hsp : ζ ⤳ η) :
    stalkHeight ζ ≤ stalkHeight η := by
  obtain ⟨⟨U, hU⟩, hηU⟩ := Subscheme.exists_affineOpen_mem η
  replace hηU : η ∈ U := hηU
  replace hU : IsAffineOpen U := hU
  have hζU : ζ ∈ U := hsp.mem_open U.isOpen hηU
  rw [stalkHeight_eq_height_primeIdealOf hU hζU, stalkHeight_eq_height_primeIdealOf hU hηU]
  refine Ideal.height_mono ?_
  rw [← Subscheme.compStalk_fromSpec_specializes_iff hU, hU.fromSpec_primeIdealOf,
    hU.fromSpec_primeIdealOf]
  exact hsp

/-- Codimension of the closure of a point at a point of it. -/
theorem codimAt_ofClosed_closure_singleton {η x : X} (hsp : η ⤳ x) :
    (Subscheme.ofClosed ⟨closure {η}, isClosed_closure⟩).codimAt x = stalkHeight η := by
  obtain ⟨⟨U, hU⟩, hxU⟩ := Subscheme.exists_affineOpen_mem x
  replace hxU : x ∈ U := hxU
  replace hU : IsAffineOpen U := hU
  have hηU : η ∈ U := hsp.mem_open U.isOpen hxU
  set q := hU.primeIdealOf ⟨η, hηU⟩ with hqdef
  have hq : hU.fromSpec q = η := hU.fromSpec_primeIdealOf ⟨η, hηU⟩
  have hqx : q.asIdeal ≤ (hU.primeIdealOf ⟨x, hxU⟩).asIdeal := by
    refine (Subscheme.compStalk_fromSpec_specializes_iff hU q _).mp ?_
    rw [hq, hU.fromSpec_primeIdealOf]
    exact hsp
  rw [stalkHeight_eq_height_primeIdealOf hU hηU]
  unfold Subscheme.codimAt
  have hst := Subscheme.compStalk_stalkIdeal_ofClosed_closure hU hxU q
  rw [hq] at hst
  rw [hst]
  let _ := TopCat.Presheaf.algebra_section_stalk X.presheaf (⟨x, hxU⟩ : U)
  have := hU.isLocalization_stalk ⟨x, hxU⟩
  exact IsLocalization.height_map_of_disjoint (hU.primeIdealOf ⟨x, hxU⟩).asIdeal.primeCompl
    q.asIdeal (Set.disjoint_left.mpr fun a ha haq => ha (hqx haq))

theorem codim_ofClosed_closure_singleton (η : X) :
    (Subscheme.ofClosed ⟨closure {η}, isClosed_closure⟩).codim = stalkHeight η := by
  unfold Subscheme.codim
  refine le_antisymm ?_ (le_iInf₂ fun x hx => ?_)
  · refine iInf₂_le_of_le η ?_ ?_
    · rw [Subscheme.pts_ofClosed]; exact subset_closure rfl
    · exact (codimAt_ofClosed_closure_singleton (specializes_refl η)).le
  · rw [Subscheme.pts_ofClosed] at hx
    exact (codimAt_ofClosed_closure_singleton (specializes_iff_mem_closure.mpr hx)).ge

/-- At a point of `E = f⁻¹(B)` without proper generization in `E`, `E_η` is the maximal ideal. -/
theorem exceptional_stalkIdeal_eq_maximalIdeal (hX : X.IsNonsingular) (hBns : B.IsNonsingular)
    (t : MonoidalTransformation X B) {η : t.X'} (hη : η ∈ t.exceptional.pts)
    (hgen : ∀ w ∈ t.exceptional.pts, w ⤳ η → w = η) :
    t.exceptional.stalkIdeal η = maximalIdeal (t.X'.presheaf.stalk η) := by
  have hprime : (t.exceptional.stalkIdeal η).IsPrime := by
    have := t.isRegularLocalRing_quotient_exceptional hX hBns hη
    have := isDomain_of_isRegularLocalRing (t.X'.presheaf.stalk η ⧸ t.exceptional.stalkIdeal η)
    exact (Ideal.Quotient.isDomain_iff_prime _).mp this
  exact Subscheme.stalkIdeal_eq_maximalIdeal_of_maximalGeneric t.exceptional hη hgen hprime

/-- The local ring of `X'` at a generic point of the exceptional divisor has dimension one. -/
theorem stalkHeight_eq_one_of_exceptional (hX : X.IsNonsingular) (hBirr : B.IsIrreducible)
    (hBns : B.IsNonsingular) (t : MonoidalTransformation X B) {η : t.X'}
    (hη : η ∈ t.exceptional.pts) (hgen : ∀ w ∈ t.exceptional.pts, w ⤳ η → w = η) :
    stalkHeight η = 1 := by
  have h1 := (MonoidalTransformation.exceptional_isNonsingular_and_totalTransform_le_pow hX hBirr hBns t Subscheme.empty).1.2 η hη
  have h2 := exceptional_stalkIdeal_eq_maximalIdeal hX hBns t hη hgen
  unfold Subscheme.codimAt at h1
  rw [h2] at h1
  simpa using h1

/-- The ring isomorphism of stalks off the exceptional divisor preserves the dimension. -/
theorem stalkHeight_apply_of_notMem_exceptional (hX : X.IsNonsingular)
    (t : MonoidalTransformation X B) {y : t.X'}
    (hy : y ∉ t.exceptional.pts) : stalkHeight (t.f y) = stalkHeight y := by
  have hfy : t.f y ∉ B.pts := by rwa [MonoidalTransformation.pts_exceptional] at hy
  have : IsRegularLocalRing (X.presheaf.stalk (t.f y)) := hX _
  let e := RingEquiv.ofBijective (t.f.stalkMap y).hom (t.bijective_stalkMap_of_notMem y hfy)
  have h := ringKrullDim_eq_of_ringEquiv e
  have h1 := IsLocalRing.maximalIdeal_height_eq_ringKrullDim (R := X.presheaf.stalk (t.f y))
  have h2 := IsLocalRing.maximalIdeal_height_eq_ringKrullDim (R := t.X'.presheaf.stalk y)
  unfold stalkHeight
  apply WithBot.coe_injective
  rw [h1, h2]
  exact h

/-- One step of the propagation of dimension-one points of `S_c` (the use of Lemma (D.2)). -/
theorem snu_stalkHeight_one_step [Hironaka.HironakaCitedResults.{u}] {N : ℕ} (hX : IsAmbient X N)
    (ℜ : DatumII.Raw X) (hℜ : ℜ.IsDatum) (B : Subscheme X) (hB : ℜ.IsPermissible B)
    (t : MonoidalTransformation X B) {c : ℕ∞}
    (hc : 0 < c) (hcν : ℜ.nu ≤ c) {η : t.X'}
    (hη : η ∈ (ℜ.transform t).sNu c) (h1 : stalkHeight η = 1) :
    η ∉ t.exceptional.pts ∧ t.f η ∈ ℜ.sNu c ∧ stalkHeight (t.f η) = 1 := by
  obtain ⟨hXa, hXns, hXirr, -⟩ := id hX
  by_cases hE : η ∈ t.exceptional.pts
  · exfalso
    have hfη : t.f η ∈ B.pts := by rwa [MonoidalTransformation.pts_exceptional] at hE
    have hBne : B.IsNonempty := ⟨_, hfη⟩
    obtain ⟨hBns, hBirr⟩ : B.IsNonsingular ∧ B.IsIrreducible :=
      (hB.1.resolve_left (by rintro rfl; rw [Subscheme.pts_empty] at hfη; exact hfη))
    -- the level `ν(ℜ)` is positive, otherwise `S_c` of the transform is empty
    have hνpos : 0 < ℜ.nu := by
      by_contra hneg
      rw [not_lt, nonpos_iff_eq_zero] at hneg
      have h := hneg.symm
      · exfalso
        have h2 : (ℜ.transform t).nuAt η ≤ (ℜ.transform t).nu :=
          le_iSup₂ (f := fun x (_ : x ∈ (ℜ.transform t).S) =>
            (ℜ.transform t).nuAt x) η hη.1
        have h3 := DatumII.Raw.nu_transform_le hXns _ hℜ t hB
        have h4 := hη.2
        rw [← h] at h3
        exact absurd (hc.trans_le (h4.trans (h2.trans h3))) (lt_irrefl _)
    -- a generic point of `E` below `η`
    obtain ⟨ζ, hζE, hζgen, hζη⟩ := Subscheme.exists_maximalGeneric_specializes t.exceptional hE
    have hζ1 := stalkHeight_eq_one_of_exceptional hXns hBirr hBns t hζE hζgen
    have hζ : ζ = η := eq_of_specializes_of_stalkHeight_le hζη (by rw [h1, hζ1])
      (by rw [hζ1]; exact ENat.one_ne_top)
    subst hζ
    -- `E` is irreducible, hence the closure of `ζ`
    obtain ⟨ξ, hξ⟩ := QuasiSober.sober
      (Subscheme.isIrreducible_pts _ (MonoidalTransformation.isIrreducible_exceptional hXns hBns hBirr t ⟨_, hE⟩))
      t.exceptional.support.isClosed
    have hξζ : ξ ⤳ ζ := hξ.specializes hE
    have hξζ' : ξ = ζ := hζgen ξ hξ.mem hξζ
    have hEsub : t.exceptional.pts ⊆ (ℜ.transform t).sNu c := by
      have hcl : IsClosed ((ℜ.transform t).sNu c) := by
        have := t.isAlgebraicScheme
        exact LocSucc.isClosed_sNu (t.isNonsingular_and_isNonsingular_exceptional hXns hBns).1 _ c
      intro y hy
      have : y ∈ closure {ζ} := by
        rw [← hξζ']; exact hξ.def ▸ hy
      exact closure_minimal (Set.singleton_subset_iff.mpr hη) hcl this
    refine not_exceptional_pts_subset_Snu_transform N X hX ⟨ℜ, hℜ⟩ hνpos B hB hBne t (fun y hy => ?_)
    exact ⟨(hEsub hy).1, hcν.trans (hEsub hy).2⟩
  · refine ⟨hE, ?_, ?_⟩
    · exact (DatumII.Raw.mem_sNu_transform_iff_of_notMem hXns _ t hE c).mp hη
    · rw [stalkHeight_apply_of_notMem_exceptional hXns t hE]; exact h1

/-- Propagation of dimension-one points of `S_c` through a permissible succession (the iteration
behind "after this is done, this property continues to hold", p. 314). -/
theorem snu_stalkHeight_one_composite [Hironaka.HironakaCitedResults.{u}] {N : ℕ} {Y : Scheme.{u}} (g : MonoidalSuccession X Y)
    (hX : IsAmbient X N) (ℜ : DatumII.Raw X) (hℜ : ℜ.IsDatum) (hg : g.IsPermissibleII ℜ)
    {c : ℕ∞} (hc : 0 < c) (hcν : ℜ.nu ≤ c) {η : Y} (hη : η ∈ (g.transformII ℜ).sNu c)
    (h1 : stalkHeight η = 1) :
    g.composite η ∈ ℜ.sNu c ∧ stalkHeight (g.composite η) = 1 := by
  induction g with
  | nil X => exact ⟨hη, h1⟩
  | cons B t rest ih =>
    have hXa := hX.1
    obtain ⟨hX', hd⟩ := (MonoidalSuccession.cons B t (MonoidalSuccession.nil t.X')).isAmbient_transformII
      hX ℜ hℜ ⟨hg.1, trivial⟩
    have hd' : (ℜ.transform t).IsDatum := hd
    have hν' : (ℜ.transform t).nu ≤ c :=
      (DatumII.Raw.nu_transform_le hX.2.1 ℜ hℜ t hg.1).trans hcν
    obtain ⟨hm, hh⟩ := ih hX' (ℜ.transform t) hd' hg.2 hν' hη h1
    obtain ⟨-, hm2, hh2⟩ := snu_stalkHeight_one_step hX ℜ hℜ B hg.1 t hc hcν hm hh
    rw [MonoidalSuccession.composite_cons, Scheme.Hom.comp_apply]
    exact ⟨hm2, hh2⟩

/-- Every irreducible subset of a set lies in a maximal irreducible subset of it (an irreducible
component of the set). -/
theorem exists_maximal_isIrreducible_of_subset {Z s : Set X} (hs : IsIrreducible s)
    (hsZ : s ⊆ Z) : ∃ Y, s ⊆ Y ∧ Maximal (fun Y : Set X => IsIrreducible Y ∧ Y ⊆ Z) Y := by
  obtain ⟨m, hsm, hm⟩ := zorn_subset_nonempty { t : Set X | IsIrreducible t ∧ t ⊆ Z }
    (fun c hc hcc hne => by
      obtain ⟨t₀, ht₀⟩ := hne
      refine ⟨⋃₀ c, ⟨⟨(hc ht₀).1.1.mono (Set.subset_sUnion_of_mem ht₀), ?_⟩, ?_⟩,
        fun _ hxc => Set.subset_sUnion_of_mem hxc⟩
      · intro u v hu hv ⟨y, hy, hyu⟩ ⟨x, hx, hxv⟩
        obtain ⟨p, hpc, hyp⟩ := Set.mem_sUnion.1 hy
        obtain ⟨q, hqc, hxq⟩ := Set.mem_sUnion.1 hx
        rcases hcc.total hpc hqc with hpq | hqp
        · obtain ⟨x, hxp, hxuv⟩ := (hc hqc).1.2 u v hu hv ⟨y, hpq hyp, hyu⟩ ⟨x, hxq, hxv⟩
          exact ⟨x, Set.mem_sUnion_of_mem hxp hqc, hxuv⟩
        · obtain ⟨x, hxp, hxuv⟩ := (hc hpc).1.2 u v hu hv ⟨y, hyp, hyu⟩ ⟨x, hqp hxq, hxv⟩
          exact ⟨x, Set.mem_sUnion_of_mem hxp hpc, hxuv⟩
      · exact Set.sUnion_subset fun t ht => (hc ht).2)
    s ⟨hs, hsZ⟩
  exact ⟨m, hsm, hm⟩

/-- A maximal irreducible subset of a closed set is closed. -/
theorem isClosed_of_maximal_isIrreducible {Z Y : Set X} (hZ : IsClosed Z)
    (hY : Maximal (fun Y : Set X => IsIrreducible Y ∧ Y ⊆ Z) Y) : IsClosed Y := by
  have : closure Y ⊆ Y := hY.2 ⟨hY.1.1.closure, closure_minimal hY.1.2 hZ⟩ subset_closure
  exact closure_subset_iff_isClosed.mp this

theorem codim_ofClosed_closure_eq_stalkHeight {Y : Set X} {η : X} (hη : closure {η} = closure Y) :
    (Subscheme.ofClosed ⟨closure Y, isClosed_closure⟩).codim = stalkHeight η := by
  have : (⟨closure Y, isClosed_closure⟩ : TopologicalSpace.Closeds X) =
      ⟨closure {η}, isClosed_closure⟩ := TopologicalSpace.Closeds.ext hη.symm
  rw [this]
  exact codim_ofClosed_closure_singleton η

/-- A maximal irreducible subset `Y` of a closed set has a generic point `η ∈ Y`, and the
codimension of `Y` is the dimension of the local ring at `η`. -/
theorem exists_generic_point_codim_eq {Z Y : Set X} (hZ : IsClosed Z)
    (hY : Maximal (fun Y : Set X => IsIrreducible Y ∧ Y ⊆ Z) Y) :
    ∃ η ∈ Y, (Subscheme.ofClosed ⟨closure Y, isClosed_closure⟩).codim = stalkHeight η := by
  have hcl := isClosed_of_maximal_isIrreducible hZ hY
  obtain ⟨η, hη⟩ := QuasiSober.sober hY.1.1 hcl
  refine ⟨η, hη.mem, codim_ofClosed_closure_eq_stalkHeight ?_⟩
  rw [hcl.closure_eq]
  exact hη.def

theorem noCodimOneComponent_of_forall_stalkHeight_ne_one {Z : Set X} (hZ : IsClosed Z)
    (h : ∀ η ∈ Z, stalkHeight η ≠ 1) : NoCodimOneComponent Z := fun Y hY hcodim => by
  obtain ⟨η, hηY, hη⟩ := exists_generic_point_codim_eq hZ hY
  exact h η (hY.1.2 hηY) (hη ▸ hcodim)

/-- The stability assertion of p. 314: a codimension-one component of `S_c` after one more
permissible monoidal transformation would give one before it, or a component of the new
exceptional divisor, excluded by Lemma (D.2). -/
theorem noCodimOneComponent_transform [Hironaka.HironakaCitedResults.{u}] {N : ℕ} (hX : IsAmbient X N) (ℜ : DatumII.Raw X)
    (hℜ : ℜ.IsDatum) (B : Subscheme X) (hB : ℜ.IsPermissible B)
    (t : MonoidalTransformation X B) {c : ℕ∞} (hc : 0 < c) (hcν : ℜ.nu ≤ c)
    (hno : NoCodimOneComponent (ℜ.sNu c)) :
    NoCodimOneComponent ((ℜ.transform t).sNu c) := by
  obtain ⟨hXa, hXns, hXirr, -⟩ := id hX
  have hX' : IsAmbient t.X' N :=
    ((MonoidalSuccession.cons B t (MonoidalSuccession.nil t.X')).isAmbient_transformII
      hX ℜ hℜ ⟨hB, trivial⟩).1
  obtain ⟨hXa', hXns', hXirr', -⟩ := id hX'
  intro Y hY hcodim
  have hZ'' : IsClosed ((ℜ.transform t).sNu c) := LocSucc.isClosed_sNu hXns' _ c
  obtain ⟨η, hηY, hηcodim⟩ := exists_generic_point_codim_eq hZ'' hY
  have h1 : stalkHeight η = 1 := hηcodim ▸ hcodim
  obtain ⟨-, hζ, hζ1⟩ := snu_stalkHeight_one_step hX ℜ hℜ B hB t hc hcν (hY.1.2 hηY) h1
  have hZ' : IsClosed (ℜ.sNu c) := LocSucc.isClosed_sNu hXns ℜ c
  obtain ⟨Y0, hsub, hY0⟩ := exists_maximal_isIrreducible_of_subset (Z := ℜ.sNu c)
    (s := closure {t.f η}) isIrreducible_singleton.closure
    (closure_minimal (Set.singleton_subset_iff.mpr hζ) hZ')
  have hcl0 := isClosed_of_maximal_isIrreducible hZ' hY0
  obtain ⟨ξ, hξ⟩ := QuasiSober.sober hY0.1.1 hcl0
  have hsp : ξ ⤳ t.f η := hξ.specializes (hsub (subset_closure rfl))
  have hξeq : ξ = t.f η := by
    have hle := stalkHeight_le_of_specializes hsp
    rw [hζ1] at hle
    by_cases h : stalkHeight ξ = 1
    · exact eq_of_specializes_of_stalkHeight_le hsp (by rw [h, hζ1]) (by rw [h]; exact ENat.one_ne_top)
    · exfalso
      have h0 : stalkHeight ξ = 0 := by
        rcases Order.le_one_iff.mp hle with h' | h'  -- 0 or 1
        · exact h'
        · exact absurd h' h
      have hgp : genericPoint X ⤳ ξ := genericPoint_specializes ξ
      have hgp0 : stalkHeight (genericPoint X) = 0 :=
        le_antisymm (h0 ▸ stalkHeight_le_of_specializes hgp) bot_le
      have := eq_of_specializes_of_stalkHeight_le hgp (by rw [h0, hgp0]) (by rw [hgp0]; simp)
      have hξS : ξ ∈ ℜ.S := (hY0.1.2 hξ.mem).1
      exact LocSucc.genericPoint_notMem_S hXns ℜ hℜ (this ▸ hξS)
  refine hno Y0 hY0 ?_
  rw [codim_ofClosed_closure_eq_stalkHeight (η := ξ) (by rw [hcl0.closure_eq]; exact hξ.def), hξeq]
  exact hζ1

/-- For `N ≥ 2` the localization theorem (Proposition 4) already gives the first assertion: a
codimension-one component of `S_ν` would map, by the propagation lemma, to a point of `X` of
dimension one, whereas Proposition 4 puts the image among points of dimension `N`. -/
theorem exists_permissible_noCodimOne_of_two_le [Hironaka.HironakaCitedResults.{u}] (N : ℕ) (hN : 2 ≤ N)
    (hII₂ : ∀ N' : ℕ, N' < N → FundamentalTheorem.II₂.{u} N')
    (hI₂ : ∀ n : ℕ, n < N → FundamentalTheorem.I₂.{u} N n)
    (X : Scheme.{u}) (hX : IsAmbient X N) (ℜ : DatumII X)
    (hν : 0 < (ℜ : DatumII.Raw X).nu) :
    ∃ (X' : Scheme.{u}) (f : MonoidalSuccession X X'), f.IsPermissibleII ℜ ∧
      NoCodimOneComponent ((f.transformII ℜ).sNu (ℜ : DatumII.Raw X).nu) := by
  obtain ⟨X', f, hf, -, hdim⟩ := exists_isPermissibleII_finite_image_Snu_dimAt_eq N (by omega) hII₂ hI₂ X hX ℜ hν
  obtain ⟨hX', -⟩ := f.isAmbient_transformII hX ℜ.1 ℜ.2 hf
  have := hX'.1
  refine ⟨X', f, hf, noCodimOneComponent_of_forall_stalkHeight_ne_one
    (LocSucc.isClosed_sNu hX'.2.1 _ _) fun η hη h1 => ?_⟩
  obtain ⟨-, h2⟩ := snu_stalkHeight_one_composite f hX ℜ.1 ℜ.2 hf hν le_rfl hη h1
  have h3 := hdim (f.composite.base η) ⟨η, hη, rfl⟩
  have h4 : X.dimAt (f.composite.base η) =
      ((stalkHeight (f.composite.base η) : ℕ∞) : WithBot ℕ∞) := by
    unfold Scheme.dimAt stalkHeight
    exact (IsLocalRing.maximalIdeal_height_eq_ringKrullDim).symm
  have h5 : stalkHeight (f.composite.base η) = 1 := h2
  rw [h5] at h4
  rw [h4] at h3
  have : (1 : ℕ∞) = (N : ℕ∞) := by exact_mod_cast h3
  have : (1 : ℕ) = N := by exact_mod_cast this
  omega

theorem eq_genericPoint_of_stalkHeight_eq_zero [IrreducibleSpace X] {x : X}
    (h0 : stalkHeight x = 0) : x = genericPoint X := by
  have hgp : genericPoint X ⤳ x := genericPoint_specializes x
  have hgp0 : stalkHeight (genericPoint X) = 0 :=
    le_antisymm (h0 ▸ stalkHeight_le_of_specializes hgp) bot_le
  exact (eq_of_specializes_of_stalkHeight_le hgp (by rw [h0, hgp0]) (by rw [hgp0]; simp)).symm

theorem stalkHeight_le_of_dim_eq {N : ℕ} (hdim : X.dim = (N : WithBot ℕ∞)) (x : X) :
    stalkHeight x ≤ N := by
  have h1 : X.dimAt x ≤ X.dim := le_iSup (fun x => X.dimAt x) x
  have h4 : X.dimAt x = ((stalkHeight x : ℕ∞) : WithBot ℕ∞) := by
    unfold Scheme.dimAt stalkHeight
    exact (IsLocalRing.maximalIdeal_height_eq_ringKrullDim).symm
  rw [h4, hdim] at h1
  exact_mod_cast h1

/-- On a scheme of dimension one the points of `S_c(ℜ)` have dimension one (the generic point is
not in `S(ℜ)`). -/
theorem stalkHeight_eq_one_of_mem_snu (hX : IsAmbient X 1) (ℜ : DatumII.Raw X)
    (hℜ : ℜ.IsDatum) {c : ℕ∞} {x : X} (hx : x ∈ ℜ.sNu c) : stalkHeight x = 1 := by
  obtain ⟨hXa, hXns, hXirr, hdim⟩ := hX
  have hdim' : X.dim = ((1 : ℕ) : WithBot ℕ∞) := hdim
  have hle : stalkHeight x ≤ 1 := by exact_mod_cast stalkHeight_le_of_dim_eq hdim' x
  rcases Order.le_one_iff.mp hle with h | h
  · have hx0 := eq_genericPoint_of_stalkHeight_eq_zero h
    exact absurd (hx0 ▸ hx.1) (LocSucc.genericPoint_notMem_S hXns ℜ hℜ)
  · exact h

/-- On a scheme of dimension one the points of `S_c(ℜ)` are closed. -/
theorem closure_singleton_eq_of_mem_snu (hX : IsAmbient X 1) (ℜ : DatumII.Raw X)
    (hℜ : ℜ.IsDatum) {c : ℕ∞} {x : X} (hx : x ∈ ℜ.sNu c) : closure ({x} : Set X) = {x} := by
  have hdim' : X.dim = ((1 : ℕ) : WithBot ℕ∞) := hX.2.2.2
  refine Set.Subset.antisymm (fun z hz => ?_) subset_closure
  have hsp : x ⤳ z := specializes_iff_mem_closure.mpr hz
  have hle : stalkHeight z ≤ 1 := by exact_mod_cast stalkHeight_le_of_dim_eq hdim' z
  have h1 := stalkHeight_eq_one_of_mem_snu hX ℜ hℜ hx
  exact (eq_of_specializes_of_stalkHeight_le hsp (by rw [h1]; exact hle)
    (by rw [h1]; exact ENat.one_ne_top)).symm ▸ rfl

/-- On a scheme of dimension one, `S_c(ℜ)` is a finite set of closed points. -/
theorem finite_snu_of_dim_eq_one [Hironaka.HironakaCitedResults.{u}] (hX : IsAmbient X 1) (ℜ : DatumII.Raw X) (hℜ : ℜ.IsDatum)
    (c : ℕ∞) : (ℜ.sNu c).Finite := by
  obtain ⟨hXa, hXns, hXirr, hdim⟩ := id hX
  have := IsAlgebraicScheme.noetherianSpace X
  have hZ : IsClosed (ℜ.sNu c) := LocSucc.isClosed_sNu hXns ℜ c
  obtain ⟨S, hSf, hSc, hSi, hSU⟩ :=
    TopologicalSpace.NoetherianSpace.exists_finite_set_isClosed_irreducible hZ
  rw [hSU]
  refine hSf.sUnion fun t ht => ?_
  obtain ⟨η, hη⟩ := QuasiSober.sober (hSi t ht) (hSc t ht)
  have hηZ : η ∈ ℜ.sNu c := hSU ▸ Set.mem_sUnion_of_mem hη.mem ht
  rw [← hη.def, closure_singleton_eq_of_mem_snu hX ℜ hℜ hηZ]
  exact Set.finite_singleton η

/-- The reduced closed point `{y}` is a center. -/
theorem isCenter_ofClosed_closure_singleton (y : X) (hcl : closure ({y} : Set X) = {y}) :
    (Subscheme.ofClosed ⟨closure {y}, isClosed_closure⟩).IsCenter := by
  right
  refine ⟨Subscheme.isNonsingular_of_stalk_quot _ fun z hz => ?_,
    Subscheme.isIrreducible_of_pts _ ?_⟩
  · rw [Subscheme.pts_ofClosed] at hz
    have hzy : z = y := by
      have : z ∈ closure ({y} : Set X) := hz
      rw [hcl] at this
      exact this
    subst hzy
    rw [stalkIdeal_ofClosed_closure_self]
    exact (inferInstance : IsRegularLocalRing (IsLocalRing.ResidueField (X.presheaf.stalk z)))
  · rw [Subscheme.pts_ofClosed]
    exact isIrreducible_singleton.closure

/-- A closed point of `S_c(ℜ)`, `ν(ℜ) ≤ c`, is a permissible center. -/
theorem isPermissible_ofClosed_closure_singleton {ℜ : DatumII.Raw X} (hℜ : ℜ.IsDatum) {c : ℕ∞}
    (hcν : ℜ.nu ≤ c) {y : X} (hy : y ∈ ℜ.sNu c) (hcl : closure ({y} : Set X) = {y}) :
    ℜ.IsPermissible (Subscheme.ofClosed ⟨closure {y}, isClosed_closure⟩) := by
  have hpts : ∀ x ∈ (Subscheme.ofClosed (⟨closure {y}, isClosed_closure⟩ :
      TopologicalSpace.Closeds X)).pts, x = y := fun x hx => by
    rw [Subscheme.pts_ofClosed] at hx
    have : x ∈ closure ({y} : Set X) := hx
    rw [hcl] at this
    exact this
  refine ⟨isCenter_ofClosed_closure_singleton y hcl, fun x hx => ?_, fun x hx => ?_⟩
  · obtain rfl := hpts x hx
    exact ⟨hy.1, hcν.trans hy.2⟩
  · obtain rfl := hpts x hx
    obtain ⟨z, hz, hcomp, -⟩ := hℜ.2.2.1 x
    exact ⟨z, hz, hcomp, z, subset_rfl, by rw [stalkIdeal_ofClosed_closure_self]; exact hz.1.symm⟩

/-- A monoidal transformation is injective on the complement of the exceptional subscheme
(over the complement of the center it is an isomorphism). -/
theorem injOn_compl_exceptional (t : MonoidalTransformation X B) :
    Set.InjOn t.f.base t.exceptional.ptsᶜ := by
  let U : X.Opens := ⟨B.ptsᶜ, B.support.isClosed.isOpen_compl⟩
  have hBU : Subscheme.totalTransform U.ι B = Subscheme.empty := by
    refine Subscheme.eq_empty_of_pts_eq_empty ?_
    rw [FlatPreimm.pts_totalTransform]
    ext z
    simp only [Set.mem_preimage, Set.mem_empty_iff_false, iff_false]
    exact (U.ι_apply z ▸ z.2 : _)
  have hiso : IsIso (pullback.snd t.f U.ι) := MonoidalTransformation.isIso_of_eq_empty
    (t.baseChange U.ι) hBU
  let k : (U : Scheme) ⟶ t.X' := inv (pullback.snd t.f U.ι) ≫ pullback.fst t.f U.ι
  have hsurj : Function.Surjective (inv (pullback.snd t.f U.ι)).base :=
    (Scheme.homeoOfIso (asIso (inv (pullback.snd t.f U.ι)))).surjective
  have hk : Set.range k.base = t.f.base ⁻¹' (U : Set X) := by
    change Set.range (inv (pullback.snd t.f U.ι) ≫ pullback.fst t.f U.ι).base = _
    rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, hsurj.range_eq, Set.image_univ,
      Scheme.Pullback.range_fst, Scheme.Opens.range_ι]
  have hkf : k ≫ t.f = U.ι := by
    simp [k, pullback.condition]
  have hcompl : t.exceptional.ptsᶜ = t.f.base ⁻¹' (U : Set X) := by
    rw [MonoidalTransformation.pts_exceptional]; rfl
  intro w₁ hw₁ w₂ hw₂ h
  rw [hcompl, ← hk] at hw₁ hw₂
  obtain ⟨u₁, rfl⟩ := hw₁
  obtain ⟨u₂, rfl⟩ := hw₂
  have h1 : U.ι.base u₁ = U.ι.base u₂ := by
    rw [← hkf]
    simpa using h
  rw [U.ι.isOpenEmbedding.injective h1]

/-- Blowing up the closed points of `S_c` one at a time empties it, on a scheme of dimension one
(induction on the number of points; each point leaves `S_c` by Lemma (D.2), and no new point
enters since `f(S_c(f*ℜ)) ⊆ S_c(ℜ)`). -/
theorem exists_permissible_snu_eq_empty_of_dim_eq_one [Hironaka.HironakaCitedResults.{u}] {c : ℕ∞} (hc : 0 < c) :
    ∀ (n : ℕ) (X : Scheme.{u}), IsAmbient X 1 → ∀ (ℜ : DatumII.Raw X), ℜ.IsDatum → ℜ.nu ≤ c →
      (ℜ.sNu c).ncard ≤ n → ∃ (Y : Scheme.{u}) (g : MonoidalSuccession X Y),
        g.IsPermissibleII ℜ ∧ (g.transformII ℜ).sNu c = ∅ := by
  intro n
  induction n with
  | zero =>
    intro X hX ℜ hℜ hcν hn
    refine ⟨X, MonoidalSuccession.nil X, trivial, ?_⟩
    exact (Set.ncard_eq_zero (finite_snu_of_dim_eq_one hX ℜ hℜ c)).mp (Nat.le_zero.mp hn)
  | succ n ih =>
    intro X hX ℜ hℜ hcν hn
    by_cases hZ : ℜ.sNu c = ∅
    · exact ⟨X, MonoidalSuccession.nil X, trivial, hZ⟩
    obtain ⟨y, hy⟩ := Set.nonempty_iff_ne_empty.mpr hZ
    have hcl := closure_singleton_eq_of_mem_snu hX ℜ hℜ hy
    have hB := isPermissible_ofClosed_closure_singleton hℜ hcν hy hcl
    set B : Subscheme X := Subscheme.ofClosed ⟨closure {y}, isClosed_closure⟩ with hBdef
    obtain ⟨t, -⟩ := MonoidalTransformation.exists_isProper X B
    obtain ⟨hX', hd⟩ := (MonoidalSuccession.cons B t (MonoidalSuccession.nil t.X')).isAmbient_transformII
      hX ℜ hℜ ⟨hB, trivial⟩
    have hd' : (ℜ.transform t).IsDatum := hd
    have := hX.1
    have hν' : (ℜ.transform t).nu ≤ c :=
      (DatumII.Raw.nu_transform_le hX.2.1 ℜ hℜ t hB).trans hcν
    -- the points of the new `S_c` are away from `E'` and map injectively into `S_c ∖ {y}`
    have hmap : ∀ w ∈ (ℜ.transform t).sNu c, w ∉ t.exceptional.pts ∧ t.f w ∈ ℜ.sNu c ∧
        t.f w ≠ y := fun w hw => by
      obtain ⟨hwE, hwS, -⟩ := snu_stalkHeight_one_step hX ℜ hℜ B hB t hc hcν hw
        (stalkHeight_eq_one_of_mem_snu hX' _ hd' hw)
      refine ⟨hwE, hwS, fun hwy => hwE ?_⟩
      rw [MonoidalTransformation.pts_exceptional]
      show t.f w ∈ B.pts
      rw [hwy, hBdef, Subscheme.pts_ofClosed]
      exact subset_closure rfl
    have hfin := finite_snu_of_dim_eq_one hX ℜ hℜ c
    have hinj : Set.InjOn t.f.base ((ℜ.transform t).sNu c) := fun a ha b hb h =>
      injOn_compl_exceptional t (hmap a ha).1 (hmap b hb).1 h
    have hsub : t.f.base '' (ℜ.transform t).sNu c ⊆ ℜ.sNu c \ {y} := by
      rintro _ ⟨w, hw, rfl⟩
      exact ⟨(hmap w hw).2.1, (hmap w hw).2.2⟩
    have hcard : ((ℜ.transform t).sNu c).ncard ≤ n := by
      rw [← hinj.ncard_image]
      have h1 := Set.ncard_le_ncard hsub (hfin.sdiff)
      have h2 := Set.ncard_sdiff_singleton_of_mem hy
      omega
    obtain ⟨Y, g, hg, hgS⟩ := ih t.X' hX' (ℜ.transform t) hd' hν' hcard
    exact ⟨Y, MonoidalSuccession.cons B t g, ⟨hB, hg⟩, hgS⟩

/-- The case `N = 1` of the first assertion (a gap in the paper's "immediately"):
for a curve, `S_ν` is a finite set of closed points and each is removed by blowing it up. -/
theorem exists_permissible_noCodimOne_of_eq_one [Hironaka.HironakaCitedResults.{u}]
    (_hII₂ : ∀ N' : ℕ, N' < 1 → FundamentalTheorem.II₂.{u} N')
    (_hI₂ : ∀ n : ℕ, n < 1 → FundamentalTheorem.I₂.{u} 1 n)
    (X : Scheme.{u}) (hX : IsAmbient X 1) (ℜ : DatumII X)
    (hν : 0 < (ℜ : DatumII.Raw X).nu) :
    ∃ (X' : Scheme.{u}) (f : MonoidalSuccession X X'), f.IsPermissibleII ℜ ∧
      NoCodimOneComponent ((f.transformII ℜ).sNu (ℜ : DatumII.Raw X).nu) := by
  obtain ⟨Y, g, hg, hS⟩ := exists_permissible_snu_eq_empty_of_dim_eq_one hν
    ((ℜ : DatumII.Raw X).sNu (ℜ : DatumII.Raw X).nu).ncard X hX ℜ.1 ℜ.2 le_rfl le_rfl
  refine ⟨Y, g, hg, ?_⟩
  rw [hS]
  intro Y' hY'
  exact absurd (hY'.1.1.nonempty.mono hY'.1.2) (by simp)

/-! ### Closed restriction (Theorem C)

"A comparatively trivial observation shows that we may also assume the same for Theorem C"
(p. 314): the same arguments for `S_c(ℜ) ∩ F`. -/

/-- `S_c(ℜ) ∩ F` is closed. -/
theorem isClosed_sNu_closed [Hironaka.HironakaCitedResults.{u}] {N : ℕ} (hX : IsAmbient X N) (ℜ : DatumII.Raw X) (F : Subscheme X)
    (c : ℕ∞) : IsClosed (sNu ℜ (.closed F) c) := by
  have := hX.1
  exact (LocSucc.isClosed_sNu hX.2.1 ℜ c).inter F.support.isClosed

/-- Closed analogue of `noCodimOneComponent_transform`: the stability assertion of p. 314 for
`S_c(ℜ) ∩ F` (the observation "we may also assume the same for Theorem C"). -/
theorem noCodimOneComponent_transform_closed [Hironaka.HironakaCitedResults.{u}] {N : ℕ} (hX : IsAmbient X N) (ℜ : DatumII.Raw X)
    (hℜ : ℜ.IsDatum) (F : Subscheme X) (B : Subscheme X) (hB : ℜ.IsPermissible B)
    (t : MonoidalTransformation X B) {c : ℕ∞} (hc : 0 < c) (hcν : ℜ.nu ≤ c)
    (hno : NoCodimOneComponent (sNu ℜ (.closed F) c)) :
    NoCodimOneComponent (sNu (ℜ.transform t) (.closed (Subscheme.strictTransform t F)) c) := by
  obtain ⟨hXa, hXns, hXirr, -⟩ := id hX
  have hX' : IsAmbient t.X' N :=
    ((MonoidalSuccession.cons B t (MonoidalSuccession.nil t.X')).isAmbient_transformII
      hX ℜ hℜ ⟨hB, trivial⟩).1
  obtain ⟨hXa', hXns', hXirr', -⟩ := id hX'
  intro Y hY hcodim
  have hZ'' := isClosed_sNu_closed hX' (ℜ.transform t) (Subscheme.strictTransform t F) c
  obtain ⟨η, hηY, hηcodim⟩ := exists_generic_point_codim_eq hZ'' hY
  have h1 : stalkHeight η = 1 := hηcodim ▸ hcodim
  have hηS : η ∈ (ℜ.transform t).sNu c ∩ (Subscheme.strictTransform t F).pts := hY.1.2 hηY
  obtain ⟨-, hζ, hζ1⟩ := snu_stalkHeight_one_step hX ℜ hℜ B hB t hc hcν hηS.1 h1
  have hζF : t.f η ∈ F.pts := MonoidalTransformation.pts_strictTransform_subset t F hηS.2
  have hζ' : t.f η ∈ sNu ℜ (.closed F) c := ⟨hζ, hζF⟩
  have hZ' := isClosed_sNu_closed hX ℜ F c
  obtain ⟨Y0, hsub, hY0⟩ := exists_maximal_isIrreducible_of_subset (Z := sNu ℜ (.closed F) c)
    (s := closure {t.f η}) isIrreducible_singleton.closure
    (closure_minimal (Set.singleton_subset_iff.mpr hζ') hZ')
  have hcl0 := isClosed_of_maximal_isIrreducible hZ' hY0
  obtain ⟨ξ, hξ⟩ := QuasiSober.sober hY0.1.1 hcl0
  have hsp : ξ ⤳ t.f η := hξ.specializes (hsub (subset_closure rfl))
  have hξeq : ξ = t.f η := by
    have hle := stalkHeight_le_of_specializes hsp
    rw [hζ1] at hle
    by_cases h : stalkHeight ξ = 1
    · exact eq_of_specializes_of_stalkHeight_le hsp (by rw [h, hζ1])
        (by rw [h]; exact ENat.one_ne_top)
    · exfalso
      have h0 : stalkHeight ξ = 0 := by
        rcases Order.le_one_iff.mp hle with h' | h'
        · exact h'
        · exact absurd h' h
      have hgp : genericPoint X ⤳ ξ := genericPoint_specializes ξ
      have hgp0 : stalkHeight (genericPoint X) = 0 :=
        le_antisymm (h0 ▸ stalkHeight_le_of_specializes hgp) bot_le
      have := eq_of_specializes_of_stalkHeight_le hgp (by rw [h0, hgp0]) (by rw [hgp0]; simp)
      have hξS : ξ ∈ ℜ.S := (hY0.1.2 hξ.mem).1.1
      exact LocSucc.genericPoint_notMem_S hXns ℜ hℜ (this ▸ hξS)
  refine hno Y0 hY0 ?_
  rw [codim_ofClosed_closure_eq_stalkHeight (η := ξ) (by rw [hcl0.closure_eq]; exact hξ.def),
    hξeq]
  exact hζ1

/-- The case `N ≥ 2` of the closed analogue of the first assertion of `lem:IV.4-no-codim-one`
(Proposition 3 of §1 in place of Proposition 4). -/
theorem exists_permissible_noCodimOne_closed_of_two_le [Hironaka.HironakaCitedResults.{u}] (N : ℕ) (hN : 2 ≤ N)
    (hII₁ : ∀ N' : ℕ, N' < N → FundamentalTheorem.II₁.{u} N')
    (hI₂ : ∀ n : ℕ, n < N → FundamentalTheorem.I₂.{u} N n)
    (X : Scheme.{u}) (hX : IsAmbient X N) (ℜ : DatumII X) (F : Subscheme X)
    (hF : (ℜ : DatumII.Raw X).IsClosedRestriction F)
    (hν : 0 < (ℜ : DatumII.Raw X).nu) :
    ∃ (X' : Scheme.{u}) (f : MonoidalSuccession X X'), f.IsPermissibleIIClosed ℜ F ∧
      NoCodimOneComponent (sNu (f.transformII ℜ) (.closed (f.strictTransform F))
        (ℜ : DatumII.Raw X).nu) := by
  obtain ⟨X', f, hf, -, hdim⟩ := exists_isPermissibleIIClosed_finite_image_Snu_dimAt_eq N
    (by omega) hII₁ hI₂ X hX ℜ F hF hν
  obtain ⟨hX', -⟩ := f.isAmbient_transformII hX ℜ.1 ℜ.2 hf.isPermissibleII
  refine ⟨X', f, hf, noCodimOneComponent_of_forall_stalkHeight_ne_one
    (isClosed_sNu_closed hX' _ _ _) fun η hη h1 => ?_⟩
  obtain ⟨-, h2⟩ := snu_stalkHeight_one_composite f hX ℜ.1 ℜ.2 hf.isPermissibleII hν le_rfl hη.1 h1
  have h3 := hdim (f.composite.base η) ⟨η, hη, rfl⟩
  have h4 : X.dimAt (f.composite.base η) =
      ((stalkHeight (f.composite.base η) : ℕ∞) : WithBot ℕ∞) := by
    unfold Scheme.dimAt stalkHeight
    exact (IsLocalRing.maximalIdeal_height_eq_ringKrullDim).symm
  have h5 : stalkHeight (f.composite.base η) = 1 := h2
  rw [h5] at h4
  rw [h4] at h3
  have : (1 : ℕ∞) = (N : ℕ∞) := by exact_mod_cast h3
  have : (1 : ℕ) = N := by exact_mod_cast this
  omega

/-- Blowing up the closed points of `S_c(ℜ) ∩ F` one at a time empties it, on a scheme of
dimension one (closed analogue of `exists_permissible_snu_eq_empty_of_dim_eq_one`). -/
theorem exists_permissible_snu_closed_eq_empty_of_dim_eq_one [Hironaka.HironakaCitedResults.{u}] {c : ℕ∞} (hc : 0 < c) :
    ∀ (n : ℕ) (X : Scheme.{u}), IsAmbient X 1 → ∀ (ℜ : DatumII.Raw X) (F : Subscheme X),
      ℜ.IsDatum → ℜ.IsClosedRestriction F → ℜ.nu ≤ c → (sNu ℜ (.closed F) c).ncard ≤ n →
      ∃ (Y : Scheme.{u}) (g : MonoidalSuccession X Y), g.IsPermissibleIIClosed ℜ F ∧
        sNu (g.transformII ℜ) (.closed (g.strictTransform F)) c = ∅ := by
  intro n
  induction n with
  | zero =>
    intro X hX ℜ F hℜ hF hcν hn
    refine ⟨X, MonoidalSuccession.nil X, trivial, ?_⟩
    exact (Set.ncard_eq_zero ((finite_snu_of_dim_eq_one hX ℜ hℜ c).subset
      Set.inter_subset_left)).mp (Nat.le_zero.mp hn)
  | succ n ih =>
    intro X hX ℜ F hℜ hF hcν hn
    by_cases hZ : sNu ℜ (.closed F) c = ∅
    · exact ⟨X, MonoidalSuccession.nil X, trivial, hZ⟩
    obtain ⟨y, hy⟩ := Set.nonempty_iff_ne_empty.mpr hZ
    have hy1 : y ∈ ℜ.sNu c := hy.1
    have hyF : y ∈ F.pts := hy.2
    have hcl := closure_singleton_eq_of_mem_snu hX ℜ hℜ hy1
    have hB := isPermissible_ofClosed_closure_singleton hℜ hcν hy1 hcl
    set B : Subscheme X := Subscheme.ofClosed ⟨closure {y}, isClosed_closure⟩ with hBdef
    have hBF : ℜ.IsPermissibleClosed F B := ⟨hB, fun x hx => by
      rw [hBdef, Subscheme.pts_ofClosed] at hx
      have : x ∈ closure ({y} : Set X) := hx
      rw [hcl] at this
      rw [Set.mem_singleton_iff.mp this]
      exact hyF⟩
    obtain ⟨t, -⟩ := MonoidalTransformation.exists_isProper X B
    obtain ⟨hX', hd⟩ := (MonoidalSuccession.cons B t
      (MonoidalSuccession.nil t.X')).isAmbient_transformII hX ℜ hℜ ⟨hB, trivial⟩
    have hd' : (ℜ.transform t).IsDatum := hd
    have := hX.1
    have hν' : (ℜ.transform t).nu ≤ c :=
      (DatumII.Raw.nu_transform_le hX.2.1 ℜ hℜ t hB).trans hcν
    have hF' := DatumTransform.isClosedRestriction_transform_datumII hX.2.1 ℜ hℜ t hB F hF hBF
    -- the points of the new `S_c ∩ F'` are away from `E'` and map injectively into `S_c ∩ F ∖ {y}`
    have hmap : ∀ w ∈ sNu (ℜ.transform t) (.closed (Subscheme.strictTransform t F)) c,
        w ∉ t.exceptional.pts ∧ t.f w ∈ sNu ℜ (.closed F) c ∧ t.f w ≠ y := fun w hw => by
      obtain ⟨hwE, hwS, -⟩ := snu_stalkHeight_one_step hX ℜ hℜ B hB t hc hcν hw.1
        (stalkHeight_eq_one_of_mem_snu hX' _ hd' hw.1)
      refine ⟨hwE, ⟨hwS, MonoidalTransformation.pts_strictTransform_subset t F hw.2⟩,
        fun hwy => hwE ?_⟩
      rw [MonoidalTransformation.pts_exceptional]
      show t.f w ∈ B.pts
      rw [hwy, hBdef, Subscheme.pts_ofClosed]
      exact subset_closure rfl
    have hfin : (sNu ℜ (.closed F) c).Finite :=
      (finite_snu_of_dim_eq_one hX ℜ hℜ c).subset Set.inter_subset_left
    have hinj : Set.InjOn t.f.base
        (sNu (ℜ.transform t) (.closed (Subscheme.strictTransform t F)) c) := fun a ha b hb h =>
      injOn_compl_exceptional t (hmap a ha).1 (hmap b hb).1 h
    have hsub : t.f.base '' sNu (ℜ.transform t) (.closed (Subscheme.strictTransform t F)) c ⊆
        sNu ℜ (.closed F) c \ {y} := by
      rintro _ ⟨w, hw, rfl⟩
      exact ⟨(hmap w hw).2.1, (hmap w hw).2.2⟩
    have hcard : (sNu (ℜ.transform t) (.closed (Subscheme.strictTransform t F)) c).ncard ≤ n := by
      rw [← hinj.ncard_image]
      have h1 := Set.ncard_le_ncard hsub (hfin.sdiff)
      have h2 := Set.ncard_sdiff_singleton_of_mem hy
      omega
    obtain ⟨Y, g, hg, hgS⟩ := ih t.X' hX' (ℜ.transform t) (Subscheme.strictTransform t F) hd' hF'
      hν' hcard
    exact ⟨Y, MonoidalSuccession.cons B t g, ⟨hBF, hg⟩, hgS⟩

/-- The case `N = 1` of the closed analogue of the first assertion of `lem:IV.4-no-codim-one`. -/
theorem exists_permissible_noCodimOne_closed_of_eq_one [Hironaka.HironakaCitedResults.{u}]
    (X : Scheme.{u}) (hX : IsAmbient X 1) (ℜ : DatumII X) (F : Subscheme X)
    (hF : (ℜ : DatumII.Raw X).IsClosedRestriction F)
    (hν : 0 < (ℜ : DatumII.Raw X).nu) :
    ∃ (X' : Scheme.{u}) (f : MonoidalSuccession X X'), f.IsPermissibleIIClosed ℜ F ∧
      NoCodimOneComponent (sNu (f.transformII ℜ) (.closed (f.strictTransform F))
        (ℜ : DatumII.Raw X).nu) := by
  obtain ⟨Y, g, hg, hS⟩ := exists_permissible_snu_closed_eq_empty_of_dim_eq_one hν
    (sNu (ℜ : DatumII.Raw X) (.closed F) (ℜ : DatumII.Raw X).nu).ncard X hX ℜ.1 F ℜ.2 hF le_rfl
    le_rfl
  refine ⟨Y, g, hg, ?_⟩
  rw [hS]
  intro Y' hY'
  exact absurd (hY'.1.1.nonempty.mono hY'.1.2) (by simp)

end NoCodimOneInfrastructure

end CD

open CD in
/-- p. 314: "In view of the Localization Theorem (Proposition 4, §1), the above Lemma (D.2)
implies immediately that, `ℜ` and `ν` being as above, there exists a permissible succession of
monoidal transformations `f : X' → X` for `ℜ` such that `S_ν(f*(ℜ))` does not contain any
non-empty component of codimension 1.  Moreover, after this is done, this property continues to
hold by any permissible monoidal transformation."

Formalization note: the assumptions are those of Proposition 4 (`prop:IV.1-4`), which are
among those of Theorem D*.

Deviation from the paper (gap filled): the paper's "implies immediately" is proved.  A point
`η ∈ S_c(f*ℜ)` whose local ring has dimension 1 either lies off the exceptional set `E'`, and
then `f(η)` is again such a point of `S_c(ℜ)`, or lies on `E'`, which would put `E'` inside `S_c`,
excluded by Lemma (D.2).  For `N ≥ 2` this and Proposition 4 give the first assertion; the second
assertion ("continues to hold") is proved for every `N ≥ 1`.  For `N = 1` Proposition 4 and
(D.2) do not suffice (every non-generic point of a curve has dimension 1 = N); Lean instead blows
up the finitely many closed points of `S_ν` one at a time: each leaves `S_ν` by (D.2), no new
point enters (`f(S_c(f*ℜ)) ⊆ S_c(ℜ)`, `f` injective off `E'`), so `S_ν` becomes empty.
Codimension is computed as the dimension of the local ring at the generic point.

The parallel statement for Theorem C ("a comparatively trivial observation shows that we may also
assume the same for Theorem C") is `exists_isPermissibleIIClosed_noCodimOneComponent_Snu` and
`noCodimOneComponent_transform_closed` below. -/
@[blueprint "lem:IV.4-no-codim-one"
  (statement := /-- Let $N\ge1$ and suppose Theorems $\mathrm{II}_2^{N'}$ with $N'<N$ and
    Theorems $\mathrm I_2^{N,n}$ with $n<N$ are verified. Let $\mathfrak R=
    \mathfrak R^N_{\mathrm{II}}$ be a resolution datum on a non-singular irreducible algebraic
    scheme $X$ of dimension $N$, and $\nu=\nu(\mathfrak R)>0$. In view of the Localization
    Theorem (\cref{prop:IV.1-4}), Lemma (D.2) (\cref{lem:IV.D-2}) implies immediately that there
    exists a permissible succession of monoidal transformations $f\colon X'\to X$ for
    $\mathfrak R$ such that $S_\nu(f^*(\mathfrak R))$ does not contain any non-empty component of
    codimension $1$. Moreover, after this is done, this property continues to hold by any
    permissible monoidal transformation. Thus in the proof of Theorem D*, we may assume that
    $S_\nu(\mathfrak R)$ has no non-empty component of codimension $1$ in $X$. (p.~314.)
    The sentence ``A comparatively trivial observation shows that we may also assume the same for
    Theorem C'' (p.~314) is \cref{lem:IV.4-no-codim-one-closed}. -/)
  (proof := /-- By \cref{prop:IV.1-4} there is a permissible succession $f$ with
    $f(S_\nu(f^*(\mathfrak R)))$ a finite set of points at which $X$ has dimension $N$. A
    component of codimension $1$ of $S_\nu(f^*(\mathfrak R))$ maps to one of these points, so it
    lies in the union of the total transforms $E'$ of the centers of $f$ (outside them $f$ is an
    isomorphism, and a point of $X$ is of codimension $N$); an irreducible closed subset of
    codimension $1$ contained in that union of divisors is one of their components, which
    Lemma (D.2) excludes (applied to the monoidal transformation creating it and followed through
    the later transformations, which are isomorphisms at its generic point). For the second
    assertion, a codimension-one component of $S_\nu$ after a permissible monoidal
    transformation is either the strict transform of such a component before it, or a
    component of the new exceptional divisor $E'$, which Lemma (D.2) excludes.

    \textbf{Deviation from the paper (gap filled).} The paper says ``the above Lemma (D.2)
    implies immediately'' (p.~314). Lean proves the propagation step: a point
    $\eta\in S_c(f^*(\mathfrak R))$ whose local ring has dimension $1$ either lies off $E'$, and
    then $f(\eta)$ is such a point of $S_c(\mathfrak R)$, or lies on $E'$, which would force
    $E'\subseteq S_c$, excluded by Lemma (D.2). With \cref{prop:IV.1-4} this gives the first
    assertion for $N\ge2$; the second assertion is proved for every $N\ge1$. Codimension is
    computed as the dimension of the local ring at the generic point.

    \textbf{Deviation from the paper (gap filled, $N=1$).} For $N=1$ the paper's argument does
    not apply: every non-generic point of a curve has dimension $1=N$, so Proposition~4 gives no
    information. Lean blows up the finitely many closed points of $S_\nu$ one at a time; each
    leaves $S_\nu$ by Lemma (D.2), and no new point enters since
    $f(S_c(f^*(\mathfrak R)))\subseteq S_c(\mathfrak R)$ and $f$ is injective off $E'$; so
    $S_\nu$ becomes empty. -/)
  (proofUses := ["prop:IV.1-4", "lem:IV.D-2"])
  (latexEnv := "lemma")]
theorem exists_isPermissibleII_noCodimOneComponent_Snu_and_forall_transform [Hironaka.HironakaCitedResults.{u}] (N : ℕ) (hN : 1 ≤ N)
    (hII₂ : ∀ N' : ℕ, N' < N → FundamentalTheorem.II₂.{u} N')
    (hI₂ : ∀ n : ℕ, n < N → FundamentalTheorem.I₂.{u} N n)
    (X : Scheme.{u}) (hX : IsAmbient X N) (ℜ : DatumII X)
    (hν : 0 < (ℜ : DatumII.Raw X).nu) :
    (∃ (X' : Scheme.{u}) (f : MonoidalSuccession X X'), f.IsPermissibleII ℜ ∧
      NoCodimOneComponent ((f.transformII ℜ).sNu (ℜ : DatumII.Raw X).nu)) ∧
    ∀ (X' : Scheme.{u}) (f : MonoidalSuccession X X'), f.IsPermissibleII ℜ →
      NoCodimOneComponent ((f.transformII ℜ).sNu (ℜ : DatumII.Raw X).nu) →
      ∀ (B : Subscheme X') (t : MonoidalTransformation X' B),
        (f.transformII ℜ).IsPermissible B →
        NoCodimOneComponent (((f.transformII ℜ).transform t).sNu (ℜ : DatumII.Raw X).nu) := by
  refine ⟨?_, fun X' f hf hno B t hB => ?_⟩
  · rcases Nat.lt_or_ge N 2 with h | h
    · obtain rfl : N = 1 := by omega
      exact exists_permissible_noCodimOne_of_eq_one hII₂ hI₂ X hX ℜ hν
    · exact exists_permissible_noCodimOne_of_two_le N h hII₂ hI₂ X hX ℜ hν
  · obtain ⟨hX', hd⟩ := f.isAmbient_transformII hX ℜ.1 ℜ.2 hf
    have := hX.1
    exact noCodimOneComponent_transform hX' _ hd B hB t hν
      (MonoidalSuccession.nu_transformII_le f hX.2.1 ℜ.1 ℜ.2 hf) hno

/-! ## Theorem D* (pp. 314–326), assembled from the core step -/

namespace DatumII.Raw
variable {X : Scheme.{u}}

/-- `E_i` is a closed restriction for the datum it belongs to: it is non-singular irreducible of
codimension one, and `E_1 ∪ ⋯ ∪ E_α ∪ E_i = E_1 ∪ ⋯ ∪ E_α` has only normal crossings. -/
theorem isClosedRestriction_E {ℜ : Raw X} (hℜ : ℜ.IsDatum) (i : Fin ℜ.α) :
    ℜ.IsClosedRestriction (ℜ.E i) := by
  refine ⟨hℜ.2.1 i, ?_⟩
  have : ℜ.eUnion.union (ℜ.E i) = ℜ.eUnion := inf_eq_left.mpr (iInf_le _ i)
  rw [this]
  exact hℜ.2.2.1

/-- Above `ν(ℜ)`, the set `S_c` is empty. -/
theorem sNu_eq_empty_of_nu_lt {ℜ : Raw X} {c : ℕ∞} (h : ℜ.nu < c) : ℜ.sNu c = ∅ := by
  refine Set.eq_empty_iff_forall_notMem.mpr fun x hx => ?_
  have h1 : ℜ.nuAt x ≤ ℜ.nu := le_iSup₂ (f := fun x (_ : x ∈ ℜ.S) => ℜ.nuAt x) x hx.1
  exact absurd (hx.2.trans h1) (not_le.mpr h)

end DatumII.Raw

namespace MonoidalSuccession
variable {X Y : Scheme.{u}}

/-- The `E_j` of the transform (index `Fin (α + s)` in the paper) include the strict transforms
of the original `E_j`. -/
theorem exists_index_E_transformII_eq_strictTransform (g : MonoidalSuccession X Y)
    (ℜ : DatumII.Raw X) (j : Fin ℜ.α) :
    ∃ i : Fin (g.transformII ℜ).α, (g.transformII ℜ).E i = g.strictTransform (ℜ.E j) := by
  induction g with
  | nil X => exact ⟨j, rfl⟩
  | cons B t rest ih =>
    obtain ⟨i, hi⟩ := ih (ℜ.transform t) (Fin.castSucc j)
    refine ⟨i, ?_⟩
    show (rest.transformII (ℜ.transform t)).E i =
      rest.strictTransform (Subscheme.strictTransform t (ℜ.E j))
    rw [hi, CD.E_transform_castSucc]

end MonoidalSuccession

namespace DatumII.Raw
variable {X : Scheme.{u}}

theorem E_eq_of_eq {R₁ R₂ : Raw X} (h : R₁ = R₂) {i : Fin R₁.α} {j : Fin R₂.α}
    (hij : (i : ℕ) = j) : R₁.E i = R₂.E j := by
  subst h
  rw [Fin.ext hij]

/-- The empty subscheme is a permissible center of every datum (p. 168). -/
theorem isPermissible_empty (ℜ : Raw X) : ℜ.IsPermissible (Subscheme.empty : Subscheme X) :=
  ⟨Or.inl rfl, by rw [Subscheme.pts_empty]; exact Set.empty_subset _,
    fun x hx => by rw [Subscheme.pts_empty] at hx; exact hx.elim⟩

end DatumII.Raw

namespace MonoidalSuccession
variable {X Y : Scheme.{u}}

theorem snoc_eq_append (g : MonoidalSuccession X Y) (B : Subscheme Y)
    (t : MonoidalTransformation Y B) :
    g.snoc B t = g.append (cons B t (nil t.X')) := by
  induction g with
  | nil X => rfl
  | cons B' t' rest ih => exact congrArg (cons B' t') (ih B t)

theorem isPermissibleII_snoc_iff (g : MonoidalSuccession X Y) (B : Subscheme Y)
    (t : MonoidalTransformation Y B) (ℜ : DatumII.Raw X) :
    (g.snoc B t).IsPermissibleII ℜ ↔ g.IsPermissibleII ℜ ∧ (g.transformII ℜ).IsPermissible B := by
  rw [snoc_eq_append, isPermissibleII_append]
  simp [IsPermissibleII]

theorem isPermissibleIIClosed_snoc_iff (g : MonoidalSuccession X Y) (B : Subscheme Y)
    (t : MonoidalTransformation Y B) (ℜ : DatumII.Raw X) (F : Subscheme X) :
    (g.snoc B t).IsPermissibleIIClosed ℜ F ↔ g.IsPermissibleIIClosed ℜ F ∧
      (g.transformII ℜ).IsPermissibleClosed (g.strictTransform F) B := by
  rw [snoc_eq_append, isPermissibleIIClosed_append]
  simp [IsPermissibleIIClosed]

end MonoidalSuccession

namespace CD
variable {X : Scheme.{u}}

/-- Theorem II₁^N applied finitely many times (p. 320: "for the case in which `ℜ = ℜ^N_II`
without restriction, by applying Theorem II₁^N a finite number of times (in fact, at most `α`
times), we may assume that [(2)] `E_i(s) ∩ S_ν(ℜ(s))` is empty for `1 ≤ i ≤ α`"), for any finite
set `I` of indices. -/
theorem exists_isPermissibleII_inter_strictTransform_sNu_eq_empty [Hironaka.HironakaCitedResults.{u}] {N : ℕ}
    (hII₁ : FundamentalTheorem.II₁.{u} N) (X : Scheme.{u}) (hX : IsAmbient X N)
    (ℜ : DatumII.Raw X) (hℜ : ℜ.IsDatum) (hν : 0 < ℜ.nu) (I : Finset (Fin ℜ.α)) :
    ∃ (Y : Scheme.{u}) (g : MonoidalSuccession X Y), g.IsPermissibleII ℜ ∧
      ∀ i ∈ I, (g.strictTransform (ℜ.E i)).pts ∩ (g.transformII ℜ).sNu ℜ.nu = ∅ := by
  classical
  induction I using Finset.induction_on with
  | empty => exact ⟨X, MonoidalSuccession.nil X, trivial, by simp⟩
  | insert j I hj ih =>
    obtain ⟨Y₁, g₁, hg₁, hI⟩ := ih
    obtain ⟨hX₁, hd₁⟩ := g₁.isAmbient_transformII hX ℜ hℜ hg₁
    have := hX.1
    have hν₁ : (g₁.transformII ℜ).nu ≤ ℜ.nu :=
      MonoidalSuccession.nu_transformII_le g₁ hX.2.1 ℜ hℜ hg₁
    by_cases hlt : (g₁.transformII ℜ).nu < ℜ.nu
    · refine ⟨Y₁, g₁, hg₁, fun i hi => ?_⟩
      rw [DatumII.Raw.sNu_eq_empty_of_nu_lt hlt, Set.inter_empty]
    · have heq : (g₁.transformII ℜ).nu = ℜ.nu := le_antisymm hν₁ (not_lt.mp hlt)
      obtain ⟨i₀, hi₀⟩ := g₁.exists_index_E_transformII_eq_strictTransform ℜ j
      have hF := DatumII.Raw.isClosedRestriction_E hd₁ i₀
      rw [hi₀] at hF
      obtain ⟨Y₂, e, he, hdisj⟩ := hII₁ Y₁ hX₁ ⟨g₁.transformII ℜ, hd₁⟩
        (g₁.strictTransform (ℜ.E j)) hF (by show 0 < (g₁.transformII ℜ).nu; rw [heq]; exact hν)
      refine ⟨Y₂, g₁.append e, (MonoidalSuccession.isPermissibleII_append g₁ e ℜ).mpr
        ⟨hg₁, he.isPermissibleII⟩, fun i hi => ?_⟩
      rw [MonoidalSuccession.transformII_append, MonoidalSuccession.strictTransform_append]
      rcases Finset.mem_insert.mp hi with rfl | hiI
      · rw [← heq]
        exact hdisj
      · refine Set.eq_empty_iff_forall_notMem.mpr fun y hy => ?_
        have := hX₁.1
        have h1 := MonoidalSuccession.pts_strictTransform_subset e _ hy.1
        have h2 := MonoidalSuccession.mem_sNu_of_mem_sNu_transformII e hX₁.2.1 _ hd₁ he.isPermissibleII
          hy.2
        exact (Set.eq_empty_iff_forall_notMem.mp (hI i hiI)) (e.composite.base y) ⟨h1, h2⟩

/-- The image in `X` of `S_ν(g*(ℜ))`: `h_s(S_ν(ℜ(s)))` of p. 320. -/
def sNuImage {Y : Scheme.{u}} (g : MonoidalSuccession X Y) (ℜ : DatumII.Raw X) (ν : ℕ∞) :
    Set X :=
  g.composite.base '' (g.transformII ℜ).sNu ν

/-- Further permissible transformations do not enlarge `h_s(S_ν(ℜ(s)))` (p. 283: "`f(S_i(f*ℜ)) ⊆
S_i(ℜ)`"). -/
theorem sNuImage_append_subset [Hironaka.HironakaCitedResults.{u}] {N : ℕ} {Y Z : Scheme.{u}} (hX : IsAmbient X N)
    (ℜ : DatumII.Raw X) (hℜ : ℜ.IsDatum) (g : MonoidalSuccession X Y) (hg : g.IsPermissibleII ℜ)
    (e : MonoidalSuccession Y Z) (he : e.IsPermissibleII (g.transformII ℜ)) (ν : ℕ∞) :
    sNuImage (g.append e) ℜ ν ⊆ sNuImage g ℜ ν := by
  obtain ⟨hY, hd⟩ := g.isAmbient_transformII hX ℜ hℜ hg
  have := hY.1
  rintro _ ⟨y, hy, rfl⟩
  rw [MonoidalSuccession.transformII_append] at hy
  refine ⟨e.composite.base y, MonoidalSuccession.mem_sNu_of_mem_sNu_transformII e hY.2.1 _ hd he hy,
    ?_⟩
  rw [MonoidalSuccession.composite_append, Scheme.Hom.comp_base, TopCat.coe_comp]
  rfl

end CD

/-! ## The running setup (pp. 314–316) -/

namespace CD

variable {X : Scheme.{u}}

/-- The transform of a type II datum along `g` followed by `t` is the transform by `t` of the
transform along `g` (Definition 8; the type II analogue of `MonoidalSuccession.transformI_snoc`). -/
theorem _root_.Hironaka.MonoidalSuccession.transformII_snoc {X Y : Scheme.{u}} (g : MonoidalSuccession X Y) (B : Subscheme Y)
    (t : MonoidalTransformation Y B) (ℜ : DatumII.Raw X) :
    (MonoidalSuccession.snoc g B t).transformII ℜ = (g.transformII ℜ).transform t := by
  induction g with
  | nil X => rfl
  | cons B' t' rest ih => exact ih B t (ℜ.transform t')

/-- `ℜ^N_II(s)`: the transform of `ℜ^N_II` along `h_s = {f_t}_{0 ≤ t < s}` (p. 314:
"`ℜ^N_II(0) = ℜ^N_II`, … `ℜ^N_II(s+1) = f_s*(ℜ^N_II(s))`"). -/
def datum (T : AB.Tower X) (ℜ : DatumII.Raw X) (s : ℕ) : DatumII.Raw (T.X s) :=
  (T.pre s).transformII ℜ

/-- The restriction of `ℜ(s)`: `F(s)`, the strict transform of `F` along `h_s` (p. 314), or no
restriction. -/
def restriction (T : AB.Tower X) (r : Restriction X) (s : ℕ) : Restriction (T.X s) :=
  r.transformSucc (T.pre s)

/-- `ℜ^N_II(s)` has `α + s` members `E_i(s)` (Definition 7 (II), iterated). -/
theorem alpha_datum (T : AB.Tower X) (ℜ : DatumII.Raw X) : ∀ s, (datum T ℜ s).α = ℜ.α + s
  | 0 => rfl
  | s + 1 => by
    show ((MonoidalSuccession.snoc (T.pre s) (T.B s) (T.monoidalTransformation s)).transformII ℜ).α = ℜ.α + (s + 1)
    rw [Hironaka.MonoidalSuccession.transformII_snoc]
    show (datum T ℜ s).α + 1 = ℜ.α + (s + 1)
    rw [alpha_datum T ℜ s]
    rfl

/-- p. 314: the subschemes `E_1(s), …, E_{α+s}(s)` of `ℜ^N_II(s)`: "`E_i(0) = E_i`
(`1 ≦ i ≦ α`), `E_i(s+1)` = the strict transform of `E_i(s)` in `X_{s+1}` (`1 ≦ i ≦ α + s`), and
`E_{α+s+1}(s+1)` = the total transform of `B_s` in `X_{s+1}`", which is how Definition 7 (II)
forms them. -/
def eSeq (T : AB.Tower X) (ℜ : DatumII.Raw X) (s : ℕ) : Fin (ℜ.α + s) → Subscheme (T.X s) :=
  fun j => (datum T ℜ s).E (Fin.cast (alpha_datum T ℜ s).symm j)

/-- The integers `a_1, …, a_{α+s}` of `ℜ^N_II(s)` (p. 314). -/
def aSeq (T : AB.Tower X) (ℜ : DatumII.Raw X) (s : ℕ) : Fin (ℜ.α + s) → ℕ :=
  fun j => (datum T ℜ s).a (Fin.cast (alpha_datum T ℜ s).symm j)

/-- The standing assumptions of pp. 314–315. -/
@[blueprint "def:IV.4-standing"
  (statement := /-- The standing assumptions of pp.~314--315: $X$ is a non-singular irreducible
    algebraic scheme of dimension $N\ge1$ and $\mathfrak R$ is a resolution datum on $X$ which is
    either $(\mathfrak R^N_{\mathrm{II}},F)$ with closed restriction $F$ or
    $\mathfrak R^N_{\mathrm{II}}=\big(E_1,\dots,E_\alpha\,\big|\,J,b\,\big|\,a_1,\dots,a_\alpha
    \big)$ without restriction; $\nu=\nu(\mathfrak R)=\nu(\mathfrak R^N_{\mathrm{II}})>0$ (the
    assumption of Theorems C and D*, \cref{thm:IV.C}, \cref{thm:IV.D-star}); $S_\nu(\mathfrak R)$
    has no non-empty component of codimension $1$ in $X$ (``we shall prove Theorem C and Theorem
    D* under the above assumption'', \cref{lem:IV.4-no-codim-one}). ``Let us first fix and study
    an arbitrary permissible succession of monoidal transformations of $X$ for $\mathfrak R$
    \dots, say $\{f_s\colon X_{s+1}\to X_s\}$ $(s\ge0)$, where $X_0=X$. Let $B_s$ denote the center
    of the monoidal transformation $f_s$ in $X_s$. Let $\mathfrak R(s)$ and
    $\mathfrak R^N_{\mathrm{II}}(s)$ be the resolution data on $X_s$ $(s\ge0)$ which are defined as
    follows: $\mathfrak R(0)=\mathfrak R$, $\mathfrak R^N_{\mathrm{II}}(0)=
    \mathfrak R^N_{\mathrm{II}}$, $\mathfrak R(s+1)=f_s^*(\mathfrak R(s))$, and
    $\mathfrak R^N_{\mathrm{II}}(s+1)=f_s^*(\mathfrak R^N_{\mathrm{II}}(s))$ for all $s\ge0$. Let us
    write $\mathfrak R^N_{\mathrm{II}}(s)=\big(E_1(s),\dots,E_{\alpha+s}(s)\,\big|\,J(s),b\,\big|\,
    a_1,\dots,a_{\alpha+s}\big)$ where $E_i(0)=E_i$ $(1\le i\le\alpha)$, $E_i(s+1)=$ the strict
    transform of $E_i(s)$ in $X_{s+1}$ $(1\le i\le\alpha+s)$, and $E_{\alpha+s+1}(s+1)=$ the total
    transform of $B_s$ in $X_{s+1}$ $(s\ge0)$. If $\mathfrak R=(\mathfrak R^N_{\mathrm{II}},F)$, we
    shall write $\mathfrak R(s)=(\mathfrak R^N_{\mathrm{II}}(s),F(s))$ so that $F(s+1)=$ the strict
    transform of $F(s)$ for all $s\ge0$ where $F(0)=F$. Let us choose and fix an arbitrary point
    $x_0$ of $X_0$ at which $X$ has dimension $N$ and which is contained in $S_\nu(\mathfrak R)$
    $(\nu=\nu(\mathfrak R)>0)$'' (p.~314, \cref{def:IV.4-symbols}). We denote by $h_s$ the
    succession of the $f_t$ for $0\le t\le s-1$ (\cref{lem:IV.CD-3}). (Formalization notes (encoding): the
    succession is the $\mathbb N$-indexed succession of \cref{def:IV.3-succession}, a finite one
    having eventually empty centers; $\mathfrak R^N_{\mathrm{II}}(s)$, $E_i(s)$, $a_i$, $J(s)$
    and $F(s)$ are formed along $h_s$ by \cref{def:I.7-II}, \cref{def:I.8}.) -/)
  (latexEnv := "definition")]
structure Standing (N : ℕ) (ℜ : DatumII.Raw X) (r : Restriction X) (ν : ℕ) (T : AB.Tower X)
    (x₀ : X) : Prop where
  /-- `N ≧ 1`. -/
  one_le : 1 ≤ N
  /-- `X` is a non-singular irreducible algebraic scheme of dimension `N`. -/
  ambient : IsAmbient X N
  /-- `ℜ^N_II` is a resolution datum. -/
  isDatum : ℜ.IsDatum
  /-- `F` is a closed restriction for `ℜ^N_II` (if there is one). -/
  isFor : r.IsFor ℜ
  /-- `ν = ν(ℜ)`. -/
  nu_eq : (ν : ℕ∞) = nu ℜ r
  /-- `ν = ν(ℜ^N_II)` (Theorem C; automatic without restriction). -/
  nu_eq_II : (ν : ℕ∞) = ℜ.nu
  /-- `ν > 0`. -/
  nu_pos : 0 < ν
  /-- `S_ν(ℜ)` has no non-empty component of codimension one in `X` (p. 314). -/
  noCodimOne : NoCodimOneComponent (sNu ℜ r ν)
  /-- The succession `{f_s}` is permissible for `ℜ`: each initial segment `h_s` is. -/
  permissible : ∀ s, r.IsPermissibleSucc (T.pre s) ℜ
  /-- `X` has dimension `N` at `x_0`. -/
  dimAt_x₀ : X.dimAt x₀ = (N : WithBot ℕ∞)
  /-- `x_0 ∈ S_ν(ℜ)`. -/
  mem_Snu : x₀ ∈ sNu ℜ r ν

variable {N : ℕ} {ℜ : DatumII.Raw X} {r : Restriction X} {ν : ℕ} {T : AB.Tower X} {x₀ : X}

/-- The closed point `x̂_0` of `X̂_0 = Spec(Ŝ_0)` (p. 314). -/
def Standing.xh (hS : Standing N ℜ r ν T x₀) : AB.xHat0 X x₀ :=
  AB.xhat0 X x₀ (hS.ambient.2.1 x₀)

/-- p. 314: "Let us write `J_0` for the stalk `J_{x_0}` of `J` at `x_0`.  Let `M_0` denote the
maximal ideal of `S_0`.  Then we have `ν_{M_0}(J_0) = ν`." -/
@[blueprint "lem:IV.4-nu-J0"
  (statement := /-- Under the standing assumptions (\cref{def:IV.4-standing}), let $S_0$ be the
    local ring of $X_0$ at $x_0$, $J_0$ the stalk $J_{x_0}$ of $J$ at $x_0$, and $M_0$ the maximal
    ideal of $S_0$. Then we have $\nu_{M_0}(J_0)=\nu$ (\cref{def:order-nu}). (p.~314.) -/)
  (proof := /-- $x_0\in S_\nu(\mathfrak R)$ gives $x_0\in S(\mathfrak R)$ and
    $\nu(J_{x_0})\ge\nu$, and $\nu(J_{x_0})\le\max_{x\in S(\mathfrak R)}\nu(J_x)=\nu(\mathfrak R)
    =\nu$. -/)
  (latexEnv := "lemma")]
theorem Standing.nu_stalkIdeal_J_eq (hS : Standing N ℜ r ν T x₀) : Ideal.nu (ℜ.J.stalkIdeal x₀) = ν := by
  obtain ⟨hS1, hν⟩ := (mem_Snu_iff _ _ _ _).1 hS.mem_Snu
  refine le_antisymm ?_ hν
  rw [hS.nu_eq]
  exact nuAt_le_nu ℜ r hS1

/-- `Ĵ_0 = J_0 Ŝ_0` (p. 315). -/
def jHat0 (ℜ : DatumII.Raw X) (x₀ : X) : Ideal (AB.Shat X x₀) :=
  (ℜ.J.stalkIdeal x₀).map (algebraMap (X.presheaf.stalk x₀) (AB.Shat X x₀))

open Classical in
/-- The choices `[0]`, `[i]`–`[iv]`, `[iii]'` of p. 315 on the data `z = z_0` and `Jgen` (the set
of the elements `g_{ji}^{b̄/i}` of `Ŝ_0`, `b̄ = ν!`, whose images generate `J̄_0`, `[v]`, `[vi]`):
there are a regular frame `(T_0; z_0)` of `Ŝ_0` (`r = 1`), a field `k ⊆ T_0` and a system
`(y_1, …, y_{N-1})` with `T_0 = k{y_1, …, y_{N-1}}` and `(z_0, y_1, …, y_{N-1})` a regular system
of parameters of `Ŝ_0`, and a base `(g_1, …, g_m)` of `Ĵ_0` with `ν_{M_0}(g_j) = ν` and
`g_j = z_0^ν + g_{j1} z_0^{ν-1} + ⋯ + g_{jν}`, `g_{ji} ∈ T_0`, and `g_{11} = 0` without
restriction. -/
def FrameSpec (N : ℕ) (x₀ : X) (ℜ : DatumII.Raw X) (r : Restriction X) (ν : ℕ)
    [IsRegularLocalRing (AB.Shat X x₀)] (z : AB.Shat X x₀) (Jgen : Set (AB.Shat X x₀)) : Prop :=
  ∃ (Fr : RegularFrame (AB.Shat X x₀)) (h1 : Fr.r = 1),
    Fr.z ⟨0, by rw [h1]; exact Nat.one_pos⟩ = z ∧
    -- [i]
    (∀ F, r = .closed F → ∃ z₀ : X.presheaf.stalk x₀,
      algebraMap (X.presheaf.stalk x₀) (AB.Shat X x₀) z₀ = z ∧
        F.stalkIdeal x₀ = Ideal.span {z₀}) ∧
    -- [ii]
    (∃ (kk : Subring Fr.S) (_ : IsField kk) (y : Fin (N - 1) → Fr.S)
      (e : Fr.S ≃+* MvPowerSeries (Fin (N - 1)) kk),
      (∀ c : kk, e (c : Fr.S) = MvPowerSeries.C c) ∧ (∀ i, e (y i) = MvPowerSeries.X i) ∧
      IsRegularSystemOfParameters (AB.Shat X x₀)
        (insert z (Finset.image (fun i => algebraMap Fr.S (AB.Shat X x₀) (y i)) Finset.univ))) ∧
    -- [0], [iii]', [iv], [vi]
    ∃ (m : ℕ) (g : Fin m → AB.Shat X x₀) (co : Fin m → Fin ν → Fr.S),
      Ideal.span (Set.range g) = jHat0 ℜ x₀ ∧
      (∀ j, Ideal.ordElem (maximalIdeal (AB.Shat X x₀)) (g j) = ν) ∧
      (∀ j, g j = z ^ ν + ∑ i : Fin ν,
        algebraMap Fr.S (AB.Shat X x₀) (co j i) * z ^ (ν - ((i : ℕ) + 1))) ∧
      (r = .unrestricted → ∃ (hm : 0 < m) (hν : 0 < ν), co ⟨0, hm⟩ ⟨0, hν⟩ = 0) ∧
      Jgen = {w | ∃ (j : Fin m) (i : Fin ν),
        w = algebraMap Fr.S (AB.Shat X x₀) (co j i) ^ (ν.factorial / ((i : ℕ) + 1))}

/-- pp. 314–316: the completion `Ŝ_0`, the induced succession `{f̂_s}` of `X̂_0 = Spec(Ŝ_0)` with
the morphisms `c_s`, the frame `(T_0; z_0)` and base of p. 315, and the morphisms
`f̄_s : X̄_{s+1} → X̄_s` induced by `f̂_s` (p. 316).

Formalization notes: `Ŝ_0`, `X̂_0`, `c_0`, `x̂_0` are those of §3 (`AB.Shat`, `AB.xHat0`, `AB.c0`,
`AB.xhat0`); the induced succession and the `c_s` are an `AB.Completion` (which also records
`X̂_s = X_s ×_X Spec(Ŝ_0)`, used on p. 320); the regularity of `Ŝ_0` is a field; the choices of
p. 315 are recorded existentially (`CD.FrameSpec`), the data kept being `z_0` and the set of the
`g_{ji}^{b̄/i}`; the `f̄_s` are data subject to `ι ∘ f̄_s = f̂_s ∘ ι`.  Existence:
`lem:IV.4-setup-exists`. -/
@[blueprint "def:IV.4-frame"
  (statement := /-- Under the standing assumptions (\cref{def:IV.4-standing}): let $S_0$ denote
    the local ring of $X_0$ at $x_0$ and $\hat S_0$ the completion of $S_0$. Let $\hat X_0=
    \operatorname{Spec}(\hat S_0)$ and $c_0\colon\hat X_0\to X_0$ the canonical morphism
    associated with the canonical local homomorphism $S_0\to\hat S_0$; $\hat x_0$ is the unique
    closed point of $\hat X_0$, so that $c_0(\hat x_0)=x_0$. Let $\hat J_0=J_0\hat S_0$, and
    choose and fix a base of $\hat J_0$, say [0] $(g_1,\dots,g_m)\hat S_0=\hat J_0$, such that
    $\nu_{M_0}(g_j)=\nu$ for all $j$ $(1\le j\le m)$. The complete regular local ring $S_0$
    [sic; $\hat S_0$] contains a field $k$ such that $\hat S_0$ is a formal power series ring of
    $N$ variables over $k$. We fix such a subfield $k$ of $\hat S_0$. Let us choose and fix a
    regular frame $(T_0;z_0)$ of $S_0$ [sic; $\hat S_0$] (\cref{def:III.9}) as follows: [i] If
    $\mathfrak R=(\mathfrak R^N_{\mathrm{II}},F)$, then $z_0$ is an element of $S_0$ which
    generates the ideal of $F$ in $S_0$ (hence, the ideal of $c_0^{-1}(F)$ in $\hat S_0$). [ii]
    $T_0$ is a formal power series [ring] of $N-1$ variables $(y_1,\dots,y_{N-1})$ over $k$ such
    that $(z_0,y_1,\dots,y_{N-1})$ is a regular system of parameters of $\hat S_0$. [iii]
    $(y_1,\dots,y_{N-1})$ is so chosen that each $g_i$ [sic; $g_j$] can be written in the form
    $g_j=u_j(z_0^\nu+g_{j1}z_0^{\nu-1}+\dots+g_{j\nu})$ where $u_j$ is a unit of $\hat S_0$ and
    $g_{ji}\in T_0$ $(1\le j\le m,\ 1\le i\le\nu)$. [iv] If $\mathfrak R=
    \mathfrak R^N_{\mathrm{II}}$ without restriction, then $z_0$ is so chosen that $g_{11}=0$,
    i.e., $g_1=u_1(z_0^\nu+g_{12}z_0^{\nu-2}+\dots+g_{1\nu})$. (In [iii] we replace $z_0$ by
    $z_0+(1/\nu)g_{11}$.) We may assume without any loss of generality that $u_j=1$ for all $j$.
    We have [0] $\hat J_0=(g_1,\dots,g_m)\hat S_0$, and [iii]'
    $g_j=z_0^\nu+g_{j1}z_0^{\nu-1}+\dots+g_{j\nu}$ $(1\le j\le m)$ ($g_{11}=0$ if $\mathfrak R=
    \mathfrak R^N_{\mathrm{II}}$) where $g_{ji}\in T_0$. We define a sequence of non-singular
    irreducible algebraic schemes $\hat X_s$ $(s\ge0)$ (over the complete regular local ring
    $\hat S_0$): we have commutative diagrams $c_s\circ\hat f_s=f_s\circ c_{s+1}$ of canonical
    morphisms $(s\ge0)$ where $\hat f_s$ is the monoidal transformation of $X_s$ [sic;
    $\hat X_s$] with the non-singular irreducible center $\hat B_s=c_s^{-1}(B_s)$
    (\cref{def:IV.3-setup}). (pp.~314--315.) Let $\bar T_0=\hat S_0/(z_0)\hat S_0$ and
    $\bar X_0=\operatorname{Spec}(\bar T_0)$; let $\bar X_s$ be the strict transform of $\bar X_0$
    in $\hat X_s$ by the succession $\hat h_s\colon\hat X_s\to\hat X_0$; the morphism $\hat f_s$
    induces a morphism $\bar f_s\colon\bar X_{s+1}\to\bar X_s$. (p.~316.) (Formalization notes
    (encoding):
    the regularity of $\hat S_0$ is recorded as a hypothesis; the choices [0], [i]--[iv], [iii]'
    are recorded existentially, the data kept being $z_0$ and the lifts
    $g_{ji}^{\bar b/i}\in\hat S_0$ of the generators of $\bar J_0$ (\cref{def:IV.4-construction});
    ``$T_0$ is a formal power series ring over $k$'' is an isomorphism
    $T_0\simeq k\{y_1,\dots,y_{N-1}\}$ fixing $k$ and sending $y_i$ to the $i$th variable, $k$
    being recorded as a subring of $T_0$ which is a field;
    $\nu_{M_0}(g_j)$ is the order for the maximal ideal $M_0\hat S_0$ of $\hat S_0$; the
    morphisms $\bar f_s$ are recorded as data; everything exists by
    \cref{lem:IV.4-setup-exists}.)

    \textbf{Paper misprint.} On pp.~314--315 the paper writes ``the complete regular local ring
    $S_0$'' and ``a regular frame $(T_0;z_0)$ of $S_0$'' for $\hat S_0$, ``each $g_i$'' for $g_j$,
    and ``the monoidal transformation of $X_s$'' for $\hat X_s$ (marked [sic] above). -/)
  (latexEnv := "definition")]
structure Frame (hS : Standing N ℜ r ν T x₀) extends AB.Completion T x₀ where
  /-- `Ŝ_0` is a regular local ring. -/
  [regShat : IsRegularLocalRing (AB.Shat X x₀)]
  /-- The element `z_0` of the regular frame `(T_0; z_0)`. -/
  z : AB.Shat X x₀
  /-- The elements `g_{ji}^{b̄/i}` of `Ŝ_0` whose images generate `J̄_0` (`[vi]`). -/
  jGen : Set (AB.Shat X x₀)
  /-- `[0]`, `[i]`–`[iv]`, `[iii]'`, `[vi]`. -/
  frame : FrameSpec N x₀ ℜ r ν z jGen
  /-- The morphisms `f̄_s : X̄_{s+1} → X̄_s` induced by `f̂_s`. -/
  fBar : ∀ s, (AB.strictTransformZeroLocus tHat z (s + 1)).toScheme ⟶ (AB.strictTransformZeroLocus tHat z s).toScheme
  /-- `f̄_s` is induced by `f̂_s`. -/
  fBar_comm : ∀ s, fBar s ≫ (AB.strictTransformZeroLocus tHat z s).ι = (AB.strictTransformZeroLocus tHat z (s + 1)).ι ≫ tHat.f s

namespace Frame

variable {hS : Standing N ℜ r ν T x₀} (𝒮 : Frame hS)

/-- `X̄_s`, the strict transform of `X̄_0 = Spec(Ŝ_0/(z_0)Ŝ_0)` in `X̂_s` (p. 316). -/
abbrev xBar (s : ℕ) : Subscheme (𝒮.tHat.X s) := AB.strictTransformZeroLocus 𝒮.tHat 𝒮.z s

/-- `c̄_s : X̄_s → X_s`, induced by `c_s` (p. 321). -/
def cBar (s : ℕ) : (𝒮.xBar s).toScheme ⟶ T.X s := (𝒮.xBar s).ι ≫ 𝒮.c s

/-- `[v]`: `b̄ = ν!`. -/
def bBar (_𝒮 : Frame hS) : ℕ := ν.factorial

/-- The sheaf of prime ideals of `B̂_s = c_s⁻¹(B_s)` on `X̄_s` (`[vii]` (3)). -/
def bBarOn (s : ℕ) : Subscheme (𝒮.xBar s).toScheme :=
  Subscheme.totalTransform (𝒮.xBar s).ι (𝒮.tHat.B s)

/-- `[vii]`: `P̄_{s+1}`, the sheaf of ideals of the subscheme `c_{s+1}⁻¹(E_{α+s+1}(s+1)) ∩ X̄_{s+1}`
of `X̄_{s+1}`, `E_{α+s+1}(s+1) = f_s⁻¹(B_s)` (the paper prints `c_s⁻¹`, a paper misprint). -/
def pBar (s : ℕ) : Subscheme (𝒮.xBar (s + 1)).toScheme :=
  Subscheme.totalTransform (𝒮.xBar (s + 1)).ι
    (Subscheme.totalTransform (𝒮.c (s + 1)) (Subscheme.totalTransform (T.f s) (T.B s)))

/-- `[vi]`: `J̄(0)`, generated by `J̄_0 = (g_{ji}^{b̄/i}) T̄_0`. -/
def jBar0 : Subscheme (𝒮.xBar 0).toScheme :=
  Subscheme.totalTransform (𝒮.xBar 0).ι (Scheme.IdealSheafData.ofIdealTop
    ((Ideal.span 𝒮.jGen).map (Scheme.ΓSpecIso (CommRingCat.of (AB.Shat X x₀))).inv.hom))

/-- `[vi]`, `[vii]`: `J̄(0)` and `J̄(s+1) = f̄_s⁻¹(J̄(s))/(P̄_{s+1})^{b̄}`, formed for all `s` (the
paper defines `J̄(s+1)` when the conditions (1)–(3) of `[vii]` hold at `s`). -/
@[blueprint "def:IV.4-construction"
  (statement := /-- Notation as in \cref{def:IV.4-frame}. Let $\bar T_0=\hat S_0/(z_0)\hat S_0$,
    which is an isomorphic image of the subring $T_0$ of $S_0$ [sic; $\hat S_0$]. Let
    $\bar X_0=\operatorname{Spec}(\bar T_0)$, which is a non-singular irreducible subscheme of
    $\hat X_0$ of codimension $1$. We define a positive integer $\bar b$ and a coherent sheaf of
    ideals $\bar J(0)$ on $\bar X_0$ as follows: [v] $\bar b=\nu!$, and [vi] $\bar J(0)$ is
    generated by the ideal $\bar J_0=(g_{ji}^{\bar b/i})\bar T_0$ in $\bar T_0$, which denotes the
    ideal generated by the images in $\bar T_0$ of the $(\bar b/i)$th powers of $g_{ji}\in T_0$
    for $1\le j\le m$ and $1\le i\le\nu$. Let $\bar X_s$ be the strict transform of $\bar X_0$ in
    $\hat X_s$ by the succession $\hat h_s\colon\hat X_s\to\hat X_0$ for all $s\ge0$. Then
    $\bar X_s$ is an irreducible reduced subscheme of $\hat X_s$ and, for each $s\ge0$, the
    morphism $\hat f_s$ (resp.\ $\hat h_s$) induces a morphism $\bar f_s\colon\bar X_{s+1}\to\bar
    X_s$ (resp.\ $\bar h_s\colon\bar X_s\to\bar X_0$). [vii] We define a coherent sheaf of ideals
    $\bar J(s)$ on $\bar X_s$ by induction on $s\ge0$ as follows: If, for a certain integer
    $s\ge0$, (1) $\bar X_s$ is non-singular and irreducible, (2) $\hat B_s$ is contained in
    $\bar X_s$, so that the morphism $\bar f_s\colon\bar X_{s+1}\to\bar X_s$ is obtained by the
    monoidal transformation of $\bar X_s$ with the non-singular center $\hat B_s$, and (3)
    $\bar J(s)$ is defined and contained in the $\bar b$th power of the sheaf of prime ideals of
    $\hat B_s$ on $\bar X_s$, then we define $\bar J(s+1)=\bar f_s^{-1}(\bar J(s))/
    (\bar P_{s+1})^{\bar b}$, where $\bar P_{s+1}$ denotes the sheaf of invertible ideals of the
    subscheme $c_s^{-1}(E_{\alpha+s+1}(s+1))\cap\bar X_{s+1}$ [sic; $c_{s+1}^{-1}$] of the
    non-singular algebraic scheme $\bar X_{s+1}$; this subscheme is also the total transform of
    $\hat B_s$ in $\bar X_{s+1}$. (p.~316.)
    (Formalization notes (encoding): $\bar J(s+1)$ is formed for every $s$ by the paper's formula, the
    quotient being \texttt{Subscheme.divPow} as in \cref{def:I.7-II}; ``$\bar J(s)$ is defined''
    is the condition that (1), (2), (3) hold at every $t<s$; the containment in (3) is required
    stalkwise.)

    \textbf{Paper misprint.} On p.~316 the paper writes ``the subring $T_0$ of $S_0$'' for
    $\hat S_0$, and defines $\bar P_{s+1}$ as the ideal of ``$c_s^{-1}(E_{\alpha+s+1}(s+1))\cap
    \bar X_{s+1}$'' for $c_{s+1}^{-1}(E_{\alpha+s+1}(s+1))\cap\bar X_{s+1}$ (the same misprint
    recurs on p.~324). -/)
  (latexEnv := "definition")]
def jBar : ∀ s, Subscheme (𝒮.xBar s).toScheme
  | 0 => 𝒮.jBar0
  | s + 1 => Subscheme.divPow (Subscheme.totalTransform (𝒮.fBar s) (jBar s)) (𝒮.pBar s) 𝒮.bBar

/-- `[vii]` (1): `X̄_s` is non-singular and irreducible. -/
def IsNonsingIrred (s : ℕ) : Prop := (𝒮.xBar s).IsNonsingular ∧ (𝒮.xBar s).IsIrreducible

/-- `[vii]` (2): `B̂_s` is contained in `X̄_s`. -/
def IsCenterContained (s : ℕ) : Prop := (𝒮.tHat.B s).IsContainedIn (𝒮.xBar s)

/-- The containment of `[vii]` (3): `J̄(s)` is contained in the `b̄`-th power of the sheaf of prime
ideals of `B̂_s` on `X̄_s`. -/
def IsJBarContained (s : ℕ) : Prop :=
  ∀ x, (𝒮.jBar s).stalkIdeal x ≤ ((𝒮.bBarOn s).stalkIdeal x) ^ 𝒮.bBar

/-- "`J̄(s)` is defined": the conditions (1), (2), (3) of `[vii]` hold at every `t < s`. -/
def IsDefined (s : ℕ) : Prop := ∀ t, t < s → 𝒮.IsNonsingIrred t ∧ 𝒮.IsCenterContained t ∧ 𝒮.IsJBarContained t

/-- The conditions (1), (2) and (3) of `[vii]` at `s`. -/
def IsAdmissibleAt (s : ℕ) : Prop := 𝒮.IsNonsingIrred s ∧ 𝒮.IsCenterContained s ∧ 𝒮.IsDefined s ∧ 𝒮.IsJBarContained s

/-- `[vii]` (1) as printed: `X̄_s` is non-singular and irreducible, "irreducible" allowing the empty
scheme (the agreement of p. 163: the empty subscheme counts as non-singular and irreducible).
(`IsNonsingIrred` asks for a non-empty irreducible scheme.) -/
def IsNonsingIrredOrEmpty (s : ℕ) : Prop :=
  (𝒮.xBar s).IsNonsingular ∧ ((𝒮.xBar s).pts = ∅ ∨ (𝒮.xBar s).IsIrreducible)

/-- The conditions (1), (2) and (3) of `[vii]` at `s`, as printed: (1) allows the empty `X̄_s`
(`IsNonsingIrredOrEmpty`), and "`J̄(s)` is defined" is that (1), (2), (3) hold at every `t < s`. -/
def IsAdmissibleAtOrEmpty (s : ℕ) : Prop :=
  𝒮.IsNonsingIrredOrEmpty s ∧ 𝒮.IsCenterContained s ∧
    (∀ t, t < s → 𝒮.IsNonsingIrredOrEmpty t ∧ 𝒮.IsCenterContained t ∧ 𝒮.IsJBarContained t) ∧
    𝒮.IsJBarContained s

/-- `[vii]`: "`P̄_{s+1}` … this subscheme is also the total transform of `B̂_s` in `X̄_{s+1}`"
(p. 316).  Proved from the commutative diagrams `c_s ∘ f̂_s = f_s ∘ c_{s+1}`,
`ι ∘ f̄_s = f̂_s ∘ ι` and `B̂_s = c_s⁻¹(B_s)`. -/
@[blueprint "lem:IV.4-Pbar"
  (statement := /-- The subscheme $c_{s+1}^{-1}(E_{\alpha+s+1}(s+1))\cap\bar X_{s+1}$ of
    $\bar X_{s+1}$ (\cref{def:IV.4-construction}) is also the total transform of $\hat B_s$ in
    $\bar X_{s+1}$, i.e.\ $\bar P_{s+1}=\bar f_s^{-1}(\hat B_s\cap\bar X_s)$. (p.~316.) -/)
  (proof := /-- $E_{\alpha+s+1}(s+1)=f_s^{-1}(B_s)$, and total transforms are functorial
    (\cref{def:total-transform}); by $f_s\circ c_{s+1}=c_s\circ\hat f_s$, $\hat f_s\circ\iota=
    \iota\circ\bar f_s$ and $\hat B_s=c_s^{-1}(B_s)$ both sides are the total transform of $B_s$
    along $\bar X_{s+1}\to X_s$. -/)
  (latexEnv := "lemma")]
theorem pBar_eq (s : ℕ) :
    𝒮.pBar s = Subscheme.totalTransform (𝒮.fBar s) (𝒮.bBarOn s) := by
  simp only [pBar, bBarOn, 𝒮.B_hat s, ← Subscheme.totalTransform_comp]
  congr 1
  rw [← 𝒮.c_comm s, ← Category.assoc, ← 𝒮.fBar_comm s, Category.assoc]

end Frame

/-- `dim Ŝ_0 = N` (p. 314): the completion of the regular local ring `S_0` of dimension `N`. -/
theorem Standing.ringKrullDim_shat (hS : Standing N ℜ r ν T x₀) :
    ringKrullDim (AB.Shat X x₀) = (N : WithBot ℕ∞) := by
  have : IsRegularLocalRing (X.presheaf.stalk x₀) := hS.ambient.2.1 x₀
  have : IsRegularLocalRing (AB.Shat X x₀) :=
    isRegularLocalRing_adicCompletion_of_isRegularLocalRing _
  rw [← IsRegularLocalRing.spanFinrank_maximalIdeal, AdicCompletion.spanFinrank_maximalIdeal_eq,
    IsRegularLocalRing.spanFinrank_maximalIdeal]
  exact hS.dimAt_x₀

/-- The choice of `z` in the closed case, [i] (p. 315): the ideal of the closed restriction `F` in
`O_{X,x}` is generated by one element `z₀` which is a member of a regular system of parameters of
`O_{X,x}` (type II analogue of the shared [a] lemma).

Deviation from the paper (gap filled): the paper (p. 315, [i]) says only "`z_0` is an element of `S_0`
which generates the ideal of `F` in `S_0`" and does not argue that such an element exists and is a
regular parameter: `F` is non-singular of codimension one with `E ∪ F` having only normal crossings,
so a regular system of parameters adapted to `F` exists. -/
theorem _root_.Hironaka.DatumII.Raw.exists_extendsToRSOP_and_stalkIdeal_eq_span_of_isClosedRestriction
    (hX : X.IsNonsingular) {ℜ : DatumII.Raw X} (hℜ : ℜ.IsDatum)
    {F : Subscheme X} (hF : ℜ.IsClosedRestriction F) {x : X} (hx : x ∈ F.pts) :
    ∃ z₀ : X.presheaf.stalk x, ExtendsToRSOP _ {z₀} ∧ F.stalkIdeal x = Ideal.span {z₀} := by
  classical
  have hBred : (Subscheme.empty : Subscheme X).IsReduced :=
    DatumTransform.isReduced_of_isNonsingular Subscheme.isNonsingular_empty
  obtain ⟨Z, hZ, -, hF'⟩ :=
    DatumTransform.exists_rsop_adapted_of_isClosedRestriction_datumII (B := Subscheme.empty) hX
      ℜ.E hℜ.2.1 (fun y hy => by rw [DatumTransform.pts_empty] at hy; exact hy.elim) hF.1 hF.2
      hBred (by rw [DatumTransform.pts_empty]; exact Set.empty_subset _) x
  rcases hF' none with h | ⟨a, haZ, ha⟩
  · exact absurd h (Subscheme.mem_pts_iff_stalkIdeal_ne_top.mp hx)
  · exact ⟨a, ⟨Z, Finset.singleton_subset_iff.mpr haZ, hZ⟩, ha⟩

/-- pp. 314–316: the objects of the setup exist.

Deviation from the paper (gap filled): [i] (p. 315, "`z_0` is an element of `S_0` which generates the
ideal of `F` in `S_0`", that it is a regular parameter is not argued) is
`DatumII.Raw.exists_extendsToRSOP_and_stalkIdeal_eq_span_of_isClosedRestriction`; the order of `Ĵ_0`
(`ν_{M̂_0}(Ĵ_0) = ν_{M_0}(J_0)`, Corollary of Lemma 2, §3, Ch. III) and the choices [0], [ii], [iii]', [iv]
are the ring-level theorems `exists_cdFrame_of_given_z` and `exists_cdFrame_unrestricted`
(CDFrame.lean); `f̄_s` is the map induced on strict transforms (`strictTransformMap`). -/
@[blueprint "lem:IV.4-setup-exists"
  (statement := /-- Under the standing assumptions (\cref{def:IV.4-standing}), the objects of
    \cref{def:IV.4-frame} exist: the induced succession $\{\hat f_s\}$ of
    $\hat X_0=\operatorname{Spec}(\hat S_0)$ with the morphisms $c_s$, the base [0], the subfield
    $k$ and the regular frame $(T_0;z_0)$ of $\hat S_0$ with [i]--[iv], [iii]', and the morphisms
    $\bar f_s\colon\bar X_{s+1}\to\bar X_s$ induced by $\hat f_s$. (pp.~314--316.) -/)
  (proof := /-- The induced succession and the $c_s$ exist as in \S3 (\cref{lem:IV.3-setup-exists};
    $\hat X_s=X_s\times_X\hat X_0$ by faithful flatness of $\hat S_0$ over $S_0$). $\hat S_0$ is a
    complete regular local ring, containing a coefficient field $k$ with $\hat S_0$ a formal
    power series ring of $N$ variables over $k$ (Cohen's structure theorem). Since
    $\nu_{M_0}(J_0)=\nu$ (\cref{lem:IV.4-nu-J0}), $\hat J_0$ has a base of elements of order
    $\nu$. In the closed case $z_0\in S_0$ is a generator of the ideal of the non-singular
    divisor $F$ through $x_0$ ($x_0\in S_\nu(\mathfrak R)\subseteq F$), a regular parameter.
    Replacing the $y_j$ by $y_j+c_jz_0$ with suitable $c_j\in k$ ($k$ is infinite, of
    characteristic zero) makes every $g_j$ regular of order $\nu$ in $z_0$, and the Weierstrass
    preparation theorem gives [iii]; in the unrestricted case the Tschirnhausen substitution
    $z_0\mapsto z_0+(1/\nu)g_{11}$ (characteristic zero) gives [iv]; dividing by the units $u_j$
    gives [iii]'. Finally $\bar X_{s+1}$ is the strict transform of $\bar X_s$ by $\hat f_s$, so
    $\hat f_s$ maps it into $\bar X_s$ and induces $\bar f_s$. -/)
  (proofUses := ["lem:IV.3-setup-exists", "lem:IV.4-nu-J0"])
  (latexEnv := "lemma")]
theorem Standing.nonempty_frame [Hironaka.HironakaCitedResults.{u}] (hS : Standing N ℜ r ν T x₀) : Nonempty (Frame hS):= by
  classical
  have hx : X.IsSimpleAt x₀ := hS.ambient.2.1 x₀
  have : IsRegularLocalRing (X.presheaf.stalk x₀) := hx
  have := hS.ambient.1
  have hreg : IsRegularLocalRing (AB.Shat X x₀) := inferInstance
  let α := algebraMap (X.presheaf.stalk x₀) (AB.Shat X x₀)
  have : CharZero (ResidueField (AB.Shat X x₀)) :=
    (RingHom.charZero_iff (ResidueField.map α).injective).mp (charZero_residueField_stalk X x₀)
  have hmaps : RingHom.MapsRSOP α := mapsRSOP_algebraMap_adicCompletion
  have hN : ((N : ℕ) : WithBot ℕ∞) = ringKrullDim (AB.Shat X x₀) := hS.ringKrullDim_shat.symm
  -- the order of `Ĵ_0`
  have hnuH : (ν : ℕ∞) = ⨅ f ∈ jHat0 ℜ x₀, Ideal.ordElem (maximalIdeal (AB.Shat X x₀)) f := by
    have h1 := (nuI_one_eq_nu_and_nuI_two_and_nuI_le_nuParen (X.presheaf.stalk x₀) (ℜ.J.stalkIdeal x₀)).1.2
    have h2 := nuI_map_eq_of_mapsRSOP α hmaps (ℜ.J.stalkIdeal x₀) 1
    have h3 := (nuI_one_eq_nu_and_nuI_two_and_nuI_le_nuParen (AB.Shat X x₀) (jHat0 ℜ x₀)).1.1
    rw [← h3]
    show (ν : ℕ∞) = nuI _ ((ℜ.J.stalkIdeal x₀).map α) 1
    rw [← h2, h1, hS.nu_stalkIdeal_J_eq]
  have hlow : ∀ a ∈ jHat0 ℜ x₀, (ν : ℕ∞) ≤ Ideal.ordElem (maximalIdeal (AB.Shat X x₀)) a :=
    fun a ha => hnuH ▸ iInf₂_le a ha
  have hex : ∃ a ∈ jHat0 ℜ x₀, Ideal.ordElem (maximalIdeal (AB.Shat X x₀)) a = ν := by
    by_contra hcon
    push Not at hcon
    have : ((ν : ℕ∞) + 1) ≤ (ν : ℕ∞) := by
      conv_rhs => rw [hnuH]
      refine le_iInf₂ fun a ha => ?_
      exact Order.add_one_le_of_lt (lt_of_le_of_ne (hlow a ha) (hcon a ha).symm)
    have h2 : (ν + 1 : ℕ) ≤ ν := by exact_mod_cast this
    omega
  let 𝒞 := T.completion x₀ hx
  -- the frame data, in the two cases
  have key : ∃ (z : AB.Shat X x₀) (jG : Set (AB.Shat X x₀)), FrameSpec N x₀ ℜ r ν z jG := by
    cases r with
    | closed F =>
      have hxF : x₀ ∈ F.pts := hS.mem_Snu.2
      have hF : ℜ.IsClosedRestriction F := hS.isFor
      obtain ⟨z₀, ⟨Z, hzZ, hZ⟩, hFz⟩ :=
        _root_.Hironaka.DatumII.Raw.exists_extendsToRSOP_and_stalkIdeal_eq_span_of_isClosedRestriction
          hS.ambient.2.1 hS.isDatum hF hxF
      have hz : ExtendsToRSOP (AB.Shat X x₀) {α z₀} :=
        ⟨Z.image α, by
          rw [Finset.singleton_subset_iff]
          exact Finset.mem_image_of_mem _ (hzZ (Finset.mem_singleton_self z₀)),
          (hmaps.isRegularSystemOfParameters_image hZ).1⟩
      obtain ⟨Fr, h1, hFz', hii, m, g, co, hspan, hord, hform⟩ :=
        exists_cdFrame_of_given_z N hN (jHat0 ℜ x₀) ν hlow hex hz
      refine ⟨α z₀, _, Fr, h1, hFz', fun F' hF' => ?_, hii, m, g, co, hspan, hord, hform,
        fun hu => (by cases hu), rfl⟩
      obtain rfl : F = F' := Restriction.closed.inj hF'
      exact ⟨z₀, rfl, hFz⟩
    | unrestricted =>
      obtain ⟨z, Fr, h1, hFz', hii, m, g, co, hspan, hord, hform, hm, hν', h0⟩ :=
        exists_cdFrame_unrestricted N hN (by
          have := hS.one_le
          exact this) (jHat0 ℜ x₀) ν hS.nu_pos hlow hex
      exact ⟨z, _, Fr, h1, hFz', fun F hF => (by cases hF), hii, m, g, co, hspan, hord, hform,
        fun _ => ⟨hm, hν', h0⟩, rfl⟩
  obtain ⟨z, jG, hfr⟩ := key
  exact ⟨{ toCompletion := 𝒞
           regShat := hreg
           z := z
           jGen := jG
           frame := hfr
           fBar := fun s => (𝒞.tHat.monoidalTransformation s).strictTransformMap
             (AB.strictTransformZeroLocus 𝒞.tHat z s)
           fBar_comm := fun s => MonoidalTransformation.strictTransformMap_ι _ _ }⟩

end CD

end

end Hironaka
