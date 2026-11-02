/-
Copyright (c) 2026 Daattavya Aggarwal, Minhyong Kim, Oisin Kim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daattavya Aggarwal, Minhyong Kim, Oisin Kim
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Architect
public import Hironaka.Compat.MainISystem
public import Hironaka.Compat.MonoidalSuccessionBaseChange
public import Hironaka.Compat.CompletionResolved
public import Hironaka.Compat.LocalizeDim
public import Hironaka.Ch4.ImplicationsAB
public import Hironaka.Ch4.CompletionFibre
public import Hironaka.Compat.CompletionFibreSmallest
public import Hironaka.Statements

/-!
# Main Theorem I(n), pp. 175–176: the center `C` of `V₀(r)` and the induced succession with empty centers

> Let `Ĉ` be the center of `ĝ`.  Then `Ĉ` is a reduced irreducible subscheme of `V̂₀(r)`, which is contained in
> `Ŝ(r)`.  Since the point `x` is a generic point of `S̄(r)`, the image of `Ŝ(r)` in `V̂₀` is the unique closed point.
> Therefore, we can find a reduced irreducible subscheme `C` of `V₀(r)` such that `Ĉ = c_r⁻¹(C)`.  In fact, we take
> the smallest subscheme `C` of `V₀(r)` such that `Ĉ = c_r⁻¹(C)`.  We have `C ⊆ S(r)`.  Hence `dim(C) = n′ < n`.  We
> apply theorem I(n′) to `V₀(r)`, `V₁(r)`, …, `V_β(r)`, `W(r)`, and `C`.  Since `Ĉ` is non-singular and all the
> `V̂_j(r)` and `Ŵ(r)` are normally flat along `Ĉ`, any succession of monoidal transformations which appears in the
> application of theorem I(n′) induces in `V̂₀(r)` a succession of monoidal transformations with empty centers.
> (pp. 175–176)

Contents:
* generic points: a point `w` of a closed set `S̄` which specializes to a generic point `x` of an irreducible component
  of `S̄` is `x`;
* the Corollary of (AB.3) for an arbitrary algebraic scheme: for a reduced irreducible `Ĉ ⊆ Ŷ` lying over `x`, the
  scheme-theoretic image `C` of `Ĉ → Y` is reduced irreducible, `c⁻¹(C) = Ĉ`, and `C` is the smallest such
  (Ch. IV has this for non-singular `X` and simple `x₀`, `Completion.exists_unique_irreducible_totalTransform`; here `Y`
  is singular, and only flatness of the local maps is available);
* `C ⊆ S(r)` and `dim C < n`;
* the centers of the succession from I(n′) avoid the range of `c_r`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

namespace Hironaka

universe u

/-! ### Generic points -/

/-- `x` is a generic point of an irreducible component of the set `S` of `X` (p. 175: "take a generic point `x` of
`S̄(r)`"): `closure {x}` is a maximal irreducible subset of `S`. -/
@[blueprint "def:I.3-generic-point-of-component"
  (statement := /-- A generic point of an irreducible component of a subset $S$ of a scheme: a point $x\in S$ such that $\overline{\{x\}}$ is a maximal irreducible subset of $S$ (p.~175: ``Now, take a generic point $x$ of $\bar S(r)$, assuming that $S(r)$ is not empty.''). -/)
  (latexEnv := "definition")]
def IsGenericPointOfComponent {X : Scheme.{u}} (S : Set X) (x : X) : Prop :=
  Maximal (fun T : Set X => IsIrreducible T ∧ T ⊆ S) (closure {x})

/-- p. 175: "Since the point `x` is a generic point of `S̄(r)`, the image of `Ŝ(r)` in `V̂₀` is the unique closed point":
a point `w` of the closed set `S` which specializes to a generic point `x` of an irreducible component of `S` equals `x`
(the points of `Spec O_x` are the generizations of `x`, `Scheme.range_fromSpecStalk`). -/
@[blueprint "lem:I.3-generic-point-specialization"
  (statement := /-- Let $S$ be a closed subset of a scheme and $x$ a generic point of an irreducible component of $S$. A point $w$ of $S$ which specializes to $x$ equals $x$ (used in p.~175: ``Since the point $x$ is a generic point of $\bar S(r)$, the image of $\hat S(r)$ in $\hat V_0$ is the unique closed point.''). -/)
  (proof := /-- $\overline{\{w\}}\subseteq S$ is irreducible and contains $\overline{\{x\}}$, so by maximality they are equal, and $w\rightsquigarrow x\rightsquigarrow w$. -/)
  (latexEnv := "lemma")]
theorem eq_of_specializes_of_isGenericPointOfComponent {X : Scheme.{u}} {S : Set X} (hS : IsClosed S)
    {x w : X} (hx : IsGenericPointOfComponent S x) (hw : w ∈ S) (hwx : w ⤳ x) : w = x := by
  have hcl : closure {w} ⊆ S := closure_minimal (Set.singleton_subset_iff.mpr hw) hS
  have hxw : closure {x} ⊆ closure {w} :=
    closure_minimal (Set.singleton_subset_iff.mpr (specializes_iff_mem_closure.mp hwx)) isClosed_closure
  have h1 := hx.2 ⟨isIrreducible_singleton.closure, hcl⟩ hxw
  have hxw' : x ⤳ w := specializes_iff_mem_closure.mpr (h1 (subset_closure rfl))
  exact (hwx.antisymm hxw').eq

/-- The points of `Ŷ` over the unique closed point: let `T` be a closed subset of `X` of which `x` is a generic point of an
irreducible component, `S ⊆ Y` with `g(S) ⊆ T`, and `c : Ŷ ⟶ Y` over `Spec(Ô_{X,x})` (`c ≫ g = ĝ ≫ c0`); then every
point of `c⁻¹(S)` maps to `x` in `X`, i.e. to the closed point `x̂` of `V̂₀`.  (`T = S̄(r)` for the starting stage; at a later
stage `S̄(r′) ⊆ S̄(r)`.) -/
@[blueprint "lem:I.3-fibre-over-generic-point"
  (statement := /-- p.~175: ``Since the point $x$ is a generic point of $\bar S(r)$, the image of $\hat S(r)$ in $\hat V_0$ is the unique closed point.'' Let $T$ be a closed subset of $X$ of which $x$ is a generic point of an irreducible component, $S\subseteq Y$ with $g(S)\subseteq T$, and $c\colon\hat Y\to Y$ lying over $\operatorname{Spec}\hat{\mathcal O}_{X,x}$. Then every point of $c^{-1}(S)$ maps to $x$ in $X$. -/)
  (proof := /-- The image of a point of $\hat Y$ in $X$ is a generization of $x$ (the points of $\operatorname{Spec}\mathcal O_{X,x}$ are the generizations of $x$) which lies in $T$, so it is $x$ by \cref{lem:I.3-generic-point-specialization}. -/)
  (latexEnv := "lemma")]
theorem g_eq_of_mem_preimage {X Y Ŷ : Scheme.{u}} (x : X) (g : Y ⟶ X) (c : Ŷ ⟶ Y) (ĝ : Ŷ ⟶ AB.xHat0 X x)
    (H : c ≫ g = ĝ ≫ AB.c0 X x) (S : Set Y) (T : Set X) (hT : IsClosed T) (hx : IsGenericPointOfComponent T x)
    (hST : g.base '' S ⊆ T) {ŷ : Ŷ} (hŷ : c.base ŷ ∈ S) : g.base (c.base ŷ) = x := by
  have hw : g.base (c.base ŷ) = (AB.c0 X x).base (ĝ.base ŷ) := by
    have := congrArg (fun φ : Ŷ ⟶ X => φ.base ŷ) H
    simpa using this
  have hspec : g.base (c.base ŷ) ⤳ x := by
    rw [hw]
    have hrange := Scheme.range_fromSpecStalk (X := X) (x := x)
    have hmem : (AB.c0 X x).base (ĝ.base ŷ) ∈ Set.range (X.fromSpecStalk x).base := by
      refine ⟨(Spec.map (CommRingCat.ofHom (algebraMap (X.presheaf.stalk x) (AB.Shat X x)))).base
        (ĝ.base ŷ), ?_⟩
      rfl
    rw [hrange] at hmem
    exact hmem
  exact eq_of_specializes_of_isGenericPointOfComponent hT hx (hST ⟨c.base ŷ, hŷ, rfl⟩) hspec

/-! ### `C ⊆ S(r)` and `dim C < n` -/

namespace MonoidalSuccession

variable {X Y : Scheme.{u}} [IsAlgebraicScheme X] (s : MonoidalSuccession X Y) {β : ℕ}

/-- `dim W(r) ≤ dim W`: the monoidal transformations do not raise the dimension of the strict transform
(`MonoidalTransformation.dim_strictTransform_le`, p. 169, Remark 1). -/
theorem dim_strictTransform_le [Hironaka.HironakaCitedResults.{u}] (W : Subscheme X) : (s.strictTransform W).dim ≤ W.dim := by
  revert W
  revert ‹IsAlgebraicScheme X›
  induction s with
  | nil X =>
    intro _ W
    exact le_rfl
  | cons B t rest ih =>
    intro hX W
    have := t.isAlgebraicScheme
    exact (ih _).trans (t.dim_strictTransform_le W)

/-- p. 175: "We have `C ⊆ S(r)`.  Hence `dim(C) = n′ < n`": a nonempty reduced subscheme `C` of `V₀(r)` whose points lie
in `S(r)` has dimension `n′ < n`, where `n = dim W`.  (Every point `x` of `S(r)` has a strict generization `η` at which
`W(r)` is resolved (density of the resolved points of the reduced `W(r)`), so `height x + 1 ≤ height η ≤ dim W(r)
≤ dim W`, `MonoidalTransformation.dim_strictTransform_le`.) -/
@[blueprint "lem:I.3-dim-C-lt-n"
  (statement := /-- p.~175: ``We have $C\subseteq S(r)$. Hence $\dim(C)=n'<n$.'' Let $W$ be a reduced subscheme of dimension $n$ contained in $\bigcap V_j$, $\{f_i\}_{0\le i<r}$ a succession and $C$ a non-empty subscheme of $V_0(r)$ whose points lie in $S(r)$. Then $\dim C=n'$ with $n'<n$. -/)
  (proof := /-- Every point $x$ of $S(r)$ has a strict generization $\eta$ at which the reduced $W(r)$ is resolved (\cref{lem:I.3-resolved-generization}), so $\operatorname{height}x+1\le\operatorname{height}\eta\le\dim W(r)\le\dim W=n$, the monoidal transformations not raising the dimension of the strict transform (Remark~1, p.~169). -/)
  (latexEnv := "lemma")]
theorem exists_dim_eq_lt_of_pts_subset_mainUnresolvedAt [Hironaka.HironakaCitedResults.{u}] (V : Fin (β + 1) → Subscheme X) (W : Subscheme X)
    (hW : W.IsReduced) (hWV : ∀ j, W.IsContainedIn (V j)) {n : ℕ} (hn : W.dim = (n : WithBot ℕ∞))
    (C : Subscheme Y) (hCne : C.pts.Nonempty) (hC : C.pts ⊆ s.mainUnresolvedAt V W) :
    ∃ n' : ℕ, C.dim = (n' : WithBot ℕ∞) ∧ n' < n := by
  have := s.isAlgebraicScheme_target
  have hW' : (s.strictTransform W).IsReduced := s.isReduced_strictTransform_of_isReduced W hW
  have hWV' : ∀ j, (s.strictTransform W).IsContainedIn (s.strictTransform (V j)) := fun j =>
    isContainedIn_strictTransform s (hWV j)
  have hdim : (s.strictTransform W).dim ≤ (n : WithBot ℕ∞) := hn ▸ s.dim_strictTransform_le W
  -- every point of `C` has `height + 1 ≤ n`
  have hh : ∀ x ∈ C.pts, Order.height x + 1 ≤ (n : ℕ∞) := by
    intro x hx
    obtain ⟨hxW, hxn⟩ := hC hx
    obtain ⟨η, hηx, hη⟩ := Subscheme.exists_specializes_isMainResolvedAt
      (fun j => s.strictTransform (V j)) (s.strictTransform W) hW' hWV' hxW
    have hlt : x < η := by
      refine lt_of_le_not_ge (Scheme.le_iff_specializes.mpr hηx) fun h => ?_
      have : x = η := ((Scheme.le_iff_specializes.mp h).antisymm hηx).eq
      exact hxn (this ▸ hη)
    have h1 : Order.height x + 1 ≤ Order.height η := Order.height_add_one_le hlt
    have h2 : (Order.height η : WithBot ℕ∞) ≤ (s.strictTransform W).dim :=
      StrictDim.height_le_dim _ hη.1.1
    have h3 : (Order.height η : WithBot ℕ∞) ≤ ((n : ℕ∞) : WithBot ℕ∞) := h2.trans hdim
    exact h1.trans (by exact_mod_cast h3)
  obtain ⟨x₀, hx₀⟩ := hCne
  have hnpos : 0 < n := by
    by_contra hn0
    have := hh x₀ hx₀
    rw [Nat.pos_iff_ne_zero, not_not] at hn0
    subst hn0
    simp at this
  have hle : C.dim ≤ ((n - 1 : ℕ) : WithBot ℕ∞) := by
    refine StrictDim.dim_le_of_forall C fun x hx => ?_
    have h3 := hh x hx
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    have h4 : Order.height x + 1 ≤ (m : ℕ∞) + 1 := by simpa using h3
    have h5 := (ENat.add_le_add_iff_right (by simp)).mp h4
    simpa using (show ((Order.height x : ℕ∞) : WithBot ℕ∞) ≤ ((m : ℕ∞) : WithBot ℕ∞) by exact_mod_cast h5)
  have hge : ((Order.height x₀ : ℕ∞) : WithBot ℕ∞) ≤ C.dim := StrictDim.height_le_dim C hx₀
  have hne : C.dim ≠ ⊥ := ne_bot_of_le_ne_bot (WithBot.coe_ne_bot) hge
  obtain ⟨e, he⟩ := WithBot.ne_bot_iff_exists.mp hne
  have hetop : e ≠ ⊤ := by
    intro htop
    rw [← he, htop] at hle
    have h : (⊤ : ℕ∞) ≤ ((n - 1 : ℕ) : ℕ∞) := WithBot.coe_le_coe.mp hle
    exact ENat.natCast_ne_top _ (top_le_iff.mp h)
  obtain ⟨k, rfl⟩ := ENat.ne_top_iff_exists.mp hetop
  refine ⟨k, he.symm, ?_⟩
  rw [← he] at hle
  have h : (k : ℕ∞) ≤ ((n - 1 : ℕ) : ℕ∞) := WithBot.coe_le_coe.mp hle
  have : k ≤ n - 1 := by exact_mod_cast h
  omega

end MonoidalSuccession

/-! ### The centers of the succession from I(n′) avoid the range of `c_r` -/

/-- p. 175–176: "Since `Ĉ` is non-singular and all the `V̂_j(r)` and `Ŵ(r)` are normally flat along `Ĉ`, any succession
… which appears in the application of theorem I(n′) induces in `V̂₀(r)` a succession of monoidal transformations with
empty centers."  If `s` satisfies (1), (2), (3) for the data `(V′; C)` and every point of `C` in the set `R` is a resolved
point (simple, all `V′_j` normally flat along `C`), then the centers of `s` avoid `R` (induction on `s` with (2); at the next
stage the points over `R` are resolved because the monoidal transformation is a local isomorphism off its center). -/
@[blueprint "lem:I.3-centers-avoid"
  (statement := /-- pp.~175--176: ``Since $\hat C$ is non-singular and all the $\hat V_j(r)$ and $\hat W(r)$ are normally flat along $\hat C$, any succession of monoidal transformations which appears in the application of theorem I($n'$) induces in $\hat V_0(r)$ a succession of monoidal transformations with empty centers.'' If $s$ satisfies (1), (2), (3) for the data $(V';C)$ and every point of $C$ in a set $R$ is resolved, then the centers of $s$ avoid $R$. -/)
  (proof := /-- Induction on $s$ using (2): a center $B_0\subseteq C$ contains no resolved point, so it misses $R$; at the next stage the points over $R$ are resolved because the monoidal transformation is a local isomorphism off its center (\cref{lem:I.3-resolved-off-exceptional}). -/)
  (latexEnv := "lemma")]
theorem MonoidalSuccession.centersAvoid_of_isMain123 {Y Y' : Scheme.{u}} (s : MonoidalSuccession Y Y')
    {β : ℕ} (V' : Fin (β + 1) → Subscheme Y) (C : Subscheme Y) (hCV : ∀ j, C.IsContainedIn (V' j))
    (hs : s.IsMain123 V' C) (R : Set Y)
    (hR : ∀ y ∈ C.pts, y ∈ R → Subscheme.IsMainResolvedAt V' C y) : s.CentersAvoid R := by
  induction s generalizing β with
  | nil X => trivial
  | cons B t rest ih =>
    obtain ⟨⟨⟨hBc, hBC⟩, hB2, -⟩, hrest⟩ := hs
    refine ⟨fun y hy hyR => hB2 y hy (hR y (pts_subset_of_isContainedIn hBC hy) hyR), ?_⟩
    refine ih (fun j => Subscheme.strictTransform t (V' j)) (Subscheme.strictTransform t C)
      (fun j => Subscheme.IsContainedIn.strictTransform t (hCV j)) hrest _ ?_
    intro y' hy' hy'R
    have hfy : t.f.base y' ∈ C.pts := MonoidalTransformation.pts_strictTransform_subset t C hy'
    have hres := hR _ hfy hy'R
    have hyE : y' ∉ t.exceptional.pts := fun hE => by
      rw [MonoidalTransformation.pts_exceptional] at hE
      exact hB2 _ hE hres
    exact Subscheme.isMainResolvedAt_strictTransform_of_notMem_exceptional t V' C hCV hyE hres

end Hironaka
