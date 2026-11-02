/-
Copyright (c) 2026 Daattavya Aggarwal, Minhyong Kim, Oisin Kim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daattavya Aggarwal, Minhyong Kim, Oisin Kim
-/
module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Architect
public import Hironaka.Ch1.ResolutionData
public import Hironaka.Compat.LocalizeSuccession
public import Hironaka.Compat.TransformNormalCrossingsLocalized
public import Hironaka.Ch4.CompletionTransforms
public import Hironaka.Statements

/-!
# Main Theorem I(n) (Ch. I §3, pp. 172–176): vocabulary and the lemmas about the sets `S(i)`

> MAIN THEOREM I(n). Let V₀ be an arbitrary algebraic scheme, V_j (1 ≤ j ≤ β) a finite number of
> subschemes of V₀, and W a reduced subscheme of V₀ of dimension n which is contained in ⋂_{j=1}^β V_j.
> Then there exists a finite succession of monoidal transformations {f_i : V₀(i+1) → V₀(i)} with centers
> B_i in V₀(i) for 0 ≤ i < r, where V₀(0) = V₀, such that if {V_j(i+1) → V_j(i)} and {W(i+1) → W(i)} are
> the monoidal transformations induced by f_i, where V_j(0) = V_j and W(0) = W, then
> (1) B_i is a non-singular irreducible subscheme of W(i);
> (2) B_i does not contain any simple point of W(i) at which all the V_j(i) for 0 ≤ j ≤ β are normally
>     flat along W(i);
> (3) all the V_j(i) (0 ≤ j ≤ β) and W(i) are normally flat along B_i; and finally
> (4) W(r) is non-singular and all the V_j(r) for 0 ≤ j ≤ β are normally flat along W(r).  (p. 174)

This file holds the vocabulary of the whole statement and
the lemmas about the sets `S(i)`, the prolongations and the descending chain of p. 174.

Encoding (formalization notes):
* `V_0` is the scheme itself, the subscheme `⊥` (zero ideal sheaf); `mainSystem V = Fin.cons ⊥ V`.
* The monoidal transformations `V_j(i+1) → V_j(i)` induced by `f_i` are encoded by the strict transforms
  `V_j(i+1) = strictTransform f_i V_j(i)` (p. 173: "See the paragraphs preceding Definition 6, § 1"), as in Ch. IV.
* A succession is the inductive `MonoidalSuccession V₀ Y`; conditions (1)–(3) are the recursion `IsMain123`,
  condition (4) is `IsMain4` on the last stage.
* `Reach4` (p. 175: "a prolongation of {f̂_i} satisfying (4), in addition to (1), (2) and (3)") is stated as a
  property of the *data* `(Y; V; W)` with a recursion on the length of the prolongation, so that no succession has
  to be transported along an isomorphism (encoding).
* The centers `B̂_i = c_i⁻¹(B_i)` of the completion are non-singular, but need not be irreducible
  (`IsMain123Hat`; the printed "Obviously, B̂_i, Ŵ(i) and V̂_j(i) satisfy the conditions (1), (2) and (3)" is
  imprecise on irreducibility, which is never used).
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace Hironaka

universe u

/-! ### The systems `(V_0, V_1, …, V_β)` and the sets `S(i)` -/

section Vocabulary

variable {X : Scheme.{u}} {β : ℕ}



/-- p. 173 (`S(i)`) and p. 174 (`S(r)`): "the complement in `W(i)` of the set of those points of `W(i)` which are
simple points of `W(i)` and at which all the `V_j(i)` are normally flat along `W(i)`". -/
@[blueprint "def:I.3-main-S"
  (statement := /-- The set $S$ of the points of $W$ which are not resolved (\cref{def:I.3-main-resolved}): ``$S(r)$ denotes the closed subset of $W(r)$ complementary to the set of those simple points of $W(r)$ at which all the $V_j(r)$ for $0\le j\le\beta$ are normally flat along $W(r)$'' (p.~174); for the intermediate stages, p.~173: ``Let $S(i)$ be the complement in $W(i)$ of the set of those points of $W(i)$ which are simple points of $W(i)$ and at which all the $V_j(i)$ ($1\le j\le\beta$) are normally flat along $W(i)$.'' (The index $j=0$ is included: on a non-singular ambient scheme the two sets agree.) -/)
  (latexEnv := "definition")]
def Subscheme.mainUnresolved (V : Fin (β + 1) → Subscheme X) (W : Subscheme X) : Set X :=
  {x | x ∈ W.pts ∧ ¬ Subscheme.IsMainResolvedAt V W x}


/-- Conditions (1), (2), (3) of Main Theorem I(n) at one stage, as printed: `B` is a non-singular irreducible
subscheme of `W` (the empty subscheme counts, p. 163), `B` contains no simple point of `W` at which all `V_j` are
normally flat along `W`, and all the `V_j` and `W` are normally flat along `B`. -/
@[blueprint "def:I.3-main-step"
  (statement := /-- Conditions (1), (2), (3) of Main Theorem~I($n$) at one stage, as printed (p.~174): (1) $B_i$ is a non-singular irreducible subscheme of $W(i)$ (the empty subscheme counts, p.~163); (2) $B_i$ does not contain any simple point of $W(i)$ at which all the $V_j(i)$ for $0\le j\le\beta$ are normally flat along $W(i)$; (3) all the $V_j(i)$ ($0\le j\le\beta$) and $W(i)$ are normally flat along $B_i$. -/)
  (latexEnv := "definition")]
abbrev Subscheme.IsMainStep (V : Fin (β + 1) → Subscheme X) (W B : Subscheme X) : Prop :=
  Subscheme.IsMainStepWith (fun D => Subscheme.IsCenter D) V W B


end Vocabulary

/-! ### Successions satisfying (1)–(4) -/

namespace MonoidalSuccession



/-- (1) with "non-singular" instead of "non-singular irreducible", (2), (3) for all `i`: the form in which
the properties hold for the completed successions `{f̂_i}` (the centers `c_i⁻¹(B_i)` need not be irreducible). -/
@[blueprint "def:I.3-main-123-hat"
  (statement := /-- The conditions (1), (2), (3) for all $i$ with ``non-singular'' in place of ``non-singular irreducible'' in (1): the form in which the properties hold for the completed successions $\{\hat f_i\}$ (p.~175: ``Obviously, $\hat B_i$, $\hat W(i)$ and the $\hat V_j(i)$ for all $j$ satisfy the conditions (1), (2) and (3)''; the centers $\hat B_i=c_i^{-1}(B_i)$ are non-singular but need not be irreducible, which is never used). -/)
  (latexEnv := "definition")]
abbrev IsMain123Hat {X Y : Scheme.{u}} (s : MonoidalSuccession X Y) {β : ℕ}
    (V : Fin (β + 1) → Subscheme X) (W : Subscheme X) : Prop :=
  s.IsMain123With (fun {_} D => Subscheme.IsNonsingular D) V W



/-- `S(r)`: the points of `W(r)` which are not simple points at which all `V_j(r)` are normally flat along
`W(r)`, for the succession `s`. -/
@[blueprint "def:I.3-main-S-at"
  (statement := /-- The set $S(r)$ of the points of $W(r)$ which are not resolved, for a succession $\{f_i\}_{0\le i<r}$ (p.~174: ``$S(r)$ denotes the closed subset of $W(r)$ complementary to the set of those simple points of $W(r)$ at which all the $V_j(r)$ for $0\le j\le\beta$ are normally flat along $W(r)$''). -/)
  (latexEnv := "definition")]
def mainUnresolvedAt {X Y : Scheme.{u}} (s : MonoidalSuccession X Y) {β : ℕ}
    (V : Fin (β + 1) → Subscheme X) (W : Subscheme X) : Set Y :=
  Subscheme.mainUnresolved (fun j => s.strictTransform (V j)) (s.strictTransform W)

/-- `S̄(r)` (p. 174): "the image of `S(r)` in `V₀`". -/
@[blueprint "def:I.3-main-image"
  (statement := /-- The set $\bar S(r)$, the image of $S(r)$ in $V_0$ (p.~174: ``We shall denote by $\bar S(r)$ the image of $S(r)$ in $V_0$, which is a closed subset of $V_0$ (contained in $W$) because all the morphisms $f_i$ are proper''). -/)
  (latexEnv := "definition")]
def mainImage {X Y : Scheme.{u}} (s : MonoidalSuccession X Y) {β : ℕ}
    (V : Fin (β + 1) → Subscheme X) (W : Subscheme X) : Set X :=
  s.composite.base '' mainUnresolvedAt s V W

/-- Every succession satisfying (1), (2), (3) as printed satisfies them with non-singular centers. -/
theorem IsMain123.isMain123Hat {X Y : Scheme.{u}} {s : MonoidalSuccession X Y} {β : ℕ}
    {V : Fin (β + 1) → Subscheme X} {W : Subscheme X} (h : s.IsMain123 V W) : s.IsMain123Hat V W := by
  induction s generalizing β with
  | nil X => trivial
  | cons B t rest ih =>
    obtain ⟨⟨⟨hB, hBW⟩, h2, h3⟩, hrest⟩ := h
    refine ⟨⟨⟨?_, hBW⟩, h2, h3⟩, ih hrest⟩
    rcases hB with rfl | ⟨hns, -⟩
    · exact Subscheme.isNonsingular_empty
    · exact hns

end MonoidalSuccession

/-! ### Reaching (4) by a prolongation of a given length (p. 175) -/

/-- p. 175: "there exists a prolongation of `{f̂_i}` satisfying (4), in addition to (1), (2) and (3)", as a
property of the data `(Y; V; W)` at the end of `{f̂_i}`: there are `ℓ` more monoidal transformations, the `k`-th
satisfying (1), (2), (3) for the transformed data, and the final data satisfy (4).  The recursion is on the
length, existential over the FIRST monoidal transformation only, so that the property is invariant under
isomorphism of the data by transporting a single monoidal transformation (encoding; avoids transporting whole
successions). -/
@[blueprint "def:I.3-reach4"
  (statement := /-- Reaching condition (4) by a prolongation of a given length (p.~175: ``there exists a prolongation of $\{\hat f_i\}$ satisfying (4), in addition to (1), (2) and (3)''): for the data $(Y;V_0,\dots,V_\beta;W)$ at the end of $\{\hat f_i\}$ and $\ell\ge0$, there are $\ell$ more monoidal transformations, the $k$-th satisfying (1), (2), (3) for the transformed data, and the data at the end satisfy (4). Formalization note (encoding): the recursion on $\ell$ quantifies over the first monoidal transformation only, so that the property is invariant under isomorphism of the data by transporting a single monoidal transformation, without transporting whole successions. -/)
  (latexEnv := "definition")]
def Reach4 {β : ℕ} : ℕ → (Y : Scheme.{u}) → (Fin (β + 1) → Subscheme Y) → Subscheme Y → Prop
  | 0, _, V, W => Subscheme.IsMain4Data V W
  | ℓ + 1, Y, V, W => ∃ (B : Subscheme Y) (t : MonoidalTransformation Y B),
      Subscheme.IsMainStep V W B ∧
      Reach4 ℓ t.X' (fun j => Subscheme.strictTransform t (V j)) (Subscheme.strictTransform t W)

/-! ### Transport of a monoidal transformation along an isomorphism of its base, and along an equality of centers -/

namespace MonoidalTransformation

variable {Y₁ Y₂ : Scheme.{u}}

/-- Transport of a monoidal transformation along an isomorphism `e : Y₁ ≅ Y₂` of its base: the blow-up `t.X'` of
`Y₂` with center `B` is the blow-up of `Y₁` with center `e⁻¹(B)`, with structure morphism `t.f ≫ e⁻¹`. -/
noncomputable def ofIso (e : Y₁ ≅ Y₂) {B : Subscheme Y₂} (t : MonoidalTransformation Y₂ B) :
    MonoidalTransformation Y₁ (Subscheme.totalTransform e.hom B) where
  X' := t.X'
  f := t.f ≫ e.inv
  invertible := by
    have h : Subscheme.totalTransform (t.f ≫ e.inv) (Subscheme.totalTransform e.hom B) =
        Subscheme.totalTransform t.f B := by
      rw [Subscheme.totalTransform_comp, ← Subscheme.totalTransform_comp e.inv e.hom, e.inv_hom_id,
        Subscheme.totalTransform_id]
    rw [h]
    exact t.invertible
  universal := fun X'' f' hf' => by
    have h1 : (Subscheme.totalTransform (f' ≫ e.hom) B).IsInvertibleIdeal := by
      rw [Subscheme.totalTransform_comp]
      exact hf'
    obtain ⟨h, hh, huniq⟩ := t.universal X'' (f' ≫ e.hom) h1
    refine ⟨h, ?_, fun h' hh' => huniq h' ?_⟩
    · show h ≫ t.f ≫ e.inv = f'
      rw [← Category.assoc, hh, Category.assoc, e.hom_inv_id, Category.comp_id]
    · have := congrArg (fun g => g ≫ e.hom) hh'
      simpa using this

@[simp] theorem ofIso_X' (e : Y₁ ≅ Y₂) {B : Subscheme Y₂} (t : MonoidalTransformation Y₂ B) :
    (t.ofIso e).X' = t.X' := rfl

@[simp] theorem ofIso_f (e : Y₁ ≅ Y₂) {B : Subscheme Y₂} (t : MonoidalTransformation Y₂ B) :
    (t.ofIso e).f = t.f ≫ e.inv := rfl

theorem exceptional_ofIso (e : Y₁ ≅ Y₂) {B : Subscheme Y₂} (t : MonoidalTransformation Y₂ B) :
    (t.ofIso e).exceptional = t.exceptional := by
  unfold exceptional
  show Subscheme.totalTransform (t.f ≫ e.inv) (Subscheme.totalTransform e.hom B) =
    Subscheme.totalTransform t.f B
  rw [Subscheme.totalTransform_comp, ← Subscheme.totalTransform_comp e.inv e.hom, e.inv_hom_id,
    Subscheme.totalTransform_id]

/-- The strict transform along the transported monoidal transformation: `e⁻¹(V)` has the same strict transform as `V`
(the strict transform depends only on the exceptional subscheme and on the total transform). -/
theorem strictTransform_ofIso (e : Y₁ ≅ Y₂) {B : Subscheme Y₂} (t : MonoidalTransformation Y₂ B)
    (V : Subscheme Y₂) :
    Subscheme.strictTransform (t.ofIso e) (Subscheme.totalTransform e.hom V) =
      Subscheme.strictTransform t V := by
  have h1 := exceptional_ofIso e t
  have h2 : Subscheme.totalTransform (t.ofIso e).f (Subscheme.totalTransform e.hom V) =
      Subscheme.totalTransform t.f V := by
    show Subscheme.totalTransform (t.f ≫ e.inv) (Subscheme.totalTransform e.hom V) = _
    rw [Subscheme.totalTransform_comp, ← Subscheme.totalTransform_comp e.inv e.hom, e.inv_hom_id,
      Subscheme.totalTransform_id]
  unfold Subscheme.strictTransform
  rw [h1, h2]
  rfl

variable {X : Scheme.{u}}

/-- Transport of a monoidal transformation along an equality of centers (same blown-up scheme and morphism). -/
def congrCenter {B B' : Subscheme X} (h : B = B') (t : MonoidalTransformation X B) :
    MonoidalTransformation X B' where
  X' := t.X'
  f := t.f
  invertible := by subst h; exact t.invertible
  universal := fun X'' f' hf' => by subst h; exact t.universal X'' f' hf'

@[simp] theorem congrCenter_X' {B B' : Subscheme X} (h : B = B') (t : MonoidalTransformation X B) :
    (congrCenter h t).X' = t.X' := rfl

@[simp] theorem congrCenter_f {B B' : Subscheme X} (h : B = B') (t : MonoidalTransformation X B) :
    (congrCenter h t).f = t.f := rfl

theorem strictTransform_congrCenter {B B' : Subscheme X} (h : B = B') (t : MonoidalTransformation X B)
    (V : Subscheme X) :
    Subscheme.strictTransform (congrCenter h t) V = Subscheme.strictTransform t V := by
  subst h
  rfl

end MonoidalTransformation

/-- Resolved points correspond under an isomorphism of the ambient schemes. -/
theorem Subscheme.isMainResolvedAt_totalTransform_iso_iff {Y₁ Y₂ : Scheme.{u}} {β : ℕ} (e : Y₁ ≅ Y₂)
    (V : Fin (β + 1) → Subscheme Y₂) (W : Subscheme Y₂) (hWV : ∀ j, W.IsContainedIn (V j)) (x : Y₁) :
    Subscheme.IsMainResolvedAt (fun j => Subscheme.totalTransform e.hom (V j))
        (Subscheme.totalTransform e.hom W) x ↔
      Subscheme.IsMainResolvedAt V W (e.hom.base x) := by
  refine and_congr (FlatPreimm.isSimpleAt_totalTransform_iff e.hom W x) (forall_congr' fun j => ?_)
  exact FlatPreimm.isNormallyFlatAlongAt'_totalTransform_iff e.hom (V j) W (hWV j) x

/-- Condition (4) is invariant under isomorphism of the data. -/
theorem Subscheme.IsMain4Data.totalTransform_iso {Y₁ Y₂ : Scheme.{u}} {β : ℕ} (e : Y₁ ≅ Y₂)
    (V : Fin (β + 1) → Subscheme Y₂) (W : Subscheme Y₂) (hWV : ∀ j, W.IsContainedIn (V j))
    (h : Subscheme.IsMain4Data V W) :
    Subscheme.IsMain4Data (fun j => Subscheme.totalTransform e.hom (V j)) (Subscheme.totalTransform e.hom W) := by
  obtain ⟨hns, hnf⟩ := h
  refine ⟨?_, fun j x hx => ?_⟩
  · exact FlatPreimm.isNonsingular_totalTransform e.hom W hns
  · rw [FlatPreimm.pts_totalTransform] at hx
    exact (FlatPreimm.isNormallyFlatAlongAt'_totalTransform_iff e.hom (V j) W (hWV j) x).mpr
      (hnf j _ hx)

/-- The pull-back of a center along an isomorphism is a center. -/
theorem Subscheme.IsCenter.totalTransform_iso {Y₁ Y₂ : Scheme.{u}} (e : Y₁ ≅ Y₂) {B : Subscheme Y₂}
    (hB : B.IsCenter) : (Subscheme.totalTransform e.hom B).IsCenter := by
  rcases hB with rfl | ⟨hns, hirr⟩
  · left
    exact Subscheme.totalTransform_empty e.hom
  · rcases FlatPreimm.empty_or_isIrreducible_totalTransform e.hom B hirr with h | h
    · left
      exact h
    · right
      exact ⟨FlatPreimm.isNonsingular_totalTransform e.hom B hns, h⟩

/-- `Reach4` is invariant under isomorphism of the data: if `e : Y₁ ≅ Y₂` carries the data `(V₂; W₂)` to `(V₁; W₁)`
(`V₁ j = e⁻¹(V₂ j)`, `W₁ = e⁻¹(W₂)`), then `Reach4 ℓ Y₂ V₂ W₂` implies `Reach4 ℓ Y₁ V₁ W₁`.  Only the first monoidal
transformation is transported (`MonoidalTransformation.ofIso`): its strict transforms are the same subschemes of the
same scheme (`strictTransform_ofIso`), so the rest of the recursion is unchanged. -/
@[blueprint "lem:I.3-reach4-of-iso"
  (statement := /-- The property \texttt{Reach4} (\cref{def:I.3-reach4}) is invariant under isomorphism of the data: if $e\colon Y_1\cong Y_2$ carries $(V_2;W_2)$ to $(V_1;W_1)$, then $\mathrm{Reach4}\ \ell\ Y_2\ V_2\ W_2$ implies $\mathrm{Reach4}\ \ell\ Y_1\ V_1\ W_1$. (This is the identification of the monoidal transformations $\hat V_j(i+1)\to\hat V_j(i)$ ``with the monoidal transformations with center $\hat B_i$'', p.~175.) -/)
  (proof := /-- Only the first monoidal transformation is transported along $e$ (it is a monoidal transformation of $Y_1$ with the transported center), its strict transforms are the same subschemes of the same scheme, so the rest of the recursion is unchanged. -/)
  (latexEnv := "lemma")]
theorem Reach4.of_iso {β : ℕ} (ℓ : ℕ) {Y₁ Y₂ : Scheme.{u}} (e : Y₁ ≅ Y₂) (V₁ : Fin (β + 1) → Subscheme Y₁)
    (V₂ : Fin (β + 1) → Subscheme Y₂) (W₁ : Subscheme Y₁) (W₂ : Subscheme Y₂)
    (hWV : ∀ j, W₂.IsContainedIn (V₂ j))
    (hV : ∀ j, V₁ j = Subscheme.totalTransform e.hom (V₂ j)) (hW : W₁ = Subscheme.totalTransform e.hom W₂)
    (h : Reach4 ℓ Y₂ V₂ W₂) : Reach4 ℓ Y₁ V₁ W₁ := by
  have hV' : V₁ = fun j => Subscheme.totalTransform e.hom (V₂ j) := funext hV
  subst hV' hW
  cases ℓ with
  | zero => exact Subscheme.IsMain4Data.totalTransform_iso e V₂ W₂ hWV h
  | succ ℓ =>
    obtain ⟨B, t, ⟨⟨hBc, hBW⟩, h2, h3⟩, hrest⟩ := h
    refine ⟨Subscheme.totalTransform e.hom B, t.ofIso e, ⟨⟨hBc.totalTransform_iso e, ?_⟩, ?_, ?_⟩, ?_⟩
    · intro U
      exact FlatPreimm.totalTransform_mono e.hom (fun U => hBW U) U
    · intro x hx hres
      rw [FlatPreimm.pts_totalTransform] at hx
      exact h2 _ hx ((Subscheme.isMainResolvedAt_totalTransform_iso_iff e V₂ W₂ hWV x).mp hres)
    · intro x hx
      rw [FlatPreimm.pts_totalTransform] at hx
      refine ⟨fun j => ?_, ?_⟩
      · exact (FlatPreimm.isNormallyFlatAlongAt'_totalTransform_iff e.hom (V₂ j) B
          (hBW.trans (hWV j)) x).mpr ((h3 _ hx).1 j)
      · exact (FlatPreimm.isNormallyFlatAlongAt'_totalTransform_iff e.hom W₂ B hBW x).mpr (h3 _ hx).2
    · have hs : ∀ V : Subscheme Y₂, Subscheme.strictTransform (t.ofIso e) (Subscheme.totalTransform e.hom V) =
          Subscheme.strictTransform t V := fun V => MonoidalTransformation.strictTransform_ofIso e t V
      simp only [hs]
      exact hrest

/-! ### The statements -/

namespace MainTheorem


/-- **The ambient result of pp. 172–174** (quoted on p. 175 as "the previous result"): Main Theorem I(n) for a
non-singular irreducible algebraic scheme `X` of dimension `N`, `n < N` (the range of the fundamental
theorems).  Its conclusion reads, in the paper's terms: (1′) `B̄_i` is a non-singular irreducible subscheme of
`W̄(i)` which is contained in `S̄(i)`, i.e. (1) and (2); (2) all the `V̄_j(i)` and `W̄(i)` are normally flat along
`B̄_i`, i.e. (3); (3) `W̄(r)` is non-singular and all the `V̄_j(r)` are normally flat along `W̄(r)`, i.e. (4). -/
@[blueprint "def:I.3-main-I-ambient-statement"
  (statement := /-- The ambient result of pp.~172--174 (``the previous result'', p.~175): Main Theorem~I($n$) for a non-singular irreducible algebraic scheme $X$ of dimension $N>n$ in place of the arbitrary algebraic scheme $V_0$ (the range $N>n$ of the fundamental theorems). Its conclusion reads, in the paper's terms: ($1'$) $\bar B_i$ is a non-singular irreducible subscheme of $\bar W(i)$ which is contained in $\bar S(i)$ (i.e.\ (1) and (2)); (2) all the $\bar V_j(i)$ and $\bar W(i)$ are normally flat along $\bar B_i$ (i.e.\ (3)); (3) $\bar W(r)$ is non-singular and all the $\bar V_j(r)$ are normally flat along $\bar W(r)$ (i.e.\ (4)). -/)
  (latexEnv := "definition")]
def IAmbient (N n : ℕ) : Prop :=
  ∀ (X : Scheme.{u}), IsAmbient X N → ∀ (β : ℕ) (V : Fin β → Subscheme X) (W : Subscheme X),
    W.IsReduced → W.dim = (n : WithBot ℕ∞) → (∀ j, W.IsContainedIn (V j)) →
    ∃ (Y : Scheme.{u}) (s : MonoidalSuccession X Y), s.IsMainI (mainSystem V) W

end MainTheorem

/-! ### The sets `S(i)`: closedness, the effect of a monoidal transformation, prolongations -/

section Lemmas

variable {X : Scheme.{u}} {β : ℕ}

/-- p. 173: "(Note that `S(i)` is a closed subset of `W(i)` which is nowhere dense (Th. I, § 1, Ch. II).)", closedness.
Simple points are open (class 𝔅 (iii), `exists_isOpen_isSimpleAt`), and the normally flat points of each `V_j` are
open (Cor. of Th. 1, `Subscheme.exists_isOpen_isNormallyFlatAlongAt'`). -/
@[blueprint "lem:I.3-S-closed"
  (statement := /-- Let $V$ be an algebraic scheme, $V_1,\dots,V_\beta$ subschemes and $W$ a subscheme contained in $\bigcap V_j$. Then $S$ (\cref{def:I.3-main-S}) is a closed subset of $W$ (p.~173: ``(Note that $S(i)$ is a closed subset of $W(i)$ which is nowhere dense (Th.~I, \S1, Ch.~II).)''). -/)
  (proof := /-- The set of simple points of $W$ is open (property (iii) of the class $\mathfrak B$, p.~161), and for each $j$ the set of those points of $W$ at which $V_j$ is normally flat along $W$ is open (Corollary of Th.~1, \S1, Ch.~II, p.~189); $S$ is the complement in $W$ of the intersection of these finitely many open sets. -/)
  (latexEnv := "lemma")]
theorem Subscheme.isClosed_mainUnresolved [Hironaka.HironakaCitedResults.{u}] [IsAlgebraicScheme X] (V : Fin (β + 1) → Subscheme X)
    (W : Subscheme X) (hWV : ∀ j, W.IsContainedIn (V j)) : IsClosed (Subscheme.mainUnresolved V W) := by
  obtain ⟨Os, hOs, hsimple⟩ := Subscheme.exists_isOpen_isSimpleAt W
  choose Onf hOnf hnf using fun j => Subscheme.exists_isOpen_isNormallyFlatAlongAt' (V j) W
  have hopen : IsOpen (Os ∩ ⋂ j, Onf j) := hOs.inter (isOpen_iInter_of_finite hOnf)
  have heq : Subscheme.mainUnresolved V W = W.pts ∩ (Os ∩ ⋂ j, Onf j)ᶜ := by
    ext y
    simp only [Subscheme.mainUnresolved, Subscheme.IsMainResolvedAt, Set.mem_ofPred_eq, Set.mem_inter_iff,
      Set.mem_compl_iff, Set.mem_iInter]
    constructor
    · rintro ⟨hy, hn⟩
      refine ⟨hy, fun ⟨hyO, hyN⟩ => hn ⟨(hsimple y hy).mpr hyO, fun j =>
        (hnf j y hy (pts_subset_of_isContainedIn (hWV j) hy)).mpr (hyN j)⟩⟩
    · rintro ⟨hy, hn⟩
      refine ⟨hy, fun ⟨hs, hf⟩ => hn ⟨(hsimple y hy).mp hs, fun j =>
        (hnf j y hy (pts_subset_of_isContainedIn (hWV j) hy)).mp (hf j)⟩⟩
  rw [heq]
  exact W.support.isClosed.inter hopen.isClosed_compl

/-- Normal flatness along a maximal ideal: the graded pieces are vector spaces over the residue field. -/
theorem isNormallyFlatAlongIdeal_of_isMaximal {R : Type u} [CommRing R] (J : Ideal R) [J.IsMaximal] :
    IsNormallyFlatAlongIdeal J := by
  intro p
  let _ : Field (R ⧸ J) := Ideal.Quotient.field J
  exact Module.Free.of_divisionRing _ _

/-- At the generic point of an irreducible component of a reduced `W ⊆ ⋂ V_j` all the data are resolved: the ideal of
`W` is the maximal ideal (`stalkIdeal_eq_maximalIdeal_of_isReduced`), so `W` is simple there and the graded pieces are
vector spaces.  Hence every point of `W` has a generization at which `W` is resolved; this is the density of the
resolved points (p. 172: "the set of simple points of a reduced algebraic scheme is open and dense", "the set of those
points of `W` at which `V` is normally flat along `W` is an open dense subset of `W`"). -/
@[blueprint "lem:I.3-resolved-generization"
  (statement := /-- Let $W$ be a reduced subscheme of an algebraic scheme contained in $\bigcap V_j$. Every point of $W$ is a specialization of a point of $W$ at which the data are resolved (\cref{def:I.3-main-resolved}). (p.~172: ``the set of simple points of a reduced algebraic scheme is open and dense'' and ``if $V$ is an algebraic scheme and $W$ a reduced subscheme of $V$, the set of those points of $W$ at which $V$ is normally flat along $W$ is an open dense subset of $W$''.) -/)
  (proof := /-- At the generic point $\eta$ of an irreducible component of the reduced $W$ the ideal of $W$ is the maximal ideal of the local ring (it is a field), so $W$ is simple at $\eta$, and the graded pieces are vector spaces over the residue field, whence $V_j$ is normally flat along $W$ at $\eta$. Every point of $W$ specializes from the generic point of a component through it. -/)
  (latexEnv := "lemma")]
theorem Subscheme.exists_specializes_isMainResolvedAt [IsAlgebraicScheme X]
    (V : Fin (β + 1) → Subscheme X) (W : Subscheme X) (hW : W.IsReduced)
    (hWV : ∀ j, W.IsContainedIn (V j)) {x : X} (hx : x ∈ W.pts) :
    ∃ η : X, η ⤳ x ∧ Subscheme.IsMainResolvedAt V W η := by
  have hx' : x ∈ Set.range W.ι := by
    rw [Scheme.IdealSheafData.range_subschemeι]
    exact hx
  obtain ⟨y, rfl⟩ := hx'
  have := IsAlgebraicScheme.isNoetherian X
  have := isAlgebraicScheme_toScheme W
  have := IsAlgebraicScheme.isNoetherian W.toScheme
  obtain ⟨η, hη⟩ := QuasiSober.sober (isIrreducible_irreducibleComponent (x := y))
    isClosed_irreducibleComponent
  have hηc : closure {η} ∈ _root_.irreducibleComponents W.toScheme := by
    rw [hη.def]
    exact irreducibleComponent_mem_irreducibleComponents y
  have hηW : W.ι η ∈ W.pts := by
    show W.ι η ∈ (W.support : Set X)
    rw [← Scheme.IdealSheafData.range_subschemeι]
    exact ⟨η, rfl⟩
  have hsp : W.ι η ⤳ W.ι y := by
    have : η ⤳ y := by
      rw [specializes_iff_mem_closure, hη.def]
      exact mem_irreducibleComponent
    exact this.map W.ι.continuous
  have hWm := stalkIdeal_eq_maximalIdeal_of_isReduced W hW η hηc
  refine ⟨W.ι η, hsp, ⟨hηW, ?_⟩, fun j => ?_⟩
  · rw [hWm]
    show IsRegularLocalRing (IsLocalRing.ResidueField (X.presheaf.stalk (W.ι η)))
    infer_instance
  · have hVpts : W.ι η ∈ (V j).pts := pts_subset_of_isContainedIn (hWV j) hηW
    refine isNormallyFlatAlongAt'_of_isNormallyFlatAlongIdeal (V j) W hVpts hηW ?_
    rw [hWm]
    have hVle : (V j).stalkIdeal (W.ι η) ≤ IsLocalRing.maximalIdeal (X.presheaf.stalk (W.ι η)) :=
      stalkIdeal_le_maximalIdeal_of_mem_pts (V j) hVpts
    have hmax : (Ideal.map (Ideal.Quotient.mk ((V j).stalkIdeal (W.ι η)))
        (IsLocalRing.maximalIdeal (X.presheaf.stalk (W.ι η)))).IsMaximal := by
      rcases Ideal.map_eq_top_or_isMaximal_of_surjective
        (Ideal.Quotient.mk ((V j).stalkIdeal (W.ι η))) Ideal.Quotient.mk_surjective (IsLocalRing.maximalIdeal.isMaximal (X.presheaf.stalk (W.ι η))) with h | h
      · exfalso
        have h1 : (1 : X.presheaf.stalk (W.ι η) ⧸ (V j).stalkIdeal (W.ι η)) ∈ Ideal.map
            (Ideal.Quotient.mk ((V j).stalkIdeal (W.ι η)))
            (IsLocalRing.maximalIdeal (X.presheaf.stalk (W.ι η))) := by rw [h]; trivial
        obtain ⟨a, ha, ha1⟩ := (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).mp h1
        have : a - 1 ∈ (V j).stalkIdeal (W.ι η) := by
          rw [← Ideal.Quotient.eq]; exact ha1
        have h2 := hVle this
        have h3 : (1 : X.presheaf.stalk (W.ι η)) ∈
            IsLocalRing.maximalIdeal (X.presheaf.stalk (W.ι η)) := by
          have := Ideal.sub_mem _ ha h2
          simp at this
        exact (IsLocalRing.maximalIdeal.isMaximal (X.presheaf.stalk (W.ι η))).ne_top
          ((Ideal.eq_top_iff_one _).mpr h3)
      · exact h
    exact isNormallyFlatAlongIdeal_of_isMaximal _

/-- p. 173, nowhere density: for a reduced `W`, the resolved points are dense in `W` (open dense by (iii) and
Th. 1), so `S` has empty interior in `W`. -/
@[blueprint "lem:I.3-S-nowhere-dense"
  (statement := /-- Let $W$ be a reduced subscheme contained in $\bigcap V_j$. The resolved points are dense in $W$: $W\subseteq\overline{W\setminus S}$, i.e.\ $S$ is nowhere dense in $W$ (p.~173: ``(Note that $S(i)$ is a closed subset of $W(i)$ which is nowhere dense (Th.~I, \S1, Ch.~II).)''). -/)
  (proof := /-- By \cref{lem:I.3-resolved-generization} every point of $W$ is a specialization of a resolved point, which lies in $W\setminus S$. -/)
  (latexEnv := "lemma")]
theorem Subscheme.pts_subset_closure_diff_mainUnresolved [IsAlgebraicScheme X]
    (V : Fin (β + 1) → Subscheme X) (W : Subscheme X) (hW : W.IsReduced)
    (hWV : ∀ j, W.IsContainedIn (V j)) : W.pts ⊆ closure (W.pts \ Subscheme.mainUnresolved V W) := by
  intro x hx
  obtain ⟨η, hηx, hη⟩ := Subscheme.exists_specializes_isMainResolvedAt V W hW hWV hx
  refine closure_mono (Set.singleton_subset_iff.mpr ?_) (specializes_iff_mem_closure.mp hηx)
  have hηW : η ∈ W.pts := hη.1.1
  exact ⟨hηW, fun h => h.2 hη⟩

/-- `W ⊆ V_0 = X` and `W ⊆ V_j`: the containments `W ⊆ ⋂ V_j` of the data give `W ⊆ mainSystem V j` for all `j`. -/
theorem mainSystem_isContainedIn (V : Fin β → Subscheme X) (W : Subscheme X)
    (hWV : ∀ j, W.IsContainedIn (V j)) : ∀ j, W.IsContainedIn (mainSystem V j) := by
  intro j
  refine Fin.cases ?_ (fun i => ?_) j
  · intro U
    exact bot_le
  · exact hWV i

/-- The end scheme of a succession of an algebraic scheme is algebraic (each `f_i` is proper, hence of finite type). -/
theorem MonoidalSuccession.isAlgebraicScheme_target [Hironaka.HironakaCitedResults.{u}] {Y : Scheme.{u}} [hX : IsAlgebraicScheme X]
    (s : MonoidalSuccession X Y) : IsAlgebraicScheme Y := by
  revert hX
  induction s with
  | nil X => exact inferInstance
  | cons B t rest ih =>
    intro hX
    have := t.isAlgebraicScheme
    exact ih

/-- Off the exceptional divisor a monoidal transformation is a local isomorphism (p. 167): a point `y` of the strict
transforms off `f⁻¹(B)` is resolved iff `f(y)` is.  (As in
`DatumI.Raw.resolvedAt_transform_of_resolvedAt_of_notMem_exceptional`, without the normal crossings of `E`.) -/
@[blueprint "lem:I.3-resolved-off-exceptional"
  (statement := /-- Let $f\colon V'\to V$ be a monoidal transformation with center $B$ and $y$ a point of $V'$ outside $f^{-1}(B)$. Then $y$ is resolved for the strict transforms of the data if and only if $f(y)$ is resolved for the data (p.~167: $f$ is an isomorphism outside the center). -/)
  (proof := /-- Outside $f^{-1}(B)$ the monoidal transformation is a local isomorphism (a flat preimmersion lifting the open immersion of $V-B$), under which strict transforms are pull-backs; simplicity and normal flatness are invariant under flat preimmersions. -/)
  (latexEnv := "lemma")]
theorem Subscheme.isMainResolvedAt_strictTransform_iff_of_notMem_exceptional {B : Subscheme X}
    (t : MonoidalTransformation X B) (V : Fin (β + 1) → Subscheme X) (W : Subscheme X)
    (hWV : ∀ j, W.IsContainedIn (V j)) {y : t.X'} (hyE : y ∉ t.exceptional.pts) :
    Subscheme.IsMainResolvedAt (fun j => Subscheme.strictTransform t (V j))
      (Subscheme.strictTransform t W) y ↔ Subscheme.IsMainResolvedAt V W (t.f.base y) := by
  obtain ⟨Z, ι, j', h1, h2, h3, h4, -, hcomp, hrι, hrange, hexc, htt⟩ :=
    Hironaka.DatumTransform.exists_flat_isPreimmersion_off_center t
  have hyr : y ∈ Set.range j'.base := by rw [hrange]; exact hyE
  obtain ⟨u, rfl⟩ := hyr
  have hc : ι.base u = t.f.base (j'.base u) := (hcomp u).symm
  rw [← hc]
  refine and_congr ?_ (forall_congr' fun j => ?_)
  · rw [← FlatPreimm.isSimpleAt_totalTransform_iff j' _ u, ← FlatPreimm.isSimpleAt_totalTransform_iff ι _ u, htt]
  · rw [← FlatPreimm.isNormallyFlatAlongAt'_totalTransform_iff j' _ _
      (Subscheme.IsContainedIn.strictTransform t (hWV j)) u,
      ← FlatPreimm.isNormallyFlatAlongAt'_totalTransform_iff ι _ _ (hWV j) u, htt, htt]

/-- Resolved points off the exceptional divisor lie over resolved points (one direction of the above). -/
theorem Subscheme.isMainResolvedAt_strictTransform_of_notMem_exceptional {B : Subscheme X}
    (t : MonoidalTransformation X B) (V : Fin (β + 1) → Subscheme X) (W : Subscheme X)
    (hWV : ∀ j, W.IsContainedIn (V j)) {y : t.X'} (hyE : y ∉ t.exceptional.pts)
    (hres : Subscheme.IsMainResolvedAt V W (t.f.base y)) :
    Subscheme.IsMainResolvedAt (fun j => Subscheme.strictTransform t (V j))
      (Subscheme.strictTransform t W) y :=
  (Subscheme.isMainResolvedAt_strictTransform_iff_of_notMem_exceptional t V W hWV hyE).mpr hres

/-- Condition (4) for the data `(V; W)` iff `S` is empty. -/
theorem Subscheme.isMain4Data_iff_mainUnresolved_eq_empty (V : Fin (β + 1) → Subscheme X) (W : Subscheme X) :
    Subscheme.IsMain4Data V W ↔ Subscheme.mainUnresolved V W = ∅ := by
  unfold Subscheme.IsMain4Data Subscheme.mainUnresolved Subscheme.IsMainResolvedAt
  constructor
  · rintro ⟨hns, hnf⟩
    refine Set.eq_empty_of_forall_notMem fun x ⟨hx, hn⟩ => hn ⟨?_, fun j => hnf j x hx⟩
    exact ⟨hx, Subscheme.isRegular_stalk_quot W hns hx⟩
  · intro h
    have hres : ∀ x ∈ W.pts, W.IsSimpleAt x ∧ ∀ j, Subscheme.IsNormallyFlatAlongAt' (V j) W x := by
      intro x hx
      by_contra hn
      exact (Set.eq_empty_iff_forall_notMem.mp h) x ⟨hx, hn⟩
    exact ⟨Subscheme.isNonsingular_of_stalk_quot W fun z hz => (hres z hz).1.2,
      fun j x hx => (hres x hx).2 j⟩

namespace MonoidalSuccession

variable {Y Z : Scheme.{u}}

/-- (1), (2), (3) for all `i` are inherited by and composed from the pieces of a prolongation. -/
theorem isMain123With_append (Cen : ∀ {X : Scheme.{u}}, Subscheme X → Prop) (s : MonoidalSuccession X Y)
    (s' : MonoidalSuccession Y Z) (V : Fin (β + 1) → Subscheme X) (W : Subscheme X) :
    (s.append s').IsMain123With Cen V W ↔
      s.IsMain123With Cen V W ∧
        s'.IsMain123With Cen (fun j => s.strictTransform (V j)) (s.strictTransform W) := by
  induction s generalizing β with
  | nil X => simp [IsMain123With]
  | cons B t rest ih =>
    simp only [cons_append, IsMain123With, ih, strictTransform_cons, and_assoc]

/-- p. 174: "(4) holds iff `S(r)` is empty": `W(r)` non-singular with all `V_j(r)` normally flat along it iff
every point of `W(r)` is a simple point at which all the `V_j(r)` are normally flat along `W(r)`. -/
@[blueprint "lem:I.3-main-4-iff-S-empty"
  (statement := /-- For a succession $\{f_i\}_{0\le i<r}$, condition (4) holds if and only if $S(r)$ is empty: $W(r)$ is non-singular with all $V_j(r)$ normally flat along it if and only if every point of $W(r)$ is a simple point at which all the $V_j(r)$ are normally flat along $W(r)$ (used in p.~174: ``We first remark that the above assertion is equivalent to that of the theorem''). -/)
  (proof := /-- A scheme is non-singular if and only if all its points are simple, and normal flatness along $W$ is required at every point of $W$. -/)
  (latexEnv := "lemma")]
theorem isMain4_iff_mainUnresolvedAt_eq_empty (s : MonoidalSuccession X Y) (V : Fin (β + 1) → Subscheme X)
    (W : Subscheme X) : s.IsMain4 V W ↔ mainUnresolvedAt s V W = ∅ :=
  Subscheme.isMain4Data_iff_mainUnresolved_eq_empty _ _

/-- p. 174, "the image of `S(r′)` in `V₀` is ... always contained in that of `S(r)`": one step.  Off the center the
monoidal transformation is a local isomorphism, so the points of `W(i+1)` over resolved points of `W(i)` not on the
center are resolved; condition (2) says that the center contains no resolved point. -/
@[blueprint "lem:I.3-S-transform-subset"
  (statement := /-- Let $f\colon V'\to V$ be a monoidal transformation with center $B$ such that $B$ contains no resolved point (condition (2)). Then the points of $S'$ (for the strict transforms) lie over $S$: $S'\subseteq f^{-1}(S)$ (p.~174: ``the image of $S(r')$ in $V_0$ is different from (but always contained in) that of $S(r)$'', one step). -/)
  (proof := /-- A point of the strict transform over a resolved point of $V$ is resolved: off the center $f$ is a local isomorphism (\cref{lem:I.3-resolved-off-exceptional}) and by (2) the points over the center are not resolved to begin with. -/)
  (latexEnv := "lemma")]
theorem mainUnresolved_strictTransform_subset {B : Subscheme X} (t : MonoidalTransformation X B)
    (V : Fin (β + 1) → Subscheme X) (W : Subscheme X) (hWV : ∀ j, W.IsContainedIn (V j))
    (hB : ∀ x ∈ B.pts, ¬ Subscheme.IsMainResolvedAt V W x) :
    Subscheme.mainUnresolved (fun j => Subscheme.strictTransform t (V j)) (Subscheme.strictTransform t W) ⊆
      t.f.base ⁻¹' Subscheme.mainUnresolved V W := by
  rintro y ⟨hyW, hyn⟩
  refine ⟨MonoidalTransformation.pts_strictTransform_subset t W hyW, fun hres => hyn ?_⟩
  by_cases hyE : y ∈ t.exceptional.pts
  · exact absurd hres (hB _ (by rwa [MonoidalTransformation.pts_exceptional] at hyE))
  · exact Subscheme.isMainResolvedAt_strictTransform_of_notMem_exceptional t V W hWV hyE hres

/-- Along a prolongation satisfying (2), the unresolved points lie over unresolved points (iterating
`mainUnresolved_strictTransform_subset`). -/
theorem mainUnresolvedAt_subset_preimage (s' : MonoidalSuccession Y Z) (V : Fin (β + 1) → Subscheme Y)
    (W : Subscheme Y) (hWV : ∀ j, W.IsContainedIn (V j)) (h : s'.IsMain123 V W) :
    mainUnresolvedAt s' V W ⊆ s'.composite.base ⁻¹' Subscheme.mainUnresolved V W := by
  induction s' with
  | nil X => intro y hy; exact hy
  | cons B t rest ih =>
    obtain ⟨⟨-, hB, -⟩, hrest⟩ := h
    have hWV' : ∀ j, (Subscheme.strictTransform t W).IsContainedIn
        (Subscheme.strictTransform t (V j)) := fun j =>
      Subscheme.IsContainedIn.strictTransform t (hWV j)
    intro z hz
    have h1 := ih (fun j => Subscheme.strictTransform t (V j)) (Subscheme.strictTransform t W) hWV' hrest hz
    have h2 := mainUnresolved_strictTransform_subset t V W hWV hB h1
    simpa [composite_cons] using h2

/-- p. 174: "the image of `S(r′)` in `V₀` is different from (but always contained in) that of `S(r)`": the
containment, for a prolongation satisfying (2). -/
@[blueprint "lem:I.3-main-image-append"
  (statement := /-- Let $\{f_i\}_{0\le i<r}$ be a succession and $\{f_i\}_{r\le i<r'}$ a prolongation satisfying (2). Then $\bar S(r')\subseteq\bar S(r)$ (p.~174: ``such that the image of $S(r')$ in $V_0$ is different from (but always contained in) that of $S(r)$''). -/)
  (proof := /-- Iterate \cref{lem:I.3-S-transform-subset} along the prolongation: the points of $S(r')$ lie over points of $S(r)$. -/)
  (latexEnv := "lemma")]
theorem mainImage_append_subset [IsAlgebraicScheme X] (s : MonoidalSuccession X Y)
    (s' : MonoidalSuccession Y Z) (V : Fin (β + 1) → Subscheme X) (W : Subscheme X)
    (hWV : ∀ j, W.IsContainedIn (V j))
    (h : s'.IsMain123 (fun j => s.strictTransform (V j)) (s.strictTransform W)) :
    mainImage (s.append s') V W ⊆ mainImage s V W := by
  rintro _ ⟨z, hz, rfl⟩
  have hz' : z ∈ mainUnresolvedAt s' (fun j => s.strictTransform (V j)) (s.strictTransform W) := by
    simpa [mainUnresolvedAt, strictTransform_append] using hz
  have hWV' : ∀ j, (s.strictTransform W).IsContainedIn (s.strictTransform (V j)) := fun j =>
    isContainedIn_strictTransform s (hWV j)
  have h1 := mainUnresolvedAt_subset_preimage s' _ _ hWV' h hz'
  refine ⟨s'.composite.base z, h1, ?_⟩
  simp [composite_append]

/-- p. 174: "`S̄(r)` ... is a closed subset of `V₀` (contained in `W`) because all the morphisms `f_i` are proper". -/
@[blueprint "lem:I.3-main-image-closed"
  (statement := /-- $\bar S(r)$ is a closed subset of $V_0$ contained in $W$ (p.~174: ``which is a closed subset of $V_0$ (contained in $W$) because all the morphisms $f_i$ are proper''). -/)
  (proof := /-- $S(r)$ is closed (\cref{lem:I.3-S-closed}) and the composite of the $f_i$ is proper, hence closed; $S(r)\subseteq W(r)$ lies over $W$. -/)
  (latexEnv := "lemma")]
theorem isClosed_mainImage [Hironaka.HironakaCitedResults.{u}] [IsAlgebraicScheme X] (s : MonoidalSuccession X Y)
    (V : Fin (β + 1) → Subscheme X) (W : Subscheme X) (hWV : ∀ j, W.IsContainedIn (V j)) :
    IsClosed (mainImage s V W) ∧ mainImage s V W ⊆ W.pts := by
  have := s.isAlgebraicScheme_target
  have := IsAlgebraicScheme.isNoetherian X
  have hWV' : ∀ j, (s.strictTransform W).IsContainedIn (s.strictTransform (V j)) := fun j =>
    isContainedIn_strictTransform s (hWV j)
  refine ⟨s.isClosed_image_composite
    (Subscheme.isClosed_mainUnresolved _ _ hWV'), ?_⟩
  rintro _ ⟨z, ⟨hz, -⟩, rfl⟩
  exact s.pts_strictTransform_subset W hz

end MonoidalSuccession

/-- p. 174: "We first remark that the above assertion is equivalent to that of the theorem": the direction used.
If every succession satisfying (1), (2), (3) with `S(r) ≠ ∅` has a prolongation satisfying (1), (2), (3) with
`S̄(r′) ⊂ S̄(r)`, then there is a succession satisfying (1)–(4) (descending chain of closed subsets of the
noetherian scheme `V₀`, starting from the empty succession). -/
@[blueprint "lem:I.3-main-I-improve"
  (statement := /-- Let $V_0$ be an algebraic scheme. Suppose that every succession satisfying (1), (2), (3) for all $i$ with $S(r)\neq\emptyset$ has a prolongation satisfying (1), (2), (3) with $\bar S(r')\subsetneq\bar S(r)$. Then there is a finite succession satisfying (1), (2), (3) and (4) (p.~174: ``We first remark that the above assertion is equivalent to that of the theorem''). -/)
  (proof := /-- Descending chain of closed subsets of the noetherian scheme $V_0$ (\cref{lem:I.3-main-image-closed}), by well-founded induction starting from the empty succession; when $S(r)$ is empty, (4) holds by \cref{lem:I.3-main-4-iff-S-empty}. -/)
  (latexEnv := "lemma")]
theorem exists_isMainI_of_improve [Hironaka.HironakaCitedResults.{u}] [IsAlgebraicScheme X] (V : Fin β → Subscheme X) (W : Subscheme X)
    (hWV : ∀ j, W.IsContainedIn (V j))
    (hP : ∀ (Y : Scheme.{u}) (s : MonoidalSuccession X Y), s.IsMain123 (mainSystem V) W →
      (s.mainUnresolvedAt (mainSystem V) W).Nonempty →
      ∃ (Y' : Scheme.{u}) (t : MonoidalSuccession Y Y'), (s.append t).IsMain123 (mainSystem V) W ∧
        (s.append t).mainImage (mainSystem V) W ⊂ s.mainImage (mainSystem V) W) :
    ∃ (Y : Scheme.{u}) (s : MonoidalSuccession X Y), s.IsMainI (mainSystem V) W := by
  have hWV' := mainSystem_isContainedIn V W hWV
  have := IsAlgebraicScheme.noetherianSpace X
  have key : ∀ C : TopologicalSpace.Closeds X, ∀ (Y : Scheme.{u}) (s : MonoidalSuccession X Y),
      s.IsMain123 (mainSystem V) W → (s.mainImage (mainSystem V) W : Set X) = C →
      ∃ (Y : Scheme.{u}) (s : MonoidalSuccession X Y), s.IsMainI (mainSystem V) W := by
    intro C
    induction C using WellFoundedLT.induction with
    | _ C ih =>
      intro Y s hs hC
      by_cases hne : (s.mainUnresolvedAt (mainSystem V) W).Nonempty
      · obtain ⟨Y', t, ht, hlt⟩ := hP Y s hs hne
        refine ih ⟨(s.append t).mainImage (mainSystem V) W,
          (MonoidalSuccession.isClosed_mainImage _ _ _ hWV').1⟩ ?_ Y' (s.append t) ht rfl
        rw [← SetLike.coe_ssubset_coe]
        exact hC ▸ hlt
      · refine ⟨Y, s, hs, ?_⟩
        rw [MonoidalSuccession.isMain4_iff_mainUnresolvedAt_eq_empty]
        exact Set.not_nonempty_iff_eq_empty.mp hne
  exact key ⟨(MonoidalSuccession.nil X).mainImage (mainSystem V) W,
    (MonoidalSuccession.isClosed_mainImage _ _ _ hWV').1⟩ X (MonoidalSuccession.nil X) trivial rfl

end Lemmas

end Hironaka
