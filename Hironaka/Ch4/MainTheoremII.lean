/-
Copyright (c) 2026 Daattavya Aggarwal, Minhyong Kim, Oisin Kim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daattavya Aggarwal, Minhyong Kim, Oisin Kim
-/
module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.Order.CompletePartialOrder
public import Architect
public import Hironaka.Ch4.Conclusion
public import Hironaka.Compat.ResolveComponents
public import Hironaka.Statements

/-!
# Ch. I §3 (pp. 176–177): Main Theorem II(N)

> **Main Theorem II(N).**  Let `X` be a non-singular algebraic scheme of dimension `N`.  Let `J` be a
> coherent sheaf of non-zero ideals on `X`, and `E` a reduced subscheme of `X` which is everywhere
> of codimension one and has only normal crossings.  Then there exists a finite succession of
> monoidal transformations `{f_i : X_{i+1} → X_i}` with centers `B_i` in `X_i`, where `0 ≦ i < r`
> and `X_0 = X`, which has the following properties:
> (1) `B_i` is a non-singular irreducible subscheme of `X_i`;
> (2) if `J_{i+1}` is the weak transform of `J_i` by the monoidal transformations `f_i` for all `i`,
> where `J_0 = J`, and if `d_i` is the maximal integer attained by `ν(J_{iy})` for the points `y` of
> `X_i`, then `d_i` is a positive integer and `ν(J_{iz}) = d_i` for all the points `z` of `B_i`;
> (3) if `E_{i+1}` denotes the reduced subscheme `red(f_i⁻¹(E_i ∪ B_i))` of `X_{i+1}` for all `i`,
> where `E_0 = E`, then `E_i` has only normal crossings with `B_i`; and
> (4) `E_r` has only normal crossings and `J_r` is equal to `O_{X_r}`.  (p. 176)

> As is easily seen, the proof of the main theorem can be reduced to the case in which `X` is
> irreducible.  Assuming that `X` is irreducible, we apply the fundamental theorem `II₂^N` to the
> resolution datum on `X`: `ℜ^N_II = (E_1, …, E_α | J, b ; a_1, …, a_α)`, where `b = 1`, the `E_i`
> denote the irreducible components of `E`, and all the integers `a_i` are zero.  If
> `{f_i : X_{i+1} → X_i}` for `0 ≦ i < r'` is a succession of monoidal transformations which is
> obtained by applying the fundamental theorem to the above `ℜ^N_II`, then we take the smallest
> integer `r` such that `O_{X_r}` is the sheaf of ideals attached to the transform of `ℜ^N_II` by the
> succession `{f_i, 0 ≦ i < r}`.  Then this succession of `r` monoidal transformations has the
> properties stated in main theorem II(N).  (pp. 176–177)

The statement is `MainTheorem.II`, with the succession and its properties (1)–(4) as the recursively
defined predicate `MonoidalSuccession.IsMainSuccession` (as for permissibility, Definition 8, the
data `J_i`, `E_i` are carried along the succession).  The proof follows the printed one:

* the datum `ℜ = (E_1, …, E_α | J, 1 ; 0, …, 0)` with the irreducible components `E_i` of `E`
  (`DatumII.Raw.exists_mainDatum`);
* the fundamental theorem `II₂` (here: for a non-singular algebraic scheme which need not be
  irreducible, `exists_isPermissibleII_resolvedEverywhere_of_isNonsingular` of
  `Hironaka/Compat/ResolveComponents.lean`, the reduction "easily seen" on p. 176);
* the smallest `r` (the first stage with `J_r = O`), and the properties (1)–(4) read off the
  permissibility of the succession for `ℜ` (`exists_isMainSuccession_of_isPermissibleII`).

Deviation from the paper (gap filled): the reduction to an irreducible `X` ("As is easily seen") is
carried out in `Hironaka/Compat/ResolveComponents.lean`; the steps of the proof which the paper does
not spell out (that the datum is a datum, that `ν(ℜ_i)` is the maximum of the orders `ν(J_{iy})`
over all `y`, that the transform of `J` is the weak transform also for an empty center, that
`E_{i+1}` has the points of the union of the `E'_j` of the transform) are proved.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace IsLocalRing

namespace Hironaka

universe u

/-! ### The statement -/

namespace MonoidalSuccession


end MonoidalSuccession


/-! ### The datum of the proof (p. 177) and the facts on `ν` -/

section Facts

variable {X : Scheme.{u}}

/-- `ν(J_x) ≥ 1` iff `J_x` is a proper ideal (a proper ideal of a local ring lies in the maximal
ideal, `Ideal.ord_basic`). -/
theorem Subscheme.one_le_nu_stalkIdeal_iff (J : Subscheme X) (x : X) :
    1 ≤ Ideal.nu (J.stalkIdeal x) ↔ J.stalkIdeal x ≠ ⊤ := by
  rw [(Ideal.ord_basic (maximalIdeal (X.presheaf.stalk x)) (J.stalkIdeal x) ⊤ ⊤).2.1]
  exact ⟨fun h htop => (maximalIdeal.isMaximal _).ne_top (top_le_iff.mp (htop ▸ h)),
    fun h => IsLocalRing.le_maximalIdeal h⟩

theorem Subscheme.exists_stalkIdeal_ne_top_of_ne_top {J : Subscheme X} (h : J ≠ ⊤) :
    ∃ y, J.stalkIdeal y ≠ ⊤ := by
  by_contra hcon
  push Not at hcon
  exact h (Subscheme.ext_stalkIdeal fun x => by rw [hcon x, Subscheme.stalkIdeal_top_eq])

/-- A datum of type II with `b = 1` which is resolved everywhere has `J = O_X`:
`ν(J_x) + ∑_{x ∈ E_i} a_i < 1` for every `x`. -/
theorem DatumII.Raw.J_eq_top_of_resolvedEverywhere (ℜ : DatumII.Raw X) (hb : ℜ.b = 1)
    (h : ℜ.ResolvedEverywhere) : ℜ.J = ⊤ := by
  refine Subscheme.ext_stalkIdeal fun x => ?_
  rw [Subscheme.stalkIdeal_top_eq]
  by_contra hne
  have h1 : 1 ≤ ℜ.nuAt x := (ℜ.J.one_le_nu_stalkIdeal_iff x).mpr hne
  have h2 : (ℜ.weight x : ℕ∞) + ℜ.nuAt x < ℜ.b := h x
  rw [hb] at h2
  exact absurd (lt_of_le_of_lt (h1.trans le_add_self) h2) (lt_irrefl _)

/-- The property (2) of Main Theorem II(N), for the datum `ℜ` with `b = 1`: if `J ≠ O_X` and `B` is
a permissible center for `ℜ`, then `ν(ℜ)` is the maximal integer attained by the orders `ν(J_y)`
over all the points `y` of `X`, it is positive, and `ν(J_z) = ν(ℜ)` for all `z ∈ B`.  This uses
only that, for `b = 1`, `S(ℜ)` contains all the points with `ν(J_y) ≥ 1`, whatever the weights
are, and `B ⊆ S_ν(ℜ)`. -/
theorem DatumII.Raw.exists_property_two [Hironaka.HironakaCitedResults.{u}] [IsAlgebraicScheme X] (hX : X.IsNonsingular)
    (ℜ : DatumII.Raw X) (hℜ : ℜ.IsDatum) (hb : ℜ.b = 1) (hJ : ℜ.J ≠ ⊤) {B : Subscheme X}
    (hB : ℜ.IsPermissible B) :
    ∃ d : ℕ, 0 < d ∧ IsGreatest (Set.range fun y => Ideal.nu (ℜ.J.stalkIdeal y)) (d : ℕ∞) ∧
      ∀ z ∈ B.pts, Ideal.nu (ℜ.J.stalkIdeal z) = d := by
  classical
  have hJstalk : ∀ x, ℜ.J.stalkIdeal x ≠ ⊥ := hℜ.2.2.2
  obtain ⟨y₀, hy₀⟩ := Subscheme.exists_stalkIdeal_ne_top_of_ne_top hJ
  have h1 : (1 : ℕ∞) ≤ ℜ.nuAt y₀ := (ℜ.J.one_le_nu_stalkIdeal_iff y₀).mpr hy₀
  have hS : ∀ y, 1 ≤ ℜ.nuAt y → y ∈ ℜ.S := fun y hy => by
    show (ℜ.b : ℕ∞) ≤ (ℜ.weight y : ℕ∞) + ℜ.nuAt y
    rw [hb]
    exact (by simpa using hy : (1 : ℕ∞) ≤ ℜ.nuAt y).trans le_add_self
  have hν1 : 1 ≤ ℜ.nu :=
    h1.trans (le_iSup₂ (f := fun x (_ : x ∈ ℜ.S) => ℜ.nuAt x) y₀ (hS y₀ h1))
  have hνtop : ℜ.nu ≠ ⊤ := ℜ.nu_ne_top hX hJstalk
  obtain ⟨y₁, hy₁S, hy₁⟩ := ℜ.exists_mem_S_nuAt_eq_nu hX hJstalk ⟨y₀, hS y₀ h1⟩
  have hle : ∀ y, ℜ.nuAt y ≤ ℜ.nu := fun y => by
    by_cases h0 : 1 ≤ ℜ.nuAt y
    · exact le_iSup₂ (f := fun x (_ : x ∈ ℜ.S) => ℜ.nuAt x) y (hS y h0)
    · have : ℜ.nuAt y = 0 := by
        push Not at h0
        exact Order.lt_one_iff.mp h0
      rw [this]
      exact zero_le
  obtain ⟨d, hd⟩ : ∃ d : ℕ, ℜ.nu = d := by
    obtain ⟨d, hd⟩ := ENat.ne_top_iff_exists.mp hνtop
    exact ⟨d, hd.symm⟩
  refine ⟨d, ?_, ⟨⟨y₁, ?_⟩, ?_⟩, fun z hz => ?_⟩
  · have : (1 : ℕ∞) ≤ d := hd ▸ hν1
    exact_mod_cast this
  · exact hy₁.trans hd
  · rintro _ ⟨y, rfl⟩
    exact hd ▸ hle y
  · have hz' : z ∈ ℜ.sStar := hB.2.1 hz
    exact le_antisymm (hd ▸ hle z) (hd ▸ hz'.2)

/-- The union of the components of the transform of a datum: `E'_1 ∪ ⋯ ∪ E'_α ∪ E_{α+1}` has the
points `f⁻¹(E_1 ∪ ⋯ ∪ E_α ∪ B)` (the strict transform of `E_i` contains `f⁻¹(E_i)` off `f⁻¹(B)`,
and `E_{α+1} = f⁻¹(B)`). -/
theorem DatumII.Raw.pts_eUnion_transform (ℜ : DatumII.Raw X) {B : Subscheme X}
    (t : MonoidalTransformation X B) :
    (ℜ.transform t).eUnion.pts = t.f.base ⁻¹' (ℜ.eUnion.pts ∪ B.pts) := by
  classical
  unfold DatumII.Raw.eUnion
  rw [Subscheme.pts_iInf, Subscheme.pts_iInf]
  ext y
  simp only [Set.mem_iUnion, Set.mem_preimage, Set.mem_union]
  change (∃ i : Fin (ℜ.α + 1), y ∈ ((ℜ.transform t).E i).pts) ↔ _
  rw [Fin.exists_fin_succ']
  simp only [DatumII.Raw.transform, Fin.snoc_castSucc, Fin.snoc_last]
  constructor
  · rintro (⟨i, hi⟩ | hexc)
    · exact Or.inl ⟨i, t.pts_strictTransform_subset _ hi⟩
    · rw [t.pts_exceptional] at hexc
      exact Or.inr hexc
  · rintro (⟨i, hi⟩ | hB)
    · by_cases hy : y ∈ t.exceptional.pts
      · exact Or.inr hy
      · exact Or.inl ⟨i, (t.mem_pts_strictTransform_iff_of_notMem _ hy).mpr hi⟩
    · exact Or.inr (by rw [t.pts_exceptional]; exact hB)

/-- The points of `E_{i+1} = red(f_i⁻¹(E_i ∪ B_i))` (p. 176, (3)). -/
theorem pts_radical_totalTransform_union {B : Subscheme X} (t : MonoidalTransformation X B)
    (E : Subscheme X) :
    Subscheme.pts (Subscheme.totalTransform t.f (E.union B)).radical =
      t.f.base ⁻¹' (E.pts ∪ B.pts) := by
  have h1 : Subscheme.pts (Subscheme.totalTransform t.f (E.union B)).radical =
      Subscheme.pts (Subscheme.totalTransform t.f (E.union B)) := rfl
  rw [h1, Subscheme.pts_totalTransform_eq_preimage]
  exact congrArg _ (Subscheme.pts_inf E B)

/-- For a permissible center `B`, the ideal of the transform of `ℜ` is the weak transform of `J`
(Ch. III, Remark 2, p. 214; p. 176: "This is the kind of transform of a coherent sheaf of ideals that
has appeared in the definition of the transform of a resolution datum of type `ℜ^N_II`"), also for
an empty center, where the monoidal transformation is an isomorphism and both are the total
transform. -/
theorem DatumII.Raw.transform_J_eq_weakTransform_of_isPermissible [IsAlgebraicScheme X]
    (hX : X.IsNonsingular) (ℜ : DatumII.Raw X) (hℜ : ℜ.IsDatum) {B : Subscheme X}
    (t : MonoidalTransformation X B) (hB : ℜ.IsPermissible B) :
    (ℜ.transform t).J = Subscheme.weakTransform t ℜ.J := by
  by_cases hne : B.pts.Nonempty
  · exact DatumII.Raw.transform_J_eq_weakTransform hX ℜ hℜ t hB hne
  · have hB0 : B = Subscheme.empty := by
      rcases hB.1 with h | ⟨-, hirr⟩
      · exact h
      · exact absurd (Subscheme.isIrreducible_pts B hirr).nonempty hne
    subst hB0
    have hnogen : ¬ ∃ ξ : X, IsGenericPoint ξ (Subscheme.empty : Subscheme X).pts :=
      fun ⟨ξ, hξ⟩ => by simpa [Subscheme.pts_empty] using hξ.mem
    unfold Subscheme.weakTransform
    split_ifs
    show Subscheme.divPow (Subscheme.totalTransform t.f ℜ.J) t.exceptional ℜ.nu.toNat = _
    have : t.exceptional = Subscheme.empty := Subscheme.totalTransform_empty t.f
    rw [this, Subscheme.divPow_empty]

theorem hasOnlyNormalCrossings_of_pts_eq {E₁ E₂ : Subscheme X} (h : E₁.pts = E₂.pts)
    (h₁ : E₁.HasOnlyNormalCrossings) : E₂.HasOnlyNormalCrossings := fun x =>
  (Subscheme.hasOnlyNormalCrossingsWithAt_congr h ⊥ x).mp (h₁ x)

end Facts

/-! ### The properties (1)–(4) from a permissible succession which resolves the datum -/

namespace MonoidalSuccession

variable {X Y : Scheme.{u}}

private theorem exists_isMainSuccession_of_isAlgebraicScheme [Hironaka.HironakaCitedResults.{u}] (s : MonoidalSuccession X Y)
    (hXa : IsAlgebraicScheme X) (hX : X.IsNonsingular) :
    ∀ (ℜ : DatumII.Raw X) (J E : Subscheme X), ℜ.IsDatum → ℜ.b = 1 → ℜ.J = J →
      ℜ.eUnion.pts = E.pts → s.IsPermissibleII ℜ → (s.transformII ℜ).ResolvedEverywhere →
      ∃ (Y' : Scheme.{u}) (s' : MonoidalSuccession X Y'), s'.IsMainSuccession J E := by
  induction s with
  | nil _ =>
    intro ℜ J E hℜ hb hJ hE _ hres
    exact ⟨_, MonoidalSuccession.nil _, hasOnlyNormalCrossings_of_pts_eq hE hℜ.2.2.1,
      hJ ▸ ℜ.J_eq_top_of_resolvedEverywhere hb hres⟩
  | cons B t rest ih =>
    intro ℜ J E hℜ hb hJ hE hs hres
    have := hXa
    subst hJ
    by_cases hJtop : ℜ.J = ⊤
    · exact ⟨_, MonoidalSuccession.nil _, hasOnlyNormalCrossings_of_pts_eq hE hℜ.2.2.1, hJtop⟩
    · have hperm : ℜ.IsPermissible B := hs.1
      obtain ⟨d, hd0, hdmax, hdz⟩ := ℜ.exists_property_two hX hℜ hb hJtop hperm
      have hX' := (t.isNonsingular_and_isNonsingular_exceptional hX hperm.1.isNonsingular).1
      have hℜ' := (DatumII.Raw.transform_isDatum hX ℜ hℜ t hperm).1
      have hJ' : (ℜ.transform t).J = Subscheme.weakTransform t ℜ.J :=
        ℜ.transform_J_eq_weakTransform_of_isPermissible hX hℜ t hperm
      have hE' : (ℜ.transform t).eUnion.pts =
          Subscheme.pts (Subscheme.totalTransform t.f (E.union B)).radical := by
        rw [ℜ.pts_eUnion_transform t, hE, pts_radical_totalTransform_union]
      obtain ⟨Y', s', hs'⟩ := ih t.isAlgebraicScheme hX' (ℜ.transform t) _ _ hℜ' hb hJ' hE' hs.2 hres
      exact ⟨Y', MonoidalSuccession.cons B t s', hperm.1, ⟨d, hd0, hdmax, hdz⟩,
        fun x hx => (Subscheme.hasOnlyNormalCrossingsWithAt_congr hE B x).mp (hperm.2.2 x hx),
        hs'⟩

/-- **The properties (1)–(4) of Main Theorem II(N)** (p. 177: "then we take the smallest integer `r`
such that `O_{X_r}` is the sheaf of ideals attached to the transform of `ℜ^N_II` by the succession
`{f_i, 0 ≦ i < r}`.  Then this succession of `r` monoidal transformations has the properties stated
in main theorem II(N)").  Let `ℜ` be a datum of type II with `b = 1`, ideal `J` and `E_1 ∪ ⋯ ∪ E_α`
having the points of `E`, on a non-singular algebraic scheme, and `s` a permissible succession
which resolves `ℜ`.  Then there is a succession (an initial segment of `s`: the first stage at
which `J_r = O`) with the properties (1)–(4) for `J` and `E`.

Deviation from the paper (gap filled): the paper says only that the succession "has the properties
stated"; the proofs are: (1) is the center condition of permissibility; (2): for `b = 1` the set
`S(ℜ)` contains every point with `ν(J_y) ≥ 1`, whatever the weights `a_i` are, so `ν(ℜ_i)` is the
maximum of the orders `ν(J_{iy})` over all the points `y` of `X_i`, it is positive if `J_i ≠ O` (and
finite and attained, `DatumII.Raw.nu_ne_top`, `DatumII.Raw.exists_mem_S_nuAt_eq_nu`), and the
points `z` of the center lie in `S_ν`, so `ν(J_{iz}) = d_i`; the sheaf `J_{i+1}` of the transform of
`ℜ_i` is the weak transform of `J_i` (`DatumII.Raw.transform_J_eq_weakTransform_of_isPermissible`,
for an empty center too); (3) is the normal crossings condition of permissibility, the union of
the components of the transform having the points `f_i⁻¹(E_i ∪ B_i)` (`DatumII.Raw.pts_eUnion_transform`);
(4): `ℜ_r` is a datum, so its union of the components has only normal crossings, and it is resolved,
which for `b = 1` means `J_r = O`. -/
@[blueprint "lem:I.3-main-II-properties"
  (statement := /-- Let $\mathfrak R=(E_1,\dots,E_\alpha\mid J,b)$ be a resolution datum of type
    $\mathfrak R^N_{\mathrm{II}}$ on a non-singular algebraic scheme $X$ with $b=1$ (and arbitrary
    $a_i\ge0$) such that $E_1\cup\dots\cup E_\alpha$ and $E$ have the same points, and let
    $\{f_i\}_{0\le i<r'}$ be a permissible succession for $\mathfrak R$ such that $f^*(\mathfrak
    R)$ is resolved everywhere. Then, for the smallest $r\le r'$ such that $J_r=\mathcal
    O_{X_r}$, the succession $\{f_i\}_{0\le i<r}$ has the properties (1)--(4) of main theorem
    II($N$) for $J$ and $E$. (p.~177.) -/)
  (proof := /-- (1) is part of the permissibility of $f_i$ for $\mathfrak R_i$. (2) Since $b=1$,
    $S(\mathfrak R_i)$ contains every point $y$ with $\nu(J_{iy})\ge1$, so, for $J_i\ne\mathcal
    O$, $\nu(\mathfrak R_i)$ is the maximum $d_i\ge1$ of the $\nu(J_{iy})$ over all points of
    $X_i$ (it is finite and attained, \cref{lem:I.nu-attained}); $B_i\subseteq S_{\nu}(\mathfrak
    R_i)$ gives $\nu(J_{iz})\ge d_i$ hence $=d_i$ for $z\in B_i$. The ideal of the transform is
    the weak transform of $J_i$ (\cref{lem:I.7-II-weak-transform}; also for an empty center, where
    $f_i$ is an isomorphism). (3) $E_1\cup\dots\cup E_\alpha$ has only normal crossings with $B_i$
    by permissibility; the union of the components of $\mathfrak R_{i+1}$ has the points of
    $f_i^{-1}(E_i\cup B_i)$, since the strict transform of $E_j$ contains $f_i^{-1}(E_j)$ off
    $f_i^{-1}(B_i)$ and $E_{\alpha+1}=f_i^{-1}(B_i)$. (4) $\mathfrak R_r$ is a resolution datum
    (Remark~1, \cref{rem:I.1-transform-is-datum-II}), so its union of components has only normal
    crossings, and it is resolved everywhere, which for $b=1$ means $J_r=\mathcal O_{X_r}$; $r$ is
    the first stage with $J_r=\mathcal O$, the succession being cut off there.

    \textbf{Deviation from the paper (gap filled).} The paper says only that the succession ``has
    the properties stated in main theorem II($N$)'' (p.~177). -/)
  (proofUses := ["lem:I.nu-attained", "lem:I.7-II-weak-transform", "rem:I.1-transform-is-datum-II",
    "def:I.6-II", "def:I.8"])
  (latexEnv := "lemma")]
theorem exists_isMainSuccession_of_isPermissibleII [Hironaka.HironakaCitedResults.{u}] [IsAlgebraicScheme X] (hX : X.IsNonsingular)
    (s : MonoidalSuccession X Y) (ℜ : DatumII.Raw X) (J E : Subscheme X) (hℜ : ℜ.IsDatum)
    (hb : ℜ.b = 1) (hJ : ℜ.J = J) (hE : ℜ.eUnion.pts = E.pts) (hs : s.IsPermissibleII ℜ)
    (hres : (s.transformII ℜ).ResolvedEverywhere) :
    ∃ (Y' : Scheme.{u}) (s' : MonoidalSuccession X Y'), s'.IsMainSuccession J E :=
  exists_isMainSuccession_of_isAlgebraicScheme s inferInstance hX ℜ J E hℜ hb hJ hE hs hres

end MonoidalSuccession

/-! ### The datum `ℜ^N_II = (E_1, …, E_α | J, 1; 0, …, 0)` and Main Theorem II(N) -/

section MainDatum

variable {X : Scheme.{u}}

/-- The resolution datum of p. 177: `ℜ^N_II = (E_1,…,E_α | J, b ; a_1,…,a_α)` with `b = 1`, the `E_i`
the irreducible components of `E` and all `a_i = 0`; it is a datum, and the union of the `E_i` is
`E` (the components of the reduced `E` with only normal crossings are non-singular irreducible
subschemes of codimension one, p. 274; `E` is reduced, so it is their union). -/
theorem DatumII.Raw.exists_mainDatum [IsAlgebraicScheme X] (hX : X.IsNonsingular)
    (J : Subscheme X) (hJ : ∀ x, J.stalkIdeal x ≠ ⊥) (E : Subscheme X) (hE : E.IsReduced)
    (hnc : E.HasOnlyNormalCrossings) :
    ∃ ℜ : DatumII.Raw X, ℜ.IsDatum ∧ ℜ.b = 1 ∧ ℜ.J = J ∧ ℜ.eUnion = E := by
  have := IsAlgebraicScheme.noetherianSpace X
  obtain ⟨α, C, hC, -, hcov⟩ := Subscheme.exists_family_irreducibleComponents E
  have hEeq : E = ⨅ i, C i := Subscheme.eq_iInf_of_isReduced hE C hC hcov
  refine ⟨⟨α, C, fun _ => 0, J, 1⟩, ⟨one_pos, fun i => ?_, ?_, hJ⟩, rfl, rfl, hEeq.symm⟩
  · exact Subscheme.isNonsingularIrreducibleCodimOne_of_mem_irreducibleComponents_of_hasOnlyNormalCrossings
      hX hnc (hC i)
  · show (⨅ i, C i).HasOnlyNormalCrossings
    rw [← hEeq]
    exact hnc

end MainDatum

/-- **Main Theorem II(N)** from the fundamental theorems `II₂^{N'}` (p. 177): the proof of the
paper. -/
theorem MainTheorem.II_of_fundamental [Hironaka.HironakaCitedResults.{u}] (hII : ∀ N, FundamentalTheorem.II₂.{u} N) (N : ℕ) :
    MainTheorem.II.{u} N := by
  intro X hXa hX hdim J hJ E hEred _ hEnc
  have := hXa
  obtain ⟨ℜ, hℜ, hb, hJℜ, hEℜ⟩ := DatumII.Raw.exists_mainDatum hX J hJ E hEred hEnc
  obtain ⟨Y, s, hs, hres⟩ :=
    exists_isPermissibleII_resolvedEverywhere_of_isNonsingular hII hX hdim.le ℜ hℜ
  exact MonoidalSuccession.exists_isMainSuccession_of_isPermissibleII hX s ℜ J E hℜ hb hJℜ
    (by rw [hEℜ]) hs hres

/-- **Main Theorem II(N)** (p. 176): for every `N ≧ 0`, deduced from the fundamental theorems
`II₂^{N'}` (`allFundamentalTheorems_printedRange`) as on pp. 176–177. -/
theorem mainTheorem_II [Hironaka.HironakaCitedResults.{u}] (N : ℕ) : MainTheorem.II.{u} N :=
  MainTheorem.II_of_fundamental (fun N => (allFundamentalTheorems_printedRange.{u}.2 N).2) N

end Hironaka
