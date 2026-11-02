/-
Copyright (c) 2026 Daattavya Aggarwal, Minhyong Kim, Oisin Kim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daattavya Aggarwal, Minhyong Kim, Oisin Kim
-/
module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Architect
public import Hironaka.Ch4.MainTheoremII
public import Hironaka.Compat.LocalizeSuccessionII
public import Hironaka.Compat.ResolutionBookkeeping
public import Hironaka.Compat.CompletionEmbedding
public import Hironaka.Statements

/-!
# Ch. 0 §5 (pp. 142–143): Main Theorem II and (B\*), from the fundamental theorem II₂

> **Main Theorem II.**  Let `X` be a non-singular algebraic `B`-scheme with a field `B` of characteristic zero.  Let
> `J` be a coherent sheaf of non-zero ideals on `X`.  Let `d` be the maximum of `ν(J_x)` for all the points `x` of
> `X`.  Let `E₀` be a reduced subscheme of everywhere codimension one of `X`, which has only normal crossings.  Then
> there exists a finite succession of monoidal transformations `{f_i : X_{i+1} → X_i}` with centers `D_i`, where
> `0 ≦ i < r` and `X = X₀`, which has the following properties:
> (i) `D_i` is non-singular and irreducible;
> (ii) if `J_i` denotes the sheaf of ideals on `X_i` such that `J_{i+1}` is the weak transform of `J_i` by the
> monoidal transformation `f_i`, for `0 ≦ i < r` and `J = J₀`, then `ν(J_{i,x(i)}) ≧ d` for all the points `x(i)`
> of `D_i` for `0 ≦ i < r`;
> (iii) if `E_i` denotes the subscheme of `X_i` such that `E_{i+1} = red(f_i⁻¹(E_i) ∪ f_i⁻¹(D_i))`, for
> `0 ≦ i < r`, where `red( )` denotes the associated reduced scheme, then `E_i` has only normal crossings with
> `D_i`; and
> (iv) `E_r` has only normal crossings, and we have `ν(J_{r,y}) < d` for every point `y` of `X_r`.  (p. 142–143)

> We remark that, in the above theorem, the first property of (iv) is an obvious consequence of (iii); in fact, all
> the `E_i` have only normal crossings by (iii).  Moreover, it follows from (ii) that, for every `i` with
> `0 ≦ i < r`, `d` is the maximum of `ν(J_{iz})` for all the points `z` of `X_i`, so that in particular we have
> `ν(J_{i,x(i)}) = d`.  More precisely, we have the following theorem, analogous to (B) of § 4:
> **(B\*)** Let `X` be a non-singular algebraic `B`-scheme, `J` a coherent sheaf of non-zero ideals on `X`, and `D` a
> non-singular subscheme of `X`, say irreducible.  Let `f : X' → X` be the monoidal transformation with center `D`,
> and `J'` the weak transform of `J` by this `f`.  If `ν(J_x)` is constant for `x ∈ D`, then we have
> `ν(J'_{x'}) ≦ ν(J_{f(x')})` for all `x' ∈ X'`.  (p. 143)

The paper prints no derivation of Main Theorem II ("We shall prove in this work the following …", p. 142); the proof
of Main Theorem II(N) (pp. 176–177) is the only argument on record, so that every step below is a gap filled.

Route (the proof of II(N) of p. 177 with a different stopping rule): `ℜ = (E_1,…,E_α | J, 1; 0,…,0)` is a resolution
datum (`DatumII.Raw.exists_mainDatum`); the fundamental theorem `II₂` gives a permissible succession which resolves
it; one follows it until the first stage at which the maximum of the orders `ν(J_{iy})` has dropped below `d` (it
has, at the latest, when `J_r = O`, where all orders are `0 < d`), and one cuts the succession there.  Along the way,
for `b = 1`, the maximum `d_i` of the orders is attained and equals `ν(J_{iz})` on the center
(`DatumII.Raw.exists_property_two`), hence `ν(J_{iz}) = d_i ≧ d` (ii); (B\*) shows that the maximum does not increase
(`MonoidalTransformation.nu_weakTransform_le`: stalkwise Lemma 8 of Ch. III, p. 217), which gives the remark: `d_i = d`
for `i < r`.  `E_i` has only normal crossings for all `i` as the union of the components of the transform of a datum.

Why not literally from `MainTheorem.II` (II(N)): its predicate `IsMainSuccession` carries only the normal crossings of
`E_i` *with `B_i`* for `i < r`, not the normal crossings of `E_i` (the first property of (iv), which the paper calls
"an obvious consequence of (iii)": it needs that the transform of a datum is a datum, Remark 1 of Ch. I).  The
datum-level induction below is that of `exists_isMainSuccession_of_isPermissibleII` with the stopping rule `ν < d`.

Corrections / gaps: (1) for `J = O_X` (so `d = 0`) condition (iv) would need
`ν(J_{r,y}) < 0`, so it can only be met with `X_r = ∅` (centers which are components of `X`): the printed statement is
then true, but only degenerately; the main theorems are first proved for `1 ≤ d`, and the case `d = 0` is
`exists_isMainIIZero_zero_aux`, so that `II_full_of_isAlgebraicScheme` is Main Theorem II exactly as printed.  (2) (ii) prints `≧ d`, the
remark `= d`: both are proved (the remark for the succession constructed; for an arbitrary succession with (i)–(iv)
it needs that no center is empty after the maximum has dropped below `d`).  The statements are for algebraic schemes
over a local ring of the class `𝔅` (p. 151); the printed form (`B` a field of characteristic zero, `X` of finite
type over `B`) is the corollary `MainTheorem.Ch0.II`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace IsLocalRing

namespace Hironaka

universe u

/-! ### The properties (i)–(iv) -/

namespace MonoidalSuccession


/-- The remark of p. 143 on the succession of Main Theorem II: "all the `E_i` have only normal crossings by (iii)" and
"it follows from (ii) that, for every `i` with `0 ≦ i < r`, `d` is the maximum of `ν(J_{iz})` for all the points `z`
of `X_i`, so that in particular we have `ν(J_{i,x(i)}) = d`", for `0 ≦ i < r`. -/
def IsMainIIZeroRemark (d : ℕ) : {X Y : Scheme.{u}} → MonoidalSuccession X Y → Subscheme X →
    Subscheme X → Prop
  | _, _, nil _, _, _ => True
  | _, _, cons B t rest, J, E =>
      E.HasOnlyNormalCrossings ∧
      IsGreatest (Set.range fun y => Ideal.nu (J.stalkIdeal y)) (d : ℕ∞) ∧
      (∀ z ∈ B.pts, Ideal.nu (J.stalkIdeal z) = d) ∧
      rest.IsMainIIZeroRemark d (Subscheme.weakTransform t J)
        (Subscheme.totalTransform t.f (E.union B)).radical

end MonoidalSuccession

/-! ### (B\*): the order of the weak transform -/

section BStar

variable {X : Scheme.{u}} {B : Subscheme X}

/-- Off the center, the weak transform is the total transform, and `f` is a local isomorphism. -/
theorem MonoidalTransformation.nu_weakTransform_eq_of_notMem [IsAlgebraicScheme X] (hX : X.IsNonsingular)
    (J : Subscheme X) (t : MonoidalTransformation X B) {y : t.X'} (hy : y ∉ t.exceptional.pts) :
    Ideal.nu ((Subscheme.weakTransform t J).stalkIdeal y) = Ideal.nu (J.stalkIdeal (t.f y)) := by
  have : IsRegularLocalRing (X.presheaf.stalk (t.f y)) := hX _
  have hfy : t.f y ∉ B.pts := by
    rwa [MonoidalTransformation.pts_exceptional] at hy
  have hw : (Subscheme.weakTransform t J).stalkIdeal y = (Subscheme.totalTransform t.f J).stalkIdeal y := by
    by_cases h : ∃ ξ : X, IsGenericPoint ξ B.pts
    · obtain ⟨ξ, hξ⟩ := h
      rw [Subscheme.stalkIdeal_weakTransform t J hξ y, Subscheme.stalkIdeal_eq_top_of_notMem_pts hy]
      simp only [Ideal.top_pow, Submodule.top_coe, Submodule.colon_univ]
      exact le_antisymm (iSup₂_le fun _ _ => le_rfl) (le_iSup₂_of_le 0 (by simp) le_rfl)
    · unfold Subscheme.weakTransform
      simp only [h, dite_false]
  rw [hw, stalkIdeal_totalTransform]
  exact LocSucc.nu_map_ringEquiv
    (RingEquiv.ofBijective _ (t.bijective_stalkMap_of_notMem y hfy)) _

/-- **(B\*)** (p. 143), for an algebraic scheme: let `J` be a sheaf of non-zero ideals on the non-singular algebraic
scheme `X`, `B` a non-singular irreducible subscheme (possibly empty) on which `ν(J_x)` is constant, `t` the monoidal
transformation with center `B` and `J'` the weak transform of `J` by `t`.  Then `ν(J'_{y}) ≤ ν(J_{f(y)})` for all
`y ∈ X'`.

The paper prints (B\*) without proof ("analogous to (B) of § 4").  Proof: off the exceptional subscheme `f` is a local
isomorphism and `J'` is the total transform; over a point of `B`, `O_{X',y}` is a monoidal transform of `O_{X,f(y)}`
with center `P = B_{f(y)}` (Remark 2 of Ch. III, `stalkIdeal_weakTransform_eq_map`), the weak transform `J'_y` is the
weak transform of the ideal `J_{f(y)}` in the sense of Ch. III Def. 5 (the exponent `ν(J_ξ)` at the generic point of `B`
is `ν_P(J_{f(y)})` by `le_nu_generic_iff`), `ν_P(J_x) = ν(J_x)` because `ν(J_x)` is constant on `B`, and Lemma 8 of Ch. III
(`LocSucc.nu_weakTransformIdeal_le`) gives `ν(J'_y) ≤ ν(J_{f(y)})`.

Deviation from the paper (gap filled): (B\*) is stated without proof; the scheme-level deduction from the stalkwise
Lemma 8 is the argument of p. 283 (Prop. IV.1-3, `DatumII.Raw.nuAt_transform_le`), carried out here for a center on
which `ν(J_x)` is constant instead of a permissible center of a datum. -/
@[blueprint "thm:0.3-B-star"
  (statement := /-- (\textbf{B}$^*$) Let $X$ be a non-singular algebraic scheme, $J$ a coherent sheaf of non-zero
    ideals on $X$, and $D$ a non-singular irreducible subscheme of $X$. Let $f\colon X'\to X$ be the monoidal
    transformation with center $D$, and $J'$ the weak transform of $J$ by $f$. If $\nu(J_x)$ is constant for
    $x\in D$, then $\nu(J'_{x'})\le\nu(J_{f(x')})$ for all $x'\in X'$. (p.~143.)
    Formalization note (encoding): ``non-zero ideals'' is $J_x\ne0$ for every $x$; the empty subscheme counts as a
    non-singular irreducible subscheme; the algebraic $\mathbf B$-scheme is an algebraic scheme in the sense of
    p.~151 (a scheme of finite type over a local ring of the class $\mathfrak B$). -/)
  (proof := /-- Off the exceptional subscheme $f$ is a local isomorphism and $J'=f^{-1}(J)$ there. At a point $y'$ over
    $y\in D$, $\mathcal O_{X',y'}$ is a monoidal transform of $\mathcal O_{X,y}$ with center $P=D_y$ and $J'_{y'}$ is the
    weak transform of $J_y$ (Remark~2, \cref{rem:III.2-2}); since $\nu(J_x)$ is constant on $D$, $\nu_P(J_y)=\nu(J_y)$, and
    Lemma~8 of Ch.~III (\cref{lem:III.8}) gives $\nu(J'_{y'})\le\nu(J_y)$.
    \textbf{Gap in the paper filled.} (B$^*$) is printed without proof. -/)
  (proofUses := ["lem:III.8", "rem:III.2-2", "def:III.2-weak-transform-sheaf"])
  (latexEnv := "theorem")]
theorem MonoidalTransformation.nu_weakTransform_le [Hironaka.HironakaCitedResults.{u}] [IsAlgebraicScheme X] (hX : X.IsNonsingular)
    (J : Subscheme X) (hJ : ∀ x, J.stalkIdeal x ≠ ⊥) (hB : B.IsCenter) (t : MonoidalTransformation X B)
    (hconst : ∀ x ∈ B.pts, ∀ x' ∈ B.pts, Ideal.nu (J.stalkIdeal x) = Ideal.nu (J.stalkIdeal x'))
    (y : t.X') :
    Ideal.nu ((Subscheme.weakTransform t J).stalkIdeal y) ≤ Ideal.nu (J.stalkIdeal (t.f y)) := by
  classical
  by_cases hy : y ∈ t.exceptional.pts
  swap
  · exact (MonoidalTransformation.nu_weakTransform_eq_of_notMem hX J t hy).le
  have hfy : t.f y ∈ B.pts := by rwa [MonoidalTransformation.pts_exceptional] at hy
  obtain ⟨hns, hirr⟩ : B.IsNonsingular ∧ B.IsIrreducible := by
    rcases hB with h | h
    · exfalso
      have : B.pts = ∅ := by rw [h]; exact Subscheme.pts_empty
      rw [this] at hfy
      exact hfy
    · exact h
  have := IsAlgebraicScheme.noetherianSpace X
  obtain ⟨ξ, hξ⟩ := QuasiSober.sober (Subscheme.isIrreducible_pts B hirr) B.support.isClosed
  have hξB : ξ ∈ B.pts := hξ.mem
  have : IsRegularLocalRing (X.presheaf.stalk (t.f y)) := hX _
  have : IsDomain (X.presheaf.stalk (t.f y)) := Transforms.isDomain_of_isRegularLocalRing _
  obtain ⟨s, e, he⟩ := t.exists_monoidalTransform_stalk y
  have hse := Subscheme.stalkIdeal_weakTransform_eq_map hX hns t J hξ y s e he
  have hP := Subscheme.isPrime_stalkIdeal_of_isNonsingular hns hfy
  have hSr := Subscheme.isRegularLocalRing_quotient_of_isNonsingular hns hfy
  have hPJ : Ideal.ord (B.stalkIdeal (t.f y)) (J.stalkIdeal (t.f y)) =
      Ideal.nu (J.stalkIdeal (t.f y)) := by
    refine le_antisymm (Ideal.ord_le fun n hn => Ideal.le_ord (hn.trans
      (Ideal.pow_right_mono (stalkIdeal_le_maximalIdeal_of_mem_pts B hfy) n))) ?_
    obtain ⟨-, -, -, h4, -⟩ :=
      MonoidalTransformation.exceptional_isNonsingular_and_totalTransform_le_pow hX hirr hns t J
    obtain ⟨k, hk, -⟩ := h4 ξ hξ (hJ ξ)
    rw [(hconst _ hfy ξ hξB).trans hk]
    exact Ideal.le_ord ((Subscheme.le_nu_generic_iff hX hns hξ hfy J k).mp hk.ge)
  rw [hse, LocSucc.nu_map_ringEquiv_of_equivLike]
  exact LocSucc.nu_weakTransformIdeal_le _ (hJ _) hP hSr hPJ s

end BStar

/-! ### The construction -/

section Core

variable {X Y : Scheme.{u}}

private theorem exists_isMainIIZero_aux [Hironaka.HironakaCitedResults.{u}] (d : ℕ) (hd1 : 1 ≤ d) (s : MonoidalSuccession X Y)
    (hXa : IsAlgebraicScheme X) (hX : X.IsNonsingular) :
    ∀ (ℜ : DatumII.Raw X) (J E : Subscheme X), ℜ.IsDatum → ℜ.b = 1 → ℜ.J = J →
      ℜ.eUnion.pts = E.pts → (∀ y, Ideal.nu (J.stalkIdeal y) ≤ d) → s.IsPermissibleII ℜ →
      (s.transformII ℜ).ResolvedEverywhere →
      ∃ (Y' : Scheme.{u}) (s' : MonoidalSuccession X Y'), s'.IsMainIIZero d J E ∧
        s'.IsMainIIZeroRemark d J E := by
  induction s with
  | nil _ =>
    intro ℜ J E hℜ hb hJ hE _ _ hres
    have hJtop : J = ⊤ := hJ ▸ ℜ.J_eq_top_of_resolvedEverywhere hb hres
    refine ⟨_, MonoidalSuccession.nil _, ⟨hasOnlyNormalCrossings_of_pts_eq hE hℜ.2.2.1, fun y => ?_⟩,
      trivial⟩
    have : ¬ 1 ≤ Ideal.nu (J.stalkIdeal y) := by
      rw [J.one_le_nu_stalkIdeal_iff y, hJtop, Subscheme.stalkIdeal_top_eq]
      exact fun h => h rfl
    have h0 : Ideal.nu (J.stalkIdeal y) = 0 := Order.lt_one_iff.mp (not_le.mp this)
    rw [h0]
    exact_mod_cast hd1
  | cons B t rest ih =>
    intro ℜ J E hℜ hb hJ hE hub hs hres
    have := hXa
    subst hJ
    by_cases hlt : ∀ y, Ideal.nu (ℜ.J.stalkIdeal y) < d
    · exact ⟨_, MonoidalSuccession.nil _, ⟨hasOnlyNormalCrossings_of_pts_eq hE hℜ.2.2.1, hlt⟩,
        trivial⟩
    · push Not at hlt
      obtain ⟨y₀, hy₀⟩ := hlt
      have hJtop : ℜ.J ≠ ⊤ := by
        intro h
        have h1 : 1 ≤ Ideal.nu (ℜ.J.stalkIdeal y₀) := (by exact_mod_cast hd1 : (1 : ℕ∞) ≤ d).trans hy₀
        rw [ℜ.J.one_le_nu_stalkIdeal_iff y₀, h, Subscheme.stalkIdeal_top_eq] at h1
        exact h1 rfl
      have hperm : ℜ.IsPermissible B := hs.1
      obtain ⟨d', hd'0, hdmax, hdz⟩ := ℜ.exists_property_two hX hℜ hb hJtop hperm
      have hd'd : d' = d := by
        have h1 : (d : ℕ∞) ≤ d' := hy₀.trans (hdmax.2 ⟨y₀, rfl⟩)
        obtain ⟨y₁, hy₁⟩ := hdmax.1
        have h2 : (d' : ℕ∞) ≤ d := hy₁ ▸ hub y₁
        exact_mod_cast le_antisymm h2 h1
      subst hd'd
      have hX' := (t.isNonsingular_and_isNonsingular_exceptional hX hperm.1.isNonsingular).1
      have hℜ' := (DatumII.Raw.transform_isDatum hX ℜ hℜ t hperm).1
      have hJ' : (ℜ.transform t).J = Subscheme.weakTransform t ℜ.J :=
        ℜ.transform_J_eq_weakTransform_of_isPermissible hX hℜ t hperm
      have hE' : (ℜ.transform t).eUnion.pts =
          Subscheme.pts (Subscheme.totalTransform t.f (E.union B)).radical := by
        rw [ℜ.pts_eUnion_transform t, hE, pts_radical_totalTransform_union]
      have hub' : ∀ y, Ideal.nu ((Subscheme.weakTransform t ℜ.J).stalkIdeal y) ≤ d' := fun y =>
        (MonoidalTransformation.nu_weakTransform_le hX ℜ.J hℜ.2.2.2 hperm.1 t
          (fun x hx x' hx' => (hdz x hx).trans (hdz x' hx').symm) y).trans (hdmax.2 ⟨_, rfl⟩)
      obtain ⟨Y', s', hs', hrem'⟩ := ih t.isAlgebraicScheme hX' (ℜ.transform t) _ _ hℜ' hb hJ' hE'
        (fun y => hJ' ▸ hub' y) hs.2 hres
      exact ⟨Y', MonoidalSuccession.cons B t s',
        ⟨hperm.1, fun z hz => (hdz z hz).ge,
          fun x hx => (Subscheme.hasOnlyNormalCrossingsWithAt_congr hE B x).mp (hperm.2.2 x hx),
          hs'⟩,
        ⟨hasOnlyNormalCrossings_of_pts_eq hE hℜ.2.2.1, hdmax, hdz, hrem'⟩⟩

end Core

/-! ### The case `d = 0` (`J = O_X`): the components of `X` as centers -/

section ZeroCase

variable {X : Scheme.{u}} {B : Subscheme X}

/-- If the ideal of the center `B` is zero at each of its points, no point of `X'` lies over `B`: the pull-back of the
zero ideal is zero, and a zero ideal which is invertible forces the local ring to vanish (the argument of Remark 1,
p. 169, for `X = B`, `isEmpty_of_pts_eq_univ`). -/
theorem MonoidalTransformation.notMem_pts_of_stalkIdeal_eq_bot (t : MonoidalTransformation X B)
    (h : ∀ y ∈ B.pts, B.stalkIdeal y = ⊥) (x' : t.X') : t.f x' ∉ B.pts := by
  intro hx
  obtain ⟨g, hg, hnzd⟩ := Subscheme.IsInvertibleIdeal.exists_stalkIdeal_eq_span t.invertible x'
  have h0 : (Subscheme.totalTransform t.f B).stalkIdeal x' = ⊥ := by
    rw [stalkIdeal_totalTransform, h _ hx, Ideal.map_bot]
  rw [h0] at hg
  have hg0 : g = 0 := by
    have : g ∈ (⊥ : Ideal (t.X'.presheaf.stalk x')) := by
      rw [hg]; exact Ideal.mem_span_singleton_self g
    exact (Ideal.mem_bot).mp this
  rw [hg0] at hnzd
  exact zero_notMem_nonZeroDivisors hnzd

/-- If no point of `X'` lies over the center `B`, then `f` is an open immersion onto the complement of `B`: both `f` and
the inclusion `U ⊆ X` of the complement have invertible (trivial) pull-back of the ideal of `B`, so they factor through
each other by the universal property of `f`. -/
theorem MonoidalTransformation.isOpenImmersion_of_forall_notMem (t : MonoidalTransformation X B)
    (h : ∀ x', t.f x' ∉ B.pts) : IsOpenImmersion t.f ∧ Set.range t.f.base = (B.pts)ᶜ := by
  let U : X.Opens := ⟨(B.pts)ᶜ, B.support.isClosed.isOpen_compl⟩
  have hU : Set.range t.f ⊆ Set.range U.ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨x', rfl⟩
    exact h x'
  let g : t.X' ⟶ U.toScheme := IsOpenImmersion.lift U.ι t.f hU
  have hg : g ≫ U.ι = t.f := IsOpenImmersion.lift_fac U.ι t.f hU
  -- the inclusion of `U` has trivial (hence invertible) pull-back of the ideal of `B`
  have htop : Subscheme.totalTransform U.ι B = ⊤ := by
    refine Subscheme.ext_stalkIdeal fun u => ?_
    rw [stalkIdeal_totalTransform, Subscheme.stalkIdeal_top_eq,
      Subscheme.stalkIdeal_eq_top_of_notMem_pts (show U.ι u ∉ B.pts from by
        have : U.ι u ∈ (U : Set X) := by
          rw [← Scheme.Opens.range_ι]; exact ⟨u, rfl⟩
        exact this), Ideal.map_top]
  obtain ⟨k, hk, -⟩ := t.universal U.toScheme U.ι (htop ▸ Subscheme.isInvertibleIdeal_top)
  have h1 : g ≫ k = 𝟙 _ := by
    refine ((t.universal t.X' t.f t.invertible).unique ?_ (Category.id_comp _))
    rw [Category.assoc, hk, hg]
  have h2 : k ≫ g = 𝟙 _ := by
    rw [← cancel_mono U.ι, Category.assoc, hg, hk, Category.id_comp]
  have : IsIso g := ⟨k, h1, h2⟩
  refine ⟨?_, ?_⟩
  · rw [← hg]
    infer_instance
  · refine Set.Subset.antisymm (fun _ ⟨x', hx'⟩ => hx' ▸ h x') fun u hu => ?_
    refine ⟨k.base ⟨u, hu⟩, ?_⟩
    have := congrArg (fun m => m.base ⟨u, hu⟩) hk
    exact this

/-- The weak transform of the unit ideal is the unit ideal. -/
theorem Subscheme.weakTransform_top (t : MonoidalTransformation X B) :
    Subscheme.weakTransform t (⊤ : Subscheme X) = ⊤ := by
  classical
  by_cases h : ∃ ξ : X, IsGenericPoint ξ B.pts
  · obtain ⟨ξ, hξ⟩ := h
    refine Subscheme.ext_stalkIdeal fun y => ?_
    rw [Subscheme.stalkIdeal_weakTransform t ⊤ hξ y]
    simp only [Subscheme.stalkIdeal_top_eq]
    have htot : (Subscheme.totalTransform t.f (⊤ : Subscheme X)).stalkIdeal y = ⊤ := by
      rw [Subscheme.totalTransform_top, Subscheme.stalkIdeal_top_eq]
    refine le_antisymm le_top ?_
    rw [top_le_iff, Ideal.eq_top_iff_one]
    refine Submodule.mem_iSup_of_mem 0 (Submodule.mem_iSup_of_mem zero_le ?_)
    rw [htot]
    exact Submodule.mem_colon.mpr fun _ _ => Submodule.mem_top
  · unfold Subscheme.weakTransform
    simp only [h, dite_false]
    exact Subscheme.totalTransform_top t.f

variable {n : ℕ} {F : Fin n → X.Opens}

/-- The pieces of a decomposition into disjoint irreducible opens are closed (the complement of a piece is the union of
the others). -/
theorem isClosed_piece (hF : IsIrreducibleDecomposition n F) (i : Fin n) : IsClosed (F i : Set X) := by
  have h : (F i : Set X)ᶜ = ⋃ j ∈ Finset.univ.erase i, (F j : Set X) := by
    ext x
    simp only [Set.mem_compl_iff, Set.mem_iUnion, Finset.mem_erase, Finset.mem_univ, and_true,
      exists_prop]
    constructor
    · intro hx
      obtain ⟨j, hj⟩ := hF.2.2 x
      exact ⟨j, fun hji => hx (hji ▸ hj), hj⟩
    · rintro ⟨j, hji, hj⟩ hx
      exact Set.disjoint_left.mp (hF.2.1 i j (Ne.symm hji)) hx hj
  rw [← isOpen_compl_iff, h]
  exact isOpen_biUnion fun j _ => (F j).isOpen

/-- The reduced subscheme on the piece `F i` (a connected component of `X`). -/
noncomputable def pieceSubscheme (hF : IsIrreducibleDecomposition n F) (i : Fin n) : Subscheme X :=
  Subscheme.ofClosed ⟨F i, isClosed_piece hF i⟩

/-- The points of the piece subscheme are those of the piece. -/
theorem pts_pieceSubscheme (hF : IsIrreducibleDecomposition n F) (i : Fin n) :
    (pieceSubscheme hF i).pts = F i := Subscheme.pts_ofClosed _

/-- The piece, being open and `X` non-singular (reduced), has the zero ideal at each of its points. -/
theorem stalkIdeal_pieceSubscheme (hX : X.IsNonsingular) (hF : IsIrreducibleDecomposition n F)
    (i : Fin n) {y : X} (hy : y ∈ F i) : (pieceSubscheme hF i).stalkIdeal y = ⊥ := by
  rw [pieceSubscheme, Subscheme.stalkIdeal_ofClosed_eq_of_local (⊥ : Subscheme X) _ (F i).isOpen
    (fun z _ => Subscheme.mem_pts_bot z) (fun z hz => hz.2) (fun z _ => by
      have : IsRegularLocalRing (X.presheaf.stalk z) := hX z
      have := Transforms.isDomain_of_isRegularLocalRing (X.presheaf.stalk z)
      rw [Subscheme.stalkIdeal_bot_eq]
      exact inferInstance) hy, Subscheme.stalkIdeal_bot_eq]

/-- A piece is a center: it is a non-singular irreducible subscheme. -/
theorem isCenter_pieceSubscheme (hX : X.IsNonsingular) (hF : IsIrreducibleDecomposition n F) (i : Fin n) :
    (pieceSubscheme hF i).IsCenter := by
  right
  refine ⟨Subscheme.isNonsingular_of_forall_isSimpleAt fun y hy => ?_,
    Subscheme.isIrreducible_of_pts _ ?_⟩
  · rw [pts_pieceSubscheme] at hy
    exact ⟨by rwa [pts_pieceSubscheme], by
      rw [stalkIdeal_pieceSubscheme hX hF i hy]
      have := (Subscheme.isSimpleAt_bot hX y).2
      rw [Subscheme.stalkIdeal_bot_eq] at this
      exact this⟩
  · rw [pts_pieceSubscheme]
    exact @IsIrreducible.of_subtype _ _ (F i : Set X) (hF.1 i)

/-- `E` has only normal crossings with a piece, as the ideal of the piece is zero. -/
theorem hasOnlyNormalCrossingsWith_pieceSubscheme (hX : X.IsNonsingular)
    (hF : IsIrreducibleDecomposition n F) (i : Fin n) {E : Subscheme X} (hE : E.HasOnlyNormalCrossings) :
    E.HasOnlyNormalCrossingsWith (pieceSubscheme hF i) := fun y hy => by
  rw [pts_pieceSubscheme] at hy
  obtain ⟨z, hz, hcomp, t, htz, hD⟩ := hE y
  rw [Subscheme.stalkIdeal_bot_eq] at hD
  exact ⟨z, hz, hcomp, t, htz, by rw [stalkIdeal_pieceSubscheme hX hF i hy]; exact hD⟩

end ZeroCase

/-- **Main Theorem II for `d = 0`** (`J = O_X`): the printed statement is true, but only degenerately.  Condition (iv)
needs `ν(J_{r,y}) < 0` for every point `y` of `X_r`, so `X_r = ∅`: Lean takes as centers the pieces of a decomposition
of `X` into irreducible open and closed subschemes (the connected components, which are non-singular and irreducible) one
after the other.  The monoidal transformation with such a center is the open immersion of the complement
(`MonoidalTransformation.isOpenImmersion_of_forall_notMem`), the complement has one piece less, and `X_r = ∅` after `n`
steps. -/
@[blueprint "lem:0.3-main-II-zero"
  (statement := /-- Let $X$ be a non-singular algebraic scheme with a decomposition into $n$ irreducible open and closed
    pieces, and $E$ a subscheme with only normal crossings. Then there is a succession of monoidal transformations of $X$
    with non-singular irreducible centers, having the properties (i)--(iv) of Main Theorem~II for $J=\mathcal O_X$ and $d=0$,
    whose end $X_r$ is empty. -/)
  (proof := /-- Induction on $n$. The center is the reduced subscheme on the first piece: non-singular and irreducible, with
    zero ideal at each of its points, so that $E$ has only normal crossings with it. No point of $X'$ lies over the center
    (the pull-back of the zero ideal is zero and must be invertible), hence $f$ is the open immersion of the complement
    (universal property of $f$ and of the inclusion), which has $n-1$ pieces; the weak transform of $\mathcal O_X$ is
    $\mathcal O_{X'}$ and $E'$ has only normal crossings. -/)
  (proofUses := ["def:monoidal-transformation", "def:III.2-weak-transform-sheaf"])
  (latexEnv := "lemma")]
theorem exists_isMainIIZero_zero_aux [Hironaka.HironakaCitedResults.{u}] :
    ∀ (n : ℕ) {X : Scheme.{u}} [IsAlgebraicScheme X], X.IsNonsingular → ∀ (F : Fin n → X.Opens),
      IsIrreducibleDecomposition n F → ∀ E : Subscheme X, E.HasOnlyNormalCrossings →
      ∃ (Y : Scheme.{u}) (s : MonoidalSuccession X Y), s.IsMainIIZero 0 ⊤ E ∧ IsEmpty Y := by
  intro n
  induction n with
  | zero =>
    intro X _ hX F hF E hE
    have : IsEmpty X := ⟨fun x => by obtain ⟨i, -⟩ := hF.2.2 x; exact i.elim0⟩
    exact ⟨X, MonoidalSuccession.nil X, ⟨hE, fun y => (IsEmpty.false y).elim⟩, this⟩
  | succ n ih =>
    intro X _ hX F hF E hE
    obtain ⟨t⟩ : Nonempty (MonoidalTransformation X (pieceSubscheme hF 0)) :=
      ⟨(MonoidalTransformation.exists_isProper X _).choose⟩
    have hnot : ∀ x', t.f x' ∉ (pieceSubscheme hF 0).pts :=
      t.notMem_pts_of_stalkIdeal_eq_bot fun y hy =>
        stalkIdeal_pieceSubscheme hX hF 0 (by rwa [pts_pieceSubscheme] at hy)
    obtain ⟨hopen, hrange⟩ := t.isOpenImmersion_of_forall_notMem hnot
    have hX'a : IsAlgebraicScheme t.X' := isAlgebraicScheme_of_isOpenImmersion t.f
    have hX' : t.X'.IsNonsingular := LocSucc.isNonsingular t.f hX
    -- the decomposition of `X'`
    have hdec : IsIrreducibleDecomposition n (fun i : Fin n => t.f ⁻¹ᵁ F i.succ) := by
      refine ⟨fun i => ?_, fun i j hij => ?_, fun y => ?_⟩
      · have hirr : _root_.IsIrreducible (F i.succ : Set X) :=
          @IsIrreducible.of_subtype _ _ (F i.succ : Set X) (hF.1 i.succ)
        have hsub : (F i.succ : Set X) ⊆ Set.range t.f.base := by
          rw [hrange, pts_pieceSubscheme]
          intro z hz hz0
          exact Set.disjoint_left.mp (hF.2.1 0 i.succ (Fin.succ_ne_zero i).symm) hz0 hz
        exact Subtype.irreducibleSpace (s := ((t.f ⁻¹ᵁ F i.succ : t.X'.Opens) : Set t.X'))
          (isIrreducible_preimage_of_isInducing t.f.isOpenEmbedding.isInducing hirr hsub)
      · refine Set.disjoint_left.mpr fun y hy1 hy2 => ?_
        exact Set.disjoint_left.mp (hF.2.1 i.succ j.succ
          (fun h => hij (Fin.succ_injective _ h))) hy1 hy2
      · obtain ⟨k, hk⟩ := hF.2.2 (t.f y)
        obtain ⟨i, rfl⟩ := Fin.exists_succ_eq.mpr (show k ≠ 0 from fun h0 => by
          subst h0
          exact hnot y (by rw [pts_pieceSubscheme]; exact hk))
        exact ⟨i, hk⟩
    -- the normal crossings of `E'`
    have hE' : Subscheme.HasOnlyNormalCrossings
        (Subscheme.totalTransform t.f (E.union (pieceSubscheme hF 0))).radical := by
      have hpts : (Subscheme.totalTransform t.f E).pts =
          Subscheme.pts (Subscheme.totalTransform t.f (E.union (pieceSubscheme hF 0))).radical := by
        rw [pts_radical_totalTransform_union, Subscheme.pts_totalTransform_eq_preimage]
        ext y
        simp only [Set.mem_preimage, Set.mem_union]
        exact ⟨Or.inl, fun h => h.resolve_right (hnot y)⟩
      refine hasOnlyNormalCrossings_of_pts_eq hpts ?_
      intro y
      have := (FlatPreimm.hasOnlyNormalCrossingsWithAt_totalTransform_iff t.f E ⊥ y).mpr (hE (t.f y))
      rwa [show Subscheme.totalTransform t.f (⊥ : Subscheme X) = ⊥ from
        Scheme.IdealSheafData.comap_bot t.f] at this
    obtain ⟨Y, s, hs, hY⟩ := ih hX' _ hdec _ hE'
    refine ⟨Y, MonoidalSuccession.cons _ t s, ⟨isCenter_pieceSubscheme hX hF 0,
      fun z _ => zero_le, hasOnlyNormalCrossingsWith_pieceSubscheme hX hF 0 hE, ?_⟩, hY⟩
    show s.IsMainIIZero 0 (Subscheme.weakTransform t ⊤) _
    rw [Subscheme.weakTransform_top]
    exact hs

/-! ### Main Theorem II and (B\*) -/

namespace MainTheorem.Ch0

/-- **Main Theorem II** (p. 142) for an algebraic scheme (the form of p. 151, `B` replaced by a local ring of the
class `𝔅`), together with the remark of p. 143 for the succession constructed.  The integer `d` is, as printed,
"the maximum of `ν(J_x)` for all the points `x` of `X`" (`hd`); `hd1 : 1 ≤ d` (that is, `J ≠ O_X`) is added: for
`J = O_X`, `d = 0` and (iv) can only be met by emptying `X`: that case is `II_full_of_isAlgebraicScheme` (see `thm:0.3-main-II-full`).  The hypothesis that
`E` is everywhere of codimension one is as printed (it is implied by reducedness and normal crossings of `E`, see
`DatumII.Raw.exists_mainDatum`).

Deviation from the paper (gap filled): the paper prints no derivation of Main Theorem II (p. 142: "We shall prove in this
work"); the proof is that of II(N) on p. 177 with the stopping rule "the maximum of `ν` has dropped below `d`" (see the
header of this file). -/
@[blueprint "rem:0.3-main-II"
  (statement := /-- Let $X$, $J$, $d$, $E_0$ be as in Main Theorem~II (\cref{thm:0.3-main-II}), with $d\ge1$. Then
    there is a succession as in Main Theorem~II such that, moreover, for every $0\le i<r$ the scheme $E_i$ has only
    normal crossings, $d$ is the maximum of $\nu(J_{iz})$ for the points $z$ of $X_i$, and $\nu(J_{iz})=d$ for the
    points $z$ of $D_i$ (the remark of p.~143). -/)
  (proof := /-- Let $\mathfrak R=(E_1,\dots,E_\alpha\mid J,1;0,\dots,0)$ be the resolution datum of p.~177
    (\cref{thm:I.3-main-II}); the fundamental theorem $\mathrm{II}_2$ gives a permissible succession resolving it.
    Follow it until the first stage at which $\nu(J_{iy})<d$ for all $y$ (at the latest when $J_i=\mathcal O$). Before
    that stage the maximum $d_i$ of the orders is attained, positive, and $\nu(J_{iz})=d_i$ on the center
    (\cref{lem:I.3-main-II-properties}), so $d_i\ge d$; the maximum does not increase (\cref{thm:0.3-B-star}), so
    $d_i=d$; the $E_i$ are the unions of the components of the transform of the datum, hence have only normal
    crossings. -/)
  (proofUses := ["thm:I.2-II2", "thm:I.3-main-II", "lem:I.3-main-II-properties", "thm:0.3-B-star"])
  (latexEnv := "theorem")]
theorem exists_isMainIIZero_of_isAlgebraicScheme [Hironaka.HironakaCitedResults.{u}] (X : Scheme.{u}) [IsAlgebraicScheme X]
    (hX : X.IsNonsingular) (J : Subscheme X) (hJ : ∀ x, J.stalkIdeal x ≠ ⊥) (d : ℕ)
    (hd : IsGreatest (Set.range fun x => Ideal.nu (J.stalkIdeal x)) (d : ℕ∞)) (hd1 : 1 ≤ d)
    (E : Subscheme X) (hE : E.IsReduced) (_hE1 : E.IsEverywhereCodimOne)
    (hEnc : E.HasOnlyNormalCrossings) :
    ∃ (Y : Scheme.{u}) (s : MonoidalSuccession X Y), s.IsMainIIZero d J E ∧
      s.IsMainIIZeroRemark d J E := by
  obtain ⟨N, hN⟩ := IsAlgebraicScheme.exists_dim_le X
  obtain ⟨ℜ, hℜ, hb, hJℜ, hEℜ⟩ := DatumII.Raw.exists_mainDatum hX J hJ E hE hEnc
  obtain ⟨Y, s, hs, hres⟩ := exists_isPermissibleII_resolvedEverywhere_of_isNonsingular
    (fun N => (allFundamentalTheorems_printedRange.{u}.2 N).2) hX hN ℜ hℜ
  exact exists_isMainIIZero_aux d hd1 s ‹_› hX ℜ J E hℜ hb hJℜ (by rw [hEℜ])
    (fun y => hd.2 ⟨y, rfl⟩) hs hres

/-- **Main Theorem II** (p. 142), for an algebraic scheme: the properties (i)–(iv) only. -/
@[blueprint "thm:0.3-main-II"
  (statement := /-- \textbf{Main Theorem II.} Let $X$ be a non-singular algebraic scheme. Let $J$ be a coherent sheaf of
    non-zero ideals on $X$. Let $d$ be the maximum of $\nu(J_x)$ for all the points $x$ of $X$. Let $E_0$ be a reduced
    subscheme of everywhere codimension one of $X$, which has only normal crossings. Then there exists a finite
    succession of monoidal transformations $\{f_i\colon X_{i+1}\to X_i\}$ with centers $D_i$, where $0\le i<r$ and
    $X=X_0$, which has the following properties:
    (i) $D_i$ is non-singular and irreducible;
    (ii) if $J_i$ denotes the sheaf of ideals on $X_i$ such that $J_{i+1}$ is the weak transform of $J_i$ by the
    monoidal transformation $f_i$, for $0\le i<r$ and $J=J_0$, then $\nu(J_{i,x(i)})\ge d$ for all the points $x(i)$ of
    $D_i$ for $0\le i<r$;
    (iii) if $E_i$ denotes the subscheme of $X_i$ such that $E_{i+1}=\operatorname{red}(f_i^{-1}(E_i)\cup
    f_i^{-1}(D_i))$, for $0\le i<r$, then $E_i$ has only normal crossings with $D_i$; and
    (iv) $E_r$ has only normal crossings, and we have $\nu(J_{r,y})<d$ for every point $y$ of $X_r$. (pp.~142--143.)
    \textbf{Deviation from the paper (statement modified).} The hypothesis $d\ge1$ ($J\ne\mathcal O_X$) is added in
    this node: for $J=\mathcal O_X$, $d=0$ and (iv) forces $X_r=\emptyset$; the statement without it is
    \cref{thm:0.3-main-II-full}. The statement is for algebraic schemes (p.~151); the
    printed form ($\mathbf B$ a field of characteristic zero) is a corollary.
    Formalization note (encoding): the data $J_i$, $E_i$ are carried along the succession
    (\cref{def:I.8}); ``a non-singular irreducible subscheme'' may be empty. -/)
  (proof := /-- The paper prints no derivation. Take the resolution datum of p.~177, resolve it by the fundamental
    theorem $\mathrm{II}_2$ and cut the succession at the first stage with $\nu(J_{iy})<d$ for all $y$
    (\cref{rem:0.3-main-II}).
    \textbf{Gap in the paper filled.} The paper states this consequence of the fundamental theorem $\mathrm{II}_2$ without a derivation; the argument above supplies it. -/)
  (proofUses := ["rem:0.3-main-II"])
  (latexEnv := "theorem")]
theorem II_of_isAlgebraicScheme [Hironaka.HironakaCitedResults.{u}] (X : Scheme.{u}) [IsAlgebraicScheme X] (hX : X.IsNonsingular)
    (J : Subscheme X) (hJ : ∀ x, J.stalkIdeal x ≠ ⊥) (d : ℕ)
    (hd : IsGreatest (Set.range fun x => Ideal.nu (J.stalkIdeal x)) (d : ℕ∞)) (hd1 : 1 ≤ d)
    (E : Subscheme X) (hE : E.IsReduced) (hE1 : E.IsEverywhereCodimOne)
    (hEnc : E.HasOnlyNormalCrossings) :
    ∃ (Y : Scheme.{u}) (s : MonoidalSuccession X Y), s.IsMainIIZero d J E := by
  obtain ⟨Y, s, hs, -⟩ := exists_isMainIIZero_of_isAlgebraicScheme X hX J hJ d hd hd1 E hE hE1 hEnc
  exact ⟨Y, s, hs⟩

/-- **Main Theorem II**, printed form (p. 142): `X` a non-singular algebraic `B`-scheme, `B` a field of characteristic
zero, i.e. a scheme with a morphism `p` of finite type to `Spec B` (not necessarily separated: the statement is more
general than the printed one). -/
theorem II [Hironaka.HironakaCitedResults.{u}] {B : Type u} [Field B] [CharZero B] {X : Scheme.{u}} (p : X ⟶ Spec (CommRingCat.of B))
    [LocallyOfFiniteType p] [QuasiCompact p] (hX : X.IsNonsingular) (J : Subscheme X)
    (hJ : ∀ x, J.stalkIdeal x ≠ ⊥) (d : ℕ)
    (hd : IsGreatest (Set.range fun x => Ideal.nu (J.stalkIdeal x)) (d : ℕ∞)) (hd1 : 1 ≤ d)
    (E : Subscheme X) (hE : E.IsReduced) (hE1 : E.IsEverywhereCodimOne)
    (hEnc : E.HasOnlyNormalCrossings) :
    ∃ (Y : Scheme.{u}) (s : MonoidalSuccession X Y), s.IsMainIIZero d J E :=
  haveI := IsAlgebraicScheme.of_field p
  II_of_isAlgebraicScheme X hX J hJ d hd hd1 E hE hE1 hEnc

/-- **(B\*)**, printed form (p. 143): `X` a non-singular algebraic `B`-scheme (not necessarily separated: the statement
is more general than the printed one), `B` a field of characteristic zero. -/
theorem B_star [Hironaka.HironakaCitedResults.{u}] {B : Type u} [Field B] [CharZero B] {X : Scheme.{u}} (p : X ⟶ Spec (CommRingCat.of B))
    [LocallyOfFiniteType p] [QuasiCompact p] (hX : X.IsNonsingular) (J : Subscheme X)
    (hJ : ∀ x, J.stalkIdeal x ≠ ⊥) {D : Subscheme X} (hD : D.IsCenter) (t : MonoidalTransformation X D)
    (hconst : ∀ x ∈ D.pts, ∀ x' ∈ D.pts, Ideal.nu (J.stalkIdeal x) = Ideal.nu (J.stalkIdeal x'))
    (y : t.X') :
    Ideal.nu ((Subscheme.weakTransform t J).stalkIdeal y) ≤ Ideal.nu (J.stalkIdeal (t.f y)) :=
  haveI := IsAlgebraicScheme.of_field p
  MonoidalTransformation.nu_weakTransform_le hX J hJ hD t hconst y

/-- **Main Theorem II** (p. 142) for an algebraic scheme, exactly as printed: no hypothesis on `d`.  For `d ≧ 1` it is
`II_of_isAlgebraicScheme`; for `d = 0` (`J = O_X`) it holds degenerately, by `exists_isMainIIZero_zero_aux`: the centers
are the connected components of `X` and `X_r = ∅`. -/
@[blueprint "thm:0.3-main-II-full"
  (statement := /-- \textbf{Main Theorem II} exactly as printed (\cref{thm:0.3-main-II}), with no hypothesis on $d$: for
    $J=\mathcal O_X$ (that is, $d=0$) the conclusion holds with the connected components of $X$ as centers, $X_r=\emptyset$.
    (pp.~142--143.) -/)
  (proof := /-- If $d\ge1$ this is \cref{thm:0.3-main-II}. If $d=0$ then $J_x=\mathcal O_{X,x}$ for every $x$, and
    (iv) needs $X_r=\emptyset$; blow up the connected components of $X$ (non-singular, irreducible, open and closed) one
    after the other: the monoidal transformation with such a center is the open immersion of the complement.
    \textbf{Gap in the paper filled.} The case is not mentioned. -/)
  (proofUses := ["thm:0.3-main-II"])
  (latexEnv := "theorem")]
theorem II_full_of_isAlgebraicScheme [Hironaka.HironakaCitedResults.{u}] (X : Scheme.{u}) [IsAlgebraicScheme X] (hX : X.IsNonsingular)
    (J : Subscheme X) (hJ : ∀ x, J.stalkIdeal x ≠ ⊥) (d : ℕ)
    (hd : IsGreatest (Set.range fun x => Ideal.nu (J.stalkIdeal x)) (d : ℕ∞))
    (E : Subscheme X) (hE : E.IsReduced) (hE1 : E.IsEverywhereCodimOne)
    (hEnc : E.HasOnlyNormalCrossings) :
    ∃ (Y : Scheme.{u}) (s : MonoidalSuccession X Y), s.IsMainIIZero d J E := by
  rcases Nat.eq_zero_or_pos d with rfl | hd1
  · have hJtop : J = ⊤ := by
      refine Subscheme.ext_stalkIdeal fun y => ?_
      rw [Subscheme.stalkIdeal_top_eq]
      by_contra hne
      have h1 : 1 ≤ Ideal.nu (J.stalkIdeal y) := (J.one_le_nu_stalkIdeal_iff y).mpr hne
      have h2 : Ideal.nu (J.stalkIdeal y) ≤ ((0 : ℕ) : ℕ∞) := hd.2 ⟨y, rfl⟩
      exact absurd (h1.trans h2) (by simp)
    subst hJtop
    obtain ⟨n, F, hF⟩ := exists_irreducibleDecomposition hX
    obtain ⟨Y, s, hs, -⟩ := exists_isMainIIZero_zero_aux n hX F hF E hEnc
    exact ⟨Y, s, hs⟩
  · exact II_of_isAlgebraicScheme X hX J hJ d hd hd1 E hE hE1 hEnc

/-- **Main Theorem II**, printed form with no hypothesis on `d`: `X` a non-singular algebraic `B`-scheme (not
necessarily separated: the statement is more general than the printed one), `B` a field of characteristic zero. -/
theorem II_full [Hironaka.HironakaCitedResults.{u}] {B : Type u} [Field B] [CharZero B] {X : Scheme.{u}} (p : X ⟶ Spec (CommRingCat.of B))
    [LocallyOfFiniteType p] [QuasiCompact p] (hX : X.IsNonsingular) (J : Subscheme X)
    (hJ : ∀ x, J.stalkIdeal x ≠ ⊥) (d : ℕ)
    (hd : IsGreatest (Set.range fun x => Ideal.nu (J.stalkIdeal x)) (d : ℕ∞))
    (E : Subscheme X) (hE : E.IsReduced) (hE1 : E.IsEverywhereCodimOne)
    (hEnc : E.HasOnlyNormalCrossings) :
    ∃ (Y : Scheme.{u}) (s : MonoidalSuccession X Y), s.IsMainIIZero d J E :=
  haveI := IsAlgebraicScheme.of_field p
  II_full_of_isAlgebraicScheme X hX J hJ d hd E hE hE1 hEnc

end MainTheorem.Ch0

end Hironaka
