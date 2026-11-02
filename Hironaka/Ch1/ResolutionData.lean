/-
Copyright (c) 2026 Daattavya Aggarwal, Minhyong Kim, Oisin Kim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daattavya Aggarwal, Minhyong Kim, Oisin Kim
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.Coalgebra.IsFrobenius
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.HopfAlgebra.Basic
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Architect
public import Hironaka.Ch0.Blowup
public import Hironaka.Ch0.NormalFlatness
public import Hironaka.Ch0.NormalCrossings
public import Hironaka.Ch0.BlowupLocal
public import Hironaka.Compat.ComponentStalk
public import Hironaka.Compat.TransformRSOP
public import Hironaka.Compat.TransformRingOfFractions
public import Hironaka.Compat.BlowupDim
public import Hironaka.Compat.BlowupExceptional
public import Hironaka.Compat.StrictTransformDim
public import Hironaka.Ch3.SemiContinuity
public import Hironaka.Statements

/-!
# Ch. I §1 (pp. 163–170): resolution data and permissible transformations

Definitions 3–8 of the paper.  Design:
* A datum is a *raw tuple* (`DatumI.Raw`, `DatumII.Raw`) plus the predicate `IsDatum` recording
  the conditions of Definition 3.  Transforms (Def. 7) are defined on raw tuples; the fact
  that the transform of a datum is again a datum is Hironaka's Remark 1 (p. 169), a theorem.
* Sums over the `E_i` containing a point use classical decidability.
* Orders `ν(J_x)` live in `ℕ∞` (`Ideal.nu`); `ν(ℜ)` is a supremum, which is `0` on the empty
  set, matching Hironaka's convention.

Throughout, `X` is a non-singular irreducible algebraic scheme (Def. 3, p. 164: "We always
assume that dim(X) ≧ 0", i.e. `X` is non-empty); these hypotheses are imposed in the theorems,
not in the data.
-/

@[expose] public section

open Classical AlgebraicGeometry

namespace Hironaka

universe u

/-! ### Definition 3 (I): resolution data of type ℜ^{N,n}_I -/

namespace DatumI


variable {X : Scheme.{u}}






/-- The set of points of `W` at which the datum is *not* resolved (the set `S(ℜ)` of
Ch. IV §3 for data with open restriction). -/
def Raw.unresolvedSet (ℜ : Raw X) : Set X := {x ∈ ℜ.W.pts | ¬ ℜ.ResolvedAt x}


end DatumI


/-! ### Definition 3 (II): resolution data of type ℜ^N_{II} -/

namespace DatumII


variable {X : Scheme.{u}}











end DatumII


/-! ### Definition 5: restrictions -/

namespace DatumI.Raw

variable {X : Scheme.{u}}



end DatumI.Raw

namespace DatumII.Raw

variable {X : Scheme.{u}}


end DatumII.Raw

/-! ### Definition 6: permissible monoidal transformations -/


namespace DatumI.Raw

variable {X : Scheme.{u}}




end DatumI.Raw

namespace DatumII.Raw

variable {X : Scheme.{u}}



end DatumII.Raw

/-! ### Elementary properties of strict transforms and of `f⁻¹(J)·P⁻ᵛ` (used in Remark 1) -/

namespace Subscheme

variable {X : Scheme.{u}} {B : Subscheme X}

/-- Strict transforms are monotone: a larger sheaf of ideals (smaller subscheme) has a larger
strict transform. -/
theorem strictTransform_mono (t : MonoidalTransformation X B) {V W : Subscheme X} (h : V ≤ W) :
    strictTransform t V ≤ strictTransform t W := by
  rw [le_iff_stalkIdeal_le]
  intro x
  rw [strictTransform_stalkIdeal, strictTransform_stalkIdeal]
  exact iSup_mono fun n => Submodule.colon_mono
    (stalkIdeal_mono (Scheme.IdealSheafData.comap_mono t.f h) x) le_rfl

/-- `W ⊆ V` implies `W' ⊆ V'` for strict transforms (containment of subschemes is reverse
inclusion of ideal sheaves, p. 165). -/
theorem IsContainedIn.strictTransform (t : MonoidalTransformation X B) {V W : Subscheme X}
    (h : W.IsContainedIn V) :
    (Subscheme.strictTransform t W).IsContainedIn (Subscheme.strictTransform t V) :=
  fun U => strictTransform_mono t (Scheme.IdealSheafData.le_def.mpr h) U

/-- A bijective ring homomorphism commutes with intersections of ideals. -/
theorem _root_.Hironaka.DatumTransform.map_inf_of_bijective {R S : Type*} [CommRing R] [CommRing S]
    {f : R →+* S} (hf : Function.Bijective f) (I J : Ideal R) :
    (I ⊓ J).map f = I.map f ⊓ J.map f := by
  have h : ∀ K : Ideal R, K.map f = K.comap (RingEquiv.ofBijective f hf).symm := fun K =>
    Ideal.map_comap_of_equiv (RingEquiv.ofBijective f hf)
  rw [h, h, h, Ideal.comap_inf]

/-- The strict transform of the empty subscheme (the unit ideal sheaf) is the unit ideal sheaf. -/
theorem strictTransform_top_eq (t : MonoidalTransformation X B) :
    strictTransform t ⊤ = ⊤ :=
  top_le_iff.mp (le_sSup fun x' _ => by rw [totalTransform_top])

/-- Strict transforms commute with unions of subschemes (p. 165, "`E ∪ F`" is defined by the
intersection of the ideal sheaves): `(V ∪ W)' = V' ∪ W'`.  This is the passage from the strict
transforms `F_j'` of the irreducible components `F_j` of `E` to the strict transform `E'` of
`E = ⋃ F_j` in the proof of Remark 1 (p. 169), which the paper does not spell out.

Proof: `⊆` is monotonicity.  For `⊇`, `V' ∩ W'` has, at the points off `f⁻¹(B)` (where `f` is a local
isomorphism), the stalks `V_{f(y)} ∩ W_{f(y)}` transported by the stalk isomorphism, i.e. those of
`f⁻¹(V ∩ W)`; so it lies in the supremum defining `(V ∩ W)'`. -/
theorem strictTransform_inf (hX : X.IsNonsingular) (t : MonoidalTransformation X B)
    (V W : Subscheme X) :
    strictTransform t (V ⊓ W) = strictTransform t V ⊓ strictTransform t W := by
  refine le_antisymm (le_inf (strictTransform_mono t inf_le_left)
    (strictTransform_mono t inf_le_right)) ?_
  refine le_sSup fun y hy => ?_
  have hfy : t.f y ∉ B.pts := fun h => hy (by rw [MonoidalTransformation.pts_exceptional]; exact h)
  have : IsRegularLocalRing (X.presheaf.stalk (t.f y)) := hX _
  rw [stalkIdeal_inf_eq, MonoidalTransformation.strictTransform_stalkIdeal_of_notMem t V hy,
    MonoidalTransformation.strictTransform_stalkIdeal_of_notMem t W hy,
    stalkIdeal_totalTransform, stalkIdeal_totalTransform, stalkIdeal_totalTransform,
    stalkIdeal_inf_eq]
  exact (Hironaka.DatumTransform.map_inf_of_bijective (t.bijective_stalkMap_of_notMem y hfy) _ _).symm

/-- Strict transforms commute with finite unions of subschemes. -/
theorem strictTransform_iInf_fintype (hX : X.IsNonsingular) (t : MonoidalTransformation X B)
    {ι : Type*} [Fintype ι] (V : ι → Subscheme X) :
    strictTransform t (⨅ i, V i) = ⨅ i, strictTransform t (V i) := by
  have key : ∀ s : Finset ι, strictTransform t (⨅ i ∈ s, V i) = ⨅ i ∈ s, strictTransform t (V i) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simpa using strictTransform_top_eq t
    | insert a s ha ih =>
      rw [Finset.iInf_insert, Finset.iInf_insert, strictTransform_inf hX, ih]
  simpa using key Finset.univ

/-- If `X` is non-singular and `J` has non-zero stalks, then so has every `f⁻¹(J)·P_E⁻ᵛ`: the
canonical map `O_{X,f(y)} → O_{X',y}` is injective (it is `R → R'` for a monoidal transform
`R'` of `R`). -/
theorem stalkIdeal_divPow_totalTransform_ne_bot (hX : X.IsNonsingular)
    (t : MonoidalTransformation X B) {J : Subscheme X} (hJ : ∀ x, J.stalkIdeal x ≠ ⊥) (ν : ℕ)
    (y : t.X') : (divPow (totalTransform t.f J) t.exceptional ν).stalkIdeal y ≠ ⊥ := by
  have : IsRegularLocalRing (X.presheaf.stalk (t.f y)) := hX _
  have := Transforms.isDomain_of_isRegularLocalRing (X.presheaf.stalk (t.f y))
  obtain ⟨s, e, he⟩ := t.exists_monoidalTransform_stalk y
  have hinj : Function.Injective (t.f.stalkMap y) := by
    have : ⇑(t.f.stalkMap y) = ⇑(e.toRingHom.comp s.toRing) := by rw [he]
    rw [this]
    exact e.injective.comp s.toRing_injective
  rw [stalkIdeal_divPow (P := t.exceptional) t.invertible]
  intro h
  apply hJ (t.f y)
  rw [eq_bot_iff]
  intro a ha
  have h1 : t.f.stalkMap y a ∈ (totalTransform t.f J).stalkIdeal y := by
    rw [stalkIdeal_totalTransform]
    exact Ideal.mem_map_of_mem _ ha
  have h2 := Ideal.le_colon (S := ((t.exceptional.stalkIdeal y ^ ν : Ideal _) :
    Set (t.X'.presheaf.stalk y))) h1
  rw [h, Submodule.mem_bot] at h2
  rw [Submodule.mem_bot]
  exact hinj (h2.trans (map_zero _).symm)

/-- The quotient `I·P⁻ᵛ` of p. 168 ("`f⁻¹(J)P^{-ν}`") is exact when `I` is divisible by `Pᵛ`
(p. 142: "f⁻¹(J) is divisible by the m-th power of the sheaf of ideals of f⁻¹(D) on X'.  The sheaf
of ideals on X' obtained by this division …"; p. 176: "The quotient obtained by this division"):
if `I ⊆ Pᵛ` then `divPow I P ν` (the colon ideal sheaf used by Lean) satisfies
`(I·P⁻ᵛ)·Pᵛ = I`.  Only that `P` is locally principal is used. -/
theorem divPow_mul_pow_eq {I P : Subscheme X} (hP : P.IsInvertibleIdeal) {ν : ℕ}
    (h : I ≤ P ^ ν) : divPow I P ν * P ^ ν = I := by
  refine Subscheme.ext_stalkIdeal fun x => ?_
  rw [stalkIdeal_mul_eq, stalkIdeal_divPow hP, stalkIdeal_pow_eq]
  have hle : I.stalkIdeal x ≤ P.stalkIdeal x ^ ν := by
    have := le_iff_stalkIdeal_le.mp h x
    rwa [stalkIdeal_pow_eq] at this
  obtain ⟨g, hg, -⟩ := hP.exists_stalkIdeal_eq_span x
  apply le_antisymm
  · rw [Ideal.mul_le]
    intro r hr s hs
    rw [Submodule.mem_colon] at hr
    simpa using hr s hs
  · intro a ha
    have ha' : a ∈ P.stalkIdeal x ^ ν := hle ha
    rw [hg, Ideal.span_singleton_pow, Ideal.mem_span_singleton'] at ha'
    obtain ⟨c, rfl⟩ := ha'
    refine Ideal.mul_mem_mul ?_ ?_
    · rw [Submodule.mem_colon]
      intro s hs
      rw [hg, Ideal.span_singleton_pow, SetLike.mem_coe, Ideal.mem_span_singleton'] at hs
      obtain ⟨d, rfl⟩ := hs
      have := (I.stalkIdeal x).mul_mem_left d ha
      simpa [smul_eq_mul, mul_comm, mul_left_comm] using this
    · rw [hg, Ideal.span_singleton_pow]
      exact Ideal.mem_span_singleton_self _

/-- Powers of an invertible sheaf of ideals `P` can be cancelled: `K·Pᵛ = K'·Pᵛ` implies
`K = K'` (on stalks `Pᵛ` is generated by a non-zero-divisor).  This is why "the quotient obtained
by this division" (p. 176) is well defined. -/
theorem eq_of_mul_pow_eq_mul_pow {K K' P : Subscheme X} (hP : P.IsInvertibleIdeal) {ν : ℕ}
    (h : K * P ^ ν = K' * P ^ ν) : K = K' := by
  have key : ∀ (K K' : Subscheme X), K * P ^ ν = K' * P ^ ν → K ≤ K' := by
    intro K K' h
    refine le_iff_stalkIdeal_le.mpr fun x a ha => ?_
    have h1 := congrArg (fun L => L.stalkIdeal x) h
    simp only [stalkIdeal_mul_eq, stalkIdeal_pow_eq] at h1
    obtain ⟨g, hg, hnzd⟩ := hP.exists_stalkIdeal_eq_span x
    rw [hg, Ideal.span_singleton_pow] at h1
    have h2 : a * g ^ ν ∈ K.stalkIdeal x * Ideal.span {g ^ ν} :=
      Ideal.mul_mem_mul ha (Ideal.mem_span_singleton_self _)
    rw [h1, Ideal.mem_mul_span_singleton] at h2
    obtain ⟨z, hz, hza⟩ := h2
    have hgν : g ^ ν ∈ nonZeroDivisors (X.presheaf.stalk x) := pow_mem hnzd ν
    have hsub : (z - a) * g ^ ν = 0 := by rw [sub_mul, hza, sub_self]
    have : z = a := sub_eq_zero.mp ((mem_nonZeroDivisors_iff_right.mp hgν) _ hsub)
    rw [← this]
    exact hz
  exact le_antisymm (key K K' h) (key K' K h.symm)

end Subscheme

/-- A monoidal transform of an algebraic scheme is algebraic (its morphism is proper,
`lem:monoidal-transformation-proper`, hence of finite type). -/
theorem MonoidalTransformation.isAlgebraicScheme [Hironaka.Cited.MonoidalTransformationExistsIsProper.{u}] {X : Scheme.{u}}
    [IsAlgebraicScheme X] {B : Subscheme X} (t : MonoidalTransformation X B) :
    IsAlgebraicScheme t.X' := by
  obtain ⟨S, i1, i2, i3, p, hp1, hp2⟩ := IsAlgebraicScheme.exists_base (X := X)
  have := IsAlgebraicScheme.isNoetherian X
  have := t.isProper
  exact ⟨⟨S, i1, i2, i3, CategoryTheory.CategoryStruct.comp t.f p, inferInstance,
    inferInstance⟩⟩

/-- The empty subscheme is non-singular (it has no points). -/
theorem Subscheme.isNonsingular_empty {X : Scheme.{u}} :
    (Subscheme.empty : Subscheme X).IsNonsingular := by
  intro x
  exfalso
  have hx : ((Subscheme.empty : Subscheme X).subschemeι.base x) ∈
      Set.range (Subscheme.empty : Subscheme X).subschemeι.base := ⟨x, rfl⟩
  rw [(Subscheme.empty : Subscheme X).range_subschemeι] at hx
  simp [Subscheme.empty] at hx

/-- A center is non-singular (`Subscheme.IsCenter`: empty, or non-singular and irreducible). -/
theorem Subscheme.IsCenter.isNonsingular {X : Scheme.{u}} {B : Subscheme X}
    (hB : B.IsCenter) : B.IsNonsingular := by
  rcases hB with rfl | h
  · exact Subscheme.isNonsingular_empty
  · exact h.1

/-! ### Remark 1 (p. 169): the local computation

The chart computation of p. 169 on the stalks of `X'`, and its consequences for reducedness,
codimension, normal crossings, non-singularity and density.  Each statement is read on stalks:
at `y ∈ X'` over `x = f(y)`, the stalks of `E' ∪ E_{β+1}`, of the `E_i'`, of `E_{α+1}` and of `F'`
are generated by products of subsets of a part `K` of a regular system of parameters of
`O_{X',y}` (`DatumTransform.exists_stalk_transform`). -/

namespace Remark1

open IsLocalRing

/-- In a noetherian domain, a non-zero prime contained in a prime of height one equals it. -/
theorem _root_.Hironaka.DatumTransform.eq_of_le_of_height_eq_one {R : Type u} [CommRing R] [IsDomain R] [IsNoetherianRing R]
    {p q : Ideal R} [q.IsPrime] [p.IsPrime] (hqp : q ≤ p) (hq0 : q ≠ ⊥)
    (hp1 : p.height = 1) : q = p := by
  by_contra hne
  have hlt : q < p := lt_of_le_of_ne hqp hne
  have : p.FiniteHeight := ⟨Or.inr (by rw [hp1]; exact ENat.one_ne_top)⟩
  have h1 := Ideal.height_strict_mono_of_isPrime hlt
  rw [hp1, Order.lt_one_iff, Ideal.height_eq_zero_iff_eq_bot] at h1
  exact hq0 h1

theorem _root_.Hironaka.DatumTransform.prod_image_eq {R S : Type*} [CommMonoid S] [DecidableEq S] (φ : R → S) {A : Set R}
    (hφ : Set.InjOn φ A) (s : Finset R) (hs : (s : Set R) ⊆ A) :
    ∏ z ∈ s, φ z = ∏ w ∈ s.image φ, w := by
  rw [Finset.prod_image]
  intro a ha b hb hab
  exact hφ (hs ha) (hs hb) hab

theorem _root_.Hironaka.DatumTransform.map_span_prod {R S : Type*} [CommRing R] [CommRing S] (e : R ≃+* S) (K : Finset R) :
    (Ideal.span {∏ k ∈ K, k}).map e = Ideal.span {∏ w ∈ K.image e, w} := by
  rw [Ideal.map_span, Set.image_singleton, map_prod, Finset.prod_image]
  intro a _ b _ hab
  exact e.injective hab

theorem _root_.Hironaka.DatumTransform.isRadical_map_ringEquiv {R S : Type*} [CommRing R] [CommRing S] (e : R ≃+* S)
    {I : Ideal R} (hI : I.IsRadical) : (I.map e).IsRadical := by
  rw [← Ideal.map_coe e, Ideal.map_comap_of_equiv]
  exact hI.comap _

variable {X : Scheme.{u}} {B : Subscheme X}

theorem _root_.Hironaka.DatumTransform.mem_maximalIdeal_ringEquiv {R S : Type*} [CommRing R] [CommRing S] [IsLocalRing R]
    [IsLocalRing S] (e : R ≃+* S) (a : R) :
    e a ∈ maximalIdeal S ↔ a ∈ maximalIdeal R := by
  simp only [mem_maximalIdeal, mem_nonunits_iff, isUnit_map_iff]

/-- The chart computation of p. 169, as printed.  Let `x' = y` be a point of `X'`, `x = f(y) ∈ B`,
`(z₁, …, z_s) = Z` a regular system of parameters of `O_x`, and `T = {z_{r+1}, …, z_s} ⊆ Z` with
`B_x = (T)` (p. 169: "that `B` is defined by `z_{r+1} = ⋯ = z_s = 0` at `x`").  Then:

* "the local ring `O_{x'}` of `X'` at `x'` is a ring of fractions of `A = O_x[z_{r+1}z_t^{-1}, …,
  z_s z_t^{-1}]` for some `t` (`r + 1 ≤ t ≤ s`) with respect to a prime ideal `M` in `A`": there are
  `z_t ∈ T` and a monoidal transform `s = (x, M')` of `O_x` with `s.x = z_t` (so that
  `s.ring = A_M` with `A = blowupAlgebra O_x B_x z_t = O_x[z_v/z_t : z_v ∈ T]`, `M = s.M'`
  containing the maximal ideal of `O_x`) and an isomorphism `e : A_M ≃ O_{x'}` over `O_x`;
* "Let `z'_v = z_v` for `1 ≤ v ≤ r`, `z'_t = z_t` and `z'_v = z_v z_t^{-1}` for `r + 1 ≤ v (≠ t) ≤ s`":
  the elements `φ z = z'_v` of `O_{x'}`, with `z'_v = e(z_v z_t^{-1})`, `z_v z_t^{-1} ∈ A`;
* "`E'_{α+1}` is defined by `z'_t = 0` at `x'`, provided `x' ∈ E'_{α+1}`" (here `f(x') ∈ B`);
* "a system of those `z'_v` which are in `M` can be extended to a regular system of parameters of
  `O_{x'} = A_M`" (the `z'_v` with `z'_v ∈ M` are distinct);
* the strict transform of the subscheme `V` defined at `x` by `∏_{z ∈ J} z` (`J ⊆ Z`) is defined at `x'` by
  the product of those `z'_v`, `z_v ∈ J`, `z_v ≠ z_t`, which lie in `M`; for `J = {z_j}` this is "the
  strict transform `F_j'` of `F_j` contains the point `x'` if and only if `j ≠ t` and `z'_j ∈ M`, in
  which case `F_j'` is defined by `z'_j = 0` at `x'`" (`DatumTransform.strictTransform_component_stalk`).

Deviation from the paper (gap filled): all of this is printed with "it is easily seen" (p. 169); the
proof goes through `MonoidalTransform.exists_rsop_transform` (Ch. III §2 description
`R'/xR' ≅ ((R/P)[X₁, …, X_r])_q`, pp. 209–210) and `MonoidalTransform.exists_equiv_of_span_eq` (the sentence of
p. 209, `MonoidalTransform.exists_index_subring_eq_localization`, in the form for data). -/
@[blueprint "compat:blowup-stalk-chart-printed"
  (statement := /-- Let $f\colon X'\to X$ be the monoidal transformation with a center $B$, $y\in X'$,
    $x=f(y)\in B$, with $\mathcal O_{X,x}$ regular, and $(z_1,\dots,z_s)$ a regular system of parameters of
    $\mathcal O_{X,x}$ such that $B$ is defined at $x$ by $z_{r+1}=\dots=z_s=0$. Then there are $t$
    ($r+1\le t\le s$), a prime ideal $M$ of $A=\mathcal O_{X,x}[z_{r+1}z_t^{-1},\dots,z_sz_t^{-1}]$ containing
    the maximal ideal of $\mathcal O_{X,x}$, and an isomorphism of $\mathcal O_{X,x}$-algebras
    $A_M\cong\mathcal O_{X',y}$; with $z'_v=z_v$ ($v\le r$), $z'_t=z_t$ and $z'_v=z_vz_t^{-1}$ ($v\ne t$),
    the ideal of $f^{-1}(B)$ at $y$ is $(z'_t)$, and the $z'_v$ lying in the maximal ideal extend to a regular
    system of parameters. (Remark~1, p.~169.)
    \textbf{Gap in the paper filled.} Printed without proof. -/)
  (proof := /-- $\mathcal O_{X',y}$ is a monoidal transform of $\mathcal O_{X,x}$ with center $B_x$
    (\cref{compat:blowup-stalk-monoidal-transform}); by \cref{lem:III.2-monoidal-transform-index}
    (p.~209) $PR'=z_tR'$ for some $z_t$ among the $z_v$, and then $R'=A_M$ with $A=R[z_t^{-1}P]$; the
    rest is the regular-system-of-parameters statement of Ch.~III \S2 (pp.~209--210). -/)
  (latexEnv := "proposition")]
theorem _root_.Hironaka.DatumTransform.exists_chart_ringOfFractions
    (t : MonoidalTransformation X B) (y : t.X')
    [IsRegularLocalRing (t.X'.presheaf.stalk y)]
    [IsRegularLocalRing (X.presheaf.stalk (t.f y))] [IsDomain (X.presheaf.stalk (t.f y))]
    {Z T : Finset (X.presheaf.stalk (t.f y))}
    (hZ : IsRegularSystemOfParameters (X.presheaf.stalk (t.f y)) Z) (hTZ : T ⊆ Z)
    (hBT : B.stalkIdeal (t.f y) = Ideal.span (T : Set (X.presheaf.stalk (t.f y)))) :
    ∃ (zt : X.presheaf.stalk (t.f y))
      (s : MonoidalTransform (X.presheaf.stalk (t.f y)) (B.stalkIdeal (t.f y)))
      (e : s.ring ≃+* t.X'.presheaf.stalk y)
      (φ : X.presheaf.stalk (t.f y) → t.X'.presheaf.stalk y),
      zt ∈ T ∧ s.x = zt ∧ e.toRingHom.comp s.toRing = (t.f.stalkMap y).hom ∧
      blowupAlgebra (X.presheaf.stalk (t.f y)) (B.stalkIdeal (t.f y)) s.x =
        Algebra.adjoin (X.presheaf.stalk (t.f y))
          ((fun z => algebraMap (X.presheaf.stalk (t.f y)) (FractionRing (X.presheaf.stalk (t.f y))) z /
            algebraMap (X.presheaf.stalk (t.f y)) (FractionRing (X.presheaf.stalk (t.f y))) s.x) ''
            (T : Set (X.presheaf.stalk (t.f y)))) ∧
      (∀ z ∈ Z, z ∉ T → φ z = (t.f.stalkMap y).hom z) ∧ φ zt = (t.f.stalkMap y).hom zt ∧
      (∀ z ∈ T, z ≠ zt → ∃ hz : algebraMap (X.presheaf.stalk (t.f y))
            (FractionRing (X.presheaf.stalk (t.f y))) z /
            algebraMap (X.presheaf.stalk (t.f y)) (FractionRing (X.presheaf.stalk (t.f y))) s.x ∈
          blowupAlgebra (X.presheaf.stalk (t.f y)) (B.stalkIdeal (t.f y)) s.x,
        φ z = e (algebraMap (blowupAlgebra (X.presheaf.stalk (t.f y)) (B.stalkIdeal (t.f y)) s.x)
          s.ring ⟨_, hz⟩)) ∧
      t.exceptional.stalkIdeal y = Ideal.span {φ zt} ∧
      φ zt ∈ maximalIdeal (t.X'.presheaf.stalk y) ∧
      Set.InjOn φ {z | z ∈ Z ∧ φ z ∈ maximalIdeal (t.X'.presheaf.stalk y)} ∧
      ExtendsToRSOP (t.X'.presheaf.stalk y)
        ((Z.filter fun z => φ z ∈ maximalIdeal (t.X'.presheaf.stalk y)).image φ) ∧
      ∀ J ⊆ Z, ∀ V : Subscheme X, V.stalkIdeal (t.f y) = Ideal.span {(∏ z ∈ J, z)} →
        (Subscheme.strictTransform t V).stalkIdeal y =
          Ideal.span {(∏ z ∈ (J.erase zt).filter
            (fun z => φ z ∈ maximalIdeal (t.X'.presheaf.stalk y)), φ z)} := by
  have : IsRegularLocalRing (t.X'.presheaf.stalk y) := inferInstance
  obtain ⟨s, e, he⟩ := t.exists_monoidalTransform_stalk y
  have : IsRegularLocalRing s.ring := IsRegularLocalRing.of_ringEquiv e.symm
  obtain ⟨zt, φ, hzt, hspan, hφ₁, hφ₂, hφ₃, hinj, hext⟩ :=
    MonoidalTransform.exists_rsop_transform s hZ hTZ hBT.symm
  -- p. 169: `O_{x'}` is a ring of fractions of `A = O_x[z_{r+1}z_t^{-1}, …, z_s z_t^{-1}]`
  have hztP : zt ∈ B.stalkIdeal (t.f y) := hBT ▸ Ideal.subset_span (Finset.mem_coe.mpr hzt)
  obtain ⟨s', e₁, hsx, he₁⟩ := s.exists_equiv_of_span_eq hztP hspan
  have hm := Hironaka.DatumTransform.mem_maximalIdeal_ringEquiv e
  have htot := t.stalkIdeal_totalTransform_eq_map y s e he
  have hexc : t.exceptional.stalkIdeal y = (Ideal.span {s.toRing zt}).map e := by
    rw [MonoidalTransformation.exceptional, htot, ← hspan]
  have hfilt : ∀ K : Finset (X.presheaf.stalk (t.f y)),
      (K.filter fun z => e (φ z) ∈ maximalIdeal (t.X'.presheaf.stalk y)) =
        K.filter fun z => φ z ∈ maximalIdeal s.ring :=
    fun K => Finset.filter_congr fun z _ => hm (φ z)
  have hxR0 : s'.xR ≠ 0 := fun h =>
    s'.x_ne_zero (MonoidalTransform.toRing_injective s' (h.trans (map_zero _).symm))
  refine ⟨zt, s', e₁.symm.trans e, fun z => e (φ z), hzt, hsx, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · ext r
    show e (e₁.symm (s'.toRing r)) = _
    have h1 : s'.toRing r = e₁ (s.toRing r) := (RingHom.congr_fun he₁ r).symm
    rw [h1, RingEquiv.symm_apply_apply]
    exact RingHom.congr_fun he r
  · have := MonoidalTransform.blowupAlgebra_span_eq_adjoin (R := X.presheaf.stalk (t.f y)) T s'.x
    rw [← hBT] at this
    exact this
  · intro z hz hzT
    show e (φ z) = _
    rw [hφ₁ z hz hzT]
    exact RingHom.congr_fun he z
  · show e (φ zt) = _
    rw [hφ₂]
    exact RingHom.congr_fun he zt
  · intro z hzT hne
    have hzP : z ∈ B.stalkIdeal (t.f y) := hBT ▸ Ideal.subset_span (Finset.mem_coe.mpr hzT)
    have hz : algebraMap (X.presheaf.stalk (t.f y)) (FractionRing (X.presheaf.stalk (t.f y))) z /
        algebraMap (X.presheaf.stalk (t.f y)) (FractionRing (X.presheaf.stalk (t.f y))) s'.x ∈
        blowupAlgebra (X.presheaf.stalk (t.f y)) (B.stalkIdeal (t.f y)) s'.x :=
      Algebra.subset_adjoin ⟨z, hzP, rfl⟩
    refine ⟨hz, ?_⟩
    have key : e₁ (φ z) = algebraMap (blowupAlgebra (X.presheaf.stalk (t.f y))
        (B.stalkIdeal (t.f y)) s'.x) s'.ring ⟨_, hz⟩ := by
      apply mul_left_cancel₀ hxR0
      rw [s'.xR_mul_algebraMap_div hz]
      have h1 : s'.xR = e₁ (s.toRing zt) := by
        have := RingHom.congr_fun he₁ zt
        show s'.toRing s'.x = _
        rw [hsx]
        exact this.symm
      rw [h1, ← map_mul, hφ₃ z hzT hne]
      exact RingHom.congr_fun he₁ z
    show e (φ z) = (e₁.symm.trans e) _
    rw [RingEquiv.trans_apply, ← key, RingEquiv.symm_apply_apply]
  · show t.exceptional.stalkIdeal y = Ideal.span {e (φ zt)}
    rw [hexc, Ideal.map_span, Set.image_singleton, hφ₂]
  · show e (φ zt) ∈ _
    rw [hm, hφ₂]
    have hztm : zt ∈ maximalIdeal (X.presheaf.stalk (t.f y)) :=
      hZ.1 ▸ Ideal.subset_span (hTZ hzt)
    exact map_nonunit s.toRing zt hztm
  · intro a ha b hb hab
    exact hinj ⟨ha.1, (hm _).mp ha.2⟩ ⟨hb.1, (hm _).mp hb.2⟩ (e.injective hab)
  · have := ExtendsToRSOP.map_ringEquiv e hext
    rw [Finset.image_image] at this
    rw [hfilt]
    exact this
  · intro J hJZ V hV
    rw [Subscheme.strictTransform_stalkIdeal, hexc, htot, hV]
    have hsat := MonoidalTransform.saturation_span_prod s hZ hTZ hBT.symm hJZ hzt hspan hφ₁ hφ₂
      hφ₃ hinj hext
    rw [hfilt, ← map_prod e]
    have h2 : Ideal.span {e (∏ z ∈ (J.erase zt).filter fun z => φ z ∈ maximalIdeal s.ring, φ z)} =
        (Ideal.span {∏ z ∈ (J.erase zt).filter fun z => φ z ∈ maximalIdeal s.ring, φ z}).map e := by
      rw [Ideal.map_span, Set.image_singleton]
    rw [h2, ← hsat, Ideal.map_iSup]
    refine iSup_congr fun n => ?_
    rw [Ideal.map_colon_ringEquiv, Ideal.map_pow, Ideal.map_span s.toRing, Set.image_singleton]

/-- The chart computation of p. 169 on the stalks of `X'`: `O_{X',y}` is a monoidal transform of
`O_{X,f(y)}`, and the elements `z'_v` of p. 169 (`exists_chart_ringOfFractions`) give the stalks at
`y` of `E = f⁻¹(B)` and of the strict transforms of the subschemes `(∏ J)`, `J ⊆ Z`. -/
theorem _root_.Hironaka.DatumTransform.exists_chart (hX : X.IsNonsingular) (t : MonoidalTransformation X B) (y : t.X')
    [IsRegularLocalRing (t.X'.presheaf.stalk y)]
    {Z T : Finset (X.presheaf.stalk (t.f y))}
    (hZ : IsRegularSystemOfParameters (X.presheaf.stalk (t.f y)) Z) (hTZ : T ⊆ Z)
    (hBT : B.stalkIdeal (t.f y) = Ideal.span (T : Set (X.presheaf.stalk (t.f y)))) :
    ∃ (zt : X.presheaf.stalk (t.f y)) (φ : X.presheaf.stalk (t.f y) → t.X'.presheaf.stalk y),
      zt ∈ T ∧ t.exceptional.stalkIdeal y = Ideal.span {φ zt} ∧
      φ zt ∈ maximalIdeal (t.X'.presheaf.stalk y) ∧
      Set.InjOn φ {z | z ∈ Z ∧ φ z ∈ maximalIdeal (t.X'.presheaf.stalk y)} ∧
      ExtendsToRSOP (t.X'.presheaf.stalk y)
        ((Z.filter fun z => φ z ∈ maximalIdeal (t.X'.presheaf.stalk y)).image φ) ∧
      ∀ J ⊆ Z, ∀ V : Subscheme X, V.stalkIdeal (t.f y) = Ideal.span {(∏ z ∈ J, z)} →
        (Subscheme.strictTransform t V).stalkIdeal y =
          Ideal.span {(∏ z ∈ (J.erase zt).filter
            (fun z => φ z ∈ maximalIdeal (t.X'.presheaf.stalk y)), φ z)} := by
  have : IsRegularLocalRing (X.presheaf.stalk (t.f y)) := hX _
  have := isDomain_of_isRegularLocalRing (X.presheaf.stalk (t.f y))
  obtain ⟨zt, -, -, φ, hzt, -, -, -, -, -, -, hexc, hmem, hinj, hext, hst⟩ :=
    Hironaka.DatumTransform.exists_chart_ringOfFractions t y hZ hTZ hBT
  exact ⟨zt, φ, hzt, hexc, hmem, hinj, hext, hst⟩

/-- p. 169: "It is then easily seen that, `(F_i, z_j)` being as above, the strict transform `F_i'` of `F_i`
contains the point `x'` if and only if `j ≠ t` and `z'_j ∈ M`, in which case `F_i'` is defined by `z'_j = 0`
at `x'`."  Here `F` is a subscheme with `F_x = (z_j)` (an irreducible component of `E` through `x`, whose
ideal at `x` is generated by the member `a = z_j` of the regular system of parameters `Z`), and `zt`, `φ`
are the `z_t` and `z'_v` of the chart (`exists_chart_ringOfFractions`; `hst` is its last clause). -/
theorem _root_.Hironaka.DatumTransform.strictTransform_component_stalk
    (t : MonoidalTransformation X B) (y : t.X') {Z : Finset (X.presheaf.stalk (t.f y))}
    {zt : X.presheaf.stalk (t.f y)} {φ : X.presheaf.stalk (t.f y) → t.X'.presheaf.stalk y}
    (hst : ∀ J ⊆ Z, ∀ V : Subscheme X, V.stalkIdeal (t.f y) = Ideal.span {(∏ z ∈ J, z)} →
      (Subscheme.strictTransform t V).stalkIdeal y =
        Ideal.span {(∏ z ∈ (J.erase zt).filter
          (fun z => φ z ∈ maximalIdeal (t.X'.presheaf.stalk y)), φ z)})
    {a : X.presheaf.stalk (t.f y)} (ha : a ∈ Z) {F : Subscheme X}
    (hF : F.stalkIdeal (t.f y) = Ideal.span {a}) :
    (y ∈ (Subscheme.strictTransform t F).pts ↔
      a ≠ zt ∧ φ a ∈ maximalIdeal (t.X'.presheaf.stalk y)) ∧
    ((a ≠ zt ∧ φ a ∈ maximalIdeal (t.X'.presheaf.stalk y)) →
      (Subscheme.strictTransform t F).stalkIdeal y = Ideal.span {φ a}) := by
  have h := hst {a} (Finset.singleton_subset_iff.mpr ha) F (by rw [hF, Finset.prod_singleton])
  by_cases hc : a ≠ zt ∧ φ a ∈ maximalIdeal (t.X'.presheaf.stalk y)
  · have h1 : (({a} : Finset _).erase zt).filter
        (fun z => φ z ∈ maximalIdeal (t.X'.presheaf.stalk y)) = {a} := by
      ext b
      simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_singleton]
      constructor
      · rintro ⟨⟨-, hb⟩, -⟩; exact hb
      · rintro rfl; exact ⟨⟨hc.1, rfl⟩, hc.2⟩
    rw [h1, Finset.prod_singleton] at h
    refine ⟨⟨fun _ => hc, fun _ => ?_⟩, fun _ => h⟩
    rw [Subscheme.mem_pts_iff_stalkIdeal_ne_top, h, Ne, Ideal.span_singleton_eq_top]
    exact (IsLocalRing.mem_maximalIdeal _).mp hc.2
  · have h1 : (({a} : Finset _).erase zt).filter
        (fun z => φ z ∈ maximalIdeal (t.X'.presheaf.stalk y)) = ∅ := by
      ext b
      simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_singleton, Finset.notMem_empty,
        iff_false, not_and]
      rintro ⟨hb, rfl⟩ hm
      exact hc ⟨hb, hm⟩
    rw [h1, Finset.prod_empty, Ideal.span_singleton_one] at h
    refine ⟨⟨fun hy => ?_, fun h' => absurd h' hc⟩, fun h' => absurd h' hc⟩
    exact absurd (Subscheme.mem_pts_iff_stalkIdeal_ne_top.mp hy) (not_not.mpr h)

/-- Off the center, `f` is a local isomorphism (p. 169: "if `x ∉ B` there is nothing to
prove"). -/
theorem _root_.Hironaka.DatumTransform.exists_offCenter (hX : X.IsNonsingular) (t : MonoidalTransformation X B) (y : t.X')
    (hy : t.f y ∉ B.pts) :
    ∃ e : X.presheaf.stalk (t.f y) ≃+* t.X'.presheaf.stalk y,
      t.exceptional.stalkIdeal y = ⊤ ∧
      ∀ V : Subscheme X,
        (Subscheme.strictTransform t V).stalkIdeal y = (V.stalkIdeal (t.f y)).map e := by
  have : IsRegularLocalRing (X.presheaf.stalk (t.f y)) := hX _
  have hyE : y ∉ t.exceptional.pts := by
    rw [MonoidalTransformation.pts_exceptional]; exact hy
  refine ⟨RingEquiv.ofBijective (t.f.stalkMap y).hom (t.bijective_stalkMap_of_notMem y hy),
    Subscheme.stalkIdeal_eq_top_of_notMem_pts hyE, fun V => ?_⟩
  rw [MonoidalTransformation.strictTransform_stalkIdeal_of_notMem t V hyE,
    stalkIdeal_totalTransform]
  rfl

theorem _root_.Hironaka.DatumTransform.pts_empty : (Subscheme.empty : Subscheme X).pts = ∅ := by
  simp [Subscheme.pts, Subscheme.empty, Scheme.IdealSheafData.support_top]

/-- Normal crossings of `E₁ ∪ ⋯ ∪ E_α` (with `D`) at `x`, the `Eᵢ` non-singular irreducible of
codimension one: there is a regular system of parameters `Z` adapted to `D` such that the ideal
of every `Eᵢ` at `x` is `(1)` or generated by a member of `Z`. -/
theorem _root_.Hironaka.DatumTransform.exists_rsop_of_hasOnlyNormalCrossingsWithAt {ι : Type*} (E : ι → Subscheme X)
    (hE : ∀ i, (E i).IsNonsingularIrreducibleCodimOne) {D₀ : Subscheme X} (hD₀ : ∀ i, D₀ ≤ E i)
    {D : Subscheme X} {x : X} [IsRegularLocalRing (X.presheaf.stalk x)]
    (h : D₀.HasOnlyNormalCrossingsWithAt D x) :
    ∃ Z : Finset (X.presheaf.stalk x), IsRegularSystemOfParameters _ Z ∧
      (∃ T ⊆ Z, D.stalkIdeal x = Ideal.span (T : Set (X.presheaf.stalk x))) ∧
      ∀ i, (E i).stalkIdeal x = ⊤ ∨ ∃ a ∈ Z, (E i).stalkIdeal x = Ideal.span {a} := by
  have := isDomain_of_isRegularLocalRing (X.presheaf.stalk x)
  obtain ⟨Z, hZ, hcomp, T, hTZ, hT⟩ := h
  refine ⟨Z, hZ, ⟨T, hTZ, hT⟩, fun i => ?_⟩
  by_cases hx : x ∈ (E i).pts
  swap
  · exact Or.inl (Subscheme.stalkIdeal_eq_top_of_notMem_pts hx)
  right
  have hne : E i ≠ Subscheme.empty := by
    rintro h
    rw [h, Hironaka.DatumTransform.pts_empty] at hx
    exact hx
  obtain ⟨hns, hirr, hcod⟩ := (hE i).resolve_left hne
  have hp : ((E i).stalkIdeal x).IsPrime := Subscheme.isPrime_stalkIdeal_of_isNonsingular_of_mem_pts _ hns hx
  have hp1 : ((E i).stalkIdeal x).height = 1 := by
    rw [← Subscheme.codim_eq_height _ hns hirr hx, hcod]
  have hle : D₀.stalkIdeal x ≤ (E i).stalkIdeal x :=
    Subscheme.stalkIdeal_mono (hD₀ i) x
  obtain ⟨q, hq, hqp⟩ := Ideal.exists_minimalPrimes_le hle
  obtain ⟨C, hC, hxC, hCq⟩ :=
    Subscheme.exists_mem_irreducibleComponents_of_mem_minimalPrimes _ x hq
  obtain ⟨a, ha, hCa⟩ := hcomp C hC hxC
  refine ⟨a, ha, ?_⟩
  have hqa : q = Ideal.span {a} := hCq.symm.trans hCa
  have hext : ExtendsToRSOP _ Z := ExtendsToRSOP.of_isRegularSystemOfParameters hZ
  have := hext.isPrime_span_singleton ha
  have ha0 : Ideal.span {a} ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]; exact hext.ne_zero ha
  exact (Hironaka.DatumTransform.eq_of_le_of_height_eq_one (hqa ▸ hqp) ha0 hp1).symm

/-- Finite intersections of subschemes, on stalks. -/
theorem _root_.Hironaka.DatumTransform.stalkIdeal_iInf_fintype {ι : Type*} [Fintype ι] (E : ι → Subscheme X) (x : X) :
    (⨅ i, E i).stalkIdeal x = ⨅ i, (E i).stalkIdeal x := by
  have key : ∀ s : Finset ι, (⨅ i ∈ s, E i).stalkIdeal x = ⨅ i ∈ s, (E i).stalkIdeal x := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp [Subscheme.stalkIdeal_top_eq]
    | insert a s ha ih =>
      rw [Finset.iInf_insert, Finset.iInf_insert, Subscheme.stalkIdeal_inf_eq, ih]
  simpa using key Finset.univ

/-- The irreducible components of `E` through `x`: if `E_x = (∏ J)`, `J ⊆ Z` a part of a regular system of
parameters of `O_x`, then for every `a ∈ J` there is an irreducible component `C` of `E` through `x`
defined at `x` by `a` (the minimal primes of `E_x` are the `(a)`, `a ∈ J`; p. 169: "every irreducible
component `F_i` of `E` containing `x` is defined by `z_j = 0` at `x` for some `j`"). -/
theorem _root_.Hironaka.DatumTransform.exists_component_of_mem {E : Subscheme X} {x : X}
    [IsRegularLocalRing (X.presheaf.stalk x)] {Z J : Finset (X.presheaf.stalk x)}
    (hZ : IsRegularSystemOfParameters _ Z) (hJZ : J ⊆ Z)
    (hJ : E.stalkIdeal x = Ideal.span {∏ a ∈ J, a}) {a : X.presheaf.stalk x} (ha : a ∈ J) :
    ∃ C ∈ E.irreducibleComponents, x ∈ C.pts ∧ C.stalkIdeal x = Ideal.span {a} := by
  refine Subscheme.exists_mem_irreducibleComponents_of_mem_minimalPrimes E x ?_
  rw [hJ, ((ExtendsToRSOP.of_isRegularSystemOfParameters hZ).mono hJZ).minimalPrimes_span_prod]
  exact ⟨a, ha, rfl⟩

/-- The chart computation of p. 169 in the form used for Remark 1: given a regular system of
parameters `Z` at `x = f(y)` (adapted to `B` if `x ∈ B`), there is a part `K` of a regular system
of parameters at `y` such that `E_{y} = f⁻¹(B)_y` and the strict transform of every subscheme
defined by `∏ J`, `J ⊆ Z`, are generated at `y` by products of subsets of `K` (with at most as
many factors).

The last conjunct is the paper's computation of the strict transform `E'` of a reduced subscheme `E`
from the strict transforms of its irreducible components `F_a` through `x`, defined at `x` by the
members `a ∈ J` of `Z` (p. 169: "the strict transform `F_j'` of `F_j` contains the point `x'` if and
only if `j ≠ t` and `z'_j ∈ M`, in which case `F_j'` is defined by `z'_j = 0` at `x'`"; `E' = ⋃ F_a'`,
`Subscheme.strictTransform_iInf_fintype`), in the chart `O_{x'} = A_M`
(`exists_chart_ringOfFractions`). -/
theorem _root_.Hironaka.DatumTransform.exists_stalk_transform_components (hX : X.IsNonsingular) (hBns : B.IsNonsingular)
    (t : MonoidalTransformation X B) (y : t.X') {Z : Finset (X.presheaf.stalk (t.f y))}
    (hZ : IsRegularSystemOfParameters _ Z)
    (hBZ : t.f y ∈ B.pts → ∃ T ⊆ Z, B.stalkIdeal (t.f y) = Ideal.span (T : Set _)) :
    ∃ K : Finset (t.X'.presheaf.stalk y), ExtendsToRSOP _ K ∧
      (∃ K₀ ⊆ K, K₀.card ≤ 1 ∧ t.exceptional.stalkIdeal y = Ideal.span {∏ k ∈ K₀, k}) ∧
      (∀ J ⊆ Z, ∀ V : Subscheme X, V.stalkIdeal (t.f y) = Ideal.span {(∏ z ∈ J, z)} →
        ∃ K₀ ⊆ K, K₀.card ≤ J.card ∧
          (Subscheme.strictTransform t V).stalkIdeal y = Ideal.span {∏ k ∈ K₀, k}) ∧
      ∀ (E : Subscheme X) (J : Finset (X.presheaf.stalk (t.f y))), J ⊆ Z →
        E.stalkIdeal (t.f y) = Ideal.span {(∏ z ∈ J, z)} →
        (∀ a ∈ J, ∃ C ∈ E.irreducibleComponents, t.f y ∈ C.pts ∧
          C.stalkIdeal (t.f y) = Ideal.span {a}) →
        ∃ K₀ ⊆ K, (Subscheme.strictTransform t E).stalkIdeal y = Ideal.span {∏ k ∈ K₀, k} := by
  have : IsRegularLocalRing (t.X'.presheaf.stalk y) := t.isRegularLocalRing_stalk hX hBns y
  have : IsRegularLocalRing (X.presheaf.stalk (t.f y)) := hX _
  have := isDomain_of_isRegularLocalRing (X.presheaf.stalk (t.f y))
  by_cases hy : t.f y ∈ B.pts
  · obtain ⟨T, hTZ, hT⟩ := hBZ hy
    -- "Then the local ring `O_{x'}` … is a ring of fractions of `A` …; `z'_v`; `E'_{α+1}`; the `z'_v` in
    -- `M` extend to a regular system of parameters"
    obtain ⟨zt, -, -, φ, hzt, -, -, -, -, -, -, hexc, hmem, hinj, hrsop, hst⟩ :=
      Hironaka.DatumTransform.exists_chart_ringOfFractions t y hZ hTZ hT
    set M := maximalIdeal (t.X'.presheaf.stalk y) with hM
    have hSZ : ∀ J ⊆ Z, (J.erase zt).filter (fun z => φ z ∈ M) ⊆ Z.filter (fun z => φ z ∈ M) :=
      fun J hJZ => Finset.filter_subset_filter _ ((J.erase_subset zt).trans hJZ)
    refine ⟨_, hrsop, ⟨{φ zt}, Finset.singleton_subset_iff.mpr (Finset.mem_image_of_mem φ
      (Finset.mem_filter.mpr ⟨hTZ hzt, hmem⟩)), by simp, by rw [hexc, Finset.prod_singleton]⟩,
      fun J hJZ V hV => ?_, fun E J hJZ hJ hcomp => ?_⟩
    · -- the strict transform of `V = (∏ J)`, computed at once
      refine ⟨_, Finset.image_subset_image (hSZ J hJZ),
        Finset.card_image_le.trans ((Finset.card_filter_le _ _).trans (Finset.card_erase_le)), ?_⟩
      rw [hst J hJZ V hV, Hironaka.DatumTransform.prod_image_eq φ hinj _ (fun z hz => by
        have := hSZ J hJZ hz
        rw [Finset.mem_filter] at this
        exact this)]
    · -- the strict transform of `E = ⋃ F_a`, from those of its components `F_a`
      choose! F hFcomp hFpts hFx using hcomp
      set J' := (J.erase zt).filter (fun z => φ z ∈ M) with hJ'
      refine ⟨J'.image φ, Finset.image_subset_image (hSZ J hJZ), ?_⟩
      have hiff : ∀ a : J, a.1 ∈ J' ↔ a.1 ≠ zt ∧ φ a.1 ∈ M := fun a => by
        rw [hJ', Finset.mem_filter, Finset.mem_erase]
        exact ⟨fun ⟨⟨h1, _⟩, h2⟩ => ⟨h1, h2⟩, fun ⟨h1, h2⟩ => ⟨⟨h1, a.2⟩, h2⟩⟩
      -- "the strict transform `F_a'` of `F_a` contains `x'` iff `a ≠ z_t` and `z'_a ∈ M`, in which case
      -- `F_a'` is defined by `z'_a = 0`"
      have hFa : ∀ a : J, a.1 ∈ J' →
          (Subscheme.strictTransform t (F a)).stalkIdeal y = Ideal.span {φ a.1} := fun a ha =>
        (Hironaka.DatumTransform.strictTransform_component_stalk t y hst (hJZ a.2)
          (hFx a.1 a.2)).2 ((hiff a).mp ha)
      have hFb : ∀ a : J, a.1 ∉ J' → (Subscheme.strictTransform t (F a)).stalkIdeal y = ⊤ :=
        fun a ha => by
          by_contra hne
          exact ha ((hiff a).mpr ((Hironaka.DatumTransform.strictTransform_component_stalk t y hst
            (hJZ a.2) (hFx a.1 a.2)).1.mp (Subscheme.mem_pts_iff_stalkIdeal_ne_top.mpr hne)))
      -- "From these follows …": `E' = ⋃ F_a'`, i.e. `E'_{x'} = ⋂ F_a'_{x'}`, a product of distinct
      -- members of a regular system of parameters
      have hVx : (⨅ a : J, F a.1).stalkIdeal (t.f y) = E.stalkIdeal (t.f y) := by
        rw [Hironaka.DatumTransform.stalkIdeal_iInf_fintype, hJ,
          ← ((ExtendsToRSOP.of_isRegularSystemOfParameters hZ).mono hJZ).iInf_span_singleton]
        simp only [iInf_subtype']
        exact iInf_congr fun a => hFx a.1 a.2
      have h1 : (Subscheme.strictTransform t E).stalkIdeal y =
          (Subscheme.strictTransform t (⨅ a : J, F a.1)).stalkIdeal y := by
        rw [Subscheme.strictTransform_stalkIdeal, Subscheme.strictTransform_stalkIdeal,
          stalkIdeal_totalTransform, stalkIdeal_totalTransform, hVx]
      have himg : ⨅ k ∈ J'.image φ, Ideal.span {k} = ⨅ a ∈ J', Ideal.span {φ a} := by
        apply le_antisymm
        · exact le_iInf₂ fun a ha => iInf₂_le (φ a) (Finset.mem_image_of_mem φ ha)
        · refine le_iInf₂ fun k hk => ?_
          obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hk
          exact iInf₂_le a ha
      rw [h1, Subscheme.strictTransform_iInf_fintype hX,
        Hironaka.DatumTransform.stalkIdeal_iInf_fintype,
        ← (hrsop.mono (Finset.image_subset_image (hSZ J hJZ))).iInf_span_singleton, himg]
      apply le_antisymm
      · refine le_iInf fun a => le_iInf fun ha => ?_
        have haJ : a ∈ J := (Finset.mem_erase.mp (Finset.mem_filter.mp ha).1).2
        have h2 := iInf_le (fun b : J => (Subscheme.strictTransform t (F b)).stalkIdeal y) ⟨a, haJ⟩
        rw [hFa ⟨a, haJ⟩ ha] at h2
        exact h2
      · refine le_iInf fun a => ?_
        by_cases ha : (a : X.presheaf.stalk (t.f y)) ∈ J'
        · rw [hFa a ha]
          exact iInf₂_le (a : X.presheaf.stalk (t.f y)) ha
        · rw [hFb a ha]
          exact le_top
  · -- off `B`, `f` is a local isomorphism
    obtain ⟨e, hexc, hst⟩ := Hironaka.DatumTransform.exists_offCenter hX t y hy
    refine ⟨Z.image e, (ExtendsToRSOP.of_isRegularSystemOfParameters hZ).map_ringEquiv e,
      ⟨∅, Finset.empty_subset _, by simp, by
        rw [hexc, Finset.prod_empty, Ideal.span_singleton_one]⟩, fun J hJZ V hV => ?_,
      fun E J hJZ hJ _ => ?_⟩
    · exact ⟨J.image e, Finset.image_subset_image hJZ, Finset.card_image_le, by
        rw [hst, hV, Hironaka.DatumTransform.map_span_prod]⟩
    · exact ⟨J.image e, Finset.image_subset_image hJZ, by
        rw [hst, hJ, Hironaka.DatumTransform.map_span_prod]⟩

/-- The chart computation of p. 169 in the form used for the `E_i'` of type II data (and the closed
restriction `F'`): see `exists_stalk_transform_components`. -/
theorem _root_.Hironaka.DatumTransform.exists_stalk_transform (hX : X.IsNonsingular) (hBns : B.IsNonsingular)
    (t : MonoidalTransformation X B) (y : t.X') {Z : Finset (X.presheaf.stalk (t.f y))}
    (hZ : IsRegularSystemOfParameters _ Z)
    (hBZ : t.f y ∈ B.pts → ∃ T ⊆ Z, B.stalkIdeal (t.f y) = Ideal.span (T : Set _)) :
    ∃ K : Finset (t.X'.presheaf.stalk y), ExtendsToRSOP _ K ∧
      (∃ K₀ ⊆ K, K₀.card ≤ 1 ∧ t.exceptional.stalkIdeal y = Ideal.span {∏ k ∈ K₀, k}) ∧
      ∀ J ⊆ Z, ∀ V : Subscheme X, V.stalkIdeal (t.f y) = Ideal.span {(∏ z ∈ J, z)} →
        ∃ K₀ ⊆ K, K₀.card ≤ J.card ∧
          (Subscheme.strictTransform t V).stalkIdeal y = Ideal.span {∏ k ∈ K₀, k} := by
  obtain ⟨K, hK, hexc, hst, -⟩ :=
    Hironaka.DatumTransform.exists_stalk_transform_components hX hBns t y hZ hBZ
  exact ⟨K, hK, hexc, hst⟩

theorem _root_.Hironaka.DatumTransform.span_prod_inf_of_subset {R : Type u} [CommRing R] [IsRegularLocalRing R]
    {K K₁ K₂ : Finset R} (hK : ExtendsToRSOP R K) (h₁ : K₁ ⊆ K) (h₂ : K₂ ⊆ K) :
    Ideal.span {∏ k ∈ K₁, k} ⊓ Ideal.span {∏ k ∈ K₂, k} = Ideal.span {∏ k ∈ K₁ ∪ K₂, k} :=
  ExtendsToRSOP.span_prod_inf (hK.mono (Finset.union_subset h₁ h₂))

theorem _root_.Hironaka.DatumTransform.iInf_span_prod_of_subset {R : Type u} [CommRing R] [IsRegularLocalRing R] {ι : Type*}
    [Fintype ι] {K : Finset R} (hK : ExtendsToRSOP R K) (L : ι → Finset R) (hL : ∀ i, L i ⊆ K) :
    ⨅ i, Ideal.span {∏ k ∈ L i, k} = Ideal.span {∏ k ∈ Finset.univ.biUnion L, k} := by
  have hU : Finset.univ.biUnion L ⊆ K := Finset.biUnion_subset.mpr fun i _ => hL i
  rw [← (hK.mono hU).iInf_span_singleton, Finset.iInf_biUnion]
  simp only [Finset.mem_univ, iInf_true]
  exact iInf_congr fun i => ((hK.mono (hL i)).iInf_span_singleton).symm

/-- The stalks of the strict transform of a reduced subscheme are radical (p. 169, "`W'` is
reduced"). -/
theorem _root_.Hironaka.DatumTransform.isRadical_stalkIdeal_strictTransform (hX : X.IsNonsingular)
    (t : MonoidalTransformation X B) {V : Subscheme X} (hV : V.IsReduced) (y : t.X') :
    ((Subscheme.strictTransform t V).stalkIdeal y).IsRadical := by
  have : IsRegularLocalRing (X.presheaf.stalk (t.f y)) := hX _
  have := isDomain_of_isRegularLocalRing (X.presheaf.stalk (t.f y))
  obtain ⟨s, e, he, hE⟩ := t.exists_monoidalTransform_stalk_exceptional y
  have hrad := MonoidalTransform.isRadical_saturation s
    (Subscheme.isRadical_stalkIdeal_of_isReduced hV (t.f y))
  rw [Subscheme.strictTransform_stalkIdeal, hE, t.stalkIdeal_totalTransform_eq_map y s e he]
  have h2 : Ideal.span {e s.xR} = (Ideal.span {s.xR}).map e := by
    rw [Ideal.map_span, Set.image_singleton]
  rw [h2]
  have h3 : (⨆ n : ℕ, ((V.stalkIdeal (t.f y)).map s.toRing).colon
      ((Ideal.span {s.xR} ^ n : Ideal s.ring) : Set s.ring)).map e =
      ⨆ n : ℕ, (((V.stalkIdeal (t.f y)).map s.toRing).map e).colon
        (((Ideal.span {s.xR}).map e ^ n : Ideal _) : Set (t.X'.presheaf.stalk y)) := by
    rw [Ideal.map_iSup]
    refine iSup_congr fun n => ?_
    rw [Ideal.map_colon_ringEquiv, Ideal.map_pow]
  rw [← h3]
  exact Hironaka.DatumTransform.isRadical_map_ringEquiv e hrad

theorem _root_.Hironaka.DatumTransform.iInf_eq_span_prod {R : Type u} [CommRing R] [IsRegularLocalRing R] {ι : Type*}
    (D : ι → Ideal R) {K : Finset R} (hK : ExtendsToRSOP R K)
    (hD : ∀ i, D i = ⊤ ∨ ∃ k ∈ K, D i = Ideal.span {k}) :
    ∃ K₁ ⊆ K, ⨅ i, D i = Ideal.span {∏ k ∈ K₁, k} := by
  refine ⟨K.filter fun k => ∃ i, D i = Ideal.span {k}, Finset.filter_subset _ _, ?_⟩
  rw [← (hK.mono (Finset.filter_subset _ _)).iInf_span_singleton]
  apply le_antisymm
  · refine le_iInf₂ fun k hk => ?_
    obtain ⟨i, hi⟩ := (Finset.mem_filter.mp hk).2
    exact (iInf_le D i).trans hi.le
  · refine le_iInf fun i => ?_
    rcases hD i with h | ⟨k, hk, h⟩
    · rw [h]; exact le_top
    · rw [h]; exact iInf₂_le k (Finset.mem_filter.mpr ⟨hk, i, h⟩)

section Consequences

variable {Y : Scheme.{u}}

theorem _root_.Hironaka.DatumTransform.isReduced_of_forall_stalk (hY : Y.IsNonsingular) {D : Subscheme Y}
    (h : ∀ y, ∃ K : Finset (Y.presheaf.stalk y), ExtendsToRSOP _ K ∧
      D.stalkIdeal y = Ideal.span {∏ k ∈ K, k}) : D.IsReduced :=
  Subscheme.isReduced_of_isRadical_stalkIdeal fun y => by
    have : IsRegularLocalRing (Y.presheaf.stalk y) := hY y
    obtain ⟨K, hK, hD⟩ := h y
    rw [hD]
    exact hK.isRadical_span_prod

theorem _root_.Hironaka.DatumTransform.isEverywhereCodimOne_of_forall_stalk (hY : Y.IsNonsingular) {D : Subscheme Y}
    (h : ∀ y, ∃ K : Finset (Y.presheaf.stalk y), ExtendsToRSOP _ K ∧
      D.stalkIdeal y = Ideal.span {∏ k ∈ K, k}) : D.IsEverywhereCodimOne := by
  intro y hy
  have : IsRegularLocalRing (Y.presheaf.stalk y) := hY y
  obtain ⟨K, hK, hD⟩ := h y
  have hKne : K.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    rintro rfl
    apply Subscheme.mem_pts_iff_stalkIdeal_ne_top.mp hy
    rw [hD, Finset.prod_empty, Ideal.span_singleton_one]
  rw [Subscheme.codimAt, hD, hK.height_span_prod hKne]
  rfl

theorem _root_.Hironaka.DatumTransform.hasOnlyNormalCrossings_of_forall_stalk (hY : Y.IsNonsingular) {D : Subscheme Y}
    (hDred : D.IsReduced)
    (h : ∀ y, ∃ K : Finset (Y.presheaf.stalk y), ExtendsToRSOP _ K ∧
      D.stalkIdeal y = Ideal.span {∏ k ∈ K, k}) : D.HasOnlyNormalCrossings := by
  intro y
  have : IsRegularLocalRing (Y.presheaf.stalk y) := hY y
  obtain ⟨K, ⟨Z, hKZ, hZ⟩, hD⟩ := h y
  refine (Subscheme.hasOnlyNormalCrossingsWithAt_iff hDred (hY y)).mpr
    ⟨Z, hZ, ⟨K, hKZ, hD⟩, ⟨∅, Finset.empty_subset _, ?_⟩⟩
  rw [Subscheme.stalkIdeal_bot_eq, Finset.coe_empty, Ideal.span_empty]

/-- A subscheme whose stalks are `(1)` or generated by a member of a regular system of
parameters, and which is irreducible if non-empty, is non-singular irreducible of codimension
one (or empty). -/
theorem _root_.Hironaka.DatumTransform.isNonsingularIrreducibleCodimOne_of_forall_stalk (hY : Y.IsNonsingular)
    {D : Subscheme Y} (hirr : D.pts.Nonempty → D.IsIrreducible)
    (h : ∀ y, D.stalkIdeal y = ⊤ ∨ ∃ k : Y.presheaf.stalk y, ExtendsToRSOP _ {k} ∧
      D.stalkIdeal y = Ideal.span {k}) : D.IsNonsingularIrreducibleCodimOne := by
  rcases D.pts.eq_empty_or_nonempty with hD | hD
  · exact Or.inl (Subscheme.eq_empty_of_pts_eq_empty hD)
  obtain ⟨y₀, hy₀⟩ := hD
  have hstalk : ∀ y ∈ D.pts, ∃ k : Y.presheaf.stalk y, ExtendsToRSOP _ {k} ∧
      D.stalkIdeal y = Ideal.span {k} := fun y hy =>
    (h y).resolve_left (Subscheme.mem_pts_iff_stalkIdeal_ne_top.mp hy)
  have hns : D.IsNonsingular := Subscheme.isNonsingular_of_stalk_quot D fun y hy => by
    have : IsRegularLocalRing (Y.presheaf.stalk y) := hY y
    obtain ⟨k, hk, hD⟩ := hstalk y hy
    rw [hD]
    exact hk.isRegularLocalRing_quotient_span_singleton (Finset.mem_singleton_self k)
  have hI := hirr ⟨y₀, hy₀⟩
  refine Or.inr ⟨hns, hI, ?_⟩
  rw [Subscheme.codim_eq_height D hns hI hy₀]
  have : IsRegularLocalRing (Y.presheaf.stalk y₀) := hY y₀
  obtain ⟨k, hk, hD⟩ := hstalk y₀ hy₀
  have := hk.height_span_prod (Finset.singleton_nonempty k)
  rw [Finset.prod_singleton] at this
  rw [hD, this]

end Consequences

/-- Type I, p. 169: "To prove the assertion on `f*(ℜ)`, all that may be non-trivial is the normal
crossing property of `E' ∪ E'_{α+1}` (or `E' ∪ F' ∪ E'_{α+1}` or …).  This can be seen as follows: Let `x'` be any point of `X'`, and
`x = f(x')`.  Then we can find a regular system of parameters `(z₁, …, z_s)` of the local ring `O_x` of
`X` at `x`, such that every irreducible component `F_i` of `E` containing `x` is defined by `z_j = 0` at
`x` for some `j`, and that `B` is defined by `z_{r+1} = ⋯ = z_s = 0` at `x`.  Then the local ring
`O_{x'}` of `X'` at `x'` is a ring of fractions of `A = O_x[z_{r+1}z_t^{-1}, …, z_s z_t^{-1}]` for some
`t` with respect to a prime ideal `M` in `A`.  Let `z'_v = z_v` for `1 ≤ v ≤ r`, `z'_t = z_t` and
`z'_v = z_v z_t^{-1}` for `r + 1 ≤ v (≠ t) ≤ s`.  It is then easily seen that, `(F_i, z_j)` being as
above, the strict transform `F_i'` of `F_i` contains the point `x'` if and only if `j ≠ t` and
`z'_j ∈ M`, in which case `F_i'` is defined by `z'_j = 0` at `x'`, that `E'_{α+1}` is defined by
`z'_t = 0` at `x'`, provided `x' ∈ E'_{α+1}`, and that a system of those `z'_v` which are in `M` can be
extended to a regular system of parameters of `O_{x'} = A_M`.  From these follows the normal crossing
property of `E' ∪ E'_{α+1}`."

The stalks of `E' ∪ E'_{α+1}` are generated by products of parts of regular systems of parameters.
The proof is the paper's: at a point over `B` the components `F_a` of `E` through `x` (defined by the
members `a ∈ J ⊆ Z`), the chart `O_{x'} = A_M` (`exists_chart_ringOfFractions`), the strict transforms
`F_a'` (`strictTransform_component_stalk`), `E' = ⋃ F_a'` (`Subscheme.strictTransform_iInf_fintype`),
`E'_{α+1} = (z'_t)` and the extension of the `z'_v ∈ M` to a regular system of parameters; off `B`, `f` is
a local isomorphism. -/
theorem _root_.Hironaka.DatumTransform.exists_extendsToRSOP_stalkIdeal_union_exceptional (hX : X.IsNonsingular) (hBns : B.IsNonsingular)
    (t : MonoidalTransformation X B) {E : Subscheme X} (hEred : E.IsReduced)
    (hE : ∀ x, E.HasOnlyNormalCrossingsAt x)
    (hEB : ∀ x ∈ B.pts, E.HasOnlyNormalCrossingsWithAt B x) (y : t.X') :
    ∃ K : Finset (t.X'.presheaf.stalk y), ExtendsToRSOP _ K ∧
      ((Subscheme.strictTransform t E).union t.exceptional).stalkIdeal y =
        Ideal.span {∏ k ∈ K, k} := by
  have : IsRegularLocalRing (t.X'.presheaf.stalk y) := t.isRegularLocalRing_stalk hX hBns y
  -- "we can find a regular system of parameters `(z₁, …, z_s)` of `O_x` such that every irreducible
  -- component `F_i` of `E` containing `x` is defined by `z_j = 0` at `x` for some `j`, and that `B` is
  -- defined by `z_{r+1} = ⋯ = z_s = 0` at `x`"
  obtain ⟨Z, hZ, hBZ, J, hJZ, hJ⟩ : ∃ Z : Finset (X.presheaf.stalk (t.f y)),
      IsRegularSystemOfParameters _ Z ∧
      (t.f y ∈ B.pts → ∃ T ⊆ Z, B.stalkIdeal (t.f y) = Ideal.span (T : Set _)) ∧
      ∃ J ⊆ Z, E.stalkIdeal (t.f y) = Ideal.span {(∏ z ∈ J, z)} := by
    by_cases hy : t.f y ∈ B.pts
    · obtain ⟨Z, hZ, ⟨J, hJZ, hJ⟩, ⟨T, hTZ, hT⟩⟩ :=
        (Subscheme.hasOnlyNormalCrossingsWithAt_iff hEred (hX _)).mp (hEB _ hy)
      exact ⟨Z, hZ, fun _ => ⟨T, hTZ, hT⟩, J, hJZ, hJ⟩
    · obtain ⟨Z, hZ, ⟨J, hJZ, hJ⟩, -⟩ :=
        (Subscheme.hasOnlyNormalCrossingsWithAt_iff hEred (hX _)).mp (hE _)
      exact ⟨Z, hZ, fun h => absurd h hy, J, hJZ, hJ⟩
  have : IsRegularLocalRing (X.presheaf.stalk (t.f y)) := hX _
  -- the chart `O_{x'} = A_M`, the strict transforms `F_a'` of the components `F_a`, `E' = ⋃ F_a'`,
  -- `E'_{α+1} = (z'_t)` and the extension of the `z'_v ∈ M` to a regular system of parameters
  obtain ⟨K, hK, ⟨K₀, hK₀, -, hexc⟩, -, hst⟩ :=
    Hironaka.DatumTransform.exists_stalk_transform_components hX hBns t y hZ hBZ
  obtain ⟨K₁, hK₁, hE'⟩ := hst E J hJZ hJ fun a ha =>
    Hironaka.DatumTransform.exists_component_of_mem hZ hJZ hJ ha
  -- "From these follows the normal crossing property of `E' ∪ E'_{α+1}`"
  refine ⟨K₁ ∪ K₀, hK.mono (Finset.union_subset hK₁ hK₀), ?_⟩
  rw [Subscheme.union, Subscheme.stalkIdeal_inf_eq, hE', hexc, Hironaka.DatumTransform.span_prod_inf_of_subset hK hK₁ hK₀]

theorem _root_.Hironaka.DatumTransform.card_le_one_cases {α : Type*} {K : Finset α} (h : K.card ≤ 1) :
    K = ∅ ∨ ∃ k, K = {k} := by
  rcases K.eq_empty_or_nonempty with h0 | h0
  · exact Or.inl h0
  · exact Or.inr (Finset.card_eq_one.mp (le_antisymm h (Finset.card_pos.mpr h0)))

/-- Type II (p. 169): the stalks of the `E_i'` and of `E_{α+1}`, given regular systems of
parameters adapted to the `E_i` and to `B`. -/
theorem _root_.Hironaka.DatumTransform.exists_extendsToRSOP_stalkIdeal_family (hX : X.IsNonsingular) (hBns : B.IsNonsingular)
    (t : MonoidalTransformation X B) {ι : Type*} (E : ι → Subscheme X)
    (hdata : ∀ x, ∃ Z : Finset (X.presheaf.stalk x), IsRegularSystemOfParameters _ Z ∧
      (x ∈ B.pts → ∃ T ⊆ Z, B.stalkIdeal x = Ideal.span (T : Set _)) ∧
      ∀ i, (E i).stalkIdeal x = ⊤ ∨ ∃ a ∈ Z, (E i).stalkIdeal x = Ideal.span {a})
    (y : t.X') :
    ∃ K : Finset (t.X'.presheaf.stalk y), ExtendsToRSOP _ K ∧
      (∃ K₀ ⊆ K, K₀.card ≤ 1 ∧ t.exceptional.stalkIdeal y = Ideal.span {∏ k ∈ K₀, k}) ∧
      ∀ i, ∃ K₀ ⊆ K, K₀.card ≤ 1 ∧
        (Subscheme.strictTransform t (E i)).stalkIdeal y = Ideal.span {∏ k ∈ K₀, k} := by
  obtain ⟨Z, hZ, hBZ, hEZ⟩ := hdata (t.f y)
  obtain ⟨K, hK, hexc, hst⟩ := Hironaka.DatumTransform.exists_stalk_transform hX hBns t y hZ hBZ
  refine ⟨K, hK, hexc, fun j => ?_⟩
  rcases hEZ j with h | ⟨a, ha, h⟩
  · obtain ⟨K₀, h1, h2, h3⟩ := hst ∅ (Finset.empty_subset _) (E j)
      (by rw [h, Finset.prod_empty, Ideal.span_singleton_one])
    exact ⟨K₀, h1, h2.trans (by simp), h3⟩
  · obtain ⟨K₀, h1, h2, h3⟩ := hst {a} (Finset.singleton_subset_iff.mpr ha) (E j)
      (by rw [h, Finset.prod_singleton])
    exact ⟨K₀, h1, h2.trans (by simp), h3⟩

/-- The regular systems of parameters needed by `DatumTransform.exists_extendsToRSOP_stalkIdeal_family` for a type II datum with a
permissible center. -/
theorem _root_.Hironaka.DatumTransform.exists_rsop_adapted_of_isDatum {α : ℕ} (E : Fin α → Subscheme X) (hX : X.IsNonsingular)
    (hE : ∀ i, (E i).IsNonsingularIrreducibleCodimOne)
    (hNC : (⨅ i, E i).HasOnlyNormalCrossings) (hNCB : (⨅ i, E i).HasOnlyNormalCrossingsWith B)
    (x : X) : ∃ Z : Finset (X.presheaf.stalk x), IsRegularSystemOfParameters _ Z ∧
      (x ∈ B.pts → ∃ T ⊆ Z, B.stalkIdeal x = Ideal.span (T : Set _)) ∧
      ∀ i, (E i).stalkIdeal x = ⊤ ∨ ∃ a ∈ Z, (E i).stalkIdeal x = Ideal.span {a} := by
  have : IsRegularLocalRing (X.presheaf.stalk x) := hX x
  by_cases hx : x ∈ B.pts
  · obtain ⟨Z, hZ, hT, hE'⟩ := Hironaka.DatumTransform.exists_rsop_of_hasOnlyNormalCrossingsWithAt E hE (fun i => iInf_le _ i)
      (hNCB _ hx)
    exact ⟨Z, hZ, fun _ => hT, hE'⟩
  · obtain ⟨Z, hZ, -, hE'⟩ := Hironaka.DatumTransform.exists_rsop_of_hasOnlyNormalCrossingsWithAt E hE
      (fun i => iInf_le _ i) (D := ⊥) (hNC x)
    exact ⟨Z, hZ, fun h => absurd h hx, hE'⟩

theorem _root_.Hironaka.DatumTransform.stalkIdeal_eq_top_or_exists_of_card_le_one {Y : Scheme.{u}} {D : Subscheme Y} {y : Y}
    {K K₀ : Finset (Y.presheaf.stalk y)} (hK : ExtendsToRSOP _ K) (h1 : K₀ ⊆ K)
    (h2 : K₀.card ≤ 1) (h3 : D.stalkIdeal y = Ideal.span {∏ k ∈ K₀, k}) :
    D.stalkIdeal y = ⊤ ∨ ∃ k : Y.presheaf.stalk y, ExtendsToRSOP _ {k} ∧
      D.stalkIdeal y = Ideal.span {k} := by
  rcases Hironaka.DatumTransform.card_le_one_cases h2 with rfl | ⟨k, rfl⟩
  · left; rw [h3, Finset.prod_empty, Ideal.span_singleton_one]
  · right
    obtain ⟨Z, hKZ, hZ⟩ := hK
    exact ⟨k, ⟨Z, h1.trans hKZ, hZ⟩, by rw [h3, Finset.prod_singleton]⟩

theorem _root_.Hironaka.DatumTransform.strictTransform_isIrreducible_of_nonempty (t : MonoidalTransformation X B)
    {V : Subscheme X} (hV : V.IsNonsingularIrreducibleCodimOne)
    (hne : (Subscheme.strictTransform t V).pts.Nonempty) :
    (Subscheme.strictTransform t V).IsIrreducible := by
  obtain ⟨y, hy⟩ := hne
  obtain ⟨q, hq, hqE, -⟩ := t.exists_generization_notMem_exceptional V hy
  have hfq : t.f q ∈ V.pts := t.pts_strictTransform_subset V hq
  have hfqB : t.f q ∉ B.pts := by
    rw [MonoidalTransformation.pts_exceptional] at hqE; exact hqE
  rcases hV with rfl | ⟨-, hirr, -⟩
  · rw [Hironaka.DatumTransform.pts_empty] at hfq; exact absurd hfq id
  · exact t.strictTransform_isIrreducible V hirr (fun h => hfqB (h hfq))

/-- `E_{α+1} = f⁻¹(B)` is irreducible for a non-singular irreducible center `B` of a non-singular
algebraic `X` (used without comment in Remark 1, p. 169; `compat:blowup-exceptional-irreducible`). -/
theorem _root_.Hironaka.DatumTransform.exceptional_isIrreducible [IsAlgebraicScheme X] (hX : X.IsNonsingular) (hBns : B.IsNonsingular)
    (hBirr : B.IsIrreducible) (t : MonoidalTransformation X B)
    (hne : t.exceptional.pts.Nonempty) : t.exceptional.IsIrreducible :=
  MonoidalTransformation.isIrreducible_exceptional hX hBns hBirr t hne

/-- `ν(ℜ) < ∞` (p. 169): every `ν(J_x)` is finite (Krull's intersection theorem, `J_x ≠ 0`), and
the open sets `{x | ν(J_x) ≤ ν}` (Cor. 1 of Th. 2, Ch. III) cover the quasi-compact `X`. -/
theorem _root_.Hironaka.DatumII.Raw.nu_ne_top [Hironaka.Cited.IsHironakaBaseIsClosedSingularLocus.{u}] [Hironaka.Cited.CurveFiniteIntegralClosure.{u}] [Hironaka.Cited.IsRegularLocalRingLocalizationOfIsRegularLocalRing.{u}] [IsAlgebraicScheme X] (hX : X.IsNonsingular) (ℜ : DatumII.Raw X)
    (hJ : ∀ x, ℜ.J.stalkIdeal x ≠ ⊥) : ℜ.nu ≠ ⊤ := by
  have hfin : ∀ x : X, ∃ n : ℕ, Ideal.nu (ℜ.J.stalkIdeal x) ≤ n := by
    intro x
    have : IsRegularLocalRing (X.presheaf.stalk x) := hX x
    have hbot := Ideal.iInf_pow_eq_bot_of_isLocalRing (maximalIdeal (X.presheaf.stalk x))
      (maximalIdeal.isMaximal _).ne_top
    obtain ⟨n, hn⟩ : ∃ n, ¬ ℜ.J.stalkIdeal x ≤ maximalIdeal _ ^ n := by
      by_contra h
      push Not at h
      exact hJ x (eq_bot_iff.mpr (hbot ▸ le_iInf h))
    refine ⟨n, Ideal.ord_le fun ν hν => ?_⟩
    by_contra hlt
    push Not at hlt
    exact hn (hν.trans (Ideal.pow_le_pow_right (Nat.cast_lt.mp hlt).le))
  choose U hUo hUmem using fun n : ℕ => exists_isOpen_nu_stalk_le X hX ℜ.J n
  have := IsAlgebraicScheme.isNoetherian X
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover U hUo (fun x _ => by
    obtain ⟨n, hn⟩ := hfin x
    exact Set.mem_iUnion.mpr ⟨n, (hUmem n x).mpr hn⟩)
  have hbound : ∀ x, ℜ.nuAt x ≤ (s.sup id : ℕ) := by
    intro x
    obtain ⟨n, hn, hxn⟩ := Set.mem_iUnion₂.mp (hs (Set.mem_univ x))
    exact ((hUmem n x).mp hxn).trans (by exact_mod_cast Finset.le_sup (f := id) hn)
  exact ne_top_of_le_ne_top (ENat.natCast_ne_top (s.sup id)) (iSup₂_le fun x _ => hbound x)

/-- The printed "max" of p. 165 is attained: "`ν(ℜ^N_II) = max_{x ∈ S(ℜ^N_II)} {ν(J_x)}` if
`S(ℜ^N_II)` is not empty".  Since `ν(ℜ) < ∞` (`DatumII.Raw.nu_ne_top`), the supremum of the
natural numbers `ν(J_x)`, `x ∈ S(ℜ)`, is a maximum: a non-empty set of natural numbers with a finite
supremum is finite, so its supremum belongs to it.

Deviation from the paper (gap filled): the paper writes "max" without comment; the attainment of
the supremum used by Lean (`DatumII.Raw.nu`) is the content of the word. -/
@[blueprint "lem:I.nu-attained"
  (statement := /-- Let $\mathfrak R^N_{\mathrm{II}}$ be a resolution datum on a non-singular
    algebraic scheme $X$ with $S(\mathfrak R^N_{\mathrm{II}})\ne\emptyset$. Then there is a
    point $x\in S(\mathfrak R^N_{\mathrm{II}})$ with $\nu(J_x)=\nu(\mathfrak R^N_{\mathrm{II}})$,
    i.e.\ the supremum in \cref{def:I.nu} is the maximum printed on p.~165.
    \textbf{Gap in the paper filled.} The paper writes ``max'' without justifying that it is
    attained. -/)
  (proof := /-- $\nu(\mathfrak R)<\infty$ (\cref{rem:I.1-transform-is-datum-II}), so the set
    $\{\nu(J_x)\mid x\in S(\mathfrak R)\}$ of natural numbers has a finite supremum, hence is
    finite and contains it. -/)
  (latexEnv := "lemma")]
theorem _root_.Hironaka.DatumII.Raw.exists_mem_S_nuAt_eq_nu [Hironaka.Cited.IsHironakaBaseIsClosedSingularLocus.{u}] [Hironaka.Cited.CurveFiniteIntegralClosure.{u}] [Hironaka.Cited.IsRegularLocalRingLocalizationOfIsRegularLocalRing.{u}] [IsAlgebraicScheme X] (hX : X.IsNonsingular)
    (ℜ : DatumII.Raw X) (hJ : ∀ x, ℜ.J.stalkIdeal x ≠ ⊥) (hS : ℜ.S.Nonempty) :
    ∃ x ∈ ℜ.S, ℜ.nuAt x = ℜ.nu := by
  have hlt : ℜ.nu < ⊤ := lt_top_iff_ne_top.mpr (ℜ.nu_ne_top hX hJ)
  have : Nonempty ℜ.S := hS.to_subtype
  have heq : ℜ.nu = ⨆ x : ℜ.S, ℜ.nuAt x := by
    rw [DatumII.Raw.nu, iSup_subtype]
  rw [heq] at hlt
  obtain ⟨⟨x, hx⟩, hxeq⟩ := ENat.exists_eq_iSup_of_lt_top hlt
  exact ⟨x, hx, hxeq.trans heq.symm⟩

/-- A prime of height one containing the product of part of a regular system of parameters is
generated by one of the factors. -/
theorem _root_.Hironaka.DatumTransform.eq_span_of_prod_le {R : Type u} [CommRing R] [IsRegularLocalRing R] {Z J : Finset R}
    (hZ : IsRegularSystemOfParameters R Z) (hJ : J ⊆ Z) {p : Ideal R} [p.IsPrime]
    (hp1 : p.height = 1) (hle : Ideal.span {∏ z ∈ J, z} ≤ p) :
    ∃ a ∈ J, p = Ideal.span {a} := by
  have := isDomain_of_isRegularLocalRing R
  have hmem : ∏ z ∈ J, z ∈ p := hle (Ideal.mem_span_singleton_self _)
  obtain ⟨a, ha, hap⟩ := Ideal.IsPrime.prod_mem_iff.mp hmem
  have hext := (ExtendsToRSOP.of_isRegularSystemOfParameters hZ).mono hJ
  have := hext.isPrime_span_singleton ha
  refine ⟨a, ha, (Hironaka.DatumTransform.eq_of_le_of_height_eq_one ((Ideal.span_singleton_le_iff_mem _).mpr hap) ?_
    hp1).symm⟩
  rw [Ne, Ideal.span_singleton_eq_bot]
  exact hext.ne_zero ha

theorem _root_.Hironaka.DatumTransform.height_span_singleton_of_mem {R : Type u} [CommRing R] [IsRegularLocalRing R]
    {K : Finset R} (hK : ExtendsToRSOP R K) {j : R} (hj : j ∈ K) :
    (Ideal.span {j}).height = 1 := by
  have := (hK.mono (Finset.singleton_subset_iff.mpr hj)).height_span_prod
    (Finset.singleton_nonempty j)
  rwa [Finset.prod_singleton] at this

/-- "Similarly for the others" (p. 169): from a regular system of parameters `Z₁` adapted to
some principal primes `(j)`, `j ∈ J`, and to `B = (T)`, and another one `Z₂` adapted to the
`(j)` and to a principal prime `(f) ⊆ B`, one obtains a regular system of parameters adapted to
all of them at once (`ExtendsToRSOP.exchange`). -/
theorem _root_.Hironaka.DatumTransform.exists_rsop_exchange {R : Type u} [CommRing R] [IsRegularLocalRing R] {Z₁ Z₂ T J : Finset R}
    (hZ₁ : IsRegularSystemOfParameters R Z₁) (hZ₂ : IsRegularSystemOfParameters R Z₂)
    (hTZ : T ⊆ Z₁) (hJZ : J ⊆ Z₁) {f : R} (hf : f ∈ Z₂)
    (hfT : f ∈ Ideal.span (T : Set R))
    (hJw : ∀ j ∈ J, ∃ w ∈ Z₂, Ideal.span {j} = Ideal.span {w}) :
    ∃ Z' : Finset R, IsRegularSystemOfParameters R Z' ∧ J ⊆ Z' ∧
      (∃ a ∈ Z', Ideal.span {a} = Ideal.span {f}) ∧
      ∃ T' ⊆ Z', Ideal.span (T' : Set R) = Ideal.span (T : Set R) := by
  have := isDomain_of_isRegularLocalRing R
  by_cases hc : ∃ j ∈ J, Ideal.span {j} = Ideal.span {f}
  · obtain ⟨j, hj, hjf⟩ := hc
    exact ⟨Z₁, hZ₁, hJZ, ⟨j, hJZ hj, hjf⟩, T, hTZ, rfl⟩
  push Not at hc
  have hfJ : f ∉ J := fun h => hc f h rfl
  have hinj₁ := (ExtendsToRSOP.of_isRegularSystemOfParameters hZ₁).span_singleton_injOn
  have hinj₂ := (ExtendsToRSOP.of_isRegularSystemOfParameters hZ₂).span_singleton_injOn
  let g : R → R := fun v =>
    if h : v ≠ f ∧ ∃ j ∈ J, Ideal.span {j} = Ideal.span {v} then h.2.choose else v
  have hg_spec : ∀ v, Ideal.span {g v} = Ideal.span {v} := by
    intro v
    by_cases h : v ≠ f ∧ ∃ j ∈ J, Ideal.span {j} = Ideal.span {v}
    · have : g v = h.2.choose := dite_eq_left_of_eq_true (eq_true h)
      rw [this]
      exact h.2.choose_spec.2
    · have : g v = v := dite_eq_right_of_eq_false (eq_false h)
      rw [this]
  let L := Z₂.filter fun v => v = f ∨ ∃ j ∈ J, Ideal.span {j} = Ideal.span {v}
  have hL : ExtendsToRSOP R L :=
    (ExtendsToRSOP.of_isRegularSystemOfParameters hZ₂).mono (Finset.filter_subset _ _)
  have hginj : Set.InjOn g (L : Set R) := by
    intro v₁ h₁ v₂ h₂ h
    have h₁' := (Finset.mem_filter.mp h₁).1
    have h₂' := (Finset.mem_filter.mp h₂).1
    apply hinj₂ h₁' h₂'
    show Ideal.span {v₁} = Ideal.span {v₂}
    rw [← hg_spec v₁, ← hg_spec v₂, h]
  have hassoc : ∀ v ∈ L, Associated v (g v) := fun v _ =>
    Ideal.span_singleton_eq_span_singleton.mp (hg_spec v).symm
  have himage : L.image g = insert f J := by
    ext a
    simp only [Finset.mem_image, Finset.mem_insert]
    constructor
    · rintro ⟨v, hv, rfl⟩
      by_cases h : v ≠ f ∧ ∃ j ∈ J, Ideal.span {j} = Ideal.span {v}
      · have : g v = h.2.choose := dite_eq_left_of_eq_true (eq_true h)
        rw [this]
        exact Or.inr h.2.choose_spec.1
      · have : g v = v := dite_eq_right_of_eq_false (eq_false h)
        rw [this]
        obtain ⟨-, hv2⟩ := Finset.mem_filter.mp hv
        rcases hv2 with hvf | hj
        · exact Or.inl hvf
        · by_cases hvf : v = f
          · exact Or.inl hvf
          · exact absurd ⟨hvf, hj⟩ h
    · rintro (rfl | ha)
      · refine ⟨a, Finset.mem_filter.mpr ⟨hf, Or.inl rfl⟩, ?_⟩
        exact dite_eq_right_of_eq_false (eq_false (fun h => h.1 rfl))
      · obtain ⟨w, hw, hjw⟩ := hJw a ha
        have hwf : w ≠ f := by
          rintro rfl
          exact hc a ha hjw
        refine ⟨w, Finset.mem_filter.mpr ⟨hw, Or.inr ⟨a, ha, hjw⟩⟩, ?_⟩
        have hh : w ≠ f ∧ ∃ j ∈ J, Ideal.span {j} = Ideal.span {w} := ⟨hwf, a, ha, hjw⟩
        have : g w = hh.2.choose := dite_eq_left_of_eq_true (eq_true hh)
        rw [this]
        apply hinj₁ (hJZ hh.2.choose_spec.1) (hJZ ha)
        show Ideal.span {hh.2.choose} = Ideal.span {a}
        rw [hh.2.choose_spec.2, hjw]
  have hext : ExtendsToRSOP R (insert f J) := by
    rw [← himage]
    exact hL.image_of_associated g hginj hassoc
  obtain ⟨Z', T', hZ', hJZ', hfZ', hT'Z', hT'⟩ :=
    ExtendsToRSOP.exchange hZ₁ hJZ hTZ hfT hfJ hext
  exact ⟨Z', hZ', hJZ', ⟨f, hfZ', rfl⟩, T', hT'Z', hT'⟩

/-- If `D` is reduced and `D ⊆ F` as sets, then `F_x ⊆ D_x`. -/
theorem _root_.Hironaka.DatumTransform.stalkIdeal_le_of_pts_subset {D F : Subscheme X} (hD : D.IsReduced)
    (h : D.pts ⊆ F.pts) (x : X) : F.stalkIdeal x ≤ D.stalkIdeal x := by
  apply Subscheme.stalkIdeal_mono
  rw [Subscheme.eq_ofClosed_support D hD]
  exact Scheme.IdealSheafData.le_support_iff_le_vanishingIdeal.mp h

theorem _root_.Hironaka.DatumTransform.isReduced_of_isNonsingular {D : Subscheme X} (hD : D.IsNonsingular) : D.IsReduced :=
  Subscheme.isReduced_of_stalk_quot D fun z hz => by
    have := Subscheme.isRegular_stalk_quot D hD hz
    have := isDomain_of_isRegularLocalRing (X.presheaf.stalk z ⧸ D.stalkIdeal z)
    infer_instance

theorem _root_.Hironaka.Subscheme.IsNonsingularIrreducibleCodimOne.isNonsingular {F : Subscheme X}
    (hF : F.IsNonsingularIrreducibleCodimOne) : F.IsNonsingular := by
  rcases hF with rfl | h
  · exact Subscheme.isNonsingular_empty
  · exact h.1

/-- Regular systems of parameters adapted to `E`, `F` and `B` at every point (type I with
closed restriction, p. 169). -/
theorem _root_.Hironaka.DatumTransform.exists_rsop_adapted_of_isClosedRestriction_datumI (hX : X.IsNonsingular) {E F : Subscheme X} (hEred : E.IsReduced)
    (hE : ∀ x, E.HasOnlyNormalCrossingsAt x)
    (hEB : ∀ x ∈ B.pts, E.HasOnlyNormalCrossingsWithAt B x)
    (hF : F.IsNonsingularIrreducibleCodimOne) (hEF : (E.union F).HasOnlyNormalCrossings)
    (hBred : B.IsReduced) (hBF : B.pts ⊆ F.pts) (x : X) :
    ∃ Z : Finset (X.presheaf.stalk x), IsRegularSystemOfParameters _ Z ∧
      (x ∈ B.pts → ∃ T ⊆ Z, B.stalkIdeal x = Ideal.span (T : Set _)) ∧
      (∃ J ⊆ Z, E.stalkIdeal x = Ideal.span {∏ z ∈ J, z}) ∧
      (∃ J ⊆ Z, J.card ≤ 1 ∧ F.stalkIdeal x = Ideal.span {∏ z ∈ J, z}) := by
  have : IsRegularLocalRing (X.presheaf.stalk x) := hX x
  have := isDomain_of_isRegularLocalRing (X.presheaf.stalk x)
  obtain ⟨Z₁, hZ₁, ⟨J₁, hJ₁Z, hJ₁⟩, hT₁⟩ : ∃ Z₁ : Finset (X.presheaf.stalk x),
      IsRegularSystemOfParameters _ Z₁ ∧
      (∃ J ⊆ Z₁, E.stalkIdeal x = Ideal.span {∏ z ∈ J, z}) ∧
      (x ∈ B.pts → ∃ T ⊆ Z₁, B.stalkIdeal x = Ideal.span (T : Set _)) := by
    by_cases hx : x ∈ B.pts
    · obtain ⟨Z, hZ, hJ, hT⟩ :=
        (Subscheme.hasOnlyNormalCrossingsWithAt_iff hEred (hX x)).mp (hEB x hx)
      exact ⟨Z, hZ, hJ, fun _ => hT⟩
    · obtain ⟨Z, hZ, hJ, -⟩ := (Subscheme.hasOnlyNormalCrossingsWithAt_iff hEred (hX x)).mp (hE x)
      exact ⟨Z, hZ, hJ, fun h => absurd h hx⟩
  by_cases hxF : x ∉ F.pts
  · refine ⟨Z₁, hZ₁, hT₁, ⟨J₁, hJ₁Z, hJ₁⟩, ⟨∅, Finset.empty_subset _, by simp, ?_⟩⟩
    rw [Subscheme.stalkIdeal_eq_top_of_notMem_pts hxF, Finset.prod_empty,
      Ideal.span_singleton_one]
  push Not at hxF
  have hFne : F ≠ Subscheme.empty := by
    rintro rfl
    rw [Hironaka.DatumTransform.pts_empty] at hxF
    exact hxF
  obtain ⟨hFns, hFirr, hFcod⟩ := hF.resolve_left hFne
  have hFp : (F.stalkIdeal x).IsPrime := Subscheme.isPrime_stalkIdeal_of_isNonsingular_of_mem_pts _ hFns hxF
  have hF1 : (F.stalkIdeal x).height = 1 := by
    rw [← Subscheme.codim_eq_height _ hFns hFirr hxF, hFcod]
  have hEFred : (E.union F).IsReduced := Subscheme.isReduced_of_isRadical_stalkIdeal fun z => by
    rw [Subscheme.union, Subscheme.stalkIdeal_inf_eq]
    exact (Subscheme.isRadical_stalkIdeal_of_isReduced hEred z).inf
      (Subscheme.isRadical_stalkIdeal_of_isReduced (Hironaka.DatumTransform.isReduced_of_isNonsingular hFns) z)
  obtain ⟨Z₂, hZ₂, ⟨J₂, hJ₂Z, hJ₂⟩, -⟩ :=
    (Subscheme.hasOnlyNormalCrossingsWithAt_iff hEFred (hX x)).mp (hEF x)
  have hleE : (E.union F).stalkIdeal x ≤ E.stalkIdeal x := by
    rw [Subscheme.union, Subscheme.stalkIdeal_inf_eq]; exact inf_le_left
  have hleF : (E.union F).stalkIdeal x ≤ F.stalkIdeal x := by
    rw [Subscheme.union, Subscheme.stalkIdeal_inf_eq]; exact inf_le_right
  obtain ⟨a, haJ, hFa⟩ := Hironaka.DatumTransform.eq_span_of_prod_le hZ₂ hJ₂Z hF1 (hJ₂ ▸ hleF)
  have hext₁ := (ExtendsToRSOP.of_isRegularSystemOfParameters hZ₁).mono hJ₁Z
  have hJw : ∀ j ∈ J₁, ∃ w ∈ Z₂, Ideal.span {j} = Ideal.span {w} := by
    intro j hj
    have := hext₁.isPrime_span_singleton hj
    have hle : Ideal.span {∏ z ∈ J₂, z} ≤ Ideal.span {j} := by
      rw [← hJ₂]
      refine hleE.trans ?_
      rw [hJ₁, ← hext₁.iInf_span_singleton]
      exact iInf₂_le j hj
    obtain ⟨w, hw, hjw⟩ :=
      Hironaka.DatumTransform.eq_span_of_prod_le hZ₂ hJ₂Z (Hironaka.DatumTransform.height_span_singleton_of_mem hext₁ hj) hle
    exact ⟨w, hJ₂Z hw, hjw⟩
  by_cases hxB : x ∈ B.pts
  · obtain ⟨T, hTZ, hT⟩ := hT₁ hxB
    have hfT : a ∈ Ideal.span (T : Set _) := by
      rw [← hT]
      apply Hironaka.DatumTransform.stalkIdeal_le_of_pts_subset hBred hBF x
      rw [hFa]
      exact Ideal.mem_span_singleton_self a
    obtain ⟨Z', hZ', hJZ', ⟨a', ha'Z, ha'⟩, T', hT'Z, hT'⟩ :=
      Hironaka.DatumTransform.exists_rsop_exchange hZ₁ hZ₂ hTZ hJ₁Z (hJ₂Z haJ) hfT hJw
    refine ⟨Z', hZ', fun _ => ⟨T', hT'Z, by rw [hT, hT']⟩, ⟨J₁, hJZ', hJ₁⟩,
      ⟨{a'}, Finset.singleton_subset_iff.mpr ha'Z, by simp, ?_⟩⟩
    rw [Finset.prod_singleton, ha', hFa]
  · refine ⟨Z₂, hZ₂, fun h => absurd h hxB,
      ⟨Z₂.filter fun v => ∃ j ∈ J₁, Ideal.span {j} = Ideal.span {v},
        Finset.filter_subset _ _, ?_⟩,
      ⟨{a}, Finset.singleton_subset_iff.mpr (hJ₂Z haJ), by simp, by
        rw [Finset.prod_singleton, hFa]⟩⟩
    rw [hJ₁, ← hext₁.iInf_span_singleton, ← ((ExtendsToRSOP.of_isRegularSystemOfParameters
      hZ₂).mono (Finset.filter_subset _ _)).iInf_span_singleton]
    apply le_antisymm
    · refine le_iInf₂ fun v hv => ?_
      obtain ⟨j, hj, hjv⟩ := (Finset.mem_filter.mp hv).2
      exact (iInf₂_le j hj).trans hjv.le
    · refine le_iInf₂ fun j hj => ?_
      obtain ⟨w, hw, hjw⟩ := hJw j hj
      exact (iInf₂_le w (Finset.mem_filter.mpr ⟨hw, j, hj, hjw⟩)).trans hjw.ge

/-- Regular systems of parameters adapted to the `Eᵢ`, `F` and `B` at every point (type II with
closed restriction, p. 169). -/
theorem _root_.Hironaka.DatumTransform.exists_rsop_adapted_of_isClosedRestriction_datumII (hX : X.IsNonsingular) {α : ℕ} (E : Fin α → Subscheme X)
    (hE : ∀ i, (E i).IsNonsingularIrreducibleCodimOne)
    (hNCB : (⨅ i, E i).HasOnlyNormalCrossingsWith B) {F : Subscheme X}
    (hF : F.IsNonsingularIrreducibleCodimOne)
    (hEF : ((⨅ i, E i).union F).HasOnlyNormalCrossings)
    (hBred : B.IsReduced) (hBF : B.pts ⊆ F.pts) (x : X) :
    ∃ Z : Finset (X.presheaf.stalk x), IsRegularSystemOfParameters _ Z ∧
      (x ∈ B.pts → ∃ T ⊆ Z, B.stalkIdeal x = Ideal.span (T : Set _)) ∧
      ∀ o : Option (Fin α), (o.elim F E).stalkIdeal x = ⊤ ∨
        ∃ a ∈ Z, (o.elim F E).stalkIdeal x = Ideal.span {a} := by
  have : IsRegularLocalRing (X.presheaf.stalk x) := hX x
  have hG : ∀ o : Option (Fin α), (o.elim F E).IsNonsingularIrreducibleCodimOne := by
    rintro (_ | i)
    exacts [hF, hE i]
  have hGle : ∀ o : Option (Fin α), ((⨅ i, E i).union F) ≤ o.elim F E := by
    rintro (_ | i)
    · exact inf_le_right
    · exact inf_le_left.trans (iInf_le _ i)
  obtain ⟨Z₂, hZ₂, -, hG₂⟩ :=
    Hironaka.DatumTransform.exists_rsop_of_hasOnlyNormalCrossingsWithAt _ hG hGle (D := ⊥) (hEF x)
  by_cases hxB : x ∈ B.pts
  · obtain ⟨Z₁, hZ₁, ⟨T, hTZ, hT⟩, hE₁⟩ :=
      Hironaka.DatumTransform.exists_rsop_of_hasOnlyNormalCrossingsWithAt E hE (fun i => iInf_le _ i) (hNCB x hxB)
    have hxF := hBF hxB
    obtain ⟨f, hfZ, hFf⟩ := (hG₂ none).resolve_left
      (Subscheme.mem_pts_iff_stalkIdeal_ne_top.mp hxF)
    change F.stalkIdeal x = _ at hFf
    have hJw : ∀ j ∈ Z₁.filter (fun j => ∃ i, (E i).stalkIdeal x = Ideal.span {j}),
        ∃ w ∈ Z₂, Ideal.span {j} = Ideal.span {w} := by
      intro j hj
      obtain ⟨hjZ, i, hi⟩ := Finset.mem_filter.mp hj
      rcases hG₂ (some i) with h | ⟨w, hw, hwi⟩
      · exfalso
        change (E i).stalkIdeal x = ⊤ at h
        rw [hi, Ideal.span_singleton_eq_top] at h
        have hjm : j ∈ maximalIdeal (X.presheaf.stalk x) := hZ₁.1 ▸ Ideal.subset_span hjZ
        exact (mem_maximalIdeal j).mp hjm h
      · exact ⟨w, hw, hi.symm.trans hwi⟩
    have hfT : f ∈ Ideal.span (T : Set _) := by
      rw [← hT]
      apply Hironaka.DatumTransform.stalkIdeal_le_of_pts_subset hBred hBF x
      rw [hFf]
      exact Ideal.mem_span_singleton_self f
    obtain ⟨Z', hZ', hJZ', ⟨a, haZ, ha⟩, T', hT'Z, hT'⟩ :=
      Hironaka.DatumTransform.exists_rsop_exchange hZ₁ hZ₂ hTZ (Finset.filter_subset _ _) hfZ hfT hJw
    refine ⟨Z', hZ', fun _ => ⟨T', hT'Z, by rw [hT, hT']⟩, ?_⟩
    rintro (_ | i)
    · exact Or.inr ⟨a, haZ, by rw [Option.elim_none, hFf, ha]⟩
    · rcases hE₁ i with h | ⟨j, hj, hji⟩
      · exact Or.inl h
      · exact Or.inr ⟨j, hJZ' (Finset.mem_filter.mpr ⟨hj, i, hji⟩), hji⟩
  · exact ⟨Z₂, hZ₂, fun h => absurd h hxB, hG₂⟩

/-- The monoidal transformation is an isomorphism over `X − B` (p. 167): a lift `j'` of the open
immersion `X − B → X`, with image `X' − f⁻¹(B)`. -/
theorem _root_.Hironaka.DatumTransform.exists_flat_isPreimmersion_off_center (t : MonoidalTransformation X B) :
    ∃ (Z : Scheme.{u}) (ι : Z ⟶ X) (j' : Z ⟶ t.X'), Flat ι ∧ IsPreimmersion ι ∧ Flat j' ∧
      IsPreimmersion j' ∧ IsOpenMap ι.base ∧ (∀ v, t.f (j' v) = ι v) ∧
      Set.range ι.base = B.ptsᶜ ∧ Set.range j'.base = t.exceptional.ptsᶜ ∧
      Subscheme.totalTransform j' t.exceptional = Subscheme.empty ∧
      ∀ V, Subscheme.totalTransform j' (Subscheme.strictTransform t V) =
        Subscheme.totalTransform ι V := by
  let U : X.Opens := ⟨B.ptsᶜ, B.support.isClosed.isOpen_compl⟩
  have hdisj : ∀ z : (U : Scheme), U.ι z ∉ B.pts := fun z =>
    (U.ι_apply z ▸ z.2 : _)
  obtain ⟨j', h1, h2, hj'f, hrange, hexc, htt⟩ := t.exists_lift_of_disjoint U.ι hdisj
  have hcomp : ∀ v, t.f (j' v) = U.ι v := fun v => by rw [← Scheme.Hom.comp_apply, hj'f]
  have hrU : Set.range U.ι.base = B.ptsᶜ := Scheme.Opens.range_ι U
  refine ⟨U, U.ι, j', inferInstance, inferInstance, h1, h2, U.ι.isOpenEmbedding.isOpenMap,
    hcomp, hrU, ?_, hexc, htt⟩
  rw [hrange, hrU, MonoidalTransformation.pts_exceptional]
  rfl

theorem _root_.Hironaka.DatumTransform.mem_closure_of_notMem_exceptional (t : MonoidalTransformation X B) {A : Set X}
    {q : t.X'} (hq : q ∉ t.exceptional.pts) (hA : t.f q ∈ closure A) :
    q ∈ closure (t.f.base ⁻¹' A \ t.exceptional.pts) := by
  obtain ⟨Z, ι, j', -, -, -, -, hopen, hcomp, -, hrange, -, -⟩ := Hironaka.DatumTransform.exists_flat_isPreimmersion_off_center t
  have hqr : q ∈ Set.range j'.base := by rw [hrange]; exact hq
  obtain ⟨u, rfl⟩ := hqr
  have hu : u ∈ closure (ι.base ⁻¹' A) := by
    rw [← hopen.preimage_closure_eq_closure_preimage ι.base.hom.continuous]
    show ι u ∈ closure A
    rw [← hcomp]
    exact hA
  refine closure_mono ?_ (image_closure_subset_closure_image j'.base.hom.continuous ⟨u, hu, rfl⟩)
  rintro _ ⟨v, hv, rfl⟩
  refine ⟨show t.f (j' v) ∈ A by rw [hcomp]; exact hv, ?_⟩
  change j' v ∉ t.exceptional.pts
  rw [← Set.mem_compl_iff, ← hrange]
  exact ⟨v, rfl⟩

/-- Points of a strict transform are limits of points off the exceptional subscheme. -/
theorem _root_.Hironaka.DatumTransform.mem_closure_of_mem_strictTransform (t : MonoidalTransformation X B) {V : Subscheme X}
    {A : Set X} (hVA : V.pts ⊆ closure A) {S : Set t.X'}
    (hS : t.f.base ⁻¹' A \ t.exceptional.pts ⊆ S) {p : t.X'}
    (hp : p ∈ (Subscheme.strictTransform t V).pts) : p ∈ closure S := by
  obtain ⟨q, hq, hqE, hqp⟩ := t.exists_generization_notMem_exceptional V hp
  have h1 := Hironaka.DatumTransform.mem_closure_of_notMem_exceptional t hqE (hVA (t.pts_strictTransform_subset V hq))
  have h2 : q ∈ closure S := closure_mono hS h1
  exact closure_minimal (Set.singleton_subset_iff.mpr h2) isClosed_closure
    (specializes_iff_mem_closure.mp hqp)

end Remark1

/-! ### Remark 1 (p. 169): dimension of the transformed scheme -/

/-- Remark 1, p. 169: "Then we have `dim(X') = dim(X) = N`, unless `X = B`. If `X = B`, then `X'`
is the empty algebraic scheme."  For `X` as in Definition 3 (non-singular irreducible algebraic)
and a center `B ≠ X`, `X'` is again irreducible of the same dimension.

Deviation from the paper (statement modified): permissibility of `B` is not assumed (only that
`B` is a center different from `X`), and the conclusions "algebraic, non-singular,
irreducible" (asserted by the paper on pp. 164, 167) are included.  The following sentences of the remark are
the separate declarations `MonoidalTransformation.isEmpty_of_pts_eq_univ` ("If `X = B`, then `X'` is the empty
algebraic scheme"), `DatumII.Raw.pts_ne_univ_of_isPermissible` and `DatumI.Raw.eq_bot_of_isPermissible_of_pts_eq_univ`
("This can happen only if `ℜ = ℜ_I` and `X = V_i = W` …") and `DatumI.Raw.resolvedEverywhere_of_eq_bot`
(`Hironaka/Compat/RemarkOneDim.lean`, "clearly resolved everywhere").  Deviation from the paper (gap filled): the
paper gives no proof; `Hironaka/Compat/BlowupDim.lean` supplies one. -/
@[blueprint "rem:I.1-dim"
  (statement := /-- Let $X$ be a non-singular irreducible algebraic scheme and $f\colon X'\to X$
    the monoidal transformation with a center $B$ (\cref{def:I.6-I}) with $B\ne X$. Then $X'$ is a
    non-singular irreducible algebraic scheme and $\dim(X')=\dim(X)$. (Remark~1, p.~169.)

    \textbf{Deviation from the paper (statement modified).} Permissibility of $B$ is not
    assumed (only $B\ne X$), and the conclusions ``algebraic, non-singular, irreducible''
    (asserted by the paper on pp.~164 and~167) are included. The paper's next sentences, ``If
    $X=B$, then $X'$ is the empty algebraic scheme. This can happen only if
    $\mathfrak R=\mathfrak R^{N,n}_{\mathrm I}$ \dots\ and $X=V_i=W$ for all $i$, in which case the
    datum is clearly resolved everywhere'', are
    \cref{rem:I.1-dim-empty}, \cref{rem:I.1-dim-typeII}, \cref{rem:I.1-dim-typeI} and
    \cref{rem:I.1-dim-resolved}. -/)
  (proof := /-- $X'$ is algebraic since $f$ is proper
    (\cref{lem:monoidal-transformation-proper}), non-singular by
    \cref{lem:monoidal-transformation-nonsingular}, and irreducible of dimension $\dim X$ by
    \cref{compat:blowup-dim}.

    \textbf{Gap in the paper filled.} The paper states $\dim(X')=\dim(X)$ without proof; the
    argument of \cref{compat:blowup-dim} is ours and uses the local theory of Ch.~III \S2
    ($\dim R'\le\dim R$ for a monoidal transform, \cref{lem:III.2-dim}). -/)
  (latexEnv := "remark")]
theorem MonoidalTransformation.transform_isAmbient [Hironaka.Cited.MonoidalTransformationExistsIsProper.{u}] {X : Scheme.{u}} [IsAlgebraicScheme X]
    [IrreducibleSpace X] (hX : X.IsNonsingular) {B : Subscheme X} (hB : B.IsCenter)
    (hBX : B.pts ≠ Set.univ) (t : MonoidalTransformation X B) :
    IsAlgebraicScheme t.X' ∧ t.X'.IsNonsingular ∧ IrreducibleSpace t.X' ∧ t.X'.dim = X.dim := by
  have := t.isAlgebraicScheme
  obtain ⟨h1, h2⟩ := t.irreducibleSpace_and_dim_eq hX hB.isNonsingular hBX
  exact ⟨this, (t.isNonsingular_and_isNonsingular_exceptional hX hB.isNonsingular).1, h1, h2⟩

/-! #### The case `X = B` of Remark 1 (p. 169)

"If `X = B`, then `X'` is the empty algebraic scheme.  This can happen only if `ℜ = ℜ_I^{N,n}` (as in
Definition 3) and `X = V_i = W` for all `i`, in which case the datum `ℜ_I^{N,n}` is clearly resolved
everywhere.  We exclude once for always this uninteresting case in which `X = W`." (p. 169)

"`X = B`" is read as `B = ⊥` (the subscheme `B` is `X`, its ideal sheaf is zero), which for a
non-singular `X` (reduced) is the same as `B.pts = univ`. -/

namespace Subscheme

variable {X : Scheme.{u}}

/-- The subscheme `X` itself (zero ideal sheaf) of a non-singular scheme is reduced. -/
theorem isReduced_bot_of_isNonsingular (hX : X.IsNonsingular) : (⊥ : Subscheme X).IsReduced :=
  isReduced_of_isRadical_stalkIdeal fun x => by
    have : IsRegularLocalRing (X.presheaf.stalk x) := hX x
    have := isDomain_of_isRegularLocalRing (X.presheaf.stalk x)
    rw [stalkIdeal_bot_eq]
    exact Ideal.isRadical_bot

/-- On a non-singular scheme a subscheme with all points has zero ideal at every point. -/
theorem stalkIdeal_eq_bot_of_pts_eq_univ (hX : X.IsNonsingular) {B : Subscheme X}
    (hB : B.pts = Set.univ) (x : X) : B.stalkIdeal x = ⊥ := by
  have hbot : (⊥ : Subscheme X).pts = Set.univ := by
    change ((⊥ : Scheme.IdealSheafData X).support : Set X) = _
    rw [Scheme.IdealSheafData.support_bot]
    rfl
  have := Hironaka.DatumTransform.stalkIdeal_le_of_pts_subset (F := B)
    (isReduced_bot_of_isNonsingular hX) (by rw [hbot, hB]) x
  rw [stalkIdeal_bot_eq] at this
  exact le_bot_iff.mp this

/-- On a non-singular scheme a subscheme with all points is the whole scheme (`B = X`). -/
theorem eq_bot_of_pts_eq_univ (hX : X.IsNonsingular) {B : Subscheme X} (hB : B.pts = Set.univ) :
    B = ⊥ :=
  ext_stalkIdeal fun x => by rw [stalkIdeal_eq_bot_of_pts_eq_univ hX hB, stalkIdeal_bot_eq]

end Subscheme

/-- Remark 1 (p. 169): "If `X = B`, then `X'` is the empty algebraic scheme."

Deviation from the paper (gap filled): the paper gives no argument.  Here: `B = X` means that the ideal
sheaf of `B` is zero, so is its total transform, which must be an invertible ideal sheaf; a zero ideal
generated by a non-zero-divisor forces the local rings of `X'` to be zero. -/
@[blueprint "rem:I.1-dim-empty"
  (statement := /-- Let $X$ be a non-singular algebraic scheme and $f\colon X'\to X$ the monoidal
    transformation with center $B=X$. Then $X'$ is the empty algebraic scheme. (Remark~1, p.~169.)
    \textbf{Gap in the paper filled.} The sentence is printed without proof. -/)
  (proof := /-- The ideal sheaf of $B=X$ is zero, hence so is its total transform
    $f^{-1}(B)$, which is invertible; a zero ideal generated by a non-zero-divisor forces
    $\mathcal O_{X',y}=0$ for every $y\in X'$, which is impossible. -/)
  (latexEnv := "lemma")]
theorem MonoidalTransformation.isEmpty_of_pts_eq_univ [Hironaka.Cited.MonoidalTransformationExistsIsProper.{u}] {X : Scheme.{u}} [IsAlgebraicScheme X]
    (hX : X.IsNonsingular) {B : Subscheme X} (hB : B.pts = Set.univ)
    (t : MonoidalTransformation X B) : IsAlgebraicScheme t.X' ∧ IsEmpty t.X' := by
  have := t.isAlgebraicScheme
  refine ⟨this, ⟨fun y => ?_⟩⟩
  obtain ⟨g, hg, hnzd⟩ := Subscheme.IsInvertibleIdeal.exists_stalkIdeal_eq_span t.invertible y
  have h0 : (Subscheme.totalTransform t.f B).stalkIdeal y = ⊥ := by
    rw [stalkIdeal_totalTransform, Subscheme.stalkIdeal_eq_bot_of_pts_eq_univ hX hB, Ideal.map_bot]
  rw [h0] at hg
  have hg0 : g = 0 := by
    have : g ∈ (⊥ : Ideal (t.X'.presheaf.stalk y)) := by rw [hg]; exact Ideal.mem_span_singleton_self g
    exact (Ideal.mem_bot).mp this
  rw [hg0] at hnzd
  exact zero_notMem_nonZeroDivisors hnzd

/-- Remark 1 (p. 169): "This can happen only if `ℜ = ℜ_I^{N,n}` (as in Definition 3)": for a datum of
type II on a non-singular irreducible scheme, a permissible center is never all of `X`: the generic
point of `X` is not in `S(ℜ)` (`∑_{η ∈ E_i} a_i = 0` as the `E_i` have codimension one, and
`ν(J_η) = 0` as `O_{X,η}` is a field and `J_η ≠ 0`), whereas `B ⊆ S*(ℜ) ⊆ S(ℜ)` and `b > 0`.

Deviation from the paper (gap filled): the paper gives no argument. -/
@[blueprint "rem:I.1-dim-typeII"
  (statement := /-- Let $\mathfrak R$ be a resolution datum of type $\mathfrak R^N_{\mathrm{II}}$ on a
    non-singular irreducible algebraic scheme $X$ and $B$ a center permissible for $\mathfrak R$. Then
    $B\ne X$. (Remark~1, p.~169: $X=B$ ``can happen only if $\mathfrak R=\mathfrak R^{N,n}_{\mathrm I}$''.)
    \textbf{Gap in the paper filled.} The paper gives no argument for this remark. -/)
  (proof := /-- If $B=X$, the generic point $\eta$ of $X$ lies in $B\subseteq S(\mathfrak R)$, so
    $b\le\sum_{\eta\in E_i}a_i+\nu(J_\eta)$. No $E_i$ (empty or of codimension one) contains $\eta$, and
    $\mathcal O_{X,\eta}$ is a field, so $J_\eta\neq0$ is the unit ideal and $\nu(J_\eta)=0$:
    $b\le0$, contradicting $b>0$. -/)
  (latexEnv := "lemma")]
theorem DatumII.Raw.pts_ne_univ_of_isPermissible {X : Scheme.{u}} [IrreducibleSpace X]
    (hX : X.IsNonsingular) (ℜ : DatumII.Raw X) (hℜ : ℜ.IsDatum) {B : Subscheme X}
    (hB : ℜ.IsPermissible B) : B.pts ≠ Set.univ := by
  intro hBu
  have hdom : ∀ x : X, IsDomain (X.presheaf.stalk x) := fun x => by
    have : IsRegularLocalRing (X.presheaf.stalk x) := hX x
    exact isDomain_of_isRegularLocalRing _
  have : ∀ x : X, _root_.IsReduced (X.presheaf.stalk x) := fun x => by
    have := hdom x
    infer_instance
  have : AlgebraicGeometry.IsReduced X := AlgebraicGeometry.isReduced_of_isReduced_stalk _
  set η : X := genericPoint X with hη
  have hηcl : closure ({η} : Set X) = Set.univ := (genericPoint_spec X).def
  have hfield : IsField (X.presheaf.stalk η) :=
    AlgebraicGeometry.isField_stalk_of_closure_mem_irreducibleComponents X η
      (by rw [irreducibleComponents_eq_singleton, hηcl]; exact Set.mem_singleton _)
  have hηB : η ∈ B.pts := hBu ▸ Set.mem_univ η
  have hηS : η ∈ ℜ.sStar := hB.2.1 hηB
  -- no `E_i` contains `η` (an `E_i` through `η` is all of `X`, of codimension `0`, not `1`)
  have hE : ∀ i, η ∉ (ℜ.E i).pts := by
    intro i hηi
    rcases hℜ.2.1 i with h | ⟨-, -, hcod⟩
    · rw [h, DatumTransform.pts_empty] at hηi
      exact hηi
    · have hpts : (ℜ.E i).pts = Set.univ := by
        apply Set.eq_univ_of_univ_subset
        rw [← hηcl]
        exact (ℜ.E i).support.isClosed.closure_subset_iff.mpr (Set.singleton_subset_iff.mpr hηi)
      have hbot := Subscheme.stalkIdeal_eq_bot_of_pts_eq_univ hX hpts η
      have := hdom η
      have h0 : (ℜ.E i).codim ≤ 0 :=
        calc (ℜ.E i).codim ≤ (ℜ.E i).codimAt η := iInf₂_le η hηi
          _ = 0 := by
            rw [Subscheme.codimAt, hbot]
            exact Ideal.height_eq_zero_iff_eq_bot.mpr rfl
      rw [hcod] at h0
      exact absurd h0 (by norm_num)
  have hw : ℜ.weight η = 0 := by
    unfold DatumII.Raw.weight
    rw [Finset.sum_eq_zero]
    intro i hi
    exact absurd (Finset.mem_filter.mp hi).2 (hE i)
  -- `J_η` is a non-zero ideal of the field `O_{X,η}`, so `ν(J_η) = 0`
  have hJη : ℜ.J.stalkIdeal η = ⊤ := by
    let := hfield.toField
    exact (Ideal.eq_bot_or_top _).resolve_left (hℜ.2.2.2 η)
  have hνη : ℜ.nuAt η = 0 := by
    unfold DatumII.Raw.nuAt
    rw [hJη]
    have : ¬ (1 ≤ Ideal.nu (⊤ : Ideal (X.presheaf.stalk η))) := by
      rw [(Ideal.ord_basic (IsLocalRing.maximalIdeal (X.presheaf.stalk η)) ⊤ ⊤ ⊤).2.1]
      exact fun h => (IsLocalRing.maximalIdeal.isMaximal _).ne_top (top_le_iff.mp h)
    simpa [Order.lt_one_iff] using this
  have hS := hηS.1
  simp only [DatumII.Raw.S, Set.mem_ofPred_eq, hw, hνη] at hS
  have : ℜ.b = 0 := by exact_mod_cast le_antisymm (by simpa using hS) (Nat.zero_le _)
  exact absurd this hℜ.1.ne'

/-- Remark 1 (p. 169): "This can happen only if … `X = V_i = W` for all `i`": for a datum of type I
and a permissible center `B = X`, the principal subscheme and all the `V_j` are `X`.  (`B ⊆ W` and
`B ⊆ V_j` by Definition 3 (iii) for `(E; V_1, …, V_β, W; B)`.)

Deviation from the paper (gap filled): the paper gives no argument. -/
@[blueprint "rem:I.1-dim-typeI"
  (statement := /-- Let $\mathfrak R=(E;V_1,\dots,V_\beta;W)$ be a resolution datum of type
    $\mathfrak R^{N,n}_{\mathrm I}$ on a non-singular algebraic scheme $X$ and $B=X$ a permissible
    center. Then $W=X$ and $V_j=X$ for all $j$. (Remark~1, p.~169.)
    \textbf{Gap in the paper filled.} The paper gives no argument for this remark. -/)
  (proof := /-- $(E;V_1,\dots,V_\beta,W;B)$ is a datum, so $B\subseteq V_j$ and $B\subseteq W$; with
    $B=X$ (zero ideal sheaf) the ideal sheaves of $V_j$ and $W$ are zero. -/)
  (latexEnv := "lemma")]
theorem DatumI.Raw.eq_bot_of_isPermissible_of_pts_eq_univ {X : Scheme.{u}}
    (hX : X.IsNonsingular) (ℜ : DatumI.Raw X) {B : Subscheme X} (hB : ℜ.IsPermissible B)
    (hBu : B.pts = Set.univ) : ℜ.W = ⊥ ∧ ∀ j, ℜ.V j = ⊥ := by
  have hB0 : B = ⊥ := Subscheme.eq_bot_of_pts_eq_univ hX hBu
  have h := hB.2.1.2.2.2.2
  refine ⟨?_, fun j => ?_⟩
  · have := h (Fin.last ℜ.β)
    simp only [DatumI.Raw.extendBy, Fin.snoc_last] at this
    rw [hB0] at this
    exact le_bot_iff.mp (fun U => this U)
  · have := h (Fin.castSucc j)
    simp only [DatumI.Raw.extendBy, Fin.snoc_castSucc] at this
    rw [hB0] at this
    exact le_bot_iff.mp (fun U => this U)

/-! ### Definition 7: transforms of resolution data -/

namespace DatumI.Raw

variable {X : Scheme.{u}}



end DatumI.Raw

namespace DatumII.Raw

variable {X : Scheme.{u}}


/-! #### Twins of Definition 7 (type II): the exponent `a_{α+1}` as printed

The printed exponent is an integer that can be negative for the empty center; the corrected statement is `DatumII.Raw.transform` above.  The following results
record the statement as printed (false) and show that it fails, and that for non-empty
permissible centers the printed integer is `≥ 0`, so that Lean's truncation is harmless there. -/

/-- Definition 7 (type II) AS PRINTED: `a_{α+1} = (∑_{B ⊆ E_i} a_i) + ν − b`, computed in `ℤ`.

Statement as printed (false); see the corrected `DatumII.Raw.transform`: for the empty center (permissible for every datum by Def. 6) this integer can be
negative (`isPermissible_empty_and_printedExponent_eq_neg_one`), whereas Def. 3 (II)(i) requires
`a_i ≥ 0`. -/
@[blueprint "def:I.7-II-as-printed"
  (statement := /-- For a permissible monoidal transformation with center $B$, the integer
    $a_{\alpha+1}=\big(\sum_{B\subseteq E_i}a_i\big)+\nu-b$ of Definition~7, with
    $\nu=\nu(\mathfrak R)$,
    computed in $\mathbb Z$. (Def.\ 7, p.\ 168.)
    \textbf{Statement as printed (false); see the corrected statement \cref{def:I.7-II}.} -/)
  (latexEnv := "definition")]
noncomputable def printedExponent (ℜ : Raw X) (B : Subscheme X) : ℤ :=
  ((∑ i ∈ (Finset.univ.filter fun i => B.IsContainedIn (ℜ.E i)), ℜ.a i : ℕ) : ℤ)
    + (ℜ.nu.toNat : ℤ) - ℜ.b

/-- Lean's exponent `a_{α+1}` of `DatumII.Raw.transform` is the truncation to `ℕ` of the printed
integer. -/
theorem transform_a_last_eq_toNat_printedExponent (ℜ : Raw X) {B : Subscheme X}
    (t : MonoidalTransformation X B) :
    (ℜ.transform t).a (Fin.last ℜ.α) = (ℜ.printedExponent B).toNat := by
  simp only [transform, printedExponent, Fin.snoc_last]
  omega

/-- The orders `ν(J_x)` of the unit ideal sheaf vanish. -/
theorem nuAt_eq_zero_of_J_eq_top (ℜ : Raw X) (hJ : ℜ.J = ⊤) (x : X) : ℜ.nuAt x = 0 := by
  unfold Raw.nuAt
  rw [hJ, Subscheme.stalkIdeal_top_eq]
  have : ¬ (1 ≤ Ideal.nu (⊤ : Ideal (X.presheaf.stalk x))) := by
    rw [(Ideal.ord_basic (IsLocalRing.maximalIdeal (X.presheaf.stalk x)) ⊤ ⊤ ⊤).2.1]
    exact fun h => (IsLocalRing.maximalIdeal.isMaximal _).ne_top (top_le_iff.mp h)
  simpa [Order.lt_one_iff] using this

/-- Counterexample to the printed Definition 7 / Remark 1 (type II), p. 168–169: for `α = 0`,
`J = O_X` and `b = 1` the empty center is permissible (Def. 6: `B` may be empty, then the
transformation is permissible for any datum), `ν(ℜ) = 0`, and the printed exponent is `−1 < 0`.
So `f*(ℜ)` is not a resolution datum of type II as printed.

Statement as printed (false); see the corrected `DatumII.Raw.transform`. -/
@[blueprint "rem:I.1-as-printed-false"
  (statement := /-- Let $\mathfrak R=(\,\mid J,b\mid\,)$ be a datum of type
    $\mathfrak R^N_{\mathrm{II}}$ with
    $\alpha=0$, $J=\mathcal O_X$ the unit ideal sheaf and $b=1$. Then the empty center is
    permissible, $\nu(\mathfrak R)=0$, and the integer $a_{\alpha+1}$ of Definition~7 as printed
    equals
    $-1<0$, so $f^*(\mathfrak R)$ is not a resolution datum (contrary to Remark~1, p.~169).
    \textbf{Statement as printed (false); see the corrected statement \cref{def:I.7-II}.} -/)
  (proof := /-- The empty subscheme has no points, so the conditions of Definition~6 are vacuous.
    The order of the unit ideal in a local ring is $0$, so $S(\mathfrak R)=\emptyset$ and
    $\nu(\mathfrak R)=0$; with $\alpha=0$ the sum is empty and $a_1=0+0-1=-1$. -/)
  (latexEnv := "proposition")]
theorem isPermissible_empty_and_printedExponent_eq_neg_one (ℜ : Raw X) (hα : ℜ.α = 0)
    (hJ : ℜ.J = ⊤) (hb : ℜ.b = 1) :
    ℜ.IsPermissible Subscheme.empty ∧ ℜ.printedExponent Subscheme.empty = -1 := by
  have : IsEmpty (Fin ℜ.α) := by rw [hα]; infer_instance
  have hS : ℜ.S = ∅ := by
    ext x
    simp [Raw.S, Raw.weight, nuAt_eq_zero_of_J_eq_top ℜ hJ x, hb]
  have hnu : ℜ.nu = 0 := by simp [Raw.nu, hS]
  refine ⟨⟨Or.inl rfl, ?_, ?_⟩, ?_⟩
  · rw [DatumTransform.pts_empty]; exact Set.empty_subset _
  · intro x hx; rw [DatumTransform.pts_empty] at hx; exact absurd hx (Set.notMem_empty x)
  · simp [printedExponent, hnu, hb]

/-- Non-vacuity of `isPermissible_empty_and_printedExponent_eq_neg_one`: on every non-empty
non-singular `X` there is a
datum with `α = 0`, `J = O_X` and `b = 1`. -/
theorem exists_isDatum_of_J_eq_top (hX : X.IsNonsingular) [Nonempty X] :
    ∃ ℜ : Raw X, ℜ.IsDatum ∧ ℜ.α = 0 ∧ ℜ.J = ⊤ ∧ ℜ.b = 1 := by
  refine ⟨⟨0, Fin.elim0, Fin.elim0, ⊤, 1⟩, ⟨one_pos, fun i => i.elim0, ?_, ?_⟩, rfl, rfl, rfl⟩
  · intro x
    have : IsRegularLocalRing (X.presheaf.stalk x) := hX x
    obtain ⟨-, s, hs⟩ := (isRegularLocalRing_iff_exists_rsop (X.presheaf.stalk x)).mp this
    refine ⟨s, hs, ?_, ∅, Finset.empty_subset _, by simp [Subscheme.stalkIdeal_bot_eq]⟩
    rintro C ⟨Z, hZ, rfl⟩ hxC
    exfalso
    have hE : (Raw.eUnion (X := X) ⟨0, Fin.elim0, Fin.elim0, ⊤, 1⟩).pts = ∅ := by
      show (⨅ i : Fin 0, (Fin.elim0 i : Subscheme X)).pts = ∅
      rw [iInf_of_isEmpty, sInf_empty]; exact DatumTransform.pts_empty
    obtain ⟨z, hz⟩ := hZ.1.1.nonempty
    have := hZ.1.2 hz
    rw [hE] at this
    exact this
  · intro x
    have : IsRegularLocalRing (X.presheaf.stalk x) := hX x
    simp [Subscheme.stalkIdeal_top_eq]

/-- The spectrum of a field is non-singular. -/
theorem _root_.AlgebraicGeometry.Scheme.isNonsingular_spec_of_field (K : Type u) [Field K] :
    (Spec (CommRingCat.of K)).IsNonsingular := by
  intro x
  have hf : IsField ((Spec (CommRingCat.of K)).presheaf.stalk x) :=
    isField_stalk_of_closure_mem_irreducibleComponents _ x (by
      rw [irreducibleComponents_eq_singleton]
      refine Set.mem_singleton_iff.mpr (Set.eq_univ_of_forall fun z => ?_)
      have : Subsingleton (Spec (CommRingCat.of K)) :=
        inferInstanceAs (Subsingleton (PrimeSpectrum K))
      have : z = x := Subsingleton.elim z x
      exact subset_closure (by simp [this]))
  have : IsLocalRing ((Spec (CommRingCat.of K)).presheaf.stalk x) := inferInstance
  let := hf.toField
  show IsRegularLocalRing _
  infer_instance

/-- A concrete instance of `isPermissible_empty_and_printedExponent_eq_neg_one`: on `Spec K`,
`K` a field, the datum
`(\mid O_X, 1\mid)` exists, the empty center is permissible and the printed exponent is `−1`. -/
theorem exists_isDatum_isPermissible_empty_printedExponent_eq_neg_one (K : Type u) [Field K] :
    ∃ ℜ : Raw (Spec (CommRingCat.of K)), ℜ.IsDatum ∧
      ℜ.IsPermissible Subscheme.empty ∧ ℜ.printedExponent Subscheme.empty = -1 := by
  have : Nonempty (Spec (CommRingCat.of K)) := inferInstanceAs (Nonempty (PrimeSpectrum K))
  obtain ⟨ℜ, h, hα, hJ, hb⟩ := exists_isDatum_of_J_eq_top
    (_root_.AlgebraicGeometry.Scheme.isNonsingular_spec_of_field K)
  exact ⟨ℜ, h, isPermissible_empty_and_printedExponent_eq_neg_one ℜ hα hJ hb⟩

/-- For a non-empty permissible center the printed integer `a_{α+1}` is non-negative, so the
truncation in `DatumII.Raw.transform` changes nothing there.  Gap in the paper filled (p. 168 is
silent): at the generic point
`η` of `B ⊆ S_ν(ℜ)` one has
`∑_{η ∈ E_i} a_i + ν ≥ b`, and `η ∈ E_i` implies `B ⊆ E_i`.  (`ν(ℜ) < ∞` is
`DatumII.Raw.nu_ne_top`.) -/
@[blueprint "lem:I.7-II-exponent-nonneg"
  (statement := /-- Let $\mathfrak R$ be a resolution datum of type
    $\mathfrak R^N_{\mathrm{II}}$ on the
    non-singular algebraic scheme $X$ and $B\neq\emptyset$ a permissible center. Then
    $b\le\sum_{B\subseteq E_i}a_i+\nu(\mathfrak R)$, i.e.\ the integer $a_{\alpha+1}$ of
    Definition~7 is $\ge0$. Hence the truncated subtraction used in Lean agrees with the printed
    formula for non-empty centers. (Used in the discussion of Def.~7, p.~168.)
    \textbf{Gap in the paper filled.} The paper does not remark that $a_{\alpha+1}\ge0$ for
    non-empty $B$ (needed for Remark~1 as printed). -/)
  (proof := /-- Let $\eta$ be the generic point of $B$. Since $\eta\in S^*(\mathfrak R)$,
    $\sum_{\eta\in E_i}a_i+\nu\ge b$, and $\eta\in E_i$ implies $B\subseteq E_i$ because $B$ is
    reduced. -/)
  (latexEnv := "lemma")]
theorem printedExponent_nonneg_of_isPermissible [Hironaka.Cited.IsHironakaBaseIsClosedSingularLocus.{u}] [Hironaka.Cited.CurveFiniteIntegralClosure.{u}] [Hironaka.Cited.IsRegularLocalRingLocalizationOfIsRegularLocalRing.{u}] [IsAlgebraicScheme X] (hX : X.IsNonsingular)
    (ℜ : Raw X) (hℜ : ℜ.IsDatum) (B : Subscheme X) (hB : ℜ.IsPermissible B)
    (hne : B.pts.Nonempty) : 0 ≤ ℜ.printedExponent B := by
  have hBc : B.IsNonsingular ∧ B.IsIrreducible := by
    rcases hB.1 with h | h
    · exfalso; obtain ⟨z, hz⟩ := hne; rw [h, DatumTransform.pts_empty] at hz; exact hz
    · exact h
  have hBred : B.IsReduced := DatumTransform.isReduced_of_isNonsingular hBc.1
  have : IrreducibleSpace B.toScheme := hBc.2
  set η : B.toScheme := genericPoint B.toScheme
  set y : X := B.ι.base η with hy_def
  have hrange : B.pts = Set.range B.ι := B.range_subschemeι.symm
  have hyB : y ∈ B.pts := by rw [hrange]; exact ⟨η, rfl⟩
  -- every point of B specializes from y
  have hspec : ∀ i, y ∈ (ℜ.E i).pts → B.IsContainedIn (ℜ.E i) := by
    intro i hyE
    have hsub : B.pts ⊆ (ℜ.E i).pts := by
      rw [hrange]
      rintro _ ⟨w, rfl⟩
      have hw : w ∈ closure ({η} : Set B.toScheme) := by
        rw [genericPoint_spec]; trivial
      have h1 : B.ι.base w ∈ closure (B.ι.base '' {η}) :=
        image_closure_subset_closure_image B.ι.base.hom.continuous ⟨w, hw, rfl⟩
      rw [Set.image_singleton] at h1
      exact ((ℜ.E i).support.isClosed.closure_subset_iff.mpr (Set.singleton_subset_iff.mpr hyE)) h1
    have hle : ℜ.E i ≤ B := by
      conv_rhs => rw [Subscheme.eq_ofClosed_support B hBred]
      exact (Scheme.IdealSheafData.le_support_iff_le_vanishingIdeal (I := ℜ.E i)
        (Z := B.support)).mp fun z hz => hsub hz
    exact fun U => hle U
  obtain ⟨hySS, hynu⟩ := hB.2.1 hyB
  have hnuy : ℜ.nuAt y = ℜ.nu := le_antisymm
    (le_iSup₂ (f := fun x (_ : x ∈ ℜ.S) => ℜ.nuAt x) y hySS) hynu
  have hnutop : ℜ.nu ≠ ⊤ := DatumII.Raw.nu_ne_top hX ℜ hℜ.2.2.2
  have hb : (ℜ.b : ℕ∞) ≤ (ℜ.weight y : ℕ∞) + (ℜ.nu.toNat : ℕ∞) := by
    have := hySS
    simp only [Raw.S, Set.mem_ofPred_eq] at this
    rw [hnuy] at this; rwa [ENat.natCast_toNat hnutop]
  have hb' : ℜ.b ≤ ℜ.weight y + ℜ.nu.toNat := by exact_mod_cast hb
  have hw : ℜ.weight y ≤ ∑ i ∈ (Finset.univ.filter fun i => B.IsContainedIn (ℜ.E i)), ℜ.a i :=
    Finset.sum_le_sum_of_subset
      (fun i hi => by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
        exact hspec i hi)
  unfold printedExponent
  omega

end DatumII.Raw

/-! ### Remark 1 (p. 169): assembling the local computation -/

namespace Remark1

open IsLocalRing

variable {X : Scheme.{u}} {B : Subscheme X}

theorem _root_.Hironaka.DatumTransform.isDatum_transform_datumI (hX : X.IsNonsingular) (ℜ : DatumI.Raw X)
    (hℜ : ℜ.IsDatum) (t : MonoidalTransformation X B) (hB : ℜ.IsPermissible B) :
    (ℜ.transform t).IsDatum := by
  have hBns := hB.1.isNonsingular
  have hX' := (t.isNonsingular_and_isNonsingular_exceptional hX hBns).1
  have hst := Hironaka.DatumTransform.exists_extendsToRSOP_stalkIdeal_union_exceptional hX hBns t hℜ.1 hℜ.2.2.1 (fun x hx => (hB.2.2 x hx).2.2)
  have hred := Hironaka.DatumTransform.isReduced_of_forall_stalk hX' hst
  exact ⟨hred, Hironaka.DatumTransform.isEverywhereCodimOne_of_forall_stalk hX' hst,
    Hironaka.DatumTransform.hasOnlyNormalCrossings_of_forall_stalk hX' hred hst,
    Subscheme.isReduced_of_isRadical_stalkIdeal
      (Hironaka.DatumTransform.isRadical_stalkIdeal_strictTransform hX t hℜ.2.2.2.1),
    fun j => (hℜ.2.2.2.2 j).strictTransform t⟩

theorem _root_.Hironaka.DatumTransform.isDatum_transform_datumII [IsAlgebraicScheme X] (hX : X.IsNonsingular) (ℜ : DatumII.Raw X)
    (hℜ : ℜ.IsDatum) (t : MonoidalTransformation X B) (hB : ℜ.IsPermissible B) :
    (ℜ.transform t).IsDatum := by
  have hBns := hB.1.isNonsingular
  have hX' := (t.isNonsingular_and_isNonsingular_exceptional hX hBns).1
  have hdata := Hironaka.DatumTransform.exists_rsop_adapted_of_isDatum ℜ.E hX hℜ.2.1 hℜ.2.2.1 hB.2.2
  have hmem : ∀ y, ∃ K : Finset (t.X'.presheaf.stalk y), ExtendsToRSOP _ K ∧
      ∀ i, ∃ K₀ ⊆ K, K₀.card ≤ 1 ∧
        ((ℜ.transform t).E i).stalkIdeal y = Ideal.span {∏ k ∈ K₀, k} := by
    intro y
    obtain ⟨K, hK, hexc, hst⟩ := Hironaka.DatumTransform.exists_extendsToRSOP_stalkIdeal_family hX hBns t ℜ.E hdata y
    refine ⟨K, hK, fun i => ?_⟩
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp only [DatumII.Raw.transform, Fin.snoc_last]; exact hexc
    · simp only [DatumII.Raw.transform, Fin.snoc_castSucc]; exact hst j
  refine ⟨hℜ.1, fun i => ?_, ?_,
    fun x => Subscheme.stalkIdeal_divPow_totalTransform_ne_bot hX t hℜ.2.2.2 _ x⟩
  · apply Hironaka.DatumTransform.isNonsingularIrreducibleCodimOne_of_forall_stalk hX'
    · refine Fin.lastCases ?_ (fun j => ?_) i
      · simp only [DatumII.Raw.transform, Fin.snoc_last]
        intro hne
        rcases hB.1 with hBe | ⟨-, hBirr⟩
        · exfalso
          obtain ⟨y, hy⟩ := hne
          have h3 : B.pts = ∅ := by rw [hBe]; exact Hironaka.DatumTransform.pts_empty
          rw [MonoidalTransformation.pts_exceptional] at hy
          have h4 : t.f y ∈ B.pts := hy
          rw [h3] at h4
          exact h4
        · exact Hironaka.DatumTransform.exceptional_isIrreducible hX hBns hBirr t hne
      · simp only [DatumII.Raw.transform, Fin.snoc_castSucc]
        exact Hironaka.DatumTransform.strictTransform_isIrreducible_of_nonempty t (hℜ.2.1 j)
    · intro y
      obtain ⟨K, hK, h⟩ := hmem y
      obtain ⟨K₀, h1, h2, h3⟩ := h i
      exact Hironaka.DatumTransform.stalkIdeal_eq_top_or_exists_of_card_le_one hK h1 h2 h3
  · have hU : ∀ y, ∃ K : Finset (t.X'.presheaf.stalk y), ExtendsToRSOP _ K ∧
        (ℜ.transform t).eUnion.stalkIdeal y = Ideal.span {∏ k ∈ K, k} := by
      intro y
      have : IsRegularLocalRing (t.X'.presheaf.stalk y) := hX' y
      obtain ⟨K, hK, h⟩ := hmem y
      choose L hL _ hLe using h
      refine ⟨Finset.univ.biUnion L, hK.mono (Finset.biUnion_subset.mpr fun i _ => hL i), ?_⟩
      rw [DatumII.Raw.eUnion, Hironaka.DatumTransform.stalkIdeal_iInf_fintype, ← Hironaka.DatumTransform.iInf_span_prod_of_subset hK L hL]
      exact iInf_congr hLe
    exact Hironaka.DatumTransform.hasOnlyNormalCrossings_of_forall_stalk hX' (Hironaka.DatumTransform.isReduced_of_forall_stalk hX' hU) hU

theorem _root_.Hironaka.DatumTransform.isClosedRestriction_transform_datumI (hX : X.IsNonsingular) (ℜ : DatumI.Raw X)
    (hℜ : ℜ.IsDatum) (t : MonoidalTransformation X B) (hB : ℜ.IsPermissible B)
    (F : Subscheme X) (hF : ℜ.IsClosedRestriction F) (hBF : ℜ.IsPermissibleClosed F B) :
    (ℜ.transform t).IsClosedRestriction (Subscheme.strictTransform t F) := by
  have hBns := hB.1.isNonsingular
  have hX' := (t.isNonsingular_and_isNonsingular_exceptional hX hBns).1
  have hdata := Hironaka.DatumTransform.exists_rsop_adapted_of_isClosedRestriction_datumI hX hℜ.1 hℜ.2.2.1 (fun x hx => (hB.2.2 x hx).2.2) hF.1 hF.2.1
    (Hironaka.DatumTransform.isReduced_of_isNonsingular hBns) (fun x hx => (hBF.2 hx).2)
  have hst : ∀ y : t.X', ∃ K : Finset (t.X'.presheaf.stalk y), ExtendsToRSOP _ K ∧
      (∃ K₀ ⊆ K, (Subscheme.strictTransform t ℜ.E).stalkIdeal y = Ideal.span {∏ k ∈ K₀, k}) ∧
      (∃ K₀ ⊆ K, t.exceptional.stalkIdeal y = Ideal.span {∏ k ∈ K₀, k}) ∧
      (∃ K₀ ⊆ K, K₀.card ≤ 1 ∧
        (Subscheme.strictTransform t F).stalkIdeal y = Ideal.span {∏ k ∈ K₀, k}) := by
    intro y
    obtain ⟨Z, hZ, hBZ, ⟨J, hJZ, hJ⟩, ⟨JF, hJFZ, hJF1, hJF⟩⟩ := hdata (t.f y)
    have : IsRegularLocalRing (X.presheaf.stalk (t.f y)) := hX _
    obtain ⟨K, hK, ⟨K₀, hK₀, -, hexc⟩, htr, htc⟩ :=
      Hironaka.DatumTransform.exists_stalk_transform_components hX hBns t y hZ hBZ
    obtain ⟨K₁, hK₁, h1⟩ := htc ℜ.E J hJZ hJ fun a ha =>
      Hironaka.DatumTransform.exists_component_of_mem hZ hJZ hJ ha
    obtain ⟨K₂, hK₂, hc2, h2⟩ := htr JF hJFZ F hJF
    exact ⟨K, hK, ⟨K₁, hK₁, h1⟩, ⟨K₀, hK₀, hexc⟩, ⟨K₂, hK₂, hc2.trans hJF1, h2⟩⟩
  refine ⟨?_, ?_, ?_⟩
  · apply Hironaka.DatumTransform.isNonsingularIrreducibleCodimOne_of_forall_stalk hX'
      (Hironaka.DatumTransform.strictTransform_isIrreducible_of_nonempty t hF.1)
    intro y
    obtain ⟨K, hK, -, -, K₂, hK₂, hc, h⟩ := hst y
    exact Hironaka.DatumTransform.stalkIdeal_eq_top_or_exists_of_card_le_one hK hK₂ hc h
  · have hU : ∀ y, ∃ K : Finset (t.X'.presheaf.stalk y), ExtendsToRSOP _ K ∧
        ((ℜ.transform t).E.union (Subscheme.strictTransform t F)).stalkIdeal y =
          Ideal.span {∏ k ∈ K, k} := by
      intro y
      have : IsRegularLocalRing (t.X'.presheaf.stalk y) := hX' y
      obtain ⟨K, hK, ⟨K₁, hK₁, h1⟩, ⟨K₀, hK₀, h0⟩, ⟨K₂, hK₂, -, h2⟩⟩ := hst y
      refine ⟨K₁ ∪ K₀ ∪ K₂, hK.mono (Finset.union_subset (Finset.union_subset hK₁ hK₀) hK₂), ?_⟩
      show ((Subscheme.strictTransform t ℜ.E ⊓ t.exceptional) ⊓
        Subscheme.strictTransform t F).stalkIdeal y = _
      rw [Subscheme.stalkIdeal_inf_eq, Subscheme.stalkIdeal_inf_eq, h1, h0, h2,
        Hironaka.DatumTransform.span_prod_inf_of_subset hK hK₁ hK₀,
        Hironaka.DatumTransform.span_prod_inf_of_subset hK (Finset.union_subset hK₁ hK₀) hK₂]
    exact Hironaka.DatumTransform.hasOnlyNormalCrossings_of_forall_stalk hX' (Hironaka.DatumTransform.isReduced_of_forall_stalk hX' hU) hU
  · intro p hp
    refine Hironaka.DatumTransform.mem_closure_of_mem_strictTransform t hF.2.2 ?_ hp
    rintro y ⟨⟨hyW, hyF⟩, hyE⟩
    exact ⟨(t.mem_pts_strictTransform_iff_of_notMem _ hyE).mpr hyW,
      fun h => hyF ((t.mem_pts_strictTransform_iff_of_notMem _ hyE).mp h)⟩

theorem _root_.Hironaka.DatumTransform.isOpenRestriction_transform_datumI (ℜ : DatumI.Raw X)
    (hℜ : ℜ.IsDatum) (t : MonoidalTransformation X B)
    (U : Set X) (hU : ℜ.IsOpenRestriction U) (hBU : ℜ.IsPermissibleOpen U B) :
    (ℜ.transform t).IsOpenRestriction (DatumI.Raw.transformOpen t U) := by
  obtain ⟨⟨U₀, hU₀, rfl⟩, hdense, hres⟩ := hU
  have hBU' : ∀ x ∈ U₀ ∩ ℜ.W.pts, x ∉ B.pts := fun x hx hxB => (hBU.2 hxB).2 hx
  refine ⟨⟨t.f.base ⁻¹' U₀ ∩ t.exceptional.ptsᶜ,
    (hU₀.preimage t.f.base.hom.continuous).inter t.exceptional.support.isClosed.isOpen_compl,
    ?_⟩, ?_, ?_⟩
  · ext y
    change t.f y ∈ U₀ ∩ ℜ.W.pts ↔ (t.f y ∈ U₀ ∧ y ∉ t.exceptional.pts) ∧
      y ∈ (Subscheme.strictTransform t ℜ.W).pts
    constructor
    · rintro ⟨hy0, hyW⟩
      have hyE : y ∉ t.exceptional.pts := by
        rw [MonoidalTransformation.pts_exceptional]; exact hBU' _ ⟨hy0, hyW⟩
      exact ⟨⟨hy0, hyE⟩, (t.mem_pts_strictTransform_iff_of_notMem _ hyE).mpr hyW⟩
    · rintro ⟨⟨hy0, hyE⟩, hyW⟩
      exact ⟨hy0, (t.mem_pts_strictTransform_iff_of_notMem _ hyE).mp hyW⟩
  · intro p hp
    exact closure_mono Set.sdiff_subset
      (Hironaka.DatumTransform.mem_closure_of_mem_strictTransform t hdense subset_rfl hp)
  · intro y hy
    have hx := hres _ hy
    obtain ⟨Z, ι, j', h1, h2, h3, h4, -, hcomp, hrι, hrange, hexc, htt⟩ := Hironaka.DatumTransform.exists_flat_isPreimmersion_off_center t
    have hyE : y ∉ t.exceptional.pts := by
      rw [MonoidalTransformation.pts_exceptional]; exact hBU' _ hy
    have hyr : y ∈ Set.range j'.base := by rw [hrange]; exact hyE
    obtain ⟨u, rfl⟩ := hyr
    rw [hcomp] at hx
    refine ⟨?_, fun j => ?_, ?_⟩
    · refine (FlatPreimm.isSimpleAt_totalTransform_iff j' _ u).mp ?_
      show (Subscheme.totalTransform j' (Subscheme.strictTransform t ℜ.W)).IsSimpleAt u
      rw [htt]
      exact (FlatPreimm.isSimpleAt_totalTransform_iff ι _ u).mpr hx.1
    · refine (FlatPreimm.isNormallyFlatAlongAt'_totalTransform_iff j' _ _
        ((hℜ.2.2.2.2 j).strictTransform t) u).mp ?_
      show Subscheme.IsNormallyFlatAlongAt'
        (Subscheme.totalTransform j' (Subscheme.strictTransform t (ℜ.V j)))
        (Subscheme.totalTransform j' (Subscheme.strictTransform t ℜ.W)) u
      rw [htt, htt]
      exact (FlatPreimm.isNormallyFlatAlongAt'_totalTransform_iff ι _ _
        (hℜ.2.2.2.2 j) u).mpr (hx.2.1 j)
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
      exact (FlatPreimm.hasOnlyNormalCrossingsWithAt_totalTransform_iff ι _ _ u).mpr hx.2.2

theorem _root_.Hironaka.DatumTransform.isClosedRestriction_transform_datumII (hX : X.IsNonsingular) (ℜ : DatumII.Raw X)
    (hℜ : ℜ.IsDatum) (t : MonoidalTransformation X B) (hB : ℜ.IsPermissible B)
    (F : Subscheme X) (hF : ℜ.IsClosedRestriction F) (hBF : ℜ.IsPermissibleClosed F B) :
    (ℜ.transform t).IsClosedRestriction (Subscheme.strictTransform t F) := by
  have hBns := hB.1.isNonsingular
  have hX' := (t.isNonsingular_and_isNonsingular_exceptional hX hBns).1
  have hdata := Hironaka.DatumTransform.exists_rsop_adapted_of_isClosedRestriction_datumII hX ℜ.E hℜ.2.1 hB.2.2 hF.1 hF.2
    (Hironaka.DatumTransform.isReduced_of_isNonsingular hBns) hBF.2
  have hst : ∀ y : t.X', ∃ K : Finset (t.X'.presheaf.stalk y), ExtendsToRSOP _ K ∧
      (∀ i, ∃ K₀ ⊆ K, K₀.card ≤ 1 ∧
        ((ℜ.transform t).E i).stalkIdeal y = Ideal.span {∏ k ∈ K₀, k}) ∧
      (∃ K₀ ⊆ K, K₀.card ≤ 1 ∧
        (Subscheme.strictTransform t F).stalkIdeal y = Ideal.span {∏ k ∈ K₀, k}) := by
    intro y
    obtain ⟨K, hK, hexc, h⟩ :=
      Hironaka.DatumTransform.exists_extendsToRSOP_stalkIdeal_family hX hBns t (fun o : Option (Fin ℜ.α) => o.elim F ℜ.E) hdata y
    refine ⟨K, hK, fun i => ?_, h none⟩
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp only [DatumII.Raw.transform, Fin.snoc_last]; exact hexc
    · simp only [DatumII.Raw.transform, Fin.snoc_castSucc]; exact h (some j)
  refine ⟨?_, ?_⟩
  · apply Hironaka.DatumTransform.isNonsingularIrreducibleCodimOne_of_forall_stalk hX'
      (Hironaka.DatumTransform.strictTransform_isIrreducible_of_nonempty t hF.1)
    intro y
    obtain ⟨K, hK, -, K₂, hK₂, hc, h⟩ := hst y
    exact Hironaka.DatumTransform.stalkIdeal_eq_top_or_exists_of_card_le_one hK hK₂ hc h
  · have hU : ∀ y, ∃ K : Finset (t.X'.presheaf.stalk y), ExtendsToRSOP _ K ∧
        ((ℜ.transform t).eUnion.union (Subscheme.strictTransform t F)).stalkIdeal y =
          Ideal.span {∏ k ∈ K, k} := by
      intro y
      have : IsRegularLocalRing (t.X'.presheaf.stalk y) := hX' y
      obtain ⟨K, hK, h, K₂, hK₂, -, h2⟩ := hst y
      choose L hL _ hLe using h
      have hLU : Finset.univ.biUnion L ⊆ K := Finset.biUnion_subset.mpr fun i _ => hL i
      refine ⟨Finset.univ.biUnion L ∪ K₂, hK.mono (Finset.union_subset hLU hK₂), ?_⟩
      show ((ℜ.transform t).eUnion ⊓ Subscheme.strictTransform t F).stalkIdeal y = _
      rw [Subscheme.stalkIdeal_inf_eq, DatumII.Raw.eUnion, Hironaka.DatumTransform.stalkIdeal_iInf_fintype, h2,
        ← Hironaka.DatumTransform.span_prod_inf_of_subset hK hLU hK₂, ← Hironaka.DatumTransform.iInf_span_prod_of_subset hK L hL]
      exact congrArg (· ⊓ _) (iInf_congr hLe)
    exact Hironaka.DatumTransform.hasOnlyNormalCrossings_of_forall_stalk hX' (Hironaka.DatumTransform.isReduced_of_forall_stalk hX' hU) hU

end Remark1

namespace DatumI.Raw

variable {X : Scheme.{u}}

/-- Remark 1 (p. 169): the transform of a datum by a permissible monoidal transformation is
again a datum of the same type (and with the same kind of restriction).  "All that may be
non-trivial is the normal crossing property of `E' ∪ E'_{α+1}`", proved on p. 169 by the
explicit description of `O_{X',x'}` as a ring of fractions of `O_x[z_{r+1}/z_t, …, z_s/z_t]`.

Deviation from the paper (statement modified): Remark 1 speaks of "a resolution datum on `X` as
in Definition 7", and Definition 3 (p. 164) fixes `X` to be a non-singular irreducible algebraic
scheme ("We always assume that dim(X) ≧ 0").  The statement assumes only that `X` is algebraic
and non-singular (without these the formal `IsDatum` is not preserved: a non-noetherian
valuation ring gives a counterexample).  Irreducibility and non-emptiness are not assumed: the
argument is local, and they are not preserved by the transformation with center `B = X` (then
`X' = ∅`).  The type indices `N`, `n` are not part of `IsDatum`; see `transform_isAmbient` and
`dim_transform_W`.

The proof follows the paper (`DatumTransform.exists_extendsToRSOP_stalkIdeal_union_exceptional`): at
`x' ∈ X'`, `x = f(x')`, a regular system of parameters of `O_x` adapted to the components `F_j` of `E` through
`x` and to `B`; `O_{x'}` is a ring of fractions `A_M` of `A = O_x[z_{r+1}z_t^{-1}, …, z_s z_t^{-1}]`
(`DatumTransform.exists_chart_ringOfFractions`, with `MonoidalTransform.exists_equiv_of_span_eq`); the
elements `z'_v`; the strict transform `F_j'` of each component (`DatumTransform.strictTransform_component_stalk`),
`E' = ⋃ F_j'` (`Subscheme.strictTransform_iInf_fintype`); `E'_{α+1}` defined by `z'_t`; the extension of the
`z'_v ∈ M` to a regular system of parameters.

Deviation from the paper (gap filled): all conditions other than normal crossings, the existence of `t`
(p. 209), the "easily seen" assertions of the chart computation, `E' = ⋃ F_j'`, "similarly for the others"
(via `DatumTransform.exists_rsop_exchange` / `ExtendsToRSOP.exchange`) and the open restriction (via flat
preimmersions) are proved here and in `Hironaka/Compat/TransformRSOP.lean` and
`Hironaka/Compat/TransformRingOfFractions.lean`. -/
@[blueprint "rem:I.1-transform-is-datum-I"
  (statement := /-- If $f$ is permissible for $\mathfrak R^{N,n}_{\mathrm I}$, then
    $f^*(\mathfrak R^{N,n}_{\mathrm I})$ is again a resolution datum of type
    $\mathfrak R^{N',n'}_{\mathrm I}$ on $X'$, with $N'=N$ unless $B=X$, and $n'=n$ unless
    $B$ contains an irreducible component of $W$. If $F$ (resp.\ $U$) is a closed (resp.\
    open) restriction, then $F'$ (resp.\ $U'$) is one for the transform. (Remark 1, p.\ 169.)

    \textbf{Deviation from the paper (statement modified).} $X$ is assumed algebraic and
    non-singular, as in Definition~3 (p.~164); irreducibility and non-emptiness
    (``$\dim(X)\ge0$'') are not assumed, since the argument is local and they fail for $X'$
    when $B=X$. The type indices $N,n$ are not part of the Lean notion of datum; they are
    treated in \cref{rem:I.1-dim} and \cref{rem:I.1-dim-W}. -/)
  (proof := /-- The paper's argument (p.~169): all that may be non-trivial is the normal
    crossing property of $E'\cup E'_{\alpha+1}$ (and of $E'\cup F'\cup E'_{\alpha+1}$ etc.).
    Choose a regular system of parameters $(z_1,\dots,z_r,z_{r+1},\dots,z_s)$ at $x=f(x')$
    with the components of $E$ through $x$ given by $z_j=0$ and $B$ by
    $z_{r+1}=\dots=z_s=0$; then $\mathcal O_{x'}$ is a ring of fractions of
    $\mathcal O_x[z_{r+1}/z_t,\dots,z_s/z_t]$ for some $t$, and with $z'_v=z_v$ ($v\le r$),
    $z'_t=z_t$, $z'_v=z_v/z_t$ ``it is easily seen'' that the strict transform of a component
    $z_j=0$ passes through $x'$ iff $j\ne t$ and $z'_j\in M$, in which case it is defined by
    $z'_j=0$, that $E'_{\alpha+1}$ is defined by $z'_t=0$, and that those $z'_v$ which lie in
    $M$ extend to a regular system of parameters of $\mathcal O_{x'}$; ``similarly for the
    others''.

    \textbf{Gap in the paper filled.} Lean proves every step the paper calls trivial or
    ``easily seen'', along the paper's route: the existence of $t$ and of the ring of fractions
    $\mathcal O_{x'}=A_M$, $A=\mathcal O_x[z_{r+1}/z_t,\dots,z_s/z_t]$ (p.~209, from
    $x=\sum c_jz_j$, \cref{lem:III.2-monoidal-transform-index}), the strict transforms $F_j'$ of
    the components $F_j$ and $E'=\bigcup F'_j$, the extension of the $z'_v$ to a regular system of parameters (through
    the Ch.~III \S2 description $R'/xR'\cong((R/P)[X_1,\dots,X_r])_{\mathfrak q}$, regularity
    of $R'$ and $R'/xR'$, and a derivation argument), the reducedness of $W'$, the density of
    the transformed restrictions, and the open restriction (resolvedness transported along the
    flat preimmersions $X-B\to X$, $X-B\to X'$). ``Similarly for the others'' needs one
    regular system of parameters adapted at once to $E$, $F$ and $B$, which the hypotheses do
    not provide directly; Lean constructs it by an exchange lemma, using $B\subseteq F$. -/)
  (latexEnv := "proposition")]
theorem transform_isDatum [IsAlgebraicScheme X] (hX : X.IsNonsingular) (ℜ : Raw X)
    (hℜ : ℜ.IsDatum) {B : Subscheme X}
    (t : MonoidalTransformation X B) (hB : ℜ.IsPermissible B) :
    (ℜ.transform t).IsDatum ∧
    (∀ F, ℜ.IsClosedRestriction F → ℜ.IsPermissibleClosed F B →
      (ℜ.transform t).IsClosedRestriction (Subscheme.strictTransform t F)) ∧
    (∀ U, ℜ.IsOpenRestriction U → ℜ.IsPermissibleOpen U B →
      (ℜ.transform t).IsOpenRestriction (transformOpen t U)) := by
  exact ⟨DatumTransform.isDatum_transform_datumI hX ℜ hℜ t hB,
    fun F hF hBF => DatumTransform.isClosedRestriction_transform_datumI hX ℜ hℜ t hB F hF hBF,
    fun U hU hBU => DatumTransform.isOpenRestriction_transform_datumI ℜ hℜ t U hU hBU⟩

/-- Remark 1, p. 169: "Let `W'` be as in Definition 7. Then we have `dim(W') = dim(W) = n`,
unless `B` contains an irreducible component of `W`. … In this last case, `f*(ℜ)` is in general
a resolution datum of type `ℜ^{N,n'}_I` with an integer `n' ≦ n`."

"Note that B can not contain any irreducible component of W if ℜ has restriction either closed or open" is
`DatumI.Raw.dim_transform_W_eq_of_restriction` (`Hironaka/Compat/RemarkOneDim.lean`, from
`DatumI.Raw.IsPermissibleClosed.not_pts_subset_of_mem_irreducibleComponents` and its open analogue in
`Hironaka/Compat/LocalizeSuccession.lean`).  Deviation from the paper (gap filled): the paper gives no
proof; `Hironaka/Compat/StrictTransformDim.lean` supplies one (the hypotheses `_hX`, `_hℜ`,
`_hB` are not used). -/
@[blueprint "rem:I.1-dim-W"
  (statement := /-- If $f$ is permissible for $\mathfrak R^{N,n}_{\mathrm I}=(E;V;W)$ and $W'$ is
    the strict transform of $W$, then $\dim(W')\le\dim(W)$, with equality unless $B$ contains an
    irreducible component of $W$. (Remark~1, p.~169.)

    The paper's remark ``Note that $B$ can not contain any irreducible
    component of $W$ if $\mathfrak R$ has restriction either closed or open'' (p.~169) is
    \cref{rem:I.1-dim-W-restriction}. -/)
  (proof := /-- Off $f^{-1}(B)$, $f$ is an isomorphism, and every point of $W'$ is a
    specialization of a point of $W'$ off $f^{-1}(B)$. In an affine chart
    $\operatorname{Spec}A[I/a]$ the local rings of $W'$ are birational finitely generated
    extensions of those of $W$, so $\dim(W')\le\dim(W)$ by the dimension inequality
    (\cref{compat:strict-transform-dim-le}). If $B$ contains no irreducible component of $W$, a
    chain of irreducible closed subsets of $W$ ending at a component lifts to $W'$, $f$ being
    proper and hence specializing (\cref{compat:strict-transform-dim-eq}).

    \textbf{Gap in the paper filled.} The paper states the dimension claims without proof;
    the argument above is ours (it uses the dimension inequality for finitely generated
    birational extensions, \cref{compat:dimension-inequality-birational}, and the properness
    of $f$), and needs neither non-singularity of $X$ nor permissibility of $B$. -/)
  (latexEnv := "remark")]
theorem dim_transform_W [Hironaka.Cited.MonoidalTransformationExistsIsProper.{u}] [IsAlgebraicScheme X] (_hX : X.IsNonsingular) (ℜ : Raw X)
    (_hℜ : ℜ.IsDatum) {B : Subscheme X} (t : MonoidalTransformation X B)
    (_hB : ℜ.IsPermissible B) :
    (ℜ.transform t).W.dim ≤ ℜ.W.dim ∧
    ((∀ C ∈ ℜ.W.irreducibleComponents, ¬ C.pts ⊆ B.pts) →
      (ℜ.transform t).W.dim = ℜ.W.dim) :=
  -- `W' = f*(W)` is the strict transform of `W`; the dimension estimates hold for the strict
  -- transform of any subscheme of an algebraic scheme (`Hironaka/Compat/StrictTransformDim.lean`):
  -- `≤` by the dimension inequality in the charts `Spec A[I/a]`, `=` by lifting chains of
  -- specializations along the proper map `f`, starting at the generic points (off `B`) of the
  -- irreducible components of `W`.  Non-singularity of `X`, the datum conditions and
  -- permissibility of `B` are not needed.
  ⟨MonoidalTransformation.dim_strictTransform_le t ℜ.W,
    MonoidalTransformation.dim_strictTransform_eq t ℜ.W⟩

end DatumI.Raw

namespace DatumII.Raw

variable {X : Scheme.{u}}

/-- Remark 1 (p. 169) for type II data.

Deviation from the paper (statement modified): Remark 1 speaks of "a resolution datum on `X` as
in Definition 7", and Definition 3 (p. 164) fixes `X` to be a non-singular irreducible algebraic
scheme ("We always assume that dim(X) ≧ 0").  The statement assumes only that `X` is algebraic
and non-singular (without these the formal `IsDatum` is not preserved: a non-noetherian
valuation ring gives a counterexample).  Irreducibility and non-emptiness are not assumed: the
argument is local, and they are not preserved by the transformation with center `B = X` (then
`X' = ∅`).  The conclusion `ℜ.nu ≠ ⊤` is not part of Remark 1 (it is implicit in Def. 4).

The divisibility of `f⁻¹(J)` by `P^ν` (asserted in the paper, pp. 142, 176 and 214), on which the
agreement of `divPow` with the paper's quotient `f⁻¹(J)P^{-ν}` rests, is
`DatumII.Raw.totalTransform_le_exceptional_pow_nu`; the transformed datum with the printed quotient is
`DatumII.Raw.transform_isDatum_of_mul_exceptional_pow_eq`.

Deviation from the paper (gap filled): normal crossings of `E'₁ ∪ ⋯ ∪ E'_{α+1}` (and with `F'`)
as for type I; irreducibility of `E_{α+1} = f⁻¹(B)` (`compat:blowup-exceptional-irreducible`);
non-zero stalks of the transformed ideal; `ν(ℜ) < ∞` (`DatumII.Raw.nu_ne_top`, using Ch. III). -/
@[blueprint "rem:I.1-transform-is-datum-II"
  (statement := /-- If $f$ is permissible for $\mathfrak R^N_{\mathrm{II}}$ then
    $f^*(\mathfrak R^N_{\mathrm{II}})$ is a resolution datum of type
    $\mathfrak R^N_{\mathrm{II}}$ on $X'$; if $F$ is a closed restriction so is $F'$.
    Moreover $\nu(\mathfrak R)<\infty$. (Remark~1, p.~169, for the first two assertions;
    the last is implicit in the ``max'' of Definition~4, p.~165.)

    \textbf{Deviation from the paper (statement modified).} As for type I
    (\cref{rem:I.1-transform-is-datum-I}), $X$ is assumed algebraic and non-singular, but not
    irreducible; the conclusion $\nu(\mathfrak R)<\infty$ is added. The transformed ideal is the
    colon ideal $(f^{-1}(J):P^\nu)$; that this is the paper's quotient $f^{-1}(J)P^{-\nu}$
    (the divisibility of $f^{-1}(J)$ by $P^{\nu}$, pp.~142, 176) is \cref{lem:I.7-II-divisible},
    and the statement with the quotient as printed is
    \cref{rem:I.1-transform-is-datum-II-quotient}. See also the correction in
    \cref{def:I.7-II} (empty center). -/)
  (proof := /-- The paper's argument is that of \cref{rem:I.1-transform-is-datum-I}: all that
    may be non-trivial is the normal crossing property of
    $E_1'\cup\dots\cup E_\alpha'\cup E'_{\alpha+1}$ (resp.\ with $F'$), seen in the chart
    of p.~169.

    \textbf{Gap in the paper filled.} As for type I; in addition Lean proves that $E'_i$ and
    $E'_{\alpha+1}=f^{-1}(B)$ are irreducible (\cref{compat:blowup-exceptional-irreducible};
    the paper uses this without comment), that the stalks of the transformed ideal are
    non-zero, and that $\nu(\mathfrak R)<\infty$ (Krull's intersection theorem and the upper
    semicontinuity of Ch.~III, Cor.~1 of Th.~2, on the quasi-compact $X$). For the closed
    restriction, a regular system of parameters adapted at once to the $E_i$, $F$ and $B$ is
    constructed by an exchange lemma, using $B\subseteq F$. -/)
  (latexEnv := "proposition")]
theorem transform_isDatum [Hironaka.Cited.IsHironakaBaseIsClosedSingularLocus.{u}] [Hironaka.Cited.CurveFiniteIntegralClosure.{u}] [Hironaka.Cited.IsRegularLocalRingLocalizationOfIsRegularLocalRing.{u}] [IsAlgebraicScheme X] (hX : X.IsNonsingular) (ℜ : Raw X)
    (hℜ : ℜ.IsDatum) {B : Subscheme X}
    (t : MonoidalTransformation X B) (hB : ℜ.IsPermissible B) :
    (ℜ.transform t).IsDatum ∧
    (∀ F, ℜ.IsClosedRestriction F → ℜ.IsPermissibleClosed F B →
      (ℜ.transform t).IsClosedRestriction (Subscheme.strictTransform t F)) ∧
    ℜ.nu ≠ ⊤ := by
  exact ⟨DatumTransform.isDatum_transform_datumII hX ℜ hℜ t hB,
    fun F hF hBF => DatumTransform.isClosedRestriction_transform_datumII hX ℜ hℜ t hB F hF hBF,
    DatumII.Raw.nu_ne_top hX ℜ hℜ.2.2.2⟩

/-! #### The quotient `f⁻¹(J)P^{-ν}` of Definition 7 (type II)

Definition 7 (p. 168) writes the transformed ideal as `f⁻¹(J)P^{-ν}`; the paper asserts that
`f⁻¹(J)` is divisible by `P^ν` (p. 142: "f⁻¹(J) is divisible by the m-th power of the sheaf of
ideals of f⁻¹(D) on X'"; p. 176: "the sheaf of ideals f⁻¹(J) is divisible by the ν-th power of the
sheaf of ideals of f⁻¹(B) on X'. The quotient obtained by this division is called the weak transform
of J by the monoidal transformation f. This is the kind of transform of a coherent sheaf of ideals
that has appeared in the definition of the transform of a resolution datum of type ℜ_II^N. (See
Definition 7, §1.)"), and in Ch. III, Remark 2 (p. 214): "Let x be the generic point of B; we assume
that B is not empty. Then for every non-negative integer ν ≤ ν(J_x), f⁻¹(J) is contained in P_E^ν."
The paper gives no argument for these assertions. -/

variable {B : Subscheme X}

/-- Divisibility of `f⁻¹(J)` by `P^ν`, `ν = ν(ℜ)` (pp. 142, 176; Ch. III, Remark 2, p. 214):
`f⁻¹(J) ⊆ P^ν`, where `P` is the sheaf of ideals of `E_{α+1}' = f⁻¹(B)`, for a center `B` permissible
for the datum `ℜ` of type II.

If `B` is empty then `P` is the unit ideal sheaf.  Otherwise let `ξ` be the generic point of `B`.
Since `B ⊆ S*(ℜ)`, `ν(J_ξ) = ν(ℜ)` (`ξ ∈ S(ℜ)` gives `≤`, `ξ ∈ S_{ν(ℜ)}` gives `≥`), and the claim
is Remark 2 of Ch. III (`Subscheme.totalTransform_le_exceptional_pow`): `J_y ⊆ P_y^ν` for
`ν ≤ ν(J_ξ)`, because `ν(J_ξ) = ν_P(J_y)` (`Subscheme.le_nu_generic_iff`; the powers of `P` are
`P`-primary since `R/P` is regular, `lem:III.3-order-facts`), and then `f⁻¹(J)_{y'} = J_yR' ⊆ P^νR'`.
Here `ν` is `ν(ℜ).toNat`, as in `DatumII.Raw.transform`.  The equivalent form of p. 142, "`ν = ν(f⁻¹(J)_y)` for the
generic point `y` of `f⁻¹(B)`", is `DatumII.Raw.nu_totalTransform_generic_eq_nu`. -/
theorem totalTransform_le_exceptional_pow_nu [IsAlgebraicScheme X] (hX : X.IsNonsingular)
    (ℜ : Raw X) (t : MonoidalTransformation X B) (hB : ℜ.IsPermissible B) :
    Subscheme.totalTransform t.f ℜ.J ≤ t.exceptional ^ ℜ.nu.toNat := by
  by_cases hne : B.pts.Nonempty
  · obtain ⟨hns, hirr⟩ : B.IsNonsingular ∧ B.IsIrreducible := by
      rcases hB.1 with h | h
      · exfalso
        obtain ⟨z, hz⟩ := hne
        rw [h, DatumTransform.pts_empty] at hz
        exact hz
      · exact h
    obtain ⟨ξ, hξ⟩ := Subscheme.exists_isGenericPoint hirr
    have hξS : ξ ∈ ℜ.sStar := hB.2.1 hξ.mem
    have hνξ : ℜ.nuAt ξ = ℜ.nu :=
      le_antisymm (le_iSup₂ (f := fun x (_ : x ∈ ℜ.S) => ℜ.nuAt x) ξ hξS.1) hξS.2
    refine Subscheme.totalTransform_le_exceptional_pow hX hns t ℜ.J hξ ?_
    rw [← nuAt, hνξ]
    exact ENat.natCast_toNat_le_self _
  · rw [Set.not_nonempty_iff_eq_empty] at hne
    rw [Subscheme.le_iff_stalkIdeal_le]
    intro y
    have hx : t.f y ∉ B.pts := by
      rw [hne]
      exact Set.notMem_empty _
    rw [Subscheme.stalkIdeal_pow_eq, MonoidalTransformation.exceptional,
      stalkIdeal_totalTransform t.f B y, ← Ideal.map_pow,
      Subscheme.stalkIdeal_eq_top_of_notMem_pts hx, Ideal.top_pow, Ideal.map_top]
    exact le_top

/-- The transformed ideal `J'` of `f*(ℜ)` times `P^ν` is `f⁻¹(J)`: the colon ideal used by Lean is a
quotient in the sense of the paper ("the sheaf of ideals obtained by this division", p. 142). -/
theorem transform_J_mul_exceptional_pow [IsAlgebraicScheme X] (hX : X.IsNonsingular)
    (ℜ : Raw X) (t : MonoidalTransformation X B) (hB : ℜ.IsPermissible B) :
    (ℜ.transform t).J * t.exceptional ^ ℜ.nu.toNat = Subscheme.totalTransform t.f ℜ.J :=
  Subscheme.divPow_mul_pow_eq t.invertible (totalTransform_le_exceptional_pow_nu hX ℜ t hB)

/-- Definition 7 (type II), p. 168, and pp. 142, 176: "`f⁻¹(J)` is divisible by the `ν`-th power of
the sheaf of ideals of `f⁻¹(B)` on `X'`.  The quotient obtained by this division …": for `B`
permissible, `f⁻¹(J) ⊆ P^ν` (`ν = ν(ℜ)`), the quotient `f⁻¹(J)P^{-ν}`, i.e. the sheaf of ideals `K`
with `K·P^ν = f⁻¹(J)`, exists and is unique (`P` is invertible), and it is the transformed ideal of
`DatumII.Raw.transform` (`transform_J_mul_exceptional_pow`).

Gap in the paper filled: neither the divisibility nor the uniqueness of the quotient is argued by
the paper (pp. 142, 176, 214); `ν(J_ξ) = ν(ℜ)` for the generic point `ξ` of `B ⊆ S*(ℜ)` is also
tacit. -/
@[blueprint "lem:I.7-II-divisible"
  (statement := /-- Let $\mathfrak R$ be a resolution datum of type $\mathfrak R^N_{\mathrm{II}}$ on
    a non-singular algebraic scheme $X$, $f\colon X'\to X$ the monoidal transformation with a
    center $B$ permissible for $\mathfrak R$, $\nu=\nu(\mathfrak R)$, and $P$ the sheaf of
    ideals of $E'_{\alpha+1}=f^{-1}(B)$. Then $f^{-1}(J)$ is divisible by $P^\nu$, i.e.\
    $f^{-1}(J)\subseteq P^{\nu}$; the quotient $f^{-1}(J)P^{-\nu}$ (the sheaf of ideals $K$
    with $KP^{\nu}=f^{-1}(J)$) exists and is unique; and it is the transformed ideal of
    \cref{def:I.7-II}. (pp.~142, 176, 214; Definition~7, p.~168.)
    \textbf{Gap in the paper filled.} The paper asserts the divisibility (``or equivalently'',
    p.~142; p.~176; Ch.~III, Remark~2, p.~214) without argument. -/)
  (proof := /-- If $B=\emptyset$ then $P=\mathcal O_{X'}$. Otherwise let $\xi$ be the generic
    point of $B$; since $B\subseteq S^*(\mathfrak R)$, $\nu(J_\xi)=\nu(\mathfrak R)$, and
    Ch.~III, Remark~2 (\cref{rem:III.2-2}) gives $f^{-1}(J)\subseteq P^\nu$: for $y\in B$,
    $\nu\le\nu(J_\xi)$ iff $J_y\subseteq P_B^{\nu}$, the powers of $P_B$ being $P_B$-primary
    because $\mathcal O_{B,y}$ is regular (\cref{lem:III.3-order-facts}). On stalks $P$ is
    principal, so $(f^{-1}(J):P^\nu)P^\nu=f^{-1}(J)$ when $f^{-1}(J)\subseteq P^\nu$, and a power
    of a principal ideal generated by a non-zero-divisor can be cancelled. -/)
  (latexEnv := "lemma")]
theorem le_exceptional_pow_and_existsUnique_mul_eq [IsAlgebraicScheme X] (hX : X.IsNonsingular)
    (ℜ : Raw X) (t : MonoidalTransformation X B) (hB : ℜ.IsPermissible B) :
    Subscheme.totalTransform t.f ℜ.J ≤ t.exceptional ^ ℜ.nu.toNat ∧
    ∃! K : Subscheme t.X', K * t.exceptional ^ ℜ.nu.toNat = Subscheme.totalTransform t.f ℜ.J :=
  ⟨totalTransform_le_exceptional_pow_nu hX ℜ t hB, (ℜ.transform t).J,
    transform_J_mul_exceptional_pow hX ℜ t hB, fun _ hK =>
      Subscheme.eq_of_mul_pow_eq_mul_pow t.invertible
        (hK.trans (transform_J_mul_exceptional_pow hX ℜ t hB).symm)⟩

/-- Ch. 0 §5, p. 142: "`f⁻¹(J)` is divisible by the `m`-th power of the sheaf of ideals of `f⁻¹(D)` on `X'`"
holds exactly when `m ≤ ν(f⁻¹(J)_y)` for the generic point `y` of `f⁻¹(D)`: this is the equivalence of the two
forms of the statement on p. 142 ("we have `m = ν(f⁻¹(J)_y)` for the generic point `y` of `f⁻¹(D)`, or
equivalently, `f⁻¹(J)` is divisible by the `m`-th power of the sheaf of ideals of `f⁻¹(D)`"; see
`MonoidalTransformation.nu_totalTransform_generic_eq` for the equality `m = ν(f⁻¹(J)_y)`).  Here `D = B`, a
non-singular irreducible subscheme, `f⁻¹(B)` is non-singular and irreducible (`isIrreducible_exceptional`),
and the powers of its ideal are primary (`Subscheme.le_nu_generic_iff`).

Deviation from the paper (gap filled): the paper gives no argument. -/
theorem _root_.Hironaka.MonoidalTransformation.totalTransform_le_exceptional_pow_iff {X : Scheme.{u}}
    {B : Subscheme X} [IsAlgebraicScheme X] (hX : X.IsNonsingular) (hBns : B.IsNonsingular)
    (t : MonoidalTransformation X B) {η : t.X'} (hη : IsGenericPoint η t.exceptional.pts)
    (J : Subscheme X) (m : ℕ) :
    Subscheme.totalTransform t.f J ≤ t.exceptional ^ m ↔
      (m : ℕ∞) ≤ Ideal.nu ((Subscheme.totalTransform t.f J).stalkIdeal η) := by
  have hE := t.isNonsingular_and_isNonsingular_exceptional hX hBns
  constructor
  · intro h
    refine (Subscheme.le_nu_generic_iff hE.1 hE.2 hη hη.mem (Subscheme.totalTransform t.f J) m).mpr ?_
    have := Subscheme.le_iff_stalkIdeal_le.mp h η
    rwa [Subscheme.stalkIdeal_pow_eq] at this
  · intro hν
    rw [Subscheme.le_iff_stalkIdeal_le]
    intro y'
    rw [Subscheme.stalkIdeal_pow_eq]
    by_cases hy : y' ∈ t.exceptional.pts
    · exact (Subscheme.le_nu_generic_iff hE.1 hE.2 hη hy _ m).mp hν
    · rw [Subscheme.stalkIdeal_eq_top_of_notMem_pts hy, Ideal.top_pow]
      exact le_top

/-- Ch. 0 §5, p. 142: "If `m = ν(J_x)` for the generic point `x` of `D`, then we have `m = ν(f⁻¹(J)_y)` for the
generic point `y` of `f⁻¹(D)`, or equivalently, `f⁻¹(J)` is divisible by the `m`-th power of the sheaf of
ideals of `f⁻¹(D)` on `X'`." (`D = B` is a non-singular irreducible subscheme of the non-singular
algebraic scheme `X`, `f` the monoidal transformation with center `B`, `J` with `J_x ≠ 0`.)

Both forms hold, and they are equivalent for every `m`
(`MonoidalTransformation.totalTransform_le_exceptional_pow_iff`).

Proof: `f⁻¹(J) ⊆ P_E^m` is Remark 2 of Ch. III (p. 214, `Subscheme.totalTransform_le_exceptional_pow`), which
gives `m ≤ ν(f⁻¹(J)_y)`; if `m + 1 ≤ ν(f⁻¹(J)_y)` then `f⁻¹(J) ⊆ P_E^{m+1}`, hence at `y` over `x' = f(y) ∈ B`:
`J_{x'} ⊆ P_E,y^{m+1} ∩ O_{X,x'} = B_{x'}^{m+1}` (p. 215, `stalkMap_mem_exceptional_pow_iff`) and so
`m + 1 ≤ ν(J_x)` (`Subscheme.le_nu_generic_iff`), contradicting `m = ν(J_x)`.

Deviation from the paper (gap filled): the paper gives no argument. -/
@[blueprint "lem:0.5-weak-transform-order"
  (statement := /-- Let $X$ be a non-singular algebraic scheme, $J$ a coherent sheaf of ideals on $X$, $D$ a
    non-singular irreducible subscheme of $X$ with generic point $x$ such that $J_x\ne0$, and
    $f\colon X'\to X$ the monoidal transformation with center $D$. If $m=\nu(J_x)$, then
    $m=\nu(f^{-1}(J)_y)$ for the generic point $y$ of $f^{-1}(D)$; and $f^{-1}(J)$ is divisible by the $m$-th
    power of the sheaf of ideals of $f^{-1}(D)$ on $X'$. More generally, for every $m$, $f^{-1}(J)$ is
    divisible by the $m$-th power of the sheaf of ideals of $f^{-1}(D)$ if and only if
    $m\le\nu(f^{-1}(J)_y)$. (Ch.~0 \S5, p.~142.)
    \textbf{Gap in the paper filled.} The paper states the equality and the divisibility as equivalent
    forms, without argument. -/)
  (proof := /-- $f^{-1}(J)\subseteq P_E^m$ is Remark~2 of Ch.~III (\cref{rem:III.2-2}), which gives
    $m\le\nu(f^{-1}(J)_y)$. If $m+1\le\nu(f^{-1}(J)_y)$ then $f^{-1}(J)\subseteq P_E^{m+1}$ (the powers of the
    ideal of the non-singular $E$ are primary), hence $J_{x'}\subseteq P_E^{m+1}\mathcal O_{X',y}\cap
    \mathcal O_{X,x'}=B_{x'}^{m+1}$ for $x'=f(y)\in B$ (p.~215), so $m+1\le\nu(J_x)$, a contradiction. -/)
  (latexEnv := "lemma")]
theorem _root_.Hironaka.MonoidalTransformation.nu_totalTransform_generic_eq {X : Scheme.{u}}
    {B : Subscheme X} [IsAlgebraicScheme X] (hX : X.IsNonsingular) (hBns : B.IsNonsingular)
    (t : MonoidalTransformation X B) {η : t.X'} (hη : IsGenericPoint η t.exceptional.pts)
    (J : Subscheme X) {ξ : X} (hξ : IsGenericPoint ξ B.pts) {m : ℕ}
    (hm : Ideal.nu (J.stalkIdeal ξ) = m) :
    Ideal.nu ((Subscheme.totalTransform t.f J).stalkIdeal η) = m ∧
      Subscheme.totalTransform t.f J ≤ t.exceptional ^ m := by
  have hle : Subscheme.totalTransform t.f J ≤ t.exceptional ^ m :=
    Subscheme.totalTransform_le_exceptional_pow hX hBns t J hξ (by rw [hm])
  have hge := (t.totalTransform_le_exceptional_pow_iff hX hBns hη J m).mp hle
  refine ⟨le_antisymm ?_ hge, hle⟩
  by_contra hlt
  have hlt' : ((m + 1 : ℕ) : ℕ∞) ≤ Ideal.nu ((Subscheme.totalTransform t.f J).stalkIdeal η) := by
    rw [not_le] at hlt
    exact_mod_cast Order.add_one_le_of_lt hlt
  have h1 := (t.totalTransform_le_exceptional_pow_iff hX hBns hη J (m + 1)).mpr hlt'
  have hfη := t.mem_pts_of_mem_exceptional hη.mem
  have h2 : J.stalkIdeal (t.f η) ≤ B.stalkIdeal (t.f η) ^ (m + 1) := by
    intro g hg
    refine (MonoidalTransformation.stalkMap_mem_exceptional_pow_iff hX hBns t hη.mem (m + 1) g).mp ?_
    have h3 : t.f.stalkMap η g ∈ (Subscheme.totalTransform t.f J).stalkIdeal η := by
      rw [stalkIdeal_totalTransform]
      exact Ideal.mem_map_of_mem _ hg
    have h4 := Subscheme.le_iff_stalkIdeal_le.mp h1 η
    rw [Subscheme.stalkIdeal_pow_eq] at h4
    exact h4 h3
  have h5 := (Subscheme.le_nu_generic_iff hX hBns hξ hfη J (m + 1)).mpr h2
  rw [hm] at h5
  exact absurd (Nat.cast_le.mp h5) (by omega)

/-- p. 142 for the datum `ℜ` of type II and a non-empty permissible center `B ⊆ S*(ℜ)`: `ν(ℜ) = ν(f⁻¹(J)_y)`
for the generic point `y` of `E'_{α+1} = f⁻¹(B)` (the generic point `x` of `B` has `ν(J_x) = ν(ℜ)`, as `x ∈ S*(ℜ)`),
the equality form of the divisibility `DatumII.Raw.totalTransform_le_exceptional_pow_nu` (`ν = ν(ℜ)`).

Gap in the paper filled: see `MonoidalTransformation.nu_totalTransform_generic_eq`. -/
theorem nu_totalTransform_generic_eq_nu [Hironaka.Cited.IsHironakaBaseIsClosedSingularLocus.{u}] [Hironaka.Cited.CurveFiniteIntegralClosure.{u}] [Hironaka.Cited.IsRegularLocalRingLocalizationOfIsRegularLocalRing.{u}] [IsAlgebraicScheme X] (hX : X.IsNonsingular) (ℜ : Raw X)
    (hℜ : ℜ.IsDatum) (t : MonoidalTransformation X B) (hB : ℜ.IsPermissible B)
    (hne : B.pts.Nonempty) {η : t.X'} (hη : IsGenericPoint η t.exceptional.pts) :
    Ideal.nu ((Subscheme.totalTransform t.f ℜ.J).stalkIdeal η) = ℜ.nu := by
  obtain ⟨hns, hirr⟩ : B.IsNonsingular ∧ B.IsIrreducible := by
    rcases hB.1 with h | h
    · exfalso
      obtain ⟨z, hz⟩ := hne
      rw [h, DatumTransform.pts_empty] at hz
      exact hz
    · exact h
  obtain ⟨ξ, hξ⟩ := Subscheme.exists_isGenericPoint hirr
  have hξS : ξ ∈ ℜ.sStar := hB.2.1 hξ.mem
  have hνξ : ℜ.nuAt ξ = ℜ.nu :=
    le_antisymm (le_iSup₂ (f := fun x (_ : x ∈ ℜ.S) => ℜ.nuAt x) ξ hξS.1) hξS.2
  have hνtop : ℜ.nu ≠ ⊤ := DatumII.Raw.nu_ne_top hX ℜ hℜ.2.2.2
  have hm : Ideal.nu (ℜ.J.stalkIdeal ξ) = (ℜ.nu.toNat : ℕ) := by
    rw [← nuAt, hνξ, ENat.natCast_toNat hνtop]
  rw [(t.nu_totalTransform_generic_eq hX hns hη ℜ.J hξ hm).1, ENat.natCast_toNat hνtop]

/-- p. 176: "the sheaf of ideals `f⁻¹(J)` is divisible by the `ν`-th power of the sheaf of ideals of
`f⁻¹(B)` on `X'`.  The quotient obtained by this division is called the weak transform of `J` by
the monoidal transformation `f`.  This is the kind of transform of a coherent sheaf of ideals that
has appeared in the definition of the transform of a resolution datum of type ℜ_II^N.  (See
Definition 7, §1.)"  For a non-empty center `B` permissible for a datum `ℜ`, the transformed ideal
of `f*(ℜ)` is the weak transform `Subscheme.weakTransform` of `J` (Ch. III, Remark 2, p. 214), the
increasing union of the `f⁻¹(J)P_E^{-ν}`, `ν ≤ ν(J_ξ)`: here `ν(J_ξ) = ν(ℜ)` for the generic point
`ξ` of `B ⊆ S*(ℜ)`, and `J_ξ ≠ 0` by Definition 3 (II)(iii) so that `ν(J_ξ)` is finite
(`rem:III.2-2`). -/
@[blueprint "lem:I.7-II-weak-transform"
  (statement := /-- Let $\mathfrak R$ be a resolution datum of type $\mathfrak R^N_{\mathrm{II}}$ on
    a non-singular algebraic scheme $X$ and $f\colon X'\to X$ the monoidal transformation with a
    non-empty center $B$ permissible for $\mathfrak R$. Then the sheaf of ideals $f^{-1}(J)P^{-\nu}$
    of $f^*(\mathfrak R)$ (Definition~7) is the weak transform of $J$ by $f$
    (\cref{def:III.2-weak-transform-sheaf}). (p.~176: ``This is the kind of transform of a
    coherent sheaf of ideals that has appeared in the definition of the transform of a resolution
    datum of type $\mathfrak R^N_{\mathrm{II}}$. (See Definition~7, \S1.)'') -/)
  (proof := /-- Let $\xi$ be the generic point of $B$. As $B\subseteq S^*(\mathfrak R)$,
    $\nu(J_\xi)=\nu(\mathfrak R)$, which is finite as $J_\xi\ne0$. By \cref{rem:III.2-2},
    the weak transform is $f^{-1}(J)P^{-\nu}$ with $\nu=\nu(J_\xi)$. -/)
  (latexEnv := "lemma")]
theorem transform_J_eq_weakTransform [IsAlgebraicScheme X] (hX : X.IsNonsingular) (ℜ : Raw X)
    (hℜ : ℜ.IsDatum) (t : MonoidalTransformation X B) (hB : ℜ.IsPermissible B)
    (hne : B.pts.Nonempty) : (ℜ.transform t).J = Subscheme.weakTransform t ℜ.J := by
  obtain ⟨hns, hirr⟩ : B.IsNonsingular ∧ B.IsIrreducible := by
    rcases hB.1 with h | h
    · exfalso
      obtain ⟨z, hz⟩ := hne
      rw [h, DatumTransform.pts_empty] at hz
      exact hz
    · exact h
  obtain ⟨ξ, hξ⟩ := Subscheme.exists_isGenericPoint hirr
  have hξS : ξ ∈ ℜ.sStar := hB.2.1 hξ.mem
  have hνξ : ℜ.nuAt ξ = ℜ.nu :=
    le_antisymm (le_iSup₂ (f := fun x (_ : x ∈ ℜ.S) => ℜ.nuAt x) ξ hξS.1) hξS.2
  obtain ⟨-, -, -, h4, -⟩ :=
    MonoidalTransformation.exceptional_isNonsingular_and_totalTransform_le_pow hX hirr hns t ℜ.J
  obtain ⟨k, hk, hweak⟩ := h4 ξ hξ (hℜ.2.2.2 ξ)
  have hkν : ℜ.nu.toNat = k := by
    have : (k : ℕ∞) = ℜ.nu := by rw [← hk, ← hνξ]; rfl
    rw [← this]
    simp
  show Subscheme.divPow _ _ _ = _
  rw [hkν, hweak]

/-- Remark 1 (p. 169) for type II data, with the transformed ideal as printed on p. 168: the tuple
`(E₁',…,E_α', E'_{α+1} | f⁻¹(J)P^{-ν}, b | a₁,…,a_{α+1})` in which the ideal is the quotient `K` of
`f⁻¹(J)` by `P^ν` (any sheaf of ideals `K` with `K·P^ν = f⁻¹(J)`; it is unique, and it is the colon
ideal `(f⁻¹(J) : P^ν)` used in `DatumII.Raw.transform`) is a resolution datum of type II, and `F'`
is a closed restriction of it if `F` is one of `ℜ`.

The hypotheses on `X` are those of `DatumII.Raw.transform_isDatum` (algebraic, non-singular). -/
@[blueprint "rem:I.1-transform-is-datum-II-quotient"
  (statement := /-- Let $\mathfrak R$ be a resolution datum of type $\mathfrak R^N_{\mathrm{II}}$ on
    a non-singular algebraic scheme $X$ and $f\colon X'\to X$ the monoidal transformation with a
    center $B$ permissible for $\mathfrak R$; let $P$ be the sheaf of ideals of
    $E'_{\alpha+1}=f^{-1}(B)$ and $\nu=\nu(\mathfrak R)$. If $K$ is a sheaf of ideals with
    $KP^{\nu}=f^{-1}(J)$, i.e.\ $K=f^{-1}(J)P^{-\nu}$, then
    $\big(E_1',\dots,E_\alpha',E'_{\alpha+1}\,\big|\,K,b\,\big|\,a_1,\dots,a_{\alpha+1}\big)$ is a
    resolution datum of type $\mathfrak R^N_{\mathrm{II}}$ on $X'$ (and $F'$ is a closed restriction
    of it if $F$ is one of $\mathfrak R$). (Remark~1, p.~169, with Definition~7, p.~168.) -/)
  (proof := /-- By \cref{lem:I.7-II-divisible} such a $K$ exists and equals the colon ideal
    $(f^{-1}(J):P^\nu)$ of \cref{def:I.7-II}; apply
    \cref{rem:I.1-transform-is-datum-II}. -/)
  (latexEnv := "proposition")]
theorem transform_isDatum_of_mul_exceptional_pow_eq [Hironaka.Cited.IsHironakaBaseIsClosedSingularLocus.{u}] [Hironaka.Cited.CurveFiniteIntegralClosure.{u}] [Hironaka.Cited.IsRegularLocalRingLocalizationOfIsRegularLocalRing.{u}] [IsAlgebraicScheme X] (hX : X.IsNonsingular)
    (ℜ : Raw X) (hℜ : ℜ.IsDatum) (t : MonoidalTransformation X B) (hB : ℜ.IsPermissible B)
    {K : Subscheme t.X'}
    (hK : K * t.exceptional ^ ℜ.nu.toNat = Subscheme.totalTransform t.f ℜ.J) :
    ({ ℜ.transform t with J := K } : Raw t.X').IsDatum ∧
    (∀ F, ℜ.IsClosedRestriction F → ℜ.IsPermissibleClosed F B →
      ({ ℜ.transform t with J := K } : Raw t.X').IsClosedRestriction
        (Subscheme.strictTransform t F)) ∧
    ℜ.nu ≠ ⊤ := by
  obtain rfl : K = (ℜ.transform t).J :=
    (le_exceptional_pow_and_existsUnique_mul_eq hX ℜ t hB).2.unique hK
      (transform_J_mul_exceptional_pow hX ℜ t hB)
  exact transform_isDatum hX ℜ hℜ t hB

end DatumII.Raw

/-! ### Definition 8: permissible successions and their transforms -/

namespace MonoidalSuccession

variable {X Y : Scheme.{u}}


/-- Transform of an open restriction along a succession. -/
def transformOpen : {X Y : Scheme.{u}} → MonoidalSuccession X Y → Set X → Set Y
  | _, _, nil _, U => U
  | _, _, cons _ t rest, U => rest.transformOpen (DatumI.Raw.transformOpen t U)


@[simp] theorem transformI_nil (ℜ : DatumI.Raw X) : (nil X).transformI ℜ = ℜ := rfl

@[simp] theorem transformI_cons (B : Subscheme X) (t : MonoidalTransformation X B)
    (rest : MonoidalSuccession t.X' Y) (ℜ : DatumI.Raw X) :
    (cons B t rest).transformI ℜ = rest.transformI (ℜ.transform t) := rfl

@[simp] theorem transformOpen_nil (U : Set X) : (nil X).transformOpen U = U := rfl

@[simp] theorem transformOpen_cons (B : Subscheme X) (t : MonoidalTransformation X B)
    (rest : MonoidalSuccession t.X' Y) (U : Set X) :
    (cons B t rest).transformOpen U = rest.transformOpen (DatumI.Raw.transformOpen t U) := rfl

@[simp] theorem transformII_nil (ℜ : DatumII.Raw X) : (nil X).transformII ℜ = ℜ := rfl

@[simp] theorem transformII_cons (B : Subscheme X) (t : MonoidalTransformation X B)
    (rest : MonoidalSuccession t.X' Y) (ℜ : DatumII.Raw X) :
    (cons B t rest).transformII ℜ = rest.transformII (ℜ.transform t) := rfl

/-- Definition 8: a succession `{fᵢ}` is *permissible* for `ℜ` if each `fᵢ` is permissible for
the transform `ℜᵢ` of `ℜ` by the preceding ones. (Type I, no restriction.)

Formalization note (encoding): the paper requires the intermediate `ℜᵢ` to be resolution data;
here permissibility is checked on raw tuples, and that the `ℜᵢ` are data is a lemma
(`transformI_isDatum`, from Remark 1). -/
@[blueprint "def:I.8"
  (statement := /-- A succession of monoidal transformations $f=\{f_i\colon X_{i+1}\to X_i\}$
    with centers $B_i$ is \emph{permissible} for $\mathfrak R$ if there are resolution data
    $\mathfrak R_i$ on $X_i$ with $\mathfrak R_0=\mathfrak R$, $f_i$ permissible for
    $\mathfrak R_i$, and $\mathfrak R_{i+1}=f_i^*(\mathfrak R_i)$. Then
    $f^*(\mathfrak R):=\mathfrak R_m$. (Def.\ 8, p.\ 169.)

    Formalization note (encoding): permissibility is defined recursively on raw tuples; that
    the intermediate $\mathfrak R_i$ are resolution data is \cref{lem:I.8-transform-is-datum}
    (from Remark~1). -/)
  (latexEnv := "definition")]
def IsPermissibleI : {X Y : Scheme.{u}} → MonoidalSuccession X Y → DatumI.Raw X → Prop
  | _, _, nil _, _ => True
  | _, _, cons B t rest, ℜ => ℜ.IsPermissible B ∧ rest.IsPermissibleI (ℜ.transform t)





private theorem transformI_isDatum_of_isAlgebraicScheme [Hironaka.Cited.MonoidalTransformationExistsIsProper.{u}] (s : MonoidalSuccession X Y)
    (hXa : IsAlgebraicScheme X) (hX : X.IsNonsingular) (ℜ : DatumI.Raw X)
    (hℜ : ℜ.IsDatum) (hs : s.IsPermissibleI ℜ) : (s.transformI ℜ).IsDatum := by
  induction s with
  | nil X => exact hℜ
  | cons B t rest ih =>
    exact ih t.isAlgebraicScheme (t.isNonsingular_and_isNonsingular_exceptional hX hs.1.1.isNonsingular).1 (ℜ.transform t)
      (DatumI.Raw.transform_isDatum hX ℜ hℜ t hs.1).1 hs.2

private theorem transformII_isDatum_of_isAlgebraicScheme [Hironaka.Cited.IsHironakaBaseIsClosedSingularLocus.{u}] [Hironaka.Cited.MonoidalTransformationExistsIsProper.{u}] [Hironaka.Cited.CurveFiniteIntegralClosure.{u}] [Hironaka.Cited.IsRegularLocalRingLocalizationOfIsRegularLocalRing.{u}] (s : MonoidalSuccession X Y)
    (hXa : IsAlgebraicScheme X) (hX : X.IsNonsingular) (ℜ : DatumII.Raw X)
    (hℜ : ℜ.IsDatum) (hs : s.IsPermissibleII ℜ) : (s.transformII ℜ).IsDatum := by
  induction s with
  | nil X => exact hℜ
  | cons B t rest ih =>
    exact ih t.isAlgebraicScheme (t.isNonsingular_and_isNonsingular_exceptional hX hs.1.1.isNonsingular).1 (ℜ.transform t)
      (DatumII.Raw.transform_isDatum hX ℜ hℜ t hs.1).1 hs.2

/-- Along a permissible succession every intermediate transform is a datum (iterate
Remark 1). -/
@[blueprint "lem:I.8-transform-is-datum"
  (statement := /-- If $f$ is a permissible succession for a resolution datum $\mathfrak R$,
    then $f^*(\mathfrak R)$ is a resolution datum of the same type. -/)
  (proof := /-- Induction on the length of the succession using Remark 1. -/)
  (latexEnv := "lemma")]
theorem transformI_isDatum [Hironaka.Cited.MonoidalTransformationExistsIsProper.{u}] (s : MonoidalSuccession X Y) [IsAlgebraicScheme X]
    (hX : X.IsNonsingular) (ℜ : DatumI.Raw X)
    (hℜ : ℜ.IsDatum) (hs : s.IsPermissibleI ℜ) : (s.transformI ℜ).IsDatum :=
  transformI_isDatum_of_isAlgebraicScheme s inferInstance hX ℜ hℜ hs

theorem transformII_isDatum [Hironaka.Cited.IsHironakaBaseIsClosedSingularLocus.{u}] [Hironaka.Cited.MonoidalTransformationExistsIsProper.{u}] [Hironaka.Cited.CurveFiniteIntegralClosure.{u}] [Hironaka.Cited.IsRegularLocalRingLocalizationOfIsRegularLocalRing.{u}] (s : MonoidalSuccession X Y) [IsAlgebraicScheme X]
    (hX : X.IsNonsingular) (ℜ : DatumII.Raw X)
    (hℜ : ℜ.IsDatum) (hs : s.IsPermissibleII ℜ) : (s.transformII ℜ).IsDatum :=
  transformII_isDatum_of_isAlgebraicScheme s inferInstance hX ℜ hℜ hs

end MonoidalSuccession

end Hironaka

