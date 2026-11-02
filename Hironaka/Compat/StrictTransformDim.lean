/-
Copyright (c) 2026 Daattavya Aggarwal, Minhyong Kim, Oisin Kim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daattavya Aggarwal, Minhyong Kim, Oisin Kim
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.KrullDimension.NonZeroDivisors
public import Architect
public import Hironaka.Compat.DimInequality
public import Hironaka.Compat.BlowupDim
public import Hironaka.Compat.ComponentStalk

/-!
# Dimension of a strict transform (Ch. I §1, Remark 1, p. 169)

> Let `W'` be as in Definition 7. Then we have `dim(W') = dim(W) = n`, unless `B` contains an
> irreducible component of `W`.

For a monoidal transformation `f : X' → X` of an algebraic scheme with center `B` and a subscheme
`V ⊆ X` with strict transform `V'`:

* `dim V' ≤ dim V` (`MonoidalTransformation.dim_strictTransform_le`).  Every point of `V'` is a
  specialization of a point `c'` of `V'` off `f⁻¹(B)`, and the closure of `c'` has dimension at
  most that of the closure of `f(c')`: a chain of specializations of `c'` lies in a chart
  `Spec A[I/a]`, and `A[I/a]/q'` is a finitely generated birational extension of `A/q`
  (`q = q' ∩ A`, `a ∉ q'`), so the dimension inequality `dim A[I/a]/q' ≤ dim A/q` (Matsumura 15.5
  with transcendence degree `0`, `Hironaka/Compat/DimInequality.lean`) bounds the length of the
  chain.
* `dim V' = dim V` if no irreducible component of `V` lies in `B`
  (`MonoidalTransformation.dim_strictTransform_eq`): a chain of specializations in `V` starting
  at the generic point `c ∉ B` of a component lifts, starting at the point `c'` over `c`, along
  the closed (proper) map `f`.

Deviation from the paper (gap filled): the paper states the equality without proof; this module
supplies one.  No hypothesis on `X`, `B` or `V` beyond `X` algebraic (noetherian) is needed;
properness of `f` comes from the cited existence theorem `thm:monoidal-transformation-exists`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Order

namespace Hironaka

universe u

/-! ### Heights of points of schemes -/

namespace StrictDim

/-- An inducing map of schemes preserves and reflects the (strict) specialization order. -/
theorem lt_iff_of_isInducing {Y Z : Scheme.{u}} {g : Y → Z} (hg : Topology.IsInducing g)
    {a b : Y} : g a < g b ↔ a < b := by
  simp only [lt_iff_le_not_ge, Scheme.le_iff_specializes, hg.specializes_iff]

/-- An inducing map of schemes is strictly monotone for the specialization order. -/
theorem strictMono_of_isInducing {Y Z : Scheme.{u}} {g : Y → Z} (hg : Topology.IsInducing g) :
    StrictMono g := fun _ _ h => (lt_iff_of_isInducing hg).mpr h

/-- If every strict predecessor of `g a` is the image of a strict predecessor of `a`, then
`height (g a) ≤ height a`. -/
theorem height_le_of_lift {α β : Type*} [Preorder α] [Preorder β] (g : α → β)
    (hlift : ∀ a b, b < g a → ∃ a' < a, g a' = b) (a : α) : height (g a) ≤ height a := by
  suffices h : ∀ n : ℕ, ∀ a, (n : ℕ∞) ≤ height (g a) → (n : ℕ∞) ≤ height a from
    ENat.forall_natCast_le_iff_le.mp fun n hn => h n a hn
  intro n
  induction n with
  | zero => intro a _; simp
  | succ n ih =>
    intro a hn
    have h1 : ¬ height (g a) ≤ n := by
      intro h
      have := hn.trans h
      norm_cast at this
      omega
    rw [height_le_coe_iff] at h1
    push Not at h1
    obtain ⟨b, hb, hbn⟩ := h1
    obtain ⟨a', ha', rfl⟩ := hlift a b hb
    have h2 := ih a' hbn
    calc ((n + 1 : ℕ) : ℕ∞) = (n : ℕ∞) + 1 := by push_cast; rfl
      _ ≤ height a' + 1 := by gcongr
      _ ≤ height a := height_add_one_le ha'

/-- Specializations lift along a specializing (e.g. closed) morphism, so heights can only go up:
`height (f y) ≤ height y`. -/
theorem height_apply_le_of_specializingMap {Y Z : Scheme.{u}} (f : Y ⟶ Z)
    (hf : SpecializingMap f) (y : Y) : height (f y) ≤ height y := by
  refine height_le_of_lift (fun y => f y) (fun a b hb => ?_) y
  rw [lt_iff_le_not_ge, Scheme.le_iff_specializes, Scheme.le_iff_specializes] at hb
  obtain ⟨a', ha', rfl⟩ := hf hb.1
  refine ⟨a', ?_, rfl⟩
  rw [lt_iff_le_not_ge, Scheme.le_iff_specializes, Scheme.le_iff_specializes]
  exact ⟨ha', fun h => hb.2 (h.map f.continuous)⟩

/-- The height of a point of `Spec R` is the coheight of the prime in `PrimeSpectrum R`. -/
theorem height_spec_eq_coheight (R : CommRingCat.{u}) (x : Spec R) :
    height x = coheight (show PrimeSpectrum R from x) := by
  rw [← height_orderIso (specOrderIsoPrimeSpectrum R) x]
  rfl

/-- `coheight q = dim R/q`. -/
theorem coheight_eq_ringKrullDim_quotient {R : Type*} [CommRing R] (q : PrimeSpectrum R) :
    (coheight q : WithBot ℕ∞) = ringKrullDim (R ⧸ q.asIdeal) := by
  rw [ringKrullDim_quotient q.asIdeal, coheight_eq_krullDim_Ici]
  have : PrimeSpectrum.zeroLocus (R := R) (q.asIdeal : Set R) = Set.Ici q := by
    ext x
    exact Iff.rfl
  rw [this]

/-- A strict chain lying in the image of an inducing map lifts. -/
theorem exists_lift_ltSeries {Y Z : Scheme.{u}} {g : Y → Z} (hg : Topology.IsInducing g)
    (q : LTSeries Z) (hq : ∀ i, q i ∈ Set.range g) :
    ∃ z : LTSeries Y, z.length = q.length ∧ g z.last = q.last := by
  choose w hw using hq
  refine ⟨LTSeries.mk q.length w fun i j hij => ?_, rfl, hw (Fin.last _)⟩
  rw [← lt_iff_of_isInducing hg, hw, hw]
  exact q.strictMono hij

/-- `dim Y` is the Krull dimension of the specialization order. -/
theorem scheme_dim_eq_krullDim (Y : Scheme.{u}) : Y.dim = krullDim Y := by
  show (⨆ y : Y, Y.dimAt y) = _
  rw [krullDim_eq_iSup_coheight]
  exact iSup_congr fun y => ringKrullDim_stalk_eq_coheight y

variable {X : Scheme.{u}}

/-- Heights in a closed subscheme are heights in the ambient scheme. -/
theorem height_ι (D : Subscheme X) (z : D.toScheme) : height (D.ι z) = height z := by
  have hind : Topology.IsInducing D.ι := D.ι.isEmbedding.isInducing
  refine (height_eq_of_strictMono _ (strictMono_of_isInducing hind) (fun a b hb => ?_) z).symm
  have hba : D.ι a ⤳ b := Scheme.le_iff_specializes.mp hb.le
  have hbD : b ∈ D.pts := hba.mem_closed D.support.isClosed (Subscheme.mem_pts_ι D a)
  obtain ⟨a', rfl⟩ := Subscheme.exists_ι_eq_of_mem_pts D hbD
  exact ⟨a', (lt_iff_of_isInducing hind).mp hb, rfl⟩

/-- The height of a point `x` of `D` (the dimension of its closure) is at most `dim D`. -/
theorem height_le_dim (D : Subscheme X) {x : X} (hx : x ∈ D.pts) :
    (height x : WithBot ℕ∞) ≤ D.dim := by
  obtain ⟨z, rfl⟩ := Subscheme.exists_ι_eq_of_mem_pts D hx
  rw [height_ι, Subscheme.dim, scheme_dim_eq_krullDim]
  exact height_le_krullDim z

/-- `dim D` is the supremum of the heights of its points. -/
theorem dim_le_of_forall (D : Subscheme X) {d : WithBot ℕ∞}
    (h : ∀ x ∈ D.pts, (height x : WithBot ℕ∞) ≤ d) : D.dim ≤ d := by
  rw [Subscheme.dim, scheme_dim_eq_krullDim, krullDim_eq_iSup_height]
  exact iSup_le fun z => by rw [← height_ι]; exact h _ (Subscheme.mem_pts_ι D z)

end StrictDim

/-! ### Dimension of the strict transform -/

namespace MonoidalTransformation

variable {X : Scheme.{u}} {B : Subscheme X}

open StrictDim

/-- For a point `y` of `X'` over a point outside the center, the closure of `y` has dimension at
most that of the closure of `f(y)`: `height y ≤ height (f y)` (dimension inequality in a chart). -/
theorem height_le_height_apply [IsAlgebraicScheme X] (t : MonoidalTransformation X B)
    {y : t.X'} (hy : t.f y ∉ B.pts) : height y ≤ height (t.f y) := by
  have := IsAlgebraicScheme.isNoetherian X
  refine ENat.forall_natCast_le_iff_le.mp fun n hn => ?_
  obtain ⟨q, hqlast, hqlen⟩ := exists_series_of_le_height y hn
  obtain ⟨U, hxU⟩ := Subscheme.exists_affineOpen_mem (t.f q.head)
  obtain ⟨a, ha, hya⟩ := t.exists_mem_chartOpen U hxU
  have hmem : ∀ i, q i ∈ Set.range (t.chart U ha) := by
    intro i
    rw [t.range_chart U ha]
    have hle : q.head ≤ q i := q.monotone (Fin.zero_le _)
    exact (Scheme.le_iff_specializes.mp hle).mem_open (t.chartOpen U a).isOpen hya
  have := t.isOpenImmersion_chart U ha
  obtain ⟨z, hzlen, hzlast⟩ :=
    exists_lift_ltSeries (t.chart U ha).isOpenEmbedding.isInducing q hmem
  rw [hqlast] at hzlast
  have hU : IsAffineOpen (U : X.Opens) := isAffineOpen_of_mem_affineOpens U
  let φ := algebraMap Γ(X, U) (chartAlgebra (B.ideal U) a)
  let Q : PrimeSpectrum (chartAlgebra (B.ideal U) a) := z.last
  have hbase : t.f y = hU.fromSpec (PrimeSpectrum.comap φ Q) := by
    rw [← hzlast, ← Scheme.Hom.comp_apply, t.chart_f]
    rfl
  have hQa : φ a ∉ Q.asIdeal := by
    intro haQ
    apply hy
    rw [hbase, Subscheme.compStalk_fromSpec_mem_pts_iff B hU]
    intro i hi
    show φ i ∈ Q.asIdeal
    rw [← chartAlgebra.algebraMap_mul_frac hi]
    exact Q.asIdeal.mul_mem_right _ haQ
  have hA : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian U
  have hdim : coheight Q ≤ coheight (PrimeSpectrum.comap φ Q) := by
    have h1 := coheight_eq_ringKrullDim_quotient Q
    have h2 := coheight_eq_ringKrullDim_quotient (PrimeSpectrum.comap φ Q)
    have h3 := DimIneq.ringKrullDim_quotient_chartAlgebra_le Q.asIdeal hQa
    rw [← h1] at h3
    change _ ≤ ringKrullDim (Γ(X, U) ⧸ (PrimeSpectrum.comap φ Q).asIdeal) at h3
    rw [← h2] at h3
    exact_mod_cast h3
  calc (n : ℕ∞) = z.length := by rw [hzlen, hqlen]
    _ ≤ height z.last := length_le_height_last
    _ = coheight Q := height_spec_eq_coheight _ _
    _ ≤ coheight (PrimeSpectrum.comap φ Q) := hdim
    _ = height (show Spec Γ(X, U) from PrimeSpectrum.comap φ Q) :=
        (height_spec_eq_coheight _ _).symm
    _ ≤ height (hU.fromSpec (PrimeSpectrum.comap φ Q)) :=
        height_le_height_apply_of_strictMono _
          (strictMono_of_isInducing hU.fromSpec.isOpenEmbedding.isInducing) _
    _ = height (t.f y) := by rw [hbase]

/-- Remark 1, p. 169: the strict transform has dimension at most that of the subscheme. -/
@[blueprint "compat:strict-transform-dim-le"
  (statement := /-- Let $f\colon X'\to X$ be the monoidal transformation of an algebraic scheme
    $X$ with center $B$, and $V'$ the strict transform of a subscheme $V$. Then
    $\dim V'\le\dim V$. (Used in Remark~1, p.~169.) -/)
  (proof := /-- $\dim V'$ is the supremum of the lengths of chains of specializations in $V'$.
    Every point of $V'$ is a specialization of a point $c'\in V'$ off $f^{-1}(B)$
    (\cref{lem:strict-transform-saturation}). A chain of specializations of $c'$ lies in a chart
    $\operatorname{Spec}A[I/a]$ around its last point (\cref{compat:blowup-charts-cover}), where
    $a\notin\mathfrak q_{c'}$ since $f(c')\notin B$; by
    \cref{compat:chart-quotient-dim} its length is at most $\dim A/(\mathfrak q_{c'}\cap A)$,
    the length of a chain of specializations of $f(c')\in V$. -/)
  (latexEnv := "lemma")]
theorem dim_strictTransform_le [IsAlgebraicScheme X] (t : MonoidalTransformation X B)
    (V : Subscheme X) : (Subscheme.strictTransform t V).dim ≤ V.dim := by
  refine dim_le_of_forall _ fun y hy => ?_
  obtain ⟨q, hqV, hqE, hqy⟩ := t.exists_generization_notMem_exceptional V hy
  have hqB : t.f q ∉ B.pts := by
    rw [t.pts_exceptional] at hqE
    exact hqE
  calc (height y : WithBot ℕ∞) ≤ height q := by
        exact_mod_cast height_mono (Scheme.le_iff_specializes.mpr hqy)
    _ ≤ height (t.f q) := by exact_mod_cast t.height_le_height_apply hqB
    _ ≤ V.dim := height_le_dim V (t.pts_strictTransform_subset V hqV)

/-- Remark 1, p. 169: "`dim(W') = dim(W)`, unless `B` contains an irreducible component of `W`".
-/
@[blueprint "compat:strict-transform-dim-eq"
  (statement := /-- In the situation of \cref{compat:strict-transform-dim-le}, if no irreducible
    component of $V$ is contained in $B$, then $\dim V'=\dim V$. (Remark~1, p.~169.) -/)
  (proof := /-- A chain of specializations in $V$ can be taken to start at the generic point $c$
    of an irreducible component of $V$, and $c\notin B$. Off $B$ the transformation is an
    isomorphism, so there is $c'\in V'$ over $c$. Since $f$ is proper
    (\cref{lem:monoidal-transformation-proper}), it is closed, so specializations of $f(c')$ lift
    to specializations of $c'$, which stay in the closed set $V'$; the lifted chain has the same
    length. Combine with \cref{compat:strict-transform-dim-le}. -/)
  (latexEnv := "lemma")]
theorem dim_strictTransform_eq [Hironaka.Cited.MonoidalTransformationExistsIsProper.{u}] [IsAlgebraicScheme X] (t : MonoidalTransformation X B)
    (V : Subscheme X) (hV : ∀ C ∈ V.irreducibleComponents, ¬ C.pts ⊆ B.pts) :
    (Subscheme.strictTransform t V).dim = V.dim := by
  refine le_antisymm (t.dim_strictTransform_le V) (dim_le_of_forall _ fun x hx => ?_)
  -- an irreducible component `Z` of `V` through `x`, with generic point `c ∉ B`
  have hne : V.stalkIdeal x ≠ ⊤ := Subscheme.mem_pts_iff_stalkIdeal_ne_top.mp hx
  obtain ⟨⟨p, hp⟩⟩ := Ideal.nonempty_minimalPrimes hne
  obtain ⟨C, hC, hxC, -⟩ := Subscheme.exists_mem_irreducibleComponents_of_mem_minimalPrimes V x hp
  have hCB := hV C hC
  obtain ⟨Z, hZ, rfl⟩ := hC
  rw [Subscheme.pts_ofClosed] at hxC hCB
  obtain ⟨c, hc⟩ : ∃ c, IsGenericPoint c (Z : Set X) := QuasiSober.sober hZ.prop.1 Z.isClosed
  have hcx : c ⤳ x := hc.specializes hxC
  have hcV : c ∈ V.pts := hZ.prop.2 hc.mem
  have hcB : c ∉ B.pts := by
    intro hcB
    apply hCB
    rw [← hc.def]
    exact closure_minimal (Set.singleton_subset_iff.mpr hcB) B.support.isClosed
  -- the point `c'` over `c` lies on the strict transform
  obtain ⟨c', rfl⟩ := t.exists_apply_eq_of_notMem hcB
  have hc'E : c' ∉ t.exceptional.pts := by
    rw [t.pts_exceptional]
    exact hcB
  have hc'V : c' ∈ (Subscheme.strictTransform t V).pts :=
    (t.mem_pts_strictTransform_iff_of_notMem V hc'E).mpr hcV
  -- `f` is closed, so specializations of `f(c')` lift to specializations of `c'`
  have := IsAlgebraicScheme.isNoetherian X
  have := t.isProper
  have hsp : SpecializingMap t.f := t.f.isClosedMap.specializingMap
  calc (height x : WithBot ℕ∞) ≤ height (t.f c') := by
        exact_mod_cast height_mono (Scheme.le_iff_specializes.mpr hcx)
    _ ≤ height c' := by exact_mod_cast height_apply_le_of_specializingMap t.f hsp c'
    _ ≤ (Subscheme.strictTransform t V).dim := height_le_dim _ hc'V

end MonoidalTransformation

end Hironaka
