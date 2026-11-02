/-
Copyright (c) 2026 Daattavya Aggarwal, Minhyong Kim, Oisin Kim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daattavya Aggarwal, Minhyong Kim, Oisin Kim
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.Order.CompletePartialOrder
public import Architect
public import Hironaka.Compat.LocalizeSuccessionII

/-!
# Resolvability of a raw type II datum (the interface for the lifting of Ch. IV §4, pp. 321-326)

> Thus, applying Theorem `II₂^{N-1}` to the resolution datum `ℜ^{N-1}_II` on `X̃` (without
> restriction), we can prove that there exists a finite permissible succession of monoidal
> transformations of `X_s` for `ℜ(s)`, which induces a permissible succession of monoidal
> transformations of `X̃` for `ℜ^{N-1}_II` and which resolve the datum `ℜ^{N-1}_II`.  (p. 310;
> the same step on p. 322 for Theorems C and D*.)

The only property of the auxiliary datum `ℜ^{N-1}_II = (Ẽ_1, …, Ẽ_α̃ | J̃, b̃ | ã_1, …, ã_α̃)` that
the induction of §4 (the lifting of a resolving succession of `X̃` to `X_s`) needs is that it is
*resolvable*: there is a succession permissible for it after which `S` is empty.  Permissibility,
transforms and `S` are defined for raw tuples, so this notion does not mention `IsDatum`; the
hypothesis "`ℜ^{N-1}_II` is a resolution datum" enters only when Theorem `II₂^{N-1}` produces the
succession.

* `Subscheme.IsNonsingularDivisor`: non-singular and everywhere of codimension one (possibly
  reducible; the empty subscheme is allowed): what remains true of the `Ẽ_j` of p. 321 (the
  irreducibility asserted there is false).
* `DatumII.Raw.IsWeakDatum`: the clauses of `IsDatum` with "non-singular irreducible of
  codimension one" weakened to `IsNonsingularDivisor`.  The Remarks 1--3 of §4 (pp. 321--326) need
  exactly this of the auxiliary datum `ℜ^{N-1}_II`; Theorem `II₂^{N-1}` needs `IsDatum`.
* `DatumII.Raw.Resolvable`: there is a permissible succession `σ` with `S(σ*ℜ) = ∅`
  (`S(ℜ) = ∅` iff `ℜ` is resolved at every point, `resolvedEverywhere_iff_S_eq_empty`).
* `DatumII.Raw.ResolvableLen k`: resolvable by a succession of length exactly `k`;
  `resolvable_iff_exists_resolvableLen`.
* `resolvableLen_pullback_of_surjective`: resolvability is invariant under the pull-back along a
  surjective flat preimmersion (e.g. an isomorphism).
* `resolvableLen_of_sameChar`, `resolvableLen_of_transform_of_center_empty`: resolvability is
  invariant under data with the same characteristics (p. 275), and a monoidal transformation
  with empty center (the identity, p. 295) does not help.
* `resolvableLen_transform_congr`: the transforms of a datum by two monoidal transformations
  with the same center are resolvable by successions of the same length.  The paper uses this
  tacitly: "`X̄_{s+1}`" and the blow-up of `X̃` produced by Theorem `II₂^{N-1}` are two monoidal
  transformations of `X̃` with the same center `B̃`, "the" monoidal transformation (p. 166,
  unique up to isomorphism).

Not in the paper (infrastructure for the formalization).
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace IsLocalRing

namespace Hironaka

universe u

namespace Subscheme

variable {X : Scheme.{u}}

/-- A non-singular subscheme which is everywhere of codimension one (p. 163): a non-singular
divisor, possibly reducible, possibly empty.  The `Ẽ_j` of p. 321 are of this kind; p. 321 also
asserts that they are irreducible, which is false. -/
def IsNonsingularDivisor (E : Subscheme X) : Prop :=
  E.IsNonsingular ∧ E.IsEverywhereOfCodim 1

/-- A non-singular irreducible subscheme of codimension one is a non-singular divisor. -/
theorem IsNonsingularIrreducibleCodimOne.isNonsingularDivisor {E : Subscheme X}
    (hE : E.IsNonsingularIrreducibleCodimOne) : E.IsNonsingularDivisor := by
  rcases hE with rfl | ⟨hns, hirr, hcod⟩
  · refine ⟨Subscheme.isNonsingular_empty, fun x hx => ?_⟩
    simp [Hironaka.DatumTransform.pts_empty] at hx
  · refine ⟨hns, fun x hx => ?_⟩
    rw [Subscheme.codimAt, ← Subscheme.codim_eq_height E hns hirr hx, hcod]
    rfl

end Subscheme

namespace DatumII.Raw

variable {X : Scheme.{u}}

/-- The clauses of Definition 3 (II) that the lifting of §4 uses of the auxiliary datum
`ℜ^{N-1}_II`: `b > 0`, the `E_i` are non-singular divisors (everywhere of codimension one,
possibly reducible), their union has only normal crossings, and `J_x ≠ 0` at every point.  A
resolution datum is a weak datum (`IsDatum.isWeakDatum`); the converse fails exactly when some
`E_i` is reducible. -/
def IsWeakDatum (ℜ : Raw X) : Prop :=
  0 < ℜ.b ∧ (∀ i, (ℜ.E i).IsNonsingularDivisor) ∧ ℜ.eUnion.HasOnlyNormalCrossings ∧
    ∀ x : X, ℜ.J.stalkIdeal x ≠ ⊥

theorem IsDatum.isWeakDatum {ℜ : Raw X} (h : ℜ.IsDatum) : ℜ.IsWeakDatum :=
  ⟨h.1, fun i => (h.2.1 i).isNonsingularDivisor, h.2.2.1, h.2.2.2⟩

/-- `ℜ` is resolvable by a succession of exactly `k` monoidal transformations, each permissible
for the transform of `ℜ` by the preceding ones, with `S` empty at the end. -/
noncomputable def ResolvableLen : ℕ → ∀ {X : Scheme.{u}}, Raw X → Prop
  | 0, _, ℜ => ℜ.S = ∅
  | k + 1, X, ℜ => ∃ (B : Subscheme X) (t : MonoidalTransformation X B),
      ℜ.IsPermissible B ∧ ResolvableLen k (ℜ.transform t)

/-- `ℜ` is *resolvable*: there is a permissible succession `σ` of monoidal transformations with
`S(σ*ℜ) = ∅`, i.e. `σ*ℜ` resolved at every point (`resolvedEverywhere_iff_S_eq_empty`).  This is
what Theorem `II₂^{N-1}` gives for a resolution datum on an `(N-1)`-dimensional scheme. -/
def Resolvable {X : Scheme.{u}} (ℜ : Raw X) : Prop :=
  ∃ (Z : Scheme.{u}) (σ : MonoidalSuccession X Z), σ.IsPermissibleII ℜ ∧ (σ.transformII ℜ).S = ∅

/-- `Resolvable` as the existence of a length. -/
theorem resolvable_iff_exists_resolvableLen {X : Scheme.{u}} (ℜ : Raw X) :
    ℜ.Resolvable ↔ ∃ k, ResolvableLen k ℜ := by
  constructor
  · rintro ⟨Z, σ, hσ, hS⟩
    induction σ with
    | nil X => exact ⟨0, hS⟩
    | cons B t rest ih =>
      obtain ⟨k, hk⟩ := ih (ℜ.transform t) hσ.2 hS
      exact ⟨k + 1, B, t, hσ.1, hk⟩
  · rintro ⟨k, hk⟩
    induction k generalizing X with
    | zero => exact ⟨X, MonoidalSuccession.nil X, trivial, hk⟩
    | succ k ih =>
      obtain ⟨B, t, hp, hrest⟩ := hk
      obtain ⟨Z, σ, hσ, hS⟩ := ih (ℜ.transform t) hrest
      exact ⟨Z, MonoidalSuccession.cons B t σ, ⟨hp, hσ⟩, hS⟩


section Pullback

variable {Y Z : Scheme.{u}} (j : Z ⟶ Y) [Flat j] [IsPreimmersion j]

/-- The union of the pulled-back components is the pull-back of the union. -/
theorem eUnion_pullback (ℜ : Raw Y) :
    (ℜ.pullback j).eUnion = Subscheme.totalTransform j ℜ.eUnion := by
  refine Subscheme.ext_stalkIdeal fun z => ?_
  unfold eUnion
  rw [Hironaka.DatumTransform.stalkIdeal_iInf_fintype, FlatPreimm.stalkIdeal_totalTransform,
    Hironaka.DatumTransform.stalkIdeal_iInf_fintype]
  have h1 : ∀ i, ((ℜ.pullback j).E i).stalkIdeal z =
      ((ℜ.E i).stalkIdeal (j z)).map (FlatPreimm.stalkEquiv j z) := fun i =>
    FlatPreimm.stalkIdeal_totalTransform j (ℜ.E i) z
  simp only [h1]
  rw [← Ideal.map_coe (FlatPreimm.stalkEquiv j z)]
  simp only [← Ideal.map_coe (FlatPreimm.stalkEquiv j z), Ideal.map_comap_of_equiv,
    Ideal.comap_iInf]
  rfl

theorem nu_pullback_eq_of_surjective (hj : Function.Surjective j.base) (ℜ : Raw Y) :
    (ℜ.pullback j).nu = ℜ.nu := by
  refine le_antisymm (nu_pullback_le j ℜ) ?_
  refine iSup₂_le fun x hx => ?_
  obtain ⟨z, rfl⟩ := hj x
  have hz : z ∈ (ℜ.pullback j).S := (mem_S_pullback j ℜ z).mpr hx
  have := le_iSup₂ (f := fun w (_ : w ∈ (ℜ.pullback j).S) => (ℜ.pullback j).nuAt w) z hz
  exact (nuAt_pullback j ℜ z).symm.le.trans this

/-- A permissible center pulls back to a permissible center along a surjective flat
preimmersion. -/
theorem isPermissible_pullback (hj : Function.Surjective j.base) {ℜ : Raw Y} {B : Subscheme Y}
    (hB : ℜ.IsPermissible B) : (ℜ.pullback j).IsPermissible (Subscheme.totalTransform j B) := by
  obtain ⟨hc, hS, hNC⟩ := hB
  refine ⟨DatumI.Raw.isCenter_pullback j hc, fun z hz => ?_, ?_⟩
  · have hjz : j z ∈ B.pts := by
      have : z ∈ (Subscheme.totalTransform j B).pts := hz
      rwa [FlatPreimm.pts_totalTransform] at this
    refine (mem_sNu_pullback j ℜ _ z).mpr ?_
    rw [nu_pullback_eq_of_surjective j hj]
    exact hS hjz
  · intro z hz
    rw [eUnion_pullback]
    have hjz : j z ∈ B.pts := by
      have : z ∈ (Subscheme.totalTransform j B).pts := hz
      rwa [FlatPreimm.pts_totalTransform] at this
    exact (FlatPreimm.hasOnlyNormalCrossingsWithAt_totalTransform_iff j ℜ.eUnion B z).mpr
      (hNC _ hjz)

end Pullback

/-- Total transforms along a surjective flat preimmersion reflect inclusions. -/
theorem _root_.Hironaka.FlatPreimm.totalTransform_le_iff {Y Z : Scheme.{u}} (j : Z ⟶ Y) [Flat j]
    [IsPreimmersion j] (hj : Function.Surjective j.base) {A B : Subscheme Y} :
    Subscheme.totalTransform j A ≤ Subscheme.totalTransform j B ↔ A ≤ B := by
  refine ⟨fun h => Subscheme.le_iff_stalkIdeal_le.mpr fun y => ?_,
    FlatPreimm.totalTransform_mono j⟩
  obtain ⟨z, rfl⟩ := hj y
  have := Subscheme.le_iff_stalkIdeal_le.mp h z
  rw [FlatPreimm.stalkIdeal_totalTransform, FlatPreimm.stalkIdeal_totalTransform] at this
  rw [← Ideal.map_coe (FlatPreimm.stalkEquiv j z),
    ← Ideal.map_coe (FlatPreimm.stalkEquiv j z)] at this
  rw [Ideal.map_comap_of_equiv, Ideal.map_comap_of_equiv] at this
  exact (Ideal.comap_le_comap_iff_of_surjective _ (FlatPreimm.stalkEquiv j z).symm.surjective
    _ _).mp this

/-- **Resolvability is invariant under surjective flat preimmersions** (the pull-back of the
datum; for an isomorphism this is the transport of a resolving succession).  The monoidal
transformations of `Y` are lifted one by one along `j` (`MonoidalTransformation.exists_lift`
with the base change as the transformation of `Z`). -/
theorem resolvableLen_pullback_of_surjective :
    ∀ (k : ℕ) {Y Z : Scheme.{u}} (j : Z ⟶ Y) [Flat j] [IsPreimmersion j],
      Function.Surjective j.base → ∀ ℜ : Raw Y, ResolvableLen k ℜ →
        ResolvableLen k (ℜ.pullback j) := by
  intro k
  induction k with
  | zero =>
    intro Y Z j _ _ hj ℜ h
    show (ℜ.pullback j).S = ∅
    refine Set.eq_empty_iff_forall_notMem.mpr fun z hz => ?_
    have h' : ℜ.S = ∅ := h
    rw [mem_S_pullback j ℜ z, h'] at hz
    exact hz
  | succ k ih =>
    intro Y Z j _ _ hj ℜ hℜ
    obtain ⟨B, t, hp, hrest⟩ := hℜ
    obtain ⟨j', hfl, hpre, hsq, hrange, hexc, hst⟩ := MonoidalTransformation.exists_lift t j
      (rfl : Subscheme.totalTransform j B = Subscheme.totalTransform j B) (t.baseChange j)
    have := hfl
    have := hpre
    have hcont : ∀ i, B.IsContainedIn (ℜ.E i) ↔
        (Subscheme.totalTransform j B).IsContainedIn (Subscheme.totalTransform j (ℜ.E i)) :=
      fun i => ((FlatPreimm.totalTransform_le_iff j hj).trans Iff.rfl).symm
    have hT := pullback_transform_of_lift t j (t.baseChange j) j' hsq hexc hst ℜ hcont
      (nu_pullback_eq_of_surjective j hj ℜ)
    have hj' : Function.Surjective j'.base := by
      rw [← Set.range_eq_univ, hrange, Set.range_eq_univ.mpr hj, Set.preimage_univ]
    refine ⟨_, t.baseChange j, isPermissible_pullback j hj hp, ?_⟩
    rw [← hT]
    exact ih j' hj' (ℜ.transform t) hrest

/-- Two monoidal transformations with the same center give resolvability-equivalent transforms
(they are isomorphic over `X`: `MonoidalTransformation.unique_up_to_iso`). -/
theorem resolvableLen_transform_congr {X : Scheme.{u}} {B : Subscheme X}
    (t t' : MonoidalTransformation X B) (ℜ : Raw X) (k : ℕ) :
    ResolvableLen k (ℜ.transform t) → ResolvableLen k (ℜ.transform t') := by
  intro h
  obtain ⟨j', hfl, hpre, hsq, hrange, hexc, hst⟩ :=
    MonoidalTransformation.exists_lift t (𝟙 X) (Subscheme.totalTransform_id B) t'
  have := hfl
  have := hpre
  have hcont : ∀ i, B.IsContainedIn (ℜ.E i) ↔
      B.IsContainedIn (Subscheme.totalTransform (𝟙 X) (ℜ.E i)) := fun i => by
    rw [Subscheme.totalTransform_id]
  have hν : ((ℜ.pullback (𝟙 X))).nu = ℜ.nu := by rw [pullback_id]
  have hT := pullback_transform_of_lift t (𝟙 X) t' j' hsq hexc hst ℜ hcont hν
  rw [pullback_id] at hT
  have hj' : Function.Surjective j'.base := by
    rw [← Set.range_eq_univ, hrange]
    simp
  rw [← hT]
  exact resolvableLen_pullback_of_surjective k j' hj' _ h

/-- Having the same characteristics (p. 275) is compatible with resolvability. -/
theorem resolvableLen_of_sameChar :
    ∀ (k : ℕ) {X : Scheme.{u}} {ℜ₁ ℜ₂ : Raw X}, SameChar ℜ₁ ℜ₂ → ResolvableLen k ℜ₁ →
      ResolvableLen k ℜ₂ := by
  intro k
  induction k with
  | zero =>
    intro X ℜ₁ ℜ₂ h h1
    show ℜ₂.S = ∅
    rw [← h.S_eq]
    exact h1
  | succ k ih =>
    intro X ℜ₁ ℜ₂ h h1
    obtain ⟨B, t, hp, hrest⟩ := h1
    exact ⟨B, t, h.isPermissible hp, ih (h.transform t) hrest⟩

end DatumII.Raw

namespace MonoidalTransformation

variable {X : Scheme.{u}}

/-- For the empty center the strict transform is the total transform (the exceptional subscheme
is empty, so nothing is divided out). -/
theorem strictTransform_eq_totalTransform_of_center_empty
    (t : MonoidalTransformation X Subscheme.empty) (V : Subscheme X) :
    Subscheme.strictTransform t V = Subscheme.totalTransform t.f V := by
  refine Subscheme.ext_stalkIdeal fun z => ?_
  rw [Subscheme.strictTransform_stalkIdeal]
  have hexc : t.exceptional = ⊤ := Subscheme.totalTransform_top t.f
  rw [hexc, Subscheme.stalkIdeal_top_eq]
  simp only [Ideal.top_pow, Submodule.top_coe, Submodule.colon_univ, iSup_const]

end MonoidalTransformation

namespace DatumII.Raw

variable {X : Scheme.{u}}

/-- A monoidal transformation with empty center changes the resolvability only by an
isomorphism and an empty component: if `ℜ.transform t` is resolvable by `k` transformations, so is
`ℜ`. -/
theorem resolvableLen_of_transform_of_center_empty (t : MonoidalTransformation X Subscheme.empty)
    (ℜ : Raw X) (k : ℕ) (h : ResolvableLen k (ℜ.transform t)) : ResolvableLen k ℜ := by
  have hiso : IsIso t.f := MonoidalTransformation.isIso_of_empty t
  have hexc : Subscheme.totalTransform (𝟙 t.X') t.exceptional = Subscheme.empty := by
    rw [Subscheme.totalTransform_id]
    exact Subscheme.totalTransform_top t.f
  have hst : ∀ V, Subscheme.totalTransform (𝟙 t.X') (Subscheme.strictTransform t V) =
      Subscheme.totalTransform t.f V := fun V => by
    rw [Subscheme.totalTransform_id, MonoidalTransformation.strictTransform_eq_totalTransform_of_center_empty]
  have hsc := sameChar_pullback_transform_of_lift_disjoint t t.f (𝟙 t.X') (Category.id_comp _)
    hexc hst ℜ
  rw [pullback_id] at hsc
  have h2 : ResolvableLen k (ℜ.pullback t.f) := resolvableLen_of_sameChar k hsc h
  have h3 := resolvableLen_pullback_of_surjective k (inv t.f) (by
    intro x
    exact ⟨t.f.base x, by rw [← Scheme.Hom.comp_apply, IsIso.hom_inv_id]; rfl⟩) _ h2
  rwa [← pullback_comp, IsIso.inv_hom_id, pullback_id] at h3

end DatumII.Raw

end Hironaka
