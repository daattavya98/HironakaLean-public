/-
Copyright (c) 2026 Daattavya Aggarwal, Minhyong Kim, Oisin Kim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daattavya Aggarwal, Minhyong Kim, Oisin Kim
-/
module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Architect
public import Hironaka.Ch1.FundamentalTheorems
public import Hironaka.Compat.BlowupBaseChange
public import Hironaka.Statements

/-!
# Compatibility layer for Ch. IV §1: localizing and lifting successions

The four localization theorems of Ch. IV §1 (Propositions 1–4, pp. 278–286) share one
construction.  Given a permissible succession `f : X' → X`, a point `x ∈ X` and the localization
`j : X'_S → X'` (`S = O_{X,x}`), a permissible succession `f̄` of `X'_S` (obtained from the
induction hypothesis on the lower-dimensional scheme `X'_S`) is lifted to a permissible
succession `f'` of `X'`, interleaved with successions whose centers induce the empty subscheme
on `X'_S` ("(1)–(3)" of the proof of Proposition 1, p. 279).  The composite `f ∘ f'` then no
longer sends the relevant closed set to `x`, and since there is no infinite strictly
descending chain of closed subsets of an algebraic scheme, the proposition follows (p. 278).

This file collects the parts of that argument which do not depend on Ch. IV itself:

* dimension at a point along specializations (`dimAt` is the coheight in the specialization
  order), and the finiteness of a closed set all of whose points have maximal dimension;
* the descending-chain argument of p. 278, in an abstract form;
* concatenation of successions of monoidal transformations;
* the pull-back of a type I datum along a flat preimmersion (such as `j : X'_S → X'`), which is
  how Definition 1 (p. 276) localizes a datum, and its compatibility with transforms along
  lifted monoidal transformations (`MonoidalTransformation.exists_lift`,
  `compat:blowup-flat-base-change`) and with permissibility;
* stages `IsStageI N n` of the constructions (ambient scheme of dimension `N`, datum of type
  `ℜ^{N,n}_I`, i.e. `dim W = n` exactly, as in the paper), preserved along permissible
  successions with a closed or an open restriction by Remark 1 of Ch. I (including
  `rem:I.1-dim-W`, "`n' = n` unless `B` contains an irreducible component of `W`", and the
  remark of p. 169 that for a restriction `B` can not contain such a component).  The weaker
  stages `IsGoodDatumI N n` (`dim W ≤ n`) are used by the other files of Ch. IV;
* the lifting construction "(1)–(3)" of p. 279 for type I data with closed or open restriction
  (`LocSucc.lift_succession_closed`, `LocSucc.lift_succession_open`).  Lemma 1 of Ch. IV §1
  (`lem:IV.1-1`), proved in `Hironaka/Ch4/Localization.lean`, enters as the hypothesis
  `Lemma1Holds` (the openness half is also `ResolvedSetIsOpen`, used for type II).

The type II analogues are in `Hironaka/Compat/LocalizeSuccessionII.lean`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

namespace Hironaka

universe u

/-! ### Dimension at a point along specializations -/

namespace LocSucc

open _root_.Order in
/-- `dim_x X` is the coheight of `x` in the specialization order. -/
theorem dimAt_eq_coheight {X : Scheme.{u}} (x : X) : X.dimAt x = (coheight x : WithBot ℕ∞) :=
  ringKrullDim_stalk_eq_coheight x

open _root_.Order in
/-- The dimension at a generization is at most the dimension at the point (`O_{X,w}` is a
localization of `O_{X,x}`). -/
theorem dimAt_le_of_specializes {X : Scheme.{u}} {w x : X} (h : w ⤳ x) :
    X.dimAt w ≤ X.dimAt x := by
  rw [dimAt_eq_coheight, dimAt_eq_coheight]
  exact_mod_cast coheight_anti (Scheme.le_iff_specializes.mpr h)

open _root_.Order in
/-- The dimension at a proper generization is strictly smaller. -/
theorem dimAt_add_one_le_of_specializes {X : Scheme.{u}} {w x : X} (h : w ⤳ x) (hne : w ≠ x) :
    X.dimAt w + 1 ≤ X.dimAt x := by
  rw [dimAt_eq_coheight, dimAt_eq_coheight]
  have hlt : x < w := by
    refine lt_of_le_not_ge (Scheme.le_iff_specializes.mpr h) fun h' => hne ?_
    exact (h.antisymm (Scheme.le_iff_specializes.mp h')).eq
  have := coheight_add_one_le hlt
  exact_mod_cast this

theorem dimAt_le_dim {X : Scheme.{u}} (x : X) : X.dimAt x ≤ X.dim :=
  le_iSup (fun x => X.dimAt x) x

/-- On an algebraic scheme, a closed subset all of whose points have the same finite
dimension `N` is a finite set of (closed) points.  (A point `z` with `dim_z X = N` has no proper
specialization `w`, since `dim_w X ≥ dim_z X + 1`; so every irreducible component of the closed
set is a single point, and there are finitely many of them.)

Gap in the paper filled: this is the step "the Proposition will follow immediately" of p. 278
(and its analogues in Propositions 2–4). -/
theorem finite_of_forall_dimAt_eq {X : Scheme.{u}} [IsAlgebraicScheme X] {N : ℕ} {Z : Set X} (hZ : IsClosed Z)
    (hdim : ∀ z ∈ Z, X.dimAt z = (N : WithBot ℕ∞)) : Z.Finite := by
  have := IsAlgebraicScheme.noetherianSpace X
  -- every point of `Z` is closed
  have hcl : ∀ z ∈ Z, closure ({z} : Set X) = {z} := by
    intro z hz
    refine subset_antisymm (fun w hw => ?_) subset_closure
    have hzw : z ⤳ w := specializes_iff_mem_closure.mpr hw
    have hwZ : w ∈ Z := hzw.mem_closed hZ hz
    by_contra hne
    have h1 := dimAt_add_one_le_of_specializes hzw (Ne.symm hne)
    rw [hdim z hz, hdim w hwZ] at h1
    have h2 : ((N : WithBot ℕ∞) + 1) = ((N + 1 : ℕ) : WithBot ℕ∞) := by norm_cast
    rw [h2] at h1
    have : (N + 1 : ℕ) ≤ N := by exact_mod_cast h1
    omega
  -- `Z` is the union of its finitely many irreducible components, each a point
  have hZn : NoetherianSpace Z := NoetherianSpace.set Z
  have : QuasiSober Z := hZ.isClosedEmbedding_subtypeVal.quasiSober
  have hfin := NoetherianSpace.finite_irreducibleComponents (α := Z)
  have hcomp : ∀ C ∈ irreducibleComponents Z, ∃ z : Z, C = {z} := by
    intro C hC
    have hirr : IsIrreducible C := hC.1
    have hCcl : IsClosed C := isClosed_of_mem_irreducibleComponents C hC
    have h1 : closure ({hirr.genericPoint} : Set Z) = C := hirr.closure_genericPoint hCcl
    refine ⟨hirr.genericPoint, ?_⟩
    refine h1.symm.trans ?_
    have hemb : Topology.IsEmbedding (Subtype.val : Z → X) := Topology.IsEmbedding.subtypeVal
    rw [hemb.isInducing.closure_eq_preimage_closure_image, Set.image_singleton,
      hcl _ hirr.genericPoint.2]
    ext w
    simp [Subtype.ext_iff]
  have huniv : (Set.univ : Set Z).Finite := by
    rw [← sUnion_irreducibleComponents]
    refine Set.Finite.sUnion hfin fun C hC => ?_
    obtain ⟨z, rfl⟩ := hcomp C hC
    exact Set.finite_singleton z
  have : Finite Z := Set.finite_univ_iff.mp huniv
  exact Set.toFinite Z

/-- The descending-chain argument of p. 278 ("in view of the fact that we do not have any
infinite sequence of strictly descending closed subsets on an algebraic scheme"), abstractly:
if every state `s` whose closed set `Z s` contains a bad point `x` can be improved to a state
`s'` with `Z s' ⊆ Z s` and `x ∉ Z s'`, then some state reachable from the initial one has no bad
point at all. -/
theorem exists_forall_not_of_improve {X : Type*} [TopologicalSpace X] [NoetherianSpace X]
    {σ : Type*} (Z : σ → Set X) (hZ : ∀ s, IsClosed (Z s)) (P : X → Prop)
    (himp : ∀ s, ∀ x ∈ Z s, P x → ∃ s', Z s' ⊆ Z s ∧ x ∉ Z s') (s₀ : σ) :
    ∃ s, ∀ x ∈ Z s, ¬ P x := by
  by_contra hcon
  push Not at hcon
  -- the closed sets `Z s` have no minimal element
  have key : ∀ C : Closeds X, ∀ s, (C : Set X) = Z s → False := by
    intro C
    induction C using WellFoundedLT.induction with
    | _ C ih =>
      intro s hs
      obtain ⟨x, hx, hPx⟩ := hcon s
      obtain ⟨s', hs', hxs'⟩ := himp s x hx hPx
      refine ih ⟨Z s', hZ s'⟩ ?_ s' rfl
      refine lt_of_le_of_ne (fun y hy => ?_) fun h => hxs' ?_
      · show y ∈ (C : Set X)
        rw [hs]
        exact hs' hy
      have : Z s' = Z s := by rw [← hs]; exact congrArg (fun C : Closeds X => (C : Set X)) h
      rw [this]
      exact hx
  exact key ⟨Z s₀, hZ s₀⟩ s₀ rfl

end LocSucc

/-! ### Concatenation of successions -/

namespace MonoidalSuccession

/-- The succession `s` followed by the succession `s'` of the last scheme of `s`. -/
def append : {X Y Z : Scheme.{u}} → MonoidalSuccession X Y → MonoidalSuccession Y Z →
    MonoidalSuccession X Z
  | _, _, _, nil _, s' => s'
  | _, _, _, cons B t rest, s' => cons B t (rest.append s')

variable {X Y Z : Scheme.{u}}

@[simp] theorem nil_append (s' : MonoidalSuccession X Z) : (nil X).append s' = s' := rfl

@[simp] theorem cons_append (B : Subscheme X) (t : MonoidalTransformation X B)
    (rest : MonoidalSuccession t.X' Y) (s' : MonoidalSuccession Y Z) :
    (cons B t rest).append s' = cons B t (rest.append s') := rfl

theorem composite_append (s : MonoidalSuccession X Y) (s' : MonoidalSuccession Y Z) :
    (s.append s').composite = s'.composite ≫ s.composite := by
  induction s with
  | nil X => simp
  | cons B t rest ih => simp [ih]

theorem strictTransform_append (s : MonoidalSuccession X Y) (s' : MonoidalSuccession Y Z)
    (V : Subscheme X) : (s.append s').strictTransform V = s'.strictTransform (s.strictTransform V) := by
  induction s with
  | nil X => rfl
  | cons B t rest ih => exact ih s' (Subscheme.strictTransform t V)

theorem transformI_append (s : MonoidalSuccession X Y) (s' : MonoidalSuccession Y Z)
    (ℜ : DatumI.Raw X) : (s.append s').transformI ℜ = s'.transformI (s.transformI ℜ) := by
  induction s with
  | nil X => rfl
  | cons B t rest ih => exact ih s' (ℜ.transform t)

theorem transformII_append (s : MonoidalSuccession X Y) (s' : MonoidalSuccession Y Z)
    (ℜ : DatumII.Raw X) : (s.append s').transformII ℜ = s'.transformII (s.transformII ℜ) := by
  induction s with
  | nil X => rfl
  | cons B t rest ih => exact ih s' (ℜ.transform t)

theorem transformOpen_append (s : MonoidalSuccession X Y) (s' : MonoidalSuccession Y Z)
    (U : Set X) : (s.append s').transformOpen U = s'.transformOpen (s.transformOpen U) := by
  induction s with
  | nil X => rfl
  | cons B t rest ih => exact ih s' (DatumI.Raw.transformOpen t U)

theorem isPermissibleIClosed_append (s : MonoidalSuccession X Y) (s' : MonoidalSuccession Y Z)
    (ℜ : DatumI.Raw X) (F : Subscheme X) :
    (s.append s').IsPermissibleIClosed ℜ F ↔
      s.IsPermissibleIClosed ℜ F ∧ s'.IsPermissibleIClosed (s.transformI ℜ) (s.strictTransform F) := by
  induction s with
  | nil X => simp [IsPermissibleIClosed]
  | cons B t rest ih =>
    simp only [cons_append, IsPermissibleIClosed, transformI_cons, strictTransform_cons, ih, and_assoc]

theorem isPermissibleIOpen_append (s : MonoidalSuccession X Y) (s' : MonoidalSuccession Y Z)
    (ℜ : DatumI.Raw X) (U : Set X) :
    (s.append s').IsPermissibleIOpen ℜ U ↔
      s.IsPermissibleIOpen ℜ U ∧ s'.IsPermissibleIOpen (s.transformI ℜ) (s.transformOpen U) := by
  induction s with
  | nil X => simp [IsPermissibleIOpen]
  | cons B t rest ih =>
    simp only [cons_append, IsPermissibleIOpen, transformI_cons, transformOpen_cons, ih, and_assoc]

theorem isPermissibleII_append (s : MonoidalSuccession X Y) (s' : MonoidalSuccession Y Z)
    (ℜ : DatumII.Raw X) :
    (s.append s').IsPermissibleII ℜ ↔ s.IsPermissibleII ℜ ∧ s'.IsPermissibleII (s.transformII ℜ) := by
  induction s with
  | nil X => simp [IsPermissibleII]
  | cons B t rest ih =>
    simp only [cons_append, IsPermissibleII, transformII_cons, ih, and_assoc]

theorem isPermissibleIIClosed_append (s : MonoidalSuccession X Y) (s' : MonoidalSuccession Y Z)
    (ℜ : DatumII.Raw X) (F : Subscheme X) :
    (s.append s').IsPermissibleIIClosed ℜ F ↔
      s.IsPermissibleIIClosed ℜ F ∧
        s'.IsPermissibleIIClosed (s.transformII ℜ) (s.strictTransform F) := by
  induction s with
  | nil X => simp [IsPermissibleIIClosed]
  | cons B t rest ih =>
    simp only [cons_append, IsPermissibleIIClosed, transformII_cons, strictTransform_cons, ih,
      and_assoc]

/-- A succession permissible for `(ℜ, F)` is permissible for `ℜ`. -/
theorem IsPermissibleIClosed.isPermissibleI {s : MonoidalSuccession X Y} {ℜ : DatumI.Raw X}
    {F : Subscheme X} (h : s.IsPermissibleIClosed ℜ F) : s.IsPermissibleI ℜ := by
  induction s with
  | nil X => trivial
  | cons B t rest ih => exact ⟨h.1.1, ih h.2⟩

/-- A succession permissible for `(ℜ, U)` is permissible for `ℜ`. -/
theorem IsPermissibleIOpen.isPermissibleI {s : MonoidalSuccession X Y} {ℜ : DatumI.Raw X}
    {U : Set X} (h : s.IsPermissibleIOpen ℜ U) : s.IsPermissibleI ℜ := by
  induction s with
  | nil X => trivial
  | cons B t rest ih => exact ⟨h.1.1, ih h.2⟩

/-- A succession permissible for `(ℜ, F)` (type II) is permissible for `ℜ`. -/
theorem IsPermissibleIIClosed.isPermissibleII {s : MonoidalSuccession X Y} {ℜ : DatumII.Raw X}
    {F : Subscheme X} (h : s.IsPermissibleIIClosed ℜ F) : s.IsPermissibleII ℜ := by
  induction s with
  | nil X => trivial
  | cons B t rest ih => exact ⟨h.1.1, ih h.2⟩

/-- The image of a closed set under the composite of a succession of a locally noetherian
scheme is closed (`lem:succession-proper`). -/
theorem isClosed_image_composite [Hironaka.Cited.MonoidalTransformationExistsIsProper.{u}] [IsLocallyNoetherian X] (s : MonoidalSuccession X Y) {T : Set Y}
    (hT : IsClosed T) :
    IsClosed (s.composite.base '' T) := by
  have := s.isProper_composite
  exact s.composite.isClosedMap T hT

/-- The strict transform lies over the subscheme. -/
theorem pts_strictTransform_subset (s : MonoidalSuccession X Y) (V : Subscheme X) :
    (s.strictTransform V).pts ⊆ s.composite.base ⁻¹' V.pts := by
  induction s with
  | nil X => intro y hy; exact hy
  | cons B t rest ih =>
    intro y hy
    have h1 := ih _ hy
    have h2 := MonoidalTransformation.pts_strictTransform_subset t V h1
    simpa [composite_cons] using h2

end MonoidalSuccession

/-! ### Subschemes along flat preimmersions -/

namespace Subscheme

variable {Y : Scheme.{u}}

/-- A reduced subscheme is contained in every subscheme whose points contain its points. -/
theorem isContainedIn_of_pts_subset {D V : Subscheme Y} (hD : D.IsReduced)
    (h : D.pts ⊆ V.pts) : D.IsContainedIn V := by
  have hle : V ≤ D := by
    conv_rhs => rw [Subscheme.eq_ofClosed_support D hD]
    exact (Scheme.IdealSheafData.le_support_iff_le_vanishingIdeal (I := V)
      (Z := D.support)).mp fun y hy => h hy
  exact fun U => hle U

theorem union_empty (A : Subscheme Y) : A.union Subscheme.empty = A := inf_top_eq A

end Subscheme

/-! ### Pull-back of a type I datum -/

namespace DatumI.Raw

variable {Y Z : Scheme.{u}}

/-- The pull-back of a type I raw datum along a morphism `g : Z → Y`: every subscheme is
replaced by its total transform.  For the canonical immersion `j : X'_S → X'` this is the
localized datum `ℜ'_S` of Definition 1 (I), p. 276 (`DatumI.Raw.localize`). -/
noncomputable def pullback (g : Z ⟶ Y) (ℜ : Raw Y) : Raw Z where
  E := Subscheme.totalTransform g ℜ.E
  β := ℜ.β
  V := fun j => Subscheme.totalTransform g (ℜ.V j)
  W := Subscheme.totalTransform g ℜ.W

@[simp] theorem pullback_E (g : Z ⟶ Y) (ℜ : Raw Y) :
    (ℜ.pullback g).E = Subscheme.totalTransform g ℜ.E := rfl
@[simp] theorem pullback_W (g : Z ⟶ Y) (ℜ : Raw Y) :
    (ℜ.pullback g).W = Subscheme.totalTransform g ℜ.W := rfl

theorem mk_eq_mk {X : Scheme.{u}} {E E' : Subscheme X} {β : ℕ} {V V' : Fin β → Subscheme X}
    {W W' : Subscheme X} (hE : E = E') (hV : ∀ j, V j = V' j) (hW : W = W') :
    (⟨E, β, V, W⟩ : Raw X) = ⟨E', β, V', W'⟩ := by
  subst hE hW
  rw [funext hV]

theorem pullback_extendBy (g : Z ⟶ Y) (ℜ : Raw Y) (B : Subscheme Y) :
    (ℜ.extendBy B).pullback g = (ℜ.pullback g).extendBy (Subscheme.totalTransform g B) := by
  refine mk_eq_mk rfl (fun j => ?_) rfl
  refine Fin.lastCases ?_ (fun i => ?_) j
  · simp [extendBy, pullback, Fin.snoc_last]
  · simp [extendBy, pullback, Fin.snoc_castSucc]

theorem transform_extendBy {X : Scheme.{u}} (ℜ : Raw X) {C : Subscheme X}
    (t : MonoidalTransformation X C) (B : Subscheme X) :
    (ℜ.extendBy B).transform t = (ℜ.transform t).extendBy (Subscheme.strictTransform t B) := by
  refine mk_eq_mk rfl (fun j => ?_) rfl
  refine Fin.lastCases ?_ (fun i => ?_) j
  · simp [extendBy, transform, Fin.snoc_last]
  · simp [extendBy, transform, Fin.snoc_castSucc]

theorem pullback_id (ℜ : Raw Y) : ℜ.pullback (𝟙 Y) = ℜ := by
  refine mk_eq_mk ?_ (fun j => ?_) ?_ <;> simp

theorem pullback_comp {Z' : Scheme.{u}} (g : Z ⟶ Y) (g' : Z' ⟶ Z) (ℜ : Raw Y) :
    ℜ.pullback (g' ≫ g) = (ℜ.pullback g).pullback g' := by
  refine mk_eq_mk ?_ (fun j => ?_) ?_ <;> simp [pullback]

variable (g : Z ⟶ Y) [Flat g] [IsPreimmersion g]

/-- Resolvedness is a property of the local rings, which a flat preimmersion preserves. -/
theorem resolvedAt_pullback_iff (ℜ : Raw Y) (hWV : ∀ j, ℜ.W.IsContainedIn (ℜ.V j)) (z : Z) :
    (ℜ.pullback g).ResolvedAt z ↔ ℜ.ResolvedAt (g z) := by
  unfold ResolvedAt
  rw [show (ℜ.pullback g).W = Subscheme.totalTransform g ℜ.W from rfl,
    FlatPreimm.isSimpleAt_totalTransform_iff,
    show (ℜ.pullback g).E = Subscheme.totalTransform g ℜ.E from rfl,
    FlatPreimm.hasOnlyNormalCrossingsWithAt_totalTransform_iff]
  refine and_congr Iff.rfl (and_congr (forall_congr' fun j => ?_) Iff.rfl)
  exact FlatPreimm.isNormallyFlatAlongAt'_totalTransform_iff g _ _ (hWV j) z

/-- The pull-back of a datum along a flat preimmersion is a datum (Remark 1, p. 276). -/
theorem isDatum_pullback {ℜ : Raw Y} (hℜ : ℜ.IsDatum) : (ℜ.pullback g).IsDatum := by
  obtain ⟨hEred, hEcodim, hEnc, hWred, hWV⟩ := hℜ
  refine ⟨FlatPreimm.isReduced_totalTransform g _ hEred, fun z hz => ?_, fun z => ?_,
    FlatPreimm.isReduced_totalTransform g _ hWred,
    fun j U => FlatPreimm.totalTransform_mono g (fun U => hWV j U) U⟩
  · show (Subscheme.totalTransform g ℜ.E).codimAt z = 1
    rw [FlatPreimm.codimAt_totalTransform]
    refine hEcodim _ ?_
    have : z ∈ (Subscheme.totalTransform g ℜ.E).pts := hz
    rwa [FlatPreimm.pts_totalTransform] at this
  · show (Subscheme.totalTransform g ℜ.E).HasOnlyNormalCrossingsWithAt ⊥ z
    have := (FlatPreimm.hasOnlyNormalCrossingsWithAt_totalTransform_iff g ℜ.E ⊥ z).mpr (hEnc _)
    rwa [show Subscheme.totalTransform g (⊥ : Subscheme Y) = ⊥ from
      Scheme.IdealSheafData.comap_bot _] at this

/-- A center pulls back to a center. -/
theorem isCenter_pullback {B : Subscheme Y} (hB : B.IsCenter) :
    (Subscheme.totalTransform g B).IsCenter := by
  rcases hB with rfl | ⟨hns, hirr⟩
  · left
    exact Subscheme.totalTransform_empty g
  · rcases FlatPreimm.empty_or_isIrreducible_totalTransform g B hirr with h | h
    · exact Or.inl h
    · exact Or.inr ⟨FlatPreimm.isNonsingular_totalTransform g B hns, h⟩

/-- Permissibility is inherited by the pull-back along a flat preimmersion. -/
theorem isPermissible_pullback {ℜ : Raw Y} {B : Subscheme Y} (hB : ℜ.IsPermissible B) :
    (ℜ.pullback g).IsPermissible (Subscheme.totalTransform g B) := by
  obtain ⟨hc, hd, hr⟩ := hB
  refine ⟨isCenter_pullback g hc, ?_, fun z hz => ?_⟩
  · rw [← pullback_extendBy]
    exact isDatum_pullback g hd
  · rw [← pullback_extendBy, resolvedAt_pullback_iff g _ hd.2.2.2.2]
    refine hr _ ?_
    have : z ∈ (Subscheme.totalTransform g B).pts := hz
    rwa [FlatPreimm.pts_totalTransform] at this

end DatumI.Raw

/-! ### Transforms along lifted monoidal transformations -/

namespace DatumI.Raw

variable {Y Z : Scheme.{u}}

/-- In a commutative square of monoidal transformations over a flat preimmersion
(`MonoidalTransformation.exists_lift`), the pull-back of the transform is the transform of the
pull-back (Ch. IV §1, p. 276: `h_S` is the monoidal transformation of `X''_S` with center
`B''_S`, and transforms of data are formed from strict transforms and exceptional
subschemes). -/
theorem pullback_transform_of_lift {B : Subscheme Y} (t : MonoidalTransformation Y B)
    (g : Z ⟶ Y) {Bs : Subscheme Z} (ts : MonoidalTransformation Z Bs) (g' : ts.X' ⟶ t.X')
    [Flat g'] [IsPreimmersion g']
    (hexc : Subscheme.totalTransform g' t.exceptional = ts.exceptional)
    (hst : ∀ V, Subscheme.totalTransform g' (Subscheme.strictTransform t V) =
      Subscheme.strictTransform ts (Subscheme.totalTransform g V)) (ℜ : Raw Y) :
    (ℜ.transform t).pullback g' = (ℜ.pullback g).transform ts := by
  refine mk_eq_mk ?_ (fun j => hst _) (hst _)
  show Subscheme.totalTransform g' ((Subscheme.strictTransform t ℜ.E).union t.exceptional) =
    (Subscheme.strictTransform ts (Subscheme.totalTransform g ℜ.E)).union ts.exceptional
  rw [FlatPreimm.totalTransform_union, hst, hexc]

/-- The disjoint case: over a flat preimmersion missing the center, the pull-back of the
transform is the pull-back (the monoidal transformation is an isomorphism there). -/
theorem pullback_transform_of_lift_disjoint {B : Subscheme Y} (t : MonoidalTransformation Y B)
    (g : Z ⟶ Y) (g' : Z ⟶ t.X') [Flat g'] [IsPreimmersion g']
    (hexc : Subscheme.totalTransform g' t.exceptional = Subscheme.empty)
    (hst : ∀ V, Subscheme.totalTransform g' (Subscheme.strictTransform t V) =
      Subscheme.totalTransform g V) (ℜ : Raw Y) :
    (ℜ.transform t).pullback g' = ℜ.pullback g := by
  refine mk_eq_mk ?_ (fun j => hst _) (hst _)
  show Subscheme.totalTransform g' ((Subscheme.strictTransform t ℜ.E).union t.exceptional) =
    Subscheme.totalTransform g ℜ.E
  rw [FlatPreimm.totalTransform_union, hst, hexc, Subscheme.union_empty]

end DatumI.Raw

namespace MonoidalSuccession

variable {X Y Z : Scheme.{u}}

/-- The transform of an open restriction along a succession is its preimage. -/
theorem transformOpen_eq (s : MonoidalSuccession X Y) (U : Set X) :
    s.transformOpen U = s.composite.base ⁻¹' U := by
  induction s with
  | nil X => rfl
  | cons B t rest ih =>
    rw [transformOpen_cons, ih]
    show rest.composite.base ⁻¹' (t.f.base ⁻¹' U) = (rest.composite ≫ t.f).base ⁻¹' U
    rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.preimage_comp]

/-- Transforms commute with adjoining a principal subscheme (Def. 6, 7). -/
theorem transformI_extendBy (s : MonoidalSuccession X Y) (ℜ : DatumI.Raw X) (B : Subscheme X) :
    s.transformI (ℜ.extendBy B) = (s.transformI ℜ).extendBy (s.strictTransform B) := by
  induction s with
  | nil X => rfl
  | cons C t rest ih =>
    rw [transformI_cons, DatumI.Raw.transform_extendBy, ih]
    rfl

/-- "The centers of the succession avoid `R`": the center `B_k` of the `k`-th transformation
has no point in the preimage of `R ⊆ X` in `X_k`. -/
def CentersAvoid : {X Y : Scheme.{u}} → MonoidalSuccession X Y → Set X → Prop
  | _, _, nil _, _ => True
  | _, _, cons B t rest, R => (∀ y ∈ B.pts, y ∉ R) ∧ rest.CentersAvoid (t.f.base ⁻¹' R)

/-- A succession whose centers avoid the range of a flat preimmersion `j : Z → X` lifts it:
`j` factors through the composite by a flat preimmersion `j₁` whose range is the preimage of
that of `j`, and which pulls strict transforms and transforms of data back to the plain
pull-backs (Ch. IV §1, p. 279: "the centers of the `f'_k` induce the empty subscheme of
`(X'_k)_S`"). -/
theorem exists_lift_of_centersAvoid (s : MonoidalSuccession X Y) (j : Z ⟶ X) [Flat j]
    [IsPreimmersion j] (hs : s.CentersAvoid (Set.range j.base)) :
    ∃ j₁ : Z ⟶ Y, Flat j₁ ∧ IsPreimmersion j₁ ∧ j₁ ≫ s.composite = j ∧
      Set.range j₁.base = s.composite.base ⁻¹' Set.range j.base ∧
      (∀ V, Subscheme.totalTransform j₁ (s.strictTransform V) = Subscheme.totalTransform j V) ∧
      ∀ ℜ : DatumI.Raw X, (s.transformI ℜ).pullback j₁ = ℜ.pullback j := by
  induction s with
  | nil X =>
    exact ⟨j, inferInstance, inferInstance, Category.comp_id j, rfl, fun V => rfl, fun ℜ => rfl⟩
  | cons B t rest ih =>
    obtain ⟨hB, hrest⟩ := hs
    obtain ⟨j', hfl, hpre, hj', hr', hexc, hst⟩ :=
      t.exists_lift_of_disjoint j fun z hz => hB _ hz ⟨z, rfl⟩
    rw [← hr'] at hrest
    obtain ⟨j₁, hfl₁, hpre₁, hj₁, hr₁, hst₁, hℜ₁⟩ := ih j' hrest
    refine ⟨j₁, hfl₁, hpre₁, ?_, ?_, fun V => ?_, fun ℜ => ?_⟩
    · rw [composite_cons, ← Category.assoc, hj₁, hj']
    · rw [hr₁, hr', composite_cons, Scheme.Hom.comp_base, TopCat.coe_comp, Set.preimage_comp]
    · rw [strictTransform_cons, hst₁, hst]
    · rw [transformI_cons, hℜ₁, DatumI.Raw.pullback_transform_of_lift_disjoint t j j' hexc hst]

/-- The centers of a succession permissible for `(ℜ, U)` lie over `W − U`; so they avoid any
`R` meeting `W` only inside `U`. -/
theorem centersAvoid_of_isPermissibleIOpen (s : MonoidalSuccession X Y) (ℜ : DatumI.Raw X)
    (U R : Set X) (hs : s.IsPermissibleIOpen ℜ U) (hR : ∀ y ∈ ℜ.W.pts, y ∈ R → y ∈ U) :
    s.CentersAvoid R := by
  induction s with
  | nil X => trivial
  | cons B t rest ih =>
    obtain ⟨⟨-, hBW⟩, hrest⟩ := hs
    refine ⟨fun y hy hyR => (hBW hy).2 (hR y (hBW hy).1 hyR), ih _ _ _ hrest ?_⟩
    intro y hy hyR
    exact hR _ (MonoidalTransformation.pts_strictTransform_subset t ℜ.W hy) hyR

end MonoidalSuccession

/-! ### Centers, containment and irreducibility along successions -/

namespace Subscheme

variable {Y : Scheme.{u}}

theorem pts_empty : (Subscheme.empty : Subscheme Y).pts = ∅ := by
  change ((⊤ : Scheme.IdealSheafData Y).support : Set Y) = ∅
  rw [Scheme.IdealSheafData.support_top]
  rfl

theorem isReduced_empty : (Subscheme.empty : Subscheme Y).IsReduced :=
  Subscheme.isReduced_of_stalk_quot _ fun y hy => by
    rw [pts_empty] at hy
    exact hy.elim

/-- A non-singular subscheme is reduced. -/
theorem isReduced_of_isNonsingular {D : Subscheme Y} (hD : D.IsNonsingular) : D.IsReduced :=
  Subscheme.isReduced_of_stalk_quot _ fun y hy => by
    have := Subscheme.isRegular_stalk_quot D hD hy
    have := isDomain_of_isRegularLocalRing (Y.presheaf.stalk y ⧸ D.stalkIdeal y)
    infer_instance

theorem IsCenter.isReduced {D : Subscheme Y} (hD : D.IsCenter) : D.IsReduced :=
  isReduced_of_isNonsingular hD.isNonsingular

/-- On a non-singular irreducible scheme, a non-singular irreducible subscheme of codimension
one does not contain the generic point (the local ring there is a field, so the ideal of a
subscheme through it has height `0`). -/
theorem genericPoint_notMem_of_codimOne [IrreducibleSpace Y] (hY : Y.IsNonsingular)
    {F : Subscheme Y} (hF : F.IsNonsingularIrreducibleCodimOne) : genericPoint Y ∉ F.pts := by
  intro hη
  have hred : ∀ y : Y, _root_.IsReduced (Y.presheaf.stalk y) := fun y => by
    have : IsRegularLocalRing (Y.presheaf.stalk y) := hY y
    have := isDomain_of_isRegularLocalRing (Y.presheaf.stalk y)
    infer_instance
  have : AlgebraicGeometry.IsReduced Y := isReduced_of_isReduced_stalk Y
  have hfield : IsField (Y.presheaf.stalk (genericPoint Y)) :=
    isField_stalk_of_closure_mem_irreducibleComponents Y (genericPoint Y)
      (by rw [irreducibleComponents_eq_singleton, (genericPoint_spec Y).def]; rfl)
  have := hfield.isDomain
  rcases hF with h | ⟨-, -, hcodim⟩
  · rw [h, pts_empty] at hη
    exact hη
  · have hle : (1 : ℕ∞) ≤ F.codimAt (genericPoint Y) := by
      rw [← hcodim]
      exact iInf₂_le _ hη
    by_cases hI : F.stalkIdeal (genericPoint Y) = ⊥
    · rw [Subscheme.codimAt, hI, Ideal.height_eq_zero_iff_eq_bot.mpr rfl] at hle
      exact absurd hle (by norm_num)
    · obtain ⟨a, haI, ha⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI
      obtain ⟨b, hb⟩ := hfield.mul_inv_cancel ha
      have htop := Ideal.eq_top_of_isUnit_mem _ haI (IsUnit.of_mul_eq_one b hb)
      have := stalkIdeal_le_maximalIdeal_of_mem_pts F hη
      rw [htop, top_le_iff] at this
      exact (IsLocalRing.maximalIdeal.isMaximal _).ne_top this

theorem pts_ne_univ_of_codimOne [IrreducibleSpace Y] (hY : Y.IsNonsingular)
    {F : Subscheme Y} (hF : F.IsNonsingularIrreducibleCodimOne) : F.pts ≠ Set.univ := fun h =>
  genericPoint_notMem_of_codimOne hY hF (h ▸ Set.mem_univ _)

end Subscheme

namespace DatumI.Raw

variable {Y : Scheme.{u}}

/-- The empty subscheme is permissible for every datum (with any closed restriction). -/
theorem isPermissibleClosed_empty {ℜ : Raw Y} (hℜ : ℜ.IsDatum) (F : Subscheme Y) :
    ℜ.IsPermissibleClosed F Subscheme.empty := by
  obtain ⟨h1, h2, h3, -, -⟩ := hℜ
  refine ⟨⟨Or.inl rfl, ⟨h1, h2, h3, Subscheme.isReduced_empty, fun j U => le_top⟩, fun y hy => ?_⟩,
    fun y hy => ?_⟩
  · have : y ∈ (Subscheme.empty : Subscheme Y).pts := hy
    rw [Subscheme.pts_empty] at this
    exact this.elim
  · rw [Subscheme.pts_empty] at hy
    exact hy.elim

/-- A center permissible for `(E; V, W; B)` is permissible for `(E; V; W)` and lies in `B`. -/
theorem isPermissible_of_extendBy {ℜ : Raw Y} {B C : Subscheme Y}
    (h : (ℜ.extendBy B).IsPermissible C) : ℜ.IsPermissible C ∧ C.pts ⊆ B.pts := by
  obtain ⟨hc, ⟨h1, h2, h3, h4, h5⟩, hr⟩ := h
  have hCV : ∀ j : Fin (ℜ.β + 1), C.IsContainedIn ((ℜ.extendBy C).V j) := fun j => by
    have := h5 (Fin.castSucc j)
    simpa [extendBy, Fin.snoc_castSucc] using this
  refine ⟨⟨hc, ⟨h1, h2, h3, h4, hCV⟩, fun y hy => ?_⟩, ?_⟩
  · obtain ⟨hs, hnf, hnc⟩ := hr y hy
    refine ⟨hs, fun j => ?_, hnc⟩
    have := hnf (Fin.castSucc j)
    have e : ((ℜ.extendBy B).extendBy C).V (Fin.castSucc j) = (ℜ.extendBy C).V j := by
      simp only [extendBy]
      exact Fin.snoc_castSucc (α := fun _ => Subscheme Y) _ _ _
    rw [e] at this
    exact this
  · have := h5 (Fin.last _)
    simp only [extendBy, Fin.snoc_last] at this
    exact pts_subset_of_isContainedIn this

end DatumI.Raw

namespace MonoidalSuccession

variable {X Y Z : Scheme.{u}}

/-- Containment of subschemes is preserved by strict transforms along a succession. -/
theorem isContainedIn_strictTransform (s : MonoidalSuccession X Y) {V W : Subscheme X}
    (h : W.IsContainedIn V) : (s.strictTransform W).IsContainedIn (s.strictTransform V) := by
  induction s with
  | nil X => exact h
  | cons B t rest ih => exact ih (MonoidalTransformation.isContainedIn_strictTransform t h)

/-- A succession permissible for `((E; V, W; B''), U'')` whose principal subscheme `B''` lies in
`W ∩ F` is permissible for `((E; V; W), F)` (p. 280: "as is easily seen, the succession `h` is
permissible for the resolution datum `_bℜ'`"). -/
theorem isPermissibleIClosed_of_isPermissibleIOpen_extendBy (s : MonoidalSuccession X Y)
    (ℜ : DatumI.Raw X) (B F : Subscheme X) (U : Set X)
    (hs : s.IsPermissibleIOpen (ℜ.extendBy B) U) (hBW : B.IsContainedIn ℜ.W)
    (hBF : B.IsContainedIn F) : s.IsPermissibleIClosed ℜ F := by
  induction s with
  | nil X => trivial
  | cons C t rest ih =>
    obtain ⟨⟨hC, hCW⟩, hrest⟩ := hs
    obtain ⟨hCperm, hCB⟩ := DatumI.Raw.isPermissible_of_extendBy hC
    refine ⟨⟨hCperm, fun y hy => ?_⟩, ?_⟩
    · exact ⟨pts_subset_of_isContainedIn hBW (hCB hy), pts_subset_of_isContainedIn hBF (hCB hy)⟩
    · rw [DatumI.Raw.transform_extendBy] at hrest
      exact ih (ℜ.transform t) (Subscheme.strictTransform t B) (Subscheme.strictTransform t F)
        _ hrest (MonoidalTransformation.isContainedIn_strictTransform t hBW)
        (MonoidalTransformation.isContainedIn_strictTransform t hBF)

/-- Strict transforms of an irreducible subscheme meeting the range of a flat preimmersion
along a succession whose centers avoid that range stay irreducible (p. 280: `B*` is
irreducible). -/
theorem strictTransform_isIrreducible_of_centersAvoid (s : MonoidalSuccession X Y)
    (j : Z ⟶ X) [Flat j] [IsPreimmersion j] (hs : s.CentersAvoid (Set.range j.base))
    (V : Subscheme X) (hV : V.IsIrreducible) (hne : (Subscheme.totalTransform j V).pts.Nonempty) :
    (s.strictTransform V).IsIrreducible := by
  induction s with
  | nil X => exact hV
  | cons B t rest ih =>
    obtain ⟨hB, hrest⟩ := hs
    obtain ⟨z, hz⟩ := hne
    rw [FlatPreimm.pts_totalTransform] at hz
    have hVB : ¬ V.pts ⊆ B.pts := fun h => hB _ (h hz) ⟨z, rfl⟩
    obtain ⟨j', hfl, hpre, -, hr', -, hst⟩ :=
      t.exists_lift_of_disjoint j fun z hz => hB _ hz ⟨z, rfl⟩
    rw [← hr'] at hrest
    refine ih j' hrest _ (MonoidalTransformation.strictTransform_isIrreducible t V hV hVB) ?_
    rw [hst, FlatPreimm.pts_totalTransform]
    exact ⟨z, hz⟩


theorem IsPermissibleI.hasNonsingularCenters {s : MonoidalSuccession X Y} {ℜ : DatumI.Raw X}
    (h : s.IsPermissibleI ℜ) : s.HasNonsingularCenters := by
  induction s with
  | nil X => trivial
  | cons B t rest ih => exact ⟨h.1.1.isNonsingular, ih h.2⟩

theorem IsPermissibleII.hasNonsingularCenters {s : MonoidalSuccession X Y} {ℜ : DatumII.Raw X}
    (h : s.IsPermissibleII ℜ) : s.HasNonsingularCenters := by
  induction s with
  | nil X => trivial
  | cons B t rest ih => exact ⟨h.1.1.isNonsingular, ih h.2⟩

/-- Along a succession of monoidal transformations of a non-singular scheme with non-singular
centers, `dim_{y} X_m ≤ dim_{f(y)} X` (iterating `MonoidalTransformation.dimAt_le`). -/
theorem dimAt_le_composite (s : MonoidalSuccession X Y) (hX : X.IsNonsingular)
    (hs : s.HasNonsingularCenters) (y : Y) : Y.dimAt y ≤ X.dimAt (s.composite y) := by
  induction s with
  | nil X => exact le_rfl
  | cons B t rest ih =>
    obtain ⟨hB, hrest⟩ := hs
    refine (ih (t.isNonsingular_and_isNonsingular_exceptional hX hB).1 hrest y).trans ?_
    rw [composite_cons, Scheme.Hom.comp_apply]
    exact MonoidalTransformation.dimAt_le hX hB t _

end MonoidalSuccession

/-! ### Irreducibility of the localization -/

/-- If `j : Z → Y` is a flat preimmersion into an irreducible scheme and `Z` is non-empty, then
`Z` is irreducible: its range is closed under generization, hence contains the generic point of
`Y`, of which all its points are specializations (p. 275: "if `Y'` is irreducible, then `Y'_S`
is irreducible"). -/
theorem irreducibleSpace_of_flat_preimmersion {Y Z : Scheme.{u}} [IrreducibleSpace Y]
    (j : Z ⟶ Y) [Flat j] [IsPreimmersion j] [Nonempty Z] : IrreducibleSpace Z := by
  obtain ⟨z⟩ := ‹Nonempty Z›
  have hη : genericPoint Y ∈ Set.range j.base :=
    FlatPreimm.mem_range_of_specializes j (genericPoint_specializes _) ⟨z, rfl⟩
  have hr : IsIrreducible (Set.range j.base) := by
    refine ⟨⟨_, hη⟩, fun u v hu hv ⟨a, ha, hau⟩ ⟨b, hb, hbv⟩ => ?_⟩
    exact ⟨genericPoint Y, hη, (genericPoint_specializes a).mem_open hu hau,
      (genericPoint_specializes b).mem_open hv hbv⟩
  have := Subtype.irreducibleSpace hr
  let e := j.isEmbedding.toHomeomorph
  have h2 := (IrreducibleSpace.isIrreducible_univ (Set.range j.base)).image e.symm
    e.symm.continuous.continuousOn
  rw [Set.image_univ, e.symm.surjective.range_eq] at h2
  exact (irreducibleSpace_def _).mpr h2

/-! ### Dimensions along flat preimmersions and of closed subsets -/

namespace LocSucc

/-- An element `d ≠ ⊥` of `WithBot ℕ∞` with `d + 1 ≤ n` is a natural number `< n`. -/
theorem exists_nat_of_add_one_le {d : WithBot ℕ∞} {n : ℕ} (hne : d ≠ ⊥)
    (h : d + 1 ≤ (n : WithBot ℕ∞)) : ∃ m : ℕ, d = m ∧ m < n := by
  induction d using WithBot.recBotCoe with
  | bot => exact absurd rfl hne
  | coe e =>
    induction e using ENat.recTopCoe with
    | top =>
      exfalso
      have h' : ((⊤ + 1 : ℕ∞) : WithBot ℕ∞) ≤ ((n : ℕ∞) : WithBot ℕ∞) := by exact_mod_cast h
      rw [WithBot.coe_le_coe, top_add, top_le_iff] at h'
      exact ENat.natCast_ne_top n h'
    | coe m =>
      refine ⟨m, rfl, ?_⟩
      have h' : ((m + 1 : ℕ) : WithBot ℕ∞) ≤ (n : WithBot ℕ∞) := by exact_mod_cast h
      have : m + 1 ≤ n := by exact_mod_cast h'
      omega

theorem topologicalKrullDim_univ (Y : Type*) [TopologicalSpace Y] :
    topologicalKrullDim (Set.univ : Set Y) = topologicalKrullDim Y :=
  IsHomeomorph.topologicalKrullDim_eq _ (Homeomorph.Set.univ Y).isHomeomorph

/-- A non-empty closed subset `T` of a scheme all of whose points are proper specializations of
a point `c ∉ T` has dimension `< dim Y`. -/
theorem topologicalKrullDim_add_one_le_dim {Y : Scheme.{u}} {T : Set Y} (hT : IsClosed T)
    (hTne : T.Nonempty) {c : Y} (hcT : c ∉ T) (hc : ∀ t ∈ T, c ⤳ t) :
    topologicalKrullDim T + 1 ≤ Y.dim := by
  rw [Scheme.dim_eq_topologicalKrullDim, ← topologicalKrullDim_univ Y]
  exact topologicalKrullDim_add_one_le hT (Set.subset_univ T) hTne (Set.mem_univ c) hcT hc

/-- A subscheme which is not everything has dimension `< dim Y` on an irreducible scheme. -/
theorem dim_add_one_le_of_pts_ne_univ {Y : Scheme.{u}} [IrreducibleSpace Y] {D : Subscheme Y}
    (hD : D.pts ≠ Set.univ) (hne : D.pts.Nonempty) : D.dim + 1 ≤ Y.dim := by
  rw [Subscheme.dim_eq_topologicalKrullDim]
  refine topologicalKrullDim_add_one_le_dim D.support.isClosed hne (c := genericPoint Y) ?_
    fun t _ => genericPoint_specializes t
  intro h
  apply hD
  refine Set.eq_univ_of_forall fun y => ?_
  exact (genericPoint_specializes y).mem_closed D.support.isClosed h

section FlatPreimm

variable {Y Z : Scheme.{u}} (j : Z ⟶ Y) [Flat j] [IsPreimmersion j]

theorem dimAt_eq (z : Z) : Z.dimAt z = Y.dimAt (j z) :=
  (ringKrullDim_eq_of_ringEquiv (FlatPreimm.stalkEquiv j z)).symm

include j in
theorem isNonsingular (hY : Y.IsNonsingular) : Z.IsNonsingular := fun z => by
  have : IsRegularLocalRing (Y.presheaf.stalk (j z)) := hY (j z)
  exact IsRegularLocalRing.of_ringEquiv (FlatPreimm.stalkEquiv j z)

omit [Flat j] in
theorem dim_totalTransform_le (D : Subscheme Y) :
    (Subscheme.totalTransform j D).dim ≤ D.dim := by
  rw [Subscheme.dim_eq_topologicalKrullDim, Subscheme.dim_eq_topologicalKrullDim,
    FlatPreimm.pts_totalTransform]
  exact (j.isEmbedding.isInducing.restrictPreimage D.pts).topologicalKrullDim_le

theorem dim_le_of_forall {d : WithBot ℕ∞} (h : ∀ z : Z, Y.dimAt (j z) ≤ d) : Z.dim ≤ d :=
  iSup_le fun z => (dimAt_eq j z).trans_le (h z)

end FlatPreimm

/-- The generic point of an irreducible scheme lies on no subscheme of smaller dimension. -/
theorem genericPoint_notMem_of_dim_lt {Y : Scheme.{u}} [IrreducibleSpace Y] {D : Subscheme Y}
    (h : D.dim < Y.dim) : genericPoint Y ∉ D.pts := by
  intro hη
  have hD : D.pts = Set.univ := Set.eq_univ_of_forall fun y =>
    (genericPoint_specializes y).mem_closed D.support.isClosed hη
  rw [Subscheme.dim_eq_topologicalKrullDim, hD, topologicalKrullDim_univ,
    ← Scheme.dim_eq_topologicalKrullDim] at h
  exact lt_irrefl _ h

end LocSucc

namespace MonoidalSuccession

variable {X Y : Scheme.{u}}

theorem transformI_W (s : MonoidalSuccession X Y) (ℜ : DatumI.Raw X) :
    (s.transformI ℜ).W = s.strictTransform ℜ.W := by
  induction s with
  | nil X => rfl
  | cons B t rest ih => exact ih (ℜ.transform t)

end MonoidalSuccession

/-! ### Stages of a permissible succession -/

/-- A *weak* stage of the constructions of Ch. IV §1 for type I data: an ambient scheme of
dimension `N` carrying a datum whose principal subscheme has dimension at most `n`.  Stages are
preserved by permissible monoidal transformations: the ambient scheme by Remark 1 of Ch. I
(`rem:I.1-dim`), the datum by `rem:I.1-transform-is-datum-I`, and the bound on `dim W` by
`rem:I.1-dim-W`.

This is the notion used by the other files of Ch. IV.  The proofs of Propositions 1 and 2
(pp. 278–281) carry the printed `dim(_bW') = n` instead: `IsStageI`, which implies this one
(`IsStageI.isGoodDatumI`). -/
def IsGoodDatumI (N n : ℕ) (Y : Scheme.{u}) (ℜ : DatumI.Raw Y) : Prop :=
  IsAmbient Y N ∧ ℜ.IsDatum ∧ ℜ.W.dim ≤ (n : WithBot ℕ∞)

namespace IsGoodDatumI

variable {N n : ℕ}

theorem transform_closed [Hironaka.Cited.MonoidalTransformationExistsIsProper.{u}] {Y : Scheme.{u}}
    {ℜ : DatumI.Raw Y} (h : IsGoodDatumI N n Y ℜ) {F : Subscheme Y} (hF : ℜ.IsClosedRestriction F)
    {B : Subscheme Y} (hB : ℜ.IsPermissibleClosed F B) (t : MonoidalTransformation Y B) :
    IsGoodDatumI N n t.X' (ℜ.transform t) ∧
      (ℜ.transform t).IsClosedRestriction (Subscheme.strictTransform t F) := by
  obtain ⟨hY, hℜ, hW⟩ := h
  have := hY.1
  have := hY.2.2.1
  have hBX : B.pts ≠ Set.univ := fun hB' =>
    Subscheme.pts_ne_univ_of_codimOne hY.2.1 hF.1
      (Set.eq_univ_of_univ_subset (hB' ▸ fun y hy => (hB.2 hy).2))
  obtain ⟨h1, h2, h3, h4⟩ := MonoidalTransformation.transform_isAmbient hY.2.1 hB.1.1 hBX t
  have hT := DatumI.Raw.transform_isDatum hY.2.1 ℜ hℜ t hB.1
  refine ⟨⟨⟨h1, h2, h3, h4.trans hY.2.2.2⟩, hT.1, ?_⟩, hT.2.1 F hF hB⟩
  exact (DatumI.Raw.dim_transform_W hY.2.1 ℜ hℜ t hB.1).1.trans hW

theorem transform_open [Hironaka.Cited.MonoidalTransformationExistsIsProper.{u}] {Y : Scheme.{u}}
    {ℜ : DatumI.Raw Y} (h : IsGoodDatumI N n Y ℜ) {U : Set Y} (hU : ℜ.IsOpenRestriction U)
    {B : Subscheme Y} (hB : ℜ.IsPermissibleOpen U B) (t : MonoidalTransformation Y B) :
    IsGoodDatumI N n t.X' (ℜ.transform t) ∧
      (ℜ.transform t).IsOpenRestriction (DatumI.Raw.transformOpen t U) := by
  obtain ⟨hY, hℜ, hW⟩ := h
  have := hY.1
  have := hY.2.2.1
  have hBX : B.pts ≠ Set.univ := by
    intro hB'
    obtain ⟨y⟩ : Nonempty Y := inferInstance
    have hWU : ∀ z, z ∉ U := fun z hz =>
      ((hB.2 (hB' ▸ Set.mem_univ z)).2) hz
    have hWu : ℜ.W.pts = Set.univ := Set.eq_univ_of_forall fun z => (hB.2 (hB' ▸ Set.mem_univ z)).1
    have := hU.2.1 (hWu ▸ Set.mem_univ y)
    rw [Set.eq_empty_of_forall_notMem hWU, closure_empty] at this
    exact this
  obtain ⟨h1, h2, h3, h4⟩ := MonoidalTransformation.transform_isAmbient hY.2.1 hB.1.1 hBX t
  have hT := DatumI.Raw.transform_isDatum hY.2.1 ℜ hℜ t hB.1
  refine ⟨⟨⟨h1, h2, h3, h4.trans hY.2.2.2⟩, hT.1, ?_⟩, hT.2.2 U hU hB⟩
  exact (DatumI.Raw.dim_transform_W hY.2.1 ℜ hℜ t hB.1).1.trans hW

theorem succession_closed [Hironaka.Cited.MonoidalTransformationExistsIsProper.{u}] {X Y : Scheme.{u}}
    (s : MonoidalSuccession X Y) {ℜ : DatumI.Raw X} (h : IsGoodDatumI N n X ℜ) {F : Subscheme X}
    (hF : ℜ.IsClosedRestriction F) (hs : s.IsPermissibleIClosed ℜ F) :
    IsGoodDatumI N n Y (s.transformI ℜ) ∧ (s.transformI ℜ).IsClosedRestriction (s.strictTransform F) := by
  induction s with
  | nil X => exact ⟨h, hF⟩
  | cons B t rest ih =>
    obtain ⟨h', hF'⟩ := transform_closed h hF hs.1 t
    exact ih h' hF' hs.2

theorem succession_open [Hironaka.Cited.MonoidalTransformationExistsIsProper.{u}] {X Y : Scheme.{u}}
    (s : MonoidalSuccession X Y) {ℜ : DatumI.Raw X} (h : IsGoodDatumI N n X ℜ) {U : Set X}
    (hU : ℜ.IsOpenRestriction U) (hs : s.IsPermissibleIOpen ℜ U) :
    IsGoodDatumI N n Y (s.transformI ℜ) ∧ (s.transformI ℜ).IsOpenRestriction (s.transformOpen U) := by
  induction s with
  | nil X => exact ⟨h, hU⟩
  | cons B t rest ih =>
    obtain ⟨h', hU'⟩ := transform_open h hU hs.1 t
    exact ih h' hU' hs.2

end IsGoodDatumI

/-! ### Remark 1 (p. 169): for a restriction, a permissible center contains no component of `W` -/

namespace Subscheme

variable {Y : Scheme.{u}}

/-- The subscheme defined by an irreducible closed subset `D.pts` has `D.pts` as an irreducible
component. -/
theorem ofClosed_mem_irreducibleComponents_of_isIrreducible {D : Subscheme Y}
    (hD : _root_.IsIrreducible D.pts) :
    Subscheme.ofClosed ⟨D.pts, D.support.isClosed⟩ ∈ D.irreducibleComponents :=
  ⟨⟨D.pts, D.support.isClosed⟩, ⟨⟨hD, subset_rfl⟩, fun _ hy _ => hy.2⟩, rfl⟩

/-- The points of `ofClosed Z` are the points of `Z`. -/
theorem mem_pts_ofClosed {Z : Closeds Y} {y : Y} : y ∈ (Subscheme.ofClosed Z).pts ↔ y ∈ Z := by
  change y ∈ ((Scheme.IdealSheafData.vanishingIdeal Z).support : Set Y) ↔ _
  rw [Scheme.IdealSheafData.coe_support_vanishingIdeal]
  rfl

/-- If the closed subscheme `W` lies in the closure of its part `O ∩ W` in an open set `O`, then
every irreducible component of `W` has a point in `O`: the generic point `ξ` of the component is
a specialization of a point `κ ∈ O ∩ W`, and the maximality of the component gives `κ ∈ C`. -/
theorem exists_mem_of_mem_irreducibleComponents [IsAlgebraicScheme Y] {W C : Subscheme Y}
    {O : Set Y} (hO : IsOpen O) (hW : W.pts ⊆ closure (O ∩ W.pts))
    (hC : C ∈ W.irreducibleComponents) : ∃ κ ∈ O, κ ∈ C.pts := by
  obtain ⟨Z, ⟨⟨hZirr, hZW⟩, hZmax⟩, rfl⟩ := hC
  set ξ := hZirr.genericPoint with hξdef
  have hξZ : closure {ξ} = (Z : Set Y) := by
    rw [(hZirr.isGenericPoint_genericPoint_closure).def, Z.isClosed.closure_eq]
  have hξmem : ξ ∈ (Z : Set Y) := hξZ ▸ subset_closure rfl
  obtain ⟨κ, ⟨hκO, hκW⟩, hκξ⟩ := exists_specializes_of_mem_closure hO W.support.isClosed
    (hW (hZW hξmem))
  have hξκ : ξ ∈ closure {κ} := specializes_iff_mem_closure.mp hκξ
  have hmax := hZmax (y := ⟨closure {κ}, isClosed_closure⟩)
    ⟨isIrreducible_singleton.closure,
      closure_minimal (Set.singleton_subset_iff.mpr hκW) W.support.isClosed⟩
    (by
      show (Z : Set Y) ⊆ closure {κ}
      rw [← hξZ]
      exact closure_minimal (Set.singleton_subset_iff.mpr hξκ) isClosed_closure)
  exact ⟨κ, hκO, mem_pts_ofClosed.mpr (hmax (subset_closure rfl))⟩

end Subscheme

namespace DatumI.Raw

variable {Y : Scheme.{u}}

/-- Remark 1, p. 169: "Note that `B` can not contain any irreducible component of `W` if `ℜ` has
restriction either closed or open" (the paper gives no argument).  Closed restriction `F`:
`W − W ∩ F` is dense in `W`, so every irreducible component of `W` has a point off `F`, while
`B ⊆ F`. -/
theorem IsPermissibleClosed.not_pts_subset_of_mem_irreducibleComponents [IsAlgebraicScheme Y]
    {ℜ : Raw Y} {F B : Subscheme Y} (hF : ℜ.IsClosedRestriction F)
    (hB : ℜ.IsPermissibleClosed F B) :
    ∀ C ∈ ℜ.W.irreducibleComponents, ¬ C.pts ⊆ B.pts := by
  intro C hC hCB
  have hW : ℜ.W.pts ⊆ closure (F.ptsᶜ ∩ ℜ.W.pts) := by
    have := hF.2.2
    rwa [Set.sdiff_eq, Set.inter_comm] at this
  obtain ⟨κ, hκF, hκC⟩ := Subscheme.exists_mem_of_mem_irreducibleComponents
    F.support.isClosed.isOpen_compl hW hC
  exact hκF (hB.2 (hCB hκC)).2

/-- Remark 1, p. 169 (see above), open restriction `U`: `U` is dense in `W` and `B ⊆ W − U`. -/
theorem IsPermissibleOpen.not_pts_subset_of_mem_irreducibleComponents [IsAlgebraicScheme Y]
    {ℜ : Raw Y} {U : Set Y} {B : Subscheme Y} (hU : ℜ.IsOpenRestriction U)
    (hB : ℜ.IsPermissibleOpen U B) :
    ∀ C ∈ ℜ.W.irreducibleComponents, ¬ C.pts ⊆ B.pts := by
  intro C hC hCB
  obtain ⟨⟨U₀, hU₀, hUeq⟩, hdense, -⟩ := hU
  have hW : ℜ.W.pts ⊆ closure (U₀ ∩ ℜ.W.pts) := hUeq ▸ hdense
  obtain ⟨κ, hκU, hκC⟩ := Subscheme.exists_mem_of_mem_irreducibleComponents hU₀ hW hC
  exact (hB.2 (hCB hκC)).2 (hUeq ▸ ⟨hκU, (hB.2 (hCB hκC)).1⟩)

end DatumI.Raw

/-! ### The exact stages `IsStageI` (pp. 279–280) -/

/-- A stage of the constructions of Ch. IV §1 for type I data, as in the paper: an ambient
scheme `Y` of dimension `N` carrying a resolution datum of type `ℜ^{N,n}_I`, i.e. with
`n = dim W` (Definition 3 (I) (iv), p. 164).  The proofs of Propositions 1 and 2 use
"`dim(B'') < dim(_bW') = n`" (p. 280): the exact value `dim(_bW') = n` is preserved by
permissible successions with a closed or open restriction because a center contains no
irreducible component of `W` (`DatumI.Raw.IsPermissibleClosed.not_pts_subset_of_mem_irreducibleComponents`;
`rem:I.1-dim-W`, Remark 1, p. 169). -/
def IsStageI (N n : ℕ) (Y : Scheme.{u}) (ℜ : DatumI.Raw Y) : Prop :=
  IsAmbient Y N ∧ ℜ.IsDatum ∧ ℜ.n = (n : WithBot ℕ∞)

namespace IsStageI

variable {N n : ℕ}

theorem isGoodDatumI {Y : Scheme.{u}} {ℜ : DatumI.Raw Y} (h : IsStageI N n Y ℜ) :
    IsGoodDatumI N n Y ℜ :=
  ⟨h.1, h.2.1, h.2.2.le⟩

theorem transform_closed [Hironaka.Cited.MonoidalTransformationExistsIsProper.{u}] {Y : Scheme.{u}}
    {ℜ : DatumI.Raw Y} (h : IsStageI N n Y ℜ) {F : Subscheme Y} (hF : ℜ.IsClosedRestriction F)
    {B : Subscheme Y} (hB : ℜ.IsPermissibleClosed F B) (t : MonoidalTransformation Y B) :
    IsStageI N n t.X' (ℜ.transform t) ∧
      (ℜ.transform t).IsClosedRestriction (Subscheme.strictTransform t F) := by
  obtain ⟨hgood', hF'⟩ := IsGoodDatumI.transform_closed h.isGoodDatumI hF hB t
  have := h.1.1
  refine ⟨⟨hgood'.1, hgood'.2.1, ?_⟩, hF'⟩
  show (ℜ.transform t).W.dim = _
  rw [(DatumI.Raw.dim_transform_W h.1.2.1 ℜ h.2.1 t hB.1).2
    (hB.not_pts_subset_of_mem_irreducibleComponents hF)]
  exact h.2.2

theorem transform_open [Hironaka.Cited.MonoidalTransformationExistsIsProper.{u}] {Y : Scheme.{u}}
    {ℜ : DatumI.Raw Y} (h : IsStageI N n Y ℜ) {U : Set Y} (hU : ℜ.IsOpenRestriction U)
    {B : Subscheme Y} (hB : ℜ.IsPermissibleOpen U B) (t : MonoidalTransformation Y B) :
    IsStageI N n t.X' (ℜ.transform t) ∧
      (ℜ.transform t).IsOpenRestriction (DatumI.Raw.transformOpen t U) := by
  obtain ⟨hgood', hU'⟩ := IsGoodDatumI.transform_open h.isGoodDatumI hU hB t
  have := h.1.1
  refine ⟨⟨hgood'.1, hgood'.2.1, ?_⟩, hU'⟩
  show (ℜ.transform t).W.dim = _
  rw [(DatumI.Raw.dim_transform_W h.1.2.1 ℜ h.2.1 t hB.1).2
    (hB.not_pts_subset_of_mem_irreducibleComponents hU)]
  exact h.2.2

theorem succession_closed [Hironaka.Cited.MonoidalTransformationExistsIsProper.{u}] {X Y : Scheme.{u}}
    (s : MonoidalSuccession X Y) {ℜ : DatumI.Raw X} (h : IsStageI N n X ℜ) {F : Subscheme X}
    (hF : ℜ.IsClosedRestriction F) (hs : s.IsPermissibleIClosed ℜ F) :
    IsStageI N n Y (s.transformI ℜ) ∧ (s.transformI ℜ).IsClosedRestriction (s.strictTransform F) := by
  induction s with
  | nil X => exact ⟨h, hF⟩
  | cons B t rest ih =>
    obtain ⟨h', hF'⟩ := transform_closed h hF hs.1 t
    exact ih h' hF' hs.2

theorem succession_open [Hironaka.Cited.MonoidalTransformationExistsIsProper.{u}] {X Y : Scheme.{u}}
    (s : MonoidalSuccession X Y) {ℜ : DatumI.Raw X} (h : IsStageI N n X ℜ) {U : Set X}
    (hU : ℜ.IsOpenRestriction U) (hs : s.IsPermissibleIOpen ℜ U) :
    IsStageI N n Y (s.transformI ℜ) ∧ (s.transformI ℜ).IsOpenRestriction (s.transformOpen U) := by
  induction s with
  | nil X => exact ⟨h, hU⟩
  | cons B t rest ih =>
    obtain ⟨h', hU'⟩ := transform_open h hU hs.1 t
    exact ih h' hU' hs.2

end IsStageI

/-! ### Successions whose centers lie inside the strict transforms of a subscheme -/

namespace DatumI.Raw

variable {Y : Scheme.{u}}

/-- A permissible center lies in the principal subscheme. -/
theorem IsPermissible.isContainedIn_W {ℜ : Raw Y} {B : Subscheme Y} (h : ℜ.IsPermissible B) :
    B.IsContainedIn ℜ.W := by
  have := h.2.1.2.2.2.2 (Fin.last _)
  simp only [extendBy, Fin.snoc_last] at this
  exact this

theorem IsPermissible.pts_subset_W {ℜ : Raw Y} {B : Subscheme Y} (h : ℜ.IsPermissible B) :
    B.pts ⊆ ℜ.W.pts :=
  pts_subset_of_isContainedIn h.isContainedIn_W

/-- Adjoining a reduced subscheme of `W` as new principal subscheme gives a datum (Def. 6). -/
theorem isDatum_extendBy {ℜ : Raw Y} (hℜ : ℜ.IsDatum) {D : Subscheme Y} (hD : D.IsReduced)
    (hDW : D.pts ⊆ ℜ.W.pts) : (ℜ.extendBy D).IsDatum := by
  refine ⟨hℜ.1, hℜ.2.1, hℜ.2.2.1, hD, fun i => ?_⟩
  refine Subscheme.isContainedIn_of_pts_subset hD ?_
  refine Fin.lastCases ?_ (fun i => ?_) i
  · simpa [extendBy, Fin.snoc_last] using hDW
  · have h := pts_subset_of_isContainedIn (hℜ.2.2.2.2 i)
    simpa [extendBy, Fin.snoc_castSucc] using hDW.trans h

/-- Enlarging the open restriction preserves permissibility. -/
theorem IsPermissibleOpen.mono {ℜ : Raw Y} {U U' : Set Y} {B : Subscheme Y}
    (h : ℜ.IsPermissibleOpen U' B) (hUU' : U ⊆ U') : ℜ.IsPermissibleOpen U B :=
  ⟨h.1, fun _ hy => ⟨(h.2 hy).1, fun hU => (h.2 hy).2 (hUU' hU)⟩⟩

end DatumI.Raw

namespace MonoidalSuccession

variable {X Y Z : Scheme.{u}}

theorem IsPermissibleIOpen.mono {s : MonoidalSuccession X Y} {ℜ : DatumI.Raw X} {U U' : Set X}
    (h : s.IsPermissibleIOpen ℜ U') (hUU' : U ⊆ U') : s.IsPermissibleIOpen ℜ U := by
  induction s with
  | nil X => trivial
  | cons B t rest ih =>
    exact ⟨h.1.mono hUU', ih h.2 (Set.preimage_mono hUU')⟩

/-- Every center is permissible for the corresponding transform of `ℜ` and lies inside the
corresponding strict transform of `D`. -/
def PermissibleWithin : {X Y : Scheme.{u}} → MonoidalSuccession X Y → DatumI.Raw X →
    Subscheme X → Prop
  | _, _, nil _, _, _ => True
  | _, _, cons B t rest, ℜ, D =>
      ℜ.IsPermissible B ∧ B.pts ⊆ D.pts ∧
        rest.PermissibleWithin (ℜ.transform t) (Subscheme.strictTransform t D)

theorem permissibleWithin_append (s : MonoidalSuccession X Y) (s' : MonoidalSuccession Y Z)
    (ℜ : DatumI.Raw X) (D : Subscheme X) :
    (s.append s').PermissibleWithin ℜ D ↔
      s.PermissibleWithin ℜ D ∧ s'.PermissibleWithin (s.transformI ℜ) (s.strictTransform D) := by
  induction s with
  | nil X => simp [PermissibleWithin]
  | cons B t rest ih =>
    simp only [cons_append, PermissibleWithin, transformI_cons, strictTransform_cons, ih,
      and_assoc]

theorem PermissibleWithin.isPermissibleIClosed {s : MonoidalSuccession X Y} {ℜ : DatumI.Raw X}
    {D F : Subscheme X} (h : s.PermissibleWithin ℜ D) (hDW : D.IsContainedIn ℜ.W)
    (hDF : D.IsContainedIn F) : s.IsPermissibleIClosed ℜ F := by
  induction s with
  | nil X => trivial
  | cons B t rest ih =>
    obtain ⟨hB, hBD, hrest⟩ := h
    refine ⟨⟨hB, fun y hy => ⟨pts_subset_of_isContainedIn hDW (hBD hy),
      pts_subset_of_isContainedIn hDF (hBD hy)⟩⟩, ?_⟩
    exact ih hrest (MonoidalTransformation.isContainedIn_strictTransform t hDW)
      (MonoidalTransformation.isContainedIn_strictTransform t hDF)

theorem PermissibleWithin.isPermissibleIOpen {s : MonoidalSuccession X Y} {ℜ : DatumI.Raw X}
    {D : Subscheme X} {U : Set X} (h : s.PermissibleWithin ℜ D) (hDW : D.IsContainedIn ℜ.W)
    (hDU : ∀ y ∈ D.pts, y ∉ U) : s.IsPermissibleIOpen ℜ U := by
  induction s with
  | nil X => trivial
  | cons B t rest ih =>
    obtain ⟨hB, hBD, hrest⟩ := h
    refine ⟨⟨hB, fun y hy => ⟨pts_subset_of_isContainedIn hDW (hBD hy), hDU _ (hBD hy)⟩⟩, ?_⟩
    refine ih hrest (MonoidalTransformation.isContainedIn_strictTransform t hDW) fun y hy hyU => ?_
    exact hDU _ (MonoidalTransformation.pts_strictTransform_subset t D hy) hyU

theorem permissibleWithin_of_isPermissibleIOpen_extendBy {s : MonoidalSuccession X Y}
    {ℜ : DatumI.Raw X} {D : Subscheme X} {U : Set X}
    (h : s.IsPermissibleIOpen (ℜ.extendBy D) U) : s.PermissibleWithin ℜ D := by
  induction s with
  | nil X => trivial
  | cons B t rest ih =>
    obtain ⟨⟨hB, -⟩, hrest⟩ := h
    obtain ⟨hB', hBD⟩ := DatumI.Raw.isPermissible_of_extendBy hB
    rw [DatumI.Raw.transform_extendBy] at hrest
    exact ⟨hB', hBD, ih hrest⟩

end MonoidalSuccession

namespace Subscheme

variable {Y : Scheme.{u}}

/-- A subscheme with a point has dimension `≥ 0` (the direction "non-empty implies `dim ≠ ⊥`" of
`Subscheme.dim_eq_bot_iff`, p. 163: "We take the integer −1 as the dimension of the empty scheme"). -/
theorem dim_ne_bot {D : Subscheme Y} (h : D.pts.Nonempty) : D.dim ≠ ⊥ := fun hb =>
  h.ne_empty ((Subscheme.dim_eq_bot_iff D).mp hb)

/-- A non-empty closed subset `D ⊆ W` all of whose points are proper specializations of a point
`c ∈ W − D` has smaller dimension than `W`. -/
theorem dim_add_one_le_of_generization {D W : Subscheme Y} (hDW : D.pts ⊆ W.pts)
    (hne : D.pts.Nonempty) {c : Y} (hcW : c ∈ W.pts) (hcD : c ∉ D.pts)
    (hc : ∀ t ∈ D.pts, c ⤳ t) : D.dim + 1 ≤ W.dim := by
  rw [Subscheme.dim_eq_topologicalKrullDim, Subscheme.dim_eq_topologicalKrullDim]
  exact topologicalKrullDim_add_one_le D.support.isClosed hDW hne hcW hcD hc

end Subscheme

/-! ### Lifting successions along a flat preimmersion ("(1)–(3)", p. 279) -/

/-- The openness half of Lemma 1 of Ch. IV §1 (p. 277, `lem:IV.1-1`): the set of points of `W`
at which a type I datum on a non-singular algebraic scheme is resolved is open in `W`.  It is
proved in `Hironaka/Ch4/Localization.lean` (which imports this file) and is taken here as a
hypothesis of the lifting constructions, discharged there. -/
def ResolvedSetIsOpen : Prop :=
  ∀ (Y : Scheme.{u}) (_ : IsAlgebraicScheme Y), Y.IsNonsingular → ∀ ℜ : DatumI.Raw Y,
    ℜ.IsDatum → ∃ U₀ : Set Y, IsOpen U₀ ∧ {y ∈ ℜ.W.pts | ℜ.ResolvedAt y} = U₀ ∩ ℜ.W.pts

/-- Lemma 1 of Ch. IV §1 (p. 277, `lem:IV.1-1`), the hypothesis of the type I lifting
constructions: for a resolution datum of type I on a non-singular irreducible algebraic scheme,
the set `U` of points of `W` at which it is resolved is an open subset of `W` which has
non-empty intersection with every irreducible component of `W`.  It is proved in
`Hironaka/Ch4/Localization.lean` (which imports this file) and is taken here as a hypothesis of
the lifting constructions, discharged there.  (The expression `⋃ E_i` of the datum, a hypothesis
of Lemma 1 as printed, is not used by the proof of Lemma 1 in Lean.) -/
def Lemma1Holds : Prop :=
  ∀ (Y : Scheme.{u}) [IsAlgebraicScheme Y] [IrreducibleSpace Y], Y.IsNonsingular →
    ∀ ℜ : DatumI.Raw Y, ℜ.IsDatum →
    (∃ U₀ : Set Y, IsOpen U₀ ∧ {y ∈ ℜ.W.pts | ℜ.ResolvedAt y} = U₀ ∩ ℜ.W.pts) ∧
    ∀ C ∈ ℜ.W.irreducibleComponents, (C.pts ∩ {y ∈ ℜ.W.pts | ℜ.ResolvedAt y}).Nonempty

namespace LocSucc

theorem exists_nat_of_le {d : WithBot ℕ∞} {N : ℕ} (hne : d ≠ ⊥) (h : d ≤ (N : WithBot ℕ∞)) :
    ∃ m : ℕ, d = m ∧ m ≤ N := by
  obtain ⟨m, hm, hmN⟩ := exists_nat_of_add_one_le (n := N + 1) hne
    (by
      have : (((N + 1 : ℕ)) : WithBot ℕ∞) = (N : WithBot ℕ∞) + 1 := by norm_cast
      rw [this]
      gcongr)
  exact ⟨m, hm, by omega⟩

open MonoidalSuccession

/-- The core of the lifting step of p. 280.  Let `j : Z → Y` be a flat preimmersion into an
ambient scheme `Y` of dimension `N`, `ℜ` a datum on `Y`, and `B̄` a non-empty center on `Z`
permissible for the pulled-back datum `ℜ_Z`.  Let `B''` be the smallest (reduced) subscheme of
`Y` inducing `B̄` ("the smallest irreducible subscheme of `X'_{k(b)}` such that
`B̄_b = (B'')_S`"), of dimension `n''`.  Theorem `I₂^{N,n''}`, applied to
`((E; V, W; B''), U'')` with `U''` the resolved points of `B''`, gives a succession `h` whose
centers avoid the range of `j`, and the strict transform `B*` of `B''` is then a permissible
center inducing `B̄`.  The succession `h` followed by the monoidal transformation with center
`B*` lifts the monoidal transformation of `Z` with center `B̄`.

As printed (p. 280): "`U''` is an open dense subset of `B''` by Lemma 1".  Lemma 1
(`Lemma1Holds`, applied to the datum `(E; V, W; B'')` of the irreducible scheme `Y`) says that the
set `U''` of resolved points of `B''` is open in `B''` and meets every irreducible component of
`B''`; `B''` is irreducible, so it is its own component, `U''` is non-empty, and an open
non-empty subset of an irreducible space is dense. -/
theorem lift_transformation [Hironaka.Cited.MonoidalTransformationExistsIsProper.{u}] (hL1 : Lemma1Holds.{u}) (N n'' : ℕ) (hI₂ : FundamentalTheorem.I₂.{u} N n'')
    {Y Z : Scheme.{u}} (hY : IsAmbient Y N) (j : Z ⟶ Y) [Flat j] [IsPreimmersion j]
    (ℜ : DatumI.Raw Y) (hℜ : ℜ.IsDatum) {Bb : Subscheme Z}
    (hBb : (ℜ.pullback j).IsPermissible Bb) (hBbne : Bb.pts.Nonempty)
    (hdim : (FlatPreimm.closureLift j Bb).dim = (n'' : WithBot ℕ∞))
    (tb : MonoidalTransformation Z Bb) :
    ∃ (Y' : Scheme.{u}) (s : MonoidalSuccession Y Y') (j' : tb.X' ⟶ Y'), Flat j' ∧
      IsPreimmersion j' ∧ s.PermissibleWithin ℜ (FlatPreimm.closureLift j Bb) ∧
      j' ≫ s.composite = tb.f ≫ j ∧
      Set.range j'.base = s.composite.base ⁻¹' Set.range j.base ∧
      (s.transformI ℜ).pullback j' = (ℜ.pullback j).transform tb ∧
      ∀ V, Subscheme.totalTransform j' (s.strictTransform V) =
        Subscheme.strictTransform tb (Subscheme.totalTransform j V) := by
  have := hY.1
  have := hY.2.2.1
  set B'' := FlatPreimm.closureLift j Bb with hB''
  have hBbirr : Bb.IsIrreducible := by
    rcases hBb.1 with h | h
    · exfalso
      rw [h, Subscheme.pts_empty] at hBbne
      exact hBbne.ne_empty rfl
    · exact h.2
  have hBbred : Bb.IsReduced := hBb.1.isReduced
  have hjB : Subscheme.totalTransform j B'' = Bb :=
    FlatPreimm.totalTransform_closureLift j Bb hBbred
  have hB''red : B''.IsReduced := FlatPreimm.closureLift_isReduced j Bb
  have hB''irr : B''.IsIrreducible := FlatPreimm.closureLift_isIrreducible j Bb hBbirr
  have hB''W : B''.pts ⊆ ℜ.W.pts := by
    rw [hB'', FlatPreimm.pts_closureLift]
    refine closure_minimal ?_ ℜ.W.support.isClosed
    rintro _ ⟨z, hz, rfl⟩
    have := hBb.pts_subset_W hz
    rw [DatumI.Raw.pullback_W, FlatPreimm.pts_totalTransform] at this
    exact this
  set ℜ'' := ℜ.extendBy B'' with hℜ''def
  have hℜ'' : ℜ''.IsDatum := DatumI.Raw.isDatum_extendBy hℜ hB''red hB''W
  have hres : ∀ z ∈ Bb.pts, ℜ''.ResolvedAt (j z) := by
    intro z hz
    rw [← DatumI.Raw.resolvedAt_pullback_iff j ℜ'' hℜ''.2.2.2.2, hℜ''def,
      DatumI.Raw.pullback_extendBy, hjB]
    exact hBb.2.2 z hz
  have := hY.2.2.1
  -- Lemma 1 for the datum `ℜ'' = (E; V, W; B'')` on the irreducible scheme `Y`
  obtain ⟨⟨U₀, hU₀, hU₀eq⟩, hmeet⟩ := hL1 Y hY.2.1 ℜ'' hℜ''
  set U'' : Set Y := {y ∈ ℜ''.W.pts | ℜ''.ResolvedAt y} with hU''def
  have hU'' : ℜ''.IsOpenRestriction U'' := by
    refine ⟨⟨U₀, hU₀, hU₀eq⟩, ?_, fun y hy => hy.2⟩
    -- "`U''` is an open dense subset of `B''` by Lemma 1": `B''` is irreducible, hence its own
    -- irreducible component, so `U''` meets it
    have hirr := Subscheme.isIrreducible_pts B'' hB''irr
    obtain ⟨y₀, hy₀B, hy₀U⟩ := hmeet _
      (Subscheme.ofClosed_mem_irreducibleComponents_of_isIrreducible hirr)
    have hy₀ : y₀ ∈ B''.pts := Subscheme.mem_pts_ofClosed.mp hy₀B
    have hy₀U₀ : y₀ ∈ U₀ ∩ ℜ''.W.pts := by
      rw [← hU₀eq]
      exact hy₀U
    have := subset_closure_inter_of_isPreirreducible_of_isOpen hirr.2 hU₀
      ⟨y₀, hy₀U₀.2, hy₀U₀.1⟩
    rw [hU₀eq, Set.inter_comm]
    exact this
  obtain ⟨Y₁, h, hperm, hresolved⟩ := hI₂ Y hY ⟨ℜ'', hℜ''⟩ U'' hU'' hdim
  have hperm' : h.IsPermissibleIOpen ℜ'' U'' := hperm
  have havoid : h.CentersAvoid (Set.range j.base) := by
    refine centersAvoid_of_isPermissibleIOpen h ℜ'' U'' _ hperm' fun y hy hyr => ?_
    obtain ⟨z, rfl⟩ := hyr
    have : j z ∈ j.base '' Bb.pts := by
      rw [← FlatPreimm.pts_closureLift_inter_range]
      exact ⟨hy, z, rfl⟩
    obtain ⟨z', hz', hzz⟩ := this
    have hz'z := j.isEmbedding.injective hzz
    subst hz'z
    exact ⟨hy, hres z' hz'⟩
  obtain ⟨j₁, hfl₁, hpre₁, hj₁, hr₁, hst₁, hℜ₁⟩ := exists_lift_of_centersAvoid h j havoid
  set Bs := h.strictTransform B'' with hBs
  have hBsj : Subscheme.totalTransform j₁ Bs = Bb := (hst₁ B'').trans hjB
  have hext : h.transformI ℜ'' = (h.transformI ℜ).extendBy Bs := transformI_extendBy h ℜ B''
  have hdat : (h.transformI ℜ'').IsDatum :=
    transformI_isDatum h hY.2.1 ℜ'' hℜ'' hperm'.isPermissibleI
  have hresolved' : ((h.transformI ℜ).extendBy Bs).ResolvedEverywhere := by
    rw [← hext]
    exact hresolved
  have hBsns : Bs.IsNonsingular := Subscheme.isNonsingular_of_stalk_quot Bs fun y hy =>
    (hresolved' y hy).1.2
  have hBsirr : Bs.IsIrreducible :=
    strictTransform_isIrreducible_of_centersAvoid h j havoid B'' hB''irr
      (by rw [hjB]; exact hBbne)
  have hBsperm : (h.transformI ℜ).IsPermissible Bs :=
    ⟨Or.inr ⟨hBsns, hBsirr⟩, hext ▸ hdat, hresolved'⟩
  obtain ⟨ts, -⟩ := MonoidalTransformation.exists_isProper Y₁ Bs
  obtain ⟨j', hfl', hpre', hsq, hr', hexc', hst'⟩ := ts.exists_lift j₁ hBsj tb
  refine ⟨ts.X', h.append (cons Bs ts (nil _)), j', hfl', hpre', ?_, ?_, ?_, ?_, fun V => ?_⟩
  · rw [permissibleWithin_append]
    exact ⟨permissibleWithin_of_isPermissibleIOpen_extendBy hperm', hBsperm, subset_rfl, trivial⟩
  · rw [composite_append, composite_cons, composite_nil, Category.id_comp, ← Category.assoc, hsq,
      Category.assoc, hj₁]
  · rw [hr', hr₁, composite_append, composite_cons, composite_nil, Category.id_comp,
      Scheme.Hom.comp_base, TopCat.coe_comp, Set.preimage_comp]
  · rw [transformI_append, transformI_cons, transformI_nil,
      DatumI.Raw.pullback_transform_of_lift ts j₁ tb j' hexc' hst', hℜ₁]
  · rw [strictTransform_append, strictTransform_cons, strictTransform_nil, hst', hst₁]

/-- The lifting step when the center on `Z` is empty: the monoidal transformation of `Y` with
empty center (an isomorphism) lifts it.

Deviation from the paper (alternative proof): the empty subscheme is a non-singular irreducible
center by the paper's agreement, but the construction of `B''` on p. 280 does not address it;
this degenerate case is handled separately. -/
theorem lift_empty {Y Z : Scheme.{u}} (j : Z ⟶ Y) [Flat j] [IsPreimmersion j]
    {Bb : Subscheme Z} (hBb : Bb = Subscheme.empty) (tb : MonoidalTransformation Z Bb) :
    ∃ (s : MonoidalSuccession Y Y) (j' : tb.X' ⟶ Y), Flat j' ∧ IsPreimmersion j' ∧
      s = cons Subscheme.empty (MonoidalTransformation.idEmpty Y) (nil _) ∧
      j' ≫ s.composite = tb.f ≫ j ∧
      Set.range j'.base = s.composite.base ⁻¹' Set.range j.base ∧
      (∀ ℜ : DatumI.Raw Y, (s.transformI ℜ).pullback j' = (ℜ.pullback j).transform tb) ∧
      ∀ V, Subscheme.totalTransform j' (s.strictTransform V) =
        Subscheme.strictTransform tb (Subscheme.totalTransform j V) := by
  obtain ⟨j', hfl, hpre, hsq, hr, hexc, hst⟩ :=
    (MonoidalTransformation.idEmpty Y).exists_lift j
      ((Subscheme.totalTransform_empty j).trans hBb.symm) tb
  refine ⟨_, j', hfl, hpre, rfl, ?_, ?_, fun ℜ => ?_, fun V => ?_⟩
  · change j' ≫ (𝟙 Y ≫ 𝟙 Y) = _
    simpa using hsq
  · change Set.range j'.base = (𝟙 Y ≫ 𝟙 Y : Y ⟶ Y).base ⁻¹' _
    rw [hr]
    rfl
  · exact DatumI.Raw.pullback_transform_of_lift _ j tb j' hexc hst ℜ
  · exact hst V

/-- The lifting step for a closed restriction (p. 280): a monoidal transformation of `Z`
permissible for `(ℜ_Z, F_Z)` is lifted by a succession of `Y` permissible for `(ℜ, F)`.  As
printed: `B'' ⊆ _bW' ∩ _bF'`, and "`dim(B'') < dim(_bW') = n`" (the stage carries
`dim W = n`, `IsStageI`). -/
theorem lift_step_closed [Hironaka.Cited.MonoidalTransformationExistsIsProper.{u}] (hL1 : Lemma1Holds.{u}) (N n : ℕ)
    (hI₂ : ∀ n'' : ℕ, n'' < n → FundamentalTheorem.I₂.{u} N n'')
    {Y Z : Scheme.{u}} (j : Z ⟶ Y) [Flat j] [IsPreimmersion j] (ℜ : DatumI.Raw Y)
    (F : Subscheme Y) (hstage : IsStageI N n Y ℜ) (hF : ℜ.IsClosedRestriction F) {Bb : Subscheme Z}
    (hBb : (ℜ.pullback j).IsPermissibleClosed (Subscheme.totalTransform j F) Bb)
    (tb : MonoidalTransformation Z Bb) :
    ∃ (Y' : Scheme.{u}) (s : MonoidalSuccession Y Y') (j' : tb.X' ⟶ Y'), Flat j' ∧
      IsPreimmersion j' ∧ s.IsPermissibleIClosed ℜ F ∧
      j' ≫ s.composite = tb.f ≫ j ∧
      Set.range j'.base = s.composite.base ⁻¹' Set.range j.base ∧
      (s.transformI ℜ).pullback j' = (ℜ.pullback j).transform tb ∧
      ∀ V, Subscheme.totalTransform j' (s.strictTransform V) =
        Subscheme.strictTransform tb (Subscheme.totalTransform j V) := by
  obtain ⟨hY, hℜ, hWn⟩ := hstage
  have := hY.1
  by_cases h0 : Bb.pts.Nonempty
  · set B'' := FlatPreimm.closureLift j Bb with hB''
    have hB''red : B''.IsReduced := FlatPreimm.closureLift_isReduced j Bb
    have hBbirr : Bb.IsIrreducible := by
      rcases hBb.1.1 with h | h
      · exfalso
        rw [h, Subscheme.pts_empty] at h0
        exact h0.ne_empty rfl
      · exact h.2
    have hB''irr : B''.IsIrreducible := FlatPreimm.closureLift_isIrreducible j Bb hBbirr
    have hB''WF : B''.pts ⊆ ℜ.W.pts ∩ F.pts := by
      rw [hB'', FlatPreimm.pts_closureLift]
      refine closure_minimal ?_ (ℜ.W.support.isClosed.inter F.support.isClosed)
      rintro _ ⟨z, hz, rfl⟩
      obtain ⟨h1, h2⟩ := hBb.2 hz
      rw [DatumI.Raw.pullback_W, FlatPreimm.pts_totalTransform] at h1
      rw [FlatPreimm.pts_totalTransform] at h2
      exact ⟨h1, h2⟩
    -- `dim B'' < dim W = n` (p. 280)
    obtain ⟨b, hb⟩ := QuasiSober.sober (Subscheme.isIrreducible_pts B'' hB''irr)
      B''.support.isClosed
    have hbcl : b ∈ closure (F.ptsᶜ ∩ ℜ.W.pts) := by
      have := hF.2.2 (hB''WF hb.mem).1
      rwa [Set.sdiff_eq, Set.inter_comm] at this
    obtain ⟨κ, ⟨hκF, hκW⟩, hκb⟩ := exists_specializes_of_mem_closure
      F.support.isClosed.isOpen_compl ℜ.W.support.isClosed hbcl
    have hdimlt : B''.dim + 1 ≤ (n : WithBot ℕ∞) :=
      (Subscheme.dim_add_one_le_of_generization (fun y hy => (hB''WF hy).1) ⟨b, hb.mem⟩ hκW
        (fun h => hκF (hB''WF h).2) fun t ht => hκb.trans (hb.specializes ht)).trans_eq hWn
    obtain ⟨m, hm, hmn⟩ := exists_nat_of_add_one_le
      (Subscheme.dim_ne_bot (D := B'') (by
        rw [hB'', FlatPreimm.pts_closureLift]
        exact (Set.Nonempty.image _ h0).mono subset_closure)) hdimlt
    obtain ⟨Y', s, j', hfl, hpre, hperm, hcomp, hr, hℜ', hst⟩ :=
      lift_transformation hL1 N m (hI₂ m hmn) hY j ℜ hℜ hBb.1 h0 hm tb
    refine ⟨Y', s, j', hfl, hpre, ?_, hcomp, hr, hℜ', hst⟩
    exact hperm.isPermissibleIClosed
      (Subscheme.isContainedIn_of_pts_subset hB''red fun y hy => (hB''WF hy).1)
      (Subscheme.isContainedIn_of_pts_subset hB''red fun y hy => (hB''WF hy).2)
  · have hBe : Bb = Subscheme.empty :=
      Subscheme.eq_empty_of_pts_eq_empty (Set.not_nonempty_iff_eq_empty.mp h0)
    obtain ⟨s, j', hfl, hpre, rfl, hcomp, hr, hℜ', hst⟩ := lift_empty j hBe tb
    exact ⟨Y, cons Subscheme.empty (MonoidalTransformation.idEmpty Y) (nil _), j', hfl, hpre,
      ⟨DatumI.Raw.isPermissibleClosed_empty hℜ F, trivial⟩, hcomp, hr, hℜ' ℜ, hst⟩

/-- The lifting step for an open restriction (p. 281; "exactly as in Proposition 1", with
"obviously `dim(B'') < dim(_bW') = n`", the stage carrying `dim W = n`, `IsStageI`). -/
theorem lift_step_open [Hironaka.Cited.MonoidalTransformationExistsIsProper.{u}] (hL1 : Lemma1Holds.{u}) (N n : ℕ)
    (hI₂ : ∀ n'' : ℕ, n'' < n → FundamentalTheorem.I₂.{u} N n'')
    {Y Z : Scheme.{u}} (j : Z ⟶ Y) [Flat j] [IsPreimmersion j] (ℜ : DatumI.Raw Y)
    (U : Set Y) (hstage : IsStageI N n Y ℜ) (hU : ℜ.IsOpenRestriction U) {Bb : Subscheme Z}
    (hBb : (ℜ.pullback j).IsPermissibleOpen (j.base ⁻¹' U) Bb)
    (tb : MonoidalTransformation Z Bb) :
    ∃ (Y' : Scheme.{u}) (s : MonoidalSuccession Y Y') (j' : tb.X' ⟶ Y'), Flat j' ∧
      IsPreimmersion j' ∧ s.IsPermissibleIOpen ℜ U ∧
      j' ≫ s.composite = tb.f ≫ j ∧
      Set.range j'.base = s.composite.base ⁻¹' Set.range j.base ∧
      (s.transformI ℜ).pullback j' = (ℜ.pullback j).transform tb ∧
      ∀ V, Subscheme.totalTransform j' (s.strictTransform V) =
        Subscheme.strictTransform tb (Subscheme.totalTransform j V) := by
  obtain ⟨hY, hℜ, hWn⟩ := hstage
  have := hY.1
  by_cases h0 : Bb.pts.Nonempty
  · set B'' := FlatPreimm.closureLift j Bb with hB''
    have hB''red : B''.IsReduced := FlatPreimm.closureLift_isReduced j Bb
    have hBbirr : Bb.IsIrreducible := by
      rcases hBb.1.1 with h | h
      · exfalso
        rw [h, Subscheme.pts_empty] at h0
        exact h0.ne_empty rfl
      · exact h.2
    have hB''irr : B''.IsIrreducible := FlatPreimm.closureLift_isIrreducible j Bb hBbirr
    obtain ⟨U₀, hU₀, hUeq⟩ := hU.1
    have hB''WU : B''.pts ⊆ ℜ.W.pts ∩ U₀ᶜ := by
      rw [hB'', FlatPreimm.pts_closureLift]
      refine closure_minimal ?_ (ℜ.W.support.isClosed.inter hU₀.isClosed_compl)
      rintro _ ⟨z, hz, rfl⟩
      obtain ⟨h1, h2⟩ := hBb.2 hz
      rw [DatumI.Raw.pullback_W, FlatPreimm.pts_totalTransform] at h1
      refine ⟨h1, fun h => h2 ?_⟩
      show j z ∈ U
      rw [hUeq]
      exact ⟨h, h1⟩
    obtain ⟨b, hb⟩ := QuasiSober.sober (Subscheme.isIrreducible_pts B'' hB''irr)
      B''.support.isClosed
    have hbcl : b ∈ closure (U₀ ∩ ℜ.W.pts) := by
      have := hU.2.1 (hB''WU hb.mem).1
      rwa [hUeq] at this
    obtain ⟨κ, ⟨hκU, hκW⟩, hκb⟩ := exists_specializes_of_mem_closure hU₀
      ℜ.W.support.isClosed hbcl
    have hdimlt : B''.dim + 1 ≤ (n : WithBot ℕ∞) :=
      (Subscheme.dim_add_one_le_of_generization (fun y hy => (hB''WU hy).1) ⟨b, hb.mem⟩ hκW
        (fun h => (hB''WU h).2 hκU) fun t ht => hκb.trans (hb.specializes ht)).trans_eq hWn
    obtain ⟨m, hm, hmn⟩ := exists_nat_of_add_one_le
      (Subscheme.dim_ne_bot (D := B'') (by
        rw [hB'', FlatPreimm.pts_closureLift]
        exact (Set.Nonempty.image _ h0).mono subset_closure)) hdimlt
    obtain ⟨Y', s, j', hfl, hpre, hperm, hcomp, hr, hℜ', hst⟩ :=
      lift_transformation hL1 N m (hI₂ m hmn) hY j ℜ hℜ hBb.1 h0 hm tb
    refine ⟨Y', s, j', hfl, hpre, ?_, hcomp, hr, hℜ', hst⟩
    refine hperm.isPermissibleIOpen
      (Subscheme.isContainedIn_of_pts_subset hB''red fun y hy => (hB''WU hy).1)
      fun y hy hyU => ?_
    rw [hUeq] at hyU
    exact (hB''WU hy).2 hyU.1
  · have hBe : Bb = Subscheme.empty :=
      Subscheme.eq_empty_of_pts_eq_empty (Set.not_nonempty_iff_eq_empty.mp h0)
    obtain ⟨s, j', hfl, hpre, rfl, hcomp, hr, hℜ', hst⟩ := lift_empty j hBe tb
    refine ⟨Y, cons Subscheme.empty (MonoidalTransformation.idEmpty Y) (nil _), j', hfl, hpre,
      ⟨⟨(DatumI.Raw.isPermissibleClosed_empty hℜ ⊥).1, fun y hy => ?_⟩, trivial⟩, hcomp, hr,
      hℜ' ℜ, hst⟩
    rw [Subscheme.pts_empty] at hy
    exact hy.elim

/-- Lifting a whole succession, closed restriction ("(1)–(3)", p. 279): a succession of `Z`
permissible for `(ℜ_Z, F_Z)` is lifted to a succession of `Y` permissible for `(ℜ, F)`,
interleaving successions whose centers avoid the range of `j`. -/
theorem lift_succession_closed [Hironaka.Cited.MonoidalTransformationExistsIsProper.{u}] (hL1 : Lemma1Holds.{u}) (N n : ℕ)
    (hI₂ : ∀ n'' : ℕ, n'' < n → FundamentalTheorem.I₂.{u} N n'') {Z Z' : Scheme.{u}}
    (sb : MonoidalSuccession Z Z') :
    ∀ {Y : Scheme.{u}} (j : Z ⟶ Y) [Flat j] [IsPreimmersion j] (ℜ : DatumI.Raw Y)
      (F : Subscheme Y), IsStageI N n Y ℜ → ℜ.IsClosedRestriction F →
      sb.IsPermissibleIClosed (ℜ.pullback j) (Subscheme.totalTransform j F) →
      ∃ (Y' : Scheme.{u}) (s : MonoidalSuccession Y Y') (j' : Z' ⟶ Y'), Flat j' ∧
        IsPreimmersion j' ∧ s.IsPermissibleIClosed ℜ F ∧
        Set.range j'.base = s.composite.base ⁻¹' Set.range j.base ∧
        (s.transformI ℜ).pullback j' = sb.transformI (ℜ.pullback j) ∧
        Subscheme.totalTransform j' (s.strictTransform F) =
          sb.strictTransform (Subscheme.totalTransform j F) := by
  induction sb with
  | nil Z =>
    intro Y j _ _ ℜ F _ _ _
    exact ⟨Y, nil Y, j, inferInstance, inferInstance, trivial, by simp, rfl, rfl⟩
  | cons Bb tb rest ih =>
    intro Y j _ _ ℜ F hstage hF hsb
    obtain ⟨hBb, hrest⟩ := hsb
    obtain ⟨Y₁, s₁, j₁, hfl₁, hpre₁, hperm₁, -, hr₁, hℜ₁, hst₁⟩ :=
      lift_step_closed hL1 N n hI₂ j ℜ F hstage hF hBb tb
    obtain ⟨hstage₁, hF₁⟩ := IsStageI.succession_closed s₁ hstage hF hperm₁
    rw [← hℜ₁, ← hst₁ F] at hrest
    obtain ⟨Y', s₂, j', hfl, hpre, hperm₂, hr₂, hℜ₂, hst₂⟩ :=
      ih j₁ (s₁.transformI ℜ) (s₁.strictTransform F) hstage₁ hF₁ hrest
    refine ⟨Y', s₁.append s₂, j', hfl, hpre, (isPermissibleIClosed_append _ _ _ _).mpr
      ⟨hperm₁, hperm₂⟩, ?_, ?_, ?_⟩
    · rw [hr₂, hr₁, composite_append, Scheme.Hom.comp_base, TopCat.coe_comp, Set.preimage_comp]
    · rw [transformI_append, hℜ₂, hℜ₁]
      rfl
    · rw [strictTransform_append, hst₂, hst₁]
      rfl

/-- Lifting a whole succession, open restriction (p. 281). -/
theorem lift_succession_open [Hironaka.Cited.MonoidalTransformationExistsIsProper.{u}] (hL1 : Lemma1Holds.{u}) (N n : ℕ)
    (hI₂ : ∀ n'' : ℕ, n'' < n → FundamentalTheorem.I₂.{u} N n'') {Z Z' : Scheme.{u}}
    (sb : MonoidalSuccession Z Z') :
    ∀ {Y : Scheme.{u}} (j : Z ⟶ Y) [Flat j] [IsPreimmersion j] (ℜ : DatumI.Raw Y)
      (U : Set Y), IsStageI N n Y ℜ → ℜ.IsOpenRestriction U →
      sb.IsPermissibleIOpen (ℜ.pullback j) (j.base ⁻¹' U) →
      ∃ (Y' : Scheme.{u}) (s : MonoidalSuccession Y Y') (j' : Z' ⟶ Y'), Flat j' ∧
        IsPreimmersion j' ∧ s.IsPermissibleIOpen ℜ U ∧
        Set.range j'.base = s.composite.base ⁻¹' Set.range j.base ∧
        (s.transformI ℜ).pullback j' = sb.transformI (ℜ.pullback j) := by
  induction sb with
  | nil Z =>
    intro Y j _ _ ℜ U _ _ _
    exact ⟨Y, nil Y, j, inferInstance, inferInstance, trivial, by simp, rfl⟩
  | cons Bb tb rest ih =>
    intro Y j _ _ ℜ U hstage hU hsb
    obtain ⟨hBb, hrest⟩ := hsb
    obtain ⟨Y₁, s₁, j₁, hfl₁, hpre₁, hperm₁, hcomp₁, hr₁, hℜ₁, -⟩ :=
      lift_step_open hL1 N n hI₂ j ℜ U hstage hU hBb tb
    obtain ⟨hstage₁, hU₁⟩ := IsStageI.succession_open s₁ hstage hU hperm₁
    have hU₁eq : j₁.base ⁻¹' (s₁.transformOpen U) =
        DatumI.Raw.transformOpen tb (j.base ⁻¹' U) := by
      rw [transformOpen_eq, ← Set.preimage_comp, ← TopCat.coe_comp, ← Scheme.Hom.comp_base,
        hcomp₁]
      rfl
    rw [← hℜ₁, ← hU₁eq] at hrest
    obtain ⟨Y', s₂, j', hfl, hpre, hperm₂, hr₂, hℜ₂⟩ :=
      ih j₁ (s₁.transformI ℜ) (s₁.transformOpen U) hstage₁ hU₁ hrest
    refine ⟨Y', s₁.append s₂, j', hfl, hpre, (isPermissibleIOpen_append _ _ _ _).mpr
      ⟨hperm₁, hperm₂⟩, ?_, ?_⟩
    · rw [hr₂, hr₁, composite_append, Scheme.Hom.comp_base, TopCat.coe_comp, Set.preimage_comp]
    · rw [transformI_append, hℜ₂, hℜ₁]
      rfl

end LocSucc

end Hironaka

