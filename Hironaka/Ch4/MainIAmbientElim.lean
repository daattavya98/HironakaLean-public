/-
Copyright (c) 2026 Daattavya Aggarwal, Minhyong Kim, Oisin Kim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daattavya Aggarwal, Minhyong Kim, Oisin Kim
-/
module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Architect
public import Hironaka.Compat.MainISystem
public import Hironaka.Compat.BlowupBaseChange
public import Hironaka.Compat.PermissibleCenterDescent
public import Hironaka.Ch3.Stability
public import Hironaka.Statements

/-!
# Main Theorem I(n), pp. 173–174: the elimination of the centers outside `S(i)`

> … To be precise, we construct a new succession of monoidal
> transformations `{f̄_i : X̄(i+1) → X̄(i)}` where `0 ≤ i < r` and `X̄(0) = X`, such that there exists a morphism
> `g_i : X(i) → X̄(i)` for every `i` having the following properties: (a) the center `B̄_i` of `f̄_i` is either the image
> of `B_i` or the empty subscheme of `X̄(i)`; (b) … then `B̄_i`, `W̄(i)` and `V̄_j(i)` for all `j`
> have the properties (1′), (2) and (3); and finally (c) if `S̄(i)` denotes the complement in `W̄(i)` of the set of those
> points of `W̄(i)` which are simple points of `W̄(i)` and at which all the `V̄_j(i)` (`1 ≤ j ≤ β`) are normally flat
> along `W̄(i)`, then there exists an open neighborhood of `S̄(i)` in `X̄(i)` in which `g_i⁻¹` exists as a morphism.  The
> new succession may be constructed without any difficulty.  (pp. 173–174)

This file is the construction "without any difficulty", by
induction on the succession `{f_i}` (`MonoidalSuccession.exists_isMain123_and_mainUnresolvedAt_eq_empty`).  The
inductive invariant is the *local correspondence* `MainCorr` between the stage `(X(i); V_j(i); W(i))` and the stage
`(X̄(i); V̄_j(i); W̄(i))`, i.e. the part of (c) that is used: two flat preimmersions `ι : Z → X(i)`, `j : Z → X̄(i)`
(open immersions: `j ∘ (g_i|_{Z})⁻¹`) with the same pull-back of `V_j`, `W`, `V̄_j`, `W̄`, whose ranges contain `S(i)`
and `S̄(i)`.  The global morphisms `g_i` are not constructed: nothing but their inverse over the neighborhood of
`S̄(i)` is used.  (Formalization note, encoding.)

* Good step (`B_i ⊆ S(i)`, `exists_step_good`): `B̄_i` is the reduced structure on the closure of the image of
  `B_i` (`FlatPreimm.closureLift`), contained in `S̄(i)` because `S̄(i)` is closed ("`S(i)` is a closed subset");
  the monoidal transformations `f_i`, `f̄_i` and the monoidal transformation of `Z` with the common center are
  compared by lifting the flat preimmersions (`MonoidalTransformation.exists_lift`).
* Bad step (`B_i ∩ S(i) = ∅`, `exists_corr_of_disjoint`): the new transformation has empty center; `Z` is
  shrunk to `Z − ι⁻¹(B_i)` and the preimmersion `ι` is lifted off the center
  (`MonoidalTransformation.exists_lift_of_disjoint`).  That the points of `S(i+1)` lie over `S(i)`, in particular off
  `B_i`, is the persistence of resolvedness (`Subscheme.isMainResolvedAt_strictTransform`: Cor. 2 of Th. 5, Ch. III,
  with the regularity of the strict transform of a simple point of `W` along a center in `W`); the paper uses this
  tacitly ("without affecting (2) and (3)").
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace Hironaka

universe u

section ResolvedAlongBlowup

variable {X : Scheme.{u}} {β : ℕ}

/-- The persistence of resolvedness along a monoidal transformation with a center `B ⊆ W` (used tacitly on p. 173,
"eliminate those monoidal transformation[s] with `B_i` not contained in `S(i)` … without affecting (2) and (3)"):
if `B` is non-singular irreducible with `W − B` dense in `W` and `y` is a point of the strict transform `W'` over a
point `f(y)` at which `W` is simple and all the `V_j` are normally flat along `W`, then `W'` is simple at `y` and all
the `V_j'` are normally flat along `W'` at `y`.  Off the exceptional subscheme `f` is a local isomorphism
(`Subscheme.isMainResolvedAt_strictTransform_of_notMem_exceptional`); on it, simplicity of `W'` is the regularity of the
monoidal transform of the regular local ring `O_{W,f(y)}` along the regular center `B` (Ch. III §2,
`MonoidalTransformation.isRegularLocalRing_quotient_stalkIdeal_strictTransform`) and normal flatness is Corollary 2 of
Theorem 5 (Ch. III, `isNormallyFlatAlongAt'_strictTransform`); the hypothesis of that corollary that `W − B` is dense
in `W` is fact (1) of p. 173 ("nowhere dense"). -/
theorem Subscheme.isMainResolvedAt_strictTransform [Hironaka.HironakaCitedResults.{u}] [IsAlgebraicScheme X] [IrreducibleSpace X]
    (hX : X.IsNonsingular) {V : Fin (β + 1) → Subscheme X} {W B : Subscheme X}
    (hWV : ∀ j, W.IsContainedIn (V j)) (hBc : B.IsCenter) (hBW : B.IsContainedIn W)
    (hdense : W.pts ⊆ closure (W.pts \ B.pts)) (t : MonoidalTransformation X B) {y : t.X'}
    (hy : y ∈ (Subscheme.strictTransform t W).pts)
    (hres : Subscheme.IsMainResolvedAt V W (t.f.base y)) :
    Subscheme.IsMainResolvedAt (fun j => Subscheme.strictTransform t (V j))
      (Subscheme.strictTransform t W) y := by
  by_cases hyE : y ∈ t.exceptional.pts
  · have hxB : t.f.base y ∈ B.pts := by
      rw [MonoidalTransformation.pts_exceptional] at hyE
      exact hyE
    have hBne : B ≠ Subscheme.empty := fun hE => by
      have h2 := congrArg Subscheme.pts hE
      rw [h2, Subscheme.pts_empty] at hxB
      exact hxB
    obtain ⟨hBns, hBirr⟩ := hBc.resolve_left hBne
    refine ⟨⟨hy, ?_⟩, fun j => ?_⟩
    · exact MonoidalTransformation.isRegularLocalRing_quotient_stalkIdeal_strictTransform hX hBns t
        W y (Subscheme.stalkIdeal_le_stalkIdeal_of_isContainedIn hBW _) hres.1.2 hy
    · exact isNormallyFlatAlongAt'_strictTransform ‹_› hX (V j) W B (hWV j) hBW hBns hBirr hdense t
        _ hxB hres.1 (hres.2 j) y hy rfl
  · exact Subscheme.isMainResolvedAt_strictTransform_of_notMem_exceptional t V W hWV hyE hres

end ResolvedAlongBlowup

/-! ### Local correspondence between two stages -/

namespace FlatPreimm

variable {Y Y' : Scheme.{u}} (g : Y' ⟶ Y) [Flat g] [IsPreimmersion g]

/-- Comparison of stalk ideals is invariant under the pull-back along a flat preimmersion. -/
theorem stalkIdeal_totalTransform_le_iff (D E : Subscheme Y) (u : Y') :
    (Subscheme.totalTransform g D).stalkIdeal u ≤ (Subscheme.totalTransform g E).stalkIdeal u ↔
      D.stalkIdeal (g u) ≤ E.stalkIdeal (g u) := by
  rw [Hironaka.stalkIdeal_totalTransform, Hironaka.stalkIdeal_totalTransform]
  constructor
  · intro h
    have := Ideal.comap_mono (f := (g.stalkMap u).hom) h
    rwa [Ideal.comap_map_of_bijective _ (stalkMap_bijective g u),
      Ideal.comap_map_of_bijective _ (stalkMap_bijective g u)] at this
  · exact Ideal.map_mono

/-- A subscheme whose points lie in the range of a flat preimmersion is contained in another one as soon
as the pull-backs are. -/
theorem isContainedIn_of_isContainedIn_totalTransform (D E : Subscheme Y)
    (hD : D.pts ⊆ Set.range g.base)
    (h : (Subscheme.totalTransform g D).IsContainedIn (Subscheme.totalTransform g E)) :
    D.IsContainedIn E := by
  have hle : E ≤ D := by
    refine Subscheme.le_iff_stalkIdeal_le.mpr fun x => ?_
    by_cases hx : x ∈ D.pts
    · obtain ⟨u, rfl⟩ := hD hx
      exact (stalkIdeal_totalTransform_le_iff g E D u).mp
        (Subscheme.le_iff_stalkIdeal_le.mp (show Subscheme.totalTransform g E ≤
          Subscheme.totalTransform g D from fun U => h U) u)
    · rw [Subscheme.stalkIdeal_eq_top_of_notMem_pts hx]
      exact le_top
  exact fun U => hle U

/-- Non-singularity descends along a flat preimmersion whose range contains the subscheme. -/
theorem isNonsingular_of_isNonsingular_totalTransform (D : Subscheme Y)
    (hD : D.pts ⊆ Set.range g.base) (h : (Subscheme.totalTransform g D).IsNonsingular) :
    D.IsNonsingular := by
  refine Subscheme.isNonsingular_of_stalk_quot D fun y hy => ?_
  obtain ⟨u, rfl⟩ := hD hy
  obtain ⟨e⟩ := quotEquiv g D u
  have hu : u ∈ (Subscheme.totalTransform g D).pts := by
    rw [pts_totalTransform]; exact hy
  have := Subscheme.isRegular_stalk_quot _ h hu
  exact IsRegularLocalRing.of_ringEquiv e.symm

end FlatPreimm


/-! ### The local correspondence between two stages -/

section Corr

variable {X Xb : Scheme.{u}} {β : ℕ}

/-- The local correspondence between a stage `(X; V; W)` of the given succession and a stage `(X̄; V̄; W̄)` of the
new succession (pp. 173–174: "there exists a morphism `g_i : X(i) → X̄(i)` … an open neighborhood of `S̄(i)` in
`X̄(i)` in which `g_i⁻¹` exists as a morphism"): two flat preimmersions `ι : Z → X`, `j : Z → X̄` (open
immersions in the application) under which `V_k`, `W` and `V̄_k`, `W̄` have the same pull-back, whose ranges
contain `S(i)` and `S̄(i)` respectively.  (Encoding: only the isomorphism `j ∘ ι⁻¹` between neighborhoods of
`S(i)` and `S̄(i)` is carried, not the global morphism `g_i`, which the rest of the argument never uses.) -/
def MainCorr (V : Fin (β + 1) → Subscheme X) (W : Subscheme X)
    (Vb : Fin (β + 1) → Subscheme Xb) (Wb : Subscheme Xb) : Prop :=
  ∃ (Z : Scheme.{u}) (ι : Z ⟶ X) (j : Z ⟶ Xb), Flat ι ∧ IsPreimmersion ι ∧ Flat j ∧ IsPreimmersion j ∧
    Subscheme.totalTransform ι W = Subscheme.totalTransform j Wb ∧
    (∀ k, Subscheme.totalTransform ι (V k) = Subscheme.totalTransform j (Vb k)) ∧
    Subscheme.mainUnresolved V W ⊆ Set.range ι.base ∧
    Subscheme.mainUnresolved Vb Wb ⊆ Set.range j.base

variable {Z : Scheme.{u}} {V : Fin (β + 1) → Subscheme X} {W : Subscheme X}
  {Vb : Fin (β + 1) → Subscheme Xb} {Wb : Subscheme Xb} (ι : Z ⟶ X) (j : Z ⟶ Xb)
  [Flat ι] [IsPreimmersion ι] [Flat j] [IsPreimmersion j]

/-- Resolvedness at corresponding points. -/
theorem isMainResolvedAt_iff_of_totalTransform_eq
    (hW : Subscheme.totalTransform ι W = Subscheme.totalTransform j Wb)
    (hV : ∀ k, Subscheme.totalTransform ι (V k) = Subscheme.totalTransform j (Vb k))
    (hWV : ∀ k, W.IsContainedIn (V k)) (hWbVb : ∀ k, Wb.IsContainedIn (Vb k)) (z : Z) :
    Subscheme.IsMainResolvedAt V W (ι z) ↔ Subscheme.IsMainResolvedAt Vb Wb (j z) := by
  have hs : W.IsSimpleAt (ι z) ↔ Wb.IsSimpleAt (j z) := by
    rw [← FlatPreimm.isSimpleAt_totalTransform_iff ι W z,
      ← FlatPreimm.isSimpleAt_totalTransform_iff j Wb z, hW]
  have hn : ∀ k, Subscheme.IsNormallyFlatAlongAt' (V k) W (ι z) ↔
      Subscheme.IsNormallyFlatAlongAt' (Vb k) Wb (j z) := fun k => by
    rw [← FlatPreimm.isNormallyFlatAlongAt'_totalTransform_iff ι (V k) W (hWV k) z,
      ← FlatPreimm.isNormallyFlatAlongAt'_totalTransform_iff j (Vb k) Wb (hWbVb k) z, hW, hV k]
  exact and_congr hs (forall_congr' hn)

omit [Flat ι] [IsPreimmersion ι] [Flat j] [IsPreimmersion j] in
/-- Membership in the principal subscheme at corresponding points. -/
theorem mem_pts_iff_of_totalTransform_eq
    (hW : Subscheme.totalTransform ι W = Subscheme.totalTransform j Wb) (z : Z) :
    ι z ∈ W.pts ↔ j z ∈ Wb.pts := by
  have h1 := FlatPreimm.pts_totalTransform ι W
  have h2 := FlatPreimm.pts_totalTransform j Wb
  rw [hW] at h1
  have : z ∈ (Subscheme.totalTransform j Wb).pts ↔ z ∈ ι.base ⁻¹' W.pts := by rw [h1]
  rw [h2] at this
  exact this.symm

/-- `S(i)` and `S̄(i)` at corresponding points. -/
theorem mem_mainUnresolved_iff_of_totalTransform_eq
    (hW : Subscheme.totalTransform ι W = Subscheme.totalTransform j Wb)
    (hV : ∀ k, Subscheme.totalTransform ι (V k) = Subscheme.totalTransform j (Vb k))
    (hWV : ∀ k, W.IsContainedIn (V k)) (hWbVb : ∀ k, Wb.IsContainedIn (Vb k)) (z : Z) :
    ι z ∈ Subscheme.mainUnresolved V W ↔ j z ∈ Subscheme.mainUnresolved Vb Wb := by
  unfold Subscheme.mainUnresolved
  simp only [Set.mem_ofPred_eq]
  rw [mem_pts_iff_of_totalTransform_eq ι j hW z,
    isMainResolvedAt_iff_of_totalTransform_eq ι j hW hV hWV hWbVb z]


/-- **The good step** (p. 174, (a)–(c) for a center `B_i ⊆ S(i)`): given the correspondence, the center
`B̄_i` is "the image of `B_i`" (the reduced structure on the closure of its image, `FlatPreimm.closureLift`),
lies in the open set over which `g_i⁻¹` exists, has the properties (1′), (2), (3), and the correspondence
persists for the blow-ups `f_i`, `f̄_i`. -/
theorem exists_step_good [Hironaka.HironakaCitedResults.{u}] [IsAlgebraicScheme Xb] {B : Subscheme X} (hBc : B.IsCenter)
    (hBW : B.IsContainedIn W)
    (hNF : ∀ x ∈ B.pts, (∀ k, Subscheme.IsNormallyFlatAlongAt' (V k) B x) ∧
      Subscheme.IsNormallyFlatAlongAt' W B x)
    (hWV : ∀ k, W.IsContainedIn (V k)) (hWbVb : ∀ k, Wb.IsContainedIn (Vb k))
    (hcorr : MainCorr V W Vb Wb) (hsub : B.pts ⊆ Subscheme.mainUnresolved V W)
    (t : MonoidalTransformation X B) :
    ∃ (Bb : Subscheme Xb) (tb : MonoidalTransformation Xb Bb), Subscheme.IsMainStep Vb Wb Bb ∧
      MainCorr (fun k => Subscheme.strictTransform t (V k)) (Subscheme.strictTransform t W)
        (fun k => Subscheme.strictTransform tb (Vb k)) (Subscheme.strictTransform tb Wb) := by
  obtain ⟨Z, ι, j, hf1, hp1, hf2, hp2, hW, hV, hS, hSb⟩ := hcorr
  have hBred : B.IsReduced := Hironaka.DatumTransform.isReduced_of_isNonsingular hBc.isNonsingular
  have hBsred : (Subscheme.totalTransform ι B).IsReduced :=
    FlatPreimm.isReduced_totalTransform ι B hBred
  obtain ⟨Bb, hBb⟩ : ∃ Bb : Subscheme Xb, Bb = FlatPreimm.closureLift j (Subscheme.totalTransform ι B) :=
    ⟨_, rfl⟩
  have hBb1 : Subscheme.totalTransform j Bb = Subscheme.totalTransform ι B := by
    rw [hBb]; exact FlatPreimm.totalTransform_closureLift j _ hBsred
  have hSbclosed : IsClosed (Subscheme.mainUnresolved Vb Wb) :=
    Subscheme.isClosed_mainUnresolved Vb Wb hWbVb
  have hBbS : Bb.pts ⊆ Subscheme.mainUnresolved Vb Wb := by
    rw [hBb, FlatPreimm.pts_closureLift]
    refine hSbclosed.closure_subset_iff.mpr ?_
    rintro _ ⟨z, hz, rfl⟩
    have hz' : ι z ∈ B.pts := by
      rw [FlatPreimm.pts_totalTransform] at hz
      exact hz
    exact (mem_mainUnresolved_iff_of_totalTransform_eq ι j hW hV hWV hWbVb z).mp (hsub hz')
  have hrange : ∀ x ∈ Bb.pts, x ∈ Set.range j.base := fun x hx => hSb (hBbS hx)
  have hBbempty : (Subscheme.totalTransform ι B).pts = ∅ → Bb = Subscheme.empty := fun h => by
    refine Subscheme.eq_empty_of_pts_eq_empty ?_
    rw [hBb, FlatPreimm.pts_closureLift, h]
    simp
  have hBbc : Bb.IsCenter := by
    rcases hBc with hB0 | ⟨hns, hirr⟩
    · left
      exact hBbempty (by rw [hB0, Subscheme.totalTransform_empty]; exact Subscheme.pts_empty)
    · rcases FlatPreimm.empty_or_isIrreducible_totalTransform ι B hirr with h | h
      · left
        exact hBbempty (by rw [h]; exact Subscheme.pts_empty)
      · right
        refine ⟨FlatPreimm.isNonsingular_of_isNonsingular_totalTransform j Bb hrange ?_, ?_⟩
        · rw [hBb1]; exact FlatPreimm.isNonsingular_totalTransform ι B hns
        · rw [hBb]; exact FlatPreimm.closureLift_isIrreducible j _ h
  have hBbWb : Bb.IsContainedIn Wb := by
    refine FlatPreimm.isContainedIn_of_isContainedIn_totalTransform j Bb Wb hrange ?_
    rw [hBb1, ← hW]
    exact fun U => FlatPreimm.totalTransform_mono ι (show W ≤ B from fun U => hBW U) U
  have hBV : ∀ k, B.IsContainedIn (V k) := fun k => Subscheme.IsContainedIn.trans hBW (hWV k)
  have hBbVb : ∀ k, Bb.IsContainedIn (Vb k) := fun k => Subscheme.IsContainedIn.trans hBbWb (hWbVb k)
  have hstep : Subscheme.IsMainStep Vb Wb Bb := by
    refine ⟨⟨hBbc, hBbWb⟩, fun x hx => (hBbS hx).2, fun x hx => ?_⟩
    obtain ⟨u, rfl⟩ := hrange x hx
    have hu : ι u ∈ B.pts := by
      have : u ∈ (Subscheme.totalTransform j Bb).pts := by
        rw [FlatPreimm.pts_totalTransform]; exact hx
      rw [hBb1, FlatPreimm.pts_totalTransform] at this
      exact this
    obtain ⟨hV', hW'⟩ := hNF (ι u) hu
    refine ⟨fun k => ?_, ?_⟩
    · refine (FlatPreimm.isNormallyFlatAlongAt'_totalTransform_iff j (Vb k) Bb (hBbVb k) u).mp ?_
      rw [hBb1, ← hV k]
      exact (FlatPreimm.isNormallyFlatAlongAt'_totalTransform_iff ι (V k) B (hBV k) u).mpr (hV' k)
    · refine (FlatPreimm.isNormallyFlatAlongAt'_totalTransform_iff j Wb Bb hBbWb u).mp ?_
      rw [hBb1, ← hW]
      exact (FlatPreimm.isNormallyFlatAlongAt'_totalTransform_iff ι W B hBW u).mpr hW'
  obtain ⟨tb, -⟩ : ∃ tb : MonoidalTransformation Xb Bb, True :=
    ⟨(MonoidalTransformation.exists_isProper Xb Bb).choose, trivial⟩
  obtain ⟨ts, -⟩ : ∃ ts : MonoidalTransformation Z (Subscheme.totalTransform ι B), True :=
    ⟨(MonoidalTransformation.exists_isProper Z (Subscheme.totalTransform ι B)).choose, trivial⟩
  obtain ⟨ι', hι'f, hι'p, -, hι'range, -, hι'st⟩ := MonoidalTransformation.exists_lift t ι rfl ts
  obtain ⟨j', hj'f, hj'p, -, hj'range, -, hj'st⟩ := MonoidalTransformation.exists_lift tb j hBb1 ts
  refine ⟨Bb, tb, hstep, ts.X', ι', j', hι'f, hι'p, hj'f, hj'p, ?_, fun k => ?_, ?_, ?_⟩
  · exact (hι'st W).trans ((congrArg (Subscheme.strictTransform ts) hW).trans (hj'st Wb).symm)
  · exact (hι'st (V k)).trans ((congrArg (Subscheme.strictTransform ts) (hV k)).trans (hj'st (Vb k)).symm)
  · intro y hy
    have hyS := MonoidalSuccession.mainUnresolved_strictTransform_subset t V W hWV
      (fun x hx => (hsub hx).2) hy
    rw [hι'range]
    exact hS hyS
  · intro y hy
    have hyS := MonoidalSuccession.mainUnresolved_strictTransform_subset tb Vb Wb hWbVb
      (fun x hx => (hBbS hx).2) hy
    rw [hj'range]
    exact hSb hyS


/-- **The bad step** (p. 173, "eliminate those monoidal transformations with `B_i` not contained in `S(i)`"):
if `B_i` is disjoint from `S(i)`, the new succession uses the monoidal transformation with empty center
(`X̄(i+1) = X̄(i)`), and the correspondence persists on the open set `Z − ι⁻¹(B_i)`: the points of `S(i+1)`
lie over `S(i)` (Cor. 2 of Th. 5 for the points over `B_i`, which are resolved), hence off `B_i`. -/
theorem exists_corr_of_disjoint [Hironaka.HironakaCitedResults.{u}] [IsAlgebraicScheme X] [IrreducibleSpace X] (hXns : X.IsNonsingular)
    {B : Subscheme X} (hBc : B.IsCenter) (hBW : B.IsContainedIn W)
    (hdense : W.pts ⊆ closure (W.pts \ B.pts))
    (hWV : ∀ k, W.IsContainedIn (V k)) (hWbVb : ∀ k, Wb.IsContainedIn (Vb k))
    (hcorr : MainCorr V W Vb Wb) (hdisj : Disjoint B.pts (Subscheme.mainUnresolved V W))
    (t : MonoidalTransformation X B) :
    MainCorr (fun k => Subscheme.strictTransform t (V k)) (Subscheme.strictTransform t W) Vb Wb := by
  obtain ⟨Z, ι, j, hf1, hp1, hf2, hp2, hW, hV, hS, hSb⟩ := hcorr
  let O : Z.Opens := ⟨ι.base ⁻¹' B.ptsᶜ,
    B.support.isClosed.isOpen_compl.preimage ι.base.hom.continuous⟩
  have hdisj0 : ∀ z : (O : Scheme.{u}), (O.ι ≫ ι) z ∉ B.pts := fun z => by
    show ι (O.ι z) ∉ B.pts
    exact (O.ι_apply z) ▸ z.2
  obtain ⟨ι', hι'f, hι'p, -, hι'range, -, hι'st⟩ :=
    MonoidalTransformation.exists_lift_of_disjoint t (O.ι ≫ ι) hdisj0
  refine ⟨O, ι', O.ι ≫ j, hι'f, hι'p, inferInstance, inferInstance, ?_, fun k => ?_, ?_, ?_⟩
  · rw [hι'st W, Subscheme.totalTransform_comp, hW, ← Subscheme.totalTransform_comp]
  · rw [hι'st (V k), Subscheme.totalTransform_comp, hV k, ← Subscheme.totalTransform_comp]
  · intro y hy
    have hfy : t.f.base y ∈ Subscheme.mainUnresolved V W :=
      ⟨MonoidalTransformation.pts_strictTransform_subset t W hy.1, fun hres =>
        hy.2 (Subscheme.isMainResolvedAt_strictTransform hXns hWV hBc hBW hdense t hy.1 hres)⟩
    obtain ⟨z, hz⟩ := hS hfy
    have hzO : z ∈ O := by
      show ι.base z ∈ B.ptsᶜ
      rw [hz]
      exact Set.disjoint_right.mp hdisj hfy
    rw [hι'range]
    exact ⟨⟨z, hzO⟩, hz⟩
  · intro x hx
    obtain ⟨z, rfl⟩ := hSb hx
    have hzS : ι z ∈ Subscheme.mainUnresolved V W :=
      (mem_mainUnresolved_iff_of_totalTransform_eq ι j hW hV hWV hWbVb z).mpr hx
    have hzO : z ∈ O := Set.disjoint_right.mp hdisj hzS
    exact ⟨⟨z, hzO⟩, rfl⟩

end Corr

/-! ### The elimination -/

/-- The monoidal transformation with empty center (the identity), with `X'` reducibly equal to `Z`, so that a
succession of `Z` can be prefixed by it without transport. -/
@[reducible] noncomputable def MonoidalTransformation.idEmptyR (Z : Scheme.{u}) :
    MonoidalTransformation Z Subscheme.empty :=
  ⟨Z, 𝟙 Z, (MonoidalTransformation.idEmpty Z).invertible, (MonoidalTransformation.idEmpty Z).universal⟩

theorem MonoidalTransformation.strictTransform_idEmptyR {Z : Scheme.{u}} (V : Subscheme Z) :
    Subscheme.strictTransform (MonoidalTransformation.idEmptyR Z) V = V :=
  MonoidalTransformation.strictTransform_idEmpty V

namespace MonoidalSuccession

/-- The facts (1), (2), (3) of p. 173 for a succession, in the form used by the elimination: for each `i`,
the ambient scheme is non-singular irreducible algebraic, `B_i` is a non-singular irreducible subscheme of `W(i)`
which is nowhere dense in it (hence `W(i) − B_i` is dense), `V_j(i)` and `W(i)` are normally flat along `B_i`, and
(1′) `B_i ⊆ S(i)` or `B_i ∩ S(i) = ∅`; finally (3) `S(r) = ∅`, i.e. `W(r)` is non-singular and all `V_j(r)` are
normally flat along it. -/
def IsMainPre : {X Y : Scheme.{u}} → MonoidalSuccession X Y → {β : ℕ} →
    (Fin (β + 1) → Subscheme X) → Subscheme X → Prop
  | _, _, nil _, _, V, W => Subscheme.mainUnresolved V W = ∅
  | X, _, cons B t rest, _, V, W =>
      (IsAlgebraicScheme X ∧ X.IsNonsingular ∧ IrreducibleSpace X) ∧
      (B.IsCenter ∧ B.IsContainedIn W) ∧
      W.pts ⊆ closure (W.pts \ B.pts) ∧
      (∀ x ∈ B.pts, (∀ j, Subscheme.IsNormallyFlatAlongAt' (V j) B x) ∧
        Subscheme.IsNormallyFlatAlongAt' W B x) ∧
      (B.pts ⊆ Subscheme.mainUnresolved V W ∨ Disjoint B.pts (Subscheme.mainUnresolved V W)) ∧
      rest.IsMainPre (fun j => Subscheme.strictTransform t (V j)) (Subscheme.strictTransform t W)

/-- **The elimination of p. 173–174.**  From a succession with the facts (1), (2), (3) and (1′), and any stage
correspondence `MainCorr`, the new succession `{f̄_i}` exists: its centers are the images `B̄_i` of the `B_i`
contained in `S(i)`, and empty otherwise; it satisfies (1), (2), (3) for all `i` and `S̄(r) = ∅`. -/
theorem exists_isMain123_and_mainUnresolvedAt_eq_empty [Hironaka.HironakaCitedResults.{u}] :
    ∀ {X Y : Scheme.{u}} (s : MonoidalSuccession X Y) {β : ℕ} (V : Fin (β + 1) → Subscheme X)
      (W : Subscheme X) {Xb : Scheme.{u}} [IsAlgebraicScheme Xb] (Vb : Fin (β + 1) → Subscheme Xb)
      (Wb : Subscheme Xb),
      s.IsMainPre V W → (∀ k, W.IsContainedIn (V k)) → (∀ k, Wb.IsContainedIn (Vb k)) →
      MainCorr V W Vb Wb →
      ∃ (Yb : Scheme.{u}) (sb : MonoidalSuccession Xb Yb),
        sb.IsMain123 Vb Wb ∧ sb.mainUnresolvedAt Vb Wb = ∅ := by
  intro X Y s
  induction s with
  | nil X =>
    intro β V W Xb _ Vb Wb hpre hWV hWbVb hcorr
    refine ⟨Xb, MonoidalSuccession.nil Xb, trivial, ?_⟩
    obtain ⟨Z, ι, j, hf1, hp1, hf2, hp2, hW, hV, hS, hSb⟩ := hcorr
    show Subscheme.mainUnresolved Vb Wb = ∅
    refine Set.eq_empty_of_forall_notMem fun x hx => ?_
    obtain ⟨z, rfl⟩ := hSb hx
    have := (mem_mainUnresolved_iff_of_totalTransform_eq ι j hW hV hWV hWbVb z).mpr hx
    rw [show Subscheme.mainUnresolved V W = ∅ from hpre] at this
    exact this
  | cons B t rest ih =>
    intro β V W Xb _ Vb Wb hpre hWV hWbVb hcorr
    obtain ⟨⟨hXalg, hXns, hXirr⟩, ⟨hBc, hBW⟩, hdense, hNF, hdich, hrest⟩ := hpre
    have hWV' : ∀ k, (Subscheme.strictTransform t W).IsContainedIn (Subscheme.strictTransform t (V k)) :=
      fun k => MonoidalTransformation.isContainedIn_strictTransform t (hWV k)
    by_cases hsub : B.pts ⊆ Subscheme.mainUnresolved V W
    · obtain ⟨Bb, tb, hstep, hcorr'⟩ := exists_step_good hBc hBW hNF hWV hWbVb hcorr hsub t
      have := tb.isAlgebraicScheme
      obtain ⟨Yb, sb, h123, hS⟩ := ih (fun k => Subscheme.strictTransform t (V k))
        (Subscheme.strictTransform t W) (fun k => Subscheme.strictTransform tb (Vb k))
        (Subscheme.strictTransform tb Wb) hrest hWV'
        (fun k => MonoidalTransformation.isContainedIn_strictTransform tb (hWbVb k)) hcorr'
      exact ⟨Yb, MonoidalSuccession.cons Bb tb sb, ⟨hstep, h123⟩, hS⟩
    · have hdisj := hdich.resolve_left hsub
      have hcorr' := exists_corr_of_disjoint hXns hBc hBW hdense hWV hWbVb hcorr hdisj t
      obtain ⟨Yb, sb, h123, hS⟩ := ih (fun k => Subscheme.strictTransform t (V k))
        (Subscheme.strictTransform t W) Vb Wb hrest hWV' hWbVb hcorr'
      refine ⟨Yb, MonoidalSuccession.cons Subscheme.empty (MonoidalTransformation.idEmptyR Xb) sb,
        ⟨⟨⟨Or.inl rfl, fun U => le_top⟩, fun x hx => ?_, fun x hx => ?_⟩, ?_⟩, ?_⟩
      · rw [Subscheme.pts_empty] at hx; exact hx.elim
      · rw [Subscheme.pts_empty] at hx; exact hx.elim
      · simp only [MonoidalTransformation.strictTransform_idEmptyR]
        exact h123
      · show Subscheme.mainUnresolved _ _ = ∅
        simp only [MonoidalSuccession.strictTransform_cons, MonoidalTransformation.strictTransform_idEmptyR]
        exact hS

end MonoidalSuccession

end Hironaka
