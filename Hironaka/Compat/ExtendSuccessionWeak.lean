/-
Copyright (c) 2026 Daattavya Aggarwal, Minhyong Kim, Oisin Kim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daattavya Aggarwal, Minhyong Kim, Oisin Kim
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Architect
public import Hironaka.Compat.BlowupLocalIso
public import Hironaka.Compat.ExtendSuccession
public import Hironaka.Compat.LocalizeSuccessionII
public import Hironaka.Compat.WeakTransformProduct
public import Hironaka.Statements

/-!
# Extension of a succession from an open piece, with the weak transforms of a system of ideals (Ch. 0 §5, p. 144)

> By (ii) of main theorem II, we see that all the `D̄(i)` are mapped into the closed subset `T − S` of the
> underlying topological space of `X`.  Thus we get a finite succession of monoidal transformations
> `f_i : X(i + 1) → X(i)` with non-singular irreducible centers `D(i)` in `X(i)`, where `X(0) = X` and
> `0 ≦ i < r̄`, such that there exists an open immersion `u_i : X̄(i) → X(i)` for each `i` having the
> properties that `u_i(D̄(i)) = D(i)` and `u_i ∘ f̄_i = f_i ∘ u_{i+1}` for all `i`, where `u_0` is the canonical
> immersion.  (p. 144, proof of Corollary 1)

`MonoidalSuccession.exists_extension` (`Compat/ExtendSuccession.lean`) constructs the succession `f_i` of
`X(0) = X` from the succession `f̄_i` of the open subscheme `X̄ = X − S` whose centers `D̄(i)` are mapped into a
closed subset `C = T − S` contained in `X̄`, and the open immersions `u_i`.  The proof of Corollary 1 follows the
weak transforms `J_j(i)` of a *system* `(J_j)` of sheaves of ideals along the two successions.  This file adds
that to the extension: with `J_j(i)` the weak transforms of `J_j` along the extended succession, `u_i⁻¹(J_j(i))`
are the weak transforms of `u_0⁻¹(J_j)` along the given one (`Subscheme.totalTransform_weakTransform_of_lift`; a
step the paper does not argue), and property (1) of Corollary 1 for the given succession (which is stated for
`X̄`) gives property (1) for the extended one (`MonoidalSuccession.IsTrivializingSteps`).  Moreover, at the points
of `X(i)` lying over a point outside the closed set `C` the succession is a local isomorphism, so `J_j(i)` is the
unit ideal there iff `J_j` is at the image point (`MonoidalSuccession.stalkIdeal_weakTransformFamily_eq_top_iff`).
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

namespace Hironaka

universe u

/-! ### The weak transforms `J_j(i)` of a system, and the property (1) of Corollary 1 -/

namespace MonoidalSuccession

variable {e : ℕ}



end MonoidalSuccession

/-! ### Flat preimmersions: `ν` and the sup of ideal sheaves -/

namespace FlatPreimm

variable {Y Y' : Scheme.{u}} (g : Y' ⟶ Y) [Flat g] [IsPreimmersion g]

/-- The total transform along a flat preimmersion commutes with suprema of ideal sheaves (the stalks are
identified by the stalk isomorphisms). -/
theorem totalTransform_iSup {ι : Sort*} (K : ι → Subscheme Y) :
    Subscheme.totalTransform g (⨆ i, K i) = ⨆ i, Subscheme.totalTransform g (K i) := by
  refine Subscheme.ext_stalkIdeal fun z => ?_
  rw [stalkIdeal_totalTransform, Subscheme.stalkIdeal_iSup_eq', Subscheme.stalkIdeal_iSup_eq',
    Ideal.map_iSup]
  exact iSup_congr fun i => (stalkIdeal_totalTransform g (K i) z).symm

/-- `ν` is preserved by the total transform along a flat preimmersion (`O_{Y,g z} ≅ O_{Y',z}`). -/
theorem nu_stalkIdeal_totalTransform (J : Subscheme Y) (z : Y') :
    Ideal.nu ((Subscheme.totalTransform g J).stalkIdeal z) = Ideal.nu (J.stalkIdeal (g z)) := by
  rw [stalkIdeal_totalTransform]
  exact LocSucc.nu_map_ringEquiv (stalkEquiv g z) _

end FlatPreimm

/-! ### The weak transform and the lifting of a monoidal transformation along a flat preimmersion -/

namespace Subscheme

variable {Y Z : Scheme.{u}}

/-- With no generic point of the center (i.e. an empty center), the weak transform is the total transform
(`f` is then the identity; Remark 2, p. 214: "If `B` is empty, we have `X' = X` with the identity `f` and we put
`J' = J`"). -/
theorem weakTransform_eq_totalTransform_of_not_exists {B : Subscheme Y} (t : MonoidalTransformation Y B)
    (K : Subscheme Y) (h : ¬ ∃ ξ : Y, IsGenericPoint ξ B.pts) :
    Subscheme.weakTransform t K = Subscheme.totalTransform t.f K := by
  unfold Subscheme.weakTransform
  simp only [h, dite_false]

/-- **The weak transform commutes with the lifting of a monoidal transformation along a flat preimmersion**
(the step "`u_i⁻¹` of the weak transform is the weak transform" of the proof of Corollary 1, p. 144, which the paper
does not argue): let `t` be a monoidal transformation of `Y` with center `B`, `g : Z → Y` a flat preimmersion,
`ts` a monoidal transformation of `Z` with center `Bs = g⁻¹(B)` and `g' : Z' → Y'` a flat preimmersion over `g`
with `g'⁻¹(P_E) = P_{E_s}`, where `B = \overline{g(Bs)}`.  Then `g'⁻¹(J') = (g⁻¹ J)'` for the weak transforms.
The generic point of `Bs` maps to that of `B`, `ν` is preserved (`O_{Y,g ξ_s} ≅ O_{Z,ξ_s}`), and the divisions
`f⁻¹(J)·P_E⁻ᵛ` are compatible with `g'⁻¹`. -/
theorem totalTransform_weakTransform_of_lift {B : Subscheme Y} (t : MonoidalTransformation Y B)
    (g : Z ⟶ Y) [Flat g] [IsPreimmersion g] {Bs : Subscheme Z} (ts : MonoidalTransformation Z Bs)
    (g' : ts.X' ⟶ t.X') [Flat g'] [IsPreimmersion g'] (hsq : g' ≫ t.f = ts.f ≫ g)
    (hexc : Subscheme.totalTransform g' t.exceptional = ts.exceptional)
    (hBpts : B.pts = g.base '' Bs.pts) (hBs : Subscheme.totalTransform g B = Bs) (J : Subscheme Y) :
    Subscheme.totalTransform g' (Subscheme.weakTransform t J) =
      Subscheme.weakTransform ts (Subscheme.totalTransform g J) := by
  have hcomm : Subscheme.totalTransform g' (Subscheme.totalTransform t.f J) =
      Subscheme.totalTransform ts.f (Subscheme.totalTransform g J) := by
    rw [← Subscheme.totalTransform_comp, hsq, Subscheme.totalTransform_comp]
  have hemb := g.isEmbedding
  have hBclosed : IsClosed B.pts := B.support.isClosed
  have hBsp : Bs.pts = g.base ⁻¹' B.pts := by rw [← hBs, FlatPreimm.pts_totalTransform]
  -- the generic points of `Bs` and of `B` correspond
  have hgen : ∀ ξs : Z, IsGenericPoint ξs Bs.pts → IsGenericPoint (g.base ξs) B.pts := by
    intro ξs hξs
    show closure {g.base ξs} = B.pts
    apply Set.Subset.antisymm
    · exact closure_minimal (Set.singleton_subset_iff.mpr
        (by rw [hBpts]; exact ⟨ξs, hξs.mem, rfl⟩)) hBclosed
    · rw [hBpts, ← hξs.def]
      exact (image_closure_subset_closure_image g.base.hom.continuous).trans
        (by rw [Set.image_singleton])
  have hgen' : (∃ ξ : Y, IsGenericPoint ξ B.pts) → ∃ ξs : Z, IsGenericPoint ξs Bs.pts := by
    rintro ⟨ξ, hξ⟩
    have hξB : ξ ∈ B.pts := hξ.mem
    rw [hBpts] at hξB
    obtain ⟨ξs, -, rfl⟩ := hξB
    refine ⟨ξs, ?_⟩
    show closure {ξs} = Bs.pts
    rw [hemb.isInducing.closure_eq_preimage_closure_image, Set.image_singleton, hξ.def, hBsp]
  by_cases hs : ∃ ξs : Z, IsGenericPoint ξs Bs.pts
  swap
  · have hB : ¬ ∃ ξ : Y, IsGenericPoint ξ B.pts := fun h => hs (hgen' h)
    rw [weakTransform_eq_totalTransform_of_not_exists t _ hB,
      weakTransform_eq_totalTransform_of_not_exists ts _ hs, hcomm]
  obtain ⟨ξs, hξs⟩ := hs
  rw [Subscheme.weakTransform_eq t J (hgen ξs hξs), Subscheme.weakTransform_eq ts _ hξs,
    FlatPreimm.totalTransform_iSup, FlatPreimm.nu_stalkIdeal_totalTransform g J ξs]
  refine iSup_congr fun ν => ?_
  rw [FlatPreimm.totalTransform_iSup]
  refine iSup_congr fun _ => ?_
  rw [Subscheme.totalTransform_divPow g' _ t.exceptional t.invertible, hexc, hcomm]

/-- Off the exceptional subscheme the stalks of the weak transform are those of the total transform
(Remark 2, p. 214: `J'` and `f⁻¹(J)` differ only at the points of `f⁻¹(B)`). -/
theorem stalkIdeal_weakTransform_eq_of_notMem {B : Subscheme Y} (t : MonoidalTransformation Y B)
    (J : Subscheme Y) {y : t.X'} (hy : y ∉ t.exceptional.pts) :
    (Subscheme.weakTransform t J).stalkIdeal y = (Subscheme.totalTransform t.f J).stalkIdeal y := by
  by_cases h : ∃ ξ : Y, IsGenericPoint ξ B.pts
  · obtain ⟨ξ, hξ⟩ := h
    rw [Subscheme.stalkIdeal_weakTransform t J hξ y, Subscheme.stalkIdeal_eq_top_of_notMem_pts hy]
    simp only [Ideal.top_pow, Submodule.top_coe, Submodule.colon_univ]
    exact le_antisymm (iSup₂_le fun _ _ => le_rfl) (le_iSup₂_of_le 0 (by simp) le_rfl)
  · rw [weakTransform_eq_totalTransform_of_not_exists t J h]

end Subscheme

/-! ### Extension of a succession of an open piece, with the weak transforms of a system -/

namespace MonoidalSuccession

variable {Z Z' Y : Scheme.{u}} {e : ℕ}

/-- **Extension of a succession of an open piece, with the weak transforms of a system of ideals** (p. 144, proof of
Corollary 1): this is `MonoidalSuccession.exists_extension` (the closed set `C` is `T − S`, `j` the canonical
immersion `u_0 : X̄ → X`) together with: the centers of the extended succession lie in `C` (`CentersClosedIn`), the
weak transforms `J_j(i)` of a system `(J_j)` of `Y` along the extended succession pull back under `j'` to the weak
transforms of `j⁻¹(J_j)` along the given one, and property (1) of Corollary 1 (`IsTrivializingSteps`) for the given
succession and the pulled-back system gives property (1) for the extended one and the system. -/
theorem exists_extension_weak [Hironaka.Cited.MonoidalTransformationExistsIsProper.{u}] (s : MonoidalSuccession Z Z') :
    ∀ {Y : Scheme.{u}} (j : Z ⟶ Y) [Flat j] [IsPreimmersion j] (C : Set Y), IsClosed C →
      C ⊆ Set.range j.base → s.CentersClosedIn j C →
      ∃ (Y' : Scheme.{u}) (sY : MonoidalSuccession Y Y') (j' : Z' ⟶ Y'), Flat j' ∧
        IsPreimmersion j' ∧ j' ≫ sY.composite = s.composite ≫ j ∧
        Set.range j'.base = sY.composite.base ⁻¹' Set.range j.base ∧
        sY.CentersClosedIn (𝟙 Y) C ∧
        ∀ {e : ℕ} (J : Fin e → Subscheme Y),
          (∀ k, Subscheme.totalTransform j' (sY.weakTransformFamily J k) =
            s.weakTransformFamily (fun k => Subscheme.totalTransform j (J k)) k) ∧
          (s.IsTrivializingSteps (fun k => Subscheme.totalTransform j (J k)) →
            sY.IsTrivializingSteps J) := by
  induction s with
  | nil Z =>
    intro Y j _ _ C _ _ _
    exact ⟨Y, nil Y, j, inferInstance, inferInstance, by simp, by simp, trivial,
      fun J => ⟨fun k => rfl, fun _ => trivial⟩⟩
  | cons B ts rest ih =>
    intro Y j _ _ C hC hCj hs
    obtain ⟨hBred, hBC, hrest⟩ := hs
    have hcl : IsClosed (j.base '' B.pts) := by
      have h1 : closure (j.base '' B.pts) ⊆ C := closure_minimal hBC hC
      have h2 := FlatPreimm.pts_closureLift_inter_range j B
      rw [FlatPreimm.pts_closureLift] at h2
      rw [← h2, Set.inter_eq_left.mpr (h1.trans hCj)]
      exact isClosed_closure
    obtain ⟨BY, tY, j', hfl, hpre, hBYred, hBYpts, htt, hsq, hrange, hexc, -⟩ :=
      MonoidalTransformation.exists_extend_step j hBred hcl ts
    obtain ⟨Y', sY, j'', hfl', hpre', hcomp, hrange', hcc, hfam⟩ :=
      ih j' (tY.f.base ⁻¹' C) (hC.preimage tY.f.continuous)
        (fun y hy => by rw [hrange]; exact hCj hy)
        ((centersClosedIn_comp rest j' tY.f C).mp (by rw [hsq]; exact hrest))
    have hrng : BY.pts ⊆ Set.range j.base := by
      rw [hBYpts]; rintro _ ⟨z, -, rfl⟩; exact ⟨z, rfl⟩
    have hlift : ∀ J : Subscheme Y, Subscheme.totalTransform j' (Subscheme.weakTransform tY J) =
        Subscheme.weakTransform ts (Subscheme.totalTransform j J) := fun J =>
      Subscheme.totalTransform_weakTransform_of_lift tY j ts j' hsq hexc hBYpts htt J
    refine ⟨Y', cons BY tY sY, j'', hfl', hpre', ?_, ?_, ?_, ?_⟩
    · rw [composite_cons, composite_cons, ← Category.assoc, hcomp, Category.assoc, hsq,
        Category.assoc]
    · rw [hrange', composite_cons, hrange]
      rfl
    · refine ⟨hBYred, ?_, ?_⟩
      · rw [hBYpts]
        simpa using hBC
      · rw [Category.comp_id]
        simpa using (centersClosedIn_comp sY (𝟙 _) tY.f C).mpr hcc
    · intro e J
      obtain ⟨hfam1, hfam2⟩ := hfam (fun k => Subscheme.weakTransform tY (J k))
      have hfun : (fun k => Subscheme.totalTransform j' (Subscheme.weakTransform tY (J k))) =
          fun k => Subscheme.weakTransform ts (Subscheme.totalTransform j (J k)) :=
        funext fun k => hlift (J k)
      refine ⟨fun k => ?_, fun hT => ?_⟩
      · show Subscheme.totalTransform j'' (sY.weakTransformFamily
          (fun k => Subscheme.weakTransform tY (J k)) k) =
            rest.weakTransformFamily (fun k => Subscheme.weakTransform ts
              (Subscheme.totalTransform j (J k))) k
        rw [hfam1 k, hfun]
      · obtain ⟨hB, hconst, hrestT⟩ := hT
        refine ⟨DatumI.Raw.isCenter_of_totalTransform_eq j htt hrng hB, fun k => ?_,
          hfam2 (by rw [hfun]; exact hrestT)⟩
        obtain ⟨c, hc, hcB⟩ := hconst k
        refine ⟨c, hc, fun y hy => ?_⟩
        obtain ⟨z, hz, rfl⟩ : y ∈ j.base '' B.pts := hBYpts ▸ hy
        rw [← FlatPreimm.nu_stalkIdeal_totalTransform j (J k) z]
        exact hcB z hz

/-- **Off the centers the extended succession is a local isomorphism**: if the centers of the succession `s` (of
`Y`) lie over `C` (`CentersClosedIn`) and the image `composite(x)` of a point `x` of the last scheme is not in
`C`, then `J_j(r)_x` is the unit ideal iff `J_j` is at the point `composite(x)` (the weak transform and the total
transform agree off the exceptional subscheme, and the stalk maps off the centers are isomorphisms). -/
theorem stalkIdeal_weakTransformFamily_eq_top_iff {Y' : Scheme.{u}} (s : MonoidalSuccession Y Y') :
    ∀ (C : Set Y), s.CentersClosedIn (𝟙 Y) C → ∀ {e : ℕ} (J : Fin e → Subscheme Y) (x : Y'),
      s.composite.base x ∉ C → ∀ k,
        (s.weakTransformFamily J k).stalkIdeal x = ⊤ ↔
          (J k).stalkIdeal (s.composite.base x) = ⊤ := by
  induction s with
  | nil Y =>
    intro C _ e J x _ k
    exact Iff.rfl
  | cons B t rest ih =>
    intro C hs e J x hx k
    obtain ⟨-, hBC, hrest⟩ := hs
    have hy : t.f.base (rest.composite.base x) ∉ C := by
      simpa [composite_cons] using hx
    have hyB : t.f.base (rest.composite.base x) ∉ B.pts := fun h =>
      hy (by simpa using hBC ⟨_, h, rfl⟩)
    have hyE : rest.composite.base x ∉ t.exceptional.pts := by
      rw [MonoidalTransformation.pts_exceptional]
      exact hyB
    have hrest' : rest.CentersClosedIn (𝟙 t.X') (t.f.base ⁻¹' C) := by
      have := (centersClosedIn_comp rest (𝟙 _) t.f C).mp
      rw [Category.id_comp] at this
      exact this (by simpa using hrest)
    have hih := ih (t.f.base ⁻¹' C) hrest' (fun k => Subscheme.weakTransform t (J k)) x hy k
    rw [show (cons B t rest).weakTransformFamily J k =
        rest.weakTransformFamily (fun k => Subscheme.weakTransform t (J k)) k from rfl, hih,
      Subscheme.stalkIdeal_weakTransform_eq_of_notMem t (J k) hyE, stalkIdeal_totalTransform]
    simp only [composite_cons]
    have hbij := t.bijective_stalkMap_of_notMem_pts _ hyB
    constructor
    · intro h
      have := congrArg (Ideal.comap (t.f.stalkMap (rest.composite.base x)).hom) h
      rwa [Ideal.comap_map_of_bijective _ hbij, Ideal.comap_top] at this
    · intro h
      have h' : (J k).stalkIdeal (t.f.base (rest.composite.base x)) = ⊤ := h
      rw [h', Ideal.map_top]

end MonoidalSuccession

end Hironaka
