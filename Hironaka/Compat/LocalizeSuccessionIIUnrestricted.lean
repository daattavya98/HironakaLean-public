/-
Copyright (c) 2026 Daattavya Aggarwal, Minhyong Kim, Oisin Kim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daattavya Aggarwal, Minhyong Kim, Oisin Kim
-/
module

public import Hironaka.Compat.LocalizeSuccessionII

/-!
# Compatibility layer for Ch. IV §1: lifting successions for type II data without restriction

Proposition 4 (p. 286) says of its proof only: "The proof is entirely similar to that of
Proposition 3."  Proposition 3 treats a datum `(ℜ^N_II, F)` with a closed restriction `F`
(`Hironaka/Compat/LocalizeSuccessionII.lean`); here the datum carries no restriction, and Theorem
`II₂^{N̄}` replaces `II₁^{N̄}` on `X'_S`.  This file is the argument of pp. 283–285 for a datum
without restriction: the lifting of one monoidal transformation of `X'_S` (the centers
`B'' ⊆ S_ν(_kℜ)` only, no `_kF'`), of a whole succession, with the condition
`S_ν = ∅` in place of `S_ν ∩ F̄ = ∅`.

Where the printed argument of Proposition 3 uses `ν > 0`, it is to apply Theorem `II₁^{N̄}` (which
requires `ν(ℜ̄) > 0`); Theorem `II₂^{N̄}` needs no such hypothesis, so the lifting below does not use it.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace IsLocalRing

namespace Hironaka

universe u

namespace MonoidalSuccession

variable {X Y : Scheme.{u}}

/-- A succession permissible for a type I datum `ℜ_I = (⋃ E_i; V; B'')` with open restriction
is permissible for the type II datum `ℜ` (without restriction), as long as the principal subscheme
`B''` of `ℜ_I` lies in `S_*(ℜ)`, `U` is not empty, and the divisor of `ℜ_I` has the same points as
`⋃ E_i` (the argument of pp. 284–285 for Proposition 4, where the datum carries no restriction, with
the printed invariants "`_kB''` is contained in `S_*(_kℜ^N_II) = S_ν(_kℜ^N_II)`" and "`_kU''` is not
empty": "The monoidal transformation `f'_k` with center `_kC` (which is permissible for `_kℜ''`)
is clearly permissible for `_kℜ'`, because `_kC ⊂ _kB''`.  Since `_kC ≠ _kB''` (for `_kU''` is not
empty), `_{k+1}B''` must be contained in `S_ν(_{k+1}ℜ^N_II)`, and hence `S_ν(_{k+1}ℜ^N_II) =
S_*(_{k+1}ℜ^N_II)`").  The conditions are inherited by the transforms.

Gap in the paper filled, as for `isPermissibleIIClosed_of_isPermissibleIOpen_of_nonempty`: "must be
contained" is the closure of the part off the exceptional subscheme, where `f_k` is a local
isomorphism, together with the closedness of `S_ν` (Lemma 2). -/
theorem isPermissibleII_of_isPermissibleIOpen_of_nonempty [Hironaka.Cited.IsHironakaBaseIsClosedSingularLocus.{u}] [Hironaka.Cited.MonoidalTransformationExistsIsProper.{u}] [Hironaka.Cited.CurveFiniteIntegralClosure.{u}] [Hironaka.Cited.IsRegularLocalRingLocalizationOfIsRegularLocalRing.{u}] (h : MonoidalSuccession X Y) :
    ∀ (ℜ : DatumII.Raw X) (ℜI : DatumI.Raw X) (U : Set X),
      IsAlgebraicScheme X → X.IsNonsingular → ℜ.IsDatum → ℜI.IsDatum →
      ℜI.IsOpenRestriction U → U.Nonempty → ℜI.W.pts ⊆ ℜ.sStar →
      ℜI.E.pts = ℜ.eUnion.pts → h.IsPermissibleIOpen ℜI U →
      h.IsPermissibleII ℜ ∧ (h.transformII ℜ).nu = ℜ.nu ∧
        (h.transformI ℜI).W.pts ⊆ (h.transformII ℜ).sStar ∧
        (h.transformI ℜI).E.pts = (h.transformII ℜ).eUnion.pts := by
  induction h with
  | nil X =>
    intro ℜ ℜI U _ _ _ _ _ _ hWS hE _
    exact ⟨trivial, rfl, hWS, hE⟩
  | cons C t rest ih =>
    intro ℜ ℜI U hXa hX hℜ hℜI hU hUne hWS hE hs
    have := hXa
    obtain ⟨hC, hrest⟩ := hs
    have hCW : C.pts ⊆ ℜI.W.pts := hC.1.pts_subset_W
    -- the center is permissible for `ℜ`: `_kC ⊂ _kB'' ⊆ S_*(_kℜ)`
    have hCperm : ℜ.IsPermissible C := by
      refine ⟨hC.1.1, fun y hy => hWS (hCW hy), fun y hy => ?_⟩
      have := (hC.1.2.2 y hy).2.2
      exact (Subscheme.hasOnlyNormalCrossingsWithAt_congr hE C y).mp this
    -- the transforms
    have := t.isAlgebraicScheme
    have hX' := (t.isNonsingular_and_isNonsingular_exceptional hX hC.1.1.isNonsingular).1
    have hℜ' := (DatumII.Raw.transform_isDatum hX ℜ hℜ t hCperm).1
    obtain ⟨hℜI', -, hU'⟩ := DatumI.Raw.transform_isDatum hX ℜI hℜI t hC.1
    -- `_kC ≠ _kB''` (for `_kU''` is not empty): a point `u` of `U` is not in `C ⊆ W − U`,
    -- and has a point `u'` over it, off the exceptional subscheme, in `W'` and in `U'`
    obtain ⟨u, huU⟩ := hUne
    have huW : u ∈ ℜI.W.pts := by
      obtain ⟨U₀, -, hU₀⟩ := hU.1
      exact (hU₀ ▸ huU).2
    have huC : u ∉ C.pts := fun hu => (hC.2 hu).2 huU
    obtain ⟨u', hu'⟩ := t.exists_apply_eq_of_notMem huC
    have hu'E : u' ∉ t.exceptional.pts := by
      rw [MonoidalTransformation.pts_exceptional]
      exact fun hh => huC (hu' ▸ hh)
    have hu'U : u' ∈ DatumI.Raw.transformOpen t U := show t.f u' ∈ U by rw [hu']; exact huU
    -- `ν(_{k+1}ℜ) = ν`: `u'` lies in `S_ν(_{k+1}ℜ)`, `ν(_{k+1}ℜ) ≤ ν(_kℜ)`
    have hu'S : u' ∈ (ℜ.transform t).sNu ℜ.nu :=
      (DatumII.Raw.mem_sNu_transform_iff_of_notMem hX ℜ t hu'E ℜ.nu).mpr
        (by rw [hu']; exact hWS huW)
    have hν' : (ℜ.transform t).nu = ℜ.nu := le_antisymm
      (DatumII.Raw.nu_transform_le hX ℜ hℜ t hCperm)
      (hu'S.2.trans (le_iSup₂ (f := fun x (_ : x ∈ (ℜ.transform t).S) => (ℜ.transform t).nuAt x)
        u' hu'S.1))
    -- `W' ⊆ S_ν(ℜ')`: "`_{k+1}B''` must be contained in `S_ν(_{k+1}ℜ^N_II)`", and hence
    -- `S_ν = S_*` (`ν(_{k+1}ℜ) = ν`)
    have hWS' : (ℜI.transform t).W.pts ⊆ (ℜ.transform t).sStar := by
      show _ ⊆ (ℜ.transform t).sNu (ℜ.transform t).nu
      rw [hν']
      show (Subscheme.strictTransform t ℜI.W).pts ⊆ _
      rw [MonoidalTransformation.pts_strictTransform_eq_closure]
      refine closure_minimal (fun y hy => ?_) (LocSucc.isClosed_sNu hX' _ ℜ.nu)
      exact (DatumII.Raw.mem_sNu_transform_iff_of_notMem hX ℜ t hy.2 ℜ.nu).mpr (hWS hy.1)
    -- the divisors have the same points
    have hE' : (ℜI.transform t).E.pts = (ℜ.transform t).eUnion.pts := by
      show ((Subscheme.strictTransform t ℜI.E).union t.exceptional).pts =
        (⨅ k, Fin.snoc (α := fun _ => Subscheme t.X')
          (fun i => Subscheme.strictTransform t (ℜ.E i)) t.exceptional k).pts
      rw [Subscheme.union, Subscheme.pts_inf, Subscheme.pts_iInf,
        MonoidalTransformation.pts_strictTransform_congr t hE, DatumII.Raw.eUnion,
        MonoidalTransformation.pts_strictTransform_eq_closure, Subscheme.pts_iInf,
        Set.preimage_iUnion, Set.iUnion_sdiff, closure_iUnion_of_finite]
      ext y
      simp only [Set.mem_union, Set.mem_iUnion, Fin.exists_fin_succ', Fin.snoc_castSucc,
        Fin.snoc_last, MonoidalTransformation.pts_strictTransform_eq_closure]
    obtain ⟨h1, h2, h3, h5⟩ := ih (ℜ.transform t) (ℜI.transform t)
      (DatumI.Raw.transformOpen t U) inferInstance hX' hℜ'
      hℜI' (hU' U hU hC) ⟨u', hu'U⟩ hWS' hE' hrest
    exact ⟨⟨hCperm, h1⟩, h2.trans hν', h3, h5⟩

end MonoidalSuccession

namespace LocSucc

open MonoidalSuccession

variable {X Y : Scheme.{u}}

/-- The lifting step of pp. 283–285 for a non-empty center, for a datum without restriction (the
adapted argument of Proposition 3 for Proposition 4, p. 286: "The proof is entirely similar to that of
Proposition 3"; the closed restriction `F` is dropped, all the other steps are as in
`lift_transformationII`).  Let `j : Z → Y` be a flat
preimmersion into an ambient scheme `Y` of dimension `N`, `ℜ` a type II datum on `Y` with
`ν(ℜ) ≤ ν`, and `B̄` a non-empty center on `Z` contained in
`S_ν(ℜ_Z)` with which `⋃ (E_i)_Z` has only normal crossings.  Let `B''` be the smallest
subscheme of `Y` inducing `B̄`.  Theorem `I₂^{N,n''}`, `n'' = dim B'' < N`, applied to
`(⋃ E_i; B'')` with open restriction the resolved points of `B''`, gives a succession `h` which
is permissible for `ℜ` and whose centers avoid the range of `j`; the strict transform `B*`
of `B''` is then permissible for `h*ℜ` and induces `B̄`.  The succession `h` followed by
the monoidal transformation with center `B*` lifts the monoidal transformation of `Z` with
center `B̄`, the transforms of `ℜ` corresponding up to the identification of p. 275.  Here
`ν(ℜ) = ν` since `B̄ ⊆ S_ν(ℜ_Z)` is non-empty, `_kU''` is not empty, and the permissibility of `h` for `ℜ`
is `isPermissibleII_of_isPermissibleIOpen_of_nonempty`, with the printed invariants of p. 285.

Gap in the paper filled: the paper says only "we see immediately … properties (1)–(3)"; for
the transform of the type II datum by `B*` to induce that by `B̄` one needs that `B*` lies on
exactly those `E_i` whose localizations contain `B̄` (`hcont`, which governs the new
coefficient `a_{α+1}`) and that `ν` does not drop under localization (`hνeq`, which governs
`J·P^{-ν}`).  Also `n'' = dim B'' < N` is derived from `B'' ⊆ S_ν(ℜ)`, which misses the
generic point. -/
theorem lift_transformationII_unrestricted [Hironaka.Cited.IsHironakaBaseIsClosedSingularLocus.{u}] [Hironaka.Cited.MonoidalTransformationExistsIsProper.{u}] [Hironaka.Cited.CurveFiniteIntegralClosure.{u}] [Hironaka.Cited.IsRegularLocalRingLocalizationOfIsRegularLocalRing.{u}] (hL1 : ResolvedSetIsOpen.{u}) (N : ℕ)
    (hI₂ : ∀ n : ℕ, n < N → FundamentalTheorem.I₂.{u} N n) (ν : ℕ∞) {Y Z : Scheme.{u}} (hY : IsAmbient Y N)
    (j : Z ⟶ Y) [Flat j] [IsPreimmersion j] (ℜ : DatumII.Raw Y) (hℜ : ℜ.IsDatum)
    (hν : ℜ.nu ≤ ν) {Bb : Subscheme Z} (hBbc : Bb.IsCenter)
    (hBbne : Bb.pts.Nonempty) (hBbS : Bb.pts ⊆ (ℜ.pullback j).sNu ν)
    (hBbnc : ∀ z ∈ Bb.pts, (ℜ.pullback j).eUnion.HasOnlyNormalCrossingsWithAt Bb z)
    (tb : MonoidalTransformation Z Bb) :
    ∃ (Y' : Scheme.{u}) (s : MonoidalSuccession Y Y') (j' : tb.X' ⟶ Y'), Flat j' ∧
      IsPreimmersion j' ∧ s.IsPermissibleII ℜ ∧ j' ≫ s.composite = tb.f ≫ j ∧
      Set.range j'.base = s.composite.base ⁻¹' Set.range j.base ∧
      DatumII.Raw.SameChar ((s.transformII ℜ).pullback j') ((ℜ.pullback j).transform tb) := by
  have := hY.1
  have := hY.2.2.1
  set B'' := FlatPreimm.closureLift j Bb with hB''
  have hBbirr : Bb.IsIrreducible := by
    rcases hBbc with h | h
    · exfalso
      have : Bb.pts = ∅ := by rw [h]; exact Subscheme.pts_empty
      rw [this] at hBbne
      exact hBbne.ne_empty rfl
    · exact h.2
  have hBbred : Bb.IsReduced := hBbc.isReduced
  have hjB : Subscheme.totalTransform j B'' = Bb :=
    FlatPreimm.totalTransform_closureLift j Bb hBbred
  have hB''red : B''.IsReduced := FlatPreimm.closureLift_isReduced j Bb
  have hB''irr : B''.IsIrreducible := FlatPreimm.closureLift_isIrreducible j Bb hBbirr
  have hmemB'' : ∀ z ∈ Bb.pts, j z ∈ B''.pts := fun z hz => by
    rw [hB'', FlatPreimm.pts_closureLift]
    exact subset_closure ⟨z, hz, rfl⟩
  -- `B'' ⊆ S_ν(ℜ)`
  have hB''S : B''.pts ⊆ ℜ.sNu ν := by
    rw [hB'', FlatPreimm.pts_closureLift]
    refine closure_minimal ?_ (isClosed_sNu hY.2.1 ℜ ν)
    rintro _ ⟨z, hz, rfl⟩
    exact (DatumII.Raw.mem_sNu_pullback j ℜ ν z).mp (hBbS hz)
  -- `ν(ℜ) = ν`, so that `S_ν(ℜ) = S_*(ℜ)` ("`S_*(_kℜ^N_II) = S_ν(_kℜ^N_II)`", p. 285)
  have hνℜ : ℜ.nu = ν := by
    refine le_antisymm hν ?_
    obtain ⟨z, hz⟩ := hBbne
    have hz' := hBbS hz
    exact hz'.2.trans ((le_iSup₂ (f := fun x (_ : x ∈ (ℜ.pullback j).S) => (ℜ.pullback j).nuAt x)
      z hz'.1).trans (DatumII.Raw.nu_pullback_le j ℜ))
  have hStar : ℜ.sNu ν = ℜ.sStar := by rw [DatumII.Raw.sStar, hνℜ]
  -- `n'' = dim B'' < N`
  have hB''ne : B''.pts.Nonempty := by
    obtain ⟨z, hz⟩ := hBbne
    exact ⟨j z, hmemB'' z hz⟩
  have hB''u : B''.pts ≠ Set.univ := fun h =>
    genericPoint_notMem_S hY.2.1 ℜ hℜ (hB''S (h ▸ Set.mem_univ _)).1
  have hdimlt : B''.dim + 1 ≤ (N : WithBot ℕ∞) :=
    (dim_add_one_le_of_pts_ne_univ hB''u hB''ne).trans hY.2.2.2.le
  obtain ⟨n'', hn'', hn''N⟩ := exists_nat_of_add_one_le (Subscheme.dim_ne_bot hB''ne) hdimlt
  -- the type I datum `(⋃ E_i; B'')` and the resolved points `U''` of `B''`
  set ℜI := ℜ.eUnionDatumI B'' with hℜIdef
  have hℜI : ℜI.IsDatum := DatumII.Raw.isDatum_eUnionDatumI hY.2.1 hℜ hB''red
  have hres : ∀ z ∈ Bb.pts, ℜI.ResolvedAt (j z) := by
    intro z hz
    rw [← DatumI.Raw.resolvedAt_pullback_iff j ℜI (fun i => i.elim0) z]
    refine ⟨?_, fun i => i.elim0, ?_⟩
    · show (Subscheme.totalTransform j B'').IsSimpleAt z
      rw [hjB]
      exact ⟨hz, Subscheme.isRegular_stalk_quot Bb hBbc.isNonsingular hz⟩
    · show (Subscheme.totalTransform j ℜ.eUnion).HasOnlyNormalCrossingsWithAt
        (Subscheme.totalTransform j B'') z
      rw [hjB]
      refine (Subscheme.hasOnlyNormalCrossingsWithAt_congr ?_ Bb z).mpr (hBbnc z hz)
      rw [FlatPreimm.pts_totalTransform, DatumII.Raw.pts_eUnion_pullback]
  obtain ⟨U₀, hU₀, hU₀eq⟩ := hL1 Y hY.1 hY.2.1 ℜI hℜI
  set U'' : Set Y := {y ∈ ℜI.W.pts | ℜI.ResolvedAt y} with hU''def
  have hU'' : ℜI.IsOpenRestriction U'' := by
    refine ⟨⟨U₀, hU₀, hU₀eq⟩, ?_, fun y hy => hy.2⟩
    obtain ⟨z, hz⟩ := hBbne
    have hjzU : j z ∈ U₀ ∩ ℜI.W.pts := by
      rw [← hU₀eq]
      exact ⟨hmemB'' z hz, hres z hz⟩
    have hirr := Subscheme.isIrreducible_pts B'' hB''irr
    have := subset_closure_inter_of_isPreirreducible_of_isOpen hirr.2 hU₀
      ⟨j z, hjzU.2, hjzU.1⟩
    rw [hU₀eq, Set.inter_comm]
    exact this
  -- "`_kU''` is not empty" (the points of `B''` over `B̄_b` are resolved)
  have hU''ne : U''.Nonempty := by
    obtain ⟨z, hz⟩ := hBbne
    exact ⟨j z, hmemB'' z hz, hres z hz⟩
  -- Theorem `I₂^{N, n''}`
  obtain ⟨Y₁, h, hperm, hresolved⟩ := hI₂ n'' hn''N Y hY ⟨ℜI, hℜI⟩ U'' hU'' hn''
  have hperm' : h.IsPermissibleIOpen ℜI U'' := hperm
  have havoid : h.CentersAvoid (Set.range j.base) := by
    refine centersAvoid_of_isPermissibleIOpen h ℜI U'' _ hperm' fun y hy hyr => ?_
    obtain ⟨z, rfl⟩ := hyr
    have : j z ∈ j.base '' Bb.pts := by
      rw [← FlatPreimm.pts_closureLift_inter_range]
      exact ⟨hy, z, rfl⟩
    obtain ⟨z', hz', hzz⟩ := this
    have hz'z := j.isEmbedding.injective hzz
    subst hz'z
    exact ⟨hy, hres z' hz'⟩
  -- `h` is permissible for `ℜ` (pp. 284–285)
  obtain ⟨hpermII, hνh, hWSh, hEh⟩ := h.isPermissibleII_of_isPermissibleIOpen_of_nonempty ℜ ℜI
    U'' hY.1 hY.2.1 hℜ hℜI hU'' hU''ne (hStar ▸ hB''S) rfl hperm'
  obtain ⟨j₁, hfl₁, hpre₁, hj₁, hr₁, hst₁, hℜ₁⟩ := h.exists_lift_of_centersAvoidII j havoid
  set Bs := h.strictTransform B'' with hBs
  have hBsj : Subscheme.totalTransform j₁ Bs = Bb := (hst₁ B'').trans hjB
  have hWBs : (h.transformI ℜI).W = Bs := transformI_W h ℜI
  have hresolved' : (h.transformI ℜI).ResolvedEverywhere := hresolved
  have hBsns : Bs.IsNonsingular := Subscheme.isNonsingular_of_stalk_quot Bs fun y hy => by
    have := (hresolved' y (by rw [hWBs]; exact hy)).1.2
    rwa [hWBs] at this
  have hBsirr : Bs.IsIrreducible :=
    strictTransform_isIrreducible_of_centersAvoid h j havoid B'' hB''irr
      (by rw [hjB]; exact hBbne)
  -- the center `B*` is permissible for `h*ℜ`
  have hBsperm : (h.transformII ℜ).IsPermissible Bs := by
    refine ⟨Or.inr ⟨hBsns, hBsirr⟩, fun y hy => ?_, fun y hy => ?_⟩
    · exact hWSh (hWBs ▸ hy)
    · have := (hresolved' y (hWBs ▸ hy)).2.2
      rw [hWBs] at this
      exact (Subscheme.hasOnlyNormalCrossingsWithAt_congr hEh Bs y).mp this
  obtain ⟨ts, -⟩ := MonoidalTransformation.exists_isProper Y₁ Bs
  obtain ⟨j', hfl', hpre', hsq, hr', hexc', hst'⟩ := ts.exists_lift j₁ hBsj tb
  -- `ν` does not drop under the pull-back
  have hSC := hℜ₁ ℜ
  have hνeq : ((h.transformII ℜ).pullback j₁).nu = (h.transformII ℜ).nu := by
    refine le_antisymm (DatumII.Raw.nu_pullback_le j₁ _) ?_
    obtain ⟨z, hz⟩ := hBbne
    have hz' : z ∈ ((h.transformII ℜ).pullback j₁).sNu ν := by
      rw [hSC.sNu_eq]
      exact hBbS hz
    rw [hνh, hνℜ]
    exact hz'.2.trans
      (le_iSup₂ (f := fun x (_ : x ∈ ((h.transformII ℜ).pullback j₁).S) =>
        ((h.transformII ℜ).pullback j₁).nuAt x) z hz'.1)
  -- `B*` lies on exactly those `E_i` whose pull-backs contain `B̄`
  have hBspts : Bs.pts ⊆ closure (j₁.base '' Bb.pts) := by
    have := pts_subset_closure_image j₁ hBsirr (by rw [hBsj]; exact hBbne)
    rwa [hBsj] at this
  have hcont : ∀ i, Bs.IsContainedIn ((h.transformII ℜ).E i) ↔
      Bb.IsContainedIn (Subscheme.totalTransform j₁ ((h.transformII ℜ).E i)) := by
    intro i
    constructor
    · intro hc
      rw [← hBsj]
      exact fun U => FlatPreimm.totalTransform_mono j₁ (show _ ≤ Bs from fun U => hc U) U
    · intro hc
      refine Subscheme.isContainedIn_of_pts_subset (Subscheme.isReduced_of_isNonsingular hBsns)
        (hBspts.trans (closure_minimal ?_ ((h.transformII ℜ).E i).support.isClosed))
      rintro _ ⟨z, hz, rfl⟩
      have := pts_subset_of_isContainedIn hc hz
      rwa [FlatPreimm.pts_totalTransform] at this
  have hmatch := DatumII.Raw.pullback_transform_of_lift ts j₁ tb j' hsq hexc' hst'
    (h.transformII ℜ) hcont hνeq
  refine ⟨ts.X', h.append (cons Bs ts (nil _)), j', hfl', hpre', ?_, ?_, ?_, ?_⟩
  · rw [isPermissibleII_append]
    exact ⟨hpermII, hBsperm, trivial⟩
  · rw [composite_append, composite_cons, composite_nil, Category.id_comp, ← Category.assoc, hsq,
      Category.assoc, hj₁]
  · rw [hr', hr₁, composite_append, composite_cons, composite_nil, Category.id_comp,
      Scheme.Hom.comp_base, TopCat.coe_comp, Set.preimage_comp]
  · rw [transformII_append, transformII_cons, transformII_nil, hmatch]
    exact hSC.transform tb

/-- The lifting step for type II data without restriction (pp. 283–285, adapted to Proposition 4):
a monoidal transformation of `Z`
permissible for `ℜ_Z`, where `ℜ_Z` has the characteristics of the pull-back of `ℜ` and
`ν(ℜ_Z) = ν ≥ ν(ℜ)`, is lifted by a succession of `Y` permissible for `ℜ`; the transforms
correspond again.  (For an empty center, the monoidal transformation of `Y` with empty center
lifts it.) -/
theorem lift_stepII_unrestricted [Hironaka.Cited.IsHironakaBaseIsClosedSingularLocus.{u}] [Hironaka.Cited.MonoidalTransformationExistsIsProper.{u}] [Hironaka.Cited.CurveFiniteIntegralClosure.{u}] [Hironaka.Cited.IsRegularLocalRingLocalizationOfIsRegularLocalRing.{u}] (hL1 : ResolvedSetIsOpen.{u}) (N : ℕ)
    (hI₂ : ∀ n : ℕ, n < N → FundamentalTheorem.I₂.{u} N n) (ν : ℕ∞) {Y Z : Scheme.{u}} (hY : IsAmbient Y N)
    (j : Z ⟶ Y) [Flat j] [IsPreimmersion j] (ℜ : DatumII.Raw Y) (hℜ : ℜ.IsDatum)
    (hν : ℜ.nu ≤ ν) (ℜZ : DatumII.Raw Z)
    (hZ : DatumII.Raw.SameChar ℜZ (ℜ.pullback j)) (hνZ : ℜZ.nu = ν) {Bb : Subscheme Z}
    (hBb : ℜZ.IsPermissible Bb)
    (tb : MonoidalTransformation Z Bb) :
    ∃ (Y' : Scheme.{u}) (s : MonoidalSuccession Y Y') (j' : tb.X' ⟶ Y'), Flat j' ∧
      IsPreimmersion j' ∧ s.IsPermissibleII ℜ ∧
      Set.range j'.base = s.composite.base ⁻¹' Set.range j.base ∧
      DatumII.Raw.SameChar (ℜZ.transform tb) ((s.transformII ℜ).pullback j') := by
  by_cases h0 : Bb.pts.Nonempty
  · have hBbS : Bb.pts ⊆ (ℜ.pullback j).sNu ν := by
      rw [← hZ.sNu_eq, ← hνZ]
      exact hBb.2.1
    have hBbnc : ∀ z ∈ Bb.pts, (ℜ.pullback j).eUnion.HasOnlyNormalCrossingsWithAt Bb z := by
      rw [← hZ.eUnion_eq]
      exact hBb.2.2
    obtain ⟨Y', s, j', hfl, hpre, hperm, -, hr, hSC⟩ := lift_transformationII_unrestricted hL1 N hI₂ ν hY j ℜ hℜ
      hν hBb.1 h0 hBbS hBbnc tb
    exact ⟨Y', s, j', hfl, hpre, hperm, hr, (hZ.transform tb).trans hSC.symm⟩
  · have hBbpts : Bb.pts = ∅ := Set.not_nonempty_iff_eq_empty.mp h0
    have hBe : Bb = Subscheme.empty := Subscheme.eq_empty_of_pts_eq_empty hBbpts
    obtain ⟨j', hfl, hpre, hsq, hr, -, hst⟩ :=
      (MonoidalTransformation.idEmpty Y).exists_lift j
        ((Subscheme.totalTransform_empty j).trans hBe.symm) tb
    refine ⟨Y, cons Subscheme.empty (MonoidalTransformation.idEmpty Y) (nil _), j', hfl, hpre,
      ⟨⟨Or.inl rfl, fun y hy => ?_, fun y hy => ?_⟩, trivial⟩, ?_, ?_⟩
    · rw [Subscheme.pts_empty] at hy
      exact hy.elim
    · rw [Subscheme.pts_empty] at hy
      exact hy.elim
    · change Set.range j'.base = (𝟙 Y ≫ 𝟙 Y : Y ⟶ Y).base ⁻¹' _
      rw [hr]
      rfl
    · have hsq' : j' ≫ (MonoidalTransformation.idEmpty Y).f = tb.f ≫ j := hsq
      have h1 := (DatumII.Raw.sameChar_transform_of_pts_eq_empty tb hBbpts ℜZ).trans
        (hZ.pullback tb.f)
      rw [← DatumII.Raw.pullback_comp, ← hsq', DatumII.Raw.pullback_comp] at h1
      refine h1.trans ?_
      have h2 := DatumII.Raw.sameChar_transform_of_pts_eq_empty
        (MonoidalTransformation.idEmpty Y) Subscheme.pts_empty ℜ
      exact (h2.pullback j').symm

/-- The empty succession of `Y` already has the property required of the lifting as soon as
`S_ν(ℜ_Z) = ∅` (Proposition 4: no restriction). -/
theorem lift_stop_unrestricted (ν : ℕ∞) {Y Z : Scheme.{u}} (j : Z ⟶ Y) [Flat j] [IsPreimmersion j]
    (ℜ : DatumII.Raw Y) (ℜZ : DatumII.Raw Z)
    (hZ : DatumII.Raw.SameChar ℜZ (ℜ.pullback j)) (hempty : ℜZ.sNu ν = ∅) :
    ∃ (Y' : Scheme.{u}) (s : MonoidalSuccession Y Y'), s.IsPermissibleII ℜ ∧
      ∀ y ∈ (s.transformII ℜ).sNu ν, s.composite y ∉ Set.range j.base := by
  refine ⟨Y, nil Y, trivial, fun y hy hyr => ?_⟩
  obtain ⟨z, hz⟩ := hyr
  have hz' : j z = y := hz
  have hz1 : z ∈ ℜZ.sNu ν := by
    rw [hZ.sNu_eq, DatumII.Raw.mem_sNu_pullback, hz']
    exact hy
  exact (Set.eq_empty_iff_forall_notMem.mp hempty) z hz1

end LocSucc

namespace MonoidalSuccession

variable {X Y : Scheme.{u}}

/-- The succession `f̄ = {f̄_j}`, `0 ≤ j ≤ a − 1`, of `X̄_0` is *minimal* for `S_ν(ᵃℜ̄) = ∅` (Proposition 4,
no restriction; p. 283 for Proposition 3: "such that, if `f̄*(ℜ'_S) = (ᵃℜ̄, ᵃF̄)`, then `S_ν(ᵃℜ̄) ∩ ᵃF̄`
is empty.  We may assume that this last condition is not satisfied if we omit the last
transformation `f̄_{a−1}`"): `S_ν(ᵇℜ̄)` is non-empty for `b < a` and empty for `b = a`. -/
def IsMinimalSNuEmptyII (ν : ℕ∞) :
    {X Y : Scheme.{u}} → MonoidalSuccession X Y → DatumII.Raw X → Prop
  | _, _, nil _, ℜ => ℜ.sNu ν = ∅
  | _, _, cons _ t rest, ℜ => (ℜ.sNu ν).Nonempty ∧ rest.IsMinimalSNuEmptyII ν (ℜ.transform t)

/-- "We may assume that this last condition is not satisfied if we omit the last transformation
`f̄_{a−1}`" (p. 283), for a datum without restriction: omitting the last transformation while the
condition `S_ν(ᵃℜ̄) = ∅` persists, one gets a permissible succession which is minimal for it (a
prefix of the given one). -/
theorem exists_isMinimalSNuEmptyII (ν : ℕ∞) (s : MonoidalSuccession X Y) :
    ∀ ℜ : DatumII.Raw X, s.IsPermissibleII ℜ → (s.transformII ℜ).sNu ν = ∅ →
      ∃ (Y' : Scheme.{u}) (s' : MonoidalSuccession X Y'),
        s'.IsPermissibleII ℜ ∧ s'.IsMinimalSNuEmptyII ν ℜ := by
  induction s with
  | nil X =>
    intro ℜ _ h
    exact ⟨X, nil X, trivial, h⟩
  | cons B t rest ih =>
    intro ℜ hs h
    by_cases h0 : (ℜ.sNu ν).Nonempty
    · obtain ⟨Y', s', hp, hm⟩ := ih (ℜ.transform t) hs.2 h
      exact ⟨Y', cons B t s', ⟨hs.1, hp⟩, h0, hm⟩
    · exact ⟨_, nil _, trivial, Set.not_nonempty_iff_eq_empty.mp h0⟩

end MonoidalSuccession

namespace LocSucc

open MonoidalSuccession

/-- Lifting a whole minimal succession for type II data without restriction (pp. 283–285, "(1)–(3)",
as adapted in the proof of Proposition 4, p. 286): if `f̄` is a succession
of `Z` permissible for `ℜ_Z` which is minimal for `S_ν(f̄*ℜ_Z) = ∅`
(`MonoidalSuccession.IsMinimalSNuEmptyII`), where `ℜ_Z` has the
characteristics of the pull-back of `ℜ` and `ν(ℜ) ≤ ν`, then there is a succession `f'` of `Y`
permissible for `ℜ` such that no point of `S_ν(f'*ℜ)` lies over the range of `j`.
By induction on `b`, each center `B̄_b`, `b < a`, being lifted by `lift_stepII_unrestricted`; until
then `ν(ᵇℜ̄) = ν`, because `S_ν(ᵇℜ̄) ≠ ∅` (minimality). -/
theorem lift_successionII_unrestricted [Hironaka.Cited.IsHironakaBaseIsClosedSingularLocus.{u}] [Hironaka.Cited.MonoidalTransformationExistsIsProper.{u}] [Hironaka.Cited.CurveFiniteIntegralClosure.{u}] [Hironaka.Cited.IsRegularLocalRingLocalizationOfIsRegularLocalRing.{u}] (hL1 : ResolvedSetIsOpen.{u}) (N : ℕ)
    (hI₂ : ∀ n : ℕ, n < N → FundamentalTheorem.I₂.{u} N n) (ν : ℕ∞) {Z Z' : Scheme.{u}}
    (sb : MonoidalSuccession Z Z') :
    ∀ {Y : Scheme.{u}} (j : Z ⟶ Y) [Flat j] [IsPreimmersion j] (ℜ : DatumII.Raw Y)
      (ℜZ : DatumII.Raw Z), IsAmbient Y N → ℜ.IsDatum → ℜ.nu ≤ ν →
      DatumII.Raw.SameChar ℜZ (ℜ.pullback j) → sb.IsPermissibleII ℜZ →
      sb.IsMinimalSNuEmptyII ν ℜZ →
      ∃ (Y' : Scheme.{u}) (s : MonoidalSuccession Y Y'), s.IsPermissibleII ℜ ∧
        ∀ y ∈ (s.transformII ℜ).sNu ν, s.composite y ∉ Set.range j.base := by
  induction sb with
  | nil Z =>
    intro Y j _ _ ℜ ℜZ _ _ _ hZ _ hmin
    exact lift_stop_unrestricted ν j ℜ ℜZ hZ hmin
  | cons Bb tb rest ih =>
    intro Y j _ _ ℜ ℜZ hY hℜ hν hZ hsb hmin
    have := hY.1
    obtain ⟨hBb, hrest⟩ := hsb
    obtain ⟨hne, hmin'⟩ := hmin
    -- `ν(ℜ_Z) = ν`: `S_ν(ℜ_Z) ≠ ∅` (minimality)
    have hνZ : ℜZ.nu = ν := by
      refine le_antisymm ?_ ?_
      · rw [hZ.nu_eq]
        exact (DatumII.Raw.nu_pullback_le j ℜ).trans hν
      · obtain ⟨z, hz⟩ := hne
        exact hz.2.trans (le_iSup₂ (f := fun x (_ : x ∈ ℜZ.S) => ℜZ.nuAt x) z hz.1)
    obtain ⟨Y₁, s₁, j₁, hfl₁, hpre₁, hperm₁, hr₁, hSC₁⟩ :=
      lift_stepII_unrestricted hL1 N hI₂ ν hY j ℜ hℜ hν ℜZ hZ hνZ hBb tb
    obtain ⟨hY₁, hℜ₁⟩ := s₁.isAmbient_transformII hY ℜ hℜ hperm₁
    have hν₁ := (s₁.nu_transformII_le hY.2.1 ℜ hℜ hperm₁).trans hν
    obtain ⟨Y', s₂, hperm₂, hlast⟩ := ih j₁ (s₁.transformII ℜ) (ℜZ.transform tb) hY₁ hℜ₁ hν₁ hSC₁
      hrest hmin'
    refine ⟨Y', s₁.append s₂, (isPermissibleII_append _ _ _).mpr ⟨hperm₁, hperm₂⟩,
      fun y hy hyr => ?_⟩
    rw [transformII_append] at hy
    rw [composite_append, Scheme.Hom.comp_apply] at hyr
    refine hlast y hy ?_
    rw [hr₁]
    exact hyr

end LocSucc

end Hironaka
