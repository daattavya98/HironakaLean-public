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
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Architect
public import Hironaka.Ch4.AuxiliaryDatumRepair
public import Hironaka.Statements

/-!
# Ch. IV §4 (pp. 311-326): Theorem C and the implication (C)

> We shall prove the following Theorems C and D, which complete the inductive proof of all the
> theorems stated in Ch. I.  (p. 311)

This file proves Theorem C (closed restriction) from the common construction of pp. 314-326, as
formalized in `Ch4/ImplicationsCD.lean` (the frame, the lifting of successions of `X̃` and the
non-vanishing `J̄(s) ≠ 0`) and in `Ch4/AuxiliaryDatumRepair.lean` (the repaired auxiliary datum
`ℜ^{N-1}_II`, repairing the paper's error on the subschemes `Ẽ_j`, p. 308).  The file is separate because the closed
core step needs the repair, which itself imports `ImplicationsCD`.

* the closed core step (`CD.exists_extension_not_mem_sNuImageClosed`, pp. 320-326), proved
  with the repaired auxiliary datum (`lem:IV.4-core-step-closed`),
* the induction on the finitely many points of `h_s(S_ν(ℜ(s)))` (p. 326) and the localization,
* Theorem C (`thm:IV.C`), and the implication (C) of Ch. I §2 (`impl:C`; the Ch. I node is a pointer
  to this proof).
-/

@[expose] public section

open AlgebraicGeometry IsLocalRing CategoryTheory CategoryTheory.Limits

namespace Hironaka

universe u

noncomputable section

namespace CD

section ClosedLifting

variable {N : ℕ} {X : Scheme.{u}}

/-- **`J̄(s)` has non-zero stalks when the shifted threshold is `0`** (`d_s = b - ν - δ_s = 0`,
which contains the case `ν ≥ b`; p. 321).  Without restriction and for `ν ≥ b` this is
`stalkIdeal_jBar_ne_bot`.  For `ν < b`, `F = E_i`, the weight of the dropped traces `Ẽ_j = X̃`
(components `E_j ⊇ F`) makes the points of `F` with `ν(J_y) ≥ ν` lie in `S(ℜ)`
(`mem_S_of_thresholdRep_eq_zero`), which is what the argument of
`stalkIdeal_jBar_ne_bot_of_forall_isNonsingular` needs. -/
theorem Frame.stalkIdeal_jBar_ne_bot_of_thresholdRep_eq_zero [Hironaka.HironakaCitedResults.{u}] {ℜ : DatumII.Raw X}
    {r : Restriction X} {ν : ℕ} {T : AB.Tower X} {x₀ : X} {hS : Standing N ℜ r ν T x₀}
    (𝒮 : Frame hS) {s : ℕ} (hprep : PrepHyp N ℜ r ν T x₀ s) (h0 : 𝒮.thresholdRep s = 0)
    (xb : 𝒮.xTilde s) : (𝒮.jBar s).stalkIdeal xb ≠ ⊥ := by
  have hadm := 𝒮.isAdmissibleAt_of_prepHyp hprep
  exact 𝒮.stalkIdeal_jBar_ne_bot_of_forall_isNonsingular
    (fun y hy hF => 𝒮.mem_S_of_thresholdRep_eq_zero hprep h0 hy hF)
    (fun t ht => (hadm.2.2.1 t ht).1.1) s le_rfl xb

namespace LiftData

variable {ℜ : DatumII.Raw X} {F : Subscheme X} {ν : ℕ} {x₀ : X}
  (L : LiftData N ℜ (Restriction.closed F) ν x₀)

/-- The motive of the induction for the repaired auxiliary datum: at the stage `g`, the emptied
and shifted datum `ℜ̃` (with its factorization `J̃ ∏ (P̃^e_j)^{ã_j}` of `J̄^♯(s)`) is resolvable by a
succession of exactly `k` monoidal transformations. -/
def QRep {Y : Scheme.{u}} (g : MonoidalSuccession X Y) (k : ℕ) : Prop :=
  ∃ (n : ℕ) (σ : FrameStage Y) (D : DatumII.Raw Y), g.length = n ∧ σ = L.stage g ∧
    D = g.transformII ℜ ∧
    ∃ (a : ℕ → ℕ) (Jt : Subscheme σ.xBar.toScheme),
      Jt * ∏ j : Fin (alphaT (Restriction.closed F) ℜ.α n),
        ((σ.eTilde D (Restriction.closed F) ℜ.α n j).emptyIfBot) ^ a j =
          σ.jBarRep D (Restriction.closed F) ℜ.α n ℜ.b ν ν.factorial ∧
      DatumII.Raw.ResolvableLen k
        (σ.datumRep D (Restriction.closed F) ℜ.α n ℜ.b ν ν.factorial (fun j => a j) Jt)

/-- The end of the induction at the level of stages: if `x_0 ∈ h(S_ν(ℜ(s)))`, the repaired datum
`ℜ̃` is not resolved at the stage `g`. -/
theorem not_QRep_zero [Hironaka.HironakaCitedResults.{u}] (hN : 1 ≤ N) (hX : IsAmbient X N) (hℜ : ℜ.IsDatum)
    (hF : ℜ.IsClosedRestriction F) (hν : 0 < ν) (hνeq : (ν : ℕ∞) = nu ℜ (.closed F))
    (hνeq' : (ν : ℕ∞) = ℜ.nu) (hno : NoCodimOneComponent (sNu ℜ (.closed F) ν))
    {Y : Scheme.{u}} (g : MonoidalSuccession X Y) (hP : PreparedClosed N ℜ F ν g)
    (hx : x₀ ∈ sNuImageClosed g ℜ F ν) : ¬ L.QRep g 0 := by
  rintro ⟨n, σ, D, hn, hσ, hD, a, Jt, hJt, hres⟩
  obtain ⟨T, n', h, hpre, -, hS, hprep⟩ := exists_standing_prepHyp_tower_closed hN hX ℜ hℜ F hF
    ν hν hνeq hνeq' hno g hP hx
  subst h
  have hpre' : T.pre n' = g := hpre
  subst hpre'
  obtain rfl : n = n' := hn.symm.trans (AB.Tower.length_pre T n')
  have := L.reg
  have hσ' : σ = (Frame.canon hS L.z L.jGen L.fr).stageOf n :=
    hσ.trans (Frame.canon_stageOf_eq_fold n).symm
  subst hσ'
  subst hD
  generalize Frame.canon hS L.z L.jGen L.fr = 𝒮 at *
  change Subscheme (𝒮.xTilde n) at Jt
  have hS' : (𝒮.datumRep n (fun j => a j) Jt).S = ∅ := by
    rw [𝒮.datumRep_eq_stageOf]
    exact hres
  have hJt' : Jt * ∏ j, ((𝒮.eTilde n j).emptyIfBot) ^ (a j) = 𝒮.jBarRep n := by
    have h1 : (∏ j : Fin (alphaT (Restriction.closed F) ℜ.α n),
        ((𝒮.eTilde n j).emptyIfBot) ^ (a j)) =
        ∏ j, ((((𝒮.stageOf n).eTilde (datum T ℜ n) (Restriction.closed F) ℜ.α n j)).emptyIfBot)
          ^ (a j) :=
      Finset.prod_congr rfl fun j _ => by rw [𝒮.eTilde_eq_stageOf]; rfl
    rw [h1]
    exact hJt.trans (𝒮.jBarRep_eq_stageOf n).symm
  have hJne := 𝒮.stalkIdeal_ne_bot_of_mul_eq_jBarRep hprep
    (fun h0 x => 𝒮.stalkIdeal_jBar_ne_bot_of_thresholdRep_eq_zero hprep h0 x) (fun j => a j) Jt
    hJt'
  obtain ⟨xb, hxb⟩ := 𝒮.S_datumRep_nonempty hprep (fun j => a j) Jt hJt' hJne
  rw [hS'] at hxb
  exact hxb

/-- **Remarks 1 and 2 at the level of stages** (pp. 322-323), for the repaired datum: a monoidal
transformation of `X̃` permissible for `ℜ̃` and with non-singular irreducible center `B̃` comes from
a center `B_s` of `X_s` permissible for `ℜ(s)` (with the closed restriction `F(s)`), with
`B̃ = c_s⁻¹(B_s)`. -/
theorem exists_center_closed [Hironaka.HironakaCitedResults.{u}] (hN : 1 ≤ N) (hX : IsAmbient X N) (hℜ : ℜ.IsDatum)
    (hF : ℜ.IsClosedRestriction F) (hν : 0 < ν) (hνeq : (ν : ℕ∞) = nu ℜ (.closed F))
    (hνeq' : (ν : ℕ∞) = ℜ.nu) (hno : NoCodimOneComponent (sNu ℜ (.closed F) ν))
    {Y : Scheme.{u}} (g : MonoidalSuccession X Y) (hP : PreparedClosed N ℜ F ν g)
    (hx : x₀ ∈ sNuImageClosed g ℜ F ν) {n : ℕ} (hn : g.length = n) {σ : FrameStage Y}
    (hσ : σ = L.stage g) {D : DatumII.Raw Y} (hD : D = g.transformII ℜ) (a : ℕ → ℕ)
    (Jt : Subscheme σ.xBar.toScheme)
    (hJt : Jt * ∏ j : Fin (alphaT (Restriction.closed F) ℜ.α n),
      ((σ.eTilde D (Restriction.closed F) ℜ.α n j).emptyIfBot) ^ a j =
        σ.jBarRep D (Restriction.closed F) ℜ.α n ℜ.b ν ν.factorial)
    (Bt : Subscheme σ.xBar.toScheme) (hBt : Bt.IsNonsingular) (hBti : Bt.IsIrreducible)
    (hperm : (σ.datumRep D (Restriction.closed F) ℜ.α n ℜ.b ν ν.factorial (fun j => a j)
      Jt).IsPermissible Bt) :
    ∃ B : Subscheme Y, B.IsNonsingular ∧ B.IsIrreducible ∧
      (Bt.ι ≫ σ.xBar.ι).ker = Subscheme.totalTransform σ.c B ∧
      (∃ e : Bt.toScheme ≅ B.toScheme, e.hom ≫ B.ι = Bt.ι ≫ σ.xBar.ι ≫ σ.c) ∧
      D.IsPermissibleClosed (g.strictTransform F) B := by
  obtain ⟨T, n', h, hpre, -, hS, hprep⟩ := exists_standing_prepHyp_tower_closed hN hX ℜ hℜ F hF
    ν hν hνeq hνeq' hno g hP hx
  subst h
  have hpre' : T.pre n' = g := hpre
  subst hpre'
  obtain rfl : n = n' := hn.symm.trans (AB.Tower.length_pre T n')
  have := L.reg
  have hσ' : σ = (Frame.canon hS L.z L.jGen L.fr).stageOf n :=
    hσ.trans (Frame.canon_stageOf_eq_fold n).symm
  subst hσ'
  subst hD
  generalize Frame.canon hS L.z L.jGen L.fr = 𝒮 at *
  change Subscheme (𝒮.xTilde n) at Jt Bt
  have hJt' : Jt * ∏ j, ((𝒮.eTilde n j).emptyIfBot) ^ (a j) = 𝒮.jBarRep n := by
    have h1 : (∏ j : Fin (alphaT (Restriction.closed F) ℜ.α n),
        ((𝒮.eTilde n j).emptyIfBot) ^ (a j)) =
        ∏ j, ((((𝒮.stageOf n).eTilde (datum T ℜ n) (Restriction.closed F) ℜ.α n j)).emptyIfBot)
          ^ (a j) :=
      Finset.prod_congr rfl fun j _ => by rw [𝒮.eTilde_eq_stageOf]; rfl
    rw [h1]
    exact hJt.trans (𝒮.jBarRep_eq_stageOf n).symm
  have hperm' : (𝒮.datumRep n (fun j => a j) Jt).IsPermissible Bt := by
    rw [𝒮.datumRep_eq_stageOf]
    exact hperm
  have hJne := 𝒮.stalkIdeal_ne_bot_of_mul_eq_jBarRep hprep
    (fun h0 x => 𝒮.stalkIdeal_jBar_ne_bot_of_thresholdRep_eq_zero hprep h0 x) (fun j => a j) Jt
    hJt'
  exact 𝒮.exists_isPermissibleCenter_of_isPermissible_datumRep n hprep (fun j => a j) Jt hJt'
    hJne Bt hBt hBti hperm'

/-- **The relation of p. 322 and Remark 3 at the level of stages**, for the repaired datum: once the
center `B̃` of the monoidal transformation `t̃` of `X̃` has been lifted to the center `B_s` of
`X_s`, the resolvability of `t̃*(ℜ̃)` by `k` more transformations is the resolvability of the
repaired datum of the next stage `h_{s+1}`, by `k` transformations. -/
theorem exists_QRep_snoc [Hironaka.HironakaCitedResults.{u}] (hN : 1 ≤ N) (hX : IsAmbient X N) (hℜ : ℜ.IsDatum)
    (hF : ℜ.IsClosedRestriction F) (hν : 0 < ν) (hνeq : (ν : ℕ∞) = nu ℜ (.closed F))
    (hνeq' : (ν : ℕ∞) = ℜ.nu) (hno : NoCodimOneComponent (sNu ℜ (.closed F) ν))
    {Y : Scheme.{u}} (g : MonoidalSuccession X Y) (hP : PreparedClosed N ℜ F ν g)
    (hx : x₀ ∈ sNuImageClosed g ℜ F ν) {n : ℕ} (hn : g.length = n) {σ : FrameStage Y}
    (hσ : σ = L.stage g) {D : DatumII.Raw Y} (hD : D = g.transformII ℜ) (a : ℕ → ℕ)
    (Jt : Subscheme σ.xBar.toScheme)
    (hJt : Jt * ∏ j : Fin (alphaT (Restriction.closed F) ℜ.α n),
      ((σ.eTilde D (Restriction.closed F) ℜ.α n j).emptyIfBot) ^ a j =
        σ.jBarRep D (Restriction.closed F) ℜ.α n ℜ.b ν ν.factorial)
    (Bt : Subscheme σ.xBar.toScheme) (hBt : Bt.IsNonsingular) (hBti : Bt.IsIrreducible)
    (tTil : MonoidalTransformation σ.xBar.toScheme Bt) {k : ℕ}
    (hperm : (σ.datumRep D (Restriction.closed F) ℜ.α n ℜ.b ν ν.factorial (fun j => a j)
      Jt).IsPermissible Bt)
    (hrest : DatumII.Raw.ResolvableLen k
      ((σ.datumRep D (Restriction.closed F) ℜ.α n ℜ.b ν ν.factorial (fun j => a j)
        Jt).transform tTil))
    (B : Subscheme Y) (hB : B.IsNonsingular) (hBi : B.IsIrreducible)
    (hker : (Bt.ι ≫ σ.xBar.ι).ker = Subscheme.totalTransform σ.c B)
    (he : ∃ e : Bt.toScheme ≅ B.toScheme, e.hom ≫ B.ι = Bt.ι ≫ σ.xBar.ι ≫ σ.c)
    (hBperm : D.IsPermissibleClosed (g.strictTransform F) B) (t : MonoidalTransformation Y B) :
    L.QRep (g.snoc B t) k := by
  obtain ⟨T, n', h, hpre, hBheq, hmt, hT⟩ :=
    AB.Tower.exists_pre_heq_and_monoidalTransformation_heq g t
  subst h
  have hpre' : T.pre n' = g := eq_of_heq hpre
  subst hpre'
  have hB' : T.B n' = B := eq_of_heq hBheq
  subst hB'
  have hmt' : T.monoidalTransformation n' = t := eq_of_heq hmt
  subst hmt'
  obtain rfl : n = n' := hn.symm.trans (AB.Tower.length_pre T n')
  subst hD
  have hgm : (T.pre (n + 1)).IsPermissibleIIClosed ℜ F :=
    (MonoidalSuccession.isPermissibleIIClosed_snoc_iff (T.pre n) (T.B n)
      (T.monoidalTransformation n) ℜ F).mpr ⟨hP.isPermissibleIIClosed, hBperm⟩
  obtain ⟨hS, hprep⟩ := standing_prepHyp_of_tower_closed hN hX ℜ hℜ F hF ν hν hνeq hνeq' hno T n
    (n + 1) hT hgm hP hx
  have := L.reg
  obtain ⟨𝒮, h𝒮⟩ : ∃ 𝒮, 𝒮 = Frame.canon hS L.z L.jGen L.fr := ⟨_, rfl⟩
  have hσ' : σ = 𝒮.stageOf n := by
    rw [hσ, h𝒮]; exact (Frame.canon_stageOf_eq_fold n).symm
  subst hσ'
  change Subscheme (𝒮.xTilde n) at Jt Bt
  have hJt' : Jt * ∏ j, ((𝒮.eTilde n j).emptyIfBot) ^ (a j) = 𝒮.jBarRep n := by
    have h1 : (∏ j : Fin (alphaT (Restriction.closed F) ℜ.α n),
        ((𝒮.eTilde n j).emptyIfBot) ^ (a j)) =
        ∏ j, ((((𝒮.stageOf n).eTilde (datum T ℜ n) (Restriction.closed F) ℜ.α n j)).emptyIfBot)
          ^ (a j) :=
      Finset.prod_congr rfl fun j _ => by rw [𝒮.eTilde_eq_stageOf]; rfl
    rw [h1]
    exact hJt.trans (𝒮.jBarRep_eq_stageOf n).symm
  have hperm' : (𝒮.datumRep n (fun j => a j) Jt).IsPermissible Bt := by
    rw [𝒮.datumRep_eq_stageOf]
    exact hperm
  have hrest' : DatumII.Raw.ResolvableLen k
      ((𝒮.datumRep n (fun j => a j) Jt).transform tTil) := by
    rw [𝒮.datumRep_eq_stageOf]
    exact hrest
  have hJne := 𝒮.stalkIdeal_ne_bot_of_mul_eq_jBarRep hprep
    (fun h0 x => 𝒮.stalkIdeal_jBar_ne_bot_of_thresholdRep_eq_zero hprep h0 x) (fun j => a j) Jt
    hJt'
  have hBe' : ∃ e : Bt.toScheme ≅ (T.B n).toScheme, e.hom ≫ (T.B n).ι = Bt.ι ≫ 𝒮.cBar n := he
  have hBperm' : (restriction T (Restriction.closed F) n).IsPermissibleCenter (datum T ℜ n)
      (T.B n) := hBperm
  obtain ⟨-, h, anew, Jt', htr, hJt''⟩ :=
    𝒮.ker_eq_B_and_exists_transform_eq_datumRep n hprep (fun j => a j) Jt hJt' hJne Bt hBt hBti
      hperm' (T.B n) ⟨hB, hBi⟩ hBe' hBperm' rfl
  have hres1 := DatumII.Raw.resolvableLen_transform_congr tTil
    (⟨_, 𝒮.fBar n, h.1, h.2⟩ : MonoidalTransformation (𝒮.xTilde n) Bt) _ k hrest'
  have hres2 : DatumII.Raw.ResolvableLen k
      (𝒮.datumRep (n + 1) (extendA (fun j => a j) anew) Jt') := by
    rw [← htr]; exact hres1
  have hsnoc : (T.pre n).snoc (T.B n) (T.monoidalTransformation n) = T.pre (n + 1) := rfl
  rw [hsnoc]
  have hst : 𝒮.stageOf (n + 1) = L.stage (T.pre (n + 1)) := by
    rw [h𝒮]; exact Frame.canon_stageOf_eq_fold (n + 1)
  refine ⟨n + 1, 𝒮.stageOf (n + 1), datum T ℜ (n + 1), AB.Tower.length_pre T (n + 1), hst, rfl,
    extendN (alphaT (Restriction.closed F) ℜ.α n) (fun j => a j) anew, Jt', ?_, ?_⟩
  · have h1 : (∏ j : Fin (alphaT (Restriction.closed F) ℜ.α (n + 1)),
        ((((𝒮.stageOf (n + 1)).eTilde (datum T ℜ (n + 1)) (Restriction.closed F) ℜ.α (n + 1)
          j)).emptyIfBot) ^ (extendN (alphaT (Restriction.closed F) ℜ.α n) (fun j => a j)
            anew j)) =
        ∏ j, ((𝒮.eTilde (n + 1) j).emptyIfBot) ^ (extendA (fun j => a j) anew j) :=
      Finset.prod_congr rfl fun j _ => by
        rw [𝒮.eTilde_eq_stageOf, extendA_eq_extendN]; rfl
    exact (congrArg (fun P => Jt' * P) h1).trans (hJt''.trans (𝒮.jBarRep_eq_stageOf (n + 1)))
  · have h3 := 𝒮.datumRep_eq_stageOf (n + 1) (extendA (fun j => a j) anew) Jt'
    rw [h3] at hres2
    have h2 : (fun j : Fin (alphaT (Restriction.closed F) ℜ.α (n + 1)) =>
        extendN (alphaT (Restriction.closed F) ℜ.α n) (fun j => a j) anew j) =
        extendA (fun j => a j) anew :=
      funext fun j => (extendA_eq_extendN _ anew j).symm
    rw [h2]
    exact hres2

/-- One step of the induction, for the repaired datum: either the first transformation of the
resolving succession of `X̃` has empty center (and is dropped), or it is lifted to the center `B_s`
of `X_s` and the resolvability of the next stage is read off the relation of `ℜ(s+1)` with
`f̄_s*(ℜ̃)` (Remarks 1--3, pp. 321--326). -/
theorem stepRep [Hironaka.HironakaCitedResults.{u}] (hN : 1 ≤ N) (hX : IsAmbient X N) (hℜ : ℜ.IsDatum)
    (hF : ℜ.IsClosedRestriction F) (hν : 0 < ν) (hνeq : (ν : ℕ∞) = nu ℜ (.closed F))
    (hνeq' : (ν : ℕ∞) = ℜ.nu) (hno : NoCodimOneComponent (sNu ℜ (.closed F) ν))
    {Y : Scheme.{u}} (g : MonoidalSuccession X Y) (hP : PreparedClosed N ℜ F ν g)
    (hx : x₀ ∈ sNuImageClosed g ℜ F ν) (k : ℕ) (hQ : L.QRep g (k + 1)) :
    L.QRep g k ∨ ∃ (B : Subscheme Y) (t : MonoidalTransformation Y B),
      (g.transformII ℜ).IsPermissibleClosed (g.strictTransform F) B ∧ L.QRep (g.snoc B t) k := by
  obtain ⟨n, σ, D, hn, hσ, hD, a, Jt, hJt, Bt, tTil, hperm, hrest⟩ := hQ
  rcases hperm.1 with hBt | ⟨hBt, hBti⟩
  · subst hBt
    left
    exact ⟨n, σ, D, hn, hσ, hD, a, Jt, hJt,
      DatumII.Raw.resolvableLen_of_transform_of_center_empty tTil _ k hrest⟩
  · right
    obtain ⟨B, hB, hBi, hker, he, hBperm⟩ := L.exists_center_closed hN hX hℜ hF hν hνeq hνeq' hno
      g hP hx hn hσ hD a Jt hJt Bt hBt hBti hperm
    obtain ⟨t, -⟩ := MonoidalTransformation.exists_isProper Y B
    exact ⟨B, t, hD ▸ hBperm, L.exists_QRep_snoc hN hX hℜ hF hν hνeq hνeq' hno g hP hx hn hσ hD a
      Jt hJt Bt hBt hBti tTil hperm hrest B hB hBi hker he hBperm t⟩

end LiftData

/-- **The core step for Theorem C** (pp. 320-326), closed case: for a finite permissible
succession `g` of `X` for `(ℜ, F)` satisfying `[(1)]` and a point `x_0` of `h_s(S_ν(ℜ(s)))`,
`g` can be extended by a permissible succession `e` such that `x_0` leaves `h(S_ν(ℜ(s)))`.
(There is no `[(2)]` in the closed case.)

\textbf{Deviation from the paper (proof corrected, repair of the paper's error on the subschemes $\tilde E_j$, items 2 and
3: emptying and the shifted threshold).} The paper (p. 321): "We see that, in both cases, `Ẽ_j`
`(1 ≤ j ≤ α̃)` are non-singular irreducible subschemes of `X̃` of codimension 1, and `Ẽ_1 ∪ ⋯ ∪
Ẽ_α̃` has only normal crossings on `X̃`", and then (p. 322) for `ν < b`: "`J*(s) = (J̄(s)^{b-ν},
(∏ P_j^{c_j})^{b̄})` … `b̃ = b̄(b - ν)`" (p. 323), with `J̄(s)` resp. `J*(s) = J̃ ∏ P̃_j^{ã_j}`.
This is false: the `Ẽ_j` can be reducible, and `Ẽ_i = X̃` when
`F = E_i` (closed case), where the second generator of `J*(s)` vanishes and Remark 2 (p. 323)
fails.  Lean runs the induction with the datum `datumRep` of `AuxiliaryDatumRepair`: the entries
equal to `X̃` emptied (a weak datum, resolvable by `resolvable_of_isWeakDatum`), and the threshold
`b - ν` shifted by their weight `δ_s`.  The non-vanishing of the stalks of `J̄(s)` is
`Frame.stalkIdeal_jBar_ne_bot_of_thresholdRep_eq_zero`.  Everything else is the paper's: the
lifting of a resolving succession of `X̃` (Theorem `II₂^{N-1}`) one transformation at a time
(Remarks 1-3), the frame of §4 being rebuilt at every stage (`FrameStage.fold`, `Frame.canon`). -/
@[blueprint "lem:IV.4-core-step-closed"
  (statement := /-- Let $X$ be a non-singular irreducible algebraic scheme of dimension $N\ge1$ and
    $\mathfrak R=(\mathfrak R^N_{\mathrm{II}},F)$ a resolution datum on $X$ with closed restriction
    $F$ and $\nu=\nu(\mathfrak R)=\nu(\mathfrak R^N_{\mathrm{II}})>0$ such that
    $S_\nu(\mathfrak R)$ has no non-empty component of codimension $1$. Suppose Theorems
    $\mathrm{II}_2^{N''}$, $N''<N$, were verified. Let $h_s$ be a permissible succession of
    monoidal transformations of $X$ for $\mathfrak R$ satisfying [(1)] $h_s(S_\nu(\mathfrak
    R(s)))$ is a finite set of points at which $X$ has dimension $N$ (\cref{def:IV.4-conditions}),
    and let $x_0\in h_s(S_\nu(\mathfrak R(s)))$. Then $h_s$ can be extended by a permissible
    succession such that $x_0\notin h_{s'}(S_\nu(\mathfrak R(s')))$. (The core of the proof of
    Theorem~C, pp.~314--326.) -/)
  (proof := /-- With reference to $x_0$ construct $\hat X_t$, $c_t$, $\bar X_t$, $\bar J(t)$ and
    $\tilde X=\bar X_s$ (\cref{def:IV.4-frame}, \cref{def:IV.4-construction},
    \cref{def:IV.4-tilde}), and the repaired datum $\tilde{\mathfrak R}^e$ on $\tilde X$
    (\cref{def:IV.4-case-lt-repaired}). By Theorem $\mathrm{II}_2^{N-1}$ applied to this weak datum
    (\cref{lem:IV.4-tilde-resolvable-repaired}) there is a permissible succession of monoidal
    transformations of $\tilde X$ resolving it. Lift it one transformation at a time: by
    Remarks~1 and~2 (\cref{rem:IV.4-1-repaired}) the center $\tilde B$ comes from a center $B_s$
    of $X_s$ permissible for $\mathfrak R(s)$; extending $h_s$ by $f_s$ with center $B_s$, the
    relation between $\mathfrak R(s+1)$ and $\bar f_s^*(\tilde{\mathfrak R}^e)$ is the same as
    between $\mathfrak R(s)$ and $\tilde{\mathfrak R}^e$
    (\cref{lem:IV.4-case-ge-relation-repaired}, \cref{rem:IV.4-3-repaired}). When $\tilde{\mathfrak
    R}^e$ is resolved, $S(\tilde{\mathfrak R}^e)$ is empty, whereas it is non-empty if $x_0\in
    h_{s'}(S_\nu(\mathfrak R(s')))$ (\cref{rem:IV.4-2-repaired}).

    \textbf{Deviation from the paper (proof corrected, repair of the paper's error on the subschemes $\tilde E_j$, items 2 and
    3: emptying and the shifted threshold).} The paper (p.~321) asserts that the $\tilde E_j$ are
    non-singular irreducible subschemes of $\tilde X$ of codimension $1$, and (pp.~322--323)
    puts $\bar J^*(s)=(\bar J(s)^{b-\nu},(\prod\tilde P_j^{c_j})^{\bar b})$ and $\tilde b=\bar
    b(b-\nu)$ for $\nu<b$. Both are false in the closed case with $F=E_i$: the entries $\tilde E_i=\tilde X$ are emptied and their weight is subtracted from
    $b-\nu$ (\cref{def:IV.4-case-lt-repaired}). The non-vanishing of the stalks of $\bar J(s)$
    (Definition~3 (II)) is \cref{lem:IV.4-jbar-nonzero}, whose hypothesis is satisfied by the
    shifted threshold. -/)
  (proofUses := ["def:IV.4-conditions", "lem:IV.4-x0", "def:IV.4-frame", "def:IV.4-construction",
    "def:IV.4-tilde", "def:IV.4-case-lt-repaired", "rem:IV.4-1-repaired", "rem:IV.4-2-repaired",
    "rem:IV.4-3-repaired", "lem:IV.4-case-ge-relation-repaired", "lem:IV.4-jbar-nonzero",
    "lem:IV.4-tilde-resolvable-repaired", "thm:I.2-II2"])
  (latexEnv := "lemma")]
theorem exists_extension_not_mem_sNuImageClosed [Hironaka.HironakaCitedResults.{u}] (hN : 1 ≤ N)
    (hII₂ : ∀ N'' : ℕ, N'' < N → FundamentalTheorem.II₂.{u} N'')
    (hX : IsAmbient X N) (ℜ : DatumII.Raw X) (hℜ : ℜ.IsDatum)
    (F : Subscheme X) (hF : ℜ.IsClosedRestriction F) (ν : ℕ) (hν : 0 < ν)
    (hνeq : (ν : ℕ∞) = nu ℜ (.closed F)) (hνeq' : (ν : ℕ∞) = ℜ.nu)
    (hno : NoCodimOneComponent (sNu ℜ (.closed F) ν)) {Y : Scheme.{u}}
    (g : MonoidalSuccession X Y) (hP : PreparedClosed N ℜ F ν g) {x₀ : X}
    (hx₀ : x₀ ∈ sNuImageClosed g ℜ F ν) :
    ∃ (Z : Scheme.{u}) (e : MonoidalSuccession Y Z),
      e.IsPermissibleIIClosed (g.transformII ℜ) (g.strictTransform F) ∧
      x₀ ∉ sNuImageClosed (g.append e) ℜ F ν := by
  -- the tower-independent data of the frame, and the initial resolvability
  obtain ⟨T, n, h, hpre, -, hS, hprep⟩ := exists_standing_prepHyp_tower_closed hN hX ℜ hℜ F hF ν
    hν hνeq hνeq' hno g hP hx₀
  obtain ⟨𝒮₀⟩ := hS.nonempty_frame
  let L : LiftData N ℜ (Restriction.closed F) ν x₀ :=
    { reg := 𝒮₀.regShat, hx := hX.2.1 x₀, z := 𝒮₀.z, jGen := 𝒮₀.jGen, fr := 𝒮₀.frame }
  have hQ : ∃ k, L.QRep g k := by
    subst h
    have hpre' : T.pre n = g := hpre
    subst hpre'
    have := L.reg
    have hglue : ∀ Z : Scheme.{u}, IsAmbient Z (N - 1) → ∀ D : DatumII.Raw Z, D.IsWeakDatum →
        D.Resolvable := fun Z hZ D hD =>
      DatumII.Raw.resolvable_of_isWeakDatum (hII₂ (N - 1) (by omega)) hZ hD
    obtain ⟨k, hk⟩ := (DatumII.Raw.resolvable_iff_exists_resolvableLen _).mp
      ((Frame.canon hS L.z L.jGen L.fr).resolvable_datumRep_zero hprep
        (fun h0 x => (Frame.canon hS L.z L.jGen L.fr).stalkIdeal_jBar_ne_bot_of_thresholdRep_eq_zero
          hprep h0 x) hglue)
    refine ⟨k, n, (Frame.canon hS L.z L.jGen L.fr).stageOf n, datum T ℜ n,
      AB.Tower.length_pre T n, Frame.canon_stageOf_eq_fold n, rfl, fun _ => 0,
      (Frame.canon hS L.z L.jGen L.fr).jBarRep n, ?_, ?_⟩
    · simp only [pow_zero, Finset.prod_const_one]
      exact (mul_one _).trans ((Frame.canon hS L.z L.jGen L.fr).jBarRep_eq_stageOf n)
    · have h3 := (Frame.canon hS L.z L.jGen L.fr).datumRep_eq_stageOf n (fun j => 0)
        ((Frame.canon hS L.z L.jGen L.fr).jBarRep n)
      rw [h3] at hk
      exact hk
  obtain ⟨k, hk⟩ := hQ
  exact exists_extension_of_resolvableLen_closed hX hℜ (fun {Y} g k => L.QRep g k)
    (fun g hP hx => L.not_QRep_zero hN hX hℜ hF hν hνeq hνeq' hno g hP hx)
    (fun g k hP hx hQ => L.stepRep hN hX hℜ hF hν hνeq hνeq' hno g hP hx k hQ) k g hP hx₀ hk

end ClosedLifting

section ClosedCore

variable {N : ℕ} {X : Scheme.{u}}

/-- p. 326, closed case: after finitely many applications of the core step, `h_s(S_ν(ℜ(s)))` is
empty, hence so is `S_ν(ℜ(s))` (induction on the number of points of the finite set
`h_s(S_ν(ℜ(s)))`, each step removing the point `x_0`, no new point being created by further
permissible transformations). -/
theorem exists_isPermissibleIIClosed_sNu_eq_empty_of_sNuImageClosed_finite [Hironaka.HironakaCitedResults.{u}] (hN : 1 ≤ N)
    (hII₂ : ∀ N'' : ℕ, N'' < N → FundamentalTheorem.II₂.{u} N'')
    (hX : IsAmbient X N) (ℜ : DatumII.Raw X) (hℜ : ℜ.IsDatum)
    (F : Subscheme X) (hF : ℜ.IsClosedRestriction F) (ν : ℕ) (hν : 0 < ν)
    (hνeq : (ν : ℕ∞) = nu ℜ (.closed F)) (hνeq' : (ν : ℕ∞) = ℜ.nu)
    (hno : NoCodimOneComponent (sNu ℜ (.closed F) ν)) {Y₀ : Scheme.{u}}
    (g₀ : MonoidalSuccession X Y₀) (hP₀ : PreparedClosed N ℜ F ν g₀) :
    ∃ (Y : Scheme.{u}) (g : MonoidalSuccession X Y), g.IsPermissibleIIClosed ℜ F ∧
      sNu (g.transformII ℜ) (.closed (g.strictTransform F)) ν = ∅ := by
  classical
  have key : ∀ n : ℕ, ∀ (Y : Scheme.{u}) (g : MonoidalSuccession X Y),
      PreparedClosed N ℜ F ν g → (sNuImageClosed g ℜ F ν).ncard ≤ n →
      ∃ (Y' : Scheme.{u}) (g' : MonoidalSuccession X Y'), g'.IsPermissibleIIClosed ℜ F ∧
        sNu (g'.transformII ℜ) (.closed (g'.strictTransform F)) ν = ∅ := by
    intro n
    induction n with
    | zero =>
      intro Y g hP hn
      refine ⟨Y, g, hP.isPermissibleIIClosed, Set.eq_empty_iff_forall_notMem.mpr fun y hy => ?_⟩
      have h0 : sNuImageClosed g ℜ F ν = ∅ :=
        (Set.ncard_eq_zero hP.finite).mp (Nat.le_zero.mp hn)
      exact (Set.eq_empty_iff_forall_notMem.mp h0) _ ⟨y, hy, rfl⟩
    | succ n ih =>
      intro Y g hP hn
      by_cases hZ : sNuImageClosed g ℜ F ν = ∅
      · refine ⟨Y, g, hP.isPermissibleIIClosed, Set.eq_empty_iff_forall_notMem.mpr fun y hy => ?_⟩
        exact (Set.eq_empty_iff_forall_notMem.mp hZ) _ ⟨y, hy, rfl⟩
      obtain ⟨x₀, hx₀⟩ := Set.nonempty_iff_ne_empty.mpr hZ
      obtain ⟨Z, e, he, hx₀'⟩ := exists_extension_not_mem_sNuImageClosed hN hII₂ hX ℜ hℜ F hF ν hν
        hνeq hνeq' hno g hP hx₀
      have hsub' : sNuImageClosed (g.append e) ℜ F ν ⊆ sNuImageClosed g ℜ F ν :=
        sNuImageClosed_append_subset hX ℜ hℜ F g hP.isPermissibleIIClosed e he ν
      refine ih Z (g.append e) (hP.append hX hℜ e he) ?_
      have hlt : sNuImageClosed (g.append e) ℜ F ν ⊂ sNuImageClosed g ℜ F ν :=
        ⟨hsub', fun h => hx₀' (h hx₀)⟩
      have := Set.ncard_lt_ncard hlt hP.finite
      omega
  exact key _ Y₀ g₀ hP₀ le_rfl

/-- p. 326 and the localization, closed case: if `S_ν(ℜ) ∩ F` has no non-empty component of
codimension one, there is a permissible succession for `(ℜ, F)` with `S_ν(f*(ℜ)) = ∅`. -/
theorem exists_isPermissibleIIClosed_sNu_eq_empty_of_noCodimOneComponent [Hironaka.HironakaCitedResults.{u}] (hN : 1 ≤ N)
    (hII₁ : ∀ N' : ℕ, N' < N → FundamentalTheorem.II₁.{u} N')
    (hII₂ : ∀ N'' : ℕ, N'' < N → FundamentalTheorem.II₂.{u} N'')
    (hI₂ : ∀ n : ℕ, n < N → FundamentalTheorem.I₂.{u} N n)
    (hX : IsAmbient X N) (ℜ : DatumII.Raw X) (hℜ : ℜ.IsDatum)
    (F : Subscheme X) (hF : ℜ.IsClosedRestriction F) (ν : ℕ) (hν : 0 < ν)
    (hνeq : (ν : ℕ∞) = nu ℜ (.closed F)) (hνeq' : (ν : ℕ∞) = ℜ.nu)
    (hno : NoCodimOneComponent (sNu ℜ (.closed F) ν)) :
    ∃ (Y : Scheme.{u}) (g : MonoidalSuccession X Y), g.IsPermissibleIIClosed ℜ F ∧
      sNu (g.transformII ℜ) (.closed (g.strictTransform F)) ν = ∅ := by
  have hνpos : 0 < ℜ.nu := by rw [← hνeq']; exact_mod_cast hν
  obtain ⟨Y₁, g₁, hg₁, hfin₁, hdim₁⟩ := exists_isPermissibleIIClosed_finite_image_Snu_dimAt_eq N
    hN hII₁ hI₂ X hX ⟨ℜ, hℜ⟩ F hF hνpos
  rw [← hνeq'] at hfin₁ hdim₁
  exact exists_isPermissibleIIClosed_sNu_eq_empty_of_sNuImageClosed_finite hN hII₂ hX ℜ hℜ F hF
    ν hν hνeq hνeq' hno g₁ ⟨hg₁, hfin₁, hdim₁⟩

end ClosedCore

end CD

open CD in
/-- **Theorem C** (p. 311).  The hypotheses are read off the printed text: "Suppose Theorems `II₁^{N'}`
with `N' < N`, Theorems `I₂^{N',n'}` with `n' < N' ≦ N`, and Theorems `II₂^{N'}` with `N' < N`
were verified.  Then, assuming that `ν = ν(ℜ) = ν(ℜ^N_II) > 0`, …".  The
conclusion `S_ν(f*(ℜ)) = ∅` is `S_ν(f*(ℜ^N_II)) ∩ F' = ∅` (p. 311), `F'` the strict transform.

\textbf{Deviation from the paper (gap filled).} (i) "A comparatively trivial observation shows that
we may also assume the same for Theorem C" (p. 314: `S_ν(ℜ)` has no non-empty component of
codimension one) is proved: `CD.exists_isPermissibleIIClosed_noCodimOneComponent_Snu` (the
Localization Theorem, Proposition 3 of §1, with Lemma (D.2) applied to `ℜ^N_II`, as `S_ν(f*ℜ) ⊆
S_ν(f*ℜ^N_II)`; for `N = 1` the closed points of `S_ν ∩ F` are blown up one at a time) and
`CD.noCodimOneComponent_transform_closed` ("continues to hold by any permissible monoidal
transformation").  (ii) The finitely many points of `h_s(S_ν(ℜ(s)))` are treated one at a time
(`CD.exists_isPermissibleIIClosed_sNu_eq_empty_of_sNuImageClosed_finite`), the paper's "since
`h_s(S_ν(ℜ(s)))` is finite" (p. 326).  (iii) The hypothesis `ν(ℜ) = ν(ℜ^N_II)` of the statement
is not used: the equalities needed after the localization are obtained by cases (if
`ν(f*ℜ) < ν` then `S_ν(f*ℜ) = ∅`).
(iv) The core step of pp. 320-326 for the closed case, `CD.exists_extension_not_mem_sNuImageClosed`,
is proved with the repaired auxiliary datum (the repair of the paper's error on the subschemes `Ẽ_j`; proof
corrected: the entries `Ẽ_j = X̃` emptied, the threshold `b - ν` shifted by their weight). -/
@[blueprint "thm:IV.C"
  (statement := /-- \textbf{Theorem C.} Let $X$ be a non-singular irreducible algebraic scheme
    of dimension $N\ge1$ and $\mathfrak R=(\mathfrak R^N_{\mathrm{II}},F)$ a resolution datum on
    $X$ with closed restriction $F$ (\cref{def:I.3-II}, \cref{def:I.5-II.1}). Suppose Theorems
    $\mathrm{II}_1^{N'}$ with $N'<N$, Theorems $\mathrm I_2^{N',n'}$ with $n'<N'\le N$, and
    Theorems $\mathrm{II}_2^{N'}$ with $N'<N$ were verified (\cref{thm:I.2-II1},
    \cref{thm:I.2-I2}, \cref{thm:I.2-II2}). Then, assuming that
    $\nu=\nu(\mathfrak R)=\nu(\mathfrak R^N_{\mathrm{II}})>0$ (\cref{def:IV.4-symbols}), there
    exists a permissible succession of monoidal transformations $f\colon X'\to X$ for
    $\mathfrak R$ (\cref{def:I.8}), such that $S_\nu(f^*(\mathfrak R))$ is empty. (p.~311.) -/)
  (proof := /-- (pp.~314--326.) As for Theorem D* (\cref{lem:IV.4-no-codim-one}), ``a
    comparatively trivial observation shows that we may also assume'' that $S_\nu(\mathfrak R)$
    has no non-empty component of codimension $1$ in $X$ (p.~314). By the localization theorem
    (\cref{prop:IV.1-3}, whose hypotheses $\mathrm{II}_1^{N'}$, $N'<N$, and
    $\mathrm I_2^{N,n}$, $n<N$, are among ours) we find a permissible succession $h_s=\{f_t\colon
    X_{t+1}\to X_t\}$ $(0\le t\le s-1)$ such that
    [(1)] $h_s(S_\nu(\mathfrak R(s)))$ consists of a finite number of points at which $X$ has
    dimension $N$ (\cref{def:IV.4-conditions}). Let $x_0$ be any point of $X$ in
    $h_s(S_\nu(\mathfrak R(s)))$; then $x_0\in S_\nu(\mathfrak R)$ (\cref{lem:IV.4-x0}). With
    reference to $x_0$ construct $\hat X_t$, $c_t$, $\bar X_t$, $\bar J(t)$ and $\bar b=\nu!$
    (\cref{def:IV.4-frame}, \cref{def:IV.4-construction}, \cref{lem:IV.4-setup-exists}), and on
    the non-singular irreducible $\tilde X=\bar X_s$ of dimension $N-1$ the subschemes
    $\tilde E_j=\hat E_j(s)\cap\tilde X$, $1\le j\le\tilde\alpha=\alpha+s$
    (\cref{def:IV.4-tilde}, \cref{lem:IV.4-tilde-facts}). \emph{The case $\nu\ge b$.} Take any
    datum $\mathfrak R^{N-1}_{\mathrm{II}}=(\tilde E_1,\dots,\tilde E_{\tilde\alpha}\,|\,
    \tilde J,\bar b\,|\,\tilde a_1,\dots,\tilde a_{\tilde\alpha})$ with
    $\bar J(s)=\tilde J\prod\tilde P_j^{\tilde a_j}$ (\cref{def:IV.4-case-ge}). By Remark~1
    (\cref{rem:IV.4-1}) every monoidal transformation of $\tilde X$ permissible for
    $\mathfrak R^{N-1}_{\mathrm{II}}$ with center $\tilde B$ comes from a monoidal
    transformation $f_s$ of $X_s$ with center $B\simeq\tilde B$ permissible for
    $\mathfrak R(s)$; extending $h_s$ by $f_s$, the relation between $\mathfrak R(s+1)$ and
    $\bar f_s^*(\mathfrak R^{N-1}_{\mathrm{II}})$ is the same as that between $\mathfrak R(s)$
    and $\mathfrak R^{N-1}_{\mathrm{II}}$ (\cref{lem:IV.4-case-ge-relation}). Thus the proof is
    reduced to the resolution of $\mathfrak R^{N-1}_{\mathrm{II}}$ on $\tilde X$, which is done
    by Theorem $\mathrm{II}_2^{N-1}$ (\cref{thm:I.2-II2}); when $\mathfrak R^{N-1}_{\mathrm{II}}$
    is resolved, the Corollary of Lemma (CD.4) (\cref{cor:IV.CD-4}) shows that
    $S(\mathfrak R(s))\cap h_s^{-1}(x_0)$ [sic; the Corollary gives this for
    $S_\nu(\mathfrak R(s))$] is empty. \emph{The case $\nu<b$.} Replace $\bar J(s)$ by
    $\bar J^*(s)=(\bar J(s)^{b-\nu},(\prod_j\tilde P_j^{c_j})^{\bar b})$ and $\bar b$ by
    $\bar b(b-\nu)$ (\cref{def:IV.4-case-lt}); by Remarks~2 and~3 (\cref{rem:IV.4-2},
    \cref{rem:IV.4-3}) the proof is again reduced to the resolution of the datum
    $\mathfrak R^{N-1}_{\mathrm{II}}$ on $\tilde X$, done by Theorem $\mathrm{II}_2^{N-1}$. In
    both cases $S_\nu(\mathfrak R(s'))\cap h_{s'}^{-1}(x_0)$ becomes empty; since
    $h_s(S_\nu(\mathfrak R(s)))$ is finite, repeating this for its finitely many points proves
    Theorem C. (Theorems $\mathrm{II}_1^{N'}$, $N'<N$, and $\mathrm I_2^{N,n}$, $n<N$, enter
    through the localization theorem \cref{prop:IV.1-3}, and Theorem $\mathrm{II}_2^{N-1}$
    through the resolution of $\mathfrak R^{N-1}_{\mathrm{II}}$.)

    \textbf{Paper misprint.} On p.~322 the paper reads ``(By Corollary of Lemma (CD.4), if
    $\mathfrak R^{N-1}_{\mathrm{II}}$ is resolved then $S(\mathfrak R(s))\cap h_s^{-1}(x_0)$ is
    empty.)''; meant is $S_\nu(\mathfrak R(s))\cap h_s^{-1}(x_0)$, the Corollary of Lemma (CD.4)
    being about $S_\nu$.

    \textbf{Deviation from the paper (gap filled).} The sentence ``a comparatively trivial
    observation shows that we may also assume the same for Theorem C'' (p.~314) is proved
    (Localization Theorem with closed restriction, \cref{prop:IV.1-3}, and Lemma (D.2),
    \cref{lem:IV.D-2}, applied to $\mathfrak R^N_{\mathrm{II}}$ since $S_\nu(f^*\mathfrak R)
    \subseteq S_\nu(f^*\mathfrak R^N_{\mathrm{II}})$; for $N=1$ the closed points of $S_\nu\cap F$
    are blown up one at a time). Lean treats the finitely many points of
    $h_s(S_\nu(\mathfrak R(s)))$ one at a time, no new point being created
    ($f(S_\nu(f^*\mathfrak R))\subseteq S_\nu(\mathfrak R)$). The core step (pp.~320--326) for the
    closed restriction is \cref{lem:IV.4-core-step-closed}, proved with the repaired auxiliary
    datum (proof corrected: the entries $\tilde E_i=\tilde X$ emptied and the threshold $b-\nu$
    shifted by their weight). -/)
  (proofUses := ["lem:IV.4-no-codim-one-closed", "prop:IV.1-3", "def:IV.4-conditions",
    "lem:IV.4-core-step-closed", "thm:I.2-II2"])
  (latexEnv := "theorem")]
theorem exists_isPermissibleIIClosed_Snu_eq_empty_of_nu_closed_eq [Hironaka.HironakaCitedResults.{u}] (N : ℕ) (hN : 1 ≤ N)
    (hII₁ : ∀ N' : ℕ, N' < N → FundamentalTheorem.II₁.{u} N')
    (hI₂ : ∀ N' n' : ℕ, n' < N' → N' ≤ N → FundamentalTheorem.I₂.{u} N' n')
    (hII₂ : ∀ N' : ℕ, N' < N → FundamentalTheorem.II₂.{u} N')
    (X : Scheme.{u}) (hX : IsAmbient X N) (ℜ : DatumII X) (F : Subscheme X)
    (hF : (ℜ : DatumII.Raw X).IsClosedRestriction F)
    (_hνeq : nu (ℜ : DatumII.Raw X) (.closed F) = (ℜ : DatumII.Raw X).nu)
    (hν : 0 < (ℜ : DatumII.Raw X).nu) :
    ∃ (X' : Scheme.{u}) (f : MonoidalSuccession X X'),
      f.IsPermissibleIIClosed ℜ F ∧
      sNu (f.transformII ℜ) (.closed (f.strictTransform F)) (ℜ : DatumII.Raw X).nu = ∅ := by
  classical
  have := hX.1
  obtain ⟨X₀, f₀, hf₀, hno⟩ := exists_isPermissibleIIClosed_noCodimOneComponent_Snu N hN hII₁
    (fun n hn => hI₂ N n hn le_rfl) X hX ℜ F hF hν
  obtain ⟨hX₀, hd₀⟩ := f₀.isAmbient_transformII hX ℜ.1 ℜ.2 hf₀.isPermissibleII
  have hF₀ := f₀.isClosedRestriction_transformII hX ℜ.1 ℜ.2 F hF hf₀
  have hν₀ : (f₀.transformII ℜ.1).nu ≤ ℜ.1.nu :=
    MonoidalSuccession.nu_transformII_le f₀ hX.2.1 ℜ.1 ℜ.2 hf₀.isPermissibleII
  have hfin : ℜ.1.nu ≠ ⊤ := DatumII.Raw.nu_ne_top hX.2.1 ℜ.1 ℜ.2.2.2.2
  have hn : ((ℜ.1.nu.toNat : ℕ) : ℕ∞) = ℜ.1.nu := ENat.natCast_toNat hfin
  have hnpos : 0 < ℜ.1.nu.toNat := by
    have : (0 : ℕ∞) < (ℜ.1.nu.toNat : ℕ∞) := by rw [hn]; exact hν
    exact_mod_cast this
  by_cases hlt : (f₀.transformII ℜ.1).nu < ℜ.1.nu
  · refine ⟨X₀, f₀, hf₀, ?_⟩
    show (f₀.transformII ℜ.1).sNu ℜ.1.nu ∩ _ = ∅
    rw [DatumII.Raw.sNu_eq_empty_of_nu_lt hlt, Set.empty_inter]
  have heq : (f₀.transformII ℜ.1).nu = ℜ.1.nu := le_antisymm hν₀ (not_lt.mp hlt)
  by_cases hlt2 : nu (f₀.transformII ℜ.1) (.closed (f₀.strictTransform F)) < ℜ.1.nu
  · refine ⟨X₀, f₀, hf₀, Set.eq_empty_iff_forall_notMem.mpr fun y hy => ?_⟩
    obtain ⟨hyS, hyν⟩ := (mem_Snu_iff _ _ _ _).1 hy
    exact absurd (hyν.trans (nuAt_le_nu _ _ hyS)) (not_le.mpr hlt2)
  have hνeq₀ : nu (f₀.transformII ℜ.1) (.closed (f₀.strictTransform F)) = ℜ.1.nu :=
    le_antisymm ((nu_le _ _).trans hν₀) (not_lt.mp hlt2)
  obtain ⟨Y, g', hg', hS⟩ := exists_isPermissibleIIClosed_sNu_eq_empty_of_noCodimOneComponent hN
    hII₁ hII₂ (fun n hn' => hI₂ N n hn' le_rfl) hX₀ (f₀.transformII ℜ.1) hd₀
    (f₀.strictTransform F) hF₀ ℜ.1.nu.toNat hnpos (by rw [hn, hνeq₀]) (by rw [hn, heq])
    (by rw [hn]; exact hno)
  refine ⟨Y, f₀.append g', (MonoidalSuccession.isPermissibleIIClosed_append f₀ g' ℜ.1 F).mpr
    ⟨hf₀, hg'⟩, ?_⟩
  rw [MonoidalSuccession.transformII_append, MonoidalSuccession.strictTransform_append, ← hn]
  exact hS

open CD in
/-- The implication (C) of Ch. I §2 (p. 172) follows from Theorem C.  Theorem C assumes
`ν(ℜ) = ν(ℜ^N_II)`; when `ν(ℜ) < ν(ℜ^N_II)` the empty succession already has
`S_ν(ℜ^N_II) ∩ F = ∅`, since every point of `S(ℜ^N_II) ∩ F` has `ν(J_x) ≤ ν(ℜ)`.

Gap in the paper filled: the paper does not treat the case `ν(ℜ) < ν(ℜ^N_II)` when it derives
(C) from Theorem C. -/
@[blueprint "impl:C"
  (statement := /-- \textbf{The implication (C).} Given $N\ge1$:
    Th.\ $\mathrm{II}_1^{N'}$ for $N'<N$, Th.\ $\mathrm I_2^{N^*,n^*}$ for $n^*<N^*\le N$, and
    Th.\ $\mathrm{II}_2^{N'}$ for $N'<N$ together imply Th.\ $\mathrm{II}_1^{N}$. (Lean:
    \cref{def:I.2-implication-C}.) The proof is in Ch.~IV: Theorem~C (\cref{thm:IV.C}, p.~311;
    ``We shall prove the following Theorems C and D, which complete the inductive proof of all
    the theorems stated in Ch.~I'', p.~311). -/)
  (proof := /-- Theorem C (\cref{thm:IV.C}) has exactly these hypotheses. Let
    $(\mathfrak R^N_{\mathrm{II}},F)$ be given with $\nu=\nu(\mathfrak R^N_{\mathrm{II}})>0$. We
    always have $\nu(\mathfrak R)\le\nu(\mathfrak R^N_{\mathrm{II}})$ since
    $S(\mathfrak R)=S(\mathfrak R^N_{\mathrm{II}})\cap F$ (\cref{def:IV.4-symbols}). If
    $\nu(\mathfrak R)=\nu(\mathfrak R^N_{\mathrm{II}})$, Theorem C gives a permissible succession
    $f$ with $S_\nu(f^*(\mathfrak R^N_{\mathrm{II}}))\cap F'=\emptyset$, the conclusion of
    Theorem $\mathrm{II}_1^N$ (\cref{thm:I.2-II1}). Otherwise $\nu(\mathfrak R)<\nu$, and the
    empty succession works: a point $x$ of $F\cap S_\nu(\mathfrak R^N_{\mathrm{II}})$ would lie
    in $S(\mathfrak R)$ with $\nu\le\nu(J_x)\le\nu(\mathfrak R)$.

    \textbf{Gap in the paper filled.} Theorem C assumes $\nu(\mathfrak R)=
    \nu(\mathfrak R^N_{\mathrm{II}})$, whereas Theorem $\mathrm{II}_1^N$ assumes only
    $\nu(\mathfrak R^N_{\mathrm{II}})>0$; the paper, which says that Theorems C and D ``complete
    the inductive proof'' (pp.~311, 326), does not treat the case $\nu(\mathfrak R)<
    \nu(\mathfrak R^N_{\mathrm{II}})$, settled here by the empty succession. -/)
  (latexEnv := "corollary")]
theorem implicationC_fundamentalFamily [Hironaka.HironakaCitedResults.{u}] : fundamentalFamily.{u}.ImplicationC := by
  intro N hN hII₁ hI₂ hII₂ X hX ℜ F hF hν
  by_cases hν' : nu (ℜ : DatumII.Raw X) (.closed F) = (ℜ : DatumII.Raw X).nu
  · obtain ⟨X', f, hf, hS⟩ := exists_isPermissibleIIClosed_Snu_eq_empty_of_nu_closed_eq N hN hII₁
      hI₂ hII₂ X hX ℜ F hF hν' hν
    refine ⟨X', f, hf, ?_⟩
    rw [Set.inter_comm]
    exact hS
  · refine ⟨X, .nil X, trivial, ?_⟩
    show F.pts ∩ (ℜ : DatumII.Raw X).sNu (ℜ : DatumII.Raw X).nu = ∅
    refine Set.eq_empty_of_forall_notMem fun x ⟨hxF, hxS, hxν⟩ => hν' ?_
    refine le_antisymm (nu_le _ _) ?_
    exact hxν.trans (nuAt_le_nu (ℜ : DatumII.Raw X) (.closed F) ⟨hxS, hxF⟩)

end

end Hironaka

/-- Paper name (Hironaka 1964) of `exists_isPermissibleIIClosed_Snu_eq_empty_of_nu_closed_eq`. -/
alias _root_.Hironaka.theoremC := Hironaka.exists_isPermissibleIIClosed_Snu_eq_empty_of_nu_closed_eq
