/-
Copyright (c) 2026 Daattavya Aggarwal, Minhyong Kim, Oisin Kim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daattavya Aggarwal, Minhyong Kim, Oisin Kim
-/
module

public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Hironaka.Compat.WeierstrassFrameStep
public import Hironaka.Compat.TauZBaseChange
public import Hironaka.Compat.WeierstrassDatumBaseChange
public import Hironaka.Compat.NormalizedStrictTransform
public import Hironaka.Compat.StageStability
public import Hironaka.Statements

/-!
# Lemma 25 (pp. 269--272): the induction along a sequence

"One can easily see that, if we prove these facts, then the proof of the lemma is completed"
(p. 271).  This file carries out that induction.

* `WeierstrassDatum.map`, `hasShape_map`, `inTauStar_map`: the datum of the reformulation carried
  along a ring isomorphism (`RegularFrame.expCoeff_transport`);
* `WeierstrassStageInv`: the invariant of the induction along a sequence `{(R_α, P_{α-1})}`: at the
  stage `β` a datum on `R_β` whose frame consists of strict transforms of the `z_j`, with `w^{(β)}`
  a strict transform of `w` and `f_β` a strict transform of `f`, satisfying the hypotheses (1)
  "`(z^{(β)})` is `J_β`-stable", (2) "`f_β` is `(J_β, τ_{(z^{(β)})})`-stable", (3)
  `w^{(β)} ∈ T*` and (4) the shape of the facts of the reformulation;
* `WeierstrassStageInv.succ`: the step `β → β + 1`: the facts (a), (b), (c) of the reformulation
  (`weierstrassDatum_facts`) are applied at the stage `β` to the monoidal transform
  `R_β → R_{β+1}`; (3), (4) at `β + 1` are (c)(ii), (iii), and (1), (2) at `β + 1` are the
  transitivity of stability along one step, "easily seen" (`IsJStable.succ_stage`,
  `IsJTauZStable.succ_stage` of `Compat/StageStability.lean`); for a trivial center the datum is
  carried along `R_β ≅ R_{β+1}`;
* `WeierstrassDatum.isJTauZStable_snoc`: `(z, w)` is `J`-stable and `f` is `(J, τ_{(z,w)})`-stable;
* `exists_isJTauZStable_snoc_aux`: Lemma 25 from its parts.
-/

@[expose] public section

open IsLocalRing

namespace Hironaka

universe u

section Transport

variable {A B : Type u} [CommRing A] [IsRegularLocalRing A] [CommRing B] [IsRegularLocalRing B]

/-- The datum of the reformulation of Lemma 25 carried along a ring isomorphism. -/
noncomputable def WeierstrassDatum.map (D : WeierstrassDatum A) (φ : A ≃+* B) :
    WeierstrassDatum B where
  F := D.F.transport φ
  F0 := D.F0
  rank_eq_one := D.rank_eq_one

@[simp]
theorem WeierstrassDatum.map_w (D : WeierstrassDatum A) (φ : A ≃+* B) :
    (D.map φ).w = D.w := rfl

theorem WeierstrassDatum.map_z (D : WeierstrassDatum A) (φ : A ≃+* B) :
    (D.map φ).F.z = fun j => φ (D.F.z j) := rfl

end Transport

section TransportFacts

variable {A B : Type u} [CommRing A] [IsRegularLocalRing A] [CommRing B] [IsRegularLocalRing B]

/-- The expansion coefficients are unchanged by transport along a ring isomorphism. -/
theorem RegularFrame.expCoeff_transport (F : RegularFrame A) (φ : A ≃+* B) (x : A)
    (C : Fin F.r →₀ ℕ) : (F.transport φ).expCoeff (φ x) C = F.expCoeff x C := by
  classical
  obtain ⟨G, hG⟩ := exists_evZ_sub_mem_pow F (C.degree + 1) x
  have hev : ∀ G : MvPolynomial (Fin F.r) F.S, (F.transport φ).evZ G = φ (F.evZ G) := by
    intro G
    induction G using MvPolynomial.induction_on with
    | C c =>
      have e1 : (F.transport φ).evZ (MvPolynomial.C c) = algebraMap (F.transport φ).S B c :=
        (F.transport φ).evZ.commutes c
      have e2 : F.evZ (MvPolynomial.C c) = algebraMap F.S A c := F.evZ.commutes c
      exact e1.trans ((show algebraMap (F.transport φ).S B c = φ (algebraMap F.S A c) from rfl).trans
        (congrArg φ e2.symm))
    | add p q hp hq =>
      have e1 : (F.transport φ).evZ (p + q) =
          (F.transport φ).evZ p + (F.transport φ).evZ q := map_add _ _ _
      have e2 : F.evZ (p + q) = F.evZ p + F.evZ q := map_add _ _ _
      calc (F.transport φ).evZ (p + q)
          = (F.transport φ).evZ p + (F.transport φ).evZ q := e1
        _ = φ (F.evZ p) + φ (F.evZ q) := by rw [hp, hq]
        _ = φ (F.evZ p + F.evZ q) := (map_add φ _ _).symm
        _ = φ (F.evZ (p + q)) := by rw [e2]
    | mul_X p j hp =>
      have e1 : (F.transport φ).evZ (p * MvPolynomial.X j) =
          (F.transport φ).evZ p * (F.transport φ).evZ (MvPolynomial.X j) := map_mul _ _ _
      have e2 : F.evZ (p * MvPolynomial.X j) = F.evZ p * F.evZ (MvPolynomial.X j) := map_mul _ _ _
      have e3 : (F.transport φ).evZ (MvPolynomial.X j) = φ (F.z j) := by
        let _ : Algebra F.S B := (F.transport φ).algebra
        exact MvPolynomial.aeval_X (R := F.S) (F.transport φ).z j
      have e4 : F.evZ (MvPolynomial.X j) = F.z j := MvPolynomial.aeval_X F.z j
      calc (F.transport φ).evZ (p * MvPolynomial.X j)
          = (F.transport φ).evZ p * (F.transport φ).evZ (MvPolynomial.X j) := e1
        _ = φ (F.evZ p) * φ (F.z j) := by rw [hp, e3]
        _ = φ (F.evZ p * F.z j) := (map_mul φ _ _).symm
        _ = φ (F.evZ (p * MvPolynomial.X j)) := by rw [e2, e4]
  have hG' : φ x - (F.transport φ).evZ G ∈ (F.transport φ).idealZ ^ (C.degree + 1) := by
    rw [hev, ← map_sub, F.idealZ_transport φ, ← Ideal.map_pow]
    exact Ideal.mem_map_of_mem _ hG
  rw [RegularFrame.expCoeff_eq (F.transport φ) hG' (Nat.lt_succ_self _),
    RegularFrame.expCoeff_eq F hG (Nat.lt_succ_self _)]
  rfl

end TransportFacts

section TransportFacts2

variable {A B : Type u} [CommRing A] [IsRegularLocalRing A] [CommRing B] [IsRegularLocalRing B]

/-- The shape (4) is preserved by ring isomorphisms. -/
theorem WeierstrassDatum.hasShape_map (D : WeierstrassDatum A) (φ : A ≃+* B) {f : A}
    (h : D.HasShape f) : (D.map φ).HasShape (φ f) := by
  obtain ⟨C, e, u, p, hu, he, hdeg, hcoef⟩ := h
  refine ⟨C, e, u, p, hu, he, ?_, ?_⟩
  · rw [ordElem_maximalIdeal_ringEquiv_aux φ]
    exact hdeg
  · show (D.F.transport φ).expCoeff (φ f) C = _
    rw [RegularFrame.expCoeff_transport]
    exact hcoef

/-- The condition (3) is preserved by ring isomorphisms. -/
theorem WeierstrassDatum.inTauStar_map [Hironaka.HironakaCitedResults.{u}] (D : WeierstrassDatum A) (φ : A ≃+* B) {f : A}
    (h : D.InTauStar f) : (D.map φ).InTauStar (φ f) := by
  have hα := mapsRSOP_of_bijective_aux (φ : A →+* B) φ.bijective
  have hsep := isResiduallySeparable_of_bijective_aux (φ : A →+* B) φ.bijective
  have := grMapMax_mem_tauZSubmoduleStar (φ : A →+* B) hα hsep D.F.z (fun _ : Fin 1 => f) h
  show initialForm (maximalIdeal B) (φ D.wR) ∈ _
  rw [show φ D.wR = (φ : A →+* B) D.wR from rfl, initialForm_map_of_mapsRSOP (φ : A →+* B) hα]
  exact this

end TransportFacts2

section Helpers

variable {A : Type u} [CommRing A] [IsRegularLocalRing A]

omit [IsRegularLocalRing A] in
/-- The order with respect to a smaller ideal is smaller. -/
theorem Ideal.ordElem_mono_ideal {I K : Ideal A} (h : I ≤ K) (a : A) :
    Ideal.ordElem I a ≤ Ideal.ordElem K a :=
  Ideal.ordElem_le fun ν hν => Ideal.le_ordElem (Ideal.pow_right_mono h ν hν)

/-- Reindexing a system of elements along an equality of the lengths does not change `T*`. -/
theorem tauZSubmoduleStar_cast {n m i : ℕ} (h : n = m) (z : Fin m → A) (f : Fin i → A) :
    tauZSubmoduleStar A (fun j : Fin n => z (Fin.cast h j)) f = tauZSubmoduleStar A z f := by
  subst h
  rfl

/-- Reindexing a system of elements along an equality of the lengths does not change `τ_{(z)}`. -/
theorem tauZ_cast {n m i : ℕ} (h : n = m) (z : Fin m → A) (f : Fin i → A) :
    tauZ A (fun j : Fin n => z (Fin.cast h j)) f = tauZ A z f := by
  subst h
  rfl

end Helpers

section CharZero

variable {R : Type u} [CommRing R] [IsRegularLocalRing R]

/-- The residue field of every `R_β` of a sequence has characteristic zero when that of `R` has
(the canonical homomorphisms are local). -/
theorem MonoidalSequence.charZero_residueField [CharZero (ResidueField R)]
    (Sq : MonoidalSequence.{u}) (e : R ≃+* Sq.ring 0) (β : ℕ) :
    CharZero (ResidueField (Sq.ring β)) := by
  induction β with
  | zero =>
    exact (RingHom.charZero_iff (ResidueField.map (e : R →+* Sq.ring 0)).injective).mp inferInstance
  | succ β ih =>
    exact (RingHom.charZero_iff (ResidueField.map ((Sq.equiv β : (Sq.transform β).ring →+*
      Sq.ring (β + 1)).comp (Sq.transform β).toRing)).injective).mp ih

end CharZero

section Induction

variable {R : Type u} [CommRing R] [IsRegularLocalRing R] [IsDomain R] [CharZero (ResidueField R)]

/-- The data of a permissible residually separable algebraic sequence of monoidal transforms of
`R` for `J` along which `ν*`, `t`, `τ^{(a)}` are those of `J` at the index `ᾱ` (the hypotheses of
Definitions 11 and 13). -/
structure SequenceUpTo (J : Ideal R) (αb : ℕ) where
  /-- The sequence. -/
  Sq : MonoidalSequence.{u}
  /-- `R = R₀`. -/
  e : R ≃+* Sq.ring 0
  h0 : Sq.ideal 0 = J.map e
  hperm : Sq.IsPermissible
  hsep : Sq.IsResiduallySeparableAlgebraic
  hnu : nuStar (Sq.ring αb) (Sq.ideal αb) = nuStar R J
  ht : t (Sq.ring αb) (Sq.ideal αb) = t R J
  htau : ∀ a, 1 ≤ a → a ≤ t R J → tau (Sq.ring αb) (Sq.ideal αb) a = tau R J a

/-- **The invariant of the induction along a sequence** ("one can easily see that, if we prove
these facts, then the proof of the lemma is completed", p. 271): at the stage `β`, the datum
`(S_β; z^{(β)}), (S₀,β; w^{(β)})` of the reformulation on `R_β`, whose frame consists of strict
transforms of the `z_j`, whose `w^{(β)}` is a strict transform of `w`, and an `f_β` which is a
strict transform of `f`, satisfying the hypotheses of the reformulation at `R_β`, `J_β`:
(1) `(z^{(β)})` is `J_β`-stable, (2) `f_β` is `(J_β, τ_{(z^{(β)})})`-stable, (3) `w^{(β)}` lies in
`T*` of `f_β`, (4) `f_β` has the shape (4). -/
def WeierstrassStageInv (D : WeierstrassDatum R) (f : R)
    (Sq : MonoidalSequence.{u}) (e : R ≃+* Sq.ring 0) (β : ℕ) : Prop :=
  ∃ (D' : WeierstrassDatum (Sq.ring β)) (f' : Sq.ring β), Sq.IsStrictFrame D.F e β D'.F ∧
    Sq.IsStrictTransformElem e D.wR β D'.wR ∧ Sq.IsStrictTransformElem e f β f' ∧
    D'.InTauStar f' ∧ D'.HasShape f' ∧ D'.F.IsJStable (Sq.ideal β) ∧
    IsJTauZStable (Sq.ideal β) D'.F.z f'

omit [IsDomain R] [CharZero (ResidueField R)] in
/-- The start of the induction (the stage `0`: `R ≅ R₀`, the hypotheses transported along the
isomorphism). -/
theorem WeierstrassStageInv.zero [Hironaka.HironakaCitedResults.{u}] {J : Ideal R} {D : WeierstrassDatum R} {f : R}
    (h1 : D.F.IsJStable J) (h2 : IsJTauZStable J D.F.z f) (h3 : D.InTauStar f)
    (h4 : D.HasShape f) (Sq : MonoidalSequence.{u}) (e : R ≃+* Sq.ring 0)
    (h0 : Sq.ideal 0 = J.map e) :
    WeierstrassStageInv D f Sq e 0 := by
  refine ⟨D.map e, e f, MonoidalSequence.IsStrictFrame.zero Sq D.F e, rfl, rfl,
    D.inTauStar_map e h3, D.hasShape_map e h4, ?_, ?_⟩
  · intro j
    have := IsJStable.transport e (h1 j)
    rwa [← h0] at this
  · have := IsJTauZStable.transport e h2
    rwa [← h0] at this

/-- What `(J; τ_{(z)})`-stability of `f` gives at the stage `β ≤ ᾱ` for a frame of strict
transforms of the `z_j` and a strict transform `f_β`: `ν_{M_β}(f_β) = ν`, `ν_{P_β}(f_β) = ν`
and `τ_{(z^{(β)})}(f_β) = τ_{(z)}(f)`. -/
theorem WeierstrassInv.facts [Hironaka.HironakaCitedResults.{u}] {J : Ideal R} {D : WeierstrassDatum R} {f : R}
    (h2 : IsJTauZStable J D.F.z f) {αb : ℕ} (S : SequenceUpTo J αb) {β : ℕ} (hβ : β ≤ αb)
    {D' : WeierstrassDatum (S.Sq.ring β)} {f' : S.Sq.ring β}
    (hSF : S.Sq.IsStrictFrame D.F S.e β D'.F) (hf : S.Sq.IsStrictTransformElem S.e f β f') :
    Ideal.ordElem (maximalIdeal (S.Sq.ring β)) f' = Ideal.ordElem (maximalIdeal R) f ∧
      (S.Sq.center β ≠ ⊤ → Ideal.ordElem (S.Sq.center β) f' = Ideal.ordElem (maximalIdeal R) f) ∧
      tauZ (S.Sq.ring β) D'.F.z (fun _ : Fin 1 => f') = tauZ R D.F.z (fun _ : Fin 1 => f) := by
  have hmono := MonoidalSequence.nuStar_t_tau_eq_of_le J S.Sq S.e S.h0 S.hperm S.hsep αb S.hnu
    S.htau
  obtain ⟨hr, hz⟩ := hSF
  have hzs : ∀ j : Fin D.F.r, S.Sq.IsStrictTransformElem S.e (D.F.z j) β
      (D'.F.z (Fin.cast hr.symm j)) := fun j => by
    have := hz (Fin.cast hr.symm j)
    rwa [show Fin.cast hr (Fin.cast hr.symm j) = j from Fin.ext rfl] at this
  obtain ⟨h1', h2', h3'⟩ := h2.2.2 S.Sq S.e S.h0 S.hperm S.hsep β (hmono β hβ).1
    (hmono β hβ).2.1 (hmono β hβ).2.2 _ hzs f' hf
  refine ⟨h1', h2', ?_⟩
  rw [← h3']
  exact (tauZ_cast hr.symm D'.F.z _).symm

end Induction

section InductionStep

variable {R : Type u} [CommRing R] [IsRegularLocalRing R] [IsDomain R] [CharZero (ResidueField R)]

omit [IsDomain R] [CharZero (ResidueField R)] in
/-- Between the stages `β` and `β + 1` of a sequence along which `ν*`, `t`, `τ^{(a)}` are those of
`J` at `ᾱ`, they do not change. -/
theorem SequenceUpTo.stage_conditions [Hironaka.HironakaCitedResults.{u}] {J : Ideal R} {αb : ℕ} (S : SequenceUpTo J αb) {β : ℕ}
    (hβ : β < αb) :
    nuStar (S.Sq.ring (β + 1)) (S.Sq.ideal (β + 1)) = nuStar (S.Sq.ring β) (S.Sq.ideal β) ∧
      t (S.Sq.ring (β + 1)) (S.Sq.ideal (β + 1)) = t (S.Sq.ring β) (S.Sq.ideal β) ∧
      ∀ a, 1 ≤ a → a ≤ t (S.Sq.ring β) (S.Sq.ideal β) →
        tau (S.Sq.ring (β + 1)) (S.Sq.ideal (β + 1)) a = tau (S.Sq.ring β) (S.Sq.ideal β) a := by
  have hmono := MonoidalSequence.nuStar_t_tau_eq_of_le J S.Sq S.e S.h0 S.hperm S.hsep αb S.hnu
    S.htau
  have h1 := hmono (β + 1) hβ
  have h0 := hmono β hβ.le
  exact ⟨h1.1.trans h0.1.symm, h1.2.1.trans h0.2.1.symm, fun a ha hat =>
    (h1.2.2 a ha (hat.trans h0.2.1.le)).trans (h0.2.2 a ha (hat.trans h0.2.1.le)).symm⟩

omit [IsDomain R] [CharZero (ResidueField R)] in
/-- The same for the strict transform of `J_β` in the monoidal transform `R_β → R_{β+1}`. -/
theorem SequenceUpTo.transform_conditions [Hironaka.HironakaCitedResults.{u}] {J : Ideal R} {αb : ℕ} (S : SequenceUpTo J αb) {β : ℕ}
    (hβ : β < αb) :
    nuStar (S.Sq.transform β).ring (strictTransformIdeal (S.Sq.transform β) (S.Sq.ideal β)) =
        nuStar (S.Sq.ring β) (S.Sq.ideal β) ∧
      t (S.Sq.transform β).ring (strictTransformIdeal (S.Sq.transform β) (S.Sq.ideal β)) =
        t (S.Sq.ring β) (S.Sq.ideal β) ∧
      ∀ a, 1 ≤ a → a ≤ t (S.Sq.ring β) (S.Sq.ideal β) →
        tau (S.Sq.transform β).ring (strictTransformIdeal (S.Sq.transform β) (S.Sq.ideal β)) a =
          tau (S.Sq.ring β) (S.Sq.ideal β) a := by
  obtain ⟨hc1, hc2, hc3⟩ := S.stage_conditions hβ
  have hI : S.Sq.ideal (β + 1) = (strictTransformIdeal (S.Sq.transform β) (S.Sq.ideal β)).map
      (S.Sq.equiv β : (S.Sq.transform β).ring →+* S.Sq.ring (β + 1)) := S.Sq.ideal_succ β
  obtain ⟨e1, e2, e3⟩ := nuStar_t_tau_map_of_bijective_aux
    (S.Sq.equiv β : (S.Sq.transform β).ring →+* S.Sq.ring (β + 1)) (S.Sq.equiv β).bijective
    (strictTransformIdeal (S.Sq.transform β) (S.Sq.ideal β))
  rw [← hI] at e1 e2 e3
  refine ⟨e1.symm.trans hc1, e2.symm.trans hc2, fun a ha hat => ?_⟩
  exact (e3 a ha (hat.trans (e2.symm.trans hc2).ge)).symm.trans (hc3 a ha hat)

open Classical in
omit [IsDomain R] in
/-- **The induction step** (p. 271, "one can easily see that, if we prove these facts, then the
proof of the lemma is completed"): the invariant at the stage `β < ᾱ` implies the invariant at
`β + 1`.  For a center `P_β ≠ R_β` the facts (a), (b), (c) of the reformulation
(`weierstrassDatum_facts`) are applied to `R_β`, `J_β`, the datum and `f_β` of the stage `β`, whose
hypotheses (1)--(4) hold by the invariant; (3), (4) at `β + 1` are (ii), (iii) of (c), and (1), (2)
at `β + 1` are the transitivity of stability along one step (`IsJStable.succ_stage`,
`IsJTauZStable.succ_stage`).  For a trivial center the datum is carried along the isomorphism
`R_β ≅ R_{β+1}`. -/
theorem WeierstrassStageInv.succ [Hironaka.HironakaCitedResults.{u}] {J : Ideal R} {D : WeierstrassDatum R} {f : R}
    (h1 : D.F.IsJStable J) {αb : ℕ} (S : SequenceUpTo J αb) {β : ℕ} (hβ : β < αb)
    (hI : WeierstrassStageInv D f S.Sq S.e β) :
    WeierstrassStageInv D f S.Sq S.e (β + 1) := by
  classical
  obtain ⟨D', f', hSF, hw, hf, hT, hS, h1β, h2β⟩ := hI
  have hreg := S.hperm.hasRegularCenters
  have hperm : IsPermissibleCenter (S.Sq.ring β) (S.Sq.ideal β) (S.Sq.center β) := S.hperm β
  obtain ⟨hnuβ, htβ, hτβ⟩ := S.stage_conditions hβ
  -- the datum at the stage `β + 1`
  obtain ⟨D₂, f₂, hSF2, hw2, hf2, hT2, hS2⟩ :
      ∃ (D₂ : WeierstrassDatum (S.Sq.ring (β + 1))) (f₂ : S.Sq.ring (β + 1)),
        S.Sq.IsStrictFrame D.F S.e (β + 1) D₂.F ∧
        S.Sq.IsStrictTransformElem S.e D.wR (β + 1) D₂.wR ∧
        S.Sq.IsStrictTransformElem S.e f (β + 1) f₂ ∧ D₂.InTauStar f₂ ∧ D₂.HasShape f₂ := by
    by_cases hc : S.Sq.center β = ⊤
    · -- trivial center: `R_β ≅ R_{β+1}`
      have hbij := MonoidalSequence.toRing_bijective_of_eq_top_aux (S.Sq.transform β) hc
      let ψ : S.Sq.ring β ≃+* S.Sq.ring (β + 1) := RingEquiv.ofBijective
        ((S.Sq.equiv β : (S.Sq.transform β).ring →+* S.Sq.ring (β + 1)).comp
          (S.Sq.transform β).toRing) ((S.Sq.equiv β).bijective.comp hbij)
      obtain ⟨hr, hz⟩ := hSF
      refine ⟨D'.map ψ, ψ f', ⟨hr, fun j => ?_⟩, ?_, ?_, D'.inTauStar_map ψ hT,
        D'.hasShape_map ψ hS⟩
      · exact S.Sq.isStrictTransformElem_succ_of_center_eq_top S.e (hz j) hc
      · exact S.Sq.isStrictTransformElem_succ_of_center_eq_top S.e hw hc
      · exact S.Sq.isStrictTransformElem_succ_of_center_eq_top S.e hf hc
    · -- a proper center: the facts (a), (b), (c) of the reformulation at the stage `β`
      obtain ⟨hP, hSreg⟩ := ((hreg β).2).resolve_left hc
      have : (S.Sq.center β).IsPrime := hP
      have : IsRegularLocalRing (S.Sq.ring β ⧸ S.Sq.center β) := hSreg
      have : CharZero (ResidueField (S.Sq.ring β)) := S.Sq.charZero_residueField S.e β
      have : IsRegularLocalRing (S.Sq.transform β).ring :=
        IsRegularLocalRing.of_ringEquiv (S.Sq.equiv β).symm
      have hPM : S.Sq.center β ≤ maximalIdeal (S.Sq.ring β) :=
        IsLocalRing.le_maximalIdeal (Ideal.IsPrime.ne_top ‹_›)
      obtain ⟨⟨-, hwP⟩, hbν, hc3⟩ := weierstrassDatum_facts (S.Sq.ideal β) D' f' h1β h2β
        ((D'.inTauStar_iff_tauParams f').mp hT) hS (S.Sq.center β) hperm (S.Sq.transform β)
        (S.hsep β)
      obtain ⟨hn1, ht1, hτ1⟩ := S.transform_conditions hβ
      obtain ⟨y, FT, FT0, -, -, -, -, -, hmul, hfin⟩ := hc3 hn1 ht1 hτ1
      obtain ⟨ν, hν⟩ : ∃ ν : ℕ, (ν : ℕ∞) = Ideal.ordElem (maximalIdeal (S.Sq.ring β)) f' := by
        obtain ⟨A, e', -, -, -, -, hdeg, -⟩ := hS
        exact ⟨A.degree + e', hdeg⟩
      obtain ⟨f₂, hf₂, hTau, -, hsh⟩ := hfin ν hν
      have hb : Ideal.ordElem (S.Sq.center β) f' = ν := hbν ν hν
      have hT₂ : (D'.transform FT FT0).InTauStar f₂ :=
        ((D'.transform FT FT0).inTauStar_iff_tauParams f₂).mpr hTau
      -- `w` has order `1` along the center
      have hordw : Ideal.ordElem (S.Sq.center β) D'.wR = 1 := by
        refine le_antisymm ?_ ?_
        · exact (Ideal.ordElem_mono_ideal hPM D'.wR).trans D'.ordElem_wR.le
        · exact Ideal.le_ordElem (by simpa using hwP)
      refine ⟨(D'.transform FT FT0).map (S.Sq.equiv β), S.Sq.equiv β f₂, ?_, ?_, ?_,
        (D'.transform FT FT0).inTauStar_map _ hT₂, (D'.transform FT FT0).hasShape_map _ hsh⟩
      · exact MonoidalSequence.IsStrictFrame.transport_frameTransform h1 S.h0 S.hperm S.hsep
          S.hnu S.htau hβ hSF FT
      · exact S.Sq.isStrictTransformElem_succ_of_center_ne_top S.e hreg hw hc (ν := 1)
          (by rw [hordw]; rfl) FT.span_x (by rw [pow_one]; exact hmul.symm)
      · exact S.Sq.isStrictTransformElem_succ_of_center_ne_top S.e hreg hf hc (hν := hb)
          FT.span_x hf₂
  -- the hypotheses (1), (2) at the stage `β + 1`: transitivity of stability along one step
  have key : ∀ {r₂ : ℕ} (z₂ : Fin r₂ → S.Sq.ring (β + 1)) (hr' : r₂ = D'.F.r)
      (_ : ExtendsToRSOP (S.Sq.ring (β + 1)) (Finset.image z₂ Finset.univ))
      (_ : ∀ j : Fin r₂, Ideal.span {z₂ j} = (strictTransformIdeal (S.Sq.transform β)
        (Ideal.span {D'.F.z (Fin.cast hr' j)})).map (S.Sq.equiv β))
      (f₂ : S.Sq.ring (β + 1)) (_ : Ideal.span {f₂} = (strictTransformIdeal (S.Sq.transform β)
        (Ideal.span {f'})).map (S.Sq.equiv β)),
      IsJStableSystem (S.Sq.ideal (β + 1)) z₂ ∧ IsJTauZStable (S.Sq.ideal (β + 1)) z₂ f₂ := by
    intro r₂ z₂ hr'
    subst hr'
    intro hext hz₂ f₂ hf₂
    exact ⟨fun j => IsJStable.succ_stage S.Sq β hperm (S.hsep β) hnuβ htβ hτβ (h1β j) (hz₂ j),
      IsJTauZStable.succ_stage S.Sq β hperm (S.hsep β) hnuβ htβ hτβ h2β hext hz₂ hf₂⟩
  obtain ⟨hr, hz⟩ := hSF
  obtain ⟨hr2, hz2⟩ := hSF2
  obtain ⟨hJ₂, hτ₂⟩ := key D₂.F.z (hr2.trans hr.symm) D₂.F.extends_rsop (fun j => by
    have hzj := hz (Fin.cast (hr2.trans hr.symm) j)
    have hz2j := hz2 j
    rw [show Fin.cast hr (Fin.cast (hr2.trans hr.symm) j) = Fin.cast hr2 j from Fin.ext rfl]
      at hzj
    exact MonoidalSequence.isStrictTransformElem_oneStep S.Sq S.e hzj hz2j) f₂
    (MonoidalSequence.isStrictTransformElem_oneStep S.Sq S.e hf hf2)
  exact ⟨D₂, f₂, ⟨hr2, hz2⟩, hw2, hf2, hT2, hS2, hJ₂, hτ₂⟩

omit [IsDomain R] in
/-- The invariant holds along the whole sequence up to `ᾱ`. -/
theorem WeierstrassStageInv.of_le [Hironaka.HironakaCitedResults.{u}] {J : Ideal R} {D : WeierstrassDatum R} {f : R}
    (h1 : D.F.IsJStable J) (h2 : IsJTauZStable J D.F.z f) (h3 : D.InTauStar f)
    (h4 : D.HasShape f) {αb : ℕ} (S : SequenceUpTo J αb) :
    ∀ β ≤ αb, WeierstrassStageInv D f S.Sq S.e β := by
  intro β
  induction β with
  | zero => exact fun _ => WeierstrassStageInv.zero h1 h2 h3 h4 S.Sq S.e S.h0
  | succ β ih => exact fun hβ => WeierstrassStageInv.succ h1 S (by omega) (ih (by omega))

end InductionStep

section Final

variable {R : Type u} [CommRing R] [IsRegularLocalRing R] [IsDomain R] [CharZero (ResidueField R)]

open Classical in
omit [IsDomain R] in
/-- `w` has order `1` along a proper center: it lies in the center by (a) of the facts of the
reformulation at the stage. -/
theorem WeierstrassStageInv.ordElem_center_wR [Hironaka.HironakaCitedResults.{u}] {J : Ideal R} {αb : ℕ} (S : SequenceUpTo J αb)
    {β : ℕ} {D' : WeierstrassDatum (S.Sq.ring β)} {f' : S.Sq.ring β} (hT : D'.InTauStar f')
    (hS : D'.HasShape f') (h1β : D'.F.IsJStable (S.Sq.ideal β))
    (h2β : IsJTauZStable (S.Sq.ideal β) D'.F.z f') (hc : S.Sq.center β ≠ ⊤) :
    Ideal.ordElem (S.Sq.center β) D'.wR = 1 := by
  obtain ⟨hP, hSreg⟩ := ((S.hperm.hasRegularCenters β).2).resolve_left hc
  have : (S.Sq.center β).IsPrime := hP
  have : IsRegularLocalRing (S.Sq.ring β ⧸ S.Sq.center β) := hSreg
  have : CharZero (ResidueField (S.Sq.ring β)) := S.Sq.charZero_residueField S.e β
  have : IsRegularLocalRing (S.Sq.transform β).ring :=
    IsRegularLocalRing.of_ringEquiv (S.Sq.equiv β).symm
  have hPM : S.Sq.center β ≤ maximalIdeal (S.Sq.ring β) :=
    IsLocalRing.le_maximalIdeal (Ideal.IsPrime.ne_top ‹_›)
  obtain ⟨⟨-, hwP⟩, -, -⟩ := weierstrassDatum_facts (S.Sq.ideal β) D' f' h1β h2β
    ((D'.inTauStar_iff_tauParams f').mp hT) hS (S.Sq.center β) (S.hperm β) (S.Sq.transform β)
    (S.hsep β)
  refine le_antisymm ?_ ?_
  · exact (Ideal.ordElem_mono_ideal hPM D'.wR).trans D'.ordElem_wR.le
  · exact Ideal.le_ordElem (by simpa using hwP)

open Classical in
/-- **"One can easily see that, if we prove these facts, then the proof of the lemma is
completed"** (p. 271): from the facts (a), (b), (c) of the reformulation (applied along a
permissible sequence, step by step, with the frames carried along as in the proof of Remark 3,
`WeierstrassStageInv.succ`) one gets that `(z, w)` is `J`-stable and that `f` is
`(J, τ_{(z,w)})`-stable.  The paper's induction along the sequence is not written. -/
theorem WeierstrassDatum.isJTauZStable_snoc [Hironaka.HironakaCitedResults.{u}] (J : Ideal R)
    (D : WeierstrassDatum R) (f : R) (h1 : D.F.IsJStable J) (h2 : IsJTauZStable J D.F.z f)
    (h3 : D.InTauStar f) (h4 : D.HasShape f)
    (_hinj : Function.Injective (Fin.snoc D.F.z D.wR : Fin (D.F.r + 1) → R))
    (hext : ExtendsToRSOP R
      (Finset.image (Fin.snoc D.F.z D.wR : Fin (D.F.r + 1) → R) Finset.univ)) :
    IsJStableSystem J (Fin.snoc D.F.z D.wR : Fin (D.F.r + 1) → R) ∧
      IsJTauZStable J (Fin.snoc D.F.z D.wR : Fin (D.F.r + 1) → R) f := by
  classical
  -- `w` is `J`-stable
  have hW : IsJStable J D.wR := by
    intro Sq e h0 hperm hsep α hnu ht htau wα hwα
    let S : SequenceUpTo J α := ⟨Sq, e, h0, hperm, hsep, hnu, ht, htau⟩
    obtain ⟨D', f', hSF, hw, hf, hT, hS, h1β, h2β⟩ :=
      WeierstrassStageInv.of_le h1 h2 h3 h4 S α le_rfl
    obtain ⟨u, hu⟩ := MonoidalSequence.IsStrictTransformElem.unique Sq hwα hw
    have hord : ∀ I : Ideal (Sq.ring α), Ideal.ordElem I D'.wR = Ideal.ordElem I wα := fun I => by
      rw [hu]
      exact Ideal.ordElem_isUnit_mul I u.isUnit wα
    refine ⟨(hord _).symm.trans (D'.ordElem_wR.trans D.ordElem_wR.symm), fun hc => ?_⟩
    rw [← hord, WeierstrassStageInv.ordElem_center_wR S hT hS h1β h2β hc, D.ordElem_wR]
    simp
  have hJS : IsJStableSystem J (Fin.snoc D.F.z D.wR : Fin (D.F.r + 1) → R) := by
    intro j
    refine Fin.lastCases ?_ (fun j => ?_) j
    · simpa using hW
    · simpa using h1 j
  refine ⟨hJS, hext, hJS, ?_⟩
  intro Sq e h0 hperm hsep αb hnu ht htau zα hzα fα hfα
  let S : SequenceUpTo J αb := ⟨Sq, e, h0, hperm, hsep, hnu, ht, htau⟩
  obtain ⟨D', f', hSF, hw, hf, hT, hS, -, -⟩ := WeierstrassStageInv.of_le h1 h2 h3 h4 S αb le_rfl
  obtain ⟨hA, hB, -⟩ := h2.2.2 Sq e h0 hperm hsep αb hnu ht htau (Fin.init zα)
    (fun j => by have := hzα j.castSucc; rwa [Fin.snoc_castSucc] at this) fα hfα
  refine ⟨hA, hB, ?_⟩
  obtain ⟨-, -, hτ'⟩ := WeierstrassInv.facts h2 S le_rfl hSF hf
  obtain ⟨hr, hz⟩ := hSF
  set zF : Fin D.F.r → Sq.ring αb := fun j => D'.F.z (Fin.cast hr.symm j) with hzF
  have hzs : ∀ j : Fin D.F.r, Sq.IsStrictTransformElem e (D.F.z j) αb (zF j) := fun j => by
    have := hz (Fin.cast hr.symm j)
    rwa [show Fin.cast hr (Fin.cast hr.symm j) = j from Fin.ext rfl] at this
  have hassoc : ∀ j, Associated (zα j)
      ((Fin.snoc zF D'.wR : Fin (D.F.r + 1) → Sq.ring αb) j) := by
    intro j
    refine Fin.lastCases ?_ (fun j => ?_) j
    · obtain ⟨u, hu⟩ := MonoidalSequence.IsStrictTransformElem.unique Sq
        (by simpa using hzα (Fin.last _)) hw
      exact ⟨u, by rw [Fin.snoc_last, hu, mul_comm]⟩
    · obtain ⟨u, hu⟩ := MonoidalSequence.IsStrictTransformElem.unique Sq
        (by simpa using hzα j.castSucc) (hzs j)
      exact ⟨u, by rw [Fin.snoc_castSucc, hu, mul_comm]⟩
  have hfassoc : Associated fα f' := by
    obtain ⟨u, hu⟩ := MonoidalSequence.IsStrictTransformElem.unique Sq hfα hf
    exact ⟨u, by rw [hu, mul_comm]⟩
  have hmem : initialForm (maximalIdeal (Sq.ring αb)) D'.wR ∈
      tauZSubmoduleStar (Sq.ring αb) zF (fun _ : Fin 1 => f') := by
    rw [hzF, tauZSubmoduleStar_cast hr.symm D'.F.z]
    exact hT
  rw [tauZ_snoc_eq_sub_one_of_mem D.F.z _ D.wR h3,
    tauZ_congr_of_associated zα _ fα f' hassoc hfassoc,
    tauZ_snoc_eq_sub_one_of_mem zF _ D'.wR hmem, ← hτ', hzF, tauZ_cast hr.symm D'.F.z]

end Final

section LemmaTwentyFive

open Classical in
/-- **Lemma 25 from its three parts**: the choice of `w` (`exists_weierstrassDatum`), the facts of
the reformulation (`weierstrassDatum_facts`) and the induction along a sequence
(`WeierstrassDatum.isJTauZStable_snoc`); (2) is `tauZ_snoc_eq_sub_one_of_mem`. -/
theorem exists_isJTauZStable_snoc_aux [Hironaka.HironakaCitedResults.{u}] {R : Type u} [CommRing R] [IsRegularLocalRing R]
    [IsAdicComplete (maximalIdeal R) R] [CharZero (ResidueField R)] (J : Ideal R) {r : ℕ}
    (z : Fin r → R) (hz : Function.Injective z) (f : R)
    (h_i : IsJStableSystem J z ∧ ExtendsToRSOP R (Finset.image z Finset.univ))
    (h_ii : IsJTauZStable J z f) (hτ : 1 ≤ tauZ R z (fun _ : Fin 1 => f)) :
    ∃ w : R, Function.Injective (Fin.snoc z w : Fin (r + 1) → R) ∧
      (IsJStableSystem J (Fin.snoc z w : Fin (r + 1) → R) ∧
        ExtendsToRSOP R (Finset.image (Fin.snoc z w : Fin (r + 1) → R) Finset.univ)) ∧
      tauZ R (Fin.snoc z w : Fin (r + 1) → R) (fun _ : Fin 1 => f) =
        tauZ R z (fun _ : Fin 1 => f) - 1 ∧
      IsJTauZStable J (Fin.snoc z w : Fin (r + 1) → R) f := by
  have : IsDomain R := Transforms.isDomain_of_isRegularLocalRing R
  obtain ⟨D, hr, hzD, h3, h4, hinj, hext⟩ := exists_weierstrassDatum z hz h_i.2 f hτ
  subst hr
  have hzz : D.F.z = z := funext fun j => by simpa using hzD j
  subst hzz
  obtain ⟨hs, hst⟩ := D.isJTauZStable_snoc J f h_i.1 h_ii h3 h4 hinj hext
  exact ⟨D.wR, hinj, ⟨hs, hext⟩, tauZ_snoc_eq_sub_one_of_mem D.F.z _ D.wR h3, hst⟩

end LemmaTwentyFive

end Hironaka
