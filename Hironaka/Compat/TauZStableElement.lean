/-
Copyright (c) 2026 Daattavya Aggarwal, Minhyong Kim, Oisin Kim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daattavya Aggarwal, Minhyong Kim, Oisin Kim
-/
module

public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Hironaka.Ch3.JStability
public import Hironaka.Ch3.FrameTransforms
public import Hironaka.Compat.NormalizedStrictTransform
public import Hironaka.Compat.TauZMonotone
public import Hironaka.Compat.TauZTransport
public import Hironaka.Compat.TauZBaseChange
public import Hironaka.Compat.WeierstrassSequence
public import Hironaka.Ch3.JStableStandardBase
public import Hironaka.Compat.NormalizedStandardBase
public import Hironaka.Statements

/-!
# `f_{i+1}` is `(J, tau_{(z)})`-stable (claim (B) of Theorem 9, p. 274)

Claim (B) of the proof of Theorem 9 chooses `f_{i+1}` normalized by `(f_1, ..., f_i)` and says: "The
proof of (B) for this `f_{i+1}` can be obtained by Lemmas 18-19, §7, and Lemmas 20-21, §8".  The
condition to be proved for `f_{i+1}` is (6) of the induction: `f_{i+1}` is `(J, tau_{(z)})`-stable
(Definition 13), a statement about all permissible sequences of monoidal transforms.  The lemmas
quoted treat ONE monoidal transform; this file carries out both parts.

* `tauZ_stage_oneStep`: one monoidal transform `R_1` of `R` with centre `P`, a frame transform
  `(S_1; w)` and the quotients `g_j = x^{-nu_j} f_j`, `g' = x^{-nu_{i+1}} f'`: the conclusions of
  Lemma 20 (`g'` normalized by `(g_1, ..., g_i)`, `(g_1, ..., g_i, g')` extendable to a standard
  base of `J_1`), of Lemma 21 (`tau_{(w)}(g') = tau_{(z)}(f')`), and the transport of the condition
  `Z_1, ..., Z_r ∈ T(f_1, ..., f_i)` (that is (11) of Lemma 21) to `W_1, ..., W_r ∈ T(g_1, ..., g_i)`.
  `nu_P(f') = nu_{i+1}` is the first assertion of Lemma 18 (`ordElem_prime_snoc_eq_nuI`).
* `ElemInv`, `ElemInv.zero`, `ElemInv.succ`, `ElemInv.of_le`: the induction along a sequence
  (the frames of Remark 3 are strict transforms of the `z_j`, the `f_j` of the induction are
  `(J, tau_{(z)})`-stable, which gives (2), (8), (9) at every stage), and
* `isJTauZStable_snoc_element`: `f_{i+1}` is `(J, tau_{(z)})`-stable.
-/

@[expose] public section

open IsLocalRing MvPolynomial

namespace Hironaka

universe u

section Helpers

variable {R : Type u} [CommRing R] [IsRegularLocalRing R]

/-- The characters `ν^{(k)}` of two ideals with the same `ν*` agree. -/
theorem nuI_eq_of_nuStar_eq {R' : Type u} [CommRing R'] [IsRegularLocalRing R'] {J : Ideal R}
    {J' : Ideal R'} (hnu : nuStar R' J' = nuStar R J) (k : ℕ+) : nuI R' J' k = nuI R J k :=
  congrFun (toLex.injective hnu) _

/-- The members of a system extendable to a standard base of `J` lie in `J`. -/
theorem ExtendsToStandardBase.mem_ideal {J : Ideal R} {i : ℕ} {f : Fin i → R}
    (h : ExtendsToStandardBase J f) (j : Fin i) : f j ∈ J := by
  obtain ⟨m, σ, him, hσ, hσf⟩ := h
  rw [← hσf j]
  exact hσ.1 _

end Helpers

section Lemma18Use

attribute [local instance] RegularFrame.isDomain_S

variable {R : Type u} [CommRing R] [IsRegularLocalRing R]

/-- `ν_P(f_{i+1}) = ν^{(i+1)}(J)` for a member normalized by `(f₁, …, f_i)` of a system
extendable to a standard base, and a permissible center `P ⊇ (z)` along which `ν_P(f_j) = ν^{(j)}(J)`
(Lemma 18 gives `≥`; `P ⊆ M` and `ν_M(f_{i+1}) = ν^{(i+1)}(J)` give `≤`). -/
theorem ordElem_prime_snoc_eq_nuI [Hironaka.HironakaCitedResults.{u}] (J : Ideal R) (F : RegularFrame R) {i : ℕ} (f : Fin i → R)
    (g : R) (hfJ : ∀ j, f j ∈ J) (hgJ : g ∈ J)
    (h1 : ExtendsToStandardBase J (Fin.snoc f g : Fin (i + 1) → R))
    (h2 : ∀ j : Fin i, tauZ R F.z (fun _ : Fin 1 => f j) = 0) (h3 : F.IsNormalizedBy f g)
    (P : Ideal R) [P.IsPrime] (h4 : IsPermissibleCenter R J P) (h5 : F.idealZ ≤ P)
    (h6 : ∀ j : Fin i, Ideal.ordElem P (f j) = nuI R J (j : ℕ).succPNat) :
    Ideal.ordElem P g = nuI R J i.succPNat := by
  have hPM : P ≤ maximalIdeal R := le_maximalIdeal (Ideal.IsPrime.ne_top ‹_›)
  obtain ⟨hge, -⟩ := ordElem_ge_nuI_of_isNormalizedBy F J f hfJ h1.of_snoc
    (fun j => RegularFrame.initialForm_mem_adjoin_of_tauZ_eq_zero F (f j) (h2 j)) g hgJ h3 P h5 h4 h6
  have hle : Ideal.ordElem P g ≤ Ideal.ordElem (maximalIdeal R) g :=
    Ideal.ordElem_mono_ideal hPM g
  have hM : Ideal.ordElem (maximalIdeal R) g = nuI R J i.succPNat := by
    have := ordElem_snoc_eq_nuI h1 (Fin.last i)
    rw [Fin.snoc_last] at this
    simpa using this
  exact le_antisymm (hle.trans hM.le) hge

end Lemma18Use

section Transport

variable {A B : Type u} [CommRing A] [IsRegularLocalRing A] [CommRing B] [IsRegularLocalRing B]

/-- **The stage data are transported by ring isomorphisms**: the standard base, the normalization,
the membership `Z_l ∈ T(h)` and `τ_{(z)}(g)` of the stage data of claim (B) are unchanged under a
ring isomorphism `φ : A ≃+* B` carrying the ideal, the frame and the elements. -/
theorem stageData_transport [Hironaka.HironakaCitedResults.{u}] (φ : A ≃+* B) (I : Ideal A) (G : RegularFrame A) {i : ℕ}
    (h : Fin i → A) (g : A) (hext : ExtendsToStandardBase I (Fin.snoc h g : Fin (i + 1) → A))
    (hnorm : G.IsNormalizedBy h g) (hZ : ∀ l, frameForm G.z l ∈ tauZSubmodule A h) :
    ExtendsToStandardBase (I.map (φ : A →+* B))
        (Fin.snoc (fun j => φ (h j)) (φ g) : Fin (i + 1) → B) ∧
      (G.transport φ).IsNormalizedBy (fun j => φ (h j)) (φ g) ∧
      (∀ l, frameForm (G.transport φ).z l ∈ tauZSubmodule B (fun j => φ (h j))) ∧
      tauZ B (G.transport φ).z (fun _ : Fin 1 => φ g) = tauZ A G.z (fun _ : Fin 1 => g) := by
  have hα := mapsRSOP_of_bijective_aux (φ : A →+* B) φ.bijective
  have hsep := isResiduallySeparable_of_bijective_aux (φ : A →+* B) φ.bijective
  have := IsLocalHom.of_surjective (φ : A →+* B) φ.bijective.2
  refine ⟨?_, G.isNormalizedBy_transport φ h g hnorm, fun l => ?_, ?_⟩
  · obtain ⟨m, σ, him, hσ, hσf⟩ := hext
    refine ⟨m, fun j => φ (σ j), him,
      isStandardBase_map_of_bijective_aux (φ : A →+* B) φ.bijective I σ hσ, fun j => ?_⟩
    simp only [hσf]
    refine Fin.lastCases ?_ (fun j => ?_) j
    · simp
    · simp
  · have hmap : tauZSubmodule B (fun j => φ (h j)) = Submodule.span (B ⧸ maximalIdeal B)
        (grMapMax (φ : A →+* B) hα '' (tauZSubmodule A h : Set (AssocGraded (maximalIdeal A)))) :=
      tauZSubmodule_map (φ : A →+* B) hα hsep h
    rw [hmap]
    refine Submodule.subset_span ⟨frameForm G.z l, hZ l, ?_⟩
    exact (initialForm_map_of_mapsRSOP (φ : A →+* B) hα (G.z l)).symm
  · exact tauZ_map (φ : A →+* B) hα hsep G.z (fun _ : Fin 1 => g)

end Transport

section OneStepMain

attribute [local instance] RegularFrame.isDomain_S
attribute [local instance] Ideal.Quotient.field

variable {R : Type u} [CommRing R] [IsRegularLocalRing R] [IsDomain R]

/-- **The inductive step along one monoidal transform** (pp. 273–274, claim (B): "The proof of
(B) for this `f_{i+1}` can be obtained by Lemmas 18–19, §7, and Lemmas 20–21, §8"): for the
data of Lemma 20 and Lemma 21 (hypotheses (1)–(10) and (12)), with the condition (2) of the
induction in the form `Z₁, …, Z_r ∈ T(f₁, …, f_i)`, the quotients `g_j = x^{-ν_j} f_j`,
`g' = x^{-ν_{i+1}} f'` (the latter exists, `ν_P(f') = ν_{i+1}` by Lemma 18) satisfy again the same
conditions for the frame transform `(S₁; w)`: `g'` is normalized by `(g₁, …, g_i)` and
`(g₁, …, g_i, g')` extends to a standard base of `J₁` (Lemma 20), `W₁, …, W_r ∈ T(g₁, …, g_i)`
(the transport of (11), `frameForm_mem_tauZSubmodule`), and `τ_{(w)}(g') = τ_{(z)}(f')`
(Lemma 21). -/
theorem tauZ_stage_oneStep [Hironaka.HironakaCitedResults.{u}] (J : Ideal R) (F : RegularFrame R) {i : ℕ} (f : Fin i → R) (f' : R)
    (hfJ : ∀ j, f j ∈ J) (hf'J : f' ∈ J)
    (h1 : ExtendsToStandardBase J (Fin.snoc f f' : Fin (i + 1) → R))
    (h2 : ∀ j : Fin i, tauZ R F.z (fun _ : Fin 1 => f j) = 0)
    (h3 : F.IsNormalizedBy f f')
    (hZ : ∀ l, frameForm F.z l ∈ tauZSubmodule R f)
    (P : Ideal R) [P.IsPrime] (h4 : IsPermissibleCenter R J P) (h5 : F.idealZ ≤ P)
    (h6 : ∀ j : Fin i, Ideal.ordElem P (f j) = nuI R J (j : ℕ).succPNat)
    (T : MonoidalTransform R P) [IsLocalHom T.toRing] [IsRegularLocalRing T.ring]
    (hsep : RingHom.IsResiduallySeparableAlgebraic (R := R) (R' := T.ring) T.toRing)
    (x : F.S) (hxP : algebraMap F.S R x ∈ P)
    (h7 : P.map T.toRing = Ideal.span {T.toRing (algebraMap F.S R x)})
    (FT : F.FrameTransform T) (h7' : FT.x = T.toRing (algebraMap F.S R x))
    (ν : Fin (i + 1) → ℕ) (hν : ∀ j : Fin (i + 1), (ν j : ℕ∞) = nuI R J (j : ℕ).succPNat)
    (g : Fin i → T.ring)
    (hg : ∀ j : Fin i, T.toRing (algebraMap F.S R x) ^ ν j.castSucc * g j = T.toRing (f j))
    (h8 : ∀ j : Fin i, tauZ T.ring FT.w (fun _ : Fin 1 => g j) = 0)
    (h9 : ∀ j : Fin i, Ideal.ordElem (maximalIdeal T.ring) (g j) = nuI R J (j : ℕ).succPNat)
    (h10 : ∀ j : ℕ+, (j : ℕ) ≤ i + 1 → nuI T.ring (strictTransformIdeal T J) j = nuI R J j)
    (h12 : ∀ a, 1 ≤ a → a ≤ t R J → tau T.ring (strictTransformIdeal T J) a = tau R J a) :
    (∀ l, frameForm FT.w l ∈ tauZSubmodule T.ring g) ∧
    ∃ g' : T.ring, T.toRing (algebraMap F.S R x) ^ ν (Fin.last i) * g' = T.toRing f' ∧
      FT.toRegularFrame.IsNormalizedBy g g' ∧
      ExtendsToStandardBase (strictTransformIdeal T J) (Fin.snoc g g' : Fin (i + 1) → T.ring) ∧
      tauZ T.ring FT.w (fun _ : Fin 1 => g') = tauZ R F.z (fun _ : Fin 1 => f') := by
  classical
  have hord := ordElem_snoc_eq_nuI h1
  have hordf : ∀ j : Fin i, Ideal.ordElem (maximalIdeal R) (f j) = ν j.castSucc := fun j => by
    have := hord j.castSucc
    rw [Fin.snoc_castSucc] at this
    exact this.trans (hν j.castSucc).symm
  -- the order of `f'` along `P`
  have h6' : Ideal.ordElem P f' = nuI R J i.succPNat :=
    ordElem_prime_snoc_eq_nuI J F f f' hfJ hf'J h1 h2 h3 P h4 h5 h6
  -- the quotient `g' = x^{-ν_{i+1}} f'`
  obtain ⟨g', hg'⟩ : ∃ g' : T.ring,
      T.toRing (algebraMap F.S R x) ^ ν (Fin.last i) * g' = T.toRing f' := by
    have hfP : f' ∈ P ^ ν (Fin.last i) := Ideal.mem_pow_of_ordElem (by
      rw [h6']
      simpa using (hν (Fin.last i)).symm)
    have hmem : T.toRing f' ∈ (P ^ ν (Fin.last i)).map T.toRing := Ideal.mem_map_of_mem _ hfP
    rw [Ideal.map_pow, h7, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at hmem
    obtain ⟨c, hc⟩ := hmem
    exact ⟨c, hc.symm⟩
  -- Lemma 20
  have hl20 := isNormalizedBy_frameTransform_and_extendsToStandardBase J F f f' hfJ hf'J h1 h2 h3
    P h4 h5 h6 h6' T hsep x hxP h7 FT h7' ν hν g hg h8 h9 g' hg'
  -- the transport of (11)
  have hFTx0 : FT.x ≠ 0 := by
    intro h0
    have hxT : T.toRing T.x ∈ Ideal.span {FT.x} := by
      rw [FT.span_x]; exact Ideal.mem_map_of_mem _ T.x_mem
    rw [h0, Ideal.span_singleton_eq_bot.mpr rfl, Ideal.mem_bot] at hxT
    exact T.x_ne_zero (MonoidalTransform.toRing_injective T (hxT.trans (map_zero _).symm))
  have hx0 : FT.TS.toRing x ≠ 0 := fun h0 =>
    hFTx0 (by rw [h7', ← FT.beta_toRing x, h0, map_zero])
  have hg0 : ∀ j : Fin i, FT.x ^ ν j.castSucc * g j = T.toRing (f j) := fun j => by
    rw [h7']; exact hg j
  have hgM : ∀ j : Fin i, Ideal.ordElem (maximalIdeal T.ring) (g j) = ν j.castSucc :=
    fun j => (h9 j).trans (hν j.castSucc).symm
  have hWg := FT.frameForm_mem_tauZSubmodule x h7' hx0 hsep f g (fun j => ν j.castSucc) hordf h2
    hg0 hgM h8 hZ
  -- Lemma 21
  obtain ⟨a, ha1, hat, hmua⟩ := exists_mu_eq_of_nuI_eq J i.succPNat (ν (Fin.last i))
    (by simpa using (hν (Fin.last i)).symm)
  have hμ : (mu R J a : ℕ∞) = nuI R J i.succPNat := by
    rw [hmua]
    simpa using hν (Fin.last i)
  have h21 := tauZ_eq_tauZ_frameTransform J F f f' hfJ hf'J h1 h2 h3 P h4 h5 h6 h6' T hsep x hxP
    h7 FT h7' ν hν g hg h8 h9 g' hg' h10 a ha1 hat hμ (tauZ_empty_eq_of_mem h2 hZ)
    (h12 a ha1 hat)
  exact ⟨hWg, g', hg', hl20.1, hl20.2 h10, h21.symm⟩

end OneStepMain
section Induction

attribute [local instance] RegularFrame.isDomain_S

variable {R : Type u} [CommRing R] [IsRegularLocalRing R] [IsDomain R]
  [CharZero (ResidueField R)]

/-- **The invariant of the induction along a sequence** (claim (B), p. 274: "The proof of (B) for
this `f_{i+1}` can be obtained by Lemmas 18–19, §7, and Lemmas 20–21, §8", applied along the
sequence of Definition 13): at the stage `β` a regular frame `G` of `R_β` whose members are strict
transforms of the `z_j`, strict transforms `h_j` of the `f_j` and `g'` of `g` such that
`(h₁, …, h_i, g')` extends to a standard base of `J_β`, `g'` is normalized by `(h₁, …, h_i)`
with respect to `G`, `Z₁, …, Z_r ∈ T(h₁, …, h_i)` (condition (2) of the induction, which gives
(11) of Lemma 21) and `τ_{(z^{(β)})}(g') = τ_{(z)}(g)`. -/
def ElemInv (F : RegularFrame R) {i : ℕ} (f : Fin i → R) (g : R) (Sq : MonoidalSequence.{u})
    (e : R ≃+* Sq.ring 0) (β : ℕ) : Prop :=
  ∃ (G : RegularFrame (Sq.ring β)) (h : Fin i → Sq.ring β) (g' : Sq.ring β),
    Sq.IsStrictFrame F e β G ∧ (∀ j, Sq.IsStrictTransformElem e (f j) β (h j)) ∧
    Sq.IsStrictTransformElem e g β g' ∧
    ExtendsToStandardBase (Sq.ideal β) (Fin.snoc h g' : Fin (i + 1) → Sq.ring β) ∧
    G.IsNormalizedBy h g' ∧ (∀ l, frameForm G.z l ∈ tauZSubmodule (Sq.ring β) h) ∧
    tauZ (Sq.ring β) G.z (fun _ : Fin 1 => g') = tauZ R F.z (fun _ : Fin 1 => g)

omit [IsDomain R] [CharZero (ResidueField R)] in
/-- The start of the induction. -/
theorem ElemInv.zero [Hironaka.HironakaCitedResults.{u}] {J : Ideal R} {F : RegularFrame R} {i : ℕ} {f : Fin i → R} {g : R}
    (hext : ExtendsToStandardBase J (Fin.snoc f g : Fin (i + 1) → R)) (hnorm : F.IsNormalizedBy f g)
    (hZ : ∀ l, frameForm F.z l ∈ tauZSubmodule R f) (Sq : MonoidalSequence.{u})
    (e : R ≃+* Sq.ring 0) (h0 : Sq.ideal 0 = J.map e) : ElemInv F f g Sq e 0 := by
  obtain ⟨hex, hn, hZ', hτ⟩ := stageData_transport e J F f g hext hnorm hZ
  exact ⟨F.transport e, fun j => e (f j), e g, MonoidalSequence.IsStrictFrame.zero Sq F e,
    fun _ => rfl, rfl, by rw [h0]; exact hex, hn, hZ', hτ⟩

omit [IsDomain R] [CharZero (ResidueField R)] in
/-- What `(J; τ_{(z)})`-stability of the `f_j` gives at the stage `β ≤ ᾱ`. -/
theorem ElemInv.facts [Hironaka.HironakaCitedResults.{u}] {J : Ideal R} {F : RegularFrame R} {i : ℕ} {f : Fin i → R}
    (hst : ∀ j, IsJTauZStable J F.z (f j)) {αb : ℕ} (S : SequenceUpTo J αb) {β : ℕ}
    (hβ : β ≤ αb) {G : RegularFrame (S.Sq.ring β)} {h : Fin i → S.Sq.ring β}
    (hSF : S.Sq.IsStrictFrame F S.e β G) (hh : ∀ j, S.Sq.IsStrictTransformElem S.e (f j) β (h j))
    (j : Fin i) :
    Ideal.ordElem (maximalIdeal (S.Sq.ring β)) (h j) = Ideal.ordElem (maximalIdeal R) (f j) ∧
      (S.Sq.center β ≠ ⊤ →
        Ideal.ordElem (S.Sq.center β) (h j) = Ideal.ordElem (maximalIdeal R) (f j)) ∧
      tauZ (S.Sq.ring β) G.z (fun _ : Fin 1 => h j) = tauZ R F.z (fun _ : Fin 1 => f j) := by
  have hmono := MonoidalSequence.nuStar_t_tau_eq_of_le J S.Sq S.e S.h0 S.hperm S.hsep αb S.hnu
    S.htau
  obtain ⟨hr, hz⟩ := hSF
  have hzs : ∀ k : Fin F.r, S.Sq.IsStrictTransformElem S.e (F.z k) β
      (G.z (Fin.cast hr.symm k)) := fun k => by
    have := hz (Fin.cast hr.symm k)
    rwa [show Fin.cast hr (Fin.cast hr.symm k) = k from Fin.ext rfl] at this
  obtain ⟨h1', h2', h3'⟩ := (hst j).2.2 S.Sq S.e S.h0 S.hperm S.hsep β (hmono β hβ).1
    (hmono β hβ).2.1 (hmono β hβ).2.2 _ hzs (h j) (hh j)
  refine ⟨h1', h2', ?_⟩
  rw [← h3']
  exact (tauZ_cast hr.symm G.z _).symm

open Classical in
/-- **The induction step** (claim (B), p. 274): the invariant at the stage `β < ᾱ` implies the
invariant at `β + 1`.  For a trivial center the data are carried along the isomorphism
`R_β ≅ R_{β+1}`; for a center `P_β ≠ R_β` Lemmas 18, 20, 21 are applied (`tauZ_stage_oneStep`) to
the frame transform of Remark 3 with denominator in `P_β ∩ S_β`, the data at the stage `β` and the
quotients `x^{-ν_j} h_j`; the hypotheses (2) `τ_{(z^{(β)})}(h_j) = 0`, (8) and (9) come from the
`(J, τ_{(z)})`-stability of the `f_j`, and (10), (12) from the invariance of `ν*` and `τ^{(a)}`. -/
theorem ElemInv.succ [Hironaka.HironakaCitedResults.{u}] {J : Ideal R} {F : RegularFrame R} (hF : F.IsJStable J) {i : ℕ}
    {f : Fin i → R} {g : R} (hst : ∀ j, IsJTauZStable J F.z (f j))
    (hτf : ∀ j, tauZ R F.z (fun _ : Fin 1 => f j) = 0)
    (hext0 : ExtendsToStandardBase J (Fin.snoc f g : Fin (i + 1) → R)) {αb : ℕ}
    (S : SequenceUpTo J αb) {β : ℕ} (hβ : β < αb) (hI : ElemInv F f g S.Sq S.e β) :
    ElemInv F f g S.Sq S.e (β + 1) := by
  obtain ⟨G, h, g', hSF, hh, hg, hext, hnorm, hZ, hτg⟩ := hI
  have hmono := MonoidalSequence.nuStar_t_tau_eq_of_le J S.Sq S.e S.h0 S.hperm S.hsep αb S.hnu
    S.htau
  have hreg := S.hperm.hasRegularCenters
  have hβ' : β ≤ αb := hβ.le
  have hfacts := ElemInv.facts hst S hβ' hSF hh
  have hτh : ∀ j, tauZ (S.Sq.ring β) G.z (fun _ : Fin 1 => h j) = 0 := fun j =>
    (hfacts j).2.2.trans (hτf j)
  have hhJ : ∀ j, h j ∈ S.Sq.ideal β := fun j => by
    have := hext.mem_ideal j.castSucc
    simpa using this
  have hgJ : g' ∈ S.Sq.ideal β := by
    have := hext.mem_ideal (Fin.last i)
    simpa using this
  have hnuβ : nuStar (S.Sq.ring β) (S.Sq.ideal β) = nuStar R J := (hmono β hβ').1
  have hnuI : ∀ k, nuI (S.Sq.ring β) (S.Sq.ideal β) k = nuI R J k := nuI_eq_of_nuStar_eq hnuβ
  by_cases hc : S.Sq.center β = ⊤
  · -- trivial center: `R_β ≅ R_{β+1}`
    have hbij := MonoidalSequence.toRing_bijective_of_eq_top_aux (S.Sq.transform β) hc
    let ψ : S.Sq.ring β ≃+* S.Sq.ring (β + 1) := RingEquiv.ofBijective
      ((S.Sq.equiv β : (S.Sq.transform β).ring →+* S.Sq.ring (β + 1)).comp
        (S.Sq.transform β).toRing) ((S.Sq.equiv β).bijective.comp hbij)
    have hIψ : S.Sq.ideal (β + 1) = (S.Sq.ideal β).map (ψ : S.Sq.ring β →+* S.Sq.ring (β + 1)) := by
      rw [S.Sq.ideal_succ β, MonoidalSequence.strictTransformIdeal_eq_map_of_eq_top_aux _ hc]
      exact Ideal.map_map (S.Sq.transform β).toRing
        (S.Sq.equiv β : (S.Sq.transform β).ring →+* S.Sq.ring (β + 1))
    obtain ⟨hex', hn', hZ', hτ'⟩ := stageData_transport ψ (S.Sq.ideal β) G h g' hext hnorm hZ
    obtain ⟨hr, hz⟩ := hSF
    refine ⟨G.transport ψ, fun j => ψ (h j), ψ g', ⟨hr, fun j => ?_⟩, fun j => ?_, ?_, ?_, hn',
      hZ', hτ'.trans hτg⟩
    · exact S.Sq.isStrictTransformElem_succ_of_center_eq_top S.e (hz j) hc
    · exact S.Sq.isStrictTransformElem_succ_of_center_eq_top S.e (hh j) hc
    · exact S.Sq.isStrictTransformElem_succ_of_center_eq_top S.e hg hc
    · rw [hIψ]; exact hex'
  · -- a proper center
    set T := S.Sq.transform β with hT
    set I' := strictTransformIdeal T (S.Sq.ideal β) with hI'
    obtain ⟨hP, hSreg⟩ := ((hreg β).2).resolve_left hc
    have : (S.Sq.center β).IsPrime := hP
    have : IsRegularLocalRing (S.Sq.ring β ⧸ S.Sq.center β) := hSreg
    have : IsRegularLocalRing (S.Sq.transform β).ring :=
      IsRegularLocalRing.of_ringEquiv (S.Sq.equiv β).symm
    have hzP : G.idealZ ≤ S.Sq.center β :=
      MonoidalSequence.IsStrictFrame.idealZ_le_center hF S.h0 S.hperm S.hsep S.hnu S.htau hβ' hSF hc
    obtain ⟨FT, x, hxQ, hFTx⟩ := MonoidalSequence.IsStrictFrame.exists_isDenominatorInCenter hF
      S.h0 S.hperm S.hsep S.hnu S.htau hβ hSF
    have hx : (S.Sq.center β).map (S.Sq.transform β).toRing =
        Ideal.span {(S.Sq.transform β).toRing (algebraMap G.S (S.Sq.ring β) x)} := by
      rw [← hFTx]
      exact FT.span_x.symm
    -- the characters `ν_j = ν^{(j)}(J)` are finite
    have hfin : ∀ j : Fin (i + 1), ∃ n : ℕ, (n : ℕ∞) = nuI R J (j : ℕ).succPNat := by
      intro j
      obtain ⟨m, σ, him, hσ, hσf⟩ := hext0
      obtain ⟨n, hn⟩ := hσ.exists_ordElem_eq_natCast (Fin.castLE him j)
      refine ⟨n, ?_⟩
      have := ordElem_eq_nuI_of_isStandardBase J σ hσ (Fin.castLE him j)
      rw [hn] at this
      simpa using this
    choose ν hν using hfin
    have hord0 := ordElem_snoc_eq_nuI hext0
    have hordcenter : ∀ j : Fin i, Ideal.ordElem (S.Sq.center β) (h j) = ν j.castSucc := fun j => by
      rw [(hfacts j).2.1 hc]
      have := hord0 j.castSucc
      rw [Fin.snoc_castSucc] at this
      exact this.trans (hν j.castSucc).symm
    have h6 : ∀ j : Fin i, Ideal.ordElem (S.Sq.center β) (h j) =
        nuI (S.Sq.ring β) (S.Sq.ideal β) (j : ℕ).succPNat := fun j => by
      rw [hordcenter j, hnuI]
      exact hν j.castSucc
    -- the quotients `g_j = x^{-ν_j} h_j`
    choose gs hgs using fun j : Fin i =>
      MonoidalSequence.exists_mul_pow_eq_toRing_aux (S.Sq.transform β)
        (x := algebraMap G.S (S.Sq.ring β) x) hx.symm
        (Ideal.mem_pow_of_ordElem (hordcenter j) : h j ∈ S.Sq.center β ^ ν j.castSucc)
    have hstr : ∀ j, S.Sq.IsStrictTransformElem S.e (f j) (β + 1) (S.Sq.equiv β (gs j)) :=
      fun j => S.Sq.isStrictTransformElem_succ_of_center_ne_top S.e hreg (hh j) hc
        (ν := ν j.castSucc) (hordcenter j)
        (x := (S.Sq.transform β).toRing (algebraMap G.S (S.Sq.ring β) x)) hx.symm (w := gs j)
        (hgs j)
    -- the frame at the stage `β + 1`
    have hSF1 := MonoidalSequence.IsStrictFrame.transport_frameTransform hF S.h0 S.hperm S.hsep
      S.hnu S.htau hβ hSF FT
    obtain ⟨hr1, hz1⟩ := hSF1
    have hzs1 : ∀ k : Fin F.r, S.Sq.IsStrictTransformElem S.e (F.z k) (β + 1)
        (S.Sq.equiv β (FT.w (Fin.cast hr1.symm k))) := fun k => by
      have := hz1 (Fin.cast hr1.symm k)
      rwa [show Fin.cast hr1 (Fin.cast hr1.symm k) = k from Fin.ext rfl] at this
    have hα := mapsRSOP_of_bijective_aux (S.Sq.equiv β : (S.Sq.transform β).ring →+*
      S.Sq.ring (β + 1)) (S.Sq.equiv β).bijective
    have hsepα := isResiduallySeparable_of_bijective_aux (S.Sq.equiv β :
      (S.Sq.transform β).ring →+* S.Sq.ring (β + 1)) (S.Sq.equiv β).bijective
    -- (8), (9): stability of the `f_j` at the stage `β + 1`
    have hstab1 := fun j => (hst j).2.2 S.Sq S.e S.h0 S.hperm S.hsep (β + 1)
      (hmono (β + 1) hβ).1 (hmono (β + 1) hβ).2.1 (hmono (β + 1) hβ).2.2 _ hzs1 _ (hstr j)
    have h9 : ∀ j : Fin i, Ideal.ordElem (maximalIdeal (S.Sq.transform β).ring) (gs j) =
        nuI (S.Sq.ring β) (S.Sq.ideal β) (j : ℕ).succPNat := fun j => by
      rw [← ordElem_maximalIdeal_ringEquiv_aux (S.Sq.equiv β) (gs j), (hstab1 j).1, hnuI]
      have := hord0 j.castSucc
      rw [Fin.snoc_castSucc] at this
      exact this
    have h8 : ∀ j : Fin i, tauZ (S.Sq.transform β).ring FT.w (fun _ : Fin 1 => gs j) = 0 := by
      intro j
      calc tauZ (S.Sq.transform β).ring FT.w (fun _ : Fin 1 => gs j)
          = tauZ (S.Sq.transform β).ring (fun k : Fin F.r => FT.w (Fin.cast hr1.symm k))
              (fun _ : Fin 1 => gs j) := (tauZ_cast hr1.symm FT.w _).symm
        _ = tauZ (S.Sq.ring (β + 1)) (fun k : Fin F.r => S.Sq.equiv β (FT.w (Fin.cast hr1.symm k)))
              (fun _ : Fin 1 => S.Sq.equiv β (gs j)) :=
            (tauZ_map (S.Sq.equiv β : (S.Sq.transform β).ring →+* S.Sq.ring (β + 1)) hα hsepα
              (fun k : Fin F.r => FT.w (Fin.cast hr1.symm k)) (fun _ : Fin 1 => gs j)).symm
        _ = 0 := (hstab1 j).2.2.trans (hτf j)
    -- (10), (12): the invariants of `J_β` and `J_{β+1}`
    have hmapβ : nuStar (S.Sq.ring (β + 1)) (S.Sq.ideal (β + 1)) = nuStar T.ring I' ∧
        t (S.Sq.ring (β + 1)) (S.Sq.ideal (β + 1)) = t T.ring I' ∧
        ∀ k, 1 ≤ k → k ≤ t T.ring I' →
          tau (S.Sq.ring (β + 1)) (S.Sq.ideal (β + 1)) k = tau T.ring I' k := by
      rw [S.Sq.ideal_succ β]
      exact nuStar_t_tau_map_of_bijective_aux (S.Sq.equiv β : T.ring →+* S.Sq.ring (β + 1))
        (S.Sq.equiv β).bijective I'
    obtain ⟨hnuβ1, htβ1, hτβ1⟩ := hmono (β + 1) hβ
    obtain ⟨-, htβ, hτβ⟩ := hmono β hβ'
    have hnuT : nuStar T.ring I' = nuStar (S.Sq.ring β) (S.Sq.ideal β) :=
      hmapβ.1.symm.trans (hnuβ1.trans hnuβ.symm)
    have htT : t T.ring I' = t R J := hmapβ.2.1.symm.trans htβ1
    have h12 : ∀ a, 1 ≤ a → a ≤ t (S.Sq.ring β) (S.Sq.ideal β) →
        tau T.ring I' a = tau (S.Sq.ring β) (S.Sq.ideal β) a := fun a ha hat => by
      rw [htβ] at hat
      rw [← hmapβ.2.2 a ha (htT ▸ hat), hτβ1 a ha hat, hτβ a ha hat]
    have h10 : ∀ k : ℕ+, (k : ℕ) ≤ i + 1 → nuI T.ring I' k = nuI (S.Sq.ring β) (S.Sq.ideal β) k :=
      fun k _ => nuI_eq_of_nuStar_eq hnuT k
    -- the one-step theorem
    obtain ⟨hWg, g'', hg'', hnormT, hextT, hτT⟩ := tauZ_stage_oneStep (S.Sq.ideal β) G h g' hhJ hgJ
      hext hτh hnorm hZ (S.Sq.center β) (S.hperm β) hzP h6 T (S.hsep β) x hxQ hx FT hFTx
      ν (fun j => (hν j).trans (hnuI _).symm) gs hgs h8 h9 h10 h12
    -- the strict transform of `g`
    have hordg : Ideal.ordElem (S.Sq.center β) g' = ν (Fin.last i) := by
      rw [ordElem_prime_snoc_eq_nuI (S.Sq.ideal β) G h g' hhJ hgJ hext hτh hnorm (S.Sq.center β)
        (S.hperm β) hzP h6, hnuI]
      simpa using (hν (Fin.last i)).symm
    have hstrg : S.Sq.IsStrictTransformElem S.e g (β + 1) (S.Sq.equiv β g'') :=
      S.Sq.isStrictTransformElem_succ_of_center_ne_top S.e hreg hg hc (ν := ν (Fin.last i)) hordg
        (x := T.toRing (algebraMap G.S (S.Sq.ring β) x)) hx.symm (w := g'') hg''
    obtain ⟨hex', hn', hZ', hτ'⟩ := stageData_transport (S.Sq.equiv β) I' FT.toRegularFrame gs g''
      hextT hnormT hWg
    refine ⟨RegularFrame.transport FT.toRegularFrame (S.Sq.equiv β), fun j => S.Sq.equiv β (gs j),
      S.Sq.equiv β g'', ⟨hr1, hz1⟩, hstr, hstrg, ?_, hn', hZ', hτ'.trans (hτT.trans hτg)⟩
    rw [S.Sq.ideal_succ β]
    exact hex'

/-- The invariant holds along the whole sequence up to `ᾱ`. -/
theorem ElemInv.of_le [Hironaka.HironakaCitedResults.{u}] {J : Ideal R} {F : RegularFrame R} (hF : F.IsJStable J) {i : ℕ}
    {f : Fin i → R} {g : R} (hst : ∀ j, IsJTauZStable J F.z (f j))
    (hτf : ∀ j, tauZ R F.z (fun _ : Fin 1 => f j) = 0)
    (hext0 : ExtendsToStandardBase J (Fin.snoc f g : Fin (i + 1) → R))
    (hnorm : F.IsNormalizedBy f g) (hZ : ∀ l, frameForm F.z l ∈ tauZSubmodule R f) {αb : ℕ}
    (S : SequenceUpTo J αb) : ∀ β ≤ αb, ElemInv F f g S.Sq S.e β := by
  intro β
  induction β with
  | zero => exact fun _ => ElemInv.zero hext0 hnorm hZ S.Sq S.e S.h0
  | succ β ih => exact fun hβ => ElemInv.succ hF hst hτf hext0 S (by omega) (ih (by omega))

open Classical in
/-- **`g = f_{i+1}` is `(J, τ_{(z)})`-stable** (claim (B), p. 274: "The proof of (B) for this
`f_{i+1}` can be obtained by Lemmas 18–19, §7, and Lemmas 20–21, §8"): the `f_j`, `j ≤ i`, being
`(J, τ_{(z)})`-stable with `τ_{(z)}(f_j) = 0`, `Z₁, …, Z_r ∈ T(f₁, …, f_i)`, and `g` being
normalized by `(f₁, …, f_i)` with `(f₁, …, f_i, g)` extendable to a standard base of `J`.  The
paper treats one monoidal transform (`tauZ_stage_oneStep`); the induction along the sequence of
Definition 13 (`ElemInv`) is not written there. -/
theorem isJTauZStable_snoc_element [Hironaka.HironakaCitedResults.{u}] {J : Ideal R} {F : RegularFrame R} (hF : F.IsJStable J)
    {i : ℕ} {f : Fin i → R} {g : R} (hst : ∀ j, IsJTauZStable J F.z (f j))
    (hτf : ∀ j, tauZ R F.z (fun _ : Fin 1 => f j) = 0)
    (hext0 : ExtendsToStandardBase J (Fin.snoc f g : Fin (i + 1) → R))
    (hnorm : F.IsNormalizedBy f g) (hZ : ∀ l, frameForm F.z l ∈ tauZSubmodule R f) :
    IsJTauZStable J F.z g := by
  refine ⟨F.extends_rsop, hF, ?_⟩
  intro Sq e h0 hperm hsep αb hnu ht htau zα hzα fα hfα
  let S : SequenceUpTo J αb := ⟨Sq, e, h0, hperm, hsep, hnu, ht, htau⟩
  obtain ⟨G, h, g', hSF, hh, hg, hext, hnormβ, hZβ, hτβ⟩ :=
    ElemInv.of_le hF hst hτf hext0 hnorm hZ S αb le_rfl
  obtain ⟨u, hu⟩ := MonoidalSequence.IsStrictTransformElem.unique Sq hg hfα
  have hfacts := ElemInv.facts hst S le_rfl hSF hh
  have hτh : ∀ j, tauZ (Sq.ring αb) G.z (fun _ : Fin 1 => h j) = 0 := fun j =>
    (hfacts j).2.2.trans (hτf j)
  have hhJ : ∀ j, h j ∈ Sq.ideal αb := fun j => by
    have := hext.mem_ideal j.castSucc
    simpa using this
  have hgJ : g' ∈ Sq.ideal αb := by
    have := hext.mem_ideal (Fin.last i)
    simpa using this
  have hnuI : ∀ k, nuI (Sq.ring αb) (Sq.ideal αb) k = nuI R J k := nuI_eq_of_nuStar_eq hnu
  have hord0 := ordElem_snoc_eq_nuI hext0
  have hordg : Ideal.ordElem (maximalIdeal R) g = nuI R J i.succPNat := by
    have := hord0 (Fin.last i)
    rw [Fin.snoc_last] at this
    simpa using this
  refine ⟨?_, fun hc => ?_, ?_⟩
  · rw [hu, Ideal.ordElem_isUnit_mul _ u.isUnit, hordg, ← hnuI]
    have := ordElem_snoc_eq_nuI hext (Fin.last i)
    rw [Fin.snoc_last] at this
    simpa using this
  · obtain ⟨hQ, hSreg⟩ := ((hperm.hasRegularCenters αb).2).resolve_left hc
    have : (Sq.center αb).IsPrime := hQ
    have : IsRegularLocalRing (Sq.ring αb ⧸ Sq.center αb) := hSreg
    have hzP : G.idealZ ≤ Sq.center αb :=
      MonoidalSequence.IsStrictFrame.idealZ_le_center hF h0 hperm hsep hnu htau le_rfl hSF hc
    have h6 : ∀ j : Fin i, Ideal.ordElem (Sq.center αb) (h j) =
        nuI (Sq.ring αb) (Sq.ideal αb) (j : ℕ).succPNat := fun j => by
      rw [(hfacts j).2.1 hc, hnuI]
      have := hord0 j.castSucc
      rw [Fin.snoc_castSucc] at this
      exact this
    rw [hu, Ideal.ordElem_isUnit_mul _ u.isUnit,
      ordElem_prime_snoc_eq_nuI (Sq.ideal αb) G h g' hhJ hgJ hext hτh hnormβ (Sq.center αb)
        (hperm αb) hzP h6, hnuI, hordg]
  · obtain ⟨hr, hz⟩ := hSF
    set zF : Fin F.r → Sq.ring αb := fun j => G.z (Fin.cast hr.symm j) with hzF
    have hzs : ∀ j : Fin F.r, Sq.IsStrictTransformElem e (F.z j) αb (zF j) := fun j => by
      have := hz (Fin.cast hr.symm j)
      rwa [show Fin.cast hr (Fin.cast hr.symm j) = j from Fin.ext rfl] at this
    have hassoc : ∀ j, Associated (zα j) (zF j) := fun j => by
      obtain ⟨v, hv⟩ := MonoidalSequence.IsStrictTransformElem.unique Sq (hzs j) (hzα j)
      exact ⟨v⁻¹, by rw [hv, mul_comm (v : Sq.ring αb) (zF j), mul_assoc, Units.mul_inv, mul_one]⟩
    have hfassoc : Associated fα g' :=
      ⟨u⁻¹, by rw [hu, mul_comm (u : Sq.ring αb) g', mul_assoc, Units.mul_inv, mul_one]⟩
    rw [tauZ_congr_of_associated zα zF fα g' hassoc hfassoc]
    show tauZ (Sq.ring αb) (fun j : Fin F.r => G.z (Fin.cast hr.symm j)) _ = _
    rw [tauZ_cast hr.symm G.z _]
    exact hτβ

end Induction

section Choice

variable {R : Type u} [CommRing R] [IsRegularLocalRing R]

/-- **The choice of `f_{i+1}`** (p. 274: "Then take an element `f_{i+1}` of `J` such that
`(f₁, …, f_i, f_{i+1})` is extendable to a standard base of `J` and that `f_{i+1}` is normalized
by `(f₁, …, f_i)` with respect to `(S; z₁, …, z_r)`. (We should refer to Lemma 17, §7. See also the
footnote 11 of this chapter.)"): this is the inductive step of footnote 11
(`RegularFrame.exists_snoc_isNormalizedSystem`) for a system `(f₁, …, f_i)` whose initial forms
lie in the associated subalgebra of `(S; z)` (for a normalized system) but which need not be
normalized itself, and for a regular frame which is not a `τ`-frame: only Lemma 17
(`exists_isNormalizedBy_sub_sum`) and the choice of the standard base are used. -/
theorem RegularFrame.exists_snoc_isNormalizedBy [IsAdicComplete (maximalIdeal R) R]
    (F : RegularFrame R) (J : Ideal R) {i : ℕ} (f : Fin i → R) (hfJ : ∀ j, f j ∈ J)
    (hext : ExtendsToStandardBase J f)
    (hfsub : ∀ j, initialForm (maximalIdeal R) (f j) ∈ F.assocSubalgebra)
    (hnot : ¬ IsStandardBase R J f) :
    ∃ g : R, g ∈ J ∧ ExtendsToStandardBase J (Fin.snoc f g : Fin (i + 1) → R) ∧
      F.IsNormalizedBy f g := by
  classical
  obtain ⟨m', G, hle, hG, hGf⟩ := hext
  have hi : i < m' := by
    rcases lt_or_eq_of_le hle with h | h
    · exact h
    · exfalso
      apply hnot
      subst h
      have hfG : f = G := funext fun j => (hGf j).symm
      rw [hfG]
      exact hG
  have hext : ExtendsToStandardBase J f := ⟨m', G, hle, hG, hGf⟩
  set k : Fin m' := ⟨i, hi⟩ with hk
  obtain ⟨h, hh1, hh2⟩ := F.exists_isNormalizedBy_sub_sum f hfsub (G k)
  set f' := G k - ∑ j, h j * f j with hf'
  obtain ⟨hGJ, hφJ, ⟨d, hd, hmono⟩, hspan, hirr⟩ := hG
  have hGstd : IsStandardBase R J G := ⟨hGJ, hφJ, ⟨d, hd, hmono⟩, hspan, hirr⟩
  have hgM : ∀ j, Ideal.ordElem (maximalIdeal R) (G j) = d j := fun j =>
    ordElem_eq_of_isStandardBase_of_initialForm_mem_homogeneous J G hGstd d hd j
  have hGf' : ∀ j : Fin (k : ℕ), G (Fin.castLE k.2.le j) = f j := hGf
  have hhh : ∀ j : Fin (k : ℕ), Ideal.ordElem (maximalIdeal R) (G k) -
      Ideal.ordElem (maximalIdeal R) (G (Fin.castLE k.2.le j)) ≤
        Ideal.ordElem (maximalIdeal R) (h j) := fun j => by
    rw [hGf' j]; exact hh1 j
  obtain ⟨hord, hirrf'⟩ := ordElem_sub_sum_eq_and_initialForm_notMem J G hGstd k h hhh
  have hsumeq : ∑ j : Fin (k : ℕ), h j * G (Fin.castLE k.2.le j) = ∑ j, h j * f j :=
    Finset.sum_congr rfl fun j _ => by rw [hGf' j]
  rw [hsumeq] at hord hirrf'
  have hrange : (Set.range fun j : Fin (k : ℕ) =>
      initialForm (maximalIdeal R) (G (Fin.castLE k.2.le j))) =
      Set.range fun j : Fin i => initialForm (maximalIdeal R) (f j) := by
    congr 1; funext j; rw [hGf' j]
  rw [hrange] at hirrf'
  have hf'J : f' ∈ J := sub_mem (hGJ k) (Ideal.sum_mem _ fun j _ => J.mul_mem_left _ (hfJ j))
  have hlow : ∀ j : Fin i, Ideal.ordElem (maximalIdeal R) (f j) ≤ d k := fun j => by
    rw [← hGf j, hgM]
    exact_mod_cast hmono (by simp [Fin.le_def, k])
  have hup : ((d k : ℕ) : ℕ∞) ≤ nuI R J i.succPNat := by
    have := ordElem_eq_nuI_of_isStandardBase J G hGstd k
    rw [hgM] at this
    exact this.le
  exact ⟨f', hf'J, extendsToStandardBase_snoc J f f' hext hf'J (d k) (by rw [hord, hgM]) hlow hup
    hirrf', hh2⟩

end Choice

end Hironaka
