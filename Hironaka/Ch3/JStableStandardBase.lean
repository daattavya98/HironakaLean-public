/-
Copyright (c) 2026 Daattavya Aggarwal, Minhyong Kim, Oisin Kim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daattavya Aggarwal, Minhyong Kim, Oisin Kim
-/
module

public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Architect
public import Hironaka.Ch3.JStability
public import Hironaka.Ch3.FrameTransforms
public import Hironaka.Compat.FrameChain
public import Hironaka.Compat.TauOrderedFrame
public import Hironaka.Compat.NormalizedStrictTransform
public import Hironaka.Statements

/-!
# `J`-stability of normalized standard bases (Theorem 8, pp. 264-265)

Theorem 8: for a `J`-stable regular `tau`-frame `(S; z_1, ..., z_tau)` of `R` for `J`, every
normalized standard base of `J` with respect to `(S; z_1, ..., z_tau)` is `J`-stable.

The printed proof treats one monoidal transform (the one-step theorem
`isNormalizedStandardBase_strictTransform_of_isRegularTauFrame` of
`Hironaka/Compat/NormalizedStrictTransform.lean`: the reduction to complete `R = S{z}`, and the
induction on the blocks `a` with the partial frames `S^{(a)}`, Lemma 20 and Lemma 19, in
`Hironaka/Compat/NormalizedStrictTransformComplete.lean`).
This file adds what the paper leaves out: the induction along the sequence of Definition 11
(`exists_isNormalizedStage_succ`, `exists_isNormalizedStage_of_le`), the identification of the
frames of the chain of frame transforms of Remark 3 with the regular `tau`-frames of Definition 12
(`MonoidalSequence.IsStrictFrame.isRegularTauFrame`), and the final computation of the orders
`nu_{M}`, `nu_{P}`.  See the docstring of `isJStableSystem_of_isNormalizedStandardBase` for the
printed route and the gaps filled.
-/

@[expose] public section

open IsLocalRing

namespace Hironaka

universe u

section ChainInduction

variable {R : Type u} [CommRing R] [IsRegularLocalRing R] [IsDomain R]

omit [IsDomain R] in
/-- The members of a standard base have a finite order (their initial forms are non-zero). -/
theorem IsStandardBase.exists_ordElem_eq_natCast {J : Ideal R} {m : ℕ} {g : Fin m → R}
    (hg : IsStandardBase R J g) (j : Fin m) :
    ∃ n : ℕ, Ideal.ordElem (maximalIdeal R) (g j) = n := by
  have hne : initialForm (maximalIdeal R) (g j) ≠ 0 := fun h0 =>
    hg.2.2.2.2 j (by beta_reduce; rw [h0]; exact zero_mem _)
  have htop : Ideal.ordElem (maximalIdeal R) (g j) ≠ ⊤ := fun h => hne (by
    rw [initialForm, dite_eq_left h])
  exact ENat.ne_top_iff_exists.mp htop |>.imp fun n hn => hn.symm

omit [IsDomain R] in
/-- **Frames of strict transforms are regular `τ`-frames** (p. 264, Definition 12): along a
permissible residually separable algebraic sequence with `ν*` and the `τ^{(a)}` unchanged up to
`ᾱ`, every regular frame `G` of `R_β` (`β ≤ ᾱ`) whose members are strict transforms of the members
of a `J`-stable regular `τ`-frame `F` of `R` for `J` is a regular `τ`-frame of `R_β` for `J_β`.
Definition 12 provides a regular `τ`-frame `G₀` of `R_β` for `J_β` which is a frame transform of
`F` along the sequence; its members are also strict transforms of the members of `F`
(`MonoidalSequence.FrameTransformAlong.isStrictTransformElem_frame`), hence differ from those of
`G` by units, which does not affect being a regular `τ`-frame
(`RegularFrame.isRegularTauFrame_of_associated`).  (The paper identifies the `J`-stable `τ`-frame
of Definition 12 with the frames of the chain of frame transforms tacitly.) -/
theorem MonoidalSequence.IsStrictFrame.isRegularTauFrame [Hironaka.HironakaCitedResults.{u}] {F : RegularFrame R} {J : Ideal R}
    (hF : F.IsJStableTauFrame J) (ht1 : 1 ≤ t R J) {Sq : MonoidalSequence.{u}}
    {e : R ≃+* Sq.ring 0} (h0 : Sq.ideal 0 = J.map e) (hperm : Sq.IsPermissible)
    (hsep : Sq.IsResiduallySeparableAlgebraic) {αb : ℕ}
    (hnu : nuStar (Sq.ring αb) (Sq.ideal αb) = nuStar R J)
    (htau : ∀ a, 1 ≤ a → a ≤ t R J → tau (Sq.ring αb) (Sq.ideal αb) a = tau R J a)
    {β : ℕ} (hβ : β ≤ αb) {G : RegularFrame (Sq.ring β)} (hG : Sq.IsStrictFrame F e β G) :
    G.IsRegularTauFrame (Sq.ideal β) := by
  classical
  have hmono := MonoidalSequence.nuStar_t_tau_eq_of_le J Sq e h0 hperm hsep αb hnu htau
  have key : ∃ G₀ : RegularFrame (Sq.ring β), G₀.IsRegularTauFrame (Sq.ideal β) ∧
      Sq.IsStrictFrame F e β G₀ := by
    rcases Nat.eq_zero_or_pos β with rfl | hpos
    · refine ⟨F.transport e, ?_, MonoidalSequence.IsStrictFrame.zero Sq F e⟩
      rw [h0]
      exact F.isRegularTauFrame_transport e J ht1 hF.1
    · obtain ⟨G₀, hG₀, hfr⟩ := hF.2.2 Sq e h0 hperm hsep β hpos (hmono β hβ).1
        (hmono β hβ).2.1 (hmono β hβ).2.2
      obtain ⟨c, hc⟩ := hfr
      subst hc
      exact ⟨c.frame β, hG₀, MonoidalSequence.FrameTransformAlong.isStrictTransformElem_frame
        F J hF.2.1 Sq e h0 hperm hsep β (hmono β hβ).1 (hmono β hβ).2.2 c β le_rfl⟩
  obtain ⟨G₀, hG₀, hr₀, hz₀⟩ := key
  obtain ⟨hr, hz⟩ := hG
  have hr' : G.r = G₀.r := hr.trans hr₀.symm
  choose u hu using fun j : Fin G.r =>
    MonoidalSequence.IsStrictTransformElem.unique Sq (hz₀ (Fin.cast hr' j)) (hz j)
  exact RegularFrame.isRegularTauFrame_of_associated G₀ G (Sq.ideal β) hr' u hu hG₀

end ChainInduction

section ChainInduction2

variable {R : Type u} [CommRing R] [IsRegularLocalRing R] [IsDomain R]

omit [IsDomain R] in
/-- The invariant of the induction along the sequence in the proof of Theorem 8: `G` is a regular
frame of `R_β` whose members are strict transforms of the members of `F` and `g` is a normalized
standard base of `J_β` with respect to `G` consisting of strict transforms of the members of the
normalized standard base `f` of `J`. -/
def MonoidalSequence.IsNormalizedStage (Sq : MonoidalSequence.{u}) (F : RegularFrame R)
    (e : R ≃+* Sq.ring 0) {m : ℕ} (f : Fin m → R) (β : ℕ) (G : RegularFrame (Sq.ring β))
    (g : Fin m → Sq.ring β) : Prop :=
  Sq.IsStrictFrame F e β G ∧ (∀ j, Sq.IsStrictTransformElem e (f j) β (g j)) ∧
    G.IsNormalizedStandardBase (Sq.ideal β) g

omit [IsDomain R] in
/-- **One step of the induction along the sequence in the proof of Theorem 8** (p. 264).  The
paper proves the case of one monoidal transform "with center `P`" and a frame transform
`(S₁; w₁, …, w_τ)` of `(S; z₁, …, z_τ)` "in `R₁` with denominator `x ∈ P ∩ S`", and applies it
along the sequence; here the step from `R_β` to `R_{β+1}` is made for the frame `G` of `R_β` (a
`J_β`-stable `τ`-frame in the sense of the paper only through the facts that its members are strict
transforms of the `z_j` and that it is a regular `τ`-frame for `J_β`, both of which are used).
Nontrivial center: `isNormalizedStandardBase_strictTransform_of_isRegularTauFrame` (the printed
one-step argument), with `ν_{P_β}(g_j) = ν_j` by Theorem 6; trivial center `R_β`: the canonical
frame transform with denominator `1`.  The `τ`-frame hypotheses on the stage frame and on the new
frame come from Definition 12 (`MonoidalSequence.IsStrictFrame.isRegularTauFrame`). -/
theorem exists_isNormalizedStage_succ [Hironaka.HironakaCitedResults.{u}] {F : RegularFrame R} {J : Ideal R}
    (hF : F.IsJStableTauFrame J) (ht1 : 1 ≤ t R J) {Sq : MonoidalSequence.{u}}
    {e : R ≃+* Sq.ring 0} (h0 : Sq.ideal 0 = J.map e) (hperm : Sq.IsPermissible)
    (hsep : Sq.IsResiduallySeparableAlgebraic) {αb : ℕ}
    (hnu : nuStar (Sq.ring αb) (Sq.ideal αb) = nuStar R J)
    (htau : ∀ a, 1 ≤ a → a ≤ t R J → tau (Sq.ring αb) (Sq.ideal αb) a = tau R J a)
    {m : ℕ} {f : Fin m → R} {β : ℕ} (hβ : β < αb) {G : RegularFrame (Sq.ring β)}
    {g : Fin m → Sq.ring β} (hst : Sq.IsNormalizedStage F e f β G g) :
    ∃ (G' : RegularFrame (Sq.ring (β + 1))) (g' : Fin m → Sq.ring (β + 1)),
      Sq.IsNormalizedStage F e f (β + 1) G' g' := by
  classical
  have hmono := MonoidalSequence.nuStar_t_tau_eq_of_le J Sq e h0 hperm hsep αb hnu htau
  have hreg := hperm.hasRegularCenters
  obtain ⟨hGs, hgs, hnorm⟩ := hst
  by_cases hc : Sq.center β = ⊤
  · -- the trivial monoidal transform with center `R_β`
    refine ⟨RegularFrame.transport
      (RegularFrame.topFrameTransform G hc (Sq.transform β)).toRegularFrame (Sq.equiv β),
      fun j => Sq.equiv β ((Sq.transform β).toRing (g j)),
      MonoidalSequence.IsStrictFrame.transport_frameTransform hF.2.1 h0 hperm hsep hnu htau hβ hGs
        _, fun j => Sq.isStrictTransformElem_succ_of_center_eq_top e (hgs j) hc, ?_⟩
    rw [Sq.ideal_succ β]
    exact RegularFrame.isNormalizedStandardBase_transport _ (Sq.equiv β) _ _
      (RegularFrame.isNormalizedStandardBase_topFrameTransform G hc (Sq.transform β)
        (Sq.ideal β) g hnorm)
  · obtain ⟨hQ, hS⟩ := ((hreg β).2).resolve_left hc
    obtain ⟨-, hJQ, -, -⟩ := (hperm β).resolve_left hc
    have : (Sq.center β).IsPrime := hQ
    have : IsRegularLocalRing (Sq.ring β ⧸ Sq.center β) := hS
    set T := Sq.transform β with hT
    set I' := strictTransformIdeal T (Sq.ideal β) with hI'
    have hzQ : G.idealZ ≤ Sq.center β :=
      MonoidalSequence.IsStrictFrame.idealZ_le_center hF.2.1 h0 hperm hsep hnu htau hβ.le hGs hc
    obtain ⟨FT, x, hxQ, hFTx⟩ := MonoidalSequence.IsStrictFrame.exists_isDenominatorInCenter
      hF.2.1 h0 hperm hsep hnu htau hβ hGs
    have hx : (Sq.center β).map T.toRing =
        Ideal.span {T.toRing (algebraMap G.S (Sq.ring β) x)} := by
      rw [← hFTx]
      exact FT.span_x.symm
    -- the invariants at the stages `β` and `β + 1`
    have hmapβ : nuStar (Sq.ring (β + 1)) (Sq.ideal (β + 1)) = nuStar T.ring I' ∧
        t (Sq.ring (β + 1)) (Sq.ideal (β + 1)) = t T.ring I' ∧
        ∀ i, 1 ≤ i → i ≤ t T.ring I' →
          tau (Sq.ring (β + 1)) (Sq.ideal (β + 1)) i = tau T.ring I' i := by
      rw [Sq.ideal_succ β]
      exact nuStar_t_tau_map_of_bijective_aux (Sq.equiv β : T.ring →+* Sq.ring (β + 1))
        (Sq.equiv β).bijective I'
    obtain ⟨hnuβ, htβ, hτβ⟩ := hmono β hβ.le
    obtain ⟨hnuβ1, htβ1, hτβ1⟩ := hmono (β + 1) hβ
    have hnuT : nuStar T.ring I' = nuStar (Sq.ring β) (Sq.ideal β) :=
      hmapβ.1.symm.trans (hnuβ1.trans hnuβ.symm)
    have htT : t T.ring I' = t R J := hmapβ.2.1.symm.trans htβ1
    have htauT : ∀ a, 1 ≤ a → a ≤ t (Sq.ring β) (Sq.ideal β) →
        tau T.ring I' a = tau (Sq.ring β) (Sq.ideal β) a := fun a ha hat => by
      rw [htβ] at hat
      rw [← hmapβ.2.2 a ha (htT ▸ hat), hτβ1 a ha hat, hτβ a ha hat]
    -- the new frame is a regular `τ`-frame
    have hG's : Sq.IsStrictFrame F e (β + 1) (RegularFrame.transport FT.toRegularFrame
        (Sq.equiv β)) :=
      MonoidalSequence.IsStrictFrame.transport_frameTransform hF.2.1 h0 hperm hsep hnu htau hβ
        hGs FT
    have hτ1 : FT.toRegularFrame.IsRegularTauFrame I' := by
      refine RegularFrame.isRegularTauFrame_of_transport FT.toRegularFrame (Sq.equiv β) I'
        (htT ▸ ht1) ?_
      have := MonoidalSequence.IsStrictFrame.isRegularTauFrame hF ht1 h0 hperm hsep hnu htau
        hβ hG's
      rwa [Sq.ideal_succ β] at this
    -- `ν_{P_β}(g_j) = ν^{(j)}(J_β)` by Theorem 6
    have hJ : Sq.ideal β ≠ ⊤ := fun h => hQ.ne_top (top_le_iff.mp (h ▸ hJQ))
    have hfQ := (isPermissibleCenter_iff_ordElem_eq_nuI G (Sq.ideal β) hJ g hnorm
      (Sq.center β) hS hzQ).mp (hperm β)
    have hordM : ∀ j, Ideal.ordElem (maximalIdeal (Sq.ring β)) (g j) =
        nuI (Sq.ring β) (Sq.ideal β) (j : ℕ).succPNat := fun j =>
      ordElem_eq_nuI_of_isStandardBase (Sq.ideal β) g hnorm.1 j
    set ν : Fin m → ℕ := fun j => (nuI (Sq.ring β) (Sq.ideal β) (j : ℕ).succPNat).toNat with hν
    have hνfin : ∀ j, (ν j : ℕ∞) = nuI (Sq.ring β) (Sq.ideal β) (j : ℕ).succPNat := fun j => by
      obtain ⟨n, hn⟩ := hnorm.1.exists_ordElem_eq_natCast j
      rw [hordM j] at hn
      simp only [hν, hn, ENat.toNat_natCast]
    have hgQ : ∀ j, g j ∈ Sq.center β ^ ν j := fun j =>
      Ideal.mem_pow_of_ordElem ((hfQ j).trans (hνfin j).symm)
    choose w hw using fun j => MonoidalSequence.exists_mul_pow_eq_toRing_aux T
      (x := algebraMap G.S (Sq.ring β) x) hx.symm (hgQ j)
    have hGτ : G.IsRegularTauFrame (Sq.ideal β) :=
      MonoidalSequence.IsStrictFrame.isRegularTauFrame hF ht1 h0 hperm hsep hnu htau hβ.le hGs
    obtain ⟨hnormT, -⟩ := isNormalizedStandardBase_strictTransform_of_isRegularTauFrame
      (Sq.ideal β) G hGτ (Sq.center β) (hperm β) hzQ T (hsep β) x hxQ hx FT hFTx
      hnuT htauT hτ1 g hnorm hfQ ν hνfin w hw
    refine ⟨RegularFrame.transport FT.toRegularFrame (Sq.equiv β),
      fun j => Sq.equiv β (w j), hG's, fun j => ?_, ?_⟩
    · refine Sq.isStrictTransformElem_succ_of_center_ne_top e hreg (hgs j) hc (ν := ν j)
        ((hfQ j).trans (hνfin j).symm) (x := T.toRing (algebraMap G.S (Sq.ring β) x)) hx.symm
        (w := w j) (hw j)
    · rw [Sq.ideal_succ β]
      exact RegularFrame.isNormalizedStandardBase_transport _ (Sq.equiv β) _ _ hnormT

end ChainInduction2

section ChainInduction3

variable {R : Type u} [CommRing R] [IsRegularLocalRing R]

/-- **The induction along the sequence in the proof of Theorem 8** (p. 264).  For a `J`-stable
regular `τ`-frame `F` of `R` for `J`, a normalized standard base `f` of `J` with respect to `F` and
a permissible residually separable algebraic sequence along which `ν*` and the `τ^{(a)}` are
unchanged up to `ᾱ`, there are, for every `β ≤ ᾱ`, a regular frame `G` of `R_β` and a normalized
standard base `g` of `J_β` with respect to `G` which consists of strict transforms of the `f_j`
(and `G` consists of strict transforms of the `z_j`).  The paper treats one monoidal transform and
applies the result along the sequence tacitly. -/
theorem exists_isNormalizedStage_of_le [Hironaka.HironakaCitedResults.{u}] {F : RegularFrame R} {J : Ideal R}
    (hF : F.IsJStableTauFrame J) (ht1 : 1 ≤ t R J) {Sq : MonoidalSequence.{u}}
    {e : R ≃+* Sq.ring 0} (h0 : Sq.ideal 0 = J.map e) (hperm : Sq.IsPermissible)
    (hsep : Sq.IsResiduallySeparableAlgebraic) {αb : ℕ}
    (hnu : nuStar (Sq.ring αb) (Sq.ideal αb) = nuStar R J)
    (htau : ∀ a, 1 ≤ a → a ≤ t R J → tau (Sq.ring αb) (Sq.ideal αb) a = tau R J a)
    {m : ℕ} {f : Fin m → R} (hf : F.IsNormalizedStandardBase J f) :
    ∀ β ≤ αb, ∃ (G : RegularFrame (Sq.ring β)) (g : Fin m → Sq.ring β),
      Sq.IsNormalizedStage F e f β G g := by
  intro β
  induction β with
  | zero =>
    intro _
    refine ⟨F.transport e, fun j => e (f j), MonoidalSequence.IsStrictFrame.zero Sq F e,
      fun j => rfl, ?_⟩
    rw [h0]
    exact RegularFrame.isNormalizedStandardBase_transport F e J f hf
  | succ β ih =>
    intro hβ
    obtain ⟨G, g, hst⟩ := ih (by omega)
    exact exists_isNormalizedStage_succ hF ht1 h0 hperm hsep hnu htau (by omega) hst

end ChainInduction3

section Theorem8Final

variable {R : Type u} [CommRing R] [IsRegularLocalRing R]

/-- Theorem 8, p. 264: "Let `R` be a regular local ring, `J` an ideal in `R`, and
`(S; z₁, …, z_τ)` a `J`-stable regular `τ`-frame of `R` for `J`. Then every normalized standard base
of `J` with respect to `(S; z₁, …, z_τ)` is `J`-stable."

Proved along the printed route.  The printed proof treats one monoidal transform of `R` and
proves that the `g_j = x^{-ν_j} f_j` form a normalized standard base of `J₁` with respect to the
frame transform `(S₁; w₁, …, w_τ)` (the one-step theorem
`isNormalizedStandardBase_strictTransform_of_isRegularTauFrame`,
`Hironaka/Compat/NormalizedStrictTransform.lean`): "we may assume that `R` is complete with respect
to the topology defined by the powers of `(z₁, …, z_τ)R`, so that `R = S{z₁, …, z_τ}`" (the base
change of §8 for the identity of `S`), then the partial frames `(S^{(a)}; z₁, …, z_{τ_a})`,
`S^{(a)} = S{z_{τ_a+1}, …, z_τ}` (`RegularFrame.partialFrame`), their frame transforms
`(S^{(a)}₁; w₁, …, w_{τ_a})` with the denominator `x`, and the induction on `a` (`1 ≤ a ≤ t`) with
Lemma 20 for `S^{(a)}` and Lemma 19 for `S^{(a)}₁`
(`isNormalizedStandardBase_strictTransform_of_mvPowerSeries`,
`Hironaka/Compat/NormalizedStrictTransformComplete.lean`).  Gaps filled (the paper's words are
quoted):
(1) "It is sufficient to show that `(g₁, …, g_m)` is a normalized standard base of `J₁` with
respect to `(S₁; w₁, …, w_τ)`": the paper does not say how `J`-stability (Definition 11), a
statement about sequences, follows.  Induction along the sequence
(`exists_isNormalizedStage_of_le`, `exists_isNormalizedStage_succ`): at each stage `β < ᾱ` the
one-step result is applied to the stage frame (whose members are strict transforms of the `z_j`,
`MonoidalSequence.IsStrictFrame`) and the stage normalized standard base (strict transforms of the
`f_j`); at `ᾱ`, `ν_{M_ᾱ}(f_ᾱ) = ν^{(j)}(J_ᾱ) = ν^{(j)}(J)` since the `g_j` form a standard base of
`J_ᾱ` and `ν*(J_ᾱ) = ν*(J)`, and `ν_{P_ᾱ}(f_ᾱ) = ν^{(j)}(J)` by Theorem 6 for `J_ᾱ`, since
`(w)R_ᾱ ⊆ P_ᾱ` (`ν_{P_ᾱ}(w_j) = 1` as `(z)` is `J`-stable).
(2) "Let `(S₁; w₁, …, w_τ)` be a frame transform of `(S; z₁, …, z_τ)` in `R₁` with denominator
`x ∈ P ∩ S`": the existence at every stage is the second assertion of Remark 3
(`MonoidalSequence.IsStrictFrame.exists_isDenominatorInCenter`); for a trivial transform (center
`R_β`, by which finite sequences are continued) the frame transform with denominator `1`
(`RegularFrame.topFrameTransform`, `RegularFrame.isNormalizedStandardBase_topFrameTransform`).
(3) The one-step result needs the stage frame and the frame transform to be regular `τ`-frames
(Theorem 7 and Lemma 19); Definition 12 gives regular `τ`-frames of `R_β` for `J_β` which are frame
transforms of `(S; z)` along the sequence, whose members, like those of the chain frames, are strict
transforms of the `z_j`, hence differ by units; being a regular `τ`-frame depends only on the members
up to units (`RegularFrame.isRegularTauFrame_of_associated`,
`MonoidalSequence.IsStrictFrame.isRegularTauFrame`).
(4) "we may assume that `R` is complete": the paper does not carry out the reduction; the
hypotheses are verified for `R̃ = S⟦z⟧`, the canonical lift `R̃₁` of `R₁` and the lifted frame
transform, and the conclusions descend to `R₁` (normalization through the canonical map
`S₁ → S̃₁`, as for Lemma 20).  The existence of `(S^{(a)}₁; w₁, …, w_{τ_a})` with the same
denominator `x` is not argued (`RegularFrame.exists_partialFrame_frameTransform`).
(5) The printed induction: "The first two assertions are clear for `a = 1`" (Lemma 20 for `S^{(1)}`
with the empty system and Lemma 19 for `S^{(1)}₁`); "This lemma also shows that
`(g₁, …, g_{m_{a+1}})` can be extended to a standard base of `J₁`" (Lemma 20 for `S^{(a)}` gives this
only for `(g₁, …, g_{m_a}, g_j)`, one `j` at a time; Lean applies Lemma 20 for `S^{(t)} = S` to
`g_{m_{a+1}}` and all its predecessors, after the second assertion for `a + 1`); "Thus … `(g₁, …,
g_m)` is a normalized standard base of `J₁`" (the induction gives normalization only by the earlier
blocks and only with respect to the partial frames `S^{(a)}₁`; the normalization of `g_j` by all
its predecessors with respect to `(S₁; w)` is Lemma 20 for `S^{(t)} = S`; the normalizations with
respect to different `S^{(a)}₁` need not be compared).
-/
@[blueprint "thm:III.8"
  (statement := /-- Let $R$ be a regular local ring, $J$ an ideal in $R$, and
    $(S;z_1,\dots,z_\tau)$ a $J$-stable regular $\tau$-frame of $R$ for $J$ (\cref{def:III.12}).
    Then every normalized standard base of $J$ with respect to $(S;z_1,\dots,z_\tau)$
    (\cref{def:III.9-normalized-standard-base}) is $J$-stable (\cref{def:III.11}).
    (Theorem 8, p.~264.) -/)
  (proof := /-- Let $P$ be a prime ideal in $R$ which is a permissible center for $J$. Let $R_1$
    be a monoidal transform of $R$ with center $P$ which is residually separable algebraic over
    $R$, and $J_1$ the strict transform of $J$ in $R_1$. Assume that $\nu^*(J_1)=\nu^*(J)$, and
    $\tau^*(J_1)=\tau^*(J)$. Let $(S_1;w_1,\dots,w_\tau)$ be a frame transform of
    $(S;z_1,\dots,z_\tau)$ in $R_1$ with denominator $x\in P\cap S$ (such that $(x)R_1=PR_1$)
    (\cref{def:III.8-frame-transform}). Let $(f_1,\dots,f_m)$ be a normalized standard base of
    $J$ with respect to $(S;z_1,\dots,z_\tau)$. Let $\nu_j=\nu^{(j)}(J)$ for $1\le j\le m$, and
    $g_j=x^{-\nu_j}f_j$ for $1\le j\le m$. It is sufficient to show that $(g_1,\dots,g_m)$ is a
    normalized standard base of $J_1$ with respect to $(S_1;w_1,\dots,w_\tau)$. First of all, by
    Theorem~6 of \S7 (\cref{thm:III.6}), $\nu_P(f_j)=\nu_j$ for all $j$ ($1\le j\le m$), so that
    $g_j\in J_1$ for $1\le j\le m$. To prove that $(g_1,\dots,g_m)$ is a normalized standard base
    of $J_1$, we may assume that $R$ is complete with respect to the topology defined by the
    powers of $(z_1,\dots,z_\tau)R$, so that $R=S\{z_1,\dots,z_\tau\}$. Let $t=t(J)$, so that
    $\tau=\tau^{(t)}(J)$. Let $\tau_a=\tau^{(a)}(J)$ for $1\le a\le t$. Let $m_a$ = the maximal
    integer such that $\nu^{(m_a)}(J)=\mu^{(a)}(J)$ for $1\le a\le t$. Let
    $S^{(a)}=S\{z_{\tau_a+1},\dots,z_\tau\}$. Let $(S^{(a)}_1;w_1,\dots,w_{\tau_a})$ be the frame
    transform of $(S^{(a)};z_1,\dots,z_{\tau_a})$ in $R_1$ with the denominator $x$. We shall
    prove, by induction on $a$ ($1\le a\le t$), that $(g_1,\dots,g_{m_a})$ can be extend [sic]
    to a standard base of $J_1$, that $\tau_{(w)_a}(g_1,\dots,g_{m_a})=0$ where
    $(w)_a=(w_1,\dots,w_{\tau_a})$, and that $g_{m_a+1},\dots,g_{m_{a+1}}$ are all normalized by
    $(g_1,\dots,g_{m_a})$ with respect to $(S^{(a)}_1;w_1,\dots,w_{\tau_a})$. The first two
    assertions are clear for $a=1$. For an arbitrary $a\ge1$, the last assertion follows from
    the first two by Lemma~20 of \S8 (\cref{lem:III.20}). This lemma also shows that
    $(g_1,\dots,g_{m_{a+1}})$ can be extended to a standard base of $J_1$, i.e., the first
    assertion for $a$ increased by $1$. Then the second assertion for $a$ increased by $1$
    follows by virtue of Lemma~19 of \S7 (\cref{lem:III.19}). Thus
    $\tau_{(w)}(g_1,\dots,g_m)=0$ for $(w)=(w_1,\dots,w_\tau)$, and $(g_1,\dots,g_m)$ is a
    normalized standard base of $J_1$. \qed

    \textbf{Gap fills} (the paper's words are quoted). The printed proof treats one monoidal
    transform; the formalization of this part is the one-step theorem, proved as printed: the
    reduction to $R=S\{z_1,\dots,z_\tau\}$ by the base change of \S8 for the identity of $S$ (as in
    the proofs of Lemma~18 and Lemma~20, \cref{lem:III.18}, \cref{lem:III.20}), the partial frames
    $(S^{(a)};z_1,\dots,z_{\tau_a})$ of $S\{z\}$ with their frame transforms
    $(S^{(a)}_1;w_1,\dots,w_{\tau_a})$ with the denominator $x$ (\cref{def:III.8-frame-transform}),
    and the induction on $a$ with Lemma~20 for $S^{(a)}$ and Lemma~19 for $S^{(a)}_1$; the
    hypothesis~(2) of Lemma~20 for $S^{(a)}$, $\tau_{(z)_a}(f_1,\dots,f_{m_a})=0$, is Theorem~7
    (\cref{thm:III.7}), and hypothesis~(3) is obtained, as in the proof of Theorem~7, by Remarks~1
    and~2 of \S7 (\cref{rem:III.7-1}, \cref{rem:III.7-2}). (1) ``It is sufficient to show that
    $(g_1,\dots,g_m)$ is a normalized standard base of $J_1$ with respect to
    $(S_1;w_1,\dots,w_\tau)$'': the paper does not say how $J$-stability (Definition~11), a
    statement about sequences, follows. By induction along the sequence, applying the one-step
    result at each stage $\beta<\bar\alpha$ to the stage frame (whose members are strict
    transforms of the $z_j$; \cref{def:III.12} and \cref{rem:III.9-3}) and the stage normalized
    standard base (the strict transforms of the $f_j$, i.e.\ the $x^{-\nu_j}$-multiples), one
    obtains at $\bar\alpha$ a normalized standard base $(g_j)$ of $J_{\bar\alpha}$ with respect to
    a regular $\tau$-frame of $R_{\bar\alpha}$; then
    $\nu_{M_{\bar\alpha}}(f_{\bar\alpha})=\nu^{(j)}(J_{\bar\alpha})=\nu^{(j)}(J)$ because $(g_j)$ is
    a standard base of $J_{\bar\alpha}$ and $\nu^*(J_{\bar\alpha})=\nu^*(J)$, and
    $\nu_{P_{\bar\alpha}}(f_{\bar\alpha})=\nu^{(j)}(J)$ by Theorem~6 for $J_{\bar\alpha}$, since
    $(w)R_{\bar\alpha}\subseteq P_{\bar\alpha}$ ($\nu_{P_{\bar\alpha}}(w_j)=1$ because the system
    $(z)$ is $J$-stable). (2) ``Let $(S_1;w_1,\dots,w_\tau)$ be a frame transform of
    $(S;z_1,\dots,z_\tau)$ in $R_1$ with denominator $x\in P\cap S$'': the existence of such a
    frame transform at every stage is the second assertion of Remark~3 (\cref{rem:III.9-3}); for a
    trivial transform (center $R_\beta$, by which finite sequences are continued) the frame
    transform with denominator $1$ is used. (3) The $\tau$-frame property of the stage frame and
    of the frame transform (Theorem~7, Lemma~19): \cref{def:III.12} gives regular $\tau$-frames
    which are frame transforms of $(S;z)$ along the sequence; their members and those of the
    chain frames are strict transforms of the $z_j$, hence differ by units, and being a regular
    $\tau$-frame depends on the members only up to units. (4) ``we may assume that $R$ is
    complete'': the hypotheses hold for $\tilde R=S\{z\}$, the canonical lift $\tilde R_1$ of
    $R_1$ and the lifted frame transform, and the conclusions descend to $R_1$ (normalization
    through the canonical map $S_1\to\tilde S_1$, as for Lemma~20); the existence of
    $(S^{(a)}_1;w_1,\dots,w_{\tau_a})$ with the same denominator $x$ is not argued in the paper.
    (5) ``The first two assertions are clear for $a=1$'': Lemma~20 for $S^{(1)}$ with the empty
    system and Lemma~19 for $S^{(1)}_1$. ``This lemma also shows that $(g_1,\dots,g_{m_{a+1}})$ can be
    extended to a standard base of $J_1$'': Lemma~20 for $S^{(a)}$ gives this only for
    $(g_1,\dots,g_{m_a},g_j)$, one $j$ at a time; it is Lemma~20 for $S^{(t)}=S$ applied to
    $g_{m_{a+1}}$ and all its predecessors (the second assertion for $a+1$ gives its hypothesis
    (8)). ``Thus \dots\ $(g_1,\dots,g_m)$ is a normalized standard base of $J_1$'': the induction
    gives normalization only by the earlier blocks and only with respect to the partial frames
    $S^{(a)}_1$; the normalization of every $g_j$ by all its predecessors with respect to
    $(S_1;w)$ is again Lemma~20 for $S^{(t)}=S$, so the normalizations with respect to different
    $S^{(a)}_1$ need not be compared. -/)
  (latexEnv := "theorem")]
theorem isJStableSystem_of_isNormalizedStandardBase [Hironaka.HironakaCitedResults.{u}] (J : Ideal R) (F : RegularFrame R)
    (hF : F.IsJStableTauFrame J) {m : ℕ} (f : Fin m → R)
    (hf : F.IsNormalizedStandardBase J f) : IsJStableSystem J f := by
  classical
  intro j Sq e h0 hperm hsep αb hnu _ htau fα hfα
  have ht1 : 1 ≤ t R J := one_le_t_of_isStandardBase hf.1 (Nat.pos_of_ne_zero fun h => by
    subst h
    exact j.elim0)
  obtain ⟨G, g, hGs, hgs, hnorm⟩ :=
    exists_isNormalizedStage_of_le hF ht1 h0 hperm hsep hnu htau hf αb le_rfl
  obtain ⟨u, hu⟩ := MonoidalSequence.IsStrictTransformElem.unique Sq (hgs j) hfα
  have hnuI : nuI (Sq.ring αb) (Sq.ideal αb) (j : ℕ).succPNat = nuI R J (j : ℕ).succPNat :=
    congrFun (toLex.injective hnu) _
  refine ⟨?_, fun hc => ?_⟩
  · rw [hu, Ideal.ordElem_isUnit_mul _ u.isUnit,
      ordElem_eq_nuI_of_isStandardBase (Sq.ideal αb) g hnorm.1 j, hnuI,
      ← ordElem_eq_nuI_of_isStandardBase J f hf.1 j]
  · obtain ⟨hQ, hS⟩ := ((hperm.hasRegularCenters αb).2).resolve_left hc
    obtain ⟨-, hJQ, -, -⟩ := (hperm αb).resolve_left hc
    have hJ : Sq.ideal αb ≠ ⊤ := fun h => hQ.ne_top (top_le_iff.mp (h ▸ hJQ))
    have hzQ : G.idealZ ≤ Sq.center αb :=
      MonoidalSequence.IsStrictFrame.idealZ_le_center hF.2.1 h0 hperm hsep hnu htau le_rfl hGs hc
    have h6 := (isPermissibleCenter_iff_ordElem_eq_nuI G (Sq.ideal αb) hJ g hnorm
      (Sq.center αb) hS hzQ).mp (hperm αb) j
    rw [hu, Ideal.ordElem_isUnit_mul _ u.isUnit, h6, hnuI,
      ← ordElem_eq_nuI_of_isStandardBase J f hf.1 j]

end Theorem8Final

end Hironaka
