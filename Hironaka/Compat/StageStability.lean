/-
Copyright (c) 2026 Daattavya Aggarwal, Minhyong Kim, Oisin Kim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daattavya Aggarwal, Minhyong Kim, Oisin Kim
-/
module

public import Hironaka.Ch3.JStability
public import Hironaka.Compat.TauZBaseChange
public import Hironaka.Statements

/-!
# Stability along the stages of a sequence: the transitivity "easily seen" in the proof of Lemma 25

In the proof of Lemma 25 (p. 271) the paper reduces the lemma to the facts (a), (b), (c) of its
reformulation, for one monoidal transform at a time, and says: "One can easily see that, if we
prove these facts, then the proof of the lemma is completed."  To apply the facts at the stage
`R_β` of a sequence `{(R_α, P_{α-1})}` one needs their hypotheses (1) "`(z^{(β)})` is `J_β`-stable"
and (2) "`f_β` is `(J_β, τ_{(z^{(β)})})`-stable" for the strict transforms `z_j^{(β)}`, `f_β` of
`z_j`, `f` at `R_β`: the paper uses this implicitly.  This file proves it for one step
`R_β → R_{β+1}` (`IsJStable.succ_stage`, `IsJTauZStable.succ_stage`): if `z` is `J_β`-stable in
`R_β` and `z₁` is its strict transform in `R_{β+1}` then `z₁` is `J_{β+1}`-stable; the same for
`(J; τ_{(z)})`-stability.  The proof prefixes the first step `R_β → R_{β+1}` to an arbitrary
sequence of `R_{β+1}` (`MonoidalSequence.prependStep`), which is a sequence of `R_β`, with
`ν*`, `t`, `τ^{(a)}` unchanged by the monotonicity along the sequence.  The transport of stability
along a ring isomorphism (`IsJStable.transport`, `IsJTauZStable.transport`) gives the
stage `0` (`R ≅ R₀`).
-/

@[expose] public section

open IsLocalRing

namespace Hironaka

universe u

namespace MonoidalSequence

section Cons

/-- The rings of `prependStep`: `A, R'₀, R'₁, …`. -/
@[reducible] def PrependStep.ring (A : Type u) (S' : MonoidalSequence.{u}) : ℕ → Type u
  | 0 => A
  | n + 1 => S'.ring n

noncomputable instance (A : Type u) [CommRing A] (S' : MonoidalSequence.{u}) (n : ℕ) :
    CommRing (PrependStep.ring A S' n) :=
  match n with
  | 0 => inferInstanceAs (CommRing A)
  | n + 1 => inferInstanceAs (CommRing (S'.ring n))

noncomputable instance (A : Type u) [CommRing A] [IsRegularLocalRing A] (S' : MonoidalSequence.{u})
    (n : ℕ) : IsRegularLocalRing (PrependStep.ring A S' n) :=
  match n with
  | 0 => inferInstanceAs (IsRegularLocalRing A)
  | n + 1 => inferInstanceAs (IsRegularLocalRing (S'.ring n))

noncomputable instance (A : Type u) [CommRing A] [IsDomain A] (S' : MonoidalSequence.{u})
    (n : ℕ) : IsDomain (PrependStep.ring A S' n) :=
  match n with
  | 0 => inferInstanceAs (IsDomain A)
  | n + 1 => inferInstanceAs (IsDomain (S'.ring n))

variable {A : Type u} [CommRing A] [IsRegularLocalRing A] [IsDomain A] {P : Ideal A}

/-- The centers of `prependStep`: `P, P'₀, P'₁, …`. -/
noncomputable def PrependStep.center (_T0 : MonoidalTransform A P) (S' : MonoidalSequence.{u}) :
    ∀ n, Ideal (PrependStep.ring A S' n)
  | 0 => P
  | n + 1 => S'.center n

/-- The transforms of `prependStep`: `T0, T'₀, T'₁, …`. -/
noncomputable def PrependStep.transform (T0 : MonoidalTransform A P) (S' : MonoidalSequence.{u}) :
    ∀ n, MonoidalTransform (PrependStep.ring A S' n) (PrependStep.center T0 S' n)
  | 0 => T0
  | n + 1 => S'.transform n

/-- The identifications of the transforms of `prependStep` with the next rings. -/
noncomputable def PrependStep.equiv (T0 : MonoidalTransform A P) [IsRegularLocalRing T0.ring]
    (S' : MonoidalSequence.{u}) (e0 : T0.ring ≃+* S'.ring 0) :
    ∀ n, (PrependStep.transform T0 S' n).ring ≃+* PrependStep.ring A S' (n + 1)
  | 0 => e0
  | n + 1 => S'.equiv n

noncomputable instance (T0 : MonoidalTransform A P) (S' : MonoidalSequence.{u}) (n : ℕ) :
    IsLocalHom (PrependStep.transform T0 S' n).toRing :=
  MonoidalTransform.isLocalHom_toRing _

/-- The ideals of `prependStep`: `I, J'₀, J'₁, …`. -/
def PrependStep.ideal (S' : MonoidalSequence.{u}) (I : Ideal A) :
    ∀ n, Ideal (PrependStep.ring A S' n)
  | 0 => I
  | n + 1 => S'.ideal n

/-- The sequence `R, R'₀, R'₁, …` obtained by putting one monoidal transform `T0` of `R` (with
center `P`) in front of the sequence `S'` whose first ring is identified with `T0.ring` by `e0`;
the ideal of `S'` at the index `0` must be the strict transform of `I`. -/
noncomputable def prependStep (T0 : MonoidalTransform A P) [IsRegularLocalRing T0.ring]
    (S' : MonoidalSequence.{u}) (e0 : T0.ring ≃+* S'.ring 0) (I : Ideal A)
    (hI : S'.ideal 0 = (strictTransformIdeal T0 I).map e0) :
    MonoidalSequence.{u} where
  ring := PrependStep.ring A S'
  ideal := PrependStep.ideal S' I
  center := PrependStep.center T0 S'
  transform := PrependStep.transform T0 S'
  equiv := PrependStep.equiv T0 S' e0
  ideal_succ := fun n => match n with
    | 0 => hI
    | n + 1 => S'.ideal_succ n

/-- The strict transforms along `prependStep` are those along `S'` of the strict transform of the
first step. -/
theorem strictAlong_prependStep (T0 : MonoidalTransform A P) [IsRegularLocalRing T0.ring]
    (S' : MonoidalSequence.{u}) (e0 : T0.ring ≃+* S'.ring 0) (I : Ideal A)
    (hI : S'.ideal 0 = (strictTransformIdeal T0 I).map e0) (J : Ideal A) (n : ℕ) :
    (prependStep T0 S' e0 I hI).strictAlong J (n + 1) =
      S'.strictAlong ((strictTransformIdeal T0 J).map e0) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    show (strictTransformIdeal (S'.transform n)
      ((prependStep T0 S' e0 I hI).strictAlong J (n + 1))).map (S'.equiv n) =
        (strictTransformIdeal (S'.transform n)
          (S'.strictAlong ((strictTransformIdeal T0 J).map e0) n)).map (S'.equiv n)
    rw [ih]

/-- `prependStep` is permissible when the first center is a permissible center and `S'` is
permissible. -/
theorem prependStep_isPermissible (T0 : MonoidalTransform A P) [IsRegularLocalRing T0.ring]
    (S' : MonoidalSequence.{u}) (e0 : T0.ring ≃+* S'.ring 0) (I : Ideal A)
    (hI : S'.ideal 0 = (strictTransformIdeal T0 I).map e0)
    (hP : IsPermissibleCenter A I P) (hS : S'.IsPermissible) :
    (prependStep T0 S' e0 I hI).IsPermissible := by
  intro n
  cases n with
  | zero => exact hP
  | succ n => exact hS n

/-- `prependStep` is residually separable algebraic when the first step and `S'` are. -/
theorem prependStep_isResiduallySeparableAlgebraic (T0 : MonoidalTransform A P)
    [IsRegularLocalRing T0.ring] (S' : MonoidalSequence.{u}) (e0 : T0.ring ≃+* S'.ring 0)
    (I : Ideal A) (hI : S'.ideal 0 = (strictTransformIdeal T0 I).map e0)
    (hT : RingHom.IsResiduallySeparableAlgebraic (R := A) (R' := T0.ring) T0.toRing)
    (hS : S'.IsResiduallySeparableAlgebraic) :
    (prependStep T0 S' e0 I hI).IsResiduallySeparableAlgebraic := by
  intro n
  cases n with
  | zero => exact hT
  | succ n => exact hS n

end Cons

section Stage

/-- The ideal of the first step of a sequence of `R_{β+1}` prefixed by the step `β`. -/
theorem stage_hI (Sq : MonoidalSequence.{u}) (β : ℕ) (T' : MonoidalSequence.{u})
    (e' : Sq.ring (β + 1) ≃+* T'.ring 0) (h0' : T'.ideal 0 = (Sq.ideal (β + 1)).map e') :
    T'.ideal 0 =
      (strictTransformIdeal (Sq.transform β) (Sq.ideal β)).map ((Sq.equiv β).trans e') := by
  rw [h0', Sq.ideal_succ β]
  exact Ideal.map_map (Sq.equiv β : (Sq.transform β).ring →+* Sq.ring (β + 1))
    (e' : Sq.ring (β + 1) →+* T'.ring 0)

/-- The regularity of the monoidal transform `R_β[x⁻¹P_β]` of a sequence (it is `R_{β+1}`). -/
local instance stageTransformIsRegularLocalRing (Sq : MonoidalSequence.{u}) (β : ℕ) :
    IsRegularLocalRing (Sq.transform β).ring :=
  IsRegularLocalRing.of_ringEquiv (Sq.equiv β).symm

/-- The sequence of `R_β` obtained by putting the step `R_β → R_{β+1}` of `Sq` in front of a
sequence `T'` of `R_{β+1}` (`e' : R_{β+1} ≅ R'_0`, `J'_0 = J_{β+1}R'_0`). -/
noncomputable def stageSeq (Sq : MonoidalSequence.{u}) (β : ℕ) (T' : MonoidalSequence.{u})
    (e' : Sq.ring (β + 1) ≃+* T'.ring 0) (h0' : T'.ideal 0 = (Sq.ideal (β + 1)).map e') :
    MonoidalSequence.{u} :=
  prependStep (Sq.transform β) T' ((Sq.equiv β).trans e') (Sq.ideal β) (stage_hI Sq β T' e' h0')

variable (Sq : MonoidalSequence.{u}) (β : ℕ) {T' : MonoidalSequence.{u}}
  {e' : Sq.ring (β + 1) ≃+* T'.ring 0} {h0' : T'.ideal 0 = (Sq.ideal (β + 1)).map e'}

theorem stageSeq_ideal_zero :
    (stageSeq Sq β T' e' h0').ideal 0 = (Sq.ideal β).map (RingEquiv.refl (Sq.ring β)) :=
  (Ideal.map_id _).symm

theorem stageSeq_isPermissible
    (hperm : IsPermissibleCenter (Sq.ring β) (Sq.ideal β) (Sq.center β))
    (hperm' : T'.IsPermissible) : (stageSeq Sq β T' e' h0').IsPermissible :=
  prependStep_isPermissible _ _ _ _ (stage_hI Sq β T' e' h0') hperm hperm'

theorem stageSeq_isResiduallySeparableAlgebraic
    (hsep : RingHom.IsResiduallySeparableAlgebraic (R := Sq.ring β) (R' := (Sq.transform β).ring)
      (Sq.transform β).toRing)
    (hsep' : T'.IsResiduallySeparableAlgebraic) :
    (stageSeq Sq β T' e' h0').IsResiduallySeparableAlgebraic :=
  prependStep_isResiduallySeparableAlgebraic _ _ _ _ (stage_hI Sq β T' e' h0') hsep hsep'

/-- A strict transform along `T'` of the strict transform `x₁` of `x` at `R_{β+1}` is a strict
transform of `x` along the sequence `stageSeq` (at the index shifted by one). -/
theorem stageSeq_isStrictTransformElem {x : Sq.ring β} {x₁ : Sq.ring (β + 1)}
    (hx₁ : Ideal.span {x₁} =
      (strictTransformIdeal (Sq.transform β) (Ideal.span {x})).map (Sq.equiv β))
    {n : ℕ} {g : T'.ring n} (hg : T'.IsStrictTransformElem e' x₁ n g) :
    (stageSeq Sq β T' e' h0').IsStrictTransformElem (RingEquiv.refl (Sq.ring β)) x (n + 1) g := by
  show Ideal.span {g} = (stageSeq Sq β T' e' h0').strictAlong
    (Ideal.span {(RingEquiv.refl (Sq.ring β)) x}) (n + 1)
  refine Eq.trans ?_ (strictAlong_prependStep (Sq.transform β) T' ((Sq.equiv β).trans e')
    (Sq.ideal β)
    (stage_hI Sq β T' e' h0') (Ideal.span {(RingEquiv.refl (Sq.ring β)) x}) n).symm
  rw [show Ideal.span {g} = T'.strictAlong (Ideal.span {e' x₁}) n from hg]
  congr 1
  rw [show Ideal.span {e' x₁} = (Ideal.span {x₁}).map e' by
    rw [Ideal.map_span, Set.image_singleton], hx₁]
  exact Ideal.map_map (Sq.equiv β : (Sq.transform β).ring →+* Sq.ring (β + 1))
    (e' : Sq.ring (β + 1) →+* T'.ring 0)

/-- One step of the strict transform of an element: if `g` and `g₂` are strict transforms of `x`
at the stages `β` and `β + 1` along the sequence, then `(g₂)` is the strict transform of `(g)` in
the monoidal transform `R_β → R_{β+1}`. -/
theorem isStrictTransformElem_oneStep {R : Type u} [CommRing R] (Sq : MonoidalSequence.{u})
    (e : R ≃+* Sq.ring 0) {x : R} {β : ℕ} {g : Sq.ring β} {g₂ : Sq.ring (β + 1)}
    (hg : Sq.IsStrictTransformElem e x β g) (hg₂ : Sq.IsStrictTransformElem e x (β + 1) g₂) :
    Ideal.span {g₂} =
      (strictTransformIdeal (Sq.transform β) (Ideal.span {g})).map (Sq.equiv β) := by
  refine (show Ideal.span {g₂} = _ from hg₂).trans ?_
  rw [MonoidalSequence.strictAlong, ← (show Ideal.span {g} = _ from hg)]

end Stage

end MonoidalSequence

section StageStability

open MonoidalSequence

/-- The conditions `ν*`, `t`, `τ^{(a)}` along a sequence `T'` of `R_{β+1}` relative to `J_{β+1}`
give those relative to `J_β` as soon as they agree at `β, β + 1`. -/
theorem stage_conditions (Sq : MonoidalSequence.{u}) (β : ℕ) (T' : MonoidalSequence.{u}) (α : ℕ)
    (hnu : nuStar (Sq.ring (β + 1)) (Sq.ideal (β + 1)) = nuStar (Sq.ring β) (Sq.ideal β))
    (ht : t (Sq.ring (β + 1)) (Sq.ideal (β + 1)) = t (Sq.ring β) (Sq.ideal β))
    (htau : ∀ a, 1 ≤ a → a ≤ t (Sq.ring β) (Sq.ideal β) →
      tau (Sq.ring (β + 1)) (Sq.ideal (β + 1)) a = tau (Sq.ring β) (Sq.ideal β) a)
    (hnu' : nuStar (T'.ring α) (T'.ideal α) = nuStar (Sq.ring (β + 1)) (Sq.ideal (β + 1)))
    (ht' : t (T'.ring α) (T'.ideal α) = t (Sq.ring (β + 1)) (Sq.ideal (β + 1)))
    (htau' : ∀ a, 1 ≤ a → a ≤ t (Sq.ring (β + 1)) (Sq.ideal (β + 1)) →
      tau (T'.ring α) (T'.ideal α) a = tau (Sq.ring (β + 1)) (Sq.ideal (β + 1)) a) :
    nuStar (T'.ring α) (T'.ideal α) = nuStar (Sq.ring β) (Sq.ideal β) ∧
      t (T'.ring α) (T'.ideal α) = t (Sq.ring β) (Sq.ideal β) ∧
      ∀ a, 1 ≤ a → a ≤ t (Sq.ring β) (Sq.ideal β) →
        tau (T'.ring α) (T'.ideal α) a = tau (Sq.ring β) (Sq.ideal β) a :=
  ⟨hnu'.trans hnu, ht'.trans ht, fun a h1 h2 =>
    (htau' a h1 (by rw [ht]; exact h2)).trans (htau a h1 h2)⟩

/-- The conditions of `T'` at the index `0` (`J'_0 = J_{β+1}R'_0`, `R_{β+1} ≅ R'_0`). -/
theorem stage_conditions_zero [Hironaka.HironakaCitedResults.{u}] (Sq : MonoidalSequence.{u}) (β : ℕ) (T' : MonoidalSequence.{u})
    (e' : Sq.ring (β + 1) ≃+* T'.ring 0) (h0' : T'.ideal 0 = (Sq.ideal (β + 1)).map e') :
    nuStar (T'.ring 0) (T'.ideal 0) = nuStar (Sq.ring (β + 1)) (Sq.ideal (β + 1)) ∧
      t (T'.ring 0) (T'.ideal 0) = t (Sq.ring (β + 1)) (Sq.ideal (β + 1)) ∧
      ∀ a, 1 ≤ a → a ≤ t (Sq.ring (β + 1)) (Sq.ideal (β + 1)) →
        tau (T'.ring 0) (T'.ideal 0) a = tau (Sq.ring (β + 1)) (Sq.ideal (β + 1)) a := by
  obtain ⟨h1, h2, h3⟩ := nuStar_t_tau_map_of_bijective_aux (e' : Sq.ring (β + 1) →+* T'.ring 0)
    e'.bijective (Sq.ideal (β + 1))
  rw [← show T'.ideal 0 = (Sq.ideal (β + 1)).map (e' : Sq.ring (β + 1) →+* T'.ring 0) from h0']
    at h1 h2 h3
  exact ⟨h1, h2, h3⟩

/-- **Transitivity of `J`-stability along one step of a sequence** (the "easily seen" statement
used at p. 271): if `z` is `J_β`-stable in `R_β` and `z₁` is its strict transform in `R_{β+1}`
(`J_{β+1}` being the strict transform of `J_β`), where `ν*`, `t`, `τ^{(a)}` of `J_{β+1}` and `J_β`
agree and the step is permissible and residually separable algebraic, then `z₁` is
`J_{β+1}`-stable.  (Any sequence of `R_{β+1}` is prefixed by the step `β`; it is then a sequence
of `R_β` along which the stability of `z` applies.) -/
theorem IsJStable.succ_stage [Hironaka.HironakaCitedResults.{u}] (Sq : MonoidalSequence.{u}) (β : ℕ)
    (hperm : IsPermissibleCenter (Sq.ring β) (Sq.ideal β) (Sq.center β))
    (hsep : RingHom.IsResiduallySeparableAlgebraic (R := Sq.ring β) (R' := (Sq.transform β).ring)
      (Sq.transform β).toRing)
    (hnu : nuStar (Sq.ring (β + 1)) (Sq.ideal (β + 1)) = nuStar (Sq.ring β) (Sq.ideal β))
    (ht : t (Sq.ring (β + 1)) (Sq.ideal (β + 1)) = t (Sq.ring β) (Sq.ideal β))
    (htau : ∀ a, 1 ≤ a → a ≤ t (Sq.ring β) (Sq.ideal β) →
      tau (Sq.ring (β + 1)) (Sq.ideal (β + 1)) a = tau (Sq.ring β) (Sq.ideal β) a)
    {z : Sq.ring β} (hz : IsJStable (Sq.ideal β) z) {z₁ : Sq.ring (β + 1)}
    (hz₁ : Ideal.span {z₁} =
      (strictTransformIdeal (Sq.transform β) (Ideal.span {z})).map (Sq.equiv β)) :
    IsJStable (Sq.ideal (β + 1)) z₁ := by
  intro T' e' h0' hperm' hsep' α hnu' ht' htau' fα hfα
  have hCperm := stageSeq_isPermissible Sq β hperm hperm' (e' := e') (h0' := h0')
  have hCsep := stageSeq_isResiduallySeparableAlgebraic Sq β hsep hsep' (e' := e') (h0' := h0')
  have hC0 := stageSeq_ideal_zero Sq β (e' := e') (h0' := h0')
  -- the order of `z₁` is that of `z`: the index `1` of the prefixed sequence
  obtain ⟨hN0, ht0, hτ0⟩ := stage_conditions_zero Sq β T' e' h0'
  obtain ⟨hN1, ht1, hτ1⟩ := stage_conditions Sq β T' 0 hnu ht htau hN0 ht0 hτ0
  have hν := hz (stageSeq Sq β T' e' h0') (RingEquiv.refl (Sq.ring β)) hC0 hCperm hCsep 1 hN1 ht1
    hτ1
    (e' z₁)
    (stageSeq_isStrictTransformElem Sq β hz₁ (n := 0) (g := e' z₁) rfl)
  obtain ⟨hN, ht'', hτ⟩ := stage_conditions Sq β T' α hnu ht htau hnu' ht' htau'
  have hα := hz (stageSeq Sq β T' e' h0') (RingEquiv.refl (Sq.ring β)) hC0 hCperm hCsep (α + 1) hN
    ht'' hτ fα
    (stageSeq_isStrictTransformElem Sq β hz₁ hfα)
  have hν' : Ideal.ordElem (maximalIdeal (Sq.ring β)) z =
      Ideal.ordElem (maximalIdeal (Sq.ring (β + 1))) z₁ :=
    hν.1.symm.trans (ordElem_maximalIdeal_ringEquiv_aux e' z₁)
  exact ⟨hα.1.trans hν', fun hc => (hα.2 hc).trans hν'⟩

open Classical in
/-- **Transitivity of `(J; τ_{(z)})`-stability along one step of a sequence**: the same for a
system `z` and an element `f`, with `τ_{(z)}(f)` compared through `R_{β+1} ≅ R'_0`. -/
theorem IsJTauZStable.succ_stage [Hironaka.HironakaCitedResults.{u}] (Sq : MonoidalSequence.{u}) (β : ℕ)
    (hperm : IsPermissibleCenter (Sq.ring β) (Sq.ideal β) (Sq.center β))
    (hsep : RingHom.IsResiduallySeparableAlgebraic (R := Sq.ring β) (R' := (Sq.transform β).ring)
      (Sq.transform β).toRing)
    (hnu : nuStar (Sq.ring (β + 1)) (Sq.ideal (β + 1)) = nuStar (Sq.ring β) (Sq.ideal β))
    (ht : t (Sq.ring (β + 1)) (Sq.ideal (β + 1)) = t (Sq.ring β) (Sq.ideal β))
    (htau : ∀ a, 1 ≤ a → a ≤ t (Sq.ring β) (Sq.ideal β) →
      tau (Sq.ring (β + 1)) (Sq.ideal (β + 1)) a = tau (Sq.ring β) (Sq.ideal β) a)
    {r : ℕ} {z : Fin r → Sq.ring β} {f : Sq.ring β} (hz : IsJTauZStable (Sq.ideal β) z f)
    {z₁ : Fin r → Sq.ring (β + 1)} {f₁ : Sq.ring (β + 1)}
    (hext₁ : ExtendsToRSOP (Sq.ring (β + 1)) (Finset.image z₁ Finset.univ))
    (hz₁ : ∀ j, Ideal.span {z₁ j} =
      (strictTransformIdeal (Sq.transform β) (Ideal.span {z j})).map (Sq.equiv β))
    (hf₁ : Ideal.span {f₁} =
      (strictTransformIdeal (Sq.transform β) (Ideal.span {f})).map (Sq.equiv β)) :
    IsJTauZStable (Sq.ideal (β + 1)) z₁ f₁ := by
  refine ⟨hext₁, fun j => IsJStable.succ_stage Sq β hperm hsep hnu ht htau (hz.2.1 j) (hz₁ j), ?_⟩
  intro T' e' h0' hperm' hsep' α hnu' ht' htau' zα hzα fα hfα
  have hCperm := stageSeq_isPermissible Sq β hperm hperm' (e' := e') (h0' := h0')
  have hCsep := stageSeq_isResiduallySeparableAlgebraic Sq β hsep hsep' (e' := e') (h0' := h0')
  have hC0 := stageSeq_ideal_zero Sq β (e' := e') (h0' := h0')
  obtain ⟨hN0, ht0, hτ0⟩ := stage_conditions_zero Sq β T' e' h0'
  obtain ⟨hN1, ht1, hτ1⟩ := stage_conditions Sq β T' 0 hnu ht htau hN0 ht0 hτ0
  -- the index `1` of the prefixed sequence: orders and `τ` of the first strict transforms
  have h1 := hz.2.2 (stageSeq Sq β T' e' h0') (RingEquiv.refl (Sq.ring β)) hC0 hCperm hCsep 1 hN1
    ht1 hτ1 (fun j => e' (z₁ j))
    (fun j => stageSeq_isStrictTransformElem Sq β (hz₁ j) (n := 0) (g := e' (z₁ j)) rfl) (e' f₁)
    (stageSeq_isStrictTransformElem Sq β hf₁ (n := 0) (g := e' f₁) rfl)
  obtain ⟨hN, ht'', hτ⟩ := stage_conditions Sq β T' α hnu ht htau hnu' ht' htau'
  have hα := hz.2.2 (stageSeq Sq β T' e' h0') (RingEquiv.refl (Sq.ring β)) hC0 hCperm hCsep (α + 1)
    hN ht'' hτ zα (fun j => stageSeq_isStrictTransformElem Sq β (hz₁ j) (hzα j)) fα
    (stageSeq_isStrictTransformElem Sq β hf₁ hfα)
  have hν' : Ideal.ordElem (maximalIdeal (Sq.ring β)) f =
      Ideal.ordElem (maximalIdeal (Sq.ring (β + 1))) f₁ :=
    h1.1.symm.trans (ordElem_maximalIdeal_ringEquiv_aux e' f₁)
  have hτ₁ : tauZ (Sq.ring (β + 1)) z₁ (fun _ : Fin 1 => f₁) =
      tauZ (Sq.ring β) z (fun _ : Fin 1 => f) :=
    (tauZ_map (e' : Sq.ring (β + 1) →+* T'.ring 0) (mapsRSOP_of_bijective_aux _ e'.bijective)
      (isResiduallySeparable_of_bijective_aux _ e'.bijective) z₁ (fun _ : Fin 1 => f₁)).symm.trans
      h1.2.2
  exact ⟨hα.1.trans hν', fun hc => (hα.2.1 hc).trans hν', hα.2.2.trans hτ₁.symm⟩

end StageStability

section TransportRingEquiv

variable {A B : Type u} [CommRing A] [IsRegularLocalRing A] [CommRing B] [IsRegularLocalRing B]

/-- `J`-stability is invariant under ring isomorphisms (`R ≅ R₀` in the definition of stability
along sequences). -/
theorem IsJStable.transport [Hironaka.HironakaCitedResults.{u}] (φ : A ≃+* B) {J : Ideal A} {z : A} (hz : IsJStable J z) :
    IsJStable (J.map φ) (φ z) := by
  intro Sq e h0 hperm hsep α hnu ht htau fα hfα
  obtain ⟨hN, ht', hτ⟩ := nuStar_t_tau_map_of_bijective_aux (φ : A →+* B) φ.bijective J
  have h := hz Sq (φ.trans e)
    (by rw [h0]; exact Ideal.map_map (φ : A →+* B) (e : B →+* Sq.ring 0)) hperm hsep α
    (hnu.trans hN) (ht.trans ht') (fun a h1 h2 =>
      (htau a h1 (le_of_le_of_eq h2 ht'.symm)).trans (hτ a h1 h2)) fα hfα
  rw [ordElem_maximalIdeal_ringEquiv_aux φ z]
  exact h

open Classical in
/-- `(J; τ_{(z)})`-stability is invariant under ring isomorphisms. -/
theorem IsJTauZStable.transport [Hironaka.HironakaCitedResults.{u}] (φ : A ≃+* B) {J : Ideal A} {r : ℕ} {z : Fin r → A} {f : A}
    (hz : IsJTauZStable J z f) : IsJTauZStable (J.map φ) (fun j => φ (z j)) (φ f) := by
  refine ⟨?_, fun j => IsJStable.transport φ (hz.2.1 j), ?_⟩
  · have := extendsToRSOP_image_ringEquiv φ hz.1
    rwa [Finset.image_image] at this
  intro Sq e h0 hperm hsep α hnu ht htau zα hzα fα hfα
  obtain ⟨hN, ht', hτ⟩ := nuStar_t_tau_map_of_bijective_aux (φ : A →+* B) φ.bijective J
  have h := hz.2.2 Sq (φ.trans e)
    (by rw [h0]; exact Ideal.map_map (φ : A →+* B) (e : B →+* Sq.ring 0)) hperm hsep α
    (hnu.trans hN) (ht.trans ht') (fun a h1 h2 =>
      (htau a h1 (le_of_le_of_eq h2 ht'.symm)).trans (hτ a h1 h2)) zα hzα fα hfα
  rw [ordElem_maximalIdeal_ringEquiv_aux φ f]
  refine ⟨h.1, h.2.1, h.2.2.trans ?_⟩
  exact (tauZ_map (φ : A →+* B) (mapsRSOP_of_bijective_aux _ φ.bijective)
    (isResiduallySeparable_of_bijective_aux _ φ.bijective) z (fun _ : Fin 1 => f)).symm

end TransportRingEquiv

end Hironaka
