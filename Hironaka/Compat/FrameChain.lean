/-
Copyright (c) 2026 Daattavya Aggarwal, Minhyong Kim, Oisin Kim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daattavya Aggarwal, Minhyong Kim, Oisin Kim
-/
module

public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Hironaka.Ch3.JStability
public import Hironaka.Statements

/-!
# The frames of a chain of frame transforms (Ch. III, Remark 3, pp. 263–264)

Along a permissible residually separable algebraic sequence with `ν*` and the `τ^{(a)}` unchanged, each
member of the frame of a chain of frame transforms starting at a `J`-stable frame is a strict transform of
the corresponding member of the first frame (Definition 13).
-/

@[expose] public section

open IsLocalRing

namespace Hironaka

universe u

section FrameChain

variable {R : Type u} [CommRing R] [IsRegularLocalRing R]

/-- **The frames of a chain of frame transforms are strict transforms** (Remark 3,
pp. 263--264: "`(S_ᾱ; z_1^{(ᾱ)}, …, z_r^{(ᾱ)})` [is] a frame transform of `(S; z₁, …, z_r)` in
`R_ᾱ` along the sequence", the `z_j^{(ᾱ)}` being "a system of strict monoidal transforms of `z_j`",
Definition 13): along a permissible residually separable algebraic sequence with `ν*` and the
`τ^{(a)}` unchanged at `ᾱ`, the `j`-th member of the frame `(S_β; z^{(β)})` of any chain of frame
transforms starting at a `J`-stable frame `(S; z)` is a strict transform of `z_j` in `R_β`, for
every `β ≤ ᾱ`.  (This is the invariant of the induction in the proof of
`exists_frameTransformAlong_of_isJStable`; it is not part of the conclusion of that theorem.) -/
theorem MonoidalSequence.FrameTransformAlong.isStrictTransformElem_frame [Hironaka.HironakaCitedResults.{u}]
    (F : RegularFrame R) (J : Ideal R) (hF : F.IsJStable J) (Sq : MonoidalSequence.{u})
    (e : R ≃+* Sq.ring 0) (h0 : Sq.ideal 0 = J.map e) (hperm : Sq.IsPermissible)
    (hsep : Sq.IsResiduallySeparableAlgebraic) (αb : ℕ)
    (hnu : nuStar (Sq.ring αb) (Sq.ideal αb) = nuStar R J)
    (htau : ∀ a, 1 ≤ a → a ≤ t R J → tau (Sq.ring αb) (Sq.ideal αb) a = tau R J a)
    (c : Sq.FrameTransformAlong (F.transport e) αb) :
    ∀ β ≤ αb, ∃ hr : (c.frame β).r = F.r, ∀ j,
      Sq.IsStrictTransformElem e (F.z (Fin.cast hr j)) β ((c.frame β).z j) := by
  classical
  have hmono := MonoidalSequence.nuStar_t_tau_eq_of_le J Sq e h0 hperm hsep αb hnu htau
  have hreg := hperm.hasRegularCenters
  let INVG : ∀ β : ℕ, RegularFrame (Sq.ring β) → Prop := fun β G' =>
    ∃ hr : G'.r = F.r, ∀ j : Fin G'.r,
      Sq.IsStrictTransformElem e (F.z (Fin.cast hr j)) β (G'.z j)
  -- order of the `z^{(β)}_j` along `P_β`
  have hord : ∀ β ≤ αb, INVG β (c.frame β) → Sq.center β ≠ ⊤ → ∀ j : Fin (c.frame β).r,
      Ideal.ordElem (Sq.center β) ((c.frame β).z j) = 1 := by
    intro β hβ ⟨hr, hz⟩ hcβ j
    have := (hF (Fin.cast hr j) Sq e h0 hperm hsep β (hmono β hβ).1 (hmono β hβ).2.1
      (hmono β hβ).2.2 ((c.frame β).z j) (hz j)).2 hcβ
    rw [this]
    exact ordElem_maximalIdeal_eq_one_of_mem_extendsToRSOP F.extends_rsop
      (Finset.mem_image_of_mem _ (Finset.mem_univ _))
  show ∀ β ≤ αb, INVG β (c.frame β)
  intro β
  induction β with
  | zero =>
    intro _
    show INVG 0 (c.frame 0)
    rw [c.frame_zero]
    exact ⟨rfl, fun j => rfl⟩
  | succ β ih =>
    intro hβ
    have hI := ih (by omega)
    have hlt : β < αb := by omega
    obtain ⟨hr, hz⟩ := hI
    have hG := c.frame_succ β hlt
    show INVG (β + 1) (c.frame (β + 1))
    rw [hG]
    generalize c.step β hlt = FT
    refine ⟨hr, fun j => ?_⟩
    by_cases hcβ : Sq.center β = ⊤
    · have h1 := Sq.isStrictTransformElem_succ_of_center_eq_top e (hz j) hcβ
      have hunit : IsUnit FT.x := by
        have := FT.span_x
        rw [MonoidalSequence.map_eq_top_of_eq_top_aux (Sq.transform β) hcβ] at this
        exact Ideal.span_singleton_eq_top.mp this
      have h1' : Ideal.span {Sq.equiv β ((Sq.transform β).toRing ((c.frame β).z j))} =
          Sq.strictAlong (Ideal.span {e (F.z (Fin.cast hr j))}) (β + 1) := h1
      refine Eq.trans ?_ h1'
      show Ideal.span {Sq.equiv β (FT.w j)} = _
      rw [← FT.mul_w j, map_mul]
      exact (Ideal.span_singleton_mul_left_unit (hunit.map (Sq.equiv β)) _).symm
    · exact Sq.isStrictTransformElem_succ_of_center_ne_top e hreg (hz j) hcβ (ν := 1)
        (hord β (by omega) ⟨hr, hz⟩ hcβ j) (x := FT.x) FT.span_x (w := FT.w j)
        (by rw [pow_one]; exact FT.mul_w j)

end FrameChain

end Hironaka
