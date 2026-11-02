/-
Copyright (c) 2026 Daattavya Aggarwal, Minhyong Kim, Oisin Kim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daattavya Aggarwal, Minhyong Kim, Oisin Kim
-/
module

public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Architect
public import Hironaka.Ch3.JStability
public import Hironaka.Statements

/-!
# Compatibility layer: ν*, t and τ are constant along the first steps of a sequence (Ch. III §9)

In Remark 2 (p. 263) and in the proofs of Lemma 25 and Theorem 9 the paper applies a statement
about one monoidal transform `R_{β} → R_{β+1}` to *every* step of a permissible sequence, for the
indices `β < ᾱ` with `ν*(J_ᾱ) = ν*(J)` and `τ*(J_ᾱ) = τ*(J)`.  This needs that the equalities
`ν*(J_β) = ν*(J)`, `t(J_β) = t(J)` and `τ^{(a)}(J_β) = τ^{(a)}(J)` hold for all `β ≤ ᾱ`: `ν*` does
not increase (Theorem 3, §5) and, as long as it stays the same, `t` stays the same and the
`τ^{(a)}` do not decrease.  The paper does not say this ("One can easily see that, if we prove
these facts, then the proof of the lemma is completed", p. 271); the argument is the one inside the
proof of `isStandardBase_strictTransform_of_isJStableSystem`, extracted here.
-/

@[expose] public section

open IsLocalRing

namespace Hironaka

universe u

namespace MonoidalSequence

/-- Along a permissible sequence of strict monoidal transforms which is residually separable
algebraic, if `ν*`, `t` and `τ^{(a)}` at the index `ᾱ` are those of `J`, the same holds at every
index `β ≤ ᾱ` (the `step`/`chain` argument inside Remark 2, p. 263). -/
theorem IsPermissible.nuStar_t_tau_eq_of_le [Hironaka.HironakaCitedResults.{u}] {R : Type u} [CommRing R] [IsRegularLocalRing R]
    {S : MonoidalSequence.{u}} (hperm : S.IsPermissible) (J : Ideal R) (e : R ≃+* S.ring 0)
    (h0 : S.ideal 0 = J.map e) (hsep : S.IsResiduallySeparableAlgebraic) (αb : ℕ)
    (hnu : nuStar (S.ring αb) (S.ideal αb) = nuStar R J)
    (ht : t (S.ring αb) (S.ideal αb) = t R J)
    (htau : ∀ a, 1 ≤ a → a ≤ t R J → tau (S.ring αb) (S.ideal αb) a = tau R J a) :
    ∀ n ≤ αb, nuStar (S.ring n) (S.ideal n) = nuStar R J ∧ t (S.ring n) (S.ideal n) = t R J ∧
      ∀ a, 1 ≤ a → a ≤ t R J → tau (S.ring n) (S.ideal n) a = tau R J a := by
  classical
  -- one step `R_n → R_{n+1}`: `ν*` does not increase, and if it stays the same then `t` stays
  -- the same and the `τ^{(i)}` do not decrease (Theorem 3, §5)
  have step : ∀ n, nuStar (S.ring (n + 1)) (S.ideal (n + 1)) ≤ nuStar (S.ring n) (S.ideal n) ∧
      (nuStar (S.ring (n + 1)) (S.ideal (n + 1)) = nuStar (S.ring n) (S.ideal n) →
        t (S.ring (n + 1)) (S.ideal (n + 1)) = t (S.ring n) (S.ideal n) ∧
        ∀ i, 1 ≤ i → i ≤ t (S.ring n) (S.ideal n) →
          tau (S.ring n) (S.ideal n) i ≤ tau (S.ring (n + 1)) (S.ideal (n + 1)) i) := by
    intro n
    rcases hperm n with htop | ⟨hP, hJP, hreg, -⟩
    · -- center `R_n`: `R_n → R_{n+1}` is an isomorphism
      have hbij := MonoidalSequence.toRing_bijective_of_eq_top_aux (S.transform n) htop
      have hφ : Function.Bijective
          ((S.equiv n : (S.transform n).ring →+* S.ring (n + 1)).comp (S.transform n).toRing) :=
        (S.equiv n).bijective.comp hbij
      have hI : S.ideal (n + 1) = (S.ideal n).map
          ((S.equiv n : (S.transform n).ring →+* S.ring (n + 1)).comp (S.transform n).toRing) := by
        rw [S.ideal_succ n, MonoidalSequence.strictTransformIdeal_eq_map_of_eq_top_aux _ htop]
        exact Ideal.map_map (S.transform n).toRing
          (S.equiv n : (S.transform n).ring →+* S.ring (n + 1))
      obtain ⟨h1, h2, h3⟩ := nuStar_t_tau_map_of_bijective_aux _ hφ (S.ideal n)
      rw [← hI] at h1 h2 h3
      exact ⟨h1.le, fun _ => ⟨h2, fun i hi hit => (h3 i hi hit).ge⟩⟩
    · have := hP
      have := hreg
      obtain ⟨h1, h2⟩ := nuStar_strictTransform_le (S.ring n) (S.center n) (S.ideal n) hJP
        (S.transform n) (hsep n) (hperm n)
      obtain ⟨e1, e2, e3⟩ := nuStar_t_tau_map_of_bijective_aux
        (S.equiv n : (S.transform n).ring →+* S.ring (n + 1)) (S.equiv n).bijective
        (strictTransformIdeal (S.transform n) (S.ideal n))
      have hI : S.ideal (n + 1) = (strictTransformIdeal (S.transform n) (S.ideal n)).map
          (S.equiv n : (S.transform n).ring →+* S.ring (n + 1)) := S.ideal_succ n
      rw [← hI] at e1 e2 e3
      refine ⟨e1.trans_le h1, fun heq => ?_⟩
      obtain ⟨ht', htau'⟩ := h2 (e1.symm.trans heq)
      exact ⟨e2.trans ht', fun i hi hit =>
        (htau' i hi hit).trans (e3 i hi (hit.trans ht'.ge)).ge⟩
  -- `R₀ = R`
  obtain ⟨hN0, ht0, hτ0⟩ := nuStar_t_tau_map_of_bijective_aux (e : R →+* S.ring 0) e.bijective J
  rw [← show S.ideal 0 = J.map (e : R →+* S.ring 0) from h0] at hN0 ht0 hτ0
  -- `ν*` along the sequence
  have chain : ∀ n k,
      nuStar (S.ring (n + k)) (S.ideal (n + k)) ≤ nuStar (S.ring n) (S.ideal n) := by
    intro n k
    induction k with
    | zero => exact le_rfl
    | succ k ih => exact (step (n + k)).1.trans ih
  have hnuα : ∀ n ≤ αb, nuStar (S.ring n) (S.ideal n) = nuStar R J := by
    intro n hn
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
    refine le_antisymm ?_ (hnu.symm.trans_le (chain n k))
    have := chain 0 n
    rw [zero_add] at this
    exact this.trans_eq hN0
  have htα : ∀ n ≤ αb, t (S.ring n) (S.ideal n) = t R J := by
    intro n
    induction n with
    | zero => exact fun _ => ht0
    | succ n ih =>
      intro hn
      exact ((step n).2 ((hnuα (n + 1) hn).trans (hnuα n (by omega)).symm)).1.trans (ih (by omega))
  have hτup : ∀ n k, n + k ≤ αb → ∀ i, 1 ≤ i → i ≤ t R J →
      tau (S.ring n) (S.ideal n) i ≤ tau (S.ring (n + k)) (S.ideal (n + k)) i := by
    intro n k
    induction k with
    | zero => exact fun _ _ _ _ => le_rfl
    | succ k ih =>
      intro hk i hi hit
      refine (ih (by omega) i hi hit).trans (((step (n + k)).2
        ((hnuα (n + k + 1) hk).trans (hnuα (n + k) (by omega)).symm)).2 i hi ?_)
      rw [htα (n + k) (by omega)]
      exact hit
  have hτα : ∀ n ≤ αb, ∀ a, 1 ≤ a → a ≤ t R J → tau (S.ring n) (S.ideal n) a = tau R J a := by
    intro n hn a ha hat
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
    refine le_antisymm ((hτup n k le_rfl a ha hat).trans_eq (htau a ha hat)) ?_
    have := hτup 0 n (by omega) a ha hat
    rw [zero_add] at this
    exact (hτ0 a ha hat).symm.trans_le this
  exact fun n hn => ⟨hnuα n hn, htα n hn, hτα n hn⟩

end MonoidalSequence

end Hironaka
