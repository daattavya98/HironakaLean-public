/-
Copyright (c) 2026 Daattavya Aggarwal, Minhyong Kim, Oisin Kim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daattavya Aggarwal, Minhyong Kim, Oisin Kim
-/
module

public import Hironaka.Compat.FrameCoordinates

/-!
# Modifying frames: replacing a vector, and quotients by a frame vector (Compat API for Corollary 2)

Hironaka, Ch. 0, Corollary 2 of Main Theorem II (p. 145): "We can easily see that `f*(F)/L` is locally free on
`X'`" (the quotient is not argued).  Locally `L = O·e` with `e = ∑ h'_j f*(c_j)` a vector whose
coordinates generate the unit ideal, hence one of them, `h'_{j₀}`, is a unit near the point.  This module
supplies the two pieces of frame algebra:

* `Hironaka.Scheme.Modules.IsFrame.replace`: if `p` is a frame of `G` over `U` and `e = ∑ uₖ pₖ` with `u_{j₀}` a
  unit, replacing `p_{j₀}` by `e` still gives a frame;
* `Hironaka.Scheme.Modules.isFrame_cokernel`: if `c` is a frame of `G` over `U`, `φ : L ⟶ G` with `L` having a
  one-element frame `ε` over `U` and `φ(ε) = c_{j₀}`, then the images of the other `c_k` form a frame of
  `cokernel φ` over `U` (Yoneda criterion `isFrame_iff_bijective_frameHomMap` and the universal property of the
  cokernel).

This is infrastructure (no statement of the paper); it is not a deviation.
-/

@[expose] public section

open CategoryTheory Limits Opposite AlgebraicGeometry TopologicalSpace

universe u

namespace Hironaka

namespace Scheme.Modules

open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Modules

variable {Y : Scheme.{u}}

/-- **Replacing a frame vector by a vector with a unit coefficient.**  If `p` is a frame of `G` over `U`, `V ≤ U`
and `e = ∑ uₖ p_k|_V` with `u_{j₀}` a unit of `Γ(Y, V)`, then replacing `p_{j₀}|_V` by `e` gives a frame over `V`. -/
theorem IsFrame.replace {G : Y.Modules} {U : Y.Opens} {ι : Type u} [Fintype ι] [DecidableEq ι]
    {p : ι → Γ(G, U)} (hp : IsFrame G U p) {V : Y.Opens} (hVU : V ≤ U) (u : ι → Γ(Y, V)) (j₀ : ι)
    (hu : IsUnit (u j₀)) :
    IsFrame G V (fun i => if i = j₀ then ∑ k, u k • G.sectionRes hVU (p k) else G.sectionRes hVU (p i)) := by
  refine ⟨fun V' hV' => ?_⟩
  have hV'U : V' ≤ U := hV'.trans hVU
  have hbij := hp.bijective V' hV'U
  let u' : ι → Γ(Y, V') := fun k => resO Y hV' (u k)
  have hu' : IsUnit (u' j₀) := hu.map (Y.presheaf.map (homOfLE hV').op).hom
  obtain ⟨v, hv⟩ := hu'.exists_right_inv
  let T : (ι → Γ(Y, V')) → (ι → Γ(Y, V')) := fun a k => (if k = j₀ then 0 else a k) + a j₀ * u' k
  have hT : Function.Bijective T := by
    constructor
    · intro a b hab
      have h1 : a j₀ * u' j₀ = b j₀ * u' j₀ := by
        have := congrFun hab j₀
        simpa [T] using this
      have h2 : a j₀ = b j₀ := hu'.mul_left_inj.mp h1
      funext k
      by_cases hk : k = j₀
      · rw [hk]; exact h2
      · have := congrFun hab k
        simp only [T, hk, ite_false, h2] at this
        exact add_right_cancel this
    · intro t
      let a0 : Γ(Y, V') := t j₀ * v
      refine ⟨fun k => if k = j₀ then a0 else t k - a0 * u' k, ?_⟩
      funext k
      by_cases hk : k = j₀
      · subst hk
        simp only [T, ite_true, zero_add]
        rw [mul_assoc, mul_comm v, hv, mul_one]
      · simp [T, hk, a0]
  have heq : (fun a : ι → Γ(Y, V') => ∑ i, a i • G.presheaf.map (homOfLE hV').op
      (if i = j₀ then ∑ k, u k • G.sectionRes hVU (p k) else G.sectionRes hVU (p i))) =
      (fun a : ι → Γ(Y, V') => ∑ i, a i • G.presheaf.map (homOfLE hV'U).op (p i)) ∘ T := by
    funext a
    let r : ι → Γ(G, V') := fun k => G.sectionRes hV'U (p k)
    have hE : G.sectionRes hV' (∑ k, u k • G.sectionRes hVU (p k)) = ∑ k, u' k • r k := by
      rw [sectionRes_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [sectionRes_smul, sectionRes_res]
    have hterm : ∀ i, a i • G.sectionRes hV'
        (if i = j₀ then ∑ k, u k • G.sectionRes hVU (p k) else G.sectionRes hVU (p i)) =
        (if i = j₀ then a j₀ • ∑ k, u' k • r k else 0) + (if i = j₀ then 0 else a i) • r i := by
      intro i
      by_cases hi : i = j₀
      · subst hi
        simp only [ite_true, zero_smul, add_zero, hE]
      · simp only [hi, ite_false, zero_add, sectionRes_res]
        rfl
    have hL : (∑ i, a i • G.presheaf.map (homOfLE hV').op
        (if i = j₀ then ∑ k, u k • G.sectionRes hVU (p k) else G.sectionRes hVU (p i))) =
        a j₀ • ∑ k, u' k • r k + ∑ i, (if i = j₀ then 0 else a i) • r i := by
      show ∑ i, a i • G.sectionRes hV' _ = _
      rw [Finset.sum_congr rfl fun i _ => hterm i, Finset.sum_add_distrib]
      simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    have hR : (∑ i, T a i • G.presheaf.map (homOfLE hV'U).op (p i)) =
        a j₀ • ∑ k, u' k • r k + ∑ i, (if i = j₀ then 0 else a i) • r i := by
      show ∑ i, T a i • r i = _
      simp only [T, add_smul, Finset.sum_add_distrib, Finset.smul_sum, mul_smul]
      exact add_comm _ _
    exact hL.trans hR.symm
  show Function.Bijective (fun a : ι → Γ(Y, V') => ∑ i, a i • G.presheaf.map (homOfLE hV').op
      (if i = j₀ then ∑ k, u k • G.sectionRes hVU (p k) else G.sectionRes hVU (p i)))
  rw [heq]
  exact hbij.comp hT

/-- The zero morphism has all frame values zero. -/
theorem frameHomMap_zero {M : Y.Modules} {U : Y.Opens} {ι : Type u} (c : ι → Γ(M, U))
    (S : U.toScheme.Modules) (i : ι) : frameHomMap M U c S 0 i = 0 := by
  unfold frameHomMap
  exact (congrArg (S.presheaf.map (homOfLE (Scheme.Opens.ι_preimage_self U).ge).op)
    (rfl : (0 : M ⟶ (pushforward U.ι).obj S).app U (c i) = 0)).trans (map_zero _)

/-- **The quotient by a frame vector.**  If `c` is a frame of `G` over `U`, `φ : L ⟶ G` and `L` has a one-element
frame `ε` over `U` with `φ(ε) = c_{j₀}`, then the images of the other `c_k` form a frame of `cokernel φ` over `U`. -/
theorem isFrame_cokernel {G L : Y.Modules} {U : Y.Opens} {ι : Type u} [Fintype ι] [DecidableEq ι]
    {c : ι → Γ(G, U)} (hc : IsFrame G U c) (j₀ : ι) (φ : L ⟶ G) {ε : Γ(L, U)}
    (hε : IsFrame L U (fun _ : PUnit.{u + 1} => ε)) (hφ : φ.app U ε = c j₀) :
    IsFrame (cokernel φ) U (fun k : {k // k ≠ j₀} => (cokernel.π φ).app U (c k)) := by
  refine (isFrame_iff_bijective_frameHomMap _).mpr fun S => ?_
  have hG := (isFrame_iff_bijective_frameHomMap c).mp hc S
  have hL := (isFrame_iff_bijective_frameHomMap _).mp hε S
  have hzero : ∀ χ : cokernel φ ⟶ (pushforward U.ι).obj S,
      frameHomMap G U c S (cokernel.π φ ≫ χ) j₀ = 0 := by
    intro χ
    have : frameHomMap G U c S (cokernel.π φ ≫ χ) j₀ =
        frameHomMap L U (fun _ : PUnit.{u + 1} => ε) S (φ ≫ cokernel.π φ ≫ χ) PUnit.unit := by
      unfold frameHomMap
      rw [← hφ]
      rfl
    rw [this, ← Category.assoc, cokernel.condition, zero_comp]
    exact frameHomMap_zero _ _ _
  constructor
  · intro χ₁ χ₂ h
    have h1 : frameHomMap G U c S (cokernel.π φ ≫ χ₁) = frameHomMap G U c S (cokernel.π φ ≫ χ₂) := by
      funext k
      by_cases hk : k = j₀
      · subst hk; rw [hzero, hzero]
      · exact congrFun h ⟨k, hk⟩
    exact (cancel_epi (cokernel.π φ)).mp (hG.1 h1)
  · intro t
    let t' : ι → Γ(S, ⊤) := fun k => if hk : k = j₀ then 0 else t ⟨k, hk⟩
    obtain ⟨χ, hχ⟩ := hG.2 t'
    have hφχ : φ ≫ χ = 0 := by
      refine hL.1 ?_
      funext i
      cases i
      have : frameHomMap L U (fun _ : PUnit.{u + 1} => ε) S (φ ≫ χ) PUnit.unit =
          frameHomMap G U c S χ j₀ := by
        unfold frameHomMap
        rw [← hφ]
        rfl
      rw [this, hχ]
      simp only [t', dite_true]
      exact (frameHomMap_zero (fun _ : PUnit.{u + 1} => ε) S PUnit.unit).symm
    refine ⟨cokernel.desc φ χ hφχ, ?_⟩
    funext k
    have : frameHomMap (cokernel φ) U (fun k : {k // k ≠ j₀} => (cokernel.π φ).app U (c k)) S
        (cokernel.desc φ χ hφχ) k = frameHomMap G U c S (cokernel.π φ ≫ cokernel.desc φ χ hφχ) k := rfl
    rw [this, cokernel.π_desc, hχ]
    simp [t', k.2]

end Scheme.Modules

end Hironaka
