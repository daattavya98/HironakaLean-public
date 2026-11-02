/-
Copyright (c) 2026 Daattavya Aggarwal, Minhyong Kim, Oisin Kim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daattavya Aggarwal, Minhyong Kim, Oisin Kim
-/
module

public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.RingTheory.MvPowerSeries.Basic
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Architect
public import Hironaka.Compat.FrameGraded

/-!
# Compatibility layer: leading coefficients of initial forms in a regular frame (Ch. III §8)

For a regular frame `(S; z₁, …, z_r)` of `R` (Definition 9) and an element `g ∈ Mᵈ` whose initial
form `[g]_d ∈ grᵈ_M(R)` lies in the subalgebra `k[Z]` of `gr_M(R)` (`k = R/M = S/N`), the initial
form is read off from the power series expansion `g = Σ c_A z^A`, `c_A ∈ S`, of `g`: the paper
uses this without comment in the proof of Lemma 20 (p. 255: "`ψ_j = φ_j(W₁, …, W_r) + λ_j`
for `1 ≤ j ≤ i`", the coefficients of `φ_j(W)` being the residues of the coefficients `c_A` of
`z^A`, `|A| = ν_j`).  The statement proved here is the following consequence of
`RegularFrame.mem_maximalIdeal_pow_iff_coeff_mem_pow` (`Compat/FrameGraded.lean`).

* `RegularFrame.exists_algebraMap_residue_eq`: `S → R/M` is surjective (`k = S/N = R/M`).
* `RegularFrame.coeff_eq_residue_expCoeff_of_frameAlgHom_eq_mk`: if `Q ∈ k[Z₁, …, Z_r]` is a
  homogeneous polynomial of degree `d` with `Q(Z) = [g]_d` in `grᵈ_M(R)` (`g ∈ Mᵈ`), then for every
  exponent `A` with `|A| = d` the coefficient of `Z^A` in `Q` is the residue class of the
  expansion coefficient `c_A(g) ∈ S`.
-/

@[expose] public section

open IsLocalRing MvPolynomial

namespace Hironaka

universe u

namespace RegularFrame

section LeadingCoefficient

variable {R : Type u} [CommRing R] [IsRegularLocalRing R] (F : RegularFrame R)

/-- `k = S/N = R/M`: every element of `R/M` is the residue class of the image of an element of
`S` (Definition 9(1), p. 248: `R/(z₁, …, z_r)R` is canonically isomorphic to `S`, and
`(z) ⊆ M`). -/
theorem exists_algebraMap_residue_eq (q : R ⧸ maximalIdeal R) :
    ∃ s : F.S, Ideal.Quotient.mk (maximalIdeal R) (algebraMap F.S R s) = q := by
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective q
  obtain ⟨s, hs⟩ := F.quot_bijective.2 (Ideal.Quotient.mk (Ideal.span (Set.range F.z)) r)
  refine ⟨s, ?_⟩
  rw [RingHom.comp_apply, Ideal.Quotient.eq] at hs
  rw [Ideal.Quotient.eq]
  have hle : F.idealZ ≤ maximalIdeal R := by
    rw [F.maximalIdeal_eq_idealZ_sup_map]
    exact le_sup_left
  exact hle hs

/-- The class `[c]_0` of an element `c` of `S` in `gr⁰_M(R) = k` is its residue class. -/
theorem grMap_zero_eq_algebraMap (c : F.S) :
    F.grMap 0 c = algebraMap (R ⧸ maximalIdeal R) (AssocGraded (maximalIdeal R))
      (Ideal.Quotient.mk (maximalIdeal R) (algebraMap F.S R c)) := by
  have h0 : c ∈ maximalIdeal F.S ^ 0 := by simp
  simp only [grMap, h0, ↓reduceDIte]
  exact AssocGraded.mk_zero_eq_algebraMap _ _ _

/-- `[0]_k = 0`. -/
theorem grMap_zero_right (k : ℕ) : F.grMap k 0 = 0 := by
  simp only [grMap, zero_mem, ↓reduceDIte]
  exact (AssocGraded.mk_eq_zero_iff _ _).mpr (by rw [map_zero]; exact zero_mem _)

/-- **Leading coefficients of an initial form in `k[Z]`** (p. 255: "`ψ_j = φ_j(W₁, …, W_r) +
λ_j`", the coefficient of `W^A` in `φ_j(W)` being the residue of `c_A`): if `g ∈ Mᵈ` and the
initial form `[g]_d` of degree `d` is `Q(Z₁, …, Z_r)` for a homogeneous polynomial `Q` of degree
`d` over `k = R/M`, then for every exponent `A` of degree `d` the coefficient of `Z^A` in `Q` is
the residue class of the coefficient `c_A(g) ∈ S` of `z^A` in the power series expansion of
`g`. -/
theorem coeff_eq_residue_expCoeff_of_frameAlgHom_eq_mk {d : ℕ} {g : R}
    (hg : g ∈ maximalIdeal R ^ d) {Q : MvPolynomial (Fin F.r) (R ⧸ maximalIdeal R)}
    (hQ : Q.IsHomogeneous d)
    (h : frameAlgHom F.z Q = AssocGraded.mk (maximalIdeal R) d g hg)
    (A : Fin F.r →₀ ℕ) (hA : A.degree = d) :
    Q.coeff A = Ideal.Quotient.mk (maximalIdeal R) (algebraMap F.S R (F.expCoeff g A)) := by
  classical
  choose q hq using F.exists_algebraMap_residue_eq
  -- a polynomial over `S` lifting `Q`
  set H : MvPolynomial (Fin F.r) F.S := ∑ B ∈ Q.support, monomial B (q (Q.coeff B)) with hH
  have hHcoeff : ∀ B, H.coeff B = if B ∈ Q.support then q (Q.coeff B) else 0 := by
    intro B
    rw [hH, MvPolynomial.coeff_sum]
    simp only [MvPolynomial.coeff_monomial]
    by_cases hB : B ∈ Q.support
    · rw [Finset.sum_eq_single_of_mem B hB (fun B' _ hB' => by simp [hB'])]
      simp [hB]
    · simp only [hB, ↓reduceIte]
      exact Finset.sum_eq_zero fun B' hB' => by
        have : B' ≠ B := fun e => hB (e ▸ hB')
        simp [this]
  have hdeg : ∀ B ∈ Q.support, B.degree = d := fun B hB => by
    rw [Finsupp.degree_eq_weight_one]
    exact hQ (mem_support_iff.mp hB)
  -- the element `h' = H(z)`
  have hH0 : ∀ B : Fin F.r →₀ ℕ, B.degree ≤ d →
      H.coeff B ∈ maximalIdeal F.S ^ (d - B.degree) := by
    intro B hB
    rw [hHcoeff]
    split_ifs with hBs
    · rw [hdeg B hBs, Nat.sub_self, pow_zero, Ideal.one_eq_top]
      trivial
    · exact zero_mem _
  have hh' : MvPolynomial.aeval F.z H ∈ maximalIdeal R ^ d := F.aeval_mem_maximalIdeal_pow d H hH0
  have hexp : ∀ B, F.expCoeff (MvPolynomial.aeval F.z H) B = H.coeff B := fun B =>
    expCoeff_eq F (G := H) (n := B.degree + 1)
      (by rw [show evZ F H = MvPolynomial.aeval F.z H from rfl, sub_self]; exact zero_mem _)
      (Nat.lt_succ_self _)
  -- `[h']_d = Q(Z)`
  have hmk := F.mk_eq_sum_grMap_mul (isExpansion_expansion F) hh'
  have hfA : frameAlgHom F.z Q = ∑ B ∈ Q.support,
      algebraMap (R ⧸ maximalIdeal R) (AssocGraded (maximalIdeal R)) (Q.coeff B) *
        ∏ i, frameForm F.z i ^ B i := by
    unfold frameAlgHom
    rw [MvPolynomial.aeval_def, MvPolynomial.eval₂_eq']
  have hmkQ : AssocGraded.mk (maximalIdeal R) d (MvPolynomial.aeval F.z H) hh' =
      frameAlgHom F.z Q := by
    rw [hmk, hfA]
    have hsub : Q.support ⊆ (Finsupp.finite_of_degree_le (σ := Fin F.r) d).toFinset := by
      intro B hB
      simp [(hdeg B hB).le]
    rw [← Finset.sum_subset hsub (fun B _ hB => ?_)]
    · refine Finset.sum_congr rfl fun B hB => ?_
      rw [coeff_expansion, hexp, hHcoeff]
      simp only [hB, ↓reduceIte]
      rw [hdeg B hB, Nat.sub_self, grMap_zero_eq_algebraMap, hq]
    · rw [coeff_expansion, hexp, hHcoeff]
      simp only [hB, ↓reduceIte]
      rw [grMap_zero_right, zero_mul]
  -- `g - H(z) ∈ M^(d+1)`
  have hdiff : g - MvPolynomial.aeval F.z H ∈ maximalIdeal R ^ (d + 1) :=
    sub_mem_pow_succ_of_mk_eq_mk (maximalIdeal R) hg hh' (h.symm.trans hmkQ.symm)
  have hcoef := (F.mem_maximalIdeal_pow_iff_coeff_mem_pow (isExpansion_expansion F) (d + 1) _).mp
    hdiff A (by omega)
  rw [map_sub, map_sub, coeff_expansion, coeff_expansion, hexp,
    show d + 1 - A.degree = 1 by omega, pow_one] at hcoef
  have hres : Ideal.Quotient.mk (maximalIdeal R)
      (algebraMap F.S R (F.expCoeff g A - H.coeff A)) = 0 := by
    rw [Ideal.Quotient.eq_zero_iff_mem]
    exact map_maximalIdeal_le _ (Ideal.mem_map_of_mem _ hcoef)
  rw [map_sub, map_sub, sub_eq_zero] at hres
  rw [hres, hHcoeff]
  by_cases hAs : A ∈ Q.support
  · simp only [hAs, ↓reduceIte, hq]
  · simp only [hAs, ↓reduceIte, map_zero]
    exact notMem_support_iff.mp hAs

end LeadingCoefficient

end RegularFrame

end Hironaka
