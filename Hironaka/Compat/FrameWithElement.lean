/-
Copyright (c) 2026 Daattavya Aggarwal, Minhyong Kim, Oisin Kim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daattavya Aggarwal, Minhyong Kim, Oisin Kim
-/
module

public import Mathlib.RingTheory.MvPowerSeries.Rename
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Architect
public import Hironaka.Compat.CoefficientField
public import Hironaka.Compat.NormalizedStandardBase

/-!
# Compatibility layer: regular frames of a complete regular local ring (Ch. III §8, p. 258)

> "Then `R` is a formal power series ring over a field, by Cohen's structure theorem."
> (Proof of Proposition 2, p. 258)
> "Let `(y₁, …, y_s)` be a system of elements of `R` such that `(x, z₁, …, z_t, y₁, …, y_s)` is a
> regular system of parameters of `R`. We have a subfield `k` of `R` such that
> `R = k{x, z₁, …, z_t, y₁, …, y_s}`. […] Let `S = k{z_{r+1}, …, z_t, x, y₁, …, y_s}`. Then
> `(S; z₁, …, z_r)` is a regular `τ`-frame of `R` for `J` having the required property as above."
> (Proof of Proposition 2, p. 258)

This file contains

* `exists_regularFrame_of_extendsToRSOP_insert`: for a complete regular local ring `R` with a
  coefficient field `k = σ(R/M)` (Cohen's structure theorem, the cited leaf
  `exists_residue_comp_eq_id_of_isAdicComplete_of_ringChar_eq` of
  `Hironaka/Compat/CoefficientField.lean`, which gives `σ` for a ring of equal characteristic) and
  an injective system `(z₁, …, z_r)` such that `(z₁, …, z_r, x)` can be extended to a regular
  system of parameters, a regular frame `(S; z₁, …, z_r)` of `R` such that `x` is the image of an
  element of `S`;
* `RegularFrame.initialForm_mem_assocSubalgebra_of_isNormalizedBy`: the initial form of an element
  which is normalized by `(f₁, …, f_i)` (and extends it to a standard base) lies in the associated
  subalgebra of a regular `τ`-frame, by Lemma 19 (Definition 9 (3) (i)).
-/

@[expose] public section

open IsLocalRing

namespace Hironaka

universe u

section FrameWithElement

open _root_.MvPowerSeries

variable {R : Type u} [CommRing R] [IsRegularLocalRing R] [IsAdicComplete (maximalIdeal R) R]

open Classical in
/-- **A regular frame of a complete regular local ring with a prescribed element in the
coefficient ring** (p. 258): let `R` be a complete regular local ring of equal characteristic,
`(z₁, …, z_r)` an injective system and `x ∉ {z_j}` such that `(z₁, …, z_r, x)` can be extended to a
regular system of parameters of `R`.  Then there is a regular frame `(S; z₁, …, z_r)` of `R` with
`x` in the image of `S` (`S = k{x, y₁, …, y_s}` for a coefficient field `k` and a regular system of
parameters `(z, x, y)`); `σ` is the coefficient field (Cohen's structure theorem, p. 258, cited:
`exists_residue_comp_eq_id_of_isAdicComplete_of_ringChar_eq`). -/
theorem exists_regularFrame_of_extendsToRSOP_insert
    (σ : ResidueField R →+* R) (hσ : (IsLocalRing.residue R).comp σ = RingHom.id _)
    {r : ℕ} {z : Fin r → R}
    (hinj : Function.Injective z) (x : R) (hx : x ∉ Finset.image z Finset.univ)
    (hext : ExtendsToRSOP R (insert x (Finset.image z Finset.univ))) :
    ∃ (F : RegularFrame R) (h : F.r = r), (∀ j, F.z (Fin.cast h.symm j) = z j) ∧
      ∃ s : F.S, algebraMap F.S R s = x := by
  obtain ⟨s, hts, hs⟩ := hext
  -- the system `(z₁, …, z_r, x)`
  let z' : Fin (r + 1) → R := Fin.append z (fun _ : Fin 1 => x)
  have hz'z : ∀ j, z' (Fin.castAdd 1 j) = z j := fun j => Fin.append_left _ _ j
  have hz'x : z' (Fin.natAdd r 0) = x := Fin.append_right _ _ 0
  have hz'inj : Function.Injective z' := by
    intro a b hab
    induction a using Fin.addCases with
    | left i =>
      induction b using Fin.addCases with
      | left j => rw [hz'z, hz'z] at hab; rw [hinj hab]
      | right j =>
        rw [hz'z] at hab
        have : j = 0 := Subsingleton.elim _ _
        subst this
        rw [hz'x] at hab
        exact absurd (hab ▸ Finset.mem_image_of_mem z (Finset.mem_univ i)) hx
    | right i =>
      have hi : i = 0 := Subsingleton.elim _ _
      subst hi
      induction b using Fin.addCases with
      | left j =>
        rw [hz'z, hz'x] at hab
        exact absurd (hab ▸ Finset.mem_image_of_mem z (Finset.mem_univ j)) hx
      | right j =>
        have : j = 0 := Subsingleton.elim _ _
        rw [this]
  have hz'sub : Finset.image z' Finset.univ ⊆ s := by
    intro y hy
    obtain ⟨a, -, rfl⟩ := Finset.mem_image.mp hy
    induction a using Fin.addCases with
    | left i =>
      rw [hz'z]
      exact hts (Finset.mem_insert_of_mem (Finset.mem_image_of_mem z (Finset.mem_univ i)))
    | right i =>
      have hi : i = 0 := Subsingleton.elim _ _
      subst hi
      rw [hz'x]
      exact hts (Finset.mem_insert_self _ _)
  obtain ⟨m', xs, hxsinj, hxsz, himg, hcard⟩ := exists_injective_append_enumeration hz'inj hz'sub
  -- reindex `Fin ((r + 1) + m')` as `Fin (r + (1 + m'))`
  have hidx : r + (1 + m') = r + 1 + m' := by omega
  let e : Fin (r + (1 + m')) ≃ Fin (r + 1 + m') := finCongr hidx
  let x'' : Fin (r + (1 + m')) → R := fun i => xs (e i)
  have hx''inj : Function.Injective x'' := hxsinj.comp e.injective
  have hx''s : IsRegularSystemOfParameters R (Finset.univ.image x'') := by
    have : Finset.univ.image x'' = s := by
      rw [← himg]
      ext y
      simp only [Finset.mem_image, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨i, rfl⟩
        exact ⟨e i, rfl⟩
      · rintro ⟨i, rfl⟩
        exact ⟨e.symm i, by simp [x'']⟩
    rw [this]
    exact hs
  obtain ⟨Φ, hΦx, hΦσ, hΦord⟩ := exists_ringEquiv_mvPowerSeries_of_coefficientField σ hσ x''
    hx''inj hx''s
  have hx''z : ∀ j : Fin r, x'' (Fin.castAdd (1 + m') j) = z j := by
    intro j
    have : e (Fin.castAdd (1 + m') j) = Fin.castAdd m' (Fin.castAdd 1 j) := Fin.ext rfl
    simp only [x'', this, hxsz, hz'z]
  have hx''x : x'' (Fin.natAdd r (Fin.castAdd m' 0)) = x := by
    have : e (Fin.natAdd r (Fin.castAdd m' (0 : Fin 1))) = Fin.castAdd m' (Fin.natAdd r 0) :=
      Fin.ext rfl
    simp only [x'', this, hxsz, hz'x]
  have hΦz : ∀ j, Φ (z j) = X (Fin.castAdd (1 + m') j) := fun j => by
    rw [← hx''z j, hΦx]
  have hzext : ExtendsToRSOP R (Finset.image z Finset.univ) :=
    ExtendsToRSOP.mono ⟨s, hts, hs⟩ (Finset.subset_insert _ _)
  obtain ⟨F, h, hFz, ET, hET⟩ := exists_regularFrame_of_ringEquiv_mvPowerSeries Φ hinj hzext hΦz
  refine ⟨F, h, hFz, ET.symm (X (Fin.castAdd m' 0)), ?_⟩
  apply Φ.injective
  rw [hET, RingEquiv.apply_symm_apply, MvPowerSeries.rename_X, ← hΦx, hx''x]

end FrameWithElement

section NormalizedAssoc

variable {R : Type u} [CommRing R] [IsRegularLocalRing R]

/-- **Definition 9 (3) (i) from Lemma 19** (p. 259, repair of the paper's use of Lemma 21 (c)): let
`(S; z)` be a regular `τ`-frame of `R` for `J`, `(f₁, …, f_i)` elements of `J` whose initial forms
lie in the associated subalgebra `k[Z]`, and `f'` an element of `J` which is normalized by
`(f₁, …, f_i)` and such that `(f₁, …, f_i, f')` can be extended to a standard base of `J`.  Then the
initial form of `f'` lies in `k[Z]`.  (The `τ`-parameters of Lemma 19 are taken among the `z_j`,
Definition 10, as in the induction step of footnote 11.) -/
theorem RegularFrame.initialForm_mem_assocSubalgebra_of_isNormalizedBy (F : RegularFrame R)
    (J : Ideal R) (hF : F.IsRegularTauFrame J) {i : ℕ} (f : Fin i → R) (hfJ : ∀ j, f j ∈ J)
    (hfsub : ∀ j, initialForm (maximalIdeal R) (f j) ∈ F.assocSubalgebra) (f' : R) (hf'J : f' ∈ J)
    (hext' : ExtendsToStandardBase J (Fin.snoc f f' : Fin (i + 1) → R))
    (hnorm : F.IsNormalizedBy f f') :
    initialForm (maximalIdeal R) f' ∈ F.assocSubalgebra := by
  classical
  obtain ⟨m', G, him, hG, hGf⟩ := hext'
  set k : Fin m' := Fin.castLE him (Fin.last i) with hk
  have hGk : G k = f' := by
    rw [hk, hGf (Fin.last i), Fin.snoc_last]
  have hord : Ideal.ordElem (maximalIdeal R) f' = nuI R J i.succPNat := by
    have := ordElem_eq_nuI_of_isStandardBase J G hG k
    rw [hGk] at this
    rw [this]
    congr 1
  have hfin : nuI R J i.succPNat ≠ ⊤ := by
    rw [← hord]
    intro htop
    apply hG.2.2.2.2 k
    dsimp only
    rw [hGk, show initialForm (maximalIdeal R) f' = 0 by rw [initialForm, dite_eq_left htop]]
    exact zero_mem _
  obtain ⟨d, hd⟩ := ENat.ne_top_iff_exists.mp hfin
  obtain ⟨a, ha1, hat, hmua⟩ := exists_mu_eq_of_nuI_eq J i.succPNat d hd.symm
  obtain ⟨x, hx, hxz⟩ :=
    RegularFrame.IsRegularTauFrame.exists_isRegularSystemOfTauParameters F J hF ha1 hat
  have hmu : (mu R J a : ℕ∞) = nuI R J i.succPNat := by rw [hmua, hd]
  have h19 := initialForm_mem_adjoin_of_isNormalizedBy F J f hfJ
    (fun j => F.tauZ_eq_zero_of_initialForm_mem (f j) (hfsub j)) f' hf'J a ha1 hmu
    ⟨m', G, him, hG, hGf⟩ hnorm x hx
  have hstar : tauParamsSubmoduleStar J a x F.z ≤
      (Hironaka.assocSubalgebra F.z).toSubmodule := by
    unfold tauParamsSubmoduleStar
    refine Submodule.span_le.mpr ?_
    rintro _ (⟨i', rfl⟩ | ⟨j, rfl⟩)
    · obtain ⟨k', hk'⟩ := hxz i'
      have : linearForms R x i' = frameForm F.z k' := by
        rw [F.frameForm_eq_mk k']
        simp only [linearForms]
        congr 1
      rw [this]
      exact Algebra.subset_adjoin ⟨k', rfl⟩
    · exact Algebra.subset_adjoin ⟨j, rfl⟩
  exact Algebra.adjoin_le (fun y hy => hstar hy) h19

end NormalizedAssoc

end Hironaka
