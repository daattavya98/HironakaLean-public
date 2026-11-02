/-
Copyright (c) 2026 Daattavya Aggarwal, Minhyong Kim, Oisin Kim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daattavya Aggarwal, Minhyong Kim, Oisin Kim
-/
module

public import Mathlib.Algebra.DualNumber
public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Architect
public import Hironaka.Compat.PowerSeriesPolynomialRing

/-!
# Compatibility layer: extending a derivation along localization and completion

A step in the proof of property (c) of the class 𝔅 (p. 161): the
partial derivations `∂/∂t_j`, `∂/∂x_i` of `T = k⟦t⟧[x]` must act on the local rings `T_P`, on their
completions `T̂_P` and on the polynomial extensions of these, so that the jacobian criterion
(`Hironaka/Compat/JacobianMinors.lean`) can be applied in the completion.  Mathlib has no
extension of derivations to localizations or completions; here are the general statements.

* `exists_derivation_of_isLocalization`: a `k`-derivation of `A` extends to every localization
  `B = S⁻¹A` (the quotient rule, constructed through the dual numbers `B[ε]`: `a ↦ a + D(a)ε` sends
  `S` to units, so it extends to `B`);
* `exists_derivation_adicCompletion`: a `k`-derivation `D` of `Λ` extends to the `I`-adic completion
  (continuity: `D(Iⁿ⁺¹) ⊆ Iⁿ`, `D̂(lim cₙ) = lim D(c_{n+1})`);
* `map_mapCoeffsDerivation`, `pderiv_map` (Mathlib): the coefficientwise derivation of a polynomial
  ring commutes with the base change of coefficients.
-/

@[expose] public section

open TrivSqZeroExt

noncomputable section

namespace Hironaka

universe u

section

variable {k A B : Type*} [CommRing k] [CommRing A] [Algebra k A] [CommRing B] [Algebra A B]

/-- The ring map `a ↦ a + D(a) ε` from `A` to the dual numbers over `B` defined by a derivation. -/
def derivationToDual (D : Derivation k A A) : A →+* TrivSqZeroExt B B where
  toFun a := inl (algebraMap A B a) + inr (algebraMap A B (D a))
  map_one' := by
    ext
    · simp
    · simp only [snd_add, snd_inl, snd_inr, snd_one]
      rw [Derivation.map_one_eq_zero, map_zero]; simp
  map_mul' a b := by
    ext
    · simp
    · simp only [snd_add, snd_inl, snd_inr, snd_mul, fst_add, fst_inl, fst_inr, Derivation.leibniz,
        map_add, map_mul, smul_eq_mul, zero_add, add_zero, MulOpposite.smul_eq_mul_unop,
        MulOpposite.unop_op, mul_comm (algebraMap A B (D a))]
  map_zero' := by
    ext
    · simp
    · simp only [snd_add, snd_inl, snd_inr, snd_zero, map_zero, add_zero]
  map_add' a b := by
    ext
    · simp
    · simp only [snd_add, snd_inl, snd_inr, map_add, zero_add]

theorem fst_derivationToDual (D : Derivation k A A) (a : A) :
    (derivationToDual (B := B) D a).fst = algebraMap A B a := by
  show (inl (algebraMap A B a) + inr (algebraMap A B (D a)) : TrivSqZeroExt B B).fst = _
  simp only [fst_add, fst_inl, fst_inr, add_zero]

theorem snd_derivationToDual (D : Derivation k A A) (a : A) :
    (derivationToDual (B := B) D a).snd = algebraMap A B (D a) := by
  show (inl (algebraMap A B a) + inr (algebraMap A B (D a)) : TrivSqZeroExt B B).snd = _
  simp only [snd_add, snd_inl, snd_inr, zero_add]

variable [Algebra k B] [IsScalarTower k A B]

/-- **A derivation extends to a localization.**

Deviation from the paper (gap filled): footnote 30 (p. 161) says only "For this case, will suffice
the jacobian criterion for simplicity"; applying it in the completion needs the derivations of the
polynomial ring to act on the local ring, shown here. -/
@[blueprint "lem:derivation-localization"
  (statement := /-- Let $D$ be a $k$-derivation of a ring $A$ and $B=S^{-1}A$ a localization of
    $A$. Then $D$ extends to a $k$-derivation of $B$. -/)
  (proof := /-- The quotient rule; formally, $a\mapsto a+D(a)\varepsilon$ is a ring homomorphism
    $A\to B[\varepsilon]/(\varepsilon^2)$ sending $S$ to units, hence extends to $B$, and the
    $\varepsilon$-part is the derivation. \textbf{Deviation from the paper (gap filled).}
    Footnote~30 says only ``For this case, will suffice the jacobian criterion for
    simplicity''. -/)
  (latexEnv := "lemma")]
theorem exists_derivation_of_isLocalization (S : Submonoid A) [IsLocalization S B]
    (D : Derivation k A A) :
    ∃ D' : Derivation k B B, ∀ a, D' (algebraMap A B a) = algebraMap A B (D a) := by
  have hunit : ∀ s : S, IsUnit (derivationToDual (B := B) D (s : A)) := fun s => by
    rw [isUnit_iff_isUnit_fst, fst_derivationToDual]
    exact IsLocalization.map_units B s
  let Φ : B →+* TrivSqZeroExt B B := IsLocalization.lift hunit
  have hΦ : ∀ a, Φ (algebraMap A B a) = derivationToDual D a := fun a => IsLocalization.lift_eq _ a
  have hfst : ∀ b, (Φ b).fst = b := by
    intro b
    have : ((fstHom B B B : TrivSqZeroExt B B →ₐ[B] B) : TrivSqZeroExt B B →+* B).comp Φ =
        RingHom.id B := by
      refine IsLocalization.ringHom_ext S ?_
      ext a
      simp [hΦ, fst_derivationToDual]
    exact congrArg (fun f => f b) this
  have hsmul : ∀ (c : k) (b : B), (Φ (c • b)).snd = c • (Φ b).snd := by
    intro c b
    have h1 : c • b = algebraMap A B (algebraMap k A c) * b := by
      rw [Algebra.smul_def, IsScalarTower.algebraMap_apply k A B]
    rw [h1, map_mul, hΦ, snd_mul, fst_derivationToDual, hfst, snd_derivationToDual,
      Derivation.map_algebraMap, map_zero, smul_zero, add_zero,
      smul_eq_mul, Algebra.smul_def c, IsScalarTower.algebraMap_apply k A B]
  let D' : Derivation k B B := Derivation.mk'
    { toFun := fun b => (Φ b).snd
      map_add' := fun x y => by simp [snd_add]
      map_smul' := fun c b => by simpa using hsmul c b }
    (fun x y => by
      show (Φ (x * y)).snd = x • (Φ y).snd + y • (Φ x).snd
      rw [map_mul, snd_mul, hfst, hfst]
      simp only [smul_eq_mul, MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op]
      ring)
  refine ⟨D', fun a => ?_⟩
  show (Φ (algebraMap A B a)).snd = _
  rw [hΦ, snd_derivationToDual]

end

section Completion

variable {k Λ : Type*} [CommRing k] [CommRing Λ] [Algebra k Λ] (I : Ideal Λ)
  (D : Derivation k Λ Λ)

/-- A derivation maps `Iⁿ⁺¹` into `Iⁿ`. -/
theorem derivation_mem_pow_of_mem_pow_succ {n : ℕ} {z : Λ} (hz : z ∈ I ^ (n + 1)) :
    D z ∈ I ^ n := by
  induction n generalizing z with
  | zero => simp
  | succ n ih =>
    rw [pow_succ'] at hz
    refine Submodule.mul_induction_on hz (fun x hx y hy => ?_) (fun x y hx hy => ?_)
    · rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]
      refine add_mem ?_ (Ideal.mul_mem_right _ _ hy)
      rw [pow_succ']
      exact Ideal.mul_mem_mul hx (ih hy)
    · rw [map_add]
      exact add_mem hx hy

theorem smodEq_pow_smul_top_iff {x y : Λ} {n : ℕ} :
    x ≡ y [SMOD (I ^ n • ⊤ : Submodule Λ Λ)] ↔ x - y ∈ I ^ n := by
  rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top]

/-- The derivative of a Cauchy sequence, shifted by one step: `(D c)ₙ = D (c_{n+1})`. -/
def AdicCauchySequence.shiftDerivation (c : AdicCompletion.AdicCauchySequence I Λ) :
    AdicCompletion.AdicCauchySequence I Λ :=
  AdicCompletion.AdicCauchySequence.mk I Λ (fun n => D (c.val (n + 1))) (fun n => by
    rw [smodEq_pow_smul_top_iff, ← map_sub]
    apply derivation_mem_pow_of_mem_pow_succ
    have := c.property (Nat.le_succ (n + 1))
    rw [smodEq_pow_smul_top_iff] at this
    exact this)

theorem adicCompletion_mk_eq_zero_iff (c : AdicCompletion.AdicCauchySequence I Λ) :
    AdicCompletion.mk I Λ c = 0 ↔ ∀ n, c.val n ∈ I ^ n := by
  constructor
  · intro h n
    have := congrArg (fun x => x.val n) h
    simp only [AdicCompletion.mk_apply_coe, Submodule.mkQ_apply, AdicCompletion.val_zero,
      Pi.zero_apply] at this
    rw [Submodule.Quotient.mk_eq_zero, smul_eq_mul, Ideal.mul_top] at this
    exact this
  · intro h
    ext n
    simp only [AdicCompletion.mk_apply_coe, Submodule.mkQ_apply, AdicCompletion.val_zero,
      Pi.zero_apply]
    rw [Submodule.Quotient.mk_eq_zero, smul_eq_mul, Ideal.mul_top]
    exact h n

theorem AdicCauchySequence.shiftDerivation_apply (c : AdicCompletion.AdicCauchySequence I Λ)
    (n : ℕ) : (AdicCauchySequence.shiftDerivation I D c).val n = D (c.val (n + 1)) := rfl

theorem mk_shiftDerivation_eq_zero (c : AdicCompletion.AdicCauchySequence I Λ)
    (h : AdicCompletion.mk I Λ c = 0) :
    AdicCompletion.mk I Λ (AdicCauchySequence.shiftDerivation I D c) = 0 := by
  rw [adicCompletion_mk_eq_zero_iff] at h ⊢
  intro n
  rw [AdicCauchySequence.shiftDerivation_apply]
  exact derivation_mem_pow_of_mem_pow_succ I D (h (n + 1))

theorem shiftDerivation_sub (a b : AdicCompletion.AdicCauchySequence I Λ) :
    AdicCauchySequence.shiftDerivation I D (a - b) =
      AdicCauchySequence.shiftDerivation I D a - AdicCauchySequence.shiftDerivation I D b :=
  Subtype.ext (funext fun _ => map_sub D _ _)

/-- The extension of a derivation `D` of `Λ` to the `I`-adic completion (as a function). -/
def completionDerivationFun (x : AdicCompletion I Λ) : AdicCompletion I Λ :=
  AdicCompletion.mk I Λ (AdicCauchySequence.shiftDerivation I D
    (Classical.choose (AdicCompletion.mk_surjective I Λ x)))

theorem completionDerivationFun_mk (c : AdicCompletion.AdicCauchySequence I Λ) :
    completionDerivationFun I D (AdicCompletion.mk I Λ c) =
      AdicCompletion.mk I Λ (AdicCauchySequence.shiftDerivation I D c) := by
  have h := Classical.choose_spec (AdicCompletion.mk_surjective I Λ (AdicCompletion.mk I Λ c))
  set c' := Classical.choose (AdicCompletion.mk_surjective I Λ (AdicCompletion.mk I Λ c))
  have h0 : AdicCompletion.mk I Λ (c' - c) = 0 := by rw [map_sub, h, sub_self]
  have := mk_shiftDerivation_eq_zero I D (c' - c) h0
  rw [shiftDerivation_sub, map_sub, sub_eq_zero] at this
  exact this

theorem completionDerivationFun_add (x y : AdicCompletion I Λ) :
    completionDerivationFun I D (x + y) =
      completionDerivationFun I D x + completionDerivationFun I D y := by
  induction x using AdicCompletion.induction_on with | h c =>
  induction y using AdicCompletion.induction_on with | h c' =>
  rw [← map_add, completionDerivationFun_mk, completionDerivationFun_mk,
    completionDerivationFun_mk, ← map_add]
  congr 1
  exact Subtype.ext (funext fun n => map_add D _ _)

theorem completionDerivationFun_mul (x y : AdicCompletion I Λ) :
    completionDerivationFun I D (x * y) =
      x * completionDerivationFun I D y + y * completionDerivationFun I D x := by
  induction x using AdicCompletion.induction_on with | h c =>
  induction y using AdicCompletion.induction_on with | h c' =>
  have hmul : ∀ a b : AdicCompletion.AdicCauchySequence I Λ,
      AdicCompletion.mk I Λ a * AdicCompletion.mk I Λ b = AdicCompletion.mk I Λ (a * b) :=
    fun a b => ((AdicCompletion.mkₐ I).map_mul a b).symm
  rw [hmul c c', completionDerivationFun_mk, completionDerivationFun_mk,
    completionDerivationFun_mk, hmul, hmul, ← map_add, ← sub_eq_zero, ← map_sub,
    adicCompletion_mk_eq_zero_iff]
  intro n
  have hc : c.val (n + 1) - c.val n ∈ I ^ n := by
    have := c.property (Nat.le_succ n)
    rw [smodEq_pow_smul_top_iff] at this
    simpa using (Ideal.neg_mem_iff _).mpr this
  have hc' : c'.val (n + 1) - c'.val n ∈ I ^ n := by
    have := c'.property (Nat.le_succ n)
    rw [smodEq_pow_smul_top_iff] at this
    simpa using (Ideal.neg_mem_iff _).mpr this
  have : (AdicCauchySequence.shiftDerivation I D (c * c') -
      (c * AdicCauchySequence.shiftDerivation I D c' +
        c' * AdicCauchySequence.shiftDerivation I D c)).val n =
      (c.val (n + 1) - c.val n) * D (c'.val (n + 1)) +
        (c'.val (n + 1) - c'.val n) * D (c.val (n + 1)) := by
    show D (c.val (n + 1) * c'.val (n + 1)) -
      (c.val n * D (c'.val (n + 1)) + c'.val n * D (c.val (n + 1))) = _
    rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]
    ring
  rw [this]
  exact add_mem (Ideal.mul_mem_right _ _ hc) (Ideal.mul_mem_right _ _ hc')

theorem completionDerivationFun_algebraMap (a : Λ) :
    completionDerivationFun I D (algebraMap Λ (AdicCompletion I Λ) a) =
      algebraMap Λ (AdicCompletion I Λ) (D a) := by
  have h1 : ∀ b : Λ, algebraMap Λ (AdicCompletion I Λ) b =
      AdicCompletion.mk I Λ (algebraMap Λ (AdicCompletion.AdicCauchySequence I Λ) b) := fun b =>
    ((AdicCompletion.mkₐ I).commutes b).symm
  rw [h1, completionDerivationFun_mk, h1]
  congr 1

/-- **A derivation extends to the adic completion**: for a `k`-derivation `D` of `Λ`, the formula
`D̂(lim cₙ) = lim D(c_{n+1})` defines a `k`-derivation of `Λ̂ = AdicCompletion I Λ` (continuity:
`D(Iⁿ⁺¹) ⊆ Iⁿ`), compatible with the canonical map `Λ → Λ̂`.

Deviation from the paper (gap filled): see `exists_derivation_of_isLocalization`. -/
@[blueprint "lem:derivation-completion"
  (statement := /-- Let $D$ be a $k$-derivation of a ring $\Lambda$ and $I$ an ideal. Then $D$
    extends to a $k$-derivation of the $I$-adic completion $\hat\Lambda$, compatibly with
    $\Lambda\to\hat\Lambda$. -/)
  (proof := /-- A derivation maps $I^{n+1}$ into $I^n$, so $D(\lim c_n)=\lim D(c_{n+1})$ is well
    defined on $I$-adic Cauchy sequences and respects the zero sequences; the Leibniz rule holds
    because $c_{n+1}-c_n\in I^n$. \textbf{Deviation from the paper (gap filled).}
    Footnote~30 says only ``For this case, will suffice the jacobian criterion for
    simplicity''. -/)
  (latexEnv := "lemma")]
theorem exists_derivation_adicCompletion :
    ∃ D' : Derivation k (AdicCompletion I Λ) (AdicCompletion I Λ),
      ∀ a : Λ, D' (algebraMap Λ (AdicCompletion I Λ) a) =
        algebraMap Λ (AdicCompletion I Λ) (D a) := by
  have hsmul : ∀ (c : k) (x : AdicCompletion I Λ), completionDerivationFun I D (c • x) =
      c • completionDerivationFun I D x := by
    intro c x
    have h1 : c • x = algebraMap Λ (AdicCompletion I Λ) (algebraMap k Λ c) * x := by
      rw [← Algebra.smul_def]
      exact (algebraMap_smul Λ c x).symm
    have h0 : completionDerivationFun I D (algebraMap Λ (AdicCompletion I Λ) (algebraMap k Λ c)) =
        0 := by
      rw [completionDerivationFun_algebraMap, Derivation.map_algebraMap, map_zero]
    rw [h1, completionDerivationFun_mul, h0, mul_zero, add_zero]
    rw [← Algebra.smul_def, algebraMap_smul]
  refine ⟨Derivation.mk'
    { toFun := completionDerivationFun I D
      map_add' := completionDerivationFun_add I D
      map_smul' := hsmul }
    (fun x y => by
      show completionDerivationFun I D (x * y) = x • completionDerivationFun I D y +
        y • completionDerivationFun I D x
      rw [completionDerivationFun_mul]
      simp [smul_eq_mul]), fun a => ?_⟩
  exact completionDerivationFun_algebraMap I D a

end Completion

section LocalizationCompletion

open IsLocalRing

/-- **A derivation of `T` extends to the completion of `T_P`.**  For a `k`-derivation `D` of a
`k`-algebra `T` and a prime `P`, there is a `k`-derivation `D̂` of the completion
`(T_P)^ = AdicCompletion (maximalIdeal T_P) T_P` with `D̂(t) = D(t)` for `t ∈ T`.  (Localization,
then completion.) -/
theorem exists_derivation_adicCompletion_localization {k T : Type u} [CommRing k] [CommRing T]
    [Algebra k T] (P : Ideal T) [P.IsPrime] (D : Derivation k T T) :
    ∃ D' : Derivation k (AdicCompletion (maximalIdeal (Localization.AtPrime P))
        (Localization.AtPrime P)) (AdicCompletion (maximalIdeal (Localization.AtPrime P))
        (Localization.AtPrime P)),
      ∀ t : T, D' (algebraMap (Localization.AtPrime P) (AdicCompletion
          (maximalIdeal (Localization.AtPrime P)) (Localization.AtPrime P))
          (algebraMap T (Localization.AtPrime P) t)) =
        algebraMap (Localization.AtPrime P) (AdicCompletion (maximalIdeal (Localization.AtPrime P))
          (Localization.AtPrime P)) (algebraMap T (Localization.AtPrime P) (D t)) := by
  obtain ⟨D₁, hD₁⟩ := exists_derivation_of_isLocalization (B := Localization.AtPrime P)
    P.primeCompl D
  obtain ⟨D₂, hD₂⟩ := exists_derivation_adicCompletion (maximalIdeal (Localization.AtPrime P)) D₁
  refine ⟨D₂, fun t => ?_⟩
  rw [hD₂, hD₁]

end LocalizationCompletion

section MapCoeffs

variable {k R₀ R₁ σ : Type*} [CommRing k] [CommRing R₀] [CommRing R₁] [Algebra k R₀]
  [Algebra k R₁]

/-- The coefficientwise derivation of a polynomial ring commutes with a change of coefficients
compatible with the derivations. -/
theorem map_mapCoeffsDerivation (ρ : R₀ →+* R₁) (d₀ : Derivation k R₀ R₀)
    (d₁ : Derivation k R₁ R₁) (h : ∀ a, d₁ (ρ a) = ρ (d₀ a)) (p : MvPolynomial σ R₀) :
    MvPolynomial.map ρ (mapCoeffsDerivation k σ d₀ p) =
      mapCoeffsDerivation k σ d₁ (MvPolynomial.map ρ p) := by
  ext m
  show ((MvPolynomial.map ρ) (mapCoeffsFun σ d₀ p)).coeff m =
    (mapCoeffsFun σ d₁ (MvPolynomial.map ρ p)).coeff m
  rw [MvPolynomial.coeff_map, coeff_mapCoeffsFun, coeff_mapCoeffsFun, MvPolynomial.coeff_map, h]

/-- **Extension to `R₁[σ]_Q`** (coefficientwise part).  Let `ρ : R₀ → R₁` be a ring homomorphism
compatible with `k`-derivations `d₀`, `d₁`, and `Q` a prime of `R₁[σ]`.  Then the coefficientwise
derivation `d₀` of `R₀[σ]` extends, along `R₀[σ] → R₁[σ] → R₁[σ]_Q`, to a `k`-derivation of the
local ring `R₁[σ]_Q`. -/
theorem exists_derivation_localization_mvPolynomial_mapCoeffs (ρ : R₀ →+* R₁)
    (d₀ : Derivation k R₀ R₀) (d₁ : Derivation k R₁ R₁) (h : ∀ a, d₁ (ρ a) = ρ (d₀ a))
    (Q : Ideal (MvPolynomial σ R₁)) [Q.IsPrime] :
    ∃ D : Derivation k (Localization.AtPrime Q) (Localization.AtPrime Q),
      ∀ F : MvPolynomial σ R₀,
        D (algebraMap (MvPolynomial σ R₁) (Localization.AtPrime Q) (MvPolynomial.map ρ F)) =
          algebraMap (MvPolynomial σ R₁) (Localization.AtPrime Q)
            (MvPolynomial.map ρ (mapCoeffsDerivation k σ d₀ F)) := by
  obtain ⟨D, hD⟩ := exists_derivation_of_isLocalization (B := Localization.AtPrime Q) Q.primeCompl
    (mapCoeffsDerivation k σ d₁)
  refine ⟨D, fun F => ?_⟩
  rw [hD, map_mapCoeffsDerivation ρ d₀ d₁ h]

omit [Algebra k R₀] in
/-- **Extension to `R₁[σ]_Q`** (polynomial variables).  The partial derivative `∂/∂y_a` of `R₀[σ]`
extends, along `R₀[σ] → R₁[σ] → R₁[σ]_Q`, to a `k`-derivation of the local ring `R₁[σ]_Q`. -/
theorem exists_derivation_localization_mvPolynomial_pderiv (ρ : R₀ →+* R₁)
    (Q : Ideal (MvPolynomial σ R₁)) [Q.IsPrime] (a : σ) :
    ∃ D : Derivation k (Localization.AtPrime Q) (Localization.AtPrime Q),
      ∀ F : MvPolynomial σ R₀,
        D (algebraMap (MvPolynomial σ R₁) (Localization.AtPrime Q) (MvPolynomial.map ρ F)) =
          algebraMap (MvPolynomial σ R₁) (Localization.AtPrime Q)
            (MvPolynomial.map ρ (MvPolynomial.pderiv a F)) := by
  obtain ⟨D, hD⟩ := exists_derivation_of_isLocalization (B := Localization.AtPrime Q) Q.primeCompl
    ((MvPolynomial.pderiv a :
      Derivation R₁ (MvPolynomial σ R₁) (MvPolynomial σ R₁)).restrictScalars k)
  refine ⟨D, fun F => ?_⟩
  rw [hD]
  simp only [Derivation.restrictScalars_apply]
  rw [MvPolynomial.pderiv_map]

end MapCoeffs

end Hironaka
