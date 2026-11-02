/-
Copyright (c) 2026 Daattavya Aggarwal, Minhyong Kim, Oisin Kim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daattavya Aggarwal, Minhyong Kim, Oisin Kim
-/
module

public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Localization.Submodule
public import Mathlib.RingTheory.MvPowerSeries.Basic
public import Architect
public import Hironaka.Compat.ClassBCompleteTransport

/-!
# Compatibility layer: the kernel of `Λ̂[y] → B ⊗_R R̂` in the complete case of (c)

Footnote 31 (p. 161).  With the notation of `ClassBCompleteTransport.lean` (`θ : Λ̂[y] → B ⊗_R R̂`,
`ρ : T₁ → Λ̂[y]`, `ψ₁ : T₁ → B`, `K₁ = ker ψ₁`): `ker θ = K₁Λ̂[y]`, i.e.
`B ⊗_R R̂ ≅ Λ̂[y]/K₁Λ̂[y]`.  The inclusion `K₁Λ̂[y] ⊆ ker θ` is `θ ∘ ρ = ψ₁ ⊗ 1`; for the converse,
a ring homomorphism `χ : B ⊗_R R̂ → Λ̂[y]/K₁Λ̂[y]` with `χ ∘ θ = (quotient map)` is built from the
three `R`-algebra maps `R → Q`, `B → Q`, `R̂ → Q` (`Q = Λ̂[y]/K₁Λ̂[y]`).
-/

@[expose] public section

open IsLocalRing

noncomputable section

namespace Hironaka

universe u

section Kernel

open PowerSeriesPolynomialRing
open scoped TensorProduct

variable {k : Type u} [Field k] {n m : ℕ} (P : Ideal (PowerSeriesPolynomialRing k n m))
  [P.IsPrime] {R : Type u} [CommRing R] [IsLocalRing R] (φ : Localization.AtPrime P →+* R)
  (hφ : Function.Surjective φ) {l : ℕ} {B : Type u} [CommRing B] [Algebra R B]
  (ψ : MvPolynomial (Fin l) R →ₐ[R] B)

/-- `K₁ = ker (ψ₁ : T₁ → B)`. -/
abbrev presentationKernel : Ideal (PowerSeriesPolynomialRing k n (m + l)) :=
  RingHom.ker (presentationHom P φ ψ)

/-- `K₁Λ̂[y]`, the extension of `K₁` along `ρ : T₁ → Λ̂[y]`. -/
abbrev presentationKernelMap : Ideal (MvPolynomial (Fin l) (completionAtPrime P)) :=
  (presentationKernel P φ ψ).map (completionExtensionHom P l)

/-- `ρ (incl a) = C (a)`: the inclusion `T → T₁` followed by `ρ` is the coefficient map. -/
theorem completionExtensionHom_inclusion (a : PowerSeriesPolynomialRing k n m) :
    completionExtensionHom P l (powerSeriesPolynomialRingInclusion l a) =
      MvPolynomial.C (algebraMap (PowerSeriesPolynomialRing k n m) (completionAtPrime P) a) :=
  extensionHom_powerSeriesPolynomialRingInclusion _ a

/-- `Λ → Q = Λ̂[y]/K₁Λ̂[y]`: the coefficient map. -/
abbrev quotientIota : Localization.AtPrime P →+*
    (MvPolynomial (Fin l) (completionAtPrime P) ⧸ presentationKernelMap P φ ψ) :=
  (Ideal.Quotient.mk (presentationKernelMap P φ ψ)).comp
    (MvPolynomial.C.comp (algebraMap (Localization.AtPrime P) (completionAtPrime P)))

omit [IsLocalRing R] in
/-- The coefficient map `Λ → Λ̂[y]/K₁Λ̂[y]` kills `ker φ`. -/
theorem quotientIota_eq_zero_of_map_eq_zero (x : Localization.AtPrime P) (hx : φ x = 0) :
    quotientIota P φ ψ x = 0 := by
  obtain ⟨⟨a, s⟩, hxs⟩ := IsLocalization.surj P.primeCompl x
  have h1 : toTarget P φ a = 0 := by
    have h : φ (x * algebraMap (PowerSeriesPolynomialRing k n m) (Localization.AtPrime P) s) =
        φ (algebraMap (PowerSeriesPolynomialRing k n m) (Localization.AtPrime P) a) := by
      rw [hxs]
    rw [map_mul, hx, zero_mul] at h
    exact h.symm
  have h2 : powerSeriesPolynomialRingInclusion l a ∈ presentationKernel P φ ψ := by
    rw [RingHom.mem_ker]
    show ψ (extensionHom (l := l) (toTarget P φ) (powerSeriesPolynomialRingInclusion l a)) = 0
    rw [extensionHom_powerSeriesPolynomialRingInclusion, h1, map_zero, map_zero]
  have h3 : quotientIota P φ ψ
      (algebraMap (PowerSeriesPolynomialRing k n m) (Localization.AtPrime P) a) = 0 := by
    show Ideal.Quotient.mk _ (MvPolynomial.C (algebraMap (Localization.AtPrime P)
      (completionAtPrime P) (algebraMap (PowerSeriesPolynomialRing k n m)
        (Localization.AtPrime P) a))) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem, ← IsScalarTower.algebraMap_apply
      (PowerSeriesPolynomialRing k n m) (Localization.AtPrime P) (completionAtPrime P),
      ← completionExtensionHom_inclusion P a]
    exact Ideal.mem_map_of_mem _ h2
  have hu : IsUnit (quotientIota P φ ψ
      (algebraMap (PowerSeriesPolynomialRing k n m) (Localization.AtPrime P) s)) :=
    (IsLocalization.map_units (Localization.AtPrime P) s).map _
  have h4 : quotientIota P φ ψ x * quotientIota P φ ψ
      (algebraMap (PowerSeriesPolynomialRing k n m) (Localization.AtPrime P) s) = 0 := by
    rw [← map_mul, hxs, h3]
  exact (hu.mul_left_eq_zero).mp h4

/-- `R → Q`, induced by `Λ → Q` (it kills `ker φ`). -/
abbrev quotientRingHomR : R →+*
    (MvPolynomial (Fin l) (completionAtPrime P) ⧸ presentationKernelMap P φ ψ) :=
  (Ideal.Quotient.lift (RingHom.ker φ) (quotientIota P φ ψ)
    (fun x hx => quotientIota_eq_zero_of_map_eq_zero P φ ψ x (RingHom.mem_ker.mp hx))).comp
    (RingHom.quotientKerEquivOfSurjective hφ).symm.toRingHom

omit [IsLocalRing R] in
theorem quotientRingHomR_apply (x : Localization.AtPrime P) :
    quotientRingHomR P φ hφ ψ (φ x) = quotientIota P φ ψ x := by
  have h : (RingHom.quotientKerEquivOfSurjective hφ).symm (φ x) =
      Ideal.Quotient.mk (RingHom.ker φ) x := by
    rw [RingEquiv.symm_apply_eq]
    rfl
  unfold quotientRingHomR
  rw [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, h]
  exact Ideal.Quotient.lift_mk _ _ _

/-- `Λ̂ → Q`, the coefficient map of `Λ̂[y]/K₁Λ̂[y]`. -/
abbrev quotientIotaHat : completionAtPrime P →+*
    (MvPolynomial (Fin l) (completionAtPrime P) ⧸ presentationKernelMap P φ ψ) :=
  (Ideal.Quotient.mk (presentationKernelMap P φ ψ)).comp MvPolynomial.C

omit [IsLocalRing R] in
theorem map_ker_le_ker_quotientIotaHat :
    (RingHom.ker φ).map (algebraMap (Localization.AtPrime P) (completionAtPrime P)) ≤
      RingHom.ker (quotientIotaHat P φ ψ) :=
  Ideal.map_le_iff_le_comap.mpr fun x hx => by
    rw [Ideal.mem_comap, RingHom.mem_ker]
    exact quotientIota_eq_zero_of_map_eq_zero P φ ψ x (RingHom.mem_ker.mp hx)

/-- The isomorphism `R̂ ≅ Λ̂/(ker φ)Λ̂` of `exists_ringEquiv_adicCompletion_quotient_comp`. -/
def completionQuotientEquiv : AdicCompletion (maximalIdeal R) R ≃+*
    (AdicCompletion (maximalIdeal (Localization.AtPrime P)) (Localization.AtPrime P) ⧸
      (RingHom.ker φ).map (algebraMap (Localization.AtPrime P) (completionAtPrime P))) :=
  (exists_ringEquiv_adicCompletion_quotient_comp φ hφ).choose

theorem completionQuotientEquiv_completionMap (x : completionAtPrime P) :
    completionQuotientEquiv P φ hφ (completionMap φ hφ x) = Ideal.Quotient.mk _ x :=
  (exists_ringEquiv_adicCompletion_quotient_comp φ hφ).choose_spec x

/-- `R̂ → Q`, via `R̂ ≅ Λ̂/(ker φ)Λ̂`. -/
def quotientRingHomRHat : AdicCompletion (maximalIdeal R) R →+*
    (MvPolynomial (Fin l) (completionAtPrime P) ⧸ presentationKernelMap P φ ψ) :=
  (Ideal.Quotient.lift
    ((RingHom.ker φ).map (algebraMap (Localization.AtPrime P) (completionAtPrime P)))
    (quotientIotaHat P φ ψ) (fun _ ha => RingHom.mem_ker.mp
      (map_ker_le_ker_quotientIotaHat P φ ψ ha))).comp
    (completionQuotientEquiv P φ hφ).toRingHom

theorem quotientRingHomRHat_completionMap (x : completionAtPrime P) :
    quotientRingHomRHat P φ hφ ψ (completionMap φ hφ x) = quotientIotaHat P φ ψ x := by
  unfold quotientRingHomRHat
  rw [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe,
    completionQuotientEquiv_completionMap]
  exact Ideal.Quotient.lift_mk _ _ _

theorem quotientRingHomRHat_algebraMap (r : R) :
    quotientRingHomRHat P φ hφ ψ (algebraMap R (AdicCompletion (maximalIdeal R) R) r) =
      quotientRingHomR P φ hφ ψ r := by
  obtain ⟨x, rfl⟩ := hφ r
  rw [← completionMap_algebraMap φ hφ x, quotientRingHomRHat_completionMap,
    quotientRingHomR_apply]
  rfl

/-- `R[y] → Q`: `R → Q` on coefficients and `y_a ↦ y_a`. -/
abbrev quotientRingHomPoly : MvPolynomial (Fin l) R →+*
    (MvPolynomial (Fin l) (completionAtPrime P) ⧸ presentationKernelMap P φ ψ) :=
  MvPolynomial.eval₂Hom (quotientRingHomR P φ hφ ψ)
    (fun a => Ideal.Quotient.mk _ (MvPolynomial.X a))

omit [IsLocalRing R] in
theorem quotientRingHomR_toTarget (t : PowerSeriesPolynomialRing k n m) :
    quotientRingHomR P φ hφ ψ (toTarget P φ t) =
      Ideal.Quotient.mk (presentationKernelMap P φ ψ)
        (MvPolynomial.C (algebraMap (PowerSeriesPolynomialRing k n m)
          (completionAtPrime P) t)) := by
  show quotientRingHomR P φ hφ ψ (φ (algebraMap _ _ t)) = _
  rw [quotientRingHomR_apply, IsScalarTower.algebraMap_apply
    (PowerSeriesPolynomialRing k n m) (Localization.AtPrime P) (completionAtPrime P)]
  rfl

omit [IsLocalRing R] in
theorem quotientRingHomPoly_extensionHom (x : PowerSeriesPolynomialRing k n (m + l)) :
    quotientRingHomPoly P φ hφ ψ (extensionHom (l := l) (toTarget P φ) x) =
      Ideal.Quotient.mk (presentationKernelMap P φ ψ) (completionExtensionHom P l x) := by
  have hXx : ∀ i : Fin (m + l),
      quotientRingHomPoly P φ hφ ψ (extensionHom (l := l) (toTarget P φ) (X i)) =
        Ideal.Quotient.mk (presentationKernelMap P φ ψ)
          (completionExtensionHom P l (X i)) := by
    intro i
    induction i using Fin.addCases with
    | left j =>
      show quotientRingHomPoly P φ hφ ψ (extensionHom (l := l) (toTarget P φ)
        (X (Fin.castAdd l j))) = Ideal.Quotient.mk _ (extensionHom (l := l) _ (X (Fin.castAdd l j)))
      rw [extensionHom_X_castAdd, extensionHom_X_castAdd]
      simp only [quotientRingHomPoly, MvPolynomial.eval₂Hom_C]
      exact quotientRingHomR_toTarget P φ hφ ψ (X j)
    | right a =>
      show quotientRingHomPoly P φ hφ ψ (extensionHom (l := l) (toTarget P φ)
        (X (Fin.natAdd m a))) = Ideal.Quotient.mk _ (extensionHom (l := l) _ (X (Fin.natAdd m a)))
      rw [extensionHom_X_natAdd, extensionHom_X_natAdd]
      simp only [quotientRingHomPoly, MvPolynomial.eval₂Hom_X']
  refine induction_on_C_X (k := k) (n := n) (m := m + l)
    (P := fun x => quotientRingHomPoly P φ hφ ψ (extensionHom (l := l) (toTarget P φ) x) =
      Ideal.Quotient.mk (presentationKernelMap P φ ψ) (completionExtensionHom P l x)) x
    (fun c => ?_) (fun p q hp hq => ?_) (fun p i hp => ?_)
  · rw [extensionHom_C, extensionHom_C]
    simp only [quotientRingHomPoly, MvPolynomial.eval₂Hom_C]
    exact quotientRingHomR_toTarget P φ hφ ψ (C c)
  · rw [RingHom.map_add, RingHom.map_add, hp, hq, RingHom.map_add, RingHom.map_add]
  · rw [RingHom.map_mul, RingHom.map_mul, RingHom.map_mul, RingHom.map_mul, hp, hXx]

omit [IsLocalRing R] in
/-- `ker ψ ⊆ ker (R[y] → Q)`: an element `F` of `ker ψ` becomes, after multiplication by a unit
`τ_R(u)`, the image of `F' ∈ K₁`. -/
theorem quotientRingHomPoly_eq_zero_of_map_eq_zero (F : MvPolynomial (Fin l) R) (hF : ψ F = 0) :
    quotientRingHomPoly P φ hφ ψ F = 0 := by
  obtain ⟨u, hu, F', hF'⟩ := exists_mul_C_mem_range_extensionHom P φ hφ F
  have h1 : F' ∈ presentationKernel P φ ψ := by
    rw [RingHom.mem_ker]
    show ψ (extensionHom (l := l) (toTarget P φ) F') = 0
    rw [hF', map_mul, hF, zero_mul]
  have h2 : Ideal.Quotient.mk (presentationKernelMap P φ ψ) (completionExtensionHom P l F') = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_map_of_mem _ h1)
  rw [← quotientRingHomPoly_extensionHom P φ hφ ψ, hF', map_mul] at h2
  have hu' : IsUnit (quotientRingHomPoly P φ hφ ψ (MvPolynomial.C (toTarget P φ u))) := by
    have : IsUnit (toTarget P φ u) :=
      (IsLocalization.map_units (Localization.AtPrime P) (⟨u, hu⟩ : P.primeCompl)).map φ
    simpa [quotientRingHomPoly] using this.map (quotientRingHomR P φ hφ ψ)
  exact (hu'.mul_left_eq_zero).mp h2

/-- `B → Q`, induced by `R[y] → Q` and the surjection `ψ : R[y] ↠ B`. -/
def quotientRingHomB (hψ : Function.Surjective ψ) : B →+*
    (MvPolynomial (Fin l) (completionAtPrime P) ⧸ presentationKernelMap P φ ψ) :=
  (Ideal.Quotient.lift (RingHom.ker ψ.toRingHom) (quotientRingHomPoly P φ hφ ψ)
    (fun F hF => quotientRingHomPoly_eq_zero_of_map_eq_zero P φ hφ ψ F
      (RingHom.mem_ker.mp hF))).comp
    (RingHom.quotientKerEquivOfSurjective (f := ψ.toRingHom) hψ).symm.toRingHom

omit [IsLocalRing R] in
theorem quotientRingHomB_apply (hψ : Function.Surjective ψ) (F : MvPolynomial (Fin l) R) :
    quotientRingHomB P φ hφ ψ hψ (ψ F) = quotientRingHomPoly P φ hφ ψ F := by
  have h : (RingHom.quotientKerEquivOfSurjective (f := ψ.toRingHom) hψ).symm (ψ.toRingHom F) =
      Ideal.Quotient.mk (RingHom.ker ψ.toRingHom) F := by
    rw [RingEquiv.symm_apply_eq]
    rfl
  show quotientRingHomB P φ hφ ψ hψ (ψ.toRingHom F) = _
  unfold quotientRingHomB
  rw [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, h]
  exact Ideal.Quotient.lift_mk _ _ _

omit [IsLocalRing R] in
/-- `B → Q` is `R`-linear for the structure `R → Q` of `quotientRingHomR`. -/
theorem quotientRingHomB_algebraMap (hψ : Function.Surjective ψ) (r : R) :
    quotientRingHomB P φ hφ ψ hψ (algebraMap R B r) = quotientRingHomR P φ hφ ψ r := by
  rw [← ψ.commutes r, MvPolynomial.algebraMap_eq, quotientRingHomB_apply]
  simp [quotientRingHomPoly]

/-- `χ : B ⊗_R R̂ → Q = Λ̂[y]/K₁Λ̂[y]`, built from `B → Q` and `R̂ → Q` (both `R`-algebra maps for
the structure `R → Q` of `quotientRingHomR`). -/
def tensorQuotientHom (hψ : Function.Surjective ψ) :
    B ⊗[R] AdicCompletion (maximalIdeal R) R →+*
      (MvPolynomial (Fin l) (completionAtPrime P) ⧸ presentationKernelMap P φ ψ) :=
  letI : Algebra R (MvPolynomial (Fin l) (completionAtPrime P) ⧸ presentationKernelMap P φ ψ) :=
    (quotientRingHomR P φ hφ ψ).toAlgebra
  (Algebra.TensorProduct.lift
    ({ quotientRingHomB P φ hφ ψ hψ with
        commutes' := fun r => quotientRingHomB_algebraMap P φ hφ ψ hψ r } : B →ₐ[R] _)
    ({ quotientRingHomRHat P φ hφ ψ with
        commutes' := fun r => quotientRingHomRHat_algebraMap P φ hφ ψ r } :
      AdicCompletion (maximalIdeal R) R →ₐ[R] _)
    (fun _ _ => Commute.all _ _)).toRingHom

theorem tensorQuotientHom_tmul (hψ : Function.Surjective ψ) (b : B)
    (r : AdicCompletion (maximalIdeal R) R) :
    tensorQuotientHom P φ hφ ψ hψ (b ⊗ₜ[R] r) =
      quotientRingHomB P φ hφ ψ hψ b * quotientRingHomRHat P φ hφ ψ r := by
  rfl

/-- `χ ∘ θ` is the quotient map `Λ̂[y] → Λ̂[y]/K₁Λ̂[y]`. -/
theorem tensorQuotientHom_completionTensorHom (hψ : Function.Surjective ψ)
    (x : MvPolynomial (Fin l) (completionAtPrime P)) :
    tensorQuotientHom P φ hφ ψ hψ (completionTensorHom P φ hφ ψ x) =
      Ideal.Quotient.mk (presentationKernelMap P φ ψ) x := by
  have h : (tensorQuotientHom P φ hφ ψ hψ).comp (completionTensorHom P φ hφ ψ) =
      Ideal.Quotient.mk (presentationKernelMap P φ ψ) := by
    refine MvPolynomial.ringHom_ext (fun c => ?_) (fun a => ?_)
    · rw [RingHom.comp_apply, completionTensorHom_C, tensorQuotientHom_tmul, map_one, one_mul,
        quotientRingHomRHat_completionMap]
      rfl
    · rw [RingHom.comp_apply, completionTensorHom_X, tensorQuotientHom_tmul, map_one, mul_one,
        quotientRingHomB_apply]
      simp [quotientRingHomPoly]
  exact RingHom.congr_fun h x

/-- **The kernel of `θ : Λ̂[y] → B ⊗_R R̂`** is `K₁Λ̂[y]`. -/
@[blueprint "lem:ker-completion-tensor-hom"
  (statement := /-- Let $R=T_{\mathfrak P}/\ker\varphi$ be a quotient of $\Lambda=T_{\mathfrak P}$,
    $B=R[y]/I$ a finite type $R$-algebra presented by $\psi\colon R[y]\twoheadrightarrow B$, and
    $K_1=\ker(\psi_1\colon T_1\to B)$. The natural surjection $\theta\colon\hat\Lambda[y]\to
    B\otimes_R\hat R$ has kernel $K_1\hat\Lambda[y]$; that is,
    $B\otimes_R\hat R\cong\hat\Lambda[y]/K_1\hat\Lambda[y]$. -/)
  (proof := /-- $\theta\circ\rho=(B\to B\otimes\hat R)\circ\psi_1$ shows $K_1\hat\Lambda[y]\subseteq
    \ker\theta$. Conversely, since $\hat R\cong\hat\Lambda/(\ker\varphi)\hat\Lambda$
    (\cref{lem:completion-quotient}), the three $R$-algebra maps $R\to Q$, $B\to Q$ and
    $\hat R\to Q$ into $Q=\hat\Lambda[y]/K_1\hat\Lambda[y]$ (the second induced by $R[y]\to Q$
    after clearing denominators in $T\setminus P$, which become units) give a ring homomorphism
    $\chi\colon B\otimes_R\hat R\to Q$ with $\chi\circ\theta$ the quotient map, so $\ker\theta
    \subseteq K_1\hat\Lambda[y]$. \textbf{Deviation from the paper (gap filled).} This is the
    bookkeeping behind ``apply the jacobian criterion'' in footnote~31. -/)
  (proofUses := ["lem:completion-quotient"])
  (latexEnv := "lemma")]
theorem ker_completionTensorHom (hψ : Function.Surjective ψ) :
    RingHom.ker (completionTensorHom P φ hφ ψ) = presentationKernelMap P φ ψ := by
  refine le_antisymm (fun x hx => ?_) ?_
  · rw [RingHom.mem_ker] at hx
    rw [← Ideal.Quotient.eq_zero_iff_mem, ← tensorQuotientHom_completionTensorHom P φ hφ ψ hψ,
      hx, map_zero]
  · refine Ideal.map_le_iff_le_comap.mpr fun x hx => ?_
    rw [Ideal.mem_comap, RingHom.mem_ker,
      completionTensorHom_completionExtensionHom]
    have : presentationHom P φ ψ x = 0 := hx
    rw [this, map_zero]

end Kernel

end Hironaka
