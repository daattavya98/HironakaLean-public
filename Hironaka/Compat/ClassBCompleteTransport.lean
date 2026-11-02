/-
Copyright (c) 2026 Daattavya Aggarwal, Minhyong Kim, Oisin Kim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daattavya Aggarwal, Minhyong Kim, Oisin Kim
-/
module

public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
public import Mathlib.RingTheory.MvPowerSeries.Basic
public import Mathlib.RingTheory.TensorProduct.Maps
public import Architect
public import Hironaka.Compat.ClassBCompleteCore
public import Hironaka.Compat.QuotientCompletion
public import Hironaka.Compat.PowerSeriesPresentation

/-!
# Compatibility layer: identification of the local rings in the complete case of (c)

Footnote 31 (p. 161).  Helpers for `exists_localRingEquivs` (`ClassBCompleteCase.lean`): the
local rings of a finite type `R`-algebra `B` (and of `B ⊗_R R̂`) are local rings of quotients of
`T₁ = k⟦t⟧[x, y]` (resp. of `Λ̂[y]`):

* `exists_ringEquiv_localization_quotient_of_unit_denominators`: if `g : A₁ → B₁` is a ring
  homomorphism such that every `b ∈ B₁` is `g(x)/g(s)` with `g(s)` a unit, then
  `(B₁)_q ≅ (A₁)_{g⁻¹ q}/(ker g)`;
* the elements of `R[y]` have denominators from `T ∖ P` making them lie in the image of `T₁`.
-/

@[expose] public section

open IsLocalRing

noncomputable section

namespace Hironaka

universe u

section UnitDenominators

variable {A₁ B₁ : Type u} [CommRing A₁] [CommRing B₁] (g : A₁ →+* B₁)

/-- Local rings of a ring homomorphism with unit denominators. -/
@[blueprint "lem:localization-quotient-unit-denominators"
  (statement := /-- Let $g\colon A_1\to B_1$ be a ring homomorphism such that every $b\in B_1$ is
    $g(x)/g(s)$ with $g(s)$ a unit, and $q$ a prime of $B_1$. Then
    $(B_1)_q\cong(A_1)_{g^{-1}q}/(\ker g)(A_1)_{g^{-1}q}$, compatibly with $g$. -/)
  (proof := /-- The induced map $g_*\colon(A_1)_{g^{-1}q}\to(B_1)_q$ kills
    $(\ker g)(A_1)_{g^{-1}q}$.
    Injectivity on the quotient: if $g_*(a/s)=0$ then $wg(a)=0$ for some $w\notin q$; write
    $w=g(x)/g(t)$ with $g(t)$ a unit, so $x\notin g^{-1}q$ and $g(xa)=0$; thus $a/s=xa/(xs)$
    lies in $(\ker g)(A_1)_{g^{-1}q}$. Surjectivity: for $b/b'$ write $b=g(x)/g(s)$ and
    $b'=g(x')/g(s')$ with $g(s),g(s')$ units; then $b/b'=g_*(xs'/x's)$, where $x's\notin g^{-1}q$
    because $g(x's)=b'g(s')g(s)\notin q$. -/)
  (latexEnv := "lemma")]
theorem exists_ringEquiv_localization_quotient_of_unit_denominators
    (hg : ∀ b : B₁, ∃ s x : A₁, IsUnit (g s) ∧ b * g s = g x) (q : Ideal B₁) [q.IsPrime] :
    ∃ e : Localization.AtPrime q ≃+* (Localization.AtPrime (q.comap g) ⧸
        (RingHom.ker g).map (algebraMap A₁ (Localization.AtPrime (q.comap g)))),
      ∀ x : A₁, e (algebraMap B₁ (Localization.AtPrime q) (g x)) =
        Ideal.Quotient.mk _ (algebraMap A₁ (Localization.AtPrime (q.comap g)) x) := by
  let Q₁ := q.comap g
  let f : Localization.AtPrime Q₁ →+* Localization.AtPrime q :=
    Localization.localRingHom Q₁ q g rfl
  have hf : ∀ x, f (algebraMap A₁ _ x) = algebraMap B₁ _ (g x) :=
    fun x => Localization.localRingHom_to_map Q₁ q g rfl x
  have hker : (RingHom.ker g).map (algebraMap A₁ (Localization.AtPrime Q₁)) ≤ RingHom.ker f := by
    rw [Ideal.map_le_iff_le_comap]
    intro x hx
    rw [Ideal.mem_comap, RingHom.mem_ker, hf, RingHom.mem_ker.mp hx, map_zero]
  let fbar : (Localization.AtPrime Q₁ ⧸
      (RingHom.ker g).map (algebraMap A₁ (Localization.AtPrime Q₁)))
      →+* Localization.AtPrime q := Ideal.Quotient.lift _ f (fun a ha => hker ha)
  have hQ : ∀ x : A₁, x ∈ Q₁.primeCompl ↔ g x ∈ q.primeCompl := fun x => Iff.rfl
  have hunit_not_mem : ∀ x : A₁, IsUnit (g x) → g x ∈ q.primeCompl := fun x hx h =>
    q.ne_top_iff_one.mp (Ideal.IsPrime.ne_top ‹q.IsPrime›) (by
      obtain ⟨u, hu⟩ := hx
      have : (1 : B₁) = ((u⁻¹ : B₁ˣ) : B₁) * g x := by rw [← hu]; simp
      rw [this]
      exact Ideal.mul_mem_left _ _ h)
  have hbij : Function.Bijective fbar := by
    constructor
    · -- injective
      rw [injective_iff_map_eq_zero]
      intro z hz
      obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective z
      obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective Q₁.primeCompl z
      have h0 : f (IsLocalization.mk' (Localization.AtPrime Q₁) a s) = 0 := hz
      rw [Localization.localRingHom_mk'] at h0
      obtain ⟨w, hw⟩ := (IsLocalization.mk'_eq_zero_iff _ _).mp h0
      obtain ⟨t, x, htu, htx⟩ := hg (w : B₁)
      have hxQ : x ∈ Q₁.primeCompl := by
        rw [hQ, ← htx]
        exact Submonoid.mul_mem _ w.2 (hunit_not_mem t htu)
      have hxa : x * a ∈ RingHom.ker g := by
        rw [RingHom.mem_ker, map_mul, ← htx]
        calc (w : B₁) * g t * g a = g t * ((w : B₁) * g a) := by ring
          _ = 0 := by rw [hw, mul_zero]
      have hmk : IsLocalization.mk' (Localization.AtPrime Q₁) a s =
          IsLocalization.mk' (Localization.AtPrime Q₁) (x * a) (⟨x, hxQ⟩ * s) := by
        rw [IsLocalization.mk'_eq_iff_eq]
        simp only [Submonoid.coe_mul]
        ring_nf
      show Ideal.Quotient.mk _ (IsLocalization.mk' (Localization.AtPrime Q₁) a s) = 0
      rw [hmk, Ideal.Quotient.eq_zero_iff_mem, IsLocalization.mk'_eq_mul_mk'_one]
      exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ hxa)
    · -- surjective
      intro y
      obtain ⟨⟨b, b'⟩, rfl⟩ := IsLocalization.mk'_surjective q.primeCompl y
      obtain ⟨s', x', hs', hbx'⟩ := hg (b' : B₁)
      obtain ⟨s, x, hs, hbx⟩ := hg b
      have hden : x' * s ∈ Q₁.primeCompl := by
        rw [hQ, map_mul, ← hbx']
        exact Submonoid.mul_mem _ (Submonoid.mul_mem _ b'.2 (hunit_not_mem s' hs'))
          (hunit_not_mem s hs)
      refine ⟨Ideal.Quotient.mk _ (IsLocalization.mk' (Localization.AtPrime Q₁) (x * s')
        ⟨x' * s, hden⟩), ?_⟩
      show f _ = _
      rw [Localization.localRingHom_mk', IsLocalization.mk'_eq_iff_eq]
      congr 1
      show (b' : B₁) * g (x * s') = g (x' * s) * b
      rw [map_mul, map_mul, ← hbx', ← hbx]
      ring
  refine ⟨(RingEquiv.ofBijective fbar hbij).symm, fun x => ?_⟩
  rw [RingEquiv.symm_apply_eq]
  simp only [RingEquiv.ofBijective_apply]
  exact (hf x).symm

end UnitDenominators

section Inclusion

open PowerSeriesPolynomialRing

variable {k : Type u} [Field k] {n m : ℕ}

/-- The inclusion `k⟦t⟧[x] → k⟦t⟧[x, y₁..y_l]`. -/
def powerSeriesPolynomialRingInclusion (l : ℕ) :
    PowerSeriesPolynomialRing k n m →+* PowerSeriesPolynomialRing k n (m + l) :=
  eval₂ C (fun i => X (Fin.castAdd l i))

theorem extensionHom_powerSeriesPolynomialRingInclusion {S : Type u} [CommRing S] {l : ℕ}
    (τ : PowerSeriesPolynomialRing k n m →+* S) (a : PowerSeriesPolynomialRing k n m) :
    extensionHom (l := l) τ (powerSeriesPolynomialRingInclusion l a) = MvPolynomial.C (τ a) := by
  refine induction_on_C_X (k := k) (n := n) (m := m) (P := fun a => extensionHom (l := l) τ
    (powerSeriesPolynomialRingInclusion l a) = MvPolynomial.C (τ a)) a (fun c => ?_)
    (fun p q hp hq => ?_) (fun p i hp => ?_)
  · simp only [powerSeriesPolynomialRingInclusion, eval₂_C, extensionHom_C]
  · rw [map_add, map_add, hp, hq, map_add, map_add]
  · simp only [map_mul, hp]
    have : powerSeriesPolynomialRingInclusion l (X (k := k) (n := n) i) =
        X (k := k) (n := n) (Fin.castAdd l i) := by
      simp [powerSeriesPolynomialRingInclusion]
    rw [this, extensionHom_X_castAdd]

end Inclusion

section Denominators

open PowerSeriesPolynomialRing

variable {k : Type u} [Field k] {n m : ℕ} (P : Ideal (PowerSeriesPolynomialRing k n m))
  [P.IsPrime] {R : Type u} [CommRing R] (φ : Localization.AtPrime P →+* R)

/-- `τ_R : T → R`, the composite `T → T_P → R`. -/
abbrev toTarget : PowerSeriesPolynomialRing k n m →+* R :=
  φ.comp (algebraMap (PowerSeriesPolynomialRing k n m) (Localization.AtPrime P))

/-- Every polynomial `F ∈ R[y]` becomes, after multiplication by a constant `τ_R(u)` with
`u ∈ T ∖ P`, the image of an element of `T₁ = k⟦t⟧[x, y]` (a surjection `φ : T_P → R` has
denominators `T ∖ P`). -/
theorem exists_mul_C_mem_range_extensionHom (hφ : Function.Surjective φ) {l : ℕ}
    (F : MvPolynomial (Fin l) R) :
    ∃ u : PowerSeriesPolynomialRing k n m, u ∉ P ∧
      F * MvPolynomial.C (toTarget P φ u) ∈ (extensionHom (l := l) (toTarget P φ)).range := by
  have hCmem : ∀ u : PowerSeriesPolynomialRing k n m,
      MvPolynomial.C (toTarget P φ u) ∈ (extensionHom (l := l) (toTarget P φ)).range :=
    fun u => ⟨powerSeriesPolynomialRingInclusion l u,
      extensionHom_powerSeriesPolynomialRingInclusion _ u⟩
  induction F using MvPolynomial.induction_on with
  | C r =>
    obtain ⟨lam, rfl⟩ := hφ r
    obtain ⟨⟨a, s⟩, hs⟩ := IsLocalization.surj P.primeCompl lam
    refine ⟨s, s.2, ?_⟩
    have : (MvPolynomial.C (φ lam) : MvPolynomial (Fin l) R) *
        MvPolynomial.C (toTarget P φ (s : PowerSeriesPolynomialRing k n m)) =
        MvPolynomial.C (toTarget P φ a) := by
      rw [← map_mul]
      congr 1
      show φ lam * φ (algebraMap (PowerSeriesPolynomialRing k n m) (Localization.AtPrime P) s) =
        φ (algebraMap (PowerSeriesPolynomialRing k n m) (Localization.AtPrime P) a)
      rw [← map_mul, hs]
    rw [this]
    exact hCmem a
  | add F G hF hG =>
    obtain ⟨uF, huF, hFr⟩ := hF
    obtain ⟨uG, huG, hGr⟩ := hG
    refine ⟨uF * uG, fun h => (Ideal.IsPrime.mem_or_mem inferInstance h).elim huF huG, ?_⟩
    have : (F + G) * MvPolynomial.C (toTarget P φ (uF * uG)) =
        (F * MvPolynomial.C (toTarget P φ uF)) * MvPolynomial.C (toTarget P φ uG) +
        (G * MvPolynomial.C (toTarget P φ uG)) * MvPolynomial.C (toTarget P φ uF) := by
      rw [map_mul, map_mul]
      ring
    rw [this]
    exact add_mem (mul_mem hFr (hCmem uG)) (mul_mem hGr (hCmem uF))
  | mul_X F i hF =>
    obtain ⟨u, hu, hFr⟩ := hF
    refine ⟨u, hu, ?_⟩
    have hX : (MvPolynomial.X i : MvPolynomial (Fin l) R) ∈
        (extensionHom (l := l) (toTarget P φ)).range :=
      ⟨X (Fin.natAdd m i), extensionHom_X_natAdd _ i⟩
    have : F * MvPolynomial.X i * MvPolynomial.C (toTarget P φ u) =
        (F * MvPolynomial.C (toTarget P φ u)) * MvPolynomial.X i := by ring
    rw [this]
    exact mul_mem hFr hX

/-- The presentation of a finite type `R`-algebra `B` by `T₁`: the composite
`T₁ → R[y] → B` (here `ψ_B : R[y] ↠ B`). -/
abbrev presentationHom {l : ℕ} {B : Type u} [CommRing B] [Algebra R B]
    (ψ : MvPolynomial (Fin l) R →ₐ[R] B) :
    PowerSeriesPolynomialRing k n (m + l) →+* B :=
  ψ.toRingHom.comp (extensionHom (l := l) (toTarget P φ))

/-- **Unit denominators for the presentation**: every `b ∈ B` is `ψ₁(x)/ψ₁(s)` with `ψ₁(s)` a
unit of `B` (`s ∈ T ∖ P`). -/
theorem exists_unit_denominators_presentationHom (hφ : Function.Surjective φ) {l : ℕ}
    {B : Type u} [CommRing B] [Algebra R B] (ψ : MvPolynomial (Fin l) R →ₐ[R] B)
    (hψ : Function.Surjective ψ) (b : B) :
    ∃ s x : PowerSeriesPolynomialRing k n (m + l),
      IsUnit (presentationHom P φ ψ s) ∧
        b * presentationHom P φ ψ s = presentationHom P φ ψ x := by
  obtain ⟨F, rfl⟩ := hψ b
  obtain ⟨u, hu, F', hF'⟩ := exists_mul_C_mem_range_extensionHom P φ hφ F
  refine ⟨powerSeriesPolynomialRingInclusion l u, F', ?_, ?_⟩
  · show IsUnit (ψ (extensionHom (l := l) (toTarget P φ)
      (powerSeriesPolynomialRingInclusion l u)))
    rw [extensionHom_powerSeriesPolynomialRingInclusion]
    have h1 : IsUnit (toTarget P φ u) :=
      (IsLocalization.map_units (Localization.AtPrime P) (⟨u, hu⟩ : P.primeCompl)).map φ
    have h2 : ψ (MvPolynomial.C (toTarget P φ u)) = algebraMap R B (toTarget P φ u) :=
      ψ.commutes (toTarget P φ u)
    rw [h2]
    exact h1.map _
  · show ψ F * ψ (extensionHom (l := l) (toTarget P φ) (powerSeriesPolynomialRingInclusion l u)) =
      ψ (extensionHom (l := l) (toTarget P φ) F')
    rw [extensionHom_powerSeriesPolynomialRingInclusion, hF', map_mul]

end Denominators

section CompletionSide

open PowerSeriesPolynomialRing
open scoped TensorProduct

variable {k : Type u} [Field k] {n m : ℕ} (P : Ideal (PowerSeriesPolynomialRing k n m))
  [P.IsPrime] {R : Type u} [CommRing R] [IsLocalRing R] (φ : Localization.AtPrime P →+* R)
  (hφ : Function.Surjective φ) {l : ℕ} {B : Type u} [CommRing B] [Algebra R B]
  (ψ : MvPolynomial (Fin l) R →ₐ[R] B)

/-- The ring homomorphism `θ : Λ̂[y] → B ⊗_R R̂`: `Λ̂ → R̂ → B ⊗_R R̂` on coefficients (the
completion of `φ`), and `y_a ↦ ψ(y_a) ⊗ 1`. -/
def completionTensorHom :
    MvPolynomial (Fin l) (completionAtPrime P) →+* B ⊗[R] AdicCompletion (maximalIdeal R) R :=
  MvPolynomial.eval₂Hom
    ((Algebra.TensorProduct.includeRight :
      AdicCompletion (maximalIdeal R) R →ₐ[R]
        B ⊗[R] AdicCompletion (maximalIdeal R) R).toRingHom.comp
      (completionMap φ hφ))
    (fun a => ψ (MvPolynomial.X a) ⊗ₜ[R] 1)

theorem completionTensorHom_C (c : completionAtPrime P) :
    completionTensorHom P φ hφ ψ (MvPolynomial.C c) =
      1 ⊗ₜ[R] (completionMap φ hφ c) := by
  simp [completionTensorHom]

theorem completionTensorHom_X (a : Fin l) :
    completionTensorHom P φ hφ ψ (MvPolynomial.X a) = ψ (MvPolynomial.X a) ⊗ₜ[R] 1 := by
  simp [completionTensorHom]

/-- `completionMap φ` sends the image of `t ∈ T` to the image of `τ_R t`. -/
theorem completionMap_algebraMap_powerSeriesPolynomialRing
    (t : PowerSeriesPolynomialRing k n m) :
    completionMap φ hφ (algebraMap (PowerSeriesPolynomialRing k n m) (completionAtPrime P) t) =
      algebraMap R (AdicCompletion (maximalIdeal R) R) (toTarget P φ t) := by
  rw [IsScalarTower.algebraMap_apply (PowerSeriesPolynomialRing k n m) (Localization.AtPrime P)
    (completionAtPrime P), completionMap_algebraMap]
  rfl

theorem completionTensorHom_one_tmul_algebraMap (r : R) :
    (1 : B) ⊗ₜ[R] (algebraMap R (AdicCompletion (maximalIdeal R) R) r) =
      algebraMap B (B ⊗[R] AdicCompletion (maximalIdeal R) R) (algebraMap R B r) := by
  show _ = (algebraMap R B r) ⊗ₜ[R] (1 : AdicCompletion (maximalIdeal R) R)
  exact (Algebra.TensorProduct.tmul_one_eq_one_tmul r).symm

/-- `θ ∘ ρ = (B → B ⊗ R̂) ∘ ψ₁` on `T₁`. -/
theorem completionTensorHom_completionExtensionHom
    (x : PowerSeriesPolynomialRing k n (m + l)) :
    completionTensorHom P φ hφ ψ (completionExtensionHom P l x) =
      algebraMap B (B ⊗[R] AdicCompletion (maximalIdeal R) R) (presentationHom P φ ψ x) := by
  have hCc : ∀ t : PowerSeriesPolynomialRing k n m,
      completionTensorHom P φ hφ ψ (MvPolynomial.C (algebraMap _ (completionAtPrime P) t)) =
        algebraMap B (B ⊗[R] AdicCompletion (maximalIdeal R) R)
          (ψ (MvPolynomial.C (toTarget P φ t))) := by
    intro t
    rw [completionTensorHom_C, completionMap_algebraMap_powerSeriesPolynomialRing,
      completionTensorHom_one_tmul_algebraMap, ← MvPolynomial.algebraMap_eq, ψ.commutes]
  have hXx : ∀ i : Fin (m + l),
      completionTensorHom P φ hφ ψ (completionExtensionHom P l (X i)) =
        algebraMap B (B ⊗[R] AdicCompletion (maximalIdeal R) R) (presentationHom P φ ψ (X i)) := by
    intro i
    induction i using Fin.addCases with
    | left j =>
      show completionTensorHom P φ hφ ψ (extensionHom _ (X (Fin.castAdd l j))) =
        algebraMap B _ (ψ (extensionHom _ (X (Fin.castAdd l j))))
      rw [extensionHom_X_castAdd, extensionHom_X_castAdd]
      exact hCc (X j)
    | right a =>
      show completionTensorHom P φ hφ ψ (extensionHom _ (X (Fin.natAdd m a))) =
        algebraMap B _ (ψ (extensionHom _ (X (Fin.natAdd m a))))
      rw [extensionHom_X_natAdd, extensionHom_X_natAdd, completionTensorHom_X]
      rfl
  refine induction_on_C_X (k := k) (n := n) (m := m + l)
    (P := fun x => completionTensorHom P φ hφ ψ (completionExtensionHom P l x) =
      algebraMap B (B ⊗[R] AdicCompletion (maximalIdeal R) R) (presentationHom P φ ψ x)) x
    (fun c => ?_) (fun p q hp hq => ?_) (fun p i hp => ?_)
  · show completionTensorHom P φ hφ ψ (extensionHom _ (C c)) =
      algebraMap B _ (ψ (extensionHom _ (C c)))
    rw [extensionHom_C, extensionHom_C]
    exact hCc (C c)
  · rw [RingHom.map_add, RingHom.map_add, hp, hq, RingHom.map_add, RingHom.map_add]
  · rw [RingHom.map_mul, RingHom.map_mul, RingHom.map_mul, RingHom.map_mul, hp, hXx]

/-- `θ : Λ̂[y] → B ⊗_R R̂` is surjective (as `Λ̂ → R̂` and `ψ` are). -/
theorem completionTensorHom_surjective (hψ : Function.Surjective ψ) :
    Function.Surjective (completionTensorHom P φ hφ ψ) := by
  intro z
  show z ∈ (completionTensorHom P φ hφ ψ).range
  induction z using TensorProduct.inductionOn with
  | add x y hx hy => exact add_mem hx hy
  | tmul b rh =>
    obtain ⟨F, rfl⟩ := hψ b
    induction F using MvPolynomial.induction_on with
    | C r =>
      obtain ⟨ĉ, hĉ⟩ := completionMap_surjective φ hφ
        (algebraMap R (AdicCompletion (maximalIdeal R) R) r * rh)
      refine ⟨MvPolynomial.C ĉ, ?_⟩
      rw [completionTensorHom_C, hĉ, ← MvPolynomial.algebraMap_eq, ψ.commutes]
      have h1 : (algebraMap R B r) ⊗ₜ[R] rh =
          ((algebraMap R B r) ⊗ₜ[R] (1 : AdicCompletion (maximalIdeal R) R)) *
            ((1 : B) ⊗ₜ[R] rh) := by
        rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
      rw [h1, Algebra.TensorProduct.tmul_one_eq_one_tmul, Algebra.TensorProduct.tmul_mul_tmul,
        mul_one]
    | add F G hF hG =>
      rw [map_add, TensorProduct.add_tmul]
      exact add_mem hF hG
    | mul_X F a hF =>
      have hX : ψ (MvPolynomial.X a) ⊗ₜ[R] (1 : AdicCompletion (maximalIdeal R) R) ∈
          (completionTensorHom P φ hφ ψ).range :=
        ⟨MvPolynomial.X a, completionTensorHom_X P φ hφ ψ a⟩
      have := mul_mem hF hX
      rwa [Algebra.TensorProduct.tmul_mul_tmul, mul_one, ← map_mul] at this

end CompletionSide

end Hironaka
