/-
Copyright (c) 2026 Daattavya Aggarwal, Minhyong Kim, Oisin Kim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daattavya Aggarwal, Minhyong Kim, Oisin Kim
-/
module

public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.MvPowerSeries.Basic
public import Architect
public import Hironaka.Compat.PowerSeriesPolynomialRing

/-!
# Compatibility layer: presenting a finite-type algebra over a complete local ring by `k⟦t⟧[x]`

A step in the proof of property (c) of the class 𝔅 (p. 161).  Footnote
30: "... in which A is a homomorphic image of a polynomial ring over such a formal power series
ring."

* `exists_surjective_powerSeriesPolynomialRing`: if `S` is a homomorphic image of `k⟦t₁,…,t_n⟧`
  and `A` is an `S`-algebra of finite type, then `A` is a homomorphic image of `k⟦t⟧[x₁,…,x_m]`
  for some `m`, compatibly with the maps from `k⟦t⟧`;
* `exists_ringEquiv_localization_quotient`: for a surjection `Φ : T → A` and a prime `p` of `A`,
  `A_p ≅ T_P / (ker Φ) T_P` with `P = Φ⁻¹ p` (the local ring `A_p` is a quotient of the regular
  local ring `T_P`).
-/

@[expose] public section

open IsLocalRing

noncomputable section

namespace Hironaka

universe u

open PowerSeriesPolynomialRing in
/-- If `S` is a homomorphic image of `k⟦t₁,…,t_n⟧` (via `f`) and `A` is an `S`-algebra of finite
type, then `A` is a homomorphic image of `k⟦t⟧[x₁,…,x_m]` for some `m`, by a map extending
`algebraMap S A ∘ f` on `k⟦t⟧`.

Footnote 30, p. 161: "A is a homomorphic image of a polynomial ring over such a formal power
series ring". -/
theorem exists_surjective_powerSeriesPolynomialRing {S A : Type u} [CommRing S] [CommRing A]
    [Algebra S A] [Algebra.FiniteType S A] {n : ℕ} {k : Type u} [Field k]
    (f : MvPowerSeries (Fin n) k →+* S) (hf : Function.Surjective f) :
    ∃ (m : ℕ) (Φ : PowerSeriesPolynomialRing k n m →+* A), Function.Surjective Φ ∧
      ∀ c : MvPowerSeries (Fin n) k, Φ (C c) = algebraMap S A (f c) := by
  obtain ⟨m, g, hg⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.mp ‹Algebra.FiniteType S A›
  refine ⟨m, g.toRingHom.comp (MvPolynomial.map f), ?_, fun c => ?_⟩
  · exact hg.comp (MvPolynomial.map_surjective f hf)
  · show g (MvPolynomial.map f (MvPolynomial.C c)) = _
    rw [MvPolynomial.map_C]
    exact g.commutes (f c)

/-- For a surjective ring homomorphism `Φ : T → A` and a prime `p` of `A`, the local ring `A_p` is
isomorphic to `T_P / (ker Φ) T_P`, `P = Φ⁻¹ p`, compatibly with the maps from `T`. -/
theorem exists_ringEquiv_localization_quotient {T A : Type u} [CommRing T] [CommRing A]
    (Φ : T →+* A) (hΦ : Function.Surjective Φ) (p : Ideal A) [p.IsPrime] :
    ∃ e : Localization.AtPrime p ≃+* (Localization.AtPrime (p.comap Φ) ⧸
        (RingHom.ker Φ).map (algebraMap T (Localization.AtPrime (p.comap Φ)))),
      ∀ x : T, e (algebraMap A (Localization.AtPrime p) (Φ x)) =
        Ideal.Quotient.mk _ (algebraMap T (Localization.AtPrime (p.comap Φ)) x) := by
  let P : Ideal T := p.comap Φ
  let eQ : (T ⧸ RingHom.ker Φ) ≃+* A := RingHom.quotientKerEquivOfSurjective hΦ
  have H : (Algebra.algebraMapSubmonoid (T ⧸ RingHom.ker Φ) P.primeCompl).map eQ.toMonoidHom =
      p.primeCompl := by
    ext a
    constructor
    · rintro ⟨_, ⟨t, ht, rfl⟩, rfl⟩
      show Φ t ∉ p
      exact ht
    · intro ha
      obtain ⟨t, rfl⟩ := hΦ a
      exact ⟨Ideal.Quotient.mk _ t, ⟨t, ha, rfl⟩, rfl⟩
  let E := IsLocalization.ringEquivOfRingEquiv
    (Localization.AtPrime P ⧸ (RingHom.ker Φ).map (algebraMap T (Localization.AtPrime P)))
    (Localization.AtPrime p) eQ H
  refine ⟨E.symm, fun x => ?_⟩
  rw [RingEquiv.symm_apply_eq]
  have h1 : Ideal.Quotient.mk ((RingHom.ker Φ).map (algebraMap T (Localization.AtPrime P)))
      (algebraMap T (Localization.AtPrime P) x) =
      algebraMap (T ⧸ RingHom.ker Φ) (Localization.AtPrime P ⧸
        (RingHom.ker Φ).map (algebraMap T (Localization.AtPrime P)))
        (Ideal.Quotient.mk (RingHom.ker Φ) x) := rfl
  rw [h1]
  have h2 := IsLocalization.ringEquivOfRingEquiv_eq (S := Localization.AtPrime P ⧸
    (RingHom.ker Φ).map (algebraMap T (Localization.AtPrime P)))
    (Q := Localization.AtPrime p) (j := eQ) H (Ideal.Quotient.mk (RingHom.ker Φ) x)
  rw [h2]
  have h3 : eQ (Ideal.Quotient.mk (RingHom.ker Φ) x) = Φ x := rfl
  rw [h3]

/-- The version of `exists_ringEquiv_localization_quotient` for `Φ = mk 𝔭 : T → T/𝔭` in terms of
a prime `𝔮` of `T` containing `𝔭`: with `𝔮' = 𝔮.map (mk 𝔭)`, `(T/𝔭)_{𝔮'} ≅ T_𝔮/𝔭T_𝔮`. -/
theorem nonempty_ringEquiv_localization_quotient_mk {T : Type u} [CommRing T] (𝔭 P : Ideal T)
    [P.IsPrime] (𝔮' : Ideal (T ⧸ 𝔭)) [𝔮'.IsPrime] (h : 𝔮'.comap (Ideal.Quotient.mk 𝔭) = P) :
    Nonempty (Localization.AtPrime 𝔮' ≃+*
      (Localization.AtPrime P ⧸ 𝔭.map (algebraMap T (Localization.AtPrime P)))) := by
  subst h
  obtain ⟨e, -⟩ := exists_ringEquiv_localization_quotient (Ideal.Quotient.mk 𝔭)
    Ideal.Quotient.mk_surjective 𝔮'
  exact ⟨e.trans (Ideal.quotEquivOfEq (by rw [Ideal.mk_ker]))⟩

end Hironaka
