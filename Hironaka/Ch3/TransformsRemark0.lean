/-
Copyright (c) 2026 Daattavya Aggarwal, Minhyong Kim, Oisin Kim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daattavya Aggarwal, Minhyong Kim, Oisin Kim
-/
module

public import Architect
public import Hironaka.Ch3.Transforms
public import Mathlib.RingTheory.PowerSeries.Inverse

/-!
# Remark 0 (p. 213): one local ring, two centers

> Remark 0. In the above definition of the strict (resp. the weak) transform `J'` of `J` in the
> monoidal transform `R'` of `R` with center `P`, the reference to the center `P` is essential. A
> simple example shows that we can have one and the same local ring `R'` (in the field of
> quotients of `R`) which is the monoidal transforms of `R` with two different centers `P` and `Q`.
> Moreover, the transform `J'` of `J` in `R'` with respect to `P` may not be the same as that of `J`
> in `R'` with respect to `Q`. (p. 213)

The example: `R' = R`, which is the monoidal transform of `R` with center `R` and also with every
principal center `Q = (x)` (p. 209: "In this case, the monoidal transform of `R` is canonically
isomorphic to `R`. Note that we have also such an isomorphism when `P` is principal",
`MonoidalTransform.bijective_toRing_of_isPrincipal`).  For `J = (x)` the strict transform with respect
to `R` is `JR' ≠ R'` and with respect to `(x)` it is `R'`.
-/

@[expose] public section

open IsLocalRing

namespace Hironaka

universe u

section Remark0

variable {R : Type u} [CommRing R] [IsRegularLocalRing R] [IsDomain R]

/-- If `P = (x)` is principal, `R[x⁻¹P] = R`: `q/x ∈ R` for `q ∈ P`. -/
theorem blowupAlgebra_eq_bot_of_eq_span_singleton {P : Ideal R} {x : R} (hx0 : x ≠ 0)
    (hP : P = Ideal.span {x}) : blowupAlgebra R P x = ⊥ := by
  apply le_antisymm
  · refine Algebra.adjoin_le ?_
    rintro _ ⟨q, hq, rfl⟩
    obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.mp (hP ▸ hq : q ∈ Ideal.span {x})
    refine Algebra.mem_bot.mpr ⟨r, ?_⟩
    have hxK : algebraMap R (FractionRing R) x ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective R (FractionRing R))).mpr hx0
    rw [eq_div_iff hxK, ← map_mul, hr]
  · exact bot_le


/-- A monoidal transform with principal center `P = (x)`, `x ≠ 0`: `R[x⁻¹P] = R`, and `M'` is the
maximal ideal. -/
noncomputable def MonoidalTransform.ofPrincipal {P : Ideal R} {x : R} (hx0 : x ≠ 0)
    (hP : P = Ideal.span {x}) : MonoidalTransform R P :=
  have hsurj : Function.Surjective (algebraMap R (blowupAlgebra R P x)) := by
    rintro ⟨z, hz⟩
    obtain ⟨r, hr⟩ := Algebra.mem_bot.mp (blowupAlgebra_eq_bot_of_eq_span_singleton hx0 hP ▸ hz)
    exact ⟨r, Subtype.ext hr⟩
  have hinj : Function.Injective (algebraMap R (blowupAlgebra R P x)) := fun a b h =>
    IsFractionRing.injective R (FractionRing R) (congrArg Subtype.val h)
  have hker : RingHom.ker (algebraMap R (blowupAlgebra R P x)) ≤ maximalIdeal R := by
    rw [(RingHom.injective_iff_ker_eq_bot _).mp hinj]
    exact bot_le
  { x := x
    x_mem := hP ▸ Ideal.subset_span rfl
    x_ne_zero := hx0
    M' := (maximalIdeal R).map (algebraMap R (blowupAlgebra R P x))
    isPrime := Ideal.map_isPrime_of_surjective hsurj hker
    le := le_rfl }

theorem MonoidalTransform.bijective_toRing_ofPrincipal {P : Ideal R} {x : R} (hx0 : x ≠ 0)
    (hP : P = Ideal.span {x}) : Function.Bijective (MonoidalTransform.ofPrincipal hx0 hP).toRing :=
  (MonoidalTransform.ofPrincipal hx0 hP).bijective_toRing_of_isPrincipal ⟨⟨x, hP⟩⟩

theorem MonoidalTransform.subring_ofPrincipal {P : Ideal R} {x : R} (hx0 : x ≠ 0)
    (hP : P = Ideal.span {x}) :
    (MonoidalTransform.ofPrincipal hx0 hP).subring = (algebraMap R (FractionRing R)).range := by
  have hbij := MonoidalTransform.bijective_toRing_ofPrincipal hx0 hP
  ext y
  constructor
  · rintro ⟨w, rfl⟩
    obtain ⟨r, rfl⟩ := hbij.2 w
    exact ⟨r, ((MonoidalTransform.ofPrincipal hx0 hP).toFractionRing_toRing r).symm⟩
  · rintro ⟨r, rfl⟩
    exact ⟨(MonoidalTransform.ofPrincipal hx0 hP).toRing r,
      (MonoidalTransform.ofPrincipal hx0 hP).toFractionRing_toRing r⟩

variable (R) in
/-- The monoidal transform of `R` with center `R` (p. 209: "it is convenient to include the case
`P = R`"): `x = 1`, `R[1⁻¹R] = R`. -/
noncomputable def MonoidalTransform.ofTop : MonoidalTransform R (⊤ : Ideal R) :=
  MonoidalTransform.ofPrincipal (x := (1 : R)) one_ne_zero Ideal.span_singleton_one.symm

theorem MonoidalTransform.bijective_toRing_ofTop :
    Function.Bijective (MonoidalTransform.ofTop R).toRing :=
  MonoidalTransform.bijective_toRing_ofPrincipal (x := (1 : R)) one_ne_zero
    Ideal.span_singleton_one.symm

/-- Remark 0 (p. 213), the example, first half: the strict transform of `J = (x₀)` in `R' = R` with
respect to the center `R` is contained in `JR'`, which does not contain `1` if `x₀ ∈ M`. -/
theorem MonoidalTransform.one_notMem_image_strictTransformIdeal_ofTop {x₀ : R}
    (hx₀ : x₀ ∈ maximalIdeal R) :
    (1 : FractionRing R) ∉ (MonoidalTransform.ofTop R).toFractionRing ''
      (strictTransformIdeal (MonoidalTransform.ofTop R) (Ideal.span {x₀}) : Set _) := by
  set t := MonoidalTransform.ofTop R with ht
  have hbij : Function.Bijective t.toRing := MonoidalTransform.bijective_toRing_ofTop
  rintro ⟨y, hy, hy1⟩
  -- the strict transform lies in `JR'`
  have hle : strictTransformIdeal t (Ideal.span {x₀}) ≤ (Ideal.span {x₀}).map t.toRing := by
    rw [strictTransformIdeal, Ideal.span_le]
    rintro y ⟨x', hx', f, hf, ν, -, hxy⟩
    have hunit : IsUnit x' := by
      rw [← Ideal.span_singleton_eq_top, hx', Ideal.map_top]
    obtain ⟨u, hu⟩ := (hunit.pow ν).exists_right_inv
    have : y = u * t.toRing f := by
      rw [← hxy, ← mul_assoc, mul_comm u, mul_assoc, ← mul_assoc, hu, one_mul]
    rw [SetLike.mem_coe, this]
    exact Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _ hf)
  have hy' := hle hy
  rw [Ideal.map_span, Set.image_singleton, Ideal.mem_span_singleton'] at hy'
  obtain ⟨w, hw⟩ := hy'
  obtain ⟨r, rfl⟩ := hbij.2 w
  have h1 : algebraMap R (FractionRing R) (r * x₀) = algebraMap R (FractionRing R) 1 := by
    rw [map_one, ← hy1, ← hw, ← map_mul t.toRing, t.toFractionRing_toRing]
  have h2 : r * x₀ = 1 := IsFractionRing.injective R (FractionRing R) h1
  have h3 : (1 : R) ∈ maximalIdeal R := h2 ▸ Ideal.mul_mem_left _ r hx₀
  exact (maximalIdeal.isMaximal R).ne_top ((Ideal.eq_top_iff_one _).mpr h3)

/-- Remark 0 (p. 213), the example, second half: the strict transform of `J = (x₀)` in `R' = R`
with respect to the center `(x₀)` is the unit ideal (`x₀⁻¹ x₀ = 1`). -/
theorem MonoidalTransform.one_mem_strictTransformIdeal_ofPrincipal {x₀ : R} (hx0 : x₀ ≠ 0) :
    (1 : (MonoidalTransform.ofPrincipal hx0 (rfl : Ideal.span {x₀} = Ideal.span {x₀})).ring) ∈
      strictTransformIdeal (MonoidalTransform.ofPrincipal hx0 (rfl : Ideal.span {x₀} = Ideal.span {x₀}))
        (Ideal.span {x₀}) := by
  set t := MonoidalTransform.ofPrincipal hx0 (rfl : Ideal.span {x₀} = Ideal.span {x₀}) with ht
  refine Ideal.subset_span ⟨t.xR, t.span_xR_eq_map, x₀, Ideal.mem_span_singleton_self _, 1, ?_, ?_⟩
  · exact Ideal.le_ordElem (by rw [pow_one]; exact Ideal.mem_span_singleton_self _)
  · rw [pow_one, mul_one]
    rfl

/-- The statement of Remark 0 (p. 213): "A simple example shows that we can have one and the same
local ring `R'` (in the field of quotients of `R`) which is the monoidal transform of `R` with two
different centers `P` and `Q`. Moreover, the transform `J'` of `J` in `R'` with respect to `P` may
not be the same as that of `J` in `R'` with respect to `Q`."  For the rings `R'` in the field of
quotients of `R` as subrings (`MonoidalTransform.subring`); the transforms are compared through their
images in `Frac R`.  Both centers satisfy the hypotheses of p. 209 (`P ≠ (0)` prime with `R/P` regular,
or `P = R`). -/
def HasTwoCenters (R : Type u) [CommRing R] [IsRegularLocalRing R] [IsDomain R] : Prop :=
  ∃ (P Q : Ideal R) (t : MonoidalTransform R P) (t' : MonoidalTransform R Q),
    P ≠ Q ∧ P ≠ ⊥ ∧ Q ≠ ⊥ ∧ (P = ⊤ ∨ P.IsPrime ∧ IsRegularLocalRing (R ⧸ P)) ∧
      (Q = ⊤ ∨ Q.IsPrime ∧ IsRegularLocalRing (R ⧸ Q)) ∧ t.subring = t'.subring ∧
      ∃ J : Ideal R, t.toFractionRing '' (strictTransformIdeal t J : Set t.ring) ≠
        t'.toFractionRing '' (strictTransformIdeal t' J : Set t'.ring)

/-- Remark 0 (p. 213): for every regular local ring `R` with a non-zero `x₀ ∈ M` such that `(x₀)` is
prime with `R/(x₀)` regular, the ring `R' = R` is a monoidal transform of `R` with center `P = R` and
with center `Q = (x₀)` (`R' ≅ R` when the center is `R` or principal, p. 209), and for `J = (x₀)` the
transform of `J` with respect to `R` is `JR' ≠ R'` while with respect to `(x₀)` it is `R'`. -/
@[blueprint "rem:III.2-0"
  (statement := /-- Let $R$ be a regular local ring and $x_0\ne0$ an element of its maximal ideal such
    that $(x_0)$ is prime and $R/(x_0)$ is regular. Then one and the same local ring $R'=R$ (in the
    field of quotients of $R$) is a monoidal transform of $R$ with the two different centers $P=R$
    and $Q=(x_0)$ (\cref{def:III.2-monoidal-transform}); moreover, for $J=(x_0)$ the strict transform
    of $J$ in $R'$ with respect to $P$ is $JR'\ne R'$, and with respect to $Q$ it is $R'$, so the
    transforms differ. (Remark 0, p.~213: ``A simple example shows \dots''. Formalization note
    (encoding): $R'$ is compared as a subring of the field of quotients of $R$, and the transforms
    through their images there.) -/)
  (proof := /-- For the center $R$, $x=1$ and $R[1^{-1}R]=R$; for the principal center $(x_0)$,
    $x=x_0$ and $R[x_0^{-1}(x_0)]=R$; in both cases $M'$ is the maximal ideal and $R'=R$
    (\cref{lem:III.2-monoidal-transform-principal}), so both give the subring $R$ of the field of
    quotients. The strict transform of $J=(x_0)$ with respect to $R$ is contained in $JR'$ ($x$ is a
    unit), and $1\notin JR'$ since $x_0\in M$; with respect to $(x_0)$ it contains $x_0^{-1}x_0=1$.
    For instance $R=\mathbb Q[[X]]$, $x_0=X$. (p.~213.) -/)
  (latexEnv := "remark")]
theorem hasTwoCenters_of_prime_regular {x₀ : R} (hx₀ : x₀ ∈ maximalIdeal R) (hx0 : x₀ ≠ 0)
    (hprime : (Ideal.span {x₀}).IsPrime) (hreg : IsRegularLocalRing (R ⧸ Ideal.span {x₀})) :
    HasTwoCenters R := by
  have hne : (⊤ : Ideal R) ≠ Ideal.span {x₀} := by
    rw [Ne, eq_comm, Ideal.span_singleton_eq_top]
    exact (IsLocalRing.mem_maximalIdeal _).mp hx₀
  refine ⟨⊤, Ideal.span {x₀}, MonoidalTransform.ofTop R, MonoidalTransform.ofPrincipal hx0 rfl,
    hne, top_ne_bot, ?_, Or.inl rfl, Or.inr ⟨hprime, hreg⟩, ?_, Ideal.span {x₀}, ?_⟩
  · rw [Ne, Ideal.span_singleton_eq_bot]; exact hx0
  · rw [MonoidalTransform.ofTop, MonoidalTransform.subring_ofPrincipal,
      MonoidalTransform.subring_ofPrincipal]
  · intro h
    have h1 : (1 : FractionRing R) ∈ (MonoidalTransform.ofPrincipal hx0
        (rfl : Ideal.span {x₀} = Ideal.span {x₀})).toFractionRing ''
        (strictTransformIdeal (MonoidalTransform.ofPrincipal hx0 (rfl : Ideal.span {x₀} = Ideal.span {x₀}))
          (Ideal.span {x₀}) : Set _) :=
      ⟨1, MonoidalTransform.one_mem_strictTransformIdeal_ofPrincipal hx0, map_one _⟩
    rw [← h] at h1
    exact MonoidalTransform.one_notMem_image_strictTransformIdeal_ofTop hx₀ h1

/-- Remark 0 (p. 213), a concrete example: `R = ℚ⟦X⟧`, `P = R`, `Q = M = (X)`, `J = (X)`. -/
theorem hasTwoCenters_powerSeries : HasTwoCenters (PowerSeries ℚ) := by
  have hmax : IsLocalRing.maximalIdeal (PowerSeries ℚ) = Ideal.span {(PowerSeries.X : PowerSeries ℚ)} :=
    PowerSeries.maximalIdeal_eq_span_X
  refine hasTwoCenters_of_prime_regular (x₀ := PowerSeries.X) ?_ PowerSeries.X_ne_zero ?_ ?_
  · rw [hmax]; exact Ideal.subset_span rfl
  · rw [← hmax]; infer_instance
  · rw [← hmax]
    exact (inferInstance : IsRegularLocalRing (IsLocalRing.ResidueField (PowerSeries ℚ)))

end Remark0

end Hironaka
