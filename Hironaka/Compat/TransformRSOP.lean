/-
Copyright (c) 2026 Daattavya Aggarwal, Minhyong Kim, Oisin Kim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daattavya Aggarwal, Minhyong Kim, Oisin Kim
-/
module

public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.RegularLocalRing.Polynomial
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.Smooth.Flat
public import Architect
public import Hironaka.Ch3.Transforms
public import Hironaka.Compat.RSOPProducts

/-!
# Regular systems of parameters of a monoidal transform (Ch. I §1, Remark 1, p. 169)

> Let x' be any point of X', and x = f(x'). Then we can find a regular system of parameters
> (z₁, …, z_r, z_{r+1}, …, z_s) of the local ring O_x of X at x, such that every irreducible
> component F_j of E containing x is defined by z_j = 0 at x for some j, and that B is defined
> by z_{r+1} = ⋯ = z_s = 0 at x. Then the local ring O_{x'} of X' at x' is a ring of fractions
> of A = O_x[z_{r+1}/z_t, …, z_s/z_t] for some t (r + 1 ≤ t ≤ s) with respect to a prime ideal
> M in A. Let z'_v = z_v for 1 ≤ v ≤ r, z'_t = z_t and z'_v = z_v/z_t for r + 1 ≤ v (≠ t) ≤ s.
> It is then easily seen that, (F_j, z_j) being as above, the strict transform F_j' of F_j
> contains the point x' if and only if j ≠ t and z'_j ∈ M, in which case F_j' is defined by
> z'_j = 0 at x', that E'_{α+1} is defined by z'_t = 0 at x', provided x' ∈ E'_{α+1}, and that a
> system of those z'_v which are in M can be extended to a regular system of parameters of
> O_{x'} = A_M.

This module proves the local-algebra content of this passage for a monoidal transform
`R' = R[x⁻¹P]_{M'}` (`MonoidalTransform`, Ch. III §2) of a regular local ring `R` with center
`P = (T)`, `T` a subset of a regular system of parameters `Z` of `R`.  (The paper writes
`z₁, …, z_s` for a regular system of parameters, `s = dim R`; the members of `Z` outside
`{z₁, …, z_s}` of the quotation do not occur there because `s` is the dimension.)

Formalization note: the elements `z'_v` are given by a function `φ : R → R'` on `Z`; the
statement "those `z'_v` which are in `M`" is `φ z ∈ maximalIdeal R'`.

Deviation from the paper (gap filled): the paper asserts these facts with "it is easily seen".  Here
the existence of `t` is derived from `x = Σ c_t t` for the generator `x` of the data `(x, M')` of
`R' = R[x⁻¹P]_{M'}` (this is the sentence of p. 209, "there exist an index `i` …",
`MonoidalTransform.exists_index_subring_eq_localization`; the paper prints it without proof).  The
form of p. 169, `R'` a ring of fractions of `A = R[z_v/z_t]` with respect to a prime ideal `M` of `A`, is
`MonoidalTransform.exists_equiv_of_span_eq` (`Hironaka/Compat/TransformRingOfFractions.lean`), applied
to the `z_t` of `exists_rsop_transform`; the elements `z'_v` are `φ z` (`φ z = z / z_t` in `A` for
`z ∈ T`, `z ≠ z_t`, see `DatumTransform.exists_chart_ringOfFractions`).  The extension of the
`z'_v ∈ M` to a regular system of parameters is proved through the Ch. III §2 description
`R'/xR' ≅ ((R/P)[X₁, …, X_r])_q`, the regularity of `R'` and of `R'/xR'` (pp. 209–210), and a
derivation argument.
-/

@[expose] public section

open IsLocalRing Classical

namespace Hironaka

universe u

/-! ### Localized polynomial rings over a regular local ring -/

section PolyRSOP

open MvPolynomial

/-- The derivation argument: if `X_j ∈ q`, then `X_j` is not in `(S) + M²` in `k[X]_q` for `S`
consisting of images of polynomials `g ∈ q` with `∂g/∂X_j ∈ q`. -/
theorem mvPoly_X_notMem_span_sup_sq {k : Type*} [CommRing k] {r : ℕ}
    (q : Ideal (MvPolynomial (Fin r) k)) [q.IsPrime] (j : Fin r) (hj : (X j : MvPolynomial (Fin r) k) ∈ q)
    (S : Set (Localization.AtPrime q))
    (hS : ∀ y ∈ S, ∃ g, g ∈ q ∧ pderiv j g ∈ q ∧ y = algebraMap _ _ g) :
    algebraMap _ (Localization.AtPrime q) (X j : MvPolynomial (Fin r) k) ∉
      Ideal.span S ⊔ maximalIdeal (Localization.AtPrime q) ^ 2 := by
  classical
  let D : Ideal (MvPolynomial (Fin r) k) :=
    { carrier := {f | f ∈ q ∧ pderiv j f ∈ q}
      add_mem' := fun ha hb => ⟨add_mem ha.1 hb.1, by rw [map_add]; exact add_mem ha.2 hb.2⟩
      zero_mem' := ⟨zero_mem _, by rw [map_zero]; exact zero_mem _⟩
      smul_mem' := fun c f hf => ⟨q.mul_mem_left c hf.1, by
        rw [smul_eq_mul, Derivation.leibniz, smul_eq_mul, smul_eq_mul]
        exact add_mem (q.mul_mem_left _ hf.2) (q.mul_mem_right _ hf.1)⟩ }
  have hle : Ideal.span S ⊔ maximalIdeal (Localization.AtPrime q) ^ 2 ≤
      D.map (algebraMap _ (Localization.AtPrime q)) := by
    refine sup_le (Ideal.span_le.mpr fun y hy => ?_) ?_
    · obtain ⟨g, hg, hg', rfl⟩ := hS y hy
      exact Ideal.mem_map_of_mem _ (show g ∈ D from ⟨hg, hg'⟩)
    · rw [← Localization.AtPrime.map_eq_maximalIdeal, ← Ideal.map_pow]
      refine Ideal.map_mono ?_
      rw [pow_two]
      refine Ideal.mul_le.mpr fun a ha b hb => (show a * b ∈ D from ⟨q.mul_mem_right _ ha, ?_⟩)
      rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]
      exact add_mem (q.mul_mem_right _ ha) (q.mul_mem_right _ hb)
  intro hmem
  obtain ⟨m, hm, hmX⟩ :=
    (IsLocalization.algebraMap_mem_map_algebraMap_iff q.primeCompl _ _ _).mp (hle hmem)
  have h2 : pderiv j (m * X j) ∈ q := hmX.2
  rw [Derivation.leibniz, pderiv_X_self, smul_eq_mul, smul_eq_mul, mul_one] at h2
  have : m = (m + X j * pderiv j m) - X j * pderiv j m := by ring
  exact hm (this ▸ sub_mem h2 (q.mul_mem_right _ hj))

/-- `k[X]_q / m_k k[X]_q` (for `q` lying over the maximal ideal of the regular local ring `k`)
is a regular local ring, of dimension `dim k[X]_q - dim k`. -/
theorem mvPoly_loc_quotient_maximalIdeal {k : Type u} [CommRing k] [IsRegularLocalRing k] {r : ℕ}
    (q : Ideal (MvPolynomial (Fin r) k)) [q.IsPrime] (hq : q.comap C = maximalIdeal k) :
    ∃ _ : IsRegularLocalRing (Localization.AtPrime q ⧸
        ((maximalIdeal k).map (C : k →+* MvPolynomial (Fin r) k)).map
          (algebraMap _ (Localization.AtPrime q))),
      ringKrullDim (Localization.AtPrime q ⧸
        ((maximalIdeal k).map (C : k →+* MvPolynomial (Fin r) k)).map
          (algebraMap _ (Localization.AtPrime q))) + ringKrullDim k ≤
        ringKrullDim (Localization.AtPrime q) := by
  classical
  set A := MvPolynomial (Fin r) k
  set B := Localization.AtPrime q
  set I : Ideal A := (maximalIdeal k).map (C : k →+* A) with hI
  have hIq : I ≤ q := by rw [hI, Ideal.map_le_iff_le_comap, hq]
  have hker : RingHom.ker (Ideal.Quotient.mk I) ≤ q := by rw [Ideal.mk_ker]; exact hIq
  set qb := q.map (Ideal.Quotient.mk I) with hqb
  have hqbp : qb.IsPrime := Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective hker
  have hcomap : qb.comap (Ideal.Quotient.mk I) = q := by
    rw [hqb, Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective,
      ← RingHom.ker_eq_comap_bot, sup_eq_left.mpr hker]
  -- `B/IB` is the localization of `A/I` at `qb`
  have hsub : Algebra.algebraMapSubmonoid (A ⧸ I) q.primeCompl = qb.primeCompl := by
    ext y
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective y
    constructor
    · rintro ⟨b, hb, hba⟩ hy
      apply hb
      rw [← hcomap, SetLike.mem_coe, Ideal.mem_comap]
      have : Ideal.Quotient.mk I b = Ideal.Quotient.mk I a := hba
      rw [this]
      exact hy
    · intro hy
      refine ⟨a, fun h => hy ?_, rfl⟩
      rw [← hcomap] at h
      exact h
  have h0 : IsLocalization (Algebra.algebraMapSubmonoid (A ⧸ I) q.primeCompl)
      (B ⧸ I.map (algebraMap A B)) := inferInstance
  rw [hsub] at h0
  have hloc : IsLocalization.AtPrime (B ⧸ I.map (algebraMap A B)) qb := h0
  have hdimQ := IsLocalization.AtPrime.ringKrullDim_eq_height qb (B ⧸ I.map (algebraMap A B))
  have hdimB := IsLocalization.AtPrime.ringKrullDim_eq_height q B
  have hlies : q.LiesOver (maximalIdeal k) :=
    ⟨by rw [Ideal.under_def, MvPolynomial.algebraMap_eq, hq]⟩
  have hgd := Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown (maximalIdeal k) q
  rw [MvPolynomial.algebraMap_eq] at hgd
  -- regularity
  let := Ideal.Quotient.field (maximalIdeal k)
  let e₁ := MvPolynomial.quotientEquivQuotientMvPolynomial (σ := Fin r) (maximalIdeal k)
  have : IsRegularRing (A ⧸ I) := IsRegularRing.of_ringEquiv e₁.toRingEquiv
  let e₂ := IsLocalization.algEquiv qb.primeCompl (B ⧸ I.map (algebraMap A B))
    (Localization.AtPrime qb)
  refine ⟨IsRegularLocalRing.of_ringEquiv (R := Localization.AtPrime qb) e₂.symm.toRingEquiv, ?_⟩
  rw [hdimQ, hdimB, hgd, ← IsLocalRing.maximalIdeal_height_eq_ringKrullDim, add_comm]
  exact le_of_eq (by push_cast; rfl)

/-- The variables lying in `q`, together with the constants from a regular system of parameters
of `k`, are independent in `k[X]_q` (hence part of a regular system of parameters). -/
theorem mvPoly_rsopIndep {k : Type u} [CommRing k] [IsRegularLocalRing k] {r : ℕ}
    (q : Ideal (MvPolynomial (Fin r) k)) [q.IsPrime] (hq : q.comap C = maximalIdeal k)
    [IsRegularLocalRing (Localization.AtPrime q)]
    {ι : Type*} {F₁ F₂ : Finset ι} (hdisj : Disjoint F₁ F₂) (a : ι → k)
    (hY : IsRegularSystemOfParameters k (F₁.image a)) (ha : Set.InjOn a F₁)
    (v : ι → Localization.AtPrime q)
    (hv₁ : ∀ i ∈ F₁, v i = algebraMap _ _ (C (a i) : MvPolynomial (Fin r) k))
    (hv₂ : ∀ i ∈ F₂, ∃ j, (X j : MvPolynomial (Fin r) k) ∈ q ∧
      v i = algebraMap _ _ (X j : MvPolynomial (Fin r) k))
    (hinj₂ : Set.InjOn v F₂) :
    RSOPIndep (F₁ ∪ F₂) v := by
  classical
  have hk := isDomain_of_isRegularLocalRing k
  have hinjA : Function.Injective
      (algebraMap (MvPolynomial (Fin r) k) (Localization.AtPrime q)) :=
    IsLocalization.injective _ (Ideal.primeCompl_le_nonZeroDivisors q)
  have haM : ∀ i ∈ F₁, a i ∈ maximalIdeal k := fun i hi =>
    hY.1 ▸ Ideal.subset_span (Finset.mem_coe.mpr (Finset.mem_image_of_mem a hi))
  have hCq : ∀ i ∈ F₁, (C (a i) : MvPolynomial (Fin r) k) ∈ q := fun i hi => by
    rw [← Ideal.mem_comap, hq]; exact haM i hi
  have hmax : maximalIdeal (Localization.AtPrime q) =
      q.map (algebraMap _ (Localization.AtPrime q)) :=
    (Localization.AtPrime.map_eq_maximalIdeal).symm
  -- the constants
  have h₁ : RSOPIndep F₁ v := by
    refine RSOPIndep.of_extends ?_ ?_
    · intro i hi j hj hij
      have hij' : v i = v j := hij
      rw [hv₁ i hi, hv₁ j hj] at hij'
      exact ha hi hj (C_injective _ _ (hinjA hij'))
    obtain ⟨hreg, hdim⟩ := mvPoly_loc_quotient_maximalIdeal q hq
    have hspan : Ideal.span ((F₁.image v : Finset _) : Set (Localization.AtPrime q)) =
        ((maximalIdeal k).map (C : k →+* MvPolynomial (Fin r) k)).map
          (algebraMap _ (Localization.AtPrime q)) := by
      apply le_antisymm
      · rw [Ideal.span_le]
        intro y hy
        obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hy)
        rw [SetLike.mem_coe, hv₁ i hi]
        exact Ideal.mem_map_of_mem _ (Ideal.mem_map_of_mem _ (haM i hi))
      · rw [← hY.1, Ideal.map_span, Ideal.map_span, Ideal.span_le]
        rintro _ ⟨_, ⟨c, hc, rfl⟩, rfl⟩
        obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hc)
        exact Ideal.subset_span (by
          rw [Finset.coe_image]
          exact ⟨i, Finset.mem_coe.mpr hi, hv₁ i hi⟩)
    have : IsRegularLocalRing (Localization.AtPrime q ⧸
        Ideal.span ((F₁.image v : Finset _) : Set (Localization.AtPrime q))) := by
      rw [hspan]; exact hreg
    refine rsop_extends_of_quotient_regular (fun y hy => ?_) ?_
    · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hy
      rw [hv₁ i hi, hmax]
      exact Ideal.mem_map_of_mem _ (hCq i hi)
    · have hcard : ((F₁.image v).card : WithBot ℕ∞) ≤ ringKrullDim k := by
        rw [← hY.2, Finset.card_image_of_injOn ha]
        exact_mod_cast Finset.card_image_le
      calc _ ≤ ringKrullDim (Localization.AtPrime q ⧸
              ((maximalIdeal k).map (C : k →+* MvPolynomial (Fin r) k)).map
                (algebraMap _ (Localization.AtPrime q))) + ringKrullDim k := by
            rw [hspan]
            exact add_le_add le_rfl hcard
        _ ≤ _ := hdim
  -- the variables
  refine RSOPIndep.union hdisj h₁ fun i hi => ?_
  obtain ⟨j, hjq, hvi⟩ := hv₂ i hi
  refine ⟨?_, ?_⟩
  · rw [hvi, hmax]
    exact Ideal.mem_map_of_mem _ hjq
  · rw [hvi]
    refine mvPoly_X_notMem_span_sup_sq q j hjq _ ?_
    rintro _ ⟨x, ⟨hx, hxi⟩, rfl⟩
    rcases Finset.mem_union.mp (Finset.mem_coe.mp hx) with hx | hx
    · exact ⟨C (a x), hCq x hx, by rw [pderiv_C]; exact zero_mem _, hv₁ x hx⟩
    · obtain ⟨j', hj'q, hvx⟩ := hv₂ x hx
      refine ⟨X j', hj'q, ?_, hvx⟩
      rw [pderiv_X_of_ne]
      · exact zero_mem _
      · intro h
        apply hxi
        rw [Set.mem_singleton_iff]
        apply hinj₂ hx hi
        rw [hvx, hvi, h]

end PolyRSOP

namespace MonoidalTransform

variable {R : Type u} [CommRing R] [IsRegularLocalRing R] [IsDomain R] {P : Ideal R}

/-- `p/x ∈ R'` for `p ∈ P`, since `PR' = (x)R'`. -/
private theorem exists_mul_eq_toRing (s : MonoidalTransform R P) {p : R} (hp : p ∈ P) :
    ∃ u : s.ring, s.xR * u = s.toRing p := by
  have := s.span_xR_eq_map ▸ Ideal.mem_map_of_mem s.toRing hp
  obtain ⟨u, hu⟩ := Ideal.mem_span_singleton'.mp this
  exact ⟨u, by rw [mul_comm]; exact hu⟩

private theorem toRing_ne_zero (s : MonoidalTransform R P) {a : R} (ha : a ≠ 0) :
    s.toRing a ≠ 0 :=
  fun h => ha (MonoidalTransform.toRing_injective s (h.trans (map_zero _).symm))

/-- Elements of `R[x⁻¹P]` become elements of `R` after multiplication by a power of `x`. -/
private theorem exists_algebraMap_mul_pow_eq_toRing (s : MonoidalTransform R P) (a : blowupAlgebra R P s.x) :
    ∃ (k : ℕ) (g : R), algebraMap _ s.ring a * s.xR ^ k = s.toRing g := by
  obtain ⟨k, g, -, hag⟩ :=
    MonoidalTransform.exists_mul_pow_eq_of_mem_blowupAlgebra s.x_mem s.x_ne_zero a.2
  refine ⟨k, g, ?_⟩
  have : a * algebraMap R _ s.x ^ k = algebraMap R _ g := Subtype.ext (by simpa using hag)
  rw [MonoidalTransform.xR, MonoidalTransform.toRing, RingHom.comp_apply, ← map_pow,
    ← map_mul, this]
  rfl

/-- Every element `y` of `IR'` has, after multiplication by a unit `u` of `R'` (the image of an
element of `R[x⁻¹P]` outside `M'`) and by a power `xᵐ`, the form `F` with `F ∈ I`. -/
private theorem exists_mul_eq_toRing_of_mem_map (s : MonoidalTransform R P) (I : Ideal R)
    {y : s.ring} (hy : y ∈ I.map s.toRing) :
    ∃ (u : blowupAlgebra R P s.x) (_ : u ∉ s.M') (m : ℕ) (F : R), F ∈ I ∧
      y * algebraMap _ s.ring u * s.xR ^ m = s.toRing F := by
  induction hy using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨f, hf, rfl⟩ := hy
    exact ⟨1, s.isPrime.ne_top ∘ (Ideal.eq_top_of_isUnit_mem _ · isUnit_one), 0, f, hf,
      by simp⟩
  | zero => exact ⟨1, s.isPrime.ne_top ∘ (Ideal.eq_top_of_isUnit_mem _ · isUnit_one), 0, 0,
      zero_mem _, by simp⟩
  | add y₁ y₂ _ _ h₁ h₂ =>
    obtain ⟨u₁, hu₁, m₁, F₁, hF₁, e₁⟩ := h₁
    obtain ⟨u₂, hu₂, m₂, F₂, hF₂, e₂⟩ := h₂
    obtain ⟨k₁, g₁, r₁⟩ := exists_algebraMap_mul_pow_eq_toRing s u₁
    obtain ⟨k₂, g₂, r₂⟩ := exists_algebraMap_mul_pow_eq_toRing s u₂
    refine ⟨u₁ * u₂, fun h => (s.isPrime.mem_or_mem h).elim hu₁ hu₂, m₁ + m₂ + k₁ + k₂,
      F₁ * g₂ * s.x ^ (m₂ + k₁) + F₂ * g₁ * s.x ^ (m₁ + k₂), ?_, ?_⟩
    · exact Ideal.add_mem _ (I.mul_mem_right _ (I.mul_mem_right _ hF₁))
        (I.mul_mem_right _ (I.mul_mem_right _ hF₂))
    · have hxR : s.toRing s.x = s.xR := rfl
      simp only [map_add, map_mul, map_pow, hxR]
      rw [← e₁, ← e₂, ← r₁, ← r₂]
      ring
  | smul c y _ h =>
    obtain ⟨u, hu, m, F, hF, e₁⟩ := h
    obtain ⟨⟨a, b⟩, hab⟩ := IsLocalization.mk'_surjective s.M'.primeCompl c
    obtain ⟨k, g, r⟩ := exists_algebraMap_mul_pow_eq_toRing s a
    refine ⟨u * b, fun h => (s.isPrime.mem_or_mem h).elim hu b.2, m + k, F * g,
      I.mul_mem_right _ hF, ?_⟩
    have hc : c * algebraMap _ s.ring (b : blowupAlgebra R P s.x) = algebraMap _ s.ring a := by
      rw [← hab]; exact IsLocalization.mk'_spec _ _ _
    simp only [map_mul, smul_eq_mul]
    rw [← e₁, ← r, ← hc]
    ring

/-- The regular system of parameters `(z'_v)` of p. 169.  Given a regular system of parameters `Z` of `R` and `T ⊆ Z` generating the center `P`, there
are `z_t ∈ T` with `P R' = z_t R'` and elements `z'_z = φ z` of `R'` (`z ∈ Z`) with `z'_z = z` for
`z ∉ T`, `z'_{z_t} = z_t`, and `z_t z'_z = z` for `z ∈ T \ {z_t}`, such that those `z'_z` which
lie in the maximal ideal of `R'` are distinct and can be extended to a regular system of
parameters of `R'`.

Proof: writing `x = Σ c_t t`, `1 = Σ c_t (t/x)` in `R'`, so some `c_{t₀}` is a unit of `R` and
`t₀/x` a unit of `R'` (the second half is the key step of p. 209,
`MonoidalTransform.exists_index_isUnit_toRing_mul`; the unit `c_{t₀}` is needed here in addition); take
`z_t = t₀`.  The ring of fractions `A_M` of the paper, with `x` replaced by `z_t`, is
`MonoidalTransform.exists_equiv_of_span_eq`.  Then `(x, Z \ {t₀})` is a minimal system of generators of
`M`, and `R'/xR' ≅ (R/P)[X]_q` with `X_t ↦ t/x` (`exists_quotient_equiv_localization`).  The
`z'_z` other than `z_t` correspond, up to the unit `t₀/x`, to the constants `z ∈ Z \ T` (a regular
system of parameters of `R/P`) and to the variables lying in `q`, which are independent in
`(R/P)[X]_q` (`mvPoly_rsopIndep`); finally `z_t ∉ M'²` as `R'/z_tR'` is regular. -/
theorem exists_rsop_transform (s : MonoidalTransform R P) {Z T : Finset R}
    (hZ : IsRegularSystemOfParameters R Z) (hTZ : T ⊆ Z) (hT : Ideal.span (T : Set R) = P) :
    ∃ (zt : R) (φ : R → s.ring), zt ∈ T ∧
      Ideal.span {s.toRing zt} = P.map s.toRing ∧
      (∀ z ∈ Z, z ∉ T → φ z = s.toRing z) ∧ φ zt = s.toRing zt ∧
      (∀ z ∈ T, z ≠ zt → s.toRing zt * φ z = s.toRing z) ∧
      Set.InjOn φ {z | z ∈ Z ∧ φ z ∈ maximalIdeal s.ring} ∧
      ExtendsToRSOP s.ring ((Z.filter fun z => φ z ∈ maximalIdeal s.ring).image φ) := by
  subst hT
  have hTe : ExtendsToRSOP R T := ⟨Z, hTZ, hZ⟩
  have hPp : (Ideal.span (T : Set R)).IsPrime := hTe.isPrime_span
  have hS : IsRegularLocalRing (R ⧸ Ideal.span (T : Set R)) := hTe.isRegularLocalRing_quotient
  have hP0 : Ideal.span (T : Set R) ≠ ⊥ := fun h =>
    s.x_ne_zero ((Submodule.eq_bot_iff _).mp h _ s.x_mem)
  obtain ⟨hreg, -, -⟩ := s.isRegularLocalRing_and_isLocalHom_and_span_xR_eq_map hPp hP0 hS
  have hQreg : IsRegularLocalRing (s.ring ⧸ Ideal.span {s.xR}) := s.isRegularLocalRing_quotient_span_xR hPp hS
  have hZM : ∀ z ∈ Z, z ∈ maximalIdeal R := fun z hz => hZ.1 ▸ Ideal.subset_span hz
  have hTP : ∀ t ∈ T, t ∈ Ideal.span (T : Set R) := fun t ht => Ideal.subset_span ht
  have hxR0 : s.xR ≠ 0 := toRing_ne_zero s s.x_ne_zero
  -- the quotients `t/x`
  have hu : ∀ p, ∃ u : s.ring, p ∈ Ideal.span (T : Set R) → s.xR * u = s.toRing p := by
    intro p
    by_cases hp : p ∈ Ideal.span (T : Set R)
    · obtain ⟨u, hu⟩ := exists_mul_eq_toRing s hp
      exact ⟨u, fun _ => hu⟩
    · exact ⟨0, fun h => absurd h hp⟩
  choose u hu using hu
  -- `x = Σ c_t t`, hence `1 = Σ c_t (t/x)`
  obtain ⟨c, -, hc⟩ := Submodule.mem_span_finset.mp
    (s.x_mem : s.x ∈ Submodule.span R (T : Set R))
  have hsum : ∑ t ∈ T, s.toRing (c t) * u t = 1 := by
    apply mul_left_cancel₀ hxR0
    rw [Finset.mul_sum, mul_one]
    calc ∑ t ∈ T, s.xR * (s.toRing (c t) * u t) = ∑ t ∈ T, s.toRing (c t • t) := by
          refine Finset.sum_congr rfl fun t ht => ?_
          rw [smul_eq_mul, map_mul, ← hu t (hTP t ht)]
          ring
      _ = s.xR := by rw [← map_sum, hc]; rfl
  obtain ⟨t₀, ht₀T, ht₀⟩ : ∃ t ∈ T, s.toRing (c t) * u t ∉ maximalIdeal s.ring := by
    by_contra h
    push Not at h
    have h1 : ∑ t ∈ T, s.toRing (c t) * u t ∈ maximalIdeal s.ring := Ideal.sum_mem _ h
    rw [hsum] at h1
    exact (IsLocalRing.mem_maximalIdeal _).mp h1 isUnit_one
  have hct₀ : c t₀ ∉ maximalIdeal R := fun h =>
    ht₀ (Ideal.mul_mem_right _ _ (map_nonunit s.toRing _ h))
  have hut₀ : IsUnit (u t₀) := by
    by_contra h
    exact ht₀ (Ideal.mul_mem_left _ _ ((IsLocalRing.mem_maximalIdeal _).mpr h))
  have hxt₀ : s.xR * u t₀ = s.toRing t₀ := hu t₀ (hTP t₀ ht₀T)
  have hspan₀ : Ideal.span {s.toRing t₀} = Ideal.span {s.xR} :=
    (Ideal.span_singleton_eq_span_singleton.mpr ⟨hut₀.unit, hxt₀⟩).symm
  -- the quotients `z/z_t`
  have hw : ∀ p, ∃ w : s.ring, p ∈ Ideal.span (T : Set R) → s.toRing t₀ * w = s.toRing p := by
    intro p
    by_cases hp : p ∈ Ideal.span (T : Set R)
    · have hm : s.toRing p ∈ Ideal.span {s.toRing t₀} := by
        rw [hspan₀, s.span_xR_eq_map]
        exact Ideal.mem_map_of_mem _ hp
      obtain ⟨w, hw⟩ := Ideal.mem_span_singleton'.mp hm
      exact ⟨w, fun _ => by rw [mul_comm]; exact hw⟩
    · exact ⟨0, fun h => absurd h hp⟩
  choose w hw using hw
  have huw : ∀ t ∈ T, u t₀ * w t = u t := by
    intro t ht
    apply mul_left_cancel₀ hxR0
    rw [← mul_assoc, hxt₀, hw t (hTP t ht), hu t (hTP t ht)]
  set φ : R → s.ring := fun z => if z ∈ T ∧ z ≠ t₀ then w z else s.toRing z with hφ
  have hφ₁ : ∀ z, z ∉ T → φ z = s.toRing z := fun z hz => ite_eq_right (fun h => hz h.1)
  have hφ₀ : φ t₀ = s.toRing t₀ := ite_eq_right (fun h => h.2 rfl)
  have hφ₂ : ∀ z ∈ T, z ≠ t₀ → φ z = w z := fun z hz hne => ite_eq_left ⟨hz, hne⟩
  refine ⟨t₀, φ, ht₀T, hspan₀.trans s.span_xR_eq_map, fun z _ hz => hφ₁ z hz, hφ₀,
    fun z hz hne => by rw [hφ₂ z hz hne]; exact hw z (hTP z hz), ?_⟩
  set F := Z.filter fun z => φ z ∈ maximalIdeal s.ring with hF
  suffices hind : RSOPIndep F φ by
    obtain ⟨hinj, hext⟩ := hind.injOn_and_extends
    refine ⟨fun a ha b hb hab => hinj ?_ ?_ hab, hext⟩
    · exact Finset.mem_coe.mpr (Finset.mem_filter.mpr ha)
    · exact Finset.mem_coe.mpr (Finset.mem_filter.mpr hb)
  -- a minimal system of generators `{x} ∪ (Z \ {t₀})` of `M`
  have ht₀mem : ∀ {I : Ideal R}, s.x ∈ I → (∀ t ∈ T.erase t₀, t ∈ I) → t₀ ∈ I := by
    intro I hxI hTI
    obtain ⟨v, hv⟩ :=
      ((IsLocalRing.mem_maximalIdeal _).not.mp hct₀ |> not_not.mp).exists_left_inv
    have hsplit : c t₀ * t₀ = s.x - ∑ a ∈ T.erase t₀, c a • a := by
      rw [← hc, ← Finset.add_sum_erase T _ ht₀T, smul_eq_mul]
      ring
    have : t₀ = v * (s.x - ∑ a ∈ T.erase t₀, c a • a) := by
      rw [← hsplit, ← mul_assoc, hv, one_mul]
    rw [this]
    exact I.mul_mem_left _ (sub_mem hxI (sum_mem fun a ha => I.smul_mem _ (hTI a ha)))
  have hxM : s.x ∈ maximalIdeal R :=
    (Ideal.span_le.mpr fun t ht => hZM t (hTZ (Finset.mem_coe.mp ht))) s.x_mem
  have hTeZ : ∀ a ∈ T.erase t₀, a ∈ Z.erase t₀ := fun a ha =>
    Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp ha).1, hTZ (Finset.mem_erase.mp ha).2⟩
  set S := insert s.x (Z.erase t₀) with hSdef
  have hSM : Ideal.span (S : Set R) = maximalIdeal R := by
    refine le_antisymm (Ideal.span_le.mpr ?_) ?_
    · rw [hSdef, Finset.coe_insert]
      exact Set.insert_subset hxM fun a ha => hZM a (Finset.mem_of_mem_erase ha)
    · rw [← hZ.1, Ideal.span_le]
      intro z hz
      by_cases hzt : z = t₀
      · rw [hzt]
        refine ht₀mem (Ideal.subset_span (Finset.mem_coe.mpr (Finset.mem_insert_self _ _)))
          fun t ht => Ideal.subset_span (Finset.mem_coe.mpr
            (Finset.mem_insert_of_mem (hTeZ t ht)))
      · exact Ideal.subset_span (Finset.mem_coe.mpr (Finset.mem_insert_of_mem
          (Finset.mem_erase.mpr ⟨hzt, Finset.mem_coe.mp hz⟩)))
  have hZcard := rsop_card_eq_spanFinrank hZ
  have hScard : S.card = (maximalIdeal R).spanFinrank := by
    have h1 := rsop_spanFinrank_le_card hSM
    have h2 : S.card ≤ (Z.erase t₀).card + 1 := Finset.card_insert_le _ _
    have h3 := Finset.card_erase_add_one (hTZ ht₀T)
    omega
  have hxS : s.x ∉ Z.erase t₀ := by
    intro h
    have h1 : S = Z.erase t₀ := Finset.insert_eq_of_mem h
    have h2 := hScard
    rw [h1] at h2
    have h3 := Finset.card_erase_add_one (hTZ ht₀T)
    omega
  set eT := (T.erase t₀).equivFin with heT
  set zf : Fin ((T.erase t₀).card + 1) → R :=
    Fin.cons s.x (fun i => ((eT.symm i : T.erase t₀) : R)) with hzf
  have hzf_succ : ∀ i, zf i.succ = ((eT.symm i : T.erase t₀) : R) := fun i => by
    simp only [hzf, Fin.cons_succ]
  have hrange : Set.range (fun i => ((eT.symm i : T.erase t₀) : R)) = (T.erase t₀ : Set R) := by
    ext a
    constructor
    · rintro ⟨i, rfl⟩
      exact (eT.symm i).2
    · intro ha
      exact ⟨eT ⟨a, ha⟩, by simp⟩
  have hzinj : Function.Injective zf := by
    rw [hzf, Fin.cons_injective_iff]
    refine ⟨fun ⟨i, hi⟩ => hxS ?_, fun i j hij => eT.symm.injective (Subtype.ext hij)⟩
    rw [← hi]
    exact hTeZ _ (eT.symm i).2
  have hzS : ∀ i, zf i ∈ S := by
    intro i
    refine Fin.cases ?_ (fun i => ?_) i
    · simp only [hzf, Fin.cons_zero, hSdef]
      exact Finset.mem_insert_self _ _
    · rw [hzf_succ]
      exact Finset.mem_insert_of_mem (hTeZ _ (eT.symm i).2)
  have hzP : Ideal.span (Set.range zf) = Ideal.span (T : Set R) := by
    rw [hzf, Fin.range_cons, hrange]
    refine le_antisymm (Ideal.span_le.mpr (Set.insert_subset s.x_mem fun a ha =>
      Ideal.subset_span (Finset.mem_of_mem_erase ha))) (Ideal.span_le.mpr fun t ht => ?_)
    by_cases htt : t = t₀
    · rw [htt]
      exact ht₀mem (Ideal.subset_span (Set.mem_insert _ _))
        fun a ha => Ideal.subset_span (Set.mem_insert_of_mem _ ha)
    · exact Ideal.subset_span (Set.mem_insert_of_mem _
        (Finset.mem_coe.mpr (Finset.mem_erase.mpr ⟨htt, ht⟩)))
  have hzsP : ∀ i : Fin (T.erase t₀).card, zf i.succ ∈ Ideal.span (T : Set R) := by
    intro i
    rw [← hzP]
    exact Ideal.subset_span ⟨i.succ, rfl⟩
  have : (Ideal.span (T : Set R)).IsPrime := hPp
  obtain ⟨q, hq, e, hqC, -, hCe, hXe⟩ :=
    s.exists_quotient_equiv_localization hS hSM hScard hzinj hzS (Fin.cons_zero _ _) hzP
  have hXe' := hXe (fun i => u (zf i.succ)) (fun i => hu _ (hzsP i))
  have : IsRegularLocalRing (s.ring ⧸ Ideal.span {s.xR}) := hQreg
  have hBreg : IsRegularLocalRing (Localization.AtPrime q) :=
    IsRegularLocalRing.of_ringEquiv (R := s.ring ⧸ Ideal.span {s.xR}) e.symm
  have := isDomain_of_isRegularLocalRing (R ⧸ Ideal.span (T : Set R))
  -- the index sets
  have ht₀F : t₀ ∈ F := Finset.mem_filter.mpr ⟨hTZ ht₀T, by
    rw [hφ₀]; exact map_nonunit s.toRing _ (hZM _ (hTZ ht₀T))⟩
  set G := F.erase t₀ with hGdef
  set F₁ := G.filter fun z => z ∉ T with hF₁def
  set F₂ := G.filter fun z => ¬ (z ∉ T) with hF₂def
  have hG12 : F₁ ∪ F₂ = G := Finset.filter_union_filter_not_eq _ _
  have hmemG : ∀ z ∈ G, z ∈ Z ∧ φ z ∈ maximalIdeal s.ring ∧ z ≠ t₀ := by
    intro z hz
    obtain ⟨hne, hzF⟩ := Finset.mem_erase.mp hz
    obtain ⟨hzZ, hzm⟩ := Finset.mem_filter.mp hzF
    exact ⟨hzZ, hzm, hne⟩
  have hF₁ : F₁ = Z \ T := by
    ext z
    simp only [hF₁def, hGdef, hF, Finset.mem_filter, Finset.mem_erase, Finset.mem_sdiff]
    constructor
    · rintro ⟨⟨-, hzZ, -⟩, hzT⟩
      exact ⟨hzZ, hzT⟩
    · rintro ⟨hzZ, hzT⟩
      refine ⟨⟨fun h => hzT (h ▸ ht₀T), hzZ, ?_⟩, hzT⟩
      rw [hφ₁ z hzT]
      exact map_nonunit s.toRing _ (hZM z hzZ)
  set mkP := Ideal.Quotient.mk (Ideal.span (T : Set R)) with hmkP
  set mkQ := Ideal.Quotient.mk (Ideal.span {s.xR}) with hmkQ
  obtain ⟨_, hrsopq, hcardq⟩ := rsop_quotient hZ hTZ
  have hY : IsRegularSystemOfParameters (R ⧸ Ideal.span (T : Set R)) (F₁.image mkP) := by
    rw [hF₁]; exact hrsopq
  have hinjP : Set.InjOn mkP F₁ := by
    rw [hF₁]
    exact Finset.card_image_iff.mp hcardq
  -- the family in `(R/P)[X]_q`
  set v' : R → Localization.AtPrime q := fun z =>
    if h : z ∈ T.erase t₀ then
      algebraMap _ _ (MvPolynomial.X (eT ⟨z, h⟩) : MvPolynomial _ (R ⧸ Ideal.span (T : Set R)))
    else algebraMap _ _ (MvPolynomial.C (mkP z) : MvPolynomial (Fin (T.erase t₀).card) _)
    with hv'
  have hinjA := IsLocalization.injective (S := Localization.AtPrime q)
    (Ideal.primeCompl_le_nonZeroDivisors q)
  have hv₁ : ∀ z ∈ F₁, v' z = algebraMap _ _ (MvPolynomial.C (mkP z) :
      MvPolynomial (Fin (T.erase t₀).card) _) := by
    intro z hz
    have hzT : z ∉ T := (Finset.mem_filter.mp hz).2
    exact dite_eq_right fun h => hzT (Finset.mem_of_mem_erase h)
  have hmemF₂ : ∀ z ∈ F₂, z ∈ T.erase t₀ := by
    intro z hz
    obtain ⟨hzG, hzT⟩ := Finset.mem_filter.mp hz
    exact Finset.mem_erase.mpr ⟨(hmemG z hzG).2.2, not_not.mp hzT⟩
  have hv'X : ∀ z (h : z ∈ T.erase t₀), v' z = algebraMap _ _
      (MvPolynomial.X (eT ⟨z, h⟩) : MvPolynomial _ (R ⧸ Ideal.span (T : Set R))) :=
    fun z h => dite_eq_left h
  have hzfe : ∀ z (h : z ∈ T.erase t₀), zf (eT ⟨z, h⟩).succ = z := by
    intro z h
    rw [hzf_succ, Equiv.symm_apply_apply]
  have hv₂ : ∀ z ∈ F₂, ∃ j, (MvPolynomial.X j : MvPolynomial _ (R ⧸ Ideal.span (T : Set R))) ∈ q ∧
      v' z = algebraMap _ _ (MvPolynomial.X j : MvPolynomial _ (R ⧸ Ideal.span (T : Set R))) := by
    intro z hz
    have h := hmemF₂ z hz
    refine ⟨eT ⟨z, h⟩, (hXe' (eT ⟨z, h⟩)).1.mpr ?_, hv'X z h⟩
    show u (zf (eT ⟨z, h⟩).succ) ∈ maximalIdeal s.ring
    rw [hzfe, ← huw z (Finset.mem_of_mem_erase h), ← hφ₂ z (Finset.mem_of_mem_erase h)
      (Finset.ne_of_mem_erase h)]
    exact Ideal.mul_mem_left _ _ (hmemG z (Finset.mem_of_mem_filter z hz)).2.1
  have hinj₂ : Set.InjOn v' F₂ := by
    intro z₁ h₁ z₂ h₂ h12
    have k₁ := hmemF₂ z₁ h₁
    have k₂ := hmemF₂ z₂ h₂
    have h12' : v' z₁ = v' z₂ := h12
    rw [hv'X z₁ k₁, hv'X z₂ k₂] at h12'
    have := eT.injective (MvPolynomial.X_injective (hinjA h12'))
    exact congrArg Subtype.val this
  have indB : RSOPIndep G v' := by
    rw [← hG12]
    exact mvPoly_rsopIndep q hqC (Finset.disjoint_filter_filter_not _ _ _) mkP hY hinjP v'
      hv₁ hv₂ hinj₂
  -- transport to `R'/xR'`
  have indB' : RSOPIndep G (fun z => e.symm (mkQ (φ z))) := by
    refine indB.of_associated fun z hz => ?_
    by_cases hzT : z ∈ T
    · have hne := (hmemG z hz).2.2
      have h : z ∈ T.erase t₀ := Finset.mem_erase.mpr ⟨hne, hzT⟩
      have hv'z : v' z = e.symm (mkQ (u z)) := by
        rw [hv'X z h, RingEquiv.eq_symm_apply, (hXe' (eT ⟨z, h⟩)).2]
        show mkQ (u (zf (eT ⟨z, h⟩).succ)) = mkQ (u z)
        rw [hzfe]
      have hU : IsUnit (e.symm (mkQ (u t₀))) := (hut₀.map mkQ).map e.symm
      refine Associated.symm ⟨hU.unit, ?_⟩
      rw [IsUnit.unit_spec, ← map_mul, ← map_mul, hφ₂ z hzT hne, mul_comm, huw z hzT, hv'z]
    · have : e.symm (mkQ (φ z)) = v' z := by
        rw [hφ₁ z hzT, ← hCe z, RingEquiv.symm_apply_apply]
        symm
        exact dite_eq_right fun h => hzT (Finset.mem_of_mem_erase h)
      rw [this]
      exact Associated.refl _
  have indQ : RSOPIndep G (fun z => mkQ (φ z)) := by
    have := indB'.map_ringEquiv e
    simp only [RingEquiv.apply_symm_apply] at this
    exact this
  -- `z_t ∉ M'²`, and the union
  have hG0 : RSOPIndep {t₀} φ := by
    intro z hz
    rw [Finset.mem_singleton] at hz
    subst hz
    refine ⟨by rw [hφ₀]; exact map_nonunit s.toRing _ (hZM _ (hTZ ht₀T)), ?_⟩
    have hempty : φ '' (((({z} : Finset R) : Set R)) \ {z}) = ∅ := by simp
    rw [hempty, Ideal.span_empty, bot_sup_eq, hφ₀]
    have : IsRegularLocalRing (s.ring ⧸ Ideal.span {s.toRing z}) := by
      rw [hspan₀]; exact hQreg
    exact rsop_notMem_sq_of_quotient (map_nonunit s.toRing _ (hZM _ (hTZ ht₀T)))
      (toRing_ne_zero s (hTe.ne_zero ht₀T))
  have hJ : Ideal.span {s.xR} = Ideal.span (φ '' (({t₀} : Finset R) : Set R)) := by
    rw [Finset.coe_singleton, Set.image_singleton, hφ₀, hspan₀]
  have hall := RSOPIndep.union_of_quotient
    (Finset.disjoint_singleton_left.mpr (Finset.notMem_erase t₀ F)) hG0 hJ indQ
  rwa [← Finset.insert_eq, Finset.insert_erase ht₀F] at hall

/-- The strict transform of `(∏ J)`, `J ⊆ Z` (p. 169: "the strict transform F_j' of F_j contains
the point x' if and only if j ≠ t and z'_j ∈ M, in which case F_j' is defined by z'_j = 0"): with
`z_t`, `φ` as in `exists_rsop_transform`, the saturation of `(∏ J) R'` with respect to
`P R' = (z_t)` is
generated by the product of those `z'_z`, `z ∈ J`, `z ≠ z_t`, which lie in the maximal ideal of
`R'`.  (The `z'_z` outside the maximal ideal are units; the others are distinct members of a
regular system of parameters, hence generate primes not containing `z_t`.) -/
theorem saturation_span_prod (s : MonoidalTransform R P) {Z T J : Finset R}
    (hZ : IsRegularSystemOfParameters R Z) (hTZ : T ⊆ Z) (hT : Ideal.span (T : Set R) = P)
    (hJZ : J ⊆ Z) {zt : R} {φ : R → s.ring} (hzt : zt ∈ T)
    (hspan : Ideal.span {s.toRing zt} = P.map s.toRing)
    (hφ₁ : ∀ z ∈ Z, z ∉ T → φ z = s.toRing z) (hφ₂ : φ zt = s.toRing zt)
    (hφ₃ : ∀ z ∈ T, z ≠ zt → s.toRing zt * φ z = s.toRing z)
    (hinj : Set.InjOn φ {z | z ∈ Z ∧ φ z ∈ maximalIdeal s.ring})
    (hext : ExtendsToRSOP s.ring ((Z.filter fun z => φ z ∈ maximalIdeal s.ring).image φ)) :
    ⨆ n : ℕ, (Ideal.span {s.toRing (∏ z ∈ J, z)}).colon
        ((Ideal.span {s.toRing zt} ^ n : Ideal s.ring) : Set s.ring) =
      Ideal.span {∏ z ∈ ((J.erase zt).filter fun z => φ z ∈ maximalIdeal s.ring), φ z} := by
  have _ := hspan
  have hZ' := ExtendsToRSOP.of_isRegularSystemOfParameters hZ
  -- `R'` is regular (p. 209)
  have hTe : ExtendsToRSOP R T := hZ'.mono hTZ
  have hPp : P.IsPrime := hT ▸ hTe.isPrime_span
  have hS : IsRegularLocalRing (R ⧸ P) := hT ▸ hTe.isRegularLocalRing_quotient
  have hP0 : P ≠ ⊥ := fun h => s.x_ne_zero (by simpa [h] using s.x_mem)
  have : IsRegularLocalRing s.ring := (s.isRegularLocalRing_and_isLocalHom_and_span_xR_eq_map hPp hP0 hS).1
  set M' := maximalIdeal s.ring with hM'
  set y := s.toRing zt with hy
  set Jf := (J.erase zt).filter fun z => φ z ∈ M' with hJf
  set Pr := ∏ z ∈ Jf, φ z with hPr
  have hZM : ∀ z ∈ Z, s.toRing z ∈ M' := fun z hz =>
    map_nonunit s.toRing _ (hZ'.mem_maximalIdeal hz)
  have hztZ := hTZ hzt
  have hJfJ : Jf ⊆ J := (Finset.filter_subset _ _).trans (Finset.erase_subset _ _)
  have hmemJf : ∀ z ∈ Jf, z ∈ J ∧ z ≠ zt ∧ φ z ∈ M' := by
    intro z hz
    obtain ⟨h1, h2⟩ := Finset.mem_filter.mp hz
    exact ⟨Finset.mem_of_mem_erase h1, Finset.ne_of_mem_erase h1, h2⟩
  have hinJf : ∀ z ∈ J, z ≠ zt → φ z ∈ M' → z ∈ Jf := fun z hz hne hm =>
    Finset.mem_filter.mpr ⟨Finset.mem_erase.mpr ⟨hne, hz⟩, hm⟩
  -- `(∏ J) ∣ Pr · z_tⁿ` and `Pr ∣ ∏ J` in `R'`
  have hdiv : ∀ z ∈ J, s.toRing z ∣ (if z ∈ Jf then φ z else 1) * y := by
    intro z hz
    by_cases hzT : z ∈ T
    · by_cases hzz : z = zt
      · have : z ∉ Jf := fun h => (hmemJf z h).2.1 hzz
        rw [ite_eq_right this, one_mul, hy, hzz]
      · rw [← hφ₃ z hzT hzz]
        by_cases hm : φ z ∈ M'
        · rw [ite_eq_left (hinJf z hz hzz hm), mul_comm]
        · have : z ∉ Jf := fun h => hm (hmemJf z h).2.2
          rw [ite_eq_right this, one_mul]
          obtain ⟨v, hv⟩ :=
            ((IsLocalRing.mem_maximalIdeal _).not.mp hm |> not_not.mp).exists_right_inv
          exact ⟨v, by rw [mul_assoc, hv, mul_one]⟩
    · have hzz : z ≠ zt := fun h => hzT (h ▸ hzt)
      have hm : φ z ∈ M' := by rw [hφ₁ z (hJZ hz) hzT]; exact hZM z (hJZ hz)
      rw [ite_eq_left (hinJf z hz hzz hm), hφ₁ z (hJZ hz) hzT]
      exact dvd_mul_right _ _
  have hprod : s.toRing (∏ z ∈ J, z) ∣ Pr * y ^ J.card := by
    rw [map_prod]
    calc ∏ z ∈ J, s.toRing z ∣ ∏ z ∈ J, (if z ∈ Jf then φ z else 1) * y :=
          Finset.prod_dvd_prod_of_dvd _ _ hdiv
      _ = Pr * y ^ J.card := by
          rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.prod_ite_mem,
            Finset.inter_eq_right.mpr hJfJ]
  have hPrdvd : Pr ∣ s.toRing (∏ z ∈ J, z) := by
    rw [map_prod]
    refine (Finset.prod_dvd_prod_of_dvd _ _ fun z hz => ?_).trans
      (Finset.prod_dvd_prod_of_subset _ _ _ hJfJ)
    obtain ⟨hzJ, hzz, -⟩ := hmemJf z hz
    by_cases hzT : z ∈ T
    · rw [← hφ₃ z hzT hzz]
      exact dvd_mul_left _ _
    · rw [hφ₁ z (hJZ hzJ) hzT]
  -- the members `φ z`, `z ∈ Jf`, and `z_t` are part of a regular system of parameters
  set L := Jf.image φ with hL
  have hKsub : insert y L ⊆ (Z.filter fun z => φ z ∈ M').image φ := by
    intro a ha
    rcases Finset.mem_insert.mp ha with rfl | ha
    · exact Finset.mem_image.mpr ⟨zt, Finset.mem_filter.mpr ⟨hztZ, by rw [hφ₂]; exact hZM _ hztZ⟩,
        hφ₂⟩
    · obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp ha
      exact Finset.mem_image_of_mem _ (Finset.mem_filter.mpr
        ⟨hJZ (hmemJf z hz).1, (hmemJf z hz).2.2⟩)
  have hK := hext.mono hKsub
  have hyL : ∀ l ∈ L, l ≠ y := by
    intro l hl hly
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hl
    obtain ⟨hzJ, hzz, hzm⟩ := hmemJf z hz
    refine hzz (hinj ⟨hJZ hzJ, hzm⟩ ⟨hztZ, by rw [hφ₂]; exact hZM _ hztZ⟩ ?_)
    rw [hly, hφ₂]
  have hPrL : Pr = ∏ l ∈ L, l := by
    rw [hL, Finset.prod_image]
    intro a ha b hb hab
    exact hinj ⟨hJZ (hmemJf a ha).1, (hmemJf a ha).2.2⟩ ⟨hJZ (hmemJf b hb).1, (hmemJf b hb).2.2⟩ hab
  have key : ∀ (a : s.ring) (n : ℕ), a * y ^ n ∈ Ideal.span {Pr} → a ∈ Ideal.span {Pr} := by
    intro a n ha
    rw [hPrL, ← (hK.mono (Finset.subset_insert _ _)).iInf_span_singleton] at ha ⊢
    refine Submodule.mem_iInf _ |>.mpr fun l => Submodule.mem_iInf _ |>.mpr fun hl => ?_
    have hl' := Submodule.mem_iInf _ |>.mp (Submodule.mem_iInf _ |>.mp ha l) hl
    have := hK.isPrime_span_singleton (Finset.mem_insert_of_mem hl)
    have hyl : y ∉ Ideal.span {l} := hK.notMem_span_singleton (Finset.mem_insert_of_mem hl)
      (Finset.mem_insert_self _ _) (hyL l hl)
    exact (Ideal.IsPrime.mem_or_mem this hl').resolve_right
      fun h => hyl (Ideal.IsPrime.mem_of_pow_mem this n h)
  apply le_antisymm
  · refine iSup_le fun n a ha => ?_
    have h1 : a * y ^ n ∈ Ideal.span {s.toRing (∏ z ∈ J, z)} := by
      have := Submodule.mem_colon.mp ha (y ^ n)
        (by rw [Ideal.span_singleton_pow]; exact Ideal.mem_span_singleton_self _)
      simpa [smul_eq_mul] using this
    exact key a n ((Ideal.span_singleton_le_span_singleton.mpr hPrdvd) h1)
  · rw [Ideal.span_le, Set.singleton_subset_iff]
    refine Ideal.mem_iSup_of_mem J.card (Submodule.mem_colon.mpr fun p hp => ?_)
    rw [Ideal.span_singleton_pow, SetLike.mem_coe, Ideal.mem_span_singleton'] at hp
    obtain ⟨c, rfl⟩ := hp
    rw [smul_eq_mul]
    exact Ideal.mem_span_singleton.mpr (hprod.trans ⟨c, by ring⟩)

/-- p. 169, used for the reducedness of strict transforms: the saturation of `I R'` with respect
to `P R' = x R'` is radical if `I` is.  (`R'[1/x]` is a localization of `R`, and the saturation
is the contraction of `I R'[1/x]`.) -/
theorem isRadical_saturation (s : MonoidalTransform R P) {I : Ideal R} (hI : I.IsRadical) :
    (⨆ n : ℕ, (I.map s.toRing).colon ((Ideal.span {s.xR} ^ n : Ideal s.ring) : Set s.ring)).IsRadical := by
  set N := I.map s.toRing with hN
  -- membership in the saturation
  have hmem : ∀ a : s.ring, a ∈ (⨆ n : ℕ, N.colon ((Ideal.span {s.xR} ^ n : Ideal s.ring) :
      Set s.ring)) ↔ ∃ n : ℕ, a * s.xR ^ n ∈ N := by
    intro a
    have hmono : Monotone (fun n : ℕ =>
        N.colon ((Ideal.span {s.xR} ^ n : Ideal s.ring) : Set s.ring)) := by
      intro m n hmn b hb
      refine Submodule.mem_colon.mpr fun p hp => Submodule.mem_colon.mp hb p ?_
      exact Ideal.pow_le_pow_right hmn hp
    rw [Submodule.mem_iSup_of_directed _ hmono.directed_le]
    constructor
    · rintro ⟨n, hn⟩
      refine ⟨n, ?_⟩
      have := Submodule.mem_colon.mp hn (s.xR ^ n)
        (by rw [Ideal.span_singleton_pow]; exact Ideal.mem_span_singleton_self _)
      simpa [smul_eq_mul] using this
    · rintro ⟨n, hn⟩
      refine ⟨n, Submodule.mem_colon.mpr fun p hp => ?_⟩
      rw [Ideal.span_singleton_pow, SetLike.mem_coe, Ideal.mem_span_singleton'] at hp
      obtain ⟨c, rfl⟩ := hp
      rw [smul_eq_mul, show a * (c * s.xR ^ n) = c * (a * s.xR ^ n) by ring]
      exact N.mul_mem_left c hn
  intro a ha
  obtain ⟨m, hm⟩ := ha
  obtain ⟨n, hn⟩ := (hmem _).mp hm
  rw [hmem]
  -- `a = g / (d xᵏ)` with `d` a unit
  obtain ⟨⟨b, d⟩, hbd⟩ := IsLocalization.mk'_surjective s.M'.primeCompl a
  have hd : a * algebraMap _ s.ring (d : blowupAlgebra R P s.x) = algebraMap _ s.ring b := by
    rw [← hbd]; exact IsLocalization.mk'_spec _ _ _
  have hdu : IsUnit (algebraMap _ s.ring (d : blowupAlgebra R P s.x)) :=
    IsLocalization.map_units s.ring d
  obtain ⟨k, g, hg⟩ := exists_algebraMap_mul_pow_eq_toRing s b
  have hag : a * algebraMap _ s.ring (d : blowupAlgebra R P s.x) * s.xR ^ k = s.toRing g := by
    rw [hd, hg]
  -- `g^m xⁿ ∈ IR'`
  have h1 : s.toRing (g ^ m * s.x ^ n) ∈ N := by
    have : s.toRing (g ^ m * s.x ^ n) = a ^ m * s.xR ^ n *
        (algebraMap _ s.ring (d : blowupAlgebra R P s.x) * s.xR ^ k) ^ m := by
      rw [map_mul, map_pow, map_pow, ← hag]
      simp only [MonoidalTransform.xR]
      ring
    rw [this]
    exact N.mul_mem_right _ hn
  obtain ⟨v, hv, m', F, hF, hvF⟩ := exists_mul_eq_toRing_of_mem_map s I h1
  obtain ⟨l, h, hh⟩ := exists_algebraMap_mul_pow_eq_toRing s v
  have hvu : IsUnit (algebraMap _ s.ring v) := IsLocalization.map_units s.ring (⟨v, hv⟩ : s.M'.primeCompl)
  -- `g^m x^(n+m') h = F x^l ∈ I` in `R`
  have h2 : g ^ m * s.x ^ (n + m') * h ∈ I := by
    have : s.toRing (g ^ m * s.x ^ (n + m') * h) = s.toRing (F * s.x ^ l) := by
      rw [map_mul, map_mul, ← hh, map_mul, map_pow, ← hvF]
      simp only [map_mul, map_pow, MonoidalTransform.xR]
      ring
    rw [MonoidalTransform.toRing_injective s this]
    exact I.mul_mem_right _ hF
  -- hence `g x h ∈ I`, `I` being radical
  have h3 : g * s.x * h ∈ I := by
    refine hI ⟨m + n + m' + 1, ?_⟩
    have : (g * s.x * h) ^ (m + n + m' + 1) = (g ^ m * s.x ^ (n + m') * h) *
        (g ^ (n + m' + 1) * s.x ^ (m + 1) * h ^ (m + n + m')) := by ring
    rw [this]
    exact I.mul_mem_right _ h2
  -- back in `R'`
  obtain ⟨vi, hvi⟩ := hvu.exists_right_inv
  obtain ⟨di, hdi⟩ := hdu.exists_right_inv
  refine ⟨k + 1 + l, ?_⟩
  have h4 := N.mul_mem_right (vi * di) (Ideal.mem_map_of_mem s.toRing h3)
  have : a * s.xR ^ (k + 1 + l) = s.toRing (g * s.x * h) * (vi * di) := by
    rw [map_mul, map_mul, ← hh, ← hag]
    simp only [MonoidalTransform.xR]
    calc a * s.toRing s.x ^ (k + 1 + l) = a * s.toRing s.x ^ (k + 1 + l) *
          ((algebraMap _ s.ring v * vi) * (algebraMap _ s.ring (d : blowupAlgebra R P s.x) * di)) := by
          rw [hvi, hdi, mul_one, mul_one]
      _ = _ := by ring
  rw [this]
  exact h4

end MonoidalTransform

end Hironaka

