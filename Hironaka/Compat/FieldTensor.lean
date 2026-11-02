/-
Copyright (c) 2026 Daattavya Aggarwal, Minhyong Kim, Oisin Kim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daattavya Aggarwal, Minhyong Kim, Oisin Kim
-/
module

public import Mathlib.Algebra.Algebra.IsSimpleRing
public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.FieldTheory.CardinalEmb
public import Mathlib.FieldTheory.PurelyInseparable.PerfectClosure
public import Mathlib.FieldTheory.SeparablyGenerated
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.Coalgebra.IsFrobenius
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.HopfAlgebra.Basic
public import Mathlib.RingTheory.LocalProperties.Reduced
public import Mathlib.RingTheory.PicardGroup
public import Mathlib.RingTheory.RegularLocalRing.Polynomial
public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.TensorProduct.Free
public import Mathlib.RingTheory.Unramified.LocalRing
public import Architect

/-!
# Compatibility layer: tensor products of field extensions (Ch. III §2, pp. 211–212)

The proof of Lemma 4 of Ch. III §2 (pp. 210–212) describes the monoidal transforms `R̄'` of `R̄`
which admit a canonical local homomorphism `R' → R̄'` through the prime ideals `q̄` of
`k̄ ⊗_k (k[X]/m̄')` lying over `(0)`, i.e. through the prime ideals of `k̄ ⊗_k k'`, where `k`,
`k̄` and `k'` are the residue fields of `R`, `R̄` and `R'`:

> Therefore, if either `R̄` or `R'` is residually algebraic over `R`, then the number of `R̄'`
> which admit a canonical local homomorphism `R' → R̄'` is equal to the number of the associated
> prime ideals of `m̄'k̄[X₂, …, X_r]`, which is obviously finite. In particular, if `R̄` is
> residually algebraic over `R`, then this number does not exceed the separable degree of the
> residue field extension `k → k̄`. … If `R̄` is residually separable over `R`, i.e., `k̄` is
> separable over `k` in the sense that for every purely inseparable extension `k'` over `k` the
> tensor product `k̄ ⊗_k k'` has no nilpotent elements, then for every prime ideal `q̄` …, the
> localization … with respect to `q̄` is regular.  (pp. 211–212)

This file proves the field-theoretic facts used there, for fields `k`, `K`, `L` with `K` and
`L` extensions of `k` (`K` plays the role of `k'`, `L` that of `k̄`).

## Main results
- `isReduced_tensorProduct_of_isSeparable`, `isField_localization_tensorProduct_of_isSeparable`:
  `L/k` separable algebraic ⇒ `K ⊗_k L` is reduced and its localizations at primes are fields.
- `finite_primeSpectrum_tensorProduct_of_finite`, `finite_primeSpectrum_tensorProduct_of_fg`:
  finiteness of `Spec (K ⊗_k L)`.
- `cardinalMk_primeSpectrum_tensorProduct_le_sepDegree_of_fg`: the bound by the separable degree
  (p. 211), for `K/k` finitely generated, as in Lemma 4. Formalization note: without a finiteness
  hypothesis the bound is false when the separable degree is infinite: for `k = ℚ`, `K = L = ℚ̄`
  the primes of `ℚ̄ ⊗_ℚ ℚ̄` correspond to the elements of `Gal(ℚ̄/ℚ)`, of cardinality `2 ^ ℵ₀`,
  while `Field.sepDegree ℚ ℚ̄ = ℵ₀`. The general bound is
  `cardinalMk_primeSpectrum_tensorProduct_le_cardinalMk_emb`.
- `isRegularLocalRing_localization_tensorProduct_of_separable`: "separable ⇒ geometrically
  regular" (p. 212), via Mac Lane's criterion and the ascent of regularity along flat maps
  `isRegularLocalRing_localization_of_flat_of_map_eq_maximalIdeal`.
-/

@[expose] public section

open scoped TensorProduct

namespace Hironaka

universe u

section FieldTensor

variable (k K L : Type u) [Field k] [Field K] [Field L] [Algebra k K] [Algebra k L]

/-- The finite case of `isReduced_tensorProduct_of_isSeparable`: if `L/k` is finite separable,
then `K ⊗_k L` is a finite unramified `K`-algebra (base change of the unramified `k`-algebra `L`),
hence reduced. -/
theorem isReduced_tensorProduct_of_finiteDimensional_of_isSeparable
    [FiniteDimensional k L] [Algebra.IsSeparable k L] : IsReduced (K ⊗[k] L) := by
  have : Algebra.FormallyUnramified k L := Algebra.FormallyUnramified.of_isSeparable k L
  have : Algebra.FormallyUnramified K (K ⊗[k] L) := inferInstance
  have : Algebra.EssFiniteType K (K ⊗[k] L) := inferInstance
  exact Algebra.FormallyUnramified.isReduced_of_field K (K ⊗[k] L)

/-- If `L/k` is separable algebraic, then `K ⊗_k L` is reduced.

`L` is the directed union of its finite separable subextensions and `K` is flat over `k`, so a
nilpotent of `K ⊗_k L` comes from some `K ⊗_k E` with `E/k` finite separable, which is reduced by
`isReduced_tensorProduct_of_finiteDimensional_of_isSeparable`. -/
@[blueprint "compat:field-tensor-reduced"
  (statement := /-- Let $K$ and $L$ be field extensions of a field $k$, with $L/k$ separable
    algebraic. Then $K\otimes_kL$ is reduced. -/)
  (proof := /-- $L$ is the directed union of its finite separable subextensions $E$, and $K$ is
    flat over $k$, so a nilpotent element of $K\otimes_kL$ comes from some $K\otimes_kE$; it
    suffices to treat $L/k$ finite. Then $L$ is unramified over $k$, so $K\otimes_kL$ is a finite
    unramified $K$-algebra, hence reduced (Mathlib's
    \texttt{Algebra.FormallyUnramified.isReduced\_of\_field}). -/)
  (latexEnv := "lemma")]
theorem isReduced_tensorProduct_of_isSeparable [Algebra.IsSeparable k L] :
    IsReduced (K ⊗[k] L) := by
  refine IsReduced.tensorProduct_of_flat_of_forall_fg fun B hB => ?_
  -- a finitely generated subalgebra `B = k[s]` lies in the finite separable extension `k(s)`
  obtain ⟨s, hs⟩ := hB
  let E : IntermediateField k L := IntermediateField.adjoin k (s : Set L)
  have hint : ∀ x ∈ s, IsIntegral k x := fun x _ =>
    (Algebra.IsSeparable.isSeparable k x).isIntegral
  have : FiniteDimensional k E := IntermediateField.finiteDimensional_adjoin hint
  have hBE : B ≤ E.toSubalgebra := hs ▸ IntermediateField.algebra_adjoin_le_adjoin k (s : Set L)
  have hred : IsReduced (K ⊗[k] E) :=
    isReduced_tensorProduct_of_finiteDimensional_of_isSeparable k K E
  -- `K ⊗_k B → K ⊗_k E` is injective since `K` is flat over the field `k`
  exact isReduced_of_injective
    (Algebra.TensorProduct.map (AlgHom.id k K) (Subalgebra.inclusion hBE))
    (Module.Flat.lTensor_preserves_injective_linearMap _ (Subalgebra.inclusion_injective hBE))

/-- If `L/k` is algebraic, then `K ⊗_k L` has Krull dimension zero: it is integral over the field
`K`, so every prime ideal lies over the maximal ideal `(0)` of `K` and is therefore maximal. -/
theorem ringKrullDimLE_zero_tensorProduct_of_isAlgebraic [Algebra.IsAlgebraic k L] :
    Ring.KrullDimLE 0 (K ⊗[k] L) := by
  have : Algebra.IsIntegral K (K ⊗[k] L) := inferInstance
  refine Ring.KrullDimLE.mk₀ fun I hI => ?_
  refine Ideal.isMaximal_of_isIntegral_of_isMaximal_under (R := K) I ?_
  have : (I.under K).IsPrime := Ideal.IsPrime.under K I
  rw [Ideal.eq_bot_of_prime (I.under K)]
  exact Ideal.bot_isMaximal

/-- If `L/k` is separable algebraic, then every localization of `K ⊗_k L` at a prime ideal is a
field (`K ⊗_k L` is reduced and integral over the field `K`, hence of dimension zero). -/
@[blueprint "compat:field-tensor-local-field"
  (statement := /-- Let $K$ and $L$ be field extensions of a field $k$, with $L/k$ separable
    algebraic. Then the localization of $K\otimes_kL$ at any prime ideal is a field. -/)
  (proof := /-- $K\otimes_kL$ is integral over the field $K$, so every prime ideal lies over
    $(0)$ and is maximal: $K\otimes_kL$ has dimension zero and every prime ideal is minimal. The
    localization at a prime is therefore a local ring of dimension zero, and it is reduced by
    \cref{compat:field-tensor-reduced}; a reduced local ring of dimension zero is a field. -/)
  (latexEnv := "lemma")]
theorem isField_localization_tensorProduct_of_isSeparable [Algebra.IsSeparable k L]
    (p : Ideal (K ⊗[k] L)) [p.IsPrime] : IsField (Localization.AtPrime p) := by
  have : IsReduced (K ⊗[k] L) := isReduced_tensorProduct_of_isSeparable k K L
  have : Ring.KrullDimLE 0 (K ⊗[k] L) := ringKrullDimLE_zero_tensorProduct_of_isAlgebraic k K L
  -- in dimension zero every prime is minimal, so the localization at `p` has dimension zero
  have hp : p ∈ minimalPrimes (K ⊗[k] L) := by
    rw [Ring.KrullDimLE.minimalPrimes_eq_setOfPred_isPrime]
    exact ‹p.IsPrime›
  have : Ring.KrullDimLE 0 (Localization.AtPrime p) := .of_isLocalization p hp _
  -- a reduced local ring of dimension zero is a field
  exact Ring.KrullDimLE.isField_of_isReduced

/-- If `K/k` is finite, then `K ⊗_k L` has only finitely many prime ideals (it is a finite
`L`-algebra). -/
@[blueprint "compat:field-tensor-finite-spec-finite"
  (statement := /-- Let $K$ and $L$ be field extensions of a field $k$ with $K/k$ finite. Then
    $K\otimes_kL$ has only finitely many prime ideals. -/)
  (proof := /-- $K\otimes_kL$ is a finite $L$-algebra, hence an artinian ring, and an artinian
    ring has only finitely many prime ideals. -/)
  (latexEnv := "lemma")]
theorem finite_primeSpectrum_tensorProduct_of_finite [Module.Finite k K] :
    Finite (PrimeSpectrum (K ⊗[k] L)) := by
  -- `L ⊗_k K` is a finite `L`-algebra, hence artinian, hence has finitely many primes
  have : IsArtinianRing (L ⊗[k] K) := IsArtinianRing.of_finite L (L ⊗[k] K)
  exact Finite.of_equiv _
    (PrimeSpectrum.comapEquiv (Algebra.TensorProduct.comm k L K).toRingEquiv).toEquiv

variable {k K L} in
/-- Denominators: if every element of `K` is a fraction of elements of the subalgebra `D`, then
every element of `K ⊗_k L` times some `d ⊗ 1` (`0 ≠ d ∈ D`) comes from `D ⊗_k L`. -/
theorem exists_mul_mem_range_tensorProduct_map_of_forall_div (D : Subalgebra k K)
    (hD : ∀ a : K, ∃ r ∈ D, ∃ s ∈ D, s ≠ 0 ∧ s * a = r) (x : K ⊗[k] L) :
    ∃ d : D, (d : K) ≠ 0 ∧ ∃ y : D ⊗[k] L,
      Algebra.TensorProduct.map D.val (AlgHom.id k L) y = ((d : K) ⊗ₜ[k] (1 : L)) * x := by
  induction x with
  | tmul a l =>
    obtain ⟨r, hr, s, hs, hs0, h⟩ := hD a
    exact ⟨⟨s, hs⟩, hs0, ⟨r, hr⟩ ⊗ₜ l, by simp [h]⟩
  | add x y hx hy =>
    obtain ⟨d₁, hd₁, y₁, h₁⟩ := hx
    obtain ⟨d₂, hd₂, y₂, h₂⟩ := hy
    refine ⟨d₁ * d₂, by simpa using mul_ne_zero hd₁ hd₂,
      (d₂ ⊗ₜ[k] (1 : L)) * y₁ + (d₁ ⊗ₜ[k] (1 : L)) * y₂, ?_⟩
    simp only [map_add, map_mul, h₁, h₂, Algebra.TensorProduct.map_tmul, Subalgebra.coe_val,
      AlgHom.coe_id, id_eq, Subalgebra.coe_mul]
    rw [← mul_assoc, ← mul_assoc, Algebra.TensorProduct.tmul_mul_tmul,
      Algebra.TensorProduct.tmul_mul_tmul, mul_add, mul_comm (d₂ : K), mul_one]

variable {k K} in
/-- A finitely generated field extension `K = k(s)` is the field of fractions of the finitely
generated `k`-algebra `k[s]`. -/
theorem exists_fg_subalgebra_forall_div (hK : (⊤ : IntermediateField k K).FG) :
    ∃ D : Subalgebra k K, D.FG ∧ ∀ a : K, ∃ r ∈ D, ∃ t ∈ D, t ≠ 0 ∧ t * a = r := by
  obtain ⟨s, hs⟩ := hK
  refine ⟨Algebra.adjoin k (s : Set K), ⟨s, rfl⟩, fun a => ?_⟩
  have ha : a ∈ IntermediateField.adjoin k (s : Set K) := hs ▸ IntermediateField.mem_top
  obtain ⟨r, hr, t, ht, rfl⟩ := IntermediateField.mem_adjoin_iff_div.mp ha
  by_cases ht0 : t = 0
  · exact ⟨0, Subalgebra.zero_mem _, 1, Subalgebra.one_mem _, one_ne_zero, by simp [ht0]⟩
  · exact ⟨r, hr, t, ht, ht0, by field_simp⟩

/-- If `K/k` is finitely generated, then `K ⊗_k L` is noetherian: it is a localization of
`D ⊗_k L` for a finitely generated `k`-algebra `D` with fraction field `K`, and `D ⊗_k L` is a
finitely generated `L`-algebra. -/
theorem isNoetherianRing_tensorProduct_of_fg (hK : (⊤ : IntermediateField k K).FG) :
    IsNoetherianRing (K ⊗[k] L) := by
  obtain ⟨D, hDfg, hD⟩ := exists_fg_subalgebra_forall_div hK
  have : Algebra.FiniteType k D := (Subalgebra.fg_iff_finiteType D).mp hDfg
  have : IsNoetherianRing (L ⊗[k] D) := Algebra.FiniteType.isNoetherianRing L (L ⊗[k] D)
  have : IsNoetherianRing (D ⊗[k] L) :=
    isNoetherianRing_of_ringEquiv _ (Algebra.TensorProduct.comm k L D).toRingEquiv
  let φ : D ⊗[k] L →ₐ[k] K ⊗[k] L := Algebra.TensorProduct.map D.val (AlgHom.id k L)
  have hφ : Function.Injective φ :=
    Module.Flat.rTensor_preserves_injective_linearMap (M := L) D.val.toLinearMap
      Subtype.val_injective
  let : Algebra (D ⊗[k] L) (K ⊗[k] L) := φ.toRingHom.toAlgebra
  let M : Submonoid (D ⊗[k] L) :=
    Algebra.algebraMapSubmonoid (D ⊗[k] L) (nonZeroDivisors D)
  have : IsLocalization M (K ⊗[k] L) := by
    refine ⟨?_, ?_, ?_⟩
    · rintro ⟨_, d, hd, rfl⟩
      have hd0 : (d : K) ≠ 0 := by
        simpa using nonZeroDivisors.ne_zero hd
      change IsUnit (φ (algebraMap D (D ⊗[k] L) d))
      simpa [φ, Algebra.TensorProduct.algebraMap_apply] using
        (isUnit_iff_ne_zero.mpr hd0).map (algebraMap K (K ⊗[k] L))
    · intro x
      obtain ⟨d, hd, y, hy⟩ := exists_mul_mem_range_tensorProduct_map_of_forall_div D hD x
      have hdM : algebraMap D (D ⊗[k] L) d ∈ M :=
        ⟨d, mem_nonZeroDivisors_of_ne_zero (by simpa using hd), rfl⟩
      refine ⟨(y, ⟨_, hdM⟩), ?_⟩
      change x * φ (algebraMap D (D ⊗[k] L) d) = φ y
      rw [hy, mul_comm]
      simp [φ, Algebra.TensorProduct.algebraMap_apply]
    · intro x y h
      exact ⟨1, by simpa using hφ h⟩
  exact IsLocalization.isNoetherianRing M _ inferInstance

/-- If `K/k` is finitely generated and `L/k` is algebraic, then `K ⊗_k L` has only finitely many
prime ideals (it is a noetherian ring of dimension zero: a localization of a finitely generated
`L`-algebra, integral over `K`). -/
@[blueprint "compat:field-tensor-finite-spec-fg"
  (statement := /-- Let $K$ and $L$ be field extensions of a field $k$ with $K/k$ finitely
    generated and $L/k$ algebraic. Then $K\otimes_kL$ has only finitely many prime ideals. -/)
  (proof := /-- Write $K=k(s)$ with $s$ finite and put $D=k[s]$, so that every element of $K$ is
    a quotient of elements of $D$. $D\otimes_kL$ is a finitely generated $L$-algebra, hence
    noetherian, and it is integral over $D$. A prime $P$ of $K\otimes_kL$ contracts to the prime
    $(0)$ of the field $K$, so its contraction to $D\otimes_kL$ lies over $(0)$ of $D$ and is a
    minimal prime of $D\otimes_kL$ (incomparability in integral extensions). The contraction is
    injective, since every element of $K\otimes_kL$ is mapped into $D\otimes_kL$ by
    multiplication with a unit $d\otimes1$, $0\neq d\in D$. A noetherian ring has only finitely
    many minimal primes. -/)
  (latexEnv := "lemma")]
theorem finite_primeSpectrum_tensorProduct_of_fg [Algebra.IsAlgebraic k L]
    (hK : (⊤ : IntermediateField k K).FG) :
    Finite (PrimeSpectrum (K ⊗[k] L)) := by
  -- `D`: a finitely generated `k`-algebra with fraction field `K`
  obtain ⟨D, hDfg, hD⟩ := exists_fg_subalgebra_forall_div hK
  have : Algebra.FiniteType k D := (Subalgebra.fg_iff_finiteType D).mp hDfg
  -- `D ⊗_k L` is noetherian (a finitely generated `L`-algebra) and integral over `D`
  have : IsNoetherianRing (L ⊗[k] D) := Algebra.FiniteType.isNoetherianRing L (L ⊗[k] D)
  have : IsNoetherianRing (D ⊗[k] L) :=
    isNoetherianRing_of_ringEquiv _ (Algebra.TensorProduct.comm k L D).toRingEquiv
  have : Algebra.IsIntegral D (D ⊗[k] L) := inferInstance
  let φ : D ⊗[k] L →ₐ[k] K ⊗[k] L := Algebra.TensorProduct.map D.val (AlgHom.id k L)
  -- every prime of `K ⊗_k L` contracts to a minimal prime of `D ⊗_k L`
  have hmin (P : PrimeSpectrum (K ⊗[k] L)) : P.asIdeal.comap φ ∈ minimalPrimes (D ⊗[k] L) := by
    have : (P.asIdeal.comap φ).IsPrime := Ideal.IsPrime.comap _
    have hbot : (P.asIdeal.comap φ).under D = ⊥ := by
      rw [eq_bot_iff]
      intro d hd
      have hP : (P.asIdeal.under K).IsPrime := Ideal.IsPrime.under K P.asIdeal
      have hd' : (d : K) ∈ P.asIdeal.under K := by
        simpa [Ideal.mem_comap, φ, Algebra.TensorProduct.algebraMap_apply] using hd
      rw [Ideal.eq_bot_of_prime (P.asIdeal.under K), Ideal.mem_bot] at hd'
      simpa [Ideal.mem_bot] using hd'
    have := Ideal.IsIntegral.mem_minimalPrimes_map_under (R := D) (P.asIdeal.comap φ)
    rwa [hbot, Ideal.map_bot] at this
  -- and the contraction is injective
  have hinj : Function.Injective fun P : PrimeSpectrum (K ⊗[k] L) =>
      (⟨P.asIdeal.comap φ, hmin P⟩ : minimalPrimes (D ⊗[k] L)) := by
    have key (P Q : PrimeSpectrum (K ⊗[k] L)) (h : P.asIdeal.comap φ = Q.asIdeal.comap φ) :
        P.asIdeal ≤ Q.asIdeal := by
      intro x hx
      obtain ⟨d, hd, y, hy⟩ := exists_mul_mem_range_tensorProduct_map_of_forall_div D hD x
      have hu : IsUnit ((d : K) ⊗ₜ[k] (1 : L)) :=
        ((isUnit_iff_ne_zero.mpr hd).map (algebraMap K (K ⊗[k] L)))
      have hyP : y ∈ P.asIdeal.comap φ := by
        rw [Ideal.mem_comap]
        change Algebra.TensorProduct.map D.val (AlgHom.id k L) y ∈ P.asIdeal
        rw [hy]
        exact P.asIdeal.mul_mem_left _ hx
      rw [h, Ideal.mem_comap] at hyP
      change Algebra.TensorProduct.map D.val (AlgHom.id k L) y ∈ Q.asIdeal at hyP
      rw [hy] at hyP
      exact (Ideal.unit_mul_mem_iff_mem Q.asIdeal hu).mp hyP
    intro P Q h
    have h' : P.asIdeal.comap φ = Q.asIdeal.comap φ := congrArg Subtype.val h
    exact PrimeSpectrum.ext (le_antisymm (key P Q h') (key Q P h'.symm))
  have : Finite (minimalPrimes (D ⊗[k] L)) :=
    (minimalPrimes.finite_of_isNoetherianRing (D ⊗[k] L)).to_subtype
  exact Finite.of_injective _ hinj

/-- If `L/k` is algebraic, the prime ideals of `K ⊗_k L` inject into the `k`-embeddings of `L`
into an algebraic closure `K̄` of `K`: a prime `p` is maximal (`K ⊗_k L` is integral over `K`), its
residue field is algebraic over `K` and so embeds into `K̄` over `K`, which gives a `K`-algebra map
`K ⊗_k L → K̄` with kernel `p`; this map is determined by its restriction to `L`. -/
theorem cardinalMk_primeSpectrum_tensorProduct_le_cardinalMk_algHom [Algebra.IsAlgebraic k L] :
    Cardinal.mk (PrimeSpectrum (K ⊗[k] L)) ≤
      Cardinal.mk (L →ₐ[k] AlgebraicClosure K) := by
  have hdim := ringKrullDimLE_zero_tensorProduct_of_isAlgebraic k K L
  have : Algebra.IsIntegral K (K ⊗[k] L) := inferInstance
  -- for each prime `P` (maximal), a `K`-embedding of the residue field into `K̄`
  let Φ : PrimeSpectrum (K ⊗[k] L) → (K ⊗[k] L →ₐ[K] AlgebraicClosure K) := fun P =>
    have : P.asIdeal.IsMaximal := P.asIdeal.isMaximal_of_isPrime
    (IsAlgClosed.lift : (K ⊗[k] L ⧸ P.asIdeal) →ₐ[K] AlgebraicClosure K).comp
      (Ideal.Quotient.mkₐ K P.asIdeal)
  have hker (P : PrimeSpectrum (K ⊗[k] L)) (x : K ⊗[k] L) : Φ P x = 0 ↔ x ∈ P.asIdeal := by
    have : P.asIdeal.IsMaximal := P.asIdeal.isMaximal_of_isPrime
    simp only [Φ, AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk]
    let := Ideal.Quotient.field P.asIdeal
    set f : (K ⊗[k] L ⧸ P.asIdeal) →ₐ[K] AlgebraicClosure K := IsAlgClosed.lift
    rw [map_eq_zero_iff f f.toRingHom.injective, Ideal.Quotient.eq_zero_iff_mem]
  let σ : PrimeSpectrum (K ⊗[k] L) → (L →ₐ[k] AlgebraicClosure K) := fun P =>
    ((Φ P).restrictScalars k).comp Algebra.TensorProduct.includeRight
  have hσ : Function.Injective σ := by
    intro P Q h
    have hΦ : Φ P = Φ Q := by
      apply Algebra.TensorProduct.ext
      · exact Subsingleton.elim _ _
      · exact h
    ext x
    rw [← hker P x, ← hker Q x, hΦ]
  exact Cardinal.mk_le_of_injective hσ

/-- `#Spec(K ⊗_k L) ≤ #Emb_k(L, k̄)` for `L/k` algebraic (`Field.Emb k L`; its cardinality is the
separable degree if that is finite and `2 ^ sepDegree` otherwise, `Field.Emb.cardinal_eq`). -/
theorem cardinalMk_primeSpectrum_tensorProduct_le_cardinalMk_emb [Algebra.IsAlgebraic k L] :
    Cardinal.mk (PrimeSpectrum (K ⊗[k] L)) ≤ Cardinal.mk (Field.Emb k L) :=
  (cardinalMk_primeSpectrum_tensorProduct_le_cardinalMk_algHom k K L).trans_eq
    (Cardinal.mk_congr (Field.embEquivOfIsAlgClosed k L (AlgebraicClosure K)).symm)

/-- The bound of p. 211 when the separable degree of `L/k` is finite. -/
theorem cardinalMk_primeSpectrum_tensorProduct_le_sepDegree_of_lt_aleph0
    [Algebra.IsAlgebraic k L] (h : Field.sepDegree k L < Cardinal.aleph0) :
    Cardinal.mk (PrimeSpectrum (K ⊗[k] L)) ≤ Field.sepDegree k L := by
  refine (cardinalMk_primeSpectrum_tensorProduct_le_cardinalMk_emb k K L).trans_eq ?_
  rw [Field.Emb.cardinal_eq]
  dsimp only
  simp [not_le.mpr h]

/-- The bound of p. 211 in the situation of Lemma 4 (`K` finitely generated over `k`): the number
of prime ideals of `K ⊗_k L` does not exceed the separable degree of `L/k`. If the separable
degree is finite this is `cardinalMk_primeSpectrum_tensorProduct_le_sepDegree_of_lt_aleph0`;
otherwise the number of primes is finite (`finite_primeSpectrum_tensorProduct_of_fg`). -/
@[blueprint "compat:field-tensor-sepdeg-fg"
  (statement := /-- Let $K$ and $L$ be field extensions of a field $k$ with $K/k$ finitely
    generated and $L/k$ algebraic. Then the number of prime ideals of $K\otimes_kL$ does not
    exceed the separable degree of $L/k$. -/)
  (proof := /-- A prime $\mathfrak p$ of $K\otimes_kL$ is maximal (the ring is integral over $K$)
    and its residue field is algebraic over $K$, so it embeds over $K$ into an algebraic closure
    $\bar K$; this gives a $K$-algebra map $K\otimes_kL\to\bar K$ with kernel $\mathfrak p$,
    determined by its restriction to $L$, a $k$-embedding $L\to\bar K$. Hence the number of
    primes is at most the number of $k$-embeddings of $L$ into $\bar K$, which is the separable
    degree of $L/k$ when the latter is finite. When the separable degree is infinite the bound
    holds because the number of primes is finite (\cref{compat:field-tensor-finite-spec-fg}). -/)
  (latexEnv := "lemma")]
theorem cardinalMk_primeSpectrum_tensorProduct_le_sepDegree_of_fg [Algebra.IsAlgebraic k L]
    (hK : (⊤ : IntermediateField k K).FG) :
    Cardinal.mk (PrimeSpectrum (K ⊗[k] L)) ≤ Field.sepDegree k L := by
  rcases lt_or_ge (Field.sepDegree k L) Cardinal.aleph0 with h | h
  · exact cardinalMk_primeSpectrum_tensorProduct_le_sepDegree_of_lt_aleph0 k K L h
  · have := finite_primeSpectrum_tensorProduct_of_fg k K L hK
    exact Cardinal.mk_lt_aleph0.le.trans h

/-! ### Regularity (p. 212)

Auxiliary results for `isRegularLocalRing_localization_tensorProduct_of_separable`. -/

section Regular

open IsLocalRing

/-- Regularity ascends along a flat map `B → C` (with `C` noetherian) at a prime `P` of `C` such
that the maximal ideal of `C_P` is generated by the contraction `q = P ∩ B`. -/
@[blueprint "compat:regular-flat-ascent"
  (statement := /-- Let $B\to C$ be a flat homomorphism of noetherian rings, $P$ a prime ideal of
    $C$ and $\mathfrak q=P\cap B$. If $B_{\mathfrak q}$ is regular and $\mathfrak qC_P$ is the
    maximal ideal of $C_P$, then $C_P$ is a regular local ring. -/)
  (proof := /-- The maximal ideal of $C_P$ is generated by the image of the maximal ideal of
    $B_{\mathfrak q}$, hence by $\dim B_{\mathfrak q}$ elements. By going down for flat
    extensions, $\dim C_P=\operatorname{ht}P=\operatorname{ht}\mathfrak q+
    \operatorname{ht}(P/\mathfrak qC)\geq\dim B_{\mathfrak q}$. -/)
  (latexEnv := "lemma")]
theorem isRegularLocalRing_localization_of_flat_of_map_eq_maximalIdeal
    {B C : Type*} [CommRing B] [CommRing C] [Algebra B C] [Module.Flat B C]
    [IsNoetherianRing B] [IsNoetherianRing C]
    (P : Ideal C) [P.IsPrime]
    (hreg : IsRegularLocalRing (Localization.AtPrime (P.under B)))
    (hP : (P.under B).map (algebraMap B (Localization.AtPrime P)) =
      maximalIdeal (Localization.AtPrime P)) :
    IsRegularLocalRing (Localization.AtPrime P) := by
  set q := P.under B
  have hqP : P.LiesOver q := ⟨rfl⟩
  apply IsRegularLocalRing.of_spanFinrank_maximalIdeal_le
  -- the maximal ideal of `C_P` is the image of that of `B_q`
  let f : Localization.AtPrime q →+* Localization.AtPrime P :=
    Localization.localRingHom q P (algebraMap B C) rfl
  have hmap : (maximalIdeal (Localization.AtPrime q)).map f =
      maximalIdeal (Localization.AtPrime P) := by
    rw [← hP, ← Localization.AtPrime.map_eq_maximalIdeal, Ideal.map_map]
    congr 1
    ext b
    simp [f, Localization.localRingHom_to_map, IsScalarTower.algebraMap_apply B C
      (Localization.AtPrime P)]
  have hfg : (maximalIdeal (Localization.AtPrime q)).FG :=
    (maximalIdeal (Localization.AtPrime q)).fg_of_isNoetherianRing
  have h1 : ((maximalIdeal (Localization.AtPrime P)).spanFinrank : WithBot ℕ∞) ≤
      ringKrullDim (Localization.AtPrime q) := by
    rw [← hreg.spanFinrank_maximalIdeal, ← hmap]
    exact_mod_cast Ideal.spanFinrank_map_le_of_fg f hfg
  -- `dim B_q = ht q ≤ ht P = dim C_P` by going down
  have h2 : ringKrullDim (Localization.AtPrime q) ≤ ringKrullDim (Localization.AtPrime P) := by
    rw [IsLocalization.AtPrime.ringKrullDim_eq_height q,
      IsLocalization.AtPrime.ringKrullDim_eq_height P,
      Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown q P]
    exact_mod_cast le_self_add
  exact h1.trans h2

/-- A flat, formally unramified algebra `C` essentially of finite type over a regular ring `B` is
regular, provided `C` is noetherian: at a prime `P` over `q`, unramifiedness gives
`m_{C_P} = q C_P` (`Algebra.isUnramifiedAt_iff_map_eq`). -/
theorem isRegularRing_of_flat_of_formallyUnramified
    {B C : Type*} [CommRing B] [CommRing C] [Algebra B C] [Module.Flat B C]
    [Algebra.FormallyUnramified B C] [Algebra.EssFiniteType B C]
    [IsRegularRing B] [IsNoetherianRing C] : IsRegularRing C := by
  rw [isRegularRing_iff]
  intro P hP
  set q := P.under B
  have : P.LiesOver q := ⟨rfl⟩
  let : Algebra (Localization.AtPrime q) (Localization.AtPrime P) :=
    (Localization.localRingHom q P (algebraMap B C) rfl).toAlgebra
  have : IsScalarTower B (Localization.AtPrime q) (Localization.AtPrime P) :=
    IsScalarTower.of_algebraMap_eq fun b => by
      simp [RingHom.algebraMap_toAlgebra, Localization.localRingHom_to_map,
        IsScalarTower.algebraMap_apply B C (Localization.AtPrime P)]
  have hun : Algebra.IsUnramifiedAt B P := inferInstance
  have hP := ((Algebra.isUnramifiedAt_iff_map_eq B q P).mp hun).2
  exact isRegularLocalRing_localization_of_flat_of_map_eq_maximalIdeal P inferInstance hP

/-- (3) ⇒ (2) of Stacks 030W: if `M ⊗_k k'` is reduced for every purely inseparable `k'/k`
(`k` of characteristic `p`), then the `p`-th powers of `k`-linearly independent elements of `M`
are `k`-linearly independent. (If `∑ cᵢ xᵢ^p = 0`, then `z = ∑ xᵢ ⊗ cᵢ^{1/p}` satisfies `z^p = 0`
in `M ⊗_k k^{1/p}`, so `z = 0` and all `cᵢ = 0`.) -/
theorem linearIndepOn_pow_of_forall_isReduced_tensorProduct {k M : Type u} [Field k] [Field M]
    [Algebra k M] (p : ℕ) [hp : Fact p.Prime] [CharP k p]
    (hM : ∀ (k' : Type u) [Field k'] [Algebra k k'], IsPurelyInseparable k k' →
      IsReduced (M ⊗[k] k'))
    (s : Finset M) (hs : LinearIndepOn k id (s : Set M)) :
    LinearIndepOn k (· ^ p) (s : Set M) := by
  -- a purely inseparable extension `k'` of `k` in which every element of `k` is a `p`-th power
  let Ω := AlgebraicClosure k
  have : CharP Ω p := charP_of_injective_algebraMap (algebraMap k Ω).injective p
  let k' := perfectClosure k Ω
  have : PerfectRing k' p := inferInstance
  have hred : IsReduced (k' ⊗[k] M) :=
    have := hM k' inferInstance
    isReduced_of_injective (Algebra.TensorProduct.comm k k' M).toAlgHom
      (Algebra.TensorProduct.comm k k' M).injective
  have : CharP (k' ⊗[k] M) p :=
    charP_of_injective_algebraMap (algebraMap k (k' ⊗[k] M)).injective p
  -- the `k'`-basis of `k' ⊗_k M` extending `1 ⊗ s`
  let b := Module.Basis.extend hs
  let b' := Algebra.TensorProduct.basis k' b
  have hli : LinearIndependent k' (fun x : (s : Set M) => (1 : k') ⊗ₜ[k] (x : M)) := by
    have := b'.linearIndependent.comp (fun x : (s : Set M) =>
      (⟨x, hs.subset_extend _ x.2⟩ : hs.extend (Set.subset_univ _)))
      (fun x y h => Subtype.ext (by simpa using congrArg Subtype.val h))
    convert this using 1
    ext x
    simp [b', b, Algebra.TensorProduct.basis_apply]
  rw [LinearIndepOn, Fintype.linearIndependent_iff]
  intro g hg x
  let r : ↥(s : Set M) → k' := fun y => (frobeniusEquiv k' p).symm (algebraMap k k' (g y))
  have hr (y) : r y ^ p = algebraMap k k' (g y) := by
    simp [r]
  let z : k' ⊗[k] M := ∑ y, r y ⊗ₜ[k] (y : M)
  have hg' : ∑ y : (s : Set M), g y • ((y : M) ^ p) = 0 := by simpa using hg
  have hz : z ^ p = 0 := by
    have hy : ∀ y : (s : Set M),
        (r y ⊗ₜ[k] (y : M)) ^ p = (1 : k') ⊗ₜ[k] (g y • (y : M) ^ p) := by
      intro y
      rw [Algebra.TensorProduct.tmul_pow, hr, Algebra.algebraMap_eq_smul_one,
        TensorProduct.smul_tmul]
    show (∑ y, r y ⊗ₜ[k] (y : M)) ^ p = 0
    have : ExpChar (k' ⊗[k] M) p := ExpChar.prime hp.out
    have hsum :=
      sum_pow_char p (Finset.univ : Finset ↥(s : Set M)) (fun y => r y ⊗ₜ[k] (y : M))
    rw [hsum]
    simp only [hy, ← TensorProduct.tmul_sum, hg', TensorProduct.tmul_zero]
  have hz0 : z = 0 := IsReduced.eq_zero z ⟨p, hz⟩
  have := Fintype.linearIndependent_iff.mp hli r (by
    simpa [z, TensorProduct.smul_tmul', smul_eq_mul] using hz0) x
  have : algebraMap k k' (g x) = 0 := by rw [← hr, this, zero_pow hp.out.ne_zero]
  simpa using this

/-- Mac Lane: a finitely generated extension `E/k` such that `E ⊗_k k'` is reduced for every
purely inseparable `k'/k` is separably generated. -/
theorem exists_isTranscendenceBasis_isSeparable_of_forall_isReduced {k E : Type u} [Field k]
    [Field E] [Algebra k E] [Algebra.EssFiniteType k E]
    (hE : ∀ (k' : Type u) [Field k'] [Algebra k k'], IsPurelyInseparable k k' →
      IsReduced (E ⊗[k] k')) :
    ∃ s : Finset E, IsTranscendenceBasis k ((↑) : s → E) ∧
      Algebra.IsSeparable (IntermediateField.adjoin k (s : Set E)) E := by
  obtain _ | ⟨p, hp, hpk⟩ := CharP.exists' k
  · exact exists_isTranscendenceBasis_and_isSeparable_of_perfectField k E
  · have : ExpChar k p := .prime hp.out
    exact exists_isTranscendenceBasis_and_isSeparable_of_linearIndepOn_pow_of_essFiniteType p
      hp.out (fun s hs => linearIndepOn_pow_of_forall_isReduced_tensorProduct p hE s hs)

open scoped IntermediateField.algebraAdjoinAdjoin in
/-- If `E/k` is finitely generated with a separating transcendence basis `s` and `K/k` is
finitely generated, then `K ⊗_k E` is a regular ring: it is obtained from the polynomial ring
`K[s]` by the flat, unramified, essentially finite base change `k[s] → E`. -/
theorem isRegularRing_tensorProduct_of_isTranscendenceBasis {k K E : Type u} [Field k] [Field K]
    [Field E] [Algebra k K] [Algebra k E] [Algebra.EssFiniteType k E]
    (hK : (⊤ : IntermediateField k K).FG) (s : Finset E)
    (hs : IsTranscendenceBasis k ((↑) : s → E))
    [Algebra.IsSeparable (IntermediateField.adjoin k (s : Set E)) E] :
    IsRegularRing (K ⊗[k] E) := by
  let R₀ := Algebra.adjoin k (s : Set E)
  let L₀ := IntermediateField.adjoin k (s : Set E)
  -- `R₀ ≅ k[s]`, so `R₀ ⊗_k K ≅ K[s]` is regular
  have hrange : Set.range ((↑) : s → E) = (s : Set E) := by ext; simp
  let e₀ : MvPolynomial s k ≃ₐ[k] R₀ :=
    hs.1.aevalEquiv.trans (Subalgebra.equivOfEq _ _ (by rw [hrange]))
  let eB : R₀ ⊗[k] K ≃+* MvPolynomial s K :=
    ((Algebra.TensorProduct.congr e₀.symm AlgEquiv.refl).trans
      (Algebra.TensorProduct.comm k _ K)).toRingEquiv.trans
      (MvPolynomial.algebraTensorAlgEquiv k K).toRingEquiv
  have : IsRegularRing (R₀ ⊗[k] K) := IsRegularRing.of_ringEquiv eB.symm
  -- `R₀ → E` is flat, formally unramified and essentially of finite type
  have : Module.Flat R₀ L₀ := IsLocalization.flat L₀ (nonZeroDivisors R₀)
  have : Module.Flat R₀ E := Module.Flat.trans R₀ L₀ E
  have : Algebra.FormallyUnramified R₀ L₀ :=
    .of_isLocalization (nonZeroDivisors R₀)
  have : Algebra.FormallyUnramified L₀ E := .of_isSeparable L₀ E
  have : Algebra.FormallyUnramified R₀ E := .comp R₀ L₀ E
  have : Algebra.EssFiniteType R₀ L₀ := .of_isLocalization L₀ (nonZeroDivisors R₀)
  have : Algebra.EssFiniteType L₀ E := .of_comp k L₀ E
  have : Algebra.EssFiniteType R₀ E := .comp R₀ L₀ E
  -- `(R₀ ⊗_k K) ⊗_{R₀} E ≅ K ⊗_k E`
  let eC : (R₀ ⊗[k] K) ⊗[R₀] E ≃+* K ⊗[k] E :=
    ((Algebra.TensorProduct.comm R₀ (R₀ ⊗[k] K) E).trans
      (Algebra.TensorProduct.cancelBaseChange k R₀ R₀ E K)).toRingEquiv.trans
      (Algebra.TensorProduct.comm k E K).toRingEquiv
  have : IsNoetherianRing (K ⊗[k] E) := isNoetherianRing_tensorProduct_of_fg k K E hK
  have : IsNoetherianRing ((R₀ ⊗[k] K) ⊗[R₀] E) := isNoetherianRing_of_ringEquiv _ eC.symm
  have : IsRegularRing ((R₀ ⊗[k] K) ⊗[R₀] E) :=
    isRegularRing_of_flat_of_formallyUnramified (B := R₀ ⊗[k] K)
  exact IsRegularRing.of_ringEquiv (R := (R₀ ⊗[k] K) ⊗[R₀] E) eC

end Regular

/-- `K ⊗_k E ⊆ K ⊗_k E'` inside `K ⊗_k L` for intermediate fields `E ≤ E'` of `L/k`. -/
theorem range_tensorProduct_map_val_mono {E E' : IntermediateField k L} (h : E ≤ E') :
    (Algebra.TensorProduct.map (AlgHom.id k K) E.val).range ≤
      (Algebra.TensorProduct.map (AlgHom.id k K) E'.val).range := by
  have : Algebra.TensorProduct.map (AlgHom.id k K) E.val =
      (Algebra.TensorProduct.map (AlgHom.id k K) E'.val).comp
        (Algebra.TensorProduct.map (AlgHom.id k K) (IntermediateField.inclusion h)) := by
    ext <;> simp
  rw [this]
  exact AlgHom.range_comp_le_range _ _

variable {k K L} in
/-- Every element of `K ⊗_k L` comes from `K ⊗_k k(t)` for a finite subset `t` of `L`. -/
theorem exists_finset_mem_range_tensorProduct_map_adjoin (x : K ⊗[k] L) :
    ∃ t : Finset L, x ∈ (Algebra.TensorProduct.map (AlgHom.id k K)
      (IntermediateField.adjoin k (t : Set L)).val).range := by
  classical
  induction x with
  | tmul a l =>
    refine ⟨{l}, a ⊗ₜ ⟨l, IntermediateField.subset_adjoin k _ (by simp)⟩, by simp⟩
  | add x y hx hy =>
    obtain ⟨t₁, h₁⟩ := hx
    obtain ⟨t₂, h₂⟩ := hy
    refine ⟨t₁ ∪ t₂, add_mem ?_ ?_⟩
    · exact range_tensorProduct_map_val_mono k K L
        (IntermediateField.adjoin.mono k _ _ (by simp)) h₁
    · exact range_tensorProduct_map_val_mono k K L
        (IntermediateField.adjoin.mono k _ _ (by simp)) h₂

/-- p. 212: if `L` is separable over `k` in the sense of p. 212 (for every purely inseparable
extension `k'` of `k`, `L ⊗_k k'` has no nilpotent elements) and `K/k` is finitely generated,
then every localization of `K ⊗_k L` at a prime ideal is a regular local ring. -/
@[blueprint "compat:field-tensor-regular"
  (statement := /-- Let $K$ and $L$ be field extensions of a field $k$ with $K/k$ finitely
    generated and $L$ separable over $k$ in the sense of p.~212: for every purely inseparable
    extension $k'$ of $k$, $L\otimes_kk'$ has no nilpotent elements. Then the localization of
    $K\otimes_kL$ at every prime ideal is a regular local ring. -/)
  (proof := /-- (Asserted on p.~212.) $K\otimes_kL$ is noetherian: it is a localization of
    $D\otimes_kL$, $D$ a finitely generated $k$-algebra with field of fractions $K$. Let
    $\mathfrak p$ be a prime of $K\otimes_kL$; its finitely many generators lie in $K\otimes_kE$
    for a finitely generated subextension $E$ of $L/k$, and $E$ is again separable over $k$
    ($E\otimes_kk'\subseteq L\otimes_kk'$). By Mac Lane's criterion $E/k$ is separably
    generated: there is a transcendence basis $s$ with $E/k(s)$ finite separable (in
    characteristic $p$, reducedness of $E\otimes_kk^{1/p}$ shows that $p$-th powers of
    $k$-linearly independent elements are linearly independent, and Mathlib's \texttt{exists\_%
    isTranscendenceBasis\_and\_isSeparable\_of\_linearIndepOn\_pow\_of\_essFiniteType}
    applies). Then $k[s]\to E$ is flat, unramified and essentially of finite type, so
    $K\otimes_kE\cong K[s]\otimes_{k[s]}E$ is flat and unramified over the regular ring $K[s]$,
    and is regular by \cref{compat:regular-flat-ascent} (unramifiedness gives
    $\mathfrak m_P=\mathfrak q(K\otimes_kE)_P$). Finally $K\otimes_kL$ is flat over
    $K\otimes_kE$ and $\mathfrak p$ is generated by its contraction $\mathfrak q$, so
    $(K\otimes_kL)_{\mathfrak p}$ is regular by \cref{compat:regular-flat-ascent}. -/)
  (latexEnv := "lemma")]
theorem isRegularLocalRing_localization_tensorProduct_of_separable
    (hL : ∀ (k' : Type u) [Field k'] [Algebra k k'], IsPurelyInseparable k k' →
      IsReduced (L ⊗[k] k'))
    (hK : (⊤ : IntermediateField k K).FG) (p : Ideal (K ⊗[k] L)) [p.IsPrime] :
    IsRegularLocalRing (Localization.AtPrime p) := by
  classical
  have : IsNoetherianRing (K ⊗[k] L) := isNoetherianRing_tensorProduct_of_fg k K L hK
  -- generators of `p` come from `K ⊗_k E` for a finitely generated subextension `E` of `L`
  obtain ⟨g, hg⟩ : p.FG := IsNoetherian.noetherian p
  choose t ht using exists_finset_mem_range_tensorProduct_map_adjoin (k := k) (K := K) (L := L)
  let E := IntermediateField.adjoin k ((g.biUnion t : Finset L) : Set L)
  let ι : K ⊗[k] E →ₐ[k] K ⊗[k] L := Algebra.TensorProduct.map (AlgHom.id k K) E.val
  have hgι : ∀ c ∈ g, c ∈ ι.range := fun c hc =>
    range_tensorProduct_map_val_mono k K L
      (IntermediateField.adjoin.mono k _ _ (by
        intro x hx
        simp only [Finset.coe_biUnion, Set.mem_iUnion]
        exact ⟨c, hc, hx⟩)) (ht c)
  -- `E` is finitely generated and separable over `k`, hence `K ⊗_k E` is regular
  have : Algebra.EssFiniteType k E :=
    IntermediateField.essFiniteType_iff.mpr ⟨g.biUnion t, rfl⟩
  have hE : ∀ (k' : Type u) [Field k'] [Algebra k k'], IsPurelyInseparable k k' →
      IsReduced (E ⊗[k] k') := fun k' _ _ h =>
    have := hL k' h
    isReduced_of_injective (Algebra.TensorProduct.map E.val (AlgHom.id k k'))
      (Module.Flat.rTensor_preserves_injective_linearMap (M := k') E.val.toLinearMap
        E.val.injective)
  obtain ⟨s, hs, hsep⟩ := exists_isTranscendenceBasis_isSeparable_of_forall_isReduced hE
  have : IsRegularRing (K ⊗[k] E) := isRegularRing_tensorProduct_of_isTranscendenceBasis hK s hs
  -- `K ⊗_k E → K ⊗_k L` is flat and `p` is generated by its contraction
  let : Algebra (K ⊗[k] E) (K ⊗[k] L) := ι.toRingHom.toAlgebra
  have : Module.Flat (K ⊗[k] E) (K ⊗[k] L) :=
    RingHom.Flat.tensorProductMap (RingHom.Flat.id _)
      (RingHom.Flat.of_isField (Field.toIsField E) _)
  have hp : (p.comap ι.toRingHom).map ι.toRingHom = p := by
    refine le_antisymm Ideal.map_comap_le ?_
    have hle : Ideal.span (g : Set (K ⊗[k] L)) ≤ (p.comap ι.toRingHom).map ι.toRingHom := by
      rw [Ideal.span_le]
      intro c hc
      obtain ⟨y, hy⟩ := hgι c hc
      have hcp : c ∈ p := hg ▸ Ideal.subset_span hc
      rw [← hy]
      refine Ideal.mem_map_of_mem _ ?_
      rw [Ideal.mem_comap]
      change ι y ∈ p
      rwa [show ι y = c from hy]
    rwa [hg] at hle
  refine isRegularLocalRing_localization_of_flat_of_map_eq_maximalIdeal (B := K ⊗[k] E) p
    inferInstance ?_
  rw [IsScalarTower.algebraMap_eq (K ⊗[k] E) (K ⊗[k] L) (Localization.AtPrime p),
    ← Ideal.map_map]
  change ((p.comap ι.toRingHom).map ι.toRingHom).map _ = _
  rw [hp, Localization.AtPrime.map_eq_maximalIdeal]

end FieldTensor

end Hironaka
