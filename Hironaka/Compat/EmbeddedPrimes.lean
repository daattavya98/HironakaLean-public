/-
Copyright (c) 2026 Daattavya Aggarwal, Minhyong Kim, Oisin Kim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daattavya Aggarwal, Minhyong Kim, Oisin Kim
-/
module

public import Architect
public import Hironaka.Ch3.Transforms
public import Mathlib.RingTheory.NoetherNormalization
public import Mathlib.RingTheory.Flat.Localization
public import Mathlib.RingTheory.TensorProduct.Free
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.Ideal.GoingUp

/-!
# The associated primes of `m̄'k̃[X]` are isolated (Ch. III §2, p. 211)

Hironaka, p. 211: "We note here that all the associated prime ideals of `m̄'k̃[X₂,…,X_r]` are isolated
because `m̄'` is a prime ideal in `k[X₂,…,X_r]`."  The paper gives no argument, and the claim is for an
arbitrary field extension `k → k̃`.

Proof (gap filled): by Noether normalization `k[T] ⊆ D = k[X]/m̄'`, `D` is integral over the polynomial ring
`k[T]`.  The non-zero elements of `k̃[T] = k[T] ⊗_k k̃` are non-zero-divisors on `K ⊗_k k̃`, `K = Frac D`
(`K ⊗_k k̃ = K ⊗_{k[T]} (k[T] ⊗_k k̃)`, `K` is flat over `k[T]`, and `k[T] ⊗_k k̃ ≅ k̃[T]` is a
domain), hence on the subring `D ⊗_k k̃ ≅ k̃[X]/m̄'k̃[X]` (`Ψ(k̃[X]) ⊆ K ⊗_k k̃`, see
`exists_ringHom_tensor_fractionRing`), so an associated prime meets `k̃[T]` in `(0)`; and `k̃[X]/m̄'k̃[X]`
is integral over `k̃[T]`, so by incomparability the associated prime is minimal.  This works in every
characteristic.
-/

@[expose] public section

open scoped TensorProduct

namespace Hironaka

universe u

/-- A field `K` containing the domain `P` is flat over `P`: `K` is a vector space over the field of
fractions `F` of `P` (hence free), and `F` is flat over `P`. -/
theorem flat_of_faithfulSMul_field (P K : Type*) [CommRing P] [IsDomain P] [Field K]
    [Algebra P K] [FaithfulSMul P K] : Module.Flat P K := by
  let _ : Algebra (FractionRing P) K := FractionRing.liftAlgebra P K
  have _ : IsScalarTower P (FractionRing P) K := FractionRing.isScalarTower_liftAlgebra P K
  have _ : Module.Flat P (FractionRing P) :=
    IsLocalization.flat (FractionRing P) (nonZeroDivisors P)
  exact Module.Flat.trans P (FractionRing P) K

section TensorNonZeroDivisor

variable {k k' P K : Type*} [Field k] [Field k'] [Field K] [CommRing P] [Algebra k P]
  [Algebra k K] [Algebra k k']

/-- If `P ⊆ K` (a domain in a field, over `k`), `P ⊗_k k'` is a domain, and `τ ≠ 0` lies in `P ⊗_k k'`,
then the image of `τ` in `K ⊗_k k'` is a non-zero-divisor.  Indeed `K ⊗_k k' = K ⊗_P (P ⊗_k k')`,
`K` is flat over `P` (a vector space over the field of fractions of `P`), and `τ` acts injectively on the
domain `P ⊗_k k'`. -/
theorem eq_zero_of_map_mul_eq_zero (gK : P →ₐ[k] K) (hinj : Function.Injective gK)
    [IsDomain (P ⊗[k] k')] {τ : P ⊗[k] k'} (hτ : τ ≠ 0) {x : K ⊗[k] k'}
    (h : Algebra.TensorProduct.map gK (AlgHom.id k k') τ * x = 0) : x = 0 := by
  have hPdom : IsDomain P := Function.Injective.isDomain gK.toRingHom hinj
  let _ : Algebra P K := gK.toRingHom.toAlgebra
  have _ : IsScalarTower k P K :=
    IsScalarTower.of_algebraMap_eq fun x => (gK.commutes x).symm
  have _ : FaithfulSMul P K := (faithfulSMul_iff_algebraMap_injective P K).mpr hinj
  have _ : Module.Flat P K := flat_of_faithfulSMul_field P K
  let e : K ⊗[P] (P ⊗[k] k') ≃ₐ[K] K ⊗[k] k' := Algebra.TensorProduct.cancelBaseChange k P K K k'
  have he : ∀ τ : P ⊗[k] k', e (1 ⊗ₜ τ) = Algebra.TensorProduct.map gK (AlgHom.id k k') τ := by
    intro τ
    induction τ using TensorProduct.inductionOn with
    | tmul p μ => simp [e, Algebra.TensorProduct.cancelBaseChange_tmul, Algebra.smul_def]; rfl
    | add a b ha hb => rw [TensorProduct.tmul_add, map_add, ha, hb, map_add]
  have h1 : Algebra.TensorProduct.map gK (AlgHom.id k k') τ * e (e.symm x) = 0 := by
    rw [e.apply_symm_apply]; exact h
  have h2 : (1 ⊗ₜ τ : K ⊗[P] (P ⊗[k] k')) * e.symm x = 0 := by
    apply e.injective
    rw [map_mul, he, map_zero]
    exact h1
  have h3 : ∀ z : K ⊗[P] (P ⊗[k] k'),
      (1 ⊗ₜ τ : K ⊗[P] (P ⊗[k] k')) * z = LinearMap.lTensor K (LinearMap.mulLeft P τ) z := by
    intro z
    induction z using TensorProduct.inductionOn with
    | tmul a q => simp [Algebra.TensorProduct.tmul_mul_tmul]
    | add a b ha hb => rw [mul_add, map_add, ha, hb]
  have hinj' : Function.Injective (LinearMap.lTensor K (LinearMap.mulLeft P τ)) :=
    Module.Flat.lTensor_preserves_injective_linearMap _ fun a b hab =>
      mul_left_cancel₀ hτ hab
  have h4 : e.symm x = 0 := hinj' (by rw [← h3, h2, map_zero])
  rw [← e.apply_symm_apply x, h4, map_zero]

end TensorNonZeroDivisor

section Abstract

variable {B E Q : Type*} [CommRing B] [CommRing E] [CommRing Q] [IsNoetherianRing B]

/-- Abstract form of the isolatedness of the associated primes of the kernel of `Ψ : B → E`: if
`ε : Q → E` has image in `Ψ(B)`, non-zero elements of `Q` go to non-zero-divisors of `E`, and `Ψ(B)`
is integral over the image of `Q`, then every associated prime of `B/ker Ψ` is a minimal prime. -/
theorem mem_minimalPrimes_ker_of_mem_associatedPrimes (Ψ : B →+* E) (ε : Q →+* E)
    (hε : ∀ t, ε t ∈ Ψ.range) (hnzd : ∀ t, t ≠ 0 → ∀ x : E, ε t * x = 0 → x = 0)
    (hint : ∀ r : Ψ.range, (ε.codRestrict Ψ.range hε).IsIntegralElem r) [Nontrivial E]
    {q : Ideal B} (hq : q ∈ associatedPrimes B (B ⧸ RingHom.ker Ψ)) :
    q ∈ (RingHom.ker Ψ).minimalPrimes := by
  classical
  obtain ⟨hqp, x, hx⟩ := isAssociatedPrime_iff.mp hq
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective x
  have hIq : RingHom.ker Ψ ≤ q := le_of_mem_associatedPrimes_quotient hq
  -- `ε t` is not in `Ψ(q)` for `t ≠ 0`
  have hA : ∀ c ∈ q, ∀ t, ε t = Ψ c → t = 0 := by
    intro c hc t htc
    by_contra ht
    have hcb : c * b ∈ RingHom.ker Ψ := by
      have : c ∈ (⊥ : Submodule B (B ⧸ RingHom.ker Ψ)).colon {Ideal.Quotient.mk (RingHom.ker Ψ) b} :=
        hx ▸ hc
      rw [Submodule.mem_colon_singleton, Submodule.mem_bot, smul_quotient_mk,
        Ideal.Quotient.eq_zero_iff_mem] at this
      exact this
    have h0 : ε t * Ψ b = 0 := by
      rw [htc, ← map_mul]; exact hcb
    have hb : b ∈ RingHom.ker Ψ := hnzd t ht _ h0
    have : (⊥ : Submodule B (B ⧸ RingHom.ker Ψ)).colon {Ideal.Quotient.mk (RingHom.ker Ψ) b} = ⊤ := by
      rw [eq_top_iff]
      intro r _
      rw [Submodule.mem_colon_singleton, Submodule.mem_bot, smul_quotient_mk,
        Ideal.Quotient.eq_zero_iff_mem]
      exact Ideal.mul_mem_left _ _ hb
    exact hqp.ne_top (hx.trans this)
  -- pass to `R = Ψ(B)`
  set Ψ' : B →+* Ψ.range := Ψ.rangeRestrict with hΨ'
  have hΨ's : Function.Surjective Ψ' := Ψ.rangeRestrict_surjective
  have hkerΨ' : RingHom.ker Ψ' = RingHom.ker Ψ := Ψ.ker_rangeRestrict
  set ν : Q →+* Ψ.range := ε.codRestrict Ψ.range hε with hν
  let _ : Algebra Q Ψ.range := ν.toAlgebra
  have _ : Algebra.IsIntegral Q Ψ.range := ⟨fun r => hint r⟩
  have hmap : ∀ J : Ideal B, RingHom.ker Ψ ≤ J → (J.map Ψ').comap Ψ' = J := fun J hJ => by
    rw [Ideal.comap_map_of_surjective _ hΨ's, ← RingHom.ker_eq_comap_bot, hkerΨ',
      sup_eq_left.mpr hJ]
  refine ⟨⟨hqp, hIq⟩, fun q' ⟨hq'p, hIq'⟩ hq'q => ?_⟩
  by_contra hne
  have hlt : q' < q := lt_of_le_of_ne hq'q (fun h => hne (h ▸ le_rfl))
  have hqE : (q.map Ψ').IsPrime := Ideal.map_isPrime_of_surjective hΨ's (hkerΨ'.symm ▸ hIq)
  have hq'E : (q'.map Ψ').IsPrime := Ideal.map_isPrime_of_surjective hΨ's (hkerΨ'.symm ▸ hIq')
  have hltE : q'.map Ψ' < q.map Ψ' := by
    refine lt_of_le_of_ne (Ideal.map_mono hq'q) fun h => ?_
    have := congrArg (Ideal.comap Ψ') h
    rw [hmap q' hIq', hmap q hIq] at this
    exact hlt.ne this
  have := Ideal.IsIntegral.under_lt_under (R := Q) hltE
  have hbot : (q.map Ψ').under Q = ⊥ := by
    ext t
    simp only [Ideal.mem_under, Ideal.mem_bot]
    constructor
    · intro ht
      obtain ⟨c, hc, hct⟩ := (Ideal.mem_map_iff_of_surjective Ψ' hΨ's).mp ht
      refine hA c hc t ?_
      exact (congrArg Subtype.val hct).symm
    · rintro rfl
      rw [map_zero]
      exact zero_mem _
  rw [hbot] at this
  exact (not_lt_bot) this

end Abstract

section EmbeddedPrimes

theorem isDomain_tensor_mvPolynomial (k k' : Type u) [Field k] [Field k'] [Algebra k k'] (s : ℕ) :
    IsDomain (MvPolynomial (Fin s) k ⊗[k] k') := by
  let e : MvPolynomial (Fin s) k ⊗[k] k' ≃+* MvPolynomial (Fin s) k' :=
    (Algebra.TensorProduct.comm k (MvPolynomial (Fin s) k) k').toRingEquiv.trans
      (MvPolynomial.algebraTensorAlgEquiv k k').toRingEquiv
  exact Function.Injective.isDomain e.toRingHom e.injective

-- The proof is long (the instance setup for `K ⊗_k k̃` over `k[T] ⊗_k k̃` and the integrality of
-- `Ψ(k̃[X])` over `k̃[T]`); it needs more than the default 200000 heartbeats.
set_option maxHeartbeats 400000 in
/-- p. 211, "all the associated prime ideals of `m̄'k̃[X₂, …, X_r]` are isolated because `m̄'` is a
prime ideal in `k[X₂, …, X_r]`", for every field extension `κ : k → k̃`.  Proof: Noether
normalization `k[T] ⊆ D = k[X]/m̄'`; the non-zero elements of `k̃[T] = k[T] ⊗_k k̃` are non-zero-divisors
in `K ⊗_k k̃ ⊇ D ⊗_k k̃ = k̃[X]/m̄'k̃[X]` (`eq_zero_of_map_mul_eq_zero`), so an associated prime meets
`k̃[T]` in `(0)`, and `k̃[X]/m̄'k̃[X]` is integral over `k̃[T]`, whence minimal (incomparability). -/
@[blueprint "lem:III.4-isolated"
  (statement := /-- Let $k\to\bar k$ be a field extension and $\bar m'$ a prime ideal of
    $k[X_2,\dots,X_r]$. Then all the associated prime ideals of $\bar m'\bar k[X_2,\dots,X_r]$ are
    isolated (minimal over $\bar m'\bar k[X_2,\dots,X_r]$). (p.~211: ``We note here that all the
    associated prime ideals of $\bar m'\tilde k[X_2,\dots,X_r]$ are isolated because $\bar m'$ is a
    prime ideal in $k[X_2,\dots,X_r]$.'') -/)
  (proof := /-- \textbf{Not proved in the paper.} Let $D=k[X]/\bar m'$, a domain of finite type over
    $k$. By Noether normalization there is a polynomial ring $k[T]\subseteq D$ with $D$ integral
    (even finite) over $k[T]$. Let $K=\operatorname{Frac}D$, so $\bar k[X]/\bar m'\bar k[X]\subseteq
    K\otimes_k\bar k=K\otimes_{k[T]}(k[T]\otimes_k\bar k)$ and $k[T]\otimes_k\bar k\cong\bar k[T]$ is a
    domain. $K$ is flat over $k[T]$ (a vector space over $\operatorname{Frac}k[T]$), so a non-zero
    element of $\bar k[T]$ acts injectively on $K\otimes_k\bar k$, hence on
    $\bar k[X]/\bar m'\bar k[X]$: it lies in no associated prime. So an associated prime $\mathfrak q$
    has $\mathfrak q\cap\bar k[T]=(0)$. Now $\bar k[X]/\bar m'\bar k[X]$ is integral over $\bar k[T]$;
    by incomparability a prime $\mathfrak q'\subseteq\mathfrak q$ with $\mathfrak q'\supseteq\bar m'\bar k[X]$
    also meets $\bar k[T]$ in $(0)$, so $\mathfrak q'=\mathfrak q$. (This works in every
    characteristic.) (p.~211.) -/)
  (latexEnv := "lemma")]
theorem mem_minimalPrimes_of_mem_associatedPrimes {k k' : Type u} [Field k] [Field k']
    (κ : k →+* k') {σ : Type} [Finite σ] (m : Ideal (MvPolynomial σ k)) [m.IsPrime]
    {q : Ideal (MvPolynomial σ k')}
    (hq : q ∈ associatedPrimes (MvPolynomial σ k')
      (MvPolynomial σ k' ⧸ m.map (MvPolynomial.map κ))) :
    q ∈ (m.map (MvPolynomial.map κ)).minimalPrimes := by
  classical
  let _ : Algebra k k' := κ.toAlgebra
  have hD : IsDomain (MvPolynomial σ k ⧸ m) := Ideal.Quotient.isDomain m
  obtain ⟨Ψ, hΨ1, hΨ2, hker⟩ := exists_ringHom_tensor_fractionRing κ m
  rw [← hker] at hq ⊢
  -- Noether normalization of `D = k[X]/m̄'` over `k`
  have : Algebra.FiniteType k (MvPolynomial σ k ⧸ m) :=
    Algebra.FiniteType.of_surjective (A := MvPolynomial σ k)
      (Ideal.Quotient.mkₐ k m) Ideal.Quotient.mk_surjective
  have : Nontrivial (MvPolynomial σ k ⧸ m) :=
    Ideal.Quotient.nontrivial_iff.mpr (Ideal.IsPrime.ne_top ‹_›)
  obtain ⟨s, g, hginj, hgint⟩ := exists_integral_inj_algHom_of_fg k (MvPolynomial σ k ⧸ m)
  let gK : MvPolynomial (Fin s) k →ₐ[k] FractionRing (MvPolynomial σ k ⧸ m) :=
    (IsScalarTower.toAlgHom k (MvPolynomial σ k ⧸ m) (FractionRing (MvPolynomial σ k ⧸ m))).comp g
  have hgK : Function.Injective gK :=
    (IsFractionRing.injective (MvPolynomial σ k ⧸ m)
      (FractionRing (MvPolynomial σ k ⧸ m))).comp hginj
  have hdom : IsDomain (MvPolynomial (Fin s) k ⊗[k] k') := isDomain_tensor_mvPolynomial k k' s
  set ε : MvPolynomial (Fin s) k ⊗[k] k' →+*
      FractionRing (MvPolynomial σ k ⧸ m) ⊗[k] k' :=
    (Algebra.TensorProduct.map gK (AlgHom.id k k')).toRingHom with hεdef
  -- the image of `ε` lies in `Ψ(B)`
  have hε : ∀ t, ε t ∈ Ψ.range := by
    intro t
    induction t using TensorProduct.inductionOn with
    | tmul p μ =>
      obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (g p)
      refine ⟨MvPolynomial.C μ * MvPolynomial.map κ a, ?_⟩
      rw [map_mul, hΨ2, hΨ1, ha]
      simp [hεdef, gK, Algebra.TensorProduct.tmul_mul_tmul]
    | add a b ha hb =>
      rw [map_add]
      exact add_mem ha hb
  have hnzd : ∀ t, t ≠ 0 → ∀ x : FractionRing (MvPolynomial σ k ⧸ m) ⊗[k] k', ε t * x = 0 → x = 0 :=
    fun t ht x h => eq_zero_of_map_mul_eq_zero gK hgK ht h
  -- `Ψ(B)` is integral over the image of `k[T] ⊗_k k̃`
  have hint : ∀ r : Ψ.range, (ε.codRestrict Ψ.range hε).IsIntegralElem r := by
    set ν := ε.codRestrict Ψ.range hε with hν
    have hCi : ∀ c : k', ν.IsIntegralElem (Ψ.rangeRestrict (MvPolynomial.C c)) := by
      intro c
      have : Ψ.rangeRestrict (MvPolynomial.C c) = ν (1 ⊗ₜ c) := by
        apply Subtype.ext
        simp [hν, hεdef, hΨ2, gK]
      rw [this]
      exact RingHom.isIntegralElem_map (f := ν)
    have hXi : ∀ i : σ, ν.IsIntegralElem (Ψ.rangeRestrict (MvPolynomial.X i)) := by
      intro i
      obtain ⟨f, hfm, hf⟩ := hgint (Ideal.Quotient.mk m (MvPolynomial.X i))
      refine ⟨f.map (Algebra.TensorProduct.includeLeftRingHom : MvPolynomial (Fin s) k →+*
        MvPolynomial (Fin s) k ⊗[k] k'), hfm.map (Algebra.TensorProduct.includeLeftRingHom : MvPolynomial (Fin s) k →+*
        MvPolynomial (Fin s) k ⊗[k] k'), ?_⟩
      set d := Ideal.Quotient.mk m (MvPolynomial.X i) with hd
      set j : FractionRing (MvPolynomial σ k ⧸ m) →+* FractionRing (MvPolynomial σ k ⧸ m) ⊗[k] k' :=
        Algebra.TensorProduct.includeLeftRingHom with hj
      have hΨX : Ψ (MvPolynomial.X i) = j (algebraMap (MvPolynomial σ k ⧸ m)
          (FractionRing (MvPolynomial σ k ⧸ m)) d) := by
        have := hΨ1 (MvPolynomial.X i)
        rw [MvPolynomial.map_X] at this
        rw [this]
        rfl
      have e1 : (Ψ.range.subtype.comp ν).comp
          (Algebra.TensorProduct.includeLeftRingHom : MvPolynomial (Fin s) k →+*
            MvPolynomial (Fin s) k ⊗[k] k') =
          (j.comp (algebraMap (MvPolynomial σ k ⧸ m)
            (FractionRing (MvPolynomial σ k ⧸ m)))).comp g.toRingHom := by
        refine RingHom.ext fun p => ?_
        simp [hν, hεdef, gK, hj]
      apply Subtype.ext
      have h1 : Ψ.range.subtype (Polynomial.eval₂ ν (Ψ.rangeRestrict (MvPolynomial.X i))
          (f.map (Algebra.TensorProduct.includeLeftRingHom : MvPolynomial (Fin s) k →+*
            MvPolynomial (Fin s) k ⊗[k] k'))) = 0 := by
        rw [Polynomial.hom_eval₂, Polynomial.eval₂_map, e1]
        have e2 : Ψ.range.subtype (Ψ.rangeRestrict (MvPolynomial.X i)) =
            j (algebraMap (MvPolynomial σ k ⧸ m) (FractionRing (MvPolynomial σ k ⧸ m)) d) := hΨX
        rw [e2]
        have key := Polynomial.hom_eval₂ f g.toRingHom
          (j.comp (algebraMap (MvPolynomial σ k ⧸ m) (FractionRing (MvPolynomial σ k ⧸ m)))) d
        rw [hf, map_zero] at key
        exact key.symm
      exact h1
    intro r
    obtain ⟨b, rfl⟩ := Ψ.rangeRestrict_surjective r
    induction b using MvPolynomial.induction_on with
    | C c => exact hCi c
    | add p p' hp hp' => rw [map_add]; exact RingHom.IsIntegralElem.add ν hp hp'
    | mul_X p i hp => rw [map_mul]; exact RingHom.IsIntegralElem.mul ν hp (hXi i)
  exact mem_minimalPrimes_ker_of_mem_associatedPrimes Ψ ε hε hnzd hint hq


end EmbeddedPrimes

section Chart

variable {R Rb : Type u} [CommRing R] [IsRegularLocalRing R] [IsDomain R]
  [CommRing Rb] [IsRegularLocalRing Rb] [IsDomain Rb] {P : Ideal R}

omit [IsDomain Rb] in
/-- p. 211, "all the associated prime ideals of `m̄'k̃[X₂,…,X_r]` are isolated because `m̄'` is a prime
ideal in `k[X₂,…,X_r]`", for the residue fields `k ⊆ k̃` of `R ⊆ R̃` and `m̄' = M'/MA'`, without any
hypothesis on `k̃/k` (`Hironaka.mem_minimalPrimes_of_mem_associatedPrimes`). -/
theorem MonoidalTransform.mem_minimalPrimes_of_mem_associatedPrimes_map_general (α : R →+* Rb)
    [IsLocalHom α] (t : MonoidalTransform R P) {r : ℕ}
    (π : blowupAlgebra R P t.x →+* MvPolynomial (Fin r) (IsLocalRing.ResidueField R))
    (hπ : Function.Surjective π) (hkπ : RingHom.ker π ≤ t.M')
    {q : Ideal (MvPolynomial (Fin r) (IsLocalRing.ResidueField Rb))}
    (hq : q ∈ associatedPrimes (MvPolynomial (Fin r) (IsLocalRing.ResidueField Rb))
      (MvPolynomial (Fin r) (IsLocalRing.ResidueField Rb) ⧸
        (t.M'.map π).map (MvPolynomial.map (IsLocalRing.ResidueField.map α)))) :
    q ∈ ((t.M'.map π).map (MvPolynomial.map (IsLocalRing.ResidueField.map α))).minimalPrimes := by
  have : (t.M'.map π).IsPrime := Ideal.map_isPrime_of_surjective hπ hkπ
  exact mem_minimalPrimes_of_mem_associatedPrimes (IsLocalRing.ResidueField.map α) (t.M'.map π) hq

end Chart

end Hironaka
