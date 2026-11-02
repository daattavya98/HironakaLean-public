/-
Copyright (c) 2026 Daattavya Aggarwal, Minhyong Kim, Oisin Kim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daattavya Aggarwal, Minhyong Kim, Oisin Kim
-/
module

public import Mathlib.RingTheory.Ideal.UFD
public import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
public import Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Localization.AsSubring
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.Localization.Integer
public import Mathlib.RingTheory.Localization.Submodule
public import Mathlib.Algebra.GCDMonoid.Finset
public import Mathlib.RingTheory.UniqueFactorizationDomain.GCDMonoid

/-!
# Primitive vectors over a UFD and the primitive locus (Compat API for Corollary 2 of Main Theorem II)

Hironaka, Ch. 0, Corollary 2 of Main Theorem II (p. 145) begins with the remark "we first remark that
any locally free coherent sheaf `F` contains an invertible sheaf of `O_X`-modules `M`", asserted without
proof or citation (filled in `Hironaka/Compat/InvertibleSubsheaf.lean`).  The proof used there is
the standard one for a regular scheme: the saturation of a rational section of `F` is invertible because
the local rings are unique factorization domains (the factoriality of regular local rings is the cited
fact of `Hironaka/Compat/RegularLocalRingUFD.lean`; footnote 3, p. 116).  This module is the ring-theoretic
core, with no sheaves.  Let `K` be the fraction field of a domain `A`.  A vector `w : ι → K` is *primitive*
for a subset `S ⊆ K` if a scalar `l` with all `l * wᵢ ∈ S` lies in `S`.

* `Hironaka.exists_mul_coprime_of_ufd`: a nonzero vector over a UFD is a multiple `g • w` of a vector with
  no common non-unit divisor;
* `Hironaka.exists_isPrimitive_smul`: in the fraction field `K` of a UFD `B` every nonzero vector is a
  nonzero scalar multiple of a vector of `B` which is primitive for `B`;
* `Hironaka.exists_forall_isPrimitive_of_isPrimitive`: if `A` is a noetherian domain all of whose
  localizations at primes are UFDs, the primitive locus of `w : ι → A` is open: if `w` is primitive for
  `A_p`, there is `f ∉ p` such that `w` is primitive for `A_q` for every prime `q` with `f ∉ q`.  (The
  non-primitive primes lie over the finitely many height-one minimal primes of `(wᵢ)`.)

This is infrastructure (no statement of the paper); it is not a deviation.
-/

@[expose] public section

open scoped nonZeroDivisors

namespace Hironaka

/-- In a UFD a vector which is not zero is `g • w` where `w` has no common non-unit divisor. -/
theorem exists_mul_coprime_of_ufd {B : Type*} [CommRing B] [IsDomain B] [UniqueFactorizationMonoid B]
    {ι : Type*} [Fintype ι] (p : ι → B) (hp : ∃ i, p i ≠ 0) :
    ∃ (g : B) (w : ι → B), g ≠ 0 ∧ (∀ i, p i = g * w i) ∧ ∀ b : B, (∀ i, b ∣ w i) → IsUnit b := by
  classical
  have := UniqueFactorizationMonoid.strongNormalizationMonoid (α := B)
  have := UniqueFactorizationMonoid.toNormalizedGCDMonoid B
  set g : B := Finset.univ.gcd p with hg
  have hg0 : g ≠ 0 := by
    intro h
    obtain ⟨i, hi⟩ := hp
    exact hi (Finset.gcd_eq_zero_iff.mp h i (Finset.mem_univ i))
  have hdvd : ∀ i, g ∣ p i := fun i => Finset.gcd_dvd (Finset.mem_univ i)
  choose w hw using hdvd
  refine ⟨g, w, hg0, hw, fun b hb => ?_⟩
  have h1 : g * b ∣ g := by
    refine Finset.dvd_gcd fun i _ => ?_
    rw [hw i]
    exact mul_dvd_mul_left g (hb i)
  have h2 : g * b ∣ g * 1 := by simpa using h1
  exact isUnit_of_dvd_one ((mul_dvd_mul_iff_left hg0).mp h2)

/-- The vector `w` is *primitive* for the subset `S` of `K`: a scalar `l` with all `l * wᵢ` in `S`
lies in `S`. -/
def IsPrimitive {K : Type*} [Mul K] (S : Set K) {ι : Type*} (w : ι → K) : Prop :=
  ∀ l : K, (∀ i, l * w i ∈ S) → l ∈ S

/-- In a UFD `B` with fraction field `K`, if `l ∈ K` is not in `B` but all `l * wᵢ` are, then the `wᵢ`
have a common divisor which is not a unit (the denominator of `l` in lowest terms). -/
theorem exists_nonUnit_dvd_of_mul_mem {B K : Type*} [CommRing B] [IsDomain B]
    [UniqueFactorizationMonoid B] [Field K] [Algebra B K] [IsFractionRing B K] {ι : Type*}
    (w : ι → B) (l : K) (hl : l ∉ Set.range (algebraMap B K))
    (hlw : ∀ i, l * algebraMap B K (w i) ∈ Set.range (algebraMap B K)) :
    ∃ b : B, ¬ IsUnit b ∧ b ≠ 0 ∧ ∀ i, b ∣ w i := by
  have hinj : Function.Injective (algebraMap B K) := IsFractionRing.injective B K
  obtain ⟨x, y, hy, hxy⟩ := IsFractionRing.div_surjective B l
  have hy0 : y ≠ 0 := nonZeroDivisors.ne_zero hy
  have hx0 : x ≠ 0 := by
    rintro rfl
    exact hl ⟨0, by rw [← hxy]; simp⟩
  obtain ⟨a', b', c', hrel, hca, hcb⟩ := UniqueFactorizationMonoid.exists_reduced_factors x hx0 y
  have hc0 : c' ≠ 0 := by
    rintro rfl
    exact hy0 (by rw [← hcb]; simp)
  have hb'0 : b' ≠ 0 := by
    rintro rfl
    exact hy0 (by rw [← hcb]; simp)
  have hlab : l = algebraMap B K a' / algebraMap B K b' := by
    rw [← hxy, ← hca, ← hcb, map_mul, map_mul]
    have : algebraMap B K c' ≠ 0 := fun h => hc0 (hinj (by simpa using h))
    field_simp
  have hbw : ∀ i, b' ∣ w i := by
    intro i
    obtain ⟨z, hz⟩ := hlw i
    rw [hlab] at hz
    have hb'K : algebraMap B K b' ≠ 0 := fun h => hb'0 (hinj (by simpa using h))
    have h3 : algebraMap B K (a' * w i) = algebraMap B K (z * b') := by
      rw [map_mul, map_mul, hz]
      field_simp
    have h4 : a' * w i = z * b' := hinj h3
    have h5 : b' ∣ a' * w i := ⟨z, by rw [h4]; ring⟩
    exact hrel.symm.dvd_of_dvd_mul_left h5
  refine ⟨b', fun hu => hl ?_, hb'0, hbw⟩
  obtain ⟨u, hu⟩ := hu
  refine ⟨a' * ↑u⁻¹, ?_⟩
  rw [hlab, map_mul, ← hu]
  simp [div_eq_mul_inv]

/-- **Primitive representatives over a UFD.** In the fraction field `K` of a UFD `B`, every vector which is
not zero is a non-zero scalar multiple `μ • α` of a vector with entries in `B` which is primitive for `B`. -/
theorem exists_isPrimitive_smul {B K : Type*} [CommRing B] [IsDomain B] [UniqueFactorizationMonoid B]
    [Field K] [Algebra B K] [IsFractionRing B K] {ι : Type*} [Fintype ι] (α : ι → K)
    (hα : ∃ i, α i ≠ 0) :
    ∃ μ : K, μ ≠ 0 ∧ (∀ i, μ * α i ∈ Set.range (algebraMap B K)) ∧
      IsPrimitive (Set.range (algebraMap B K)) fun i => μ * α i := by
  classical
  have hinj : Function.Injective (algebraMap B K) := IsFractionRing.injective B K
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples_of_finset (nonZeroDivisors B)
    (Finset.univ.image α)
  choose p hp using fun i => hb (α i) (Finset.mem_image_of_mem _ (Finset.mem_univ i))
  have hpα : ∀ i, algebraMap B K (p i) = (b : B) • α i := hp
  have hb0 : algebraMap B K (b : B) ≠ 0 := by
    intro h
    exact nonZeroDivisors.coe_ne_zero b (hinj (by simp at h ⊢))
  have hpne : ∃ i, p i ≠ 0 := by
    obtain ⟨i, hi⟩ := hα
    refine ⟨i, fun h => ?_⟩
    have := hpα i
    rw [h, map_zero, Algebra.smul_def] at this
    exact hi ((mul_eq_zero.mp this.symm).resolve_left hb0)
  obtain ⟨g, w, hg0, hw, hcop⟩ := exists_mul_coprime_of_ufd p hpne
  have hg0' : algebraMap B K g ≠ 0 := fun h => hg0 (hinj (by simpa using h))
  have hμ : ∀ i, algebraMap B K (b : B) / algebraMap B K g * α i = algebraMap B K (w i) := by
    intro i
    have h1 := hpα i
    rw [Algebra.smul_def, hw i, map_mul] at h1
    field_simp
    rw [← h1]
  refine ⟨algebraMap B K (b : B) / algebraMap B K g, div_ne_zero hb0 hg0',
    fun i => ⟨w i, (hμ i).symm⟩, fun l hl => ?_⟩
  by_contra hl'
  simp only [hμ] at hl
  obtain ⟨c, hc, -, hcw⟩ := exists_nonUnit_dvd_of_mul_mem w l hl' hl
  exact hc (hcop c hcw)

section PrimitiveLocus

variable {A : Type*} (K : Type*) [CommRing A] [IsDomain A] [Field K] [Algebra A K] [IsFractionRing A K]

/-- The localization `A_q` of a domain `A` at a prime `q`, as a subalgebra of its fraction field `K`. -/
noncomputable abbrev locAlg (q : Ideal A) [q.IsPrime] : Subalgebra A K :=
  Localization.subalgebra.ofField K q.primeCompl q.primeCompl_le_nonZeroDivisors

variable {K}

variable {ι : Type*}

/-- If `Q ≤ p` is a prime of height one of `A` and the entries of `w` lie in `Q`, `w` is not primitive for
`A_p` when `A_p` is a UFD: `Q A_p = (π)` is principal and `l = π⁻¹` violates primitivity. -/
theorem not_isPrimitive_of_height_eq_one {w : ι → A} {p Q : Ideal A} [p.IsPrime] [Q.IsPrime]
    (hUFD : UniqueFactorizationMonoid (locAlg K p)) (hQ : Q.height = 1) (hQp : Q ≤ p)
    (hw : ∀ i, w i ∈ Q) :
    ¬ IsPrimitive (locAlg K p : Set K) fun i => algebraMap A K (w i) := by
  intro hprim
  let B := locAlg K p
  have hdisj : Disjoint (p.primeCompl : Set A) Q := by
    rw [Set.disjoint_left]
    intro a ha haQ
    exact ha (hQp haQ)
  let P : Ideal B := Q.map (algebraMap A B)
  have hP : P.IsPrime := IsLocalization.isPrime_of_isPrime_disjoint p.primeCompl B Q ‹_› hdisj
  have hPQ : P.under A = Q := IsLocalization.under_map_of_isPrime_disjoint p.primeCompl B ‹_› hdisj
  have hPh : P.height = 1 := by
    rw [← IsLocalization.height_under p.primeCompl P, hPQ, hQ]
  obtain ⟨π, hπ_eq⟩ := (UniqueFactorizationMonoid.isPrincipal_of_height_eq_one hPh).principal
  have hπ0 : π ≠ 0 := by
    rintro rfl
    have : P = ⊥ := by rw [hπ_eq]; simp
    exact Ideal.ne_bot_of_height_eq_one hPh this
  have hπK : ((π : B) : K) ≠ 0 := fun h => hπ0 (Subtype.ext h)
  have hmem : ∀ i, algebraMap A B (w i) ∈ P := fun i => Ideal.mem_map_of_mem _ (hw i)
  have hdvd : ∀ i, π ∣ algebraMap A B (w i) := fun i => by
    have := hmem i
    rw [hπ_eq, Ideal.mem_span_singleton] at this
    exact this
  have key := hprim ((π : K)⁻¹) fun i => by
    obtain ⟨t, ht⟩ := hdvd i
    have h1 : algebraMap A K (w i) = (π : K) * (t : K) := by
      have e : ((algebraMap A B (w i) : B) : K) = algebraMap A K (w i) := rfl
      rw [← e, ht]
      rfl
    show (π : K)⁻¹ * algebraMap A K (w i) ∈ B
    rw [h1, ← mul_assoc, inv_mul_cancel₀ hπK, one_mul]
    exact t.2
  have hs : (π : K)⁻¹ ∈ B := key
  have hunit : IsUnit π := IsUnit.of_mul_eq_one (⟨_, hs⟩ : B) (Subtype.ext (mul_inv_cancel₀ hπK))
  exact hP.ne_top (by rw [hπ_eq, Ideal.span_singleton_eq_top]; exact hunit)


/-- If `w` is not primitive for the UFD `A_q`, some prime `π` of `A_q` divides all the entries; it contracts
to a prime `Q ≤ q` of height one of the noetherian domain `A` containing all `wᵢ`. -/
theorem exists_height_eq_one_of_not_isPrimitive [IsNoetherianRing A] {w : ι → A} {q : Ideal A}
    [q.IsPrime] (hUFD : UniqueFactorizationMonoid (locAlg K q))
    (h : ¬ IsPrimitive (locAlg K q : Set K) fun i => algebraMap A K (w i)) :
    ∃ Q : Ideal A, Q.IsPrime ∧ Q.height = 1 ∧ (∀ i, w i ∈ Q) ∧ Q ≤ q := by
  let B := locAlg K q
  have hNB : IsNoetherianRing B := IsLocalization.isNoetherianRing q.primeCompl B ‹_›
  simp only [IsPrimitive, not_forall] at h
  obtain ⟨l, hl, hlB⟩ := h
  obtain ⟨b, hb, hb0, hbw⟩ := exists_nonUnit_dvd_of_mul_mem (B := B) (K := K)
    (fun i => algebraMap A B (w i)) l (fun ⟨x, hx⟩ => hlB (hx ▸ x.2)) fun i => ⟨⟨_, hl i⟩, rfl⟩
  obtain ⟨π, hπirr, hπb⟩ := WfDvdMonoid.exists_irreducible_factor hb hb0
  have hπ : Prime π := UniqueFactorizationMonoid.irreducible_iff_prime.mp hπirr
  let P : Ideal B := Ideal.span {π}
  have hP : P.IsPrime := (Ideal.span_singleton_prime hπ.ne_zero).mpr hπ
  have hPne : P ≠ ⊥ := by simpa [P] using hπ.ne_zero
  have hP1 : P.height = 1 := by
    refine le_antisymm (Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes P P
      ⟨⟨hP, le_rfl⟩, fun r hr _ => hr.2⟩) ?_
    rw [Order.one_le_iff_pos, pos_iff_ne_zero]
    intro h0
    exact hPne (Ideal.height_eq_zero_iff_eq_bot.mp h0)
  refine ⟨P.under A, inferInstance, ?_, fun i => ?_, fun a ha => ?_⟩
  · rw [IsLocalization.height_under q.primeCompl P, hP1]
  · rw [Ideal.mem_comap, Ideal.mem_span_singleton]
    exact hπb.trans (hbw i)
  · by_contra haq
    have hu : IsUnit (algebraMap A B a) := IsLocalization.map_units B (⟨a, haq⟩ : q.primeCompl)
    exact hP.ne_top (Ideal.eq_top_of_isUnit_mem P (Ideal.mem_comap.mp ha) hu)

/-- **Openness of the primitive locus.** Let `A` be a noetherian domain whose localizations at primes are UFDs
and `w : ι → A` a vector which is not zero.  If `w` is primitive for `A_p`, there is `f ∉ p` such that `w` is
primitive for `A_q` for every prime `q` with `f ∉ q`.  (The `q` for which `w` is not primitive contain one of
the finitely many minimal primes of `(wᵢ)` of height one, and none of these lies in `p`.) -/
theorem exists_forall_isPrimitive_of_isPrimitive [IsNoetherianRing A]
    (hUFD : ∀ (q : Ideal A) [q.IsPrime], UniqueFactorizationMonoid (locAlg K q)) [Finite ι]
    {w : ι → A} (hw : ∃ i, w i ≠ 0) {p : Ideal A} [p.IsPrime]
    (hp : IsPrimitive (locAlg K p : Set K) fun i => algebraMap A K (w i)) :
    ∃ f : A, f ∉ p ∧ ∀ (q : Ideal A) [q.IsPrime], f ∉ q →
      IsPrimitive (locAlg K q : Set K) fun i => algebraMap A K (w i) := by
  classical
  let I : Ideal A := Ideal.span (Set.range w)
  have hwI : ∀ i, w i ∈ I := fun i => Ideal.subset_span ⟨i, rfl⟩
  have hI0 : I ≠ ⊥ := by
    obtain ⟨i, hi⟩ := hw
    exact fun h => hi (by simpa [h] using hwI i)
  have hfin : {Q : Ideal A | Q ∈ I.minimalPrimes ∧ Q.height = 1}.Finite :=
    (I.finite_minimalPrimes_of_isNoetherianRing A).subset fun Q hQ => hQ.1
  let N := hfin.toFinset
  have hN : ∀ Q, Q ∈ N ↔ Q ∈ I.minimalPrimes ∧ Q.height = 1 := fun Q => by simp [N]
  have hnotle : ¬ (N.prod id) ≤ p := by
    rw [Ideal.IsPrime.prod_le ‹p.IsPrime›]
    rintro ⟨Q, hQ, hQp⟩
    obtain ⟨hQmin, hQ1⟩ := (hN Q).mp hQ
    have := hQmin.1.1
    exact not_isPrimitive_of_height_eq_one (hUFD p) hQ1 hQp
      (fun i => hQmin.1.2 (hwI i)) hp
  obtain ⟨f, hfN, hfp⟩ := IsConcreteLE.not_le_iff_exists.mp hnotle
  refine ⟨f, hfp, fun q _ hfq => ?_⟩
  by_contra hq
  obtain ⟨Q, hQ, hQ1, hwQ, hQq⟩ := exists_height_eq_one_of_not_isPrimitive (hUFD q) hq
  have hIQ : I ≤ Q := Ideal.span_le.mpr (by rintro _ ⟨i, rfl⟩; exact hwQ i)
  have hfh : Q.FiniteHeight := by simp [Q.finiteHeight_iff, hQ1]
  have hIh : 1 ≤ I.height := by
    rw [Order.one_le_iff_pos, pos_iff_ne_zero]
    exact fun h0 => hI0 (Ideal.height_eq_zero_iff_eq_bot.mp h0)
  have hmin : Q ∈ I.minimalPrimes := Ideal.mem_minimalPrimes_of_height_le hIQ (hQ1 ▸ hIh)
  have hQN : Q ∈ N := (hN Q).mpr ⟨hmin, hQ1⟩
  have hfQ : f ∈ Q := (Finset.inf_le hQN : N.inf id ≤ Q) (Ideal.prod_le_inf hfN)
  exact hfq (hQq hfQ)

variable (K) in
/-- The image of a localization `B` of `A` at `q` in the fraction field `K` is `A_q ⊆ K`. -/
theorem range_algebraMap_eq_locAlg (q : Ideal A) [q.IsPrime] (B : Type*) [CommRing B] [Algebra A B]
    [IsLocalization.AtPrime B q] [Algebra B K] [IsScalarTower A B K] :
    Set.range (algebraMap B K) = (locAlg K q : Set K) := by
  let e := IsLocalization.algEquiv q.primeCompl B (locAlg K q)
  have h : algebraMap B K = (algebraMap (locAlg K q) K).comp (e : B ≃+* locAlg K q).toRingHom := by
    refine IsLocalization.ringHom_ext q.primeCompl ?_
    ext a
    simp [IsScalarTower.algebraMap_apply A B K, e]
  ext x
  constructor
  · rintro ⟨b, rfl⟩
    rw [h]
    exact (e b).2
  · intro hx
    refine ⟨e.symm ⟨x, hx⟩, ?_⟩
    rw [h]
    simp

variable (K) in
/-- A UFD localization transports along the identification with `A_q ⊆ K`. -/
theorem uniqueFactorizationMonoid_locAlg (q : Ideal A) [q.IsPrime] (B : Type*) [CommRing B]
    [Algebra A B] [IsLocalization.AtPrime B q] (hB : UniqueFactorizationMonoid B) :
    UniqueFactorizationMonoid (locAlg K q) :=
  (IsLocalization.algEquiv q.primeCompl B (locAlg K q)).toMulEquiv.uniqueFactorizationMonoid hB

end PrimitiveLocus

end Hironaka
