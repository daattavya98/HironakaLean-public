/-
Copyright (c) 2026 Daattavya Aggarwal, Minhyong Kim, Oisin Kim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daattavya Aggarwal, Minhyong Kim, Oisin Kim
-/
module

public import Mathlib.Algebra.GCDMonoid.Finset
public import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
public import Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Localization.Ideal
public import Mathlib.RingTheory.UniqueFactorizationDomain.GCDMonoid
public import Hironaka.Compat.PrimitiveLocus

/-!
# The divisor of an ideal in a unique factorization domain, and its spreading (ring theory)

Ring-theoretic core of the decomposition "a sheaf of non-zero ideals on a non-singular scheme is an invertible sheaf of
ideals times one which is not divisible by any invertible sheaf of ideals" (used when (*) of p. 141 is applied; see
`Hironaka/Compat/PrimitiveIdeal.lean`).  Everything here is about rings; there are no sheaves.

* `Hironaka.gcdIdeal I`: the intersection of the principal ideals containing `I`.  In a unique factorization domain, if
  `I = (a w₁, …, w_n a)` with the `wᵢ` without common non-unit divisor, then `gcdIdeal I = (a)`
  (`gcdIdeal_eq_span_of_coprime`), and `I = (g wᵢ)` for some `g`, `wᵢ` always exists (`exists_gcd_decomposition`).
* `Hironaka.HeightGood w q`: no prime `Q ≤ q` of height at most one of the ring contains all the `wᵢ`.  For a localization
  `B` of `A` at `q` which is a unique factorization domain, it is equivalent to "the `wᵢ` have no common non-unit divisor
  in `B`" (`heightGood_iff_coprime`), and it is open: `exists_forall_heightGood`.

This is infrastructure (no statement of the paper); the paper uses the decomposition tacitly.
-/

@[expose] public section

open scoped nonZeroDivisors

namespace Hironaka

universe u v

section Gcd

variable {B : Type u} [CommRing B]

/-- The intersection of the principal ideals containing `I`. -/
def gcdIdeal (I : Ideal B) : Ideal B :=
  ⨅ (Q : Ideal B) (_ : Q.IsPrincipal ∧ I ≤ Q), Q

theorem le_gcdIdeal (I : Ideal B) : I ≤ gcdIdeal I :=
  le_iInf₂ fun _ hQ => hQ.2

theorem gcdIdeal_le_of_le_span {I : Ideal B} {h : B} (hI : I ≤ Ideal.span {h}) :
    gcdIdeal I ≤ Ideal.span {h} :=
  iInf₂_le (Ideal.span {h}) ⟨⟨⟨h, rfl⟩⟩, hI⟩

/-- In a unique factorization domain, `gcdIdeal (a·(w₁, …, w_n)) = (a)` if the `wᵢ` have no common non-unit divisor. -/
theorem gcdIdeal_eq_span_of_coprime [IsDomain B] [UniqueFactorizationMonoid B] {ι : Type*} [Fintype ι]
    (a : B) (w : ι → B) (hw : ∀ b : B, (∀ i, b ∣ w i) → IsUnit b) :
    gcdIdeal (Ideal.span (Set.range fun i => a * w i)) = Ideal.span {a} := by
  classical
  refine le_antisymm (gcdIdeal_le_of_le_span ?_) ?_
  · rw [Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    exact Ideal.mem_span_singleton.mpr (dvd_mul_right a (w i))
  · refine le_iInf₂ fun Q hQ => ?_
    obtain ⟨⟨h, rfl⟩⟩ := hQ.1
    have hdvd : ∀ i, h ∣ a * w i := fun i =>
      Ideal.mem_span_singleton.mp (hQ.2 (Ideal.subset_span ⟨i, rfl⟩))
    have := UniqueFactorizationMonoid.strongNormalizationMonoid (α := B)
    have := UniqueFactorizationMonoid.toNormalizedGCDMonoid B
    have h1 : h ∣ Finset.univ.gcd fun i => a * w i :=
      Finset.dvd_gcd fun i _ => hdvd i
    have h1' : h ∣ a * Finset.univ.gcd w :=
      ((Finset.gcd_mul_left' Finset.univ w a).dvd_iff_dvd_right).mp h1
    have hu : IsUnit (Finset.univ.gcd w) :=
      hw _ fun i => Finset.gcd_dvd (Finset.mem_univ i)
    exact Ideal.span_singleton_le_span_singleton.mpr (hu.dvd_mul_right.mp h1')

/-- In a noetherian unique factorization domain, a non-zero ideal `I` has a divisor: `I ≤ (g)` and `gcdIdeal I = (g)`
with `g ≠ 0`. -/
theorem exists_gcdIdeal_eq_span [IsDomain B] [IsNoetherianRing B] [UniqueFactorizationMonoid B] (I : Ideal B)
    (hI : I ≠ ⊥) : ∃ g : B, g ≠ 0 ∧ gcdIdeal I = Ideal.span {g} ∧ I ≤ Ideal.span {g} := by
  classical
  obtain ⟨s, hs⟩ := (IsNoetherian.noetherian I : I.FG)
  have hp : ∃ i : s, (i : B) ≠ 0 := by
    by_contra hcon
    push Not at hcon
    apply hI
    rw [← hs, Ideal.span_eq_bot]
    intro z hz
    exact hcon ⟨z, hz⟩
  obtain ⟨g, w, hg0, hpw, hcop⟩ := exists_mul_coprime_of_ufd (fun i : s => (i : B)) hp
  have hI' : I = Ideal.span (Set.range fun i : s => g * w i) := by
    rw [← hs]
    congr 1
    ext z
    constructor
    · intro hz
      exact ⟨⟨z, hz⟩, (hpw ⟨z, hz⟩).symm⟩
    · rintro ⟨i, rfl⟩
      show g * w i ∈ (s : Set B)
      rw [← hpw i]
      exact i.2
  refine ⟨g, hg0, ?_, ?_⟩
  · rw [hI']
    exact gcdIdeal_eq_span_of_coprime g w hcop
  · rw [hI', Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    exact Ideal.mem_span_singleton.mpr (dvd_mul_right g (w i))

end Gcd

section HeightGood

theorem enat_le_one_of_lt_two {h : ℕ∞} (hh : h < 2) : h ≤ 1 := by
  induction h using ENat.recTopCoe with
  | top => simp at hh
  | coe n =>
    have : n < 2 := by exact_mod_cast hh
    have : n ≤ 1 := by omega
    show ((n : ℕ) : ℕ∞) ≤ ((1 : ℕ) : ℕ∞)
    exact ENat.natCast_le_natCast.mpr this

variable {A : Type u} [CommRing A] {ι : Type*}

/-- No prime `Q ≤ q` of height at most one of `A` contains all the `wᵢ`. -/
def HeightGood (w : ι → A) (q : Ideal A) : Prop :=
  ∀ Q : Ideal A, Q.IsPrime → Q ≤ q → (∀ i, w i ∈ Q) → 2 ≤ Q.height

variable {B : Type v} [CommRing B] [Algebra A B] (q : Ideal A) [q.IsPrime] [IsLocalization.AtPrime B q]
  [IsDomain B] [IsNoetherianRing B] [UniqueFactorizationMonoid B] (w : ι → A)

/-- For a localization `B` of `A` at a prime `q` which is a unique factorization domain, `HeightGood w q` says that the
`wᵢ` have no common non-unit divisor in `B` (in particular they are not all zero there). -/
theorem heightGood_iff_coprime :
    HeightGood w q ↔ ∀ π : B, (∀ i, π ∣ algebraMap A B (w i)) → IsUnit π := by
  constructor
  · intro hgood π hπ
    by_contra hnu
    by_cases hπ0 : π = 0
    · subst hπ0
      have hw0 : ∀ i, algebraMap A B (w i) = 0 := fun i => zero_dvd_iff.mp (hπ i)
      have hQ : ((⊥ : Ideal B).under A).IsPrime := Ideal.comap_isPrime _ _
      have hle : (⊥ : Ideal B).under A ≤ q := by
        intro a ha
        rw [Ideal.mem_comap, Ideal.mem_bot] at ha
        obtain ⟨s, hs⟩ := (IsLocalization.map_eq_zero_iff q.primeCompl B a).mp ha
        by_contra haq
        have : (s : A) * a ∈ q := by rw [hs]; exact q.zero_mem
        rcases Ideal.IsPrime.mem_or_mem inferInstance this with h | h
        · exact s.2 h
        · exact haq h
      have h2 := hgood _ hQ hle fun i => by
        rw [Ideal.mem_comap, hw0 i]; exact Ideal.zero_mem _
      rw [IsLocalization.height_under q.primeCompl (⊥ : Ideal B)] at h2
      have : (⊥ : Ideal B).height = 0 := Ideal.height_eq_zero_iff_eq_bot.mpr rfl
      rw [this] at h2
      exact absurd h2 (by norm_num)
    · obtain ⟨ρ, hρirr, hρπ⟩ := WfDvdMonoid.exists_irreducible_factor hnu hπ0
      have hρ : Prime ρ := UniqueFactorizationMonoid.irreducible_iff_prime.mp hρirr
      let P : Ideal B := Ideal.span {ρ}
      have hP : P.IsPrime := (Ideal.span_singleton_prime hρ.ne_zero).mpr hρ
      have hPne : P ≠ ⊥ := by simpa [P] using hρ.ne_zero
      have hP1 : P.height = 1 := by
        refine le_antisymm (Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes P P
          ⟨⟨hP, le_rfl⟩, fun r hr _ => hr.2⟩) ?_
        rw [Order.one_le_iff_pos, pos_iff_ne_zero]
        intro h0
        exact hPne (Ideal.height_eq_zero_iff_eq_bot.mp h0)
      have h2 := hgood (P.under A) inferInstance (fun a ha => by
          by_contra haq
          have hu : IsUnit (algebraMap A B a) :=
            IsLocalization.map_units B (⟨a, haq⟩ : q.primeCompl)
          exact hP.ne_top (Ideal.eq_top_of_isUnit_mem P (Ideal.mem_comap.mp ha) hu))
        (fun i => by
          rw [Ideal.mem_comap, Ideal.mem_span_singleton]
          exact hρπ.trans (hπ i))
      rw [IsLocalization.height_under q.primeCompl P, hP1] at h2
      exact absurd h2 (by norm_num)
  · intro hcop Q hQ hQq hwQ
    by_contra hlt
    rw [not_le] at hlt
    have hdisj : Disjoint (q.primeCompl : Set A) Q := by
      rw [Set.disjoint_left]
      intro a ha haQ
      exact ha (hQq haQ)
    let P : Ideal B := Q.map (algebraMap A B)
    have hP : P.IsPrime := IsLocalization.isPrime_of_isPrime_disjoint q.primeCompl B Q hQ hdisj
    have hPQ : P.under A = Q := IsLocalization.under_map_of_isPrime_disjoint q.primeCompl B hQ hdisj
    have hPh : P.height < 2 := by rw [← IsLocalization.height_under q.primeCompl P, hPQ]; exact hlt
    have hmem : ∀ i, algebraMap A B (w i) ∈ P := fun i => Ideal.mem_map_of_mem _ (hwQ i)
    by_cases h0 : P.height = 0
    · have hPbot : P = ⊥ := Ideal.height_eq_zero_iff_eq_bot.mp h0
      have hw0 : ∀ i, algebraMap A B (w i) = 0 := fun i => by
        have := hmem i
        rwa [hPbot, Ideal.mem_bot] at this
      exact not_isUnit_zero (hcop 0 fun i => by rw [hw0 i])
    · have h1 : P.height = 1 := by
        refine le_antisymm (enat_le_one_of_lt_two hPh) ?_
        rw [Order.one_le_iff_pos, pos_iff_ne_zero]
        exact h0
      obtain ⟨π, hπ_eq⟩ := (UniqueFactorizationMonoid.isPrincipal_of_height_eq_one h1).principal
      have hdvd : ∀ i, π ∣ algebraMap A B (w i) := fun i => by
        have := hmem i
        rw [hπ_eq, Ideal.mem_span_singleton] at this
        exact this
      have hu := hcop π hdvd
      exact hP.ne_top (by rw [hπ_eq, Ideal.span_singleton_eq_top]; exact hu)

/-- **Openness of `HeightGood`.**  If the `wᵢ` satisfy `HeightGood` at the prime `p` of a noetherian ring `A`, there is
`f ∉ p` such that they satisfy it at every prime `q` with `f ∉ q`: the primes of height at most one containing `(wᵢ)`
contain one of the finitely many minimal primes of `(wᵢ)` of height at most one, and none of these lies in `p`. -/
theorem exists_forall_heightGood [IsNoetherianRing A] [Finite ι] (w : ι → A) {p : Ideal A} [p.IsPrime]
    (hp : HeightGood w p) :
    ∃ f : A, f ∉ p ∧ ∀ (q : Ideal A) [q.IsPrime], f ∉ q → HeightGood w q := by
  classical
  let I : Ideal A := Ideal.span (Set.range w)
  have hwI : ∀ i, w i ∈ I := fun i => Ideal.subset_span ⟨i, rfl⟩
  have hfin : {Q : Ideal A | Q ∈ I.minimalPrimes ∧ Q.height ≤ 1}.Finite :=
    (I.finite_minimalPrimes_of_isNoetherianRing A).subset fun Q hQ => hQ.1
  let N := hfin.toFinset
  have hN : ∀ Q, Q ∈ N ↔ Q ∈ I.minimalPrimes ∧ Q.height ≤ 1 := fun Q => by simp [N]
  have hnotle : ¬ (N.prod id) ≤ p := by
    rw [Ideal.IsPrime.prod_le ‹p.IsPrime›]
    rintro ⟨Q, hQ, hQp⟩
    obtain ⟨hQmin, hQ1⟩ := (hN Q).mp hQ
    have h2 := hp Q hQmin.1.1 hQp (fun i => hQmin.1.2 (hwI i))
    exact absurd (hQ1.trans_lt (by norm_num)) (not_lt.mpr h2)
  obtain ⟨f, hfN, hfp⟩ := IsConcreteLE.not_le_iff_exists.mp hnotle
  refine ⟨f, hfp, fun q _ hfq Q hQ hQq hwQ => ?_⟩
  by_contra hlt
  rw [not_le] at hlt
  have hIQ : I ≤ Q := Ideal.span_le.mpr (by rintro _ ⟨i, rfl⟩; exact hwQ i)
  obtain ⟨P, hP, hPQ⟩ := Ideal.exists_minimalPrimes_le hIQ
  have hPh : P.height ≤ 1 := (Ideal.height_mono hPQ).trans (enat_le_one_of_lt_two hlt)
  have hPN : P ∈ N := (hN P).mpr ⟨hP, hPh⟩
  have hfP : f ∈ P := (Finset.inf_le hPN : N.inf id ≤ P) (Ideal.prod_le_inf hfN)
  exact hfq (hQq (hPQ hfP))

end HeightGood

section Spread

variable {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]

/-- **Spreading a local factorization.**  Let `B` be the localization of `A` at `p` and suppose `k i = g * w i` in `B`
(`i` in a finite type).  Then there are `a, cᵢ ∈ A` and `s, u ∉ p` with `a = s g` and `cᵢ = s wᵢ` in `B` and
`u (s² kᵢ) = u (a cᵢ)` in `A`: after inverting `s u`, `kᵢ = (a / s²) cᵢ`. -/
theorem exists_spread (p : Ideal A) [p.IsPrime] [IsLocalization.AtPrime B p] {ι : Type*} [Fintype ι]
    (k : ι → A) (g : B) (w : ι → B) (h : ∀ i, algebraMap A B (k i) = g * w i) :
    ∃ (a : A) (c : ι → A) (s u : A), s ∉ p ∧ u ∉ p ∧ algebraMap A B a = algebraMap A B s * g ∧
      (∀ i, algebraMap A B (c i) = algebraMap A B s * w i) ∧ ∀ i, u * (s ^ 2 * k i) = u * (a * c i) := by
  classical
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples_of_finset p.primeCompl
    (insert g (Finset.univ.image w))
  obtain ⟨a, ha⟩ := hb g (Finset.mem_insert_self _ _)
  have hc : ∀ i, ∃ c : A, algebraMap A B c = (b : A) • w i := fun i =>
    hb (w i) (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ (Finset.mem_univ i)))
  choose c hc using hc
  have hrel : ∀ i, ∃ u : p.primeCompl, (u : A) * ((b : A) ^ 2 * k i) = (u : A) * (a * c i) := fun i => by
    have h1 : algebraMap A B ((b : A) ^ 2 * k i) = algebraMap A B (a * c i) := by
      simp only [map_mul, map_pow, ha, hc i, h i, Algebra.smul_def]
      ring
    obtain ⟨u, hu⟩ := (IsLocalization.eq_iff_exists p.primeCompl B).mp h1
    exact ⟨u, hu⟩
  choose u hu using hrel
  refine ⟨a, c, b, ∏ i, (u i : A), b.2, ?_, ?_, ?_, ?_⟩
  · -- the product of the `u i` is outside `p`
    intro hmem
    obtain ⟨i, -, hi⟩ := Ideal.IsPrime.prod_mem_iff.mp hmem
    exact (u i).2 hi
  · rw [ha, Algebra.smul_def]
  · intro i
    rw [hc i, Algebra.smul_def]
  · intro i
    have : ∏ j, (u j : A) = (u i : A) * ∏ j ∈ Finset.univ.erase i, (u j : A) :=
      (Finset.mul_prod_erase _ _ (Finset.mem_univ i)).symm
    rw [this]
    calc (u i : A) * (∏ j ∈ Finset.univ.erase i, (u j : A)) * ((b : A) ^ 2 * k i)
        = (∏ j ∈ Finset.univ.erase i, (u j : A)) * ((u i : A) * ((b : A) ^ 2 * k i)) := by ring
      _ = (∏ j ∈ Finset.univ.erase i, (u j : A)) * ((u i : A) * (a * c i)) := by rw [hu i]
      _ = _ := by ring

end Spread

end Hironaka
