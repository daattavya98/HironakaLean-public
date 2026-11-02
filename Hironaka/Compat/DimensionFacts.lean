/-
Copyright (c) 2026 Daattavya Aggarwal, Minhyong Kim, Oisin Kim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daattavya Aggarwal, Minhyong Kim, Oisin Kim
-/
module

public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
public import Mathlib.RingTheory.KrullDimension.NonZeroDivisors
public import Architect
public import Hironaka.Compat.PermissibleCenterBlowdown
public import Hironaka.Statements

/-!
# Compatibility layer: dimension theory for the induction of Corollary 2 (Ch. III §8, p. 261)

> "We can assume that `dim(R̂/Q̂) = dim(R/Q)`. Now, the proof of Corollary 2 is done by induction on
> `dim(R/Q)`. […] Let us consider the case of `dim(R/Q) > 1`. We may again assume that `R` is
> complete. By the dimension assumption, we can find a prime ideal `Q'` in `R` such that `Q'`
> contains `Q` and `dim(R/Q') = 1`. […] Therefore, by the induction assumption, the flatness of
> `gr_{PR_Q}(R_Q/JR_Q)` over `R_Q/PR_Q` implies the same of `gr_{PR_{Q'}}(R_{Q'}/JR_{Q'})` over
> `R_{Q'}/PR_{Q'}`." (Proof of Corollary 2, p. 261)

The facts about dimensions used by the induction:

* `ringKrullDim_adicCompletion_quotient_eq` (cited leaf): `dim(R̂/QR̂) = dim(R/Q)`
  (`R̂/QR̂` is the completion of `R/Q`, whose dimension is that of `R/Q`; Samuel–Zariski, as
  footnote 3, p. 116, "The two chapters, VII and VIII, of Samuel-Zariski, [18], should cover all
  that
  we need from the theory of local rings");
* `exists_mem_minimalPrimes_ringKrullDim_quotient_eq_of_ideal`: a minimal prime `Q̂` of `QR̂` with
  `dim(R̂/Q̂) = dim(R̂/QR̂)` ("We can assume that `dim(R̂/Q̂) = dim(R/Q)`");
* `exists_prime_adjacent_maximalIdeal_of_ringKrullDim_quotient_eq`: "the dimension assumption" of
  the case `dim(R/Q) > 1`, with `dim(R_{Q'}/QR_{Q'}) < dim(R/Q)` so that the induction assumption
  applies to `R_{Q'}`;
* `exists_natCast_eq_ringKrullDim`: the dimension of a noetherian local ring is a natural number.
-/

@[expose] public section

open IsLocalRing

namespace Hironaka

universe u

section DimensionFacts


/-- Cited (p. 261: "We can assume that `dim(R̂/Q̂) = dim(R/Q)`"; footnote 3, p. 116: "The two
chapters,
VII and VIII, of Samuel-Zariski, [18], should cover all that we need from the theory of local
rings"): for a noetherian local ring `R` and an ideal `Q`, the ring `R̂/QR̂`, which is the
completion
of `R/Q`, has the same Krull dimension as `R/Q`.  Not proved in the paper (Zariski–Samuel,
*Commutative
Algebra II*, Ch. VII–VIII: the dimension of a local ring is that of its completion, `R̂/QR̂ =
(R/Q)^`);
Mathlib has no dimension theory of completions. -/
@[blueprint "lem:III.8-cor2-completion-dimension"
  (statement := /-- Let $R$ be a noetherian local ring, $\hat R$ its completion and $Q$ an ideal of
    $R$. Then $\dim(\hat R/Q\hat R)=\dim(R/Q)$. (Used on p.~261: ``We can assume that
    $\dim(\hat R/\hat Q)=\dim(R/Q)$''.) -/)
  (proof := /-- Cited, not proved in the paper: $\hat R/Q\hat R$ is the completion of $R/Q$
    (Zariski--Samuel, \emph{Commutative Algebra} II, Ch.~VII), and the dimension of a noetherian
    local ring is that of its completion (Ch.~VIII). Footnote~3 (p.~116): ``The two chapters, VII
    and VIII, of Samuel-Zariski, [18], should cover all that we need from the theory of local
    rings''. -/)
  (latexEnv := "lemma")]
theorem ringKrullDim_adicCompletion_quotient_eq [Hironaka.Cited.RingKrullDimAdicCompletionQuotientEq.{u}] :
    ∀ (R : Type u) [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] (Q : Ideal R),
    ringKrullDim (AdicCompletion (maximalIdeal R) R ⧸
      Q.map (algebraMap R (AdicCompletion (maximalIdeal R) R))) = ringKrullDim (R ⧸ Q) :=
  @Hironaka.Cited.RingKrullDimAdicCompletionQuotientEq.ringKrullDim_adicCompletion_quotient_eq _

/-- A noetherian local ring has finite Krull dimension, i.e. its dimension is a natural number. -/
theorem exists_natCast_eq_ringKrullDim (A : Type u) [CommRing A] [IsLocalRing A]
    [IsNoetherianRing A] : ∃ n : ℕ, ringKrullDim A = n := by
  obtain ⟨e, he⟩ := WithBot.ne_bot_iff_exists.mp (ringKrullDim_ne_bot (R := A))
  have hetop : e ≠ ⊤ := fun h => ringKrullDim_ne_top (R := A) (by rw [← he, h]; rfl)
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp hetop
  exact ⟨n, by rw [← he, ← hn]; rfl⟩

/-- **The prime `Q'` adjacent to the maximal ideal** (p. 261: "By the dimension assumption, we can
find a prime ideal `Q'` in `R` such that `Q'` contains `Q` and `dim(R/Q') = 1`"): for a prime `Q` of
a
noetherian local ring `R` with `dim(R/Q) = n ≥ 1` there is a prime `Q' ⊇ Q`, `Q' ≠ M`, with no prime
strictly between `Q'` and `M` (i.e. `dim(R/Q') = 1`), such that `R_{Q'}/QR_{Q'}` has dimension
`< n`.  No dimension theory beyond the definition is needed: `Q'/Q` is the last-but-one member of a
series of primes of length `n` between `Q/Q` and `M/Q`. -/
theorem exists_prime_adjacent_maximalIdeal_of_ringKrullDim_quotient_eq {R : Type u} [CommRing R]
    [IsLocalRing R] [IsNoetherianRing R] (Q : Ideal R) [Q.IsPrime] {n : ℕ} (hn : 1 ≤ n)
    (hdim : ringKrullDim (R ⧸ Q) = n) :
    ∃ (Q' : Ideal R) (_ : Q'.IsPrime), Q ≤ Q' ∧ Q' ≠ maximalIdeal R ∧
      (∀ p : Ideal R, p.IsPrime → Q' ≤ p → p = Q' ∨ p = maximalIdeal R) ∧
      ∃ n' : ℕ, n' < n ∧ ringKrullDim (Localization.AtPrime Q' ⧸
        Q.map (algebraMap R (Localization.AtPrime Q'))) = n' := by
  classical
  have _ : IsLocalRing (R ⧸ Q) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk Q) Ideal.Quotient.mk_surjective
  set A := R ⧸ Q with hA
  have hsurj : Function.Surjective (Ideal.Quotient.mk Q) := Ideal.Quotient.mk_surjective
  -- the closed point `⊤` of `Spec A` has height `n`
  have hhtM : Order.height (⊤ : PrimeSpectrum A) = n := by
    have h1 := IsLocalRing.maximalIdeal_height_eq_ringKrullDim (R := A)
    rw [hdim] at h1
    have h2 : (maximalIdeal A).height = n := by exact_mod_cast h1
    have h3 := PrimeSpectrum.height_eq_orderHeight (⊤ : PrimeSpectrum A)
    exact h3 ▸ h2
  obtain ⟨l, hl, hlen⟩ := Order.exists_series_of_height_eq_coe (⊤ : PrimeSpectrum A) hhtM
  have hl0 : l.length ≠ 0 := by omega
  set q : PrimeSpectrum A := l.eraseLast.last with hq
  have hqm : q < ⊤ := hl ▸ l.eraseLast_last_rel_last hl0
  -- no prime strictly between `q` and the closed point
  have hmin : ∀ r : PrimeSpectrum A, q ≤ r → r = q ∨ r = ⊤ := by
    intro r hqr
    by_contra hcon
    rw [not_or] at hcon
    have hqr' : q < r := lt_of_le_of_ne hqr (Ne.symm hcon.1)
    have hrm : r < ⊤ := lt_of_le_of_ne le_top hcon.2
    have hrm' : (l.eraseLast.snoc r hqr').last < ⊤ := by rw [RelSeries.last_snoc]; exact hrm
    have h1 := Order.length_le_height_last
      (p := (l.eraseLast.snoc r hqr').snoc (⊤ : PrimeSpectrum A) hrm')
    rw [RelSeries.last_snoc, hhtM] at h1
    simp only [RelSeries.snoc_length, RelSeries.eraseLast_length, hlen] at h1
    norm_cast at h1
    omega
  -- `ht q + 1 ≤ ht ⊤ = n`
  have hhq : Order.height q + 1 ≤ n := hhtM ▸ Order.height_add_one_le hqm
  obtain ⟨n', hn'⟩ : ∃ n' : ℕ, Order.height q = n' :=
    ENat.ne_top_iff_exists.mp (ne_of_lt (lt_of_le_of_lt (le_self_add.trans hhq)
      (ENat.natCast_lt_top n))) |>.imp fun m hm => hm.symm
  have hn'n : n' < n := by
    rw [hn'] at hhq
    have : n' + 1 ≤ n := by exact_mod_cast hhq
    omega
  -- transfer to `R`
  let Q' : Ideal R := q.asIdeal.comap (Ideal.Quotient.mk Q)
  have hQ'prime : Q'.IsPrime := Ideal.comap_isPrime _ _
  have hQQ' : Q ≤ Q' := by
    intro x hx
    show Ideal.Quotient.mk Q x ∈ q.asIdeal
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr hx]
    exact zero_mem _
  have hmapQ' : Q'.map (Ideal.Quotient.mk Q) = q.asIdeal :=
    Ideal.map_comap_of_surjective _ hsurj _
  refine ⟨Q', hQ'prime, hQQ', ?_, ?_, n', hn'n, ?_⟩
  · intro hQ'M
    have : q.asIdeal = maximalIdeal A := by
      rw [← hmapQ', hQ'M, IsLocalRing.map_maximalIdeal_of_surjective _ hsurj]
    exact absurd (PrimeSpectrum.ext this) hqm.ne
  · intro p hp hQ'p
    have hQp : Q ≤ p := hQQ'.trans hQ'p
    have hpm : (p.map (Ideal.Quotient.mk Q)).IsPrime :=
      Ideal.map_isPrime_of_surjective hsurj (by rw [Ideal.mk_ker]; exact hQp)
    have hqr : q ≤ (⟨p.map (Ideal.Quotient.mk Q), hpm⟩ : PrimeSpectrum A) := by
      show q.asIdeal ≤ p.map (Ideal.Quotient.mk Q)
      rw [← hmapQ']
      exact Ideal.map_mono hQ'p
    have hcomap : p = (p.map (Ideal.Quotient.mk Q)).comap (Ideal.Quotient.mk Q) := by
      rw [Ideal.comap_map_of_surjective _ hsurj, ← RingHom.ker_eq_comap_bot, Ideal.mk_ker]
      exact (sup_eq_left.mpr hQp).symm
    rcases hmin _ hqr with h | h
    · left
      have : p.map (Ideal.Quotient.mk Q) = q.asIdeal := congrArg PrimeSpectrum.asIdeal h
      rw [hcomap, this]
    · right
      have h' : p.map (Ideal.Quotient.mk Q) = maximalIdeal A := congrArg PrimeSpectrum.asIdeal h
      have hM : maximalIdeal A = (maximalIdeal R).map (Ideal.Quotient.mk Q) :=
        (IsLocalRing.map_maximalIdeal_of_surjective _ hsurj).symm
      rw [hcomap, h', hM, Ideal.comap_map_of_surjective _ hsurj, ← RingHom.ker_eq_comap_bot,
        Ideal.mk_ker]
      exact sup_eq_left.mpr (le_maximalIdeal (Ideal.IsPrime.ne_top ‹_›))
  · have : Q'.IsPrime := hQ'prime
    have : (Q'.map (Ideal.Quotient.mk Q)).IsPrime := hmapQ' ▸ q.isPrime
    obtain ⟨e, -⟩ := Ideal.exists_ringEquiv_localization_quotient_of_le Q Q' hQQ'
    rw [ringKrullDim_eq_of_ringEquiv e,
      IsLocalization.AtPrime.ringKrullDim_eq_height (Q'.map (Ideal.Quotient.mk Q))
        (Localization.AtPrime (Q'.map (Ideal.Quotient.mk Q))), hmapQ',
      PrimeSpectrum.height_eq_orderHeight q, hn']
    rfl

/-- `dim A` is attained at a minimal prime: for a nontrivial noetherian ring `A` there is a minimal
prime `p` with `dim(A/p) = dim A`.  (Every series of primes starts above a minimal prime `p` and so
lies in the set of primes containing `p`; there are finitely many minimal primes.) -/
theorem exists_mem_minimalPrimes_ringKrullDim_quotient_eq (A : Type u) [CommRing A]
    [IsNoetherianRing A] [Nontrivial A] :
    ∃ p ∈ minimalPrimes A, ringKrullDim (A ⧸ p) = ringKrullDim A := by
  classical
  -- `dim(A/p) = coheight p`
  have hcoh : ∀ p : PrimeSpectrum A, (Order.coheight p : WithBot ℕ∞) =
      ringKrullDim (A ⧸ p.asIdeal) := by
    intro p
    rw [Order.coheight_eq_krullDim_Ici, ringKrullDim_quotient]
    congr 2
  have hfin : (minimalPrimes A).Finite := minimalPrimes.finite_of_isNoetherianRing A
  have hne : (minimalPrimes A).Nonempty := by
    obtain ⟨m, hm⟩ := Ideal.exists_maximal A
    obtain ⟨p, hp, -⟩ := Ideal.exists_minimalPrimes_le (bot_le : (⊥ : Ideal A) ≤ m)
    exact ⟨p, hp⟩
  obtain ⟨p, hp, hpmax⟩ := Set.exists_max_image (minimalPrimes A)
    (fun p => ringKrullDim (A ⧸ p)) hfin hne
  have hlen : ∀ l : LTSeries (PrimeSpectrum A),
      (l.length : ℕ∞) ≤ Order.coheight (⟨p, hp.1.1⟩ : PrimeSpectrum A) := fun l => by
    obtain ⟨p₀, hp₀, hp₀le⟩ :=
      Ideal.exists_minimalPrimes_le (bot_le : (⊥ : Ideal A) ≤ l.head.asIdeal)
    have h1 : (l.length : ℕ∞) ≤ Order.coheight l.head := Order.length_le_coheight_head
    have h2 : Order.coheight l.head ≤ Order.coheight (⟨p₀, hp₀.1.1⟩ : PrimeSpectrum A) :=
      Order.coheight_anti hp₀le
    have h3 : (Order.coheight (⟨p₀, hp₀.1.1⟩ : PrimeSpectrum A) : WithBot ℕ∞) ≤
        (Order.coheight (⟨p, hp.1.1⟩ : PrimeSpectrum A) : WithBot ℕ∞) := by
      rw [hcoh, hcoh]
      exact hpmax p₀ hp₀
    exact h1.trans (h2.trans (by exact_mod_cast h3))
  refine ⟨p, hp, le_antisymm (ringKrullDim_quotient_le p) ?_⟩
  rw [← hcoh (⟨p, hp.1.1⟩ : PrimeSpectrum A), ringKrullDim, Order.krullDim_eq_iSup_length]
  exact_mod_cast iSup_le hlen

/-- **Choice of a minimal prime with the dimension of the quotient** (p. 261: "We can assume that
`dim(R̂/Q̂) = dim(R/Q)`"): for a proper ideal `I` of a noetherian ring `B` there is a minimal prime
`p` of `I` with `dim(B/p) = dim(B/I)`. -/
theorem exists_mem_minimalPrimes_ringKrullDim_quotient_eq_of_ideal {B : Type u} [CommRing B]
    [IsNoetherianRing B] (I : Ideal B) (hI : I ≠ ⊤) :
    ∃ p ∈ I.minimalPrimes, ringKrullDim (B ⧸ p) = ringKrullDim (B ⧸ I) := by
  have : Nontrivial (B ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr hI
  obtain ⟨p', hp', hdim⟩ := exists_mem_minimalPrimes_ringKrullDim_quotient_eq (B ⧸ I)
  have hp : p'.comap (Ideal.Quotient.mk I) ∈ I.minimalPrimes := by
    rw [Ideal.minimalPrimes_eq_comap]
    exact ⟨p', hp', rfl⟩
  refine ⟨_, hp, ?_⟩
  have hle : I ≤ p'.comap (Ideal.Quotient.mk I) := by
    intro x hx
    show Ideal.Quotient.mk I x ∈ p'
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr hx]
    exact zero_mem _
  have hmap : (p'.comap (Ideal.Quotient.mk I)).map (Ideal.Quotient.mk I) = p' :=
    Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective _
  rw [← hdim]
  refine ringKrullDim_eq_of_ringEquiv ?_
  refine (DoubleQuot.quotQuotEquivQuotOfLE hle).symm.trans ?_
  exact (Ideal.quotEquivOfEq hmap)

end DimensionFacts

end Hironaka
