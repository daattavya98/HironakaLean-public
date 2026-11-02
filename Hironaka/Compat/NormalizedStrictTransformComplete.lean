/-
Copyright (c) 2026 Daattavya Aggarwal, Minhyong Kim, Oisin Kim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daattavya Aggarwal, Minhyong Kim, Oisin Kim
-/
module

public import Hironaka.Compat.PartialFrames
public import Hironaka.Compat.TauOrderedFrame
public import Hironaka.Compat.NormalizedStandardBase
public import Hironaka.Compat.TauZMonotone
public import Hironaka.Statements

/-!
# The one-step theorem of Theorem 8 for complete `R = S{z₁, …, z_τ}` (Ch. III p. 264)

The proof of Theorem 8 (p. 264) treats one monoidal transform and, after "we may assume that `R`
is complete with respect to the topology defined by the powers of `(z₁, …, z_τ)R`, so that
`R = S{z₁, …, z_τ}`", proves by induction on the blocks `a`:

> Let `t = t(J)`, so that `τ = τ^{(t)}(J)`. Let `τ_a = τ^{(a)}(J)` for `1 ≤ a ≤ t`. Let `m_a` = the
> maximal integer such that `ν^{(m_a)}(J) = μ^{(a)}(J)` for `1 ≤ a ≤ t`. Let
> `S^{(a)} = S{z_{τ_a+1}, …, z_τ}`. Let `(S^{(a)}₁; w₁, …, w_{τ_a})` be the frame transform of
> `(S^{(a)}; z₁, …, z_{τ_a})` in `R₁` with the denominator `x`. We shall prove, by induction on `a`
> …, that `(g₁, …, g_{m_a})` can be extend to a standard base of `J₁`, that
> `τ_{(w)_a}(g₁, …, g_{m_a}) = 0` where `(w)_a = (w₁, …, w_{τ_a})`, and that
> `g_{m_a+1}, …, g_{m_{a+1}}` are all normalized by `(g₁, …, g_{m_a})` with respect to
> `(S^{(a)}₁; w₁, …, w_{τ_a})`. … the last assertion follows from the first two by Lemma 20 of §8. …
> Then the second assertion for `a` increased by `1` follows by virtue of
> Lemma 19 of §7. …

This file is that argument for `R = S⟦z₁, …, z_r⟧` with the frame `(S; z₁, …, z_r)`
(`RegularFrame.mvPowerSeries`), the partial frames `(S^{(a)}; z₁, …, z_{τ_a})` being
`RegularFrame.partialFrame` (`Compat/PartialFrames.lean`).  The reduction to this case is in
`Compat/NormalizedStrictTransform.lean`.
* `blockEnd`: the integers `m_a` ("the maximal integer such that `ν^{(m_a)}(J) = μ^{(a)}(J)`").
* `isNormalizedBy_partialFrameTransform_and_extends` (Lemma 20 for the partial frame
  `(S^{(a)}; z₁, …, z_{τ_a})`) and `initialForm_mem_adjoin_of_partialFrameTransform` (Lemma 19 for
  its frame transform `(S^{(a)}₁; w₁, …, w_{τ_a})`).
* `isNormalizedStandardBase_strictTransform_of_mvPowerSeries`: the induction on `a` and the
  conclusion.
-/

@[expose] public section

open IsLocalRing

namespace Hironaka

universe u

/-! ### The integers `m_a` -/

section BlockEnd

variable {R : Type u} [CommRing R] [IsRegularLocalRing R] (J : Ideal R)

theorem mu_mem_muSet' {a : ℕ} (ha : 1 ≤ a) (hat : a ≤ t R J) : mu R J a ∈ muSet R J := by
  have hf := (muSet_finite R J).1
  have hcard : hf.toFinset.card = t R J := (Set.ncard_eq_toFinset_card _ hf).symm
  exact Nat.nth_mem_of_lt_card (p := (· ∈ muSet R J)) hf (by rw [hcard]; omega)

theorem mu_lt_mu_succ {a : ℕ} (ha : 1 ≤ a) (hat : a < t R J) : mu R J a < mu R J (a + 1) := by
  have hf := (muSet_finite R J).1
  have hcard : hf.toFinset.card = t R J := (Set.ncard_eq_toFinset_card _ hf).symm
  have key := Nat.nth_strictMonoOn (p := (· ∈ muSet R J)) hf
  have h := key (Set.mem_Iio.mpr (show a - 1 < hf.toFinset.card by rw [hcard]; omega))
    (Set.mem_Iio.mpr (show a + 1 - 1 < hf.toFinset.card by rw [hcard]; omega)) (by omega)
  exact h

/-- An element of `μ*(J)` larger than `μ^{(a)}(J)` is at least `μ^{(a+1)}(J)`. -/
theorem mu_succ_le_of_mem_muSet {a : ℕ} (ha : 1 ≤ a) {μ : ℕ} (hμ : μ ∈ muSet R J)
    (h : mu R J a < μ) : mu R J (a + 1) ≤ μ := by
  by_contra hlt
  rw [not_le] at hlt
  have h1 : μ < Nat.nth (· ∈ muSet R J) (a - 1 + 1) := by
    have : mu R J (a + 1) = Nat.nth (· ∈ muSet R J) (a - 1 + 1) := by
      show Nat.nth _ (a + 1 - 1) = _
      congr 1
      omega
    omega
  have := Nat.le_nth_of_lt_nth_succ h1 hμ
  exact absurd h (not_lt.mpr this)

open Classical in
/-- **The integer `m_a`** (Theorem 7, p. 253, and Theorem 8, p. 264: "Let `m_a` = the maximal
integer such that `ν^{(m_a)}(J) = μ^{(a)}(J)`"), for a standard base with `m` members (all
`ν^{(n)}(J)`, `n > m`, are `∞`). -/
noncomputable def blockEnd (m a : ℕ) : ℕ :=
  Nat.findGreatest (fun k => ∃ h : 0 < k, nuI R J ⟨k, h⟩ = (mu R J a : ℕ∞)) m

variable {J}

theorem blockEnd_le (m a : ℕ) : blockEnd J m a ≤ m := Nat.findGreatest_le m

/-- `m_a ≥ 1`, `ν^{(m_a)}(J) = μ^{(a)}(J)`, and `m_a` is the largest such integer. -/
theorem blockEnd_spec {m : ℕ} {f : Fin m → R} (hf : IsStandardBase R J f) {a : ℕ} (ha : 1 ≤ a)
    (hat : a ≤ t R J) :
    ∃ h : 0 < blockEnd J m a, nuI R J ⟨blockEnd J m a, h⟩ = (mu R J a : ℕ∞) ∧
      ∀ n : ℕ+, nuI R J n = (mu R J a : ℕ∞) → (n : ℕ) ≤ blockEnd J m a := by
  classical
  obtain ⟨i, hi⟩ := mu_mem_muSet' J ha hat
  have him : (i : ℕ) ≤ m := by
    by_contra hlt
    rw [not_le] at hlt
    obtain ⟨-, htop⟩ := nuI_eq_of_hasLemma1Properties R J _ hf.2
    rw [htop i hlt] at hi
    exact ENat.top_ne_natCast _ hi
  have hP : ∃ h : 0 < (i : ℕ), nuI R J ⟨i, h⟩ = (mu R J a : ℕ∞) := ⟨i.pos, hi⟩
  have hle : (i : ℕ) ≤ blockEnd J m a := Nat.le_findGreatest him hP
  have hspec : ∃ h : 0 < blockEnd J m a, nuI R J ⟨blockEnd J m a, h⟩ = (mu R J a : ℕ∞) :=
    Nat.findGreatest_spec (P := fun k => ∃ h : 0 < k, nuI R J ⟨k, h⟩ = (mu R J a : ℕ∞)) him hP
  obtain ⟨hpos, heq⟩ := hspec
  refine ⟨hpos, heq, fun n hn => ?_⟩
  have hnm : (n : ℕ) ≤ m := by
    by_contra hlt
    rw [not_le] at hlt
    obtain ⟨-, htop⟩ := nuI_eq_of_hasLemma1Properties R J _ hf.2
    rw [htop n hlt] at hn
    exact ENat.top_ne_natCast _ hn
  exact Nat.le_findGreatest hnm ⟨n.pos, hn⟩

/-- The members `f₁, …, f_{m_a}` are those of order `≤ μ^{(a)}(J)`. -/
theorem lt_blockEnd_iff {m : ℕ} {f : Fin m → R} (hf : IsStandardBase R J f) {a : ℕ} (ha : 1 ≤ a)
    (hat : a ≤ t R J) (j : Fin m) :
    (j : ℕ) < blockEnd J m a ↔ Ideal.ordElem (maximalIdeal R) (f j) ≤ (mu R J a : ℕ∞) := by
  obtain ⟨hpos, heq, hmax⟩ := blockEnd_spec hf ha hat
  rw [ordElem_eq_nuI_of_isStandardBase J f hf j]
  constructor
  · intro hj
    rw [← heq]
    refine nuI_mono J ((PNat.coe_le_coe _ _).mp ?_)
    simp only [Nat.succPNat_coe, PNat.mk_coe]
    omega
  · intro hj
    by_contra hge
    rw [not_lt] at hge
    have h1 : nuI R J ⟨blockEnd J m a, hpos⟩ ≤ nuI R J (j : ℕ).succPNat :=
      nuI_mono J ((PNat.coe_le_coe _ _).mp (by simp only [Nat.succPNat_coe, PNat.mk_coe]; omega))
    rw [heq] at h1
    have := hmax _ (le_antisymm hj h1)
    simp only [Nat.succPNat_coe] at this
    omega

/-- `m_t = m`: every member has order `≤ μ^{(t)}(J)`. -/
theorem lt_blockEnd_t {m : ℕ} {f : Fin m → R} (hf : IsStandardBase R J f) (ht : 1 ≤ t R J)
    (j : Fin m) : (j : ℕ) < blockEnd J m (t R J) :=
  (lt_blockEnd_iff hf ht le_rfl j).mpr (ordElem_le_mu_t J hf j)

/-- `m_a < m_{a+1}` and `ν^{(m_a + 1)}(J) = μ^{(a+1)}(J)` for `a < t`. -/
theorem blockEnd_lt_and_nuI_succ {m : ℕ} {f : Fin m → R} (hf : IsStandardBase R J f) {a : ℕ}
    (ha : 1 ≤ a) (hat : a < t R J) :
    blockEnd J m a < blockEnd J m (a + 1) ∧
      nuI R J (blockEnd J m a).succPNat = (mu R J (a + 1) : ℕ∞) := by
  obtain ⟨hpos, heq, hmax⟩ := blockEnd_spec hf ha hat.le
  obtain ⟨hpos', heq', hmax'⟩ := blockEnd_spec hf (a := a + 1) (by omega) hat
  have hmu := mu_lt_mu_succ J ha hat
  have hlt : blockEnd J m a < blockEnd J m (a + 1) := by
    by_contra hge
    rw [not_lt] at hge
    have h1 : nuI R J ⟨blockEnd J m (a + 1), hpos'⟩ ≤ nuI R J ⟨blockEnd J m a, hpos⟩ :=
      nuI_mono J ((PNat.coe_le_coe _ _).mp hge)
    rw [heq, heq'] at h1
    exact absurd (by exact_mod_cast h1 : mu R J (a + 1) ≤ mu R J a) (not_le.mpr hmu)
  refine ⟨hlt, ?_⟩
  have hup : nuI R J (blockEnd J m a).succPNat ≤ (mu R J (a + 1) : ℕ∞) := by
    rw [← heq']
    exact nuI_mono J ((PNat.coe_le_coe _ _).mp
      (by simp only [Nat.succPNat_coe, PNat.mk_coe]; omega))
  have hlow : (mu R J a : ℕ∞) ≤ nuI R J (blockEnd J m a).succPNat := by
    rw [← heq]
    exact nuI_mono J ((PNat.coe_le_coe _ _).mp
      (by simp only [Nat.succPNat_coe, PNat.mk_coe]; omega))
  have hne : nuI R J (blockEnd J m a).succPNat ≠ (mu R J a : ℕ∞) := fun h => by
    have := hmax _ h
    simp only [Nat.succPNat_coe] at this
    omega
  obtain ⟨μ, hμ⟩ : ∃ μ : ℕ, nuI R J (blockEnd J m a).succPNat = μ := by
    have htop : nuI R J (blockEnd J m a).succPNat ≠ ⊤ := fun h => by
      rw [h] at hup
      exact absurd hup (by simp)
    exact ⟨_, (ENat.natCast_toNat htop).symm⟩
  rw [hμ] at hup hlow hne ⊢
  have hμmem : μ ∈ muSet R J := ⟨_, hμ⟩
  have h1 : mu R J a < μ := by
    have : mu R J a ≤ μ := by exact_mod_cast hlow
    have : mu R J a ≠ μ := fun h => hne (by rw [h])
    omega
  have := mu_succ_le_of_mem_muSet J ha hμmem h1
  have : μ ≤ mu R J (a + 1) := by exact_mod_cast hup
  exact_mod_cast le_antisymm ‹_› ‹_›

end BlockEnd

/-! ### Regular systems of `a`-th `τ`-parameters from a regular `τ`-frame -/

section TauPrefix

variable {R : Type u} [CommRing R] [IsRegularLocalRing R] {J : Ideal R}

open Classical in
/-- The members `z₁, …, z_{τ_a}` of a regular `τ`-frame for `J` form a regular system of `a`-th
`τ`-parameters for `J` (Definition 7, p. 222, and Definition 10). -/
theorem RegularFrame.IsRegularTauFrame.isRegularSystemOfTauParameters_prefix {F : RegularFrame R}
    (hF : F.IsRegularTauFrame J) {a : ℕ} (ha : 1 ≤ a) (hat : a ≤ t R J) :
    ∃ hle : tau R J a ≤ F.r, IsRegularSystemOfTauParameters R J a
      (fun i => ⟨F.z (Fin.castLE hle i), F.extends_rsop.mem_maximalIdeal
        (Finset.mem_image_of_mem _ (Finset.mem_univ _))⟩) := by
  obtain ⟨hτ, hz, hreg⟩ := hF
  have hale : tau R J a ≤ F.r := hτ ▸ tau_le_tau_of_le J ha hat le_rfl
  refine ⟨hale, fun b hb1 hba => ?_⟩
  have hbt : b ≤ t R J := hba.trans hat
  have hbalt : tau R J b ≤ tau R J a := tau_le_tau_of_le J hb1 hba hat
  have h1 := hreg b hb1 hbt
  convert h1 using 2
  ext y
  simp only [Set.mem_range]
  constructor
  · rintro ⟨⟨i, hi⟩, rfl⟩
    refine ⟨⟨⟨i, hτ ▸ lt_of_lt_of_le i.2 hale⟩, hi⟩, ?_⟩
    rfl
  · rintro ⟨⟨i, hi⟩, rfl⟩
    refine ⟨⟨⟨i, lt_of_lt_of_le hi hbalt⟩, hi⟩, ?_⟩
    rfl

end TauPrefix

/-! ### Lemma 20 for the partial frames and Lemma 19 for their frame transforms -/

/-- Normalization by `(f₁, …, f_j)` implies normalization by `(f₁, …, f_i)`, `i ≤ j` (the `E`-set
of the smaller system is contained in that of the larger one). -/
theorem RegularFrame.IsNormalizedBy.prefix_castLE {R : Type u} [CommRing R] [IsRegularLocalRing R]
    (F : RegularFrame R) {m : ℕ} (f : Fin m → R) {i j : ℕ} (hi : i ≤ m) (hj : j ≤ m)
    (hij : i ≤ j) {g : R} (h : F.IsNormalizedBy (fun l : Fin j => f (Fin.castLE hj l)) g) :
    F.IsNormalizedBy (fun l : Fin i => f (Fin.castLE hi l)) g := by
  intro e he A hA
  refine h e he A (eSet_mono ?_ hA)
  unfold frameInitialIdeal
  refine Ideal.span_mono ?_
  rintro ψ ⟨l, hl⟩
  exact ⟨Fin.castLE hij l, by rw [hl]; exact congrArg _ (congrArg f (Fin.ext rfl))⟩

section Steps

variable {S : Type u} [CommRing S] [IsRegularLocalRing S] {r : ℕ}

/-- **Lemma 20 of §8 for the partial frame `(S^{(a)}; z₁, …, z_{τ_a})`** (p. 264: "For an
arbitrary `a ≥ 1`, the last assertion follows from the first two by Lemma 20 of §8. This lemma also
shows that …"): for the partial frame `(S{z_{p+1}, …, z_r}; z₁, …, z_p)` of `R = S{z}` and its
frame transform `(S^{(a)}₁; w₁, …, w_p)` in `R₁` with the denominator `x`, if the initial forms of
`f₁, …, f_i` lie in `k[Z₁, …, Z_p]`, those of `g₁, …, g_i` in `k[W₁, …, W_p]` (i.e.
`τ_{(z)_a}(f_l) = 0`, `τ_{(w)_a}(g_l) = 0`), `ν_{M₁}(g_l) = ν^{(l)}(J)` for `l ≤ i`, and
`ν^{(j)}(J) = ν^{(i+1)}(J)` for some `j > i`, then `g_j` is normalized by `(g₁, …, g_i)` with
respect to `(S^{(a)}₁; w₁, …, w_p)` and `(g₁, …, g_i, g_j)` can be extended to a standard base of
`J₁`.  The hypotheses (1)–(10) of Lemma 20 for the partial frame: (1) by the choice of `j`
(`extendsToStandardBase_snoc`); (2) from `k[Z₁, …, Z_p]`; (3) Remarks 1 and 2 of §7
(`RegularFrame.isNormalizedBy_partialFrame`) from the normalization of `f_j` with respect to
`(S; z)`; (5) `(z₁, …, z_p)R ⊆ (z)R ⊆ P`; the denominator `x ∈ S ⊆ S^{(a)}`. -/
theorem isNormalizedBy_partialFrameTransform_and_extends [Hironaka.HironakaCitedResults.{u}]
    (J : Ideal (MvPowerSeries (Fin r) S)) (Q : Ideal (MvPowerSeries (Fin r) S)) [Q.IsPrime]
    (hQperm : IsPermissibleCenter _ J Q) (hzQ : (RegularFrame.mvPowerSeries S r).idealZ ≤ Q)
    (T : MonoidalTransform _ Q) [IsLocalHom T.toRing] [IsRegularLocalRing T.ring]
    (hsep : RingHom.IsResiduallySeparableAlgebraic (R := MvPowerSeries (Fin r) S) (R' := T.ring)
      T.toRing)
    (x : (RegularFrame.mvPowerSeries S r).S)
    (hxQ : algebraMap _ (MvPowerSeries (Fin r) S) x ∈ Q)
    (hx : Q.map T.toRing = Ideal.span {T.toRing (algebraMap _ (MvPowerSeries (Fin r) S) x)})
    {m : ℕ} (f : Fin m → MvPowerSeries (Fin r) S)
    (hf : (RegularFrame.mvPowerSeries S r).IsNormalizedStandardBase J f)
    (hfQ : ∀ j : Fin m, Ideal.ordElem Q (f j) = nuI _ J (j : ℕ).succPNat)
    (ν : Fin m → ℕ) (hν : ∀ j, (ν j : ℕ∞) = nuI _ J (j : ℕ).succPNat)
    (g : Fin m → T.ring)
    (hg : ∀ j, T.toRing (algebraMap _ (MvPowerSeries (Fin r) S) x) ^ ν j * g j = T.toRing (f j))
    (hnuI : ∀ i, nuI T.ring (strictTransformIdeal T J) i = nuI _ J i)
    {p : ℕ} (hp : p ≤ r) (FTp : (RegularFrame.partialFrame S r p hp).FrameTransform T)
    (hFTpx : FTp.x = T.toRing (algebraMap _ (MvPowerSeries (Fin r) S) x))
    {i : ℕ} (hi : i ≤ m)
    (hfi : ∀ l : Fin m, (l : ℕ) < i → initialForm (maximalIdeal _) (f l) ∈
      (RegularFrame.partialFrame S r p hp).assocSubalgebra)
    (hgi : ∀ l : Fin m, (l : ℕ) < i → initialForm (maximalIdeal T.ring) (g l) ∈
      FTp.toRegularFrame.assocSubalgebra)
    (hgo : ∀ l : Fin m, (l : ℕ) < i →
      Ideal.ordElem (maximalIdeal T.ring) (g l) = nuI _ J (l : ℕ).succPNat)
    (j : Fin m) (hij : i ≤ j) (hνj : nuI _ J (j : ℕ).succPNat = nuI _ J i.succPNat) :
    FTp.toRegularFrame.IsNormalizedBy (fun l : Fin i => g (Fin.castLE hi l)) (g j) ∧
      ExtendsToStandardBase (strictTransformIdeal T J)
        (Fin.snoc (fun l : Fin i => g (Fin.castLE hi l)) (g j) : Fin (i + 1) → T.ring) := by
  classical
  have hC := RegularFrame.partialFrame_algebraMap_C (S := S) r p hp x
  have hord : ∀ l : Fin m, Ideal.ordElem (maximalIdeal _) (f l) = nuI _ J (l : ℕ).succPNat :=
    fun l => ordElem_eq_nuI_of_isStandardBase J f hf.1 l
  -- (1): `(f₁, …, f_i, f_j)` can be extended to a standard base of `J`
  have h1 : ExtendsToStandardBase J (Fin.snoc (fun l : Fin i => f (Fin.castLE hi l)) (f j) :
      Fin (i + 1) → MvPowerSeries (Fin r) S) := by
    refine extendsToStandardBase_snoc J _ (f j) ⟨m, f, hi, hf.1, fun l => rfl⟩ (hf.1.1 j) (ν j)
      (by rw [hord j, hν j]) (fun l => ?_) (by rw [hν j, hνj]) ?_
    · rw [hord, hν j]
      exact nuI_mono J ((PNat.coe_le_coe _ _).mp (by
        simp only [Nat.succPNat_coe, Fin.val_castLE]; omega))
    · intro hmem
      apply hf.1.2.2.2.2 j
      refine Ideal.span_mono ?_ hmem
      rintro _ ⟨l, rfl⟩
      exact ⟨Fin.castLE hij l, rfl⟩
  -- the data for Lemma 20 for the partial frame
  set f₀ : Fin i → MvPowerSeries (Fin r) S := fun l => f (Fin.castLE hi l) with hf₀
  set g₀ : Fin i → T.ring := fun l => g (Fin.castLE hi l) with hg₀
  set ν' : Fin (i + 1) → ℕ := Fin.snoc (fun l : Fin i => ν (Fin.castLE hi l)) (ν j) with hν'
  have hν'cast : ∀ l : Fin i, ν' l.castSucc = ν (Fin.castLE hi l) := fun l => by
    rw [hν', Fin.snoc_castSucc]
  have hν'last : ν' (Fin.last i) = ν j := by rw [hν', Fin.snoc_last]
  have h2 : ∀ l : Fin i, tauZ _ (RegularFrame.partialFrame S r p hp).z (fun _ : Fin 1 => f₀ l) = 0 := fun l =>
    (RegularFrame.partialFrame S r p hp).tauZ_eq_zero_of_initialForm_mem _ (hfi _ l.2)
  have h3' : (RegularFrame.mvPowerSeries S r).IsNormalizedBy f₀ (f j) :=
    RegularFrame.IsNormalizedBy.prefix_castLE _ f hi j.2.le hij (hf.2.2 j)
  have hfi' : ∀ l : Fin i, initialForm (maximalIdeal _) (f₀ l) ∈ (RegularFrame.partialFrame S r p hp).assocSubalgebra :=
    fun l => hfi _ l.2
  have h3 : (RegularFrame.partialFrame S r p hp).IsNormalizedBy f₀ (f j) :=
    RegularFrame.isNormalizedBy_partialFrame r p hp f₀ (f j) hfi' h3'
  have h5 : (RegularFrame.partialFrame S r p hp).idealZ ≤ Q := by
    rw [RegularFrame.idealZ, Ideal.span_le]
    rintro _ ⟨l, rfl⟩
    rw [SetLike.mem_coe, RegularFrame.partialFrame_z]
    exact hzQ (Ideal.subset_span ⟨_, rfl⟩)
  have h6 : ∀ l : Fin i, Ideal.ordElem Q (f₀ l) = nuI _ J (l : ℕ).succPNat := fun l => hfQ _
  have h6' : Ideal.ordElem Q (f j) = nuI _ J i.succPNat := by rw [hfQ j, hνj]
  have hxP : algebraMap (RegularFrame.partialFrame S r p hp).S (MvPowerSeries (Fin r) S) (MvPowerSeries.C x) ∈ Q := by
    rw [hC]; exact hxQ
  have h7 : Q.map T.toRing = Ideal.span {T.toRing (algebraMap (RegularFrame.partialFrame S r p hp).S (MvPowerSeries (Fin r) S)
      (MvPowerSeries.C x))} := by
    rw [hC]; exact hx
  have h7' : FTp.x = T.toRing (algebraMap (RegularFrame.partialFrame S r p hp).S _ (MvPowerSeries.C x)) := by
    rw [hC]; exact hFTpx
  have hν₀ : ∀ l : Fin (i + 1), (ν' l : ℕ∞) = nuI _ J (l : ℕ).succPNat := by
    intro l
    refine Fin.lastCases ?_ (fun l => ?_) l
    · rw [hν'last, hν j, hνj]
      rfl
    · rw [hν'cast, hν]
      rfl
  have hg₀ : ∀ l : Fin i, T.toRing (algebraMap (RegularFrame.partialFrame S r p hp).S _ (MvPowerSeries.C x))
      ^ ν' l.castSucc * g₀ l = T.toRing (f₀ l) := fun l => by
    rw [hC, hν'cast]; exact hg _
  have h8 : ∀ l : Fin i, tauZ T.ring FTp.w (fun _ : Fin 1 => g₀ l) = 0 := fun l =>
    FTp.toRegularFrame.tauZ_eq_zero_of_initialForm_mem _ (hgi _ l.2)
  have h9 : ∀ l : Fin i, Ideal.ordElem (maximalIdeal T.ring) (g₀ l) =
      nuI _ J (l : ℕ).succPNat := fun l => hgo _ l.2
  have hg' : T.toRing (algebraMap (RegularFrame.partialFrame S r p hp).S _ (MvPowerSeries.C x))
      ^ ν' (Fin.last i) * g j = T.toRing (f j) := by
    rw [hC, hν'last]; exact hg j
  obtain ⟨hN, hE⟩ := isNormalizedBy_frameTransform_and_extendsToStandardBase J
    (RegularFrame.partialFrame S r p hp) f₀ (f j)
    (fun l => hf.1.1 _) (hf.1.1 j) h1 h2 h3 Q hQperm h5 h6 h6' T hsep (MvPowerSeries.C x) hxP h7
    FTp h7' ν' hν₀ g₀ hg₀ h8 h9 (g j) hg'
  exact ⟨hN, hE fun k _ => hnuI k⟩

/-- **Lemma 19 of §7 for the frame transform `(S^{(a)}₁; w₁, …, w_{τ_a})` of the partial frame**
(p. 265: "Then the second assertion for `a` increased by `1` follows by virtue of Lemma 19 of §7"):
if `τ_{(w)_a}(g_l) = 0` for `l ≤ i`, `μ^{(b)}(J₁) = ν^{(i+1)}(J₁)` with `p ≤ τ^{(b)}(J₁)`,
`(g₁, …, g_i, g_j)` can be extended to a standard base of `J₁` and `g_j` is normalized by
`(g₁, …, g_i)` with respect to `(S^{(a)}₁; w₁, …, w_p)`, then the initial form of `g_j` lies in
`k[W₁, …, W_{τ^{(b)}}]`.  Lemma 19 gives `k[T*]`, `T*` generated by a regular system of `b`-th
`τ`-parameters of `J₁` and `W₁, …, W_p`; for the regular `τ`-frame `(S₁; w₁, …, w_τ)` of `R₁` for
`J₁` the system `(w₁, …, w_{τ^{(b)}})` is one, so `T*` is spanned by `W₁, …, W_{τ^{(b)}}`. -/
theorem initialForm_mem_adjoin_of_partialFrameTransform {Q : Ideal (MvPowerSeries (Fin r) S)}
    {T : MonoidalTransform _ Q} [IsRegularLocalRing T.ring] (J₁ : Ideal T.ring)
    (FT : (RegularFrame.mvPowerSeries S r).FrameTransform T)
    (hF₁ : FT.toRegularFrame.IsRegularTauFrame J₁)
    {p : ℕ} (hp : p ≤ r) (FTp : (RegularFrame.partialFrame S r p hp).FrameTransform T)
    (hFTpw : ∀ l, FTp.w l = FT.w (Fin.castLE (RegularFrame.partialFrame_r_le r p hp) l))
    {m : ℕ} (g : Fin m → T.ring) (hgJ : ∀ l, g l ∈ J₁) {i : ℕ} (hi : i ≤ m)
    (hgi : ∀ l : Fin m, (l : ℕ) < i → initialForm (maximalIdeal T.ring) (g l) ∈
      FTp.toRegularFrame.assocSubalgebra)
    (b : ℕ) (hb : 1 ≤ b) (hbt : b ≤ t T.ring J₁) (hpb : p ≤ tau T.ring J₁ b)
    (hmu : (mu T.ring J₁ b : ℕ∞) = nuI T.ring J₁ i.succPNat) (j : Fin m)
    (h1 : ExtendsToStandardBase J₁
      (Fin.snoc (fun l : Fin i => g (Fin.castLE hi l)) (g j) : Fin (i + 1) → T.ring))
    (h2 : FTp.toRegularFrame.IsNormalizedBy (fun l : Fin i => g (Fin.castLE hi l)) (g j)) :
    initialForm (maximalIdeal T.ring) (g j) ∈ Algebra.adjoin (T.ring ⧸ maximalIdeal T.ring)
      (Set.range fun q : {q : Fin FT.toRegularFrame.r // (q : ℕ) < tau T.ring J₁ b} =>
        frameForm FT.w q.1) := by
  classical
  obtain ⟨hle, hxs⟩ := hF₁.isRegularSystemOfTauParameters_prefix hb hbt
  have h := initialForm_mem_adjoin_of_isNormalizedBy FTp.toRegularFrame J₁
    (fun l : Fin i => g (Fin.castLE hi l)) (fun l => hgJ _)
    (fun l => FTp.toRegularFrame.tauZ_eq_zero_of_initialForm_mem _ (hgi _ l.2)) (g j) (hgJ j)
    b (by omega) hmu h1 h2 _ hxs
  rw [tauParamsSubmoduleStar, Algebra.adjoin_span] at h
  refine Algebra.adjoin_mono ?_ h
  have hord : ∀ k, Ideal.ordElem (maximalIdeal T.ring) (FT.w k) = 1 := fun k =>
    ordElem_maximalIdeal_eq_one_of_mem_extendsToRSOP FT.extends_rsop
      (Finset.mem_image_of_mem _ (Finset.mem_univ k))
  rintro _ (⟨l, rfl⟩ | ⟨l, rfl⟩)
  · refine ⟨⟨Fin.castLE hle l, l.2⟩, ?_⟩
    show initialForm _ (FT.w (Fin.castLE hle l)) = _
    rw [initialForm_eq_mk _ (hord _)]
    rfl
  · refine ⟨⟨Fin.castLE (RegularFrame.partialFrame_r_le (S := S) r p hp) l,
      lt_of_lt_of_le l.2 hpb⟩, ?_⟩
    exact congrArg (initialForm (maximalIdeal T.ring)) (hFTpw l).symm

end Steps

/-! ### Auxiliary facts for the induction on `a` -/

section Aux

variable {A : Type u} [CommRing A] [IsRegularLocalRing A]

/-- The members of a system which can be extended to a standard base have the orders
`ν^{(l)}(J)`. -/
theorem ExtendsToStandardBase.ordElem_eq {J : Ideal A} {n : ℕ} {s : Fin n → A}
    (h : ExtendsToStandardBase J s) (l : Fin n) :
    Ideal.ordElem (maximalIdeal A) (s l) = nuI A J (l : ℕ).succPNat := by
  obtain ⟨m₂, G, him, hG, hGf⟩ := h
  rw [← hGf l, ordElem_eq_nuI_of_isStandardBase J G hG]
  rfl

/-- `(g₁, …, g_k, g_{k+1})` written as `(g₁, …, g_{k+1})`. -/
theorem ExtendsToStandardBase.of_snoc_castLE {J : Ideal A} {m : ℕ} {G : Fin m → A} (k : Fin m)
    (h : ExtendsToStandardBase J (Fin.snoc (fun l : Fin k => G (Fin.castLE k.2.le l)) (G k) :
      Fin ((k : ℕ) + 1) → A)) {n : ℕ} (hn : n = (k : ℕ) + 1) (hnm : n ≤ m) :
    ExtendsToStandardBase J (fun l : Fin n => G (Fin.castLE hnm l)) := by
  subst hn
  obtain ⟨m₂, G', him, hG', hGf⟩ := h
  refine ⟨m₂, G', him, hG', fun l => ?_⟩
  refine Fin.lastCases ?_ (fun l => ?_) l
  · have := hGf (Fin.last _)
    rw [Fin.snoc_last] at this
    rw [this]
    exact congrArg G (Fin.ext rfl)
  · have := hGf l.castSucc
    rw [Fin.snoc_castSucc] at this
    rw [this]
    exact congrArg G (Fin.ext rfl)

/-- `μ^{(1)}(J)` is the least element of `μ*(J)`. -/
theorem mu_one_le_of_mem_muSet {J : Ideal A} {μ : ℕ} (hμ : μ ∈ muSet A J) : mu A J 1 ≤ μ := by
  show Nat.nth (· ∈ muSet A J) (1 - 1) ≤ μ
  rw [Nat.sub_self, Nat.nth_zero]
  exact Nat.sInf_le hμ

/-- `k[Z₁, …, Z_k]` for a system `(z₁, …, z_n)` (the `k`-subalgebra of `gr_M(A)` generated by the
initial forms of the `z_q` with `q < k`). -/
noncomputable def framePrefixSubalgebra {n : ℕ} (z : Fin n → A) (k : ℕ) :
    Subalgebra (A ⧸ maximalIdeal A) (AssocGraded (maximalIdeal A)) :=
  Algebra.adjoin (A ⧸ maximalIdeal A) (Set.range fun q : {q : Fin n // (q : ℕ) < k} =>
    frameForm z q.1)

theorem framePrefixSubalgebra_mono {n : ℕ} (z : Fin n → A) {k k' : ℕ} (h : k ≤ k') :
    framePrefixSubalgebra z k ≤ framePrefixSubalgebra z k' := by
  refine Algebra.adjoin_mono ?_
  rintro _ ⟨⟨q, hq⟩, rfl⟩
  exact ⟨⟨q, lt_of_lt_of_le hq h⟩, rfl⟩

theorem framePrefixSubalgebra_le_assocSubalgebra {n : ℕ} (z : Fin n → A) (k : ℕ) :
    framePrefixSubalgebra z k ≤ Hironaka.assocSubalgebra z := by
  refine Algebra.adjoin_mono ?_
  rintro _ ⟨⟨q, -⟩, rfl⟩
  exact ⟨q, rfl⟩

/-- For a system `z'` consisting of the first `p` members of `z`, `k[Z'] = k[Z₁, …, Z_p]`. -/
theorem assocSubalgebra_eq_framePrefixSubalgebra {n p : ℕ} (z : Fin n → A) (z' : Fin p → A)
    (hp : p ≤ n) (hz : ∀ l, z' l = z (Fin.castLE hp l)) :
    Hironaka.assocSubalgebra z' = framePrefixSubalgebra z p := by
  refine le_antisymm (Algebra.adjoin_mono ?_) (Algebra.adjoin_mono ?_)
  · rintro _ ⟨l, rfl⟩
    exact ⟨⟨Fin.castLE hp l, l.2⟩, by simp only [frameForm, hz]⟩
  · rintro _ ⟨⟨q, hq⟩, rfl⟩
    exact ⟨⟨q, hq⟩, by simp only [frameForm, hz]; rfl⟩

/-- Only `q < n` matter: `k[Z₁, …, Z_{min(k, n)}] = k[Z₁, …, Z_k]`. -/
theorem framePrefixSubalgebra_min {n : ℕ} (z : Fin n → A) (k : ℕ) :
    framePrefixSubalgebra z (min k n) = framePrefixSubalgebra z k := by
  refine le_antisymm (framePrefixSubalgebra_mono z (min_le_left _ _)) (Algebra.adjoin_mono ?_)
  rintro _ ⟨⟨q, hq⟩, rfl⟩
  exact ⟨⟨q, lt_min hq q.2⟩, rfl⟩

end Aux

/-! ### Theorem 7 (p. 253) for complete `R = S{z₁, …, z_r}`

"First of all, `R` may be assumed to be complete with respect to the topology defined by the powers
of `(z₁, …, z_r)R`.  Hence `R = S{z₁, …, z_r}`.  We shall prove the assertion of the theorem by
induction on `a`."  The reduction is `initialForm_mem_adjoin_of_isNormalizedStandardBase`
(`Compat/FrameTheorem7.lean`); here is the complete case, with the partial frames
`(S_a; z₁, …, z_{τ_a})` of `Compat/PartialFrames.lean` and Lemma 19. -/

section Theorem7Complete

variable {S : Type u} [CommRing S] [IsRegularLocalRing S] {r : ℕ}

/-- `ν^{(1)}(J) = μ^{(1)}(J)` as soon as `ν^{(m_1)}(J) = μ^{(1)}(J)` for some `m_1`: `μ^{(1)}(J)` is the
least element of `μ*(J)`, which contains `ν^{(1)}(J)` when that is finite, and
`ν^{(1)}(J) ≤ ν^{(m_1)}(J)`. -/
theorem nuI_one_eq_mu_one {R : Type u} [CommRing R] [IsRegularLocalRing R] {J : Ideal R} {n : ℕ+}
    (hn : nuI R J n = (mu R J 1 : ℕ∞)) : nuI R J 1 = (mu R J 1 : ℕ∞) := by
  have hle : nuI R J 1 ≤ (mu R J 1 : ℕ∞) := hn ▸ nuI_mono J one_le
  obtain ⟨μ, hμ⟩ : ∃ μ : ℕ, nuI R J 1 = μ := by
    have htop : nuI R J 1 ≠ ⊤ := fun h => by
      rw [h] at hle
      exact absurd hle (by simp)
    exact ⟨_, (ENat.natCast_toNat htop).symm⟩
  have h1 : mu R J 1 ≤ μ := mu_one_le_of_mem_muSet ⟨_, hμ⟩
  rw [hμ] at hle ⊢
  exact_mod_cast le_antisymm (by exact_mod_cast hle) h1

/-- **The inductive step of Theorem 7** (p. 253): "(f₁, …, f_{m_a}, f_{m_a+j}) can be extended to a
standard base of `J`.  Moreover, `f_{m_a+j}` is normalized by `(f₁, …, f_{m_a})` with respect to
`(S; z₁, …, z_r)` and therefore, in view of Remarks 1 and 2, `f_{m_a+j}` is normalized by
`(f₁, …, f_{m_a})` with respect to `(S_a; z₁, …, z_{τ_a})`.  Therefore, by Lemma 19, the initial form
of `f_{m_a+j}` belongs to the `k`-subalgebra generated by the initial forms of `z₁, …, z_{τ_{a+1}}`",
for the partial frame `(S_a; z₁, …, z_p)` (`RegularFrame.partialFrame`, `p = τ_a`) of the complete
`R = S⟦z₁, …, z_r⟧`.  Here `i = m_a`, `b = a + 1`, and `j` is a member of the block of `b`:
`ν^{(j+1)}(J) = ν^{(i+1)}(J) = μ^{(b)}(J)`.  Gaps filled: the extension to a standard base
(`extendsToStandardBase_snoc`), and that `T*` of Lemma 19, generated by a regular system of
`b`-th `τ`-parameters (here `z₁, …, z_{τ_b}`, `isRegularSystemOfTauParameters_prefix`) and
`Z₁, …, Z_p` (`p ≤ τ_b`), lies in `k[Z₁, …, Z_{τ_b}]`. -/
theorem initialForm_mem_framePrefixSubalgebra_of_partialFrame
    (J : Ideal (MvPowerSeries (Fin r) S))
    (hF : (RegularFrame.mvPowerSeries S r).IsRegularTauFrame J)
    {m : ℕ} (f : Fin m → MvPowerSeries (Fin r) S)
    (hf : (RegularFrame.mvPowerSeries S r).IsNormalizedStandardBase J f)
    {b : ℕ} (hb : 1 ≤ b) (hbt : b ≤ t _ J) {p : ℕ} (hp : p ≤ r) (hpb : p ≤ tau _ J b)
    {i : ℕ} (hi : i ≤ m)
    (hfi : ∀ l : Fin m, (l : ℕ) < i → initialForm (maximalIdeal _) (f l) ∈
      framePrefixSubalgebra (RegularFrame.mvPowerSeries S r).z p)
    (hmu : (mu _ J b : ℕ∞) = nuI _ J i.succPNat)
    (j : Fin m) (hij : i ≤ j) (hνj : nuI _ J (j : ℕ).succPNat = nuI _ J i.succPNat) :
    initialForm (maximalIdeal _) (f j) ∈
      framePrefixSubalgebra (RegularFrame.mvPowerSeries S r).z (tau _ J b) := by
  classical
  have hassoc : (RegularFrame.partialFrame S r p hp).assocSubalgebra =
      framePrefixSubalgebra (RegularFrame.mvPowerSeries S r).z p := by
    rw [RegularFrame.assocSubalgebra]
    exact assocSubalgebra_eq_framePrefixSubalgebra _ _ _ (RegularFrame.partialFrame_z r p hp)
  have hord : ∀ l : Fin m, Ideal.ordElem (maximalIdeal _) (f l) = nuI _ J (l : ℕ).succPNat :=
    fun l => ordElem_eq_nuI_of_isStandardBase J f hf.1 l
  set f₀ : Fin i → MvPowerSeries (Fin r) S := fun l => f (Fin.castLE hi l) with hf₀
  have hfi' : ∀ l : Fin i, initialForm (maximalIdeal _) (f₀ l) ∈
      (RegularFrame.partialFrame S r p hp).assocSubalgebra := fun l => by
    rw [hassoc]
    exact hfi _ l.2
  -- hypothesis (i) of Lemma 19: "`(f₁, …, f_{m_a}, f_{m_a+j})` can be extended to a standard base"
  have hμj : Ideal.ordElem (maximalIdeal _) (f j) = ((mu _ J b : ℕ) : ℕ∞) := by
    rw [hord j, hνj, hmu]
  have h1 : ExtendsToStandardBase J (Fin.snoc f₀ (f j) : Fin (i + 1) → MvPowerSeries (Fin r) S) := by
    refine extendsToStandardBase_snoc J _ (f j) ⟨m, f, hi, hf.1, fun l => rfl⟩ (hf.1.1 j)
      (mu _ J b) hμj (fun l => ?_) hmu.le ?_
    · rw [hf₀, hord]
      rw [← hmu, ← hνj] at *
      exact nuI_mono J ((PNat.coe_le_coe _ _).mp (by
        simp only [Nat.succPNat_coe, Fin.val_castLE]; omega))
    · intro hmem
      apply hf.1.2.2.2.2 j
      refine Ideal.span_mono ?_ hmem
      rintro _ ⟨l, rfl⟩
      exact ⟨Fin.castLE hij l, rfl⟩
  -- hypothesis (ii): Remarks 1 and 2
  have h3' : (RegularFrame.mvPowerSeries S r).IsNormalizedBy f₀ (f j) :=
    RegularFrame.IsNormalizedBy.prefix_castLE _ f hi j.2.le hij (hf.2.2 j)
  have h2 : (RegularFrame.partialFrame S r p hp).IsNormalizedBy f₀ (f j) :=
    RegularFrame.isNormalizedBy_partialFrame r p hp f₀ (f j) hfi' h3'
  -- Lemma 19 for the partial frame
  obtain ⟨hle, hxs⟩ := hF.isRegularSystemOfTauParameters_prefix hb hbt
  have h := initialForm_mem_adjoin_of_isNormalizedBy (RegularFrame.partialFrame S r p hp) J f₀
    (fun l => hf.1.1 _)
    (fun l => (RegularFrame.partialFrame S r p hp).tauZ_eq_zero_of_initialForm_mem _ (hfi' l))
    (f j) (hf.1.1 j) b (by omega) hmu h1 h2 _ hxs
  rw [tauParamsSubmoduleStar, Algebra.adjoin_span] at h
  refine Algebra.adjoin_mono ?_ h
  have hord1 : ∀ k, Ideal.ordElem (maximalIdeal _) ((RegularFrame.mvPowerSeries S r).z k) = 1 :=
    fun k => ordElem_maximalIdeal_eq_one_of_mem_extendsToRSOP
      (RegularFrame.mvPowerSeries S r).extends_rsop
      (Finset.mem_image_of_mem _ (Finset.mem_univ k))
  rintro _ (⟨l, rfl⟩ | ⟨l, rfl⟩)
  · refine ⟨⟨Fin.castLE hle l, l.2⟩, ?_⟩
    show frameForm _ (Fin.castLE hle l) = _
    rw [frameForm, initialForm_eq_mk _ (hord1 _)]
    rfl
  · refine ⟨⟨Fin.castLE (RegularFrame.partialFrame_r_le (S := S) r p hp) l,
      lt_of_lt_of_le l.2 hpb⟩, ?_⟩
    exact (congrArg (initialForm (maximalIdeal _)) (RegularFrame.partialFrame_z r p hp l)).symm

/-- **Theorem 7 (p. 253) for complete `R = S{z₁, …, z_r}`**, by the printed induction on `a`: the
initial forms of `f₁, …, f_{m_a}` lie in `k[Z₁, …, Z_{τ_a}]`.  For `a = 1` the paper says "the
assertion is clear from the definition of a regular system of `τ`-parameters"; here it is the same
step as the others, with the empty system `(f_i)_{i < 0}` and the empty partial frame `p = 0`
(Lemma 19 with `i = 0`).  For `a → a + 1`: the step
`initialForm_mem_framePrefixSubalgebra_of_partialFrame` with `p = τ_a`, `i = m_a`. -/
theorem initialForm_mem_adjoin_of_isNormalizedStandardBase_mvPowerSeries
    (J : Ideal (MvPowerSeries (Fin r) S))
    (hF : (RegularFrame.mvPowerSeries S r).IsRegularTauFrame J)
    {m : ℕ} (f : Fin m → MvPowerSeries (Fin r) S)
    (hf : (RegularFrame.mvPowerSeries S r).IsNormalizedStandardBase J f)
    (a : ℕ) (ha : 1 ≤ a) (hat : a ≤ t _ J) (ma : ℕ+)
    (hma : IsGreatest {n : ℕ+ | nuI _ J n = (mu _ J a : ℕ∞)} ma) :
    ∀ j : Fin m, (j : ℕ) < (ma : ℕ) →
      initialForm (maximalIdeal _) (f j) ∈
        Algebra.adjoin (MvPowerSeries (Fin r) S ⧸ maximalIdeal (MvPowerSeries (Fin r) S))
          (Set.range fun l : {l : Fin (RegularFrame.mvPowerSeries S r).r // (l : ℕ) < tau _ J a} =>
            frameForm (RegularFrame.mvPowerSeries S r).z l.1) := by
  classical
  obtain ⟨hFr, -, -⟩ := id hF
  have hτr : ∀ b, 1 ≤ b → b ≤ t _ J → tau _ J b ≤ r := fun b hb hbt =>
    (tau_le_tau_of_le J hb hbt le_rfl).trans hFr.le
  have hblk := fun b (hb : 1 ≤ b) (hbt : b ≤ t _ J) => lt_blockEnd_iff hf.1 hb hbt
  have main : ∀ b, 1 ≤ b → b ≤ t _ J → ∀ j : Fin m, (j : ℕ) < blockEnd J m b →
      initialForm (maximalIdeal _) (f j) ∈
        framePrefixSubalgebra (RegularFrame.mvPowerSeries S r).z (tau _ J b) := by
    intro b hb1
    induction b, hb1 using Nat.le_induction with
    | base =>
      intro hbt j hj
      obtain ⟨hpos, heq, hmax⟩ := blockEnd_spec hf.1 le_rfl hbt
      have hnu1 : nuI _ J 1 = (mu _ J 1 : ℕ∞) := nuI_one_eq_mu_one heq
      have hjo : Ideal.ordElem (maximalIdeal _) (f j) ≤ (mu _ J 1 : ℕ∞) := (hblk 1 le_rfl hbt j).mp hj
      have h0 : (0 : ℕ).succPNat = 1 := rfl
      refine initialForm_mem_framePrefixSubalgebra_of_partialFrame J hF f hf le_rfl hbt
        (Nat.zero_le r) (Nat.zero_le _) (Nat.zero_le m) (fun l hl => absurd hl (Nat.not_lt_zero _))
        (by rw [h0]; exact hnu1.symm) j (Nat.zero_le _) ?_
      rw [ordElem_eq_nuI_of_isStandardBase J f hf.1 j] at hjo
      have hge : nuI _ J 1 ≤ nuI _ J (j : ℕ).succPNat := nuI_mono J one_le
      rw [h0]
      exact le_antisymm (hjo.trans hnu1.ge) hge
    | succ b hb ih =>
      intro hbt j hj
      have hbt' : b ≤ t _ J := by omega
      obtain ⟨hlt, hnu⟩ := blockEnd_lt_and_nuI_succ hf.1 hb (by omega)
      by_cases hjb : (j : ℕ) < blockEnd J m b
      · refine framePrefixSubalgebra_mono _ ?_ (ih hbt' j hjb)
        exact tau_le_tau_of_le J hb (by omega) hbt
      · rw [not_lt] at hjb
        have hjo : Ideal.ordElem (maximalIdeal _) (f j) ≤ (mu _ J (b + 1) : ℕ∞) :=
          (hblk (b + 1) (by omega) hbt j).mp hj
        rw [ordElem_eq_nuI_of_isStandardBase J f hf.1 j] at hjo
        have hge : nuI _ J (blockEnd J m b).succPNat ≤ nuI _ J (j : ℕ).succPNat :=
          nuI_mono J ((PNat.coe_le_coe _ _).mp (by simp only [Nat.succPNat_coe]; omega))
        refine initialForm_mem_framePrefixSubalgebra_of_partialFrame J hF f hf (by omega) hbt
          (hτr b hb hbt') (tau_le_tau_of_le J hb (by omega) hbt) (blockEnd_le m b)
          (fun l hl => ih hbt' l hl) hnu.symm j hjb ?_
        exact le_antisymm (hjo.trans hnu.ge) hge
  intro j hj
  obtain ⟨hpos, heq, hmax⟩ := blockEnd_spec hf.1 ha hat
  have hma' : (ma : ℕ) ≤ blockEnd J m a := hmax ma hma.1
  exact main a ha hat j (lt_of_lt_of_le hj hma')

end Theorem7Complete

/-! ### The one-step theorem for `R = S{z₁, …, z_τ}`: the induction on `a` -/

section Main

variable {S : Type u} [CommRing S] [IsRegularLocalRing S] {r : ℕ}

/-- **The one-step theorem of Theorem 8 for complete `R = S{z₁, …, z_τ}`** (p. 264, after "we may
assume that `R` is complete … so that `R = S{z₁, …, z_τ}`"), proved by the printed induction on
`a`.  Notation: `(S; z₁, …, z_τ)` the regular `τ`-frame of `R = S⟦z₁, …, z_τ⟧` for `J`, `R₁`,
`J₁`, `(S₁; w₁, …, w_τ)` with denominator `x`, `(f₁, …, f_m)`, `g_j = x^{-ν_j} f_j` as in the
paper; `m_a = blockEnd J m a`, `S^{(a)} = S{z_{τ_a+1}, …, z_τ}` (`RegularFrame.partialFrame`) and
`(S^{(a)}₁; w₁, …, w_{τ_a})` its frame transform with denominator `x`
(`RegularFrame.exists_partialFrame_frameTransform`).  For `1 ≤ a ≤ t` the induction proves the
paper's three assertions:
(1) "`(g₁, …, g_{m_a})` can be extend [sic] to a standard base of `J₁`",
(2) "`τ_{(w)_a}(g₁, …, g_{m_a}) = 0`" (the initial forms of `g₁, …, g_{m_a}` lie in
`k[W₁, …, W_{τ_a}]`), and
(3) "`g_{m_a+1}, …, g_{m_{a+1}}` are all normalized by `(g₁, …, g_{m_a})` with respect to
`(S^{(a)}₁; w₁, …, w_{τ_a})`" (with "`(g₁, …, g_{m_a}, g_j)` can be extended to a standard base",
the second conclusion of the same application of Lemma 20);
together with `ν_{M₁}(g_l) = ν^{(l)}(J)` for `l ≤ m_a`.  The last assertion is Lemma 20 for the
partial frame (`isNormalizedBy_partialFrameTransform_and_extends`), the second for `a + 1` is
Lemma 19 for `(S^{(a)}₁; w₁, …, w_{τ_a})` (`initialForm_mem_adjoin_of_partialFrameTransform`).
Gaps filled: "The first two assertions are clear for `a = 1`": Lemma 20 for `(S^{(1)}; z₁, …,
z_{τ_1})` with the empty system and Lemma 19 for `(S^{(1)}₁; w₁, …, w_{τ_1})`; "This lemma also shows
that `(g₁, …, g_{m_{a+1}})` can be extended to a standard base of `J₁`": Lemma 20 for `S^{(t)} = S`,
i.e. the frame `(S; z₁, …, z_τ)`, applied to `g_{m_{a+1}}` and all its predecessors (the second
assertion for `a + 1` gives its hypothesis (8)); "Thus … `(g₁, …, g_m)` is a normalized standard base
of `J₁`": the same application of Lemma 20 to every member gives the normalization by all
predecessors with respect to `(S₁; w)`.  The hypothesis `hF` (the frame is a regular `τ`-frame for
`J`, as in Theorem 8) gives, by Theorem 7, `τ_{(z)_a}(f₁, …, f_{m_a}) = 0`, hypothesis (2) of Lemma
20 for the partial frame. -/
theorem isNormalizedStandardBase_strictTransform_of_mvPowerSeries [Hironaka.HironakaCitedResults.{u}]
    (J : Ideal (MvPowerSeries (Fin r) S))
    (hF : (RegularFrame.mvPowerSeries S r).IsRegularTauFrame J)
    (Q : Ideal (MvPowerSeries (Fin r) S)) [Q.IsPrime]
    (hQperm : IsPermissibleCenter _ J Q) (hzQ : (RegularFrame.mvPowerSeries S r).idealZ ≤ Q)
    (T : MonoidalTransform _ Q) [IsLocalHom T.toRing] [IsRegularLocalRing T.ring]
    (hsep : RingHom.IsResiduallySeparableAlgebraic (R := MvPowerSeries (Fin r) S) (R' := T.ring)
      T.toRing)
    (x : (RegularFrame.mvPowerSeries S r).S)
    (hxQ : algebraMap _ (MvPowerSeries (Fin r) S) x ∈ Q)
    (hx : Q.map T.toRing = Ideal.span {T.toRing (algebraMap _ (MvPowerSeries (Fin r) S) x)})
    (FT : (RegularFrame.mvPowerSeries S r).FrameTransform T)
    (hFTx : FT.x = T.toRing (algebraMap _ (MvPowerSeries (Fin r) S) x))
    (hnu : nuStar T.ring (strictTransformIdeal T J) = nuStar _ J)
    (htau : ∀ a, 1 ≤ a → a ≤ t _ J → tau T.ring (strictTransformIdeal T J) a = tau _ J a)
    (hF₁ : FT.toRegularFrame.IsRegularTauFrame (strictTransformIdeal T J))
    {m : ℕ} (f : Fin m → MvPowerSeries (Fin r) S)
    (hf : (RegularFrame.mvPowerSeries S r).IsNormalizedStandardBase J f)
    (hfQ : ∀ j : Fin m, Ideal.ordElem Q (f j) = nuI _ J (j : ℕ).succPNat)
    (ν : Fin m → ℕ) (hν : ∀ j, (ν j : ℕ∞) = nuI _ J (j : ℕ).succPNat)
    (g : Fin m → T.ring)
    (hg : ∀ j, T.toRing (algebraMap _ (MvPowerSeries (Fin r) S) x) ^ ν j * g j = T.toRing (f j)) :
    FT.toRegularFrame.IsNormalizedStandardBase (strictTransformIdeal T J) g ∧
      ∀ a, 1 ≤ a → a ≤ t _ J → ∀ j : Fin m,
        Ideal.ordElem (maximalIdeal _) (f j) ≤ (mu _ J a : ℕ∞) →
          initialForm (maximalIdeal T.ring) (g j) ∈ Algebra.adjoin (T.ring ⧸ maximalIdeal T.ring)
            (Set.range fun q : {q : Fin (RegularFrame.mvPowerSeries S r).r //
              (q : ℕ) < tau _ J a} => frameForm FT.w q.1) := by
  classical
  have hnuI : ∀ i, nuI T.ring (strictTransformIdeal T J) i = nuI _ J i :=
    fun i => congrFun (toLex.injective hnu) i
  have hg_mem : ∀ j, g j ∈ strictTransformIdeal T J := fun j =>
    Ideal.subset_span ⟨T.toRing (algebraMap _ (MvPowerSeries (Fin r) S) x), hx.symm, f j,
      hf.1.1 j, ν j, ((hν j).trans (hfQ j).symm).le, hg j⟩
  have ht : t T.ring (strictTransformIdeal T J) = t _ J := t_congr_of_nuStar_eq hnu
  have hmu : ∀ a, mu T.ring (strictTransformIdeal T J) a = mu _ J a := mu_congr_of_nuStar_eq hnu
  have hord : ∀ l : Fin m, Ideal.ordElem (maximalIdeal _) (f l) = nuI _ J (l : ℕ).succPNat :=
    fun l => ordElem_eq_nuI_of_isStandardBase J f hf.1 l
  have hQreg : IsRegularLocalRing (MvPowerSeries (Fin r) S ⧸ Q) := by
    rcases hQperm with hQtop | ⟨-, -, hreg, -⟩
    · exact absurd hQtop (Ideal.IsPrime.ne_top ‹Q.IsPrime›)
    · exact hreg
  obtain ⟨hFr, -, -⟩ := id hF
  have hτr : ∀ a, 1 ≤ a → a ≤ t _ J → tau _ J a ≤ r := fun a ha hat =>
    (tau_le_tau_of_le J ha hat le_rfl).trans hFr.le
  -- the frame transforms `(S^{(a)}₁; w₁, …, w_{τ_a})` with the denominator `x`
  have hex : ∀ a, ∃ FTp : (RegularFrame.partialFrame S r (min (tau _ J a) r)
      (min_le_right _ _)).FrameTransform T,
      FTp.x = T.toRing (algebraMap _ (MvPowerSeries (Fin r) S) x) ∧
        ∀ l, FTp.w l = FT.w (Fin.castLE (RegularFrame.partialFrame_r_le r _ _) l) := fun a =>
    RegularFrame.exists_partialFrame_frameTransform (min_le_right _ _) x hxQ hx FT hFTx
  choose FTp hFTpx hFTpw using hex
  -- the subalgebras `k[Z₁, …, Z_{τ_a}]` and `k[W₁, …, W_{τ_a}]`
  have hassocF : ∀ a, (RegularFrame.partialFrame S r (min (tau _ J a) r)
      (min_le_right _ _)).assocSubalgebra =
        framePrefixSubalgebra (RegularFrame.mvPowerSeries S r).z (tau _ J a) := fun a => by
    rw [RegularFrame.assocSubalgebra]
    exact (assocSubalgebra_eq_framePrefixSubalgebra _ _ _ (RegularFrame.partialFrame_z r _ _)).trans
      (framePrefixSubalgebra_min _ _)
  have hassocT : ∀ a, (FTp a).toRegularFrame.assocSubalgebra =
      framePrefixSubalgebra FT.w (tau _ J a) := fun a => by
    rw [RegularFrame.assocSubalgebra, RegularFrame.FrameTransform.toRegularFrame_z]
    exact (assocSubalgebra_eq_framePrefixSubalgebra _ _ _ (hFTpw a)).trans
      (framePrefixSubalgebra_min _ _)
  -- the blocks
  have hblk := fun a (ha : 1 ≤ a) (hat : a ≤ t _ J) => lt_blockEnd_iff hf.1 ha hat
  -- Theorem 7: the initial forms of `f₁, …, f_{m_a}` lie in `k[Z₁, …, Z_{τ_a}]`
  have hthm7 : ∀ a, 1 ≤ a → a ≤ t _ J → ∀ l : Fin m, (l : ℕ) < blockEnd J m a →
      initialForm (maximalIdeal _) (f l) ∈ framePrefixSubalgebra
        (RegularFrame.mvPowerSeries S r).z (tau _ J a) := by
    intro a ha hat l hl
    obtain ⟨hpos, heq, hmax⟩ := blockEnd_spec hf.1 ha hat
    exact initialForm_mem_adjoin_of_isNormalizedStandardBase_mvPowerSeries J hF f hf a ha hat
      ⟨blockEnd J m a, hpos⟩ ⟨heq, fun n hn => (PNat.coe_le_coe _ _).mp (hmax n hn)⟩ l hl
  -- Lemma 20 for `S^{(t)} = S`, i.e. for the frame `(S; z₁, …, z_τ)` itself, and a member `g_k`
  -- with all its predecessors
  have hfull : ∀ k : Fin m, (∀ l : Fin m, (l : ℕ) < k →
      Ideal.ordElem (maximalIdeal T.ring) (g l) = nuI _ J (l : ℕ).succPNat) →
      (∀ l : Fin m, (l : ℕ) < k → initialForm (maximalIdeal T.ring) (g l) ∈
        FT.toRegularFrame.assocSubalgebra) →
      FT.toRegularFrame.IsNormalizedBy (fun l : Fin k => g (Fin.castLE k.2.le l)) (g k) ∧
      ExtendsToStandardBase (strictTransformIdeal T J)
        (Fin.snoc (fun l : Fin k => g (Fin.castLE k.2.le l)) (g k) :
          Fin ((k : ℕ) + 1) → T.ring) := by
    intro k hko hka
    set ν' : Fin ((k : ℕ) + 1) → ℕ := fun l => ν (Fin.castLE (Nat.succ_le_of_lt k.2) l)
      with hν'
    have hν'cast : ∀ l : Fin (k : ℕ), ν' l.castSucc = ν (Fin.castLE k.2.le l) := fun l =>
      congrArg ν (Fin.ext rfl)
    have hν'last : ν' (Fin.last (k : ℕ)) = ν k := congrArg ν (Fin.ext rfl)
    have h1 : ExtendsToStandardBase J (Fin.snoc (fun l : Fin (k : ℕ) => f (Fin.castLE k.2.le l))
        (f k) : Fin ((k : ℕ) + 1) → MvPowerSeries (Fin r) S) := by
      refine ⟨m, f, Nat.succ_le_of_lt k.2, hf.1, fun l => ?_⟩
      induction l using Fin.lastCases with
      | last => rw [Fin.snoc_last]; exact congrArg f (Fin.ext rfl)
      | cast l => rw [Fin.snoc_castSucc]; exact congrArg f (Fin.ext rfl)
    obtain ⟨hN, hE⟩ := isNormalizedBy_frameTransform_and_extendsToStandardBase J
      (RegularFrame.mvPowerSeries S r) (fun l : Fin (k : ℕ) => f (Fin.castLE k.2.le l)) (f k)
      (fun l => hf.1.1 _) (hf.1.1 k) h1
      (fun l => (RegularFrame.mvPowerSeries S r).tauZ_eq_zero_of_initialForm_mem _ (hf.2.1 _))
      (hf.2.2 k) Q hQperm hzQ (fun l => hfQ _) (hfQ k) T hsep x hxQ hx FT hFTx ν'
      (fun l => hν _) (fun l : Fin (k : ℕ) => g (Fin.castLE k.2.le l))
      (fun l => by rw [hν'cast]; exact hg _)
      (fun l => FT.toRegularFrame.tauZ_eq_zero_of_initialForm_mem _ (hka _ l.2))
      (fun l => hko _ l.2) (g k) (by rw [hν'last]; exact hg k)
    exact ⟨hN, hE fun i _ => hnuI i⟩
  -- the members of the `(a+1)`-st block have the order `ν^{(m_a+1)}(J) = μ^{(a+1)}(J)`
  have hνblk : ∀ a, 1 ≤ a → a < t _ J → ∀ j : Fin m, blockEnd J m a ≤ j →
      (j : ℕ) < blockEnd J m (a + 1) →
        nuI _ J (j : ℕ).succPNat = nuI _ J (blockEnd J m a).succPNat := by
    intro a ha hat j hj1 hj2
    obtain ⟨-, hsucc⟩ := blockEnd_lt_and_nuI_succ hf.1 ha hat
    apply le_antisymm
    · rw [hsucc, ← hord j]
      exact (hblk (a + 1) (by omega) hat j).mp hj2
    · exact nuI_mono J ((PNat.coe_le_coe _ _).mp (by simp only [Nat.succPNat_coe]; omega))
  -- "The first assertion": by Lemma 20 for `(S; z₁, …, z_τ)`
  have hfirst : ∀ a, 1 ≤ a → a ≤ t _ J →
      (∀ l : Fin m, (l : ℕ) < blockEnd J m a →
        Ideal.ordElem (maximalIdeal T.ring) (g l) = nuI _ J (l : ℕ).succPNat) →
      (∀ l : Fin m, (l : ℕ) < blockEnd J m a → initialForm (maximalIdeal T.ring) (g l) ∈
        framePrefixSubalgebra FT.w (tau _ J a)) →
      ExtendsToStandardBase (strictTransformIdeal T J)
        (fun l : Fin (blockEnd J m a) => g (Fin.castLE (blockEnd_le m a) l)) := by
    intro a ha hat hko hka
    obtain ⟨hpos, -, -⟩ := blockEnd_spec hf.1 ha hat
    have hle := blockEnd_le (J := J) m a
    have hlt : blockEnd J m a - 1 < m := by omega
    have hk := (hfull ⟨blockEnd J m a - 1, hlt⟩
      (fun l hl => hko l (by have : (l : ℕ) < blockEnd J m a - 1 := hl; omega))
      (fun l hl => framePrefixSubalgebra_le_assocSubalgebra _ _
        (hka l (by have : (l : ℕ) < blockEnd J m a - 1 := hl; omega)))).2
    exact hk.of_snoc_castLE ⟨blockEnd J m a - 1, hlt⟩ (by simp only; omega) (blockEnd_le m a)
  -- "the last assertion follows from the first two by Lemma 20 of §8": Lemma 20 for
  -- `(S^{(a)}; z₁, …, z_{τ_a})`
  have hthird : ∀ a, 1 ≤ a → a < t _ J →
      (∀ l : Fin m, (l : ℕ) < blockEnd J m a →
        Ideal.ordElem (maximalIdeal T.ring) (g l) = nuI _ J (l : ℕ).succPNat) →
      (∀ l : Fin m, (l : ℕ) < blockEnd J m a → initialForm (maximalIdeal T.ring) (g l) ∈
        framePrefixSubalgebra FT.w (tau _ J a)) →
      ∀ j : Fin m, blockEnd J m a ≤ j → (j : ℕ) < blockEnd J m (a + 1) →
        (FTp a).toRegularFrame.IsNormalizedBy
          (fun l : Fin (blockEnd J m a) => g (Fin.castLE (blockEnd_le m a) l)) (g j) ∧
        ExtendsToStandardBase (strictTransformIdeal T J)
          (Fin.snoc (fun l : Fin (blockEnd J m a) => g (Fin.castLE (blockEnd_le m a) l)) (g j) :
            Fin (blockEnd J m a + 1) → T.ring) := by
    intro a ha hat hko hka j hj1 hj2
    exact isNormalizedBy_partialFrameTransform_and_extends J Q hQperm hzQ T hsep x hxQ hx f hf
      hfQ ν hν g hg hnuI (min_le_right _ _) (FTp a) (hFTpx a) (blockEnd_le m a)
      (fun l hl => by rw [hassocF a]; exact hthm7 a ha hat.le l hl)
      (fun l hl => by rw [hassocT a]; exact hka l hl)
      hko j hj1 (hνblk a ha hat j hj1 hj2)
  -- "Then the second assertion for `a` increased by `1` follows by virtue of Lemma 19 of §7":
  -- Lemma 19 for `(S^{(a)}₁; w₁, …, w_{τ_a})`
  have hsecond : ∀ a, 1 ≤ a → a < t _ J →
      (∀ l : Fin m, (l : ℕ) < blockEnd J m a → initialForm (maximalIdeal T.ring) (g l) ∈
        framePrefixSubalgebra FT.w (tau _ J a)) →
      ∀ j : Fin m, blockEnd J m a ≤ j → (j : ℕ) < blockEnd J m (a + 1) →
        (FTp a).toRegularFrame.IsNormalizedBy
          (fun l : Fin (blockEnd J m a) => g (Fin.castLE (blockEnd_le m a) l)) (g j) →
        ExtendsToStandardBase (strictTransformIdeal T J)
          (Fin.snoc (fun l : Fin (blockEnd J m a) => g (Fin.castLE (blockEnd_le m a) l)) (g j) :
            Fin (blockEnd J m a + 1) → T.ring) →
        initialForm (maximalIdeal T.ring) (g j) ∈ framePrefixSubalgebra FT.w (tau _ J (a + 1)) := by
    intro a ha hat hka j hj1 hj2 hN hE
    obtain ⟨-, hsucc⟩ := blockEnd_lt_and_nuI_succ hf.1 ha hat
    have htau1 := htau (a + 1) (by omega) (by omega)
    have h := initialForm_mem_adjoin_of_partialFrameTransform (strictTransformIdeal T J) FT hF₁
      (min_le_right _ _) (FTp a) (hFTpw a) g hg_mem (blockEnd_le m a)
      (fun l hl => by rw [hassocT a]; exact hka l hl) (a + 1) (by omega) (by rw [ht]; omega)
      (by
        rw [htau1]
        exact (min_le_left _ _).trans (tau_le_tau_of_le J ha (by omega) (by omega)))
      (by rw [hmu, hnuI, hsucc]) j hE hN
    rw [htau1] at h
    exact h
  -- "The first two assertions are clear for `a = 1`": Lemma 20 for `(S^{(1)}; z₁, …, z_{τ_1})`
  -- with the empty system and Lemma 19 for `(S^{(1)}₁; w₁, …, w_{τ_1})`
  have hbase : ∀ j : Fin m, (j : ℕ) < blockEnd J m 1 →
      Ideal.ordElem (maximalIdeal T.ring) (g j) = nuI _ J (j : ℕ).succPNat ∧
      initialForm (maximalIdeal T.ring) (g j) ∈ framePrefixSubalgebra FT.w (tau _ J 1) := by
    intro j hj
    have ht1 : 1 ≤ t _ J := one_le_t_of_isStandardBase hf.1 (lt_of_le_of_lt (Nat.zero_le _) j.2)
    have hν1 : nuI _ J (0 : ℕ).succPNat = (mu _ J 1 : ℕ∞) := by
      obtain ⟨hpos, heq, -⟩ := blockEnd_spec hf.1 le_rfl ht1
      have hle : nuI _ J (0 : ℕ).succPNat ≤ (mu _ J 1 : ℕ∞) := by
        rw [← heq]
        exact nuI_mono J ((PNat.coe_le_coe _ _).mp
          (by simp only [Nat.succPNat_coe, PNat.mk_coe]; omega))
      have htop : nuI _ J (0 : ℕ).succPNat ≠ ⊤ := ne_top_of_le_ne_top (ENat.natCast_ne_top _) hle
      rw [← ENat.natCast_toNat htop] at hle ⊢
      have hmem : (nuI _ J (0 : ℕ).succPNat).toNat ∈ muSet _ J :=
        ⟨_, (ENat.natCast_toNat htop).symm⟩
      exact_mod_cast le_antisymm (by exact_mod_cast hle) (mu_one_le_of_mem_muSet hmem)
    have hνj : nuI _ J (j : ℕ).succPNat = nuI _ J (0 : ℕ).succPNat := by
      apply le_antisymm
      · rw [hν1, ← hord j]
        exact (hblk 1 le_rfl ht1 j).mp hj
      · exact nuI_mono J ((PNat.coe_le_coe _ _).mp (by simp only [Nat.succPNat_coe]; omega))
    obtain ⟨hN, hE⟩ := isNormalizedBy_partialFrameTransform_and_extends J Q hQperm hzQ T hsep x
      hxQ hx f hf hfQ ν hν g hg hnuI (min_le_right _ _) (FTp 1) (hFTpx 1) (Nat.zero_le m)
      (fun l hl => absurd hl (Nat.not_lt_zero _)) (fun l hl => absurd hl (Nat.not_lt_zero _))
      (fun l hl => absurd hl (Nat.not_lt_zero _)) j (Nat.zero_le _) hνj
    refine ⟨?_, ?_⟩
    · have := hE.ordElem_eq (Fin.last 0)
      rw [Fin.snoc_last, hnuI] at this
      rw [this, hνj]
      rfl
    · have htau1 := htau 1 le_rfl ht1
      have h := initialForm_mem_adjoin_of_partialFrameTransform (strictTransformIdeal T J) FT hF₁
        (min_le_right _ _) (FTp 1) (hFTpw 1) g hg_mem (Nat.zero_le m)
        (fun l hl => absurd hl (Nat.not_lt_zero _)) 1 le_rfl (by rw [ht]; exact ht1)
        (by rw [htau1]; exact min_le_left _ _) (by rw [hmu, hnuI, hν1]) j hE hN
      rw [htau1] at h
      exact h
  -- the induction on `a`
  have main : ∀ a, 1 ≤ a → a ≤ t _ J →
      (∀ l : Fin m, (l : ℕ) < blockEnd J m a →
        Ideal.ordElem (maximalIdeal T.ring) (g l) = nuI _ J (l : ℕ).succPNat) ∧
      ExtendsToStandardBase (strictTransformIdeal T J)
        (fun l : Fin (blockEnd J m a) => g (Fin.castLE (blockEnd_le m a) l)) ∧
      (∀ l : Fin m, (l : ℕ) < blockEnd J m a → initialForm (maximalIdeal T.ring) (g l) ∈
        framePrefixSubalgebra FT.w (tau _ J a)) ∧
      (a < t _ J → ∀ j : Fin m, blockEnd J m a ≤ j → (j : ℕ) < blockEnd J m (a + 1) →
        (FTp a).toRegularFrame.IsNormalizedBy
          (fun l : Fin (blockEnd J m a) => g (Fin.castLE (blockEnd_le m a) l)) (g j) ∧
        ExtendsToStandardBase (strictTransformIdeal T J)
          (Fin.snoc (fun l : Fin (blockEnd J m a) => g (Fin.castLE (blockEnd_le m a) l)) (g j) :
            Fin (blockEnd J m a + 1) → T.ring)) := by
    intro a ha
    induction a, ha using Nat.le_induction with
    | base =>
      intro hat
      have h0 := fun l hl => (hbase l hl).1
      have h2 := fun l hl => (hbase l hl).2
      exact ⟨h0, hfirst 1 le_rfl hat h0 h2, h2, fun hlt => hthird 1 le_rfl hlt h0 h2⟩
    | succ a ha ih =>
      intro hat
      obtain ⟨h0, -, h2, h3⟩ := ih (by omega)
      have h3' := h3 (by omega)
      have h0' : ∀ l : Fin m, (l : ℕ) < blockEnd J m (a + 1) →
          Ideal.ordElem (maximalIdeal T.ring) (g l) = nuI _ J (l : ℕ).succPNat := by
        intro l hl
        by_cases hla : (l : ℕ) < blockEnd J m a
        · exact h0 l hla
        · have hE := (h3' l (not_lt.mp hla) hl).2
          have := hE.ordElem_eq (Fin.last _)
          rw [Fin.snoc_last, hnuI] at this
          rw [this, hνblk a ha (by omega) l (not_lt.mp hla) hl]
          rfl
      have h2' : ∀ l : Fin m, (l : ℕ) < blockEnd J m (a + 1) →
          initialForm (maximalIdeal T.ring) (g l) ∈ framePrefixSubalgebra FT.w (tau _ J (a + 1)) := by
        intro l hl
        by_cases hla : (l : ℕ) < blockEnd J m a
        · exact framePrefixSubalgebra_mono _ (tau_le_tau_of_le J ha (by omega) hat) (h2 l hla)
        · exact hsecond a ha (by omega) h2 l (not_lt.mp hla) hl (h3' l (not_lt.mp hla) hl).1
            (h3' l (not_lt.mp hla) hl).2
      exact ⟨h0', hfirst (a + 1) (by omega) hat h0' h2', h2',
        fun hlt => hthird (a + 1) (by omega) hlt h0' h2'⟩
  -- "Thus `τ_{(w)}(g₁, …, g_m) = 0` for `(w) = (w₁, …, w_τ)`, and `(g₁, …, g_m)` is a normalized
  -- standard base of `J₁`"
  by_cases hm : m = 0
  · subst hm
    refine ⟨⟨?_, fun j => j.elim0, fun j => j.elim0⟩, fun a _ _ j => j.elim0⟩
    obtain ⟨m₂, G, hG⟩ := exists_isStandardBase (strictTransformIdeal T J)
    have : m₂ = 0 := length_eq_of_nuI_eq hG hf.1 (fun i => hnuI i)
    subst this
    have : g = G := funext fun j => j.elim0
    rw [this]
    exact hG
  have ht1 : 1 ≤ t _ J := one_le_t_of_isStandardBase hf.1 (Nat.pos_of_ne_zero hm)
  obtain ⟨h0t, -, h2t, -⟩ := main (t _ J) ht1 le_rfl
  have h0 : ∀ l : Fin m, Ideal.ordElem (maximalIdeal T.ring) (g l) =
      nuI _ J (l : ℕ).succPNat := fun l => h0t l (lt_blockEnd_t hf.1 ht1 l)
  have h2 : ∀ l : Fin m, initialForm (maximalIdeal T.ring) (g l) ∈
      FT.toRegularFrame.assocSubalgebra := fun l =>
    framePrefixSubalgebra_le_assocSubalgebra _ _ (h2t l (lt_blockEnd_t hf.1 ht1 l))
  have hN : ∀ k : Fin m, FT.toRegularFrame.IsNormalizedBy
      (fun l : Fin k => g (Fin.castLE k.2.le l)) (g k) := fun k =>
    (hfull k (fun l _ => h0 l) (fun l _ => h2 l)).1
  have hstd : IsStandardBase T.ring (strictTransformIdeal T J) g := by
    obtain ⟨m₀, rfl⟩ : ∃ m₀, m = m₀ + 1 := ⟨m - 1, by omega⟩
    have hext := ((hfull ⟨m₀, Nat.lt_succ_self _⟩ (fun l _ => h0 l) (fun l _ => h2 l)).2).of_snoc_castLE
      ⟨m₀, Nat.lt_succ_self _⟩ rfl le_rfl
    obtain ⟨m₂, G, him, hG, hGf⟩ := hext
    have hlen : m₂ = m₀ + 1 := length_eq_of_nuI_eq hG hf.1 (fun i => hnuI i)
    subst hlen
    have : g = G := funext fun j => by
      have h := hGf j
      simp only at h
      rw [show Fin.castLE him j = j from Fin.ext rfl] at h
      rw [← h]
    rw [this]
    exact hG
  refine ⟨⟨hstd, h2, hN⟩, fun a ha hat j hj => ?_⟩
  exact (main a ha hat).2.2.1 j ((hblk a ha hat j).mpr hj)

end Main

end Hironaka
