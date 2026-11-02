/-
Copyright (c) 2026 Daattavya Aggarwal, Minhyong Kim, Oisin Kim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daattavya Aggarwal, Minhyong Kim, Oisin Kim
-/
module

public import Mathlib.RingTheory.LocalProperties.Reduced
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Architect
public import Hironaka.Ch3.JStability
public import Hironaka.Compat.CompleteRationalBaseChange
public import Hironaka.Compat.CanonicalLiftResidue

/-!
# Lifting a sequence of monoidal transforms along a local homomorphism (Remark 1, pp. 262-263)

Remark 1 of Ch. III §9: for a local homomorphism `R -> R'` of regular local rings which transforms
a regular system of parameters into one and is residually separable, every sequence of monoidal
transforms of `R` lifts to a sequence of `R'` with a commutative diagram of canonical local
homomorphisms `R_alpha -> R'_alpha`; "by Lemma 4, §2, `R_alpha -> R'_alpha` has the same properties
as `R -> R'` for every `alpha`".

This file contains the one-stage input (Lemma 4 for the step `R_alpha -> R_{alpha+1}`): a canonical
lift whose closed fibre `R'_bar/M_{R'}R'_bar` has a single prime ideal
(`exists_isCanonicalLift_isMinimal`, chosen with the prime of `B'_bar` minimal over `M'B'_bar`),
hence of the same dimension (`IsCanonicalLift.ringKrullDim_eq_of_forall_prime_eq`), and then, by
`Hironaka/Compat/CanonicalLiftResidue.lean`, again transforming a regular system of parameters into
one and residually separable
(`exists_isCanonicalLift_mapsRSOP_isResiduallySeparable`).
-/

@[expose] public section

open IsLocalRing
open scoped TensorProduct

namespace Hironaka

universe u

section MinimalLift

/-- A prime ideal `q` of `B̄` which is minimal over `M'B̄` and contracts to the prime `M'` of `B`
gives a local homomorphism `B_{M'} → B̄_q` whose closed fibre has a single prime ideal: a prime
ideal `Q₀` of `B̄_q` containing `M_{B_{M'}}B̄_q` contracts to a prime of `B̄` containing `M'B̄` and
contained in `q`, hence to `q`. -/
theorem eq_maximalIdeal_of_le_map_of_minimalPrimes {B Bb : Type u} [CommRing B] [CommRing Bb]
    (ψ : B →+* Bb) (M' : Ideal B) [M'.IsPrime] (q : Ideal Bb) [q.IsPrime]
    (hqM : q.comap ψ = M') (hqmin : q ∈ (M'.map ψ).minimalPrimes)
    (Q₀ : Ideal (Localization.AtPrime q)) [Q₀.IsPrime]
    (hle : (maximalIdeal (Localization.AtPrime M')).map
      (Localization.localRingHom M' q ψ hqM.symm) ≤ Q₀) :
    Q₀ = maximalIdeal (Localization.AtPrime q) := by
  set q₀ := Q₀.comap (algebraMap Bb (Localization.AtPrime q)) with hq₀def
  have hq₀ : q₀.IsPrime := Ideal.comap_isPrime _ _
  -- `q₀ ≤ q`
  have hq₀q : q₀ ≤ q := by
    have h1 : Q₀ ≤ maximalIdeal (Localization.AtPrime q) :=
      le_maximalIdeal (Ideal.IsPrime.ne_top ‹_›)
    calc q₀ ≤ (maximalIdeal (Localization.AtPrime q)).comap
            (algebraMap Bb (Localization.AtPrime q)) := Ideal.comap_mono h1
      _ = q := IsLocalization.AtPrime.under_maximalIdeal (Localization.AtPrime q) q
  -- `M'B̄ ≤ q₀`
  have hIq₀ : M'.map ψ ≤ q₀ := by
    rw [Ideal.map_le_iff_le_comap]
    intro x hx
    rw [Ideal.mem_comap, Ideal.mem_comap]
    have h1 : algebraMap B (Localization.AtPrime M') x ∈ maximalIdeal (Localization.AtPrime M') :=
      (IsLocalization.AtPrime.to_map_mem_maximal_iff (Localization.AtPrime M') M' x).mpr hx
    have h2 := hle (Ideal.mem_map_of_mem _ h1)
    rwa [Localization.localRingHom_to_map] at h2
  have hqq₀ : q ≤ q₀ := hqmin.2 ⟨hq₀, hIq₀⟩ hq₀q
  have hq₀eq : q₀ = q := le_antisymm hq₀q hqq₀
  calc Q₀ = (Q₀.comap (algebraMap Bb (Localization.AtPrime q))).map
          (algebraMap Bb (Localization.AtPrime q)) :=
        (IsLocalization.map_under q.primeCompl (Localization.AtPrime q) Q₀).symm
    _ = q.map (algebraMap Bb (Localization.AtPrime q)) := by rw [← hq₀def, hq₀eq]
    _ = maximalIdeal (Localization.AtPrime q) := Localization.AtPrime.map_eq_maximalIdeal

end MinimalLift

section CanonicalLiftExistence

/-- Elements of `R[x⁻¹P]` are fractions `f / xᴺ`, with `N` as large as wanted. -/
private theorem exists_pow_mul_eq_of_mem_blowupAlgebra' {R : Type u} [CommRing R]
    [IsRegularLocalRing R] [IsDomain R] {P : Ideal R} {x : R} (hx : x ≠ 0) {y : FractionRing R}
    (hy : y ∈ blowupAlgebra R P x) :
    ∃ N : ℕ, ∀ n, N ≤ n → ∃ f : R,
      algebraMap R (FractionRing R) x ^ n * y = algebraMap R (FractionRing R) f := by
  have hx' : algebraMap R (FractionRing R) x ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective R _)).mpr hx
  suffices h : ∃ (N : ℕ) (f : R),
      algebraMap R (FractionRing R) x ^ N * y = algebraMap R (FractionRing R) f by
    obtain ⟨N, f, hf⟩ := h
    refine ⟨N, fun n hn => ⟨x ^ (n - N) * f, ?_⟩⟩
    rw [map_mul, map_pow, ← hf, ← mul_assoc, ← pow_add, Nat.sub_add_cancel hn]
  induction hy using Algebra.adjoin_induction with
  | mem y hy =>
    obtain ⟨p, -, rfl⟩ := hy
    exact ⟨1, p, by rw [pow_one, mul_div_cancel₀ _ hx']⟩
  | algebraMap r => exact ⟨0, r, by rw [pow_zero, one_mul]⟩
  | add y z _ _ hy hz =>
    obtain ⟨N₁, f₁, h₁⟩ := hy
    obtain ⟨N₂, f₂, h₂⟩ := hz
    refine ⟨N₁ + N₂, x ^ N₂ * f₁ + x ^ N₁ * f₂, ?_⟩
    rw [map_add, map_mul, map_mul, map_pow, map_pow, ← h₁, ← h₂]
    ring
  | mul y z _ _ hy hz =>
    obtain ⟨N₁, f₁, h₁⟩ := hy
    obtain ⟨N₂, f₂, h₂⟩ := hz
    refine ⟨N₁ + N₂, f₁ * f₂, ?_⟩
    rw [map_mul, ← h₁, ← h₂]
    ring

/-- **Existence of canonical monoidal transforms with a unique prime in the closed fibre**
(pp. 211-212, the existence half of Lemma 4 (1)): as `exists_isCanonicalLift`, the prime `M''` of
`B̄ = R̄[x⁻¹PR̄]` over the prime `M'` of `B = R[x⁻¹P]` is chosen minimal over `M'B̄`.  Then the
closed fibre `R̄'/M_{R'}R̄'` of the canonical lift has a single prime ideal (it has dimension `0`),
so that `dim R̄' = dim R'`.  (The paper's description of the canonical lifts through the prime
ideals of `k' ⊗_k k̄`, pp. 211-212, gives these lifts as those `q̄` which are minimal.) -/
theorem exists_isCanonicalLift_isMinimal {R R' : Type u} [CommRing R] [IsRegularLocalRing R]
    [IsDomain R] [CommRing R'] [IsRegularLocalRing R'] [IsDomain R'] (α : R →+* R')
    [IsLocalHom α] (hα : RingHom.MapsRSOP α) {P : Ideal R} (T : MonoidalTransform R P) :
    ∃ (T' : MonoidalTransform R' (P.map α)) (β : T.ring →+* T'.ring),
      IsCanonicalLift α T T' β ∧ ∀ Q₀ : Ideal T'.ring, Q₀.IsPrime →
        (maximalIdeal T.ring).map β ≤ Q₀ → Q₀ = maximalIdeal T'.ring := by
  classical
  let _ : Algebra R R' := α.toAlgebra
  have _ : IsLocalHom (algebraMap R R') := ‹IsLocalHom α›
  have _ : Module.Flat R R' := hα.flat
  have _ : Module.FaithfullyFlat R R' := Module.FaithfullyFlat.of_flat_of_isLocalHom
  have hinj : Function.Injective α := FaithfulSMul.algebraMap_injective R R'
  have hle : nonZeroDivisors R ≤ (nonZeroDivisors R').comap α := fun y hy =>
    mem_nonZeroDivisors_of_ne_zero ((map_ne_zero_iff α hinj).mpr (nonZeroDivisors.ne_zero hy))
  let φ : FractionRing R →+* FractionRing R' := IsLocalization.map (FractionRing R') α hle
  have hφ : ∀ r, φ (algebraMap R (FractionRing R) r) = algebraMap R' (FractionRing R') (α r) :=
    fun r => IsLocalization.map_eq hle r
  have hx'P : α T.x ∈ P.map α := Ideal.mem_map_of_mem α T.x_mem
  have hx'0 : α T.x ≠ 0 := (map_ne_zero_iff α hinj).mpr T.x_ne_zero
  -- `φ` maps `B = R[x⁻¹P]` into `B̄ = R̄[x⁻¹PR̄]`
  have hBB' : ∀ y ∈ blowupAlgebra R P T.x, φ y ∈ blowupAlgebra R' (P.map α) (α T.x) := by
    intro y hy
    induction hy using Algebra.adjoin_induction with
    | mem y hy =>
      obtain ⟨p, hp, rfl⟩ := hy
      rw [map_div₀, hφ, hφ]
      exact Algebra.subset_adjoin ⟨α p, Ideal.mem_map_of_mem α hp, rfl⟩
    | algebraMap r =>
      rw [hφ]
      exact Subalgebra.algebraMap_mem _ (α r)
    | add y z _ _ hy hz =>
      rw [map_add]
      exact add_mem hy hz
    | mul y z _ _ hy hz =>
      rw [map_mul]
      exact mul_mem hy hz
  let ψ : blowupAlgebra R P T.x →+* blowupAlgebra R' (P.map α) (α T.x) :=
    (φ.comp (blowupAlgebra R P T.x).val.toRingHom).codRestrict _ fun b => hBB' b b.2
  have hψ : ∀ b, ((ψ b : blowupAlgebra R' (P.map α) (α T.x)) : FractionRing R') = φ b :=
    fun b => rfl
  -- `B̄` lies in the `R̄`-span of `φ(B)`
  set S := Submodule.span R' (Set.range fun b : blowupAlgebra R P T.x => φ b) with hSdef
  have hSmul : ∀ y z, y ∈ S → z ∈ S → y * z ∈ S := by
    intro y z hy hz
    have h := Submodule.mul_mem_mul hy hz
    rw [Submodule.span_mul_span] at h
    refine Submodule.span_mono ?_ h
    rintro _ ⟨_, ⟨b₁, rfl⟩, _, ⟨b₂, rfl⟩, rfl⟩
    exact ⟨b₁ * b₂, by simp only [Subalgebra.coe_mul, map_mul]⟩
  have hspan : ∀ y ∈ blowupAlgebra R' (P.map α) (α T.x), y ∈ S := by
    intro y hy
    induction hy using Algebra.adjoin_induction with
    | mem y hy =>
      obtain ⟨p', hp', rfl⟩ := hy
      induction hp' using Submodule.span_induction with
      | mem p' hp' =>
        obtain ⟨p, hp, rfl⟩ := hp'
        refine Submodule.subset_span ⟨⟨_, Algebra.subset_adjoin ⟨p, hp, rfl⟩⟩, ?_⟩
        simp only [map_div₀, hφ]
      | zero => simp
      | add a b _ _ ha hb =>
        dsimp only at ha hb ⊢
        rw [map_add, add_div]
        exact add_mem ha hb
      | smul r' a _ ha =>
        dsimp only at ha ⊢
        rw [smul_eq_mul, map_mul, mul_div_assoc, ← Algebra.smul_def]
        exact Submodule.smul_mem _ _ ha
    | algebraMap r' =>
      rw [Algebra.algebraMap_eq_smul_one]
      refine Submodule.smul_mem _ _ (Submodule.subset_span ⟨1, ?_⟩)
      simp
    | add y z _ _ hy hz => exact add_mem hy hz
    | mul y z _ _ hy hz => exact hSmul y z hy hz
  have hxK : algebraMap R (FractionRing R) T.x ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective R _)).mpr T.x_ne_zero
  -- `(I B̄) ∩ B = I` for every ideal `I` of `B`
  have hcm : ∀ I : Ideal (blowupAlgebra R P T.x), (I.map ψ).comap ψ ≤ I := by
    intro I b hb
    rw [Ideal.mem_comap] at hb
    -- (i) `φ(b)` lies in the `R̄`-span of `φ(I)`
    set SI := Submodule.span R' ((fun a : blowupAlgebra R P T.x => φ a) '' (I : Set _))
      with hSI
    have hSImul : ∀ y z, y ∈ S → z ∈ SI → y * z ∈ SI := by
      intro y z hy hz
      have h := Submodule.mul_mem_mul hy hz
      rw [Submodule.span_mul_span] at h
      refine Submodule.span_mono ?_ h
      rintro _ ⟨_, ⟨b₁, rfl⟩, _, ⟨a, ha, rfl⟩, rfl⟩
      exact ⟨b₁ * a, I.mul_mem_left b₁ ha, by simp only [Subalgebra.coe_mul, map_mul]⟩
    have hb' : ψ b ∈ Ideal.span (ψ '' (I : Set _)) := hb
    have key : ∀ z ∈ Ideal.span (ψ '' (I : Set _)),
        ((z : blowupAlgebra R' (P.map α) (α T.x)) : FractionRing R') ∈ SI := by
      intro z hz
      induction hz using Submodule.span_induction with
      | mem z hz =>
        obtain ⟨a, ha, rfl⟩ := hz
        exact Submodule.subset_span ⟨a, ha, rfl⟩
      | zero => simp
      | add y z _ _ hy hz =>
        rw [Subalgebra.coe_add]
        exact add_mem hy hz
      | smul c z _ hz =>
        rw [smul_eq_mul, Subalgebra.coe_mul]
        exact hSImul _ _ (hspan _ c.2) hz
    have h1 : φ b ∈ SI := by
      rw [← hψ]
      exact key _ hb'
    -- (ii) a finite `R̄`-combination
    obtain ⟨n, c, a, hsum⟩ := Submodule.mem_span_set'.mp h1
    choose a' ha' hga using fun i => (a i).2
    -- (iii) common denominators `xᴺ`
    obtain ⟨Nb, hNb⟩ := exists_pow_mul_eq_of_mem_blowupAlgebra' T.x_ne_zero b.2
    choose Ni hNi using fun i => exists_pow_mul_eq_of_mem_blowupAlgebra' T.x_ne_zero (a' i).2
    set N := max Nb (Finset.univ.sup Ni)
    obtain ⟨f, hf⟩ := hNb N (le_max_left _ _)
    choose g hg using fun i =>
      hNi i N ((Finset.le_sup (f := Ni) (Finset.mem_univ i)).trans (le_max_right _ _))
    -- (iv) `α(f) = Σ cᵢ α(gᵢ)` in `R̄`
    have hfg : α f = ∑ i, c i * α (g i) := by
      apply IsFractionRing.injective R' (FractionRing R')
      calc algebraMap R' (FractionRing R') (α f)
          = φ (algebraMap R (FractionRing R) f) := (hφ f).symm
        _ = φ (algebraMap R (FractionRing R) T.x) ^ N * φ b := by rw [← hf, map_mul, map_pow]
        _ = ∑ i, algebraMap R' (FractionRing R') (c i) *
            φ (algebraMap R (FractionRing R) T.x ^ N * a' i) := by
          rw [← hsum, Finset.mul_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Algebra.smul_def, ← hga i, map_mul, map_pow]
          ring
        _ = algebraMap R' (FractionRing R') (∑ i, c i * α (g i)) := by
          rw [map_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [hg i, hφ, map_mul]
    -- (v) `f ∈ (g₁, …, g_n)` by faithful flatness
    have hmem : α f ∈ (Ideal.span (Set.range g)).map α := by
      rw [hfg, Ideal.map_span]
      exact Ideal.sum_mem _ fun i _ =>
        Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨g i, ⟨i, rfl⟩, rfl⟩)
    have hf' : f ∈ Ideal.span (Set.range g) := by
      rw [← Ideal.comap_map_eq_self_of_faithfullyFlat (B := R') (Ideal.span (Set.range g))]
      exact hmem
    obtain ⟨s, hs⟩ := Ideal.mem_span_range_iff_exists_fun.mp hf'
    -- (vi) `b = Σ sᵢ aᵢ ∈ I`
    have hbK : (b : FractionRing R) =
        ∑ i, algebraMap R (FractionRing R) (s i) * (a' i : FractionRing R) := by
      apply mul_left_cancel₀ (pow_ne_zero N hxK)
      rw [hf, ← hs, map_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_mul, ← hg i]
      ring
    have hbeq : b = ∑ i, algebraMap R (blowupAlgebra R P T.x) (s i) * a' i := by
      apply Subtype.ext
      rw [hbK]
      simp
    rw [hbeq]
    exact Ideal.sum_mem _ fun i _ => I.mul_mem_left _ (ha' i)
  -- a prime of `B̄` over `M'`
  obtain ⟨q₁, hq₁, hqM₁⟩ := (Ideal.comap_map_eq_self_iff_of_isPrime T.M').mp
    (le_antisymm (hcm _) Ideal.le_comap_map)
  -- a prime of `B̄` over `M'` which is minimal over `M'B̄`
  have hI₁ : T.M'.map ψ ≤ q₁ := Ideal.map_le_iff_le_comap.mpr hqM₁.ge
  obtain ⟨q, hqmin, hqq₁⟩ := Ideal.exists_minimalPrimes_le hI₁
  have hq : q.IsPrime := hqmin.1.1
  have hIq : T.M'.map ψ ≤ q := hqmin.1.2
  have hqM : q.comap ψ = T.M' :=
    le_antisymm (le_trans (Ideal.comap_mono hqq₁) hqM₁.le) (Ideal.map_le_iff_le_comap.mp hIq)
  have hcompat : ψ.comp (algebraMap R (blowupAlgebra R P T.x)) =
      (algebraMap R' (blowupAlgebra R' (P.map α) (α T.x))).comp α :=
    RingHom.ext fun r => Subtype.ext (hφ r)
  have hle' : (maximalIdeal R').map (algebraMap R' (blowupAlgebra R' (P.map α) (α T.x))) ≤ q := by
    rw [← hα.map_maximalIdeal, Ideal.map_map, ← hcompat, ← Ideal.map_map]
    refine (Ideal.map_mono T.le).trans ?_
    rw [Ideal.map_le_iff_le_comap, hqM]
  let T' : MonoidalTransform R' (P.map α) := ⟨α T.x, hx'P, hx'0, q, hq, hle'⟩
  refine ⟨T', Localization.localRingHom T.M' q ψ hqM.symm, ⟨?_, ?_⟩, ?_⟩
  · exact Localization.isLocalHom_localRingHom _ _ _ _
  · refine RingHom.ext fun r => ?_
    have h1 := Localization.localRingHom_to_map T.M' q ψ hqM.symm
      (algebraMap R (blowupAlgebra R P T.x) r)
    exact h1.trans (congrArg _ (DFunLike.congr_fun hcompat r))
  · -- the closed fibre has a single prime: `q` is minimal over `M'B̄`
    intro Q₀ hQ₀ hle
    exact @eq_maximalIdeal_of_le_map_of_minimalPrimes _ _ _ _ ψ T.M' _ q hq hqM hqmin Q₀ hQ₀ hle

end CanonicalLiftExistence

section FibreDimension

variable {R Rb : Type u} [CommRing R] [IsRegularLocalRing R] [IsDomain R] [CommRing Rb]
  [IsRegularLocalRing Rb] [IsDomain Rb]

/-- If the closed fibre `R̄'/M_{R'}R̄'` of a canonical lift has a single prime ideal, then
`dim R̄' = dim R'` (`dim R̄' = dim R' + dim R̄'/M_{R'}R̄'`, p. 212). -/
theorem IsCanonicalLift.ringKrullDim_eq_of_forall_prime_eq (α : R →+* Rb) [IsLocalHom α]
    (hα : RingHom.MapsRSOP α) {P : Ideal R} (t : MonoidalTransform R P)
    (tb : MonoidalTransform Rb (P.map α)) (β : t.ring →+* tb.ring)
    (hβ : IsCanonicalLift α t tb β)
    (hU : ∀ Q₀ : Ideal tb.ring, Q₀.IsPrime → (maximalIdeal t.ring).map β ≤ Q₀ →
      Q₀ = maximalIdeal tb.ring) :
    ringKrullDim tb.ring = ringKrullDim t.ring := by
  have := hβ.isLocalHom
  set I := (maximalIdeal t.ring).map β with hIdef
  have hI : I ≤ maximalIdeal tb.ring :=
    Ideal.map_le_iff_le_comap.mpr fun a ha => map_nonunit β a ha
  have : IsLocalRing (tb.ring ⧸ I) := isLocalRing_quotient_of_le hI
  have hheight := IsCanonicalLift.height_maximalIdeal_eq_add α hα t tb β hβ
  have hmax : (maximalIdeal tb.ring).map (Ideal.Quotient.mk I) = maximalIdeal (tb.ring ⧸ I) :=
    map_maximalIdeal_of_surjective _ Ideal.Quotient.mk_surjective
  -- the maximal ideal of the closed fibre is a minimal prime
  have hmin' : maximalIdeal (tb.ring ⧸ I) ∈ minimalPrimes (tb.ring ⧸ I) := by
    refine ⟨⟨inferInstance, bot_le⟩, fun 𝔮 h𝔮 h𝔮le => ?_⟩
    obtain ⟨h𝔮prime, -⟩ := h𝔮
    have h1 := hU (𝔮.comap (Ideal.Quotient.mk I)) (Ideal.comap_isPrime _ _) (fun a ha => by
      rw [Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.mpr ha]
      exact 𝔮.zero_mem)
    intro x hx
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    have ha : a ∈ maximalIdeal tb.ring := by
      by_contra h
      exact (IsLocalRing.mem_maximalIdeal _).mp hx ((IsLocalRing.notMem_maximalIdeal.mp h).map _)
    have : a ∈ 𝔮.comap (Ideal.Quotient.mk I) := h1 ▸ ha
    exact this
  have hmin : (maximalIdeal tb.ring).map (Ideal.Quotient.mk I) ∈ minimalPrimes (tb.ring ⧸ I) :=
    hmax ▸ hmin'
  have : ((maximalIdeal tb.ring).map (Ideal.Quotient.mk I)).IsPrime := by
    rw [hmax]; infer_instance
  have h0 : ((maximalIdeal tb.ring).map (Ideal.Quotient.mk I)).height = 0 :=
    Ideal.height_eq_zero_iff.mpr hmin
  rw [h0, add_zero] at hheight
  rw [← IsLocalRing.maximalIdeal_height_eq_ringKrullDim,
    ← IsLocalRing.maximalIdeal_height_eq_ringKrullDim, hheight]

end FibreDimension

section GoodLift

variable {R Rb : Type u} [CommRing R] [IsRegularLocalRing R] [IsDomain R] [CommRing Rb]
  [IsRegularLocalRing Rb] [IsDomain Rb]

/-- **Existence of a canonical lift with the same properties** (Lemma 4, pp. 210-212, applied at
every stage of the lifting of a sequence, Remark 1, p. 263): if `α : R → R̄` transforms a regular
system of parameters into one and is residually separable, then every monoidal transform `R'` of
`R` with a center `P` which is `R` or a prime with `R/P` regular has a canonical lift `R̄'`, a
regular local ring, such that `R' → R̄'` again transforms a regular system of parameters into one
and is residually separable.  (The lift is chosen with `dim R̄' = dim R'`; for `R'` residually
algebraic over `R` this holds for every canonical lift, Lemma 4 (1).) -/
theorem exists_isCanonicalLift_mapsRSOP_isResiduallySeparable (α : R →+* Rb) [IsLocalHom α]
    (hα : RingHom.MapsRSOP α) (hsep : RingHom.IsResiduallySeparable α) {P : Ideal R}
    (hP : P = ⊤ ∨ (P.IsPrime ∧ IsRegularLocalRing (R ⧸ P))) (T : MonoidalTransform R P)
    [IsRegularLocalRing T.ring] :
    ∃ (T' : MonoidalTransform Rb (P.map α)) (β : T.ring →+* T'.ring)
      (hβ : IsCanonicalLift α T T' β) (_ : IsRegularLocalRing T'.ring),
        haveI := hβ.isLocalHom
        RingHom.MapsRSOP β ∧ RingHom.IsResiduallySeparable β := by
  obtain ⟨T', β, hβ, hU⟩ := exists_isCanonicalLift_isMinimal α hα T
  have hreg : IsRegularLocalRing T'.ring := by
    rcases hP with hP | ⟨hPp, hPr⟩
    · have hP' : P.map α = ⊤ := by rw [hP, Ideal.map_top]
      exact IsRegularLocalRing.of_ringEquiv
        (RingEquiv.ofBijective T'.toRing (MonoidalSequence.toRing_bijective_of_eq_top_aux T' hP'))
    · have := hPp
      have := hPr
      exact (⟨T', β, hβ⟩ : BaseChangeLift α T).isRegularLocalRing hα
  have hdim := IsCanonicalLift.ringKrullDim_eq_of_forall_prime_eq α hα T T' β hβ hU
  exact ⟨T', β, hβ, hreg, IsCanonicalLift.mapsRSOP_and_isResiduallySeparable_of_ringKrullDim_eq α
    hα hsep T T' β hβ hdim⟩

end GoodLift

end Hironaka
