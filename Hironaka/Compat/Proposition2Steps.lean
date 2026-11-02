/-
Copyright (c) 2026 Daattavya Aggarwal, Minhyong Kim, Oisin Kim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daattavya Aggarwal, Minhyong Kim, Oisin Kim
-/
module

public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Architect
public import Hironaka.Ch3.Stability
public import Hironaka.Ch3.PermissibleEffects
public import Hironaka.Ch3.StabilityCor3c
public import Hironaka.Compat.NormalizedStandardBase

/-!
# Compatibility layer: auxiliary steps of the proof of Proposition 2 (Ch. III §8, pp. 258–259)

> "However, `x` is a unit in `R_P = (R₁)_{P₁}`, and therefore `ν_{PR_P}(f_j) = ν_j` for all `j`
> `(1 ≤ j ≤ m)` which implies `ν_P(f_j) = ν_j` for all `j` `(1 ≤ j ≤ m)` by the assumption (ii)."
> (Proof of Proposition 2, p. 259)

* `MonoidalTransform.localRingHom_bijective_of_notMem` (`R_P = (R₁)_{P₁}` for a prime `P₁` of a
  monoidal transform with centre `Q` over a prime `P` with `x ∉ P`) and
  `MonoidalTransform.le_ordElem_of_le_ordElem_toRing` (the passage from `ν_{P₁}(f) ≥ ν` to
  `ν_P(f) ≥ ν`, for `R/P` and `R₁/P₁` regular);
* `length_eq_of_nuI_eq`: standard bases of ideals with the same sequence `ν*` have the same length;
* `isPermissibleCenter_of_t_eq_zero`: every prime `P ⊇ J` with `R/P` regular is a permissible
  center for `J` if `t(J) = 0`, i.e. if `J = (0)`.
-/

@[expose] public section

open IsLocalRing

namespace Hironaka

universe u

section LocalRingHom

variable {R : Type u} [CommRing R] [IsRegularLocalRing R] [IsDomain R]

/-- For a monoidal transform `R₁` of `R` with centre `Q` (element `x`) and a prime `P₁` of `R₁`
lying over a prime `P` of `R` with `x ∉ P`, the canonical map `R_P → (R₁)_{P₁}` is bijective:
`R₁ ⊆ R[1/x] ⊆ R_P` inside the field of quotients (p. 259, "`R_P = (R₁)_{P₁}`").  This is
`MonoidalTransform.localRingHom_bijective_of_x_notMem` for an arbitrary centre `Q`. -/
theorem MonoidalTransform.localRingHom_bijective_of_notMem {Q : Ideal R}
    (t : MonoidalTransform R Q) (P : Ideal R) [P.IsPrime] (P' : Ideal t.ring) [P'.IsPrime]
    (hP' : P = P'.comap t.toRing) (hxP : t.x ∉ P) :
    Function.Bijective (Localization.localRingHom P P' t.toRing hP') := by
  have hxM : t.x ∈ Q := t.x_mem
  set f := Localization.localRingHom P P' t.toRing hP'
  set T := Localization.AtPrime P'
  let A := blowupAlgebra R Q t.x
  set α := algebraMap t.ring T
  let β : A →+* T := α.comp (algebraMap A t.ring)
  have hxpow : ∀ m, t.x ^ m ∈ P.primeCompl := fun m h =>
    hxP (Ideal.IsPrime.mem_of_pow_mem ‹_› m h)
  -- every `b = g/xᵐ ∈ A` comes from `R_P`
  have hβ : ∀ b : A, ∃ y, f y = β b := by
    intro b
    obtain ⟨m, g, -, hbg⟩ :=
      MonoidalTransform.exists_mul_pow_eq_of_mem_blowupAlgebra hxM t.x_ne_zero b.2
    refine ⟨IsLocalization.mk' _ g ⟨t.x ^ m, hxpow m⟩, ?_⟩
    rw [Localization.localRingHom_mk', IsLocalization.mk'_eq_iff_eq_mul]
    have hA : b * algebraMap R A (t.x ^ m) = algebraMap R A g :=
      Subtype.ext (by simpa [map_pow] using hbg)
    show α (algebraMap A t.ring (algebraMap R A g)) =
      β b * α (algebraMap A t.ring (algebraMap R A (t.x ^ m)))
    rw [← hA, map_mul, map_mul]
    rfl
  -- and so do the inverses of the units among them (`f` is local)
  have hβinv : ∀ b : A, IsUnit (β b) → ∃ y, f y * β b = 1 := by
    intro b hb
    obtain ⟨y, hy⟩ := hβ b
    have hyu : IsUnit y := isUnit_of_map_unit f y (hy ▸ hb)
    refine ⟨↑hyu.unit⁻¹, ?_⟩
    rw [← hy, ← map_mul, hyu.val_inv_mul, map_one]
  refine ⟨?_, ?_⟩
  · rw [injective_iff_map_eq_zero]
    intro z hz
    obtain ⟨r, s, rfl⟩ := IsLocalization.exists_mk'_eq P.primeCompl z
    rw [Localization.localRingHom_mk', IsLocalization.mk'_eq_zero_iff] at hz
    obtain ⟨c, hc⟩ := hz
    have hc0 : (c : t.ring) ≠ 0 := fun h0 => c.2 (by rw [h0]; exact zero_mem _)
    have hr : t.toRing r = 0 := (mul_eq_zero.mp hc).resolve_left hc0
    have : r = 0 := t.toRing_injective (by rw [hr, map_zero])
    rw [this, IsLocalization.mk'_zero]
  · intro z
    obtain ⟨a, s, rfl⟩ := IsLocalization.exists_mk'_eq P'.primeCompl z
    obtain ⟨b, u, rfl⟩ := IsLocalization.exists_mk'_eq t.M'.primeCompl a
    obtain ⟨c, w, hcw⟩ := IsLocalization.exists_mk'_eq t.M'.primeCompl (s : t.ring)
    have h1 : α (IsLocalization.mk' t.ring b u) * β u = β b := by
      show α _ * α (algebraMap A t.ring u) = α (algebraMap A t.ring b)
      rw [← map_mul, IsLocalization.mk'_spec]
    have h2 : α s * β w = β c := by
      show α _ * α (algebraMap A t.ring w) = α (algebraMap A t.ring c)
      rw [← hcw, ← map_mul, IsLocalization.mk'_spec]
    have hβu : IsUnit (β u) := (IsLocalization.map_units t.ring u).map α
    have hβc : IsUnit (β c) := by
      rw [← h2]
      exact (IsLocalization.map_units T s).mul ((IsLocalization.map_units t.ring w).map α)
    obtain ⟨yb, hyb⟩ := hβ b
    obtain ⟨yw, hyw⟩ := hβ w
    obtain ⟨yc, hyc⟩ := hβinv c hβc
    obtain ⟨yu, hyu⟩ := hβinv u hβu
    refine ⟨yb * yw * yc * yu, ?_⟩
    rw [map_mul, map_mul, map_mul, hyb, hyw, eq_comm, IsLocalization.mk'_eq_iff_eq_mul]
    linear_combination (-(α (IsLocalization.mk' t.ring b u))) * hyu + f yu * h1 -
      (β b * f yu) * hyc - (β b * f yu * f yc) * h2

/-- **`ν_P ≥ ν` from `ν_{P₁} ≥ ν`** (p. 259: "`x` is a unit in `R_P = (R₁)_{P₁}`, and therefore
`ν_{PR_P}(f_j) = ν_j` […] which implies `ν_P(f_j) = ν_j` by the assumption (ii)"): for a monoidal
transform `R₁` of `R` with centre `Q`, primes `P ⊆ R`, `P₁ ⊆ R₁` with `P₁ ∩ R = P`, `x ∉ P`, and
`R/P`, `R₁/P₁` regular, `ν ≤ ν_{P₁}(f)` implies `ν ≤ ν_P(f)`. -/
theorem MonoidalTransform.le_ordElem_of_le_ordElem_toRing {Q : Ideal R}
    (t : MonoidalTransform R Q) [IsLocalHom t.toRing] [IsRegularLocalRing t.ring]
    (P : Ideal R) [P.IsPrime] [IsRegularLocalRing (R ⧸ P)] (P₁ : Ideal t.ring) [P₁.IsPrime]
    [IsRegularLocalRing (t.ring ⧸ P₁)] (hP₁ : P₁.comap t.toRing = P) (hxP : t.x ∉ P) (f : R)
    (n : ℕ∞) (hf : n ≤ Ideal.ordElem P₁ (t.toRing f)) : n ≤ Ideal.ordElem P f := by
  set φ := Localization.localRingHom P P₁ t.toRing hP₁.symm with hφdef
  have hφ : Function.Bijective φ := t.localRingHom_bijective_of_notMem P P₁ hP₁.symm hxP
  have hmax : (P.map (algebraMap R (Localization.AtPrime P))).map φ =
      P₁.map (algebraMap t.ring (Localization.AtPrime P₁)) := by
    rw [Localization.AtPrime.map_eq_maximalIdeal, Localization.AtPrime.map_eq_maximalIdeal]
    exact map_maximalIdeal_of_surjective φ hφ.2
  have h1 := Ideal.ordElem_map_of_bijective φ hφ (P.map (algebraMap R (Localization.AtPrime P)))
    (algebraMap R (Localization.AtPrime P) f)
  rw [hmax, hφdef, Localization.localRingHom_to_map] at h1
  rw [ordElem_localization_eq_of_isRegularLocalRing_quotient P inferInstance f,
    ordElem_localization_eq_of_isRegularLocalRing_quotient P₁ inferInstance] at h1
  rw [← h1]
  exact hf

end LocalRingHom

section StandardBaseLength

variable {S S' : Type u} [CommRing S] [IsRegularLocalRing S] [CommRing S'] [IsRegularLocalRing S']

/-- `i ≤ m` iff `ν^{(i)}(J) < ∞`, for a standard base of length `m`. -/
theorem le_length_iff_nuI_ne_top {J : Ideal S} {m : ℕ} {g : Fin m → S}
    (hg : IsStandardBase S J g) (i : ℕ+) : (i : ℕ) ≤ m ↔ nuI S J i ≠ ⊤ := by
  obtain ⟨⟨d, -, hd⟩, htop⟩ := nuI_eq_of_hasLemma1Properties S J _ hg.2
  constructor
  · intro hi
    have := hd ⟨(i : ℕ) - 1, by have := i.pos; omega⟩
    have hi' : (⟨((⟨(i : ℕ) - 1, by have := i.pos; omega⟩ : Fin m) : ℕ) + 1, Nat.succ_pos _⟩ : ℕ+)
        = i := PNat.eq (by simp; have := i.pos; omega)
    rw [hi'] at this
    rw [this]
    exact ENat.natCast_ne_top _
  · intro hne
    by_contra hlt
    exact hne (htop i (by omega))

/-- Standard bases of ideals with the same sequence `ν*` have the same length. -/
theorem length_eq_of_nuI_eq {J : Ideal S} {J' : Ideal S'} {m m' : ℕ} {g : Fin m → S}
    {g' : Fin m' → S'} (hg : IsStandardBase S J g) (hg' : IsStandardBase S' J' g')
    (h : ∀ i, nuI S J i = nuI S' J' i) : m = m' := by
  have key : ∀ i : ℕ+, (i : ℕ) ≤ m ↔ (i : ℕ) ≤ m' := fun i => by
    rw [le_length_iff_nuI_ne_top hg, le_length_iff_nuI_ne_top hg', h i]
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
  · have := (key ⟨m + 1, Nat.succ_pos _⟩).mpr (by simp; omega)
    simp at this
  · have := (key ⟨m' + 1, Nat.succ_pos _⟩).mp (by simp; omega)
    simp at this

end StandardBaseLength

section TrivialCase

variable {R : Type u} [CommRing R] [IsRegularLocalRing R]

/-- If `t(J) = 0` (i.e. `J = (0)`), every prime `P ⊇ J` with `R/P` regular is a permissible center
for `J` (the empty system is a standard base of `J`). -/
theorem isPermissibleCenter_of_t_eq_zero (J P : Ideal R) [P.IsPrime] (hJP : J ≤ P)
    [IsRegularLocalRing (R ⧸ P)] (ht : t R J = 0) : IsPermissibleCenter R J P := by
  obtain ⟨m, g, hg⟩ := exists_isStandardBase J
  have hm : m = 0 := by
    by_contra hm
    have hfin : (muSet R J).Finite := (muSet_finite R J).1
    have hmem : (muSet R J).Nonempty := by
      obtain ⟨⟨d, -, hd⟩, -⟩ := nuI_eq_of_hasLemma1Properties R J _ hg.2
      exact ⟨d ⟨0, by omega⟩, ⟨⟨1, Nat.one_pos⟩, (hd ⟨0, by omega⟩)⟩⟩
    have : 0 < (muSet R J).ncard := (Set.ncard_pos hfin).mpr hmem
    exact absurd ht (by rw [t]; omega)
  subst hm
  refine Or.inr ⟨inferInstance, hJP, inferInstance, ?_⟩
  have h13 : IsNormallyFlatAlongIdeal (P.map (Ideal.Quotient.mk J)) ↔
      ∃ (m : ℕ) (f : Fin m → R), IsStandardBase R J f ∧
        ∀ j : Fin m, Ideal.ordElem P (f j) = nuI R J ((j : ℕ).succPNat) :=
    (isPermissibleCenter_tfae R J P hJP).out 1 3
  exact h13.mpr ⟨0, g, hg, fun j => j.elim0⟩

end TrivialCase

end Hironaka
