/-
Copyright (c) 2026 Daattavya Aggarwal, Minhyong Kim, Oisin Kim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daattavya Aggarwal, Minhyong Kim, Oisin Kim
-/
module

public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Architect
public import Hironaka.Ch3.FrameTransforms
public import Hironaka.Compat.RegularGraded
public import Hironaka.Compat.RSOPProducts

/-!
# Compatibility layer: regular frames and their transforms (Ch. III §§ 7–9, used in Ch. IV)

Ring-level facts about a regular frame `(S; z)` (`r = 1`) of a regular local ring `R` used by the
frame arguments of Ch. IV §3 (Lemmas (AB.4)–(AB.6), pp. 300–306) and Ch. IV §4 (Lemma (CD.4)):

* `RegularFrame.eq_span_sup_map_comap_of_mem`: `Q = zR + (Q ∩ S)R` for an ideal `Q ∋ z`;
* `RegularFrame.mem_comap_pow_of_mem_pow_sup`: `S ∩ (Q^k + (z)) = (Q ∩ S)^k`;
* `RegularFrame.coeff_mem_comap_pow_of_mem_pow`: if `z^n + c_1 z^{n-1} + ⋯ + c_n ∈ Q^n` for a
  prime `Q ∋ z` with `R/Q` regular, then `c_i ∈ (Q ∩ S)^i` (p. 302: "and `g_{jki}(s) ∈ Q̂_s^i`";
  p. 318: "it then follows that `g_{ji}(t) ∈ (Q̂'_t ∩ T'_t)^i`");
* `RegularFrame.exists_mem_comap_mul_unit` (Nakayama) and
  `RegularFrame.exists_frameTransform_of_mem_maximalIdeal`: the frame transform `(S₁; z/v)` of
  `(S; z)` in a monoidal transform `R₁` of `R` with center `Q ∋ z`, with a denominator `v ∈ Q ∩ S`,
  when `z/x_{R₁}` is a non-unit (p. 300: "it admits a frame transform `(T_t; z_t)` …
  `z_{t+1} = z_t/v_t` with the denominator `v_t ∈ T_t`"), and the division of the elements of
  `(Q ∩ S)^n` by `v^n` in `S₁`;
* `initialForm_maximalIdeal_unit`, `IsStandardBase.of_unit_mul`: standard bases may be multiplied
  by units (the arguments of private lemmas of `Hironaka/Ch3/JStability.lean`).

The first three statements and the proofs of the frame transform are adapted from the proofs of
`frame_ideal_eq_sup`, `frame_mem_comap_pow_of_mem_pow_add`, `frame_coeff_mem_pow`,
`exists_mem_comap_assoc_w` and `frame_step_core_of_exists` of `Hironaka/Ch4/ImplicationsCD.lean`
(Lemma (CD.4), p. 318), which state them for the frames of § 4; the names here are distinct so
that both files can be imported together.
-/

@[expose] public section

open IsLocalRing

namespace Hironaka

universe u

noncomputable section

namespace RegularFrame

/-- `Q = zR + (Q ∩ S)R` for a regular frame `(S; z)` (`r = 1`) and an ideal `Q ∋ z`
(`R/(z) ≅ S`). -/
theorem eq_span_sup_map_comap_of_mem {R : Type u} [CommRing R] [IsRegularLocalRing R]
    (F : RegularFrame R) (z : R) (hzF : ∀ j, F.z j = z) (hr : F.r = 1) (Q : Ideal R)
    (hzQ : z ∈ Q) :
    Q = Ideal.span {z} ⊔ (Q.comap (algebraMap F.S R)).map (algebraMap F.S R) := by
  have hq := F.quot_bijective
  have hzrange : Set.range F.z = {z} := by
    ext a
    simp only [Set.mem_range, Set.mem_singleton_iff]
    constructor
    · rintro ⟨j, rfl⟩; exact hzF j
    · rintro rfl
      exact ⟨⟨0, by rw [hr]; exact Nat.one_pos⟩, hzF _⟩
  rw [hzrange] at hq
  refine le_antisymm (fun q hq' => ?_) (sup_le ((Ideal.span_singleton_le_iff_mem _).mpr hzQ)
    Ideal.map_comap_le)
  obtain ⟨s, hs⟩ := hq.2 (Ideal.Quotient.mk _ q)
  have hs' : algebraMap F.S R s - q ∈ Ideal.span {z} := Ideal.Quotient.eq.mp hs
  have hsQ : algebraMap F.S R s ∈ Q := by
    have : algebraMap F.S R s = (algebraMap F.S R s - q) + q := by ring
    rw [this]
    exact Q.add_mem ((Ideal.span_singleton_le_iff_mem _).mpr hzQ hs') hq'
  have hq2 : q = algebraMap F.S R s - (algebraMap F.S R s - q) := by ring
  rw [hq2]
  exact Ideal.sub_mem _ (Ideal.mem_sup_right (Ideal.mem_map_of_mem _ hsQ))
    (Ideal.mem_sup_left hs')

/-- `S ∩ (Q^k + (z)) = (Q ∩ S)^k`: if `R/(z) ≅ S` and `z ∈ Q`, then `y ∈ S` with `y ∈ Q^k + (z)`
(in `R`) lies in `(Q ∩ S)^k` (the argument of `frame_mem_comap_pow_of_mem_pow_add` of
`Hironaka/Ch4/ImplicationsCD.lean`). -/
theorem mem_comap_pow_of_mem_pow_sup {R : Type u} [CommRing R] [IsRegularLocalRing R]
    (F : RegularFrame R) (z : R) (hzF : ∀ j, F.z j = z) (hr : F.r = 1) (Q : Ideal R)
    (hzQ : z ∈ Q) (k : ℕ) (y : F.S)
    (hy : algebraMap F.S R y ∈ Q ^ k ⊔ Ideal.span {z}) :
    y ∈ (Q.comap (algebraMap F.S R)) ^ k := by
  have hq := F.quot_bijective
  have hzrange : Set.range F.z = {z} := by
    ext a
    simp only [Set.mem_range, Set.mem_singleton_iff]
    constructor
    · rintro ⟨j, rfl⟩; exact hzF j
    · rintro rfl
      exact ⟨⟨0, by rw [hr]; exact Nat.one_pos⟩, hzF _⟩
  rw [hzrange] at hq
  let ψ : F.S ≃+* R ⧸ Ideal.span {z} := RingEquiv.ofBijective _ hq
  have hψ : ∀ s, ψ s = Ideal.Quotient.mk _ (algebraMap F.S R s) := fun s => rfl
  have hspan : Ideal.span {z} ≤ Q := (Ideal.span_singleton_le_iff_mem _).mpr hzQ
  have hk : Ideal.comap (Ideal.Quotient.mk (Ideal.span {z})) ⊥ = Ideal.span {z} := by
    rw [← RingHom.ker_eq_comap_bot]; exact Ideal.mk_ker
  have hcomap : (Q.map (Ideal.Quotient.mk (Ideal.span {z}))).comap (ψ : F.S →+* _) =
      Q.comap (algebraMap F.S R) := by
    ext s
    rw [Ideal.mem_comap, Ideal.mem_comap, RingEquiv.coe_toRingHom, hψ,
      ← Ideal.mem_comap, Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective, hk,
      sup_eq_left.mpr hspan]
  have e1 : ∀ I : Ideal (R ⧸ Ideal.span {z}),
      I.comap (ψ : F.S →+* _) = I.map (ψ.symm : (R ⧸ Ideal.span {z}) →+* F.S) := fun I => by
    exact Ideal.comap_symm (I := I) ψ.symm
  have hpow : ((Q.map (Ideal.Quotient.mk (Ideal.span {z}))) ^ k).comap (ψ : F.S →+* _) =
      (Q.comap (algebraMap F.S R)) ^ k := by
    rw [e1, Ideal.map_pow, ← e1, hcomap]
  rw [← hpow, Ideal.mem_comap, RingEquiv.coe_toRingHom, hψ]
  rw [← Ideal.map_pow]
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp hy
  have hb' : Ideal.Quotient.mk (Ideal.span {z}) b = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hb
  have : Ideal.Quotient.mk (Ideal.span {z}) (algebraMap F.S R y) =
      Ideal.Quotient.mk (Ideal.span {z}) a := by
    rw [← hab, map_add, hb', add_zero]
  rw [this]
  exact Ideal.mem_map_of_mem _ ha

/-- Ring level: if `z^n + c_1 z^{n-1} + ⋯ + c_n ∈ Q^n` for a regular frame `(S; z)` (`r = 1`)
and a prime `Q ∋ z` with `R/Q` regular, then `c_i ∈ (Q ∩ S)^i` (p. 302: "It follows that
`g_{jk}(s) ∈ Q̂^{ν_{jk}}` … and `g_{jki}(s) ∈ Q̂_s^i`"; p. 318).

\textbf{Deviation from the paper (gap filled).} The paper says "it follows" without proof (the
argument of `frame_coeff_mem_pow` of `Hironaka/Ch4/ImplicationsCD.lean`): modulo `z` the element
is `c_n`, so `c_n ∈ (Q ∩ S)^n` (`R/(z) ≅ S`); then `z · g'' ∈ Q^n` where `g''` has the same shape
with `n - 1`, and `ν_Q(z) = 1` (`z ∉ M²`) with `gr_Q(R)` a domain gives `g'' ∈ Q^{n-1}`. -/
theorem coeff_mem_comap_pow_of_mem_pow {R : Type u} [CommRing R]
    [IsRegularLocalRing R] (F : RegularFrame R) (z : R) (hzF : ∀ j, F.z j = z) (hr : F.r = 1)
    (Q : Ideal R) [Q.IsPrime] (hQ : IsRegularLocalRing (R ⧸ Q)) (hzQ : z ∈ Q) :
    ∀ (n : ℕ) (c : Fin n → F.S),
      z ^ n + ∑ i : Fin n, algebraMap F.S R (c i) * z ^ (n - ((i : ℕ) + 1)) ∈ Q ^ n →
        ∀ i : Fin n, c i ∈ (Q.comap (algebraMap F.S R)) ^ ((i : ℕ) + 1) := by
  classical
  have hdom := isDomain_of_isRegularLocalRing R
  have hgr := isDomain_assocGraded Q hQ
  have hzmem : z ∈ Finset.image F.z Finset.univ :=
    Finset.mem_image.mpr ⟨⟨0, by rw [hr]; exact Nat.one_pos⟩, Finset.mem_univ _, hzF _⟩
  have hzM2 : z ∉ maximalIdeal R ^ 2 := F.extends_rsop.notMem_maximalIdeal_sq hzmem
  have hzQ2 : z ∉ Q ^ 2 := fun h =>
    hzM2 (Ideal.pow_right_mono (IsLocalRing.le_maximalIdeal (Ideal.IsPrime.ne_top ‹_›)) 2 h)
  have hordz : Ideal.ordElem Q z = 1 := by
    refine le_antisymm ?_ ?_
    · exact Ideal.ordElem_le_of_notMem (m := 1) hzQ2
    · exact_mod_cast Ideal.le_ordElem (ν := 1) (by rwa [pow_one])
  intro n
  induction n with
  | zero => intro c _ i; exact i.elim0
  | succ n ih =>
    intro c hg i
    set g'' : R := z ^ n + ∑ i : Fin n, algebraMap F.S R (c i.castSucc) * z ^ (n - ((i : ℕ) + 1))
      with hg''
    have hsplit : z ^ (n + 1) + ∑ i : Fin (n + 1),
        algebraMap F.S R (c i) * z ^ (n + 1 - ((i : ℕ) + 1)) =
        z * g'' + algebraMap F.S R (c (Fin.last n)) := by
      rw [Fin.sum_univ_castSucc, hg'', mul_add, Finset.mul_sum]
      simp only [Fin.val_last, Fin.val_castSucc, Nat.sub_self, pow_zero, mul_one]
      have : ∀ j : Fin n, z * (algebraMap F.S R (c j.castSucc) * z ^ (n - ((j : ℕ) + 1))) =
          algebraMap F.S R (c j.castSucc) * z ^ (n + 1 - ((j : ℕ) + 1)) := fun j => by
        have hj := j.2
        rw [show n + 1 - ((j : ℕ) + 1) = (n - ((j : ℕ) + 1)) + 1 by omega, pow_succ]
        ring
      simp only [this]
      ring
    rw [hsplit] at hg
    have hlast : c (Fin.last n) ∈ (Q.comap (algebraMap F.S R)) ^ (n + 1) := by
      refine mem_comap_pow_of_mem_pow_sup F z hzF hr Q hzQ (n + 1) _ ?_
      have h1 : algebraMap F.S R (c (Fin.last n)) =
          (z * g'' + algebraMap F.S R (c (Fin.last n))) - z * g'' := by ring
      rw [h1]
      exact Ideal.sub_mem _ (Ideal.mem_sup_left hg)
        (Ideal.mem_sup_right (Ideal.mul_mem_right _ _ (Ideal.subset_span rfl)))
    have hlastQ : algebraMap F.S R (c (Fin.last n)) ∈ Q ^ (n + 1) := by
      have h := Ideal.mem_map_of_mem (algebraMap F.S R) hlast
      rw [Ideal.map_pow] at h
      exact Ideal.pow_right_mono Ideal.map_comap_le _ h
    have hzg : z * g'' ∈ Q ^ (n + 1) := by
      have : z * g'' = (z * g'' + algebraMap F.S R (c (Fin.last n))) -
          algebraMap F.S R (c (Fin.last n)) := by ring
      rw [this]
      exact Ideal.sub_mem _ hg hlastQ
    have hg''Q : g'' ∈ Q ^ n := by
      refine Ideal.mem_pow_of_le_ordElem (I := Q) ?_
      have h1 : ((n + 1 : ℕ) : ℕ∞) ≤ Ideal.ordElem Q (z * g'') := Ideal.le_ordElem hzg
      rw [ordElem_mul_of_isDomain, hordz] at h1
      have h2 : ((n : ℕ) : ℕ∞) + 1 ≤ 1 + Ideal.ordElem Q g'' := by
        simpa [add_comm] using h1
      rw [add_comm (1 : ℕ∞)] at h2
      exact (ENat.add_le_add_iff_right (by norm_num)).mp h2
    have ih' := ih (fun i => c i.castSucc) (by simpa [hg''] using hg''Q)
    induction i using Fin.lastCases with
    | last => simpa using hlast
    | cast i => simpa using ih' i

/-- Nakayama: if `T(z) = x_{R₁} ζ` with `ζ ∈ M₁`, some element of `Q ∩ S` generates `Q R₁`. -/
theorem exists_mem_comap_mul_unit {R : Type u} [CommRing R] [IsRegularLocalRing R] [IsDomain R]
    (F : RegularFrame R) (z : R) (hzF : ∀ j, F.z j = z) (hr : F.r = 1) (Q : Ideal R)
    (hzQ : z ∈ Q) (T : MonoidalTransform R Q) [IsLocalHom T.toRing]
    (ζ : T.ring) (hζ : T.toRing z = T.xR * ζ) (hζm : ζ ∈ maximalIdeal T.ring) :
    ∃ x : F.S, algebraMap F.S R x ∈ Q ∧ ∃ ε : T.ringˣ,
      T.toRing (algebraMap F.S R x) = T.xR * ε := by
  classical
  by_contra hcon
  push Not at hcon
  have hw := T.span_xR_eq_map
  have hw0 : T.xR ≠ 0 := fun h0 => T.x_ne_zero (T.toRing_injective (by
    rw [map_zero]; exact h0))
  have hx : ∀ x : F.S, algebraMap F.S R x ∈ Q → ∃ e ∈ maximalIdeal T.ring,
      T.toRing (algebraMap F.S R x) = T.xR * e := by
    intro x hx
    have hmem : T.toRing (algebraMap F.S R x) ∈ Ideal.span {T.xR} := by
      rw [hw]; exact Ideal.mem_map_of_mem _ hx
    obtain ⟨e, he⟩ := Ideal.mem_span_singleton'.mp hmem
    refine ⟨e, ?_, by rw [← he, mul_comm]⟩
    by_contra hem
    have hu := IsLocalRing.notMem_maximalIdeal.mp hem
    exact hcon x hx hu.unit (by rw [IsUnit.unit_spec, ← he, mul_comm])
  set P' := Q.comap (algebraMap F.S R) with hP'
  have hle : P'.map (T.toRing.comp (algebraMap F.S R)) ≤
      Ideal.span {T.xR} * maximalIdeal T.ring := by
    rw [Ideal.map_le_iff_le_comap]
    intro p hp
    obtain ⟨e, he, hpe⟩ := hx p (Ideal.mem_comap.mp hp)
    rw [Ideal.mem_comap]
    show T.toRing (algebraMap F.S R p) ∈ _
    rw [hpe]
    exact Ideal.mul_mem_mul (Ideal.mem_span_singleton_self _) he
  have hwQ : T.xR ∈ Q.map T.toRing := hw ▸ Ideal.mem_span_singleton_self _
  have hwQ' : T.xR ∈ Ideal.span {T.toRing z} ⊔ P'.map (T.toRing.comp (algebraMap F.S R)) := by
    have h1 := Ideal.map_mono (f := T.toRing) (eq_span_sup_map_comap_of_mem F z hzF hr Q hzQ).le
    have h2 : Ideal.map T.toRing (Ideal.span {z} ⊔ P'.map (algebraMap F.S R)) =
        Ideal.span {T.toRing z} ⊔ P'.map (T.toRing.comp (algebraMap F.S R)) := by
      rw [Ideal.map_sup, Ideal.map_span, Set.image_singleton, Ideal.map_map]
    exact h2 ▸ h1 hwQ
  obtain ⟨a', ha', p, hp, hap⟩ := Submodule.mem_sup.mp hwQ'
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp ha'
  have hp' := hle hp
  rw [mul_comm, Ideal.mem_mul_span_singleton] at hp'
  obtain ⟨e, he, hep⟩ := hp'
  have h1 : (c * ζ + e - 1) * T.xR = 0 := by
    have : T.xR = c * (T.xR * ζ) + e * T.xR := by rw [← hζ, hc, hep, hap]
    calc (c * ζ + e - 1) * T.xR = c * (T.xR * ζ) + e * T.xR - T.xR := by ring
      _ = 0 := by rw [← this, sub_self]
  rcases mul_eq_zero.mp h1 with h0 | h0
  · have h2 : (1 : T.ring) = c * ζ + e := by
      rw [sub_eq_zero] at h0; exact h0.symm
    have : (1 : T.ring) ∈ maximalIdeal T.ring := by
      rw [h2]; exact add_mem (Ideal.mul_mem_left _ _ hζm) he
    exact (IsLocalRing.maximalIdeal.isMaximal T.ring).ne_top ((Ideal.eq_top_iff_one _).mpr this)
  · exact hw0 h0

/-- **The frame transform of `(T_t; z_t)` in `Ŝ_{t+1}`** (p. 300, ring level): let `(S; z)` be a
regular frame (`r = 1`) of `R`, `Q ∋ z` a prime of `R` with `R/Q` regular, `R₁` a monoidal
transform of `R` with center `Q`, and suppose `z = x_{R₁} ζ` with `ζ ∈ M₁`.  Then `(S; z)` admits
a frame transform `(S₁; z₁)` in `R₁` with a denominator `v ∈ S` (`v = x_S`, `(v)R₁ = QR₁`,
`z = v z₁`), and every element `c ∈ (Q ∩ S)^n` is `c₁ v^n` with `c₁ ∈ S₁` ("`g_{jki}(t)/v_t^i =
g_{jki}(t + 1)`", p. 301). -/
theorem exists_frameTransform_of_mem_maximalIdeal {R : Type u} [CommRing R]
    [IsRegularLocalRing R] [IsDomain R] (F : RegularFrame R) (z : R) (hzF : ∀ j, F.z j = z)
    (hr : F.r = 1) (Q : Ideal R) [Q.IsPrime] [IsRegularLocalRing (R ⧸ Q)] (hzQ : z ∈ Q)
    (T : MonoidalTransform R Q) [IsLocalHom T.toRing] [IsRegularLocalRing T.ring]
    (ζ : T.ring) (hζ : T.toRing z = T.xR * ζ) (hζm : ζ ∈ maximalIdeal T.ring) :
    ∃ (F' : RegularFrame T.ring) (z' : T.ring) (c₀ : F'.S), F'.r = 1 ∧ (∀ j, F'.z j = z') ∧
      Ideal.span {algebraMap F'.S T.ring c₀} = Q.map T.toRing ∧
      T.toRing z = algebraMap F'.S T.ring c₀ * z' ∧ c₀ ≠ 0 ∧
      ∀ (n : ℕ) (c : F.S), c ∈ (Q.comap (algebraMap F.S R)) ^ n →
        ∃ c' : F'.S, T.toRing (algebraMap F.S R c) =
          algebraMap F'.S T.ring c' * (algebraMap F'.S T.ring c₀) ^ n := by
  classical
  have hdomT := isDomain_of_isRegularLocalRing T.ring
  have hw := T.span_xR_eq_map
  set w := T.xR with hwdef
  obtain ⟨x₀, hx₀Q, ε, hε⟩ := exists_mem_comap_mul_unit F z hzF hr Q hzQ T ζ hζ hζm
  have hadm : F.AdmitsFrameTransform T := by
    rw [RegularFrame.admitsFrameTransform_iff]
    refine ⟨x₀, hx₀Q, ?_, fun _ => (↑ε⁻¹ : T.ring) * ζ, fun j => ?_, fun j => ?_⟩
    · rw [hε, ← hw, Ideal.span_singleton_mul_right_unit ε.isUnit]
    · rw [hε, hzF j, hζ]
      calc w * ↑ε * (↑ε⁻¹ * ζ) = w * (↑ε * ↑ε⁻¹) * ζ := by ring
        _ = w * ζ := by rw [Units.mul_inv, mul_one]
    · intro hu
      have := IsLocalRing.notMem_maximalIdeal.mpr hu
      exact this (Ideal.mul_mem_left _ _ hζm)
  obtain ⟨FT⟩ := hadm
  have := F.isDomain_S
  have := FT.isRegular
  set TS := FT.TS with hTS
  set β := FT.β with hβ
  have hcomm : ∀ s : F.S, β (TS.toRing s) = T.toRing (algebraMap F.S R s) := fun s =>
    RingHom.congr_fun FT.canonical.comm s
  -- the image `ξ` of `x_S` generates `(Q ∩ S) R₁ = Q R₁`
  set ξ : T.ring := T.toRing (algebraMap F.S R TS.x) with hξ
  have hξspan : Ideal.span {ξ} =
      (Q.comap (algebraMap F.S R)).map (T.toRing.comp (algebraMap F.S R)) := by
    have h1 : ξ = β TS.xR := (hcomm TS.x).symm
    have h2 : (Q.comap (algebraMap F.S R)).map (T.toRing.comp (algebraMap F.S R)) =
        (Q.comap (algebraMap F.S R)).map (β.comp TS.toRing) := by
      congr 1; exact (RingHom.ext fun s => (hcomm s).symm)
    rw [h2, ← Ideal.map_map, ← TS.span_xR_eq_map, Ideal.map_span, Set.image_singleton, h1]
  have hξ0 : ξ ≠ 0 := by
    have hinjS : Function.Injective (algebraMap F.S R) := fun a b hab =>
      F.quot_bijective.1 (by simp only [RingHom.comp_apply]; rw [hab])
    exact fun h0 => TS.x_ne_zero (hinjS (T.toRing_injective (by
      rw [← hξ, h0, map_zero, map_zero])))
  have hξw : Ideal.span {ξ} = Ideal.span {w} := by
    rw [hw]
    refine le_antisymm ?_ ?_
    · rw [Ideal.span_le, Set.singleton_subset_iff]
      exact Ideal.mem_map_of_mem _ (Ideal.mem_comap.mp TS.x_mem)
    · rw [← hw, Ideal.span_le, Set.singleton_subset_iff]
      have h1 : T.toRing (algebraMap F.S R x₀) ∈ Ideal.span {ξ} := by
        rw [hξspan]
        exact Ideal.mem_map_of_mem _ (Ideal.mem_comap.mpr hx₀Q)
      have : w = (↑ε⁻¹ : T.ring) * T.toRing (algebraMap F.S R x₀) := by
        rw [hε]
        calc w = w * (↑ε * ↑ε⁻¹) := by rw [Units.mul_inv, mul_one]
          _ = ↑ε⁻¹ * (w * ↑ε) := by ring
      rw [this]
      exact Ideal.mul_mem_left _ _ h1
  obtain ⟨v, hv⟩ := Ideal.span_singleton_eq_span_singleton.mp hξw
  -- `z' = z/ξ`
  set z' : T.ring := (v : T.ring) * ζ with hz'
  have hξz' : ξ * z' = T.toRing z := by
    rw [hζ, hz', ← mul_assoc, hv]
  -- the denominator of `FT` is associated to `ξ`
  have hFTx : Ideal.span {FT.x} = Ideal.span {ξ} := by rw [FT.span_x, ← hw, hξw]
  obtain ⟨u₂, hu₂⟩ := Ideal.span_singleton_eq_span_singleton.mp hFTx.symm
  have hFTx0 : FT.x ≠ 0 := by rw [← hu₂]; exact mul_ne_zero hξ0 u₂.ne_zero
  let j0 : Fin F.r := ⟨0, by rw [hr]; exact Nat.one_pos⟩
  have hFTw : ∀ j, FT.w j = FT.w j0 := fun j => by
    apply mul_left_cancel₀ hFTx0
    rw [FT.mul_w, FT.mul_w, hzF j, hzF j0]
  have hz'eq : FT.w j0 * (u₂ : T.ring) = z' := by
    apply mul_left_cancel₀ hξ0
    rw [hξz']
    calc ξ * (FT.w j0 * ↑u₂) = (ξ * ↑u₂) * FT.w j0 := by ring
      _ = T.toRing z := by rw [hu₂, FT.mul_w, hzF j0]
  have hassoc : Associated z' (FT.w j0) := (Associated.symm ⟨u₂, hz'eq⟩)
  have hFTrange : Set.range FT.w = {FT.w j0} := by
    ext a
    simp only [Set.mem_range, Set.mem_singleton_iff]
    exact ⟨fun ⟨j, hj⟩ => hj ▸ hFTw j, fun h => ⟨j0, h.symm⟩⟩
  have hspanz' : Ideal.span {FT.w j0} = Ideal.span {z'} :=
    Ideal.span_singleton_eq_span_singleton.mpr hassoc.symm
  have hext : ExtendsToRSOP T.ring (Finset.image (fun _ : Fin 1 => z') Finset.univ) := by
    have h1 := ExtendsToRSOP.image_of_associated FT.extends_rsop (fun _ => z')
      (fun a ha b hb _ => by
        obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp ha
        obtain ⟨j', -, rfl⟩ := Finset.mem_image.mp hb
        rw [hFTw j, hFTw j']) (fun k hk => by
        obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hk
        rw [hFTw j]; exact hassoc.symm)
    have hne : (Finset.image FT.w Finset.univ).Nonempty := ⟨FT.w j0, Finset.mem_image.mpr ⟨j0,
        Finset.mem_univ _, rfl⟩⟩
    rwa [Finset.image_const hne, ← Finset.image_const (s := (Finset.univ : Finset (Fin 1)))
      Finset.univ_nonempty] at h1
  have hquot : Function.Bijective ((Ideal.Quotient.mk (Ideal.span (Set.range fun _ : Fin 1 =>
      z'))).comp β) := by
    have h1 := FT.quot_bijective
    rw [hFTrange] at h1
    have h2 : Set.range (fun _ : Fin 1 => z') = {z'} := Set.range_const
    rw [h2, ← hspanz']
    exact h1
  have hxR0 : TS.xR ≠ 0 := by
    intro h0
    apply TS.x_ne_zero
    apply TS.toRing_injective
    rw [map_zero]
    exact h0
  have hβxR : β TS.xR = ξ := hcomm TS.x
  refine ⟨{ S := TS.ring
            algebra := β.toAlgebra
            isLocalHom := FT.canonical.isLocalHom
            r := 1
            z := fun _ => z'
            z_injective := Function.injective_of_subsingleton _
            extends_rsop := hext
            quot_bijective := hquot }, z', TS.xR, rfl, fun _ => rfl, ?_, ?_, hxR0, ?_⟩
  · show Ideal.span {β TS.xR} = _
    rw [hβxR, hξw, hw]
  · show T.toRing z = β TS.xR * z'
    rw [hβxR, hξz']
  · intro n c hc
    have h1 := Ideal.mem_map_of_mem TS.toRing hc
    rw [Ideal.map_pow, ← TS.span_xR_eq_map, Ideal.span_singleton_pow,
      Ideal.mem_span_singleton'] at h1
    obtain ⟨c', hc'⟩ := h1
    refine ⟨c', ?_⟩
    show T.toRing (algebraMap F.S R c) = β c' * (β TS.xR) ^ n
    rw [← hcomm, ← hc', map_mul, map_pow]

end RegularFrame

/-- The initial form of a unit `u` is the image of its class `ū ∈ k = A/M` in `gr_M(A)` (the
argument of the private `initialForm_unit_aux` of `Hironaka/Ch3/JStability.lean`). -/
theorem initialForm_maximalIdeal_unit {A : Type u} [CommRing A] [IsRegularLocalRing A] (u : Aˣ) :
    initialForm (maximalIdeal A) (u : A) =
      algebraMap (A ⧸ maximalIdeal A) (AssocGraded (maximalIdeal A))
        (Ideal.Quotient.mk (maximalIdeal A) u) := by
  have h0 : Ideal.ordElem (maximalIdeal A) (u : A) = ((0 : ℕ) : ℕ∞) := by
    refine le_antisymm (Ideal.ordElem_le_of_notMem ?_) (by simp)
    rw [zero_add, pow_one]
    exact fun h => (maximalIdeal.isMaximal A).ne_top (Ideal.eq_top_of_isUnit_mem _ h u.isUnit)
  rw [initialForm_eq_mk _ h0]
  show AssocGraded.mk _ 0 _ _ = AssocGraded.algebraMapQuot _ (Ideal.Quotient.mk _ _)
  rw [AssocGraded.algebraMapQuot, Ideal.Quotient.lift_mk, AssocGraded.algebraMap_apply,
    AssocGraded.mk]
  congr 1

/-- Multiplying the members of a standard base by units gives a standard base (the initial forms
change by non-zero constants of `k`); the argument of the private `isStandardBase_of_unit_mul_aux`
of `Hironaka/Ch3/JStability.lean`. -/
theorem IsStandardBase.of_unit_mul {A : Type u} [CommRing A] [IsRegularLocalRing A]
    {J : Ideal A} {m : ℕ} {f f' : Fin m → A} (hf : IsStandardBase A J f) (u : Fin m → Aˣ)
    (hu : ∀ j, f' j = u j * f j) : IsStandardBase A J f' := by
  have hfwd : ∀ j, initialForm (maximalIdeal A) (f' j) =
      Ideal.Quotient.mk (maximalIdeal A) (u j : A) • initialForm (maximalIdeal A) (f j) :=
    fun j => by
      rw [hu j, initialForm_mul_maximalIdeal, Algebra.smul_def, ← initialForm_maximalIdeal_unit]
  have hbwd : ∀ j, initialForm (maximalIdeal A) (f j) =
      initialForm (maximalIdeal A) (((u j)⁻¹ : Aˣ) : A) * initialForm (maximalIdeal A) (f' j) :=
    fun j => by
      rw [← initialForm_mul_maximalIdeal, hu j, ← mul_assoc, ← Units.val_mul, inv_mul_cancel,
        Units.val_one, one_mul]
  have hle : ∀ {n : ℕ} (ψ χ : Fin n → AssocGraded (maximalIdeal A)),
      (∀ j, ∃ a, ψ j = a * χ j) → Ideal.span (Set.range ψ) ≤ Ideal.span (Set.range χ) := by
    intro n ψ χ h
    rw [Ideal.span_le]
    rintro _ ⟨j, rfl⟩
    obtain ⟨a, ha⟩ := h j
    rw [SetLike.mem_coe, ha]
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨j, rfl⟩)
  have hfwd' : ∀ j, ∃ a, initialForm (maximalIdeal A) (f' j) =
      a * initialForm (maximalIdeal A) (f j) := fun j =>
    ⟨_, (hfwd j).trans (Algebra.smul_def _ _)⟩
  have hbwd' : ∀ j, ∃ a, initialForm (maximalIdeal A) (f j) =
      a * initialForm (maximalIdeal A) (f' j) := fun j => ⟨_, hbwd j⟩
  obtain ⟨hJ, hin, ⟨d, hd, hmono⟩, hspan, hiii⟩ := hf
  refine ⟨fun j => (hu j) ▸ J.mul_mem_left _ (hJ j), fun j => ?_, ⟨d, fun j => ?_, hmono⟩,
    hspan.trans (le_antisymm (hle _ _ hbwd') (hle _ _ hfwd')), fun i h => hiii i ?_⟩
  · beta_reduce
    rw [hfwd j]
    exact Submodule.smul_of_tower_mem _ _ (hin j)
  · beta_reduce
    rw [hfwd j]
    exact Submodule.smul_mem _ _ (hd j)
  · have h' := hle (fun j : Fin i => initialForm (maximalIdeal A) (f' (Fin.castLE i.2.le j)))
      (fun j : Fin i => initialForm (maximalIdeal A) (f (Fin.castLE i.2.le j)))
      (fun j => hfwd' _) h
    beta_reduce
    rw [hbwd i]
    exact Ideal.mul_mem_left _ _ h'

end

end Hironaka
