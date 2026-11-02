/-
Copyright (c) 2026 Daattavya Aggarwal, Minhyong Kim, Oisin Kim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daattavya Aggarwal, Minhyong Kim, Oisin Kim
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Architect
public import Hironaka.Compat.LocalizeSuccession

/-!
# Compatibility layer for Ch. IV §1: localizing and lifting successions, type II

Propositions 3 and 4 of Ch. IV §1 (pp. 282–286) repeat the construction of Propositions 1 and 2
(`Hironaka/Compat/LocalizeSuccession.lean`) for resolution data of type `ℜ^N_II`.  This file
collects what is specific to type II.

* Lemma 8 of Ch. III §3 (`lem:III.8`) for every monoidal transform of a regular local ring (the
  lemma assumes the transform residually algebraic; a general one is a localization of a
  residually algebraic one, and Theorem 1 of Ch. III §3, `thm:III.1`, compares the two), and its
  consequences for a permissible monoidal transformation `f` of a type II datum, which the paper
  lists on p. 283: `ν(J'_{x'}) ≤ ν(J_{f(x')})`, `f(S_i(f*ℜ)) ⊆ S_i(ℜ)` and `ν(f*ℜ) ≤ ν(ℜ)`.
* The closedness of the sets `S(ℜ)` and `{x | ν(J_x) ≥ c}` (the argument of Lemma 2 of
  Ch. IV §1, `lem:IV.1-2`).
* The pull-back of a type II datum along a flat preimmersion (for the canonical immersion
  `X'_S → X'` this is Definition 1 (II), p. 276), and data with the same "essential
  characteristics" (p. 275): the non-empty `E_i`, the integers `a(E) = ∑_{E_i = E} a_i`, `J` and
  `b`.  The pull-back of the transform of a datum by a monoidal transformation whose center misses
  the localization is the pull-back of the datum only up to such an identification (the new
  exceptional component pulls back to the empty subscheme).
* The lifting construction of pp. 283–285: the permissibility of the succession `h` for `_bℜ'` with
  the printed invariants (`isPermissibleIIClosed_of_isPermissibleIOpen_of_nonempty`), the lifting of
  one monoidal transformation of `X'_S` (`lift_transformationII`, `lift_stepII`), the choice of a
  minimal `a` ("we may assume that this last condition is not satisfied if we omit the last
  transformation", `MonoidalSuccession.IsMinimalSNuEmptyIIClosed`), and the lifting of the whole
  succession (`lift_successionII`).
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace IsLocalRing

namespace Hironaka

universe u

/-! ### `ν` under ring isomorphisms, and Lemma 8 for all monoidal transforms -/

namespace LocSucc

/-- `ν` is invariant under ring isomorphisms of local rings. -/
theorem nu_map_ringEquiv {A B : Type*} [CommRing A] [CommRing B] [IsLocalRing A] [IsLocalRing B]
    (e : A ≃+* B) (I : Ideal A) : Ideal.nu (I.map (e : A →+* B)) = Ideal.nu I := by
  have hM : (maximalIdeal A).map (e : A →+* B) = maximalIdeal B := by
    ext b
    rw [Ideal.map_comap_of_equiv, Ideal.mem_comap, mem_maximalIdeal, mem_maximalIdeal,
      mem_nonunits_iff, mem_nonunits_iff]
    exact not_congr (MulEquiv.isUnit_map (e.symm : B ≃* A))
  have key : ∀ n : ℕ, I.map (e : A →+* B) ≤ maximalIdeal B ^ n ↔ I ≤ maximalIdeal A ^ n := by
    intro n
    rw [← hM, ← Ideal.map_pow, Ideal.map_comap_of_equiv, Ideal.map_comap_of_equiv]
    exact Ideal.comap_le_comap_iff_of_surjective _ e.symm.surjective _ _
  unfold Ideal.nu Ideal.ord
  exact iSup_congr fun n => iSup_congr_Prop (key n) fun _ => rfl

/-- `ν` is invariant under ring isomorphisms of local rings. -/
theorem nu_map_ringEquiv_of_equivLike {A B : Type*} [CommRing A] [CommRing B] [IsLocalRing A]
    [IsLocalRing B] (e : A ≃+* B) (I : Ideal A) : Ideal.nu (I.map e) = Ideal.nu I := by
  rw [← Ideal.map_coe]
  exact nu_map_ringEquiv e I

/-- `ν` is antitone. -/
theorem nu_anti {A : Type*} [CommRing A] [IsLocalRing A] {I J : Ideal A} (h : I ≤ J) :
    Ideal.nu J ≤ Ideal.nu I :=
  (Ideal.ord_basic (maximalIdeal A) ⊥ I J).2.2.1 h

section Lemma8

/-- Theorem 1 of Ch. III §3 (`thm:III.1`, Zariski–Nagata) along an injective local homomorphism
`ψ : S → T` which makes `T` a localization of `S` at a prime (every element of `T` is a quotient
`ψ(a)/ψ(s)` with `ψ(s)` a unit): `ν(IT) ≤ ν(I)`. -/
theorem nu_map_le_of_isLocalization [Hironaka.Cited.CurveFiniteIntegralClosure.{u}] [Hironaka.Cited.IsRegularLocalRingLocalizationOfIsRegularLocalRing.{u}] {S T : Type u} [CommRing S] [IsRegularLocalRing S]
    [CommRing T] [IsLocalRing T] (ψ : S →+* T) (hψ : Function.Injective ψ)
    (hsurj : ∀ z : T, ∃ a s : S, IsUnit (ψ s) ∧ z * ψ s = ψ a) (I : Ideal S) (hI : I ≠ ⊥) :
    Ideal.nu (I.map ψ) ≤ Ideal.nu I := by
  let _ : Algebra S T := ψ.toAlgebra
  let Q : Ideal S := (maximalIdeal T).comap ψ
  have : Q.IsPrime := Ideal.comap_isPrime ψ (maximalIdeal T)
  have hQ : ∀ s : S, IsUnit (ψ s) → s ∈ Q.primeCompl := fun s hs hsQ =>
    (mem_maximalIdeal _).mp hsQ hs
  have : IsLocalization.AtPrime T Q :=
    { map_units := fun y => by
        have hy : ψ (y : S) ∉ maximalIdeal T := y.2
        rw [mem_maximalIdeal, mem_nonunits_iff, not_not] at hy
        exact hy
      surj := fun z => by
        obtain ⟨a, s, hs, hz⟩ := hsurj z
        exact ⟨⟨a, ⟨s, hQ s hs⟩⟩, hz⟩
      exists_of_eq := fun {x y} h => ⟨1, by rw [hψ h]⟩ }
  let e : Localization.AtPrime Q ≃ₐ[S] T := IsLocalization.algEquiv Q.primeCompl _ _
  have he : (e.toRingEquiv : Localization.AtPrime Q →+* T).comp
      (algebraMap S (Localization.AtPrime Q)) = ψ := by
    ext s
    exact e.commutes s
  calc Ideal.nu (I.map ψ)
      = Ideal.nu ((I.map (algebraMap S (Localization.AtPrime Q))).map
          (e.toRingEquiv : Localization.AtPrime Q →+* T)) := by
        rw [Ideal.map_map, he]
    _ = Ideal.nu (I.map (algebraMap S (Localization.AtPrime Q))) := nu_map_ringEquiv _ _
    _ ≤ Ideal.nu I := nu_localization_le S I hI Q

variable {R : Type u} [CommRing R] [IsRegularLocalRing R] [IsDomain R] {P : Ideal R}

/-- Lemma 8 of Ch. III §3 (`lem:III.8`, p. 217) for every monoidal transform: if `R/P` is regular
and `ν_P(J) = ν(J)`, then `ν(J') ≤ ν(J)` for the weak transform `J'` of `J` in any monoidal
transform `R'` of `R` with center `P`.

The lemma is stated for `R'` residually algebraic over `R`.  In general `R' = R[x⁻¹P]_{M'}` is a
localization of `R'' = R[x⁻¹P]_{M''}`, `M'' ⊇ M'` a maximal ideal, and `R''` is residually
algebraic over `R` (`MonoidalTransform.isMaximal_iff_isResiduallyAlgebraic`).  The weak
transform of `J` in `R'` contains the ideal generated by that in `R''`; so
`ν(J'_{R'}) ≤ ν(J'_{R''} R') ≤ ν(J'_{R''}) ≤ ν(J)` by Theorem 1 (`thm:III.1`) and Lemma 8.

Correction of the paper (proof): p. 283 of Ch. IV §1 invokes Lemma 8 for every point `x'` of
`X'`, although the lemma (p. 217) assumes `R'` residually algebraic over `R`; this extension
supplies the missing case. -/
theorem nu_weakTransformIdeal_le [Hironaka.Cited.CurveFiniteIntegralClosure.{u}] [Hironaka.Cited.IsRegularLocalRingLocalizationOfIsRegularLocalRing.{u}] (J : Ideal R) (hJ : J ≠ ⊥) (hP : P.IsPrime)
    (hS : IsRegularLocalRing (R ⧸ P)) (hPJ : Ideal.ord P J = Ideal.nu J)
    (t : MonoidalTransform R P) :
    Ideal.nu (weakTransformIdeal t J) ≤ Ideal.nu J := by
  classical
  obtain ⟨M'', hM'', hle⟩ := Ideal.exists_le_maximal t.M' (Ideal.IsPrime.ne_top t.isPrime)
  let t'' : MonoidalTransform R P :=
    { x := t.x, x_mem := t.x_mem, x_ne_zero := t.x_ne_zero, M' := M'', isPrime := hM''.isPrime,
      le := t.le.trans hle }
  have hP0 : P ≠ ⊥ := fun h => t.x_ne_zero (by simpa [h] using t.x_mem)
  obtain ⟨hreg'', -, -⟩ := t''.isRegularLocalRing_and_isLocalHom_and_span_xR_eq_map hP hP0 hS
  have halg := (t''.isMaximal_iff_isResiduallyAlgebraic).mp hM''
  have := hP
  have := hS
  have h8 := nu_weakTransform_le R J hJ P hPJ t'' halg
  -- the canonical homomorphism `R'' → R'`
  have : IsLocalization t''.M'.primeCompl t''.ring :=
    MonoidalTransform.instAtPrimeSubtypeFractionRingMemSubalgebraBlowupAlgebraXRingM' t''
  let g : blowupAlgebra R P t''.x →+* t.ring := algebraMap (blowupAlgebra R P t.x) t.ring
  have hg : ∀ y : t''.M'.primeCompl, IsUnit (g y) := fun y =>
    IsLocalization.map_units (M := t.M'.primeCompl) t.ring ⟨y, fun h => y.2 (hle h)⟩
  let ψ : t''.ring →+* t.ring := IsLocalization.lift (M := t''.M'.primeCompl) hg
  have hψ : ∀ a, ψ (algebraMap (blowupAlgebra R P t''.x) t''.ring a) = g a :=
    IsLocalization.lift_eq hg
  have hψt : ψ.comp t''.toRing = t.toRing := by
    ext r
    exact hψ _
  have hginj : Function.Injective g :=
    IsLocalization.injective (M := t.M'.primeCompl) t.ring
      (Ideal.primeCompl_le_nonZeroDivisors t.M')
  have hψinj : Function.Injective ψ := by
    refine (injective_iff_map_eq_zero ψ).mpr fun z hz => ?_
    obtain ⟨⟨a, s⟩, hzs⟩ := IsLocalization.surj t''.M'.primeCompl z
    have h1 : g a = 0 := by
      rw [← hψ, ← hzs, map_mul, hz, zero_mul]
    rw [hginj (h1.trans (map_zero g).symm), map_zero] at hzs
    exact (IsLocalization.map_units t''.ring s).mul_left_eq_zero.mp hzs
  have hsurj : ∀ z : t.ring, ∃ a s : t''.ring, IsUnit (ψ s) ∧ z * ψ s = ψ a := by
    intro z
    obtain ⟨⟨a, m⟩, hz⟩ := IsLocalization.surj t.M'.primeCompl z
    refine ⟨algebraMap (blowupAlgebra R P t''.x) t''.ring a,
      algebraMap (blowupAlgebra R P t''.x) t''.ring m, ?_, ?_⟩
    · rw [hψ]
      exact IsLocalization.map_units t.ring m
    · rw [hψ, hψ]
      exact hz
  -- `J'_{R''} R' ⊆ J'_{R'}`
  have hincl : (weakTransformIdeal t'' J).map ψ ≤ weakTransformIdeal t J := by
    rw [weakTransformIdeal, Ideal.map_span, Ideal.span_le]
    rintro _ ⟨y, ⟨x', hx', f, hf, ν, hν, hy⟩, rfl⟩
    refine Ideal.subset_span ⟨ψ x', ?_, f, hf, ν, hν, ?_⟩
    · rw [← Set.image_singleton, ← Ideal.map_span, hx', Ideal.map_map, hψt]
    · rw [← map_pow, ← map_mul, hy, ← RingHom.comp_apply, hψt]
  -- `J'_{R''} ≠ 0`
  have hne : weakTransformIdeal t'' J ≠ ⊥ := by
    obtain ⟨f, hfJ, hf0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hJ
    intro hbot
    have hmem : t''.toRing f ∈ weakTransformIdeal t'' J :=
      Ideal.subset_span ⟨t''.xR, t''.span_xR_eq_map, f, hfJ, 0, zero_le, by simp⟩
    rw [hbot, Submodule.mem_bot] at hmem
    exact hf0 (MonoidalTransform.toRing_injective t'' (by rw [hmem, map_zero]))
  calc Ideal.nu (weakTransformIdeal t J)
      ≤ Ideal.nu ((weakTransformIdeal t'' J).map ψ) :=
        nu_anti hincl
    _ ≤ Ideal.nu (weakTransformIdeal t'' J) :=
        nu_map_le_of_isLocalization ψ hψinj hsurj _ hne
    _ ≤ Ideal.nu J := h8

end Lemma8

end LocSucc

/-! ### Lemma 2 (p. 278) along the printed route: `J' = ∏ P_i^{a_i} J` and `ν(J'_x)`

The proof of Lemma 2 (p. 278) forms `J' = ∏ P_i^{a_i} J` and states
`S(ℜ^N_II) = {x ∈ X | ν(J'_x) ≥ b}`.  This uses, without comment, `ν(P_{i,x}) = 1` for `x ∈ E_i`
(and `0` for `x ∉ E_i`) and the additivity `ν(IK) = ν(I) + ν(K)` of `ν` for ideals of the regular
local ring `O_{X,x}`; both are proved here. -/

section Lemma2Helpers

variable {R : Type u} [CommRing R] [IsLocalRing R]

/-- The order of an ideal of finite order is attained by an element of the ideal. -/
theorem Ideal.exists_mem_ordElem_eq_nu (I : Ideal R) (hI : Ideal.nu I ≠ ⊤) :
    ∃ f ∈ I, Ideal.ordElem (maximalIdeal R) f = Ideal.nu I := by
  obtain ⟨n, hn⟩ : ∃ n : ℕ, Ideal.nu I = n := ⟨_, (ENat.natCast_toNat hI).symm⟩
  have hle : I ≤ maximalIdeal R ^ n := Ideal.le_pow_of_le_ord hn.ge
  by_contra h
  have hall : I ≤ maximalIdeal R ^ (n + 1) := by
    intro f hf
    refine Ideal.mem_pow_of_le_ordElem ?_
    have h1 : (n : ℕ∞) ≤ Ideal.ordElem (maximalIdeal R) f := Ideal.le_ordElem (hle hf)
    have h2 : Ideal.ordElem (maximalIdeal R) f ≠ n := fun h' => h ⟨f, hf, h'.trans hn.symm⟩
    have h3 : (n : ℕ∞) < Ideal.ordElem (maximalIdeal R) f := lt_of_le_of_ne h1 (Ne.symm h2)
    exact_mod_cast Order.add_one_le_of_lt h3
  have := Ideal.le_ord (M := maximalIdeal R) hall
  rw [← Ideal.nu, hn] at this
  exact absurd (by exact_mod_cast this : n + 1 ≤ n) (by omega)

/-- `ν(R) = 0`: the unit ideal is not contained in the maximal ideal. -/
theorem Ideal.nu_top_eq_zero : Ideal.nu (⊤ : Ideal R) = 0 := by
  refine le_antisymm (Ideal.ord_le fun n hn => ?_) zero_le
  by_contra hlt
  have hn1 : 1 ≤ n := by
    rcases Nat.eq_zero_or_pos n with h | h
    · exact absurd (by simp [h]) hlt
    · exact h
  have h1 : (1 : R) ∈ maximalIdeal R ^ n := hn (Submodule.mem_top : (1 : R) ∈ (⊤ : Ideal R))
  have h2 : maximalIdeal R ^ n ≤ maximalIdeal R :=
    (Ideal.pow_le_pow_right hn1).trans (pow_one _).le
  exact (maximalIdeal.isMaximal R).ne_top ((Ideal.eq_top_iff_one _).mpr (h2 h1))

end Lemma2Helpers

section Lemma2Regular

variable {R : Type u} [CommRing R] [IsRegularLocalRing R]

/-- **Additivity of `ν` on ideals** of a regular local ring: `ν(IK) = ν(I) + ν(K)`.  This is the
fact used without comment in the proof of Lemma 2 (p. 278): the inequality `≥` holds in any
local ring (`Ideal.ord_basic`); for `≤` take `f ∈ I` and `g ∈ K` of orders `ν(I)` and `ν(K)`:
`gr_M(R)` is a domain (`ordElem_mul_maximalIdeal`, Zariski–Samuel Ch. VIII, cited in footnote 3,
p. 116), so `fg ∈ IK` has order `ν(I) + ν(K)`. -/
theorem Ideal.nu_mul_eq (I K : Ideal R) : Ideal.nu (I * K) = Ideal.nu I + Ideal.nu K := by
  refine le_antisymm ?_ (Ideal.ord_basic _ ⊥ I K).2.2.2
  by_cases hI : Ideal.nu I = ⊤
  · rw [hI, top_add]; exact le_top
  by_cases hK : Ideal.nu K = ⊤
  · rw [hK, add_top]; exact le_top
  obtain ⟨f, hf, hfo⟩ := Ideal.exists_mem_ordElem_eq_nu I hI
  obtain ⟨g, hg, hgo⟩ := Ideal.exists_mem_ordElem_eq_nu K hK
  refine Ideal.ord_le fun k hk => ?_
  have h1 : (k : ℕ∞) ≤ Ideal.ordElem (maximalIdeal R) (f * g) :=
    Ideal.le_ordElem (hk (Ideal.mul_mem_mul hf hg))
  rwa [ordElem_mul_maximalIdeal, hfo, hgo] at h1

/-- `ν(I^k) = k ν(I)` in a regular local ring (from `Ideal.nu_mul_eq`). -/
theorem Ideal.nu_pow_eq (I : Ideal R) (k : ℕ) : Ideal.nu (I ^ k) = k * Ideal.nu I := by
  induction k with
  | zero => rw [pow_zero, Ideal.one_eq_top, Ideal.nu_top_eq_zero, Nat.cast_zero, zero_mul]
  | succ k ih => rw [pow_succ, Ideal.nu_mul_eq, ih]; push_cast; ring

/-- `ν` of a finite product of ideals of a regular local ring is the sum of the orders (from
`Ideal.nu_mul_eq`). -/
theorem Ideal.nu_prod_eq {ι : Type*} (s : Finset ι) (I : ι → Ideal R) :
    Ideal.nu (∏ i ∈ s, I i) = ∑ i ∈ s, Ideal.nu (I i) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.prod_empty, Finset.sum_empty, Ideal.one_eq_top, Ideal.nu_top_eq_zero]
  | insert i s hi ih => rw [Finset.prod_insert hi, Finset.sum_insert hi, Ideal.nu_mul_eq, ih]

end Lemma2Regular

section Lemma2Datum

variable {X : Scheme.{u}}

/-- The stalk of a finite product of ideal sheaves is the product of the stalks. -/
theorem Subscheme.stalkIdeal_prod {ι : Type*} (s : Finset ι) (f : ι → Subscheme X) (x : X) :
    (∏ i ∈ s, f i).stalkIdeal x = ∏ i ∈ s, (f i).stalkIdeal x := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    have : (1 : Subscheme X) = ⊤ := rfl
    rw [Finset.prod_empty, Finset.prod_empty, this, Subscheme.stalkIdeal_top_eq]
    exact Ideal.one_eq_top.symm
  | insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.prod_insert hi, Subscheme.stalkIdeal_mul_eq, ih]

/-- `ν(P_{i,x}) = 1` for `x ∈ E_i` (used without comment in the proof of Lemma 2, p. 278): at a
point `x` of a non-singular irreducible subscheme `E` of codimension one of a non-singular scheme,
`E_x` is a prime of height one with `O_{X,x}/E_x` regular, hence it is generated by part of a
regular system of parameters, so it contains an element outside `M²` and `E_x ⊆ M`. -/
theorem Subscheme.IsNonsingularIrreducibleCodimOne.nu_stalkIdeal_eq_one {E : Subscheme X}
    (hX : X.IsNonsingular) (hE : E.IsNonsingularIrreducibleCodimOne) {x : X} (hx : x ∈ E.pts) :
    Ideal.nu (E.stalkIdeal x) = 1 := by
  have : IsRegularLocalRing (X.presheaf.stalk x) := hX x
  rcases hE with rfl | ⟨hns, hirr, hcod⟩
  · rw [DatumTransform.pts_empty] at hx
    exact absurd hx (Set.notMem_empty x)
  have hP := Subscheme.isPrime_stalkIdeal_of_isNonsingular hns hx
  have hreg := Subscheme.isRegularLocalRing_quotient_of_isNonsingular hns hx
  have hht : (E.stalkIdeal x).height = 1 :=
    (Subscheme.codim_eq_height E hns hirr hx).symm.trans hcod
  have hne : E.stalkIdeal x ≠ ⊥ := fun h => by
    rw [h, Ideal.height_bot] at hht
    exact absurd hht (by simp)
  obtain ⟨S, T, hS, hScard, hTS, hT⟩ := exists_finset_span_eq_prime _ (E.stalkIdeal x) hreg
  have hSr : IsRegularSystemOfParameters _ S :=
    ⟨hS, by rw [hScard]; exact IsRegularLocalRing.spanFinrank_maximalIdeal⟩
  have hTe : ExtendsToRSOP _ T := ⟨S, hTS, hSr⟩
  have hTne : T.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    rintro rfl
    apply hne
    rw [← hT]
    simp
  obtain ⟨t, ht⟩ := hTne
  have htE : t ∈ E.stalkIdeal x := hT ▸ Ideal.subset_span ht
  apply le_antisymm
  · refine Ideal.ord_le fun n hn => ?_
    by_contra hlt
    have h2 : 2 ≤ n := by
      have : (1 : ℕ∞) < n := not_le.mp hlt
      exact_mod_cast this
    exact hTe.notMem_maximalIdeal_sq ht (Ideal.pow_le_pow_right h2 (hn htE))
  · exact (Ideal.ord_basic (maximalIdeal (X.presheaf.stalk x)) (E.stalkIdeal x) ⊥ ⊥).2.1.mpr
      (Subscheme.stalkIdeal_le_maximalIdeal E hx)

/-- **Corollary 1 of Theorem 2, Ch. III §3** (`cor:III.thm2-1`), in the form used in the proof of
Lemma 2 (p. 278): for a coherent sheaf of ideals `J` of a non-singular algebraic scheme `X`, the
set `{x ∈ X | ν(J_x) ≥ c}` is closed, being the complement of the open sets `{x | ν(J_x) ≤ n}`,
`n < c`. -/
theorem Subscheme.isClosed_setOf_le_nu_stalkIdeal [Hironaka.Cited.IsHironakaBaseIsClosedSingularLocus.{u}] [Hironaka.Cited.CurveFiniteIntegralClosure.{u}] [Hironaka.Cited.IsRegularLocalRingLocalizationOfIsRegularLocalRing.{u}] [IsAlgebraicScheme X] (hX : X.IsNonsingular)
    (J : Subscheme X) (c : ℕ∞) : IsClosed {x : X | c ≤ Ideal.nu (J.stalkIdeal x)} := by
  choose U hU hUiff using exists_isOpen_nu_stalk_le X hX J
  have heq : {x : X | c ≤ Ideal.nu (J.stalkIdeal x)} = ⋂ (n : ℕ) (_ : (n : ℕ∞) < c), (U n)ᶜ := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_iInter, Set.mem_compl_iff, hUiff, not_le]
    refine ⟨fun h n hn => hn.trans_le h, fun h => le_of_forall_lt fun d hd => ?_⟩
    induction d using ENat.recTopCoe with
    | top => exact absurd hd (not_lt.mpr le_top)
    | coe n => exact h n hd
  rw [heq]
  exact isClosed_iInter fun n => isClosed_iInter fun _ => (hU n).isClosed_compl

namespace DatumII.Raw

/-- The coherent sheaf of ideals `J' = ∏_{i=1}^α P_i^{a_i} J` of the proof of Lemma 2 (p. 278),
where `P_i` is the coherent sheaf of ideals of `E_i` on `X`. -/
noncomputable def jPrime (ℜ : Raw X) : Subscheme X := (∏ i, ℜ.E i ^ ℜ.a i) * ℜ.J

/-- The stalkwise formula behind "We have `S(ℜ^N_II) = {x ∈ X | ν(J'_x) ≥ b}`" (Lemma 2, p. 278):
`ν(J'_x) = ∑_{x ∈ E_i} a_i + ν(J_x)`.  Uses `ν(P_{i,x}) = 1` for `x ∈ E_i`, `ν(P_{i,x}) = 0` for
`x ∉ E_i` (`P_{i,x}` is then the unit ideal) and the additivity of `ν` in the regular local ring
`O_{X,x}` (`Ideal.nu_mul_eq`). -/
theorem nu_stalkIdeal_jPrime (hX : X.IsNonsingular) (ℜ : Raw X) (hℜ : ℜ.IsDatum) (x : X) :
    Ideal.nu (ℜ.jPrime.stalkIdeal x) = (ℜ.weight x : ℕ∞) + ℜ.nuAt x := by
  classical
  have : IsRegularLocalRing (X.presheaf.stalk x) := hX x
  have hi : ∀ i, Ideal.nu ((ℜ.E i).stalkIdeal x) = if x ∈ (ℜ.E i).pts then 1 else 0 := by
    intro i
    split_ifs with hx
    · exact (hℜ.2.1 i).nu_stalkIdeal_eq_one hX hx
    · rw [Subscheme.stalkIdeal_eq_top_of_notMem_pts hx, Ideal.nu_top_eq_zero]
  unfold jPrime
  rw [Subscheme.stalkIdeal_mul_eq, Subscheme.stalkIdeal_prod, Ideal.nu_mul_eq, Ideal.nu_prod_eq]
  simp only [Subscheme.stalkIdeal_pow_eq, Ideal.nu_pow_eq, hi]
  unfold weight
  rw [Nat.cast_sum, Finset.sum_filter]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  split_ifs <;> simp

/-- "We have `S(ℜ^N_II) = {x ∈ X | ν(J'_x) ≥ b}`" (Lemma 2, p. 278). -/
theorem S_eq_setOf_le_nu_jPrime (hX : X.IsNonsingular) (ℜ : Raw X) (hℜ : ℜ.IsDatum) :
    ℜ.S = {x | (ℜ.b : ℕ∞) ≤ Ideal.nu (ℜ.jPrime.stalkIdeal x)} := by
  ext x
  simp only [S, Set.mem_ofPred_eq]
  rw [nu_stalkIdeal_jPrime hX ℜ hℜ x]

/-- **Lemma 2, p. 278, closedness of `S(ℜ^N_II)`** along the printed route: "We have
`S(ℜ^N_II) = {x ∈ X | ν(J'_x) ≥ b}`, which is closed in `X` by Corollary 1 of Theorem 2 of §3,
Ch. III" (`S_eq_setOf_le_nu_jPrime` and `Subscheme.isClosed_setOf_le_nu_stalkIdeal`, the latter
applied to `J'`). -/
theorem isClosed_S_of_isDatum [Hironaka.Cited.IsHironakaBaseIsClosedSingularLocus.{u}] [Hironaka.Cited.CurveFiniteIntegralClosure.{u}] [Hironaka.Cited.IsRegularLocalRingLocalizationOfIsRegularLocalRing.{u}] [IsAlgebraicScheme X] (hX : X.IsNonsingular) (ℜ : Raw X)
    (hℜ : ℜ.IsDatum) : IsClosed ℜ.S := by
  rw [S_eq_setOf_le_nu_jPrime hX ℜ hℜ]
  exact Subscheme.isClosed_setOf_le_nu_stalkIdeal hX _ _

/-- **Lemma 2, p. 278, closedness of `S_c(ℜ^N_II)`, in particular of `S_*(ℜ^N_II)`** along the
printed route: "We have `S_*(ℜ^N_II) = S(ℜ^N_II) ∩ {x ∈ X | ν(J_x) ≥ ν̄}` which is closed, by the
same reason" (`isClosed_S_of_isDatum` and `Subscheme.isClosed_setOf_le_nu_stalkIdeal` applied to
`J`). -/
theorem isClosed_sNu_of_isDatum [Hironaka.Cited.IsHironakaBaseIsClosedSingularLocus.{u}] [Hironaka.Cited.CurveFiniteIntegralClosure.{u}] [Hironaka.Cited.IsRegularLocalRingLocalizationOfIsRegularLocalRing.{u}] [IsAlgebraicScheme X] (hX : X.IsNonsingular) (ℜ : Raw X)
    (hℜ : ℜ.IsDatum) (c : ℕ∞) : IsClosed (ℜ.sNu c) :=
  (isClosed_S_of_isDatum hX ℜ hℜ).inter (Subscheme.isClosed_setOf_le_nu_stalkIdeal hX ℜ.J c)

end DatumII.Raw

end Lemma2Datum

namespace LocSucc

/-! ### The sets `S(ℜ)` and `S_c(ℜ)` are closed, for arbitrary tuples (`ℜ` not assumed a datum) -/

variable {X : Scheme.{u}}

/-- `{x | c ≤ ν(J_x)}` is closed, by the upper semicontinuity of `ν` (Cor. 1 of Th. 2, Ch. III
§3, `cor:III.thm2-1`; see `Subscheme.isClosed_setOf_le_nu_stalkIdeal`). -/
theorem isClosed_le_nuAt [Hironaka.Cited.IsHironakaBaseIsClosedSingularLocus.{u}] [Hironaka.Cited.CurveFiniteIntegralClosure.{u}] [Hironaka.Cited.IsRegularLocalRingLocalizationOfIsRegularLocalRing.{u}] [IsAlgebraicScheme X] (hX : X.IsNonsingular) (ℜ : DatumII.Raw X)
    (c : ℕ∞) : IsClosed {x : X | c ≤ ℜ.nuAt x} :=
  Subscheme.isClosed_setOf_le_nu_stalkIdeal hX ℜ.J c

/-- `S(ℜ)` is closed, for an arbitrary tuple `ℜ` (not assumed to be a resolution datum): it is the
finite union, over the sets `T` of indices, of the closed sets
`{x | b ≤ ∑_T aᵢ + ν(J_x)} ∩ ⋂_{i ∈ T} Eᵢ`.

This is NOT the proof of Lemma 2 (`lem:IV.1-2`).  Lemma 2 (p. 278) is proved along the printed
route, with `J' = ∏ P_i^{a_i} J` and the hypothesis that `ℜ` is a datum, in
`DatumII.Raw.isClosed_S_of_isDatum`.  This version without the datum hypothesis is kept because
later files (`LocSucc.isClosed_sNu`) use it at tuples whose datum property is not at hand; it
needs neither the multiplicativity of `ν` nor `ν(P_{i,x}) = 1`. -/
theorem isClosed_S [Hironaka.Cited.IsHironakaBaseIsClosedSingularLocus.{u}] [Hironaka.Cited.CurveFiniteIntegralClosure.{u}] [Hironaka.Cited.IsRegularLocalRingLocalizationOfIsRegularLocalRing.{u}] [IsAlgebraicScheme X] (hX : X.IsNonsingular) (ℜ : DatumII.Raw X) :
    IsClosed ℜ.S := by
  classical
  have hS : ℜ.S = ⋃ T : Finset (Fin ℜ.α),
      ({x : X | ((ℜ.b : ℕ∞) - ((∑ i ∈ T, ℜ.a i : ℕ) : ℕ∞)) ≤ ℜ.nuAt x} ∩
        ⋂ i ∈ T, (ℜ.E i).pts) := by
    ext x
    simp only [DatumII.Raw.S, Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_inter_iff,
      Set.mem_iInter, tsub_le_iff_left]
    constructor
    · intro h
      refine ⟨Finset.univ.filter fun i => x ∈ (ℜ.E i).pts, h, fun i hi => ?_⟩
      exact (Finset.mem_filter.mp hi).2
    · rintro ⟨T, hT, hTE⟩
      refine le_trans hT (add_le_add_left ?_ _)
      unfold DatumII.Raw.weight
      exact_mod_cast Finset.sum_le_sum_of_subset (fun i hi =>
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, hTE i hi⟩)
  rw [hS]
  exact isClosed_iUnion_of_finite fun T => (isClosed_le_nuAt hX ℜ _).inter
    (isClosed_biInter fun i _ => (ℜ.E i).support.isClosed)

/-- `S_c(ℜ) = {x ∈ S(ℜ) | ν(J_x) ≥ c}` is closed. -/
theorem isClosed_sNu [Hironaka.Cited.IsHironakaBaseIsClosedSingularLocus.{u}] [Hironaka.Cited.CurveFiniteIntegralClosure.{u}] [Hironaka.Cited.IsRegularLocalRingLocalizationOfIsRegularLocalRing.{u}] [IsAlgebraicScheme X] (hX : X.IsNonsingular) (ℜ : DatumII.Raw X)
    (c : ℕ∞) : IsClosed (ℜ.sNu c) :=
  (isClosed_S hX ℜ).inter (isClosed_le_nuAt hX ℜ c)

/-- The generic point of `X` does not lie on `S(ℜ)` (Lemma 2, `lem:IV.1-2`: "obviously, the
generic point of `X` does not belong to `S(ℜ)`"): `O_{X,η}` is a field, so `ν(J_η) = 0` and no
`E_i` passes through `η`, while `b > 0`.  (Gap in the paper filled.) -/
theorem genericPoint_notMem_S [IrreducibleSpace X] (hX : X.IsNonsingular)
    (ℜ : DatumII.Raw X) (hℜ : ℜ.IsDatum) : genericPoint X ∉ ℜ.S := by
  classical
  have hred : ∀ x : X, _root_.IsReduced (X.presheaf.stalk x) := fun x => by
    have : IsRegularLocalRing (X.presheaf.stalk x) := hX x
    have := isDomain_of_isRegularLocalRing (X.presheaf.stalk x)
    infer_instance
  have : IsReduced X := isReduced_of_isReduced_stalk X
  have hfield : IsField (X.presheaf.stalk (genericPoint X)) :=
    isField_stalk_of_closure_mem_irreducibleComponents X (genericPoint X)
      (by rw [irreducibleComponents_eq_singleton, (genericPoint_spec X).def]; rfl)
  have := hfield.isDomain
  have hbt : ∀ I : Ideal (X.presheaf.stalk (genericPoint X)), I = ⊥ ∨ I = ⊤ := by
    intro I
    by_cases hI : I = ⊥
    · exact Or.inl hI
    · right
      obtain ⟨a, haI, ha⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI
      obtain ⟨b, hb⟩ := hfield.mul_inv_cancel ha
      exact Ideal.eq_top_of_isUnit_mem _ haI (IsUnit.of_mul_eq_one b hb)
  have hnuη : ℜ.nuAt (genericPoint X) = 0 := by
    have hJ : ℜ.J.stalkIdeal (genericPoint X) = ⊤ :=
      (hbt _).resolve_left (hℜ.2.2.2 (genericPoint X))
    rw [DatumII.Raw.nuAt]
    refine le_antisymm (Ideal.ord_le fun n hn => ?_) zero_le
    rcases n with _ | n
    · simp
    · rw [hJ, top_le_iff] at hn
      have h1 := Ideal.pow_le_self (I := maximalIdeal
        (X.presheaf.stalk (genericPoint X))) n.succ_ne_zero
      rw [hn, top_le_iff] at h1
      exact absurd h1 (maximalIdeal.isMaximal _).ne_top
  have hEη : ∀ i, genericPoint X ∉ (ℜ.E i).pts := fun i =>
    Subscheme.genericPoint_notMem_of_codimOne hX (hℜ.2.1 i)
  intro h
  have hw : ℜ.weight (genericPoint X) = 0 := by
    rw [DatumII.Raw.weight, Finset.sum_eq_zero]
    intro i hi
    exact absurd (Finset.mem_filter.mp hi).2 (hEη i)
  simp only [DatumII.Raw.S, Set.mem_ofPred_eq, hw, hnuη, Nat.cast_zero, add_zero] at h
  have hb0 : (ℜ.b : ℕ∞) = 0 := nonpos_iff_eq_zero.mp h
  have := hℜ.1
  simp only [Nat.cast_eq_zero] at hb0
  omega

end LocSucc

/-! ### Permissible monoidal transformations of type II data (p. 283) -/

namespace DatumII.Raw

variable {X : Scheme.{u}} {B : Subscheme X}

theorem weight_transform_of_notMem (ℜ : Raw X) (t : MonoidalTransformation X B) {y : t.X'}
    (hy : y ∉ t.exceptional.pts) : (ℜ.transform t).weight y = ℜ.weight (t.f y) := by
  classical
  rw [weight, weight, Finset.sum_filter, Finset.sum_filter]
  change (∑ i : Fin (ℜ.α + 1), if y ∈ (Fin.snoc (α := fun _ => Subscheme t.X')
      (fun i => Subscheme.strictTransform t (ℜ.E i)) t.exceptional i).pts then
      Fin.snoc (α := fun _ => ℕ) ℜ.a _ i else 0) = _
  rw [Fin.sum_univ_castSucc]
  simp only [Fin.snoc_castSucc, Fin.snoc_last, hy, ite_false, add_zero]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [t.mem_pts_strictTransform_iff_of_notMem _ hy]

/-- Off the exceptional subscheme, `J'_{y} = J_{f(y)}`. -/
theorem nuAt_transform_of_notMem (hX : X.IsNonsingular) (ℜ : Raw X)
    (t : MonoidalTransformation X B) {y : t.X'} (hy : y ∉ t.exceptional.pts) :
    (ℜ.transform t).nuAt y = ℜ.nuAt (t.f y) := by
  have : IsRegularLocalRing (X.presheaf.stalk (t.f y)) := hX _
  have hfy : t.f y ∉ B.pts := by
    rwa [MonoidalTransformation.pts_exceptional] at hy
  unfold nuAt
  rw [show (ℜ.transform t).J = Subscheme.divPow (Subscheme.totalTransform t.f ℜ.J)
      t.exceptional ℜ.nu.toNat from rfl,
    Subscheme.stalkIdeal_divPow (P := t.exceptional) t.invertible,
    Subscheme.stalkIdeal_eq_top_of_notMem_pts hy]
  simp only [Ideal.top_pow, Submodule.top_coe, Submodule.colon_univ]
  rw [stalkIdeal_totalTransform]
  exact LocSucc.nu_map_ringEquiv
    (RingEquiv.ofBijective _ (t.bijective_stalkMap_of_notMem y hfy)) _

theorem mem_sNu_transform_iff_of_notMem (hX : X.IsNonsingular) (ℜ : Raw X)
    (t : MonoidalTransformation X B) {y : t.X'} (hy : y ∉ t.exceptional.pts) (c : ℕ∞) :
    y ∈ (ℜ.transform t).sNu c ↔ t.f y ∈ ℜ.sNu c := by
  simp only [sNu, S, Set.mem_ofPred_eq, weight_transform_of_notMem ℜ t hy,
    nuAt_transform_of_notMem hX ℜ t hy]
  rfl

variable [IsAlgebraicScheme X]

/-- Lemma 8 of Ch. III §3 for a permissible monoidal transformation (p. 283): "if `x' ∈ X'` then
`ν(J'_{x'}) ≤ ν(J_{f(x')})`".  Off the exceptional subscheme `f` is a local isomorphism.  Over a
point `y` of the center `B`, `J'` is the weak transform of `J` (Remark 2 of Ch. III §2,
`rem:III.2-2`, `ν = ν(ℜ) = ν(J_ξ)` for the generic point `ξ` of `B ⊆ S*(ℜ)`), `O_{X',x'}` is a
monoidal transform of `O_{X,y}` with center `P = B_y`, and `ν_P(J_y) = ν(J_ξ) = ν(J_y)`
(`Subscheme.le_nu_generic_iff`). -/
theorem nuAt_transform_le [Hironaka.Cited.IsHironakaBaseIsClosedSingularLocus.{u}] [Hironaka.Cited.CurveFiniteIntegralClosure.{u}] [Hironaka.Cited.IsRegularLocalRingLocalizationOfIsRegularLocalRing.{u}] (hX : X.IsNonsingular) (ℜ : Raw X) (hℜ : ℜ.IsDatum)
    (t : MonoidalTransformation X B) (hB : ℜ.IsPermissible B) (y : t.X') :
    (ℜ.transform t).nuAt y ≤ ℜ.nuAt (t.f y) := by
  by_cases hy : y ∉ t.exceptional.pts
  · exact (nuAt_transform_of_notMem hX ℜ t hy).le
  rw [not_not] at hy
  have hfy : t.f y ∈ B.pts := by
    rwa [MonoidalTransformation.pts_exceptional] at hy
  obtain ⟨hns, hirr⟩ : B.IsNonsingular ∧ B.IsIrreducible := by
    rcases hB.1 with h | h
    · exfalso
      have : B.pts = ∅ := by rw [h]; exact Subscheme.pts_empty
      rw [this] at hfy
      exact hfy
    · exact h
  have := IsAlgebraicScheme.noetherianSpace X
  obtain ⟨ξ, hξ⟩ := QuasiSober.sober (Subscheme.isIrreducible_pts B hirr) B.support.isClosed
  -- `ν(J_ξ) = ν(ℜ)`
  have hξS : ξ ∈ ℜ.sStar := hB.2.1 hξ.mem
  have hνξ : ℜ.nuAt ξ = ℜ.nu :=
    le_antisymm (le_iSup₂ (f := fun x (_ : x ∈ ℜ.S) => ℜ.nuAt x) ξ hξS.1) hξS.2
  have hνtop : ℜ.nu ≠ ⊤ := (DatumII.Raw.transform_isDatum hX ℜ hℜ t hB).2.2
  set k := ℜ.nu.toNat with hkdef
  have hk : (k : ℕ∞) = ℜ.nu := ENat.natCast_toNat hνtop
  obtain ⟨-, -, -, h4, -⟩ := MonoidalTransformation.exceptional_isNonsingular_and_totalTransform_le_pow hX hirr hns t ℜ.J
  obtain ⟨k', hk', hweak⟩ := h4 ξ hξ (hℜ.2.2.2 ξ)
  have hkk' : k' = k := by
    have : (k' : ℕ∞) = k := by rw [← hk', hk]; exact hνξ
    exact_mod_cast this
  subst hkk'
  have hJ' : (ℜ.transform t).J = Subscheme.weakTransform t ℜ.J := hweak.symm
  have : IsRegularLocalRing (X.presheaf.stalk (t.f y)) := hX _
  have : IsDomain (X.presheaf.stalk (t.f y)) := Transforms.isDomain_of_isRegularLocalRing _
  obtain ⟨s, e, he⟩ := t.exists_monoidalTransform_stalk y
  have hse := Subscheme.stalkIdeal_weakTransform_eq_map hX hns t ℜ.J hξ y s e he
  have hP := Subscheme.isPrime_stalkIdeal_of_isNonsingular hns hfy
  have hSr := Subscheme.isRegularLocalRing_quotient_of_isNonsingular hns hfy
  -- `ν_P(J_y) = ν(J_y)`
  have hPJ : Ideal.ord (B.stalkIdeal (t.f y)) (ℜ.J.stalkIdeal (t.f y)) =
      Ideal.nu (ℜ.J.stalkIdeal (t.f y)) := by
    refine le_antisymm (Ideal.ord_le fun n hn => Ideal.le_ord (hn.trans
      (Ideal.pow_right_mono (stalkIdeal_le_maximalIdeal_of_mem_pts B hfy) n))) ?_
    have h1 : Ideal.nu (ℜ.J.stalkIdeal (t.f y)) ≤ ℜ.nu :=
      le_iSup₂ (f := fun x (_ : x ∈ ℜ.S) => ℜ.nuAt x) (t.f y) (hB.2.1 hfy).1
    refine h1.trans ?_
    rw [← hk]
    refine Ideal.le_ord ((Subscheme.le_nu_generic_iff hX hns hξ hfy ℜ.J k).mp ?_)
    rw [← nuAt, hνξ, hk]
  unfold nuAt
  rw [hJ', hse, LocSucc.nu_map_ringEquiv_of_equivLike]
  exact LocSucc.nu_weakTransformIdeal_le _ (hℜ.2.2.2 _) hP hSr hPJ s

/-- `f(S_c(f*ℜ)) ⊆ S_c(ℜ)` (p. 283: "for every non-negative integer `i`,
`f(S_i(f*(ℜ))) ⊆ S_i(ℜ)`"). -/
theorem mem_sNu_of_mem_sNu_transform [Hironaka.Cited.IsHironakaBaseIsClosedSingularLocus.{u}] [Hironaka.Cited.CurveFiniteIntegralClosure.{u}] [Hironaka.Cited.IsRegularLocalRingLocalizationOfIsRegularLocalRing.{u}] (hX : X.IsNonsingular) (ℜ : Raw X) (hℜ : ℜ.IsDatum)
    (t : MonoidalTransformation X B) (hB : ℜ.IsPermissible B) {c : ℕ∞} {y : t.X'}
    (h : y ∈ (ℜ.transform t).sNu c) : t.f y ∈ ℜ.sNu c := by
  by_cases hy : y ∈ t.exceptional.pts
  · have hfy : t.f y ∈ B.pts := by
      rwa [MonoidalTransformation.pts_exceptional] at hy
    exact ⟨(hB.2.1 hfy).1, h.2.trans (nuAt_transform_le hX ℜ hℜ t hB y)⟩
  · exact (mem_sNu_transform_iff_of_notMem hX ℜ t hy c).mp h

theorem mem_S_of_mem_S_transform [Hironaka.Cited.IsHironakaBaseIsClosedSingularLocus.{u}] [Hironaka.Cited.CurveFiniteIntegralClosure.{u}] [Hironaka.Cited.IsRegularLocalRingLocalizationOfIsRegularLocalRing.{u}] (hX : X.IsNonsingular) (ℜ : Raw X) (hℜ : ℜ.IsDatum)
    (t : MonoidalTransformation X B) (hB : ℜ.IsPermissible B) {y : t.X'}
    (h : y ∈ (ℜ.transform t).S) : t.f y ∈ ℜ.S :=
  (mem_sNu_of_mem_sNu_transform hX ℜ hℜ t hB (c := 0) ⟨h, zero_le⟩).1

/-- `ν(f*ℜ) ≤ ν(ℜ)` (p. 283). -/
theorem nu_transform_le [Hironaka.Cited.IsHironakaBaseIsClosedSingularLocus.{u}] [Hironaka.Cited.CurveFiniteIntegralClosure.{u}] [Hironaka.Cited.IsRegularLocalRingLocalizationOfIsRegularLocalRing.{u}] (hX : X.IsNonsingular) (ℜ : Raw X) (hℜ : ℜ.IsDatum)
    (t : MonoidalTransformation X B) (hB : ℜ.IsPermissible B) :
    (ℜ.transform t).nu ≤ ℜ.nu :=
  iSup₂_le fun y hy => (nuAt_transform_le hX ℜ hℜ t hB y).trans
    (le_iSup₂ (f := fun x (_ : x ∈ ℜ.S) => ℜ.nuAt x) (t.f y)
      (mem_S_of_mem_S_transform hX ℜ hℜ t hB hy))

end DatumII.Raw

/-! ### Divisions `I·P⁻ᵛ` along flat preimmersions -/

namespace Subscheme

variable {Y Z : Scheme.{u}}

theorem divPow_empty (I : Subscheme Y) (k : ℕ) : Subscheme.divPow I Subscheme.empty k = I := by
  refine Subscheme.ext_stalkIdeal fun x => ?_
  rw [Subscheme.stalkIdeal_divPow Subscheme.isInvertibleIdeal_empty,
    show (Subscheme.empty : Subscheme Y) = ⊤ from rfl, Subscheme.stalkIdeal_top_eq]
  simp only [Ideal.top_pow, Submodule.top_coe, Submodule.colon_univ]

theorem totalTransform_divPow (g : Z ⟶ Y) [Flat g] [IsPreimmersion g] (I P : Subscheme Y)
    (hP : P.IsInvertibleIdeal) (k : ℕ) :
    Subscheme.totalTransform g (Subscheme.divPow I P k) =
      Subscheme.divPow (Subscheme.totalTransform g I) (Subscheme.totalTransform g P) k := by
  refine Subscheme.ext_stalkIdeal fun z => ?_
  rw [FlatPreimm.stalkIdeal_totalTransform, Subscheme.stalkIdeal_divPow hP,
    Subscheme.stalkIdeal_divPow (isInvertibleIdeal_totalTransform_of_flat g hP),
    FlatPreimm.stalkIdeal_totalTransform, FlatPreimm.stalkIdeal_totalTransform,
    Ideal.map_colon_ringEquiv, Ideal.map_pow]

end Subscheme

/-! ### Pull-backs of type II data and data with the same essential characteristics -/

namespace LocSucc

open Classical in
/-- A sum over the indices whose component satisfies `p`, regrouped by the values of the
components. -/
theorem sum_filter_eq_sum_image {n : ℕ} {W : Type*} (E : Fin n → W) (a : Fin n → ℕ)
    (p : W → Prop) :
    ∑ i ∈ Finset.univ.filter (fun i => p (E i)), a i =
      ∑ D ∈ (Finset.univ.image E).filter p,
        ∑ i ∈ Finset.univ.filter (fun i => E i = D), a i := by
  rw [← Finset.sum_fiberwise_of_maps_to (s := Finset.univ.filter (fun i => p (E i)))
    (t := (Finset.univ.image E).filter p) (g := E) (fun i hi => Finset.mem_filter.mpr
      ⟨Finset.mem_image_of_mem E (Finset.mem_univ i), (Finset.mem_filter.mp hi).2⟩)]
  refine Finset.sum_congr rfl fun D hD => ?_
  have hpD := (Finset.mem_filter.mp hD).2
  rw [Finset.filter_filter]
  refine Finset.sum_congr (Finset.filter_congr fun i _ => ?_) fun _ _ => rfl
  exact ⟨fun h => h.2, fun h => ⟨h ▸ hpD, h⟩⟩

open Classical in
theorem sum_filter_snoc {n : ℕ} {W : Type*} (E : Fin n → W) (e : W) (a : Fin n → ℕ) (c : ℕ)
    (p : W → Prop) :
    ∑ i ∈ Finset.univ.filter (fun i => p (Fin.snoc (α := fun _ => W) E e i)),
        Fin.snoc (α := fun _ => ℕ) a c i =
      (∑ i ∈ Finset.univ.filter (fun i => p (E i)), a i) + if p e then c else 0 := by
  rw [Finset.sum_filter, Finset.sum_filter, Fin.sum_univ_castSucc]
  simp only [Fin.snoc_castSucc, Fin.snoc_last]

end LocSucc

namespace DatumII.Raw

open Classical

section Pullback

variable {Y Z : Scheme.{u}}

/-- The pull-back of a type II raw datum along a morphism `g : Z → Y`: every subscheme is
replaced by its total transform.  For the canonical immersion `X'_S → X'` this is the localized
datum of Definition 1 (II), p. 276 (`DatumII.Raw.localize`). -/
noncomputable def pullback (g : Z ⟶ Y) (ℜ : Raw Y) : Raw Z where
  α := ℜ.α
  E := fun i => Subscheme.totalTransform g (ℜ.E i)
  a := ℜ.a
  J := Subscheme.totalTransform g ℜ.J
  b := ℜ.b

variable (g : Z ⟶ Y) [Flat g] [IsPreimmersion g]

omit [Flat g] [IsPreimmersion g] in
theorem weight_pullback (ℜ : Raw Y) (z : Z) : (ℜ.pullback g).weight z = ℜ.weight (g z) := by
  unfold weight
  refine Finset.sum_congr (Finset.filter_congr fun i _ => ?_) fun _ _ => rfl
  show z ∈ (Subscheme.totalTransform g (ℜ.E i)).pts ↔ _
  rw [FlatPreimm.pts_totalTransform]
  rfl

theorem nuAt_pullback (ℜ : Raw Y) (z : Z) : (ℜ.pullback g).nuAt z = ℜ.nuAt (g z) := by
  unfold nuAt
  show Ideal.nu ((Subscheme.totalTransform g ℜ.J).stalkIdeal z) = _
  rw [FlatPreimm.stalkIdeal_totalTransform, LocSucc.nu_map_ringEquiv_of_equivLike]

theorem mem_sNu_pullback (ℜ : Raw Y) (c : ℕ∞) (z : Z) :
    z ∈ (ℜ.pullback g).sNu c ↔ g z ∈ ℜ.sNu c := by
  simp only [sNu, S, Set.mem_ofPred_eq, weight_pullback, nuAt_pullback]
  rfl

theorem mem_S_pullback (ℜ : Raw Y) (z : Z) : z ∈ (ℜ.pullback g).S ↔ g z ∈ ℜ.S := by
  simp only [S, Set.mem_ofPred_eq, weight_pullback, nuAt_pullback]
  rfl

theorem nu_pullback_le (ℜ : Raw Y) : (ℜ.pullback g).nu ≤ ℜ.nu :=
  iSup₂_le fun z hz => (nuAt_pullback g ℜ z).trans_le
    (le_iSup₂ (f := fun x (_ : x ∈ ℜ.S) => ℜ.nuAt x) (g z) ((mem_S_pullback g ℜ z).mp hz))

omit [Flat g] [IsPreimmersion g] in
theorem pts_eUnion_pullback (ℜ : Raw Y) :
    (ℜ.pullback g).eUnion.pts = g.base ⁻¹' ℜ.eUnion.pts := by
  unfold eUnion
  rw [Subscheme.pts_iInf, Subscheme.pts_iInf, Set.preimage_iUnion]
  refine Set.iUnion_congr fun i => ?_
  exact FlatPreimm.pts_totalTransform g _

end Pullback

variable {X : Scheme.{u}}

/-- Two type II data with the same "essential characteristics" (p. 275: "all that are
essential among its characteristics are the following ones: the set `C(ℜ^N_II)` of those
irreducible subschemes `E_i` of `X` which are not empty, the integers `a(E) = ∑_{E_i = E} a_i`
for `E ∈ C(ℜ^N_II)`, `J` and `b`").

Deviation from the paper (encoding): the paper also says (p. 275) that it will
"distinguish any two resolution data with different expressions", and then asserts
`_bℜ̄ = (_bℜ')_S` in the proof of Proposition 3 (p. 284); for type II this holds only up to the
identification above, which is what the lifting proves (`SameChar`). -/
def SameChar (ℜ₁ ℜ₂ : Raw X) : Prop :=
  ℜ₁.J = ℜ₂.J ∧ ℜ₁.b = ℜ₂.b ∧ ∀ D : Subscheme X, D.pts.Nonempty →
    ((∃ i, ℜ₁.E i = D) ↔ ∃ i, ℜ₂.E i = D) ∧
      ∑ i ∈ Finset.univ.filter (fun i => ℜ₁.E i = D), ℜ₁.a i =
        ∑ i ∈ Finset.univ.filter (fun i => ℜ₂.E i = D), ℜ₂.a i

namespace SameChar

variable {ℜ₁ ℜ₂ ℜ₃ : Raw X}

theorem refl (ℜ : Raw X) : SameChar ℜ ℜ := ⟨rfl, rfl, fun _ _ => ⟨Iff.rfl, rfl⟩⟩

theorem symm (h : SameChar ℜ₁ ℜ₂) : SameChar ℜ₂ ℜ₁ :=
  ⟨h.1.symm, h.2.1.symm, fun D hD => ⟨(h.2.2 D hD).1.symm, (h.2.2 D hD).2.symm⟩⟩

theorem trans (h : SameChar ℜ₁ ℜ₂) (h' : SameChar ℜ₂ ℜ₃) : SameChar ℜ₁ ℜ₃ :=
  ⟨h.1.trans h'.1, h.2.1.trans h'.2.1, fun D hD =>
    ⟨(h.2.2 D hD).1.trans (h'.2.2 D hD).1, (h.2.2 D hD).2.trans (h'.2.2 D hD).2⟩⟩

/-- Sums of the `a_i` over the components satisfying a condition which forces non-emptiness
agree. -/
theorem sum_eq (h : SameChar ℜ₁ ℜ₂) (p : Subscheme X → Prop)
    (hp : ∀ D, p D → D.pts.Nonempty) :
    ∑ i ∈ Finset.univ.filter (fun i => p (ℜ₁.E i)), ℜ₁.a i =
      ∑ i ∈ Finset.univ.filter (fun i => p (ℜ₂.E i)), ℜ₂.a i := by
  rw [LocSucc.sum_filter_eq_sum_image, LocSucc.sum_filter_eq_sum_image]
  have himg : (Finset.univ.image ℜ₁.E).filter p = (Finset.univ.image ℜ₂.E).filter p := by
    ext D
    simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and]
    exact ⟨fun ⟨h1, h2⟩ => ⟨(h.2.2 D (hp D h2)).1.mp h1, h2⟩,
      fun ⟨h1, h2⟩ => ⟨(h.2.2 D (hp D h2)).1.mpr h1, h2⟩⟩
  rw [himg]
  exact Finset.sum_congr rfl fun D hD => (h.2.2 D (hp D (Finset.mem_filter.mp hD).2)).2

theorem weight_eq (h : SameChar ℜ₁ ℜ₂) (x : X) : ℜ₁.weight x = ℜ₂.weight x :=
  h.sum_eq (fun D => x ∈ D.pts) fun _ hD => ⟨x, hD⟩

theorem nuAt_eq (h : SameChar ℜ₁ ℜ₂) (x : X) : ℜ₁.nuAt x = ℜ₂.nuAt x := by
  unfold nuAt
  rw [h.1]

theorem sNu_eq (h : SameChar ℜ₁ ℜ₂) (c : ℕ∞) : ℜ₁.sNu c = ℜ₂.sNu c := by
  ext x
  simp only [sNu, S, Set.mem_ofPred_eq, h.weight_eq, h.nuAt_eq, h.2.1]

theorem S_eq (h : SameChar ℜ₁ ℜ₂) : ℜ₁.S = ℜ₂.S := by
  ext x
  simp only [S, Set.mem_ofPred_eq, h.weight_eq, h.nuAt_eq, h.2.1]

theorem nu_eq (h : SameChar ℜ₁ ℜ₂) : ℜ₁.nu = ℜ₂.nu := by
  unfold nu
  rw [h.S_eq]
  exact iSup_congr fun x => iSup_congr fun _ => h.nuAt_eq x

theorem sStar_eq (h : SameChar ℜ₁ ℜ₂) : ℜ₁.sStar = ℜ₂.sStar := by
  unfold sStar
  rw [h.nu_eq, h.sNu_eq]

theorem eUnion_eq (h : SameChar ℜ₁ ℜ₂) : ℜ₁.eUnion = ℜ₂.eUnion := by
  have key : ∀ {ℜ ℜ' : Raw X}, SameChar ℜ ℜ' → ℜ.eUnion ≤ ℜ'.eUnion := by
    intro ℜ ℜ' hh
    refine le_iInf fun i => ?_
    by_cases hne : (ℜ'.E i).pts.Nonempty
    · obtain ⟨k, hk⟩ := (hh.2.2 _ hne).1.mpr ⟨i, rfl⟩
      exact hk ▸ iInf_le _ k
    · rw [Subscheme.eq_empty_of_pts_eq_empty (Set.not_nonempty_iff_eq_empty.mp hne)]
      exact le_top
  exact le_antisymm (key h) (key h.symm)

theorem isDatum (h : SameChar ℜ₁ ℜ₂) (h₁ : ℜ₁.IsDatum) : ℜ₂.IsDatum := by
  refine ⟨h.2.1 ▸ h₁.1, fun i => ?_, h.eUnion_eq ▸ h₁.2.2.1, h.1 ▸ h₁.2.2.2⟩
  by_cases hne : (ℜ₂.E i).pts.Nonempty
  · obtain ⟨k, hk⟩ := (h.2.2 _ hne).1.mpr ⟨i, rfl⟩
    exact hk ▸ h₁.2.1 k
  · exact Or.inl (Subscheme.eq_empty_of_pts_eq_empty (Set.not_nonempty_iff_eq_empty.mp hne))

theorem isPermissible (h : SameChar ℜ₁ ℜ₂) {B : Subscheme X} (h₁ : ℜ₁.IsPermissible B) :
    ℜ₂.IsPermissible B :=
  ⟨h₁.1, h.sStar_eq ▸ h₁.2.1, h.eUnion_eq ▸ h₁.2.2⟩

/-- The transforms of two data with the same characteristics by the same monoidal transformation
have the same characteristics. -/
theorem transform (h : SameChar ℜ₁ ℜ₂) {B : Subscheme X} (t : MonoidalTransformation X B) :
    SameChar (ℜ₁.transform t) (ℜ₂.transform t) := by
  have hst : ∀ V : Subscheme X, (Subscheme.strictTransform t V).pts.Nonempty → V.pts.Nonempty :=
    fun V ⟨y, hy⟩ => ⟨_, t.pts_strictTransform_subset V hy⟩
  refine ⟨?_, h.2.1, fun D hD => ⟨?_, ?_⟩⟩
  · show Subscheme.divPow (Subscheme.totalTransform t.f ℜ₁.J) t.exceptional ℜ₁.nu.toNat =
      Subscheme.divPow (Subscheme.totalTransform t.f ℜ₂.J) t.exceptional ℜ₂.nu.toNat
    rw [h.1, h.nu_eq]
  · show (∃ k, Fin.snoc (α := fun _ => Subscheme t.X')
        (fun i => Subscheme.strictTransform t (ℜ₁.E i)) t.exceptional k = D) ↔
      ∃ k, Fin.snoc (α := fun _ => Subscheme t.X')
        (fun i => Subscheme.strictTransform t (ℜ₂.E i)) t.exceptional k = D
    have key : ∀ {ℜ ℜ' : Raw X}, SameChar ℜ ℜ' →
        (∃ i, Subscheme.strictTransform t (ℜ.E i) = D) →
          ∃ i, Subscheme.strictTransform t (ℜ'.E i) = D := by
      rintro ℜ ℜ' hh ⟨i, hi⟩
      obtain ⟨k, hk⟩ := (hh.2.2 _ (hst _ (hi ▸ hD))).1.mp ⟨i, rfl⟩
      exact ⟨k, by rw [hk, hi]⟩
    rw [Fin.exists_fin_succ', Fin.exists_fin_succ']
    simp only [Fin.snoc_castSucc, Fin.snoc_last]
    exact ⟨Or.imp_left (key h), Or.imp_left (key h.symm)⟩
  · show ∑ i ∈ Finset.univ.filter (fun i => Fin.snoc (α := fun _ => Subscheme t.X')
        (fun i => Subscheme.strictTransform t (ℜ₁.E i)) t.exceptional i = D),
          Fin.snoc (α := fun _ => ℕ) ℜ₁.a _ i =
      ∑ i ∈ Finset.univ.filter (fun i => Fin.snoc (α := fun _ => Subscheme t.X')
        (fun i => Subscheme.strictTransform t (ℜ₂.E i)) t.exceptional i = D),
          Fin.snoc (α := fun _ => ℕ) ℜ₂.a _ i
    rw [LocSucc.sum_filter_snoc _ _ _ _ (fun V => V = D),
      LocSucc.sum_filter_snoc _ _ _ _ (fun V => V = D)]
    rw [h.sum_eq (fun V => Subscheme.strictTransform t V = D) fun V hV => hst V (hV ▸ hD)]
    congr 1
    by_cases hexc : t.exceptional = D
    · have hB : B.pts.Nonempty := by
        obtain ⟨y, hy⟩ := hD
        rw [← hexc, MonoidalTransformation.pts_exceptional] at hy
        exact ⟨_, hy⟩
      rw [ite_eq_left hexc, ite_eq_left hexc,
        h.sum_eq (fun V => B.IsContainedIn V) fun V hV => hB.mono (pts_subset_of_isContainedIn hV),
        h.nu_eq, h.2.1]
    · rw [ite_eq_right hexc, ite_eq_right hexc]

/-- Pull-backs of data with the same characteristics have the same characteristics. -/
theorem pullback (h : SameChar ℜ₁ ℜ₂) {Z : Scheme.{u}} (g : Z ⟶ X) :
    SameChar (ℜ₁.pullback g) (ℜ₂.pullback g) := by
  have htt : ∀ V : Subscheme X, (Subscheme.totalTransform g V).pts.Nonempty → V.pts.Nonempty :=
    fun V ⟨z, hz⟩ => ⟨g z, by rwa [FlatPreimm.pts_totalTransform] at hz⟩
  refine ⟨by show Subscheme.totalTransform g ℜ₁.J = Subscheme.totalTransform g ℜ₂.J; rw [h.1],
    h.2.1, fun D hD => ⟨?_, ?_⟩⟩
  · have key : ∀ {ℜ ℜ' : Raw X}, SameChar ℜ ℜ' →
        (∃ i, Subscheme.totalTransform g (ℜ.E i) = D) →
          ∃ i, Subscheme.totalTransform g (ℜ'.E i) = D := by
      rintro ℜ ℜ' hh ⟨i, hi⟩
      obtain ⟨k, hk⟩ := (hh.2.2 _ (htt _ (hi ▸ hD))).1.mp ⟨i, rfl⟩
      exact ⟨k, by rw [hk, hi]⟩
    exact ⟨key h, key h.symm⟩
  · exact h.sum_eq (fun V => Subscheme.totalTransform g V = D) fun V hV => htt V (hV ▸ hD)

end SameChar

section Lift

variable {Y Z : Scheme.{u}}

/-- In a commutative square of monoidal transformations over a flat preimmersion
(`MonoidalTransformation.exists_lift`), the pull-back of the transform is the transform of the
pull-back (Definition 7 (II), p. 168; p. 276: "`h_S` is the monoidal transformation of `X''_S`
with center `B''_S`"), provided the center `B` of `Y` lies in exactly those `E_i` whose
pull-backs contain the center `B_Z` of `Z` (so that the new coefficient
`a_{α+1} = ∑_{B ⊆ E_i} a_i + ν − b` is the same) and `ν` does not drop under the pull-back. -/
theorem pullback_transform_of_lift {B : Subscheme Y} (t : MonoidalTransformation Y B)
    (g : Z ⟶ Y) {Bs : Subscheme Z} (ts : MonoidalTransformation Z Bs) (g' : ts.X' ⟶ t.X')
    [Flat g'] [IsPreimmersion g'] (hsq : g' ≫ t.f = ts.f ≫ g)
    (hexc : Subscheme.totalTransform g' t.exceptional = ts.exceptional)
    (hst : ∀ V, Subscheme.totalTransform g' (Subscheme.strictTransform t V) =
      Subscheme.strictTransform ts (Subscheme.totalTransform g V)) (ℜ : Raw Y)
    (hcont : ∀ i, B.IsContainedIn (ℜ.E i) ↔
      Bs.IsContainedIn (Subscheme.totalTransform g (ℜ.E i)))
    (hν : (ℜ.pullback g).nu = ℜ.nu) :
    (ℜ.transform t).pullback g' = (ℜ.pullback g).transform ts := by
  have hE : (fun i => Subscheme.totalTransform g' (Fin.snoc (α := fun _ => Subscheme t.X')
      (fun i => Subscheme.strictTransform t (ℜ.E i)) t.exceptional i)) =
      Fin.snoc (α := fun _ => Subscheme ts.X')
        (fun i => Subscheme.strictTransform ts (Subscheme.totalTransform g (ℜ.E i)))
        ts.exceptional := by
    funext k
    refine Fin.lastCases ?_ (fun i => ?_) k
    · simp only [Fin.snoc_last, hexc]
    · simp only [Fin.snoc_castSucc, hst]
  have ha : (∑ i ∈ Finset.univ.filter (fun i => B.IsContainedIn (ℜ.E i)), ℜ.a i) =
      ∑ i ∈ Finset.univ.filter
        (fun i => Bs.IsContainedIn (Subscheme.totalTransform g (ℜ.E i))), ℜ.a i :=
    Finset.sum_congr (Finset.filter_congr fun i _ => hcont i) fun _ _ => rfl
  have hJ : Subscheme.totalTransform g' (Subscheme.divPow
      (Subscheme.totalTransform t.f ℜ.J) t.exceptional ℜ.nu.toNat) =
      Subscheme.divPow (Subscheme.totalTransform ts.f (Subscheme.totalTransform g ℜ.J))
        ts.exceptional (ℜ.pullback g).nu.toNat := by
    rw [Subscheme.totalTransform_divPow g' _ t.exceptional t.invertible,
      ← Subscheme.totalTransform_comp, hsq, Subscheme.totalTransform_comp, hexc, hν]
  show (⟨ℜ.α + 1, _, _, _, ℜ.b⟩ : Raw ts.X') = ⟨ℜ.α + 1, _, _, _, ℜ.b⟩
  congr 1
  show Fin.snoc (α := fun _ => ℕ) ℜ.a _ = Fin.snoc (α := fun _ => ℕ) ℜ.a _
  rw [ha, hν]
  rfl

/-- The disjoint case: over a flat preimmersion missing the center, the pull-back of the
transform has the same characteristics as the pull-back (the new component `E_{α+1}` pulls back
to the empty subscheme, and `f⁻¹(J)·P⁻ᵛ` to the pull-back of `J`). -/
theorem sameChar_pullback_transform_of_lift_disjoint {B : Subscheme Y}
    (t : MonoidalTransformation Y B) (g : Z ⟶ Y) (g' : Z ⟶ t.X') [Flat g'] [IsPreimmersion g']
    (hcomp : g' ≫ t.f = g)
    (hexc : Subscheme.totalTransform g' t.exceptional = Subscheme.empty)
    (hst : ∀ V, Subscheme.totalTransform g' (Subscheme.strictTransform t V) =
      Subscheme.totalTransform g V) (ℜ : Raw Y) :
    SameChar ((ℜ.transform t).pullback g') (ℜ.pullback g) := by
  have hE : ((ℜ.transform t).pullback g').E = Fin.snoc (α := fun _ => Subscheme Z)
      (fun i => Subscheme.totalTransform g (ℜ.E i)) Subscheme.empty := by
    funext k
    refine Fin.lastCases ?_ (fun i => ?_) k
    · show Subscheme.totalTransform g' (Fin.snoc (α := fun _ => Subscheme t.X')
        (fun i => Subscheme.strictTransform t (ℜ.E i)) t.exceptional (Fin.last _)) = _
      simp only [Fin.snoc_last, hexc]
    · show Subscheme.totalTransform g' (Fin.snoc (α := fun _ => Subscheme t.X')
        (fun i => Subscheme.strictTransform t (ℜ.E i)) t.exceptional (Fin.castSucc i)) = _
      simp only [Fin.snoc_castSucc, hst]
  refine ⟨?_, rfl, fun D hD => ⟨?_, ?_⟩⟩
  · show Subscheme.totalTransform g' (Subscheme.divPow (Subscheme.totalTransform t.f ℜ.J)
      t.exceptional ℜ.nu.toNat) = Subscheme.totalTransform g ℜ.J
    rw [Subscheme.totalTransform_divPow g' _ t.exceptional t.invertible,
      ← Subscheme.totalTransform_comp, hcomp, hexc, Subscheme.divPow_empty]
  · have hDe : Subscheme.empty ≠ D := by
      rintro rfl
      rw [Subscheme.pts_empty] at hD
      exact hD.ne_empty rfl
    rw [hE]
    show (∃ i : Fin (ℜ.α + 1), _) ↔ _
    rw [Fin.exists_fin_succ']
    simp only [Fin.snoc_castSucc, Fin.snoc_last]
    exact ⟨fun h => h.resolve_right hDe, Or.inl⟩
  · have hDe : ¬ Subscheme.empty = D := by
      rintro rfl
      rw [Subscheme.pts_empty] at hD
      exact hD.ne_empty rfl
    rw [hE]
    show ∑ i ∈ Finset.univ.filter (fun i : Fin (ℜ.α + 1) => Fin.snoc (α := fun _ => Subscheme Z)
        (fun i => Subscheme.totalTransform g (ℜ.E i)) Subscheme.empty i = D),
        Fin.snoc (α := fun _ => ℕ) ℜ.a _ i = _
    rw [LocSucc.sum_filter_snoc _ _ _ _ (fun V => V = D), ite_eq_right hDe, add_zero]
    rfl

end Lift

end DatumII.Raw

namespace MonoidalSuccession

variable {X Y Z : Scheme.{u}}

/-- `MonoidalSuccession.exists_lift_of_centersAvoid`, together with the type II data: the pull-back
of the transform of a type II datum has the same characteristics as the pull-back of the datum. -/
theorem exists_lift_of_centersAvoidII (s : MonoidalSuccession X Y) (j : Z ⟶ X) [Flat j]
    [IsPreimmersion j] (hs : s.CentersAvoid (Set.range j.base)) :
    ∃ j₁ : Z ⟶ Y, Flat j₁ ∧ IsPreimmersion j₁ ∧ j₁ ≫ s.composite = j ∧
      Set.range j₁.base = s.composite.base ⁻¹' Set.range j.base ∧
      (∀ V, Subscheme.totalTransform j₁ (s.strictTransform V) = Subscheme.totalTransform j V) ∧
      ∀ ℜ : DatumII.Raw X, DatumII.Raw.SameChar ((s.transformII ℜ).pullback j₁)
        (ℜ.pullback j) := by
  induction s with
  | nil X =>
    exact ⟨j, inferInstance, inferInstance, Category.comp_id j, rfl, fun V => rfl,
      fun ℜ => DatumII.Raw.SameChar.refl _⟩
  | cons B t rest ih =>
    obtain ⟨hB, hrest⟩ := hs
    obtain ⟨j', hfl, hpre, hj', hr', hexc, hst⟩ :=
      t.exists_lift_of_disjoint j fun z hz => hB _ hz ⟨z, rfl⟩
    rw [← hr'] at hrest
    obtain ⟨j₁, hfl₁, hpre₁, hj₁, hr₁, hst₁, hℜ₁⟩ := ih j' hrest
    refine ⟨j₁, hfl₁, hpre₁, ?_, ?_, fun V => ?_, fun ℜ => ?_⟩
    · rw [composite_cons, ← Category.assoc, hj₁, hj']
    · rw [hr₁, hr', composite_cons, Scheme.Hom.comp_base, TopCat.coe_comp, Set.preimage_comp]
    · rw [strictTransform_cons, hst₁, hst]
    · rw [transformII_cons]
      exact (hℜ₁ _).trans
        (DatumII.Raw.sameChar_pullback_transform_of_lift_disjoint t j j' hj' hexc hst ℜ)

theorem sameChar_transformII (s : MonoidalSuccession X Y) {ℜ₁ ℜ₂ : DatumII.Raw X}
    (h : DatumII.Raw.SameChar ℜ₁ ℜ₂) :
    DatumII.Raw.SameChar (s.transformII ℜ₁) (s.transformII ℜ₂) := by
  induction s with
  | nil X => exact h
  | cons B t rest ih => exact ih (h.transform t)

end MonoidalSuccession

/-! ### Strict transforms and exceptional subschemes -/

namespace MonoidalTransformation

variable {X : Scheme.{u}} {B : Subscheme X}

/-- The points of the strict transform `V'` form the closure of the part of `f⁻¹(V)` off the
exceptional subscheme. -/
theorem pts_strictTransform_eq_closure (t : MonoidalTransformation X B) (V : Subscheme X) :
    (Subscheme.strictTransform t V).pts =
      closure (t.f.base ⁻¹' V.pts \ t.exceptional.pts) := by
  apply subset_antisymm
  · intro p hp
    obtain ⟨q, hq, hqE, hqp⟩ := t.exists_generization_notMem_exceptional V hp
    have h1 : p ∈ closure {q} := specializes_iff_mem_closure.mp hqp
    exact closure_mono (Set.singleton_subset_iff.mpr
      (Set.mem_sdiff_of_mem (t.pts_strictTransform_subset V hq) hqE)) h1
  · refine closure_minimal (fun y hy => ?_) (Subscheme.strictTransform t V).support.isClosed
    exact (t.mem_pts_strictTransform_iff_of_notMem V hy.2).mpr hy.1

theorem pts_strictTransform_congr (t : MonoidalTransformation X B) {V V' : Subscheme X}
    (h : V.pts = V'.pts) :
    (Subscheme.strictTransform t V).pts = (Subscheme.strictTransform t V').pts := by
  rw [pts_strictTransform_eq_closure, pts_strictTransform_eq_closure, h]

/-- The strict transform of a subscheme containing all points contains all points (the
exceptional subscheme is nowhere dense). -/
theorem pts_strictTransform_eq_univ (t : MonoidalTransformation X B) [IsAlgebraicScheme t.X']
    {V : Subscheme X} (h : V.pts = Set.univ) :
    (Subscheme.strictTransform t V).pts = Set.univ := by
  rw [pts_strictTransform_eq_closure, h, Set.preimage_univ, ← Set.compl_eq_univ_sdiff,
    closure_compl, interior_pts_exceptional, Set.compl_empty]

end MonoidalTransformation

/-! ### The type I datum `(⋃ E_i; B)` attached to a type II datum (pp. 283–284) -/

namespace DatumII.Raw

variable {X : Scheme.{u}}

/-- The type I datum `(⋃_i E_i; W)` (no `V`'s) of p. 283, with principal subscheme `W`. -/
noncomputable def eUnionDatumI (ℜ : Raw X) (W : Subscheme X) : DatumI.Raw X :=
  ⟨ℜ.eUnion, 0, Fin.elim0, W⟩

@[simp] theorem eUnionDatumI_e (ℜ : Raw X) (W : Subscheme X) : (ℜ.eUnionDatumI W).E = ℜ.eUnion := rfl
@[simp] theorem eUnionDatumI_principal (ℜ : Raw X) (W : Subscheme X) : (ℜ.eUnionDatumI W).W = W := rfl

/-- `(⋃ E_i; W)` is a type I datum when `W` is reduced: the union of the `E_i` is reduced,
everywhere of codimension one and has only normal crossings, since at every point the `E_i`
through it are defined by members of one regular system of parameters. -/
theorem isDatum_eUnionDatumI (hX : X.IsNonsingular) {ℜ : Raw X} (hℜ : ℜ.IsDatum) {W : Subscheme X}
    (hW : W.IsReduced) : (ℜ.eUnionDatumI W).IsDatum := by
  have hstalk : ∀ x, ∃ K : Finset (X.presheaf.stalk x), ExtendsToRSOP _ K ∧
      ℜ.eUnion.stalkIdeal x = Ideal.span {∏ k ∈ K, k} := by
    intro x
    have : IsRegularLocalRing (X.presheaf.stalk x) := hX x
    obtain ⟨Z, hZ, -, hE⟩ := DatumTransform.exists_rsop_adapted_of_isDatum (B := ⊥) ℜ.E hX hℜ.2.1 hℜ.2.2.1
      (fun x _ => hℜ.2.2.1 x) x
    obtain ⟨K, hKZ, hK⟩ := DatumTransform.iInf_eq_span_prod (fun i => (ℜ.E i).stalkIdeal x)
      ⟨Z, subset_rfl, hZ⟩ hE
    refine ⟨K, ⟨Z, hKZ, hZ⟩, ?_⟩
    rw [eUnion, DatumTransform.stalkIdeal_iInf_fintype]
    exact hK
  have hred := DatumTransform.isReduced_of_forall_stalk hX hstalk
  exact ⟨hred, DatumTransform.isEverywhereCodimOne_of_forall_stalk hX hstalk,
    DatumTransform.hasOnlyNormalCrossings_of_forall_stalk hX hred hstalk, hW, fun i => i.elim0⟩

end DatumII.Raw

/-! ### Permissibility for type II along successions permissible for `(⋃ E_i; B'')` -/

namespace MonoidalSuccession

variable {X Y : Scheme.{u}}

private theorem nu_transformII_le_of_isAlgebraicScheme [Hironaka.Cited.IsHironakaBaseIsClosedSingularLocus.{u}] [Hironaka.Cited.MonoidalTransformationExistsIsProper.{u}] [Hironaka.Cited.CurveFiniteIntegralClosure.{u}] [Hironaka.Cited.IsRegularLocalRingLocalizationOfIsRegularLocalRing.{u}] (s : MonoidalSuccession X Y) (hXa : IsAlgebraicScheme X)
    (hX : X.IsNonsingular) (ℜ : DatumII.Raw X) (hℜ : ℜ.IsDatum) (hs : s.IsPermissibleII ℜ) :
    (s.transformII ℜ).nu ≤ ℜ.nu := by
  induction s with
  | nil X => exact le_rfl
  | cons B t rest ih =>
    have := hXa
    exact (ih t.isAlgebraicScheme (t.isNonsingular_and_isNonsingular_exceptional hX hs.1.1.isNonsingular).1 _
      (DatumII.Raw.transform_isDatum hX ℜ hℜ t hs.1).1 hs.2).trans
      (DatumII.Raw.nu_transform_le hX ℜ hℜ t hs.1)

theorem nu_transformII_le [Hironaka.Cited.IsHironakaBaseIsClosedSingularLocus.{u}] [Hironaka.Cited.MonoidalTransformationExistsIsProper.{u}] [Hironaka.Cited.CurveFiniteIntegralClosure.{u}] [Hironaka.Cited.IsRegularLocalRingLocalizationOfIsRegularLocalRing.{u}] (s : MonoidalSuccession X Y) [IsAlgebraicScheme X]
    (hX : X.IsNonsingular) (ℜ : DatumII.Raw X) (hℜ : ℜ.IsDatum) (hs : s.IsPermissibleII ℜ) :
    (s.transformII ℜ).nu ≤ ℜ.nu :=
  nu_transformII_le_of_isAlgebraicScheme s inferInstance hX ℜ hℜ hs

private theorem mem_sNu_of_mem_sNu_transformII_of_isAlgebraicScheme [Hironaka.Cited.IsHironakaBaseIsClosedSingularLocus.{u}] [Hironaka.Cited.MonoidalTransformationExistsIsProper.{u}] [Hironaka.Cited.CurveFiniteIntegralClosure.{u}] [Hironaka.Cited.IsRegularLocalRingLocalizationOfIsRegularLocalRing.{u}] (s : MonoidalSuccession X Y)
    (hXa : IsAlgebraicScheme X) (hX : X.IsNonsingular) (ℜ : DatumII.Raw X) (hℜ : ℜ.IsDatum)
    (hs : s.IsPermissibleII ℜ) {c : ℕ∞} {y : Y} (hy : y ∈ (s.transformII ℜ).sNu c) :
    s.composite y ∈ ℜ.sNu c := by
  induction s with
  | nil X => exact hy
  | cons B t rest ih =>
    have := hXa
    have h1 := ih t.isAlgebraicScheme (t.isNonsingular_and_isNonsingular_exceptional hX hs.1.1.isNonsingular).1 _
      (DatumII.Raw.transform_isDatum hX ℜ hℜ t hs.1).1 hs.2 hy
    rw [composite_cons, Scheme.Hom.comp_apply]
    exact DatumII.Raw.mem_sNu_of_mem_sNu_transform hX ℜ hℜ t hs.1 h1

/-- `f(S_c(f*ℜ)) ⊆ S_c(ℜ)` along a permissible succession. -/
theorem mem_sNu_of_mem_sNu_transformII [Hironaka.Cited.IsHironakaBaseIsClosedSingularLocus.{u}] [Hironaka.Cited.MonoidalTransformationExistsIsProper.{u}] [Hironaka.Cited.CurveFiniteIntegralClosure.{u}] [Hironaka.Cited.IsRegularLocalRingLocalizationOfIsRegularLocalRing.{u}] (s : MonoidalSuccession X Y) [IsAlgebraicScheme X]
    (hX : X.IsNonsingular) (ℜ : DatumII.Raw X) (hℜ : ℜ.IsDatum) (hs : s.IsPermissibleII ℜ)
    {c : ℕ∞} {y : Y} (hy : y ∈ (s.transformII ℜ).sNu c) : s.composite y ∈ ℜ.sNu c :=
  mem_sNu_of_mem_sNu_transformII_of_isAlgebraicScheme s inferInstance hX ℜ hℜ hs hy

/-- Along a permissible succession of an ambient scheme, the schemes stay ambient and the data
stay data (the centers lie in `S(ℜ)`, which misses the generic point). -/
theorem isAmbient_transformII [Hironaka.Cited.IsHironakaBaseIsClosedSingularLocus.{u}] [Hironaka.Cited.MonoidalTransformationExistsIsProper.{u}] [Hironaka.Cited.CurveFiniteIntegralClosure.{u}] [Hironaka.Cited.IsRegularLocalRingLocalizationOfIsRegularLocalRing.{u}] {N : ℕ} (s : MonoidalSuccession X Y) (hX : IsAmbient X N)
    (ℜ : DatumII.Raw X) (hℜ : ℜ.IsDatum) (hs : s.IsPermissibleII ℜ) :
    IsAmbient Y N ∧ (s.transformII ℜ).IsDatum := by
  induction s with
  | nil X => exact ⟨hX, hℜ⟩
  | cons B t rest ih =>
    have := hX.1
    have := hX.2.2.1
    have hBX : B.pts ≠ Set.univ := fun h =>
      LocSucc.genericPoint_notMem_S hX.2.1 ℜ hℜ ((hs.1.2.1 (h ▸ Set.mem_univ _)).1)
    obtain ⟨h1, h2, h3, h4⟩ := MonoidalTransformation.transform_isAmbient hX.2.1 hs.1.1 hBX t
    exact ih ⟨h1, h2, h3, h4.trans hX.2.2.2⟩ _
      (DatumII.Raw.transform_isDatum hX.2.1 ℜ hℜ t hs.1).1 hs.2

/-- A succession permissible for a type I datum `ℜ_I = (⋃ E_i; V; B'')` with open restriction
is permissible for the type II datum `ℜ` with closed restriction `F`, as long as the principal
subscheme `B''` of `ℜ_I` lies in `S_*(ℜ) ∩ F`, `U` is not empty, and the divisor of `ℜ_I` has the
same points as `⋃ E_i`.  This is the induction of pp. 284–285, with the printed invariants "`_kB''` is
contained in `S_*(_kℜ^N_II) = S_ν(_kℜ^N_II)` as well as in `_kF'`" and "`_kU''` is not empty": "The
monoidal transformation `f'_k` with center `_kC` (which is permissible for `_kℜ''`) is clearly
permissible for `_kℜ'`, because `_kC ⊂ _kB''`.  Since `_kC ≠ _kB''` (for `_kU''` is not empty),
`_{k+1}B''` must be contained in `S_ν(_{k+1}ℜ^N_II)`, and hence `S_ν(_{k+1}ℜ^N_II) =
S_*(_{k+1}ℜ^N_II)`."  The conditions are inherited by the transforms.

Gap in the paper filled: "`_{k+1}B''` must be contained in `S_ν(_{k+1}ℜ^N_II)`" is not argued.  Lean
proves it: `_{k+1}B''` is the closure of its part off the exceptional subscheme, where `f_k` is a local
isomorphism, and `S_ν` is closed (Lemma 2).  Where `_kC ≠ _kB''` is used (as printed): the part of
`_kB''` off `_kC` is not empty (it contains a point of `_kU''`), so that `ν(_{k+1}ℜ) = ν` and
`S_ν(_{k+1}ℜ) = S_*(_{k+1}ℜ)`. -/
theorem isPermissibleIIClosed_of_isPermissibleIOpen_of_nonempty [Hironaka.Cited.IsHironakaBaseIsClosedSingularLocus.{u}] [Hironaka.Cited.MonoidalTransformationExistsIsProper.{u}] [Hironaka.Cited.CurveFiniteIntegralClosure.{u}] [Hironaka.Cited.IsRegularLocalRingLocalizationOfIsRegularLocalRing.{u}] (h : MonoidalSuccession X Y) :
    ∀ (ℜ : DatumII.Raw X) (ℜI : DatumI.Raw X) (U : Set X) (F : Subscheme X),
      IsAlgebraicScheme X → X.IsNonsingular → ℜ.IsDatum → ℜI.IsDatum →
      ℜI.IsOpenRestriction U → U.Nonempty → ℜI.W.pts ⊆ ℜ.sStar → ℜI.W.IsContainedIn F →
      ℜI.E.pts = ℜ.eUnion.pts → h.IsPermissibleIOpen ℜI U →
      h.IsPermissibleIIClosed ℜ F ∧ (h.transformII ℜ).nu = ℜ.nu ∧
        (h.transformI ℜI).W.pts ⊆ (h.transformII ℜ).sStar ∧
        (h.transformI ℜI).W.IsContainedIn (h.strictTransform F) ∧
        (h.transformI ℜI).E.pts = (h.transformII ℜ).eUnion.pts := by
  induction h with
  | nil X =>
    intro ℜ ℜI U F _ _ _ _ _ _ hWS hWF hE _
    exact ⟨trivial, rfl, hWS, hWF, hE⟩
  | cons C t rest ih =>
    intro ℜ ℜI U F hXa hX hℜ hℜI hU hUne hWS hWF hE hs
    have := hXa
    obtain ⟨hC, hrest⟩ := hs
    have hCW : C.pts ⊆ ℜI.W.pts := hC.1.pts_subset_W
    -- the center is permissible for `ℜ`: `_kC ⊂ _kB'' ⊆ S_*(_kℜ)`
    have hCperm : ℜ.IsPermissible C := by
      refine ⟨hC.1.1, fun y hy => hWS (hCW hy), fun y hy => ?_⟩
      have := (hC.1.2.2 y hy).2.2
      exact (Subscheme.hasOnlyNormalCrossingsWithAt_congr hE C y).mp this
    have hCF : ℜ.IsPermissibleClosed F C :=
      ⟨hCperm, fun y hy => pts_subset_of_isContainedIn hWF (hCW hy)⟩
    -- the transforms
    have := t.isAlgebraicScheme
    have hX' := (t.isNonsingular_and_isNonsingular_exceptional hX hC.1.1.isNonsingular).1
    have hℜ' := (DatumII.Raw.transform_isDatum hX ℜ hℜ t hCperm).1
    obtain ⟨hℜI', -, hU'⟩ := DatumI.Raw.transform_isDatum hX ℜI hℜI t hC.1
    -- `_kC ≠ _kB''` (for `_kU''` is not empty): a point `u` of `U` is not in `C ⊆ W − U`,
    -- and has a point `u'` over it, off the exceptional subscheme, in `W'` and in `U'`
    obtain ⟨u, huU⟩ := hUne
    have huW : u ∈ ℜI.W.pts := by
      obtain ⟨U₀, -, hU₀⟩ := hU.1
      exact (hU₀ ▸ huU).2
    have huC : u ∉ C.pts := fun hu => (hC.2 hu).2 huU
    obtain ⟨u', hu'⟩ := t.exists_apply_eq_of_notMem huC
    have hu'E : u' ∉ t.exceptional.pts := by
      rw [MonoidalTransformation.pts_exceptional]
      exact fun hh => huC (hu' ▸ hh)
    have hu'W : u' ∈ (ℜI.transform t).W.pts := by
      show u' ∈ (Subscheme.strictTransform t ℜI.W).pts
      rw [MonoidalTransformation.pts_strictTransform_eq_closure]
      exact subset_closure ⟨show t.f u' ∈ ℜI.W.pts by rw [hu']; exact huW, hu'E⟩
    have hu'U : u' ∈ DatumI.Raw.transformOpen t U := show t.f u' ∈ U by rw [hu']; exact huU
    -- `ν(_{k+1}ℜ) = ν`: `u'` lies in `S_ν(_{k+1}ℜ)`, `ν(_{k+1}ℜ) ≤ ν(_kℜ)`
    have hu'S : u' ∈ (ℜ.transform t).sNu ℜ.nu :=
      (DatumII.Raw.mem_sNu_transform_iff_of_notMem hX ℜ t hu'E ℜ.nu).mpr
        (by rw [hu']; exact hWS huW)
    have hν' : (ℜ.transform t).nu = ℜ.nu := le_antisymm
      (DatumII.Raw.nu_transform_le hX ℜ hℜ t hCperm)
      (hu'S.2.trans (le_iSup₂ (f := fun x (_ : x ∈ (ℜ.transform t).S) => (ℜ.transform t).nuAt x)
        u' hu'S.1))
    -- `W' ⊆ S_ν(ℜ')`: "`_{k+1}B''` must be contained in `S_ν(_{k+1}ℜ^N_II)`", and hence
    -- `S_ν = S_*` (`ν(_{k+1}ℜ) = ν`)
    have hWS' : (ℜI.transform t).W.pts ⊆ (ℜ.transform t).sStar := by
      show _ ⊆ (ℜ.transform t).sNu (ℜ.transform t).nu
      rw [hν']
      show (Subscheme.strictTransform t ℜI.W).pts ⊆ _
      rw [MonoidalTransformation.pts_strictTransform_eq_closure]
      refine closure_minimal (fun y hy => ?_) (LocSucc.isClosed_sNu hX' _ ℜ.nu)
      exact (DatumII.Raw.mem_sNu_transform_iff_of_notMem hX ℜ t hy.2 ℜ.nu).mpr (hWS hy.1)
    have hWF' : (ℜI.transform t).W.IsContainedIn (Subscheme.strictTransform t F) :=
      MonoidalTransformation.isContainedIn_strictTransform t hWF
    -- the divisors have the same points
    have hE' : (ℜI.transform t).E.pts = (ℜ.transform t).eUnion.pts := by
      show ((Subscheme.strictTransform t ℜI.E).union t.exceptional).pts =
        (⨅ k, Fin.snoc (α := fun _ => Subscheme t.X')
          (fun i => Subscheme.strictTransform t (ℜ.E i)) t.exceptional k).pts
      rw [Subscheme.union, Subscheme.pts_inf, Subscheme.pts_iInf,
        MonoidalTransformation.pts_strictTransform_congr t hE, DatumII.Raw.eUnion,
        MonoidalTransformation.pts_strictTransform_eq_closure, Subscheme.pts_iInf,
        Set.preimage_iUnion, Set.iUnion_sdiff, closure_iUnion_of_finite]
      ext y
      simp only [Set.mem_union, Set.mem_iUnion, Fin.exists_fin_succ', Fin.snoc_castSucc,
        Fin.snoc_last, MonoidalTransformation.pts_strictTransform_eq_closure]
    obtain ⟨h1, h2, h3, h4, h5⟩ := ih (ℜ.transform t) (ℜI.transform t)
      (DatumI.Raw.transformOpen t U) (Subscheme.strictTransform t F) inferInstance hX' hℜ'
      hℜI' (hU' U hU hC) ⟨u', hu'U⟩ hWS' hWF' hE' hrest
    exact ⟨⟨hCF, h1⟩, h2.trans hν', h3, h4, h5⟩

end MonoidalSuccession

/-! ### Transforms with empty center, and pull-backs along composites -/

namespace DatumII.Raw

variable {X Y Z : Scheme.{u}}

theorem pullback_id (ℜ : Raw X) : ℜ.pullback (𝟙 X) = ℜ := by
  show (⟨ℜ.α, fun i => Subscheme.totalTransform (𝟙 X) (ℜ.E i), ℜ.a,
    Subscheme.totalTransform (𝟙 X) ℜ.J, ℜ.b⟩ : Raw X) = ⟨ℜ.α, ℜ.E, ℜ.a, ℜ.J, ℜ.b⟩
  simp only [Subscheme.totalTransform_id]

theorem pullback_comp (g : Z ⟶ Y) (g' : Y ⟶ X) (ℜ : Raw X) :
    ℜ.pullback (g ≫ g') = (ℜ.pullback g').pullback g := by
  show (⟨ℜ.α, fun i => Subscheme.totalTransform (g ≫ g') (ℜ.E i), ℜ.a,
    Subscheme.totalTransform (g ≫ g') ℜ.J, ℜ.b⟩ : Raw Z) =
    ⟨ℜ.α, fun i => Subscheme.totalTransform g (Subscheme.totalTransform g' (ℜ.E i)), ℜ.a,
      Subscheme.totalTransform g (Subscheme.totalTransform g' ℜ.J), ℜ.b⟩
  simp only [Subscheme.totalTransform_comp]

/-- A monoidal transformation with empty center is an isomorphism, and the transform of a datum
has the same characteristics as its pull-back. -/
theorem sameChar_transform_of_pts_eq_empty {B : Subscheme X} (t : MonoidalTransformation X B)
    (hB : B.pts = ∅) (ℜ : Raw X) : SameChar (ℜ.transform t) (ℜ.pullback t.f) := by
  have hexc : t.exceptional = Subscheme.empty := by
    refine Subscheme.eq_empty_of_pts_eq_empty ?_
    rw [MonoidalTransformation.pts_exceptional, hB, Set.preimage_empty]
  have hst : ∀ V, Subscheme.strictTransform t V = Subscheme.totalTransform t.f V := by
    intro V
    refine Subscheme.ext_stalkIdeal fun y => ?_
    refine t.strictTransform_stalkIdeal_of_notMem V ?_
    rw [hexc, Subscheme.pts_empty]
    exact id
  have h := sameChar_pullback_transform_of_lift_disjoint t t.f (𝟙 t.X') (Category.id_comp _)
    (by rw [Subscheme.totalTransform_id, hexc]) (fun V => by rw [Subscheme.totalTransform_id, hst])
    ℜ
  rwa [pullback_id] at h

end DatumII.Raw

/-! ### Lifting successions for type II data (pp. 283–285) -/

namespace MonoidalSuccession

variable {X Y : Scheme.{u}}

/-- Along a succession permissible for `(ℜ, F)` the transforms of `F` stay closed restrictions
(Remark 1, `rem:I.1-transform-is-datum-II`). -/
theorem isClosedRestriction_transformII [Hironaka.Cited.IsHironakaBaseIsClosedSingularLocus.{u}] [Hironaka.Cited.MonoidalTransformationExistsIsProper.{u}] [Hironaka.Cited.CurveFiniteIntegralClosure.{u}] [Hironaka.Cited.IsRegularLocalRingLocalizationOfIsRegularLocalRing.{u}] {N : ℕ} (s : MonoidalSuccession X Y)
    (hX : IsAmbient X N) (ℜ : DatumII.Raw X) (hℜ : ℜ.IsDatum) (F : Subscheme X)
    (hF : ℜ.IsClosedRestriction F) (hs : s.IsPermissibleIIClosed ℜ F) :
    (s.transformII ℜ).IsClosedRestriction (s.strictTransform F) := by
  induction s with
  | nil X => exact hF
  | cons B t rest ih =>
    have := hX.1
    obtain ⟨hA, hℜ'⟩ := (cons B t (nil _)).isAmbient_transformII hX ℜ hℜ ⟨hs.1.1, trivial⟩
    exact ih hA _ hℜ' _ ((DatumII.Raw.transform_isDatum hX.2.1 ℜ hℜ t hs.1.1).2.1 F hF hs.1)
      hs.2

/-- If `F` contains every point, the successions permissible for `(ℜ, F)` are those permissible
for `ℜ` (the strict transforms of `F` contain every point). -/
theorem isPermissibleIIClosed_of_pts_eq_univ [Hironaka.Cited.MonoidalTransformationExistsIsProper.{u}] (s : MonoidalSuccession X Y)
    (hX : IsAlgebraicScheme X) (ℜ : DatumII.Raw X) (F : Subscheme X) (hF : F.pts = Set.univ)
    (hs : s.IsPermissibleII ℜ) :
    s.IsPermissibleIIClosed ℜ F ∧ (s.strictTransform F).pts = Set.univ := by
  induction s with
  | nil X => exact ⟨trivial, hF⟩
  | cons B t rest ih =>
    have := t.isAlgebraicScheme
    obtain ⟨h1, h2⟩ := ih inferInstance _ _ (t.pts_strictTransform_eq_univ hF) hs.2
    exact ⟨⟨⟨hs.1, fun y _ => hF ▸ Set.mem_univ y⟩, h1⟩, h2⟩

end MonoidalSuccession

namespace LocSucc

open MonoidalSuccession

/-- An irreducible subscheme meeting the range of a flat preimmersion `j` is the closure of its
part in the range (its generic point lies in the range, which is closed under generization). -/
theorem pts_subset_closure_image {Y Z : Scheme.{u}} (j : Z ⟶ Y) [Flat j] [IsPreimmersion j]
    {D : Subscheme Y} (hD : D.IsIrreducible)
    (hne : (Subscheme.totalTransform j D).pts.Nonempty) :
    D.pts ⊆ closure (j.base '' (Subscheme.totalTransform j D).pts) := by
  obtain ⟨η, hη⟩ := QuasiSober.sober (Subscheme.isIrreducible_pts D hD) D.support.isClosed
  obtain ⟨z, hz⟩ := hne
  rw [FlatPreimm.pts_totalTransform] at hz
  obtain ⟨z', hz'⟩ := FlatPreimm.mem_range_of_specializes j (hη.specializes hz) ⟨z, rfl⟩
  have hz'D : z' ∈ (Subscheme.totalTransform j D).pts := by
    rw [FlatPreimm.pts_totalTransform]
    show j z' ∈ D.pts
    rw [hz']
    exact hη.mem
  have hηimg : η ∈ j.base '' (Subscheme.totalTransform j D).pts := ⟨z', hz'D, hz'⟩
  intro y hy
  exact closure_mono (Set.singleton_subset_iff.mpr hηimg)
    (specializes_iff_mem_closure.mp (hη.specializes hy))

/-- The lifting step of pp. 283–285 for a non-empty center.  Let `j : Z → Y` be a flat
preimmersion into an ambient scheme `Y` of dimension `N`, `ℜ` a type II datum on `Y` with
`ν(ℜ) ≤ ν`, `F` a subscheme of `Y`, and `B̄` a non-empty center on `Z` contained in
`S_ν(ℜ_Z) ∩ F_Z` with which `⋃ (E_i)_Z` has only normal crossings.  Let `B''` be the smallest
subscheme of `Y` inducing `B̄`.  Theorem `I₂^{N,n''}`, `n'' = dim B'' < N`, applied to
`(⋃ E_i; B'')` with open restriction the resolved points of `B''`, gives a succession `h` which
is permissible for `(ℜ, F)` and whose centers avoid the range of `j`; the strict transform `B*`
of `B''` is then permissible for `(h*ℜ, h*F)` and induces `B̄`.  The succession `h` followed by
the monoidal transformation with center `B*` lifts the monoidal transformation of `Z` with
center `B̄`, the transforms of `ℜ` corresponding up to the identification of p. 275.  Here `ν(ℜ) = ν`
("`S_*(_kℜ^N_II) = S_ν(_kℜ^N_II)`", p. 285) since `B̄ ⊆ S_ν(ℜ_Z)` is non-empty, `_kU''` is not empty
(the points of `B''` over `B̄` are resolved: "`(B'' − U'')_S` is empty"), and the permissibility of `h`
for `(ℜ, F)` is `isPermissibleIIClosed_of_isPermissibleIOpen_of_nonempty`, with the printed
invariants of p. 285.

Gap in the paper filled: the paper says only "we see immediately … properties (1)–(3)"; for
the transform of the type II datum by `B*` to induce that by `B̄` one needs that `B*` lies on
exactly those `E_i` whose localizations contain `B̄` (`hcont`, which governs the new
coefficient `a_{α+1}`) and that `ν` does not drop under localization (`hνeq`, which governs
`J·P^{-ν}`).  Also `n'' = dim B'' < N` is derived from `B'' ⊆ S_ν(ℜ)`, which misses the
generic point. -/
theorem lift_transformationII [Hironaka.Cited.IsHironakaBaseIsClosedSingularLocus.{u}] [Hironaka.Cited.MonoidalTransformationExistsIsProper.{u}] [Hironaka.Cited.CurveFiniteIntegralClosure.{u}] [Hironaka.Cited.IsRegularLocalRingLocalizationOfIsRegularLocalRing.{u}] (hL1 : ResolvedSetIsOpen.{u}) (N : ℕ)
    (hI₂ : ∀ n : ℕ, n < N → FundamentalTheorem.I₂.{u} N n) (ν : ℕ∞) {Y Z : Scheme.{u}} (hY : IsAmbient Y N)
    (j : Z ⟶ Y) [Flat j] [IsPreimmersion j] (ℜ : DatumII.Raw Y) (hℜ : ℜ.IsDatum)
    (hν : ℜ.nu ≤ ν) (F : Subscheme Y) {Bb : Subscheme Z} (hBbc : Bb.IsCenter)
    (hBbne : Bb.pts.Nonempty) (hBbS : Bb.pts ⊆ (ℜ.pullback j).sNu ν)
    (hBbF : Bb.pts ⊆ (Subscheme.totalTransform j F).pts)
    (hBbnc : ∀ z ∈ Bb.pts, (ℜ.pullback j).eUnion.HasOnlyNormalCrossingsWithAt Bb z)
    (tb : MonoidalTransformation Z Bb) :
    ∃ (Y' : Scheme.{u}) (s : MonoidalSuccession Y Y') (j' : tb.X' ⟶ Y'), Flat j' ∧
      IsPreimmersion j' ∧ s.IsPermissibleIIClosed ℜ F ∧ j' ≫ s.composite = tb.f ≫ j ∧
      Set.range j'.base = s.composite.base ⁻¹' Set.range j.base ∧
      DatumII.Raw.SameChar ((s.transformII ℜ).pullback j') ((ℜ.pullback j).transform tb) ∧
      ∀ V, Subscheme.totalTransform j' (s.strictTransform V) =
        Subscheme.strictTransform tb (Subscheme.totalTransform j V) := by
  have := hY.1
  have := hY.2.2.1
  set B'' := FlatPreimm.closureLift j Bb with hB''
  have hBbirr : Bb.IsIrreducible := by
    rcases hBbc with h | h
    · exfalso
      have : Bb.pts = ∅ := by rw [h]; exact Subscheme.pts_empty
      rw [this] at hBbne
      exact hBbne.ne_empty rfl
    · exact h.2
  have hBbred : Bb.IsReduced := hBbc.isReduced
  have hjB : Subscheme.totalTransform j B'' = Bb :=
    FlatPreimm.totalTransform_closureLift j Bb hBbred
  have hB''red : B''.IsReduced := FlatPreimm.closureLift_isReduced j Bb
  have hB''irr : B''.IsIrreducible := FlatPreimm.closureLift_isIrreducible j Bb hBbirr
  have hmemB'' : ∀ z ∈ Bb.pts, j z ∈ B''.pts := fun z hz => by
    rw [hB'', FlatPreimm.pts_closureLift]
    exact subset_closure ⟨z, hz, rfl⟩
  -- `B'' ⊆ S_ν(ℜ) ∩ F`
  have hB''S : B''.pts ⊆ ℜ.sNu ν := by
    rw [hB'', FlatPreimm.pts_closureLift]
    refine closure_minimal ?_ (isClosed_sNu hY.2.1 ℜ ν)
    rintro _ ⟨z, hz, rfl⟩
    exact (DatumII.Raw.mem_sNu_pullback j ℜ ν z).mp (hBbS hz)
  have hB''F : B''.pts ⊆ F.pts := by
    rw [hB'', FlatPreimm.pts_closureLift]
    refine closure_minimal ?_ F.support.isClosed
    rintro _ ⟨z, hz, rfl⟩
    have := hBbF hz
    rwa [FlatPreimm.pts_totalTransform] at this
  -- `ν(ℜ) = ν`, so that `S_ν(ℜ) = S_*(ℜ)` ("`S_*(_kℜ^N_II) = S_ν(_kℜ^N_II)`", p. 285)
  have hνℜ : ℜ.nu = ν := by
    refine le_antisymm hν ?_
    obtain ⟨z, hz⟩ := hBbne
    have hz' := hBbS hz
    exact hz'.2.trans ((le_iSup₂ (f := fun x (_ : x ∈ (ℜ.pullback j).S) => (ℜ.pullback j).nuAt x)
      z hz'.1).trans (DatumII.Raw.nu_pullback_le j ℜ))
  have hStar : ℜ.sNu ν = ℜ.sStar := by rw [DatumII.Raw.sStar, hνℜ]
  -- `n'' = dim B'' < N`
  have hB''ne : B''.pts.Nonempty := by
    obtain ⟨z, hz⟩ := hBbne
    exact ⟨j z, hmemB'' z hz⟩
  have hB''u : B''.pts ≠ Set.univ := fun h =>
    genericPoint_notMem_S hY.2.1 ℜ hℜ (hB''S (h ▸ Set.mem_univ _)).1
  have hdimlt : B''.dim + 1 ≤ (N : WithBot ℕ∞) :=
    (dim_add_one_le_of_pts_ne_univ hB''u hB''ne).trans hY.2.2.2.le
  obtain ⟨n'', hn'', hn''N⟩ := exists_nat_of_add_one_le (Subscheme.dim_ne_bot hB''ne) hdimlt
  -- the type I datum `(⋃ E_i; B'')` and the resolved points `U''` of `B''`
  set ℜI := ℜ.eUnionDatumI B'' with hℜIdef
  have hℜI : ℜI.IsDatum := DatumII.Raw.isDatum_eUnionDatumI hY.2.1 hℜ hB''red
  have hres : ∀ z ∈ Bb.pts, ℜI.ResolvedAt (j z) := by
    intro z hz
    rw [← DatumI.Raw.resolvedAt_pullback_iff j ℜI (fun i => i.elim0) z]
    refine ⟨?_, fun i => i.elim0, ?_⟩
    · show (Subscheme.totalTransform j B'').IsSimpleAt z
      rw [hjB]
      exact ⟨hz, Subscheme.isRegular_stalk_quot Bb hBbc.isNonsingular hz⟩
    · show (Subscheme.totalTransform j ℜ.eUnion).HasOnlyNormalCrossingsWithAt
        (Subscheme.totalTransform j B'') z
      rw [hjB]
      refine (Subscheme.hasOnlyNormalCrossingsWithAt_congr ?_ Bb z).mpr (hBbnc z hz)
      rw [FlatPreimm.pts_totalTransform, DatumII.Raw.pts_eUnion_pullback]
  obtain ⟨U₀, hU₀, hU₀eq⟩ := hL1 Y hY.1 hY.2.1 ℜI hℜI
  set U'' : Set Y := {y ∈ ℜI.W.pts | ℜI.ResolvedAt y} with hU''def
  have hU'' : ℜI.IsOpenRestriction U'' := by
    refine ⟨⟨U₀, hU₀, hU₀eq⟩, ?_, fun y hy => hy.2⟩
    obtain ⟨z, hz⟩ := hBbne
    have hjzU : j z ∈ U₀ ∩ ℜI.W.pts := by
      rw [← hU₀eq]
      exact ⟨hmemB'' z hz, hres z hz⟩
    have hirr := Subscheme.isIrreducible_pts B'' hB''irr
    have := subset_closure_inter_of_isPreirreducible_of_isOpen hirr.2 hU₀
      ⟨j z, hjzU.2, hjzU.1⟩
    rw [hU₀eq, Set.inter_comm]
    exact this
  -- "`_kU''` is not empty" (the points of `B''` over `B̄_b` are resolved)
  have hU''ne : U''.Nonempty := by
    obtain ⟨z, hz⟩ := hBbne
    exact ⟨j z, hmemB'' z hz, hres z hz⟩
  -- Theorem `I₂^{N, n''}`
  obtain ⟨Y₁, h, hperm, hresolved⟩ := hI₂ n'' hn''N Y hY ⟨ℜI, hℜI⟩ U'' hU'' hn''
  have hperm' : h.IsPermissibleIOpen ℜI U'' := hperm
  have havoid : h.CentersAvoid (Set.range j.base) := by
    refine centersAvoid_of_isPermissibleIOpen h ℜI U'' _ hperm' fun y hy hyr => ?_
    obtain ⟨z, rfl⟩ := hyr
    have : j z ∈ j.base '' Bb.pts := by
      rw [← FlatPreimm.pts_closureLift_inter_range]
      exact ⟨hy, z, rfl⟩
    obtain ⟨z', hz', hzz⟩ := this
    have hz'z := j.isEmbedding.injective hzz
    subst hz'z
    exact ⟨hy, hres z' hz'⟩
  -- `h` is permissible for `(ℜ, F)` (pp. 284–285)
  obtain ⟨hpermII, hνh, hWSh, hWFh, hEh⟩ := h.isPermissibleIIClosed_of_isPermissibleIOpen_of_nonempty ℜ ℜI
    U'' F hY.1 hY.2.1 hℜ hℜI hU'' hU''ne (hStar ▸ hB''S)
    (Subscheme.isContainedIn_of_pts_subset hB''red hB''F) rfl hperm'
  obtain ⟨j₁, hfl₁, hpre₁, hj₁, hr₁, hst₁, hℜ₁⟩ := h.exists_lift_of_centersAvoidII j havoid
  set Bs := h.strictTransform B'' with hBs
  have hBsj : Subscheme.totalTransform j₁ Bs = Bb := (hst₁ B'').trans hjB
  have hWBs : (h.transformI ℜI).W = Bs := transformI_W h ℜI
  have hresolved' : (h.transformI ℜI).ResolvedEverywhere := hresolved
  have hBsns : Bs.IsNonsingular := Subscheme.isNonsingular_of_stalk_quot Bs fun y hy => by
    have := (hresolved' y (by rw [hWBs]; exact hy)).1.2
    rwa [hWBs] at this
  have hBsirr : Bs.IsIrreducible :=
    strictTransform_isIrreducible_of_centersAvoid h j havoid B'' hB''irr
      (by rw [hjB]; exact hBbne)
  -- the center `B*` is permissible for `(h*ℜ, h*F)`
  have hBsperm : (h.transformII ℜ).IsPermissibleClosed (h.strictTransform F) Bs := by
    refine ⟨⟨Or.inr ⟨hBsns, hBsirr⟩, fun y hy => ?_, fun y hy => ?_⟩, fun y hy => ?_⟩
    · exact hWSh (hWBs ▸ hy)
    · have := (hresolved' y (hWBs ▸ hy)).2.2
      rw [hWBs] at this
      exact (Subscheme.hasOnlyNormalCrossingsWithAt_congr hEh Bs y).mp this
    · exact pts_subset_of_isContainedIn hWFh (hWBs ▸ hy)
  obtain ⟨ts, -⟩ := MonoidalTransformation.exists_isProper Y₁ Bs
  obtain ⟨j', hfl', hpre', hsq, hr', hexc', hst'⟩ := ts.exists_lift j₁ hBsj tb
  -- `ν` does not drop under the pull-back
  have hSC := hℜ₁ ℜ
  have hνeq : ((h.transformII ℜ).pullback j₁).nu = (h.transformII ℜ).nu := by
    refine le_antisymm (DatumII.Raw.nu_pullback_le j₁ _) ?_
    obtain ⟨z, hz⟩ := hBbne
    have hz' : z ∈ ((h.transformII ℜ).pullback j₁).sNu ν := by
      rw [hSC.sNu_eq]
      exact hBbS hz
    rw [hνh, hνℜ]
    exact hz'.2.trans
      (le_iSup₂ (f := fun x (_ : x ∈ ((h.transformII ℜ).pullback j₁).S) =>
        ((h.transformII ℜ).pullback j₁).nuAt x) z hz'.1)
  -- `B*` lies on exactly those `E_i` whose pull-backs contain `B̄`
  have hBspts : Bs.pts ⊆ closure (j₁.base '' Bb.pts) := by
    have := pts_subset_closure_image j₁ hBsirr (by rw [hBsj]; exact hBbne)
    rwa [hBsj] at this
  have hcont : ∀ i, Bs.IsContainedIn ((h.transformII ℜ).E i) ↔
      Bb.IsContainedIn (Subscheme.totalTransform j₁ ((h.transformII ℜ).E i)) := by
    intro i
    constructor
    · intro hc
      rw [← hBsj]
      exact fun U => FlatPreimm.totalTransform_mono j₁ (show _ ≤ Bs from fun U => hc U) U
    · intro hc
      refine Subscheme.isContainedIn_of_pts_subset (Subscheme.isReduced_of_isNonsingular hBsns)
        (hBspts.trans (closure_minimal ?_ ((h.transformII ℜ).E i).support.isClosed))
      rintro _ ⟨z, hz, rfl⟩
      have := pts_subset_of_isContainedIn hc hz
      rwa [FlatPreimm.pts_totalTransform] at this
  have hmatch := DatumII.Raw.pullback_transform_of_lift ts j₁ tb j' hsq hexc' hst'
    (h.transformII ℜ) hcont hνeq
  refine ⟨ts.X', h.append (cons Bs ts (nil _)), j', hfl', hpre', ?_, ?_, ?_, ?_, fun V => ?_⟩
  · rw [isPermissibleIIClosed_append]
    exact ⟨hpermII, hBsperm, trivial⟩
  · rw [composite_append, composite_cons, composite_nil, Category.id_comp, ← Category.assoc, hsq,
      Category.assoc, hj₁]
  · rw [hr', hr₁, composite_append, composite_cons, composite_nil, Category.id_comp,
      Scheme.Hom.comp_base, TopCat.coe_comp, Set.preimage_comp]
  · rw [transformII_append, transformII_cons, transformII_nil, hmatch]
    exact hSC.transform tb
  · rw [strictTransform_append, strictTransform_cons, strictTransform_nil, hst', hst₁]

/-- The lifting step for type II data (pp. 283–285): a monoidal transformation of `Z`
permissible for `(ℜ_Z, F_Z)`, where `ℜ_Z` has the characteristics of the pull-back of `ℜ` and
`ν(ℜ_Z) = ν ≥ ν(ℜ)`, is lifted by a succession of `Y` permissible for `(ℜ, F)`; the transforms
correspond again.  (For an empty center, the monoidal transformation of `Y` with empty center
lifts it.) -/
theorem lift_stepII [Hironaka.Cited.IsHironakaBaseIsClosedSingularLocus.{u}] [Hironaka.Cited.MonoidalTransformationExistsIsProper.{u}] [Hironaka.Cited.CurveFiniteIntegralClosure.{u}] [Hironaka.Cited.IsRegularLocalRingLocalizationOfIsRegularLocalRing.{u}] (hL1 : ResolvedSetIsOpen.{u}) (N : ℕ)
    (hI₂ : ∀ n : ℕ, n < N → FundamentalTheorem.I₂.{u} N n) (ν : ℕ∞) {Y Z : Scheme.{u}} (hY : IsAmbient Y N)
    (j : Z ⟶ Y) [Flat j] [IsPreimmersion j] (ℜ : DatumII.Raw Y) (hℜ : ℜ.IsDatum)
    (hν : ℜ.nu ≤ ν) (F : Subscheme Y) (ℜZ : DatumII.Raw Z)
    (hZ : DatumII.Raw.SameChar ℜZ (ℜ.pullback j)) (hνZ : ℜZ.nu = ν) {Bb : Subscheme Z}
    (hBb : ℜZ.IsPermissibleClosed (Subscheme.totalTransform j F) Bb)
    (tb : MonoidalTransformation Z Bb) :
    ∃ (Y' : Scheme.{u}) (s : MonoidalSuccession Y Y') (j' : tb.X' ⟶ Y'), Flat j' ∧
      IsPreimmersion j' ∧ s.IsPermissibleIIClosed ℜ F ∧
      Set.range j'.base = s.composite.base ⁻¹' Set.range j.base ∧
      DatumII.Raw.SameChar (ℜZ.transform tb) ((s.transformII ℜ).pullback j') ∧
      Subscheme.totalTransform j' (s.strictTransform F) =
        Subscheme.strictTransform tb (Subscheme.totalTransform j F) := by
  by_cases h0 : Bb.pts.Nonempty
  · have hBbS : Bb.pts ⊆ (ℜ.pullback j).sNu ν := by
      rw [← hZ.sNu_eq, ← hνZ]
      exact hBb.1.2.1
    have hBbnc : ∀ z ∈ Bb.pts, (ℜ.pullback j).eUnion.HasOnlyNormalCrossingsWithAt Bb z := by
      rw [← hZ.eUnion_eq]
      exact hBb.1.2.2
    obtain ⟨Y', s, j', hfl, hpre, hperm, -, hr, hSC, hst⟩ := lift_transformationII hL1 N hI₂ ν hY j ℜ hℜ
      hν F hBb.1.1 h0 hBbS hBb.2 hBbnc tb
    exact ⟨Y', s, j', hfl, hpre, hperm, hr, (hZ.transform tb).trans hSC.symm, hst F⟩
  · have hBbpts : Bb.pts = ∅ := Set.not_nonempty_iff_eq_empty.mp h0
    have hBe : Bb = Subscheme.empty := Subscheme.eq_empty_of_pts_eq_empty hBbpts
    obtain ⟨j', hfl, hpre, hsq, hr, -, hst⟩ :=
      (MonoidalTransformation.idEmpty Y).exists_lift j
        ((Subscheme.totalTransform_empty j).trans hBe.symm) tb
    refine ⟨Y, cons Subscheme.empty (MonoidalTransformation.idEmpty Y) (nil _), j', hfl, hpre,
      ⟨⟨⟨Or.inl rfl, fun y hy => ?_, fun y hy => ?_⟩, fun y hy => ?_⟩, trivial⟩, ?_, ?_, hst F⟩
    · rw [Subscheme.pts_empty] at hy
      exact hy.elim
    · rw [Subscheme.pts_empty] at hy
      exact hy.elim
    · rw [Subscheme.pts_empty] at hy
      exact hy.elim
    · change Set.range j'.base = (𝟙 Y ≫ 𝟙 Y : Y ⟶ Y).base ⁻¹' _
      rw [hr]
      rfl
    · have hsq' : j' ≫ (MonoidalTransformation.idEmpty Y).f = tb.f ≫ j := hsq
      have h1 := (DatumII.Raw.sameChar_transform_of_pts_eq_empty tb hBbpts ℜZ).trans
        (hZ.pullback tb.f)
      rw [← DatumII.Raw.pullback_comp, ← hsq', DatumII.Raw.pullback_comp] at h1
      refine h1.trans ?_
      have h2 := DatumII.Raw.sameChar_transform_of_pts_eq_empty
        (MonoidalTransformation.idEmpty Y) Subscheme.pts_empty ℜ
      exact (h2.pullback j').symm

/-- The empty succession of `Y` already has the property required of the lifting as soon as
`S_ν(ℜ_Z) ∩ F_Z = ∅`. -/
theorem lift_stop (ν : ℕ∞) {Y Z : Scheme.{u}} (j : Z ⟶ Y) [Flat j] [IsPreimmersion j]
    (ℜ : DatumII.Raw Y) (F : Subscheme Y) (ℜZ : DatumII.Raw Z)
    (hZ : DatumII.Raw.SameChar ℜZ (ℜ.pullback j))
    (hempty : ℜZ.sNu ν ∩ (Subscheme.totalTransform j F).pts = ∅) :
    ∃ (Y' : Scheme.{u}) (s : MonoidalSuccession Y Y'), s.IsPermissibleIIClosed ℜ F ∧
      ∀ y ∈ (s.transformII ℜ).sNu ν ∩ (s.strictTransform F).pts,
        s.composite y ∉ Set.range j.base := by
  refine ⟨Y, nil Y, trivial, fun y hy hyr => ?_⟩
  obtain ⟨z, hz⟩ := hyr
  have hz' : j z = y := hz
  have hz1 : z ∈ ℜZ.sNu ν := by
    rw [hZ.sNu_eq, DatumII.Raw.mem_sNu_pullback, hz']
    exact hy.1
  have hz2 : z ∈ (Subscheme.totalTransform j F).pts := by
    rw [FlatPreimm.pts_totalTransform]
    show j z ∈ F.pts
    rw [hz']
    exact hy.2
  exact (Set.eq_empty_iff_forall_notMem.mp hempty) z ⟨hz1, hz2⟩

end LocSucc

namespace MonoidalSuccession

variable {X Y : Scheme.{u}}

/-- The succession `f̄ = {f̄_j}`, `0 ≤ j ≤ a − 1`, of `X̄_0` is *minimal* for `S_ν(ᵃℜ̄) ∩ ᵃF̄ = ∅`
(p. 283: "such that, if `f̄*(ℜ'_S) = (ᵃℜ̄, ᵃF̄)`, then `S_ν(ᵃℜ̄) ∩ ᵃF̄` is empty.  We may assume
that this last condition is not satisfied if we omit the last transformation `f̄_{a−1}`"):
`S_ν(ᵇℜ̄) ∩ ᵇF̄` is non-empty for `b < a` and empty for `b = a`. -/
def IsMinimalSNuEmptyIIClosed (ν : ℕ∞) :
    {X Y : Scheme.{u}} → MonoidalSuccession X Y → DatumII.Raw X → Subscheme X → Prop
  | _, _, nil _, ℜ, F => ℜ.sNu ν ∩ F.pts = ∅
  | _, _, cons _ t rest, ℜ, F =>
      (ℜ.sNu ν ∩ F.pts).Nonempty ∧
      rest.IsMinimalSNuEmptyIIClosed ν (ℜ.transform t) (Subscheme.strictTransform t F)

/-- "We may assume that this last condition is not satisfied if we omit the last transformation
`f̄_{a−1}`" (p. 283): omitting the last transformation while the condition `S_ν(ᵃℜ̄) ∩ ᵃF̄ = ∅`
persists, one gets a permissible succession which is minimal for it (a prefix of the given one). -/
theorem exists_isMinimalSNuEmptyIIClosed (ν : ℕ∞) (s : MonoidalSuccession X Y) :
    ∀ (ℜ : DatumII.Raw X) (F : Subscheme X), s.IsPermissibleIIClosed ℜ F →
      (s.transformII ℜ).sNu ν ∩ (s.strictTransform F).pts = ∅ →
      ∃ (Y' : Scheme.{u}) (s' : MonoidalSuccession X Y'),
        s'.IsPermissibleIIClosed ℜ F ∧ s'.IsMinimalSNuEmptyIIClosed ν ℜ F := by
  induction s with
  | nil X =>
    intro ℜ F _ h
    exact ⟨X, nil X, trivial, h⟩
  | cons B t rest ih =>
    intro ℜ F hs h
    by_cases h0 : (ℜ.sNu ν ∩ F.pts).Nonempty
    · obtain ⟨Y', s', hp, hm⟩ := ih (ℜ.transform t) (Subscheme.strictTransform t F) hs.2 h
      exact ⟨Y', cons B t s', ⟨hs.1, hp⟩, h0, hm⟩
    · exact ⟨_, nil _, trivial, Set.not_nonempty_iff_eq_empty.mp h0⟩

end MonoidalSuccession

namespace LocSucc

open MonoidalSuccession

/-- Lifting a whole minimal succession for type II data (pp. 283–285, "(1)–(3)"): if `f̄` is a
succession of `Z` permissible for `(ℜ_Z, F_Z)` which is minimal for `S_ν(f̄*ℜ_Z) ∩ F̄ = ∅`
(`MonoidalSuccession.IsMinimalSNuEmptyIIClosed`), where `ℜ_Z` has the characteristics of the
pull-back of `ℜ` and `ν(ℜ) ≤ ν`, then there is a succession `f'` of `Y` permissible for `(ℜ, F)`
such that no point of `S_ν(f'*ℜ) ∩ F'` lies over the range of `j`.  By induction on `b`, each center
`B̄_b`, `b < a`, being lifted by `lift_stepII`; until then `ν(ᵇℜ̄) = ν`, because
`S_ν(ᵇℜ̄) ∩ ᵇF̄ ≠ ∅` (minimality). -/
theorem lift_successionII [Hironaka.Cited.IsHironakaBaseIsClosedSingularLocus.{u}] [Hironaka.Cited.MonoidalTransformationExistsIsProper.{u}] [Hironaka.Cited.CurveFiniteIntegralClosure.{u}] [Hironaka.Cited.IsRegularLocalRingLocalizationOfIsRegularLocalRing.{u}] (hL1 : ResolvedSetIsOpen.{u}) (N : ℕ)
    (hI₂ : ∀ n : ℕ, n < N → FundamentalTheorem.I₂.{u} N n) (ν : ℕ∞) {Z Z' : Scheme.{u}}
    (sb : MonoidalSuccession Z Z') :
    ∀ {Y : Scheme.{u}} (j : Z ⟶ Y) [Flat j] [IsPreimmersion j] (ℜ : DatumII.Raw Y)
      (F : Subscheme Y) (ℜZ : DatumII.Raw Z), IsAmbient Y N → ℜ.IsDatum → ℜ.nu ≤ ν →
      DatumII.Raw.SameChar ℜZ (ℜ.pullback j) →
      sb.IsPermissibleIIClosed ℜZ (Subscheme.totalTransform j F) →
      sb.IsMinimalSNuEmptyIIClosed ν ℜZ (Subscheme.totalTransform j F) →
      ∃ (Y' : Scheme.{u}) (s : MonoidalSuccession Y Y'), s.IsPermissibleIIClosed ℜ F ∧
        ∀ y ∈ (s.transformII ℜ).sNu ν ∩ (s.strictTransform F).pts,
          s.composite y ∉ Set.range j.base := by
  induction sb with
  | nil Z =>
    intro Y j _ _ ℜ F ℜZ _ _ _ hZ _ hmin
    exact lift_stop ν j ℜ F ℜZ hZ hmin
  | cons Bb tb rest ih =>
    intro Y j _ _ ℜ F ℜZ hY hℜ hν hZ hsb hmin
    have := hY.1
    obtain ⟨hBb, hrest⟩ := hsb
    obtain ⟨hne, hmin'⟩ := hmin
    -- `ν(ℜ_Z) = ν`: `S_ν(ℜ_Z) ∩ F_Z ≠ ∅` (minimality)
    have hνZ : ℜZ.nu = ν := by
      refine le_antisymm ?_ ?_
      · rw [hZ.nu_eq]
        exact (DatumII.Raw.nu_pullback_le j ℜ).trans hν
      · obtain ⟨z, hz, -⟩ := hne
        exact hz.2.trans (le_iSup₂ (f := fun x (_ : x ∈ ℜZ.S) => ℜZ.nuAt x) z hz.1)
    obtain ⟨Y₁, s₁, j₁, hfl₁, hpre₁, hperm₁, hr₁, hSC₁, hF₁⟩ :=
      lift_stepII hL1 N hI₂ ν hY j ℜ hℜ hν F ℜZ hZ hνZ hBb tb
    obtain ⟨hY₁, hℜ₁⟩ := s₁.isAmbient_transformII hY ℜ hℜ hperm₁.isPermissibleII
    have hν₁ := (s₁.nu_transformII_le hY.2.1 ℜ hℜ hperm₁.isPermissibleII).trans hν
    rw [← hF₁] at hrest hmin'
    obtain ⟨Y', s₂, hperm₂, hlast⟩ := ih j₁ (s₁.transformII ℜ) (s₁.strictTransform F)
      (ℜZ.transform tb) hY₁ hℜ₁ hν₁ hSC₁ hrest hmin'
    refine ⟨Y', s₁.append s₂, (isPermissibleIIClosed_append _ _ _ _).mpr ⟨hperm₁, hperm₂⟩,
      fun y hy hyr => ?_⟩
    rw [transformII_append, strictTransform_append] at hy
    rw [composite_append, Scheme.Hom.comp_apply] at hyr
    refine hlast y hy ?_
    rw [hr₁]
    exact hyr

end LocSucc

end Hironaka

