/-
Copyright (c) 2026 Daattavya Aggarwal, Minhyong Kim, Oisin Kim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daattavya Aggarwal, Minhyong Kim, Oisin Kim
-/
module

public import Mathlib.FieldTheory.Perfect
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.AdicCompletion.LocalRing
public import Mathlib.RingTheory.Coalgebra.IsFrobenius
public import Mathlib.RingTheory.DedekindDomain.Ideal.Basic
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.HopfAlgebra.Basic
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Architect
public import Hironaka.Ch3.Stability
public import Hironaka.Compat.AdicCompletionRegular
public import Hironaka.Compat.CurveResolution
public import Hironaka.Compat.RegularLocalization
public import Hironaka.Compat.StrictTransformDim

/-!
# Ch. III §6 (pp. 242–244): Corollary 3 (c) of Theorem 5

> COROLLARY 3. Let `R` be a regular local ring, and `M` the maximal ideal of `R`. Let `Q` be a
> prime ideal in `R`, and `J` an ideal in `R` such that `Q ⊇ J`. Suppose we have a system of
> elements `(g₁, …, g_m)` of `J` such that (i) the initial forms of the `g_j` in `gr_M(R)`
> generate the ideal `gr_M(J, R)`, and (ii) `ν_M(g_j) = ν_{QR_Q}(g_j)` for all `j`. Then we
> have the following facts: … (c) If the residue field of `R` is of characteristic zero, and
> there exists a prime ideal `Q̂` in the completion `R̂` of `R` such that `Q̂ ∩ R = Q` and that
> `Q̂R̂_{Q̂} = QR̂_{Q̂}`, then the initial forms of the elements `g_j` (`1 ≤ j ≤ m`) in
> `gr_{QR_Q}(R_Q)` generate the ideal `gr_{QR_Q}(JR_Q, R_Q)`.  (p. 242)

Assertions (a) and (b), and the predicate `IsLocallyAdaptedSystem` packaging (i) and (ii), are in
`Hironaka/Ch3/Stability.lean`; assertion (c) is kept in this separate file because its proof
(reduction to the complete case, then to `dim R/Q = 1`, then a sequence of monoidal transforms
with center the maximal ideals, pp. 243–244) uses the facts on completions of
`Hironaka/Compat/AdicCompletionRegular.lean` and the resolution of curve germs of
`Hironaka/Compat/CurveResolution.lean`.  Nothing else in the project uses it.

Structure of the proof here.
* `grIdeal_localization_eq_span_initialForm_of_regular`: the case `R/Q` regular (Lemma 7 of
  Ch. II §2).
* `exists_monoidalTransform_curveImage_lt`, `exists_ringHom_curveImage_lt_of_comap_eq`, `grIdeal_localization_eq_span_initialForm_of_curveImage_eq`, `grIdeal_localization_eq_span_initialForm_of_dimensionLEOne`: the case `dim(R/Q) ≤ 1` under the
  finiteness of the integral closure of `R/Q` (the sequence of monoidal transforms of p. 244: an
  admissible transform exists, and for every admissible transform the measure `φ(R) ∩ W` strictly
  increases; the integral closure is only semi-local, so the proofs use a "general element" of `M`).
* `grIdeal_localization_eq_span_initialForm_of_le_localization`, `forall_grIdeal_localization_eq_span_initialForm_of_finite`,
  `grIdeal_localization_eq_span_initialForm_of_finite`: the induction on `dim(R/Q)` (on the
  primes of `R`, from the top), under the finiteness condition of footnote 10.
* `finite_integralClosure_localization_quotient_of_isAdicComplete`, `RingHom.mapsRSOP_of_flat_of_map_maximalIdeal_eq`,
  `grIdeal_eq_span_initialForm_of_mapsRSOP`, `grIdeal_localization_eq_span_initialForm_of_faithfullyFlat`: the reduction to the complete case, and the final
  assembly `grIdeal_localization_eq_span_initialForm_of_adicCompletion`.

Where these steps argue differently from the paper, this is recorded as "Deviation from the paper
(…)" in the docstring and the blueprint text of Corollary 3 (c).
-/

@[expose] public section

open IsLocalRing

namespace Hironaka

universe u

/-- The canonical homomorphism `gr_I(A) → gr_{IB}(B)` induced by `α : A → B`
(`AssocGraded.map`) maps the initial form of `a` to that of `α(a)` as soon as
`ν_{IB}(α(a)) = ν_I(a)`. -/
theorem AssocGraded.map_initialForm_of_ordElem_map_eq {A B : Type u} [CommRing A] [CommRing B]
    (α : A →+* B) (I : Ideal A) (a : A)
    (h : Ideal.ordElem (I.map α) (α a) = Ideal.ordElem I a) :
    AssocGraded.map α I (initialForm I a) = initialForm (I.map α) (α a) := by
  by_cases htop : Ideal.ordElem I a = ⊤
  · have htop' : Ideal.ordElem (I.map α) (α a) = ⊤ := by rw [h, htop]
    rw [initialForm, dite_eq_left htop, map_zero, initialForm, dite_eq_left htop']
  · obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp htop
    rw [initialForm_eq_mk I hn.symm, AssocGraded.map_mk,
      initialForm_eq_mk _ (h.trans hn.symm)]

/-- A module over a ring in which the non-zero natural numbers are units is not a finite union of
proper submodules. -/
theorem _root_.Submodule.exists_forall_notMem_of_ne_top {T V : Type*} [CommRing T] [AddCommGroup V] [Module T V]
    (hT : ∀ n : ℕ, n ≠ 0 → IsUnit (n : T)) (s : Finset (Submodule T V))
    (hs : ∀ H ∈ s, H ≠ ⊤) : ∃ v : V, ∀ H ∈ s, v ∉ H := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨0, by simp⟩
  | insert H₀ s hH₀ ih =>
    obtain ⟨u, hu⟩ := ih fun H hH => hs H (Finset.mem_insert_of_mem hH)
    by_cases huH₀ : u ∉ H₀
    · refine ⟨u, fun H hH => ?_⟩
      rcases Finset.mem_insert.mp hH with rfl | hH
      · exact huH₀
      · exact hu H hH
    push Not at huH₀
    obtain ⟨w, hw⟩ : ∃ w, w ∉ H₀ := by
      by_contra h
      push Not at h
      exact hs H₀ (Finset.mem_insert_self _ _) (eq_top_iff.mpr fun v _ => h v)
    -- `(k - l) w ∈ H` with `k ≠ l` forces `w ∈ H`
    have hdiff : ∀ (H : Submodule T V) (k l : ℕ), k ≠ l → u + (k : T) • w ∈ H →
        u + (l : T) • w ∈ H → w ∈ H := by
      intro H k l hkl hk hl
      have hsub := H.sub_mem hk hl
      rw [add_sub_add_left_eq_sub, ← sub_smul] at hsub
      rcases lt_or_gt_of_ne hkl with h | h
      · have := H.neg_mem hsub
        rw [← neg_smul, neg_sub, ← Nat.cast_sub h.le] at this
        exact (Submodule.smul_mem_iff_of_isUnit H (hT _ (by omega))).mp this
      · rw [← Nat.cast_sub h.le] at hsub
        exact (Submodule.smul_mem_iff_of_isUnit H (hT _ (by omega))).mp hsub
    set B : Set ℕ := {0} ∪ ⋃ H ∈ (s : Set (Submodule T V)), {k | u + (k : T) • w ∈ H}
    have hB : B.Finite := by
      refine (Set.finite_singleton 0).union (Set.Finite.biUnion s.finite_toSet fun H hH => ?_)
      refine Set.Subsingleton.finite fun k hk l hl => ?_
      by_contra hkl
      have hwH := hdiff H k l hkl hk hl
      apply hu H hH
      have := H.sub_mem hk (H.smul_mem (k : T) hwH)
      rwa [add_sub_cancel_right] at this
    obtain ⟨k, hk⟩ := hB.exists_notMem
    refine ⟨u + (k : T) • w, fun H hH => ?_⟩
    rcases Finset.mem_insert.mp hH with rfl | hH
    · intro hmem
      have hk0 : k ≠ 0 := fun h => hk (Or.inl h)
      have := H.sub_mem hmem huH₀
      rw [add_sub_cancel_left] at this
      exact hw ((Submodule.smul_mem_iff_of_isUnit H (hT k hk0)).mp this)
    · intro hmem
      exact hk (Or.inr (Set.mem_biUnion hH hmem))

/-- "General element": in a Dedekind domain `W` with finitely many maximal ideals, an ideal
generated by a submodule `X` (over a ring in which the non-zero natural numbers are units) is
generated by a single element of `X`. -/
theorem exists_mem_span_singleton_eq_span_of_finite_isMaximal {S₀ W : Type*} [CommRing S₀] [CommRing W]
    [IsDedekindDomain W] [Algebra S₀ W] (hS₀ : ∀ n : ℕ, n ≠ 0 → IsUnit (n : S₀))
    (hfin : {n : Ideal W | n.IsMaximal}.Finite) (X : Submodule S₀ W)
    (hX : Ideal.span (X : Set W) ≠ ⊥) :
    ∃ x ∈ X, Ideal.span {x} = Ideal.span (X : Set W) := by
  classical
  set I := Ideal.span (X : Set W) with hI
  let H : Ideal W → Submodule S₀ X := fun n =>
    ((I * n).restrictScalars S₀).comap X.subtype
  have hH : ∀ n ∈ hfin.toFinset.image H, n ≠ ⊤ := by
    intro Hn hHn htop
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hHn
    have hnmax : n.IsMaximal := by simpa using hn
    have hXle : I ≤ I * n := by
      rw [hI, Ideal.span_le]
      intro y hy
      have : (⟨y, hy⟩ : X) ∈ H n := htop ▸ Submodule.mem_top
      exact this
    have heq : I * n = I * ⊤ := by
      rw [Ideal.mul_top]
      exact le_antisymm (Ideal.mul_le_inf.trans inf_le_left) hXle
    exact hnmax.ne_top (mul_left_cancel₀ hX heq)
  obtain ⟨v, hv⟩ := Submodule.exists_forall_notMem_of_ne_top hS₀ _ hH
  refine ⟨v, v.2, ?_⟩
  have hle : Ideal.span {(v : W)} ≤ I := by
    rw [Ideal.span_le, Set.singleton_subset_iff]
    exact Ideal.subset_span v.2
  obtain ⟨K, hK⟩ := Ideal.dvd_iff_le.mpr hle
  by_cases hKtop : K = ⊤
  · rw [hK, hKtop, Ideal.mul_top]
  obtain ⟨n, hnmax, hKn⟩ := Ideal.exists_le_maximal K hKtop
  exfalso
  apply hv (H n) (Finset.mem_image.mpr ⟨n, by simpa using hnmax, rfl⟩)
  show (v : W) ∈ I * n
  have : (v : W) ∈ I * K := hK ▸ Ideal.mem_span_singleton_self _
  exact Ideal.mul_mono_right hKn this

/-- Multiplying by a unit `u` multiplies the initial form by the (degree-`0`, invertible) class
of `u`. -/
theorem initialForm_mul_unit {A : Type u} [CommRing A] (I : Ideal A) (a : A) (u : Aˣ) :
    initialForm I (a * u) = initialForm I a * algebraMap A (AssocGraded I) (u : A) := by
  have hiff : ∀ n : ℕ, a * u ∈ I ^ n ↔ a ∈ I ^ n := fun n =>
    ⟨fun h => by simpa using Ideal.mul_mem_right ((u⁻¹ : Aˣ) : A) _ h,
      fun h => Ideal.mul_mem_right _ _ h⟩
  have hord : Ideal.ordElem I (a * u) = Ideal.ordElem I a := by
    simp only [Ideal.ordElem, hiff]
  by_cases htop : Ideal.ordElem I a = ⊤
  · rw [initialForm, dite_eq_left (hord.trans htop), initialForm, dite_eq_left htop, zero_mul]
  · obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp htop
    rw [initialForm_eq_mk I (hord.trans hn.symm), initialForm_eq_mk I hn.symm]
    have h0 : (u : A) ∈ I ^ 0 := by simp
    have : algebraMap A (AssocGraded I) (u : A) = AssocGraded.mk I 0 u h0 := rfl
    rw [this, AssocGraded.mk_mul_mk]
    rfl

/-- Transport of "the initial forms of the `f_j` generate `gr_I(J, A)`" along a ring
isomorphism `α : A → B`. -/
theorem grIdeal_map_eq_span_initialForm_of_bijective {A B : Type u} [CommRing A] [CommRing B]
    (α : A →+* B) (hα : Function.Bijective α) (I J : Ideal A) {m : ℕ} (f : Fin m → A)
    (h : grIdeal I J = Ideal.span (Set.range fun j => initialForm I (f j))) :
    grIdeal (I.map α) (J.map α) =
      Ideal.span (Set.range fun j => initialForm (I.map α) (α (f j))) := by
  have hord : ∀ a, Ideal.ordElem (I.map α) (α a) = Ideal.ordElem I a := by
    intro a
    have hiff : ∀ n : ℕ, α a ∈ I.map α ^ n ↔ a ∈ I ^ n := by
      intro n
      rw [← Ideal.map_pow]
      refine ⟨fun ha => ?_, Ideal.mem_map_of_mem α⟩
      rw [← Ideal.comap_map_of_bijective α hα (I := I ^ n)]
      exact ha
    simp only [Ideal.ordElem, hiff]
  have hin : ∀ a, AssocGraded.map α I (initialForm I a) = initialForm (I.map α) (α a) :=
    fun a => AssocGraded.map_initialForm_of_ordElem_map_eq α I a (hord a)
  have hgr : grIdeal (I.map α) (J.map α) = (grIdeal I J).map (AssocGraded.map α I) := by
    refine le_antisymm ?_ ?_
    · rw [grIdeal, Ideal.span_le]
      rintro _ ⟨y, hy, rfl⟩
      obtain ⟨a, ha, rfl⟩ := (Ideal.mem_map_iff_of_surjective α hα.2).mp hy
      rw [SetLike.mem_coe, ← hin]
      exact Ideal.mem_map_of_mem _ (Ideal.subset_span ⟨a, ha, rfl⟩)
    · rw [Ideal.map_le_iff_le_comap, grIdeal, Ideal.span_le]
      rintro _ ⟨a, ha, rfl⟩
      rw [SetLike.mem_coe, Ideal.mem_comap, hin]
      exact Ideal.subset_span ⟨α a, Ideal.mem_map_of_mem α ha, rfl⟩
  rw [hgr, h, Ideal.map_span, ← Set.range_comp]
  congr 2
  funext j
  exact hin (f j)

/-- Multiplying the `f_j` by units does not change the ideal generated by their initial forms. -/
theorem span_range_initialForm_mul_units {A : Type u} [CommRing A] (I : Ideal A) {m : ℕ}
    (f : Fin m → A) (u : Fin m → Aˣ) :
    Ideal.span (Set.range fun j => initialForm I (f j * u j)) =
      Ideal.span (Set.range fun j => initialForm I (f j)) := by
  refine le_antisymm (Ideal.span_le.mpr ?_) (Ideal.span_le.mpr ?_)
  · rintro _ ⟨j, rfl⟩
    show initialForm I (f j * u j) ∈ _
    rw [initialForm_mul_unit]
    exact Ideal.mul_mem_right _ _ (Ideal.subset_span ⟨j, rfl⟩)
  · rintro _ ⟨j, rfl⟩
    have : f j = f j * u j * ((u j)⁻¹ : Aˣ) := by rw [mul_assoc, Units.mul_inv, mul_one]
    show initialForm I (f j) ∈ _
    rw [this, initialForm_mul_unit]
    exact Ideal.mul_mem_right _ _ (Ideal.subset_span ⟨j, rfl⟩)

section Corollary3cRegular

variable {R : Type u} [CommRing R] [IsRegularLocalRing R]

/-- Corollary 3 (c) when `R/Q` is regular, p. 243: "The assertion (c) follows Lemma 7, §2,
Ch. II, if `R/Q` is regular."  (No hypothesis on the residue field or on the completion is needed
in this case.)

Lemma 7 (`inf_grIdeal_eq_mul_span_initialForm`) is applied with its `P := Q` and its `Q := M`:
its hypothesis (ii) is (i) of Corollary 3, and its hypothesis (i), `ν_M(g_j) = ν_Q(g_j)`, follows
from (ii) of Corollary 3 because `ν_{QR_Q} = ν_Q` when `R/Q` is regular
(`ordElem_localization_eq_of_isRegularLocalRing_quotient`).  This gives `gr_Q(J, R) = (in_Q(g_j))`.  One then passes to
`R_Q` by the canonical homomorphism `gr_Q(R) → gr_{QR_Q}(R_Q)`, which maps `in_Q(a)` to
`in_{QR_Q}(a)` (the orders agree); every element of `JR_Q` is `a · u` with `a ∈ J` and `u` a unit,
and `in_{QR_Q}(a u) = in_{QR_Q}(a) in_{QR_Q}(u)` since `gr_{QR_Q}(R_Q)` is a domain (`R_Q` is
regular). -/
theorem grIdeal_localization_eq_span_initialForm_of_regular (Q J : Ideal R) [Q.IsPrime]
    (hJQ : J ≤ Q) {m : ℕ} (g : Fin m → R) (hg : IsLocallyAdaptedSystem R Q J g)
    [hQreg : IsRegularLocalRing (R ⧸ Q)] :
    grIdeal (Q.map (algebraMap R (Localization.AtPrime Q)))
        (J.map (algebraMap R (Localization.AtPrime Q))) =
      Ideal.span (Set.range fun j =>
        initialForm (Q.map (algebraMap R (Localization.AtPrime Q)))
          (algebraMap R (Localization.AtPrime Q) (g j))) := by
  classical
  set L := Localization.AtPrime Q
  set φ : R →+* L := algebraMap R L with hφ
  -- Lemma 7 of Ch. II §2 with its `P := Q` and its `Q := M`: `gr_Q(J, R) = (in_Q(g_j))`
  have hres : IsRegularLocalRing (R ⧸ maximalIdeal R) := by
    let _ : Field (R ⧸ maximalIdeal R) := Ideal.Quotient.field _
    infer_instance
  have h7 := (inf_grIdeal_eq_mul_span_initialForm J Q (maximalIdeal R) hJQ
    (le_maximalIdeal Ideal.IsPrime.ne_top') g hg.1
    (fun j => (hg.2.2 j).trans (ordElem_localization_eq_of_isRegularLocalRing_quotient Q hQreg (g j))) hg.2.1.symm).2
  -- `gr_{QR_Q}(R_Q)` is a domain (`R_Q` regular, `QR_Q` its maximal ideal)
  have _ : IsRegularLocalRing L := isRegularLocalRing_localization_of_isRegularLocalRing_quotient Q hQreg
  have hdom : IsDomain (AssocGraded (Q.map φ)) := by
    rw [hφ, Localization.AtPrime.map_eq_maximalIdeal]
    exact isDomain_assocGraded_maximalIdeal
  -- the canonical map `gr_Q(R) → gr_{QR_Q}(R_Q)` sends `in_Q(a)` to `in_{QR_Q}(a)`
  have hmapin : ∀ a : R, AssocGraded.map φ Q (initialForm Q a) = initialForm (Q.map φ) (φ a) :=
    fun a => AssocGraded.map_initialForm_of_ordElem_map_eq φ Q a (ordElem_localization_eq_of_isRegularLocalRing_quotient Q hQreg a)
  have hspan : Ideal.span (Set.range fun j => initialForm (Q.map φ) (φ (g j))) =
      (grIdeal Q J).map (AssocGraded.map φ Q) := by
    rw [h7, Ideal.map_span, ← Set.range_comp]
    congr 2
    funext j
    exact (hmapin (g j)).symm
  rw [hspan]
  refine le_antisymm ?_ ?_
  · -- an element of `JR_Q` is `a u` with `a ∈ J`, `u` a unit
    rw [grIdeal, Ideal.span_le]
    rintro _ ⟨y, hy, rfl⟩
    obtain ⟨⟨⟨a, haJ⟩, s⟩, hys⟩ :=
      (IsLocalization.mem_map_algebraMap_iff Q.primeCompl L).mp hy
    simp only at hys
    obtain ⟨v, hv⟩ : IsUnit (φ s) := IsLocalization.map_units L s
    have hy' : y = φ a * ((v⁻¹ : Lˣ) : L) := by
      rw [← hys, ← hv, mul_assoc, Units.mul_inv, mul_one]
    rw [SetLike.mem_coe, hy', initialForm_mul_of_isDomain, ← hmapin]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ (Ideal.subset_span ⟨a, haJ, rfl⟩))
  · rw [Ideal.map_le_iff_le_comap, grIdeal, Ideal.span_le]
    rintro _ ⟨a, haJ, rfl⟩
    rw [SetLike.mem_coe, Ideal.mem_comap, hmapin]
    exact Ideal.subset_span ⟨φ a, Ideal.mem_map_of_mem φ haJ, rfl⟩

end Corollary3cRegular

/-- The conclusion of Corollary 3 (c) descends along a monoidal transform `R → R₁` with center
`M` and a prime `Q₁` of `R₁` with `R_Q = (R₁)_{Q₁}` (p. 244: "Then we have `R_Q = (R₁)_{Q₁}`,
`JR_Q = J₁(R₁)_{Q₁}`, and `(g_j)R_Q = (h_j)(R₁)_{Q₁}` for each `j`"). -/
theorem grIdeal_localization_eq_span_initialForm_of_transform {R : Type u} [CommRing R] [IsRegularLocalRing R]
    [IsDomain R] (Q J : Ideal R) [Q.IsPrime] (t : MonoidalTransform R (maximalIdeal R))
    (Q₁ : Ideal t.ring) [Q₁.IsPrime] (hQ : Q = Q₁.comap t.toRing)
    (hbij : Function.Bijective (Localization.localRingHom Q Q₁ t.toRing hQ)) (hxQ : t.x ∉ Q)
    {m : ℕ} (g : Fin m → R) (ν : Fin m → ℕ) (h : Fin m → t.ring)
    (hh : ∀ j, t.toRing t.x ^ ν j * h j = t.toRing (g j))
    (h₁ : grIdeal (Q₁.map (algebraMap t.ring (Localization.AtPrime Q₁)))
        ((strictTransformIdeal t J).map (algebraMap t.ring (Localization.AtPrime Q₁))) =
      Ideal.span (Set.range fun j => initialForm (Q₁.map (algebraMap t.ring
        (Localization.AtPrime Q₁))) (algebraMap t.ring (Localization.AtPrime Q₁) (h j)))) :
    grIdeal (Q.map (algebraMap R (Localization.AtPrime Q)))
        (J.map (algebraMap R (Localization.AtPrime Q))) =
      Ideal.span (Set.range fun j =>
        initialForm (Q.map (algebraMap R (Localization.AtPrime Q)))
          (algebraMap R (Localization.AtPrime Q) (g j))) := by
  classical
  set L := Localization.AtPrime Q
  set L₁ := Localization.AtPrime Q₁
  set f := Localization.localRingHom Q Q₁ t.toRing hQ
  let e : L ≃+* L₁ := RingEquiv.ofBijective f hbij
  let α : L₁ →+* L := e.symm.toRingHom
  have hαbij : Function.Bijective α := e.symm.bijective
  have hcomp : ∀ r, α (algebraMap t.ring L₁ (t.toRing r)) = algebraMap R L r := by
    intro r
    have : f (algebraMap R L r) = algebraMap t.ring L₁ (t.toRing r) :=
      Localization.localRingHom_to_map Q Q₁ t.toRing hQ r
    rw [← this]
    exact e.symm_apply_apply _
  -- `α` maps the maximal ideal onto the maximal ideal
  have ha : (Q₁.map (algebraMap t.ring L₁)).map α = Q.map (algebraMap R L) := by
    rw [Localization.AtPrime.map_eq_maximalIdeal, Localization.AtPrime.map_eq_maximalIdeal]
    exact IsLocalRing.map_maximalIdeal_of_surjective α hαbij.2
  have hxQ₁ : t.toRing t.x ∉ Q₁ := fun hx => hxQ (hQ ▸ hx)
  -- `J₁(R₁)_{Q₁} = J(R₁)_{Q₁}` (`x` is a unit in `(R₁)_{Q₁}`)
  have hJ₁ : (strictTransformIdeal t J).map (algebraMap t.ring L₁) =
      (J.map t.toRing).map (algebraMap t.ring L₁) := by
    apply le_antisymm
    · rw [Ideal.map_le_iff_le_comap, strictTransformIdeal, Ideal.span_le]
      rintro y ⟨x', hx', f', hf', ν', -, hy⟩
      have hx'Q : x' ∉ Q₁ := by
        intro hx'mem
        apply hxQ₁
        have hmem : t.toRing t.x ∈ (maximalIdeal R).map t.toRing :=
          Ideal.mem_map_of_mem _ t.x_mem
        rw [← hx'] at hmem
        exact (Ideal.span_singleton_le_iff_mem _).mpr hx'mem hmem
      have hu : IsUnit (algebraMap t.ring L₁ x' ^ ν') :=
        (IsLocalization.map_units L₁ (⟨x', hx'Q⟩ : Q₁.primeCompl)).pow ν'
      rw [SetLike.mem_coe, Ideal.mem_comap,
        ← Ideal.unit_mul_mem_iff_mem _ hu, ← map_pow, ← map_mul, hy]
      exact Ideal.mem_map_of_mem _ (Ideal.mem_map_of_mem _ hf')
    · apply Ideal.map_mono
      rw [Ideal.map_le_iff_le_comap]
      intro f' hf'
      exact Ideal.subset_span ⟨t.xR, t.span_xR_eq_map, f', hf', 0, by simp, by simp⟩
  have hJ : ((strictTransformIdeal t J).map (algebraMap t.ring L₁)).map α = J.map (algebraMap R L) := by
    rw [hJ₁, Ideal.map_map, Ideal.map_map]
    congr 1
    exact RingHom.ext hcomp
  -- `α(h_j) = g_j · x^{-ν_j}`
  have hv : IsUnit (algebraMap R L t.x) := IsLocalization.map_units L (⟨t.x, hxQ⟩ : Q.primeCompl)
  let u : Fin m → Lˣ := fun j => (hv.unit ^ ν j)⁻¹
  have hc : ∀ j, α (algebraMap t.ring L₁ (h j)) = algebraMap R L (g j) * u j := by
    intro j
    have h1 := congrArg (fun z => α (algebraMap t.ring L₁ z)) (hh j)
    simp only [map_mul, map_pow, hcomp] at h1
    have hu1 : (u j : L) * algebraMap R L t.x ^ ν j = 1 := by
      have e1 : ((hv.unit ^ ν j : Lˣ) : L) = algebraMap R L t.x ^ ν j := by
        rw [Units.val_pow_eq_pow_val, IsUnit.unit_spec]
      rw [← e1]
      exact Units.inv_mul _
    rw [← h1]
    linear_combination (-(α (algebraMap t.ring L₁ (h j)))) * hu1
  have key := grIdeal_map_eq_span_initialForm_of_bijective α hαbij _ _
    (fun j => algebraMap t.ring L₁ (h j)) h₁
  rw [ha, hJ] at key
  simp only [hc] at key
  rw [key, span_range_initialForm_mul_units]

/-- If `f` is integral over `R` through `ρ ∘ σ` and `u ∈ T` satisfies `ρ(u) f = 1`, then `f ∈ ρ(T)`. -/
theorem exists_eq_of_isIntegral_of_mul_eq_one {R T F : Type*} [CommRing R] [CommRing T] [Field F]
    (σ : R →+* T) (ρ : T →+* F) (f : F) (p : Polynomial R) (hp : p.Monic)
    (hf : p.eval₂ (ρ.comp σ) f = 0) (u : T) (hu : ρ u * f = 1) : ∃ v : T, ρ v = f := by
  classical
  set n := p.natDegree with hn
  have hn0 : n ≠ 0 := by
    intro h0
    have : p = 1 := Polynomial.eq_one_of_monic_natDegree_zero hp h0
    rw [this] at hf
    simp at hf
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hn0
  have hsum := hp.as_sum
  rw [← hn] at hsum
  rw [hsum] at hf
  simp only [Polynomial.eval₂_add, Polynomial.eval₂_X_pow, Polynomial.eval₂_finsetSum,
    Polynomial.eval₂_mul, Polynomial.eval₂_C, Polynomial.eval₂_X_pow] at hf
  set g := ρ u with hg
  have hfg : f * g = 1 := by rw [mul_comm]; exact hu
  have key : f = -∑ i ∈ Finset.range n, (ρ.comp σ) (p.coeff i) * g ^ (k - i) := by
    have h1 : f ^ n * g ^ k = f := by
      rw [hk, pow_succ]
      calc f ^ k * f * g ^ k = f * (f * g) ^ k := by ring
        _ = f := by rw [hfg, one_pow, mul_one]
    have h2 : ∀ i ∈ Finset.range n, (ρ.comp σ) (p.coeff i) * f ^ i * g ^ k =
        (ρ.comp σ) (p.coeff i) * g ^ (k - i) := by
      intro i hi
      have hik : i ≤ k := by
        have := Finset.mem_range.mp hi
        omega
      have : f ^ i * g ^ k = g ^ (k - i) := by
        calc f ^ i * g ^ k = f ^ i * (g ^ i * g ^ (k - i)) := by rw [← pow_add, Nat.add_sub_cancel' hik]
          _ = (f * g) ^ i * g ^ (k - i) := by ring
          _ = g ^ (k - i) := by rw [hfg, one_pow, one_mul]
      rw [mul_assoc, this]
    have h3 : f ^ n + ∑ i ∈ Finset.range n, (ρ.comp σ) (p.coeff i) * f ^ i = 0 := hf
    have h4 := congrArg (· * g ^ k) h3
    simp only [zero_mul, add_mul, Finset.sum_mul] at h4
    rw [h1, Finset.sum_congr rfl h2] at h4
    linear_combination h4
  refine ⟨-∑ i ∈ Finset.range n, σ (p.coeff i) * u ^ (k - i), ?_⟩
  rw [key]
  simp [map_sum, hg]

section Cor3cCurve

attribute [local instance] RingHom.ker_isPrime

variable {F : Type u} [Field F] {S₀ : Type u} [CommRing S₀] [Algebra S₀ F]
  (W : Subalgebra S₀ F)

/-- The ring `B = {f ∈ F | φ(b) f ∈ W for some b ∈ R ∖ M with φ(b) ∈ W}` (`W` localized at the
elements `φ(b)` of `W` with `b` a unit of `R`). -/
def curveLocalRing {R : Type u} [CommRing R] [IsLocalRing R] (φ : R →+* F) : Subring F where
  carrier := {f | ∃ b, b ∉ maximalIdeal R ∧ φ b ∈ W ∧ φ b * f ∈ W}
  one_mem' := ⟨1, by simp, by simp, by simp⟩
  mul_mem' := by
    rintro f₁ f₂ ⟨b₁, hb₁, hb₁W, hf₁⟩ ⟨b₂, hb₂, hb₂W, hf₂⟩
    refine ⟨b₁ * b₂, fun h => ?_, by rw [map_mul]; exact mul_mem hb₁W hb₂W, ?_⟩
    · rcases (Ideal.IsPrime.mem_or_mem inferInstance h) with h | h
      · exact hb₁ h
      · exact hb₂ h
    · have : φ (b₁ * b₂) * (f₁ * f₂) = (φ b₁ * f₁) * (φ b₂ * f₂) := by rw [map_mul]; ring
      rw [this]
      exact mul_mem hf₁ hf₂
  add_mem' := by
    rintro f₁ f₂ ⟨b₁, hb₁, hb₁W, hf₁⟩ ⟨b₂, hb₂, hb₂W, hf₂⟩
    refine ⟨b₁ * b₂, fun h => ?_, by rw [map_mul]; exact mul_mem hb₁W hb₂W, ?_⟩
    · rcases (Ideal.IsPrime.mem_or_mem inferInstance h) with h | h
      · exact hb₁ h
      · exact hb₂ h
    · have : φ (b₁ * b₂) * (f₁ + f₂) = φ b₂ * (φ b₁ * f₁) + φ b₁ * (φ b₂ * f₂) := by
        rw [map_mul]; ring
      rw [this]
      exact add_mem (mul_mem hb₂W hf₁) (mul_mem hb₁W hf₂)
  zero_mem' := ⟨1, by simp, by simp, by simp⟩
  neg_mem' := by
    rintro f ⟨b, hb, hbW, hf⟩
    exact ⟨b, hb, hbW, by rw [mul_neg]; exact neg_mem hf⟩

/-- For a monoidal transform `R'` of `R` with center `M` (element `x`) and a prime `P'` of `R'`
over a prime `P` of `R` with `x ∉ P`, the canonical map `R_P → R'_{P'}` is bijective:
`R' ⊆ R[1/x] ⊆ R_P` inside the field of quotients (as in `exists_curveImage_lt_of_lift`). -/
theorem MonoidalTransform.localRingHom_bijective_of_x_notMem {R : Type u} [CommRing R] [IsRegularLocalRing R] [IsDomain R]
    (t : MonoidalTransform R (maximalIdeal R)) (P : Ideal R) [P.IsPrime] (P' : Ideal t.ring)
    [P'.IsPrime] (hP' : P = P'.comap t.toRing) (hxP : t.x ∉ P) :
    Function.Bijective (Localization.localRingHom P P' t.toRing hP') := by
  have hxM : t.x ∈ maximalIdeal R := t.x_mem
  set f := Localization.localRingHom P P' t.toRing hP'
  set T := Localization.AtPrime P'
  let A := blowupAlgebra R (maximalIdeal R) t.x
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

/-- If `M ⊆ xR + P` with `x ∈ M ∖ P`, then the maximal ideal of `R/P` is principal, so `R/P` is a
discrete valuation ring, hence regular (as in `exists_curveImage_lt_of_lift`). -/
theorem isRegularLocalRing_quotient_of_forall_sub_mem {R : Type u} [CommRing R]
    [IsRegularLocalRing R] (P : Ideal R) [P.IsPrime] {x : R} (hxM : x ∈ maximalIdeal R)
    (hxP : x ∉ P) (hMx : ∀ m ∈ maximalIdeal R, ∃ r, m - x * r ∈ P) :
    IsRegularLocalRing (R ⧸ P) := by
  have hloc : IsLocalRing (R ⧸ P) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk P) Ideal.Quotient.mk_surjective
  have hmaxS : maximalIdeal (R ⧸ P) = Ideal.span {Ideal.Quotient.mk P x} := by
    rw [← IsLocalRing.map_maximalIdeal_of_surjective (Ideal.Quotient.mk P)
      Ideal.Quotient.mk_surjective]
    apply le_antisymm
    · rw [Ideal.map_le_iff_le_comap]
      intro m hm
      obtain ⟨r, hr⟩ := hMx m hm
      rw [Ideal.mem_comap, Ideal.mem_span_singleton']
      refine ⟨Ideal.Quotient.mk P r, ?_⟩
      rw [← map_mul, mul_comm, eq_comm, Ideal.Quotient.eq]
      exact hr
    · rw [Ideal.span_le, Set.singleton_subset_iff]
      exact Ideal.mem_map_of_mem _ hxM
  have hxS : Ideal.Quotient.mk P x ≠ 0 := by
    rwa [Ne, Ideal.Quotient.eq_zero_iff_mem]
  have hnf : ¬ IsField (R ⧸ P) := by
    rw [IsLocalRing.isField_iff_maximalIdeal_eq, hmaxS]
    intro h
    exact hxS (Ideal.span_singleton_eq_bot.mp h)
  have : IsDiscreteValuationRing (R ⧸ P) :=
    ((IsDiscreteValuationRing.TFAE (R ⧸ P) hnf).out 5 1).mp
      (⟨⟨_, hmaxS⟩⟩ : (maximalIdeal (R ⧸ P)).IsPrincipal)
  infer_instance

/-- The monoidal transform part of `exists_monoidalTransform_curveImage_lt`, for a given transform `t` with center the
maximal ideal and the extension `ψ : R[M/x] → F` of `φ`, with values in `cor3cLocRing W φ`,
whose center on `R[M/x]` is the maximal ideal `t.M'`. -/
theorem exists_ringHom_curveImage_lt_of_transform {R : Type u} [CommRing R] [IsRegularLocalRing R] [IsDomain R]
    (φ : R →+* F) (hφS : ∀ s, algebraMap S₀ F s ∈ φ.range)
    (hInv : ∀ r, ∃ b, b ∉ maximalIdeal R ∧ φ b ∈ W ∧ φ (b * r) ∈ W)
    (hS : ¬ IsRegularLocalRing (R ⧸ RingHom.ker φ))
    (t : MonoidalTransform R (maximalIdeal R)) (hx0 : φ t.x ≠ 0)
    (hdiv : ∀ m ∈ maximalIdeal R, ∀ _ : φ m ∈ W, ∃ w : W, φ m = φ t.x * w)
    (ψA : blowupAlgebra R (maximalIdeal R) t.x →+* F)
    (hψA_alg : ∀ r, ψA (algebraMap R _ r) = φ r)
    (hψA : ∀ (a : blowupAlgebra R (maximalIdeal R) t.x) (m : ℕ) (g : R),
      (a : FractionRing R) * algebraMap R _ t.x ^ m = algebraMap R _ g → ψA a * φ t.x ^ m = φ g)
    (hψA_B : ∀ a, ψA a ∈ curveLocalRing W φ)
    (hNunit : ∀ u : t.M'.primeCompl, IsUnit (ψA u)) (hNmax : t.M'.IsMaximal) :
    ∃ (φ' : t.ring →+* F) (hP' : RingHom.ker φ = (RingHom.ker φ').comap t.toRing),
      Function.Bijective (Localization.localRingHom _ _ t.toRing hP') ∧
      RingHom.IsResiduallyAlgebraic (R := R) (R' := t.ring) t.toRing ∧
      IsRegularLocalRing t.ring ∧ t.x ∉ RingHom.ker φ ∧
      (∀ r, ∃ b, b ∉ maximalIdeal t.ring ∧ φ' b ∈ W ∧ φ' (b * r) ∈ W) ∧
      ∃ hφ'S : ∀ s, algebraMap S₀ F s ∈ φ'.range,
        curveImage W φ hφS < curveImage W φ' hφ'S := by
  classical
  set P := RingHom.ker φ with hPdef
  have hunitR : ∀ b, b ∉ maximalIdeal R → IsUnit b := fun b hb => by
    by_contra h
    exact hb ((IsLocalRing.mem_maximalIdeal b).mpr h)
  have hxM : t.x ∈ maximalIdeal R := t.x_mem
  have hxP : t.x ∉ P := fun h => hx0 (RingHom.mem_ker.mp h)
  have hxK : algebraMap R (FractionRing R) t.x ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective R _)).mpr t.x_ne_zero
  let φ' : t.ring →+* F := IsLocalization.lift (M := t.M'.primeCompl) (S := t.ring) hNunit
  have hφ'_alg : ∀ b, φ' (algebraMap _ t.ring b) = ψA b := IsLocalization.lift_eq hNunit
  have hφ'_toRing : ∀ r, φ' (t.toRing r) = φ r := fun r => (hφ'_alg _).trans (hψA_alg r)
  have hφ'_comp : φ'.comp t.toRing = φ := RingHom.ext hφ'_toRing
  have hP' : P = (RingHom.ker φ').comap t.toRing := by
    rw [RingHom.comap_ker, hφ'_comp]
  have hM0 : maximalIdeal R ≠ ⊥ := fun h => t.x_ne_zero (by simpa [h] using hxM)
  have hresreg : IsRegularLocalRing (R ⧸ maximalIdeal R) := by
    let _ : Field (R ⧸ maximalIdeal R) := Ideal.Quotient.field _
    infer_instance
  -- `φ'` again satisfies the invariant: `φ'(a/u) = ψ(a)/ψ(u)`
  have hInv' : ∀ y : t.ring, ∃ b, b ∉ maximalIdeal t.ring ∧ φ' b ∈ W ∧ φ' (b * y) ∈ W := by
    intro y
    obtain ⟨a, u, rfl⟩ := IsLocalization.exists_mk'_eq t.M'.primeCompl y
    obtain ⟨ba, hba, hbaW, hbaa⟩ := hψA_B a
    obtain ⟨bu, hbu, hbuW, hbuu⟩ := hψA_B u
    refine ⟨t.toRing (ba * bu) * algebraMap _ t.ring (u : blowupAlgebra R (maximalIdeal R) t.x), ?_, ?_, ?_⟩
    · have h1 : IsUnit (t.toRing (ba * bu)) := ((hunitR ba hba).mul (hunitR bu hbu)).map _
      have h2 : IsUnit (algebraMap _ t.ring (u : blowupAlgebra R (maximalIdeal R) t.x)) :=
        IsLocalization.map_units t.ring u
      exact fun hmem => (IsLocalRing.mem_maximalIdeal _).mp hmem (h1.mul h2)
    · rw [map_mul, hφ'_toRing, hφ'_alg, map_mul, mul_assoc]
      exact mul_mem hbaW hbuu
    · have hmk : φ' (IsLocalization.mk' t.ring a u) * ψA u = ψA a := by
        rw [← hφ'_alg, ← map_mul, IsLocalization.mk'_spec, hφ'_alg]
      have : φ' (t.toRing (ba * bu) * algebraMap _ t.ring (u : blowupAlgebra R (maximalIdeal R) t.x) *
          IsLocalization.mk' t.ring a u) = φ bu * (φ ba * ψA a) := by
        rw [map_mul, map_mul, hφ'_toRing, hφ'_alg, map_mul, ← hmk]
        ring
      rw [this]
      exact mul_mem hbuW hbaa
  have hφ'S : ∀ s, algebraMap S₀ F s ∈ φ'.range := by
    intro s
    obtain ⟨r, hr⟩ := hφS s
    exact ⟨t.toRing r, (hφ'_toRing r).trans hr⟩
  refine ⟨φ', hP', MonoidalTransform.localRingHom_bijective_of_x_notMem t P _ hP' hxP,
    (t.isMaximal_iff_isResiduallyAlgebraic).mp hNmax,
    (t.isRegularLocalRing_and_isLocalHom_and_span_xR_eq_map (maximalIdeal.isMaximal R).isPrime hM0 hresreg).1, hxP, hInv', hφ'S, ?_⟩
  refine lt_of_le_of_ne (fun v hv => ?_) (fun heq => hS ?_)
  · obtain ⟨r, hr⟩ := hv
    exact ⟨t.toRing r, (hφ'_toRing r).trans hr⟩
  -- otherwise `φ(bm)/φ(x) ∈ φ(R)` for all `m ∈ M`, i.e. `M ⊆ xR + P`
  refine isRegularLocalRing_quotient_of_forall_sub_mem P hxM hxP fun m hm => ?_
  obtain ⟨b, hb, hbW, hbm⟩ := hInv m
  obtain ⟨w, hw⟩ := hdiv (b * m) (Ideal.mul_mem_left _ _ hm) hbm
  let a : blowupAlgebra R (maximalIdeal R) t.x :=
    ⟨algebraMap R _ (b * m) / algebraMap R _ t.x,
      Algebra.subset_adjoin ⟨b * m, Ideal.mul_mem_left _ _ hm, rfl⟩⟩
  have ha1 : ψA a * φ t.x = φ (b * m) := by
    have := hψA a 1 (b * m) (by simp only [a, pow_one]; exact div_mul_cancel₀ _ hxK)
    rwa [pow_one] at this
  have haw : ψA a = w := mul_right_cancel₀ hx0 (by rw [ha1, hw, mul_comm])
  have hmem : w ∈ curveImage W φ' hφ'S := ⟨algebraMap _ t.ring a, (hφ'_alg a).trans haw⟩
  rw [← heq] at hmem
  obtain ⟨r, hr⟩ := hmem
  refine ⟨(((hunitR b hb).unit⁻¹ : Rˣ) : R) * r, ?_⟩
  have hbmr : b * m - t.x * r ∈ P := by
    rw [RingHom.mem_ker, map_sub, hw, map_mul φ t.x r, hr, sub_self]
  have hbb : (((hunitR b hb).unit⁻¹ : Rˣ) : R) * b = 1 := (hunitR b hb).val_inv_mul
  have := Ideal.mul_mem_left P (((hunitR b hb).unit⁻¹ : Rˣ) : R) hbmr
  convert this using 1
  linear_combination (-m) * hbb

/-- Every element of `W` is integral over `R` through `φ`, and so is every element of the ring
`curveLocalRing W φ` (`W` localized at the `φ(b)`, `b` a unit of `R`). -/
theorem exists_monic_eval₂_eq_zero_of_mem_curveLocalRing [Algebra.IsIntegral S₀ W]
    {R : Type u} [CommRing R] [IsLocalRing R] (φ : R →+* F)
    (hφS : ∀ s, algebraMap S₀ F s ∈ φ.range) {f : F} (hf : f ∈ curveLocalRing W φ) :
    ∃ p : Polynomial R, p.Monic ∧ p.eval₂ φ f = 0 := by
  have hintW : ∀ w : W, φ.IsIntegralElem (w : F) := by
    intro w
    obtain ⟨q, hqm, hq⟩ := Algebra.IsIntegral.isIntegral (R := S₀) w
    have hlift : q.map (algebraMap S₀ F) ∈ Polynomial.lifts φ := by
      rw [Polynomial.lifts_iff_coeff_lifts]
      intro n
      rw [Polynomial.coeff_map]
      exact hφS (q.coeff n)
    obtain ⟨p, hp, -, hpm⟩ := Polynomial.lifts_and_natDegree_eq_and_monic hlift (hqm.map _)
    refine ⟨p, hpm, ?_⟩
    rw [Polynomial.eval₂_eq_eval_map, hp, Polynomial.eval_map]
    have := congrArg (algebraMap W F) hq
    rwa [map_zero, Polynomial.hom_eval₂, ← IsScalarTower.algebraMap_eq] at this
  obtain ⟨b, hb, hbW, hbf⟩ := hf
  have hunitR : IsUnit b := by
    by_contra h
    exact hb ((IsLocalRing.mem_maximalIdeal b).mpr h)
  let _ : Algebra R F := φ.toAlgebra
  have h1 : IsIntegral R (φ b * f) := hintW ⟨_, hbf⟩
  have h2 : IsIntegral R (φ (hunitR.unit⁻¹ : Rˣ)) := isIntegral_algebraMap
  have h3 : IsIntegral R (φ (hunitR.unit⁻¹ : Rˣ) * (φ b * f)) := h2.mul h1
  have hfeq : φ (hunitR.unit⁻¹ : Rˣ) * (φ b * f) = f := by
    rw [← mul_assoc, ← map_mul]
    have : ((hunitR.unit⁻¹ : Rˣ) : R) * b = 1 := hunitR.val_inv_mul
    rw [this, map_one, one_mul]
  rw [hfeq] at h3
  exact h3

/-- A "general element" of `M`: if `R/P` is not regular, there is `x ∈ M` with `φ(x) ≠ 0` such that
`φ(m) ∈ φ(x) W` for all `m ∈ M` with `φ(m) ∈ W` (so `φ(M)W = φ(x)W`; `W` is semi-local Dedekind and the
non-zero integers are units, characteristic zero).  Used in
`exists_monoidalTransform_curveImage_lt` and `exists_ringHom_curveImage_lt_of_comap_eq`. -/
theorem exists_generalElement_of_not_isRegularLocalRing_quotient [Module.Finite S₀ W] [IsDedekindDomain W]
    (hWfin : {n : Ideal W | n.IsMaximal}.Finite) (hS₀ : ∀ n : ℕ, n ≠ 0 → IsUnit (n : S₀))
    {R : Type u} [CommRing R] [IsRegularLocalRing R] [IsDomain R] (φ : R →+* F)
    (hφS : ∀ s, algebraMap S₀ F s ∈ φ.range)
    (hInv : ∀ r, ∃ b, b ∉ maximalIdeal R ∧ φ b ∈ W ∧ φ (b * r) ∈ W)
    (hS : ¬ IsRegularLocalRing (R ⧸ RingHom.ker φ)) :
    ∃ x ∈ maximalIdeal R, φ x ≠ 0 ∧ ∀ m ∈ maximalIdeal R, φ m ∈ W → ∃ w : W, φ m = φ x * w := by
  classical
  set M := maximalIdeal R with hMdef
  set P := RingHom.ker φ with hPdef
  have hPM : P ≤ M := le_maximalIdeal (Ideal.IsPrime.ne_top inferInstance)
  -- the `S₀`-submodule `X = φ(M) ∩ W` of `W`
  let X : Submodule S₀ W :=
    { carrier := {w | ∃ m ∈ M, φ m = (w : F)}
      add_mem' := by
        rintro a b ⟨m, hm, hma⟩ ⟨n, hn, hnb⟩
        exact ⟨m + n, add_mem hm hn, by rw [map_add, hma, hnb]; rfl⟩
      zero_mem' := ⟨0, zero_mem _, by simp⟩
      smul_mem' := by
        rintro c a ⟨m, hm, hma⟩
        obtain ⟨r, hr⟩ := hφS c
        refine ⟨r * m, Ideal.mul_mem_left _ _ hm, ?_⟩
        rw [map_mul, hr, hma]
        show _ = ((c • a : W) : F)
        rw [Subalgebra.coe_smul, Algebra.smul_def] }
  -- `φ(M) ≠ 0`, as `R/P` is not regular
  obtain ⟨m₀, hm₀M, hm₀⟩ : ∃ m ∈ M, φ m ≠ 0 := by
    by_contra h
    push Not at h
    apply hS
    have hMP : M ≤ P := fun m hm => RingHom.mem_ker.mpr (h m hm)
    have hPM' : P = M := le_antisymm hPM hMP
    have : P.IsMaximal := hPM' ▸ maximalIdeal.isMaximal R
    let _ : Field (R ⧸ P) := Ideal.Quotient.field P
    infer_instance
  have hX : Ideal.span (X : Set W) ≠ ⊥ := by
    obtain ⟨b, hb, hbW, hbm⟩ := hInv m₀
    intro hbot
    have hmem : (⟨_, hbm⟩ : W) ∈ X := ⟨b * m₀, Ideal.mul_mem_left _ _ hm₀M, rfl⟩
    have h0 := (Ideal.span_eq_bot.mp hbot) _ hmem
    have hb0 : φ b ≠ 0 := fun h0 => hb (hPM (RingHom.mem_ker.mpr h0))
    exact mul_ne_zero hb0 hm₀ (by rw [← map_mul]; exact congrArg Subtype.val h0)
  obtain ⟨xw, ⟨x, hxM, hxw⟩, hxspan⟩ :=
    exists_mem_span_singleton_eq_span_of_finite_isMaximal (S₀ := S₀) hS₀ hWfin X hX
  refine ⟨x, hxM, ?_, ?_⟩
  · intro h0
    apply hX
    rw [← hxspan, Ideal.span_singleton_eq_bot]
    exact Subtype.ext (by rw [← hxw, h0]; rfl)
  · intro m hm hmW
    have : (⟨φ m, hmW⟩ : W) ∈ Ideal.span {xw} := hxspan ▸ Ideal.subset_span ⟨m, hm, rfl⟩
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp this
    refine ⟨c, ?_⟩
    rw [hxw, mul_comm]
    exact (congrArg Subtype.val hc).symm

/-- Existence of the first step of the dimension-one case of Corollary 3 (c), p. 244: "Let `R₁` be any
monoidal transform of `R` with center `M` which is residually algebraic (hence, separable algebraic) over
`R`, and such that there exists a prime ideal `Q₁` in `R₁` such that `Q₁ ∩ R = Q`."  The paper does not
say that such an `R₁` exists (gap filled here): `R/Q` is embedded by `φ : R → F` (kernel `Q`) in a
field `F`, and `W ⊆ F` is a fixed semi-local Dedekind domain, finite over a noetherian base
`S₀ ⊆ φ(R)` (in the application, the integral closure of the original `R/Q`).  The invariant `hInv`
says that `φ(R)` is a localization of `φ(R) ∩ W`.  To construct `R₁`, the element `x` is taken to be a
"general element" of `M` (`exists_generalElement_of_not_isRegularLocalRing_quotient`, using that the
non-zero integers are units, i.e. the characteristic-zero residue field), so that `φ(M) W = φ(x) W`
and all `φ(m)/φ(x)` lie in `W`; the center `M'` of the transform is the contraction of a maximal ideal
of the ring `curveLocalRing W φ ⊇ φ(R[M/x])`, integral over `R`, hence maximal (`R₁` is residually
algebraic), and `φ` extends to `R₁` with kernel `Q₁` over `Q`.

The conclusions on the invariant and on the measure `φ(R) ∩ W` (the `S₀`-submodule of `W`; "this process
cannot be repeated infinitely many times, because the integral closure of `R/Q` in its field of quotients
is a finite `R/Q`-module") hold for EVERY such `R₁` and `Q₁`, as printed:
`exists_ringHom_curveImage_lt_of_comap_eq`.  The dimension-one case uses of the present lemma only the
existence of `R₁` and `Q₁` (the transform `t`, `Q₁ = ker φ'`, residual algebraicity, regularity), and
takes everything else from `exists_ringHom_curveImage_lt_of_comap_eq`. -/
theorem exists_monoidalTransform_curveImage_lt [Module.Finite S₀ W] [IsDedekindDomain W]
    (hWfin : {n : Ideal W | n.IsMaximal}.Finite) (hS₀ : ∀ n : ℕ, n ≠ 0 → IsUnit (n : S₀))
    {R : Type u} [CommRing R] [IsRegularLocalRing R] [IsDomain R] (φ : R →+* F)
    (hφS : ∀ s, algebraMap S₀ F s ∈ φ.range)
    (hInv : ∀ r, ∃ b, b ∉ maximalIdeal R ∧ φ b ∈ W ∧ φ (b * r) ∈ W)
    (hS : ¬ IsRegularLocalRing (R ⧸ RingHom.ker φ)) :
    ∃ (t : MonoidalTransform R (maximalIdeal R)) (φ' : t.ring →+* F)
      (hP' : RingHom.ker φ = (RingHom.ker φ').comap t.toRing),
      Function.Bijective (Localization.localRingHom _ _ t.toRing hP') ∧
      RingHom.IsResiduallyAlgebraic (R := R) (R' := t.ring) t.toRing ∧
      IsRegularLocalRing t.ring ∧ t.x ∉ RingHom.ker φ ∧
      (∀ r, ∃ b, b ∉ maximalIdeal t.ring ∧ φ' b ∈ W ∧ φ' (b * r) ∈ W) ∧
      ∃ hφ'S : ∀ s, algebraMap S₀ F s ∈ φ'.range,
        curveImage W φ hφS < curveImage W φ' hφ'S := by
  classical
  set M := maximalIdeal R with hMdef
  set P := RingHom.ker φ with hPdef
  have hker : RingHom.ker φ = P := rfl
  -- elements of `W` are integral over `R` (through `φ`)
  have hintW : ∀ w : W, φ.IsIntegralElem (w : F) := by
    intro w
    obtain ⟨q, hqm, hq⟩ := Algebra.IsIntegral.isIntegral (R := S₀) w
    have hlift : q.map (algebraMap S₀ F) ∈ Polynomial.lifts φ := by
      rw [Polynomial.lifts_iff_coeff_lifts]
      intro n
      rw [Polynomial.coeff_map]
      exact hφS (q.coeff n)
    obtain ⟨p, hp, -, hpm⟩ := Polynomial.lifts_and_natDegree_eq_and_monic hlift (hqm.map _)
    refine ⟨p, hpm, ?_⟩
    rw [Polynomial.eval₂_eq_eval_map, hp, Polynomial.eval_map]
    have := congrArg (algebraMap W F) hq
    rwa [map_zero, Polynomial.hom_eval₂, ← IsScalarTower.algebraMap_eq] at this
  have hunitR : ∀ b, b ∉ M → IsUnit b := fun b hb => by
    by_contra h
    exact hb ((IsLocalRing.mem_maximalIdeal b).mpr h)
  have hPM : P ≤ M := le_maximalIdeal (Ideal.IsPrime.ne_top inferInstance)
  -- the ring `B ⊇ φ(R)`, integral over `R`
  set B := curveLocalRing W φ with hBdef
  have hφB : ∀ r, φ r ∈ B := by
    intro r
    obtain ⟨b, hb, hbW, hbr⟩ := hInv r
    exact ⟨b, hb, hbW, by rw [← map_mul]; exact hbr⟩
  let φB : R →+* B := φ.codRestrict B hφB
  have hBint : φB.IsIntegral := by
    rintro ⟨f, hfB⟩
    have ⟨b, hb, hbW, hbf⟩ := hfB
    let _ : Algebra R F := φ.toAlgebra
    have h1 : IsIntegral R (φ b * f) := hintW ⟨_, hbf⟩
    have h2 : IsIntegral R (φ ((hunitR b hb).unit⁻¹ : Rˣ)) := isIntegral_algebraMap
    have h3 : IsIntegral R (φ ((hunitR b hb).unit⁻¹ : Rˣ) * (φ b * f)) := h2.mul h1
    have hf : φ ((hunitR b hb).unit⁻¹ : Rˣ) * (φ b * f) = f := by
      rw [← mul_assoc, ← map_mul]
      have : (((hunitR b hb).unit⁻¹ : Rˣ) : R) * b = 1 := (hunitR b hb).val_inv_mul
      rw [this, map_one, one_mul]
    rw [hf] at h3
    obtain ⟨p, hpm, hp⟩ := h3
    refine ⟨p, hpm, Subtype.ext ?_⟩
    have := Polynomial.hom_eval₂ p φB B.subtype ⟨f, hfB⟩
    exact this.trans hp
  -- a general element `x`: `φ(x) W = φ(M) W` (`W` semi-local Dedekind)
  obtain ⟨x, hxM, hx0, hdiv⟩ := exists_generalElement_of_not_isRegularLocalRing_quotient W hWfin hS₀
    φ hφS hInv hS
  have hx0' : x ≠ 0 := fun h => hx0 (by rw [h, map_zero])
  have hxP : x ∉ P := fun h => hx0 (RingHom.mem_ker.mp h)
  have hxK : algebraMap R (FractionRing R) x ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective R _)).mpr hx0'
  -- the blow-up algebra `A = R[M/x]` lies in `R[1/x]`, on which `φ` extends to `ψ : A → F`
  set A := blowupAlgebra R M x with hAdef
  have hxS : Submonoid.powers x ≤ nonZeroDivisors R :=
    powers_le_nonZeroDivisors_of_noZeroDivisors hx0'
  let D := Localization.subalgebra.ofField (FractionRing R) (Submonoid.powers x) hxS
  have hunit : ∀ y : Submonoid.powers x, IsUnit (φ y) := by
    rintro ⟨_, n, rfl⟩
    exact isUnit_iff_ne_zero.mpr (by rw [map_pow]; exact pow_ne_zero n hx0)
  let ψD : D →+* F := IsLocalization.lift (M := Submonoid.powers x) (S := D) hunit
  have hψD : ∀ r, ψD (algebraMap R D r) = φ r := IsLocalization.lift_eq hunit
  have hAD : A ≤ D := by
    refine Algebra.adjoin_le ?_
    rintro _ ⟨m, -, rfl⟩
    exact ⟨m, x, Submonoid.mem_powers x, div_eq_mul_inv _ _⟩
  let ψA : A →+* F := ψD.comp (Subalgebra.inclusion hAD).toRingHom
  have hψA : ∀ (a : A) (m : ℕ) (g : R), (a : FractionRing R) * algebraMap R _ x ^ m =
      algebraMap R _ g → ψA a * φ x ^ m = φ g := by
    intro a m g h
    have h' : Subalgebra.inclusion hAD a * algebraMap R D (x ^ m) = algebraMap R D g :=
      Subtype.ext (by simpa [map_pow] using h)
    have := congrArg ψD h'
    rwa [map_mul, hψD, hψD, map_pow] at this
  have hψA_alg : ∀ r, ψA (algebraMap R A r) = φ r := by
    intro r
    simpa using hψA (algebraMap R A r) 0 r (by simp)
  clear_value ψA
  -- `ψ(A) ⊆ B`: `φ(b) · (m/x) ∈ W` for `b` as in `hInv m`, by the choice of `x`
  have hψA_B : ∀ a : A, ψA a ∈ B := by
    rintro ⟨a, ha⟩
    induction ha using Algebra.adjoin_induction with
    | mem y hy =>
      obtain ⟨m, hm, rfl⟩ := hy
      obtain ⟨b, hb, hbW, hbm⟩ := hInv m
      obtain ⟨w, hw⟩ := hdiv (b * m) (Ideal.mul_mem_left _ _ hm) hbm
      have h1 := hψA ⟨_, Algebra.subset_adjoin ⟨m, hm, rfl⟩⟩ 1 m
        (by simp only [pow_one]; exact div_mul_cancel₀ _ hxK)
      rw [pow_one] at h1
      refine ⟨b, hb, hbW, ?_⟩
      have : φ b * ψA ⟨_, Algebra.subset_adjoin ⟨m, hm, rfl⟩⟩ = w := by
        apply mul_right_cancel₀ hx0
        rw [mul_assoc, h1, ← map_mul, hw, mul_comm]
      rw [this]
      exact w.2
    | algebraMap r =>
      have e : (⟨algebraMap R (FractionRing R) r, Subalgebra.algebraMap_mem _ r⟩ : A) =
        algebraMap R A r := rfl
      rw [e, hψA_alg]
      exact hφB r
    | add y z hy hz ihy ihz =>
      have e : (⟨y + z, add_mem hy hz⟩ : A) = ⟨y, hy⟩ + ⟨z, hz⟩ := rfl
      rw [e, map_add]
      exact add_mem ihy ihz
    | mul y z hy hz ihy ihz =>
      have e : (⟨y * z, mul_mem hy hz⟩ : A) = ⟨y, hy⟩ * ⟨z, hz⟩ := rfl
      rw [e, map_mul]
      exact mul_mem ihy ihz
  let ψB : A →+* B := ψA.codRestrict B hψA_B
  have hψB_comp : ψB.comp (algebraMap R A) = φB :=
    RingHom.ext fun r => Subtype.ext (hψA_alg r)
  have hAint : ψB.IsIntegral :=
    RingHom.IsIntegral.tower_top (algebraMap R A) ψB (hψB_comp ▸ hBint)
  -- a maximal ideal `𝔫` of `B`, and the center `N = 𝔫 ∩ A` (maximal, containing `MA`)
  obtain ⟨𝔫, h𝔫⟩ := Ideal.exists_maximal B
  have hMcomap : Ideal.comap φB 𝔫 = M :=
    IsLocalRing.eq_maximalIdeal (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal φB hBint 𝔫)
  set N : Ideal A := Ideal.comap ψB 𝔫 with hNdef
  have hNmax : N.IsMaximal := Ideal.isMaximal_comap_of_isIntegral_of_isMaximal ψB hAint 𝔫
  have hMN : M.map (algebraMap R A) ≤ N := by
    rw [Ideal.map_le_iff_le_comap, Ideal.comap_comap, hψB_comp, hMcomap]
  have hNunit : ∀ u : N.primeCompl, IsUnit (ψA u) := by
    rintro ⟨b, hb⟩
    refine isUnit_iff_ne_zero.mpr fun h0 => hb ?_
    show ψB b ∈ 𝔫
    have : ψB b = 0 := Subtype.ext h0
    rw [this]
    exact zero_mem _
  exact ⟨⟨x, hxM, hx0', N, hNmax.isPrime, hMN⟩, exists_ringHom_curveImage_lt_of_transform W φ hφS hInv hS
    ⟨x, hxM, hx0', N, hNmax.isPrime, hMN⟩ hx0 hdiv ψA hψA_alg hψA hψA_B hNunit hNmax⟩

/-- The extension `φ'` of `φ` to a monoidal transform `R₁` of `R` with center `M` and a prime `Q₁` of `R₁`
with `Q₁ ∩ R = ker φ` (p. 244, "there exists a prime ideal `Q₁` in `R₁` such that `Q₁ ∩ R = Q`"): since
`R_Q = (R₁)_{Q₁}` (`MonoidalTransform.exists_ringEquiv_localization_of_comap_eq`), `φ` extends to
`R_Q`, hence to `R₁ → (R₁)_{Q₁} ≅ R_Q → F`, with kernel `Q₁`. -/
theorem exists_ringHom_ker_eq_of_comap_eq {R : Type u} [CommRing R] [IsRegularLocalRing R] [IsDomain R]
    (φ : R →+* F) (hS : ¬ IsRegularLocalRing (R ⧸ RingHom.ker φ))
    (t : MonoidalTransform R (maximalIdeal R)) (Q₁ : Ideal t.ring) [Q₁.IsPrime]
    (hQ₁ : Q₁.comap t.toRing = RingHom.ker φ) :
    ∃ φ' : t.ring →+* F, RingHom.ker φ' = Q₁ ∧ ∀ r, φ' (t.toRing r) = φ r := by
  classical
  set P := RingHom.ker φ with hPdef
  have hPM : P ≤ maximalIdeal R := le_maximalIdeal (Ideal.IsPrime.ne_top inferInstance)
  have hMP : maximalIdeal R ≠ P := by
    intro h
    apply hS
    have : P.IsMaximal := h ▸ maximalIdeal.isMaximal R
    let _ := Ideal.Quotient.field P
    infer_instance
  obtain ⟨e, he⟩ := MonoidalTransform.exists_ringEquiv_localization_of_comap_eq (maximalIdeal R) P hPM
    hMP t Q₁ hQ₁
  have hunit : ∀ y : P.primeCompl, IsUnit (φ y) := fun y =>
    isUnit_iff_ne_zero.mpr fun h0 => y.2 (RingHom.mem_ker.mpr h0)
  let ψ : Localization.AtPrime P →+* F := IsLocalization.lift (M := P.primeCompl) hunit
  have hψ : ∀ r, ψ (algebraMap R _ r) = φ r := IsLocalization.lift_eq hunit
  have hker : RingHom.ker ψ = maximalIdeal (Localization.AtPrime P) := by
    refine le_antisymm ?_ ?_
    · refine le_maximalIdeal fun htop => ?_
      have h1 : (1 : Localization.AtPrime P) ∈ RingHom.ker ψ := htop ▸ Submodule.mem_top
      simp [RingHom.mem_ker] at h1
    · rw [← Localization.AtPrime.map_eq_maximalIdeal, Ideal.map_le_iff_le_comap]
      intro p hp
      rw [Ideal.mem_comap, RingHom.mem_ker, hψ]
      exact RingHom.mem_ker.mp hp
  refine ⟨ψ.comp (e.symm.toRingHom.comp (algebraMap t.ring (Localization.AtPrime Q₁))), ?_, ?_⟩
  · ext y
    rw [RingHom.mem_ker]
    show ψ (e.symm (algebraMap t.ring _ y)) = 0 ↔ y ∈ Q₁
    rw [← RingHom.mem_ker, hker, ← IsLocalization.AtPrime.to_map_mem_maximal_iff
      (Localization.AtPrime Q₁) Q₁ y]
    simp only [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    exact not_congr (MulEquiv.isUnit_map e.symm.toMulEquiv)
  · intro r
    show ψ (e.symm (algebraMap t.ring _ (t.toRing r))) = φ r
    rw [← he r, e.symm_apply_apply, hψ]

/-- Corollary 3 (c), p. 244: for EVERY monoidal transform `R₁` of `R` with center `M` and every prime
`Q₁` of `R₁` with `Q₁ ∩ R = Q` (`Q = ker φ`, `R/Q` not regular), `R₁/Q₁` again satisfies the invariant of
the measure and the measure strictly increases.  (Residual algebraicity of `R₁` is not needed here.)
Notation: `φ : R → F` has kernel `Q`, `W ⊆ F` is the integral closure of `S₀ = R/Q`.
1. `R_Q = (R₁)_{Q₁}` and `φ` extends to `φ' : R₁ → F` with kernel `Q₁`
   (`exists_ringHom_ker_eq_of_comap_eq`).
2. (gap filled) for `m ∈ M` and `y ∈ R₁` with `x y = m` (`(x)R₁ = MR₁`): with a general element `x_g`
   of `M` (`φ(M)W = φ(x_g)W`), `φ(x)/φ(x_g)` is integral over `R`, and `u = x_g/x ∈ R₁` has inverse
   in `φ'(R₁)` (an integral element whose inverse lies in a ring lies in it,
   `exists_eq_of_isIntegral_of_mul_eq_one`); hence `φ'(b y) ∈ W` for a suitable unit `b` of `R₁`
   with `φ'(b) ∈ W`.  So `φ'(R₁)` is again a localization of `φ'(R₁) ∩ W`.
3. The `S₀`-submodule `φ(R) ∩ W` of the finite module `W` is contained in `φ'(R₁) ∩ W`, and the
   inclusion is strict: otherwise `M ⊆ x_g R + Q`, and `R/Q` would be a discrete valuation ring. -/
theorem exists_ringHom_curveImage_lt_of_comap_eq [Module.Finite S₀ W] [IsDedekindDomain W]
    (hWfin : {n : Ideal W | n.IsMaximal}.Finite) (hS₀ : ∀ n : ℕ, n ≠ 0 → IsUnit (n : S₀))
    {R : Type u} [CommRing R] [IsRegularLocalRing R] [IsDomain R] (φ : R →+* F)
    (hφS : ∀ s, algebraMap S₀ F s ∈ φ.range)
    (hInv : ∀ r, ∃ b, b ∉ maximalIdeal R ∧ φ b ∈ W ∧ φ (b * r) ∈ W)
    (hS : ¬ IsRegularLocalRing (R ⧸ RingHom.ker φ))
    (t : MonoidalTransform R (maximalIdeal R)) (Q₁ : Ideal t.ring) [Q₁.IsPrime]
    (hQ₁ : Q₁.comap t.toRing = RingHom.ker φ) :
    ∃ φ' : t.ring →+* F, RingHom.ker φ' = Q₁ ∧ (∀ r, φ' (t.toRing r) = φ r) ∧ t.x ∉ RingHom.ker φ ∧
      (∀ y, ∃ b, b ∉ maximalIdeal t.ring ∧ φ' b ∈ W ∧ φ' (b * y) ∈ W) ∧
      ∃ hφ'S : ∀ s, algebraMap S₀ F s ∈ φ'.range,
        curveImage W φ hφS < curveImage W φ' hφ'S := by
  classical
  set P := RingHom.ker φ with hPdef
  have hPM : P ≤ (maximalIdeal R) := le_maximalIdeal (Ideal.IsPrime.ne_top inferInstance)
  have hMP : (maximalIdeal R) ≠ P := by
    intro h
    apply hS
    have : P.IsMaximal := h ▸ maximalIdeal.isMaximal R
    let _ := Ideal.Quotient.field P
    infer_instance
  have hunitR : ∀ b, b ∉ (maximalIdeal R) → IsUnit b := fun b hb => by
    by_contra h
    exact hb ((IsLocalRing.mem_maximalIdeal b).mpr h)
  have hunitT : ∀ b : t.ring, b ∉ maximalIdeal t.ring → IsUnit b := fun b hb => by
    by_contra h
    exact hb ((IsLocalRing.mem_maximalIdeal b).mpr h)
  -- `x ∉ Q` (as `Q₁ ∩ R = Q ≠ (maximalIdeal R)`)
  have hxP : t.x ∉ P := by
    intro hx
    apply hMP
    refine le_antisymm (fun p hp => ?_) hPM
    rw [← hQ₁, Ideal.mem_comap]
    have hp' : t.toRing p ∈ (maximalIdeal R).map t.toRing := Ideal.mem_map_of_mem _ hp
    rw [← t.span_xR_eq_map, Ideal.mem_span_singleton'] at hp'
    obtain ⟨c, hc⟩ := hp'
    rw [← hc]
    refine Ideal.mul_mem_left _ _ ?_
    show t.toRing t.x ∈ Q₁
    rw [← Ideal.mem_comap, hQ₁]
    exact hx
  have hx0 : φ t.x ≠ 0 := fun h => hxP (RingHom.mem_ker.mpr h)
  obtain ⟨φ', hker', hφ'⟩ := exists_ringHom_ker_eq_of_comap_eq φ hS t Q₁ hQ₁
  have hQ₁max : Q₁ ≤ maximalIdeal t.ring := le_maximalIdeal (Ideal.IsPrime.ne_top inferInstance)
  have hφ'comp : φ'.comp t.toRing = φ := RingHom.ext hφ'
  -- a general element `x_g` of `(maximalIdeal R)`
  obtain ⟨xg, hxgM, hxg0, hdiv⟩ := exists_generalElement_of_not_isRegularLocalRing_quotient W hWfin hS₀
    φ hφS hInv hS
  have hxgP : xg ∉ P := fun h => hxg0 (RingHom.mem_ker.mp h)
  -- `x_g = u x` with `u ∈ R₁`
  obtain ⟨u, hu⟩ : ∃ u : t.ring, u * t.toRing t.x = t.toRing xg := by
    have : t.toRing xg ∈ (maximalIdeal R).map t.toRing := Ideal.mem_map_of_mem _ hxgM
    rw [← t.span_xR_eq_map, Ideal.mem_span_singleton'] at this
    exact this
  have hφ'u : φ' u * φ t.x = φ xg := by
    rw [← hφ' t.x, ← map_mul, hu, hφ']
  -- `w' = φ(x)/φ(x_g)` lies in `φ'(R₁)`, with `φ'(v) = w'` and `v ∉ M₁`
  have hw' : ∃ v : t.ring, v ∉ maximalIdeal t.ring ∧ φ' v = φ t.x / φ xg := by
    obtain ⟨b1, hb1, hb1W, hb1x⟩ := hInv t.x
    obtain ⟨w1, hw1⟩ := hdiv (b1 * t.x) (Ideal.mul_mem_left _ _ t.x_mem) hb1x
    have hmem : φ t.x / φ xg ∈ curveLocalRing W φ := by
      refine ⟨b1, hb1, hb1W, ?_⟩
      have : φ b1 * (φ t.x / φ xg) = w1 := by
        rw [map_mul] at hw1
        field_simp
        linear_combination hw1
      rw [this]
      exact w1.2
    have _ : Algebra.IsIntegral S₀ W := Algebra.IsIntegral.of_finite S₀ W
    obtain ⟨p, hpm, hp⟩ := exists_monic_eval₂_eq_zero_of_mem_curveLocalRing W φ hφS hmem
    obtain ⟨v, hv⟩ := exists_eq_of_isIntegral_of_mul_eq_one t.toRing φ' _ p hpm
      (by rw [hφ'comp]; exact hp) u (by rw [← mul_div_assoc, hφ'u, div_self hxg0])
    refine ⟨v, fun hvM => ?_, hv⟩
    have h1 : u * v - 1 ∈ Q₁ := by
      rw [← hker', RingHom.mem_ker, map_sub, map_mul, hv, map_one]
      rw [← mul_div_assoc, hφ'u, div_self hxg0, sub_self]
    have h2 : u * v ∈ maximalIdeal t.ring := Ideal.mul_mem_left _ _ hvM
    have h3 : (1 : t.ring) ∈ maximalIdeal t.ring := by
      have := sub_mem h2 (hQ₁max h1)
      rwa [sub_sub_cancel] at this
    exact (maximalIdeal.isMaximal t.ring).ne_top ((Ideal.eq_top_iff_one _).mpr h3)
  -- the generators `m / x`
  have hgen : ∀ m ∈ (maximalIdeal R), ∀ y : t.ring, t.toRing t.x * y = t.toRing m →
      ∃ b : t.ring, b ∉ maximalIdeal t.ring ∧ φ' b ∈ W ∧ φ' (b * y) ∈ W ∧
        ∃ b0 : R, b0 ∉ (maximalIdeal R) ∧ ∃ w2 : W, φ (b0 * m) = φ xg * w2 ∧ φ' (b * y) = w2 := by
    intro m hm y hy
    obtain ⟨v, hvM, hv⟩ := hw'
    obtain ⟨b0, hb0, hb0W, hb0m⟩ := hInv m
    obtain ⟨b1, hb1, hb1W, hb1x⟩ := hInv t.x
    obtain ⟨w1, hw1⟩ := hdiv (b1 * t.x) (Ideal.mul_mem_left _ _ t.x_mem) hb1x
    have hb01m : φ (b1 * (b0 * m)) ∈ W := by rw [map_mul]; exact mul_mem hb1W hb0m
    obtain ⟨w2, hw2⟩ := hdiv (b1 * (b0 * m)) (Ideal.mul_mem_left _ _ (Ideal.mul_mem_left _ _ hm)) hb01m
    have hφy : φ t.x * φ' y = φ m := by rw [← hφ', ← hφ', ← map_mul, hy]
    have hb01 : b0 * b1 ∉ (maximalIdeal R) := fun h => by
      rcases (inferInstance : (maximalIdeal R).IsPrime).mem_or_mem h with h | h
      exacts [hb0 h, hb1 h]
    have hφb : φ' (v * t.toRing (b0 * b1)) ∈ W := by
      rw [map_mul, hv, hφ']
      have : φ t.x / φ xg * φ (b0 * b1) = φ b0 * w1 := by
        rw [map_mul] at hw1 ⊢
        have : φ t.x * φ b1 = φ xg * w1 := by rw [mul_comm]; exact hw1
        field_simp
        linear_combination φ b0 * this
      rw [this]
      exact mul_mem hb0W w1.2
    have hval : φ' (v * t.toRing (b0 * b1) * y) = w2 := by
      rw [map_mul, map_mul, hv, hφ', div_mul_eq_mul_div, div_mul_eq_mul_div, div_eq_iff hxg0]
      have e1 : φ b1 * (φ b0 * φ m) = φ xg * w2 := by rw [← map_mul, ← map_mul]; exact hw2
      rw [map_mul]
      linear_combination (φ b0 * φ b1) * hφy + e1
    refine ⟨v * t.toRing (b0 * b1), ?_, hφb, by rw [hval]; exact w2.2, b1 * b0, fun h => ?_, w2, ?_, hval⟩
    · exact fun hmem => (IsLocalRing.mem_maximalIdeal _).mp hmem
        ((hunitT v hvM).mul ((hunitR _ hb01).map _))
    · rcases (inferInstance : (maximalIdeal R).IsPrime).mem_or_mem h with h | h
      exacts [hb1 h, hb0 h]
    · rw [mul_assoc]; exact hw2
  have hxK : algebraMap R (FractionRing R) t.x ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective R _)).mpr t.x_ne_zero
  have hy_of_gen : ∀ (m : R) (hm : m ∈ (maximalIdeal R)), t.toRing t.x * algebraMap _ t.ring
      (⟨_, Algebra.subset_adjoin ⟨m, hm, rfl⟩⟩ : blowupAlgebra R (maximalIdeal R) t.x) = t.toRing m := by
    intro m hm
    have h1 : (⟨_, Algebra.subset_adjoin ⟨m, hm, rfl⟩⟩ : blowupAlgebra R (maximalIdeal R) t.x) *
        algebraMap R _ t.x = algebraMap R _ m := Subtype.ext (div_mul_cancel₀ _ hxK)
    have h2 := congrArg (algebraMap (blowupAlgebra R (maximalIdeal R) t.x) t.ring) h1
    rw [map_mul] at h2
    rw [mul_comm]
    exact h2
  -- `φ'(a) ∈ C` for `a ∈ R[(maximalIdeal R)/x]`
  set C := curveLocalRing W φ' with hCdef
  have hA : ∀ a : blowupAlgebra R (maximalIdeal R) t.x, φ' (algebraMap _ t.ring a) ∈ C := by
    rintro ⟨a, ha⟩
    induction ha using Algebra.adjoin_induction with
    | mem z hz =>
      obtain ⟨m, hm, rfl⟩ := hz
      obtain ⟨b, hb, hbW, hby, -⟩ := hgen m hm _ (hy_of_gen m hm)
      exact ⟨b, hb, hbW, by rw [← map_mul]; exact hby⟩
    | algebraMap r =>
      have e : (⟨algebraMap R (FractionRing R) r, Subalgebra.algebraMap_mem _ r⟩ :
          blowupAlgebra R (maximalIdeal R) t.x) = algebraMap R _ r := rfl
      obtain ⟨b0, hb0, hb0W, hb0r⟩ := hInv r
      refine ⟨t.toRing b0, fun h => ?_, by rw [hφ']; exact hb0W, ?_⟩
      · exact (IsLocalRing.mem_maximalIdeal _).mp h ((hunitR b0 hb0).map _)
      · rw [e]
        have : algebraMap (blowupAlgebra R (maximalIdeal R) t.x) t.ring (algebraMap R _ r) = t.toRing r := rfl
        rw [this, hφ', hφ', ← map_mul]
        exact hb0r
    | add y z hy hz ihy ihz =>
      have e : (⟨y + z, add_mem hy hz⟩ : blowupAlgebra R (maximalIdeal R) t.x) = ⟨y, hy⟩ + ⟨z, hz⟩ := rfl
      rw [e, map_add, map_add]
      exact add_mem ihy ihz
    | mul y z hy hz ihy ihz =>
      have e : (⟨y * z, mul_mem hy hz⟩ : blowupAlgebra R (maximalIdeal R) t.x) = ⟨y, hy⟩ * ⟨z, hz⟩ := rfl
      rw [e, map_mul, map_mul]
      exact mul_mem ihy ihz
  -- the invariant for `R₁`
  have hInv' : ∀ y : t.ring, ∃ b, b ∉ maximalIdeal t.ring ∧ φ' b ∈ W ∧ φ' (b * y) ∈ W := by
    intro y
    obtain ⟨a, c, rfl⟩ := IsLocalization.exists_mk'_eq t.M'.primeCompl y
    obtain ⟨ba, hba, hbaW, hbaa⟩ := hA a
    obtain ⟨bc, hbc, hbcW, hbcc⟩ := hA (c : blowupAlgebra R (maximalIdeal R) t.x)
    have hcu : IsUnit (algebraMap _ t.ring (c : blowupAlgebra R (maximalIdeal R) t.x)) :=
      IsLocalization.map_units t.ring c
    refine ⟨ba * bc * algebraMap _ t.ring (c : blowupAlgebra R (maximalIdeal R) t.x), fun hmem => ?_, ?_, ?_⟩
    · exact (IsLocalRing.mem_maximalIdeal _).mp hmem (((hunitT ba hba).mul (hunitT bc hbc)).mul hcu)
    · rw [map_mul, map_mul, mul_assoc]
      exact mul_mem hbaW hbcc
    · have hmk : IsLocalization.mk' t.ring a c * algebraMap _ t.ring (c : blowupAlgebra R (maximalIdeal R) t.x) =
          algebraMap _ t.ring a := IsLocalization.mk'_spec t.ring a c
      have : φ' (ba * bc * algebraMap _ t.ring (c : blowupAlgebra R (maximalIdeal R) t.x) *
          IsLocalization.mk' t.ring a c) = φ' bc * (φ' ba * φ' (algebraMap _ t.ring a)) := by
        rw [← hmk]
        simp only [map_mul]
        ring
      rw [this]
      exact mul_mem hbcW hbaa
  have hφ'S : ∀ s, algebraMap S₀ F s ∈ φ'.range := by
    intro s
    obtain ⟨r, hr⟩ := hφS s
    exact ⟨t.toRing r, (hφ' r).trans hr⟩
  refine ⟨φ', hker', hφ', hxP, hInv', hφ'S, lt_of_le_of_ne (fun v hv => ?_) (fun heq => hS ?_)⟩
  · obtain ⟨r, hr⟩ := hv
    exact ⟨t.toRing r, (hφ' r).trans hr⟩
  -- otherwise `(maximalIdeal R) ⊆ x_g R + Q`, and `R/Q` is a discrete valuation ring
  refine isRegularLocalRing_quotient_of_forall_sub_mem P hxgM hxgP fun m hm => ?_
  have hmx : t.toRing m ∈ Ideal.span {t.xR} := by
    rw [t.span_xR_eq_map]
    exact Ideal.mem_map_of_mem _ hm
  obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.mp hmx
  obtain ⟨b, -, -, -, b0, hb0, w2, hw2, hval⟩ := hgen m hm y (by rw [← hy, mul_comm]; rfl)
  have hmem : w2 ∈ curveImage W φ' hφ'S := ⟨b * y, hval⟩
  rw [← heq] at hmem
  obtain ⟨r, hr⟩ := hmem
  refine ⟨(((hunitR b0 hb0).unit⁻¹ : Rˣ) : R) * r, ?_⟩
  have hbmr : b0 * m - xg * r ∈ P := by
    rw [RingHom.mem_ker, map_sub, hw2, map_mul φ xg r, hr, sub_self]
  have hbb : (((hunitR b0 hb0).unit⁻¹ : Rˣ) : R) * b0 = 1 := (hunitR b0 hb0).val_inv_mul
  have := Ideal.mul_mem_left P (((hunitR b0 hb0).unit⁻¹ : Rˣ) : R) hbmr
  convert this using 1
  linear_combination (-m) * hbb

-- the induction quantifies over `[IsRegularLocalRing R]` and `[IsDomain R]`, as `CurveResolvable`
set_option linter.overlappingInstances false in
/-- The dimension-one case of Corollary 3 (c) (p. 244), following the printed proof: "Assume that
`dim(R/Q) = 1`. Let `R₁` be any monoidal transform of `R` with center `M` which is residually
algebraic (hence, separable algebraic) over `R`, and such that there exists a prime ideal `Q₁` in `R₁`
such that `Q₁ ∩ R = Q`. Let `J₁` be the strict transform of `J` in `R₁`, `x` an element of `M` such that
`MR₁ = (x)R₁`, and `h_j = x^{-ν_j} g_j` with `ν_j = ν_M(g_j)` for each `j`. Then we have `R_Q = (R₁)_{Q₁}`,
`JR_Q = J₁(R₁)_{Q₁}`, and `(g_j)R_Q = (h_j)(R₁)_{Q₁}` for each `j`. Therefore, in view of (b), the
assertion (c) remains equivalent if we replace `R`, `J`, `Q`, `M` and `(g₁, …, g_m)` by `R₁`, `J₁`,
`Q₁`, `M₁` and `(h₁, …, h_m)` respectively. Therefore, if `R₁/Q₁` is regular, then the proof is done. If
otherwise, we repeat the same process. As is easily seen, this process cannot be repeated infinitely
many times, because the integral closure of `R/Q` in its field of quotients is a finite
`R/Q`-module."

Formalization of the last sentence: the process is a well-founded induction on the `S₀`-submodule
`φ(R) ∩ W` of the noetherian `S₀`-module `W` (`W` the integral closure of `R/Q`).  For EVERY admissible
`R₁` and `Q₁` (not only for a constructed one) the submodule strictly increases and the invariant "`φ(R₁)`
is a localization of `φ(R₁) ∩ W`" is preserved (`exists_ringHom_curveImage_lt_of_comap_eq`); that an
admissible `R₁` exists is `exists_monoidalTransform_curveImage_lt` (gap filled).  The remaining steps
are those of the printed text: (a) `M` is a permissible center, (b) gives the properties (i), (ii) for
`R₁`, `Q₁`, `J₁`, `(h_j)`, and `grIdeal_localization_eq_span_initialForm_of_transform` descends the
conclusion along `R_Q = (R₁)_{Q₁}`. -/
theorem grIdeal_localization_eq_span_initialForm_of_curveImage_eq [Hironaka.Cited.CurveFiniteIntegralClosure.{u}] [Hironaka.Cited.IsRegularLocalRingLocalizationOfIsRegularLocalRing.{u}] [Hironaka.Cited.IsSeparableFieldExtensionIff.{u}] [Module.Finite S₀ W] [IsNoetherianRing S₀] [IsDedekindDomain W]
    (hWfin : {n : Ideal W | n.IsMaximal}.Finite) (hS₀ : ∀ n : ℕ, n ≠ 0 → IsUnit (n : S₀))
    (N : Submodule S₀ W) :
    ∀ {R : Type u} [CommRing R] [IsRegularLocalRing R] [IsDomain R] [CharZero (ResidueField R)]
      (φ : R →+* F) (hφS : ∀ s, algebraMap S₀ F s ∈ φ.range),
      (∀ r, ∃ b, b ∉ maximalIdeal R ∧ φ b ∈ W ∧ φ (b * r) ∈ W) →
      curveImage W φ hφS = N → ∀ (J : Ideal R), J ≤ RingHom.ker φ → ∀ {m : ℕ} (g : Fin m → R),
      (∀ j, g j ≠ 0) → IsLocallyAdaptedSystem R (RingHom.ker φ) J g →
      grIdeal ((RingHom.ker φ).map (algebraMap R (Localization.AtPrime (RingHom.ker φ))))
          (J.map (algebraMap R (Localization.AtPrime (RingHom.ker φ)))) =
        Ideal.span (Set.range fun j =>
          initialForm ((RingHom.ker φ).map (algebraMap R (Localization.AtPrime (RingHom.ker φ))))
            (algebraMap R (Localization.AtPrime (RingHom.ker φ)) (g j))) := by
  induction N using WellFoundedGT.induction with
  | _ N ih =>
  intro R _ _ _ _ φ hφS hInv hN J hJ m g hg0 hg
  by_cases hS : IsRegularLocalRing (R ⧸ RingHom.ker φ)
  · exact grIdeal_localization_eq_span_initialForm_of_regular _ J hJ g hg
  -- "Let `R₁` be any monoidal transform of `R` with center `M` which is residually algebraic over `R`,
  -- and such that there exists a prime ideal `Q₁` in `R₁` such that `Q₁ ∩ R = Q`": such `R₁` exists
  obtain ⟨t, φ₀, hP₀, -, halg, hreg, -⟩ :=
    exists_monoidalTransform_curveImage_lt W hWfin hS₀ φ hφS hInv hS
  -- and for ANY such `R₁` and `Q₁`: `R₁/Q₁` is again of the same kind and the measure strictly increases
  obtain ⟨φ', hker', -, hxP, hInv', hφ'S, hlt⟩ := exists_ringHom_curveImage_lt_of_comap_eq W hWfin hS₀ φ hφS
    hInv hS t (RingHom.ker φ₀) hP₀.symm
  have hP' : RingHom.ker φ = (RingHom.ker φ').comap t.toRing := by rw [hker']; exact hP₀
  have hbij := MonoidalTransform.localRingHom_bijective_of_x_notMem t (RingHom.ker φ) _ hP' hxP
  have _ : IsRegularLocalRing t.ring := hreg
  have _ : CharZero (ResidueField t.ring) :=
    (RingHom.charZero_iff (ResidueField.map t.toRing).injective).mp inferInstance
  -- residually algebraic, hence residually separable algebraic (characteristic zero)
  have hsep : RingHom.IsResiduallySeparableAlgebraic (R := R) (R' := t.ring) t.toRing := by
    let _ := (ResidueField.map t.toRing).toAlgebra
    have : Algebra.IsAlgebraic (ResidueField R) (ResidueField t.ring) := halg
    exact Algebra.IsAlgebraic.isSeparable_of_perfectField
  have hQM : RingHom.ker φ ≤ maximalIdeal R := le_maximalIdeal (Ideal.IsPrime.ne_top inferInstance)
  have hMQ : maximalIdeal R ≠ RingHom.ker φ := by
    intro h
    apply hS
    have : (RingHom.ker φ).IsMaximal := h ▸ maximalIdeal.isMaximal R
    let _ := Ideal.Quotient.field (RingHom.ker φ)
    infer_instance
  have _ : IsRegularLocalRing (R ⧸ maximalIdeal R) := by
    let _ : Field (R ⧸ maximalIdeal R) := Ideal.Quotient.field _
    infer_instance
  -- (a): `M` is a permissible center for `J`
  have hperm := isPermissibleCenter_of_isLocallyAdaptedSystem _ J hJ g hg (maximalIdeal R) hQM
  -- `ν_j = ν_M(g_j)` and `h_j = x^{-ν_j} g_j`
  have hν : ∀ j, (((Ideal.ordElem (maximalIdeal R) (g j)).toNat : ℕ) : ℕ∞) =
      Ideal.ordElem (maximalIdeal R) (g j) := fun j =>
    ENat.natCast_toNat ((Ideal.ordElem_eq_top_iff_eq_zero (maximalIdeal.isMaximal R).ne_top).not.mpr
      (hg0 j))
  have hex : ∀ j, ∃ hj : t.ring,
      t.toRing t.x ^ (Ideal.ordElem (maximalIdeal R) (g j)).toNat * hj = t.toRing (g j) := by
    intro j
    have hmem : g j ∈ maximalIdeal R ^ (Ideal.ordElem (maximalIdeal R) (g j)).toNat :=
      Ideal.mem_pow_of_ordElem (hν j).symm
    have : t.toRing (g j) ∈ Ideal.span {t.xR ^ (Ideal.ordElem (maximalIdeal R) (g j)).toNat} := by
      rw [← Ideal.span_singleton_pow, t.span_xR_eq_map, ← Ideal.map_pow]
      exact Ideal.mem_map_of_mem _ hmem
    obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.mp this
    exact ⟨a, by rw [mul_comm]; exact ha⟩
  choose h hh using hex
  -- (b): the transformed system has the properties (i), (ii) for `R₁`, `Q₁`, `J₁`
  obtain ⟨hg₁, -⟩ := isLocallyAdaptedSystem_strictTransform (RingHom.ker φ) J hJ g hg (maximalIdeal R)
    hperm hQM hMQ t hsep (RingHom.ker φ') hP'.symm t.x t.x_mem t.span_xR_eq_map.symm
    (fun j => (Ideal.ordElem (maximalIdeal R) (g j)).toNat) hν h hh
  -- `J₁ ⊆ Q₁`
  have hJ₁ : strictTransformIdeal t J ≤ RingHom.ker φ' := by
    rw [strictTransformIdeal, Ideal.span_le]
    rintro y ⟨x', hx', f', hf', ν', -, hy⟩
    have hx'Q : x' ∉ RingHom.ker φ' := by
      intro hx'mem
      apply hxP
      have hmem : t.toRing t.x ∈ (maximalIdeal R).map t.toRing := Ideal.mem_map_of_mem _ t.x_mem
      rw [← hx'] at hmem
      rw [hP']
      exact (Ideal.span_singleton_le_iff_mem _).mpr hx'mem hmem
    have hmem : x' ^ ν' * y ∈ RingHom.ker φ' := by
      rw [hy]
      have : f' ∈ (RingHom.ker φ').comap t.toRing := hP' ▸ hJ hf'
      exact this
    rcases (inferInstance : (RingHom.ker φ').IsPrime).mem_or_mem hmem with h' | h'
    · exact absurd ((inferInstance : (RingHom.ker φ').IsPrime).mem_of_pow_mem _ h') hx'Q
    · exact h'
  have hh0 : ∀ j, h j ≠ 0 := by
    intro j h0
    apply hg0 j
    apply t.toRing_injective
    rw [← hh j, h0, mul_zero, map_zero]
  have h₁ := ih _ (hN ▸ hlt) φ' hφ'S hInv' rfl (strictTransformIdeal t J) hJ₁ h hh0 hg₁
  exact grIdeal_localization_eq_span_initialForm_of_transform (RingHom.ker φ) J t (RingHom.ker φ') hP' hbij hxP g
    (fun j => (Ideal.ordElem (maximalIdeal R) (g j)).toNat) h hh h₁

/-- Wrapper of `grIdeal_localization_eq_span_initialForm_of_curveImage_eq` for a prime `Q` with `ker φ = Q`. -/
theorem grIdeal_localization_eq_span_initialForm_of_curve [Hironaka.Cited.CurveFiniteIntegralClosure.{u}] [Hironaka.Cited.IsRegularLocalRingLocalizationOfIsRegularLocalRing.{u}] [Hironaka.Cited.IsSeparableFieldExtensionIff.{u}] [Module.Finite S₀ W] [IsNoetherianRing S₀] [IsDedekindDomain W]
    (hWfin : {n : Ideal W | n.IsMaximal}.Finite) (hS₀ : ∀ n : ℕ, n ≠ 0 → IsUnit (n : S₀))
    {R : Type u} [CommRing R] [IsRegularLocalRing R] [IsDomain R] [CharZero (ResidueField R)]
    (φ : R →+* F) (hφS : ∀ s, algebraMap S₀ F s ∈ φ.range)
    (hInv : ∀ r, ∃ b, b ∉ maximalIdeal R ∧ φ b ∈ W ∧ φ (b * r) ∈ W)
    (Q : Ideal R) [Q.IsPrime] (hker : RingHom.ker φ = Q) (J : Ideal R) (hJ : J ≤ Q) {m : ℕ}
    (g : Fin m → R) (hg0 : ∀ j, g j ≠ 0) (hg : IsLocallyAdaptedSystem R Q J g) :
    grIdeal (Q.map (algebraMap R (Localization.AtPrime Q)))
        (J.map (algebraMap R (Localization.AtPrime Q))) =
      Ideal.span (Set.range fun j =>
        initialForm (Q.map (algebraMap R (Localization.AtPrime Q)))
          (algebraMap R (Localization.AtPrime Q) (g j))) := by
  subst hker
  exact grIdeal_localization_eq_span_initialForm_of_curveImage_eq W hWfin hS₀ _ φ hφS hInv rfl J hJ g hg0 hg

end Cor3cCurve

/-- A finite algebra over a local ring has only finitely many maximal ideals (they all contain
`M W`, and `W/MW` is artinian). -/
theorem finite_setOf_isMaximal {S₀ W : Type u} [CommRing S₀] [IsLocalRing S₀] [CommRing W]
    [Algebra S₀ W] [Module.Finite S₀ W] : {n : Ideal W | n.IsMaximal}.Finite := by
  set I := (maximalIdeal S₀).map (algebraMap S₀ W)
  have hart : IsArtinianRing (W ⧸ I) := by
    let _ : Field (S₀ ⧸ maximalIdeal S₀) := Ideal.Quotient.field _
    have : Module.Finite S₀ (W ⧸ I) :=
      Module.Finite.of_surjective (Ideal.Quotient.mkₐ S₀ I).toLinearMap
        Ideal.Quotient.mk_surjective
    have : Module.Finite (S₀ ⧸ maximalIdeal S₀) (W ⧸ I) :=
      Module.Finite.of_restrictScalars_finite S₀ _ _
    exact IsArtinianRing.of_finite (S₀ ⧸ maximalIdeal S₀) (W ⧸ I)
  have hfin := IsArtinianRing.setOfPred_isMaximal_finite (W ⧸ I)
  refine (hfin.image (Ideal.comap (Ideal.Quotient.mk I))).subset ?_
  intro n hn
  have hn : n.IsMaximal := hn
  have hint : (algebraMap S₀ W).IsIntegral := fun x => Algebra.IsIntegral.isIntegral x
  have hIn : I ≤ n := by
    rw [Ideal.map_le_iff_le_comap]
    have := Ideal.isMaximal_comap_of_isIntegral_of_isMaximal _ hint n
    rw [IsLocalRing.eq_maximalIdeal this]
  have hcm : (n.map (Ideal.Quotient.mk I)).comap (Ideal.Quotient.mk I) = n := by
    rw [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective, ← RingHom.ker_eq_comap_bot,
      Ideal.mk_ker, sup_eq_left.mpr hIn]
  refine ⟨n.map (Ideal.Quotient.mk I), ?_, hcm⟩
  refine (Ideal.map_eq_top_or_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective hn).resolve_left
    fun htop => hn.ne_top ?_
  rw [← hcm, htop, Ideal.comap_top]

/-- The dimension-one case of Corollary 3 (c) (pp. 243–244: "Assume that `dim(R/Q) = 1`"),
under the finiteness condition of footnote 10 for `R/Q`, and for a system without zeros.
"`dim(R/Q) ≤ 1`" is `Ring.DimensionLEOne (R ⧸ Q)` (every non-zero prime of `R/Q` is maximal). -/
theorem grIdeal_localization_eq_span_initialForm_of_dimensionLEOne [Hironaka.Cited.CurveFiniteIntegralClosure.{u}] [Hironaka.Cited.IsRegularLocalRingLocalizationOfIsRegularLocalRing.{u}] [Hironaka.Cited.IsSeparableFieldExtensionIff.{u}] {R : Type u} [CommRing R] [IsRegularLocalRing R]
    [CharZero (ResidueField R)] (Q J : Ideal R) [Q.IsPrime] (hJQ : J ≤ Q) {m : ℕ}
    (g : Fin m → R) (hg0 : ∀ j, g j ≠ 0) (hg : IsLocallyAdaptedSystem R Q J g)
    (hdim : Ring.DimensionLEOne (R ⧸ Q))
    (hfin : Module.Finite (R ⧸ Q) (integralClosure (R ⧸ Q) (FractionRing (R ⧸ Q)))) :
    grIdeal (Q.map (algebraMap R (Localization.AtPrime Q)))
        (J.map (algebraMap R (Localization.AtPrime Q))) =
      Ideal.span (Set.range fun j =>
        initialForm (Q.map (algebraMap R (Localization.AtPrime Q)))
          (algebraMap R (Localization.AtPrime Q) (g j))) := by
  have _ : IsDomain R := Transforms.isDomain_of_isRegularLocalRing R
  have _ : IsLocalRing (R ⧸ Q) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk Q) Ideal.Quotient.mk_surjective
  set W := integralClosure (R ⧸ Q) (FractionRing (R ⧸ Q))
  have := hdim
  have : IsNoetherianRing W := IsNoetherianRing.of_finite (R ⧸ Q) W
  have : IsIntegrallyClosed W :=
    integralClosure.isIntegrallyClosedOfFiniteExtension (FractionRing (R ⧸ Q))
  have : IsDedekindDomain W := { }
  have hWfin : {n : Ideal W | n.IsMaximal}.Finite := finite_setOf_isMaximal (S₀ := R ⧸ Q)
  -- the non-zero integers are units (the residue field has characteristic zero)
  have hS₀ : ∀ n : ℕ, n ≠ 0 → IsUnit (n : R ⧸ Q) := by
    intro n hn
    have hres : IsLocalRing.residue R (n : R) ≠ 0 := by
      rw [map_natCast]
      exact Nat.cast_ne_zero.mpr hn
    have hu : IsUnit (n : R) := by
      by_contra h
      exact hres ((IsLocalRing.residue_eq_zero_iff _).mpr ((IsLocalRing.mem_maximalIdeal _).mpr h))
    simpa using hu.map (Ideal.Quotient.mk Q)
  let φ : R →+* FractionRing (R ⧸ Q) :=
    (algebraMap (R ⧸ Q) (FractionRing (R ⧸ Q))).comp (Ideal.Quotient.mk Q)
  have hφS : ∀ s, algebraMap (R ⧸ Q) (FractionRing (R ⧸ Q)) s ∈ φ.range := by
    intro s
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective s
    exact ⟨r, rfl⟩
  have hInv : ∀ r, ∃ b, b ∉ maximalIdeal R ∧ φ b ∈ W ∧ φ (b * r) ∈ W := fun r =>
    ⟨1, fun h => (maximalIdeal.isMaximal R).ne_top ((Ideal.eq_top_iff_one _).mpr h),
      W.algebraMap_mem _, W.algebraMap_mem _⟩
  have hker : RingHom.ker φ = Q := by
    rw [RingHom.ker_comp_of_injective _ (IsFractionRing.injective _ _), Ideal.mk_ker]
  exact grIdeal_localization_eq_span_initialForm_of_curve W hWfin hS₀ φ hφS hInv Q hker J hJQ g hg0 hg

/-- Orders are preserved by ring isomorphisms. -/
theorem Ideal.ordElem_map_of_bijective {A B : Type*} [CommRing A] [CommRing B] (α : A →+* B)
    (hα : Function.Bijective α) (I : Ideal A) (a : A) :
    Ideal.ordElem (I.map α) (α a) = Ideal.ordElem I a := by
  have hiff : ∀ n : ℕ, α a ∈ I.map α ^ n ↔ a ∈ I ^ n := by
    intro n
    rw [← Ideal.map_pow]
    refine ⟨fun ha => ?_, Ideal.mem_map_of_mem α⟩
    rw [← Ideal.comap_map_of_bijective α hα (I := I ^ n)]
    exact ha
  simp only [Ideal.ordElem, hiff]

/-- `ν_I(f) ≤ ν_{IB}(φ(f))` for a ring homomorphism `φ : A → B`. -/
theorem Ideal.ordElem_le_ordElem_map {A B : Type*} [CommRing A] [CommRing B] (φ : A →+* B)
    (I : Ideal A) (f : A) : Ideal.ordElem I f ≤ Ideal.ordElem (I.map φ) (φ f) :=
  Ideal.ordElem_le fun _ hν => Ideal.le_ordElem (by
    rw [← Ideal.map_pow]
    exact Ideal.mem_map_of_mem φ hν)

theorem Ideal.ord_span_singleton {A : Type*} [CommRing A] (I : Ideal A) (x : A) :
    Ideal.ord I (Ideal.span {x}) = Ideal.ordElem I x := by
  simp only [Ideal.ord, Ideal.ordElem, Ideal.span_singleton_le_iff_mem]

theorem initialForm_zero {A : Type*} [CommRing A] (I : Ideal A) :
    initialForm I (0 : A) = 0 := by
  rw [initialForm, dite_eq_left (Ideal.ordElem_eq_top_iff.mpr fun ν => zero_mem _)]

/-- Dropping the indices where `v` vanishes does not change the ideal generated by the
values of `v`. -/
theorem Ideal.span_range_eq_span_range_filter_of_forall_eq_zero {B : Type*} [CommSemiring B] {m : ℕ} (p : Fin m → Prop)
    [DecidablePred p] (v : Fin m → B) (hv : ∀ j, ¬ p j → v j = 0) :
    Ideal.span (Set.range v) = Ideal.span (Set.range fun i : Fin (Fintype.card {j // p j}) =>
      v ((Fintype.equivFin {j // p j}).symm i).1) := by
  refine le_antisymm (Ideal.span_le.mpr ?_) (Ideal.span_mono ?_)
  · rintro _ ⟨j, rfl⟩
    by_cases hj : p j
    · exact Ideal.subset_span ⟨Fintype.equivFin {j // p j} ⟨j, hj⟩, by simp⟩
    · rw [SetLike.mem_coe, hv j hj]
      exact zero_mem _
  · rintro _ ⟨i, rfl⟩
    exact ⟨_, rfl⟩

section Cor3cInduction

variable {R : Type u} [CommRing R] [IsRegularLocalRing R]

/-- Theorem 1 of §3 for `R`: `ν_{Q'R_{Q'}}(f) ≤ ν_M(f)`. -/
theorem Ideal.ordElem_localization_le_ordElem_maximalIdeal [Hironaka.Cited.CurveFiniteIntegralClosure.{u}] [Hironaka.Cited.IsRegularLocalRingLocalizationOfIsRegularLocalRing.{u}] (Q' : Ideal R) [Q'.IsPrime] (f : R) :
    Ideal.ordElem (Q'.map (algebraMap R (Localization.AtPrime Q')))
      (algebraMap R (Localization.AtPrime Q') f) ≤ Ideal.ordElem (maximalIdeal R) f := by
  have _ : IsDomain R := Transforms.isDomain_of_isRegularLocalRing R
  by_cases hf : f = 0
  · have h0 : Ideal.ordElem (maximalIdeal R) (0 : R) = ⊤ :=
      Ideal.ordElem_eq_top_iff.mpr fun ν => zero_mem _
    rw [hf, h0]
    exact le_top
  have h1 := nu_localization_le R (Ideal.span {f}) (by rwa [ne_eq, Ideal.span_singleton_eq_bot]) Q'
  simp only [Ideal.nu, Ideal.map_span, Set.image_singleton, Ideal.ord_span_singleton] at h1
  rwa [Localization.AtPrime.map_eq_maximalIdeal]

/-- Theorem 1 of §3 applied to `R_{Q'}` (regular by Serre's theorem, footnote 9): for primes
`Q ⊆ Q'`, `ν_{QR_Q}(f) ≤ ν_{Q'R_{Q'}}(f)`. -/
theorem Ideal.ordElem_localization_mono [Hironaka.Cited.CurveFiniteIntegralClosure.{u}] [Hironaka.Cited.IsRegularLocalRingLocalizationOfIsRegularLocalRing.{u}] (Q Q' : Ideal R) [Q.IsPrime] [Q'.IsPrime]
    (hQQ' : Q ≤ Q') (f : R) :
    Ideal.ordElem (Q.map (algebraMap R (Localization.AtPrime Q)))
        (algebraMap R (Localization.AtPrime Q) f) ≤
      Ideal.ordElem (Q'.map (algebraMap R (Localization.AtPrime Q')))
        (algebraMap R (Localization.AtPrime Q') f) := by
  classical
  have _ : IsDomain R := Transforms.isDomain_of_isRegularLocalRing R
  by_cases hf : f = 0
  · have h0 : Ideal.ordElem (Q'.map (algebraMap R (Localization.AtPrime Q')))
        (0 : Localization.AtPrime Q') = ⊤ := Ideal.ordElem_eq_top_iff.mpr fun ν => zero_mem _
    rw [hf, map_zero, map_zero, h0]
    exact le_top
  have _ : IsRegularLocalRing (Localization.AtPrime Q') :=
    isRegularLocalRing_localization_of_isRegularLocalRing R Q'
  have hdisj : Disjoint (Q'.primeCompl : Set R) (Q : Set R) :=
    Set.disjoint_left.mpr fun a ha haQ => ha (hQQ' haQ)
  have _ : (Q.map (algebraMap R (Localization.AtPrime Q'))).IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint Q'.primeCompl _ Q inferInstance hdisj
  have hpQ : (Q.map (algebraMap R (Localization.AtPrime Q'))).comap
      (algebraMap R (Localization.AtPrime Q')) = Q :=
    IsLocalization.under_map_of_isPrime_disjoint Q'.primeCompl _ inferInstance hdisj
  let p := Q.map (algebraMap R (Localization.AtPrime Q'))
  let g : R →+* Localization.AtPrime p :=
    (algebraMap (Localization.AtPrime Q') (Localization.AtPrime p)).comp
      (algebraMap R (Localization.AtPrime Q'))
  have hg : ∀ y : Q.primeCompl, IsUnit (g y) := by
    intro y
    refine (IsLocalization.AtPrime.isUnit_to_map_iff (Localization.AtPrime p) p _).mpr ?_
    intro hy
    have hy' : (y : R) ∈ p.comap (algebraMap R (Localization.AtPrime Q')) := hy
    exact y.2 (hpQ.le hy')
  let φ : Localization.AtPrime Q →+* Localization.AtPrime p :=
    IsLocalization.lift (M := Q.primeCompl) hg
  have hmap : (Q.map (algebraMap R (Localization.AtPrime Q))).map φ =
      maximalIdeal (Localization.AtPrime p) := by
    rw [Ideal.map_map, IsLocalization.lift_comp, ← Localization.AtPrime.map_eq_maximalIdeal,
      Ideal.map_map]
  have hx0 : algebraMap R (Localization.AtPrime Q') f ≠ 0 := by
    intro h
    apply hf
    exact IsLocalization.injective (Localization.AtPrime Q')
      (Ideal.primeCompl_le_nonZeroDivisors Q') (h.trans (map_zero _).symm)
  have h1 := nu_localization_le (Localization.AtPrime Q')
    (Ideal.span {algebraMap R (Localization.AtPrime Q') f})
    (by rwa [ne_eq, Ideal.span_singleton_eq_bot]) p
  simp only [Ideal.nu, Ideal.map_span, Set.image_singleton, Ideal.ord_span_singleton] at h1
  calc _ ≤ Ideal.ordElem ((Q.map (algebraMap R (Localization.AtPrime Q))).map φ)
        (φ (algebraMap R (Localization.AtPrime Q) f)) := Ideal.ordElem_le_ordElem_map φ _ _
    _ = Ideal.ordElem (maximalIdeal (Localization.AtPrime p))
        (algebraMap (Localization.AtPrime Q') (Localization.AtPrime p)
          (algebraMap R (Localization.AtPrime Q') f)) := by
      rw [hmap, IsLocalization.lift_eq]
      rfl
    _ ≤ Ideal.ordElem (maximalIdeal (Localization.AtPrime Q'))
        (algebraMap R (Localization.AtPrime Q') f) := h1
    _ = _ := by rw [Localization.AtPrime.map_eq_maximalIdeal]

omit [IsRegularLocalRing R] in
/-- `R_Q = (R_{Q'})_{QR_{Q'}}` for primes `Q ⊆ Q'`: the canonical map is bijective. -/
theorem _root_.Localization.localRingHom_bijective_of_eq_comap_map (Q Q' : Ideal R) [Q.IsPrime] [Q'.IsPrime]
    [(Q.map (algebraMap R (Localization.AtPrime Q'))).IsPrime]
    (hQ : Q = (Q.map (algebraMap R (Localization.AtPrime Q'))).comap
      (algebraMap R (Localization.AtPrime Q'))) :
    Function.Bijective (Localization.localRingHom Q (Q.map (algebraMap R
      (Localization.AtPrime Q'))) (algebraMap R (Localization.AtPrime Q')) hQ) := by
  set R' := Localization.AtPrime Q'
  set Q₁ := Q.map (algebraMap R R')
  set T := Localization.AtPrime Q₁
  have hT : IsLocalization Q.primeCompl T := by
    have h := IsLocalization.isLocalization_isLocalization_atPrime_isLocalization
      (M := Q'.primeCompl) (S := R') (T := T) Q₁
    have hsub : (Q₁.comap (algebraMap R R')).primeCompl = Q.primeCompl := by
      ext r
      show r ∉ Q₁.comap (algebraMap R R') ↔ r ∉ Q
      rw [← hQ]
    exact hsub ▸ h
  let e := IsLocalization.algEquiv Q.primeCompl (Localization.AtPrime Q) T
  have heq : Localization.localRingHom Q Q₁ (algebraMap R R') hQ = e.toRingHom := by
    refine IsLocalization.ringHom_ext Q.primeCompl (RingHom.ext fun r => ?_)
    simp only [RingHom.comp_apply, Localization.localRingHom_to_map]
    show _ = e (algebraMap R (Localization.AtPrime Q) r)
    rw [AlgEquiv.commutes, IsScalarTower.algebraMap_apply R R' T]
  rw [heq]
  exact e.bijective

omit [IsRegularLocalRing R] in
/-- If no prime lies strictly between `Q` and `Q'`, then `R_{Q'}/QR_{Q'}` has dimension `≤ 1`. -/
theorem dimensionLEOne_quotient_localization_of_forall_prime_eq_or_eq (Q Q' : Ideal R) [Q.IsPrime] [Q'.IsPrime]
    (hmin : ∀ P : Ideal R, P.IsPrime → Q ≤ P → P ≤ Q' → P = Q ∨ P = Q') :
    Ring.DimensionLEOne (Localization.AtPrime Q' ⧸ Q.map (algebraMap R
      (Localization.AtPrime Q'))) := by
  constructor
  intro pbar hp0 hpbar
  have := hpbar
  have hpP : (pbar.comap (Ideal.Quotient.mk (Q.map (algebraMap R
      (Localization.AtPrime Q'))))).IsPrime := Ideal.comap_isPrime _ _
  have hpmap' : (pbar.comap (Ideal.Quotient.mk (Q.map (algebraMap R
      (Localization.AtPrime Q'))))).map (Ideal.Quotient.mk (Q.map (algebraMap R
      (Localization.AtPrime Q')))) = pbar :=
    Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective pbar
  generalize hp : pbar.comap (Ideal.Quotient.mk (Q.map (algebraMap R
      (Localization.AtPrime Q')))) = p at hpP hpmap'
  have hQ₁p : Q.map (algebraMap R (Localization.AtPrime Q')) ≤ p := fun x hx => by
    rw [← hp]
    show Ideal.Quotient.mk _ x ∈ pbar
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr hx]
    exact zero_mem _
  have hP : (p.comap (algebraMap R (Localization.AtPrime Q'))).IsPrime := Ideal.comap_isPrime _ _
  have hQP : Q ≤ p.comap (algebraMap R (Localization.AtPrime Q')) :=
    fun x hx => hQ₁p (Ideal.mem_map_of_mem _ hx)
  have hPQ' : p.comap (algebraMap R (Localization.AtPrime Q')) ≤ Q' := by
    intro x hx
    by_contra hxQ'
    have hu : IsUnit (algebraMap R (Localization.AtPrime Q') x) :=
      IsLocalization.map_units (Localization.AtPrime Q') (⟨x, hxQ'⟩ : Q'.primeCompl)
    exact hpP.ne_top (Ideal.eq_top_of_isUnit_mem _ hx hu)
  have hpmap : (p.comap (algebraMap R (Localization.AtPrime Q'))).map
      (algebraMap R (Localization.AtPrime Q')) = p :=
    IsLocalization.map_under Q'.primeCompl (Localization.AtPrime Q') p
  rcases hmin _ hP hQP hPQ' with h | h
  · exfalso
    apply hp0
    rw [← hpmap', ← hpmap, h]
    exact Ideal.map_quotient_self _
  · have hpmax : p.IsMaximal := by
      rw [← hpmap, h, Localization.AtPrime.map_eq_maximalIdeal]
      exact maximalIdeal.isMaximal _
    rw [← hpmap']
    refine (Ideal.map_eq_top_or_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective
      hpmax).resolve_left fun htop => ?_
    rw [hpmap'] at htop
    exact hpbar.ne_top htop

/-- A prime `Q ≠ M` of `R` is contained in a prime `Q' ⊋ Q` with no prime strictly between
(take `Q'` of minimal height among the primes strictly containing `Q`). -/
theorem exists_isPrime_lt_forall_eq_or_eq_of_ne_maximalIdeal (Q : Ideal R) [Q.IsPrime] (hQ : Q ≠ maximalIdeal R) :
    ∃ Q' : Ideal R, Q'.IsPrime ∧ Q < Q' ∧
      ∀ P : Ideal R, P.IsPrime → Q ≤ P → P ≤ Q' → P = Q ∨ P = Q' := by
  classical
  set S := {P : Ideal R | P.IsPrime ∧ Q < P}
  have hne : S.Nonempty := ⟨maximalIdeal R, (maximalIdeal.isMaximal R).isPrime,
    lt_of_le_of_ne (le_maximalIdeal Ideal.IsPrime.ne_top') hQ⟩
  obtain ⟨Q', ⟨hQ'p, hQQ'⟩, hmin⟩ :=
    (InvImage.wf (fun P : Ideal R => P.height) wellFounded_lt).has_min S hne
  refine ⟨Q', hQ'p, hQQ', fun P hP hQP hPQ' => ?_⟩
  by_cases h1 : P = Q
  · exact Or.inl h1
  by_cases h2 : P = Q'
  · exact Or.inr h2
  exfalso
  have := hP
  have hlt : P < Q' := lt_of_le_of_ne hPQ' h2
  exact hmin P ⟨hP, lt_of_le_of_ne hQP (Ne.symm h1)⟩ (Ideal.height_strict_mono_of_isPrime hlt)

/-- The passage from `(R, Q')` to `(R, Q)` for primes `Q ⊆ Q'` with `dim(R_{Q'}/QR_{Q'}) ≤ 1`
(p. 243: "by an obvious induction on the dimension of `R/Q`, the proof of (c) can be reduced to
the case in which `dim(R/Q) = 1`"): the conclusion for `Q'` is (i) for the regular local ring
`R_{Q'}`, and the dimension-one case applies to `R_{Q'}` and `QR_{Q'}`, as
`(R_{Q'})_{QR_{Q'}} = R_Q`. -/
theorem grIdeal_localization_eq_span_initialForm_of_le_localization [Hironaka.Cited.CurveFiniteIntegralClosure.{u}] [Hironaka.Cited.IsRegularLocalRingLocalizationOfIsRegularLocalRing.{u}] [Hironaka.Cited.IsSeparableFieldExtensionIff.{u}] [CharZero (ResidueField R)] (Q Q' J : Ideal R) [Q.IsPrime]
    [Q'.IsPrime] (hQQ' : Q ≤ Q') (hJQ : J ≤ Q) {m : ℕ} (g : Fin m → R) (hg0 : ∀ j, g j ≠ 0)
    (hg : IsLocallyAdaptedSystem R Q J g)
    (hA : grIdeal (Q'.map (algebraMap R (Localization.AtPrime Q')))
        (J.map (algebraMap R (Localization.AtPrime Q'))) =
      Ideal.span (Set.range fun j =>
        initialForm (Q'.map (algebraMap R (Localization.AtPrime Q')))
          (algebraMap R (Localization.AtPrime Q') (g j))))
    (hB : ∀ j, Ideal.ordElem (Q'.map (algebraMap R (Localization.AtPrime Q')))
        (algebraMap R (Localization.AtPrime Q') (g j)) =
      Ideal.ordElem (Q.map (algebraMap R (Localization.AtPrime Q)))
        (algebraMap R (Localization.AtPrime Q) (g j)))
    (hdim : Ring.DimensionLEOne (Localization.AtPrime Q' ⧸
      Q.map (algebraMap R (Localization.AtPrime Q'))))
    (hfin : Module.Finite (Localization.AtPrime Q' ⧸ Q.map (algebraMap R (Localization.AtPrime Q')))
      (integralClosure (Localization.AtPrime Q' ⧸ Q.map (algebraMap R (Localization.AtPrime Q')))
        (FractionRing (Localization.AtPrime Q' ⧸
          Q.map (algebraMap R (Localization.AtPrime Q')))))) :
    grIdeal (Q.map (algebraMap R (Localization.AtPrime Q)))
        (J.map (algebraMap R (Localization.AtPrime Q))) =
      Ideal.span (Set.range fun j =>
        initialForm (Q.map (algebraMap R (Localization.AtPrime Q)))
          (algebraMap R (Localization.AtPrime Q) (g j))) := by
  classical
  have _ : IsDomain R := Transforms.isDomain_of_isRegularLocalRing R
  have _ : IsRegularLocalRing (Localization.AtPrime Q') :=
    isRegularLocalRing_localization_of_isRegularLocalRing R Q'
  have hdisj : Disjoint (Q'.primeCompl : Set R) (Q : Set R) :=
    Set.disjoint_left.mpr fun a ha haQ => ha (hQQ' haQ)
  have _ : (Q.map (algebraMap R (Localization.AtPrime Q'))).IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint Q'.primeCompl _ Q inferInstance hdisj
  have hQ : Q = (Q.map (algebraMap R (Localization.AtPrime Q'))).comap
      (algebraMap R (Localization.AtPrime Q')) :=
    (IsLocalization.under_map_of_isPrime_disjoint Q'.primeCompl _ inferInstance hdisj).symm
  -- the residue field of `R_{Q'}` has characteristic zero (`ℚ ⊆ R`)
  have _ : CharZero (ResidueField (Localization.AtPrime Q')) := by
    refine charZero_of_inj_zero fun n hn => ?_
    by_contra hn0
    have hres : residue R (n : R) ≠ 0 := by
      rw [map_natCast]
      exact Nat.cast_ne_zero.mpr hn0
    have hu : IsUnit (n : R) := by
      by_contra h
      exact hres ((residue_eq_zero_iff _).mpr ((mem_maximalIdeal _).mpr h))
    have hu' := (hu.map (algebraMap R (Localization.AtPrime Q'))).map
      (residue (Localization.AtPrime Q'))
    rw [map_natCast, map_natCast, hn] at hu'
    exact not_isUnit_zero hu'
  set ψ := Localization.localRingHom Q (Q.map (algebraMap R (Localization.AtPrime Q')))
    (algebraMap R (Localization.AtPrime Q')) hQ
  have hψ : Function.Bijective ψ := Localization.localRingHom_bijective_of_eq_comap_map Q Q' hQ
  have hψ_map : ∀ r, ψ (algebraMap R (Localization.AtPrime Q) r) =
      algebraMap (Localization.AtPrime Q') (Localization.AtPrime
        (Q.map (algebraMap R (Localization.AtPrime Q')))) (algebraMap R _ r) :=
    Localization.localRingHom_to_map _ _ _ hQ
  have hψmax : (Q.map (algebraMap R (Localization.AtPrime Q))).map ψ =
      (Q.map (algebraMap R (Localization.AtPrime Q'))).map (algebraMap
        (Localization.AtPrime Q') (Localization.AtPrime
          (Q.map (algebraMap R (Localization.AtPrime Q'))))) := by
    rw [Localization.AtPrime.map_eq_maximalIdeal, Localization.AtPrime.map_eq_maximalIdeal]
    exact map_maximalIdeal_of_surjective ψ hψ.2
  -- (i) and (ii) for `R_{Q'}`, `QR_{Q'}`, `JR_{Q'}` and the images of the `g_j`
  have hg' : IsLocallyAdaptedSystem (Localization.AtPrime Q')
      (Q.map (algebraMap R (Localization.AtPrime Q')))
      (J.map (algebraMap R (Localization.AtPrime Q')))
      (fun j => algebraMap R (Localization.AtPrime Q') (g j)) := by
    refine ⟨fun j => Ideal.mem_map_of_mem _ (hg.1 j), ?_, fun j => ?_⟩
    · have h := hA
      rwa [Localization.AtPrime.map_eq_maximalIdeal] at h
    · have h1 := Ideal.ordElem_map_of_bijective ψ hψ (Q.map (algebraMap R
        (Localization.AtPrime Q))) (algebraMap R (Localization.AtPrime Q) (g j))
      rw [hψmax, hψ_map] at h1
      rw [← Localization.AtPrime.map_eq_maximalIdeal, hB j, h1]
  have hg0' : ∀ j, algebraMap R (Localization.AtPrime Q') (g j) ≠ 0 := fun j h =>
    hg0 j (IsLocalization.injective (Localization.AtPrime Q')
      (Ideal.primeCompl_le_nonZeroDivisors Q') (h.trans (map_zero _).symm))
  have key := grIdeal_localization_eq_span_initialForm_of_dimensionLEOne (Q.map (algebraMap R (Localization.AtPrime Q')))
    (J.map (algebraMap R (Localization.AtPrime Q'))) (Ideal.map_mono hJQ) _ hg0' hg' hdim hfin
  -- transport back along `ψ⁻¹ : (R_{Q'})_{QR_{Q'}} → R_Q`
  let e := RingEquiv.ofBijective ψ hψ
  let α := e.symm.toRingHom
  have hα : Function.Bijective α := e.symm.bijective
  have hαmap : ∀ r, α (algebraMap (Localization.AtPrime Q') (Localization.AtPrime
      (Q.map (algebraMap R (Localization.AtPrime Q')))) (algebraMap R _ r)) =
      algebraMap R (Localization.AtPrime Q) r := by
    intro r
    rw [← hψ_map]
    exact e.symm_apply_apply _
  have h2 := grIdeal_map_eq_span_initialForm_of_bijective α hα _ _ _ key
  have hmax : ((Q.map (algebraMap R (Localization.AtPrime Q'))).map (algebraMap
      (Localization.AtPrime Q') (Localization.AtPrime
        (Q.map (algebraMap R (Localization.AtPrime Q')))))).map α =
      Q.map (algebraMap R (Localization.AtPrime Q)) := by
    rw [Localization.AtPrime.map_eq_maximalIdeal, Localization.AtPrime.map_eq_maximalIdeal]
    exact map_maximalIdeal_of_surjective α hα.2
  have hJmap : ((J.map (algebraMap R (Localization.AtPrime Q'))).map (algebraMap
      (Localization.AtPrime Q') (Localization.AtPrime
        (Q.map (algebraMap R (Localization.AtPrime Q')))))).map α =
      J.map (algebraMap R (Localization.AtPrime Q)) := by
    rw [Ideal.map_map, Ideal.map_map]
    congr 1
    exact RingHom.ext hαmap
  rw [hmax, hJmap] at h2
  simp only [hαmap] at h2
  exact h2

/-- The dimension of `R/Q` is a natural number: `dim R/Q ≤ dim R = n` (`R` regular local). -/
theorem exists_ringKrullDim_quotient_eq_natCast (Q : Ideal R) [Q.IsPrime] :
    ∃ d : ℕ, ringKrullDim (R ⧸ Q) = d := by
  have h1 := StrictDim.coheight_eq_ringKrullDim_quotient (⟨Q, inferInstance⟩ : PrimeSpectrum R)
  have hn := IsRegularLocalRing.spanFinrank_maximalIdeal (R := R)
  have h2 : ringKrullDim (R ⧸ Q) ≤ ((maximalIdeal R).spanFinrank : WithBot ℕ∞) := by
    rw [hn]
    exact ringKrullDim_quotient_le Q
  rw [← h1] at h2
  have h3 : Order.coheight (⟨Q, inferInstance⟩ : PrimeSpectrum R) ≤
      ((maximalIdeal R).spanFinrank : ℕ∞) := by
    exact_mod_cast h2
  obtain ⟨d, hd⟩ := ENat.ne_top_iff_exists.mp
    (ne_top_of_le_ne_top (ENat.natCast_ne_top _) h3)
  refine ⟨d, ?_⟩
  rw [← h1, ← hd]
  rfl

/-- For primes `Q ⊊ Q'` of `R`, `dim R/Q' < dim R/Q`. -/
theorem ringKrullDim_quotient_lt_of_lt {Q Q' : Ideal R} [Q.IsPrime] [Q'.IsPrime] (h : Q < Q') :
    ringKrullDim (R ⧸ Q') < ringKrullDim (R ⧸ Q) := by
  obtain ⟨d', hd'⟩ := exists_ringKrullDim_quotient_eq_natCast Q'
  have h1 := StrictDim.coheight_eq_ringKrullDim_quotient (⟨Q, inferInstance⟩ : PrimeSpectrum R)
  have h1' := StrictDim.coheight_eq_ringKrullDim_quotient (⟨Q', inferInstance⟩ : PrimeSpectrum R)
  have hfin : Order.coheight (⟨Q', inferInstance⟩ : PrimeSpectrum R) < ⊤ := by
    have : (Order.coheight (⟨Q', inferInstance⟩ : PrimeSpectrum R) : WithBot ℕ∞) = (d' : ℕ) := by
      rw [h1', hd']
    have h4 : Order.coheight (⟨Q', inferInstance⟩ : PrimeSpectrum R) = (d' : ℕ∞) := by
      exact_mod_cast this
    rw [h4]
    exact ENat.natCast_lt_top _
  have := Order.coheight_strictAnti (show (⟨Q, inferInstance⟩ : PrimeSpectrum R) <
    ⟨Q', inferInstance⟩ from h) hfin
  rw [← h1, ← h1']
  exact_mod_cast this

/-- The induction of p. 243 on the dimension of `R/Q` ("by an obvious induction on the dimension of
`R/Q`, the proof of (c) can be reduced to the case in which `dim(R/Q) = 1`"), for a system without zeros:
the statement for `Q` with `dim R/Q = d` follows from that for the primes `Q' ⊋ Q` (which have
`dim R/Q' < d`) by the dimension-`≤ 1` case applied to `R_{Q'}` and `QR_{Q'}`. -/
theorem forall_grIdeal_localization_eq_span_initialForm_of_finite [Hironaka.Cited.CurveFiniteIntegralClosure.{u}] [Hironaka.Cited.IsRegularLocalRingLocalizationOfIsRegularLocalRing.{u}] [Hironaka.Cited.IsSeparableFieldExtensionIff.{u}] [CharZero (ResidueField R)]
    (hfin : ∀ (Q' Q'' : Ideal R) [Q'.IsPrime] [Q''.IsPrime], Q'' ≤ Q' →
      Module.Finite (Localization.AtPrime Q' ⧸ Q''.map (algebraMap R (Localization.AtPrime Q')))
        (integralClosure (Localization.AtPrime Q' ⧸
          Q''.map (algebraMap R (Localization.AtPrime Q')))
          (FractionRing (Localization.AtPrime Q' ⧸
            Q''.map (algebraMap R (Localization.AtPrime Q'))))))
    (J : Ideal R) {m : ℕ} (g : Fin m → R) (hg0 : ∀ j, g j ≠ 0) (Q : Ideal R) :
    ∀ _ : Q.IsPrime, J ≤ Q → IsLocallyAdaptedSystem R Q J g →
      grIdeal (Q.map (algebraMap R (Localization.AtPrime Q)))
          (J.map (algebraMap R (Localization.AtPrime Q))) =
        Ideal.span (Set.range fun j =>
          initialForm (Q.map (algebraMap R (Localization.AtPrime Q)))
            (algebraMap R (Localization.AtPrime Q) (g j))) := by
  -- induction on the dimension `d` of `R/Q`
  suffices H : ∀ d : ℕ, ∀ (Q : Ideal R) [Q.IsPrime], ringKrullDim (R ⧸ Q) = d → J ≤ Q →
      IsLocallyAdaptedSystem R Q J g →
      grIdeal (Q.map (algebraMap R (Localization.AtPrime Q)))
          (J.map (algebraMap R (Localization.AtPrime Q))) =
        Ideal.span (Set.range fun j =>
          initialForm (Q.map (algebraMap R (Localization.AtPrime Q)))
            (algebraMap R (Localization.AtPrime Q) (g j))) by
    intro hQ hJQ hg
    obtain ⟨d, hd⟩ := exists_ringKrullDim_quotient_eq_natCast Q
    exact H d Q hd hJQ hg
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
  intro Q _ hdQ hJQ hg
  by_cases hreg : IsRegularLocalRing (R ⧸ Q)
  · exact grIdeal_localization_eq_span_initialForm_of_regular Q J hJQ g hg
  have hQM : Q ≠ maximalIdeal R := by
    intro h
    apply hreg
    rw [h]
    let _ : Field (R ⧸ maximalIdeal R) := Ideal.Quotient.field _
    infer_instance
  obtain ⟨Q', hQ'p, hQQ', hmin⟩ := exists_isPrime_lt_forall_eq_or_eq_of_ne_maximalIdeal Q hQM
  -- (ii) for `Q'`: `ν_M(g_j) ≥ ν_{Q'R_{Q'}}(g_j) ≥ ν_{QR_Q}(g_j) = ν_M(g_j)` (Theorem 1, §3)
  have hB : ∀ j, Ideal.ordElem (Q'.map (algebraMap R (Localization.AtPrime Q')))
      (algebraMap R (Localization.AtPrime Q') (g j)) =
      Ideal.ordElem (Q.map (algebraMap R (Localization.AtPrime Q)))
        (algebraMap R (Localization.AtPrime Q) (g j)) := fun j =>
    le_antisymm ((Ideal.ordElem_localization_le_ordElem_maximalIdeal Q' (g j)).trans (hg.2.2 j).le)
      (Ideal.ordElem_localization_mono Q Q' hQQ'.le (g j))
  have hg' : IsLocallyAdaptedSystem R Q' J g := ⟨hg.1, hg.2.1, fun j => (hg.2.2 j).trans (hB j).symm⟩
  -- the induction hypothesis for `Q'`, `dim R/Q' < dim R/Q`
  obtain ⟨d', hd'⟩ := exists_ringKrullDim_quotient_eq_natCast Q'
  have hd'd : d' < d := by
    have := ringKrullDim_quotient_lt_of_lt hQQ'
    rw [hd', hdQ] at this
    exact_mod_cast this
  have hA := ih d' hd'd Q' hd' (hJQ.trans hQQ'.le) hg'
  exact grIdeal_localization_eq_span_initialForm_of_le_localization Q Q' J hQQ'.le hJQ g hg0 hg hA hB
    (dimensionLEOne_quotient_localization_of_forall_prime_eq_or_eq Q Q' hmin) (hfin Q' Q hQQ'.le)

/-- Corollary 3 (c) under the finiteness condition of footnote 10 ("if `Q'` and `Q''` are any
pair of prime ideals in `R` such that `Q' ⊇ Q''`, then the integral closure of
`R_{Q'}/Q''R_{Q'}` in its field of quotients is a finite module over this ring"), p. 243. -/
theorem grIdeal_localization_eq_span_initialForm_of_finite [Hironaka.Cited.CurveFiniteIntegralClosure.{u}] [Hironaka.Cited.IsRegularLocalRingLocalizationOfIsRegularLocalRing.{u}] [Hironaka.Cited.IsSeparableFieldExtensionIff.{u}] [CharZero (ResidueField R)]
    (hfin : ∀ (Q' Q'' : Ideal R) [Q'.IsPrime] [Q''.IsPrime], Q'' ≤ Q' →
      Module.Finite (Localization.AtPrime Q' ⧸ Q''.map (algebraMap R (Localization.AtPrime Q')))
        (integralClosure (Localization.AtPrime Q' ⧸
          Q''.map (algebraMap R (Localization.AtPrime Q')))
          (FractionRing (Localization.AtPrime Q' ⧸
            Q''.map (algebraMap R (Localization.AtPrime Q'))))))
    (Q J : Ideal R) [Q.IsPrime] (hJQ : J ≤ Q) {m : ℕ} (g : Fin m → R)
    (hg : IsLocallyAdaptedSystem R Q J g) :
    grIdeal (Q.map (algebraMap R (Localization.AtPrime Q)))
        (J.map (algebraMap R (Localization.AtPrime Q))) =
      Ideal.span (Set.range fun j =>
        initialForm (Q.map (algebraMap R (Localization.AtPrime Q)))
          (algebraMap R (Localization.AtPrime Q) (g j))) := by
  classical
  -- remove the zero elements of the system (their initial forms are `0`)
  have hg' : IsLocallyAdaptedSystem R Q J
      (fun i => g ((Fintype.equivFin {j // g j ≠ 0}).symm i).1) := by
    refine ⟨fun i => hg.1 _, ?_, fun i => hg.2.2 _⟩
    rw [hg.2.1]
    exact Ideal.span_range_eq_span_range_filter_of_forall_eq_zero (fun j => g j ≠ 0) (fun j => initialForm _ (g j))
      fun j hj => by rw [not_not.mp hj, initialForm_zero]
  rw [forall_grIdeal_localization_eq_span_initialForm_of_finite hfin J _ (fun i => ((Fintype.equivFin {j // g j ≠ 0}).symm i).2) Q
    inferInstance hJQ hg']
  exact (Ideal.span_range_eq_span_range_filter_of_forall_eq_zero (fun j => g j ≠ 0)
    (fun j => initialForm _ (algebraMap R (Localization.AtPrime Q) (g j)))
    fun j hj => by rw [not_not.mp hj, map_zero, initialForm_zero]).symm

end Cor3cInduction

/-! ### Reduction to the completion (p. 243) -/

/-- For a faithfully flat `A`-algebra `B`, `ν_{IB}(a) = ν_I(a)` (`Iⁿ B ∩ A = Iⁿ`). -/
theorem Ideal.ordElem_map_of_faithfullyFlat {A B : Type*} [CommRing A] [CommRing B]
    [Algebra A B] [Module.FaithfullyFlat A B] (I : Ideal A) (a : A) :
    Ideal.ordElem (I.map (algebraMap A B)) (algebraMap A B a) = Ideal.ordElem I a := by
  have h : ∀ ν : ℕ, algebraMap A B a ∈ I.map (algebraMap A B) ^ ν ↔ a ∈ I ^ ν := by
    intro ν
    rw [← Ideal.map_pow]
    refine ⟨fun h => ?_, Ideal.mem_map_of_mem _⟩
    rw [← Ideal.comap_map_eq_self_of_faithfullyFlat (B := B) (I ^ ν)]
    exact h
  simp only [Ideal.ordElem, h]

/-- Lemma 2 of §1 for a faithfully flat homomorphism (as in the Remark, p. 238): if the initial
forms of the `g_j` generate `gr_I(J, A)`, then those of their images generate `gr_{IB}(JB, B)`. -/
theorem grIdeal_map_eq_span_initialForm_of_faithfullyFlat {A B : Type u} [CommRing A] [CommRing B]
    [IsNoetherianRing A] [IsNoetherianRing B] [Algebra A B] [Module.FaithfullyFlat A B]
    (I J : Ideal A) (hI : I.map (algebraMap A B) ≤ Ring.jacobson B) {m : ℕ} (g : Fin m → A)
    (hg : grIdeal I J = Ideal.span (Set.range fun j => initialForm I (g j))) :
    grIdeal (I.map (algebraMap A B)) (J.map (algebraMap A B)) =
      Ideal.span (Set.range fun j =>
        initialForm (I.map (algebraMap A B)) (algebraMap A B (g j))) := by
  rw [← map_grIdeal_eq_grIdeal_map_of_flat A B I J hI, hg, Ideal.map_span, ← Set.range_comp]
  congr 2
  funext j
  exact AssocGraded.map_initialForm_of_ordElem_map_eq _ I (g j)
    (Ideal.ordElem_map_of_faithfullyFlat I (g j))

/-- Integral closure and localization (footnote 10: "this condition … obviously remains valid if
we replace `R` by a ring of quotients"): if the integral closure of the domain `S` is finite and
`T = U⁻¹S`, then the integral closure of `T` is finite over `T`. -/
theorem finite_integralClosure_of_isLocalization {S T K : Type u} [CommRing S]
    [IsDomain S] [CommRing T] [IsDomain T] [IsNoetherianRing T] [Field K] [Algebra S T]
    [Algebra T K] [IsFractionRing T K] (U : Submonoid S) (hU : U ≤ nonZeroDivisors S)
    [IsLocalization U T] (hS : Module.Finite S (integralClosure S (FractionRing S))) :
    Module.Finite T (integralClosure T K) := by
  classical
  let _ : Algebra S K := ((algebraMap T K).comp (algebraMap S T)).toAlgebra
  have _ : IsScalarTower S T K := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hinj : Function.Injective (algebraMap S K) :=
    (IsFractionRing.injective T K).comp (IsLocalization.injective T hU)
  have _ : FaithfulSMul S K := (faithfulSMul_iff_algebraMap_injective S K).mpr hinj
  have _ : IsFractionRing S K := by
    refine IsFractionRing.of_field S K fun z => ?_
    obtain ⟨t₁, t₂, -, rfl⟩ := IsFractionRing.div_surjective (A := T) z
    obtain ⟨s₁, u₁, rfl⟩ := IsLocalization.exists_mk'_eq U t₁
    obtain ⟨s₂, u₂, rfl⟩ := IsLocalization.exists_mk'_eq U t₂
    refine ⟨s₁ * u₂, s₂ * u₁, ?_⟩
    have h1 : algebraMap T K (IsLocalization.mk' T s₁ u₁) * algebraMap S K u₁ =
        algebraMap S K s₁ := by
      show _ * algebraMap T K (algebraMap S T u₁) = algebraMap T K (algebraMap S T s₁)
      rw [← map_mul, IsLocalization.mk'_spec]
    have h2 : algebraMap T K (IsLocalization.mk' T s₂ u₂) * algebraMap S K u₂ =
        algebraMap S K s₂ := by
      show _ * algebraMap T K (algebraMap S T u₂) = algebraMap T K (algebraMap S T s₂)
      rw [← map_mul, IsLocalization.mk'_spec]
    have hu₁ : algebraMap S K u₁ ≠ 0 :=
      (map_ne_zero_iff _ hinj).mpr (nonZeroDivisors.ne_zero (hU u₁.2))
    have hu₂ : algebraMap S K u₂ ≠ 0 :=
      (map_ne_zero_iff _ hinj).mpr (nonZeroDivisors.ne_zero (hU u₂.2))
    rw [map_mul, map_mul, ← h1, ← h2]
    field_simp
  let e : FractionRing S ≃ₐ[S] K := IsLocalization.algEquiv (nonZeroDivisors S) (FractionRing S) K
  have hW : Module.Finite S (integralClosure S K) := by
    rw [← integralClosure_map_algEquiv e]
    exact Module.Finite.equiv
      (Subalgebra.equivMapOfInjective (integralClosure S (FractionRing S)) (e : FractionRing S →ₐ[S] K)
        e.injective).toLinearEquiv
  obtain ⟨s, hs⟩ := hW.fg_top
  set N : Submodule T K := Submodule.span T ((fun w : integralClosure S K => (w : K)) '' (s : Set _))
  have _ : IsNoetherian T N :=
    isNoetherian_span_of_finite T ((s.finite_toSet).image _)
  have hle : (integralClosure T K).toSubmodule ≤ N := by
    intro x hx
    obtain ⟨u, hu⟩ := IsIntegral.exists_multiple_integral_of_isLocalization U (Rₘ := T) x hx
    have hux : (⟨u • x, hu⟩ : integralClosure S K) ∈ Submodule.span S (s : Set _) :=
      hs ▸ Submodule.mem_top
    have hux' : u • x ∈ Submodule.span S ((fun w : integralClosure S K => (w : K)) '' (s : Set _)) := by
      have := Submodule.apply_mem_span_image_of_mem_span (integralClosure S K).val.toLinearMap hux
      simpa using this
    have hux'' : u • x ∈ N := Submodule.span_le_restrictScalars S T _ hux'
    obtain ⟨v, hv⟩ := IsLocalization.map_units T u
    have hx' : x = ((v⁻¹ : Tˣ) : T) • (u • x) := by
      rw [Submonoid.smul_def, Algebra.smul_def, Algebra.smul_def, ← mul_assoc,
        IsScalarTower.algebraMap_apply S T K, ← map_mul, ← hv, Units.inv_mul, map_one, one_mul]
    rw [hx']
    exact N.smul_mem _ hux''
  have hfg : (integralClosure T K).toSubmodule.FG := Submodule.FG.of_le_of_isNoetherian hle
  exact Module.Finite.iff_fg.mpr hfg

/-- Footnote 10 for a complete noetherian local ring `A`: for primes `Q'' ⊆ Q'` of `A`, the
integral closure of `A_{Q'}/Q''A_{Q'}` is finite over it, since that of the complete local
domain `A/Q''` is (`curve_finite_integralClosure`, the cited fact of footnote 10) and
`A_{Q'}/Q''A_{Q'}` is a ring of quotients of `A/Q''`. -/
theorem finite_integralClosure_localization_quotient_of_isAdicComplete [Hironaka.Cited.CurveFiniteIntegralClosure.{u}] {A : Type u} [CommRing A] [IsLocalRing A]
    [IsNoetherianRing A] [IsAdicComplete (maximalIdeal A) A] (Q' Q'' : Ideal A) [Q'.IsPrime]
    [Q''.IsPrime] (hQ : Q'' ≤ Q') :
    Module.Finite (Localization.AtPrime Q' ⧸ Q''.map (algebraMap A (Localization.AtPrime Q')))
      (integralClosure (Localization.AtPrime Q' ⧸ Q''.map (algebraMap A (Localization.AtPrime Q')))
        (FractionRing (Localization.AtPrime Q' ⧸
          Q''.map (algebraMap A (Localization.AtPrime Q'))))) := by
  have hdisj : Disjoint (Q'.primeCompl : Set A) (Q'' : Set A) :=
    Set.disjoint_left.mpr fun a ha haQ => ha (hQ haQ)
  have _ : (Q''.map (algebraMap A (Localization.AtPrime Q'))).IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint Q'.primeCompl _ Q'' inferInstance hdisj
  have _ : IsLocalRing (A ⧸ Q'') :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk Q'') Ideal.Quotient.mk_surjective
  have _ : IsAdicComplete (maximalIdeal (A ⧸ Q'')) (A ⧸ Q'') := by
    have : IsAdicComplete (maximalIdeal A) (A ⧸ Q'') := curve_isAdicComplete_of_finite _ _
    have h := curve_isAdicComplete_map (B := A ⧸ Q'') (maximalIdeal A)
    rwa [Ideal.Quotient.algebraMap_eq, IsLocalRing.map_maximalIdeal_of_surjective _
      Ideal.Quotient.mk_surjective] at h
  have hS := curve_finite_integralClosure (A ⧸ Q'')
  refine finite_integralClosure_of_isLocalization
    (Algebra.algebraMapSubmonoid (A ⧸ Q'') Q'.primeCompl) ?_ hS
  rintro _ ⟨r, hr, rfl⟩
  refine mem_nonZeroDivisors_of_ne_zero ?_
  rw [Ne, Ideal.Quotient.algebraMap_eq, Ideal.Quotient.eq_zero_iff_mem]
  exact fun h => hr (hQ h)

/-- p. 243: "the local homomorphism of `R_Q` into `R̂_{Q̂}` transforms a regular system of parameters
of the first local ring into such a system of parameters of the second", for a flat local
homomorphism `α : A → B` of regular local rings with `MB = M'` (here `A = R_Q`, `B = R̂_{Q̂}`, and
`M B = M'` is the hypothesis `Q̂R̂_{Q̂} = QR̂_{Q̂}`): an `A`-regular system of parameters `s` is mapped
by `α` onto a system generating `M'`; as `dim A ≤ dim B` by flatness (going down, Matsumura 13.B
Thm. 19, `Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown`), `dim B = #(α s) = #s` since `B` is
regular. -/
theorem RingHom.mapsRSOP_of_flat_of_map_maximalIdeal_eq {A B : Type u} [CommRing A] [CommRing B]
    [IsRegularLocalRing A] [IsRegularLocalRing B] (α : A →+* B) [IsLocalHom α]
    (hflat : letI := α.toAlgebra; Module.Flat A B)
    (hM : (maximalIdeal A).map α = maximalIdeal B) : RingHom.MapsRSOP α := by
  classical
  obtain ⟨-, s, hs⟩ := (isRegularLocalRing_iff_exists_rsop A).mp inferInstance
  have hspan : Ideal.span ((s.image α : Finset B) : Set B) = maximalIdeal B := by
    rw [Finset.coe_image, ← Ideal.map_span, hs.1, hM]
  have hle : (s.image α).card ≤ s.card := Finset.card_image_le
  -- `dim A ≤ dim B` (flat, going down)
  have hdim : ringKrullDim A ≤ ringKrullDim B := by
    let _ := α.toAlgebra
    have : Module.Flat A B := hflat
    have : IsLocalHom (algebraMap A B) := ‹IsLocalHom α›
    have h := Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown (maximalIdeal A)
      (maximalIdeal B)
    rw [← IsLocalRing.maximalIdeal_height_eq_ringKrullDim (R := A),
      ← IsLocalRing.maximalIdeal_height_eq_ringKrullDim (R := B), h]
    exact_mod_cast le_self_add
  -- `dim B ≤ #(α s)` (the images generate the maximal ideal)
  have hge : ringKrullDim B ≤ (s.image α).card := by
    refine (ringKrullDim_le_spanFinrank_maximalIdeal B).trans ?_
    rw [← hspan]
    have := Submodule.spanFinrank_span_le_ncard_of_finite (R := B) (s.image α).finite_toSet
    rw [Set.ncard_coe_finset] at this
    exact_mod_cast this
  have hcard : (s.image α).card = s.card := by
    have h1 : (s.card : WithBot ℕ∞) ≤ (s.image α).card := by rw [hs.2]; exact hdim.trans hge
    have : s.card ≤ (s.image α).card := by exact_mod_cast h1
    omega
  refine ⟨s, hs, ⟨hspan, ?_⟩, ?_⟩
  · rw [hcard, hs.2]
    exact le_antisymm hdim (hge.trans (by rw [hcard, ← hs.2]))
  · exact Finset.card_image_iff.mp hcard

/-- p. 243: "the conclusion in (c) is changed into an equivalent one" (the direction used: from
`R'_{Q'} = R̂_{Q̂}` back to `R_Q`).  Let `α : A → B` be a local homomorphism of regular local rings which
transforms a regular system of parameters of `A` into such a system of parameters of `B`, `J` an ideal of
`A` and `(g_j)` elements of `J`.  If the initial forms of the `α(g_j)` generate
`gr_{M'}(JB, B)`, then those of the `g_j` generate `gr_M(J, A)`.  This is the Remark of p. 238: a
subsystem of `(α(g_j))` is a standard base of `JB` (as on p. 243 for (b): "a suitably re-ordered
subsystem of `(g₁, …, g_m)` is a standard base"), hence the corresponding subsystem of `(g_j)` is a
standard base of `J`, whose initial forms generate `gr_M(J, A)`. -/
theorem grIdeal_eq_span_initialForm_of_mapsRSOP {A B : Type u} [CommRing A] [CommRing B]
    [IsRegularLocalRing A] [IsRegularLocalRing B] (α : A →+* B) [IsLocalHom α]
    (hα : RingHom.MapsRSOP α) (J : Ideal A) {m : ℕ} (g : Fin m → A) (hgJ : ∀ j, g j ∈ J)
    (h : grIdeal (maximalIdeal B) (J.map α) =
      Ideal.span (Set.range fun j => initialForm (maximalIdeal B) (α (g j)))) :
    grIdeal (maximalIdeal A) J = Ideal.span (Set.range fun j => initialForm (maximalIdeal A) (g j)) := by
  obtain ⟨k, σ, -, hσ⟩ := exists_isStandardBase_comp B (J.map α) (fun j => α (g j))
    (fun j => Ideal.mem_map_of_mem _ (hgJ j)) h.symm
  have hσ' := (isStandardBase_iff_isStandardBase_map α hα J (g ∘ σ)).mpr hσ
  refine le_antisymm ?_ (Ideal.span_le.mpr ?_)
  · rw [hσ'.2.2.2.1]
    refine Ideal.span_mono ?_
    rintro _ ⟨t, rfl⟩
    exact ⟨σ t, rfl⟩
  · rintro _ ⟨j, rfl⟩
    exact Ideal.subset_span ⟨g j, hgJ j, rfl⟩

/-- The reduction of Corollary 3 (c) to a faithfully flat local extension `R → R'` with
`MR' = M'` (p. 243: "if we replace `R`, `M`, `J` and `Q` by `R̂`, `MR̂`, `Ĵ = JR̂` and `Q̂`
respectively, then the conditions (i) and (ii) remain satisfied by `(g₁, …, g_m)`, viewed as a
system of elements of `Ĵ`; and moreover the conclusion in (c) is changed into an equivalent
one"), for a prime `Q'` of `R'` over `Q` with `Q'R'_{Q'} = QR'_{Q'}`, when `R'` satisfies the
finiteness condition of footnote 10.

The proof follows the printed one (p. 243): "by assumption, we have a prime ideal `Q̂` in the completion
`R̂` of `R` such that `Q̂ ∩ R = Q`, and that the local homomorphism of `R_Q` into `R̂_{Q̂}` transforms a
regular system of parameters of the first local ring into such a system of parameters of the second"
(`R_Q` and `R'_{Q'}` are regular by footnote 9, the cited leaf of Serre's theorem; the transformation of
the regular system of parameters is `RingHom.mapsRSOP_of_flat_of_map_maximalIdeal_eq`, from
`QR'_{Q'} = Q'R'_{Q'}`); "it is easily seen that, if we replace `R`, `M`, `J` and `Q` by `R̂`, `MR̂`,
`Ĵ = JR̂` and `Q̂` respectively, then the conditions (i) and (ii) remain satisfied by `(g₁, …, g_m)`"
(Lemma 2 of §1 for `R → R'`, `grIdeal_map_eq_span_initialForm_of_faithfullyFlat`, and the preservation
of the orders `ν_M` and `ν_{QR_Q}`); "and moreover the conclusion in (c) is changed into an equivalent
one" (`grIdeal_eq_span_initialForm_of_mapsRSOP`, from the Remark of p. 238 for `R_Q → R'_{Q'}`). -/
theorem grIdeal_localization_eq_span_initialForm_of_faithfullyFlat [Hironaka.Cited.CurveFiniteIntegralClosure.{u}] [Hironaka.Cited.IsRegularLocalRingLocalizationOfIsRegularLocalRing.{u}] [Hironaka.Cited.IsSeparableFieldExtensionIff.{u}] {R R' : Type u} [CommRing R] [IsRegularLocalRing R]
    [CharZero (ResidueField R)] [CommRing R'] [IsRegularLocalRing R'] [Algebra R R']
    [Module.FaithfullyFlat R R'] [IsLocalHom (algebraMap R R')]
    (hM : (maximalIdeal R).map (algebraMap R R') = maximalIdeal R')
    (hfin : ∀ (Q' Q'' : Ideal R') [Q'.IsPrime] [Q''.IsPrime], Q'' ≤ Q' →
      Module.Finite (Localization.AtPrime Q' ⧸ Q''.map (algebraMap R' (Localization.AtPrime Q')))
        (integralClosure (Localization.AtPrime Q' ⧸
          Q''.map (algebraMap R' (Localization.AtPrime Q')))
          (FractionRing (Localization.AtPrime Q' ⧸
            Q''.map (algebraMap R' (Localization.AtPrime Q'))))))
    (Q J : Ideal R) [Q.IsPrime] (hJQ : J ≤ Q) {m : ℕ} (g : Fin m → R)
    (hg : IsLocallyAdaptedSystem R Q J g) (Q' : Ideal R') [Q'.IsPrime]
    (hQ' : Q'.comap (algebraMap R R') = Q)
    (hQ'' : Q'.map (algebraMap R' (Localization.AtPrime Q')) =
      Q.map ((algebraMap R' (Localization.AtPrime Q')).comp (algebraMap R R'))) :
    grIdeal (Q.map (algebraMap R (Localization.AtPrime Q)))
        (J.map (algebraMap R (Localization.AtPrime Q))) =
      Ideal.span (Set.range fun j =>
        initialForm (Q.map (algebraMap R (Localization.AtPrime Q)))
          (algebraMap R (Localization.AtPrime Q) (g j))) := by
  classical
  have _ : CharZero (ResidueField R') :=
    (RingHom.charZero_iff (ResidueField.map (algebraMap R R')).injective).mp inferInstance
  -- the local homomorphism `β : R_Q → R'_{Q'}`, faithfully flat
  have hQc : Q = Q'.comap (algebraMap R R') := hQ'.symm
  set β := Localization.localRingHom Q Q' (algebraMap R R') hQc with hβdef
  have hβmap : ∀ r, β (algebraMap R (Localization.AtPrime Q) r) =
      algebraMap R' (Localization.AtPrime Q') (algebraMap R R' r) :=
    Localization.localRingHom_to_map Q Q' (algebraMap R R') hQc
  let _ : Algebra (Localization.AtPrime Q) (Localization.AtPrime Q') := β.toAlgebra
  have _ : IsScalarTower R (Localization.AtPrime Q) (Localization.AtPrime Q') :=
    IsScalarTower.of_algebraMap_eq fun r => by
      show algebraMap R (Localization.AtPrime Q') r = β (algebraMap R _ r)
      rw [hβmap, IsScalarTower.algebraMap_apply R R' (Localization.AtPrime Q')]
  have _ : Module.Flat (Localization.AtPrime Q) (Localization.AtPrime Q') := inferInstance
  have _ : IsLocalHom (algebraMap (Localization.AtPrime Q) (Localization.AtPrime Q')) :=
    (inferInstance : IsLocalHom β)
  have _ : Module.FaithfullyFlat (Localization.AtPrime Q) (Localization.AtPrime Q') :=
    Module.FaithfullyFlat.of_flat_of_isLocalHom
  have hcomp : (algebraMap R' (Localization.AtPrime Q')).comp (algebraMap R R') =
      (algebraMap (Localization.AtPrime Q) (Localization.AtPrime Q')).comp
        (algebraMap R (Localization.AtPrime Q)) :=
    (RingHom.ext hβmap).symm
  have hmapQ : Q'.map (algebraMap R' (Localization.AtPrime Q')) =
      (Q.map (algebraMap R (Localization.AtPrime Q))).map
        (algebraMap (Localization.AtPrime Q) (Localization.AtPrime Q')) := by
    rw [hQ'', Ideal.map_map, hcomp]
  have hmapJ : (J.map (algebraMap R R')).map (algebraMap R' (Localization.AtPrime Q')) =
      (J.map (algebraMap R (Localization.AtPrime Q))).map
        (algebraMap (Localization.AtPrime Q) (Localization.AtPrime Q')) := by
    rw [Ideal.map_map, Ideal.map_map, hcomp]
  -- (i) and (ii) for `R'`, `M'`, `Q'`, `JR'` and the images of the `g_j`
  have hjac : (maximalIdeal R).map (algebraMap R R') ≤ Ring.jacobson R' := by
    rw [hM, ← Ideal.jacobson_bot]
    exact maximalIdeal_le_jacobson _
  have hg' : IsLocallyAdaptedSystem R' Q' (J.map (algebraMap R R')) fun j => algebraMap R R' (g j) := by
    refine ⟨fun j => Ideal.mem_map_of_mem _ (hg.1 j), ?_, fun j => ?_⟩
    · have := grIdeal_map_eq_span_initialForm_of_faithfullyFlat (maximalIdeal R) J hjac g hg.2.1
      rwa [hM] at this
    · rw [← hM, Ideal.ordElem_map_of_faithfullyFlat, hg.2.2 j, hmapQ, ← hβmap]
      exact (Ideal.ordElem_map_of_faithfullyFlat (B := Localization.AtPrime Q') _ _).symm
  have hJQ' : J.map (algebraMap R R') ≤ Q' := by
    rw [Ideal.map_le_iff_le_comap, hQ']
    exact hJQ
  have key := grIdeal_localization_eq_span_initialForm_of_finite hfin Q'
    (J.map (algebraMap R R')) hJQ' _ hg'
  rw [hmapQ, hmapJ] at key
  simp only [← hβmap] at key
  -- footnote 9: `R_Q` and `R'_{Q'}` are regular local rings (localizations of regular local rings)
  have _ : IsRegularLocalRing (Localization.AtPrime Q) :=
    isRegularLocalRing_localization_of_isRegularLocalRing R Q
  have _ : IsRegularLocalRing (Localization.AtPrime Q') :=
    isRegularLocalRing_localization_of_isRegularLocalRing R' Q'
  have hmaxQ : Q.map (algebraMap R (Localization.AtPrime Q)) =
      maximalIdeal (Localization.AtPrime Q) := Localization.AtPrime.map_eq_maximalIdeal
  have hmaxQ' : Q'.map (algebraMap R' (Localization.AtPrime Q')) =
      maximalIdeal (Localization.AtPrime Q') := Localization.AtPrime.map_eq_maximalIdeal
  -- "the local homomorphism of `R_Q` into `R'_{Q'}` transforms a regular system of parameters of the
  -- first local ring into such a system of parameters of the second"
  have hβM : (maximalIdeal (Localization.AtPrime Q)).map β =
      maximalIdeal (Localization.AtPrime Q') := by
    rw [← hmaxQ', hmapQ, hmaxQ]
    rfl
  have hβ : RingHom.MapsRSOP β := RingHom.mapsRSOP_of_flat_of_map_maximalIdeal_eq β
    ‹Module.Flat (Localization.AtPrime Q) (Localization.AtPrime Q')› hβM
  -- "the conclusion in (c) is changed into an equivalent one"
  have hβM' : (maximalIdeal (Localization.AtPrime Q)).map
      (algebraMap (Localization.AtPrime Q) (Localization.AtPrime Q')) =
        maximalIdeal (Localization.AtPrime Q') := hβM
  rw [hmaxQ, hβM'] at key
  rw [hmaxQ]
  exact grIdeal_eq_span_initialForm_of_mapsRSOP β hβ _ (fun j => algebraMap R (Localization.AtPrime Q) (g j))
    (fun j => Ideal.mem_map_of_mem _ (hg.1 j)) key

section Corollary3c

variable {R : Type u} [CommRing R] [IsRegularLocalRing R]

/-- Corollary 3 (c), p. 242: "If the residue field of `R` is of characteristic zero, and there
exists a prime ideal `Q̂` in the completion `R̂` of `R` such that `Q̂ ∩ R = Q` and that
`Q̂R̂_{Q̂} = QR̂_{Q̂}`, then the initial forms of the elements `g_j` (`1 ≤ j ≤ m`) in
`gr_{QR_Q}(R_Q)` generate the ideal `gr_{QR_Q}(JR_Q, R_Q)`."

Footnote 10 (p. 243), quoted for the finiteness condition used in the proof: "This follows from
the fact that `R̂/Q''` satisfies the finiteness condition. (Recall the fact that this condition
is satisfied by every complete noetherian local ring without nilpotent elements.)"  Footnote 9
(p. 243): "We recall the fact that a localization of a regular local ring by any prime ideal is
regular. (This fact is due to J. P. Serre, *Sur la dimension homologique des anneaux et des
modules noethériens*, Proc. of the International Symposium, Tokyo-Nikko (1955), Scientific
Council of Japan, 1956, pp. 175–189.) Replace `Q̂`, if necessary, by a minimal divisor of `QR̂`
which is contained in it."

Formalization notes (encoding).
* `R̂` is `AdicCompletion (maximalIdeal R) R`; `Q̂ ∩ R = Q` is
  `Qhat.comap (algebraMap R (AdicCompletion (maximalIdeal R) R)) = Q` and `Q̂R̂_{Q̂} = QR̂_{Q̂}`
  is the equality of the two extensions to `R̂_{Q̂} = Localization.AtPrime Q̂`.
* "the residue field of `R` is of characteristic zero" is `[CharZero (ResidueField R)]`.
* No regularity hypothesis on `R̂` is imposed: that `R̂` is regular is proved
  (`isRegularLocalRing_adicCompletion_of_isRegularLocalRing`).

The reduction to the complete case (`grIdeal_localization_eq_span_initialForm_of_faithfullyFlat`) follows
the paper: footnote 9 (Serre's theorem) gives that `R_Q` and `R̂_{Q̂}` are regular, the local homomorphism
`R_Q → R̂_{Q̂}` transforms a regular system of parameters into such a system
(`RingHom.mapsRSOP_of_flat_of_map_maximalIdeal_eq`; the replacement of `Q̂` by a minimal divisor of `QR̂` is
vacuous, since `QR̂_{Q̂} = Q̂R̂_{Q̂}` makes `Q̂` minimal over `QR̂`), (i) and (ii) pass to `R̂`, `Q̂`, `JR̂`
(Lemma 2 of §1 and the preservation of orders, `IR̂ ∩ R = I`), and the conclusion for `R̂_{Q̂}` implies
that for `R_Q` by the Remark of p. 238 (`grIdeal_eq_span_initialForm_of_mapsRSOP`).

Finiteness and induction (the proof follows the printed one).
* Finiteness (`finite_integralClosure_localization_quotient_of_isAdicComplete`): "if `Q'` and `Q''` are
  any pair of prime ideals in `R` such that `Q' ⊃ Q''`, then the integral closure of `R_{Q'}/Q''R_{Q'}` in
  its field of quotients is a finite module over this ring.  (Footnote 10: This follows from the fact that
  `R/Q''` satisfies the finiteness condition.  (Recall the fact that this condition is satisfied by every
  complete noetherian local ring without nilpotent elements.))": the finiteness of the integral closure of
  the complete local domain `R̂/Q''` is the cited leaf `lem:III.1-derived-normal-ring-finite`
  (`curve_finite_integralClosure`, the fact recalled in footnote 10, which the paper also uses on p. 218);
  the passage to the ring of quotients `R̂_{Q'}/Q''R̂_{Q'}` of `R̂/Q''` is proved
  (`finite_integralClosure_of_isLocalization`).  The preceding sentence "We then see that `R` is a formal power
  series ring over a field of characteristic zero" is an assertion without proof (Cohen's structure
  theorem); the argument of footnote 10 does not use it, so it is not formalized.
* Induction (`forall_grIdeal_localization_eq_span_initialForm_of_finite`): "by an obvious induction on the
  dimension of `R/Q`, the proof of (c) can be reduced to the case in which `dim(R/Q) = 1`": strong induction
  on the natural number `dim(R/Q)` (`exists_ringKrullDim_quotient_eq_natCast`,
  `ringKrullDim_quotient_lt_of_lt`); the base case is "`R/Q` regular" (Lemma 7), the step passes to a prime
  `Q' ⊋ Q` with no prime strictly between (so `dim R/Q' < dim R/Q`) and applies the dimension-`≤ 1` case to
  `R_{Q'}` and `QR_{Q'}`; "which obviously remains valid if we replace `R` by a ring of quotients of `R` with
  respect to any prime ideal" is the finiteness hypothesis, quantified over all pairs `Q'' ⊆ Q'` of primes of
  the ambient ring.

The reduction to the complete case (footnote 9) and the dimension-one case (p. 244) follow the printed
proof, for every admissible monoidal transform `R₁` (not a specially constructed one); the steps the paper
does not argue are gaps filled (below).

Deviation from the paper (gap filled): the regular case (Lemma 7 gives `gr_Q(J, R)`, transported
to `gr_{QR_Q}(R_Q)`), the transfer of (i), (ii) to `R̂`, that the local homomorphism `R_Q → R̂_{Q̂}` transforms a
regular system of parameters into such a system (from `QR̂_{Q̂} = Q̂R̂_{Q̂}` and the dimension formula for flat
local homomorphisms), properties (i), (ii) for `Q'` in the
induction (Theorem 1 twice), `R_Q ≅ (R₁)_{Q₁}`, `JR_Q = J₁(R₁)_{Q₁}`, `h_j = g_j · unit`, the
permissibility of `M` before applying (b), and the removal of zero `g_j` are proved; so are the existence
of an admissible monoidal transform `R₁` with a prime `Q₁` over `Q` (`exists_monoidalTransform_curveImage_lt`)
and "as is easily seen, this process cannot be repeated infinitely many times" for every admissible `R₁`
(`exists_ringHom_curveImage_lt_of_comap_eq`: `R₁/Q₁` is again a localization of its intersection `φ(R₁) ∩ W`
with the integral closure `W` of `R/Q`, and this intersection strictly contains `φ(R) ∩ W`). -/
@[blueprint "cor:III.thm5-3c"
  (statement := /-- Hypotheses as in \cref{cor:III.thm5-3a}. (c) If the residue field of $R$ is
    of characteristic zero, and there exists a prime ideal $\hat Q$ in the completion $\hat R$
    of $R$ such that $\hat Q\cap R=Q$ and that $\hat Q\hat R_{\hat Q}=Q\hat R_{\hat Q}$, then
    the initial forms of the elements $g_j$ $(1\le j\le m)$ in
    $\operatorname{gr}_{QR_Q}(R_Q)$ generate the ideal $\operatorname{gr}_{QR_Q}(JR_Q,R_Q)$.
    (Corollary 3 (c), p.~242.) -/)
  (proof := /-- The assertion (c) follows Lemma~7, \S2, Ch.~II (\cref{lem:II.2-7}), if
    $R/Q$ is regular. The proof of (c) for the general case can first be reduced to the case in
    which $R$ is complete. In fact, by assumption, we have a prime ideal $\hat Q$ in the
    completion $\hat R$ of $R$ such that $\hat Q\cap R=Q$, and that the local homomorphism of
    $R_Q$ into $\hat R_{\hat Q}$ transforms a regular system of parameters of the first local
    ring into such a system of parameters of the second (footnote 9: ``We recall the fact that a
    localization of a regular local ring by any prime ideal is regular. (This fact is due to
    J.~P.~Serre, \emph{Sur la dimension homologique des anneaux et des modules
    noeth\'eriens}, Proc.\ of the International Symposium, Tokyo-Nikko (1955), Scientific
    Council of Japan, 1956, pp.~175--189.) Replace $\hat Q$, if necessary, by a minimal divisor
    of $Q\hat R$ which is contained in it.''). It is easily seen that, if we replace $R$, $M$,
    $J$ and $Q$ by
    $\hat R$, $M\hat R$, $\hat J=J\hat R$ and $\hat Q$ respectively, then the conditions (i) and
    (ii) remain satisfied by $(g_1,\dots,g_m)$, viewed as a system of elements of $\hat J$; and
    moreover the conclusion in (c) is changed into an equivalent one. Therefore, we assume that
    $R$ is complete. We then see that $R$ is a formal power series ring over a field of
    characteristic zero. From this, we can first deduce that if $Q'$ and $Q''$ are any pair of
    prime ideals in $R$ such that $Q'\supseteq Q''$, then the integral closure of
    $R_{Q'}/Q''R_{Q'}$ in its field of quotients is a finite module over this ring (footnote 10:
    ``This follows from the fact that $R/Q''$ satisfies the finiteness condition. (Recall the
    fact that this condition is satisfied by every complete noetherian local ring without
    nilpotent elements.)''). Thus, to prove (c), we shall assume that $R$ has this property,
    which obviously remains valid if we replace $R$ by a ring of quotients of $R$ with respect
    to any prime ideal. Now, by an obvious induction on the dimension of $R/Q$, the proof of (c)
    can be reduced to the case in which $\dim(R/Q)=1$. Assume that $\dim(R/Q)=1$. Let $R_1$ be
    any monoidal transform of $R$ with center $M$ which is residually algebraic (hence,
    separable algebraic) over $R$, and such that there exists a prime ideal $Q_1$ in $R_1$ such
    that $Q_1\cap R=Q$. Let $J_1$ be the strict transform of $J$ in $R_1$, $x$ an element of $M$
    such that $MR_1=(x)R_1$, and $h_j=x^{-\nu_j}g_j$ with $\nu_j=\nu_M(g_j)$ for each $j$. Then
    we have $R_Q=(R_1)_{Q_1}$, $JR_Q=J_1(R_1)_{Q_1}$, and $(g_j)R_Q=(h_j)(R_1)_{Q_1}$ for each
    $j$. Therefore, in view of (b) (\cref{cor:III.thm5-3b}), the assertion (c) remains
    equivalent if we replace $R$, $J$, $Q$, $M$ and $(g_1,\dots,g_m)$ by $R_1$, $J_1$, $Q_1$,
    $M_1$ and $(h_1,\dots,h_m)$ respectively. Therefore, if $R_1/Q_1$ is regular, then the proof
    is done. If otherwise, we repeat the same process. As is easily seen, this process cannot be
    repeated infinitely many times, because the integral closure of $R/Q$ in its field of
    quotients is a finite $R/Q$-module. \qed

    \textbf{Formal proof.} The Lean proof follows the printed one. The reduction to the complete
    case follows footnote~9 (Serre's theorem gives that $R_Q$ and $\hat R_{\hat Q}$ are regular, the
    local homomorphism transforms a regular system of parameters into such a system, and the replacement
    of $\hat Q$ by a minimal divisor of $Q\hat R$ is vacuous because
    $Q\hat R_{\hat Q}=\hat Q\hat R_{\hat Q}$). The finiteness of the integral closure of
    $\hat R_{Q'}/Q''\hat R_{Q'}$ is footnote~10: the finiteness for the complete local domain
    $\hat R/Q''$ is the cited fact (\cref{lem:III.1-derived-normal-ring-finite}), and the passage to
    the ring of quotients is proved. The sentence ``We then see that $R$ is a formal power series ring over
    a field of characteristic zero'' is an assertion without proof; the argument of footnote~10 does
    not use it, so it is not formalized. The induction on $\dim(R/Q)$ is a strong induction on
    $\dim(R/Q)\in\mathbf N$ with base case ``$R/Q$ regular'' (Lemma~7); it passes from $Q$ to a prime
    $Q'\supsetneq Q$ with no prime strictly between them and applies the dimension-$\le1$ case to
    $R_{Q'}$ and $QR_{Q'}$; the finiteness hypothesis is assumed for all pairs $Q''\subseteq Q'$ of
    primes.

    \textbf{Gap in the paper filled.} Lean also proves: the transport of Lemma~7 from
    $\operatorname{gr}_Q(R)$ to $\operatorname{gr}_{QR_Q}(R_Q)$; that (i), (ii) hold for
    $\hat R$; that the local homomorphism $R_Q\to\hat R_{\hat Q}$ transforms a regular system of
    parameters into such a system (from $Q\hat R_{\hat Q}=\hat Q\hat R_{\hat Q}$ and the dimension formula
    for flat local homomorphisms); and, in the induction, for $Q'$ (Theorem~1 twice); $R_Q=(R_1)_{Q_1}$,
    $JR_Q=J_1(R_1)_{Q_1}$ and $(g_j)R_Q=(h_j)(R_1)_{Q_1}$; that $M$ is a permissible center
    (by (a)) before (b) is applied; the existence of a transform $R_1$ with a prime $Q_1$
    over $Q$; and ``as is easily seen, this process cannot be repeated infinitely many times'' for
    \emph{every} such $R_1$ (not only a constructed one): $R_1/Q_1$ is again a localization of its
    intersection with the integral closure $W$ of $R/Q$ (a general element of $M$ is used to see this),
    and this intersection strictly contains that of $R/Q$, a submodule of the finite module $W$. -/)
  (latexEnv := "corollary")]
theorem grIdeal_localization_eq_span_initialForm_of_adicCompletion [Hironaka.Cited.CurveFiniteIntegralClosure.{u}] [Hironaka.Cited.IsRegularLocalRingLocalizationOfIsRegularLocalRing.{u}] [Hironaka.Cited.IsSeparableFieldExtensionIff.{u}] (Q J : Ideal R) [Q.IsPrime] (hJQ : J ≤ Q)
    {m : ℕ} (g : Fin m → R) (hg : IsLocallyAdaptedSystem R Q J g) [CharZero (ResidueField R)]
    (Qhat : Ideal (AdicCompletion (maximalIdeal R) R)) [Qhat.IsPrime]
    (hQhat : Qhat.comap (algebraMap R (AdicCompletion (maximalIdeal R) R)) = Q)
    (hQhat' : Qhat.map (algebraMap (AdicCompletion (maximalIdeal R) R)
        (Localization.AtPrime Qhat)) =
      Q.map ((algebraMap (AdicCompletion (maximalIdeal R) R) (Localization.AtPrime Qhat)).comp
        (algebraMap R (AdicCompletion (maximalIdeal R) R)))) :
    grIdeal (Q.map (algebraMap R (Localization.AtPrime Q)))
        (J.map (algebraMap R (Localization.AtPrime Q))) =
      Ideal.span (Set.range fun j =>
        initialForm (Q.map (algebraMap R (Localization.AtPrime Q)))
          (algebraMap R (Localization.AtPrime Q) (g j))) := by
  have _ : IsRegularLocalRing (AdicCompletion (maximalIdeal R) R) :=
    isRegularLocalRing_adicCompletion_of_isRegularLocalRing R
  have _ := faithfullyFlat_adicCompletion_maximalIdeal R
  exact grIdeal_localization_eq_span_initialForm_of_faithfullyFlat AdicCompletion.maximalIdeal_eq_map.symm
    (fun Q' Q'' _ _ h => finite_integralClosure_localization_quotient_of_isAdicComplete Q' Q'' h) Q J hJQ g hg
    Qhat hQhat hQhat'

end Corollary3c

end Hironaka

