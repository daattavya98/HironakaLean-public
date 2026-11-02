/-
Copyright (c) 2026 Daattavya Aggarwal, Minhyong Kim, Oisin Kim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daattavya Aggarwal, Minhyong Kim, Oisin Kim
-/
module

public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Architect
public import Hironaka.Ch3.JStability
public import Hironaka.Compat.TauZSystem

/-!
# Compatibility layer: the property of Definition 10* for a single element (Ch. III §7, p. 251)

Definition 10* defines `T` as the smallest `k`-submodule of `gr¹_M(R)` such that
`((φ₁, …, φ_i) gr_M(R) ∩ k[T]) gr_M(R) = (φ₁, …, φ_i) gr_M(R)`.  For a single element `f`
(`i = 1`) this says exactly `φ ∈ k[T]` (`φ` the initial form of `f`): the elements of lowest degree
of `((φ) ∩ k[T]) gr_M(R)` are constants multiples of `φ`.  The paper uses this silently, e.g. in
Lemma 25 ("Then `φ` is a form of degree `ν` in `Z₁, …, Z_r, X₁, …, X_t`", p. 270).  The proof
transports the statement to the polynomial ring `gr_M(R) ≅ k[X₁, …, X_n]`
(`exists_bijective_aeval_mk`) and uses `mem_adjoin_of_isTauSubmoduleMv_aux` of
`Hironaka/Ch3/JStability.lean` (Lemma 23).

* `isTauZSubmodule_singleton_iff`: `IsTauZSubmodule R (f) T ↔ T ⊆ gr¹ ∧ φ ∈ k[T]`;
* `initialForm_mem_adjoin_tauZSubmodule`, `initialForm_mem_adjoin_tauZSubmoduleStar`,
  `tauZSubmodule_le_of_mem_adjoin`;
* `tauZ_eq_zero_of_initialForm_mem_adjoin`: `φ ∈ k[Z]` implies `τ_{(z)}(f) = 0`.
-/

@[expose] public section

open IsLocalRing MvPolynomial

namespace Hironaka

universe u

section GradedPolynomial

variable {R : Type u} [CommRing R] [IsRegularLocalRing R]

open Classical in
/-- `gr_M(R) ≅ k[X₁, …, X_n]`, `X_i ↦ [y_i]`, for some regular system of parameters
`(y₁, …, y_n)` of `R`. -/
theorem exists_bijective_aeval_mk :
    ∃ (n : ℕ) (y : Fin n → R) (hy : ∀ i, y i ∈ maximalIdeal R ^ 1),
      Function.Bijective (aeval (R := R ⧸ maximalIdeal R)
        fun i => AssocGraded.mk (maximalIdeal R) 1 (y i) (hy i)) := by
  obtain ⟨-, s, hs⟩ := (isRegularLocalRing_iff_exists_rsop R).mp inferInstance
  have hz : ∀ i : Fin s.card, ((s.equivFin.symm i : s) : R) ∈ maximalIdeal R ^ 1 := fun i => by
    rw [pow_one, ← hs.1]
    exact Ideal.subset_span (s.equivFin.symm i).2
  exact ⟨s.card, fun i => ((s.equivFin.symm i : s) : R), hz,
    assocGraded_maximalIdeal_aeval_bijective_of_rsop hs hz⟩

end GradedPolynomial


section PolyLemma

open MvPolynomial in
/-- For a form `F` and a space `T` of linear forms, `((F) ∩ E[T]) = (F)` iff `F ∈ E[T]`. -/
theorem span_inter_adjoin_eq_span_iff {E : Type u} [Field E] {m : ℕ}
    {F : MvPolynomial (Fin m) E} {ν : ℕ} (hF : F ∈ homogeneousSubmodule (Fin m) E ν)
    {T : Submodule E (MvPolynomial (Fin m) E)} (hT : T ≤ homogeneousSubmodule (Fin m) E 1) :
    Ideal.span ((Ideal.span {F} : Set (MvPolynomial (Fin m) E)) ∩
        (Algebra.adjoin E (T : Set (MvPolynomial (Fin m) E)) : Set (MvPolynomial (Fin m) E))) =
      Ideal.span {F} ↔ F ∈ Algebra.adjoin E (T : Set (MvPolynomial (Fin m) E)) := by
  constructor
  · intro h
    refine mem_adjoin_of_isTauSubmoduleMv_aux hF ?_ |> fun h' => h'
    refine ⟨hT, fun μ _ ψ _ => ?_⟩
    rw [h]
  · intro hFT
    refine le_antisymm (Ideal.span_le.mpr fun x hx => hx.1) ?_
    rw [Ideal.span_le, Set.singleton_subset_iff]
    exact Ideal.subset_span ⟨Ideal.mem_span_singleton_self F, hFT⟩

end PolyLemma

section Singleton

variable {R : Type u} [CommRing R] [IsRegularLocalRing R]

open Classical in
/-- **Definition 10* for a single element** (p. 251): `T` has the property of Definition 10* for
`(f)` iff `T` consists of linear forms and the initial form `φ` of `f` lies in `k[T]`.  (If
`((φ) ∩ k[T]) gr = (φ) gr`, then the elements of lowest degree of the left hand side are
multiples of `φ` by constants.) -/
theorem isTauZSubmodule_singleton_iff (f : R)
    (T : Submodule (R ⧸ maximalIdeal R) (AssocGraded (maximalIdeal R))) :
    IsTauZSubmodule R (fun _ : Fin 1 => f) T ↔
      T ≤ AssocGraded.homogeneous (maximalIdeal R) 1 ∧
        initialForm (maximalIdeal R) f ∈
          Algebra.adjoin (R ⧸ maximalIdeal R) (T : Set (AssocGraded (maximalIdeal R))) := by
  let _ : Field (R ⧸ maximalIdeal R) := Ideal.Quotient.field _
  set φ := initialForm (maximalIdeal R) f with hφdef
  unfold IsTauZSubmodule
  simp only [Set.range_const]
  constructor
  · rintro ⟨hT, hspan⟩
    refine ⟨hT, ?_⟩
    by_cases hφ0 : φ = 0
    · rw [hφ0]; exact zero_mem _
    obtain ⟨n, y, hy, hbij⟩ := exists_bijective_aeval_mk (R := R)
    let e := AlgEquiv.ofBijective _ hbij
    have he : ∀ q, e q = aeval (R := R ⧸ maximalIdeal R)
        (fun i => AssocGraded.mk (maximalIdeal R) 1 (y i) (hy i)) q := fun q => rfl
    have hφhom := initialForm_mem_homogeneous_toNat (S := R) f
    set d := (Ideal.ordElem (maximalIdeal R) f).toNat
    have hp : e.symm φ ∈ homogeneousSubmodule (Fin n) (R ⧸ maximalIdeal R) d := by
      rw [mem_homogeneousSubmodule]
      refine isHomogeneous_of_aeval_mem_homogeneous (maximalIdeal R) y hy hbij ?_
      rw [← he, e.apply_symm_apply]
      exact hφhom
    set T' := T.comap e.toLinearMap with hT'
    have hT'1 : T' ≤ homogeneousSubmodule (Fin n) (R ⧸ maximalIdeal R) 1 := by
      intro t ht
      rw [mem_homogeneousSubmodule]
      exact isHomogeneous_of_aeval_mem_homogeneous (maximalIdeal R) y hy hbij (hT ht)
    -- `φ ∈ ((φ) ∩ k[T]) gr`, transported to the polynomial ring
    have hmem : φ ∈ Ideal.span ((Ideal.span {φ} : Set (AssocGraded (maximalIdeal R))) ∩
        (Algebra.adjoin (R ⧸ maximalIdeal R) (T : Set (AssocGraded (maximalIdeal R))) :
          Set (AssocGraded (maximalIdeal R)))) := by
      rw [hspan]; exact Ideal.mem_span_singleton_self φ
    have hmem' : e.symm φ ∈ Ideal.span ((Ideal.span {e.symm φ} :
        Set (MvPolynomial (Fin n) (R ⧸ maximalIdeal R))) ∩
        (Algebra.adjoin (R ⧸ maximalIdeal R)
          (T' : Set (MvPolynomial (Fin n) (R ⧸ maximalIdeal R))) :
          Set (MvPolynomial (Fin n) (R ⧸ maximalIdeal R)))) := by
      have h1 := Ideal.mem_map_of_mem (e.symm : AssocGraded (maximalIdeal R) →+*
        MvPolynomial (Fin n) (R ⧸ maximalIdeal R)) hmem
      rw [Ideal.map_span] at h1
      refine Ideal.span_mono ?_ h1
      rintro _ ⟨x, ⟨hx1, hx2⟩, rfl⟩
      refine ⟨?_, ?_⟩
      · obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp hx1
        rw [SetLike.mem_coe, Ideal.mem_span_singleton']
        exact ⟨e.symm c, by rw [← hc]; simp⟩
      · have : (e.symm x) ∈ Algebra.adjoin (R ⧸ maximalIdeal R)
            (T' : Set (MvPolynomial (Fin n) (R ⧸ maximalIdeal R))) := by
          have h2 : x ∈ (Algebra.adjoin (R ⧸ maximalIdeal R)
              (T' : Set (MvPolynomial (Fin n) (R ⧸ maximalIdeal R)))).map
                (e : MvPolynomial (Fin n) (R ⧸ maximalIdeal R) →ₐ[R ⧸ maximalIdeal R] _) := by
            rw [AlgHom.map_adjoin]
            refine Algebra.adjoin_mono ?_ hx2
            intro t ht
            exact ⟨e.symm t, by simpa [hT'] using ht, by simp⟩
          obtain ⟨q, hq, hqx⟩ := h2
          have : e.symm x = q := by rw [← hqx]; simp
          rwa [this]
        exact this
    have hEq : Ideal.span ((Ideal.span {e.symm φ} :
        Set (MvPolynomial (Fin n) (R ⧸ maximalIdeal R))) ∩
        (Algebra.adjoin (R ⧸ maximalIdeal R)
          (T' : Set (MvPolynomial (Fin n) (R ⧸ maximalIdeal R))) :
          Set (MvPolynomial (Fin n) (R ⧸ maximalIdeal R)))) = Ideal.span {e.symm φ} :=
      le_antisymm (Ideal.span_le.mpr fun x hx => hx.1)
        (Ideal.span_le.mpr (by rw [Set.singleton_subset_iff]; exact hmem'))
    have hpA := (span_inter_adjoin_eq_span_iff hp hT'1).mp hEq
    have hφA : φ ∈ (Algebra.adjoin (R ⧸ maximalIdeal R)
        (T' : Set (MvPolynomial (Fin n) (R ⧸ maximalIdeal R)))).map
          (e : MvPolynomial (Fin n) (R ⧸ maximalIdeal R) →ₐ[R ⧸ maximalIdeal R] _) :=
      ⟨e.symm φ, hpA, by simp⟩
    rw [AlgHom.map_adjoin] at hφA
    exact Algebra.adjoin_mono (by rintro _ ⟨t, ht, rfl⟩; exact ht) hφA
  · rintro ⟨hT, hφT⟩
    refine ⟨hT, le_antisymm (Ideal.span_le.mpr fun x hx => hx.1) ?_⟩
    rw [Ideal.span_le, Set.singleton_subset_iff]
    exact Ideal.subset_span ⟨Ideal.mem_span_singleton_self φ, hφT⟩

/-- The initial form of `f` lies in `k[T]` (Definition 10*, p. 251). -/
theorem initialForm_mem_adjoin_tauZSubmodule (f : R) :
    initialForm (maximalIdeal R) f ∈ Algebra.adjoin (R ⧸ maximalIdeal R)
      (tauZSubmodule R (fun _ : Fin 1 => f) : Set (AssocGraded (maximalIdeal R))) :=
  ((isTauZSubmodule_singleton_iff f _).mp (tauZSubmodule_spec R (fun _ : Fin 1 => f))).2

/-- ... and in `k[T*]`. -/
theorem initialForm_mem_adjoin_tauZSubmoduleStar {r : ℕ} (z : Fin r → R) (f : R) :
    initialForm (maximalIdeal R) f ∈ Algebra.adjoin (R ⧸ maximalIdeal R)
      (tauZSubmoduleStar R z (fun _ : Fin 1 => f) : Set (AssocGraded (maximalIdeal R))) :=
  Algebra.adjoin_mono (by exact_mod_cast le_sup_left) (initialForm_mem_adjoin_tauZSubmodule f)

/-- Minimality of `T`: a space `T'` of linear forms with `φ ∈ k[T']` contains `T`. -/
theorem tauZSubmodule_le_of_mem_adjoin (f : R)
    (T' : Submodule (R ⧸ maximalIdeal R) (AssocGraded (maximalIdeal R)))
    (hT' : T' ≤ AssocGraded.homogeneous (maximalIdeal R) 1)
    (h : initialForm (maximalIdeal R) f ∈ Algebra.adjoin (R ⧸ maximalIdeal R)
      (T' : Set (AssocGraded (maximalIdeal R)))) :
    tauZSubmodule R (fun _ : Fin 1 => f) ≤ T' :=
  sInf_le ((isTauZSubmodule_singleton_iff f T').mpr ⟨hT', h⟩)

open Classical in
/-- `τ_{(z)}(f) = 0` as soon as the initial form of `f` lies in `k[Z₁, …, Z_r]` (an injective
system extending to a regular system of parameters): then `T ⊆ ⟨Z⟩`, `T* = ⟨Z⟩`. -/
theorem tauZ_eq_zero_of_initialForm_mem_adjoin {r : ℕ} {z : Fin r → R}
    (hinj : Function.Injective z) (hz : ExtendsToRSOP R (Finset.image z Finset.univ)) (f : R)
    (h : initialForm (maximalIdeal R) f ∈ Algebra.adjoin (R ⧸ maximalIdeal R)
      (Set.range (frameForm z))) :
    tauZ R z (fun _ : Fin 1 => f) = 0 := by
  obtain ⟨hli, hord⟩ := linearIndependent_frameForm hinj hz
  have hle : Submodule.span (R ⧸ maximalIdeal R) (Set.range (frameForm z)) ≤
      AssocGraded.homogeneous (maximalIdeal R) 1 := by
    rw [Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    rw [frameForm, initialForm_eq_mk _ (hord j)]
    exact AssocGraded.mk_mem_homogeneous _ _
  have h1 : tauZSubmodule R (fun _ : Fin 1 => f) ≤
      Submodule.span (R ⧸ maximalIdeal R) (Set.range (frameForm z)) :=
    tauZSubmodule_le_of_mem_adjoin f _ hle
      (Algebra.adjoin_mono Submodule.subset_span h)
  have h2 : tauZSubmoduleStar R z (fun _ : Fin 1 => f) =
      Submodule.span (R ⧸ maximalIdeal R) (Set.range (frameForm z)) :=
    sup_eq_right.mpr h1
  have h3 := finrank_tauZSubmoduleStar_eq hinj hz (fun _ : Fin 1 => f)
  rw [h2, finrank_span_eq_card hli, Fintype.card_fin] at h3
  omega

end Singleton

end Hironaka
