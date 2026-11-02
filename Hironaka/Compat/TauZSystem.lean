/-
Copyright (c) 2026 Daattavya Aggarwal, Minhyong Kim, Oisin Kim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daattavya Aggarwal, Minhyong Kim, Oisin Kim
-/
module

public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Architect
public import Hironaka.Ch3.Frames

/-!
# Compatibility layer: the integer `τ_{(z)}` when the system `(z)` is lengthened (Ch. III, §10)

In the proof of Lemma 25 (p. 270) the paper replaces the system `(z) = (z_1, …, z_r)` by
`(z, w) = (z_1, …, z_r, w)` for a member `w = x_1` of a regular system of `τ_{(z)}`-parameters of
`R` for `f`, and says: "The property (2) is clear from our selection of `w`", that is
`τ_{(z,w)}(f) = τ_{(z)}(f) - 1`.  This file proves the statement behind it (Definition 10*,
p. 251): the `k`-module `T*` of `(f)` does not change when `(z)` is replaced by `(z, w)` with
`in(w) ∈ T*`, so that the integer `τ` drops by one.  Used for Lemma 25 and Theorem 9
(Ch. III, pp. 269–274).

It also proves the facts on the classes `Z_j` of the members of `(z)` which the paper uses without
comment in Definition 10* (p. 251): they are linearly independent in `gr¹_M(R)`
(`linearIndependent_frameForm`), each `z_j` has order `1`, and `rank T* = τ_{(z)}(f) + r`
(`finrank_tauZSubmoduleStar_eq`).
-/

@[expose] public section

open IsLocalRing

namespace Hironaka

universe u

section TauZSnoc

variable {R : Type u} [CommRing R] [IsRegularLocalRing R] {r : ℕ}

/-- The `k`-span of the initial forms of the system `(z_1, …, z_r, w)` is that of `(z)` together
with the initial form of `w`. -/
theorem span_range_frameForm_snoc (z : Fin r → R) (w : R) :
    Submodule.span (R ⧸ maximalIdeal R) (Set.range (frameForm (Fin.snoc z w : Fin (r + 1) → R))) =
      Submodule.span (R ⧸ maximalIdeal R) (Set.range (frameForm z)) ⊔
        Submodule.span (R ⧸ maximalIdeal R) {initialForm (maximalIdeal R) w} := by
  have hrange : Set.range (frameForm (Fin.snoc z w : Fin (r + 1) → R)) =
      Set.range (frameForm z) ∪ {initialForm (maximalIdeal R) w} := by
    ext x
    simp only [Set.mem_range, Set.mem_union, Set.mem_singleton_iff]
    constructor
    · rintro ⟨j, rfl⟩
      refine Fin.lastCases ?_ (fun j => ?_) j
      · right; simp [frameForm]
      · left; exact ⟨j, by simp [frameForm]⟩
    · rintro (⟨j, rfl⟩ | rfl)
      · exact ⟨j.castSucc, by simp [frameForm]⟩
      · exact ⟨Fin.last r, by simp [frameForm]⟩
  rw [hrange, Submodule.span_union]

/-- `T*` of `(f)` for `(z)` is contained in `T*` for `(z, w)`. -/
theorem tauZSubmoduleStar_le_snoc {i : ℕ} (z : Fin r → R) (f : Fin i → R) (w : R) :
    tauZSubmoduleStar R z f ≤ tauZSubmoduleStar R (Fin.snoc z w : Fin (r + 1) → R) f := by
  unfold tauZSubmoduleStar
  rw [span_range_frameForm_snoc, ← sup_assoc]
  exact le_sup_left

/-- `T*` of `(f)` does not change when `(z)` is replaced by `(z, w)` with `in(w) ∈ T*`. -/
theorem tauZSubmoduleStar_snoc_eq_of_mem {i : ℕ} (z : Fin r → R) (f : Fin i → R) (w : R)
    (hw : initialForm (maximalIdeal R) w ∈ tauZSubmoduleStar R z f) :
    tauZSubmoduleStar R (Fin.snoc z w : Fin (r + 1) → R) f = tauZSubmoduleStar R z f := by
  refine le_antisymm ?_ (tauZSubmoduleStar_le_snoc z f w)
  unfold tauZSubmoduleStar
  rw [span_range_frameForm_snoc, ← sup_assoc]
  refine sup_le le_rfl ?_
  exact (Submodule.span_singleton_le_iff_mem _ _).mpr hw

/-- `τ_{(z,w)}(f) = τ_{(z)}(f) - 1` when the initial form of `w` lies in `T*` of `(f)`
(Lemma 25, p. 270: "The property (2) is clear from our selection of `w`"). -/
theorem tauZ_snoc_eq_sub_one_of_mem {i : ℕ} (z : Fin r → R) (f : Fin i → R) (w : R)
    (hw : initialForm (maximalIdeal R) w ∈ tauZSubmoduleStar R z f) :
    tauZ R (Fin.snoc z w : Fin (r + 1) → R) f = tauZ R z f - 1 := by
  unfold tauZ
  rw [tauZSubmoduleStar_snoc_eq_of_mem z f w hw, Nat.sub_sub]

end TauZSnoc


section LinearIndependence


variable {R : Type u} [CommRing R] [IsRegularLocalRing R] {r : ℕ}

omit [IsRegularLocalRing R] in
/-- If `a ∈ Iⁿ` has non-zero class in `Iⁿ/Iⁿ⁺¹`, then `ν_I(a) = n` and its initial form is that
class. -/
theorem ordElem_eq_of_mk_ne_zero_aux {A : Type*} [CommRing A] (I : Ideal A) {n : ℕ} {a : A}
    (ha : a ∈ I ^ n) (h : AssocGraded.mk I n a ha ≠ 0) :
    Ideal.ordElem I a = n ∧ initialForm I a = AssocGraded.mk I n a ha := by
  have hn : Ideal.ordElem I a = n := by
    refine le_antisymm (Ideal.ordElem_le_of_notMem fun h' => h ?_) (Ideal.le_ordElem ha)
    exact (AssocGraded.mk_eq_zero_iff I ha).mpr h'
  exact ⟨hn, initialForm_eq_mk I hn⟩

open Classical in
/-- The classes `Z_j` of an injective system `(z_1, …, z_r)` which can be extended to a regular
system of parameters are linearly independent in `gr¹_M(R) = M/M²` ("Then `(Z) = (Z_1, …, Z_r)`
is a system of linearly independent linear forms in `gr¹_M(R)`", Definition 10*, p. 251), and
each `z_j` has order `1`. -/
theorem linearIndependent_frameForm {z : Fin r → R} (hinj : Function.Injective z)
    (hz : ExtendsToRSOP R (Finset.image z Finset.univ)) :
    LinearIndependent (R ⧸ maximalIdeal R) (frameForm z) ∧
      ∀ j, Ideal.ordElem (maximalIdeal R) (z j) = ((1 : ℕ) : ℕ∞) := by
  obtain ⟨s, hts, hs⟩ := hz
  set t : Finset R := s \ Finset.image z Finset.univ with htdef
  -- enumerate `s` with the members of `z` first
  let u : Fin t.card → R := fun i => (t.equivFin.symm i : R)
  have huinj : Function.Injective u := Subtype.val_injective.comp t.equivFin.symm.injective
  have hurange : Set.range u = (t : Set R) := by
    ext y
    constructor
    · rintro ⟨i, rfl⟩
      exact (t.equivFin.symm i).2
    · intro hy
      exact ⟨t.equivFin ⟨y, hy⟩, by simp [u]⟩
  set y : Fin (r + t.card) → R := Fin.append z u with hydef
  have hzmem : ∀ i, z i ∈ Finset.image z Finset.univ := fun i =>
    Finset.mem_image_of_mem z (Finset.mem_univ i)
  have hunot : ∀ j, u j ∉ Finset.image z Finset.univ := fun j =>
    (Finset.mem_sdiff.mp (t.equivFin.symm j).2).2
  have hyinj : Function.Injective y := by
    intro a b hab
    induction a using Fin.addCases with
    | left i =>
      induction b using Fin.addCases with
      | left j => rw [hydef, Fin.append_left, Fin.append_left] at hab; rw [hinj hab]
      | right j =>
        rw [hydef, Fin.append_left, Fin.append_right] at hab
        exact absurd (hab ▸ hzmem i) (hunot j)
    | right i =>
      induction b using Fin.addCases with
      | left j =>
        rw [hydef, Fin.append_left, Fin.append_right] at hab
        exact absurd (hab ▸ hzmem j) (hunot i)
      | right j => rw [hydef, Fin.append_right, Fin.append_right] at hab; rw [huinj hab]
  have hyrange : Set.range y = (s : Set R) := by
    ext x
    constructor
    · rintro ⟨a, rfl⟩
      induction a using Fin.addCases with
      | left i =>
        rw [hydef, Fin.append_left]
        exact hts (hzmem i)
      | right i =>
        rw [hydef, Fin.append_right]
        exact (Finset.mem_sdiff.mp (t.equivFin.symm i).2).1
    · intro hx
      by_cases hxz : x ∈ Finset.image z Finset.univ
      · obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hxz
        exact ⟨Fin.castAdd _ i, by rw [hydef, Fin.append_left]⟩
      · have hxt : x ∈ t := Finset.mem_sdiff.mpr ⟨hx, hxz⟩
        refine ⟨Fin.natAdd r (t.equivFin ⟨x, hxt⟩), ?_⟩
        rw [hydef, Fin.append_right]
        simp [u]
  have hspan : Ideal.span (Set.range y) = maximalIdeal R := by rw [hyrange]; exact hs.1
  have hcardy : r + t.card = s.card := by
    have h1 : t.card + (Finset.image z Finset.univ).card = s.card :=
      Finset.card_sdiff_add_card_eq_card hts
    rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin] at h1
    omega
  have hcard : ((r + t.card : ℕ) : WithBot ℕ∞) = ringKrullDim R := by
    rw [hcardy]; exact hs.2
  have hymem : ∀ i, y i ∈ maximalIdeal R ^ 1 := fun i => by
    rw [pow_one, ← hspan]; exact Ideal.subset_span ⟨i, rfl⟩
  have hbij := assocGraded_maximalIdeal_aeval_bijective hspan hcard hymem
  -- the classes `[y_i]` are the images of the variables
  have hli : LinearIndependent (R ⧸ maximalIdeal R)
      (fun i => AssocGraded.mk (maximalIdeal R) 1 (y i) (hymem i)) := by
    have := (MvPolynomial.linearIndependent_X (Fin (r + t.card)) (R ⧸ maximalIdeal R)).map'
      (MvPolynomial.aeval (R := R ⧸ maximalIdeal R)
        fun i => AssocGraded.mk (maximalIdeal R) 1 (y i) (hymem i)).toLinearMap
      (LinearMap.ker_eq_bot.mpr hbij.1)
    convert this using 1
    ext i
    simp
  have hne : ∀ j, AssocGraded.mk (maximalIdeal R) 1 (z j)
      (by simpa [hydef] using hymem (Fin.castAdd _ j)) ≠ 0 := by
    intro j
    have := hli.ne_zero (Fin.castAdd _ j)
    simpa [hydef] using this
  have hord : ∀ j, Ideal.ordElem (maximalIdeal R) (z j) = ((1 : ℕ) : ℕ∞) := fun j =>
    (ordElem_eq_of_mk_ne_zero_aux _ _ (hne j)).1
  refine ⟨?_, hord⟩
  have hfF : ∀ j, frameForm z j = AssocGraded.mk (maximalIdeal R) 1 (z j)
      (by simpa [hydef] using hymem (Fin.castAdd _ j)) := fun j =>
    (ordElem_eq_of_mk_ne_zero_aux _ _ (hne j)).2
  have hcomp := hli.comp (Fin.castAdd t.card) (Fin.castAdd_injective r t.card)
  convert hcomp using 1
  ext j
  rw [hfF j]
  simp [hydef]


end LinearIndependence

section Rank

variable {R : Type u} [CommRing R] [IsRegularLocalRing R] {r : ℕ}

/-- `gr¹_M(R)` is a finite-dimensional `k`-module. -/
theorem finite_homogeneous_one :
    Module.Finite (R ⧸ maximalIdeal R) (AssocGraded.homogeneous (maximalIdeal R) 1) := by
  refine Module.Finite.iff_fg.mpr ?_
  rw [AssocGraded.homogeneous, LinearMap.range_eq_map]
  exact Module.Finite.fg_top.map _

/-- `T*` lies in `gr¹_M(R)` when the members of `(z)` have order one. -/
theorem tauZSubmoduleStar_le_homogeneous_one {i : ℕ} {z : Fin r → R} {f : Fin i → R}
    (hz : ∀ j, Ideal.ordElem (maximalIdeal R) (z j) = ((1 : ℕ) : ℕ∞)) :
    tauZSubmoduleStar R z f ≤ AssocGraded.homogeneous (maximalIdeal R) 1 := by
  refine sup_le (tauZSubmodule_spec R f).1 (Submodule.span_le.mpr ?_)
  rintro _ ⟨j, rfl⟩
  have hmem : z j ∈ maximalIdeal R ^ 1 := Ideal.mem_pow_of_ordElem (hz j)
  rw [frameForm, initialForm_eq_mk _ (hz j)]
  exact AssocGraded.mk_mem_homogeneous _ _

open Classical in
/-- `rank T* = τ_{(z)}(f) + r` for an injective system `(z)` which can be extended to a regular
system of parameters (Definition 10*: "the rank of `T*` minus `r`", the paper's `rank T* ≥ r`). -/
theorem finrank_tauZSubmoduleStar_eq {i : ℕ} {z : Fin r → R} (hinj : Function.Injective z)
    (hz : ExtendsToRSOP R (Finset.image z Finset.univ)) (f : Fin i → R) :
    Module.finrank (R ⧸ maximalIdeal R) (tauZSubmoduleStar R z f) = tauZ R z f + r := by
  obtain ⟨hli, hord⟩ := linearIndependent_frameForm hinj hz
  have := finite_homogeneous_one (R := R)
  have hle := tauZSubmoduleStar_le_homogeneous_one (f := f) hord
  have : Module.Finite (R ⧸ maximalIdeal R) (tauZSubmoduleStar R z f) :=
    Module.Finite.of_injective (Submodule.inclusion hle) (Submodule.inclusion_injective hle)
  have hfin : Module.Finite (R ⧸ maximalIdeal R)
      ↥(tauZSubmodule R f ⊔ Submodule.span (R ⧸ maximalIdeal R) (Set.range (frameForm z))) :=
    this
  have h1 : Module.finrank (R ⧸ maximalIdeal R)
      (Submodule.span (R ⧸ maximalIdeal R) (Set.range (frameForm z))) = r := by
    rw [finrank_span_eq_card hli, Fintype.card_fin]
  have hsp : Submodule.span (R ⧸ maximalIdeal R) (Set.range (frameForm z)) ≤
      tauZSubmoduleStar R z f := le_sup_right
  have h3 : Module.finrank (R ⧸ maximalIdeal R)
      (Submodule.span (R ⧸ maximalIdeal R) (Set.range (frameForm z))) ≤
      Module.finrank (R ⧸ maximalIdeal R) (tauZSubmoduleStar R z f) :=
    Submodule.finrank_mono hsp
  have h2 : r ≤ Module.finrank (R ⧸ maximalIdeal R) (tauZSubmoduleStar R z f) :=
    le_of_eq_of_le h1.symm h3
  unfold tauZ
  omega

end Rank

section StarGeneral

variable {R : Type u} [CommRing R] [IsRegularLocalRing R] {r : ℕ}

/-- Minimality of `T` (Definition 10*): a space `T'` of linear forms such that the initial form of
every `f_j` lies in `k[T']` contains `T`. -/
theorem tauZSubmodule_le_of_forall_mem_adjoin {i : ℕ} (f : Fin i → R)
    (T' : Submodule (R ⧸ maximalIdeal R) (AssocGraded (maximalIdeal R)))
    (hT' : T' ≤ AssocGraded.homogeneous (maximalIdeal R) 1)
    (h : ∀ j, initialForm (maximalIdeal R) (f j) ∈ Algebra.adjoin (R ⧸ maximalIdeal R)
      (T' : Set (AssocGraded (maximalIdeal R)))) :
    tauZSubmodule R f ≤ T' := by
  refine sInf_le ⟨hT', le_antisymm ?_ ?_⟩
  · rw [Ideal.span_le]
    intro x hx
    exact hx.1
  · rw [Ideal.span_le]
    rintro _ ⟨j, rfl⟩
    exact Ideal.subset_span ⟨Ideal.subset_span ⟨j, rfl⟩, h j⟩

/-- `T*` is a finite-dimensional `k`-space when the members of `(z)` have order one. -/
theorem finite_tauZSubmoduleStar {i : ℕ} {z : Fin r → R}
    (hz : ∀ j, Ideal.ordElem (maximalIdeal R) (z j) = ((1 : ℕ) : ℕ∞)) (f : Fin i → R) :
    Module.Finite (R ⧸ maximalIdeal R) (tauZSubmoduleStar R z f) := by
  have := finite_homogeneous_one (R := R)
  have hle := tauZSubmoduleStar_le_homogeneous_one (f := f) hz
  exact Module.Finite.of_injective (Submodule.inclusion hle) (Submodule.inclusion_injective hle)

/-- For an empty system `(z)`, `τ(f)` is the rank of `T`. -/
theorem tauZ_empty {i : ℕ} (f : Fin i → R) :
    tauZ R (![] : Fin 0 → R) f = Module.finrank (R ⧸ maximalIdeal R) (tauZSubmodule R f) := by
  have h0 : Set.range (frameForm (![] : Fin 0 → R)) = ∅ := Set.range_eq_empty _
  unfold tauZ tauZSubmoduleStar
  rw [h0, Submodule.span_empty, sup_bot_eq]
  simp

open Classical in
/-- If `τ_{(z)}(f) = 0`, then `T* = ⟨Z₁, …, Z_r⟩`. -/
theorem tauZSubmoduleStar_eq_span_of_tauZ_eq_zero {i : ℕ} {z : Fin r → R}
    (hinj : Function.Injective z) (hz : ExtendsToRSOP R (Finset.image z Finset.univ))
    (f : Fin i → R) (h : tauZ R z f = 0) :
    tauZSubmoduleStar R z f = Submodule.span (R ⧸ maximalIdeal R) (Set.range (frameForm z)) := by
  obtain ⟨hli, hord⟩ := linearIndependent_frameForm hinj hz
  have h3 := finrank_tauZSubmoduleStar_eq hinj hz f
  have hfin := finite_tauZSubmoduleStar hord f
  have hle : Submodule.span (R ⧸ maximalIdeal R) (Set.range (frameForm z)) ≤
      tauZSubmoduleStar R z f := le_sup_right
  let _ : Field (R ⧸ maximalIdeal R) := Ideal.Quotient.field _
  have : FiniteDimensional (R ⧸ maximalIdeal R) (tauZSubmoduleStar R z f) := hfin
  refine (Submodule.eq_of_le_of_finrank_eq hle ?_).symm
  rw [finrank_span_eq_card hli, Fintype.card_fin, h3, h]
  simp

end StarGeneral

section SnocStar

variable {R : Type u} [CommRing R] [IsRegularLocalRing R] {r : ℕ}

omit [CommRing R] [IsRegularLocalRing R] in
/-- The prefix `(z)` of an injective system `(z, w)` is injective. -/
theorem injective_of_injective_snoc {z : Fin r → R} {w : R}
    (hinj : Function.Injective (Fin.snoc z w : Fin (r + 1) → R)) : Function.Injective z := by
  intro a b hab
  apply Fin.castSucc_injective r
  apply hinj
  simpa using hab

open Classical in
/-- The prefix `(z)` of a system `(z, w)` which can be extended to a regular system of parameters
can be extended to one. -/
theorem extendsToRSOP_of_snoc {z : Fin r → R} {w : R}
    (hz : ExtendsToRSOP R (Finset.image (Fin.snoc z w : Fin (r + 1) → R) Finset.univ)) :
    ExtendsToRSOP R (Finset.image z Finset.univ) := by
  obtain ⟨s, hs, hsr⟩ := hz
  refine ⟨s, fun x hx => hs ?_, hsr⟩
  obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hx
  exact Finset.mem_image.mpr ⟨j.castSucc, Finset.mem_univ _, by simp⟩

open Classical in
/-- `τ_{(z,w)}(f) = 0` as soon as `τ_{(z)}(f) = 0`, for a system `(z, w)` which is independent
modulo `M²` (then `T* = ⟨Z₁, …, Z_r, W⟩` has rank `r + 1`). -/
theorem tauZ_snoc_eq_zero_of_tauZ_eq_zero {i : ℕ} {z : Fin r → R} {w : R}
    (hinj : Function.Injective (Fin.snoc z w : Fin (r + 1) → R))
    (hz : ExtendsToRSOP R (Finset.image (Fin.snoc z w : Fin (r + 1) → R) Finset.univ))
    (f : Fin i → R) (h : tauZ R z f = 0) :
    tauZ R (Fin.snoc z w : Fin (r + 1) → R) f = 0 := by
  have hstar := tauZSubmoduleStar_eq_span_of_tauZ_eq_zero (injective_of_injective_snoc hinj)
    (extendsToRSOP_of_snoc hz) f h
  obtain ⟨hli, -⟩ := linearIndependent_frameForm hinj hz
  have hZle : Submodule.span (R ⧸ maximalIdeal R) (Set.range (frameForm z)) ≤
      Submodule.span (R ⧸ maximalIdeal R)
        (Set.range (frameForm (Fin.snoc z w : Fin (r + 1) → R))) := by
    rw [span_range_frameForm_snoc]
    exact le_sup_left
  have heq : tauZSubmoduleStar R (Fin.snoc z w : Fin (r + 1) → R) f =
      Submodule.span (R ⧸ maximalIdeal R)
        (Set.range (frameForm (Fin.snoc z w : Fin (r + 1) → R))) := by
    refine le_antisymm (sup_le ?_ le_rfl) le_sup_right
    exact (le_sup_left.trans hstar.le).trans hZle
  have h3 := finrank_tauZSubmoduleStar_eq hinj hz f
  rw [heq, finrank_span_eq_card hli, Fintype.card_fin] at h3
  omega

open Classical in
/-- If `τ_{(z,w)}(f) = τ_{(z)}(f) - 1` with `τ_{(z)}(f) ≥ 1`, the initial form of `w` lies in `T*`
(the converse of `tauZ_snoc_eq_sub_one_of_mem`). -/
theorem initialForm_mem_tauZSubmoduleStar_of_tauZ_snoc {i : ℕ} {z : Fin r → R} {w : R}
    (hinj : Function.Injective (Fin.snoc z w : Fin (r + 1) → R))
    (hz : ExtendsToRSOP R (Finset.image (Fin.snoc z w : Fin (r + 1) → R) Finset.univ))
    (f : Fin i → R) (hτ : 1 ≤ tauZ R z f)
    (h : tauZ R (Fin.snoc z w : Fin (r + 1) → R) f = tauZ R z f - 1) :
    initialForm (maximalIdeal R) w ∈ tauZSubmoduleStar R z f := by
  obtain ⟨-, hord⟩ := linearIndependent_frameForm hinj hz
  have h1 := finrank_tauZSubmoduleStar_eq (injective_of_injective_snoc hinj)
    (extendsToRSOP_of_snoc hz) f
  have h2 := finrank_tauZSubmoduleStar_eq hinj hz f
  let _ : Field (R ⧸ maximalIdeal R) := Ideal.Quotient.field _
  have hfin : FiniteDimensional (R ⧸ maximalIdeal R)
      (tauZSubmoduleStar R (Fin.snoc z w : Fin (r + 1) → R) f) :=
    finite_tauZSubmoduleStar hord f
  have heq : tauZSubmoduleStar R z f =
      tauZSubmoduleStar R (Fin.snoc z w : Fin (r + 1) → R) f :=
    Submodule.eq_of_le_of_finrank_eq (tauZSubmoduleStar_le_snoc z f w) (by omega)
  rw [heq]
  have hmem : initialForm (maximalIdeal R) w ∈ Submodule.span (R ⧸ maximalIdeal R)
      (Set.range (frameForm (Fin.snoc z w : Fin (r + 1) → R))) :=
    Submodule.subset_span ⟨Fin.last r, by simp [frameForm]⟩
  exact Submodule.mem_sup_right hmem

end SnocStar

end Hironaka
