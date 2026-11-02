/-
Copyright (c) 2026 Daattavya Aggarwal, Minhyong Kim, Oisin Kim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daattavya Aggarwal, Minhyong Kim, Oisin Kim
-/
module

public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Hironaka.Ch3.PermissibleEffects
public import Hironaka.Compat.TauZSystem
public import Hironaka.Compat.TauZSingleton

/-!
# Regular systems of `τ_{(z)}`-parameters through a given vector

Definition 10* (p. 251): a regular system `(x_1, …, x_τ)` of `τ_{(z)}`-parameters of `R` for `f`
is a system of elements of `M` whose classes in `gr¹_M(R)` and `Z_1, …, Z_r` generate `T*`.  If the
class of an element `w ∈ M` lies in `T*` but not in `⟨Z_1, …, Z_r⟩`, `w` is one of the `x_i` for a
suitable system (`exists_isRegularSystemOfTauZParameters_of_mem`); the other `x_i` can be taken in
any ideal `𝔞` of `R` whose classes in `gr¹_M(R)` contain `T*`.  This is used for Lemma 24
(pp. 268--269), which needs `P ⊇ (z_1, …, z_r, y_1, …, y_τ)R` for a prime center `P` with `ν_P(f) = ν_M(f)`
(`tauZSubmoduleStar_le_classSubmodule`).
-/

@[expose] public section

open IsLocalRing

namespace Hironaka

universe u

section LinearAlgebra

/-- A vector `W` of a finite-dimensional subspace `U` which does not lie in a subspace `Z ≤ U` can
be completed to a family of `dim U - dim Z` vectors of `U` which span `U` together with `Z`. -/
theorem exists_family_span_sup_eq_of_notMem {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    {U Z : Submodule K V} [FiniteDimensional K U] (hZU : Z ≤ U) {W : V} (hWU : W ∈ U)
    (hWZ : W ∉ Z) :
    ∃ c : Fin (Module.finrank K U - Module.finrank K Z) → V, (∀ i, c i ∈ U) ∧ (∃ i, c i = W) ∧
      Z ⊔ Submodule.span K (Set.range c) = U := by
  classical
  have hZfin : FiniteDimensional K Z := Submodule.finiteDimensional_of_le hZU
  set Z' : Submodule K V := Z ⊔ Submodule.span K {W} with hZ'
  have hZ'U : Z' ≤ U := sup_le hZU ((Submodule.span_singleton_le_iff_mem _ _).mpr hWU)
  have hZ'fin : FiniteDimensional K Z' := Submodule.finiteDimensional_of_le hZ'U
  have hdim : Module.finrank K Z' = Module.finrank K Z + 1 := by
    have h1 : Z ⊓ Submodule.span K {W} = ⊥ := by
      rw [Submodule.eq_bot_iff]
      intro x hx
      obtain ⟨hxZ, hxW⟩ := Submodule.mem_inf.mp hx
      obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hxW
      by_cases ha : a = 0
      · simp [ha]
      · exact absurd ((Z.smul_mem_iff ha).mp hxZ) hWZ
    have h2 := Submodule.finrank_sup_add_finrank_inf_eq Z (Submodule.span K {W})
    have hW0 : W ≠ 0 := by rintro rfl; exact hWZ Z.zero_mem
    rw [h1, finrank_bot, add_zero, finrank_span_singleton hW0] at h2
    omega
  obtain ⟨C₀, hC₀⟩ := Submodule.exists_isCompl (Z'.comap U.subtype)
  set m := Module.finrank K C₀ with hm
  have hZ'comap : Module.finrank K (Z'.comap U.subtype) = Module.finrank K Z' :=
    LinearEquiv.finrank_eq (Submodule.comapSubtypeEquivOfLe hZ'U)
  have hsum : Module.finrank K (Z'.comap U.subtype) + m = Module.finrank K U :=
    Submodule.finrank_add_eq_of_isCompl hC₀
  have hd : Module.finrank K U - Module.finrank K Z = m + 1 := by omega
  let bC := Module.finBasis K C₀
  let c0 : Fin (m + 1) → V := Fin.cons W (fun i => (((bC i : C₀) : U) : V))
  refine ⟨fun i => c0 (Fin.cast hd i), fun i => ?_, ⟨Fin.cast hd.symm 0, by simp [c0]⟩, ?_⟩
  · have hi : ∀ j : Fin (m + 1), c0 j ∈ U := by
      intro j
      refine Fin.cases ?_ (fun j => ?_) j
      · exact hWU
      · exact ((bC j : C₀) : U).2
    exact hi _
  · have hsurj : Function.Surjective (Fin.cast hd) := fun j => ⟨Fin.cast hd.symm j, by ext; simp⟩
    have hrange : Set.range (fun i => c0 (Fin.cast hd i)) = Set.range c0 :=
      hsurj.range_comp c0
    rw [hrange]
    have hr0 : Set.range c0 = insert W (Set.range fun i : Fin m => (((bC i : C₀) : U) : V)) :=
      Fin.range_cons W _
    have hbasis : Submodule.span K (Set.range fun i : Fin m => (((bC i : C₀) : U) : V)) =
        C₀.map U.subtype := by
      have h1 : (Set.range fun i : Fin m => (((bC i : C₀) : U) : V)) =
          (U.subtype ∘ₗ C₀.subtype) '' Set.range bC := by
        rw [← Set.range_comp]
        rfl
      rw [h1, Submodule.span_image, bC.span_eq, Submodule.map_top, LinearMap.range_comp,
        Submodule.range_subtype]
    rw [hr0, Submodule.span_insert, hbasis, ← sup_assoc, ← hZ']
    refine le_antisymm (sup_le hZ'U (Submodule.map_subtype_le U C₀)) ?_
    intro v hv
    have hvU : (⟨v, hv⟩ : U) ∈ (Z'.comap U.subtype) ⊔ C₀ := by rw [hC₀.sup_eq_top]; trivial
    obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp hvU
    refine Submodule.mem_sup.mpr ⟨(a : V), ha, (b : V), ⟨b, hb, rfl⟩, ?_⟩
    have := congrArg (fun x : U => (x : V)) hab
    simpa using this

end LinearAlgebra


section ClassSubmodule

noncomputable section

variable {R : Type u} [CommRing R] [IsLocalRing R]

/-- The classes in `gr¹_M(R) = M/M²` of the elements of an ideal `𝔞`. -/
def classSet (𝔞 : Ideal R) : Set (AssocGraded (maximalIdeal R)) :=
  {v | ∃ (a : R) (ha : a ∈ maximalIdeal R ^ 1), a ∈ 𝔞 ∧ AssocGraded.mk (maximalIdeal R) 1 a ha = v}

/-- The `k`-span of the classes of the elements of `𝔞`. -/
def classSubmodule (𝔞 : Ideal R) :
    Submodule (R ⧸ maximalIdeal R) (AssocGraded (maximalIdeal R)) :=
  Submodule.span (R ⧸ maximalIdeal R) (classSet 𝔞)

/-- Every element of `classSubmodule 𝔞` is the class of an element of `𝔞`. -/
theorem exists_lift_of_mem_classSubmodule {𝔞 : Ideal R} {v : AssocGraded (maximalIdeal R)}
    (hv : v ∈ classSubmodule 𝔞) :
    ∃ (a : R) (ha : a ∈ maximalIdeal R ^ 1), a ∈ 𝔞 ∧
      AssocGraded.mk (maximalIdeal R) 1 a ha = v := by
  induction hv using Submodule.span_induction with
  | mem v hv => exact hv
  | zero => exact ⟨0, zero_mem _, zero_mem _, map_zero (AssocGraded.mkLinear _ 1)⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, ha, ha𝔞, rfl⟩ := hx
    obtain ⟨b, hb, hb𝔞, rfl⟩ := hy
    exact ⟨a + b, add_mem ha hb, add_mem ha𝔞 hb𝔞, AssocGraded.mk_add (maximalIdeal R) 1 a b ha hb⟩
  | smul c x _ hx =>
    obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective c
    obtain ⟨a, ha, ha𝔞, rfl⟩ := hx
    exact ⟨s * a, Ideal.mul_mem_left _ s ha, 𝔞.mul_mem_left s ha𝔞,
      (AssocGraded.smul_mk _ _ s a ha).symm⟩

theorem classSet_subset_classSubmodule (𝔞 : Ideal R) : classSet 𝔞 ⊆ classSubmodule 𝔞 :=
  Submodule.subset_span

theorem classSubmodule_le_homogeneous_one (𝔞 : Ideal R) :
    classSubmodule 𝔞 ≤ AssocGraded.homogeneous (maximalIdeal R) 1 := by
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨a, ha, -, rfl⟩
  exact AssocGraded.mk_mem_homogeneous _ ha

/-- An element of `Pⁿ` has its class in `grⁿ_M(R)` in the algebra generated by the classes of the
elements of `P` (`P ⊆ M`). -/
theorem exists_mk_mem_adjoin_classSubmodule_of_mem_pow (P : Ideal R) (hP : P ≤ maximalIdeal R) :
    ∀ (n : ℕ) (x : R), x ∈ P ^ n → ∃ h : x ∈ maximalIdeal R ^ n,
      AssocGraded.mk (maximalIdeal R) n x h ∈
        Algebra.adjoin (R ⧸ maximalIdeal R)
          (classSubmodule P : Set (AssocGraded (maximalIdeal R))) := by
  intro n
  induction n with
  | zero =>
    intro x _
    refine ⟨by simp, ?_⟩
    rw [AssocGraded.mk_zero_eq_algebraMap]
    exact Subalgebra.algebraMap_mem _ _
  | succ n ih =>
    intro x hx
    rw [pow_succ] at hx
    refine Submodule.mul_induction_on
      (C := fun x => ∃ h : x ∈ maximalIdeal R ^ (n + 1),
        AssocGraded.mk (maximalIdeal R) (n + 1) x h ∈
        Algebra.adjoin (R ⧸ maximalIdeal R)
          (classSubmodule P : Set (AssocGraded (maximalIdeal R)))) hx ?_ ?_
    · intro a ha b hb
      obtain ⟨hMa, hadj⟩ := ih a ha
      have hMb : b ∈ maximalIdeal R ^ 1 := by rw [pow_one]; exact hP hb
      have hb' := classSet_subset_classSubmodule P ⟨b, hMb, hb, rfl⟩
      have hprod := Subalgebra.mul_mem _ hadj (Algebra.subset_adjoin hb')
      rw [AssocGraded.mk_mul_mk] at hprod
      exact ⟨by rw [pow_succ]; exact Ideal.mul_mem_mul hMa (by rwa [pow_one] at hMb), hprod⟩
    · rintro x y ⟨hx, hxa⟩ ⟨hy, hya⟩
      exact ⟨add_mem hx hy, by
        rw [AssocGraded.mk_add (maximalIdeal R) (n + 1) x y hx hy]
        exact Subalgebra.add_mem _ hxa hya⟩


/-- Every element of `gr¹_M(R)` is the class of an element of `M`. -/
theorem homogeneous_one_le_classSubmodule_maximalIdeal :
    AssocGraded.homogeneous (maximalIdeal R) 1 ≤ classSubmodule (maximalIdeal R) := by
  intro v hv
  obtain ⟨y, hy, rfl⟩ := AssocGraded.exists_mk_eq_of_mem_homogeneous _ hv
  exact classSet_subset_classSubmodule _ ⟨y, hy, by rwa [pow_one] at hy, rfl⟩

end

end ClassSubmodule

section Lift

variable {R : Type u} [CommRing R] [IsRegularLocalRing R]

/-- **`T*` lies in the classes of a prime center** (used for Lemma 24): if `z_j ∈ P ⊆ M`, `f ∈ Pⁿ`
and `ν_M(f) = n`, then `in(f) ∈ k[classes of P]`, so `T*` (the span of `T` and the `Z_j`)
consists of classes of elements of `P`. -/
theorem tauZSubmoduleStar_le_classSubmodule {r : ℕ} {z : Fin r → R}
    (hz : ∀ j, Ideal.ordElem (maximalIdeal R) (z j) = ((1 : ℕ) : ℕ∞)) (P : Ideal R)
    (hP : P ≤ maximalIdeal R) (hzP : ∀ j, z j ∈ P) {f : R} {ν : ℕ}
    (hν : Ideal.ordElem (maximalIdeal R) f = ν) (hfP : f ∈ P ^ ν) :
    tauZSubmoduleStar R z (fun _ : Fin 1 => f) ≤ classSubmodule P := by
  obtain ⟨hM, hadj⟩ := exists_mk_mem_adjoin_classSubmodule_of_mem_pow P hP ν f hfP
  have hin : initialForm (maximalIdeal R) f ∈ Algebra.adjoin (R ⧸ maximalIdeal R)
      (classSubmodule P : Set (AssocGraded (maximalIdeal R))) := by
    rw [initialForm_eq_mk _ hν]
    exact hadj
  have hT : tauZSubmodule R (fun _ : Fin 1 => f) ≤ classSubmodule P :=
    tauZSubmodule_le_of_mem_adjoin f _ (classSubmodule_le_homogeneous_one P) hin
  refine sup_le hT (Submodule.span_le.mpr ?_)
  rintro _ ⟨j, rfl⟩
  have hzM : z j ∈ maximalIdeal R ^ 1 := Ideal.mem_pow_of_ordElem (hz j)
  show initialForm (maximalIdeal R) (z j) ∈ classSubmodule P
  rw [initialForm_eq_mk _ (hz j)]
  exact classSet_subset_classSubmodule P ⟨z j, hzM, hzP j, rfl⟩

open Classical in
/-- **Regular systems of `τ_{(z)}`-parameters through a given vector** (Definition 10*, p. 251): if
the initial form of `w` lies in `T*` but not in `⟨Z₁, …, Z_r⟩`, there is a regular system
`(x₁, …, x_τ)` of `τ_{(z)}`-parameters of `R` for `f` with `w` among its members; if `T*` consists
of classes of elements of an ideal `𝔞 ∋ w`, the `x_i` can be taken in `𝔞`. -/
theorem exists_isRegularSystemOfTauZParameters_of_mem {r : ℕ} {z : Fin r → R}
    (hinj : Function.Injective z) (hz : ExtendsToRSOP R (Finset.image z Finset.univ)) {f : R}
    {𝔞 : Ideal R} (hU : tauZSubmoduleStar R z (fun _ : Fin 1 => f) ≤ classSubmodule 𝔞) {w : R}
    (hw𝔞 : w ∈ 𝔞) (hwM : w ∈ maximalIdeal R ^ 1)
    (hW : AssocGraded.mk (maximalIdeal R) 1 w hwM ∈ tauZSubmoduleStar R z (fun _ : Fin 1 => f))
    (hWZ : AssocGraded.mk (maximalIdeal R) 1 w hwM ∉
      Submodule.span (R ⧸ maximalIdeal R) (Set.range (frameForm z))) :
    ∃ x : Fin (tauZ R z (fun _ : Fin 1 => f)) → maximalIdeal R,
      IsRegularSystemOfTauZParameters R z (fun _ : Fin 1 => f) x ∧ (∀ i, (x i : R) ∈ 𝔞) ∧
        ∃ i, (x i : R) = w := by
  let _ : Field (R ⧸ maximalIdeal R) := Ideal.Quotient.field _
  obtain ⟨hli, hord⟩ := linearIndependent_frameForm hinj hz
  have hfin : FiniteDimensional (R ⧸ maximalIdeal R)
      (tauZSubmoduleStar R z (fun _ : Fin 1 => f)) := finite_tauZSubmoduleStar hord _
  have hZU : Submodule.span (R ⧸ maximalIdeal R) (Set.range (frameForm z)) ≤
      tauZSubmoduleStar R z (fun _ : Fin 1 => f) := le_sup_right
  have hrank := finrank_tauZSubmoduleStar_eq hinj hz (fun _ : Fin 1 => f)
  have hZrank : Module.finrank (R ⧸ maximalIdeal R)
      (Submodule.span (R ⧸ maximalIdeal R) (Set.range (frameForm z))) = r := by
    rw [finrank_span_eq_card hli, Fintype.card_fin]
  obtain ⟨c, hcU, ⟨i₀, hi₀⟩, hspan⟩ := exists_family_span_sup_eq_of_notMem hZU hW hWZ
  have hidx : Module.finrank (R ⧸ maximalIdeal R) (tauZSubmoduleStar R z (fun _ : Fin 1 => f)) -
      Module.finrank (R ⧸ maximalIdeal R)
        (Submodule.span (R ⧸ maximalIdeal R) (Set.range (frameForm z))) =
      tauZ R z (fun _ : Fin 1 => f) := by omega
  set c' : Fin (tauZ R z (fun _ : Fin 1 => f)) → AssocGraded (maximalIdeal R) :=
    fun i => c (Fin.cast hidx.symm i) with hc'
  have hsurj : Function.Surjective (Fin.cast hidx.symm :
      Fin (tauZ R z (fun _ : Fin 1 => f)) → _) := fun j => ⟨Fin.cast hidx j, by ext; simp⟩
  have hrange : Set.range c' = Set.range c := hsurj.range_comp c
  have hlift : ∀ i, ∃ (a : R) (ha : a ∈ maximalIdeal R ^ 1), a ∈ 𝔞 ∧
      AssocGraded.mk (maximalIdeal R) 1 a ha = c' i := fun i =>
    exists_lift_of_mem_classSubmodule (hU (hcU _))
  choose a ha ha𝔞 hac using hlift
  set Wv := AssocGraded.mk (maximalIdeal R) 1 w hwM with hWv
  let a' : Fin (tauZ R z (fun _ : Fin 1 => f)) → R := fun i => if c' i = Wv then w else a i
  have ha'M : ∀ i, a' i ∈ maximalIdeal R ^ 1 := fun i => by
    by_cases h : c' i = Wv
    · simp only [a', h, ↓reduceIte]; exact hwM
    · simp only [a', h, ↓reduceIte]; exact ha i
  have ha'𝔞 : ∀ i, a' i ∈ 𝔞 := fun i => by
    by_cases h : c' i = Wv
    · simp only [a', h, ↓reduceIte]; exact hw𝔞
    · simp only [a', h, ↓reduceIte]; exact ha𝔞 i
  have ha'c : ∀ i, AssocGraded.mk (maximalIdeal R) 1 (a' i) (ha'M i) = c' i := fun i => by
    by_cases h : c' i = Wv
    · simp only [a', h, ↓reduceIte]; rfl
    · simp only [a', h, ↓reduceIte]; exact hac i
  refine ⟨fun i => ⟨a' i, by simpa using ha'M i⟩, ?_, fun i => ha'𝔞 i,
    ⟨Fin.cast hidx i₀, ?_⟩⟩
  · show Submodule.span (R ⧸ maximalIdeal R) (Set.range (linearForms R _) ∪
      Set.range (frameForm z)) = _
    have hlf : Set.range (linearForms R (fun i => (⟨a' i, by simpa using ha'M i⟩ :
        maximalIdeal R))) = Set.range c' := by
      refine congrArg Set.range (funext fun i => ?_)
      exact ha'c i
    rw [hlf, hrange, Submodule.span_union, sup_comm]
    exact hspan
  · show a' (Fin.cast hidx i₀) = w
    have : c' (Fin.cast hidx i₀) = Wv := by simp [hc', hi₀, hWv]
    simp only [a', this, ↓reduceIte]

end Lift

end Hironaka
