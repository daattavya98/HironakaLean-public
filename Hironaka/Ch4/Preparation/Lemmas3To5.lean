/-
Copyright (c) 2026 Daattavya Aggarwal, Minhyong Kim, Oisin Kim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daattavya Aggarwal, Minhyong Kim, Oisin Kim
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
public import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.LinearAlgebra.Dimension.OrzechProperty
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.KrullDimension.Regular
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Architect
public import Hironaka.Ch1.FundamentalTheorems
public import Hironaka.Compat.RegularQuotient
public import Hironaka.Compat.SubschemeStalk
public import Hironaka.Compat.LocalizeSuccession
public import Hironaka.Ch2.PointwiseFlatness
public import Hironaka.Ch2.AscendingChain
public import Hironaka.Ch3.Stability
public import Hironaka.Ch4.Localization
public import Hironaka.Compat.StrictTransformExceptional
public import Hironaka.Compat.BlowupOrderDrop
public import Hironaka.Compat.DatumPresentationBase
public import Hironaka.Compat.TransformNormalCrossingsLocalized

/-!
# Ch. IV §2 (pp. 286–288): Lemmas 3, 4 and 5

The union `E_1 ∪ ⋯ ∪ E_α` of a family of subschemes, Lemma 3 (p. 286), the local computation in the chart
`R' = R[P/z_t]` and Lemma 4 (pp. 286–287), and Lemma 5 (pp. 287–288).

This is part 1 of 3 of `Hironaka.Ch4.Preparation`, which imports all parts; its description holds the
notation and the formalization notes for the whole section.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace Hironaka

universe u v

noncomputable section

/-! ### The union `E_1 ∪ ⋯ ∪ E_α` of a family of subschemes -/

/-- The union `⋃_i E_i` of a family of subschemes: the *meet* of the ideal sheaves, exactly
as `Subscheme.union` (p. 165) for two of them.  For an empty family this is `⊤`, the empty
subscheme.  (Same construction as `DatumII.Raw.eUnion` for data of type `ℜ^N_II`.) -/
def Subscheme.unionFam {X : Scheme.{u}} {ι : Type v} (E : ι → Subscheme X) : Subscheme X :=
  ⨅ i, E i

/-- The union of the empty family is the empty subscheme (the case `α = 0`). -/
theorem Subscheme.unionFam_of_isEmpty {X : Scheme.{u}} {ι : Type v} [IsEmpty ι]
    (E : ι → Subscheme X) : Subscheme.unionFam E = Subscheme.empty := by
  simp [Subscheme.unionFam, Subscheme.empty]

/-! ### Lemma 3 (p. 286) -/

section L3Algebra

open IsLocalRing

section CotAlg

variable {R : Type u} [CommRing R] [IsLocalRing R]

open Classical in
/-- The class in `m/m²` of an element of `R` (zero outside `m`). -/
private noncomputable def cotR (a : R) : CotangentSpace R :=
  if h : a ∈ maximalIdeal R then (maximalIdeal R).toCotangent ⟨a, h⟩ else 0

private theorem cotR_of_mem {a : R} (h : a ∈ maximalIdeal R) :
    cotR a = (maximalIdeal R).toCotangent ⟨a, h⟩ := by
  unfold cotR
  simp [h]

private theorem cotR_add {a b : R} (ha : a ∈ maximalIdeal R) (hb : b ∈ maximalIdeal R) :
    cotR (a + b) = cotR a + cotR b := by
  rw [cotR_of_mem ha, cotR_of_mem hb, cotR_of_mem (add_mem ha hb), ← map_add]
  rfl

private theorem cotR_sub {a b : R} (ha : a ∈ maximalIdeal R) (hb : b ∈ maximalIdeal R) :
    cotR (a - b) = cotR a - cotR b := by
  rw [cotR_of_mem ha, cotR_of_mem hb, cotR_of_mem (sub_mem ha hb), ← map_sub]
  rfl

private theorem cotR_mul (r : R) {a : R} (ha : a ∈ maximalIdeal R) :
    cotR (r * a) = (IsLocalRing.residue R r) • cotR a := by
  rw [cotR_of_mem ha, cotR_of_mem (Ideal.mul_mem_left _ r ha),
    ← IsLocalRing.ResidueField.algebraMap_eq, algebraMap_smul, ← map_smul]
  rfl

private theorem cotR_eq_zero_iff {a : R} (ha : a ∈ maximalIdeal R) :
    cotR a = 0 ↔ a ∈ maximalIdeal R ^ 2 := by
  rw [cotR_of_mem ha, Ideal.toCotangent_eq_zero]

private theorem cotR_zero : cotR (0 : R) = 0 := by
  rw [cotR_eq_zero_iff (zero_mem _)]
  exact zero_mem _

private theorem cotR_mem_span_of_mem_span {s : Set R} (hs : s ⊆ maximalIdeal R) {a : R}
    (ha : a ∈ Ideal.span s) :
    cotR a ∈ Submodule.span (ResidueField R) (cotR '' s) := by
  have hle : Ideal.span s ≤ maximalIdeal R := Ideal.span_le.mpr hs
  induction ha using Submodule.span_induction with
  | mem x hx => exact Submodule.subset_span ⟨x, hx, rfl⟩
  | zero => rw [cotR_zero]; exact zero_mem _
  | add x y hx hy ihx ihy =>
    rw [cotR_add (hle hx) (hle hy)]
    exact add_mem ihx ihy
  | smul r x hx ihx =>
    rw [smul_eq_mul, cotR_mul r (hle hx)]
    exact Submodule.smul_mem _ _ ihx

private theorem exists_sub_mem_sq_of_cotR_mem_span {g : Set R} (hg : g ⊆ maximalIdeal R)
    {a : R} (ha : a ∈ maximalIdeal R)
    (h : cotR a ∈ Submodule.span (ResidueField R) (cotR '' g)) :
    ∃ b ∈ Ideal.span g, a - b ∈ maximalIdeal R ^ 2 := by
  have hle : Ideal.span g ≤ maximalIdeal R := Ideal.span_le.mpr hg
  have key : ∀ v ∈ Submodule.span (ResidueField R) (cotR '' g),
      ∃ b ∈ Ideal.span g, cotR b = v := by
    intro v hv
    induction hv using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨y, hy, rfl⟩ := hx
      exact ⟨y, Ideal.subset_span hy, rfl⟩
    | zero => exact ⟨0, zero_mem _, cotR_zero⟩
    | add x y _ _ ihx ihy =>
      obtain ⟨b₁, hb₁, rfl⟩ := ihx
      obtain ⟨b₂, hb₂, rfl⟩ := ihy
      exact ⟨b₁ + b₂, add_mem hb₁ hb₂, cotR_add (hle hb₁) (hle hb₂)⟩
    | smul c x _ ihx =>
      obtain ⟨b, hb, rfl⟩ := ihx
      obtain ⟨r, rfl⟩ := IsLocalRing.residue_surjective c
      exact ⟨r * b, Ideal.mul_mem_left _ r hb, cotR_mul r (hle hb)⟩
  obtain ⟨b, hb, hbv⟩ := key _ h
  refine ⟨b, hb, (cotR_eq_zero_iff (sub_mem ha (hle hb))).mp ?_⟩
  rw [cotR_sub ha (hle hb), hbv, sub_self]

/-- Nakayama's lemma in the form used below. -/
private theorem le_span_of_cotR [IsNoetherianRing R] (N : Ideal R) (hN : N ≤ maximalIdeal R)
    {g : Set R} (hgN : g ⊆ N)
    (h1 : ∀ a ∈ N, cotR a ∈ Submodule.span (ResidueField R) (cotR '' g))
    (h2 : ∀ e ∈ N, e ∈ maximalIdeal R ^ 2 → e ∈ maximalIdeal R * N) :
    N ≤ Ideal.span g := by
  refine Submodule.le_of_le_smul_of_le_jacobson_bot (IsNoetherian.noetherian N)
    (IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top).ge ?_
  intro a ha
  obtain ⟨b, hb, hab⟩ := exists_sub_mem_sq_of_cotR_mem_span (hgN.trans hN) (hN ha) (h1 a ha)
  have hbN : b ∈ N := Ideal.span_le.mpr hgN hb
  have : a - b ∈ maximalIdeal R • N := h2 _ (sub_mem ha hbN) hab
  rw [show a = b + (a - b) by ring]
  exact Submodule.add_mem_sup hb this

end CotAlg

section CotAlgReg

variable {R : Type u} [CommRing R] [IsRegularLocalRing R]

private theorem finrank_cotangentSpace_eq :
    ((Module.finrank (ResidueField R) (CotangentSpace R) : ℕ) : WithBot ℕ∞) =
      ringKrullDim R := by
  rw [← IsLocalRing.spanFinrank_maximalIdeal_eq_finrank_cotangentSpace,
    IsRegularLocalRing.spanFinrank_maximalIdeal]

private theorem rsop_subset {z : Finset R} (hz : IsRegularSystemOfParameters R z) :
    (z : Set R) ⊆ maximalIdeal R := by
  rw [← hz.1]
  exact Ideal.subset_span

private theorem span_cotR_eq_top_of_rsop {z : Finset R} (hz : IsRegularSystemOfParameters R z) :
    Submodule.span (ResidueField R) (cotR '' (z : Set R)) = ⊤ := by
  refine eq_top_iff.mpr fun v _ => ?_
  obtain ⟨⟨a, ha⟩, rfl⟩ := (maximalIdeal R).toCotangent_surjective v
  rw [← cotR_of_mem ha]
  refine cotR_mem_span_of_mem_span (rsop_subset hz) ?_
  rw [hz.1]
  exact ha

private theorem linearIndepOn_cotR_of_rsop {z : Finset R}
    (hz : IsRegularSystemOfParameters R z) :
    LinearIndepOn (ResidueField R) cotR (z : Set R) := by
  refine linearIndependent_of_top_le_span_of_card_eq_finrank ?_ ?_
  · rw [← Set.image_eq_range, span_cotR_eq_top_of_rsop hz]
  · have h := hz.2
    rw [← finrank_cotangentSpace_eq] at h
    have h' : z.card = Module.finrank (ResidueField R) (CotangentSpace R) := by
      exact_mod_cast h
    simpa using h'

private theorem rsop_of_linearIndepOn (z : Finset R)
    (hzm : (z : Set R) ⊆ maximalIdeal R) (hind : LinearIndepOn (ResidueField R) cotR (z : Set R))
    (hspan : Submodule.span (ResidueField R) (cotR '' (z : Set R)) = ⊤) :
    IsRegularSystemOfParameters R z := by
  refine ⟨le_antisymm (Ideal.span_le.mpr hzm) ?_, ?_⟩
  · refine le_span_of_cotR _ le_rfl hzm (fun a _ => by rw [hspan]; trivial) ?_
    intro e _ he
    rwa [← pow_two]
  · have h1 := finrank_span_eq_card hind
    rw [← Set.image_eq_range, hspan, finrank_top] at h1
    rw [← finrank_cotangentSpace_eq, h1]
    simp

private theorem cotR_sum {T : Finset R} (hT : ∀ i ∈ T, i ∈ maximalIdeal R) (f : R → R) :
    cotR (∑ i ∈ T, f i * i) = ∑ i ∈ T, (IsLocalRing.residue R (f i)) • cotR i := by
  classical
  induction T using Finset.induction_on with
  | empty => simp [cotR_zero]
  | insert j T hj ih =>
    have hj' := hT j (Finset.mem_insert_self j T)
    have hT' : ∀ i ∈ T, i ∈ maximalIdeal R := fun i hi => hT i (Finset.mem_insert_of_mem hi)
    rw [Finset.sum_insert hj, Finset.sum_insert hj,
      cotR_add (Ideal.mul_mem_left _ _ hj')
        (sum_mem fun i hi => Ideal.mul_mem_left _ _ (hT' i hi)),
      cotR_mul _ hj', ih hT']

/-- If `T` is part of a regular system of parameters, then `(T) ∩ m² = m (T)`. -/
private theorem mem_mul_span_of_mem_sq {z T : Finset R}
    (hz : IsRegularSystemOfParameters R z) (hTz : T ⊆ z) {e : R}
    (he : e ∈ Ideal.span (T : Set R)) (he2 : e ∈ maximalIdeal R ^ 2) :
    e ∈ maximalIdeal R * Ideal.span (T : Set R) := by
  classical
  obtain ⟨f, -, rfl⟩ := Submodule.mem_span_finset.mp he
  have hTm : ∀ i ∈ T, i ∈ maximalIdeal R := fun i hi => rsop_subset hz (hTz hi)
  have hind : LinearIndepOn (ResidueField R) cotR (T : Set R) :=
    (linearIndepOn_cotR_of_rsop hz).mono (by exact_mod_cast hTz)
  have hsum : ∑ i ∈ T, (IsLocalRing.residue R (f i)) • cotR i = 0 := by
    have := cotR_sum hTm f
    simp only [smul_eq_mul] at he2 ⊢
    rw [← this, cotR_eq_zero_iff (sum_mem fun i hi => Ideal.mul_mem_left _ _ (hTm i hi))]
    exact he2
  have hf := linearIndepOn_finset_iff.mp hind (fun i => IsLocalRing.residue R (f i)) hsum
  refine sum_mem fun i hi => ?_
  rw [smul_eq_mul]
  have : f i ∈ maximalIdeal R := (IsLocalRing.residue_eq_zero_iff _).mp (hf i hi)
  exact Ideal.mul_mem_mul this (Ideal.subset_span hi)

/-- Core of the "flag" lemma (see `exists_rsop_adapted_to_flag`): the component generators `C` lie
literally in both `zB` and `zW`. -/
private theorem exists_rsop_adapted_to_flag_of_subset (Q P : Ideal R) (hQP : Q ≤ P) (zB tB zW tW C : Finset R)
    (hzB : IsRegularSystemOfParameters R zB) (htB : tB ⊆ zB) (hP : P = Ideal.span (tB : Set R))
    (hzW : IsRegularSystemOfParameters R zW) (htW : tW ⊆ zW) (hQ : Q = Ideal.span (tW : Set R))
    (hCB : C ⊆ zB) (hCW : ∀ c ∈ C, c ∉ Q → c ∈ zW) :
    ∃ Z : Finset R, IsRegularSystemOfParameters R Z ∧ C ⊆ Z ∧
      ∃ tP ⊆ Z, P = Ideal.span (tP : Set R) ∧ ∃ tQ ⊆ tP, Q = Ideal.span (tQ : Set R) := by
  classical
  have hzBm := rsop_subset hzB
  have hzWm := rsop_subset hzW
  have hBind := linearIndepOn_cotR_of_rsop hzB
  have hWind := linearIndepOn_cotR_of_rsop hzW
  have htBm : (tB : Set R) ⊆ maximalIdeal R := (by exact_mod_cast htB : (tB : Set R) ⊆ zB).trans hzBm
  have htWm : (tW : Set R) ⊆ maximalIdeal R := (by exact_mod_cast htW : (tW : Set R) ⊆ zW).trans hzWm
  set A : Set R := {c | c ∈ (C : Set R) ∧ c ∈ Q} with hAdef
  set M : Set R := {c | c ∈ (C : Set R) ∧ c ∈ P ∧ c ∉ Q} with hMdef
  set N : Set R := {c | c ∈ (C : Set R) ∧ c ∉ P} with hNdef
  -- step 1: a basis `b₁` of the image of `Q` containing `A`
  have hAind : LinearIndepOn (ResidueField R) cotR A := hBind.mono fun x hx => hCB hx.1
  obtain ⟨b₁, hb₁sub, hAb₁, hspan₁, hb₁ind⟩ :=
    exists_linearIndepOn_extension hAind (Set.subset_union_left : A ⊆ A ∪ (tW : Set R))
  have hb₁Q : b₁ ⊆ Q := fun x hx => (hb₁sub hx).elim (fun h => h.2)
    (fun h => hQ ▸ Ideal.subset_span h)
  -- step 2: add `M`
  have hMtW : Disjoint (tW : Set R) M := Set.disjoint_left.mpr fun x hx hxM =>
    hxM.2.2 (hQ ▸ Ideal.subset_span hx)
  have hMWind : LinearIndepOn (ResidueField R) cotR ((tW : Set R) ∪ M) :=
    hWind.mono (Set.union_subset (by exact_mod_cast htW) fun x hx => hCW x hx.1 hx.2.2)
  have hMW := (linearIndepOn_union_iff hMtW).mp hMWind
  have hb₁t : Submodule.span (ResidueField R) (cotR '' b₁) ≤
      Submodule.span (ResidueField R) (cotR '' (tW : Set R)) := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨x, hx, rfl⟩
    refine cotR_mem_span_of_mem_span htWm ?_
    rw [← hQ]
    exact hb₁Q hx
  have hb₁M : LinearIndepOn (ResidueField R) cotR (b₁ ∪ M) :=
    hb₁ind.union hMW.2.1 (Disjoint.mono_left hb₁t hMW.2.2)
  obtain ⟨b₂, hb₂sub, hb₁Mb₂, hspan₂, hb₂ind⟩ :=
    exists_linearIndepOn_extension hb₁M (Set.subset_union_left : b₁ ∪ M ⊆ (b₁ ∪ M) ∪ (tB : Set R))
  have hb₂P : b₂ ⊆ P := by
    intro x hx
    rcases hb₂sub hx with (h | h) | h
    · exact hQP (hb₁Q h)
    · exact h.2.1
    · exact hP ▸ Ideal.subset_span h
  -- step 3: add `N`
  have hNtB : Disjoint (tB : Set R) N := Set.disjoint_left.mpr fun x hx hxN =>
    hxN.2 (hP ▸ Ideal.subset_span hx)
  have hNBind : LinearIndepOn (ResidueField R) cotR ((tB : Set R) ∪ N) :=
    hBind.mono (Set.union_subset (by exact_mod_cast htB) fun x hx => hCB hx.1)
  have hNB := (linearIndepOn_union_iff hNtB).mp hNBind
  have hb₂t : Submodule.span (ResidueField R) (cotR '' b₂) ≤
      Submodule.span (ResidueField R) (cotR '' (tB : Set R)) := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨x, hx, rfl⟩
    refine cotR_mem_span_of_mem_span htBm ?_
    rw [← hP]
    exact hb₂P hx
  have hb₂N : LinearIndepOn (ResidueField R) cotR (b₂ ∪ N) :=
    hb₂ind.union hNB.2.1 (Disjoint.mono_left hb₂t hNB.2.2)
  obtain ⟨b₃, hb₃sub, hb₂Nb₃, hspan₃, hb₃ind⟩ :=
    exists_linearIndepOn_extension hb₂N (Set.subset_union_left : b₂ ∪ N ⊆ (b₂ ∪ N) ∪ (zB : Set R))
  have hb₃top : Submodule.span (ResidueField R) (cotR '' b₃) = ⊤ := by
    refine eq_top_iff.mpr ?_
    rw [← span_cotR_eq_top_of_rsop hzB]
    refine Submodule.span_le.mpr ((Set.image_mono ?_).trans hspan₃)
    exact Set.subset_union_right
  have hb₃sub' : b₃ ⊆ ((zB ∪ zW : Finset R) : Set R) := by
    intro x hx
    rw [Finset.coe_union]
    rcases hb₃sub hx with (h | h) | h
    · rcases hb₂sub h with (h' | h') | h'
      · rcases hb₁sub h' with h'' | h''
        · exact Or.inl (hCB h''.1)
        · exact Or.inr (htW h'')
      · exact Or.inl (hCB h'.1)
      · exact Or.inl (htB h')
    · exact Or.inl (hCB h.1)
    · exact Or.inl h
  have hb₃fin : b₃.Finite := (Finset.finite_toSet _).subset hb₃sub'
  have hb₂fin : b₂.Finite := hb₃fin.subset (Set.subset_union_left.trans hb₂Nb₃)
  have hb₁fin : b₁.Finite := hb₂fin.subset (Set.subset_union_left.trans hb₁Mb₂)
  have hb₁b₂ : b₁ ⊆ b₂ := Set.subset_union_left.trans hb₁Mb₂
  have hb₂b₃ : b₂ ⊆ b₃ := Set.subset_union_left.trans hb₂Nb₃
  refine ⟨hb₃fin.toFinset, rsop_of_linearIndepOn _ ?_ ?_ ?_, ?_, hb₂fin.toFinset, ?_, ?_⟩
  · rw [Set.Finite.coe_toFinset]
    refine hb₃sub'.trans ?_
    rw [Finset.coe_union]
    exact Set.union_subset hzBm hzWm
  · rwa [Set.Finite.coe_toFinset]
  · rwa [Set.Finite.coe_toFinset]
  · intro c hc
    rw [Set.Finite.mem_toFinset]
    by_cases hcP : c ∈ P
    · by_cases hcQ : c ∈ Q
      · exact hb₂b₃ (hb₁b₂ (hAb₁ ⟨hc, hcQ⟩))
      · exact hb₂b₃ (hb₁Mb₂ (Or.inr ⟨hc, hcP, hcQ⟩))
    · exact hb₂Nb₃ (Or.inr ⟨hc, hcP⟩)
  · intro x hx
    rw [Set.Finite.mem_toFinset] at hx ⊢
    exact hb₂b₃ hx
  refine ⟨?_, hb₁fin.toFinset, fun x hx => ?_, ?_⟩
  · rw [Set.Finite.coe_toFinset]
    refine le_antisymm (le_span_of_cotR P (hP ▸ Ideal.span_le.mpr htBm) hb₂P
      (fun a ha => ?_) (fun e he he2 => ?_)) (Ideal.span_le.mpr hb₂P)
    · rw [hP] at ha
      refine Submodule.span_le.mpr ?_ (cotR_mem_span_of_mem_span htBm ha)
      rintro _ ⟨x, hx, rfl⟩
      exact hspan₂ ⟨x, Or.inr hx, rfl⟩
    · rw [hP] at he ⊢
      exact mem_mul_span_of_mem_sq hzB htB he he2
  · rw [Set.Finite.mem_toFinset] at hx
    rw [Set.Finite.mem_toFinset]
    exact hb₁b₂ hx
  · rw [Set.Finite.coe_toFinset]
    refine le_antisymm (le_span_of_cotR Q (hQ ▸ Ideal.span_le.mpr htWm) hb₁Q
      (fun a ha => ?_) (fun e he he2 => ?_)) (Ideal.span_le.mpr hb₁Q)
    · rw [hQ] at ha
      refine Submodule.span_le.mpr ?_ (cotR_mem_span_of_mem_span htWm ha)
      rintro _ ⟨x, hx, rfl⟩
      exact hspan₁ ⟨x, Or.inr hx, rfl⟩
    · rw [hQ] at he ⊢
      exact mem_mul_span_of_mem_sq hzW htW he he2

/-- The "flag" lemma behind the tacit step of Lemma 4 (p. 287): a regular system of parameters
`Z` of `R` adapted *simultaneously* to the generators `C` of the components `E_j` through `x`,
to the prime `P = B_x` and to the prime `Q = W_x ⊆ P` (both generated by parts of `Z`, `Q` by
a part of that for `P`), given two regular systems of parameters `zB`, `zW`, adapted to `C`
and `P`, resp. to `C` (up to associates) and `Q`. -/
theorem exists_rsop_adapted_to_flag (Q P : Ideal R) (hQP : Q ≤ P) (zB tB zW tW C : Finset R)
    (hzB : IsRegularSystemOfParameters R zB) (htB : tB ⊆ zB) (hP : P = Ideal.span (tB : Set R))
    (hzW : IsRegularSystemOfParameters R zW) (htW : tW ⊆ zW) (hQ : Q = Ideal.span (tW : Set R))
    (hCB : C ⊆ zB) (hCW : ∀ c ∈ C, c ∉ Q → ∃ a ∈ zW, Ideal.span {c} = Ideal.span {a}) :
    ∃ Z : Finset R, IsRegularSystemOfParameters R Z ∧ C ⊆ Z ∧
      ∃ tP ⊆ Z, P = Ideal.span (tP : Set R) ∧ ∃ tQ ⊆ tP, Q = Ideal.span (tQ : Set R) := by
  classical
  have := isDomain_of_isRegularLocalRing R
  have hzBe := ExtendsToRSOP.of_isRegularSystemOfParameters hzB
  have hzWe := ExtendsToRSOP.of_isRegularSystemOfParameters hzW
  let g : R → R := fun a =>
    if h : ∃ c ∈ C, Ideal.span {c} = Ideal.span {a} then h.choose else a
  have hg : ∀ a, Ideal.span {g a} = Ideal.span {a} := by
    intro a
    by_cases h : ∃ c ∈ C, Ideal.span {c} = Ideal.span {a}
    · have : g a = h.choose := dite_eq_left_of_eq_true (eq_true h)
      rw [this]; exact h.choose_spec.2
    · have : g a = a := dite_eq_right_of_eq_false (eq_false h)
      rw [this]
  have hginj : Set.InjOn g (zW : Set R) := by
    intro a ha b hb hab
    refine hzWe.span_singleton_injOn ha hb ?_
    show Ideal.span {a} = Ideal.span {b}
    rw [← hg a, ← hg b, hab]
  have hassoc : ∀ v ∈ zW, Associated v (g v) := fun v _ =>
    Ideal.span_singleton_eq_span_singleton.mp (hg v).symm
  obtain ⟨Y, hWY, hY⟩ := hzWe.image_of_associated g hginj hassoc
  have hCY : ∀ c ∈ C, c ∉ Q → c ∈ Y := by
    intro c hc hcQ
    obtain ⟨a, ha, hca⟩ := hCW c hc hcQ
    apply hWY
    refine Finset.mem_image.mpr ⟨a, ha, ?_⟩
    have h : ∃ c' ∈ C, Ideal.span {c'} = Ideal.span {a} := ⟨c, hc, hca⟩
    have hga : g a = h.choose := dite_eq_left_of_eq_true (eq_true h)
    rw [hga]
    exact hzBe.span_singleton_injOn (hCB h.choose_spec.1) (hCB hc) (h.choose_spec.2.trans hca.symm)
  have htWY : tW.image g ⊆ Y := fun x hx =>
    hWY (Finset.image_subset_image htW hx)
  have hQ' : Q = Ideal.span ((tW.image g : Finset R) : Set R) := by
    rw [hQ]
    apply le_antisymm
    · refine Ideal.span_le.mpr fun a ha => ?_
      have : a ∈ Ideal.span {g a} := by
        rw [hg]; exact Ideal.mem_span_singleton_self a
      refine Ideal.span_mono ?_ ((Ideal.span_singleton_le_iff_mem _).mpr (Ideal.subset_span
        (Finset.mem_coe.mpr (Finset.mem_image_of_mem g ha))) this)
      exact fun _ h => h
    · refine Ideal.span_le.mpr fun x hx => ?_
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hx)
      have : g a ∈ Ideal.span {a} := by
        rw [← hg]; exact Ideal.mem_span_singleton_self _
      exact (Ideal.span_singleton_le_iff_mem _).mpr (Ideal.subset_span (Finset.mem_coe.mpr ha)) this
  exact exists_rsop_adapted_to_flag_of_subset Q P hQP zB tB Y (tW.image g) C hzB htB hP hY htWY hQ' hCB hCY

end CotAlgReg

end L3Algebra

/-- At a point of a non-singular subscheme `D`, `D_x` is prime and `O_{X,x}/D_x` is regular. -/
private theorem isPrime_and_isRegularLocalRing_quotient_of_isNonsingular {X : Scheme.{u}} (D : Subscheme X)
    (hD : D.IsNonsingular) {x : X} (hx : x ∈ D.pts) :
    (D.stalkIdeal x).IsPrime ∧ IsRegularLocalRing (X.presheaf.stalk x ⧸ D.stalkIdeal x) := by
  have hx' : x ∈ Set.range D.ι := by
    rw [Scheme.IdealSheafData.range_subschemeι]
    exact hx
  obtain ⟨x', rfl⟩ := hx'
  obtain ⟨e⟩ := nonempty_stalk_quot_equiv D x'
  have : IsRegularLocalRing (D.toScheme.presheaf.stalk x') := hD x'
  have hreg : IsRegularLocalRing (X.presheaf.stalk (D.ι x') ⧸ D.stalkIdeal (D.ι x')) :=
    IsRegularLocalRing.of_ringEquiv e.symm
  have := isDomain_of_isRegularLocalRing
    (X.presheaf.stalk (D.ι x') ⧸ D.stalkIdeal (D.ι x'))
  exact ⟨(Ideal.Quotient.isDomain_iff_prime _).mp this, hreg⟩

/-- A non-singular subscheme is reduced. -/
private theorem isReduced_toScheme_of_isNonsingular {X : Scheme.{u}} (D : Subscheme X)
    (hD : D.IsNonsingular) : IsReduced D.toScheme := by
  have : ∀ y : D.toScheme, _root_.IsReduced (D.toScheme.presheaf.stalk y) := fun y => by
    have : IsRegularLocalRing (D.toScheme.presheaf.stalk y) := hD y
    have := isDomain_of_isRegularLocalRing (D.toScheme.presheaf.stalk y)
    infer_instance
  exact isReduced_of_isReduced_stalk _

/-- The ideal sheaf of a reduced subscheme is its own radical. -/
private theorem radical_eq_self_of_isReduced_toScheme {X : Scheme.{u}} (D : Subscheme X)
    (hD : IsReduced D.toScheme) : D.radical = D := by
  refine Scheme.IdealSheafData.ext (funext fun U => ?_)
  show (D.ideal U).radical = D.ideal U
  have e := (Scheme.IdealSheafData.subschemeObjIso D U).commRingCatIsoToRingEquiv
  have : _root_.IsReduced (Γ(X, U) ⧸ D.ideal U) :=
    isReduced_of_injective e.symm.toRingHom e.symm.injective
  exact ((Ideal.isRadical_iff_quotient_reduced _).mpr this).radical

/-- For a reduced `F`, `F ⊆ D` as soon as the points of `F` lie on `D`. -/
private theorem isContainedIn_of_pts_subset_of_isReduced_toScheme {X : Scheme.{u}} {F D : Subscheme X}
    (hF : IsReduced F.toScheme) (h : F.pts ⊆ D.pts) : F.IsContainedIn D := by
  have h1 : D ≤ Scheme.IdealSheafData.vanishingIdeal F.support :=
    Scheme.IdealSheafData.le_support_iff_le_vanishingIdeal.mp h
  rw [Scheme.IdealSheafData.vanishingIdeal_support, radical_eq_self_of_isReduced_toScheme F hF] at h1
  exact fun U => h1 U

/-- The points of `E₁ ∪ ⋯ ∪ E_α` are those lying on some `E_j`. -/
private theorem mem_pts_unionFam_iff {X : Scheme.{u}} {α : ℕ} (E : Fin α → Subscheme X)
    {x : X} : x ∈ (Subscheme.unionFam E).pts ↔ ∃ j, x ∈ (E j).pts := by
  classical
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  let U' : X.affineOpens := ⟨U, hU⟩
  have hmem : ∀ D : Subscheme X, x ∈ D.pts ↔ ∀ f ∈ D.ideal U', x ∉ X.basicOpen f := by
    intro D
    show x ∈ (D.support : Set X) ↔ _
    rw [SetLike.mem_coe, Scheme.IdealSheafData.mem_support_iff_of_mem (U := U') hxU,
      Scheme.mem_zeroLocus_iff]
    rfl
  rw [hmem]
  simp_rw [hmem]
  have hideal : (Subscheme.unionFam E).ideal U' = ⨅ j, (E j).ideal U' := by
    rw [Subscheme.unionFam, Scheme.IdealSheafData.ideal_iInf, iInf_apply]
  rw [hideal]
  constructor
  · intro h
    by_contra hne
    push Not at hne
    choose f hf hxf using hne
    have hprod : ∏ j, f j ∈ ⨅ j, (E j).ideal U' := by
      refine Submodule.mem_iInf _ |>.mpr fun j => ?_
      rw [← Finset.mul_prod_erase Finset.univ f (Finset.mem_univ j)]
      exact Ideal.mul_mem_right _ _ (hf j)
    refine h _ hprod ?_
    rw [Scheme.mem_basicOpen _ _ _ hxU, map_prod, IsUnit.prod_univ_iff]
    intro j
    have := hxf j
    rwa [Scheme.mem_basicOpen _ _ _ hxU] at this
  · rintro ⟨j, hj⟩ f hf
    exact hj f ((Submodule.mem_iInf _).mp hf j)

/-- Local-to-global: if `D₁,x ⊆ D₂,x` and a generization `η` of `x` lies on `D₂`, then `η` lies
on `D₁`. -/
theorem mem_pts_of_stalkIdeal_le_of_specializes {X : Scheme.{u}} {D₁ D₂ : Subscheme X} {x η : X}
    (hηx : η ⤳ x) (hη : η ∈ D₂.pts) (h : D₁.stalkIdeal x ≤ D₂.stalkIdeal x) : η ∈ D₁.pts := by
  by_contra hη1
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  let U' : X.affineOpens := ⟨U, hU⟩
  have hηU : η ∈ U := hηx.mem_open U.isOpen hxU
  have : ¬ η ∈ X.zeroLocus (U := U) (D₁.ideal U') := by
    rwa [← Scheme.IdealSheafData.mem_support_iff_of_mem (U := U') hηU]
  rw [Scheme.mem_zeroLocus_iff] at this
  push Not at this
  obtain ⟨s, hs, hηs⟩ := this
  rw [Scheme.mem_basicOpen _ _ _ hηU] at hηs
  have hgx : X.presheaf.germ U x hxU s ∈ D₂.stalkIdeal x :=
    h (Ideal.subset_span ⟨U', hxU, s, hs, rfl⟩)
  -- the specialization map sends `D₂,x` into `D₂,η`
  have hsp : ∀ a ∈ D₂.stalkIdeal x, X.presheaf.stalkSpecializes hηx a ∈ D₂.stalkIdeal η := by
    intro a ha
    induction ha using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨V, hxV, f, hf, rfl⟩ := hy
      rw [TopCat.Presheaf.germ_stalkSpecializes_apply]
      exact Ideal.subset_span ⟨V, hηx.mem_open V.1.isOpen hxV, f, hf, rfl⟩
    | zero => rw [map_zero]; exact zero_mem _
    | add a b _ _ ha hb => rw [map_add]; exact add_mem ha hb
    | smul r a _ ha => rw [smul_eq_mul, map_mul]; exact Ideal.mul_mem_left _ _ ha
  have h1 := stalkIdeal_le_maximalIdeal_of_mem_pts D₂ hη (hsp _ hgx)
  rw [TopCat.Presheaf.germ_stalkSpecializes_apply] at h1
  exact (IsLocalRing.mem_maximalIdeal _).mp h1 hηs

/-- If `W` lies in `Z` and `W_x` is prime, then `(red Z)_x ⊆ W_x`. -/
private theorem stalkIdeal_ofClosed_le_of_isPrime {X : Scheme.{u}} {W : Subscheme X} {Z : Closeds X}
    (hWZ : W.pts ⊆ Z) {x : X} (hWx : (W.stalkIdeal x).IsPrime) :
    (Subscheme.ofClosed Z).stalkIdeal x ≤ W.stalkIdeal x := by
  refine Ideal.span_le.mpr ?_
  rintro a ⟨U, hx, s, hs, rfl⟩
  have h1 : Subscheme.ofClosed Z ≤ W.radical := by
    rw [← Scheme.IdealSheafData.vanishingIdeal_support]
    exact Scheme.IdealSheafData.vanishingIdeal_antimono hWZ
  obtain ⟨n, hn⟩ := h1 U hs
  refine hWx.mem_of_pow_mem n ?_
  rw [← map_pow]
  exact Ideal.subset_span ⟨U, hx, s ^ n, hn, rfl⟩

section PrepUnionQuotient

open IsLocalRing

open Classical in
/-- "A set `T` extending to a regular system of parameters of `A`, whose residues in `A/(T)`
(regular) are followed by a set whose residues extend to a regular system of parameters of
`A/(T)`, give together a set extending to a regular system of parameters of `A`": the passage
from (b) and (c) to a regular system of parameters of `R'` in the proof of Lemma 4, generalising
`rsop_extends_insert_of_quotient`. -/
theorem ExtendsToRSOP.union_of_quotient {A : Type u} [CommRing A] [IsRegularLocalRing A]
    {T S : Finset A} (hT : ExtendsToRSOP A T)
    [IsRegularLocalRing (A ⧸ Ideal.span (T : Set A))]
    (hS : ExtendsToRSOP (A ⧸ Ideal.span (T : Set A))
      (S.image (Ideal.Quotient.mk (Ideal.span (T : Set A)))))
    (hinj : Set.InjOn (Ideal.Quotient.mk (Ideal.span (T : Set A))) S) :
    ExtendsToRSOP A (T ∪ S) := by
  classical
  obtain ⟨Z, hTZ, hZ⟩ := hT
  obtain ⟨_hreg, hRS, hcard⟩ := rsop_quotient hZ hTZ
  set J := Ideal.span (T : Set A) with hJ
  set mk := Ideal.Quotient.mk J with hmk
  obtain ⟨W, hSW, hW⟩ := hS
  set σ := Function.surjInv (Ideal.Quotient.mk_surjective (I := J)) with hσdef
  have hσ : mk ∘ σ = id := funext (Function.surjInv_eq _)
  have hZM : ∀ z ∈ Z, z ∈ maximalIdeal A := fun z hz => hZ.1 ▸ Ideal.subset_span hz
  have hloc : IsLocalHom mk := IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective
  have hmem : ∀ a : A, mk a ∈ maximalIdeal (A ⧸ J) → a ∈ maximalIdeal A := fun a ha =>
    (IsLocalRing.mem_maximalIdeal _).mpr fun hu =>
      (IsLocalRing.mem_maximalIdeal _).mp ha (hu.map _)
  set V' : Finset A := S ∪ (W \ S.image mk).image σ with hV'
  have hV'W : V'.image mk = W := by
    rw [hV', Finset.image_union, Finset.image_image, hσ, Finset.image_id,
      Finset.union_sdiff_of_subset hSW]
  have hspan : Ideal.span ((T ∪ V' : Finset A) : Set A) = maximalIdeal A := by
    refine le_antisymm (Ideal.span_le.mpr fun b hb => ?_) fun a ha => ?_
    · rcases Finset.mem_union.mp (Finset.mem_coe.mp hb) with hb | hb
      · exact hZM b (hTZ hb)
      · apply hmem
        have : mk b ∈ W := by rw [← hV'W]; exact Finset.mem_image_of_mem _ hb
        exact hW.1 ▸ Ideal.subset_span this
    · have hmk' : mk a ∈ Ideal.span ((V'.image mk : Finset _) : Set (A ⧸ J)) := by
        rw [hV'W, hW.1]
        exact map_nonunit mk a ha
      have := rsop_mem_span_sup_of_mk_mem hmk'
      rw [Finset.coe_union, Ideal.span_union, sup_comm]
      exact this
  have hcardV : V'.card ≤ W.card := by
    have a1 : V'.card ≤ S.card + (W \ S.image mk).card := by
      rw [hV']
      exact (Finset.card_union_le _ _).trans (Nat.add_le_add_left Finset.card_image_le _)
    have a3 := Finset.card_sdiff_add_card_eq_card hSW
    have a4 : (S.image mk).card = S.card := Finset.card_image_of_injOn hinj
    omega
  have h1 := rsop_card_eq_spanFinrank hW
  have h2 := rsop_card_eq_spanFinrank hRS
  have h3 := rsop_card_eq_spanFinrank hZ
  have h4 := Finset.card_sdiff_add_card_eq_card hTZ
  have hfin : (T ∪ V').card ≤ (maximalIdeal A).spanFinrank :=
    (Finset.card_union_le _ _).trans (by omega)
  exact ⟨T ∪ V', Finset.union_subset_union_right (Finset.subset_union_left),
    rsop_of_span_of_card_le hspan hfin⟩

end PrepUnionQuotient

section PrepLemma3

open IsLocalRing Classical

/-- Steps 1 and 2 of the proof of Lemma 3 (p. 286): "`(z_1, …, z_β)` can be extended to a minimal
base of `P`" and "`(z, w)` can be extended to a minimal base of `Q`".  Let `P` be a prime of the
regular local ring `A` with `A/P` regular, and `K ⊆ P` a part of a regular system of parameters
of `A`.  Then there is a set `T ⊇ K` generating `P` which is again part of a regular system of
parameters (a "minimal base" of `P` containing `K`).  Proof: `A/(K)` is regular, `P/(K)` is a prime
of it with regular quotient `A/P`, hence generated by a part of a regular system of parameters
of `A/(K)` (`exists_finset_span_eq_prime`); lift the generators and use
`ExtendsToRSOP.union_of_quotient`. -/
theorem exists_extendsToRSOP_span_eq_of_extendsToRSOP {A : Type u} [CommRing A]
    [IsRegularLocalRing A] (P : Ideal A) [P.IsPrime] (hP : IsRegularLocalRing (A ⧸ P))
    {K : Finset A} (hK : ExtendsToRSOP A K) (hKP : (K : Set A) ⊆ P) :
    ∃ T : Finset A, K ⊆ T ∧ ExtendsToRSOP A T ∧ Ideal.span (T : Set A) = P := by
  classical
  set J := Ideal.span (K : Set A) with hJ
  have : IsRegularLocalRing (A ⧸ J) := hK.isRegularLocalRing_quotient
  have hJP : J ≤ P := Ideal.span_le.mpr hKP
  set mk := Ideal.Quotient.mk J with hmk
  have hker : RingHom.ker mk ≤ P := by rw [hmk, Ideal.mk_ker]; exact hJP
  have hPbar : (P.map mk).IsPrime :=
    Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective hker
  have hreg : IsRegularLocalRing ((A ⧸ J) ⧸ P.map mk) :=
    IsRegularLocalRing.of_ringEquiv (DoubleQuot.quotQuotEquivQuotOfLE hJP).symm
  obtain ⟨Sb, Tb, hSb, hSbcard, hTbSb, hTb⟩ := exists_finset_span_eq_prime (A ⧸ J) (P.map mk) hreg
  set σ := Function.surjInv (Ideal.Quotient.mk_surjective (I := J)) with hσdef
  have hσ : mk ∘ σ = id := funext (Function.surjInv_eq _)
  have hT'mk : (Tb.image σ).image mk = Tb := by
    rw [Finset.image_image, hσ, Finset.image_id]
  have hTbe : ExtendsToRSOP (A ⧸ J) ((Tb.image σ).image mk) := by
    rw [hT'mk]
    exact ⟨Sb, hTbSb, rsop_of_span_of_card_le hSb hSbcard.le⟩
  have hinj : Set.InjOn mk (Tb.image σ : Set A) := by
    intro a ha b hb hab
    obtain ⟨u, -, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp ha)
    obtain ⟨v, -, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hb)
    have h1 : mk (σ u) = u := congrFun hσ u
    have h2 : mk (σ v) = v := congrFun hσ v
    rw [h1, h2] at hab
    rw [hab]
  refine ⟨K ∪ Tb.image σ, Finset.subset_union_left, hK.union_of_quotient hTbe hinj, ?_⟩
  rw [Finset.coe_union, Ideal.span_union]
  refine le_antisymm (sup_le hJP ?_) ?_
  · refine Ideal.span_le.mpr fun a ha => ?_
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp ha)
    have h0 : mk (σ u) = u := congrFun hσ u
    have h1 : mk (σ u) ∈ P.map mk := by
      rw [h0, ← hTb]; exact Ideal.subset_span hu
    rw [hmk, Ideal.mem_quotient_iff_mem_sup, sup_eq_left.mpr hJP] at h1
    exact h1
  · intro p hp
    have h1 : mk p ∈ P.map mk := Ideal.mem_map_of_mem _ hp
    rw [← hTb, hT'mk.symm, Finset.coe_image, ← Ideal.map_span] at h1
    rw [hmk, Ideal.mem_quotient_iff_mem_sup] at h1
    rw [sup_comm]
    exact h1

/-- Step 3 of the proof of Lemma 3 (p. 286): "Since `F` is non-singular, (ii) and (iii) imply that
`(z_1, …, z_β, w, y, z_{β+1}, …, z_α)` can be extended to a regular system of parameters of `R`".
Ring-level form: `T'` is a minimal base of the prime `Q` (part of a regular system of parameters),
`Q` is also generated by a part `t` of a regular system of parameters `z` (this is what (ii)
provides) and `G ⊆ z` consists of elements outside `Q` (the `z_j`, `j > β`, which by (iii) do not
lie in `Q`).  Then `T' ∪ G` is part of a regular system of parameters of `R`. -/
theorem exists_extendsToRSOP_union_of_quotient_of_subset {A : Type u} [CommRing A]
    [IsRegularLocalRing A] (Q : Ideal A) {T' t z G : Finset A} (hT' : ExtendsToRSOP A T')
    (hQT' : Ideal.span (T' : Set A) = Q) (hz : IsRegularSystemOfParameters A z) (htz : t ⊆ z)
    (hQt : Ideal.span (t : Set A) = Q) (hGz : G ⊆ z) (hGQ : ∀ a ∈ G, a ∉ Q) :
    ExtendsToRSOP A (T' ∪ G) := by
  classical
  have : IsRegularLocalRing (A ⧸ Ideal.span (T' : Set A)) := hT'.isRegularLocalRing_quotient
  have hGt : ∀ a ∈ G, a ∈ z \ t := fun a ha =>
    Finset.mem_sdiff.mpr ⟨hGz ha, fun hat => hGQ a ha (hQt ▸ Ideal.subset_span hat)⟩
  have hres : ∀ J : Ideal A, J = Ideal.span (t : Set A) → [IsRegularLocalRing (A ⧸ J)] →
      ExtendsToRSOP (A ⧸ J) (G.image (Ideal.Quotient.mk J)) ∧
        Set.InjOn (Ideal.Quotient.mk J) G := by
    intro J hJ _
    subst hJ
    obtain ⟨_, hrs, hcard⟩ := rsop_quotient hz htz
    refine ⟨(ExtendsToRSOP.of_isRegularSystemOfParameters hrs).mono
      (Finset.image_subset_image fun a ha => hGt a ha), ?_⟩
    have := Finset.card_image_iff.mp hcard
    exact this.mono fun a ha => hGt a ha
  obtain ⟨hS, hinj⟩ := hres (Ideal.span (T' : Set A)) (hQT'.trans hQt.symm)
  exact hT'.union_of_quotient hS hinj

/-- Step 2 of the proof of Lemma 3 (p. 286), "`(z, w)` can be extended to a minimal base of `Q`", with
one new generator prescribed: let `Q` be a prime of the regular local ring `A` with `A/Q` regular, `T`
part of a regular system of parameters, and `Q = (T) + (z)` with `z ∉ (T)`.  Then there is a
minimal base `T' ⊇ T ∪ {z}` of `Q` (part of a regular system of parameters, `(T') = Q`) containing `z`.
Proof: take a minimal base `T''` of `Q` containing `T`
(`exists_extendsToRSOP_span_eq_of_extendsToRSOP`); `z` has a unit coefficient on a member `i` of
`T'' ∖ T` (otherwise `Q ⊆ (T) + 𝔪Q`, so `Q = (T)` by Nakayama and `z ∈ (T)`), and `i` is replaced by `z`
in `T''` and in a regular system of parameters containing it.

Gap filled: the paper's Lemma 3 does not cover a component through `F` that does not contain `W`
(hypothesis (iii)); in the transversal case of Proposition 5 (p. 291, "with help of Lemma 3") the
generator `z` of `E_1`, which lies in `Q = P + (z)`, has to be a member of the regular system of
parameters; it plays the role of `y_1` in the minimal base of `Q`. -/
theorem exists_extendsToRSOP_insert_span_eq_of_eq_sup {A : Type u} [CommRing A]
    [IsRegularLocalRing A] (Q : Ideal A) [Q.IsPrime] (hQ : IsRegularLocalRing (A ⧸ Q))
    {T : Finset A} (hT : ExtendsToRSOP A T) {z : A}
    (hQeq : Q = Ideal.span (T : Set A) ⊔ Ideal.span {z}) (hz : z ∉ Ideal.span (T : Set A)) :
    ∃ T' : Finset A, T ⊆ T' ∧ z ∈ T' ∧ ExtendsToRSOP A T' ∧ Ideal.span (T' : Set A) = Q := by
  classical
  have hTQ : (T : Set A) ⊆ Q := fun a ha => hQeq ▸ Ideal.mem_sup_left (Ideal.subset_span ha)
  have hzQ : z ∈ Q := hQeq ▸ Ideal.mem_sup_right (Ideal.mem_span_singleton_self z)
  obtain ⟨T'', hTT'', ⟨Z, hT''Z, hZ⟩, hT''Q⟩ :=
    exists_extendsToRSOP_span_eq_of_extendsToRSOP Q hQ hT hTQ
  have hZM : ∀ y ∈ Z, y ∈ maximalIdeal A := fun y hy => hZ.1 ▸ Ideal.subset_span hy
  have hzT'' : z ∈ Ideal.span (T'' : Set A) := hT''Q ▸ hzQ
  obtain ⟨c, -, hc⟩ := Submodule.mem_span_finset.mp hzT''
  -- some coefficient on a member of `T'' ∖ T` is a unit (Nakayama)
  obtain ⟨i, hiT'', hiT, hci⟩ : ∃ i ∈ T'', i ∉ T ∧ c i ∉ maximalIdeal A := by
    by_contra hcon
    push Not at hcon
    have hz' : z ∈ Ideal.span (T : Set A) ⊔ maximalIdeal A * Q := by
      rw [← hc]
      refine Ideal.sum_mem _ fun a ha => ?_
      by_cases haT : a ∈ T
      · exact Ideal.mem_sup_left (Ideal.mul_mem_left _ _
          (Ideal.subset_span (Finset.mem_coe.mpr haT)))
      · refine Ideal.mem_sup_right ?_
        rw [smul_eq_mul]
        exact Ideal.mul_mem_mul (hcon a ha haT)
          (hT''Q ▸ Ideal.subset_span (Finset.mem_coe.mpr ha))
    have hQle : Q ≤ Ideal.span (T : Set A) ⊔ maximalIdeal A * Q := by
      conv_lhs => rw [hQeq]
      exact sup_le le_sup_left ((Ideal.span_singleton_le_iff_mem _).mpr hz')
    have hfg : (Q : Submodule A A).FG := by
      rw [← hT''Q]; exact ⟨T'', rfl⟩
    have := Submodule.le_of_le_smul_of_le_jacobson_bot (I := maximalIdeal A)
      (N := Ideal.span (T : Set A)) (N' := Q) hfg (IsLocalRing.maximalIdeal_le_jacobson ⊥) hQle
    exact hz (this hzQ)
  have hiZ : i ∈ Z := hT''Z hiT''
  have hu : IsUnit (c i) := (IsLocalRing.mem_maximalIdeal _).not.mp hci |> not_not.mp
  obtain ⟨v, hv⟩ := hu.exists_left_inv
  have hsplit : c i * i = z - ∑ a ∈ T''.erase i, c a • a := by
    rw [← hc, ← Finset.add_sum_erase T'' _ hiT'', smul_eq_mul]
    ring
  -- the exchange: `i` is replaced by `z`
  have hiT' : i ∈ Ideal.span ((insert z (T''.erase i) : Finset A) : Set A) := by
    have h1 : i = v * (z - ∑ a ∈ T''.erase i, c a • a) := by
      rw [← hsplit, ← mul_assoc, hv, one_mul]
    have key : v * (z - ∑ a ∈ T''.erase i, c a • a) ∈
        Ideal.span ((insert z (T''.erase i) : Finset A) : Set A) := by
      refine Ideal.mul_mem_left _ _ (sub_mem (Ideal.subset_span (by simp))
        (Ideal.sum_mem _ fun a ha => Ideal.mul_mem_left _ _ (Ideal.subset_span ?_)))
      rw [Finset.coe_insert]
      exact Set.mem_insert_of_mem _ (Finset.mem_coe.mpr ha)
    rwa [← h1] at key
  have hzM : z ∈ maximalIdeal A :=
    (Ideal.span_le.mpr fun t ht => hZM t (hT''Z (Finset.mem_coe.mp ht))) hzT''
  have himem : i ∈ Ideal.span ((insert z (Z.erase i) : Finset A) : Set A) :=
    Ideal.span_mono (by
      rw [Finset.coe_insert, Finset.coe_insert]
      exact Set.insert_subset_insert (fun a ha => by
        have ha' := Finset.mem_erase.mp (Finset.mem_coe.mp ha)
        exact Finset.mem_coe.mpr (Finset.mem_erase.mpr ⟨ha'.1, hT''Z ha'.2⟩))) hiT'
  have hZ'span : Ideal.span ((insert z (Z.erase i) : Finset A) : Set A) = maximalIdeal A := by
    refine le_antisymm (Ideal.span_le.mpr ?_) ?_
    · rw [Finset.coe_insert]
      exact Set.insert_subset hzM fun a ha => hZM a (Finset.mem_of_mem_erase (Finset.mem_coe.mp ha))
    · rw [← hZ.1, Ideal.span_le]
      intro y hy
      by_cases hyi : y = i
      · exact hyi ▸ himem
      · exact Ideal.subset_span (by simp [hyi, Finset.mem_coe.mp hy])
  have hZ' : IsRegularSystemOfParameters A (insert z (Z.erase i)) := by
    refine rsop_of_span_of_card_le hZ'span ?_
    have h1 := Finset.card_insert_le z (Z.erase i)
    have h2 := Finset.card_erase_add_one hiZ
    have h3 := rsop_card_eq_spanFinrank hZ
    omega
  refine ⟨insert z (T''.erase i), fun a ha => ?_, Finset.mem_insert_self _ _,
    ⟨insert z (Z.erase i), Finset.insert_subset_insert _ (Finset.erase_subset_erase i hT''Z), hZ'⟩,
    ?_⟩
  · exact Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨fun h => hiT (h ▸ ha), hTT'' ha⟩)
  · refine le_antisymm (Ideal.span_le.mpr ?_) ?_
    · rw [Finset.coe_insert]
      exact Set.insert_subset hzQ fun a ha =>
        hT''Q ▸ Ideal.subset_span (Finset.mem_coe.mpr (Finset.mem_of_mem_erase (Finset.mem_coe.mp ha)))
    · rw [← hT''Q, Ideal.span_le]
      intro a ha
      by_cases hai : a = i
      · exact hai ▸ hiT'
      · exact Ideal.subset_span (by
          rw [Finset.coe_insert]
          exact Set.mem_insert_of_mem _ (Finset.mem_coe.mpr
            (Finset.mem_erase.mpr ⟨hai, Finset.mem_coe.mp ha⟩)))

/-- If the stalk of `C` at `x ∈ F` lies in that of the irreducible `F`, then `F ⊆ C`: the generic
point of `F` specializes to `x` (the passage from "`z_j ∈ Q`" (local) to "`F ⊆ E_j`" (global) which
the paper uses silently in "(ii) and (iii) imply"). -/
theorem pts_subset_of_stalkIdeal_le_of_isIrreducible {X : Scheme.{u}} {F C : Subscheme X}
    (hFirr : F.IsIrreducible) {x : X} (hxF : x ∈ F.pts)
    (hCx : C.stalkIdeal x ≤ F.stalkIdeal x) : F.pts ⊆ C.pts := by
  have hFirr' := Subscheme.isIrreducible_pts F hFirr
  have hFcl : IsClosed F.pts := F.support.isClosed
  set η := hFirr'.genericPoint with hηdef
  have hηspec : closure {η} = F.pts := by
    rw [hFirr'.isGenericPoint_genericPoint_closure.def, hFcl.closure_eq]
  have hηF : η ∈ F.pts := by
    rw [← hηspec]
    exact subset_closure rfl
  have hηx : η ⤳ x := specializes_iff_mem_closure.mpr (by rw [hηspec]; exact hxF)
  have hηC : η ∈ C.pts := mem_pts_of_stalkIdeal_le_of_specializes hηx hηF hCx
  rw [← hηspec]
  exact closure_minimal (Set.singleton_subset_iff.mpr hηC) C.support.isClosed

/-- Each irreducible component of `E_1 ∪ ⋯ ∪ E_α` (with the `E_j` irreducible of codimension one)
is one of the `E_j`, as a set: the components of the union are the non-empty `E_j` (maximal
irreducible closed subsets). -/
theorem exists_pts_eq_of_mem_irreducibleComponents_unionFam {X : Scheme.{u}} {α : ℕ}
    (E : Fin α → Subscheme X) (hE : ∀ j, (E j).IsNonsingularIrreducibleCodimOne)
    {C : Subscheme X} (hC : C ∈ (Subscheme.unionFam E).irreducibleComponents) :
    ∃ j, C.pts = (E j).pts := by
  classical
  obtain ⟨Z, ⟨⟨hZirr, hZsub⟩, hZmax⟩, rfl⟩ := hC
  have hCpts : (Subscheme.ofClosed Z).pts = Z :=
    Scheme.IdealSheafData.coe_support_vanishingIdeal Z
  rw [hCpts]
  obtain ⟨j, hZj⟩ : ∃ j, (Z : Set X) ⊆ (E j).pts := by
    obtain ⟨z₀, hz₀, hZz₀⟩ := isIrreducible_iff_sUnion_isClosed.mp hZirr
      (Finset.univ.image fun j => (E j).pts)
      (by
        intro s hs
        obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hs
        exact (E j).support.isClosed)
      (by
        intro y hy
        obtain ⟨j, hj⟩ := (mem_pts_unionFam_iff E).mp (hZsub hy)
        exact Set.mem_sUnion.mpr ⟨(E j).pts, by simp, hj⟩)
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hz₀
    exact ⟨j, hZz₀⟩
  have hEj : (E j).pts ⊆ Z := by
    have hne : (E j).pts.Nonempty := hZirr.nonempty.mono hZj
    rcases hE j with h | ⟨-, hirr, -⟩
    · rw [h] at hne
      obtain ⟨y, hy⟩ := hne
      exact absurd hy (by
        show y ∉ ((⊤ : Subscheme X).support : Set X)
        rw [Scheme.IdealSheafData.support_top]
        exact id)
    · exact hZmax (y := ⟨(E j).pts, (E j).support.isClosed⟩)
        ⟨Subscheme.isIrreducible_pts (E j) hirr,
          fun y hy => (mem_pts_unionFam_iff E).mpr ⟨j, hy⟩⟩ hZj
  exact ⟨j, Set.Subset.antisymm hZj hEj⟩

end PrepLemma3

/-- **Lemma 3** (p. 286).  Normal crossings with `W` at the points of `F`, given normal
crossings with `F` and the containment condition (iii).

The proof follows the paper at `x ∈ F` (`R = O_{X,x}`, `P = W_x`, `Q = F_x`; the `z_j` are the
generators of the components of `E_1 ∪ ⋯ ∪ E_α` through `x`, which are the `E_j` through `x`, and the
index set is split into those with `W ⊆ E_j` (`j ≤ β`) and the others):
(1) "By (i), `(z_1, …, z_β)` can be extended to a minimal base of `P`"
(`exists_extendsToRSOP_span_eq_of_extendsToRSOP`: the `z_j`, `j ≤ β`, lie in `P` and are part of a
regular system of parameters by (i));
(2) "Since `W` is non-singular, `(z, w)` can be extended to a minimal base of `Q`" (the same lemma,
for `Q ⊇ P`, using that `R/Q` is regular);
(3) "Since `F` is non-singular, (ii) and (iii) imply that `(z, w, y, z_{β+1}, …, z_α)` can be
extended to a regular system of parameters of `R`"
(`exists_extendsToRSOP_union_of_quotient_of_subset`: by (ii) the `z_j` are in a regular system of
parameters `z'` in which `Q` is generated by a part `t`; for `j > β` the generator `z_j` is not in
`Q`, because `z_j ∈ Q` forces `F ⊆ E_j` (the generic point of `F` specializes to `x`,
`pts_subset_of_stalkIdeal_le_of_isIrreducible`), hence `W ⊆ E_j` by (iii));
(4) "It follows that `E_1 ∪ ⋯ ∪ E_α` has only normal crossings with `W` at `x`".

Gaps filled: the passage from `z_j ∈ Q` (local) to `F ⊆ E_j` (global), implicit in "(ii) and (iii)
imply"; that the components through `x` are the `E_j` through `x`
(`exists_pts_eq_of_mem_irreducibleComponents_unionFam`); and the independence statements behind
"can be extended to a minimal base" (a minimal base of `P` extending a part of a regular system of
parameters).  Encoding: the `E_j` are replaced by the components of the union through `x`
(equal to them as sets), the repetition of the `E_j` being irrelevant for the generating elements. -/
@[blueprint "lem:IV.2-3"
  (statement := /-- \textbf{Lemma 3.} Let $X$ be a non-singular irreducible algebraic
    scheme, $W$ and $F$ non-singular irreducible subschemes of $X$ such that $F\subseteq W$.
    Let $E_1,\dots,E_\alpha$ be non-singular irreducible subschemes of codimension $1$ of
    $X$ such that:
    \begin{enumerate}
      \item[(i)] $E_1\cup\dots\cup E_\alpha$ has only normal crossings,
      \item[(ii)] $E_1\cup\dots\cup E_\alpha$ has only normal crossings with $F$, and
      \item[(iii)] any $E_j$ containing $F$ contains $W$.
    \end{enumerate}
    Then $E_1\cup\dots\cup E_\alpha$ has only normal crossings with $W$ at every point of
    $F$. (p.~286.)
    (Formalization note (encoding): the family $E_1,\dots,E_\alpha$ is a map
    $E\colon\mathrm{Fin}\,\alpha\to\mathrm{Subscheme}\,X$ and
    $\bigcup_jE_j$ is $\bigsqcap_jE_j$, the meet of the ideal sheaves; the $E_j$ are allowed
    to be empty and to repeat, per the agreement of pp.~274--275.) -/)
  (proof := /-- Let $x$ be any point of $F$. Let $R$ be the local ring of $X$ at $x$, $P$ the
    prime ideal of $W$ in $R$, and $Q$ the prime ideal of $F$ in $R$. We arrange the indices
    of the $E_j$ in such a way that $W\subseteq E_j$ for $1\le j\le\beta$ and
    $W\not\subseteq E_j$ for $j>\beta$, where $0\le\beta\le\alpha$. To prove that
    $E_1\cup\dots\cup E_\alpha$ has only normal crossings with $W$ at $x$, we may assume that
    $x\in E_j$ for $1\le j\le\alpha$. Let $z_j$ be an element of $R$ which generates the
    prime ideal of $E_j$ in $R$. By (i), $(z_1,\dots,z_\beta)$ can be extended to a minimal
    base of $P$, say $(z_1,\dots,z_\beta,w_1,\dots,w_s)$ where $\beta+s=$ the codimension of
    $W$ in $X$. Since $W$ is non-singular, $(z_1,\dots,z_\beta,w_1,\dots,w_s)$ can be
    extended to a minimal base of $Q$, say $(z_1,\dots,z_\beta,w_1,\dots,w_s,y_1,\dots,y_t)$.
    Since $F$ is non-singular, (ii) and (iii) imply that
    $(z_1,\dots,z_\beta,w_1,\dots,w_s,y_1,\dots,y_t,z_{\beta+1},\dots,z_\alpha)$ can be
    extended to a regular system of parameters of $R$. It follows that
    $E_1\cup\dots\cup E_\alpha$ has only normal crossings with $W$ at $x$, i.e., at every
    point of $F$. \textsc{q.e.d.}

    \textbf{Gaps filled.} The proof is formalized step by step as printed, with the components of
    $E_1\cup\dots\cup E_\alpha$ through $x$ (which are the $E_j$ through $x$, as sets) in place of
    the indexed $E_j$, and the generators $z_j$ taken from the regular systems of parameters
    given by (i) and (ii). (1) ``$(z_1,\dots,z_\beta)$ can be extended to a minimal base of
    $P$'': the $z_j$, $j\le\beta$, lie in $P$ (as $W\subseteq E_j$) and are part of a regular
    system of parameters by (i); modulo the prime they generate, $P$ is generated by part of a
    regular system of parameters of the (regular) quotient, since $R/P$ is regular; lifting gives
    the minimal base. (2) The same argument for $Q\supseteq P$, with $R/Q$ regular. (3) By (ii)
    the $z_j$ lie in a regular system of parameters in which $Q$ is generated by a part; for
    $j>\beta$ the generator $z_j$ does not lie in $Q$ (the paper uses this tacitly in ``(ii) and
    (iii) imply''): if $z_j\in Q$, the generic point of $F$, which specializes to $x$, lies on
    $E_j$, so $F\subseteq E_j$ (as $F$ is reduced), hence $W\subseteq E_j$ by (iii),
    contradicting $j>\beta$. So the residues of the $z_j$, $j>\beta$, are part of a regular
    system of parameters of $R/Q$, and adjoining them to the minimal base of $Q$ gives a part of
    a regular system of parameters of $R$. (4) The conclusion is then immediate: the minimal
    base of $P$ and the generators of all components lie in this regular system of parameters.
    Hypotheses ``$X$ algebraic, irreducible'' and ``$W$ irreducible'' are not used.

    \textbf{Deviation from the paper (statement modified).} Proposition~5
    (\cref{prop:IV.2-5}) uses the lemma in two pointwise forms, with hypotheses only at the point
    and without the irreducibility of $W$ and $F$ or the global non-singularity of $W$: for step
    (4), with a transversality $F_x=W_x+E_{1,x}$ in place of (iii) for $E_1$
    (\texttt{Subscheme.hasOnlyNormalCrossingsWithAt\_unionFam\_of\_transversal}), and for condition
    (2) of the first reduction, with (iii) for the prime of $F$ at the point
    (\texttt{Subscheme.hasOnlyNormalCrossingsWithAt\_unionFam\_of\_prime\_flag}). Both are proved
    along the printed chain (minimal base of $P$, minimal base of $Q$, adjoin the remaining $z_j$): the
    first at a point, with the regular system of parameters of (ii) in place of that of (i) and with
    (iii) read on the stalks, the second with the generator $z$ of $E_1$ (which lies in $Q=P+(z)$ but
    not in $P$) adjoined to the minimal base of $Q$ by an exchange
    (\texttt{exists\_extendsToRSOP\_insert\_span\_eq\_of\_eq\_sup}). -/)
  (latexEnv := "lemma")]
theorem hasOnlyNormalCrossingsWithAt_unionFam_of_isContainedIn {X : Scheme.{u}} (_hXalg : IsAlgebraicScheme X) (hXns : X.IsNonsingular)
    (_hXirr : IrreducibleSpace X) (W F : Subscheme X)
    (hWns : W.IsNonsingular) (_hWirr : W.IsIrreducible)
    (hFns : F.IsNonsingular) (hFirr : F.IsIrreducible) (hFW : F.IsContainedIn W)
    (α : ℕ) (E : Fin α → Subscheme X)
    (hE : ∀ j, (E j).IsNonsingularIrreducibleCodimOne)
    (hi : (Subscheme.unionFam E).HasOnlyNormalCrossings)
    (hii : (Subscheme.unionFam E).HasOnlyNormalCrossingsWith F)
    (hiii : ∀ j, F.IsContainedIn (E j) → W.IsContainedIn (E j)) :
    ∀ x ∈ F.pts, (Subscheme.unionFam E).HasOnlyNormalCrossingsWithAt W x := by
  intro x hxF
  classical
  have : IsRegularLocalRing (X.presheaf.stalk x) := hXns x
  have hxW : x ∈ W.pts := pts_subset_of_isContainedIn hFW hxF
  -- `P` the prime ideal of `W` in `R`, `Q` the prime ideal of `F` in `R`
  obtain ⟨hPprime, hPreg⟩ := isPrime_and_isRegularLocalRing_quotient_of_isNonsingular W hWns hxW
  obtain ⟨hQprime, hQreg⟩ := isPrime_and_isRegularLocalRing_quotient_of_isNonsingular F hFns hxF
  have hPQ : W.stalkIdeal x ≤ F.stalkIdeal x := Subscheme.stalkIdeal_mono (fun U => hFW U) x
  -- the components `E_j` through `x` are generated by elements of regular systems of parameters:
  -- by (i) (in `z₀`) and by (ii) (in `z₁`, in which `Q` is generated by a part `t`)
  obtain ⟨z₀, hz₀, hcomp₀, -⟩ := hi x
  obtain ⟨z₁, hz₁, hcomp₁, t, htz₁, hFt⟩ := hii x hxF
  -- "We arrange the indices ... `W ⊆ E_j` for `1 ≤ j ≤ β` and `W ⊄ E_j` for `j > β`":
  -- the generators `z_1, …, z_β` and `z_{β+1}, …, z_α`
  set Gβ : Finset (X.presheaf.stalk x) := z₀.filter fun a => ∃ C ∈ (Subscheme.unionFam E).irreducibleComponents,
    x ∈ C.pts ∧ W.pts ⊆ C.pts ∧ C.stalkIdeal x = Ideal.span {a} with hGβ
  set Gγ : Finset (X.presheaf.stalk x) := z₁.filter fun a => ∃ C ∈ (Subscheme.unionFam E).irreducibleComponents,
    x ∈ C.pts ∧ ¬ W.pts ⊆ C.pts ∧ C.stalkIdeal x = Ideal.span {a} with hGγ
  -- `z_j ∈ P` for `j ≤ β` (as `W ⊆ E_j`)
  have hGβP : (Gβ : Set (X.presheaf.stalk x)) ⊆ W.stalkIdeal x := by
    intro a ha
    obtain ⟨C, -, -, hWC, hCa⟩ := (Finset.mem_filter.mp (Finset.mem_coe.mp ha)).2
    have hWC' : W.IsContainedIn C :=
      isContainedIn_of_pts_subset_of_isReduced_toScheme (isReduced_toScheme_of_isNonsingular W hWns) hWC
    have := Subscheme.stalkIdeal_mono (fun U => hWC' U) x
    rw [hCa] at this
    exact this (Ideal.mem_span_singleton_self a)
  -- `z_j ∉ Q` for `j > β` (by (iii): `z_j ∈ Q` would give `F ⊆ E_j`, hence `W ⊆ E_j`)
  have hGγQ : ∀ a ∈ Gγ, a ∉ F.stalkIdeal x := by
    intro a ha haQ
    obtain ⟨C, hC, -, hWC, hCa⟩ := (Finset.mem_filter.mp ha).2
    have hCx : C.stalkIdeal x ≤ F.stalkIdeal x := by
      rw [hCa]
      exact (Ideal.span_singleton_le_iff_mem _).mpr haQ
    have hFC : F.pts ⊆ C.pts := pts_subset_of_stalkIdeal_le_of_isIrreducible hFirr hxF hCx
    obtain ⟨j, hCj⟩ := exists_pts_eq_of_mem_irreducibleComponents_unionFam E hE hC
    have hFE : F.IsContainedIn (E j) := isContainedIn_of_pts_subset_of_isReduced_toScheme
      (isReduced_toScheme_of_isNonsingular F hFns) (hCj ▸ hFC)
    exact hWC (hCj ▸ pts_subset_of_isContainedIn (hiii j hFE))
  -- (1) "By (i), `(z_1, …, z_β)` can be extended to a minimal base of `P`"
  have hGβe : ExtendsToRSOP (X.presheaf.stalk x) Gβ :=
    (ExtendsToRSOP.of_isRegularSystemOfParameters hz₀).mono (Finset.filter_subset _ _)
  obtain ⟨T, hGβT, hTe, hTP⟩ := exists_extendsToRSOP_span_eq_of_extendsToRSOP (W.stalkIdeal x)
    hPreg hGβe hGβP
  -- (2) "Since `W` is non-singular, `(z, w)` can be extended to a minimal base of `Q`"
  have hTQ : (T : Set (X.presheaf.stalk x)) ⊆ F.stalkIdeal x := fun a ha =>
    hPQ (hTP ▸ Ideal.subset_span ha)
  obtain ⟨T', hTT', hT'e, hT'Q⟩ := exists_extendsToRSOP_span_eq_of_extendsToRSOP (F.stalkIdeal x)
    hQreg hTe hTQ
  -- (3) "Since `F` is non-singular, (ii) and (iii) imply that `(z, w, y, z_{β+1}, …, z_α)` can be
  -- extended to a regular system of parameters of `R`"
  have hext : ExtendsToRSOP (X.presheaf.stalk x) (T' ∪ Gγ) :=
    exists_extendsToRSOP_union_of_quotient_of_subset (F.stalkIdeal x) hT'e hT'Q hz₁ htz₁ hFt.symm
      (Finset.filter_subset _ _) hGγQ
  obtain ⟨Z, hUZ, hZ⟩ := hext
  -- (4) "It follows that `E_1 ∪ ⋯ ∪ E_α` has only normal crossings with `W` at `x`"
  refine ⟨Z, hZ, fun C hC hxC => ?_, T, fun a ha => hUZ (Finset.mem_union_left _ (hTT' ha)),
    hTP.symm⟩
  by_cases hWC : W.pts ⊆ C.pts
  · obtain ⟨a, haz, hCa⟩ := hcomp₀ C hC hxC
    have haG : a ∈ Gβ := Finset.mem_filter.mpr ⟨haz, C, hC, hxC, hWC, hCa⟩
    exact ⟨a, hUZ (Finset.mem_union_left _ (hTT' (hGβT haG))), hCa⟩
  · obtain ⟨a, haz, hCa⟩ := hcomp₁ C hC hxC
    have haG : a ∈ Gγ := Finset.mem_filter.mpr ⟨haz, C, hC, hxC, hWC, hCa⟩
    exact ⟨a, hUZ (Finset.mem_union_right _ haG), hCa⟩

/-! ### Local computation in the chart `R' = R[P/z_t]` (used in Lemma 4) -/

section PrepChartAlgebra

open IsLocalRing

variable {R : Type u} [CommRing R] [IsRegularLocalRing R] [IsDomain R] {P : Ideal R}

open Classical in
/-- Saturation of the ideal `(S) R'`, `S ⊆ T`, `(T) = P`, in the chart `R' = R[P/z_t]`
(an analogue of `MonoidalTransform.saturation_span_prod` for ideals generated by a part of a
regular system of parameters, not by a product): `⋃ₙ ((S)R' : z_tⁿ)` is `(1)` if `z_t ∈ S`,
and `(z'_s : s ∈ S)` otherwise. -/
theorem MonoidalTransform.saturation_span_eq_ite (s : MonoidalTransform R P) {Z T S : Finset R}
    (hZ : IsRegularSystemOfParameters R Z) (hTZ : T ⊆ Z) (hT : Ideal.span (T : Set R) = P)
    (hST : S ⊆ T) {zt : R} {φ : R → s.ring} (hzt : zt ∈ T)
    (hφ₂ : φ zt = s.toRing zt)
    (hφ₃ : ∀ z ∈ T, z ≠ zt → s.toRing zt * φ z = s.toRing z)
    (hinj : Set.InjOn φ {z | z ∈ Z ∧ φ z ∈ maximalIdeal s.ring})
    (hext : ExtendsToRSOP s.ring ((Z.filter fun z => φ z ∈ maximalIdeal s.ring).image φ)) :
    ⨆ n : ℕ, ((Ideal.span (S : Set R)).map s.toRing).colon
        ((Ideal.span {s.toRing zt} ^ n : Ideal s.ring) : Set s.ring) =
      if zt ∈ S then ⊤ else Ideal.span (φ '' (S : Set R)) := by
  classical
  have hZ' := ExtendsToRSOP.of_isRegularSystemOfParameters hZ
  have hTe : ExtendsToRSOP R T := hZ'.mono hTZ
  have hPp : P.IsPrime := hT ▸ hTe.isPrime_span
  have hS : IsRegularLocalRing (R ⧸ P) := hT ▸ hTe.isRegularLocalRing_quotient
  have hP0 : P ≠ ⊥ := fun h => s.x_ne_zero (by simpa [h] using s.x_mem)
  have : IsRegularLocalRing s.ring := (s.isRegularLocalRing_and_isLocalHom_and_span_xR_eq_map hPp hP0 hS).1
  have := isDomain_of_isRegularLocalRing s.ring
  set y := s.toRing zt with hy
  have hy0 : y ≠ 0 := fun h => hTe.ne_zero hzt (s.toRing_injective (h.trans (map_zero _).symm))
  have hZM : ∀ z ∈ Z, s.toRing z ∈ maximalIdeal s.ring := fun z hz =>
    map_nonunit s.toRing _ (hZ'.mem_maximalIdeal hz)
  by_cases hztS : zt ∈ S
  · simp only [hztS, ↓reduceIte]
    refine top_le_iff.mp (le_trans ?_ (le_iSup _ 1))
    intro a _
    refine Submodule.mem_colon.mpr fun p hp => ?_
    rw [pow_one, SetLike.mem_coe, Ideal.mem_span_singleton'] at hp
    obtain ⟨c, rfl⟩ := hp
    have : y ∈ (Ideal.span (S : Set R)).map s.toRing :=
      Ideal.mem_map_of_mem _ (Ideal.subset_span hztS)
    rw [smul_eq_mul, show a * (c * y) = (a * c) * y by ring]
    exact Ideal.mul_mem_left _ _ this
  · simp only [hztS, ↓reduceIte]
    set I0 : Ideal s.ring := Ideal.span (φ '' (S : Set R)) with hI0
    have hgen : ∀ z ∈ S, s.toRing z = y * φ z := fun z hz =>
      (hφ₃ z (hST hz) (fun h => hztS (h ▸ hz))).symm
    have hQR : (Ideal.span (S : Set R)).map s.toRing = Ideal.span {y} * I0 := by
      rw [Ideal.map_span, hI0, Ideal.span_mul_span]
      apply le_antisymm
      · refine Ideal.span_le.mpr ?_
        rintro _ ⟨z, hz, rfl⟩
        exact Ideal.subset_span (Set.mem_mul.mpr ⟨y, rfl, φ z, ⟨z, hz, rfl⟩, (hgen z hz).symm⟩)
      · refine Ideal.span_le.mpr ?_
        rintro _ ⟨_, rfl, _, ⟨z, hz, rfl⟩, rfl⟩
        exact Ideal.subset_span ⟨z, hz, (hgen z hz)⟩
    have key : ∀ (a : s.ring) (n : ℕ), a * y ^ n ∈ I0 → a ∈ I0 := by
      intro a n ha
      by_cases hunit : ∃ z ∈ S, φ z ∉ maximalIdeal s.ring
      · obtain ⟨z, hz, hzu⟩ := hunit
        have : I0 = ⊤ := Ideal.eq_top_of_isUnit_mem _ (Ideal.subset_span ⟨z, hz, rfl⟩)
          ((IsLocalRing.mem_maximalIdeal _).not.mp hzu |> not_not.mp)
        rw [this]; exact trivial
      · push Not at hunit
        have hSZ : ∀ z ∈ S, z ∈ Z := fun z hz => hTZ (hST hz)
        set L := S.image φ with hL
        have hLK : L ⊆ (Z.filter fun z => φ z ∈ maximalIdeal s.ring).image φ := by
          intro l hl
          obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hl
          exact Finset.mem_image_of_mem φ (Finset.mem_filter.mpr ⟨hSZ z hz, hunit z hz⟩)
        have hytop : y ∈ (Z.filter fun z => φ z ∈ maximalIdeal s.ring).image φ :=
          Finset.mem_image.mpr ⟨zt, Finset.mem_filter.mpr
            ⟨hTZ hzt, by rw [hφ₂]; exact hZM _ (hTZ hzt)⟩, hφ₂⟩
        have hyL : y ∉ Ideal.span (L : Set s.ring) := by
          obtain ⟨Z0, hKZ0, hZ0⟩ := hext
          refine rsop_notMem_span hZ0 (hLK.trans hKZ0) (hKZ0 hytop) ?_
          intro hyl
          obtain ⟨z, hz, hzy⟩ := Finset.mem_image.mp hyl
          have := hinj ⟨hSZ z hz, hunit z hz⟩
            ⟨hTZ hzt, by rw [hφ₂]; exact hZM _ (hTZ hzt)⟩ (hzy.trans hφ₂.symm)
          exact hztS (this ▸ hz)
        have hpr := (hext.mono hLK).isPrime_span
        have hI0L : I0 = Ideal.span (L : Set s.ring) := by
          rw [hI0, hL, Finset.coe_image]
        rw [hI0L] at ha ⊢
        exact (Ideal.IsPrime.mem_or_mem hpr ha).resolve_right fun h => hyL (hpr.mem_of_pow_mem n h)
    apply le_antisymm
    · refine iSup_le fun n a ha => ?_
      have h1 := Submodule.mem_colon.mp ha (y ^ n)
        (by rw [Ideal.span_singleton_pow]; exact Ideal.mem_span_singleton_self _)
      rw [hQR] at h1
      -- `yⁿ a ∈ (y) I0 ⊆ I0`
      have h2 : a • y ^ n ∈ I0 :=
        (Ideal.mul_le_right : Ideal.span {y} * I0 ≤ I0) h1
      exact key a n h2
    · refine le_iSup_of_le 1 fun a ha => Submodule.mem_colon.mpr fun p hp => ?_
      rw [pow_one, SetLike.mem_coe, Ideal.mem_span_singleton'] at hp
      obtain ⟨c, rfl⟩ := hp
      rw [smul_eq_mul, hQR, show a * (c * y) = y * (a * c) by ring]
      exact Ideal.mul_mem_mul (Ideal.mem_span_singleton_self _) (Ideal.mul_mem_right _ _ ha)

end PrepChartAlgebra

section PrepChart

open IsLocalRing

variable {X : Scheme.{u}} {B : Subscheme X}

open Classical in
/-- The chart computation of p. 169 (`DatumTransform.exists_chart`) with two more pieces of
information: the relation `z'_t · z'_z = z` for the generators `z ∈ T` of the center
(`z'_z = z / z_t`), and the strict transform of a subscheme whose ideal at `f(y)` is generated by
a subset `S ⊆ T` (it is `(1)` if `z_t ∈ S` and `(z'_z : z ∈ S)` otherwise). -/
theorem MonoidalTransformation.exists_chart_strictTransform_stalkIdeal (hX : X.IsNonsingular)
    (t : MonoidalTransformation X B) (y : t.X')
    [IsRegularLocalRing (t.X'.presheaf.stalk y)]
    {Z T : Finset (X.presheaf.stalk (t.f y))}
    (hZ : IsRegularSystemOfParameters (X.presheaf.stalk (t.f y)) Z) (hTZ : T ⊆ Z)
    (hBT : B.stalkIdeal (t.f y) = Ideal.span (T : Set (X.presheaf.stalk (t.f y)))) :
    ∃ (zt : X.presheaf.stalk (t.f y)) (φ : X.presheaf.stalk (t.f y) → t.X'.presheaf.stalk y),
      zt ∈ T ∧ t.exceptional.stalkIdeal y = Ideal.span {φ zt} ∧
      φ zt ∈ maximalIdeal (t.X'.presheaf.stalk y) ∧ φ zt = t.f.stalkMap y zt ∧
      (∀ z ∈ T, z ≠ zt → φ zt * φ z = t.f.stalkMap y z) ∧
      Set.InjOn φ {z | z ∈ Z ∧ φ z ∈ maximalIdeal (t.X'.presheaf.stalk y)} ∧
      ExtendsToRSOP (t.X'.presheaf.stalk y)
        ((Z.filter fun z => φ z ∈ maximalIdeal (t.X'.presheaf.stalk y)).image φ) ∧
      (∀ J ⊆ Z, ∀ V : Subscheme X, V.stalkIdeal (t.f y) = Ideal.span {(∏ z ∈ J, z)} →
        (Subscheme.strictTransform t V).stalkIdeal y =
          Ideal.span {(∏ z ∈ (J.erase zt).filter
            (fun z => φ z ∈ maximalIdeal (t.X'.presheaf.stalk y)), φ z)}) ∧
      (∀ S ⊆ T, ∀ V : Subscheme X, V.stalkIdeal (t.f y) = Ideal.span (S : Set _) →
        (Subscheme.strictTransform t V).stalkIdeal y =
          if zt ∈ S then ⊤ else Ideal.span (φ '' (S : Set _))) := by
  have : IsRegularLocalRing (X.presheaf.stalk (t.f y)) := hX _
  have := isDomain_of_isRegularLocalRing (X.presheaf.stalk (t.f y))
  obtain ⟨s, e, he⟩ := t.exists_monoidalTransform_stalk y
  have : IsRegularLocalRing s.ring := IsRegularLocalRing.of_ringEquiv e.symm
  obtain ⟨zt, φ, hzt, hspan, hφ₁, hφ₂, hφ₃, hinj, hext⟩ :=
    MonoidalTransform.exists_rsop_transform s hZ hTZ hBT.symm
  have hm := DatumTransform.mem_maximalIdeal_ringEquiv e
  have htot := t.stalkIdeal_totalTransform_eq_map y s e he
  have hexc : t.exceptional.stalkIdeal y = (Ideal.span {s.toRing zt}).map e := by
    rw [MonoidalTransformation.exceptional, htot, ← hspan]
  have hfilt : ∀ K : Finset (X.presheaf.stalk (t.f y)),
      (K.filter fun z => e (φ z) ∈ maximalIdeal (t.X'.presheaf.stalk y)) =
        K.filter fun z => φ z ∈ maximalIdeal s.ring :=
    fun K => Finset.filter_congr fun z _ => hm (φ z)
  refine ⟨zt, fun z => e (φ z), hzt, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hexc, Ideal.map_span, Set.image_singleton]
    show Ideal.span {e (s.toRing zt)} = Ideal.span {e (φ zt)}
    rw [hφ₂]
  · rw [hm, hφ₂]
    have hztm : zt ∈ maximalIdeal (X.presheaf.stalk (t.f y)) :=
      hZ.1 ▸ Ideal.subset_span (hTZ hzt)
    exact map_nonunit s.toRing zt hztm
  · show e (φ zt) = (t.f.stalkMap y).hom zt
    rw [hφ₂, ← he]
    rfl
  · intro z hz hne
    show e (φ zt) * e (φ z) = (t.f.stalkMap y).hom z
    rw [← map_mul, hφ₂, hφ₃ z hz hne, ← he]
    rfl
  · intro a ha b hb hab
    exact hinj ⟨ha.1, (hm _).mp ha.2⟩ ⟨hb.1, (hm _).mp hb.2⟩ (e.injective hab)
  · have := ExtendsToRSOP.map_ringEquiv e hext
    rw [Finset.image_image] at this
    rw [hfilt]
    exact this
  · intro J hJZ V hV
    rw [Subscheme.strictTransform_stalkIdeal, hexc, htot, hV]
    have hsat := MonoidalTransform.saturation_span_prod s hZ hTZ hBT.symm hJZ hzt hspan hφ₁ hφ₂
      hφ₃ hinj hext
    rw [hfilt, ← map_prod e]
    have h2 : Ideal.span {e (∏ z ∈ (J.erase zt).filter fun z => φ z ∈ maximalIdeal s.ring, φ z)} =
        (Ideal.span {∏ z ∈ (J.erase zt).filter fun z => φ z ∈ maximalIdeal s.ring, φ z}).map e := by
      rw [Ideal.map_span, Set.image_singleton]
    rw [h2, ← hsat, Ideal.map_iSup]
    refine iSup_congr fun n => ?_
    rw [Ideal.map_colon_ringEquiv, Ideal.map_pow, Ideal.map_span s.toRing, Set.image_singleton]
  · intro S hST V hV
    rw [Subscheme.strictTransform_stalkIdeal, hexc, htot, hV]
    have hsat := MonoidalTransform.saturation_span_eq_ite s hZ hTZ hBT.symm hST hzt hφ₂ hφ₃ hinj hext
    have hmap : (if zt ∈ S then (⊤ : Ideal s.ring) else Ideal.span (φ '' (S : Set _))).map e =
        if zt ∈ S then ⊤ else Ideal.span ((fun z => e (φ z)) '' (S : Set _)) := by
      split_ifs
      · exact Ideal.map_top _
      · rw [Ideal.map_span, Set.image_image]
    rw [← hmap, ← hsat, Ideal.map_iSup]
    refine iSup_congr fun n => ?_
    rw [Ideal.map_colon_ringEquiv, Ideal.map_pow]

end PrepChart

/-- Stalks commute with sums (joins) of sheaves of ideals. -/
theorem Subscheme.stalkIdeal_sup_eq {X : Scheme.{u}} (I J : Subscheme X) (x : X) :
    (I ⊔ J).stalkIdeal x = I.stalkIdeal x ⊔ J.stalkIdeal x := by
  obtain ⟨W, hx⟩ := Subscheme.exists_affineOpen_mem x
  rw [Subscheme.stalkIdeal_eq_map_germ_affine _ W hx, Subscheme.stalkIdeal_eq_map_germ_affine _ W hx,
    Subscheme.stalkIdeal_eq_map_germ_affine _ W hx, Scheme.IdealSheafData.ideal_sup, Pi.sup_apply,
    Ideal.map_sup]

section Prep4
open IsLocalRing Classical

variable {X : Scheme.{u}}

/-- Step A of the proof of Lemma 4: stalks of `E_1' ∪ ⋯ ∪ E_α' ∪ E'` are generated by products of
parts of regular systems of parameters (copy of `DatumTransform.isDatum_transform_datumII`'s `hU`, using `DatumTransform.exists_extendsToRSOP_stalkIdeal_family`). -/
private theorem exists_extendsToRSOP_stalkIdeal_union_exceptional {B : Subscheme X}
    (hXns : X.IsNonsingular) (hBns : B.IsNonsingular)
    (t : MonoidalTransformation X B) {α : ℕ} (E : Fin α → Subscheme X)
    (hE : ∀ j, (E j).IsNonsingularIrreducibleCodimOne)
    (hi : (Subscheme.unionFam E).HasOnlyNormalCrossings)
    (hiiB : (Subscheme.unionFam E).HasOnlyNormalCrossingsWith B) (y : t.X') :
    ∃ K : Finset (t.X'.presheaf.stalk y), ExtendsToRSOP _ K ∧
      ((Subscheme.unionFam fun j => Subscheme.strictTransform t (E j)).union
        t.exceptional).stalkIdeal y = Ideal.span {∏ k ∈ K, k} := by
  have : IsRegularLocalRing (t.X'.presheaf.stalk y) := (t.isNonsingular_and_isNonsingular_exceptional hXns hBns).1 y
  have hdata := DatumTransform.exists_rsop_adapted_of_isDatum (B := B) E hXns hE hi hiiB
  obtain ⟨K, hK, ⟨K₀, hK₀, -, hexc⟩, hE'⟩ := DatumTransform.exists_extendsToRSOP_stalkIdeal_family hXns hBns t E hdata y
  choose L hL _ hLe using hE'
  have hLU : Finset.univ.biUnion L ⊆ K := Finset.biUnion_subset.mpr fun i _ => hL i
  refine ⟨Finset.univ.biUnion L ∪ K₀, hK.mono (Finset.union_subset hLU hK₀), ?_⟩
  show ((Subscheme.unionFam fun j => Subscheme.strictTransform t (E j)) ⊓
    t.exceptional).stalkIdeal y = _
  rw [Subscheme.stalkIdeal_inf_eq, Subscheme.unionFam, DatumTransform.stalkIdeal_iInf_fintype, hexc,
    ← DatumTransform.span_prod_inf_of_subset hK hLU hK₀, ← DatumTransform.iInf_span_prod_of_subset hK L hL]
  exact congrArg (· ⊓ _) (iInf_congr hLe)

/-- Step B: the local statement at a point `y ∈ W'`. -/
private theorem exists_extendsToRSOP_of_mem_pts_strictTransform {B : Subscheme X}
    (hXns : X.IsNonsingular)
    (W : Subscheme X) (hWns : W.IsNonsingular) (hBns : B.IsNonsingular) (hBW : B.IsContainedIn W)
    (t : MonoidalTransformation X B) {α : ℕ} (E : Fin α → Subscheme X)
    (hE : ∀ j, (E j).IsNonsingularIrreducibleCodimOne)
    (hiiW : (Subscheme.unionFam E).HasOnlyNormalCrossingsWith W)
    (hiiB : (Subscheme.unionFam E).HasOnlyNormalCrossingsWith B)
    (y : t.X') (hy : y ∈ (Subscheme.strictTransform t W).pts) :
    ∃ K : Finset (t.X'.presheaf.stalk y), ExtendsToRSOP _ K ∧
      (∃ K₁ ⊆ K, ((Subscheme.unionFam fun j => Subscheme.strictTransform t (E j)).union
          t.exceptional).stalkIdeal y = Ideal.span {∏ k ∈ K₁, k}) ∧
      (∃ T ⊆ K, (Subscheme.strictTransform t W).stalkIdeal y = Ideal.span (T : Set _)) ∧
      (∃ K₀ ⊆ K, K₀.card ≤ 1 ∧ t.exceptional.stalkIdeal y = Ideal.span {∏ k ∈ K₀, k}) := by
  classical
  have hX' := (t.isNonsingular_and_isNonsingular_exceptional hXns hBns).1
  have : IsRegularLocalRing (t.X'.presheaf.stalk y) := hX' y
  have : IsRegularLocalRing (X.presheaf.stalk (t.f y)) := hXns _
  have hxW : t.f y ∈ W.pts := MonoidalTransformation.pts_strictTransform_subset t W hy
  by_cases hxB : t.f y ∈ B.pts
  · ------------------------------------------------------------------ on the centre
    obtain ⟨ZW, hZW, ⟨tW, htWZ, hWt⟩, hEW⟩ :=
      DatumTransform.exists_rsop_of_hasOnlyNormalCrossingsWithAt E hE (fun i => iInf_le _ i) (hiiW _ hxW)
    obtain ⟨ZB, hZB, ⟨tB, htBZ, hBt⟩, hEB⟩ :=
      DatumTransform.exists_rsop_of_hasOnlyNormalCrossingsWithAt E hE (fun i => iInf_le _ i) (hiiB _ hxB)
    obtain ⟨hWp, -⟩ := isPrime_and_isRegularLocalRing_quotient_of_isNonsingular W hWns hxW
    obtain ⟨hBp, -⟩ := isPrime_and_isRegularLocalRing_quotient_of_isNonsingular B hBns hxB
    have hQP : W.stalkIdeal (t.f y) ≤ B.stalkIdeal (t.f y) :=
      Subscheme.stalkIdeal_mono (fun U => hBW U) _
    let C : Finset (X.presheaf.stalk (t.f y)) :=
      ZB.filter fun b => ∃ j, (E j).stalkIdeal (t.f y) = Ideal.span {b}
    obtain ⟨Z, hZ, hCZ, tP, htPZ, hPt, tQ, htQ, hQt⟩ :=
      exists_rsop_adapted_to_flag (W.stalkIdeal (t.f y)) (B.stalkIdeal (t.f y)) hQP ZB tB ZW tW C
        hZB htBZ hBt hZW htWZ hWt
        (Finset.filter_subset _ _) (by
          intro c hc _
          obtain ⟨-, j, hj⟩ := Finset.mem_filter.mp hc
          rcases hEW j with h | ⟨a, ha, haj⟩
          · exfalso; rw [hj, Ideal.span_singleton_eq_top] at h
            exact (IsLocalRing.mem_maximalIdeal c).mp
              (hZB.1 ▸ Ideal.subset_span (Finset.mem_filter.mp hc).1) h
          · exact ⟨a, ha, hj.symm.trans haj⟩)
    obtain ⟨zt, φ, hzt, hexc, hztm, -, hrel, hinj, hext, hstP, hstS⟩ :=
      MonoidalTransformation.exists_chart_strictTransform_stalkIdeal hXns t y hZ htPZ hPt
    set m' := maximalIdeal (t.X'.presheaf.stalk y)
    set K := (Z.filter fun z => φ z ∈ m').image φ with hKdef
    -- `Q' = W'_y` is generated by the `z_s' ` (`s` in the part `tQ` of the system generating `Q`)
    have hW'' : zt ∉ tQ ∧ (tQ.image φ ⊆ K) ∧
        (Subscheme.strictTransform t W).stalkIdeal y = Ideal.span ((tQ.image φ : Finset _) : Set _) := by
      have h1 := hstS tQ htQ W hQt
      have hne : (Subscheme.strictTransform t W).stalkIdeal y ≠ ⊤ :=
        Subscheme.mem_pts_iff_stalkIdeal_ne_top.mp hy
      rw [h1] at hne
      have hztQ : zt ∉ tQ := fun h => hne (by simp [h])
      simp only [hztQ, ↓reduceIte] at h1 hne
      -- every `φ z`, `z ∈ tQ`, is a non-unit (else the span is `⊤`)
      have hnu : ∀ z ∈ tQ, φ z ∈ m' := by
        intro z hz; by_contra h
        exact hne (Ideal.eq_top_of_isUnit_mem _ (Ideal.subset_span ⟨z, hz, rfl⟩)
          ((IsLocalRing.mem_maximalIdeal _).not.mp h |> not_not.mp))
      refine ⟨hztQ, ?_, by rw [h1, Finset.coe_image]⟩
      intro k hk
      obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hk
      exact Finset.mem_image_of_mem φ (Finset.mem_filter.mpr ⟨htPZ (htQ hz), hnu z hz⟩)
    set T : Finset (t.X'.presheaf.stalk y) := tQ.image φ with hTdef
    -- Claim (a) of the paper: `z_j' = z_j / w` generates the prime of `E_j'` when it is a
    -- non-unit (and `E_j'` does not pass through `x'` otherwise); `w = z_t`.
    have claim_a : ∀ j b, (E j).stalkIdeal (t.f y) = Ideal.span {b} → b ∈ C → b ≠ zt →
        (b ∈ B.stalkIdeal (t.f y) → φ zt * φ b = t.f.stalkMap y b) ∧
        ((φ b ∈ m' → (Subscheme.strictTransform t (E j)).stalkIdeal y = Ideal.span {φ b}) ∧
         (φ b ∉ m' → (Subscheme.strictTransform t (E j)).stalkIdeal y = ⊤)) := by
      intro j b hbj hbC hbzt
      have hbZ := hCZ hbC
      have h1 := hstP {b} (Finset.singleton_subset_iff.mpr hbZ) (E j)
        (by rw [hbj, Finset.prod_singleton])
      refine ⟨fun hbP => ?_, fun hm => ?_, fun hm => ?_⟩
      · have hbtP : b ∈ tP := by
          by_contra h
          exact rsop_notMem_span hZ htPZ hbZ h (hPt ▸ hbP)
        exact hrel b hbtP hbzt
      · have : (({b} : Finset _).erase zt).filter (fun z => φ z ∈ m') = {b} := by
          ext z
          simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_singleton]
          constructor
          · rintro ⟨⟨-, rfl⟩, -⟩; rfl
          · rintro rfl; exact ⟨⟨hbzt, rfl⟩, hm⟩
        rw [h1, this, Finset.prod_singleton]
      · have : (({b} : Finset _).erase zt).filter (fun z => φ z ∈ m') = ∅ := by
          refine Finset.filter_eq_empty_iff.mpr fun z hz => ?_
          have hzb : z = b := Finset.mem_singleton.mp (Finset.mem_erase.mp hz).2
          rw [hzb]; exact hm
        rw [h1, this, Finset.prod_empty, Ideal.span_singleton_one]
    -- Claim (b): `R'/Q'` is regular and `z_1', …, z_a'` extend to a minimal base of `Q'`
    -- (`Q' = (T)`, `T` part of a regular system of parameters of `R'`).
    have claim_b : ExtendsToRSOP _ T ∧
        (Subscheme.strictTransform t W).stalkIdeal y = Ideal.span (T : Set (t.X'.presheaf.stalk y)) ∧
        IsRegularLocalRing (t.X'.presheaf.stalk y ⧸ Ideal.span (T : Set (t.X'.presheaf.stalk y))) ∧
        ∀ b ∈ C, b ∈ W.stalkIdeal (t.f y) → φ b ∈ T := by
      have hTe : ExtendsToRSOP _ T := hext.mono hW''.2.1
      refine ⟨hTe, hW''.2.2, hTe.isRegularLocalRing_quotient, fun b hbC hbQ => ?_⟩
      have hbtQ : b ∈ tQ := by
        by_contra h
        exact rsop_notMem_span hZ (htQ.trans htPZ) (hCZ hbC) h (hQt ▸ hbQ)
      exact Finset.mem_image_of_mem φ hbtQ
    -- Claim (c): the residues of `z_j'` (`a < j ≤ b`), `z_j` (`b < j ≤ c`) and `w` extend to a
    -- regular system of parameters of `R'/Q'`.
    set S0 : Finset (t.X'.presheaf.stalk y) :=
      insert (φ zt) ((C.filter fun b => b ∉ W.stalkIdeal (t.f y) ∧ φ b ∈ m').image φ) with hS0
    have claim_c : ∃ _ : IsRegularLocalRing (t.X'.presheaf.stalk y ⧸
          Ideal.span (T : Set (t.X'.presheaf.stalk y))),
        ExtendsToRSOP (t.X'.presheaf.stalk y ⧸ Ideal.span (T : Set (t.X'.presheaf.stalk y)))
          (S0.image (Ideal.Quotient.mk (Ideal.span (T : Set (t.X'.presheaf.stalk y))))) ∧
        Set.InjOn (Ideal.Quotient.mk (Ideal.span (T : Set (t.X'.presheaf.stalk y)))) S0 := by
      obtain ⟨Z', hKZ', hZ'⟩ := hext
      obtain ⟨hreg, hRS, hcard⟩ := rsop_quotient hZ' (hW''.2.1.trans hKZ')
      have hinK : ∀ z ∈ Z, φ z ∈ m' → φ z ∈ Z' := fun z hz hm =>
        hKZ' (Finset.mem_image_of_mem φ (Finset.mem_filter.mpr ⟨hz, hm⟩))
      have hnotT : ∀ z ∈ Z, φ z ∈ m' → z ∉ tQ → φ z ∉ T := by
        intro z hz hm hzn hmem
        obtain ⟨w, hw, hwz⟩ := Finset.mem_image.mp hmem
        exact hzn (hinj ⟨htPZ (htQ hw), by rw [hwz]; exact hm⟩ ⟨hz, hm⟩ hwz ▸ hw)
      have hsub : S0 ⊆ Z' \ T := by
        intro k hk
        rcases Finset.mem_insert.mp hk with rfl | hk
        · exact Finset.mem_sdiff.mpr ⟨hinK zt (htPZ hzt) hztm, hnotT zt (htPZ hzt) hztm hW''.1⟩
        · obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hk
          obtain ⟨hbC, hbQ, hbm⟩ := Finset.mem_filter.mp hb
          have hbZ := hCZ hbC
          refine Finset.mem_sdiff.mpr ⟨hinK b hbZ hbm, hnotT b hbZ hbm fun h => hbQ ?_⟩
          rw [hQt]; exact Ideal.subset_span h
      exact ⟨hreg, ⟨_, Finset.image_subset_image hsub, hRS⟩,
        (Finset.card_image_iff.mp hcard).mono (by exact_mod_cast hsub)⟩
    -- "The conclusion follows immediately": (b) and (c) give a set `T ∪ S0` extending to a
    -- regular system of parameters of `R'`, of which every ideal in sight is generated by a part.
    obtain ⟨hTe, hTW, -, hTa⟩ := claim_b
    obtain ⟨hregQ, hS0e, hS0inj⟩ := claim_c
    have hKe : ExtendsToRSOP _ (T ∪ S0) := ExtendsToRSOP.union_of_quotient hTe hS0e hS0inj
    -- the exceptional divisor `E' = (w)`
    have hK0 : ∃ K₀ ⊆ T ∪ S0, K₀.card ≤ 1 ∧
        t.exceptional.stalkIdeal y = Ideal.span {∏ k ∈ K₀, k} :=
      ⟨{φ zt}, Finset.singleton_subset_iff.mpr
        (Finset.mem_union_right _ (Finset.mem_insert_self _ _)), by simp, by
        rw [hexc, Finset.prod_singleton]⟩
    -- the strict transforms of the `E_j`, by (a)
    have hEj : ∀ j, ∃ K₀ ⊆ T ∪ S0, K₀.card ≤ 1 ∧
        (Subscheme.strictTransform t (E j)).stalkIdeal y = Ideal.span {∏ k ∈ K₀, k} := by
      intro j
      have hbot : ∀ h : (Subscheme.strictTransform t (E j)).stalkIdeal y = ⊤,
          ∃ K₀ ⊆ T ∪ S0, K₀.card ≤ 1 ∧
            (Subscheme.strictTransform t (E j)).stalkIdeal y = Ideal.span {∏ k ∈ K₀, k} :=
        fun h => ⟨∅, Finset.empty_subset _, by simp, by rw [h]; simp⟩
      rcases hEB j with h | ⟨b, hb, hbj⟩
      · have h1 := hstP ∅ (Finset.empty_subset _) (E j)
          (by rw [h, Finset.prod_empty, Ideal.span_singleton_one])
        exact hbot (by rw [h1]; simp)
      · have hbC : b ∈ C := Finset.mem_filter.mpr ⟨hb, j, hbj⟩
        by_cases hbzt : b = zt
        · subst hbzt
          have h1 := hstP {b} (Finset.singleton_subset_iff.mpr (hCZ hbC)) (E j)
            (by rw [hbj, Finset.prod_singleton])
          exact hbot (by
            rw [h1, show (({b} : Finset _).erase b).filter (fun z => φ z ∈ m') = ∅ by simp]
            simp)
        · obtain ⟨-, ha1, ha2⟩ := claim_a j b hbj hbC hbzt
          by_cases hm : φ b ∈ m'
          · refine ⟨{φ b}, Finset.singleton_subset_iff.mpr ?_, by simp, by
              rw [ha1 hm, Finset.prod_singleton]⟩
            by_cases hbQ : b ∈ W.stalkIdeal (t.f y)
            · exact Finset.mem_union_left _ (hTa b hbC hbQ)
            · exact Finset.mem_union_right _ (Finset.mem_insert_of_mem
                (Finset.mem_image_of_mem φ (Finset.mem_filter.mpr ⟨hbC, hbQ, hm⟩)))
          · exact hbot (ha2 hm)
    -- `K₁` for the union `D'`
    have hD : ∃ K₁ ⊆ T ∪ S0, ((Subscheme.unionFam fun j => Subscheme.strictTransform t (E j)).union
        t.exceptional).stalkIdeal y = Ideal.span {∏ k ∈ K₁, k} := by
      obtain ⟨K₀, hK₀K, -, hK₀⟩ := hK0
      choose L hLK hLc hLe using hEj
      have hLU : Finset.univ.biUnion L ⊆ T ∪ S0 := Finset.biUnion_subset.mpr fun i _ => hLK i
      refine ⟨Finset.univ.biUnion L ∪ K₀, Finset.union_subset hLU hK₀K, ?_⟩
      show ((Subscheme.unionFam fun j => Subscheme.strictTransform t (E j)) ⊓
        t.exceptional).stalkIdeal y = _
      rw [Subscheme.stalkIdeal_inf_eq, Subscheme.unionFam, DatumTransform.stalkIdeal_iInf_fintype, hK₀,
        ← DatumTransform.span_prod_inf_of_subset hKe hLU hK₀K, ← DatumTransform.iInf_span_prod_of_subset hKe L hLK]
      exact congrArg (· ⊓ _) (iInf_congr hLe)
    exact ⟨T ∪ S0, hKe, hD, ⟨T, Finset.subset_union_left, hTW⟩, hK0⟩
  · ------------------------------------------------------------------ off the centre
    obtain ⟨e, hexc, hst⟩ := DatumTransform.exists_offCenter hXns t y hxB
    obtain ⟨ZW, hZW, ⟨tW, htWZ, hWt⟩, hEW⟩ :=
      DatumTransform.exists_rsop_of_hasOnlyNormalCrossingsWithAt E hE (fun i => iInf_le _ i) (hiiW _ hxW)
    have hKe : ExtendsToRSOP _ (ZW.image e) :=
      (ExtendsToRSOP.of_isRegularSystemOfParameters hZW).map_ringEquiv e
    refine ⟨ZW.image e, hKe, ?_, ⟨tW.image e, Finset.image_subset_image htWZ, ?_⟩,
      ⟨∅, Finset.empty_subset _, by simp, by rw [hexc]; simp⟩⟩
    · -- D'_y = ⨅_j (E_j,x).map e = span ∏ ..
      have hD : ∀ j, (Subscheme.strictTransform t (E j)).stalkIdeal y = ⊤ ∨
          ∃ k ∈ ZW.image e, (Subscheme.strictTransform t (E j)).stalkIdeal y = Ideal.span {k} := by
        intro j; rw [hst]
        rcases hEW j with h | ⟨a, ha, haj⟩
        · left; rw [h, Ideal.map_top]
        · right; refine ⟨e a, Finset.mem_image_of_mem _ ha, ?_⟩
          rw [haj, Ideal.map_span, Set.image_singleton]
      obtain ⟨K₁, hK₁, h⟩ := DatumTransform.iInf_eq_span_prod _ hKe hD
      refine ⟨K₁, hK₁, ?_⟩
      show ((Subscheme.unionFam fun j => Subscheme.strictTransform t (E j)) ⊓ t.exceptional).stalkIdeal y = _
      rw [Subscheme.stalkIdeal_inf_eq, Subscheme.unionFam, DatumTransform.stalkIdeal_iInf_fintype, hexc, inf_top_eq, h]
    · rw [hst, hWt, Ideal.map_span, Finset.coe_image]

end Prep4

/-! ### Lemma 4 (pp. 286–287) -/

/-- **Lemma 4** (pp. 286–287).  Normal crossings are preserved by a monoidal transformation
whose center is a non-singular irreducible subscheme `B` of `W` with which `⋃E_j` has only
normal crossings.

Formalization note (encoding): the paper arranges the indices of the `E_j` (`a ≤ b ≤ c`); Lean
does not reorder them but works with the set `C` of generators of the stalk ideals of the `E_j`
at `x` (elements of a regular system of parameters), and with the elements `z' = z / z_t` of the
chart, `z_t` playing the part of `w`.

Deviation from the paper (gap filled): the paper uses, without comment, *one* system
`(z_1, …, z_c, …)` that is simultaneously adapted to the components `E_j` through `x`, to
`Q = W_x` (generated by `z_1, …, z_a` and further members) and to `P = B_x` (generated by
`z_1, …, z_b` and further members).  Hypothesis (ii) provides only two different regular systems
of parameters (one adapted to `W`, one to `B`).  `exists_rsop_adapted_to_flag` constructs the
joint system by linear algebra in `m/m²`.

Deviation from the paper (gap filled): "If `x' ∈ W' − W'∩E'`, then `f` is locally at `x'` an
isomorphism" and "We may assume that `W ≠ B`" are asserted by the paper.  Lean proves the first
on stalks (`DatumTransform.exists_offCenter`, for `x = f(x') ∉ B`, which is equivalent to
`x' ∉ E'`), and the second is not a reduction but a vacuous case: for `W = B` the chart gives
`W'_{x'} = (1)`, i.e. `W' = ∅` (`MonoidalTransformation.exists_chart_strictTransform_stalkIdeal`).

Deviation from the paper (gap filled): the claims (a) `z_j/w` generate the primes of the `E_j'`,
(b) `R'/Q'` is regular and `z'_1, …, z'_a` extend to a minimal base of `Q'`, (c) the residues of
`z'_{a+1}, …, z'_b, z_{b+1}, …, z_c, w` extend to a regular system of parameters of `R'/Q'`, are
proved (`claim_a`, `claim_b`, `claim_c` in `exists_extendsToRSOP_of_mem_pts_strictTransform`) from
the chart `MonoidalTransformation.exists_chart_strictTransform_stalkIdeal` (with the saturation computation
`MonoidalTransform.saturation_span_eq_ite`), and "the conclusion follows immediately" is made
explicit: (b) and (c) give a set extending to a regular system of parameters of `R'`
(`ExtendsToRSOP.union_of_quotient`) of which the ideals of `E_1' ∪ ⋯ ∪ E_α' ∪ E'`, `W'` and
`W'∩E'` are generated by products, resp. subsets, so that normal crossings follow from the
stalkwise characterization (`Subscheme.hasOnlyNormalCrossingsWithAt_iff`).  `W'` is not identified with the
blow-up of `W` along `B`: its ideal is computed directly in the chart.

Deviation from the paper (statement modified): `W'∩E'` is `Subscheme.inter`, the sum of the
ideal sheaves; the `E_j` may be empty or repeated, per the agreement of pp. 274–275.
Hypotheses `hXalg`, `hXirr`, `hWirr`, `hBirr` are not used. -/
@[blueprint "lem:IV.2-4"
  (statement := /-- \textbf{Lemma 4.} Let $X$ be a non-singular irreducible algebraic scheme,
    $W$ a non-singular irreducible subscheme of $X$, and $B$ a non-singular irreducible
    subscheme of $W$. Let $E_1,\dots,E_\alpha$ be non-singular irreducible subschemes of
    codimension $1$ of $X$ such that
    \begin{enumerate}
      \item[(i)] $E_1\cup\dots\cup E_\alpha$ has only normal crossings,
      \item[(ii)] $E_1\cup\dots\cup E_\alpha$ has only normal crossings with $W$ as well as
        with $B$.
    \end{enumerate}
    Let $f\colon X'\to X$ be the monoidal transformation of $X$ with center $B$. Let
    $E_j'\ (1\le j\le\alpha)$, $W'$ be the strict transforms of $E_j$, $W$ respectively, and
    $E'$ the total transform $f^{-1}(B)$ of $B$ on $X'$. Then
    $E_1'\cup\dots\cup E_\alpha'\cup E'$ has only normal crossings with $W'$ as well as with
    $W'\cap E'$. (pp.~286--287.) (Formalization note (encoding): as in \cref{lem:IV.2-3},
    $\bigcup_jE_j$ is the meet of the ideal sheaves of the family $E\colon\mathrm{Fin}\,\alpha\to
    \mathrm{Subscheme}\,X$, and $E'$ is the exceptional subscheme $f^{-1}(B)$ of $f$.) -/)
  (proof := /-- We may assume that $W\ne B$. (See Remark 1, \S1, Ch.~I.) If
    $x'\in W'-W'\cap E'$, then the morphism $f$ is locally at $x'$ an isomorphism. Therefore
    we have only to consider the case in which $x'\in W'\cap E'$ to prove that
    $E_1'\cup\dots\cup E_\alpha'\cup E'$ has only normal crossings with $W'$ as well as with
    $W'\cap E'$ at $x'$. Now let $x=f(x')$. Let $R$ (resp.\ $R'$) be the local ring of $X$ at
    $x$ (resp.\ of $X'$ at $x'$). To prove the assertion at $x'$ we may assume that
    $x\in E_j$ for all $j$ $(1\le j\le\alpha)$. Let $P$ (resp.\ $Q$) be the prime ideal of
    $B$ (resp.\ $W$) in $R$. By arranging the indices of the $E_j$, if necessary, we may
    assume that $x'\in E_j'$ for $1\le j\le c$ and $x'\notin E_j'$ for $j>c$, that
    $E_j\supseteq W$ for $1\le j\le a$ but $E_j\not\supseteq W$ for $a<j\le c$, and that
    $E_j\supseteq B$ for $1\le j\le b$ but $E_j\not\supseteq B$ for $b<j\le c$, where
    $1\le a\le b\le c\le\alpha$. Let $z_j\ (1\le j\le c)$ be an element of $R$ which generates
    the prime ideal of $E_j$ in $R$. Let us take an element $w\in P$ such that $(w)R'=PR'$.
    Then $z_j'=z_j/w\ (1\le j\le b)$ are non-units in $R'$ and generate the prime ideal of
    $E_j'\ (1\le j\le b)$ in $R'$. If $Q'$ is the prime ideal of $W'$ in $R'$, then $R'/Q'$ is
    regular, and $(z_1',\dots,z_a')$ can be extended to a minimal base of $Q'$. Moreover, if
    $\bar z_j\ (a+1\le j\le b)$, $\bar z_j\ (b+1\le j\le c)$ and $\bar w$ denote the residue
    classes of $z_j'\ (a+1\le j\le b)$, $z_j\ (b+1\le j\le c)$ and $w$ in $R'/Q'$
    respectively, then $(\bar z_{a+1},\dots,\bar z_b,\bar z_{b+1},\dots,\bar z_c,\bar w)$ can
    be extended to a regular system of parameters of $R'/Q'$. The conclusion of Lemma 4
    follows immediately. \textsc{q.e.d.}

    \textbf{Formalization note (encoding).} Lean does not reorder the $E_j$ ($a\le b\le c$);
    it works with the set of generators of the stalk ideals of the $E_j$ at $x$ and with the chart
    elements $z'=z/z_t$, $z_t$ playing the part of $w$.

    \textbf{Deviation from the paper (gap filled).} The paper uses tacitly a single system
    $(z_1,\dots,z_c,\dots)$ adapted at once to the components $E_j$, to $Q$ and to $P$;
    hypothesis (ii) gives two different regular systems of parameters. Lean builds the joint one
    (\texttt{exists\_rsop\_adapted\_to\_flag}) by linear algebra in $M/M^2$.

    \textbf{Deviation from the paper (gap filled).} The paper asserts that $f$ is locally an
    isomorphism at $x'\in W'-W'\cap E'$ and that one may assume $W\ne B$. Lean proves the first
    on stalks (for $f(x')\notin B$, equivalent to $x'\notin E'$); for $W=B$ the chart gives
    $W'_{x'}=(1)$, so $W'=\emptyset$ and the statement is vacuous.

    \textbf{Deviation from the paper (gap filled).} The claims (a), (b), (c) are proved from the
    chart $R'=R[P/z_t]$ (the saturation of $(S)R'$ by $z_t$ is computed in
    \texttt{MonoidalTransform.saturation\_span\_sub}), and ``the conclusion follows immediately''
    is made explicit: (b) and (c) give a set extending to a regular system of parameters of $R'$
    (\texttt{ExtendsToRSOP.union\_of\_quotient}, generalizing the one-element criterion), of
    which the ideals of $E_1'\cup\dots\cup E_\alpha'\cup E'$, $W'$ and $W'\cap E'$ are generated
    by products, resp.\ subsets; normal crossings follow from the stalkwise characterization. $W'$
    is not identified with the blow-up of $W$ along $B$; its ideal is computed in the chart.

    \textbf{Deviation from the paper (statement modified).} $W'\cap E'$ is the subscheme with the
    sum of the ideal sheaves; the hypotheses of irreducibility of $X$, $W$, $B$ and that $X$ is
    algebraic are not used. -/)
  (latexEnv := "lemma")]
theorem MonoidalTransformation.hasOnlyNormalCrossingsWith_strictTransform_and_inter_exceptional {X : Scheme.{u}} (_hXalg : IsAlgebraicScheme X) (hXns : X.IsNonsingular)
    (_hXirr : IrreducibleSpace X) (W : Subscheme X)
    (hWns : W.IsNonsingular) (_hWirr : W.IsIrreducible) (B : Subscheme X)
    (hBns : B.IsNonsingular) (_hBirr : B.IsIrreducible) (hBW : B.IsContainedIn W)
    (α : ℕ) (E : Fin α → Subscheme X)
    (hE : ∀ j, (E j).IsNonsingularIrreducibleCodimOne)
    (hi : (Subscheme.unionFam E).HasOnlyNormalCrossings)
    (hiiW : (Subscheme.unionFam E).HasOnlyNormalCrossingsWith W)
    (hiiB : (Subscheme.unionFam E).HasOnlyNormalCrossingsWith B)
    (t : MonoidalTransformation X B) :
    ((Subscheme.unionFam fun j => Subscheme.strictTransform t (E j)).union
        t.exceptional).HasOnlyNormalCrossingsWith (Subscheme.strictTransform t W) ∧
    ((Subscheme.unionFam fun j => Subscheme.strictTransform t (E j)).union
        t.exceptional).HasOnlyNormalCrossingsWith
      ((Subscheme.strictTransform t W).inter t.exceptional) := by
  classical
  have hX' := (t.isNonsingular_and_isNonsingular_exceptional hXns hBns).1
  have hDred := DatumTransform.isReduced_of_forall_stalk hX'
    (exists_extendsToRSOP_stalkIdeal_union_exceptional hXns hBns t E hE hi hiiB)
  refine ⟨fun y hy => ?_, fun y hy => ?_⟩
  · obtain ⟨K, ⟨Z', hKZ', hZ'⟩, ⟨K₁, hK₁, hD⟩, ⟨T, hT, hW⟩, -⟩ :=
      exists_extendsToRSOP_of_mem_pts_strictTransform hXns W hWns hBns hBW t E hE hiiW hiiB y hy
    exact (Subscheme.hasOnlyNormalCrossingsWithAt_iff hDred (hX' y)).mpr
      ⟨Z', hZ', ⟨K₁, hK₁.trans hKZ', hD⟩, ⟨T, hT.trans hKZ', hW⟩⟩
  · -- y ∈ W' ∩ E': stalk is W'_y ⊔ exc_y ≠ ⊤, so y ∈ W'
    have hne := Subscheme.mem_pts_iff_stalkIdeal_ne_top.mp hy
    have hyW : y ∈ (Subscheme.strictTransform t W).pts := by
      rw [Subscheme.mem_pts_iff_stalkIdeal_ne_top]
      intro h
      apply hne
      show ((Subscheme.strictTransform t W) ⊔ t.exceptional).stalkIdeal y = ⊤
      rw [Subscheme.stalkIdeal_sup_eq, h, top_sup_eq]
    obtain ⟨K, ⟨Z', hKZ', hZ'⟩, ⟨K₁, hK₁, hD⟩, ⟨T, hT, hW⟩, ⟨K₀, hK₀, hc, hexc⟩⟩ :=
      exists_extendsToRSOP_of_mem_pts_strictTransform hXns W hWns hBns hBW t E hE hiiW hiiB y hyW
    rcases DatumTransform.card_le_one_cases hc with rfl | ⟨k, rfl⟩
    · exfalso; apply hne
      show ((Subscheme.strictTransform t W) ⊔ t.exceptional).stalkIdeal y = ⊤
      rw [Subscheme.stalkIdeal_sup_eq, hexc]; simp
    · refine (Subscheme.hasOnlyNormalCrossingsWithAt_iff hDred (hX' y)).mpr
        ⟨Z', hZ', ⟨K₁, hK₁.trans hKZ', hD⟩, ⟨insert k T, ?_, ?_⟩⟩
      · exact Finset.insert_subset (hKZ' (hK₀ (Finset.mem_singleton_self k))) (hT.trans hKZ')
      · show ((Subscheme.strictTransform t W) ⊔ t.exceptional).stalkIdeal y = _
        rw [Subscheme.stalkIdeal_sup_eq, hW, hexc, Finset.prod_singleton, Finset.coe_insert,
          Ideal.span_insert, sup_comm]

/-- A monoidal transformation whose center has an invertible sheaf of ideals is an isomorphism
(the identity morphism already makes the pull-back of the ideal invertible; cf.
`MonoidalTransformation.isIso_of_empty`). -/
theorem MonoidalTransformation.isIso_of_isInvertibleIdeal {X : Scheme.{u}} {B : Subscheme X}
    (t : MonoidalTransformation X B) (hB : B.IsInvertibleIdeal) : IsIso t.f := by
  obtain ⟨h, hh, -⟩ := t.universal X (𝟙 X) (by rw [Subscheme.totalTransform_id]; exact hB)
  have h2 : t.f ≫ h = 𝟙 _ :=
    (t.universal t.X' t.f t.invertible).unique
      (by rw [Category.assoc, hh, Category.comp_id]) (Category.id_comp _)
  exact ⟨⟨h, h2, hh⟩⟩

/-- If the ideal of `F ∩ W` in `W` is invertible, the strict transform of `W` under the
monoidal transformation with center `F` is isomorphic to `W`, compatibly with the immersions
into `X'` and `X` (the first assertion of Lemma 5). -/
theorem Subscheme.exists_iso_strictTransform_of_isInvertibleIdeal [Hironaka.Cited.MonoidalTransformationExistsIsProper.{u}] {X : Scheme.{u}}
    {F : Subscheme X} (t : MonoidalTransformation X F) (W : Subscheme X)
    (hF : (Subscheme.totalTransform W.ι F).IsInvertibleIdeal) :
    ∃ e : (Subscheme.strictTransform t W).toScheme ≅ W.toScheme,
      e.hom ≫ W.ι = (Subscheme.strictTransform t W).ι ≫ t.f := by
  obtain ⟨⟨s⟩, hs⟩ := Subscheme.nonempty_monoidalTransformation_strictTransform t W
  obtain ⟨e, he⟩ := hs s
  have := s.isIso_of_isInvertibleIdeal hF
  refine ⟨e.symm ≪≫ asIso s.f, ?_⟩
  simp only [Iso.trans_hom, Iso.symm_hom, asIso_hom, Category.assoc]
  rw [← he]
  simp

open Classical in
/-- Local principality at a prime spreads to a basic open neighbourhood. -/
theorem exists_away_span_singleton_of_isLocalization_atPrime {A : Type u} [CommRing A]
    [IsNoetherianRing A] (p : Ideal A) [p.IsPrime] (Ap : Type u) [CommRing Ap] [Algebra A Ap]
    [IsLocalization.AtPrime Ap p] (I : Ideal A) {g : Ap}
    (hI : I.map (algebraMap A Ap) = Ideal.span {g}) (hg : g ∈ nonZeroDivisors Ap) :
    ∃ h ∉ p, ∃ i ∈ I, ∀ (B : Type u) [CommRing B] [Algebra A B] [IsLocalization.Away h B],
      I.map (algebraMap A B) = Ideal.span {algebraMap A B i} ∧
        algebraMap A B i ∈ nonZeroDivisors B := by
  -- a generator coming from `I`
  have hgI : g ∈ I.map (algebraMap A Ap) := hI ▸ Ideal.mem_span_singleton_self g
  obtain ⟨⟨⟨i, hiI⟩, s⟩, hgs⟩ := (IsLocalization.mem_map_algebraMap_iff p.primeCompl Ap).mp hgI
  have hsu : IsUnit (algebraMap A Ap (s : A)) := IsLocalization.map_units Ap s
  set G := algebraMap A Ap i with hG
  have hGg : G = g * algebraMap A Ap (s : A) := by rw [hG]; exact hgs.symm
  have hspan : Ideal.span {G} = Ideal.span {g} := by
    rw [hGg]; exact (Ideal.span_singleton_mul_right_unit hsu g)
  have hGnzd : G ∈ nonZeroDivisors Ap := by
    rw [hGg]; exact mul_mem hg (hsu.mem_nonZeroDivisors)
  -- finitely many generators of `I`
  obtain ⟨cs, hcs⟩ := (IsNoetherian.noetherian I : I.FG)
  -- for each element of `I`, a common denominator
  have hden : ∀ c ∈ I, ∃ v ∈ p.primeCompl, ∃ b : A, v * c = b * i := by
    intro c hc
    have hc' : algebraMap A Ap c ∈ Ideal.span {G} := by
      rw [hspan, ← hI]; exact Ideal.mem_map_of_mem _ hc
    obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.mp hc'
    obtain ⟨⟨a, u⟩, hau⟩ := IsLocalization.surj p.primeCompl r
    have h1 : algebraMap A Ap ((u : A) * c) = algebraMap A Ap (a * i) := by
      rw [map_mul, map_mul, ← hau, ← hG, ← hr]; ring
    obtain ⟨w, hw⟩ := (IsLocalization.eq_iff_exists p.primeCompl Ap).mp h1
    exact ⟨w * u, mul_mem w.2 u.2, w * a, by
      have : (w : A) * ((u : A) * c) = (w : A) * (a * i) := hw
      calc (↑w * ↑u) * c = ↑w * (↑u * c) := by ring
        _ = ↑w * (a * i) := this
        _ = (↑w * a) * i := by ring⟩
  choose! v hvS b hvb using hden
  -- the annihilator of `i`
  let ann : Ideal A := LinearMap.ker (LinearMap.toSpanSingleton A A i)
  have hmemann : ∀ z, z ∈ ann ↔ z * i = 0 := fun z => by
    simp [ann, LinearMap.mem_ker, LinearMap.toSpanSingleton_apply]
  obtain ⟨as, has⟩ := (IsNoetherian.noetherian ann : ann.FG)
  have hkill : ∀ a ∈ ann, ∃ w ∈ p.primeCompl, w * a = 0 := by
    intro a ha
    have h0 : algebraMap A Ap a * G = 0 := by
      rw [hG, ← map_mul, (hmemann a).mp ha, map_zero]
    have h1 := (mem_nonZeroDivisors_iff_right.mp hGnzd) _ h0
    obtain ⟨w, hw⟩ := (IsLocalization.map_eq_zero_iff p.primeCompl Ap a).mp h1
    exact ⟨w, w.2, hw⟩
  have hkill' : ∀ a : A, ∃ w ∈ p.primeCompl, a ∈ ann → w * a = 0 := by
    intro a
    by_cases ha : a ∈ ann
    · obtain ⟨w, hw, h⟩ := hkill a ha; exact ⟨w, hw, fun _ => h⟩
    · exact ⟨1, one_mem _, fun h => absurd h ha⟩
  choose! w hwS hwa using hkill'
  set h₁ : A := ∏ c ∈ cs, v c with hh₁
  set h₂ : A := ∏ a ∈ as, w a with hh₂
  have hh₁S : h₁ ∈ p.primeCompl := Submonoid.prod_mem _ fun c hc => hvS c (by
    rw [← hcs]; exact Ideal.subset_span hc)
  have hh₂S : h₂ ∈ p.primeCompl := Submonoid.prod_mem _ fun a _ => hwS a
  refine ⟨h₁ * h₂, mul_mem hh₁S hh₂S, i, hiI, fun B _ _ _ => ?_⟩
  have hunit : IsUnit (algebraMap A B (h₁ * h₂)) := IsLocalization.Away.algebraMap_isUnit _
  have hu1 : IsUnit (algebraMap A B h₁) := by
    rw [map_mul] at hunit; exact isUnit_of_mul_isUnit_left hunit
  have hdvd1 : ∀ c ∈ cs, IsUnit (algebraMap A B (v c)) := fun c hc => by
    have : v c ∣ h₁ := Finset.dvd_prod_of_mem _ hc
    obtain ⟨k, hk⟩ := this
    rw [hk, map_mul] at hu1; exact isUnit_of_mul_isUnit_left hu1
  have hu2 : IsUnit (algebraMap A B h₂) := by
    rw [map_mul] at hunit; exact isUnit_of_mul_isUnit_right hunit
  refine ⟨le_antisymm ?_ ?_, ?_⟩
  · rw [← hcs, Ideal.map_span, Ideal.span_le]
    rintro _ ⟨c, hc, rfl⟩
    have hcI : c ∈ I := by rw [← hcs]; exact Ideal.subset_span hc
    have := congrArg (algebraMap A B) (hvb c hcI)
    rw [map_mul, map_mul] at this
    obtain ⟨u, hu⟩ := hdvd1 c hc
    rw [SetLike.mem_coe, Ideal.mem_span_singleton']
    refine ⟨algebraMap A B (b c) * ↑u⁻¹, ?_⟩
    calc algebraMap A B (b c) * ↑u⁻¹ * algebraMap A B i
        = ↑u⁻¹ * (algebraMap A B (b c) * algebraMap A B i) := by ring
      _ = ↑u⁻¹ * (algebraMap A B (v c) * algebraMap A B c) := by rw [this]
      _ = algebraMap A B c := by rw [← hu, ← mul_assoc, Units.inv_mul, one_mul]
  · rw [Ideal.span_le, Set.singleton_subset_iff]
    exact Ideal.mem_map_of_mem _ hiI
  · rw [mem_nonZeroDivisors_iff_right]
    intro z hz
    obtain ⟨⟨x, n⟩, hxn⟩ := IsLocalization.surj (Submonoid.powers (h₁ * h₂)) z
    obtain ⟨n, hn⟩ := n
    obtain ⟨m, rfl⟩ := hn
    have hzx : algebraMap A B (x * i) = 0 := by
      rw [map_mul, ← hxn, mul_assoc, mul_comm _ (algebraMap A B i), ← mul_assoc, hz, zero_mul]
    obtain ⟨⟨_, k, rfl⟩, hk⟩ := (IsLocalization.map_eq_zero_iff (Submonoid.powers (h₁ * h₂)) B _).mp hzx
    -- `(h₁h₂)^k x ∈ ann`, killed by `h₂`
    have hmem : (h₁ * h₂) ^ k * x ∈ ann := by
      rw [hmemann]; simpa [mul_assoc] using hk
    have hsum : (∏ a ∈ as, w a) * ((h₁ * h₂) ^ k * x) = 0 := by
      have : (h₁ * h₂) ^ k * x ∈ Submodule.span A (as : Set A) := by rw [has]; exact hmem
      obtain ⟨f, -, hf⟩ := Submodule.mem_span_finset.mp this
      rw [← hf, Finset.mul_sum]
      refine Finset.sum_eq_zero fun a ha => ?_
      have haann : a ∈ ann := by rw [← has]; exact Ideal.subset_span ha
      have hdv : w a ∣ ∏ a ∈ as, w a := Finset.dvd_prod_of_mem _ ha
      obtain ⟨q, hq⟩ := hdv
      rw [smul_eq_mul, hq, show w a * q * (f a * a) = q * f a * (w a * a) by ring, hwa a haann,
        mul_zero]
    have hx0 : algebraMap A B x = 0 := by
      have := congrArg (algebraMap A B) hsum
      rw [map_mul, map_mul, map_zero] at this
      have hU1 : IsUnit (algebraMap A B (∏ a ∈ as, w a)) := hu2
      have hU2 : IsUnit (algebraMap A B ((h₁ * h₂) ^ k)) := by
        rw [map_pow]; exact hunit.pow k
      exact hU2.mul_right_eq_zero.mp (hU1.mul_right_eq_zero.mp this)
    have : z * algebraMap A B ((h₁ * h₂) ^ m) = 0 := by rw [hxn, hx0]
    have hU3 : IsUnit (algebraMap A B ((h₁ * h₂) ^ m)) := by rw [map_pow]; exact hunit.pow m
    exact hU3.mul_left_eq_zero.mp this

/-- A sheaf of ideals on a locally noetherian scheme whose stalks are all generated by a
non-zero-divisor is invertible: a local generator at a point generates the ideal on a
basic open neighborhood (finite generation of the ideal and of the annihilator of the
generator). -/
theorem Subscheme.isInvertibleIdeal_of_forall_stalkIdeal_eq_span {Y : Scheme.{u}}
    [IsLocallyNoetherian Y] (D : Subscheme Y)
    (h : ∀ y, ∃ g, D.stalkIdeal y = Ideal.span {g} ∧ g ∈ nonZeroDivisors (Y.presheaf.stalk y)) :
    D.IsInvertibleIdeal := by
  intro y
  obtain ⟨g, hg1, hg2⟩ := h y
  obtain ⟨U, hyU⟩ := Subscheme.exists_affineOpen_mem y
  have : IsNoetherianRing Γ(Y, U) := IsLocallyNoetherian.component_noetherian U
  let := TopCat.Presheaf.algebra_section_stalk Y.presheaf (⟨y, hyU⟩ : (U : Y.Opens))
  have hloc := U.2.isLocalization_stalk ⟨y, hyU⟩
  have hI : (D.ideal U).map (algebraMap Γ(Y, U) (Y.presheaf.stalk y)) = Ideal.span {g} := by
    rw [← hg1, Subscheme.stalkIdeal_eq_map_germ_affine D U hyU]
    rfl
  obtain ⟨h₀, hh₀, i, hiI, hB⟩ :=
    exists_away_span_singleton_of_isLocalization_atPrime
      (U.2.primeIdealOf ⟨y, hyU⟩).asIdeal (Y.presheaf.stalk y) (D.ideal U) hI hg2
  have hyV : y ∈ (Y.basicOpen h₀ : Y.Opens) := by
    by_contra hn
    exact hh₀ ((Subscheme.mem_primeIdealOf_iff U.2 hyU h₀).mpr hn)
  have hVU : Y.affineBasicOpen h₀ ≤ U := Y.basicOpen_le h₀
  have := U.2.isLocalization_basicOpen h₀
  obtain ⟨hB1, hB2⟩ := hB Γ(Y, Y.basicOpen h₀)
  refine ⟨Y.affineBasicOpen h₀, hyV, algebraMap Γ(Y, U) Γ(Y, Y.basicOpen h₀) i, ?_, hB2⟩
  exact (D.map_ideal hVU).symm.trans hB1

section PrepCodimOne

open IsLocalRing

/-- A nonzero prime `P` of height at most one in a regular local ring, with regular quotient, is
principal and generated by a non-zero element: `P = (T)` with `T` part of a regular system of
parameters, and two distinct members of `T` would give a chain `0 < (t) < P` of primes. -/
theorem exists_span_singleton_of_height_le_one {R : Type u} [CommRing R] [IsRegularLocalRing R]
    (P : Ideal R) [P.IsPrime] (hreg : IsRegularLocalRing (R ⧸ P)) (hP0 : P ≠ ⊥)
    (hh : P.height ≤ 1) : ∃ a : R, P = Ideal.span {a} ∧ a ≠ 0 := by
  classical
  have := isDomain_of_isRegularLocalRing R
  obtain ⟨S, T, hS, hScard, hTS, hT⟩ := exists_finset_span_eq_prime R P hreg
  have hSr : IsRegularSystemOfParameters R S :=
    ⟨hS, by rw [hScard]; exact IsRegularLocalRing.spanFinrank_maximalIdeal⟩
  have hTe : ExtendsToRSOP R T := ⟨S, hTS, hSr⟩
  have hTne : T.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    rintro rfl
    apply hP0
    rw [← hT]; simp
  by_cases hcard : T.card ≤ 1
  · obtain ⟨a, rfl⟩ := Finset.card_eq_one.mp (le_antisymm hcard (Finset.card_pos.mpr hTne))
    exact ⟨a, by rw [← hT]; simp, hTe.ne_zero (Finset.mem_singleton_self a)⟩
  · exfalso
    obtain ⟨t₁, ht₁, t₂, ht₂, hne⟩ := Finset.one_lt_card.mp (not_le.mp hcard)
    have hp1 := hTe.isPrime_span_singleton ht₁
    have hlt : Ideal.span {t₁} < P := by
      refine lt_of_le_of_ne ?_ ?_
      · rw [← hT, Ideal.span_singleton_le_iff_mem]; exact Ideal.subset_span ht₁
      · intro h
        have : t₂ ∈ Ideal.span {t₁} := by
          rw [h, ← hT]; exact Ideal.subset_span ht₂
        exact hTe.notMem_span_singleton ht₁ ht₂ hne this
    have hfin : P.FiniteHeight := ⟨Or.inr (ne_top_of_le_ne_top ENat.one_ne_top hh)⟩
    have h1 := Ideal.height_strict_mono_of_isPrime hlt
    rw [DatumTransform.height_span_singleton_of_mem hTe ht₁] at h1
    exact absurd (lt_of_lt_of_le h1 hh) (lt_irrefl _)

end PrepCodimOne

section PrepIsoW

open IsLocalRing

variable {X : Scheme.{u}}

/-- If `W` is a non-singular irreducible subscheme not contained in `E`, then at no point `x` of
`W` does the stalk of `E` lie in the stalk of `W`: otherwise the generic point of `W` would lie
on `E`, hence `W ⊆ E` as `W` is reduced. -/
theorem not_stalkIdeal_le_of_not_isContainedIn (W E : Subscheme X) (hWns : W.IsNonsingular)
    (hWirr : W.IsIrreducible) (hEW : ¬ W.IsContainedIn E) {x : X} (hx : x ∈ W.pts) :
    ¬ E.stalkIdeal x ≤ W.stalkIdeal x := by
  intro hle
  have hWirr' := Subscheme.isIrreducible_pts W hWirr
  have hWcl : IsClosed W.pts := W.support.isClosed
  set η := hWirr'.genericPoint with hηdef
  have hηspec : closure {η} = W.pts := by
    rw [hWirr'.isGenericPoint_genericPoint_closure.def, hWcl.closure_eq]
  have hηW : η ∈ W.pts := by
    rw [← hηspec]; exact subset_closure rfl
  have hηx : η ⤳ x := specializes_iff_mem_closure.mpr (by rw [hηspec]; exact hx)
  have hηE : η ∈ E.pts := mem_pts_of_stalkIdeal_le_of_specializes hηx hηW hle
  have hWE : W.pts ⊆ E.pts := by
    rw [← hηspec]
    exact closure_minimal (Set.singleton_subset_iff.mpr hηE) E.support.isClosed
  exact hEW (isContainedIn_of_pts_subset_of_isReduced_toScheme (isReduced_toScheme_of_isNonsingular W hWns) hWE)

/-- Stalkwise version of "`F ∩ W` has codimension one in `W`" (first assertion of Lemma 5): the
ideal of `F` in `O_{W,y}` is generated by a non-zero-divisor. -/
theorem exists_stalkIdeal_totalTransform_eq_span_of_exists_stalkIdeal_eq_span
    (hXns : X.IsNonsingular) (W : Subscheme X) (hWns : W.IsNonsingular)
    (hWirr : W.IsIrreducible) (E : Subscheme X) (F : Subscheme X)
    (hEprin : ∀ x ∈ F.pts, ∃ e, E.stalkIdeal x = Ideal.span {e})
    (hEW : ¬ W.IsContainedIn E) (hF : F ∈ (W.inter E).irreducibleComponents)
    (hFns : F.IsNonsingular) (y : W.toScheme) :
    ∃ g, (Subscheme.totalTransform W.ι F).stalkIdeal y = Ideal.span {g} ∧
      g ∈ nonZeroDivisors (W.toScheme.presheaf.stalk y) := by
  classical
  rw [stalkIdeal_totalTransform]
  set x := W.ι y with hxdef
  by_cases hxF : x ∈ F.pts
  swap
  · exact ⟨1, by rw [Subscheme.stalkIdeal_eq_top_of_notMem_pts hxF, Ideal.map_top,
      Ideal.span_singleton_one], one_mem _⟩
  obtain ⟨Z, hZmax, hFZ⟩ := id hF
  have hFred := isReduced_toScheme_of_isNonsingular F hFns
  have hFinter : F.pts ⊆ (W.inter E).pts := by
    have : F.pts = Z := by
      rw [hFZ]; exact Scheme.IdealSheafData.coe_support_vanishingIdeal Z
    rw [this]; exact hZmax.1.2
  have hFWpts : F.pts ⊆ W.pts := fun z hz =>
    Scheme.IdealSheafData.support_antitone (le_sup_left : W ≤ W ⊔ E) (hFinter hz)
  have hFEpts : F.pts ⊆ E.pts := fun z hz =>
    Scheme.IdealSheafData.support_antitone (le_sup_right : E ≤ W ⊔ E) (hFinter hz)
  have hFWc := isContainedIn_of_pts_subset_of_isReduced_toScheme hFred hFWpts
  have hFEc := isContainedIn_of_pts_subset_of_isReduced_toScheme hFred hFEpts
  have hWF : W.stalkIdeal x ≤ F.stalkIdeal x := Subscheme.stalkIdeal_mono (fun U => hFWc U) x
  have hEF : E.stalkIdeal x ≤ F.stalkIdeal x := Subscheme.stalkIdeal_mono (fun U => hFEc U) x
  have hxW : x ∈ W.pts := hFWpts hxF
  have hxE : x ∈ E.pts := hFEpts hxF
  have : IsRegularLocalRing (X.presheaf.stalk x) := hXns x
  have := isDomain_of_isRegularLocalRing (X.presheaf.stalk x)
  have : IsRegularLocalRing (W.toScheme.presheaf.stalk y) := hWns y
  have := isDomain_of_isRegularLocalRing (W.toScheme.presheaf.stalk y)
  obtain ⟨hFp, hFreg⟩ := isPrime_and_isRegularLocalRing_quotient_of_isNonsingular F hFns hxF
  obtain ⟨e, hee⟩ := hEprin x hxF
  -- pass to `O_{W,y}`
  set φ := (W.ι.stalkMap y).hom with hφdef
  have hφ : Function.Surjective φ := W.ι.stalkMap_surjective y
  have hker : RingHom.ker φ = W.stalkIdeal x := (stalkIdeal_eq_ker_stalkMap W y).symm
  have hē : φ e ≠ 0 := by
    intro h
    refine not_stalkIdeal_le_of_not_isContainedIn W E hWns hWirr hEW hxW ?_
    rw [hee, Ideal.span_singleton_le_iff_mem, ← hker]
    exact h
  have heF : e ∈ F.stalkIdeal x := hEF (hee ▸ Ideal.mem_span_singleton_self e)
  set F' : Ideal (W.toScheme.presheaf.stalk y) := (F.stalkIdeal x).map φ with hF'
  have hF'p : F'.IsPrime := Ideal.map_isPrime_of_surjective hφ (by rw [hker]; exact hWF)
  have hmin : F' ∈ (Ideal.span {φ e}).minimalPrimes := by
    refine ⟨⟨hF'p, (Ideal.span_singleton_le_iff_mem _).mpr (Ideal.mem_map_of_mem _ heF)⟩, ?_⟩
    rintro q ⟨hq, hle⟩ hqF
    have hqe : φ e ∈ q := hle (Ideal.mem_span_singleton_self _)
    -- `F_x` is minimal over `W_x ⊔ E_x`
    have hFmin := Subscheme.stalkIdeal_mem_minimalPrimes hF hxF
    rw [show (W.inter E) = W ⊔ E from rfl, Subscheme.stalkIdeal_sup_eq] at hFmin
    have hcq : (W.stalkIdeal x ⊔ E.stalkIdeal x) ≤ q.comap φ := by
      refine sup_le ?_ ?_
      · rw [← hker]; intro z hz; rw [Ideal.mem_comap, RingHom.mem_ker.mp hz]; exact zero_mem _
      · rw [hee, Ideal.span_singleton_le_iff_mem, Ideal.mem_comap]; exact hqe
    have hcF : q.comap φ ≤ F.stalkIdeal x := by
      have : q.comap φ ≤ F'.comap φ := Ideal.comap_mono hqF
      refine this.trans ?_
      rw [hF', Ideal.comap_map_of_surjective φ hφ, ← RingHom.ker_eq_comap_bot, hker]
      exact sup_le le_rfl hWF
    have := hFmin.2 ⟨inferInstance, hcq⟩ hcF
    calc F' = (F.stalkIdeal x).map φ := rfl
      _ ≤ (q.comap φ).map φ := Ideal.map_mono (hFmin.2 ⟨Ideal.comap_isPrime φ q, hcq⟩ hcF)
      _ ≤ q := Ideal.map_comap_le
  have hh : F'.height ≤ 1 :=
    Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes (Ideal.span {φ e}) F' hmin
  have hF'0 : F' ≠ ⊥ := fun h => hē (by
    have : φ e ∈ F' := Ideal.mem_map_of_mem _ heF
    rwa [h, Ideal.mem_bot] at this)
  -- `O_{W,y}/F' ≅ O_{X,x}/F_x` is regular
  have hreg : IsRegularLocalRing (W.toScheme.presheaf.stalk y ⧸ F') := by
    let q : X.presheaf.stalk x →+* W.toScheme.presheaf.stalk y ⧸ F' :=
      (Ideal.Quotient.mk F').comp φ
    have hq : Function.Surjective q := Ideal.Quotient.mk_surjective.comp hφ
    have hkq : RingHom.ker q = F.stalkIdeal x := by
      rw [show RingHom.ker q = (F'.comap φ) from by
        ext z; simp [q, RingHom.mem_ker, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_comap]]
      rw [hF', Ideal.comap_map_of_surjective φ hφ, ← RingHom.ker_eq_comap_bot, hker]
      exact sup_eq_left.mpr hWF
    let eq := (Ideal.quotEquivOfEq hkq.symm).trans (RingHom.quotientKerEquivOfSurjective hq)
    exact IsRegularLocalRing.of_ringEquiv eq
  obtain ⟨a, ha, ha0⟩ := exists_span_singleton_of_height_le_one F' hreg hF'0 hh
  exact ⟨a, ha, mem_nonZeroDivisors_of_ne_zero ha0⟩

/-- First assertion of Lemma 5 (p. 287): "Then `f` induces an isomorphism `f̃` of `W'` to `W`."

Deviation from the paper (gap filled): the paper proves it in one line, "The monoidal
transformation `f : X' → X` induces in `W` the monoidal transformation of `W` with center `F`,
which is clearly an isomorphism because `W` is non-singular and `F` has codimension 1 in `W`."
Lean proves that the ideal of `F` in `W` is invertible: at `x ∈ F` the ideal of `F` in
`O_{W,x}` is a prime of height `≤ 1` (Krull's principal ideal theorem, since it is minimal over
the image of the generator of `E`, which is nonzero because `W ⊄ E`), nonzero, with regular
quotient, hence principal (`exists_span_singleton_of_height_le_one`), generated by a
non-zero-divisor; stalkwise principal ideals are invertible
(`Subscheme.isInvertibleIdeal_of_forall_stalkIdeal_eq_span`); and a monoidal transformation
with invertible center is an isomorphism (`MonoidalTransformation.isIso_of_isInvertibleIdeal`). -/
theorem Subscheme.exists_iso_strictTransform_of_exists_stalkIdeal_eq_span [Hironaka.Cited.MonoidalTransformationExistsIsProper.{u}]
    {X : Scheme.{u}} (hXalg : IsAlgebraicScheme X) (hXns : X.IsNonsingular)
    (W : Subscheme X) (hWns : W.IsNonsingular) (hWirr : W.IsIrreducible) (E : Subscheme X)
    (F : Subscheme X) (hEprin : ∀ x ∈ F.pts, ∃ e, E.stalkIdeal x = Ideal.span {e})
    (hEW : ¬ W.IsContainedIn E) (hF : F ∈ (W.inter E).irreducibleComponents) (hFns : F.IsNonsingular)
    (t : MonoidalTransformation X F) :
    ∃ e : (Subscheme.strictTransform t W).toScheme ≅ W.toScheme,
      e.hom ≫ W.ι = (Subscheme.strictTransform t W).ι ≫ t.f := by
  have := hXalg
  have := isAlgebraicScheme_toScheme W
  have := IsAlgebraicScheme.isNoetherian W.toScheme
  exact Subscheme.exists_iso_strictTransform_of_isInvertibleIdeal t W
    (Subscheme.isInvertibleIdeal_of_forall_stalkIdeal_eq_span _ fun y =>
      exists_stalkIdeal_totalTransform_eq_span_of_exists_stalkIdeal_eq_span hXns W hWns hWirr E F
        hEprin hEW hF hFns y)

end PrepIsoW

/-! ### Lemma 4 at a single point -/

section PrepLemmaFourPointwise

open IsLocalRing Classical

variable {X : Scheme.{u}}

/-- The stalk-level core of Lemma 4 at one point `y` of `W'` lying over a point `x` of the
center: with `E` reduced having only normal crossings with `W` and with `B` at `x`
and `B ⊆ W` non-singular, the stalk ideals of `E' ∪ E_exc` and of `W'` at `y` are generated by
a product, resp. a subset, of a set `K` extending to a regular system of parameters of
`O_{X',y}`.  Only `E` (not a presentation `E = ⋃ E_j`) enters. -/
theorem MonoidalTransformation.exists_extendsToRSOP_stalkIdeal_of_hasOnlyNormalCrossingsWithAt
    (hX : X.IsNonsingular) {B W E : Subscheme X} (hBns : B.IsNonsingular)
    (hBW : B.IsContainedIn W) (hEred : E.IsReduced) (t : MonoidalTransformation X B)
    {y : t.X'} (hEW : E.HasOnlyNormalCrossingsWithAt W (t.f y))
    (hEB : E.HasOnlyNormalCrossingsWithAt B (t.f y))
    (hy : y ∈ (Subscheme.strictTransform t W).pts) :
    ∃ K : Finset (t.X'.presheaf.stalk y), ExtendsToRSOP _ K ∧
      (∃ K₁ ⊆ K, ((Subscheme.strictTransform t E).union t.exceptional).stalkIdeal y =
        Ideal.span {∏ k ∈ K₁, k}) ∧
      (∃ T ⊆ K, (Subscheme.strictTransform t W).stalkIdeal y =
        Ideal.span (T : Set (t.X'.presheaf.stalk y))) := by
  have : IsRegularLocalRing (t.X'.presheaf.stalk y) := t.isRegularLocalRing_stalk hX hBns y
  have : IsRegularLocalRing (X.presheaf.stalk (t.f y)) := hX _
  obtain ⟨ZW, hZW, ⟨JW, hJWZ, hEJW⟩, ⟨tW, htWZ, hWt⟩⟩ :=
    (Subscheme.hasOnlyNormalCrossingsWithAt_iff hEred (hX _)).mp hEW
  obtain ⟨ZB, hZB, ⟨JB, hJBZ, hEJB⟩, ⟨tB, htBZ, hBt⟩⟩ :=
    (Subscheme.hasOnlyNormalCrossingsWithAt_iff hEred (hX _)).mp hEB
  have hQP : W.stalkIdeal (t.f y) ≤ B.stalkIdeal (t.f y) :=
    Subscheme.stalkIdeal_mono (fun U => hBW U) _
  have hassoc : ∀ c ∈ JB, ∃ a ∈ ZW, Ideal.span {c} = Ideal.span {a} := by
    intro c hc
    have hext := (ExtendsToRSOP.of_isRegularSystemOfParameters hZB).mono hJBZ
    have hp := hext.isPrime_span_singleton hc
    have hp1 := DatumTransform.height_span_singleton_of_mem hext hc
    have hle : Ideal.span {∏ z ∈ JW, z} ≤ Ideal.span {c} := by
      rw [← hEJW, hEJB, ← hext.iInf_span_singleton]; exact iInf₂_le c hc
    obtain ⟨a, haJ, hca⟩ := DatumTransform.eq_span_of_prod_le hZW hJWZ hp1 hle
    exact ⟨a, hJWZ haJ, hca⟩
  obtain ⟨Z, hZ, hCZ, tP, htPZ, hPt, tQ, htQ, hQt⟩ :=
    exists_rsop_adapted_to_flag (W.stalkIdeal (t.f y)) (B.stalkIdeal (t.f y)) hQP ZB tB ZW tW JB
      hZB htBZ hBt hZW htWZ hWt hJBZ (fun c hc _ => hassoc c hc)
  obtain ⟨zt, φ, hzt, hexc, hztm, -, hrel, hinj, hext, hstP, hstS⟩ :=
    t.exists_chart_strictTransform_stalkIdeal hX y hZ htPZ hPt
  -- the strict transform of `W`
  have h1 := hstS tQ htQ W hQt
  have hne : (Subscheme.strictTransform t W).stalkIdeal y ≠ ⊤ :=
    Subscheme.mem_pts_iff_stalkIdeal_ne_top.mp hy
  rw [h1] at hne
  have hztQ : zt ∉ tQ := fun h => hne (by simp [h])
  simp only [hztQ, ↓reduceIte] at h1 hne
  have hnu : ∀ q ∈ tQ, φ q ∈ maximalIdeal (t.X'.presheaf.stalk y) := by
    intro q hq; by_contra h
    exact hne (Ideal.eq_top_of_isUnit_mem _ (Ideal.subset_span ⟨q, hq, rfl⟩)
      ((IsLocalRing.mem_maximalIdeal _).not.mp h |> not_not.mp))
  -- the strict transform of `E`
  have hE' := hstP JB hCZ E hEJB
  have hsubK : ∀ z ∈ (JB.erase zt).filter (fun z => φ z ∈ maximalIdeal (t.X'.presheaf.stalk y)),
      z ∈ Z ∧ φ z ∈ maximalIdeal (t.X'.presheaf.stalk y) := fun z hz =>
    ⟨hCZ (Finset.mem_of_mem_erase (Finset.mem_filter.mp hz).1), (Finset.mem_filter.mp hz).2⟩
  set K₁' := ((JB.erase zt).filter
    (fun z => φ z ∈ maximalIdeal (t.X'.presheaf.stalk y))).image φ with hK₁'
  have hK₁'K : K₁' ⊆ (Z.filter fun z => φ z ∈ maximalIdeal (t.X'.presheaf.stalk y)).image φ := by
    intro a ha
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp ha
    exact Finset.mem_image_of_mem φ (Finset.mem_filter.mpr (hsubK z hz))
  have hztK : φ zt ∈ (Z.filter fun z => φ z ∈ maximalIdeal (t.X'.presheaf.stalk y)).image φ :=
    Finset.mem_image_of_mem φ (Finset.mem_filter.mpr ⟨htPZ hzt, hztm⟩)
  have hE'prod : (Subscheme.strictTransform t E).stalkIdeal y = Ideal.span {∏ k ∈ K₁', k} := by
    rw [hE', hK₁', ← DatumTransform.prod_image_eq φ hinj _ hsubK]
  refine ⟨_, hext, ⟨K₁' ∪ {φ zt}, Finset.union_subset hK₁'K (Finset.singleton_subset_iff.mpr hztK),
    ?_⟩, ⟨tQ.image φ, ?_, ?_⟩⟩
  · show ((Subscheme.strictTransform t E) ⊓ t.exceptional).stalkIdeal y = _
    have hexc' : t.exceptional.stalkIdeal y = Ideal.span {∏ k ∈ ({φ zt} : Finset _), k} := by
      rw [hexc, Finset.prod_singleton]
    rw [Subscheme.stalkIdeal_inf_eq, hE'prod, hexc',
      DatumTransform.span_prod_inf_of_subset hext hK₁'K (Finset.singleton_subset_iff.mpr hztK)]
  · intro a ha
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp ha
    exact Finset.mem_image_of_mem φ (Finset.mem_filter.mpr ⟨htPZ (htQ hq), hnu q hq⟩)
  · rw [h1, Finset.coe_image]

end PrepLemmaFourPointwise

/-! ### local computation for the blow-up at a bad component -/

section PrepPhase19

open IsLocalRing Classical

section PrepReplaceGenerator

variable {R : Type u} [CommRing R]

/-- Replacing a generator with a unit coefficient. -/
theorem span_insert_erase_eq_of_unit {s : Finset R} {w z : R} {h : R → R} (hw : w ∈ s)
    (hz : z = ∑ t ∈ s, h t * t) (hu : IsUnit (h w)) :
    Ideal.span ((insert z (s.erase w) : Finset R) : Set R) = Ideal.span (s : Set R) := by
  have hzs : z ∈ Ideal.span (s : Set R) :=
    hz ▸ Ideal.sum_mem _ fun t ht => Ideal.mul_mem_left _ _ (Ideal.subset_span ht)
  have hwz : w ∈ Ideal.span ((insert z (s.erase w) : Finset R) : Set R) := by
    obtain ⟨u, hu'⟩ := hu
    have h1 : z = h w * w + ∑ t ∈ s.erase w, h t * t := by
      rw [hz]; exact (Finset.add_sum_erase s (fun t => h t * t) hw).symm
    have h2 : w = ↑u⁻¹ * (z - ∑ t ∈ s.erase w, h t * t) := by
      rw [h1, add_sub_cancel_right, ← hu']
      simp [← mul_assoc]
    have key : (↑u⁻¹ : R) * (z - ∑ t ∈ s.erase w, h t * t) ∈
        Ideal.span ((insert z (s.erase w) : Finset R) : Set R) := by
      refine Ideal.mul_mem_left _ _ (sub_mem (Ideal.subset_span (by simp))
        (Ideal.sum_mem _ fun t ht => Ideal.mul_mem_left _ _ (Ideal.subset_span ?_)))
      exact Finset.mem_coe.mpr (Finset.mem_insert_of_mem ht)
    rwa [← h2] at key
  apply le_antisymm
  · refine Ideal.span_le.mpr fun t ht => ?_
    rcases Finset.mem_insert.mp (Finset.mem_coe.mp ht) with rfl | ht
    · exact hzs
    · exact Ideal.subset_span (Finset.mem_coe.mpr (Finset.mem_of_mem_erase ht))
  · refine Ideal.span_le.mpr fun t ht => ?_
    by_cases htw : t = w
    · exact htw ▸ hwz
    · exact Ideal.subset_span (by simp [htw, Finset.mem_coe.mp ht])

end PrepReplaceGenerator

section PrepReplaceRSOP

variable {R : Type u} [CommRing R] [IsRegularLocalRing R]

/-- The ring-theoretic core of the local computation for `(1)` after a blow-up at a bad component
(see the docstring of the file). -/
theorem exists_rsop_replace_of_mem {Z C tQ tP : Finset R} (hZ : IsRegularSystemOfParameters R Z)
    (hCZ : C ⊆ Z) (htQP : tQ ⊆ tP) (htPZ : tP ⊆ Z) {zj z1 : R} (hzjC : zj ∈ C)
    (hP : (Ideal.span (tP : Set R)).IsPrime) (hzj : zj ∉ Ideal.span (tP : Set R))
    (hz1P : z1 ∈ Ideal.span (tP : Set R))
    (hz1G : z1 ∈ Ideal.span ((insert zj tQ : Finset R) : Set R))
    (hind : z1 ∉ Ideal.span (C : Set R) ⊔ maximalIdeal R ^ 2) :
    ∃ w ∈ tQ, w ∉ C ∧ IsRegularSystemOfParameters R (insert z1 (Z.erase w)) ∧
      Ideal.span ((insert z1 (tP.erase w) : Finset R) : Set R) = Ideal.span (tP : Set R) ∧
      Ideal.span ((insert z1 ((insert zj tQ).erase w) : Finset R) : Set R) =
        Ideal.span ((insert zj tQ : Finset R) : Set R) := by
  have hZm : ∀ z ∈ Z, z ∈ maximalIdeal R := fun z hz => hZ.1 ▸ Ideal.subset_span hz
  have hzjQ : zj ∉ tQ := fun h => hzj (Ideal.subset_span (htQP h))
  obtain ⟨f, -, hf⟩ := Submodule.mem_span_finset.mp hz1G
  rw [Finset.sum_insert hzjQ] at hf
  simp only [smul_eq_mul] at hf
  have hfz : f zj * zj ∈ Ideal.span (tP : Set R) := by
    have : f zj * zj = z1 - ∑ i ∈ tQ, f i * i := by rw [← hf]; ring
    rw [this]
    exact sub_mem hz1P (Ideal.sum_mem _ fun i hi =>
      Ideal.mul_mem_left _ _ (Ideal.subset_span (htQP hi)))
  have hfzP : f zj ∈ Ideal.span (tP : Set R) := (hP.mem_or_mem hfz).resolve_right hzj
  obtain ⟨g, -, hg⟩ := Submodule.mem_span_finset.mp hfzP
  simp only [smul_eq_mul] at hg
  -- a coefficient that is a unit
  have hex : ∃ w ∈ tQ, w ∉ C ∧ IsUnit (f w) := by
    by_contra hcon
    push Not at hcon
    apply hind
    rw [← hf]
    refine add_mem (Ideal.mem_sup_left (Ideal.mul_mem_left _ _ (Ideal.subset_span hzjC)))
      (Ideal.sum_mem _ fun i hi => ?_)
    by_cases hiC : i ∈ C
    · exact Ideal.mem_sup_left (Ideal.mul_mem_left _ _ (Ideal.subset_span hiC))
    · refine Ideal.mem_sup_right ?_
      have hfi : f i ∈ maximalIdeal R := (IsLocalRing.mem_maximalIdeal _).mpr (hcon i hi hiC)
      rw [pow_two]
      exact Ideal.mul_mem_mul hfi (hZm i (htPZ (htQP hi)))
  obtain ⟨w, hwQ, hwC, hwu⟩ := hex
  have hwP : w ∈ tP := htQP hwQ
  -- the coefficients of `z1` in terms of `tP`
  set h : R → R := fun t => (if t ∈ tQ then f t else 0) + g t * zj with hh
  have hz1 : z1 = ∑ t ∈ tP, h t * t := by
    have e1 : ∑ t ∈ tP, (if t ∈ tQ then f t else 0) * t = ∑ i ∈ tQ, f i * i := by
      have : ∀ t ∈ tP, (if t ∈ tQ then f t else 0) * t = if t ∈ tQ then f t * t else 0 := by
        intro t _; split_ifs <;> simp
      rw [Finset.sum_congr rfl this, Finset.sum_ite_mem, Finset.inter_eq_right.mpr htQP]
    have e2 : ∑ t ∈ tP, g t * zj * t = f zj * zj := by
      rw [← hg, Finset.sum_mul]
      exact Finset.sum_congr rfl fun t _ => by ring
    simp only [hh, add_mul, Finset.sum_add_distrib, e1, e2]
    rw [← hf]; ring
  have hhw : IsUnit (h w) := by
    have : h w = f w + g w * zj := by simp [hh, hwQ]
    rw [this]
    by_contra hnu
    have hm : f w + g w * zj ∈ maximalIdeal R := (IsLocalRing.mem_maximalIdeal _).mpr hnu
    have hzm : g w * zj ∈ maximalIdeal R :=
      Ideal.mul_mem_left _ _ (hZm zj (hCZ hzjC))
    have : f w ∈ maximalIdeal R := by simpa using sub_mem hm hzm
    exact (IsLocalRing.mem_maximalIdeal _).mp this hwu
  have hspanP := span_insert_erase_eq_of_unit hwP hz1 hhw
  have hspanG := span_insert_erase_eq_of_unit (s := insert zj tQ) (h := f) (z := z1)
    (Finset.mem_insert_of_mem hwQ) (by rw [Finset.sum_insert hzjQ]; exact hf.symm) hwu
  refine ⟨w, hwQ, hwC, ?_, hspanP, hspanG⟩
  -- regular system of parameters
  have hwZ : w ∈ Z := htPZ hwP
  have hwspan : w ∈ Ideal.span ((insert z1 (Z.erase w) : Finset R) : Set R) := by
    have : w ∈ Ideal.span ((insert z1 (tP.erase w) : Finset R) : Set R) := by
      rw [hspanP]; exact Ideal.subset_span hwP
    refine Ideal.span_mono ?_ this
    intro t ht
    simp only [Finset.coe_insert, Set.mem_insert_iff, Finset.mem_coe] at ht ⊢
    rcases ht with rfl | ht
    · exact Or.inl rfl
    · exact Or.inr (Finset.erase_subset_erase w htPZ ht)
  apply rsop_of_span_of_card_le
  · apply le_antisymm
    · refine Ideal.span_le.mpr fun t ht => ?_
      rcases Finset.mem_insert.mp (Finset.mem_coe.mp ht) with rfl | ht
      · exact (Ideal.span_le.mpr fun x hx => hZm x (htPZ hx)) hz1P
      · exact hZm t (Finset.mem_of_mem_erase ht)
    · rw [← hZ.1]
      refine Ideal.span_le.mpr fun t ht => ?_
      by_cases htw : t = w
      · exact htw ▸ hwspan
      · exact Ideal.subset_span (by simp [htw, Finset.mem_coe.mp ht])
  · calc (insert z1 (Z.erase w)).card ≤ (Z.erase w).card + 1 := Finset.card_insert_le _ _
      _ = Z.card := Finset.card_erase_add_one hwZ
      _ = (maximalIdeal R).spanFinrank := rsop_card_eq_spanFinrank hZ

end PrepReplaceRSOP

section PrepChartAlgebra2
variable {R : Type u} [CommRing R] [IsRegularLocalRing R] [IsDomain R] {P : Ideal R}

open Classical in
/-- Saturation of `(S) R'` for `S ⊆ Z` not necessarily inside the center's generators `T`: `(1)` if
`z_t ∈ S`, else `(z'_s : s ∈ S)`. -/
theorem MonoidalTransform.saturation_span_eq_ite_of_subset (s : MonoidalTransform R P) {Z T S :
    Finset R}
    (hZ : IsRegularSystemOfParameters R Z) (hTZ : T ⊆ Z) (hT : Ideal.span (T : Set R) = P)
    (hSZ : S ⊆ Z) {zt : R} {φ : R → s.ring} (hzt : zt ∈ T)
    (hφ₁ : ∀ z ∈ Z, z ∉ T → φ z = s.toRing z)
    (hφ₂ : φ zt = s.toRing zt)
    (hφ₃ : ∀ z ∈ T, z ≠ zt → s.toRing zt * φ z = s.toRing z)
    (hinj : Set.InjOn φ {z | z ∈ Z ∧ φ z ∈ maximalIdeal s.ring})
    (hext : ExtendsToRSOP s.ring ((Z.filter fun z => φ z ∈ maximalIdeal s.ring).image φ)) :
    ⨆ n : ℕ, ((Ideal.span (S : Set R)).map s.toRing).colon
        ((Ideal.span {s.toRing zt} ^ n : Ideal s.ring) : Set s.ring) =
      if zt ∈ S then ⊤ else Ideal.span (φ '' (S : Set R)) := by
  classical
  have hZ' := ExtendsToRSOP.of_isRegularSystemOfParameters hZ
  have hTe : ExtendsToRSOP R T := hZ'.mono hTZ
  have hPp : P.IsPrime := hT ▸ hTe.isPrime_span
  have hS : IsRegularLocalRing (R ⧸ P) := hT ▸ hTe.isRegularLocalRing_quotient
  have hP0 : P ≠ ⊥ := fun h => s.x_ne_zero (by simpa [h] using s.x_mem)
  have : IsRegularLocalRing s.ring := (s.isRegularLocalRing_and_isLocalHom_and_span_xR_eq_map hPp hP0 hS).1
  have := isDomain_of_isRegularLocalRing s.ring
  set y := s.toRing zt with hy
  have hy0 : y ≠ 0 := fun h => hTe.ne_zero hzt (s.toRing_injective (h.trans (map_zero _).symm))
  have hZM : ∀ z ∈ Z, s.toRing z ∈ maximalIdeal s.ring := fun z hz =>
    map_nonunit s.toRing _ (hZ'.mem_maximalIdeal hz)
  by_cases hztS : zt ∈ S
  · simp only [hztS, ↓reduceIte]
    refine top_le_iff.mp (le_trans ?_ (le_iSup _ 1))
    intro a _
    refine Submodule.mem_colon.mpr fun p hp => ?_
    rw [pow_one, SetLike.mem_coe, Ideal.mem_span_singleton'] at hp
    obtain ⟨c, rfl⟩ := hp
    have : y ∈ (Ideal.span (S : Set R)).map s.toRing :=
      Ideal.mem_map_of_mem _ (Ideal.subset_span hztS)
    rw [smul_eq_mul, show a * (c * y) = (a * c) * y by ring]
    exact Ideal.mul_mem_left _ _ this
  · simp only [hztS, ↓reduceIte]
    set I0 : Ideal s.ring := Ideal.span (φ '' (S : Set R)) with hI0
    have hgen : ∀ z ∈ S, s.toRing z = y * φ z ∨ s.toRing z = φ z := by
      intro z hz
      by_cases hzT : z ∈ T
      · exact Or.inl (hφ₃ z hzT (fun h => hztS (h ▸ hz))).symm
      · exact Or.inr (hφ₁ z (hSZ hz) hzT).symm
    have hmapI0 : ∀ a ∈ (Ideal.span (S : Set R)).map s.toRing, a ∈ I0 := by
      intro a ha
      rw [Ideal.map_span] at ha
      refine (Ideal.span_le.mpr ?_ : Ideal.span (s.toRing '' (S : Set R)) ≤ I0) ha
      rintro _ ⟨z, hz, rfl⟩
      rcases hgen z hz with h | h
      · rw [h]; exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨z, hz, rfl⟩)
      · rw [h]; exact Ideal.subset_span ⟨z, hz, rfl⟩
    have hyI0 : ∀ a ∈ I0, y * a ∈ (Ideal.span (S : Set R)).map s.toRing := by
      intro a ha
      refine Submodule.span_induction (p := fun a _ => y * a ∈
        (Ideal.span (S : Set R)).map s.toRing) ?_ (by simp) ?_ ?_ ha
      · rintro _ ⟨z, hz, rfl⟩
        rcases hgen z hz with h | h
        · rw [← h]; exact Ideal.mem_map_of_mem _ (Ideal.subset_span hz)
        · rw [← h]; exact Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _ (Ideal.subset_span hz))
      · intro a b _ _ ha hb; rw [mul_add]; exact add_mem ha hb
      · intro c a _ ha; rw [smul_eq_mul, mul_left_comm]; exact Ideal.mul_mem_left _ _ ha
    have key : ∀ (a : s.ring) (n : ℕ), a * y ^ n ∈ I0 → a ∈ I0 := by
      intro a n ha
      by_cases hunit : ∃ z ∈ S, φ z ∉ maximalIdeal s.ring
      · obtain ⟨z, hz, hzu⟩ := hunit
        have : I0 = ⊤ := Ideal.eq_top_of_isUnit_mem _ (Ideal.subset_span ⟨z, hz, rfl⟩)
          ((IsLocalRing.mem_maximalIdeal _).not.mp hzu |> not_not.mp)
        rw [this]; exact trivial
      · push Not at hunit
        set L := S.image φ with hL
        have hLK : L ⊆ (Z.filter fun z => φ z ∈ maximalIdeal s.ring).image φ := by
          intro l hl
          obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hl
          exact Finset.mem_image_of_mem φ (Finset.mem_filter.mpr ⟨hSZ hz, hunit z hz⟩)
        have hytop : y ∈ (Z.filter fun z => φ z ∈ maximalIdeal s.ring).image φ :=
          Finset.mem_image.mpr ⟨zt, Finset.mem_filter.mpr
            ⟨hTZ hzt, by rw [hφ₂]; exact hZM _ (hTZ hzt)⟩, hφ₂⟩
        have hyL : y ∉ Ideal.span (L : Set s.ring) := by
          obtain ⟨Z0, hKZ0, hZ0⟩ := hext
          refine rsop_notMem_span hZ0 (hLK.trans hKZ0) (hKZ0 hytop) ?_
          intro hyl
          obtain ⟨z, hz, hzy⟩ := Finset.mem_image.mp hyl
          have := hinj ⟨hSZ hz, hunit z hz⟩
            ⟨hTZ hzt, by rw [hφ₂]; exact hZM _ (hTZ hzt)⟩ (hzy.trans hφ₂.symm)
          exact hztS (this ▸ hz)
        have hpr := (hext.mono hLK).isPrime_span
        have hI0L : I0 = Ideal.span (L : Set s.ring) := by
          rw [hI0, hL, Finset.coe_image]
        rw [hI0L] at ha ⊢
        exact (Ideal.IsPrime.mem_or_mem hpr ha).resolve_right fun h => hyL (hpr.mem_of_pow_mem n h)
    apply le_antisymm
    · refine iSup_le fun n a ha => ?_
      have h1 := Submodule.mem_colon.mp ha (y ^ n)
        (by rw [Ideal.span_singleton_pow]; exact Ideal.mem_span_singleton_self _)
      exact key a n (hmapI0 _ h1)
    · refine le_iSup_of_le 1 fun a ha => Submodule.mem_colon.mpr fun p hp => ?_
      rw [pow_one, SetLike.mem_coe, Ideal.mem_span_singleton'] at hp
      obtain ⟨c, rfl⟩ := hp
      rw [smul_eq_mul, show a * (c * y) = c * (y * a) by ring]
      exact Ideal.mul_mem_left _ _ (hyI0 a ha)

end PrepChartAlgebra2

section PrepChart2

variable {X : Scheme.{u}} {B : Subscheme X}

open Classical in
/-- The chart computation of `exists_chart_strictTransform_stalkIdeal` with the strict transform of
a
subscheme whose ideal at `f(y)` is generated by ANY subset `S ⊆ Z` (not only `S ⊆ T`): `(1)` if
`z_t ∈ S`, else `(z'_s : s ∈ S)`, where `z'_s = z_s` for `s ∉ T`. -/
theorem MonoidalTransformation.exists_chart_strictTransform_stalkIdeal_of_subset (hX :
    X.IsNonsingular)
    (t : MonoidalTransformation X B) (y : t.X')
    [IsRegularLocalRing (t.X'.presheaf.stalk y)]
    {Z T : Finset (X.presheaf.stalk (t.f y))}
    (hZ : IsRegularSystemOfParameters (X.presheaf.stalk (t.f y)) Z) (hTZ : T ⊆ Z)
    (hBT : B.stalkIdeal (t.f y) = Ideal.span (T : Set (X.presheaf.stalk (t.f y)))) :
    ∃ (zt : X.presheaf.stalk (t.f y)) (φ : X.presheaf.stalk (t.f y) → t.X'.presheaf.stalk y),
      zt ∈ T ∧ t.exceptional.stalkIdeal y = Ideal.span {φ zt} ∧
      φ zt ∈ maximalIdeal (t.X'.presheaf.stalk y) ∧ φ zt = t.f.stalkMap y zt ∧
      (∀ z ∈ T, z ≠ zt → φ zt * φ z = t.f.stalkMap y z) ∧
      Set.InjOn φ {z | z ∈ Z ∧ φ z ∈ maximalIdeal (t.X'.presheaf.stalk y)} ∧
      ExtendsToRSOP (t.X'.presheaf.stalk y)
        ((Z.filter fun z => φ z ∈ maximalIdeal (t.X'.presheaf.stalk y)).image φ) ∧
      (∀ J ⊆ Z, ∀ V : Subscheme X, V.stalkIdeal (t.f y) = Ideal.span {(∏ z ∈ J, z)} →
        (Subscheme.strictTransform t V).stalkIdeal y =
          Ideal.span {(∏ z ∈ (J.erase zt).filter
            (fun z => φ z ∈ maximalIdeal (t.X'.presheaf.stalk y)), φ z)}) ∧
      (∀ z ∈ Z, z ∉ T → φ z = t.f.stalkMap y z) ∧
      (∀ S ⊆ Z, ∀ V : Subscheme X, V.stalkIdeal (t.f y) = Ideal.span (S : Set _) →
        (Subscheme.strictTransform t V).stalkIdeal y =
          if zt ∈ S then ⊤ else Ideal.span (φ '' (S : Set _))) := by
  have : IsRegularLocalRing (X.presheaf.stalk (t.f y)) := hX _
  have := isDomain_of_isRegularLocalRing (X.presheaf.stalk (t.f y))
  obtain ⟨s, e, he⟩ := t.exists_monoidalTransform_stalk y
  have : IsRegularLocalRing s.ring := IsRegularLocalRing.of_ringEquiv e.symm
  obtain ⟨zt, φ, hzt, hspan, hφ₁, hφ₂, hφ₃, hinj, hext⟩ :=
    MonoidalTransform.exists_rsop_transform s hZ hTZ hBT.symm
  have hm := DatumTransform.mem_maximalIdeal_ringEquiv e
  have htot := t.stalkIdeal_totalTransform_eq_map y s e he
  have hexc : t.exceptional.stalkIdeal y = (Ideal.span {s.toRing zt}).map e := by
    rw [MonoidalTransformation.exceptional, htot, ← hspan]
  have hfilt : ∀ K : Finset (X.presheaf.stalk (t.f y)),
      (K.filter fun z => e (φ z) ∈ maximalIdeal (t.X'.presheaf.stalk y)) =
        K.filter fun z => φ z ∈ maximalIdeal s.ring :=
    fun K => Finset.filter_congr fun z _ => hm (φ z)
  refine ⟨zt, fun z => e (φ z), hzt, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hexc, Ideal.map_span, Set.image_singleton]
    show Ideal.span {e (s.toRing zt)} = Ideal.span {e (φ zt)}
    rw [hφ₂]
  · rw [hm, hφ₂]
    have hztm : zt ∈ maximalIdeal (X.presheaf.stalk (t.f y)) :=
      hZ.1 ▸ Ideal.subset_span (hTZ hzt)
    exact map_nonunit s.toRing zt hztm
  · show e (φ zt) = (t.f.stalkMap y).hom zt
    rw [hφ₂, ← he]
    rfl
  · intro z hz hne
    show e (φ zt) * e (φ z) = (t.f.stalkMap y).hom z
    rw [← map_mul, hφ₂, hφ₃ z hz hne, ← he]
    rfl
  · intro a ha b hb hab
    exact hinj ⟨ha.1, (hm _).mp ha.2⟩ ⟨hb.1, (hm _).mp hb.2⟩ (e.injective hab)
  · have := ExtendsToRSOP.map_ringEquiv e hext
    rw [Finset.image_image] at this
    rw [hfilt]
    exact this
  · intro J hJZ V hV
    rw [Subscheme.strictTransform_stalkIdeal, hexc, htot, hV]
    have hsat := MonoidalTransform.saturation_span_prod s hZ hTZ hBT.symm hJZ hzt hspan hφ₁ hφ₂
      hφ₃ hinj hext
    rw [hfilt, ← map_prod e]
    have h2 : Ideal.span {e (∏ z ∈ (J.erase zt).filter fun z => φ z ∈ maximalIdeal s.ring, φ z)} =
        (Ideal.span {∏ z ∈ (J.erase zt).filter fun z => φ z ∈ maximalIdeal s.ring, φ z}).map e := by
      rw [Ideal.map_span, Set.image_singleton]
    rw [h2, ← hsat, Ideal.map_iSup]
    refine iSup_congr fun n => ?_
    rw [Ideal.map_colon_ringEquiv, Ideal.map_pow, Ideal.map_span s.toRing, Set.image_singleton]
  · intro z hz hzT
    show e (φ z) = (t.f.stalkMap y).hom z
    rw [hφ₁ z hz hzT, ← he]
    rfl
  · intro S hSZ V hV
    rw [Subscheme.strictTransform_stalkIdeal, hexc, htot, hV]
    have hsat := MonoidalTransform.saturation_span_eq_ite_of_subset s hZ hTZ hBT.symm hSZ hzt hφ₁
        hφ₂ hφ₃ hinj hext
    have hmap : (if zt ∈ S then (⊤ : Ideal s.ring) else Ideal.span (φ '' (S : Set _))).map e =
        if zt ∈ S then ⊤ else Ideal.span ((fun z => e (φ z)) '' (S : Set _)) := by
      split_ifs
      · exact Ideal.map_top _
      · rw [Ideal.map_span, Set.image_image]
    rw [← hmap, ← hsat, Ideal.map_iSup]
    refine iSup_congr fun n => ?_
    rw [Ideal.map_colon_ringEquiv, Ideal.map_pow]

end PrepChart2

section PrepAdaptedNC

open IsLocalRing Classical

variable {X : Scheme.{u}}

/-- The stalk-level core of "(1) remains after a blow-up" (p. 291) at a point `y` of the strict
transform `F'` of `F`: if one regular system of parameters `Z` of `O_{X,f(y)}` is adapted to the
center `B` (`B_x = (T)`), to `E` (`E_x = (∏ J)`) and to `F` (`F_x = (S)`), `T, J, S ⊆ Z`, then the
stalk ideals of `E' ∪ E_exc` and of `F'` at `y` are generated by a product, resp. a subset, of one
set extending to a regular system of parameters of `O_{X',y}`.  Unlike Lemma 4 (which needs
`B ⊆ F`), `S` is an arbitrary subset of `Z`: the chart formula
`exists_chart_strictTransform_stalkIdeal_of_subset` is used. -/
theorem MonoidalTransformation.exists_extendsToRSOP_stalkIdeal_of_adapted
    (hX : X.IsNonsingular) {B F E : Subscheme X} (hBns : B.IsNonsingular)
    (t : MonoidalTransformation X B) {y : t.X'}
    {Z T J S : Finset (X.presheaf.stalk (t.f y))}
    (hZ : IsRegularSystemOfParameters (X.presheaf.stalk (t.f y)) Z) (hTZ : T ⊆ Z) (hJZ : J ⊆ Z)
    (hSZ : S ⊆ Z) (hBT : B.stalkIdeal (t.f y) = Ideal.span (T : Set _))
    (hE : E.stalkIdeal (t.f y) = Ideal.span {∏ z ∈ J, z})
    (hF : F.stalkIdeal (t.f y) = Ideal.span (S : Set _))
    (hy : y ∈ (Subscheme.strictTransform t F).pts) :
    ∃ K : Finset (t.X'.presheaf.stalk y), ExtendsToRSOP _ K ∧
      (∃ K₁ ⊆ K, ((Subscheme.strictTransform t E).union t.exceptional).stalkIdeal y =
        Ideal.span {∏ k ∈ K₁, k}) ∧
      (∃ T' ⊆ K, (Subscheme.strictTransform t F).stalkIdeal y =
        Ideal.span (T' : Set (t.X'.presheaf.stalk y))) := by
  have : IsRegularLocalRing (t.X'.presheaf.stalk y) := t.isRegularLocalRing_stalk hX hBns y
  have : IsRegularLocalRing (X.presheaf.stalk (t.f y)) := hX _
  obtain ⟨zt, φ, hzt, hexc, hztm, -, hrel, hinj, hext, hstP, hφ₁, hstS⟩ :=
    t.exists_chart_strictTransform_stalkIdeal_of_subset hX y hZ hTZ hBT
  -- the strict transform of `F`
  have h1 := hstS S hSZ F hF
  have hne : (Subscheme.strictTransform t F).stalkIdeal y ≠ ⊤ :=
    Subscheme.mem_pts_iff_stalkIdeal_ne_top.mp hy
  rw [h1] at hne
  have hztS : zt ∉ S := fun h => hne (by simp [h])
  simp only [hztS, ↓reduceIte] at h1 hne
  have hnu : ∀ q ∈ S, φ q ∈ maximalIdeal (t.X'.presheaf.stalk y) := by
    intro q hq; by_contra h
    exact hne (Ideal.eq_top_of_isUnit_mem _ (Ideal.subset_span ⟨q, hq, rfl⟩)
      ((IsLocalRing.mem_maximalIdeal _).not.mp h |> not_not.mp))
  have hsubK : ∀ z ∈ (J.erase zt).filter (fun z => φ z ∈ maximalIdeal (t.X'.presheaf.stalk y)),
      z ∈ Z ∧ φ z ∈ maximalIdeal (t.X'.presheaf.stalk y) := fun z hz =>
    ⟨hJZ (Finset.mem_of_mem_erase (Finset.mem_filter.mp hz).1), (Finset.mem_filter.mp hz).2⟩
  have hE' := hstP J hJZ E hE
  set K₁' := ((J.erase zt).filter
    (fun z => φ z ∈ maximalIdeal (t.X'.presheaf.stalk y))).image φ with hK₁'
  have hK₁'K : K₁' ⊆ (Z.filter fun z => φ z ∈ maximalIdeal (t.X'.presheaf.stalk y)).image φ := by
    intro a ha
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp ha
    exact Finset.mem_image_of_mem φ (Finset.mem_filter.mpr (hsubK z hz))
  have hztK : φ zt ∈ (Z.filter fun z => φ z ∈ maximalIdeal (t.X'.presheaf.stalk y)).image φ :=
    Finset.mem_image_of_mem φ (Finset.mem_filter.mpr ⟨hTZ hzt, hztm⟩)
  have hE'prod : (Subscheme.strictTransform t E).stalkIdeal y = Ideal.span {∏ k ∈ K₁', k} := by
    rw [hE', hK₁', ← DatumTransform.prod_image_eq φ hinj _ hsubK]
  refine ⟨_, hext, ⟨K₁' ∪ {φ zt}, Finset.union_subset hK₁'K (Finset.singleton_subset_iff.mpr hztK),
    ?_⟩, ⟨S.image φ, ?_, ?_⟩⟩
  · show ((Subscheme.strictTransform t E) ⊓ t.exceptional).stalkIdeal y = _
    have hexc' : t.exceptional.stalkIdeal y = Ideal.span {∏ k ∈ ({φ zt} : Finset _), k} := by
      rw [hexc, Finset.prod_singleton]
    rw [Subscheme.stalkIdeal_inf_eq, hE'prod, hexc',
      DatumTransform.span_prod_inf_of_subset hext hK₁'K (Finset.singleton_subset_iff.mpr hztK)]
  · intro a ha
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp ha
    exact Finset.mem_image_of_mem φ (Finset.mem_filter.mpr ⟨hSZ hq, hnu q hq⟩)
  · rw [h1, Finset.coe_image]

end PrepAdaptedNC

end PrepPhase19

/-! ### Lemma 4 on a neighbourhood

"Lemma 4, §2, Ch. IV" is cited on pp. 290 (Proposition 5), 294 (Lemma (AB.1)) and 307 (Remark 1) for a
datum which is resolved only at the points considered; the citation implicitly localizes. -/

namespace DatumI.Raw

/-- **Lemma 4 of Ch. IV §2, applied as cited in the proofs of Lemma (AB.1) (p. 294), Proposition 5
(p. 290) and Remark 1 (p. 307)**: if `ℜ` is resolved at a point `x` of the permissible center `B`, then the
principal part `E'` of the transform `f*(ℜ)` has only normal crossings with `W'` at every point `y` of `W'`
over `x`.  The proof restricts to an open neighbourhood `O` of `x` on which the hypotheses of Lemma 4 hold,
applies Lemma 4 to the monoidal transformation of `O` with center `B ∩ O` (the flat base change of `f`)
and carries the conclusion back to `X'` along the lift `f⁻¹(O) → X'`.

Deviation from the paper (gap filled): the paper cites Lemma 4, which is stated for a non-singular
irreducible `W` with `E = ⋃ E_i` having only normal crossings with `W` and `B` at every point, for a datum
resolved only at `x`; the citation implicitly localizes.  Lean restricts to `O = V ∩ U₁ ∩ O₂`, where `V` is an
affine open in which the ideal of `W` is prime (`W ∩ O` irreducible; `Subscheme.exists_isAffineOpen_prime_system`),
`U₁` an open set on which `E` has only normal crossings with `W` (Lemma 1 of §1, `Subscheme.exists_isOpen_hasOnlyNormalCrossingsWithAt`)
and `O₂` the open set of simple points of `W` (p. 161 (iii), `Subscheme.exists_isOpen_isSimpleAt`), and pulls
the datum, the center and a presentation `E = ⋃ E_i` (`DatumI.Raw.isUnionOfDivisors_of_isNonsingular`) back
to `O`. -/
theorem hasOnlyNormalCrossingsWithAt_transform_of_resolvedAt_localized [Hironaka.Cited.IsHironakaBaseIsClosedSingularLocus.{u}]
    {X : Scheme.{u}} [IsAlgebraicScheme X] (hXirr : IrreducibleSpace X) (hX : X.IsNonsingular)
    {B : Subscheme X} {ℜ : DatumI.Raw X}
    (hℜ : ℜ.IsDatum) (hB : ℜ.IsPermissible B) (t : MonoidalTransformation X B) {x : X}
    (hxB : x ∈ B.pts) (hres : ℜ.ResolvedAt x) {y : t.X'}
    (hy : y ∈ (Subscheme.strictTransform t ℜ.W).pts) (hyx : t.f.base y = x) :
    (ℜ.transform t).E.HasOnlyNormalCrossingsWithAt (Subscheme.strictTransform t ℜ.W) y := by
  classical
  have hXalg : IsAlgebraicScheme X := inferInstance
  have hXns : X.IsNonsingular := hX
  -- an open neighbourhood `O` of `x` on which the hypotheses of Lemma 4 hold
  obtain ⟨z0, t0, V, hV, hxV, f, -, -, -, -, hG, hDV, -, -⟩ :=
    Subscheme.exists_isAffineOpen_prime_system hXns ℜ.E ℜ.W x hres.2.2
  have hprime : (ℜ.W.ideal ⟨V, hV⟩).IsPrime := by
    have := (hG ∅ (Finset.empty_mem_powerset _)).1
    rwa [Finset.union_empty, ← hDV] at this
  have hirrV := Subscheme.isIrreducible_pts_inter_of_isPrime ℜ.W hV hprime
  obtain ⟨U₁, hU₁, hxU₁, hU₁nc⟩ := Subscheme.exists_isOpen_hasOnlyNormalCrossingsWithAt hXns ℜ.E ℜ.W x hres.2.2
  obtain ⟨O₂, hO₂, hO₂s⟩ := Subscheme.exists_isOpen_isSimpleAt ℜ.W
  have hxW : x ∈ ℜ.W.pts := hres.1.1
  have hxO₂ : x ∈ O₂ := (hO₂s x hxW).mp hres.1
  let O : X.Opens := ⟨U₁ ∩ O₂, hU₁.inter hO₂⟩ ⊓ V
  have hxO : x ∈ O := ⟨⟨hxU₁, hxO₂⟩, hxV⟩
  let j : O.toScheme ⟶ X := O.ι
  have hjO : ∀ z : O.toScheme, j z ∈ O := fun z => z.2
  -- the scheme `O`
  have hOalg : IsAlgebraicScheme O.toScheme := isAlgebraicScheme_of_isOpenImmersion j
  have hOns : O.toScheme.IsNonsingular := LocSucc.isNonsingular j hXns
  have : Nonempty O.toScheme := ⟨⟨x, hxO⟩⟩
  have : IrreducibleSpace O.toScheme := irreducibleSpace_of_flat_preimmersion j
  -- the pulled-back datum, center and monoidal transformation
  let ℜZ : DatumI.Raw O.toScheme := ℜ.pullback j
  have hℜZ : ℜZ.IsDatum := isDatum_pullback j hℜ
  have hBZ : ℜZ.IsPermissible (Subscheme.totalTransform j B) := isPermissible_pullback j hB
  have hpB : ∀ z : O.toScheme, z ∈ (Subscheme.totalTransform j B).pts ↔ j z ∈ B.pts := fun z => by
    rw [FlatPreimm.pts_totalTransform]; rfl
  have hpW : ∀ z : O.toScheme, z ∈ (Subscheme.totalTransform j ℜ.W).pts ↔ j z ∈ ℜ.W.pts :=
    fun z => by rw [FlatPreimm.pts_totalTransform]; rfl
  have hBne : Subscheme.totalTransform j B ≠ Subscheme.empty := fun h => by
    have h1 : (⟨x, hxO⟩ : O.toScheme) ∈ (Subscheme.totalTransform j B).pts := (hpB _).mpr hxB
    rw [h, Subscheme.pts_empty] at h1
    exact h1
  obtain ⟨hBZns, hBZirr⟩ := hBZ.1.resolve_left hBne
  have hBW : B.IsContainedIn ℜ.W := by
    have := hB.2.1.2.2.2.2 (Fin.last ℜ.β)
    simpa [DatumI.Raw.extendBy] using this
  have hBWZ : (Subscheme.totalTransform j B).IsContainedIn (Subscheme.totalTransform j ℜ.W) :=
    fun U => FlatPreimm.totalTransform_mono j (fun U' => hBW U') U
  let ts : MonoidalTransformation O.toScheme (Subscheme.totalTransform j B) := t.baseChange j
  obtain ⟨j', hj'f, hj'p, -, hj'range, hj'exc, hj'st⟩ :=
    MonoidalTransformation.exists_lift t j (rfl : Subscheme.totalTransform j B = _) ts
  have := hj'f
  have := hj'p
  -- a presentation of `E` and its pull-back
  obtain ⟨α, E, hE, hEu⟩ := DatumI.Raw.isUnionOfDivisors_of_isNonsingular hX ℜ hℜ
  let EZ : Fin α → Subscheme O.toScheme := fun i => Subscheme.totalTransform j (E i)
  have hEZ : ∀ i, (EZ i).IsNonsingularIrreducibleCodimOne := fun i =>
    FlatPreimm.isNonsingularIrreducibleCodimOne_totalTransform j (E i) (hE i)
  have hEZu : ℜZ.E = Subscheme.unionFam EZ := by
    show Subscheme.totalTransform j ℜ.E = ⨅ i, EZ i
    rw [hEu, FlatPreimm.totalTransform_iInf]
  have hunion : Subscheme.unionFam EZ = Subscheme.totalTransform j ℜ.E := hEZu.symm
  -- the hypotheses of Lemma 4 on `O`
  have hWZns : (Subscheme.totalTransform j ℜ.W).IsNonsingular := by
    refine Subscheme.isNonsingular_of_stalk_quot _ fun z hz => ?_
    have hzW : j z ∈ ℜ.W.pts := (hpW z).mp hz
    have hzO₂ : j z ∈ O₂ := (hjO z).1.2
    exact ((FlatPreimm.isSimpleAt_totalTransform_iff j ℜ.W z).mpr ((hO₂s _ hzW).mpr hzO₂)).2
  have hWZirr : (Subscheme.totalTransform j ℜ.W).IsIrreducible := by
    refine Subscheme.isIrreducible_of_pts _ ?_
    have hset : (Subscheme.totalTransform j ℜ.W).pts = j.base ⁻¹' (ℜ.W.pts ∩ (V : Set X)) := by
      ext z
      rw [FlatPreimm.pts_totalTransform]
      exact ⟨fun h => ⟨h, (hjO z).2⟩, fun h => h.1⟩
    rw [hset]
    exact ⟨⟨⟨x, hxO⟩, hxW, hxV⟩, hirrV.isPreirreducible.preimage j.isOpenEmbedding⟩
  have hiiW : (Subscheme.unionFam EZ).HasOnlyNormalCrossingsWith (Subscheme.totalTransform j ℜ.W) :=
    fun z hz => by
      rw [hunion]
      exact (FlatPreimm.hasOnlyNormalCrossingsWithAt_totalTransform_iff j ℜ.E ℜ.W z).mpr
        (hU₁nc (j z) ⟨(hjO z).1.1, (hpW z).mp hz⟩)
  have hiiB : (Subscheme.unionFam EZ).HasOnlyNormalCrossingsWith (Subscheme.totalTransform j B) :=
    fun z hz => by
      rw [hunion]
      exact (FlatPreimm.hasOnlyNormalCrossingsWithAt_totalTransform_iff j ℜ.E B z).mpr
        ((hB.2.2 (j z) ((hpB z).mp hz)).2.2)
  have hi : (Subscheme.unionFam EZ).HasOnlyNormalCrossings := by
    rw [← hEZu]; exact hℜZ.2.2.1
  -- Lemma 4 on `O`
  have hL4 := MonoidalTransformation.hasOnlyNormalCrossingsWith_strictTransform_and_inter_exceptional
    hOalg hOns ‹IrreducibleSpace O.toScheme› (Subscheme.totalTransform j ℜ.W) hWZns hWZirr
    (Subscheme.totalTransform j B) hBZns hBZirr hBWZ α EZ hEZ hi hiiW hiiB ts
  -- the conclusion, carried back to `X'`
  have hEeq : ((Subscheme.unionFam fun k => Subscheme.strictTransform ts (EZ k)).union
      ts.exceptional) = (ℜZ.transform ts).E := by
    show _ = (Subscheme.strictTransform ts ℜZ.E).union ts.exceptional
    rw [hEZu]
    show _ = (Subscheme.strictTransform ts (⨅ i, EZ i)).union ts.exceptional
    rw [Subscheme.strictTransform_iInf_fintype hOns ts EZ]
    rfl
  have hyr : y ∈ Set.range j'.base := by
    rw [hj'range]
    show t.f.base y ∈ Set.range j.base
    rw [hyx]
    exact ⟨⟨x, hxO⟩, rfl⟩
  obtain ⟨yZ, rfl⟩ := hyr
  have hst : Subscheme.totalTransform j' (Subscheme.strictTransform t ℜ.W) =
      Subscheme.strictTransform ts (Subscheme.totalTransform j ℜ.W) := hj'st ℜ.W
  have hyZ : yZ ∈ (Subscheme.strictTransform ts (Subscheme.totalTransform j ℜ.W)).pts := by
    rw [← hst, FlatPreimm.pts_totalTransform]
    exact hy
  have hpull : (ℜ.transform t).pullback j' = ℜZ.transform ts :=
    pullback_transform_of_lift t j ts j' hj'exc hj'st ℜ
  refine (FlatPreimm.hasOnlyNormalCrossingsWithAt_totalTransform_iff j' (ℜ.transform t).E
    (Subscheme.strictTransform t ℜ.W) yZ).mp ?_
  rw [hst]
  have hE' : Subscheme.totalTransform j' (ℜ.transform t).E = (ℜZ.transform ts).E :=
    congrArg Raw.E hpull
  rw [hE', ← hEeq]
  exact hL4.1 yZ hyZ

end DatumI.Raw

/-- A subscheme `D` with `E` having only normal crossings with `D` at a point `y` of `D` of a
non-singular scheme is simple at `y`. (Re-proved here from the definition; the paper uses this
tacitly on p. 290 when passing from the normal crossings of `E'` with `W'` to the simplicity of
`W'`.) -/
theorem Subscheme.IsSimpleAt.of_hasOnlyNormalCrossingsWithAt {Y : Scheme.{u}} {E D : Subscheme Y}
    {y : Y} (hY : Y.IsSimpleAt y) (hyD : y ∈ D.pts) (h : E.HasOnlyNormalCrossingsWithAt D y) :
    D.IsSimpleAt y := by
  obtain ⟨z, hz, -, T, hTz, hD⟩ := h
  have : IsRegularLocalRing (Y.presheaf.stalk y) := hY
  refine ⟨hyD, ?_⟩
  rw [hD]
  exact ((ExtendsToRSOP.of_isRegularSystemOfParameters hz).mono hTz).isRegularLocalRing_quotient

/-- Off the center, resolvedness is transported by a monoidal transformation: if `y` is not on
`f⁻¹(B)` and `ℜ` is resolved at `f(y)`, then `f*(ℜ)` is resolved at `y` (`f` is a local
isomorphism there). -/
theorem DatumI.Raw.resolvedAt_transform_of_resolvedAt_of_notMem_exceptional {X : Scheme.{u}}
    {B : Subscheme X} {ℜ : DatumI.Raw X}
    (hℜ : ℜ.IsDatum) (t : MonoidalTransformation X B) {y : t.X'}
    (hyE : y ∉ t.exceptional.pts) (hres : ℜ.ResolvedAt (t.f.base y)) :
    (ℜ.transform t).ResolvedAt y := by
  obtain ⟨Z, ι, j', h1, h2, h3, h4, -, hcomp, hrι, hrange, hexc, htt⟩ :=
    Hironaka.DatumTransform.exists_flat_isPreimmersion_off_center t
  have hyr : y ∈ Set.range j'.base := by rw [hrange]; exact hyE
  obtain ⟨u, rfl⟩ := hyr
  rw [hcomp] at hres
  refine ⟨?_, fun j => ?_, ?_⟩
  · refine (FlatPreimm.isSimpleAt_totalTransform_iff j' _ u).mp ?_
    show (Subscheme.totalTransform j' (Subscheme.strictTransform t ℜ.W)).IsSimpleAt u
    rw [htt]
    exact (FlatPreimm.isSimpleAt_totalTransform_iff ι _ u).mpr hres.1
  · refine (FlatPreimm.isNormallyFlatAlongAt'_totalTransform_iff j' _ _
      ((hℜ.2.2.2.2 j).strictTransform t) u).mp ?_
    show Subscheme.IsNormallyFlatAlongAt'
      (Subscheme.totalTransform j' (Subscheme.strictTransform t (ℜ.V j)))
      (Subscheme.totalTransform j' (Subscheme.strictTransform t ℜ.W)) u
    rw [htt, htt]
    exact (FlatPreimm.isNormallyFlatAlongAt'_totalTransform_iff ι _ _
      (hℜ.2.2.2.2 j) u).mpr (hres.2.1 j)
  · refine (FlatPreimm.hasOnlyNormalCrossingsWithAt_totalTransform_iff j' _ _ u).mp ?_
    have hE' : Subscheme.totalTransform j' ((ℜ.transform t).E) =
        Subscheme.totalTransform ι ℜ.E := by
      show Subscheme.totalTransform j'
        ((Subscheme.strictTransform t ℜ.E).union t.exceptional) = _
      rw [FlatPreimm.totalTransform_union, htt, hexc]
      exact inf_top_eq _
    show (Subscheme.totalTransform j' (ℜ.transform t).E).HasOnlyNormalCrossingsWithAt
      (Subscheme.totalTransform j' (Subscheme.strictTransform t ℜ.W)) u
    rw [hE', htt]
    exact (FlatPreimm.hasOnlyNormalCrossingsWithAt_totalTransform_iff ι _ _ u).mpr hres.2.2

/-- Lemma 4 of this section and Corollary 2 of Theorem 5 (Ch. III), at one point (p. 290: "in
view of Lemma 4 of this section and Corollary 2 of Theorem 5, §6, Ch. III"): if `B` is a
permissible center for `ℜ`, `W − B` is dense in `W`, and `ℜ` is resolved at `f(y)`, then `f*(ℜ)`
is resolved at `y`.

Deviation from the paper (gap filled): the paper cites the two results; Lean applies Lemma 4 itself on
a neighbourhood of `f(y)` on which its hypotheses hold
(`DatumI.Raw.hasOnlyNormalCrossingsWithAt_transform_of_resolvedAt_localized`) and proves the case
distinction (`y` on or off the exceptional divisor; off it `f` is a local isomorphism), the
passage from `ℜ.IsPermissible B` to the non-singular irreducible `B` of Corollary 2 (`B` is
nonempty since `f(y) ∈ B`), and the simplicity of `W'` at `y` (from the normal crossings with
`W'`). The density of `W − B` in `W` is a hypothesis; it comes from the open restriction
(`DatumI.Raw.pts_subset_closure_diff_of_isPermissibleOpen`). -/
theorem DatumI.Raw.resolvedAt_transform_of_resolvedAt [Hironaka.Cited.IsHironakaBaseIsClosedSingularLocus.{u}] [Hironaka.Cited.IsSeparableFieldExtensionIff.{u}] {X : Scheme.{u}} [IsAlgebraicScheme X]
    (hXirr : IrreducibleSpace X) (hX : X.IsNonsingular) {B : Subscheme X} {ℜ : DatumI.Raw X}
    (hℜ : ℜ.IsDatum) (hB : ℜ.IsPermissible B) (hdense : ℜ.W.pts ⊆ closure (ℜ.W.pts \ B.pts))
    (t : MonoidalTransformation X B) {y : t.X'} (hyW : y ∈ (Subscheme.strictTransform t ℜ.W).pts)
    (hres : ℜ.ResolvedAt (t.f.base y)) : (ℜ.transform t).ResolvedAt y := by
  by_cases hyE : y ∈ t.exceptional.pts
  · have hxB : t.f.base y ∈ B.pts := by
      rw [MonoidalTransformation.pts_exceptional] at hyE
      exact hyE
    have hBne : B ≠ Subscheme.empty := fun hE => by
      have h2 := congrArg Subscheme.pts hE
      rw [h2, Subscheme.pts_empty] at hxB
      exact hxB
    obtain ⟨hBns, hBirr⟩ := hB.1.resolve_left hBne
    have hNF : ∀ j, Subscheme.IsNormallyFlatAlongAt' (Subscheme.strictTransform t (ℜ.V j))
        (Subscheme.strictTransform t ℜ.W) y := fun j =>
      isNormallyFlatAlongAt'_strictTransform hXirr hX (ℜ.V j) ℜ.W B (hℜ.2.2.2.2 j)
        (DatumI.Raw.IsPermissible.isContainedIn_W hB) hBns hBirr hdense t _ hxB hres.1
        (hres.2.1 j) y hyW rfl
    have hnc := DatumI.Raw.hasOnlyNormalCrossingsWithAt_transform_of_resolvedAt_localized hXirr hX
      hℜ hB t hxB hres hyW rfl
    have hX' := (t.isNonsingular_and_isNonsingular_exceptional hX hBns).1
    exact ⟨Subscheme.IsSimpleAt.of_hasOnlyNormalCrossingsWithAt (hX' y) hyW hnc, hNF, hnc⟩
  · exact DatumI.Raw.resolvedAt_transform_of_resolvedAt_of_notMem_exceptional hℜ t hyE hres

/-- The density of `W − B` in `W` for a center permissible for an open restriction `U` (used
tacitly on p. 290 for Corollary 2 of Theorem 5): `U ∩ W` is dense in `W` and misses `B`.

Deviation from the paper (gap filled): the paper does not mention the density, which is a
hypothesis of Corollary 2 (`cor:III.thm5-2`). -/
theorem DatumI.Raw.pts_subset_closure_diff_of_isPermissibleOpen {X : Scheme.{u}}
    {ℜ : DatumI.Raw X} {U : Set X} {B : Subscheme X} (hU : ℜ.IsOpenRestriction U)
    (hB : ℜ.IsPermissibleOpen U B) : ℜ.W.pts ⊆ closure (ℜ.W.pts \ B.pts) := by
  obtain ⟨⟨U₀, -, hUeq⟩, hdU, -⟩ := hU
  intro w hw
  refine closure_mono ?_ (hdU hw)
  intro u hu
  exact ⟨(hUeq ▸ hu : u ∈ U₀ ∩ ℜ.W.pts).2, fun huB => (hB.2 huB).2 hu⟩

/-- Succession version of `DatumI.Raw.resolvedAt_transform_of_resolvedAt` for an open restriction:
along a succession permissible for `(ℜ, U)`, the image of the points of `W^{(m)}` where `f*(ℜ)` is
not resolved lies in the points of `W` where `ℜ` is not resolved (induction on the succession;
the stages stay good data by `IsGoodDatumI.transform_open`). -/
theorem MonoidalSuccession.resolvedAt_transformI_of_resolvedAt_open [Hironaka.Cited.IsHironakaBaseIsClosedSingularLocus.{u}] [Hironaka.Cited.MonoidalTransformationExistsIsProper.{u}] [Hironaka.Cited.IsSeparableFieldExtensionIff.{u}] {N n : ℕ}
    {X Y : Scheme.{u}} (s : MonoidalSuccession X Y)
    {ℜ : DatumI.Raw X} {U : Set X} (h : IsGoodDatumI N n X ℜ) (hU : ℜ.IsOpenRestriction U)
    (hs : s.IsPermissibleIOpen ℜ U) {y : Y}
    (hyW : y ∈ (s.transformI ℜ).W.pts) (hres : ℜ.ResolvedAt (s.composite.base y)) :
    (s.transformI ℜ).ResolvedAt y := by
  induction s with
  | nil X => exact hres
  | cons B t rest ih =>
    obtain ⟨h', hU'⟩ := IsGoodDatumI.transform_open h hU hs.1 t
    have hyW' : y ∈ (rest.transformI (ℜ.transform t)).W.pts := hyW
    rw [MonoidalSuccession.transformI_W] at hyW'
    have hx'W : rest.composite.base y ∈ (ℜ.transform t).W.pts :=
      rest.pts_strictTransform_subset _ hyW'
    have hres' : ℜ.ResolvedAt (t.f.base (rest.composite.base y)) := hres
    have := h.1.1
    have hone := DatumI.Raw.resolvedAt_transform_of_resolvedAt h.1.2.2.1 h.1.2.1 h.2.1 hs.1.1
      (DatumI.Raw.pts_subset_closure_diff_of_isPermissibleOpen hU hs.1) t hx'W hres'
    exact ih h' hU' hs.2 hyW hone

/-! ### Lemma 5 (pp. 287–288) -/

section PrepSaturationAlgebra

open IsLocalRing in
/-- In a noetherian local domain, the saturation of a principal ideal `(ε)` with respect to a
prime element `x` is principal: `ε = xᵏ ε'` with `x ∤ ε'`, and `⋃ₙ ((ε) : xⁿ) = (ε')`. -/
theorem exists_iSup_colon_pow_eq_span_singleton {R : Type u} [CommRing R] [IsDomain R]
    [IsNoetherianRing R] [IsLocalRing R] {x : R} (hx : Prime x) (hxm : x ∈ maximalIdeal R)
    (ε : R) :
    ∃ ε' : R, ⨆ n : ℕ, (Ideal.span {ε}).colon ((Ideal.span {x} ^ n : Ideal R) : Set R) =
      Ideal.span {ε'} := by
  classical
  by_cases hε : ε = 0
  · subst hε
    refine ⟨0, ?_⟩
    apply le_antisymm
    · refine iSup_le fun n a ha => ?_
      have h1 := Submodule.mem_colon.mp ha (x ^ n)
        (by rw [Ideal.span_singleton_pow]; exact Ideal.mem_span_singleton_self _)
      rw [Ideal.span_singleton_eq_bot.mpr rfl, Submodule.mem_bot, smul_eq_mul] at h1
      rw [Ideal.span_singleton_eq_bot.mpr rfl, Submodule.mem_bot]
      exact (mul_eq_zero.mp h1).resolve_right (pow_ne_zero n hx.ne_zero)
    · simp
  -- the exact power of `x` dividing `ε`
  have hex : ∃ n : ℕ, ¬ x ^ n ∣ ε := by
    by_contra h
    push Not at h
    have hmem : ε ∈ ⨅ n : ℕ, (Ideal.span {x}) ^ n := by
      refine Submodule.mem_iInf _ |>.mpr fun n => ?_
      rw [Ideal.span_singleton_pow]; exact Ideal.mem_span_singleton.mpr (h n)
    have hne : Ideal.span {x} ≠ ⊤ := by
      rw [Ne, Ideal.span_singleton_eq_top]
      exact (mem_maximalIdeal x).mp hxm
    rw [Ideal.iInf_pow_eq_bot_of_isLocalRing _ hne, Submodule.mem_bot] at hmem
    exact hε hmem
  have hN0 : Nat.find hex ≠ 0 := by
    intro h0
    have := Nat.find_spec hex
    rw [h0] at this
    exact this (by simp)
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hN0
  have hk2 : ¬ x ^ (k + 1) ∣ ε := by
    have h := Nat.find_spec hex
    rw [hk] at h
    exact h
  have hk1 : x ^ k ∣ ε := by
    by_contra h
    exact Nat.find_min hex (by omega : k < Nat.find hex) h
  obtain ⟨ε', hε'⟩ := hk1
  have hxε' : ¬ x ∣ ε' := fun h => hk2 (by
    obtain ⟨d, hd⟩ := h
    exact ⟨d, by rw [hε', hd]; ring⟩)
  have hxk : x ^ k ≠ 0 := pow_ne_zero k hx.ne_zero
  -- key divisibility claim
  have key : ∀ j : ℕ, ∀ a c : R, a * x ^ (k + j) = c * (x ^ k * ε') → ε' ∣ a := by
    intro j
    induction j with
    | zero =>
      intro a c h
      simp only [add_zero] at h
      have : a = c * ε' := mul_right_cancel₀ hxk (by linear_combination h)
      exact ⟨c, by rw [this]; ring⟩
    | succ j ih =>
      intro a c h
      have h1 : a * x ^ (j + 1) = c * ε' := by
        apply mul_left_cancel₀ hxk
        calc x ^ k * (a * x ^ (j + 1)) = a * x ^ (k + (j + 1)) := by ring
          _ = c * (x ^ k * ε') := h
          _ = x ^ k * (c * ε') := by ring
      have hdvd : x ∣ c * ε' := ⟨a * x ^ j, by rw [← h1]; ring⟩
      obtain ⟨c', rfl⟩ := (hx.dvd_or_dvd hdvd).resolve_right hxε'
      refine ih a c' ?_
      have h2 : a * x ^ j = c' * ε' := by
        apply mul_left_cancel₀ hx.ne_zero
        calc x * (a * x ^ j) = a * x ^ (j + 1) := by ring
          _ = x * c' * ε' := h1
          _ = x * (c' * ε') := by ring
      calc a * x ^ (k + j) = x ^ k * (a * x ^ j) := by ring
        _ = x ^ k * (c' * ε') := by rw [h2]
        _ = c' * (x ^ k * ε') := by ring
  refine ⟨ε', le_antisymm (iSup_le fun n a ha => ?_) ?_⟩
  · have h1 := Submodule.mem_colon.mp ha (x ^ n)
      (by rw [Ideal.span_singleton_pow]; exact Ideal.mem_span_singleton_self _)
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp (by simpa [smul_eq_mul] using h1)
    rw [hε'] at hc
    rw [Ideal.mem_span_singleton]
    rcases le_total n k with hnk | hkn
    · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hnk
      refine ⟨c * x ^ d, ?_⟩
      apply mul_left_cancel₀ (pow_ne_zero n hx.ne_zero)
      calc x ^ n * a = a * x ^ n := by ring
        _ = c * (x ^ (n + d) * ε') := hc.symm
        _ = x ^ n * (ε' * (c * x ^ d)) := by ring
    · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hkn
      exact key j a c hc.symm
  · rw [Ideal.span_le, Set.singleton_subset_iff]
    refine Ideal.mem_iSup_of_mem k (Submodule.mem_colon.mpr fun p hp => ?_)
    rw [Ideal.span_singleton_pow, SetLike.mem_coe, Ideal.mem_span_singleton'] at hp
    obtain ⟨q, rfl⟩ := hp
    rw [smul_eq_mul, hε', Ideal.mem_span_singleton']
    exact ⟨q, by ring⟩

end PrepSaturationAlgebra

section PrepStrictTransformPrincipal

open IsLocalRing

variable {X : Scheme.{u}} {B : Subscheme X}

/-- At a point `y` of the exceptional subscheme, the stalk of the strict transform of a
subscheme `V` whose ideal at `f(y)` is principal is principal: the saturation of a principal
ideal by the prime element generating the ideal of `f⁻¹(B)` is principal
(`exists_iSup_colon_pow_eq_span_singleton`). -/
theorem MonoidalTransformation.exists_stalkIdeal_strictTransform_eq_span
    (hX : X.IsNonsingular) (hB : B.IsNonsingular) (t : MonoidalTransformation X B)
    {V : Subscheme X} {y : t.X'} (hy : y ∈ t.exceptional.pts)
    (hV : ∃ e, V.stalkIdeal (t.f y) = Ideal.span {e}) :
    ∃ ε, (Subscheme.strictTransform t V).stalkIdeal y = Ideal.span {ε} := by
  have : IsRegularLocalRing (t.X'.presheaf.stalk y) := t.isRegularLocalRing_stalk hX hB y
  have := isDomain_of_isRegularLocalRing (t.X'.presheaf.stalk y)
  have : IsRegularLocalRing (X.presheaf.stalk (t.f y)) := hX _
  have := isDomain_of_isRegularLocalRing (X.presheaf.stalk (t.f y))
  obtain ⟨e₀, he₀⟩ := hV
  obtain ⟨s, e, he, hE⟩ := t.exists_monoidalTransform_stalk_exceptional y
  have hreg := t.isRegularLocalRing_quotient_exceptional hX hB hy
  have hdom := isDomain_of_isRegularLocalRing (t.X'.presheaf.stalk y ⧸ t.exceptional.stalkIdeal y)
  have hprime : (t.exceptional.stalkIdeal y).IsPrime :=
    (Ideal.Quotient.isDomain_iff_prime _).mp hdom
  have hne : t.exceptional.stalkIdeal y ≠ ⊤ := Subscheme.mem_pts_iff_stalkIdeal_ne_top.mp hy
  have hxR0 : s.xR ≠ 0 := fun h => s.x_ne_zero (s.toRing_injective
    ((show s.toRing s.x = s.xR from rfl).trans (h.trans (map_zero _).symm)))
  have hxx0 : e s.xR ≠ 0 := (map_ne_zero_iff e e.injective).mpr hxR0
  have hxprime : Prime (e s.xR) := by
    rw [← Ideal.span_singleton_prime hxx0, ← hE]; exact hprime
  have hxm : e s.xR ∈ maximalIdeal (t.X'.presheaf.stalk y) := by
    rw [mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    apply hne
    rw [hE, Ideal.span_singleton_eq_top]; exact hu
  obtain ⟨ε', hε'⟩ := exists_iSup_colon_pow_eq_span_singleton hxprime hxm
    (e (s.toRing e₀))
  refine ⟨ε', ?_⟩
  rw [Subscheme.strictTransform_stalkIdeal, hE, t.stalkIdeal_totalTransform_eq_map y s e he, he₀,
    Ideal.map_span, Ideal.map_span, Set.image_singleton, Set.image_singleton]
  exact hε'

end PrepStrictTransformPrincipal

section PrepIsoConsequences

variable {X : Scheme.{u}}

/-- Transport of the properties of `W` to `W' ≅ W`: `W'` is non-singular and irreducible. -/
theorem Subscheme.isNonsingular_and_isIrreducible_of_iso {Y : Scheme.{u}} {W : Subscheme X}
    {W' : Subscheme Y}
    (e : W'.toScheme ≅ W.toScheme) (hWns : W.IsNonsingular) (hWirr : W.IsIrreducible) :
    W'.IsNonsingular ∧ W'.IsIrreducible := by
  refine ⟨fun y => ?_, ?_⟩
  · have : IsRegularLocalRing (W.toScheme.presheaf.stalk (e.hom y)) := hWns (e.hom y)
    have e' := asIso (e.hom.stalkMap y)
    exact IsRegularLocalRing.of_ringEquiv e'.commRingCatIsoToRingEquiv
  · have : IrreducibleSpace W.toScheme := hWirr
    exact Function.Surjective.irreducibleSpace (f := e.inv) (Scheme.Hom.continuous _)
      (e.inv.surjective)

/-- If `e : W' ≅ W` is compatible with the immersions, the points of `W'` are exactly the images
`g w` of the points `w` of `W` under `g = ι' ∘ e⁻¹`, and `f ∘ g = ι`. -/
theorem MonoidalTransformation.exists_map_of_iso {F : Subscheme X} (t : MonoidalTransformation X F)
    (W : Subscheme X) (e : (Subscheme.strictTransform t W).toScheme ≅ W.toScheme)
    (he : e.hom ≫ W.ι = (Subscheme.strictTransform t W).ι ≫ t.f) :
    ∃ g : W.toScheme → t.X', Continuous g ∧ (∀ w, t.f (g w) = W.ι w) ∧
      (∀ w, g w ∈ (Subscheme.strictTransform t W).pts) ∧
      ∀ z ∈ (Subscheme.strictTransform t W).pts, ∃ w, g w = z := by
  have h : e.inv ≫ ((Subscheme.strictTransform t W).ι ≫ t.f) = W.ι := by
    rw [← he, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  refine ⟨fun w => (Subscheme.strictTransform t W).ι (e.inv w),
    (Scheme.Hom.continuous _).comp (Scheme.Hom.continuous _), fun w => ?_, fun w => ?_, ?_⟩
  · calc t.f ((Subscheme.strictTransform t W).ι (e.inv w))
        = (e.inv ≫ ((Subscheme.strictTransform t W).ι ≫ t.f)) w := rfl
      _ = W.ι w := by rw [h]
  · have : (Subscheme.strictTransform t W).ι (e.inv w) ∈
        Set.range (Subscheme.strictTransform t W).ι := ⟨e.inv w, rfl⟩
    rwa [Scheme.IdealSheafData.range_subschemeι] at this
  · intro z hz
    have hz' : z ∈ Set.range (Subscheme.strictTransform t W).ι := by
      rw [Scheme.IdealSheafData.range_subschemeι]; exact hz
    obtain ⟨y, rfl⟩ := hz'
    refine ⟨e.hom y, ?_⟩
    show (Subscheme.strictTransform t W).ι ((e.hom ≫ e.inv) y) = _
    rw [Iso.hom_inv_id]; rfl

end PrepIsoConsequences

/-- `f̃⁻¹(D)` of Lemma 5: for a monoidal transformation `f : X' → X` inducing an isomorphism
`f̃` of the strict transform `W'` of `W` onto `W`, and a subscheme `D` of `W`, the subscheme
`f̃⁻¹(D) = red(W' ∩ f⁻¹(D))` of `X'`.  (In the proof of Lemma 5 Hironaka himself writes
`f̃⁻¹(F)` in exactly this way, as `W' ∩ f⁻¹(F)`.) -/
def Subscheme.inducedPreimage {X : Scheme.{u}} {B : Subscheme X}
    (t : MonoidalTransformation X B) (W D : Subscheme X) : Subscheme t.X' :=
  Subscheme.ofClosed ((Subscheme.strictTransform t W).support ⊓
    (Subscheme.totalTransform t.f D).support)

/-- One stage `(X^{(i)}, W^{(i)}, E^{(i)}, F^{(i)})` of the iteration described in the
statement of Lemma 5 (pp. 287–288). -/
structure IterationStage : Type (u + 1) where
  /-- The ambient scheme `X^{(i)}`. -/
  X : Scheme.{u}
  /-- The strict transform `W^{(i)}` of `W`. -/
  W : Subscheme X
  /-- The strict transform `E^{(i)}` of `E`. -/
  E : Subscheme X
  /-- The center `F^{(i)}` of the next monoidal transformation. -/
  F : Subscheme X

/-- The next stage of the iteration of Lemma 5: `X^{(i+1)} = X'` is the monoidal transform of
`X^{(i)}` with center `F^{(i)}`, `W^{(i+1)}` and `E^{(i+1)}` are the strict transforms of
`W^{(i)}` and `E^{(i)}`, and `F^{(i+1)}` is "the image of `F^{(i)}` in the strict transform
`W^{(i+1)}` of `W^{(i)}`", i.e. `f̃⁻¹(F^{(i)}) = red(W^{(i+1)} ∩ f⁻¹(F^{(i)}))`. -/
def IterationStage.next (s : IterationStage.{u}) (t : MonoidalTransformation s.X s.F) :
    IterationStage.{u} where
  X := t.X'
  W := Subscheme.strictTransform t s.W
  E := Subscheme.strictTransform t s.E
  F := Subscheme.inducedPreimage t s.W s.F

/-- "Let `{f^{(i)} : X^{(i+1)} → X^{(i)}}` be any sequence of monoidal transformations with
center `F^{(i)}` in `X^{(i)}`" (p. 288). -/
def IterationStage.IsIteration (g : ℕ → IterationStage.{u}) : Prop :=
  ∀ i, ∃ t : MonoidalTransformation (g i).X (g i).F, g (i + 1) = (g i).next t

section PrepInterPoints

open IsLocalRing

variable {X : Scheme.{u}}

/-- The points of an intersection `D ∩ D'` (sum of the ideal sheaves) are the common points: in
a local ring a sum of proper ideals is proper. -/
theorem Subscheme.mem_pts_inter_iff {D D' : Subscheme X} {x : X} :
    x ∈ (D.inter D').pts ↔ x ∈ D.pts ∧ x ∈ D'.pts := by
  simp only [Subscheme.mem_pts_iff_stalkIdeal_ne_top]
  show (D ⊔ D').stalkIdeal x ≠ ⊤ ↔ _
  rw [Subscheme.stalkIdeal_sup_eq]
  constructor
  · intro h
    exact ⟨fun h1 => h (by rw [h1, top_sup_eq]), fun h1 => h (by rw [h1, sup_top_eq])⟩
  · rintro ⟨h1, h2⟩ h
    have := sup_le (Subscheme.stalkIdeal_le_maximalIdeal D
      (Subscheme.mem_pts_iff_stalkIdeal_ne_top.mpr h1))
      (Subscheme.stalkIdeal_le_maximalIdeal D'
      (Subscheme.mem_pts_iff_stalkIdeal_ne_top.mpr h2))
    rw [h, top_le_iff] at this
    exact (maximalIdeal.isMaximal _).ne_top this

/-- The points of `f̃⁻¹(D) = red(W' ∩ f⁻¹(D))`. -/
theorem Subscheme.pts_inducedPreimage {B : Subscheme X} (t : MonoidalTransformation X B)
    (W D : Subscheme X) :
    (Subscheme.inducedPreimage t W D).pts =
      (Subscheme.strictTransform t W).pts ∩ t.f.base ⁻¹' D.pts := by
  unfold Subscheme.inducedPreimage Subscheme.pts
  rw [Subscheme.ofClosed, Scheme.IdealSheafData.coe_support_vanishingIdeal,
    TopologicalSpace.Closeds.coe_inf]
  rw [show ((Subscheme.totalTransform t.f D).support : Set t.X') = t.f.base ⁻¹' D.pts from
    FlatPreimm.pts_totalTransform t.f D]
  rfl

/-- A reduced structure on a finite union of closed sets is the union of the reduced
structures. -/
theorem Subscheme.ofClosed_support_eq_unionFam {ι : Type v} [Fintype ι] (D : Subscheme X)
    (Z : ι → TopologicalSpace.Closeds X) (h : (D.support : Set X) = ⋃ i, (Z i : Set X)) :
    Subscheme.ofClosed D.support = Subscheme.unionFam (fun i => Subscheme.ofClosed (Z i)) := by
  have hsup : D.support = ⨆ i, Z i := by
    apply SetLike.coe_injective
    rw [h, ← Finset.sup_univ_eq_iSup, TopologicalSpace.Closeds.coe_finset_sup]
    simp
  rw [hsup, Subscheme.ofClosed, Scheme.IdealSheafData.vanishingIdeal_iSup]
  rfl

end PrepInterPoints

section PrepRedInter

open IsLocalRing

variable {X : Scheme.{u}}

/-- Every point of `W' ∩ E'` lies on some `f̃⁻¹(F_j)`: it lies over a point of `W ∩ E`, which
lies on an irreducible component `F_j` of `W ∩ E`. -/
theorem MonoidalTransformation.exists_mem_pts_inducedPreimage_of_mem_pts_inter
    {B : Subscheme X} (t : MonoidalTransformation X B) (W E : Subscheme X) {ι : Type v}
    (Fc : ι → Subscheme X) (hcover : ∀ C ∈ (W.inter E).irreducibleComponents, ∃ j, Fc j = C)
    {z : t.X'} (hz : z ∈ ((Subscheme.strictTransform t W).inter
      (Subscheme.strictTransform t E)).pts) :
    ∃ j, z ∈ (Subscheme.inducedPreimage t W (Fc j)).pts := by
  obtain ⟨hzW, hzE⟩ := Subscheme.mem_pts_inter_iff.mp hz
  have hx : t.f z ∈ (W.inter E).pts := Subscheme.mem_pts_inter_iff.mpr
    ⟨MonoidalTransformation.pts_strictTransform_subset t W hzW,
      MonoidalTransformation.pts_strictTransform_subset t E hzE⟩
  have hne := Subscheme.mem_pts_iff_stalkIdeal_ne_top.mp hx
  obtain ⟨q, hq, -⟩ := Ideal.exists_minimalPrimes_le
    (Subscheme.stalkIdeal_le_maximalIdeal _ hx)
  obtain ⟨C, hC, hxC, -⟩ :=
    Subscheme.exists_mem_irreducibleComponents_of_mem_minimalPrimes (W.inter E) (t.f z) hq
  obtain ⟨j, rfl⟩ := hcover C hC
  exact ⟨j, by rw [Subscheme.pts_inducedPreimage]; exact ⟨hzW, hxC⟩⟩

end PrepRedInter

section PrepRedInterSupset

open IsLocalRing

variable {X : Scheme.{u}}

/-- A component `F_j ≠ F` of `W ∩ E` is not contained in `F`. -/
theorem Subscheme.not_pts_subset_of_mem_irreducibleComponents_of_ne {D F Fj : Subscheme X}
    (hF : F ∈ D.irreducibleComponents) (hFj : Fj ∈ D.irreducibleComponents) (hne : Fj ≠ F) :
    ¬ Fj.pts ⊆ F.pts := by
  intro hsub
  obtain ⟨Z0, hZ0, rfl⟩ := hF
  obtain ⟨Zj, hZj, rfl⟩ := hFj
  have hpts : ∀ Z : Closeds X, (Subscheme.ofClosed Z).pts = Z := fun Z =>
    Scheme.IdealSheafData.coe_support_vanishingIdeal Z
  rw [hpts, hpts] at hsub
  have : Zj = Z0 := le_antisymm hsub (hZj.2 hZ0.1 hsub)
  exact hne (by rw [this])

/-- Points of `W'` lying over a component `F_j ≠ F` of `W ∩ E` lie on `E'` (second step of the
description of `red(W' ∩ E')`): over `F_j − F`, `f` is a local isomorphism and `E' = E`, and the
points over `F_j ∩ F` are limits of those, `F_j` being irreducible. -/
theorem MonoidalTransformation.mem_pts_strictTransform_of_mem_pts_inducedPreimage
    (hXns : X.IsNonsingular) {F : Subscheme X} (t : MonoidalTransformation X F)
    (W E Fj : Subscheme X) (e : (Subscheme.strictTransform t W).toScheme ≅ W.toScheme)
    (he : e.hom ≫ W.ι = (Subscheme.strictTransform t W).ι ≫ t.f)
    (hFj : Fj ∈ (W.inter E).irreducibleComponents) (hFjF : ¬ Fj.pts ⊆ F.pts)
    {z : t.X'} (hz : z ∈ (Subscheme.inducedPreimage t W Fj).pts) :
    z ∈ (Subscheme.strictTransform t E).pts := by
  obtain ⟨g, hgc, hgf, hgW, hgsurj⟩ := t.exists_map_of_iso W e he
  rw [Subscheme.pts_inducedPreimage] at hz
  obtain ⟨hzW, hzP⟩ := hz
  obtain ⟨w₀, rfl⟩ := hgsurj z hzW
  -- the component `F_j`
  obtain ⟨Zj, hZj, hFjeq⟩ := hFj
  have hP : Fj.pts = Zj := by
    rw [hFjeq]; exact Scheme.IdealSheafData.coe_support_vanishingIdeal Zj
  have hPirr : IsIrreducible (Zj : Set X) := hZj.1.1
  have hPsub : (Zj : Set X) ⊆ (W.inter E).pts := hZj.1.2
  have hPW : (Zj : Set X) ⊆ W.pts := fun u hu => (Subscheme.mem_pts_inter_iff.mp (hPsub hu)).1
  have hPE : (Zj : Set X) ⊆ E.pts := fun u hu => (Subscheme.mem_pts_inter_iff.mp (hPsub hu)).2
  rw [hP] at hFjF hzP
  -- the closed set `g⁻¹(E')` of `W`
  set C : Set W.toScheme := g ⁻¹' (Subscheme.strictTransform t E).pts with hC
  have hCcl : IsClosed C := (Subscheme.strictTransform t E).support.isClosed.preimage hgc
  -- points of `W` over `F_j − F` lie in `C`
  have hA' : ∀ w : W.toScheme, W.ι w ∈ Zj → W.ι w ∉ F.pts → w ∈ C := by
    intro w hwP hwF
    have hnot : t.f (g w) ∉ F.pts := by rw [hgf]; exact hwF
    obtain ⟨e', -, hst⟩ := DatumTransform.exists_offCenter hXns t (g w) hnot
    have hEpts : t.f (g w) ∈ E.pts := by rw [hgf]; exact hPE hwP
    have hI := Subscheme.mem_pts_iff_stalkIdeal_ne_top.mp hEpts
    rw [hC, Set.mem_preimage, Subscheme.mem_pts_iff_stalkIdeal_ne_top, hst]
    intro htop
    apply hI
    have h2 := Ideal.comap_map_of_bijective (f := e'.toRingHom) (by exact e'.bijective)
      (I := E.stalkIdeal (t.f (g w)))
    have h3 : Ideal.map e'.toRingHom (E.stalkIdeal (t.f (g w))) = ⊤ := htop
    rw [h3, Ideal.comap_top] at h2
    exact h2.symm
  have hmain : ∀ w : W.toScheme, W.ι w ∈ Zj → w ∈ C := by
    intro w hw
    by_contra hwC
    have hopen : IsOpen Cᶜ := hCcl.isOpen_compl
    obtain ⟨N, hNo, hN⟩ := (W.ι.isClosedEmbedding.isInducing.isOpen_iff).mp hopen
    have hwN : W.ι w ∈ N := by
      have : w ∈ Cᶜ := hwC
      rw [← hN] at this; exact this
    obtain ⟨u, huP, huF⟩ := Set.not_subset.mp hFjF
    obtain ⟨v, hvZ, hvN, hvF⟩ := hPirr.2 N (F.pts)ᶜ hNo F.support.isClosed.isOpen_compl
      ⟨W.ι w, hw, hwN⟩ ⟨u, huP, huF⟩
    obtain ⟨w', rfl⟩ : v ∈ Set.range W.ι := by
      rw [Scheme.IdealSheafData.range_subschemeι]; exact hPW hvZ
    exact (show w' ∈ Cᶜ by rw [← hN]; exact hvN) (hA' w' hvZ hvF)
  exact hmain w₀ (by rw [← hgf w₀]; exact hzP)

end PrepRedInterSupset

section PrepRedInterSubset

open IsLocalRing

variable {X : Scheme.{u}}

/-- The ideal of a non-singular irreducible subscheme of codimension one of a non-singular scheme
is principal at each of its points (height one, regular quotient). -/
theorem Subscheme.exists_stalkIdeal_eq_span_of_isNonsingularIrreducibleCodimOne
    (hX : X.IsNonsingular) {E : Subscheme X} (hE : E.IsNonsingularIrreducibleCodimOne) {x : X}
    (hx : x ∈ E.pts) : ∃ e, E.stalkIdeal x = Ideal.span {e} := by
  have : IsRegularLocalRing (X.presheaf.stalk x) := hX x
  obtain ⟨hEns, hEirr, hEcod⟩ := hE.resolve_left fun hEe => by
    rw [hEe] at hx
    exact absurd hx (by rw [DatumTransform.pts_empty]; exact id)
  obtain ⟨hEp, hEreg⟩ := isPrime_and_isRegularLocalRing_quotient_of_isNonsingular E hEns hx
  have hE1 : (E.stalkIdeal x).height = 1 := by
    rw [← Subscheme.codim_eq_height _ hEns hEirr hx, hEcod]
  obtain ⟨e, hee, -⟩ := exists_span_singleton_of_height_le_one (E.stalkIdeal x) hEreg
    (fun h => by rw [h, Ideal.height_bot] at hE1; exact absurd hE1 (by simp)) hE1.le
  exact ⟨e, hee⟩

end PrepRedInterSubset

section PrepIsoWrapper

variable {X : Scheme.{u}}

/-- The points of a component `F` of `W ∩ E` lie on `W` and on `E`. -/
theorem Subscheme.pts_subset_and_pts_subset_of_mem_irreducibleComponents_inter {W E F : Subscheme X}
    (hF : F ∈ (W.inter E).irreducibleComponents) : F.pts ⊆ W.pts ∧ F.pts ⊆ E.pts := by
  obtain ⟨Z0, hZ0, hFeq⟩ := hF
  have hFpts : F.pts = Z0 := by
    rw [hFeq]; exact Scheme.IdealSheafData.coe_support_vanishingIdeal Z0
  have hFWE : F.pts ⊆ (W.inter E).pts := by rw [hFpts]; exact hZ0.1.2
  exact ⟨fun u hu => ((Subscheme.mem_pts_inter_iff (D := W) (D' := E)).mp (hFWE hu)).1,
    fun u hu => ((Subscheme.mem_pts_inter_iff (D := W) (D' := E)).mp (hFWE hu)).2⟩

/-- First assertion of Lemma 5 (p. 287): "Then `f` induces an isomorphism `f̃` of `W'` to `W`."
Version of `Subscheme.exists_iso_strictTransform_of_exists_stalkIdeal_eq_span` for `E` non-singular
irreducible of codimension one.

Deviation from the paper (gap filled): see
`Subscheme.exists_iso_strictTransform_of_exists_stalkIdeal_eq_span`. -/
theorem Subscheme.exists_iso_strictTransform_of_mem_irreducibleComponents [Hironaka.Cited.MonoidalTransformationExistsIsProper.{u}]
    {X : Scheme.{u}} (hXalg : IsAlgebraicScheme X) (hXns : X.IsNonsingular)
    (W : Subscheme X) (hWns : W.IsNonsingular) (hWirr : W.IsIrreducible) (E : Subscheme X)
    (hE : E.IsNonsingularIrreducibleCodimOne) (hEW : ¬ W.IsContainedIn E) (F : Subscheme X)
    (hF : F ∈ (W.inter E).irreducibleComponents) (hFns : F.IsNonsingular)
    (t : MonoidalTransformation X F) :
    ∃ e : (Subscheme.strictTransform t W).toScheme ≅ W.toScheme,
      e.hom ≫ W.ι = (Subscheme.strictTransform t W).ι ≫ t.f :=
  Subscheme.exists_iso_strictTransform_of_exists_stalkIdeal_eq_span hXalg hXns W hWns hWirr E F
    (fun _ hx => Subscheme.exists_stalkIdeal_eq_span_of_isNonsingularIrreducibleCodimOne hXns hE
      ((Subscheme.pts_subset_and_pts_subset_of_mem_irreducibleComponents_inter hF).2 hx))
    hEW hF hFns t

end PrepIsoWrapper

section PrepRedInterBranch

open IsLocalRing

variable {X : Scheme.{u}}

end PrepRedInterBranch

section PrepFiberNonsingular

open IsLocalRing

variable {X : Scheme.{u}}

/-- At a point `z` of `W' ∩ f⁻¹(F)`, the ideal of `W' ∩ E_exc` (with `E_exc = f⁻¹(F)` the
exceptional subscheme) is generated by a part of a regular system of parameters of `O_{X',z}`:
by the chart `R' = R[P/z_t]`, `W'_z = (z'_s)` for a part `(z_s)` of a regular system of
parameters of `R = O_{X,f(z)}` adapted to `W_x ⊆ F_x`, and `E_exc,z = (z'_t)`. -/
theorem MonoidalTransformation.exists_extendsToRSOP_stalkIdeal_strictTransform_sup_exceptional
    (hXns : X.IsNonsingular) {F : Subscheme X} (hFns : F.IsNonsingular)
    (t : MonoidalTransformation X F) (W : Subscheme X) (hWns : W.IsNonsingular)
    (hFW : F.IsContainedIn W) {z : t.X'} (hzW : z ∈ (Subscheme.strictTransform t W).pts)
    (hzF : t.f z ∈ F.pts) :
    ∃ K : Finset (t.X'.presheaf.stalk z), ExtendsToRSOP _ K ∧
      ((Subscheme.strictTransform t W) ⊔ t.exceptional).stalkIdeal z =
        Ideal.span (K : Set (t.X'.presheaf.stalk z)) := by
  classical
  have hX' := (t.isNonsingular_and_isNonsingular_exceptional hXns hFns).1
  have : IsRegularLocalRing (t.X'.presheaf.stalk z) := hX' z
  have : IsRegularLocalRing (X.presheaf.stalk (t.f z)) := hXns _
  have hxW : t.f z ∈ W.pts := MonoidalTransformation.pts_strictTransform_subset t W hzW
  obtain ⟨hWp, hWreg⟩ := isPrime_and_isRegularLocalRing_quotient_of_isNonsingular W hWns hxW
  obtain ⟨hFp, hFreg⟩ := isPrime_and_isRegularLocalRing_quotient_of_isNonsingular F hFns hzF
  have hWF : W.stalkIdeal (t.f z) ≤ F.stalkIdeal (t.f z) :=
    Subscheme.stalkIdeal_mono (fun U => hFW U) _
  obtain ⟨zW, tW, hzWspan, hzWcard, htWzW, hWt⟩ :=
    exists_finset_span_eq_prime _ (W.stalkIdeal (t.f z)) hWreg
  obtain ⟨zF, tF, hzFspan, hzFcard, htFzF, hFt⟩ :=
    exists_finset_span_eq_prime _ (F.stalkIdeal (t.f z)) hFreg
  have hzWr : IsRegularSystemOfParameters _ zW :=
    ⟨hzWspan, by rw [hzWcard]; exact IsRegularLocalRing.spanFinrank_maximalIdeal⟩
  have hzFr : IsRegularSystemOfParameters _ zF :=
    ⟨hzFspan, by rw [hzFcard]; exact IsRegularLocalRing.spanFinrank_maximalIdeal⟩
  obtain ⟨Z, hZ, -, tP, htPZ, hPt, tQ, htQ, hQt⟩ :=
    exists_rsop_adapted_to_flag (W.stalkIdeal (t.f z)) (F.stalkIdeal (t.f z)) hWF zF tF zW tW ∅
      hzFr htFzF hFt.symm hzWr htWzW hWt.symm (Finset.empty_subset _) (by simp)
  obtain ⟨zt, φ, hzt, hexc, hztm, -, hrel, hinj, hext, hstP, hstS⟩ :=
    MonoidalTransformation.exists_chart_strictTransform_stalkIdeal hXns t z hZ htPZ hPt
  have h1 := hstS tQ htQ W hQt
  have hne : (Subscheme.strictTransform t W).stalkIdeal z ≠ ⊤ :=
    Subscheme.mem_pts_iff_stalkIdeal_ne_top.mp hzW
  rw [h1] at hne
  have hztQ : zt ∉ tQ := fun h => hne (by simp [h])
  simp only [hztQ, ↓reduceIte] at h1 hne
  have hnu : ∀ q ∈ tQ, φ q ∈ maximalIdeal (t.X'.presheaf.stalk z) := by
    intro q hq; by_contra h
    exact hne (Ideal.eq_top_of_isUnit_mem _ (Ideal.subset_span ⟨q, hq, rfl⟩)
      ((IsLocalRing.mem_maximalIdeal _).not.mp h |> not_not.mp))
  refine ⟨insert (φ zt) (tQ.image φ), hext.mono ?_, ?_⟩
  · intro a ha
    rcases Finset.mem_insert.mp ha with rfl | ha
    · exact Finset.mem_image_of_mem φ (Finset.mem_filter.mpr ⟨htPZ hzt, hztm⟩)
    · obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp ha
      exact Finset.mem_image_of_mem φ (Finset.mem_filter.mpr ⟨htPZ (htQ hq), hnu q hq⟩)
  · show (Subscheme.strictTransform t W ⊔ t.exceptional).stalkIdeal z = _
    rw [Subscheme.stalkIdeal_sup_eq, h1, hexc, Finset.coe_insert, Ideal.span_insert,
      Finset.coe_image, sup_comm]

/-- The preimage `f̃⁻¹(F) = red(W' ∩ f⁻¹(F))` is the scheme-theoretic intersection of `W'` with the
exceptional subscheme `f⁻¹(F)`: the latter is already reduced, its stalks being generated by
parts of regular systems of parameters (primes). -/
theorem MonoidalTransformation.inducedPreimage_eq_strictTransform_sup_exceptional
    (hXns : X.IsNonsingular) {F : Subscheme X} (hFns : F.IsNonsingular)
    (t : MonoidalTransformation X F) (W : Subscheme X) (hWns : W.IsNonsingular)
    (hFW : F.IsContainedIn W) :
    Subscheme.inducedPreimage t W F = Subscheme.strictTransform t W ⊔ t.exceptional := by
  classical
  have hX' := (t.isNonsingular_and_isNonsingular_exceptional hXns hFns).1
  have hrad : ∀ z, ((Subscheme.strictTransform t W ⊔ t.exceptional).stalkIdeal z).IsRadical := by
    intro z
    by_cases hz : z ∈ (Subscheme.strictTransform t W ⊔ t.exceptional).pts
    · have hz' := (Subscheme.mem_pts_inter_iff (D := Subscheme.strictTransform t W)
        (D' := t.exceptional)).mp hz
      have hzF : t.f z ∈ F.pts := by
        have := hz'.2
        rwa [MonoidalTransformation.pts_exceptional] at this
      have : IsRegularLocalRing (t.X'.presheaf.stalk z) := hX' z
      obtain ⟨K, hK, hspan⟩ := t.exists_extendsToRSOP_stalkIdeal_strictTransform_sup_exceptional
        hXns hFns W hWns hFW hz'.1 hzF
      rw [hspan]
      exact hK.isPrime_span.isRadical
    · rw [Subscheme.stalkIdeal_eq_top_of_notMem_pts hz]
      intro x _
      exact Submodule.mem_top
  have hred : (Subscheme.strictTransform t W ⊔ t.exceptional).IsReduced :=
    Subscheme.isReduced_of_isRadical_stalkIdeal hrad
  calc Subscheme.inducedPreimage t W F
      = Subscheme.ofClosed ((Subscheme.strictTransform t W).support ⊓ t.exceptional.support) :=
        rfl
    _ = Subscheme.ofClosed (Subscheme.strictTransform t W ⊔ t.exceptional).support := by
        rw [Scheme.IdealSheafData.support_sup]
    _ = Subscheme.strictTransform t W ⊔ t.exceptional :=
        (Subscheme.eq_ofClosed_support _ hred).symm

/-- `f̃⁻¹(F)` is non-singular: it is `W' ∩ f⁻¹(F)`, whose local rings are `R'/(K)` with `K` part of
a regular system of parameters of `R'`. -/
theorem MonoidalTransformation.isNonsingular_inducedPreimage
    (hXns : X.IsNonsingular) {F : Subscheme X} (hFns : F.IsNonsingular)
    (t : MonoidalTransformation X F) (W : Subscheme X) (hWns : W.IsNonsingular)
    (hFW : F.IsContainedIn W) : (Subscheme.inducedPreimage t W F).IsNonsingular := by
  classical
  have hX' := (t.isNonsingular_and_isNonsingular_exceptional hXns hFns).1
  rw [t.inducedPreimage_eq_strictTransform_sup_exceptional hXns hFns W hWns hFW]
  intro u
  have hz : (Subscheme.strictTransform t W ⊔ t.exceptional).ι u ∈
      (Subscheme.strictTransform t W ⊔ t.exceptional).pts := by
    have : (Subscheme.strictTransform t W ⊔ t.exceptional).ι u ∈
        Set.range (Subscheme.strictTransform t W ⊔ t.exceptional).ι := ⟨u, rfl⟩
    rwa [Scheme.IdealSheafData.range_subschemeι] at this
  have hz' := (Subscheme.mem_pts_inter_iff (D := Subscheme.strictTransform t W)
    (D' := t.exceptional)).mp hz
  have hzF : t.f ((Subscheme.strictTransform t W ⊔ t.exceptional).ι u) ∈ F.pts := by
    have := hz'.2
    rwa [MonoidalTransformation.pts_exceptional] at this
  have : IsRegularLocalRing (t.X'.presheaf.stalk
      ((Subscheme.strictTransform t W ⊔ t.exceptional).ι u)) := hX' _
  obtain ⟨K, hK, hspan⟩ := t.exists_extendsToRSOP_stalkIdeal_strictTransform_sup_exceptional
    hXns hFns W hWns hFW hz'.1 hzF
  obtain ⟨e⟩ := nonempty_stalk_quot_equiv (Subscheme.strictTransform t W ⊔ t.exceptional) u
  have hreg := hK.isRegularLocalRing_quotient
  rw [← hspan] at hreg
  exact IsRegularLocalRing.of_ringEquiv e

end PrepFiberNonsingular

section PrepInducedPreimage

variable {X : Scheme.{u}}

/-- `f̃⁻¹(D)` is irreducible for an irreducible `D ⊆ W`. -/
theorem MonoidalTransformation.isIrreducible_pts_inducedPreimage
    {F : Subscheme X} (t : MonoidalTransformation X F) (W D : Subscheme X)
    (hFW : D.pts ⊆ W.pts) (hFirr : _root_.IsIrreducible D.pts)
    (e : (Subscheme.strictTransform t W).toScheme ≅ W.toScheme)
    (he : e.hom ≫ W.ι = (Subscheme.strictTransform t W).ι ≫ t.f) :
    _root_.IsIrreducible (Subscheme.inducedPreimage t W D).pts := by
  obtain ⟨g, hgc, hgf, hgW, hgsurj⟩ := t.exists_map_of_iso W e he
  have hY0eq : (Subscheme.inducedPreimage t W D).pts =
      g '' (W.ι ⁻¹' D.pts) := by
    rw [Subscheme.pts_inducedPreimage]
    ext z
    constructor
    · rintro ⟨hz, hzF⟩
      obtain ⟨w, rfl⟩ := hgsurj z hz
      exact ⟨w, by rw [Set.mem_preimage, ← hgf]; exact hzF, rfl⟩
    · rintro ⟨w, hw, rfl⟩
      exact ⟨hgW w, by rw [Set.mem_preimage, hgf]; exact hw⟩
  have hpre : _root_.IsIrreducible (W.ι ⁻¹' D.pts) := by
    refine isIrreducible_preimage_of_isInducing W.ι.isClosedEmbedding.isInducing hFirr ?_
    intro u hu
    rw [Scheme.IdealSheafData.range_subschemeι]
    exact hFW hu
  rw [hY0eq]; exact hpre.image g hgc.continuousOn

/-- `f̃⁻¹(F)` is irreducible, and `f` maps it onto `F`. -/
theorem MonoidalTransformation.isIrreducible_pts_inducedPreimage_and_subset_image
    {F : Subscheme X} (t : MonoidalTransformation X F) (W : Subscheme X)
    (hFW : F.pts ⊆ W.pts) (hFirr : _root_.IsIrreducible F.pts)
    (e : (Subscheme.strictTransform t W).toScheme ≅ W.toScheme)
    (he : e.hom ≫ W.ι = (Subscheme.strictTransform t W).ι ≫ t.f) :
    _root_.IsIrreducible (Subscheme.inducedPreimage t W F).pts ∧
      F.pts ⊆ t.f.base '' (Subscheme.inducedPreimage t W F).pts := by
  obtain ⟨g, hgc, hgf, hgW, hgsurj⟩ := t.exists_map_of_iso W e he
  have hY0eq : (Subscheme.inducedPreimage t W F).pts =
      g '' (W.ι ⁻¹' F.pts) := by
    rw [Subscheme.pts_inducedPreimage]
    ext z
    constructor
    · rintro ⟨hz, hzF⟩
      obtain ⟨w, rfl⟩ := hgsurj z hz
      exact ⟨w, by rw [Set.mem_preimage, ← hgf]; exact hzF, rfl⟩
    · rintro ⟨w, hw, rfl⟩
      exact ⟨hgW w, by rw [Set.mem_preimage, hgf]; exact hw⟩
  refine ⟨t.isIrreducible_pts_inducedPreimage W F hFW hFirr e he, fun u hu => ?_⟩
  obtain ⟨w, rfl⟩ : u ∈ Set.range W.ι := by
    rw [Scheme.IdealSheafData.range_subschemeι]; exact hFW hu
  rw [hY0eq]
  exact ⟨g w, ⟨w, hu, rfl⟩, hgf w⟩

/-- If `f̃⁻¹(F) ⊆ W' ∩ E'` and `F` is a component of `W ∩ E`, then `f̃⁻¹(F)` is a component of
`W' ∩ E'`: an irreducible closed `Z' ⊇ f̃⁻¹(F)` inside `W' ∩ E'` maps into the irreducible closed
subset `closure f(Z')` of `W ∩ E` containing `F`, hence into `F`. -/
theorem MonoidalTransformation.inducedPreimage_mem_irreducibleComponents
    {F : Subscheme X} (t : MonoidalTransformation X F) (W E : Subscheme X)
    (hF : F ∈ (W.inter E).irreducibleComponents)
    (e : (Subscheme.strictTransform t W).toScheme ≅ W.toScheme)
    (he : e.hom ≫ W.ι = (Subscheme.strictTransform t W).ι ≫ t.f)
    (hsub : (Subscheme.inducedPreimage t W F).pts ⊆
      ((Subscheme.strictTransform t W).inter (Subscheme.strictTransform t E)).pts) :
    Subscheme.inducedPreimage t W F ∈
      ((Subscheme.strictTransform t W).inter (Subscheme.strictTransform t E)).irreducibleComponents := by
  obtain ⟨Z0, hZ0, hFeq⟩ := id hF
  have hFpts : F.pts = Z0 := by
    rw [hFeq]; exact Scheme.IdealSheafData.coe_support_vanishingIdeal Z0
  have hFirr : _root_.IsIrreducible F.pts := by rw [hFpts]; exact hZ0.1.1
  have hFW : F.pts ⊆ W.pts := (Subscheme.pts_subset_and_pts_subset_of_mem_irreducibleComponents_inter
    hF).1
  obtain ⟨hY0irr, hFimg⟩ := t.isIrreducible_pts_inducedPreimage_and_subset_image W hFW hFirr e he
  refine ⟨(Subscheme.strictTransform t W).support ⊓ t.exceptional.support, ?_, rfl⟩
  have hY0pts : (((Subscheme.strictTransform t W).support ⊓ t.exceptional.support :
      TopologicalSpace.Closeds t.X') : Set t.X') = (Subscheme.inducedPreimage t W F).pts :=
    (Scheme.IdealSheafData.coe_support_vanishingIdeal _).symm
  refine ⟨⟨by rw [hY0pts]; exact hY0irr, by rw [hY0pts]; exact hsub⟩, ?_⟩
  intro Z' hZ' hle
  have hle' : (Subscheme.inducedPreimage t W F).pts ⊆ (Z' : Set t.X') := by
    rw [← hY0pts]; exact hle
  intro z hz
  show z ∈ (((Subscheme.strictTransform t W).support ⊓ t.exceptional.support :
      TopologicalSpace.Closeds t.X') : Set t.X')
  rw [hY0pts, Subscheme.pts_inducedPreimage]
  have hzT := hZ'.2 hz
  obtain ⟨hzW', hzE'⟩ := Subscheme.mem_pts_inter_iff.mp hzT
  refine ⟨hzW', ?_⟩
  -- `closure f(Z')` is an irreducible closed subset of `W ∩ E` containing `F`
  have himg : _root_.IsIrreducible (t.f.base '' (Z' : Set t.X')) :=
    hZ'.1.image _ t.f.continuous.continuousOn
  have hsubWE : t.f.base '' (Z' : Set t.X') ⊆ (W.inter E).pts := by
    rintro _ ⟨z', hz', rfl⟩
    obtain ⟨h1, h2⟩ := Subscheme.mem_pts_inter_iff.mp (hZ'.2 hz')
    exact Subscheme.mem_pts_inter_iff.mpr
      ⟨MonoidalTransformation.pts_strictTransform_subset t W h1,
        MonoidalTransformation.pts_strictTransform_subset t E h2⟩
  have hcl : closure (t.f.base '' (Z' : Set t.X')) ⊆ (W.inter E).pts :=
    closure_minimal hsubWE (W.inter E).support.isClosed
  have hZ0le : Z0 ≤ ⟨closure (t.f.base '' (Z' : Set t.X')), isClosed_closure⟩ := by
    intro u hu
    have hu' : u ∈ F.pts := by rw [hFpts]; exact hu
    obtain ⟨y, hy, rfl⟩ := hFimg hu'
    exact subset_closure ⟨y, hle' hy, rfl⟩
  have hmax := hZ0.2 (y := ⟨closure (t.f.base '' (Z' : Set t.X')), isClosed_closure⟩)
    ⟨himg.closure, hcl⟩ hZ0le
  have : t.f.base z ∈ closure (t.f.base '' (Z' : Set t.X')) := subset_closure ⟨z, hz, rfl⟩
  rw [hFpts]
  exact hmax this

end PrepInducedPreimage

section PrepAdmissible

variable {X : Scheme.{u}}

/-- If `W ⊄ E`, then the strict transforms satisfy `W' ⊄ E'` (given the isomorphism `W' ≅ W` over
`W`: `W` is covered by the images of the points of `W'`, which lie over `E` if `W' ⊆ E'`). -/
theorem MonoidalTransformation.not_isContainedIn_strictTransform {F : Subscheme X}
    (t : MonoidalTransformation X F) (W E : Subscheme X) (hWns : W.IsNonsingular)
    (hEW : ¬ W.IsContainedIn E)
    (e : (Subscheme.strictTransform t W).toScheme ≅ W.toScheme)
    (he : e.hom ≫ W.ι = (Subscheme.strictTransform t W).ι ≫ t.f) :
    ¬ (Subscheme.strictTransform t W).IsContainedIn (Subscheme.strictTransform t E) := by
  intro h
  apply hEW
  obtain ⟨g, hgc, hgf, hgW, hgsurj⟩ := t.exists_map_of_iso W e he
  refine isContainedIn_of_pts_subset_of_isReduced_toScheme
    (isReduced_toScheme_of_isNonsingular W hWns) ?_
  intro u hu
  obtain ⟨w, rfl⟩ : u ∈ Set.range W.ι := by
    rw [Scheme.IdealSheafData.range_subschemeι]; exact hu
  rw [← hgf]
  exact MonoidalTransformation.pts_strictTransform_subset t E
    (pts_subset_of_isContainedIn h (hgW w))

/-- The hypotheses of Lemma 5 at one stage of the iteration (the paper applies the lemma again to
`(X', W', E', F')`): `X` is a non-singular algebraic scheme, `W` a non-singular irreducible
subscheme, `F` a non-singular component of `W ∩ E`, `W ⊄ E`, and the ideal of `E` is principal at
the points of `F` (for `E` non-singular of codimension one this holds at each of its points). -/
def IterationStage.IsAdmissible (s : IterationStage.{u}) : Prop :=
  IsAlgebraicScheme s.X ∧ s.X.IsNonsingular ∧ s.W.IsNonsingular ∧ s.W.IsIrreducible ∧
    s.F.IsNonsingular ∧ s.F ∈ (s.W.inter s.E).irreducibleComponents ∧
    ¬ s.W.IsContainedIn s.E ∧ ∀ x ∈ s.F.pts, ∃ e, s.E.stalkIdeal x = Ideal.span {e}

/-- The hypotheses of Lemma 5 are inherited by `(X', W', E', F')` as long as `F' ⊆ W' ∩ E'`
(second assertion of the paper's iteration: "If `F' ⊆ W' ∩ E'`, then we take the monoidal
transformation `f'` with center `F'`"). -/
theorem IterationStage.isAdmissible_next [Hironaka.Cited.MonoidalTransformationExistsIsProper.{u}] (s : IterationStage.{u}) (hs : s.IsAdmissible)
    (t : MonoidalTransformation s.X s.F)
    (hsub : (s.next t).F.IsContainedIn ((s.next t).W.inter (s.next t).E)) :
    (s.next t).IsAdmissible := by
  obtain ⟨hXalg, hXns, hWns, hWirr, hFns, hF, hEW, hEprin⟩ := hs
  obtain ⟨e, he⟩ := Subscheme.exists_iso_strictTransform_of_exists_stalkIdeal_eq_span hXalg hXns
    s.W hWns hWirr s.E s.F hEprin hEW hF hFns t
  obtain ⟨hW'ns, hW'irr⟩ := Subscheme.isNonsingular_and_isIrreducible_of_iso e hWns hWirr
  have hFW : s.F.IsContainedIn s.W := isContainedIn_of_pts_subset_of_isReduced_toScheme
    (isReduced_toScheme_of_isNonsingular s.F hFns)
    (Subscheme.pts_subset_and_pts_subset_of_mem_irreducibleComponents_inter hF).1
  have := hXalg
  refine ⟨t.isAlgebraicScheme, (t.isNonsingular_and_isNonsingular_exceptional hXns hFns).1,
    hW'ns, hW'irr, t.isNonsingular_inducedPreimage hXns hFns s.W hWns hFW,
    t.inducedPreimage_mem_irreducibleComponents s.W s.E hF e he (pts_subset_of_isContainedIn hsub),
    t.not_isContainedIn_strictTransform s.W s.E hWns hEW e he, ?_⟩
  intro x hx
  have hx' : x ∈ (Subscheme.inducedPreimage t s.W s.F).pts := hx
  rw [Subscheme.pts_inducedPreimage] at hx'
  have hzexc : x ∈ t.exceptional.pts := by
    rw [MonoidalTransformation.pts_exceptional]; exact hx'.2
  exact t.exists_stalkIdeal_strictTransform_eq_span hXns hFns hzexc (hEprin _ hx'.2)

end PrepAdmissible

section PrepGenericPoints

open IsLocalRing

variable {X : Scheme.{u}}

/-- A subset of a regular system of parameters which generates the maximal ideal is itself a
regular system of parameters. -/
theorem isRegularSystemOfParameters_of_subset_of_span_eq_maximalIdeal {R : Type u} [CommRing R]
    [IsRegularLocalRing R] {K Z : Finset R} (hZ : IsRegularSystemOfParameters R Z) (hKZ : K ⊆ Z)
    (hspan : Ideal.span (K : Set R) = maximalIdeal R) : IsRegularSystemOfParameters R K :=
  rsop_of_span_of_card_le hspan ((Finset.card_le_card hKZ).trans (rsop_card_eq_spanFinrank hZ).le)

/-- At the generic point `η` of an irreducible reduced subscheme `D`, the stalk of the ideal sheaf
is the maximal ideal. -/
theorem Subscheme.stalkIdeal_eq_maximalIdeal_of_isGenericPoint {D : Subscheme X}
    (hD : D.IsReduced) (hirr : _root_.IsIrreducible D.pts) {η : X}
    (hη : IsGenericPoint η D.pts) :
    D.stalkIdeal η = maximalIdeal (X.presheaf.stalk η) := by
  have hηD : η ∈ D.pts := hη.mem
  obtain ⟨ξ, rfl⟩ : η ∈ Set.range D.ι := by
    rw [Scheme.IdealSheafData.range_subschemeι]; exact hηD
  have hind := D.ι.isClosedEmbedding.isInducing
  have hpre : ∀ u : D.toScheme, D.ι u ∈ D.pts := fun u => by
    have : D.ι u ∈ Set.range D.ι := ⟨u, rfl⟩
    rwa [Scheme.IdealSheafData.range_subschemeι] at this
  have huniv : D.ι ⁻¹' D.pts = Set.univ := Set.eq_univ_of_forall hpre
  have hirrU : _root_.IsIrreducible (Set.univ : Set D.toScheme) := by
    rw [← huniv]
    exact isIrreducible_preimage_of_isInducing hind hirr (by
      intro u hu; rw [Scheme.IdealSheafData.range_subschemeι]; exact hu)
  have : IrreducibleSpace D.toScheme := irreducibleSpace_def _ |>.mpr hirrU
  refine stalkIdeal_eq_maximalIdeal_of_isReduced D hD ξ ?_
  have hcl : closure {ξ} = Set.univ := by
    rw [hind.closure_eq_preimage_closure_image, Set.image_singleton, hη.def, huniv]
  rw [hcl, irreducibleComponents_eq_singleton]
  rfl

/-- The generic point of `f̃⁻¹(F)` lies over the generic point of `F`. -/
theorem MonoidalTransformation.eq_of_isGenericPoint_inducedPreimage {F : Subscheme X}
    (t : MonoidalTransformation X F) (W : Subscheme X) (hFW : F.pts ⊆ W.pts)
    (hFirr : _root_.IsIrreducible F.pts)
    (e : (Subscheme.strictTransform t W).toScheme ≅ W.toScheme)
    (he : e.hom ≫ W.ι = (Subscheme.strictTransform t W).ι ≫ t.f) {η : X} (hη : IsGenericPoint η F.pts)
    {η' : t.X'} (hη' : IsGenericPoint η' (Subscheme.inducedPreimage t W F).pts) :
    t.f η' = η := by
  obtain ⟨-, hFimg⟩ := t.isIrreducible_pts_inducedPreimage_and_subset_image W hFW hFirr e he
  have hη'mem : η' ∈ (Subscheme.inducedPreimage t W F).pts := hη'.mem
  have hfF : t.f η' ∈ F.pts := by
    have := hη'mem
    rw [Subscheme.pts_inducedPreimage] at this
    exact this.2
  have hcl : closure {t.f η'} = F.pts := by
    apply Set.Subset.antisymm
    · exact closure_minimal (Set.singleton_subset_iff.mpr hfF) F.support.isClosed
    · refine hFimg.trans ?_
      rintro _ ⟨u, hu, rfl⟩
      rw [← hη'.def] at hu
      exact image_closure_subset_closure_image t.f.continuous ⟨u, hu, rfl⟩ |> fun h => by
        simpa using h
  exact (hcl ▸ isGenericPoint_closure : IsGenericPoint (t.f η') F.pts).eq hη

end PrepGenericPoints

section PrepRedInterCodim

open IsLocalRing

variable {X : Scheme.{u}}

/-- The ideal of a non-singular irreducible subscheme of codimension one of a non-singular scheme is
principal at *every* point (the unit ideal off the subscheme; at its points
`Subscheme.exists_stalkIdeal_eq_span_of_isNonsingularIrreducibleCodimOne`). -/
theorem Subscheme.forall_exists_stalkIdeal_eq_span_of_isNonsingularIrreducibleCodimOne
    (hX : X.IsNonsingular) {E : Subscheme X} (hE : E.IsNonsingularIrreducibleCodimOne) (x : X) :
    ∃ e, E.stalkIdeal x = Ideal.span {e} := by
  by_cases hx : x ∈ E.pts
  · exact Subscheme.exists_stalkIdeal_eq_span_of_isNonsingularIrreducibleCodimOne hX hE hx
  · exact ⟨1, by rw [Subscheme.stalkIdeal_eq_top_of_notMem_pts hx, Ideal.span_singleton_one]⟩

/-- The ideal of the strict transform `V'` of a subscheme `V` whose ideal is principal at every
point is principal at every point of `X'`: at the points of the exceptional divisor it is the
saturation of a principal ideal by a prime element
(`MonoidalTransformation.exists_stalkIdeal_strictTransform_eq_span`); elsewhere the strict
transform is the total transform, and `f` is a local isomorphism. -/
theorem MonoidalTransformation.forall_exists_stalkIdeal_strictTransform_eq_span
    {B : Subscheme X} (hX : X.IsNonsingular) (hB : B.IsNonsingular)
    (t : MonoidalTransformation X B) {V : Subscheme X}
    (hV : ∀ x, ∃ e, V.stalkIdeal x = Ideal.span {e}) (z : t.X') :
    ∃ ε, (Subscheme.strictTransform t V).stalkIdeal z = Ideal.span {ε} := by
  by_cases hz : z ∈ t.exceptional.pts
  · exact t.exists_stalkIdeal_strictTransform_eq_span hX hB hz (hV _)
  · obtain ⟨e, he⟩ := hV (t.f z)
    refine ⟨(t.f.stalkMap z).hom e, ?_⟩
    rw [MonoidalTransformation.strictTransform_stalkIdeal_of_notMem t V hz, stalkIdeal_totalTransform,
      he, Ideal.map_span, Set.image_singleton]

/-- "`W' ∩ E'` is everywhere of codimension 1 on the non-singular irreducible algebraic scheme `W'`"
(Lemma 5, p. 288), abstract form: let `W'` be a non-singular irreducible subscheme of a scheme `Y`
and `E'` a subscheme whose ideal is principal at every point and which does not contain `W'`.
Then `W' ∩ E'`, as the subscheme `W' ×_Y E'` of the scheme `W'`, is everywhere of codimension 1.

Deviation from the paper (gap filled): the paper asserts the codimension without proof.  At a
point `w` of `W' ∩ E'` the ideal of `W' ∩ E'` in the regular local ring `O_{W',w}` is generated by
the image `ε̄` of a generator `ε` of `E'_w`; `ε̄` is not a unit (`w ∈ E'`) and not zero (else
`E'_w ⊆ W'_w`, so the generic point of `W'` lies on `E'` and `W' ⊆ E'`, as `W'` is reduced), so
the ideal has height `1` by Krull's principal ideal theorem. -/
theorem Subscheme.isEverywhereCodimOne_totalTransform_of_forall_stalkIdeal_eq_span
    {Y : Scheme.{u}} (W' E' : Subscheme Y) (hW'ns : W'.IsNonsingular) (hW'irr : W'.IsIrreducible)
    (hprinc : ∀ z, ∃ ε, E'.stalkIdeal z = Ideal.span {ε}) (hWE : ¬ W'.IsContainedIn E') :
    (Subscheme.totalTransform W'.ι E').IsEverywhereCodimOne := by
  classical
  intro w hw
  obtain ⟨ε, hε⟩ := hprinc (W'.ι w)
  have hT : (Subscheme.totalTransform W'.ι E').stalkIdeal w =
      Ideal.span {(W'.ι.stalkMap w).hom ε} := by
    rw [stalkIdeal_totalTransform, hε, Ideal.map_span, Set.image_singleton]
  have : IsRegularLocalRing (W'.toScheme.presheaf.stalk w) := hW'ns w
  have := isDomain_of_isRegularLocalRing (W'.toScheme.presheaf.stalk w)
  have hne : (Subscheme.totalTransform W'.ι E').stalkIdeal w ≠ ⊤ :=
    Subscheme.mem_pts_iff_stalkIdeal_ne_top.mp hw
  have hnu : ¬ IsUnit ((W'.ι.stalkMap w).hom ε) := fun hu =>
    hne (by rw [hT]; exact Ideal.span_singleton_eq_top.mpr hu)
  have hne0 : (W'.ι.stalkMap w).hom ε ≠ 0 := by
    intro h0
    -- `ε ∈ ker = W'_z`: then `E'_z ≤ W'_z`, so the generic point of `W'` lies on `E'`, `W' ⊆ E'`
    have hker : ε ∈ W'.stalkIdeal (W'.ι w) := by
      rw [stalkIdeal_eq_ker_stalkMap]; exact h0
    have hle : E'.stalkIdeal (W'.ι w) ≤ W'.stalkIdeal (W'.ι w) := by
      rw [hε, Ideal.span_le]; exact Set.singleton_subset_iff.mpr hker
    have hWirr' := Subscheme.isIrreducible_pts W' hW'irr
    have hWcl : IsClosed W'.pts := W'.support.isClosed
    set η := hWirr'.genericPoint with hηdef
    have hηspec : closure {η} = W'.pts := by
      rw [hWirr'.isGenericPoint_genericPoint_closure.def, hWcl.closure_eq]
    have hηW : η ∈ W'.pts := by rw [← hηspec]; exact subset_closure rfl
    have hzW : W'.ι w ∈ W'.pts := by
      have : W'.ι w ∈ Set.range W'.ι := ⟨w, rfl⟩
      rwa [Scheme.IdealSheafData.range_subschemeι] at this
    have hηz : η ⤳ W'.ι w := specializes_iff_mem_closure.mpr (by rw [hηspec]; exact hzW)
    have hηE' : η ∈ E'.pts := mem_pts_of_stalkIdeal_le_of_specializes hηz hηW hle
    have hsub : W'.pts ⊆ E'.pts := by
      rw [← hηspec]
      exact closure_minimal (Set.singleton_subset_iff.mpr hηE') E'.support.isClosed
    exact hWE (isContainedIn_of_pts_subset_of_isReduced_toScheme
      (isReduced_toScheme_of_isNonsingular W' hW'ns) hsub)
  show ((Subscheme.totalTransform W'.ι E').stalkIdeal w).height = ((1 : ℕ) : ℕ∞)
  rw [hT, Nat.cast_one]
  exact Ideal.height_span_singleton_eq_one_of_mem_nonZeroDivisors
    (mem_nonZeroDivisors_of_ne_zero hne0) hnu

/-- Lemma 5, p. 288: "`W' ∩ E'` is everywhere of codimension 1 on the non-singular irreducible
algebraic scheme `W'`" (the first assertion of the proof of the second assertion of the lemma).
The ideal of `E'` is principal at every point (`forall_exists_stalkIdeal_strictTransform_eq_span`)
and `W' ⊄ E'` (`not_isContainedIn_strictTransform`), so the abstract form applies.

Deviation from the paper (gap filled): the paper asserts it without proof; see
`Subscheme.isEverywhereCodimOne_totalTransform_of_forall_stalkIdeal_eq_span`. -/
theorem MonoidalTransformation.isEverywhereCodimOne_totalTransform_strictTransform
    (hXns : X.IsNonsingular) {F : Subscheme X} (hFns : F.IsNonsingular)
    (t : MonoidalTransformation X F) (W : Subscheme X) (hWns : W.IsNonsingular)
    (hWirr : W.IsIrreducible) (E : Subscheme X) (hE : E.IsNonsingularIrreducibleCodimOne)
    (hEW : ¬ W.IsContainedIn E)
    (e : (Subscheme.strictTransform t W).toScheme ≅ W.toScheme)
    (he : e.hom ≫ W.ι = (Subscheme.strictTransform t W).ι ≫ t.f) :
    (Subscheme.totalTransform (Subscheme.strictTransform t W).ι
      (Subscheme.strictTransform t E)).IsEverywhereCodimOne := by
  obtain ⟨hW'ns, hW'irr⟩ := Subscheme.isNonsingular_and_isIrreducible_of_iso e hWns hWirr
  exact Subscheme.isEverywhereCodimOne_totalTransform_of_forall_stalkIdeal_eq_span _ _ hW'ns hW'irr
    (t.forall_exists_stalkIdeal_strictTransform_eq_span hXns hFns
      (Subscheme.forall_exists_stalkIdeal_eq_span_of_isNonsingularIrreducibleCodimOne hXns hE))
    (t.not_isContainedIn_strictTransform W E hWns hEW e he)

/-- Local-ring content of the "Therefore" of Lemma 5 (p. 288): in a scheme `Z`, if `T` is
everywhere of codimension 1 and `ξ` is the generic point of an irreducible component `C` of `T`,
then `dim O_{Z,ξ} = 1`: the maximal ideal is the only minimal prime of `T_ξ`, so its height is
that of `T_ξ`. -/
theorem Subscheme.dimAt_eq_one_of_isEverywhereCodimOne {Z : Scheme.{u}} {T C : Subscheme Z}
    (hT : T.IsEverywhereCodimOne) (hC : C ∈ T.irreducibleComponents)
    {ξ : Z} (hξ : IsGenericPoint ξ C.pts) (hCirr : _root_.IsIrreducible C.pts) :
    Z.dimAt ξ = 1 := by
  have hξC : ξ ∈ C.pts := hξ.mem
  have hCred : C.IsReduced := by
    obtain ⟨Z0, -, rfl⟩ := hC
    exact Subscheme.ofClosed_isReduced Z0
  have hCm : C.stalkIdeal ξ = maximalIdeal (Z.presheaf.stalk ξ) :=
    Subscheme.stalkIdeal_eq_maximalIdeal_of_isGenericPoint hCred hCirr hξ
  have hmin := Subscheme.stalkIdeal_mem_minimalPrimes hC hξC
  rw [hCm] at hmin
  have hξT : ξ ∈ T.pts := by
    obtain ⟨Z0, hZ0, rfl⟩ := hC
    exact hZ0.1.2 hξC
  have h1 : (T.stalkIdeal ξ).height = 1 := by
    have := hT ξ hξT
    rw [Subscheme.codimAt] at this
    exact_mod_cast this
  have hJ : ∀ J ∈ (T.stalkIdeal ξ).minimalPrimes, J = maximalIdeal (Z.presheaf.stalk ξ) :=
    fun J hJ => le_antisymm (IsLocalRing.le_maximalIdeal hJ.1.1.ne_top)
      (hmin.2 hJ.1 (IsLocalRing.le_maximalIdeal hJ.1.1.ne_top))
  have h2 : (T.stalkIdeal ξ).height = (maximalIdeal (Z.presheaf.stalk ξ)).height := by
    rw [Ideal.height_eq_inf_minimalPrimes]
    exact le_antisymm (iInf₂_le _ hmin) (le_iInf₂ fun J hJ' => by rw [hJ J hJ'])
  have h3 := IsLocalRing.maximalIdeal_height_eq_ringKrullDim (R := Z.presheaf.stalk ξ)
  rw [← h2, h1] at h3
  show ringKrullDim (Z.presheaf.stalk ξ) = 1
  rw [← h3]
  rfl

/-- The "Therefore" of Lemma 5 (p. 288): `T = W' ∩ E'` is everywhere of codimension 1 on the
irreducible scheme `Z = W'` and contained in a finite union of proper irreducible closed subsets
`D_i` (the `f̃⁻¹(F_j)`); then every point of `T` lies on some `D_i` which is contained in `T`
("red(`W' ∩ E'`) is a union of some of the `f̃⁻¹(F_j)`").  The irreducible component `C` of `T`
through the point lies in some `D_i`, and cannot be strictly smaller: that would give a chain
`Z ⊋ D_i ⊋ C` of irreducible closed sets, so `dim O_{Z,ξ} ≥ 2` at the generic point `ξ` of `C`,
contradicting `dim O_{Z,ξ} = 1`. -/
theorem Subscheme.exists_mem_subset_pts_of_isEverywhereCodimOne {Z : Scheme.{u}}
    [IrreducibleSpace Z] (T : Subscheme Z) (hT : T.IsEverywhereCodimOne) {ι : Type v} [Fintype ι]
    (D : ι → Set Z) (hDcl : ∀ i, IsClosed (D i)) (hDirr : ∀ i, _root_.IsIrreducible (D i))
    (hDne : ∀ i, D i ≠ Set.univ) (hsub : T.pts ⊆ ⋃ i, D i) :
    ∀ z ∈ T.pts, ∃ i, z ∈ D i ∧ D i ⊆ T.pts := by
  classical
  intro z hz
  obtain ⟨q, hq, -⟩ := Ideal.exists_minimalPrimes_le (Subscheme.stalkIdeal_le_maximalIdeal _ hz)
  obtain ⟨C, hC, hzC, -⟩ := Subscheme.exists_mem_irreducibleComponents_of_mem_minimalPrimes T z hq
  obtain ⟨Zc, hZc, hCeq⟩ := id hC
  have hCpts : C.pts = Zc := by
    rw [hCeq]; exact Scheme.IdealSheafData.coe_support_vanishingIdeal Zc
  -- the component lies in some `D i`
  obtain ⟨s₀, hs₀, hZcs₀⟩ := isIrreducible_iff_sUnion_isClosed.mp hZc.1.1
    (Finset.univ.image D)
    (fun s hs => by obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hs; exact hDcl i)
    (fun u hu => by
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hsub (hZc.1.2 hu))
      exact Set.mem_sUnion.mpr ⟨D i, by simp, hi⟩)
  obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hs₀
  have hDi : D i ⊆ (Zc : Set Z) := by
    by_contra hne
    set ξ := hZc.1.1.genericPoint with hξdef
    have hξspec : closure {ξ} = (Zc : Set Z) := by
      rw [hZc.1.1.isGenericPoint_genericPoint_closure.def, Zc.isClosed.closure_eq]
    have hξgen : IsGenericPoint ξ C.pts := by
      show closure {ξ} = C.pts
      rw [hCpts]; exact hξspec
    have hCirr : _root_.IsIrreducible C.pts := by rw [hCpts]; exact hZc.1.1
    have hdim1 : Z.dimAt ξ = 1 := Subscheme.dimAt_eq_one_of_isEverywhereCodimOne hT hC hξgen hCirr
    have hξD : ξ ∈ D i := hZcs₀ (hξspec ▸ subset_closure rfl)
    set ζ := (hDirr i).genericPoint with hζdef
    have hζspec : closure {ζ} = D i := by
      rw [(hDirr i).isGenericPoint_genericPoint_closure.def, (hDcl i).closure_eq]
    have hζξ : ζ ⤳ ξ := specializes_iff_mem_closure.mpr (by rw [hζspec]; exact hξD)
    have hζne : ζ ≠ ξ := fun h => hne (by rw [← hζspec, h, hξspec])
    have hηζ : genericPoint Z ⤳ ζ :=
      specializes_iff_mem_closure.mpr (by rw [(genericPoint_spec Z).def]; trivial)
    have hηne : genericPoint Z ≠ ζ := fun h =>
      hDne i (by rw [← hζspec, ← h, (genericPoint_spec Z).def])
    have d1 := LocSucc.dimAt_add_one_le_of_specializes hηζ hηne
    have d2 := LocSucc.dimAt_add_one_le_of_specializes hζξ hζne
    have d0 : (0 : WithBot ℕ∞) ≤ Z.dimAt (genericPoint Z) := ringKrullDim_nonneg_of_nontrivial
    rw [hdim1] at d2
    have : (2 : WithBot ℕ∞) ≤ 1 := by
      calc (2 : WithBot ℕ∞) = 0 + 1 + 1 := by norm_num
        _ ≤ Z.dimAt (genericPoint Z) + 1 + 1 := by gcongr
        _ ≤ Z.dimAt ζ + 1 := by gcongr
        _ ≤ 1 := d2
    exact absurd this (by norm_num)
  exact ⟨i, hZcs₀ (hCpts ▸ hzC), hDi.trans hZc.1.2⟩

/-- The points of `W' ∩ E'`, regarded as the subscheme `W' ×_Y E'` of the scheme `W'`: `w` lies on it
iff its image lies on `W' ∩ E'`. -/
theorem Subscheme.mem_pts_totalTransform_ι_iff_mem_pts_inter {Y : Scheme.{u}} (W' E' : Subscheme Y)
    (w : W'.toScheme) :
    w ∈ (Subscheme.totalTransform W'.ι E').pts ↔ W'.ι w ∈ (W'.inter E').pts := by
  rw [Subscheme.mem_pts_iff_stalkIdeal_ne_top, Subscheme.mem_pts_iff_stalkIdeal_ne_top,
    stalkIdeal_totalTransform]
  show _ ≠ ⊤ ↔ (W' ⊔ E').stalkIdeal _ ≠ ⊤
  rw [Subscheme.stalkIdeal_sup_eq, stalkIdeal_eq_ker_stalkMap, Ne, Ne, not_iff_not]
  have hsurj : Function.Surjective (W'.ι.stalkMap w).hom := W'.ι.stalkMap_surjective w
  rw [Ideal.eq_top_iff_one, Ideal.eq_top_iff_one]
  constructor
  · intro h
    obtain ⟨a, ha, ha1⟩ := (Ideal.mem_map_iff_of_surjective _ hsurj).mp h
    refine Submodule.mem_sup.mpr ⟨1 - a, ?_, a, ha, by ring⟩
    show _ ∈ RingHom.ker _
    rw [RingHom.mem_ker, map_sub, ha1, map_one, sub_self]
  · intro h
    obtain ⟨k, hk, a, ha, hka⟩ := Submodule.mem_sup.mp h
    have : (W'.ι.stalkMap w).hom 1 = (W'.ι.stalkMap w).hom a := by
      rw [← hka, map_add, RingHom.mem_ker.mp hk, zero_add]
    rw [map_one] at this
    rw [this]
    exact Ideal.mem_map_of_mem _ ha

end PrepRedInterCodim

section PrepRedInterAssemble

variable {X : Scheme.{u}}

/-- `W' ⊄ f̃⁻¹(F_j)` for a subscheme `F_j ⊆ E` of `W ≅ W'`: otherwise `W = f(W') ⊆ F_j ⊆ E`. -/
theorem MonoidalTransformation.not_pts_subset_inducedPreimage {F : Subscheme X}
    (t : MonoidalTransformation X F) (W E Fj : Subscheme X) (hWns : W.IsNonsingular)
    (hEW : ¬ W.IsContainedIn E) (hFjE : Fj.pts ⊆ E.pts)
    (e : (Subscheme.strictTransform t W).toScheme ≅ W.toScheme)
    (he : e.hom ≫ W.ι = (Subscheme.strictTransform t W).ι ≫ t.f) :
    ¬ (Subscheme.strictTransform t W).pts ⊆ (Subscheme.inducedPreimage t W Fj).pts := by
  intro hW'
  apply hEW
  obtain ⟨g, hgc, hgf, hgW, hgsurj⟩ := t.exists_map_of_iso W e he
  refine isContainedIn_of_pts_subset_of_isReduced_toScheme
    (isReduced_toScheme_of_isNonsingular W hWns) ?_
  intro u hu
  obtain ⟨w, rfl⟩ : u ∈ Set.range W.ι := by
    rw [Scheme.IdealSheafData.range_subschemeι]; exact hu
  have hz := hW' (hgW w)
  rw [Subscheme.pts_inducedPreimage] at hz
  apply hFjE
  rw [← hgf]; exact hz.2

/-- The "Therefore" of Lemma 5 (p. 288), assembled: `W' ∩ E'` is everywhere of codimension 1 on the
irreducible scheme `W'` (`isEverywhereCodimOne_totalTransform_strictTransform`) and
`red(W' ∩ E') ⊆ ⋃_j f̃⁻¹(F_j)` with `f̃⁻¹(F_j)` irreducible, closed and proper in `W'`; so every
point of `W' ∩ E'` lies on some `f̃⁻¹(F_j)` which is contained in `W' ∩ E'`
(`Subscheme.exists_mem_subset_pts_of_isEverywhereCodimOne`). -/
theorem MonoidalTransformation.exists_mem_inducedPreimage_subset_pts_inter
    (hXns : X.IsNonsingular) {F : Subscheme X} (hFns : F.IsNonsingular)
    (t : MonoidalTransformation X F) (W : Subscheme X) (hWns : W.IsNonsingular)
    (hWirr : W.IsIrreducible) (E : Subscheme X) (hE : E.IsNonsingularIrreducibleCodimOne)
    (hEW : ¬ W.IsContainedIn E)
    (e : (Subscheme.strictTransform t W).toScheme ≅ W.toScheme)
    (he : e.hom ≫ W.ι = (Subscheme.strictTransform t W).ι ≫ t.f)
    {ι : Type v} [Fintype ι] (Fc : ι → Subscheme X)
    (hcomp : ∀ j, Fc j ∈ (W.inter E).irreducibleComponents)
    (hsub : ((Subscheme.strictTransform t W).inter (Subscheme.strictTransform t E)).pts ⊆
      ⋃ j, (Subscheme.inducedPreimage t W (Fc j)).pts) :
    ∀ z ∈ ((Subscheme.strictTransform t W).inter (Subscheme.strictTransform t E)).pts,
      ∃ j, z ∈ (Subscheme.inducedPreimage t W (Fc j)).pts ∧
        (Subscheme.inducedPreimage t W (Fc j)).pts ⊆
          ((Subscheme.strictTransform t W).inter (Subscheme.strictTransform t E)).pts := by
  classical
  obtain ⟨hW'ns, hW'irr⟩ := Subscheme.isNonsingular_and_isIrreducible_of_iso e hWns hWirr
  have : IrreducibleSpace (Subscheme.strictTransform t W).toScheme := hW'irr
  have hcodim := MonoidalTransformation.isEverywhereCodimOne_totalTransform_strictTransform hXns
    hFns t W hWns hWirr E hE hEW e he
  have hFj : ∀ j, (Fc j).pts ⊆ W.pts ∧ (Fc j).pts ⊆ E.pts := fun j =>
    Subscheme.pts_subset_and_pts_subset_of_mem_irreducibleComponents_inter (hcomp j)
  have hFjirr : ∀ j, _root_.IsIrreducible (Fc j).pts := fun j => by
    obtain ⟨Z0, hZ0, hFeq⟩ := hcomp j
    have : (Fc j).pts = Z0 := by
      rw [hFeq]; exact Scheme.IdealSheafData.coe_support_vanishingIdeal Z0
    rw [this]; exact hZ0.1.1
  have hrange : ∀ u ∈ (Subscheme.strictTransform t W).pts,
      u ∈ Set.range (Subscheme.strictTransform t W).ι := fun u hu => by
    rw [Scheme.IdealSheafData.range_subschemeι]; exact hu
  let D : ι → Set (Subscheme.strictTransform t W).toScheme := fun j =>
    (Subscheme.strictTransform t W).ι ⁻¹' (Subscheme.inducedPreimage t W (Fc j)).pts
  have hDcl : ∀ j, IsClosed (D j) := fun j =>
    (Subscheme.inducedPreimage t W (Fc j)).support.isClosed.preimage
      (Subscheme.strictTransform t W).ι.continuous
  have hDirr : ∀ j, _root_.IsIrreducible (D j) := fun j =>
    isIrreducible_preimage_of_isInducing
      (Subscheme.strictTransform t W).ι.isClosedEmbedding.isInducing
      (t.isIrreducible_pts_inducedPreimage W (Fc j) (hFj j).1 (hFjirr j) e he)
      (fun u hu => by
        rw [Subscheme.pts_inducedPreimage] at hu
        exact hrange u hu.1)
  have hDne : ∀ j, D j ≠ Set.univ := fun j h =>
    t.not_pts_subset_inducedPreimage W E (Fc j) hWns hEW (hFj j).2 e he (fun u hu => by
      obtain ⟨w, rfl⟩ := hrange u hu
      have : w ∈ D j := h ▸ Set.mem_univ w
      exact this)
  have hTsub : (Subscheme.totalTransform (Subscheme.strictTransform t W).ι
      (Subscheme.strictTransform t E)).pts ⊆ ⋃ j, D j := fun w hw => by
    obtain ⟨j, hj⟩ := Set.mem_iUnion.mp
      (hsub ((Subscheme.mem_pts_totalTransform_ι_iff_mem_pts_inter _ _ w).mp hw))
    exact Set.mem_iUnion.mpr ⟨j, hj⟩
  have key := Subscheme.exists_mem_subset_pts_of_isEverywhereCodimOne _ hcodim D hDcl hDirr hDne
    hTsub
  intro z hz
  obtain ⟨w, rfl⟩ := hrange z (Subscheme.mem_pts_inter_iff.mp hz).1
  obtain ⟨j, hwj, hDj⟩ := key w ((Subscheme.mem_pts_totalTransform_ι_iff_mem_pts_inter _ _ w).mpr hz)
  refine ⟨j, hwj, fun u hu => ?_⟩
  rw [Subscheme.pts_inducedPreimage] at hu
  obtain ⟨w', rfl⟩ := hrange u hu.1
  rw [← Subscheme.pts_inducedPreimage] at hu
  exact (Subscheme.mem_pts_totalTransform_ι_iff_mem_pts_inter _ _ w').mp (hDj hu)

/-- Second assertion of Lemma 5 (p. 287): `red(W' ∩ E')` is either `⋃_{j=2}^m f̃⁻¹(F_j)` or
`⋃_{j=1}^m f̃⁻¹(F_j)` (with the enumeration `F_0 = F, F_1, …, F_m` of the irreducible components
of `W ∩ E`).

Proof as printed (p. 288): "`W' ∩ E'` is everywhere of codimension 1 on the non-singular
irreducible algebraic scheme `W'`" (`isEverywhereCodimOne_totalTransform_strictTransform`), "and
`red(W' ∩ E') ⊆ (⋃_{j=2}^m f̃⁻¹(F_j)) ∪ (W' ∩ f⁻¹(F)) = ⋃_{j=1}^m f̃⁻¹(F_j)`" (`hsub`).
"Therefore either `red(W' ∩ E') = ⋃_{j=2}^m f̃⁻¹(F_j)` or `= ⋃_{j=1}^m f̃⁻¹(F_j)`": by
`exists_mem_inducedPreimage_subset_pts_inter`, `red(W' ∩ E')` is a union of some of the
`f̃⁻¹(F_j)`; the `f̃⁻¹(F_j)` with `j ≥ 2` are all contained in `W' ∩ E'` (`hsup`), so it is
`⋃_{j≥1}` if `f̃⁻¹(F) ⊆ W' ∩ E'` and `⋃_{j≥2}` otherwise.

Gaps in the paper filled: the codimension assertion (Krull's principal ideal theorem; the ideal
of `E'` is principal at every point); the inclusion `⊆ ⋃_{j≥1}` (a point of `W' ∩ E'` lies over a
point of `W ∩ E`, which lies on a component); the inclusion `⊇ ⋃_{j≥2}`, omitted by the paper
(over `F_j − F` the map `f` is a local isomorphism, so `E' = E` there, and `f̃⁻¹(F_j)` is the
closure of the part over `F_j − F` as `F_j` is irreducible and not contained in `F`); and the
deduction of "Therefore" (components of codimension 1, `dim O_{W',ξ} = 1`). -/
theorem MonoidalTransformation.ofClosed_support_inter_eq_unionFam_inducedPreimage_or
    (hXns : X.IsNonsingular) {F : Subscheme X} (hFns : F.IsNonsingular)
    (t : MonoidalTransformation X F) (W : Subscheme X) (hWns : W.IsNonsingular)
    (hWirr : W.IsIrreducible) (E : Subscheme X) (hE : E.IsNonsingularIrreducibleCodimOne)
    (hEW : ¬ W.IsContainedIn E) (hF : F ∈ (W.inter E).irreducibleComponents)
    (e : (Subscheme.strictTransform t W).toScheme ≅ W.toScheme)
    (he : e.hom ≫ W.ι = (Subscheme.strictTransform t W).ι ≫ t.f)
    (m : ℕ) (Fc : Fin (m + 1) → Subscheme X) (h0 : Fc 0 = F) (hinj : Function.Injective Fc)
    (hcomp : ∀ j, Fc j ∈ (W.inter E).irreducibleComponents)
    (hcover : ∀ C ∈ (W.inter E).irreducibleComponents, ∃ j, Fc j = C) :
    Subscheme.ofClosed ((Subscheme.strictTransform t W).inter
        (Subscheme.strictTransform t E)).support =
      Subscheme.unionFam (fun j : Fin m => Subscheme.inducedPreimage t W (Fc j.succ)) ∨
    Subscheme.ofClosed ((Subscheme.strictTransform t W).inter
        (Subscheme.strictTransform t E)).support =
      Subscheme.unionFam (fun j : Fin (m + 1) => Subscheme.inducedPreimage t W (Fc j)) := by
  classical
  -- (i)
  have hsub : ((Subscheme.strictTransform t W).inter (Subscheme.strictTransform t E)).pts ⊆
      ⋃ j, (Subscheme.inducedPreimage t W (Fc j)).pts := fun z hz => by
    obtain ⟨j, hj⟩ :=
      t.exists_mem_pts_inducedPreimage_of_mem_pts_inter W E Fc hcover hz
    exact Set.mem_iUnion.mpr ⟨j, hj⟩
  -- (ii)
  have hsup : ∀ j : Fin (m + 1), j ≠ 0 → (Subscheme.inducedPreimage t W (Fc j)).pts ⊆
      ((Subscheme.strictTransform t W).inter (Subscheme.strictTransform t E)).pts := by
    intro j hj z hz
    have hjF : Fc j ≠ F := fun h => hj (hinj (h.trans h0.symm))
    have hz' := hz
    rw [Subscheme.pts_inducedPreimage] at hz'
    exact Subscheme.mem_pts_inter_iff.mpr ⟨hz'.1,
      t.mem_pts_strictTransform_of_mem_pts_inducedPreimage hXns W E (Fc j) e he (hcomp j)
        (Subscheme.not_pts_subset_of_mem_irreducibleComponents_of_ne hF (hcomp j) hjF) hz⟩
  have hZpts : ∀ D : Subscheme X, ((Subscheme.strictTransform t W).support ⊓
      (Subscheme.totalTransform t.f D).support : TopologicalSpace.Closeds t.X') =
        (Subscheme.inducedPreimage t W D).pts := fun D =>
    (Scheme.IdealSheafData.coe_support_vanishingIdeal _).symm
  by_cases hB0 : (Subscheme.inducedPreimage t W (Fc 0)).pts ⊆
      ((Subscheme.strictTransform t W).inter (Subscheme.strictTransform t E)).pts
  · right
    refine Subscheme.ofClosed_support_eq_unionFam _ (fun j : Fin (m + 1) =>
      (Subscheme.strictTransform t W).support ⊓ (Subscheme.totalTransform t.f (Fc j)).support)
      ?_
    refine Set.Subset.antisymm ?_ ?_
    · intro z hz
      obtain ⟨j, hj⟩ := Set.mem_iUnion.mp (hsub hz)
      exact Set.mem_iUnion.mpr ⟨j, by rw [hZpts]; exact hj⟩
    · intro z hz
      obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hz
      rw [hZpts] at hj
      by_cases hj0 : j = 0
      · subst hj0; exact hB0 hj
      · exact hsup j hj0 hj
  · left
    have hmain : ((Subscheme.strictTransform t W).inter (Subscheme.strictTransform t E)).pts ⊆
        ⋃ j : Fin m, (Subscheme.inducedPreimage t W (Fc j.succ)).pts := by
      intro z hz
      obtain ⟨j, hzj, hjT⟩ := t.exists_mem_inducedPreimage_subset_pts_inter hXns hFns W hWns hWirr
        E hE hEW e he Fc hcomp hsub z hz
      by_cases hj0 : j = 0
      · subst hj0; exact absurd hjT hB0
      · obtain ⟨i, rfl⟩ := Fin.exists_succ_eq.mpr hj0
        exact Set.mem_iUnion.mpr ⟨i, hzj⟩
    refine Subscheme.ofClosed_support_eq_unionFam _ (fun j : Fin m =>
      (Subscheme.strictTransform t W).support ⊓
        (Subscheme.totalTransform t.f (Fc j.succ)).support) ?_
    refine Set.Subset.antisymm ?_ ?_
    · intro z hz
      obtain ⟨j, hj⟩ := Set.mem_iUnion.mp (hmain hz)
      exact Set.mem_iUnion.mpr ⟨j, by rw [hZpts]; exact hj⟩
    · intro z hz
      obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hz
      rw [hZpts] at hj
      exact hsup j.succ (Fin.succ_ne_zero j) hj

end PrepRedInterAssemble

section PrepGeneratesIdeal

open IsLocalRing

/-- A non-zero element of the maximal ideal of a regular local ring which is not in `M²`
extends to a regular system of parameters. -/
theorem extendsToRSOP_singleton_of_notMem_maximalIdeal_sq {A : Type u} [CommRing A]
    [IsRegularLocalRing A] {w : A} (hw : w ∈ maximalIdeal A) (hw2 : w ∉ maximalIdeal A ^ 2) :
    ExtendsToRSOP A {w} := by
  classical
  have hw0 : w ≠ 0 := fun h => hw2 (h ▸ zero_mem _)
  have : IsLocalRing (A ⧸ Ideal.span {w}) :=
    isLocalRing_quotient_of_le ((Ideal.span_singleton_le_iff_mem _).mpr hw)
  have := (quotient_span_singleton_regular hw hw2).1
  obtain ⟨-, W, hW⟩ :=
    (isRegularLocalRing_iff_exists_rsop (A ⧸ Ideal.span {w})).mp this
  have h := rsop_extends_insert_of_quotient hw hw0 (V := ∅)
    (by rw [Finset.image_empty]; exact ⟨W, Finset.empty_subset _, hW⟩) (by simp)
  simpa using h

variable {X : Scheme.{u}} {B : Subscheme X}

open Classical in
/-- The generation step of Lemma 5 (p. 288: "`w^{(i)}` … generates the prime ideal of `E^{(i)}`
in `R_i`"): let `η'` be a point of `X'` over a point at which the ideal of the center `B` is the
maximal ideal, `V` a subscheme whose ideal at `f(η')` is generated by `e ∈ M \ M²` (`V` non-singular
of codimension one there), `(y')` the ideal of the exceptional divisor at `η'` and `w₂ · y' = f^♯ e`
(`w₂ = y⁻¹ e`).  Then the ideal of the strict transform of `V` at `η'` is generated by `w₂` and
`w₂ ∉ M'²` (so the strict transform is again non-singular of codimension one there, which is what
the next step of the induction needs).  Proof: `e` is part of a regular system of parameters `Z`
of `R`; in the chart of `Z` (`exists_chart_strictTransform_stalkIdeal` with `J = {e}`) the ideal
of the strict transform is generated by `φ e = z_t⁻¹ e` (or `1`), which differs from `w₂` by a
unit. -/
theorem MonoidalTransformation.stalkIdeal_strictTransform_eq_span_and_notMem_sq
    (hX : X.IsNonsingular) (hB : B.IsNonsingular) (t : MonoidalTransformation X B) (η' : t.X')
    (hBη : B.stalkIdeal (t.f η') = maximalIdeal (X.presheaf.stalk (t.f η')))
    {V : Subscheme X} {e : X.presheaf.stalk (t.f η')}
    (hV : V.stalkIdeal (t.f η') = Ideal.span {e}) (he : e ∈ maximalIdeal (X.presheaf.stalk (t.f η')))
    (he2 : e ∉ maximalIdeal (X.presheaf.stalk (t.f η')) ^ 2)
    {y' w₂ : t.X'.presheaf.stalk η'} (hy'exc : t.exceptional.stalkIdeal η' = Ideal.span {y'})
    (hy' : y' ∈ nonZeroDivisors (t.X'.presheaf.stalk η'))
    (hw₂ : w₂ * y' = (t.f.stalkMap η').hom e) :
    (Subscheme.strictTransform t V).stalkIdeal η' = Ideal.span {w₂} ∧
      w₂ ∉ maximalIdeal (t.X'.presheaf.stalk η') ^ 2 := by
  have : IsRegularLocalRing (t.X'.presheaf.stalk η') := t.isRegularLocalRing_stalk hX hB η'
  have := isDomain_of_isRegularLocalRing (t.X'.presheaf.stalk η')
  have : IsRegularLocalRing (X.presheaf.stalk (t.f η')) := hX _
  have hy'0 : y' ≠ 0 := nonZeroDivisors.ne_zero hy'
  obtain ⟨Z, heZ, hZ⟩ := extendsToRSOP_singleton_of_notMem_maximalIdeal_sq he he2
  have heZ' : e ∈ Z := heZ (Finset.mem_singleton_self e)
  obtain ⟨zt, φ, hzt, hexc, hztm, hφzt, hrel, hinj, hext, hJ, -⟩ :=
    t.exists_chart_strictTransform_stalkIdeal hX η' hZ (Finset.Subset.refl _)
      (by rw [hBη]; exact hZ.1.symm)
  have hVJ := hJ {e} (Finset.singleton_subset_iff.mpr heZ') V
    (by rw [Finset.prod_singleton]; exact hV)
  obtain ⟨u, hu⟩ := (Ideal.span_singleton_eq_span_singleton.mp (hexc.symm.trans hy'exc))
  -- `y' = φ zt * u`
  have hzt0 : φ zt ≠ 0 := fun h => hy'0 (by rw [← hu, h, zero_mul])
  have hnotsq : ∀ a : t.X'.presheaf.stalk η', IsUnit a → a ∉ maximalIdeal (t.X'.presheaf.stalk η') ^ 2 :=
    fun a ha h => (mem_maximalIdeal _).mp (Ideal.pow_le_self two_ne_zero h) ha
  by_cases hez : e = zt
  · subst hez
    have hunit : IsUnit w₂ := by
      have h1 : w₂ * (φ e * u) = φ e := by rw [hu, hw₂, hφzt]
      have h2 : φ e * (w₂ * u - 1) = 0 := by linear_combination h1
      have h3 : w₂ * u = 1 := by
        have := (mul_eq_zero.mp h2).resolve_left hzt0
        linear_combination this
      exact isUnit_iff_exists_inv.mpr ⟨u, h3⟩
    rw [Finset.erase_singleton, Finset.filter_empty, Finset.prod_empty] at hVJ
    exact ⟨hVJ.trans (by rw [Ideal.span_singleton_one, Ideal.span_singleton_eq_top.mpr hunit]),
      hnotsq _ hunit⟩
  · have h1 := hrel e heZ' hez
    have hwu : w₂ * (u : t.X'.presheaf.stalk η') = φ e := by
      have h2 : φ zt * (w₂ * u - φ e) = 0 := by
        have : w₂ * (φ zt * u) = φ zt * φ e := by rw [hu, hw₂, ← h1]
        linear_combination this
      have := (mul_eq_zero.mp h2).resolve_left hzt0
      linear_combination this
    have hassoc : Ideal.span {w₂} = Ideal.span {φ e} :=
      Ideal.span_singleton_eq_span_singleton.mpr ⟨u, hwu⟩
    have hee : ({e} : Finset _).erase zt = {e} :=
      Finset.erase_eq_of_notMem (by simpa [eq_comm] using hez)
    by_cases hm : φ e ∈ maximalIdeal (t.X'.presheaf.stalk η')
    · rw [hee, Finset.filter_singleton] at hVJ
      simp only [hm, ↓reduceIte, Finset.prod_singleton] at hVJ
      refine ⟨hVJ.trans hassoc.symm, fun h2 => ?_⟩
      have hφe := hext.notMem_maximalIdeal_sq (k := φ e)
        (Finset.mem_image_of_mem φ (Finset.mem_filter.mpr ⟨heZ', hm⟩))
      exact hφe (hwu ▸ Ideal.mul_mem_right _ _ h2)
    · have hφu : IsUnit (φ e) := IsLocalRing.notMem_maximalIdeal.mp hm
      have hunit : IsUnit w₂ := isUnit_of_mul_isUnit_left (hwu ▸ hφu)
      rw [hee, Finset.filter_singleton] at hVJ
      simp only [hm, ↓reduceIte, Finset.prod_empty] at hVJ
      exact ⟨hVJ.trans (by rw [Ideal.span_singleton_one, Ideal.span_singleton_eq_top.mpr hunit]),
        hnotsq _ hunit⟩

/-- The ideal generated by an element of `M \ M²` of a regular local ring is prime (the quotient
is regular, hence a domain).  In Lemma 5 (p. 288) this is the "prime ideal of `E^{(i)}`" of which
`w^{(i)}` is the generator. -/
theorem isPrime_span_singleton_of_mem_maximalIdeal_of_notMem_sq {A : Type u} [CommRing A]
    [IsRegularLocalRing A] {w : A} (hw : w ∈ maximalIdeal A) (hw2 : w ∉ maximalIdeal A ^ 2) :
    (Ideal.span {w}).IsPrime :=
  (extendsToRSOP_singleton_of_notMem_maximalIdeal_sq hw hw2).isPrime_span_singleton
    (Finset.mem_singleton_self w)

end PrepGeneratesIdeal

section PrepLocalChain

open IsLocalRing

open Classical in
/-- The local data carried along the iteration of Lemma 5 at the generic point `η` of `F^{(k)}`
(paper, p. 288): a ring map `ψ : R₀ → R_k`, `y` the image of `y₀`, `z^{(k)}_j = ζ z_j` with
`ψ z_j = yᵏ z^{(k)}_j`, `w^{(k)} = w'` with `ψ w₀ = yᵏ w^{(k)}`, `w^{(k)}` *generating* the ideal of
`E^{(k)}` in `R_k` (the printed claim "`w^{(i)}` … generates the prime ideal of `E^{(i)}` in `R_i`")
and not in `M_k²` (`E^{(k)}` is non-singular of codimension one at `η`, which is what makes the
ideal prime and keeps the induction going), `(z^{(k)}_1, …, z^{(k)}_r, y)` a regular system of
parameters of `R_k` with `W^{(k)}_η = (z^{(k)}_j)` and `F^{(k)}_η` the maximal ideal. -/
def IterationStage.LocalClaim (s : IterationStage.{u}) {R₀ : Type u} [CommRing R₀]
    (T₀ : Finset R₀) (y₀ w₀ : R₀) (k : ℕ) : Prop :=
  ∃ η : s.X, IsGenericPoint η s.F.pts ∧
    ∃ (ψ : R₀ →+* s.X.presheaf.stalk η) (y : s.X.presheaf.stalk η)
      (ζ : R₀ → s.X.presheaf.stalk η) (w' : s.X.presheaf.stalk η),
      ψ y₀ = y ∧ y ∈ nonZeroDivisors (s.X.presheaf.stalk η) ∧
      (∀ z ∈ T₀, ψ z = y ^ k * ζ z) ∧
      (∀ z ∈ T₀, ζ z ∈ maximalIdeal (s.X.presheaf.stalk η)) ∧
      ψ w₀ = y ^ k * w' ∧ s.E.stalkIdeal η = Ideal.span {w'} ∧ y ∉ T₀.image ζ ∧
      IsRegularSystemOfParameters (s.X.presheaf.stalk η) (insert y (T₀.image ζ)) ∧
      s.W.stalkIdeal η = Ideal.span ((T₀.image ζ : Finset _) : Set (s.X.presheaf.stalk η)) ∧
      s.F.stalkIdeal η = maximalIdeal (s.X.presheaf.stalk η) ∧
      w' ∉ maximalIdeal (s.X.presheaf.stalk η) ^ 2

end PrepLocalChain

section PrepLocalChainStep

open IsLocalRing Classical

/-- One step of the paper's induction on p. 288: from the local data at the generic point of
`F^{(k)}` to those at the generic point of `F^{(k+1)}`.  The local ring `R_{k+1}` is the local
ring of the monoidal transform `X^{(k+1)}` at the generic point `η'` of `F^{(k+1)}`, which lies
over `η`; in the chart `R_{k+1} = R_k[M_k / z_t]` the element `z_t` is `y` (the only member of the
regular system of parameters outside the ideal of `W^{(k)}`, since `W^{(k+1)}_{η'} ≠ (1)`), and
`z_j^{(k+1)} = y⁻¹ z_j^{(k)}`, `w^{(k+1)} = y⁻¹ w^{(k)}`.

Gaps filled: "Then we can easily see that `(z_1^{(i)}, …, z_r^{(i)}, y)` is a regular system of
parameters of `R_i`" is proved here (via the chart, the equality `F' = W' ∩ f⁻¹(F)` and the generic
point of `F'` having the maximal ideal as stalk ideal).  The printed claim "as long as `E^{(i)}`
contains `F^{(i)}`, `w^{(i)}` is an element of `M_i` and it generates the prime ideal of `E^{(i)}`
in `R_i`" is proved in the form: if the ideal of `E^{(k)}` in `R_k` is generated by `w^{(k)}`, which
is not in `M_k²`, then the ideal of `E^{(k+1)}` in `R_{k+1}` is generated by `w^{(k+1)} = y⁻¹ w^{(k)}`
(`w^{(k+1)}·y = f^♯ w^{(k)}`) and `w^{(k+1)} ∉ M_{k+1}²`
(`MonoidalTransformation.stalkIdeal_strictTransform_eq_span_and_notMem_sq`).  The condition
`w^{(k)} ∉ M_k²` (`E^{(k)}` non-singular of codimension one at the generic point of `F^{(k)}`) is
what the printed statement tacitly uses: it makes `(w^{(k)})` the *prime* ideal and keeps `y` from
dividing `w^{(k+1)}`. -/
theorem IterationStage.localClaim_next [Hironaka.Cited.MonoidalTransformationExistsIsProper.{u}] (s : IterationStage.{u}) (hs : s.IsAdmissible)
    (hsF : s.F.IsContainedIn (s.W.inter s.E)) (t : MonoidalTransformation s.X s.F)
    (hs' : (s.next t).IsAdmissible) {R₀ : Type u} [CommRing R₀] {T₀ : Finset R₀} {y₀ w₀ : R₀}
    {k : ℕ} (hk : s.LocalClaim T₀ y₀ w₀ k) : (s.next t).LocalClaim T₀ y₀ w₀ (k + 1) := by
  obtain ⟨hXalg, hXns, hWns, hWirr, hFns, hF, hEW, hEprin⟩ := hs
  obtain ⟨-, hX'ns, hW'ns, hW'irr, hF'ns, hF', hE'W', hE'prin⟩ := hs'
  obtain ⟨e, he⟩ := Subscheme.exists_iso_strictTransform_of_exists_stalkIdeal_eq_span hXalg hXns
    s.W hWns hWirr s.E s.F hEprin hEW hF hFns t
  have hFpts := Subscheme.pts_subset_and_pts_subset_of_mem_irreducibleComponents_inter hF
  obtain ⟨Z0, hZ0, hFeq⟩ := id hF
  have hFirr : _root_.IsIrreducible s.F.pts := by
    have : s.F.pts = Z0 := by
      rw [hFeq]; exact Scheme.IdealSheafData.coe_support_vanishingIdeal Z0
    rw [this]; exact hZ0.1.1
  obtain ⟨hF'irr, -⟩ := t.isIrreducible_pts_inducedPreimage_and_subset_image s.W hFpts.1 hFirr e he
  obtain ⟨η', hη'⟩ : ∃ η', IsGenericPoint η' (Subscheme.inducedPreimage t s.W s.F).pts := by
    have := hF'irr.isGenericPoint_genericPoint_closure
    have hcl : closure (Subscheme.inducedPreimage t s.W s.F).pts =
        (Subscheme.inducedPreimage t s.W s.F).pts :=
      (Subscheme.inducedPreimage t s.W s.F).support.isClosed.closure_eq
    rw [hcl] at this
    exact ⟨_, this⟩
  obtain ⟨η, hη, ψ, y, ζ, w', hψy, hy, hψζ, hζm, hψw, hw'E, hyζ, hZrsop, hWη, hFη, hw'sq⟩ := hk
  have hfη' : t.f η' = η := t.eq_of_isGenericPoint_inducedPreimage s.W hFpts.1 hFirr e he hη hη'
  subst hfη'
  have hFW : s.F.IsContainedIn s.W := isContainedIn_of_pts_subset_of_isReduced_toScheme
    (isReduced_toScheme_of_isNonsingular s.F hFns) hFpts.1
  have : IsRegularLocalRing (t.X'.presheaf.stalk η') := hX'ns η'
  have : IsRegularLocalRing (s.X.presheaf.stalk (t.f η')) := hXns _
  have hη'F' : η' ∈ (Subscheme.inducedPreimage t s.W s.F).pts := hη'.mem
  have hη'W' : η' ∈ (Subscheme.strictTransform t s.W).pts := by
    have := hη'F'
    rw [Subscheme.pts_inducedPreimage] at this
    exact this.1
  obtain ⟨zt, φ, hzt, hexc, hztm, hφzt, hrel, hinj, hext, -, hstS⟩ :=
    t.exists_chart_strictTransform_stalkIdeal hXns η' hZrsop (Finset.Subset.refl _)
      (by rw [hFη]; exact hZrsop.1.symm)
  have h1 := hstS (T₀.image ζ) (Finset.subset_insert _ _) s.W hWη
  have hne : (Subscheme.strictTransform t s.W).stalkIdeal η' ≠ ⊤ :=
    Subscheme.mem_pts_iff_stalkIdeal_ne_top.mp hη'W'
  rw [h1] at hne
  have hztS : zt ∉ T₀.image ζ := fun h => hne (by simp [h])
  simp only [hztS, ↓reduceIte] at h1 hne
  have hnu : ∀ q ∈ T₀.image ζ, φ q ∈ maximalIdeal (t.X'.presheaf.stalk η') := by
    intro q hq; by_contra h
    exact hne (Ideal.eq_top_of_isUnit_mem _ (Ideal.subset_span ⟨q, hq, rfl⟩)
      ((IsLocalRing.mem_maximalIdeal _).not.mp h |> not_not.mp))
  have hzty : zt = y := by
    rcases Finset.mem_insert.mp hzt with h | h
    · exact h
    · exact absurd h hztS
  rw [hzty] at hφzt hexc hztm hrel
  -- the element `w'` goes into the exceptional ideal
  have hηE : t.f η' ∈ s.E.pts :=
    (Subscheme.mem_pts_inter_iff.mp (pts_subset_of_isContainedIn hsF hη.mem)).2
  have hw'm : w' ∈ maximalIdeal (s.X.presheaf.stalk (t.f η')) :=
    Subscheme.stalkIdeal_le_maximalIdeal s.E hηE
      (by rw [hw'E]; exact Ideal.mem_span_singleton_self w')
  have hw'F : w' ∈ s.F.stalkIdeal (t.f η') := by rw [hFη]; exact hw'm
  have hfw' : (t.f.stalkMap η').hom w' ∈ t.exceptional.stalkIdeal η' := by
    rw [MonoidalTransformation.exceptional, stalkIdeal_totalTransform]
    exact Ideal.mem_map_of_mem _ hw'F
  rw [hexc, Ideal.mem_span_singleton'] at hfw'
  obtain ⟨w2, hw2⟩ := hfw'
  -- the regular system of parameters at `η'`
  have hspanW : (Subscheme.strictTransform t s.W).stalkIdeal η' =
      Ideal.span ((T₀.image (fun z => φ (ζ z)) : Finset _) : Set (t.X'.presheaf.stalk η')) := by
    rw [h1]
    congr 1
    ext a
    simp
  have hG := t.inducedPreimage_eq_strictTransform_sup_exceptional hXns hFns s.W hWns hFW
  have hF'stalk : (Subscheme.inducedPreimage t s.W s.F).stalkIdeal η' =
      maximalIdeal (t.X'.presheaf.stalk η') :=
    Subscheme.stalkIdeal_eq_maximalIdeal_of_isGenericPoint
      (isReduced_toScheme_of_isNonsingular _ hF'ns) hF'irr hη'
  have hspanK : Ideal.span ((insert (φ y) (T₀.image (fun z => φ (ζ z))) : Finset _) :
      Set (t.X'.presheaf.stalk η')) = maximalIdeal (t.X'.presheaf.stalk η') := by
    rw [← hF'stalk, hG, Subscheme.stalkIdeal_sup_eq, hspanW, hexc, Finset.coe_insert,
      Ideal.span_insert, sup_comm]
  obtain ⟨Z', hKZ', hZ'⟩ := hext
  have hKsub : insert (φ y) (T₀.image (fun z => φ (ζ z))) ⊆ Z' := by
    refine Finset.Subset.trans ?_ hKZ'
    intro a ha
    rcases Finset.mem_insert.mp ha with rfl | ha
    · exact Finset.mem_image_of_mem φ (Finset.mem_filter.mpr ⟨Finset.mem_insert_self _ _, hztm⟩)
    · obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp ha
      exact Finset.mem_image_of_mem φ (Finset.mem_filter.mpr
        ⟨Finset.mem_insert_of_mem (Finset.mem_image_of_mem ζ hz), hnu _ (Finset.mem_image_of_mem ζ hz)⟩)
  have hynzd : φ y ∈ nonZeroDivisors (t.X'.presheaf.stalk η') := by
    obtain ⟨g, hg1, hg2⟩ := Subscheme.IsInvertibleIdeal.exists_stalkIdeal_eq_span t.invertible η'
    exact Subscheme.mem_nonZeroDivisors_of_span_eq (hexc.symm.trans hg1) hg2
  -- the printed claim: `w^{(k+1)}` generates the ideal of `E^{(k+1)}` (and is not in `M²`)
  obtain ⟨hE'gen, hE'sq⟩ := t.stalkIdeal_strictTransform_eq_span_and_notMem_sq hXns hFns η' hFη
    hw'E hw'm hw'sq hexc hynzd hw2
  refine ⟨η', hη', (t.f.stalkMap η').hom.comp ψ, φ y, fun z => φ (ζ z), w2, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_⟩
  · show (t.f.stalkMap η').hom (ψ y₀) = φ y
    rw [hψy, hφzt]
  · exact hynzd
  · intro z hz
    show (t.f.stalkMap η').hom (ψ z) = (φ y) ^ (k + 1) * φ (ζ z)
    have hζy : ζ z ≠ y := fun h => hyζ (h ▸ Finset.mem_image_of_mem ζ hz)
    have := hrel (ζ z) (Finset.mem_insert_of_mem (Finset.mem_image_of_mem ζ hz)) hζy
    rw [hψζ z hz, map_mul, map_pow, ← hφzt, ← this]
    ring
  · intro z hz
    exact hnu _ (Finset.mem_image_of_mem ζ hz)
  · show (t.f.stalkMap η').hom (ψ w₀) = (φ y) ^ (k + 1) * w2
    rw [hψw, map_mul, map_pow, ← hφzt, ← hw2]
    ring
  · exact hE'gen
  · intro h
    obtain ⟨z, hz, hzeq⟩ := Finset.mem_image.mp h
    have hzmem : ζ z ∈ insert y (T₀.image ζ) := Finset.mem_insert_of_mem (Finset.mem_image_of_mem ζ hz)
    have := hinj ⟨hzmem, hnu _ (Finset.mem_image_of_mem ζ hz)⟩
      ⟨Finset.mem_insert_self _ _, hztm⟩ hzeq
    exact hyζ (this ▸ Finset.mem_image_of_mem ζ hz)
  · show IsRegularSystemOfParameters (t.X'.presheaf.stalk η')
      (insert (φ y) (T₀.image fun z => φ (ζ z)))
    exact isRegularSystemOfParameters_of_subset_of_span_eq_maximalIdeal hZ' hKsub hspanK
  · exact hspanW
  · exact hF'stalk
  · exact hE'sq

end PrepLocalChainStep

section PrepLocalChainBase

open IsLocalRing Classical

/-- The starting data of the paper's argument (p. 288): at the generic point `η` of `F`, with
`R = O_{X,η}`, `P = W_η` and maximal ideal `M = F_η`: a minimal base `(z_1, …, z_r)` of `P`
(`T₀`) completed by `y₀` to a regular system of parameters (`M = P + (y₀)` because `F` has
codimension one in `W`), and an element `w₀` of the ideal of `E` which is not in `P` since
`E ⊉ W`.

Deviation from the paper (gap filled): "Let `(z_1, …, z_r)` be a minimal base of the prime ideal
`P_0` in `R_0` and `(z_1, …, z_r, y)` a regular system of parameters of `R_0`": the existence of
`y` uses that the image of `F` in `O_{W,η}` is a principal prime (`F` has codimension one in `W`,
as in the first assertion of Lemma 5). The element `w₀` is, as printed, a generator of the ideal of `E` in `R₀`
(`E` has codimension one and is non-singular at `η`, so the ideal is principal), and it is not in
`P_0` since `E` does not contain `W`; moreover `w₀ ∉ M₀²` because `R₀/(w₀)` is regular (this is
the base case of the invariant `w^{(k)} ∉ M_k²`, gap filled). -/
theorem IterationStage.exists_localClaim_zero (s : IterationStage.{u}) (hs : s.IsAdmissible)
    (hE : s.E.IsNonsingularIrreducibleCodimOne) :
    ∃ η : s.X, IsGenericPoint η s.F.pts ∧
      ∃ (T₀ : Finset (s.X.presheaf.stalk η)) (y₀ w₀ : s.X.presheaf.stalk η),
        w₀ ∈ s.E.stalkIdeal η ∧ w₀ ∉ s.W.stalkIdeal η ∧
        s.W.stalkIdeal η = Ideal.span (T₀ : Set (s.X.presheaf.stalk η)) ∧
        maximalIdeal (s.X.presheaf.stalk η) = s.W.stalkIdeal η ⊔ Ideal.span {y₀} ∧
        s.LocalClaim T₀ y₀ w₀ 0 := by
  obtain ⟨hXalg, hXns, hWns, hWirr, hFns, hF, hEW, hEprin⟩ := hs
  have hFpts := Subscheme.pts_subset_and_pts_subset_of_mem_irreducibleComponents_inter hF
  obtain ⟨Z0, hZ0, hFeq⟩ := id hF
  have hFirr : _root_.IsIrreducible s.F.pts := by
    have : s.F.pts = Z0 := by
      rw [hFeq]; exact Scheme.IdealSheafData.coe_support_vanishingIdeal Z0
    rw [this]; exact hZ0.1.1
  obtain ⟨η, hη⟩ : ∃ η, IsGenericPoint η s.F.pts := by
    have := hFirr.isGenericPoint_genericPoint_closure
    have hcl : closure s.F.pts = s.F.pts := s.F.support.isClosed.closure_eq
    rw [hcl] at this
    exact ⟨_, this⟩
  have hFη : s.F.stalkIdeal η = maximalIdeal (s.X.presheaf.stalk η) :=
    Subscheme.stalkIdeal_eq_maximalIdeal_of_isGenericPoint
      (isReduced_toScheme_of_isNonsingular _ hFns) hFirr hη
  have hηF : η ∈ s.F.pts := hη.mem
  have hηW : η ∈ s.W.pts := hFpts.1 hηF
  have hFW' : s.F.IsContainedIn s.W := isContainedIn_of_pts_subset_of_isReduced_toScheme
    (isReduced_toScheme_of_isNonsingular s.F hFns) hFpts.1
  obtain ⟨u, rfl⟩ : η ∈ Set.range s.W.ι := by
    rw [Scheme.IdealSheafData.range_subschemeι]; exact hηW
  have : IsRegularLocalRing (s.X.presheaf.stalk (s.W.ι u)) := hXns _
  have := isDomain_of_isRegularLocalRing (s.X.presheaf.stalk (s.W.ι u))
  obtain ⟨hWp, hWreg⟩ := isPrime_and_isRegularLocalRing_quotient_of_isNonsingular s.W hWns hηW
  -- `w₀`: a generator of the ideal of `E` in `R₀` ("an element of `M₀` which generates the ideal
  -- `E^{(0)}` in `R₀`"); it is not in `P₀` since `E` does not contain `W`
  have hηE : s.W.ι u ∈ s.E.pts := hFpts.2 hηF
  obtain ⟨w₀, hEe⟩ := hEprin _ hηF
  have hw₀E : w₀ ∈ s.E.stalkIdeal (s.W.ι u) := by rw [hEe]; exact Ideal.mem_span_singleton_self w₀
  have hw₀W : w₀ ∉ s.W.stalkIdeal (s.W.ι u) := fun h =>
    not_stalkIdeal_le_of_not_isContainedIn s.W s.E hWns hWirr hEW hηW
      (by rw [hEe]; exact (Ideal.span_singleton_le_iff_mem _).mpr h)
  -- `E` is non-singular of codimension one: `R₀/(w₀)` is regular, so `w₀ ∉ M₀²`
  have hw₀m : w₀ ∈ maximalIdeal (s.X.presheaf.stalk (s.W.ι u)) :=
    Subscheme.stalkIdeal_le_maximalIdeal s.E hηE hw₀E
  have hw₀sq : w₀ ∉ maximalIdeal (s.X.presheaf.stalk (s.W.ι u)) ^ 2 := by
    obtain ⟨hEns, -, -⟩ := hE.resolve_left fun hEe' => by
      rw [hEe'] at hηE
      exact absurd hηE (by rw [DatumTransform.pts_empty]; exact id)
    obtain ⟨-, hEreg⟩ := isPrime_and_isRegularLocalRing_quotient_of_isNonsingular s.E hEns hηE
    have hw₀0 : w₀ ≠ 0 := fun h => hw₀W (h ▸ zero_mem _)
    have : IsRegularLocalRing (s.X.presheaf.stalk (s.W.ι u) ⧸ Ideal.span {w₀}) := by
      rw [← hEe]; exact hEreg
    exact rsop_notMem_sq_of_quotient hw₀m hw₀0
  -- `T₀`
  obtain ⟨S, T₀, hS, hScard, hTS, hT₀⟩ :=
    exists_finset_span_eq_prime _ (s.W.stalkIdeal (s.W.ι u)) hWreg
  have hSr : IsRegularSystemOfParameters _ S :=
    ⟨hS, by rw [hScard]; exact IsRegularLocalRing.spanFinrank_maximalIdeal⟩
  -- the principal ideal of `F` in `O_{W,u}`
  obtain ⟨g, hg1, hg2⟩ := exists_stalkIdeal_totalTransform_eq_span_of_exists_stalkIdeal_eq_span
    hXns s.W hWns hWirr s.E s.F hEprin hEW hF hFns u
  set φ := (s.W.ι.stalkMap u).hom with hφdef
  have hφ : Function.Surjective φ := s.W.ι.stalkMap_surjective u
  have hker : RingHom.ker φ = s.W.stalkIdeal (s.W.ι u) := (stalkIdeal_eq_ker_stalkMap s.W u).symm
  have hg0 : g ≠ 0 := by
    rintro rfl
    have := (mem_nonZeroDivisors_iff_right.mp hg2) 1 (by simp)
    exact one_ne_zero this
  rw [stalkIdeal_totalTransform, hFη] at hg1
  have hgmem : g ∈ (maximalIdeal (s.X.presheaf.stalk (s.W.ι u))).map φ := by
    rw [hg1]; exact Ideal.mem_span_singleton_self g
  obtain ⟨y₀, hy₀m, hy₀g⟩ := (Ideal.mem_map_iff_of_surjective φ hφ).mp hgmem
  have hy₀0 : y₀ ≠ 0 := by rintro rfl; exact hg0 (by rw [← hy₀g, map_zero])
  have hy₀W : y₀ ∉ s.W.stalkIdeal (s.W.ι u) := by
    intro h; rw [← hker] at h; exact hg0 (by rw [← hy₀g]; exact h)
  -- `M = P + (y₀)`
  have hM : maximalIdeal (s.X.presheaf.stalk (s.W.ι u)) =
      s.W.stalkIdeal (s.W.ι u) ⊔ Ideal.span {y₀} := by
    apply le_antisymm
    · intro a ha
      have hφa : φ a ∈ Ideal.span {g} := by
        rw [← hg1]; exact Ideal.mem_map_of_mem _ ha
      obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp hφa
      obtain ⟨c', rfl⟩ := hφ c
      have : a - c' * y₀ ∈ s.W.stalkIdeal (s.W.ι u) := by
        rw [← hker, RingHom.mem_ker, map_sub, map_mul, hy₀g, hc, sub_self]
      have h2 : a = (a - c' * y₀) + c' * y₀ := by ring
      rw [h2]
      exact Submodule.add_mem_sup this (Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self y₀))
    · refine sup_le ?_ ?_
      · rw [← hFη]; exact Subscheme.stalkIdeal_mono (fun U => hFW' U) _
      · rw [Ideal.span_le, Set.singleton_subset_iff]; exact hy₀m
  have hWm : s.W.stalkIdeal (s.W.ι u) ≠ maximalIdeal (s.X.presheaf.stalk (s.W.ι u)) := by
    intro h; apply hy₀W; rw [h]; exact hy₀m
  have hy₀T : y₀ ∉ T₀ := fun h => hy₀W (by rw [← hT₀]; exact Ideal.subset_span h)
  have hTm : ∀ z ∈ T₀, z ∈ maximalIdeal (s.X.presheaf.stalk (s.W.ι u)) := by
    intro z hz
    have : z ∈ s.W.stalkIdeal (s.W.ι u) := by rw [← hT₀]; exact Ideal.subset_span hz
    exact (Subscheme.stalkIdeal_le_maximalIdeal s.W hηW) this
  have hspanZ : Ideal.span ((insert y₀ T₀ : Finset _) : Set (s.X.presheaf.stalk (s.W.ι u))) =
      maximalIdeal (s.X.presheaf.stalk (s.W.ι u)) := by
    rw [Finset.coe_insert, Ideal.span_insert, hT₀, hM, sup_comm]
  have hTne : T₀ ≠ S := by
    rintro rfl
    exact hWm (by rw [← hT₀, hS])
  have hcard : (insert y₀ T₀).card ≤ (maximalIdeal (s.X.presheaf.stalk (s.W.ι u))).spanFinrank := by
    rw [Finset.card_insert_of_notMem hy₀T, ← hScard]
    exact Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hTS, hTne⟩)
  have hZrsop : IsRegularSystemOfParameters _ (insert y₀ T₀) :=
    rsop_of_span_of_card_le hspanZ hcard
  refine ⟨_, hη, T₀, y₀, w₀, hw₀E, hw₀W, hT₀.symm, hM, ?_⟩
  refine ⟨_, hη, RingHom.id _, y₀, id, w₀, rfl, mem_nonZeroDivisors_of_ne_zero hy₀0, ?_, ?_,
    by simp, hEe, by simpa using hy₀T, by simpa using hZrsop, by simpa using hT₀.symm, hFη,
    hw₀sq⟩
  · intro z hz; simp
  · intro z hz; exact hTm z hz

end PrepLocalChainBase

section PrepNu

open IsLocalRing Classical

/-- The integer `ν` of the paper (p. 288): "we have a positive integer `ν` such that
`P_0 + (y^ν)R_0` contains `w` but `P_0 + (y^{ν+1})R_0` does not" (Krull's intersection theorem in
`R_0/P_0`, `w ∉ P_0`). -/
theorem exists_nat_mem_sup_pow_not_mem_sup_pow {R : Type u} [CommRing R] [IsNoetherianRing R]
    [IsLocalRing R] (P : Ideal R) {y w : R} (hy : y ∈ maximalIdeal R) (hw : w ∉ P) :
    ∃ ν : ℕ, w ∈ P ⊔ Ideal.span {y ^ ν} ∧ w ∉ P ⊔ Ideal.span {y ^ (ν + 1)} := by
  have hPm : P ≤ maximalIdeal R :=
    IsLocalRing.le_maximalIdeal fun h => hw (h ▸ Submodule.mem_top)
  have := isLocalRing_quotient_of_le hPm
  have hex : ∃ n : ℕ, w ∉ P ⊔ Ideal.span {y ^ n} := by
    by_contra h
    push Not at h
    have : IsLocalHom (Ideal.Quotient.mk P) :=
      IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective
    have hy' : Ideal.Quotient.mk P y ∈ maximalIdeal (R ⧸ P) :=
      map_nonunit (Ideal.Quotient.mk P) y hy
    have hne : Ideal.span {Ideal.Quotient.mk P y} ≠ ⊤ := by
      rw [Ne, Ideal.span_singleton_eq_top]
      exact (mem_maximalIdeal _).mp hy'
    have hmem : Ideal.Quotient.mk P w ∈ ⨅ n : ℕ, (Ideal.span {Ideal.Quotient.mk P y}) ^ n := by
      refine Submodule.mem_iInf _ |>.mpr fun n => ?_
      rw [Ideal.span_singleton_pow]
      have := (Ideal.mem_quotient_iff_mem_sup (I := P) (J := Ideal.span {y ^ n})).mpr
        (by rw [sup_comm]; exact h n)
      rwa [Ideal.map_span, Set.image_singleton, map_pow] at this
    rw [Ideal.iInf_pow_eq_bot_of_isLocalRing _ hne, Submodule.mem_bot,
      Ideal.Quotient.eq_zero_iff_mem] at hmem
    exact hw hmem
  have hN0 : Nat.find hex ≠ 0 := by
    intro h0
    have := Nat.find_spec hex
    rw [h0] at this
    exact this (by rw [pow_zero, Ideal.span_singleton_one, sup_top_eq]; exact Submodule.mem_top)
  obtain ⟨ν, hν⟩ := Nat.exists_eq_succ_of_ne_zero hN0
  refine ⟨ν, ?_, ?_⟩
  · by_contra h
    exact Nat.find_min hex (by omega : ν < Nat.find hex) h
  · have := Nat.find_spec hex
    rwa [hν] at this

end PrepNu

section PrepTermination

open IsLocalRing Classical

/-- Third assertion of Lemma 5 (p. 288): the process `F ↦ F' ↦ F'' ↦ ⋯` ends after a finite
number of steps.  The proof follows the paper: if `F^{(i)} ⊆ W^{(i)} ∩ E^{(i)}` for all `i`, then
with `R_i`, `P_i`, `w`, `(z_1,…,z_r,y)`, `z_j^{(i)} = y^{-i} z_j`, `w^{(i)} = y^{-i} w` (`w` a generator of the ideal of `E` in `R_0`) and the
integer `ν` with `w ∈ P_0 + (y^ν)`, `w ∉ P_0 + (y^{ν+1})`, one has `w = Σ a_j z_j + u y^ν` with
`u` a unit, hence `w^{(ν)} = Σ a_j z_j^{(ν)} + u` is a unit of `R_ν` lying in the ideal of
`E^{(ν)}`, so `E^{(ν)}` does not pass through the generic point of `F^{(ν)}`.

Gaps filled: the printed claim "Then, as long as `E^{(i)}` contains `F^{(i)}`, `w^{(i)}` is an
element of `M_i` and it generates the prime ideal of `E^{(i)}` in `R_i`" is proved as printed
(`hprinted`, from `IterationStage.localClaim_next`; `w` is a generator of the ideal of `E` in
`R_0`; tacitly the induction carries `w^{(i)} ∉ M_i²`, i.e. `E^{(i)}` non-singular of codimension
one at the generic point of `F^{(i)}`, which also gives the primality); "we can easily see that
`(z_1^{(i)}, …, z_r^{(i)}, y)` is a regular system of parameters of `R_i`" and "one can easily see
that `w^{(ν)}` is a unit" are proved (the latter from `w = Σ a_j z_j + u y^ν`: `u` is a unit since
otherwise `w ∈ P_0 + (y^{ν+1})`).  Also the paper applies Lemma 5 again to `(X', W', E', F')`
without checking its hypotheses: `IterationStage.isAdmissible_next` proves that they hold
(non-singularity of `X'` and of `f̃⁻¹(F)`, `f̃⁻¹(F)` a component of `W' ∩ E'`, `W' ⊄ E'`, the ideal
of `E'` principal along `f̃⁻¹(F)`). -/
theorem exists_not_isContainedIn_of_isIteration [Hironaka.Cited.MonoidalTransformationExistsIsProper.{u}] {X : Scheme.{u}} (hXalg : IsAlgebraicScheme X)
    (hXns : X.IsNonsingular) (W : Subscheme X) (hWns : W.IsNonsingular)
    (hWirr : W.IsIrreducible) (E : Subscheme X) (hE : E.IsNonsingularIrreducibleCodimOne)
    (hEW : ¬ W.IsContainedIn E) (F : Subscheme X) (hF : F ∈ (W.inter E).irreducibleComponents)
    (hFns : F.IsNonsingular) (g : ℕ → IterationStage.{u}) (hg : IterationStage.IsIteration g)
    (h0 : g 0 = ⟨X, W, E, F⟩) :
    ∃ i, ¬ (g i).F.IsContainedIn ((g i).W.inter (g i).E) := by
  by_contra hcon
  have H : ∀ i, (g i).F.IsContainedIn ((g i).W.inter (g i).E) := fun i =>
    by_contra fun h => hcon ⟨i, h⟩
  have hEprin : ∀ x ∈ F.pts, ∃ e, E.stalkIdeal x = Ideal.span {e} := fun x hx =>
    Subscheme.exists_stalkIdeal_eq_span_of_isNonsingularIrreducibleCodimOne hXns hE
      ((Subscheme.pts_subset_and_pts_subset_of_mem_irreducibleComponents_inter hF).2 hx)
  have adm : ∀ i, (g i).IsAdmissible := by
    intro i
    induction i with
    | zero => rw [h0]; exact ⟨hXalg, hXns, hWns, hWirr, hFns, hF, hEW, hEprin⟩
    | succ i ih =>
      obtain ⟨t, ht⟩ := hg i
      rw [ht]
      exact (g i).isAdmissible_next ih t (ht ▸ H (i + 1))
  obtain ⟨η₀, hη₀, T₀, y₀, w₀, hw₀E, hw₀W, hT₀, hM, hc0⟩ :=
    (g 0).exists_localClaim_zero (adm 0) (by rw [h0]; exact hE)
  have hclaim : ∀ k, (g k).LocalClaim T₀ y₀ w₀ k := by
    intro k
    induction k with
    | zero => exact hc0
    | succ k ih =>
      obtain ⟨t, ht⟩ := hg k
      rw [ht]
      exact (g k).localClaim_next (adm k) (H k) t (ht ▸ adm (k + 1)) ih
  -- "Then, as long as `E^{(i)}` contains `F^{(i)}`, `w^{(i)}` is an element of `M_i` and it
  -- generates the prime ideal of `E^{(i)}` in `R_i`":
  have hprinted : ∀ k, ∃ η, IsGenericPoint η (g k).F.pts ∧ ∃ w' : (g k).X.presheaf.stalk η,
      w' ∈ maximalIdeal ((g k).X.presheaf.stalk η) ∧
      (g k).E.stalkIdeal η = Ideal.span {w'} ∧ ((g k).E.stalkIdeal η).IsPrime := by
    intro k
    obtain ⟨η, hη, ψ, y, ζ, w', -, -, -, -, -, hw'E, -, -, -, -, hw'sq⟩ := hclaim k
    have hηE : η ∈ (g k).E.pts :=
      (Subscheme.mem_pts_inter_iff.mp (pts_subset_of_isContainedIn (H k) hη.mem)).2
    have hw'm : w' ∈ maximalIdeal ((g k).X.presheaf.stalk η) :=
      Subscheme.stalkIdeal_le_maximalIdeal (g k).E hηE
        (by rw [hw'E]; exact Ideal.mem_span_singleton_self w')
    have : IsRegularLocalRing ((g k).X.presheaf.stalk η) := (adm k).2.1 η
    refine ⟨η, hη, w', hw'm, hw'E, ?_⟩
    rw [hw'E]
    exact isPrime_span_singleton_of_mem_maximalIdeal_of_notMem_sq hw'm hw'sq
  -- the integer `ν`
  have hXn : IsRegularLocalRing ((g 0).X.presheaf.stalk η₀) := (adm 0).2.1 η₀
  have hy₀m : y₀ ∈ maximalIdeal ((g 0).X.presheaf.stalk η₀) := by
    rw [hM]; exact Ideal.mem_sup_right (Ideal.mem_span_singleton_self y₀)
  obtain ⟨ν, hν1, hν2⟩ := exists_nat_mem_sup_pow_not_mem_sup_pow ((g 0).W.stalkIdeal η₀) hy₀m hw₀W
  obtain ⟨p, hp, q, hq, hpq⟩ := Submodule.mem_sup.mp hν1
  obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hq
  -- `c` is a unit
  have hcu : IsUnit c := by
    by_contra hcu
    apply hν2
    have hcm : c ∈ (g 0).W.stalkIdeal η₀ ⊔ Ideal.span {y₀} := by
      rw [← hM]; exact (mem_maximalIdeal c).mpr hcu
    obtain ⟨p', hp', e', he', hp'e'⟩ := Submodule.mem_sup.mp hcm
    obtain ⟨d, rfl⟩ := Ideal.mem_span_singleton'.mp he'
    rw [← hpq, ← hp'e']
    refine Submodule.mem_sup.mpr ⟨p + p' * y₀ ^ ν, ?_, d * y₀ ^ (ν + 1), ?_, ?_⟩
    · exact Ideal.add_mem _ hp (Ideal.mul_mem_right _ _ hp')
    · exact Ideal.mem_span_singleton'.mpr ⟨d, by ring⟩
    · ring
  -- the unit `w^{(ν)}`
  obtain ⟨η, hη, ψ, y, ζ, w', hψy, hy, hψζ, hζm, hψw, hw'E, -, -, -, -, -⟩ := hclaim ν
  rw [hT₀] at hp
  obtain ⟨a, -, hap⟩ := Submodule.mem_span_finset.mp hp
  have hψp : ψ p = ∑ z ∈ T₀, ψ (a z) * (y ^ ν * ζ z) := by
    rw [← hap, map_sum]
    exact Finset.sum_congr rfl fun z hz => by rw [smul_eq_mul, map_mul, hψζ z hz]
  have hkey : y ^ ν * w' = y ^ ν * ((∑ z ∈ T₀, ψ (a z) * ζ z) + ψ c) := by
    rw [← hψw, ← hpq, map_add, map_mul, map_pow, hψy, hψp, mul_add, Finset.mul_sum]
    congr 1
    · exact Finset.sum_congr rfl fun z hz => by ring
    · ring
  have hnz : y ^ ν ∈ nonZeroDivisors ((g ν).X.presheaf.stalk η) := pow_mem hy ν
  have hw'eq : w' = (∑ z ∈ T₀, ψ (a z) * ζ z) + ψ c := by
    have : (w' - ((∑ z ∈ T₀, ψ (a z) * ζ z) + ψ c)) * y ^ ν = 0 := by
      rw [sub_mul, mul_comm w', hkey, mul_comm]; ring
    exact sub_eq_zero.mp ((mul_right_mem_nonZeroDivisors_eq_zero_iff hnz).mp this)
  -- contradiction: `w'` lies in a proper ideal
  have hηE : η ∈ (g ν).E.pts :=
    (Subscheme.mem_pts_inter_iff.mp (pts_subset_of_isContainedIn (H ν) hη.mem)).2
  have hw'm : w' ∈ maximalIdeal ((g ν).X.presheaf.stalk η) :=
    Subscheme.stalkIdeal_le_maximalIdeal (g ν).E hηE
      (by rw [hw'E]; exact Ideal.mem_span_singleton_self w')
  have hSm : (∑ z ∈ T₀, ψ (a z) * ζ z) ∈ maximalIdeal ((g ν).X.presheaf.stalk η) :=
    Ideal.sum_mem _ fun z hz => Ideal.mul_mem_left _ _ (hζm z hz)
  have : ψ c ∈ maximalIdeal ((g ν).X.presheaf.stalk η) := by
    have h2 : ψ c = w' - ∑ z ∈ T₀, ψ (a z) * ζ z := by rw [hw'eq]; ring
    rw [h2]; exact Ideal.sub_mem _ hw'm hSm
  exact (mem_maximalIdeal _).mp this (hcu.map ψ)

end PrepTermination

/-- **Lemma 5** (pp. 287–288).  Blowing up a non-singular component `F` of `W ∩ E` does not
change `W`, replaces `red(W ∩ E)` by (at most) the components other than `F`, and the
resulting process terminates. -/
@[blueprint "lem:IV.2-5"
  (statement := /-- \textbf{Lemma 5.} Let $X$ be a non-singular irreducible algebraic scheme,
    $W$ a non-singular irreducible subscheme of $X$, and $E$ a non-singular irreducible
    subscheme of codimension $1$ of $X$ such that $E$ does not contain $W$. Let $F$ be a
    reduced irreducible component of $W\cap E$, and assume that $F$ is non-singular. Let
    $f\colon X'\to X$ be the monoidal transformation of $X$ with center $F$, and let $E'$ and
    $W'$ be the strict transforms of $E$ and $W$ on $X'$ respectively. Then $f$ induces an
    isomorphism $\tilde f$ of $W'$ to $W$. If $F_1(=F),\dots,F_m$ are the reduced irreducible
    components of $W\cap E$, then $\operatorname{red}(W'\cap E')$ is either
    $\bigcup_{j=2}^m\tilde f^{-1}(F_j)$ or $\bigcup_{j=1}^m\tilde f^{-1}(F_j)$. Let
    $F'=\tilde f^{-1}(F)$. If $F'\subseteq W'\cap E'$, then we take the monoidal
    transformation $f'\colon X''\to X'$ with center $F'$. Let $\tilde f'$ be the induced
    isomorphism of the strict transform $W''$ of $W'$ (on $X''$) to $W'$. If
    $\tilde f'^{-1}(F')\subseteq W''\cap E''$, where $E''$ is the strict transform of $E'$ on
    $X''$, we take the monoidal transformation of $X''$ with center
    $F''=\tilde f'^{-1}(F')$, and so on. Then this process ends up by a finite number of
    steps. (pp.~287--288.)

    (Formalization notes (encoding). (a) ``$f$ induces an isomorphism $\tilde f$ of $W'$ to $W$'' is
    rendered as the existence of an isomorphism of schemes $e\colon W'\to W$ with
    $e\circ\iota_W=\iota_{W'}\circ f$, i.e.\ compatible with the closed immersions into $X$
    and $X'$. (b) $\tilde f^{-1}(D)$ for $D\subseteq W$ is rendered as
    $\operatorname{red}(W'\cap f^{-1}(D))$, which is how Hironaka himself writes
    $\tilde f^{-1}(F)$ in the proof. (c) The enumeration $F_1,\dots,F_m$ is indexed by
    $\mathrm{Fin}(m+1)$ with $F_0=F$, so the paper's $m$ is our $m+1$ and the paper's
    $\bigcup_{j=2}^m$ is our union over $\mathrm{Fin}\,m$ shifted by one. (d) The last
    assertion is rendered as: for every sequence of stages
    $(X^{(i)},W^{(i)},E^{(i)},F^{(i)})$ obtained by the described iteration, there is an $i$
    with $F^{(i)}\not\subseteq W^{(i)}\cap E^{(i)}$ --- which is exactly what the proof
    establishes (``we want to show that $E^{(i)}\cap W^{(i)}$ does not contain $F^{(i)}$ for
    sufficiently large $i$''), the iteration stopping at the first such $i$.
    (e) $E$ is allowed to be empty, following the agreement of pp.~274--275; the hypothesis
    on $F$ is then vacuous.) -/)
  (proof := /-- The monoidal transformation $f\colon X'\to X$ induces in $W$ the monoidal
    transformation of $W$ with center $F$, which is clearly an isomorphism because $W$ is
    non-singular and $F$ has codimension $1$ in $W$.

    \textbf{Deviation from the paper (gap filled).} ``Clearly an isomorphism'' is proved in
    Lean: the ideal of $F$ in $W$ is invertible, because at $x\in F$ it is a prime of
    $\mathcal O_{W,x}$ of height $\le1$ (Krull's principal ideal theorem: it is minimal over the
    image of the equation of $E$, which is nonzero as $W\not\subseteq E$), nonzero, with regular
    quotient ($F$ is non-singular), hence principal, generated by a non-zero-divisor; a sheaf of
    ideals which is stalkwise principal generated by a non-zero-divisor is invertible; and a
    monoidal transformation whose center has an invertible ideal sheaf is an isomorphism.

    $W'\cap E'$ is everywhere of codimension
    $1$ on the non-singular irreducible algebraic scheme $W'$, and
    $\operatorname{red}(W'\cap E')\subseteq
    \big(\bigcup_{j=2}^m\tilde f^{-1}(F_j)\big)\cup\big(W'\cap f^{-1}(F)\big)
    =\bigcup_{j=1}^m\tilde f^{-1}(F_j)$. Therefore either
    $\operatorname{red}(W'\cap E')=\bigcup_{j=2}^m\tilde f^{-1}(F_j)$ or
    $=\bigcup_{j=1}^m\tilde f^{-1}(F_j)$.

    \textbf{Gaps filled.} (1) ``$W'\cap E'$ is everywhere of codimension $1$ on $W'$'' is asserted
    without proof; Lean proves it: the ideal of $E'$ is principal at every point of $X'$ (at the
    exceptional divisor by saturating the principal ideal of $E$ by the prime element equation of
    the exceptional divisor, elsewhere $f$ is a local isomorphism), and at a point $w$ of
    $W'\cap E'$ the ideal of $W'\cap E'$ in the regular local ring $\mathcal O_{W',w}$ is generated
    by a non-zero non-unit (non-zero, otherwise the generic point of $W'$ lies on $E'$ and
    $W'\subseteq E'$, contradicting $W\not\subseteq E$), hence has height $1$ by Krull's principal
    ideal theorem. (2) The inclusion $\operatorname{red}(W'\cap E')\subseteq\bigcup_{j\ge1}\tilde
    f^{-1}(F_j)$: a point of $W'\cap E'$ lies over a point of $W\cap E$, which lies on an
    irreducible component. (3) $\tilde f^{-1}(F_j)\subseteq W'\cap E'$ for $j\ge2$, which the
    paper does not mention: over $F_j-F$ the morphism $f$ is a local isomorphism, so $E'=E$ there,
    and $\tilde f^{-1}(F_j)$ is the closure of the part over $F_j-F$ because $F_j$ is irreducible
    and $F_j\not\subseteq F$. (4) Each $\tilde f^{-1}(F_j)$ is irreducible and proper in $W'$
    ($W'\subseteq\tilde f^{-1}(F_j)$ would give $W=f(W')\subseteq F_j\subseteq E$). ``Therefore
    either \dots'': every point of $W'\cap E'$ lies on some $\tilde f^{-1}(F_j)$ contained in
    $W'\cap E'$ (an irreducible component $C$ through it lies in some $\tilde f^{-1}(F_j)$; if
    $C\subsetneq\tilde f^{-1}(F_j)$, the chain $W'\supsetneq\tilde f^{-1}(F_j)\supsetneq C$ gives
    dimension $\ge2$ at the generic point of $C$, contradicting codimension $1$), so
    $\operatorname{red}(W'\cap E')$ is a union of some of the $\tilde f^{-1}(F_j)$; as all
    $\tilde f^{-1}(F_j)$ with $j\ge2$ are contained in $W'\cap E'$, it is
    $\bigcup_{j\ge2}$ or $\bigcup_{j\ge1}$.

    To prove the last statement, let $\{f^{(i)}\colon X^{(i+1)}\to X^{(i)}\}$ be any sequence
    of monoidal transformations with center $F^{(i)}$ in $X^{(i)}$, where $X^{(0)}=X$,
    $F^{(0)}=F$, and $F^{(i+1)}=$ the image of $F^{(i)}$ in the strict transform $W^{(i+1)}$
    of $W^{(i)}\ (=W)$ on $X^{(i+1)}$ $(i=0,1,2,\dots)$. Let $E^{(i)}$ be the strict transform
    of $E^{(0)}\ (=E)$ on $X^{(i)}$. We want to show that $E^{(i)}\cap W^{(i)}$ does not
    contain $F^{(i)}$ for sufficiently large $i$. Let $R_i$ be the local ring of $X^{(i)}$ at
    the generic point of $F^{(i)}$, $M_i$ the maximal ideal of $R_i$ and $P_i$ the prime ideal
    of $W^{(i)}$ in $R_i$ $(i=0,1,2,\dots)$. Let $w$ be an element of $M_0$ which generates
    the ideal of $E^{(0)}$ in $R_0$. Let $(z_1,\dots,z_r)$ be a minimal base of the prime
    ideal $P_0$ in $R_0$ and $(z_1,\dots,z_r,y)$ a regular system of parameters of $R_0$. Let
    $z_j^{(i)}=y^{-i}z_j\ (1\le j\le r)$ for $i=0,1,2,\dots$. Then we can easily see that
    $(z_1^{(i)},\dots,z_r^{(i)},y)$ is a regular system of parameters of $R_i$. Let
    $w^{(i)}=y^{-i}w$ for $i=0,1,2,\dots$. Then, as long as $E^{(i)}$ contains $F^{(i)}$,
    $w^{(i)}$ is an element of $M_i$ and it generates the prime ideal of $E^{(i)}$ in $R_i$.
    Since $E$ does not contain $W$, $w$ is not contained in $P_0$; hence we have a positive
    integer $\nu$ such that $P_0+(y^\nu)R_0$ contains $w$ but $P_0+(y^{\nu+1})R_0$ does not.
    Then one can easily see that $w^{(\nu)}$ is a unit of $R_\nu$. In fact, $w$ can be written
    in the form $w=\sum a_jz_j+uy^\nu$ with $a_j\in R_0\ (1\le j\le r)$ and with a unit $u$ of
    $R_0$. Then $w^{(\nu)}=\sum a_jz_j^{(\nu)}+u$, which is clearly a unit of $R_\nu$.
    \textsc{q.e.d.}

    \textbf{Gaps filled.} The paper's termination argument is followed step by step; what it
    omits, asserts or uses tacitly is proved in Lean. (1) The paper applies
    the lemma again to $(X',W',E',F')$ and so on: Lean proves that the hypotheses of the lemma
    are inherited (non-singularity of $X'$ and of $\tilde f^{-1}(F)=W'\cap f^{-1}(F)$ as a
    scheme, $\tilde f^{-1}(F)$ is a component of $W'\cap E'$, $W'\not\subseteq E'$, the ideal of
    $E'$ is principal along $\tilde f^{-1}(F)$), and that $F^{(i)}\ne\emptyset$ (through
    $W^{(i+1)}\cong W^{(i)}$). (2) ``Let $(z_1,\dots,z_r,y)$ be a regular system of
    parameters of $R_0$'': the element $y$ exists because the image of $F$ in $\mathcal O_{W,\eta}$
    is a principal prime ($F$ has codimension one in $W$), so $M_0=P_0+(y)$. (3) ``Then we can
    easily see that $(z_1^{(i)},\dots,z_r^{(i)},y)$ is a regular system of parameters of $R_i$'':
    proved from the chart $R_{i+1}=R_i[M_i/z_t]$, where $z_t=y$ because $W^{(i+1)}$ has a point
    over the generic point of $F^{(i)}$, together with $F'=W'\cap f^{-1}(F)$ and the fact that the
    stalk of the ideal of the generic point of $F^{(i+1)}$ is the maximal ideal. (4)
    ``$w^{(i)}$ is an element of $M_i$ and it generates the prime ideal of $E^{(i)}$ in $R_i$'':
    proved as printed, with $w$ a generator of the ideal of $E$ in $R_0$ (it is principal since $E$
    is non-singular of codimension one). The proof is by induction on $i$ and carries the tacit
    fact that $w^{(i)}\notin M_i^2$ (i.e.\ $E^{(i)}$ is non-singular of codimension one at the
    generic point of $F^{(i)}$): for $i=0$ because $R_0/(w)$ is regular; if the ideal of $E^{(i)}$
    is $(w^{(i)})$ with $w^{(i)}\in M_i\setminus M_i^2$, $w^{(i)}$ is part of a regular system of
    parameters of $R_i$, and in the corresponding chart of the monoidal transformation the ideal
    of the strict transform is generated by $y^{-1}w^{(i)}=w^{(i+1)}$, which is again outside
    $M_{i+1}^2$. Since $w^{(i)}\in M_i\setminus M_i^2$, the quotient is regular, so $(w^{(i)})$ is
    prime. (5) The integer $\nu$ (Krull's intersection
    theorem in $R_0/P_0$), the form $w=\sum a_jz_j+uy^\nu$ with $u$ a unit (otherwise
    $w\in P_0+(y^{\nu+1})$) and ``$w^{(\nu)}$ is clearly a unit'' are proved: $w^{(\nu)}$ lies in
    the (proper) ideal of $E^{(\nu)}$, so $E^{(\nu)}$ does not contain $F^{(\nu)}$. -/)
  (latexEnv := "lemma")]
theorem MonoidalTransformation.strictTransform_iso_and_inter_eq_unionFam_inducedPreimage [Hironaka.Cited.MonoidalTransformationExistsIsProper.{u}] {X : Scheme.{u}} (hXalg : IsAlgebraicScheme X) (hXns : X.IsNonsingular)
    (_hXirr : IrreducibleSpace X) (W : Subscheme X)
    (hWns : W.IsNonsingular) (hWirr : W.IsIrreducible) (E : Subscheme X)
    (hE : E.IsNonsingularIrreducibleCodimOne) (hEW : ¬ W.IsContainedIn E)
    (F : Subscheme X) (hF : F ∈ (W.inter E).irreducibleComponents) (hFns : F.IsNonsingular)
    (t : MonoidalTransformation X F) :
    -- `f` induces an isomorphism `f̃` of `W'` onto `W`, compatible with the immersions:
    (∃ e : (Subscheme.strictTransform t W).toScheme ≅ W.toScheme,
      e.hom ≫ W.ι = (Subscheme.strictTransform t W).ι ≫ t.f) ∧
    -- `red(W' ∩ E')` is `⋃_{j=2}^m f̃⁻¹(F_j)` or `⋃_{j=1}^m f̃⁻¹(F_j)`:
    (∀ (m : ℕ) (Fc : Fin (m + 1) → Subscheme X), Fc 0 = F → Function.Injective Fc →
      (∀ j, Fc j ∈ (W.inter E).irreducibleComponents) →
      (∀ C ∈ (W.inter E).irreducibleComponents, ∃ j, Fc j = C) →
      Subscheme.ofClosed ((Subscheme.strictTransform t W).inter
          (Subscheme.strictTransform t E)).support =
        Subscheme.unionFam (fun j : Fin m => Subscheme.inducedPreimage t W (Fc j.succ)) ∨
      Subscheme.ofClosed ((Subscheme.strictTransform t W).inter
          (Subscheme.strictTransform t E)).support =
        Subscheme.unionFam (fun j : Fin (m + 1) => Subscheme.inducedPreimage t W (Fc j))) ∧
    -- the iteration `F ↦ F' ↦ F'' ↦ ⋯` ends after a finite number of steps:
    (∀ g : ℕ → IterationStage.{u}, IterationStage.IsIteration g → g 0 = ⟨X, W, E, F⟩ →
      ∃ i, ¬ (g i).F.IsContainedIn ((g i).W.inter (g i).E)) := by
  obtain ⟨e, he⟩ := Subscheme.exists_iso_strictTransform_of_mem_irreducibleComponents hXalg
    hXns W hWns hWirr E hE hEW F hF hFns t
  refine ⟨⟨e, he⟩, ?_, ?_⟩
  · intro m Fc h0 hinj hcomp hcover
    exact t.ofClosed_support_inter_eq_unionFam_inducedPreimage_or hXns hFns W hWns hWirr E hE hEW
      hF e he m Fc h0 hinj hcomp hcover
  · intro g hg h0
    exact exists_not_isContainedIn_of_isIteration hXalg hXns W hWns hWirr E hE hEW F hF hFns g hg
      h0

section PrepPresentation

open IsLocalRing Classical

variable {X : Scheme.{u}} {B : Subscheme X}

/-- `⋂_{i < n+1} f i = (⋂_{i < n} f i) ∩ f n` in a complete lattice. -/
theorem iInf_fin_snoc {L : Type*} [CompleteLattice L] {n : ℕ} (f : Fin (n + 1) → L) :
    ⨅ i, f i = (⨅ i : Fin n, f i.castSucc) ⊓ f (Fin.last n) := by
  refine le_antisymm (le_inf (le_iInf fun i => iInf_le _ i.castSucc) (iInf_le _ (Fin.last n)))
    (le_iInf fun i => ?_)
  refine Fin.lastCases ?_ (fun j => ?_) i
  · exact inf_le_right
  · exact inf_le_left.trans (iInf_le _ j)

/-- The strict transform of `E_1 ∪ ⋯ ∪ E_α` is `E_1' ∪ ⋯ ∪ E_α'` when the `E_i` have normal
crossings with `B` (p. 169, Remark 1: the stalks are computed in the chart: a product of parts of
a regular system of parameters has as strict transform the product of the images of those factors
that are not the center's parameter).

Deviation from the paper (gap filled): the paper writes the boundary of `f*(ℜ)` as the union of the
strict transforms of the `E_i` and the exceptional divisors (Definition 7 and p. 290) without
proving that the strict transform of the union is the union of the strict transforms. -/
theorem DatumTransform.strictTransform_iInf_eq (hX : X.IsNonsingular) (hBns : B.IsNonsingular)
    (t : MonoidalTransformation X B) {ι : Type*} [Fintype ι] (E : ι → Subscheme X)
    (hdata : ∀ x, ∃ Z : Finset (X.presheaf.stalk x), IsRegularSystemOfParameters _ Z ∧
      (x ∈ B.pts → ∃ T ⊆ Z, B.stalkIdeal x = Ideal.span (T : Set _)) ∧
      ∀ i, (E i).stalkIdeal x = ⊤ ∨ ∃ a ∈ Z, (E i).stalkIdeal x = Ideal.span {a}) :
    Subscheme.strictTransform t (⨅ i, E i) = ⨅ i, Subscheme.strictTransform t (E i) := by
  apply Subscheme.ext_stalkIdeal
  intro y
  have : IsRegularLocalRing (X.presheaf.stalk (t.f y)) := hX _
  have : IsRegularLocalRing (t.X'.presheaf.stalk y) := t.isRegularLocalRing_stalk hX hBns y
  rw [DatumTransform.stalkIdeal_iInf_fintype (E := fun i => Subscheme.strictTransform t (E i))]
  obtain ⟨Z, hZ, hBZ, hEZ⟩ := hdata (t.f y)
  have hJ : ∀ i, ∃ J : Finset (X.presheaf.stalk (t.f y)), J ⊆ Z ∧
      (E i).stalkIdeal (t.f y) = Ideal.span {∏ z ∈ J, z} := by
    intro i
    rcases hEZ i with h | ⟨a, ha, h⟩
    · exact ⟨∅, Finset.empty_subset _, by rw [h, Finset.prod_empty, Ideal.span_singleton_one]⟩
    · exact ⟨{a}, Finset.singleton_subset_iff.mpr ha, by rw [h, Finset.prod_singleton]⟩
  choose J hJZ hJe using hJ
  set Jall := Finset.univ.biUnion J with hJall
  have hJallZ : Jall ⊆ Z := Finset.biUnion_subset.mpr fun i _ => hJZ i
  have hUnion : (⨅ i, E i).stalkIdeal (t.f y) = Ideal.span {∏ z ∈ Jall, z} := by
    rw [DatumTransform.stalkIdeal_iInf_fintype]
    simp_rw [hJe]
    exact DatumTransform.iInf_span_prod_of_subset
      (ExtendsToRSOP.of_isRegularSystemOfParameters hZ) J hJZ
  by_cases hy : t.f y ∈ B.pts
  · obtain ⟨T, hTZ, hT⟩ := hBZ hy
    obtain ⟨zt, φ, hzt, hexc, hztm, hinj, hext, hst⟩ :=
      DatumTransform.exists_chart hX t y hZ hTZ hT
    rw [hst Jall hJallZ _ hUnion]
    have hR : ∀ i, (Subscheme.strictTransform t (E i)).stalkIdeal y = Ideal.span
        {∏ z ∈ ((J i).erase zt).filter (fun z => φ z ∈ maximalIdeal (t.X'.presheaf.stalk y)),
          φ z} := fun i => hst (J i) (hJZ i) (E i) (hJe i)
    simp_rw [hR]
    set m := maximalIdeal (t.X'.presheaf.stalk y) with hm
    have hprod : ∀ s : Finset (X.presheaf.stalk (t.f y)),
        (∀ z ∈ s, z ∈ Z ∧ φ z ∈ m) → ∏ z ∈ s, φ z = ∏ w ∈ s.image φ, w := fun s hs =>
      DatumTransform.prod_image_eq φ hinj s fun z hz => hs z hz
    set L : ι → Finset (t.X'.presheaf.stalk y) := fun i =>
      (((J i).erase zt).filter (fun z => φ z ∈ m)).image φ with hL
    have hLK : ∀ i, L i ⊆ (Z.filter fun z => φ z ∈ m).image φ := fun i =>
      Finset.image_subset_image (Finset.filter_subset_filter _
        ((Finset.erase_subset _ _).trans (hJZ i)))
    have hmem : ∀ i, ∀ z ∈ ((J i).erase zt).filter (fun z => φ z ∈ m), z ∈ Z ∧ φ z ∈ m :=
      fun i z hz => by
        obtain ⟨hz1, hz2⟩ := Finset.mem_filter.mp hz
        exact ⟨hJZ i (Finset.mem_of_mem_erase hz1), hz2⟩
    have h1 : ∀ i, Ideal.span {∏ z ∈ ((J i).erase zt).filter (fun z => φ z ∈ m), φ z} =
        Ideal.span {∏ w ∈ L i, w} := fun i => by rw [hprod _ (hmem i)]
    simp_rw [h1]
    rw [DatumTransform.iInf_span_prod_of_subset hext L hLK]
    have h2 : ((Jall.erase zt).filter (fun z => φ z ∈ m)).image φ = Finset.univ.biUnion L := by
      ext w
      simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_erase, Finset.mem_biUnion,
        Finset.mem_univ, true_and, hL, hJall]
      constructor
      · rintro ⟨z, ⟨⟨hz1, i, hzi⟩, hz2⟩, rfl⟩
        exact ⟨i, z, ⟨⟨hz1, hzi⟩, hz2⟩, rfl⟩
      · rintro ⟨i, z, ⟨⟨hz1, hzi⟩, hz2⟩, rfl⟩
        exact ⟨z, ⟨⟨hz1, i, hzi⟩, hz2⟩, rfl⟩
    rw [hprod _ (fun z hz => by
      obtain ⟨hz1, hz2⟩ := Finset.mem_filter.mp hz
      exact ⟨hJallZ (Finset.mem_of_mem_erase hz1), hz2⟩), h2]
  · obtain ⟨e, -, he⟩ := DatumTransform.exists_offCenter hX t y hy
    have key : ∀ I : Ideal (X.presheaf.stalk (t.f y)), Ideal.map e I = Ideal.comap e.symm I :=
      fun I => by rw [← Ideal.map_coe e]; exact Ideal.map_comap_of_equiv e
    rw [he]
    simp_rw [he, key]
    rw [DatumTransform.stalkIdeal_iInf_fintype, Ideal.comap_iInf]

/-- The presentation of the transformed boundary (Definition 7, p. 168, type I): if
`ℜ.E = E_1 ∪ ⋯ ∪ E_α` with the `E_i` non-singular irreducible of codimension one, then
`(f*ℜ).E = E_1' ∪ ⋯ ∪ E_α' ∪ E_{α+1}'` with `E_i'` the strict transforms and `E_{α+1}' = f⁻¹(B)`
the exceptional divisor, again non-singular irreducible of codimension one (the `Fin.snoc` of the
strict transforms and the exceptional divisor).

Deviation from the paper (gap filled): the convention that `f*(ℜ)` is presented by the strict
transforms of the `E_i` first and the exceptional divisor last is tacit in the paper (Definition 7,
p. 168; the proof of Proposition 5, p. 290: "`f*(ℜ) = (⋃_{i=1}^{α'} E_i'; …)`"); here the
non-singularity, irreducibility and codimension one of the `E_i'` and the equality
`(f*ℜ).E = ⋃ E_i'` are proved, reusing the stalk computation of Remark 1. -/
theorem DatumI.Raw.exists_presentation_transform [IsAlgebraicScheme X] (hX : X.IsNonsingular)
    {α : ℕ} (E : Fin α → Subscheme X) (hE : ∀ i, (E i).IsNonsingularIrreducibleCodimOne)
    (ℜ : DatumI.Raw X) (hℜ : ℜ.IsDatum) (hEunion : ℜ.E = Subscheme.unionFam E)
    (t : MonoidalTransformation X B) (hB : ℜ.IsPermissible B) :
    ∃ E' : Fin (α + 1) → Subscheme t.X', (∀ i, (E' i).IsNonsingularIrreducibleCodimOne) ∧
      (ℜ.transform t).E = Subscheme.unionFam E' ∧
      (∀ i : Fin α, E' i.castSucc = Subscheme.strictTransform t (E i)) ∧
      E' (Fin.last α) = t.exceptional := by
  have hBns := hB.1.isNonsingular
  have hX' := (t.isNonsingular_and_isNonsingular_exceptional hX hBns).1
  have hNC : (⨅ i, E i).HasOnlyNormalCrossings := by
    have := hℜ.2.2.1; rw [hEunion] at this; exact this
  have hNCB : (⨅ i, E i).HasOnlyNormalCrossingsWith B := fun x hx => by
    have := (hB.2.2 x hx).2.2
    change ℜ.E.HasOnlyNormalCrossingsWithAt B x at this
    rw [hEunion] at this; exact this
  have hdata := DatumTransform.exists_rsop_adapted_of_isDatum E hX hE hNC hNCB
  have hmem : ∀ y, ∃ K : Finset (t.X'.presheaf.stalk y), ExtendsToRSOP _ K ∧
      (∃ K₀ ⊆ K, K₀.card ≤ 1 ∧ t.exceptional.stalkIdeal y = Ideal.span {∏ k ∈ K₀, k}) ∧
      ∀ i, ∃ K₀ ⊆ K, K₀.card ≤ 1 ∧
        (Subscheme.strictTransform t (E i)).stalkIdeal y = Ideal.span {∏ k ∈ K₀, k} := fun y =>
    DatumTransform.exists_extendsToRSOP_stalkIdeal_family hX hBns t E hdata y
  refine ⟨Fin.snoc (α := fun _ => Subscheme t.X')
    (fun i => Subscheme.strictTransform t (E i)) t.exceptional, fun i => ?_, ?_,
    fun i => Fin.snoc_castSucc (α := fun _ => Subscheme t.X') _ _ i,
    Fin.snoc_last (α := fun _ => Subscheme t.X') _ _⟩
  · apply DatumTransform.isNonsingularIrreducibleCodimOne_of_forall_stalk hX'
    · refine Fin.lastCases ?_ (fun j => ?_) i
      · simp only [Fin.snoc_last]
        intro hne
        rcases hB.1 with hBe | ⟨-, hBirr⟩
        · exfalso
          obtain ⟨y, hy⟩ := hne
          have h3 : B.pts = ∅ := by rw [hBe]; exact DatumTransform.pts_empty
          rw [MonoidalTransformation.pts_exceptional] at hy
          have h4 : t.f y ∈ B.pts := hy
          rw [h3] at h4
          exact h4
        · exact DatumTransform.exceptional_isIrreducible hX hBns hBirr t hne
      · simp only [Fin.snoc_castSucc]
        exact DatumTransform.strictTransform_isIrreducible_of_nonempty t (hE j)
    · intro y
      obtain ⟨K, hK, hexc, hst⟩ := hmem y
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simp only [Fin.snoc_last]
        obtain ⟨K₀, h1, h2, h3⟩ := hexc
        exact DatumTransform.stalkIdeal_eq_top_or_exists_of_card_le_one hK h1 h2 h3
      · simp only [Fin.snoc_castSucc]
        obtain ⟨K₀, h1, h2, h3⟩ := hst j
        exact DatumTransform.stalkIdeal_eq_top_or_exists_of_card_le_one hK h1 h2 h3
  · have hst := DatumTransform.strictTransform_iInf_eq hX hBns t E hdata
    change (Subscheme.strictTransform t ℜ.E).union t.exceptional = Subscheme.unionFam _
    rw [hEunion]
    have hu : ∀ F : Fin (α + 1) → Subscheme t.X', Subscheme.unionFam F = ⨅ i, F i := fun F => rfl
    have hE' : Subscheme.unionFam E = ⨅ i, E i := rfl
    rw [hu, Subscheme.union, hE', hst, iInf_fin_snoc]
    simp only [Fin.snoc_castSucc, Fin.snoc_last]

/-- The presentation of the transformed boundary along a permissible succession: the boundary of
`s.transformI ℜ` is `E_1' ∪ ⋯ ∪ E_{α'}'` with non-singular irreducible `E_i'` of codimension one,
the first `α` of which are the strict transforms of `E_1, …, E_α` along `s` (the others being the
strict transforms of the exceptional divisors of the successive steps); in particular `E_1'` is
the strict transform of `E_1`.

Deviation from the paper (gap filled): the paper writes `f*(ℜ) = (⋃_{i=1}^{α'} E_i'; …)` with the
strict transforms of the `E_i` first and the exceptional divisors last, without comment (p. 168
and the proof of Proposition 5, p. 290); this is proved here, by induction on the succession. -/
theorem MonoidalSuccession.exists_presentation_transformI [Hironaka.Cited.MonoidalTransformationExistsIsProper.{u}] {X Y : Scheme.{u}}
    (s : MonoidalSuccession X Y) (hXa : IsAlgebraicScheme X) (hX : X.IsNonsingular)
    {α : ℕ} (E : Fin α → Subscheme X) (hE : ∀ i, (E i).IsNonsingularIrreducibleCodimOne)
    (ℜ : DatumI.Raw X) (hℜ : ℜ.IsDatum) (hEunion : ℜ.E = Subscheme.unionFam E)
    (hs : s.IsPermissibleI ℜ) :
    ∃ (α' : ℕ) (h : α ≤ α') (E' : Fin α' → Subscheme Y),
      (∀ i, (E' i).IsNonsingularIrreducibleCodimOne) ∧
      (s.transformI ℜ).E = Subscheme.unionFam E' ∧
      ∀ i : Fin α, E' (Fin.castLE h i) = s.strictTransform (E i) := by
  induction s generalizing α with
  | nil X => exact ⟨α, le_rfl, E, hE, hEunion, fun i => rfl⟩
  | cons B t rest ih =>
    obtain ⟨E₁, hE₁, hEq₁, hcs, -⟩ :=
      @DatumI.Raw.exists_presentation_transform _ _ hXa hX α E hE ℜ hℜ hEunion t hs.1
    have hdat := (DatumI.Raw.transform_isDatum (X := _) hX ℜ hℜ t hs.1).1
    obtain ⟨α', h', E', hE', hEq', hcs'⟩ := ih t.isAlgebraicScheme
      (t.isNonsingular_and_isNonsingular_exceptional hX hs.1.1.isNonsingular).1 E₁ hE₁
      (ℜ.transform t) hdat hEq₁ hs.2
    refine ⟨α', (Nat.le_succ α).trans h', E', hE', hEq', fun i => ?_⟩
    have h1 : Fin.castLE ((Nat.le_succ α).trans h') i = Fin.castLE h' i.castSucc := Fin.ext rfl
    rw [h1, hcs' i.castSucc, hcs i]
    rfl

end PrepPresentation

section PrepPermissible

open Classical

variable {X Y : Scheme.{u}}

/-- "As is easily seen, a permissible succession of monoidal transformations of `X` for
`(ℜ̄, F ∩ U)` is such a succession for `(ℜ, U)`" (p. 289), for `ℜ̄ = ℜ.extendBy F`, `F ⊆ W`, in the
form: a succession permissible for `(ℜ.extendBy F, U₁)` with `F ∩ U ⊆ U₁` is permissible for
`(ℜ, U)`.  Each centre is permissible for `ℜ` (it is permissible for `ℜ̄`), lies in `F ⊆ W`, and
does not meet `U` (it lies in `F` and avoids `F ∩ U ⊆ U₁`).

Deviation from the paper (gap filled): "as is easily seen" is tacit; the induction along the
succession uses `transform_extendBy` and the strict transforms `F' ⊆ W'`, `F' ∩ f⁻¹U ⊆ f⁻¹U₁`. -/
theorem MonoidalSuccession.isPermissibleIOpen_of_isPermissibleIOpen_extendBy
    (s : MonoidalSuccession X Y) (ℜ : DatumI.Raw X) (F : Subscheme X) (U U₁ : Set X)
    (hs : s.IsPermissibleIOpen (ℜ.extendBy F) U₁) (hFW : F.IsContainedIn ℜ.W)
    (hFU : F.pts ∩ U ⊆ U₁) : s.IsPermissibleIOpen ℜ U := by
  induction s with
  | nil X => trivial
  | cons B t rest ih =>
    obtain ⟨⟨hC, hCW⟩, hrest⟩ := hs
    obtain ⟨hperm, hBF⟩ := DatumI.Raw.isPermissible_of_extendBy hC
    refine ⟨⟨hperm, fun y hy => ⟨pts_subset_of_isContainedIn hFW (hBF hy),
      fun hyU => (hCW hy).2 (hFU ⟨hBF hy, hyU⟩)⟩⟩, ?_⟩
    rw [DatumI.Raw.transform_extendBy] at hrest
    exact ih (ℜ.transform t) (Subscheme.strictTransform t F) (DatumI.Raw.transformOpen t U)
      (DatumI.Raw.transformOpen t U₁) hrest
      (MonoidalTransformation.isContainedIn_strictTransform t hFW)
      (fun y hy => hFU ⟨MonoidalTransformation.pts_strictTransform_subset t F hy.1, hy.2⟩)

end PrepPermissible

end

end Hironaka
