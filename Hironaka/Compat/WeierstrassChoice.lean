/-
Copyright (c) 2026 Daattavya Aggarwal, Minhyong Kim, Oisin Kim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daattavya Aggarwal, Minhyong Kim, Oisin Kim
-/
module

public import Mathlib.Algebra.MvPolynomial.Supported
public import Mathlib.LinearAlgebra.Dimension.OrzechProperty
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
public import Mathlib.RingTheory.MvPowerSeries.Equiv
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Hironaka.Compat.InitialFormPowerSeries
public import Hironaka.Compat.TauParameterLift
public import Hironaka.Compat.RSOPProducts
public import Hironaka.Compat.WeierstrassDatum
public import Hironaka.Compat.CoefficientField
public import Hironaka.Compat.TauZSystem
public import Hironaka.Compat.TauZSingleton
public import Hironaka.Compat.FrameGraded
public import Hironaka.Compat.WeierstrassCoordinates
public import Hironaka.Compat.MvPowerSeriesRegular
public import Hironaka.Compat.RSOPProducts
public import Hironaka.Statements

/-!
# The choice of `w` in Lemma 25 (pp. 269--270)

"Let us take a regular system of parameters `(z₁, …, z_r, x₁, …, x_s)` of `R` such that, if
`t = τ_{(z)}(f)`, `(x₁, …, x_t)` is a regular system of `τ_{(z)}`-parameters of `R` for `f`.  We have
a subfield `k` of `R` such that `R = k{z₁, …, z_r, x₁, …, x_s}` by the structure theorem of a
complete regular local ring (equi-characteristic) […]" (p. 269).

This file carries out the part of the proof of Lemma 25 from there to the choice of `w = x₁`
(`exists_weierstrassDatum`):

* `exists_isRegularSystemOfTauZParameters`, `exists_rsop_enumeration_tauZ`: the regular system of
  parameters `(z, x)` (the classes of `z` and `x` generate `T*`, of rank `r + t`, so they are
  independent modulo `M²`: `rsopIndep_of_linearIndependent`);
* `CohenCoordinates`: the structure theorem `R = k{z, x}` together with the identification
  `S = k{x}` of the coefficient ring of the frame, and the identification of `gr_M(R)` with the
  polynomial ring `k[Z, X]` (`InitialFormPowerSeries.lean`);
* `CohenCoordinates.exists_support_data`: the choice of `Ā` and `e` ("Since `(x₁, …, x_t)` is a
  regular system of `τ_{(z)}`-parameters of `R` for `f`, those `φ_A` are forms in `X₁, …, X_t`, and
  there exists `Ā` such that `|Ā| + ν_M(h_Ā) = ν` and that `deg φ_Ā > 0`");
* `exists_weierstrassDatum`: the linear transformation of `(x₁, …, x_t)`, the Weierstrass
  preparation theorem and the replacement of `x₁` (`exists_weierstrass_coordinates`,
  `WeierstrassCoordinates.lean`) give a new regular frame `(S₀; w)` of `S` for which
  `h_Ā = u(w^e + p₂w^{e-2} + ⋯ + p_e)`.
-/

@[expose] public section

open IsLocalRing MvPowerSeries

namespace Hironaka

universe u

section Independence

variable {R : Type u} [CommRing R] [IsLocalRing R]

/-- A family of elements of `M` whose classes in `M/M²` are linearly independent over `k = R/M` is
independent in the sense of `RSOPIndep`. -/
theorem rsopIndep_of_linearIndependent {ι : Type*} [Fintype ι] (v : ι → R)
    (hv : ∀ i, v i ∈ maximalIdeal R ^ 1)
    (hli : LinearIndependent (R ⧸ maximalIdeal R)
      (fun i => AssocGraded.mk (maximalIdeal R) 1 (v i) (hv i))) :
    RSOPIndep (Finset.univ : Finset ι) v := by
  classical
  intro z _
  refine ⟨by simpa using hv z, fun hmem => ?_⟩
  set g : ι → AssocGraded (maximalIdeal R) :=
    fun i => AssocGraded.mk (maximalIdeal R) 1 (v i) (hv i) with hg
  set L : Submodule (R ⧸ maximalIdeal R) (AssocGraded (maximalIdeal R)) :=
    Submodule.span (R ⧸ maximalIdeal R) (g '' {j | j ≠ z}) with hL
  have key : ∀ b ∈ Ideal.span (v '' (((Finset.univ : Finset ι) : Set ι) \ {z})),
      ∃ h : b ∈ maximalIdeal R ^ 1, AssocGraded.mk (maximalIdeal R) 1 b h ∈ L := by
    intro b hb
    refine Submodule.span_induction (p := fun b _ => ∃ h : b ∈ maximalIdeal R ^ 1,
      AssocGraded.mk (maximalIdeal R) 1 b h ∈ L) ?_ ?_ ?_ ?_ hb
    · rintro _ ⟨j, hj, rfl⟩
      refine ⟨hv j, Submodule.subset_span ⟨j, ?_, rfl⟩⟩
      simpa using hj
    · refine ⟨zero_mem _, ?_⟩
      have : AssocGraded.mk (maximalIdeal R) 1 (0 : R) (zero_mem _) = 0 :=
        map_zero (AssocGraded.mkLinear (maximalIdeal R) 1)
      rw [this]
      exact zero_mem _
    · rintro a b - - ⟨ha, ha'⟩ ⟨hb, hb'⟩
      refine ⟨add_mem ha hb, ?_⟩
      rw [AssocGraded.mk_add (maximalIdeal R) 1 a b ha hb]
      exact add_mem ha' hb'
    · rintro s a - ⟨ha, ha'⟩
      refine ⟨Ideal.mul_mem_left _ s ha, ?_⟩
      have := AssocGraded.smul_mk (maximalIdeal R) 1 s a ha
      show AssocGraded.mk (maximalIdeal R) 1 (s * a) (Ideal.mul_mem_left _ s ha) ∈ L
      rw [← this]
      exact L.smul_mem _ ha'
  have h1 : v z ∈ Ideal.span (v '' (((Finset.univ : Finset ι) : Set ι) \ {z})) ⊔
      maximalIdeal R ^ 2 := hmem
  obtain ⟨b, hb, c, hc, hbc⟩ := Submodule.mem_sup.mp h1
  obtain ⟨hbM, hbL⟩ := key b hb
  have hvz : v z ∈ maximalIdeal R ^ 1 := hv z
  have hdiff : v z - b ∈ maximalIdeal R ^ (1 + 1) := by
    rw [← hbc]
    simpa using hc
  have heq := AssocGraded.mk_eq_mk_of_sub_mem_pow_succ (maximalIdeal R) 1 hvz hbM hdiff
  have : g z ∈ L := by
    show AssocGraded.mk (maximalIdeal R) 1 (v z) (hv z) ∈ L
    rw [heq]
    exact hbL
  exact hli.notMem_span_image (s := {j | j ≠ z}) (by simp) this

end Independence

section Coordinates

variable {R : Type u} [CommRing R] [IsRegularLocalRing R] {r : ℕ}

open Classical in
/-- **A regular system of `τ_{(z)}`-parameters exists** (Definition 10*, p. 251) when `τ_{(z)}(f) ≥ 1`:
pick a vector of `T*` outside `⟨Z₁, …, Z_r⟩` (the rank of `T*` is `r + τ`) and apply
`exists_isRegularSystemOfTauZParameters_of_mem`. -/
theorem exists_isRegularSystemOfTauZParameters {z : Fin r → R} (hinj : Function.Injective z)
    (hz : ExtendsToRSOP R (Finset.image z Finset.univ)) {f : R}
    (hτ : 1 ≤ tauZ R z (fun _ : Fin 1 => f)) :
    ∃ x : Fin (tauZ R z (fun _ : Fin 1 => f)) → maximalIdeal R,
      IsRegularSystemOfTauZParameters R z (fun _ : Fin 1 => f) x := by
  let _ : Field (R ⧸ maximalIdeal R) := Ideal.Quotient.field _
  obtain ⟨hli, hord⟩ := linearIndependent_frameForm hinj hz
  have hfin := finite_tauZSubmoduleStar (f := fun _ : Fin 1 => f) hord
  have hZU : Submodule.span (R ⧸ maximalIdeal R) (Set.range (frameForm z)) ≤
      tauZSubmoduleStar R z (fun _ : Fin 1 => f) := le_sup_right
  have hnot : ¬ tauZSubmoduleStar R z (fun _ : Fin 1 => f) ≤
      Submodule.span (R ⧸ maximalIdeal R) (Set.range (frameForm z)) := by
    intro hle
    have h1 := finrank_tauZSubmoduleStar_eq hinj hz (fun _ : Fin 1 => f)
    have h2 : Module.finrank (R ⧸ maximalIdeal R) (tauZSubmoduleStar R z (fun _ : Fin 1 => f)) =
        r := by
      rw [le_antisymm hle hZU, finrank_span_eq_card hli, Fintype.card_fin]
    omega
  obtain ⟨v, hvT, hvZ⟩ := IsConcreteLE.not_le_iff_exists.mp hnot
  have hU : tauZSubmoduleStar R z (fun _ : Fin 1 => f) ≤ classSubmodule (maximalIdeal R) :=
    (tauZSubmoduleStar_le_homogeneous_one hord).trans
      homogeneous_one_le_classSubmodule_maximalIdeal
  obtain ⟨w, hw, hw𝔞, rfl⟩ := exists_lift_of_mem_classSubmodule (hU hvT)
  obtain ⟨x, hx, -, -⟩ := exists_isRegularSystemOfTauZParameters_of_mem hinj hz hU hw𝔞 hw hvT hvZ
  exact ⟨x, hx⟩

end Coordinates

section Enumeration

variable {R : Type u} [CommRing R] [IsRegularLocalRing R] {r : ℕ}

open Classical in
/-- Auxiliary form of `exists_rsop_enumeration_tauZ`: `x` is given as a family indexed by `Fin t`,
generating `T*` together with the `Z_j`, with `t = τ_{(z)}(f)`. -/
theorem exists_rsop_enumeration_aux {z : Fin r → R} (hinj : Function.Injective z)
    (hz : ExtendsToRSOP R (Finset.image z Finset.univ)) {f : R} {t : ℕ}
    (ht : tauZ R z (fun _ : Fin 1 => f) = t) (x : Fin t → maximalIdeal R)
    (hx : Submodule.span (R ⧸ maximalIdeal R)
      (Set.range (linearForms R x) ∪ Set.range (frameForm z)) =
        tauZSubmoduleStar R z (fun _ : Fin 1 => f)) :
    ∃ (m : ℕ) (hm : t ≤ m) (Y : Fin (r + m) → R),
      Function.Injective Y ∧ (∀ j, Y (Fin.castAdd m j) = z j) ∧
      IsRegularSystemOfParameters R (Finset.univ.image Y) ∧
      ∀ i, (x i : R) = Y (Fin.natAdd r (Fin.castLE hm i)) := by
  let _ : Field (R ⧸ maximalIdeal R) := Ideal.Quotient.field _
  obtain ⟨hli, hord⟩ := linearIndependent_frameForm hinj hz
  set z' : Fin (r + t) → R := Fin.append z (fun i => (x i : R)) with hz'
  have hzM : ∀ j, z j ∈ maximalIdeal R ^ 1 := fun j => Ideal.mem_pow_of_ordElem (hord j)
  have hxM : ∀ i, (x i : R) ∈ maximalIdeal R ^ 1 := fun i => by
    rw [pow_one]; exact (x i).2
  have hz'M : ∀ i, z' i ∈ maximalIdeal R ^ 1 := fun i => by
    induction i using Fin.addCases with
    | left j => rw [hz', Fin.append_left]; exact hzM j
    | right i => rw [hz', Fin.append_right]; exact hxM i
  -- the classes of `(z, x)` are the generators of `T*`
  have hfam : (fun i => AssocGraded.mk (maximalIdeal R) 1 (z' i) (hz'M i)) =
      Fin.append (frameForm z) (linearForms R x) := by
    funext i
    induction i using Fin.addCases with
    | left j =>
      rw [Fin.append_left, frameForm, initialForm_eq_mk _ (hord j)]
      exact mk_congr_of_eq _ rfl (by rw [hz', Fin.append_left]) _ _
    | right i =>
      rw [Fin.append_right]
      exact mk_congr_of_eq _ rfl (by rw [hz', Fin.append_right]) _ _
  have hrange : Set.range (Fin.append (frameForm z) (linearForms R x)) =
      Set.range (linearForms R x) ∪ Set.range (frameForm z) := by
    ext v
    simp only [Set.mem_range, Set.mem_union]
    constructor
    · rintro ⟨i, rfl⟩
      induction i using Fin.addCases with
      | left j => exact Or.inr ⟨j, by rw [Fin.append_left]⟩
      | right i => exact Or.inl ⟨i, by rw [Fin.append_right]⟩
    · rintro (⟨i, rfl⟩ | ⟨j, rfl⟩)
      · exact ⟨Fin.natAdd r i, by rw [Fin.append_right]⟩
      · exact ⟨Fin.castAdd t j, by rw [Fin.append_left]⟩
  have hlin : LinearIndependent (R ⧸ maximalIdeal R)
      (fun i => AssocGraded.mk (maximalIdeal R) 1 (z' i) (hz'M i)) := by
    rw [hfam, linearIndependent_iff_card_eq_finrank_span, Fintype.card_fin, Set.finrank,
      hrange]
    have h1 := finrank_tauZSubmoduleStar_eq hinj hz (fun _ : Fin 1 => f)
    rw [hx, h1, ht]
    omega
  have hind := rsopIndep_of_linearIndependent z' hz'M hlin
  obtain ⟨hinj', hext⟩ := hind.injOn_and_extends
  have hz'inj : Function.Injective z' := fun a b h =>
    hinj' (Finset.mem_coe.mpr (Finset.mem_univ a)) (Finset.mem_coe.mpr (Finset.mem_univ b)) h
  obtain ⟨s, hts, hs⟩ := hext
  obtain ⟨m', X, hXinj, hXz, himg, -⟩ := exists_injective_append_enumeration hz'inj hts
  refine ⟨t + m', Nat.le_add_right t m', fun i => X (Fin.cast (Nat.add_assoc r t m').symm i),
    ?_, ?_, ?_, ?_⟩
  · intro a b hab
    exact Fin.cast_injective _ (hXinj hab)
  · intro j
    have : Fin.cast (Nat.add_assoc r t m').symm (Fin.castAdd (t + m') j) =
        Fin.castAdd m' (Fin.castAdd t j) := Fin.ext rfl
    simp only [this, hXz, hz', Fin.append_left]
  · have : Finset.univ.image (fun i => X (Fin.cast (Nat.add_assoc r t m').symm i)) =
        Finset.univ.image X := by
      ext y
      simp only [Finset.mem_image, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨i, rfl⟩; exact ⟨_, rfl⟩
      · rintro ⟨i, rfl⟩
        exact ⟨Fin.cast (Nat.add_assoc r t m') i, by simp⟩
    rw [this, himg]
    exact hs
  · intro i
    have : Fin.cast (Nat.add_assoc r t m').symm
        (Fin.natAdd r (Fin.castLE (Nat.le_add_right t m') i)) =
        Fin.castAdd m' (Fin.natAdd r i) := Fin.ext rfl
    simp only [this, hXz, hz', Fin.append_right]

open Classical in
/-- **The regular system of parameters of the proof of Lemma 25** (p. 269): "Let us take a regular
system of parameters `(z₁, …, z_r, x₁, …, x_s)` of `R` such that, if `t = τ_{(z)}(f)`,
`(x₁, …, x_t)` is a regular system of `τ_{(z)}`-parameters of `R` for `f`."  Here the whole system
is enumerated as `Y : Fin (r + m) → R` with `Y_j = z_j` and `Y_{r + i} = x_i` for `i < t ≤ m`.
(`(z, x)` is independent modulo `M²` because the classes of `z` and `x` generate `T*`, of rank
`r + t`; so it can be extended to a regular system of parameters.) -/
theorem exists_rsop_enumeration_tauZ {z : Fin r → R} (hinj : Function.Injective z)
    (hz : ExtendsToRSOP R (Finset.image z Finset.univ)) {f : R}
    (hτ : 1 ≤ tauZ R z (fun _ : Fin 1 => f)) :
    ∃ (m : ℕ) (hm : tauZ R z (fun _ : Fin 1 => f) ≤ m) (Y : Fin (r + m) → R)
      (x : Fin (tauZ R z (fun _ : Fin 1 => f)) → maximalIdeal R),
      Function.Injective Y ∧ (∀ j, Y (Fin.castAdd m j) = z j) ∧
      IsRegularSystemOfParameters R (Finset.univ.image Y) ∧
      IsRegularSystemOfTauZParameters R z (fun _ : Fin 1 => f) x ∧
      ∀ i, (x i : R) = Y (Fin.natAdd r (Fin.castLE hm i)) := by
  obtain ⟨x, hx⟩ := exists_isRegularSystemOfTauZParameters hinj hz hτ
  obtain ⟨m, hm, Y, h1, h2, h3, h4⟩ := exists_rsop_enumeration_aux hinj hz rfl x hx
  exact ⟨m, hm, Y, x, h1, h2, h3, hx, h4⟩

end Enumeration

section Slice

variable {K : Type*} [CommRing K] {r m : ℕ}


theorem mapDomain_castAdd_apply_castAdd (C : Fin r →₀ ℕ) (j : Fin r) :
    Finsupp.mapDomain (Fin.castAdd m) C (Fin.castAdd m j) = C j :=
  Finsupp.mapDomain_apply_of_injective (Fin.castAdd_injective r m) C j

theorem mapDomain_castAdd_apply_natAdd (C : Fin r →₀ ℕ) (i : Fin m) :
    Finsupp.mapDomain (Fin.castAdd m) C (Fin.natAdd r i) = 0 :=
  Finsupp.mapDomain_of_notMem_range C _ (by
    rintro ⟨j, hj⟩
    have := congrArg Fin.val hj
    simp at this
    omega)

theorem mapDomain_natAdd_apply_castAdd (C : Fin m →₀ ℕ) (j : Fin r) :
    Finsupp.mapDomain (Fin.natAdd r) C (Fin.castAdd m j) = 0 :=
  Finsupp.mapDomain_of_notMem_range C _ (by
    rintro ⟨i, hi⟩
    have := congrArg Fin.val hi
    simp at this
    omega)

theorem mapDomain_natAdd_apply_natAdd (C : Fin m →₀ ℕ) (i : Fin m) :
    Finsupp.mapDomain (Fin.natAdd r) C (Fin.natAdd r i) = C i :=
  Finsupp.mapDomain_apply_of_injective (Fin.natAdd_injective m r) C i

/-- The coefficient of a "slice": for `p ∈ K[Y₁, …, Y_m]` and monomials `Z^A` in extra variables
`Z₁, …, Z_r` (placed first), the coefficient of `Z^{A'} Y^B` in `p(Y) Z^A` is `δ_{A,A'}` times the
coefficient of `Y^B` in `p`. -/
theorem coeff_rename_natAdd_mul_monomial_castAdd (p : MvPolynomial (Fin m) K)
    (A A' : Fin r →₀ ℕ) (B : Fin m →₀ ℕ) :
    (MvPolynomial.rename (Fin.natAdd r) p *
        MvPolynomial.monomial (Finsupp.mapDomain (Fin.castAdd m) A) 1).coeff
        (Finsupp.mapDomain (Fin.castAdd m) A' + Finsupp.mapDomain (Fin.natAdd r) B) =
      if A' = A then p.coeff B else 0 := by
  classical
  rw [MvPolynomial.coeff_mul_monomial']
  have hcast := mapDomain_castAdd_apply_castAdd (r := r) (m := m)
  have hnat := mapDomain_natAdd_apply_castAdd (r := r) (m := m)
  by_cases hA : A' = A
  · subst hA
    have hle : Finsupp.mapDomain (Fin.castAdd m) A' ≤
        Finsupp.mapDomain (Fin.castAdd m) A' + Finsupp.mapDomain (Fin.natAdd r) B := le_self_add
    simp only [hle, ↓reduceIte, add_tsub_cancel_left, mul_one]
    exact MvPolynomial.coeff_rename_mapDomain _ (Fin.natAdd_injective m r) _ _
  · simp only [hA, ↓reduceIte]
    split_ifs with hle
    · rw [mul_one]
      refine MvPolynomial.coeff_rename_eq_zero (Fin.natAdd r) p _ fun u hu => ?_
      exfalso
      -- `A ≤ A'` and `A ≠ A'`, so some `A j < A' j`
      have hle' : ∀ j, A j ≤ A' j := fun j => by
        have := hle (Fin.castAdd m j)
        rwa [hcast, Finsupp.add_apply, hcast, hnat, add_zero] at this
      obtain ⟨j, hj⟩ : ∃ j, A j ≠ A' j := by
        by_contra hall
        push Not at hall
        exact hA (Finsupp.ext fun j => (hall j).symm)
      have hlt : A j < A' j := lt_of_le_of_ne (hle' j) hj
      have := congrArg (fun d => d (Fin.castAdd m j)) hu
      simp only [hnat, Finsupp.tsub_apply, Finsupp.add_apply, hcast] at this
      omega
    · rfl

end Slice

section CohenCoordinates

variable {R : Type u} [CommRing R] [IsRegularLocalRing R]

/-- **Cohen coordinates adapted to a regular frame** (p. 269): "We have a subfield `k` of `R` such
that `R = k{z₁, …, z_r, x₁, …, x_s}` by the structure theorem of a complete regular local ring
(equi-characteristic)", `S = k{x₁, …, x_s}`.  The data: a regular system of parameters
`Y = (z₁, …, z_r, x₁, …, x_{n+1})`, a coefficient field `σ`, the isomorphism
`Φ : R ≃ k{Y₁, …, Y_{r+n+1}}` (order preserving, `Y_i ↦ Y_i`, `σ(c) ↦ c`), and the identification
`ET` of the coefficient ring `S` of the frame with `k{x₁, …, x_{n+1}}`. -/
structure CohenCoordinates (F : RegularFrame R) (n : ℕ) where
  /-- The regular system of parameters `(z₁, …, z_r, x₁, …, x_{n+1})`. -/
  Y : Fin (F.r + (n + 1)) → R
  span_Y : Ideal.span (Set.range Y) = maximalIdeal R
  dim_Y : ((F.r + (n + 1) : ℕ) : WithBot ℕ∞) = ringKrullDim R
  /-- The coefficient field. -/
  σ : R ⧸ maximalIdeal R →+* R
  residue_comp_σ : (Ideal.Quotient.mk (maximalIdeal R)).comp σ = RingHom.id _
  /-- The structure theorem `R ≃ k{Y}`. -/
  Φ : R ≃+* MvPowerSeries (Fin (F.r + (n + 1))) (R ⧸ maximalIdeal R)
  Φ_Y : ∀ i, Φ (Y i) = MvPowerSeries.X i
  Φ_σ : ∀ c, Φ (σ c) = MvPowerSeries.C c
  order_Φ : ∀ a, (Φ a).order = Ideal.ordElem (maximalIdeal R) a
  Y_castAdd : ∀ j, Y (Fin.castAdd (n + 1) j) = F.z j
  /-- `S ≃ k{x}`. -/
  ET : F.S ≃+* MvPowerSeries (Fin (n + 1)) (R ⧸ maximalIdeal R)
  Φ_algebraMap : ∀ s, Φ (algebraMap F.S R s) = MvPowerSeries.rename (Fin.natAdd F.r) (ET s)

namespace CohenCoordinates

variable {F : RegularFrame R} {n : ℕ} (C : CohenCoordinates F n)

theorem Y_mem (i : Fin (F.r + (n + 1))) : C.Y i ∈ maximalIdeal R ^ 1 := by
  rw [pow_one, ← C.span_Y]
  exact Ideal.subset_span ⟨i, rfl⟩

/-- The graded polynomial map `k[Y] → gr_M(R)`, `Y_i ↦ [Y_i]` (p. 269--270: "`gr_M(R)` can be
identified with the polynomial ring `k[Z₁, …, Z_r, X₁, …, X_s]`"). -/
noncomputable def toGraded : MvPolynomial (Fin (F.r + (n + 1))) (R ⧸ maximalIdeal R) →ₐ[R ⧸ maximalIdeal R]
    AssocGraded (maximalIdeal R) :=
  MvPolynomial.aeval fun i => AssocGraded.mk (maximalIdeal R) 1 (C.Y i) (C.Y_mem i)

theorem toGraded_bijective : Function.Bijective C.toGraded := by
  exact assocGraded_maximalIdeal_aeval_bijective C.span_Y C.dim_Y C.Y_mem

/-- The class of `a ∈ Mᵏ` in `grᵏ_M(R)` is the value at `[Y]` of the homogeneous component of
degree `k` of `Φ(a)`. -/
theorem mk_eq {k : ℕ} {a : R} (ha : a ∈ maximalIdeal R ^ k) :
    AssocGraded.mk (maximalIdeal R) k a ha = C.toGraded (homogPart k (C.Φ a)) :=
  mk_eq_aeval_homogPart C.Y C.Y_mem C.σ C.residue_comp_σ C.Φ C.Φ_Y C.Φ_σ C.order_Φ ha

theorem toGraded_X (i : Fin (F.r + (n + 1))) :
    C.toGraded (MvPolynomial.X i) = AssocGraded.mk (maximalIdeal R) 1 (C.Y i) (C.Y_mem i) := by
  rw [toGraded, MvPolynomial.aeval_X]

/-- `Z_j` is the image of the variable `Y_j`. -/
theorem frameForm_eq (j : Fin F.r) :
    frameForm F.z j = C.toGraded (MvPolynomial.X (Fin.castAdd (n + 1) j)) := by
  have hz : F.z j ∈ maximalIdeal R ^ 1 := by rw [← C.Y_castAdd j]; exact C.Y_mem _
  rw [F.frameForm_eq_mk_one j hz, C.toGraded_X]
  exact mk_congr_of_eq _ rfl (C.Y_castAdd j).symm _ _

/-- `Z^A` is the image of the monomial `Y^A` in the first `r` variables. -/
theorem toGraded_monomial_castAdd (A : Fin F.r →₀ ℕ) :
    C.toGraded (MvPolynomial.monomial (Finsupp.mapDomain (Fin.castAdd (n + 1)) A) 1) =
      ∏ i, frameForm F.z i ^ A i := by
  classical
  rw [toGraded, MvPolynomial.aeval_monomial, map_one, one_mul,
    Finsupp.prod_mapDomain_index_inj (Fin.castAdd_injective _ _),
    Finsupp.prod_fintype _ _ (fun i => pow_zero _)]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [C.frameForm_eq i, toGraded, MvPolynomial.aeval_X]

/-- The map `gr_N(S) → gr_M(R)` on a class `[c]_k`, through the coordinates. -/
theorem grMap_eq {k : ℕ} {c : F.S} (hc : c ∈ maximalIdeal F.S ^ k) :
    F.grMap k c = C.toGraded (MvPolynomial.rename (Fin.natAdd F.r) (homogPart k (C.ET c))) := by
  have hmem : algebraMap F.S R c ∈ maximalIdeal R ^ k := by
    have := Ideal.mem_map_of_mem (algebraMap F.S R) hc
    rw [Ideal.map_pow] at this
    exact Ideal.pow_right_mono (map_maximalIdeal_le _) _ this
  simp only [RegularFrame.grMap, hc, ↓reduceDIte]
  rw [C.mk_eq hmem, C.Φ_algebraMap, homogPart_rename _ (Fin.natAdd_injective _ _)]

open Classical in
/-- **The initial form of `f` in the coordinates** (p. 270: "`φ = Σ_A φ_A Z^A`"): for
`ν_M(f) = ν`, `in(f) = Σ_{|A| ≤ ν} [h_A]_{ν-|A|} Z^A`, where the class of the coefficient `h_A ∈ S`
is the homogeneous component of degree `ν - |A|` of `h_A ∈ k{x}`. -/
theorem initialForm_eq {f : R} {ν : ℕ} (hν : Ideal.ordElem (maximalIdeal R) f = ν) :
    initialForm (maximalIdeal R) f = C.toGraded
      (∑ A ∈ (Finsupp.finite_of_degree_le (σ := Fin F.r) ν).toFinset,
        MvPolynomial.rename (Fin.natAdd F.r) (homogPart (ν - A.degree) (C.ET (F.expCoeff f A))) *
          MvPolynomial.monomial (Finsupp.mapDomain (Fin.castAdd (n + 1)) A) 1) := by
  have hf : f ∈ maximalIdeal R ^ ν := Ideal.mem_pow_of_ordElem hν
  have he := RegularFrame.isExpansion_expansion F
  rw [initialForm_eq_mk _ hν, F.mk_eq_sum_grMap_mul he hf, map_sum]
  refine Finset.sum_congr rfl fun A hA => ?_
  have hAd : A.degree ≤ ν := by simpa using hA
  have hc : MvPowerSeries.coeff A (RegularFrame.expansion F f) ∈
      maximalIdeal F.S ^ (ν - A.degree) :=
    (F.mem_maximalIdeal_pow_iff_coeff_mem_pow he ν f).mp hf A hAd
  rw [map_mul, C.grMap_eq hc, C.toGraded_monomial_castAdd, RegularFrame.coeff_expansion]

end CohenCoordinates

end CohenCoordinates

section SupportExtraction

variable {R : Type u} [CommRing R] [IsRegularLocalRing R]

omit [IsRegularLocalRing R] in
/-- The homogeneous component of degree `0` is the constant term. -/
theorem homogPart_zero {N : ℕ} {K : Type*} [CommRing K] (g : MvPowerSeries (Fin N) K) :
    homogPart 0 g = MvPolynomial.C (MvPowerSeries.constantCoeff g) := by
  ext d
  rw [coeff_homogPart, MvPolynomial.coeff_C]
  by_cases hd : d = 0
  · subst hd; simp
  · have : d.degree ≠ 0 := fun h => hd ((Finsupp.degree_eq_zero_iff d).mp h)
    simp [this, Ne.symm hd]

namespace CohenCoordinates

variable {F : RegularFrame R} {n : ℕ} (C : CohenCoordinates F n)

open Classical in
/-- **The choice of `Ā` and `e`** (p. 270): "Since `(x₁, …, x_t)` is a regular system of
`τ_{(z)}`-parameters of `R` for `f`, those `φ_A` are forms in `X₁, …, X_t`, and there exists
`Ā ∈ Z₀ʳ` such that `|Ā| + ν_M(h_Ā) = ν` and that `deg φ_Ā > 0`.  Let `deg φ_Ā = ν_M(h_Ā) = e`."
In the coordinates: some coefficient `h_Ā` of the expansion of `f` over `S` has, in `k{x}`, order
`e = ν - |Ā| > 0` and a leading form involving only `x₁, …, x_t`.  (`x` is given as a family
indexed by `Fin t` with `t = τ_{(z)}(f) ≥ 1`, whose classes and the `Z_j` generate `T*`.) -/
theorem exists_support_data {f : R} {ν t : ℕ} (hν : Ideal.ordElem (maximalIdeal R) f = ν)
    (htτ : tauZ R F.z (fun _ : Fin 1 => f) = t) (ht1 : 1 ≤ t) (htle : t ≤ n + 1)
    (x : Fin t → maximalIdeal R)
    (hx : Submodule.span (R ⧸ maximalIdeal R)
      (Set.range (linearForms R x) ∪ Set.range (frameForm F.z)) =
        tauZSubmoduleStar R F.z (fun _ : Fin 1 => f))
    (hxY : ∀ i, (x i : R) = C.Y (Fin.natAdd F.r (Fin.castLE htle i))) :
    ∃ (A : Fin F.r →₀ ℕ) (e : ℕ), 0 < e ∧ A.degree + e = ν ∧
      (C.ET (F.expCoeff f A)).order = e ∧
      ∀ d : Fin (n + 1) →₀ ℕ, d.degree = e → MvPowerSeries.coeff d (C.ET (F.expCoeff f A)) ≠ 0 →
        ∀ i : Fin (n + 1), t ≤ (i : ℕ) → d i = 0 := by
  set Sν := (Finsupp.finite_of_degree_le (σ := Fin F.r) ν).toFinset with hSν
  have hmemS : ∀ A, A ∈ Sν ↔ A.degree ≤ ν := fun A => by simp [hSν]
  set hp : (Fin F.r →₀ ℕ) → MvPolynomial (Fin (n + 1)) (R ⧸ maximalIdeal R) :=
    fun A => homogPart (ν - A.degree) (C.ET (F.expCoeff f A)) with hhp
  set Q : MvPolynomial (Fin (F.r + (n + 1))) (R ⧸ maximalIdeal R) :=
    ∑ A ∈ Sν, MvPolynomial.rename (Fin.natAdd F.r) (hp A) *
      MvPolynomial.monomial (Finsupp.mapDomain (Fin.castAdd (n + 1)) A) 1 with hQdef
  have hQ : initialForm (maximalIdeal R) f = C.toGraded Q := C.initialForm_eq hν
  -- the coefficients of `Q`
  have hcoeffQ : ∀ (A : Fin F.r →₀ ℕ) (B : Fin (n + 1) →₀ ℕ),
      Q.coeff (Finsupp.mapDomain (Fin.castAdd (n + 1)) A + Finsupp.mapDomain (Fin.natAdd F.r) B) =
        if A.degree ≤ ν then (hp A).coeff B else 0 := by
    intro A B
    rw [hQdef, MvPolynomial.coeff_sum]
    simp only [coeff_rename_natAdd_mul_monomial_castAdd]
    simp only [Finset.sum_ite_eq Sν A, hmemS]
  -- `in(f)` lies in `k[T*]`, so `Q` involves only the variables of `T*`
  set V : Set (Fin (F.r + (n + 1))) := {v | (∃ j, v = Fin.castAdd (n + 1) j) ∨
    ∃ i : Fin t, v = Fin.natAdd F.r (Fin.castLE htle i)} with hV
  have hS : (Set.range (linearForms R x) ∪ Set.range (frameForm F.z) :
      Set (AssocGraded (maximalIdeal R))) = C.toGraded '' (MvPolynomial.X '' V) := by
    ext v
    simp only [Set.mem_union, Set.mem_range, Set.mem_image]
    constructor
    · rintro (⟨i, rfl⟩ | ⟨j, rfl⟩)
      · refine ⟨_, ⟨Fin.natAdd F.r (Fin.castLE htle i), Or.inr ⟨i, rfl⟩, rfl⟩, ?_⟩
        rw [C.toGraded_X]
        exact mk_congr_of_eq _ rfl (hxY i).symm _ _
      · exact ⟨_, ⟨Fin.castAdd _ j, Or.inl ⟨j, rfl⟩, rfl⟩, (C.frameForm_eq j).symm⟩
    · rintro ⟨_, ⟨v', hv', rfl⟩, rfl⟩
      rcases hv' with ⟨j, rfl⟩ | ⟨i, rfl⟩
      · exact Or.inr ⟨j, C.frameForm_eq j⟩
      · refine Or.inl ⟨i, ?_⟩
        rw [C.toGraded_X]
        exact mk_congr_of_eq _ rfl (hxY i) _ _
  have hin := initialForm_mem_adjoin_tauZSubmoduleStar F.z f
  rw [← hx, Algebra.adjoin_span, hS, ← AlgHom.map_adjoin, hQ] at hin
  obtain ⟨q, hq, hqQ⟩ := hin
  have hqQ' : q = Q := C.toGraded_bijective.1 hqQ
  rw [hqQ'] at hq
  have hQsupp : ∀ d ∈ Q.support, ∀ i ∈ d.support, i ∈ V := by
    intro d hd i hi
    have : Q ∈ MvPolynomial.supported (R ⧸ maximalIdeal R) V := hq
    rw [MvPolynomial.mem_supported] at this
    exact this (Finset.mem_coe.mpr ((MvPolynomial.mem_vars_iff_mem_support i).mpr ⟨d, hd, hi⟩))

  -- (a) there is `Ā` with `|Ā| < ν` and `hp Ā ≠ 0`, else `in(f) ∈ k[Z]` and `τ = 0`
  have hex : ∃ A, A.degree < ν ∧ hp A ≠ 0 := by
    by_contra hnone
    push Not at hnone
    have hzero : initialForm (maximalIdeal R) f ∈
        Algebra.adjoin (R ⧸ maximalIdeal R) (Set.range (frameForm F.z)) := by
      rw [hQ, hQdef, map_sum]
      refine Subalgebra.sum_mem _ fun A hA => ?_
      have hAd := (hmemS A).mp hA
      by_cases hlt : A.degree < ν
      · rw [hnone A hlt]; simp
      · have hAν : A.degree = ν := le_antisymm hAd (not_lt.mp hlt)
        have h0 : hp A = MvPolynomial.C (MvPowerSeries.constantCoeff
            (C.ET (F.expCoeff f A))) := by
          rw [hhp]
          simp only [hAν, Nat.sub_self]
          exact homogPart_zero _
        rw [h0, MvPolynomial.rename_C, map_mul, C.toGraded_monomial_castAdd]
        refine Subalgebra.mul_mem _ ?_ (Subalgebra.prod_mem _ fun i _ =>
          Subalgebra.pow_mem _ (Algebra.subset_adjoin (Set.mem_range_self i)) _)
        rw [CohenCoordinates.toGraded, MvPolynomial.aeval_C]
        exact Subalgebra.algebraMap_mem _ _
    have := tauZ_eq_zero_of_initialForm_mem_adjoin F.z_injective F.extends_rsop f hzero
    omega
  obtain ⟨A, hAlt, hAne⟩ := hex
  have hAν : A.degree ≤ ν := hAlt.le
  have hcoef : ∀ B, (hp A).coeff B = if B.degree = ν - A.degree then
      MvPowerSeries.coeff B (C.ET (F.expCoeff f A)) else 0 := fun B => coeff_homogPart _ _ B
  refine ⟨A, ν - A.degree, by omega, by omega, ?_, ?_⟩
  · rw [MvPowerSeries.order_eq_nat]
    refine ⟨?_, ?_⟩
    · obtain ⟨B, hB⟩ : ∃ B, (hp A).coeff B ≠ 0 := by
        by_contra h
        push Not at h
        exact hAne (MvPolynomial.ext _ _ h)
      rw [hcoef] at hB
      by_cases hdeg : B.degree = ν - A.degree
      · exact ⟨B, by simpa [hdeg] using hB, hdeg⟩
      · simp [hdeg] at hB
    · intro d hd
      have hf : f ∈ maximalIdeal R ^ ν := Ideal.mem_pow_of_ordElem hν
      have hcN : F.expCoeff f A ∈ maximalIdeal F.S ^ (ν - A.degree) :=
        (F.mem_maximalIdeal_pow_iff_coeff_mem_pow (RegularFrame.isExpansion_expansion F) ν f).mp
          hf A hAν
      have hcR : algebraMap F.S R (F.expCoeff f A) ∈ maximalIdeal R ^ (ν - A.degree) := by
        have := Ideal.mem_map_of_mem (algebraMap F.S R) hcN
        rw [Ideal.map_pow] at this
        exact Ideal.pow_right_mono (map_maximalIdeal_le _) _ this
      have hge : ((ν - A.degree : ℕ) : ℕ∞) ≤
          (C.Φ (algebraMap F.S R (F.expCoeff f A))).order := by
        rw [C.order_Φ]
        exact Ideal.le_ordElem hcR
      let e : Fin (n + 1) ↪ Fin (F.r + (n + 1)) := ⟨Fin.natAdd F.r, Fin.natAdd_injective _ _⟩
      have h1 : MvPowerSeries.coeff (Finsupp.embDomain e d)
          (C.Φ (algebraMap F.S R (F.expCoeff f A))) =
          MvPowerSeries.coeff d (C.ET (F.expCoeff f A)) := by
        rw [C.Φ_algebraMap]
        exact MvPowerSeries.coeff_embDomain_rename e _ d
      have h2 : (Finsupp.embDomain e d).degree = d.degree := by
        rw [Finsupp.embDomain_eq_mapDomain, Finsupp.degree_mapDomain]
      rw [← h1]
      exact MvPowerSeries.coeff_of_lt_order (lt_of_lt_of_le (by rw [h2]; exact_mod_cast hd) hge)
  · intro d hdeg hd i hi
    have hdA : (hp A).coeff d ≠ 0 := by
      rw [hcoef]
      simp only [hdeg, ↓reduceIte]
      exact hd
    have hQd : Q.coeff (Finsupp.mapDomain (Fin.castAdd (n + 1)) A +
        Finsupp.mapDomain (Fin.natAdd F.r) d) ≠ 0 := by
      rw [hcoeffQ]
      simp only [hAν, ↓reduceIte]
      exact hdA
    by_contra hdi
    have hmem : Fin.natAdd F.r i ∈ (Finsupp.mapDomain (Fin.castAdd (n + 1)) A +
        Finsupp.mapDomain (Fin.natAdd F.r) d).support := by
      rw [Finsupp.mem_support_iff, Finsupp.add_apply, mapDomain_castAdd_apply_natAdd,
        mapDomain_natAdd_apply_natAdd, zero_add]
      exact hdi
    rcases hQsupp _ (MvPolynomial.mem_support_iff.mpr hQd) _ hmem with ⟨j, hj⟩ | ⟨i', hi'⟩
    · have := congrArg Fin.val hj
      simp at this
      omega
    · have := congrArg Fin.val hi'
      simp at this
      omega

end CohenCoordinates

end SupportExtraction

section FrameOfPowerSeries

/-- p. 297 (and the frame `(S₀; w)` of p. 270): if `Φ : R ≃ K{Z, Y₁, …, Y_m}` sends `z` to `Z`,
then `T = Φ⁻¹(K{Y₁, …, Y_m})` gives a regular frame `(T; z)` of `R` with `r = 1` (and `R = T{z}`).
(The same statement as `exists_regularFrame_one_of_ringEquiv_mvPowerSeries` of
`Hironaka/Ch4/ImplicationsAB.lean`, which cannot be imported here since it depends on Theorem 9.) -/
theorem exists_regularFrame_singleton_of_ringEquiv_mvPowerSeries {R : Type u} [CommRing R]
    [IsRegularLocalRing R] {K : Type u} [Field K] {m : ℕ}
    (Φ : R ≃+* MvPowerSeries (Fin (m + 1)) K) {z : R} (hz : ExtendsToRSOP R {z})
    (hΦz : Φ z = MvPowerSeries.X 0) :
    ∃ (Fr : RegularFrame R) (h1 : Fr.r = 1), Fr.z ⟨0, by rw [h1]; exact Nat.one_pos⟩ = z ∧
      ∃ ET : Fr.S ≃+* MvPowerSeries (Fin m) K, ∀ s,
        Φ (algebraMap Fr.S R s) = (MvPowerSeries.finSuccEquiv K m).symm (PowerSeries.C (ET s)) := by
  classical
  let E : R ≃+* PowerSeries (MvPowerSeries (Fin m) K) :=
    Φ.trans (MvPowerSeries.finSuccEquiv K m).toRingEquiv
  have hEz : E z = PowerSeries.X := by
    show MvPowerSeries.finSuccEquiv K m (Φ z) = PowerSeries.X
    rw [hΦz, MvPowerSeries.finSuccEquiv_X_zero]
  let T := MvPowerSeries (Fin m) K
  let ι : T →+* R := (E.symm : PowerSeries T →+* R).comp PowerSeries.C
  let φ : T →+* R ⧸ Ideal.span {z} := (Ideal.Quotient.mk _).comp ι
  have hφ : Function.Bijective φ := by
    refine ⟨(injective_iff_map_eq_zero φ).mpr fun t ht => ?_, fun w => ?_⟩
    · rw [RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton'] at ht
      obtain ⟨c, hc⟩ := ht
      have h2 := congrArg E hc
      rw [map_mul, hEz] at h2
      have h3 : E (ι t) = PowerSeries.C t := E.apply_symm_apply _
      rw [h3] at h2
      have := congrArg PowerSeries.constantCoeff h2
      rwa [map_mul, PowerSeries.constantCoeff_X, mul_zero, PowerSeries.constantCoeff_C,
        eq_comm] at this
    · obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective w
      refine ⟨PowerSeries.constantCoeff (E r), ?_⟩
      rw [RingHom.comp_apply, Ideal.Quotient.eq, Ideal.mem_span_singleton']
      have hdvd : PowerSeries.X ∣ E r - PowerSeries.C (PowerSeries.constantCoeff (E r)) := by
        rw [PowerSeries.X_dvd_iff, map_sub, PowerSeries.constantCoeff_C, sub_self]
      obtain ⟨g, hg⟩ := hdvd
      refine ⟨-E.symm g, ?_⟩
      apply E.injective
      have h3 : E (ι (PowerSeries.constantCoeff (E r))) =
          PowerSeries.C (PowerSeries.constantCoeff (E r)) := E.apply_symm_apply _
      rw [map_mul, map_neg, E.apply_symm_apply, hEz, map_sub, h3]
      linear_combination hg
  have hreg : IsRegularLocalRing (R ⧸ Ideal.span {z}) :=
    ExtendsToRSOP.isRegularLocalRing_quotient_span_singleton hz (Finset.mem_singleton_self z)
  let eφ := RingEquiv.ofBijective φ hφ
  have hregT : IsRegularLocalRing T := IsRegularLocalRing.of_ringEquiv eφ.symm
  have hloc : IsLocalHom ι := ⟨fun t ht => by
    have h1 : IsUnit (φ t) := ht.map (Ideal.Quotient.mk _)
    have h2 : IsUnit (eφ.symm (φ t)) := h1.map eφ.symm
    rwa [show eφ.symm (φ t) = t from eφ.symm_apply_apply t] at h2⟩
  let Fr : RegularFrame R :=
    { S := T
      algebra := ι.toAlgebra
      isRegular := hregT
      isLocalHom := hloc
      r := 1
      z := fun _ => z
      z_injective := fun i j _ => Subsingleton.elim i j
      extends_rsop := by
        rw [Finset.image_const Finset.univ_nonempty]
        exact hz
      quot_bijective := by
        rw [Set.range_const]
        exact hφ }
  refine ⟨Fr, rfl, rfl, RingEquiv.refl T, fun s => ?_⟩
  show Φ (Φ.symm ((MvPowerSeries.finSuccEquiv K m).toRingEquiv.symm (PowerSeries.C s))) = _
  rw [Φ.apply_symm_apply]
  rfl


open Classical in
/-- The variables form a regular system of parameters of `k⟦X₁, …, X_N⟧`. -/
theorem isRegularSystemOfParameters_X {K : Type u} [Field K] (N : ℕ) :
    IsRegularSystemOfParameters (MvPowerSeries (Fin N) K)
      (Finset.univ.image (MvPowerSeries.X : Fin N → MvPowerSeries (Fin N) K)) := by
  have := isRegularLocalRing_mvPowerSeries K N
  have hspan : Ideal.span ((Finset.univ.image
      (MvPowerSeries.X : Fin N → MvPowerSeries (Fin N) K)) : Set (MvPowerSeries (Fin N) K)) =
      maximalIdeal (MvPowerSeries (Fin N) K) := by
    rw [Finset.coe_image, Finset.coe_univ, Set.image_univ, ← mvPowerSeriesMaximalIdeal_eq_span_X]
  refine rsop_of_span_of_card_le hspan ?_
  have h1 := le_ringKrullDim_mvPowerSeries K N
  have h2 := IsRegularLocalRing.spanFinrank_maximalIdeal (R := MvPowerSeries (Fin N) K)
  rw [← h2] at h1
  have h3 : (Finset.univ.image (MvPowerSeries.X : Fin N → MvPowerSeries (Fin N) K)).card ≤ N :=
    Finset.card_image_le.trans (by simp)
  exact h3.trans (by exact_mod_cast h1)

/-- `(S₀; w)` of the proof of Lemma 25: if `θ : S ≃ k{X₀, X₁, …, X_n}` is a ring isomorphism of a
regular local ring `S`, then `w = θ⁻¹(X₀)` and `S₀ = θ⁻¹ (k{X₁, …, X_n})` form a regular frame of
`S` with one element (p. 297, `exists_regularFrame_one_of_ringEquiv_mvPowerSeries`), and
`θ(S₀) = k{X₁, …, X_n}` (the variables `X_{j+1}`). -/
theorem exists_regularFrame_one_of_ringEquiv {S : Type u} [CommRing S] [IsRegularLocalRing S]
    {K : Type u} [Field K] {n : ℕ} (θ : S ≃+* MvPowerSeries (Fin (n + 1)) K) :
    ∃ (Fr : RegularFrame S) (h1 : Fr.r = 1),
      Fr.z ⟨0, by rw [h1]; exact Nat.one_pos⟩ = θ.symm (MvPowerSeries.X 0) ∧
      ∃ ET : Fr.S ≃+* MvPowerSeries (Fin n) K, ∀ s,
        θ (algebraMap Fr.S S s) = MvPowerSeries.rename Fin.succ (ET s) := by
  classical
  have hX : ExtendsToRSOP (MvPowerSeries (Fin (n + 1)) K)
      ({MvPowerSeries.X 0} : Finset (MvPowerSeries (Fin (n + 1)) K)) :=
    (ExtendsToRSOP.of_isRegularSystemOfParameters (isRegularSystemOfParameters_X (K := K)
      (n + 1))).mono (by
        intro y hy
        rw [Finset.mem_singleton] at hy
        subst hy
        exact Finset.mem_image_of_mem _ (Finset.mem_univ _))
  have hz : ExtendsToRSOP S ({θ.symm (MvPowerSeries.X 0)} : Finset S) := by
    have := hX.map_ringEquiv θ.symm
    rwa [Finset.image_singleton] at this
  obtain ⟨Fr, h1, hz1, ET, hET⟩ := exists_regularFrame_singleton_of_ringEquiv_mvPowerSeries θ hz
    (θ.apply_symm_apply _)
  refine ⟨Fr, h1, hz1, ET, fun s => ?_⟩
  rw [hET]
  exact (coeffRingInclusion_eq_rename (ET s))

end FrameOfPowerSeries

section Choice

open Classical in
/-- **The choice of `w`** (p. 270): "Let us take a regular system of parameters
`(z₁, …, z_r, x₁, …, x_s)` of `R` such that, if `t = τ_{(z)}(f)`, `(x₁, …, x_t)` is a regular system
of `τ_{(z)}`-parameters of `R` for `f`.  We have a subfield `k` of `R` such that
`R = k{z₁, …, z_r, x₁, …, x_s}` by the structure theorem of a complete regular local ring
(equi-characteristic) […] Let `S = k{x₁, …, x_s}` and `S₀ = k{x₂, …, x_s}` […] By taking a suitable
linear (non-singular) transformation of `(x₁, …, x_t)` with coefficients in `k`, we may assume that
`φ_Ā` has the term of `X₁^e` with non-zero coefficient in `k`.  Then by the Weierstrass
preparation theorem, we can write `h_Ā = u(x₁^e + p'₁x₁^{e-1} + ⋯ + p'_e)` […] Therefore, we may
replace `x₁` by `x₁ + e⁻¹p'₁` […] Thus we may assume that `h_Ā = u(x₁^e + p₂x₁^{e-2} + ⋯ + p_e)`
[…] We shall prove that `w = x₁` has the property required in the Lemma."

Formalized as the existence of the data of the reformulation (a `WeierstrassDatum` with
`F.z = z`) for which (3) `w ∈ T*` and (4) the Weierstrass shape of `f` hold, and `(z, w)` is
injective and can be extended to a regular system of parameters.  The structure theorem is
Cohen's coefficient field (the cited leaf of `CoefficientField.lean`) together with
`exists_ringEquiv_mvPowerSeries_of_coefficientField` (`R = k{z, x}`, proved).  The "suitable linear
transformation of `(x₁, …, x_t)`" (the shift `X_{j+1} ↦ X_{j+1} + c_jX₀` with `c_j = 0` for
`j + 1 ≥ t`), the Weierstrass preparation theorem (Mathlib's) and the replacement of `x₁` are done
in `exists_weierstrass_coordinates` (`WeierstrassCoordinates.lean`). -/
theorem exists_weierstrassDatum [Hironaka.HironakaCitedResults.{u}] {R : Type u} [CommRing R] [IsRegularLocalRing R]
    [IsAdicComplete (maximalIdeal R) R] [CharZero (ResidueField R)] {r : ℕ} (z : Fin r → R)
    (hz : Function.Injective z) (hext : ExtendsToRSOP R (Finset.image z Finset.univ)) (f : R)
    (hτ : 1 ≤ tauZ R z (fun _ : Fin 1 => f)) :
    ∃ (D : WeierstrassDatum R) (hr : D.F.r = r), (∀ j, D.F.z (Fin.cast hr.symm j) = z j) ∧
      D.InTauStar f ∧ D.HasShape f ∧
      Function.Injective (Fin.snoc D.F.z D.wR : Fin (D.F.r + 1) → R) ∧
      ExtendsToRSOP R (Finset.image (Fin.snoc D.F.z D.wR : Fin (D.F.r + 1) → R) Finset.univ) := by
  -- the regular system of parameters `(z, x₁, …, x_s)` and Cohen's structure theorem
  obtain ⟨m, hm, Y, x, hYinj, hYz, hYrsop, hx, hxY⟩ := exists_rsop_enumeration_tauZ hz hext hτ
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
  obtain ⟨σ, hσ⟩ := exists_residue_comp_eq_id_of_isAdicComplete R
  obtain ⟨Φ, hΦY, hΦσ, hΦo⟩ :=
    exists_ringEquiv_mvPowerSeries_of_coefficientField σ hσ Y hYinj hYrsop
  have hΦz : ∀ j, Φ (z j) = MvPowerSeries.X (Fin.castAdd (n + 1) j) := fun j => by
    rw [← hYz j, hΦY]
  obtain ⟨F, h, hFz, ET, hET⟩ := exists_regularFrame_of_ringEquiv_mvPowerSeries Φ hz hext hΦz
  subst h
  have hzF : F.z = z := funext fun j => by simpa using hFz j
  subst hzF
  let C : CohenCoordinates F n :=
    { Y := Y
      span_Y := by rw [← hYrsop.1, Finset.coe_image, Finset.coe_univ, Set.image_univ]
      dim_Y := by
        have := hYrsop.2
        rwa [Finset.card_image_of_injective _ hYinj, Finset.card_univ, Fintype.card_fin] at this
      σ := σ
      residue_comp_σ := hσ
      Φ := Φ
      Φ_Y := hΦY
      Φ_σ := hΦσ
      order_Φ := hΦo
      Y_castAdd := hYz
      ET := ET
      Φ_algebraMap := hET }
  -- `f ≠ 0` and `ν = ν_M(f)`
  have hf0 : f ≠ 0 := by
    rintro rfl
    have h0 : initialForm (maximalIdeal R) (0 : R) = 0 := by
      rw [initialForm, dite_eq_left (Ideal.ordElem_eq_top_iff.mpr fun n => zero_mem _)]
    have := tauZ_eq_zero_of_initialForm_mem_adjoin F.z_injective F.extends_rsop (0 : R)
      (by rw [h0]; exact zero_mem _)
    omega
  obtain ⟨ν, hν⟩ : ∃ ν : ℕ, Ideal.ordElem (maximalIdeal R) f = ν := by
    have : Ideal.ordElem (maximalIdeal R) f ≠ ⊤ :=
      (Ideal.ordElem_eq_top_iff_eq_zero (maximalIdeal.isMaximal R).ne_top).not.mpr hf0
    exact ENat.ne_top_iff_exists.mp this |>.imp fun ν hν => hν.symm
  -- the support: `Ā`, `e`, `h_Ā`
  obtain ⟨A, e, he, hAe, hord, hsupp⟩ := C.exists_support_data (t := tauZ R F.z (fun _ : Fin 1 => f))
    hν rfl hτ hm x hx hxY
  -- Weierstrass preparation and the Tschirnhaus substitution
  obtain ⟨ψ, ψ', u, p, hψ'ψ, hψψ', hψg, hc0, hlin⟩ :=
    exists_weierstrass_coordinates (k := ResidueField R) (t := tauZ R F.z (fun _ : Fin 1 => f)) hτ
      (C.ET (F.expCoeff f A)) he hord hsupp
  -- the new coordinates on `S` and the frame `(S₀; w)`
  let ψe : MvPowerSeries (Fin (n + 1)) (ResidueField R) ≃ₐ[ResidueField R]
      MvPowerSeries (Fin (n + 1)) (ResidueField R) :=
    AlgEquiv.ofAlgHom ψ ψ' (AlgHom.ext hψψ') (AlgHom.ext hψ'ψ)
  let θ0 : F.S ≃+* MvPowerSeries (Fin (n + 1)) (ResidueField R) :=
    C.ET.trans ψe.toRingEquiv
  obtain ⟨Fr, h1, hFr0, ET0, hET0⟩ := exists_regularFrame_one_of_ringEquiv θ0
  let D : WeierstrassDatum R := ⟨F, Fr, h1⟩
  have hw : D.w = θ0.symm (MvPowerSeries.X 0) := by
    have : Fin.cast D.rank_eq_one.symm (0 : Fin 1) = ⟨0, by rw [h1]; exact Nat.one_pos⟩ :=
      Fin.ext rfl
    rw [WeierstrassDatum.w, this]
    exact hFr0
  have hθ0w : θ0 D.w = MvPowerSeries.X 0 := by rw [hw]; exact θ0.apply_symm_apply _
  have hETw : C.ET D.w = ψ' (MvPowerSeries.X 0) := by
    rw [hw]
    exact C.ET.apply_symm_apply (ψ' (MvPowerSeries.X 0))
  -- (3): the initial form of `w` lies in `T*`
  have hInTau : D.InTauStar f := by
    show initialForm (maximalIdeal R) D.wR ∈ tauZSubmoduleStar R F.z (fun _ : Fin 1 => f)
    rw [D.initialForm_wR, C.mk_eq D.wR_mem_pow_one]
    have hΦw : C.Φ D.wR =
        MvPowerSeries.rename (Fin.natAdd F.r) (ψ' (MvPowerSeries.X 0)) := by
      show C.Φ (algebraMap F.S R D.w) = _
      exact (C.Φ_algebraMap D.w).trans (congrArg _ hETw)
    set P : MvPolynomial (Fin (n + 1)) (R ⧸ maximalIdeal R) :=
      homogPart 1 (ψ' (MvPowerSeries.X 0)) with hP
    have h2 : homogPart 1 (C.Φ D.wR) = MvPolynomial.rename (Fin.natAdd F.r) P := by
      rw [hΦw]
      exact homogPart_rename _ (Fin.natAdd_injective _ _) 1 _
    rw [h2]
    have hPcoeff : ∀ d, P.coeff d =
        if d.degree = 1 then MvPowerSeries.coeff d (ψ' (MvPowerSeries.X 0)) else 0 :=
      fun d => coeff_homogPart 1 _ d
    have hhom : (MvPolynomial.rename (Fin.natAdd F.r) P).IsHomogeneous 1 :=
      (isHomogeneous_homogPart 1 _).rename_isHomogeneous
    set V' : Set (Fin (F.r + (n + 1))) :=
      {v | ∃ i : Fin (tauZ R F.z (fun _ : Fin 1 => f)),
        v = Fin.natAdd F.r (Fin.castLE hm i)} with hV'
    have hVsupp : ∀ d ∈ (MvPolynomial.rename (Fin.natAdd F.r) P).support,
        ∀ i ∈ d.support, i ∈ V' := by
      intro d hd i hi
      obtain ⟨u0, rfl, hu0⟩ := MvPolynomial.coeff_rename_ne_zero _ _ _
        (MvPolynomial.mem_support_iff.mp hd)
      rw [hPcoeff] at hu0
      by_cases hdeg : u0.degree = 1
      · simp only [hdeg, ↓reduceIte] at hu0
        obtain ⟨s, rfl⟩ := exists_eq_single_one_of_degree_eq_one u0 hdeg
        rw [Finsupp.mapDomain_single, Finsupp.support_single _ one_ne_zero,
          Finset.mem_singleton] at hi
        subst hi
        have hs : (s : ℕ) < tauZ R F.z (fun _ : Fin 1 => f) := by
          by_contra hs
          push Not at hs
          exact hu0 (hlin s hs)
        exact ⟨⟨s, hs⟩, rfl⟩
      · simp only [hdeg, ↓reduceIte] at hu0
        exact (hu0 rfl).elim
    have hspanX := mem_span_X_of_isHomogeneous_one hhom V' hVsupp
    have hmem := Submodule.apply_mem_span_image_of_mem_span C.toGraded.toLinearMap hspanX
    refine (Submodule.span_le.mpr ?_) hmem
    rintro _ ⟨_, ⟨v, ⟨i, rfl⟩, rfl⟩, rfl⟩
    show C.toGraded (MvPolynomial.X _) ∈ _
    rw [C.toGraded_X]
    have hlf : AssocGraded.mk (maximalIdeal R) 1 (C.Y (Fin.natAdd F.r (Fin.castLE hm i)))
        (C.Y_mem _) = linearForms R x i := mk_congr_of_eq _ rfl (hxY i).symm _ _
    rw [hlf]
    have hxT : Submodule.span (R ⧸ maximalIdeal R)
        (Set.range (linearForms R x) ∪ Set.range (frameForm F.z)) =
        tauZSubmoduleStar R F.z (fun _ : Fin 1 => f) := hx
    rw [← hxT]
    exact Submodule.subset_span (Or.inl ⟨i, rfl⟩)
  -- (4): the Weierstrass shape
  have hShape : D.HasShape f := by
    refine ⟨A, e, θ0.symm (u : MvPowerSeries (Fin (n + 1)) (ResidueField R)),
      fun j => ET0.symm (p j), (u.isUnit).map θ0.symm, he, ?_, ?_⟩
    · rw [hν]; exact_mod_cast hAe
    · apply θ0.injective
      have hg : θ0 (F.expCoeff f A) = ψ (C.ET (F.expCoeff f A)) := rfl
      show θ0 (F.expCoeff f A) = _
      rw [hg, hψg, map_mul, map_add, map_pow, hθ0w, RingEquiv.apply_symm_apply, map_sum]
      congr 2
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_mul, map_pow, hθ0w, hET0, RingEquiv.apply_symm_apply]
  refine ⟨D, rfl, fun j => by simp [D], hInTau, hShape, D.injective_snoc, D.extendsToRSOP_snoc⟩

end Choice

end Hironaka
