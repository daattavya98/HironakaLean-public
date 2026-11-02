/-
Copyright (c) 2026 Daattavya Aggarwal, Minhyong Kim, Oisin Kim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daattavya Aggarwal, Minhyong Kim, Oisin Kim
-/
module

public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.MvPowerSeries.Equiv
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Architect
public import Hironaka.Ch4.ImplicationsAB
public import Hironaka.Statements

/-!
# Ch. IV §4 (pp. 314–315): the ring-level data of the frame of Lemma (CD.1)--(CD.5)

> [i] If `ℜ = (ℜ^N_II, F)`, then `z₀` is an element of `S₀` which generates the ideal of `F` in
> `S₀` … [ii] `T₀` is a formal power series [ring] of `N − 1` variables `(y₁, …, y_{N-1})` over
> `k` such that `(z₀, y₁, …, y_{N-1})` is a regular system of parameters of `Ŝ₀`. [iii]
> `(y₁, …, y_{N-1})` is so chosen that each `g_i` can be written in the form
> `g_j = u_j(z₀^ν + g_{j1} z₀^{ν-1} + ⋯ + g_{jν})` where `u_j` is a unit of `Ŝ₀` and `g_{ji} ∈ T₀`.
> [iv] If `ℜ = ℜ^N_II` without restriction, then `z₀` is so chosen that `g_{11} = 0` …
> (In [iii] we replace `z₀` by `z₀ + (1/ν)g_{11}`.) We may assume without any loss of generality
> that `u_j = 1` for all `j`. (pp. 314–315)

This file proves the existence of this data for an arbitrary complete regular local ring `R` with
residue field of characteristic zero (`R = Ŝ₀`) and an ideal `J` (`= Ĵ₀`) of order `ν`, without
the scheme-level objects of CD (`X̂_s`, `f̄_s`, the set `jGen`), which are left to
`ImplicationsCD.lean`:

* `exists_generators_ordElem_eq`: the base `[0]` with all `ν_M(g_j) = ν`;
* `exists_coefficientField_data`: `[ii]` (the subfield `k ⊆ T₀`, `T₀ ≅ k{y}`);
* `exists_cdFrame_of_given_z`: `[ii]`, `[iii]'` for a given `z₀` (the closed case `[i]`, where
  `z₀` is imposed by the divisor `F`);
* `exists_cdFrame_unrestricted`: `[ii]`, `[iii]'` and `[iv]` (`g₁₁ = 0`), `z₀` being produced by the
  Tschirnhausen substitution `z₀ ↦ z₀ + (1/ν)g₁₁`: `zTranslation` (the substitution `Z ↦ Z − τ`
  of `k{Z, Y}`, fixing `k{Y}`), `coeff_pred_taylor_eq_zero` (the Taylor expansion of the monic
  polynomial of `g_j` over `T₀`).
-/

@[expose] public section

open IsLocalRing

namespace Hironaka

universe u

section Generators

variable {R : Type u} [CommRing R] [IsRegularLocalRing R]

/-- A base of an ideal `J` whose elements all have order exactly `ν = ν_M(J)`. -/
theorem exists_generators_ordElem_eq (J : Ideal R) (ν : ℕ)
    (hlow : ∀ a ∈ J, (ν : ℕ∞) ≤ Ideal.ordElem (maximalIdeal R) a)
    (hex : ∃ a ∈ J, Ideal.ordElem (maximalIdeal R) a = ν) :
    ∃ (m : ℕ) (g : Fin m → R), Ideal.span (Set.range g) = J ∧
      ∀ j, Ideal.ordElem (maximalIdeal R) (g j) = ν := by
  classical
  obtain ⟨a₀, ha₀J, ha₀⟩ := hex
  obtain ⟨s, hs⟩ := IsNoetherian.noetherian J
  have hnot : a₀ ∉ maximalIdeal R ^ (ν + 1) := fun h => by
    have := Ideal.le_ordElem h
    rw [ha₀] at this
    have h2 : ν + 1 ≤ ν := by exact_mod_cast this
    omega
  let f : R → R := fun h => if Ideal.ordElem (maximalIdeal R) h = ν then h else h + a₀
  have hf : ∀ h ∈ J, f h ∈ J ∧ Ideal.ordElem (maximalIdeal R) (f h) = ν := by
    intro h hh
    by_cases hc : Ideal.ordElem (maximalIdeal R) h = ν
    · have hfh : f h = h := if_pos hc
      rw [hfh]; exact ⟨hh, hc⟩
    · have hfh : f h = h + a₀ := if_neg hc
      rw [hfh]
      refine ⟨J.add_mem hh ha₀J, ?_⟩
      have hgt : (ν + 1 : ℕ∞) ≤ Ideal.ordElem (maximalIdeal R) h :=
        Order.add_one_le_of_lt (lt_of_le_of_ne (hlow h hh) (Ne.symm hc))
      have hmem : h ∈ maximalIdeal R ^ (ν + 1) := by
        by_cases htop : Ideal.ordElem (maximalIdeal R) h = ⊤
        · have := (Ideal.ordElem_eq_top_iff.mp htop) (ν + 1); exact this
        · obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp htop
          have hn' : Ideal.ordElem (maximalIdeal R) h = n := hn.symm
          have : ν + 1 ≤ n := by rw [hn'] at hgt; exact_mod_cast hgt
          exact Ideal.pow_le_pow_right this (Ideal.mem_pow_of_ordElem hn')
      have hnot' : h + a₀ ∉ maximalIdeal R ^ (ν + 1) := fun h' =>
        hnot (by simpa using (maximalIdeal R ^ (ν + 1)).sub_mem h' hmem)
      exact le_antisymm (Ideal.ordElem_le_of_notMem hnot') (hlow _ (J.add_mem hh ha₀J))
  let F : Finset R := s.image f ∪ {a₀}
  refine ⟨F.card, fun j => (F.equivFin.symm j : R), ?_, fun j => ?_⟩
  · have hrange : Set.range (fun j => (F.equivFin.symm j : R)) = (F : Set R) := by
      ext y
      constructor
      · rintro ⟨j, rfl⟩; exact (F.equivFin.symm j).2
      · intro hy; exact ⟨F.equivFin ⟨y, hy⟩, by simp⟩
    rw [hrange]
    apply le_antisymm
    · rw [Ideal.span_le]
      intro y hy
      rcases Finset.mem_union.mp hy with hy | hy
      · obtain ⟨h, hh, rfl⟩ := Finset.mem_image.mp hy
        exact (hf h (hs ▸ Ideal.subset_span hh)).1
      · rw [Finset.mem_singleton.mp hy]; exact ha₀J
    · rw [← hs, Ideal.span_le]
      intro h hh
      have h1 : f h ∈ Ideal.span (F : Set R) := Ideal.subset_span (by
        exact Finset.mem_union_left _ (Finset.mem_image_of_mem f hh))
      have h2 : a₀ ∈ Ideal.span (F : Set R) := Ideal.subset_span (by
        exact Finset.mem_union_right _ (Finset.mem_singleton_self a₀))
      by_cases hc : Ideal.ordElem (maximalIdeal R) h = ν
      · simpa [f, hc] using h1
      · have : h = f h - a₀ := by simp [f, hc]
        rw [this]; exact sub_mem h1 h2
  · have hy := (F.equivFin.symm j).2
    rcases Finset.mem_union.mp hy with hy | hy
    · obtain ⟨h, hh, hfh⟩ := Finset.mem_image.mp hy
      show Ideal.ordElem (maximalIdeal R) (F.equivFin.symm j : R) = ν
      rw [← hfh]
      exact (hf h (hs ▸ Ideal.subset_span hh)).2
    · show Ideal.ordElem (maximalIdeal R) (F.equivFin.symm j : R) = ν
      rw [Finset.mem_singleton.mp hy]; exact ha₀

end Generators

section CoefficientField

variable {R : Type u} [CommRing R] [IsRegularLocalRing R]

open Classical in
/-- The data `[ii]` of p. 315: the coefficient field `k ⊆ T_0`, the variables `y_i ∈ T_0` and an
isomorphism `T_0 ≃ k{y₁, …, y_{N-1}}` fixing `k` and sending `y_i` to the `i`th variable, with
`(z_0, y₁, …, y_{N-1})` a regular system of parameters of `R`; obtained from a ring isomorphism
`Φ : R ≃ K{Z, Y₁, …, Y_n}`, `Φ z = Z`, and the induced `ET : T ≃ K{Y}`. -/
theorem exists_coefficientField_data (Fr : RegularFrame R) {K : Type u} [Field K] {n : ℕ}
    (Φ : R ≃+* MvPowerSeries (Fin (n + 1)) K) (ET : Fr.S ≃+* MvPowerSeries (Fin n) K)
    (hΦ : ∀ s, Φ (algebraMap Fr.S R s) =
      (MvPowerSeries.finSuccEquiv K n).symm (PowerSeries.C (ET s)))
    {z : R} (hΦz : Φ z = MvPowerSeries.X 0) (hdim : ((n + 1 : ℕ) : WithBot ℕ∞) = ringKrullDim R) :
    ∃ (kk : Subring Fr.S) (_ : IsField kk) (y : Fin n → Fr.S)
      (e : Fr.S ≃+* MvPowerSeries (Fin n) kk),
      (∀ c : kk, e (c : Fr.S) = MvPowerSeries.C c) ∧ (∀ i, e (y i) = MvPowerSeries.X i) ∧
      IsRegularSystemOfParameters R
        (insert z (Finset.image (fun i => algebraMap Fr.S R (y i)) Finset.univ)) := by
  classical
  let ψ : K →+* Fr.S := ET.symm.toRingHom.comp MvPowerSeries.C
  have hψ : Function.Injective ψ := by
    intro a b hab
    have := ET.symm.injective hab
    exact MvPowerSeries.C_injective this
  let eK : K ≃+* ψ.range := RingEquiv.ofBijective ψ.rangeRestrict
    ⟨fun a b hab => hψ (congrArg Subtype.val hab), ψ.rangeRestrict_surjective⟩
  have hfield : IsField ψ.range := by
    refine ⟨⟨0, 1, zero_ne_one⟩, mul_comm, fun {a} ha => ?_⟩
    obtain ⟨κ, rfl⟩ := eK.surjective a
    have hκ : κ ≠ 0 := fun h => ha (by rw [h, map_zero])
    exact ⟨eK κ⁻¹, by rw [← map_mul, mul_inv_cancel₀ hκ, map_one]⟩
  let mapE : MvPowerSeries (Fin n) K ≃+* MvPowerSeries (Fin n) ψ.range :=
    RingEquiv.ofRingHom (MvPowerSeries.map (eK : K →+* ψ.range))
      (MvPowerSeries.map (eK.symm : ψ.range →+* K))
      (by rw [← MvPowerSeries.map_comp]
          have : (eK : K →+* ψ.range).comp (eK.symm : ψ.range →+* K) = RingHom.id _ := by
            ext x; simp
          rw [this, MvPowerSeries.map_id])
      (by rw [← MvPowerSeries.map_comp]
          have : (eK.symm : ψ.range →+* K).comp (eK : K →+* ψ.range) = RingHom.id _ := by
            ext x; simp
          rw [this, MvPowerSeries.map_id])
  let e : Fr.S ≃+* MvPowerSeries (Fin n) ψ.range := ET.trans mapE
  have hψK : ∀ κ : K, ET (ψ κ) = MvPowerSeries.C κ := fun κ => by
    show ET (ET.symm (MvPowerSeries.C κ)) = _
    exact ET.apply_symm_apply _
  refine ⟨ψ.range, hfield, fun i => ET.symm (MvPowerSeries.X i), e, ?_, ?_, ?_⟩
  · rintro ⟨_, κ, rfl⟩
    show MvPowerSeries.map (eK : K →+* ψ.range) (ET (ψ κ)) = _
    rw [hψK, MvPowerSeries.map_C]
    rfl
  · intro i
    show MvPowerSeries.map (eK : K →+* ψ.range) (ET (ET.symm (MvPowerSeries.X i))) = _
    rw [ET.apply_symm_apply, MvPowerSeries.map_X]
  · -- the regular system of parameters
    have hy : ∀ i : Fin n, Φ (algebraMap Fr.S R (ET.symm (MvPowerSeries.X i))) =
        MvPowerSeries.X i.succ := fun i => by
      rw [hΦ, ET.apply_symm_apply, ← MvPowerSeries.finSuccEquiv_X_succ, AlgEquiv.symm_apply_apply]
    have hz0 : Φ.symm (MvPowerSeries.X 0) = z := (Φ.symm_apply_eq).mpr hΦz.symm
    have hsucc : ∀ i : Fin n, Φ.symm (MvPowerSeries.X i.succ) =
        algebraMap Fr.S R (ET.symm (MvPowerSeries.X i)) := fun i =>
      (Φ.symm_apply_eq).mpr (hy i).symm
    have hs : insert z (Finset.image (fun i => algebraMap Fr.S R (ET.symm (MvPowerSeries.X i)))
        Finset.univ) = Finset.univ.image (fun i : Fin (n + 1) => Φ.symm (MvPowerSeries.X i)) := by
      ext r
      simp only [Finset.mem_insert, Finset.mem_image, Finset.mem_univ, true_and]
      constructor
      · rintro (rfl | ⟨i, rfl⟩)
        · exact ⟨0, hz0⟩
        · exact ⟨i.succ, hsucc i⟩
      · rintro ⟨i, rfl⟩
        refine Fin.cases ?_ (fun j => ?_) i
        · exact Or.inl hz0
        · exact Or.inr ⟨j, (hsucc j).symm⟩
    rw [hs]
    refine ⟨?_, ?_⟩
    · have h1 : (fun i : Fin (n + 1) => Φ.symm (MvPowerSeries.X i)) =
          Φ.symm ∘ (MvPowerSeries.X : Fin (n + 1) → MvPowerSeries (Fin (n + 1)) K) := rfl
      rw [Finset.coe_image, Finset.coe_univ, Set.image_univ, h1, Set.range_comp, ← Ideal.map_span,
        ← maximalIdeal_mvPowerSeries_eq_span_X]
      exact IsLocalRing.map_ringEquiv_maximalIdeal Φ.symm
    · rw [Finset.card_image_of_injective _ (fun a b hab => ?_)]
      · simpa using hdim
      · exact MvPowerSeries.X_inj.mp (Φ.symm.injective hab)

end CoefficientField

section GivenZ

variable {R : Type u} [CommRing R] [IsRegularLocalRing R] [IsAdicComplete (maximalIdeal R) R]
  [CharZero (ResidueField R)]

open Classical in
/-- **The frame of pp. 314--315 for a given `z_0`** (`[0]`, `[ii]`, `[iii]'`): for an ideal `J` of
the complete regular local ring `R = Ŝ_0` of characteristic-zero residue field and dimension `N`,
with `ν_M(J) = ν`, and any `z` extending to a regular system of parameters, there are a regular
frame `(T; z)` of `R` with `r = 1` (`T ≅ k{y₁, …, y_{N-1}}`, `(z, y₁, …, y_{N-1})` a regular system
of parameters) and a base `(g_1, …, g_m)` of `J` with `ν_M(g_j) = ν` and
`g_j = z^ν + g_{j1} z^{ν-1} + ⋯ + g_{jν}`, `g_{ji} ∈ T`.  The coefficient field `k` and the
Weierstrass preparation are those of `exists_regularFrame_one_and_weierstrass_form`.

Deviation from the paper (gap filled): the paper says "[iii] `(y_1, …, y_{N-1})` is so chosen that
each `g_j` can be written in the form `g_j = u_j(z_0^ν + g_{j1}z_0^{ν-1} + ⋯ + g_{jν})` where
`u_j` is a unit of `Ŝ_0` and `g_{ji} ∈ T_0`" and "We may assume without any loss of generality that
`u_j = 1`" (p. 315).  The choice of the `y_j` (generic coordinates and Weierstrass preparation) is
`exists_regularFrame_one_and_weierstrass_form`; here the units are removed by replacing `g_j` by
`u_j⁻¹ g_j` (same ideal, same order), and the base `[0]` with all `ν_M(g_j) = ν` is constructed from
any base of `J`. -/
@[blueprint "lem:IV.4-frame-given-z"
  (statement := /-- Let $R$ be a complete regular local ring of dimension $N$ whose residue field
    has characteristic $0$, $J$ an ideal of $R$ with $\nu_M(J)=\nu$, and $z\in R$ a member of a
    regular system of parameters. Then there are a regular frame $(T;z)$ of $R$ with
    $T\simeq k\{y_1,\dots,y_{N-1}\}$ (the isomorphism fixing the subfield $k$ and sending $y_i$ to
    the $i$th variable, $(z,y_1,\dots,y_{N-1})$ a regular system of parameters of $R$) and a base
    $(g_1,\dots,g_m)$ of $J$ with $\nu_M(g_j)=\nu$ and
    $g_j=z^\nu+g_{j1}z^{\nu-1}+\dots+g_{j\nu}$, $g_{ji}\in T$. -/)
  (proof := /-- Take a base of $J$ of elements of order $\nu$ (replace a generator of order $>\nu$
    by its sum with an element of order $\nu$). Apply \cref{lem:IV.3-frame-weierstrass} to the
    $g_j$: $g_j=u_j(z^\nu+\dots)$ with $u_j$ a unit and coefficients in $T$ and in
    $\mathfrak m_T^i$; replace $g_j$ by $u_j^{-1}g_j$. The data $[ii]$ comes from the isomorphism
    $R\simeq k\{Z,Y\}$ of the proof of \cref{lem:IV.3-frame-weierstrass}.

    \textbf{Deviation from the paper (gap filled).} The paper says ``$(y_1,\dots,y_{N-1})$ is so
    chosen that each $g_j$ can be written in the form $g_j=u_j(z_0^\nu+g_{j1}z_0^{\nu-1}+\dots+
    g_{j\nu})$'' and ``We may assume without any loss of generality that $u_j=1$'' (p.~315). The
    choice of the $y_j$ (generic coordinates and Weierstrass preparation) is
    \cref{lem:IV.3-frame-weierstrass}; the units are removed by replacing $g_j$ by $u_j^{-1}g_j$,
    and the base [0] with $\nu_M(g_j)=\nu$ for all $j$ is constructed. -/)
  (proofUses := ["lem:IV.3-frame-weierstrass"])
  (latexEnv := "lemma")]
theorem exists_cdFrame_of_given_z [Hironaka.HironakaCitedResults.{u}] (N : ℕ) (hN : (N : WithBot ℕ∞) = ringKrullDim R) (J : Ideal R)
    (ν : ℕ) (hlow : ∀ a ∈ J, (ν : ℕ∞) ≤ Ideal.ordElem (maximalIdeal R) a)
    (hex : ∃ a ∈ J, Ideal.ordElem (maximalIdeal R) a = ν) {z : R} (hz : ExtendsToRSOP R {z}) :
    ∃ (Fr : RegularFrame R) (h1 : Fr.r = 1),
      Fr.z ⟨0, by rw [h1]; exact Nat.one_pos⟩ = z ∧
      (∃ (kk : Subring Fr.S) (_ : IsField kk) (y : Fin (N - 1) → Fr.S)
        (e : Fr.S ≃+* MvPowerSeries (Fin (N - 1)) kk),
        (∀ c : kk, e (c : Fr.S) = MvPowerSeries.C c) ∧ (∀ i, e (y i) = MvPowerSeries.X i) ∧
        IsRegularSystemOfParameters R
          (insert z (Finset.image (fun i => algebraMap Fr.S R (y i)) Finset.univ))) ∧
      ∃ (m : ℕ) (g : Fin m → R) (co : Fin m → Fin ν → Fr.S),
        Ideal.span (Set.range g) = J ∧
        (∀ j, Ideal.ordElem (maximalIdeal R) (g j) = ν) ∧
        (∀ j, g j = z ^ ν + ∑ i : Fin ν,
          algebraMap Fr.S R (co j i) * z ^ (ν - ((i : ℕ) + 1))) := by
  classical
  obtain ⟨m, g', hspan, hord⟩ := exists_generators_ordElem_eq J ν hlow hex
  have hg0 : ∀ j, g' j ≠ 0 := fun j h0 => by
    have := hord j
    have htop : Ideal.ordElem (maximalIdeal R) (0 : R) = ⊤ :=
      (Ideal.ordElem_eq_top_iff_eq_zero (maximalIdeal.isMaximal R).ne_top).mpr rfl
    rw [h0, htop] at this
    exact ENat.top_ne_natCast ν this
  obtain ⟨Fr, h1, hFz, νf, u, co, hνf, hform, -, n, Φ, ET, hΦz, hΦET, hdim⟩ :=
    exists_regularFrame_one_and_weierstrass_form hz g' hg0
  obtain rfl : N = n + 1 := by
    have : ((N : ℕ) : WithBot ℕ∞) = ((n + 1 : ℕ) : WithBot ℕ∞) := hN.trans hdim.symm
    exact_mod_cast this
  have hνi : ∀ i, νf i = ν := fun i => by
    have := (hνf i).trans (hord i)
    exact_mod_cast this
  obtain rfl : νf = fun _ => ν := funext hνi
  refine ⟨Fr, h1, hFz, ?_, m, fun j => ((u j)⁻¹ : Rˣ) * g' j, co, ?_, fun j => ?_, fun j => ?_⟩
  · exact exists_coefficientField_data Fr Φ ET hΦET hΦz hdim
  · apply le_antisymm
    · rw [Ideal.span_le]
      rintro _ ⟨j, rfl⟩
      rw [← hspan]
      exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨j, rfl⟩)
    · rw [← hspan, Ideal.span_le]
      rintro _ ⟨j, rfl⟩
      have : g' j = (u j : R) * (((u j)⁻¹ : Rˣ) * g' j) := by
        rw [← mul_assoc, Units.mul_inv, one_mul]
      rw [this]
      exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨j, rfl⟩)
  · rw [ordElem_mul_maximalIdeal, Ideal.ordElem_eq_zero_of_isUnit (Units.isUnit _), hord j,
      zero_add]
  · have := hform j
    beta_reduce at this
    show ((u j)⁻¹ : Rˣ) * g' j = _
    rw [this, ← mul_assoc, Units.inv_mul, one_mul]

end GivenZ

section Tschirnhausen

variable {K : Type u} [Field K] {n : ℕ}

theorem prod_X_succ_pow (d : Fin n →₀ ℕ) :
    (d.prod fun s k => (MvPowerSeries.X s.succ : MvPowerSeries (Fin (n + 1)) K) ^ k) =
      MvPowerSeries.monomial (Finsupp.mapDomain Fin.succ d) (1 : K) := by
  classical
  have h1 : ((MvPolynomial.monomial (Finsupp.mapDomain Fin.succ d) (1 : K) :
      MvPolynomial (Fin (n + 1)) K) : MvPowerSeries (Fin (n + 1)) K) =
      MvPowerSeries.monomial (Finsupp.mapDomain Fin.succ d) (1 : K) := by
    rw [MvPolynomial.coe_monomial]
  rw [← h1, MvPolynomial.monomial_eq, Finsupp.prod_mapDomain_index (by simp) (by intros; simp [pow_add])]
  have := map_prod (MvPolynomial.coeToMvPowerSeries.ringHom (σ := Fin (n + 1)) (R := K))
    (fun x => (MvPolynomial.X x.succ : MvPolynomial (Fin (n + 1)) K) ^ d x) d.support
  simp only [MvPolynomial.coeToMvPowerSeries.ringHom_apply, MvPolynomial.coe_pow,
    MvPolynomial.coe_X] at this
  simp only [Finsupp.prod]
  rw [← this]
  simp

theorem mapDomain_succ_eq_cons (d : Fin n →₀ ℕ) :
    Finsupp.mapDomain Fin.succ d = Finsupp.cons 0 d := by
  ext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [Finsupp.mapDomain_of_notMem_range]
  · rw [Finsupp.mapDomain_apply_of_injective (Fin.succ_injective n) d j]; simp

theorem coeff_cons_coeffRingInclusion (f : MvPowerSeries (Fin n) K) (k : ℕ) (β : Fin n →₀ ℕ) :
    MvPowerSeries.coeff (Finsupp.cons k β) (coeffRingInclusion K n f) =
      if k = 0 then MvPowerSeries.coeff β f else 0 := by
  rw [← MvPowerSeries.coeff_coeff_finSuccEquiv]
  have : MvPowerSeries.finSuccEquiv K n (coeffRingInclusion K n f) = PowerSeries.C f :=
    (MvPowerSeries.finSuccEquiv K n).apply_symm_apply _
  rw [this, PowerSeries.coeff_C]
  split_ifs <;> simp

theorem subst_succ_eq_coeffRingInclusion (f : MvPowerSeries (Fin n) K) :
    MvPowerSeries.subst (fun j : Fin n => (MvPowerSeries.X j.succ : MvPowerSeries (Fin (n + 1)) K))
      f = coeffRingInclusion K n f := by
  classical
  have hs : MvPowerSeries.HasSubst
      (fun j : Fin n => (MvPowerSeries.X j.succ : MvPowerSeries (Fin (n + 1)) K)) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (fun j => by simp)
  ext e
  obtain ⟨a, β, rfl⟩ : ∃ a β, e = Finsupp.cons a β := ⟨e 0, Finsupp.tail e, (Finsupp.cons_tail e).symm⟩
  rw [MvPowerSeries.coeff_subst hs, coeff_cons_coeffRingInclusion]
  simp only [prod_X_succ_pow, MvPowerSeries.coeff_monomial, mapDomain_succ_eq_cons,
    Finsupp.cons_injective2.eq_iff]
  by_cases ha : a = 0
  · subst ha
    rw [if_pos rfl, finsum_eq_single _ β]
    · simp
    · intro d hd; simp [Ne.symm hd]
  · rw [if_neg ha]
    exact finsum_eq_zero_of_forall_eq_zero fun d => by
      simp
      intro h; exact absurd h ha

variable (K n) in
/-- The substitution data `Z ↦ Z − τ`, `Y_j ↦ Y_j` for `τ ∈ K{Y}`. -/
noncomputable def zTranslationData (τ : MvPowerSeries (Fin n) K) :
    Fin (n + 1) → MvPowerSeries (Fin (n + 1)) K :=
  Fin.cons (MvPowerSeries.X 0 - coeffRingInclusion K n τ) (fun j => MvPowerSeries.X j.succ)

theorem constantCoeff_coeffRingInclusion (f : MvPowerSeries (Fin n) K) :
    MvPowerSeries.constantCoeff (coeffRingInclusion K n f) = MvPowerSeries.constantCoeff f := by
  rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, ← MvPowerSeries.coeff_zero_eq_constantCoeff_apply]
  have := coeff_cons_coeffRingInclusion f 0 0
  rw [Finsupp.cons_zero_zero] at this
  simpa using this

theorem hasSubst_zTranslationData {τ : MvPowerSeries (Fin n) K}
    (hτ : MvPowerSeries.constantCoeff τ = 0) :
    MvPowerSeries.HasSubst (zTranslationData K n τ) := by
  refine MvPowerSeries.hasSubst_of_constantCoeff_zero fun s => ?_
  refine Fin.cases ?_ (fun j => ?_) s
  · simp [zTranslationData, constantCoeff_coeffRingInclusion, hτ]
  · simp [zTranslationData]

/-- The `K`-algebra endomorphism `Z ↦ Z − τ` of `K{Z, Y}`. -/
noncomputable def zTranslation {τ : MvPowerSeries (Fin n) K}
    (hτ : MvPowerSeries.constantCoeff τ = 0) :
    MvPowerSeries (Fin (n + 1)) K →ₐ[K] MvPowerSeries (Fin (n + 1)) K :=
  MvPowerSeries.substAlgHom (hasSubst_zTranslationData hτ)

theorem zTranslation_X_zero {τ : MvPowerSeries (Fin n) K} (hτ : MvPowerSeries.constantCoeff τ = 0) :
    zTranslation hτ (MvPowerSeries.X 0) = MvPowerSeries.X 0 - coeffRingInclusion K n τ := by
  unfold zTranslation
  rw [MvPowerSeries.substAlgHom_apply, MvPowerSeries.subst_X (hasSubst_zTranslationData hτ)]
  simp [zTranslationData]

theorem zTranslation_coeffRingInclusion {τ : MvPowerSeries (Fin n) K}
    (hτ : MvPowerSeries.constantCoeff τ = 0) (f : MvPowerSeries (Fin n) K) :
    zTranslation hτ (coeffRingInclusion K n f) = coeffRingInclusion K n f := by
  have hs : MvPowerSeries.HasSubst
      (fun j : Fin n => (MvPowerSeries.X j.succ : MvPowerSeries (Fin (n + 1)) K)) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (fun j => by simp)
  unfold zTranslation
  rw [← subst_succ_eq_coeffRingInclusion, MvPowerSeries.substAlgHom_apply,
    MvPowerSeries.subst_comp_subst_apply hs (hasSubst_zTranslationData hτ)]
  congr 1
  funext j
  rw [MvPowerSeries.subst_X (hasSubst_zTranslationData hτ)]
  simp [zTranslationData]

theorem zTranslationData_zero (τ : MvPowerSeries (Fin n) K) :
    zTranslationData K n τ 0 = MvPowerSeries.X 0 - coeffRingInclusion K n τ := by
  simp [zTranslationData]

theorem zTranslationData_succ (τ : MvPowerSeries (Fin n) K) (j : Fin n) :
    zTranslationData K n τ j.succ = MvPowerSeries.X j.succ := by
  simp [zTranslationData]

theorem zTranslation_X_succ {τ : MvPowerSeries (Fin n) K} (hτ : MvPowerSeries.constantCoeff τ = 0)
    (j : Fin n) : zTranslation hτ (MvPowerSeries.X j.succ) = MvPowerSeries.X j.succ := by
  unfold zTranslation
  rw [MvPowerSeries.substAlgHom_apply, MvPowerSeries.subst_X (hasSubst_zTranslationData hτ),
    zTranslationData_succ]

theorem zTranslation_neg_zTranslation {τ τ' : MvPowerSeries (Fin n) K}
    (hτ : MvPowerSeries.constantCoeff τ = 0) (hτ' : MvPowerSeries.constantCoeff τ' = 0)
    (h : τ' = -τ) (g : MvPowerSeries (Fin (n + 1)) K) :
    zTranslation hτ' (zTranslation hτ g) = g := by
  subst h
  have : (fun s => zTranslation hτ' (zTranslationData K n τ s)) =
      (MvPowerSeries.X : Fin (n + 1) → MvPowerSeries (Fin (n + 1)) K) := by
    funext s
    refine Fin.cases ?_ (fun j => ?_) s
    · rw [zTranslationData_zero, map_sub, zTranslation_X_zero hτ', zTranslation_coeffRingInclusion,
        map_neg]
      ring
    · rw [zTranslationData_succ, zTranslation_X_succ hτ']
  have h2 : zTranslation hτ' (zTranslation hτ g) =
      MvPowerSeries.subst (fun s => zTranslation hτ' (zTranslationData K n τ s)) g := by
    unfold zTranslation
    rw [MvPowerSeries.substAlgHom_comp_substAlgHom_apply, MvPowerSeries.substAlgHom_apply]
  rw [h2, this, MvPowerSeries.subst_self]
  rfl

open Polynomial in
theorem coeff_pred_taylor_eq_zero {A : Type*} [CommRing A] {ν : ℕ} (hν : 0 < ν) (P : A[X])
    (hm : P.Monic) (hd : P.natDegree = ν) {u : A} (hu : u * (ν : A) = 1) :
    (taylor (-(u * P.coeff (ν - 1))) P).coeff (ν - 1) = 0 := by
  obtain ⟨k, rfl⟩ : ∃ k, ν = k + 1 := ⟨ν - 1, by omega⟩
  rw [taylor_coeff]
  have hdeg : (hasseDeriv (k + 1 - 1) P).natDegree < 2 :=
    lt_of_le_of_lt (natDegree_hasseDeriv_le P (k + 1 - 1)) (by omega)
  rw [eval_eq_sum_range' hdeg]
  have hc : P.coeff (k + 1) = 1 := by rw [← hd]; exact hm
  simp only [Nat.add_sub_cancel, Finset.sum_range_succ, Finset.sum_range_zero, hasseDeriv_coeff,
    zero_add, Nat.choose_self, Nat.cast_one, one_mul, pow_zero, pow_one, hc, add_comm 1 k,
    Nat.choose_succ_self_right, mul_one]
  push_cast at hu ⊢
  linear_combination (P.coeff k) * (-1 : A) * (hu)

end Tschirnhausen

section PolynomialPart

open Polynomial

variable {A : Type*} [CommRing A]

/-- `X^ν + ∑_{i<ν} c_i X^{ν-(i+1)}`. -/
noncomputable def monicOfCoeffs {ν : ℕ} (c : Fin ν → A) : A[X] :=
  X ^ ν + ∑ i : Fin ν, C (c i) * X ^ (ν - ((i : ℕ) + 1))

theorem natDegree_sum_lt {ν : ℕ} (hν : 0 < ν) (c : Fin ν → A) :
    (∑ i : Fin ν, C (c i) * (X : A[X]) ^ (ν - ((i : ℕ) + 1))).natDegree < ν := by
  refine lt_of_le_of_lt (natDegree_sum_le_of_forall_le _ _ (n := ν - 1) fun i _ => ?_) (by omega)
  exact (natDegree_C_mul_X_pow_le _ _).trans (by omega)

theorem monic_monicOfCoeffs [Nontrivial A] {ν : ℕ} (hν : 0 < ν) (c : Fin ν → A) :
    (monicOfCoeffs c).Monic ∧ (monicOfCoeffs c).natDegree = ν := by
  have h := natDegree_sum_lt hν c
  have hdeg : (∑ i : Fin ν, C (c i) * (X : A[X]) ^ (ν - ((i : ℕ) + 1))).degree < ν :=
    lt_of_le_of_lt degree_le_natDegree (by exact_mod_cast h)
  refine ⟨monic_X_pow_add hdeg, ?_⟩
  unfold monicOfCoeffs
  rw [natDegree_add_eq_left_of_degree_lt (by rwa [degree_X_pow]), natDegree_X_pow]

theorem coeff_pred_monicOfCoeffs [Nontrivial A] {ν : ℕ} (hν : 0 < ν) (c : Fin ν → A) :
    (monicOfCoeffs c).coeff (ν - 1) = c ⟨0, hν⟩ := by
  unfold monicOfCoeffs
  rw [coeff_add, coeff_X_pow, finsetSum_coeff, if_neg (by omega), zero_add,
    Finset.sum_eq_single ⟨0, hν⟩]
  · simp
  · intro i _ hi
    rw [coeff_C_mul_X_pow, if_neg]
    have : (i : ℕ) ≠ 0 := fun h => hi (Fin.ext h)
    have := i.2
    omega
  · simp

theorem aeval_monicOfCoeffs {R : Type*} [CommRing R] [Algebra A R] {ν : ℕ} (c : Fin ν → A)
    (x : R) :
    aeval x (monicOfCoeffs c) = x ^ ν + ∑ i : Fin ν, algebraMap A R (c i) * x ^ (ν - ((i : ℕ) + 1)) := by
  simp [monicOfCoeffs]

/-- A monic polynomial of degree `ν` is `monicOfCoeffs` of its coefficients. -/
theorem aeval_eq_of_monic {R : Type*} [CommRing R] [Algebra A R] (Q : A[X]) (hm : Q.Monic)
    {ν : ℕ} (hd : Q.natDegree = ν) (x : R) :
    aeval x Q = x ^ ν + ∑ l : Fin ν, algebraMap A R (Q.coeff (ν - ((l : ℕ) + 1))) *
      x ^ (ν - ((l : ℕ) + 1)) := by
  have h1 := hm.as_sum
  rw [hd] at h1
  conv_lhs => rw [h1]
  simp only [map_add, map_sum, map_mul, aeval_C, map_pow, aeval_X]
  congr 1
  rw [← Finset.sum_range_reflect, ← Fin.sum_univ_eq_sum_range]
  refine Finset.sum_congr rfl fun l _ => ?_
  have hl : ν - 1 - (l : ℕ) = ν - ((l : ℕ) + 1) := by omega
  rw [hl]

end PolynomialPart

section Unrestricted

variable {R : Type u} [CommRing R] [IsRegularLocalRing R]

open Classical in
theorem isRegularSystemOfParameters_image_symm_X {K : Type u} [Field K] {n : ℕ}
    (Φ : R ≃+* MvPowerSeries (Fin (n + 1)) K) (hdim : ((n + 1 : ℕ) : WithBot ℕ∞) = ringKrullDim R) :
    IsRegularSystemOfParameters R
      (Finset.univ.image fun i : Fin (n + 1) => Φ.symm (MvPowerSeries.X i)) := by
  classical
  refine ⟨?_, ?_⟩
  · have h1 : (fun i : Fin (n + 1) => Φ.symm (MvPowerSeries.X i)) =
        Φ.symm ∘ (MvPowerSeries.X : Fin (n + 1) → MvPowerSeries (Fin (n + 1)) K) := rfl
    rw [Finset.coe_image, Finset.coe_univ, Set.image_univ, h1, Set.range_comp, ← Ideal.map_span,
      ← maximalIdeal_mvPowerSeries_eq_span_X]
    exact IsLocalRing.map_ringEquiv_maximalIdeal Φ.symm
  · rw [Finset.card_image_of_injective _ (fun a b hab => ?_)]
    · simpa using hdim
    · exact MvPowerSeries.X_inj.mp (Φ.symm.injective hab)

open Classical in
theorem extendsToRSOP_of_ringEquiv_mvPowerSeries {K : Type u} [Field K] {n : ℕ}
    (Φ : R ≃+* MvPowerSeries (Fin (n + 1)) K) (hdim : ((n + 1 : ℕ) : WithBot ℕ∞) = ringKrullDim R)
    {z : R} (hΦz : Φ z = MvPowerSeries.X 0) : ExtendsToRSOP R {z} := by
  classical
  refine ⟨_, ?_, isRegularSystemOfParameters_image_symm_X Φ hdim⟩
  rw [Finset.singleton_subset_iff, Finset.mem_image]
  exact ⟨0, Finset.mem_univ _, (Φ.symm_apply_eq).mpr hΦz.symm⟩

theorem exists_extendsToRSOP_singleton (hR : (1 : WithBot ℕ∞) ≤ ringKrullDim R) :
    ∃ z : R, ExtendsToRSOP R {z} := by
  classical
  obtain ⟨s, hcard, hspan⟩ := (IsNoetherian.noetherian (maximalIdeal R)).exists_span_finset_card_eq_spanFinrank
  have hrs : IsRegularSystemOfParameters R s := ⟨hspan, by
    rw [hcard]; exact IsRegularLocalRing.spanFinrank_maximalIdeal⟩
  have hne : s.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    rintro rfl
    have := hrs.2
    simp at this
    rw [← this] at hR
    exact absurd hR (by simp)
  obtain ⟨z, hz⟩ := hne
  exact ⟨z, s, Finset.singleton_subset_iff.mpr hz, hrs⟩

end Unrestricted

section UnrestrictedFrame

variable {R : Type u} [CommRing R] [IsRegularLocalRing R] [IsAdicComplete (maximalIdeal R) R]
  [CharZero (ResidueField R)]

open Classical Polynomial in
/-- **The frame of pp. 314--315, unrestricted case** (`[ii]`, `[iii]'`, `[iv]`): as
`exists_cdFrame_of_given_z`, but `z_0` is chosen so that `g_{11} = 0`: the generic frame for an
arbitrary `z` is changed by the Tschirnhausen substitution `z ↦ z + (1/ν) g_{11}`.

Deviation from the paper (gap filled): the paper says only "[iv] If `ℜ = ℜ^N_II` without
restriction, then `z_0` is so chosen that `g_{11} = 0` … (In [iii] we replace `z_0` by
`z_0 + (1/ν)g_{11}`.)" (p. 315), with no argument.  Lean proves it: for `t = g_{11}/ν ∈ T`, the
translation `Z ↦ Z − t` is a ring automorphism `θ` of `k{Z, Y}` fixing `k{Y}` (substitution,
`zTranslation`), so `θ ∘ Φ` maps `z' = z + t` to `Z` and `T` to `k{Y}`, giving a regular frame
`(T'; z')` with the same image of `T`; every `g_j = P_j(z)` is re-expanded in `z'` by the Taylor
expansion `P_j(X − t)` of the monic polynomial `P_j` over `T`, whose coefficient of `X^{ν-1}` is
`g_{j1} − ν t`, which vanishes for `j = 1`. -/
@[blueprint "lem:IV.4-frame-unrestricted"
  (statement := /-- In the situation of \cref{lem:IV.4-frame-given-z} with $\nu>0$ and $N\ge1$,
    there are $z\in R$, a regular frame $(T;z)$ and a base $(g_1,\dots,g_m)$ of $J$ as there, such
    that moreover $g_{11}=0$, i.e.\ $g_1=z^\nu+g_{12}z^{\nu-2}+\dots+g_{1\nu}$. -/)
  (proof := /-- Start with the frame of \cref{lem:IV.4-frame-given-z} for an arbitrary $z_0$ and put
    $t=g_{11}/\nu\in\mathfrak m_T$ ($\nu$ is a unit of $T$) and $z=z_0+t$. The substitution
    $Z\mapsto Z-t$ is an automorphism $\theta$ of $k\{Z,Y\}$ fixing $k\{Y\}$, so $\theta\circ\Phi$
    maps $z$ to $Z$ and $T$ onto $k\{Y\}$; the regular frame $(T';z)$ of $R$ attached to it has the
    same image of $T'=T$ in $R$. Each $g_j=P_j(z_0)$, $P_j\in T[X]$ monic of degree $\nu$, equals
    $P_j(X-t)|_{X=z}$, a monic polynomial of degree $\nu$ in $z$ over $T$ by Taylor's formula, whose
    coefficient of $X^{\nu-1}$ is $g_{j1}-\nu t$, zero for $j=1$.

    \textbf{Deviation from the paper (gap filled).} The paper gives only the parenthetical ``(In
    [iii] we replace $z_0$ by $z_0+(1/\nu)g_{11}$.)'' (p.~315), without the re-expansion of the
    $g_j$ in the new variable nor the check that $T$ is unchanged. -/)
  (proofUses := ["lem:IV.4-frame-given-z"])
  (latexEnv := "lemma")]
theorem exists_cdFrame_unrestricted [Hironaka.HironakaCitedResults.{u}] (N : ℕ) (hN : (N : WithBot ℕ∞) = ringKrullDim R) (hN1 : 1 ≤ N)
    (J : Ideal R) (ν : ℕ) (hν : 0 < ν) (hlow : ∀ a ∈ J, (ν : ℕ∞) ≤ Ideal.ordElem (maximalIdeal R) a)
    (hex : ∃ a ∈ J, Ideal.ordElem (maximalIdeal R) a = ν) :
    ∃ (z : R) (Fr : RegularFrame R) (h1 : Fr.r = 1),
      Fr.z ⟨0, by rw [h1]; exact Nat.one_pos⟩ = z ∧
      (∃ (kk : Subring Fr.S) (_ : IsField kk) (y : Fin (N - 1) → Fr.S)
        (e : Fr.S ≃+* MvPowerSeries (Fin (N - 1)) kk),
        (∀ c : kk, e (c : Fr.S) = MvPowerSeries.C c) ∧ (∀ i, e (y i) = MvPowerSeries.X i) ∧
        IsRegularSystemOfParameters R
          (insert z (Finset.image (fun i => algebraMap Fr.S R (y i)) Finset.univ))) ∧
      ∃ (m : ℕ) (g : Fin m → R) (co : Fin m → Fin ν → Fr.S),
        Ideal.span (Set.range g) = J ∧
        (∀ j, Ideal.ordElem (maximalIdeal R) (g j) = ν) ∧
        (∀ j, g j = z ^ ν + ∑ i : Fin ν,
          algebraMap Fr.S R (co j i) * z ^ (ν - ((i : ℕ) + 1))) ∧
        ∃ (hm : 0 < m) (hν' : 0 < ν), co ⟨0, hm⟩ ⟨0, hν'⟩ = 0 := by
  obtain ⟨z₀, hz₀⟩ := exists_extendsToRSOP_singleton (R := R) (by
    rw [← hN]; exact_mod_cast hN1)
  obtain ⟨m, g', hspan, hord⟩ := exists_generators_ordElem_eq J ν hlow hex
  have hg0 : ∀ j, g' j ≠ 0 := fun j h0 => by
    have := hord j
    have htop : Ideal.ordElem (maximalIdeal R) (0 : R) = ⊤ :=
      (Ideal.ordElem_eq_top_iff_eq_zero (maximalIdeal.isMaximal R).ne_top).mpr rfl
    rw [h0, htop] at this
    exact ENat.top_ne_natCast ν this
  have hm : 0 < m := by
    obtain ⟨a, haJ, ha⟩ := hex
    by_contra h
    have hm0 : m = 0 := by omega
    subst hm0
    have : J = ⊥ := by rw [← hspan]; simp
    rw [this, Ideal.mem_bot] at haJ
    rw [haJ] at ha
    have htop : Ideal.ordElem (maximalIdeal R) (0 : R) = ⊤ :=
      (Ideal.ordElem_eq_top_iff_eq_zero (maximalIdeal.isMaximal R).ne_top).mpr rfl
    rw [htop] at ha
    exact ENat.top_ne_natCast ν ha
  obtain ⟨Fr, h1, hFz, νf, u, co, hνf, hform, hco, n, Φ, ET, hΦz, hΦET, hdim⟩ :=
    exists_regularFrame_one_and_weierstrass_form hz₀ g' hg0
  obtain rfl : N = n + 1 := by
    have : ((N : ℕ) : WithBot ℕ∞) = ((n + 1 : ℕ) : WithBot ℕ∞) := hN.trans hdim.symm
    exact_mod_cast this
  have hνi : ∀ i, νf i = ν := fun i => by
    have := (hνf i).trans (hord i)
    exact_mod_cast this
  obtain rfl : νf = fun _ => ν := funext hνi
  classical
  set K := ResidueField R with hK
  let P : Fin m → Fr.S[X] := fun j => monicOfCoeffs (co j)
  have hP : ∀ j, (P j).Monic ∧ (P j).natDegree = ν := fun j => monic_monicOfCoeffs hν (co j)
  -- `ν` is a unit of `T`
  have hνunit : IsUnit (ν : Fr.S) := by
    have h1 : IsUnit (ET (ν : Fr.S)) := by
      rw [map_natCast, MvPowerSeries.isUnit_iff_constantCoeff, map_natCast, isUnit_iff_ne_zero]
      exact Nat.cast_ne_zero.mpr hν.ne'
    exact (isUnit_map_iff ET _).mp h1
  obtain ⟨uν, huν⟩ := hνunit.exists_left_inv
  let j0 : Fin m := ⟨0, hm⟩
  set t : Fr.S := uν * (P j0).coeff (ν - 1) with ht
  have htN : t ∈ maximalIdeal Fr.S := by
    rw [ht, show (P j0).coeff (ν - 1) = co j0 ⟨0, hν⟩ from coeff_pred_monicOfCoeffs hν (co j0)]
    have := hco j0 ⟨0, hν⟩
    simp only [zero_add, pow_one] at this
    exact Ideal.mul_mem_left _ _ this
  have hτ : MvPowerSeries.constantCoeff (ET t) = 0 := by
    by_contra h
    have : IsUnit (ET t) := by
      rw [MvPowerSeries.isUnit_iff_constantCoeff, isUnit_iff_ne_zero]; exact h
    exact (IsLocalRing.mem_maximalIdeal t).mp htN ((isUnit_map_iff ET _).mp this)
  have hτ' : MvPowerSeries.constantCoeff (-(ET t)) = 0 := by rw [map_neg, hτ, neg_zero]
  let θe : MvPowerSeries (Fin (n + 1)) K ≃+* MvPowerSeries (Fin (n + 1)) K :=
    RingEquiv.ofRingHom (zTranslation hτ).toRingHom (zTranslation hτ').toRingHom
      (RingHom.ext fun g => zTranslation_neg_zTranslation hτ' hτ (neg_neg _).symm g)
      (RingHom.ext fun g => zTranslation_neg_zTranslation hτ hτ' rfl g)
  let Φ' : R ≃+* MvPowerSeries (Fin (n + 1)) K := Φ.trans θe
  have hΦ'alg : ∀ s : Fr.S, Φ' (algebraMap Fr.S R s) = coeffRingInclusion K n (ET s) := fun s => by
    show zTranslation hτ (Φ (algebraMap Fr.S R s)) = _
    rw [hΦET]
    exact zTranslation_coeffRingInclusion hτ _
  set z' : R := z₀ + algebraMap Fr.S R t with hz'
  have hΦ'z' : Φ' z' = MvPowerSeries.X 0 := by
    show zTranslation hτ (Φ z') = _
    rw [hz', map_add, hΦz]
    have h2 : Φ (algebraMap Fr.S R t) = coeffRingInclusion K n (ET t) := hΦET t
    rw [h2, map_add, zTranslation_X_zero hτ, zTranslation_coeffRingInclusion]
    ring
  have hz'rsop := extendsToRSOP_of_ringEquiv_mvPowerSeries Φ' hdim hΦ'z'
  obtain ⟨Fr', h1', hFz', ET', hΦ'ET'⟩ :=
    exists_regularFrame_one_of_ringEquiv_mvPowerSeries Φ' hz'rsop hΦ'z'
  -- the coefficients of `T` are coefficients of `T'`
  let tr : Fr.S → Fr'.S := fun s => ET'.symm (ET s)
  have htr : ∀ s, algebraMap Fr'.S R (tr s) = algebraMap Fr.S R s := fun s => by
    apply Φ'.injective
    rw [hΦ'ET' (tr s), hΦ'alg]
    show coeffRingInclusion K n (ET'  (ET'.symm (ET s))) = _
    rw [ET'.apply_symm_apply]
  have htr0 : tr 0 = 0 := by simp [tr]
  -- the Taylor expansion
  let Q : Fin m → Fr.S[X] := fun j => taylor (-t) (P j)
  have hQ : ∀ j, (Q j).Monic ∧ (Q j).natDegree = ν := fun j =>
    ⟨by unfold Monic; rw [leadingCoeff_taylor]; exact (hP j).1, by
      rw [natDegree_taylor]; exact (hP j).2⟩
  have hQ0 : (Q j0).coeff (ν - 1) = 0 :=
    coeff_pred_taylor_eq_zero hν (P j0) (hP j0).1 (hP j0).2 huν
  have hQeval : ∀ j, aeval z' (Q j) = aeval z₀ (P j) := fun j => by
    show aeval z' (taylor (-t) (P j)) = _
    rw [taylor_apply, aeval_comp]
    simp [hz']
  refine ⟨z', Fr', h1', hFz', exists_coefficientField_data Fr' Φ' ET' hΦ'ET' hΦ'z' hdim, m,
    fun j => ((u j)⁻¹ : Rˣ) * g' j, fun j l => tr ((Q j).coeff (ν - ((l : ℕ) + 1))), ?_, ?_,
    fun j => ?_, hm, hν, ?_⟩
  · apply le_antisymm
    · rw [Ideal.span_le]
      rintro _ ⟨j, rfl⟩
      rw [← hspan]
      exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨j, rfl⟩)
    · rw [← hspan, Ideal.span_le]
      rintro _ ⟨j, rfl⟩
      have : g' j = (u j : R) * (((u j)⁻¹ : Rˣ) * g' j) := by
        rw [← mul_assoc, Units.mul_inv, one_mul]
      rw [this]
      exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨j, rfl⟩)
  · intro j
    rw [ordElem_mul_maximalIdeal, Ideal.ordElem_eq_zero_of_isUnit (Units.isUnit _), hord j,
      zero_add]
  · have hf := hform j
    beta_reduce at hf
    have h1 : ((u j)⁻¹ : Rˣ) * g' j = aeval z₀ (P j) := by
      rw [hf, ← mul_assoc, Units.inv_mul, one_mul]
      simp [P, aeval_monicOfCoeffs]
    show ((u j)⁻¹ : Rˣ) * g' j = _
    rw [h1, ← hQeval, aeval_eq_of_monic (Q j) (hQ j).1 (hQ j).2]
    simp only [htr]
  · show tr ((Q j0).coeff (ν - ((0 : ℕ) + 1))) = 0
    rw [zero_add, show ν - 1 = ν - 1 from rfl, hQ0, htr0]

end UnrestrictedFrame

end Hironaka
