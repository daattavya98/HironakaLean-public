/-
Copyright (c) 2026 Daattavya Aggarwal, Minhyong Kim, Oisin Kim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daattavya Aggarwal, Minhyong Kim, Oisin Kim
-/
module

public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.Coalgebra.IsFrobenius
public import Mathlib.RingTheory.Derivation.Basic
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.HopfAlgebra.Basic
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Architect
public import Hironaka.Compat.JacobianCriterion
public import Hironaka.Compat.PowerSeriesPresentation
public import Hironaka.Compat.IndepModSqHeight

/-!
# Compatibility layer: the minor form of the jacobian criterion

Footnote 30 (p. 161) says that for `A` a homomorphic image of a polynomial ring over a formal power
series ring, "will suffice the jacobian criterion for simplicity (cf. Nagata, [14], or Nagata,
§ 46, Ch. VII of [15])".  Nagata's theorem
(`isRegularLocalRing_localization_iff_rank_jacobian_eq_height`,
`Hironaka/Compat/JacobianCriterion.lean`) is stated for the prime `𝔭 ⊆ 𝔮` and the rank of the
jacobian matrix of generators of `𝔭`.  The proof of property (c) of the class 𝔅 needs the following
consequence, derived here (a gap fill):

* `exists_minor_notMem_of_isIndepModSq`: if `T = k⟦t⟧[x]` (`k` of characteristic zero), `P` is a
  prime of `T` with `T_P` regular, and `f₁,…,f_h ∈ P` are independent modulo `𝔫²` in `T_P` (part
  of a regular system of parameters), then some `h × h` minor of the matrix of partial derivatives
  `(∂_j f_i)` is not in `P`.

Proof: `(f)T_P` is prime (the quotient is regular, hence a domain); let `𝔭` be its contraction to
`T`, so `T_P/𝔭T_P` is regular and `ht 𝔭 ≥ h` (a chain of primes `(f₁..f_i)T_P ∩ T`,
`IsIndepModSq.le_height_comap_span`).  By Nagata's theorem the jacobian matrix of generators `g` of
`𝔭` has rank `ht 𝔭 ≥ h` modulo `P`.  Each `g_j` satisfies `s g_j = Σ cᵢ fᵢ` with `s ∉ P`, so
modulo `P` the rows of `J(g)` are combinations of the rows of `J(f)` (`∂(s g) = s ∂g + g ∂s ≡ s ∂g`,
`∂(Σ cᵢfᵢ) ≡ Σ cᵢ ∂fᵢ`), whence `rank J(f) ≥ rank J(g) ≥ h`; as `J(f)` has `h` rows, its rank is
`h` and some `h × h` minor does not vanish.
-/

@[expose] public section

open IsLocalRing
open scoped Matrix

noncomputable section

namespace Hironaka

universe u

/-! ### Linear algebra: a full-rank matrix has a nonvanishing maximal minor -/

/-- A matrix over a field with `h` rows and rank `h` has a nonvanishing `h × h` minor. -/
theorem exists_det_submatrix_ne_zero_of_rank_eq {K ι : Type*} [Field K] [Fintype ι] {h : ℕ}
    (A : Matrix (Fin h) ι K) (hA : A.rank = h) :
    ∃ s : Fin h → ι, (A.submatrix id s).det ≠ 0 := by
  classical
  have hspan : Submodule.span K (Set.range A.col) = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    rw [← Matrix.rank_eq_finrank_span_cols, hA]
    simp
  obtain ⟨κ, a, ha, hsp, hli⟩ := exists_linearIndependent' K A.col
  have hbasis : Submodule.span K (Set.range (A.col ∘ a)) = ⊤ := hsp.trans hspan
  have : Finite κ := Finite.of_injective a ha
  have : Fintype κ := Fintype.ofFinite κ
  let b : Module.Basis κ K (Fin h → K) := Module.Basis.mk hli (by rw [hbasis])
  have hcard : Fintype.card κ = h := by
    rw [← Module.finrank_eq_card_basis b]
    simp
  let e : Fin h ≃ κ := (Fintype.equivFinOfCardEq hcard).symm
  refine ⟨a ∘ e, ?_⟩
  have hli' : LinearIndependent K (A.submatrix id (a ∘ e)).col := by
    exact hli.comp e e.injective
  exact (Matrix.isUnit_iff_isUnit_det _ |>.mp
    (Matrix.linearIndependent_cols_iff_isUnit.mp hli')).ne_zero

/-! ### The jacobian rank modulo a prime -/

section Jacobian

open PowerSeriesPolynomialRing

variable {k : Type u} [Field k] {n m : ℕ}

/-- The rank of the jacobian matrix `J(f)` of `f₁,…,f_r ∈ k⟦t⟧[x]` modulo a prime `𝔮` (over the
fraction field of `T/𝔮`), the quantity in Nagata's theorem. -/
def jacobianRank {r : ℕ} (f : Fin r → PowerSeriesPolynomialRing k n m)
    (𝔮 : Ideal (PowerSeriesPolynomialRing k n m)) [𝔮.IsPrime] : ℕ :=
  ((jacobian f).map (residueMap 𝔮)).rank

theorem jacobianRank_congr {r : ℕ} (f : Fin r → PowerSeriesPolynomialRing k n m)
    {𝔮₁ 𝔮₂ : Ideal (PowerSeriesPolynomialRing k n m)} [𝔮₁.IsPrime] [𝔮₂.IsPrime]
    (h : 𝔮₁ = 𝔮₂) : jacobianRank f 𝔮₁ = jacobianRank f 𝔮₂ := by
  subst h
  rfl

/-- **Nagata's theorem, "only if" direction, in terms of a prime `P ⊇ 𝔭` of `T`**: if
`T_P/𝔭T_P` is regular, the rank of the jacobian matrix of generators of `𝔭` modulo `P` is the
height of `𝔭`. -/
theorem jacobianRank_eq_height_of_isRegularLocalRing_quotient [Hironaka.Cited.IsRegularLocalRingLocalizationIffRankJacobianEqHeight.{u}] [CharZero k]
    (𝔭 P : Ideal (PowerSeriesPolynomialRing k n m)) [𝔭.IsPrime] [P.IsPrime] (h𝔭P : 𝔭 ≤ P)
    {r : ℕ} (g : Fin r → PowerSeriesPolynomialRing k n m) (hg : Ideal.span (Set.range g) = 𝔭)
    (hreg : IsRegularLocalRing (Localization.AtPrime P ⧸
      𝔭.map (algebraMap (PowerSeriesPolynomialRing k n m) (Localization.AtPrime P)))) :
    (jacobianRank g P : ℕ∞) = 𝔭.height := by
  let 𝔮' : Ideal (PowerSeriesPolynomialRing k n m ⧸ 𝔭) := P.map (Ideal.Quotient.mk 𝔭)
  have : 𝔮'.IsPrime := Ideal.isPrime_map_quotientMk_of_isPrime h𝔭P
  have hc : 𝔮'.comap (Ideal.Quotient.mk 𝔭) = P := by
    rw [Ideal.comap_map_of_surjective' _ Ideal.Quotient.mk_surjective, Ideal.mk_ker]
    exact sup_eq_left.mpr h𝔭P
  obtain ⟨e⟩ := nonempty_ringEquiv_localization_quotient_mk 𝔭 P 𝔮' hc
  have hreg' : IsRegularLocalRing (Localization.AtPrime 𝔮') :=
    IsRegularLocalRing.of_ringEquiv e.symm
  have key := (isRegularLocalRing_localization_iff_rank_jacobian_eq_height k n m 𝔭 𝔮' g hg).mp
    hreg'
  have hrank : jacobianRank g (𝔮'.comap (Ideal.Quotient.mk 𝔭)) = jacobianRank g P :=
    jacobianRank_congr g hc
  rw [← hrank]
  exact key

theorem residueMap_eq_zero_iff (P : Ideal (PowerSeriesPolynomialRing k n m)) [P.IsPrime]
    (x : PowerSeriesPolynomialRing k n m) : residueMap P x = 0 ↔ x ∈ P := by
  unfold residueMap
  rw [RingHom.comp_apply, map_eq_zero_iff _ (IsFractionRing.injective _ _),
    Ideal.Quotient.eq_zero_iff_mem]

/-- Rows of a jacobian matrix: if `s g_j = Σ cᵢ fᵢ` with `s ∉ P` and `fᵢ, g_j ∈ P`, then modulo
`P` the rows of `J(g)` are combinations of the rows of `J(f)` (`∂(s g) = s ∂g + g ∂s ≡ s ∂g` and
`∂(Σ cᵢ fᵢ) ≡ Σ cᵢ ∂fᵢ` modulo `P`), so `rank J(g) ≤ rank J(f)` modulo `P`. -/
theorem jacobianRank_le_of_forall_exists_mul_eq_sum {h r : ℕ}
    (P : Ideal (PowerSeriesPolynomialRing k n m)) [P.IsPrime]
    (f : Fin h → PowerSeriesPolynomialRing k n m) (g : Fin r → PowerSeriesPolynomialRing k n m)
    (hfP : ∀ i, f i ∈ P) (hgP : ∀ j, g j ∈ P)
    (hg : ∀ j, ∃ s ∉ P, ∃ c : Fin h → PowerSeriesPolynomialRing k n m,
      s * g j = ∑ i, c i * f i) :
    jacobianRank g P ≤ jacobianRank f P := by
  classical
  choose s hs c hsc using hg
  set φ := residueMap P with hφ
  have hφs : ∀ j, φ (s j) ≠ 0 := fun j => fun h0 => hs j ((residueMap_eq_zero_iff P _).mp h0)
  let C : Matrix (Fin r) (Fin h) (FractionRing (PowerSeriesPolynomialRing k n m ⧸ P)) :=
    Matrix.of fun j i => (φ (s j))⁻¹ * φ (c j i)
  have key : (jacobian g).map φ = C * (jacobian f).map φ := by
    ext j l
    simp only [Matrix.map_apply, jacobian, Matrix.of_apply, Matrix.mul_apply, C]
    set D := pderiv k n m l with hD
    have h1 : D (s j * g j) = D (∑ i, c j i * f i) := by rw [hsc j]
    simp only [Derivation.leibniz, map_sum, smul_eq_mul] at h1
    have h2 : s j * D (g j) - ∑ i, c j i * D (f i) ∈ P := by
      have : s j * D (g j) - ∑ i, c j i * D (f i) =
          ∑ i, f i * D (c j i) - g j * D (s j) := by
        rw [Finset.sum_add_distrib] at h1
        linear_combination h1
      rw [this]
      exact sub_mem (Ideal.sum_mem _ fun i _ => Ideal.mul_mem_right _ _ (hfP i))
        (Ideal.mul_mem_right _ _ (hgP j))
    have h3 := (residueMap_eq_zero_iff P _).mpr h2
    rw [map_sub, map_mul, map_sum, sub_eq_zero] at h3
    rw [← hφ] at h3
    rw [← inv_mul_cancel_left₀ (hφs j) (φ (D (g j))), h3, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [map_mul]; ring
  unfold jacobianRank
  rw [key]
  exact Matrix.rank_mul_le_right _ _

/-- **The minor form of the jacobian criterion** (footnote 30, p. 161).  Let `k` be a field of
characteristic zero, `T = k⟦t⟧[x]`, `P` a prime of `T` with `T_P` regular, and `f₁,…,f_h ∈ P` whose
images in `T_P` are independent modulo `𝔫²` (part of a regular system of parameters).  Then some
`h × h` minor `det(∂_{s_j} f_i)` of the matrix of partial derivatives is not in `P`.

Deviation from the paper (gap filled): the paper says "For this case, will suffice the jacobian
criterion for simplicity (cf. Nagata, [14], or Nagata, § 46, Ch. VII of [15])"; Nagata's theorem is
about generators of a prime `𝔭 ⊆ 𝔮` and `rank J = ht 𝔭`.  The consequence used for (c) is derived
here from the cited theorem, see the module docstring (the chain of primes `(f₁..f_i)T_P ∩ T`
gives `ht 𝔭 ≥ h`; the rows of the jacobian matrix of generators of `𝔭` are combinations, modulo
`P`, of the rows of `J(f)`). -/
@[blueprint "lem:jacobian-minor"
  (statement := /-- Let $k$ be a field of characteristic zero, $T=k[[t_1,\dots,t_n]][x_1,\dots,
    x_m]$, $\mathfrak P$ a prime of $T$ with $T_{\mathfrak P}$ regular, and
    $f_1,\dots,f_h\in\mathfrak P$ independent modulo the square of the maximal ideal of
    $T_{\mathfrak P}$ (part of a regular system of parameters). Then some $h\times h$ minor of
    the matrix $(\partial f_i/\partial u_j)$ of partial derivatives is not in
    $\mathfrak P$. -/)
  (proof := /-- The ideal $(f)T_{\mathfrak P}$ is prime (the quotient is regular, hence a
    domain); let $\mathfrak p$ be its contraction to $T$, so that $T_{\mathfrak P}/\mathfrak
    pT_{\mathfrak P}$ is regular. The primes $(f_1,\dots,f_i)T_{\mathfrak P}\cap T$ form a strict
    chain, so $\operatorname{ht}\mathfrak p\ge h$. By Nagata's theorem
    (\cref{lem:jacobian-criterion}) the jacobian matrix of a set of generators $g$ of
    $\mathfrak p$ has rank $\operatorname{ht}\mathfrak p$ modulo $\mathfrak P$. Each $g_j$
    satisfies $sg_j=\sum c_if_i$ with $s\notin\mathfrak P$; differentiating, modulo
    $\mathfrak P$ the rows of $J(g)$ are combinations of the rows of $J(f)$, so
    $\operatorname{rank}J(f)\ge h$; as $J(f)$ has $h$ rows its rank is $h$ and some $h\times h$
    minor does not vanish. \textbf{Deviation from the paper (gap filled).} Footnote~30 says only
    ``For this case, will suffice the jacobian criterion for simplicity''. -/)
  (proofUses := ["lem:jacobian-criterion"])
  (latexEnv := "lemma")]
theorem exists_minor_notMem_of_isIndepModSq [Hironaka.Cited.IsRegularLocalRingLocalizationIffRankJacobianEqHeight.{u}] [CharZero k]
    (P : Ideal (PowerSeriesPolynomialRing k n m)) [P.IsPrime]
    [IsRegularLocalRing (Localization.AtPrime P)] {h : ℕ}
    (f : Fin h → PowerSeriesPolynomialRing k n m) (hfP : ∀ i, f i ∈ P)
    (hind : IsIndepModSq (fun i => algebraMap (PowerSeriesPolynomialRing k n m)
      (Localization.AtPrime P) (f i))) :
    ∃ s : Fin h → Fin (n + m),
      (Matrix.of fun i j => pderiv k n m (s j) (f i)).det ∉ P := by
  classical
  set φL := algebraMap (PowerSeriesPolynomialRing k n m) (Localization.AtPrime P) with hφL
  have hfm : ∀ i, φL (f i) ∈ maximalIdeal (Localization.AtPrime P) := fun i =>
    (IsLocalization.AtPrime.to_map_mem_maximal_iff (Localization.AtPrime P) P _).mpr (hfP i)
  set 𝔞 : Ideal (Localization.AtPrime P) := Ideal.span (Set.range fun i => φL (f i)) with h𝔞
  have h𝔞prime : 𝔞.IsPrime := IsIndepModSq.isPrime_span hfm hind
  set 𝔭 : Ideal (PowerSeriesPolynomialRing k n m) := 𝔞.comap φL with h𝔭
  have h𝔭prime : 𝔭.IsPrime := Ideal.comap_isPrime φL 𝔞
  have h𝔭P : 𝔭 ≤ P := by
    intro x hx
    have h1 : φL x ∈ maximalIdeal (Localization.AtPrime P) := by
      have : 𝔞 ≤ maximalIdeal (Localization.AtPrime P) :=
        Ideal.span_le.mpr (by rintro _ ⟨i, rfl⟩; exact hfm i)
      exact this hx
    exact (IsLocalization.AtPrime.to_map_mem_maximal_iff (Localization.AtPrime P) P x).mp h1
  have hf𝔭 : ∀ i, f i ∈ 𝔭 := fun i => Ideal.subset_span ⟨i, rfl⟩
  -- the height of `𝔭` is at least `h`
  have hheight : (h : ℕ∞) ≤ 𝔭.height :=
    IsIndepModSq.le_height_comap_span φL h f hfm hind
  -- the quotient `T_P / 𝔭 T_P` is regular
  have hreg0 : IsRegularLocalRing (Localization.AtPrime P ⧸ 𝔞) :=
    hind.isRegularLocalRing_quotient hfm
  have hmap : 𝔭.map φL = 𝔞 := IsLocalization.map_under P.primeCompl (Localization.AtPrime P) 𝔞
  have hreg : IsRegularLocalRing (Localization.AtPrime P ⧸ 𝔭.map φL) :=
    IsRegularLocalRing.of_ringEquiv (Ideal.quotEquivOfEq hmap.symm)
  -- generators of `𝔭` and Nagata's theorem
  obtain ⟨r, g, hg⟩ := Submodule.fg_iff_exists_fin_generating_family.mp
    (IsNoetherian.noetherian 𝔭)
  have hrank : (jacobianRank g P : ℕ∞) = 𝔭.height :=
    jacobianRank_eq_height_of_isRegularLocalRing_quotient 𝔭 P h𝔭P g hg hreg
  have hgP : ∀ j, g j ∈ P := fun j => h𝔭P (by rw [← hg]; exact Ideal.subset_span ⟨j, rfl⟩)
  -- the rows of `J(g)` are combinations of the rows of `J(f)`
  have hrows : ∀ j, ∃ s ∉ P, ∃ c : Fin h → PowerSeriesPolynomialRing k n m,
      s * g j = ∑ i, c i * f i := by
    intro j
    have hgj𝔭 : g j ∈ 𝔭 := by
      rw [← hg]
      exact Ideal.subset_span ⟨j, rfl⟩
    have hgj : φL (g j) ∈ 𝔞 := hgj𝔭
    obtain ⟨c', hc'⟩ :=
      (Submodule.mem_span_range_iff_exists_fun (Localization.AtPrime P)).mp hgj
    obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples P.primeCompl Finset.univ c'
    choose a ha using fun i => hb i (Finset.mem_univ i)
    have ha' : ∀ i, φL (a i) = (b : PowerSeriesPolynomialRing k n m) • c' i := ha
    have h1 : φL ((b : PowerSeriesPolynomialRing k n m) * g j) = φL (∑ i, a i * f i) := by
      rw [map_mul, map_sum, ← hc', Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_mul, ha' i]
      simp only [smul_eq_mul, Algebra.smul_def, ← hφL]
      ring
    obtain ⟨w, hw⟩ := (IsLocalization.eq_iff_exists P.primeCompl (Localization.AtPrime P)).mp h1
    refine ⟨(w : PowerSeriesPolynomialRing k n m) * b, P.primeCompl.mul_mem w.2 b.2,
      fun i => w * a i, ?_⟩
    rw [mul_assoc, hw, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  have hle : jacobianRank g P ≤ jacobianRank f P :=
    jacobianRank_le_of_forall_exists_mul_eq_sum P f g hfP hgP hrows
  have hup : jacobianRank f P ≤ h := by
    have := Matrix.rank_le_card_height ((jacobian f).map (residueMap P))
    unfold jacobianRank
    simpa using this
  have hfull : jacobianRank f P = h := by
    refine le_antisymm hup ?_
    have : (h : ℕ∞) ≤ jacobianRank f P := by
      calc (h : ℕ∞) ≤ 𝔭.height := hheight
        _ = jacobianRank g P := hrank.symm
        _ ≤ jacobianRank f P := by exact_mod_cast hle
    exact_mod_cast this
  obtain ⟨s, hs⟩ := exists_det_submatrix_ne_zero_of_rank_eq _ hfull
  refine ⟨s, fun hdet => hs ?_⟩
  have : ((jacobian f).map (residueMap P)).submatrix id s =
      ((Matrix.of fun i j => pderiv k n m (s j) (f i)).map (residueMap P)) := rfl
  rw [this, ← RingHom.mapMatrix_apply, ← RingHom.map_det,
    (residueMap_eq_zero_iff P _).mpr hdet]

end Jacobian

end Hironaka
