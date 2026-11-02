/-
Copyright (c) 2026 Daattavya Aggarwal, Minhyong Kim, Oisin Kim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daattavya Aggarwal, Minhyong Kim, Oisin Kim
-/
module

public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
public import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Maps
public import Architect
public import Hironaka.Compat.BlowupCharts
public import Hironaka.Compat.BlowupProjectiveRing
public import Hironaka.Compat.ProjectiveChartCompat

/-!
# The chart maps `H_(uᵦ) → H'_(y_{ab})` of a blow-up of `Proj H` (step L1c of the p. 132 lemma)

Step L1c of the proof of `MonoidalTransformation.isProjectiveOver` (`Hironaka/Compat/BlowupProjective.lean`, the
unproved, uncited step "a monoidal transformation of a projective scheme is projective" of the Corollary on p. 132).
Notation: `H = B[T₀, …, T_{n-1}] ⧸ 𝔭` (a domain), `uᵢ` the images of the variables, `g₁, …, g_N ∈ H_e` and
`H' = B[V_k] ⧸ 𝔟` the ring of `Hironaka/Compat/BlowupProjectiveRing.lean`, `y_{(a,i)} = g_a uᵢ`.

* `BlowupRing.kappa a : H → H'`, the graded ring homomorphism `uᵢ ↦ y_{(a,i)}` (well defined because `𝔭` is homogeneous);
  `incl (κ_a x) = g_a ^ d * x` for `x ∈ H_d`.
* `BlowupRing.rho a b : H_(u_b) → H'_(y_{ab})`, `x / u_b ^ d ↦ κ_a x / y_{ab} ^ d`.
* `BlowupRing.exists_theta`: the ring isomorphism `θ : Γ(D₊(u_b))[I/γ_{ab}] ≅ H'_(y_{ab})` between the chart ring of the
  blow-up (`chartAlgebra`, `Hironaka/Compat/BlowupCharts.lean`) and the chart ring of `Proj H'`; here
  `γ_{ab} = g_a / u_b ^ e` and `I = (γ_{cb})_c` is the ideal of the center on the chart (hypothesis `hI`, supplied by
  L1a `quotientGrading.exists_forms_generating`); `θ` extends `ψ_{ab} = ρ_{ab} ∘ (H_(u_b) ≅ Γ(D₊(u_b)))⁻¹`;
* `BlowupRing.pullback_fst_comp_eq`: the chart maps `Spec H'_(y_{ab}) → Spec H_(u_b) → Proj H` agree on the overlaps
  `D₊(y_{ab}) ∩ D₊(y_{cd})`, so they glue by `Scheme.OpenCover.glueMorphisms` (`chartCover`, `toBase`).  This is the
  gluing condition that the maps `Spec θ_{ab} ≫ t.chart` into a monoidal transformation `t` must satisfy, by the
  uniqueness in (ii) (`MonoidalTransformation.hom_ext`).

Everything is computed inside the fraction field of `H` (`awayEmb`).  Nothing here is printed: it is part of the
proof of a gap filled.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory MvPolynomial DirectSum HomogeneousLocalization

namespace Hironaka

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

set_option linter.unusedSectionVars false

namespace BlowupRing

variable {B : Type u} [Field B] {n N e : ℕ} (𝔭 : HomogeneousIdeal (homogeneousSubmodule (Fin n) B))
  (g : Fin N → MvPolynomial (Fin n) B ⧸ 𝔭.toIdeal) (hg : ∀ a, g a ∈ quotientGrading 𝔭 e)

/-- The index `(a, i) ↦ k` of the generator `y_{(a,i)} = g_a uᵢ`. -/
def idx (a : Fin N) (i : Fin n) : Fin (N * n) := finProdFinEquiv (a, i)

/-- The substitution `T_i ↦ V_{(a,i)}` of polynomial rings. -/
noncomputable def subst (a : Fin N) : MvPolynomial (Fin n) B →ₐ[B] MvPolynomial (Fin (N * n)) B :=
  aeval fun i => X (idx a i)

/-- A form `p` of degree `d` is scaled by `c ^ d` when every variable is scaled by `c`. -/
theorem aeval_mul_eq_pow_mul {R S σ : Type*} [CommRing R] [CommRing S] [Algebra R S] {p : MvPolynomial σ R}
    {d : ℕ} (hp : p.IsHomogeneous d) (c : S) (f : σ → S) :
    aeval (fun i => c * f i) p = c ^ d * aeval f p := by
  classical
  rw [p.as_sum, map_sum, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  rw [aeval_monomial, aeval_monomial, Finsupp.prod, Finsupp.prod]
  simp only [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
  have hmd : ∑ i ∈ m.support, m i = d := by
    have := hp (mem_support_iff.mp hm)
    simpa [Finsupp.weight_apply, Finsupp.sum] using this
  rw [hmd]; ring

/-- `subst a` preserves forms of degree `d`. -/
theorem subst_isHomogeneous (a : Fin N) {d : ℕ} {p : MvPolynomial (Fin n) B} (hp : p.IsHomogeneous d) :
    (subst a p).IsHomogeneous d := by
  have := hp.aeval (fun i => X (idx a i)) (fun i => isHomogeneous_X B _)
  rwa [one_mul] at this

/-- The generators `y_{(a,i)} = g_a uᵢ`. -/
theorem gen_idx (a : Fin N) (i : Fin n) : gen 𝔭 g (idx a i) = g a * quotientGrading.var 𝔭 i := by
  simp [gen, idx]

/-- `eval ∘ subst a = (T_i ↦ g_a uᵢ)`. -/
theorem eval_subst (a : Fin N) (p : MvPolynomial (Fin n) B) :
    eval 𝔭 g (subst a p) = aeval (fun i => g a * quotientGrading.var 𝔭 i) p := by
  have : (eval 𝔭 g).comp (subst a) = aeval (fun i => g a * quotientGrading.var 𝔭 i) := by
    refine MvPolynomial.algHom_ext fun i => ?_
    simp [subst, eval_X, gen_idx]
  exact congrArg (fun φ => φ p) this

/-- The evaluation at the variables `uᵢ` of `H` is the quotient map. -/
theorem aeval_var (p : MvPolynomial (Fin n) B) :
    aeval (quotientGrading.var 𝔭) p = Ideal.Quotient.mk 𝔭.toIdeal p := by
  have : (Ideal.Quotient.mkₐ B 𝔭.toIdeal) = aeval (quotientGrading.var 𝔭) := by
    refine MvPolynomial.algHom_ext fun i => ?_
    simp [quotientGrading.var]
  exact (congrArg (fun φ => φ p) this).symm

/-- For a form `p` of degree `d`, `eval (subst a p) = g_a ^ d * p`. -/
theorem eval_subst_homogeneous (a : Fin N) {d : ℕ} {p : MvPolynomial (Fin n) B} (hp : p.IsHomogeneous d) :
    eval 𝔭 g (subst a p) = g a ^ d * Ideal.Quotient.mk 𝔭.toIdeal p := by
  rw [eval_subst, aeval_mul_eq_pow_mul hp, aeval_var]

/-- The homogeneous components of an element of the homogeneous ideal `𝔭` lie in `𝔭`. -/
theorem homogeneousComponent_mem_ideal {p : MvPolynomial (Fin n) B} (hp : p ∈ 𝔭.toIdeal) (i : ℕ) :
    homogeneousComponent i p ∈ 𝔭.toIdeal :=
  (MvPolynomial.decomposition.decompose'_apply p i) ▸ 𝔭.isHomogeneous i hp

/-- `subst a` sends `𝔭` into `𝔟 = ker (eval)`. -/
theorem eval_subst_eq_zero (a : Fin N) {p : MvPolynomial (Fin n) B} (hp : p ∈ 𝔭.toIdeal) :
    eval 𝔭 g (subst a p) = 0 := by
  conv_lhs => rw [← sum_homogeneousComponent p]
  rw [map_sum, map_sum]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [eval_subst_homogeneous 𝔭 g a (homogeneousComponent_isHomogeneous i p),
    (Ideal.Quotient.eq_zero_iff_mem).mpr (homogeneousComponent_mem_ideal 𝔭 hp i), mul_zero]

/-- The ring homomorphism `κ_a : H → H'`, `uᵢ ↦ y_{(a,i)} = g_a uᵢ`. -/
noncomputable def kappa (a : Fin N) :
    MvPolynomial (Fin n) B ⧸ 𝔭.toIdeal →+*
      MvPolynomial (Fin (N * n)) B ⧸ (kerIdeal 𝔭 g hg).toIdeal :=
  Ideal.Quotient.lift 𝔭.toIdeal
    ((Ideal.Quotient.mk (kerIdeal 𝔭 g hg).toIdeal).comp (subst a).toRingHom) fun p hp => by
      simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
        Ideal.Quotient.eq_zero_iff_mem, mem_kerIdeal_iff]
      exact eval_subst_eq_zero 𝔭 g a hp

/-- `κ_a` on a class `mk p` is the class of `subst a p`. -/
theorem kappa_mk (a : Fin N) (p : MvPolynomial (Fin n) B) :
    kappa 𝔭 g hg a (Ideal.Quotient.mk 𝔭.toIdeal p) = Ideal.Quotient.mk _ (subst a p) := rfl

/-- `κ_a` maps `H_d` into `H'_d`. -/
theorem kappa_mem (a : Fin N) {d : ℕ} {x : MvPolynomial (Fin n) B ⧸ 𝔭.toIdeal}
    (hx : x ∈ quotientGrading 𝔭 d) : kappa 𝔭 g hg a x ∈ quotientGrading (kerIdeal 𝔭 g hg) d := by
  obtain ⟨p, hp, hpx⟩ := hx
  have : x = Ideal.Quotient.mk 𝔭.toIdeal p := hpx.symm
  rw [this, kappa_mk]
  exact mk_mem_quotientGrading _ (subst_isHomogeneous a hp)

/-- `incl (κ_a x) = g_a ^ d * x` for `x ∈ H_d`. -/
theorem incl_kappa (a : Fin N) {d : ℕ} {x : MvPolynomial (Fin n) B ⧸ 𝔭.toIdeal}
    (hx : x ∈ quotientGrading 𝔭 d) : incl 𝔭 g hg (kappa 𝔭 g hg a x) = g a ^ d * x := by
  obtain ⟨p, hp, hpx⟩ := hx
  have : x = Ideal.Quotient.mk 𝔭.toIdeal p := hpx.symm
  rw [this, kappa_mk, incl_mk, eval_subst_homogeneous 𝔭 g a hp]

/-- The graded ring homomorphism `κ_a : H → H'`. -/
noncomputable def kappaGraded (a : Fin N) : quotientGrading 𝔭 →+*ᵍ quotientGrading (kerIdeal 𝔭 g hg) :=
  ⟨kappa 𝔭 g hg a, fun hx => kappa_mem 𝔭 g hg a hx⟩

/-- The underlying map of `kappaGraded` is `kappa`. -/
theorem kappaGraded_apply (a : Fin N) (x : MvPolynomial (Fin n) B ⧸ 𝔭.toIdeal) :
    kappaGraded 𝔭 g hg a x = kappa 𝔭 g hg a x := rfl

/-- Abstract injectivity of the chart algebra map: if `ψ : A → S` and `E : S → K` embed compatibly into a field
(`E ∘ ψ = eA` injective, `eA a ≠ 0`), then every `θ : A[I/a] → S` extending `ψ` is injective. -/
theorem chartAlgebra_injective_of_embed {A S K : Type*} [CommRing A] [CommRing S] [Field K] {I : Ideal A}
    {a : A} (ψ : A →+* S) (E : S →+* K) (eA : A →+* K) (heA : Function.Injective eA)
    (hE : ∀ r, E (ψ r) = eA r) (ha : eA a ≠ 0) (θ : chartAlgebra I a →+* S)
    (hθ : θ.comp (algebraMap A (chartAlgebra I a)) = ψ) : Function.Injective θ := by
  have hunit : IsUnit (eA a) := ha.isUnit
  let Λ : Localization.Away a →+* K := Localization.awayLift eA a hunit
  let φ2 : chartAlgebra I a →+* K := Λ.comp (chartAlgebra I a).val.toRingHom
  have hEθ : E.comp θ = φ2 := by
    refine chartAlgebra.ringHom_ext ?_ ?_
    · refine RingHom.ext fun r => ?_
      have h1 : θ (algebraMap A _ r) = ψ r := RingHom.congr_fun hθ r
      show E (θ (algebraMap A _ r)) = Λ (algebraMap A (Localization.Away a) r)
      rw [h1, hE]
      exact (IsLocalization.lift_eq _ _).symm
    · have h1 : θ (algebraMap A _ a) = ψ a := RingHom.congr_fun hθ a
      show E (θ (algebraMap A _ a)) ∈ nonZeroDivisors K
      rw [h1, hE]
      exact mem_nonZeroDivisors_of_ne_zero ha
  have hΛinj : Function.Injective Λ := by
    have hu : ∀ y : Submonoid.powers a, IsUnit (eA y) := by
      rintro ⟨_, k, rfl⟩
      simpa using hunit.pow k
    show Function.Injective (IsLocalization.lift (M := Submonoid.powers a) hu)
    rw [IsLocalization.lift_injective_iff]
    intro x y
    constructor
    · intro h
      obtain ⟨⟨_, k, rfl⟩, hk⟩ := (IsLocalization.eq_iff_exists (Submonoid.powers a)
        (Localization.Away a)).mp h
      have hk' : eA (a ^ k) * eA x = eA (a ^ k) * eA y := by
        rw [← map_mul, ← map_mul]; exact congrArg eA hk
      exact mul_left_cancel₀ (hu ⟨_, k, rfl⟩).ne_zero hk'
    · intro h
      rw [heA h]
  intro x y hxy
  have : φ2 x = φ2 y := by rw [← hEθ]; simp only [RingHom.comp_apply, hxy]
  exact Subtype.val_injective (hΛinj this)

/-- Generic form of the values of `θ : A[I/a] → S` in a field `K`: `E (θ (i / a)) = eA i / eA a`. -/
theorem embed_theta_frac {A S K : Type*} [CommRing A] [CommRing S] [Field K] {I : Ideal A} {a : A}
    (ψ : A →+* S) (E : S →+* K) (eA : A →+* K) (hE : ∀ r, E (ψ r) = eA r) (ha : eA a ≠ 0)
    (θ : chartAlgebra I a →+* S) (hθ : θ.comp (algebraMap A (chartAlgebra I a)) = ψ) {i : A} (hi : i ∈ I) :
    E (θ (chartAlgebra.frac hi)) = eA i / eA a := by
  have h := congrArg (fun x => E (θ x)) (chartAlgebra.algebraMap_mul_frac (a := a) hi)
  simp only [map_mul] at h
  have h1 : ∀ r, θ (algebraMap A (chartAlgebra I a) r) = ψ r := fun r => RingHom.congr_fun hθ r
  rw [h1, h1, hE, hE] at h
  rw [eq_div_iff ha, mul_comm]
  exact h

/-- Generic: `E (θ (algebraMap r)) = eA r`. -/
theorem embed_theta_algebraMap {A S K : Type*} [CommRing A] [CommRing S] [Field K] {I : Ideal A} {a : A}
    (ψ : A →+* S) (E : S →+* K) (eA : A →+* K) (hE : ∀ r, E (ψ r) = eA r)
    (θ : chartAlgebra I a →+* S) (hθ : θ.comp (algebraMap A (chartAlgebra I a)) = ψ) (r : A) :
    E (θ (algebraMap A (chartAlgebra I a) r)) = eA r := by
  have h1 : θ (algebraMap A (chartAlgebra I a) r) = ψ r := RingHom.congr_fun hθ r
  rw [h1, hE]

/-- Generic: the element `(i / a) * r` of `A[I/a]` has `E (θ ·) = eA i / eA a * eA r`. -/
theorem embed_theta_frac_mul {A S K : Type*} [CommRing A] [CommRing S] [Field K] {I : Ideal A} {a : A}
    (ψ : A →+* S) (E : S →+* K) (eA : A →+* K) (hE : ∀ r, E (ψ r) = eA r) (ha : eA a ≠ 0)
    (θ : chartAlgebra I a →+* S) (hθ : θ.comp (algebraMap A (chartAlgebra I a)) = ψ) {i : A} (hi : i ∈ I)
    (r : A) : ∃ x : chartAlgebra I a, E (θ x) = eA i / eA a * eA r := by
  refine ⟨chartAlgebra.frac hi * algebraMap A (chartAlgebra I a) r, ?_⟩
  rw [map_mul θ, map_mul E, embed_theta_frac ψ E eA hE ha θ hθ hi, embed_theta_algebraMap ψ E eA hE θ hθ]

/-- A ring homomorphism whose range contains the image of `R` and a generating set of the `R`-algebra `S`
is surjective. -/
theorem surjective_of_adjoin_eq_top {R C S : Type*} [CommRing R] [CommRing C] [CommRing S] [Algebra R S]
    (θ : C →+* S) {Gen : Set S} (hgen : Algebra.adjoin R Gen = ⊤)
    (h1 : ∀ r : R, algebraMap R S r ∈ θ.range) (h2 : ∀ x ∈ Gen, x ∈ θ.range) :
    Function.Surjective θ := by
  intro z
  have hz : z ∈ Algebra.adjoin R Gen := by rw [hgen]; trivial
  have : z ∈ θ.range := by
    induction hz using Algebra.adjoin_induction with
    | mem x hx => exact h2 x hx
    | algebraMap r => exact h1 r
    | add x y _ _ hx hy => exact add_mem hx hy
    | mul x y _ _ hx hy => exact mul_mem hx hy
  exact this

section Domain

variable [IsDomain (MvPolynomial (Fin n) B ⧸ 𝔭.toIdeal)]

/-- The fraction field of `H`, in which the charts of `Proj H` and `Proj H'` are compared. -/
abbrev FracH := FractionRing (MvPolynomial (Fin n) B ⧸ 𝔭.toIdeal)

/-- `H ↪ Frac H`. -/
noncomputable def jA : MvPolynomial (Fin n) B ⧸ 𝔭.toIdeal →+* FracH 𝔭 :=
  algebraMap (MvPolynomial (Fin n) B ⧸ 𝔭.toIdeal) (FracH 𝔭)

/-- `H' ↪ H ↪ Frac H`. -/
noncomputable def jB : MvPolynomial (Fin (N * n)) B ⧸ (kerIdeal 𝔭 g hg).toIdeal →+* FracH 𝔭 :=
  (jA 𝔭).comp (incl 𝔭 g hg).toRingHom

/-- `jA` is injective. -/
theorem jA_injective : Function.Injective (jA 𝔭) := IsFractionRing.injective _ _

/-- `jB` is injective. -/
theorem jB_injective : Function.Injective (jB 𝔭 g hg) :=
  (jA_injective 𝔭).comp (incl_injective 𝔭 g hg)

/-- `jB` is `incl` followed by `jA`. -/
theorem jB_apply (x : MvPolynomial (Fin (N * n)) B ⧸ (kerIdeal 𝔭 g hg).toIdeal) :
    jB 𝔭 g hg x = jA 𝔭 (incl 𝔭 g hg x) := rfl

/-- `jB (κ_a x) = jA (g_a) ^ d * jA x` for `x ∈ H_d`. -/
theorem jB_kappa (a : Fin N) {d : ℕ} {x : MvPolynomial (Fin n) B ⧸ 𝔭.toIdeal}
    (hx : x ∈ quotientGrading 𝔭 d) : jB 𝔭 g hg (kappa 𝔭 g hg a x) = jA 𝔭 (g a) ^ d * jA 𝔭 x := by
  rw [jB_apply, incl_kappa 𝔭 g hg a hx, map_mul, map_pow]

/-- The element `y_{ab} = κ_a (u_b) = g_a u_b` of `H'` (degree one). -/
noncomputable def fab (a : Fin N) (b : Fin n) : MvPolynomial (Fin (N * n)) B ⧸ (kerIdeal 𝔭 g hg).toIdeal :=
  kappa 𝔭 g hg a (quotientGrading.var 𝔭 b)

/-- `y_{ab}` has degree one in `H'`. -/
theorem fab_mem (a : Fin N) (b : Fin n) : fab 𝔭 g hg a b ∈ quotientGrading (kerIdeal 𝔭 g hg) 1 :=
  kappa_mem 𝔭 g hg a (quotientGrading.var_mem 𝔭 b)

/-- `jB (y_{ab}) = g_a u_b` in the fraction field. -/
theorem jB_fab (a : Fin N) (b : Fin n) :
    jB 𝔭 g hg (fab 𝔭 g hg a b) = jA 𝔭 (g a) * jA 𝔭 (quotientGrading.var 𝔭 b) := by
  rw [fab, jB_kappa 𝔭 g hg a (quotientGrading.var_mem 𝔭 b), pow_one]

/-- `fab a b` is the variable `V_{(a,b)}` of `H'`. -/
theorem fab_eq_var (a : Fin N) (b : Fin n) :
    fab 𝔭 g hg a b = quotientGrading.var (kerIdeal 𝔭 g hg) (idx a b) := by
  simp [fab, kappa_mk, quotientGrading.var, subst, idx]

/-- The chart map `ρ_{ab} : H_(u_b) → H'_(y_{ab})`, `x / u_b ^ d ↦ κ_a x / y_{ab} ^ d`. -/
noncomputable def rho (a : Fin N) (b : Fin n) :
    Away (quotientGrading 𝔭) (quotientGrading.var 𝔭 b) →+*
      Away (quotientGrading (kerIdeal 𝔭 g hg)) (fab 𝔭 g hg a b) :=
  Away.map (kappaGraded 𝔭 g hg a) (quotientGrading.var 𝔭 b)

/-- `ρ_{ab}` on the fraction `x / u_b ^ d`. -/
theorem rho_mk (a : Fin N) (b : Fin n) (d : ℕ) (x : MvPolynomial (Fin n) B ⧸ 𝔭.toIdeal)
    (hx : x ∈ quotientGrading 𝔭 (d • 1)) :
    rho 𝔭 g hg a b (Away.mk (quotientGrading 𝔭) (quotientGrading.var_mem 𝔭 b) d x hx) =
      Away.mk (quotientGrading (kerIdeal 𝔭 g hg)) (fab_mem 𝔭 g hg a b) d (kappa 𝔭 g hg a x)
        (by simpa using kappa_mem 𝔭 g hg a (by simpa using hx)) :=
  Away.map_mk _ _ _ _ _ _

/-- The chart maps `ρ_{ab}` are compatible with the embeddings into `Frac H`. -/
theorem awayEmb_rho (a : Fin N) (b : Fin n) (hf0 : jB 𝔭 g hg (fab 𝔭 g hg a b) ≠ 0)
    (hu0 : jA 𝔭 (quotientGrading.var 𝔭 b) ≠ 0)
    (z : Away (quotientGrading 𝔭) (quotientGrading.var 𝔭 b)) :
    awayEmb (quotientGrading (kerIdeal 𝔭 g hg)) (jB 𝔭 g hg) (fab 𝔭 g hg a b) hf0 (rho 𝔭 g hg a b z) =
      awayEmb (quotientGrading 𝔭) (jA 𝔭) (quotientGrading.var 𝔭 b) hu0 z := by
  obtain ⟨d, x, hx, rfl⟩ := Away.mk_surjective (quotientGrading 𝔭) (quotientGrading.var_mem 𝔭 b) z
  have hga : jA 𝔭 (g a) ≠ 0 := by
    intro h; apply hf0; rw [jB_fab, h, zero_mul]
  rw [rho_mk, awayEmb_mk hf0, awayEmb_mk hu0, jB_kappa 𝔭 g hg a (by simpa using hx), jB_fab]
  field_simp
  rw [mul_pow]; ring

/-- `y_{ab} ≠ 0` forces `u_b ≠ 0` and `g_a ≠ 0` (in the fraction field). -/
theorem jA_var_ne_zero {a : Fin N} {b : Fin n} (h : jB 𝔭 g hg (fab 𝔭 g hg a b) ≠ 0) :
    jA 𝔭 (quotientGrading.var 𝔭 b) ≠ 0 := by
  intro h0; apply h; rw [jB_fab, h0, mul_zero]

/-- `y_{ab} ≠ 0` forces `g_a ≠ 0`. -/
theorem jA_gen_ne_zero {a : Fin N} {b : Fin n} (h : jB 𝔭 g hg (fab 𝔭 g hg a b) ≠ 0) :
    jA 𝔭 (g a) ≠ 0 := by
  intro h0; apply h; rw [jB_fab, h0, zero_mul]

/-- **Gluing condition.**  On the overlap `D₊(y_{ab}) ∩ D₊(y_{cd})` of two charts of `Proj H'` the two maps
`Spec H'_(y_{ab}) → Spec H_(u_b) → Proj H` and `Spec H'_(y_{cd}) → Spec H_(u_d) → Proj H` agree. -/
theorem pullback_fst_comp_eq {a c : Fin N} {b d : Fin n} (hab : jB 𝔭 g hg (fab 𝔭 g hg a b) ≠ 0)
    (hcd : jB 𝔭 g hg (fab 𝔭 g hg c d) ≠ 0) :
    Limits.pullback.fst (Proj.awayι (quotientGrading (kerIdeal 𝔭 g hg)) (fab 𝔭 g hg a b)
          (fab_mem 𝔭 g hg a b) one_pos)
        (Proj.awayι (quotientGrading (kerIdeal 𝔭 g hg)) (fab 𝔭 g hg c d) (fab_mem 𝔭 g hg c d) one_pos) ≫
      (Spec.map (CommRingCat.ofHom (rho 𝔭 g hg a b)) ≫
        Proj.awayι (quotientGrading 𝔭) (quotientGrading.var 𝔭 b) (quotientGrading.var_mem 𝔭 b) one_pos) =
    Limits.pullback.snd (Proj.awayι (quotientGrading (kerIdeal 𝔭 g hg)) (fab 𝔭 g hg a b)
          (fab_mem 𝔭 g hg a b) one_pos)
        (Proj.awayι (quotientGrading (kerIdeal 𝔭 g hg)) (fab 𝔭 g hg c d) (fab_mem 𝔭 g hg c d) one_pos) ≫
      (Spec.map (CommRingCat.ofHom (rho 𝔭 g hg c d)) ≫
        Proj.awayι (quotientGrading 𝔭) (quotientGrading.var 𝔭 d) (quotientGrading.var_mem 𝔭 d) one_pos) := by
  have := isDomain_quotient 𝔭 g hg
  have hw0 : jB 𝔭 g hg (fab 𝔭 g hg a b * fab 𝔭 g hg c d) ≠ 0 := by
    rw [map_mul]; exact mul_ne_zero hab hcd
  have hb0 := jA_var_ne_zero 𝔭 g hg hab
  have hd0 := jA_var_ne_zero 𝔭 g hg hcd
  have hga := jA_gen_ne_zero 𝔭 g hg hab
  have hgc := jA_gen_ne_zero 𝔭 g hg hcd
  refine ProjChart.pullback_fst_comp_eq (jB_injective 𝔭 g hg) (quotientGrading.var_mem 𝔭 b)
    (quotientGrading.var_mem 𝔭 d) (fab_mem 𝔭 g hg a b) (fab_mem 𝔭 g hg c d) hb0 hd0 hab hcd hw0
    (rho 𝔭 g hg a b) (rho 𝔭 g hg c d) (awayEmb_rho 𝔭 g hg a b hab hb0)
    (awayEmb_rho 𝔭 g hg c d hcd hd0) ?_
  have hw : fab 𝔭 g hg a b * fab 𝔭 g hg c b ∈
      quotientGrading (kerIdeal 𝔭 g hg) (1 • (1 + 1)) := by
    simpa using SetLike.mul_mem_graded (fab_mem 𝔭 g hg a b) (fab_mem 𝔭 g hg c b)
  refine ⟨Away.mk _ (SetLike.mul_mem_graded (fab_mem 𝔭 g hg a b) (fab_mem 𝔭 g hg c d)) 1
    (fab 𝔭 g hg a b * fab 𝔭 g hg c b) hw, ?_⟩
  rw [awayEmb_mk hw0, pow_one, map_mul, map_mul, jB_fab, jB_fab, jB_fab]
  field_simp

/-- The chart `D₊(u_b)` of `Proj H` as an affine open. -/
noncomputable abbrev chartU (b : Fin n) : (Proj (quotientGrading 𝔭)).affineOpens :=
  ProjChart.basicAffineOpen (quotientGrading 𝔭) (quotientGrading.var_mem 𝔭 b) one_pos

/-- `H_(u_b) ≃+* Γ(Proj H, D₊(u_b))`. -/
noncomputable def sigma (b : Fin n) :
    Away (quotientGrading 𝔭) (quotientGrading.var 𝔭 b) ≃+* Γ(Proj (quotientGrading 𝔭), (chartU 𝔭 b : _)) :=
  RingEquiv.ofBijective (Proj.awayToSection (quotientGrading 𝔭) (quotientGrading.var 𝔭 b)).hom
    (ProjChart.bijective_awayToSection (quotientGrading 𝔭) (quotientGrading.var_mem 𝔭 b) one_pos)

/-- The fraction `γ_{cb} = g_c / u_b ^ e` as a section over `D₊(u_b)`. -/
noncomputable def gammaSec (b : Fin n) (c : Fin N) : Γ(Proj (quotientGrading 𝔭), (chartU 𝔭 b : _)) :=
  sigma 𝔭 b (ProjChart.frac (quotientGrading 𝔭) (quotientGrading.var_mem 𝔭 b) e (g c) (hg c))

/-- The ring map `ψ_{ab} : Γ(D₊(u_b)) → H'_(y_{ab})`. -/
noncomputable def psi (a : Fin N) (b : Fin n) :
    Γ(Proj (quotientGrading 𝔭), (chartU 𝔭 b : _)) →+*
      Away (quotientGrading (kerIdeal 𝔭 g hg)) (fab 𝔭 g hg a b) :=
  (rho 𝔭 g hg a b).comp (sigma 𝔭 b).symm.toRingHom

/-- The embedding `H'_(y_{ab}) → Frac H`. -/
noncomputable def embS (a : Fin N) (b : Fin n) (hab : jB 𝔭 g hg (fab 𝔭 g hg a b) ≠ 0) :
    Away (quotientGrading (kerIdeal 𝔭 g hg)) (fab 𝔭 g hg a b) →+* FracH 𝔭 :=
  awayEmb (quotientGrading (kerIdeal 𝔭 g hg)) (jB 𝔭 g hg) (fab 𝔭 g hg a b) hab

/-- The embedding `Γ(D₊(u_b)) ≅ H_(u_b) → Frac H`. -/
noncomputable def embU (b : Fin n) (hb0 : jA 𝔭 (quotientGrading.var 𝔭 b) ≠ 0) :
    Γ(Proj (quotientGrading 𝔭), (chartU 𝔭 b : _)) →+* FracH 𝔭 :=
  (awayEmb (quotientGrading 𝔭) (jA 𝔭) (quotientGrading.var 𝔭 b) hb0).comp (sigma 𝔭 b).symm.toRingHom

/-- `embS` is injective. -/
theorem embS_injective (a : Fin N) (b : Fin n) (hab : jB 𝔭 g hg (fab 𝔭 g hg a b) ≠ 0) :
    Function.Injective (embS 𝔭 g hg a b hab) :=
  have := isDomain_quotient 𝔭 g hg
  awayEmb_injective (jB_injective 𝔭 g hg) hab

/-- `embU` is injective. -/
theorem embU_injective (b : Fin n) (hb0 : jA 𝔭 (quotientGrading.var 𝔭 b) ≠ 0) :
    Function.Injective (embU 𝔭 b hb0) :=
  (awayEmb_injective (jA_injective 𝔭) hb0).comp (sigma 𝔭 b).symm.injective

/-- `embS ∘ ψ_{ab} = embU`. -/
theorem embS_psi (a : Fin N) (b : Fin n) (hab : jB 𝔭 g hg (fab 𝔭 g hg a b) ≠ 0)
    (r : Γ(Proj (quotientGrading 𝔭), (chartU 𝔭 b : _))) :
    embS 𝔭 g hg a b hab (psi 𝔭 g hg a b r) = embU 𝔭 b (jA_var_ne_zero 𝔭 g hg hab) r :=
  awayEmb_rho 𝔭 g hg a b hab (jA_var_ne_zero 𝔭 g hg hab) _

/-- `embU (γ_{cb}) = g_c / u_b ^ e` in the fraction field. -/
theorem embU_gammaSec (b : Fin n) (hb0 : jA 𝔭 (quotientGrading.var 𝔭 b) ≠ 0) (c : Fin N) :
    embU 𝔭 b hb0 (gammaSec 𝔭 g hg b c) = jA 𝔭 (g c) / jA 𝔭 (quotientGrading.var 𝔭 b) ^ e := by
  simp only [embU, gammaSec, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
    RingEquiv.symm_apply_apply]
  exact awayEmb_mk hb0 (quotientGrading.var_mem 𝔭 b) e (g c) _

/-- The quotient `y_{cb} / y_{ab}` in `H'_(y_{ab})`. -/
noncomputable def quotY (a : Fin N) (b : Fin n) (c : Fin N) :
    Away (quotientGrading (kerIdeal 𝔭 g hg)) (fab 𝔭 g hg a b) :=
  Away.mk _ (fab_mem 𝔭 g hg a b) 1 (fab 𝔭 g hg c b) (by simpa using fab_mem 𝔭 g hg c b)

/-- `embS (y_{cb} / y_{ab}) = g_c / g_a`. -/
theorem embS_quotY (a : Fin N) (b : Fin n) (hab : jB 𝔭 g hg (fab 𝔭 g hg a b) ≠ 0) (c : Fin N) :
    embS 𝔭 g hg a b hab (quotY 𝔭 g hg a b c) = jA 𝔭 (g c) / jA 𝔭 (g a) := by
  have hb0 := jA_var_ne_zero 𝔭 g hg hab
  have hga := jA_gen_ne_zero 𝔭 g hg hab
  rw [quotY, embS, awayEmb_mk hab, pow_one, jB_fab, jB_fab]
  field_simp

section Theta

variable (a : Fin N) (b : Fin n) (hab : jB 𝔭 g hg (fab 𝔭 g hg a b) ≠ 0)
include hab

/-- `ψ_{ab} (γ_{ab}) ≠ 0`. -/
theorem psi_gamma_ne_zero : psi 𝔭 g hg a b (gammaSec 𝔭 g hg b a) ≠ 0 := by
  have hb0 := jA_var_ne_zero 𝔭 g hg hab
  have hga := jA_gen_ne_zero 𝔭 g hg hab
  intro h
  have := embS_psi 𝔭 g hg a b hab (gammaSec 𝔭 g hg b a)
  rw [h, map_zero, embU_gammaSec] at this
  exact div_ne_zero hga (pow_ne_zero _ hb0) this.symm

/-- `ψ_{ab} (γ_{ab}) * (y_{cb} / y_{ab}) = ψ_{ab} (γ_{cb})`. -/
theorem psi_gamma_mul_quotY (c : Fin N) :
    psi 𝔭 g hg a b (gammaSec 𝔭 g hg b a) * quotY 𝔭 g hg a b c = psi 𝔭 g hg a b (gammaSec 𝔭 g hg b c) := by
  have hb0 := jA_var_ne_zero 𝔭 g hg hab
  have hga := jA_gen_ne_zero 𝔭 g hg hab
  apply embS_injective 𝔭 g hg a b hab
  rw [map_mul, embS_psi, embS_psi, embS_quotY, embU_gammaSec, embU_gammaSec]
  field_simp

/-- Existence of the ring map `θ : Γ(D₊(u_b))[I / γ_{ab}] → H'_(y_{ab})` extending `ψ_{ab}`, by the universal property of the chart algebra. -/
theorem exists_theta_hom (I : Ideal Γ(Proj (quotientGrading 𝔭), (chartU 𝔭 b : _)))
    (hI : I = Ideal.span (Set.range (gammaSec 𝔭 g hg b))) :
    ∃ θ : chartAlgebra I (gammaSec 𝔭 g hg b a) →+*
        Away (quotientGrading (kerIdeal 𝔭 g hg)) (fab 𝔭 g hg a b),
      θ.comp (algebraMap _ _) = psi 𝔭 g hg a b := by
  have hnz : psi 𝔭 g hg a b (gammaSec 𝔭 g hg b a) ∈
      nonZeroDivisors (Away (quotientGrading (kerIdeal 𝔭 g hg)) (fab 𝔭 g hg a b)) :=
    have := isDomain_quotient 𝔭 g hg
    have : IsDomain (Away (quotientGrading (kerIdeal 𝔭 g hg)) (fab 𝔭 g hg a b)) :=
      (embS_injective 𝔭 g hg a b hab).isDomain (embS 𝔭 g hg a b hab)
    mem_nonZeroDivisors_of_ne_zero (psi_gamma_ne_zero 𝔭 g hg a b hab)
  have hI' : ∀ i ∈ I, ∃ c, psi 𝔭 g hg a b (gammaSec 𝔭 g hg b a) * c = psi 𝔭 g hg a b i := by
    intro i hi
    rw [hI, Ideal.mem_span_range_iff_exists_fun] at hi
    obtain ⟨r, rfl⟩ := hi
    refine ⟨∑ c, psi 𝔭 g hg a b (r c) * quotY 𝔭 g hg a b c, ?_⟩
    rw [Finset.mul_sum, map_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [map_mul, mul_left_comm, psi_gamma_mul_quotY 𝔭 g hg a b hab]
  exact chartAlgebra.exists_ringHom (A := Γ(Proj (quotientGrading 𝔭), (chartU 𝔭 b : _)))
    (I := I) (a := gammaSec 𝔭 g hg b a) (psi 𝔭 g hg a b) hnz hI'

/-- Any such `θ` is injective. -/
theorem theta_injective (I : Ideal Γ(Proj (quotientGrading 𝔭), (chartU 𝔭 b : _)))
    (θ : chartAlgebra I (gammaSec 𝔭 g hg b a) →+*
      Away (quotientGrading (kerIdeal 𝔭 g hg)) (fab 𝔭 g hg a b))
    (hθ : θ.comp (algebraMap _ _) = psi 𝔭 g hg a b) : Function.Injective θ := by
  have hb0 := jA_var_ne_zero 𝔭 g hg hab
  have hga := jA_gen_ne_zero 𝔭 g hg hab
  refine chartAlgebra_injective_of_embed (psi 𝔭 g hg a b) (embS 𝔭 g hg a b hab) (embU 𝔭 b hb0)
    (embU_injective 𝔭 b hb0) (embS_psi 𝔭 g hg a b hab) ?_ θ hθ
  rw [embU_gammaSec]
  exact div_ne_zero hga (pow_ne_zero _ hb0)

/-- The monomials `∏ y_k ^ {a_k} / y_{ab} ^ a` of `H'_(y_{ab})` are products of the fractions `y_k / y_{ab}`. -/
theorem mk_prod_eq (a' : ℕ) (ai : Fin (N * n) → ℕ) (hai : ∑ i, ai i • (fun _ : Fin (N * n) => 1) i = a' • 1) :
    Away.mk (quotientGrading (kerIdeal 𝔭 g hg)) (fab_mem 𝔭 g hg a b) a'
        (∏ i, quotientGrading.var (kerIdeal 𝔭 g hg) i ^ ai i) (hai ▸ SetLike.prod_pow_mem_graded _ _ _ _
          fun i _ => quotientGrading.var_mem (kerIdeal 𝔭 g hg) i) =
      ∏ k, Away.mk (quotientGrading (kerIdeal 𝔭 g hg)) (fab_mem 𝔭 g hg a b) 1
        (quotientGrading.var (kerIdeal 𝔭 g hg) k)
        (by simpa using quotientGrading.var_mem (kerIdeal 𝔭 g hg) k) ^ ai k := by
  have hdom := isDomain_quotient 𝔭 g hg
  have hsum : ∑ i, ai i = a' := by simpa using hai
  apply embS_injective 𝔭 g hg a b hab
  show awayEmb _ _ _ hab _ = awayEmb _ _ _ hab _
  rw [awayEmb_mk hab, map_prod, map_prod]
  simp only [map_pow, awayEmb_mk hab, pow_one, div_pow, Finset.prod_div_distrib,
    Finset.prod_pow_eq_pow_sum, hsum]

section ThetaSurj

variable (I : Ideal Γ(Proj (quotientGrading 𝔭), (chartU 𝔭 b : _)))
  (hI : I = Ideal.span (Set.range (gammaSec 𝔭 g hg b)))
  (θ : chartAlgebra I (gammaSec 𝔭 g hg b a) →+*
      Away (quotientGrading (kerIdeal 𝔭 g hg)) (fab 𝔭 g hg a b))
  (hθ : θ.comp (algebraMap _ _) = psi 𝔭 g hg a b)
include hI hθ

set_option maxHeartbeats 400000 in
/-- The fraction `y_{cd} / y_{ab}` lies in the range of `θ`. -/
theorem quotient_mem_range_theta (c : Fin N) (d : Fin n) :
    Away.mk (quotientGrading (kerIdeal 𝔭 g hg)) (fab_mem 𝔭 g hg a b) 1 (fab 𝔭 g hg c d)
      (by simpa using fab_mem 𝔭 g hg c d) ∈ θ.range := by
  have hb0 := jA_var_ne_zero 𝔭 g hg hab
  have hga := jA_gen_ne_zero 𝔭 g hg hab
  have hdom := isDomain_quotient 𝔭 g hg
  have hc : gammaSec 𝔭 g hg b c ∈ I := by rw [hI]; exact Ideal.subset_span ⟨c, rfl⟩
  have hγa : embU 𝔭 b hb0 (gammaSec 𝔭 g hg b a) ≠ 0 := by
    rw [embU_gammaSec]; exact div_ne_zero hga (pow_ne_zero _ hb0)
  let u : Away (quotientGrading 𝔭) (quotientGrading.var 𝔭 b) :=
    Away.mk _ (quotientGrading.var_mem 𝔭 b) 1 (quotientGrading.var 𝔭 d)
      (by simpa using quotientGrading.var_mem 𝔭 d)
  obtain ⟨x, hx⟩ := embed_theta_frac_mul (psi 𝔭 g hg a b) (embS 𝔭 g hg a b hab) (embU 𝔭 b hb0)
    (fun r => embS_psi 𝔭 g hg a b hab r) hγa θ hθ hc (sigma 𝔭 b u)
  have h2' : embU 𝔭 b hb0 (sigma 𝔭 b u) =
      jA 𝔭 (quotientGrading.var 𝔭 d) / jA 𝔭 (quotientGrading.var 𝔭 b) := by
    simp only [embU, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
      RingEquiv.symm_apply_apply, u]
    rw [awayEmb_mk hb0, pow_one]
  refine ⟨x, embS_injective 𝔭 g hg a b hab ?_⟩
  rw [hx, h2', embU_gammaSec, embU_gammaSec]
  show _ = awayEmb _ _ _ hab _
  rw [awayEmb_mk hab, pow_one, jB_fab, jB_fab]
  field_simp

set_option maxHeartbeats 400000 in
/-- The fractions `y_k / y_{ab}` lie in the range of `θ`. -/
theorem W_mem_range_theta (k : Fin (N * n)) :
    Away.mk (quotientGrading (kerIdeal 𝔭 g hg)) (fab_mem 𝔭 g hg a b) 1
      (quotientGrading.var (kerIdeal 𝔭 g hg) k)
      (by simpa using quotientGrading.var_mem (kerIdeal 𝔭 g hg) k) ∈ θ.range := by
  obtain ⟨⟨c, d⟩, hk⟩ := finProdFinEquiv.surjective k
  have hv : quotientGrading.var (kerIdeal 𝔭 g hg) k = fab 𝔭 g hg c d := by
    rw [fab_eq_var, ← hk]; rfl
  have h := quotient_mem_range_theta 𝔭 g hg a b hab I hI θ hθ c d
  have e := ProjChart.away_mk_congr (quotientGrading (kerIdeal 𝔭 g hg)) (fab_mem 𝔭 g hg a b)
    (n₁ := 1) (n₂ := 1) rfl hv (by simpa using quotientGrading.var_mem (kerIdeal 𝔭 g hg) k)
    (by simpa using fab_mem 𝔭 g hg c d)
  rw [e]
  exact h

set_option maxHeartbeats 400000 in
/-- `θ` is surjective: its range contains the image of `H'_0` and the generators `y_{cd} / y_{ab}` of `H'_(y_{ab})`. -/
theorem theta_surjective : Function.Surjective θ := by
  have hb0 := jA_var_ne_zero 𝔭 g hg hab
  have hdom := isDomain_quotient 𝔭 g hg
  have hf := fab_mem 𝔭 g hg a b
  have hgen := Away.adjoin_mk_prod_pow_eq_top (𝒜 := quotientGrading (kerIdeal 𝔭 g hg)) hf
    (Fin (N * n)) (fun k => quotientGrading.var (kerIdeal 𝔭 g hg) k)
    (quotientGrading.adjoin_range_var (kerIdeal 𝔭 g hg)) (fun _ => 1)
    (fun k => quotientGrading.var_mem (kerIdeal 𝔭 g hg) k)
  refine surjective_of_adjoin_eq_top θ hgen ?_ ?_
  · -- the image of `H'_0`
    intro c
    obtain ⟨b', rfl⟩ := algebraMap_quotientGrading_zero_surjective (kerIdeal 𝔭 g hg) c
    let r0 : Γ(Proj (quotientGrading 𝔭), (chartU 𝔭 b : _)) := sigma 𝔭 b
      (algebraMap (quotientGrading 𝔭 0) _ (algebraMap B (quotientGrading 𝔭 0) b'))
    refine ⟨algebraMap _ _ r0, embS_injective 𝔭 g hg a b hab ?_⟩
    rw [embed_theta_algebraMap (psi 𝔭 g hg a b) (embS 𝔭 g hg a b hab) (embU 𝔭 b hb0)
      (fun r => embS_psi 𝔭 g hg a b hab r) θ hθ r0]
    have e1 : embU 𝔭 b hb0 r0 = jA 𝔭 (algebraMap B (MvPolynomial (Fin n) B ⧸ 𝔭.toIdeal) b') := by
      simp only [embU, r0, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
        RingEquiv.symm_apply_apply]
      rw [awayEmb_algebraMap]
      rfl
    have e2 : embS 𝔭 g hg a b hab (algebraMap (quotientGrading (kerIdeal 𝔭 g hg) 0) _
        (algebraMap B (quotientGrading (kerIdeal 𝔭 g hg) 0) b')) =
        jA 𝔭 (algebraMap B (MvPolynomial (Fin n) B ⧸ 𝔭.toIdeal) b') := by
      show awayEmb _ _ _ hab _ = _
      rw [awayEmb_algebraMap, jB_apply]
      congr 1
      exact (incl 𝔭 g hg).commutes b'
    rw [e1, e2]
  · rintro _ ⟨a', ai, hai, hle, rfl⟩
    have hW := W_mem_range_theta 𝔭 g hg a b hab I hI θ hθ
    rw [mk_prod_eq 𝔭 g hg a b hab a' ai hai]
    exact prod_mem fun k _ => pow_mem (hW k) _

end ThetaSurj

/-- **The chart rings agree**: for the ideal `I = (γ_{cb})_c` of the center on `D₊(u_b)`, the chart algebra
`Γ(D₊(u_b))[I / γ_{ab}]` of the monoidal transformation is isomorphic to `H'_(y_{ab})`, by a ring isomorphism
extending `ψ_{ab} : Γ(D₊(u_b)) → H'_(y_{ab})`. -/
theorem exists_theta (I : Ideal Γ(Proj (quotientGrading 𝔭), (chartU 𝔭 b : _)))
    (hI : I = Ideal.span (Set.range (gammaSec 𝔭 g hg b))) :
    ∃ θ : chartAlgebra I (gammaSec 𝔭 g hg b a) →+*
        Away (quotientGrading (kerIdeal 𝔭 g hg)) (fab 𝔭 g hg a b),
      θ.comp (algebraMap _ _) = psi 𝔭 g hg a b ∧ Function.Bijective θ := by
  have hex := exists_theta_hom 𝔭 g hg a b hab I hI
  obtain ⟨θ, hθ⟩ := hex
  have h1 := theta_injective 𝔭 g hg a b hab I θ hθ
  have h2 := theta_surjective 𝔭 g hg a b hab I hI θ hθ
  exact ⟨θ, hθ, h1, h2⟩

end Theta

section Cover

/-- The indices `(a, b)` with `y_{ab} ≠ 0`, i.e. the non-empty standard charts of `Proj H'`. -/
abbrev NZIdx : Type := {p : Fin N × Fin n // fab 𝔭 g hg p.1 p.2 ≠ 0}

/-- The irrelevant ideal of `H'` is spanned by the nonzero `y_{ab}`. -/
theorem irrelevant_le_span_fab :
    (HomogeneousIdeal.irrelevant (quotientGrading (kerIdeal 𝔭 g hg))).toIdeal ≤
      Ideal.span (Set.range fun p : NZIdx 𝔭 g hg => fab 𝔭 g hg p.1.1 p.1.2) := by
  classical
  set 𝒬 := quotientGrading (kerIdeal 𝔭 g hg)
  have hgen : ∀ x ∈ (HomogeneousIdeal.irrelevant 𝒬).toIdeal,
      x ∈ Ideal.span (Set.range (quotientGrading.var (kerIdeal 𝔭 g hg))) := by
    intro x hx
    convert_to x - GradedRing.projZeroRingHom 𝒬 x ∈ _
    · rw [GradedRing.projZeroRingHom_apply, ← GradedRing.proj_apply,
        (HomogeneousIdeal.mem_irrelevant_iff _ _).mp hx, sub_zero]
    clear hx
    have := (eq_iff_iff.mp congr(x ∈ $(quotientGrading.adjoin_range_var (kerIdeal 𝔭 g hg)))).mpr trivial
    induction this using Algebra.adjoin_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      rw [GradedRing.projZeroRingHom_apply, DirectSum.decompose_of_mem_ne 𝒬
        (quotientGrading.var_mem (kerIdeal 𝔭 g hg) i) one_ne_zero, sub_zero]
      exact Ideal.subset_span ⟨_, rfl⟩
    | algebraMap r =>
      convert! zero_mem (Ideal.span _)
      rw [sub_eq_zero]
      exact (DirectSum.decompose_of_mem_same 𝒬 r.2).symm
    | add x y hx hy _ _ =>
      rw [map_add, add_sub_add_comm]
      exact add_mem ‹_› ‹_›
    | mul x y hx hy hx' hy' =>
      convert!
        add_mem (Ideal.mul_mem_left _ x hy')
          (Ideal.mul_mem_right (GradedRing.projZeroRingHom 𝒬 y) _ hx') using 1
      rw [map_mul]
      ring
  intro x hx
  refine Ideal.span_le.mpr ?_ (hgen x hx)
  rintro _ ⟨k, rfl⟩
  obtain ⟨⟨c, d⟩, hk⟩ := finProdFinEquiv.surjective k
  have hv : quotientGrading.var (kerIdeal 𝔭 g hg) k = fab 𝔭 g hg c d := by
    rw [fab_eq_var, ← hk]; rfl
  rw [hv]
  by_cases h0 : fab 𝔭 g hg c d = 0
  · rw [h0]; exact zero_mem _
  · exact Ideal.subset_span ⟨⟨(c, d), h0⟩, rfl⟩

/-- The open cover of `Proj H'` by the non-empty standard charts `D₊(y_{ab}) = Spec H'_(y_{ab})`. -/
noncomputable def chartCover : (Proj (quotientGrading (kerIdeal 𝔭 g hg))).OpenCover :=
  (Proj.affineOpenCoverOfIrrelevantLESpan (quotientGrading (kerIdeal 𝔭 g hg))
    (fun p : NZIdx 𝔭 g hg => fab 𝔭 g hg p.1.1 p.1.2) (m := fun _ => 1)
    (fun p => fab_mem 𝔭 g hg p.1.1 p.1.2) (fun _ => one_pos) (irrelevant_le_span_fab 𝔭 g hg)).openCover

set_option maxHeartbeats 400000 in
/-- The morphism `π : Proj H' → Proj H`, glued from the chart maps `Spec H'_(y_{ab}) → Spec H_(u_b) → Proj H` over the
open cover of `Proj H'` by the charts `D₊(y_{ab})` (Mathlib's `Scheme.OpenCover.glueMorphisms`; the gluing
condition is `pullback_fst_comp_eq`). -/
noncomputable def toBase : Proj (quotientGrading (kerIdeal 𝔭 g hg)) ⟶ Proj (quotientGrading 𝔭) :=
  (chartCover 𝔭 g hg).glueMorphisms
    (fun p => Spec.map (CommRingCat.ofHom (rho 𝔭 g hg p.1.1 p.1.2)) ≫
      Proj.awayι (quotientGrading 𝔭) (quotientGrading.var 𝔭 p.1.2)
        (quotientGrading.var_mem 𝔭 p.1.2) one_pos)
    (fun p q => pullback_fst_comp_eq 𝔭 g hg
      (fun h => p.2 (jB_injective 𝔭 g hg (by rw [h, map_zero])))
      (fun h => q.2 (jB_injective 𝔭 g hg (by rw [h, map_zero]))))

set_option maxHeartbeats 400000 in
/-- On the chart `D₊(y_{ab})`, `π` is `Spec ρ_{ab}` followed by `D₊(u_b) ↪ Proj H`. -/
theorem awayι_comp_toBase (p : NZIdx 𝔭 g hg) :
    Proj.awayι (quotientGrading (kerIdeal 𝔭 g hg)) (fab 𝔭 g hg p.1.1 p.1.2) (fab_mem 𝔭 g hg p.1.1 p.1.2)
        one_pos ≫ toBase 𝔭 g hg =
      Spec.map (CommRingCat.ofHom (rho 𝔭 g hg p.1.1 p.1.2)) ≫
        Proj.awayι (quotientGrading 𝔭) (quotientGrading.var 𝔭 p.1.2)
          (quotientGrading.var_mem 𝔭 p.1.2) one_pos :=
  (chartCover 𝔭 g hg).ι_glueMorphisms _ _ p

end Cover

end Domain

end BlowupRing

end Hironaka
