/-
Copyright (c) 2026 Daattavya Aggarwal, Minhyong Kim, Oisin Kim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daattavya Aggarwal, Minhyong Kim, Oisin Kim
-/
module

public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
public import Mathlib.RingTheory.Coalgebra.IsFrobenius
public import Mathlib.RingTheory.Finiteness.Quotient
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.HopfAlgebra.Basic
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Architect
public import Hironaka.Ch3.Transforms
public import Hironaka.Statements

/-!
# Resolving a curve germ by point blow-ups (Ch. III §3, proof of Theorem 1, p. 218)

> Thus we shall assume that R is complete and dim(R/P) = 1. Let S = R/P. Then we know that the
> derived normal ring of S in its field of quotients is an S-module of finite type and that every
> localization of the derived normal ring is regular. In view of these facts, it is not difficult
> to show that there exists a finite sequence of successive monoidal transforms with center the
> maximal ideals, R = R₀ → R₁ → ⋯ → R_s, such that:
> (i) R_i is residually algebraic over R_{i-1} for i = 1, 2, …, s;
> (ii) for each i ≥ 1, there exists a prime ideal P_i in R_i such that R_P = (R_i)_{P_i}; and
> (iii) R_s/P_s is regular.

`CurveResolvable R P` records the existence of such a sequence, inductively: either `R/P` is
regular (`s = 0`), or there is a monoidal transform `R'` of `R` with center the maximal ideal
(`MonoidalTransform`, Ch. III §2), residually algebraic over `R`, and a prime `P'` of `R'` lying
over `P` with `R_P ≅ R'_{P'}` canonically, such that `(R', P')` is again resolvable.

Formalization note (encoding): the paper identifies local rings inside the field of quotients of `R`
("`R_P = (R_i)_{P_i}`"); here this is the bijectivity of the canonical local homomorphism
`R_P → R'_{P'}`.
-/

@[expose] public section

open IsLocalRing Polynomial

namespace Hironaka

universe u

/-- A regular local ring `R` with a prime `P` admits a finite sequence of monoidal transforms with
center the maximal ideals satisfying (i)–(iii) of p. 218. -/
inductive CurveResolvable : (R : Type u) → [CommRing R] → [IsRegularLocalRing R] → [IsDomain R] →
    (P : Ideal R) → Prop
  /-- `s = 0`: `R/P` is regular. -/
  | regular {R : Type u} [CommRing R] [IsRegularLocalRing R] [IsDomain R] (P : Ideal R)
      (hP : IsRegularLocalRing (R ⧸ P)) : CurveResolvable R P
  /-- One monoidal transform `R → R'` with center the maximal ideal, residually algebraic, with a
  prime `P'` of `R'` over `P` such that `R_P → R'_{P'}` is an isomorphism. -/
  | step {R : Type u} [CommRing R] [IsRegularLocalRing R] [IsDomain R] (P : Ideal R) [P.IsPrime]
      (t : MonoidalTransform R (maximalIdeal R))
      (halg : RingHom.IsResiduallyAlgebraic (R := R) (R' := t.ring) t.toRing)
      (P' : Ideal t.ring) [P'.IsPrime] (hP' : P = P'.comap t.toRing)
      (hloc : Function.Bijective (Localization.localRingHom P P' t.toRing hP'))
      (hreg : IsRegularLocalRing t.ring)
      (h : @CurveResolvable t.ring _ hreg _ P') : CurveResolvable R P

/-! ### The derived normal ring of a complete local domain of dimension one -/

/-- A finite module over a noetherian ring complete for `I` is complete for `I`. -/
theorem curve_isAdicComplete_of_finite {R : Type u} [CommRing R] [IsNoetherianRing R] (I : Ideal R)
    [IsAdicComplete I R] (M : Type u) [AddCommGroup M] [Module R M] [Module.Finite R M] :
    IsAdicComplete I M := by
  rw [← AdicCompletion.of_bijective_iff]
  have hR : Function.Bijective (AdicCompletion.of I R) :=
    AdicCompletion.of_bijective_iff.mpr inferInstance
  let e : R ≃ₗ[R] AdicCompletion I R := LinearEquiv.ofBijective _ hR
  have h : ⇑(AdicCompletion.of I M) = ⇑(AdicCompletion.ofTensorProduct I M) ∘
      ⇑(LinearEquiv.rTensor M e) ∘ ⇑(TensorProduct.lid R M).symm := by
    funext m
    have h1 : AdicCompletion.of I R 1 = 1 := rfl
    simp [e, AdicCompletion.ofTensorProduct_tmul, h1]
  rw [h]
  exact (AdicCompletion.ofTensorProduct_bijective_of_finite_of_isNoetherian I M).comp
    ((LinearEquiv.bijective _).comp (LinearEquiv.bijective _))

/-- `I`-adic completeness of an `R`-algebra `B` is `I B`-adic completeness. -/
theorem curve_isAdicComplete_map {R B : Type*} [CommRing R] [CommRing B] [Algebra R B]
    (I : Ideal R) [h : IsAdicComplete I B] : IsAdicComplete (I.map (algebraMap R B)) B := by
  have key : ∀ (n : ℕ) (x y : B),
      x ≡ y [SMOD ((I.map (algebraMap R B)) ^ n • ⊤ : Submodule B B)] ↔
        x ≡ y [SMOD (I ^ n • ⊤ : Submodule R B)] := by
    intro n x y
    simp only [SModEq.sub_mem, Ideal.smul_top_eq_map, Submodule.restrictScalars_mem,
      smul_eq_mul, Ideal.mul_top, Ideal.map_pow]
  exact
    { haus' := fun x hx => IsHausdorff.haus' (I := I) x fun n => (key n x 0).1 (hx n)
      prec' := fun f hf => by
        obtain ⟨L, hL⟩ := IsPrecomplete.prec' (I := I) f fun hmn => (key _ _ _).1 (hf hmn)
        exact ⟨L, fun n => (key n _ _).2 (hL n)⟩ }

/-- A domain `B` finite over a complete noetherian local ring `R` is local: `B` is henselian for
`M B`, `B/MB` is artinian, and an element `a` with `a`, `1 - a` both non-units would give (Hensel's
lemma for `X² - X`) a non-trivial idempotent. (This is why the derived normal ring of `S = R/P` is
a local ring in the proof of `curveResolvable_of_isAdicComplete`.) -/
theorem curve_isLocalRing_of_finite {R B : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [IsAdicComplete (maximalIdeal R) R] [CommRing B] [IsDomain B] [Algebra R B]
    [Module.Finite R B] : IsLocalRing B := by
  set I := (maximalIdeal R).map (algebraMap R B)
  have : IsAdicComplete (maximalIdeal R) B := curve_isAdicComplete_of_finite _ B
  have : IsAdicComplete I B := curve_isAdicComplete_map _
  have hH : HenselianRing B I := inferInstance
  have hart : IsArtinianRing (B ⧸ I) := by
    let _ : Field (R ⧸ maximalIdeal R) := Ideal.Quotient.field _
    exact IsArtinianRing.of_finite (R ⧸ maximalIdeal R) (B ⧸ I)
  refine IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun a => ?_
  by_contra hcon
  push Not at hcon
  obtain ⟨ha, ha1⟩ := hcon
  obtain ⟨n, y, hy⟩ := IsArtinian.exists_pow_succ_smul_dvd (Ideal.Quotient.mk I a) (1 : B ⧸ I)
  set ā := Ideal.Quotient.mk I a
  simp only [smul_eq_mul, mul_one] at hy
  -- `c = ā y` fixes `āᵏ` (`k = n + 1`), so `e = cᵏ` is an idempotent with `e āᵏ = āᵏ`
  set k := n + 1
  have hc : ā ^ k * (ā * y) = ā ^ k := by
    rw [Nat.succ_eq_add_one] at hy
    calc ā ^ k * (ā * y) = ā * (ā ^ (n + 1) * y) := by ring
      _ = ā ^ k := by rw [hy]; ring
  have hcj : ∀ j : ℕ, (ā * y) ^ j * ā ^ k = ā ^ k := by
    intro j
    induction j with
    | zero => simp
    | succ j ih => rw [pow_succ, mul_assoc, mul_comm (ā * y), hc, ih]
  have he2 : (ā * y) ^ k * (ā * y) ^ k = (ā * y) ^ k := by
    calc (ā * y) ^ k * (ā * y) ^ k = ((ā * y) ^ k * ā ^ k) * y ^ k := by rw [mul_pow]; ring
      _ = (ā * y) ^ k := by rw [hcj, ← mul_pow]
  obtain ⟨y₀, rfl⟩ := Ideal.Quotient.mk_surjective y
  set e₀ := (a * y₀) ^ k
  have hmke : Ideal.Quotient.mk I e₀ = (ā * Ideal.Quotient.mk I y₀) ^ k := by
    simp [e₀, ā]
  -- Hensel's lemma for `X² - X` at `e₀`
  have hmem : e₀ ^ 2 - e₀ ∈ I := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_pow, hmke, sq, he2, sub_self]
  have hd : ((X ^ 2 - X : B[X]).derivative).eval e₀ = 2 * e₀ - 1 := by
    simp only [derivative_sub, derivative_X_pow, derivative_X, eval_sub, eval_mul, eval_C,
      eval_pow, eval_X, eval_one]
    norm_num
  obtain ⟨r, hr, hre⟩ := hH.is_henselian (X ^ 2 - X)
    (monic_X_pow_sub (by rw [degree_X]; norm_num)) e₀
    (by simpa only [eval_sub, eval_pow, eval_X] using hmem)
    (by
      refine IsUnit.of_mul_eq_one (Ideal.Quotient.mk I (2 * e₀ - 1)) ?_
      rw [hd, ← map_mul, ← map_one (Ideal.Quotient.mk I), ← sub_eq_zero, ← map_sub,
        Ideal.Quotient.eq_zero_iff_mem]
      have : (2 * e₀ - 1) * (2 * e₀ - 1) - 1 = 4 * (e₀ ^ 2 - e₀) := by ring
      rw [this]
      exact I.mul_mem_left _ hmem)
  have hr2 : r * (r - 1) = 0 := by
    have := hr.eq_zero
    simp only [eval_sub, eval_pow, eval_X] at this
    linear_combination this
  have hjac := hH.jac
  rcases mul_eq_zero.mp hr2 with h0 | h1
  · -- `r = 0`: then `e = 0`, so `āᵏ = 0`, `aᵏ ∈ I ⊆ jac(B)` and `1 - a` is a unit
    apply ha1
    have hek : Ideal.Quotient.mk I e₀ = 0 := by
      rw [h0, zero_sub, neg_mem_iff] at hre
      exact Ideal.Quotient.eq_zero_iff_mem.mpr hre
    have hak : a ^ k ∈ I := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_pow, ← hcj k, ← hmke, hek, zero_mul]
    have hu := Ideal.mem_jacobson_bot.mp (hjac hak) (-1)
    rw [mul_neg_one, neg_add_eq_sub, ← mul_neg_geom_sum] at hu
    exact isUnit_of_mul_isUnit_left hu
  · -- `r = 1`: then `e = 1`, so `aᵏ y₀ᵏ ≡ 1` and `a` is a unit
    apply ha
    have hek : e₀ - 1 ∈ I := by
      have : r = 1 := sub_eq_zero.mp h1
      rw [this, ← neg_sub, neg_mem_iff] at hre
      exact hre
    have hu := Ideal.mem_jacobson_bot.mp (hjac hek) 1
    rw [mul_one, sub_add_cancel] at hu
    have hrw : e₀ = a * (a ^ n * y₀ ^ (n + 1)) := by simp only [e₀, k]; ring
    rw [hrw] at hu
    exact isUnit_of_mul_isUnit_left hu


/-- Proof of Theorem 1, p. 218: "we know that the derived normal ring of `S` in its field of
quotients is an `S`-module of finite type". Cited leaf, a hypothesis.

Deviation from the paper (cited-leaf issue): the paper invokes this as a known fact ("we know
that") without a reference on p. 218; footnote 10 (p. 243) recalls the same fact ("Recall the
fact that this condition is satisfied by every complete noetherian local ring without nilpotent
elements"), so the leaf is cited (consistent with `lem:IV.AB-5-nagata-finite`).  The
reference (Nagata, *Local rings*, (32.1)) is supplied by the formalization, and the leaf is
stated for every complete noetherian local domain, more generally than the case `S = R/P`
(`R` complete regular, `dim S = 1`) used on p. 218. -/
@[blueprint "lem:III.1-derived-normal-ring-finite"
  (statement := /-- Let $S$ be a complete noetherian local domain. Then the derived normal ring
    of $S$ (the integral closure of $S$ in its field of quotients) is an $S$-module of finite
    type. (Proof of Theorem~1, p.~218: ``we know that the derived normal ring of $S$ in its field
    of quotients is an $S$-module of finite type''.) -/)
  (proof := /-- Cited, not proved in the paper: ``we know that the derived normal ring of $S$ in
    its field of quotients is an $S$-module of finite type'' (p.~218). A complete local ring is a
    Nagata (pseudo-geometric) ring: M.~Nagata, \emph{Local rings}, Interscience 1962, (32.1);
    Mathlib does not have this.

    \textbf{Cited-leaf issue.} The paper gives no reference on p.~218 (``we know that'');
    footnote~10 (p.~243) recalls the same fact (``Recall the fact that this condition is
    satisfied by every complete noetherian local ring without nilpotent elements''), so the leaf
    is cited. The reference is supplied by
    the formalization. The leaf is stated for every complete noetherian local
    domain, more generally than the case used on p.~218 ($S=R/P$ with $R$ complete regular
    and $\dim S=1$). -/)
  (latexEnv := "lemma")]
theorem curve_finite_integralClosure [Hironaka.Cited.CurveFiniteIntegralClosure.{u}] :
    ∀ (S : Type u) [CommRing S] [IsDomain S] [IsLocalRing S]
    [IsNoetherianRing S] [IsAdicComplete (maximalIdeal S) S],
    Module.Finite S (integralClosure S (FractionRing S)) :=
  @Hironaka.Cited.CurveFiniteIntegralClosure.curve_finite_integralClosure _

/-- The derived normal ring of a complete local domain `S` of dimension `≤ 1` is a valuation ring
(a discrete valuation ring or a field): it is local (`S` is henselian), noetherian, integrally
closed and of dimension `≤ 1` ("every localization of the derived normal ring is regular"). -/
theorem curve_valuationRing_integralClosure [Hironaka.Cited.CurveFiniteIntegralClosure.{u}] (S : Type u) [CommRing S] [IsDomain S]
    [IsLocalRing S] [IsNoetherianRing S] [IsAdicComplete (maximalIdeal S) S]
    (hdim : ringKrullDim S ≤ 1) : ValuationRing (integralClosure S (FractionRing S)) := by
  set V := integralClosure S (FractionRing S)
  have : Module.Finite S V := curve_finite_integralClosure S
  have : IsLocalRing V := curve_isLocalRing_of_finite (R := S)
  have : IsNoetherianRing V := IsNoetherianRing.of_finite S V
  have : Ring.KrullDimLE 1 S := Ring.krullDimLE_iff.mpr hdim
  have : Ring.DimensionLEOne S := ⟨fun hp0 hp => hp.isMaximal_of_ne_bot hp0⟩
  have : IsIntegrallyClosed V :=
    integralClosure.isIntegrallyClosedOfFiniteExtension (FractionRing S)
  by_cases hV : IsField V
  · let _ : Field V := hV.toField
    infer_instance
  · have hD : IsDedekindDomain V := { }
    have key := (IsDiscreteValuationRing.TFAE V hV).out 3 2
    exact key.mp hD

section CurveStep

attribute [local instance] RingHom.ker_isPrime

variable {F : Type*} [Field F] {S₀ : Type*} [CommRing S₀] [Algebra S₀ F]
  (V : Subalgebra S₀ F)

/-- The part `φ(R) ∩ V` of a subring `φ(R) ⊆ V` containing the image of `S₀`, as an
`S₀`-submodule of `V` (the measure of the induction in the proof of
`curveResolvable_of_isAdicComplete`). -/
def curveImage {R : Type*} [CommRing R] (φ : R →+* F)
    (hφS : ∀ s, algebraMap S₀ F s ∈ φ.range) : Submodule S₀ V where
  carrier := {v | (v : F) ∈ φ.range}
  add_mem' {a b} ha hb := by
    show (a : F) + b ∈ φ.range
    exact add_mem ha hb
  zero_mem' := by
    show (0 : F) ∈ φ.range
    exact zero_mem _
  smul_mem' c v hv := by
    show c • (v : F) ∈ φ.range
    rw [Algebra.smul_def]
    exact mul_mem (hφS c) hv

/-- The monoidal transform step of `exists_monoidalTransform_of_not_isRegularLocalRing_quotient`, for a given transform `t` with center the
maximal ideal and a map `ψ : R[M/x] → V` extending `φ` whose center on `R[M/x]` is `t.M'`. -/
theorem exists_curveImage_lt_of_lift [ValuationRing V]
    {R : Type u} [CommRing R] [IsRegularLocalRing R] [IsDomain R] {P : Ideal R} [P.IsPrime]
    (φ : R →+* F) (hφS : ∀ s, algebraMap S₀ F s ∈ φ.range)
    (hker : RingHom.ker φ = P) (hS : ¬ IsRegularLocalRing (R ⧸ P))
    (t : MonoidalTransform R (maximalIdeal R))
    (ψ : blowupAlgebra R (maximalIdeal R) t.x →+* V)
    (hψalg : ∀ r, (ψ (algebraMap R _ r) : F) = φ r)
    (hψmul : ∀ (b : blowupAlgebra R (maximalIdeal R) t.x) (m : ℕ) (g : R),
      (b : FractionRing R) * algebraMap R _ t.x ^ m = algebraMap R _ g →
        (ψ b : F) * φ t.x ^ m = φ g)
    (hN : t.M' = Ideal.comap ψ (maximalIdeal V)) (hNmax : t.M'.IsMaximal) (hx0 : φ t.x ≠ 0) :
    ∃ (φ' : t.ring →+* F) (hP' : P = (RingHom.ker φ').comap t.toRing),
      Function.Bijective (Localization.localRingHom P (RingHom.ker φ') t.toRing hP') ∧
      RingHom.IsResiduallyAlgebraic (R := R) (R' := t.ring) t.toRing ∧
      IsRegularLocalRing t.ring ∧ (∀ r, φ' r ∈ V) ∧
      ∃ hφ'S : ∀ s, algebraMap S₀ F s ∈ φ'.range,
        curveImage V φ hφS < curveImage V φ' hφ'S := by
  classical
  have hNunit : ∀ u : t.M'.primeCompl, IsUnit (ψ u) := by
    rintro ⟨b, hb⟩
    have hb' : b ∉ t.M' := hb
    rw [hN] at hb'
    by_contra hnu
    exact hb' ((IsLocalRing.mem_maximalIdeal _).mpr hnu)
  let φ'V : t.ring →+* V := IsLocalization.lift (M := t.M'.primeCompl) (S := t.ring) hNunit
  have hφ'V : ∀ b, φ'V (algebraMap (blowupAlgebra R (maximalIdeal R) t.x) t.ring b) = ψ b :=
    IsLocalization.lift_eq hNunit
  let φ' : t.ring →+* F := V.val.toRingHom.comp φ'V
  have hφ'_alg : ∀ b, φ' (algebraMap (blowupAlgebra R (maximalIdeal R) t.x) t.ring b) = ψ b :=
    fun b => congrArg Subtype.val (hφ'V b)
  have hφ'_toRing : ∀ r, φ' (t.toRing r) = φ r := fun r => (hφ'_alg _).trans (hψalg r)
  have hφ'_comp : φ'.comp t.toRing = φ := RingHom.ext hφ'_toRing
  have hP' : P = (RingHom.ker φ').comap t.toRing := by
    rw [RingHom.comap_ker, hφ'_comp, hker]
  have hxP : t.x ∉ P := fun h => hx0 (by rw [← RingHom.mem_ker, hker]; exact h)
  have hxM : t.x ∈ maximalIdeal R := t.x_mem
  have hφ'S : ∀ s, algebraMap S₀ F s ∈ φ'.range := by
    intro s
    obtain ⟨r, hr⟩ := hφS s
    exact ⟨t.toRing r, (hφ'_toRing r).trans hr⟩
  refine ⟨φ', hP', ?_, (t.isMaximal_iff_isResiduallyAlgebraic).mp hNmax, ?_,
    fun r => (φ'V r).2, hφ'S, ?_⟩
  · -- `R_P → R'_{P'}` is bijective: `R' ⊆ R_P` inside the field of quotients
    set f := Localization.localRingHom P (RingHom.ker φ') t.toRing hP'
    set T := Localization.AtPrime (RingHom.ker φ')
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
      obtain ⟨a, s, rfl⟩ := IsLocalization.exists_mk'_eq (RingHom.ker φ').primeCompl z
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
  · have hM0 : maximalIdeal R ≠ ⊥ := fun h => t.x_ne_zero (by simpa [h] using hxM)
    have hresreg : IsRegularLocalRing (R ⧸ maximalIdeal R) := by
      let _ : Field (R ⧸ maximalIdeal R) := Ideal.Quotient.field _
      infer_instance
    exact (t.isRegularLocalRing_and_isLocalHom_and_span_xR_eq_map (maximalIdeal.isMaximal R).isPrime hM0 hresreg).1
  · refine lt_of_le_of_ne (fun v hv => ?_) (fun heq => hS ?_)
    · obtain ⟨r, hr⟩ := hv
      exact ⟨t.toRing r, (hφ'_toRing r).trans hr⟩
    -- if `φ'(R') ∩ V = φ(R) ∩ V`, then every `m/x` lies in `φ(R)`, i.e. `M ⊆ xR + P`
    have hMx : ∀ m ∈ maximalIdeal R, ∃ r, m - t.x * r ∈ P := by
      intro m hm
      let b : blowupAlgebra R (maximalIdeal R) t.x :=
        ⟨algebraMap R _ m / algebraMap R _ t.x, Algebra.subset_adjoin ⟨m, hm, rfl⟩⟩
      have hb1 : (ψ b : F) * φ t.x = φ m := by
        have := hψmul b 1 m (by
          simp only [b, pow_one]
          exact div_mul_cancel₀ _
            ((map_ne_zero_iff _ (IsFractionRing.injective R _)).mpr t.x_ne_zero))
        rwa [pow_one] at this
      have hmem : ψ b ∈ curveImage V φ' hφ'S := ⟨algebraMap _ t.ring b, hφ'_alg b⟩
      rw [← heq] at hmem
      obtain ⟨r, hr⟩ := hmem
      refine ⟨r, ?_⟩
      rw [← hker, RingHom.mem_ker, map_sub, map_mul, hr, mul_comm, hb1, sub_self]
    -- so the maximal ideal of `R/P` is principal, and `R/P` is a discrete valuation ring
    have hloc : IsLocalRing (R ⧸ P) :=
      IsLocalRing.of_surjective' (Ideal.Quotient.mk P) Ideal.Quotient.mk_surjective
    have hmaxS : maximalIdeal (R ⧸ P) = Ideal.span {Ideal.Quotient.mk P t.x} := by
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
    have hxS : Ideal.Quotient.mk P t.x ≠ 0 := by
      rwa [Ne, Ideal.Quotient.eq_zero_iff_mem]
    have hnf : ¬ IsField (R ⧸ P) := by
      rw [IsLocalRing.isField_iff_maximalIdeal_eq, hmaxS]
      intro h
      exact hxS (Ideal.span_singleton_eq_bot.mp h)
    have : IsDiscreteValuationRing (R ⧸ P) :=
      ((IsDiscreteValuationRing.TFAE (R ⧸ P) hnf).out 5 1).mp
        (⟨⟨_, hmaxS⟩⟩ : (maximalIdeal (R ⧸ P)).IsPrincipal)
    infer_instance

/-- One step of the proof of `curveResolvable_of_isAdicComplete`. Let `φ : R → V ⊆ F` have kernel
`P`, with `V` a valuation ring finite over `S₀ ⊆ φ(R)`, and suppose `R/P` is not regular. Choose
`x ∈ M` with `φ(x)` of minimal value, so that `φ(M) V = φ(x) V`; then `φ` extends to
`R[M/x] → V`, and the center of `V` on `R[M/x]` gives a monoidal transform `R'` of `R` with center
`M`, residually algebraic, regular, with `R_P = R'_{P'}` (`P'` the kernel of the extension), and
`φ'(R') ∩ V` strictly larger than `φ(R) ∩ V` (otherwise `M ⊆ xR + P` and `R/P` would be a discrete
valuation ring). -/
theorem exists_monoidalTransform_of_not_isRegularLocalRing_quotient [ValuationRing V] [Module.Finite S₀ V]
    {R : Type u} [CommRing R] [IsRegularLocalRing R] [IsDomain R] {P : Ideal R} [P.IsPrime]
    (φ : R →+* F) (hφV : ∀ r, φ r ∈ V) (hφS : ∀ s, algebraMap S₀ F s ∈ φ.range)
    (hker : RingHom.ker φ = P) (hS : ¬ IsRegularLocalRing (R ⧸ P)) :
    ∃ (t : MonoidalTransform R (maximalIdeal R)) (φ' : t.ring →+* F)
      (hP' : P = (RingHom.ker φ').comap t.toRing),
      Function.Bijective (Localization.localRingHom P (RingHom.ker φ') t.toRing hP') ∧
      RingHom.IsResiduallyAlgebraic (R := R) (R' := t.ring) t.toRing ∧
      IsRegularLocalRing t.ring ∧ (∀ r, φ' r ∈ V) ∧
      ∃ hφ'S : ∀ s, algebraMap S₀ F s ∈ φ'.range,
        curveImage V φ hφS < curveImage V φ' hφ'S := by
  classical
  set M := maximalIdeal R with hMdef
  let φV : R →+* V := φ.codRestrict V hφV
  -- `V` is integral over `R` (through `φ`), since it is finite over `S₀ ⊆ φ(R)`
  have hint : φV.IsIntegral := by
    intro v
    obtain ⟨q, hqm, hq⟩ := Algebra.IsIntegral.isIntegral (R := S₀) v
    have hlift : q.map (algebraMap S₀ V) ∈ Polynomial.lifts φV := by
      rw [Polynomial.lifts_iff_coeff_lifts]
      intro n
      rw [Polynomial.coeff_map]
      obtain ⟨r, hr⟩ := hφS (q.coeff n)
      exact ⟨r, Subtype.ext hr⟩
    obtain ⟨p, hp, -, hpm⟩ := Polynomial.lifts_and_natDegree_eq_and_monic hlift (hqm.map _)
    refine ⟨p, hpm, ?_⟩
    rw [Polynomial.eval₂_eq_eval_map, hp, Polynomial.eval_map]
    exact hq
  -- hence `φ(M) ⊆ m_V`
  have hMcomap : Ideal.comap φV (maximalIdeal V) = M :=
    IsLocalRing.eq_maximalIdeal
      (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal φV hint (maximalIdeal V))
  -- `P ≠ M`, as `R/P` is not regular (a field is regular)
  obtain ⟨m₀, hm₀M, hm₀⟩ : ∃ m ∈ M, φ m ≠ 0 := by
    by_contra h
    push Not at h
    apply hS
    have hMP : M ≤ P := fun m hm => hker ▸ RingHom.mem_ker.mpr (h m hm)
    have hPM : P = M := le_antisymm (le_maximalIdeal (Ideal.IsPrime.ne_top ‹_›)) hMP
    have : P.IsMaximal := hPM ▸ maximalIdeal.isMaximal R
    let _ : Field (R ⧸ P) := Ideal.Quotient.field P
    infer_instance
  -- choose `x ∈ M` with `φ(x) ≠ 0` of minimal value: `φ(M)V = φ(x)V`
  obtain ⟨x, hxM, hx0, hdiv⟩ :
      ∃ x ∈ M, φ x ≠ 0 ∧ M ≤ Ideal.comap φV (Ideal.span {φV x}) := by
    obtain ⟨T, hT⟩ := (IsNoetherian.noetherian M : M.FG)
    have hTM : ∀ f ∈ T, f ∈ M := fun f hf => hT ▸ Submodule.subset_span hf
    have key : ∀ T' : Finset R, (∀ f ∈ T', f ∈ M) →
        ∃ x ∈ M, φ x ≠ 0 ∧ ∀ f ∈ T', φV x ∣ φV f := by
      intro T'
      induction T' using Finset.induction_on with
      | empty => exact fun _ => ⟨m₀, hm₀M, hm₀, by simp⟩
      | insert f T' hf ih =>
        intro hT'
        obtain ⟨x, hxM, hx0, hxd⟩ := ih fun g hg => hT' g (Finset.mem_insert_of_mem hg)
        rcases ValuationRing.dvd_total (φV x) (φV f) with hxf | hfx
        · refine ⟨x, hxM, hx0, fun g hg => ?_⟩
          rcases Finset.mem_insert.mp hg with rfl | hg
          · exact hxf
          · exact hxd g hg
        · refine ⟨f, hT' f (Finset.mem_insert_self f T'), fun hf0 => hx0 ?_, fun g hg => ?_⟩
          · have : φV f = 0 := Subtype.ext hf0
            rw [this, zero_dvd_iff] at hfx
            exact congrArg Subtype.val hfx
          · rcases Finset.mem_insert.mp hg with rfl | hg
            · exact dvd_rfl
            · exact hfx.trans (hxd g hg)
    obtain ⟨x, hxM, hx0, hxd⟩ := key T hTM
    refine ⟨x, hxM, hx0, ?_⟩
    rw [← hT, Ideal.span_le]
    intro f hf
    exact Ideal.mem_comap.mpr (Ideal.mem_span_singleton.mpr (hxd f hf))
  have hx0' : x ≠ 0 := fun h => hx0 (by rw [h, map_zero])
  have hxP : x ∉ P := fun h => hx0 (by rw [← RingHom.mem_ker, hker]; exact h)
  -- the blow-up algebra `A = R[M/x]` lies in `R[1/x]`, on which `φ` extends to `ψ : A → V`
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
  have hMpow : ∀ m, M ^ m ≤ Ideal.comap φV (Ideal.span {φV x ^ m}) := by
    intro m
    rw [← Ideal.span_singleton_pow]
    exact (Ideal.pow_right_mono hdiv m).trans (Ideal.le_comap_pow _ m)
  have hψA_V : ∀ a, ψA a ∈ V := by
    intro a
    obtain ⟨m, g, hg, hag⟩ :=
      MonoidalTransform.exists_mul_pow_eq_of_mem_blowupAlgebra hxM hx0' a.2
    obtain ⟨v, hv⟩ := Ideal.mem_span_singleton'.mp (Ideal.mem_comap.mp (hMpow m hg))
    have h2 : φ g = (v : F) * φ x ^ m := by
      have := congrArg Subtype.val hv
      push_cast at this
      exact this.symm
    have : ψA a = v := mul_right_cancel₀ (pow_ne_zero m hx0) ((hψA a m g hag).trans h2)
    rw [this]
    exact v.2
  let ψV : A →+* V := ψA.codRestrict V hψA_V
  have hψV_comp : ψV.comp (algebraMap R A) = φV := RingHom.ext fun r => Subtype.ext (hψA_alg r)
  -- the center `N` of `V` on `A`: a maximal ideal containing `M A`
  set N : Ideal A := Ideal.comap ψV (maximalIdeal V) with hNdef
  have hNmax : N.IsMaximal :=
    Ideal.isMaximal_comap_of_isIntegral_of_isMaximal ψV
      (RingHom.IsIntegral.tower_top (algebraMap R A) ψV (hψV_comp ▸ hint)) _
  have hMN : M.map (algebraMap R A) ≤ N := by
    rw [Ideal.map_le_iff_le_comap, Ideal.comap_comap, hψV_comp, hMcomap]
  exact ⟨⟨x, hxM, hx0', N, hNmax.isPrime, hMN⟩, exists_curveImage_lt_of_lift V φ hφS hker hS
    ⟨x, hxM, hx0', N, hNmax.isPrime, hMN⟩ ψV hψA_alg hψA rfl hNmax hx0⟩

-- `CurveResolvable` asks for both `[IsRegularLocalRing R]` and `[IsDomain R]`
set_option linter.overlappingInstances false in
/-- The induction of the proof of `curveResolvable_of_isAdicComplete`, on the `S₀`-submodule
`φ(R) ∩ V` of the noetherian `S₀`-module `V`, which strictly increases under `exists_monoidalTransform_of_not_isRegularLocalRing_quotient`. -/
theorem curveResolvable_of_curveImage_eq [ValuationRing V] [Module.Finite S₀ V] [IsNoetherianRing S₀]
    (N : Submodule S₀ V) :
    ∀ {R : Type u} [CommRing R] [IsRegularLocalRing R] [IsDomain R] (φ : R →+* F),
      (∀ r, φ r ∈ V) → ∀ hφS : (∀ s, algebraMap S₀ F s ∈ φ.range),
      curveImage V φ hφS = N → CurveResolvable R (RingHom.ker φ) := by
  induction N using WellFoundedGT.induction with
  | _ N ih =>
  intro R _ _ _ φ hφV hφS hN
  by_cases hS : IsRegularLocalRing (R ⧸ RingHom.ker φ)
  · exact CurveResolvable.regular _ hS
  obtain ⟨t, φ', hP', hbij, halg, hreg, hφ'V, hφ'S, hlt⟩ := exists_monoidalTransform_of_not_isRegularLocalRing_quotient V φ hφV hφS rfl hS
  exact CurveResolvable.step _ t halg (RingHom.ker φ') hP' hbij hreg
    (@ih _ (hN ▸ hlt) t.ring _ hreg _ φ' hφ'V hφ'S rfl)

end CurveStep

/-- Proof of Theorem 1, p. 218: for a complete regular local ring `R` and a prime `P` with
`dim(R/P) ≤ 1`, the sequence of monoidal transforms (i)–(iii) exists ("it is not difficult to
show").

Deviation from the paper (gap filled): the paper gives no argument; the construction (point
blow-ups centred at the valuation of the derived normal ring, induction on `φ(R) ∩ V`) is
supplied here. -/
@[blueprint "lem:III.1-curve-resolution"
  (statement := /-- Let $R$ be a complete regular local ring and $P$ a prime ideal of $R$ with
    $\dim(R/P)\le1$. Then there is a finite sequence of monoidal transforms with center the
    maximal ideals, $R=R_0\to R_1\to\dots\to R_s$, such that (i) $R_i$ is residually algebraic
    over $R_{i-1}$; (ii) for each $i\ge1$ there is a prime ideal $P_i$ of $R_i$ with
    $R_P=(R_i)_{P_i}$; (iii) $R_s/P_s$ is regular. (Proof of Theorem~1, p.~218: ``it is not
    difficult to show''.) -/)
  (proof := /-- If $R/P$ is regular take $s=0$ (this includes $P$ maximal). Otherwise
    $S=R/P$ is a complete local domain of dimension one; its derived normal ring $V$ is a finite
    $S$-module (\cref{lem:III.1-derived-normal-ring-finite}), hence a local ring ($S$ is
    henselian), noetherian, integrally closed of dimension one, i.e.\ a discrete valuation ring.
    Induct on the $S$-submodule $\varphi(R)\cap V$ of the noetherian $S$-module $V$, where
    $\varphi\colon R\to V$ has kernel $P$. If $R/P$ is not regular, pick $x\in M$ with
    $\varphi(x)$ of least value, so $\varphi(M)V=\varphi(x)V$; $\varphi$ extends to
    $R[M/x]\to V$, and the center of $V$ on $R[M/x]$ gives a monoidal transform $R_1$ of $R$ with
    center $M$, residually algebraic (the center is a maximal ideal) and regular
    (\cref{lem:III.2-monoidal-transform-regular}). Its prime $P_1=\ker\varphi_1$ satisfies
    $R_P=(R_1)_{P_1}$, since $R[M/x]\subseteq R[1/x]\subseteq R_P$ ($x\notin P$). Finally
    $\varphi_1(R_1)\cap V\supsetneq\varphi(R)\cap V$: otherwise $\varphi(m/x)\in\varphi(R)$ for
    every $m\in M$, i.e.\ $M\subseteq xR+P$, and $R/P$ would be a discrete valuation ring.

    \textbf{Gap in the paper filled.} The paper only says ``it is not difficult to show''; the
    construction above is supplied by the formalization. Of the two facts the paper recalls,
    only the finiteness of the derived normal ring is a cited leaf; the regularity of its
    localizations is proved (it is a discrete valuation ring or a field). The statement allows
    $\dim(R/P)\le1$ (the paper has $\dim(R/P)=1$), and
    ``$R_P=(R_i)_{P_i}$'' is expressed as the bijectivity of the canonical homomorphism. -/)
  (latexEnv := "lemma")]
theorem curveResolvable_of_isAdicComplete [Hironaka.Cited.CurveFiniteIntegralClosure.{u}] {R : Type u} [CommRing R] [IsRegularLocalRing R]
    [IsDomain R] [IsAdicComplete (maximalIdeal R) R] (P : Ideal R) [P.IsPrime]
    (hP : ringKrullDim (R ⧸ P) ≤ 1) : CurveResolvable R P := by
  by_cases hreg : IsRegularLocalRing (R ⧸ P)
  · exact .regular P hreg
  have : IsLocalRing (R ⧸ P) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk P) Ideal.Quotient.mk_surjective
  have : IsAdicComplete (maximalIdeal (R ⧸ P)) (R ⧸ P) := by
    have : IsAdicComplete (maximalIdeal R) (R ⧸ P) := curve_isAdicComplete_of_finite _ _
    have h := curve_isAdicComplete_map (B := R ⧸ P) (maximalIdeal R)
    rwa [Ideal.Quotient.algebraMap_eq, IsLocalRing.map_maximalIdeal_of_surjective _
      Ideal.Quotient.mk_surjective] at h
  set V := integralClosure (R ⧸ P) (FractionRing (R ⧸ P))
  have : Module.Finite (R ⧸ P) V := curve_finite_integralClosure _
  have : ValuationRing V := curve_valuationRing_integralClosure _ hP
  let φ : R →+* FractionRing (R ⧸ P) :=
    (algebraMap (R ⧸ P) (FractionRing (R ⧸ P))).comp (Ideal.Quotient.mk P)
  have hφV : ∀ r, φ r ∈ V := fun r => V.algebraMap_mem _
  have hφS : ∀ s, algebraMap (R ⧸ P) (FractionRing (R ⧸ P)) s ∈ φ.range := by
    intro s
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective s
    exact ⟨r, rfl⟩
  have hker : RingHom.ker φ = P := by
    rw [RingHom.ker_comp_of_injective _ (IsFractionRing.injective _ _), Ideal.mk_ker]
  have := curveResolvable_of_curveImage_eq V (curveImage V φ hφS) φ hφV hφS rfl
  rwa [hker] at this

end Hironaka

