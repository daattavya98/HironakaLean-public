/-
Copyright (c) 2026 Daattavya Aggarwal, Minhyong Kim, Oisin Kim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daattavya Aggarwal, Minhyong Kim, Oisin Kim
-/
module

public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.LocalProperties.Reduced
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.TotallySplit
public import Architect
public import Hironaka.Ch3.Stability
public import Hironaka.Ch3.StabilityCor3c
public import Hironaka.Ch3.PermissibleEffects
public import Hironaka.Ch3.SemiContinuity
public import Hironaka.Ch2.AscendingChain
public import Hironaka.Compat.NagataFinite
public import Hironaka.Compat.RegularClosedPoint

/-!
# Compatibility layer: the reduction of Corollary 1 to Proposition 2 (pp. 259–260)

The proof of Corollary 1 of Proposition 2 (Ch. III, §8) replaces the monoidal transform `R₁` by a
monoidal transform `R₁'` which is residually separable algebraic over `R`, so that Proposition 2
can be applied to `R₁'` and the prime `P₁' = P₁ ∩ R₁'`:

> "Let `A = R[x₁/x, …, x_r/x]`. Then there exists a prime ideal `N` in `A` such that `R₁ = A_N`.
> … We then know that the singular locus of `Spec(Ā)` is a nowhere dense closed subset
> (footnote 12: cf. Zariski [29]). Therefore we can find a maximal ideal `N'` in `A` such that `N'`
> contains `N` and that `A_{N'}/NA_{N'}` is regular. Let `R₁' = A_{N'}`. Then `R₁'` is a monoidal
> transform of `R` with center `Q` such that `R₁'` is residually algebraic (hence, separable
> algebraic) over `R`, and that there exists a prime ideal `H` in `R₁'` such that `R₁ = (R₁')_H`.
> … It follows, by Theorem 5, §6, that
> `ν*(J) = ν*(J₁')`, … and that `H` is a permissible center for `J₁'`. We have `R₁ = (R₁')_H`,
> `J₁ = (J₁')R₁` and `P₁ = (P₁')R₁` with `P₁' = P₁ ∩ R₁'`. …"
> (pp. 259–260)

This file contains everything in that proof except the application of Proposition 2 itself:

* `exists_isMaximal_le_isRegularLocalRing_quotient`: the closed point `N'` (from the cited
  footnote 12, see `Hironaka/Compat/RegularClosedPoint.lean`);
* `MonoidalTransform.exists_refinement_localization_equiv`: `R₁'` and `H`, with
  `(R₁')_H ≃ R₁` compatible with the maps from `R`;
* `MonoidalTransform.ordElem_maximalIdeal_le_of_pow_mul_eq` (Lemma 8 of §3 in the form needed to
  pass from `ν_H(g_j) = ν_j` to `ν_{M₁'}(g_j) = ν_j`, the hypothesis of Theorem 5);
* `MonoidalTransform.isRegularLocalRing_quotient_of_comap_eq_of_lt` ("`R₁'/P₁'` is regular because
  it is a monoidal transform of `R/P` with center `Q/P`"), a copy of the private lemma of
  `Hironaka/Ch3/Stability.lean`;
* `MonoidalTransform.strictTransformIdeal_eq_map_of_toRing_comp` ("`J₁ = (J₁')R₁`"), a copy of the
  lemma of `Hironaka/Compat/FrameLocalization.lean`, which lies downstream of
  `Hironaka/Ch3/FrameTransforms.lean` and so cannot be imported there;
* `isNormallyFlatAlongIdeal_of_localizationEquiv` (Theorem 3 of Ch. II, §3, for a localization);
* `exists_transform_of_perfectField_residueField`: the assembly.

**Deviations from the paper** (each recorded in the docstring of the declaration concerned):

* the algebra `A` is the chart `R[T.x⁻¹Q]` of the given monoidal transform `T` (so that
  `R₁ = A_N` holds by definition, with `x := T.x`) and not `R[x₁/x, …, x_r/x]` for a minimal base
  `(x, x₁, …, x_r)` of `Q` and the element `x` of (vi); the hypothesis (vi) is invariant under a
  unit factor, since `(x)R₁ = (T.x)R₁ = QR₁`;
* "a monoidal transform `R₁'` of `R` with center `Q`" is `T.withPrime N'` (the same `x`, the prime
  `N'` of `A`); that it is regular and local over `R` is the Lemma of §2 on monoidal transforms
  whose centre has a regular quotient;
* the passage from "`ν_H(g_j) = ν_j`" to the hypothesis of Theorem 5, "`ν_{M₁'}(g_j) = ν_j`", needs
  Lemma 8 of §3 (`ν_{M₁'}(g_j) ≤ ν_M(f_j)`) and the regularity of `R₁'/H` (so that `ν_H` agrees with
  `ν_{HR_H}`); the paper does not say so.
-/

@[expose] public section

open IsLocalRing

namespace Hironaka

universe u

section LocalizationQuotient

/-- `R_p/(I R_p) ≅ (R/I)_{p/I}` for a prime `p ⊇ I`, compatibly with the maps from `R` (Serre).
(A copy of `exists_localization_quotient_equiv_apply` of `FrameLocalization.lean`, which lies
downstream of `FrameTransforms.lean`.) -/
theorem Ideal.exists_ringEquiv_localization_quotient_of_le {R : Type u} [CommRing R] (I p : Ideal R)
    [p.IsPrime] (hp : I ≤ p) :
    have : (p.map (Ideal.Quotient.mk I)).IsPrime :=
      Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by
        rw [Ideal.mk_ker]; exact hp)
    ∃ e : (Localization.AtPrime p ⧸ I.map (algebraMap R (Localization.AtPrime p))) ≃+*
      Localization.AtPrime (p.map (Ideal.Quotient.mk I)), ∀ r : R,
        e (Ideal.Quotient.mk _ (algebraMap R (Localization.AtPrime p) r)) =
          algebraMap (R ⧸ I) _ (Ideal.Quotient.mk I r) := by
  have : (p.map (Ideal.Quotient.mk I)).IsPrime :=
    Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by
      rw [Ideal.mk_ker]; exact hp)
  have hcomap : p = (p.map (Ideal.Quotient.mk I)).comap (Ideal.Quotient.mk I) := by
    rw [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective p,
      ← RingHom.ker_eq_comap_bot, Ideal.mk_ker]
    exact (sup_eq_left.mpr hp).symm
  let φ := Localization.localRingHom p (p.map (Ideal.Quotient.mk I)) (Ideal.Quotient.mk I) hcomap
  have hφ : Function.Surjective φ := by
    intro y
    obtain ⟨b, s, rfl⟩ := IsLocalization.exists_mk'_eq (p.map (Ideal.Quotient.mk I)).primeCompl y
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective b
    obtain ⟨s0, hs0⟩ := Ideal.Quotient.mk_surjective (s : R ⧸ I)
    have hs0p : s0 ∉ p := fun h => s.2 (hs0 ▸ Ideal.mem_map_of_mem _ h)
    refine ⟨IsLocalization.mk' (Localization.AtPrime p) a (⟨s0, hs0p⟩ : p.primeCompl), ?_⟩
    simp only [φ, Localization.localRingHom, IsLocalization.map_mk']
    congr 1
    exact Subtype.ext hs0
  have hker : RingHom.ker φ = I.map (algebraMap R (Localization.AtPrime p)) := by
    refine le_antisymm ?_ ?_
    · intro x hx
      obtain ⟨a, s, rfl⟩ := IsLocalization.exists_mk'_eq p.primeCompl x
      simp only [RingHom.mem_ker, φ, Localization.localRingHom, IsLocalization.map_mk'] at hx
      rw [IsLocalization.mk'_eq_zero_iff] at hx
      obtain ⟨t, ht⟩ := hx
      obtain ⟨t0, ht0e⟩ := Ideal.Quotient.mk_surjective (t : R ⧸ I)
      have ht0 : t0 ∉ p := fun h => t.2 (ht0e ▸ Ideal.mem_map_of_mem _ h)
      have hmem : t0 * a ∈ I := by
        rw [← Ideal.Quotient.eq_zero_iff_mem, map_mul, ht0e]
        simpa [mul_comm] using ht
      have : IsLocalization.mk' (Localization.AtPrime p) a s =
          IsLocalization.mk' (Localization.AtPrime p) (t0 * a) (⟨t0, ht0⟩ * s) := by
        rw [IsLocalization.mk'_eq_iff_eq]
        simp only [Submonoid.coe_mul]
        ring_nf
      rw [this, IsLocalization.mk'_eq_mul_mk'_one]
      exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ hmem)
    · rw [Ideal.map_le_iff_le_comap]
      intro i hi
      rw [Ideal.mem_comap, RingHom.mem_ker]
      simp only [φ, Localization.localRingHom_to_map]
      rw [Ideal.Quotient.eq_zero_iff_mem.mpr hi, map_zero]
  refine ⟨(Ideal.quotEquivOfEq hker.symm).trans (RingHom.quotientKerEquivOfSurjective hφ),
    fun r => ?_⟩
  simp only [RingEquiv.trans_apply]
  show φ (algebraMap R _ r) = _
  simp only [φ, Localization.localRingHom_to_map]

end LocalizationQuotient

section ClosedPoint

/-- **A closed point of the special fibre with regular reduction** (p. 260: "we can find a maximal
ideal `N'` in `A` such that `N'` contains `N` and that `A_{N'}/NA_{N'}` is regular").  Let `A` be an
`R`-algebra of finite type over a local ring `R` whose residue field `k` is perfect and `N` a prime
of `A` containing the maximal ideal of `R`; then `A/N` is a `k`-algebra of finite type (a domain)
and the claim follows from `exists_isMaximal_isRegularLocalRing_localization`.

Deviation from the paper (gap filled): the paper writes "the singular locus of `Spec(Ā)` is a
nowhere dense closed subset (footnote 12: cf. Zariski [29])".  That the singular locus is closed
is the cited fact `isClosed_compl_regularLocus_of_finiteType` (a leaf, as the paper cites it); that
it is nowhere dense, and that a closed point then exists outside it, is proved in Lean
(`exists_isMaximal_isRegularLocalRing_localization`: the generic point of the domain `Ā` is regular,
and the closed points of a finite type algebra over a field are dense, `Ā` being a Jacobson ring).
That `Ā` is an algebra of finite type over the residue field `k` of `R` ("`N ∩ R = M`, and
therefore") is checked here: the maximal ideal of `R` maps into `N`. -/
@[blueprint "lem:III.8-cor1-closed-point"
  (statement := /-- Let $R$ be a local ring whose residue field is perfect, $A$ an $R$-algebra of
    finite type and $N$ a prime ideal of $A$ containing the maximal ideal of $R$. Then there is a
    maximal ideal $N'\supseteq N$ of $A$ such that $A_{N'}/NA_{N'}$ is regular. -/)
  (proof := /-- $\bar A=A/N$ is a domain and an algebra of finite type over the residue field $k$
    of $R$, because the maximal ideal of $R$ maps into $N$. The singular locus of
    $\operatorname{Spec}\bar A$ is closed (\cref{lem:III.8-singular-locus-closed}, cited:
    footnote~12, p.~260) and does not contain the generic point, so it is a proper closed subset;
    $\bar A$ is a Jacobson ring, so a maximal ideal $\bar N'$ of $\bar A$ outside it exists. Put
    $N'$ the inverse image of $\bar N'$; then $A_{N'}/NA_{N'}\cong\bar A_{\bar N'}$ is regular.
    \textbf{Gap in the paper filled.} The nowhere density of the singular locus (the paper cites
    it together with closedness) and the existence of a closed point outside it are proved. -/)
  (latexEnv := "lemma")]
theorem exists_isMaximal_le_isRegularLocalRing_quotient [Hironaka.Cited.IsClosedComplRegularLocusOfFiniteType.{u}] {R A : Type u} [CommRing R] [IsLocalRing R]
    [PerfectField (ResidueField R)] [CommRing A] [Algebra R A] [Algebra.FiniteType R A]
    (N : Ideal A) [N.IsPrime] (hN : (maximalIdeal R).map (algebraMap R A) ≤ N) :
    ∃ (N' : Ideal A) (_ : N'.IsPrime), N ≤ N' ∧ N'.IsMaximal ∧
      IsRegularLocalRing (Localization.AtPrime N' ⧸
        N.map (algebraMap A (Localization.AtPrime N'))) := by
  classical
  let ψ : R →+* A ⧸ N := (Ideal.Quotient.mk N).comp (algebraMap R A)
  have hψ : ∀ a ∈ maximalIdeal R, ψ a = 0 := fun a ha =>
    Ideal.Quotient.eq_zero_iff_mem.mpr (hN (Ideal.mem_map_of_mem _ ha))
  let κ : ResidueField R →+* A ⧸ N := Ideal.Quotient.lift (maximalIdeal R) ψ hψ
  let _ : Algebra (ResidueField R) (A ⧸ N) := κ.toAlgebra
  have : IsScalarTower R (ResidueField R) (A ⧸ N) :=
    IsScalarTower.of_algebraMap_eq fun r => rfl
  have : Algebra.FiniteType R (A ⧸ N) :=
    Algebra.FiniteType.trans (S := A) inferInstance inferInstance
  have : Algebra.FiniteType (ResidueField R) (A ⧸ N) :=
    Algebra.FiniteType.of_restrictScalars_finiteType R (ResidueField R) (A ⧸ N)
  obtain ⟨m, hm, hreg⟩ := exists_isMaximal_isRegularLocalRing_localization (ResidueField R) (A ⧸ N)
  refine ⟨m.asIdeal.comap (Ideal.Quotient.mk N), Ideal.comap_isPrime _ _, ?_, ?_, ?_⟩
  · intro a ha
    rw [Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.mpr ha]
    exact m.asIdeal.zero_mem
  · exact Ideal.comap_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective
  · have hle : N ≤ m.asIdeal.comap (Ideal.Quotient.mk N) := fun a ha => by
      rw [Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.mpr ha]
      exact m.asIdeal.zero_mem
    have : (m.asIdeal.comap (Ideal.Quotient.mk N)).IsPrime := Ideal.comap_isPrime _ _
    obtain ⟨e, -⟩ := Ideal.exists_ringEquiv_localization_quotient_of_le N
      (m.asIdeal.comap (Ideal.Quotient.mk N)) hle
    have hmap : (m.asIdeal.comap (Ideal.Quotient.mk N)).map (Ideal.Quotient.mk N) = m.asIdeal :=
      Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective _
    have hp : ((m.asIdeal.comap (Ideal.Quotient.mk N)).map (Ideal.Quotient.mk N)).IsPrime :=
      by rw [hmap]; exact m.isPrime
    have hreg' : ∀ (I : Ideal (A ⧸ N)) [I.IsPrime], I = m.asIdeal →
        IsRegularLocalRing (Localization.AtPrime I) := by
      rintro I _ rfl
      exact hreg
    have := hreg' _ hmap
    exact IsRegularLocalRing.of_ringEquiv e.symm

end ClosedPoint

section RefinedTransform

namespace MonoidalTransform

variable {R : Type u} [CommRing R] [IsRegularLocalRing R] [IsDomain R]

/-- **The closed-point refinement of a monoidal transform** (proof of Corollary 1, p. 260): for a
monoidal transform `R₁ = A_N` of `R` with prime center `Q` (`R/Q` regular), `A = R[x⁻¹Q]`, and a
perfect residue field of `R`, there is a maximal ideal `N' ⊇ N` of `A` such that `R₁' = A_{N'}` is a
monoidal transform of `R` with centre `Q` (the same `x`), residually separable algebraic over `R`,
`R₁'` is regular, `R₁ = (R₁')_H` for the prime `H = N R₁'` and `R₁'/H = A_{N'}/NA_{N'}` is
regular.

Deviation from the paper (harmless): the algebra `A` is the chart `R[T.x⁻¹Q]` of the given monoidal
transform `T` (so that `R₁ = A_N` holds by definition and `R₁' = T.withPrime N'` has the same `x`)
and not `R[x₁/x, …, x_r/x]` for a minimal base `(x, x₁, …, x_r)` of `Q` and the element `x` of (vi);
the two generate the same ideal `QR₁`, and the hypothesis (vi) is invariant under a unit factor.

Deviation from the paper (gap filled): "`R₁'` is residually algebraic (hence separable algebraic)
over `R`" is `MonoidalTransform.isMaximal_iff_isResiduallyAlgebraic` (Zariski's lemma) and the
perfectness of the residue field of `R`; that `R₁'` is regular and local over `R`, and the
isomorphism `(R₁')_H ≃ R₁` with the equality `R₁ = (R₁')_H` of the paper, are proved here (the
localization of the localization `A_{N'}` at `NA_{N'}` is `A_N`). -/
@[blueprint "lem:III.8-cor1-refinement"
  (statement := /-- Let $R$ be a regular local ring with perfect residue field, $Q$ a prime ideal
    with $R/Q$ regular and $R_1=A_N$ a monoidal transform of $R$ with center $Q$, where
    $A=R[x^{-1}Q]$. There is a maximal ideal $N'\supseteq N$ of $A$ such that $R_1'=A_{N'}$ is a
    regular local ring, a monoidal transform of $R$ with center $Q$, residually separable
    algebraic over $R$, and, with $H=NR_1'$, $R_1\cong(R_1')_H$ (compatibly with the maps from
    $R$) and $R_1'/H$ is regular. -/)
  (proof := /-- Take $N'$ from \cref{lem:III.8-cor1-closed-point}; $N'$ is maximal, so $R_1'$ is
    residually algebraic over $R$ (Zariski's lemma, \S2), hence separable algebraic as the
    residue field is perfect, and regular by \cref{lem:III.2-monoidal-transform-regular}.
    $R_1=A_N$ is the
    localization of $A_{N'}$ at $H=NA_{N'}$, and $R_1'/H=A_{N'}/NA_{N'}$ is regular by the choice
    of $N'$. \textbf{Deviation (harmless).} $A=R[T.x^{-1}Q]$ is the chart of the given transform,
    $x:=T.x$ in place of the element $x$ of (vi) of Corollary~1. -/)
  (latexEnv := "lemma")]
theorem exists_refinement_localization_equiv [Hironaka.Cited.IsClosedComplRegularLocusOfFiniteType.{u}] [PerfectField (ResidueField R)]
    (Q : Ideal R) [Q.IsPrime] (hQreg : IsRegularLocalRing (R ⧸ Q)) (T : MonoidalTransform R Q) :
    ∃ (T' : MonoidalTransform R Q) (H : Ideal T'.ring) (_ : H.IsPrime)
      (L : Localization.AtPrime H ≃+* T.ring),
      T'.x = T.x ∧ IsRegularLocalRing T'.ring ∧ IsLocalHom T'.toRing ∧
      RingHom.IsResiduallySeparableAlgebraic (R := R) (R' := T'.ring) T'.toRing ∧
      IsRegularLocalRing (T'.ring ⧸ H) ∧
      ∀ a : R, L (algebraMap T'.ring (Localization.AtPrime H) (T'.toRing a)) = T.toRing a := by
  classical
  have : Algebra.FiniteType R (blowupAlgebra R Q T.x) :=
    MonoidalTransform.finiteType_blowupAlgebra T.x
  obtain ⟨M₂, hM₂p, hle, hM₂, hreg⟩ :=
    exists_isMaximal_le_isRegularLocalRing_quotient (R := R) (A := blowupAlgebra R Q T.x) T.M'
      T.le
  let T₂ := T.withPrime M₂ hle
  have hQ0 : Q ≠ ⊥ := fun h => T.x_ne_zero (Ideal.mem_bot.mp (h ▸ T.x_mem))
  have hsep : RingHom.IsResiduallySeparableAlgebraic (R := R) (R' := T₂.ring) T₂.toRing := by
    have halg := (T₂.isMaximal_iff_isResiduallyAlgebraic).mp hM₂
    unfold RingHom.IsResiduallyAlgebraic at halg
    unfold RingHom.IsResiduallySeparableAlgebraic
    let _ := (ResidueField.map T₂.toRing).toAlgebra
    exact Algebra.IsAlgebraic.isSeparable_of_perfectField
  have hdisj : Disjoint (M₂.primeCompl : Set (blowupAlgebra R Q T.x)) T.M' :=
    Set.disjoint_left.mpr fun a ha haQ => ha (hle haQ)
  have hQ₁p : (T.M'.map (algebraMap (blowupAlgebra R Q T.x) (Localization.AtPrime M₂))).IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint M₂.primeCompl (Localization.AtPrime M₂) T.M'
      inferInstance hdisj
  have hcomap : T.M' = (T.M'.map (algebraMap (blowupAlgebra R Q T.x)
      (Localization.AtPrime M₂))).comap (algebraMap (blowupAlgebra R Q T.x)
        (Localization.AtPrime M₂)) :=
    (IsLocalization.under_map_of_isPrime_disjoint M₂.primeCompl (Localization.AtPrime M₂)
      inferInstance hdisj).symm
  have hψ := Localization.localRingHom_bijective_of_eq_comap_map T.M' M₂ hcomap
  refine ⟨T₂, T.M'.map (algebraMap (blowupAlgebra R Q T.x) (Localization.AtPrime M₂)), hQ₁p,
    (RingEquiv.ofBijective _ hψ).symm, rfl, ?_, ?_, hsep, hreg, fun a => ?_⟩
  · exact (MonoidalTransform.isRegularLocalRing_and_isLocalHom_and_span_xR_eq_map T₂ inferInstance
      hQ0 hQreg).1
  · exact (MonoidalTransform.isRegularLocalRing_and_isLocalHom_and_span_xR_eq_map T₂ inferInstance
      hQ0 hQreg).2.1
  · refine (RingEquiv.symm_apply_eq _).mpr ?_
    show _ = Localization.localRingHom T.M' _ (algebraMap _ _) hcomap
      (algebraMap (blowupAlgebra R Q T.x) (Localization.AtPrime T.M')
        (algebraMap R (blowupAlgebra R Q T.x) a))
    rw [Localization.localRingHom_to_map]
    rfl

end MonoidalTransform

end RefinedTransform

section OrderLemmas

/-- `ν_I(f) ≤ ν_{I'}(φ f)` for `I' ⊇ φ(I)`. -/
theorem Ideal.ordElem_le_ordElem_of_map_le {A B : Type*} [CommRing A] [CommRing B] (φ : A →+* B)
    (I : Ideal A) (I' : Ideal B) (h : I.map φ ≤ I') (f : A) :
    Ideal.ordElem I f ≤ Ideal.ordElem I' (φ f) :=
  Ideal.ordElem_le fun _ hν => Ideal.le_ordElem (by
    have : φ f ∈ (I ^ _).map φ := Ideal.mem_map_of_mem φ hν
    rw [Ideal.map_pow] at this
    exact Ideal.pow_right_mono h _ this)

/-- The order is invariant under a ring isomorphism. -/
theorem Ideal.ordElem_map_ringEquiv_of_eq {A B : Type*} [CommRing A] [CommRing B] (e : A ≃+* B)
    (I : Ideal A) (I' : Ideal B) (h : I.map e = I') (a : A) :
    Ideal.ordElem I' (e a) = Ideal.ordElem I a := by
  subst h
  refine le_antisymm ?_ (Ideal.ordElem_le_ordElem_of_map_le (e : A →+* B) I _ le_rfl a)
  have h2 := Ideal.ordElem_le_ordElem_of_map_le (e.symm : B →+* A) (I.map (e : A →+* B)) I
    (by rw [Ideal.map_map]; simp) (e a)
  simp only [RingEquiv.coe_toRingHom, RingEquiv.symm_apply_apply] at h2
  exact h2

/-- Multiplying by a unit does not change the order. -/
theorem Ideal.ordElem_isUnit_mul {A : Type*} [CommRing A] (I : Ideal A) {u : A} (hu : IsUnit u)
    (a : A) : Ideal.ordElem I (u * a) = Ideal.ordElem I a := by
  obtain ⟨v, rfl⟩ := hu
  refine le_antisymm (Ideal.ordElem_le fun n hn => Ideal.le_ordElem ?_)
    (Ideal.ordElem_le fun n hn => Ideal.le_ordElem (Ideal.mul_mem_left _ _ hn))
  have := Ideal.mul_mem_left _ ((↑v⁻¹ : Aˣ) : A) hn
  rwa [← mul_assoc, Units.inv_mul, one_mul] at this

end OrderLemmas

section RegularQuotientCopy

variable {R : Type u} [CommRing R] [IsRegularLocalRing R]

/-- If `ρ : B = R[x⁻¹P] → B̄` is surjective with kernel `Q₁ ∩ B` and `R̄₁ = B̄_{ρ(M')}` is a
regular monoidal transform, then `R₁/Q₁ ≅ R̄₁` is regular. -/
private theorem isRegularLocalRing_quotient_of_surjective_blowupAlgebra {P : Ideal R}
    [IsDomain R] (t : MonoidalTransform R P) (Q₁ : Ideal t.ring) [Q₁.IsPrime] {Rb : Type u}
    [CommRing Rb] [IsRegularLocalRing Rb] [IsDomain Rb] {Pb : Ideal Rb}
    (Tb : MonoidalTransform Rb Pb)
    [IsRegularLocalRing Tb.ring] (ρ : blowupAlgebra R P t.x →+* blowupAlgebra Rb Pb Tb.x)
    (hsurj : Function.Surjective ρ)
    (hker : RingHom.ker ρ = Q₁.comap (algebraMap (blowupAlgebra R P t.x) t.ring))
    (hM : Tb.M' = t.M'.map ρ) : IsRegularLocalRing (t.ring ⧸ Q₁) := by
  have hqM : Q₁.comap (algebraMap (blowupAlgebra R P t.x) t.ring) ≤ t.M' := by
    rw [← IsLocalization.AtPrime.under_maximalIdeal t.ring t.M']
    exact Ideal.comap_mono (le_maximalIdeal (Ideal.IsPrime.ne_top inferInstance))
  have hcomapM : (t.M'.map ρ).comap ρ = t.M' := by
    rw [Ideal.comap_map_of_surjective _ hsurj, sup_eq_left]
    exact (Ideal.comap_mono bot_le).trans (by rw [← RingHom.ker_eq_comap_bot, hker]; exact hqM)
  let iso₁ := (Ideal.quotEquivOfEq hker.symm).trans (RingHom.quotientKerEquivOfSurjective hsurj)
  have hiso₁ : ∀ s, iso₁ (Ideal.Quotient.mk _ s) = ρ s := fun s => by
    simp only [iso₁, RingEquiv.trans_apply, Ideal.quotEquivOfEq_mk,
      RingHom.quotientKerEquivOfSurjective_apply_mk]
  have hQ₁eq : (Q₁.comap (algebraMap (blowupAlgebra R P t.x) t.ring)).map
      (algebraMap (blowupAlgebra R P t.x) t.ring) = Q₁ :=
    IsLocalization.map_under t.M'.primeCompl t.ring Q₁
  let φb : blowupAlgebra Rb Pb Tb.x →+* t.ring ⧸ Q₁ :=
    (Ideal.quotientMap Q₁ (algebraMap (blowupAlgebra R P t.x) t.ring) le_rfl).comp
      iso₁.symm.toRingHom
  let _ : Algebra (blowupAlgebra Rb Pb Tb.x) (t.ring ⧸ Q₁) := φb.toAlgebra
  have hH : (Ideal.Quotient.mk Q₁).comp (algebraMap (blowupAlgebra R P t.x) t.ring) =
      (algebraMap _ (t.ring ⧸ Q₁)).comp ρ := by
    refine RingHom.ext fun b => ?_
    show _ = φb (ρ b)
    simp only [φb, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom]
    rw [← hiso₁, RingEquiv.symm_apply_apply, Ideal.quotientMap_mk]
  have hloc := IsLocalization.of_surjective t.M'.primeCompl t.ring ρ hsurj
    (Ideal.Quotient.mk Q₁) Ideal.Quotient.mk_surjective hH
    (by rw [Ideal.mk_ker, hker, hQ₁eq])
  have hsub : t.M'.primeCompl.map ρ = Tb.M'.primeCompl := by
    ext y
    constructor
    · rintro ⟨s, hs, rfl⟩ hy
      apply hs
      have h' : s ∈ (t.M'.map ρ).comap ρ := by rw [← hM]; exact hy
      rwa [hcomapM] at h'
    · intro hy
      obtain ⟨s, rfl⟩ := hsurj y
      exact ⟨s, fun h => hy (by rw [hM]; exact Ideal.mem_map_of_mem ρ h), rfl⟩
  rw [hsub] at hloc
  exact IsRegularLocalRing.of_ringEquiv
    (IsLocalization.algEquiv Tb.M'.primeCompl Tb.ring (t.ring ⧸ Q₁)).toRingEquiv

/-- `R₁/Q₁` is a monoidal transform of `R/Q` with center `P/Q` (p. 241), hence regular.
(A copy of the private lemma of `Stability.lean` used for Corollary 1 of Theorem 5.) -/
theorem MonoidalTransform.isRegularLocalRing_quotient_of_comap_eq_of_lt [IsDomain R]
    (P Q : Ideal R) [P.IsPrime]
    [Q.IsPrime] [IsRegularLocalRing (R ⧸ P)] [IsRegularLocalRing (R ⧸ Q)] (hQP : Q ≤ P)
    (hQneP : Q ≠ P) (t : MonoidalTransform R P) (Q₁ : Ideal t.ring) [Q₁.IsPrime]
    (hQ₁ : Q₁.comap t.toRing = Q) : IsRegularLocalRing (t.ring ⧸ Q₁) := by
  classical
  set K := FractionRing R
  set x := t.x
  -- `x ∉ Q`
  have hxQ : x ∉ Q := by
    intro hxQ
    apply hQneP
    refine le_antisymm hQP fun p hp => ?_
    rw [← hQ₁, Ideal.mem_comap]
    have : t.toRing p ∈ P.map t.toRing := Ideal.mem_map_of_mem _ hp
    rw [← t.span_xR_eq_map, Ideal.mem_span_singleton] at this
    obtain ⟨c, hc⟩ := this
    rw [hc]
    refine Ideal.mul_mem_right _ _ ?_
    show t.toRing x ∈ Q₁
    rw [← Ideal.mem_comap, hQ₁]
    exact hxQ
  -- the localization `R_x` inside `K`
  have hxK : IsUnit (algebraMap R K x) :=
    isUnit_iff_ne_zero.mpr ((map_ne_zero_iff _ (IsFractionRing.injective R K)).mpr t.x_ne_zero)
  let ι : Localization.Away x →+* K := IsLocalization.Away.lift x hxK
  have hι : Function.Injective ι := by
    refine (IsLocalization.lift_injective_iff (M := Submonoid.powers x) _).mpr fun a b => ?_
    refine ⟨fun h => ?_, fun h => by rw [(IsFractionRing.injective R K) h]⟩
    have := congrArg ι h
    simpa only [ι, IsLocalization.Away.lift_eq] using this
  -- `R̄ = R/Q`, `P̄ = P/Q`, `x̄`
  have hxb : Ideal.Quotient.mk Q x ≠ 0 := by
    rw [ne_eq, Ideal.Quotient.eq_zero_iff_mem]
    exact hxQ
  have hxbK : IsUnit (((algebraMap (R ⧸ Q) (FractionRing (R ⧸ Q))).comp
      (Ideal.Quotient.mk Q)) x) :=
    isUnit_iff_ne_zero.mpr (by
      rw [RingHom.comp_apply]
      exact (map_ne_zero_iff _ (IsFractionRing.injective (R ⧸ Q) _)).mpr hxb)
  let θ : Localization.Away x →+* FractionRing (R ⧸ Q) := IsLocalization.Away.lift x hxbK
  let e := RingEquiv.ofLeftInverse (Function.leftInverse_invFun hι)
  -- `B = R[x⁻¹P] ⊆ R_x`
  have hinv : ι (IsLocalization.Away.invSelf x) = (algebraMap R K x)⁻¹ := by
    have h1 : ι (algebraMap R (Localization.Away x) x) = algebraMap R K x :=
      IsLocalization.Away.lift_eq x hxK x
    have h2 : algebraMap R K x * ι (IsLocalization.Away.invSelf x) = 1 := by
      rw [← h1, ← map_mul, IsLocalization.Away.mul_invSelf, map_one]
    exact eq_inv_of_mul_eq_one_right h2
  have hBle : ∀ b ∈ blowupAlgebra R P x, b ∈ ι.range := by
    intro b hb
    induction hb using Algebra.adjoin_induction with
    | mem y hy =>
      obtain ⟨p, -, rfl⟩ := hy
      refine ⟨algebraMap R (Localization.Away x) p * IsLocalization.Away.invSelf x, ?_⟩
      rw [map_mul, hinv, IsLocalization.Away.lift_eq]
      exact (div_eq_mul_inv _ _).symm
    | algebraMap r => exact ⟨algebraMap R _ r, IsLocalization.Away.lift_eq x hxK r⟩
    | add y z _ _ hy hz => exact add_mem hy hz
    | mul y z _ _ hy hz => exact mul_mem hy hz
  let incl : blowupAlgebra R P x →+* ι.range :=
    ((blowupAlgebra R P x).val.toRingHom).codRestrict ι.range fun b => hBle b b.2
  let ρ₀ : blowupAlgebra R P x →+* FractionRing (R ⧸ Q) :=
    θ.comp (e.symm.toRingHom.comp incl)
  have hρ₀ : ∀ r, ρ₀ (algebraMap R (blowupAlgebra R P x) r) =
      algebraMap (R ⧸ Q) (FractionRing (R ⧸ Q)) (Ideal.Quotient.mk Q r) := by
    intro r
    have h1 : incl (algebraMap R (blowupAlgebra R P x) r) = e (algebraMap R _ r) :=
      Subtype.ext (IsLocalization.Away.lift_eq x hxK r).symm
    show θ (e.symm (incl _)) = _
    rw [h1, e.symm_apply_apply, IsLocalization.Away.lift_eq]
    rfl
  have hxKb : algebraMap (R ⧸ Q) (FractionRing (R ⧸ Q)) (Ideal.Quotient.mk Q x) ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr hxb
  -- `xᴺ b = f` gives `x̄ᴺ ρ₀(b) = f̄`
  have hρrep : ∀ (b : blowupAlgebra R P x) (N : ℕ) (f : R),
      algebraMap R K x ^ N * (b : K) = algebraMap R K f →
      algebraMap (R ⧸ Q) (FractionRing (R ⧸ Q)) (Ideal.Quotient.mk Q x) ^ N * ρ₀ b =
        algebraMap (R ⧸ Q) (FractionRing (R ⧸ Q)) (Ideal.Quotient.mk Q f) := by
    intro b N f h
    have hB : algebraMap R (blowupAlgebra R P x) x ^ N * b =
        algebraMap R (blowupAlgebra R P x) f := Subtype.ext h
    have := congrArg ρ₀ hB
    rwa [map_mul, map_pow, hρ₀, hρ₀] at this
  have hgen : ∀ (p : R) (hp : p ∈ P),
      ρ₀ ⟨algebraMap R K p / algebraMap R K x, Algebra.subset_adjoin ⟨p, hp, rfl⟩⟩ =
        algebraMap (R ⧸ Q) (FractionRing (R ⧸ Q)) (Ideal.Quotient.mk Q p) /
          algebraMap (R ⧸ Q) (FractionRing (R ⧸ Q)) (Ideal.Quotient.mk Q x) := by
    intro p hp
    have hrep := hρrep ⟨_, Algebra.subset_adjoin ⟨p, hp, rfl⟩⟩ 1 p
      (by rw [pow_one]; exact mul_div_cancel₀ _ hxK.ne_zero)
    rw [pow_one] at hrep
    rw [eq_div_iff hxKb, mul_comm]
    exact hrep
  -- `ρ₀` maps `B` into `B̄ = (R/Q)[x̄⁻¹P̄]`
  have hρB : ∀ b : blowupAlgebra R P x, ρ₀ b ∈
      blowupAlgebra (R ⧸ Q) (P.map (Ideal.Quotient.mk Q)) (Ideal.Quotient.mk Q x) := by
    rintro ⟨b, hb⟩
    induction hb using Algebra.adjoin_induction with
    | mem y hy =>
      obtain ⟨p, hp, rfl⟩ := hy
      rw [hgen p hp]
      exact Algebra.subset_adjoin ⟨Ideal.Quotient.mk Q p, Ideal.mem_map_of_mem _ hp, rfl⟩
    | algebraMap r =>
      have h := hρ₀ r
      rw [show algebraMap R (blowupAlgebra R P x) r = ⟨algebraMap R K r, _⟩ from rfl] at h
      rw [h]
      exact Subalgebra.algebraMap_mem _ _
    | add y z hy hz ihy ihz =>
      rw [show (⟨y + z, add_mem hy hz⟩ : blowupAlgebra R P x) = ⟨y, hy⟩ + ⟨z, hz⟩ from rfl,
        map_add]
      exact add_mem ihy ihz
    | mul y z hy hz ihy ihz =>
      rw [show (⟨y * z, mul_mem hy hz⟩ : blowupAlgebra R P x) = ⟨y, hy⟩ * ⟨z, hz⟩ from rfl,
        map_mul]
      exact mul_mem ihy ihz
  let ρ : blowupAlgebra R P x →+*
      blowupAlgebra (R ⧸ Q) (P.map (Ideal.Quotient.mk Q)) (Ideal.Quotient.mk Q x) :=
    ρ₀.codRestrict _ hρB
  have hsurj : Function.Surjective ρ := by
    rintro ⟨y, hy⟩
    induction hy using Algebra.adjoin_induction with
    | mem y hy =>
      obtain ⟨pb, hpb, rfl⟩ := hy
      obtain ⟨p, hp, rfl⟩ :=
        (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).mp hpb
      exact ⟨⟨_, Algebra.subset_adjoin ⟨p, hp, rfl⟩⟩, Subtype.ext (hgen p hp)⟩
    | algebraMap rb =>
      obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective rb
      exact ⟨algebraMap R _ r, Subtype.ext (hρ₀ r)⟩
    | add y z hy hz ihy ihz =>
      obtain ⟨u, hu⟩ := ihy
      obtain ⟨v, hv⟩ := ihz
      exact ⟨u + v, by rw [map_add, hu, hv]; rfl⟩
    | mul y z hy hz ihy ihz =>
      obtain ⟨u, hu⟩ := ihy
      obtain ⟨v, hv⟩ := ihz
      exact ⟨u * v, by rw [map_mul, hu, hv]; rfl⟩
  have hxQ₁ : t.toRing x ∉ Q₁ := fun h => hxQ (by rw [← hQ₁]; exact h)
  -- `ker ρ = Q₁ ∩ B`
  have hker : RingHom.ker ρ = Q₁.comap (algebraMap (blowupAlgebra R P x) t.ring) := by
    ext b
    obtain ⟨N, hN⟩ := exists_forall_pow_mul_eq_of_mem_blowupAlgebra t.x_ne_zero b.2
    obtain ⟨f, hf⟩ := hN N le_rfl
    have h1 := hρrep b N f hf
    have hB : algebraMap R (blowupAlgebra R P x) x ^ N * b =
        algebraMap R (blowupAlgebra R P x) f := Subtype.ext hf
    have h2 : t.toRing x ^ N * algebraMap (blowupAlgebra R P x) t.ring b = t.toRing f := by
      have := congrArg (algebraMap (blowupAlgebra R P x) t.ring) hB
      rwa [map_mul, map_pow] at this
    rw [RingHom.mem_ker, Ideal.mem_comap]
    constructor
    · intro h0
      have h0' : ρ₀ b = 0 := congrArg Subtype.val h0
      rw [h0', mul_zero, eq_comm, map_eq_zero_iff _ (IsFractionRing.injective _ _),
        Ideal.Quotient.eq_zero_iff_mem] at h1
      have hfQ₁ : t.toRing f ∈ Q₁ := by
        rw [← Ideal.mem_comap, hQ₁]
        exact h1
      rw [← h2] at hfQ₁
      exact ((inferInstance : Q₁.IsPrime).mem_or_mem hfQ₁).resolve_left fun h =>
        hxQ₁ ((inferInstance : Q₁.IsPrime).mem_of_pow_mem N h)
    · intro hb
      have hfQ : f ∈ Q := by
        rw [← hQ₁, Ideal.mem_comap, ← h2]
        exact Ideal.mul_mem_left _ _ hb
      apply Subtype.ext
      show ρ₀ b = 0
      rw [(Ideal.Quotient.eq_zero_iff_mem).mpr hfQ, map_zero] at h1
      exact (mul_eq_zero.mp h1).resolve_left (pow_ne_zero _ hxKb)
  have hρval : ∀ b, ((ρ b : blowupAlgebra (R ⧸ Q) (P.map (Ideal.Quotient.mk Q))
      (Ideal.Quotient.mk Q x)) : FractionRing (R ⧸ Q)) = ρ₀ b := fun b => rfl
  clear_value ρ ρ₀ incl e θ ι
  -- `Q₁ ∩ B ⊆ M'`
  have hqM : Q₁.comap (algebraMap (blowupAlgebra R P x) t.ring) ≤ t.M' := by
    rw [← IsLocalization.AtPrime.under_maximalIdeal t.ring t.M']
    exact Ideal.comap_mono (le_maximalIdeal (Ideal.IsPrime.ne_top inferInstance))
  have hkerM : RingHom.ker ρ ≤ t.M' := hker.le.trans hqM
  have hMb : (t.M'.map ρ).IsPrime := Ideal.map_isPrime_of_surjective hsurj hkerM
  have hcomapM : (t.M'.map ρ).comap ρ = t.M' := by
    rw [Ideal.comap_map_of_surjective _ hsurj, sup_eq_left]
    exact (Ideal.comap_mono bot_le).trans (by rw [← RingHom.ker_eq_comap_bot]; exact hkerM)
  -- the monoidal transform `R̄₁` of `R̄ = R/Q` with center `P̄ = P/Q`
  have hPb : (P.map (Ideal.Quotient.mk Q)).IsPrime :=
    Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective
      (by rw [Ideal.mk_ker]; exact hQP)
  have hxPb : Ideal.Quotient.mk Q x ∈ P.map (Ideal.Quotient.mk Q) :=
    Ideal.mem_map_of_mem _ t.x_mem
  have hcomp : (algebraMap (R ⧸ Q) (blowupAlgebra (R ⧸ Q) (P.map (Ideal.Quotient.mk Q))
      (Ideal.Quotient.mk Q x))).comp (Ideal.Quotient.mk Q) =
        ρ.comp (algebraMap R (blowupAlgebra R P x)) :=
    RingHom.ext fun r => Subtype.ext (by
      simp only [RingHom.comp_apply]
      rw [hρval, hρ₀]
      rfl)
  have hleb : (maximalIdeal (R ⧸ Q)).map (algebraMap (R ⧸ Q) (blowupAlgebra (R ⧸ Q)
      (P.map (Ideal.Quotient.mk Q)) (Ideal.Quotient.mk Q x))) ≤ t.M'.map ρ := by
    rw [← map_maximalIdeal_of_surjective (Ideal.Quotient.mk Q) Ideal.Quotient.mk_surjective,
      Ideal.map_map, hcomp, ← Ideal.map_map]
    exact Ideal.map_mono t.le
  let Tb : MonoidalTransform (R ⧸ Q) (P.map (Ideal.Quotient.mk Q)) :=
    ⟨Ideal.Quotient.mk Q x, hxPb, hxb, t.M'.map ρ, hMb, hleb⟩
  have hPb0 : P.map (Ideal.Quotient.mk Q) ≠ ⊥ := fun h => hxb (Ideal.mem_bot.mp (h.le hxPb))
  have hSb : IsRegularLocalRing ((R ⧸ Q) ⧸ P.map (Ideal.Quotient.mk Q)) :=
    IsRegularLocalRing.of_ringEquiv (DoubleQuot.quotQuotEquivQuotOfLE hQP).symm
  have hregb : IsRegularLocalRing Tb.ring :=
    (MonoidalTransform.isRegularLocalRing_and_isLocalHom_and_span_xR_eq_map Tb hPb hPb0 hSb).1
  exact isRegularLocalRing_quotient_of_surjective_blowupAlgebra t Q₁ Tb ρ hsurj hker rfl

end RegularQuotientCopy

namespace MonoidalTransform

section StrictTransformCopy

variable {R : Type u} [CommRing R] [IsRegularLocalRing R] [IsDomain R]

/-- **The strict transform commutes with the passage to a localization of the transform.**  If
`T₁`, `T₂` are monoidal transforms of `R` with the same center `Q` and `λ : T₂.ring → T₁.ring` is a
ring homomorphism compatible with the maps from `R` (the localization of
`exists_isResiduallySeparableAlgebraic_localization_equiv`), then the strict transform of `J` in
`T₁` is generated by the image of the strict transform in `T₂`. -/
theorem strictTransformIdeal_eq_map_of_toRing_comp (Q : Ideal R) [Q.IsPrime]
    (T₁ T₂ : MonoidalTransform R Q) (lam : T₂.ring →+* T₁.ring)
    (hlam : ∀ a : R, lam (T₂.toRing a) = T₁.toRing a) (J : Ideal R) :
    strictTransformIdeal T₁ J = (strictTransformIdeal T₂ J).map lam := by
  have h1 : Ideal.span {T₁.xR} = Q.map T₁.toRing := T₁.span_xR_eq_map
  have h2 : Ideal.span {T₂.xR} = Q.map T₂.toRing := T₂.span_xR_eq_map
  have hmapQ : (Q.map T₂.toRing).map lam = Q.map T₁.toRing := by
    rw [Ideal.map_map]
    congr 1
    exact RingHom.ext hlam
  have hT1 : Function.Injective T₁.toRing := MonoidalTransform.toRing_injective T₁
  have hxR1 : T₁.xR ≠ 0 := fun h0 => T₁.x_ne_zero (hT1 (by rw [map_zero]; exact h0))
  refine le_antisymm (Ideal.span_le.mpr ?_) ?_
  · rintro y ⟨x₁, hx₁, f, hf, ν, hν, hy⟩
    have hfQ : f ∈ Q ^ ν := Ideal.mem_pow_of_le_ordElem hν
    have hfx : T₂.toRing f ∈ Ideal.span {T₂.xR ^ ν} := by
      rw [← Ideal.span_singleton_pow, h2, ← Ideal.map_pow]
      exact Ideal.mem_map_of_mem _ hfQ
    obtain ⟨y₂, hy₂⟩ := Ideal.mem_span_singleton'.mp hfx
    have hass : Ideal.span {lam T₂.xR} = Ideal.span {x₁} := by
      rw [← Set.image_singleton (f := lam), ← Ideal.map_span, h2, hmapQ, hx₁]
    obtain ⟨u, hu⟩ : Associated (lam T₂.xR) x₁ := Ideal.span_singleton_eq_span_singleton.mp hass
    have hx0 : x₁ ≠ 0 := by
      intro h0
      have : T₁.xR ∈ Ideal.span {x₁} := by
        rw [hx₁, ← h1]; exact Ideal.mem_span_singleton_self _
      rw [h0, Ideal.span_singleton_eq_bot.mpr rfl, Ideal.mem_bot] at this
      exact hxR1 this
    have hlx0 : lam T₂.xR ≠ 0 := by
      intro h0; apply hx0; rw [← hu, h0, zero_mul]
    have hkey : lam T₂.xR ^ ν * ((u : T₁.ring) ^ ν * y - lam y₂) = 0 := by
      have e1 : T₁.toRing f = lam (T₂.toRing f) := (hlam f).symm
      rw [← hy₂, map_mul, map_pow] at e1
      rw [← hu, mul_pow] at hy
      linear_combination hy + e1
    rcases mul_eq_zero.mp hkey with h | h
    · exact absurd (pow_eq_zero_iff'.mp h).1 hlx0
    · have hy' : y = ((u⁻¹ : (T₁.ring)ˣ) : T₁.ring) ^ ν * lam y₂ := by
        have : (u : T₁.ring) ^ ν * y = lam y₂ := sub_eq_zero.mp h
        rw [← this, ← mul_assoc, ← mul_pow, Units.inv_mul, one_pow, one_mul]
      rw [hy']
      exact Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _ (Ideal.subset_span
        ⟨T₂.xR, h2, f, hf, ν, hν, hy₂.symm ▸ by rw [mul_comm]⟩))
  · unfold strictTransformIdeal
    rw [Ideal.map_span, Ideal.span_le]
    rintro _ ⟨y₂, ⟨x₂', hx₂', f, hf, ν, hν, hy₂⟩, rfl⟩
    refine Ideal.subset_span ⟨lam x₂', ?_, f, hf, ν, hν, ?_⟩
    · rw [← Set.image_singleton (f := lam), ← Ideal.map_span, hx₂', hmapQ]
    · rw [← map_pow, ← map_mul, hy₂, hlam]

end StrictTransformCopy

end MonoidalTransform

section Lemma8

variable {R : Type u} [CommRing R] [IsRegularLocalRing R] [IsDomain R]

/-- **Lemma 8 of §3 for the exact division `x^ν h = f`** (the bound `ν_{M₁}(g_j) ≤ ν_M(f_j)` that
the proof of Corollary 1 of Proposition 2 uses implicitly): for a monoidal transform `t` of `R`
with prime center `Q` (`R/Q` regular), residually separable algebraic over `R`, an element `f` with
`ν_M(f) = ν_Q(f) = ν` and `x^ν h = f` where `x ≠ 0` and `(x)t.ring = Q t.ring`, we have
`ν_{M₁}(h) ≤ ν_M(f)`.

Deviation from the paper (gap filled): in the proof of Corollary 1 the paper passes from
"(vi) is equivalent to saying that `ν_H(g_j) = ν_j`" to Theorem 5, whose hypothesis is
`ν_{M₁'}(g_j) = ν_j`.  Since `H ⊆ M₁'` we have `ν_H(g_j) ≤ ν_{M₁'}(g_j)`, and this lemma gives the
other inequality `ν_{M₁'}(g_j) ≤ ν_M(f_j) = ν_j` (the proof is that of `(1)` in
`ordElem_eq_and_ordElem_localization_eq_of_strictTransform`). -/
@[blueprint "lem:III.8-cor1-lemma8"
  (statement := /-- Let $R$ be a regular local ring, $Q$ a prime ideal with $R/Q$ regular, $R_1$ a
    monoidal transform of $R$ with center $Q$ which is residually separable algebraic over $R$, and
    $x\ne0$ with $(x)R_1=QR_1$. If $f\in R$ satisfies $\nu_M(f)=\nu_Q(f)=\nu$ and
    $x^\nu h=f$ with $h\in R_1$, then $\nu_{M_1}(h)\le\nu_M(f)$. -/)
  (proof := /-- The weak transform of $(f)$ in $R_1$ is $(h)$, and $\nu_Q((f))=\nu_M((f))$;
    Lemma~8 of \S3 (\cref{lem:III.8}) gives $\nu((h))\le\nu((f))$. \textbf{Gap in the paper
    filled.} The paper uses $\nu_{M_1'}(g_j)=\nu_j$ (the hypothesis of Theorem~5) without
    derivation. -/)
  (latexEnv := "lemma")]
theorem MonoidalTransform.ordElem_maximalIdeal_le_of_pow_mul_eq (Q : Ideal R) [Q.IsPrime]
    [IsRegularLocalRing (R ⧸ Q)] (t : MonoidalTransform R Q) [IsLocalHom t.toRing]
    [IsRegularLocalRing t.ring]
    (hsep : RingHom.IsResiduallySeparableAlgebraic (R := R) (R' := t.ring) t.toRing)
    (x : R) (hx0' : x ≠ 0) (hx : Q.map t.toRing = Ideal.span {t.toRing x}) (f : R) (ν : ℕ)
    (hν : (ν : ℕ∞) = Ideal.ordElem Q f) (hMQ : Ideal.ordElem (maximalIdeal R) f = Ideal.ordElem Q f)
    (h : t.ring) (hh : t.toRing x ^ ν * h = t.toRing f) :
    Ideal.ordElem (maximalIdeal t.ring) h ≤ Ideal.ordElem (maximalIdeal R) f := by
  classical
  have hinj := MonoidalTransform.toRing_injective t
  have hf0 : f ≠ 0 := fun h0 => by
    rw [h0, Ideal.ordElem_eq_top_iff.mpr fun n => zero_mem (Q ^ n)] at hν
    exact ENat.natCast_ne_top _ hν
  have hx0 : t.toRing x ≠ 0 := fun h0 => hx0' (hinj (h0.trans (map_zero _).symm))
  have hJ0 : Ideal.span {f} ≠ ⊥ := by rw [ne_eq, Ideal.span_singleton_eq_bot]; exact hf0
  have hPJ : Ideal.ord Q (Ideal.span {f}) = Ideal.nu (Ideal.span {f}) := by
    simp only [Ideal.nu, Ideal.ord_span_singleton, hMQ]
  have halg : RingHom.IsResiduallyAlgebraic (R := R) (R' := t.ring) t.toRing := by
    let _ : Algebra (ResidueField R) (ResidueField t.ring) :=
      (ResidueField.map t.toRing).toAlgebra
    have _ : Algebra.IsSeparable (ResidueField R) (ResidueField t.ring) := hsep
    exact Algebra.IsSeparable.isAlgebraic _ _
  have h8 := nu_weakTransform_le R (Ideal.span {f}) hJ0 Q hPJ t halg
  obtain ⟨-, -, -, -, h5⟩ := t.divIdeal_monotone_and_strictTransformIdeal_eq_iSup inferInstance
    inferInstance (Ideal.span {f}) (t.toRing x) hx.symm
  obtain ⟨ν', hν', -, hweak⟩ := h5 hJ0 (Ideal.IsPrime.ne_top inferInstance)
  have hνν' : ν' = ν := by
    have : (ν' : ℕ∞) = ν := by rw [← hν', Ideal.ord_span_singleton, hν]
    exact_mod_cast this
  have hdiv : t.divIdeal (t.toRing x) ν' (Ideal.span {f}) = Ideal.span {h} := by
    rw [hνν']
    apply le_antisymm
    · rw [MonoidalTransform.divIdeal, Ideal.span_le]
      rintro y ⟨f', hf', hy⟩
      obtain ⟨r, rfl⟩ := Ideal.mem_span_singleton'.mp hf'
      rw [SetLike.mem_coe, Ideal.mem_span_singleton']
      refine ⟨t.toRing r, mul_left_cancel₀ (pow_ne_zero ν hx0) ?_⟩
      rw [hy, map_mul, ← hh]
      ring
    · rw [Ideal.span_le, Set.singleton_subset_iff]
      exact Ideal.subset_span ⟨f, Ideal.mem_span_singleton_self _, hh⟩
  rw [hweak, hdiv] at h8
  simpa only [Ideal.nu, Ideal.ord_span_singleton] using h8

end Lemma8

section LocalizationEquiv

variable {A B : Type u} [CommRing A] [CommRing B]

/-- The composite `A → A_H ≃ B` of the localization map at a prime `H` with a ring isomorphism. -/
noncomputable def localizationEquivHom (H : Ideal A) [H.IsPrime]
    (L : Localization.AtPrime H ≃+* B) :
    A →+* B :=
  (L : Localization.AtPrime H →+* B).comp (algebraMap A (Localization.AtPrime H))

/-- The contraction of the maximal ideal of `B ≃ A_H` to `A` is `H`. -/
theorem comap_maximalIdeal_localizationEquivHom [IsLocalRing B] (H : Ideal A) [H.IsPrime]
    (L : Localization.AtPrime H ≃+* B) :
    (maximalIdeal B).comap (localizationEquivHom H L) = H := by
  have h1 : (maximalIdeal B).comap (L : Localization.AtPrime H →+* B) =
      maximalIdeal (Localization.AtPrime H) := by
    rw [← IsLocalRing.map_ringEquiv_maximalIdeal L]
    exact Ideal.comap_map_of_bijective _ L.bijective
  rw [localizationEquivHom, ← Ideal.comap_comap, h1]
  exact IsLocalization.AtPrime.under_maximalIdeal _ H

/-- The extension of the contraction of an ideal of `B ≃ A_H` is the ideal itself. -/
theorem map_comap_localizationEquivHom (H : Ideal A) [H.IsPrime] (L : Localization.AtPrime H ≃+* B)
    (I : Ideal B) : (I.comap (localizationEquivHom H L)).map (localizationEquivHom H L) = I := by
  rw [localizationEquivHom, ← Ideal.comap_comap, ← Ideal.map_map]
  have h1 : ((I.comap (L : Localization.AtPrime H →+* B)).comap
      (algebraMap A (Localization.AtPrime H))).map (algebraMap A (Localization.AtPrime H)) =
        I.comap (L : Localization.AtPrime H →+* B) :=
    IsLocalization.map_under H.primeCompl (Localization.AtPrime H) _
  rw [h1]
  exact Ideal.map_comap_of_surjective _ L.surjective I

end LocalizationEquiv

section Descent

/-- **Theorem 3 of Ch. II, §3, for a localization** (p. 260, "Therefore, by Theorem 3, §3, Ch. II,
if `P₁` is a permissible center for `J₁`, then `P₁'` is a permissible center for `J₁'`"): let `O` be
a local ring, `J ⊆ P ⊆ H` ideals with `P`, `H` prime and `O/P`, `O/H` regular, and `L : O_H ≃ B` a
ring isomorphism; put `λ = L ∘ (O → O_H)`.  If `H` is normally flat modulo `J` and `λ(P)` is
normally flat modulo `λ(J)` in `B`, then `P` is normally flat modulo `J`.

Deviation from the paper (gap filled): the paper applies Theorem 3 of Ch. II to "`R₁ = (R₁')_H`,
`J₁ = (J₁')R₁` and `P₁ = (P₁')R₁`" without comment; here the identification of `(O/J)_{H/J}` with
`B/λ(J)` (the localization of a quotient is the quotient of the localization) and of the images of
the ideals is carried out. -/
@[blueprint "lem:III.8-cor1-descent"
  (statement := /-- Let $O$ be a noetherian local ring, $J\subseteq P\subseteq H$ ideals of $O$
    with $P$, $H$ prime and $O/P$, $O/H$ regular, and $B\cong O_H$. If $O/J$ is normally flat
    along $H/J$ and $B/JB$ is normally flat along $PB/JB$, then $O/J$ is normally flat along
    $P/J$. -/)
  (proof := /-- Theorem~3 of Ch.~II, \S3 (\cref{thm:II.3-3}) for the local ring $O/J$ and the
    primes $P/J\subseteq H/J$, together with $(O/J)_{H/J}\cong B/JB$. \textbf{Gap in the paper
    filled.} The paper applies Theorem~3 of Ch.~II to ``$R_1=(R_1')_H$, $J_1=(J_1')R_1$ and $P_1=(P_1')R_1$'' without comment; here the identification of $(O/J)_{H/J}$ with $B/JB$ (the localization of a quotient is the quotient of the localization) and of the images of the ideals is carried out. -/)
  (latexEnv := "lemma")]
theorem isNormallyFlatAlongIdeal_of_localizationEquiv [Hironaka.Cited.ExistsSurjectiveOfIsRegularLocalRingOfIsAdicComplete.{u}] [Hironaka.Cited.IsRegularLocalRingLocalizationOfIsRegularLocalRing.{u}] {O B : Type u} [CommRing O] [IsLocalRing O]
    [IsNoetherianRing O] [CommRing B] (J P H : Ideal O) [P.IsPrime] [H.IsPrime] (hPH : P ≤ H)
    (hJP : J ≤ P) (hPreg : IsRegularLocalRing (O ⧸ P)) (hHreg : IsRegularLocalRing (O ⧸ H))
    (L : Localization.AtPrime H ≃+* B)
    (hH : IsNormallyFlatAlongIdeal (H.map (Ideal.Quotient.mk J)))
    (hP : IsNormallyFlatAlongIdeal ((P.map (localizationEquivHom H L)).map
      (Ideal.Quotient.mk (J.map (localizationEquivHom H L))))) :
    IsNormallyFlatAlongIdeal (P.map (Ideal.Quotient.mk J)) := by
  classical
  have hJH : J ≤ H := hJP.trans hPH
  have hJtop : J ≠ ⊤ := fun h => (Ideal.IsPrime.ne_top ‹P.IsPrime›) (top_le_iff.mp (h ▸ hJP))
  have : Nontrivial (O ⧸ J) := Ideal.Quotient.nontrivial_iff.mpr hJtop
  have : IsLocalRing (O ⧸ J) := IsLocalRing.of_surjective' (Ideal.Quotient.mk J)
    Ideal.Quotient.mk_surjective
  have hPbar : (P.map (Ideal.Quotient.mk J)).IsPrime :=
    Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by rw [Ideal.mk_ker]; exact hJP)
  have hHbar : (H.map (Ideal.Quotient.mk J)).IsPrime :=
    Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by rw [Ideal.mk_ker]; exact hJH)
  have hPHbar : P.map (Ideal.Quotient.mk J) ≤ H.map (Ideal.Quotient.mk J) := Ideal.map_mono hPH
  have hreg1 : IsRegularLocalRing ((O ⧸ J) ⧸ P.map (Ideal.Quotient.mk J)) :=
    IsRegularLocalRing.of_ringEquiv (DoubleQuot.quotQuotEquivQuotOfLE hJP).symm
  have hreg2 : IsRegularLocalRing ((O ⧸ J) ⧸ H.map (Ideal.Quotient.mk J)) :=
    IsRegularLocalRing.of_ringEquiv (DoubleQuot.quotQuotEquivQuotOfLE hJH).symm
  refine ((isNormallyFlatAlongIdeal_iff_of_le (O ⧸ J) (P.map (Ideal.Quotient.mk J))
    (H.map (Ideal.Quotient.mk J)) hPHbar).mpr ⟨hH, ?_⟩)
  -- the ring isomorphism `(O/J)_{H/J} ≃ B/λ(J)`
  obtain ⟨e₁, he₁⟩ := Ideal.exists_ringEquiv_localization_quotient_of_le J H hJH
  have hJmap : J.map (localizationEquivHom H L) =
      (J.map (algebraMap O (Localization.AtPrime H))).map L :=
    (Ideal.map_map (algebraMap O (Localization.AtPrime H))
      (L : Localization.AtPrime H →+* B)).symm
  let e₂ : (Localization.AtPrime H ⧸ J.map (algebraMap O (Localization.AtPrime H))) ≃+*
      (B ⧸ J.map (localizationEquivHom H L)) :=
    Ideal.quotientEquiv _ _ L hJmap
  let E : Localization.AtPrime (H.map (Ideal.Quotient.mk J)) ≃+*
      (B ⧸ J.map (localizationEquivHom H L)) := e₁.symm.trans e₂
  have hE : ∀ r : O, E (algebraMap (O ⧸ J) _ (Ideal.Quotient.mk J r)) =
      Ideal.Quotient.mk _ (localizationEquivHom H L r) := by
    intro r
    simp only [E, RingEquiv.trans_apply]
    rw [← he₁ r, RingEquiv.symm_apply_apply]
    rfl
  have hmapE : ((P.map (Ideal.Quotient.mk J)).map (algebraMap (O ⧸ J)
      (Localization.AtPrime (H.map (Ideal.Quotient.mk J))))).map
        (E : Localization.AtPrime (H.map (Ideal.Quotient.mk J)) →+*
          (B ⧸ J.map (localizationEquivHom H L))) =
        (P.map (localizationEquivHom H L)).map
          (Ideal.Quotient.mk (J.map (localizationEquivHom H L))) := by
    rw [Ideal.map_map, Ideal.map_map, Ideal.map_map]
    congr 1
    exact RingHom.ext fun r => hE r
  refine Hironaka.isNormallyFlatAlongIdeal_of_ringEquiv E.symm _ _ ?_ hP
  rw [← hmapE, Ideal.map_map]
  convert Ideal.map_id _ using 2
  ext a
  simp

end Descent

section Assembly

variable {R : Type u} [CommRing R] [IsRegularLocalRing R] [IsDomain R]

/-- **The reduction of Corollary 1 to Proposition 2** (proof of Corollary 1, pp. 259–260): under the
hypotheses of Corollary 1 there is a monoidal transform `R₁'` of `R` with centre `Q`, regular, local
over `R` and residually separable algebraic, and a prime `P₁'` of `R₁'` over `P`, such that
`ν*(J₁') = ν*(J)` and `P₁'` is a permissible center for the strict transform `J₁'` of `J` in `R₁'`.
Proposition 2 applied to `R₁'` and `P₁'` then gives Corollary 1.

This is the whole proof of Corollary 1 except the last sentence ("This implies, by Proposition 2,
that `P` is a permissible center for `J`").  The steps follow the paper: closed point
(`exists_isMaximal_le_isRegularLocalRing_quotient`), `R₁'` and `H`
(`MonoidalTransform.exists_refinement_localization_equiv`), "`(x)R₁' = QR₁'` and `g_j ∈ J₁'`" (the
elements `g'_j = x^{-ν_j} f_j` of `R₁'`), "(vi) is equivalent to saying that `ν_H(g_j) = ν_j` for all `j`", Theorem 5
(`isStandardBase_strictTransform`, applied to a standard base contained in `(f_j)`:
`exists_isStandardBase_comp`), `H` permissible for `J₁'` (`isPermissibleCenter_tfae`), and
Theorem 3 of Ch. II (`isNormallyFlatAlongIdeal_of_localizationEquiv`).

Deviation from the paper (gap filled): "a suitable subsystem (suitably reordered) of `(g₁, …, g_m)` is a
standard base of `J₁'`" is `exists_isStandardBase_comp` applied to `(f_j)` (hypothesis (iv)) and
transported by Theorem 5; "(vi) is equivalent to saying that `ν_H(g_j) = ν_j` for all `j`" and the further bound
`ν_{M₁'}(g_j) = ν_j` are proved (`MonoidalTransform.ordElem_maximalIdeal_le_of_pow_mul_eq`, the
regularity of `R₁'/H`); the regularity of `R₁'/P₁'` ("it is a monoidal transform of `R/P` with
center `Q/P`", `MonoidalTransform.isRegularLocalRing_quotient_of_comap_eq_of_lt`) and
`J₁ = (J₁')R₁`, `P₁ = (P₁')R₁` (`MonoidalTransform.strictTransformIdeal_eq_map_of_toRing_comp`,
`map_comap_localizationEquivHom`) are proved. -/
@[blueprint "lem:III.8-cor1-reduction"
  (statement := /-- In the situation of Corollary~1 (\cref{cor:III.prop2-1}) there is a monoidal
    transform $R_1'$ of $R$ with center $Q$, regular, local over $R$ and residually separable
    algebraic over $R$, and a prime ideal $P_1'$ of $R_1'$ with $P_1'\cap R=P$, such that
    $\nu^*(J_1')=\nu^*(J)$ and $P_1'$ is a permissible center for the strict transform $J_1'$ of
    $J$ in $R_1'$. -/)
  (proof := /-- As in the proof of Corollary~1: choose $N'$, $R_1'$ and $H$
    (\cref{lem:III.8-cor1-refinement}); the elements $g_j'=x^{-\nu_j}f_j$ of $R_1'$ satisfy
    $\nu_H(g_j')=\nu_{M_1}(g_j)=\nu_j$ and $\nu_{M_1'}(g_j')=\nu_j$
    (\cref{lem:III.8-cor1-lemma8}); Theorem~5 (\cref{thm:III.5}) gives $\nu^*(J_1')=\nu^*(J)$ and a
    standard base of $J_1'$, so that $H$ is a permissible center for $J_1'$; finally
    \cref{lem:III.8-cor1-descent} (Theorem~3 of Ch.~II) gives that $P_1'=P_1\cap R_1'$ is a
    permissible center for $J_1'$, $R_1'/P_1'$ being regular as a monoidal transform of $R/P$.
    \textbf{Deviation from the paper (gap filled).} The assertion ``a suitable subsystem (suitably reordered) of $(g_1,\dots,g_m)$ is a standard base of $J_1'$'' is obtained from the standard base contained in $(f_j)$ (hypothesis (iv)) transported by Theorem~5; ``(vi) is equivalent to saying that $\nu_H(g_j)=\nu_j$ for all $j$'' and the further bound $\nu_{M_1'}(g_j)=\nu_j$ are proved; the regularity of $R_1'/P_1'$ and $J_1=(J_1')R_1$, $P_1=(P_1')R_1$, which the paper states without proof, are proved. -/)
  (latexEnv := "lemma")]
theorem exists_transform_of_perfectField_residueField [Hironaka.Cited.ExistsSurjectiveOfIsRegularLocalRingOfIsAdicComplete.{u}] [Hironaka.Cited.IsClosedComplRegularLocusOfFiniteType.{u}] [Hironaka.Cited.IsRegularLocalRingLocalizationOfIsRegularLocalRing.{u}] [Hironaka.Cited.IsSeparableFieldExtensionIff.{u}] [PerfectField (ResidueField R)]
    (J P Q : Ideal R) [P.IsPrime] [Q.IsPrime] (hPQ : P ≤ Q) (hJP : J ≤ P) (hQP : Q ≠ P)
    [IsRegularLocalRing (R ⧸ P)] [IsRegularLocalRing (R ⧸ Q)]
    {m : ℕ} (f : Fin m → R) (hfJ : ∀ j, f j ∈ J)
    (hiii : ∀ j, Ideal.ordElem (maximalIdeal R) (f j) = Ideal.ordElem Q (f j))
    (hiv : Ideal.span (Set.range fun j => initialForm (maximalIdeal R) (f j)) =
      grIdeal (maximalIdeal R) J)
    (T : MonoidalTransform R Q) [IsLocalHom T.toRing] [IsRegularLocalRing T.ring]
    (P₁ : Ideal T.ring) [P₁.IsPrime] (hv : P₁.comap T.toRing = P)
    (x : R) (hx : Q.map T.toRing = Ideal.span {T.toRing x})
    (ν : Fin m → ℕ) (hν : ∀ j, (ν j : ℕ∞) = Ideal.ordElem Q (f j))
    (g : Fin m → T.ring) (hg : ∀ j, T.toRing x ^ ν j * g j = T.toRing (f j))
    (hvi : ∀ j, Ideal.ordElem (maximalIdeal T.ring) (g j) = (ν j : ℕ∞))
    (hperm₁ : IsPermissibleCenter T.ring (strictTransformIdeal T J) P₁) :
    ∃ (T' : MonoidalTransform R Q) (_ : IsLocalHom T'.toRing) (_ : IsRegularLocalRing T'.ring)
      (_ : RingHom.IsResiduallySeparableAlgebraic (R := R) (R' := T'.ring) T'.toRing)
      (P₁' : Ideal T'.ring) (_ : P₁'.IsPrime), P₁'.comap T'.toRing = P ∧
        nuStar T'.ring (strictTransformIdeal T' J) = nuStar R J ∧
        IsPermissibleCenter T'.ring (strictTransformIdeal T' J) P₁' := by
  classical
  have hJQ : J ≤ Q := hJP.trans hPQ
  -- the closed-point refinement `R₁' = A_{N'}` of `R₁ = A_N`
  obtain ⟨T', H, hH, L, hx', hregT', hlocT', hsep, hHreg, hL⟩ :=
    MonoidalTransform.exists_refinement_localization_equiv Q ‹_› T
  have := hregT'
  have := hlocT'
  have := hH
  set lam := localizationEquivHom H L with hlam_def
  have hlam : ∀ a : R, lam (T'.toRing a) = T.toRing a := hL
  have hHmax : (maximalIdeal T.ring).comap lam = H :=
    comap_maximalIdeal_localizationEquivHom H L
  have hJ₁ : strictTransformIdeal T J = (strictTransformIdeal T' J).map lam :=
    MonoidalTransform.strictTransformIdeal_eq_map_of_toRing_comp Q T T' lam hlam J
  -- the prime `P₁' = P₁ ∩ R₁'`
  obtain ⟨hJ₁P₁, hP₁reg, hP₁nf⟩ : strictTransformIdeal T J ≤ P₁ ∧ IsRegularLocalRing (T.ring ⧸ P₁) ∧
      IsNormallyFlatAlongIdeal (P₁.map (Ideal.Quotient.mk (strictTransformIdeal T J))) := by
    rcases hperm₁ with h | ⟨-, h1, h2, h3⟩
    · exact absurd h (Ideal.IsPrime.ne_top inferInstance)
    · exact ⟨h1, h2, h3⟩
  have hP₁' : (P₁.comap lam).IsPrime := Ideal.comap_isPrime lam P₁
  have hP₁'comap : (P₁.comap lam).comap T'.toRing = P := by
    rw [Ideal.comap_comap]
    have : lam.comp T'.toRing = T.toRing := RingHom.ext hlam
    rw [this]
    exact hv
  have hP₁'H : P₁.comap lam ≤ H := by
    rw [← hHmax]
    exact Ideal.comap_mono (le_maximalIdeal (Ideal.IsPrime.ne_top inferInstance))
  have hJ₁'P₁' : strictTransformIdeal T' J ≤ P₁.comap lam := by
    intro y hy
    rw [Ideal.mem_comap]
    exact hJ₁P₁ (hJ₁ ▸ Ideal.mem_map_of_mem lam hy)
  have hJ₁'H : strictTransformIdeal T' J ≤ H := hJ₁'P₁'.trans hP₁'H
  have hP₁'reg : IsRegularLocalRing (T'.ring ⧸ P₁.comap lam) :=
    MonoidalTransform.isRegularLocalRing_quotient_of_comap_eq_of_lt Q P hPQ hQP.symm T'
      (P₁.comap lam) hP₁'comap
  -- the elements `g'_j = x^{-ν_j} f_j` of `R₁'`
  have hQf : ∀ j, Ideal.ordElem Q (f j) = ν j := fun j => (hν j).symm
  have hMf : ∀ j, Ideal.ordElem (maximalIdeal R) (f j) = ν j := fun j => (hiii j).trans (hQf j)
  have hg' : ∀ j, ∃ g' : T'.ring, T'.toRing T'.x ^ ν j * g' = T'.toRing (f j) := by
    intro j
    have hfQ : f j ∈ Q ^ ν j := Ideal.mem_pow_of_ordElem (hQf j)
    have hmem : T'.toRing (f j) ∈ (Q ^ ν j).map T'.toRing := Ideal.mem_map_of_mem _ hfQ
    rw [Ideal.map_pow, ← T'.span_xR_eq_map, Ideal.span_singleton_pow,
      Ideal.mem_span_singleton'] at hmem
    obtain ⟨c, hc⟩ := hmem
    exact ⟨c, by rw [mul_comm]; exact hc⟩
  choose g' hg' using hg'
  -- the orders of the `g'_j`
  have hT'x0 : T'.x ≠ 0 := T'.x_ne_zero
  have hxR : T.toRing T'.x = T.xR := by rw [hx']; rfl
  have hassoc : Associated T.xR (T.toRing x) :=
    Ideal.span_singleton_eq_span_singleton.mp (T.span_xR_eq_map.trans hx)
  obtain ⟨u, hu⟩ := hassoc
  have hxR0 : T.xR ≠ 0 := fun h0 =>
    T.x_ne_zero (MonoidalTransform.toRing_injective T (h0.trans (map_zero _).symm))
  have hlamg : ∀ j, lam (g' j) = (u : T.ring) ^ ν j * g j := by
    intro j
    have h1 := congrArg lam (hg' j)
    simp only [map_mul, map_pow, hlam, hxR] at h1
    have h2 := hg j
    rw [← hu, mul_pow] at h2
    refine mul_left_cancel₀ (pow_ne_zero (ν j) hxR0) ?_
    rw [h1, ← h2]
    ring
  have hordG : ∀ j, Ideal.ordElem (maximalIdeal T.ring) (lam (g' j)) = ν j := by
    intro j
    rw [hlamg, Ideal.ordElem_isUnit_mul _ ((Units.isUnit u).pow _), hvi]
  have hordH : ∀ j, Ideal.ordElem H (g' j) = ν j := by
    intro j
    have h1 := ordElem_localization_eq_of_isRegularLocalRing_quotient H hHreg (g' j)
    rw [Localization.AtPrime.map_eq_maximalIdeal] at h1
    rw [← h1]
    have h2 := Ideal.ordElem_map_ringEquiv_of_eq L (maximalIdeal (Localization.AtPrime H))
      (maximalIdeal T.ring) (IsLocalRing.map_ringEquiv_maximalIdeal L)
      (algebraMap T'.ring (Localization.AtPrime H) (g' j))
    rw [← h2]
    exact hordG j
  have hordM : ∀ j, Ideal.ordElem (maximalIdeal T'.ring) (g' j) = ν j := by
    intro j
    refine le_antisymm ?_ ((hordH j).symm.le.trans (Ideal.ordElem_mono
      (le_maximalIdeal (Ideal.IsPrime.ne_top inferInstance)) _))
    exact (MonoidalTransform.ordElem_maximalIdeal_le_of_pow_mul_eq Q T' hsep T'.x hT'x0
      T'.span_xR_eq_map.symm (f j) (ν j) (hν j) (hiii j) (g' j) (hg' j)).trans (hMf j).le
  -- Theorem 5 for `R₁'`
  obtain ⟨m', σ, -, hstd⟩ := exists_isStandardBase_comp R J f hfJ hiv
  have h5 := isStandardBase_strictTransform J Q hJQ T' hsep T'.x T'.x_mem
    T'.span_xR_eq_map.symm (f ∘ σ) (ν ∘ σ) (g' ∘ σ)
    (fun j => (hMf (σ j)).symm) (fun j => hg' (σ j)) hstd (fun j => (hiii (σ j)).symm)
    (fun j => hordM (σ j))
  -- `H` is a permissible center for `J₁'`
  have hHperm : IsPermissibleCenter T'.ring (strictTransformIdeal T' J) H := by
    refine Or.inr ⟨hH, hJ₁'H, hHreg, ?_⟩
    have h12 : IsNormallyFlatAlongIdeal (H.map (Ideal.Quotient.mk (strictTransformIdeal T' J))) ↔
        HasInitialFormSystem (strictTransformIdeal T' J) H (maximalIdeal T'.ring) :=
      (isPermissibleCenter_tfae T'.ring (strictTransformIdeal T' J) H hJ₁'H).out 1 2
    exact h12.mpr ⟨m', g' ∘ σ, h5.1.1, fun j => (hordM (σ j)).trans (hordH (σ j)).symm,
      h5.1.2.2.2.1.symm⟩
  obtain ⟨-, -, -, hHnf⟩ := hHperm.resolve_left (Ideal.IsPrime.ne_top hH)
  -- `P₁'` is a permissible center for `J₁'` (Theorem 3 of Ch. II)
  refine ⟨T', hlocT', hregT', hsep, P₁.comap lam, hP₁', hP₁'comap, h5.2, Or.inr ⟨hP₁', hJ₁'P₁',
    hP₁'reg, ?_⟩⟩
  refine isNormallyFlatAlongIdeal_of_localizationEquiv (strictTransformIdeal T' J) (P₁.comap lam) H
    hP₁'H hJ₁'P₁' hP₁'reg hHreg L hHnf ?_
  rw [← hlam_def, map_comap_localizationEquivHom H L P₁, ← hJ₁]
  exact hP₁nf

end Assembly

end Hironaka
