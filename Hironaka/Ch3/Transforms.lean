/-
Copyright (c) 2026 Daattavya Aggarwal, Minhyong Kim, Oisin Kim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daattavya Aggarwal, Minhyong Kim, Oisin Kim
-/
module

public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.Coalgebra.IsFrobenius
public import Mathlib.RingTheory.Flat.Equalizer
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.HopfAlgebra.Basic
public import Mathlib.RingTheory.KrullDimension.Regular
public import Mathlib.RingTheory.MvPolynomial.Ideal
public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
public import Mathlib.RingTheory.Polynomial.IsIntegral
public import Mathlib.RingTheory.RegularLocalRing.Polynomial
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.TotallySplit
public import Architect
public import Hironaka.Ch3.Basic
public import Hironaka.Compat.RegularQuotient
public import Hironaka.Compat.RegularGraded
public import Hironaka.Ch0.Blowup
public import Hironaka.Compat.BlowupCharts
public import Hironaka.Compat.FieldTensor
public import Hironaka.Compat.AssociatedPrimes
public import Hironaka.Compat.MapsRSOPOrder
public import Hironaka.Statements

/-!
# Ch. III §2 (pp. 209–217): monoidal transforms, canonical homomorphisms, and the strict and
# weak transforms of an ideal

> Let R be a regular local ring and P a prime ideal in R such that P ≠ (0) and S = R/P is
> regular. By a monoidal transform of R with center P, we shall mean a local ring in the field of
> quotients of R which is obtained as a localization of a ring of the form R[x⁻¹P] with x ∈ P
> with respect to a prime ideal in R[x⁻¹P] containing the maximal ideal of R. In this definition
> of monoidal transform, it is convenient to include the case in which P = R. In this case, the
> monoidal transform of R is canonically isomorphic to R. Note that we have also such an
> isomorphism when P is principal. … It is clear that the canonical injection R → R' is a local
> homomorphism.  (p. 209)

The definitions of the section (monoidal transforms, residually algebraic / rational / separable
homomorphisms, Definition 5: strict and weak transforms) are in `Hironaka/Ch3/Basic.lean`.  This
file transcribes the remaining statements of §2, in the paper's order:

* the facts of pp. 209–210: `R'` is regular, `PR' = (x₁)R'`, `dim R' = dim R` iff `R'` is
  residually algebraic over `R`, and the regular system of parameters
  `(x₁, x₂/x₁, …, x_r/x₁, y₁, …, y_s)` of a residually rational monoidal transform;
* the *canonical* local homomorphisms `R' → R̄'` of p. 211 and Lemma 4 (p. 212); its
  Corollaries 1 and 2 (pp. 212–213), on the completion, are in
  `Hironaka/Ch3/TransformsCompletion.lean`;
* Remarks 0–4 following Definition 5 (pp. 213–215), including the weak and strict transforms of a
  coherent sheaf of ideals by a monoidal transformation of a non-singular algebraic scheme;
* Lemma 5 (p. 215; "This proof was provided by D. S. Rim") and its Corollary (pp. 215–216);
* Lemma 6 (pp. 216–217).

Encoding conventions are flagged as "Formalization note (encoding)" in the docstrings and in
the blueprint texts; every place where a statement or proof departs from the paper is flagged
as "Deviation from the paper (…)", "Gap in the paper filled" or "Not formalized".  In this file: the facts of pp. 209–210 (gaps filled; the claims of
p. 209 that a monoidal transform is `R[x₁/xᵢ, …, x_r/xᵢ]_{M'}` for some index `i` and is
isomorphic to `R` for `P` principal, along the printed route; the dimension
criterion along the printed route, through the regular system of parameters
`(x₁, y₁, …, y_s, f₁, …, f_t)` of `R'`), Lemma 4 (an alternative proof through `R' ⊗_R R̄`, which
uses the flatness of `R → R̄`, `lem:III.rsop-map-flat`, which the paper does not use there),
Remarks 1–4 (gaps filled) and Lemma 6 (along the printed route, in the chart ring `A'`).  The
main encodings:
* a monoidal transform is *data* `t : MonoidalTransform R P` (an element `x` and a prime `M'`),
  while the paper counts monoidal transforms as *subrings of the field of quotients*; statements
  that count them ("only a finite number of `R̄'`", "a unique `R̂'`") are therefore phrased in
  terms of `t.subring ⊆ Frac R`, the image of `R' = R[x⁻¹P]_{M'}` in the field of quotients;
* regular local rings are integral domains: this classical fact, used tacitly by the paper, is
  not in Mathlib and is recorded as the background lemma
  `Transforms.isDomain_of_isRegularLocalRing`;
* Lean identifiers cannot contain combining diacritics, so in the *code* the paper's `R̄` and
  `P̄` are written `Rb` and `Pb`, a monoidal transform `R̄'` of `R̄` is the datum `tb`, and a
  monoidal transform `R̂'` of the completion `R̂` is the datum `th`; the prose and the blueprint
  statements keep the paper's notation.
-/

@[expose] public section

open IsLocalRing AlgebraicGeometry

open scoped TensorProduct

namespace Hironaka

universe u

/-! ### Background: regular local rings are domains -/

namespace Transforms

/-- Regular local rings are integral domains (Zariski–Samuel, Nagata [14] (25.4)); the paper
uses this tacitly whenever it speaks of "the field of quotients of `R`".  Mathlib does not have
it; it is proved in the compatibility layer (`Hironaka/Compat/RegularQuotient.lean`). -/
@[blueprint "lem:III.2-regular-local-domain"
  (statement := /-- A regular local ring is an integral domain. (Classical; used tacitly on
    p.~209: ``a local ring in the field of quotients of $R$''.) -/)
  (proof := /-- Not proved in the paper (Nagata, \emph{Local rings}, (25.4)); see
    \cref{lem:regular-local-domain}. -/)
  (latexEnv := "lemma")]
theorem isDomain_of_isRegularLocalRing (R : Type u) [CommRing R] [IsRegularLocalRing R] :
    IsDomain R :=
  _root_.Hironaka.isDomain_of_isRegularLocalRing R

end Transforms

/-! ### The monoidal transform `R' = R[x⁻¹P]_{M'}` inside the field of quotients (p. 209) -/

namespace MonoidalTransform

variable {R : Type u} [CommRing R] [IsRegularLocalRing R] [IsDomain R] {P : Ideal R}
  (t : MonoidalTransform R P)

/-- p. 209: "It is clear that the canonical injection `R → R'` is a local homomorphism."
(`M' ⊇ M R[x⁻¹P]` by the definition of a monoidal transform, so `M R' ⊆ M' R'`.) -/
instance isLocalHom_toRing : IsLocalHom t.toRing := by
  refine ((IsLocalRing.local_hom_TFAE t.toRing).out 3 1).mp ?_
  rw [MonoidalTransform.toRing, ← Ideal.map_map]
  exact (Ideal.map_mono t.le).trans
    (Localization.AtPrime.map_eq_maximalIdeal (I := t.M')).le

/-- p. 209: "`PA' = (x₁)A'`" for `A' = R[x⁻¹P]`, hence `PR' = (x)R'` in the monoidal transform
`R' = A'_{M'}`: every `p ∈ P` is `x · (p/x)` with `p/x ∈ A'`, and `x ∈ P`. -/
theorem span_xR_eq_map : Ideal.span {t.xR} = P.map t.toRing := by
  apply le_antisymm
  · rw [Ideal.span_le, Set.singleton_subset_iff]
    exact Ideal.mem_map_of_mem _ t.x_mem
  · rw [Ideal.map_le_iff_le_comap]
    intro p hp
    rw [Ideal.mem_comap, Ideal.mem_span_singleton]
    have hx : algebraMap R (FractionRing R) t.x ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective R (FractionRing R))).mpr t.x_ne_zero
    refine ⟨algebraMap (blowupAlgebra R P t.x) t.ring
      ⟨algebraMap R (FractionRing R) p / algebraMap R (FractionRing R) t.x,
        Algebra.subset_adjoin ⟨p, hp, rfl⟩⟩, ?_⟩
    show (algebraMap (blowupAlgebra R P t.x) t.ring) (algebraMap R _ p) =
      (algebraMap (blowupAlgebra R P t.x) t.ring) (algebraMap R _ t.x) * _
    rw [← map_mul]
    congr 1
    apply Subtype.ext
    simp
    field_simp

/-- The canonical homomorphism `R' = R[x⁻¹P]_{M'} → Frac(R)`: a non-zero element of the
subalgebra `R[x⁻¹P]` of the field of quotients is invertible there, so the localization at `M'`
maps to `Frac(R)`.  (p. 209: a monoidal transform is "a local ring in the field of quotients
of `R`".) -/
noncomputable def toFractionRing : t.ring →+* FractionRing R :=
  IsLocalization.lift (M := t.M'.primeCompl) (S := t.ring)
    (g := (blowupAlgebra R P t.x).val.toRingHom) fun y => by
      rw [isUnit_iff_ne_zero]
      intro h
      have hy : (y : blowupAlgebra R P t.x) = 0 := Subtype.ext (by simpa using h)
      have hmem : (y : blowupAlgebra R P t.x) ∈ t.M' := by rw [hy]; exact t.M'.zero_mem
      exact absurd hmem y.2

/-- The monoidal transform `R'` as a subring of the field of quotients of `R` (p. 209).
Formalization note (encoding): the paper's monoidal transforms are subrings of `Frac(R)`; a
`MonoidalTransform R P` is the *data* `(x, M')` producing one, and different data may produce
the same subring.  Statements of the paper that count monoidal transforms are formalized in
terms of `t.subring`. -/
noncomputable def subring : Subring (FractionRing R) :=
  RingHom.range (R := t.ring) (S := FractionRing R) t.toFractionRing

end MonoidalTransform

/-! ### The canonical map `R' → Frac(R)` and the ring `R'` inside it (p. 209)

These lemmas (the injectivity of `R' → Frac(R)`, the fraction description of the subring `R'`, the
embedding of `R[x₀⁻¹P] ⊆ R'`, the isomorphism of monoidal transforms with the same subring) are used
for the claim of p. 209 that a monoidal transform is `R[x₁/xᵢ, …, x_r/xᵢ]_{M'}` for some index `i`. -/

section SubringEmbedding

variable {R : Type u} [CommRing R] [IsRegularLocalRing R] [IsDomain R]

/-- The canonical map `R' → Frac(R)` extends the canonical map `R → Frac(R)`. -/
theorem MonoidalTransform.toFractionRing_toRing {P : Ideal R} (t : MonoidalTransform R P) (r : R) :
    t.toFractionRing (t.toRing r) = algebraMap R (FractionRing R) r := by
  show IsLocalization.lift _ (algebraMap (blowupAlgebra R P t.x) t.ring
    (algebraMap R (blowupAlgebra R P t.x) r)) = _
  rw [IsLocalization.lift_eq]
  rfl

end SubringEmbedding

section Generic

variable {S : Type u} [CommRing S] [IsRegularLocalRing S] [IsDomain S] {Q : Ideal S}

/-- The canonical map `T → Frac(S)` of a monoidal transform is injective. -/
theorem MonoidalTransform.injective_toFractionRing (T : MonoidalTransform S Q) :
    Function.Injective T.toFractionRing := by
  unfold MonoidalTransform.toFractionRing
  rw [IsLocalization.lift_injective_iff]
  intro a b
  constructor
  · intro h
    have : a = b := IsLocalization.injective T.ring (Ideal.primeCompl_le_nonZeroDivisors T.M') h
    rw [this]
  · intro h
    have : a = b := Subtype.ext h
    rw [this]

/-- The canonical map `T → Frac(S)` restricts to the inclusion on `S[x⁻¹Q]`. -/
theorem MonoidalTransform.toFractionRing_algebraMap_blowupAlgebra (T : MonoidalTransform S Q)
    (a : blowupAlgebra S Q T.x) :
    T.toFractionRing (algebraMap (blowupAlgebra S Q T.x) T.ring a) = (a : FractionRing S) :=
  IsLocalization.lift_eq _ a

/-- A fraction description of the elements of the subring `T ⊆ Frac(S)`: `y ∈ T` iff
`y · s = a` for some `a, s ∈ S[x⁻¹Q]` with `s ∉ M'`. -/
theorem MonoidalTransform.mem_subring_iff (T : MonoidalTransform S Q) (y : FractionRing S) :
    y ∈ T.subring ↔ ∃ a s : blowupAlgebra S Q T.x, s ∉ T.M' ∧ y * (s : FractionRing S) = a := by
  constructor
  · rintro ⟨z, rfl⟩
    obtain ⟨⟨a, s⟩, hz⟩ := IsLocalization.mk'_surjective T.M'.primeCompl z
    refine ⟨a, s, s.2, ?_⟩
    have hz' : z * algebraMap _ T.ring (s : blowupAlgebra S Q T.x) = algebraMap _ T.ring a := by
      rw [← hz]; exact IsLocalization.mk'_spec _ _ _
    have := congrArg T.toFractionRing hz'
    rwa [map_mul, T.toFractionRing_algebraMap_blowupAlgebra, T.toFractionRing_algebraMap_blowupAlgebra] at this
  · rintro ⟨a, s, hs, h⟩
    have hs0 : (s : FractionRing S) ≠ 0 := by
      intro h0
      have : s = 0 := Subtype.ext (by simpa using h0)
      exact hs (this ▸ T.M'.zero_mem)
    have hu : IsUnit (algebraMap (blowupAlgebra S Q T.x) T.ring s) :=
      IsLocalization.map_units T.ring (⟨s, hs⟩ : T.M'.primeCompl)
    refine ⟨algebraMap _ T.ring a * ↑hu.unit⁻¹, ?_⟩
    rw [map_mul, T.toFractionRing_algebraMap_blowupAlgebra]
    have h1 : T.toFractionRing (↑hu.unit⁻¹ : T.ring) * (s : FractionRing S) = 1 := by
      have := congrArg T.toFractionRing (hu.unit.inv_mul)
      rw [map_mul, IsUnit.unit_spec, T.toFractionRing_algebraMap_blowupAlgebra, map_one] at this
      simpa using this
    calc (a : FractionRing S) * T.toFractionRing ↑hu.unit⁻¹
        = y * (s : FractionRing S) * T.toFractionRing ↑hu.unit⁻¹ := by rw [h]
      _ = y * (T.toFractionRing ↑hu.unit⁻¹ * (s : FractionRing S)) := by ring
      _ = y := by rw [h1, mul_one]

/-- If the subalgebra `S[x''⁻¹Q]` of `Frac(S)` lies in the monoidal transform `T` (as a subring
of `Frac(S)`), it embeds into `T`. -/
noncomputable def MonoidalTransform.liftBlowupAlgebra (T : MonoidalTransform S Q) {x'' : S}
    (h : ∀ a ∈ blowupAlgebra S Q x'', a ∈ T.toFractionRing.range) :
    blowupAlgebra S Q x'' →+* T.ring :=
  (RingEquiv.ofBijective T.toFractionRing.rangeRestrict
    ⟨fun a b hab => T.injective_toFractionRing (by simpa using congrArg Subtype.val hab),
      T.toFractionRing.rangeRestrict_surjective⟩).symm.toRingHom.comp
    ((blowupAlgebra S Q x'').val.toRingHom.codRestrict T.toFractionRing.range fun a => h a a.2)

theorem MonoidalTransform.toFractionRing_liftBlowupAlgebra (T : MonoidalTransform S Q) {x'' : S}
    (h : ∀ a ∈ blowupAlgebra S Q x'', a ∈ T.toFractionRing.range) (a : blowupAlgebra S Q x'') :
    T.toFractionRing (T.liftBlowupAlgebra h a) = (a : FractionRing S) := by
  have h1 := RingEquiv.apply_symm_apply (RingEquiv.ofBijective T.toFractionRing.rangeRestrict
    ⟨fun a b hab => T.injective_toFractionRing (by simpa using congrArg Subtype.val hab),
      T.toFractionRing.rangeRestrict_surjective⟩) ⟨(a : FractionRing S), h a a.2⟩
  exact congrArg Subtype.val h1

end Generic

section DimEq2

variable {S : Type u} [CommRing S] [IsRegularLocalRing S] [IsDomain S] {Q : Ideal S}

/-- Two monoidal transforms with the same subring of `Frac(S)` are isomorphic rings. -/
noncomputable def MonoidalTransform.ringEquivSubring (T : MonoidalTransform S Q) :
    T.ring ≃+* T.subring :=
  RingEquiv.ofBijective T.toFractionRing.rangeRestrict
    ⟨fun _a _b hab => T.injective_toFractionRing (Subtype.ext_iff.mp hab),
      T.toFractionRing.rangeRestrict_surjective⟩

/-- Two monoidal transforms with the same subring of `Frac(S)` are isomorphic rings. -/
noncomputable def MonoidalTransform.ringEquivOfSubringEq (T₁ T₂ : MonoidalTransform S Q)
    (h : T₁.subring = T₂.subring) : T₁.ring ≃+* T₂.ring :=
  T₁.ringEquivSubring.trans ((RingEquiv.subringCongr h).trans T₂.ringEquivSubring.symm)

theorem MonoidalTransform.toFractionRing_ringEquivOfSubringEq (T₁ T₂ : MonoidalTransform S Q)
    (h : T₁.subring = T₂.subring) (z : T₁.ring) :
    T₂.toFractionRing (T₁.ringEquivOfSubringEq T₂ h z) = T₁.toFractionRing z := by
  have h1 := T₂.ringEquivSubring.apply_symm_apply
    (RingEquiv.subringCongr h (T₁.ringEquivSubring z))
  have h2 := congrArg Subtype.val h1
  exact h2

end DimEq2

/-! ### The facts of pp. 209–210 -/

section Facts

variable {R : Type u} [CommRing R] [IsRegularLocalRing R] [IsDomain R] {P : Ideal R}

/-- One step: if `B_{q'}` is regular local for `q' = p ∩ B`, then `B[X]_p` is regular local,
provided `p ∩ B` ... (copied from Mathlib's `Polynomial.isRegularRing_of_isRegularRing`;
adapted from Mathlib, Apache-2.0, © the Mathlib contributors). -/
private theorem isRegularLocalRing_atPrime_of_comap_C {B : Type u} [CommRing B] (p : Ideal (Polynomial B)) [p.IsPrime]
    [IsRegularLocalRing (Localization.AtPrime (p.comap Polynomial.C))] :
    IsRegularLocalRing (Localization.AtPrime p) := by
  open Polynomial in
  let q := p.comap C
  let S := (Localization.AtPrime q)[X]
  let pc := Submonoid.map Polynomial.C.toMonoidHom q.primeCompl
  let : Algebra B[X] S := Polynomial.algebra B (Localization.AtPrime q)
  have : IsLocalization pc S := Polynomial.isLocalization _ _
  let pS := p.map (algebraMap B[X] S)
  have disj : Disjoint (pc : Set B[X]) (p : Set B[X]) := by
    simpa [pc, q] using! Set.disjoint_image_left.mpr
      (Set.disjoint_compl_left_iff_subset.mpr (fun _ a ↦ a))
  have : pS.IsPrime := IsLocalization.isPrime_of_isPrime_disjoint pc _ _ ‹_› disj
  have : IsLocalization.AtPrime (Localization.AtPrime pS) p := by
    convert IsLocalization.isLocalization_isLocalization_atPrime_isLocalization pc
      (Localization.AtPrime pS) pS
    exact (IsLocalization.under_map_of_isPrime_disjoint pc _ ‹_› disj).symm
  have eq : Ideal.comap C pS = maximalIdeal (Localization.AtPrime q) := by
    rw [← IsLocalization.map_under q.primeCompl _ (Ideal.comap C pS),
      ← IsLocalization.map_under q.primeCompl _ (maximalIdeal (Localization.AtPrime q))]
    simp only [Ideal.comap_comap, S, pS]
    rw [← Polynomial.algebraMap_eq (R := Localization.AtPrime q),
      ← IsScalarTower.algebraMap_eq B (Localization.AtPrime q) (Localization.AtPrime q)[X],
      IsScalarTower.algebraMap_eq B B[X] (Localization.AtPrime q)[X], ← Ideal.comap_comap,
      ← Ideal.under_def B[X], IsLocalization.under_map_of_isPrime_disjoint pc _ ‹_› disj]
    simp [q, IsLocalization.AtPrime.under_maximalIdeal (Localization.AtPrime q) q]
  have := Polynomial.isRegularLocalRing_localization_atPrime_of_comap_eq_maximalIdeal _ pS eq
  exact IsRegularLocalRing.of_ringEquiv (R := Localization.AtPrime pS)
    (IsLocalization.algEquiv p.primeCompl
      (Localization.AtPrime pS) (Localization.AtPrime p)).toRingEquiv

/-- Transport along a ring isomorphism. -/
private theorem isRegularLocalRing_atPrime_comap_ringEquiv {B B' : Type u} [CommRing B] [CommRing B'] (e : B ≃+* B')
    (p : Ideal B')
    [p.IsPrime] [IsRegularLocalRing (Localization.AtPrime p)] :
    IsRegularLocalRing (Localization.AtPrime (p.comap e)) :=
  IsRegularLocalRing.of_ringEquiv (R := Localization.AtPrime p) (IsLocalization.ringEquivOfRingEquiv
    (Localization.AtPrime (p.comap e)) (Localization.AtPrime p) e
      (e.map_primeCompl_comap_eq p)).symm

private theorem isRegularLocalRing_atPrime_of_eq {B : Type u} [CommRing B] {p q : Ideal B} [p.IsPrime]
    [q.IsPrime] (hpq : p = q)
    (h : IsRegularLocalRing (Localization.AtPrime p)) :
    IsRegularLocalRing (Localization.AtPrime q) := by
  subst hpq
  exact h

private theorem isRegularLocalRing_atPrime_mvPolynomial_of_comap_C_eq (S : Type u) [CommRing S] [IsRegularLocalRing S] :
    ∀ (n : ℕ) (q : Ideal (MvPolynomial (Fin n) S)) [q.IsPrime],
      q.comap MvPolynomial.C = maximalIdeal S →
      IsRegularLocalRing (Localization.AtPrime q) := by
  intro n
  induction n with
  | zero =>
    intro q _ hq
    let e : MvPolynomial (Fin 0) S ≃+* S := (MvPolynomial.isEmptyAlgEquiv S (Fin 0)).toRingEquiv
    have hqe : q = (maximalIdeal S).comap e := by
      ext f
      rw [Ideal.mem_comap, ← hq, Ideal.mem_comap]
      have : MvPolynomial.C (e f) = f := by
        simp only [e, AlgEquiv.coe_toRingEquiv]
        exact (MvPolynomial.eq_C_of_isEmpty f).symm
      rw [this]
    have : IsRegularLocalRing (Localization.AtPrime (maximalIdeal S)) :=
      IsRegularLocalRing.of_ringEquiv (IsLocalization.atUnits S (maximalIdeal S).primeCompl
        (fun x ↦ by simpa using! fun a ↦ a)).toRingEquiv
    subst hqe
    exact isRegularLocalRing_atPrime_comap_ringEquiv e (maximalIdeal S)
  | succ n ih =>
    intro q _ hq
    let φ := (MvPolynomial.finSuccEquiv S n).toRingEquiv
    let p := q.comap (φ.symm : Polynomial (MvPolynomial (Fin n) S) →+* MvPolynomial (Fin (n + 1)) S)
    have hpq : p.comap (φ : MvPolynomial (Fin (n + 1)) S →+* Polynomial (MvPolynomial (Fin n) S)) =
        q := by
      simp only [p, Ideal.comap_comap]
      conv_rhs => rw [← Ideal.comap_id q]
      congr 1
      ext f <;> simp [φ]
    have hC : ((φ.symm : Polynomial (MvPolynomial (Fin n) S) →+* MvPolynomial (Fin (n + 1)) S).comp
        (Polynomial.C.comp MvPolynomial.C)) = MvPolynomial.C := by
      refine RingHom.ext fun s => ?_
      have := (MvPolynomial.finSuccEquiv S n).symm.commutes s
      simpa [φ, Polynomial.algebraMap_apply, MvPolynomial.algebraMap_eq] using this
    have hp' : (p.comap Polynomial.C).comap MvPolynomial.C = maximalIdeal S := by
      rw [← hq]
      simp only [p, Ideal.comap_comap]
      rw [RingHom.comp_assoc, hC]
    have := ih (p.comap Polynomial.C) hp'
    have := isRegularLocalRing_atPrime_of_comap_C p
    exact isRegularLocalRing_atPrime_of_eq hpq (h := isRegularLocalRing_atPrime_comap_ringEquiv φ p)

/-- If `x ≠ 0` lies in the maximal ideal of the noetherian local domain `A` and `A/xA` is regular,
then `A` is regular: `M` needs at most one generator more than `M/xA`, and
`dim A/xA + 1 ≤ dim A`. -/
private theorem isRegularLocalRing_of_quotient_span_singleton {A : Type u} [CommRing A] [IsLocalRing A]
    [IsNoetherianRing A] [IsDomain A] {x : A} (hx : x ∈ maximalIdeal A) (hx0 : x ≠ 0)
    (h : IsRegularLocalRing (A ⧸ Ideal.span {x})) : IsRegularLocalRing A := by
  classical
  apply IsRegularLocalRing.of_spanFinrank_maximalIdeal_le
  have hlocal : IsLocalHom (Ideal.Quotient.mk (Ideal.span {x})) :=
    IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective
  obtain ⟨V, hVcard, hVspan⟩ :=
    (IsNoetherian.noetherian (maximalIdeal (A ⧸ Ideal.span {x}))
      ).exists_span_finset_card_eq_spanFinrank
  set σ := Function.surjInv (Ideal.Quotient.mk_surjective (I := Ideal.span {x}))
  set W : Finset A := insert x (V.image σ)
  have hW : Ideal.span (W : Set A) = maximalIdeal A := by
    apply le_antisymm
    · rw [Ideal.span_le, Finset.coe_insert]
      refine Set.insert_subset hx fun a ha => ?_
      obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp ha
      have hvM : v ∈ maximalIdeal (A ⧸ Ideal.span {x}) := hVspan ▸ Submodule.subset_span hv
      rw [← Function.surjInv_eq (Ideal.Quotient.mk_surjective (I := Ideal.span {x})) v] at hvM
      exact (IsLocalRing.mem_maximalIdeal _).mpr fun hu =>
        (IsLocalRing.mem_maximalIdeal _).mp hvM (hu.map _)
    · intro a ha
      refine mem_span_insert_image_surjInv x a V ?_
      have : Ideal.span (V : Set (A ⧸ Ideal.span {x})) = maximalIdeal (A ⧸ Ideal.span {x}) :=
        hVspan
      rw [this]
      exact map_nonunit _ a ha
  have h1 : (maximalIdeal A).spanFinrank ≤ V.card + 1 := by
    rw [← hW]
    refine (Submodule.spanFinrank_span_le_ncard_of_finite (Finset.finite_toSet W)).trans ?_
    rw [Set.ncard_coe_finset]
    exact (Finset.card_insert_le _ _).trans (Nat.succ_le_succ Finset.card_image_le)
  have h2 := ringKrullDim_quotient_succ_le_of_nonZeroDivisor (mem_nonZeroDivisors_of_ne_zero hx0)
  have h3 := h.spanFinrank_maximalIdeal
  rw [← hVcard] at h3
  calc ((maximalIdeal A).spanFinrank : WithBot ℕ∞) ≤ ((V.card + 1 : ℕ) : WithBot ℕ∞) := by
        exact_mod_cast h1
    _ = (V.card : WithBot ℕ∞) + 1 := by push_cast; rfl
    _ ≤ ringKrullDim A := by rw [h3]; exact h2

/-- The canonical map `R → R'` of a monoidal transform is injective. -/
theorem MonoidalTransform.toRing_injective (t : MonoidalTransform R P) :
    Function.Injective t.toRing := by
  have h1 : Function.Injective (algebraMap R (blowupAlgebra R P t.x)) := by
    intro a b hab
    have := congrArg (fun y : blowupAlgebra R P t.x => (y : FractionRing R)) hab
    simp only [Subalgebra.coe_algebraMap] at this
    exact IsFractionRing.injective R (FractionRing R) this
  have h2 : Function.Injective (algebraMap (blowupAlgebra R P t.x) t.ring) :=
    IsLocalization.injective t.ring (Ideal.primeCompl_le_nonZeroDivisors t.M')
  exact h2.comp h1

/-- The exchange step of p. 209, for any generator `x` of `PR'`: if `x ∈ P` and `PR' = (x)R'`, then `x`
is part of a minimal system of generators of `M` which spans `P` (if all coefficients of
`x = Σ cᵢ tᵢ` were in `M`, then `1 = Σ cᵢ (tᵢ/x) ∈ MR'`, which is contained in the maximal ideal
of `R'`).  The paper uses this for `x` in Lemma 6 ("Let us take a minimal base `(x, x₁, …, x_r)` of
the prime ideal `P`", p. 216). -/
theorem MonoidalTransform.exists_minimal_generators_of_span_eq_map (t : MonoidalTransform R P)
    (hS : IsRegularLocalRing (R ⧸ P)) [P.IsPrime] {x : R} (hxP : x ∈ P)
    (hx : Ideal.span {t.toRing x} = P.map t.toRing) :
    ∃ (S : Finset R) (r : ℕ) (z : Fin (r + 1) → R),
      Ideal.span (S : Set R) = maximalIdeal R ∧ S.card = (maximalIdeal R).spanFinrank ∧
      Function.Injective z ∧ (∀ i, z i ∈ S) ∧ z 0 = x ∧ Ideal.span (Set.range z) = P := by
  classical
  obtain ⟨S, T, hSM, hScard, hTS, hTP⟩ := exists_finset_span_eq_prime R P hS
  have hxT : x ∈ Ideal.span (T : Set R) := hTP ▸ hxP
  obtain ⟨c, -, hc⟩ := Submodule.mem_span_finset.mp hxT
  -- `x ≠ 0`, because `PR' ≠ 0`
  have hX0 : t.toRing x ≠ 0 := by
    intro h0
    have h := hx ▸ Ideal.mem_map_of_mem t.toRing t.x_mem
    rw [h0, Ideal.mem_span_singleton, zero_dvd_iff, ← map_zero t.toRing] at h
    exact t.x_ne_zero (MonoidalTransform.toRing_injective t h)
  -- some coefficient is a unit
  have hunit : ∃ t₀ ∈ T, c t₀ ∉ maximalIdeal R := by
    by_contra hcon
    push Not at hcon
    have hdiv : ∀ s ∈ T, ∃ u : t.ring, t.toRing x * u = t.toRing s := fun s hs => by
      have := hx ▸ Ideal.mem_map_of_mem t.toRing (hTP ▸ Ideal.subset_span hs : s ∈ P)
      obtain ⟨u, hu⟩ := Ideal.mem_span_singleton'.mp this
      exact ⟨u, by rw [mul_comm]; exact hu⟩
    choose! u hu using hdiv
    have h1 : t.toRing x * ∑ s ∈ T, t.toRing (c s) * u s = t.toRing x * 1 := by
      rw [mul_one, Finset.mul_sum]
      conv_rhs => rw [← hc]
      rw [map_sum]
      refine Finset.sum_congr rfl fun s hs => ?_
      rw [smul_eq_mul, map_mul, ← hu s hs]
      ring
    have h2 : ∑ s ∈ T, t.toRing (c s) * u s = 1 := mul_left_cancel₀ hX0 h1
    have h3 : (1 : t.ring) ∈ maximalIdeal t.ring := by
      rw [← h2]
      exact sum_mem fun s hs => Ideal.mul_mem_right _ _
        ((IsLocalRing.mem_maximalIdeal _).mpr (map_nonunit t.toRing (c s)
          ((IsLocalRing.mem_maximalIdeal _).mp (hcon s hs))))
    exact (maximalIdeal.isMaximal t.ring).ne_top ((Ideal.eq_top_iff_one _).mpr h3)
  obtain ⟨t₀, ht₀T, ht₀⟩ := hunit
  have hu : IsUnit (c t₀) := (IsLocalRing.mem_maximalIdeal _).not.mp ht₀ |> not_not.mp
  -- `t₀ ∈ (x, T \ {t₀})`
  have hsplit : c t₀ * t₀ = x - ∑ a ∈ T.erase t₀, c a • a := by
    rw [← hc, ← Finset.add_sum_erase T _ ht₀T, smul_eq_mul]
    ring
  have ht₀mem : ∀ {I : Ideal R}, x ∈ I → (∀ a ∈ T.erase t₀, a ∈ I) → t₀ ∈ I := by
    intro I hxI hTI
    obtain ⟨v, hv⟩ := hu.exists_left_inv
    have : t₀ = v * (x - ∑ a ∈ T.erase t₀, c a • a) := by
      rw [← hsplit, ← mul_assoc, hv, one_mul]
    rw [this]
    exact I.mul_mem_left _ (sub_mem hxI (sum_mem fun a ha => I.smul_mem _ (hTI a ha)))
  -- the new systems
  have hxS : x ∉ S.erase t₀ := by
    intro hx
    refine notMem_span_of_minimal hSM hScard (Finset.erase_subset t₀ S) (hTS ht₀T)
      (Finset.notMem_erase t₀ S) (ht₀mem (Ideal.subset_span hx) fun a ha => Ideal.subset_span ?_)
    exact Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp ha).1, hTS (Finset.mem_erase.mp ha).2⟩
  have hxM : x ∈ maximalIdeal R := IsLocalRing.le_maximalIdeal (Ideal.IsPrime.ne_top ‹_›) hxP
  let e := (T.erase t₀).equivFin
  refine ⟨insert x (S.erase t₀), (T.erase t₀).card,
    Fin.cons x (fun i => ((e.symm i : T.erase t₀) : R)), ?_, ?_, ?_, ?_, Fin.cons_zero _ _, ?_⟩
  · apply le_antisymm
    · rw [Ideal.span_le, Finset.coe_insert]
      refine Set.insert_subset hxM fun a ha => ?_
      rw [← hSM]
      exact Ideal.subset_span (Finset.mem_of_mem_erase ha)
    · rw [← hSM, Ideal.span_le]
      intro a ha
      by_cases hat : a = t₀
      · subst hat
        refine ht₀mem (Ideal.subset_span (by simp)) fun b hb => Ideal.subset_span ?_
        simp only [Finset.coe_insert, Set.mem_insert_iff, Finset.mem_coe, Finset.mem_erase]
        exact Or.inr ⟨(Finset.mem_erase.mp hb).1, hTS (Finset.mem_erase.mp hb).2⟩
      · exact Ideal.subset_span (by simp [hat, ha])
  · rw [Finset.card_insert_of_notMem hxS, Finset.card_erase_of_mem (hTS ht₀T), hScard.symm]
    have := Finset.card_pos.mpr ⟨t₀, hTS ht₀T⟩
    omega
  · rw [Fin.cons_injective_iff]
    refine ⟨fun ⟨i, hi⟩ => hxS ?_, fun i j hij => e.symm.injective (Subtype.ext hij)⟩
    rw [← hi]
    exact Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp (e.symm i).2).1,
      hTS (Finset.mem_erase.mp (e.symm i).2).2⟩
  · intro i
    refine Fin.cases (by simp) (fun i => ?_) i
    simp only [Fin.cons_succ]
    exact Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp (e.symm i).2).1,
      hTS (Finset.mem_erase.mp (e.symm i).2).2⟩)
  · have hrange : Set.range (fun i => ((e.symm i : T.erase t₀) : R)) = (T.erase t₀ : Set R) := by
      ext a
      constructor
      · rintro ⟨i, rfl⟩
        exact (e.symm i).2
      · intro ha
        exact ⟨e ⟨a, ha⟩, by simp⟩
    rw [Fin.range_cons, hrange]
    apply le_antisymm
    · rw [Ideal.span_le]
      refine Set.insert_subset hxP fun a ha => ?_
      rw [← hTP]
      exact Ideal.subset_span (Finset.mem_of_mem_erase ha)
    · refine (le_of_eq hTP.symm).trans (Ideal.span_le.mpr fun a ha => ?_)
      by_cases hat : a = t₀
      · subst hat
        exact ht₀mem (Ideal.subset_span (Set.mem_insert _ _))
          fun b hb => Ideal.subset_span (Set.mem_insert_of_mem _ hb)
      · exact Ideal.subset_span (Set.mem_insert_of_mem _ (by simp [hat, ha]))

/-- The exchange step of p. 209: `x` is part of a minimal system of generators of `M` which
spans `P` (if all coefficients of `x = Σ cᵢ tᵢ` were in `M`, then `1 = Σ cᵢ (tᵢ/x) ∈ M R[x⁻¹P]`,
which is contained in the prime `M'`).  This is the form, for the data `(x, M')`, of the paper's
renaming "`R' = A'_{M'}` with `A' = R[x₂/x₁, …, x_r/x₁]`" used by the proofs below that start from
`x₁ = x`; the claim of p. 209 for a *given* minimal base, "there exist an index `i` …", is
`exists_index_subring_eq_localization`.

The paper has no statement about the given `x`: it chooses the element `x₁` of a minimal base (the index
`i` of p. 209, "renaming") and works with the monoidal transform with that element, which has the same
subring of `Frac R` (`exists_transform_eq_subring_and_minimal_generators`).  The statement here, for the
datum `t` itself, needs `x ∈ P ∖ MP`, which is the (unargued) fact that the exchange step proves; the
index `i` of p. 209 does not give it for `x` (`x` and `xᵢ` differ by a unit of `R'`, not of `R`). -/
theorem MonoidalTransform.exists_minimal_generators (t : MonoidalTransform R P)
    (hS : IsRegularLocalRing (R ⧸ P)) [P.IsPrime] :
    ∃ (S : Finset R) (r : ℕ) (z : Fin (r + 1) → R),
      Ideal.span (S : Set R) = maximalIdeal R ∧ S.card = (maximalIdeal R).spanFinrank ∧
      Function.Injective z ∧ (∀ i, z i ∈ S) ∧ z 0 = t.x ∧ Ideal.span (Set.range z) = P :=
  t.exists_minimal_generators_of_span_eq_map hS t.x_mem t.span_xR_eq_map

open MvPolynomial in
/-- `R[x⁻¹P] = R[z₁/x, …, z_r/x]` when `P = (x, z₁, …, z_r)`. -/
theorem exists_aeval_eq_of_mem_blowupAlgebra {x : R} (hx0 : x ≠ 0) {r : ℕ} {z : Fin (r + 1) → R}
    (hz0 : z 0 = x) (hzP : Ideal.span (Set.range z) = P) {y : FractionRing R}
    (hy : y ∈ blowupAlgebra R P x) :
    ∃ F : MvPolynomial (Fin r) R, aeval (fun i : Fin r => algebraMap R (FractionRing R) (z i.succ) /
      algebraMap R (FractionRing R) x) F = y := by
  have hxK : algebraMap R (FractionRing R) x ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective R (FractionRing R))).mpr hx0
  set g : Fin r → FractionRing R := fun i => algebraMap R (FractionRing R) (z i.succ) /
      algebraMap R (FractionRing R) x
  suffices h : blowupAlgebra R P x ≤ Algebra.adjoin R (Set.range g) by
    have := h hy
    rw [Algebra.adjoin_range_eq_range_aeval] at this
    exact this
  rw [blowupAlgebra, Algebra.adjoin_le_iff]
  rintro _ ⟨p, hp, rfl⟩
  rw [← hzP] at hp
  induction hp using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨j, rfl⟩ := hy
    refine Fin.cases ?_ (fun i => ?_) j
    · simp only [hz0, div_self hxK]
      exact one_mem _
    · exact Algebra.subset_adjoin ⟨i, rfl⟩
  | zero => simp
  | add y w _ _ hy hw =>
    dsimp only at hy hw ⊢
    rw [map_add, add_div]
    exact add_mem hy hw
  | smul c y _ hy =>
    dsimp only at hy ⊢
    rw [smul_eq_mul, map_mul, mul_div_assoc]
    exact Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ c) hy

open MvPolynomial in
/-- Scaling the variables of a homogeneous form of degree `j` by `c` multiplies it by `cʲ`. -/
theorem _root_.MvPolynomial.IsHomogeneous.aeval_mul_const {A K : Type*} [CommRing A] [CommRing K] [Algebra A K]
    {σ : Type*} {j : ℕ} {φ : MvPolynomial σ A} (hφ : φ.IsHomogeneous j) (y : σ → K) (c : K) :
    aeval (fun i => y i * c) φ = c ^ j * aeval y φ := by
  conv_lhs => rw [φ.as_sum]
  conv_rhs => rw [φ.as_sum]
  rw [map_sum, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  rw [aeval_monomial, aeval_monomial, Finsupp.prod, Finsupp.prod]
  simp only [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
  rw [← hφ.degree_eq_sum_deg_support hm]
  ring

open MvPolynomial in
/-- The key injectivity: if `P = (x, z₁, …, z_r)` with `x, z₁, …, z_r` part of a minimal system
of generators of `M`, and `H(z₁/x, …, z_r/x) = 0`, then all coefficients of `H` lie in `P`
(homogenize `H` and use the quasi-regularity of `x, z₁, …, z_r`). -/
private theorem coeff_mem_of_aeval_div_eq_zero {S : Finset R}
    (hS : Ideal.span (S : Set R) = maximalIdeal R) (hScard : S.card = (maximalIdeal R).spanFinrank)
    {r : ℕ} {z : Fin (r + 1) → R} (hinj : Function.Injective z) (hzS : ∀ i, z i ∈ S)
    (hz0 : z 0 ≠ 0) (hzP : Ideal.span (Set.range z) = P) {H : MvPolynomial (Fin r) R}
    (hH : aeval (fun i : Fin r => algebraMap R (FractionRing R) (z i.succ) /
      algebraMap R (FractionRing R) (z 0)) H = 0) (m : Fin r →₀ ℕ) : H.coeff m ∈ P := by
  classical
  set a := algebraMap R (FractionRing R)
  have hxK : a (z 0) ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective R (FractionRing R))).mpr hz0
  set d := H.totalDegree
  let F : MvPolynomial (Fin (r + 1)) R := ∑ j ∈ Finset.range (d + 1),
    X 0 ^ (d - j) * rename Fin.succ (homogeneousComponent j H)
  have hFhom : F.IsHomogeneous d := by
    refine IsHomogeneous.sum _ _ _ fun j hj => ?_
    have hjd : j ≤ d := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    have := (isHomogeneous_X_pow (R := R) (0 : Fin (r + 1)) (d - j)).mul
      ((homogeneousComponent_isHomogeneous j H).rename_isHomogeneous (f := Fin.succ))
    rwa [Nat.sub_add_cancel hjd] at this
  have hFeval : eval z F = 0 := by
    apply IsFractionRing.injective R (FractionRing R)
    rw [map_zero]
    have hsum := congrArg (fun y => a (z 0) ^ d * y) hH
    simp only [mul_zero] at hsum
    rw [← hsum]
    conv_rhs => rw [← sum_homogeneousComponent H]
    simp only [F, map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hjd : j ≤ d := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    have hg : (fun i : Fin r => a (z i.succ) / a (z 0)) = fun i => (a ∘ fun i => z i.succ) i *
        (a (z 0))⁻¹ := by
      funext i
      simp [div_eq_mul_inv]
    rw [hg, MvPolynomial.IsHomogeneous.aeval_mul_const (homogeneousComponent_isHomogeneous j H),
      MvPolynomial.aeval_algebraMap_apply]
    simp only [eval_X, eval_rename, map_mul, map_pow]
    rw [← mul_assoc, inv_pow, ← pow_sub₀ _ hxK hjd]
    rfl
  have hq := isQuasiRegular_of_minimal hS hScard hinj hzS d F hFhom
    (by rw [hFeval]; exact zero_mem _)
  by_cases hm : H.coeff m = 0
  · rw [hm]; exact zero_mem _
  have hmd : m.degree ≤ d := le_totalDegree (mem_support_iff.mpr hm)
  have hren : ∀ p : MvPolynomial (Fin r) R, finSuccEquiv R r (rename Fin.succ p) =
      Polynomial.C p := by
    intro p
    induction p using MvPolynomial.induction_on with
    | C c => simp [finSuccEquiv_apply]
    | add p q hp hq => simp [map_add, hp, hq]
    | mul_X p i hp => simp [map_mul, hp, finSuccEquiv_X_succ]
  have hcoeff : F.coeff (m.cons (d - m.degree)) = H.coeff m := by
    rw [← finSuccEquiv_coeff_coeff]
    simp only [F, map_sum, map_mul, map_pow, finSuccEquiv_X_zero, hren]
    rw [Polynomial.finsetSum_coeff, Finset.sum_eq_single m.degree]
    · rw [mul_comm, Polynomial.coeff_C_mul_X_pow, ite_eq_left rfl, coeff_homogeneousComponent,
        ite_eq_left rfl]
    · intro j hj hjm
      rw [mul_comm, Polynomial.coeff_C_mul_X_pow, ite_eq_right]
      have := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
      omega
    · intro h
      exact absurd (Finset.mem_range.mpr (Nat.lt_succ_of_le hmd)) h
  have := hq (m.cons (d - m.degree))
  rwa [hcoeff, hzP] at this

/-- `R[x⁻¹P]` is generated over `R` by the `pᵢ/x` for finitely many generators `pᵢ` of `P`. -/
theorem blowupAlgebra_fg (x : R) : (blowupAlgebra R P x).FG := by
  classical
  obtain ⟨s, hs⟩ := (IsNoetherian.noetherian P : P.FG)
  refine ⟨s.image (fun p => algebraMap R (FractionRing R) p /
    algebraMap R (FractionRing R) x), ?_⟩
  rw [blowupAlgebra, Finset.coe_image]
  apply le_antisymm
  · exact Algebra.adjoin_mono (Set.image_mono (by rw [← hs]; exact Submodule.subset_span))
  · rw [Algebra.adjoin_le_iff]
    rintro _ ⟨p, hp, rfl⟩
    rw [← hs] at hp
    induction hp using Submodule.span_induction with
    | mem y hy => exact Algebra.subset_adjoin ⟨y, hy, rfl⟩
    | zero => simp
    | add y z _ _ hy hz =>
      dsimp only at hy hz ⊢
      rw [map_add, add_div]
      exact add_mem hy hz
    | smul r y _ hy =>
      dsimp only at hy ⊢
      rw [smul_eq_mul, map_mul, mul_div_assoc]
      exact Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ r) hy

/-- `R[x⁻¹P]` is generated over `R` by the `pᵢ/x` for finitely many generators `pᵢ` of `P`. -/
theorem MonoidalTransform.fg_blowupAlgebra (t : MonoidalTransform R P) :
    (blowupAlgebra R P t.x).FG :=
  blowupAlgebra_fg t.x

/-- `R[x⁻¹P]` is noetherian (Hilbert's basis theorem). -/
theorem isNoetherianRing_blowupAlgebra (x : R) : IsNoetherianRing (blowupAlgebra R P x) :=
  isNoetherianRing_of_fg (blowupAlgebra_fg x)

/-- A monoidal transform is noetherian: `R[x⁻¹P]` is of finite type over `R`, hence noetherian
(Hilbert's basis theorem), and so is its localization `R'`. -/
theorem MonoidalTransform.isNoetherianRing (t : MonoidalTransform R P) :
    IsNoetherianRing t.ring :=
  IsLocalization.isNoetherianRing t.M'.primeCompl t.ring
    (isNoetherianRing_of_fg (MonoidalTransform.fg_blowupAlgebra t))

/-- p. 209: `PA' = (x₁)A'` for `A' = R[x⁻¹P]`: every `p ∈ P` is `x · (p/x)` with `p/x ∈ A'`. -/
theorem algebraMap_mem_span_blowupAlgebra {x : R} (hx0 : x ≠ 0) {p : R} (hp : p ∈ P) :
    algebraMap R (blowupAlgebra R P x) p ∈
      Ideal.span {algebraMap R (blowupAlgebra R P x) x} := by
  rw [Ideal.mem_span_singleton']
  have hx : algebraMap R (FractionRing R) x ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective R (FractionRing R))).mpr hx0
  refine ⟨⟨algebraMap R (FractionRing R) p / algebraMap R (FractionRing R) x,
    Algebra.subset_adjoin ⟨p, hp, rfl⟩⟩, ?_⟩
  apply Subtype.ext
  simp only [MulMemClass.coe_mul, Subalgebra.coe_algebraMap]
  field_simp

open MvPolynomial in
/-- pp. 209–210: "It is well known that: `PA' = (x₁)A'` and `A'/(x₁)A'` is canonically isomorphic to
a polynomial ring of `(r − 1)` variables `S[X₂, …, X_r]` over `S = R/P`, where the residue class of
`x_i/x₁` corresponds to `X_i`."  Here `P = (x, z₁, …, z_r)` with `x, z₁, …, z_r` part of a minimal
system of generators of `M`: the *chart* `χ : A' → (R/P)[T₁, …, T_r]`, `zᵢ/x ↦ Tᵢ`, is a surjective
ring homomorphism extending `R → R/P`, with kernel `(x)A'`.  (It is well defined because an
`R`-polynomial relation among the `zᵢ/x` has all its coefficients in `P`, by the quasi-regularity of
a minimal system of generators of `M`.) -/
@[blueprint "lem:III.2-chart"
  (statement := /-- Let $R$ be a regular local ring, $P$ a prime ideal of $R$ with $R/P$ regular,
    $(x_1,\dots,x_r)$ a minimal base of $P$ with $x_1=x$ which is part of a minimal base of the
    maximal ideal $M$, $S=R/P$ and $A'=R[x_2/x_1,\dots,x_r/x_1]$. Then $PA'=(x_1)A'$ and
    $A'/(x_1)A'$ is canonically isomorphic to the polynomial ring $S[X_2,\dots,X_r]$ over $S$,
    where the residue class of $x_i/x_1$ corresponds to $X_i$ ($2\le i\le r$). (p.~209.)
    (Formalization note (encoding): the isomorphism is a \emph{chart}
    $\chi\colon A'\to S[X_2,\dots,X_r]$, a surjective ring homomorphism with kernel $(x_1)A'$
    which extends $R\to S$ and sends $x_i/x_1$ to $X_i$.) -/)
  (proof := /-- The paper says only ``It is well known that''. \textbf{Gap in the paper filled.}
    The map $R[T_2,\dots,T_r]\to A'$, $T_i\mapsto x_i/x_1$, is surjective, and the induced map to
    $S[T_2,\dots,T_r]$ is well defined: if $H(x_2/x_1,\dots,x_r/x_1)=0$ then, homogenizing and
    using that a minimal system of generators of $M$ is quasi-regular, all coefficients of $H$
    lie in $P$. Its kernel is $(x_1)A'$, since $PA'=(x_1)A'$ ($p=x_1\cdot(p/x_1)$). -/)
  (latexEnv := "lemma")]
theorem exists_chart_of_mem {x : R} (hx : x ∈ P) (hx0 : x ≠ 0) [P.IsPrime]
    {S : Finset R} {r : ℕ} {z : Fin (r + 1) → R}
    (hSM : Ideal.span (S : Set R) = maximalIdeal R)
    (hScard : S.card = (maximalIdeal R).spanFinrank) (hinj : Function.Injective z)
    (hzS : ∀ i, z i ∈ S) (hz0 : z 0 = x) (hzP : Ideal.span (Set.range z) = P) :
    ∃ χ : blowupAlgebra R P x →+* MvPolynomial (Fin r) (R ⧸ P),
      Function.Surjective χ ∧
      RingHom.ker χ = Ideal.span {algebraMap R (blowupAlgebra R P x) x} ∧
      (∀ c : R, χ (algebraMap R (blowupAlgebra R P x) c) = C (Ideal.Quotient.mk P c)) ∧
      ∀ (i : Fin r) (a : blowupAlgebra R P x),
        (a : FractionRing R) = algebraMap R (FractionRing R) (z i.succ) /
          algebraMap R (FractionRing R) x → χ a = X i := by
  classical
  set A := blowupAlgebra R P x
  set g : Fin r → FractionRing R := fun i => algebraMap R (FractionRing R) (z i.succ) /
    algebraMap R (FractionRing R) x
  have hgA : ∀ i, g i ∈ A := fun i =>
    Algebra.subset_adjoin ⟨z i.succ, hzP ▸ Ideal.subset_span ⟨i.succ, rfl⟩, rfl⟩
  -- `Φ : R[T₁, …, T_r] → A = R[x⁻¹P]`, `Tᵢ ↦ zᵢ/x`, is surjective
  let Φ : MvPolynomial (Fin r) R →ₐ[R] A := aeval fun i => (⟨g i, hgA i⟩ : A)
  have hΦK : ∀ F, (Φ F : FractionRing R) = aeval g F := by
    intro F
    have := congrArg (fun φ : MvPolynomial (Fin r) R →ₐ[R] FractionRing R => φ F)
      (MvPolynomial.comp_aeval (R := R) (fun i => (⟨g i, hgA i⟩ : A)) A.val)
    simpa using this
  have hΦsurj : Function.Surjective Φ := by
    intro y
    obtain ⟨F, hF⟩ := exists_aeval_eq_of_mem_blowupAlgebra hx0 hz0 hzP y.2
    exact ⟨F, Subtype.ext ((hΦK F).trans hF)⟩
  -- `A/xA ≅ (R/P)[T]`, through `χ : A → (R/P)[T]`
  let π : MvPolynomial (Fin r) R →+* MvPolynomial (Fin r) (R ⧸ P) := map (Ideal.Quotient.mk P)
  have hπ : ∀ F, π F = 0 ↔ ∀ m, F.coeff m ∈ P := by
    intro F
    simp [π, MvPolynomial.ext_iff, MvPolynomial.coeff_map, Ideal.Quotient.eq_zero_iff_mem]
  have hker : RingHom.ker Φ.toRingHom ≤ RingHom.ker π := by
    intro F hF
    rw [RingHom.mem_ker] at hF ⊢
    refine (hπ F).mpr fun m => coeff_mem_of_aeval_div_eq_zero hSM hScard hinj hzS
      (hz0 ▸ hx0) hzP ?_ m
    rw [hz0, ← hΦK]
    exact congrArg Subtype.val hF
  let χ : A →+* MvPolynomial (Fin r) (R ⧸ P) :=
    RingHom.liftOfSurjective Φ.toRingHom hΦsurj ⟨π, hker⟩
  have hχΦ : ∀ F, χ (Φ F) = π F := fun F =>
    RingHom.liftOfSurjective_comp_apply Φ.toRingHom hΦsurj ⟨π, hker⟩ F
  have hχC : ∀ c : R, χ (algebraMap R A c) = C (Ideal.Quotient.mk P c) := by
    intro c
    rw [← Φ.commutes, MvPolynomial.algebraMap_eq, hχΦ]
    simp [π]
  refine ⟨χ, ?_, ?_, hχC, ?_⟩
  · intro y
    obtain ⟨F, rfl⟩ := MvPolynomial.map_surjective _ Ideal.Quotient.mk_surjective y
    exact ⟨Φ F, hχΦ F⟩
  · -- `ker χ = (x)A`
    apply le_antisymm
    · intro a ha
      obtain ⟨F, rfl⟩ := hΦsurj a
      rw [RingHom.mem_ker, hχΦ, hπ] at ha
      rw [F.as_sum, map_sum]
      refine sum_mem fun m _ => ?_
      rw [← mul_one (F.coeff m), ← C_mul_monomial, map_mul, ← MvPolynomial.algebraMap_eq,
        Φ.commutes]
      exact Ideal.mul_mem_right _ _ (algebraMap_mem_span_blowupAlgebra hx0 (ha m))
    · rw [Ideal.span_le, Set.singleton_subset_iff]
      show algebraMap R A x ∈ RingHom.ker χ
      rw [RingHom.mem_ker, hχC, map_eq_zero_iff _ (C_injective _ _)]
      exact Ideal.Quotient.eq_zero_iff_mem.mpr hx
  · intro i a ha
    have : a = ⟨g i, hgA i⟩ := Subtype.ext ha
    rw [this]
    have := hχΦ (X i)
    simpa [Φ, π] using this

open MvPolynomial in
/-- `exists_chart_of_mem` for the element `x` of a monoidal transform. -/
theorem MonoidalTransform.exists_chart (t : MonoidalTransform R P) [P.IsPrime]
    {S : Finset R} {r : ℕ} {z : Fin (r + 1) → R}
    (hSM : Ideal.span (S : Set R) = maximalIdeal R)
    (hScard : S.card = (maximalIdeal R).spanFinrank) (hinj : Function.Injective z)
    (hzS : ∀ i, z i ∈ S) (hz0 : z 0 = t.x) (hzP : Ideal.span (Set.range z) = P) :
    ∃ χ : blowupAlgebra R P t.x →+* MvPolynomial (Fin r) (R ⧸ P),
      Function.Surjective χ ∧
      RingHom.ker χ = Ideal.span {algebraMap R (blowupAlgebra R P t.x) t.x} ∧
      (∀ c : R, χ (algebraMap R (blowupAlgebra R P t.x) c) = C (Ideal.Quotient.mk P c)) ∧
      ∀ (i : Fin r) (a : blowupAlgebra R P t.x),
        (a : FractionRing R) = algebraMap R (FractionRing R) (z i.succ) /
          algebraMap R (FractionRing R) t.x → χ a = X i :=
  exists_chart_of_mem t.x_mem t.x_ne_zero hSM hScard hinj hzS hz0 hzP

open MvPolynomial in
/-- pp. 209–210: the local structure of `R' = A'_{M'}` along a chart `χ : A'/(x)A' ≅ S[T₁, …, T_r]`,
`S = R/P`: the prime `q = M'/(x)A'` of `S[T]` lies over the maximal ideal of `S`, and `R'/xR'` is the
localization `S[T]_q` (`M̄' = M'/(x₁)A'` and `R'/(x₁)R' = S[X₂, …, X_r]_{M̄'}`, p. 210). -/
theorem MonoidalTransform.exists_quotient_equiv_localization_of_chart (t : MonoidalTransform R P)
    [P.IsPrime] (hS : IsRegularLocalRing (R ⧸ P)) {r : ℕ} (χ : blowupAlgebra R P t.x →+* MvPolynomial (Fin r) (R ⧸ P))
    (hχ : Function.Surjective χ)
    (hχx : RingHom.ker χ = Ideal.span {algebraMap R (blowupAlgebra R P t.x) t.x})
    (hχC : ∀ c : R, χ (algebraMap R (blowupAlgebra R P t.x) c) = C (Ideal.Quotient.mk P c)) :
    ∃ (q : Ideal (MvPolynomial (Fin r) (R ⧸ P))) (_ : q.IsPrime)
      (e : Localization.AtPrime q ≃+* t.ring ⧸ Ideal.span {t.xR}),
      q = t.M'.map χ ∧ (∀ a, χ a ∈ q ↔ a ∈ t.M') ∧
      q.comap C = maximalIdeal (R ⧸ P) ∧ (q.IsMaximal ↔ t.M'.IsMaximal) ∧
      ∀ a, e (algebraMap (MvPolynomial (Fin r) (R ⧸ P)) (Localization.AtPrime q) (χ a)) =
        Ideal.Quotient.mk _ (algebraMap (blowupAlgebra R P t.x) t.ring a) := by
  classical
  have hxM : t.x ∈ maximalIdeal R :=
    IsLocalRing.le_maximalIdeal (Ideal.IsPrime.ne_top ‹_›) t.x_mem
  -- `M' ∩ R = M`
  have hAM : ∀ c : R, algebraMap R (blowupAlgebra R P t.x) c ∈ t.M' ↔ c ∈ maximalIdeal R := by
    intro c
    refine ⟨fun h => ?_, fun h => t.le (Ideal.mem_map_of_mem _ h)⟩
    by_contra hc
    have hu : IsUnit (algebraMap R (blowupAlgebra R P t.x) c) :=
      ((IsLocalRing.mem_maximalIdeal _).not.mp hc |> not_not.mp).map _
    exact t.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ h hu)
  -- `ker χ ⊆ M'`
  have hkerM : RingHom.ker χ ≤ t.M' := by
    rw [hχx, Ideal.span_le, Set.singleton_subset_iff]
    exact (hAM _).mpr hxM
  have hq : (t.M'.map χ).IsPrime := Ideal.map_isPrime_of_surjective hχ hkerM
  set q := t.M'.map χ with hqdef
  have hcomap : ∀ a, χ a ∈ q ↔ a ∈ t.M' := by
    intro a
    rw [← Ideal.mem_comap, hqdef, Ideal.comap_map_of_surjective _ hχ,
      ← RingHom.ker_eq_comap_bot,
      sup_eq_left.mpr hkerM]
  have hmapM : t.M'.primeCompl.map χ = q.primeCompl := by
    ext y
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact fun h => ha ((hcomap a).mp h)
    · intro hy
      obtain ⟨a, rfl⟩ := hχ y
      exact ⟨a, fun h => hy ((hcomap a).mpr h), rfl⟩
  -- `R'/xR'` is the localization of `(R/P)[T]` at `q`
  let Q := t.ring ⧸ Ideal.span {t.xR}
  have hker : RingHom.ker χ ≤
      RingHom.ker ((Ideal.Quotient.mk (Ideal.span {t.xR})).comp (algebraMap (blowupAlgebra R P t.x) t.ring)) := by
    rw [hχx, Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, RingHom.mem_ker,
      RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.subset_span rfl
  let θ : MvPolynomial (Fin r) (R ⧸ P) →+* Q :=
    RingHom.liftOfSurjective χ hχ ⟨(Ideal.Quotient.mk (Ideal.span {t.xR})).comp
      (algebraMap (blowupAlgebra R P t.x) t.ring), hker⟩
  have hθ : ∀ a, θ (χ a) = Ideal.Quotient.mk _ (algebraMap (blowupAlgebra R P t.x) t.ring a) := fun a =>
    RingHom.liftOfSurjective_comp_apply χ hχ
      ⟨(Ideal.Quotient.mk (Ideal.span {t.xR})).comp (algebraMap (blowupAlgebra R P t.x) t.ring), hker⟩ a
  let _ : Algebra (MvPolynomial (Fin r) (R ⧸ P)) Q := θ.toAlgebra
  have H : (Ideal.Quotient.mk (Ideal.span {t.xR})).comp (algebraMap (blowupAlgebra R P t.x) t.ring) =
      (algebraMap (MvPolynomial (Fin r) (R ⧸ P)) Q).comp χ :=
    RingHom.ext fun a => (hθ a).symm
  have H' : RingHom.ker (Ideal.Quotient.mk (Ideal.span {t.xR})) ≤
      (RingHom.ker χ).map (algebraMap (blowupAlgebra R P t.x) t.ring) := by
    rw [Ideal.mk_ker, Ideal.span_le, Set.singleton_subset_iff]
    exact Ideal.mem_map_of_mem _ (hχx ▸ Ideal.subset_span rfl)
  have hloc := IsLocalization.of_surjective t.M'.primeCompl t.ring χ hχ
    (Ideal.Quotient.mk (Ideal.span {t.xR})) Ideal.Quotient.mk_surjective H H'
  rw [hmapM] at hloc
  -- `q` lies over the maximal ideal of `R/P`
  have hlocP : IsLocalHom (Ideal.Quotient.mk P) :=
    IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective
  have hqC : q.comap C = maximalIdeal (R ⧸ P) := by
    ext c
    obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective c
    rw [Ideal.mem_comap, ← hχC, hcomap, hAM]
    constructor
    · exact map_nonunit _ c
    · intro h
      by_contra hc
      exact (IsLocalRing.mem_maximalIdeal _).mp h
        (((IsLocalRing.mem_maximalIdeal _).not.mp hc |> not_not.mp).map _)
  let e := IsLocalization.algEquiv q.primeCompl (Localization.AtPrime q) Q
  have he : ∀ F, e.toRingEquiv (algebraMap _ (Localization.AtPrime q) F) = θ F := fun F =>
    e.commutes F
  have hmax : q.IsMaximal ↔ t.M'.IsMaximal := by
    constructor
    · intro h
      have := Ideal.comap_isMaximal_of_surjective χ hχ (K := q)
      rwa [hqdef, Ideal.comap_map_of_surjective _ hχ, ← RingHom.ker_eq_comap_bot,
        sup_eq_left.mpr hkerM] at this
    · intro h
      exact Ideal.IsMaximal.map_of_surjective_of_ker_le hχ hkerM
  exact ⟨q, hq, e.toRingEquiv, hqdef, hcomap, hqC, hmax, fun a => by rw [he, hθ]⟩

open MvPolynomial in
/-- The local structure of `R' = R[x⁻¹P]_{M'}` (pp. 209–210): if `P = (x, z₁, …, z_r)` with
`x, z₁, …, z_r` part of a minimal system of generators of `M`, then `R'/xR'` is the localization
of `(R/P)[T₁, …, T_r]` at a prime `q` lying over the maximal ideal of `R/P`, the class of `Tᵢ`
corresponding to that of `zᵢ/x`.  (Obtained from the chart
`exists_chart : A'/(x)A' ≅ (R/P)[T]` and `exists_quotient_equiv_localization_of_chart`.) -/
theorem MonoidalTransform.exists_quotient_equiv_localization (t : MonoidalTransform R P) [P.IsPrime]
    (hS : IsRegularLocalRing (R ⧸ P)) {S : Finset R} {r : ℕ} {z : Fin (r + 1) → R}
    (hSM : Ideal.span (S : Set R) = maximalIdeal R)
    (hScard : S.card = (maximalIdeal R).spanFinrank) (hinj : Function.Injective z)
    (hzS : ∀ i, z i ∈ S) (hz0 : z 0 = t.x) (hzP : Ideal.span (Set.range z) = P) :
    ∃ (q : Ideal (MvPolynomial (Fin r) (R ⧸ P))) (_ : q.IsPrime)
      (e : Localization.AtPrime q ≃+* t.ring ⧸ Ideal.span {t.xR}),
      q.comap C = maximalIdeal (R ⧸ P) ∧ (q.IsMaximal ↔ t.M'.IsMaximal) ∧
      (∀ c : R, e (algebraMap (MvPolynomial (Fin r) (R ⧸ P)) (Localization.AtPrime q)
        (C (Ideal.Quotient.mk P c))) = Ideal.Quotient.mk _ (t.toRing c)) ∧
      ∀ (u : Fin r → t.ring), (∀ i, t.toRing t.x * u i = t.toRing (z i.succ)) →
        ∀ i, ((X i : MvPolynomial (Fin r) (R ⧸ P)) ∈ q ↔ u i ∈ maximalIdeal t.ring) ∧
          e (algebraMap (MvPolynomial (Fin r) (R ⧸ P)) (Localization.AtPrime q) (X i)) =
            Ideal.Quotient.mk _ (u i) := by
  classical
  have _ := hS
  obtain ⟨χ, hχ, hχx, hχC, hχX⟩ := t.exists_chart hSM hScard hinj hzS hz0 hzP
  obtain ⟨q, hq, e, -, hcomap, hqC, hmax, he⟩ :=
    t.exists_quotient_equiv_localization_of_chart hS χ hχ hχx hχC
  refine ⟨q, hq, e, hqC, hmax, fun c => ?_, fun u hu i => ?_⟩
  · rw [← hχC, he]
    rfl
  · set g : Fin r → FractionRing R := fun i => algebraMap R (FractionRing R) (z i.succ) /
      algebraMap R (FractionRing R) t.x
    have hgA : g i ∈ blowupAlgebra R P t.x :=
      Algebra.subset_adjoin ⟨z i.succ, hzP ▸ Ideal.subset_span ⟨i.succ, rfl⟩, rfl⟩
    have hx0 : t.toRing t.x ≠ 0 := fun h =>
      t.x_ne_zero (MonoidalTransform.toRing_injective t (h.trans (map_zero _).symm))
    have hui : u i = algebraMap (blowupAlgebra R P t.x) t.ring ⟨g i, hgA⟩ := by
      refine mul_left_cancel₀ hx0 ?_
      rw [hu i, MonoidalTransform.toRing, RingHom.comp_apply, RingHom.comp_apply, ← map_mul]
      congr 1
      apply Subtype.ext
      simp only [MulMemClass.coe_mul, Subalgebra.coe_algebraMap, g]
      have hxK : algebraMap R (FractionRing R) t.x ≠ 0 :=
        (map_ne_zero_iff _ (IsFractionRing.injective R (FractionRing R))).mpr t.x_ne_zero
      field_simp
    have hXi : χ ⟨g i, hgA⟩ = X i := hχX i _ rfl
    rw [hui]
    refine ⟨?_, ?_⟩
    · rw [← hXi, hcomap]
      exact (IsLocalization.AtPrime.to_map_mem_maximal_iff t.ring t.M' _).symm
    · rw [← hXi, he]

/-- `p/x ∈ R'` for `p ∈ P`, since `PR' = (x)R'`. -/
private theorem MonoidalTransform.exists_toRing_x_mul_eq_of_mem (t : MonoidalTransform R P) {p : R} (hp : p ∈ P) :
    ∃ u : t.ring, t.toRing t.x * u = t.toRing p := by
  have := t.span_xR_eq_map ▸ Ideal.mem_map_of_mem t.toRing hp
  obtain ⟨u, hu⟩ := Ideal.mem_span_singleton'.mp this
  exact ⟨u, by rw [mul_comm]; exact hu⟩

/-- `R[x₁/x, …, x_r/x]`: the subalgebra of the field of quotients of `R` generated by the
quotients `zⱼ/x`. -/
noncomputable def adjoinDiv {r : ℕ} (z : Fin r → R) (x : R) : Subalgebra R (FractionRing R) :=
  Algebra.adjoin R (Set.range fun j =>
    algebraMap R (FractionRing R) (z j) / algebraMap R (FractionRing R) x)

/-- If `P = (z₁, …, z_r)`, then `R[x⁻¹P] = R[z₁/x, …, z_r/x]`: the two descriptions of the ring of
p. 209 ("a ring of the form `R[x⁻¹P]`" and "`R[x₁/xᵢ, …, x_r/xᵢ]`" for a base `(x₁, …, x_r)`
of `P`). -/
theorem blowupAlgebra_eq_adjoinDiv {r : ℕ} {z : Fin r → R} (hz : Ideal.span (Set.range z) = P)
    (x : R) : blowupAlgebra R P x = adjoinDiv z x := by
  apply le_antisymm
  · rw [blowupAlgebra, Algebra.adjoin_le_iff]
    rintro _ ⟨p, hp, rfl⟩
    rw [← hz] at hp
    induction hp using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨j, rfl⟩ := hy
      exact Algebra.subset_adjoin ⟨j, rfl⟩
    | zero => simp
    | add y w _ _ hy hw =>
      dsimp only at hy hw ⊢
      rw [map_add, add_div]
      exact add_mem hy hw
    | smul c y _ hy =>
      dsimp only at hy ⊢
      rw [smul_eq_mul, map_mul, mul_div_assoc]
      exact Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ c) hy
  · rw [adjoinDiv, Algebra.adjoin_le_iff]
    rintro _ ⟨j, rfl⟩
    exact Algebra.subset_adjoin ⟨z j, hz ▸ Ideal.subset_span ⟨j, rfl⟩, rfl⟩

/-- The key step of the claim of p. 209, "there exist an index `i` (1 ≤ i ≤ r) …": if
`P = (z₁, …, z_r)` and `R' = R[x⁻¹P]_{M'}` is a monoidal transform with center `P`, then some
`zᵢ/x` is a unit of `R'`.  Indeed `x ∈ P` gives `x = Σ cⱼ zⱼ` with `cⱼ ∈ R`; in the domain `R'`
one has `zⱼ = x uⱼ` (`PR' = (x)R'`), so `1 = Σ cⱼ uⱼ`, and as `R'` is local one of the summands
`cᵢ uᵢ`, hence `uᵢ = zᵢ/x`, is a unit.  (The paper does not argue this.) -/
theorem MonoidalTransform.exists_index_isUnit_toRing_mul (t : MonoidalTransform R P) {r : ℕ}
    {z : Fin r → R} (hz : Ideal.span (Set.range z) = P) :
    ∃ (i : Fin r) (u : t.ring), IsUnit u ∧ t.toRing t.x * u = t.toRing (z i) := by
  classical
  have hX0 : t.toRing t.x ≠ 0 := fun h =>
    t.x_ne_zero (t.toRing_injective (h.trans (map_zero _).symm))
  have hdiv : ∀ j, ∃ u : t.ring, t.toRing t.x * u = t.toRing (z j) := fun j =>
    MonoidalTransform.exists_toRing_x_mul_eq_of_mem t (hz ▸ Ideal.subset_span ⟨j, rfl⟩)
  choose u hu using hdiv
  have hxspan : t.x ∈ Ideal.span (Set.range z) := hz ▸ t.x_mem
  obtain ⟨c, hc⟩ := Ideal.mem_span_range_iff_exists_fun.mp hxspan
  have hsum : ∑ j, t.toRing (c j) * u j = 1 := by
    refine mul_left_cancel₀ hX0 ?_
    rw [mul_one, Finset.mul_sum]
    conv_rhs => rw [← hc]
    rw [map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_mul, ← hu j]
    ring
  by_contra hcon
  push Not at hcon
  have hmem : ∀ j, t.toRing (c j) * u j ∈ maximalIdeal t.ring := fun j => by
    rw [mem_maximalIdeal, mem_nonunits_iff]
    intro h
    exact hcon j (u j) (isUnit_of_mul_isUnit_right h) (hu j)
  have h1 : (1 : t.ring) ∈ maximalIdeal t.ring := hsum ▸ sum_mem fun j _ => hmem j
  exact (maximalIdeal.isMaximal _).ne_top ((Ideal.eq_top_iff_one _).mpr h1)

/-- The rest of the claim of p. 209: if `x₀ ∈ P` and `x₀/x` is a unit of `R'` (that is, `x₀`
generates `PR'` too), then `R' = R[x₀⁻¹P]_{M''}` for the prime ideal `M'' = M_{R'} ∩ R[x₀⁻¹P]`
of `R[x₀⁻¹P]`, which contains `M R[x₀⁻¹P]`: the monoidal transform `T₂` with data `(x₀, M'')`
has the same subring of `Frac R` as `t`.  Proof: `R[x₀⁻¹P] ⊆ R'` since `p/x₀ = (p/x)(x₀/x)⁻¹`;
every element of `R[x⁻¹P]` is a quotient by a power of the unit `x/x₀ ∈ R[x₀⁻¹P]`, so each element
of `R'` is a fraction `a/s` with `a, s ∈ R[x₀⁻¹P]`, `s ∉ M''`; conversely such a fraction lies in
`R'` because `s ∉ M_{R'}` is a unit there. -/
theorem MonoidalTransform.exists_subring_eq_of_isUnit (t : MonoidalTransform R P) {x₀ : R}
    (hx₀ : x₀ ∈ P) {u : t.ring} (hu : IsUnit u) (hxu : t.toRing t.x * u = t.toRing x₀) :
    ∃ (h0 : x₀ ≠ 0) (M'' : Ideal (blowupAlgebra R P x₀)) (hM : M''.IsPrime)
      (hle : (maximalIdeal R).map (algebraMap R (blowupAlgebra R P x₀)) ≤ M''),
      (⟨x₀, hx₀, h0, M'', hM, hle⟩ : MonoidalTransform R P).subring = t.subring := by
  classical
  set K := FractionRing R
  have hFi := t.injective_toFractionRing
  have hFr := t.toFractionRing_toRing
  have hX0 : t.toRing t.x ≠ 0 := fun h =>
    t.x_ne_zero (t.toRing_injective (h.trans (map_zero _).symm))
  have hx₀0 : x₀ ≠ 0 := by
    rintro rfl
    rw [map_zero] at hxu
    exact hu.ne_zero ((mul_eq_zero.mp hxu).resolve_left hX0)
  have hxK : algebraMap R K t.x ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective R K)).mpr t.x_ne_zero
  have hx₀K : algebraMap R K x₀ ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective R K)).mpr hx₀0
  have hFu : algebraMap R K t.x * t.toFractionRing u = algebraMap R K x₀ := by
    have := congrArg t.toFractionRing hxu
    rwa [map_mul, hFr, hFr] at this
  have hFu0 : t.toFractionRing u ≠ 0 := fun h => hu.ne_zero (hFi (h.trans (map_zero _).symm))
  have hFinv : t.toFractionRing u * t.toFractionRing (↑hu.unit⁻¹ : t.ring) = 1 := by
    have h1 : u * (↑hu.unit⁻¹ : t.ring) = 1 := by
      have := hu.unit.mul_inv
      rwa [IsUnit.unit_spec] at this
    rw [← map_mul, h1, map_one]
  have e3 : t.toFractionRing (↑hu.unit⁻¹ : t.ring) = (t.toFractionRing u)⁻¹ :=
    eq_inv_of_mul_eq_one_right hFinv
  -- `R[x₀⁻¹P] ⊆ R'`
  have hrange : ∀ a ∈ blowupAlgebra R P x₀, a ∈ t.toFractionRing.range := by
    intro a ha
    induction ha using Algebra.adjoin_induction with
    | mem y hy =>
      obtain ⟨p, hp, rfl⟩ := hy
      obtain ⟨w, hw⟩ := MonoidalTransform.exists_toRing_x_mul_eq_of_mem t hp
      refine ⟨w * ↑hu.unit⁻¹, ?_⟩
      have e1 : algebraMap R K p = algebraMap R K t.x * t.toFractionRing w := by
        rw [← hFr, ← hw, map_mul, hFr]
      show t.toFractionRing (w * ↑hu.unit⁻¹) = algebraMap R K p / algebraMap R K x₀
      rw [map_mul, e3, e1, ← hFu]
      field_simp
    | algebraMap r => exact ⟨t.toRing r, hFr r⟩
    | add y z _ _ hy hz => exact add_mem hy hz
    | mul y z _ _ hy hz => exact mul_mem hy hz
  set φ := t.liftBlowupAlgebra hrange with hφdef
  have hφ : ∀ b, t.toFractionRing (φ b) = (b : K) := t.toFractionRing_liftBlowupAlgebra hrange
  have hφM : ∀ b, φ b ∈ maximalIdeal t.ring ↔ b ∈ (maximalIdeal t.ring).comap φ :=
    fun b => (Ideal.mem_comap).symm
  -- the prime `M''`
  have hM : ((maximalIdeal t.ring).comap φ).IsPrime := Ideal.comap_isPrime φ _
  have hle : (maximalIdeal R).map (algebraMap R (blowupAlgebra R P x₀)) ≤
      (maximalIdeal t.ring).comap φ := by
    rw [Ideal.map_le_iff_le_comap]
    intro c hc
    have hc' : φ (algebraMap R (blowupAlgebra R P x₀) c) = t.toRing c :=
      hFi (by rw [hφ, hFr]; rfl)
    rw [Ideal.mem_comap, Ideal.mem_comap, hc']
    exact (mem_maximalIdeal _).mpr (map_nonunit t.toRing c ((mem_maximalIdeal _).mp hc))
  refine ⟨hx₀0, _, hM, hle, ?_⟩
  set T₂ : MonoidalTransform R P := ⟨x₀, hx₀, hx₀0, _, hM, hle⟩ with hT₂
  -- `W = x/x₀ ∈ R[x₀⁻¹P]`, a unit of `R'`
  obtain ⟨W, hWdef⟩ : ∃ W : K, W = algebraMap R K t.x / algebraMap R K x₀ := ⟨_, rfl⟩
  have hW : W ∈ blowupAlgebra R P x₀ := hWdef ▸ Algebra.subset_adjoin ⟨t.x, t.x_mem, rfl⟩
  have hφW : φ ⟨W, hW⟩ * u = 1 := by
    apply hFi
    rw [map_mul, hφ, map_one]
    show W * t.toFractionRing u = 1
    rw [hWdef, div_mul_eq_mul_div, div_eq_one_iff_eq hx₀K]
    exact hFu
  have hWu : IsUnit (φ ⟨W, hW⟩) := IsUnit.of_mul_eq_one u hφW
  -- an element of `R[x⁻¹P]` times a power of `W` lies in `R[x₀⁻¹P]`
  have hgen : ∀ k ∈ blowupAlgebra R P t.x, ∃ n : ℕ, k * W ^ n ∈ blowupAlgebra R P x₀ := by
    intro k hk
    induction hk using Algebra.adjoin_induction with
    | mem y hy =>
      obtain ⟨p, hp, rfl⟩ := hy
      refine ⟨1, ?_⟩
      have : algebraMap R K p / algebraMap R K t.x * W ^ 1 = algebraMap R K p / algebraMap R K x₀ := by
        rw [hWdef, pow_one, div_mul_div_comm, mul_comm (algebraMap R K p) (algebraMap R K t.x),
          mul_div_mul_left _ _ hxK]
      rw [this]
      exact Algebra.subset_adjoin ⟨p, hp, rfl⟩
    | algebraMap r =>
      exact ⟨0, by simp⟩
    | add y z _ _ hy hz =>
      obtain ⟨n₁, h₁⟩ := hy
      obtain ⟨n₂, h₂⟩ := hz
      refine ⟨n₁ + n₂, ?_⟩
      have : (y + z) * W ^ (n₁ + n₂) = (y * W ^ n₁) * W ^ n₂ + (z * W ^ n₂) * W ^ n₁ := by ring
      rw [this]
      exact add_mem (mul_mem h₁ (pow_mem hW _)) (mul_mem h₂ (pow_mem hW _))
    | mul y z _ _ hy hz =>
      obtain ⟨n₁, h₁⟩ := hy
      obtain ⟨n₂, h₂⟩ := hz
      refine ⟨n₁ + n₂, ?_⟩
      have : y * z * W ^ (n₁ + n₂) = (y * W ^ n₁) * (z * W ^ n₂) := by ring
      rw [this]
      exact mul_mem h₁ h₂
  ext y
  constructor
  · intro hy
    obtain ⟨a, s, hs, hys⟩ := (T₂.mem_subring_iff y).mp hy
    have hsu : IsUnit (φ s) := by
      by_contra h
      exact hs ((mem_maximalIdeal _).mpr (mem_nonunits_iff.mpr h))
    have hs0 : (s : K) ≠ 0 := by
      rw [← hφ s]
      exact fun h => hsu.ne_zero (hFi (h.trans (map_zero _).symm))
    refine ⟨φ a * ↑hsu.unit⁻¹, ?_⟩
    have h1 : t.toFractionRing (↑hsu.unit⁻¹ : t.ring) * (s : K) = 1 := by
      have := congrArg t.toFractionRing hsu.unit.inv_mul
      rw [map_mul, IsUnit.unit_spec, hφ, map_one] at this
      simpa using this
    show t.toFractionRing (φ a * ↑hsu.unit⁻¹) = y
    rw [map_mul, hφ]
    calc (a : K) * t.toFractionRing ↑hsu.unit⁻¹
        = y * (s : K) * t.toFractionRing ↑hsu.unit⁻¹ := by rw [hys]
      _ = y * (t.toFractionRing ↑hsu.unit⁻¹ * (s : K)) := by ring
      _ = y := by rw [h1, mul_one]
  · intro hy
    obtain ⟨a, s, hs, hys⟩ := (t.mem_subring_iff y).mp hy
    obtain ⟨n, hn⟩ := hgen a a.2
    obtain ⟨m, hm⟩ := hgen s s.2
    have hsB : (s : K) * W ^ (m + n) ∈ blowupAlgebra R P x₀ := by
      rw [pow_add, ← mul_assoc]
      exact mul_mem hm (pow_mem hW n)
    have haB : (a : K) * W ^ (m + n) ∈ blowupAlgebra R P x₀ := by
      rw [add_comm, pow_add, ← mul_assoc]
      exact mul_mem hn (pow_mem hW m)
    have hsunit : IsUnit (φ ⟨_, hsB⟩) := by
      have h1 : φ ⟨_, hsB⟩ = algebraMap (blowupAlgebra R P t.x) t.ring s * φ ⟨W, hW⟩ ^ (m + n) := by
        apply hFi
        rw [map_mul, map_pow, hφ, hφ, t.toFractionRing_algebraMap_blowupAlgebra]
      rw [h1]
      exact (IsLocalization.map_units t.ring (⟨s, hs⟩ : t.M'.primeCompl)).mul (hWu.pow _)
    refine (T₂.mem_subring_iff y).mpr ⟨⟨_, haB⟩, ⟨_, hsB⟩, ?_, ?_⟩
    · intro h
      exact (mem_maximalIdeal _).mp h hsunit
    · show y * ((s : K) * W ^ (m + n)) = (a : K) * W ^ (m + n)
      rw [← mul_assoc, hys]

/-- p. 209: "If `(x₁, …, x_r)` is a minimal base of the prime ideal `P` and if `R'` is a monoidal
transform of `R` with center `P`, then there exist an index `i` (1 ≤ i ≤ r) and a prime ideal `M'`
in `R[x₁/xᵢ, …, x_r/xᵢ]` such that `R' = R[x₁/xᵢ, …, x_r/xᵢ]_{M'}` and
`M' ⊇ MR'[x₁/xᵢ, …, x_r/xᵢ]` where `M` = the maximal ideal of `R`."  (The printed text has `MR'[…]`
with a prime on `R`; the meaning is `MR[x₁/xᵢ, …, x_r/xᵢ]`: `MR'` is not contained in
`R[x₁/xᵢ, …]`.)

Formalization notes (encoding): `R'` is the subring `t.subring` of `Frac R` and `R[…]_{M'}` is the
set of fractions `a/s` with `a, s ∈ R[x₁/xᵢ, …, x_r/xᵢ]`, `s ∉ M'` (`xᵢ ≠ 0` is part of the
conclusion).  The base need only generate `P`; its minimality is not used. -/
@[blueprint "lem:III.2-monoidal-transform-index"
  (statement := /-- Let $R$ be a regular local ring with maximal ideal $M$, $P$ a prime ideal of
    $R$ with $R/P$ regular, $(x_1,\dots,x_r)$ a minimal base of $P$ and $R'$ a monoidal
    transform of $R$ with center $P$ (\cref{def:III.2-monoidal-transform}). Then there exist an
    index $i$ ($1\le i\le r$) and a prime ideal $M'$ in $R[x_1/x_i,\dots,x_r/x_i]$ such that
    $R'=R[x_1/x_i,\dots,x_r/x_i]_{M'}$ and $M'\supseteq MR[x_1/x_i,\dots,x_r/x_i]$. (p.~209.)
    Formalization notes (encoding): $R'$ is the subring of the field of quotients of $R$
    given by the monoidal transform, $R[\dots]_{M'}$ the set of fractions $a/s$ with
    $a,s\in R[x_1/x_i,\dots,x_r/x_i]$, $s\notin M'$, and $x_i\ne0$; the base is only required
    to generate $P$ (minimality is not used). The printed text has $MR'[\dots]$, a misprint for
    $MR[\dots]$. -/)
  (proof := /-- \textbf{Not proved in the paper.} Let $R'=R[x^{-1}P]_{N}$ and write $x=\sum_jc_jx_j$.
    In the domain $R'$ one has $x_j=xu_j$ ($PR'=(x)R'$), so $1=\sum_jc_ju_j$; as $R'$ is local,
    some $u_i=x_i/x$ is a unit of $R'$. Then $x/x_i=\sum_jd_j(x_j/x_i)\in
    R[x_1/x_i,\dots,x_r/x_i]=:B$ is a unit of $R'$, $B\subseteq R'$ (since $x_j/x_i=u_j/u_i$)
    and $M'=M_{R'}\cap B$ is a prime of $B$ containing $MB$. Every element of
    $R[x^{-1}P]=R[x_1/x,\dots,x_r/x]$ becomes an element of $B$ after multiplication by a power
    of the unit $x/x_i$ of $B_{M'}$, whence $R'=R[x^{-1}P]_N=B_{M'}$. -/)
  (latexEnv := "lemma")]
theorem MonoidalTransform.exists_index_subring_eq_localization (t : MonoidalTransform R P)
    {r : ℕ} {z : Fin r → R} (hz : Ideal.span (Set.range z) = P) :
    ∃ (i : Fin r) (_ : z i ≠ 0) (M'' : Ideal (adjoinDiv z (z i))), M''.IsPrime ∧
      (maximalIdeal R).map (algebraMap R (adjoinDiv z (z i))) ≤ M'' ∧
      (t.subring : Set (FractionRing R)) =
        {y | ∃ a s : adjoinDiv z (z i), s ∉ M'' ∧ y * (s : FractionRing R) = a} := by
  obtain ⟨i, u, hu, hxu⟩ := t.exists_index_isUnit_toRing_mul hz
  obtain ⟨h0, M'', hM, hle, hsub⟩ :=
    t.exists_subring_eq_of_isUnit (hz ▸ Ideal.subset_span ⟨i, rfl⟩) hu hxu
  refine ⟨i, h0, ?_⟩
  rw [← blowupAlgebra_eq_adjoinDiv hz (z i)]
  refine ⟨M'', hM, hle, ?_⟩
  ext y
  rw [SetLike.mem_coe, ← hsub]
  exact MonoidalTransform.mem_subring_iff
    (⟨z i, hz ▸ Ideal.subset_span ⟨i, rfl⟩, h0, M'', hM, hle⟩ : MonoidalTransform R P) y

/-- p. 209, "there exist an index `i` … such that `R' = R[x₁/xᵢ, …, x_r/xᵢ]_{M'}`", followed (pp. 209–210)
by "Let `A' = R[x₂/x₁, …, x_r/x₁]` and `R' = A'_{M'}`": for a minimal base `(x₁, …, x_r)` of `P` inside
one of `M` and a monoidal transform `R'` with center `P`, renaming the base so that `xᵢ` comes first,
`R'` is the monoidal transform `T₂` with element `x = x₁` and the same subring of `Frac R`
(`exists_index_subring_eq_localization`); so `x₁` is the first member of a minimal base of `P` which is
part of a minimal base of `M`.  This is the printed setting of pp. 209–210, for the monoidal transform
`T₂` in place of the given datum `t` (the isomorphism of their rings is `ringEquivOfSubringEq`);
`exists_minimal_generators` is the corresponding statement for the datum `t` itself. -/
theorem MonoidalTransform.exists_transform_eq_subring_and_minimal_generators
    (t : MonoidalTransform R P) [P.IsPrime] (hS : IsRegularLocalRing (R ⧸ P)) :
    ∃ (T₂ : MonoidalTransform R P) (S : Finset R) (r : ℕ) (z : Fin (r + 1) → R),
      T₂.subring = t.subring ∧ Ideal.span (S : Set R) = maximalIdeal R ∧
        S.card = (maximalIdeal R).spanFinrank ∧ Function.Injective z ∧ (∀ i, z i ∈ S) ∧
        z 0 = T₂.x ∧ Ideal.span (Set.range z) = P := by
  classical
  -- "If `(x₁, …, x_r)` is a minimal base of the prime ideal `P`": one inside a minimal base of `M`
  obtain ⟨S, T, hSM, hScard, hTS, hTP⟩ := exists_finset_span_eq_prime R P hS
  have hTne : T.card ≠ 0 := by
    intro h0
    have hx : t.x ∈ Ideal.span (T : Set R) := by rw [hTP]; exact t.x_mem
    rw [Finset.card_eq_zero.mp h0, Finset.coe_empty, Ideal.span_empty, Ideal.mem_bot] at hx
    exact t.x_ne_zero hx
  obtain ⟨r, hr⟩ := Nat.exists_eq_succ_of_ne_zero hTne
  let e : T ≃ Fin (r + 1) := T.equivFin.trans (finCongr hr)
  let z₀ : Fin (r + 1) → R := fun j => (e.symm j : R)
  have hz₀inj : Function.Injective z₀ := fun a b h => e.symm.injective (Subtype.ext h)
  have hz₀S : ∀ j, z₀ j ∈ S := fun j => hTS (e.symm j).2
  have hz₀P : Ideal.span (Set.range z₀) = P := by
    have hrange : Set.range z₀ = (T : Set R) := by
      ext a
      constructor
      · rintro ⟨j, rfl⟩
        exact (e.symm j).2
      · intro ha
        exact ⟨e ⟨a, ha⟩, by simp [z₀]⟩
    rw [hrange, hTP]
  -- "then there exist an index `i` and a prime ideal `M'` in `R[x₁/xᵢ, …, x_r/xᵢ]` such that
  -- `R' = R[x₁/xᵢ, …, x_r/xᵢ]_{M'}`" (p. 209): `xᵢ/x` is a unit of `R'`, and `R' = R[xᵢ⁻¹P]_{M''}`
  obtain ⟨i, u, hu, hxu⟩ := t.exists_index_isUnit_toRing_mul hz₀P
  obtain ⟨h0, M'', hM, hle, hsub⟩ :=
    t.exists_subring_eq_of_isUnit (hz₀P ▸ Ideal.subset_span ⟨i, rfl⟩) hu hxu
  -- the monoidal transform with data `(xᵢ, M'')`: the same ring `R'`
  let T₂ : MonoidalTransform R P := ⟨z₀ i, hz₀P ▸ Ideal.subset_span ⟨i, rfl⟩, h0, M'', hM, hle⟩
  -- renaming the base, `xᵢ` is `x₁`: `A' = R[x₂/x₁, …, x_r/x₁]`, `R' = A'_{M'}`
  have hz0 : (z₀ ∘ Equiv.swap 0 i) 0 = T₂.x := by
    show z₀ (Equiv.swap 0 i 0) = z₀ i
    rw [Equiv.swap_apply_left]
  exact ⟨T₂, S, r, z₀ ∘ Equiv.swap 0 i, hsub, hSM, hScard,
    hz₀inj.comp (Equiv.swap 0 i).injective, fun j => hz₀S _, hz0,
    by rw [(Equiv.swap 0 i).surjective.range_comp z₀, hz₀P]⟩

/-- pp. 209–210: the monoidal transform `R'` is a regular local ring, for a base `z` of `P` which is
part of a minimal base of `M` and whose first member is the element `x` of the data. -/
private theorem MonoidalTransform.isRegularLocalRing_of_exists_base (t : MonoidalTransform R P)
    [P.IsPrime] (hS : IsRegularLocalRing (R ⧸ P)) {S : Finset R} {r : ℕ} {z : Fin (r + 1) → R}
    (hSM : Ideal.span (S : Set R) = maximalIdeal R)
    (hScard : S.card = (maximalIdeal R).spanFinrank) (hinj : Function.Injective z)
    (hzS : ∀ i, z i ∈ S) (hz0 : z 0 = t.x) (hzP : Ideal.span (Set.range z) = P) :
    IsRegularLocalRing t.ring := by
  obtain ⟨q, hq, e, hqC, -, -, -⟩ :=
    t.exists_quotient_equiv_localization hS hSM hScard hinj hzS hz0 hzP
  have := isRegularLocalRing_atPrime_mvPolynomial_of_comap_C_eq (R ⧸ P) r q hqC
  have hQ : IsRegularLocalRing (t.ring ⧸ Ideal.span {t.xR}) :=
    IsRegularLocalRing.of_ringEquiv (R := Localization.AtPrime q) e
  have := MonoidalTransform.isNoetherianRing t
  have hxM : t.x ∈ maximalIdeal R :=
    IsLocalRing.le_maximalIdeal (Ideal.IsPrime.ne_top ‹_›) t.x_mem
  exact isRegularLocalRing_of_quotient_span_singleton (map_nonunit t.toRing t.x hxM)
    (fun h => t.x_ne_zero (MonoidalTransform.toRing_injective t (h.trans (map_zero _).symm))) hQ

/-- pp. 209–210: the monoidal transform `R'` is a regular local ring (for the data `(x, M')`, `x`
is the first member of a minimal base of `P` which is part of a minimal base of `M`,
`exists_minimal_generators`).  (The statements of Ch. III §§4–6 do not
carry the redundant hypothesis `[IsRegularLocalRing T.ring]`.) -/
theorem MonoidalTransform.isRegularLocalRing_of_isRegularLocalRing_quotient (t : MonoidalTransform R P) [P.IsPrime]
    (hS : IsRegularLocalRing (R ⧸ P)) : IsRegularLocalRing t.ring := by
  obtain ⟨S, r, z, hSM, hScard, hinj, hzS, hz0, hzP⟩ := t.exists_minimal_generators hS
  exact t.isRegularLocalRing_of_exists_base hS hSM hScard hinj hzS hz0 hzP

/-- The instance form of `MonoidalTransform.isRegularLocalRing_of_isRegularLocalRing_quotient`: the monoidal
transform `R'` of `R` with center a prime `P` with `R/P` regular is a regular local ring (pp. 209–210). -/
instance MonoidalTransform.instIsRegularLocalRing (t : MonoidalTransform R P) [P.IsPrime]
    [IsRegularLocalRing (R ⧸ P)] : IsRegularLocalRing t.ring :=
  t.isRegularLocalRing_of_isRegularLocalRing_quotient inferInstance

/-- pp. 209–210: "Let `A' = R[x₂/x₁, …, x_r/x₁]` and `R' = A'_{M'}` with a prime ideal `M'` in
`A'` which contains `MA'`. It is well known that: `PA' = (x₁)A'` and `A'/(x₁)A'` is
canonically isomorphic to a polynomial ring of `(r − 1)` variables `S[X₂, …, X_r]` over
`S = R/P` … Since `S` is regular, the polynomial ring `S[X₂, …, X_r]` over `S` is also regular.
Hence `S[X₂, …, X_r]_{M̄'} = R'/(x₁)R'` is regular and so is `R'`."  Together with p. 209: the
canonical injection `R → R'` is a local homomorphism.

Proof, as printed: take a minimal base `(x₁, …, x_r)` of `P` (one inside
a minimal base of `M`, `exists_finset_span_eq_prime`).  By the claim of p. 209, "there exist an
index `i` … such that `R' = R[x₁/xᵢ, …, x_r/xᵢ]_{M'}`" (`exists_index_subring_eq_localization`,
whose proof is `exists_index_isUnit_toRing_mul` and `exists_subring_eq_of_isUnit`), the monoidal
transform `R'` is the one with data `(xᵢ, M')`, which has the same subring of `Frac R` as `t`
and is therefore isomorphic to it (`ringEquivOfSubringEq`).  Renaming the base so that `xᵢ`
comes first, `A' = R[x₂/x₁, …, x_r/x₁]` and `R' = A'_{M'}` as in the paper; then the chart
`A'/(x₁)A' ≅ S[X₂, …, X_r]` (`exists_chart`), the localization `R'/(x₁)R' ≅ S[X₂, …, X_r]_{M̄'}`
(`exists_quotient_equiv_localization`), the regularity of `S[X₂, …, X_r]` and the passage from
`R'/(x₁)R'` to `R'` (`isRegularLocalRing_of_quotient_span_singleton`) are as in the paper.

Gaps in the paper filled: the claim "there exist an index `i`" (p. 209), see
`exists_index_subring_eq_localization`; the "well known" facts, `A'/(x₁)A' ≅ S[X₂, …, X_r]` as a
chart (`exists_chart`) and `R'/xR' ≅ (R/P)[T]_q` after localization at `M'`
(`exists_quotient_equiv_localization`), the injectivity coming from the quasi-regularity of a
minimal system of generators of `M`; and "so is `R'`", from the regularity of `R'/(x₁)R'` (one
generator more for the maximal ideal, `dim R'/(x₁)R' + 1 ≤ dim R'`).  The canonical isomorphism
with `R` for `P` principal (p. 209) is `bijective_toRing_of_isPrincipal`.  The hypothesis
`P ≠ (0)` is not used (it is automatic). -/
@[blueprint "lem:III.2-monoidal-transform-regular"
  (statement := /-- Let $R$ be a regular local ring, $P\ne(0)$ a prime ideal of $R$ with $R/P$
    regular, and $R'=R[x^{-1}P]_{M'}$ a monoidal transform of $R$ with center $P$
    (\cref{def:III.2-monoidal-transform}). Then $R'$ is a regular local ring, the canonical
    injection $R\to R'$ is a local homomorphism, and $PR'=(x)R'$. (pp.~209--210.)

    (The other claims of p.~209: that for $P$ principal the monoidal transform is canonically
    isomorphic to $R$, and that for every minimal base $(x_1,\dots,x_r)$ of $P$ one has
    $R'=R[x_1/x_i,\dots,x_r/x_i]_{M'}$ for some $i$, are \cref{lem:III.2-monoidal-transform-principal}
    and \cref{lem:III.2-monoidal-transform-index}.) -/)
  (proof := /-- Let $(x_1,\dots,x_r)$ be a minimal base of $P$ (part of a minimal base of $M$).
    By \cref{lem:III.2-monoidal-transform-index} there are an index $i$ and a prime $M'$ of
    $R[x_1/x_i,\dots,x_r/x_i]$ with $R'=R[x_1/x_i,\dots,x_r/x_i]_{M'}$ and $M'\supseteq MA'$;
    renaming we may take $i=1$: $A'=R[x_2/x_1,\dots,x_r/x_1]$ and $R'=A'_{M'}$. Then
    $PA'=(x_1)A'$ and $A'/(x_1)A'\cong S[X_2,\dots,X_r]$, $S=R/P$, the class of $x_i/x_1$
    corresponding to $X_i$. Since $S$ is regular, so is the polynomial ring
    $S[X_2,\dots,X_r]$, hence so is its localization
    $S[X_2,\dots,X_r]_{\bar M'}=R'/(x_1)R'$ at the prime $\bar M'=M'/(x_1)A'$, and therefore
    $R'$ is regular. The homomorphism $R\to R'$ is local because $M'\supseteq MA'$.
    (pp.~209--210.)

    \textbf{Gaps in the paper filled.} (i) The claim ``there exist an index $i$'' is proved
    (\cref{lem:III.2-monoidal-transform-index}). (ii) The ``well known'' facts are proved: the
    surjection $A'\to(R/P)[T_2,\dots,T_r]$, $x_i/x_1\mapsto T_i$, is well defined (an
    $R$-polynomial relation among the $x_i/x_1$ has all its coefficients in $P$) by the
    quasi-regularity of a minimal system of generators of $M$, and its kernel is $(x_1)A'$
    (\cref{lem:III.2-chart}), whence $R'/(x_1)R'\cong(R/P)[T]_{\mathfrak q}$ after localization
    at $M'$. (iii) ``and so is $R'$'': the maximal ideal of $R'$ needs one generator more than
    that of $R'/(x_1)R'$, and $\dim R'/(x_1)R'+1\le\dim R'$. -/)
  (latexEnv := "lemma")]
theorem MonoidalTransform.isRegularLocalRing_and_isLocalHom_and_span_xR_eq_map (t : MonoidalTransform R P) (hP : P.IsPrime) (hP0 : P ≠ ⊥)
    (hS : IsRegularLocalRing (R ⧸ P)) :
    IsRegularLocalRing t.ring ∧ IsLocalHom t.toRing ∧ Ideal.span {t.xR} = P.map t.toRing := by
  refine ⟨?_, inferInstance, t.span_xR_eq_map⟩
  -- (`P ≠ (0)` is automatic: `P` contains the non-zero element `x`)
  have _ := hP0
  have := hP
  -- "If `(x₁, …, x_r)` is a minimal base of the prime ideal `P`", "then there exist an index `i` … such
  -- that `R' = R[x₁/xᵢ, …, x_r/xᵢ]_{M'}`" (p. 209); renaming, `R' = A'_{M'}`, `A' = R[x₂/x₁, …, x_r/x₁]`
  obtain ⟨T₂, S, r, z, hsub, hSM, hScard, hinj, hzS, hz0, hzP⟩ :=
    t.exists_transform_eq_subring_and_minimal_generators hS
  have hreg₂ : IsRegularLocalRing T₂.ring :=
    T₂.isRegularLocalRing_of_exists_base hS hSM hScard hinj hzS hz0 hzP
  have := hreg₂
  exact IsRegularLocalRing.of_ringEquiv (T₂.ringEquivOfSubringEq t hsub)

/-- p. 209: "In this case [`P = R`], the monoidal transform of `R` is canonically isomorphic to `R`.
Note that we have also such an isomorphism when `P` is principal."  (For `P = R = (1)` see
`MonoidalTransform.bijective_toRing_of_eq_top`.)  If `P = (p)` then `x = cp` with `c` a unit of
`R` (otherwise `1 = cv ∈ M R'` for `v = p/x ∈ R'`), so `P = (x)`, `R[x⁻¹P] = R`, and the
localization of the local ring `R` at the prime `M'`, which contains the maximal ideal, is `R`
itself. -/
@[blueprint "lem:III.2-monoidal-transform-principal"
  (statement := /-- Let $R'$ be a monoidal transform of the regular local ring $R$ with center
    $P$ (\cref{def:III.2-monoidal-transform}). If $P$ is principal, then the canonical
    homomorphism $R\to R'$ is an isomorphism. (p.~209: ``Note that we have also such an
    isomorphism when $P$ is principal.'') -/)
  (proof := /-- \textbf{Not proved in the paper.} Let $P=(p)$, $R'=R[x^{-1}P]_{M'}$, so $x=cp$
    with $c\in R$ and $p\ne0$. Since $PR'=(x)R'$, $p=xv$ for some $v\in R'$, whence
    $1=cv$ in the domain $R'$ and $c$ is a unit of $R'$, hence of $R$ ($R\to R'$ is local).
    Thus $P=(x)$ and $R[x^{-1}P]=R$. The ring $R'$ is the localization of the local ring $R$
    at a prime containing its maximal ideal, that is, at the maximal ideal, so it is $R$. -/)
  (latexEnv := "lemma")]
theorem MonoidalTransform.bijective_toRing_of_isPrincipal (t : MonoidalTransform R P)
    (hP : P.IsPrincipal) : Function.Bijective t.toRing := by
  classical
  set K := FractionRing R
  have hPp : P = Ideal.span {Submodule.IsPrincipal.generator P} :=
    (Submodule.IsPrincipal.span_singleton_generator P).symm
  set p := Submodule.IsPrincipal.generator P
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp (hPp ▸ t.x_mem : t.x ∈ Ideal.span {p})
  have hp0 : p ≠ 0 := by
    rintro h
    rw [h, mul_zero] at hc
    exact t.x_ne_zero hc.symm
  have hpP : p ∈ P := hPp ▸ Ideal.subset_span rfl
  have hX0 : t.toRing t.x ≠ 0 := fun h =>
    t.x_ne_zero (t.toRing_injective (h.trans (map_zero _).symm))
  -- `c` is a unit of `R`
  have hcu : IsUnit c := by
    obtain ⟨v, hv⟩ := MonoidalTransform.exists_toRing_x_mul_eq_of_mem t hpP
    have hp0' : t.toRing p ≠ 0 := fun h => hp0 (t.toRing_injective (h.trans (map_zero _).symm))
    have h1 : t.toRing p * (t.toRing c * v) = t.toRing p * 1 := by
      rw [mul_one]
      calc t.toRing p * (t.toRing c * v) = (t.toRing c * t.toRing p) * v := by ring
        _ = t.toRing t.x * v := by rw [← map_mul, hc]
        _ = t.toRing p := hv
    have h2 : t.toRing c * v = 1 := mul_left_cancel₀ hp0' h1
    exact (isUnit_map_iff t.toRing c).mp (IsUnit.of_mul_eq_one v h2)
  obtain ⟨c', hc'⟩ := hcu.exists_left_inv
  have hxK : algebraMap R K t.x ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective R K)).mpr t.x_ne_zero
  -- hence `R[x⁻¹P] = R`
  have hsurj : Function.Surjective (algebraMap R (blowupAlgebra R P t.x)) := by
    rintro ⟨z, hz⟩
    have hle : blowupAlgebra R P t.x ≤ ⊥ := by
      refine Algebra.adjoin_le ?_
      rintro _ ⟨q, hq, rfl⟩
      obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.mp (hPp ▸ hq : q ∈ Ideal.span {p})
      refine Algebra.mem_bot.mpr ⟨r * c', ?_⟩
      have : r * c' * t.x = q := by
        rw [← hc, ← hr]
        calc r * c' * (c * p) = r * (c' * c) * p := by ring
          _ = r * p := by rw [hc', mul_one]
      rw [eq_div_iff hxK, ← map_mul, this]
    obtain ⟨r, hr⟩ := Algebra.mem_bot.mp (hle hz)
    exact ⟨r, Subtype.ext hr⟩
  have hinj : Function.Injective (algebraMap R (blowupAlgebra R P t.x)) := fun a b h =>
    IsFractionRing.injective R K (congrArg Subtype.val h)
  -- every element outside `M'` is a unit, so `R' = R[x⁻¹P]_{M'} = R`
  have hunits : t.M'.primeCompl ≤ IsUnit.submonoid _ := by
    intro b hb
    obtain ⟨r, rfl⟩ := hsurj b
    have hr : r ∉ maximalIdeal R := fun h => hb (t.le (Ideal.mem_map_of_mem _ h))
    rw [mem_maximalIdeal, mem_nonunits_iff, not_not] at hr
    exact hr.map _
  have hbij : Function.Bijective (algebraMap (blowupAlgebra R P t.x) t.ring) :=
    (IsLocalization.atUnits _ t.M'.primeCompl (S := t.ring) hunits).bijective
  exact hbij.comp ⟨hinj, hsurj⟩

/-- pp. 209–210: "`S[X₂, …, X_r]_{M̄'} = R'/(x₁)R'` is regular": the quotient of a monoidal
transform `R'` by the ideal `PR' = xR'` is a regular local ring. -/
theorem MonoidalTransform.isRegularLocalRing_quotient_span_xR (t : MonoidalTransform R P) (hP : P.IsPrime)
    (hS : IsRegularLocalRing (R ⧸ P)) : IsRegularLocalRing (t.ring ⧸ Ideal.span {t.xR}) := by
  have := hP
  obtain ⟨S, r, z, hSM, hScard, hinj, hzS, hz0, hzP⟩ := t.exists_minimal_generators hS
  obtain ⟨q, hq, e, hqC, -, -, -⟩ :=
    t.exists_quotient_equiv_localization hS hSM hScard hinj hzS hz0 hzP
  have := isRegularLocalRing_atPrime_mvPolynomial_of_comap_C_eq (R ⧸ P) r q hqC
  exact IsRegularLocalRing.of_ringEquiv (R := Localization.AtPrime q) e

open MvPolynomial in
/-- A polynomial minus its constant term lies in the ideal generated by the variables. -/
private theorem sub_C_constantCoeff_mem_span_X {S : Type u} [CommRing S] {n : ℕ} (F : MvPolynomial (Fin n) S) :
    F - C (constantCoeff F) ∈ Ideal.span (Set.range (X : Fin n → MvPolynomial (Fin n) S)) := by
  rw [← Set.image_univ, mem_ideal_span_X_image]
  intro m hm
  have hm0 : m ≠ 0 := by
    rintro rfl
    rw [mem_support_iff, coeff_sub, coeff_C, ite_eq_left rfl, ← constantCoeff_eq, sub_self] at hm
    exact hm rfl
  obtain ⟨i, hi⟩ := Finsupp.ne_iff.mp hm0
  exact ⟨i, Set.mem_univ _, hi⟩

open MvPolynomial in
/-- Every maximal ideal of a polynomial ring `k[T₁, …, T_n]` over a field has height `n`. -/
private theorem height_eq_of_isMaximal_of_isField (k : Type u) [CommRing k] (hk : IsField k) :
    ∀ (n : ℕ) (m : Ideal (MvPolynomial (Fin n) k)) [m.IsMaximal], m.height = n := by
  let _ := hk.toField
  intro n
  induction n with
  | zero =>
    intro m hm
    let e : MvPolynomial (Fin 0) k ≃+* k := (isEmptyAlgEquiv k (Fin 0)).toRingEquiv
    have hm' : (m.comap e.symm).IsMaximal :=
      Ideal.comap_isMaximal_of_surjective _ e.symm.surjective
    have hbot : m.comap e.symm = ⊥ := (Ideal.eq_bot_or_top _).resolve_right hm'.ne_top
    have hme : m = (m.comap e.symm).comap e := by
      ext F
      simp
    rw [hme, RingEquiv.height_comap, hbot, Ideal.height_bot]
    rfl
  | succ n ih =>
    intro m hm
    let φ := (finSuccEquiv k n).toRingEquiv
    let P' := m.comap
      (φ.symm : Polynomial (MvPolynomial (Fin n) k) →+* MvPolynomial (Fin (n + 1)) k)
    have hP'max : P'.IsMaximal := Ideal.comap_isMaximal_of_surjective _ φ.symm.surjective
    have hlo : P'.LiesOver (P'.under (MvPolynomial (Fin n) k)) := ⟨rfl⟩
    have hpmax : (P'.under (MvPolynomial (Fin n) k)).IsMaximal :=
      Polynomial.isMaximal_comap_C_of_isJacobsonRing P'
    have h1 := Polynomial.height_eq_height_add_one (P'.under (MvPolynomial (Fin n) k)) P'
    rw [ih] at h1
    have h2 : m.height = P'.height := (RingEquiv.height_comap φ.symm m).symm
    rw [h2, h1]
    push_cast
    rfl

/-- Let `B` be an algebra of finite type over the local ring `R`, `M'` a prime of `B` containing
`M B`, and `S = B_{M'}`. Then `S` is residually algebraic over `R` iff `M'` is maximal (the
residue field of `S` is the field of fractions of `B/M'`, a `k`-algebra of finite type; Zariski's
lemma), and then the residue field of `S` is a finite extension of that of `R`. -/
private theorem isMaximal_iff_isResiduallyAlgebraic_comp {A B S : Type u} [CommRing A] [IsLocalRing A]
    [CommRing B] [Algebra A B] [Algebra.FiniteType A B] [CommRing S] [IsLocalRing S] [Algebra B S]
    (M' : Ideal B) [M'.IsPrime] [IsLocalization.AtPrime S M']
    (hle : ∀ c ∈ maximalIdeal A, algebraMap A B c ∈ M')
    [IsLocalHom ((algebraMap B S).comp (algebraMap A B))] :
    (M'.IsMaximal ↔ RingHom.IsResiduallyAlgebraic ((algebraMap B S).comp (algebraMap A B))) ∧
      (M'.IsMaximal → letI := (ResidueField.map ((algebraMap B S).comp (algebraMap A B))).toAlgebra
        Module.Finite (ResidueField A) (ResidueField S)) := by
  classical
  have hmem : ∀ a : B, algebraMap B S a ∈ maximalIdeal S ↔ a ∈ M' := fun a =>
    IsLocalization.AtPrime.to_map_mem_maximal_iff S M' a
  -- `ι : B/M' → k(S)`, injective
  let ι : B ⧸ M' →+* ResidueField S := Ideal.Quotient.lift M'
    ((IsLocalRing.residue S).comp (algebraMap B S)) (fun a ha => by
      rw [RingHom.comp_apply, IsLocalRing.residue_eq_zero_iff]
      exact (hmem a).mpr ha)
  have hιmk : ∀ a, ι (Ideal.Quotient.mk M' a) = IsLocalRing.residue S (algebraMap B S a) :=
    fun a => rfl
  have hιinj : Function.Injective ι := by
    rw [injective_iff_map_eq_zero]
    intro w hw
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective w
    rw [hιmk, IsLocalRing.residue_eq_zero_iff, hmem] at hw
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hw
  -- `σ : k → B/M'`
  let σ : ResidueField A →+* B ⧸ M' := Ideal.Quotient.lift (maximalIdeal A)
    ((Ideal.Quotient.mk M').comp (algebraMap A B)) (fun c hc => by
      rw [RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem]
      exact hle c hc)
  have hισ : ∀ c, ι (σ c) = ResidueField.map ((algebraMap B S).comp (algebraMap A B)) c := by
    intro c
    obtain ⟨c, rfl⟩ := IsLocalRing.residue_surjective c
    rw [IsLocalRing.ResidueField.map_residue]
    rfl
  let _ := σ.toAlgebra
  let _ := (ResidueField.map ((algebraMap B S).comp (algebraMap A B))).toAlgebra
  let ιₐ : B ⧸ M' →ₐ[ResidueField A] ResidueField S := { ι with commutes' := hισ }
  have hfin : M'.IsMaximal → Module.Finite (ResidueField A) (ResidueField S) := by
    intro hmax
    let _ := Ideal.Quotient.field M'
    have : IsScalarTower A (ResidueField A) (B ⧸ M') :=
      IsScalarTower.of_algebraMap_eq fun c => rfl
    have : Algebra.FiniteType A (B ⧸ M') :=
      Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ A M')
        (Ideal.Quotient.mkₐ_surjective A M')
    have : Algebra.FiniteType (ResidueField A) (B ⧸ M') :=
      Algebra.FiniteType.of_restrictScalars_finiteType A _ _
    have := finite_of_finite_type_of_isJacobsonRing (ResidueField A) (B ⧸ M')
    have hιsurj : Function.Surjective ι := by
      intro w
      obtain ⟨y, rfl⟩ := IsLocalRing.residue_surjective w
      obtain ⟨⟨a, s⟩, hy⟩ := IsLocalization.mk'_surjective M'.primeCompl y
      dsimp only at hy
      have hs : Ideal.Quotient.mk M' (s : B) ≠ 0 := fun h =>
        s.2 (Ideal.Quotient.eq_zero_iff_mem.mp h)
      refine ⟨Ideal.Quotient.mk M' a * (Ideal.Quotient.mk M' (s : B))⁻¹, ?_⟩
      have hs' : IsLocalRing.residue S (algebraMap B S (s : B)) ≠ 0 := by
        rw [← hιmk]
        exact (map_ne_zero_iff ι hιinj).mpr hs
      rw [map_mul, map_inv₀, hιmk, hιmk, ← hy, mul_inv_eq_iff_eq_mul₀ hs', ← map_mul,
        IsLocalization.mk'_spec]
    exact Module.Finite.of_surjective ιₐ.toLinearMap hιsurj
  refine ⟨?_, hfin⟩
  unfold RingHom.IsResiduallyAlgebraic
  constructor
  · intro hmax
    have := hfin hmax
    exact Algebra.IsAlgebraic.of_finite (ResidueField A) (ResidueField S)
  · intro halg
    have halg' : Algebra.IsAlgebraic (ResidueField A) (B ⧸ M') :=
      ⟨fun w => (isAlgebraic_algHom_iff ιₐ hιinj).mp (halg.isAlgebraic (ιₐ w))⟩
    have hfield : IsField (B ⧸ M') :=
      (Algebra.IsIntegral.isField_iff_isField (R := ResidueField A) (S := B ⧸ M')
        (algebraMap (ResidueField A) (B ⧸ M')).injective).mp (Field.toIsField _)
    exact Ideal.Quotient.maximal_of_isField _ hfield

/-- p. 210: `R'` is residually algebraic over `R` iff `M'` is a maximal ideal of `R[x⁻¹P]`.

This is the Nullstellensatz step of the printed sentence "Then we see that `dim R = dim R'` if and only
if the residue field of `R'` is algebraic (necessarily, of finite degree) over that of `R`": the residue
field of `R'` is the field of fractions of `A'/M'`, a `k`-algebra of finite type, so it is algebraic over
`k` iff `A'/M'` is a field (an algebraic domain over a field is a field), and a field of finite type over
`k` is finite over `k` (Zariski's lemma).  The lemma is stated for every monoidal transform, with no
hypothesis on `P`; for `P` prime with `R/P` regular it is the composite of the two printed facts of
p. 210 (`isMaximal_iff_isResiduallyAlgebraic_of_isRegular`): "`dim R' = dim R` iff `M'` is a maximal
ideal in `A'`" (`ringKrullDim_eq_iff_isMaximal`: the count `dim R' = 1 + s + t` through the regular system
of parameters `(x₁, y, f)`) and the sentence just quoted (`ringKrullDim_eq_iff`).  The dimension count
alone does not give the equivalence: the passage between "maximal" and "algebraic" is the Nullstellensatz
(cited by the paper, footnote 3, p. 116; no transcendence-degree formula `dim R' + tr.deg = dim R` is used
by the paper here or needed). -/
theorem MonoidalTransform.isMaximal_iff_isResiduallyAlgebraic (t : MonoidalTransform R P) :
    t.M'.IsMaximal ↔ RingHom.IsResiduallyAlgebraic (R := R) (R' := t.ring) t.toRing := by
  have : Algebra.FiniteType R (blowupAlgebra R P t.x) :=
    (Subalgebra.fg_iff_finiteType _).mp (MonoidalTransform.fg_blowupAlgebra t)
  have : IsLocalHom ((algebraMap (blowupAlgebra R P t.x) t.ring).comp
      (algebraMap R (blowupAlgebra R P t.x))) := t.isLocalHom_toRing
  exact (isMaximal_iff_isResiduallyAlgebraic_comp (S := t.ring) t.M'
    (fun c hc => t.le (Ideal.mem_map_of_mem _ hc))).1

/-- p. 210: "(necessarily, of finite degree)": if `M'` is a maximal ideal of `R[x⁻¹P]`, the residue
field of `R'` is a finite extension of that of `R` (it is `B/M'`, a `k`-algebra of finite type which is
a field, hence finite by Zariski's lemma). -/
theorem MonoidalTransform.finite_residueField_of_isMaximal (t : MonoidalTransform R P)
    (h : t.M'.IsMaximal) :
    letI := (ResidueField.map t.toRing).toAlgebra
    Module.Finite (ResidueField R) (ResidueField t.ring) := by
  have : Algebra.FiniteType R (blowupAlgebra R P t.x) :=
    (Subalgebra.fg_iff_finiteType _).mp (MonoidalTransform.fg_blowupAlgebra t)
  have : IsLocalHom ((algebraMap (blowupAlgebra R P t.x) t.ring).comp
      (algebraMap R (blowupAlgebra R P t.x))) := t.isLocalHom_toRing
  exact (isMaximal_iff_isResiduallyAlgebraic_comp (S := t.ring) t.M'
    (fun c hc => t.le (Ideal.mem_map_of_mem _ hc))).2 h

open MvPolynomial in
/-- Going down for the flat extension `S → S[T₁, …, T_n]`: a prime `q` of `S[T]` lying over the
maximal ideal of the noetherian local ring `S` has height `ht(M_S) + ht(q̄)`, where
`q̄ = q/M_S S[T]` is its image in `k[T]`, `k = S/M_S`.  (Used for `dim S[X₂, …, X_r]_{M̄'}
= dim S + dim k[X₂, …, X_r]_{m̄'}`, p. 210.) -/
theorem height_eq_add_height_map_residue (S : Type u) [CommRing S] [IsLocalRing S]
    [IsNoetherianRing S] (n : ℕ)
    (q : Ideal (MvPolynomial (Fin n) S)) [q.IsPrime] (hqC : q.comap C = maximalIdeal S) :
    q.height = (maximalIdeal S).height +
      (q.map (MvPolynomial.map (IsLocalRing.residue S))).height := by
  let φk : MvPolynomial (Fin n) S →+* MvPolynomial (Fin n) (ResidueField S) :=
    MvPolynomial.map (IsLocalRing.residue S)
  have hφsurj : Function.Surjective φk :=
    MvPolynomial.map_surjective _ IsLocalRing.residue_surjective
  have hJ : (maximalIdeal S).map (algebraMap S (MvPolynomial (Fin n) S)) = RingHom.ker φk := by
    rw [MvPolynomial.ker_map, IsLocalRing.ker_residue, MvPolynomial.algebraMap_eq]
  have hlo : q.LiesOver (maximalIdeal S) := ⟨hqC.symm⟩
  have hgd := Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown (maximalIdeal S) q
  let ψ := (Ideal.quotEquivOfEq hJ).trans (RingHom.quotientKerEquivOfSurjective hφsurj)
  rw [← RingEquiv.height_map ψ] at hgd
  have hmapq : Ideal.map ψ (q.map (Ideal.Quotient.mk
      ((maximalIdeal S).map (algebraMap S (MvPolynomial (Fin n) S))))) = q.map φk := by
    have hψmk : ∀ a, ψ (Ideal.Quotient.mk
        ((maximalIdeal S).map (algebraMap S (MvPolynomial (Fin n) S))) a) = φk a := by
      intro a
      rw [RingEquiv.trans_apply, Ideal.quotEquivOfEq_mk,
        RingHom.quotientKerEquivOfSurjective_apply_mk]
    apply le_antisymm
    · rw [Ideal.map_le_iff_le_comap, Ideal.map_le_iff_le_comap]
      intro a ha
      rw [Ideal.mem_comap, Ideal.mem_comap, hψmk]
      exact Ideal.mem_map_of_mem _ ha
    · rw [Ideal.map_le_iff_le_comap]
      intro a ha
      rw [Ideal.mem_comap, ← hψmk]
      exact Ideal.mem_map_of_mem _ (Ideal.mem_map_of_mem _ ha)
  rw [hmapq] at hgd
  exact hgd

open MvPolynomial in
/-- A prime ideal `m` of a polynomial ring `k[T₁, …, T_n]` over a field has height `n` iff it is
maximal. -/
theorem height_eq_iff_isMaximal_of_isField (k : Type u) [CommRing k] (hk : IsField k)
    (n : ℕ) (m : Ideal (MvPolynomial (Fin n) k)) [m.IsPrime] :
    m.height = n ↔ m.IsMaximal := by
  constructor
  · intro hm
    by_contra hnm
    obtain ⟨m', hm', hmm'⟩ := Ideal.exists_le_maximal m (Ideal.IsPrime.ne_top inferInstance)
    have hlt : m < m' := lt_of_le_of_ne hmm' (fun h' => hnm (h' ▸ hm'))
    have h1 := Ideal.height_add_one_le_of_lt_of_isPrime hlt
    rw [hm, height_eq_of_isMaximal_of_isField k hk n m'] at h1
    have h2 : n + 1 ≤ n := by exact_mod_cast h1
    omega
  · intro hmax
    exact height_eq_of_isMaximal_of_isField k hk n m

open MvPolynomial in
/-- Clearing denominators in `k[T]_{m̄'}` (`k = S/M_S`): let `q` be a prime of `S[T]` lying over the
maximal ideal of the local ring `S`, `m = q/M_S S[T]`, `(y₁, …, y_s)` generators of `M_S` and
`f₁, …, f_t ∈ S[T]` whose images generate the maximal ideal of `k[T]_m`.  Then for every `g ∈ q`
there is `d ∉ q` with `d g ∈ (y₁, …, y_s, f₁, …, f_t)S[T]`. -/
private theorem exists_mul_eq_sum_of_mem_prime {S : Type u} [CommRing S] [IsLocalRing S] {n : ℕ}
    (q : Ideal (MvPolynomial (Fin n) S)) [q.IsPrime]
    (m : Ideal (MvPolynomial (Fin n) (ResidueField S))) [m.IsPrime]
    (hm : m = q.map (MvPolynomial.map (IsLocalRing.residue S)))
    {s u : ℕ} (y : Fin s → S) (hy : Ideal.span (Set.range y) = maximalIdeal S)
    (f : Fin u → MvPolynomial (Fin n) S)
    (hf : maximalIdeal (Localization.AtPrime m) = Ideal.span (Set.range fun i =>
      algebraMap (MvPolynomial (Fin n) (ResidueField S)) (Localization.AtPrime m)
        (MvPolynomial.map (IsLocalRing.residue S) (f i))))
    {g : MvPolynomial (Fin n) S} (hg : g ∈ q) :
    ∃ d : MvPolynomial (Fin n) S, d ∉ q ∧ ∃ (lam : Fin s → MvPolynomial (Fin n) S)
      (gam : Fin u → MvPolynomial (Fin n) S),
      d * g = ∑ j, lam j * C (y j) + ∑ i, gam i * f i := by
  classical
  let ρ : MvPolynomial (Fin n) S →+* MvPolynomial (Fin n) (ResidueField S) :=
    MvPolynomial.map (IsLocalRing.residue S)
  have hρsurj : Function.Surjective ρ :=
    MvPolynomial.map_surjective _ IsLocalRing.residue_surjective
  have hρker : RingHom.ker ρ =
      Ideal.span (Set.range fun j => (C (y j) : MvPolynomial (Fin n) S)) := by
    rw [MvPolynomial.ker_map, IsLocalRing.ker_residue, ← hy, Ideal.map_span]
    congr 1
    ext w
    simp [Set.mem_image, Set.mem_range]
  have hρg : ρ g ∈ m := hm ▸ Ideal.mem_map_of_mem _ hg
  have hmem : algebraMap _ (Localization.AtPrime m) (ρ g) ∈
      maximalIdeal (Localization.AtPrime m) :=
    (IsLocalization.AtPrime.to_map_mem_maximal_iff (Localization.AtPrime m) m _).mpr hρg
  rw [hf, Ideal.mem_span_range_iff_exists_fun] at hmem
  obtain ⟨c, hc⟩ := hmem
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples m.primeCompl Finset.univ c
  have hb' : ∀ i, ∃ a, algebraMap (MvPolynomial (Fin n) (ResidueField S)) (Localization.AtPrime m) a =
      (b : MvPolynomial (Fin n) (ResidueField S)) • c i := fun i => hb i (Finset.mem_univ i)
  choose γ0 hγ0 using hb'
  have hinj : Function.Injective
      (algebraMap (MvPolynomial (Fin n) (ResidueField S)) (Localization.AtPrime m)) :=
    IsLocalization.injective (Localization.AtPrime m) (Ideal.primeCompl_le_nonZeroDivisors m)
  have heq : (b : MvPolynomial (Fin n) (ResidueField S)) * ρ g = ∑ i, γ0 i * ρ (f i) := by
    apply hinj
    rw [map_mul, map_sum, ← hc, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, hγ0 i, Algebra.smul_def]
    ring
  obtain ⟨d, hd⟩ := hρsurj b
  choose γ hγ using fun i => hρsurj (γ0 i)
  have hmemker : d * g - ∑ i, γ i * f i ∈ RingHom.ker ρ := by
    rw [RingHom.mem_ker, map_sub, map_mul, map_sum, hd, heq, sub_eq_zero]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, hγ]
  refine ⟨d, fun hdq => ?_, ?_⟩
  · have h1 : ρ d ∈ m := by
      rw [hm]
      exact Ideal.mem_map_of_mem _ hdq
    rw [hd] at h1
    exact b.2 h1
  · rw [hρker, Ideal.mem_span_range_iff_exists_fun] at hmemker
    obtain ⟨lam, hlam⟩ := hmemker
    exact ⟨lam, γ, by rw [hlam]; ring⟩

open Classical MvPolynomial in
/-- p. 210: "Let `t = dim(k[X₂, …, X_r]_{m̄'})`, and choose a system of elements `(f₁, …, f_t)` of
`M'` such that their images in `k[X₂, …, X_r]` form a regular system of parameters of
`k[X₂, …, X_r]_{m̄'}`. Let us also choose a system of elements `(y₁, …, y_s)` of `R` such that their
images in `S` form a regular system of parameters of `S`. Then we can easily see that
`(x₁, y₁, …, y_s, f₁, …, f_t)` is a regular system of parameters of `R'`."

Formalization note (encoding): `A' = R[x⁻¹P]` is `blowupAlgebra R P t.x`; `χ : A' → S[X₂, …, X_r]`
is a chart (`exists_chart`, the printed identification of `A'/(x₁)A'` with `S[X₂, …, X_r]`,
`S = R/P`), so that `M̄' = M'/(x₁)A'` is `t.M'.map χ`; `k = S/M̄ = R/M` is `ResidueField (R ⧸ P)`, and
`m̄' = M̄'/M̄S[X₂, …, X_r]`, the prime ideal of `k[X₂, …, X_r]`, is `m`.  The elements
`f₁, …, f_t ∈ M'` are `f : Fin u → A'` with `f i ∈ t.M'` (`u = t`), their images in
`k[X₂, …, X_r]_{m̄'}` are `χ` followed by the reduction modulo `M̄` and the localization, and
`y : Fin s → R`.

Gap in the paper filled ("we can easily see"): Lean proves the two facts contained in this
sentence.  (1) `x₁, y₁, …, y_s, f₁, …, f_t` generate the maximal ideal of `R'`: an element of it is
`g/b` with `g ∈ M'`, `b ∉ M'`; its image in `R'/(x₁)R' = S[X₂, …, X_r]_{M̄'}` is handled by clearing
denominators in `k[X₂, …, X_r]_{m̄'}`, where the images of the `f_i` generate the maximal ideal, and
the kernel `M̄S[X₂, …, X_r]` of the reduction is generated by the `y_j`.  (2) `dim R' = 1 + s + t`:
`x₁` is a non-zero-divisor in the maximal ideal of `R'`, and
`dim R'/(x₁)R' = ht M̄' = ht M̄ + ht m̄' = s + t` (going down for the flat extension `S → S[X]`).
So the `1 + s + t` generators form a regular system of parameters. -/
@[blueprint "lem:III.2-dim-rsop"
  (statement := /-- With the notation of \cref{lem:III.2-monoidal-transform-regular}
    ($A'=R[x_2/x_1,\dots,x_r/x_1]$, $R'=A'_{M'}$, $\bar M'=M'/(x_1)A'$ a prime ideal of
    $S[X_2,\dots,X_r]$, $k=S/\bar M=R/M$, and $\bar m'=\bar M'/\bar MS[X_2,\dots,X_r]$ a prime ideal
    of $k[X_2,\dots,X_r]$), let $t=\dim k[X_2,\dots,X_r]_{\bar m'}$ and choose elements
    $(f_1,\dots,f_t)$ of $M'$ such that their images in $k[X_2,\dots,X_r]$ form a regular system of
    parameters of $k[X_2,\dots,X_r]_{\bar m'}$; choose elements $(y_1,\dots,y_s)$ of $R$ such
    that their images in $S$ form a regular system of parameters of $S$. Then
    $(x_1,y_1,\dots,y_s,f_1,\dots,f_t)$ is a regular system of parameters of $R'$.
    (p.~210.) (Formalization note (encoding): the identification
    $A'/(x_1)A'=S[X_2,\dots,X_r]$ is a chart $\chi\colon A'\to S[X_2,\dots,X_r]$
    (\cref{lem:III.2-chart}); $\bar M'=\chi(M')$, and $\bar m'$ is its image in $k[X_2,\dots,X_r]$.) -/)
  (proof := /-- The paper says only ``Then we can easily see that''. \textbf{Gap in the paper
    filled.} Lean proves the two facts contained in this sentence. (1) The elements
    $x_1,y_1,\dots,y_s,f_1,\dots,f_t$ generate the maximal ideal of $R'$: an element of it is
    $g/b$ with $g\in M'$, $b\notin M'$, and its image in
    $R'/(x_1)R'=S[X_2,\dots,X_r]_{\bar M'}$ is treated by clearing denominators in
    $k[X_2,\dots,X_r]_{\bar m'}$, where the images of the $f_i$ generate the maximal ideal, the
    kernel $\bar MS[X_2,\dots,X_r]$ of the reduction being generated by the $y_j$. (2)
    $\dim R'=1+s+t$: $x_1$ is a non-zero-divisor in the maximal ideal of $R'$, and
    $\dim R'/(x_1)R'=\operatorname{ht}\bar M'=\operatorname{ht}\bar M+\operatorname{ht}\bar m'=s+t$
    (going down for the flat extension $S\to S[X_2,\dots,X_r]$). Hence the $1+s+t$ generators
    form a regular system of parameters. -/)
  (latexEnv := "lemma")]
theorem MonoidalTransform.isRegularSystemOfParameters_xR_y_f (t : MonoidalTransform R P)
    (hP : P.IsPrime) (hS : IsRegularLocalRing (R ⧸ P)) {r : ℕ}
    (χ : blowupAlgebra R P t.x →+* MvPolynomial (Fin r) (R ⧸ P))
    (hχ : Function.Surjective χ)
    (hχx : RingHom.ker χ = Ideal.span {algebraMap R (blowupAlgebra R P t.x) t.x})
    (hχC : ∀ c : R, χ (algebraMap R (blowupAlgebra R P t.x) c) = C (Ideal.Quotient.mk P c))
    (m : Ideal (MvPolynomial (Fin r) (ResidueField (R ⧸ P)))) [m.IsPrime]
    (hm : m = (t.M'.map χ).map (MvPolynomial.map (IsLocalRing.residue (R ⧸ P))))
    {s u : ℕ} (y : Fin s → R) (f : Fin u → blowupAlgebra R P t.x) (hfM : ∀ i, f i ∈ t.M')
    (hy : IsRegularSystemOfParameters (R ⧸ P)
        (Finset.image (fun j => Ideal.Quotient.mk P (y j)) Finset.univ) ∧
      (Finset.image (fun j => Ideal.Quotient.mk P (y j)) Finset.univ).card = s)
    (hf : IsRegularSystemOfParameters (Localization.AtPrime m)
        (Finset.image (fun i => algebraMap (MvPolynomial (Fin r) (ResidueField (R ⧸ P)))
          (Localization.AtPrime m)
          (MvPolynomial.map (IsLocalRing.residue (R ⧸ P)) (χ (f i)))) Finset.univ) ∧
      (Finset.image (fun i => algebraMap (MvPolynomial (Fin r) (ResidueField (R ⧸ P)))
          (Localization.AtPrime m)
          (MvPolynomial.map (IsLocalRing.residue (R ⧸ P)) (χ (f i)))) Finset.univ).card = u) :
    IsRegularSystemOfParameters t.ring
        ({t.xR} ∪ Finset.image (fun j => t.toRing (y j)) Finset.univ ∪
          Finset.image (fun i => algebraMap (blowupAlgebra R P t.x) t.ring (f i)) Finset.univ) ∧
      ({t.xR} ∪ Finset.image (fun j => t.toRing (y j)) Finset.univ ∪
          Finset.image (fun i => algebraMap (blowupAlgebra R P t.x) t.ring (f i))
            Finset.univ).card = 1 + s + u := by
  have := hP
  obtain ⟨q, hq, e, hqdef, hcomap, hqC, -, he⟩ :=
    t.exists_quotient_equiv_localization_of_chart hS χ hχ hχx hχC
  have hmq : m = q.map (MvPolynomial.map (IsLocalRing.residue (R ⧸ P))) := by rw [hm, hqdef]
  have hPM : P ≤ maximalIdeal R := IsLocalRing.le_maximalIdeal hP.ne_top
  have hxM : t.x ∈ maximalIdeal R := hPM t.x_mem
  have hNoeth := MonoidalTransform.isNoetherianRing t
  have hX0 : t.toRing t.x ≠ 0 := fun h =>
    t.x_ne_zero (MonoidalTransform.toRing_injective t (h.trans (map_zero _).symm))
  -- the generators
  have hyspan : Ideal.span (Set.range fun j => Ideal.Quotient.mk P (y j)) =
      maximalIdeal (R ⧸ P) := by
    rw [← hy.1.1]
    congr 1
    ext w
    simp
  have hfspan : maximalIdeal (Localization.AtPrime m) = Ideal.span (Set.range fun i =>
      algebraMap (MvPolynomial (Fin r) (ResidueField (R ⧸ P))) (Localization.AtPrime m)
        (MvPolynomial.map (IsLocalRing.residue (R ⧸ P)) (χ (f i)))) := by
    rw [← hf.1.1]
    congr 1
    ext w
    simp
  have hyM : ∀ j, y j ∈ maximalIdeal R := by
    intro j
    have h1 : Ideal.Quotient.mk P (y j) ∈ maximalIdeal (R ⧸ P) := by
      rw [← hyspan]
      exact Ideal.subset_span ⟨j, rfl⟩
    by_contra h2
    exact ((IsLocalRing.mem_maximalIdeal _).mp h1)
      (((IsLocalRing.mem_maximalIdeal _).not.mp h2 |> not_not.mp).map _)
  -- dimension: `dim R' = 1 + s + t`
  have hdimR' : ringKrullDim t.ring = (q.height : WithBot ℕ∞) + 1 := by
    have h1 := Module.ringKrullDim_quotient_add_one_of_mem_nonZeroDivisors
      (mem_nonZeroDivisors_of_ne_zero hX0) (p := maximalIdeal t.ring)
      IsLocalRing.maximalIdeal_height_eq_ringKrullDim (map_nonunit t.toRing t.x hxM)
    rw [← h1, ← IsLocalization.AtPrime.ringKrullDim_eq_height q (Localization.AtPrime q),
      ringKrullDim_eq_of_ringEquiv e]
    rfl
  have hgd := height_eq_add_height_map_residue (R ⧸ P) r q hqC
  rw [← hmq] at hgd
  have hs : (maximalIdeal (R ⧸ P)).height = s := by
    have h1 := IsLocalRing.maximalIdeal_height_eq_ringKrullDim (R := R ⧸ P)
    rw [← hy.1.2, hy.2] at h1
    exact_mod_cast h1
  have hu : m.height = u := by
    have h1 := IsLocalization.AtPrime.ringKrullDim_eq_height m (Localization.AtPrime m)
    rw [← hf.1.2, hf.2] at h1
    exact_mod_cast h1.symm
  have hdim : ringKrullDim t.ring = ((1 + s + u : ℕ) : WithBot ℕ∞) := by
    rw [hdimR', hgd, hs, hu]
    push_cast
    ring
  -- the maximal ideal of `R'` is generated by `x, y, f`
  set F : Finset t.ring := {t.xR} ∪ Finset.image (fun j => t.toRing (y j)) Finset.univ ∪
    Finset.image (fun i => algebraMap (blowupAlgebra R P t.x) t.ring (f i)) Finset.univ with hF
  have hxF : t.xR ∈ F :=
    Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton_self _))
  have hyF : ∀ j, t.toRing (y j) ∈ F := fun j =>
    Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_univ j)))
  have hfF : ∀ i, algebraMap (blowupAlgebra R P t.x) t.ring (f i) ∈ F := fun i =>
    Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_univ i))
  have hFN : Ideal.span (F : Set t.ring) ≤ maximalIdeal t.ring := by
    rw [Ideal.span_le]
    intro a ha
    simp only [hF, Finset.coe_union, Finset.coe_singleton, Finset.coe_image, Finset.coe_univ,
      Set.image_univ, Set.mem_union, Set.mem_singleton_iff, Set.mem_range] at ha
    rcases ha with (rfl | ⟨j, rfl⟩) | ⟨i, rfl⟩
    · exact map_nonunit t.toRing t.x hxM
    · exact map_nonunit t.toRing _ (hyM j)
    · exact (IsLocalization.AtPrime.to_map_mem_maximal_iff t.ring t.M' _).mpr (hfM i)
  have hNF : maximalIdeal t.ring ≤ Ideal.span (F : Set t.ring) := by
    intro n hn
    have hQloc : IsLocalRing (t.ring ⧸ Ideal.span {t.xR}) := isLocalRing_quotient_of_le
      (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr (map_nonunit t.toRing _ hxM)))
    have hlocQ : IsLocalHom (Ideal.Quotient.mk (Ideal.span {t.xR})) :=
      IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective
    have hw : Ideal.Quotient.mk (Ideal.span {t.xR}) n ∈
        maximalIdeal (t.ring ⧸ Ideal.span {t.xR}) := map_nonunit _ n hn
    have hw' : e.symm (Ideal.Quotient.mk (Ideal.span {t.xR}) n) ∈
        maximalIdeal (Localization.AtPrime q) :=
      map_nonunit (e.symm : _ →+* Localization.AtPrime q) _ hw
    obtain ⟨⟨g, b⟩, hgb⟩ := IsLocalization.mk'_surjective q.primeCompl
      (e.symm (Ideal.Quotient.mk (Ideal.span {t.xR}) n))
    dsimp only at hgb
    have hspec := IsLocalization.mk'_spec (Localization.AtPrime q) g b
    rw [hgb] at hspec
    have hgq : g ∈ q := by
      rw [← IsLocalization.AtPrime.to_map_mem_maximal_iff (Localization.AtPrime q) q, ← hspec]
      exact Ideal.mul_mem_right _ _ hw'
    obtain ⟨d, hdq, lam, gam, hd⟩ := exists_mul_eq_sum_of_mem_prime q m hmq
      (fun j => Ideal.Quotient.mk P (y j)) hyspan (fun i => χ (f i)) hfspan hgq
    -- transport to `R'/xR'`
    let Ψ : MvPolynomial (Fin r) (R ⧸ P) →+* t.ring ⧸ Ideal.span {t.xR} :=
      (e : Localization.AtPrime q →+* t.ring ⧸ Ideal.span {t.xR}).comp
        (algebraMap (MvPolynomial (Fin r) (R ⧸ P)) (Localization.AtPrime q))
    have hΨχ : ∀ a, Ψ (χ a) = Ideal.Quotient.mk _ (algebraMap (blowupAlgebra R P t.x) t.ring a) :=
      he
    have hΨC : ∀ c : R, Ψ (C (Ideal.Quotient.mk P c)) =
        Ideal.Quotient.mk _ (t.toRing c) := fun c => by
      rw [← hχC, hΨχ]
      rfl
    have hΨg : Ψ g = Ideal.Quotient.mk _ n * Ψ (b : MvPolynomial (Fin r) (R ⧸ P)) := by
      show e (algebraMap _ (Localization.AtPrime q) g) = _ * e (algebraMap _ (Localization.AtPrime q) _)
      rw [← hspec, map_mul, RingEquiv.apply_symm_apply]
    have hΨunit : ∀ c : q.primeCompl, IsUnit (Ψ (c : MvPolynomial (Fin r) (R ⧸ P))) := fun c =>
      (IsLocalization.map_units (Localization.AtPrime q) c).map
        (e : Localization.AtPrime q →+* t.ring ⧸ Ideal.span {t.xR})
    have hdΨ := congrArg Ψ hd
    simp only [map_mul, map_add, map_sum, hΨg, hΨC, hΨχ] at hdΨ
    -- lifts to `R'`
    choose lam' hlam' using fun j => Ideal.Quotient.mk_surjective (Ψ (lam j))
    choose gam' hgam' using fun i => Ideal.Quotient.mk_surjective (Ψ (gam i))
    obtain ⟨v, hv⟩ := Ideal.Quotient.mk_surjective
      (Ψ d * Ψ (b : MvPolynomial (Fin r) (R ⧸ P)))
    have hvunit : IsUnit v := by
      have : IsUnit (Ideal.Quotient.mk (Ideal.span {t.xR}) v) := by
        rw [hv]
        exact (hΨunit ⟨d, hdq⟩).mul (hΨunit b)
      exact IsLocalHom.map_nonunit _ this
    have hmk : Ideal.Quotient.mk (Ideal.span {t.xR}) (v * n) =
        Ideal.Quotient.mk (Ideal.span {t.xR}) (∑ j, lam' j * t.toRing (y j) +
          ∑ i, gam' i * algebraMap (blowupAlgebra R P t.x) t.ring (f i)) := by
      rw [map_mul, hv, map_add, map_sum, map_sum]
      simp only [map_mul, hlam', hgam']
      rw [← hdΨ]
      ring
    have h1 := Ideal.Quotient.eq.mp hmk
    have hJ : Ideal.span {t.xR} ≤ Ideal.span (F : Set t.ring) :=
      Ideal.span_le.mpr (Set.singleton_subset_iff.mpr (Ideal.subset_span hxF))
    have hsum : ∑ j, lam' j * t.toRing (y j) +
        ∑ i, gam' i * algebraMap (blowupAlgebra R P t.x) t.ring (f i) ∈
          Ideal.span (F : Set t.ring) :=
      add_mem (sum_mem fun j _ => Ideal.mul_mem_left _ _ (Ideal.subset_span (hyF j)))
        (sum_mem fun i _ => Ideal.mul_mem_left _ _ (Ideal.subset_span (hfF i)))
    have hvn : v * n ∈ Ideal.span (F : Set t.ring) := by
      have := add_mem (hJ h1) hsum
      rwa [sub_add_cancel] at this
    obtain ⟨w, hw⟩ := hvunit.exists_left_inv
    have : n = w * (v * n) := by rw [← mul_assoc, hw, one_mul]
    rw [this]
    exact Ideal.mul_mem_left _ _ hvn
  have hspan : Ideal.span (F : Set t.ring) = maximalIdeal t.ring := le_antisymm hFN hNF
  have hFle : F.card ≤ 1 + s + u := by
    refine (Finset.card_union_le _ _).trans ?_
    have h1 := Finset.card_union_le ({t.xR} : Finset t.ring)
      (Finset.image (fun j => t.toRing (y j)) Finset.univ)
    have h2 := Finset.card_image_le (s := (Finset.univ : Finset (Fin s)))
      (f := fun j => t.toRing (y j))
    have h3 := Finset.card_image_le (s := (Finset.univ : Finset (Fin u)))
      (f := fun i => algebraMap (blowupAlgebra R P t.x) t.ring (f i))
    simp only [Finset.card_singleton, Finset.card_univ, Fintype.card_fin] at h1 h2 h3
    omega
  have hFge : (maximalIdeal t.ring).spanFinrank ≤ F.card := by
    rw [← hspan]
    exact (Submodule.spanFinrank_span_le_ncard_of_finite (Finset.finite_toSet F)).trans
      (Set.ncard_coe_finset F).le
  have hht : (maximalIdeal t.ring).height = ((1 + s + u : ℕ) : ℕ∞) := by
    have h1 := IsLocalRing.maximalIdeal_height_eq_ringKrullDim (R := t.ring)
    rw [hdim] at h1
    exact_mod_cast h1
  have hkr := Ideal.height_le_spanFinrank (maximalIdeal t.ring)
    (maximalIdeal.isMaximal t.ring).ne_top
  rw [hht] at hkr
  have hkr' : 1 + s + u ≤ (maximalIdeal t.ring).spanFinrank := by exact_mod_cast hkr
  have hcard : F.card = 1 + s + u := by omega
  refine ⟨⟨hspan, ?_⟩, hcard⟩
  rw [hcard, hdim]

open Classical in
omit [IsDomain R] in
/-- `dim R = (r + 1) + dim R/P` for `P = (z₀, …, z_r)` generated by `r + 1` elements of a minimal
system of generators of `M` with `R/P` regular (the count behind "`r + s = dim R`", p. 210: the
minimal base `(x₁, …, x_r)` of `P` extends to a regular system of parameters of `R`). -/
theorem ringKrullDim_eq_add_of_minimal_generators [P.IsPrime]
    (hS : IsRegularLocalRing (R ⧸ P)) {S : Finset R} {r : ℕ} {z : Fin (r + 1) → R}
    (hSM : Ideal.span (S : Set R) = maximalIdeal R)
    (hScard : S.card = (maximalIdeal R).spanFinrank) (hinj : Function.Injective z)
    (hzS : ∀ i, z i ∈ S) (hzP : Ideal.span (Set.range z) = P) :
    ringKrullDim R = ((r + 1 : ℕ) : WithBot ℕ∞) + ringKrullDim (R ⧸ P) := by
  have _ := hS
  have hPM : P ≤ maximalIdeal R := IsLocalRing.le_maximalIdeal (Ideal.IsPrime.ne_top ‹_›)
  let Y : Finset R := S \ Finset.image z Finset.univ
  have hcardS : S.card = r + 1 + Y.card := by
    have h1 : (Finset.image z Finset.univ).card = r + 1 := by
      rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]
    have h2 : Finset.image z Finset.univ ⊆ S := fun a ha => by
      obtain ⟨k, -, rfl⟩ := Finset.mem_image.mp ha
      exact hzS k
    have := Finset.card_sdiff_add_card_eq_card h2
    have hY : Y.card = (S \ Finset.image z Finset.univ).card := rfl
    omega
  have hMS : (maximalIdeal R).map (Ideal.Quotient.mk P) = maximalIdeal (R ⧸ P) :=
    IsLocalRing.map_maximalIdeal_of_surjective _ Ideal.Quotient.mk_surjective
  have hMSle : (maximalIdeal (R ⧸ P)).height ≤ Y.card := by
    have hspan : maximalIdeal (R ⧸ P) =
        Ideal.span ((Y.image (Ideal.Quotient.mk P) : Finset (R ⧸ P)) : Set (R ⧸ P)) := by
      apply le_antisymm
      · rw [← hMS, ← hSM, Ideal.map_span, Ideal.span_le]
        rintro _ ⟨a, ha, rfl⟩
        by_cases haz : a ∈ Finset.image z Finset.univ
        · obtain ⟨k, -, rfl⟩ := Finset.mem_image.mp haz
          rw [Ideal.Quotient.eq_zero_iff_mem.mpr (hzP ▸ Ideal.subset_span ⟨k, rfl⟩)]
          exact zero_mem _
        · exact Ideal.subset_span (Finset.mem_coe.mpr
            (Finset.mem_image_of_mem _ (Finset.mem_sdiff.mpr ⟨ha, haz⟩)))
      · rw [Ideal.span_le]
        intro w hw
        obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hw)
        rw [← hMS]
        exact Ideal.mem_map_of_mem _ (hSM ▸ Ideal.subset_span (Finset.mem_sdiff.mp ha).1)
    refine (Ideal.height_le_spanFinrank (maximalIdeal (R ⧸ P))
      (Ideal.IsPrime.ne_top inferInstance)).trans ?_
    rw [hspan]
    have h1 := Submodule.spanFinrank_span_le_ncard_of_finite (R := R ⧸ P)
      (Finset.finite_toSet (Y.image (Ideal.Quotient.mk P)))
    rw [Set.ncard_coe_finset] at h1
    exact_mod_cast h1.trans Finset.card_image_le
  have hMSge : (Y.card : ℕ∞) ≤ (maximalIdeal (R ⧸ P)).height := by
    have h := Ideal.height_le_height_add_spanFinrank_of_le (p := maximalIdeal R) hPM
    rw [hMS] at h
    have hM : (maximalIdeal R).height = ((r + 1 + Y.card : ℕ) : ℕ∞) := by
      have h1 := IsLocalRing.maximalIdeal_height_eq_ringKrullDim (R := R)
      rw [← IsRegularLocalRing.spanFinrank_maximalIdeal (R := R), ← hScard, hcardS] at h1
      exact_mod_cast h1
    have hPs : P.spanFinrank ≤ r + 1 := by
      rw [← hzP]
      refine (Submodule.spanFinrank_span_le_ncard_of_finite (Set.finite_range z)).trans ?_
      rw [Set.ncard_range_of_injective hinj, Nat.card_eq_fintype_card, Fintype.card_fin]
    rw [hM] at h
    by_cases htop : (maximalIdeal (R ⧸ P)).height = ⊤
    · rw [htop]
      exact le_top
    obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp htop
    rw [← hn] at h ⊢
    have : r + 1 + Y.card ≤ n + P.spanFinrank := by exact_mod_cast h
    exact_mod_cast (by omega : Y.card ≤ n)
  have hMSeq : (maximalIdeal (R ⧸ P)).height = Y.card := le_antisymm hMSle hMSge
  have hdimR : ringKrullDim R = ((Y.card + r : ℕ) : WithBot ℕ∞) + 1 := by
    rw [← IsRegularLocalRing.spanFinrank_maximalIdeal, ← hScard, hcardS]
    push_cast
    ring
  have hdimRP : ringKrullDim (R ⧸ P) = (Y.card : WithBot ℕ∞) := by
    rw [← IsLocalRing.maximalIdeal_height_eq_ringKrullDim, hMSeq]
    rfl
  rw [hdimR, hdimRP]
  push_cast
  ring

open Classical in
/-- A regular system of parameters of `k[T]_{m̄'}` may be chosen among images of elements of the
prime `p` (clear denominators; a unit multiple of a regular system of parameters is one). -/
private theorem exists_family_mem_prime_isRegularSystemOfParameters {B : Type u} [CommRing B]
    (p : Ideal B) [p.IsPrime] [IsRegularLocalRing (Localization.AtPrime p)] :
    ∃ (u : ℕ) (a : Fin u → B), (∀ i, a i ∈ p) ∧
      IsRegularSystemOfParameters (Localization.AtPrime p)
        (Finset.image (fun i => algebraMap B (Localization.AtPrime p) (a i)) Finset.univ) ∧
      (Finset.image (fun i => algebraMap B (Localization.AtPrime p) (a i)) Finset.univ).card = u := by
  classical
  obtain ⟨-, G, hG⟩ := (isRegularLocalRing_iff_exists_rsop (Localization.AtPrime p)).mp inferInstance
  let w : Fin G.card → Localization.AtPrime p := fun i => (G.equivFin.symm i : Localization.AtPrime p)
  have hwG : ∀ i, w i ∈ G := fun i => (G.equivFin.symm i).2
  have hGw : ∀ x ∈ G, ∃ i, w i = x := fun x hx => ⟨G.equivFin ⟨x, hx⟩, by simp [w]⟩
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples p.primeCompl (Finset.univ : Finset (Fin G.card)) w
  have hb' : ∀ i, ∃ a, algebraMap B (Localization.AtPrime p) a = (b : B) • w i := fun i =>
    hb i (Finset.mem_univ i)
  choose a ha using hb'
  have hwN : ∀ i, w i ∈ maximalIdeal (Localization.AtPrime p) := fun i => by
    rw [← hG.1]
    exact Ideal.subset_span (Finset.mem_coe.mpr (hwG i))
  have haN : ∀ i, algebraMap B (Localization.AtPrime p) (a i) ∈ maximalIdeal (Localization.AtPrime p) :=
    fun i => by
      rw [ha i, Algebra.smul_def]
      exact Ideal.mul_mem_left _ _ (hwN i)
  have hap : ∀ i, a i ∈ p := fun i =>
    (IsLocalization.AtPrime.to_map_mem_maximal_iff (Localization.AtPrime p) p _).mp (haN i)
  have hbu : IsUnit (algebraMap B (Localization.AtPrime p) (b : B)) :=
    IsLocalization.map_units (Localization.AtPrime p) b
  have hspan : Ideal.span ((Finset.image (fun i => algebraMap B (Localization.AtPrime p) (a i))
      Finset.univ : Finset (Localization.AtPrime p)) : Set (Localization.AtPrime p)) =
        maximalIdeal (Localization.AtPrime p) := by
    apply le_antisymm
    · rw [Ideal.span_le]
      intro x hx
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hx)
      exact haN i
    · rw [← hG.1, Ideal.span_le]
      intro x hx
      obtain ⟨i, rfl⟩ := hGw x (Finset.mem_coe.mp hx)
      obtain ⟨v, hv⟩ := hbu.exists_left_inv
      have : w i = v * algebraMap B (Localization.AtPrime p) (a i) := by
        rw [ha i, Algebra.smul_def, ← mul_assoc, hv, one_mul]
      rw [this]
      exact Ideal.mul_mem_left _ _ (Ideal.subset_span (Finset.mem_coe.mpr
        (Finset.mem_image_of_mem _ (Finset.mem_univ i))))
  have hle : (Finset.image (fun i => algebraMap B (Localization.AtPrime p) (a i))
      Finset.univ).card ≤ G.card := by
    simpa using Finset.card_image_le (s := (Finset.univ : Finset (Fin G.card)))
      (f := fun i => algebraMap B (Localization.AtPrime p) (a i))
  have hge : G.card ≤ (Finset.image (fun i => algebraMap B (Localization.AtPrime p) (a i))
      Finset.univ).card := by
    have h1 : (maximalIdeal (Localization.AtPrime p)).spanFinrank ≤
        (Finset.image (fun i => algebraMap B (Localization.AtPrime p) (a i)) Finset.univ).card := by
      rw [← hspan]
      exact (Submodule.spanFinrank_span_le_ncard_of_finite (Finset.finite_toSet _)).trans
        (Set.ncard_coe_finset _).le
    have h2 := IsRegularLocalRing.spanFinrank_maximalIdeal (R := Localization.AtPrime p)
    rw [← hG.2] at h2
    have h3 : (maximalIdeal (Localization.AtPrime p)).spanFinrank = G.card := by exact_mod_cast h2
    omega
  have hcard : (Finset.image (fun i => algebraMap B (Localization.AtPrime p) (a i))
      Finset.univ).card = G.card := le_antisymm hle hge
  refine ⟨G.card, a, hap, ⟨hspan, ?_⟩, hcard⟩
  rw [hcard, hG.2]

open Classical MvPolynomial in
/-- p. 210: "It follows that, for `M'` and `R'` as above, `dim R' = dim R` if and only if `M'` is a
maximal ideal in `A'`."

The printed argument: `(x₁, y₁, …, y_s, f₁, …, f_t)` is a regular system of parameters of `R'`
(`isRegularSystemOfParameters_xR_y_f`), so `dim R' = 1 + s + t`, whereas `dim R = r + s` (`r` the
number of elements of a minimal base of `P`, `s = dim S`; Lean fills this count:
`ringKrullDim_eq_add_of_minimal_generators`).  Hence `dim R' = dim R` iff `t = r − 1`, i.e. iff `m̄'`
has height `r − 1 = dim k[X₂, …, X_r]`.

Gap in the paper filled ("It follows"): a prime of a polynomial ring in `n` variables over a field
has height `n` iff it is maximal, `m̄'` is maximal iff `M̄'` is (`M̄'` contains the kernel of the
reduction `S[X] → k[X]`), and `M̄'` is maximal iff `M'` is (`M̄' = M'/(x₁)A'`).  The hypothesis
`P ≠ (0)` is not used. -/
@[blueprint "lem:III.2-dim-maximal"
  (statement := /-- For $M'$ and $R'$ as in \cref{lem:III.2-dim-rsop}, $\dim R'=\dim R$ if and
    only if $M'$ is a maximal ideal in $A'$. (p.~210.) -/)
  (proof := /-- By \cref{lem:III.2-dim-rsop}, $\dim R'=1+s+t$, where $s=\dim S$ and
    $t=\dim k[X_2,\dots,X_r]_{\bar m'}$, while $\dim R=r+s$. Hence $\dim R'=\dim R$ iff
    $t=r-1$.

    \textbf{Gap in the paper filled.} Lean proves: $r+s=\dim R$ for $P=(x_1,\dots,x_r)$ with
    $x_1,\dots,x_r$ part of a minimal base of $M$ and $R/P$ regular; a prime ideal of
    $k[X_2,\dots,X_r]$ has height $r-1$ iff it is maximal; $\bar m'$ is maximal iff $\bar M'$ is,
    iff $M'$ is. -/)
  (latexEnv := "lemma")]
theorem MonoidalTransform.ringKrullDim_eq_iff_isMaximal (t : MonoidalTransform R P) (hP : P.IsPrime)
    (hP0 : P ≠ ⊥) (hS : IsRegularLocalRing (R ⧸ P)) :
    ringKrullDim t.ring = ringKrullDim R ↔ t.M'.IsMaximal := by
  have := hP
  -- (`P ≠ (0)` is automatic: `P` contains the non-zero element `x`)
  have _ := hP0
  obtain ⟨S, r, z, hSM, hScard, hinj, hzS, hz0, hzP⟩ := t.exists_minimal_generators hS
  obtain ⟨χ, hχ, hχx, hχC, -⟩ := t.exists_chart hSM hScard hinj hzS hz0 hzP
  obtain ⟨q, hq, e, hqdef, hcomap, hqC, hmax, -⟩ :=
    t.exists_quotient_equiv_localization_of_chart hS χ hχ hχx hχC
  -- `m̄' = M̄'/M̄ S[X₂, …, X_r]`, a prime ideal of `k[X₂, …, X_r]`
  let ρ : MvPolynomial (Fin r) (R ⧸ P) →+* MvPolynomial (Fin r) (ResidueField (R ⧸ P)) :=
    MvPolynomial.map (IsLocalRing.residue (R ⧸ P))
  have hρsurj : Function.Surjective ρ :=
    MvPolynomial.map_surjective _ IsLocalRing.residue_surjective
  have hρq : RingHom.ker ρ ≤ q := by
    rw [MvPolynomial.ker_map, IsLocalRing.ker_residue]
    exact Ideal.map_le_iff_le_comap.mpr hqC.ge
  have hmprime : (q.map ρ).IsPrime := Ideal.map_isPrime_of_surjective hρsurj hρq
  set m := q.map ρ with hmdef
  have hm : m = (t.M'.map χ).map (MvPolynomial.map (IsLocalRing.residue (R ⧸ P))) := by
    rw [hmdef, hqdef]
  have hmρ : ∀ x, ρ x ∈ m ↔ x ∈ q := fun x => by
    rw [← Ideal.mem_comap, hmdef, Ideal.comap_map_of_surjective _ hρsurj,
      ← RingHom.ker_eq_comap_bot, sup_eq_left.mpr hρq]
  -- `m̄'` is maximal iff `M̄'` is
  have hmmax : m.IsMaximal ↔ q.IsMaximal := by
    constructor
    · intro h
      have := Ideal.comap_isMaximal_of_surjective ρ hρsurj (K := m)
      rwa [hmdef, Ideal.comap_map_of_surjective _ hρsurj, ← RingHom.ker_eq_comap_bot,
        sup_eq_left.mpr hρq] at this
    · intro h
      exact Ideal.IsMaximal.map_of_surjective_of_ker_le hρsurj hρq
  -- the regular system of parameters `y₁, …, y_s` of `S = R/P`
  obtain ⟨-, F, hF⟩ := (isRegularLocalRing_iff_exists_rsop (R ⧸ P)).mp hS
  have hFsurj : ∀ j : Fin F.card, ∃ c : R,
      Ideal.Quotient.mk P c = (F.equivFin.symm j : R ⧸ P) :=
    fun j => Ideal.Quotient.mk_surjective _
  choose y hy using hFsurj
  have himage : Finset.image (fun j => Ideal.Quotient.mk P (y j)) Finset.univ = F := by
    ext w
    simp only [Finset.mem_image, Finset.mem_univ, true_and, hy]
    constructor
    · rintro ⟨j, rfl⟩
      exact (F.equivFin.symm j).2
    · intro hw
      exact ⟨F.equivFin ⟨w, hw⟩, by simp⟩
  have hys : IsRegularSystemOfParameters (R ⧸ P)
      (Finset.image (fun j => Ideal.Quotient.mk P (y j)) Finset.univ) ∧
      (Finset.image (fun j => Ideal.Quotient.mk P (y j)) Finset.univ).card = F.card := by
    rw [himage]
    exact ⟨hF, rfl⟩
  -- the elements `f₁, …, f_t` of `M'` whose images form a regular system of parameters of
  -- `k[X₂, …, X_r]_{m̄'}`
  have hmC : m.comap C = maximalIdeal (ResidueField (R ⧸ P)) := by
    rw [IsLocalRing.maximalIdeal_eq_bot]
    exact Ideal.eq_bot_of_prime _
  have hreg : IsRegularLocalRing (Localization.AtPrime m) :=
    isRegularLocalRing_atPrime_mvPolynomial_of_comap_C_eq (ResidueField (R ⧸ P)) r m hmC
  obtain ⟨u, a, ham, hrsop, hcard⟩ := exists_family_mem_prime_isRegularSystemOfParameters m
  have hlift : ∀ i, ∃ c : blowupAlgebra R P t.x,
      MvPolynomial.map (IsLocalRing.residue (R ⧸ P)) (χ c) = a i := fun i => by
    obtain ⟨b, hb⟩ := hρsurj (a i)
    obtain ⟨c, hc⟩ := hχ b
    exact ⟨c, by rw [hc]; exact hb⟩
  choose f hf using hlift
  have hfM : ∀ i, f i ∈ t.M' := fun i =>
    (hcomap (f i)).mp ((hmρ _).mp (by rw [hf i]; exact ham i))
  have hfs : IsRegularSystemOfParameters (Localization.AtPrime m)
        (Finset.image (fun i => algebraMap (MvPolynomial (Fin r) (ResidueField (R ⧸ P)))
          (Localization.AtPrime m)
          (MvPolynomial.map (IsLocalRing.residue (R ⧸ P)) (χ (f i)))) Finset.univ) ∧
      (Finset.image (fun i => algebraMap (MvPolynomial (Fin r) (ResidueField (R ⧸ P)))
          (Localization.AtPrime m)
          (MvPolynomial.map (IsLocalRing.residue (R ⧸ P)) (χ (f i)))) Finset.univ).card = u := by
    simp only [hf]
    exact ⟨hrsop, hcard⟩
  -- `(x₁, y₁, …, y_s, f₁, …, f_t)` is a regular system of parameters of `R'`
  obtain ⟨hrsopR', hcardR'⟩ :=
    t.isRegularSystemOfParameters_xR_y_f hP hS χ hχ hχx hχC m hm y f hfM hys hfs
  have hdimR' : ringKrullDim t.ring = ((1 + F.card + u : ℕ) : WithBot ℕ∞) := by
    rw [← hrsopR'.2, hcardR']
  have hdimR : ringKrullDim R = ((r + 1 + F.card : ℕ) : WithBot ℕ∞) := by
    rw [ringKrullDim_eq_add_of_minimal_generators hS hSM hScard hinj hzS hzP, ← hF.2]
    push_cast
    ring
  have hu : m.height = u := by
    have h1 := IsLocalization.AtPrime.ringKrullDim_eq_height m (Localization.AtPrime m)
    rw [← hrsop.2, hcard] at h1
    exact_mod_cast h1.symm
  rw [hdimR', hdimR, ← hmax, ← hmmax,
    ← height_eq_iff_isMaximal_of_isField (ResidueField (R ⧸ P)) (Field.toIsField _) r m, hu]
  constructor
  · intro h
    have h' : 1 + F.card + u = r + 1 + F.card := by exact_mod_cast h
    have h'' : u = r := by omega
    rw [h'']
  · intro h
    have h' : u = r := by exact_mod_cast h
    rw [show 1 + F.card + u = r + 1 + F.card by omega]

/-- p. 210: "Let `R'` be a monoidal transform of `R` with center `P` as above. Then we see that
`dim R = dim R'` if and only if the residue field of `R'` is algebraic (necessarily, of finite
degree) over that of `R`."

The proof is the printed one: `dim R' = dim R` iff `M'` is a maximal ideal of `A'`
(`ringKrullDim_eq_iff_isMaximal`, "It follows that …", p. 210), and `M'` is maximal iff the residue
field of `R'`, the field of fractions of `A'/M'`, is algebraic over `k`
(`isMaximal_iff_isResiduallyAlgebraic`).  Gap in the paper filled ("Then we see that"): the last
equivalence is Zariski's lemma (`A'/M'` is a `k`-algebra of finite type, hence a field iff it is
algebraic over `k`); the parenthetical "(necessarily, of finite degree)" is
`finite_residueField_of_ringKrullDim_eq`.  The hypothesis `P ≠ (0)` is not used. -/
@[blueprint "lem:III.2-dim"
  (statement := /-- Let $R'$ be a monoidal transform of $R$ with center $P$ as in
    \cref{lem:III.2-monoidal-transform-regular}. Then $\dim R=\dim R'$ if and only if the
    residue field of $R'$ is algebraic (necessarily, of finite degree) over that of $R$, i.e.\
    iff $R'$ is residually algebraic over $R$ (\cref{def:III.2-residually}). (p.~210.)
    (The parenthetical ``(necessarily, of finite degree)'' is
    \cref{lem:III.2-dim-finite}.) -/)
  (proof := /-- By \cref{lem:III.2-dim-maximal}, $\dim R'=\dim R$ if and only if $M'$ is a maximal
    ideal in $A'$. Now the residue field of $R'$ is the field of fractions of $A'/M'$, a
    $k$-algebra of finite type; so $M'$ is maximal iff $A'/M'$ is a field iff $A'/M'$ is
    algebraic over $k$, i.e.\ iff the residue field of $R'$ is algebraic over $k$ (p.~210).

    \textbf{Gap in the paper filled.} The paper only says ``Then we see that''; Lean proves the
    last equivalence by Zariski's lemma (a field which is an algebra of finite type over $k$ is
    finite over $k$; conversely a domain algebraic over a field is a field). -/)
  (latexEnv := "lemma")]
theorem MonoidalTransform.ringKrullDim_eq_iff (t : MonoidalTransform R P) (hP : P.IsPrime)
    (hP0 : P ≠ ⊥) (hS : IsRegularLocalRing (R ⧸ P)) :
    ringKrullDim t.ring = ringKrullDim R ↔
      RingHom.IsResiduallyAlgebraic (R := R) (R' := t.ring) t.toRing :=
  (t.ringKrullDim_eq_iff_isMaximal hP hP0 hS).trans t.isMaximal_iff_isResiduallyAlgebraic

/-- p. 210, the two printed facts together, for `P` prime with `R/P` regular: `M'` is a maximal ideal of
`A'` iff `dim R' = dim R` ("It follows that, for `M'` and `R'` as above, `dim R' = dim R` if and only if
`M'` is a maximal ideal in `A'`", `ringKrullDim_eq_iff_isMaximal`) iff the residue field of `R'` is algebraic
over that of `R` ("Then we see that …", `ringKrullDim_eq_iff`).  This is the form in which Lemma 8
(p. 217) uses "`N` the maximal ideal in `A'` such that `R' = A'_N`" for a residually algebraic `R'`. -/
theorem MonoidalTransform.isMaximal_iff_isResiduallyAlgebraic_of_isRegular (t : MonoidalTransform R P)
    (hP : P.IsPrime) (hP0 : P ≠ ⊥) (hS : IsRegularLocalRing (R ⧸ P)) :
    t.M'.IsMaximal ↔ RingHom.IsResiduallyAlgebraic (R := R) (R' := t.ring) t.toRing :=
  (t.ringKrullDim_eq_iff_isMaximal hP hP0 hS).symm.trans (t.ringKrullDim_eq_iff hP hP0 hS)

/-- p. 210: "(necessarily, of finite degree)": if `dim R' = dim R`, the residue field of `R'` is a
finite extension of that of `R`.  Gap in the paper filled: by `ringKrullDim_eq_iff_isMaximal`, `M'` is
a maximal ideal of `A'`, and then the residue field of `R'` is `A'/M'`, a field of finite type over
`k`, hence finite over `k` (Zariski's lemma, `finite_residueField_of_isMaximal`). -/
@[blueprint "lem:III.2-dim-finite"
  (statement := /-- With the notation of \cref{lem:III.2-dim}, if $\dim R=\dim R'$ then the
    residue field of $R'$ is a finite extension of that of $R$. (The parenthetical ``(necessarily,
    of finite degree)'' of p.~210.) -/)
  (proof := /-- Not argued in the paper. By \cref{lem:III.2-dim-maximal}, $M'$ is a maximal ideal
    of $A'$; the residue field of $R'$ is then $A'/M'$, a field which is a $k$-algebra of finite
    type, hence finite over $k$ (Zariski's lemma). -/)
  (latexEnv := "lemma")]
theorem MonoidalTransform.finite_residueField_of_ringKrullDim_eq (t : MonoidalTransform R P)
    (hP : P.IsPrime) (hP0 : P ≠ ⊥) (hS : IsRegularLocalRing (R ⧸ P))
    (h : ringKrullDim t.ring = ringKrullDim R) :
    letI := (ResidueField.map t.toRing).toAlgebra
    Module.Finite (ResidueField R) (ResidueField t.ring) :=
  t.finite_residueField_of_isMaximal ((t.ringKrullDim_eq_iff_isMaximal hP hP0 hS).mp h)

open Classical MvPolynomial in
/-- The images of the variables are a regular system of parameters of the localization of
`k[X₁, …, X_r]` at the maximal ideal `(X₁, …, X_r)` (p. 210: "images … form a regular system of
parameters of `k[X₂, …, X_r]_{m̄'}`", here for `m̄' = (X₂, …, X_r)`). -/
private theorem isRegularSystemOfParameters_localization_span_X {k : Type u} [Field k] {r : ℕ}
    (m : Ideal (MvPolynomial (Fin r) k)) [m.IsPrime] (hm : m = Ideal.span (Set.range X)) :
    IsRegularSystemOfParameters (Localization.AtPrime m)
        (Finset.image (fun i : Fin r => algebraMap (MvPolynomial (Fin r) k) (Localization.AtPrime m)
          (X i)) Finset.univ) ∧
      (Finset.image (fun i : Fin r => algebraMap (MvPolynomial (Fin r) k) (Localization.AtPrime m)
          (X i)) Finset.univ).card = r := by
  have hmax : m.IsMaximal := by
    have hker : m = RingHom.ker (eval₂Hom (RingHom.id k) (0 : Fin r → k)) := by
      apply le_antisymm
      · rw [hm, Ideal.span_le]
        rintro _ ⟨i, rfl⟩
        simp
      · intro G hG
        rw [RingHom.mem_ker, eval₂Hom_zero_apply] at hG
        have := sub_C_constantCoeff_mem_span_X G
        rw [show constantCoeff G = 0 from hG, map_zero, sub_zero] at this
        rw [hm]
        exact this
    rw [hker]
    exact RingHom.ker_isMaximal_of_surjective _ fun a => ⟨C a, by simp⟩
  have hht : m.height = r := (height_eq_iff_isMaximal_of_isField k (Field.toIsField k) r m).mpr hmax
  set G := Finset.image (fun i : Fin r => algebraMap (MvPolynomial (Fin r) k)
    (Localization.AtPrime m) (X i)) Finset.univ with hG
  have hspan : Ideal.span (G : Set (Localization.AtPrime m)) = maximalIdeal (Localization.AtPrime m) := by
    rw [← IsLocalization.AtPrime.map_eq_maximalIdeal m (Localization.AtPrime m)]
    calc Ideal.span (G : Set (Localization.AtPrime m))
        = Ideal.map (algebraMap (MvPolynomial (Fin r) k) (Localization.AtPrime m))
            (Ideal.span (Set.range (X : Fin r → MvPolynomial (Fin r) k))) := by
          rw [Ideal.map_span, hG, Finset.coe_image, Finset.coe_univ, Set.image_univ,
            ← Set.range_comp]
          rfl
      _ = Ideal.map (algebraMap (MvPolynomial (Fin r) k) (Localization.AtPrime m)) m :=
          congrArg (Ideal.map (algebraMap (MvPolynomial (Fin r) k) (Localization.AtPrime m))) hm.symm
  have hdim : ringKrullDim (Localization.AtPrime m) = (r : WithBot ℕ∞) := by
    rw [IsLocalization.AtPrime.ringKrullDim_eq_height m (Localization.AtPrime m), hht]
    rfl
  have hle : G.card ≤ r := by
    have := Finset.card_image_le (s := (Finset.univ : Finset (Fin r)))
      (f := fun i : Fin r => algebraMap (MvPolynomial (Fin r) k) (Localization.AtPrime m) (X i))
    simpa using this
  have hge : (r : WithBot ℕ∞) ≤ G.card := by
    rw [← hdim]
    refine (ringKrullDim_le_spanFinrank_maximalIdeal (Localization.AtPrime m)).trans ?_
    rw [← hspan]
    have := Submodule.spanFinrank_span_le_ncard_of_finite (R := Localization.AtPrime m)
      G.finite_toSet
    rw [Set.ncard_coe_finset] at this
    exact_mod_cast this
  have hcard : G.card = r := le_antisymm hle (by exact_mod_cast hge)
  exact ⟨⟨hspan, by rw [hcard, hdim]⟩, hcard⟩

open Classical MvPolynomial in
/-- p. 210: the regular system of parameters `(x, x₁/x − c₁, …, x_r/x − c_r, y₁, …, y_s)` of a
residually rational monoidal transform. -/
private theorem MonoidalTransform.exists_isRegularSystemOfParameters_split_of_isResiduallyRational (t : MonoidalTransform R P) [P.IsPrime]
    (hS : IsRegularLocalRing (R ⧸ P))
    (hrat : RingHom.IsResiduallyRational (R := R) (R' := t.ring) t.toRing) :
    ∃ (r s : ℕ) (x₀ : R) (x : Fin r → R) (y : Fin s → R),
      IsRegularSystemOfParameters R
        ({x₀} ∪ Finset.image x Finset.univ ∪ Finset.image y Finset.univ) ∧
      ({x₀} ∪ Finset.image x Finset.univ ∪ Finset.image y Finset.univ).card = r + 1 + s ∧
      P = Ideal.span ({x₀} ∪ Set.range x) ∧
      ∃ x' : Fin r → t.ring, (∀ i, t.toRing x₀ * x' i = t.toRing (x i)) ∧
        IsRegularSystemOfParameters t.ring
          ({t.toRing x₀} ∪ Finset.image x' Finset.univ ∪
            Finset.image (fun j => t.toRing (y j)) Finset.univ) := by
  have hreg : IsRegularLocalRing t.ring := MonoidalTransform.isRegularLocalRing_of_isRegularLocalRing_quotient t hS
  obtain ⟨S, r, z, hSM, hScard, hinj, hzS, hz0, hzP⟩ := t.exists_minimal_generators hS
  have hPM : P ≤ maximalIdeal R := IsLocalRing.le_maximalIdeal (Ideal.IsPrime.ne_top ‹_›)
  have hzM : ∀ i, z i ∈ maximalIdeal R := fun i => hPM (hzP ▸ Ideal.subset_span ⟨i, rfl⟩)
  have hxM : t.x ∈ maximalIdeal R := hPM t.x_mem
  -- `uᵢ = zᵢ/x ∈ R'`, congruent to some `cᵢ ∈ R` modulo `M'`
  have hu : ∀ i : Fin r, ∃ u : t.ring, t.toRing t.x * u = t.toRing (z i.succ) := fun i =>
    MonoidalTransform.exists_toRing_x_mul_eq_of_mem t (hzP ▸ Ideal.subset_span ⟨i.succ, rfl⟩)
  choose u hu using hu
  have hc : ∀ i, ∃ c : R, u i - t.toRing c ∈ maximalIdeal t.ring := by
    intro i
    obtain ⟨w, hw⟩ := hrat (IsLocalRing.residue t.ring (u i))
    obtain ⟨c, rfl⟩ := IsLocalRing.residue_surjective w
    refine ⟨c, ?_⟩
    rw [← IsLocalRing.residue_eq_zero_iff, map_sub, ← hw, IsLocalRing.ResidueField.map_residue,
      sub_self]
  choose c hc using hc
  -- the new parameters
  let x : Fin r → R := fun i => z i.succ - c i * t.x
  let x' : Fin r → t.ring := fun i => u i - t.toRing (c i)
  have hx' : ∀ i, t.toRing t.x * x' i = t.toRing (x i) := by
    intro i
    simp only [x, x', mul_sub, hu i, map_sub, map_mul]
    ring
  let Y : Finset R := S \ Finset.image z Finset.univ
  let eY := Y.equivFin
  let y : Fin Y.card → R := fun j => (eY.symm j : R)
  have hyS : ∀ j, y j ∈ S := fun j => (Finset.mem_sdiff.mp (eY.symm j).2).1
  set F : Finset R := {t.x} ∪ Finset.image x Finset.univ ∪ Finset.image y Finset.univ with hF
  have hzsucc : ∀ i : Fin r, z i.succ = x i + c i * t.x := fun i => by simp [x]
  have hxF : t.x ∈ F := by simp [hF]
  have hxiF : ∀ i, x i ∈ F := fun i => by simp [hF]
  have hyF : ∀ j, y j ∈ F := fun j => by simp [hF]
  -- `F` is a regular system of parameters of `R`
  have hFM : Ideal.span (F : Set R) = maximalIdeal R := by
    apply le_antisymm
    · rw [Ideal.span_le]
      intro a ha
      simp only [hF, Finset.coe_union, Finset.coe_singleton, Finset.coe_image, Finset.coe_univ,
        Set.image_univ, Set.mem_union, Set.mem_singleton_iff, Set.mem_range] at ha
      rcases ha with (rfl | ⟨i, rfl⟩) | ⟨j, rfl⟩
      · exact hxM
      · exact sub_mem (hzM _) (Ideal.mul_mem_left _ _ hxM)
      · exact hSM ▸ Ideal.subset_span (hyS j)
    · rw [← hSM, Ideal.span_le]
      intro a ha
      by_cases haz : a ∈ Finset.image z Finset.univ
      · obtain ⟨k, -, rfl⟩ := Finset.mem_image.mp haz
        refine Fin.cases ?_ (fun i => ?_) k
        · rw [hz0]
          exact Ideal.subset_span hxF
        · rw [hzsucc]
          exact add_mem (Ideal.subset_span (hxiF i))
            (Ideal.mul_mem_left _ _ (Ideal.subset_span hxF))
      · have haY : a ∈ Y := Finset.mem_sdiff.mpr ⟨ha, haz⟩
        have : a = y (eY ⟨a, haY⟩) := by simp [y]
        rw [this]
        exact Ideal.subset_span (hyF _)
  have hcardS : S.card = r + 1 + Y.card := by
    have h1 : (Finset.image z Finset.univ).card = r + 1 := by
      rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]
    have h2 : Finset.image z Finset.univ ⊆ S := fun a ha => by
      obtain ⟨k, -, rfl⟩ := Finset.mem_image.mp ha
      exact hzS k
    have := Finset.card_sdiff_add_card_eq_card h2
    have hY : Y.card = (S \ Finset.image z Finset.univ).card := rfl
    omega
  have hxle : ({t.x} ∪ Finset.image x Finset.univ : Finset R).card ≤ r + 1 := by
    refine (Finset.card_union_le _ _).trans ?_
    have := Finset.card_image_le (s := (Finset.univ : Finset (Fin r))) (f := x)
    simp only [Finset.card_singleton, Finset.card_univ, Fintype.card_fin] at this ⊢
    omega
  have hyle : (Finset.image y Finset.univ).card ≤ Y.card := by
    have := Finset.card_image_le (s := (Finset.univ : Finset (Fin Y.card))) (f := y)
    simpa using this
  have hFle : F.card ≤ r + 1 + Y.card :=
    (Finset.card_union_le _ _).trans (by omega)
  have hFge : (maximalIdeal R).spanFinrank ≤ F.card := by
    rw [← hFM]
    exact (Submodule.spanFinrank_span_le_ncard_of_finite (Finset.finite_toSet F)).trans
      (Set.ncard_coe_finset F).le
  have hFcard : F.card = r + 1 + Y.card := by omega
  have hFcard' : F.card = (maximalIdeal R).spanFinrank := by omega
  -- `P = (x, x₁, …, x_r)`
  have hPx : P = Ideal.span ({t.x} ∪ Set.range x) := by
    apply le_antisymm
    · refine (le_of_eq hzP.symm).trans (Ideal.span_le.mpr ?_)
      rintro _ ⟨k, rfl⟩
      refine Fin.cases ?_ (fun i => ?_) k
      · rw [hz0]
        exact Ideal.subset_span (Or.inl rfl)
      · rw [hzsucc]
        exact add_mem (Ideal.subset_span (Or.inr ⟨i, rfl⟩))
          (Ideal.mul_mem_left _ _ (Ideal.subset_span (Or.inl rfl)))
    · rw [Ideal.span_le]
      rintro _ (h | ⟨i, rfl⟩)
      · rw [Set.mem_singleton_iff.mp h]
        exact t.x_mem
      · exact sub_mem (hzP ▸ Ideal.subset_span ⟨i.succ, rfl⟩) (Ideal.mul_mem_left _ _ t.x_mem)
  -- the new system `z' = (x, x₁, …, x_r)`
  let z' : Fin (r + 1) → R := Fin.cons t.x x
  have hxcard : ({t.x} ∪ Finset.image x Finset.univ : Finset R).card = r + 1 := by
    have : F.card ≤ ({t.x} ∪ Finset.image x Finset.univ : Finset R).card +
        (Finset.image y Finset.univ).card := Finset.card_union_le _ _
    omega
  have hxinj : Function.Injective x := by
    have h1 := Finset.card_union_le ({t.x} : Finset R) (Finset.image x Finset.univ)
    have h2 : (Finset.image x Finset.univ).card = (Finset.univ : Finset (Fin r)).card := by
      have := Finset.card_image_le (s := (Finset.univ : Finset (Fin r))) (f := x)
      simp only [Finset.card_singleton, Finset.card_univ, Fintype.card_fin] at h1 this ⊢
      omega
    intro i j hij
    exact (Finset.card_image_iff.mp h2) (Finset.mem_coe.mpr (Finset.mem_univ i))
      (Finset.mem_coe.mpr (Finset.mem_univ j)) hij
  have hxnot : t.x ∉ Set.range x := by
    rintro ⟨i, hi⟩
    have : ({t.x} ∪ Finset.image x Finset.univ : Finset R) = Finset.image x Finset.univ := by
      rw [Finset.union_eq_right, Finset.singleton_subset_iff, ← hi]
      exact Finset.mem_image_of_mem _ (Finset.mem_univ i)
    have h2 := Finset.card_image_le (s := (Finset.univ : Finset (Fin r))) (f := x)
    rw [this] at hxcard
    simp only [Finset.card_univ, Fintype.card_fin] at h2
    omega
  have hz'inj : Function.Injective z' := Fin.cons_injective_iff.mpr ⟨hxnot, hxinj⟩
  have hz'F : ∀ i, z' i ∈ F := fun i => Fin.cases (by simpa [z'] using hxF)
    (fun i => by simpa [z'] using hxiF i) i
  have hz'P : Ideal.span (Set.range z') = P := by
    rw [Fin.range_cons, Set.insert_eq]
    exact hPx.symm
  -- the chart `χ : A' → S[X₂, …, X_r]` (p. 209–210) for the new minimal base `z' = (x, x₁, …, x_r)`
  obtain ⟨χ, hχ, hχx, hχC, hχX⟩ :=
    t.exists_chart hFM hFcard' hz'inj hz'F (Fin.cons_zero _ _) hz'P
  obtain ⟨q, hq, e, hqdef, hχq, hqC, -, -⟩ :=
    t.exists_quotient_equiv_localization_of_chart hS χ hχ hχx hχC
  -- the elements `fᵢ = xᵢ/x ∈ A'`, with `χ(fᵢ) = Tᵢ`, whose images in `R'` are the `x' i`
  have hxP : ∀ i, x i ∈ P := fun i => hPx ▸ Ideal.subset_span (Or.inr ⟨i, rfl⟩)
  have hzA : ∀ i : Fin r, algebraMap R (FractionRing R) (x i) / algebraMap R (FractionRing R) t.x ∈
      blowupAlgebra R P t.x := fun i => Algebra.subset_adjoin ⟨x i, hxP i, rfl⟩
  let f : Fin r → blowupAlgebra R P t.x := fun i => ⟨_, hzA i⟩
  have hχf : ∀ i, χ (f i) = X i := fun i => hχX i (f i) (by simp [z', f])
  have hX0 : t.toRing t.x ≠ 0 := fun h =>
    t.x_ne_zero (MonoidalTransform.toRing_injective t (h.trans (map_zero _).symm))
  have hfx : ∀ i, algebraMap (blowupAlgebra R P t.x) t.ring (f i) = x' i := by
    intro i
    have hxne : algebraMap R (FractionRing R) t.x ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective R (FractionRing R))).mpr t.x_ne_zero
    have h1 : t.toRing t.x * algebraMap (blowupAlgebra R P t.x) t.ring (f i) = t.toRing (x i) := by
      show (algebraMap (blowupAlgebra R P t.x) t.ring) (algebraMap R _ t.x) * _ =
        (algebraMap (blowupAlgebra R P t.x) t.ring) (algebraMap R _ (x i))
      rw [← map_mul]
      congr 1
      apply Subtype.ext
      simp only [MulMemClass.coe_mul, Subalgebra.coe_algebraMap, f]
      field_simp
    exact mul_left_cancel₀ hX0 (h1.trans (hx' i).symm)
  have hfM : ∀ i, f i ∈ t.M' := fun i =>
    (IsLocalization.AtPrime.to_map_mem_maximal_iff t.ring t.M' _).mp (by rw [hfx]; exact hc i)
  have hXq : ∀ i, (X i : MvPolynomial (Fin r) (R ⧸ P)) ∈ q := fun i => by
    have := (hχq (f i)).mpr (hfM i)
    rwa [hχf] at this
  -- `q` is the ideal `(M_S, T₁, …, T_r)` of `S[T]`, `S = R/P`
  set K := RingHom.ker (eval₂Hom (IsLocalRing.residue (R ⧸ P)) (0 : Fin r → ResidueField (R ⧸ P)))
    with hKdef
  have hKsplit : ∀ G ∈ K, constantCoeff G ∈ maximalIdeal (R ⧸ P) ∧
      G - C (constantCoeff G) ∈
        Ideal.span (Set.range (X : Fin r → MvPolynomial (Fin r) (R ⧸ P))) := by
    intro G hG
    rw [hKdef, RingHom.mem_ker, eval₂Hom_zero_apply, IsLocalRing.residue_eq_zero_iff] at hG
    exact ⟨hG, sub_C_constantCoeff_mem_span_X G⟩
  have hKq : K ≤ q := by
    intro G hG
    obtain ⟨h1, h2⟩ := hKsplit G hG
    have h1' : C (constantCoeff G) ∈ q := by
      rw [← hqC] at h1
      exact h1
    have h2' : G - C (constantCoeff G) ∈ q := by
      refine (Ideal.span_le.mpr ?_) h2
      rintro _ ⟨i, rfl⟩
      exact hXq i
    simpa using add_mem h2' h1'
  have hKmax : K.IsMaximal := by
    refine RingHom.ker_isMaximal_of_surjective _ fun w => ?_
    obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective w
    exact ⟨C a, by simp⟩
  have hKq' : K = q := hKmax.eq_of_le hq.ne_top hKq
  -- `m̄' = M̄'/M̄S[X] = (X₂, …, X_r)` in `k[X₂, …, X_r]`, `k = S/M̄`
  set ρ : MvPolynomial (Fin r) (R ⧸ P) →+* MvPolynomial (Fin r) (ResidueField (R ⧸ P)) :=
    MvPolynomial.map (IsLocalRing.residue (R ⧸ P)) with hρdef
  have hρsurj : Function.Surjective ρ :=
    MvPolynomial.map_surjective _ IsLocalRing.residue_surjective
  have hρq : RingHom.ker ρ ≤ q := by
    rw [hρdef, MvPolynomial.ker_map, IsLocalRing.ker_residue]
    exact Ideal.map_le_iff_le_comap.mpr hqC.ge
  have hmprime : (q.map ρ).IsPrime := Ideal.map_isPrime_of_surjective hρsurj hρq
  have hm' : q.map ρ = Ideal.span (Set.range (X : Fin r → MvPolynomial (Fin r)
      (ResidueField (R ⧸ P)))) := by
    apply le_antisymm
    · rw [Ideal.map_le_iff_le_comap, ← hKq']
      intro G hG
      obtain ⟨h1, h2⟩ := hKsplit G hG
      rw [Ideal.mem_comap]
      have hc0 : ρ (C (constantCoeff G)) = 0 := by
        rw [hρdef, MvPolynomial.map_C, (IsLocalRing.residue_eq_zero_iff _).mpr h1, map_zero]
      have h3 : ρ (G - C (constantCoeff G)) ∈ Ideal.span (Set.range (X : Fin r →
          MvPolynomial (Fin r) (ResidueField (R ⧸ P)))) := by
        have h4 := Ideal.mem_map_of_mem ρ h2
        rw [Ideal.map_span, ← Set.range_comp] at h4
        refine (Ideal.span_le.mpr ?_) h4
        rintro _ ⟨i, rfl⟩
        exact Ideal.subset_span ⟨i, by simp [hρdef]⟩
      have : G = (G - C (constantCoeff G)) + C (constantCoeff G) := by ring
      rw [this, map_add, hc0, add_zero]
      exact h3
    · rw [Ideal.span_le]
      rintro _ ⟨i, rfl⟩
      have := Ideal.mem_map_of_mem ρ (hXq i)
      simpa [hρdef] using this
  -- `R'/xR' ≅ S[X]_{q}` and the regular system of parameters of `R'` of p. 210
  have hdimRP : ringKrullDim (R ⧸ P) = (Y.card : WithBot ℕ∞) := by
    have h1 := ringKrullDim_eq_add_of_minimal_generators hS hFM hFcard' hz'inj hz'F hz'P
    have h2 : ringKrullDim R = ((r + 1 + Y.card : ℕ) : WithBot ℕ∞) := by
      rw [← IsRegularLocalRing.spanFinrank_maximalIdeal (R := R), ← hFcard', hFcard]
    obtain ⟨k₀, -, hk₀⟩ := exists_nat_ringKrullDim_eq
      (ringKrullDim_le_spanFinrank_maximalIdeal (R ⧸ P))
    rw [h2, hk₀] at h1
    have h3 : r + 1 + Y.card = r + 1 + k₀ := by exact_mod_cast h1
    rw [hk₀]
    have : k₀ = Y.card := by omega
    rw [this]
  have hMS : (maximalIdeal R).map (Ideal.Quotient.mk P) = maximalIdeal (R ⧸ P) :=
    IsLocalRing.map_maximalIdeal_of_surjective _ Ideal.Quotient.mk_surjective
  have hyspan : Ideal.span (Set.range fun j : Fin Y.card => Ideal.Quotient.mk P (y j)) =
      maximalIdeal (R ⧸ P) := by
    apply le_antisymm
    · rw [Ideal.span_le]
      rintro _ ⟨j, rfl⟩
      have : y j ∈ maximalIdeal R := hFM ▸ Ideal.subset_span (hyF j)
      rw [← hMS]
      exact Ideal.mem_map_of_mem _ this
    · rw [← hMS, ← hFM, Ideal.map_span, Ideal.span_le]
      rintro _ ⟨a, ha, rfl⟩
      simp only [hF, Finset.coe_union, Finset.coe_singleton, Finset.coe_image, Finset.coe_univ,
        Set.image_univ, Set.mem_union, Set.mem_singleton_iff, Set.mem_range] at ha
      rcases ha with (rfl | ⟨i, rfl⟩) | ⟨j, rfl⟩
      · rw [Ideal.Quotient.eq_zero_iff_mem.mpr t.x_mem]
        exact zero_mem _
      · rw [Ideal.Quotient.eq_zero_iff_mem.mpr (hxP i)]
        exact zero_mem _
      · exact Ideal.subset_span ⟨j, rfl⟩
  have hycard : (Finset.image (fun j : Fin Y.card => Ideal.Quotient.mk P (y j))
      Finset.univ).card = Y.card := by
    have hle : (Finset.image (fun j : Fin Y.card => Ideal.Quotient.mk P (y j))
        Finset.univ).card ≤ Y.card := by
      simpa using Finset.card_image_le (s := (Finset.univ : Finset (Fin Y.card)))
        (f := fun j : Fin Y.card => Ideal.Quotient.mk P (y j))
    have hge : (Y.card : WithBot ℕ∞) ≤ (Finset.image (fun j : Fin Y.card =>
        Ideal.Quotient.mk P (y j)) Finset.univ).card := by
      rw [← hdimRP]
      refine (ringKrullDim_le_spanFinrank_maximalIdeal (R ⧸ P)).trans ?_
      have hcoe : ((Finset.image (fun j : Fin Y.card => Ideal.Quotient.mk P (y j))
          Finset.univ : Finset (R ⧸ P)) : Set (R ⧸ P)) =
          Set.range fun j : Fin Y.card => Ideal.Quotient.mk P (y j) := by
        simp [Finset.coe_image, Set.image_univ]
      have h5 := Submodule.spanFinrank_span_le_ncard_of_finite (R := R ⧸ P)
        (Finset.image (fun j : Fin Y.card => Ideal.Quotient.mk P (y j)) Finset.univ).finite_toSet
      rw [Set.ncard_coe_finset] at h5
      rw [← hyspan, ← hcoe]
      exact_mod_cast h5
    exact le_antisymm hle (by exact_mod_cast hge)
  have hy : IsRegularSystemOfParameters (R ⧸ P)
      (Finset.image (fun j : Fin Y.card => Ideal.Quotient.mk P (y j)) Finset.univ) ∧
      (Finset.image (fun j : Fin Y.card => Ideal.Quotient.mk P (y j)) Finset.univ).card = Y.card :=
    ⟨⟨by rw [Finset.coe_image, Finset.coe_univ, Set.image_univ]; exact hyspan,
      by rw [hycard, hdimRP]⟩, hycard⟩
  obtain ⟨hlocrsop, hloccard⟩ := isRegularSystemOfParameters_localization_span_X (q.map ρ) hm'
  have hf : IsRegularSystemOfParameters (Localization.AtPrime (q.map ρ))
        (Finset.image (fun i : Fin r => algebraMap (MvPolynomial (Fin r) (ResidueField (R ⧸ P)))
          (Localization.AtPrime (q.map ρ)) (MvPolynomial.map (IsLocalRing.residue (R ⧸ P))
            (χ (f i)))) Finset.univ) ∧
      (Finset.image (fun i : Fin r => algebraMap (MvPolynomial (Fin r) (ResidueField (R ⧸ P)))
          (Localization.AtPrime (q.map ρ)) (MvPolynomial.map (IsLocalRing.residue (R ⧸ P))
            (χ (f i)))) Finset.univ).card = r := by
    have hfun : (fun i : Fin r => algebraMap (MvPolynomial (Fin r) (ResidueField (R ⧸ P)))
          (Localization.AtPrime (q.map ρ)) (MvPolynomial.map (IsLocalRing.residue (R ⧸ P))
            (χ (f i)))) = fun i : Fin r => algebraMap (MvPolynomial (Fin r)
          (ResidueField (R ⧸ P))) (Localization.AtPrime (q.map ρ)) (X i) :=
      funext fun i => by rw [hχf i, MvPolynomial.map_X]
    rw [hfun]
    exact ⟨hlocrsop, hloccard⟩
  have hmeq : q.map ρ = (t.M'.map χ).map (MvPolynomial.map (IsLocalRing.residue (R ⧸ P))) := by
    rw [hqdef]
  obtain ⟨hR', -⟩ := t.isRegularSystemOfParameters_xR_y_f ‹P.IsPrime› hS χ hχ hχx hχC (q.map ρ)
    hmeq y f hfM hy hf
  have hx'f : (fun i : Fin r => algebraMap (blowupAlgebra R P t.x) t.ring (f i)) = x' :=
    funext hfx
  refine ⟨r, Y.card, t.x, x, y, ⟨hFM, ?_⟩, hFcard, hPx, x', hx', ?_⟩
  · rw [hFcard', IsRegularLocalRing.spanFinrank_maximalIdeal]
  · rw [hx'f] at hR'
    have hset : ({t.xR} ∪ Finset.image (fun j => t.toRing (y j)) Finset.univ ∪
        Finset.image x' Finset.univ : Finset t.ring) =
        {t.toRing t.x} ∪ Finset.image x' Finset.univ ∪
          Finset.image (fun j => t.toRing (y j)) Finset.univ := by
      rw [Finset.union_right_comm]
      rfl
    rw [hset] at hR'
    exact hR'

open Classical in
/-- p. 210: "if `R'` is a monoidal transform of `R` with center `P` which is residually rational
over `R`, then there exists a regular system of parameters `(x₁, x₂, …, x_r, y₁, y₂, …, y_s)` of
`R`, where `r + s = dim R`, such that `P = (x₁, x₂, …, x_r)R` and that
`(x₁, x₂/x₁, …, x_r/x₁, y₁, …, y_s)` is a regular system of parameters of `R'`."

Formalization note (encoding): the distinguished element `x₁` is `x₀ : R`, the remaining
`x₂, …, x_r` are `x : Fin r → R` (so the paper's `r` is our `r + 1`), and `y : Fin s → R`; the
quotients `x_i/x₁` are elements `x' i` of `R'` with `x₁ · x' i = x_i` (unique, `R'` being a
domain); "`r + s = dim R`" is the requirement that the listed elements be pairwise distinct
(the finset has `r + 1 + s` elements), its cardinality being `dim R` by
\cref{def:rsop}.

Proof as printed ("By the above argument", p. 210): residual rationality means that the residue field
`k'` of `R'` is `k`, so the prime `m̄'` of `k[X₂, …, X_r]` is the maximal ideal `(X₂ − c₂, …, X_r − c_r)`
with `cᵢ ∈ k`; lifting `cᵢ` to `R` and replacing `xᵢ` by `xᵢ − cᵢx₁` one has `m̄' = (X₂, …, X_r)`, the
elements `fᵢ = xᵢ/x₁ ∈ M'` have images `Xᵢ`, which form a regular system of parameters of
`k[X₂, …, X_r]_{m̄'}` (`isRegularSystemOfParameters_localization_span_X`), and
`(x₁, y₁, …, y_s, f₂, …, f_r)` is a regular system of parameters of `R'`
(`isRegularSystemOfParameters_xR_y_f`, p. 210: "Then we can easily see that …").

Gap filled ("By the above argument, we can easily show"): the lifting of the residues, the
replacement of the `xᵢ` (the new `x₁, …, x_r` are again a minimal base of `P` which extends to a
regular system of parameters of `R`), the choice `m̄' = (X₂, …, X_r)` and the regular system of
parameters of its localization.  The conclusion is the regular system of parameters itself, not merely a
dimension count (`dim R' ≥ r + 1 + s` and `M'` generated by `r + 1 + s` elements). -/
@[blueprint "lem:III.2-residually-rational-rsop"
  (statement := /-- Let $R'$ be a monoidal transform of $R$ with center $P$ as in
    \cref{lem:III.2-monoidal-transform-regular} which is residually rational over $R$
    (\cref{def:III.2-residually}). Then there exists a regular system of parameters
    $(x_1,x_2,\dots,x_r,y_1,\dots,y_s)$ of $R$, where $r+s=\dim R$, such that
    $P=(x_1,\dots,x_r)R$ and $(x_1,x_2/x_1,\dots,x_r/x_1,y_1,\dots,y_s)$ is a regular system
    of parameters of $R'$. (p.~210.) (Formalization note (encoding): $x_1$ is listed
    separately from $x_2,\dots,x_r$, and $x_i/x_1$ is the element $x_i'$ of $R'$ with
    $x_1x_i'=x_i$.) -/)
  (proof := /-- The paper only says ``By the above argument, we can easily show'' (p.~210).
    The intended argument: with the notation of
    \cref{lem:III.2-dim}, residual rationality means that the residue field of $R'$ is $k$,
    so $\bar m'$ is the maximal
    ideal $(X_2-a_2,\dots,X_r-a_r)$ of $k[X_2,\dots,X_r]$ for some $a_i\in k$; lifting $a_i$ to
    $R$ and replacing $x_i$ by $x_i-a_ix_1$ one may assume $\bar m'=(X_2,\dots,X_r)$, and then
    $f_i=x_i/x_1$ in the regular system of parameters
    $(x_1,y_1,\dots,y_s,f_2,\dots,f_r)$ of $R'$.

    \textbf{In Lean} (the printed route): the same replacement
    $x_i\mapsto x_i-c_ix_1$, the chart $A'/(x_1)A'\cong S[X_2,\dots,X_r]$ for the new minimal base,
    the prime $\bar m'=(X_2,\dots,X_r)$ of $k[X_2,\dots,X_r]$ with the regular system of parameters
    $(X_2,\dots,X_r)$ of its localization, and then the regular system of parameters
    $(x_1,y_1,\dots,y_s,f_2,\dots,f_r)$ of $R'$ of \cref{lem:III.2-dim-rsop}, $f_i=x_i/x_1$.

    \textbf{Gap in the paper filled.} The lifting of the residues, the replacement of the $x_i$, and
    $\bar m'=(X_2,\dots,X_r)$ with its regular system of parameters. -/)
  (latexEnv := "lemma")]
theorem MonoidalTransform.exists_rsop_of_isResiduallyRational (t : MonoidalTransform R P)
    (hP : P.IsPrime) (hP0 : P ≠ ⊥) (hS : IsRegularLocalRing (R ⧸ P))
    (hrat : RingHom.IsResiduallyRational (R := R) (R' := t.ring) t.toRing) :
    ∃ (r s : ℕ) (x₀ : R) (x : Fin r → R) (y : Fin s → R),
      IsRegularSystemOfParameters R
        ({x₀} ∪ Finset.image x Finset.univ ∪ Finset.image y Finset.univ) ∧
      ({x₀} ∪ Finset.image x Finset.univ ∪ Finset.image y Finset.univ).card = r + 1 + s ∧
      P = Ideal.span ({x₀} ∪ Set.range x) ∧
      ∃ x' : Fin r → t.ring, (∀ i, t.toRing x₀ * x' i = t.toRing (x i)) ∧
        IsRegularSystemOfParameters t.ring
          ({t.toRing x₀} ∪ Finset.image x' Finset.univ ∪
            Finset.image (fun j => t.toRing (y j)) Finset.univ) := by
  -- (`P ≠ (0)` is automatic: `P` contains the non-zero element `x`)
  have _ := hP0
  have := hP
  exact MonoidalTransform.exists_isRegularSystemOfParameters_split_of_isResiduallyRational t hS hrat

open MvPolynomial in
/-- Dehomogenization: the non-zero coefficients of a form `F(X₀, …, X_r)` of degree `m` are
coefficients of `F(1, X₁, …, X_r)`. -/
private theorem coeff_eq_coeff_eval_one_finSuccEquiv {S : Type*} [CommRing S] {r m : ℕ}
    {F : MvPolynomial (Fin (r + 1)) S} (hF : F.IsHomogeneous m) (α : Fin (r + 1) →₀ ℕ)
    (hα : F.coeff α ≠ 0) :
    F.coeff α = (Polynomial.eval 1 (finSuccEquiv S r F)).coeff (Finsupp.tail α) := by
  have hdeg : ∀ d, F.coeff d ≠ 0 → (∑ i, d i) = m := fun d hd => by
    have h1 := hF hd
    have h2 : Finsupp.degree d = m := by
      rw [Finsupp.degree_eq_weight_one]
      exact h1
    rwa [Finsupp.degree_eq_sum] at h2
  set p := finSuccEquiv S r F with hp
  rw [Polynomial.eval_eq_sum, Polynomial.sum_def, MvPolynomial.coeff_sum]
  simp only [one_pow, mul_one]
  rw [Finset.sum_eq_single (α 0)]
  · rw [hp, finSuccEquiv_coeff_coeff, Finsupp.cons_tail]
  · intro k _ hk
    rw [hp, finSuccEquiv_coeff_coeff]
    by_contra h
    have h1 := hdeg _ h
    have h2 := hdeg α hα
    rw [Fin.sum_univ_succ, Finsupp.cons_zero] at h1
    rw [Fin.sum_univ_succ] at h2
    simp only [Finsupp.cons_succ, Finsupp.tail_apply] at h1
    omega
  · intro h
    exfalso
    apply hα
    rw [Polynomial.mem_support_iff, not_not] at h
    rw [← Finsupp.cons_tail α, ← finSuccEquiv_coeff_coeff, ← hp, h]
    simp

open MvPolynomial in
/-- `F(1, u₁, …, u_r)` computed through `finSuccEquiv`. -/
private theorem aeval_cons_one_eq_aeval_eval_one_finSuccEquiv {S A : Type*} [CommRing S] [CommRing A] [Algebra S A]
    {r : ℕ} (u : Fin r → A) (F : MvPolynomial (Fin (r + 1)) S) :
    aeval (Fin.cons 1 u : Fin (r + 1) → A) F =
      aeval u (Polynomial.eval 1 (finSuccEquiv S r F)) := by
  induction F using MvPolynomial.induction_on with
  | C a =>
    rw [finSuccEquiv_apply, coe_eval₂Hom, eval₂_C, RingHom.comp_apply, Polynomial.eval_C,
      aeval_C, aeval_C]
  | add p q hp hq => rw [map_add, map_add, Polynomial.eval_add, map_add, hp, hq]
  | mul_X p i hp =>
    rw [map_mul, map_mul, Polynomial.eval_mul, map_mul, hp]
    congr 1
    refine Fin.cases ?_ (fun k => ?_) i
    · simp [finSuccEquiv_X_zero]
    · simp [finSuccEquiv_X_succ]

open MvPolynomial in
/-- One step of `xᵏR' ∩ R = Pᵏ`: if `f ∈ Pᵐ` and `f ∈ x^{m+1}R'`, then `f ∈ P^{m+1}`.  Write
`f = F(x, z₁, …, z_r)` with `F` a form of degree `m`; then `f/xᵐ = F(1, z₁/x, …, z_r/x)`, whose
class in `R'/xR' = (R/P)[T]_{M̄'}` is the dehomogenized form `F̄(1, T)`; it vanishes, so all
coefficients of `F` lie in `P`. -/
private theorem MonoidalTransform.mem_pow_succ_of_toRing_mem_pow_succ (t : MonoidalTransform R P) [P.IsPrime]
    (hS : IsRegularLocalRing (R ⧸ P)) {m : ℕ} {f : R} (hfm : f ∈ P ^ m)
    (hf : t.toRing f ∈ Ideal.span {t.xR} ^ (m + 1)) : f ∈ P ^ (m + 1) := by
  classical
  obtain ⟨S, r, z, hSM, hScard, hinj, hzS, hz0, hzP⟩ := t.exists_minimal_generators hS
  obtain ⟨q, hq, e, -, -, hC, hX⟩ :=
    t.exists_quotient_equiv_localization hS hSM hScard hinj hzS hz0 hzP
  have hu : ∀ i : Fin r, ∃ v, t.toRing t.x * v = t.toRing (z i.succ) := fun i =>
    MonoidalTransform.exists_toRing_x_mul_eq_of_mem t (hzP ▸ Ideal.subset_span ⟨i.succ, rfl⟩)
  choose u hu using hu
  have hXu := hX u hu
  obtain ⟨F, hFhom, rfl⟩ :=
    (Ideal.mem_span_pow_iff_exists_isHomogeneous z f).mp (by rw [hzP]; exact hfm)
  let _ : Algebra R t.ring := t.toRing.toAlgebra
  set G := Polynomial.eval 1 (finSuccEquiv R r F) with hG
  have hw : (fun j => t.toRing (z j)) =
      fun j => (Fin.cons 1 u : Fin (r + 1) → t.ring) j * t.xR := by
    funext j
    refine Fin.cases ?_ (fun i => ?_) j
    · simp only [Fin.cons_zero, one_mul, hz0]
      rfl
    · simp only [Fin.cons_succ]
      rw [← hu i, mul_comm]
      rfl
  have hfG : t.toRing (eval z F) = t.xR ^ m * aeval u G := by
    have h1 : t.toRing (eval z F) = aeval (fun j => t.toRing (z j)) F := by
      rw [aeval_def, MvPolynomial.eval, MvPolynomial.coe_eval₂Hom,
        MvPolynomial.eval₂_comp_left]
      rfl
    rw [h1, hw, MvPolynomial.IsHomogeneous.aeval_mul_const hFhom, aeval_cons_one_eq_aeval_eval_one_finSuccEquiv]
  have hx0 : t.xR ≠ 0 := fun h =>
    t.x_ne_zero (t.toRing_injective (h.trans (map_zero _).symm))
  -- `F(1, u) ∈ xR'`
  have hGx : aeval u G ∈ Ideal.span {t.xR} := by
    rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton'] at hf
    obtain ⟨c, hc⟩ := hf
    rw [hfG, pow_succ] at hc
    have : aeval u G = c * t.xR := by
      apply mul_left_cancel₀ (pow_ne_zero m hx0)
      rw [← hc]; ring
    rw [this]
    exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)
  -- its class is the image of `F̄(1, T)`
  have hψ : (Ideal.Quotient.mk (Ideal.span {t.xR})).comp (aeval u : MvPolynomial (Fin r) R →ₐ[R]
      t.ring).toRingHom = e.toRingHom.comp ((algebraMap (MvPolynomial (Fin r) (R ⧸ P))
        (Localization.AtPrime q)).comp (MvPolynomial.map (Ideal.Quotient.mk P))) := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, aeval_C,
        MvPolynomial.map_C, RingEquiv.toRingHom_eq_coe]
      rw [hC c]
      rfl
    · intro i
      simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, aeval_X,
        MvPolynomial.map_X, RingEquiv.toRingHom_eq_coe]
      rw [(hXu i).2]
  have hzero : algebraMap (MvPolynomial (Fin r) (R ⧸ P)) (Localization.AtPrime q)
      (MvPolynomial.map (Ideal.Quotient.mk P) G) = 0 := by
    have h1 := RingHom.congr_fun hψ G
    simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
      RingEquiv.toRingHom_eq_coe, Ideal.Quotient.eq_zero_iff_mem.mpr hGx] at h1
    exact (map_eq_zero_iff e e.injective).mp h1.symm
  have hG0 : MvPolynomial.map (Ideal.Quotient.mk P) G = 0 := by
    have : IsDomain (R ⧸ P) := Ideal.Quotient.isDomain P
    refine IsLocalization.injective (M := q.primeCompl) (Localization.AtPrime q)
      (Ideal.primeCompl_le_nonZeroDivisors q) ?_
    rw [hzero, map_zero]
  have hGc : ∀ β, G.coeff β ∈ P := fun β => by
    have := congrArg (fun p : MvPolynomial (Fin r) (R ⧸ P) => p.coeff β) hG0
    simpa [MvPolynomial.coeff_map, Ideal.Quotient.eq_zero_iff_mem] using this
  have hFc : ∀ α, F.coeff α ∈ P := fun α => by
    by_cases hα : F.coeff α = 0
    · rw [hα]; exact zero_mem _
    · rw [coeff_eq_coeff_eval_one_finSuccEquiv hFhom α hα]
      exact hGc _
  have := eval_mem_mul_span_pow_of_coeff_mem (y := z) hFhom hFc
  rwa [hzP, ← pow_succ'] at this

/-- `xᵏR' ∩ R = Pᵏ` for a monoidal transform `R'` of `R` with center `P`, `(x)R' = PR'`: the
`P`-adic order of `f ∈ R` is the `x`-adic order of `f` in `R'` (used for Remark 4, p. 215). -/
theorem MonoidalTransform.mem_pow_of_toRing_mem (t : MonoidalTransform R P) (hP : P.IsPrime)
    (hS : IsRegularLocalRing (R ⧸ P)) {k : ℕ} {f : R}
    (hf : t.toRing f ∈ Ideal.span {t.xR} ^ k) : f ∈ P ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    have := hP
    exact MonoidalTransform.mem_pow_succ_of_toRing_mem_pow_succ t hS (ih (Ideal.pow_le_pow_right (Nat.le_succ k) hf)) hf

/-- Elements of `R[x⁻¹P]` are fractions `g/xᵐ` with `g ∈ Pᵐ`. -/
theorem MonoidalTransform.exists_mul_pow_eq_of_mem_blowupAlgebra {x : R} (hx : x ∈ P)
    (hx0 : x ≠ 0) {y : FractionRing R} (hy : y ∈ blowupAlgebra R P x) :
    ∃ (m : ℕ) (g : R), g ∈ P ^ m ∧
      y * algebraMap R (FractionRing R) x ^ m = algebraMap R (FractionRing R) g := by
  have hxK : algebraMap R (FractionRing R) x ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective R (FractionRing R))).mpr hx0
  induction hy using Algebra.adjoin_induction with
  | mem y hy =>
    obtain ⟨p, hp, rfl⟩ := hy
    exact ⟨1, p, by rwa [pow_one], by rw [pow_one, div_mul_cancel₀ _ hxK]⟩
  | algebraMap r => exact ⟨0, r, by simp, by simp⟩
  | add y y' _ _ hy hy' =>
    obtain ⟨m, g, hg, hyg⟩ := hy
    obtain ⟨m', g', hg', hyg'⟩ := hy'
    refine ⟨m + m', g * x ^ m' + g' * x ^ m, ?_, ?_⟩
    · refine Ideal.add_mem _ ?_ ?_
      · rw [pow_add]; exact Ideal.mul_mem_mul hg (Ideal.pow_mem_pow hx m')
      · rw [pow_add, mul_comm (P ^ m)]; exact Ideal.mul_mem_mul hg' (Ideal.pow_mem_pow hx m)
    · rw [map_add, map_mul, map_mul, map_pow, map_pow, ← hyg, ← hyg']
      ring
  | mul y y' _ _ hy hy' =>
    obtain ⟨m, g, hg, hyg⟩ := hy
    obtain ⟨m', g', hg', hyg'⟩ := hy'
    refine ⟨m + m', g * g', by rw [pow_add]; exact Ideal.mul_mem_mul hg hg', ?_⟩
    rw [map_mul, ← hyg, ← hyg']
    ring

/-- Every element of `IR'` has, after multiplication by a unit `u` of `R'` (the image of an
element of `R[x⁻¹P]` outside `M'`) and by a power `xᵐ`, the form `F` with `F ∈ I Pᵐ`. -/
private theorem MonoidalTransform.exists_mul_eq_of_mem_map (t : MonoidalTransform R P) (I : Ideal R)
    {y : t.ring} (hy : y ∈ I.map t.toRing) :
    ∃ (u : blowupAlgebra R P t.x) (_ : u ∉ t.M') (m : ℕ) (F : R), F ∈ I * P ^ m ∧
      y * algebraMap _ t.ring u * t.xR ^ m = t.toRing F := by
  -- representation of elements of `R[x⁻¹P]` inside `R'`
  have hrep : ∀ a : blowupAlgebra R P t.x, ∃ (k : ℕ) (g : R), g ∈ P ^ k ∧
      algebraMap _ t.ring a * t.xR ^ k = t.toRing g := by
    intro a
    obtain ⟨k, g, hg, hag⟩ :=
      MonoidalTransform.exists_mul_pow_eq_of_mem_blowupAlgebra t.x_mem t.x_ne_zero a.2
    refine ⟨k, g, hg, ?_⟩
    have : a * algebraMap R _ t.x ^ k = algebraMap R _ g := Subtype.ext (by simpa using hag)
    rw [MonoidalTransform.xR, MonoidalTransform.toRing, RingHom.comp_apply, ← map_pow,
      ← map_mul, this]
    rfl
  induction hy using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨f, hf, rfl⟩ := hy
    exact ⟨1, t.isPrime.ne_top ∘ (Ideal.eq_top_of_isUnit_mem _ · isUnit_one), 0, f,
      by simpa using hf, by simp⟩
  | zero => exact ⟨1, t.isPrime.ne_top ∘ (Ideal.eq_top_of_isUnit_mem _ · isUnit_one), 0, 0,
      zero_mem _, by simp⟩
  | add y₁ y₂ _ _ h₁ h₂ =>
    obtain ⟨u₁, hu₁, m₁, F₁, hF₁, e₁⟩ := h₁
    obtain ⟨u₂, hu₂, m₂, F₂, hF₂, e₂⟩ := h₂
    obtain ⟨k₁, g₁, hg₁, r₁⟩ := hrep u₁
    obtain ⟨k₂, g₂, hg₂, r₂⟩ := hrep u₂
    refine ⟨u₁ * u₂, fun h => (t.isPrime.mem_or_mem h).elim hu₁ hu₂, m₁ + m₂ + k₁ + k₂,
      F₁ * g₂ * t.x ^ (m₂ + k₁) + F₂ * g₁ * t.x ^ (m₁ + k₂), ?_, ?_⟩
    · refine Ideal.add_mem _ ?_ ?_
      · have := Ideal.mul_mem_mul (Ideal.mul_mem_mul hF₁ hg₂) (Ideal.pow_mem_pow t.x_mem (m₂ + k₁))
        rw [mul_assoc, mul_assoc, ← pow_add, ← pow_add] at this
        convert this using 3
        ring
      · have := Ideal.mul_mem_mul (Ideal.mul_mem_mul hF₂ hg₁) (Ideal.pow_mem_pow t.x_mem (m₁ + k₂))
        rw [mul_assoc, mul_assoc, ← pow_add, ← pow_add] at this
        convert this using 3
        ring
    · have hxR : t.toRing t.x = t.xR := rfl
      simp only [map_add, map_mul, map_pow, hxR]
      rw [← e₁, ← e₂, ← r₁, ← r₂]
      ring
  | smul c y _ h =>
    obtain ⟨u, hu, m, F, hF, e₁⟩ := h
    obtain ⟨⟨a, b⟩, hab⟩ := IsLocalization.mk'_surjective t.M'.primeCompl c
    obtain ⟨k, g, hg, r⟩ := hrep a
    refine ⟨u * b, fun h => (t.isPrime.mem_or_mem h).elim hu b.2, m + k, F * g, ?_, ?_⟩
    · rw [pow_add, ← mul_assoc]; exact Ideal.mul_mem_mul hF hg
    · have hc : c * algebraMap _ t.ring (b : blowupAlgebra R P t.x) = algebraMap _ t.ring a := by
        rw [← hab]; exact IsLocalization.mk'_spec _ _ _
      simp only [map_mul, smul_eq_mul]
      rw [← e₁, ← r, ← hc]
      ring

end Facts

/-! ### Canonical local homomorphisms `R' → R̄'` (p. 211) and Lemma 4 (p. 212) -/

section Lemma4

variable {R Rb : Type u} [CommRing R] [IsRegularLocalRing R] [IsDomain R]
  [CommRing Rb] [IsRegularLocalRing Rb] [IsDomain Rb]

/-- p. 211: "given a monoidal transform `R'` (resp. `R̄'`) of `R` (resp. `R̄`) with center `P`
(resp. `P̄`), we say that a local homomorphism `R' → R̄'` is *canonical* if the following diagram
is commutative:
```
  R' → R̄'
  ↑     ↑
  R  → R̄
```
" (the vertical arrows being the canonical local homomorphisms of the monoidal transforms and
the bottom arrow `α`). -/
@[blueprint "def:III.2-canonical"
  (statement := /-- Let $\alpha\colon R\to\bar R$ be a local homomorphism of regular local rings,
    $R'$ a monoidal transform of $R$ with center $P$ and $\bar R'$ a monoidal transform of
    $\bar R$ with center $\bar P$ (\cref{def:III.2-monoidal-transform}). A local homomorphism
    $\beta\colon R'\to\bar R'$ is \emph{canonical} if the diagram
    $R'\to\bar R'$, $R\to\bar R$ (with the canonical homomorphisms $R\to R'$, $\bar R\to\bar R'$)
    is commutative, i.e.\ $\beta\circ(R\to R')=(\bar R\to\bar R')\circ\alpha$. (p.~211.) -/)
  (latexEnv := "definition")]
structure IsCanonicalLift (α : R →+* Rb) {P : Ideal R} {Pb : Ideal Rb}
    (t : MonoidalTransform R P) (tb : MonoidalTransform Rb Pb) (β : t.ring →+* tb.ring) :
    Prop where
  /-- `β` is a local homomorphism. -/
  isLocalHom : IsLocalHom β
  /-- The diagram commutes. -/
  comm : β.comp t.toRing = tb.toRing.comp α

/-- The set of "those monoidal transforms `R̄'` of `R̄` with center `P̄` such that we have the
commutative diagram of canonical local homomorphisms" (p. 212), as subrings of the field of
quotients of `R̄` (`MonoidalTransform.subring`; see the formalization note there). -/
noncomputable def canonicalTransforms (α : R →+* Rb) {P : Ideal R} {Pb : Ideal Rb}
    (t : MonoidalTransform R P) : Set (Subring (FractionRing Rb)) :=
  (fun tb : MonoidalTransform Rb Pb => tb.subring) ''
    {tb : MonoidalTransform Rb Pb | ∃ β, IsCanonicalLift α t tb β}

/-! #### Lemma 4: the base change `R → R̄` (p. 210) -/

omit [IsDomain R] [IsDomain Rb] in
/-- p. 210: under the same assumption, `dim R̄ = dim R`. -/
theorem RingHom.MapsRSOP.ringKrullDim_eq {α : R →+* Rb} (hα : RingHom.MapsRSOP α) :
    ringKrullDim Rb = ringKrullDim R := by
  classical
  obtain ⟨s, hs, hs', hinj⟩ := hα
  rw [← hs.2, ← hs'.2, Finset.card_image_of_injOn hinj]

omit [IsDomain R] [IsDomain Rb] in
open Classical in
/-- p. 210: "`(α(x₁), …, α(x_r), α(y₁), …, α(y_s))` is a regular system of parameters of `R̄`":
as `MR̄ = M̄` and `dim R̄ = dim R`, `α` maps *every* regular system of parameters of `R` onto one
of `R̄` (without collapsing two parameters). -/
theorem RingHom.MapsRSOP.isRegularSystemOfParameters_image {α : R →+* Rb} (hα : RingHom.MapsRSOP α) {s : Finset R}
    (hs : IsRegularSystemOfParameters R s) :
    IsRegularSystemOfParameters Rb (s.image α) ∧ (s.image α).card = s.card := by
  classical
  have hspan : Ideal.span ((s.image α : Finset Rb) : Set Rb) = maximalIdeal Rb := by
    rw [Finset.coe_image, ← Ideal.map_span, hs.1, RingHom.MapsRSOP.map_maximalIdeal hα]
  have hle : (s.image α).card ≤ s.card := Finset.card_image_le
  have hge : ringKrullDim Rb ≤ (s.image α).card := by
    refine (ringKrullDim_le_spanFinrank_maximalIdeal Rb).trans ?_
    rw [← hspan]
    have := Submodule.spanFinrank_span_le_ncard_of_finite (R := Rb) (s.image α).finite_toSet
    rw [Set.ncard_coe_finset] at this
    exact_mod_cast this
  rw [RingHom.MapsRSOP.ringKrullDim_eq hα, ← hs.2] at hge
  have hcard : (s.image α).card = s.card := by
    have : s.card ≤ (s.image α).card := by exact_mod_cast hge
    omega
  refine ⟨⟨hspan, ?_⟩, hcard⟩
  rw [hcard, hs.2, RingHom.MapsRSOP.ringKrullDim_eq hα]

open Classical in
/-- A subset `T` of a regular system of parameters `S` of a regular local ring `A` is a *minimal
base* of the ideal `(T)`: `(T)` needs `#T` generators (`dim A ≤ dim A/(T) + μ(T)` and the maximal
ideal of `A/(T)` is generated by the `#S - #T` images of `S \ T`). -/
theorem spanFinrank_span_eq_card_of_subset_isRegularSystemOfParameters {A : Type*} [CommRing A]
    [IsRegularLocalRing A] {S T : Finset A} (hSM : Ideal.span (S : Set A) = maximalIdeal A)
    (hScard : S.card = (maximalIdeal A).spanFinrank) (hTS : T ⊆ S) :
    (Ideal.span (T : Set A)).spanFinrank = T.card := by
  apply le_antisymm
  · have := Submodule.spanFinrank_span_le_ncard_of_finite (R := A) (Finset.finite_toSet T)
    rwa [Set.ncard_coe_finset] at this
  · set I := Ideal.span (T : Set A) with hI
    have hIM : I ≤ maximalIdeal A :=
      Ideal.span_le.mpr fun a ha => hSM ▸ Ideal.subset_span (hTS ha)
    have : IsLocalRing (A ⧸ I) := isLocalRing_quotient_of_le hIM
    have hM : maximalIdeal (A ⧸ I) =
        Ideal.span (((S \ T).image (Ideal.Quotient.mk I) : Finset _) : Set _) := by
      rw [← map_maximalIdeal_of_surjective (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective,
        ← hSM, Ideal.map_span]
      apply le_antisymm
      · rw [Ideal.span_le]
        rintro _ ⟨a, ha, rfl⟩
        by_cases haT : a ∈ T
        · rw [Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span haT)]
          exact zero_mem _
        · exact Ideal.subset_span (Finset.mem_image_of_mem _ (Finset.mem_sdiff.mpr ⟨ha, haT⟩))
      · rw [Ideal.span_le]
        intro w hw
        obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hw
        exact Ideal.subset_span ⟨a, (Finset.mem_sdiff.mp ha).1, rfl⟩
    have h1 : (maximalIdeal (A ⧸ I)).spanFinrank ≤ (S \ T).card := by
      rw [hM]
      refine (Submodule.spanFinrank_span_le_ncard_of_finite (Finset.finite_toSet _)).trans ?_
      rw [Set.ncard_coe_finset]
      exact Finset.card_image_le
    have h2 : ringKrullDim A ≤ ringKrullDim (A ⧸ I) + I.spanFinrank :=
      ringKrullDim_le_ringKrullDim_quotient_add_spanFinrank I
        (by rw [← Ideal.jacobson_bot, IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top]
            exact hIM)
    have h4 : ringKrullDim A = S.card := by
      rw [hScard, IsRegularLocalRing.spanFinrank_maximalIdeal]
    obtain ⟨k, hk1, hk⟩ := exists_nat_ringKrullDim_eq
      (ringKrullDim_le_spanFinrank_maximalIdeal (A ⧸ I))
    rw [h4, hk] at h2
    have h2' : S.card ≤ k + I.spanFinrank := by exact_mod_cast h2
    have hk' : k ≤ (maximalIdeal (A ⧸ I)).spanFinrank := by exact_mod_cast hk1
    have h5 := Finset.card_sdiff_add_card_eq_card hTS
    omega

omit [IsDomain R] [IsDomain Rb] in
/-- Lemma 4, first assertion (p. 210): "`P̄ = PR̄` is a prime ideal of `R̄` such that `R̄/P̄` is
regular".  Extend a minimal base `T` of `P` to a regular system of parameters `S` of `R`; then
`α(S)` is a regular system of parameters of `R̄`, `P̄ = (α(T))`, and the maximal ideal of `R̄/P̄`
is generated by the `#S - #T ≤ dim R̄/P̄` images of `α(S \ T)`. -/
theorem RingHom.MapsRSOP.isPrime_map_and_isRegularLocalRing_quotient {α : R →+* Rb} [IsLocalHom α] (hα : RingHom.MapsRSOP α)
    {P : Ideal R} (hP : P.IsPrime) (hS : IsRegularLocalRing (R ⧸ P)) :
    (P.map α).IsPrime ∧ IsRegularLocalRing (Rb ⧸ P.map α) := by
  classical
  obtain ⟨S, T, hSM, hScard, hTS, hTP⟩ := exists_finset_span_eq_prime R P hS
  have hSrsop : IsRegularSystemOfParameters R S :=
    ⟨hSM, by rw [hScard]; exact IsRegularLocalRing.spanFinrank_maximalIdeal⟩
  obtain ⟨hSb, hScardb⟩ := RingHom.MapsRSOP.isRegularSystemOfParameters_image hα hSrsop
  have hPb : P.map α = Ideal.span ((T.image α : Finset Rb) : Set Rb) := by
    rw [Finset.coe_image, ← Ideal.map_span, hTP]
  have hPbM : P.map α ≤ maximalIdeal Rb := by
    rw [← RingHom.MapsRSOP.map_maximalIdeal hα]
    exact Ideal.map_mono (le_maximalIdeal hP.ne_top)
  have : IsLocalRing (Rb ⧸ P.map α) := isLocalRing_quotient_of_le hPbM
  have hreg : IsRegularLocalRing (Rb ⧸ P.map α) := by
    apply IsRegularLocalRing.of_spanFinrank_maximalIdeal_le
    set mk := Ideal.Quotient.mk (P.map α)
    have hM : maximalIdeal (Rb ⧸ P.map α) =
        Ideal.span (((S \ T).image (fun a => mk (α a)) : Finset _) : Set _) := by
      rw [← map_maximalIdeal_of_surjective mk Ideal.Quotient.mk_surjective, ← hSb.1,
        Ideal.map_span]
      apply le_antisymm
      · rw [Ideal.span_le]
        rintro _ ⟨b, hb, rfl⟩
        obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hb
        by_cases haT : a ∈ T
        · rw [Ideal.Quotient.eq_zero_iff_mem.mpr
            (hPb ▸ Ideal.subset_span (Finset.mem_image_of_mem α haT))]
          exact zero_mem _
        · exact Ideal.subset_span (Finset.mem_image_of_mem _ (Finset.mem_sdiff.mpr ⟨ha, haT⟩))
      · rw [Ideal.span_le]
        intro w hw
        obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hw
        exact Ideal.subset_span ⟨α a, Finset.mem_image_of_mem α (Finset.mem_sdiff.mp ha).1, rfl⟩
    have h1 : (maximalIdeal (Rb ⧸ P.map α)).spanFinrank ≤ (S \ T).card := by
      rw [hM]
      refine (Submodule.spanFinrank_span_le_ncard_of_finite (Finset.finite_toSet _)).trans ?_
      rw [Set.ncard_coe_finset]
      exact Finset.card_image_le
    have h2 : ringKrullDim Rb ≤ ringKrullDim (Rb ⧸ P.map α) + (P.map α).spanFinrank :=
      ringKrullDim_le_ringKrullDim_quotient_add_spanFinrank (P.map α)
        (by rw [← Ideal.jacobson_bot, IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top]
            exact hPbM)
    have h3 : (P.map α).spanFinrank ≤ T.card := by
      rw [hPb]
      refine (Submodule.spanFinrank_span_le_ncard_of_finite (Finset.finite_toSet _)).trans ?_
      rw [Set.ncard_coe_finset]
      exact Finset.card_image_le
    have h4 : ringKrullDim Rb = S.card := by
      rw [← hScardb, hSb.2]
    obtain ⟨k, hk1, hk⟩ := exists_nat_ringKrullDim_eq
      (ringKrullDim_le_spanFinrank_maximalIdeal (Rb ⧸ P.map α))
    rw [h4, hk] at h2
    have h2' : S.card ≤ k + (P.map α).spanFinrank := by exact_mod_cast h2
    have h5 := Finset.card_sdiff_add_card_eq_card hTS
    rw [hk]
    exact_mod_cast (by omega : (maximalIdeal (Rb ⧸ P.map α)).spanFinrank ≤ k)
  have : IsDomain (Rb ⧸ P.map α) := isDomain_of_isRegularLocalRing _
  exact ⟨(Ideal.Quotient.isDomain_iff_prime _).mp this, hreg⟩

/-! #### Lemma 4 (2): injectivity and the residue field of `R̄'` (pp. 210–211) -/

/-- `x · (p/x) = p` in `R' = R[x⁻¹P]_{M'}`. -/
theorem MonoidalTransform.xR_mul_algebraMap_div {P : Ideal R} (t : MonoidalTransform R P)
    {p : R} (hp : algebraMap R (FractionRing R) p / algebraMap R (FractionRing R) t.x ∈
      blowupAlgebra R P t.x) :
    t.xR * algebraMap (blowupAlgebra R P t.x) t.ring ⟨_, hp⟩ = t.toRing p := by
  have hx : algebraMap R (FractionRing R) t.x ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective R (FractionRing R))).mpr t.x_ne_zero
  show (algebraMap (blowupAlgebra R P t.x) t.ring) (algebraMap R _ t.x) * _ =
    (algebraMap (blowupAlgebra R P t.x) t.ring) (algebraMap R _ p)
  rw [← map_mul]
  congr 1
  apply Subtype.ext
  simp only [MulMemClass.coe_mul, Subalgebra.coe_algebraMap]
  field_simp

/-- Every element of `R' ⊆ Frac(R)` is a fraction `c/d` of elements of `R`. -/
theorem MonoidalTransform.exists_toRing_mul_eq {P : Ideal R} (t : MonoidalTransform R P)
    (y : t.ring) : ∃ c d : R, d ≠ 0 ∧ t.toRing d * y = t.toRing c := by
  have hrep : ∀ a : blowupAlgebra R P t.x, ∃ (k : ℕ) (g : R),
      algebraMap _ t.ring a * t.xR ^ k = t.toRing g ∧
        (a ≠ 0 → g ≠ 0) := by
    intro a
    obtain ⟨k, g, -, hag⟩ :=
      MonoidalTransform.exists_mul_pow_eq_of_mem_blowupAlgebra t.x_mem t.x_ne_zero a.2
    refine ⟨k, g, ?_, fun ha hg => ha (Subtype.ext ?_)⟩
    · have : a * algebraMap R _ t.x ^ k = algebraMap R _ g := Subtype.ext (by simpa using hag)
      rw [MonoidalTransform.xR, MonoidalTransform.toRing, RingHom.comp_apply, ← map_pow,
        ← map_mul, this]
      rfl
    · have hx : algebraMap R (FractionRing R) t.x ^ k ≠ 0 :=
        pow_ne_zero _ ((map_ne_zero_iff _ (IsFractionRing.injective R (FractionRing R))).mpr
          t.x_ne_zero)
      rw [hg, map_zero] at hag
      simpa [hx] using hag
  obtain ⟨⟨a, s⟩, hy⟩ := IsLocalization.mk'_surjective t.M'.primeCompl y
  obtain ⟨m, g, hg, -⟩ := hrep a
  obtain ⟨n, h, hh, hh0⟩ := hrep s
  have hs0 : (s : blowupAlgebra R P t.x) ≠ 0 := fun h0 => s.2 (h0 ▸ t.M'.zero_mem)
  refine ⟨g * t.x ^ n, h * t.x ^ m, mul_ne_zero (hh0 hs0) (pow_ne_zero _ t.x_ne_zero), ?_⟩
  have hys : y * algebraMap _ t.ring (s : blowupAlgebra R P t.x) = algebraMap _ t.ring a := by
    rw [← hy]; exact IsLocalization.mk'_spec _ _ _
  have hxR : t.toRing t.x = t.xR := rfl
  rw [map_mul, map_mul, map_pow, map_pow, hxR, ← hh, ← hg, ← hys]
  ring

omit [IsDomain R] [IsDomain Rb] in
/-- Lemma 4 (2), p. 212: "All the local homomorphisms of the above diagram are injective", the
case of `α : R → R̄` (the paper gives no argument).  Gap filled: `α⁻¹(M̄ⁿ) = Mⁿ` for all `n`
(`RingHom.MapsRSOP.comap_maximalIdeal_pow`: `α` transforms a regular system of parameters into one),
so `ker α ⊆ ⋂ₙ Mⁿ = 0` by Krull's intersection theorem.  (No flatness is used.) -/
theorem RingHom.MapsRSOP.injective (α : R →+* Rb) [IsLocalHom α] (hα : RingHom.MapsRSOP α) :
    Function.Injective α := by
  rw [injective_iff_map_eq_zero]
  intro a ha
  have h1 : ∀ n : ℕ, a ∈ maximalIdeal R ^ n := fun n => by
    rw [← hα.comap_maximalIdeal_pow n, Ideal.mem_comap, ha]
    exact zero_mem _
  have hK := Ideal.iInf_pow_eq_bot_of_isLocalRing (I := maximalIdeal R) (maximalIdeal.isMaximal R).ne_top
  have h2 : a ∈ (⊥ : Ideal R) := by
    rw [← hK]
    exact (Submodule.mem_iInf _).mpr h1
  exact Ideal.mem_bot.mp h2

omit [IsDomain R] [IsDomain Rb] in
open Classical in
/-- Lemma 4, first assertion (p. 210), second half: "Let `(x₁, …, x_r)` be a minimal base of `P` and
extend it to a regular system of parameters of `R`, say `(x₁, …, x_r, y₁, …, y_s)`. Then
`(α(x₁), …, α(x_r))` is a minimal base of the ideal `P̄` and `(α(x₁), …, α(x_r), α(y₁), …, α(y_s))`
is a regular system of parameters of `R̄`."  A *minimal base* of an ideal is a generating set with
as many elements as `Ideal.spanFinrank` (the minimal number of generators).  The minimal base `T`
of `P` which extends to a regular system of parameters `S` is provided by
`exists_finset_span_eq_prime`; its image `α(T)` has `#T` distinct elements (`α` is injective) and
generates `P̄`, which needs exactly `#T` generators because `α(T)` is part of the regular system of
parameters `α(S)` of `R̄` (`spanFinrank_span_eq_card_of_subset_isRegularSystemOfParameters`). -/
@[blueprint "lem:III.4-minimal-base"
  (statement := /-- Let $\alpha\colon R\to\bar R$ be as in Lemma 4 and $P$ a prime ideal of $R$ with
    $R/P$ regular. Let $(x_1,\dots,x_r)$ be a minimal base of $P$ extended to a regular system of
    parameters $(x_1,\dots,x_r,y_1,\dots,y_s)$ of $R$. Then $(\alpha(x_1),\dots,\alpha(x_r))$ is a
    minimal base of $\bar P=P\bar R$ (the $\alpha(x_i)$ are distinct, generate $\bar P$, and $\bar P$
    needs $r$ generators) and $(\alpha(x_i),\alpha(y_j))$ is a regular system of parameters of
    $\bar R$. (p.~210.) -/)
  (proof := /-- $\alpha$ is injective and maps every regular system of parameters of $R$ onto one of
    $\bar R$ (\cref{lem:III.4}); $\bar P=(\alpha(x_i))$. A subset $T$ of a regular system of
    parameters $S$ of a regular local ring $A$ is a minimal base of $(T)$: $\dim A\le\dim A/(T)+\mu(T)$,
    and the maximal ideal of $A/(T)$ is generated by the $\#S-\#T$ images of $S\setminus T$, so
    $\#S\le(\#S-\#T)+\mu(T)$. Apply this to $R$ and to $\bar R$. (p.~210.) -/)
  (latexEnv := "lemma")]
theorem RingHom.MapsRSOP.exists_minimalBase_image {α : R →+* Rb} [IsLocalHom α]
    (hα : RingHom.MapsRSOP α) {P : Ideal R} (hP : P.IsPrime) (hS : IsRegularLocalRing (R ⧸ P)) :
    ∃ S T : Finset R, IsRegularSystemOfParameters R S ∧ T ⊆ S ∧ Ideal.span (T : Set R) = P ∧
      T.card = P.spanFinrank ∧ IsRegularSystemOfParameters Rb (S.image α) ∧
      Ideal.span ((T.image α : Finset Rb) : Set Rb) = P.map α ∧ (T.image α).card = T.card ∧
      (P.map α).spanFinrank = (T.image α).card := by
  have _ := hP
  obtain ⟨S, T, hSM, hScard, hTS, hTP⟩ := exists_finset_span_eq_prime R P hS
  have hSrsop : IsRegularSystemOfParameters R S :=
    ⟨hSM, by rw [hScard]; exact IsRegularLocalRing.spanFinrank_maximalIdeal⟩
  obtain ⟨hSb, -⟩ := RingHom.MapsRSOP.isRegularSystemOfParameters_image hα hSrsop
  have hPb : Ideal.span ((T.image α : Finset Rb) : Set Rb) = P.map α := by
    rw [Finset.coe_image, ← Ideal.map_span, hTP]
  have hTcard : (T.image α).card = T.card :=
    Finset.card_image_of_injective _ (RingHom.MapsRSOP.injective α hα)
  have hSbcard : (S.image α).card = (maximalIdeal Rb).spanFinrank := by
    have h1 := hSb.2
    rw [IsRegularLocalRing.spanFinrank_maximalIdeal.symm] at h1
    exact_mod_cast h1
  refine ⟨S, T, hSrsop, hTS, hTP, ?_, hSb, hPb, hTcard, ?_⟩
  · rw [← hTP]
    exact (spanFinrank_span_eq_card_of_subset_isRegularSystemOfParameters hSM hScard hTS).symm
  · rw [← hPb]
    exact (spanFinrank_span_eq_card_of_subset_isRegularSystemOfParameters (A := Rb) hSb.1 hSbcard
      (Finset.image_subset_image hTS))

/-- Lemma 4 (2): the canonical lift `β : R' → R̄'` is injective (p. 211).  Write `y ∈ R'` as
`y = c/d` with `c, d ∈ R`; if `β(y) = 0` then `(R̄ → R̄')(α(c)) = β(c) = 0`, so `c = 0`. -/
theorem IsCanonicalLift.injective_of_mapsRSOP (α : R →+* Rb) [IsLocalHom α] (hα : RingHom.MapsRSOP α)
    {P : Ideal R} (t : MonoidalTransform R P) (tb : MonoidalTransform Rb (P.map α))
    (β : t.ring →+* tb.ring) (hβ : IsCanonicalLift α t tb β) : Function.Injective β := by
  rw [injective_iff_map_eq_zero]
  intro y hy
  obtain ⟨c, d, hd, hcd⟩ := t.exists_toRing_mul_eq y
  have h1 := congrArg β hcd
  rw [map_mul, hy, mul_zero] at h1
  have h2 : tb.toRing (α c) = 0 := by
    rw [← RingHom.comp_apply, ← hβ.comm, RingHom.comp_apply, ← h1]
  have hc : c = 0 := by
    have := (map_eq_zero_iff _ (tb.toRing_injective)).mp h2
    exact (map_eq_zero_iff _ (RingHom.MapsRSOP.injective α hα)).mp this
  rw [hc, map_zero] at hcd
  have hd' : t.toRing d ≠ 0 := (map_ne_zero_iff _ t.toRing_injective).mpr hd
  exact (mul_eq_zero.mp hcd).resolve_left hd'

/-- The main structural fact (p. 211): every element of `R̄'` is a fraction `a/b` with `a, b` in
the subring generated by the images of `R̄` and `R'`, `b` a unit. -/
theorem IsCanonicalLift.exists_isUnit_mul_eq_of_mapsRSOP (α : R →+* Rb) [IsLocalHom α] (hα : RingHom.MapsRSOP α)
    {P : Ideal R} (t : MonoidalTransform R P) (tb : MonoidalTransform Rb (P.map α))
    (β : t.ring →+* tb.ring) (hβ : IsCanonicalLift α t tb β) (z : tb.ring) :
    ∃ a b, a ∈ Subring.closure (Set.range tb.toRing ∪ Set.range β) ∧
      b ∈ Subring.closure (Set.range tb.toRing ∪ Set.range β) ∧ IsUnit b ∧ z * b = a := by
  set D := Subring.closure (Set.range tb.toRing ∪ Set.range β)
  have hD1 : ∀ r, tb.toRing r ∈ D := fun r => Subring.subset_closure (Or.inl ⟨r, rfl⟩)
  have hD2 : ∀ y, β y ∈ D := fun y => Subring.subset_closure (Or.inr ⟨y, rfl⟩)
  have hcomm : ∀ r, β (t.toRing r) = tb.toRing (α r) := fun r => RingHom.congr_fun hβ.comm r
  set ξ := β t.xR with hξdef
  have hξ0 : ξ ≠ 0 := by
    rw [hξdef, MonoidalTransform.xR, hcomm]
    exact (map_ne_zero_iff _ tb.toRing_injective).mpr
      ((map_ne_zero_iff _ (RingHom.MapsRSOP.injective α hα)).mpr t.x_ne_zero)
  -- every `p̄ ∈ P̄` is `ξ d` with `d ∈ D`
  have hstep1 : ∀ p ∈ P.map α, ∃ d ∈ D, tb.toRing p = ξ * d := by
    intro p hp
    have hp' : p ∈ Submodule.span Rb (α '' (P : Set R)) := hp
    refine Submodule.span_induction (p := fun p _ => ∃ d ∈ D, tb.toRing p = ξ * d)
      ?_ ?_ ?_ ?_ hp'
    · rintro _ ⟨q, hq, rfl⟩
      have := t.span_xR_eq_map ▸ Ideal.mem_map_of_mem t.toRing hq
      obtain ⟨u, hu⟩ := Ideal.mem_span_singleton'.mp this
      refine ⟨β u, hD2 u, ?_⟩
      rw [← hcomm, ← hu, map_mul, mul_comm]
    · exact ⟨0, zero_mem _, by simp⟩
    · rintro p p' - - ⟨d, hd, e⟩ ⟨d', hd', e'⟩
      exact ⟨d + d', add_mem hd hd', by rw [map_add, e, e', mul_add]⟩
    · rintro c p - ⟨d, hd, e⟩
      refine ⟨tb.toRing c * d, mul_mem (hD1 c) hd, ?_⟩
      rw [smul_eq_mul, map_mul, e]
      ring
  -- `x̄ = ξ w` with `w ∈ D` a unit
  obtain ⟨w, hwD, hw⟩ := hstep1 tb.x tb.x_mem
  have hwu : IsUnit w := by
    have hmem : ξ ∈ Ideal.span {tb.xR} := by
      rw [tb.span_xR_eq_map, hξdef, MonoidalTransform.xR, hcomm]
      exact Ideal.mem_map_of_mem _ (Ideal.mem_map_of_mem _ t.x_mem)
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp hmem
    have hxw : tb.xR = ξ * w := hw
    rw [hxw] at hc
    refine IsUnit.of_mul_eq_one c ?_
    apply mul_left_cancel₀ hξ0
    rw [mul_one]
    calc ξ * (w * c) = c * (ξ * w) := by ring
      _ = ξ := hc
  -- elements of `R̄[x̄⁻¹P̄]` times a power of `w` lie in `D`
  have hstep2 : ∀ a : blowupAlgebra Rb (P.map α) tb.x, ∃ (N : ℕ) (d : tb.ring), d ∈ D ∧
      algebraMap _ tb.ring a * w ^ N = d := by
    rintro ⟨a, ha⟩
    induction ha using Algebra.adjoin_induction with
    | mem y hy =>
      obtain ⟨p, hp, rfl⟩ := hy
      obtain ⟨d, hd, e⟩ := hstep1 p hp
      refine ⟨1, d, hd, ?_⟩
      apply mul_left_cancel₀ hξ0
      have h1 := tb.xR_mul_algebraMap_div (p := p) (Algebra.subset_adjoin ⟨p, hp, rfl⟩)
      have hxw : tb.xR = ξ * w := hw
      rw [hxw] at h1
      rw [pow_one, ← e, ← h1]
      ring
    | algebraMap r =>
      refine ⟨0, tb.toRing r, hD1 r, ?_⟩
      rw [pow_zero, mul_one]
      rfl
    | add y y' hy hy' ih ih' =>
      obtain ⟨N, d, hd, e⟩ := ih
      obtain ⟨N', d', hd', e'⟩ := ih'
      refine ⟨N + N', d * w ^ N' + d' * w ^ N, add_mem (mul_mem hd (pow_mem hwD _))
        (mul_mem hd' (pow_mem hwD _)), ?_⟩
      have : (⟨y + y', add_mem hy hy'⟩ : blowupAlgebra Rb (P.map α) tb.x) = ⟨y, hy⟩ + ⟨y', hy'⟩ :=
        rfl
      rw [this, map_add, ← e, ← e']
      ring
    | mul y y' hy hy' ih ih' =>
      obtain ⟨N, d, hd, e⟩ := ih
      obtain ⟨N', d', hd', e'⟩ := ih'
      refine ⟨N + N', d * d', mul_mem hd hd', ?_⟩
      have : (⟨y * y', mul_mem hy hy'⟩ : blowupAlgebra Rb (P.map α) tb.x) = ⟨y, hy⟩ * ⟨y', hy'⟩ :=
        rfl
      rw [this, map_mul, ← e, ← e']
      ring
  -- fractions
  obtain ⟨⟨a, s⟩, hz⟩ := IsLocalization.mk'_surjective tb.M'.primeCompl z
  obtain ⟨Na, da, hda, ea⟩ := hstep2 a
  obtain ⟨Ns, ds, hds, es⟩ := hstep2 s
  have hzs : z * algebraMap _ tb.ring (s : blowupAlgebra Rb (P.map α) tb.x) =
      algebraMap _ tb.ring a := by
    rw [← hz]; exact IsLocalization.mk'_spec _ _ _
  have hsu : IsUnit (algebraMap _ tb.ring (s : blowupAlgebra Rb (P.map α) tb.x)) :=
    IsLocalization.map_units tb.ring s
  refine ⟨da * w ^ Ns, ds * w ^ Na, mul_mem hda (pow_mem hwD _), mul_mem hds (pow_mem hwD _),
    ?_, ?_⟩
  · rw [← es]
    exact (hsu.mul (hwu.pow _)).mul (hwu.pow _)
  · rw [← es, ← ea, ← hzs]
    ring

/-- Lemma 4 (2), second half: the residue field of `R̄'` is generated by those of `R'` and `R̄`. -/
theorem IsCanonicalLift.closure_residueField_ranges_eq_top (α : R →+* Rb) [IsLocalHom α]
    (hα : RingHom.MapsRSOP α) {P : Ideal R} (t : MonoidalTransform R P)
    (tb : MonoidalTransform Rb (P.map α)) (β : t.ring →+* tb.ring)
    (hβ : IsCanonicalLift α t tb β) :
    haveI := hβ.isLocalHom
    Subfield.closure
        (Set.range (ResidueField.map (R := t.ring) (S := tb.ring) β) ∪
          Set.range (ResidueField.map (R := Rb) (S := tb.ring) tb.toRing)) = ⊤ := by
  have := hβ.isLocalHom
  set F := Subfield.closure
    (Set.range (ResidueField.map (R := t.ring) (S := tb.ring) β) ∪
      Set.range (ResidueField.map (R := Rb) (S := tb.ring) tb.toRing))
  have hD : Subring.closure (Set.range tb.toRing ∪ Set.range β) ≤
      F.toSubring.comap (residue tb.ring) := by
    rw [Subring.closure_le]
    rintro _ (⟨r, rfl⟩ | ⟨y, rfl⟩)
    · show residue tb.ring (tb.toRing r) ∈ F
      rw [← ResidueField.map_residue]
      exact Subfield.subset_closure (Or.inr ⟨_, rfl⟩)
    · show residue tb.ring (β y) ∈ F
      rw [← ResidueField.map_residue]
      exact Subfield.subset_closure (Or.inl ⟨_, rfl⟩)
  rw [eq_top_iff]
  intro ζ _
  obtain ⟨z, rfl⟩ := residue_surjective ζ
  obtain ⟨a, b, ha, hb, hbu, hzb⟩ := IsCanonicalLift.exists_isUnit_mul_eq_of_mapsRSOP α hα t tb β hβ z
  have hb0 : residue tb.ring b ≠ 0 := (hbu.map (residue tb.ring)).ne_zero
  have : residue tb.ring z = residue tb.ring a * (residue tb.ring b)⁻¹ := by
    rw [eq_mul_inv_iff_mul_eq₀ hb0, ← map_mul, hzb]
  rw [this]
  exact F.mul_mem (hD ha) (F.inv_mem (hD hb))

/-- Lemma 4 (2) (p. 212). -/
theorem RingHom.MapsRSOP.injective_and_closure_residueField_ranges_eq_top (α : R →+* Rb) [IsLocalHom α] (hα : RingHom.MapsRSOP α) {P : Ideal R} :
    ∀ (t : MonoidalTransform R P) (tb : MonoidalTransform Rb (P.map α))
      (β : t.ring →+* tb.ring) (hβ : IsCanonicalLift α t tb β),
        Function.Injective α ∧ Function.Injective t.toRing ∧ Function.Injective tb.toRing ∧
        Function.Injective β ∧
        haveI := hβ.isLocalHom
        Subfield.closure
            (Set.range (ResidueField.map (R := t.ring) (S := tb.ring) β) ∪
              Set.range (ResidueField.map (R := Rb) (S := tb.ring) tb.toRing)) = ⊤ :=
  fun t tb β hβ => ⟨RingHom.MapsRSOP.injective α hα, t.toRing_injective, tb.toRing_injective,
    IsCanonicalLift.injective_of_mapsRSOP α hα t tb β hβ, IsCanonicalLift.closure_residueField_ranges_eq_top α hα t tb β hβ⟩

/-! #### Lemma 4 (3): the closed fibre `R̄'/M_{R'}R̄'` and flatness of `R' → R̄'` (pp. 211–212) -/

/-- p. 212: if `R̄` is residually separable algebraic over `R`, the closed fibre
`R̄'/M_{R'}R̄'` is a field, i.e. `M_{R'}R̄' = M_{R̄'}`. -/
theorem IsCanonicalLift.map_maximalIdeal_eq_of_isResiduallySeparableAlgebraic (α : R →+* Rb) [IsLocalHom α]
    (hα : RingHom.MapsRSOP α) {P : Ideal R} (t : MonoidalTransform R P)
    (tb : MonoidalTransform Rb (P.map α)) (β : t.ring →+* tb.ring)
    (hβ : IsCanonicalLift α t tb β) (hsep : RingHom.IsResiduallySeparableAlgebraic α) :
    (maximalIdeal t.ring).map β = maximalIdeal tb.ring := by
  have := hβ.isLocalHom
  have hcomm : ∀ r, β (t.toRing r) = tb.toRing (α r) := fun r => RingHom.congr_fun hβ.comm r
  set I := (maximalIdeal t.ring).map β with hIdef
  have hI : I ≤ maximalIdeal tb.ring :=
    Ideal.map_le_iff_le_comap.mpr fun a ha => map_nonunit β a ha
  have : IsLocalRing (tb.ring ⧸ I) := isLocalRing_quotient_of_le hI
  set mk := Ideal.Quotient.mk I
  have hMb : ∀ r ∈ maximalIdeal Rb, (mk.comp tb.toRing) r = 0 := by
    intro r hr
    rw [RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem]
    rw [← RingHom.MapsRSOP.map_maximalIdeal hα] at hr
    have h1 : tb.toRing r ∈ ((maximalIdeal R).map α).map tb.toRing := Ideal.mem_map_of_mem _ hr
    rw [Ideal.map_map, ← hβ.comm, ← Ideal.map_map] at h1
    have hloc : (maximalIdeal R).map t.toRing ≤ maximalIdeal t.ring :=
      Ideal.map_le_iff_le_comap.mpr fun a ha => map_nonunit t.toRing a ha
    exact Ideal.map_mono hloc h1
  let k := ResidueField R
  let k' := ResidueField t.ring
  let kb := ResidueField Rb
  let _ : Algebra k k' := (ResidueField.map t.toRing).toAlgebra
  let _ : Algebra k kb := (ResidueField.map α).toAlgebra
  have : Algebra.IsSeparable k kb := hsep
  let f₀ : k' →+* tb.ring ⧸ I := Ideal.Quotient.lift (maximalIdeal t.ring) (mk.comp β)
    (fun a ha => Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_map_of_mem β ha))
  let g₀ : kb →+* tb.ring ⧸ I := Ideal.Quotient.lift (maximalIdeal Rb) (mk.comp tb.toRing) hMb
  let _ : Algebra k (tb.ring ⧸ I) := (g₀.comp (ResidueField.map α)).toAlgebra
  have hf₀ : ∀ c : k, f₀ (algebraMap k k' c) = algebraMap k (tb.ring ⧸ I) c := by
    intro c
    obtain ⟨r, rfl⟩ := residue_surjective c
    show f₀ (ResidueField.map t.toRing (residue R r)) = g₀ (ResidueField.map α (residue R r))
    rw [ResidueField.map_residue, ResidueField.map_residue]
    show mk (β (t.toRing r)) = mk (tb.toRing (α r))
    rw [hcomm]
  let f : k' →ₐ[k] tb.ring ⧸ I := { f₀ with commutes' := hf₀ }
  let g : kb →ₐ[k] tb.ring ⧸ I := { g₀ with commutes' := fun _ => rfl }
  let Ψ : k' ⊗[k] kb →ₐ[k] tb.ring ⧸ I := Algebra.TensorProduct.productMap f g
  have hΨ1 : ∀ y, Ψ (residue t.ring y ⊗ₜ 1) = mk (β y) := by
    intro y
    rw [Algebra.TensorProduct.productMap_apply_tmul, map_one, mul_one]
    rfl
  have hΨ2 : ∀ r, Ψ (1 ⊗ₜ residue Rb r) = mk (tb.toRing r) := by
    intro r
    rw [Algebra.TensorProduct.productMap_apply_tmul, map_one, one_mul]
    rfl
  have hrange : Subring.closure (Set.range tb.toRing ∪ Set.range β) ≤
      Ψ.toRingHom.range.comap mk := by
    rw [Subring.closure_le]
    rintro _ (⟨r, rfl⟩ | ⟨y, rfl⟩)
    · exact RingHom.mem_range.mpr ⟨1 ⊗ₜ residue Rb r, hΨ2 r⟩
    · exact RingHom.mem_range.mpr ⟨residue t.ring y ⊗ₜ 1, hΨ1 y⟩
  have hfrac : ∀ q : tb.ring ⧸ I, ∃ a b : k' ⊗[k] kb, IsUnit (Ψ b) ∧ q * Ψ b = Ψ a := by
    intro q
    obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective q
    obtain ⟨a, b, ha, hb, hbu, hzb⟩ := IsCanonicalLift.exists_isUnit_mul_eq_of_mapsRSOP α hα t tb β hβ z
    obtain ⟨a', ha'⟩ := RingHom.mem_range.mp (hrange ha)
    obtain ⟨b', hb'⟩ := RingHom.mem_range.mp (hrange hb)
    have ha'' : Ψ a' = mk a := ha'
    have hb'' : Ψ b' = mk b := hb'
    refine ⟨a', b', ?_, ?_⟩
    · rw [hb'']; exact hbu.map mk
    · rw [hb'', ha'', ← map_mul, hzb]
  set 𝔭 := (maximalIdeal (tb.ring ⧸ I)).comap Ψ.toRingHom
  have hbot : ∀ q ∈ maximalIdeal (tb.ring ⧸ I), q = 0 := by
    intro q hq
    obtain ⟨a, b, hbu, hqb⟩ := hfrac q
    have ha : a ∈ 𝔭 := by
      show Ψ a ∈ maximalIdeal _
      rw [← hqb]; exact Ideal.mul_mem_right _ _ hq
    have hF := isField_localization_tensorProduct_of_isSeparable k k' kb 𝔭
    have h0 : algebraMap _ (Localization.AtPrime 𝔭) a = 0 := by
      by_contra hne
      obtain ⟨c, hc⟩ := hF.mul_inv_cancel hne
      have hmem :=
        (IsLocalization.AtPrime.to_map_mem_maximal_iff (Localization.AtPrime 𝔭) 𝔭 a).mpr ha
      exact (maximalIdeal.isMaximal _).ne_top
        (Ideal.eq_top_of_isUnit_mem _ hmem (IsUnit.of_mul_eq_one c hc))
    obtain ⟨⟨c, hc⟩, hca⟩ := (IsLocalization.map_eq_zero_iff 𝔭.primeCompl _ a).mp h0
    have hcu : IsUnit (Ψ c) := IsLocalRing.notMem_maximalIdeal.mp hc
    have hΨa : Ψ a = 0 := by
      have h1 := congrArg Ψ hca
      rw [map_mul, map_zero] at h1
      exact hcu.mul_right_eq_zero.mp h1
    rw [hΨa] at hqb
    exact hbu.mul_left_eq_zero.mp hqb
  apply le_antisymm hI
  intro z hz
  have : mk z ∈ maximalIdeal (tb.ring ⧸ I) := by
    rw [← map_maximalIdeal_of_surjective mk Ideal.Quotient.mk_surjective]
    exact Ideal.mem_map_of_mem _ hz
  exact Ideal.Quotient.eq_zero_iff_mem.mp (hbot _ this)

/-- A ring homomorphism `Θ : A → B` into a local ring which is injective and such that every
element of `B` is a fraction `Θ(a)/Θ(b)` makes `B` the localization of `A` at the contraction of
the maximal ideal. -/
theorem isLocalization_comap_maximalIdeal_of_injective {A B : Type*} [CommRing A] [CommRing B]
    [IsLocalRing B] (Θ : A →+* B) (hinj : Function.Injective Θ)
    (hfrac : ∀ z : B, ∃ a b, IsUnit (Θ b) ∧ z * Θ b = Θ a) :
    letI := Θ.toAlgebra
    IsLocalization.AtPrime B ((maximalIdeal B).comap Θ) := by
  let _ := Θ.toAlgebra
  rw [IsLocalization.AtPrime, isLocalization_iff]
  refine ⟨fun y => IsLocalRing.notMem_maximalIdeal.mp y.2, fun z => ?_,
    fun {x y} h => ⟨1, by rw [hinj h]⟩⟩
  obtain ⟨a, b, hbu, hzb⟩ := hfrac z
  exact ⟨⟨a, ⟨b, fun h => (IsLocalRing.mem_maximalIdeal _).mp h hbu⟩⟩, hzb⟩

/-- The canonical homomorphism `R' ⊗_R R̄ → k' ⊗_k k̄` induced by the residue maps
(`k`, `k'`, `k̄` the residue fields of `R`, `R'`, `R̄`). -/
noncomputable def residueTensorHom (α : R →+* Rb) [IsLocalHom α] {P : Ideal R}
    (t : MonoidalTransform R P) :
    letI : Algebra R Rb := α.toAlgebra
    letI : Algebra R t.ring := t.toRing.toAlgebra
    haveI : IsLocalHom (algebraMap R Rb) := inferInstanceAs (IsLocalHom α)
    haveI : IsLocalHom (algebraMap R t.ring) := t.isLocalHom_toRing
    t.ring ⊗[R] Rb →+* ResidueField t.ring ⊗[ResidueField R] ResidueField Rb :=
  letI : Algebra R Rb := α.toAlgebra
  letI : Algebra R t.ring := t.toRing.toAlgebra
  haveI : IsLocalHom (algebraMap R Rb) := inferInstanceAs (IsLocalHom α)
  haveI : IsLocalHom (algebraMap R t.ring) := t.isLocalHom_toRing
  letI : Algebra R (ResidueField t.ring ⊗[ResidueField R] ResidueField Rb) :=
    ((algebraMap (ResidueField R) (ResidueField t.ring ⊗[ResidueField R] ResidueField Rb)).comp
      (residue R)).toAlgebra
  (Algebra.TensorProduct.productMap
    { (Algebra.TensorProduct.includeLeftRingHom).comp (residue t.ring) with
      commutes' := fun r => by
        show residue t.ring (t.toRing r) ⊗ₜ (1 : ResidueField Rb) =
          algebraMap (ResidueField R) (ResidueField t.ring) (residue R r) ⊗ₜ 1
        rw [ResidueField.algebraMap_residue]
        rfl }
    { (Algebra.TensorProduct.includeRight.toRingHom).comp (residue Rb) with
      commutes' := fun r => by
        show (1 : ResidueField t.ring) ⊗ₜ residue Rb (α r) =
          algebraMap (ResidueField R) (ResidueField t.ring ⊗[ResidueField R] ResidueField Rb)
            (residue R r)
        rw [Algebra.TensorProduct.algebraMap_apply', ResidueField.algebraMap_residue]
        rfl }).toRingHom

omit [IsDomain Rb] in
/-- `residueTensorHom` on pure tensors. -/
theorem residueTensorHom_tmul (α : R →+* Rb) [IsLocalHom α] {P : Ideal R}
    (t : MonoidalTransform R P) (y : t.ring) (r : Rb) :
    letI : Algebra R Rb := α.toAlgebra
    letI : Algebra R t.ring := t.toRing.toAlgebra
    haveI : IsLocalHom (algebraMap R Rb) := inferInstanceAs (IsLocalHom α)
    haveI : IsLocalHom (algebraMap R t.ring) := t.isLocalHom_toRing
    residueTensorHom α t (y ⊗ₜ r) = residue t.ring y ⊗ₜ residue Rb r := by
  let _ : Algebra R Rb := α.toAlgebra
  let _ : Algebra R t.ring := t.toRing.toAlgebra
  have : IsLocalHom (algebraMap R Rb) := inferInstanceAs (IsLocalHom α)
  have : IsLocalHom (algebraMap R t.ring) := t.isLocalHom_toRing
  show (residue t.ring y ⊗ₜ[ResidueField R] (1 : ResidueField Rb)) *
    ((1 : ResidueField t.ring) ⊗ₜ[ResidueField R] residue Rb r) = _
  rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]

omit [IsDomain Rb] in
/-- `R' ⊗_R R̄ → k' ⊗_k k̄` is surjective. -/
theorem residueTensorHom_surjective (α : R →+* Rb) [IsLocalHom α] {P : Ideal R}
    (t : MonoidalTransform R P) :
    letI : Algebra R Rb := α.toAlgebra
    letI : Algebra R t.ring := t.toRing.toAlgebra
    haveI : IsLocalHom (algebraMap R Rb) := inferInstanceAs (IsLocalHom α)
    haveI : IsLocalHom (algebraMap R t.ring) := t.isLocalHom_toRing
    Function.Surjective (residueTensorHom α t) := by
  let _ : Algebra R Rb := α.toAlgebra
  let _ : Algebra R t.ring := t.toRing.toAlgebra
  have : IsLocalHom (algebraMap R Rb) := inferInstanceAs (IsLocalHom α)
  have : IsLocalHom (algebraMap R t.ring) := t.isLocalHom_toRing
  intro w
  induction w with
  | tmul a b =>
    obtain ⟨y, rfl⟩ := residue_surjective a
    obtain ⟨r, rfl⟩ := residue_surjective b
    exact ⟨y ⊗ₜ r, residueTensorHom_tmul α t y r⟩
  | add w w' hw hw' =>
    obtain ⟨z, rfl⟩ := hw
    obtain ⟨z', rfl⟩ := hw'
    exact ⟨z + z', map_add _ _ _⟩

/-- **Lean-only infrastructure** (not a statement of the paper; the paper describes `R̄'` through the
chart `Ã'` of p. 211, see `MonoidalTransform.exists_charts_residue`; not used by Lemma 4, its
Corollaries or Lemma 5, only by `Compat/CanonicalLiftResidue.lean` (Remark 1 of §9) and
`IsCanonicalLift.flat_of_mapsRSOP`).  The structure of a canonical lift `β : R' → R̄'`.  With
`A = R' ⊗_R R̄`: `R̄'` is the localization of `A` at a prime (the map `Θ : A → R̄'` is injective and every
element of `R̄'` is a fraction `Θ(a)/Θ(b)`); the contraction of `M_{R̄'}` is the inverse image of
a prime `q̄` of `k' ⊗_k k̄` (the paper's `q̄` with `q̄ ∩ k[X]/m̄' = (0)`), and the closed fibre
`R̄'/M_{R'}R̄'` is the localization of `k' ⊗_k k̄` at `q̄`. -/
theorem IsCanonicalLift.exists_tensorHom_injective_and_isFraction_and_quotient_equiv (α : R →+* Rb) [IsLocalHom α] (hα : RingHom.MapsRSOP α) {P : Ideal R}
    (t : MonoidalTransform R P) (tb : MonoidalTransform Rb (P.map α)) (β : t.ring →+* tb.ring)
    (hβ : IsCanonicalLift α t tb β) :
    letI : Algebra R Rb := α.toAlgebra
    letI : Algebra R t.ring := t.toRing.toAlgebra
    haveI : IsLocalHom (algebraMap R Rb) := inferInstanceAs (IsLocalHom α)
    haveI : IsLocalHom (algebraMap R t.ring) := t.isLocalHom_toRing
    ∃ Θ : t.ring ⊗[R] Rb →+* tb.ring, (∀ y b, Θ (y ⊗ₜ b) = β y * tb.toRing b) ∧
      Function.Injective Θ ∧ (∀ z, ∃ a b, IsUnit (Θ b) ∧ z * Θ b = Θ a) ∧
      ∃ (𝔭 : Ideal (ResidueField t.ring ⊗[ResidueField R] ResidueField Rb)) (_ : 𝔭.IsPrime),
        (∀ z, Θ z ∈ maximalIdeal tb.ring ↔ residueTensorHom α t z ∈ 𝔭) ∧
        Nonempty (tb.ring ⧸ (maximalIdeal t.ring).map β ≃+* Localization.AtPrime 𝔭) := by
  let _ : Algebra R Rb := α.toAlgebra
  let _ : Algebra R t.ring := t.toRing.toAlgebra
  have : IsLocalHom (algebraMap R Rb) := inferInstanceAs (IsLocalHom α)
  have : IsLocalHom (algebraMap R t.ring) := t.isLocalHom_toRing
  have := hβ.isLocalHom
  have hcomm : ∀ r, β (t.toRing r) = tb.toRing (α r) := fun r => RingHom.congr_fun hβ.comm r
  have : Module.Flat R Rb := hα.flat
  -- the homomorphism `Θ : R' ⊗_R R̄ → R̄'`
  let _ : Algebra R tb.ring := (tb.toRing.comp α).toAlgebra
  let βₐ : t.ring →ₐ[R] tb.ring := { β with commutes' := fun r => hcomm r }
  let γₐ : Rb →ₐ[R] tb.ring := { tb.toRing with commutes' := fun r => rfl }
  let Θ : t.ring ⊗[R] Rb →ₐ[R] tb.ring := Algebra.TensorProduct.productMap βₐ γₐ
  have hΘ : ∀ y b, Θ (y ⊗ₜ b) = β y * tb.toRing b := fun y b =>
    Algebra.TensorProduct.productMap_apply_tmul βₐ γₐ y b
  -- `Θ` is injective: `d z = 1 ⊗ b` for some `d ≠ 0` in `R`, and `R' ⊗_R R̄` is flat over `R'`
  have hsm : ∀ (d : R) (z : t.ring ⊗[R] Rb), t.toRing d • z = d • z := fun d z =>
    algebraMap_smul t.ring d z
  have hnorm : ∀ z : t.ring ⊗[R] Rb, ∃ d : R, d ≠ 0 ∧ ∃ b : Rb, t.toRing d • z = 1 ⊗ₜ b := by
    intro z
    induction z with
    | tmul y b =>
      obtain ⟨c, d, hd, hcd⟩ := t.exists_toRing_mul_eq y
      refine ⟨d, hd, α c * b, ?_⟩
      rw [TensorProduct.smul_tmul', smul_eq_mul, hcd]
      have : t.toRing c = c • (1 : t.ring) := by
        rw [Algebra.smul_def, mul_one]; rfl
      rw [this, TensorProduct.smul_tmul, Algebra.smul_def]
      rfl
    | add z w hz hw =>
      obtain ⟨d, hd, b, e⟩ := hz
      obtain ⟨d', hd', b', e'⟩ := hw
      refine ⟨d * d', mul_ne_zero hd hd', α d' * b + α d * b', ?_⟩
      rw [hsm] at e e' ⊢
      rw [smul_add, mul_comm d d', mul_smul, e, mul_comm d' d, mul_smul, e', TensorProduct.tmul_add,
        ← TensorProduct.tmul_smul, ← TensorProduct.tmul_smul, Algebra.smul_def, Algebra.smul_def]
      rfl
  have hΘinj : Function.Injective Θ := by
    rw [injective_iff_map_eq_zero]
    intro z hz
    obtain ⟨d, hd, b, e⟩ := hnorm z
    have h1 : Θ (t.toRing d • z) = β (t.toRing d) * Θ z := by
      rw [Algebra.smul_def, map_mul]
      congr 1
      rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply, hΘ,
        map_one, mul_one]
    rw [e, hz, mul_zero, hΘ, map_one, one_mul] at h1
    have hb : b = 0 := (map_eq_zero_iff _ tb.toRing_injective).mp h1
    rw [hb, TensorProduct.tmul_zero] at e
    have hd' : t.toRing d ∈ nonZeroDivisors t.ring :=
      mem_nonZeroDivisors_of_ne_zero ((map_ne_zero_iff _ t.toRing_injective).mpr hd)
    exact Module.Flat.isSMulRegular_of_nonZeroDivisors hd' (e.trans (smul_zero _).symm)
  -- every element of `R̄'` is a fraction `Θ(a)/Θ(b)`
  have hrange : Subring.closure (Set.range tb.toRing ∪ Set.range β) ≤ Θ.toRingHom.range := by
    rw [Subring.closure_le]
    rintro _ (⟨r, rfl⟩ | ⟨y, rfl⟩)
    · exact ⟨1 ⊗ₜ r, by rw [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, hΘ, map_one, one_mul]⟩
    · exact ⟨y ⊗ₜ 1, by rw [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, hΘ, map_one, mul_one]⟩
  have hfracΘ : ∀ z, ∃ a b, IsUnit (Θ b) ∧ z * Θ b = Θ a := by
    intro z
    obtain ⟨a, b, ha, hb, hbu, hzb⟩ := IsCanonicalLift.exists_isUnit_mul_eq_of_mapsRSOP α hα t tb β hβ z
    obtain ⟨a', rfl⟩ := hrange ha
    obtain ⟨b', rfl⟩ := hrange hb
    exact ⟨a', b', hbu, hzb⟩
  refine ⟨Θ.toRingHom, hΘ, hΘinj, hfracΘ, ?_⟩
  -- the closed fibre `Q = R̄'/M_{R'}R̄'` and `Ψ : k' ⊗_k k̄ → Q`
  set I := (maximalIdeal t.ring).map β with hIdef
  have hI : I ≤ maximalIdeal tb.ring :=
    Ideal.map_le_iff_le_comap.mpr fun a ha => map_nonunit β a ha
  have : IsLocalRing (tb.ring ⧸ I) := isLocalRing_quotient_of_le hI
  set mk := Ideal.Quotient.mk I
  have hMb : ∀ r ∈ maximalIdeal Rb, (mk.comp tb.toRing) r = 0 := by
    intro r hr
    rw [RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem]
    rw [← RingHom.MapsRSOP.map_maximalIdeal hα] at hr
    have h1 : tb.toRing r ∈ ((maximalIdeal R).map α).map tb.toRing := Ideal.mem_map_of_mem _ hr
    rw [Ideal.map_map, ← hβ.comm, ← Ideal.map_map] at h1
    have hloc : (maximalIdeal R).map t.toRing ≤ maximalIdeal t.ring :=
      Ideal.map_le_iff_le_comap.mpr fun a ha => map_nonunit t.toRing a ha
    exact Ideal.map_mono hloc h1
  let f₀ : ResidueField t.ring →+* tb.ring ⧸ I := Ideal.Quotient.lift (maximalIdeal t.ring)
    (mk.comp β) (fun a ha => Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_map_of_mem β ha))
  let g₀ : ResidueField Rb →+* tb.ring ⧸ I :=
    Ideal.Quotient.lift (maximalIdeal Rb) (mk.comp tb.toRing) hMb
  let _ : Algebra (ResidueField R) (tb.ring ⧸ I) :=
    (g₀.comp (algebraMap (ResidueField R) (ResidueField Rb))).toAlgebra
  have hf₀ : ∀ c, f₀ (algebraMap (ResidueField R) (ResidueField t.ring) c) =
      algebraMap (ResidueField R) (tb.ring ⧸ I) c := by
    intro c
    obtain ⟨r, rfl⟩ := residue_surjective c
    show f₀ (algebraMap _ _ (residue R r)) = g₀ (algebraMap _ _ (residue R r))
    rw [ResidueField.algebraMap_residue, ResidueField.algebraMap_residue]
    show mk (β (t.toRing r)) = mk (tb.toRing (α r))
    rw [hcomm]
  let f : ResidueField t.ring →ₐ[ResidueField R] tb.ring ⧸ I := { f₀ with commutes' := hf₀ }
  let g : ResidueField Rb →ₐ[ResidueField R] tb.ring ⧸ I := { g₀ with commutes' := fun _ => rfl }
  let Ψ := Algebra.TensorProduct.productMap f g
  have hΨπ : ∀ z, Ψ (residueTensorHom α t z) = mk (Θ z) := by
    intro z
    induction z with
    | tmul y r =>
      rw [residueTensorHom_tmul, Algebra.TensorProduct.productMap_apply_tmul, hΘ, map_mul]
      rfl
    | add z z' hz hz' => rw [map_add, map_add, map_add, hz, hz', map_add]
  have hmk : ∀ w, mk w ∈ maximalIdeal (tb.ring ⧸ I) ↔ w ∈ maximalIdeal tb.ring := by
    intro w
    constructor
    · intro h
      by_contra hw
      exact (IsLocalRing.mem_maximalIdeal _).mp h ((IsLocalRing.notMem_maximalIdeal.mp hw).map mk)
    · intro h
      rw [← map_maximalIdeal_of_surjective mk Ideal.Quotient.mk_surjective]
      exact Ideal.mem_map_of_mem _ h
  set 𝔭 := (maximalIdeal (tb.ring ⧸ I)).comap Ψ.toRingHom with h𝔭def
  have h𝔭 : ∀ z, Θ z ∈ maximalIdeal tb.ring ↔ residueTensorHom α t z ∈ 𝔭 := by
    intro z
    show _ ↔ Ψ (residueTensorHom α t z) ∈ maximalIdeal (tb.ring ⧸ I)
    rw [hΨπ, hmk]
  refine ⟨𝔭, inferInstance, h𝔭, ?_⟩
  -- `Ψ` induces `(k' ⊗_k k̄)_q̄ → Q`, which is surjective ...
  let Ψ𝔭 : Localization.AtPrime 𝔭 →+* tb.ring ⧸ I :=
    IsLocalization.lift (M := 𝔭.primeCompl) (g := Ψ.toRingHom)
      fun y => IsLocalRing.notMem_maximalIdeal.mp y.2
  have hsurj : Function.Surjective Ψ𝔭 := by
    intro q
    obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective q
    obtain ⟨a, b, hbu, hzb⟩ := hfracΘ z
    have hb : residueTensorHom α t b ∈ 𝔭.primeCompl := fun h =>
      (IsLocalRing.mem_maximalIdeal _).mp ((h𝔭 b).mpr h) hbu
    refine ⟨IsLocalization.mk' _ (residueTensorHom α t a) ⟨_, hb⟩, ?_⟩
    rw [IsLocalization.lift_mk'_spec]
    show Ψ (residueTensorHom α t a) = Ψ (residueTensorHom α t b) * mk z
    rw [hΨπ, hΨπ, ← map_mul, mul_comm, hzb]
  -- ... and injective: an inverse is induced by `R̄' = (R' ⊗_R R̄)_q → (k' ⊗_k k̄)_q̄`
  let _ : Algebra (t.ring ⊗[R] Rb) tb.ring := Θ.toRingHom.toAlgebra
  have hloc : IsLocalization.AtPrime tb.ring ((maximalIdeal tb.ring).comap Θ.toRingHom) :=
    isLocalization_comap_maximalIdeal_of_injective Θ.toRingHom hΘinj hfracΘ
  let ρ : tb.ring →+* Localization.AtPrime 𝔭 :=
    IsLocalization.lift (M := ((maximalIdeal tb.ring).comap Θ.toRingHom).primeCompl)
      (S := tb.ring) (g := (algebraMap _ (Localization.AtPrime 𝔭)).comp (residueTensorHom α t))
      fun y => IsLocalization.map_units (M := 𝔭.primeCompl) (Localization.AtPrime 𝔭)
        ⟨residueTensorHom α t y, fun h => y.2 ((h𝔭 y).mpr h)⟩
  have hρ : ∀ z, ρ (Θ z) = algebraMap _ (Localization.AtPrime 𝔭) (residueTensorHom α t z) :=
    fun z => IsLocalization.lift_eq _ z
  have hρI : ∀ a ∈ I, ρ a = 0 := by
    intro a ha
    have hle : I ≤ RingHom.ker ρ := by
      refine (Ideal.map_le_iff_le_comap (f := β) (K := RingHom.ker ρ)).mpr ?_
      intro y hy
      rw [Ideal.mem_comap, RingHom.mem_ker]
      have : β y = Θ (y ⊗ₜ 1) := by rw [hΘ, map_one, mul_one]
      rw [this, hρ, residueTensorHom_tmul, (residue_eq_zero_iff y).mpr hy,
        TensorProduct.zero_tmul, map_zero]
    exact hle ha
  let ρ' : tb.ring ⧸ I →+* Localization.AtPrime 𝔭 := Ideal.Quotient.lift I ρ hρI
  have hleft : Function.LeftInverse ρ' Ψ𝔭 := by
    have : ρ'.comp Ψ𝔭 = RingHom.id _ := IsLocalization.ringHom_ext 𝔭.primeCompl
      (RingHom.ext fun a => by
        obtain ⟨z, rfl⟩ := residueTensorHom_surjective α t a
        rw [RingHom.comp_apply, RingHom.comp_apply, RingHom.comp_apply, RingHom.id_apply,
          IsLocalization.lift_eq]
        show ρ' (Ψ (residueTensorHom α t z)) = _
        rw [hΨπ]
        exact hρ z)
    exact fun w => RingHom.congr_fun this w
  exact ⟨(RingEquiv.ofBijective Ψ𝔭 ⟨hleft.injective, hsurj⟩).symm⟩

/-- **Lean-only infrastructure** (not a statement of the paper; used by `height_maximalIdeal_eq_add`,
`ringKrullDim_le`, `Compat/CanonicalLiftResidue.lean` and `Ch3/SequenceLift.lean`, not by Lemma 4):
the canonical homomorphism `β : R' → R̄'` is flat: `R̄'` is a localization of
`R' ⊗_R R̄` (`IsCanonicalLift.exists_tensorHom_injective_and_isFraction_and_quotient_equiv`), which is flat over `R'` because `R̄` is flat over `R`. -/
theorem IsCanonicalLift.flat_of_mapsRSOP (α : R →+* Rb) [IsLocalHom α] (hα : RingHom.MapsRSOP α) {P : Ideal R}
    (t : MonoidalTransform R P) (tb : MonoidalTransform Rb (P.map α)) (β : t.ring →+* tb.ring)
    (hβ : IsCanonicalLift α t tb β) :
    letI := β.toAlgebra
    Module.Flat t.ring tb.ring := by
  let _ : Algebra R Rb := α.toAlgebra
  let _ : Algebra R t.ring := t.toRing.toAlgebra
  have : IsLocalHom (algebraMap R Rb) := inferInstanceAs (IsLocalHom α)
  have : IsLocalHom (algebraMap R t.ring) := t.isLocalHom_toRing
  have : Module.Flat R Rb := hα.flat
  obtain ⟨Θ, hΘ, hΘinj, hfracΘ, -⟩ := IsCanonicalLift.exists_tensorHom_injective_and_isFraction_and_quotient_equiv α hα t tb β hβ
  let _ : Algebra (t.ring ⊗[R] Rb) tb.ring := Θ.toAlgebra
  have : IsLocalization.AtPrime tb.ring ((maximalIdeal tb.ring).comap Θ) :=
    isLocalization_comap_maximalIdeal_of_injective Θ hΘinj hfracΘ
  have : Module.Flat (t.ring ⊗[R] Rb) tb.ring :=
    IsLocalization.flat tb.ring ((maximalIdeal tb.ring).comap Θ).primeCompl
  let _ : Algebra t.ring tb.ring := β.toAlgebra
  have : IsScalarTower t.ring (t.ring ⊗[R] Rb) tb.ring := IsScalarTower.of_algebraMap_eq fun y => by
    show β y = Θ (algebraMap t.ring (t.ring ⊗[R] Rb) y)
    rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply, hΘ,
      map_one, mul_one]
  exact Module.Flat.trans t.ring (t.ring ⊗[R] Rb) tb.ring

/-- **Lean-only infrastructure** (this formula is not printed in the paper; Lemma 4 (1) gets
`dim R̄' = dim R'` from the count of pp. 210-212 instead): `dim R̄' = dim R' + dim R̄'/M_{R'}R̄'` (going
down for the flat local homomorphism `β`, `IsCanonicalLift.flat_of_mapsRSOP`). -/
theorem IsCanonicalLift.height_maximalIdeal_eq_add (α : R →+* Rb) [IsLocalHom α] (hα : RingHom.MapsRSOP α)
    {P : Ideal R} (t : MonoidalTransform R P) (tb : MonoidalTransform Rb (P.map α))
    (β : t.ring →+* tb.ring) (hβ : IsCanonicalLift α t tb β) :
    (maximalIdeal tb.ring).height = (maximalIdeal t.ring).height +
      ((maximalIdeal tb.ring).map (Ideal.Quotient.mk ((maximalIdeal t.ring).map β))).height := by
  let _ : Algebra t.ring tb.ring := β.toAlgebra
  have := hβ.isLocalHom
  have : Module.Flat t.ring tb.ring := IsCanonicalLift.flat_of_mapsRSOP α hα t tb β hβ
  have : IsNoetherianRing t.ring := MonoidalTransform.isNoetherianRing t
  have : IsNoetherianRing tb.ring := MonoidalTransform.isNoetherianRing tb
  have : (maximalIdeal tb.ring).LiesOver (maximalIdeal t.ring) :=
    ⟨(IsLocalRing.maximalIdeal_comap β).symm⟩
  exact Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown (maximalIdeal t.ring)
    (maximalIdeal tb.ring)

/-- **Lean-only infrastructure** (used by `Compat/CanonicalLiftResidue.lean`; Lemma 4 (1) proves
`dim R̄' = dim R'` by the count of pp. 210-212): `dim R' ≤ dim R̄'` for a canonical lift `R' → R̄'`
(going down, `IsCanonicalLift.height_maximalIdeal_eq_add`). -/
theorem IsCanonicalLift.ringKrullDim_le (α : R →+* Rb) [IsLocalHom α] (hα : RingHom.MapsRSOP α)
    {P : Ideal R} (t : MonoidalTransform R P) (tb : MonoidalTransform Rb (P.map α))
    (β : t.ring →+* tb.ring) (hβ : IsCanonicalLift α t tb β) :
    ringKrullDim t.ring ≤ ringKrullDim tb.ring := by
  have : IsNoetherianRing t.ring := MonoidalTransform.isNoetherianRing t
  have : IsNoetherianRing tb.ring := MonoidalTransform.isNoetherianRing tb
  rw [← IsLocalRing.maximalIdeal_height_eq_ringKrullDim,
    ← IsLocalRing.maximalIdeal_height_eq_ringKrullDim,
    IsCanonicalLift.height_maximalIdeal_eq_add α hα t tb β hβ]
  exact_mod_cast le_self_add

/-- The residue field `k'` of a monoidal transform `R' = R[x⁻¹P]_{M'}` is finitely generated
over the residue field `k` of `R`: it is the field of fractions of `R[x⁻¹P]/M'`, generated by the
classes of finitely many `p/x`. -/
theorem MonoidalTransform.fg_top_residueField {P : Ideal R} (t : MonoidalTransform R P) :
    letI : Algebra R t.ring := t.toRing.toAlgebra
    haveI : IsLocalHom (algebraMap R t.ring) := t.isLocalHom_toRing
    (⊤ : IntermediateField (ResidueField R) (ResidueField t.ring)).FG := by
  classical
  let _ : Algebra R t.ring := t.toRing.toAlgebra
  have : IsLocalHom (algebraMap R t.ring) := t.isLocalHom_toRing
  obtain ⟨s, hs⟩ := MonoidalTransform.fg_blowupAlgebra t
  let g : blowupAlgebra R P t.x →+* ResidueField t.ring :=
    (residue t.ring).comp (algebraMap (blowupAlgebra R P t.x) t.ring)
  have hsA : ∀ y ∈ s, y ∈ blowupAlgebra R P t.x := fun y hy => hs ▸ Algebra.subset_adjoin hy
  let s' : Finset (ResidueField t.ring) := s.attach.image fun y => g ⟨y.1, hsA y.1 y.2⟩
  set F := IntermediateField.adjoin (ResidueField R) (s' : Set (ResidueField t.ring))
  have hg : ∀ a : blowupAlgebra R P t.x, g a ∈ F := by
    rintro ⟨a, ha⟩
    have ha' : a ∈ Algebra.adjoin R (s : Set (FractionRing R)) := by rw [hs]; exact ha
    revert ha
    induction ha' using Algebra.adjoin_induction with
    | mem y hy =>
      intro ha
      have hmem : g ⟨y, ha⟩ ∈ s' :=
        Finset.mem_image.mpr ⟨⟨y, hy⟩, Finset.mem_attach _ _, congrArg g (Subtype.ext rfl)⟩
      exact IntermediateField.subset_adjoin _ _ hmem
    | algebraMap r =>
      intro ha
      have h1 : (⟨algebraMap R (FractionRing R) r, ha⟩ : blowupAlgebra R P t.x) =
          algebraMap R (blowupAlgebra R P t.x) r := rfl
      have h2 : g (algebraMap R (blowupAlgebra R P t.x) r) =
          algebraMap (ResidueField R) (ResidueField t.ring) (residue R r) := by
        rw [ResidueField.algebraMap_residue]
        rfl
      rw [h1, h2]
      exact F.algebraMap_mem _
    | add y y' hy hy' ihy ihy' =>
      intro ha
      have hyA : y ∈ blowupAlgebra R P t.x := hs ▸ hy
      have hy'A : y' ∈ blowupAlgebra R P t.x := hs ▸ hy'
      have : (⟨y + y', ha⟩ : blowupAlgebra R P t.x) = ⟨y, hyA⟩ + ⟨y', hy'A⟩ := rfl
      rw [this, map_add]
      exact F.add_mem (ihy hyA) (ihy' hy'A)
    | mul y y' hy hy' ihy ihy' =>
      intro ha
      have hyA : y ∈ blowupAlgebra R P t.x := hs ▸ hy
      have hy'A : y' ∈ blowupAlgebra R P t.x := hs ▸ hy'
      have : (⟨y * y', ha⟩ : blowupAlgebra R P t.x) = ⟨y, hyA⟩ * ⟨y', hy'A⟩ := rfl
      rw [this, map_mul]
      exact F.mul_mem (ihy hyA) (ihy' hy'A)
  refine ⟨s', ?_⟩
  rw [eq_top_iff]
  intro ζ _
  obtain ⟨z, rfl⟩ := residue_surjective ζ
  obtain ⟨⟨a, b⟩, hz⟩ := IsLocalization.mk'_surjective t.M'.primeCompl z
  have hb0 : g b ≠ 0 := by
    intro h
    rw [RingHom.comp_apply, residue_eq_zero_iff] at h
    exact b.2 ((IsLocalization.AtPrime.to_map_mem_maximal_iff t.ring t.M' _).mp h)
  have : residue t.ring z = g a / g b := by
    rw [eq_div_iff hb0, ← hz]
    show residue _ (IsLocalization.mk' t.ring a b) *
      residue _ (algebraMap _ t.ring (b : blowupAlgebra R P t.x)) = residue _ (algebraMap _ _ a)
    rw [← map_mul, IsLocalization.mk'_spec]
  rw [this]
  exact F.div_mem (hg a) (hg b)

/-- p. 212: if `R̄` is residually separable over `R`, the closed fibre `R̄'/M_{R'}R̄'` is a regular
local ring (it is a localization of `k' ⊗_k k̄`). -/
theorem IsCanonicalLift.isRegularLocalRing_quotient_map_maximalIdeal (α : R →+* Rb) [IsLocalHom α] (hα : RingHom.MapsRSOP α)
    {P : Ideal R} (t : MonoidalTransform R P) (tb : MonoidalTransform Rb (P.map α))
    (β : t.ring →+* tb.ring) (hβ : IsCanonicalLift α t tb β)
    (hsep : RingHom.IsResiduallySeparable α) :
    IsRegularLocalRing (tb.ring ⧸ (maximalIdeal t.ring).map β) := by
  let _ : Algebra R Rb := α.toAlgebra
  let _ : Algebra R t.ring := t.toRing.toAlgebra
  have : IsLocalHom (algebraMap R Rb) := inferInstanceAs (IsLocalHom α)
  have : IsLocalHom (algebraMap R t.ring) := t.isLocalHom_toRing
  obtain ⟨Θ, -, -, -, 𝔭, h𝔭, -, ⟨e⟩⟩ := IsCanonicalLift.exists_tensorHom_injective_and_isFraction_and_quotient_equiv α hα t tb β hβ
  have hK := MonoidalTransform.fg_top_residueField t
  have heq : (ResidueField.map α).toAlgebra =
      (inferInstance : Algebra (ResidueField R) (ResidueField Rb)) := by
    ext c
    obtain ⟨r, rfl⟩ := residue_surjective c
    rfl
  have hL : ∀ (k' : Type u) [Field k'] [Algebra (ResidueField R) k'],
      IsPurelyInseparable (ResidueField R) k' → IsReduced (ResidueField Rb ⊗[ResidueField R] k') := by
    unfold RingHom.IsResiduallySeparable at hsep
    rw [heq] at hsep
    exact hsep
  have := isRegularLocalRing_localization_tensorProduct_of_separable (ResidueField R)
    (ResidueField t.ring) (ResidueField Rb) hL hK 𝔭
  exact IsRegularLocalRing.of_ringEquiv e.symm

/-! #### Lemma 4, the printed route (pp. 210–212): the charts `A'`, `Ã'` and the primes `M̃'`

The polynomial rings `k[X₂,…,X_r]`, `k̃[X₂,…,X_r]`, the correspondence of the primes `M̃'` of `Ã'` over
`M'` with the monoidal transforms `R̃'` admitting a canonical local homomorphism `R' → R̃'`, finiteness,
and the dimension count. -/

section L4PrintedRoute

open MvPolynomial

section Lemma4Redo

variable {R Rb : Type u} [CommRing R] [IsRegularLocalRing R] [IsDomain R]
  [CommRing Rb] [IsRegularLocalRing Rb] [IsDomain Rb]

omit [IsRegularLocalRing R] [IsRegularLocalRing Rb] in
/-- The field homomorphism `Frac(α) : Frac(R) → Frac(R̄)` induced by an injective `α : R → R̄`. -/
noncomputable def fractionRingMap (α : R →+* Rb) (hα : Function.Injective α) :
    FractionRing R →+* FractionRing Rb :=
  IsFractionRing.map hα

omit [IsRegularLocalRing R] [IsRegularLocalRing Rb] [IsDomain R] in
theorem fractionRingMap_algebraMap (α : R →+* Rb) (hα : Function.Injective α) (r : R) :
    fractionRingMap α hα (algebraMap R (FractionRing R) r) =
      algebraMap Rb (FractionRing Rb) (α r) := by
  unfold fractionRingMap IsFractionRing.map
  exact IsLocalization.map_eq _ r

theorem fractionRingMap_mem_blowupAlgebra (α : R →+* Rb) (hα : Function.Injective α)
    {P : Ideal R} {x : R} {a : FractionRing R} (ha : a ∈ blowupAlgebra R P x) :
    fractionRingMap α hα a ∈ blowupAlgebra Rb (P.map α) (α x) := by
  induction ha using Algebra.adjoin_induction with
  | mem y hy =>
    obtain ⟨p, hp, rfl⟩ := hy
    rw [map_div₀, fractionRingMap_algebraMap, fractionRingMap_algebraMap]
    exact Algebra.subset_adjoin ⟨α p, Ideal.mem_map_of_mem α hp, rfl⟩
  | algebraMap r =>
    rw [fractionRingMap_algebraMap]
    exact Subalgebra.algebraMap_mem _ _
  | add y z _ _ hy hz => rw [map_add]; exact add_mem hy hz
  | mul y z _ _ hy hz => rw [map_mul]; exact mul_mem hy hz

/-- p. 211: "The homomorphism `A' → Ã'` induced by `α`" (`A' = R[x⁻¹P]`, `Ã' = R̄[α(x)⁻¹ P̄]`). -/
noncomputable def blowupMap (α : R →+* Rb) (hα : Function.Injective α) (P : Ideal R) (x : R) :
    blowupAlgebra R P x →+* blowupAlgebra Rb (P.map α) (α x) :=
  ((fractionRingMap α hα).comp (blowupAlgebra R P x).val.toRingHom).codRestrict
    (blowupAlgebra Rb (P.map α) (α x)) fun a => fractionRingMap_mem_blowupAlgebra α hα a.2

theorem blowupMap_coe (α : R →+* Rb) (hα : Function.Injective α) (P : Ideal R) (x : R)
    (a : blowupAlgebra R P x) :
    ((blowupMap α hα P x a : blowupAlgebra Rb (P.map α) (α x)) : FractionRing Rb) =
      fractionRingMap α hα (a : FractionRing R) := rfl

theorem blowupMap_algebraMap (α : R →+* Rb) (hα : Function.Injective α) (P : Ideal R) (x : R)
    (r : R) :
    blowupMap α hα P x (algebraMap R (blowupAlgebra R P x) r) =
      algebraMap Rb (blowupAlgebra Rb (P.map α) (α x)) (α r) := by
  apply Subtype.ext
  rw [blowupMap_coe]
  exact fractionRingMap_algebraMap α hα r

/-- Pure algebra (the printed correspondence "by the natural homomorphism of `Ã'` onto
`k̃[X₂,…,X_r]`", p. 211): for surjections `π : A → B`, `π' : Ã → B'` compatible with `a : A → Ã` and
`ι : B → B'`, an ideal `M'` of `A` containing `ker π` and an ideal `M` of `Ã` containing `ker π'`,
`a⁻¹(M) = M'` iff `ι⁻¹(π'(M)) = π(M')`. -/
theorem comap_eq_iff_comap_map_eq {A Ã B B' : Type*} [CommRing A] [CommRing Ã] [CommRing B]
    [CommRing B'] (a : A →+* Ã) (π : A →+* B) (π' : Ã →+* B') (ι : B →+* B')
    (hπ : Function.Surjective π) (hπ' : Function.Surjective π') (hcomm : π'.comp a = ι.comp π)
    {M' : Ideal A} (hM' : RingHom.ker π ≤ M') {M : Ideal Ã} (hM : RingHom.ker π' ≤ M) :
    M.comap a = M' ↔ (M.map π').comap ι = M'.map π := by
  have h1 : M = (M.map π').comap π' := by
    rw [Ideal.comap_map_of_surjective _ hπ', ← RingHom.ker_eq_comap_bot, sup_eq_left.mpr hM]
  have h2 : M' = (M'.map π).comap π := by
    rw [Ideal.comap_map_of_surjective _ hπ, ← RingHom.ker_eq_comap_bot, sup_eq_left.mpr hM']
  have h3 : M.comap a = ((M.map π').comap ι).comap π := by
    conv_lhs => rw [h1]
    rw [Ideal.comap_comap, hcomm, ← Ideal.comap_comap]
  constructor
  · intro h
    rw [h3] at h
    have := congrArg (Ideal.map π) h
    rwa [Ideal.map_comap_of_surjective _ hπ] at this
  · intro h
    rw [h3, h, ← h2]

variable {P : Ideal R}

/-- pp. 210-211: the two charts `A'/(x₁)A' ≅ S[X₂,…,X_r]` and `Ã'/(α(x₁))Ã' ≅ S̃[X₂,…,X_r]` (`S = R/P`,
`S̃ = R̄/P̄`) are compatible with the homomorphism `A' → Ã'` induced by `α` and with `S → S̃` ("`X_j`
into itself"). -/
theorem MonoidalTransform.exists_chart_comparison (α : R →+* Rb) [IsLocalHom α]
    (hα : RingHom.MapsRSOP α) (hP : P.IsPrime) (hS : IsRegularLocalRing (R ⧸ P))
    (t : MonoidalTransform R P) :
    ∃ (r : ℕ) (χ : blowupAlgebra R P t.x →+* MvPolynomial (Fin r) (R ⧸ P))
      (χb : blowupAlgebra Rb (P.map α) (α t.x) →+* MvPolynomial (Fin r) (Rb ⧸ P.map α)),
      Function.Surjective χ ∧
      RingHom.ker χ = Ideal.span {algebraMap R (blowupAlgebra R P t.x) t.x} ∧
      (∀ c : R, χ (algebraMap R (blowupAlgebra R P t.x) c) = C (Ideal.Quotient.mk P c)) ∧
      Function.Surjective χb ∧
      RingHom.ker χb = Ideal.span {algebraMap Rb (blowupAlgebra Rb (P.map α) (α t.x)) (α t.x)} ∧
      (∀ c : Rb, χb (algebraMap Rb (blowupAlgebra Rb (P.map α) (α t.x)) c) =
        C (Ideal.Quotient.mk (P.map α) c)) ∧
      ∀ a, χb (blowupMap α (RingHom.MapsRSOP.injective α hα) P t.x a) =
        MvPolynomial.map (Ideal.quotientMap (P.map α) α Ideal.le_comap_map) (χ a) := by
  classical
  have hαinj := RingHom.MapsRSOP.injective α hα
  have hPb := (RingHom.MapsRSOP.isPrime_map_and_isRegularLocalRing_quotient hα hP hS).1
  obtain ⟨S, r, z, hSM, hScard, hinj, hzS, hz0, hzP⟩ := t.exists_minimal_generators hS
  obtain ⟨χ, hχ, hχx, hχC, hχX⟩ := t.exists_chart hSM hScard hinj hzS hz0 hzP
  have hSrsop : IsRegularSystemOfParameters R S :=
    ⟨hSM, by rw [hScard]; exact IsRegularLocalRing.spanFinrank_maximalIdeal⟩
  obtain ⟨hSb, hScardb⟩ := RingHom.MapsRSOP.isRegularSystemOfParameters_image hα hSrsop
  have hSbcard : (S.image α).card = (maximalIdeal Rb).spanFinrank := by
    have h1 := hSb.2
    rw [IsRegularLocalRing.spanFinrank_maximalIdeal.symm] at h1
    exact_mod_cast h1
  have hx0b : α t.x ≠ 0 := (map_ne_zero_iff _ hαinj).mpr t.x_ne_zero
  obtain ⟨χb, hχb, hχbx, hχbC, hχbX⟩ := exists_chart_of_mem (P := P.map α)
    (Ideal.mem_map_of_mem α t.x_mem) hx0b (S := S.image α) (z := fun i => α (z i)) hSb.1
    hSbcard (fun i j h => hinj (hαinj h)) (fun i => Finset.mem_image_of_mem _ (hzS i))
    (by rw [hz0]) (by rw [← hzP, Ideal.map_span, ← Set.range_comp]; rfl)
  refine ⟨r, χ, χb, hχ, hχx, hχC, hχb, hχbx, hχbC, ?_⟩
  -- the two ring homomorphisms `A' → S̃[X]` agree
  set g : Fin r → FractionRing R := fun i => algebraMap R (FractionRing R) (z i.succ) /
    algebraMap R (FractionRing R) t.x with hg
  have hgA : ∀ i, g i ∈ blowupAlgebra R P t.x := fun i =>
    Algebra.subset_adjoin ⟨z i.succ, hzP ▸ Ideal.subset_span ⟨i.succ, rfl⟩, rfl⟩
  let Φ : MvPolynomial (Fin r) R →ₐ[R] blowupAlgebra R P t.x :=
    aeval fun i => (⟨g i, hgA i⟩ : blowupAlgebra R P t.x)
  have hΦK : ∀ F, (Φ F : FractionRing R) = aeval g F := by
    intro F
    have := congrArg (fun φ : MvPolynomial (Fin r) R →ₐ[R] FractionRing R => φ F)
      (MvPolynomial.comp_aeval (R := R) (fun i => (⟨g i, hgA i⟩ : blowupAlgebra R P t.x))
        (blowupAlgebra R P t.x).val)
    simpa using this
  have hmain : ∀ F : MvPolynomial (Fin r) R,
      χb (blowupMap α hαinj P t.x (Φ F)) =
        MvPolynomial.map (Ideal.quotientMap (P.map α) α Ideal.le_comap_map) (χ (Φ F)) := by
    intro F
    induction F using MvPolynomial.induction_on with
    | C c =>
      have h1 : Φ (C c) = algebraMap R (blowupAlgebra R P t.x) c := by
        rw [← MvPolynomial.algebraMap_eq, Φ.commutes]
      rw [h1, blowupMap_algebraMap, hχbC, hχC, MvPolynomial.map_C]
      simp
    | add p q hp hq => rw [map_add, map_add, map_add, hp, hq, map_add, map_add]
    | mul_X p i hp =>
      have h1 : Φ (X i) = ⟨g i, hgA i⟩ := by simp [Φ]
      have h2 := hχX i ⟨g i, hgA i⟩ rfl
      have h3 : χb (blowupMap α hαinj P t.x ⟨g i, hgA i⟩) = X i := by
        apply hχbX i
        show fractionRingMap α hαinj (g i) = _
        simp only [hg, map_div₀, fractionRingMap_algebraMap]
      simp only [map_mul, hp, h1, h2, h3, MvPolynomial.map_X]
  intro a
  obtain ⟨F, hF⟩ := exists_aeval_eq_of_mem_blowupAlgebra (P := P) t.x_ne_zero hz0 hzP a.2
  have : a = Φ F := Subtype.ext ((hΦK F).trans hF).symm
  rw [this]
  exact hmain F

end Lemma4Redo

section Lemma4Redo

variable {R Rb : Type u} [CommRing R] [IsRegularLocalRing R] [IsDomain R]
  [CommRing Rb] [IsRegularLocalRing Rb] [IsDomain Rb] {P : Ideal R}

/-- The primes `M̃'` of `Ã' = R̄[α(x)⁻¹P̄]` lying over `M'`: the candidates for the `R̃' = Ã'_{M̃'}`
admitting a canonical local homomorphism `R' → R̃'` (p. 211: "if `M̃'` is an associated prime ideal of
`M'Ã'`, then we have a canonical local homomorphism of `R' = A'_{M'}` into `R̃' = Ã'_{M̃'}`"). -/
def LiftPrimes (α : R →+* Rb) (hα : Function.Injective α) (t : MonoidalTransform R P) :
    Set (Ideal (blowupAlgebra Rb (P.map α) (α t.x))) :=
  {N | N.IsPrime ∧ N.comap (blowupMap α hα P t.x) = t.M'}

/-- The monoidal transform `R̃' = Ã'_{M̃'}` of `R̄` with center `P̄` attached to a prime `M̃'` of
`Ã'` over `M'` (p. 211). -/
noncomputable def MonoidalTransform.ofLift (α : R →+* Rb) [IsLocalHom α] (hα : RingHom.MapsRSOP α)
    (t : MonoidalTransform R P) (N : Ideal (blowupAlgebra Rb (P.map α) (α t.x)))
    (hN : N ∈ LiftPrimes α (RingHom.MapsRSOP.injective α hα) t) :
    MonoidalTransform Rb (P.map α) where
  x := α t.x
  x_mem := Ideal.mem_map_of_mem α t.x_mem
  x_ne_zero := (map_ne_zero_iff _ (RingHom.MapsRSOP.injective α hα)).mpr t.x_ne_zero
  M' := N
  isPrime := hN.1
  le := by
    rw [← hα.map_maximalIdeal, Ideal.map_map, Ideal.map_le_iff_le_comap]
    intro m hm
    rw [Ideal.mem_comap, RingHom.comp_apply, ← blowupMap_algebraMap α
      (RingHom.MapsRSOP.injective α hα) P t.x m, ← Ideal.mem_comap, hN.2]
    exact t.le (Ideal.mem_map_of_mem _ hm)

/-- The canonical local homomorphism `R' = A'_{M'} → R̃' = Ã'_{M̃'}`. -/
noncomputable def MonoidalTransform.ofLiftHom (α : R →+* Rb) [IsLocalHom α]
    (hα : RingHom.MapsRSOP α) (t : MonoidalTransform R P)
    (N : Ideal (blowupAlgebra Rb (P.map α) (α t.x)))
    (hN : N ∈ LiftPrimes α (RingHom.MapsRSOP.injective α hα) t) :
    t.ring →+* (MonoidalTransform.ofLift α hα t N hN).ring :=
  have := hN.1
  Localization.localRingHom t.M' N (blowupMap α (RingHom.MapsRSOP.injective α hα) P t.x)
    hN.2.symm

theorem MonoidalTransform.isCanonicalLift_ofLiftHom (α : R →+* Rb) [IsLocalHom α]
    (hα : RingHom.MapsRSOP α) (t : MonoidalTransform R P)
    (N : Ideal (blowupAlgebra Rb (P.map α) (α t.x)))
    (hN : N ∈ LiftPrimes α (RingHom.MapsRSOP.injective α hα) t) :
    IsCanonicalLift α t (MonoidalTransform.ofLift α hα t N hN)
      (MonoidalTransform.ofLiftHom α hα t N hN) := by
  have := hN.1
  refine ⟨Localization.isLocalHom_localRingHom t.M' N _ hN.2.symm, ?_⟩
  ext r
  have h := Localization.localRingHom_to_map t.M' N
    (blowupMap α (RingHom.MapsRSOP.injective α hα) P t.x) hN.2.symm
    (algebraMap R (blowupAlgebra R P t.x) r)
  rw [blowupMap_algebraMap] at h
  exact h

end Lemma4Redo

section PartC

variable {R Rb : Type u} [CommRing R] [IsRegularLocalRing R] [IsDomain R]
  [CommRing Rb] [IsRegularLocalRing Rb] [IsDomain Rb] {P : Ideal R}

/-- A canonical local homomorphism `β : R' → R̃'` is compatible with the embeddings of `R'` and `R̃'`
in the fields of quotients: `R̃' ⊆ Frac(R̄)` receives `R' ⊆ Frac(R)` through `Frac(α)`. -/
theorem MonoidalTransform.toFractionRing_map_eq_fractionRingMap (α : R →+* Rb) [IsLocalHom α]
    (hα : RingHom.MapsRSOP α) (t : MonoidalTransform R P) (tb : MonoidalTransform Rb (P.map α))
    (β : t.ring →+* tb.ring) (hβ : IsCanonicalLift α t tb β) (y : t.ring) :
    tb.toFractionRing (β y) =
      fractionRingMap α (RingHom.MapsRSOP.injective α hα) (t.toFractionRing y) := by
  obtain ⟨c, d, hd, hcd⟩ := t.exists_toRing_mul_eq y
  have hcomm : ∀ r, β (t.toRing r) = tb.toRing (α r) := fun r => RingHom.congr_fun hβ.comm r
  have h1 := congrArg (fun w => tb.toFractionRing (β w)) hcd
  simp only [map_mul, hcomm, tb.toFractionRing_toRing] at h1
  have h2 := congrArg (fun w => fractionRingMap α (RingHom.MapsRSOP.injective α hα)
    (t.toFractionRing w)) hcd
  simp only [map_mul, t.toFractionRing_toRing, fractionRingMap_algebraMap] at h2
  have hd' : algebraMap Rb (FractionRing Rb) (α d) ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr
      ((map_ne_zero_iff _ (RingHom.MapsRSOP.injective α hα)).mpr hd)
  exact mul_left_cancel₀ hd' (h1.trans h2.symm)

/-- p. 211: if `R̃' = R̄[x̃⁻¹P̄]_{N}` admits a canonical local homomorphism `R' → R̃'`, then
`α(x) = x̃ · u` with `u` a unit of `R̃'` (both `α(x)` and `x̃` generate `P̄R̃'`). -/
theorem MonoidalTransform.exists_isUnit_toRing_eq_xR_mul (α : R →+* Rb) [IsLocalHom α]
    (t : MonoidalTransform R P) (tb : MonoidalTransform Rb (P.map α))
    (β : t.ring →+* tb.ring) (hβ : IsCanonicalLift α t tb β) :
    ∃ u : tb.ring, IsUnit u ∧ tb.toRing (α t.x) = tb.xR * u := by
  have hxtb : tb.xR ≠ 0 := fun h =>
    tb.x_ne_zero (tb.toRing_injective (h.trans (map_zero _).symm))
  have h1 : tb.toRing (α t.x) ∈ Ideal.span {tb.xR} := by
    rw [tb.span_xR_eq_map]
    exact Ideal.mem_map_of_mem _ (Ideal.mem_map_of_mem α t.x_mem)
  obtain ⟨u, hu⟩ := Ideal.mem_span_singleton'.mp h1
  have h2 : tb.xR ∈ Ideal.span {tb.toRing (α t.x)} := by
    have h3 : tb.xR ∈ (P.map α).map tb.toRing := by
      rw [← tb.span_xR_eq_map]; exact Ideal.mem_span_singleton_self _
    have h4 : (P.map α).map tb.toRing = (P.map t.toRing).map β := by
      rw [Ideal.map_map, Ideal.map_map, ← hβ.comm]
    rw [h4, ← t.span_xR_eq_map, Ideal.map_span, Set.image_singleton] at h3
    have h5 : β t.xR = tb.toRing (α t.x) := RingHom.congr_fun hβ.comm t.x
    rwa [h5] at h3
  obtain ⟨w, hw⟩ := Ideal.mem_span_singleton'.mp h2
  refine ⟨u, isUnit_iff_exists_inv.mpr ⟨w, ?_⟩, by rw [mul_comm, hu]⟩
  apply mul_left_cancel₀ hxtb
  calc tb.xR * (u * w) = w * (u * tb.xR) := by ring
    _ = tb.xR * 1 := by rw [hu, hw, mul_one]

end PartC

section PartC2

variable {R Rb : Type u} [CommRing R] [IsRegularLocalRing R] [IsDomain R]
  [CommRing Rb] [IsRegularLocalRing Rb] [IsDomain Rb] {P : Ideal R}

/-- p. 211: `Ã' = R̄[α(x)⁻¹P̄]` lies in `R̃' ⊆ Frac(R̄)` whenever `R̃'` admits a canonical local
homomorphism from `R'` (`α(x)` generates `P̄R̃'`, so `p/α(x) ∈ R̃'` for `p ∈ P̄`). -/
theorem MonoidalTransform.blowupAlgebra_le_range_of_isCanonicalLift (α : R →+* Rb) [IsLocalHom α]
    (_hα : RingHom.MapsRSOP α) (t : MonoidalTransform R P) (tb : MonoidalTransform Rb (P.map α))
    (β : t.ring →+* tb.ring) (hβ : IsCanonicalLift α t tb β) :
    ∀ a ∈ blowupAlgebra Rb (P.map α) (α t.x), a ∈ tb.toFractionRing.range := by
  obtain ⟨u, hu, hxu⟩ := MonoidalTransform.exists_isUnit_toRing_eq_xR_mul α t tb β hβ
  have hFx : tb.toFractionRing tb.xR ≠ 0 := by
    intro h
    have := tb.injective_toFractionRing (h.trans (map_zero _).symm)
    exact tb.x_ne_zero (tb.toRing_injective (this.trans (map_zero _).symm))
  have hFu : tb.toFractionRing u * tb.toFractionRing (↑hu.unit⁻¹ : tb.ring) = 1 := by
    have h1 : u * (↑hu.unit⁻¹ : tb.ring) = 1 := by
      have := hu.unit.mul_inv
      rwa [IsUnit.unit_spec] at this
    rw [← map_mul, h1, map_one]
  have hFu0 : tb.toFractionRing u ≠ 0 := left_ne_zero_of_mul_eq_one hFu
  intro a ha
  induction ha using Algebra.adjoin_induction with
  | mem y hy =>
    obtain ⟨p, hp, rfl⟩ := hy
    have hp' : tb.toRing p ∈ Ideal.span {tb.xR} := by
      rw [tb.span_xR_eq_map]; exact Ideal.mem_map_of_mem _ hp
    obtain ⟨w, hw⟩ := Ideal.mem_span_singleton'.mp hp'
    refine ⟨w * ↑hu.unit⁻¹, ?_⟩
    have e1 : algebraMap Rb (FractionRing Rb) p =
        tb.toFractionRing tb.xR * tb.toFractionRing w := by
      rw [← tb.toFractionRing_toRing, ← hw, map_mul]; ring
    have e2 : algebraMap Rb (FractionRing Rb) (α t.x) =
        tb.toFractionRing tb.xR * tb.toFractionRing u := by
      rw [← tb.toFractionRing_toRing, hxu, map_mul]
    have e3 : tb.toFractionRing (↑hu.unit⁻¹ : tb.ring) = (tb.toFractionRing u)⁻¹ :=
      eq_inv_of_mul_eq_one_right hFu
    show tb.toFractionRing (w * ↑hu.unit⁻¹) =
      algebraMap Rb (FractionRing Rb) p / algebraMap Rb (FractionRing Rb) (α t.x)
    rw [map_mul, e3, e1, e2]
    field_simp
  | algebraMap r => exact ⟨tb.toRing r, tb.toFractionRing_toRing r⟩
  | add y z _ _ hy hz => exact add_mem hy hz
  | mul y z _ _ hy hz => exact mul_mem hy hz

/-- The embedding `Ã' → R̃'` (p. 211). -/
noncomputable def MonoidalTransform.blowupToRing (α : R →+* Rb) [IsLocalHom α]
    (hα : RingHom.MapsRSOP α) (t : MonoidalTransform R P) (tb : MonoidalTransform Rb (P.map α))
    (β : t.ring →+* tb.ring) (hβ : IsCanonicalLift α t tb β) :
    blowupAlgebra Rb (P.map α) (α t.x) →+* tb.ring :=
  tb.liftBlowupAlgebra (MonoidalTransform.blowupAlgebra_le_range_of_isCanonicalLift α hα t tb β hβ)

theorem MonoidalTransform.toFractionRing_blowupToRing (α : R →+* Rb) [IsLocalHom α]
    (hα : RingHom.MapsRSOP α) (t : MonoidalTransform R P) (tb : MonoidalTransform Rb (P.map α))
    (β : t.ring →+* tb.ring) (hβ : IsCanonicalLift α t tb β)
    (a : blowupAlgebra Rb (P.map α) (α t.x)) :
    tb.toFractionRing (MonoidalTransform.blowupToRing α hα t tb β hβ a) =
      (a : FractionRing Rb) :=
  tb.toFractionRing_liftBlowupAlgebra _ a

/-- The embedding `Ã' → R̃'` is compatible with `β : R' → R̃'` and `A' → Ã'`. -/
theorem MonoidalTransform.blowupToRing_blowupMap (α : R →+* Rb) [IsLocalHom α]
    (hα : RingHom.MapsRSOP α) (t : MonoidalTransform R P) (tb : MonoidalTransform Rb (P.map α))
    (β : t.ring →+* tb.ring) (hβ : IsCanonicalLift α t tb β) (a : blowupAlgebra R P t.x) :
    MonoidalTransform.blowupToRing α hα t tb β hβ
        (blowupMap α (RingHom.MapsRSOP.injective α hα) P t.x a) =
      β (algebraMap (blowupAlgebra R P t.x) t.ring a) := by
  apply tb.injective_toFractionRing
  rw [MonoidalTransform.toFractionRing_blowupToRing,
    MonoidalTransform.toFractionRing_map_eq_fractionRingMap α hα t tb β hβ,
    t.toFractionRing_algebraMap_blowupAlgebra]
  rfl

/-- The prime `M̃' = M_{R̃'} ∩ Ã'` of `Ã'` attached to a canonical lift `R' → R̃'` lies over `M'`
(p. 211). -/
theorem MonoidalTransform.comap_maximalIdeal_blowupToRing_mem_liftPrimes (α : R →+* Rb)
    [IsLocalHom α] (hα : RingHom.MapsRSOP α) (t : MonoidalTransform R P)
    (tb : MonoidalTransform Rb (P.map α)) (β : t.ring →+* tb.ring)
    (hβ : IsCanonicalLift α t tb β) :
    (maximalIdeal tb.ring).comap (MonoidalTransform.blowupToRing α hα t tb β hβ) ∈
      LiftPrimes α (RingHom.MapsRSOP.injective α hα) t := by
  have := hβ.isLocalHom
  refine ⟨Ideal.comap_isPrime _ _, ?_⟩
  have h := IsLocalization.AtPrime.under_maximalIdeal t.ring t.M'
  ext a
  rw [Ideal.mem_comap, Ideal.mem_comap, MonoidalTransform.blowupToRing_blowupMap, ← h,
    Ideal.mem_comap]
  simp only [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, isUnit_map_iff]

end PartC2

section PartC3

variable {R Rb : Type u} [CommRing R] [IsRegularLocalRing R] [IsDomain R]
  [CommRing Rb] [IsRegularLocalRing Rb] [IsDomain Rb] {P : Ideal R}

theorem MonoidalTransform.mem_ofLift_subring_iff (α : R →+* Rb) [IsLocalHom α]
    (hα : RingHom.MapsRSOP α) (t : MonoidalTransform R P)
    (N : Ideal (blowupAlgebra Rb (P.map α) (α t.x)))
    (hN : N ∈ LiftPrimes α (RingHom.MapsRSOP.injective α hα) t) (y : FractionRing Rb) :
    y ∈ (MonoidalTransform.ofLift α hα t N hN).subring ↔
      ∃ a s : blowupAlgebra Rb (P.map α) (α t.x), s ∉ N ∧ y * (s : FractionRing Rb) = a :=
  (MonoidalTransform.ofLift α hα t N hN).mem_subring_iff y

/-- p. 211, "can be obtained in this manner": a monoidal transform `R̃'` of `R̄` with center `P̄`
which admits a canonical local homomorphism `R' → R̃'` is the monoidal transform `Ã'_{M̃'}` for
the prime `M̃' = M_{R̃'} ∩ Ã'` of `Ã'` over `M'`, as subrings of `Frac(R̄)`. -/
theorem MonoidalTransform.subring_eq_ofLift_subring (α : R →+* Rb) [IsLocalHom α]
    (hα : RingHom.MapsRSOP α) (t : MonoidalTransform R P) (tb : MonoidalTransform Rb (P.map α))
    (β : t.ring →+* tb.ring) (hβ : IsCanonicalLift α t tb β) :
    tb.subring = (MonoidalTransform.ofLift α hα t
      ((maximalIdeal tb.ring).comap (MonoidalTransform.blowupToRing α hα t tb β hβ))
      (MonoidalTransform.comap_maximalIdeal_blowupToRing_mem_liftPrimes α hα t tb β hβ)).subring := by
  set j := MonoidalTransform.blowupToRing α hα t tb β hβ with hj
  set N := (maximalIdeal tb.ring).comap j with hN
  have hFj : ∀ a, tb.toFractionRing (j a) = (a : FractionRing Rb) := fun a =>
    MonoidalTransform.toFractionRing_blowupToRing α hα t tb β hβ a
  have hmem0 := MonoidalTransform.mem_ofLift_subring_iff α hα t N
      (MonoidalTransform.comap_maximalIdeal_blowupToRing_mem_liftPrimes α hα t tb β hβ)
  have hmem1 := tb.mem_subring_iff
  -- `s ∉ N` iff `j s` is a unit
  have hsN : ∀ s : blowupAlgebra Rb (P.map α) (α t.x), s ∉ N ↔ IsUnit (j s) := by
    intro s
    rw [hN, Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, not_not]
  ext y
  constructor
  · -- `R̃' ⊆ Ã'_{M̃'}`
    intro hy
    obtain ⟨a'', s'', hs'', hys⟩ := (hmem1 y).mp hy
    obtain ⟨u, hu, hxu⟩ := MonoidalTransform.exists_isUnit_toRing_eq_xR_mul α t tb β hβ
    have hx0 : algebraMap Rb (FractionRing Rb) (α t.x) ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr
        ((map_ne_zero_iff _ (RingHom.MapsRSOP.injective α hα)).mpr t.x_ne_zero)
    -- `v = x̃/α(x) ∈ Ã'`, a unit of `R̃'`
    set v : FractionRing Rb := algebraMap Rb (FractionRing Rb) tb.x /
      algebraMap Rb (FractionRing Rb) (α t.x) with hv
    have hvA : v ∈ blowupAlgebra Rb (P.map α) (α t.x) :=
      Algebra.subset_adjoin ⟨tb.x, tb.x_mem, rfl⟩
    set vA : blowupAlgebra Rb (P.map α) (α t.x) := ⟨v, hvA⟩ with hvA'
    have hFu : tb.toFractionRing u * tb.toFractionRing (↑hu.unit⁻¹ : tb.ring) = 1 := by
      have h1 : u * (↑hu.unit⁻¹ : tb.ring) = 1 := by
        have := hu.unit.mul_inv
        rwa [IsUnit.unit_spec] at this
      rw [← map_mul, h1, map_one]
    have he2 : algebraMap Rb (FractionRing Rb) (α t.x) =
        algebraMap Rb (FractionRing Rb) tb.x * tb.toFractionRing u := by
      rw [← tb.toFractionRing_toRing, hxu, map_mul,
        show tb.xR = tb.toRing tb.x from rfl, tb.toFractionRing_toRing]
    have hFuinv : tb.toFractionRing (↑hu.unit⁻¹ : tb.ring) = v := by
      have h0 : tb.toFractionRing u ≠ 0 := left_ne_zero_of_mul_eq_one hFu
      rw [hv, he2]
      have hxne : algebraMap Rb (FractionRing Rb) tb.x ≠ 0 := by
        intro h
        apply hx0
        rw [he2, h, zero_mul]
      field_simp
      have := hFu
      linear_combination this
    have hjv : j vA = ↑hu.unit⁻¹ := by
      apply tb.injective_toFractionRing
      rw [hFj, hFuinv]
    have hvN : vA ∉ N := (hsN vA).mpr (by rw [hjv]; exact Units.isUnit _)
    -- clearing denominators: `a'' v^k ∈ Ã'`
    have hclear : ∀ a ∈ blowupAlgebra Rb (P.map α) tb.x, ∃ k : ℕ,
        a * v ^ k ∈ blowupAlgebra Rb (P.map α) (α t.x) := by
      intro a ha
      induction ha using Algebra.adjoin_induction with
      | mem z hz =>
        obtain ⟨p, hp, rfl⟩ := hz
        refine ⟨1, ?_⟩
        have : algebraMap Rb (FractionRing Rb) p / algebraMap Rb (FractionRing Rb) tb.x * v ^ 1 =
            algebraMap Rb (FractionRing Rb) p / algebraMap Rb (FractionRing Rb) (α t.x) := by
          have hxne : algebraMap Rb (FractionRing Rb) tb.x ≠ 0 :=
            (map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr tb.x_ne_zero
          rw [hv]
          field_simp
        rw [this]
        exact Algebra.subset_adjoin ⟨p, hp, rfl⟩
      | algebraMap r =>
        exact ⟨0, by simp⟩
      | add z w _ _ hz hw =>
        obtain ⟨k₁, h₁⟩ := hz
        obtain ⟨k₂, h₂⟩ := hw
        refine ⟨k₁ + k₂, ?_⟩
        have : (z + w) * v ^ (k₁ + k₂) = z * v ^ k₁ * v ^ k₂ + w * v ^ k₂ * v ^ k₁ := by ring
        rw [this]
        exact add_mem (mul_mem h₁ (pow_mem hvA _)) (mul_mem h₂ (pow_mem hvA _))
      | mul z w _ _ hz hw =>
        obtain ⟨k₁, h₁⟩ := hz
        obtain ⟨k₂, h₂⟩ := hw
        refine ⟨k₁ + k₂, ?_⟩
        have : z * w * v ^ (k₁ + k₂) = (z * v ^ k₁) * (w * v ^ k₂) := by ring
        rw [this]
        exact mul_mem h₁ h₂
    obtain ⟨k₁, h₁⟩ := hclear _ a''.2
    obtain ⟨k₂, h₂⟩ := hclear _ s''.2
    have h₁' : (a'' : FractionRing Rb) * v ^ (k₁ + k₂) ∈ blowupAlgebra Rb (P.map α) (α t.x) := by
      rw [pow_add, ← mul_assoc]; exact mul_mem h₁ (pow_mem hvA _)
    have h₂' : (s'' : FractionRing Rb) * v ^ (k₁ + k₂) ∈ blowupAlgebra Rb (P.map α) (α t.x) := by
      rw [add_comm, pow_add, ← mul_assoc]; exact mul_mem h₂ (pow_mem hvA _)
    refine (hmem0 y).mpr ⟨⟨_, h₁'⟩, ⟨_, h₂'⟩, ?_, ?_⟩
    · rw [hsN]
      have hjs : j ⟨_, h₂'⟩ = algebraMap (blowupAlgebra Rb (P.map α) tb.x) tb.ring s'' *
          (↑hu.unit⁻¹ : tb.ring) ^ (k₁ + k₂) := by
        apply tb.injective_toFractionRing
        rw [hFj, map_mul, map_pow, hFuinv, tb.toFractionRing_algebraMap_blowupAlgebra]
      rw [hjs]
      exact (IsLocalization.map_units tb.ring (⟨s'', hs''⟩ : tb.M'.primeCompl)).mul
        ((Units.isUnit _).pow _)
    · show y * ((s'' : FractionRing Rb) * v ^ (k₁ + k₂)) = (a'' : FractionRing Rb) * v ^ (k₁ + k₂)
      rw [← mul_assoc, hys]
  · -- `Ã'_{M̃'} ⊆ R̃'`
    intro hy
    obtain ⟨a, s, hs, hys⟩ := (hmem0 y).mp hy
    have hsu : IsUnit (j s) := (hsN s).mp hs
    have hs0 : (s : FractionRing Rb) ≠ 0 := by
      rw [← hFj]; exact (hsu.map tb.toFractionRing).ne_zero
    refine ⟨j a * ↑hsu.unit⁻¹, ?_⟩
    have h1 : tb.toFractionRing (↑hsu.unit⁻¹ : tb.ring) * (s : FractionRing Rb) = 1 := by
      have := congrArg tb.toFractionRing hsu.unit.inv_mul
      rw [map_mul, IsUnit.unit_spec, hFj, map_one] at this
      simpa using this
    rw [map_mul, hFj]
    calc (a : FractionRing Rb) * tb.toFractionRing ↑hsu.unit⁻¹
        = y * (s : FractionRing Rb) * tb.toFractionRing ↑hsu.unit⁻¹ := by rw [hys]
      _ = y * (tb.toFractionRing ↑hsu.unit⁻¹ * (s : FractionRing Rb)) := by ring
      _ = y := by rw [h1, mul_one]

end PartC3

section PartC4

variable {S : Type u} [CommRing S] [IsRegularLocalRing S] [IsDomain S] {Q : Ideal S}

/-- For `a ∈ S[x⁻¹Q]`: `a` is a unit of `T` iff `a ≠ 0` and `a⁻¹ ∈ T` (inside `Frac(S)`). -/
theorem MonoidalTransform.isUnit_algebraMap_iff (T : MonoidalTransform S Q)
    (a : blowupAlgebra S Q T.x) :
    IsUnit (algebraMap (blowupAlgebra S Q T.x) T.ring a) ↔
      (a : FractionRing S) ≠ 0 ∧ (a : FractionRing S)⁻¹ ∈ T.subring := by
  constructor
  · intro hu
    have h1 := congrArg T.toFractionRing hu.unit.mul_inv
    rw [map_mul, IsUnit.unit_spec, T.toFractionRing_algebraMap_blowupAlgebra, map_one] at h1
    have ha0 : (a : FractionRing S) ≠ 0 := left_ne_zero_of_mul_eq_one h1
    refine ⟨ha0, ⟨↑hu.unit⁻¹, ?_⟩⟩
    exact eq_inv_of_mul_eq_one_right h1
  · rintro ⟨ha0, ⟨z, hz⟩⟩
    refine isUnit_iff_exists_inv.mpr ⟨z, ?_⟩
    apply T.injective_toFractionRing
    rw [map_mul, T.toFractionRing_algebraMap_blowupAlgebra, hz, map_one]
    exact mul_inv_cancel₀ ha0

/-- `M'` is the set of those `a ∈ S[x⁻¹Q]` which are not units of `T`. -/
theorem MonoidalTransform.mem_M'_iff (T : MonoidalTransform S Q) (a : blowupAlgebra S Q T.x) :
    a ∈ T.M' ↔ ¬ ((a : FractionRing S) ≠ 0 ∧ (a : FractionRing S)⁻¹ ∈ T.subring) := by
  rw [← T.isUnit_algebraMap_iff a, ← IsLocalization.AtPrime.to_map_mem_maximal_iff T.ring T.M' a,
    IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]

end PartC4

section PartC5

variable {R Rb : Type u} [CommRing R] [IsRegularLocalRing R] [IsDomain R]
  [CommRing Rb] [IsRegularLocalRing Rb] [IsDomain Rb] {P : Ideal R}

/-- The prime `M̃'` is determined by the subring `Ã'_{M̃'} ⊆ Frac(R̄)`: it is the set of non-units of
the subring lying in `Ã'`. (Hence `M̃' ↦ R̃'` is one to one.) -/
theorem MonoidalTransform.ofLift_subring_injective (α : R →+* Rb) [IsLocalHom α]
    (hα : RingHom.MapsRSOP α) (t : MonoidalTransform R P)
    {N₁ N₂ : Ideal (blowupAlgebra Rb (P.map α) (α t.x))}
    (h₁ : N₁ ∈ LiftPrimes α (RingHom.MapsRSOP.injective α hα) t)
    (h₂ : N₂ ∈ LiftPrimes α (RingHom.MapsRSOP.injective α hα) t)
    (h : (MonoidalTransform.ofLift α hα t N₁ h₁).subring =
      (MonoidalTransform.ofLift α hα t N₂ h₂).subring) : N₁ = N₂ := by
  have key : ∀ (N : Ideal (blowupAlgebra Rb (P.map α) (α t.x)))
      (hN : N ∈ LiftPrimes α (RingHom.MapsRSOP.injective α hα) t) (a : blowupAlgebra Rb (P.map α) (α t.x)),
      a ∈ N ↔ ¬ ((a : FractionRing Rb) ≠ 0 ∧
        (a : FractionRing Rb)⁻¹ ∈ (MonoidalTransform.ofLift α hα t N hN).subring) := by
    intro N hN a
    exact (MonoidalTransform.ofLift α hα t N hN).mem_M'_iff a
  ext a
  rw [key N₁ h₁, key N₂ h₂, h]

end PartC5

section PartC6

variable {R Rb : Type u} [CommRing R] [IsRegularLocalRing R] [IsDomain R]
  [CommRing Rb] [IsRegularLocalRing Rb] [IsDomain Rb] {P : Ideal R}

open Classical in
/-- The subring `R̃' = Ã'_{M̃'} ⊆ Frac(R̄)` attached to a prime `M̃'` of `Ã'` over `M'` (and `⊥` for the
other ideals). -/
noncomputable def liftSubring (α : R →+* Rb) [IsLocalHom α] (hα : RingHom.MapsRSOP α)
    (t : MonoidalTransform R P) (N : Ideal (blowupAlgebra Rb (P.map α) (α t.x))) :
    Subring (FractionRing Rb) :=
  if h : N ∈ LiftPrimes α (RingHom.MapsRSOP.injective α hα) t then
    (MonoidalTransform.ofLift α hα t N h).subring else ⊥

/-- p. 211, "one to one correspondence": the monoidal transforms `R̃'` of `R̄` with center `P̄` which
admit a canonical local homomorphism `R' → R̃'` are exactly the `Ã'_{M̃'}` for the primes `M̃'` of `Ã'`
over `M'`, and `M̃' ↦ Ã'_{M̃'}` is one to one. -/
theorem canonicalTransforms_eq_image_liftSubring (α : R →+* Rb) [IsLocalHom α]
    (hα : RingHom.MapsRSOP α) (t : MonoidalTransform R P) :
    canonicalTransforms α (Pb := P.map α) t =
      liftSubring α hα t '' LiftPrimes α (RingHom.MapsRSOP.injective α hα) t := by
  ext S
  constructor
  · rintro ⟨tb, ⟨β, hβ⟩, rfl⟩
    refine ⟨_, MonoidalTransform.comap_maximalIdeal_blowupToRing_mem_liftPrimes α hα t tb β hβ, ?_⟩
    rw [liftSubring, dite_eq_left (MonoidalTransform.comap_maximalIdeal_blowupToRing_mem_liftPrimes α hα t tb β hβ)]
    exact (MonoidalTransform.subring_eq_ofLift_subring α hα t tb β hβ).symm
  · rintro ⟨N, hN, rfl⟩
    refine ⟨MonoidalTransform.ofLift α hα t N hN,
      ⟨MonoidalTransform.ofLiftHom α hα t N hN,
        MonoidalTransform.isCanonicalLift_ofLiftHom α hα t N hN⟩, ?_⟩
    rw [liftSubring, dite_eq_left hN]

theorem injOn_liftSubring (α : R →+* Rb) [IsLocalHom α] (hα : RingHom.MapsRSOP α)
    (t : MonoidalTransform R P) :
    Set.InjOn (liftSubring α hα t) (LiftPrimes α (RingHom.MapsRSOP.injective α hα) t) := by
  intro N₁ h₁ N₂ h₂ h
  rw [liftSubring, dite_eq_left h₁, liftSubring, dite_eq_left h₂] at h
  exact MonoidalTransform.ofLift_subring_injective α hα t h₁ h₂ h

end PartC6

section ChartLayer

/-- The canonical map `R/P → k = R/M` (`P ⊆ M`). -/
noncomputable def residueQuotientHom {R : Type u} [CommRing R] [IsLocalRing R] {P : Ideal R}
    (hP : P ≤ maximalIdeal R) : R ⧸ P →+* ResidueField R :=
  Ideal.Quotient.lift P (residue R) fun a ha => (IsLocalRing.residue_eq_zero_iff a).mpr (hP ha)

theorem residueQuotientHom_mk {R : Type u} [CommRing R] [IsLocalRing R] {P : Ideal R}
    (hP : P ≤ maximalIdeal R) (a : R) :
    residueQuotientHom hP (Ideal.Quotient.mk P a) = residue R a :=
  Ideal.Quotient.lift_mk _ _ _

/-- p. 210: the reduction `π : A' → A'/MA' = k[X₂,…,X_r]` (`k = R/M`) obtained from a chart
`χ : A' → (R/P)[X₂,…,X_r]` by reducing the coefficients. -/
noncomputable def chartResidue {R : Type u} [CommRing R] [IsLocalRing R] {P : Ideal R}
    (hP : P ≤ maximalIdeal R) {A : Type*} [CommRing A] {σ : Type*}
    (χ : A →+* MvPolynomial σ (R ⧸ P)) : A →+* MvPolynomial σ (ResidueField R) :=
  (MvPolynomial.map (residueQuotientHom hP)).comp χ

theorem chartResidue_surjective {R : Type u} [CommRing R] [IsLocalRing R] {P : Ideal R}
    (hP : P ≤ maximalIdeal R) {A : Type*} [CommRing A] {σ : Type*}
    {χ : A →+* MvPolynomial σ (R ⧸ P)} (hχ : Function.Surjective χ) :
    Function.Surjective (chartResidue hP χ) := by
  refine (MvPolynomial.map_surjective _ ?_).comp hχ
  intro y
  obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective y
  exact ⟨Ideal.Quotient.mk P a, residueQuotientHom_mk hP a⟩

/-- p. 210: "`A'/(x₁, y₁,…,y_s)A' = A'/MA'` is identified with `k[X₂,…,X_r]`": the kernel of
`π` is `MA'` (we need only `⊆`). -/
theorem ker_chartResidue_le {R : Type u} [CommRing R] [IsLocalRing R] {P : Ideal R}
    (hP : P ≤ maximalIdeal R) {A : Type*} [CommRing A] {σ : Type*} (ψ : R →+* A)
    {χ : A →+* MvPolynomial σ (R ⧸ P)} (hχ : Function.Surjective χ)
    (hχC : ∀ c, χ (ψ c) = MvPolynomial.C (Ideal.Quotient.mk P c))
    (hker : RingHom.ker χ ≤ (maximalIdeal R).map ψ) :
    RingHom.ker (chartResidue hP χ) ≤ (maximalIdeal R).map ψ := by
  classical
  intro a ha
  rw [RingHom.mem_ker] at ha
  have hcoeff : ∀ m, residueQuotientHom hP ((χ a).coeff m) = 0 := fun m => by
    have ha' : MvPolynomial.map (residueQuotientHom hP) (χ a) = 0 := ha
    rw [← MvPolynomial.coeff_map, ha']
    rfl
  have hlift : ∀ m, ∃ c : R, c ∈ maximalIdeal R ∧ Ideal.Quotient.mk P c = (χ a).coeff m := by
    intro m
    obtain ⟨c, hc⟩ := Ideal.Quotient.mk_surjective ((χ a).coeff m)
    refine ⟨c, ?_, hc⟩
    have := hcoeff m
    rwa [← hc, residueQuotientHom_mk, IsLocalRing.residue_eq_zero_iff] at this
  choose c hcM hcmk using hlift
  choose b hb using fun m => hχ (MvPolynomial.monomial m (1 : R ⧸ P))
  have hsum : a - ∑ m ∈ (χ a).support, ψ (c m) * b m ∈ RingHom.ker χ := by
    rw [RingHom.mem_ker, map_sub, map_sum]
    have h1 : ∀ m ∈ (χ a).support, χ (ψ (c m) * b m) = MvPolynomial.monomial m ((χ a).coeff m) := by
      intro m _
      rw [map_mul, hχC, hb, MvPolynomial.C_mul_monomial, hcmk, mul_one]
    rw [Finset.sum_congr rfl h1, ← (χ a).as_sum, sub_self]
  have h2 : ∑ m ∈ (χ a).support, ψ (c m) * b m ∈ (maximalIdeal R).map ψ :=
    Ideal.sum_mem _ fun m _ => Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem ψ (hcM m))
  have := Ideal.add_mem _ (hker hsum) h2
  simpa using this

end ChartLayer

section ResidueCharts

variable {R Rb : Type u} [CommRing R] [IsRegularLocalRing R] [IsDomain R]
  [CommRing Rb] [IsRegularLocalRing Rb] [IsDomain Rb] {P : Ideal R}

theorem le_maximalIdeal_map {α : R →+* Rb} [IsLocalHom α] (hα : RingHom.MapsRSOP α) {P : Ideal R}
    (hP : P.IsPrime) : P.map α ≤ maximalIdeal Rb := by
  rw [← hα.map_maximalIdeal]
  exact Ideal.map_mono (IsLocalRing.le_maximalIdeal hP.ne_top)

/-- pp. 210-211: the charts `χ`, `χ̃` of `A'` and `Ã'`, compatible with `A' → Ã'`, together with the
reductions `π = (R/P → k)∘χ : A' → A'/MA' = k[X₂,…,X_r]` and `π̃ : Ã' → Ã'/M̃Ã' = k̃[X₂,…,X_r]`
(`k = R/M`, `k̃ = R̄/M̄`), compatible with `A' → Ã'` and with `k[X] → k̃[X]`, `X_j ↦ X_j` (induced by
`k → k̃`). -/
theorem MonoidalTransform.exists_charts_residue (α : R →+* Rb) [IsLocalHom α]
    (hα : RingHom.MapsRSOP α) (hP : P.IsPrime) (hS : IsRegularLocalRing (R ⧸ P))
    (t : MonoidalTransform R P) :
    ∃ (r : ℕ) (χ : blowupAlgebra R P t.x →+* MvPolynomial (Fin r) (R ⧸ P))
      (χb : blowupAlgebra Rb (P.map α) (α t.x) →+* MvPolynomial (Fin r) (Rb ⧸ P.map α)),
      Function.Surjective χ ∧
      RingHom.ker χ = Ideal.span {algebraMap R (blowupAlgebra R P t.x) t.x} ∧
      (∀ c : R, χ (algebraMap R (blowupAlgebra R P t.x) c) = C (Ideal.Quotient.mk P c)) ∧
      Function.Surjective χb ∧
      RingHom.ker χb = Ideal.span {algebraMap Rb (blowupAlgebra Rb (P.map α) (α t.x)) (α t.x)} ∧
      (∀ c : Rb, χb (algebraMap Rb (blowupAlgebra Rb (P.map α) (α t.x)) c) =
        C (Ideal.Quotient.mk (P.map α) c)) ∧
      Function.Surjective (chartResidue (IsLocalRing.le_maximalIdeal hP.ne_top) χ) ∧
      RingHom.ker (chartResidue (IsLocalRing.le_maximalIdeal hP.ne_top) χ) ≤
        (maximalIdeal R).map (algebraMap R (blowupAlgebra R P t.x)) ∧
      Function.Surjective (chartResidue (P := P.map α) (le_maximalIdeal_map hα hP) χb) ∧
      RingHom.ker (chartResidue (P := P.map α) (le_maximalIdeal_map hα hP) χb) ≤
        (maximalIdeal Rb).map (algebraMap Rb (blowupAlgebra Rb (P.map α) (α t.x))) ∧
      (chartResidue (P := P.map α) (le_maximalIdeal_map hα hP) χb).comp
          (blowupMap α (RingHom.MapsRSOP.injective α hα) P t.x) =
        (MvPolynomial.map (ResidueField.map α)).comp
          (chartResidue (IsLocalRing.le_maximalIdeal hP.ne_top) χ) ∧
      (∀ c : R, chartResidue (IsLocalRing.le_maximalIdeal hP.ne_top) χ
          (algebraMap R (blowupAlgebra R P t.x) c) = C (residue R c)) ∧
      (∀ c : Rb, chartResidue (P := P.map α) (le_maximalIdeal_map hα hP) χb
          (algebraMap Rb (blowupAlgebra Rb (P.map α) (α t.x)) c) = C (residue Rb c)) := by
  obtain ⟨r, χ, χb, hχ, hχx, hχC, hχb, hχbx, hχbC, hcomp⟩ :=
    t.exists_chart_comparison α hα hP hS
  have hPM : P ≤ maximalIdeal R := IsLocalRing.le_maximalIdeal hP.ne_top
  have hPbM : P.map α ≤ maximalIdeal Rb := le_maximalIdeal_map hα hP
  refine ⟨r, χ, χb, hχ, hχx, hχC, hχb, hχbx, hχbC, chartResidue_surjective hPM hχ,
    ker_chartResidue_le hPM _ hχ hχC ?_, chartResidue_surjective hPbM hχb,
    ker_chartResidue_le hPbM _ hχb hχbC ?_, ?_, ?_, ?_⟩
  · rw [hχx, Ideal.span_le, Set.singleton_subset_iff]
    exact Ideal.mem_map_of_mem _ (hPM t.x_mem)
  · rw [hχbx, Ideal.span_le, Set.singleton_subset_iff]
    exact Ideal.mem_map_of_mem _ (hPbM (Ideal.mem_map_of_mem α t.x_mem))
  · refine RingHom.ext fun a => ?_
    show MvPolynomial.map (residueQuotientHom hPbM)
        (χb (blowupMap α (RingHom.MapsRSOP.injective α hα) P t.x a)) =
      MvPolynomial.map (ResidueField.map α) (MvPolynomial.map (residueQuotientHom hPM) (χ a))
    rw [hcomp, MvPolynomial.map_map, MvPolynomial.map_map]
    have hρ : (residueQuotientHom hPbM).comp (Ideal.quotientMap (P.map α) α Ideal.le_comap_map) =
        (ResidueField.map α).comp (residueQuotientHom hPM) := by
      apply Ideal.Quotient.ringHom_ext
      refine RingHom.ext fun c => ?_
      simp [residueQuotientHom_mk, Ideal.quotientMap_mk, ResidueField.map_residue]
    rw [hρ]
  · intro c
    simp [chartResidue, hχC, residueQuotientHom_mk]
  · intro c
    simp [chartResidue, hχbC, residueQuotientHom_mk]

/-- The old packaging: the reductions `π`, `π̃` alone. -/
theorem MonoidalTransform.exists_residue_charts (α : R →+* Rb) [IsLocalHom α]
    (hα : RingHom.MapsRSOP α) (hP : P.IsPrime) (hS : IsRegularLocalRing (R ⧸ P))
    (t : MonoidalTransform R P) :
    ∃ (r : ℕ) (π : blowupAlgebra R P t.x →+* MvPolynomial (Fin r) (ResidueField R))
      (π' : blowupAlgebra Rb (P.map α) (α t.x) →+* MvPolynomial (Fin r) (ResidueField Rb)),
      Function.Surjective π ∧
      RingHom.ker π ≤ (maximalIdeal R).map (algebraMap R (blowupAlgebra R P t.x)) ∧
      Function.Surjective π' ∧
      RingHom.ker π' ≤ (maximalIdeal Rb).map
        (algebraMap Rb (blowupAlgebra Rb (P.map α) (α t.x))) ∧
      π'.comp (blowupMap α (RingHom.MapsRSOP.injective α hα) P t.x) =
        (MvPolynomial.map (ResidueField.map α)).comp π ∧
      (∀ c : R, π (algebraMap R (blowupAlgebra R P t.x) c) = C (residue R c)) ∧
      (∀ c : Rb, π' (algebraMap Rb (blowupAlgebra Rb (P.map α) (α t.x)) c) = C (residue Rb c)) := by
  obtain ⟨r, χ, χb, -, -, -, -, -, -, h1, h2, h3, h4, h5, h6, h7⟩ :=
    t.exists_charts_residue α hα hP hS
  exact ⟨r, _, _, h1, h2, h3, h4, h5, h6, h7⟩

end ResidueCharts

section FibrePrimes

attribute [local instance] MvPolynomial.algebraMvPolynomial in
/-- If `k̃/k` is an integral (e.g. algebraic) field extension, a prime `q` of `k̃[X]` is minimal over the
extension of its contraction `q ∩ k[X]` (incomparability): the primes of `k̃[X]` over a given prime
of `k[X]` are isolated (p. 211). -/
theorem mem_minimalPrimes_map_of_isIntegral {k k' : Type*} [Field k] [Field k'] (κ : k →+* k')
    (hκ : κ.IsIntegral) {σ : Type*} (m : Ideal (MvPolynomial σ k))
    (q : Ideal (MvPolynomial σ k')) [q.IsPrime] (hq : q.comap (MvPolynomial.map κ) = m) :
    q ∈ (m.map (MvPolynomial.map κ)).minimalPrimes := by
  let : Algebra k k' := κ.toAlgebra
  have hint : Algebra.IsIntegral k k' := ⟨hκ⟩
  have hint' : Algebra.IsIntegral (MvPolynomial σ k) (MvPolynomial σ k') :=
    ⟨fun f => MvPolynomial.isIntegral_iff_isIntegral_coeff.mpr fun n => hint.isIntegral _⟩
  have := Ideal.IsIntegral.mem_minimalPrimes_map_under (R := MvPolynomial σ k) q
  have hmap : algebraMap (MvPolynomial σ k) (MvPolynomial σ k') = MvPolynomial.map κ := by
    rw [MvPolynomial.algebraMap_def]; rfl
  rw [Ideal.under_def, hmap, hq] at this
  exact this

/-- If each `X_i` is algebraic over `k` modulo the prime `m` of `k[X]` (e.g. if the residue field of
`R'`, which contains `k[X]/m`, is algebraic over `k`), then every prime of `k̃[X]` containing
`m k̃[X]` is maximal: `k̃[X]/(m k̃[X])` is integral over the field `k̃`. -/
theorem isMaximal_of_map_le_of_forall_exists_aeval_mem {k k' : Type*} [Field k] [Field k']
    (κ : k →+* k') {σ : Type*} (m : Ideal (MvPolynomial σ k))
    (h : ∀ i, ∃ g : Polynomial k, g ≠ 0 ∧ Polynomial.aeval (MvPolynomial.X i) g ∈ m)
    (q : Ideal (MvPolynomial σ k')) [q.IsPrime] (hmq : m.map (MvPolynomial.map κ) ≤ q) :
    q.IsMaximal := by
  have hdom : IsDomain (MvPolynomial σ k' ⧸ q) := Ideal.Quotient.isDomain q
  have hXint : ∀ i, IsIntegral k' (Ideal.Quotient.mk q (MvPolynomial.X i)) := by
    intro i
    obtain ⟨g, hg0, hgm⟩ := h i
    have h1 : MvPolynomial.map κ (Polynomial.aeval (MvPolynomial.X i) g) =
        Polynomial.aeval (MvPolynomial.X i) (g.map κ) := by
      rw [Polynomial.aeval_def, Polynomial.aeval_def, Polynomial.eval₂_map,
        Polynomial.hom_eval₂]
      congr 1
      · ext c; simp
      · simp
    have h2 : Polynomial.aeval (Ideal.Quotient.mk q (MvPolynomial.X i)) (g.map κ) = 0 := by
      have h3 : Polynomial.aeval (MvPolynomial.X i) (g.map κ) ∈ q :=
        hmq (h1 ▸ Ideal.mem_map_of_mem _ hgm)
      have := Polynomial.aeval_algHom_apply (Ideal.Quotient.mkₐ k' q) (MvPolynomial.X i) (g.map κ)
      simp only [Ideal.Quotient.mkₐ_eq_mk] at this
      rw [this]
      exact Ideal.Quotient.eq_zero_iff_mem.mpr h3
    have hne : g.map κ ≠ 0 := (Polynomial.map_ne_zero_iff κ.injective).mpr hg0
    exact (isAlgebraic_iff_isIntegral.mp ⟨g.map κ, hne, h2⟩)
  have hZint : Algebra.IsIntegral k' (MvPolynomial σ k' ⧸ q) := by
    refine ⟨fun z => ?_⟩
    obtain ⟨F, rfl⟩ := Ideal.Quotient.mk_surjective z
    induction F using MvPolynomial.induction_on with
    | C c => exact isIntegral_algebraMap (x := c)
    | add p p' hp hp' => rw [map_add]; exact hp.add hp'
    | mul_X p i hp => rw [map_mul]; exact hp.mul (hXint i)
  have hfield : IsField (MvPolynomial σ k' ⧸ q) :=
    isField_of_isIntegral_of_isField' (Field.toIsField k')
  exact Ideal.Quotient.maximal_of_isField q hfield

end FibrePrimes

section Fibre

variable {R : Type u} [CommRing R] [IsRegularLocalRing R] [IsDomain R] {P : Ideal R}

/-- `A'/M' = k[X]/m ↪ R'/M'R' = k'` (p. 211: "`R'/M'R'`"): the residue map `A' → R' → k'` factors
through `π : A' → k[X]` and has kernel `m = π(M')`. -/
theorem MonoidalTransform.exists_ringHom_residueField_ker_eq (t : MonoidalTransform R P)
    {σ : Type*} (π : blowupAlgebra R P t.x →+* MvPolynomial σ (ResidueField R))
    (hπ : Function.Surjective π) (hker : RingHom.ker π ≤ t.M') :
    ∃ Θ : MvPolynomial σ (ResidueField R) →+* ResidueField t.ring,
      (∀ y, Θ (π y) = residue t.ring (algebraMap (blowupAlgebra R P t.x) t.ring y)) ∧
      RingHom.ker Θ = t.M'.map π := by
  set Θ0 : blowupAlgebra R P t.x →+* ResidueField t.ring :=
    (residue t.ring).comp (algebraMap (blowupAlgebra R P t.x) t.ring) with hΘ0
  have hΘ0ker : ∀ y, Θ0 y = 0 ↔ y ∈ t.M' := fun y => by
    rw [hΘ0, RingHom.comp_apply, IsLocalRing.residue_eq_zero_iff,
      IsLocalization.AtPrime.to_map_mem_maximal_iff t.ring t.M']
  have hle : RingHom.ker π ≤ RingHom.ker Θ0 := fun y hy => by
    rw [RingHom.mem_ker, hΘ0ker]; exact hker hy
  refine ⟨RingHom.liftOfSurjective π hπ ⟨Θ0, hle⟩, fun y =>
    RingHom.liftOfSurjective_comp_apply π hπ ⟨Θ0, hle⟩ y, ?_⟩
  ext z
  obtain ⟨y, rfl⟩ := hπ z
  rw [RingHom.mem_ker, RingHom.liftOfSurjective_comp_apply]
  show Θ0 y = 0 ↔ _
  rw [hΘ0ker, Ideal.mem_map_iff_of_surjective π hπ]
  constructor
  · intro hy; exact ⟨y, hy, rfl⟩
  · rintro ⟨y', hy', hπy⟩
    have : y - y' ∈ RingHom.ker π := by rw [RingHom.mem_ker, map_sub, hπy, sub_self]
    have h1 : y - y' ∈ t.M' := hker this
    have h2 : y = (y - y') + y' := by ring
    rw [h2]
    exact add_mem h1 hy'

end Fibre

section FiniteLiftPrimes

variable {R Rb : Type u} [CommRing R] [IsRegularLocalRing R] [IsDomain R]
  [CommRing Rb] [IsRegularLocalRing Rb] [IsDomain Rb] {P : Ideal R}

/-- p. 211: "all the associated prime ideals of `m̄'k̃[X₂,…,X_r]` are isolated": if `R̄` or `R'` is
residually algebraic over `R`, then the image `M̃'k̃[X]` (`M̃' ↦ M̃'/M̄Ã'`, `π̃`) of a prime `M̃'` of `Ã'`
over `M'` is a minimal prime of `m̄'k̃[X₂,…,X_r]` (incomparability in the integral extension `k̃[X]/m̄'k̃[X]`
of the field `k̃`, resp. of the algebraic extension `k[X]/m̄' ⊆ R'/M'R'`), and lies over `m̄'`. -/
theorem MonoidalTransform.map_mem_minimalPrimes_of_mem_liftPrimes (α : R →+* Rb) [IsLocalHom α]
    (hα : RingHom.MapsRSOP α) (t : MonoidalTransform R P)
    (halg : RingHom.IsResiduallyAlgebraic α ∨
      RingHom.IsResiduallyAlgebraic (R := R) (R' := t.ring) t.toRing)
    {r : ℕ} (π : blowupAlgebra R P t.x →+* MvPolynomial (Fin r) (ResidueField R))
    (π' : blowupAlgebra Rb (P.map α) (α t.x) →+* MvPolynomial (Fin r) (ResidueField Rb))
    (hπ : Function.Surjective π) (hkπ : RingHom.ker π ≤ (maximalIdeal R).map
      (algebraMap R (blowupAlgebra R P t.x)))
    (hπ' : Function.Surjective π')
    (hkπ' : RingHom.ker π' ≤ (maximalIdeal Rb).map
      (algebraMap Rb (blowupAlgebra Rb (P.map α) (α t.x))))
    (hcomm : π'.comp (blowupMap α (RingHom.MapsRSOP.injective α hα) P t.x) =
      (MvPolynomial.map (ResidueField.map α)).comp π)
    (hπC : ∀ c : R, π (algebraMap R (blowupAlgebra R P t.x) c) = C (residue R c))
    (N : Ideal (blowupAlgebra Rb (P.map α) (α t.x)))
    (hN : N ∈ LiftPrimes α (RingHom.MapsRSOP.injective α hα) t) :
    (N.map π').IsPrime ∧
      (N.map π').comap (MvPolynomial.map (ResidueField.map α)) = t.M'.map π ∧
      N.map π' ∈ ((t.M'.map π).map (MvPolynomial.map (ResidueField.map α))).minimalPrimes := by
  classical
  have hkπM' : RingHom.ker π ≤ t.M' := hkπ.trans t.le
  have : (t.M'.map π).IsPrime := Ideal.map_isPrime_of_surjective hπ hkπM'
  set ι : MvPolynomial (Fin r) (ResidueField R) →+* MvPolynomial (Fin r) (ResidueField Rb) :=
    MvPolynomial.map (ResidueField.map α) with hι
  have hkN : RingHom.ker π' ≤ N :=
    hkπ'.trans (MonoidalTransform.ofLift α hα t N hN).le
  have hNp := hN.1
  have hqp : (N.map π').IsPrime := Ideal.map_isPrime_of_surjective hπ' hkN
  have hq : (N.map π').comap ι = t.M'.map π :=
    (comap_eq_iff_comap_map_eq _ π π' ι hπ hπ' hcomm hkπM' hkN).mp hN.2
  refine ⟨hqp, hq, ?_⟩
  rcases halg with hres | hres
  · have hκ : (ResidueField.map α).IsIntegral := by
      let := (ResidueField.map α).toAlgebra
      have : Algebra.IsAlgebraic (ResidueField R) (ResidueField Rb) := hres
      have : Algebra.IsIntegral (ResidueField R) (ResidueField Rb) := inferInstance
      exact fun x => this.isIntegral x
    exact mem_minimalPrimes_map_of_isIntegral _ hκ _ _ hq
  · obtain ⟨Θ, hΘπ, hΘker⟩ := t.exists_ringHom_residueField_ker_eq π hπ hkπM'
    have hX : ∀ i, ∃ g : Polynomial (ResidueField R), g ≠ 0 ∧
        Polynomial.aeval (MvPolynomial.X i) g ∈ t.M'.map π := by
      intro i
      let : Algebra (ResidueField R) (ResidueField t.ring) :=
        (ResidueField.map t.toRing).toAlgebra
      have halgK : Algebra.IsAlgebraic (ResidueField R) (ResidueField t.ring) := hres
      obtain ⟨g, hg0, hg⟩ := halgK.isAlgebraic (Θ (MvPolynomial.X i))
      refine ⟨g, hg0, ?_⟩
      rw [← hΘker, RingHom.mem_ker]
      let Θa : MvPolynomial (Fin r) (ResidueField R) →ₐ[ResidueField R] ResidueField t.ring :=
        { Θ with
          commutes' := fun c => by
            obtain ⟨c0, rfl⟩ := IsLocalRing.residue_surjective c
            show Θ (MvPolynomial.C (residue R c0)) = ResidueField.map t.toRing (residue R c0)
            rw [← hπC, hΘπ, ResidueField.map_residue]
            rfl }
      have := Polynomial.aeval_algHom_apply Θa (MvPolynomial.X i) g
      rw [← hg]
      exact this.symm
    have hq_le : (t.M'.map π).map ι ≤ N.map π' := Ideal.map_le_iff_le_comap.mpr hq.ge
    refine ⟨⟨hqp, hq_le⟩, fun q' hq' hq'q => ?_⟩
    have := hq'.1
    have hmax := isMaximal_of_map_le_of_forall_exists_aeval_mem (ResidueField.map α)
      (t.M'.map π) hX q' hq'.2
    exact (hmax.eq_of_le hqp.ne_top hq'q).ge

end FiniteLiftPrimes

section FlatPoly

/-- `k̃[X]` is flat over `k[X]` for a field extension `k → k̃` ("the free extension
`k[X₂,…,X_r] → k̃[X₂,…,X_r]`", p. 211). -/
theorem flat_mvPolynomial_map_of_field {k k' : Type u} [Field k] [Field k'] (κ : k →+* k')
    (σ : Type*) :
    letI := (MvPolynomial.map (σ := σ) κ).toAlgebra
    Module.Flat (MvPolynomial σ k) (MvPolynomial σ k') := by
  let _ := κ.toAlgebra
  let _ : Algebra (MvPolynomial σ k) (MvPolynomial σ k') := (MvPolynomial.map (σ := σ) κ).toAlgebra
  -- `A ⊗_k k' ≃ k'[σ]` as `A = k[σ]`-modules
  have hfl : Module.Flat (MvPolynomial σ k) (MvPolynomial σ k ⊗[k] k') := inferInstance
  let e : MvPolynomial σ k ⊗[k] k' ≃ₐ[k] MvPolynomial σ k' :=
    (Algebra.TensorProduct.comm k (MvPolynomial σ k) k').trans
      ((MvPolynomial.algebraTensorAlgEquiv k k').restrictScalars k)
  have he : ∀ a : MvPolynomial σ k, e (a ⊗ₜ[k] 1) = MvPolynomial.map κ a := by
    intro a
    have := MvPolynomial.algebraTensorAlgEquiv_symm_map (σ := σ) k k' a
    have h2 : (MvPolynomial.map (algebraMap k k')) a = MvPolynomial.map κ a := rfl
    rw [h2] at this
    simp only [e, AlgEquiv.trans_apply, Algebra.TensorProduct.comm_tmul]
    rw [AlgEquiv.restrictScalars_apply]
    have h3 := congrArg (MvPolynomial.algebraTensorAlgEquiv (σ := σ) k k') this
    rw [AlgEquiv.apply_symm_apply] at h3
    rw [h3]
  let le : MvPolynomial σ k ⊗[k] k' ≃ₗ[MvPolynomial σ k] MvPolynomial σ k' :=
    { e.toLinearEquiv with
      map_smul' := fun a z => by
        have h1 : a • z = (a ⊗ₜ[k] (1 : k')) * z := by
          induction z using TensorProduct.inductionOn with
          | tmul b c => simp [TensorProduct.smul_tmul', Algebra.TensorProduct.tmul_mul_tmul]
          | add u v hu hv => rw [smul_add, mul_add, hu, hv]
        show e (a • z) = a • e z
        rw [h1, map_mul, he]
        rfl }
  exact Module.Flat.of_linearEquiv le.symm

end FlatPoly

section HeightFlat

/-- Going down for the free extension `k[X] → k̃[X]` (p. 211): a prime `q` of `k̃[X]` over `m`
which is isolated over `m` has the height of `m`. -/
theorem height_eq_of_mem_minimalPrimes_map {k k' : Type u} [Field k] [Field k'] (κ : k →+* k')
    {σ : Type*} [Finite σ] (m : Ideal (MvPolynomial σ k)) [m.IsPrime]
    (q : Ideal (MvPolynomial σ k')) [q.IsPrime] (hq : q.comap (MvPolynomial.map κ) = m)
    (hmin : q ∈ (m.map (MvPolynomial.map κ)).minimalPrimes) : q.height = m.height := by
  let : Algebra (MvPolynomial σ k) (MvPolynomial σ k') := (MvPolynomial.map (σ := σ) κ).toAlgebra
  have : Module.Flat (MvPolynomial σ k) (MvPolynomial σ k') := flat_mvPolynomial_map_of_field κ σ
  have : q.LiesOver m := ⟨hq.symm⟩
  have hgd := Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown m q
  have h0 : (q.map (Ideal.Quotient.mk (m.map (algebraMap (MvPolynomial σ k) (MvPolynomial σ k'))))).height
      = 0 := by
    have hmin' : q ∈ (m.map (algebraMap (MvPolynomial σ k) (MvPolynomial σ k'))).minimalPrimes := hmin
    rw [Ideal.minimalPrimes_eq_comap] at hmin'
    obtain ⟨p, hp, rfl⟩ := hmin'
    have hpp : p.IsPrime := hp.1.1
    rw [Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective]
    exact Ideal.height_eq_zero_iff.mpr hp
  rw [h0, add_zero] at hgd
  exact hgd

end HeightFlat

section DimChart

/-- `height_eq_add_height_map_residue` for an arbitrary surjection `ρ : S → k` with kernel the maximal
ideal: a prime `q` of `S[T]` over the maximal ideal of the noetherian local ring `S` has height
`ht(M_S) + ht(q k[T])`. -/
theorem height_eq_add_height_map_of_ker (S : Type u) [CommRing S] [IsLocalRing S]
    [IsNoetherianRing S] {k : Type u} [CommRing k] (ρ : S →+* k) (hρ : Function.Surjective ρ)
    (hker : RingHom.ker ρ = maximalIdeal S) (n : ℕ)
    (q : Ideal (MvPolynomial (Fin n) S)) [q.IsPrime] (hqC : q.comap C = maximalIdeal S) :
    q.height = (maximalIdeal S).height + (q.map (MvPolynomial.map ρ)).height := by
  let φk : MvPolynomial (Fin n) S →+* MvPolynomial (Fin n) k := MvPolynomial.map ρ
  have hφsurj : Function.Surjective φk := MvPolynomial.map_surjective _ hρ
  have hJ : (maximalIdeal S).map (algebraMap S (MvPolynomial (Fin n) S)) = RingHom.ker φk := by
    rw [MvPolynomial.ker_map, hker, MvPolynomial.algebraMap_eq]
  have hlo : q.LiesOver (maximalIdeal S) := ⟨hqC.symm⟩
  have hgd := Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown (maximalIdeal S) q
  let ψ := (Ideal.quotEquivOfEq hJ).trans (RingHom.quotientKerEquivOfSurjective hφsurj)
  rw [← RingEquiv.height_map ψ] at hgd
  have hmapq : Ideal.map ψ (q.map (Ideal.Quotient.mk
      ((maximalIdeal S).map (algebraMap S (MvPolynomial (Fin n) S))))) = q.map φk := by
    have hψmk : ∀ a, ψ (Ideal.Quotient.mk
        ((maximalIdeal S).map (algebraMap S (MvPolynomial (Fin n) S))) a) = φk a := by
      intro a
      rw [RingEquiv.trans_apply, Ideal.quotEquivOfEq_mk,
        RingHom.quotientKerEquivOfSurjective_apply_mk]
    apply le_antisymm
    · rw [Ideal.map_le_iff_le_comap, Ideal.map_le_iff_le_comap]
      intro a ha
      rw [Ideal.mem_comap, Ideal.mem_comap, hψmk]
      exact Ideal.mem_map_of_mem _ ha
    · rw [Ideal.map_le_iff_le_comap]
      intro a ha
      rw [Ideal.mem_comap, ← hψmk]
      exact Ideal.mem_map_of_mem _ (Ideal.mem_map_of_mem _ ha)
  rw [hmapq] at hgd
  exact hgd

end DimChart

section DimChart2

variable {S : Type u} [CommRing S] [IsRegularLocalRing S] [IsDomain S] {Q : Ideal S}

theorem ker_residueQuotientHom (hQ : IsRegularLocalRing (S ⧸ Q)) (hQM : Q ≤ maximalIdeal S) :
    RingHom.ker (residueQuotientHom hQM) = maximalIdeal (S ⧸ Q) := by
  have : IsLocalHom (Ideal.Quotient.mk Q) :=
    IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective
  ext y
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective y
  rw [RingHom.mem_ker, residueQuotientHom_mk, IsLocalRing.residue_eq_zero_iff,
    IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
    isUnit_map_iff]

theorem residueQuotientHom_surjective (hQM : Q ≤ maximalIdeal S) :
    Function.Surjective (residueQuotientHom hQM) := by
  intro y
  obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective y
  exact ⟨Ideal.Quotient.mk Q a, residueQuotientHom_mk hQM a⟩

/-- p. 210 (dimension count): `dim R' = dim S + ht(m̄') + 1`, where `R' = A'_{M'}`, `S = R/P` and
`m̄' = M̄'/M̄S[X]` is the prime of `k[X]` image of `M'` under `π : A' → k[X]`
(`dim R'/(x)R' = ht M̄' = dim S + ht m̄'`, going down for the flat extension `S → S[X]`). -/
theorem MonoidalTransform.ringKrullDim_eq_of_chart (hQ : IsRegularLocalRing (S ⧸ Q)) [Q.IsPrime]
    (T : MonoidalTransform S Q) {r : ℕ}
    (χ : blowupAlgebra S Q T.x →+* MvPolynomial (Fin r) (S ⧸ Q))
    (hχ : Function.Surjective χ)
    (hχx : RingHom.ker χ = Ideal.span {algebraMap S (blowupAlgebra S Q T.x) T.x})
    (hχC : ∀ c : S, χ (algebraMap S (blowupAlgebra S Q T.x) c) = C (Ideal.Quotient.mk Q c)) :
    ringKrullDim T.ring = ringKrullDim (S ⧸ Q) +
      ((T.M'.map (chartResidue (IsLocalRing.le_maximalIdeal (Ideal.IsPrime.ne_top ‹_›)) χ)).height
        : WithBot ℕ∞) + 1 := by
  have hQM : Q ≤ maximalIdeal S := IsLocalRing.le_maximalIdeal (Ideal.IsPrime.ne_top ‹_›)
  obtain ⟨q, hq, e, hqdef, hcomap, hqC, -, -⟩ :=
    T.exists_quotient_equiv_localization_of_chart hQ χ hχ hχx hχC
  have hNoeth := MonoidalTransform.isNoetherianRing T
  have hxM : T.x ∈ maximalIdeal S := hQM T.x_mem
  have hX0 : T.toRing T.x ≠ 0 := fun h =>
    T.x_ne_zero (MonoidalTransform.toRing_injective T (h.trans (map_zero _).symm))
  have hdim : ringKrullDim T.ring = (q.height : WithBot ℕ∞) + 1 := by
    have h1 := Module.ringKrullDim_quotient_add_one_of_mem_nonZeroDivisors
      (mem_nonZeroDivisors_of_ne_zero hX0) (p := maximalIdeal T.ring)
      IsLocalRing.maximalIdeal_height_eq_ringKrullDim (map_nonunit T.toRing T.x hxM)
    rw [← h1, ← IsLocalization.AtPrime.ringKrullDim_eq_height q (Localization.AtPrime q),
      ringKrullDim_eq_of_ringEquiv e]
    rfl
  have hgd := height_eq_add_height_map_of_ker (S ⧸ Q) (residueQuotientHom hQM)
    (residueQuotientHom_surjective hQM) (ker_residueQuotientHom hQ hQM) r q hqC
  have hmap : q.map (MvPolynomial.map (residueQuotientHom hQM)) =
      T.M'.map (chartResidue hQM χ) := by
    rw [hqdef, Ideal.map_map]; rfl
  rw [hmap] at hgd
  rw [hdim, hgd]
  have h2 : ((maximalIdeal (S ⧸ Q)).height : WithBot ℕ∞) = ringKrullDim (S ⧸ Q) := by
    rw [IsLocalRing.maximalIdeal_height_eq_ringKrullDim]
  rw [WithBot.coe_add, h2]

end DimChart2

section DimEq

variable {R Rb : Type u} [CommRing R] [IsRegularLocalRing R] [IsDomain R]
  [CommRing Rb] [IsRegularLocalRing Rb] [IsDomain Rb] {P : Ideal R}

/-- p. 210: `dim R̄/P̄ = dim R/P` (`P̄ = PR̄`): `α` maps a minimal system of generators `(x₁,…,x_r, y₁,…,y_s)`
of `M` to one of `M̄`, `P = (x₁,…,x_r)`, so `dim R = r + dim R/P` and `dim R̄ = r + dim R̄/P̄`, while
`dim R̄ = dim R`. -/
theorem MonoidalTransform.ringKrullDim_quotient_map_eq (α : R →+* Rb) [IsLocalHom α]
    (hα : RingHom.MapsRSOP α) (hP : P.IsPrime) (hS : IsRegularLocalRing (R ⧸ P))
    (t : MonoidalTransform R P) :
    ringKrullDim (Rb ⧸ P.map α) = ringKrullDim (R ⧸ P) := by
  classical
  have hαinj := RingHom.MapsRSOP.injective α hα
  obtain ⟨hPb, hSq⟩ := RingHom.MapsRSOP.isPrime_map_and_isRegularLocalRing_quotient hα hP hS
  obtain ⟨S, r, z, hSM, hScard, hinj, hzS, hz0, hzP⟩ := t.exists_minimal_generators hS
  have hSrsop : IsRegularSystemOfParameters R S :=
    ⟨hSM, by rw [hScard]; exact IsRegularLocalRing.spanFinrank_maximalIdeal⟩
  obtain ⟨hSb, hScardb⟩ := RingHom.MapsRSOP.isRegularSystemOfParameters_image hα hSrsop
  have hSbcard : (S.image α).card = (maximalIdeal Rb).spanFinrank := by
    have h1 := hSb.2
    rw [IsRegularLocalRing.spanFinrank_maximalIdeal.symm] at h1
    exact_mod_cast h1
  have h1 := ringKrullDim_eq_add_of_minimal_generators hS hSM hScard hinj hzS hzP
  have h2 := ringKrullDim_eq_add_of_minimal_generators (P := P.map α) hSq
    (S := S.image α) (z := fun i => α (z i)) hSb.1 hSbcard
    (fun i j h => hinj (hαinj h)) (fun i => Finset.mem_image_of_mem _ (hzS i))
    (by rw [← hzP, Ideal.map_span, ← Set.range_comp]; rfl)
  rw [← hα.ringKrullDim_eq, h2] at h1
  -- cancel the finite summand `r + 1`
  obtain ⟨k₁, -, hk₁⟩ := exists_nat_ringKrullDim_eq
    (ringKrullDim_le_spanFinrank_maximalIdeal (R ⧸ P))
  obtain ⟨k₂, -, hk₂⟩ := exists_nat_ringKrullDim_eq
    (ringKrullDim_le_spanFinrank_maximalIdeal (Rb ⧸ P.map α))
  rw [hk₁, hk₂] at h1 ⊢
  have h4 : r + 1 + k₁ = r + 1 + k₂ := by exact_mod_cast h1.symm
  have : k₁ = k₂ := by omega
  rw [this]

end DimEq

section DimEq3

variable {R Rb : Type u} [CommRing R] [IsRegularLocalRing R] [IsDomain R]
  [CommRing Rb] [IsRegularLocalRing Rb] [IsDomain Rb] {P : Ideal R}

/-- Lemma 4 (1), "all the `R̃'` have the same dimension as `R'`" (p. 212), along the printed route:
`dim R' = dim S + ht(m̄') + 1` and `dim R̃' = dim S̃ + ht(m̃) + 1` (`p. 210`, through the charts
`A'/(x)A' = S[X]`, `Ã'/(α x)Ã' = S̃[X]`), with `dim S̃ = dim S` and `ht(m̃) = ht(m̄')`: the free extension
`k[X] → k̃[X]` is flat, so going down gives `ht(M̃'k̃[X]) = ht(m̄')` for the *isolated* prime `M̃'k̃[X]`
over `m̄'`. -/
theorem MonoidalTransform.ringKrullDim_eq_of_isCanonicalLift (α : R →+* Rb) [IsLocalHom α]
    (hα : RingHom.MapsRSOP α) (hP : P.IsPrime) (hS : IsRegularLocalRing (R ⧸ P))
    (t : MonoidalTransform R P)
    (halg : RingHom.IsResiduallyAlgebraic α ∨
      RingHom.IsResiduallyAlgebraic (R := R) (R' := t.ring) t.toRing)
    (tb : MonoidalTransform Rb (P.map α)) (β : t.ring →+* tb.ring)
    (hβ : IsCanonicalLift α t tb β) :
    ringKrullDim tb.ring = ringKrullDim t.ring := by
  classical
  have hαinj := RingHom.MapsRSOP.injective α hα
  obtain ⟨hPb, hSq⟩ := RingHom.MapsRSOP.isPrime_map_and_isRegularLocalRing_quotient hα hP hS
  obtain ⟨r, χ, χb, hχ, hχx, hχC, hχb, hχbx, hχbC, hπ, hkπ, hπ', hkπ', hcomm, hπC, hπ'C⟩ :=
    t.exists_charts_residue α hα hP hS
  have hPM : P ≤ maximalIdeal R := IsLocalRing.le_maximalIdeal hP.ne_top
  have hPbM : P.map α ≤ maximalIdeal Rb := le_maximalIdeal_map hα hP
  set N := (maximalIdeal tb.ring).comap (MonoidalTransform.blowupToRing α hα t tb β hβ) with hN
  have hNmem := MonoidalTransform.comap_maximalIdeal_blowupToRing_mem_liftPrimes α hα t tb β hβ
  set T := MonoidalTransform.ofLift α hα t N hNmem with hT
  have hsub := MonoidalTransform.subring_eq_ofLift_subring α hα t tb β hβ
  rw [ringKrullDim_eq_of_ringEquiv (tb.ringEquivOfSubringEq T hsub)]
  have h1 : ringKrullDim T.ring = ringKrullDim (Rb ⧸ P.map α) +
      ((N.map (chartResidue hPbM χb)).height : WithBot ℕ∞) + 1 :=
    @MonoidalTransform.ringKrullDim_eq_of_chart Rb _ _ _ (P.map α) hSq hPb T r χb hχb hχbx hχbC
  have h2 : ringKrullDim t.ring = ringKrullDim (R ⧸ P) +
      ((t.M'.map (chartResidue hPM χ)).height : WithBot ℕ∞) + 1 :=
    @MonoidalTransform.ringKrullDim_eq_of_chart R _ _ _ P hS hP t r χ hχ hχx hχC
  obtain ⟨hqp, hq, hmin⟩ := t.map_mem_minimalPrimes_of_mem_liftPrimes α hα halg
    (chartResidue hPM χ) (chartResidue hPbM χb) hπ hkπ hπ' hkπ' hcomm hπC N hNmem
  have hkπM' : RingHom.ker (chartResidue hPM χ) ≤ t.M' := hkπ.trans t.le
  have : (t.M'.map (chartResidue hPM χ)).IsPrime := Ideal.map_isPrime_of_surjective hπ hkπM'
  have hht := @height_eq_of_mem_minimalPrimes_map _ _ _ _ (ResidueField.map α) (Fin r) _
    (t.M'.map (chartResidue hPM χ)) this (N.map (chartResidue hPbM χb)) hqp hq hmin
  rw [h1, h2, hht, t.ringKrullDim_quotient_map_eq α hα hP hS]

end DimEq3

section FractionPrime

/-- A prime `q` of `B` containing `ker Ψ` and disjoint from a multiplicative set `U` of denominators of
`Ψ` (`Ψ(U)` units, every element of `C` is `Ψ(b)/Ψ(u)`) is the contraction of a prime of `C`. -/
theorem exists_isPrime_comap_eq_of_fraction {B C : Type*} [CommRing B] [CommRing C] (Ψ : B →+* C)
    (U : Submonoid B) (hfrac : ∀ c : C, ∃ (b : B) (u : B), u ∈ U ∧ c * Ψ u = Ψ b)
    (q : Ideal B) [hq : q.IsPrime] (hker : RingHom.ker Ψ ≤ q) (hU : Disjoint (U : Set B) (q : Set B)) :
    ∃ p : Ideal C, p.IsPrime ∧ p.comap Ψ = q := by
  classical
  let p : Ideal C :=
    { carrier := {c | ∃ b ∈ q, ∃ u ∈ U, c * Ψ u = Ψ b}
      zero_mem' := ⟨0, q.zero_mem, 1, U.one_mem, by simp⟩
      add_mem' := by
        rintro c c' ⟨b, hb, u, hu, h⟩ ⟨b', hb', u', hu', h'⟩
        refine ⟨b * u' + b' * u, q.add_mem (q.mul_mem_right _ hb) (q.mul_mem_right _ hb'),
          u * u', U.mul_mem hu hu', ?_⟩
        rw [map_add, map_mul, map_mul, map_mul, ← h, ← h']; ring
      smul_mem' := by
        intro c' c ⟨b, hb, u, hu, h⟩
        obtain ⟨b', u', hu', h'⟩ := hfrac c'
        refine ⟨b' * b, q.mul_mem_left _ hb, u' * u, U.mul_mem hu' hu, ?_⟩
        rw [map_mul, map_mul, smul_eq_mul]
        calc c' * c * (Ψ u' * Ψ u) = (c' * Ψ u') * (c * Ψ u) := by ring
          _ = _ := by rw [h, h'] }
  have hmem : ∀ c, c ∈ p ↔ ∃ b ∈ q, ∃ u ∈ U, c * Ψ u = Ψ b := fun c => Iff.rfl
  have hcomap : p.comap Ψ = q := by
    ext b
    rw [Ideal.mem_comap, hmem]
    constructor
    · rintro ⟨b', hb', u, hu, h⟩
      have h1 : b * u - b' ∈ RingHom.ker Ψ := by rw [RingHom.mem_ker, map_sub, map_mul, h, sub_self]
      have h2 : b * u ∈ q := by
        have := q.add_mem (hker h1) hb'
        simpa using this
      exact (hq.mem_or_mem h2).resolve_right fun hu' => Set.disjoint_left.mp hU hu hu'
    · intro hb
      exact ⟨b, hb, 1, U.one_mem, by simp⟩
  refine ⟨p, ⟨?_, ?_⟩, hcomap⟩
  · rw [Ideal.ne_top_iff_one]
    rintro ⟨b, hb, u, hu, h⟩
    have h1 : u - b ∈ RingHom.ker Ψ := by rw [RingHom.mem_ker, map_sub]; simp at h; rw [h]; simp
    have : u ∈ q := by simpa using q.add_mem (hker h1) hb
    exact Set.disjoint_left.mp hU hu this
  · intro c c' hcc'
    obtain ⟨b, hb, u, hu, h⟩ := hcc'
    obtain ⟨b₁, u₁, hu₁, h₁⟩ := hfrac c
    obtain ⟨b₂, u₂, hu₂, h₂⟩ := hfrac c'
    have h3 : Ψ (b₁ * b₂ * u) = Ψ (b * (u₁ * u₂)) := by
      simp only [map_mul]
      calc Ψ b₁ * Ψ b₂ * Ψ u = (c * Ψ u₁) * (c' * Ψ u₂) * Ψ u := by rw [h₁, h₂]
        _ = (c * c' * Ψ u) * (Ψ u₁ * Ψ u₂) := by ring
        _ = _ := by rw [h]
    have h4 : b₁ * b₂ * u - b * (u₁ * u₂) ∈ RingHom.ker Ψ := by
      rw [RingHom.mem_ker, map_sub, h3, sub_self]
    have h5 : b₁ * b₂ * u ∈ q := by
      have := q.add_mem (hker h4) (q.mul_mem_right (u₁ * u₂) hb)
      simpa using this
    have h6 := (hq.mem_or_mem h5).resolve_right fun hu' => Set.disjoint_left.mp hU hu hu'
    rcases hq.mem_or_mem h6 with h7 | h7
    · exact Or.inl ⟨b₁, h7, u₁, hu₁, h₁⟩
    · exact Or.inr ⟨b₂, h7, u₂, hu₂, h₂⟩

end FractionPrime

section TensorPrimes

variable {k k' : Type u} [Field k] [Field k'] (κ : k →+* k') {σ : Type} (m : Ideal (MvPolynomial σ k))
  [m.IsPrime]

/-- The ring homomorphism `Ψ : k̃[X] → K ⊗_k k̃` (`K` the field of fractions of `D = k[X]/m`) with
`Ψ(ι a) = [a] ⊗ 1` and `Ψ(c̃) = 1 ⊗ c̃` (the printed "canonical isomorphism of `k̃ ⊗_k k[X̄]` to `k̃[X̄]`",
p. 211, followed by the inclusion `D ⊆ K`); its kernel is `m k̃[X]`. -/
theorem exists_ringHom_tensor_fractionRing :
    letI := κ.toAlgebra
    ∃ Ψ : MvPolynomial σ k' →+* FractionRing (MvPolynomial σ k ⧸ m) ⊗[k] k',
      (∀ a : MvPolynomial σ k, Ψ (MvPolynomial.map κ a) =
        algebraMap (MvPolynomial σ k ⧸ m) (FractionRing (MvPolynomial σ k ⧸ m))
          (Ideal.Quotient.mk m a) ⊗ₜ 1) ∧
      (∀ c : k', Ψ (MvPolynomial.C c) = 1 ⊗ₜ c) ∧
      RingHom.ker Ψ = m.map (MvPolynomial.map κ) := by
  let := κ.toAlgebra
  have hD : IsDomain (MvPolynomial σ k ⧸ m) := Ideal.Quotient.isDomain m
  set D := MvPolynomial σ k ⧸ m
  set K := FractionRing D
  let e : k' ⊗[k] MvPolynomial σ k ≃ₐ[k'] MvPolynomial σ k' :=
    MvPolynomial.algebraTensorAlgEquiv k k'
  let mk : MvPolynomial σ k →ₐ[k] D := Ideal.Quotient.mkₐ k m
  let incl : D →ₐ[k] K := IsScalarTower.toAlgHom k D K
  have hincl : Function.Injective incl := IsFractionRing.injective D K
  let θ : MvPolynomial σ k →ₐ[k] K := incl.comp mk
  let g : k' ⊗[k] MvPolynomial σ k →ₐ[k] k' ⊗[k] K := Algebra.TensorProduct.map (AlgHom.id k k') θ
  let Ψ : MvPolynomial σ k' →+* K ⊗[k] k' :=
    ((Algebra.TensorProduct.comm k k' K).toAlgHom.toRingHom).comp
      (g.toRingHom.comp (e.symm.toAlgHom.toRingHom))
  refine ⟨Ψ, ?_, ?_, ?_⟩
  · intro a
    have h1 : e.symm (MvPolynomial.map κ a) = 1 ⊗ₜ a :=
      MvPolynomial.algebraTensorAlgEquiv_symm_map (σ := σ) k k' a
    show Algebra.TensorProduct.comm k k' K (g (e.symm (MvPolynomial.map κ a))) = _
    rw [h1]
    simp [g, θ, incl, mk]
    rfl
  · intro c
    have h1 : e.symm (MvPolynomial.C c) = c ⊗ₜ 1 := by
      rw [← MvPolynomial.algebraMap_eq, AlgEquiv.commutes]; rfl
    show Algebra.TensorProduct.comm k k' K (g (e.symm (MvPolynomial.C c))) = _
    rw [h1]
    simp [g]
  · refine le_antisymm ?_ ?_
    swap
    · rw [Ideal.map_le_iff_le_comap]
      intro a ha
      rw [Ideal.mem_comap, RingHom.mem_ker]
      have h1 : e.symm (MvPolynomial.map κ a) = 1 ⊗ₜ a :=
        MvPolynomial.algebraTensorAlgEquiv_symm_map (σ := σ) k k' a
      show Algebra.TensorProduct.comm k k' K (g (e.symm (MvPolynomial.map κ a))) = 0
      rw [h1]
      have : mk a = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr ha
      simp [g, θ, incl, this]
    intro x hx
    rw [RingHom.mem_ker] at hx
    have hx' : g (e.symm x) = 0 := by
      have : Algebra.TensorProduct.comm k k' K (g (e.symm x)) = 0 := hx
      simpa using this
    have hg : ∀ y, g y = Algebra.TensorProduct.map (AlgHom.id k k') incl
        (Algebra.TensorProduct.map (AlgHom.id k k') mk y) := by
      intro y
      induction y using TensorProduct.inductionOn with
      | tmul a b => simp [g, θ]
      | add y y' hy hy' => rw [map_add, map_add, map_add, hy, hy']
    have hinj : Function.Injective (Algebra.TensorProduct.map (AlgHom.id k k') incl) :=
      Module.Flat.lTensor_preserves_injective_linearMap _ hincl
    have h2 : Algebra.TensorProduct.map (AlgHom.id k k') mk (e.symm x) = 0 := by
      apply hinj
      rw [map_zero, ← hg]; exact hx'
    have h3 : e.symm x ∈ RingHom.ker (Algebra.TensorProduct.map (AlgHom.id k k') mk) := h2
    rw [Algebra.TensorProduct.lTensor_ker mk Ideal.Quotient.mk_surjective] at h3
    have h3' : e.symm x ∈ Ideal.map (Algebra.TensorProduct.includeRight : MvPolynomial σ k →ₐ[k] k' ⊗[k] MvPolynomial σ k) (RingHom.ker mk) := h3
    have hle : Ideal.map (Algebra.TensorProduct.includeRight :
        MvPolynomial σ k →ₐ[k] k' ⊗[k] MvPolynomial σ k) (RingHom.ker mk) ≤
        Ideal.comap e.toAlgHom.toRingHom (m.map (MvPolynomial.map κ)) := by
      rw [Ideal.map_le_iff_le_comap]
      intro a ha
      rw [Ideal.mem_comap]
      have ha' : a ∈ m := by
        have : mk a = 0 := ha
        exact Ideal.Quotient.eq_zero_iff_mem.mp this
      have : e (Algebra.TensorProduct.includeRight a) = MvPolynomial.map κ a := by
        rw [Algebra.TensorProduct.includeRight_apply, MvPolynomial.algebraTensorAlgEquiv_tmul, one_smul]; rfl
      show e (Algebra.TensorProduct.includeRight a) ∈ m.map (MvPolynomial.map κ)
      rw [this]
      exact Ideal.mem_map_of_mem _ ha'
    have := hle h3
    simpa using this

/-- The elements `[a] ⊗ 1` of `K ⊗_k k̃` with `a ∉ m` are units. -/
theorem isUnit_tensor_fractionRing (a : MvPolynomial σ k) (ha : a ∉ m) :
    letI := κ.toAlgebra
    IsUnit (algebraMap (MvPolynomial σ k ⧸ m) (FractionRing (MvPolynomial σ k ⧸ m))
      (Ideal.Quotient.mk m a) ⊗ₜ[k] (1 : k')) := by
  let := κ.toAlgebra
  have hD : IsDomain (MvPolynomial σ k ⧸ m) := Ideal.Quotient.isDomain m
  set D := MvPolynomial σ k ⧸ m
  set K := FractionRing D
  have h0 : algebraMap D K (Ideal.Quotient.mk m a) ≠ 0 := by
    intro h
    exact ha (Ideal.Quotient.eq_zero_iff_mem.mp
      ((map_eq_zero_iff _ (IsFractionRing.injective D K)).mp h))
  have : IsUnit (algebraMap D K (Ideal.Quotient.mk m a)) := isUnit_iff_ne_zero.mpr h0
  exact this.map (Algebra.TensorProduct.includeLeftRingHom : K →+* K ⊗[k] k')

/-- Every element of `K ⊗_k k̃` is `Ψ(b)/Ψ(ι a)` with `a ∉ m` ("fractions"). -/
theorem exists_fraction_tensor_fractionRing :
    letI := κ.toAlgebra
    ∀ (Ψ : MvPolynomial σ k' →+* FractionRing (MvPolynomial σ k ⧸ m) ⊗[k] k')
      (_ : ∀ a : MvPolynomial σ k, Ψ (MvPolynomial.map κ a) =
        algebraMap (MvPolynomial σ k ⧸ m) (FractionRing (MvPolynomial σ k ⧸ m))
          (Ideal.Quotient.mk m a) ⊗ₜ 1)
      (_ : ∀ c : k', Ψ (MvPolynomial.C c) = 1 ⊗ₜ c)
      (c : FractionRing (MvPolynomial σ k ⧸ m) ⊗[k] k'),
    ∃ (b u : MvPolynomial σ k'), u ∈ m.primeCompl.map (MvPolynomial.map κ) ∧
      c * Ψ u = Ψ b := by
  let := κ.toAlgebra
  intro Ψ hΨ1 hΨ2 c
  have hD : IsDomain (MvPolynomial σ k ⧸ m) := Ideal.Quotient.isDomain m
  set D := MvPolynomial σ k ⧸ m
  set K := FractionRing D
  induction c using TensorProduct.inductionOn with
  | tmul z c' =>
    obtain ⟨⟨d, s⟩, hz⟩ := IsLocalization.mk'_surjective (nonZeroDivisors D) z
    obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective d
    obtain ⟨g, hg⟩ := Ideal.Quotient.mk_surjective (s : D)
    have hs0 : (s : D) ≠ 0 := nonZeroDivisors.coe_ne_zero s
    have hgm : g ∉ m := fun h => hs0 (hg ▸ Ideal.Quotient.eq_zero_iff_mem.mpr h)
    refine ⟨MvPolynomial.C c' * MvPolynomial.map κ f, MvPolynomial.map κ g, ⟨g, hgm, rfl⟩, ?_⟩
    have hspec : z * algebraMap D K (s : D) = algebraMap D K (Ideal.Quotient.mk m f) := by
      rw [← hz]; exact IsLocalization.mk'_spec K _ s
    have hspec' : z * algebraMap D K (Ideal.Quotient.mk m g) =
        algebraMap D K (Ideal.Quotient.mk m f) := by rw [hg]; exact hspec
    rw [map_mul, hΨ2, hΨ1, hΨ1]
    rw [Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one,
      hspec']
  | add c c' hc hc' =>
    obtain ⟨b, u, hu, h⟩ := hc
    obtain ⟨b', u', hu', h'⟩ := hc'
    refine ⟨b * u' + b' * u, u * u', Submonoid.mul_mem _ hu hu', ?_⟩
    rw [map_add, map_mul, map_mul, map_mul, ← h, ← h']; ring

/-- p. 211: the primes `q̃` of `k̃[X̄]` with `q̃ ∩ k[X̄] = (0)` ("`q̃ ∩ k[X̄] = m`" before dividing by `m`)
are among the primes of `K ⊗_k k̃`, `K = Frac(k[X]/m)`. -/
theorem exists_ringHom_tensor_fractionRing_forall_isPrime_comap_eq :
    letI := κ.toAlgebra
    ∃ Ψ : MvPolynomial σ k' →+* FractionRing (MvPolynomial σ k ⧸ m) ⊗[k] k',
      ∀ q : Ideal (MvPolynomial σ k'), q.IsPrime → q.comap (MvPolynomial.map κ) = m →
        ∃ p : Ideal (FractionRing (MvPolynomial σ k ⧸ m) ⊗[k] k'), p.IsPrime ∧ p.comap Ψ = q := by
  let := κ.toAlgebra
  obtain ⟨Ψ, hΨ1, hΨ2, hker⟩ := exists_ringHom_tensor_fractionRing κ m
  refine ⟨Ψ, fun q hq hqm => ?_⟩
  let U : Submonoid (MvPolynomial σ k') := m.primeCompl.map (MvPolynomial.map κ)
  have hkerq : RingHom.ker Ψ ≤ q :=
    hker.le.trans (Ideal.map_le_iff_le_comap.mpr hqm.ge)
  have hU : Disjoint (U : Set (MvPolynomial σ k')) (q : Set (MvPolynomial σ k')) := by
    rw [Set.disjoint_left]
    rintro _ ⟨a, ha, rfl⟩ hq'
    exact ha (hqm ▸ hq')
  exact exists_isPrime_comap_eq_of_fraction Ψ U
    (fun c => exists_fraction_tensor_fractionRing κ m Ψ hΨ1 hΨ2 c) q hkerq hU

/-- The ring `K ⊗_k k̃` is the localization of `k̃[X]/m k̃[X]` at the image of `ι(k[X] ∖ m)`
(`Ψ` induces `k̃[X]/(m k̃[X]) → K ⊗_k k̃`): "`k̃ ⊗_k k[X̄] ≅ k̃[X̄]`" (p. 211), localized at the nonzero
elements of `k[X̄] = k[X]/m`. -/
theorem exists_isLocalization_tensor_fractionRing :
    letI := κ.toAlgebra
    ∃ (Ψ : MvPolynomial σ k' →+* FractionRing (MvPolynomial σ k ⧸ m) ⊗[k] k')
      (Ψb : (MvPolynomial σ k' ⧸ m.map (MvPolynomial.map κ)) →+*
        FractionRing (MvPolynomial σ k ⧸ m) ⊗[k] k'),
      (∀ b, Ψb (Ideal.Quotient.mk _ b) = Ψ b) ∧
      (∀ a : MvPolynomial σ k, Ψ (MvPolynomial.map κ a) =
        algebraMap (MvPolynomial σ k ⧸ m) (FractionRing (MvPolynomial σ k ⧸ m))
          (Ideal.Quotient.mk m a) ⊗ₜ 1) ∧
      RingHom.ker Ψ = m.map (MvPolynomial.map κ) ∧
      (∀ c : FractionRing (MvPolynomial σ k ⧸ m) ⊗[k] k', ∃ (b u : MvPolynomial σ k'),
        u ∈ m.primeCompl.map (MvPolynomial.map κ) ∧ c * Ψ u = Ψ b) ∧
      (∀ q : Ideal (MvPolynomial σ k'), q.IsPrime → q.comap (MvPolynomial.map κ) = m →
        ∃ (p : Ideal (FractionRing (MvPolynomial σ k ⧸ m) ⊗[k] k')) (_ : p.IsPrime),
          p.comap Ψ = q ∧ ringKrullDim (Localization.AtPrime p) =
            (q.map (Ideal.Quotient.mk (m.map (MvPolynomial.map κ)))).height) ∧
      letI := Ψb.toAlgebra
      IsLocalization ((m.primeCompl.map (MvPolynomial.map κ)).map
        (Ideal.Quotient.mk (m.map (MvPolynomial.map κ)))) (FractionRing (MvPolynomial σ k ⧸ m) ⊗[k] k') := by
  let := κ.toAlgebra
  obtain ⟨Ψ, hΨ1, hΨ2, hker⟩ := exists_ringHom_tensor_fractionRing κ m
  have hfr := exists_fraction_tensor_fractionRing κ m Ψ hΨ1 hΨ2
  let Ψb := Ideal.Quotient.lift (m.map (MvPolynomial.map κ)) Ψ (fun a ha => by
    rw [← RingHom.mem_ker, hker]; exact ha)
  let : Algebra (MvPolynomial σ k' ⧸ m.map (MvPolynomial.map κ))
      (FractionRing (MvPolynomial σ k ⧸ m) ⊗[k] k') := Ψb.toAlgebra
  have hloc : IsLocalization ((m.primeCompl.map (MvPolynomial.map κ)).map
        (Ideal.Quotient.mk (m.map (MvPolynomial.map κ)))) (FractionRing (MvPolynomial σ k ⧸ m) ⊗[k] k') := by
    rw [isLocalization_iff]
    refine ⟨?_, ?_, ?_⟩
    · rintro ⟨_, ⟨u, ⟨a, ha, rfl⟩, rfl⟩⟩
      show IsUnit (Ψb (Ideal.Quotient.mk _ (MvPolynomial.map κ a)))
      rw [Ideal.Quotient.lift_mk, hΨ1]
      exact isUnit_tensor_fractionRing κ m a ha
    · intro z
      obtain ⟨b, u, hu, h⟩ := hfr z
      exact ⟨(Ideal.Quotient.mk _ b, ⟨Ideal.Quotient.mk _ u, u, hu, rfl⟩), by
        show z * Ψb (Ideal.Quotient.mk _ u) = Ψb (Ideal.Quotient.mk _ b)
        rw [Ideal.Quotient.lift_mk, Ideal.Quotient.lift_mk]; exact h⟩
    · intro x y hxy
      obtain ⟨bx, rfl⟩ := Ideal.Quotient.mk_surjective x
      obtain ⟨by', rfl⟩ := Ideal.Quotient.mk_surjective y
      have h1 : Ψ bx = Ψ by' := hxy
      have h2 : bx - by' ∈ m.map (MvPolynomial.map κ) := by
        rw [← hker, RingHom.mem_ker, map_sub, h1, sub_self]
      refine ⟨1, ?_⟩
      simp only [OneMemClass.coe_one, one_mul]
      exact (Ideal.Quotient.eq.mpr h2)
  refine ⟨Ψ, Ψb, fun b => Ideal.Quotient.lift_mk _ _ _, hΨ1, hker, hfr, ?_, hloc⟩
  intro q hq hqm
  have hkerq : RingHom.ker Ψ ≤ q := hker.le.trans (Ideal.map_le_iff_le_comap.mpr hqm.ge)
  have hU : Disjoint ((m.primeCompl.map (MvPolynomial.map κ) : Submonoid _) : Set (MvPolynomial σ k'))
      (q : Set (MvPolynomial σ k')) := by
    rw [Set.disjoint_left]
    rintro _ ⟨a, ha, rfl⟩ hq'
    exact ha (hqm ▸ hq')
  obtain ⟨p, hpp, hpq⟩ := exists_isPrime_comap_eq_of_fraction Ψ _ hfr q hkerq hU
  refine ⟨p, hpp, hpq, ?_⟩
  -- `C_p` is the localization of `E = k̃[X]/(m k̃[X])` at the prime `q̄ = q E`
  have hX : p.comap Ψb = q.map (Ideal.Quotient.mk (m.map (MvPolynomial.map κ))) := by
    have h1 : (p.comap Ψb).comap (Ideal.Quotient.mk (m.map (MvPolynomial.map κ))) = q := by
      rw [Ideal.comap_comap]
      have : Ψb.comp (Ideal.Quotient.mk (m.map (MvPolynomial.map κ))) = Ψ :=
        RingHom.ext (fun b => (Ideal.Quotient.lift_mk _ _ _ : Ψb (Ideal.Quotient.mk _ b) = Ψ b))
      rw [this, hpq]
    have h2 := Ideal.map_comap_of_surjective (Ideal.Quotient.mk (m.map (MvPolynomial.map κ)))
      Ideal.Quotient.mk_surjective (p.comap Ψb)
    rw [h1] at h2
    exact h2.symm
  have : (p.comap Ψb).IsPrime := Ideal.comap_isPrime _ _
  have := IsLocalization.isLocalization_isLocalization_atPrime_isLocalization
    (((m.primeCompl.map (MvPolynomial.map κ)).map
        (Ideal.Quotient.mk (m.map (MvPolynomial.map κ))))) (Localization.AtPrime p) p
  rw [IsLocalization.AtPrime.ringKrullDim_eq_height (p.comap Ψb) (Localization.AtPrime p), hX]

end TensorPrimes

section AssociatedPrimesPoly

variable {k k' : Type u} [Field k] [Field k'] (κ : k →+* k') {σ : Type} [Finite σ]
  (m : Ideal (MvPolynomial σ k)) [m.IsPrime]

omit [Finite σ] in
/-- The elements `ι(a)`, `a ∈ k[X] ∖ m`, are non-zero-divisors modulo `m k̃[X]`
(`k[X]/m` is a domain and `k̃[X]` is flat over `k[X]`; here through `k̃[X]/m k̃[X] ⊆ K ⊗_k k̃`,
`exists_ringHom_tensor_fractionRing`). -/
theorem mem_map_of_map_mul_mem_map {a : MvPolynomial σ k} (ha : a ∉ m) {b : MvPolynomial σ k'}
    (h : MvPolynomial.map κ a * b ∈ m.map (MvPolynomial.map κ)) :
    b ∈ m.map (MvPolynomial.map κ) := by
  obtain ⟨Ψ, hΨ1, -, hker⟩ := exists_ringHom_tensor_fractionRing κ m
  rw [← hker, RingHom.mem_ker] at h ⊢
  rw [map_mul, hΨ1] at h
  exact (isUnit_tensor_fractionRing κ m a ha).mul_right_eq_zero.mp h

/-- p. 211: every associated prime `q` of `m k̃[X₂,…,X_r]` lies over `m` (`q ∩ k[X] = m`), for every
field extension `k̃/k`: the elements of `k[X] ∖ m` are non-zero-divisors modulo `m k̃[X]`
(`mem_map_of_map_mul_mem_map`), so they lie in no associated prime. -/
theorem comap_eq_of_mem_associatedPrimes {q : Ideal (MvPolynomial σ k')}
    (hq : q ∈ associatedPrimes (MvPolynomial σ k')
      (MvPolynomial σ k' ⧸ m.map (MvPolynomial.map κ))) :
    q.comap (MvPolynomial.map κ) = m := by
  have hqp : q.IsPrime := hq.1
  apply le_antisymm
  · intro a ha
    by_contra han
    rw [Ideal.mem_comap] at ha
    obtain ⟨-, x, hx⟩ := isAssociatedPrime_iff.mp hq
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective x
    have h1 : MvPolynomial.map κ a ∈
        (⊥ : Submodule (MvPolynomial σ k') (MvPolynomial σ k' ⧸ m.map (MvPolynomial.map κ))).colon
          {Ideal.Quotient.mk (m.map (MvPolynomial.map κ)) b} := hx ▸ ha
    rw [Submodule.mem_colon_singleton, Submodule.mem_bot, smul_quotient_mk,
      Ideal.Quotient.eq_zero_iff_mem] at h1
    have h2 := mem_map_of_map_mul_mem_map κ m han h1
    have h3 : (⊥ : Submodule (MvPolynomial σ k')
        (MvPolynomial σ k' ⧸ m.map (MvPolynomial.map κ))).colon
          {Ideal.Quotient.mk (m.map (MvPolynomial.map κ)) b} = ⊤ := by
      rw [eq_top_iff]
      intro r _
      rw [Submodule.mem_colon_singleton, Submodule.mem_bot, smul_quotient_mk,
        Ideal.Quotient.eq_zero_iff_mem]
      exact Ideal.mul_mem_left _ _ h2
    exact hqp.ne_top (hx.trans h3)
  · rw [← Ideal.map_le_iff_le_comap]
    exact le_of_mem_associatedPrimes_quotient hq

end AssociatedPrimesPoly

section CardBound

variable {R Rb : Type u} [CommRing R] [IsRegularLocalRing R] [IsDomain R]
  [CommRing Rb] [IsRegularLocalRing Rb] [IsDomain Rb] {P : Ideal R}

/-- Lemma 4 (1), "the number of `R̃'` does not exceed the separable degree of the residue field
extension `k → k̃`" (p. 212), along the printed route: `R̃' ↦ q̃ = M̃'k̃[X̄]` is injective with values in the
primes of `k̃[X̄] = k̃ ⊗_k k[X̄]` over `m̄'` (`q̃ ∩ k[X̄] = (0)`), and these are primes of `K ⊗_k k̃`,
`K = Frac(k[X̄])`, which has at most `[k̃ : k]_s` of them (`K/k` finitely generated, `k̃/k` algebraic). -/
theorem canonicalTransforms_card_le_sepDegree (α : R →+* Rb) [IsLocalHom α]
    (hα : RingHom.MapsRSOP α) (hP : P.IsPrime) (hS : IsRegularLocalRing (R ⧸ P))
    (t : MonoidalTransform R P) (halg : RingHom.IsResiduallyAlgebraic α) :
    letI := (ResidueField.map α).toAlgebra
    Cardinal.mk ↥(canonicalTransforms α (Pb := P.map α) t) ≤
      Field.sepDegree (ResidueField R) (ResidueField Rb) := by
  classical
  let := (ResidueField.map α).toAlgebra
  obtain ⟨r, π, π', hπ, hkπ, hπ', hkπ', hcomm, hπC, hπ'C⟩ :=
    t.exists_residue_charts α hα hP hS
  have hkπM' : RingHom.ker π ≤ t.M' := hkπ.trans t.le
  have hm : (t.M'.map π).IsPrime := Ideal.map_isPrime_of_surjective hπ hkπM'
  obtain ⟨Ψ, hΨ⟩ := exists_ringHom_tensor_fractionRing_forall_isPrime_comap_eq
    (ResidueField.map α) (t.M'.map π)
  set K := FractionRing (MvPolynomial (Fin r) (ResidueField R) ⧸ t.M'.map π) with hK
  have hD : IsDomain (MvPolynomial (Fin r) (ResidueField R) ⧸ t.M'.map π) :=
    Ideal.Quotient.isDomain _
  have : Algebra.FiniteType (ResidueField R) (MvPolynomial (Fin r) (ResidueField R) ⧸ t.M'.map π) :=
    Algebra.FiniteType.of_surjective (A := MvPolynomial (Fin r) (ResidueField R))
      (Ideal.Quotient.mkₐ (ResidueField R) _) Ideal.Quotient.mk_surjective
  have hfg : (⊤ : IntermediateField (ResidueField R) K).FG := by
    have : Algebra.EssFiniteType (ResidueField R) K := inferInstance
    exact IntermediateField.fg_top (ResidueField R) K
  have halg' : Algebra.IsAlgebraic (ResidueField R) (ResidueField Rb) := halg
  -- the injection `{M̃'} → Spec(K ⊗_k k̃)`
  have hex : ∀ N : ↥(LiftPrimes α (RingHom.MapsRSOP.injective α hα) t),
      ∃ p : PrimeSpectrum (K ⊗[ResidueField R] ResidueField Rb),
        p.asIdeal.comap Ψ = N.1.map π' := by
    intro N
    obtain ⟨hqp, hq, -⟩ := t.map_mem_minimalPrimes_of_mem_liftPrimes α hα (Or.inl halg) π π' hπ hkπ
      hπ' hkπ' hcomm hπC N.1 N.2
    obtain ⟨p, hp, hpq⟩ := hΨ _ hqp hq
    exact ⟨⟨p, hp⟩, hpq⟩
  choose f hf using hex
  have hfinj : Function.Injective f := by
    intro N₁ N₂ h
    have h1 : N₁.1.map π' = N₂.1.map π' := by rw [← hf N₁, ← hf N₂, h]
    have hk₁ : RingHom.ker π' ≤ N₁.1 := hkπ'.trans (MonoidalTransform.ofLift α hα t N₁.1 N₁.2).le
    have hk₂ : RingHom.ker π' ≤ N₂.1 := hkπ'.trans (MonoidalTransform.ofLift α hα t N₂.1 N₂.2).le
    have e : ∀ N : Ideal (blowupAlgebra Rb (P.map α) (α t.x)), RingHom.ker π' ≤ N →
        N = (N.map π').comap π' := fun N hN => by
      rw [Ideal.comap_map_of_surjective _ hπ', ← RingHom.ker_eq_comap_bot, sup_eq_left.mpr hN]
    exact Subtype.ext ((e _ hk₁).trans ((congrArg (Ideal.comap π') h1).trans (e _ hk₂).symm))
  calc Cardinal.mk ↥(canonicalTransforms α (Pb := P.map α) t)
      = Cardinal.mk ↥(liftSubring α hα t '' LiftPrimes α (RingHom.MapsRSOP.injective α hα) t) := by
        rw [canonicalTransforms_eq_image_liftSubring α hα t]
    _ ≤ Cardinal.mk ↥(LiftPrimes α (RingHom.MapsRSOP.injective α hα) t) := Cardinal.mk_image_le
    _ ≤ Cardinal.mk (PrimeSpectrum (K ⊗[ResidueField R] ResidueField Rb)) :=
        Cardinal.mk_le_of_injective hfinj
    _ ≤ _ := cardinalMk_primeSpectrum_tensorProduct_le_sepDegree_of_fg _ _ _ hfg

end CardBound

section FibreAbstract

variable {A C : Type*} [CommRing A] [CommRing C]

/-- Localization of an image at a prime: if `Φ : A → C` has "fractions" (every `c ∈ C` is `Φ(a)/Φ(w)`
with `w ∉ N`) and `p` is a prime of `C` with `Φ⁻¹(p) = N`, then `C_p` is the quotient of `A_N` by the
extension of `ker Φ` (the printed passage from `Ã'_{M̃'}/M'Ã'_{M̃'}` to the local ring `k̃[X̄]_{q̃}`). -/
theorem exists_surjective_ker_eq_localization_of_fraction (Φ : A →+* C) (N : Ideal A) [N.IsPrime]
    (p : Ideal C) [p.IsPrime] (hp : p.comap Φ = N)
    (hfrac : ∀ c : C, ∃ (a w : A), w ∉ N ∧ c * Φ w = Φ a)
    (T : Type*) [CommRing T] [Algebra A T] [IsLocalization.AtPrime T N] :
    ∃ Θ : T →+* Localization.AtPrime p, Function.Surjective Θ ∧
      (∀ a, Θ (algebraMap A T a) = algebraMap C (Localization.AtPrime p) (Φ a)) ∧
      RingHom.ker Θ = (RingHom.ker Φ).map (algebraMap A T) := by
  classical
  have hnot : ∀ w : A, w ∉ N → Φ w ∉ p := fun w hw h => hw (hp ▸ Ideal.mem_comap.mpr h)
  let Θ : T →+* Localization.AtPrime p := IsLocalization.lift (M := N.primeCompl) (S := T)
    (g := (algebraMap C (Localization.AtPrime p)).comp Φ) (fun y => by
      exact IsLocalization.map_units (Localization.AtPrime p) (⟨Φ y, hnot y y.2⟩ : p.primeCompl))
  have hΘ : ∀ a, Θ (algebraMap A T a) = algebraMap C (Localization.AtPrime p) (Φ a) := fun a =>
    IsLocalization.lift_eq _ a
  have hnotN : ∀ (u : C) (a w : A), u ∉ p → u * Φ w = Φ a → Φ w ∉ p → a ∉ N := by
    intro u a w hu h hw haN
    have : Φ a ∈ p := by
      have : a ∈ p.comap Φ := hp ▸ haN
      exact this
    rw [← h] at this
    exact (‹p.IsPrime›.mem_or_mem this).elim hu hw
  refine ⟨Θ, ?_, hΘ, ?_⟩
  · intro z
    obtain ⟨⟨c, s⟩, hz⟩ := IsLocalization.mk'_surjective p.primeCompl z
    obtain ⟨a1, w1, hw1, h1⟩ := hfrac c
    obtain ⟨a2, w2, hw2, h2⟩ := hfrac (s : C)
    have ha2 : a2 ∉ N := hnotN s a2 w2 s.2 h2 (hnot w2 hw2)
    have hwa : w1 * a2 ∈ N.primeCompl := fun h =>
      (‹N.IsPrime›.mem_or_mem h).elim hw1 ha2
    refine ⟨IsLocalization.mk' T (a1 * w2) (⟨w1 * a2, hwa⟩ : N.primeCompl), ?_⟩
    have hu : IsUnit (algebraMap C (Localization.AtPrime p) (Φ (w1 * a2))) :=
      IsLocalization.map_units (Localization.AtPrime p)
        (⟨Φ (w1 * a2), hnot _ hwa⟩ : p.primeCompl)
    have e1 : Θ (IsLocalization.mk' T (a1 * w2) (⟨w1 * a2, hwa⟩ : N.primeCompl)) *
        algebraMap C (Localization.AtPrime p) (Φ (w1 * a2)) =
        algebraMap C (Localization.AtPrime p) (Φ (a1 * w2)) := by
      have := congrArg Θ (IsLocalization.mk'_spec T (a1 * w2) (⟨w1 * a2, hwa⟩ : N.primeCompl))
      rwa [map_mul, hΘ, hΘ] at this
    have e2 : z * algebraMap C (Localization.AtPrime p) (Φ (w1 * a2)) =
        algebraMap C (Localization.AtPrime p) (Φ (a1 * w2)) := by
      have hzs : z * algebraMap C (Localization.AtPrime p) (s : C) =
          algebraMap C (Localization.AtPrime p) c := by
        rw [← hz]; exact IsLocalization.mk'_spec _ _ _
      have h3 : Φ (w1 * a2) = Φ w1 * ((s : C) * Φ w2) := by rw [h2, map_mul]
      have h4 : Φ (a1 * w2) = (c * Φ w1) * Φ w2 := by rw [h1, map_mul]
      rw [h3, h4, map_mul, map_mul, map_mul, map_mul, ← hzs]
      ring
    exact (hu.mul_left_inj).mp (e1.trans e2.symm)
  · ext y
    obtain ⟨⟨a, s'⟩, hya⟩ := IsLocalization.mk'_surjective N.primeCompl y
    have hya' : IsLocalization.mk' T a s' = y := hya
    rw [← hya']
    constructor
    · intro hy
      rw [RingHom.mem_ker] at hy
      have hspec := congrArg Θ (IsLocalization.mk'_spec T a s')
      rw [map_mul, hy, zero_mul, hΘ] at hspec
      obtain ⟨⟨u, hu⟩, hu0⟩ := (IsLocalization.map_eq_zero_iff p.primeCompl
        (Localization.AtPrime p) (Φ a)).mp hspec.symm
      obtain ⟨a3, w3, hw3, h3⟩ := hfrac u
      have ha3 : a3 ∉ N := hnotN u a3 w3 hu h3 (hnot w3 hw3)
      have hker : a3 * a ∈ RingHom.ker Φ := by
        rw [RingHom.mem_ker, map_mul, ← h3]
        have : u * Φ a = 0 := hu0
        calc u * Φ w3 * Φ a = Φ w3 * (u * Φ a) := by ring
          _ = 0 := by rw [this, mul_zero]
      have hunit : IsUnit (algebraMap A T (a3 * (s' : A))) :=
        IsLocalization.map_units T (⟨a3 * s', fun h =>
          (‹N.IsPrime›.mem_or_mem h).elim ha3 s'.2⟩ : N.primeCompl)
      obtain ⟨v, hv⟩ := hunit.exists_right_inv
      have : IsLocalization.mk' T a s' = algebraMap A T (a3 * a) * v := by
        have h5 : IsLocalization.mk' T a s' * algebraMap A T (a3 * (s' : A)) =
            algebraMap A T (a3 * a) := by
          rw [map_mul, ← mul_assoc, mul_comm _ (algebraMap A T a3), mul_assoc,
            IsLocalization.mk'_spec]
          rw [← map_mul, mul_comm]
        calc IsLocalization.mk' T a s' = IsLocalization.mk' T a s' *
              (algebraMap A T (a3 * (s' : A)) * v) := by rw [hv, mul_one]
          _ = _ := by rw [← mul_assoc, h5]
      rw [this]
      exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ hker)
    · intro hy
      have hle : (RingHom.ker Φ).map (algebraMap A T) ≤ RingHom.ker Θ := by
        rw [Ideal.map_le_iff_le_comap]
        intro a ha
        rw [Ideal.mem_comap, RingHom.mem_ker, hΘ, (RingHom.mem_ker.mp ha), map_zero]
      exact hle hy

end FibreAbstract

section FibreAbstract2

variable {A0 A' B B' C : Type*} [CommRing A0] [CommRing A'] [CommRing B] [CommRing B']
  [CommRing C]

/-- Abstract form of the passage from `Ã'_{M̃'}` to the fibre `K ⊗_k k̃` localized at a prime
(p. 211): the local ring `C_p` is the quotient of `A'_N` by the extension of `M'A'`. -/
theorem exists_surjective_ker_eq_of_chart_data (bm : A0 →+* A') (π : A0 →+* B) (π' : A' →+* B')
    (ι : B →+* B') (hπ : Function.Surjective π) (hπ' : Function.Surjective π')
    (hcomm : π'.comp bm = ι.comp π) (M' : Ideal A0) [(M'.map π).IsPrime] (N : Ideal A') [N.IsPrime]
    (hkN : RingHom.ker π' ≤ N) (hq : (N.map π').comap ι = M'.map π)
    (hkM : RingHom.ker π' ≤ M'.map bm)
    (Ψ : B' →+* C) (hker : RingHom.ker Ψ = (M'.map π).map ι)
    (hfr : ∀ c : C, ∃ (b u : B'), u ∈ (M'.map π).primeCompl.map ι ∧ c * Ψ u = Ψ b)
    (p : Ideal C) [p.IsPrime] (hpq : p.comap Ψ = N.map π')
    (T : Type*) [CommRing T] [Algebra A' T] [IsLocalization.AtPrime T N] :
    ∃ Θ : T →+* Localization.AtPrime p, Function.Surjective Θ ∧
      RingHom.ker Θ = (M'.map bm).map (algebraMap A' T) := by
  have hNeq : N = (N.map π').comap π' := by
    rw [Ideal.comap_map_of_surjective _ hπ', ← RingHom.ker_eq_comap_bot, sup_eq_left.mpr hkN]
  have hpΦ : p.comap (Ψ.comp π') = N := by
    rw [← Ideal.comap_comap, hpq, ← hNeq]
  have hfrac : ∀ c : C, ∃ (a w : A'), w ∉ N ∧ c * (Ψ.comp π') w = (Ψ.comp π') a := by
    intro c
    obtain ⟨b, u, ⟨a0, ha0, hau⟩, h⟩ := hfr c
    obtain ⟨a, hab⟩ := hπ' b
    obtain ⟨y0, hy0⟩ := hπ a0
    have hu : u = π' (bm y0) := by
      have h2 : π' (bm y0) = ι (π y0) := RingHom.congr_fun hcomm y0
      rw [h2, hy0, ← hau]
    refine ⟨a, bm y0, fun hw => ha0 ?_, ?_⟩
    · have h1 : π' (bm y0) ∈ N.map π' := Ideal.mem_map_of_mem _ hw
      rw [← hu, ← hau, ← Ideal.mem_comap, hq] at h1
      exact h1
    · rw [RingHom.comp_apply, RingHom.comp_apply, ← hu, hab]
      exact h
  obtain ⟨Θ, hΘsurj, hΘ, hΘker⟩ := exists_surjective_ker_eq_localization_of_fraction (Ψ.comp π') N p
    hpΦ hfrac T
  refine ⟨Θ, hΘsurj, ?_⟩
  rw [hΘker]
  congr 1
  rw [← RingHom.comap_ker, hker]
  have himg : (M'.map bm).map π' = (M'.map π).map ι := by
    rw [Ideal.map_map, Ideal.map_map, hcomm]
  apply le_antisymm
  · intro z hz
    rw [Ideal.mem_comap, ← himg] at hz
    obtain ⟨i, hi, hiz⟩ := (Ideal.mem_map_iff_of_surjective π' hπ').mp hz
    have : z - i ∈ RingHom.ker π' := by rw [RingHom.mem_ker, map_sub, hiz, sub_self]
    have h2 := (M'.map bm).add_mem (hkM this) hi
    simpa using h2
  · intro z hz
    rw [Ideal.mem_comap, ← himg]
    exact Ideal.mem_map_of_mem _ hz

end FibreAbstract2

noncomputable section Fibre2

variable {R Rb : Type u} [CommRing R] [IsRegularLocalRing R] [IsDomain R]
  [CommRing Rb] [IsRegularLocalRing Rb] [IsDomain Rb] {P : Ideal R}

/-- `M̃Ã' ⊆ M'Ã'`: `M̃ = MR̄` and `M ⊆ M'` (p. 211). -/
theorem MonoidalTransform.map_maximalIdeal_le_map_blowupMap (α : R →+* Rb) [IsLocalHom α]
    (hα : RingHom.MapsRSOP α) (t : MonoidalTransform R P) :
    (maximalIdeal Rb).map (algebraMap Rb (blowupAlgebra Rb (P.map α) (α t.x))) ≤
      t.M'.map (blowupMap α (RingHom.MapsRSOP.injective α hα) P t.x) := by
  rw [← hα.map_maximalIdeal, Ideal.map_map]
  have : (algebraMap Rb (blowupAlgebra Rb (P.map α) (α t.x))).comp α =
      (blowupMap α (RingHom.MapsRSOP.injective α hα) P t.x).comp
        (algebraMap R (blowupAlgebra R P t.x)) :=
    RingHom.ext fun a => (blowupMap_algebraMap α (RingHom.MapsRSOP.injective α hα) P t.x a).symm
  rw [this, ← Ideal.map_map]
  exact Ideal.map_mono t.le

/-- Going down for the free extension `k[X] → k̃[X]` (p. 211): `ht q = ht m + ht(q k̃[X]/m k̃[X])`. -/
theorem height_eq_add_height_map_quotient {k k' : Type u} [Field k] [Field k'] (κ : k →+* k')
    {σ : Type*} [Finite σ] (m : Ideal (MvPolynomial σ k)) [m.IsPrime]
    (q : Ideal (MvPolynomial σ k')) [q.IsPrime] (hq : q.comap (MvPolynomial.map κ) = m) :
    q.height = m.height +
      (q.map (Ideal.Quotient.mk (m.map (MvPolynomial.map κ)))).height := by
  let : Algebra (MvPolynomial σ k) (MvPolynomial σ k') := (MvPolynomial.map (σ := σ) κ).toAlgebra
  have : Module.Flat (MvPolynomial σ k) (MvPolynomial σ k') := flat_mvPolynomial_map_of_field κ σ
  have : q.LiesOver m := ⟨hq.symm⟩
  exact Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown m q

/-- `Frac(k[X]/m)` is a finitely generated field extension of `k`. -/
theorem fg_top_fractionRing_quotient_mvPolynomial {k : Type u} [Field k] {σ : Type} [Finite σ]
    (m : Ideal (MvPolynomial σ k)) [m.IsPrime] :
    (⊤ : IntermediateField k (FractionRing (MvPolynomial σ k ⧸ m))).FG := by
  have hD : IsDomain (MvPolynomial σ k ⧸ m) := Ideal.Quotient.isDomain m
  have : Algebra.FiniteType k (MvPolynomial σ k ⧸ m) :=
    Algebra.FiniteType.of_surjective (A := MvPolynomial σ k)
      (Ideal.Quotient.mkₐ k _) Ideal.Quotient.mk_surjective
  exact IntermediateField.fg_top k (FractionRing (MvPolynomial σ k ⧸ m))

/-- The maximal ideal of `A_{M'}` extended along the local ring map `A_{M'} → B_N` induced by
`f : A → B` (`N ∩ A = M'`) is `M'B_N`. -/
theorem map_maximalIdeal_localRingHom {A0 A' : Type*} [CommRing A0] [CommRing A'] (f : A0 →+* A')
    (M' : Ideal A0) [M'.IsPrime] (N : Ideal A') [N.IsPrime] (h : M' = N.comap f) :
    (maximalIdeal (Localization.AtPrime M')).map (Localization.localRingHom M' N f h) =
      (M'.map f).map (algebraMap A' (Localization.AtPrime N)) := by
  rw [← IsLocalization.AtPrime.map_eq_maximalIdeal M' (Localization.AtPrime M'), Ideal.map_map,
    Ideal.map_map]
  congr 1
  exact RingHom.ext fun a => Localization.localRingHom_to_map M' N f h a

/-- Lemma 4 (1)–(3), the fibre `R̃'/M'R̃'` of `R' → R̃' = Ã'_{M̃'}` (pp. 211–212): it is the local ring
`k̃[X̄]_{q̃}` (`q̃ = M̃'k̃[X]`), the localization of `K ⊗_k k̃` at a prime. Consequently
`dim R̃' = dim R' + dim (R̃'/M'R̃')` (`ht q̃ = ht m̄' + ht q̃'`, flatness of `k[X] → k̃[X]`), the fibre
is regular if `R̄` is residually separable over `R` ("the localization of `k̃[X̄]` with respect to `q̃`
is regular", p. 212), and it is a field (`M'R̃' = M̃'`) if `R̄` is residually separable algebraic. -/
theorem MonoidalTransform.exists_fibre_properties (α : R →+* Rb) [IsLocalHom α]
    (hα : RingHom.MapsRSOP α) (hP : P.IsPrime) (hS : IsRegularLocalRing (R ⧸ P))
    (t : MonoidalTransform R P) (N : Ideal (blowupAlgebra Rb (P.map α) (α t.x)))
    (hN : N ∈ LiftPrimes α (RingHom.MapsRSOP.injective α hα) t) :
    ringKrullDim (MonoidalTransform.ofLift α hα t N hN).ring = ringKrullDim t.ring +
        ringKrullDim ((MonoidalTransform.ofLift α hα t N hN).ring ⧸
          (maximalIdeal t.ring).map (MonoidalTransform.ofLiftHom α hα t N hN)) ∧
      (RingHom.IsResiduallySeparable α →
        ∀ [IsLocalRing ((MonoidalTransform.ofLift α hα t N hN).ring ⧸
          (maximalIdeal t.ring).map (MonoidalTransform.ofLiftHom α hα t N hN))],
          IsRegularLocalRing ((MonoidalTransform.ofLift α hα t N hN).ring ⧸
            (maximalIdeal t.ring).map (MonoidalTransform.ofLiftHom α hα t N hN))) ∧
      (RingHom.IsResiduallySeparableAlgebraic α →
        ((maximalIdeal t.ring).map (MonoidalTransform.ofLiftHom α hα t N hN)).IsMaximal) := by
  classical
  have hαinj := RingHom.MapsRSOP.injective α hα
  obtain ⟨hPb, hSq⟩ := RingHom.MapsRSOP.isPrime_map_and_isRegularLocalRing_quotient hα hP hS
  obtain ⟨r, χ, χb, hχ, hχx, hχC, hχb, hχbx, hχbC, hπ, hkπ, hπ', hkπ', hcomm, hπC, hπ'C⟩ :=
    t.exists_charts_residue α hα hP hS
  have hPM : P ≤ maximalIdeal R := IsLocalRing.le_maximalIdeal hP.ne_top
  have hPbM : P.map α ≤ maximalIdeal Rb := le_maximalIdeal_map hα hP
  obtain ⟨π, hπdef⟩ : ∃ π, chartResidue hPM χ = π := ⟨_, rfl⟩
  obtain ⟨π', hπ'def⟩ : ∃ π', chartResidue hPbM χb = π' := ⟨_, rfl⟩
  rw [hπdef] at hπ hkπ hcomm
  rw [hπ'def] at hπ' hkπ' hcomm
  clear hπC hπ'C
  let := (ResidueField.map α).toAlgebra
  have hkπM' : RingHom.ker π ≤ t.M' := hkπ.trans t.le
  have hkN : RingHom.ker π' ≤ N := hkπ'.trans (MonoidalTransform.ofLift α hα t N hN).le
  have hNp : N.IsPrime := hN.1
  have hm : (t.M'.map π).IsPrime := Ideal.map_isPrime_of_surjective hπ hkπM'
  have hqp : (N.map π').IsPrime := Ideal.map_isPrime_of_surjective hπ' hkN
  have hq : (N.map π').comap (MvPolynomial.map (ResidueField.map α)) = t.M'.map π :=
    (comap_eq_iff_comap_map_eq _ π π' _ hπ hπ' hcomm hkπM' hkN).mp hN.2
  obtain ⟨Ψ, Ψb, hΨb, hΨ1, hker, hfr, hprime, hloc⟩ :=
    exists_isLocalization_tensor_fractionRing (ResidueField.map α) (t.M'.map π)
  obtain ⟨p, hpp, hpq, hdimC⟩ := hprime _ hqp hq
  let : Algebra (blowupAlgebra Rb (P.map α) (α t.x)) (MonoidalTransform.ofLift α hα t N hN).ring :=
    inferInstanceAs (Algebra (blowupAlgebra Rb (P.map α) (MonoidalTransform.ofLift α hα t N hN).x)
      (MonoidalTransform.ofLift α hα t N hN).ring)
  have : IsLocalization.AtPrime (MonoidalTransform.ofLift α hα t N hN).ring N :=
    inferInstanceAs (IsLocalization.AtPrime (MonoidalTransform.ofLift α hα t N hN).ring
      (MonoidalTransform.ofLift α hα t N hN).M')
  obtain ⟨Θ, hΘsurj, hΘker⟩ := exists_surjective_ker_eq_of_chart_data
    (blowupMap α hαinj P t.x) π π' (MvPolynomial.map (ResidueField.map α)) hπ hπ' hcomm t.M' N
    hkN hq (hkπ'.trans (t.map_maximalIdeal_le_map_blowupMap α hα)) Ψ hker hfr p hpq
    (MonoidalTransform.ofLift α hα t N hN).ring
  have hI : (maximalIdeal t.ring).map (MonoidalTransform.ofLiftHom α hα t N hN) =
      RingHom.ker Θ := by
    rw [hΘker]
    exact map_maximalIdeal_localRingHom (blowupMap α hαinj P t.x) t.M' N hN.2.symm
  let e : ((MonoidalTransform.ofLift α hα t N hN).ring ⧸
      (maximalIdeal t.ring).map (MonoidalTransform.ofLiftHom α hα t N hN)) ≃+*
        Localization.AtPrime p :=
    (Ideal.quotEquivOfEq hI).trans (RingHom.quotientKerEquivOfSurjective hΘsurj)
  have hF : ringKrullDim ((MonoidalTransform.ofLift α hα t N hN).ring ⧸
      (maximalIdeal t.ring).map (MonoidalTransform.ofLiftHom α hα t N hN)) =
        ringKrullDim (Localization.AtPrime p) := ringKrullDim_eq_of_ringEquiv e
  have := hP
  have := hPb
  have h1 := MonoidalTransform.ringKrullDim_eq_of_chart hSq
    (MonoidalTransform.ofLift α hα t N hN) χb hχb hχbx hχbC
  have h1' : ringKrullDim (MonoidalTransform.ofLift α hα t N hN).ring =
      ringKrullDim (Rb ⧸ P.map α) + ((N.map π').height : WithBot ℕ∞) + 1 := by
    rw [← hπ'def]; exact h1
  have h2 := MonoidalTransform.ringKrullDim_eq_of_chart hS t χ hχ hχx hχC
  have h2' : ringKrullDim t.ring = ringKrullDim (R ⧸ P) + ((t.M'.map π).height : WithBot ℕ∞) + 1 := by
    rw [← hπdef]; exact h2
  have hQ := t.ringKrullDim_quotient_map_eq α hα hP hS
  have hh := height_eq_add_height_map_quotient (ResidueField.map α) (t.M'.map π) (N.map π') hq
  refine ⟨?_, ?_, ?_⟩
  · rw [hF, hdimC, h1', h2', hQ, hh]
    push_cast
    ring
  · intro hsep _
    have hfg := fg_top_fractionRing_quotient_mvPolynomial (t.M'.map π)
    have : IsRegularLocalRing (Localization.AtPrime p) :=
      isRegularLocalRing_localization_tensorProduct_of_separable (ResidueField R)
        (FractionRing (MvPolynomial (Fin r) (ResidueField R) ⧸ t.M'.map π)) (ResidueField Rb)
        hsep hfg p
    exact IsRegularLocalRing.of_ringEquiv (R := Localization.AtPrime p) e.symm
  · intro hsepalg
    have : Algebra.IsSeparable (ResidueField R) (ResidueField Rb) := hsepalg
    have hfield : IsField (Localization.AtPrime p) :=
      isField_localization_tensorProduct_of_isSeparable (ResidueField R)
        (FractionRing (MvPolynomial (Fin r) (ResidueField R) ⧸ t.M'.map π)) (ResidueField Rb) p
    let : Field (Localization.AtPrime p) := hfield.toField
    have := RingHom.ker_isMaximal_of_surjective Θ hΘsurj
    rw [← hI] at this
    exact this

section RsopExtension

variable {A B : Type u} [CommRing A] [CommRing B] [IsLocalRing A] [IsLocalRing B]
  [IsNoetherianRing B]

open Classical in
/-- p. 212, "the image of a regular system of parameters of `R'` can be extended to a regular system
of parameters of `R̃'`": if `β : A → B` is a local homomorphism, `dim B = dim A + dim B/(M_A B)` and
the fibre `B/(M_A B)` is regular, then the image of a regular system of parameters of `A`, together
with lifts of a regular system of parameters of the fibre, is a regular system of parameters of `B`. -/
theorem exists_isRegularSystemOfParameters_image_union (β : A →+* B) [IsLocalHom β]
    (s : Finset A) (hs : IsRegularSystemOfParameters A s)
    [IsLocalRing (B ⧸ (maximalIdeal A).map β)]
    (hF : IsRegularLocalRing (B ⧸ (maximalIdeal A).map β))
    (hdim : ringKrullDim B = ringKrullDim A + ringKrullDim (B ⧸ (maximalIdeal A).map β)) :
    ∃ U : Finset B, IsRegularSystemOfParameters B (s.image β ∪ U) := by
  classical
  set I := (maximalIdeal A).map β with hI
  have hmk : Function.Surjective (Ideal.Quotient.mk I) := Ideal.Quotient.mk_surjective
  have hlocal : IsLocalHom (Ideal.Quotient.mk I) := IsLocalHom.of_surjective _ hmk
  obtain ⟨-, G, hG⟩ := (isRegularLocalRing_iff_exists_rsop (B ⧸ I)).mp hF
  let U : Finset B := G.image (Function.surjInv hmk)
  have hUG : ∀ g ∈ G, Ideal.Quotient.mk I (Function.surjInv hmk g) = g := fun g _ =>
    Function.surjInv_eq hmk g
  have hIspan : I = Ideal.span ((s.image β : Finset B) : Set B) := by
    rw [hI, ← hs.1, Finset.coe_image, Ideal.map_span]
  have hIle : I ≤ maximalIdeal B := Ideal.map_le_iff_le_comap.mpr fun a ha =>
    map_nonunit β a ha
  have hspan : Ideal.span (((s.image β ∪ U : Finset B)) : Set B) = maximalIdeal B := by
    apply le_antisymm
    · rw [Ideal.span_le]
      intro b hb
      rcases Finset.mem_union.mp hb with hb | hb
      · exact hIle (hIspan ▸ Ideal.subset_span hb)
      · obtain ⟨g, hg, rfl⟩ := Finset.mem_image.mp hb
        have h1 : Ideal.Quotient.mk I (Function.surjInv hmk g) ∈ maximalIdeal (B ⧸ I) := by
          rw [hUG g hg, ← hG.1]; exact Ideal.subset_span hg
        show _ ∈ maximalIdeal B
        rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
        rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at h1
        exact fun hu => h1 (hu.map _)
    · intro b hb
      have h1 : Ideal.Quotient.mk I b ∈ maximalIdeal (B ⧸ I) := by
        rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
        exact fun hu => (IsLocalRing.mem_maximalIdeal b |>.mp hb) (isUnit_of_map_unit _ b hu)
      rw [← hG.1] at h1
      have hset : (Ideal.Quotient.mk I) '' (U : Set B) = (G : Set (B ⧸ I)) := by
        ext g
        constructor
        · rintro ⟨u, hu, rfl⟩
          obtain ⟨g', hg', rfl⟩ := Finset.mem_image.mp hu
          rw [hUG g' hg']; exact hg'
        · intro hg
          exact ⟨_, Finset.mem_image_of_mem _ hg, hUG g hg⟩
      have h2 : Ideal.Quotient.mk I b ∈ (Ideal.span (U : Set B)).map (Ideal.Quotient.mk I) := by
        rw [Ideal.map_span, hset]; exact h1
      obtain ⟨u, hu, hub⟩ := (Ideal.mem_map_iff_of_surjective _ hmk).mp h2
      have h3 : b - u ∈ I := Ideal.Quotient.eq.mp hub.symm
      have h4 : b = (b - u) + u := by ring
      rw [h4]
      refine Ideal.add_mem _ ?_ ?_
      · exact Ideal.span_mono Finset.subset_union_left (hIspan ▸ h3)
      · exact Ideal.span_mono (by simp) hu
  refine ⟨U, hspan, ?_⟩
  have hle : ((s.image β ∪ U).card : WithBot ℕ∞) ≤ ringKrullDim B := by
    rw [hdim, ← hs.2, ← hG.2]
    have : (s.image β ∪ U).card ≤ s.card + G.card :=
      (Finset.card_union_le _ _).trans (add_le_add Finset.card_image_le Finset.card_image_le)
    exact_mod_cast this
  have hge : ringKrullDim B ≤ ((s.image β ∪ U).card : WithBot ℕ∞) := by
    refine (ringKrullDim_le_spanFinrank_maximalIdeal B).trans ?_
    rw [← hspan]
    have := Submodule.spanFinrank_span_le_ncard_of_finite (R := B) (s.image β ∪ U).finite_toSet
    rw [Set.ncard_coe_finset] at this
    exact_mod_cast this
  exact le_antisymm hle hge

open Classical in
/-- p. 212 (separable algebraic case), "the image is a regular system of parameters": if
`(M_A)B = M_B` and `dim B = dim A`, the image of a regular system of parameters of `A` is one of `B`. -/
theorem isRegularSystemOfParameters_image_of_map_maximalIdeal_eq (β : A →+* B) [IsLocalHom β]
    (s : Finset A) (hs : IsRegularSystemOfParameters A s)
    (hmax : (maximalIdeal A).map β = maximalIdeal B) (hdim : ringKrullDim B = ringKrullDim A) :
    IsRegularSystemOfParameters B (s.image β) := by
  have hspan : Ideal.span ((s.image β : Finset B) : Set B) = maximalIdeal B := by
    rw [Finset.coe_image, ← Ideal.map_span, hs.1, hmax]
  refine ⟨hspan, le_antisymm ?_ ?_⟩
  · rw [hdim, ← hs.2]
    exact_mod_cast Finset.card_image_le
  · refine (ringKrullDim_le_spanFinrank_maximalIdeal B).trans ?_
    rw [← hspan]
    have := Submodule.spanFinrank_span_le_ncard_of_finite (R := B) (s.image β).finite_toSet
    rw [Set.ncard_coe_finset] at this
    exact_mod_cast this

end RsopExtension

/-- `exists_fibre_properties` for an arbitrary canonical local homomorphism `β : R' → R̃'`: `R̃'` is
the monoidal transform `Ã'_{M̃'}` (`subring_eq_ofLift_subring`) and `β` corresponds to the canonical
lift `R' → Ã'_{M̃'}` (both are determined by their composites with `R̃' ⊆ Frac(R̄)`). -/
theorem IsCanonicalLift.exists_fibre_properties (α : R →+* Rb) [IsLocalHom α]
    (hα : RingHom.MapsRSOP α) (hP : P.IsPrime) (hS : IsRegularLocalRing (R ⧸ P))
    (t : MonoidalTransform R P) (tb : MonoidalTransform Rb (P.map α)) (β : t.ring →+* tb.ring)
    (hβ : IsCanonicalLift α t tb β) :
    ringKrullDim tb.ring = ringKrullDim t.ring +
        ringKrullDim (tb.ring ⧸ (maximalIdeal t.ring).map β) ∧
      (RingHom.IsResiduallySeparable α →
        ∀ [IsLocalRing (tb.ring ⧸ (maximalIdeal t.ring).map β)],
          IsRegularLocalRing (tb.ring ⧸ (maximalIdeal t.ring).map β)) ∧
      (RingHom.IsResiduallySeparableAlgebraic α → ((maximalIdeal t.ring).map β).IsMaximal) := by
  have hNmem := MonoidalTransform.comap_maximalIdeal_blowupToRing_mem_liftPrimes α hα t tb β hβ
  obtain ⟨h1, h2, h3⟩ := t.exists_fibre_properties α hα hP hS _ hNmem
  have hsub := MonoidalTransform.subring_eq_ofLift_subring α hα t tb β hβ
  have hβT := MonoidalTransform.isCanonicalLift_ofLiftHom α hα t _ hNmem
  have := hβT.isLocalHom
  set T := MonoidalTransform.ofLift α hα t _ hNmem with hT
  set βT := MonoidalTransform.ofLiftHom α hα t _ hNmem with hβTdef
  let e := tb.ringEquivOfSubringEq T hsub
  have hcomp : ∀ y, e (β y) = βT y := by
    intro y
    apply T.injective_toFractionRing
    rw [MonoidalTransform.toFractionRing_ringEquivOfSubringEq,
      MonoidalTransform.toFractionRing_map_eq_fractionRingMap α hα t tb β hβ y,
      MonoidalTransform.toFractionRing_map_eq_fractionRingMap α hα t T βT hβT y]
  have hIe : Ideal.map e ((maximalIdeal t.ring).map β) = (maximalIdeal t.ring).map βT := by
    show Ideal.map e.toRingHom (Ideal.map β (maximalIdeal t.ring)) = _
    rw [Ideal.map_map]
    congr 1
    exact RingHom.ext hcomp
  let eF : (tb.ring ⧸ (maximalIdeal t.ring).map β) ≃+* (T.ring ⧸ (maximalIdeal t.ring).map βT) :=
    Ideal.quotientEquiv _ _ e hIe.symm
  refine ⟨?_, ?_, ?_⟩
  · rw [ringKrullDim_eq_of_ringEquiv e, h1, ringKrullDim_eq_of_ringEquiv eF]
  · intro hsep _
    have : IsLocalRing (T.ring ⧸ (maximalIdeal t.ring).map βT) :=
      isLocalRing_quotient_of_le (Ideal.map_le_iff_le_comap.mpr fun a ha => map_nonunit βT a ha)
    have := h2 hsep
    exact IsRegularLocalRing.of_ringEquiv (R := T.ring ⧸ (maximalIdeal t.ring).map βT) eF.symm
  · intro hs
    have hmax := h3 hs
    have hc : (maximalIdeal t.ring).map β = ((maximalIdeal t.ring).map βT).comap e := by
      rw [← Ideal.map_symm, ← hIe]
      show _ = Ideal.map e.symm.toRingHom (Ideal.map e.toRingHom _)
      rw [Ideal.map_map]
      have : e.symm.toRingHom.comp e.toRingHom = RingHom.id _ := RingHom.ext fun x => by simp
      rw [this, Ideal.map_id]
    rw [hc]
    exact Ideal.comap_isMaximal_of_surjective e.toRingHom e.surjective

section LocalizationCongruence

variable {A A' : Type*} [CommRing A] [CommRing A']

/-- The step "`R_1/MR_1 → R_1'/MR_1'` is surjective" of Lemma (AB.3) (p. 296), in abstract form:
if `A' = bm(A) + J` (`J = MA'`, "`A/MA → A'/MA'` is surjective"), `J ⊆ N'` and `N = bm⁻¹N'`, then every
element of `A'_{N'}` is congruent modulo `J A'_{N'}` to the image of an element of `A_N`. -/
theorem exists_sub_mem_map_localRingHom_of_surjective (bm : A →+* A') (N' : Ideal A') [N'.IsPrime]
    (N : Ideal A) [N.IsPrime] (hN : N = N'.comap bm) (J : Ideal A') (hJ : J ≤ N')
    (hA : ∀ z : A', ∃ a : A, z - bm a ∈ J) (I₁ : Ideal (Localization.AtPrime N))
    (hI : J.map (algebraMap A' (Localization.AtPrime N')) ≤
      I₁.map (Localization.localRingHom N N' bm hN)) (y : Localization.AtPrime N') :
    ∃ c : Localization.AtPrime N, Localization.localRingHom N N' bm hN c - y ∈
      I₁.map (Localization.localRingHom N N' bm hN) := by
  set f := Localization.localRingHom N N' bm hN with hf
  obtain ⟨⟨z, s⟩, rfl⟩ := IsLocalization.mk'_surjective N'.primeCompl y
  obtain ⟨a, ha⟩ := hA z
  obtain ⟨b, hb⟩ := hA (s : A')
  have hbN : b ∉ N := by
    intro h
    have h1 : bm b ∈ N' := Ideal.mem_comap.mp (by rw [← hN]; exact h)
    exact s.2 (by have := N'.add_mem (hJ hb) h1; simpa using this)
  have hbu : IsUnit (algebraMap A (Localization.AtPrime N) b) :=
    IsLocalization.map_units (Localization.AtPrime N) (⟨b, hbN⟩ : N.primeCompl)
  obtain ⟨v, hv⟩ := hbu.exists_right_inv
  refine ⟨algebraMap A _ a * v, ?_⟩
  have hfa : ∀ x, f (algebraMap A (Localization.AtPrime N) x) =
      algebraMap A' (Localization.AtPrime N') (bm x) := fun x =>
    Localization.localRingHom_to_map N N' bm hN x
  have hunit : IsUnit (algebraMap A' (Localization.AtPrime N') (bm b)) := by
    rw [← hfa]
    exact hbu.map f
  -- `y s = z`
  have hys : IsLocalization.mk' (Localization.AtPrime N') z s *
      algebraMap A' (Localization.AtPrime N') (s : A') = algebraMap A' (Localization.AtPrime N') z :=
    IsLocalization.mk'_spec _ _ _
  set y := IsLocalization.mk' (Localization.AtPrime N') z s
  have hJs : algebraMap A' (Localization.AtPrime N') (s : A') -
      algebraMap A' (Localization.AtPrime N') (bm b) ∈
      I₁.map f := hI (by
        rw [← map_sub]; exact Ideal.mem_map_of_mem _ hb)
  have hJz : algebraMap A' (Localization.AtPrime N') z -
      algebraMap A' (Localization.AtPrime N') (bm a) ∈ I₁.map f := hI (by
        rw [← map_sub]; exact Ideal.mem_map_of_mem _ ha)
  -- `y * alg(bm b) - alg(bm a) ∈ I`
  have h1 : y * algebraMap A' (Localization.AtPrime N') (bm b) -
      algebraMap A' (Localization.AtPrime N') (bm a) ∈ I₁.map f := by
    have : y * algebraMap A' (Localization.AtPrime N') (bm b) -
        algebraMap A' (Localization.AtPrime N') (bm a) =
        (algebraMap A' (Localization.AtPrime N') z - algebraMap A' (Localization.AtPrime N') (bm a)) -
        y * (algebraMap A' (Localization.AtPrime N') (s : A') -
          algebraMap A' (Localization.AtPrime N') (bm b)) := by
      rw [← hys]; ring
    rw [this]
    exact Ideal.sub_mem _ hJz (Ideal.mul_mem_left _ _ hJs)
  -- multiply by `f v`
  have hfv : f v * algebraMap A' (Localization.AtPrime N') (bm b) = 1 := by
    have := congrArg f hv
    rw [map_mul, hfa, map_one] at this
    rw [mul_comm]; exact this
  have h2 := Ideal.mul_mem_left _ (f v) h1
  have h3 : f (algebraMap A (Localization.AtPrime N) a * v) - y =
      -(f v * (y * algebraMap A' (Localization.AtPrime N') (bm b) -
        algebraMap A' (Localization.AtPrime N') (bm a))) := by
    rw [map_mul, hfa, mul_sub, ← mul_assoc, mul_comm (f v) y, mul_assoc, hfv]
    ring
  rw [h3]
  exact neg_mem h2

end LocalizationCongruence

section SurjectiveOnA

variable {R Rb : Type u} [CommRing R] [IsRegularLocalRing R] [IsDomain R]
  [CommRing Rb] [IsRegularLocalRing Rb] [IsDomain Rb] {P : Ideal R}

/-- p. 296: "Since `R/M → R'/MR'` is surjective, so is `A/MA → A'/MA'`" (`A = R[y₂/y₁,…]`,
`A' = R'[y₂/y₁,…]`, the latter generated over `R'` by the same quotients): every element of `A'` is
congruent modulo `MA'` to the image of an element of `A`. -/
theorem MonoidalTransform.exists_sub_mem_map_blowupMap (α : R →+* Rb) [IsLocalHom α]
    (hα : RingHom.MapsRSOP α) (t : MonoidalTransform R P) (M : Ideal R)
    (hsurj : ∀ y : Rb, ∃ r : R, α r - y ∈ M.map α)
    (z : blowupAlgebra Rb (P.map α) (α t.x)) :
    ∃ a : blowupAlgebra R P t.x,
      z - blowupMap α (RingHom.MapsRSOP.injective α hα) P t.x a ∈
        (M.map α).map (algebraMap Rb (blowupAlgebra Rb (P.map α) (α t.x))) := by
  have hαinj := RingHom.MapsRSOP.injective α hα
  set bm := blowupMap α hαinj P t.x with hbm
  set J := (M.map α).map (algebraMap Rb (blowupAlgebra Rb (P.map α) (α t.x))) with hJ
  set Q : blowupAlgebra Rb (P.map α) (α t.x) → Prop := fun z => ∃ a, z - bm a ∈ J with hQ
  have Qadd : ∀ z z', Q z → Q z' → Q (z + z') := by
    rintro z z' ⟨a, ha⟩ ⟨a', ha'⟩
    refine ⟨a + a', ?_⟩
    have := J.add_mem ha ha'
    rwa [map_add, show z + z' - (bm a + bm a') = z - bm a + (z' - bm a') by ring]
  have Qmul : ∀ z z', Q z → Q z' → Q (z * z') := by
    rintro z z' ⟨a, ha⟩ ⟨a', ha'⟩
    refine ⟨a * a', ?_⟩
    have := J.add_mem (J.mul_mem_left z ha') (J.mul_mem_left (bm a') ha)
    rwa [map_mul, show z * z' - bm a * bm a' = z * (z' - bm a') + bm a' * (z - bm a) by ring]
  have Qalg : ∀ r' : Rb, Q (algebraMap Rb _ r') := by
    intro r'
    obtain ⟨r, hr⟩ := hsurj r'
    refine ⟨algebraMap R _ r, ?_⟩
    rw [blowupMap_algebraMap]
    have : algebraMap Rb (blowupAlgebra Rb (P.map α) (α t.x)) (α r - r') ∈ J :=
      Ideal.mem_map_of_mem _ hr
    rw [map_sub] at this
    have := neg_mem this
    rwa [neg_sub] at this
  -- generators `p / α(x)`, `p ∈ PR'`
  have hgen : ∀ p ∈ P.map α, ∃ w : blowupAlgebra Rb (P.map α) (α t.x),
      (w : FractionRing Rb) = algebraMap Rb (FractionRing Rb) p /
        algebraMap Rb (FractionRing Rb) (α t.x) ∧ Q w := by
    intro p hp
    have hp' : p ∈ Submodule.span Rb (α '' (P : Set R)) := hp
    refine Submodule.span_induction (p := fun p _ => ∃ w : blowupAlgebra Rb (P.map α) (α t.x),
      (w : FractionRing Rb) = algebraMap Rb (FractionRing Rb) p /
        algebraMap Rb (FractionRing Rb) (α t.x) ∧ Q w) ?_ ?_ ?_ ?_ hp'
    · rintro _ ⟨q, hq, rfl⟩
      have hqa : algebraMap R (FractionRing R) q / algebraMap R (FractionRing R) t.x ∈
          blowupAlgebra R P t.x := Algebra.subset_adjoin ⟨q, hq, rfl⟩
      refine ⟨bm ⟨_, hqa⟩, ?_, ⟨⟨_, hqa⟩, ?_⟩⟩
      · rw [hbm, blowupMap_coe]
        simp only [map_div₀, fractionRingMap_algebraMap]
      · rw [sub_self]; exact J.zero_mem
    · exact ⟨0, by simp, ⟨0, by simp [J.zero_mem]⟩⟩
    · rintro p p' - - ⟨w, hw, hQw⟩ ⟨w', hw', hQw'⟩
      refine ⟨w + w', ?_, Qadd _ _ hQw hQw'⟩
      rw [Subalgebra.coe_add, hw, hw', map_add, add_div]
    · rintro r' p - ⟨w, hw, hQw⟩
      refine ⟨algebraMap Rb _ r' * w, ?_, Qmul _ _ (Qalg r') hQw⟩
      rw [Subalgebra.coe_mul, hw, smul_eq_mul, map_mul]
      simp only [Subalgebra.coe_algebraMap]
      ring
  have : ∀ z : blowupAlgebra Rb (P.map α) (α t.x), Q z := by
    rintro ⟨z0, hz0⟩
    induction hz0 using Algebra.adjoin_induction with
    | mem y hy =>
      obtain ⟨p, hp, rfl⟩ := hy
      obtain ⟨w, hw, hQw⟩ := hgen p hp
      have : (⟨_, Algebra.subset_adjoin ⟨p, hp, rfl⟩⟩ : blowupAlgebra Rb (P.map α) (α t.x)) = w :=
        Subtype.ext hw.symm
      simpa [this] using hQw
    | algebraMap r' => exact Qalg r'
    | add y y' hy hy' ihy ihy' => exact Qadd _ _ ihy ihy'
    | mul y y' hy hy' ihy ihy' => exact Qmul _ _ ihy ihy'
  exact this z

end SurjectiveOnA

end Fibre2

section AssociatedPrimesLift

variable {R Rb : Type u} [CommRing R] [IsRegularLocalRing R] [IsDomain R]
  [CommRing Rb] [IsRegularLocalRing Rb] [IsDomain Rb] {P : Ideal R}

/-- `ker π̃ ⊆ M'Ã'` for the chart `π̃ : Ã' → k̃[X₂,…,X_r]` of p. 211, and `π̃(M'Ã') = m̄' k̃[X]`. -/
theorem MonoidalTransform.map_map_blowupMap_eq (α : R →+* Rb) [IsLocalHom α] (hα : RingHom.MapsRSOP α)
    (t : MonoidalTransform R P) {r : ℕ}
    (π : blowupAlgebra R P t.x →+* MvPolynomial (Fin r) (ResidueField R))
    (π' : blowupAlgebra Rb (P.map α) (α t.x) →+* MvPolynomial (Fin r) (ResidueField Rb))
    (hcomm : π'.comp (blowupMap α (RingHom.MapsRSOP.injective α hα) P t.x) =
      (MvPolynomial.map (ResidueField.map α)).comp π) :
    (t.M'.map (blowupMap α (RingHom.MapsRSOP.injective α hα) P t.x)).map π' =
      (t.M'.map π).map (MvPolynomial.map (ResidueField.map α)) := by
  rw [Ideal.map_map, Ideal.map_map, hcomm]

/-- p. 211, "if `M̃'` is an associated prime ideal of `M'Ã'`, then we have a canonical local
homomorphism of `R' = A'_{M'}` into `R̃' = Ã'_{M̃'}`": an associated prime `M̃'` of `M'Ã'` is a prime of
`Ã'` over `M'` (no algebraicity needed).  Here `Ã' = R̄[α(x)⁻¹P̄]` and `M'Ã'` is the extension of `M'`
along `A' → Ã'`.  By the correspondence of the associated primes along `Ã' → k̃[X₂,…,X_r]`
(`mem_associatedPrimes_quotient_iff_map`), the image of `M̃'` is an associated prime of
`m̄'k̃[X]`, hence lies over `m̄'` (`comap_eq_of_mem_associatedPrimes`). -/
theorem MonoidalTransform.mem_liftPrimes_of_mem_associatedPrimes (α : R →+* Rb) [IsLocalHom α]
    (hα : RingHom.MapsRSOP α) (hP : P.IsPrime) (hS : IsRegularLocalRing (R ⧸ P))
    (t : MonoidalTransform R P) (N : Ideal (blowupAlgebra Rb (P.map α) (α t.x)))
    (hN : N ∈ associatedPrimes (blowupAlgebra Rb (P.map α) (α t.x))
      (blowupAlgebra Rb (P.map α) (α t.x) ⧸
        t.M'.map (blowupMap α (RingHom.MapsRSOP.injective α hα) P t.x))) :
    N ∈ LiftPrimes α (RingHom.MapsRSOP.injective α hα) t := by
  classical
  have := isNoetherianRing_blowupAlgebra (R := Rb) (P := P.map α) (α t.x)
  obtain ⟨r, π, π', hπ, hkπ, hπ', hkπ', hcomm, hπC, hπ'C⟩ :=
    t.exists_residue_charts α hα hP hS
  have hkπM' : RingHom.ker π ≤ t.M' := hkπ.trans t.le
  have hm : (t.M'.map π).IsPrime := Ideal.map_isPrime_of_surjective hπ hkπM'
  have hkJ : RingHom.ker π' ≤ t.M'.map (blowupMap α (RingHom.MapsRSOP.injective α hα) P t.x) :=
    hkπ'.trans (t.map_maximalIdeal_le_map_blowupMap α hα)
  obtain ⟨hkN, hNq⟩ := (mem_associatedPrimes_quotient_iff_map π' hπ' hkJ N).mp hN
  rw [t.map_map_blowupMap_eq α hα π π' hcomm] at hNq
  have hq := comap_eq_of_mem_associatedPrimes (ResidueField.map α) (t.M'.map π) hNq
  exact ⟨hN.1, (comap_eq_iff_comap_map_eq _ π π' _ hπ hπ' hcomm hkπM' hkN).mpr hq⟩

/-- p. 211, "the associated prime ideals of `M'Ã'` correspond to the associated prime ideals of
`m̄'k̃[X₂,…,X_r]`" and "all [of them] are isolated": if `k̃` or `R'/M'R'` is algebraic over `k`,
the primes `M̃'` of `Ã'` over `M'` are associated primes of `M'Ã'` (they are minimal over `m̄'k̃[X]`
after `Ã' → k̃[X₂,…,X_r]`, `map_mem_minimalPrimes_of_mem_liftPrimes`, and the minimal primes of an
ideal of a noetherian ring are associated). -/
theorem MonoidalTransform.mem_associatedPrimes_of_mem_liftPrimes (α : R →+* Rb) [IsLocalHom α]
    (hα : RingHom.MapsRSOP α) (hP : P.IsPrime) (hS : IsRegularLocalRing (R ⧸ P))
    (t : MonoidalTransform R P)
    (halg : RingHom.IsResiduallyAlgebraic α ∨
      RingHom.IsResiduallyAlgebraic (R := R) (R' := t.ring) t.toRing)
    (N : Ideal (blowupAlgebra Rb (P.map α) (α t.x)))
    (hN : N ∈ LiftPrimes α (RingHom.MapsRSOP.injective α hα) t) :
    N ∈ associatedPrimes (blowupAlgebra Rb (P.map α) (α t.x))
      (blowupAlgebra Rb (P.map α) (α t.x) ⧸
        t.M'.map (blowupMap α (RingHom.MapsRSOP.injective α hα) P t.x)) := by
  classical
  have := isNoetherianRing_blowupAlgebra (R := Rb) (P := P.map α) (α t.x)
  obtain ⟨r, π, π', hπ, hkπ, hπ', hkπ', hcomm, hπC, hπ'C⟩ :=
    t.exists_residue_charts α hα hP hS
  have hkπM' : RingHom.ker π ≤ t.M' := hkπ.trans t.le
  have hkJ : RingHom.ker π' ≤ t.M'.map (blowupMap α (RingHom.MapsRSOP.injective α hα) P t.x) :=
    hkπ'.trans (t.map_maximalIdeal_le_map_blowupMap α hα)
  have hkN : RingHom.ker π' ≤ N := hkπ'.trans (MonoidalTransform.ofLift α hα t N hN).le
  refine (mem_associatedPrimes_quotient_iff_map π' hπ' hkJ N).mpr ⟨hkN, ?_⟩
  rw [t.map_map_blowupMap_eq α hα π π' hcomm]
  exact minimalPrimes_subset_associatedPrimes_quotient _
    (t.map_mem_minimalPrimes_of_mem_liftPrimes α hα halg π π' hπ hkπ hπ' hkπ' hcomm hπC N hN).2.2

/-- Lemma 4, p. 211: for `Ã' = R̄[α(x)⁻¹P̄]`, `M'Ã'` the extension of the prime `M'` of
`A' = R[x⁻¹P]`: the associated primes of `M'Ã'` are exactly the primes of `Ã'` lying over `M'`, if
`R̄` or `R'` is residually algebraic over `R`.  (The inclusion "associated ⇒ over `M'`" holds without
the hypothesis.)  Used for "`N'` is an associated prime ideal of `NA'`" in Lemma (AB.3), p. 296. -/
@[blueprint "lem:III.4-associated-primes"
  (statement := /-- Notation as in \cref{lem:III.4}: $A'=R[x_2/x_1,\dots,x_r/x_1]$,
    $\bar A'=\bar R[\alpha(x_2)/\alpha(x_1),\dots,\alpha(x_r)/\alpha(x_1)]$, $M'$ a prime of $A'$
    containing $MA'$ ($R'=A'_{M'}$). If either $\bar R$ or $R'$ is residually algebraic over $R$,
    the associated prime ideals of $M'\bar A'$ are exactly the prime ideals $\bar M'$ of $\bar A'$
    with $\bar M'\cap A'=M'$ (that is, lying over $M'$). Without the hypothesis, every associated
    prime of $M'\bar A'$ lies over $M'$; so it gives a monoidal transform
    $\bar R'=\bar A'_{\bar M'}$ with a canonical local homomorphism $R'\to\bar R'$.
    (p.~211: ``if $\tilde M'$ is an associated prime ideal of $M'\tilde A'$, then we have a
    canonical local homomorphism of $R'$ into $\tilde R'$''.) -/)
  (proof := /-- The natural homomorphism $\bar A'\to\bar k[X_2,\dots,X_r]$ is onto, with kernel in
    $M'\bar A'$ and $M'\bar A'\mapsto\bar m'\bar k[X]$, so the associated primes of $M'\bar A'$ are
    the inverse images of those of $\bar m'\bar k[X]$. An associated prime of $\bar m'\bar k[X]$
    lies over $\bar m'$: an element of $k[X]\setminus\bar m'$ is a non-zero-divisor modulo
    $\bar m'\bar k[X]$ ($k[X]/\bar m'$ is a domain and $\bar k[X]$ is free over $k[X]$), hence lies in
    no associated prime. Conversely, if $\bar k$ or $R'/M'R'$ is algebraic over $k$, a prime over
    $\bar m'$ is minimal over $\bar m'\bar k[X]$ (incomparability for the integral extension
    $k[X]/\bar m'\to\bar k[X]/\bar m'\bar k[X]$, resp.\ maximality of every prime over $\bar m'$),
    and the minimal primes of an ideal of a noetherian ring are associated primes. (p.~211.) -/)
  (latexEnv := "lemma")]
theorem MonoidalTransform.mem_associatedPrimes_iff_mem_liftPrimes (α : R →+* Rb) [IsLocalHom α]
    (hα : RingHom.MapsRSOP α) (hP : P.IsPrime) (hS : IsRegularLocalRing (R ⧸ P))
    (t : MonoidalTransform R P)
    (halg : RingHom.IsResiduallyAlgebraic α ∨
      RingHom.IsResiduallyAlgebraic (R := R) (R' := t.ring) t.toRing)
    (N : Ideal (blowupAlgebra Rb (P.map α) (α t.x))) :
    N ∈ associatedPrimes (blowupAlgebra Rb (P.map α) (α t.x))
        (blowupAlgebra Rb (P.map α) (α t.x) ⧸
          t.M'.map (blowupMap α (RingHom.MapsRSOP.injective α hα) P t.x)) ↔
      N ∈ LiftPrimes α (RingHom.MapsRSOP.injective α hα) t :=
  ⟨t.mem_liftPrimes_of_mem_associatedPrimes α hα hP hS N,
    t.mem_associatedPrimes_of_mem_liftPrimes α hα hP hS halg N⟩

/-- p. 211, "Then `q̃` is a prime ideal in `k̃[X̄₂,…,X_r]` with `q̃ ∩ k[X̄₂,…,X_r] = (0)`. In this
manner, the set of those prime ideals `q̃` with this property is in a one to one correspondence with
the set of those `R̃'` which admit a canonical local homomorphism `R' → R̃'`", on the level of
`k̃[X₂,…,X_r]` (the primes of `k̃[X̄] = k̃[X]/m̄'k̃[X]` correspond to the primes of `k̃[X]` containing
`m̄'k̃[X]`, and `q̃ ∩ k[X̄] = (0)` means that the corresponding prime of `k̃[X]` lies over `m̄'`):
`M̃' ↦ M̃'k̃[X]` is a bijection from the primes `M̃'` of `Ã'` over `M'` onto the primes of `k̃[X]` over
`m̄'` (no algebraicity needed).  The surjectivity is the part not argued in the paper. -/
theorem MonoidalTransform.bijOn_map_liftPrimes (α : R →+* Rb) [IsLocalHom α]
    (hα : RingHom.MapsRSOP α) (t : MonoidalTransform R P) {r : ℕ}
    (π : blowupAlgebra R P t.x →+* MvPolynomial (Fin r) (ResidueField R))
    (π' : blowupAlgebra Rb (P.map α) (α t.x) →+* MvPolynomial (Fin r) (ResidueField Rb))
    (hπ : Function.Surjective π)
    (hkπ : RingHom.ker π ≤ (maximalIdeal R).map (algebraMap R (blowupAlgebra R P t.x)))
    (hπ' : Function.Surjective π')
    (hkπ' : RingHom.ker π' ≤ (maximalIdeal Rb).map
      (algebraMap Rb (blowupAlgebra Rb (P.map α) (α t.x))))
    (hcomm : π'.comp (blowupMap α (RingHom.MapsRSOP.injective α hα) P t.x) =
      (MvPolynomial.map (ResidueField.map α)).comp π) :
    Set.BijOn (fun N : Ideal (blowupAlgebra Rb (P.map α) (α t.x)) => N.map π')
      (LiftPrimes α (RingHom.MapsRSOP.injective α hα) t)
      {q : Ideal (MvPolynomial (Fin r) (ResidueField Rb)) | q.IsPrime ∧
        q.comap (MvPolynomial.map (ResidueField.map α)) = t.M'.map π} := by
  classical
  have hkπM' : RingHom.ker π ≤ t.M' := hkπ.trans t.le
  have e : ∀ N : Ideal (blowupAlgebra Rb (P.map α) (α t.x)), RingHom.ker π' ≤ N →
      N = (N.map π').comap π' := fun N hN => by
    rw [Ideal.comap_map_of_surjective _ hπ', ← RingHom.ker_eq_comap_bot, sup_eq_left.mpr hN]
  refine ⟨fun N hN => ?_, fun N₁ h₁ N₂ h₂ h => ?_, fun q hq => ?_⟩
  · have hkN : RingHom.ker π' ≤ N := hkπ'.trans (MonoidalTransform.ofLift α hα t N hN).le
    have := hN.1
    exact ⟨Ideal.map_isPrime_of_surjective hπ' hkN,
      (comap_eq_iff_comap_map_eq _ π π' _ hπ hπ' hcomm hkπM' hkN).mp hN.2⟩
  · have hk₁ : RingHom.ker π' ≤ N₁ := hkπ'.trans (MonoidalTransform.ofLift α hα t N₁ h₁).le
    have hk₂ : RingHom.ker π' ≤ N₂ := hkπ'.trans (MonoidalTransform.ofLift α hα t N₂ h₂).le
    rw [e N₁ hk₁, e N₂ hk₂]
    exact congrArg (Ideal.comap π') h
  · obtain ⟨hqp, hqm⟩ := hq
    have hNp : (q.comap π').IsPrime := Ideal.comap_isPrime π' q
    have hkN : RingHom.ker π' ≤ q.comap π' := by
      intro a ha
      rw [Ideal.mem_comap, RingHom.mem_ker.mp ha]
      exact zero_mem _
    have hNq : (q.comap π').map π' = q := Ideal.map_comap_of_surjective π' hπ' q
    refine ⟨q.comap π', ⟨hNp, ?_⟩, hNq⟩
    refine (comap_eq_iff_comap_map_eq _ π π' _ hπ hπ' hcomm hkπM' hkN).mpr ?_
    rw [hNq]
    exact hqm

/-- p. 211, the last correspondence, for the monoidal transforms `R̃'` themselves: the `R̃'` admitting a
canonical local homomorphism `R' → R̃'` are in one to one correspondence with the primes `q̃` of
`k̃[X₂,…,X_r]` over `m̄'` (`bijOn_map_liftPrimes`, `canonicalTransforms_eq_image_liftSubring`,
`injOn_liftSubring`). -/
@[blueprint "lem:III.4-q-correspondence"
  (statement := /-- Notation as in \cref{lem:III.4}. The set of the prime ideals $\bar{\mathfrak q}$ of
    $\bar k[X_2,\dots,X_r]$ lying over $\bar m'$ (those of
    $\bar k[\bar X_2,\dots,\bar X_r]=\bar k[X]/\bar m'\bar k[X]$ with
    $\bar{\mathfrak q}\cap k[\bar X_2,\dots,\bar X_r]=(0)$) is in a one to one correspondence with
    the set of those $\bar R'$ which admit a canonical local homomorphism $R'\to\bar R'$,
    $\bar R'=\bar A'_{\bar M'}\mapsto\bar{\mathfrak q}=$ the image of $\bar M'$. (p.~211; no
    hypothesis on the residue fields.) -/)
  (proof := /-- The primes $\bar M'$ of $\bar A'$ over $M'$ contain the kernel of
    $\bar A'\to\bar k[X]$ and correspond to the primes of $\bar k[X]$ over $\bar m'$ (the
    contraction condition is preserved on both sides); the map is injective, and onto because the
    inverse image of a prime over $\bar m'$ is a prime of $\bar A'$ over $M'$. The $\bar R'$
    correspond one to one to the $\bar M'$ (\cref{lem:III.4}). (p.~211.) -/)
  (latexEnv := "lemma")]
theorem MonoidalTransform.nonempty_canonicalTransforms_equiv_primes (α : R →+* Rb) [IsLocalHom α]
    (hα : RingHom.MapsRSOP α) (t : MonoidalTransform R P) {r : ℕ}
    (π : blowupAlgebra R P t.x →+* MvPolynomial (Fin r) (ResidueField R))
    (π' : blowupAlgebra Rb (P.map α) (α t.x) →+* MvPolynomial (Fin r) (ResidueField Rb))
    (hπ : Function.Surjective π)
    (hkπ : RingHom.ker π ≤ (maximalIdeal R).map (algebraMap R (blowupAlgebra R P t.x)))
    (hπ' : Function.Surjective π')
    (hkπ' : RingHom.ker π' ≤ (maximalIdeal Rb).map
      (algebraMap Rb (blowupAlgebra Rb (P.map α) (α t.x))))
    (hcomm : π'.comp (blowupMap α (RingHom.MapsRSOP.injective α hα) P t.x) =
      (MvPolynomial.map (ResidueField.map α)).comp π) :
    Nonempty (↥(canonicalTransforms α (Pb := P.map α) t) ≃
      {q : Ideal (MvPolynomial (Fin r) (ResidueField Rb)) // q.IsPrime ∧
        q.comap (MvPolynomial.map (ResidueField.map α)) = t.M'.map π}) := by
  have h1 : Set.BijOn (liftSubring α hα t) (LiftPrimes α (RingHom.MapsRSOP.injective α hα) t)
      (canonicalTransforms α (Pb := P.map α) t) := by
    rw [canonicalTransforms_eq_image_liftSubring α hα t]
    exact (injOn_liftSubring α hα t).bijOn_image
  have h2 := t.bijOn_map_liftPrimes α hα π π' hπ hkπ hπ' hkπ' hcomm
  exact ⟨(h1.equiv _).symm.trans (h2.equiv _)⟩

/-- p. 211, "the associated prime ideals of `M'Ã'` correspond to the associated prime ideals of
`m̄'k̃[X₂,…,X_r]` in a one to one fashion by the natural homomorphism of `Ã'` onto `k̃[X₂,…,X_r]`":
`M̃' ↦ M̃'k̃[X]` is a bijection from the associated primes of `M'Ã'` onto the associated primes of
`m̄'k̃[X]`. -/
theorem MonoidalTransform.bijOn_map_associatedPrimes (α : R →+* Rb) [IsLocalHom α]
    (hα : RingHom.MapsRSOP α) (t : MonoidalTransform R P) {r : ℕ}
    (π : blowupAlgebra R P t.x →+* MvPolynomial (Fin r) (ResidueField R))
    (π' : blowupAlgebra Rb (P.map α) (α t.x) →+* MvPolynomial (Fin r) (ResidueField Rb))
    (hkπ' : RingHom.ker π' ≤ (maximalIdeal Rb).map
      (algebraMap Rb (blowupAlgebra Rb (P.map α) (α t.x))))
    (hπ' : Function.Surjective π')
    (hcomm : π'.comp (blowupMap α (RingHom.MapsRSOP.injective α hα) P t.x) =
      (MvPolynomial.map (ResidueField.map α)).comp π) :
    Set.BijOn (fun N : Ideal (blowupAlgebra Rb (P.map α) (α t.x)) => N.map π')
      (associatedPrimes (blowupAlgebra Rb (P.map α) (α t.x))
        (blowupAlgebra Rb (P.map α) (α t.x) ⧸
          t.M'.map (blowupMap α (RingHom.MapsRSOP.injective α hα) P t.x)))
      (associatedPrimes (MvPolynomial (Fin r) (ResidueField Rb))
        (MvPolynomial (Fin r) (ResidueField Rb) ⧸
          (t.M'.map π).map (MvPolynomial.map (ResidueField.map α)))) := by
  classical
  have := isNoetherianRing_blowupAlgebra (R := Rb) (P := P.map α) (α t.x)
  have hkJ : RingHom.ker π' ≤ t.M'.map (blowupMap α (RingHom.MapsRSOP.injective α hα) P t.x) :=
    hkπ'.trans (t.map_maximalIdeal_le_map_blowupMap α hα)
  have hcm := t.map_map_blowupMap_eq α hα π π' hcomm
  refine ⟨fun N hN => ?_, fun N₁ h₁ N₂ h₂ h => ?_, fun q hq => ?_⟩
  · have := (mem_associatedPrimes_quotient_iff_map π' hπ' hkJ N).mp hN
    rw [hcm] at this
    exact this.2
  · have hk₁ := ((mem_associatedPrimes_quotient_iff_map π' hπ' hkJ N₁).mp h₁).1
    have hk₂ := ((mem_associatedPrimes_quotient_iff_map π' hπ' hkJ N₂).mp h₂).1
    have e : ∀ N : Ideal (blowupAlgebra Rb (P.map α) (α t.x)), RingHom.ker π' ≤ N →
        N = (N.map π').comap π' := fun N hN => by
      rw [Ideal.comap_map_of_surjective _ hπ', ← RingHom.ker_eq_comap_bot, sup_eq_left.mpr hN]
    rw [e N₁ hk₁, e N₂ hk₂]
    exact congrArg (Ideal.comap π') h
  · have hkN : RingHom.ker π' ≤ q.comap π' := by
      intro a ha
      rw [Ideal.mem_comap, RingHom.mem_ker.mp ha]
      exact zero_mem _
    have hNq : (q.comap π').map π' = q := Ideal.map_comap_of_surjective π' hπ' q
    refine ⟨q.comap π', ?_, hNq⟩
    rw [mem_associatedPrimes_quotient_iff_map π' hπ' hkJ, hNq, hcm]
    exact ⟨hkN, hq⟩

/-- p. 211: "Therefore, if either `R̃` or `R'` is residually algebraic over `R`, then the number of `R̃'`
which admit a canonical local homomorphism `R' → R̃'` is equal to the number of the associated prime
ideals of `m̄'k̃[X₂,…,X_r]`, which is obviously finite."  The `R̃'` correspond one to one to the primes
of `Ã'` over `M'` (`canonicalTransforms_eq_image_liftSubring`, `injOn_liftSubring`), which are the
associated primes of `M'Ã'` (`mem_associatedPrimes_iff_mem_liftPrimes`), which correspond one to one
to the associated primes of `m̄'k̃[X]` (`bijOn_map_associatedPrimes`). -/
@[blueprint "lem:III.4-count"
  (statement := /-- Notation as in \cref{lem:III.4}. If either $\bar R$ or $R'$ is residually algebraic
    over $R$, the number of the monoidal transforms $\bar R'$ of $\bar R$ with center $\bar P$ which
    admit a canonical local homomorphism $R'\to\bar R'$ is equal to the number of the associated
    prime ideals of $M'\bar A'$, and to the number of the associated prime ideals of
    $\bar m'\bar k[X_2,\dots,X_r]$, which is finite. (p.~211.) -/)
  (proof := /-- The $\bar R'$ correspond one to one to the primes $\bar M'$ of $\bar A'$ over $M'$
    (\cref{lem:III.4}), which are the associated primes of $M'\bar A'$
    (\cref{lem:III.4-associated-primes}); these correspond one to one to the associated primes of
    $\bar m'\bar k[X]$ by the natural homomorphism $\bar A'\to\bar k[X]$. A noetherian module has
    finitely many associated primes. -/)
  (proofUses := ["lem:III.4-associated-primes"])
  (latexEnv := "lemma")]
theorem MonoidalTransform.mk_canonicalTransforms_eq_mk_associatedPrimes (α : R →+* Rb)
    [IsLocalHom α] (hα : RingHom.MapsRSOP α) (hP : P.IsPrime) (hS : IsRegularLocalRing (R ⧸ P))
    (t : MonoidalTransform R P)
    (halg : RingHom.IsResiduallyAlgebraic α ∨
      RingHom.IsResiduallyAlgebraic (R := R) (R' := t.ring) t.toRing)
    {r : ℕ}
    (π : blowupAlgebra R P t.x →+* MvPolynomial (Fin r) (ResidueField R))
    (π' : blowupAlgebra Rb (P.map α) (α t.x) →+* MvPolynomial (Fin r) (ResidueField Rb))
    (hkπ' : RingHom.ker π' ≤ (maximalIdeal Rb).map
      (algebraMap Rb (blowupAlgebra Rb (P.map α) (α t.x))))
    (hπ' : Function.Surjective π')
    (hcomm : π'.comp (blowupMap α (RingHom.MapsRSOP.injective α hα) P t.x) =
      (MvPolynomial.map (ResidueField.map α)).comp π) :
    Cardinal.mk ↥(canonicalTransforms α (Pb := P.map α) t) =
      Cardinal.mk ↥(associatedPrimes (blowupAlgebra Rb (P.map α) (α t.x))
        (blowupAlgebra Rb (P.map α) (α t.x) ⧸
          t.M'.map (blowupMap α (RingHom.MapsRSOP.injective α hα) P t.x))) ∧
    Cardinal.mk ↥(canonicalTransforms α (Pb := P.map α) t) =
      Cardinal.mk ↥(associatedPrimes (MvPolynomial (Fin r) (ResidueField Rb))
        (MvPolynomial (Fin r) (ResidueField Rb) ⧸
          (t.M'.map π).map (MvPolynomial.map (ResidueField.map α)))) := by
  classical
  have hset : associatedPrimes (blowupAlgebra Rb (P.map α) (α t.x))
      (blowupAlgebra Rb (P.map α) (α t.x) ⧸
        t.M'.map (blowupMap α (RingHom.MapsRSOP.injective α hα) P t.x)) =
      LiftPrimes α (RingHom.MapsRSOP.injective α hα) t :=
    Set.ext fun N => t.mem_associatedPrimes_iff_mem_liftPrimes α hα hP hS halg N
  have h1 : Set.BijOn (liftSubring α hα t) (LiftPrimes α (RingHom.MapsRSOP.injective α hα) t)
      (canonicalTransforms α (Pb := P.map α) t) := by
    rw [canonicalTransforms_eq_image_liftSubring α hα t]
    exact (injOn_liftSubring α hα t).bijOn_image
  have h2 := t.bijOn_map_associatedPrimes α hα π π' hkπ' hπ' hcomm
  rw [hset] at h2
  have e1 := Cardinal.mk_congr (h1.equiv _)
  have e2 := Cardinal.mk_congr (h2.equiv _)
  refine ⟨?_, ?_⟩
  · rw [← e1, hset]
  · rw [← e1, e2]

/-- p. 211, "all the associated prime ideals of `m̄'k̃[X₂,…,X_r]` are isolated": if `R̄` or `R'` is
residually algebraic over `R` (the cases in which the paper counts the `R̃'`), every associated prime
of `m̄'k̃[X]` is a minimal prime of `m̄'k̃[X]`.  An associated prime of `m̄'k̃[X]` is the image of an
associated prime of `M'Ã'` (`bijOn_map_associatedPrimes`), which lies over `M'`
(`mem_liftPrimes_of_mem_associatedPrimes`), and the primes over `M'` are minimal
(`map_mem_minimalPrimes_of_mem_liftPrimes`). -/
theorem MonoidalTransform.mem_minimalPrimes_of_mem_associatedPrimes_map (α : R →+* Rb)
    [IsLocalHom α] (hα : RingHom.MapsRSOP α) (hP : P.IsPrime) (hS : IsRegularLocalRing (R ⧸ P))
    (t : MonoidalTransform R P)
    (halg : RingHom.IsResiduallyAlgebraic α ∨
      RingHom.IsResiduallyAlgebraic (R := R) (R' := t.ring) t.toRing)
    {r : ℕ} (π : blowupAlgebra R P t.x →+* MvPolynomial (Fin r) (ResidueField R))
    (π' : blowupAlgebra Rb (P.map α) (α t.x) →+* MvPolynomial (Fin r) (ResidueField Rb))
    (hπ : Function.Surjective π)
    (hkπ : RingHom.ker π ≤ (maximalIdeal R).map (algebraMap R (blowupAlgebra R P t.x)))
    (hπ' : Function.Surjective π')
    (hkπ' : RingHom.ker π' ≤ (maximalIdeal Rb).map
      (algebraMap Rb (blowupAlgebra Rb (P.map α) (α t.x))))
    (hcomm : π'.comp (blowupMap α (RingHom.MapsRSOP.injective α hα) P t.x) =
      (MvPolynomial.map (ResidueField.map α)).comp π)
    (hπC : ∀ c : R, π (algebraMap R (blowupAlgebra R P t.x) c) = C (residue R c))
    {q : Ideal (MvPolynomial (Fin r) (ResidueField Rb))}
    (hq : q ∈ associatedPrimes (MvPolynomial (Fin r) (ResidueField Rb))
      (MvPolynomial (Fin r) (ResidueField Rb) ⧸
        (t.M'.map π).map (MvPolynomial.map (ResidueField.map α)))) :
    q ∈ ((t.M'.map π).map (MvPolynomial.map (ResidueField.map α))).minimalPrimes := by
  obtain ⟨N, hN, rfl⟩ := (t.bijOn_map_associatedPrimes α hα π π' hkπ' hπ' hcomm).surjOn hq
  have hN' := t.mem_liftPrimes_of_mem_associatedPrimes α hα hP hS N hN
  exact (t.map_mem_minimalPrimes_of_mem_liftPrimes α hα halg π π' hπ hkπ hπ' hkπ' hcomm hπC N
    hN').2.2

/-- p. 211, "which is obviously finite": the set of primes `M̃'` of `Ã'` over `M'` is finite if `R̄`
or `R'` is residually algebraic over `R`: these are the associated primes of the ideal `M'Ã'` of the
noetherian ring `Ã'` (`mem_associatedPrimes_iff_mem_liftPrimes`), of which there are finitely many
(Mathlib: `associatedPrimes.finite`). -/
theorem MonoidalTransform.finite_liftPrimes (α : R →+* Rb) [IsLocalHom α]
    (hα : RingHom.MapsRSOP α) (hP : P.IsPrime) (hS : IsRegularLocalRing (R ⧸ P))
    (t : MonoidalTransform R P)
    (halg : RingHom.IsResiduallyAlgebraic α ∨
      RingHom.IsResiduallyAlgebraic (R := R) (R' := t.ring) t.toRing) :
    (LiftPrimes α (RingHom.MapsRSOP.injective α hα) t).Finite := by
  have := isNoetherianRing_blowupAlgebra (R := Rb) (P := P.map α) (α t.x)
  have hset : associatedPrimes (blowupAlgebra Rb (P.map α) (α t.x))
      (blowupAlgebra Rb (P.map α) (α t.x) ⧸
        t.M'.map (blowupMap α (RingHom.MapsRSOP.injective α hα) P t.x)) =
      LiftPrimes α (RingHom.MapsRSOP.injective α hα) t :=
    Set.ext fun N => t.mem_associatedPrimes_iff_mem_liftPrimes α hα hP hS halg N
  rw [← hset]
  exact associatedPrimes.finite _ _

/-- Lemma 4 (1), "there exist only a finite number of `R̃'`" (p. 212): "the number of `R̃'` … is equal
to the number of the associated prime ideals of `m̄'k̃[X₂,…,X_r]`, which is obviously finite" (p. 211):
the `R̃'` correspond one to one to the associated primes of `M'Ã'`
(`canonicalTransforms_eq_image_liftSubring`, `mem_associatedPrimes_iff_mem_liftPrimes`), which are
finitely many (`finite_liftPrimes`). -/
theorem canonicalTransforms_finite_of_residually_algebraic (α : R →+* Rb) [IsLocalHom α]
    (hα : RingHom.MapsRSOP α) (hP : P.IsPrime) (hS : IsRegularLocalRing (R ⧸ P))
    (t : MonoidalTransform R P)
    (halg : RingHom.IsResiduallyAlgebraic α ∨
      RingHom.IsResiduallyAlgebraic (R := R) (R' := t.ring) t.toRing) :
    (canonicalTransforms α (Pb := P.map α) t).Finite := by
  rw [canonicalTransforms_eq_image_liftSubring α hα t]
  exact (t.finite_liftPrimes α hα hP hS halg).image _

end AssociatedPrimesLift

noncomputable section SurjectiveQuotient

theorem map_map_eq_of_comp_eq {R Rb A' T t₀ : Type*} [CommRing R] [CommRing Rb] [CommRing A']
    [CommRing T] [CommRing t₀] (α : R →+* Rb) (f : Rb →+* A') (g : A' →+* T) (Tr : R →+* T)
    (hTr : Tr = g.comp (f.comp α)) (tr : R →+* t₀) (βT : t₀ →+* T)
    (hcomm : βT.comp tr = Tr) (M : Ideal R) :
    ((M.map α).map f).map g = (M.map tr).map βT := by
  rw [Ideal.map_map, Ideal.map_map, Ideal.map_map, hcomm, hTr]
  rfl

variable {R Rb : Type u} [CommRing R] [IsRegularLocalRing R] [IsDomain R]
  [CommRing Rb] [IsRegularLocalRing Rb] [IsDomain Rb] {P : Ideal R}

/-- A canonical lift `β : R' → R̃'` is, up to the isomorphism `R̃' ≅ Ã'_{M̃'}` of monoidal
transforms with the same subring of `Frac(R̄)`, the canonical lift `R' → Ã'_{M̃'}` of the prime
`M̃' = M_{R̃'} ∩ Ã'` (p. 211: "can be obtained in this manner"). -/
theorem IsCanonicalLift.exists_ringEquiv_ofLift (α : R →+* Rb) [IsLocalHom α]
    (hα : RingHom.MapsRSOP α) (t : MonoidalTransform R P) (tb : MonoidalTransform Rb (P.map α))
    (β : t.ring →+* tb.ring) (hβ : IsCanonicalLift α t tb β) :
    ∃ (N : Ideal (blowupAlgebra Rb (P.map α) (α t.x)))
      (hN : N ∈ LiftPrimes α (RingHom.MapsRSOP.injective α hα) t)
      (e : tb.ring ≃+* (MonoidalTransform.ofLift α hα t N hN).ring),
      ∀ y, e (β y) = MonoidalTransform.ofLiftHom α hα t N hN y := by
  have hNmem := MonoidalTransform.comap_maximalIdeal_blowupToRing_mem_liftPrimes α hα t tb β hβ
  have hsub := MonoidalTransform.subring_eq_ofLift_subring α hα t tb β hβ
  have hβT := MonoidalTransform.isCanonicalLift_ofLiftHom α hα t _ hNmem
  refine ⟨_, hNmem, tb.ringEquivOfSubringEq _ hsub, fun y => ?_⟩
  apply (MonoidalTransform.ofLift α hα t _ hNmem).injective_toFractionRing
  rw [MonoidalTransform.toFractionRing_ringEquivOfSubringEq,
    MonoidalTransform.toFractionRing_map_eq_fractionRingMap α hα t tb β hβ y,
    MonoidalTransform.toFractionRing_map_eq_fractionRingMap α hα t _ _ hβT y]

end SurjectiveQuotient

end L4PrintedRoute

/-! #### Lemma 4 (1): counting the `R̄'` (pp. 211–212) -/

/-- Canonical lifts are compatible with the embeddings into the fields of quotients: the image of
`y ∈ R'` in `Frac(R̄)` does not depend on the canonical lift `R' → R̄'` (`y = c/d` with
`c, d ∈ R`). -/
theorem MonoidalTransform.toFractionRing_map_eq_of_isCanonicalLift (α : R →+* Rb) [IsLocalHom α] (hα : RingHom.MapsRSOP α)
    {P : Ideal R} (t : MonoidalTransform R P) (tb₁ tb₂ : MonoidalTransform Rb (P.map α))
    (β₁ : t.ring →+* tb₁.ring) (β₂ : t.ring →+* tb₂.ring) (hβ₁ : IsCanonicalLift α t tb₁ β₁)
    (hβ₂ : IsCanonicalLift α t tb₂ β₂) (y : t.ring) :
    tb₁.toFractionRing (β₁ y) = tb₂.toFractionRing (β₂ y) := by
  obtain ⟨c, d, hd, hcd⟩ := t.exists_toRing_mul_eq y
  have key : ∀ (tb : MonoidalTransform Rb (P.map α)) (β : t.ring →+* tb.ring),
      IsCanonicalLift α t tb β → algebraMap Rb (FractionRing Rb) (α d) * tb.toFractionRing (β y) =
        algebraMap Rb (FractionRing Rb) (α c) := by
    intro tb β hβ
    have hcomm : ∀ r, β (t.toRing r) = tb.toRing (α r) := fun r => RingHom.congr_fun hβ.comm r
    have h := congrArg (fun w => tb.toFractionRing (β w)) hcd
    simp only [map_mul] at h
    rwa [hcomm, hcomm, tb.toFractionRing_toRing, tb.toFractionRing_toRing] at h
  have hd' : algebraMap Rb (FractionRing Rb) (α d) ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr
      ((map_ne_zero_iff _ (RingHom.MapsRSOP.injective α hα)).mpr hd)
  exact mul_left_cancel₀ hd' ((key tb₁ β₁ hβ₁).trans (key tb₂ β₂ hβ₂).symm)

/-- Comparison of two canonical lifts `R' → R̄'₁`, `R' → R̄'₂` through `R' ⊗_R R̄`: if every element
of `R' ⊗_R R̄` invertible in `R̄'₁` is invertible in `R̄'₂`, then `R̄'₁ ⊆ R̄'₂` inside `Frac(R̄)`. -/
theorem MonoidalTransform.subring_le_of_isCanonicalLift (α : R →+* Rb) [IsLocalHom α] (hα : RingHom.MapsRSOP α)
    {P : Ideal R} (t : MonoidalTransform R P) (tb₁ tb₂ : MonoidalTransform Rb (P.map α))
    (β₁ : t.ring →+* tb₁.ring) (β₂ : t.ring →+* tb₂.ring) (hβ₁ : IsCanonicalLift α t tb₁ β₁)
    (hβ₂ : IsCanonicalLift α t tb₂ β₂) :
    letI : Algebra R Rb := α.toAlgebra
    letI : Algebra R t.ring := t.toRing.toAlgebra
    ∀ (Θ₁ : t.ring ⊗[R] Rb →+* tb₁.ring) (Θ₂ : t.ring ⊗[R] Rb →+* tb₂.ring),
      (∀ y b, Θ₁ (y ⊗ₜ b) = β₁ y * tb₁.toRing b) → (∀ y b, Θ₂ (y ⊗ₜ b) = β₂ y * tb₂.toRing b) →
      (∀ z, ∃ a b, IsUnit (Θ₁ b) ∧ z * Θ₁ b = Θ₁ a) →
      (∀ z, Θ₂ z ∈ maximalIdeal tb₂.ring → Θ₁ z ∈ maximalIdeal tb₁.ring) →
      tb₁.subring ≤ tb₂.subring := by
  let _ : Algebra R Rb := α.toAlgebra
  let _ : Algebra R t.ring := t.toRing.toAlgebra
  intro Θ₁ Θ₂ hΘ₁ hΘ₂ hfrac hmax
  have hΘ : ∀ z, tb₁.toFractionRing (Θ₁ z) = tb₂.toFractionRing (Θ₂ z) := by
    intro z
    induction z with
    | tmul y b =>
      rw [hΘ₁, hΘ₂, map_mul, map_mul, tb₁.toFractionRing_toRing, tb₂.toFractionRing_toRing,
        MonoidalTransform.toFractionRing_map_eq_of_isCanonicalLift α hα t tb₁ tb₂ β₁ β₂ hβ₁ hβ₂ y]
    | add z z' hz hz' => rw [map_add, map_add, map_add, map_add, hz, hz']
  intro x hx
  obtain ⟨w, rfl⟩ := RingHom.mem_range.mp hx
  obtain ⟨a, b, hbu, hwb⟩ := hfrac w
  have hb2 : IsUnit (Θ₂ b) := by
    by_contra h
    exact (IsLocalRing.mem_maximalIdeal _).mp (hmax b ((IsLocalRing.mem_maximalIdeal _).mpr h)) hbu
  refine RingHom.mem_range.mpr ⟨Θ₂ a * ↑hb2.unit⁻¹, ?_⟩
  have hb1 : tb₁.toFractionRing (Θ₁ b) ≠ 0 := (hbu.map tb₁.toFractionRing).ne_zero
  apply mul_right_cancel₀ hb1
  rw [← map_mul tb₁.toFractionRing w, hwb, hΘ b, hΘ a, ← map_mul, mul_assoc, IsUnit.val_inv_mul,
    mul_one]

open Classical in
/-- Lemma 4 (3), residually separable case (p. 212), along the printed route: "for every prime ideal
`q̃` in `k̃[X̄]` such that `q̃ ∩ k[X̄] = (0)`, the localization of `k̃[X̄]` with respect to `q̃` is
regular. It follows that … the image of a regular system of parameters of `R'` can be extended to a
regular system of parameters of `R̃'`."  The localization `k̃[X̄]_{q̃}` is the fibre `R̃'/M'R̃'`
(`MonoidalTransform.exists_fibre_properties`), which is regular, and `dim R̃' = dim R' + dim` of the fibre;
the image of a regular system of parameters of `R'` together with lifts of one of the fibre is a regular
system of parameters of `R̃'` (`exists_isRegularSystemOfParameters_image_union`). -/
theorem IsCanonicalLift.extendsToRSOP_image_of_isResiduallySeparable (α : R →+* Rb) [IsLocalHom α]
    (hα : RingHom.MapsRSOP α) {P : Ideal R} (hP : P.IsPrime) (hS : IsRegularLocalRing (R ⧸ P))
    (t : MonoidalTransform R P) (tb : MonoidalTransform Rb (P.map α))
    (β : t.ring →+* tb.ring) (hβ : IsCanonicalLift α t tb β)
    (hsep : RingHom.IsResiduallySeparable α) (s : Finset t.ring)
    (hs : IsRegularSystemOfParameters t.ring s) :
    ExtendsToRSOP tb.ring (s.image β) := by
  have := hβ.isLocalHom
  have := MonoidalTransform.isNoetherianRing tb
  obtain ⟨hdim, hreg, -⟩ := IsCanonicalLift.exists_fibre_properties α hα hP hS t tb β hβ
  have : IsLocalRing (tb.ring ⧸ (maximalIdeal t.ring).map β) :=
    isLocalRing_quotient_of_le (Ideal.map_le_iff_le_comap.mpr fun a ha => map_nonunit β a ha)
  obtain ⟨U, hU⟩ := exists_isRegularSystemOfParameters_image_union β s hs (hreg hsep) hdim
  exact ⟨_, Finset.subset_union_left, hU⟩

open Classical in
/-- Lemma 4 (3), separable algebraic case (p. 212): then the fibre `R̃'/M'R̃'` is a field
(`k̃[X̄]_{q̃}` is a localization of `K ⊗_k k̃`, every localization of which is a field), i.e.
`M'R̃' = M̃'` and `dim R̃' = dim R'`, so the image of a regular system of parameters of `R'` is one of `R̃'`. -/
theorem IsCanonicalLift.isRegularSystemOfParameters_image_of_isResiduallySeparableAlgebraic
    (α : R →+* Rb) [IsLocalHom α] (hα : RingHom.MapsRSOP α) {P : Ideal R} (hP : P.IsPrime)
    (hS : IsRegularLocalRing (R ⧸ P)) (t : MonoidalTransform R P)
    (tb : MonoidalTransform Rb (P.map α)) (β : t.ring →+* tb.ring) (hβ : IsCanonicalLift α t tb β)
    (hsep : RingHom.IsResiduallySeparableAlgebraic α) (s : Finset t.ring)
    (hs : IsRegularSystemOfParameters t.ring s) :
    IsRegularSystemOfParameters tb.ring (s.image β) := by
  have := hβ.isLocalHom
  have := MonoidalTransform.isNoetherianRing tb
  obtain ⟨hdim, -, hmax⟩ := IsCanonicalLift.exists_fibre_properties α hα hP hS t tb β hβ
  have hI := hmax hsep
  have hle : (maximalIdeal t.ring).map β ≤ maximalIdeal tb.ring :=
    Ideal.map_le_iff_le_comap.mpr fun a ha => map_nonunit β a ha
  have hmaxeq : (maximalIdeal t.ring).map β = maximalIdeal tb.ring :=
    hI.eq_of_le (maximalIdeal.isMaximal tb.ring).ne_top hle
  have hF0 : ringKrullDim (tb.ring ⧸ (maximalIdeal t.ring).map β) = 0 := by
    have := hI
    let := Ideal.Quotient.field ((maximalIdeal t.ring).map β)
    exact ringKrullDim_eq_zero_of_field _
  have hd : ringKrullDim tb.ring = ringKrullDim t.ring := by rw [hdim, hF0, add_zero]
  exact isRegularSystemOfParameters_image_of_map_maximalIdeal_eq β s hs hmaxeq hd

/-- Lemma 4 (1) (pp. 211–212).  The canonical lifts `R' → R̄'` correspond to prime ideals `q̄` of
`k' ⊗_k k̄` (`IsCanonicalLift.exists_tensorHom_injective_and_isFraction_and_quotient_equiv`); the subring `R̄' ⊆ Frac(R̄)` is determined by `q̄`
(`MonoidalTransform.subring_le_of_isCanonicalLift`).  If `k̄` or `k'` is algebraic over `k`, then `k' ⊗_k k̄` has finitely many
primes, at most `[k̄ : k]_s` of them in the first case, and has dimension `0`, so that the closed
fibre `R̄'/M_{R'}R̄'` has dimension `0` and `dim R̄' = dim R'` by flatness. -/
theorem canonicalTransforms_finite_and_ringKrullDim_eq_and_card_le (α : R →+* Rb) [IsLocalHom α] (hα : RingHom.MapsRSOP α) {P : Ideal R}
    (hP : P.IsPrime) (hS : IsRegularLocalRing (R ⧸ P)) :
    ∀ t : MonoidalTransform R P,
      RingHom.IsResiduallyAlgebraic α ∨
          RingHom.IsResiduallyAlgebraic (R := R) (R' := t.ring) t.toRing →
        (canonicalTransforms α (Pb := P.map α) t).Finite ∧
        (∀ (tb : MonoidalTransform Rb (P.map α)) (β : t.ring →+* tb.ring),
          IsCanonicalLift α t tb β → ringKrullDim tb.ring = ringKrullDim t.ring) ∧
        (RingHom.IsResiduallyAlgebraic α →
          letI := (ResidueField.map α).toAlgebra
          Cardinal.mk ↥(canonicalTransforms α (Pb := P.map α) t) ≤
            Field.sepDegree (ResidueField R) (ResidueField Rb)) := by
  intro t halg
  exact ⟨canonicalTransforms_finite_of_residually_algebraic α hα hP hS t halg,
    fun tb β hβ => MonoidalTransform.ringKrullDim_eq_of_isCanonicalLift α hα hP hS t halg tb β hβ,
    fun hres => canonicalTransforms_card_le_sepDegree α hα hP hS t hres⟩

open Classical in
/-- Lemma 4, p. 212: "Let `α : R → R̄` be a local homomorphism of regular local rings such that
a regular system of parameters of `R` is transformed into such a system of parameters of `R̄`.
Let `P` be a prime ideal in `R` such that `R/P` is regular. Then `P̄ = PR̄` is a prime ideal and
`R̄/P̄` is regular. Let `R'` be a monoidal transform of `R` with center `P`. We consider those
monoidal transforms, denoted by `R̄'`, of `R̄` with center `P̄` such that we have the
commutative diagram of canonical local homomorphisms (`IsCanonicalLift`). We then have the
following facts:
(1) If either `R̄` or `R'` is residually algebraic over `R`, then there exist only a finite
number of `R̄'`, all the `R̄'` have the same dimension as `R'`, and if `R̄` is residually
algebraic over `R` the number of `R̄'` does not exceed the separable degree of the residue field
of `R̄` over that of `R`.
(2) All the local homomorphisms of the above diagram are injective, and the residue field of
`R̄'` is generated by those of `R'` and `R̄` over that of `R`.
(3) If `R̄` is residually separable (resp. separable algebraic) over `R`, then the image of a
regular system of parameters of `R'` by any of the local homomorphisms `R' → R̄'` can be
extended to (resp. the image is) a regular system of parameters of `R̄'`."

Formalization notes (encoding): the `R̄'` are counted as subrings of `Frac(R̄)`
(`canonicalTransforms`); "the number does not exceed the separable degree" is
`Cardinal.mk … ≤ Field.sepDegree k k̄` (Mathlib's separable degree of a general field extension, a cardinal); "generated by those of
`R'` and `R̄`" is: the subfield of the residue field of `R̄'` generated by the images of the
residue fields of `R'` and of `R̄` is everything (the residue field of `R` maps into both, so
"over that of `R`" is automatic).

Proof as printed (pp. 210–212), in Lean:
* the charts `A'/MA' ≅ k[X₂, …, X_r]`, `Ã'/M̄Ã' ≅ k̃[X₂, …, X_r]` compatible with `A' → Ã'` and
  `k[X] → k̃[X]`, `X_j ↦ X_j` (`MonoidalTransform.exists_charts_residue`);
* "The associated prime ideals of `M'Ã'` correspond to the associated prime ideals of
  `m̄'k̃[X₂, …, X_r]` in a one to one fashion by the natural homomorphism of `Ã'` onto `k̃[X₂, …, X_r]`"
  (`mem_associatedPrimes_quotient_iff_map` in `Hironaka/Compat/AssociatedPrimes.lean`,
  `MonoidalTransform.bijOn_map_associatedPrimes`);
* "if `M̃'` is an associated prime ideal of `M'Ã'`, then we have a canonical local homomorphism of
  `R' = A'_{M'}` into `R̃' = Ã'_{M̃'}`": the associated primes of `m̄'k̃[X]` lie over `m̄'`
  (`comap_eq_of_mem_associatedPrimes`, "because `m̄'` is a prime ideal"), so an associated prime of
  `M'Ã'` lies over `M'` (`mem_liftPrimes_of_mem_associatedPrimes`) and gives `R̃' = Ã'_{M̃'}`
  (`MonoidalTransform.ofLift`, `ofLiftHom`, `isCanonicalLift_ofLiftHom`); "and that if either `k̃` or
  `R'/M'R'` is algebraic over `k`, then every monoidal transform `R̃'` … which admits a canonical local
  homomorphism `R' → R̃'` can be obtained in this manner" (`subring_eq_ofLift_subring` and
  `mem_associatedPrimes_of_mem_liftPrimes`; together `mem_associatedPrimes_iff_mem_liftPrimes`): the
  one-to-one correspondence `R̃' ↔ M̃'` (`canonicalTransforms_eq_image_liftSubring`, `injOn_liftSubring`);
* "We note here that all the associated prime ideals of `m̄'k̃[X]` are isolated because `m̄'` is a prime
  ideal in `k[X]`": for every field extension `k̃/k` this is `Hironaka.mem_minimalPrimes_of_mem_associatedPrimes`
  (`Hironaka/Compat/EmbeddedPrimes.lean`: Noether normalization of `k[X]/m̄'`, non-zero-divisors of `k̃[T]`
  on `K ⊗_k k̃`, incomparability), in the chart form
  `MonoidalTransform.mem_minimalPrimes_of_mem_associatedPrimes_map_general`; in the cases in which the paper
  counts (`k̃/k` or `R'/M'R'` algebraic) it also follows directly from the primes over `m̄'`
  (`mem_minimalPrimes_of_mem_associatedPrimes_map`, from `map_mem_minimalPrimes_of_mem_liftPrimes`);
* "Therefore, if either `R̃` or `R'` is residually algebraic over `R`, then the number of `R̃'` … is equal
  to the number of the associated prime ideals of `m̄'k̃[X]`, which is obviously finite"
  (`mk_canonicalTransforms_eq_mk_associatedPrimes`; finite since a noetherian module has finitely many
  associated primes: `finite_liftPrimes`, `canonicalTransforms_finite_of_residually_algebraic`);
* "the set of those prime ideals `q̃` [of `k̃[X̄]` with `q̃ ∩ k[X̄] = (0)`] is in a one to one correspondence
  with the set of those `R̃'` which admit a canonical local homomorphism" (`bijOn_map_liftPrimes`,
  `nonempty_canonicalTransforms_equiv_primes`; the surjectivity is new);
* "`(α(x₁), …, α(x_r))` is a minimal base of the ideal `P̄`" (p. 210,
  `RingHom.MapsRSOP.exists_minimalBase_image`);
* the dimensions: `dim R' = dim S + ht m̄' + 1` (p. 210, `ringKrullDim_eq_of_chart`), the same for `R̃'`
  and, by going down for the free extension `k[X] → k̃[X]` (`height_eq_of_mem_minimalPrimes_map`),
  `dim R̃' = dim R'` (`MonoidalTransform.ringKrullDim_eq_of_isCanonicalLift`);
* "`k̃ ⊗_k k[X̄] → k̃[X̄]` canonical isomorphism" and the injection of the `R̃'` into the primes of
  `K ⊗_k k̃`, `K = Frac k[X̄]`, whence the bound by the separable degree
  (`exists_ringHom_tensor_fractionRing`, `canonicalTransforms_card_le_sepDegree`);
* (2): `α` is injective (`RingHom.MapsRSOP.injective`: `α⁻¹(M̄ⁿ) = Mⁿ`, no flatness), the others by
  fractions (`IsCanonicalLift.injective_of_mapsRSOP`, `closure_residueField_ranges_eq_top`);
* (3): the fibre `R̃'/M'R̃' = k̃[X̄]_{q̃}` is a localization of `K ⊗_k k̃` (regular if `k̃` is separable,
  a field if separable algebraic: `MonoidalTransform.exists_fibre_properties`) and
  `dim R̃' = dim R' + dim` of the fibre; the image of a regular system of parameters of `R'` together with
  lifts of one of the fibre is one of `R̃'` (`exists_isRegularSystemOfParameters_image_union`).
The proof does not use flatness of `α`.

Gaps filled ("it is easily seen", "obviously finite", "it follows"): the three printed
identifications above, the compatibility of the charts, the dimension count of `R̃'` and the rsop
extension; also the correspondence of the associated primes, that an associated prime of `M'Ã'` lies over
`M'` (the paper: "it is easily seen"), the equality of the number of the `R̃'` with the number of the
associated primes, the surjectivity onto the `q̃`, and the minimality of the base `(α(x_i))` (p. 210).
The route is the printed one, including the remark that all the associated primes of `m̄'k̃[X]` are
isolated (for every `k̃/k`). -/
@[blueprint "lem:III.4"
  (statement := /-- Let $\alpha\colon R\to\bar R$ be a local homomorphism of regular local rings
    such that a regular system of parameters of $R$ is transformed into such a system of
    parameters of $\bar R$ (\cref{def:III.rsop-map}). Let $P$ be a prime ideal in $R$ such that
    $R/P$ is regular. Then $\bar P=P\bar R$ is a prime ideal and $\bar R/\bar P$ is regular. Let
    $R'$ be a monoidal transform of $R$ with center $P$. Consider those monoidal transforms
    $\bar R'$ of $\bar R$ with center $\bar P$ admitting a canonical local homomorphism
    $R'\to\bar R'$ (\cref{def:III.2-canonical}). Then:
    (1) If either $\bar R$ or $R'$ is residually algebraic over $R$, then there exist only a
    finite number of $\bar R'$, all the $\bar R'$ have the same dimension as $R'$, and if
    $\bar R$ is residually algebraic over $R$ the number of $\bar R'$ does not exceed the
    separable degree of the residue field of $\bar R$ over that of $R$.
    (2) All the local homomorphisms of the diagram are injective, and the residue field of
    $\bar R'$ is generated by those of $R'$ and $\bar R$ over that of $R$.
    (3) If $\bar R$ is residually separable (resp.\ separable algebraic) over $R$, then the
    image of a regular system of parameters of $R'$ by any of the local homomorphisms
    $R'\to\bar R'$ can be extended to (resp.\ the image is) a regular system of parameters of
    $\bar R'$. (Lemma 4, p.~212.) (Formalization note (encoding): the $\bar R'$ are counted as
    subrings of the field of quotients of $\bar R$, and ``the number does not exceed the
    separable degree'' is an inequality of cardinals.) -/)
  (proof := /-- The paper's argument (pp.~210--212). Let $(x_1,\dots,x_r)$ be a minimal base of $P$, extended to a
    regular system of parameters $(x_1,\dots,x_r,y_1,\dots,y_s)$ of $R$; then
    $(\alpha(x_1),\dots,\alpha(x_r))$ is a minimal base of $\bar P$ and
    $(\alpha(x_i),\alpha(y_j))$ is a regular system of parameters of $\bar R$, whence
    $\bar P$ is prime with $\bar R/\bar P$ regular. Let $A'=R[x_2/x_1,\dots,x_r/x_1]$,
    $\bar A'=\bar R[\alpha(x_2)/\alpha(x_1),\dots]$, $M'$ a prime of $A'$ containing $MA'$,
    $\bar m'=M'/MA'\subseteq k[X_2,\dots,X_r]$. The homomorphism $A'\to\bar A'$ induces
    $k[X_2,\dots,X_r]\to\bar k[X_2,\dots,X_r]$, $X_j\mapsto X_j$. The associated primes of
    $M'\bar A'$ correspond one to one to those of $\bar m'\bar k[X_2,\dots,X_r]$, all isolated
    since $\bar m'$ is prime; if $\bar M'$ is such a prime one gets a canonical local
    homomorphism $A'_{M'}\to\bar A'_{\bar M'}$, and if either $\bar k$ or $R'/M'R'$ is
    algebraic over $k$ every $\bar R'$ admitting a canonical homomorphism arises so. Hence the
    number of $\bar R'$ equals the number of associated primes of
    $\bar m'\bar k[X_2,\dots,X_r]$, which is finite; if $\bar k/k$ is algebraic it is at most
    the separable degree of $\bar k/k$, since
    $\bar k\otimes_k k[X_2,\dots,X_r]/\bar m'\cong\bar k[X_2,\dots,X_r]/\bar m'\bar k[X]$.
    The set of the $\bar R'$ is in one to one correspondence with the set of the primes
    $\bar{\mathfrak q}$ of $\bar k\otimes_k(k[X]/\bar m')$ with
    $\bar{\mathfrak q}\cap(k[X]/\bar m')=(0)$. (The paper gives no separate argument for
    (2); it is read off from this description.) If $\bar k$ is separable over $k$ (for every
    purely inseparable $k'/k$, $\bar k\otimes_kk'$ is reduced), the localization of
    $\bar k\otimes_k(k[X]/\bar m')$ at any such $\bar{\mathfrak q}$ is regular, and ``it follows
    that'' (3) holds.

    \textbf{In Lean} (the printed route; no flatness of $\alpha$ is used). The charts
    $A'/MA'\cong k[X_2,\dots,X_r]$, $\bar A'/\bar M\bar A'\cong\bar k[X_2,\dots,X_r]$ are
    compatible with $A'\to\bar A'$ and $k[X]\to\bar k[X]$. The associated primes of $M'\bar A'$
    correspond one to one to those of $\bar m'\bar k[X]$ (\cref{lem:III.4-associated-primes});
    these lie over $\bar m'$, because the elements of $k[X]\setminus\bar m'$ are non-zero-divisors
    modulo $\bar m'\bar k[X]$, so the associated primes $\bar M'$ of $M'\bar A'$ are primes of
    $\bar A'$ over $M'$ and give the canonical homomorphisms $R'\to\bar A'_{\bar M'}$; every $\bar R'$
    admitting a canonical homomorphism arises so, one to one, and if $\bar k$ or $R'/M'R'$ is algebraic
    over $k$ the primes $\bar M'\bar k[X]$ over $\bar m'$ are minimal over $\bar m'\bar k[X]$, hence
    associated: the number of the $\bar R'$ is the number of the associated primes of
    $\bar m'\bar k[X]$ (finitely many). Going down for
    the free extension $k[X]\to\bar k[X]$ and the dimension formula
    $\dim R'=\dim R/P+\operatorname{ht}\bar m'+1$ give $\dim\bar R'=\dim R'$; the $\bar R'$ inject into
    the primes of $K\otimes_k\bar k$, $K=\operatorname{Frac}k[X]/\bar m'$, which gives the bound
    $[\bar k:k]_s$ (\cref{compat:field-tensor-sepdeg-fg}). In (3) the fibre
    $\bar R'/M'\bar R'$ is a localization of $K\otimes_k\bar k$, regular if $\bar k/k$ is separable
    (\cref{compat:field-tensor-regular}) and a field if separable algebraic
    (\cref{compat:field-tensor-local-field}), and $\dim\bar R'=\dim R'+\dim$ fibre; the image of a
    regular system of parameters of $R'$ with lifts of one of the fibre is one of $\bar R'$. In (2)
    $\alpha$ is injective since $\alpha^{-1}(\bar M^n)=M^n$ and the residue field of $\bar R'$ is
    generated by those of $R'$ and $\bar R$ by fractions.

    \textbf{Gaps in the paper filled} (``it is easily seen'', ``obviously finite'', ``it follows''):
    the identifications, the correspondence of the associated primes, the dimension count, the
    surjectivity onto the primes $\bar{\mathfrak q}$, the minimality of the base
    $(\alpha(x_i))$ and the extension of the regular system of parameters.

    The remark that all the associated primes of $\bar m'\bar k[X]$ are isolated is proved for
    every field extension $\bar k/k$ (\cref{lem:III.4-isolated}). -/)
  (latexEnv := "lemma")]
theorem RingHom.MapsRSOP.canonicalLift_properties (α : R →+* Rb) [IsLocalHom α] (hα : RingHom.MapsRSOP α) {P : Ideal R}
    (hP : P.IsPrime)
    (hS : IsRegularLocalRing (R ⧸ P)) :
    -- `P̄ = PR̄` is a prime ideal and `R̄/P̄` is regular
    ((P.map α).IsPrime ∧ IsRegularLocalRing (Rb ⧸ P.map α)) ∧
    -- (1)
    (∀ t : MonoidalTransform R P,
      RingHom.IsResiduallyAlgebraic α ∨
          RingHom.IsResiduallyAlgebraic (R := R) (R' := t.ring) t.toRing →
        (canonicalTransforms α (Pb := P.map α) t).Finite ∧
        (∀ (tb : MonoidalTransform Rb (P.map α)) (β : t.ring →+* tb.ring),
          IsCanonicalLift α t tb β → ringKrullDim tb.ring = ringKrullDim t.ring) ∧
        (RingHom.IsResiduallyAlgebraic α →
          letI := (ResidueField.map α).toAlgebra
          Cardinal.mk ↥(canonicalTransforms α (Pb := P.map α) t) ≤
            Field.sepDegree (ResidueField R) (ResidueField Rb))) ∧
    -- (2)
    (∀ (t : MonoidalTransform R P) (tb : MonoidalTransform Rb (P.map α))
      (β : t.ring →+* tb.ring) (hβ : IsCanonicalLift α t tb β),
        Function.Injective α ∧ Function.Injective t.toRing ∧ Function.Injective tb.toRing ∧
        Function.Injective β ∧
        haveI := hβ.isLocalHom
        Subfield.closure
            (Set.range (ResidueField.map (R := t.ring) (S := tb.ring) β) ∪
              Set.range (ResidueField.map (R := Rb) (S := tb.ring) tb.toRing)) = ⊤) ∧
    -- (3)
    (∀ (t : MonoidalTransform R P) (tb : MonoidalTransform Rb (P.map α))
      (β : t.ring →+* tb.ring), IsCanonicalLift α t tb β →
        (RingHom.IsResiduallySeparable α → ∀ s : Finset t.ring,
          IsRegularSystemOfParameters t.ring s → ExtendsToRSOP tb.ring (s.image β)) ∧
        (RingHom.IsResiduallySeparableAlgebraic α → ∀ s : Finset t.ring,
          IsRegularSystemOfParameters t.ring s →
            IsRegularSystemOfParameters tb.ring (s.image β))) := by
  exact ⟨RingHom.MapsRSOP.isPrime_map_and_isRegularLocalRing_quotient hα hP hS, canonicalTransforms_finite_and_ringKrullDim_eq_and_card_le α hα hP hS, RingHom.MapsRSOP.injective_and_closure_residueField_ranges_eq_top α hα,
    fun t tb β hβ => ⟨fun hsep s hs => IsCanonicalLift.extendsToRSOP_image_of_isResiduallySeparable α hα hP hS t tb β hβ hsep s hs,
      fun hsep s hs => IsCanonicalLift.isRegularSystemOfParameters_image_of_isResiduallySeparableAlgebraic α hα hP hS t tb β hβ hsep s hs⟩⟩

end Lemma4

/-! ### Remarks 0 and 1 after Definition 5 (pp. 213–214)

Remark 0 (p. 213): "In the above definition of the strict (resp. the weak) transform `J'` of `J`
in the monoidal transform `R'` of `R` with center `P`, the reference to the center `P` is
essential. A simple example shows that we can have one and the same local ring `R'` (in the
field of quotients of `R`) which is the monoidal transforms of `R` with two different centers
`P` and `Q`. Moreover, the transform `J'` of `J` in `R'` with respect to `P` may not be the same
as that of `J` in `R'` with respect to `Q`. However, by an abuse of language, if the center in
`R` with which `R'` is a monoidal transform of `R` is specified in the same context, we shall
speak of the strict (resp. the weak) transform of `J` in `R'` (with respect to the same center
as for `R'`) without explicitly mentioning the reference to the center."

In the formalization the center is part of the type `MonoidalTransform R P` of `R'`, so
`strictTransformIdeal t J` and `weakTransformIdeal t J` always refer to it.

The claim of Remark 0 that "a simple example shows" that one local ring `R'` can be a monoidal
transform of `R` with two different centers `P` and `Q`, with different transforms of `J`, is
formalized in `Hironaka/Ch3/TransformsRemark0.lean` (`hasTwoCenters_of_prime_regular`, the example
`R' = R` with the centers `R` and `(x₀)`; `hasTwoCenters_powerSeries`, `R = ℚ⟦X⟧`). -/

section Remark1

variable {R : Type u} [CommRing R] [IsRegularLocalRing R] [IsDomain R] {P : Ideal R}
  (t : MonoidalTransform R P)

/-- The ideal "`x⁻ᵛ I R'`" of Remark 1 (p. 214), for `x ∈ R'` and an ideal `I` of `R` (used with
`I ⊆ Pᵛ`): the ideal of `R'` generated by the elements `y` with `xᵛ y = f` for some `f ∈ I`
(in the domain `R'` such a `y` is the unique quotient `x⁻ᵛ f`). -/
noncomputable def MonoidalTransform.divIdeal (x : t.ring) (ν : ℕ) (I : Ideal R) : Ideal t.ring :=
  Ideal.span {y : t.ring | ∃ f ∈ I, x ^ ν * y = t.toRing f}

/-- A generator `x` of `PR'` is non-zero. -/
private theorem MonoidalTransform.ne_zero_of_span_eq_map {x : t.ring}
    (hx : Ideal.span {x} = P.map t.toRing) : x ≠ 0 := by
  rintro rfl
  have h := hx ▸ Ideal.mem_map_of_mem t.toRing t.x_mem
  rw [Ideal.mem_span_singleton, zero_dvd_iff, ← map_zero t.toRing] at h
  exact t.x_ne_zero (MonoidalTransform.toRing_injective t h)

/-- If `(x)R' = PR'`, then every `h ∈ Pᵏ` maps to a multiple of `xᵏ` in `R'`. -/
private theorem MonoidalTransform.exists_toRing_eq_pow_mul_of_mem_pow {x : t.ring}
    (hx : Ideal.span {x} = P.map t.toRing) {k : ℕ} {h : R} (hh : h ∈ P ^ k) :
    ∃ c, t.toRing h = x ^ k * c := by
  have hmem : t.toRing h ∈ (P ^ k).map t.toRing := Ideal.mem_map_of_mem _ hh
  rw [Ideal.map_pow, ← hx, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at hmem
  exact hmem

/-- Two generators of `PR'` differ by a unit: if `x'ᵛ y = a` and every `z` with `xᵛ z = a` lies
in the ideal `I`, then so does `y`. -/
private theorem MonoidalTransform.mem_of_span_eq_map {x x' : t.ring}
    (hx : Ideal.span {x} = P.map t.toRing) (hx' : Ideal.span {x'} = P.map t.toRing)
    {ν : ℕ} {y a : t.ring} (hy : x' ^ ν * y = a) {I : Ideal t.ring}
    (hI : ∀ z, x ^ ν * z = a → z ∈ I) : y ∈ I := by
  obtain ⟨u, hu⟩ := Ideal.span_singleton_eq_span_singleton.mp (hx.trans hx'.symm)
  have h := hI (↑u ^ ν * y) (by rw [← hy, ← hu]; ring)
  have hyu : y = ↑(u⁻¹) ^ ν * (↑u ^ ν * y) := by
    rw [← mul_assoc, ← mul_pow, Units.inv_mul, one_pow, one_mul]
  rw [hyu]
  exact I.mul_mem_left _ h

/-- `ν ≤ ν_I(f)` implies `f ∈ Iᵛ`. -/
theorem Ideal.mem_pow_of_le_ordElem {A : Type*} [CommRing A] {I : Ideal A} {f : A}
    {ν : ℕ} (h : (ν : ℕ∞) ≤ Ideal.ordElem I f) : f ∈ I ^ ν := by
  by_contra hf
  cases ν with
  | zero => exact hf (by simp)
  | succ m =>
    have h' := h.trans (Ideal.ordElem_le_of_notMem hf)
    rw [Nat.cast_le] at h'
    omega

/-- `ν ≤ ν_I(J)` implies `J ⊆ Iᵛ`. -/
theorem Ideal.le_pow_of_le_ord {A : Type*} [CommRing A] {I J : Ideal A}
    {ν : ℕ} (h : (ν : ℕ∞) ≤ Ideal.ord I J) : J ≤ I ^ ν := by
  by_contra hJ
  cases ν with
  | zero => exact hJ (by simp)
  | succ m =>
    have h' : Ideal.ord I J ≤ m := Ideal.ord_le fun μ hμ => by
      by_contra hlt
      rw [not_le, Nat.cast_lt] at hlt
      exact hJ (hμ.trans (Ideal.pow_le_pow_right hlt))
    have h'' := h.trans h'
    rw [Nat.cast_le] at h''
    omega

/-- Remark 1, first half: the strict transform is the union of the `x⁻ᵛ(J ∩ Pᵛ)R'`. -/
private theorem MonoidalTransform.strictTransformIdeal_eq_iSup_of_span_eq (J : Ideal R) {x : t.ring}
    (hx : Ideal.span {x} = P.map t.toRing) :
    strictTransformIdeal t J = ⨆ ν : ℕ, t.divIdeal x ν (J ⊓ P ^ ν) := by
  apply le_antisymm
  · rw [strictTransformIdeal, Ideal.span_le]
    rintro y ⟨x', hx', f, hfJ, n, hn, hy⟩
    refine Ideal.mem_iSup_of_mem n (MonoidalTransform.mem_of_span_eq_map t hx hx' hy fun z hz => ?_)
    exact Ideal.subset_span ⟨f, ⟨hfJ, Ideal.mem_pow_of_le_ordElem hn⟩, hz⟩
  · refine iSup_le fun ν => ?_
    rw [MonoidalTransform.divIdeal, Ideal.span_le]
    rintro z ⟨f, hf, hz⟩
    exact Ideal.subset_span ⟨x, hx, f, hf.1, ν, Ideal.le_ordElem hf.2, hz⟩

/-- Remark 1, first half, for any generator `x` of `PR'`: the strict transform is the union of
the `x⁻ᵛ(J ∩ Pᵛ)R'`. -/
theorem MonoidalTransform.strictTransformIdeal_eq_iSup (J : Ideal R) {x : t.ring}
    (hx : Ideal.span {x} = P.map t.toRing) :
    strictTransformIdeal t J = ⨆ ν : ℕ, t.divIdeal x ν (J ⊓ P ^ ν) :=
  MonoidalTransform.strictTransformIdeal_eq_iSup_of_span_eq t J hx

/-- Remark 1, second half, for any generator `x` of `PR'`: the weak transform is the union of the
`x⁻ᵛ J R'` with `J ⊆ Pᵛ`. -/
theorem MonoidalTransform.weakTransformIdeal_eq_iSup (J : Ideal R) {x : t.ring}
    (hx : Ideal.span {x} = P.map t.toRing) :
    weakTransformIdeal t J = ⨆ (ν : ℕ) (_ : J ≤ P ^ ν), t.divIdeal x ν J := by
  apply le_antisymm
  · rw [weakTransformIdeal, Ideal.span_le]
    rintro y ⟨x', hx', f, hfJ, n, hn, hy⟩
    refine Ideal.mem_iSup_of_mem n (Ideal.mem_iSup_of_mem (Ideal.le_pow_of_le_ord hn)
      (MonoidalTransform.mem_of_span_eq_map t hx hx' hy fun z hz => Ideal.subset_span ⟨f, hfJ, hz⟩))
  · refine iSup₂_le fun ν hν => ?_
    rw [MonoidalTransform.divIdeal, Ideal.span_le]
    rintro z ⟨f, hf, hz⟩
    exact Ideal.subset_span ⟨x, hx, f, hf, ν, Ideal.le_ord hν, hz⟩

theorem MonoidalTransform.divIdeal_mono (x : t.ring) (ν : ℕ) {I I' : Ideal R} (h : I ≤ I') :
    t.divIdeal x ν I ≤ t.divIdeal x ν I' := by
  rw [MonoidalTransform.divIdeal, Ideal.span_le]
  rintro y ⟨f, hf, hy⟩
  exact Ideal.subset_span ⟨f, h hf, hy⟩

/-- For `J ⊆ Pᵛ`, `x⁻ᵛ J R'` is the colon ideal `(JR' : xᵛR')` (`R'` is a domain). -/
theorem MonoidalTransform.divIdeal_eq_colon (J : Ideal R) {x : t.ring}
    (hx : Ideal.span {x} = P.map t.toRing) {ν : ℕ} (hJ : J ≤ P ^ ν) :
    t.divIdeal x ν J = (J.map t.toRing).colon ((Ideal.span {x} ^ ν : Ideal _) : Set t.ring) := by
  apply le_antisymm
  · rw [MonoidalTransform.divIdeal, Ideal.span_le]
    rintro y ⟨f, hf, hy⟩
    rw [SetLike.mem_coe, Submodule.mem_colon]
    intro p hp
    rw [Ideal.span_singleton_pow, SetLike.mem_coe, Ideal.mem_span_singleton'] at hp
    obtain ⟨c, rfl⟩ := hp
    rw [smul_eq_mul, show y * (c * x ^ ν) = c * (x ^ ν * y) by ring, hy]
    exact Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _ hf)
  · intro y hy
    have h1 : y * x ^ ν ∈ J.map t.toRing := by
      have := Submodule.mem_colon.mp hy (x ^ ν)
        (by rw [Ideal.span_singleton_pow]; exact Ideal.mem_span_singleton_self _)
      simpa [smul_eq_mul] using this
    have h2 : J.map t.toRing ≤ Ideal.span {x ^ ν} * t.divIdeal x ν J := by
      rw [Ideal.map_le_iff_le_comap]
      intro f hf
      obtain ⟨c, hc⟩ := MonoidalTransform.exists_toRing_eq_pow_mul_of_mem_pow t hx (hJ hf)
      rw [Ideal.mem_comap, hc]
      exact Ideal.mul_mem_mul (Ideal.mem_span_singleton_self _)
        (Ideal.subset_span ⟨f, hf, hc.symm⟩)
    obtain ⟨d, hd, hdy⟩ := Ideal.mem_span_singleton_mul.mp (h2 h1)
    have hx0 : x ^ ν ≠ 0 := pow_ne_zero ν (MonoidalTransform.ne_zero_of_span_eq_map t hx)
    have : d = y := mul_left_cancel₀ hx0 (by rw [hdy, mul_comm])
    rwa [← this]

/-- The weak transform as a union of colon ideals: `J' = ⋃_{J ⊆ Pᵛ} (JR' : xᵛR')`. -/
theorem MonoidalTransform.weakTransformIdeal_eq_iSup_colon (J : Ideal R) :
    weakTransformIdeal t J = ⨆ (ν : ℕ) (_ : J ≤ P ^ ν),
      (J.map t.toRing).colon ((Ideal.span {t.xR} ^ ν : Ideal _) : Set t.ring) := by
  rw [t.weakTransformIdeal_eq_iSup J t.span_xR_eq_map]
  exact iSup_congr fun ν => iSup_congr fun hν => t.divIdeal_eq_colon J t.span_xR_eq_map hν

/-- The strict transform as the union of the weak transforms of the `J ∩ Pᵛ` (Remark 3). -/
theorem MonoidalTransform.iSup_weakTransformIdeal_inf_pow (J : Ideal R) :
    ⨆ ν : ℕ, weakTransformIdeal t (J ⊓ P ^ ν) = strictTransformIdeal t J := by
  rw [t.strictTransformIdeal_eq_iSup J t.span_xR_eq_map]
  apply le_antisymm
  · refine iSup_le fun ν => ?_
    rw [t.weakTransformIdeal_eq_iSup _ t.span_xR_eq_map]
    refine iSup₂_le fun μ hμ => ?_
    refine le_trans (t.divIdeal_mono _ μ (le_inf inf_le_left hμ)) ?_
    exact le_iSup (fun μ => t.divIdeal t.xR μ (J ⊓ P ^ μ)) μ
  · refine iSup_le fun ν => le_trans ?_ (le_iSup _ ν)
    rw [t.weakTransformIdeal_eq_iSup _ t.span_xR_eq_map]
    exact le_iSup₂_of_le ν inf_le_right le_rfl

/-- The weak transforms of the `J ∩ Pᵛ` increase with `ν` (Remark 3). -/
theorem MonoidalTransform.monotone_weakTransformIdeal_inf_pow (J : Ideal R) :
    Monotone fun ν : ℕ => weakTransformIdeal t (J ⊓ P ^ ν) := by
  intro ν ν' hνν'
  simp only
  rw [t.weakTransformIdeal_eq_iSup _ t.span_xR_eq_map,
    t.weakTransformIdeal_eq_iSup _ t.span_xR_eq_map]
  refine iSup₂_le fun μ hμ => ?_
  have hμ' : J ⊓ P ^ ν' ≤ P ^ max μ ν' := by
    intro f hf
    rcases le_total μ ν' with h | h
    · rw [max_eq_right h]; exact hf.2
    · rw [max_eq_left h]; exact hμ ⟨hf.1, Ideal.pow_le_pow_right hνν' hf.2⟩
  refine le_iSup₂_of_le (max μ ν') hμ' ?_
  rw [MonoidalTransform.divIdeal, Ideal.span_le]
  rintro y ⟨f, hf, hy⟩
  refine Ideal.subset_span ⟨t.x ^ (max μ ν' - μ) * f, ⟨J.mul_mem_left _ hf.1, ?_⟩, ?_⟩
  · have hfμ : f ∈ P ^ μ := hμ hf
    rcases le_total μ ν' with h | h
    · have := Ideal.mul_mem_mul (Ideal.pow_mem_pow t.x_mem (max μ ν' - μ)) hfμ
      rw [← pow_add, Nat.sub_add_cancel (le_max_left μ ν')] at this
      rw [max_eq_right h] at this ⊢
      exact this
    · have := Ideal.mul_mem_mul (Ideal.pow_mem_pow t.x_mem (max μ ν' - μ)) hfμ
      rw [← pow_add, Nat.sub_add_cancel (le_max_left μ ν')] at this
      exact Ideal.pow_le_pow_right (le_max_right μ ν') this
  · rw [map_mul, map_pow, ← hy, ← MonoidalTransform.xR, ← mul_assoc, ← pow_add,
      Nat.sub_add_cancel (le_max_left μ ν')]

/-- If `w xⁿ ∈ IR'`, then `w` lies in the strict transform of `I` (the strict transform is
`x`-saturated). -/
theorem MonoidalTransform.mem_strictTransformIdeal_of_mul_pow_mem (t : MonoidalTransform R P)
    (hP : P.IsPrime) (hS : IsRegularLocalRing (R ⧸ P)) (I : Ideal R) {w : t.ring} {n : ℕ}
    (hw : w * t.xR ^ n ∈ I.map t.toRing) : w ∈ strictTransformIdeal t I := by
  obtain ⟨u, hu, m, F, hF, hwF⟩ := MonoidalTransform.exists_mul_eq_of_mem_map t I hw
  have hFP : F ∈ P ^ (n + m) := by
    refine t.mem_pow_of_toRing_mem hP hS ?_
    rw [← hwF, Ideal.span_singleton_pow, Ideal.mem_span_singleton']
    exact ⟨w * algebraMap _ t.ring u, by ring⟩
  have hunit : IsUnit (algebraMap _ t.ring u) :=
    IsLocalization.map_units t.ring (⟨u, hu⟩ : t.M'.primeCompl)
  have hmem : w * algebraMap _ t.ring u ∈ strictTransformIdeal t I := by
    have hFI' : F ∈ I := Ideal.mul_le_left (I := I) (J := P ^ m) hF
    have hFI : F ∈ I ⊓ P ^ (n + m) := Ideal.mem_inf.mpr ⟨hFI', hFP⟩
    have hgen : w * algebraMap _ t.ring u ∈ t.divIdeal t.xR (n + m) (I ⊓ P ^ (n + m)) := by
      refine Ideal.subset_span ⟨F, hFI, ?_⟩
      rw [← hwF]
      ring
    rw [t.strictTransformIdeal_eq_iSup I t.span_xR_eq_map]
    exact Ideal.mem_iSup_of_mem (n + m) hgen
  obtain ⟨v, hv⟩ := hunit.exists_right_inv
  have : w = w * algebraMap _ t.ring u * v := by rw [mul_assoc, hv, mul_one]
  rw [this]
  exact Ideal.mul_mem_right _ _ hmem

/-- The strict transform is the saturation of `IR'` with respect to `x`:
`I' = ⋃ₙ (IR' : xⁿR')`, both for a prime center with regular quotient and for `P = R`. -/
theorem MonoidalTransform.strictTransformIdeal_eq_iSup_colon (t : MonoidalTransform R P)
    (hP : (P.IsPrime ∧ IsRegularLocalRing (R ⧸ P)) ∨ P = ⊤) (I : Ideal R) :
    strictTransformIdeal t I = ⨆ n : ℕ,
      (I.map t.toRing).colon ((Ideal.span {t.xR} ^ n : Ideal _) : Set t.ring) := by
  have hdiv : ∀ ν : ℕ, t.divIdeal t.xR ν (I ⊓ P ^ ν) =
      ((I ⊓ P ^ ν).map t.toRing).colon ((Ideal.span {t.xR} ^ ν : Ideal _) : Set t.ring) :=
    fun ν => t.divIdeal_eq_colon _ t.span_xR_eq_map inf_le_right
  rw [t.strictTransformIdeal_eq_iSup I t.span_xR_eq_map]
  simp only [hdiv]
  rcases hP with ⟨hP, hS⟩ | hP
  · apply le_antisymm
    · exact iSup_mono fun ν => Submodule.colon_mono (Ideal.map_mono inf_le_left) le_rfl
    · refine iSup_le fun n w hw => ?_
      have hw' : w * t.xR ^ n ∈ I.map t.toRing := by
        have := Submodule.mem_colon.mp hw (t.xR ^ n)
          (by rw [Ideal.span_singleton_pow]; exact Ideal.mem_span_singleton_self _)
        simpa [smul_eq_mul] using this
      have := t.mem_strictTransformIdeal_of_mul_pow_mem hP hS I hw'
      rwa [t.strictTransformIdeal_eq_iSup I t.span_xR_eq_map, show (fun ν =>
        t.divIdeal t.xR ν (I ⊓ P ^ ν)) = fun ν => ((I ⊓ P ^ ν).map t.toRing).colon
          ((Ideal.span {t.xR} ^ ν : Ideal _) : Set t.ring) from funext hdiv] at this
  · subst hP
    simp only [Ideal.top_pow, inf_top_eq]

/-- Remark 1 (p. 214): "Let us take an element `x ∈ R'` such that `(x)R' = PR'`. Then the strict
transform `J'` of `J` in `R'` is the increasing union of the ideals `x⁻ᵛ(J ∩ Pᵛ)R'` for all
non-negative integers `ν`. Since `R'` is noetherian, we have `J' = x⁻ᵛ(J ∩ Pᵛ)R'` for all
sufficiently large `ν`. On the other hand, the weak transform `J'` of `J` in `R'` is the union of
the ideals `x⁻ᵛ J R'` for all non-negative integers `ν` such that `Pᵛ ⊇ J`. In particular, if
`J ≠ (0)R` and `P ≠ R`, then we have an integer `ν_P(J) = min_{f ∈ J} {ν_P(f)}` and
`J' = x⁻ᵛ J R'` with `ν = ν_P(J)`" (the last `J'` being the weak transform). -/
@[blueprint "rem:III.2-1"
  (statement := /-- Let $R$, $P$, $J$, $R'$ be as in \cref{def:III.5-strict} and $x\in R'$ with
    $(x)R'=PR'$. Then the strict transform $J'$ of $J$ in $R'$ is the increasing union of the
    ideals $x^{-\nu}(J\cap P^\nu)R'$ for all non-negative integers $\nu$, and, $R'$ being
    noetherian, $J'=x^{-\nu}(J\cap P^\nu)R'$ for all sufficiently large $\nu$. The weak
    transform of $J$ in $R'$ (\cref{def:III.5-weak}) is the union of the ideals $x^{-\nu}JR'$
    for all non-negative integers $\nu$ with $P^\nu\supseteq J$. In particular, if $J\ne(0)$
    and $P\ne R$, then $\nu_P(J)=\min_{f\in J}\nu_P(f)$ is an integer and the weak transform is
    $x^{-\nu}JR'$ with $\nu=\nu_P(J)$. (Remark 1, p.~214.)

    Remark~0 (p.~213), which precedes this remark, claims that ``a simple example shows'' that
    one and the same local ring $R'$ can be a monoidal transform of $R$ with two different
    centers $P$ and $Q$, the transforms of $J$ with respect to $P$ and $Q$ being possibly
    different; this is \cref{rem:III.2-0}. -/)
  (proof := /-- Immediate from \cref{def:III.5-strict}, \cref{def:III.5-weak} (any two
    generators $x$ of $PR'$ differ by a unit of $R'$, and $\nu_P(f)\ge\nu$ iff $f\in P^\nu$)
    and the noetherianity of $R'$ (an increasing union of ideals stabilizes). -/)
  (latexEnv := "remark")]
theorem MonoidalTransform.divIdeal_monotone_and_strictTransformIdeal_eq_iSup (hP : P.IsPrime) (hS : IsRegularLocalRing (R ⧸ P))
    (J : Ideal R) (x : t.ring) (hx : Ideal.span {x} = P.map t.toRing) :
    Monotone (fun ν : ℕ => t.divIdeal x ν (J ⊓ P ^ ν)) ∧
    strictTransformIdeal t J = ⨆ ν : ℕ, t.divIdeal x ν (J ⊓ P ^ ν) ∧
    (∃ N : ℕ, ∀ ν ≥ N, strictTransformIdeal t J = t.divIdeal x ν (J ⊓ P ^ ν)) ∧
    weakTransformIdeal t J = ⨆ (ν : ℕ) (_ : J ≤ P ^ ν), t.divIdeal x ν J ∧
    (J ≠ ⊥ → P ≠ ⊤ → ∃ ν : ℕ, Ideal.ord P J = ν ∧
      (ν : ℕ∞) = ⨅ f ∈ J, Ideal.ordElem P f ∧ weakTransformIdeal t J = t.divIdeal x ν J) := by
  -- (the hypotheses that `P` is prime and `R/P` regular are not needed)
  have _ := hP
  have _ := hS
  -- monotonicity
  have hmono : Monotone (fun ν : ℕ => t.divIdeal x ν (J ⊓ P ^ ν)) := by
    intro ν μ hνμ
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hνμ
    simp only
    rw [MonoidalTransform.divIdeal, Ideal.span_le]
    rintro y ⟨f, hf, hy⟩
    obtain ⟨u, hu⟩ := Ideal.span_singleton_eq_span_singleton.mp (hx.trans t.span_xR_eq_map.symm)
    have h : ↑u ^ k * y ∈ t.divIdeal x (ν + k) (J ⊓ P ^ (ν + k)) := by
      refine Ideal.subset_span ⟨t.x ^ k * f, ⟨J.mul_mem_left _ hf.1, ?_⟩, ?_⟩
      · rw [pow_add, mul_comm (P ^ ν)]
        exact Ideal.mul_mem_mul (Ideal.pow_mem_pow t.x_mem k) hf.2
      · rw [map_mul, map_pow, ← hy, ← MonoidalTransform.xR, ← hu]
        ring
    have hyu : y = ↑(u⁻¹) ^ k * (↑u ^ k * y) := by
      rw [← mul_assoc, ← mul_pow, Units.inv_mul, one_pow, one_mul]
    rw [SetLike.mem_coe, hyu]
    exact Ideal.mul_mem_left _ _ h
  have hsup := MonoidalTransform.strictTransformIdeal_eq_iSup_of_span_eq t J hx
  -- the weak transform
  have hweak := t.weakTransformIdeal_eq_iSup J hx
  refine ⟨hmono, hsup, ?_, hweak, ?_⟩
  · -- stabilization, `R'` being noetherian
    have := MonoidalTransform.isNoetherianRing t
    obtain ⟨N, hN⟩ := monotone_stabilizes_iff_noetherian.mpr inferInstance
      (⟨fun ν : ℕ => t.divIdeal x ν (J ⊓ P ^ ν), hmono⟩ : ℕ →o Ideal t.ring)
    refine ⟨N, fun ν hν => ?_⟩
    rw [hsup]
    refine le_antisymm (iSup_le fun μ => ?_) (le_iSup (fun ν : ℕ =>
      t.divIdeal x ν (J ⊓ P ^ ν)) ν)
    have h1 := hN (max μ ν) (le_max_of_le_right hν)
    have h2 := hN ν hν
    simp only [OrderHom.coe_mk] at h1 h2
    calc t.divIdeal x μ (J ⊓ P ^ μ) ≤ t.divIdeal x (max μ ν) (J ⊓ P ^ max μ ν) :=
          hmono (le_max_left μ ν)
      _ = t.divIdeal x ν (J ⊓ P ^ ν) := h1.symm.trans h2
  · -- `ν_P(J)` is finite and the weak transform is `x⁻ᵛ J R'`
    intro hJ hPt
    have hne : Ideal.ord P J ≠ ⊤ := by
      intro htop
      obtain ⟨f, hfJ, hf0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hJ
      refine hf0 ((Ideal.ordElem_eq_top_iff_eq_zero hPt).mp ?_)
      exact Ideal.ordElem_eq_top_iff.mpr fun n =>
        Ideal.le_pow_of_le_ord (htop ▸ le_top) hfJ
    set ν := (Ideal.ord P J).toNat with hνdef
    have hord : Ideal.ord P J = ν := (ENat.natCast_toNat hne).symm
    have hJν : J ≤ P ^ ν := Ideal.le_pow_of_le_ord hord.ge
    have hJν1 : ¬ J ≤ P ^ (ν + 1) := fun h => by
      have := (Ideal.le_ord h).trans hord.le
      rw [Nat.cast_le] at this
      omega
    obtain ⟨f₀, hf₀J, hf₀⟩ := Set.not_subset.mp hJν1
    refine ⟨ν, hord, le_antisymm (le_iInf₂ fun f hf => Ideal.le_ordElem (hJν hf))
      ((iInf₂_le f₀ hf₀J).trans (Ideal.ordElem_le_of_notMem hf₀)), ?_⟩
    rw [hweak]
    refine le_antisymm (iSup₂_le fun μ hμ => ?_) (le_iSup₂_of_le ν hJν le_rfl)
    have hμν : μ ≤ ν := by
      by_contra hlt
      exact hJν1 (hμ.trans (Ideal.pow_le_pow_right (by omega)))
    rw [MonoidalTransform.divIdeal, Ideal.span_le]
    rintro z ⟨f, hf, hz⟩
    obtain ⟨w, hw⟩ := MonoidalTransform.exists_toRing_eq_pow_mul_of_mem_pow t hx (hJν hf)
    have hwmem : w ∈ t.divIdeal x ν J := Ideal.subset_span ⟨f, hf, hw.symm⟩
    have hzw : z = x ^ (ν - μ) * w := by
      refine mul_left_cancel₀ (pow_ne_zero μ (MonoidalTransform.ne_zero_of_span_eq_map t hx)) ?_
      rw [hz, hw, ← mul_assoc, ← pow_add, Nat.add_sub_cancel' hμν]
    rw [SetLike.mem_coe, hzw]
    exact Ideal.mul_mem_left _ _ hwmem

end Remark1

/-! ### The local rings of a monoidal transformation with non-singular center

p. 214: "Let `y'` be any point of `X'`, `y = f(y')`, `R` the local ring of `X` at `y`, `R'` the
local ring of `X'` at `y'`, and `P` the ideal in `R` which defines the subscheme `B` of `X`. Then
we see that `R'` is a monoidal transform of `R` with center `P`."  The monoidal transform is
provided by the chart description of `X'` (`MonoidalTransformation.exists_monoidalTransform_stalk`,
`Hironaka/Compat/BlowupCharts.lean`); here are its consequences for non-singular `X` and `B`, used
in Remark 2 and in Ch. 0 (`lem:monoidal-transformation-nonsingular`). -/

/-- At a point `x` of a non-singular subscheme `D`, `O_{X,x}/D_x ≅ O_{D,x}` is regular. -/
theorem Subscheme.isRegularLocalRing_quotient_of_isNonsingular {X : Scheme.{u}} {D : Subscheme X}
    (hD : D.IsNonsingular) {x : X} (hx : x ∈ D.pts) :
    IsRegularLocalRing (X.presheaf.stalk x ⧸ D.stalkIdeal x) := by
  have hx' : x ∈ Set.range D.ι := by
    rw [Scheme.IdealSheafData.range_subschemeι]
    exact hx
  obtain ⟨z, rfl⟩ := hx'
  obtain ⟨e⟩ := nonempty_stalk_quot_equiv D z
  have : IsRegularLocalRing (D.toScheme.presheaf.stalk z) := hD z
  exact IsRegularLocalRing.of_ringEquiv e.symm

/-- At a point `x` of a non-singular subscheme `D`, the ideal `P = D_x` is prime and `R/P` is
regular: the hypotheses of p. 209 on the center of a monoidal transform. -/
theorem Subscheme.isPrime_stalkIdeal_of_isNonsingular {X : Scheme.{u}} {D : Subscheme X}
    (hD : D.IsNonsingular) {x : X} (hx : x ∈ D.pts) : (D.stalkIdeal x).IsPrime := by
  have := Subscheme.isRegularLocalRing_quotient_of_isNonsingular hD hx
  have := isDomain_of_isRegularLocalRing (X.presheaf.stalk x ⧸ D.stalkIdeal x)
  exact (Ideal.Quotient.isDomain_iff_prime _).mp this

/-- Membership in the prime of a point of an affine open. -/
theorem Subscheme.mem_primeIdealOf_iff {X : Scheme.{u}} {W : X.Opens} (hW : IsAffineOpen W)
    {z : X} (hz : z ∈ W) (f : Γ(X, W)) :
    f ∈ (hW.primeIdealOf ⟨z, hz⟩).asIdeal ↔ z ∉ X.basicOpen f := by
  let := TopCat.Presheaf.algebra_section_stalk X.presheaf (⟨z, hz⟩ : W)
  have := hW.isLocalization_stalk ⟨z, hz⟩
  rw [← IsLocalization.AtPrime.to_map_mem_maximal_iff (X.presheaf.stalk z) _ f,
    IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, Scheme.mem_basicOpen _ _ _ hz]
  rfl

/-- p. 214 (Remark 2): if `ξ` is the generic point of the non-singular subscheme `B` of the
non-singular scheme `X` and `x ∈ B`, then `ν ≤ ν(J_ξ)` iff `J_x ⊆ P_xᵛ`, `P_x = B_x`: the order
of `J` at the generic point of `B` is the `P`-adic order of `J_x`, the powers of `P_x` being
`P_x`-primary. -/
theorem Subscheme.le_nu_generic_iff {X : Scheme.{u}} (hX : X.IsNonsingular) {B : Subscheme X}
    (hB : B.IsNonsingular) {ξ : X} (hξ : IsGenericPoint ξ B.pts) {x : X} (hx : x ∈ B.pts)
    (J : Subscheme X) (ν : ℕ) :
    (ν : ℕ∞) ≤ Ideal.nu (J.stalkIdeal ξ) ↔ J.stalkIdeal x ≤ B.stalkIdeal x ^ ν := by
  have hsp : ξ ⤳ x := hξ.specializes hx
  have hξB : ξ ∈ B.pts := hξ.mem
  obtain ⟨W, hxW⟩ := Subscheme.exists_affineOpen_mem x
  have hξW : ξ ∈ (W : X.Opens) := hsp.mem_open W.1.isOpen hxW
  let _ : Algebra Γ(X, W) (X.presheaf.stalk x) :=
    TopCat.Presheaf.algebra_section_stalk X.presheaf (⟨x, hxW⟩ : (W : X.Opens))
  let _ : Algebra Γ(X, W) (X.presheaf.stalk ξ) :=
    TopCat.Presheaf.algebra_section_stalk X.presheaf (⟨ξ, hξW⟩ : (W : X.Opens))
  set px := (W.2.primeIdealOf ⟨x, hxW⟩).asIdeal with hpx
  set pξ := (W.2.primeIdealOf ⟨ξ, hξW⟩).asIdeal with hpξ
  have hlx : IsLocalization.AtPrime (X.presheaf.stalk x) px := W.2.isLocalization_stalk ⟨x, hxW⟩
  have hlξ : IsLocalization.AtPrime (X.presheaf.stalk ξ) pξ := W.2.isLocalization_stalk ⟨ξ, hξW⟩
  have : IsRegularLocalRing (X.presheaf.stalk x) := hX x
  have : IsRegularLocalRing (X.presheaf.stalk ξ) := hX ξ
  have hP := Subscheme.isPrime_stalkIdeal_of_isNonsingular hB hx
  have hS := Subscheme.isRegularLocalRing_quotient_of_isNonsingular hB hx
  set b := B.ideal W
  set j := J.ideal W
  have hBx : B.stalkIdeal x = b.map (algebraMap Γ(X, W) (X.presheaf.stalk x)) :=
    Subscheme.stalkIdeal_eq_map_germ_affine B W hxW
  have hJx : J.stalkIdeal x = j.map (algebraMap Γ(X, W) (X.presheaf.stalk x)) :=
    Subscheme.stalkIdeal_eq_map_germ_affine J W hxW
  have hJξ : J.stalkIdeal ξ = j.map (algebraMap Γ(X, W) (X.presheaf.stalk ξ)) :=
    Subscheme.stalkIdeal_eq_map_germ_affine J W hξW
  -- `b ⊆ pξ ⊆ px`
  have hbξ : b ≤ pξ := by
    intro f hf
    have := (Scheme.IdealSheafData.mem_support_iff_of_mem hξW).mp hξB
    rw [Scheme.mem_zeroLocus_iff] at this
    exact (Subscheme.mem_primeIdealOf_iff W.2 hξW f).mpr (this f hf)
  have hξx : pξ ≤ px := by
    intro f hf
    have h1 := (Subscheme.mem_primeIdealOf_iff W.2 hξW f).mp hf
    exact (Subscheme.mem_primeIdealOf_iff W.2 hxW f).mpr fun h =>
      h1 (hsp.mem_open (X.basicOpen f).isOpen h)
  -- `qx = B_x ∩ Γ(W)` is `pξ`
  set qx := (B.stalkIdeal x).comap (algebraMap Γ(X, W) (X.presheaf.stalk x)) with hqx
  have hqprime : qx.IsPrime := Ideal.IsPrime.comap _
  have hbq : b ≤ qx := by rw [hqx, hBx]; exact Ideal.le_comap_map
  have hqξ : pξ ≤ qx := by
    set z := W.2.fromSpec ⟨qx, hqprime⟩
    have hzW : z ∈ (W : X.Opens) := by
      rw [← SetLike.mem_coe, ← W.2.range_fromSpec]; exact ⟨_, rfl⟩
    have hzB : z ∈ B.pts := by
      refine (Scheme.IdealSheafData.mem_support_iff_of_mem hzW).mpr ?_
      rw [Scheme.mem_zeroLocus_iff]
      intro f hf hzf
      have h2 : (⟨qx, hqprime⟩ : PrimeSpectrum Γ(X, W)) ∈ PrimeSpectrum.basicOpen f := by
        rw [← W.2.fromSpec_preimage_basicOpen]
        exact hzf
      exact h2 (hbq hf)
    have h1 : ξ ⤳ z := hξ.specializes hzB
    have h1' : W.2.fromSpec (W.2.primeIdealOf ⟨ξ, hξW⟩) ⤳ z := by
      rw [W.2.fromSpec_primeIdealOf]
      exact h1
    have hWa : IsAffineOpen (W : X.Opens) := W.2
    have h2 : (W.2.primeIdealOf ⟨ξ, hξW⟩) ⤳ (⟨qx, hqprime⟩ : PrimeSpectrum Γ(X, W)) :=
      (hWa.fromSpec.isOpenEmbedding.isInducing.specializes_iff).mp h1'
    exact (PrimeSpectrum.le_iff_specializes _ _).mpr h2
  have hdisj : Disjoint (px.primeCompl : Set Γ(X, W)) (pξ : Set Γ(X, W)) := by
    rw [Set.disjoint_left]
    intro f hf hfξ
    exact hf (hξx hfξ)
  have hqξ' : qx ≤ pξ := by
    have h1 : B.stalkIdeal x ≤ pξ.map (algebraMap Γ(X, W) (X.presheaf.stalk x)) := by
      rw [hBx]; exact Ideal.map_mono hbξ
    have h3 : Ideal.comap (algebraMap Γ(X, W) (X.presheaf.stalk x))
        (pξ.map (algebraMap Γ(X, W) (X.presheaf.stalk x))) = pξ :=
      IsLocalization.under_map_of_isPrime_disjoint px.primeCompl _ inferInstance hdisj
    exact (Ideal.comap_mono h1).trans h3.le
  have hqeq : qx = pξ := le_antisymm hqξ' hqξ
  have hBx' : B.stalkIdeal x = pξ.map (algebraMap Γ(X, W) (X.presheaf.stalk x)) := by
    rw [← hqeq, hqx]
    exact (IsLocalization.map_under px.primeCompl _ _).symm
  -- the two contractions of `pξᵛ` agree
  have hC : ((pξ ^ ν).map (algebraMap Γ(X, W) (X.presheaf.stalk ξ))).comap
        (algebraMap Γ(X, W) (X.presheaf.stalk ξ)) =
      ((pξ ^ ν).map (algebraMap Γ(X, W) (X.presheaf.stalk x))).comap
        (algebraMap Γ(X, W) (X.presheaf.stalk x)) := by
    ext a
    rw [Ideal.mem_comap, Ideal.mem_comap,
      IsLocalization.algebraMap_mem_map_algebraMap_iff pξ.primeCompl,
      IsLocalization.algebraMap_mem_map_algebraMap_iff px.primeCompl]
    constructor
    · rintro ⟨s, hs, hsa⟩
      have h1 : algebraMap Γ(X, W) (X.presheaf.stalk x) s * algebraMap _ _ a ∈ B.stalkIdeal x ^ ν := by
        rw [hBx', ← Ideal.map_pow, ← map_mul]
        exact Ideal.mem_map_of_mem _ hsa
      have h2 : algebraMap Γ(X, W) (X.presheaf.stalk x) s ∉ B.stalkIdeal x := by
        intro h
        apply hs
        rw [← hqeq]
        exact h
      have h3 := mem_pow_of_mul_mem_pow_of_isRegularLocalRing_quotient (B.stalkIdeal x) hS ν _ _
        h2 h1
      rw [hBx', ← Ideal.map_pow] at h3
      exact (IsLocalization.algebraMap_mem_map_algebraMap_iff px.primeCompl
        (X.presheaf.stalk x) _ _).mp h3
    · rintro ⟨s, hs, hsa⟩
      exact ⟨s, fun h => hs (hξx h), hsa⟩
  rw [hJx, hBx', ← Ideal.map_pow, Ideal.map_le_iff_le_comap, ← hC, ← Ideal.map_le_iff_le_comap,
    ← hJξ, Ideal.map_pow, IsLocalization.AtPrime.map_eq_maximalIdeal]
  exact ⟨Ideal.le_pow_of_le_ord, Ideal.le_ord⟩

/-- Localization of colon ideals along ring isomorphisms. -/
theorem Ideal.map_colon_ringEquiv {A A' : Type*} [CommRing A] [CommRing A'] (e : A ≃+* A')
    (I K : Ideal A) :
    (I.colon (K : Set A)).map e = (I.map e).colon ((K.map e : Ideal A') : Set A') := by
  ext b
  rw [← Ideal.comap_symm, ← Ideal.comap_symm, ← Ideal.comap_symm, Ideal.mem_comap,
    Submodule.mem_colon, Submodule.mem_colon]
  constructor
  · intro h k hk
    rw [SetLike.mem_coe, Ideal.mem_comap] at hk
    rw [smul_eq_mul, Ideal.mem_comap, map_mul]
    exact h _ hk
  · intro h k hk
    have := h (e k) (by rw [SetLike.mem_coe, Ideal.mem_comap, e.symm_apply_apply]; exact hk)
    rw [smul_eq_mul, Ideal.mem_comap, map_mul, e.symm_apply_apply] at this
    exact this

namespace MonoidalTransformation

variable {X : Scheme.{u}} {B : Subscheme X} (t : MonoidalTransformation X B)

/-- The bridge at a point `y'` over `B`, with the exceptional ideal: `O_{X',y'}` is a monoidal
transform `R'` of `R = O_{X,f(y')}` with center `P = B_{f(y')}`, and the stalk of the ideal of
`E = f⁻¹(B)` is `PR' = xR'`. -/
theorem exists_monoidalTransform_stalk_exceptional (y : t.X')
    [IsRegularLocalRing (X.presheaf.stalk (t.f y))] [IsDomain (X.presheaf.stalk (t.f y))] :
    ∃ (s : MonoidalTransform (X.presheaf.stalk (t.f y)) (B.stalkIdeal (t.f y)))
      (e : s.ring ≃+* t.X'.presheaf.stalk y),
      e.toRingHom.comp s.toRing = (t.f.stalkMap y).hom ∧
      t.exceptional.stalkIdeal y = Ideal.span {e s.xR} := by
  obtain ⟨s, e, he⟩ := t.exists_monoidalTransform_stalk y
  refine ⟨s, e, he, ?_⟩
  rw [exceptional, t.stalkIdeal_totalTransform_eq_map y s e he, ← s.span_xR_eq_map,
    Ideal.map_span, Set.image_singleton]

/-- If `f(y') ∉ B` then `f(y')` has no point of `E = f⁻¹(B)` over it, i.e. `E ⊆ f⁻¹(B)` on
points. -/
theorem mem_pts_of_mem_exceptional {y : t.X'} (hy : y ∈ t.exceptional.pts) : t.f y ∈ B.pts := by
  by_contra h
  apply Subscheme.mem_pts_iff_stalkIdeal_ne_top.mp hy
  rw [exceptional, stalkIdeal_totalTransform, Subscheme.stalkIdeal_eq_top_of_notMem_pts h,
    Ideal.map_top]

/-- p. 209, applied to the local rings of `X'`: if `X` and `B` are non-singular, every local ring
of `X'` is regular. -/
theorem isRegularLocalRing_stalk (hX : X.IsNonsingular) (hB : B.IsNonsingular) (y : t.X') :
    IsRegularLocalRing (t.X'.presheaf.stalk y) := by
  have : IsRegularLocalRing (X.presheaf.stalk (t.f y)) := hX _
  have := Transforms.isDomain_of_isRegularLocalRing (X.presheaf.stalk (t.f y))
  by_cases hy : t.f y ∈ B.pts
  · have hP := Subscheme.isPrime_stalkIdeal_of_isNonsingular hB hy
    have hS := Subscheme.isRegularLocalRing_quotient_of_isNonsingular hB hy
    obtain ⟨s, e, -⟩ := t.exists_monoidalTransform_stalk y
    have hP0 : B.stalkIdeal (t.f y) ≠ ⊥ := fun h =>
      s.x_ne_zero ((Submodule.mem_bot _).mp (le_of_eq h s.x_mem))
    have := (s.isRegularLocalRing_and_isLocalHom_and_span_xR_eq_map hP hP0 hS).1
    exact IsRegularLocalRing.of_ringEquiv e
  · exact IsRegularLocalRing.of_ringEquiv
      (RingEquiv.ofBijective (t.f.stalkMap y).hom (t.bijective_stalkMap_of_notMem y hy))

/-- p. 210: at a point of `E = f⁻¹(B)`, `O_{E,y'} = R'/xR'` is regular. -/
theorem isRegularLocalRing_quotient_exceptional (hX : X.IsNonsingular) (hB : B.IsNonsingular)
    {y : t.X'} (hy : y ∈ t.exceptional.pts) :
    IsRegularLocalRing (t.X'.presheaf.stalk y ⧸ t.exceptional.stalkIdeal y) := by
  have : IsRegularLocalRing (X.presheaf.stalk (t.f y)) := hX _
  have := Transforms.isDomain_of_isRegularLocalRing (X.presheaf.stalk (t.f y))
  have hfy := t.mem_pts_of_mem_exceptional hy
  have hP := Subscheme.isPrime_stalkIdeal_of_isNonsingular hB hfy
  have hS := Subscheme.isRegularLocalRing_quotient_of_isNonsingular hB hfy
  obtain ⟨s, e, -, hE⟩ := t.exists_monoidalTransform_stalk_exceptional y
  have := s.isRegularLocalRing_quotient_span_xR hP hS
  rw [hE]
  refine IsRegularLocalRing.of_ringEquiv
    (Ideal.quotientEquiv (Ideal.span {s.xR}) (Ideal.span {e s.xR}) e ?_)
  rw [Ideal.map_span, Set.image_singleton]
  rfl

/-- If `X` and `B` are non-singular, then so are `X'` and `f⁻¹(B)` (p. 142, p. 167, p. 214). -/
theorem isNonsingular_of_isNonsingular (hX : X.IsNonsingular) (hB : B.IsNonsingular) :
    t.X'.IsNonsingular ∧ t.exceptional.IsNonsingular := by
  refine ⟨fun y => t.isRegularLocalRing_stalk hX hB y, fun z => ?_⟩
  have hz : t.exceptional.ι z ∈ t.exceptional.pts := by
    show _ ∈ (t.exceptional.support : Set t.X')
    rw [← Scheme.IdealSheafData.range_subschemeι]
    exact ⟨z, rfl⟩
  have := t.isRegularLocalRing_quotient_exceptional hX hB hz
  obtain ⟨e⟩ := nonempty_stalk_quot_equiv t.exceptional z
  exact IsRegularLocalRing.of_ringEquiv e

/-- Remark 2, p. 214: "The total pre-image `E = f⁻¹(B)` is a non-singular subscheme of `X'` of
codimension 1": at every point of `E`, its ideal `xR'` is a principal ideal of height one. -/
theorem exceptional_isEverywhereOfCodim_one (hX : X.IsNonsingular) (hB : B.IsNonsingular) :
    t.exceptional.IsEverywhereOfCodim 1 := by
  intro y hy
  have : IsRegularLocalRing (X.presheaf.stalk (t.f y)) := hX _
  have := Transforms.isDomain_of_isRegularLocalRing (X.presheaf.stalk (t.f y))
  have := t.isRegularLocalRing_stalk hX hB y
  have := Transforms.isDomain_of_isRegularLocalRing (t.X'.presheaf.stalk y)
  obtain ⟨s, e, -, hE⟩ := t.exists_monoidalTransform_stalk_exceptional y
  have hg0 : e s.xR ≠ 0 := by
    rw [ne_eq, map_eq_zero_iff e e.injective]
    intro h
    exact s.x_ne_zero (s.toRing_injective (h.trans (map_zero _).symm))
  have hgu : ¬ IsUnit (e s.xR) := fun h =>
    Subscheme.mem_pts_iff_stalkIdeal_ne_top.mp hy (by rw [hE]; exact Ideal.span_singleton_eq_top.mpr h)
  rw [Subscheme.codimAt, hE]
  exact_mod_cast Ideal.height_span_singleton_eq_one_of_mem_nonZeroDivisors
    (mem_nonZeroDivisors_of_ne_zero hg0) hgu

end MonoidalTransformation

/-! ### Remarks 2, 3, 4 (pp. 214–215): weak and strict transforms of sheaves of ideals -/

namespace Subscheme

variable {X : Scheme.{u}} {B : Subscheme X}

theorem stalkIdeal_iSup_eq' {ι : Sort*} (K : ι → Subscheme X) (x : X) :
    (⨆ i, K i).stalkIdeal x = ⨆ i, (K i).stalkIdeal x := by
  rw [← sSup_range, stalkIdeal_sSup_eq, iSup_range]

/-- `f⁻¹(J)·P⁻ᵛ` increases with `ν`. -/
theorem divPow_mono (I P : Subscheme X) {ν₁ ν₂ : ℕ} (h : ν₁ ≤ ν₂) :
    divPow I P ν₁ ≤ divPow I P ν₂ := by
  apply sSup_le_sSup
  intro K hK z
  exact (Ideal.mul_mono_right (Ideal.pow_le_pow_right h)).trans (hK z)

/-- An irreducible subscheme has a generic point. -/
theorem exists_isGenericPoint (hB : B.IsIrreducible) : ∃ ξ, IsGenericPoint ξ B.pts := by
  have : IrreducibleSpace B.toScheme := hB
  have h1 : _root_.IsIrreducible (Set.univ : Set B.toScheme) :=
    IrreducibleSpace.isIrreducible_univ _
  have h2 : _root_.IsIrreducible B.pts := by
    have := h1.image B.ι B.ι.continuous.continuousOn
    rw [Set.image_univ, Scheme.IdealSheafData.range_subschemeι] at this
    exact this
  exact QuasiSober.sober h2 B.support.isClosed


theorem weakTransform_eq (t : MonoidalTransformation X B) (J : Subscheme X) {ξ : X}
    (hξ : IsGenericPoint ξ B.pts) :
    weakTransform t J = ⨆ (ν : ℕ) (_ : (ν : ℕ∞) ≤ Ideal.nu (J.stalkIdeal ξ)),
      divPow (totalTransform t.f J) t.exceptional ν := by
  have h : ∃ ξ, IsGenericPoint ξ B.pts := ⟨ξ, hξ⟩
  rw [weakTransform, dite_eq_left_of_eq_true (eq_true h)]
  have key : ∀ c : X, c = ξ → (⨆ (ν : ℕ) (_ : (ν : ℕ∞) ≤ Ideal.nu (J.stalkIdeal c)),
      divPow (totalTransform t.f J) t.exceptional ν) = ⨆ (ν : ℕ)
        (_ : (ν : ℕ∞) ≤ Ideal.nu (J.stalkIdeal ξ)),
      divPow (totalTransform t.f J) t.exceptional ν := by
    rintro c rfl; rfl
  exact key _ (IsGenericPoint.eq (Exists.choose_spec (of_eq_true (eq_true h))) hξ)

theorem stalkIdeal_weakTransform (t : MonoidalTransformation X B) (J : Subscheme X) {ξ : X}
    (hξ : IsGenericPoint ξ B.pts) (y : t.X') :
    (weakTransform t J).stalkIdeal y = ⨆ (ν : ℕ) (_ : (ν : ℕ∞) ≤ Ideal.nu (J.stalkIdeal ξ)),
      ((totalTransform t.f J).stalkIdeal y).colon
        ((t.exceptional.stalkIdeal y ^ ν : Ideal _) : Set (t.X'.presheaf.stalk y)) := by
  rw [weakTransform_eq t J hξ, stalkIdeal_iSup_eq']
  refine iSup_congr fun ν => ?_
  rw [stalkIdeal_iSup_eq']
  exact iSup_congr fun _ => stalkIdeal_divPow (P := t.exceptional) t.invertible ν y

/-- The colon ideals `(f⁻¹(J)_{y'} : E_{y'}ᵛ)` computed in the monoidal transform `R'`. -/
theorem stalkIdeal_colon_eq_map (t : MonoidalTransformation X B) (y : t.X')
    [IsRegularLocalRing (X.presheaf.stalk (t.f y))] [IsDomain (X.presheaf.stalk (t.f y))]
    (s : MonoidalTransform (X.presheaf.stalk (t.f y)) (B.stalkIdeal (t.f y)))
    (e : s.ring ≃+* t.X'.presheaf.stalk y) (he : e.toRingHom.comp s.toRing = (t.f.stalkMap y).hom)
    (J : Subscheme X) (ν : ℕ) :
    ((totalTransform t.f J).stalkIdeal y).colon
        ((t.exceptional.stalkIdeal y ^ ν : Ideal _) : Set (t.X'.presheaf.stalk y)) =
      (((J.stalkIdeal (t.f y)).map s.toRing).colon
        ((Ideal.span {s.xR} ^ ν : Ideal _) : Set s.ring)).map e := by
  have hE : t.exceptional.stalkIdeal y = (Ideal.span {s.xR}).map e := by
    rw [MonoidalTransformation.exceptional, t.stalkIdeal_totalTransform_eq_map y s e he,
      ← s.span_xR_eq_map]
  rw [t.stalkIdeal_totalTransform_eq_map y s e he, hE, Ideal.map_colon_ringEquiv, Ideal.map_pow]

/-- Remark 2, stalks: `J'_{y'}` is the weak transform of `J_y` in `R' = O_{X',y'}`. -/
theorem stalkIdeal_weakTransform_eq_map (hX : X.IsNonsingular) (hBns : B.IsNonsingular)
    (t : MonoidalTransformation X B) (J : Subscheme X) {ξ : X} (hξ : IsGenericPoint ξ B.pts)
    (y : t.X') [IsRegularLocalRing (X.presheaf.stalk (t.f y))]
    [IsDomain (X.presheaf.stalk (t.f y))]
    (s : MonoidalTransform (X.presheaf.stalk (t.f y)) (B.stalkIdeal (t.f y)))
    (e : s.ring ≃+* t.X'.presheaf.stalk y)
    (he : e.toRingHom.comp s.toRing = (t.f.stalkMap y).hom) :
    (weakTransform t J).stalkIdeal y = (weakTransformIdeal s (J.stalkIdeal (t.f y))).map e := by
  rw [stalkIdeal_weakTransform t J hξ y, s.weakTransformIdeal_eq_iSup_colon, Ideal.map_iSup]
  simp_rw [Ideal.map_iSup, stalkIdeal_colon_eq_map t y s e he J]
  by_cases hx : t.f y ∈ B.pts
  · exact iSup_congr fun ν =>
      iSup_congr_Prop (Subscheme.le_nu_generic_iff hX hBns hξ hx J ν) fun _ => rfl
  · have hPt : B.stalkIdeal (t.f y) = ⊤ := stalkIdeal_eq_top_of_notMem_pts hx
    have hx1 : Ideal.span {s.xR} = ⊤ := by
      rw [s.span_xR_eq_map, Ideal.eq_top_iff_one]
      have h1 : (1 : X.presheaf.stalk (t.f y)) ∈ B.stalkIdeal (t.f y) := hPt ▸ Submodule.mem_top
      simpa using Ideal.mem_map_of_mem s.toRing h1
    apply le_antisymm
    · refine iSup₂_le fun ν _ => le_iSup₂_of_le ν ?_ le_rfl
      rw [hPt, Ideal.top_pow]
      exact le_top
    · refine iSup₂_le fun ν _ => le_iSup₂_of_le 0 (by simp) ?_
      simp only [hx1, Ideal.top_pow, le_rfl]

/-- Remark 2: `f⁻¹(J) ⊆ P_Eᵛ` for `ν ≤ ν(J_ξ)`. -/
theorem totalTransform_le_exceptional_pow (hX : X.IsNonsingular) (hBns : B.IsNonsingular)
    (t : MonoidalTransformation X B) (J : Subscheme X) {ξ : X} (hξ : IsGenericPoint ξ B.pts)
    {ν : ℕ} (hν : (ν : ℕ∞) ≤ Ideal.nu (J.stalkIdeal ξ)) :
    totalTransform t.f J ≤ t.exceptional ^ ν := by
  rw [le_iff_stalkIdeal_le]
  intro y
  rw [stalkIdeal_pow_eq, MonoidalTransformation.exceptional, stalkIdeal_totalTransform,
    stalkIdeal_totalTransform, ← Ideal.map_pow]
  apply Ideal.map_mono
  by_cases hx : t.f y ∈ B.pts
  · exact (Subscheme.le_nu_generic_iff hX hBns hξ hx J ν).mp hν
  · rw [stalkIdeal_eq_top_of_notMem_pts hx, Ideal.top_pow]
    exact le_top

/-- Remark 2 (p. 214): "Let `X` be a non-singular algebraic scheme, `B` an irreducible
non-singular subscheme of `X` and `J` a coherent sheaf of ideals on `X`. Let `f : X' → X` be the
monoidal transformation of `X` with center `B`. The total pre-image `E = f⁻¹(B)` is a
non-singular subscheme of `X'` of codimension 1. Let `P_E` denote the sheaf of ideals on `X'`
which define `E`. Let `f⁻¹(J)` denote the sheaf of ideals on `X'` which are generated by the
ideals of `J`. Let `ξ` be the generic point of `B`; we assume that `B` is not empty. Then for
every non-negative integer `ν ≤ ν(J_ξ)`, `f⁻¹(J)` is contained in `P_Eᵛ`. Let `J'` be the sheaf
of ideals on `X'` which is the increasing union of `f⁻¹(J)·P_E⁻ᵛ` for all `ν ≤ ν(J_ξ)`. Then
`J'` is a coherent sheaf of ideals on `X'`. If `J_ξ` is not a zero ideal then `ν(J_ξ)` is a
non-negative integer and we have `J' = f⁻¹(J)·P_E⁻ᵛ` with `ν = ν(J_ξ)`. … Let `y'` be any point
of `X'`, `y = f(y')`, `R` the local ring of `X` at `y`, `R'` the local ring of `X'` at `y'`, and
`P` the ideal in `R` which defines the subscheme `B` of `X`. Then we see that `R'` is a monoidal
transform of `R` with center `P` and that `J'_{y'}` is the weak transform of `J_y` in `R'`."

Formalization note (encoding): coherence of `J'` is automatic for `Subscheme`s; "`R'` is a
monoidal transform of `R` with center `P`" is encoded as the existence of
`s : MonoidalTransform R P` and a ring isomorphism `s.ring ≃+* O_{X',y'}` compatible with the
stalk map of `f`, carrying `weakTransformIdeal s J_y` onto `J'_{y'}`; the domain hypothesis on
`O_{X,y}` comes from \cref{lem:III.2-regular-local-domain}.

Gap in the paper filled: the assertions "`E` is non-singular of codimension 1",
"`f⁻¹(J) ⊆ P_Eᵛ` for `ν ≤ ν(J_ξ)`" and "Then we see that `R'` is a monoidal transform … and
`J'_{y'}` is the weak transform of `J_y`" are proved; the key fact `ν(J_ξ) ≥ ν ⟺ J_y ⊆ Pᵛ`
(`Subscheme.le_nu_generic_iff`) uses that the powers of `P` are `P`-primary, `R/P` being
regular. -/
@[blueprint "rem:III.2-2"
  (statement := /-- Notation as in \cref{def:III.2-weak-transform-sheaf}. The total pre-image
    $E=f^{-1}(B)$ is a non-singular subscheme of $X'$ of codimension $1$. For every
    non-negative integer $\nu\le\nu(J_\xi)$, $f^{-1}(J)$ is contained in $P_E^\nu$, and the
    $f^{-1}(J)P_E^{-\nu}$, $\nu\le\nu(J_\xi)$, form an increasing family; the weak transform
    $J'$ is a coherent sheaf of ideals on $X'$. If $J_\xi$ is not a zero ideal then
    $\nu(J_\xi)$ is a non-negative integer and $J'=f^{-1}(J)P_E^{-\nu}$ with
    $\nu=\nu(J_\xi)$. Let $y'$ be any point of $X'$, $y=f(y')$, $R=\mathcal O_{X,y}$,
    $R'=\mathcal O_{X',y'}$, and $P$ the ideal in $R$ which defines $B$. Then $R'$ is a
    monoidal transform of $R$ with center $P$ and $J'_{y'}$ is the weak transform of $J_y$
    in $R'$ (\cref{def:III.5-weak}). (Remark 2, p.~214.) (Formalization note (encoding):
    ``$R'$ is a monoidal transform of $R$'' is the existence of monoidal-transform data with
    local ring isomorphic to $R'$ compatibly with $R\to R'$.) -/)
  (proof := /-- The paper gives no argument (``Then we see''); the intended one: locally $X=\operatorname{Spec}A$, $B=V(P)$ with $P=(x_1,\dots,x_r)$, and
    $X'$ is covered by the $\operatorname{Spec}A[x_2/x_i,\dots]$, on which $f^{-1}(B)$ is the
    divisor $x_i=0$, non-singular of codimension one (p.~167, Remark 1 of Ch.~I \S1, says only that $X'$ is non-singular
    when $X$ and $B$ are; the statement about $f^{-1}(B)$ is not there). The
    local ring of $X'$ at $y'$ is the localization of $A_y[x_2/x_1,\dots,x_r/x_1]$ at a prime
    containing the maximal ideal of $A_y$, i.e.\ a monoidal transform of $R$ with center $P$;
    $f^{-1}(J)_{y'}=J_yR'$, $(P_E)_{y'}=PR'=(x_1)R'$ and $\nu(J_\xi)=\nu_P(J_y)$, so the
    stalk of $J'$ is $\bigcup_{\nu\le\nu_P(J_y)}x_1^{-\nu}J_yR'$, the weak transform of
    $J_y$ by \cref{rem:III.2-1}.

    \textbf{Gap in the paper filled.} Lean proves these assertions: the chart description is
    \cref{compat:blowup-stalk-monoidal-transform}; $E$ is non-singular of codimension one
    since $\mathcal O_{E,y'}=R'/xR'$ is regular (\cref{lem:III.2-monoidal-transform-regular})
    and by Krull's principal ideal theorem; $\nu(J_\xi)=\nu_P(J_y)$ because
    $\mathcal O_{X,\xi}=R_P$ and $P^\nu$ is $P$-primary, $R/P$ being regular
    (\cref{lem:regular-quotient-primary-powers}); the stalks of $f^{-1}(J)P_E^{-\nu}$ are the
    colon ideals $(J_yR':x^\nu R')$, $P_E$ being invertible, and for $J_y\subseteq P^\nu$
    these are $x^{-\nu}J_yR'$. -/)
  (latexEnv := "remark")]
theorem _root_.Hironaka.MonoidalTransformation.exceptional_isNonsingular_and_totalTransform_le_pow (hX : X.IsNonsingular) (hB : B.IsIrreducible) (hBns : B.IsNonsingular)
    (t : MonoidalTransformation X B) (J : Subscheme X) :
    (t.exceptional.IsNonsingular ∧ t.exceptional.IsEverywhereOfCodim 1) ∧
    (∀ ξ : X, IsGenericPoint ξ B.pts → ∀ ν : ℕ, (ν : ℕ∞) ≤ Ideal.nu (J.stalkIdeal ξ) →
      totalTransform t.f J ≤ t.exceptional ^ ν) ∧
    (∀ ξ : X, IsGenericPoint ξ B.pts → ∀ ν₁ ν₂ : ℕ, ν₁ ≤ ν₂ →
      (ν₂ : ℕ∞) ≤ Ideal.nu (J.stalkIdeal ξ) →
        divPow (totalTransform t.f J) t.exceptional ν₁ ≤
          divPow (totalTransform t.f J) t.exceptional ν₂) ∧
    (∀ ξ : X, IsGenericPoint ξ B.pts → J.stalkIdeal ξ ≠ ⊥ →
      ∃ ν : ℕ, Ideal.nu (J.stalkIdeal ξ) = ν ∧
        weakTransform t J = divPow (totalTransform t.f J) t.exceptional ν) ∧
    (∀ y' : t.X',
      haveI : IsRegularLocalRing (X.presheaf.stalk (t.f.base y')) := hX _
      haveI : IsDomain (X.presheaf.stalk (t.f.base y')) :=
        Transforms.isDomain_of_isRegularLocalRing _
      ∃ (s : MonoidalTransform (X.presheaf.stalk (t.f.base y')) (B.stalkIdeal (t.f.base y')))
        (e : s.ring ≃+* t.X'.presheaf.stalk y'),
        e.toRingHom.comp s.toRing = (t.f.stalkMap y').hom ∧
        (weakTransformIdeal s (J.stalkIdeal (t.f.base y'))).map e =
          (weakTransform t J).stalkIdeal y') := by
  obtain ⟨ξ₀, hξ₀⟩ := exists_isGenericPoint hB
  refine ⟨⟨(t.isNonsingular_of_isNonsingular hX hBns).2,
    t.exceptional_isEverywhereOfCodim_one hX hBns⟩,
    fun ξ hξ ν hν => totalTransform_le_exceptional_pow hX hBns t J hξ hν,
    fun _ _ ν₁ ν₂ h _ => divPow_mono _ _ h, ?_, ?_⟩
  · intro ξ hξ hJ
    have : IsRegularLocalRing (X.presheaf.stalk ξ) := hX ξ
    have hne : Ideal.nu (J.stalkIdeal ξ) ≠ ⊤ := by
      intro htop
      apply hJ
      have h := ((Ideal.ord_basic _ (J.stalkIdeal ξ) ⊥ ⊥).1).mp htop
      rw [eq_bot_iff, ← Ideal.iInf_pow_eq_bot_of_isLocalRing (maximalIdeal _)
        (Ideal.IsMaximal.ne_top inferInstance)]
      exact le_iInf h
    refine ⟨(Ideal.nu (J.stalkIdeal ξ)).toNat, (ENat.natCast_toNat hne).symm, ?_⟩
    rw [weakTransform_eq t J hξ]
    apply le_antisymm
    · refine iSup₂_le fun ν hν => divPow_mono _ _ ?_
      rw [← ENat.natCast_toNat hne] at hν
      exact_mod_cast hν
    · exact le_iSup₂_of_le _ (ENat.natCast_toNat hne).le le_rfl
  · intro y'
    have : IsRegularLocalRing (X.presheaf.stalk (t.f y')) := hX _
    have := Transforms.isDomain_of_isRegularLocalRing (X.presheaf.stalk (t.f y'))
    obtain ⟨s, e, he⟩ := t.exists_monoidalTransform_stalk y'
    exact ⟨s, e, he, (stalkIdeal_weakTransform_eq_map hX hBns t J hξ₀ y' s e he).symm⟩

/-- The strict transform of a coherent sheaf of ideals by a monoidal transformation (Remark 3,
pp. 214–215): "Let `P_B` denote the sheaf of ideals on `X` which define the subscheme `B` of
`X`. Then for every non-negative integer `ν`, `J^{(ν)} = J ∩ P_Bᵛ` is a coherent sheaf of ideals
on `X`. Let `J'^{(ν)}` denote the weak transform of `J^{(ν)}` on `X'`. Then `{J'^{(ν)}}` is an
increasing sequence of coherent sheaves of ideals on `X'`. Therefore the union `J''` of these
`J'^{(ν)}` for all non-negative integers `ν` is a coherent sheaf of ideals on `X'`. This sheaf
of ideals `J''` on `X'` will be called the *strict transform* of `J` on `X'` by the monoidal
transformation `f`."  The intersection of ideal sheaves is the lattice meet `⊓` of
`Subscheme X`, and `P_Bᵛ` is the `ν`-th power of ideal sheaves. -/
@[blueprint "def:III.2-strict-transform-sheaf"
  (statement := /-- Let $X$, $B$, $J$, $f$ be as in \cref{def:III.2-weak-transform-sheaf} and
    $P_B$ the sheaf of ideals of $B$. For every non-negative integer $\nu$,
    $J^{(\nu)}=J\cap P_B^\nu$ is a coherent sheaf of ideals on $X$; let $J'^{(\nu)}$ be its
    weak transform on $X'$. The \emph{strict transform} of $J$ on $X'$ by $f$ is the union
    $J''$ of the $J'^{(\nu)}$ for all non-negative integers $\nu$. (Remark 3, pp.~214--215.) -/)
  (latexEnv := "definition")]
noncomputable def strictTransformIdealSheaf (t : MonoidalTransformation X B) (J : Subscheme X) :
    Subscheme t.X' :=
  ⨆ ν : ℕ, weakTransform t (J ⊓ B ^ ν)

/-- The stalks of the weak transforms of the `J ∩ P_Bᵛ` (Remark 3). -/
theorem stalkIdeal_weakTransform_inf_pow_eq_map (hX : X.IsNonsingular) (hBns : B.IsNonsingular)
    (t : MonoidalTransformation X B) (J : Subscheme X) {ξ : X} (hξ : IsGenericPoint ξ B.pts)
    (y : t.X') [IsRegularLocalRing (X.presheaf.stalk (t.f y))]
    [IsDomain (X.presheaf.stalk (t.f y))]
    (s : MonoidalTransform (X.presheaf.stalk (t.f y)) (B.stalkIdeal (t.f y)))
    (e : s.ring ≃+* t.X'.presheaf.stalk y)
    (he : e.toRingHom.comp s.toRing = (t.f.stalkMap y).hom) (ν : ℕ) :
    (weakTransform t (J ⊓ B ^ ν)).stalkIdeal y =
      (weakTransformIdeal s (J.stalkIdeal (t.f y) ⊓ B.stalkIdeal (t.f y) ^ ν)).map e := by
  rw [stalkIdeal_weakTransform_eq_map hX hBns t _ hξ y s e he, stalkIdeal_inf_eq,
    stalkIdeal_pow_eq]

/-- Remark 3, stalks: `J''_{y'}` is the strict transform of `J_y` in `R'`. -/
theorem stalkIdeal_strictTransformIdealSheaf_eq_map (hX : X.IsNonsingular)
    (hBns : B.IsNonsingular) (t : MonoidalTransformation X B) (J : Subscheme X) {ξ : X}
    (hξ : IsGenericPoint ξ B.pts) (y : t.X') [IsRegularLocalRing (X.presheaf.stalk (t.f y))]
    [IsDomain (X.presheaf.stalk (t.f y))]
    (s : MonoidalTransform (X.presheaf.stalk (t.f y)) (B.stalkIdeal (t.f y)))
    (e : s.ring ≃+* t.X'.presheaf.stalk y)
    (he : e.toRingHom.comp s.toRing = (t.f.stalkMap y).hom) :
    (strictTransformIdealSheaf t J).stalkIdeal y =
      (strictTransformIdeal s (J.stalkIdeal (t.f y))).map e := by
  rw [strictTransformIdealSheaf, stalkIdeal_iSup_eq']
  simp_rw [stalkIdeal_weakTransform_inf_pow_eq_map hX hBns t J hξ y s e he]
  rw [← Ideal.map_iSup, s.iSup_weakTransformIdeal_inf_pow]

/-- Remark 3 (pp. 214–215): "`{J'^{(ν)}}` is an increasing sequence of coherent sheaves of
ideals on `X'`. … Let `y'` be any point of `X'`, `y = f(y')`, `R` the local ring on `X` at `y`,
`R'` the local ring of `X'` at `y'`, and `P` the ideal in `R` which defines the subscheme `B` of
`X`. Then `J''_{y'}` is the strict transform of `J_y` in `R'`."  (Same encoding of "`R'` is a
monoidal transform of `R` with center `P`" as in \cref{rem:III.2-2}.) -/
@[blueprint "rem:III.2-3"
  (statement := /-- Notation as in \cref{def:III.2-strict-transform-sheaf}. The weak transforms
    $J'^{(\nu)}$ of $J^{(\nu)}=J\cap P_B^\nu$ form an increasing sequence of coherent sheaves
    of ideals on $X'$, so their union $J''$ is a coherent sheaf of ideals. Let $y'$ be any
    point of $X'$, $y=f(y')$, $R=\mathcal O_{X,y}$, $R'=\mathcal O_{X',y'}$, and $P$ the
    ideal in $R$ which defines $B$. Then $J''_{y'}$ is the strict transform of $J_y$ in $R'$
    (\cref{def:III.5-strict}). (Remark 3, pp.~214--215.) -/)
  (proof := /-- $J^{(\nu)}\subseteq J^{(\nu-1)}$ but $\nu(J^{(\nu)}_\xi)\ge\nu$, and
    $x^{-\nu}(J\cap P^\nu)R'\subseteq x^{-\nu-1}(J\cap P^{\nu+1})R'$ on stalks
    (\cref{rem:III.2-1}); the stalk statement is \cref{rem:III.2-2} applied to the
    $J^{(\nu)}$ together with the description of the strict transform as
    $\bigcup_\nu x^{-\nu}(J_y\cap P^\nu)R'$ in \cref{rem:III.2-1}. -/)
  (latexEnv := "remark")]
theorem _root_.Hironaka.MonoidalTransformation.monotone_weakTransform_inf_pow_and_exists_stalk_equiv (hX : X.IsNonsingular) (hB : B.IsIrreducible) (hBns : B.IsNonsingular)
    (t : MonoidalTransformation X B) (J : Subscheme X) :
    Monotone (fun ν : ℕ => weakTransform t (J ⊓ B ^ ν)) ∧
    (∀ y' : t.X',
      haveI : IsRegularLocalRing (X.presheaf.stalk (t.f.base y')) := hX _
      haveI : IsDomain (X.presheaf.stalk (t.f.base y')) :=
        Transforms.isDomain_of_isRegularLocalRing _
      ∃ (s : MonoidalTransform (X.presheaf.stalk (t.f.base y')) (B.stalkIdeal (t.f.base y')))
        (e : s.ring ≃+* t.X'.presheaf.stalk y'),
        e.toRingHom.comp s.toRing = (t.f.stalkMap y').hom ∧
        (strictTransformIdeal s (J.stalkIdeal (t.f.base y'))).map e =
          (strictTransformIdealSheaf t J).stalkIdeal y') := by
  obtain ⟨ξ₀, hξ₀⟩ := exists_isGenericPoint hB
  refine ⟨fun ν ν' h => ?_, fun y' => ?_⟩
  · rw [le_iff_stalkIdeal_le]
    intro y
    have : IsRegularLocalRing (X.presheaf.stalk (t.f y)) := hX _
    have := Transforms.isDomain_of_isRegularLocalRing (X.presheaf.stalk (t.f y))
    obtain ⟨s, e, he⟩ := t.exists_monoidalTransform_stalk y
    rw [stalkIdeal_weakTransform_inf_pow_eq_map hX hBns t J hξ₀ y s e he ν,
      stalkIdeal_weakTransform_inf_pow_eq_map hX hBns t J hξ₀ y s e he ν']
    exact Ideal.map_mono (s.monotone_weakTransformIdeal_inf_pow _ h)
  · have : IsRegularLocalRing (X.presheaf.stalk (t.f y')) := hX _
    have := Transforms.isDomain_of_isRegularLocalRing (X.presheaf.stalk (t.f y'))
    obtain ⟨s, e, he⟩ := t.exists_monoidalTransform_stalk y'
    exact ⟨s, e, he,
      (stalkIdeal_strictTransformIdealSheaf_eq_map hX hBns t J hξ₀ y' s e he).symm⟩

/-- Remark 4 (p. 215): "Let `X`, `B` and `f : X' → X` be as above. Let `V` be a subscheme of `X`
which contains `B`. Let `V'` be the strict transform of `V` on `X'` by `f`, that is, the
smallest subscheme of `X'` which induces `f⁻¹(V − B)` in `X' − f⁻¹(B)`. Let `J` be the sheaf of
ideals of `V` on `X`. Then we see that the strict transform `J''` of `J` on `X'` by `f` is equal
to the sheaf of ideals of `V'` on `X'`. (See the paragraphs preceding Def. 6, §1, Ch. I, and
also §2, Ch. 0.)"  Subschemes are their sheaves of ideals, so `J = V`.

Gap in the paper filled: the proof needs `xᵏR' ∩ R = Pᵏ` (`MonoidalTransform.mem_pow_of_toRing_mem`,
by dehomogenization in `R'/xR'`), which the paper does not mention; the hypothesis `V ⊇ B`
(`hV`) is not used. -/
@[blueprint "rem:III.2-4"
  (statement := /-- Let $X$, $B$ and $f\colon X'\to X$ be as in
    \cref{def:III.2-weak-transform-sheaf}. Let $V$ be a subscheme of $X$ which contains $B$,
    $V'$ the strict transform of $V$ on $X'$ by $f$ (\cref{def:strict-transform}), that is,
    the smallest subscheme of $X'$ which induces $f^{-1}(V-B)$ in $X'-f^{-1}(B)$, and $J$
    the sheaf of ideals of $V$ on $X$. Then the strict transform $J''$ of $J$ on $X'$ by $f$
    (\cref{def:III.2-strict-transform-sheaf}) is equal to the sheaf of ideals of $V'$ on
    $X'$. (Remark 4, p.~215.) -/)
  (proof := /-- The paper says ``we see'' and refers to the paragraphs preceding Def.~6 of
    Ch.~I \S1 and to \S2 of Ch.~0: the sheaf
    of ideals of $V'$ is $\bigcup_n\big(f^{-1}(J):P_E^n\big)$
    (\cref{lem:strict-transform-saturation}), which on stalks is
    $\bigcup_\nu x^{-\nu}(J_y\cap P^\nu)R'$, the strict transform of $J_y$
    (\cref{rem:III.2-1}, \cref{rem:III.2-3}).

    \textbf{Gap in the paper filled.} The saturation $\bigcup_n(J_yR':x^nR')$ equals
    $\bigcup_\nu x^{-\nu}(J_y\cap P^\nu)R'$ because $x^kR'\cap R=P^k$, a fact the paper does
    not mention: if $f\in P^m\setminus P^{m+1}$ then $f/x^m$ is the dehomogenized initial form
    of $f$, which is non-zero in $R'/xR'$, a localization of $(R/P)[X_2,\dots,X_r]$
    (pp.~209--210). The hypothesis $V\supseteq B$ is not needed. -/)
  (latexEnv := "remark")]
theorem _root_.Hironaka.MonoidalTransformation.strictTransformIdealSheaf_eq_strictTransform (hX : X.IsNonsingular) (hB : B.IsIrreducible) (hBns : B.IsNonsingular)
    (t : MonoidalTransformation X B) (V : Subscheme X) (hV : B.IsContainedIn V) :
    strictTransformIdealSheaf t V = strictTransform t V := by
  have _ := hV
  obtain ⟨ξ₀, hξ₀⟩ := exists_isGenericPoint hB
  refine ext_stalkIdeal fun y => ?_
  have : IsRegularLocalRing (X.presheaf.stalk (t.f y)) := hX _
  have := Transforms.isDomain_of_isRegularLocalRing (X.presheaf.stalk (t.f y))
  obtain ⟨s, e, he⟩ := t.exists_monoidalTransform_stalk y
  rw [stalkIdeal_strictTransformIdealSheaf_eq_map hX hBns t V hξ₀ y s e he,
    strictTransform_stalkIdeal]
  simp_rw [stalkIdeal_colon_eq_map t y s e he V]
  rw [← Ideal.map_iSup]
  congr 1
  apply s.strictTransformIdeal_eq_iSup_colon
  by_cases hx : t.f y ∈ B.pts
  · exact Or.inl ⟨Subscheme.isPrime_stalkIdeal_of_isNonsingular hBns hx,
      Subscheme.isRegularLocalRing_quotient_of_isNonsingular hBns hx⟩
  · exact Or.inr (stalkIdeal_eq_top_of_notMem_pts hx)

end Subscheme

/-! ### Lemma 5 (p. 215) and its Corollary (pp. 215–216) -/

/-- Lemma 5 (p. 215): "Let `A → A'` be a homomorphism of noetherian rings such that `A'` is flat
over `A`. Then if `I` and `J` are ideals in `A`, we have `(J ∩ I)A' = JA' ∩ IA'`."  The
homomorphism is `algebraMap A A'`; flatness is `Module.Flat A A'`.  (The noetherian hypotheses
of the paper are kept although the proof does not use them.) -/
@[blueprint "lem:III.5"
  (statement := /-- Let $A\to A'$ be a homomorphism of noetherian rings such that $A'$ is flat
    over $A$. Then if $I$ and $J$ are ideals in $A$, we have $(J\cap I)A'=JA'\cap IA'$.
    (Lemma 5, p.~215.) -/)
  (proof := /-- (This proof was provided by D.~S.~Rim.) We have the exact sequence
    $0\to J\cap I\to A\xrightarrow{\ \sigma\ }A/J\oplus A/I$ where the homomorphism $\sigma$
    is the direct sum of the natural homomorphisms of $A$ to $A/J$ and to $A/I$. Since $A'$
    is flat over $A$, the sequence
    $0\to(J\cap I)\otimes_AA'\to A\otimes_AA'\to(A/J\oplus A/I)\otimes_AA'$, that is,
    $0\to(J\cap I)A'\to A'\to A'/JA'\oplus A'/IA'$, is exact. This implies that
    $(J\cap I)A'=JA'\cap IA'$. (p.~215.) -/)
  (latexEnv := "lemma")]
theorem Ideal.map_inf_eq_inf_map_of_flat {A A' : Type u} [CommRing A] [CommRing A'] [IsNoetherianRing A]
    [IsNoetherianRing A'] [Algebra A A'] [Module.Flat A A'] (I J : Ideal A) :
    (J ⊓ I).map (algebraMap A A') = J.map (algebraMap A A') ⊓ I.map (algebraMap A A') := by
  refine le_antisymm (Ideal.map_inf_le _) fun z hz => ?_
  -- the exact sequence `0 → J ∩ I → A → A/J ⊕ A/I`
  let φ : A →ₗ[A] (A ⧸ J) × (A ⧸ I) := J.mkQ.prod I.mkQ
  have hker : LinearMap.ker φ = J ⊓ I := by
    rw [LinearMap.ker_prod, Submodule.ker_mkQ, Submodule.ker_mkQ]
  -- tensoring with the flat `A`-algebra `A'` keeps it exact
  have hexact := Module.Flat.ker_lTensor_eq A' A' φ
  -- `z ⊗ 1` lies in the kernel of `A' ⊗ A → A' ⊗ (A/J ⊕ A/I)`, i.e. of `A' → A'/JA' ⊕ A'/IA'`
  have hz' : z ⊗ₜ[A] (1 : A) ∈
      LinearMap.ker (TensorProduct.AlgebraTensorModule.lTensor A' A' φ) := by
    rw [LinearMap.mem_ker, TensorProduct.AlgebraTensorModule.lTensor_tmul]
    apply (TensorProduct.prodRight A A' A' (A ⧸ J) (A ⧸ I)).injective
    rw [TensorProduct.prodRight_tmul, map_zero, Prod.mk_eq_zero]
    constructor
    · apply (TensorProduct.tensorQuotEquivQuotSMul A' J).injective
      change TensorProduct.tensorQuotEquivQuotSMul A' J (z ⊗ₜ[A] Ideal.Quotient.mk J 1) = _
      rw [TensorProduct.tensorQuotEquivQuotSMul_tmul_mk, map_zero, one_smul,
        Submodule.Quotient.mk_eq_zero, Ideal.smul_top_eq_map, Submodule.restrictScalars_mem]
      exact hz.1
    · apply (TensorProduct.tensorQuotEquivQuotSMul A' I).injective
      change TensorProduct.tensorQuotEquivQuotSMul A' I (z ⊗ₜ[A] Ideal.Quotient.mk I 1) = _
      rw [TensorProduct.tensorQuotEquivQuotSMul_tmul_mk, map_zero, one_smul,
        Submodule.Quotient.mk_eq_zero, Ideal.smul_top_eq_map, Submodule.restrictScalars_mem]
      exact hz.2
  rw [hexact, LinearMap.mem_range] at hz'
  obtain ⟨w, hw⟩ := hz'
  -- the image of `A' ⊗ (J ∩ I) → A' ⊗ A ≅ A'` is `(J ∩ I)A'`
  have key : ∀ w : A' ⊗[A] (LinearMap.ker φ),
      TensorProduct.AlgebraTensorModule.rid A A' A'
        (TensorProduct.AlgebraTensorModule.lTensor A' A' (LinearMap.ker φ).subtype w) ∈
        (J ⊓ I).map (algebraMap A A') := by
    intro w
    induction w using TensorProduct.inductionOn with
    | tmul a k =>
      rw [TensorProduct.AlgebraTensorModule.lTensor_tmul, Submodule.subtype_apply,
        TensorProduct.AlgebraTensorModule.rid_tmul, Algebra.smul_def]
      have hk : (k : A) ∈ J ⊓ I := by rw [← hker]; exact k.2
      exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ hk)
    | add x y hx hy =>
      rw [map_add, map_add]
      exact Ideal.add_mem _ hx hy
  have := key w
  rwa [hw, TensorProduct.AlgebraTensorModule.rid_tmul, one_smul] at this

section CorLemma5

variable {R Rb : Type u} [CommRing R] [IsRegularLocalRing R] [IsDomain R]
  [CommRing Rb] [IsRegularLocalRing Rb] [IsDomain Rb]

/-- For a canonical homomorphism `β : R' → R̄'` and `I ⊆ Pᵛ`,
`x̄⁻ᵛ(I R̄)R̄' = (x⁻ᵛ I R')R̄'` with `x̄ = β(x)`. -/
private theorem MonoidalTransform.divIdeal_map_eq_map_divIdeal (α : R →+* Rb) {P : Ideal R}
    (t : MonoidalTransform R P) (tb : MonoidalTransform Rb (P.map α)) (β : t.ring →+* tb.ring)
    (hcomm : β.comp t.toRing = tb.toRing.comp α) {x : t.ring}
    (hx : Ideal.span {x} = P.map t.toRing) (hxb : Ideal.span {β x} = (P.map α).map tb.toRing)
    (ν : ℕ) (I : Ideal R) (hI : I ≤ P ^ ν) :
    tb.divIdeal (β x) ν (I.map α) = (t.divIdeal x ν I).map β := by
  have hc : ∀ f, β (t.toRing f) = tb.toRing (α f) := fun f => DFunLike.congr_fun hcomm f
  apply le_antisymm
  · rw [MonoidalTransform.divIdeal, Ideal.span_le]
    rintro z ⟨g, hg, hz⟩
    -- `g ∈ I R̄` maps into `x̄ᵛ · (x⁻ᵛ I R')R̄'`
    have hle : I.map α ≤ Ideal.comap tb.toRing
        (Ideal.span {β x ^ ν} * (t.divIdeal x ν I).map β) := by
      rw [Ideal.map_le_iff_le_comap]
      intro f hf
      rw [Ideal.mem_comap, Ideal.mem_comap, ← hc]
      obtain ⟨y, hy⟩ := MonoidalTransform.exists_toRing_eq_pow_mul_of_mem_pow t hx (hI hf)
      rw [hy, map_mul, map_pow, Ideal.mem_span_singleton_mul]
      exact ⟨β y, Ideal.mem_map_of_mem β (Ideal.subset_span ⟨f, hf, hy.symm⟩), rfl⟩
    have hg' := hle hg
    rw [Ideal.mem_comap, Ideal.mem_span_singleton_mul] at hg'
    obtain ⟨w, hw, hwg⟩ := hg'
    have hzw : z = w := mul_left_cancel₀ (pow_ne_zero ν (MonoidalTransform.ne_zero_of_span_eq_map tb hxb))
      (hz.trans hwg.symm)
    rw [SetLike.mem_coe, hzw]
    exact hw
  · rw [MonoidalTransform.divIdeal, Ideal.map_span, Ideal.span_le]
    rintro _ ⟨y, ⟨f, hf, hy⟩, rfl⟩
    refine Ideal.subset_span ⟨α f, Ideal.mem_map_of_mem α hf, ?_⟩
    rw [← map_pow, ← map_mul, hy, hc]

/-- Corollary to Lemma 5 (pp. 215–216): "Let `R → R̄` be a local homomorphism of regular local
rings which transforms a regular system of parameters of `R` into such a system of parameters of
`R̄`. Let `P` be a prime ideal in `R` such that `R/P` is regular, and `P̄ = PR̄`. Let `J` be an
ideal in `R` and `J̄ = JR̄`. Let `R'` (resp. `R̄'`) be a monoidal transform of `R` (resp. `R̄`)
with center `P` (resp. `P̄`) such that we have the commutative diagram of canonical local
homomorphisms. Let `J'` (resp. `J̄'`) be the strict transform of `J` (resp. `J̄`) in `R'` (resp.
`R̄'`). Then we have `J̄' = J'R̄'`." -/
@[blueprint "cor:III.lem5"
  (statement := /-- Let $\alpha\colon R\to\bar R$ be a local homomorphism of regular local rings
    which transforms a regular system of parameters of $R$ into such a system of parameters
    of $\bar R$. Let $P$ be a prime ideal in $R$ such that $R/P$ is regular, and
    $\bar P=P\bar R$. Let $J$ be an ideal in $R$ and $\bar J=J\bar R$. Let $R'$ (resp.\
    $\bar R'$) be a monoidal transform of $R$ (resp.\ $\bar R$) with center $P$ (resp.\
    $\bar P$) such that we have the commutative diagram of canonical local homomorphisms
    (\cref{def:III.2-canonical}). Let $J'$ (resp.\ $\bar J'$) be the strict transform of $J$
    (resp.\ $\bar J$) in $R'$ (resp.\ $\bar R'$) (\cref{def:III.5-strict}). Then
    $\bar J'=J'\bar R'$. (Corollary to Lemma 5, pp.~215--216.) -/)
  (proof := /-- By the assumption on the local homomorphism $R\to\bar R$, we can apply
    \cref{lem:III.5} to $A=R$ and $A'=\bar R$ and get $(J\cap P^\nu)\bar R=\bar J\cap\bar P^\nu$
    for all non-negative integers $\nu$. On the other hand, if $x$ is an element of $P$ such
    that $PR'=(x)R'$, then $\bar P\bar R'=(x)\bar R'$. Thus
    $\bar J'=\bigcup_{\nu\ge0}x^{-\nu}(\bar J\cap\bar P^\nu)\bar R'
    =\bigcup_{\nu\ge0}x^{-\nu}(J\cap P^\nu)\bar R'=J'\bar R'$ (\cref{rem:III.2-1}).
    (p.~216.) -/)
  (latexEnv := "corollary")]
theorem IsCanonicalLift.strictTransformIdeal_map_eq_map_strictTransformIdeal (α : R →+* Rb) [IsLocalHom α] (hα : RingHom.MapsRSOP α) {P : Ideal R}
    (hP : P.IsPrime) (hS : IsRegularLocalRing (R ⧸ P)) (J : Ideal R)
    (t : MonoidalTransform R P) (tb : MonoidalTransform Rb (P.map α)) (β : t.ring →+* tb.ring)
    (hβ : IsCanonicalLift α t tb β) :
    strictTransformIdeal tb (J.map α) = (strictTransformIdeal t J).map β := by
  -- (the hypotheses that `P` is prime and `R/P` regular are not needed)
  have _ := hP
  have _ := hS
  -- `R̄` is flat over `R`
  let _ : Algebra R Rb := α.toAlgebra
  have hflat : Module.Flat R Rb := hα.flat
  -- `x = x_R` generates `PR'`, and `x̄ = β(x)` generates `P̄R̄'`
  have hx : Ideal.span {t.xR} = P.map t.toRing := t.span_xR_eq_map
  have hxb : Ideal.span {β t.xR} = (P.map α).map tb.toRing := by
    rw [Ideal.map_map, ← hβ.comm, ← Ideal.map_map, ← hx, Ideal.map_span, Set.image_singleton]
  rw [MonoidalTransform.strictTransformIdeal_eq_iSup_of_span_eq t J hx, MonoidalTransform.strictTransformIdeal_eq_iSup_of_span_eq tb (J.map α) hxb,
    Ideal.map_iSup]
  refine iSup_congr fun ν => ?_
  -- Lemma 5: `(J ∩ Pᵛ)R̄ = J̄ ∩ P̄ᵛ`
  have h5 := Ideal.map_inf_eq_inf_map_of_flat (A := R) (A' := Rb) (P ^ ν) J
  rw [RingHom.algebraMap_toAlgebra] at h5
  rw [← Ideal.map_pow, ← h5]
  exact MonoidalTransform.divIdeal_map_eq_map_divIdeal α t tb β hβ.comm hx hxb ν _ inf_le_right

end CorLemma5

/-! ### Lemma 6 (pp. 216–217) -/

section Lemma6

variable {R : Type u} [CommRing R] [IsRegularLocalRing R] [IsDomain R] {P : Ideal R}

/-- Lemma 6 (p. 216): "Let `R` be a regular local ring, `J` an ideal in `R`, and `P` a prime
ideal in `R` such that `R/P` is regular. Let `(f₁, …, f_m)` be a system of elements of `J` such
that their initial forms in `gr_P(R)` generate the ideal `gr_P(J, R)`. Let `R'` be a monoidal
transform of `R` with center `P`, and `x` an element of `P` such that `PR' = (x)R'`. Let
`νᵢ = ν_P(fᵢ)` for `1 ≤ i ≤ m`. Then the strict transform of `J` in `R'` is generated by the
elements `x⁻ᵛⁱ fᵢ` for `1 ≤ i ≤ m`."

Formalization note (encoding): `x⁻ᵛⁱ fᵢ` is the unique `g ∈ R'` with `xᵛⁱ g = fᵢ` (it exists since
`fᵢ ∈ Pᵛⁱ` and `PR' = (x)R'`); if `fᵢ = 0` then `ν_P(fᵢ) = ∞`, `(∞).toNat = 0` and the
corresponding generator is `0`, which changes nothing.

Proof, as printed (pp. 216–217): "Let us take a minimal base
`(x, x₁, …, x_r)` of the prime ideal `P`, where `r + 1 = dim R − dim R/P`. Let
`A' = R[x₁/x, …, x_r/x]`. By the definition of the strict transform of `J` in `R'`, it suffices to
prove that `x⁻ᵛ(J ∩ Pᵛ)A' ⊆ (x⁻ᵛ¹f₁, …, x⁻ᵛᵐf_m)A'` for all sufficiently large integers `ν`. Let
`I_ν = Σᵢ P^{ν−νᵢ} fᵢ` for every `ν ≥ max {νᵢ}`. The above inclusion will follow if we can prove
`J ∩ Pᵛ ⊆ I_ν` for all positive integers `ν ≥ max {νᵢ}`. We shall first prove that
`J ∩ Pᵛ ⊆ I_ν + P^{ν+1}`. [graded computation] Now we have `J ∩ Pᵛ ⊆ I_ν + P^{ν+1}` for all
`ν ≥ max {νᵢ}`. Since `I_{ν+n} = Pⁿ I_ν ⊆ I_ν ⊆ J` for all `ν ≥ max {νᵢ}` and all positive
integers `n`, this result implies immediately `J ∩ Pᵛ ⊆ I_ν + P^{ν+n}` for all `ν ≥ max {νᵢ}` and
all `n ≥ 0`. Hence `J ∩ Pᵛ ⊆ I_ν`."

In Lean (the comments of the proof quote the same steps):
* the minimal base `(x, x₁, …, x_r)` of `P` is `exists_minimal_generators_of_span_eq_map` (that the
  given `x` is its first element is tacit in the paper, and proved here);
* `A'` is the subring of `R'` generated by `R` and the `xᵢ/x`, and `I_ν = Σᵢ P^{ν−νᵢ} fᵢ`;
* the strict transform is `x⁻ᵛ(J ∩ Pᵛ)R'` for large `ν` by Remark 1 (`rem:III.2-1`,
  `divIdeal_monotone_and_strictTransformIdeal_eq_iSup`);
* the graded computation is `step` (via the Rees algebra), `I_{ν+n} = Pⁿ I_ν` is `hIpow`;
* "Hence" is Krull's intersection theorem in `R/I_ν` (`krull`), which the paper does not name.

Encoding: `R'` is an abstract ring, so `A' = R[x₁/x, …, x_r/x]` is the subring of `R'` generated
by (the image of) `R` and the quotients `xᵢ/x ∈ R'` (they exist since `PR' = (x)R'`); it is the
image of the paper's `A' ⊆ Frac R`, and `x⁻ᵛ(J ∩ Pᵛ)A'` is the ideal of `A'` generated by the
quotients `y` with `xᵛ y ∈ J ∩ Pᵛ`.

Steps the paper does not argue, proved here (gaps filled): that the given `x` is the first element
of a minimal base of `P`; `x⁻ᵏPᵏ ⊆ A'`, i.e. `PA' = (x)A'` of p. 209 ("It is well known that"), used
tacitly to read the inclusion in `A'`; that the `x⁻ᵛⁱfᵢ` lie in the strict transform (trivial,
`νᵢ = ν_P(fᵢ)`); and Krull's intersection theorem for "Hence".  Not used: that `R' = A'_{M'}` is a
localization of `A'` (only `A' ⊆ R'` is needed). -/
@[blueprint "lem:III.6"
  (statement := /-- Let $R$ be a regular local ring, $J$ an ideal in $R$, and $P$ a prime
    ideal in $R$ such that $R/P$ is regular. Let $(f_1,\dots,f_m)$ be a system of elements of
    $J$ such that their initial forms in $\operatorname{gr}_P(R)$
    (\cref{def:II.2-initial-form}) generate the ideal $\operatorname{gr}_P(J,R)$
    (\cref{def:II.2-graded-ideal}). Let $R'$ be a monoidal transform of $R$ with center $P$,
    and $x$ an element of $P$ such that $PR'=(x)R'$. Let $\nu_i=\nu_P(f_i)$ for
    $1\le i\le m$. Then the strict transform of $J$ in $R'$ (\cref{def:III.5-strict}) is
    generated by the elements $x^{-\nu_i}f_i$ for $1\le i\le m$. (Lemma 6, p.~216.) -/)
  (proof := /-- Take a minimal base $(x,x_1,\dots,x_r)$ of $P$, $r+1=\dim R-\dim R/P$, and
    $A'=R[x_1/x,\dots,x_r/x]$. By the definition of the strict transform of $J$ in $R'$
    (\cref{rem:III.2-1}) it suffices to prove
    $x^{-\nu}(J\cap P^\nu)A'\subseteq(x^{-\nu_1}f_1,\dots,x^{-\nu_m}f_m)A'$ for all
    sufficiently large $\nu$. Let $I_\nu=\sum_{i=1}^mP^{\nu-\nu_i}f_i$ for
    $\nu\ge\max\{\nu_i\}$; the inclusion follows if $J\cap P^\nu\subseteq I_\nu$ for all
    $\nu\ge\max\{\nu_i\}$. First, $J\cap P^\nu\subseteq I_\nu+P^{\nu+1}$: let
    $f\in J\cap P^\nu$, $f\notin P^{\nu+1}$, with initial form
    $\varphi\in\operatorname{gr}_P(J,R)=(\varphi_1,\dots,\varphi_m)\operatorname{gr}_P(R)$,
    $\varphi_i$ the initial form of $f_i$; then $\varphi=\sum_i\psi_i\varphi_i$ with forms
    $\psi_i\in\operatorname{gr}_P^{\nu-\nu_i}(R)$ (those $i$ with $\nu-\nu_i\ge0$); lifting
    $\psi_i$ to $h_i\in P^{\nu-\nu_i}$ gives $f-\sum_ih_if_i\in P^{\nu+1}$, so
    $f\in I_\nu+P^{\nu+1}$. Since $I_{\nu+n}=P^nI_\nu\subseteq I_\nu\subseteq J$ for all
    $\nu\ge\max\{\nu_i\}$ and $n>0$, this gives $J\cap P^\nu\subseteq I_\nu+P^{\nu+n}$ for all
    $n\ge0$, hence $J\cap P^\nu\subseteq I_\nu$. (pp.~216--217.)

    \textbf{Encoding.} $R'$ being an abstract ring, $A'$ is the subring of $R'$ generated by
    (the image of) $R$ and the quotients $x_i/x\in R'$, the image of the paper's $A'$.

    \textbf{Gaps in the paper filled.} (i) The given $x$ is the first element of a minimal base
    of $P$ (it is not in $MP$, since otherwise $1\in MR'\subseteq M'$). (ii)
    $x^{-k}P^k\subseteq A'$, i.e.\ $PA'=(x)A'$ of p.~209 (``It is well known that''), because
    $P=(x,x_1,\dots,x_r)$ gives $p/x\in A'$ for $p\in P$; it is used tacitly to read
    $J\cap P^\nu\subseteq I_\nu$ as an inclusion in $A'$. (iii) The elements $x^{-\nu_i}f_i$
    lie in the strict transform (they are among its defining generators, $\nu_i=\nu_P(f_i)$).
    (iv) ``Hence $J\cap P^\nu\subseteq I_\nu$'' is Krull's intersection theorem in $R/I_\nu$,
    applied to the ideal $P$ of the local ring $R$. -/)
  (latexEnv := "lemma")]
theorem MonoidalTransform.strictTransformIdeal_eq_span_of_span_initialForm_eq_grIdeal
    (hP : P.IsPrime) (hS : IsRegularLocalRing (R ⧸ P)) (J : Ideal R) {m : ℕ}
    (f : Fin m → R) (hfJ : ∀ i, f i ∈ J)
    (hgen : Ideal.span (Set.range fun i => initialForm P (f i)) = grIdeal P J)
    (t : MonoidalTransform R P) (x : R) (hx : x ∈ P)
    (hxP : Ideal.span {t.toRing x} = P.map t.toRing) :
    strictTransformIdeal t J = Ideal.span {g : t.ring | ∃ i,
      t.toRing x ^ (Ideal.ordElem P (f i)).toNat * g = t.toRing (f i)} := by
  classical
  have := hP
  -- The proof follows pp. 216–217 in the order of the paper; `X = x` in `R'`.
  set X := t.toRing x with hXdef
  have hX0 : X ≠ 0 := MonoidalTransform.ne_zero_of_span_eq_map t hxP
  let ν : Fin m → ℕ := fun i => (Ideal.ordElem P (f i)).toNat
  have hfν : ∀ i, f i ∈ P ^ ν i := fun i =>
    Ideal.mem_pow_of_le_ordElem (ENat.natCast_toNat_le_self _)
  set G : Ideal t.ring := Ideal.span {g : t.ring | ∃ i,
      X ^ (Ideal.ordElem P (f i)).toNat * g = t.toRing (f i)} with hG
  set N₀ := Finset.univ.sup ν with hN₀
  have hνN : ∀ i, ν i ≤ N₀ := fun i => Finset.le_sup (Finset.mem_univ i)
  -- "Let us take a minimal base `(x, x₁, …, x_r)` of the prime ideal `P`, where
  -- `r + 1 = dim R − dim R/P`" (p. 216); that the given `x` is its first element is tacit.
  obtain ⟨-, r, z, -, -, -, -, hz0, hzP⟩ := t.exists_minimal_generators_of_span_eq_map hS hx hxP
  -- `zᵢ/x ∈ R'`, since `PR' = (x)R'`
  have hdiv : ∀ p ∈ P, ∃ y : t.ring, X * y = t.toRing p := fun p hp => by
    have := hxP ▸ Ideal.mem_map_of_mem t.toRing hp
    obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.mp this
    exact ⟨y, by rw [mul_comm]; exact hy⟩
  choose u hu using fun i : Fin (r + 1) => hdiv (z i) (hzP ▸ Ideal.subset_span ⟨i, rfl⟩)
  -- "Let `A' = R[x₁/x, …, x_r/x]`" (p. 216), as a subring of `R'`
  let A' : Subring t.ring :=
    Subring.closure (Set.range t.toRing ∪ Set.range fun i : Fin r => u i.succ)
  have hAR : ∀ c : R, t.toRing c ∈ A' := fun c => Subring.subset_closure (Or.inl ⟨c, rfl⟩)
  have hAu : ∀ i, u i ∈ A' := by
    intro i
    refine Fin.cases ?_ (fun i => Subring.subset_closure (Or.inr ⟨i, rfl⟩)) i
    have : u 0 = 1 := mul_left_cancel₀ hX0 (by rw [hu 0, hz0, mul_one])
    rw [this]
    exact A'.one_mem
  -- `p/x ∈ A'` for `p ∈ P = (x, x₁, …, x_r)` (tacit)
  have hPA : ∀ p ∈ P, ∃ b ∈ A', X * b = t.toRing p := by
    intro p hp
    rw [← hzP] at hp
    induction hp using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨j, rfl⟩ := hy
      exact ⟨u j, hAu j, hu j⟩
    | zero => exact ⟨0, A'.zero_mem, by simp⟩
    | add y w _ _ hy hw =>
      obtain ⟨b, hb, hby⟩ := hy
      obtain ⟨b', hb', hbw⟩ := hw
      exact ⟨b + b', A'.add_mem hb hb', by rw [mul_add, hby, hbw, map_add]⟩
    | smul c y _ hy =>
      obtain ⟨b, hb, hby⟩ := hy
      exact ⟨t.toRing c * b, A'.mul_mem (hAR c) hb, by rw [smul_eq_mul, map_mul, ← hby]; ring⟩
  -- `x⁻ᵏ Pᵏ ⊆ A'`, i.e. `PA' = (x)A'` of p. 209 ("It is well known that"), used tacitly to read
  -- `J ∩ Pᵛ ⊆ I_ν` as an inclusion in `A'`
  have hPkA : ∀ k : ℕ, ∀ a ∈ P ^ k, ∃ c ∈ A', t.toRing a = X ^ k * c := by
    intro k
    induction k with
    | zero => exact fun a _ => ⟨t.toRing a, hAR a, by rw [pow_zero, one_mul]⟩
    | succ k ih =>
      intro a ha
      rw [pow_succ] at ha
      refine Submodule.mul_induction_on ha (fun v hv w hw => ?_) fun a b ⟨c, hc, hac⟩ ⟨c', hc', hbc⟩ => ?_
      · obtain ⟨c, hc, hvc⟩ := ih v hv
        obtain ⟨b, hb, hwb⟩ := hPA w hw
        exact ⟨c * b, A'.mul_mem hc hb, by rw [map_mul, hvc, ← hwb, pow_succ]; ring⟩
      · exact ⟨c + c', A'.add_mem hc hc', by rw [map_add, hac, hbc, mul_add]⟩
  -- "Let `I_ν = Σᵢ P^{ν-νᵢ} fᵢ` for every `ν ≥ max {νᵢ}`" (p. 216)
  let I : ℕ → Ideal R := fun n => ⨆ i, P ^ (n - ν i) * Ideal.span {f i}
  have hIJ : ∀ n, I n ≤ J := fun n => iSup_le fun i =>
    Ideal.mul_le_right.trans (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr (hfJ i)))
  -- "`I_{ν+n} = Pⁿ I_ν ⊆ I_ν ⊆ J` for all `ν ≥ max {νᵢ}`" (p. 216)
  have hIpow : ∀ n, N₀ ≤ n → ∀ k, I (n + k) = P ^ k * I n := by
    intro n hn k
    simp only [I]
    rw [Ideal.mul_iSup]
    refine iSup_congr fun i => ?_
    rw [← mul_assoc, ← pow_add, show n + k - ν i = k + (n - ν i) by have := hνN i; omega]
  have hIanti : ∀ n, N₀ ≤ n → ∀ k, I (n + k) ≤ I n := fun n hn k => by
    rw [hIpow n hn k]
    exact Ideal.mul_le_right
  -- initial forms as classes of monomials
  have hφ : ∀ i, initialForm P (f i) = AssocGraded.mk P (ν i) (f i) (hfν i) := by
    intro i
    by_cases htop : Ideal.ordElem P (f i) = ⊤
    · rw [initialForm, dite_eq_left htop, eq_comm, AssocGraded.mk_eq_zero_iff]
      exact Ideal.ordElem_eq_top_iff.mp htop _
    · exact initialForm_eq_mk P (ENat.natCast_toNat htop).symm
  -- "We shall first prove that `J ∩ Pᵛ ⊆ I_ν + P^{ν+1}`" (p. 216), by the graded computation
  have step : ∀ n, N₀ ≤ n → ∀ a ∈ J, a ∈ P ^ n → ∃ b ∈ I n, a - b ∈ P ^ (n + 1) := by
    intro n hn a haJ ha
    have h1 : AssocGraded.mk P n a ha ∈ Ideal.span (Set.range fun i => initialForm P (f i)) :=
      hgen ▸ mk_mem_grIdeal P haJ ha
    obtain ⟨c, hc⟩ := Ideal.mem_span_range_iff_exists_fun.mp h1
    choose p hp using fun i => Ideal.Quotient.mk_surjective (c i)
    have hmono : ∀ i, (Polynomial.monomial (ν i) (f i) : Polynomial R) ∈ reesAlgebra P :=
      fun i => reesAlgebra.monomial_mem.mpr (hfν i)
    have hq : (∑ i, p i * ⟨Polynomial.monomial (ν i) (f i), hmono i⟩ -
        ⟨Polynomial.monomial n a, reesAlgebra.monomial_mem.mpr ha⟩ : reesAlgebra P) ∈
        P.map (algebraMap R (reesAlgebra P)) := by
      rw [← Ideal.Quotient.eq]
      refine (map_sum (Ideal.Quotient.mk (P.map (algebraMap R (reesAlgebra P)))).toAddMonoidHom
        _ _).trans ((Finset.sum_congr rfl fun i _ => ?_).trans hc)
      rw [← hp i, hφ i]
      exact (Ideal.Quotient.mk (P.map (algebraMap R (reesAlgebra P)))).toMonoidHom.map_mul _ _
    have hcoeff := (mem_map_algebraMap_reesAlgebra_iff _).mp hq n
    have hco : ∀ i, ((p i : Polynomial R) * Polynomial.monomial (ν i) (f i)).coeff n =
        (p i : Polynomial R).coeff (n - ν i) * f i := by
      intro i
      have := Polynomial.coeff_mul_monomial (p i : Polynomial R) (ν i) (n - ν i) (f i)
      rwa [Nat.sub_add_cancel ((hνN i).trans hn)] at this
    simp only [AddSubgroupClass.coe_sub, AddSubmonoidClass.coe_finsetSum, MulMemClass.coe_mul,
      Polynomial.coeff_sub, Polynomial.finsetSum_coeff, hco,
      Polynomial.coeff_monomial_same] at hcoeff
    refine ⟨∑ i, (p i : Polynomial R).coeff (n - ν i) * f i, ?_, ?_⟩
    · exact Submodule.sum_mem_iSup fun i => Ideal.mul_mem_mul
        ((mem_reesAlgebra_iff P (p i : Polynomial R)).mp (p i).2 (n - ν i))
        (Ideal.mem_span_singleton_self _)
    · rw [← neg_sub]
      exact neg_mem hcoeff
  -- "this result implies immediately `J ∩ Pᵛ ⊆ I_ν + P^{ν+n}`" (pp. 216–217)
  have approx : ∀ n, N₀ ≤ n → ∀ k, ∀ a ∈ J, a ∈ P ^ n → ∃ b ∈ I n, a - b ∈ P ^ (n + k) := by
    intro n hn k
    induction k with
    | zero => exact fun a _ ha => ⟨0, zero_mem _, by simpa using ha⟩
    | succ k ih =>
      intro a haJ ha
      obtain ⟨b, hb, hab⟩ := ih a haJ ha
      obtain ⟨b', hb', hab'⟩ := step (n + k) (by omega) (a - b)
        (sub_mem haJ (hIJ n hb)) hab
      refine ⟨b + b', add_mem hb (hIanti n hn k hb'), ?_⟩
      rw [← sub_sub, ← add_assoc]
      exact hab'
  -- "Hence `J ∩ Pᵛ ⊆ I_ν`" (p. 217); tacitly this is Krull's intersection theorem in `R/I_ν`
  have krull : ∀ n, N₀ ≤ n → ∀ a ∈ J, a ∈ P ^ n → a ∈ I n := by
    intro n hn a haJ ha
    have hK := Ideal.iInf_pow_smul_eq_bot_of_isLocalRing P (M := R ⧸ I n) hP.ne_top
    have hmem : Ideal.Quotient.mk (I n) a ∈ (⨅ i : ℕ, P ^ i • ⊤ : Submodule R (R ⧸ I n)) := by
      refine (Submodule.mem_iInf _).mpr fun k => ?_
      obtain ⟨b, hb, hab⟩ := approx n hn k a haJ ha
      have h₁ : Ideal.Quotient.mk (I n) a = Ideal.Quotient.mk (I n) (a - b) :=
        Ideal.Quotient.eq.mpr (by rwa [sub_sub_cancel])
      have h₂ : Ideal.Quotient.mk (I n) (a - b) = (a - b) • (1 : R ⧸ I n) :=
        Algebra.algebraMap_eq_smul_one (a - b)
      rw [h₁, h₂]
      exact Submodule.smul_mem_smul (Ideal.pow_le_pow_right (by omega) hab) Submodule.mem_top
    rw [hK] at hmem
    exact Ideal.Quotient.eq_zero_iff_mem.mp ((Submodule.mem_bot R).mp hmem)
  -- the ideals `x⁻ᵛ(J ∩ Pᵛ)A'` and `(x⁻ᵛ¹f₁, …, x⁻ᵛᵐfₘ)A'` of `A'` (p. 216)
  let W : ℕ → Ideal A' := fun n =>
    Ideal.span {y : A' | ∃ a ∈ J ⊓ P ^ n, X ^ n * (y : t.ring) = t.toRing a}
  let H : Ideal A' := Ideal.span {g : A' | ∃ i, X ^ ν i * (g : t.ring) = t.toRing (f i)}
  -- "The above inclusion", `x⁻ᵛ(J ∩ Pᵛ)A' ⊆ (x⁻ᵛ¹f₁, …, x⁻ᵛᵐfₘ)A'`, "will follow if we can prove
  -- `J ∩ Pᵛ ⊆ I_ν`" (p. 216): `x⁻ᵛ(Σᵢ hᵢ fᵢ) = Σᵢ (x⁻⁽ᵛ⁻ᵛⁱ⁾hᵢ)(x⁻ᵛⁱfᵢ)` with `x⁻⁽ᵛ⁻ᵛⁱ⁾hᵢ ∈ A'`
  have hWH : ∀ n, N₀ ≤ n → W n ≤ H := by
    intro n hn
    refine Ideal.span_le.mpr ?_
    rintro y ⟨a, ha, hya⟩
    have hadd : ∀ b b' : R, (∃ y' ∈ H, X ^ n * (y' : t.ring) = t.toRing b) →
        (∃ y' ∈ H, X ^ n * (y' : t.ring) = t.toRing b') →
        ∃ y' ∈ H, X ^ n * (y' : t.ring) = t.toRing (b + b') := by
      rintro b b' ⟨y₁, hy₁, h₁⟩ ⟨y₂, hy₂, h₂⟩
      exact ⟨y₁ + y₂, H.add_mem hy₁ hy₂, by rw [Subring.coe_add, mul_add, h₁, h₂, map_add]⟩
    have hgen' : ∀ i, ∀ b ∈ P ^ (n - ν i) * Ideal.span {f i},
        ∃ y' ∈ H, X ^ n * (y' : t.ring) = t.toRing b := by
      intro i b hb
      refine Submodule.mul_induction_on hb (fun h hh w hw => ?_) (fun b b' h h' => hadd b b' h h')
      obtain ⟨c, hc, hhc⟩ := hPkA _ h hh
      obtain ⟨c', hc', hfc⟩ := hPkA _ (f i) (hfν i)
      obtain ⟨d, hd⟩ := Ideal.mem_span_singleton'.mp hw
      have hg : (⟨c', hc'⟩ : A') ∈ H := Ideal.subset_span ⟨i, hfc.symm⟩
      refine ⟨⟨t.toRing d, hAR d⟩ * ⟨c, hc⟩ * ⟨c', hc'⟩, H.mul_mem_left _ hg, ?_⟩
      rw [← hd, map_mul, map_mul, hhc, hfc]
      simp only [Subring.coe_mul]
      rw [show X ^ n = X ^ (n - ν i) * X ^ ν i by
        rw [← pow_add, Nat.sub_add_cancel ((hνN i).trans hn)]]
      ring
    have hIa : ∀ b ∈ I n, ∃ y' ∈ H, X ^ n * (y' : t.ring) = t.toRing b := by
      intro b hb
      refine Submodule.iSup_induction _ (motive := fun b => ∃ y' ∈ H, X ^ n * (y' : t.ring) = t.toRing b)
        hb (fun i b hb => hgen' i b hb) ⟨0, H.zero_mem, by simp⟩ hadd
    obtain ⟨y', hy', hy'b⟩ := hIa a (krull n hn a ha.1 ha.2)
    have : y = y' := Subtype.ext (mul_left_cancel₀ (pow_ne_zero n hX0) (hya.trans hy'b.symm))
    rwa [this]
  -- "By the definition of the strict transform of `J` in `R'`, it suffices to prove that
  -- `x⁻ᵛ(J ∩ Pᵛ)A' ⊆ (x⁻ᵛ¹f₁, …, x⁻ᵛᵐfₘ)A'` for all sufficiently large integers `ν`" (p. 216):
  -- Remark 1 (p. 214), `J' = x⁻ᵛ(J ∩ Pᵛ)R'` for `ν ≥ N`, and `x⁻ᵛ(J ∩ Pᵛ) ⊆ A'`.
  obtain ⟨-, -, ⟨N, hN⟩, -, -⟩ :=
    t.divIdeal_monotone_and_strictTransformIdeal_eq_iSup hP hS J X hxP
  apply le_antisymm
  · rw [hN (max N N₀) (le_max_left _ _), MonoidalTransform.divIdeal, Ideal.span_le]
    rintro y ⟨a, ha, hya⟩
    obtain ⟨c, hc, hac⟩ := hPkA _ a ha.2
    have hyc : y = c := mul_left_cancel₀ (pow_ne_zero _ hX0) (hya.trans hac)
    have hcW : (⟨c, hc⟩ : A') ∈ W (max N N₀) := Ideal.subset_span ⟨a, ha, hac.symm⟩
    have hHG : H ≤ G.comap A'.subtype := by
      refine Ideal.span_le.mpr ?_
      rintro g ⟨i, hg⟩
      exact Ideal.subset_span ⟨i, hg⟩
    rw [SetLike.mem_coe, hyc]
    exact hHG (hWH _ (le_max_right _ _) hcW)
  · rw [hG, Ideal.span_le]
    rintro y ⟨i, hi⟩
    exact Ideal.subset_span ⟨X, hxP, f i, hfJ i, _, ENat.natCast_toNat_le_self _, hi⟩

end Lemma6

end Hironaka

