/-
Copyright (c) 2026 Daattavya Aggarwal, Minhyong Kim, Oisin Kim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daattavya Aggarwal, Minhyong Kim, Oisin Kim
-/
module

public import Mathlib.FieldTheory.SeparableClosure
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
public import Mathlib.RingTheory.AdicCompletion.LocalRing
public import Mathlib.RingTheory.Coalgebra.IsFrobenius
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.HopfAlgebra.Basic
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.RingTheory.SimpleRing.Principal
public import Architect
public import Hironaka.Ch3.StabilityCor3c
public import Hironaka.Ch3.TransformsCompletion
public import Hironaka.Ch3.PermissibleEffects
public import Hironaka.Compat.PermissibleCenterBlowdown
public import Hironaka.Compat.CurveResolution
public import Hironaka.Ch2.AscendingChain
public import Hironaka.Compat.DimensionFacts

/-!
# Compatibility layer: Corollary 2 of Proposition 2 (Ch. III §8, pp. 260–261)

> COROLLARY 2. Let `R` be a regular local ring and `M` the maximal ideal in `R`. Let us assume that
> the residue field `R/M` has characteristic zero. Let `Q` be a prime ideal in `R`, and `J` an
> ideal in `R` such that `Q ⊇ J`. Suppose we have a system of elements `(g₁, …, g_m)` of `J` such
> that (i) the initial forms of `g_j` in `gr_M(R)` generate the ideal `gr_M(J, R)`, and (ii)
> `ν_M(g_j) = ν_{QR_Q}(g_j)` for all `j`. Let `P` be a prime ideal in `R` such that
> `Q ⊇ P ⊇ J` and that `R/P` is regular. If `gr_{PR_Q}(R_Q/JR_Q)` is flat over `R_Q/PR_Q`, then
> `gr_P(R/J)` is flat over `R/P`.  (p. 260)

The proof (pp. 260–261) passes to the completion (a minimal prime `Q̂` of `QR̂` with
`dim(R̂/Q̂) = dim(R/Q)`), treats the case `dim(R/Q) = 1` by a sequence of monoidal transforms with
centre the maximal ideal, applying Proposition 2 at each step, and treats `dim(R/Q) > 1` by
induction
on `dim(R/Q)`.  This file contains the whole proof, with Proposition 2 as a hypothesis
(`Proposition2Statement`), since it lies upstream of `Hironaka/Ch3/FrameTransforms.lean`, where
Proposition 2 is stated; the final theorem `isNormallyFlatAlongIdeal_of_localization` there is
`isNormallyFlatAlongIdeal_of_proposition2` applied to Proposition 2.

The architecture is that of the proof of Corollary 3 (c) (`Hironaka/Ch3/StabilityCor3c.lean`),
which the proof of Corollary 2 follows closely:

* `isNormallyFlatAlongIdeal_of_isRegularLocalRing_quotient_of_localization`: the case `R/Q`
  regular (Theorem 3 of Ch. II and Corollary 3 (a));
* `exists_prime_of_localRingHom_bijective`: one monoidal transform with `R_Q = (R₁)_{Q₁}`: the
  prime `P₁` of `R₁` with `P₁ ∩ R = P`, `PR_Q = P₁(R₁)_{Q₁}`, `JR_Q = J₁(R₁)_{Q₁}`;
* `isNormallyFlatAlongIdeal_of_curveImage_eq`, `…_of_curve`, `…_of_dimensionLEOne`: the case
  `dim(R/Q) ≤ 1`, by induction on the sequence of monoidal transforms of Corollary 3 (c);
* `Corollary2Dim n`: the assertion for the regular local rings with `dim(R/Q) = n`;
  `isNormallyFlatAlongIdeal_localization_of_le`: the induction assumption applied to `R_{Q'}`;
  `corollary2DimComplete_of_forall_lt`: the complete case (`Q'` with `dim(R/Q') = 1`);
* `corollary2Dim_of_complete`: the reduction to the completion; `corollary2Dim` and
  `isNormallyFlatAlongIdeal_of_proposition2`: the induction on `dim(R/Q)`.

The dimension theory used (the dimension of the completion, `Hironaka/Compat/DimensionFacts.lean`)
is cited from Samuel–Zariski (footnote 3, p. 116).

The proof follows the printed text.  **Gaps of the paper filled** (each recorded in the docstring of
the declaration concerned): that a monoidal transform `R₁` with centre `M`, residually algebraic
over `R`, with a prime `Q₁ ∩ R = Q` exists (`exists_monoidalTransform_curveImage_lt`), the passage
to an arbitrary such `R₁` and the termination "the process cannot be repeated infinitely many times"
(`exists_ringHom_curveImage_lt_of_comap_eq`, as in Corollary 3 (c)); and the facts "`P₁` the prime
ideal in `R₁` with `P₁ ∩ R = P`", "`R₁/P₁` regular", "`ν*(J) = ν*(J₁)`" and "`M` is a permissible
center for `J`" that the paper uses tacitly.
-/

@[expose] public section

open IsLocalRing

namespace Hironaka

universe u

section Proposition2

/-- Proposition 2 of Ch. III, §8 (pp. 258–259; `isPermissibleCenter_of_nuStar_strictTransform_eq`
in `Hironaka/Ch3/FrameTransforms.lean`), as a proposition about all data in a universe: the
proof of Corollary 2 uses it, and this file lies upstream of `FrameTransforms.lean`, so it is a
hypothesis of the theorems below and is supplied there. -/
def Proposition2Statement : Prop :=
  ∀ (R : Type u) [CommRing R] [IsRegularLocalRing R] [IsDomain R]
    (_ : ringChar R = ringChar (ResidueField R)) (J P Q : Ideal R) [P.IsPrime] [Q.IsPrime]
    (_ : P ≤ Q) (_ : J ≤ P) (_ : Q ≠ P) [IsRegularLocalRing (R ⧸ P)]
    (_ : IsPermissibleCenter R J Q) (T : MonoidalTransform R Q) [IsLocalHom T.toRing]
    [IsRegularLocalRing T.ring]
    (_ : RingHom.IsResiduallySeparableAlgebraic (R := R) (R' := T.ring) T.toRing)
    (P₁ : Ideal T.ring) [P₁.IsPrime] (_ : P₁.comap T.toRing = P)
    (_ : nuStar T.ring (strictTransformIdeal T J) = nuStar R J)
    (_ : IsPermissibleCenter T.ring (strictTransformIdeal T J) P₁),
    IsPermissibleCenter R J P

/-- In a local ring whose residue field has characteristic zero, the characteristic of the ring
and of its residue field agree (both are zero). -/
theorem ringChar_eq_of_charZero_residueField {R : Type u} [CommRing R] [IsLocalRing R]
    [CharZero (ResidueField R)] : ringChar R = ringChar (ResidueField R) := by
  have : CharZero R := by
    refine charZero_of_inj_zero fun n hn => ?_
    have h1 : residue R (n : R) = 0 := by rw [hn, map_zero]
    rw [map_natCast] at h1
    exact Nat.cast_eq_zero.mp h1
  rw [ringChar.eq_zero, ringChar.eq_zero]

end Proposition2

section Corollary2Statement

/-- The assertion of Corollary 2 (p. 260) for the regular local rings `R` (with residue field of
characteristic zero) and primes `Q` with `dim(R/Q) = n`: the statement proved by "induction on
`dim(R/Q)`" (p. 261: "Now, the proof of Corollary 2 is done by induction on `dim(R/Q)`"). -/
def Corollary2Dim (n : ℕ) : Prop :=
  ∀ (R : Type u) [CommRing R] [IsRegularLocalRing R] [CharZero (ResidueField R)]
    (Q J : Ideal R) [Q.IsPrime] {m : ℕ} (g : Fin m → R) (_ : IsLocallyAdaptedSystem R Q J g)
    (P : Ideal R) [P.IsPrime] (_ : J ≤ P) (_ : P ≤ Q) (_ : IsRegularLocalRing (R ⧸ P))
    (_ : ringKrullDim (R ⧸ Q) = n)
    (_ : IsNormallyFlatAlongIdeal ((P.map (algebraMap R (Localization.AtPrime Q))).map
      (Ideal.Quotient.mk (J.map (algebraMap R (Localization.AtPrime Q)))))),
    IsNormallyFlatAlongIdeal (P.map (Ideal.Quotient.mk J))

/-- `Corollary2Dim n` for complete regular local rings `R` only ("By the above arguments, we may
assume that `R` is complete", p. 261). -/
def Corollary2DimComplete (n : ℕ) : Prop :=
  ∀ (R : Type u) [CommRing R] [IsRegularLocalRing R] [CharZero (ResidueField R)]
    [IsAdicComplete (maximalIdeal R) R]
    (Q J : Ideal R) [Q.IsPrime] {m : ℕ} (g : Fin m → R) (_ : IsLocallyAdaptedSystem R Q J g)
    (P : Ideal R) [P.IsPrime] (_ : J ≤ P) (_ : P ≤ Q) (_ : IsRegularLocalRing (R ⧸ P))
    (_ : ringKrullDim (R ⧸ Q) = n)
    (_ : IsNormallyFlatAlongIdeal ((P.map (algebraMap R (Localization.AtPrime Q))).map
      (Ideal.Quotient.mk (J.map (algebraMap R (Localization.AtPrime Q)))))),
    IsNormallyFlatAlongIdeal (P.map (Ideal.Quotient.mk J))

end Corollary2Statement


section RingEquivTransport

/-- Normal flatness of `P` modulo `J` is invariant under a ring isomorphism. -/
theorem isNormallyFlatAlongIdeal_mod_map_ringEquiv {A B : Type u} [CommRing A] [CommRing B]
    (e : A ≃+* B) (J P : Ideal A) (J' P' : Ideal B) (hJ : J' = J.map (e : A →+* B))
    (hP : P' = P.map (e : A →+* B)) (h : IsNormallyFlatAlongIdeal (P.map (Ideal.Quotient.mk J))) :
    IsNormallyFlatAlongIdeal (P'.map (Ideal.Quotient.mk J')) := by
  subst hJ hP
  refine Hironaka.isNormallyFlatAlongIdeal_of_ringEquiv (Ideal.quotientEquiv J _ e rfl) _ _ ?_ h
  rw [Ideal.map_map, Ideal.map_map]
  congr 1

end RingEquivTransport

section BaseCase

/-- **Corollary 2 when `R/Q` is regular** (p. 261: "We know that the assertion is verified if
`R/Q` is regular, by Theorem 3, §3, Ch. II, combined with Corollary 1 of Theorem 2, Ch. II"):
`Q` is a permissible center for `J` (conditions (i), (ii), by (a) of Corollary 3 of Theorem 5), and
`P R_Q` is normally flat modulo `J R_Q`, so `P` is normally flat modulo `J`. -/
@[blueprint "lem:III.8-cor2-regular-case"
  (statement := /-- Let $R$ be a regular local ring, $Q\supseteq J$ a prime ideal with $R/Q$
    regular, $(g_j)$ a system of elements of $J$ with the properties (i), (ii) of
    \cref{cor:III.thm5-3a}, and $P$ a prime ideal with $Q\supseteq P\supseteq J$ and $R/P$
    regular. If $\operatorname{gr}_{PR_Q}(R_Q/JR_Q)$ is flat over $R_Q/PR_Q$, then
    $\operatorname{gr}_P(R/J)$ is flat over $R/P$. -/)
  (proof := /-- $Q$ is a permissible center for $J$ (\cref{cor:III.thm5-3a}), so
    $\operatorname{gr}_{Q/J}(R/J)$ is flat; Theorem~3 of Ch.~II (\cref{thm:II.3-3}) for
    $P/J\subseteq Q/J$ gives the claim. -/)
  (latexEnv := "lemma")]
theorem isNormallyFlatAlongIdeal_of_isRegularLocalRing_quotient_of_localization [Hironaka.Cited.CurveFiniteIntegralClosure.{u}] [Hironaka.Cited.ExistsSurjectiveOfIsRegularLocalRingOfIsAdicComplete.{u}] [Hironaka.Cited.IsRegularLocalRingLocalizationOfIsRegularLocalRing.{u}]
    {R : Type u} [CommRing R] [IsRegularLocalRing R] (Q J P : Ideal R) [Q.IsPrime] [P.IsPrime]
    (hJP : J ≤ P) (hPQ : P ≤ Q) [hPreg : IsRegularLocalRing (R ⧸ P)]
    [hQreg : IsRegularLocalRing (R ⧸ Q)] {m : ℕ} (g : Fin m → R)
    (hg : IsLocallyAdaptedSystem R Q J g)
    (hflat : IsNormallyFlatAlongIdeal
      ((P.map (algebraMap R (Localization.AtPrime Q))).map
        (Ideal.Quotient.mk (J.map (algebraMap R (Localization.AtPrime Q)))))) :
    IsNormallyFlatAlongIdeal (P.map (Ideal.Quotient.mk J)) := by
  have hJQ : J ≤ Q := hJP.trans hPQ
  obtain ⟨-, -, -, hQnf⟩ :=
    (isPermissibleCenter_of_isLocallyAdaptedSystem Q J hJQ g hg Q le_rfl).resolve_left
      (Ideal.IsPrime.ne_top inferInstance)
  have hL : localizationEquivHom Q (RingEquiv.refl (Localization.AtPrime Q)) =
      algebraMap R (Localization.AtPrime Q) := RingHom.ext fun _ => rfl
  refine isNormallyFlatAlongIdeal_of_localizationEquiv J P Q hPQ hJP hPreg hQreg
    (RingEquiv.refl (Localization.AtPrime Q)) hQnf ?_
  rw [hL]
  exact hflat

end BaseCase

section TransformStep

/-- **The prime `P₁` of a monoidal transform with `R_Q = (R₁)_{Q₁}`** (p. 261: "if `P₁` is the prime
ideal in `R₁` with `P₁ ∩ R = P`"; "`R_Q = (R₁)_{Q₁}`, `JR_Q = J₁(R₁)_{Q₁}`, and
`PR_Q = P₁(R₁)_{Q₁}`").
For a monoidal transform `R₁` of `R` with centre the maximal ideal `M`, a prime `Q ⊊ M` and a prime
`Q₁` of `R₁` with `x ∉ Q` such that `R_Q → (R₁)_{Q₁}` is bijective, every prime `P ⊆ Q` with `R/P`
regular is the contraction of a prime `P₁ ⊆ Q₁` of `R₁` with `R₁/P₁` regular, `J₁ ⊆ P₁` for
`J ⊆ P`, and the normal flatness of `PR_Q` modulo `JR_Q` is that of `P₁(R₁)_{Q₁}` modulo
`J₁(R₁)_{Q₁}`. -/
@[blueprint "lem:III.8-cor2-transform-step"
  (statement := /-- Let $R$ be a regular local ring, $Q\subsetneq M$ a prime ideal, $R_1$ a monoidal
    transform of $R$ with center $M$ and $Q_1$ a prime ideal of $R_1$ with $Q_1\cap R=Q$,
    $x\notin Q$, such that $R_Q\to(R_1)_{Q_1}$ is bijective. If $J\subseteq P\subseteq Q$ with
    $P$ prime and $R/P$ regular, there is a prime $P_1\subseteq Q_1$ of $R_1$ with
    $P_1\cap R=P$, $R_1/P_1$ regular, $J_1\subseteq P_1$, and $P_1(R_1)_{Q_1}$ is normally flat
    modulo $J_1(R_1)_{Q_1}$ as soon as $PR_Q$ is normally flat modulo $JR_Q$. -/)
  (proof := /-- $P_1$ is the contraction to $R_1$ of the image of $PR_Q$ under
    $R_Q\cong(R_1)_{Q_1}$. Since $x$ is a unit in $(R_1)_{Q_1}$, $J(R_1)_{Q_1}=J_1(R_1)_{Q_1}$ and
    $J_1\subseteq P_1$; $R_1/P_1$ is a monoidal transform of $R/P$ with center $M/P$, hence
    regular. \textbf{Gap in the paper filled.} The paper says ``if $P_1$ is the prime ideal in
    $R_1$ with $P_1\cap R=P$'' without constructing it. -/)
  (latexEnv := "lemma")]
theorem exists_prime_of_localRingHom_bijective {R : Type u} [CommRing R] [IsRegularLocalRing R]
    [IsDomain R] (Q J P : Ideal R) [Q.IsPrime] [P.IsPrime] (hJP : J ≤ P) (hPQ : P ≤ Q)
    [IsRegularLocalRing (R ⧸ P)] (hMQ : maximalIdeal R ≠ Q)
    (t : MonoidalTransform R (maximalIdeal R)) [IsLocalHom t.toRing] [IsRegularLocalRing t.ring]
    (Q₁ : Ideal t.ring) [Q₁.IsPrime] (hQ : Q = Q₁.comap t.toRing)
    (hbij : Function.Bijective (Localization.localRingHom Q Q₁ t.toRing hQ)) (hxQ : t.x ∉ Q)
    (hflat : IsNormallyFlatAlongIdeal ((P.map (algebraMap R (Localization.AtPrime Q))).map
      (Ideal.Quotient.mk (J.map (algebraMap R (Localization.AtPrime Q)))))) :
    ∃ (P₁ : Ideal t.ring) (_ : P₁.IsPrime), P₁.comap t.toRing = P ∧ P₁ ≤ Q₁ ∧
      strictTransformIdeal t J ≤ P₁ ∧ IsRegularLocalRing (t.ring ⧸ P₁) ∧
      IsNormallyFlatAlongIdeal ((P₁.map (algebraMap t.ring (Localization.AtPrime Q₁))).map
        (Ideal.Quotient.mk ((strictTransformIdeal t J).map
          (algebraMap t.ring (Localization.AtPrime Q₁))))) := by
  classical
  set L := Localization.AtPrime Q
  set L₁ := Localization.AtPrime Q₁
  set f := Localization.localRingHom Q Q₁ t.toRing hQ
  let e : L ≃+* L₁ := RingEquiv.ofBijective f hbij
  have hcomp : ∀ r, e (algebraMap R L r) = algebraMap t.ring L₁ (t.toRing r) :=
    Localization.localRingHom_to_map Q Q₁ t.toRing hQ
  have hxQ₁ : t.toRing t.x ∉ Q₁ := fun hx => hxQ (hQ ▸ hx)
  have hdisj : Disjoint (Q.primeCompl : Set R) (P : Set R) :=
    Set.disjoint_left.mpr fun a ha haP => ha (hPQ haP)
  have hPL : (P.map (algebraMap R L)).IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint Q.primeCompl L P inferInstance hdisj
  have hPLc : (P.map (algebraMap R L)).comap (algebraMap R L) = P :=
    IsLocalization.under_map_of_isPrime_disjoint Q.primeCompl L inferInstance hdisj
  -- the ideal `P₁`
  let P₁ : Ideal t.ring := ((P.map (algebraMap R L)).comap (e.symm : L₁ →+* L)).comap
    (algebraMap t.ring L₁)
  have hP₁prime : P₁.IsPrime := Ideal.comap_isPrime _ _
  have hP₁L : P₁.map (algebraMap t.ring L₁) = (P.map (algebraMap R L)).map (e : L →+* L₁) := by
    have h1 : P₁.map (algebraMap t.ring L₁) =
        (P.map (algebraMap R L)).comap (e.symm : L₁ →+* L) :=
      IsLocalization.map_under Q₁.primeCompl L₁ _
    rw [h1]
    exact Ideal.comap_symm (I := P.map (algebraMap R L)) e
  have hP₁comap : P₁.comap t.toRing = P := by
    show Ideal.comap t.toRing (Ideal.comap (algebraMap t.ring L₁)
      (Ideal.comap (e.symm : L₁ →+* L) (P.map (algebraMap R L)))) = P
    rw [Ideal.comap_comap, Ideal.comap_comap]
    have : (e.symm : L₁ →+* L).comp ((algebraMap t.ring L₁).comp t.toRing) = algebraMap R L :=
      RingHom.ext fun r => by
        simp only [RingHom.comp_apply, RingEquiv.coe_toRingHom]
        rw [← hcomp, RingEquiv.symm_apply_apply]
    rw [this]
    exact hPLc
  -- `P₁ ⊆ Q₁`
  have hP₁Q₁ : P₁ ≤ Q₁ := by
    have h1 : (Q.map (algebraMap R L)).comap (e.symm : L₁ →+* L) = maximalIdeal L₁ := by
      refine (Ideal.comap_symm (I := Q.map (algebraMap R L)) e).trans ?_
      rw [Localization.AtPrime.map_eq_maximalIdeal]
      exact IsLocalRing.map_ringEquiv_maximalIdeal e
    intro y hy
    have hy' : algebraMap t.ring L₁ y ∈ (P.map (algebraMap R L)).comap (e.symm : L₁ →+* L) := hy
    have h2 : (P.map (algebraMap R L)).comap (e.symm : L₁ →+* L) ≤ maximalIdeal L₁ := by
      rw [← h1]
      exact Ideal.comap_mono (Ideal.map_mono hPQ)
    have h3 := h2 hy'
    exact (IsLocalization.AtPrime.to_map_mem_maximal_iff L₁ Q₁ y).mp h3
  -- `J₁ ⊆ P₁`
  have hx'unit : ∀ x' : t.ring, Ideal.span {x'} = (maximalIdeal R).map t.toRing → x' ∉ Q₁ := by
    intro x' hx' hx'mem
    apply hxQ₁
    have hmem : t.toRing t.x ∈ (maximalIdeal R).map t.toRing := Ideal.mem_map_of_mem _ t.x_mem
    rw [← hx'] at hmem
    exact (Ideal.span_singleton_le_iff_mem _).mpr hx'mem hmem
  have hJ₁P₁ : strictTransformIdeal t J ≤ P₁ := by
    rw [strictTransformIdeal, Ideal.span_le]
    rintro y ⟨x', hx', f', hf', ν', -, hy⟩
    have hx'Q : x' ∉ Q₁ := hx'unit x' hx'
    have hx'P : x' ∉ P₁ := fun h => hx'Q (hP₁Q₁ h)
    have hf'P : t.toRing f' ∈ P₁ := by
      show algebraMap t.ring L₁ (t.toRing f') ∈
        (P.map (algebraMap R L)).comap (e.symm : L₁ →+* L)
      show e.symm (algebraMap t.ring L₁ (t.toRing f')) ∈ P.map (algebraMap R L)
      rw [← hcomp, RingEquiv.symm_apply_apply]
      exact Ideal.mem_map_of_mem _ (hJP hf')
    have hmem : x' ^ ν' * y ∈ P₁ := by
      rw [hy]
      exact hf'P
    rcases hP₁prime.mem_or_mem hmem with h | h
    · exact absurd (hP₁prime.mem_of_pow_mem _ h) hx'P
    · exact h
  -- `R₁/P₁` is regular
  have hPM : P ≤ maximalIdeal R := hPQ.trans (le_maximalIdeal Ideal.IsPrime.ne_top')
  have hPneM : P ≠ maximalIdeal R := fun h => hMQ (le_antisymm
    (h ▸ hPQ) (le_maximalIdeal Ideal.IsPrime.ne_top'))
  have : IsRegularLocalRing (R ⧸ maximalIdeal R) := by
    let _ : Field (R ⧸ maximalIdeal R) := Ideal.Quotient.field _
    infer_instance
  have hP₁reg : IsRegularLocalRing (t.ring ⧸ P₁) :=
    MonoidalTransform.isRegularLocalRing_quotient_of_comap_eq_of_lt (maximalIdeal R) P hPM
      hPneM t P₁ hP₁comap
  -- `J₁(R₁)_{Q₁} = e (J R_Q)`
  have hJ₁L : (strictTransformIdeal t J).map (algebraMap t.ring L₁) =
      (J.map (algebraMap R L)).map (e : L →+* L₁) := by
    have h1 : (strictTransformIdeal t J).map (algebraMap t.ring L₁) =
        (J.map t.toRing).map (algebraMap t.ring L₁) := by
      apply le_antisymm
      · rw [Ideal.map_le_iff_le_comap, strictTransformIdeal, Ideal.span_le]
        rintro y ⟨x', hx', f', hf', ν', -, hy⟩
        have hx'Q : x' ∉ Q₁ := hx'unit x' hx'
        have hu : IsUnit (algebraMap t.ring L₁ x' ^ ν') :=
          (IsLocalization.map_units L₁ (⟨x', hx'Q⟩ : Q₁.primeCompl)).pow ν'
        rw [SetLike.mem_coe, Ideal.mem_comap,
          ← Ideal.unit_mul_mem_iff_mem _ hu, ← map_pow, ← map_mul, hy]
        exact Ideal.mem_map_of_mem _ (Ideal.mem_map_of_mem _ hf')
      · apply Ideal.map_mono
        rw [Ideal.map_le_iff_le_comap]
        intro f' hf'
        exact Ideal.subset_span ⟨t.xR, t.span_xR_eq_map, f', hf', 0, by simp, by simp⟩
    rw [h1, Ideal.map_map, Ideal.map_map]
    congr 1
    exact RingHom.ext fun r => (hcomp r).symm
  -- transport of the normal flatness along `e`
  refine ⟨P₁, hP₁prime, hP₁comap, hP₁Q₁, hJ₁P₁, hP₁reg, ?_⟩
  exact isNormallyFlatAlongIdeal_mod_map_ringEquiv e _ _ _ _ hJ₁L hP₁L hflat

end TransformStep

section CurveFlatness

attribute [local instance] RingHom.ker_isPrime

variable {F : Type u} [Field F] {S₀ : Type u} [CommRing S₀] [Algebra S₀ F]
  (W : Subalgebra S₀ F)

-- the induction quantifies over `[IsRegularLocalRing R]` and `[IsDomain R]`, as `CurveResolvable`
set_option linter.overlappingInstances false in
/-- **The dimension-one case of Corollary 2** (p. 261: "Let us first consider the case of
`dim(R/Q) = 1`"), following the printed text: "Let us take a monoidal transform `R₁` of `R` with
center `M` which is residually algebraic over `R` and such that there exists a prime ideal `Q₁` in
`R₁` with `Q₁ ∩ R = Q`. Let `J₁` be the strict transform of `J` in `R₁`. Let `x` be an element of
`M`
such that `(x)R₁ = MR₁`, and `g_j' = g_j x^{-ν_j}` for each `j`, where `ν_j = ν_M(g_j)`. Then, by
Corollary 3 (b) of Theorem 5, § 6, the assumptions (i) and (ii) remain valid for `R₁`, `M₁`, `Q₁`,
`J₁`, and the system `(g₁', …, g_m')`. Moreover, if `P₁` is the prime ideal in `R₁` with
`P₁ ∩ R = P`, then Proposition 2 shows that the flatness of `gr_P(R/J)` over `R/P` follows the same
of `gr_{P₁}(R₁/J₁)` over `R₁/P₁`. Furthermore, `R_Q = (R₁)_{Q₁}`, `JR_Q = J₁(R₁)_{Q₁}`, and
`PR_Q = P₁(R₁)_{Q₁}`. Therefore, in order to prove the assertion of Corollary 2, we may replace
`R`, `J`, `Q`, and `P` by `R₁`, `J₁`, `Q₁`, and `P₁` respectively. We know that the assertion is
verified if `R/Q` is regular, […] If `R₁/Q₁` is not regular, we repeat the same process as above.
As is easily seen, the process cannot be repeated infinitely many times."

The pair `(R₁, Q₁)` is arbitrary: only its properties are used (centre `M`, residually algebraic,
`Q₁ ∩ R = Q`).  Gaps of the paper filled: such a pair exists
(`exists_monoidalTransform_curveImage_lt`), and for every such pair `φ(R₁)` is again a localization
of `φ(R₁) ∩ W` and the `S₀`-submodule `φ(R) ∩ W` of the noetherian module `W` strictly increases
(`exists_ringHom_curveImage_lt_of_comap_eq`): this is the proof of "the process cannot be repeated
infinitely many times", by induction on that submodule.  At each step the prime `P₁` with
`P₁ ∩ R = P` (`exists_prime_of_localRingHom_bijective`) is used: the induction hypothesis gives that
`P₁` is a permissible center for `J₁`, and Proposition 2 (with centre `M`) that `P` is one for
`J`. -/
@[blueprint "lem:III.8-cor2-curve"
  (statement := /-- Let $R$ be a regular local ring whose residue field has characteristic zero,
    $\varphi\colon R\to F$ a ring homomorphism into a field with kernel $Q$ whose image lies in
    the integral closure $W$ of $R/Q$ localized at units, $(g_j)$ a system without zeros with
    properties (i), (ii), and $P\subseteq Q$ a prime ideal with $R/P$ regular and $P\supseteq J$.
    If $PR_Q$ is normally flat modulo $JR_Q$, then $P$ is normally flat modulo $J$ (assuming
    Proposition~2). -/)
  (proof := /-- Induction on the submodule $\varphi(R)\cap W$ of the noetherian module $W$ as in
    \cref{cor:III.thm5-3c}: if $R/Q$ is regular use \cref{lem:III.8-cor2-regular-case}; otherwise
    take a monoidal transform $R_1$ of $R$ with center $M$, residually algebraic over $R$, and a
    prime $Q_1$ of $R_1$ with $Q_1\cap R=Q$ (it exists, and for any such pair
    $\varphi(R_1)\cap W$ strictly contains $\varphi(R)\cap W$, as in \cref{cor:III.thm5-3c}),
    the prime $P_1$ of \cref{lem:III.8-cor2-transform-step}, the system $(h_j)$ of
    \cref{cor:III.thm5-3b} (which also gives $\nu^*(J_1)=\nu^*(J)$), the induction hypothesis for
    $R_1$, and Proposition~2 with center $M$ ($M$ is a permissible center for $J$ by
    \cref{cor:III.thm5-3a}). -/)
  (latexEnv := "lemma")]
theorem isNormallyFlatAlongIdeal_of_curveImage_eq [Hironaka.Cited.CurveFiniteIntegralClosure.{u}] [Hironaka.Cited.ExistsSurjectiveOfIsRegularLocalRingOfIsAdicComplete.{u}] [Hironaka.Cited.IsRegularLocalRingLocalizationOfIsRegularLocalRing.{u}] [Hironaka.Cited.IsSeparableFieldExtensionIff.{u}] (hprop2 : Proposition2Statement.{u})
    [Module.Finite S₀ W] [IsNoetherianRing S₀] [IsDedekindDomain W]
    (hWfin : {n : Ideal W | n.IsMaximal}.Finite) (hS₀ : ∀ n : ℕ, n ≠ 0 → IsUnit (n : S₀))
    (N : Submodule S₀ W) :
    ∀ {R : Type u} [CommRing R] [IsRegularLocalRing R] [IsDomain R] [CharZero (ResidueField R)]
      (φ : R →+* F) (hφS : ∀ s, algebraMap S₀ F s ∈ φ.range),
      (∀ r, ∃ b, b ∉ maximalIdeal R ∧ φ b ∈ W ∧ φ (b * r) ∈ W) →
      curveImage W φ hφS = N → ∀ (J : Ideal R), J ≤ RingHom.ker φ → ∀ {m : ℕ} (g : Fin m → R),
      (∀ j, g j ≠ 0) → IsLocallyAdaptedSystem R (RingHom.ker φ) J g →
      ∀ (P : Ideal R) [P.IsPrime], J ≤ P → P ≤ RingHom.ker φ → IsRegularLocalRing (R ⧸ P) →
      IsNormallyFlatAlongIdeal
        ((P.map (algebraMap R (Localization.AtPrime (RingHom.ker φ)))).map
          (Ideal.Quotient.mk (J.map (algebraMap R (Localization.AtPrime (RingHom.ker φ)))))) →
      IsNormallyFlatAlongIdeal (P.map (Ideal.Quotient.mk J)) := by
  induction N using WellFoundedGT.induction with
  | _ N ih =>
  intro R _ _ _ _ φ hφS hInv hN J hJ m g hg0 hg P _ hJP hPQ hPreg hflat
  have _ := hPreg
  by_cases hS : IsRegularLocalRing (R ⧸ RingHom.ker φ)
  · exact isNormallyFlatAlongIdeal_of_isRegularLocalRing_quotient_of_localization _ J P hJP hPQ g
      hg hflat
  -- "Let us take a monoidal transform `R₁` of `R` with center `M` which is residually algebraic
  -- over `R` and such that there exists a prime ideal `Q₁` in `R₁` with `Q₁ ∩ R = Q`": it exists
  obtain ⟨t, φ₀, hP₀, -, halg, hreg, -⟩ :=
    exists_monoidalTransform_curveImage_lt W hWfin hS₀ φ hφS hInv hS
  -- and for ANY such `R₁` and `Q₁`: `R₁/Q₁` is again of the same kind and the measure strictly
  -- increases ("the process cannot be repeated infinitely many times")
  obtain ⟨φ', hker', -, hxP, hInv', hφ'S, hlt⟩ := exists_ringHom_curveImage_lt_of_comap_eq W hWfin
    hS₀ φ hφS hInv hS t (RingHom.ker φ₀) hP₀.symm
  have hP' : RingHom.ker φ = (RingHom.ker φ').comap t.toRing := by rw [hker']; exact hP₀
  have hbij := MonoidalTransform.localRingHom_bijective_of_x_notMem t (RingHom.ker φ) _ hP' hxP
  have _ : IsRegularLocalRing t.ring := hreg
  have _ : CharZero (ResidueField t.ring) :=
    (RingHom.charZero_iff (ResidueField.map t.toRing).injective).mp inferInstance
  -- residually algebraic, hence residually separable algebraic (characteristic zero)
  have hsep : RingHom.IsResiduallySeparableAlgebraic (R := R) (R' := t.ring) t.toRing := by
    let _ := (ResidueField.map t.toRing).toAlgebra
    have : Algebra.IsAlgebraic (ResidueField R) (ResidueField t.ring) := halg
    exact Algebra.IsAlgebraic.isSeparable_of_perfectField
  have hQM : RingHom.ker φ ≤ maximalIdeal R := le_maximalIdeal (Ideal.IsPrime.ne_top inferInstance)
  have hMQ : maximalIdeal R ≠ RingHom.ker φ := by
    intro h
    apply hS
    have : (RingHom.ker φ).IsMaximal := h ▸ maximalIdeal.isMaximal R
    let _ := Ideal.Quotient.field (RingHom.ker φ)
    infer_instance
  have _ : IsRegularLocalRing (R ⧸ maximalIdeal R) := by
    let _ : Field (R ⧸ maximalIdeal R) := Ideal.Quotient.field _
    infer_instance
  -- (a): `M` is a permissible center for `J`
  have hperm := isPermissibleCenter_of_isLocallyAdaptedSystem _ J hJ g hg (maximalIdeal R) hQM
  -- `ν_j = ν_M(g_j)` and `h_j = x^{-ν_j} g_j`
  have hν : ∀ j, (((Ideal.ordElem (maximalIdeal R) (g j)).toNat : ℕ) : ℕ∞) =
      Ideal.ordElem (maximalIdeal R) (g j) := fun j =>
    ENat.natCast_toNat ((Ideal.ordElem_eq_top_iff_eq_zero (maximalIdeal.isMaximal R).ne_top).not.mpr
      (hg0 j))
  have hex : ∀ j, ∃ hj : t.ring,
      t.toRing t.x ^ (Ideal.ordElem (maximalIdeal R) (g j)).toNat * hj = t.toRing (g j) := by
    intro j
    have hmem : g j ∈ maximalIdeal R ^ (Ideal.ordElem (maximalIdeal R) (g j)).toNat :=
      Ideal.mem_pow_of_ordElem (hν j).symm
    have : t.toRing (g j) ∈ Ideal.span {t.xR ^ (Ideal.ordElem (maximalIdeal R) (g j)).toNat} := by
      rw [← Ideal.span_singleton_pow, t.span_xR_eq_map, ← Ideal.map_pow]
      exact Ideal.mem_map_of_mem _ hmem
    obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.mp this
    exact ⟨a, by rw [mul_comm]; exact ha⟩
  choose h hh using hex
  -- (b): the transformed system has the properties (i), (ii) for `R₁`, `Q₁`, `J₁`
  obtain ⟨hg₁, hnu⟩ := isLocallyAdaptedSystem_strictTransform (RingHom.ker φ) J hJ g hg
    (maximalIdeal R) hperm hQM hMQ t hsep (RingHom.ker φ') hP'.symm t.x t.x_mem
    t.span_xR_eq_map.symm (fun j => (Ideal.ordElem (maximalIdeal R) (g j)).toNat) hν h hh
  -- `J₁ ⊆ Q₁`
  have hJ₁ : strictTransformIdeal t J ≤ RingHom.ker φ' := by
    rw [strictTransformIdeal, Ideal.span_le]
    rintro y ⟨x', hx', f', hf', ν', -, hy⟩
    have hx'Q : x' ∉ RingHom.ker φ' := by
      intro hx'mem
      apply hxP
      have hmem : t.toRing t.x ∈ (maximalIdeal R).map t.toRing := Ideal.mem_map_of_mem _ t.x_mem
      rw [← hx'] at hmem
      rw [hP']
      exact (Ideal.span_singleton_le_iff_mem _).mpr hx'mem hmem
    have hmem : x' ^ ν' * y ∈ RingHom.ker φ' := by
      rw [hy]
      have : f' ∈ (RingHom.ker φ').comap t.toRing := hP' ▸ hJ hf'
      exact this
    rcases (inferInstance : (RingHom.ker φ').IsPrime).mem_or_mem hmem with h' | h'
    · exact absurd ((inferInstance : (RingHom.ker φ').IsPrime).mem_of_pow_mem _ h') hx'Q
    · exact h'
  have hh0 : ∀ j, h j ≠ 0 := by
    intro j h0
    apply hg0 j
    apply t.toRing_injective
    rw [← hh j, h0, mul_zero, map_zero]
  -- the prime `P₁` of `R₁` over `P`
  obtain ⟨P₁, hP₁prime, hP₁comap, hP₁Q₁, hJ₁P₁, hP₁reg, hflat₁⟩ :=
    exists_prime_of_localRingHom_bijective (RingHom.ker φ) J P hJP hPQ hMQ t (RingHom.ker φ') hP'
      hbij hxP hflat
  -- the induction hypothesis: `P₁` is a permissible center for `J₁`
  have h₁ := ih _ (hN ▸ hlt) φ' hφ'S hInv' rfl (strictTransformIdeal t J) hJ₁ h hh0 hg₁ P₁ hJ₁P₁
    hP₁Q₁ hP₁reg hflat₁
  have hperm₁ : IsPermissibleCenter t.ring (strictTransformIdeal t J) P₁ :=
    Or.inr ⟨hP₁prime, hJ₁P₁, hP₁reg, h₁⟩
  -- Proposition 2 with centre `M`
  have hMP : maximalIdeal R ≠ P := fun h' => hMQ
    (le_antisymm (le_maximalIdeal Ideal.IsPrime.ne_top') (h' ▸ hPQ) |>.symm)
  have hP2 := hprop2 R ringChar_eq_of_charZero_residueField J P (maximalIdeal R)
    (hPQ.trans hQM) hJP hMP hperm t hsep P₁ hP₁comap hnu.symm hperm₁
  exact (hP2.resolve_left (Ideal.IsPrime.ne_top inferInstance)).2.2.2

/-- Wrapper of `isNormallyFlatAlongIdeal_of_curveImage_eq` for a prime `Q` with `ker φ = Q`. -/
theorem isNormallyFlatAlongIdeal_of_curve [Hironaka.Cited.CurveFiniteIntegralClosure.{u}] [Hironaka.Cited.ExistsSurjectiveOfIsRegularLocalRingOfIsAdicComplete.{u}] [Hironaka.Cited.IsRegularLocalRingLocalizationOfIsRegularLocalRing.{u}] [Hironaka.Cited.IsSeparableFieldExtensionIff.{u}] (hprop2 : Proposition2Statement.{u})
    [Module.Finite S₀ W] [IsNoetherianRing S₀] [IsDedekindDomain W]
    (hWfin : {n : Ideal W | n.IsMaximal}.Finite) (hS₀ : ∀ n : ℕ, n ≠ 0 → IsUnit (n : S₀))
    {R : Type u} [CommRing R] [IsRegularLocalRing R] [IsDomain R] [CharZero (ResidueField R)]
    (φ : R →+* F) (hφS : ∀ s, algebraMap S₀ F s ∈ φ.range)
    (hInv : ∀ r, ∃ b, b ∉ maximalIdeal R ∧ φ b ∈ W ∧ φ (b * r) ∈ W)
    (Q : Ideal R) [Q.IsPrime] (hker : RingHom.ker φ = Q) (J : Ideal R) (hJ : J ≤ Q) {m : ℕ}
    (g : Fin m → R) (hg0 : ∀ j, g j ≠ 0) (hg : IsLocallyAdaptedSystem R Q J g)
    (P : Ideal R) [P.IsPrime] (hJP : J ≤ P) (hPQ : P ≤ Q) (hPreg : IsRegularLocalRing (R ⧸ P))
    (hflat : IsNormallyFlatAlongIdeal
      ((P.map (algebraMap R (Localization.AtPrime Q))).map
        (Ideal.Quotient.mk (J.map (algebraMap R (Localization.AtPrime Q)))))) :
    IsNormallyFlatAlongIdeal (P.map (Ideal.Quotient.mk J)) := by
  subst hker
  exact isNormallyFlatAlongIdeal_of_curveImage_eq W hprop2 hWfin hS₀ _ φ hφS hInv rfl J hJ g hg0
    hg P hJP hPQ hPreg hflat

end CurveFlatness

section DimensionLEOne

/-- **Corollary 2 for `dim(R/Q) ≤ 1`** (p. 261: "Let us first consider the case of `dim(R/Q) = 1`"),
under the finiteness condition on the integral closure of `R/Q` (which holds for `R` complete,
"the integral closure of `R/Q` in its field of quotients is a finite `R/Q`-module").

The proof is the printed one, as for Corollary 3 (c)
(`grIdeal_localization_eq_span_initialForm_of_dimensionLEOne`): "Let us take a monoidal transform
`R₁` of `R` with center `M` which is residually algebraic over `R` and such that there exists a
prime ideal `Q₁` in `R₁` with `Q₁ ∩ R = Q`" is an arbitrary such pair `(R₁, Q₁)`; the paper does not
say that one exists (gap filled: `exists_monoidalTransform_curveImage_lt`), and for the arbitrary
pair the invariant "`φ(R₁)` is a localization of `φ(R₁) ∩ W`" and the strict increase of the
`R/Q`-submodule `φ(R) ∩ W` of the finite module `W` (the integral closure of `R/Q`), that is "the
process cannot be repeated infinitely many times", are
`exists_ringHom_curveImage_lt_of_comap_eq`.  This needs only the finiteness of `W`, not that `R` is
complete. -/
@[blueprint "lem:III.8-cor2-dimension-one"
  (statement := /-- Let $R$ be a regular local ring whose residue field has characteristic zero,
    $Q\supseteq J$ a prime ideal with $\dim(R/Q)\le1$ whose integral closure in its field of
    quotients is a finite $R/Q$-module, $(g_j)$ a system with properties (i), (ii), and
    $J\subseteq P\subseteq Q$ with $P$ prime and $R/P$ regular. If $PR_Q$ is normally flat
    modulo $JR_Q$, then $P$ is normally flat modulo $J$ (assuming Proposition~2). -/)
  (proof := /-- Apply \cref{lem:III.8-cor2-curve} to $\varphi\colon R\to\operatorname{Frac}(R/Q)$
    and $W$ the integral closure of $R/Q$. -/)
  (latexEnv := "lemma")]
theorem isNormallyFlatAlongIdeal_of_dimensionLEOne [Hironaka.Cited.CurveFiniteIntegralClosure.{u}] [Hironaka.Cited.ExistsSurjectiveOfIsRegularLocalRingOfIsAdicComplete.{u}] [Hironaka.Cited.IsRegularLocalRingLocalizationOfIsRegularLocalRing.{u}] [Hironaka.Cited.IsSeparableFieldExtensionIff.{u}] (hprop2 : Proposition2Statement.{u})
    {R : Type u} [CommRing R] [IsRegularLocalRing R] [CharZero (ResidueField R)]
    (Q J : Ideal R) [Q.IsPrime] (hJQ : J ≤ Q) {m : ℕ} (g : Fin m → R) (hg0 : ∀ j, g j ≠ 0)
    (hg : IsLocallyAdaptedSystem R Q J g) (hdim : Ring.DimensionLEOne (R ⧸ Q))
    (hfin : Module.Finite (R ⧸ Q) (integralClosure (R ⧸ Q) (FractionRing (R ⧸ Q))))
    (P : Ideal R) [P.IsPrime] (hJP : J ≤ P) (hPQ : P ≤ Q) (hPreg : IsRegularLocalRing (R ⧸ P))
    (hflat : IsNormallyFlatAlongIdeal
      ((P.map (algebraMap R (Localization.AtPrime Q))).map
        (Ideal.Quotient.mk (J.map (algebraMap R (Localization.AtPrime Q)))))) :
    IsNormallyFlatAlongIdeal (P.map (Ideal.Quotient.mk J)) := by
  have _ : IsDomain R := Transforms.isDomain_of_isRegularLocalRing R
  have _ : IsLocalRing (R ⧸ Q) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk Q) Ideal.Quotient.mk_surjective
  set W := integralClosure (R ⧸ Q) (FractionRing (R ⧸ Q))
  have := hdim
  have : IsNoetherianRing W := IsNoetherianRing.of_finite (R ⧸ Q) W
  have : IsIntegrallyClosed W :=
    integralClosure.isIntegrallyClosedOfFiniteExtension (FractionRing (R ⧸ Q))
  have : IsDedekindDomain W := { }
  have hWfin : {n : Ideal W | n.IsMaximal}.Finite := finite_setOf_isMaximal (S₀ := R ⧸ Q)
  -- the non-zero integers are units (the residue field has characteristic zero)
  have hS₀ : ∀ n : ℕ, n ≠ 0 → IsUnit (n : R ⧸ Q) := by
    intro n hn
    have hres : IsLocalRing.residue R (n : R) ≠ 0 := by
      rw [map_natCast]
      exact Nat.cast_ne_zero.mpr hn
    have hu : IsUnit (n : R) := by
      by_contra h
      exact hres ((IsLocalRing.residue_eq_zero_iff _).mpr ((IsLocalRing.mem_maximalIdeal _).mpr h))
    simpa using hu.map (Ideal.Quotient.mk Q)
  let φ : R →+* FractionRing (R ⧸ Q) :=
    (algebraMap (R ⧸ Q) (FractionRing (R ⧸ Q))).comp (Ideal.Quotient.mk Q)
  have hφS : ∀ s, algebraMap (R ⧸ Q) (FractionRing (R ⧸ Q)) s ∈ φ.range := by
    intro s
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective s
    exact ⟨r, rfl⟩
  have hInv : ∀ r, ∃ b, b ∉ maximalIdeal R ∧ φ b ∈ W ∧ φ (b * r) ∈ W := fun r =>
    ⟨1, fun h => (maximalIdeal.isMaximal R).ne_top ((Ideal.eq_top_iff_one _).mpr h),
      W.algebraMap_mem _, W.algebraMap_mem _⟩
  have hker : RingHom.ker φ = Q := by
    rw [RingHom.ker_comp_of_injective _ (IsFractionRing.injective _ _), Ideal.mk_ker]
  exact isNormallyFlatAlongIdeal_of_curve W hprop2 hWfin hS₀ φ hφS hInv Q hker J hJQ g hg0 hg P
    hJP hPQ hPreg hflat

end DimensionLEOne

section AdjacentPrimes

/-- **The induction assumption applied to `R_{Q'}`** (p. 261: "By Corollary 3 (c) of Theorem 5,
§ 6, the assumptions (i) and (ii) remain valid if we replace `R`, `Q`, `J`, and `M` by `R_{Q'}`,
`QR_{Q'}`, `JR_{Q'}`, and `Q'R_{Q'}`, respectively. Therefore, by the induction assumption, the
flatness of `gr_{PR_Q}(R_Q/JR_Q)` over `R_Q/PR_Q` implies the same of
`gr_{PR_{Q'}}(R_{Q'}/JR_{Q'})` over `R_{Q'}/PR_{Q'}`"): for primes `Q ⊆ Q'` such that (i), (ii)
hold for `R_{Q'}` and `QR_{Q'}` (hypotheses `hA`, `hB`), `R_Q = (R_{Q'})_{QR_{Q'}}`, and the
assertion of Corollary 2 for the regular local rings of dimension `dim(R_{Q'}/QR_{Q'}) = n'`, the
flatness of `PR_Q` modulo `JR_Q` gives that of `PR_{Q'}` modulo `JR_{Q'}`. -/
@[blueprint "lem:III.8-cor2-adjacent"
  (statement := /-- Let $R$ be a regular local ring whose residue field has characteristic zero,
    $Q\subseteq Q'$ primes of $R$ and $(g_j)$ a system with (i), (ii) for $Q$, and with (i), (ii)
    for $R_{Q'}$, $QR_{Q'}$, $JR_{Q'}$ (\cref{cor:III.thm5-3c}). If Corollary~2
    (\cref{cor:III.prop2-2}) holds for the regular local rings of dimension
    $\dim(R_{Q'}/QR_{Q'})$ and $\operatorname{gr}_{PR_Q}(R_Q/JR_Q)$ is flat over $R_Q/PR_Q$, then
    $\operatorname{gr}_{PR_{Q'}}(R_{Q'}/JR_{Q'})$ is flat over $R_{Q'}/PR_{Q'}$. -/)
  (proof := /-- $R_Q=(R_{Q'})_{QR_{Q'}}$, and (i), (ii) hold for $R_{Q'}$, $QR_{Q'}$ by hypothesis;
    $R_{Q'}/PR_{Q'}$ is regular. Apply the induction assumption to $R_{Q'}$ and its prime
    $QR_{Q'}$. -/)
  (latexEnv := "lemma")]
theorem isNormallyFlatAlongIdeal_localization_of_le [Hironaka.Cited.IsRegularLocalRingLocalizationOfIsRegularLocalRing.{u}] {n' : ℕ} (hstmt : Corollary2Dim.{u} n')
    {R : Type u} [CommRing R] [IsRegularLocalRing R] [CharZero (ResidueField R)]
    (Q Q' J : Ideal R) [Q.IsPrime] [Q'.IsPrime] (hQQ' : Q ≤ Q') {m : ℕ}
    (g : Fin m → R) (hg : IsLocallyAdaptedSystem R Q J g)
    (hA : grIdeal (Q'.map (algebraMap R (Localization.AtPrime Q')))
        (J.map (algebraMap R (Localization.AtPrime Q'))) =
      Ideal.span (Set.range fun j =>
        initialForm (Q'.map (algebraMap R (Localization.AtPrime Q')))
          (algebraMap R (Localization.AtPrime Q') (g j))))
    (hB : ∀ j, Ideal.ordElem (Q'.map (algebraMap R (Localization.AtPrime Q')))
        (algebraMap R (Localization.AtPrime Q') (g j)) =
      Ideal.ordElem (Q.map (algebraMap R (Localization.AtPrime Q)))
        (algebraMap R (Localization.AtPrime Q) (g j)))
    (hdim : ringKrullDim (Localization.AtPrime Q' ⧸
      Q.map (algebraMap R (Localization.AtPrime Q'))) = n')
    (P : Ideal R) [P.IsPrime] (hJP : J ≤ P) (hPQ : P ≤ Q) (hPreg : IsRegularLocalRing (R ⧸ P))
    (hflat : IsNormallyFlatAlongIdeal
      ((P.map (algebraMap R (Localization.AtPrime Q))).map
        (Ideal.Quotient.mk (J.map (algebraMap R (Localization.AtPrime Q)))))) :
    IsNormallyFlatAlongIdeal
      ((P.map (algebraMap R (Localization.AtPrime Q'))).map
        (Ideal.Quotient.mk (J.map (algebraMap R (Localization.AtPrime Q'))))) := by
  classical
  have _ : IsDomain R := Transforms.isDomain_of_isRegularLocalRing R
  have _ : IsRegularLocalRing (Localization.AtPrime Q') :=
    isRegularLocalRing_localization_of_isRegularLocalRing R Q'
  have hdisj : Disjoint (Q'.primeCompl : Set R) (Q : Set R) :=
    Set.disjoint_left.mpr fun a ha haQ => ha (hQQ' haQ)
  have _ : (Q.map (algebraMap R (Localization.AtPrime Q'))).IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint Q'.primeCompl _ Q inferInstance hdisj
  have hQ : Q = (Q.map (algebraMap R (Localization.AtPrime Q'))).comap
      (algebraMap R (Localization.AtPrime Q')) :=
    (IsLocalization.under_map_of_isPrime_disjoint Q'.primeCompl _ inferInstance hdisj).symm
  -- the residue field of `R_{Q'}` has characteristic zero (`ℚ ⊆ R`)
  have _ : CharZero (ResidueField (Localization.AtPrime Q')) := by
    refine charZero_of_inj_zero fun n hn => ?_
    by_contra hn0
    have hres : residue R (n : R) ≠ 0 := by
      rw [map_natCast]
      exact Nat.cast_ne_zero.mpr hn0
    have hu : IsUnit (n : R) := by
      by_contra h
      exact hres ((residue_eq_zero_iff _).mpr ((mem_maximalIdeal _).mpr h))
    have hu' := (hu.map (algebraMap R (Localization.AtPrime Q'))).map
      (residue (Localization.AtPrime Q'))
    rw [map_natCast, map_natCast, hn] at hu'
    exact not_isUnit_zero hu'
  set ψ := Localization.localRingHom Q (Q.map (algebraMap R (Localization.AtPrime Q')))
    (algebraMap R (Localization.AtPrime Q')) hQ
  have hψ : Function.Bijective ψ := Localization.localRingHom_bijective_of_eq_comap_map Q Q' hQ
  have hψ_map : ∀ r, ψ (algebraMap R (Localization.AtPrime Q) r) =
      algebraMap (Localization.AtPrime Q') (Localization.AtPrime
        (Q.map (algebraMap R (Localization.AtPrime Q')))) (algebraMap R _ r) :=
    Localization.localRingHom_to_map _ _ _ hQ
  have hψmax : (Q.map (algebraMap R (Localization.AtPrime Q))).map ψ =
      (Q.map (algebraMap R (Localization.AtPrime Q'))).map (algebraMap
        (Localization.AtPrime Q') (Localization.AtPrime
          (Q.map (algebraMap R (Localization.AtPrime Q'))))) := by
    rw [Localization.AtPrime.map_eq_maximalIdeal, Localization.AtPrime.map_eq_maximalIdeal]
    exact map_maximalIdeal_of_surjective ψ hψ.2
  -- (i) and (ii) for `R_{Q'}`, `QR_{Q'}`, `JR_{Q'}` and the images of the `g_j`
  have hg' : IsLocallyAdaptedSystem (Localization.AtPrime Q')
      (Q.map (algebraMap R (Localization.AtPrime Q')))
      (J.map (algebraMap R (Localization.AtPrime Q')))
      (fun j => algebraMap R (Localization.AtPrime Q') (g j)) := by
    refine ⟨fun j => Ideal.mem_map_of_mem _ (hg.1 j), ?_, fun j => ?_⟩
    · have h := hA
      rwa [Localization.AtPrime.map_eq_maximalIdeal] at h
    · have h1 := Ideal.ordElem_map_of_bijective ψ hψ (Q.map (algebraMap R
        (Localization.AtPrime Q))) (algebraMap R (Localization.AtPrime Q) (g j))
      rw [hψmax, hψ_map] at h1
      rw [← Localization.AtPrime.map_eq_maximalIdeal, hB j, h1]
  -- the prime `PR_{Q'}` of `R_{Q'}` and its regular quotient
  have hdisjP : Disjoint (Q'.primeCompl : Set R) (P : Set R) :=
    Set.disjoint_left.mpr fun a ha haP => ha (hQQ' (hPQ haP))
  have hP'prime : (P.map (algebraMap R (Localization.AtPrime Q'))).IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint Q'.primeCompl _ P inferInstance hdisjP
  have hP'reg : IsRegularLocalRing (Localization.AtPrime Q' ⧸
      P.map (algebraMap R (Localization.AtPrime Q'))) := by
    have hPQ' : P ≤ Q' := hPQ.trans hQQ'
    have hmapprime : (Q'.map (Ideal.Quotient.mk P)).IsPrime :=
      Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective
        (by rw [Ideal.mk_ker]; exact hPQ')
    have : IsRegularLocalRing (Localization.AtPrime (Q'.map (Ideal.Quotient.mk P))) :=
      isRegularLocalRing_localization_of_isRegularLocalRing (R ⧸ P) _
    obtain ⟨e, -⟩ := Ideal.exists_ringEquiv_localization_quotient_of_le P Q' hPQ'
    exact IsRegularLocalRing.of_ringEquiv e.symm
  -- transport of the hypothesis along `ψ`
  have hflat' : IsNormallyFlatAlongIdeal
      (((P.map (algebraMap R (Localization.AtPrime Q'))).map (algebraMap
        (Localization.AtPrime Q') (Localization.AtPrime
          (Q.map (algebraMap R (Localization.AtPrime Q')))))).map
        (Ideal.Quotient.mk ((J.map (algebraMap R (Localization.AtPrime Q'))).map (algebraMap
          (Localization.AtPrime Q') (Localization.AtPrime
            (Q.map (algebraMap R (Localization.AtPrime Q')))))))) := by
    refine isNormallyFlatAlongIdeal_mod_map_ringEquiv (RingEquiv.ofBijective ψ hψ)
      (J.map (algebraMap R (Localization.AtPrime Q)))
      (P.map (algebraMap R (Localization.AtPrime Q))) _ _ ?_ ?_ hflat
    · rw [Ideal.map_map, Ideal.map_map]
      congr 1
      exact RingHom.ext fun r => (hψ_map r).symm
    · rw [Ideal.map_map, Ideal.map_map]
      congr 1
      exact RingHom.ext fun r => (hψ_map r).symm
  exact hstmt (Localization.AtPrime Q') (Q.map (algebraMap R (Localization.AtPrime Q')))
    (J.map (algebraMap R (Localization.AtPrime Q'))) _ hg' _ (Ideal.map_mono hJP)
    (Ideal.map_mono hPQ) hP'reg hdim hflat'

end AdjacentPrimes

section CompleteCase

/-- If no prime lies strictly between `Q'` and the maximal ideal, then `R/Q'` has dimension `≤ 1`
(every non-zero prime of the domain `R/Q'` is maximal). -/
theorem dimensionLEOne_quotient_of_forall_prime_eq_or_eq {R : Type u} [CommRing R] [IsLocalRing R]
    (Q' : Ideal R) [Q'.IsPrime]
    (hmin : ∀ p : Ideal R, p.IsPrime → Q' ≤ p → p = Q' ∨ p = maximalIdeal R) :
    Ring.DimensionLEOne (R ⧸ Q') := by
  have hsurj : Function.Surjective (Ideal.Quotient.mk Q') := Ideal.Quotient.mk_surjective
  constructor
  intro pbar hp0 hpbar
  have hp : (pbar.comap (Ideal.Quotient.mk Q')).IsPrime := Ideal.comap_isPrime _ _
  have hQp : Q' ≤ pbar.comap (Ideal.Quotient.mk Q') := by
    intro x hx
    show Ideal.Quotient.mk Q' x ∈ pbar
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr hx]
    exact zero_mem _
  have hmap : (pbar.comap (Ideal.Quotient.mk Q')).map (Ideal.Quotient.mk Q') = pbar :=
    Ideal.map_comap_of_surjective _ hsurj pbar
  have _ : IsLocalRing (R ⧸ Q') :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk Q') hsurj
  rcases hmin _ hp hQp with h | h
  · exfalso
    apply hp0
    rw [← hmap, h, Ideal.map_quotient_self]
  · rw [← hmap, h, IsLocalRing.map_maximalIdeal_of_surjective _ hsurj]
    exact maximalIdeal.isMaximal _

/-- A prime `Q` with `dim(R/Q) = 1` has no prime strictly between `Q` and the maximal ideal. -/
theorem forall_prime_eq_or_eq_of_ringKrullDim_quotient_eq_one {R : Type u} [CommRing R]
    [IsLocalRing R] [IsNoetherianRing R] (Q : Ideal R) [Q.IsPrime]
    (hdim : ringKrullDim (R ⧸ Q) = 1) :
    ∀ p : Ideal R, p.IsPrime → Q ≤ p → p = Q ∨ p = maximalIdeal R := by
  classical
  intro p hp hQp
  by_contra hcon
  rw [not_or] at hcon
  have _ : IsLocalRing (R ⧸ Q) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk Q) Ideal.Quotient.mk_surjective
  have hsurj : Function.Surjective (Ideal.Quotient.mk Q) := Ideal.Quotient.mk_surjective
  have hpm : (p.map (Ideal.Quotient.mk Q)).IsPrime :=
    Ideal.map_isPrime_of_surjective hsurj (by rw [Ideal.mk_ker]; exact hQp)
  have hpmc : (p.map (Ideal.Quotient.mk Q)).comap (Ideal.Quotient.mk Q) = p := by
    rw [Ideal.comap_map_of_surjective _ hsurj, ← RingHom.ker_eq_comap_bot, Ideal.mk_ker]
    exact sup_eq_left.mpr hQp
  -- the points `⊥ < p/Q < ⊤` of `Spec (R/Q)`
  let a : PrimeSpectrum (R ⧸ Q) := ⟨⊥, inferInstance⟩
  let b : PrimeSpectrum (R ⧸ Q) := ⟨p.map (Ideal.Quotient.mk Q), hpm⟩
  have hab : a < b := by
    refine lt_of_le_of_ne bot_le fun h => hcon.1 ?_
    have : (⊥ : Ideal (R ⧸ Q)) = p.map (Ideal.Quotient.mk Q) := congrArg PrimeSpectrum.asIdeal h
    rw [← hpmc, ← this, ← RingHom.ker_eq_comap_bot, Ideal.mk_ker]
  have hbc : b < ⊤ := by
    refine lt_of_le_of_ne le_top fun h => hcon.2 ?_
    have h' : p.map (Ideal.Quotient.mk Q) = maximalIdeal (R ⧸ Q) := congrArg PrimeSpectrum.asIdeal h
    have hM : maximalIdeal (R ⧸ Q) = (maximalIdeal R).map (Ideal.Quotient.mk Q) :=
      (IsLocalRing.map_maximalIdeal_of_surjective _ hsurj).symm
    rw [← hpmc, h', hM, Ideal.comap_map_of_surjective _ hsurj, ← RingHom.ker_eq_comap_bot,
      Ideal.mk_ker]
    exact sup_eq_left.mpr (le_maximalIdeal (Ideal.IsPrime.ne_top ‹Q.IsPrime›))
  -- `height ⊤ ≥ 2`, contradicting `dim = 1`
  have h1 : Order.height a + 1 ≤ Order.height b := Order.height_add_one_le hab
  have h2 : Order.height b + 1 ≤ Order.height (⊤ : PrimeSpectrum (R ⧸ Q)) :=
    Order.height_add_one_le hbc
  have hhtM : Order.height (⊤ : PrimeSpectrum (R ⧸ Q)) = 1 := by
    have h3 := IsLocalRing.maximalIdeal_height_eq_ringKrullDim (R := R ⧸ Q)
    rw [hdim] at h3
    have h4 : (maximalIdeal (R ⧸ Q)).height = 1 := by exact_mod_cast h3
    have h5 := PrimeSpectrum.height_eq_orderHeight (⊤ : PrimeSpectrum (R ⧸ Q))
    exact h5 ▸ h4
  rw [hhtM] at h2
  have h6 : Order.height a + 1 + 1 ≤ 1 := (add_le_add_left h1 1).trans h2
  have h7 : (2 : ℕ∞) ≤ 1 := calc
    (2 : ℕ∞) = 0 + 1 + 1 := by norm_num
    _ ≤ Order.height a + 1 + 1 := by gcongr; exact bot_le
    _ ≤ 1 := h6
  norm_num at h7

/-- The integral closure of `R/Q` in its field of quotients is a finite `R/Q`-module for a prime
`Q` of a complete noetherian local ring `R` (p. 261: "Therefore, the integral closure of `R/Q` in
its field of quotients is a finite `R/Q`-module"; footnote 10, p. 243; `R/Q` is a complete local
domain). -/
theorem finite_integralClosure_quotient_of_isAdicComplete [Hironaka.Cited.CurveFiniteIntegralClosure.{u}] {A : Type u} [CommRing A] [IsLocalRing A]
    [IsNoetherianRing A] [IsAdicComplete (maximalIdeal A) A] (Q : Ideal A) [Q.IsPrime] :
    Module.Finite (A ⧸ Q) (integralClosure (A ⧸ Q) (FractionRing (A ⧸ Q))) := by
  have _ : IsLocalRing (A ⧸ Q) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk Q) Ideal.Quotient.mk_surjective
  have _ : IsAdicComplete (maximalIdeal (A ⧸ Q)) (A ⧸ Q) := by
    have : IsAdicComplete (maximalIdeal A) (A ⧸ Q) := curve_isAdicComplete_of_finite _ _
    have h := curve_isAdicComplete_map (B := A ⧸ Q) (maximalIdeal A)
    rwa [Ideal.Quotient.algebraMap_eq, IsLocalRing.map_maximalIdeal_of_surjective _
      Ideal.Quotient.mk_surjective] at h
  exact curve_finite_integralClosure (A ⧸ Q)

end CompleteCase


section CompleteInduction

/-- A prime `Q ≠ M` of a noetherian local ring has `dim(R/Q) ≥ 1`. -/
theorem one_le_ringKrullDim_quotient_of_ne_maximalIdeal {R : Type u} [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] (Q : Ideal R) [Q.IsPrime] (hQM : Q ≠ maximalIdeal R) :
    (1 : WithBot ℕ∞) ≤ ringKrullDim (R ⧸ Q) := by
  have hsurj : Function.Surjective (Ideal.Quotient.mk Q) := Ideal.Quotient.mk_surjective
  have _ : IsLocalRing (R ⧸ Q) := IsLocalRing.of_surjective' (Ideal.Quotient.mk Q) hsurj
  let a : PrimeSpectrum (R ⧸ Q) := ⟨⊥, inferInstance⟩
  have hab : a < ⊤ := by
    refine lt_of_le_of_ne le_top fun h => hQM ?_
    have h' : (⊥ : Ideal (R ⧸ Q)) = maximalIdeal (R ⧸ Q) := congrArg PrimeSpectrum.asIdeal h
    have hM : maximalIdeal (R ⧸ Q) = (maximalIdeal R).map (Ideal.Quotient.mk Q) :=
      (IsLocalRing.map_maximalIdeal_of_surjective _ hsurj).symm
    have h1 : (⊥ : Ideal (R ⧸ Q)).comap (Ideal.Quotient.mk Q) = Q := by
      rw [← RingHom.ker_eq_comap_bot, Ideal.mk_ker]
    rw [← h1, h', hM, Ideal.comap_map_of_surjective _ hsurj, ← RingHom.ker_eq_comap_bot,
      Ideal.mk_ker]
    exact sup_eq_left.mpr (le_maximalIdeal (Ideal.IsPrime.ne_top ‹_›))
  have h1 : Order.height a + 1 ≤ Order.height (⊤ : PrimeSpectrum (R ⧸ Q)) :=
    Order.height_add_one_le hab
  have h2 : ((maximalIdeal (R ⧸ Q)).height : WithBot ℕ∞) = ringKrullDim (R ⧸ Q) :=
    IsLocalRing.maximalIdeal_height_eq_ringKrullDim
  have h3 : Order.height (⊤ : PrimeSpectrum (R ⧸ Q)) = (maximalIdeal (R ⧸ Q)).height :=
    (PrimeSpectrum.height_eq_orderHeight (⊤ : PrimeSpectrum (R ⧸ Q))).symm
  have h4 : (1 : ℕ∞) ≤ (maximalIdeal (R ⧸ Q)).height := by
    rw [← h3]
    exact le_trans (by simp) h1
  rw [← h2]
  exact_mod_cast h4

/-- **The case of a complete `R`, by induction on `dim(R/Q)`** (p. 261: "Let us first consider the
case of `dim(R/Q) = 1`. By the above arguments, we may assume that `R` is complete. Therefore, the
integral closure of `R/Q` in its field of quotients is a finite `R/Q`-module. […] We know that the
assertion is verified if `R/Q` is regular […] Let us consider the case of `dim(R/Q) > 1`. We may
again assume that `R` is complete. By the dimension assumption, we can find a prime ideal `Q'` in
`R` such that `Q'` contains `Q` and `dim(R/Q') = 1`. By Corollary 3 (c) of Theorem 5, § 6, the
assumptions (i) and (ii) remain valid if we replace `R`, `Q`, `J`, and `M` by `R_{Q'}`, `QR_{Q'}`,
`JR_{Q'}`, and `Q'R_{Q'}`, respectively. Therefore, by the induction assumption, the flatness of
`gr_{PR_Q}(R_Q/JR_Q)` over `R_Q/PR_Q` implies the same of `gr_{PR_{Q'}}(R_{Q'}/JR_{Q'})` over
`R_{Q'}/PR_{Q'}`. By the above result for the 1-dimensional case, the flatness of `gr_P(R/J)` over
`R/P` follows."): Corollary 2 for the complete regular local rings with `dim(R/Q) = n`, from
Corollary 2 for all the regular local rings with `dim < n` (`IH`).

* `R/Q` regular (in particular `n = 0`):
`isNormallyFlatAlongIdeal_of_isRegularLocalRing_quotient_of_localization`
  (Theorem 3 of Ch. II and Corollary 3 (a)).
* `n = 1`: the dimension-one case `isNormallyFlatAlongIdeal_of_dimensionLEOne` (with `Q' = Q`).
* `n > 1`: a prime `Q' ⊇ Q` with `dim(R/Q') = 1` and `dim(R_{Q'}/QR_{Q'}) < n`
  (`exists_prime_adjacent_maximalIdeal_of_ringKrullDim_quotient_eq`), (i) and (ii) for `R_{Q'}` by
  Corollary 3 (c) (`grIdeal_localization_eq_span_initialForm_of_finite`; here the finiteness
  condition of footnote 10 holds since `R` is complete), the induction assumption for `R_{Q'}`
  (`isNormallyFlatAlongIdeal_localization_of_le`), and then the case `dim(R/Q') = 1`.

The dimension-one case follows the printed text (any residually algebraic monoidal transform with
centre `M`; see `isNormallyFlatAlongIdeal_of_dimensionLEOne`). -/
@[blueprint "lem:III.8-cor2-finite"
  (statement := /-- Assume Proposition~2 (\cref{prop:III.8-2}) and Corollary~2
    (\cref{cor:III.prop2-2}) for all regular local rings $R'$ (with residue field of characteristic
    zero) and primes $Q'$ with $\dim(R'/Q')<n$. Then Corollary~2 holds for the complete regular
    local rings $R$ and primes $Q$ with $\dim(R/Q)=n$. -/)
  (proof := /-- If $R/Q$ is regular use \cref{lem:III.8-cor2-regular-case}. Otherwise $n\ge1$. If
    $n=1$ apply the dimension-one case (\cref{lem:III.8-cor2-dimension-one}); if $n>1$ choose a
    prime $Q'\supseteq Q$ with $\dim(R/Q')=1$ and $\dim(R_{Q'}/QR_{Q'})<n$,
    \cref{lem:III.8-cor2-adjacent} (the induction assumption for $R_{Q'}$, with (i), (ii) for
    $R_{Q'}$ by \cref{cor:III.thm5-3c}) gives flatness at $Q'$, and the dimension-one case for $Q'$
    gives the claim. -/)
  (latexEnv := "lemma")]
theorem corollary2DimComplete_of_forall_lt [Hironaka.Cited.CurveFiniteIntegralClosure.{u}] [Hironaka.Cited.ExistsSurjectiveOfIsRegularLocalRingOfIsAdicComplete.{u}] [Hironaka.Cited.IsRegularLocalRingLocalizationOfIsRegularLocalRing.{u}] [Hironaka.Cited.IsSeparableFieldExtensionIff.{u}] (hprop2 : Proposition2Statement.{u}) (n : ℕ)
    (IH : ∀ n' < n, Corollary2Dim.{u} n') : Corollary2DimComplete.{u} n := by
  intro R _ _ _ _ Q J _ m g hg P _ hJP hPQ hPreg hdim hflat
  classical
  have _ : IsDomain R := Transforms.isDomain_of_isRegularLocalRing R
  have hJQ : J ≤ Q := hJP.trans hPQ
  have hsurj : Function.Surjective (Ideal.Quotient.mk Q) := Ideal.Quotient.mk_surjective
  have _ : IsLocalRing (R ⧸ Q) := IsLocalRing.of_surjective' (Ideal.Quotient.mk Q) hsurj
  -- `R/Q` regular: Theorem 3 of Ch. II
  by_cases hreg : IsRegularLocalRing (R ⧸ Q)
  · exact isNormallyFlatAlongIdeal_of_isRegularLocalRing_quotient_of_localization Q J P hJP hPQ g
      hg hflat
  have hQM : Q ≠ maximalIdeal R := by
    intro h
    apply hreg
    rw [h]
    let _ : Field (R ⧸ maximalIdeal R) := Ideal.Quotient.field _
    infer_instance
  have hn1 : 1 ≤ n := by
    have := one_le_ringKrullDim_quotient_of_ne_maximalIdeal Q hQM
    rw [hdim] at this
    exact_mod_cast this
  -- the finiteness condition of footnote 10 for the complete ring `R`
  have hfin : ∀ (Q' Q'' : Ideal R) [Q'.IsPrime] [Q''.IsPrime], Q'' ≤ Q' →
      Module.Finite (Localization.AtPrime Q' ⧸ Q''.map (algebraMap R (Localization.AtPrime Q')))
        (integralClosure (Localization.AtPrime Q' ⧸
          Q''.map (algebraMap R (Localization.AtPrime Q')))
          (FractionRing (Localization.AtPrime Q' ⧸
            Q''.map (algebraMap R (Localization.AtPrime Q'))))) :=
    fun Q' Q'' _ _ h => finite_integralClosure_localization_quotient_of_isAdicComplete Q' Q'' h
  -- remove the zero elements of the system (their initial forms are `0`)
  have hg' : IsLocallyAdaptedSystem R Q J
      (fun i => g ((Fintype.equivFin {j // g j ≠ 0}).symm i).1) := by
    refine ⟨fun i => hg.1 _, ?_, fun i => hg.2.2 _⟩
    rw [hg.2.1]
    exact Ideal.span_range_eq_span_range_filter_of_forall_eq_zero (fun j => g j ≠ 0)
      (fun j => initialForm _ (g j)) fun j hj => by rw [not_not.mp hj, initialForm_zero]
  set g' : Fin (Fintype.card {j // g j ≠ 0}) → R :=
    fun i => g ((Fintype.equivFin {j // g j ≠ 0}).symm i).1 with hg'def
  have hg0 : ∀ i, g' i ≠ 0 := fun i => ((Fintype.equivFin {j // g j ≠ 0}).symm i).2
  -- a prime `Q' ⊇ Q` with `dim(R/Q') ≤ 1` at which the flatness holds
  obtain ⟨Q', hQ'p, hQQ', hmin, hgQ', hflat'⟩ : ∃ (Q' : Ideal R) (_ : Q'.IsPrime), Q ≤ Q' ∧
      (∀ p : Ideal R, p.IsPrime → Q' ≤ p → p = Q' ∨ p = maximalIdeal R) ∧
      IsLocallyAdaptedSystem R Q' J g' ∧
      IsNormallyFlatAlongIdeal ((P.map (algebraMap R (Localization.AtPrime Q'))).map
        (Ideal.Quotient.mk (J.map (algebraMap R (Localization.AtPrime Q'))))) := by
    by_cases hn : n = 1
    · subst hn
      exact ⟨Q, inferInstance, le_rfl,
        forall_prime_eq_or_eq_of_ringKrullDim_quotient_eq_one Q hdim, hg', hflat⟩
    · obtain ⟨Q', hQ'p, hQQ', hQ'M, hmin, n', hn'n, hdimQ'⟩ :=
        exists_prime_adjacent_maximalIdeal_of_ringKrullDim_quotient_eq Q hn1 hdim
      -- (ii) for `Q'`: `ν_M(g_j) ≥ ν_{Q'R_{Q'}}(g_j) ≥ ν_{QR_Q}(g_j) = ν_M(g_j)` (Theorem 1, §3)
      have hB : ∀ j, Ideal.ordElem (Q'.map (algebraMap R (Localization.AtPrime Q')))
          (algebraMap R (Localization.AtPrime Q') (g' j)) =
          Ideal.ordElem (Q.map (algebraMap R (Localization.AtPrime Q)))
            (algebraMap R (Localization.AtPrime Q) (g' j)) := fun j =>
        le_antisymm ((Ideal.ordElem_localization_le_ordElem_maximalIdeal Q' (g' j)).trans
          (hg'.2.2 j).le) (Ideal.ordElem_localization_mono Q Q' hQQ' (g' j))
      have hgQ' : IsLocallyAdaptedSystem R Q' J g' :=
        ⟨hg'.1, hg'.2.1, fun j => (hg'.2.2 j).trans (hB j).symm⟩
      -- (i) for `R_{Q'}` (Corollary 3 (c))
      have hA := grIdeal_localization_eq_span_initialForm_of_finite hfin Q' J (hJQ.trans hQQ') g'
        hgQ'
      exact ⟨Q', hQ'p, hQQ', hmin, hgQ', isNormallyFlatAlongIdeal_localization_of_le (IH n' hn'n)
        Q Q' J hQQ' g' hg' hA hB hdimQ' P hJP hPQ hPreg hflat⟩
  -- the case `dim(R/Q') = 1`: the integral closure of `R/Q'` is finite since `R` is complete
  have _ := hQ'p
  exact isNormallyFlatAlongIdeal_of_dimensionLEOne hprop2 Q' J (hJQ.trans hQQ') g' hg0 hgQ'
    (dimensionLEOne_quotient_of_forall_prime_eq_or_eq Q' hmin)
    (finite_integralClosure_quotient_of_isAdicComplete Q') P hJP (hPQ.trans hQQ') hPreg hflat'

end CompleteInduction

section Completion

/-- **Every minimal prime of `QR̂` lies over `Q`** (p. 260: "Let `Q̂` be a minimal prime ideal
associated with `QR̂`, i.e., `Q̂ ∩ R = Q` and `QR̂_Q̂` is primary to the maximal ideal"): for a
prime
`Q` of a noetherian local ring `R`, a minimal prime `Q̂` of `QR̂`, `R̂` the completion, satisfies
`Q̂ ∩ R = Q`, by going down for the flat map `R → R̂`. -/
theorem comap_eq_of_mem_minimalPrimes_adicCompletion {R : Type u} [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] (Q : Ideal R) [Q.IsPrime]
    {Qh : Ideal (AdicCompletion (maximalIdeal R) R)}
    (hQhmin : Qh ∈ (Q.map (algebraMap R (AdicCompletion (maximalIdeal R) R))).minimalPrimes) :
    Qh.comap (algebraMap R (AdicCompletion (maximalIdeal R) R)) = Q := by
  classical
  have hQhp : Qh.IsPrime := Ideal.IsMinimalPrime.isPrime hQhmin
  have hQQh : Q ≤ Qh.comap (algebraMap R (AdicCompletion (maximalIdeal R) R)) := by
    rw [← Ideal.map_le_iff_le_comap]
    exact hQhmin.1.2
  -- going down for the flat map `R → R̂`
  obtain ⟨p', hp'le, hp'p, hp'lies⟩ := Ideal.exists_ideal_le_liesOver_of_le (p := Q)
    (q := Qh.under R) Qh hQQh
  have hp'c : p'.comap (algebraMap R (AdicCompletion (maximalIdeal R) R)) = Q :=
    hp'lies.over.symm
  have hp'ge : Q.map (algebraMap R (AdicCompletion (maximalIdeal R) R)) ≤ p' := by
    rw [Ideal.map_le_iff_le_comap, hp'c]
  have hpQh : Qh ≤ p' := hQhmin.2 ⟨hp'p, hp'ge⟩ hp'le
  have : p' = Qh := le_antisymm hp'le hpQh
  exact this ▸ hp'c

/-- **The reduction of Corollary 2 to the completion** (p. 260: "Let `R̂` be the completion of `R`,
and `P̂ = PR̂`. We see that `P̂` is a prime ideal in `R̂` such that `R̂/P̂` is regular. Let `Q̂`
be a minimal prime ideal associated with `QR̂`, i.e., `Q̂ ∩ R = Q` and `QR̂_Q̂` is primary to the
maximal ideal. We have `ν_{Q̂R̂_Q̂}(g_j) ≥ ν_{QR_Q}(g_j)`, and `ν_{M̂}(g_j) = ν_M(g_j)` where
`M̂ = MR̂` … Therefore, by Theorem 1, §3, (ii) implies that `ν_{M̂}(g_j) = ν_{Q̂R̂_Q̂}(g_j)` for all
`j`. Moreover, it is clear that (i) implies that the initial forms of `g_j` in `gr_{M̂}(R̂)`
generate the ideal `gr_{M̂}(Ĵ, R̂)` … We know that `R̂_Q̂` is faithfully flat over `R_Q`. Hence, by
Lemma 9, § 3, Ch. II, `gr_{PR_Q}(R_Q/JR_Q)` is flat over `R_Q/PR_Q` if and only if
`gr_{PR̂_Q̂}(R̂_Q̂/JR̂_Q̂)` is flat over `R̂_Q̂/PR̂_Q̂` … For the same reason, `gr_P(R/J)` is flat
over `R/P` if and only if `gr_{P̂}(R̂/Ĵ)` is flat over `R̂/P̂`. We can assume that
`dim(R̂/Q̂) = dim(R/Q)`."): Corollary 2 for the regular local rings of dimension `dim(R/Q) = n`
follows from Corollary 2 for the complete regular local rings of that dimension.

`Q̂` is a minimal prime of `QR̂` with `dim(R̂/Q̂) = dim(R/Q)`
(`exists_mem_minimalPrimes_ringKrullDim_quotient_eq_of_ideal`, with the cited leaf
`ringKrullDim_adicCompletion_quotient_eq`; `Q̂ ∩ R = Q` is
`comap_eq_of_mem_minimalPrimes_adicCompletion`), and the passage back from `R̂` to `R` is Lemma 9,
§3, Ch. II for the faithfully flat map `R/J → R̂/JR̂` (`isNormallyFlatAlongIdeal_map_iff`). -/
@[blueprint "lem:III.8-cor2-completion"
  (statement := /-- Let $n\ge0$. If Corollary~2 (\cref{cor:III.prop2-2}) holds for the complete
    regular local rings $R$ whose residue field has characteristic zero and the primes $Q$ with
    $\dim(R/Q)=n$, then it holds for all regular local rings whose residue field has
    characteristic zero and all primes $Q$ with $\dim(R/Q)=n$. -/)
  (proof := /-- Pass to the completion $\hat R$, $\hat P=P\hat R$, and a minimal prime $\hat Q$ of
    $Q\hat R$ with $\dim(\hat R/\hat Q)=\dim(R/Q)$ (\cref{lem:III.8-cor2-completion-dimension}):
    $\hat Q\cap R=Q$; (i), (ii) hold for $\hat R,\hat Q,\hat J$ by faithful flatness and
    Theorem~1 (\cref{thm:III.1}); flatness at $\hat Q$ follows by base change from flatness at $Q$
    (Lemma~9, \S3, Ch.~II, \cref{cor:II.3-lem9}); the complete case is the hypothesis;
    flatness of $\operatorname{gr}_{\hat P}(\hat R/\hat J)$ descends to $R$ (Lemma~9, \S3, Ch.~II,
    for
    the faithfully flat map $R/J\to\hat R/J\hat R$). -/)
  (latexEnv := "lemma")]
theorem corollary2Dim_of_complete [Hironaka.Cited.CurveFiniteIntegralClosure.{u}] [Hironaka.Cited.IsRegularLocalRingLocalizationOfIsRegularLocalRing.{u}] [Hironaka.Cited.RingKrullDimAdicCompletionQuotientEq.{u}] {n : ℕ} (hcomplete : Corollary2DimComplete.{u} n) :
    Corollary2Dim.{u} n := by
  intro R _ _ _ Q J _ m g hg P _ hJP hPQ hPreg hdim hflat
  classical
  have _ : IsDomain R := Transforms.isDomain_of_isRegularLocalRing R
  set R' := AdicCompletion (maximalIdeal R) R with hR'
  have hFF : Module.FaithfullyFlat R R' := faithfullyFlat_adicCompletion_maximalIdeal R
  have hα : RingHom.MapsRSOP (algebraMap R R') := mapsRSOP_algebraMap_adicCompletion
  have hJQ : J ≤ Q := hJP.trans hPQ
  -- a minimal prime `Q̂` of `QR̂` with `dim(R̂/Q̂) = dim(R/Q)`; `Q̂ ∩ R = Q`
  have hQtop : Q.map (algebraMap R R') ≠ ⊤ := fun h => Ideal.IsPrime.ne_top ‹Q.IsPrime›
    (by rw [← Ideal.comap_map_eq_self_of_faithfullyFlat (B := R') Q, h, Ideal.comap_top])
  obtain ⟨Qh, hQhmin, hQhdim⟩ :=
    exists_mem_minimalPrimes_ringKrullDim_quotient_eq_of_ideal (Q.map (algebraMap R R')) hQtop
  have hQhc : Qh.comap (algebraMap R R') = Q :=
    comap_eq_of_mem_minimalPrimes_adicCompletion Q hQhmin
  have hQh : Qh.IsPrime := Ideal.IsMinimalPrime.isPrime hQhmin
  have hQ' : Q = Qh.comap (algebraMap R R') := hQhc.symm
  have hQhdim' : ringKrullDim (R' ⧸ Qh) = n := by
    rw [hQhdim, ringKrullDim_adicCompletion_quotient_eq, hdim]
  -- `P̂ = PR̂` is prime with regular quotient
  obtain ⟨⟨hPh, hPhreg⟩, -⟩ := RingHom.MapsRSOP.canonicalLift_properties (algebraMap R R') hα
    (P := P) inferInstance hPreg
  -- the local homomorphism `β : R_Q → R̂_Q̂` is faithfully flat
  set β := Localization.localRingHom Q Qh (algebraMap R R') hQ' with hβ
  have hβmap : ∀ r : R, β (algebraMap R (Localization.AtPrime Q) r) =
      algebraMap R' (Localization.AtPrime Qh) (algebraMap R R' r) :=
    Localization.localRingHom_to_map Q Qh (algebraMap R R') hQ'
  let _ : Algebra (Localization.AtPrime Q) (Localization.AtPrime Qh) := β.toAlgebra
  have hβflat : Module.Flat (Localization.AtPrime Q) (Localization.AtPrime Qh) :=
    RingHom.Flat.localRingHom (RingHom.flat_algebraMap_iff.mpr inferInstance) _ _ hQ'
  have : IsLocalHom (algebraMap (Localization.AtPrime Q) (Localization.AtPrime Qh)) :=
    Localization.isLocalHom_localRingHom _ _ _ hQ'
  have hβFF : Module.FaithfullyFlat (Localization.AtPrime Q) (Localization.AtPrime Qh) :=
    Module.FaithfullyFlat.of_flat_of_isLocalHom
  -- (ii) for `R̂`
  have hmaxR' : (maximalIdeal R).map (algebraMap R R') = maximalIdeal R' :=
    AdicCompletion.maximalIdeal_eq_map.symm
  have hmax_loc : (Q.map (algebraMap R (Localization.AtPrime Q))).map β ≤
      Qh.map (algebraMap R' (Localization.AtPrime Qh)) := by
    rw [Ideal.map_map, Ideal.map_le_iff_le_comap]
    intro q hq
    have : (β.comp (algebraMap R (Localization.AtPrime Q))) q =
        algebraMap R' (Localization.AtPrime Qh) (algebraMap R R' q) :=
      hβmap q
    rw [Ideal.mem_comap, this]
    exact Ideal.mem_map_of_mem _ (hQ' ▸ hq : q ∈ Qh.comap (algebraMap R R'))
  have hord : ∀ j, Ideal.ordElem (maximalIdeal R') (algebraMap R R' (g j)) =
      Ideal.ordElem (Qh.map (algebraMap R' (Localization.AtPrime Qh)))
        (algebraMap R' (Localization.AtPrime Qh) (algebraMap R R' (g j))) := by
    intro j
    refine le_antisymm ?_ (Ideal.ordElem_localization_le_ordElem_maximalIdeal Qh _)
    rw [← hmaxR', Ideal.ordElem_map_of_faithfullyFlat (maximalIdeal R) (g j), hg.2.2 j,
      ← Ideal.ordElem_map_of_faithfullyFlat (A := Localization.AtPrime Q)
        (B := Localization.AtPrime Qh) (Q.map (algebraMap R (Localization.AtPrime Q))),
      ← hβmap]
    exact Ideal.ordElem_mono hmax_loc _
  -- (i) for `R̂`
  have hjac : (maximalIdeal R).map (algebraMap R R') ≤ Ring.jacobson R' := by
    rw [hmaxR', ← Ideal.jacobson_bot]
    exact maximalIdeal_le_jacobson _
  have hgr := grIdeal_map_eq_span_initialForm_of_faithfullyFlat (A := R) (B := R')
    (maximalIdeal R) J hjac g hg.2.1
  rw [hmaxR'] at hgr
  have hg' : IsLocallyAdaptedSystem R' Qh (J.map (algebraMap R R'))
      (fun j => algebraMap R R' (g j)) :=
    ⟨fun j => Ideal.mem_map_of_mem _ (hg.1 j), hgr, hord⟩
  -- the hypothesis of Corollary 2 for `R̂` (flat base change along `β`)
  have hflat' : IsNormallyFlatAlongIdeal
      (((P.map (algebraMap R R')).map (algebraMap R' (Localization.AtPrime Qh))).map
        (Ideal.Quotient.mk ((J.map (algebraMap R R')).map
          (algebraMap R' (Localization.AtPrime Qh))))) := by
    have h := isNormallyFlatAlongIdeal_mod_map_of_flat (S := Localization.AtPrime Q)
      (S' := Localization.AtPrime Qh) (P.map (algebraMap R (Localization.AtPrime Q)))
      (J.map (algebraMap R (Localization.AtPrime Q))) hflat
    have e1 : (P.map (algebraMap R (Localization.AtPrime Q))).map
        (algebraMap (Localization.AtPrime Q) (Localization.AtPrime Qh)) =
        (P.map (algebraMap R R')).map (algebraMap R' (Localization.AtPrime Qh)) := by
      rw [Ideal.map_map, Ideal.map_map]
      congr 1
      exact RingHom.ext hβmap
    have e2 : (J.map (algebraMap R (Localization.AtPrime Q))).map
        (algebraMap (Localization.AtPrime Q) (Localization.AtPrime Qh)) =
        (J.map (algebraMap R R')).map (algebraMap R' (Localization.AtPrime Qh)) := by
      rw [Ideal.map_map, Ideal.map_map]
      congr 1
      exact RingHom.ext hβmap
    rw [e1, e2] at h
    exact h
  have _ : CharZero (ResidueField R') :=
    (RingHom.charZero_iff (ResidueField.map (algebraMap R R')).injective).mp inferInstance
  have hPhQ : P.map (algebraMap R R') ≤ Qh := by
    rw [Ideal.map_le_iff_le_comap, ← hQ']
    exact hPQ
  have hnf := hcomplete R' Qh (J.map (algebraMap R R')) (fun j => algebraMap R R' (g j)) hg'
    (P.map (algebraMap R R')) (Ideal.map_mono hJP) hPhQ hPhreg hQhdim' hflat'
  -- descend from `R̂` to `R` by Lemma 9, §3, Ch. II (`R/J → R̂/JR̂` is faithfully flat)
  exact (isNormallyFlatAlongIdeal_map_iff J P hJP (Ideal.IsPrime.ne_top inferInstance)).mpr hnf

end Completion


section Final

/-- **Corollary 2 for the regular local rings of every dimension `dim(R/Q) = n`**, by induction on
`n` (p. 261: "Now, the proof of Corollary 2 is done by induction on `dim(R/Q)`"), assuming
Proposition 2. -/
theorem corollary2Dim [Hironaka.Cited.CurveFiniteIntegralClosure.{u}] [Hironaka.Cited.ExistsSurjectiveOfIsRegularLocalRingOfIsAdicComplete.{u}] [Hironaka.Cited.IsRegularLocalRingLocalizationOfIsRegularLocalRing.{u}] [Hironaka.Cited.IsSeparableFieldExtensionIff.{u}] [Hironaka.Cited.RingKrullDimAdicCompletionQuotientEq.{u}] (hprop2 : Proposition2Statement.{u}) (n : ℕ) : Corollary2Dim.{u} n := by
  induction n using Nat.strong_induction_on with
  | _ n ih => exact corollary2Dim_of_complete (corollary2DimComplete_of_forall_lt hprop2 n ih)

/-- **Corollary 2, assuming Proposition 2**: the induction on `dim(R/Q)` of `corollary2Dim`
(`dim(R/Q)` is finite as `R/Q` is a noetherian local ring). -/
theorem isNormallyFlatAlongIdeal_of_proposition2 [Hironaka.Cited.CurveFiniteIntegralClosure.{u}] [Hironaka.Cited.ExistsSurjectiveOfIsRegularLocalRingOfIsAdicComplete.{u}] [Hironaka.Cited.IsRegularLocalRingLocalizationOfIsRegularLocalRing.{u}] [Hironaka.Cited.IsSeparableFieldExtensionIff.{u}] [Hironaka.Cited.RingKrullDimAdicCompletionQuotientEq.{u}] (hprop2 : Proposition2Statement.{u})
    {R : Type u} [CommRing R] [IsRegularLocalRing R] [CharZero (ResidueField R)]
    (Q J : Ideal R) [Q.IsPrime] {m : ℕ} (g : Fin m → R) (hg : IsLocallyAdaptedSystem R Q J g)
    (P : Ideal R) [P.IsPrime] (hJP : J ≤ P) (hPQ : P ≤ Q) (hPreg : IsRegularLocalRing (R ⧸ P))
    (hflat : IsNormallyFlatAlongIdeal ((P.map (algebraMap R (Localization.AtPrime Q))).map
        (Ideal.Quotient.mk (J.map (algebraMap R (Localization.AtPrime Q)))))) :
    IsNormallyFlatAlongIdeal (P.map (Ideal.Quotient.mk J)) := by
  have _ : IsLocalRing (R ⧸ Q) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk Q) Ideal.Quotient.mk_surjective
  obtain ⟨n, hn⟩ := exists_natCast_eq_ringKrullDim (R ⧸ Q)
  exact corollary2Dim hprop2 n R Q J g hg P hJP hPQ hPreg hn hflat

end Final

end Hironaka
