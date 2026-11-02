/-
Copyright (c) 2026 Daattavya Aggarwal, Minhyong Kim, Oisin Kim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daattavya Aggarwal, Minhyong Kim, Oisin Kim
-/
module

public import Mathlib.FieldTheory.SeparableClosure
public import Mathlib.RingTheory.AdicCompletion.LocalRing
public import Mathlib.RingTheory.AdicCompletion.Noetherian
public import Mathlib.RingTheory.Coalgebra.IsFrobenius
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.HopfAlgebra.Basic
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology
public import Architect
public import Hironaka.Ch3.Transforms
public import Hironaka.Ch3.PermissibleEffects
public import Hironaka.Compat.AdicCompletionRegular

/-!
# Ch. III §2 (pp. 212–213): Corollaries 1 and 2 of Lemma 4 — the completion

> COROLLARY 1. Let `R` and `P` be as in Lemma 4. Let `R̂` be the completion of `R` and
> `P̂ = PR̂`. Then `P̂` is a prime ideal of `R̂` such that `R̂/P̂` is regular. For a given
> monoidal transform `R'` of `R` with center `P`, there exists a unique monoidal transform `R̂'`
> of `R̂` with center `P̂` which admits the following commutative diagram of canonical local
> homomorphisms … Moreover, the local homomorphism `R' → R̂'` induces an isomorphism of the
> residue fields of `R'` and `R̂'`, and it transforms a regular system of parameters of `R'`
> into such a system of parameters of `R̂'`.
>
> COROLLARY 2. The notation and assumptions being the same as in Corollary 1, the completions
> of `R'` and `R̂'` are canonically isomorphic to each other, and `R'` is a topological subspace
> of `R̂'`.

Lemma 4 itself and the canonical local homomorphisms `R' → R̄'` are in
`Hironaka/Ch3/Transforms.lean`; the two corollaries are kept in this separate file, which also
imports the existence of canonical lifts (`exists_isCanonicalLift`,
`Hironaka/Ch3/PermissibleEffects.lean`) and the facts on completions of
`Hironaka/Compat/AdicCompletionRegular.lean`.  Nothing else in the project uses them.

Lean identifiers cannot contain combining diacritics: a monoidal transform `R̂'` of the
completion `R̂` is the datum `th` in the code.
-/

@[expose] public section

open IsLocalRing

namespace Hironaka

universe u

/-! ### Corollaries 1 and 2 of Lemma 4 (pp. 212–213): the completion -/

section Completion

variable {R : Type u} [CommRing R] [IsRegularLocalRing R] [IsDomain R] {P : Ideal R}

/-- The completion of a regular local ring is a regular local ring
(`isRegularLocalRing_adicCompletion_of_isRegularLocalRing`); declared as an instance so that
monoidal transforms of `R̂` can be spoken of. -/
instance instIsRegularLocalRingAdicCompletion :
    IsRegularLocalRing (AdicCompletion (maximalIdeal R) R) :=
  isRegularLocalRing_adicCompletion_of_isRegularLocalRing R

/-- The completion of a regular local ring is a domain (`isDomain_of_isRegularLocalRing`). -/
instance instIsDomainAdicCompletion : IsDomain (AdicCompletion (maximalIdeal R) R) :=
  isDomain_of_isRegularLocalRing _

omit [IsDomain R] in
/-- The canonical map `R → R̂` transforms a regular system of parameters of `R` into one of `R̂`
(Corollary 1, first half of the tacit assertion). -/
theorem mapsRSOP_algebraMap_adicCompletion : RingHom.MapsRSOP (algebraMap R (AdicCompletion (maximalIdeal R) R)) := by
  classical
  obtain ⟨s, hs, hcard⟩ := ((isRegularLocalRing_iff_exists_rsop (R := R)).mp inferInstance).2
  have := faithfullyFlat_adicCompletion_maximalIdeal R
  have hinj : Function.Injective (algebraMap R (AdicCompletion (maximalIdeal R) R)) :=
    FaithfulSMul.algebraMap_injective _ _
  refine ⟨s, ⟨hs, hcard⟩, ⟨?_, ?_⟩, hinj.injOn⟩
  · rw [Finset.coe_image, ← Ideal.map_span, hs, AdicCompletion.maximalIdeal_eq_map]
  · have h1 := IsRegularLocalRing.spanFinrank_maximalIdeal (R := R)
    have h2 := IsRegularLocalRing.spanFinrank_maximalIdeal
      (R := AdicCompletion (maximalIdeal R) R)
    rw [AdicCompletion.spanFinrank_maximalIdeal_eq] at h2
    rw [Finset.card_image_of_injective _ hinj, hcard, ← h1, h2]

/-- Corollary 1 (pp. 212–213): "Let `R` and `P` be as in Lemma 4. Let `R̂` be the completion of
`R` and `P̂ = PR̂`. Then `P̂` is a prime ideal of `R̂` such that `R̂/P̂` is regular. For a given
monoidal transform `R'` of `R` with center `P`, there exists a unique monoidal transform `R̂'` of
`R̂` with center `P̂` which admits the commutative diagram of canonical local homomorphisms
(`IsCanonicalLift`). Moreover, the local homomorphism `R' → R̂'` induces an isomorphism of the
residue fields of `R'` and `R̂'`, and it transforms a regular system of parameters of `R'` into
such a system of parameters of `R̂'`."

Formalization notes (encoding): `R̂ = AdicCompletion (maximalIdeal R) R`; that `R̂` is a
regular local domain is proved (`isRegularLocalRing_adicCompletion_of_isRegularLocalRing`,
`isDomain_of_isRegularLocalRing`) and recorded as instances, so no hypotheses on `R̂` are
needed to speak of its monoidal transforms.  "Unique `R̂'`" is uniqueness of the subring of
`Frac(R̂)` (see `MonoidalTransform.subring`).

Deviation from the paper (statement modified): the tacit fact that `R → R̂` transforms a regular
system of parameters into one (so that Lemma 4 applies) is included as an additional conclusion.

Gap in the paper filled: the paper gives no proof.  Existence and uniqueness of `R̂'` follow, as
the printed text of Lemma 4 suggests, from the correspondence of p. 211: since `R → R̂` is
residually rational (`k̂ = k`), `k̂[X₂,…,X_r] = k[X₂,…,X_r]` and `m̄'k̂[X] = m̄'` is a prime ideal, which has
exactly one associated prime, so that the number of the `R̂'` which admit a canonical local homomorphism
`R' → R̂'` is `1` (`MonoidalTransform.mk_canonicalTransforms_eq_mk_associatedPrimes`).  The residue field and the regular system of parameters are Lemma 4 (2),
(3). -/
@[blueprint "cor:III.lem4-1"
  (statement := /-- Let $R$ and $P$ be as in \cref{lem:III.4}. Let $\hat R$ be the completion
    of $R$ and $\hat P=P\hat R$. Then $\hat P$ is a prime ideal of $\hat R$ such that
    $\hat R/\hat P$ is regular. For a given monoidal transform $R'$ of $R$ with center $P$,
    there exists a unique monoidal transform $\hat R'$ of $\hat R$ with center $\hat P$ which
    admits the commutative diagram of canonical local homomorphisms
    (\cref{def:III.2-canonical}). Moreover, the local homomorphism $R'\to\hat R'$ induces an
    isomorphism of the residue fields of $R'$ and $\hat R'$, and it transforms a regular
    system of parameters of $R'$ into such a system of parameters of $\hat R'$.
    (Corollary 1, pp.~212--213.) (Formalization note (encoding): that $\hat R$ is a regular
    local domain is proved separately and used implicitly; uniqueness is uniqueness of
    $\hat R'$ as a subring of the field of quotients of $\hat R$.)

    \textbf{Deviation from the paper (statement modified).} The Lean statement has the
    additional conclusion that $R\to\hat R$ transforms a regular system of parameters of $R$
    into one of $\hat R$, a fact used tacitly by the paper to apply \cref{lem:III.4}. -/)
  (proof := /-- The paper gives no proof. $R\to\hat R$ is a local homomorphism of regular
    local rings transforming a regular system of parameters of $R$ into one of $\hat R$, and
    $\hat R$ is residually rational over $R$ (so $\hat k=k$). The correspondence of p.~211
    (\cref{lem:III.4-count}) gives that the number of the monoidal transforms $\hat R'$ of $\hat R$
    with center $\hat P$ which admit a canonical local homomorphism $R'\to\hat R'$ is the number of
    associated primes of $\bar m'\hat k[X_2,\dots,X_r]$; now $\hat k=k$, so
    $\bar m'\hat k[X]=\bar m'$ is a prime ideal (the prime $(0)$ of $\hat k\otimes_kk[\bar X]=k[\bar X]$)
    and has exactly one associated prime: there is exactly one $\hat R'$, which gives the existence
    and the uniqueness. By \cref{lem:III.4} (2), the residue field of $\hat R'$ is generated by that of
    $R'$, i.e.\ $R'\to\hat R'$ is residually an isomorphism; and (3) (with $\hat k=k$ separable
    algebraic) gives that a regular system of parameters of $R'$ maps to one of $\hat R'$.

    \textbf{Gap in the paper filled.} The paper states Corollary~1 without proof; existence and
    uniqueness are read off from the count of \cref{lem:III.4-count}. -/)
  (latexEnv := "corollary")]
theorem adicCompletion_mapsRSOP_and_existsUnique_transform
    (hP : P.IsPrime) (hS : IsRegularLocalRing (R ⧸ P)) (t : MonoidalTransform R P) :
    RingHom.MapsRSOP (algebraMap R (AdicCompletion (maximalIdeal R) R)) ∧
    ((P.map (algebraMap R (AdicCompletion (maximalIdeal R) R))).IsPrime ∧
      IsRegularLocalRing (AdicCompletion (maximalIdeal R) R ⧸
        P.map (algebraMap R (AdicCompletion (maximalIdeal R) R)))) ∧
    (∃! S : Subring (FractionRing (AdicCompletion (maximalIdeal R) R)),
      ∃ th : MonoidalTransform (AdicCompletion (maximalIdeal R) R)
          (P.map (algebraMap R (AdicCompletion (maximalIdeal R) R))),
        th.subring = S ∧ ∃ β : t.ring →+* th.ring,
          IsCanonicalLift (algebraMap R (AdicCompletion (maximalIdeal R) R)) t th β) ∧
    (∀ (th : MonoidalTransform (AdicCompletion (maximalIdeal R) R)
        (P.map (algebraMap R (AdicCompletion (maximalIdeal R) R))))
      (β : t.ring →+* th.ring)
      (hβ : IsCanonicalLift (algebraMap R (AdicCompletion (maximalIdeal R) R)) t th β),
        haveI := hβ.isLocalHom
        Function.Bijective (ResidueField.map (R := t.ring) (S := th.ring) β) ∧
          RingHom.MapsRSOP (R := t.ring) (R' := th.ring) β) := by
  have hα := mapsRSOP_algebraMap_adicCompletion (R := R)
  have hL := RingHom.MapsRSOP.canonicalLift_properties (algebraMap R (AdicCompletion (maximalIdeal R) R)) hα hP hS
  refine ⟨hα, hL.1, ?_, ?_⟩
  · -- p. 211: the number of the `R̂'` is the number of the associated primes of `m̄'k̂[X]`; `k̂ = k`,
    -- so `m̄'k̂[X]` is a prime ideal and has exactly one associated prime
    have hbij := AdicCompletion.residueField_map_bijective R
    have halg : RingHom.IsResiduallyAlgebraic (algebraMap R (AdicCompletion (maximalIdeal R) R)) := by
      let := (ResidueField.map (algebraMap R (AdicCompletion (maximalIdeal R) R))).toAlgebra
      refine ⟨fun x => ?_⟩
      obtain ⟨w, hw⟩ := hbij.2 x
      have : x = algebraMap (ResidueField R) (ResidueField (AdicCompletion (maximalIdeal R) R)) w :=
        hw.symm
      rw [this]
      exact isAlgebraic_algebraMap w
    obtain ⟨r, π, π', hπ, hkπ, hπ', hkπ', hcomm, hπC, hπ'C⟩ :=
      t.exists_residue_charts (algebraMap R (AdicCompletion (maximalIdeal R) R)) hα hP hS
    have hcount := (t.mk_canonicalTransforms_eq_mk_associatedPrimes
      (algebraMap R (AdicCompletion (maximalIdeal R) R)) hα hP hS (Or.inl halg) π π' hkπ' hπ'
      hcomm).2
    have hm : (t.M'.map π).IsPrime := Ideal.map_isPrime_of_surjective hπ (hkπ.trans t.le)
    -- `ResidueField R → ResidueField R̂` is bijective, hence so is `k[X] → k̂[X]`
    let e : MvPolynomial (Fin r) (ResidueField R) ≃+*
        MvPolynomial (Fin r) (ResidueField (AdicCompletion (maximalIdeal R) R)) :=
      MvPolynomial.mapEquiv (Fin r) (RingEquiv.ofBijective _ hbij)
    have hmp : ((t.M'.map π).map (MvPolynomial.map (ResidueField.map
        (algebraMap R (AdicCompletion (maximalIdeal R) R))))).IsPrime :=
      Ideal.map_isPrime_of_equiv e
    have hass : associatedPrimes (MvPolynomial (Fin r)
          (ResidueField (AdicCompletion (maximalIdeal R) R)))
        (MvPolynomial (Fin r) (ResidueField (AdicCompletion (maximalIdeal R) R)) ⧸
          (t.M'.map π).map (MvPolynomial.map (ResidueField.map
            (algebraMap R (AdicCompletion (maximalIdeal R) R))))) =
        {(t.M'.map π).map (MvPolynomial.map (ResidueField.map
            (algebraMap R (AdicCompletion (maximalIdeal R) R))))} := by
      rw [associatedPrimes.eq_singleton_of_isPrimary hmp.isPrimary, hmp.radical]
    rw [hass, Cardinal.mk_singleton] at hcount
    obtain ⟨hsub, ⟨⟨S₀, hS₀⟩⟩⟩ := Cardinal.eq_one_iff_unique.mp hcount
    have hmem : ∀ S, S ∈ canonicalTransforms (algebraMap R (AdicCompletion (maximalIdeal R) R))
        (Pb := P.map (algebraMap R (AdicCompletion (maximalIdeal R) R))) t ↔
        ∃ th : MonoidalTransform (AdicCompletion (maximalIdeal R) R)
          (P.map (algebraMap R (AdicCompletion (maximalIdeal R) R))),
          th.subring = S ∧ ∃ β : t.ring →+* th.ring,
            IsCanonicalLift (algebraMap R (AdicCompletion (maximalIdeal R) R)) t th β := by
      intro S
      constructor
      · rintro ⟨tb, ⟨β, hβ⟩, rfl⟩
        exact ⟨tb, rfl, β, hβ⟩
      · rintro ⟨th, rfl, β, hβ⟩
        exact ⟨th, ⟨β, hβ⟩, rfl⟩
    exact ⟨S₀, (hmem S₀).mp hS₀, fun S' hS' =>
      congrArg Subtype.val (hsub.elim ⟨S', (hmem S').mpr hS'⟩ ⟨S₀, hS₀⟩)⟩
  · intro th β hβ
    have := hβ.isLocalHom
    obtain ⟨-, -, -, hβinj, hgen⟩ := hL.2.2.1 t th β hβ
    have hbij := AdicCompletion.residueField_map_bijective R
    have hsurj : Function.Surjective (ResidueField.map (R := t.ring) (S := th.ring) β) := by
      intro y
      have hy : y ∈ Subfield.closure
          (Set.range (ResidueField.map (R := t.ring) (S := th.ring) β) ∪
            Set.range (ResidueField.map (R := AdicCompletion (maximalIdeal R) R)
              (S := th.ring) th.toRing)) := by rw [hgen]; trivial
      have hle : Subfield.closure
          (Set.range (ResidueField.map (R := t.ring) (S := th.ring) β) ∪
            Set.range (ResidueField.map (R := AdicCompletion (maximalIdeal R) R)
              (S := th.ring) th.toRing)) ≤
          (ResidueField.map (R := t.ring) (S := th.ring) β).fieldRange := by
        rw [Subfield.closure_le]
        rintro _ (h | ⟨z, rfl⟩)
        · exact h
        · obtain ⟨w, hw⟩ := hbij.2 z
          obtain ⟨r, rfl⟩ := IsLocalRing.residue_surjective w
          refine ⟨IsLocalRing.residue _ (t.toRing r), ?_⟩
          rw [← hw, ResidueField.map_residue, ResidueField.map_residue, ResidueField.map_residue]
          have := RingHom.congr_fun hβ.comm r
          simp only [RingHom.comp_apply] at this
          rw [this]
      exact hle hy
    refine ⟨⟨(ResidueField.map β).injective, hsurj⟩, ?_⟩
    have hP0 : P ≠ ⊥ := (Submodule.ne_bot_iff P).mpr ⟨t.x, t.x_mem, t.x_ne_zero⟩
    obtain ⟨hreg, -, -⟩ := MonoidalTransform.isRegularLocalRing_and_isLocalHom_and_span_xR_eq_map t hP hP0 hS
    obtain ⟨s, hs⟩ := ((isRegularLocalRing_iff_exists_rsop (R := t.ring)).mp hreg).2
    have hsep : RingHom.IsResiduallySeparableAlgebraic
        (algebraMap R (AdicCompletion (maximalIdeal R) R)) := by
      let := (ResidueField.map (algebraMap R (AdicCompletion (maximalIdeal R) R))).toAlgebra
      refine ⟨fun x => ?_⟩
      obtain ⟨w, hw⟩ := hbij.2 x
      have : x = algebraMap (ResidueField R) (ResidueField (AdicCompletion (maximalIdeal R) R)) w :=
        hw.symm
      rw [this]
      exact isSeparable_algebraMap w
    exact ⟨s, hs, (hL.2.2.2 t th β hβ).2 hsep s hs, hβinj.injOn⟩

/-- `evalₐ` is compatible with the transition maps of the `I`-adic completion. -/
theorem _root_.AdicCompletion.factorPow_evalₐ {S : Type u} [CommRing S] (I : Ideal S) {m n : ℕ} (h : m ≤ n)
    (x : AdicCompletion I S) :
    Ideal.Quotient.factorPow I h (AdicCompletion.evalₐ I n x) = AdicCompletion.evalₐ I m x := by
  obtain ⟨c, rfl⟩ := AdicCompletion.mk_surjective I S x
  rw [AdicCompletion.evalₐ_mk, AdicCompletion.evalₐ_mk, Ideal.Quotient.factorPow,
    Ideal.Quotient.factor_mk, Ideal.Quotient.eq]
  have := AdicCompletion.AdicCauchySequence.mk_eq_mk h c
  rw [Submodule.Quotient.eq, smul_eq_mul, Ideal.mul_top] at this
  simpa using this

/-- A ring map `β : A → B` with `β⁻¹(Jⁿ) = Iⁿ` and `B = β(A) + Jⁿ` for all `n` induces
`A/Iⁿ ≅ B/Jⁿ`, hence an isomorphism of the `I`-adic and `J`-adic completions; the isomorphism is
the one induced by `β`: it commutes with the canonical maps `A → Â`, `B → B̂`. -/
theorem _root_.AdicCompletion.exists_ringEquiv_of_comap_pow_eq {A B : Type u} [CommRing A] [CommRing B] (β : A →+* B)
    (I : Ideal A) (J : Ideal B) (hc : ∀ n, (J ^ n).comap β = I ^ n)
    (hs : ∀ n (b : B), ∃ a, b - β a ∈ J ^ n) :
    ∃ Φ : AdicCompletion I A ≃+* AdicCompletion J B,
      ∀ a, Φ (algebraMap A (AdicCompletion I A) a) = algebraMap B (AdicCompletion J B) (β a) := by
  have hle : ∀ n, I ^ n ≤ (J ^ n).comap β := fun n => (hc n).ge
  let e : ∀ n, A ⧸ I ^ n ≃+* B ⧸ J ^ n := fun n =>
    RingEquiv.ofBijective (Ideal.quotientMap (J ^ n) β (hle n))
      ⟨Ideal.quotientMap_injective' (hc n).le, by
        intro y
        obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective y
        obtain ⟨a, ha⟩ := hs n b
        refine ⟨Ideal.Quotient.mk _ a, ?_⟩
        rw [Ideal.quotientMap_mk, Ideal.Quotient.eq]
        simpa using (Ideal.neg_mem_iff _).mpr ha⟩
  have he : ∀ n a, e n (Ideal.Quotient.mk _ a) = Ideal.Quotient.mk _ (β a) := fun n a => rfl
  have hcomp : ∀ {m n : ℕ} (hmn : m ≤ n) (y : A ⧸ I ^ n),
      Ideal.Quotient.factorPow J hmn (e n y) = e m (Ideal.Quotient.factorPow I hmn y) := by
    intro m n hmn y
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective y
    simp only [he, Ideal.Quotient.factorPow, Ideal.Quotient.factor_mk]
  let F : AdicCompletion I A →+* AdicCompletion J B :=
    AdicCompletion.liftRingHom J (fun n => ((e n : A ⧸ I ^ n →+* B ⧸ J ^ n)).comp
      (AdicCompletion.evalₐ I n : AdicCompletion I A →+* A ⧸ I ^ n)) (by
        intro m n hmn
        ext x
        simp only [RingHom.comp_apply, RingHom.coe_coe]
        rw [hcomp, AdicCompletion.factorPow_evalₐ])
  let G : AdicCompletion J B →+* AdicCompletion I A :=
    AdicCompletion.liftRingHom I (fun n => (((e n).symm : B ⧸ J ^ n ≃+* A ⧸ I ^ n) : B ⧸ J ^ n →+* A ⧸ I ^ n).comp
      (AdicCompletion.evalₐ J n : AdicCompletion J B →+* B ⧸ J ^ n)) (by
        intro m n hmn
        ext x
        simp only [RingHom.comp_apply, RingHom.coe_coe]
        rw [eq_comm, RingEquiv.symm_apply_eq, ← hcomp, RingEquiv.apply_symm_apply,
          AdicCompletion.factorPow_evalₐ])
  refine ⟨RingEquiv.ofRingHom F G ?_ ?_, ?_⟩
  · refine RingHom.ext fun y => ?_
    refine AdicCompletion.ext_evalₐ fun n => ?_
    simp [F, G]
  · refine RingHom.ext fun y => ?_
    refine AdicCompletion.ext_evalₐ fun n => ?_
    simp [F, G]
  · intro a
    refine AdicCompletion.ext_evalₐ fun n => ?_
    show AdicCompletion.evalₐ J n (F (AdicCompletion.of I A a)) =
      AdicCompletion.evalₐ J n (AdicCompletion.of J B (β a))
    simp [F]
    rfl

/-- A ring map `β : A → B` with `β⁻¹(Jⁿ) = Iⁿ` and `B = β(A) + Jⁿ` for all `n` induces
`A/Iⁿ ≅ B/Jⁿ`, hence an isomorphism of the `I`-adic and `J`-adic completions. -/
theorem _root_.AdicCompletion.nonempty_ringEquiv_of_comap_pow_eq {A B : Type u} [CommRing A] [CommRing B] (β : A →+* B)
    (I : Ideal A) (J : Ideal B) (hc : ∀ n, (J ^ n).comap β = I ^ n)
    (hs : ∀ n (b : B), ∃ a, b - β a ∈ J ^ n) :
    Nonempty (AdicCompletion I A ≃+* AdicCompletion J B) :=
  (AdicCompletion.exists_ringEquiv_of_comap_pow_eq β I J hc hs).elim fun Φ _ => ⟨Φ⟩

/-- If `IB = J` and `B = β(A) + J` then `B = β(A) + Jⁿ` for all `n`. -/
theorem exists_sub_mem_pow_of_map_eq {A B : Type u} [CommRing A] [CommRing B] (β : A →+* B)
    (I : Ideal A) (J : Ideal B) (hmap : I.map β = J) (hres : ∀ b : B, ∃ a, b - β a ∈ J) :
    ∀ n (b : B), ∃ a, b - β a ∈ J ^ n := by
  have key : ∀ n, ∀ c ∈ (I ^ n).map β, c ∈ J ^ n ∧ ∃ a, c - β a ∈ J ^ (n + 1) := by
    intro n c hc
    have hJn : (I ^ n).map β = J ^ n := by rw [Ideal.map_pow, hmap]
    unfold Ideal.map at hc
    induction hc using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨y, hy, rfl⟩ := hx
      refine ⟨?_, y, by simp⟩
      rw [← hJn]; exact Ideal.mem_map_of_mem β hy
    | zero => exact ⟨zero_mem _, 0, by simp⟩
    | add x y _ _ ihx ihy =>
      obtain ⟨hx, a, ha⟩ := ihx
      obtain ⟨hy, a', ha'⟩ := ihy
      refine ⟨add_mem hx hy, a + a', ?_⟩
      have := add_mem ha ha'
      convert this using 1
      rw [map_add]; ring
    | smul r x _ ih =>
      obtain ⟨hx, a, ha⟩ := ih
      obtain ⟨a0, he⟩ := hres r
      refine ⟨Ideal.mul_mem_left _ _ hx, a0 * a, ?_⟩
      have h1 : β a0 * (x - β a) ∈ J ^ (n + 1) := Ideal.mul_mem_left _ _ ha
      have h2 : (r - β a0) * x ∈ J ^ (n + 1) := by
        rw [pow_succ']; exact Ideal.mul_mem_mul he hx
      have := add_mem h1 h2
      convert this using 1
      rw [map_mul]; simp only [smul_eq_mul]; ring
  intro n
  induction n with
  | zero => intro b; exact ⟨0, by simp⟩
  | succ n ih =>
    intro b
    obtain ⟨a, ha⟩ := ih b
    have hc : b - β a ∈ (I ^ n).map β := by rw [Ideal.map_pow, hmap]; exact ha
    obtain ⟨-, a', ha'⟩ := key n _ hc
    exact ⟨a + a', by convert ha' using 1; rw [map_add]; ring⟩

/-- If `β⁻¹(Jⁿ) = Iⁿ` for all `n`, `β` is inducing for the adic topologies. -/
theorem isInducing_adicTopology_of_comap_pow_eq {A B : Type u} [CommRing A] [CommRing B] (β : A →+* B)
    (I : Ideal A) (J : Ideal B) (hc : ∀ n, (J ^ n).comap β = I ^ n) :
    @Topology.IsInducing A B I.adicTopology J.adicTopology β := by
  let := I.adicTopology
  let := J.adicTopology
  have := Ideal.nonarchimedean I
  have := Ideal.nonarchimedean J
  rw [IsTopologicalAddGroup.isInducing_iff_nhds_zero (f := β)]
  have h1 := Ideal.hasBasis_nhds_zero_adic I
  have h2 := (Ideal.hasBasis_nhds_zero_adic J).comap β
  have h3 : ∀ n, β ⁻¹' ((J ^ n : Ideal B) : Set B) = ((I ^ n : Ideal A) : Set A) := fun n => by
    rw [← hc n]; rfl
  simp only [h3] at h2
  exact h1.eq_of_same_basis h2

/-- The descending chain `Iₙ + mʲ` (`n ∈ ℕ`) of ideals of a noetherian local ring `A` stabilizes, for
every `j`: the quotient `A/mʲ` is Artinian. (Step of the proof of Chevalley's lemma.) -/
theorem exists_forall_sup_pow_eq_of_antitone {A : Type u} [CommRing A]
    [IsNoetherianRing A] [IsLocalRing A] (I : ℕ → Ideal A) (hanti : Antitone I) (j : ℕ) :
    ∃ N, ∀ n, N ≤ n → I n ⊔ maximalIdeal A ^ j = I N ⊔ maximalIdeal A ^ j := by
  classical
  by_cases hj : maximalIdeal A ^ j = ⊤
  · exact ⟨0, fun n _ => by simp [hj]⟩
  have : Nontrivial (A ⧸ maximalIdeal A ^ j) := Ideal.Quotient.nontrivial_iff.mpr hj
  have := IsLocalRing.of_surjective' (Ideal.Quotient.mk (maximalIdeal A ^ j))
    Ideal.Quotient.mk_surjective
  have := IsLocalHom.of_surjective (Ideal.Quotient.mk (maximalIdeal A ^ j))
    Ideal.Quotient.mk_surjective
  have hmm : (maximalIdeal A).map (Ideal.Quotient.mk (maximalIdeal A ^ j)) =
      maximalIdeal (A ⧸ maximalIdeal A ^ j) := by
    ext x
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    simp [sup_eq_left.mpr (le_maximalIdeal hj)]
  have hart : IsArtinianRing (A ⧸ maximalIdeal A ^ j) := by
    rw [isArtinianRing_iff_isNilpotent_maximalIdeal]
    refine ⟨j, ?_⟩
    rw [← hmm, ← Ideal.map_pow, Ideal.zero_eq_bot, Ideal.map_eq_bot_iff_le_ker, Ideal.mk_ker]
  obtain ⟨N, hN⟩ := IsArtinian.monotone_stabilizes (R := A ⧸ maximalIdeal A ^ j)
    (M := A ⧸ maximalIdeal A ^ j)
    ⟨fun n => OrderDual.toDual ((I n).map (Ideal.Quotient.mk (maximalIdeal A ^ j))),
      fun a b hab => Ideal.map_mono (hanti hab)⟩
  refine ⟨N, fun n hn => ?_⟩
  have h := hN n hn
  have h' : (I N).map (Ideal.Quotient.mk (maximalIdeal A ^ j)) =
      (I n).map (Ideal.Quotient.mk (maximalIdeal A ^ j)) := h
  have key : ∀ K : Ideal A, K ⊔ maximalIdeal A ^ j =
      ((K.map (Ideal.Quotient.mk (maximalIdeal A ^ j))).comap
        (Ideal.Quotient.mk (maximalIdeal A ^ j))) := by
    intro K
    rw [Ideal.comap_map_of_surjective' _ Ideal.Quotient.mk_surjective]
    rw [Ideal.mk_ker]
  rw [key, key, h']

/-- Krull's intersection theorem in the form `⋂ⱼ (K + mʲ) = K` in a noetherian local ring. -/
theorem iInf_sup_maximalIdeal_pow_eq {A : Type u} [CommRing A]
    [IsNoetherianRing A] [IsLocalRing A] (K : Ideal A) :
    ⨅ j, K ⊔ maximalIdeal A ^ j = K := by
  refine le_antisymm ?_ (le_iInf fun j => le_sup_left)
  by_cases hK : K = ⊤
  · simp [hK]
  intro x hx
  rw [Submodule.mem_iInf] at hx
  have : Nontrivial (A ⧸ K) := Ideal.Quotient.nontrivial_iff.mpr hK
  have := IsLocalRing.of_surjective' (Ideal.Quotient.mk K) Ideal.Quotient.mk_surjective
  have := IsLocalHom.of_surjective (Ideal.Quotient.mk K) Ideal.Quotient.mk_surjective
  have hmm : (maximalIdeal A).map (Ideal.Quotient.mk K) = maximalIdeal (A ⧸ K) := by
    ext y
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
    simp [sup_eq_left.mpr (le_maximalIdeal hK)]
  have h0 : Ideal.Quotient.mk K x ∈ ⨅ j : ℕ, maximalIdeal (A ⧸ K) ^ j := by
    rw [Submodule.mem_iInf]
    intro j
    rw [← hmm, ← Ideal.map_pow]
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp (hx j)
    rw [map_add, Ideal.Quotient.eq_zero_iff_mem.mpr ha, zero_add]
    exact Ideal.mem_map_of_mem _ hb
  rw [Ideal.iInf_pow_eq_bot_of_isLocalRing _ (maximalIdeal.isMaximal _).ne_top] at h0
  exact Ideal.Quotient.eq_zero_iff_mem.mp ((Ideal.mem_bot).mp h0)

/-- **Chevalley's lemma** (Zariski–Samuel, *Commutative Algebra* II, Ch. VIII, §5, Thm. 13; covered
by footnote 3 of the paper, p. 116, and used tacitly on p. 213 to conclude from "`R̂ → T` injective"
that the `M̂`-adic topology of `R̂` is induced by that of `T`): if `A` is a complete noetherian local
ring and `I₀ ⊇ I₁ ⊇ …` is a decreasing sequence of ideals with `⋂ Iₙ = 0`, then for every `k` there
is `n` with `Iₙ ⊆ mᵏ`.

Proof (the classical one). If `Iₙ ⊄ mᵏ` for all `n`, put `T_j = ⋂ₙ (Iₙ + mʲ)`; by the descending
chain condition on `A/mʲ`, `T_j = Iₙ + mʲ` for `n` large, so `T_j ⊆ T_{j+1} + mʲ` and `T_k ⊄ mᵏ`.
Choose `x₀ ∈ T_k ∖ mᵏ` and, inductively, `x_{d+1} ∈ T_{k+d+1}` with `x_d - x_{d+1} ∈ m^{k+d}`. The
sequence is `m`-adically Cauchy, so it has a limit `L` (completeness); `L ∈ Iₙ + mʲ` for all `n, j`,
so `L ∈ Iₙ` for all `n` (Krull), i.e. `L = 0`, whence `x₀ ∈ mᵏ`, a contradiction. -/
@[blueprint "compat:chevalley-complete-local"
  (statement := /-- \textbf{Chevalley's lemma} (Zariski--Samuel, \emph{Commutative Algebra} II,
    Ch.~VIII, \S5, Thm.~13; covered by footnote~3, p.~116; used tacitly on p.~213). Let $A$ be a
    complete noetherian local ring with maximal ideal $\mathfrak m$ and $I_0\supseteq I_1\supseteq\dots$
    ideals with $\bigcap_n I_n=0$. Then for every $k$ there is $n$ with $I_n\subseteq\mathfrak m^k$. -/)
  (proof := /-- If $I_n\not\subseteq\mathfrak m^k$ for all $n$, put $T_j=\bigcap_n(I_n+\mathfrak m^j)$. As
    $A/\mathfrak m^j$ is artinian, $T_j=I_n+\mathfrak m^j$ for $n\gg0$, so $T_j\subseteq
    T_{j+1}+\mathfrak m^j$ and $T_k\not\subseteq\mathfrak m^k$. Pick $x_0\in T_k\setminus\mathfrak m^k$
    and $x_{d+1}\in T_{k+d+1}$ with $x_d-x_{d+1}\in\mathfrak m^{k+d}$. The sequence is Cauchy; its
    limit $L$ lies in $I_n+\mathfrak m^j$ for all $n,j$, hence in $I_n$ (Krull), so $L=0$ and
    $x_0\in\mathfrak m^k$, a contradiction. -/)
  (latexEnv := "lemma")]
theorem exists_le_maximalIdeal_pow_of_antitone_of_iInf_eq_bot {A : Type u} [CommRing A]
    [IsNoetherianRing A] [IsLocalRing A] [IsAdicComplete (maximalIdeal A) A] (I : ℕ → Ideal A)
    (hanti : Antitone I) (h : ⨅ n, I n = ⊥) (k : ℕ) : ∃ n, I n ≤ maximalIdeal A ^ k := by
  classical
  by_contra hcon
  push Not at hcon
  set m := maximalIdeal A with hm
  let T : ℕ → Ideal A := fun j => ⨅ n, I n ⊔ m ^ j
  have hTle : ∀ j n, T j ≤ I n ⊔ m ^ j := fun j n => iInf_le _ n
  -- `T j = Iₙ + mʲ` for `n` large (descending chain condition on `A/mʲ`)
  have hT : ∀ j, ∃ N, ∀ n, N ≤ n → T j = I n ⊔ m ^ j := by
    intro j
    obtain ⟨N, hN⟩ := exists_forall_sup_pow_eq_of_antitone I hanti j
    refine ⟨N, fun n hn => le_antisymm (hTle j n) (le_iInf fun n' => ?_)⟩
    rcases le_total n' n with h1 | h1
    · exact sup_le_sup_right (hanti h1) _
    · rw [hN n' (hn.trans h1), hN n hn]
  -- `T j ⊆ T (j+1) + mʲ`
  have hb : ∀ j, T j ≤ T (j + 1) ⊔ m ^ j := by
    intro j
    obtain ⟨N₁, hN₁⟩ := hT j
    obtain ⟨N₂, hN₂⟩ := hT (j + 1)
    rw [hN₁ (max N₁ N₂) (le_max_left _ _), hN₂ (max N₁ N₂) (le_max_right _ _)]
    exact sup_le (le_sup_of_le_left le_sup_left) le_sup_right
  -- `T k ⊄ mᵏ`
  obtain ⟨x₀, hx₀, hx₀k⟩ : ∃ x₀ ∈ T k, x₀ ∉ m ^ k := by
    by_contra hh
    push Not at hh
    obtain ⟨N, hN⟩ := hT k
    refine hcon N (le_trans le_sup_left (?_ : I N ⊔ m ^ k ≤ m ^ k))
    rw [← hN N le_rfl]
    exact hh
  have step : ∀ d (a : A), a ∈ T (k + d) → ∃ b ∈ T (k + d + 1), a - b ∈ m ^ (k + d) := by
    intro d a ha
    obtain ⟨b, hb', c, hc, rfl⟩ := Submodule.mem_sup.mp (hb (k + d) ha)
    exact ⟨b, hb', by simpa using hc⟩
  let g : ℕ → A → A := fun d a =>
    if hh : a ∈ T (k + d) then (step d a hh).choose else 0
  let x : ℕ → A := fun d => Nat.rec x₀ (fun d a => g d a) d
  have hx_succ : ∀ d, x (d + 1) = g d (x d) := fun d => rfl
  have hxT : ∀ d, x d ∈ T (k + d) := by
    intro d
    induction d with
    | zero => exact hx₀
    | succ d ih =>
      rw [hx_succ, show g d (x d) = (step d (x d) ih).choose by simp [g, ih]]
      exact (step d (x d) ih).choose_spec.1
  have hxd : ∀ d, x d - x (d + 1) ∈ m ^ (k + d) := by
    intro d
    have ih := hxT d
    rw [hx_succ, show g d (x d) = (step d (x d) ih).choose by simp [g, ih]]
    exact (step d (x d) ih).choose_spec.2
  -- all `x d` are congruent to `x₀` modulo `mᵏ`
  have hx0k : ∀ d, x 0 - x d ∈ m ^ k := by
    intro d
    induction d with
    | zero => simp
    | succ d ih =>
      have := Ideal.add_mem _ ih (Ideal.pow_le_pow_right (Nat.le_add_right k d) (hxd d))
      simpa using this
  -- the sequence is Cauchy
  have hcauchy : ∀ {a b : ℕ}, a ≤ b → x a - x b ∈ m ^ a := by
    intro a b hab
    induction b, hab using Nat.le_induction with
    | base => simp
    | succ b hab ih =>
      have := Ideal.add_mem _ ih (Ideal.pow_le_pow_right (hab.trans (Nat.le_add_left b k) |>.trans_eq
        (by ring)) (hxd b))
      simpa using this
  have hsm : ∀ a : ℕ, (m ^ a • ⊤ : Submodule A A) = m ^ a := fun a => by
    rw [smul_eq_mul, Ideal.mul_top]
  obtain ⟨L, hL⟩ := IsPrecomplete.prec (inferInstance : IsPrecomplete m A) (f := x) (by
    intro a b hab
    rw [SModEq.sub_mem, hsm]
    exact hcauchy hab)
  have hLd : ∀ d, x d - L ∈ m ^ d := fun d => by
    rw [← hsm]; exact (SModEq.sub_mem.mp (hL d))
  -- `L ∈ ⋂ₙ Iₙ = 0`
  have hLmem : ∀ n, L ∈ I n := by
    intro n
    rw [← iInf_sup_maximalIdeal_pow_eq (I n), Submodule.mem_iInf]
    intro j
    have h1 : x j ∈ I n ⊔ m ^ j :=
      (hTle (k + j) n |>.trans (sup_le_sup_left (Ideal.pow_le_pow_right (Nat.le_add_left j k)) _))
        (hxT j)
    have h2 : x j - L ∈ I n ⊔ m ^ j := (le_sup_right : m ^ j ≤ I n ⊔ m ^ j) (hLd j)
    have := Ideal.sub_mem _ h1 h2
    simpa using this
  have hL0 : L = 0 := by
    have : L ∈ ⨅ n, I n := Submodule.mem_iInf _ |>.mpr hLmem
    rw [h] at this
    exact (Ideal.mem_bot).mp this
  apply hx₀k
  show x 0 ∈ m ^ k
  have h3 := Ideal.add_mem _ (hx0k k) (hLd k)
  rw [hL0] at h3
  simpa using h3

/-- If `Iⁿ ⊆ β⁻¹(Jⁿ)` and `∀ n ∃ m, β⁻¹(Jᵐ) ⊆ Iⁿ`, then `β` is inducing for the adic topologies. -/
theorem isInducing_adicTopology_of_comap_pow_le {A B : Type u} [CommRing A] [CommRing B]
    (β : A →+* B) (I : Ideal A) (J : Ideal B) (hle : ∀ n, I ^ n ≤ (J ^ n).comap β)
    (hc : ∀ n, ∃ m, (J ^ m).comap β ≤ I ^ n) :
    @Topology.IsInducing A B I.adicTopology J.adicTopology β := by
  let := I.adicTopology
  let := J.adicTopology
  have := Ideal.nonarchimedean I
  have := Ideal.nonarchimedean J
  rw [IsTopologicalAddGroup.isInducing_iff_nhds_zero (f := β)]
  have h1 := Ideal.hasBasis_nhds_zero_adic I
  have h2 := (Ideal.hasBasis_nhds_zero_adic J).comap β
  apply le_antisymm
  · rw [h2.ge_iff]
    intro m _
    exact Filter.mem_of_superset (h1.mem_of_mem (i := m) trivial) (fun x hx => hle m hx)
  · rw [h1.ge_iff]
    intro n _
    obtain ⟨m, hm⟩ := hc n
    exact Filter.mem_of_superset (h2.mem_of_mem (i := m) trivial) hm

/-- Corollary 2, first statement and the diagram of its proof (p. 213): "the completions of `R'` and
`R̂'` are canonically isomorphic to each other" and "the diagram of Corollary 1 can be extended to the
following commutative diagram of canonical local homomorphisms, all injective: `R' → R̂' → T`".
Here `T` is the common completion: `R'^` (completion of `R'`) is identified with `R̂'^` (completion of
`R̂'`) by an isomorphism `Φ` which is the one induced by `β` ("canonical"): `Φ(ι(a)) = ι̂(β(a))` for the
canonical maps `ι : R' → R'^`, `ι̂ : R̂' → R̂'^`.  So `R' → R̂' → T` commutes (with `T = R̂'^` and
`R' → T` the composite `Φ ∘ ι`), and the maps `ι`, `ι̂` are injective.

Proof as printed: "`R'` and `R̂'` have the same residue field. Hence, the fact that `R'` and `R̂'` have a
common regular system of parameters implies the first statement of Corollary 2."  In Lean:
* "the same residue field": `hbij`, from Corollary 1; so `R̂' = β(R') + M̂'`;
* "a common regular system of parameters": `hrsop`, from Corollary 1, gives `M̂' = M'R̂'`, hence
  `R̂' = β(R') + M̂'ⁿ` for all `n` (`exists_sub_mem_pow_of_map_eq`), and
  `RingHom.MapsRSOP.comap_maximalIdeal_pow`: `β⁻¹(M̂'ⁿ) = M'ⁿ`.  Together: `R'/M'ⁿ → R̂'/M̂'ⁿ` is
  bijective for every `n`, which is the isomorphism of the completions
  (`AdicCompletion.exists_ringEquiv_of_comap_pow_eq`);
* the injectivity of `R' → R'^` and `R̂' → R̂'^` is Krull's intersection theorem (the
  maximal-adic filtration of a noetherian local ring is separated).

Gap in the paper filled ("Hence, the fact that … common regular system of parameters implies"): the
printed text does not say why a common regular system of parameters and a common residue field make
`R'/M'ⁿ → R̂'/M̂'ⁿ` an isomorphism.  Lean's argument is that of equal length of the two quotients,
made explicit (`RingHom.MapsRSOP.comap_maximalIdeal_pow`): both have the same Hilbert function because
`gr_{M'}(R')` and `gr_{M̂'}(R̂')` are polynomial rings in the classes of the common regular system of
parameters; an element of `M'ᵏ` is a form of degree `k` in the common parameters and, by
quasi-regularity of these in `R̂'`, it lies in `M̂'ᵏ⁺¹` only if all its coefficients lie in `M'`; so the
surjection `R'/M'ⁿ → R̂'/M̂'ⁿ` is injective. -/
@[blueprint "cor:III.lem4-2-diagram"
  (statement := /-- With the notation of \cref{cor:III.lem4-1}, the completions $\widehat{R'}$ of $R'$ and
    $\widehat{\hat R'}$ of $\hat R'$ are canonically isomorphic: there is a ring isomorphism
    $\Phi\colon\widehat{R'}\to\widehat{\hat R'}$ with $\Phi\circ\iota=\hat\iota\circ\beta$, where
    $\iota\colon R'\to\widehat{R'}$ and $\hat\iota\colon\hat R'\to\widehat{\hat R'}$ are the
    canonical maps, and both $\iota$ and $\hat\iota$ are injective. (This is the diagram
    $R'\to\hat R'\to T$ of the proof of Corollary 2, p.~213, with $T=\widehat{\hat R'}$.) -/)
  (proof := /-- ``$R'$ and $\hat R'$ have the same residue field. Hence, the fact that $R'$ and
    $\hat R'$ have a common regular system of parameters implies the first statement.'' By
    \cref{cor:III.lem4-1} $\hat M'=M'\hat R'$ and the residue fields agree, so
    $\hat R'=\beta(R')+\hat M'^n$ for all $n$; and $\beta^{-1}(\hat M'^n)=M'^n$. Hence
    $R'/M'^n\cong\hat R'/\hat M'^n$ for all $n$, and $\Phi$ is the induced isomorphism of the
    inverse limits. The maps $\iota$, $\hat\iota$ are injective by Krull's intersection theorem.

    \textbf{Gap in the paper filled.} The equality $\beta^{-1}(\hat M'^n)=M'^n$ is the equality of
    the lengths of $R'/M'^n$ and $\hat R'/\hat M'^n$ made explicit: an element of $M'^k$ is a form of
    degree $k$ in the common regular system of parameters, and it lies in $\hat M'^{k+1}$ only if
    all its coefficients lie in $M'$, since $\operatorname{gr}_{\hat M'}(\hat R')$ is the polynomial
    ring in the classes of the parameters. -/)
  (latexEnv := "lemma")]
theorem exists_adicCompletion_ringEquiv_of_isCanonicalLift
    (hP : P.IsPrime) (hS : IsRegularLocalRing (R ⧸ P)) (t : MonoidalTransform R P)
    (th : MonoidalTransform (AdicCompletion (maximalIdeal R) R)
      (P.map (algebraMap R (AdicCompletion (maximalIdeal R) R))))
    (β : t.ring →+* th.ring)
    (hβ : IsCanonicalLift (algebraMap R (AdicCompletion (maximalIdeal R) R)) t th β) :
    ∃ Φ : AdicCompletion (R := t.ring) (maximalIdeal t.ring) t.ring ≃+*
        AdicCompletion (R := th.ring) (maximalIdeal th.ring) th.ring,
      (∀ a, Φ (algebraMap t.ring (AdicCompletion (R := t.ring) (maximalIdeal t.ring) t.ring) a) =
        algebraMap th.ring (AdicCompletion (R := th.ring) (maximalIdeal th.ring) th.ring) (β a)) ∧
      Function.Injective
        (algebraMap t.ring (AdicCompletion (R := t.ring) (maximalIdeal t.ring) t.ring)) ∧
      Function.Injective
        (algebraMap th.ring (AdicCompletion (R := th.ring) (maximalIdeal th.ring) th.ring)) := by
  classical
  have hL := (adicCompletion_mapsRSOP_and_existsUnique_transform hP hS t)
  obtain ⟨hbij, hrsop⟩ := hL.2.2.2 th β hβ
  have := hβ.isLocalHom
  have hP0 : P ≠ ⊥ := (Submodule.ne_bot_iff P).mpr ⟨t.x, t.x_mem, t.x_ne_zero⟩
  obtain ⟨hregt, -, -⟩ := MonoidalTransform.isRegularLocalRing_and_isLocalHom_and_span_xR_eq_map t hP hP0 hS
  have hPh0 : P.map (algebraMap R (AdicCompletion (maximalIdeal R) R)) ≠ ⊥ :=
    (Submodule.ne_bot_iff _).mpr ⟨th.x, th.x_mem, th.x_ne_zero⟩
  obtain ⟨hregth, -, -⟩ := MonoidalTransform.isRegularLocalRing_and_isLocalHom_and_span_xR_eq_map th hL.2.1.1 hPh0 hL.2.1.2
  -- `M' B = M̂'`
  have hmap : (maximalIdeal t.ring).map β = maximalIdeal th.ring := by
    obtain ⟨s, hs, himg, -⟩ := hrsop
    rw [← hs.1, Ideal.map_span, ← himg.1, Finset.coe_image]
  have hres : ∀ b : th.ring, ∃ a, b - β a ∈ maximalIdeal th.ring := by
    intro b
    obtain ⟨y, hy⟩ := hbij.2 (IsLocalRing.residue _ b)
    obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective y
    refine ⟨a, ?_⟩
    rw [ResidueField.map_residue] at hy
    rw [← IsLocalRing.residue_eq_zero_iff, map_sub, hy, sub_self]
  -- "the fact that `R'` and `R̂'` have a common regular system of parameters": `β⁻¹(M̂'ⁿ) = M'ⁿ`
  have hc : ∀ n, ((maximalIdeal th.ring) ^ n).comap β = (maximalIdeal t.ring) ^ n :=
    fun n => hrsop.comap_maximalIdeal_pow n
  obtain ⟨Φ, hΦ⟩ := AdicCompletion.exists_ringEquiv_of_comap_pow_eq β _ _ hc
    (exists_sub_mem_pow_of_map_eq β _ _ hmap hres)
  exact ⟨Φ, hΦ, AdicCompletion.of_injective (maximalIdeal t.ring) t.ring,
    AdicCompletion.of_injective (maximalIdeal th.ring) th.ring⟩

/-- Corollary 2 of Lemma 4, the form of the subspace statement visible in the diagram of its
proof (p. 213): "the completions of `R'` and `R̂'` are canonically isomorphic to each other" and
`R' → R̂'` is injective and the `M'`-adic topology of `R'` is the one induced from the `M̂'`-adic
topology of `R̂'` (`R'` is a topological subspace of `R̂'`).  This is NOT the statement printed on
p. 213: the printed second assertion is "`R` is a topological subspace of `R'`", which is
`exists_adicCompletion_ringEquiv_and_injective_and_isInducing_toRing` (label `cor:III.lem4-2`); the
present statement is the companion that the first diagram `R' → R̂' → T` of the proof gives (label
`cor:III.lem4-2-hat-subspace`).

Proof as printed (p. 213): "`R'` and `R̂'` have the same residue field. Hence, the fact that `R'` and
`R̂'` have a common regular system of parameters implies the first statement of Corollary 2. As for
the second, it suffices to note that, if `T` denotes the common completion of `R'` and `R̂'`, then
the diagram of Corollary 1 can be extended to the following commutative diagram of canonical local
homomorphisms, all injective: `R' → R̂' → T`, `R → R̂ → T`."  In Lean:
* "`R'` and `R̂'` have the same residue field", "a common regular system of parameters", "implies the
  first statement": `exists_adicCompletion_ringEquiv_of_isCanonicalLift`, which also gives the
  canonical isomorphism `Φ` (induced by `β`) and the injectivity of `R' → R'^`, `R̂' → R̂'^`, i.e. the
  diagram `R' → R̂' → T`, `T = R̂'^`, with `R' → T` equal to `Φ ∘ ι`, all injective;
* the subspace statement for `R' → R̂'`: `β` is injective (Lemma 4 (2)) and `β⁻¹(M̂'ⁿ) = M'ⁿ` for all
  `n` (`RingHom.MapsRSOP.comap_maximalIdeal_pow`) is the statement that the `M'`-adic topology is
  induced from the `M̂'`-adic one, so `β` is inducing (`isInducing_adicTopology_of_comap_pow_eq`).

Remark on the formalization: the Lean statement records "canonically isomorphic" as the bare existence
of a ring isomorphism of the maximal-adic completions (the canonical one, induced by `β`, is
`exists_adicCompletion_ringEquiv_of_isCanonicalLift`), and "topological subspace" as: `β` is injective
and the `M'`-adic topology of `R'` is the topology induced from the `M̂'`-adic topology of `R̂'`
(`Ideal.adicTopology`, `Topology.IsInducing`). -/
@[blueprint "cor:III.lem4-2-hat-subspace"
  (statement := /-- The notation and assumptions being the same as in \cref{cor:III.lem4-1},
    the completions of $R'$ and $\hat R'$ are canonically isomorphic to each other, and
    $R'\to\hat R'$ is injective and induces on $R'$ its $M'$-adic topology, i.e.\ $R'$ is a
    topological subspace of $\hat R'$. (This is not the statement printed in Corollary 2, p.~213,
    which is \cref{cor:III.lem4-2}: it is the companion statement for the first square of the diagram
    $R'\to\hat R'\to T$ in the proof.) The isomorphism of completions is recorded only as an
    existence statement; the canonical isomorphism, induced by $R'\to\hat R'$, is
    \cref{cor:III.lem4-2-diagram}. -/)
  (proof := /-- $R'$ and $\hat R'$ have the same residue field. Hence, the fact that $R'$ and
    $\hat R'$ have a common regular system of parameters implies the first statement. (p.~213.)

    In Lean: the first statement and the diagram $R'\to\hat R'\to T$ with all maps injective are
    \cref{cor:III.lem4-2-diagram} (the common residue field and the common regular system of
    parameters are \cref{cor:III.lem4-1}). The subspace statement follows from the injectivity of
    $R'\to\hat R'$ (\cref{lem:III.4}) and from $\beta^{-1}(\hat M'^n)=M'^n$ for all $n$, which is
    exactly the assertion that the $M'$-adic topology of $R'$ is induced by that of $\hat R'$.

    \textbf{Gap in the paper filled.} The equality $\beta^{-1}(\hat M'^n)=M'^n$ is the equality of
    the lengths of $R'/M'^n$ and $\hat R'/\hat M'^n$ made explicit; see
    \cref{cor:III.lem4-2-diagram}. -/)
  (latexEnv := "corollary")]
theorem nonempty_adicCompletion_ringEquiv_and_injective_and_isInducing
    (hP : P.IsPrime) (hS : IsRegularLocalRing (R ⧸ P)) (t : MonoidalTransform R P)
    (th : MonoidalTransform (AdicCompletion (maximalIdeal R) R)
      (P.map (algebraMap R (AdicCompletion (maximalIdeal R) R))))
    (β : t.ring →+* th.ring)
    (hβ : IsCanonicalLift (algebraMap R (AdicCompletion (maximalIdeal R) R)) t th β) :
    Nonempty (AdicCompletion (R := t.ring) (maximalIdeal t.ring) t.ring ≃+*
      AdicCompletion (R := th.ring) (maximalIdeal th.ring) th.ring) ∧
    Function.Injective β ∧
    @Topology.IsInducing t.ring th.ring (Ideal.adicTopology (maximalIdeal t.ring))
      (Ideal.adicTopology (maximalIdeal th.ring)) β := by
  classical
  have hL := (adicCompletion_mapsRSOP_and_existsUnique_transform hP hS t)
  have hα := mapsRSOP_algebraMap_adicCompletion (R := R)
  obtain ⟨-, hrsop⟩ := hL.2.2.2 th β hβ
  have := hβ.isLocalHom
  obtain ⟨-, -, -, hβinj, -⟩ :=
    (RingHom.MapsRSOP.canonicalLift_properties (algebraMap R (AdicCompletion (maximalIdeal R) R)) hα hP hS).2.2.1 t th β hβ
  have hP0 : P ≠ ⊥ := (Submodule.ne_bot_iff P).mpr ⟨t.x, t.x_mem, t.x_ne_zero⟩
  obtain ⟨hregt, -, -⟩ := MonoidalTransform.isRegularLocalRing_and_isLocalHom_and_span_xR_eq_map t hP hP0 hS
  have hPh0 : P.map (algebraMap R (AdicCompletion (maximalIdeal R) R)) ≠ ⊥ :=
    (Submodule.ne_bot_iff _).mpr ⟨th.x, th.x_mem, th.x_ne_zero⟩
  obtain ⟨hregth, -, -⟩ := MonoidalTransform.isRegularLocalRing_and_isLocalHom_and_span_xR_eq_map th hL.2.1.1 hPh0 hL.2.1.2
  obtain ⟨Φ, -⟩ := exists_adicCompletion_ringEquiv_of_isCanonicalLift hP hS t th β hβ
  -- "the fact that `R'` and `R̂'` have a common regular system of parameters": `β⁻¹(M̂'ⁿ) = M'ⁿ`
  have hc : ∀ n, ((maximalIdeal th.ring) ^ n).comap β = (maximalIdeal t.ring) ^ n :=
    fun n => hrsop.comap_maximalIdeal_pow n
  exact ⟨⟨Φ⟩, hβinj, isInducing_adicTopology_of_comap_pow_eq β _ _ hc⟩

/-- Corollary 2 (p. 213), as printed: "The notation and assumptions being the same as in Corollary 1,
the completions of **R**′ and **R̂**′ are canonically isomorphic to each other, and **R** is a
topological subspace of **R**′."

The first assertion is the canonical isomorphism `Φ : R'^ ≃+* R̂'^` of the completions, induced by
`β` (`Φ(ι a) = ι̂(β a)`), from `exists_adicCompletion_ringEquiv_of_isCanonicalLift`.  The second is
Zariski's subspace theorem for the monoidal transform: `R → R'` is injective, and the `M`-adic
topology of `R` is the topology induced from the `M'`-adic topology of `R'` (`Ideal.adicTopology`,
`Topology.IsInducing`); equivalently, for every `n` there is `m` with `M'ᵐ ∩ R ⊆ Mⁿ`
(`hcont` in the proof).

Proof as printed (p. 213): "As for the second, it suffices to note that, if `T` denotes the common
completion of `R'` and `R̂'`, then the diagram of Corollary 1 can be extended to the following
commutative diagram of canonical local homomorphisms, all injective: `R' → R̂' → T`, `R → R̂ → T`."
In Lean:
* `T = R̂'^` (completion of `R̂'`), `ψ : R̂ → R̂' → T` the composite of the canonical injections
  (`th.toRing_injective`, `AdicCompletion.of_injective`): "`R̂ → T` injective" (the diagonal arrow of
  the printed diagram is `ψ`; its commutation with `R → R̂ → R̂'` and `R → R' → R̂'` is the
  commutation of the square of Corollary 1, `IsCanonicalLift.comm`);
* `a_m = ker (R̂ → T → R̂'/M̂'ᵐ)` is a decreasing sequence of ideals of `R̂` with `⋂ a_m = ker ψ = 0`;
* tacit step (gap filled): **Chevalley's lemma** for the complete local ring `R̂`
  (`exists_le_maximalIdeal_pow_of_antitone_of_iInf_eq_bot`; Zariski–Samuel II, Ch. VIII, §5, Thm. 13,
  covered by footnote 3, p. 116) gives, for every `n`, an `m` with `a_m ⊆ M̂ⁿ`;
* if `c ∈ R` and `c ∈ M'ᵐ` (in `R'`), then `β(c) = ι(c) ∈ M̂'ᵐ` in `R̂'` (as `β⁻¹(M̂'ᵐ) = M'ᵐ`,
  Corollary 1 / `RingHom.MapsRSOP.comap_maximalIdeal_pow`), so `c ∈ a_m ⊆ M̂ⁿ = M ⁿ R̂`, and
  `M ⁿ R̂ ∩ R = Mⁿ` (`comap_map_adicCompletion_maximalIdeal`): `M'ᵐ ∩ R ⊆ Mⁿ`.
Conversely `Mⁿ ⊆ M'ⁿ ∩ R` since `R → R'` is a local homomorphism. -/
@[blueprint "cor:III.lem4-2"
  (statement := /-- The notation and assumptions being the same as in \cref{cor:III.lem4-1},
    the completions of $R'$ and $\hat R'$ are canonically isomorphic to each other, and $R$ is a
    topological subspace of $R'$. (Corollary 2, p.~213, as printed.) Here ``topological subspace''
    means: $R\to R'$ is injective and the $M$-adic topology of $R$ is the one induced by the
    $M'$-adic topology of $R'$, i.e.\ for every $n$ there is $m$ with $M'^m\cap R\subseteq M^n$
    (Zariski's subspace theorem for the monoidal transform). The canonical isomorphism of the
    completions is the one induced by $R'\to\hat R'$ (\cref{cor:III.lem4-2-diagram}). -/)
  (proof := /-- First statement: \cref{cor:III.lem4-2-diagram}. ``As for the second, it suffices to
    note that, if $T$ denotes the common completion of $R'$ and $\hat R'$, then the diagram of
    Corollary 1 can be extended to the following commutative diagram of canonical local
    homomorphisms, all injective: $R'\to\hat R'\to T$, $R\to\hat R\to T$.'' (p.~213.)

    In Lean: $R\to\hat R\to\hat R'\to T$ is injective (the diagonal of the diagram). The ideals
    $\mathfrak a_m=\ker(\hat R\to T\to\hat R'/\hat M'^m)$ decrease and
    $\bigcap_m\mathfrak a_m=\ker(\hat R\to T)=0$. By Chevalley's lemma for the complete local ring
    $\hat R$ (\cref{compat:chevalley-complete-local}) for every $n$ there is $m$ with
    $\mathfrak a_m\subseteq\hat M^n$. If $c\in R\cap M'^m$ then $\beta(c)\in\hat M'^m$, so
    $c\in\mathfrak a_m\subseteq\hat M^n=M^n\hat R$, hence $c\in M^n\hat R\cap R=M^n$. Thus
    $M'^m\cap R\subseteq M^n$; together with $M^n\subseteq M'^n\cap R$ (local homomorphism) this
    says that the $M$-adic topology of $R$ is induced by the $M'$-adic topology of $R'$.

    \textbf{Gap in the paper filled.} (1) ``All injective'': injectivity of $\hat R\to T$ is proved
    through $\hat R\to\hat R'$ (Lemma 4 (2) for $\hat R$) and $\hat R'\to T$ (Krull). (2) The
    passage from ``$\hat R\to T$ injective'' to ``$R$ is a topological subspace of $R'$'' is not
    argued in the paper: it is Chevalley's lemma (Zariski--Samuel II, Ch.~VIII, \S5, Thm.~13, covered
    by footnote 3, p.~116) used tacitly. -/)
  (latexEnv := "corollary")]
theorem exists_adicCompletion_ringEquiv_and_injective_and_isInducing_toRing
    (hP : P.IsPrime) (hS : IsRegularLocalRing (R ⧸ P)) (t : MonoidalTransform R P)
    (th : MonoidalTransform (AdicCompletion (maximalIdeal R) R)
      (P.map (algebraMap R (AdicCompletion (maximalIdeal R) R))))
    (β : t.ring →+* th.ring)
    (hβ : IsCanonicalLift (algebraMap R (AdicCompletion (maximalIdeal R) R)) t th β) :
    ∃ Φ : AdicCompletion (R := t.ring) (maximalIdeal t.ring) t.ring ≃+*
        AdicCompletion (R := th.ring) (maximalIdeal th.ring) th.ring,
      (∀ a, Φ (algebraMap t.ring (AdicCompletion (R := t.ring) (maximalIdeal t.ring) t.ring) a) =
        algebraMap th.ring (AdicCompletion (R := th.ring) (maximalIdeal th.ring) th.ring) (β a)) ∧
      Function.Injective t.toRing ∧
      @Topology.IsInducing R t.ring (Ideal.adicTopology (maximalIdeal R))
        (Ideal.adicTopology (maximalIdeal t.ring)) t.toRing := by
  classical
  obtain ⟨Φ, hΦ, -, -⟩ := exists_adicCompletion_ringEquiv_of_isCanonicalLift hP hS t th β hβ
  have hL := (adicCompletion_mapsRSOP_and_existsUnique_transform hP hS t)
  have hP0 : P ≠ ⊥ := (Submodule.ne_bot_iff P).mpr ⟨t.x, t.x_mem, t.x_ne_zero⟩
  obtain ⟨hregt, -, -⟩ := MonoidalTransform.isRegularLocalRing_and_isLocalHom_and_span_xR_eq_map t hP hP0 hS
  have hPh0 : P.map (algebraMap R (AdicCompletion (maximalIdeal R) R)) ≠ ⊥ :=
    (Submodule.ne_bot_iff _).mpr ⟨th.x, th.x_mem, th.x_ne_zero⟩
  obtain ⟨hregth, -, -⟩ := MonoidalTransform.isRegularLocalRing_and_isLocalHom_and_span_xR_eq_map th hL.2.1.1 hPh0 hL.2.1.2
  obtain ⟨-, hrsop⟩ := hL.2.2.2 th β hβ
  have := hβ.isLocalHom
  have hc : ∀ n, ((maximalIdeal th.ring) ^ n).comap β = (maximalIdeal t.ring) ^ n :=
    fun n => hrsop.comap_maximalIdeal_pow n
  refine ⟨Φ, hΦ, t.toRing_injective, ?_⟩
  -- the diagram `R̂ → R̂' → T` of the proof of Corollary 2 (p. 213)
  let T := AdicCompletion (R := th.ring) (maximalIdeal th.ring) th.ring
  let ψ : AdicCompletion (maximalIdeal R) R →+* T := (algebraMap th.ring T).comp th.toRing
  have hψ : Function.Injective ψ :=
    (AdicCompletion.of_injective (maximalIdeal th.ring) th.ring).comp th.toRing_injective
  let e : ∀ n : ℕ, AdicCompletion (maximalIdeal R) R →+* th.ring ⧸ maximalIdeal th.ring ^ n :=
    fun n => ((AdicCompletion.evalₐ (maximalIdeal th.ring) n).toRingHom).comp ψ
  have he : ∀ n r, e n r = Ideal.Quotient.mk (maximalIdeal th.ring ^ n) (th.toRing r) := by
    intro n r
    exact (AdicCompletion.evalₐ (maximalIdeal th.ring) n).commutes (th.toRing r)
  have hker : ∀ n, RingHom.ker (e n) = ((maximalIdeal th.ring) ^ n).comap th.toRing := by
    intro n
    ext r
    rw [RingHom.mem_ker, he, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_comap]
  -- `a n = ker (R̂ → T → R̂'/M̂'ⁿ)` is decreasing with intersection `0`: `R̂ → T` is injective
  have hanti : Antitone fun n => RingHom.ker (e n) := by
    intro n m hnm r hr
    simp only [hker] at hr ⊢
    exact Ideal.pow_le_pow_right hnm hr
  have hinf : ⨅ n, RingHom.ker (e n) = ⊥ := by
    rw [eq_bot_iff]
    intro r hr
    rw [Submodule.mem_iInf] at hr
    have : ψ r = ψ 0 := AdicCompletion.ext_evalₐ fun n => by
      have := hr n
      rw [RingHom.mem_ker] at this
      simpa [e] using this
    exact (Ideal.mem_bot).mpr (hψ this)
  -- Chevalley's lemma for the complete local ring `R̂`
  have hcont : ∀ k, ∃ m, ((maximalIdeal t.ring) ^ m).comap t.toRing ≤ maximalIdeal R ^ k := by
    intro k
    obtain ⟨m, hm⟩ := exists_le_maximalIdeal_pow_of_antitone_of_iInf_eq_bot _ hanti hinf k
    refine ⟨m, fun c hcm => ?_⟩
    rw [Ideal.mem_comap] at hcm
    have h1 : th.toRing (algebraMap R (AdicCompletion (maximalIdeal R) R) c) ∈
        maximalIdeal th.ring ^ m := by
      have h2 : β (t.toRing c) ∈ maximalIdeal th.ring ^ m := by
        rw [← Ideal.mem_comap, hc m]
        exact hcm
      have h4 : β (t.toRing c) = th.toRing (algebraMap R (AdicCompletion (maximalIdeal R) R) c) :=
        congrArg (fun f => f c) hβ.comm
      rwa [h4] at h2
    have h3 := hm ((hker m).symm ▸ Ideal.mem_comap.mpr h1)
    rw [AdicCompletion.maximalIdeal_eq_map, ← Ideal.map_pow] at h3
    rw [← comap_map_adicCompletion_maximalIdeal (maximalIdeal R ^ k)]
    exact h3
  have hle : ∀ n, maximalIdeal R ^ n ≤ ((maximalIdeal t.ring) ^ n).comap t.toRing := by
    intro n
    rw [← Ideal.map_le_iff_le_comap, Ideal.map_pow]
    refine Ideal.pow_right_mono (Ideal.map_le_iff_le_comap.mpr fun x hx => ?_) n
    rw [Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hx
    exact fun hu => hx (IsLocalHom.map_nonunit _ hu)
  exact isInducing_adicTopology_of_comap_pow_le t.toRing _ _ hle hcont

end Completion

end Hironaka

